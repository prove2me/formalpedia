-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1354_b0
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T21:08:38.937454+00:00
-- url     : https://prove2.me/submissions/dd224eab-6e10-45d0-b3fd-39e500a961ca

import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_rectangle_majorant
import Mathlib.Analysis.Normed.Lp.PiLp
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Analysis.MeanInequalities
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.Abel
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FinCases
import Definitions.Def_HlawkaSchatten_GapComparison
import Definitions.Def_HlawkaSchatten_DiagonalConstruction_Basic
import Definitions.Def_HlawkaSchatten_DiagonalConstruction_Normalization
import Definitions.Def_HlawkaSchatten_DiagonalCutoff6_Localization
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff6_signed_majorant
/- Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa,
bwdaugherty and Yuxuan Xu. All new numerical implications are checked below. -/
open HlawkaSchatten HlawkaSchatten.DiagonalConstruction
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalConstruction

variable {ι E : Type*} [Fintype ι] [NormedAddCommGroup E]

/-- The coordinate `p`-norm is nonnegative. -/
theorem lpNorm_nonneg (p : ℝ) (x : ι → E) : 0 ≤ lpNorm p x :=
  Real.rpow_nonneg (Finset.sum_nonneg fun _ _ ↦ Real.rpow_nonneg (norm_nonneg _) _) _

/-- The coordinate `p`-norm agrees with the `PiLp` norm. -/
theorem lpNorm_eq_piLp {p : ℝ} (hp : 0 < p) (x : ι → E) :
    lpNorm p x = ‖WithLp.toLp (ENNReal.ofReal p) x‖ := by
  rw [PiLp.norm_eq_sum (by simpa only [ENNReal.toReal_ofReal hp.le] using hp)]
  simp [lpNorm, ENNReal.toReal_ofReal hp.le]

/-- The `p`-norm of zero is zero. -/
@[simp]
theorem lpNorm_zero {p : ℝ} (hp : 0 < p) : lpNorm p (0 : ι → E) = 0 := by
  simp [lpNorm, hp.ne']

/-- The `p`-norm is invariant under negation. -/
@[simp]
theorem lpNorm_neg (p : ℝ) (x : ι → E) : lpNorm p (-x) = lpNorm p x := by
  simp [lpNorm]

/-- Minkowski's inequality for the coordinate `p`-norm. -/
theorem lpNorm_add {p : ℝ} (hp : 1 ≤ p) (x y : ι → E) :
    lpNorm p (x + y) ≤ lpNorm p x + lpNorm p y := by
  have hp0 : 0 < p := lt_of_lt_of_le zero_lt_one hp
  let : Fact (1 ≤ ENNReal.ofReal p) := ⟨ENNReal.one_le_ofReal.mpr hp⟩
  simpa only [lpNorm_eq_piLp hp0, ← WithLp.toLp_add] using
    norm_add_le (WithLp.toLp (ENNReal.ofReal p) x) (WithLp.toLp (ENNReal.ofReal p) y)

/-- Each coordinate norm is at most the `p`-norm. -/
theorem norm_apply_le_lpNorm {p : ℝ} (hp : 1 ≤ p) (x : ι → E) (i : ι) :
    ‖x i‖ ≤ lpNorm p x := by
  have hp0 : 0 < p := lt_of_lt_of_le zero_lt_one hp
  let : Fact (1 ≤ ENNReal.ofReal p) := ⟨ENNReal.one_le_ofReal.mpr hp⟩
  rw [lpNorm_eq_piLp hp0]
  exact PiLp.norm_apply_le (WithLp.toLp (ENNReal.ofReal p) x) i

/-- Raising the `p`-norm to the `p`-th power recovers the sum of `p`-th powers. -/
theorem lpNorm_rpow {p : ℝ} (hp : 0 < p) (x : ι → E) :
    lpNorm p x ^ p = ∑ i, ‖x i‖ ^ p := by
  unfold lpNorm
  rw [← Real.rpow_mul (Finset.sum_nonneg fun i _ ↦ Real.rpow_nonneg (norm_nonneg _) _)]
  rw [one_div_mul_cancel hp.ne', Real.rpow_one]

/-- The `p`-norm vanishes iff the vector is zero. -/
theorem lpNorm_eq_zero_iff {p : ℝ} (hp : 0 < p) (x : ι → E) :
    lpNorm p x = 0 ↔ x = 0 := by
  constructor
  · intro h
    have hs : (∑ i, ‖x i‖ ^ p) = 0 := by
      rw [← lpNorm_rpow hp x, h, Real.zero_rpow hp.ne']
    have hi := (Finset.sum_eq_zero_iff_of_nonneg
      (fun i (_ : i ∈ Finset.univ) ↦ Real.rpow_nonneg (norm_nonneg (x i)) p)).mp hs
    funext i
    exact norm_eq_zero.mp ((Real.rpow_eq_zero (norm_nonneg (x i)) hp.ne').mp
      (hi i (Finset.mem_univ i)))
  · rintro rfl
    exact lpNorm_zero hp

/-- A nonzero vector has strictly positive `p`-norm. -/
theorem lpNorm_pos {p : ℝ} (hp : 0 < p) {x : ι → E} (hx : x ≠ 0) :
    0 < lpNorm p x :=
  lt_of_le_of_ne (lpNorm_nonneg p x) (Ne.symm ((lpNorm_eq_zero_iff hp x).not.mpr hx))

/-- The `p`-norm of a constant vector. -/
theorem lpNorm_const {p : ℝ} (hp : 0 < p) (x : E) :
    lpNorm p (fun _ : ι ↦ x) = (Fintype.card ι : ℝ) ^ (1 / p) * ‖x‖ := by
  unfold lpNorm
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  rw [Real.mul_rpow (Nat.cast_nonneg _) (Real.rpow_nonneg (norm_nonneg _) _),
    ← Real.rpow_mul (norm_nonneg x), mul_one_div_cancel hp.ne', Real.rpow_one]

/-- The `p`-norm scales homogeneously. -/
theorem lpNorm_smul [NormedSpace ℝ E] {p : ℝ} (hp : 0 < p)
    (c : ℝ) (x : ι → E) : lpNorm p (c • x) = |c| * lpNorm p x := by
  unfold lpNorm
  simp only [Pi.smul_apply, norm_smul, Real.norm_eq_abs,
    Real.mul_rpow (abs_nonneg c) (norm_nonneg _), ← Finset.mul_sum]
  rw [Real.mul_rpow (Real.rpow_nonneg (abs_nonneg c) _)
    (Finset.sum_nonneg fun i _ ↦ Real.rpow_nonneg (norm_nonneg (x i)) _),
    ← Real.rpow_mul (abs_nonneg c), mul_one_div_cancel hp.ne', Real.rpow_one]

/-- The coordinate `p`-norm is convex for `p ≥ 1`. -/
theorem convexOn_lpNorm [NormedSpace ℝ E] {p : ℝ} (hp : 1 ≤ p) :
    ConvexOn ℝ Set.univ (lpNorm p : (ι → E) → ℝ) := by
  refine ⟨convex_univ, ?_⟩
  intro x _ y _ a b ha hb _
  have hp0 := zero_lt_one.trans_le hp
  simpa only [lpNorm_smul hp0, abs_of_nonneg ha, abs_of_nonneg hb, smul_eq_mul]
    using lpNorm_add hp (a • x) (b • y)

/-- The coordinate `p`-norm is continuous. -/
theorem continuous_lpNorm {p : ℝ} (hp : 0 < p) :
    Continuous (lpNorm p : (ι → E) → ℝ) := by
  exact (continuous_finsetSum _ fun i _ ↦
    (continuous_apply i).norm.rpow_const (fun _ ↦ Or.inr hp.le)).rpow_const
      (fun _ ↦ Or.inr (one_div_nonneg.mpr hp.le))

/-- The `p`-norm is at most `n^(1/p) * M` when each coordinate norm is at most `M`. -/
theorem lpNorm_le_card_root_mul {p M : ℝ} (hp : 0 < p) (hM : 0 ≤ M)
    (x : ι → E) (hx : ∀ i, ‖x i‖ ≤ M) :
    lpNorm p x ≤ (Fintype.card ι : ℝ) ^ (1 / p) * M := by
  have hsum : (∑ i, ‖x i‖ ^ p) ≤ (Fintype.card ι : ℝ) * M ^ p := by
    calc
      _ ≤ ∑ _ : ι, M ^ p :=
        Finset.sum_le_sum fun i _ ↦ Real.rpow_le_rpow (norm_nonneg _) (hx i) hp.le
      _ = _ := by simp
  have h := Real.rpow_le_rpow
    (Finset.sum_nonneg fun i _ ↦ Real.rpow_nonneg (norm_nonneg (x i)) p)
    hsum (one_div_nonneg.mpr hp.le)
  rw [Real.mul_rpow (Nat.cast_nonneg _) (Real.rpow_nonneg hM _),
    ← Real.rpow_mul hM, mul_one_div_cancel hp.ne', Real.rpow_one] at h
  exact h

/-- The `p`-norm of real coordinates equals the `p`-norm of their complex embeddings. -/
theorem lpNorm_ofReal (p : ℝ) (x : ι → ℝ) :
    lpNorm p (fun i ↦ (x i : ℂ)) = lpNorm p x := by
  simp [lpNorm]

/-- Appending zero coordinates does not change the `p`-norm. -/
theorem lpNorm_fin_append_zero {p : ℝ} (hp : 0 < p) {n : ℕ}
    (x : Fin n → E) (m : ℕ) :
    lpNorm p (Fin.append x (0 : Fin m → E)) = lpNorm p x := by
  simp [lpNorm, Fin.sum_univ_add, hp.ne']

/-- A Hlawka constant in dimension `n` is also admissible in every lower dimension. -/
theorem hasHlawkaConstant_fin_of_le {p C : ℝ} (hp : 0 < p)
    {m n : ℕ} (hn : m ≤ n)
    (hC : HasHlawkaConstant (lpNorm p : (Fin n → E) → ℝ) C) :
    HasHlawkaConstant (lpNorm p : (Fin m → E) → ℝ) C := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hn
  intro x y z
  have h := hC (Fin.append x (0 : Fin k → E))
    (Fin.append y (0 : Fin k → E)) (Fin.append z (0 : Fin k → E))
  have hadd (u v : Fin m → E) :
      Fin.append u (0 : Fin k → E) + Fin.append v (0 : Fin k → E) =
        Fin.append (u + v) (0 : Fin k → E) := by
    ext i
    refine Fin.addCases (fun j ↦ ?_) (fun j ↦ ?_) i <;> simp
  simpa only [tripleGap, pairGapSum, pairGap, hadd, lpNorm_fin_append_zero hp] using h

/-- A Hlawka constant in dimension `n ≥ 3` is admissible in dimension 3. -/
theorem hasHlawkaConstant_fin_three_of_ge {p C : ℝ} (hp : 0 < p)
    {n : ℕ} (hn : 3 ≤ n)
    (hC : HasHlawkaConstant (lpNorm p : (Fin n → E) → ℝ) C) :
    HasHlawkaConstant (lpNorm p : (Fin 3 → E) → ℝ) C :=
  hasHlawkaConstant_fin_of_le hp hn hC

/-- The `p`-norm is invariant under coordinate permutation. -/
theorem lpNorm_comp_equiv {κ : Type*} [Fintype κ]
    (p : ℝ) (x : κ → E) (e : ι ≃ κ) : lpNorm p (x ∘ e) = lpNorm p x := by
  unfold lpNorm
  congr 1
  exact e.sum_comp (fun i ↦ ‖x i‖ ^ p)

/-- The `p`-norm restricted to a subtype equals the full norm when unsupported entries vanish. -/
theorem lpNorm_subtype {p : ℝ} (hp : 0 < p) (x : ι → E)
    (P : ι → Prop) [DecidablePred P] (hx : ∀ i, ¬P i → x i = 0) :
    lpNorm p (fun i : Subtype P ↦ x i.1) = lpNorm p x := by
  unfold lpNorm
  congr 1
  have hzero : (∑ i : {i : ι // ¬P i}, ‖x i.1‖ ^ p) = 0 := by
    exact Finset.sum_eq_zero fun i _ ↦ by simp [hx i.1 i.2, hp.ne']
  rw [← Fintype.sum_subtype_add_sum_subtype P (fun i ↦ ‖x i‖ ^ p), hzero, add_zero]

/-- A Hlawka constant in dimension 3 lifts to any index type of cardinality at most 3. -/
theorem hasHlawkaConstant_of_card_le_three {p C : ℝ} (hp : 0 < p)
    (hcard : Fintype.card ι ≤ 3)
    (hC : HasHlawkaConstant (lpNorm p : (Fin 3 → E) → ℝ) C) :
    HasHlawkaConstant (lpNorm p : (ι → E) → ℝ) C := by
  let e := (Fintype.equivFin ι).symm
  have hf := hasHlawkaConstant_fin_of_le hp hcard hC
  intro x y z
  have h := hf (x ∘ e) (y ∘ e) (z ∘ e)
  have hadd (u v : ι → E) : u ∘ e + v ∘ e = (u + v) ∘ e := rfl
  simpa only [tripleGap, pairGapSum, pairGap, hadd, lpNorm_comp_equiv] using h

/-- The pair deficit is nonneg for `p ≥ 1` by Minkowski. -/
theorem pairGap_nonneg {p : ℝ} (hp : 1 ≤ p) (x y : ι → E) :
    0 ≤ pairGap (lpNorm p) x y := sub_nonneg.mpr (lpNorm_add hp x y)

/-- The sum of pair deficits is nonneg for `p ≥ 1`. -/
theorem pairGapSum_nonneg {p : ℝ} (hp : 1 ≤ p) (x y z : ι → E) :
    0 ≤ pairGapSum (lpNorm p) x y z :=
  add_nonneg (add_nonneg (pairGap_nonneg hp x y) (pairGap_nonneg hp x z))
    (pairGap_nonneg hp y z)

end HlawkaSchatten.DiagonalConstruction
namespace HlawkaSchatten.DiagonalRealBundle
theorem sum3 (f : Fin 3 → ℝ) {i j k : Fin 3} (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
    ∑ l, f l = f i + f j + f k := by
  rw [Fin.sum_univ_three]
  fin_cases i <;> fin_cases j <;> fin_cases k <;> simp_all <;> ring
theorem lpNorm_eq3 (p : ℝ) (x : Fin 3 → ℝ) {i j k : Fin 3} (hij : i ≠ j) (hik : i ≠ k)
    (hjk : j ≠ k) : lpNorm p x = (|x i| ^ p + |x j| ^ p + |x k| ^ p) ^ (1/p) := by
  unfold lpNorm
  rw [sum3 (fun l ↦ ‖x l‖ ^ p) hij hik hjk]
  simp [Real.norm_eq_abs]
end HlawkaSchatten.DiagonalRealBundle
namespace HlawkaSchatten.DiagonalRealBundle
theorem le_rpow_of_pow_le {x X : ℝ} (hx : 0 ≤ x) (m k : ℕ) (hk : 0 < k)
    (h : X ^ k ≤ x ^ m) : X ≤ x ^ ((m : ℝ) / k) := by
  rcases le_or_gt X 0 with hX | hX
  · exact hX.trans (Real.rpow_nonneg hx _)
  · have e : x ^ ((m : ℝ) / k) = (x ^ m) ^ ((k : ℝ)⁻¹) := by
      rw [div_eq_mul_inv, Real.rpow_mul hx, Real.rpow_natCast]
    rw [e]
    calc X = (X ^ k) ^ ((k : ℝ)⁻¹) := (Real.pow_rpow_inv_natCast hX.le hk.ne').symm
      _ ≤ (x ^ m) ^ ((k : ℝ)⁻¹) := Real.rpow_le_rpow (by positivity) h (by positivity)
theorem rpow_le_of_pow_le {x X : ℝ} (hx : 0 ≤ x) (hX : 0 ≤ X) (m k : ℕ) (hk : 0 < k)
    (h : x ^ m ≤ X ^ k) : x ^ ((m : ℝ) / k) ≤ X := by
  have e : x ^ ((m : ℝ) / k) = (x ^ m) ^ ((k : ℝ)⁻¹) := by
    rw [div_eq_mul_inv, Real.rpow_mul hx, Real.rpow_natCast]
  rw [e]
  calc (x ^ m) ^ ((k : ℝ)⁻¹) ≤ (X ^ k) ^ ((k : ℝ)⁻¹) :=
        Real.rpow_le_rpow (by positivity) h (by positivity)
    _ = X := Real.pow_rpow_inv_natCast hX hk.ne'
end HlawkaSchatten.DiagonalRealBundle

set_option autoImplicit false
namespace HlawkaSchatten.DiagonalCutoff12
open HlawkaSchatten.DiagonalConstruction
open scoped BigOperators

theorem norm_support {ι : Type*} [Fintype ι] {p q : ℝ}
    (hpq : p.HolderConjugate q) (w x : ι → ℝ)
    (hw : (∑ i, |w i| ^ q) ≤ 1) :
    (∑ i, w i*x i) ≤ lpNorm p x := by
  have h := Real.inner_le_Lp_mul_Lq Finset.univ w x hpq.symm
  have hq : 0 ≤ 1/q := hpq.symm.one_div_nonneg
  have hr := Real.rpow_le_rpow
    (Finset.sum_nonneg fun i _ => Real.rpow_nonneg (abs_nonneg (w i)) q) hw hq
  rw [Real.one_rpow] at hr
  have hn := lpNorm_nonneg p x
  have hm := mul_le_mul_of_nonneg_right hr hn
  simpa only [lpNorm, Real.norm_eq_abs, one_mul] using h.trans hm

theorem power12over11_upper {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y)
    (h : x^12 ≤ y^11) : x^(12/11 : ℝ) ≤ y := by
  have hr := Real.rpow_le_rpow (pow_nonneg hx 12) h (by norm_num : (0 : ℝ) ≤ 1/11)
  rw [← Real.rpow_natCast x 12, ← Real.rpow_natCast y 11,
    ← Real.rpow_mul hx, ← Real.rpow_mul hy] at hr
  norm_num at hr ⊢
  exact hr

theorem norm_support12 (w v x : Fin 3 → ℝ)
    (hv : ∀ i, 0 ≤ v i) (hp : ∀ i, |w i|^12 ≤ (v i)^11)
    (hs : (∑ i, v i) ≤ 1) : (∑ i, w i*x i) ≤ lpNorm 12 x := by
  apply norm_support (q := 12/11)
    (Real.holderConjugate_iff.mpr (by norm_num))
  exact (Finset.sum_le_sum fun i _ => power12over11_upper (abs_nonneg _) (hv i) (hp i)).trans hs

theorem power_ratio_upper {x y : ℝ} (m n : ℕ) (hn : 0 < n)
    (hx : 0 ≤ x) (hy : 0 ≤ y) (h : x^m ≤ y^n) :
    x^((m : ℝ)/(n : ℝ)) ≤ y := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hr := Real.rpow_le_rpow (pow_nonneg hx m) h (one_div_nonneg.mpr hn0.le)
  rw [← Real.rpow_natCast x m, ← Real.rpow_natCast y n,
    ← Real.rpow_mul hx, ← Real.rpow_mul hy,
    mul_one_div_cancel hn0.ne', Real.rpow_one] at hr
  simpa only [div_eq_mul_inv, one_div, one_mul] using hr

theorem norm_support_interval {p b : ℝ} (hp : 1 < p) (hb : 1 < b)
    (hpb : p ≤ b) (w x : Fin 3 → ℝ)
    (hw1 : ∀ i, |w i| ≤ 1)
    (hw : (∑ i, |w i|^(b/(b-1))) ≤ 1) :
    (∑ i, w i*x i) ≤ lpNorm p x := by
  have hqp : b/(b-1) ≤ p/(p-1) := by
    apply (div_le_div_iff₀ (by linarith) (by linarith)).mpr
    nlinarith
  have hq0 : 0 ≤ b/(b-1) := div_nonneg (by linarith) (by linarith)
  apply norm_support (q := p/(p-1))
    ((Real.holderConjugate_iff_eq_conjExponent hp).mpr rfl)
  apply le_trans _ hw
  exact Finset.sum_le_sum fun i _ => Real.rpow_le_rpow_of_exponent_ge'
    (abs_nonneg _) (hw1 i) hq0 hqp

theorem norm_support_interval_cert {p b : ℝ} (m n : ℕ) (hn : 0 < n)
    (hp : 1 < p) (hb : 1 < b) (hpb : p ≤ b)
    (hconj : b/(b-1) = (m : ℝ)/(n : ℝ))
    (w v x : Fin 3 → ℝ) (hw1 : ∀ i, |w i| ≤ 1) (hv : ∀ i, 0 ≤ v i)
    (hpowers : ∀ i, |w i|^m ≤ (v i)^n) (hs : (∑ i, v i) ≤ 1) :
    (∑ i, w i*x i) ≤ lpNorm p x := by
  apply norm_support_interval hp hb hpb w x hw1
  rw [hconj]
  exact (Finset.sum_le_sum fun i _ =>
    power_ratio_upper m n hn (abs_nonneg _) (hv i) (hpowers i)).trans hs

end HlawkaSchatten.DiagonalCutoff12


set_option autoImplicit false
set_option maxHeartbeats 4000000
open HlawkaSchatten.DiagonalConstruction
open scoped BigOperators
namespace HlawkaSchatten.DiagonalCutoff6




theorem total_eq (X : Fin 3 → Fin 3 → ℝ) : total X = X 0+X 1+X 2 := by
  simp [total,Fin.sum_univ_three]
theorem pair0 (X : Fin 3 → Fin 3 → ℝ) : pair X 0 = X 1+X 2 := by
  rw [pair,total_eq];abel
theorem pair1 (X : Fin 3 → Fin 3 → ℝ) : pair X 1 = X 0+X 2 := by
  rw [pair,total_eq];abel
theorem pair2 (X : Fin 3 → Fin 3 → ℝ) : pair X 2 = X 0+X 1 := by
  rw [pair,total_eq];abel


theorem oriented_frame {p q k d : ℝ} {X : Fin 3 → Fin 3 → ℝ}
    (h : RelativeOrientedData p q k d X) : Frame p k (3*q) d X := by
  constructor
  · simpa [Fin.sum_univ_three] using h.sum
  · simpa [total_eq] using h.norm_le_total
  · simpa [total_eq] using h.total_one
  · simpa [total_eq] using h.total_cap.le
  · intro i;fin_cases i
    · simpa [pair0] using h.main0
    · simpa [pair1] using h.main1
    · simpa [pair2] using h.main2
  · intro i h';fin_cases i
    · simpa [pair0] using h.max0 h'
    · simpa [pair1] using h.max1 h'
    · simpa [pair2] using h.max2 h'
  · simpa [total_eq,Fin.sum_univ_three,pair0,pair1,pair2] using h.linear_failure

theorem total_relabel (e : Equiv.Perm (Fin 3)) (X : Fin 3 → Fin 3 → ℝ) :
    total (relabel e X) = total X ∘ e := by
  ext h
  simp only [total,Finset.sum_apply,relabel,Function.comp_apply]
  exact Equiv.sum_comp e (fun j => X j (e h))

theorem pair_relabel (e : Equiv.Perm (Fin 3)) (X : Fin 3 → Fin 3 → ℝ) (i : Fin 3) :
    pair (relabel e X) i = pair X (e i) ∘ e := by
  ext h
  simp [pair,total_relabel,relabel]

theorem frame_relabel {p k A d : ℝ} {X : Fin 3 → Fin 3 → ℝ}
    (h : Frame p k A d X) (e : Equiv.Perm (Fin 3)) : Frame p k A d (relabel e X) := by
  have hr (j : Fin 3) : lpNorm p (relabel e X j) = lpNorm p (X (e j)) :=
    lpNorm_comp_equiv p (X (e j)) e
  have ht : lpNorm p (total (relabel e X)) = lpNorm p (total X) := by
    rw [total_relabel,lpNorm_comp_equiv]
  have hp (i : Fin 3) : lpNorm p (pair (relabel e X) i) = lpNorm p (pair X (e i)) := by
    rw [pair_relabel,lpNorm_comp_equiv]
  constructor
  · simp_rw [hr];rw [Equiv.sum_comp e (fun j => lpNorm p (X j))];exact h.sum
  · intro j;rw [hr,ht];exact h.row_total (e j)
  · rw [ht];exact h.total_one
  · rw [ht];exact h.total_cap
  · intro i;rw [hp,pair_relabel];exact h.main (e i)
  · intro i j;rw [pair_relabel];exact h.maximal (e i) (e j)
  · simp_rw [ht,hp];rw [Equiv.sum_comp e (fun i => lpNorm p (pair X i))];exact h.linear_failure

theorem frame_box_of_base {p k A d ell u v w rho : ℝ}
    (base : ∀ X : Fin 3 → Fin 3 → ℝ, Frame p k A d X →
      (∀ i h, i ≠ h → 0 ≤ pair X i h) →
      (∀ i h, i ≠ h → |pair X i h| ≤ rho*pair X i i) →
      -u ≤ X 0 0 ∧ X 0 0 ≤ -ell ∧ v ≤ X 0 1 ∧ X 0 1 ≤ w)
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p k A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ rho*pair X i i) :
    ∀ j i, if j=i then -u ≤ X j i ∧ X j i ≤ -ell else v ≤ X j i ∧ X j i ≤ w := by
  have permuted (e : Equiv.Perm (Fin 3)) :
      -u ≤ X (e 0) (e 0) ∧ X (e 0) (e 0) ≤ -ell ∧
      v ≤ X (e 0) (e 1) ∧ X (e 0) (e 1) ≤ w := by
    apply base (relabel e X) (frame_relabel hX e)
    · intro i j hij
      rw [pair_relabel]
      exact hsign (e i) (e j) (e.injective.ne hij)
    · intro i j hij
      rw [pair_relabel]
      exact hratio (e i) (e j) (e.injective.ne hij)
  have h0 := permuted (Equiv.refl (Fin 3))
  have h01 := permuted (Equiv.swap (0 : Fin 3) 1)
  have h02 := permuted (Equiv.swap (0 : Fin 3) 2)
  have h12 := permuted (Equiv.swap (1 : Fin 3) 2)
  have h120 := permuted ((Equiv.swap (1 : Fin 3) 2).trans (Equiv.swap 0 1))
  have h201 := permuted ((Equiv.swap (0 : Fin 3) 1).trans (Equiv.swap 1 2))
  norm_num [Equiv.swap_apply_def] at h0 h01 h02 h12 h120 h201
  intro j i
  fin_cases j <;> fin_cases i <;> simp only [ite_true,ite_false]
  · exact ⟨h0.1,h0.2.1⟩
  · exact h0.2.2
  · exact h12.2.2
  · exact h01.2.2
  · exact ⟨h01.1,h01.2.1⟩
  · exact h120.2.2
  · exact h201.2.2
  · exact h02.2.2
  · exact ⟨h02.1,h02.2.1⟩

theorem frame_ratio_of_base {p k A d rho R : ℝ}
    (base : ∀ X : Fin 3 → Fin 3 → ℝ, Frame p k A d X →
      (∀ i h, i ≠ h → 0 ≤ pair X i h) →
      (∀ i h, i ≠ h → |pair X i h| ≤ rho*pair X i i) →
      pair X 0 1 ≤ R*pair X 0 0)
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p k A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ rho*pair X i i) :
    ∀ i h, i ≠ h → |pair X i h| ≤ R*pair X i i := by
  have permuted (e : Equiv.Perm (Fin 3)) :
      pair X (e 0) (e 1) ≤ R*pair X (e 0) (e 0) := by
    have hh := base (relabel e X) (frame_relabel hX e)
      (fun i j hij => by rw [pair_relabel];exact hsign (e i) (e j) (e.injective.ne hij))
      (fun i j hij => by rw [pair_relabel];exact hratio (e i) (e j) (e.injective.ne hij))
    simpa only [pair_relabel,Function.comp_apply] using hh
  have h0 := permuted (Equiv.refl (Fin 3))
  have h01 := permuted (Equiv.swap (0 : Fin 3) 1)
  have h02 := permuted (Equiv.swap (0 : Fin 3) 2)
  have h12 := permuted (Equiv.swap (1 : Fin 3) 2)
  have h120 := permuted ((Equiv.swap (1 : Fin 3) 2).trans (Equiv.swap 0 1))
  have h201 := permuted ((Equiv.swap (0 : Fin 3) 1).trans (Equiv.swap 1 2))
  norm_num [Equiv.swap_apply_def] at h0 h01 h02 h12 h120 h201
  intro i j hij
  rw [abs_of_nonneg (hsign i j hij)]
  fin_cases i <;> fin_cases j <;> try contradiction
  all_goals first | exact h0 | exact h01 | exact h02 | exact h12 | exact h120 | exact h201

end HlawkaSchatten.DiagonalCutoff6

set_option autoImplicit false
set_option maxHeartbeats 4000000
open HlawkaSchatten.DiagonalConstruction
open scoped BigOperators
namespace HlawkaSchatten.DiagonalCutoff6


theorem pair_eq_of_distinct (X : Fin 3 → Fin 3 → ℝ) (i j l : Fin 3)
    (hij : i ≠ j) (hil : i ≠ l) (hjl : j ≠ l) : pair X i = X j+X l := by
  fin_cases i <;> fin_cases j <;> fin_cases l <;> try contradiction
  all_goals first
    | exact pair0 X
    | exact (pair0 X).trans (add_comm _ _)
    | exact pair1 X
    | exact (pair1 X).trans (add_comm _ _)
    | exact pair2 X
    | exact (pair2 X).trans (add_comm _ _)

theorem frame_linear_data {p k A d : ℝ} (hp : 1 ≤ p) (X : Fin 3 → Fin 3 → ℝ)
    (h : Frame p k A d X) :
    LinearData k A d X (fun j => lpNorm p (X j))
      (fun i => lpNorm p (pair X i)) (lpNorm p (total X)) := by
  have hn (j : Fin 3) := lpNorm_nonneg p (X j)
  have hs : lpNorm p (X 0)+lpNorm p (X 1)+lpNorm p (X 2)=3 := by
    simpa [Fin.sum_univ_three] using h.sum
  constructor
  · exact hs
  · exact hn
  · exact h.row_total
  · exact h.total_one
  · exact h.total_cap
  · intro j i;exact abs_le.mp (norm_apply_le_lpNorm hp (X j) i)
  · intro i;simpa [total_eq] using abs_le.mp (norm_apply_le_lpNorm hp (total X) i)
  · intro i;exact lpNorm_nonneg p (pair X i)
  · intro i;fin_cases i
    · change lpNorm p (pair X 0) ≤ 3-lpNorm p (X 0)
      rw [pair0];linarith only [lpNorm_add hp (X 1) (X 2),hs]
    · change lpNorm p (pair X 1) ≤ 3-lpNorm p (X 1)
      rw [pair1];linarith only [lpNorm_add hp (X 0) (X 2),hs]
    · change lpNorm p (pair X 2) ≤ 3-lpNorm p (X 2)
      rw [pair2];linarith only [lpNorm_add hp (X 0) (X 1),hs]
  · exact h.main
  · exact h.maximal
  · intro i
    have hh := lpNorm_add hp (total X) (-X i)
    simpa [pair,sub_eq_add_neg] using hh
  · intro i
    have hh := lpNorm_add hp (pair X i) (X i)
    simpa [pair] using hh
  · intro i j l hij hil hjl
    rw [pair_eq_of_distinct X i j l hij hil hjl]
    have hh := lpNorm_add hp (X j+X l) (-X l)
    have he : X j+X l+-X l = X j := by abel
    rw [he,lpNorm_neg] at hh
    linarith
  · simpa [Fin.sum_univ_three] using h.linear_failure

theorem linear_data_bounds {k A d T : ℝ} {X : Fin 3 → Fin 3 → ℝ} {N P : Fin 3 → ℝ}
    (h : LinearData k A d X N P T) (hA : A ≤ 3) :
    (∀ j i, -3 ≤ X j i ∧ X j i ≤ 3) ∧
    (∀ j, -3 ≤ N j ∧ N j ≤ 3) ∧ (∀ i, -3 ≤ P i ∧ P i ≤ 3) ∧ (-3 ≤ T ∧ T ≤ 3) := by
  have hN (j : Fin 3) : 0 ≤ N j ∧ N j ≤ 3 := by
    refine ⟨h.Nnonneg j,?_⟩
    exact ((h.Ntotal j).trans h.Tcap).trans hA
  refine ⟨?_,?_,?_,?_⟩
  · intro j i;have hc := h.coord j i;have hn := hN j;constructor <;> linarith
  · intro j;have hn := hN j;constructor <;> linarith
  · intro i;have hn := hN i;have ht := h.Ptriangle i
    have hz := h.Pnonneg i;constructor <;> linarith
  · constructor <;> linarith only [h.Tone,h.Tcap,hA]

theorem positive_pair_majorant {p a rho alpha : ℝ}
    (hp : 1 ≤ p) (ha : 0 < a) (hap : a ≤ p)
    (hrho : 0 < rho) (hrho1 : rho ≤ 1) (halpha : 0 ≤ alpha)
    (hc1 : 1+rho^a ≤ (1+alpha*rho)^a)
    (hc2 : 1+2*rho^a ≤ (1+2*alpha*rho)^a)
    (X : Fin 3 → Fin 3 → ℝ)
    (hm : ∀ i, 0 ≤ pair X i i)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ rho*pair X i i)
    (i j l : Fin 3) (hij : i ≠ j) (hil : i ≠ l) (hjl : j ≠ l) :
    lpNorm p (pair X i) ≤ pair X i i+alpha*(pair X i j+pair X i l) := by
  rw [HlawkaSchatten.DiagonalRealBundle.lpNorm_eq3 p _ hij hil hjl]
  have hh := signed_majorant hp ha hap hrho hrho1 halpha hc1 hc2 (hm i)
    (hratio i j hij) (hratio i l hil)
  simpa only [abs_of_nonneg (hsign i j hij),abs_of_nonneg (hsign i l hil)] using hh

theorem frame_weaken {p k A d k' A' d' : ℝ} {X : Fin 3 → Fin 3 → ℝ}
    (hp : 1 ≤ p) (h : Frame p k A d X) (hk : k' ≤ k) (hA : A ≤ A') (hd : d' ≤ d) :
    Frame p k' A' d' X := by
  have f := frame_linear_data hp X h
  have hs : (∑ i, lpNorm p (pair X i)) ≤ 6 := by
    rw [Fin.sum_univ_three]
    have hh := f.sum
    linarith only [f.Ptriangle 0,f.Ptriangle 1,f.Ptriangle 2,hh]
  constructor
  · exact h.sum
  · exact h.row_total
  · exact h.total_one
  · exact h.total_cap.trans hA
  · intro i
    exact (mul_le_mul_of_nonneg_right hd (lpNorm_nonneg p (pair X i))).trans (h.main i)
  · exact h.maximal
  · have hh := mul_le_mul_of_nonneg_right hk (sub_nonneg.mpr hs)
    linarith only [hh,h.linear_failure]

end HlawkaSchatten.DiagonalCutoff6
set_option autoImplicit false
set_option maxHeartbeats 4000000
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
namespace HlawkaSchatten.DiagonalCutoff4
theorem frame_box_of_interval_base {p k A d ell u v w rho lo : ℝ}
    (base : ∀ X : Fin 3 → Fin 3 → ℝ, Frame p k A d X →
      (∀ i h, i ≠ h → 0 ≤ pair X i h) →
      (∀ i h, i ≠ h → |pair X i h| ≤ rho*pair X i i) →
      (∀ i h, i ≠ h → lo*pair X i i ≤ pair X i h) →
      -u ≤ X 0 0 ∧ X 0 0 ≤ -ell ∧ v ≤ X 0 1 ∧ X 0 1 ≤ w)
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p k A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ rho*pair X i i)
    (hlower : ∀ i h, i ≠ h → lo*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -u ≤ X j i ∧ X j i ≤ -ell else v ≤ X j i ∧ X j i ≤ w := by
  have permuted (e : Equiv.Perm (Fin 3)) :
      -u ≤ X (e 0) (e 0) ∧ X (e 0) (e 0) ≤ -ell ∧
      v ≤ X (e 0) (e 1) ∧ X (e 0) (e 1) ≤ w := by
    apply base (relabel e X) (frame_relabel hX e)
    · intro i j hij
      rw [pair_relabel]
      exact hsign (e i) (e j) (e.injective.ne hij)
    · intro i j hij
      rw [pair_relabel]
      exact hratio (e i) (e j) (e.injective.ne hij)
    · intro i j hij
      rw [pair_relabel]
      exact hlower (e i) (e j) (e.injective.ne hij)
  have h0 := permuted (Equiv.refl (Fin 3))
  have h01 := permuted (Equiv.swap (0 : Fin 3) 1)
  have h02 := permuted (Equiv.swap (0 : Fin 3) 2)
  have h12 := permuted (Equiv.swap (1 : Fin 3) 2)
  have h120 := permuted ((Equiv.swap (1 : Fin 3) 2).trans (Equiv.swap 0 1))
  have h201 := permuted ((Equiv.swap (0 : Fin 3) 1).trans (Equiv.swap 1 2))
  norm_num [Equiv.swap_apply_def] at h0 h01 h02 h12 h120 h201
  intro j i
  fin_cases j <;> fin_cases i <;> simp only [ite_true,ite_false]
  · exact ⟨h0.1,h0.2.1⟩
  · exact h0.2.2
  · exact h12.2.2
  · exact h01.2.2
  · exact ⟨h01.1,h01.2.1⟩
  · exact h120.2.2
  · exact h201.2.2
  · exact h02.2.2
  · exact ⟨h02.1,h02.2.1⟩

theorem frame_interval_of_base {p k A d rho lo R L : ℝ}
    (base : ∀ X : Fin 3 → Fin 3 → ℝ, Frame p k A d X →
      (∀ i h, i ≠ h → 0 ≤ pair X i h) →
      (∀ i h, i ≠ h → |pair X i h| ≤ rho*pair X i i) →
      (∀ i h, i ≠ h → lo*pair X i i ≤ pair X i h) →
      L*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ R*pair X 0 0)
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p k A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ rho*pair X i i)
    (hlower : ∀ i h, i ≠ h → lo*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → L*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ R*pair X i i := by
  have permuted (e : Equiv.Perm (Fin 3)) :
      L*pair X (e 0) (e 0) ≤ pair X (e 0) (e 1) ∧
        pair X (e 0) (e 1) ≤ R*pair X (e 0) (e 0) := by
    have hh := base (relabel e X) (frame_relabel hX e)
      (fun i j hij => by rw [pair_relabel];exact hsign (e i) (e j) (e.injective.ne hij))
      (fun i j hij => by rw [pair_relabel];exact hratio (e i) (e j) (e.injective.ne hij))
      (fun i j hij => by rw [pair_relabel];exact hlower (e i) (e j) (e.injective.ne hij))
    simpa only [pair_relabel,Function.comp_apply] using hh
  have h0 := permuted (Equiv.refl (Fin 3))
  have h01 := permuted (Equiv.swap (0 : Fin 3) 1)
  have h02 := permuted (Equiv.swap (0 : Fin 3) 2)
  have h12 := permuted (Equiv.swap (1 : Fin 3) 2)
  have h120 := permuted ((Equiv.swap (1 : Fin 3) 2).trans (Equiv.swap 0 1))
  have h201 := permuted ((Equiv.swap (0 : Fin 3) 1).trans (Equiv.swap 1 2))
  norm_num [Equiv.swap_apply_def] at h0 h01 h02 h12 h120 h201
  intro i j hij
  rw [abs_of_nonneg (hsign i j hij)]
  fin_cases i <;> fin_cases j <;> try contradiction
  all_goals first | exact h0 | exact h01 | exact h02 | exact h12 | exact h120 | exact h201


theorem rectangle_pair_majorant {p a lo hi c alpha : ℝ}
    (hp : 1 ≤ p) (ha : 0 < a) (hap : a ≤ p)
    (hlo : 0 ≤ lo) (hlohi : lo < hi) (hhi : hi ≤ 1) (halpha : 0 ≤ alpha)
    (hc : 1 ≤ c+2*alpha*lo)
    (hcorner00 : 1+2*lo^a ≤ (c+2*alpha*lo)^a)
    (hcorner10 : 1+hi^a+lo^a ≤ (c+alpha*(hi+lo))^a)
    (hcorner11 : 1+2*hi^a ≤ (c+2*alpha*hi)^a)
    (X : Fin 3 → Fin 3 → ℝ)
    (hmain : ∀ i, 0 ≤ pair X i i)
    (hlower : ∀ i h, i ≠ h → lo*pair X i i ≤ pair X i h)
    (hupper : ∀ i h, i ≠ h → |pair X i h| ≤ hi*pair X i i)
    (i j l : Fin 3) (hij : i ≠ j) (hil : i ≠ l) (hjl : j ≠ l) :
    lpNorm p (pair X i) ≤ c*pair X i i+alpha*(pair X i j+pair X i l) := by
  have hh := rectangle_majorant hp ha hap hlo hlohi hhi halpha hc hcorner00 hcorner10 hcorner11
    (hmain i) (hlower i j hij) ((le_abs_self _).trans (hupper i j hij))
    (hlower i l hil) ((le_abs_self _).trans (hupper i l hil))
  have he : lpNorm p (pair X i) =
      (|pair X i i|^p+|pair X i j|^p+|pair X i l|^p)^(1/p) := by
    simp only [lpNorm,Real.norm_eq_abs]
    congr 1
    fin_cases i <;> fin_cases j <;> fin_cases l <;> try contradiction
    all_goals simp [Fin.sum_univ_three] <;> ring
  rw [he]
  exact hh

end HlawkaSchatten.DiagonalCutoff4

set_option autoImplicit false
namespace HlawkaSchatten.DiagonalCutoff4

theorem rational_powers_le (a b c d m n : ℕ) (hb : 0 < b) (hd : 0 < d)
    (h : a^m*d^n ≤ c^n*b^m) :
    ((a : ℝ)/b)^m ≤ ((c : ℝ)/d)^n := by
  rw [div_pow,div_pow]
  have hb' : (0 : ℝ) < b := by exact_mod_cast hb
  have hd' : (0 : ℝ) < d := by exact_mod_cast hd
  apply (div_le_div_iff₀ (pow_pos hb' m) (pow_pos hd' n)).mpr
  exact_mod_cast h

theorem rectangle_budgets {a lo hi c alpha pl ph : ℝ}
    (hl : lo^a ≤ pl) (hh : hi^a ≤ ph)
    (h00 : 1+2*pl ≤ (c+2*alpha*lo)^a)
    (h10 : 1+ph+pl ≤ (c+alpha*(hi+lo))^a)
    (h11 : 1+2*ph ≤ (c+2*alpha*hi)^a) :
    1+2*lo^a ≤ (c+2*alpha*lo)^a ∧
    1+hi^a+lo^a ≤ (c+alpha*(hi+lo))^a ∧
    1+2*hi^a ≤ (c+2*alpha*hi)^a := by
  constructor
  · linarith only [hl,h00]
  constructor
  · linarith only [hl,hh,h10]
  · linarith only [hh,h11]

theorem sum_two_bounds {x y X Y z : ℝ} (hx : x ≤ X) (hy : y ≤ Y)
    (hz : X+2*Y ≤ z) : x+2*y ≤ z := by
  linarith only [hx,hy,hz]

theorem three_bounds {x X : ℝ} (hx : x ≤ X) (hX : 3*X ≤ 1) : x+x+x ≤ 1 := by
  linarith only [hx,hX]

end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1354_s0_0 (p : ℝ) (hpa : (4313/1024 : ℝ) ≤ p) (hpb : p ≤ (2157/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-72082937/400000000 : ℝ)*x 0 + (5991750057/10000000000 : ℝ)*x 1 + (4813764039/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (72082937/400000000 : ℝ)^2157 ≤ (10571448414763/100000000000000 : ℝ)^1645 := by
    have hnat : (72082937 : ℕ)^2157*100000000000000^1645 ≤ 10571448414763^1645*400000000^2157 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      72082937 400000000 10571448414763 100000000000000 2157 1645 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5991750057/10000000000 : ℝ)^2157 ≤ (10217581607853/20000000000000 : ℝ)^1645 := by
    have hnat : (5991750057 : ℕ)^2157*20000000000000^1645 ≤ 10217581607853^1645*10000000000^2157 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5991750057 10000000000 10217581607853 20000000000000 2157 1645 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4813764039/10000000000 : ℝ)^2157 ≤ (4792580441219/12500000000000 : ℝ)^1645 := by
    have hnat : (4813764039 : ℕ)^2157*12500000000000^1645 ≤ 4792580441219^1645*10000000000^2157 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4813764039 10000000000 4792580441219 12500000000000 2157 1645 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2157/512 : ℝ)) 2157 1645 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-72082937/400000000 : ℝ), (5991750057/10000000000 : ℝ), (4813764039/10000000000 : ℝ)] ![(10571448414763/100000000000000 : ℝ), (10217581607853/20000000000000 : ℝ), (4792580441219/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-72082937/400000000 : ℝ)|^2157 ≤ (10571448414763/100000000000000 : ℝ)^1645
        have hw : |(-72082937/400000000 : ℝ)|=(72082937/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5991750057/10000000000 : ℝ)|^2157 ≤ (10217581607853/20000000000000 : ℝ)^1645
        have hw : |(5991750057/10000000000 : ℝ)|=(5991750057/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4813764039/10000000000 : ℝ)|^2157 ≤ (4792580441219/12500000000000 : ℝ)^1645
        have hw : |(4813764039/10000000000 : ℝ)|=(4813764039/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1354_s0_1 (p : ℝ) (hpa : (4313/1024 : ℝ) ≤ p) (hpb : p ≤ (2157/512 : ℝ)) (x : Fin 3 → ℝ) :
    (1100093839/2000000000 : ℝ)*x 0 + (-1235526731/5000000000 : ℝ)*x 1 + (601720563/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1100093839/2000000000 : ℝ)^2157 ≤ (11416688452687/25000000000000 : ℝ)^1645 := by
    have hnat : (1100093839 : ℕ)^2157*25000000000000^1645 ≤ 11416688452687^1645*2000000000^2157 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1100093839 2000000000 11416688452687 25000000000000 2157 1645 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1235526731/5000000000 : ℝ)^2157 ≤ (15992597785193/100000000000000 : ℝ)^1645 := by
    have hnat : (1235526731 : ℕ)^2157*100000000000000^1645 ≤ 15992597785193^1645*5000000000^2157 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1235526731 5000000000 15992597785193 100000000000000 2157 1645 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (601720563/1250000000 : ℝ)^2157 ≤ (19170324193061/50000000000000 : ℝ)^1645 := by
    have hnat : (601720563 : ℕ)^2157*50000000000000^1645 ≤ 19170324193061^1645*1250000000^2157 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      601720563 1250000000 19170324193061 50000000000000 2157 1645 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2157/512 : ℝ)) 2157 1645 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1100093839/2000000000 : ℝ), (-1235526731/5000000000 : ℝ), (601720563/1250000000 : ℝ)] ![(11416688452687/25000000000000 : ℝ), (15992597785193/100000000000000 : ℝ), (19170324193061/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1100093839/2000000000 : ℝ)|^2157 ≤ (11416688452687/25000000000000 : ℝ)^1645
        have hw : |(1100093839/2000000000 : ℝ)|=(1100093839/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1235526731/5000000000 : ℝ)|^2157 ≤ (15992597785193/100000000000000 : ℝ)^1645
        have hw : |(-1235526731/5000000000 : ℝ)|=(1235526731/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(601720563/1250000000 : ℝ)|^2157 ≤ (19170324193061/50000000000000 : ℝ)^1645
        have hw : |(601720563/1250000000 : ℝ)|=(601720563/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1354_s0_2 (p : ℝ) (hpa : (4313/1024 : ℝ) ≤ p) (hpb : p ≤ (2157/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2750234511/5000000000 : ℝ)*x 0 + (48137641/100000000 : ℝ)*x 1 + (-1235527091/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2750234511/5000000000 : ℝ)^2157 ≤ (45666751927399/100000000000000 : ℝ)^1645 := by
    have hnat : (2750234511 : ℕ)^2157*100000000000000^1645 ≤ 45666751927399^1645*5000000000^2157 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2750234511 5000000000 45666751927399 100000000000000 2157 1645 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (48137641/100000000 : ℝ)^2157 ≤ (4792580520853/12500000000000 : ℝ)^1645 := by
    have hnat : (48137641 : ℕ)^2157*12500000000000^1645 ≤ 4792580520853^1645*100000000^2157 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      48137641 100000000 4792580520853 12500000000000 2157 1645 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1235527091/5000000000 : ℝ)^2157 ≤ (1999075486921/12500000000000 : ℝ)^1645 := by
    have hnat : (1235527091 : ℕ)^2157*12500000000000^1645 ≤ 1999075486921^1645*5000000000^2157 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1235527091 5000000000 1999075486921 12500000000000 2157 1645 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2157/512 : ℝ)) 2157 1645 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2750234511/5000000000 : ℝ), (48137641/100000000 : ℝ), (-1235527091/5000000000 : ℝ)] ![(45666751927399/100000000000000 : ℝ), (4792580520853/12500000000000 : ℝ), (1999075486921/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2750234511/5000000000 : ℝ)|^2157 ≤ (45666751927399/100000000000000 : ℝ)^1645
        have hw : |(2750234511/5000000000 : ℝ)|=(2750234511/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(48137641/100000000 : ℝ)|^2157 ≤ (4792580520853/12500000000000 : ℝ)^1645
        have hw : |(48137641/100000000 : ℝ)|=(48137641/100000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1235527091/5000000000 : ℝ)|^2157 ≤ (1999075486921/12500000000000 : ℝ)^1645
        have hw : |(-1235527091/5000000000 : ℝ)|=(1235527091/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1354_s0_3 (p : ℝ) (hpa : (4313/1024 : ℝ) ≤ p) (hpb : p ≤ (2157/512 : ℝ)) (x : Fin 3 → ℝ) :
    (104423897/250000000 : ℝ)*x 0 + (3105991809/10000000000 : ℝ)*x 1 + (1116902521/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (104423897/250000000 : ℝ)^2157 ≤ (31831270160971/100000000000000 : ℝ)^1645 := by
    have hnat : (104423897 : ℕ)^2157*100000000000000^1645 ≤ 31831270160971^1645*250000000^2157 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      104423897 250000000 31831270160971 100000000000000 2157 1645 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3105991809/10000000000 : ℝ)^2157 ≤ (5396219280931/25000000000000 : ℝ)^1645 := by
    have hnat : (3105991809 : ℕ)^2157*25000000000000^1645 ≤ 5396219280931^1645*10000000000^2157 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3105991809 10000000000 5396219280931 25000000000000 2157 1645 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1116902521/2000000000 : ℝ)^2157 ≤ (9316770540081/20000000000000 : ℝ)^1645 := by
    have hnat : (1116902521 : ℕ)^2157*20000000000000^1645 ≤ 9316770540081^1645*2000000000^2157 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1116902521 2000000000 9316770540081 20000000000000 2157 1645 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2157/512 : ℝ)) 2157 1645 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(104423897/250000000 : ℝ), (3105991809/10000000000 : ℝ), (1116902521/2000000000 : ℝ)] ![(31831270160971/100000000000000 : ℝ), (5396219280931/25000000000000 : ℝ), (9316770540081/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(104423897/250000000 : ℝ)|^2157 ≤ (31831270160971/100000000000000 : ℝ)^1645
        have hw : |(104423897/250000000 : ℝ)|=(104423897/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3105991809/10000000000 : ℝ)|^2157 ≤ (5396219280931/25000000000000 : ℝ)^1645
        have hw : |(3105991809/10000000000 : ℝ)|=(3105991809/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1116902521/2000000000 : ℝ)|^2157 ≤ (9316770540081/20000000000000 : ℝ)^1645
        have hw : |(1116902521/2000000000 : ℝ)|=(1116902521/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1354_s0_4 (p : ℝ) (hpa : (4313/1024 : ℝ) ≤ p) (hpb : p ≤ (2157/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-45161687/250000000 : ℝ)*x 0 + (4844060591/10000000000 : ℝ)*x 1 + (119207427/200000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (45161687/250000000 : ℝ)^2157 ≤ (2121052169501/20000000000000 : ℝ)^1645 := by
    have hnat : (45161687 : ℕ)^2157*20000000000000^1645 ≤ 2121052169501^1645*250000000^2157 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      45161687 250000000 2121052169501 20000000000000 2157 1645 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4844060591/10000000000 : ℝ)^2157 ≤ (1932868216897/5000000000000 : ℝ)^1645 := by
    have hnat : (4844060591 : ℕ)^2157*5000000000000^1645 ≤ 1932868216897^1645*10000000000^2157 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4844060591 10000000000 1932868216897 5000000000000 2157 1645 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (119207427/200000000 : ℝ)^2157 ≤ (5073737480647/10000000000000 : ℝ)^1645 := by
    have hnat : (119207427 : ℕ)^2157*10000000000000^1645 ≤ 5073737480647^1645*200000000^2157 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      119207427 200000000 5073737480647 10000000000000 2157 1645 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2157/512 : ℝ)) 2157 1645 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-45161687/250000000 : ℝ), (4844060591/10000000000 : ℝ), (119207427/200000000 : ℝ)] ![(2121052169501/20000000000000 : ℝ), (1932868216897/5000000000000 : ℝ), (5073737480647/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-45161687/250000000 : ℝ)|^2157 ≤ (2121052169501/20000000000000 : ℝ)^1645
        have hw : |(-45161687/250000000 : ℝ)|=(45161687/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4844060591/10000000000 : ℝ)|^2157 ≤ (1932868216897/5000000000000 : ℝ)^1645
        have hw : |(4844060591/10000000000 : ℝ)|=(4844060591/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(119207427/200000000 : ℝ)|^2157 ≤ (5073737480647/10000000000000 : ℝ)^1645
        have hw : |(119207427/200000000 : ℝ)|=(119207427/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1354_s0_5 (p : ℝ) (hpa : (4313/1024 : ℝ) ≤ p) (hpb : p ≤ (2157/512 : ℝ)) (x : Fin 3 → ℝ) :
    (647419357/1250000000 : ℝ)*x 0 + (-662223991/5000000000 : ℝ)*x 1 + (1192074181/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (647419357/1250000000 : ℝ)^2157 ≤ (5275396016507/12500000000000 : ℝ)^1645 := by
    have hnat : (647419357 : ℕ)^2157*12500000000000^1645 ≤ 5275396016507^1645*1250000000^2157 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      647419357 1250000000 5275396016507 12500000000000 2157 1645 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (662223991/5000000000 : ℝ)^2157 ≤ (110304094089/1562500000000 : ℝ)^1645 := by
    have hnat : (662223991 : ℕ)^2157*1562500000000^1645 ≤ 110304094089^1645*5000000000^2157 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      662223991 5000000000 110304094089 1562500000000 2157 1645 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1192074181/2000000000 : ℝ)^2157 ≤ (10147473967883/20000000000000 : ℝ)^1645 := by
    have hnat : (1192074181 : ℕ)^2157*20000000000000^1645 ≤ 10147473967883^1645*2000000000^2157 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1192074181 2000000000 10147473967883 20000000000000 2157 1645 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2157/512 : ℝ)) 2157 1645 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(647419357/1250000000 : ℝ), (-662223991/5000000000 : ℝ), (1192074181/2000000000 : ℝ)] ![(5275396016507/12500000000000 : ℝ), (110304094089/1562500000000 : ℝ), (10147473967883/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(647419357/1250000000 : ℝ)|^2157 ≤ (5275396016507/12500000000000 : ℝ)^1645
        have hw : |(647419357/1250000000 : ℝ)|=(647419357/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-662223991/5000000000 : ℝ)|^2157 ≤ (110304094089/1562500000000 : ℝ)^1645
        have hw : |(-662223991/5000000000 : ℝ)|=(662223991/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1192074181/2000000000 : ℝ)|^2157 ≤ (10147473967883/20000000000000 : ℝ)^1645
        have hw : |(1192074181/2000000000 : ℝ)|=(1192074181/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1354_s0_6 (p : ℝ) (hpa : (4313/1024 : ℝ) ≤ p) (hpb : p ≤ (2157/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5179354757/10000000000 : ℝ)*x 0 + (5960371439/10000000000 : ℝ)*x 1 + (-1324447279/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5179354757/10000000000 : ℝ)^2157 ≤ (10550791768573/25000000000000 : ℝ)^1645 := by
    have hnat : (5179354757 : ℕ)^2157*25000000000000^1645 ≤ 10550791768573^1645*10000000000^2157 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5179354757 10000000000 10550791768573 25000000000000 2157 1645 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5960371439/10000000000 : ℝ)^2157 ≤ (50737375799881/100000000000000 : ℝ)^1645 := by
    have hnat : (5960371439 : ℕ)^2157*100000000000000^1645 ≤ 50737375799881^1645*10000000000^2157 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5960371439 10000000000 50737375799881 100000000000000 2157 1645 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1324447279/10000000000 : ℝ)^2157 ≤ (7059457108363/100000000000000 : ℝ)^1645 := by
    have hnat : (1324447279 : ℕ)^2157*100000000000000^1645 ≤ 7059457108363^1645*10000000000^2157 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1324447279 10000000000 7059457108363 100000000000000 2157 1645 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2157/512 : ℝ)) 2157 1645 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5179354757/10000000000 : ℝ), (5960371439/10000000000 : ℝ), (-1324447279/10000000000 : ℝ)] ![(10550791768573/25000000000000 : ℝ), (50737375799881/100000000000000 : ℝ), (7059457108363/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5179354757/10000000000 : ℝ)|^2157 ≤ (10550791768573/25000000000000 : ℝ)^1645
        have hw : |(5179354757/10000000000 : ℝ)|=(5179354757/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5960371439/10000000000 : ℝ)|^2157 ≤ (50737375799881/100000000000000 : ℝ)^1645
        have hw : |(5960371439/10000000000 : ℝ)|=(5960371439/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1324447279/10000000000 : ℝ)|^2157 ≤ (7059457108363/100000000000000 : ℝ)^1645
        have hw : |(-1324447279/10000000000 : ℝ)|=(1324447279/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1354_s0_7 (p : ℝ) (hpa : (4313/1024 : ℝ) ≤ p) (hpb : p ≤ (2157/512 : ℝ)) (x : Fin 3 → ℝ) :
    (1046549501/2500000000 : ℝ)*x 0 + (2760384469/5000000000 : ℝ)*x 1 + (3172013347/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1046549501/2500000000 : ℝ)^2157 ≤ (31923654755563/100000000000000 : ℝ)^1645 := by
    have hnat : (1046549501 : ℕ)^2157*100000000000000^1645 ≤ 31923654755563^1645*2500000000^2157 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1046549501 2500000000 31923654755563 100000000000000 2157 1645 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2760384469/5000000000 : ℝ)^2157 ≤ (45887871931481/100000000000000 : ℝ)^1645 := by
    have hnat : (2760384469 : ℕ)^2157*100000000000000^1645 ≤ 45887871931481^1645*5000000000^2157 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2760384469 5000000000 45887871931481 100000000000000 2157 1645 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3172013347/10000000000 : ℝ)^2157 ≤ (22188473305457/100000000000000 : ℝ)^1645 := by
    have hnat : (3172013347 : ℕ)^2157*100000000000000^1645 ≤ 22188473305457^1645*10000000000^2157 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3172013347 10000000000 22188473305457 100000000000000 2157 1645 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2157/512 : ℝ)) 2157 1645 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1046549501/2500000000 : ℝ), (2760384469/5000000000 : ℝ), (3172013347/10000000000 : ℝ)] ![(31923654755563/100000000000000 : ℝ), (45887871931481/100000000000000 : ℝ), (22188473305457/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1046549501/2500000000 : ℝ)|^2157 ≤ (31923654755563/100000000000000 : ℝ)^1645
        have hw : |(1046549501/2500000000 : ℝ)|=(1046549501/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2760384469/5000000000 : ℝ)|^2157 ≤ (45887871931481/100000000000000 : ℝ)^1645
        have hw : |(2760384469/5000000000 : ℝ)|=(2760384469/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3172013347/10000000000 : ℝ)|^2157 ≤ (22188473305457/100000000000000 : ℝ)^1645
        have hw : |(3172013347/10000000000 : ℝ)|=(3172013347/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1354_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4313/1024 : ℝ) ≤ p) (hpb : p ≤ (2157/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (155201657/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    (47/3125 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (5357/20000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (2/5 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (0 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (2/5 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (0 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (2/5 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (0 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (2/5 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (0 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (2/5 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (0 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (2/5 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (0 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hlower 2 1 (by decide)
  have fm0 := f.main 0
  simp only [pair0,pair1,pair2,Pi.add_apply] at fm0
  have fx01 := abs_le.mp (f.maximal 0 1)
  simp only [pair0,pair1,pair2,Pi.add_apply] at fx01
  have fx02 := abs_le.mp (f.maximal 0 2)
  simp only [pair0,pair1,pair2,Pi.add_apply] at fx02
  have fm1 := f.main 1
  simp only [pair0,pair1,pair2,Pi.add_apply] at fm1
  have fx10 := abs_le.mp (f.maximal 1 0)
  simp only [pair0,pair1,pair2,Pi.add_apply] at fx10
  have fx12 := abs_le.mp (f.maximal 1 2)
  simp only [pair0,pair1,pair2,Pi.add_apply] at fx12
  have fm2 := f.main 2
  simp only [pair0,pair1,pair2,Pi.add_apply] at fm2
  have fx20 := abs_le.mp (f.maximal 2 0)
  simp only [pair0,pair1,pair2,Pi.add_apply] at fx20
  have fx21 := abs_le.mp (f.maximal 2 1)
  simp only [pair0,pair1,pair2,Pi.add_apply] at fx21
  have base1 : ((1 : ℝ)*N 0+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    linarith only [f.Ntotal 0]
  have base16 : ((-1 : ℝ)*X 1 1+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    linarith only [(f.coord 1 1).1]
  have base19 : ((1 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    linarith only [(f.coord 1 2).2]
  have base23 : ((1 : ℝ)*X 2 1+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    linarith only [(f.coord 2 1).2]
  have base39 : ((-1 : ℝ)*N 0+(-1 : ℝ)*N 1+(1 : ℝ)*P 2) ≤ (0 : ℝ) := by
    linarith only [f.Ptriangle 2, f.sum]
  have base65 : ((1 : ℝ)*X 0 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 0 0).2]
  have base66 : ((-1 : ℝ)*X 0 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 0 0).1]
  have base67 : ((1 : ℝ)*X 0 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 0 1).2]
  have base68 : ((-1 : ℝ)*X 0 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 0 1).1]
  have base69 : ((1 : ℝ)*X 0 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 0 2).2]
  have base70 : ((-1 : ℝ)*X 0 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 0 2).1]
  have base71 : ((1 : ℝ)*X 1 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 1 0).2]
  have base72 : ((-1 : ℝ)*X 1 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 1 0).1]
  have base73 : ((1 : ℝ)*X 1 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 1 1).2]
  have base74 : ((-1 : ℝ)*X 1 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 1 1).1]
  have base75 : ((1 : ℝ)*X 1 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 1 2).2]
  have base76 : ((-1 : ℝ)*X 1 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 1 2).1]
  have base77 : ((1 : ℝ)*X 2 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 2 0).2]
  have base78 : ((-1 : ℝ)*X 2 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 2 0).1]
  have base79 : ((1 : ℝ)*X 2 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 2 1).2]
  have base80 : ((-1 : ℝ)*X 2 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 2 1).1]
  have base81 : ((1 : ℝ)*X 2 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 2 2).2]
  have base82 : ((-1 : ℝ)*X 2 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 2 2).1]
  have base83 : ((1 : ℝ)*N 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.1 0).2]
  have base84 : ((-1 : ℝ)*N 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.1 0).1]
  have base85 : ((1 : ℝ)*N 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.1 1).2]
  have base86 : ((-1 : ℝ)*N 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.1 1).1]
  have base87 : ((1 : ℝ)*N 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.1 2).2]
  have base88 : ((-1 : ℝ)*N 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.1 2).1]
  have base89 : ((1 : ℝ)*P 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.2.1 0).2]
  have base90 : ((-1 : ℝ)*P 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.2.1 0).1]
  have base91 : ((1 : ℝ)*P 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.2.1 1).2]
  have base92 : ((-1 : ℝ)*P 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.2.1 1).1]
  have base93 : ((1 : ℝ)*P 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.2.1 2).2]
  have base94 : ((-1 : ℝ)*P 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.2.1 2).1]
  have base95 : ((1 : ℝ)*T) ≤ (3 : ℝ) := by
    linarith only [bounds.2.2.2.2]
  have base96 : ((-1 : ℝ)*T) ≤ (3 : ℝ) := by
    linarith only [bounds.2.2.2.1]
  have hpowlo : (0 : ℝ) ^ (4313/1024 : ℝ) ≤ (0 : ℝ) := by
    have hpowers : (0 : ℝ)^4313 ≤ (0 : ℝ)^1024 := by
      have hnat : (0 : ℕ)^4313*1^1024 ≤ 0^1024*1^4313 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        0 1 0 1 4313 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (0 : ℝ)) (X := (0 : ℝ)) (by norm_num) (by norm_num) 4313 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (2/5 : ℝ) ^ (4313/1024 : ℝ) ≤ (2108195497374428721/100000000000000000000 : ℝ) := by
    have hpowers : (2/5 : ℝ)^4313 ≤ (2108195497374428721/100000000000000000000 : ℝ)^1024 := by
      have hnat : (2 : ℕ)^4313*100000000000000000000^1024 ≤ 2108195497374428721^1024*5^4313 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 5 2108195497374428721 100000000000000000000 4313 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2/5 : ℝ)) (X := (2108195497374428721/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4313 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (1 : ℝ) ≤ (1 : ℝ) ^ (4313/1024 : ℝ) := by
    have hpowers : (1 : ℝ)^1024 ≤ (1 : ℝ)^4313 := by
      have hnat : (1 : ℕ)^1024*1^4313 ≤ 1^4313*1^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 1024 4313 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) 4313 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (102108195497374428721/100000000000000000000 : ℝ) ≤ (10049655714914457/10000000000000000 : ℝ) ^ (4313/1024 : ℝ) := by
    have hpowers : (102108195497374428721/100000000000000000000 : ℝ)^1024 ≤ (10049655714914457/10000000000000000 : ℝ)^4313 := by
      have hnat : (102108195497374428721 : ℕ)^1024*10000000000000000^4313 ≤ 10049655714914457^4313*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        102108195497374428721 100000000000000000000 10049655714914457 10000000000000000 1024 4313 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10049655714914457/10000000000000000 : ℝ)) (X := (102108195497374428721/100000000000000000000 : ℝ)) (by norm_num) 4313 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (52108195497374428721/50000000000000000000 : ℝ) ≤ (5049655714914457/5000000000000000 : ℝ) ^ (4313/1024 : ℝ) := by
    have hpowers : (52108195497374428721/50000000000000000000 : ℝ)^1024 ≤ (5049655714914457/5000000000000000 : ℝ)^4313 := by
      have hnat : (52108195497374428721 : ℕ)^1024*5000000000000000^4313 ≤ 5049655714914457^4313*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        52108195497374428721 50000000000000000000 5049655714914457 5000000000000000 1024 4313 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5049655714914457/5000000000000000 : ℝ)) (X := (52108195497374428721/50000000000000000000 : ℝ)) (by norm_num) 4313 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(0 : ℝ) ≤ ((1 : ℝ)+2*(49655714914457/4000000000000000 : ℝ)*(0 : ℝ))^(4313/1024 : ℝ) := by
    rw [show (1 : ℝ)+2*(49655714914457/4000000000000000 : ℝ)*(0 : ℝ)=(1 : ℝ) by norm_num, show 1+2*(0 : ℝ)=(1 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(2108195497374428721/100000000000000000000 : ℝ)+(0 : ℝ) ≤ ((1 : ℝ)+(49655714914457/4000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ)))^(4313/1024 : ℝ) := by
    rw [show (1 : ℝ)+(49655714914457/4000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ))=(10049655714914457/10000000000000000 : ℝ) by norm_num, show 1+(2108195497374428721/100000000000000000000 : ℝ)+(0 : ℝ)=(102108195497374428721/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(2108195497374428721/100000000000000000000 : ℝ) ≤ ((1 : ℝ)+2*(49655714914457/4000000000000000 : ℝ)*(2/5 : ℝ))^(4313/1024 : ℝ) := by
    rw [show (1 : ℝ)+2*(49655714914457/4000000000000000 : ℝ)*(2/5 : ℝ)=(5049655714914457/5000000000000000 : ℝ) by norm_num, show 1+2*(2108195497374428721/100000000000000000000 : ℝ)=(52108195497374428721/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1 : ℝ)*(X 1 0+X 2 0)+(49655714914457/4000000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4313/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (49655714914457/4000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1 : ℝ)*(X 0 1+X 2 1)+(49655714914457/4000000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4313/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (49655714914457/4000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1 : ℝ)*(X 0 2+X 1 2)+(49655714914457/4000000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4313/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (49655714914457/4000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-72082937/400000000 : ℝ)*X 0 0+(5991750057/10000000000 : ℝ)*X 0 1+(4813764039/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1354_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1100093839/2000000000 : ℝ)*X 1 0+(-1235526731/5000000000 : ℝ)*X 1 1+(601720563/1250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1354_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2750234511/5000000000 : ℝ)*X 2 0+(48137641/100000000 : ℝ)*X 2 1+(-1235527091/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1354_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((104423897/250000000 : ℝ)*X 0 0+(3105991809/10000000000 : ℝ)*X 0 1+(1116902521/2000000000 : ℝ)*X 0 2+(104423897/250000000 : ℝ)*X 1 0+(3105991809/10000000000 : ℝ)*X 1 1+(1116902521/2000000000 : ℝ)*X 1 2+(104423897/250000000 : ℝ)*X 2 0+(3105991809/10000000000 : ℝ)*X 2 1+(1116902521/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1354_s0_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-45161687/250000000 : ℝ)*X 0 0+(4844060591/10000000000 : ℝ)*X 0 1+(119207427/200000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1354_s0_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((647419357/1250000000 : ℝ)*X 1 0+(-662223991/5000000000 : ℝ)*X 1 1+(1192074181/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1354_s0_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5179354757/10000000000 : ℝ)*X 2 0+(5960371439/10000000000 : ℝ)*X 2 1+(-1324447279/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1354_s0_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((1046549501/2500000000 : ℝ)*X 0 0+(2760384469/5000000000 : ℝ)*X 0 1+(3172013347/10000000000 : ℝ)*X 0 2+(1046549501/2500000000 : ℝ)*X 1 0+(2760384469/5000000000 : ℝ)*X 1 1+(3172013347/10000000000 : ℝ)*X 1 2+(1046549501/2500000000 : ℝ)*X 2 0+(2760384469/5000000000 : ℝ)*X 2 1+(3172013347/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1354_s0_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (213034786757099017166937/50000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (125206019/100000000000000 : ℝ)*(base1) + (641707/100000000000000 : ℝ)*(base16) + (19853651/2000000000000 : ℝ)*(base19) + (966624401/100000000000000 : ℝ)*(base23) + (95482601/50000000000000 : ℝ)*(upper3) + (313095560016453/50000000000000 : ℝ)*(major0) + (313095560016453/50000000000000 : ℝ)*(major1) + (313095560016453/50000000000000 : ℝ)*(major2) + (424455115313867/50000000000000 : ℝ)*(sp0) + (26528492267581/3125000000000 : ℝ)*(sp1) + (53056986203903/6250000000000 : ℝ)*(sp2) + (403467547241317/100000000000000 : ℝ)*(sp3) + (528093027/20000000000000 : ℝ)*(sp4) + (209963553/12500000000000 : ℝ)*(sp7) + (403469352155761/100000000000000 : ℝ)*(f.failure) + (16978254917737/2000000000000 : ℝ)*(f.sum) + (280768316961021/100000000000000000000000000000 : ℝ)*base65 + (2058432049961021/200000000000000000000000000000 : ℝ)*base67 + (969433249761021/200000000000000000000000000000 : ℝ)*base69 + (1596341788361021/200000000000000000000000000000 : ℝ)*base71 + (41132858538979/100000000000000000000000000000 : ℝ)*base74 + (2418494351361021/200000000000000000000000000000 : ℝ)*base75 + (2071035305161021/200000000000000000000000000000 : ℝ)*base77 + (2866983814561021/200000000000000000000000000000 : ℝ)*base79 + (223379430138979/100000000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base86 + (1/100000000000000 : ℝ)*base88 + (29295977/10000000000000000000000 : ℝ)*base89 + (29295977/10000000000000000000000 : ℝ)*base91 + (29295977/10000000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (588977798932121177337627/100000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (468342583/50000000000000 : ℝ)*(base19) + (579635271/50000000000000 : ℝ)*(base23) + (235738533/100000000000000 : ℝ)*(base39) + (90129739/100000000000000 : ℝ)*(upper3) + (99437347/50000000000000 : ℝ)*(upper5) + (660782040078407/100000000000000 : ℝ)*(major0) + (660782040078407/100000000000000 : ℝ)*(major1) + (330390902169937/50000000000000 : ℝ)*(major2) + (1083165649/50000000000000 : ℝ)*(sp1) + (2321492457/100000000000000 : ℝ)*(sp2) + (11197582124321/1250000000000 : ℝ)*(sp4) + (179160693385843/20000000000000 : ℝ)*(sp5) + (447901662460607/50000000000000 : ℝ)*(sp6) + (53219634768333/12500000000000 : ℝ)*(sp7) + (53219634768333/12500000000000 : ℝ)*(f.failure) + (895806805684213/100000000000000 : ℝ)*(f.sum) + (261646060411583/400000000000000000000000000000 : ℝ)*base66 + (1099348310320791/200000000000000000000000000000 : ℝ)*base68 + (133674614629999/400000000000000000000000000000 : ℝ)*base69 + (86707270879209/200000000000000000000000000000 : ℝ)*base71 + (1999447168411583/400000000000000000000000000000 : ℝ)*base74 + (1386127507829999/400000000000000000000000000000 : ℝ)*base75 + (431344705370001/400000000000000000000000000000 : ℝ)*base78 + (2921497813370001/400000000000000000000000000000 : ℝ)*base80 + (455883072229999/200000000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base86 + (5227781/1250000000000000000000 : ℝ)*base89 + (5227781/1250000000000000000000 : ℝ)*base91 + (5227781/1250000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1354_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4313/1024 : ℝ) ≤ p) (hpb : p ≤ (2157/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (155201657/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (47/3125 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (5357/20000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1354_s0 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1354_s1_0 (p : ℝ) (hpa : (4313/1024 : ℝ) ≤ p) (hpb : p ≤ (2157/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-992579261/5000000000 : ℝ)*x 0 + (5636790877/10000000000 : ℝ)*x 1 + (1010292233/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (992579261/5000000000 : ℝ)^2157 ≤ (12001529972001/100000000000000 : ℝ)^1645 := by
    have hnat : (992579261 : ℕ)^2157*100000000000000^1645 ≤ 12001529972001^1645*5000000000^2157 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      992579261 5000000000 12001529972001 100000000000000 2157 1645 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5636790877/10000000000 : ℝ)^2157 ≤ (5894562378043/12500000000000 : ℝ)^1645 := by
    have hnat : (5636790877 : ℕ)^2157*12500000000000^1645 ≤ 5894562378043^1645*10000000000^2157 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5636790877 10000000000 5894562378043 12500000000000 2157 1645 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1010292233/2000000000 : ℝ)^2157 ≤ (40841970978863/100000000000000 : ℝ)^1645 := by
    have hnat : (1010292233 : ℕ)^2157*100000000000000^1645 ≤ 40841970978863^1645*2000000000^2157 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1010292233 2000000000 40841970978863 100000000000000 2157 1645 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2157/512 : ℝ)) 2157 1645 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-992579261/5000000000 : ℝ), (5636790877/10000000000 : ℝ), (1010292233/2000000000 : ℝ)] ![(12001529972001/100000000000000 : ℝ), (5894562378043/12500000000000 : ℝ), (40841970978863/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-992579261/5000000000 : ℝ)|^2157 ≤ (12001529972001/100000000000000 : ℝ)^1645
        have hw : |(-992579261/5000000000 : ℝ)|=(992579261/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5636790877/10000000000 : ℝ)|^2157 ≤ (5894562378043/12500000000000 : ℝ)^1645
        have hw : |(5636790877/10000000000 : ℝ)|=(5636790877/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1010292233/2000000000 : ℝ)|^2157 ≤ (40841970978863/100000000000000 : ℝ)^1645
        have hw : |(1010292233/2000000000 : ℝ)|=(1010292233/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1354_s1_1 (p : ℝ) (hpa : (4313/1024 : ℝ) ≤ p) (hpb : p ≤ (2157/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2702234311/5000000000 : ℝ)*x 0 + (-2297185701/10000000000 : ℝ)*x 1 + (505146177/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2702234311/5000000000 : ℝ)^2157 ≤ (44624502382171/100000000000000 : ℝ)^1645 := by
    have hnat : (2702234311 : ℕ)^2157*100000000000000^1645 ≤ 44624502382171^1645*5000000000^2157 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2702234311 5000000000 44624502382171 100000000000000 2157 1645 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2297185701/10000000000 : ℝ)^2157 ≤ (2906704041821/20000000000000 : ℝ)^1645 := by
    have hnat : (2297185701 : ℕ)^2157*20000000000000^1645 ≤ 2906704041821^1645*10000000000^2157 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2297185701 10000000000 2906704041821 20000000000000 2157 1645 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (505146177/1000000000 : ℝ)^2157 ≤ (10210494348217/25000000000000 : ℝ)^1645 := by
    have hnat : (505146177 : ℕ)^2157*25000000000000^1645 ≤ 10210494348217^1645*1000000000^2157 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      505146177 1000000000 10210494348217 25000000000000 2157 1645 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2157/512 : ℝ)) 2157 1645 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2702234311/5000000000 : ℝ), (-2297185701/10000000000 : ℝ), (505146177/1000000000 : ℝ)] ![(44624502382171/100000000000000 : ℝ), (2906704041821/20000000000000 : ℝ), (10210494348217/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2702234311/5000000000 : ℝ)|^2157 ≤ (44624502382171/100000000000000 : ℝ)^1645
        have hw : |(2702234311/5000000000 : ℝ)|=(2702234311/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2297185701/10000000000 : ℝ)|^2157 ≤ (2906704041821/20000000000000 : ℝ)^1645
        have hw : |(-2297185701/10000000000 : ℝ)|=(2297185701/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(505146177/1000000000 : ℝ)|^2157 ≤ (10210494348217/25000000000000 : ℝ)^1645
        have hw : |(505146177/1000000000 : ℝ)|=(505146177/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1354_s1_2 (p : ℝ) (hpa : (4313/1024 : ℝ) ≤ p) (hpb : p ≤ (2157/512 : ℝ)) (x : Fin 3 → ℝ) :
    (1351117159/2500000000 : ℝ)*x 0 + (5051461279/10000000000 : ℝ)*x 1 + (-229718631/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1351117159/2500000000 : ℝ)^2157 ≤ (11156125633437/25000000000000 : ℝ)^1645 := by
    have hnat : (1351117159 : ℕ)^2157*25000000000000^1645 ≤ 11156125633437^1645*2500000000^2157 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1351117159 2500000000 11156125633437 25000000000000 2157 1645 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5051461279/10000000000 : ℝ)^2157 ≤ (10210493046863/25000000000000 : ℝ)^1645 := by
    have hnat : (5051461279 : ℕ)^2157*25000000000000^1645 ≤ 10210493046863^1645*10000000000^2157 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5051461279 10000000000 10210493046863 25000000000000 2157 1645 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (229718631/1000000000 : ℝ)^2157 ≤ (2906705052251/20000000000000 : ℝ)^1645 := by
    have hnat : (229718631 : ℕ)^2157*20000000000000^1645 ≤ 2906705052251^1645*1000000000^2157 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      229718631 1000000000 2906705052251 20000000000000 2157 1645 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2157/512 : ℝ)) 2157 1645 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1351117159/2500000000 : ℝ), (5051461279/10000000000 : ℝ), (-229718631/1000000000 : ℝ)] ![(11156125633437/25000000000000 : ℝ), (10210493046863/25000000000000 : ℝ), (2906705052251/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1351117159/2500000000 : ℝ)|^2157 ≤ (11156125633437/25000000000000 : ℝ)^1645
        have hw : |(1351117159/2500000000 : ℝ)|=(1351117159/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5051461279/10000000000 : ℝ)|^2157 ≤ (10210493046863/25000000000000 : ℝ)^1645
        have hw : |(5051461279/10000000000 : ℝ)|=(5051461279/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-229718631/1000000000 : ℝ)|^2157 ≤ (2906705052251/20000000000000 : ℝ)^1645
        have hw : |(-229718631/1000000000 : ℝ)|=(229718631/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1354_s1_3 (p : ℝ) (hpa : (4313/1024 : ℝ) ≤ p) (hpb : p ≤ (2157/512 : ℝ)) (x : Fin 3 → ℝ) :
    (4290166341/10000000000 : ℝ)*x 0 + (1857566241/5000000000 : ℝ)*x 1 + (4946682453/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4290166341/10000000000 : ℝ)^2157 ≤ (4120909850771/12500000000000 : ℝ)^1645 := by
    have hnat : (4290166341 : ℕ)^2157*12500000000000^1645 ≤ 4120909850771^1645*10000000000^2157 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4290166341 10000000000 4120909850771 12500000000000 2157 1645 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1857566241/5000000000 : ℝ)^2157 ≤ (5459595126239/20000000000000 : ℝ)^1645 := by
    have hnat : (1857566241 : ℕ)^2157*20000000000000^1645 ≤ 5459595126239^1645*5000000000^2157 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1857566241 5000000000 5459595126239 20000000000000 2157 1645 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4946682453/10000000000 : ℝ)^2157 ≤ (39734745537571/100000000000000 : ℝ)^1645 := by
    have hnat : (4946682453 : ℕ)^2157*100000000000000^1645 ≤ 39734745537571^1645*10000000000^2157 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4946682453 10000000000 39734745537571 100000000000000 2157 1645 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2157/512 : ℝ)) 2157 1645 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4290166341/10000000000 : ℝ), (1857566241/5000000000 : ℝ), (4946682453/10000000000 : ℝ)] ![(4120909850771/12500000000000 : ℝ), (5459595126239/20000000000000 : ℝ), (39734745537571/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4290166341/10000000000 : ℝ)|^2157 ≤ (4120909850771/12500000000000 : ℝ)^1645
        have hw : |(4290166341/10000000000 : ℝ)|=(4290166341/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1857566241/5000000000 : ℝ)|^2157 ≤ (5459595126239/20000000000000 : ℝ)^1645
        have hw : |(1857566241/5000000000 : ℝ)|=(1857566241/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4946682453/10000000000 : ℝ)|^2157 ≤ (39734745537571/100000000000000 : ℝ)^1645
        have hw : |(4946682453/10000000000 : ℝ)|=(4946682453/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1354_s1_4 (p : ℝ) (hpa : (4313/1024 : ℝ) ≤ p) (hpb : p ≤ (2157/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-397134711/2000000000 : ℝ)*x 0 + (505873837/1000000000 : ℝ)*x 1 + (2814691257/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (397134711/2000000000 : ℝ)^2157 ≤ (600280648071/5000000000000 : ℝ)^1645 := by
    have hnat : (397134711 : ℕ)^2157*5000000000000^1645 ≤ 600280648071^1645*2000000000^2157 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      397134711 2000000000 600280648071 5000000000000 2157 1645 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (505873837/1000000000 : ℝ)^2157 ≤ (20459569365401/50000000000000 : ℝ)^1645 := by
    have hnat : (505873837 : ℕ)^2157*50000000000000^1645 ≤ 20459569365401^1645*1000000000^2157 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      505873837 1000000000 20459569365401 50000000000000 2157 1645 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2814691257/5000000000 : ℝ)^2157 ≤ (47075248295553/100000000000000 : ℝ)^1645 := by
    have hnat : (2814691257 : ℕ)^2157*100000000000000^1645 ≤ 47075248295553^1645*5000000000^2157 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2814691257 5000000000 47075248295553 100000000000000 2157 1645 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2157/512 : ℝ)) 2157 1645 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-397134711/2000000000 : ℝ), (505873837/1000000000 : ℝ), (2814691257/5000000000 : ℝ)] ![(600280648071/5000000000000 : ℝ), (20459569365401/50000000000000 : ℝ), (47075248295553/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-397134711/2000000000 : ℝ)|^2157 ≤ (600280648071/5000000000000 : ℝ)^1645
        have hw : |(-397134711/2000000000 : ℝ)|=(397134711/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(505873837/1000000000 : ℝ)|^2157 ≤ (20459569365401/50000000000000 : ℝ)^1645
        have hw : |(505873837/1000000000 : ℝ)|=(505873837/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2814691257/5000000000 : ℝ)|^2157 ≤ (47075248295553/100000000000000 : ℝ)^1645
        have hw : |(2814691257/5000000000 : ℝ)|=(2814691257/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1354_s1_5 (p : ℝ) (hpa : (4313/1024 : ℝ) ≤ p) (hpb : p ≤ (2157/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5252432399/10000000000 : ℝ)*x 0 + (-859632381/5000000000 : ℝ)*x 1 + (5629382569/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5252432399/10000000000 : ℝ)^2157 ≤ (10746418254699/25000000000000 : ℝ)^1645 := by
    have hnat : (5252432399 : ℕ)^2157*25000000000000^1645 ≤ 10746418254699^1645*10000000000^2157 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5252432399 10000000000 10746418254699 25000000000000 2157 1645 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (859632381/5000000000 : ℝ)^2157 ≤ (9939078068781/100000000000000 : ℝ)^1645 := by
    have hnat : (859632381 : ℕ)^2157*100000000000000^1645 ≤ 9939078068781^1645*5000000000^2157 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      859632381 5000000000 9939078068781 100000000000000 2157 1645 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5629382569/10000000000 : ℝ)^2157 ≤ (23537624449319/50000000000000 : ℝ)^1645 := by
    have hnat : (5629382569 : ℕ)^2157*50000000000000^1645 ≤ 23537624449319^1645*10000000000^2157 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5629382569 10000000000 23537624449319 50000000000000 2157 1645 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2157/512 : ℝ)) 2157 1645 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5252432399/10000000000 : ℝ), (-859632381/5000000000 : ℝ), (5629382569/10000000000 : ℝ)] ![(10746418254699/25000000000000 : ℝ), (9939078068781/100000000000000 : ℝ), (23537624449319/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5252432399/10000000000 : ℝ)|^2157 ≤ (10746418254699/25000000000000 : ℝ)^1645
        have hw : |(5252432399/10000000000 : ℝ)|=(5252432399/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-859632381/5000000000 : ℝ)|^2157 ≤ (9939078068781/100000000000000 : ℝ)^1645
        have hw : |(-859632381/5000000000 : ℝ)|=(859632381/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5629382569/10000000000 : ℝ)|^2157 ≤ (23537624449319/50000000000000 : ℝ)^1645
        have hw : |(5629382569/10000000000 : ℝ)|=(5629382569/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1354_s1_6 (p : ℝ) (hpa : (4313/1024 : ℝ) ≤ p) (hpb : p ≤ (2157/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2626216147/5000000000 : ℝ)*x 0 + (5629382647/10000000000 : ℝ)*x 1 + (-859632399/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2626216147/5000000000 : ℝ)^2157 ≤ (21492835946011/50000000000000 : ℝ)^1645 := by
    have hnat : (2626216147 : ℕ)^2157*50000000000000^1645 ≤ 21492835946011^1645*5000000000^2157 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2626216147 5000000000 21492835946011 50000000000000 2157 1645 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5629382647/10000000000 : ℝ)^2157 ≤ (47075249753923/100000000000000 : ℝ)^1645 := by
    have hnat : (5629382647 : ℕ)^2157*100000000000000^1645 ≤ 47075249753923^1645*10000000000^2157 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5629382647 10000000000 47075249753923 100000000000000 2157 1645 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (859632399/5000000000 : ℝ)^2157 ≤ (9939078341673/100000000000000 : ℝ)^1645 := by
    have hnat : (859632399 : ℕ)^2157*100000000000000^1645 ≤ 9939078341673^1645*5000000000^2157 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      859632399 5000000000 9939078341673 100000000000000 2157 1645 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2157/512 : ℝ)) 2157 1645 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2626216147/5000000000 : ℝ), (5629382647/10000000000 : ℝ), (-859632399/5000000000 : ℝ)] ![(21492835946011/50000000000000 : ℝ), (47075249753923/100000000000000 : ℝ), (9939078341673/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2626216147/5000000000 : ℝ)|^2157 ≤ (21492835946011/50000000000000 : ℝ)^1645
        have hw : |(2626216147/5000000000 : ℝ)|=(2626216147/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5629382647/10000000000 : ℝ)|^2157 ≤ (47075249753923/100000000000000 : ℝ)^1645
        have hw : |(5629382647/10000000000 : ℝ)|=(5629382647/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-859632399/5000000000 : ℝ)|^2157 ≤ (9939078341673/100000000000000 : ℝ)^1645
        have hw : |(-859632399/5000000000 : ℝ)|=(859632399/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1354_s1_7 (p : ℝ) (hpa : (4313/1024 : ℝ) ≤ p) (hpb : p ≤ (2157/512 : ℝ)) (x : Fin 3 → ℝ) :
    (858250097/2000000000 : ℝ)*x 0 + (4931372067/10000000000 : ℝ)*x 1 + (466339717/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (858250097/2000000000 : ℝ)^2157 ≤ (32978203197807/100000000000000 : ℝ)^1645 := by
    have hnat : (858250097 : ℕ)^2157*100000000000000^1645 ≤ 32978203197807^1645*2000000000^2157 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      858250097 2000000000 32978203197807 100000000000000 2157 1645 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4931372067/10000000000 : ℝ)^2157 ≤ (19786781608779/50000000000000 : ℝ)^1645 := by
    have hnat : (4931372067 : ℕ)^2157*50000000000000^1645 ≤ 19786781608779^1645*10000000000^2157 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4931372067 10000000000 19786781608779 50000000000000 2157 1645 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (466339717/1250000000 : ℝ)^2157 ≤ (27448233570389/100000000000000 : ℝ)^1645 := by
    have hnat : (466339717 : ℕ)^2157*100000000000000^1645 ≤ 27448233570389^1645*1250000000^2157 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      466339717 1250000000 27448233570389 100000000000000 2157 1645 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2157/512 : ℝ)) 2157 1645 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(858250097/2000000000 : ℝ), (4931372067/10000000000 : ℝ), (466339717/1250000000 : ℝ)] ![(32978203197807/100000000000000 : ℝ), (19786781608779/50000000000000 : ℝ), (27448233570389/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(858250097/2000000000 : ℝ)|^2157 ≤ (32978203197807/100000000000000 : ℝ)^1645
        have hw : |(858250097/2000000000 : ℝ)|=(858250097/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4931372067/10000000000 : ℝ)|^2157 ≤ (19786781608779/50000000000000 : ℝ)^1645
        have hw : |(4931372067/10000000000 : ℝ)|=(4931372067/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(466339717/1250000000 : ℝ)|^2157 ≤ (27448233570389/100000000000000 : ℝ)^1645
        have hw : |(466339717/1250000000 : ℝ)|=(466339717/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1354_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4313/1024 : ℝ) ≤ p) (hpb : p ≤ (2157/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (155201657/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (5357/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (47/3125 : ℝ)*pair X i i ≤ pair X i h) :
    (7/100 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (4843/25000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (5357/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (47/3125 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (5357/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (47/3125 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (5357/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (47/3125 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (5357/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (47/3125 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (5357/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (47/3125 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (5357/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (47/3125 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hlower 2 1 (by decide)
  have fm0 := f.main 0
  simp only [pair0,pair1,pair2,Pi.add_apply] at fm0
  have fx01 := abs_le.mp (f.maximal 0 1)
  simp only [pair0,pair1,pair2,Pi.add_apply] at fx01
  have fx02 := abs_le.mp (f.maximal 0 2)
  simp only [pair0,pair1,pair2,Pi.add_apply] at fx02
  have fm1 := f.main 1
  simp only [pair0,pair1,pair2,Pi.add_apply] at fm1
  have fx10 := abs_le.mp (f.maximal 1 0)
  simp only [pair0,pair1,pair2,Pi.add_apply] at fx10
  have fx12 := abs_le.mp (f.maximal 1 2)
  simp only [pair0,pair1,pair2,Pi.add_apply] at fx12
  have fm2 := f.main 2
  simp only [pair0,pair1,pair2,Pi.add_apply] at fm2
  have fx20 := abs_le.mp (f.maximal 2 0)
  simp only [pair0,pair1,pair2,Pi.add_apply] at fx20
  have fx21 := abs_le.mp (f.maximal 2 1)
  simp only [pair0,pair1,pair2,Pi.add_apply] at fx21
  have base1 : ((1 : ℝ)*N 0+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    linarith only [f.Ntotal 0]
  have base19 : ((1 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    linarith only [(f.coord 1 2).2]
  have base23 : ((1 : ℝ)*X 2 1+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    linarith only [(f.coord 2 1).2]
  have base65 : ((1 : ℝ)*X 0 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 0 0).2]
  have base66 : ((-1 : ℝ)*X 0 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 0 0).1]
  have base67 : ((1 : ℝ)*X 0 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 0 1).2]
  have base68 : ((-1 : ℝ)*X 0 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 0 1).1]
  have base69 : ((1 : ℝ)*X 0 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 0 2).2]
  have base70 : ((-1 : ℝ)*X 0 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 0 2).1]
  have base71 : ((1 : ℝ)*X 1 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 1 0).2]
  have base72 : ((-1 : ℝ)*X 1 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 1 0).1]
  have base73 : ((1 : ℝ)*X 1 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 1 1).2]
  have base74 : ((-1 : ℝ)*X 1 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 1 1).1]
  have base75 : ((1 : ℝ)*X 1 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 1 2).2]
  have base76 : ((-1 : ℝ)*X 1 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 1 2).1]
  have base77 : ((1 : ℝ)*X 2 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 2 0).2]
  have base78 : ((-1 : ℝ)*X 2 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 2 0).1]
  have base79 : ((1 : ℝ)*X 2 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 2 1).2]
  have base80 : ((-1 : ℝ)*X 2 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 2 1).1]
  have base81 : ((1 : ℝ)*X 2 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 2 2).2]
  have base82 : ((-1 : ℝ)*X 2 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 2 2).1]
  have base83 : ((1 : ℝ)*N 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.1 0).2]
  have base84 : ((-1 : ℝ)*N 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.1 0).1]
  have base85 : ((1 : ℝ)*N 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.1 1).2]
  have base86 : ((-1 : ℝ)*N 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.1 1).1]
  have base87 : ((1 : ℝ)*N 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.1 2).2]
  have base88 : ((-1 : ℝ)*N 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.1 2).1]
  have base89 : ((1 : ℝ)*P 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.2.1 0).2]
  have base90 : ((-1 : ℝ)*P 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.2.1 0).1]
  have base91 : ((1 : ℝ)*P 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.2.1 1).2]
  have base92 : ((-1 : ℝ)*P 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.2.1 1).1]
  have base93 : ((1 : ℝ)*P 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.2.1 2).2]
  have base94 : ((-1 : ℝ)*P 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.2.1 2).1]
  have base95 : ((1 : ℝ)*T) ≤ (3 : ℝ) := by
    linarith only [bounds.2.2.2.2]
  have base96 : ((-1 : ℝ)*T) ≤ (3 : ℝ) := by
    linarith only [bounds.2.2.2.1]
  have hpowlo : (47/3125 : ℝ) ^ (4313/1024 : ℝ) ≤ (525611111553/25000000000000000000 : ℝ) := by
    have hpowers : (47/3125 : ℝ)^4313 ≤ (525611111553/25000000000000000000 : ℝ)^1024 := by
      have hnat : (47 : ℕ)^4313*25000000000000000000^1024 ≤ 525611111553^1024*3125^4313 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        47 3125 525611111553 25000000000000000000 4313 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (47/3125 : ℝ)) (X := (525611111553/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4313 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (5357/20000 : ℝ) ^ (4313/1024 : ℝ) ≤ (194669898609270161/50000000000000000000 : ℝ) := by
    have hpowers : (5357/20000 : ℝ)^4313 ≤ (194669898609270161/50000000000000000000 : ℝ)^1024 := by
      have hnat : (5357 : ℕ)^4313*50000000000000000000^1024 ≤ 194669898609270161^1024*20000^4313 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5357 20000 194669898609270161 50000000000000000000 4313 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (5357/20000 : ℝ)) (X := (194669898609270161/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4313 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (12500000525611111553/12500000000000000000 : ℝ) ≤ (5000000049916603/5000000000000000 : ℝ) ^ (4313/1024 : ℝ) := by
    have hpowers : (12500000525611111553/12500000000000000000 : ℝ)^1024 ≤ (5000000049916603/5000000000000000 : ℝ)^4313 := by
      have hnat : (12500000525611111553 : ℕ)^1024*5000000000000000^4313 ≤ 5000000049916603^4313*12500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12500000525611111553 12500000000000000000 5000000049916603 5000000000000000 1024 4313 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000000049916603/5000000000000000 : ℝ)) (X := (12500000525611111553/12500000000000000000 : ℝ)) (by norm_num) 4313 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (50194670949831493267/50000000000000000000 : ℝ) ≤ (625576883257969/625000000000000 : ℝ) ^ (4313/1024 : ℝ) := by
    have hpowers : (50194670949831493267/50000000000000000000 : ℝ)^1024 ≤ (625576883257969/625000000000000 : ℝ)^4313 := by
      have hnat : (50194670949831493267 : ℕ)^1024*625000000000000^4313 ≤ 625576883257969^4313*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50194670949831493267 50000000000000000000 625576883257969 625000000000000 1024 4313 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (625576883257969/625000000000000 : ℝ)) (X := (50194670949831493267/50000000000000000000 : ℝ)) (by norm_num) 4313 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (25194669898609270161/25000000000000000000 : ℝ) ≤ (5009230082210901/5000000000000000 : ℝ) ^ (4313/1024 : ℝ) := by
    have hpowers : (25194669898609270161/25000000000000000000 : ℝ)^1024 ≤ (5009230082210901/5000000000000000 : ℝ)^4313 := by
      have hnat : (25194669898609270161 : ℕ)^1024*5000000000000000^4313 ≤ 5009230082210901^4313*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25194669898609270161 25000000000000000000 5009230082210901 5000000000000000 1024 4313 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5009230082210901/5000000000000000 : ℝ)) (X := (25194669898609270161/25000000000000000000 : ℝ)) (by norm_num) 4313 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(525611111553/25000000000000000000 : ℝ) ≤ ((126391119293371016251/126405000000000000000 : ℝ)+2*(4615016147149/1264050000000000 : ℝ)*(47/3125 : ℝ))^(4313/1024 : ℝ) := by
    rw [show (126391119293371016251/126405000000000000000 : ℝ)+2*(4615016147149/1264050000000000 : ℝ)*(47/3125 : ℝ)=(5000000049916603/5000000000000000 : ℝ) by norm_num, show 1+2*(525611111553/25000000000000000000 : ℝ)=(12500000525611111553/12500000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(194669898609270161/50000000000000000000 : ℝ)+(525611111553/25000000000000000000 : ℝ) ≤ ((126391119293371016251/126405000000000000000 : ℝ)+(4615016147149/1264050000000000 : ℝ)*((5357/20000 : ℝ)+(47/3125 : ℝ)))^(4313/1024 : ℝ) := by
    rw [show (126391119293371016251/126405000000000000000 : ℝ)+(4615016147149/1264050000000000 : ℝ)*((5357/20000 : ℝ)+(47/3125 : ℝ))=(625576883257969/625000000000000 : ℝ) by norm_num, show 1+(194669898609270161/50000000000000000000 : ℝ)+(525611111553/25000000000000000000 : ℝ)=(50194670949831493267/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(194669898609270161/50000000000000000000 : ℝ) ≤ ((126391119293371016251/126405000000000000000 : ℝ)+2*(4615016147149/1264050000000000 : ℝ)*(5357/20000 : ℝ))^(4313/1024 : ℝ) := by
    rw [show (126391119293371016251/126405000000000000000 : ℝ)+2*(4615016147149/1264050000000000 : ℝ)*(5357/20000 : ℝ)=(5009230082210901/5000000000000000 : ℝ) by norm_num, show 1+2*(194669898609270161/50000000000000000000 : ℝ)=(25194669898609270161/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (126391119293371016251/126405000000000000000 : ℝ)*(X 1 0+X 2 0)+(4615016147149/1264050000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4313/1024 : ℝ)) (lo := (47/3125 : ℝ)) (hi := (5357/20000 : ℝ)) (c := (126391119293371016251/126405000000000000000 : ℝ)) (alpha := (4615016147149/1264050000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (126391119293371016251/126405000000000000000 : ℝ)*(X 0 1+X 2 1)+(4615016147149/1264050000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4313/1024 : ℝ)) (lo := (47/3125 : ℝ)) (hi := (5357/20000 : ℝ)) (c := (126391119293371016251/126405000000000000000 : ℝ)) (alpha := (4615016147149/1264050000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (126391119293371016251/126405000000000000000 : ℝ)*(X 0 2+X 1 2)+(4615016147149/1264050000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4313/1024 : ℝ)) (lo := (47/3125 : ℝ)) (hi := (5357/20000 : ℝ)) (c := (126391119293371016251/126405000000000000000 : ℝ)) (alpha := (4615016147149/1264050000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-992579261/5000000000 : ℝ)*X 0 0+(5636790877/10000000000 : ℝ)*X 0 1+(1010292233/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1354_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2702234311/5000000000 : ℝ)*X 1 0+(-2297185701/10000000000 : ℝ)*X 1 1+(505146177/1000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1354_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1351117159/2500000000 : ℝ)*X 2 0+(5051461279/10000000000 : ℝ)*X 2 1+(-229718631/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1354_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4290166341/10000000000 : ℝ)*X 0 0+(1857566241/5000000000 : ℝ)*X 0 1+(4946682453/10000000000 : ℝ)*X 0 2+(4290166341/10000000000 : ℝ)*X 1 0+(1857566241/5000000000 : ℝ)*X 1 1+(4946682453/10000000000 : ℝ)*X 1 2+(4290166341/10000000000 : ℝ)*X 2 0+(1857566241/5000000000 : ℝ)*X 2 1+(4946682453/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1354_s1_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-397134711/2000000000 : ℝ)*X 0 0+(505873837/1000000000 : ℝ)*X 0 1+(2814691257/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1354_s1_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5252432399/10000000000 : ℝ)*X 1 0+(-859632381/5000000000 : ℝ)*X 1 1+(5629382569/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1354_s1_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2626216147/5000000000 : ℝ)*X 2 0+(5629382647/10000000000 : ℝ)*X 2 1+(-859632399/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1354_s1_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((858250097/2000000000 : ℝ)*X 0 0+(4931372067/10000000000 : ℝ)*X 0 1+(466339717/1250000000 : ℝ)*X 0 2+(858250097/2000000000 : ℝ)*X 1 0+(4931372067/10000000000 : ℝ)*X 1 1+(466339717/1250000000 : ℝ)*X 1 2+(858250097/2000000000 : ℝ)*X 2 0+(4931372067/10000000000 : ℝ)*X 2 1+(466339717/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1354_s1_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1136089308446999587059037753/105337500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (51569303/100000000000000 : ℝ)*(base1) + (916378627/50000000000000 : ℝ)*(base19) + (918591469/50000000000000 : ℝ)*(base23) + (319420921/100000000000000 : ℝ)*(upper3) + (67117223/100000000000000 : ℝ)*(upper5) + (126022996635997/10000000000000 : ℝ)*(major0) + (126022996635997/10000000000000 : ℝ)*(major1) + (126022996635997/10000000000000 : ℝ)*(major2) + (1708452945827327/100000000000000 : ℝ)*(sp0) + (1708462565455017/100000000000000 : ℝ)*(sp1) + (427115640257333/25000000000000 : ℝ)*(sp2) + (202997335310607/25000000000000 : ℝ)*(sp3) + (11503954247/100000000000000 : ℝ)*(sp4) + (5782188217/100000000000000 : ℝ)*(sp7) + (202998793749987/25000000000000 : ℝ)*(f.failure) + (1708464398212271/100000000000000 : ℝ)*(f.sum) + (4757887509061/12640500000000000000000000000 : ℝ)*base66 + (5309868826282312753/1264050000000000000000000000000000 : ℝ)*base68 + (2297194811822437247/1264050000000000000000000000000000 : ℝ)*base69 + (5190855217597537247/1264050000000000000000000000000000 : ℝ)*base71 + (65200795762873/12640500000000000000000000000 : ℝ)*base74 + (2327396534735587247/1264050000000000000000000000000000 : ℝ)*base75 + (5012555178276637247/1264050000000000000000000000000000 : ℝ)*base77 + (11240359996418737247/1264050000000000000000000000000000 : ℝ)*base79 + (5370649893343/3160125000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base88 + (23871541/2500000000000000000000 : ℝ)*base90 + (23871541/2500000000000000000000 : ℝ)*base92 + (23871541/2500000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (20351558328670173769207/3511250000000000000000000000 : ℝ) := by norm_num
    linear_combination (31667219/50000000000000 : ℝ)*(base1) + (1185646591/100000000000000 : ℝ)*(base19) + (1148454651/100000000000000 : ℝ)*(base23) + (135369679/100000000000000 : ℝ)*(upper3) + (5050707/4000000000000 : ℝ)*(upper5) + (646321201279127/50000000000000 : ℝ)*(major0) + (646321201279127/50000000000000 : ℝ)*(major1) + (646321201279127/50000000000000 : ℝ)*(major2) + (1543533037/25000000000000 : ℝ)*(sp1) + (304975119/5000000000000 : ℝ)*(sp2) + (1752405421543321/100000000000000 : ℝ)*(sp4) + (27381218725471/1562500000000 : ℝ)*(sp5) + (1752398110251851/100000000000000 : ℝ)*(sp6) + (832879190369827/100000000000000 : ℝ)*(sp7) + (416439626852133/50000000000000 : ℝ)*(f.failure) + (876202679104441/50000000000000 : ℝ)*(f.sum) + (43363916989999/15800625000000000000000000000 : ℝ)*base65 + (483530238578357123/6320250000000000000000000000000000 : ℝ)*base68 + (5800748140709892877/6320250000000000000000000000000000 : ℝ)*base69 + (8374756924145357123/6320250000000000000000000000000000 : ℝ)*base72 + (567730632999827/126405000000000000000000000000 : ℝ)*base73 + (3166133586844392877/6320250000000000000000000000000000 : ℝ)*base75 + (15654006025575857123/6320250000000000000000000000000000 : ℝ)*base78 + (37454106326669892877/6320250000000000000000000000000000 : ℝ)*base79 + (119445792469111/63202500000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base83 + (1/100000000000000 : ℝ)*base85 + (35584381/5000000000000000000000 : ℝ)*base89 + (35584381/5000000000000000000000 : ℝ)*base91 + (35584381/5000000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
theorem rectangle_w1354_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4313/1024 : ℝ) ≤ p) (hpb : p ≤ (2157/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (155201657/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (5357/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (47/3125 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (7/100 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (4843/25000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1354_s1 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1354_s2_0 (p : ℝ) (hpa : (4313/1024 : ℝ) ≤ p) (hpb : p ≤ (2157/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-2024280219/10000000000 : ℝ)*x 0 + (5476511093/10000000000 : ℝ)*x 1 + (5186664061/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2024280219/10000000000 : ℝ)^2157 ≤ (6156303263681/50000000000000 : ℝ)^1645 := by
    have hnat : (2024280219 : ℕ)^2157*50000000000000^1645 ≤ 6156303263681^1645*10000000000^2157 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2024280219 10000000000 6156303263681 50000000000000 2157 1645 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5476511093/10000000000 : ℝ)^2157 ≤ (45406113082763/100000000000000 : ℝ)^1645 := by
    have hnat : (5476511093 : ℕ)^2157*100000000000000^1645 ≤ 45406113082763^1645*10000000000^2157 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5476511093 10000000000 45406113082763 100000000000000 2157 1645 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5186664061/10000000000 : ℝ)^2157 ≤ (42281280375289/100000000000000 : ℝ)^1645 := by
    have hnat : (5186664061 : ℕ)^2157*100000000000000^1645 ≤ 42281280375289^1645*10000000000^2157 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5186664061 10000000000 42281280375289 100000000000000 2157 1645 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2157/512 : ℝ)) 2157 1645 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2024280219/10000000000 : ℝ), (5476511093/10000000000 : ℝ), (5186664061/10000000000 : ℝ)] ![(6156303263681/50000000000000 : ℝ), (45406113082763/100000000000000 : ℝ), (42281280375289/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2024280219/10000000000 : ℝ)|^2157 ≤ (6156303263681/50000000000000 : ℝ)^1645
        have hw : |(-2024280219/10000000000 : ℝ)|=(2024280219/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5476511093/10000000000 : ℝ)|^2157 ≤ (45406113082763/100000000000000 : ℝ)^1645
        have hw : |(5476511093/10000000000 : ℝ)|=(5476511093/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5186664061/10000000000 : ℝ)|^2157 ≤ (42281280375289/100000000000000 : ℝ)^1645
        have hw : |(5186664061/10000000000 : ℝ)|=(5186664061/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1354_s2_1 (p : ℝ) (hpa : (4313/1024 : ℝ) ≤ p) (hpb : p ≤ (2157/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5365114401/10000000000 : ℝ)*x 0 + (-1086974489/5000000000 : ℝ)*x 1 + (129666611/250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5365114401/10000000000 : ℝ)^2157 ≤ (5524862665989/12500000000000 : ℝ)^1645 := by
    have hnat : (5365114401 : ℕ)^2157*12500000000000^1645 ≤ 5524862665989^1645*10000000000^2157 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5365114401 10000000000 5524862665989 12500000000000 2157 1645 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1086974489/5000000000 : ℝ)^2157 ≤ (6759907118677/50000000000000 : ℝ)^1645 := by
    have hnat : (1086974489 : ℕ)^2157*50000000000000^1645 ≤ 6759907118677^1645*5000000000^2157 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1086974489 5000000000 6759907118677 50000000000000 2157 1645 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (129666611/250000000 : ℝ)^2157 ≤ (42281284426487/100000000000000 : ℝ)^1645 := by
    have hnat : (129666611 : ℕ)^2157*100000000000000^1645 ≤ 42281284426487^1645*250000000^2157 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      129666611 250000000 42281284426487 100000000000000 2157 1645 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2157/512 : ℝ)) 2157 1645 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5365114401/10000000000 : ℝ), (-1086974489/5000000000 : ℝ), (129666611/250000000 : ℝ)] ![(5524862665989/12500000000000 : ℝ), (6759907118677/50000000000000 : ℝ), (42281284426487/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5365114401/10000000000 : ℝ)|^2157 ≤ (5524862665989/12500000000000 : ℝ)^1645
        have hw : |(5365114401/10000000000 : ℝ)|=(5365114401/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1086974489/5000000000 : ℝ)|^2157 ≤ (6759907118677/50000000000000 : ℝ)^1645
        have hw : |(-1086974489/5000000000 : ℝ)|=(1086974489/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(129666611/250000000 : ℝ)|^2157 ≤ (42281284426487/100000000000000 : ℝ)^1645
        have hw : |(129666611/250000000 : ℝ)|=(129666611/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1354_s2_2 (p : ℝ) (hpa : (4313/1024 : ℝ) ≤ p) (hpb : p ≤ (2157/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5365114469/10000000000 : ℝ)*x 0 + (129666609/250000000 : ℝ)*x 1 + (-33967953/156250000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5365114469/10000000000 : ℝ)^2157 ≤ (4419890206247/10000000000000 : ℝ)^1645 := by
    have hnat : (5365114469 : ℕ)^2157*10000000000000^1645 ≤ 4419890206247^1645*10000000000^2157 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5365114469 10000000000 4419890206247 10000000000000 2157 1645 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (129666609/250000000 : ℝ)^2157 ≤ (42281283571353/100000000000000 : ℝ)^1645 := by
    have hnat : (129666609 : ℕ)^2157*100000000000000^1645 ≤ 42281283571353^1645*250000000^2157 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      129666609 250000000 42281283571353 100000000000000 2157 1645 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (33967953/156250000 : ℝ)^2157 ≤ (13519814351519/100000000000000 : ℝ)^1645 := by
    have hnat : (33967953 : ℕ)^2157*100000000000000^1645 ≤ 13519814351519^1645*156250000^2157 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      33967953 156250000 13519814351519 100000000000000 2157 1645 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2157/512 : ℝ)) 2157 1645 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5365114469/10000000000 : ℝ), (129666609/250000000 : ℝ), (-33967953/156250000 : ℝ)] ![(4419890206247/10000000000000 : ℝ), (42281283571353/100000000000000 : ℝ), (13519814351519/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5365114469/10000000000 : ℝ)|^2157 ≤ (4419890206247/10000000000000 : ℝ)^1645
        have hw : |(5365114469/10000000000 : ℝ)|=(5365114469/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(129666609/250000000 : ℝ)|^2157 ≤ (42281283571353/100000000000000 : ℝ)^1645
        have hw : |(129666609/250000000 : ℝ)|=(129666609/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-33967953/156250000 : ℝ)|^2157 ≤ (13519814351519/100000000000000 : ℝ)^1645
        have hw : |(-33967953/156250000 : ℝ)|=(33967953/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1354_s2_3 (p : ℝ) (hpa : (4313/1024 : ℝ) ≤ p) (hpb : p ≤ (2157/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2158779857/5000000000 : ℝ)*x 0 + (1005655283/2500000000 : ℝ)*x 1 + (4632468107/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2158779857/5000000000 : ℝ)^2157 ≤ (6648714303427/20000000000000 : ℝ)^1645 := by
    have hnat : (2158779857 : ℕ)^2157*20000000000000^1645 ≤ 6648714303427^1645*5000000000^2157 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2158779857 5000000000 6648714303427 20000000000000 2157 1645 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1005655283/2500000000 : ℝ)^2157 ≤ (30298009701767/100000000000000 : ℝ)^1645 := by
    have hnat : (1005655283 : ℕ)^2157*100000000000000^1645 ≤ 30298009701767^1645*2500000000^2157 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1005655283 2500000000 30298009701767 100000000000000 2157 1645 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4632468107/10000000000 : ℝ)^2157 ≤ (36458418773073/100000000000000 : ℝ)^1645 := by
    have hnat : (4632468107 : ℕ)^2157*100000000000000^1645 ≤ 36458418773073^1645*10000000000^2157 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4632468107 10000000000 36458418773073 100000000000000 2157 1645 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2157/512 : ℝ)) 2157 1645 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2158779857/5000000000 : ℝ), (1005655283/2500000000 : ℝ), (4632468107/10000000000 : ℝ)] ![(6648714303427/20000000000000 : ℝ), (30298009701767/100000000000000 : ℝ), (36458418773073/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2158779857/5000000000 : ℝ)|^2157 ≤ (6648714303427/20000000000000 : ℝ)^1645
        have hw : |(2158779857/5000000000 : ℝ)|=(2158779857/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1005655283/2500000000 : ℝ)|^2157 ≤ (30298009701767/100000000000000 : ℝ)^1645
        have hw : |(1005655283/2500000000 : ℝ)|=(1005655283/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4632468107/10000000000 : ℝ)|^2157 ≤ (36458418773073/100000000000000 : ℝ)^1645
        have hw : |(4632468107/10000000000 : ℝ)|=(4632468107/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1354_s2_4 (p : ℝ) (hpa : (4313/1024 : ℝ) ≤ p) (hpb : p ≤ (2157/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-1012171387/5000000000 : ℝ)*x 0 + (5188458459/10000000000 : ℝ)*x 1 + (547470073/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1012171387/5000000000 : ℝ)^2157 ≤ (1539138180463/12500000000000 : ℝ)^1645 := by
    have hnat : (1012171387 : ℕ)^2157*12500000000000^1645 ≤ 1539138180463^1645*5000000000^2157 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1012171387 5000000000 1539138180463 12500000000000 2157 1645 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5188458459/10000000000 : ℝ)^2157 ≤ (10575115511263/25000000000000 : ℝ)^1645 := by
    have hnat : (5188458459 : ℕ)^2157*25000000000000^1645 ≤ 10575115511263^1645*10000000000^2157 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5188458459 10000000000 10575115511263 25000000000000 2157 1645 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (547470073/1000000000 : ℝ)^2157 ≤ (363091460013/800000000000 : ℝ)^1645 := by
    have hnat : (547470073 : ℕ)^2157*800000000000^1645 ≤ 363091460013^1645*1000000000^2157 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      547470073 1000000000 363091460013 800000000000 2157 1645 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2157/512 : ℝ)) 2157 1645 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1012171387/5000000000 : ℝ), (5188458459/10000000000 : ℝ), (547470073/1000000000 : ℝ)] ![(1539138180463/12500000000000 : ℝ), (10575115511263/25000000000000 : ℝ), (363091460013/800000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1012171387/5000000000 : ℝ)|^2157 ≤ (1539138180463/12500000000000 : ℝ)^1645
        have hw : |(-1012171387/5000000000 : ℝ)|=(1012171387/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5188458459/10000000000 : ℝ)|^2157 ≤ (10575115511263/25000000000000 : ℝ)^1645
        have hw : |(5188458459/10000000000 : ℝ)|=(5188458459/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(547470073/1000000000 : ℝ)|^2157 ≤ (363091460013/800000000000 : ℝ)^1645
        have hw : |(547470073/1000000000 : ℝ)|=(547470073/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1354_s2_5 (p : ℝ) (hpa : (4313/1024 : ℝ) ≤ p) (hpb : p ≤ (2157/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5290309967/10000000000 : ℝ)*x 0 + (-1885912393/10000000000 : ℝ)*x 1 + (5474700699/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5290309967/10000000000 : ℝ)^2157 ≤ (21696299727751/50000000000000 : ℝ)^1645 := by
    have hnat : (5290309967 : ℕ)^2157*50000000000000^1645 ≤ 21696299727751^1645*10000000000^2157 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5290309967 10000000000 21696299727751 50000000000000 2157 1645 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1885912393/10000000000 : ℝ)^2157 ≤ (5610484187571/50000000000000 : ℝ)^1645 := by
    have hnat : (1885912393 : ℕ)^2157*50000000000000^1645 ≤ 5610484187571^1645*10000000000^2157 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1885912393 10000000000 5610484187571 50000000000000 2157 1645 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5474700699/10000000000 : ℝ)^2157 ≤ (283665201029/625000000000 : ℝ)^1645 := by
    have hnat : (5474700699 : ℕ)^2157*625000000000^1645 ≤ 283665201029^1645*10000000000^2157 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5474700699 10000000000 283665201029 625000000000 2157 1645 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2157/512 : ℝ)) 2157 1645 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5290309967/10000000000 : ℝ), (-1885912393/10000000000 : ℝ), (5474700699/10000000000 : ℝ)] ![(21696299727751/50000000000000 : ℝ), (5610484187571/50000000000000 : ℝ), (283665201029/625000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5290309967/10000000000 : ℝ)|^2157 ≤ (21696299727751/50000000000000 : ℝ)^1645
        have hw : |(5290309967/10000000000 : ℝ)|=(5290309967/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1885912393/10000000000 : ℝ)|^2157 ≤ (5610484187571/50000000000000 : ℝ)^1645
        have hw : |(-1885912393/10000000000 : ℝ)|=(1885912393/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5474700699/10000000000 : ℝ)|^2157 ≤ (283665201029/625000000000 : ℝ)^1645
        have hw : |(5474700699/10000000000 : ℝ)|=(5474700699/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1354_s2_6 (p : ℝ) (hpa : (4313/1024 : ℝ) ≤ p) (hpb : p ≤ (2157/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5290309949/10000000000 : ℝ)*x 0 + (85542199/156250000 : ℝ)*x 1 + (-942956183/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5290309949/10000000000 : ℝ)^2157 ≤ (10848149815477/25000000000000 : ℝ)^1645 := by
    have hnat : (5290309949 : ℕ)^2157*25000000000000^1645 ≤ 10848149815477^1645*10000000000^2157 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5290309949 10000000000 10848149815477 25000000000000 2157 1645 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (85542199/156250000 : ℝ)^2157 ≤ (709163008857/1562500000000 : ℝ)^1645 := by
    have hnat : (85542199 : ℕ)^2157*1562500000000^1645 ≤ 709163008857^1645*156250000^2157 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      85542199 156250000 709163008857 1562500000000 2157 1645 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (942956183/5000000000 : ℝ)^2157 ≤ (5610484082247/50000000000000 : ℝ)^1645 := by
    have hnat : (942956183 : ℕ)^2157*50000000000000^1645 ≤ 5610484082247^1645*5000000000^2157 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      942956183 5000000000 5610484082247 50000000000000 2157 1645 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2157/512 : ℝ)) 2157 1645 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5290309949/10000000000 : ℝ), (85542199/156250000 : ℝ), (-942956183/5000000000 : ℝ)] ![(10848149815477/25000000000000 : ℝ), (709163008857/1562500000000 : ℝ), (5610484082247/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5290309949/10000000000 : ℝ)|^2157 ≤ (10848149815477/25000000000000 : ℝ)^1645
        have hw : |(5290309949/10000000000 : ℝ)|=(5290309949/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(85542199/156250000 : ℝ)|^2157 ≤ (709163008857/1562500000000 : ℝ)^1645
        have hw : |(85542199/156250000 : ℝ)|=(85542199/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-942956183/5000000000 : ℝ)|^2157 ≤ (5610484082247/50000000000000 : ℝ)^1645
        have hw : |(-942956183/5000000000 : ℝ)|=(942956183/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1354_s2_7 (p : ℝ) (hpa : (4313/1024 : ℝ) ≤ p) (hpb : p ≤ (2157/512 : ℝ)) (x : Fin 3 → ℝ) :
    (1079422913/2500000000 : ℝ)*x 0 + (2314346619/5000000000 : ℝ)*x 1 + (2013214803/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1079422913/2500000000 : ℝ)^2157 ≤ (16622451791237/50000000000000 : ℝ)^1645 := by
    have hnat : (1079422913 : ℕ)^2157*50000000000000^1645 ≤ 16622451791237^1645*2500000000^2157 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1079422913 2500000000 16622451791237 50000000000000 2157 1645 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2314346619/5000000000 : ℝ)^2157 ≤ (18209733984349/50000000000000 : ℝ)^1645 := by
    have hnat : (2314346619 : ℕ)^2157*50000000000000^1645 ≤ 18209733984349^1645*5000000000^2157 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2314346619 5000000000 18209733984349 50000000000000 2157 1645 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2013214803/5000000000 : ℝ)^2157 ≤ (6067125687173/20000000000000 : ℝ)^1645 := by
    have hnat : (2013214803 : ℕ)^2157*20000000000000^1645 ≤ 6067125687173^1645*5000000000^2157 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2013214803 5000000000 6067125687173 20000000000000 2157 1645 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2157/512 : ℝ)) 2157 1645 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1079422913/2500000000 : ℝ), (2314346619/5000000000 : ℝ), (2013214803/5000000000 : ℝ)] ![(16622451791237/50000000000000 : ℝ), (18209733984349/50000000000000 : ℝ), (6067125687173/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1079422913/2500000000 : ℝ)|^2157 ≤ (16622451791237/50000000000000 : ℝ)^1645
        have hw : |(1079422913/2500000000 : ℝ)|=(1079422913/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2314346619/5000000000 : ℝ)|^2157 ≤ (18209733984349/50000000000000 : ℝ)^1645
        have hw : |(2314346619/5000000000 : ℝ)|=(2314346619/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2013214803/5000000000 : ℝ)|^2157 ≤ (6067125687173/20000000000000 : ℝ)^1645
        have hw : |(2013214803/5000000000 : ℝ)|=(2013214803/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1354_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4313/1024 : ℝ) ≤ p) (hpb : p ≤ (2157/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (155201657/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (4843/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (7/100 : ℝ)*pair X i i ≤ pair X i h) :
    (9929/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (16057/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (4843/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (7/100 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (4843/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (7/100 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (4843/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (7/100 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (4843/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (7/100 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (4843/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (7/100 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (4843/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (7/100 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hlower 2 1 (by decide)
  have fm0 := f.main 0
  simp only [pair0,pair1,pair2,Pi.add_apply] at fm0
  have fx01 := abs_le.mp (f.maximal 0 1)
  simp only [pair0,pair1,pair2,Pi.add_apply] at fx01
  have fx02 := abs_le.mp (f.maximal 0 2)
  simp only [pair0,pair1,pair2,Pi.add_apply] at fx02
  have fm1 := f.main 1
  simp only [pair0,pair1,pair2,Pi.add_apply] at fm1
  have fx10 := abs_le.mp (f.maximal 1 0)
  simp only [pair0,pair1,pair2,Pi.add_apply] at fx10
  have fx12 := abs_le.mp (f.maximal 1 2)
  simp only [pair0,pair1,pair2,Pi.add_apply] at fx12
  have fm2 := f.main 2
  simp only [pair0,pair1,pair2,Pi.add_apply] at fm2
  have fx20 := abs_le.mp (f.maximal 2 0)
  simp only [pair0,pair1,pair2,Pi.add_apply] at fx20
  have fx21 := abs_le.mp (f.maximal 2 1)
  simp only [pair0,pair1,pair2,Pi.add_apply] at fx21
  have base19 : ((1 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    linarith only [(f.coord 1 2).2]
  have base23 : ((1 : ℝ)*X 2 1+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    linarith only [(f.coord 2 1).2]
  have base65 : ((1 : ℝ)*X 0 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 0 0).2]
  have base66 : ((-1 : ℝ)*X 0 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 0 0).1]
  have base67 : ((1 : ℝ)*X 0 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 0 1).2]
  have base68 : ((-1 : ℝ)*X 0 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 0 1).1]
  have base69 : ((1 : ℝ)*X 0 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 0 2).2]
  have base70 : ((-1 : ℝ)*X 0 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 0 2).1]
  have base71 : ((1 : ℝ)*X 1 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 1 0).2]
  have base72 : ((-1 : ℝ)*X 1 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 1 0).1]
  have base73 : ((1 : ℝ)*X 1 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 1 1).2]
  have base74 : ((-1 : ℝ)*X 1 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 1 1).1]
  have base75 : ((1 : ℝ)*X 1 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 1 2).2]
  have base76 : ((-1 : ℝ)*X 1 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 1 2).1]
  have base77 : ((1 : ℝ)*X 2 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 2 0).2]
  have base78 : ((-1 : ℝ)*X 2 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 2 0).1]
  have base79 : ((1 : ℝ)*X 2 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 2 1).2]
  have base80 : ((-1 : ℝ)*X 2 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 2 1).1]
  have base81 : ((1 : ℝ)*X 2 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 2 2).2]
  have base82 : ((-1 : ℝ)*X 2 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 2 2).1]
  have base83 : ((1 : ℝ)*N 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.1 0).2]
  have base84 : ((-1 : ℝ)*N 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.1 0).1]
  have base85 : ((1 : ℝ)*N 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.1 1).2]
  have base86 : ((-1 : ℝ)*N 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.1 1).1]
  have base87 : ((1 : ℝ)*N 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.1 2).2]
  have base88 : ((-1 : ℝ)*N 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.1 2).1]
  have base89 : ((1 : ℝ)*P 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.2.1 0).2]
  have base90 : ((-1 : ℝ)*P 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.2.1 0).1]
  have base91 : ((1 : ℝ)*P 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.2.1 1).2]
  have base92 : ((-1 : ℝ)*P 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.2.1 1).1]
  have base93 : ((1 : ℝ)*P 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.2.1 2).2]
  have base94 : ((-1 : ℝ)*P 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.2.1 2).1]
  have base95 : ((1 : ℝ)*T) ≤ (3 : ℝ) := by
    linarith only [bounds.2.2.2.2]
  have base96 : ((-1 : ℝ)*T) ≤ (3 : ℝ) := by
    linarith only [bounds.2.2.2.1]
  have hpowlo : (7/100 : ℝ) ^ (4313/1024 : ℝ) ≤ (1366633914245539/100000000000000000000 : ℝ) := by
    have hpowers : (7/100 : ℝ)^4313 ≤ (1366633914245539/100000000000000000000 : ℝ)^1024 := by
      have hnat : (7 : ℕ)^4313*100000000000000000000^1024 ≤ 1366633914245539^1024*100^4313 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        7 100 1366633914245539 100000000000000000000 4313 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (7/100 : ℝ)) (X := (1366633914245539/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4313 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (4843/25000 : ℝ) ^ (4313/1024 : ℝ) ≤ (49729041654957533/50000000000000000000 : ℝ) := by
    have hpowers : (4843/25000 : ℝ)^4313 ≤ (49729041654957533/50000000000000000000 : ℝ)^1024 := by
      have hnat : (4843 : ℕ)^4313*50000000000000000000^1024 ≤ 49729041654957533^1024*25000^4313 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        4843 25000 49729041654957533 50000000000000000000 4313 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (4843/25000 : ℝ)) (X := (49729041654957533/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4313 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50001366633914245539/50000000000000000000 : ℝ) ≤ (5000032446523163/5000000000000000 : ℝ) ^ (4313/1024 : ℝ) := by
    have hpowers : (50001366633914245539/50000000000000000000 : ℝ)^1024 ≤ (5000032446523163/5000000000000000 : ℝ)^4313 := by
      have hnat : (50001366633914245539 : ℕ)^1024*5000000000000000^4313 ≤ 5000032446523163^4313*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50001366633914245539 50000000000000000000 5000032446523163 5000000000000000 1024 4313 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000032446523163/5000000000000000 : ℝ)) (X := (50001366633914245539/50000000000000000000 : ℝ)) (by norm_num) 4313 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (20020164943444832121/20000000000000000000 : ℝ) ≤ (5001196439175347/5000000000000000 : ℝ) ^ (4313/1024 : ℝ) := by
    have hpowers : (20020164943444832121/20000000000000000000 : ℝ)^1024 ≤ (5001196439175347/5000000000000000 : ℝ)^4313 := by
      have hnat : (20020164943444832121 : ℕ)^1024*5000000000000000^4313 ≤ 5001196439175347^4313*20000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        20020164943444832121 20000000000000000000 5001196439175347 5000000000000000 1024 4313 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5001196439175347/5000000000000000 : ℝ)) (X := (20020164943444832121/20000000000000000000 : ℝ)) (by norm_num) 4313 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (25049729041654957533/25000000000000000000 : ℝ) ≤ (5002360431827531/5000000000000000 : ℝ) ^ (4313/1024 : ℝ) := by
    have hpowers : (25049729041654957533/25000000000000000000 : ℝ)^1024 ≤ (5002360431827531/5000000000000000 : ℝ)^4313 := by
      have hnat : (25049729041654957533 : ℕ)^1024*5000000000000000^4313 ≤ 5002360431827531^4313*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25049729041654957533 25000000000000000000 5002360431827531 5000000000000000 1024 4313 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5002360431827531/5000000000000000 : ℝ)) (X := (25049729041654957533/25000000000000000000 : ℝ)) (by norm_num) 4313 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(1366633914245539/100000000000000000000 : ℝ) ≤ ((5153675460937833053/5155000000000000000 : ℝ)+2*(48499693841/25775000000000 : ℝ)*(7/100 : ℝ))^(4313/1024 : ℝ) := by
    rw [show (5153675460937833053/5155000000000000000 : ℝ)+2*(48499693841/25775000000000 : ℝ)*(7/100 : ℝ)=(5000032446523163/5000000000000000 : ℝ) by norm_num, show 1+2*(1366633914245539/100000000000000000000 : ℝ)=(50001366633914245539/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(49729041654957533/50000000000000000000 : ℝ)+(1366633914245539/100000000000000000000 : ℝ) ≤ ((5153675460937833053/5155000000000000000 : ℝ)+(48499693841/25775000000000 : ℝ)*((4843/25000 : ℝ)+(7/100 : ℝ)))^(4313/1024 : ℝ) := by
    rw [show (5153675460937833053/5155000000000000000 : ℝ)+(48499693841/25775000000000 : ℝ)*((4843/25000 : ℝ)+(7/100 : ℝ))=(5001196439175347/5000000000000000 : ℝ) by norm_num, show 1+(49729041654957533/50000000000000000000 : ℝ)+(1366633914245539/100000000000000000000 : ℝ)=(20020164943444832121/20000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(49729041654957533/50000000000000000000 : ℝ) ≤ ((5153675460937833053/5155000000000000000 : ℝ)+2*(48499693841/25775000000000 : ℝ)*(4843/25000 : ℝ))^(4313/1024 : ℝ) := by
    rw [show (5153675460937833053/5155000000000000000 : ℝ)+2*(48499693841/25775000000000 : ℝ)*(4843/25000 : ℝ)=(5002360431827531/5000000000000000 : ℝ) by norm_num, show 1+2*(49729041654957533/50000000000000000000 : ℝ)=(25049729041654957533/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (5153675460937833053/5155000000000000000 : ℝ)*(X 1 0+X 2 0)+(48499693841/25775000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4313/1024 : ℝ)) (lo := (7/100 : ℝ)) (hi := (4843/25000 : ℝ)) (c := (5153675460937833053/5155000000000000000 : ℝ)) (alpha := (48499693841/25775000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (5153675460937833053/5155000000000000000 : ℝ)*(X 0 1+X 2 1)+(48499693841/25775000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4313/1024 : ℝ)) (lo := (7/100 : ℝ)) (hi := (4843/25000 : ℝ)) (c := (5153675460937833053/5155000000000000000 : ℝ)) (alpha := (48499693841/25775000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (5153675460937833053/5155000000000000000 : ℝ)*(X 0 2+X 1 2)+(48499693841/25775000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4313/1024 : ℝ)) (lo := (7/100 : ℝ)) (hi := (4843/25000 : ℝ)) (c := (5153675460937833053/5155000000000000000 : ℝ)) (alpha := (48499693841/25775000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2024280219/10000000000 : ℝ)*X 0 0+(5476511093/10000000000 : ℝ)*X 0 1+(5186664061/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1354_s2_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5365114401/10000000000 : ℝ)*X 1 0+(-1086974489/5000000000 : ℝ)*X 1 1+(129666611/250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1354_s2_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5365114469/10000000000 : ℝ)*X 2 0+(129666609/250000000 : ℝ)*X 2 1+(-33967953/156250000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1354_s2_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2158779857/5000000000 : ℝ)*X 0 0+(1005655283/2500000000 : ℝ)*X 0 1+(4632468107/10000000000 : ℝ)*X 0 2+(2158779857/5000000000 : ℝ)*X 1 0+(1005655283/2500000000 : ℝ)*X 1 1+(4632468107/10000000000 : ℝ)*X 1 2+(2158779857/5000000000 : ℝ)*X 2 0+(1005655283/2500000000 : ℝ)*X 2 1+(4632468107/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1354_s2_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1012171387/5000000000 : ℝ)*X 0 0+(5188458459/10000000000 : ℝ)*X 0 1+(547470073/1000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1354_s2_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5290309967/10000000000 : ℝ)*X 1 0+(-1885912393/10000000000 : ℝ)*X 1 1+(5474700699/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1354_s2_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5290309949/10000000000 : ℝ)*X 2 0+(85542199/156250000 : ℝ)*X 2 1+(-942956183/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1354_s2_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((1079422913/2500000000 : ℝ)*X 0 0+(2314346619/5000000000 : ℝ)*X 0 1+(2013214803/5000000000 : ℝ)*X 0 2+(1079422913/2500000000 : ℝ)*X 1 0+(2314346619/5000000000 : ℝ)*X 1 1+(2013214803/5000000000 : ℝ)*X 1 2+(1079422913/2500000000 : ℝ)*X 2 0+(2314346619/5000000000 : ℝ)*X 2 1+(2013214803/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1354_s2_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1088595288366162861815181771/128875000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (363811067/25000000000000 : ℝ)*(base19) + (725383479/50000000000000 : ℝ)*(base23) + (2586307/10000000000000 : ℝ)*(lower2) + (9865197/5000000000000 : ℝ)*(upper3) + (1214421/781250000000 : ℝ)*(upper5) + (2544957383712269/100000000000000 : ℝ)*(major0) + (2544957383712269/100000000000000 : ℝ)*(major1) + (2544957383712269/100000000000000 : ℝ)*(major2) + (107816183006267/3125000000000 : ℝ)*(sp0) + (345013840906589/10000000000000 : ℝ)*(sp1) + (3450138413543199/100000000000000 : ℝ)*(sp2) + (327952952018257/20000000000000 : ℝ)*(sp3) + (11004054807/50000000000000 : ℝ)*(sp4) + (4930729741/50000000000000 : ℝ)*(sp7) + (1639774621550767/100000000000000 : ℝ)*(f.failure) + (1725069932155079/50000000000000 : ℝ)*(f.sum) + (15941147115853/2577500000000000000000000000 : ℝ)*base65 + (3351065719931372743/515500000000000000000000000000000 : ℝ)*base68 + (4185383003104872743/515500000000000000000000000000000 : ℝ)*base70 + (4469928514226372743/515500000000000000000000000000000 : ℝ)*base72 + (2628755917367/644375000000000000000000000 : ℝ)*base73 + (8320045706142872743/515500000000000000000000000000000 : ℝ)*base76 + (2172513516438127257/515500000000000000000000000000000 : ℝ)*base77 + (3437426518372372743/515500000000000000000000000000000 : ℝ)*base80 + (16687073411829/5155000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base88 + (48020919/10000000000000000000000 : ℝ)*base89 + (48020919/10000000000000000000000 : ℝ)*base91 + (48020919/10000000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (501159530129875495747886211/128875000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (442023843/50000000000000 : ℝ)*(base19) + (7970393/800000000000 : ℝ)*(base23) + (5094587/5000000000000 : ℝ)*(upper3) + (1496573/3125000000000 : ℝ)*(lower4) + (22438131/50000000000000 : ℝ)*(upper5) + (1288486291288857/50000000000000 : ℝ)*(major0) + (1288486291288857/50000000000000 : ℝ)*(major1) + (1288486291288857/50000000000000 : ℝ)*(major2) + (9975699497/100000000000000 : ℝ)*(sp1) + (6176443873/50000000000000 : ℝ)*(sp2) + (873385571108301/25000000000000 : ℝ)*(sp4) + (174676571234301/5000000000000 : ℝ)*(sp5) + (3493528935246333/100000000000000 : ℝ)*(sp6) + (83020137554901/5000000000000 : ℝ)*(sp7) + (83020137554901/5000000000000 : ℝ)*(f.failure) + (873385571108301/25000000000000 : ℝ)*(f.sum) + (61020074683/40273437500000000000000000 : ℝ)*base66 + (2155276087193590421/257750000000000000000000000000000 : ℝ)*base67 + (1658035704452590421/257750000000000000000000000000000 : ℝ)*base69 + (1431775631015840421/257750000000000000000000000000000 : ℝ)*base71 + (1519596375687/2577500000000000000000000000 : ℝ)*base74 + (2897742132467590421/257750000000000000000000000000000 : ℝ)*base75 + (1592006884047340421/257750000000000000000000000000000 : ℝ)*base77 + (2268412611350590421/257750000000000000000000000000000 : ℝ)*base79 + (9537375042673/2577500000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base86 + (6329043/500000000000000000000 : ℝ)*base90 + (6329043/500000000000000000000 : ℝ)*base92 + (6329043/500000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1354_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4313/1024 : ℝ) ≤ p) (hpb : p ≤ (2157/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (155201657/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (4843/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (7/100 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (9929/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (16057/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1354_s2 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1354_b0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4313/1024 : ℝ) ≤ p) (hpb : p ≤ (2157/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (155201657/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (9929/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (16057/100000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1354_s0 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1354_s1 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1354_s2 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4313/1024 : ℝ) ≤ p) (hpb : p ≤ (2157/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (155201657/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (9929/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (16057/100000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1354_b0 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
