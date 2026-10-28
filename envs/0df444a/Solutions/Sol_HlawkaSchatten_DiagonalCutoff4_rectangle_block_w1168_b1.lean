-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1168_b1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T15:43:48.552778+00:00
-- url     : https://prove2.me/submissions/30ac9f5e-ec03-4b27-bb87-6ea21a386fe2

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
theorem support_rectangle_w1168_s3_0 (p : ℝ) (hpa : (1045/256 : ℝ) ≤ p) (hpb : p ≤ (8361/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2150989413/10000000000 : ℝ)*x 0 + (5426550863/10000000000 : ℝ)*x 1 + (2617234807/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2150989413/10000000000 : ℝ)^8361 ≤ (13065904808063/100000000000000 : ℝ)^6313 := by
    have hnat : (2150989413 : ℕ)^8361*100000000000000^6313 ≤ 13065904808063^6313*10000000000^8361 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2150989413 10000000000 13065904808063 100000000000000 8361 6313 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5426550863/10000000000 : ℝ)^8361 ≤ (2781511119821/6250000000000 : ℝ)^6313 := by
    have hnat : (5426550863 : ℕ)^8361*6250000000000^6313 ≤ 2781511119821^6313*10000000000^8361 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5426550863 10000000000 2781511119821 6250000000000 8361 6313 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2617234807/5000000000 : ℝ)^8361 ≤ (2121495863061/5000000000000 : ℝ)^6313 := by
    have hnat : (2617234807 : ℕ)^8361*5000000000000^6313 ≤ 2121495863061^6313*5000000000^8361 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2617234807 5000000000 2121495863061 5000000000000 8361 6313 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8361/2048 : ℝ)) 8361 6313 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2150989413/10000000000 : ℝ), (5426550863/10000000000 : ℝ), (2617234807/5000000000 : ℝ)] ![(13065904808063/100000000000000 : ℝ), (2781511119821/6250000000000 : ℝ), (2121495863061/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2150989413/10000000000 : ℝ)|^8361 ≤ (13065904808063/100000000000000 : ℝ)^6313
        have hw : |(-2150989413/10000000000 : ℝ)|=(2150989413/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5426550863/10000000000 : ℝ)|^8361 ≤ (2781511119821/6250000000000 : ℝ)^6313
        have hw : |(5426550863/10000000000 : ℝ)|=(5426550863/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2617234807/5000000000 : ℝ)|^8361 ≤ (2121495863061/5000000000000 : ℝ)^6313
        have hw : |(2617234807/5000000000 : ℝ)|=(2617234807/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1168_s3_1 (p : ℝ) (hpa : (1045/256 : ℝ) ≤ p) (hpb : p ≤ (8361/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (107063497/200000000 : ℝ)*x 0 + (-2249120063/10000000000 : ℝ)*x 1 + (2617234709/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (107063497/200000000 : ℝ)^8361 ≤ (10927235059321/25000000000000 : ℝ)^6313 := by
    have hnat : (107063497 : ℕ)^8361*25000000000000^6313 ≤ 10927235059321^6313*200000000^8361 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      107063497 200000000 10927235059321 25000000000000 8361 6313 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2249120063/10000000000 : ℝ)^8361 ≤ (3465286148659/25000000000000 : ℝ)^6313 := by
    have hnat : (2249120063 : ℕ)^8361*25000000000000^6313 ≤ 3465286148659^6313*10000000000^8361 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2249120063 10000000000 3465286148659 25000000000000 8361 6313 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2617234709/5000000000 : ℝ)^8361 ≤ (5303739394633/12500000000000 : ℝ)^6313 := by
    have hnat : (2617234709 : ℕ)^8361*12500000000000^6313 ≤ 5303739394633^6313*5000000000^8361 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2617234709 5000000000 5303739394633 12500000000000 8361 6313 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8361/2048 : ℝ)) 8361 6313 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(107063497/200000000 : ℝ), (-2249120063/10000000000 : ℝ), (2617234709/5000000000 : ℝ)] ![(10927235059321/25000000000000 : ℝ), (3465286148659/25000000000000 : ℝ), (5303739394633/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(107063497/200000000 : ℝ)|^8361 ≤ (10927235059321/25000000000000 : ℝ)^6313
        have hw : |(107063497/200000000 : ℝ)|=(107063497/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2249120063/10000000000 : ℝ)|^8361 ≤ (3465286148659/25000000000000 : ℝ)^6313
        have hw : |(-2249120063/10000000000 : ℝ)|=(2249120063/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2617234709/5000000000 : ℝ)|^8361 ≤ (5303739394633/12500000000000 : ℝ)^6313
        have hw : |(2617234709/5000000000 : ℝ)|=(2617234709/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1168_s3_2 (p : ℝ) (hpa : (1045/256 : ℝ) ≤ p) (hpb : p ≤ (8361/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5353174933/10000000000 : ℝ)*x 0 + (327154339/625000000 : ℝ)*x 1 + (-449823989/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5353174933/10000000000 : ℝ)^8361 ≤ (10927235283709/25000000000000 : ℝ)^6313 := by
    have hnat : (5353174933 : ℕ)^8361*25000000000000^6313 ≤ 10927235283709^6313*10000000000^8361 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5353174933 10000000000 10927235283709 25000000000000 8361 6313 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (327154339/625000000 : ℝ)^8361 ≤ (42429915221477/100000000000000 : ℝ)^6313 := by
    have hnat : (327154339 : ℕ)^8361*100000000000000^6313 ≤ 42429915221477^6313*625000000^8361 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      327154339 625000000 42429915221477 100000000000000 8361 6313 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (449823989/2000000000 : ℝ)^8361 ≤ (13861143631493/100000000000000 : ℝ)^6313 := by
    have hnat : (449823989 : ℕ)^8361*100000000000000^6313 ≤ 13861143631493^6313*2000000000^8361 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      449823989 2000000000 13861143631493 100000000000000 8361 6313 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8361/2048 : ℝ)) 8361 6313 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5353174933/10000000000 : ℝ), (327154339/625000000 : ℝ), (-449823989/2000000000 : ℝ)] ![(10927235283709/25000000000000 : ℝ), (42429915221477/100000000000000 : ℝ), (13861143631493/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5353174933/10000000000 : ℝ)|^8361 ≤ (10927235283709/25000000000000 : ℝ)^6313
        have hw : |(5353174933/10000000000 : ℝ)|=(5353174933/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(327154339/625000000 : ℝ)|^8361 ≤ (42429915221477/100000000000000 : ℝ)^6313
        have hw : |(327154339/625000000 : ℝ)|=(327154339/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-449823989/2000000000 : ℝ)|^8361 ≤ (13861143631493/100000000000000 : ℝ)^6313
        have hw : |(-449823989/2000000000 : ℝ)|=(449823989/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1168_s3_3 (p : ℝ) (hpa : (1045/256 : ℝ) ≤ p) (hpb : p ≤ (8361/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4358926397/10000000000 : ℝ)*x 0 + (521382501/1250000000 : ℝ)*x 1 + (9110301/20000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4358926397/10000000000 : ℝ)^8361 ≤ (16647946599549/50000000000000 : ℝ)^6313 := by
    have hnat : (4358926397 : ℕ)^8361*50000000000000^6313 ≤ 16647946599549^6313*10000000000^8361 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4358926397 10000000000 16647946599549 50000000000000 8361 6313 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (521382501/1250000000 : ℝ)^8361 ≤ (15704373264523/50000000000000 : ℝ)^6313 := by
    have hnat : (521382501 : ℕ)^8361*50000000000000^6313 ≤ 15704373264523^6313*1250000000^8361 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      521382501 1250000000 15704373264523 50000000000000 8361 6313 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (9110301/20000000 : ℝ)^8361 ≤ (3529536025649/10000000000000 : ℝ)^6313 := by
    have hnat : (9110301 : ℕ)^8361*10000000000000^6313 ≤ 3529536025649^6313*20000000^8361 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      9110301 20000000 3529536025649 10000000000000 8361 6313 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8361/2048 : ℝ)) 8361 6313 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4358926397/10000000000 : ℝ), (521382501/1250000000 : ℝ), (9110301/20000000 : ℝ)] ![(16647946599549/50000000000000 : ℝ), (15704373264523/50000000000000 : ℝ), (3529536025649/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4358926397/10000000000 : ℝ)|^8361 ≤ (16647946599549/50000000000000 : ℝ)^6313
        have hw : |(4358926397/10000000000 : ℝ)|=(4358926397/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(521382501/1250000000 : ℝ)|^8361 ≤ (15704373264523/50000000000000 : ℝ)^6313
        have hw : |(521382501/1250000000 : ℝ)|=(521382501/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(9110301/20000000 : ℝ)|^8361 ≤ (3529536025649/10000000000000 : ℝ)^6313
        have hw : |(9110301/20000000 : ℝ)|=(9110301/20000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1168_s3_4 (p : ℝ) (hpa : (1045/256 : ℝ) ≤ p) (hpb : p ≤ (8361/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2151006209/10000000000 : ℝ)*x 0 + (2617600751/5000000000 : ℝ)*x 1 + (5425815009/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2151006209/10000000000 : ℝ)^8361 ≤ (3266509982827/25000000000000 : ℝ)^6313 := by
    have hnat : (2151006209 : ℕ)^8361*25000000000000^6313 ≤ 3266509982827^6313*10000000000^8361 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2151006209 10000000000 3266509982827 25000000000000 8361 6313 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2617600751/5000000000 : ℝ)^8361 ≤ (42437774616879/100000000000000 : ℝ)^6313 := by
    have hnat : (2617600751 : ℕ)^8361*100000000000000^6313 ≤ 42437774616879^6313*5000000000^8361 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2617600751 5000000000 42437774616879 100000000000000 8361 6313 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5425815009/10000000000 : ℝ)^8361 ≤ (22248092719643/50000000000000 : ℝ)^6313 := by
    have hnat : (5425815009 : ℕ)^8361*50000000000000^6313 ≤ 22248092719643^6313*10000000000^8361 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5425815009 10000000000 22248092719643 50000000000000 8361 6313 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8361/2048 : ℝ)) 8361 6313 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2151006209/10000000000 : ℝ), (2617600751/5000000000 : ℝ), (5425815009/10000000000 : ℝ)] ![(3266509982827/25000000000000 : ℝ), (42437774616879/100000000000000 : ℝ), (22248092719643/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2151006209/10000000000 : ℝ)|^8361 ≤ (3266509982827/25000000000000 : ℝ)^6313
        have hw : |(-2151006209/10000000000 : ℝ)|=(2151006209/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2617600751/5000000000 : ℝ)|^8361 ≤ (42437774616879/100000000000000 : ℝ)^6313
        have hw : |(2617600751/5000000000 : ℝ)|=(2617600751/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5425815009/10000000000 : ℝ)|^8361 ≤ (22248092719643/50000000000000 : ℝ)^6313
        have hw : |(5425815009/10000000000 : ℝ)|=(5425815009/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1168_s3_5 (p : ℝ) (hpa : (1045/256 : ℝ) ≤ p) (hpb : p ≤ (8361/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (663052509/1250000000 : ℝ)*x 0 + (-205777519/1000000000 : ℝ)*x 1 + (5425814793/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (663052509/1250000000 : ℝ)^8361 ≤ (21591246359403/50000000000000 : ℝ)^6313 := by
    have hnat : (663052509 : ℕ)^8361*50000000000000^6313 ≤ 21591246359403^6313*1250000000^8361 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      663052509 1250000000 21591246359403 50000000000000 8361 6313 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (205777519/1000000000 : ℝ)^8361 ≤ (12321324175547/100000000000000 : ℝ)^6313 := by
    have hnat : (205777519 : ℕ)^8361*100000000000000^6313 ≤ 12321324175547^6313*1000000000^8361 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      205777519 1000000000 12321324175547 100000000000000 8361 6313 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5425814793/10000000000 : ℝ)^8361 ≤ (22248091546627/50000000000000 : ℝ)^6313 := by
    have hnat : (5425814793 : ℕ)^8361*50000000000000^6313 ≤ 22248091546627^6313*10000000000^8361 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5425814793 10000000000 22248091546627 50000000000000 8361 6313 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8361/2048 : ℝ)) 8361 6313 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(663052509/1250000000 : ℝ), (-205777519/1000000000 : ℝ), (5425814793/10000000000 : ℝ)] ![(21591246359403/50000000000000 : ℝ), (12321324175547/100000000000000 : ℝ), (22248091546627/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(663052509/1250000000 : ℝ)|^8361 ≤ (21591246359403/50000000000000 : ℝ)^6313
        have hw : |(663052509/1250000000 : ℝ)|=(663052509/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-205777519/1000000000 : ℝ)|^8361 ≤ (12321324175547/100000000000000 : ℝ)^6313
        have hw : |(-205777519/1000000000 : ℝ)|=(205777519/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5425814793/10000000000 : ℝ)|^8361 ≤ (22248091546627/50000000000000 : ℝ)^6313
        have hw : |(5425814793/10000000000 : ℝ)|=(5425814793/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1168_s3_6 (p : ℝ) (hpa : (1045/256 : ℝ) ≤ p) (hpb : p ≤ (8361/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (66305267/125000000 : ℝ)*x 0 + (169556677/312500000 : ℝ)*x 1 + (-1028887493/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (66305267/125000000 : ℝ)^8361 ≤ (10795626651449/25000000000000 : ℝ)^6313 := by
    have hnat : (66305267 : ℕ)^8361*25000000000000^6313 ≤ 10795626651449^6313*125000000^8361 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      66305267 125000000 10795626651449 25000000000000 8361 6313 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (169556677/312500000 : ℝ)^8361 ≤ (44496170830891/100000000000000 : ℝ)^6313 := by
    have hnat : (169556677 : ℕ)^8361*100000000000000^6313 ≤ 44496170830891^6313*312500000^8361 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      169556677 312500000 44496170830891 100000000000000 8361 6313 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1028887493/5000000000 : ℝ)^8361 ≤ (2464264511559/20000000000000 : ℝ)^6313 := by
    have hnat : (1028887493 : ℕ)^8361*20000000000000^6313 ≤ 2464264511559^6313*5000000000^8361 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1028887493 5000000000 2464264511559 20000000000000 8361 6313 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8361/2048 : ℝ)) 8361 6313 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(66305267/125000000 : ℝ), (169556677/312500000 : ℝ), (-1028887493/5000000000 : ℝ)] ![(10795626651449/25000000000000 : ℝ), (44496170830891/100000000000000 : ℝ), (2464264511559/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(66305267/125000000 : ℝ)|^8361 ≤ (10795626651449/25000000000000 : ℝ)^6313
        have hw : |(66305267/125000000 : ℝ)|=(66305267/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(169556677/312500000 : ℝ)|^8361 ≤ (44496170830891/100000000000000 : ℝ)^6313
        have hw : |(169556677/312500000 : ℝ)|=(169556677/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1028887493/5000000000 : ℝ)|^8361 ≤ (2464264511559/20000000000000 : ℝ)^6313
        have hw : |(-1028887493/5000000000 : ℝ)|=(1028887493/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1168_s3_7 (p : ℝ) (hpa : (1045/256 : ℝ) ≤ p) (hpb : p ≤ (8361/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4358959687/10000000000 : ℝ)*x 0 + (569210907/1250000000 : ℝ)*x 1 + (2086265869/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4358959687/10000000000 : ℝ)^8361 ≤ (16648114990173/50000000000000 : ℝ)^6313 := by
    have hnat : (4358959687 : ℕ)^8361*50000000000000^6313 ≤ 16648114990173^6313*10000000000^8361 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4358959687 10000000000 16648114990173 50000000000000 8361 6313 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (569210907/1250000000 : ℝ)^8361 ≤ (17640172522673/50000000000000 : ℝ)^6313 := by
    have hnat : (569210907 : ℕ)^8361*50000000000000^6313 ≤ 17640172522673^6313*1250000000^8361 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      569210907 1250000000 17640172522673 50000000000000 8361 6313 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2086265869/5000000000 : ℝ)^8361 ≤ (15711712479367/50000000000000 : ℝ)^6313 := by
    have hnat : (2086265869 : ℕ)^8361*50000000000000^6313 ≤ 15711712479367^6313*5000000000^8361 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2086265869 5000000000 15711712479367 50000000000000 8361 6313 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8361/2048 : ℝ)) 8361 6313 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4358959687/10000000000 : ℝ), (569210907/1250000000 : ℝ), (2086265869/5000000000 : ℝ)] ![(16648114990173/50000000000000 : ℝ), (17640172522673/50000000000000 : ℝ), (15711712479367/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4358959687/10000000000 : ℝ)|^8361 ≤ (16648114990173/50000000000000 : ℝ)^6313
        have hw : |(4358959687/10000000000 : ℝ)|=(4358959687/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(569210907/1250000000 : ℝ)|^8361 ≤ (17640172522673/50000000000000 : ℝ)^6313
        have hw : |(569210907/1250000000 : ℝ)|=(569210907/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2086265869/5000000000 : ℝ)|^8361 ≤ (15711712479367/50000000000000 : ℝ)^6313
        have hw : |(2086265869/5000000000 : ℝ)|=(2086265869/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1168_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (1045/256 : ℝ) ≤ p) (hpb : p ≤ (8361/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (149981253/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (8213/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (4593/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (10711/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (1847/12500 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (8213/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (4593/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (8213/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (4593/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (8213/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (4593/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (8213/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (4593/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (8213/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (4593/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (8213/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (4593/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (4593/50000 : ℝ) ^ (1045/256 : ℝ) ≤ (5853959725236989/100000000000000000000 : ℝ) := by
    have hpowers : (4593/50000 : ℝ)^1045 ≤ (5853959725236989/100000000000000000000 : ℝ)^256 := by
      have hnat : (4593 : ℕ)^1045*100000000000000000000^256 ≤ 5853959725236989^256*50000^1045 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        4593 50000 5853959725236989 100000000000000000000 1045 256 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (4593/50000 : ℝ)) (X := (5853959725236989/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 1045 256 (by norm_num) hpowers
    exact h
  have hpowhi : (8213/50000 : ℝ) ^ (1045/256 : ℝ) ≤ (12554700711050701/20000000000000000000 : ℝ) := by
    have hpowers : (8213/50000 : ℝ)^1045 ≤ (12554700711050701/20000000000000000000 : ℝ)^256 := by
      have hnat : (8213 : ℕ)^1045*20000000000000000000^256 ≤ 12554700711050701^256*50000^1045 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        8213 50000 12554700711050701 20000000000000000000 1045 256 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (8213/50000 : ℝ)) (X := (12554700711050701/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 1045 256 (by norm_num) hpowers
    exact h
  have hcorner00 : (50005853959725236989/50000000000000000000 : ℝ) ≤ (5000143401670553/5000000000000000 : ℝ) ^ (1045/256 : ℝ) := by
    have hpowers : (50005853959725236989/50000000000000000000 : ℝ)^256 ≤ (5000143401670553/5000000000000000 : ℝ)^1045 := by
      have hnat : (50005853959725236989 : ℕ)^256*5000000000000000^1045 ≤ 5000143401670553^1045*50000000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50005853959725236989 50000000000000000000 5000143401670553 5000000000000000 256 1045 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000143401670553/5000000000000000 : ℝ)) (X := (50005853959725236989/50000000000000000000 : ℝ)) (by norm_num) 1045 256 (by norm_num) hpowers
    exact h
  have hcorner10 : (50034313731640245247/50000000000000000000 : ℝ) ≤ (5000840386641161/5000000000000000 : ℝ) ^ (1045/256 : ℝ) := by
    have hpowers : (50034313731640245247/50000000000000000000 : ℝ)^256 ≤ (5000840386641161/5000000000000000 : ℝ)^1045 := by
      have hnat : (50034313731640245247 : ℕ)^256*5000000000000000^1045 ≤ 5000840386641161^1045*50000000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50034313731640245247 50000000000000000000 5000840386641161 5000000000000000 256 1045 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000840386641161/5000000000000000 : ℝ)) (X := (50034313731640245247/50000000000000000000 : ℝ)) (by norm_num) 1045 256 (by norm_num) hpowers
    exact h
  have hcorner11 : (10012554700711050701/10000000000000000000 : ℝ) ≤ (5001537371611769/5000000000000000 : ℝ) ^ (1045/256 : ℝ) := by
    have hpowers : (10012554700711050701/10000000000000000000 : ℝ)^256 ≤ (5001537371611769/5000000000000000 : ℝ)^1045 := by
      have hnat : (10012554700711050701 : ℕ)^256*5000000000000000^1045 ≤ 5001537371611769^1045*10000000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10012554700711050701 10000000000000000000 5001537371611769 5000000000000000 256 1045 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5001537371611769/5000000000000000 : ℝ)) (X := (10012554700711050701/10000000000000000000 : ℝ)) (by norm_num) 1045 256 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(5853959725236989/100000000000000000000 : ℝ) ≤ ((4523529152526849193/4525000000000000000 : ℝ)+2*(43561560663/22625000000000 : ℝ)*(4593/50000 : ℝ))^(1045/256 : ℝ) := by
    rw [show (4523529152526849193/4525000000000000000 : ℝ)+2*(43561560663/22625000000000 : ℝ)*(4593/50000 : ℝ)=(5000143401670553/5000000000000000 : ℝ) by norm_num, show 1+2*(5853959725236989/100000000000000000000 : ℝ)=(50005853959725236989/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(12554700711050701/20000000000000000000 : ℝ)+(5853959725236989/100000000000000000000 : ℝ) ≤ ((4523529152526849193/4525000000000000000 : ℝ)+(43561560663/22625000000000 : ℝ)*((8213/50000 : ℝ)+(4593/50000 : ℝ)))^(1045/256 : ℝ) := by
    rw [show (4523529152526849193/4525000000000000000 : ℝ)+(43561560663/22625000000000 : ℝ)*((8213/50000 : ℝ)+(4593/50000 : ℝ))=(5000840386641161/5000000000000000 : ℝ) by norm_num, show 1+(12554700711050701/20000000000000000000 : ℝ)+(5853959725236989/100000000000000000000 : ℝ)=(50034313731640245247/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(12554700711050701/20000000000000000000 : ℝ) ≤ ((4523529152526849193/4525000000000000000 : ℝ)+2*(43561560663/22625000000000 : ℝ)*(8213/50000 : ℝ))^(1045/256 : ℝ) := by
    rw [show (4523529152526849193/4525000000000000000 : ℝ)+2*(43561560663/22625000000000 : ℝ)*(8213/50000 : ℝ)=(5001537371611769/5000000000000000 : ℝ) by norm_num, show 1+2*(12554700711050701/20000000000000000000 : ℝ)=(10012554700711050701/10000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (4523529152526849193/4525000000000000000 : ℝ)*(X 1 0+X 2 0)+(43561560663/22625000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1045/256 : ℝ)) (lo := (4593/50000 : ℝ)) (hi := (8213/50000 : ℝ)) (c := (4523529152526849193/4525000000000000000 : ℝ)) (alpha := (43561560663/22625000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (4523529152526849193/4525000000000000000 : ℝ)*(X 0 1+X 2 1)+(43561560663/22625000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1045/256 : ℝ)) (lo := (4593/50000 : ℝ)) (hi := (8213/50000 : ℝ)) (c := (4523529152526849193/4525000000000000000 : ℝ)) (alpha := (43561560663/22625000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (4523529152526849193/4525000000000000000 : ℝ)*(X 0 2+X 1 2)+(43561560663/22625000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1045/256 : ℝ)) (lo := (4593/50000 : ℝ)) (hi := (8213/50000 : ℝ)) (c := (4523529152526849193/4525000000000000000 : ℝ)) (alpha := (43561560663/22625000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2150989413/10000000000 : ℝ)*X 0 0+(5426550863/10000000000 : ℝ)*X 0 1+(2617234807/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1168_s3_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((107063497/200000000 : ℝ)*X 1 0+(-2249120063/10000000000 : ℝ)*X 1 1+(2617234709/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1168_s3_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5353174933/10000000000 : ℝ)*X 2 0+(327154339/625000000 : ℝ)*X 2 1+(-449823989/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1168_s3_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4358926397/10000000000 : ℝ)*X 0 0+(521382501/1250000000 : ℝ)*X 0 1+(9110301/20000000 : ℝ)*X 0 2+(4358926397/10000000000 : ℝ)*X 1 0+(521382501/1250000000 : ℝ)*X 1 1+(9110301/20000000 : ℝ)*X 1 2+(4358926397/10000000000 : ℝ)*X 2 0+(521382501/1250000000 : ℝ)*X 2 1+(9110301/20000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1168_s3_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2151006209/10000000000 : ℝ)*X 0 0+(2617600751/5000000000 : ℝ)*X 0 1+(5425815009/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1168_s3_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((663052509/1250000000 : ℝ)*X 1 0+(-205777519/1000000000 : ℝ)*X 1 1+(5425814793/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1168_s3_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((66305267/125000000 : ℝ)*X 2 0+(169556677/312500000 : ℝ)*X 2 1+(-1028887493/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1168_s3_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4358959687/10000000000 : ℝ)*X 0 0+(569210907/1250000000 : ℝ)*X 0 1+(2086265869/5000000000 : ℝ)*X 0 2+(4358959687/10000000000 : ℝ)*X 1 0+(569210907/1250000000 : ℝ)*X 1 1+(2086265869/5000000000 : ℝ)*X 1 2+(4358959687/10000000000 : ℝ)*X 2 0+(569210907/1250000000 : ℝ)*X 2 1+(2086265869/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1168_s3_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (5587499865409614596184939/1767578125000000000000000000000 : ℝ) := by norm_num
    linear_combination (458657149/50000000000000 : ℝ)*(base19) + (908742963/100000000000000 : ℝ)*(base23) + (47799481/100000000000000 : ℝ)*(lower2) + (2571013/6250000000000 : ℝ)*(upper3) + (29110093/25000000000000 : ℝ)*(upper5) + (244053861728761/6250000000000 : ℝ)*(major0) + (244053861728761/6250000000000 : ℝ)*(major1) + (244053861728761/6250000000000 : ℝ)*(major2) + (2603070760500251/50000000000000 : ℝ)*(sp0) + (5206155967110571/100000000000000 : ℝ)*(sp1) + (5206155975681907/100000000000000 : ℝ)*(sp2) + (32544500436967/1250000000000 : ℝ)*(sp3) + (960214023/6250000000000 : ℝ)*(sp4) + (6550567949/100000000000000 : ℝ)*(sp7) + (260356658552531/10000000000000 : ℝ)*(f.failure) + (520615688442487/10000000000000 : ℝ)*(f.sum) + (2976394316873/4525000000000000000000000000 : ℝ)*base66 + (84310092109777373/28281250000000000000000000000000 : ℝ)*base67 + (397296420079152373/28281250000000000000000000000000 : ℝ)*base69 + (236856540093058623/28281250000000000000000000000000 : ℝ)*base71 + (2750204074023/4525000000000000000000000000 : ℝ)*base74 + (352172776801339873/28281250000000000000000000000000 : ℝ)*base75 + (341845084396027373/28281250000000000000000000000000 : ℝ)*base77 + (78956930809910127/28281250000000000000000000000000 : ℝ)*base80 + (37195231659077/4525000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base86 + (5701343/1000000000000000000000 : ℝ)*base89 + (5701343/1000000000000000000000 : ℝ)*base91 + (5701343/1000000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (46277679615126821692459737/4525000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (286801617/20000000000000 : ℝ)*(base19) + (1428382563/50000000000000 : ℝ)*(base23) + (71138797/50000000000000 : ℝ)*(upper3) + (526997/2500000000000 : ℝ)*(lower4) + (5781103/4000000000000 : ℝ)*(upper5) + (78698327241001/2000000000000 : ℝ)*(major0) + (78698327241001/2000000000000 : ℝ)*(major1) + (78698327241001/2000000000000 : ℝ)*(major2) + (20922677687/100000000000000 : ℝ)*(sp1) + (8199635553/25000000000000 : ℝ)*(sp2) + (5246226910284339/100000000000000 : ℝ)*(sp4) + (5246204553598567/100000000000000 : ℝ)*(sp5) + (5246191254977001/100000000000000 : ℝ)*(sp6) + (1311802736456019/50000000000000 : ℝ)*(sp7) + (1311802736456019/50000000000000 : ℝ)*(f.failure) + (5246226910284339/100000000000000 : ℝ)*(f.sum) + (1020155027851/181000000000000000000000000 : ℝ)*base66 + (56546845373337807/9050000000000000000000000000000 : ℝ)*base68 + (41967668133787807/9050000000000000000000000000000 : ℝ)*base70 + (110337836938037807/9050000000000000000000000000000 : ℝ)*base72 + (473321319527/181000000000000000000000000 : ℝ)*base73 + (118719213535087807/9050000000000000000000000000000 : ℝ)*base76 + (31639981595137807/9050000000000000000000000000000 : ℝ)*base78 + (54184708258037807/9050000000000000000000000000000 : ℝ)*base80 + (170340103327/90500000000000000000000000 : ℝ)*base82 + (9011807/5000000000000000000000 : ℝ)*base89 + (9011807/5000000000000000000000 : ℝ)*base91 + (9011807/5000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1168_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (1045/256 : ℝ) ≤ p) (hpb : p ≤ (8361/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (149981253/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (8213/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (4593/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (10711/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (1847/12500 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1168_s3 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1168_s4_0 (p : ℝ) (hpa : (1045/256 : ℝ) ≤ p) (hpb : p ≤ (8361/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-1076892207/5000000000 : ℝ)*x 0 + (1350168859/2500000000 : ℝ)*x 1 + (2629258101/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1076892207/5000000000 : ℝ)^8361 ≤ (1308839520489/10000000000000 : ℝ)^6313 := by
    have hnat : (1076892207 : ℕ)^8361*10000000000000^6313 ≤ 1308839520489^6313*5000000000^8361 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1076892207 5000000000 1308839520489 10000000000000 8361 6313 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1350168859/2500000000 : ℝ)^8361 ≤ (22111671704609/50000000000000 : ℝ)^6313 := by
    have hnat : (1350168859 : ℕ)^8361*50000000000000^6313 ≤ 22111671704609^6313*2500000000^8361 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1350168859 2500000000 22111671704609 50000000000000 8361 6313 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2629258101/5000000000 : ℝ)^8361 ≤ (42688261368231/100000000000000 : ℝ)^6313 := by
    have hnat : (2629258101 : ℕ)^8361*100000000000000^6313 ≤ 42688261368231^6313*5000000000^8361 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2629258101 5000000000 42688261368231 100000000000000 8361 6313 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8361/2048 : ℝ)) 8361 6313 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1076892207/5000000000 : ℝ), (1350168859/2500000000 : ℝ), (2629258101/5000000000 : ℝ)] ![(1308839520489/10000000000000 : ℝ), (22111671704609/50000000000000 : ℝ), (42688261368231/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1076892207/5000000000 : ℝ)|^8361 ≤ (1308839520489/10000000000000 : ℝ)^6313
        have hw : |(-1076892207/5000000000 : ℝ)|=(1076892207/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1350168859/2500000000 : ℝ)|^8361 ≤ (22111671704609/50000000000000 : ℝ)^6313
        have hw : |(1350168859/2500000000 : ℝ)|=(1350168859/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2629258101/5000000000 : ℝ)|^8361 ≤ (42688261368231/100000000000000 : ℝ)^6313
        have hw : |(2629258101/5000000000 : ℝ)|=(2629258101/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1168_s4_1 (p : ℝ) (hpa : (1045/256 : ℝ) ≤ p) (hpb : p ≤ (8361/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2673348601/5000000000 : ℝ)*x 0 + (-278251321/1250000000 : ℝ)*x 1 + (657314507/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2673348601/5000000000 : ℝ)^8361 ≤ (43638905524387/100000000000000 : ℝ)^6313 := by
    have hnat : (2673348601 : ℕ)^8361*100000000000000^6313 ≤ 43638905524387^6313*5000000000^8361 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2673348601 5000000000 43638905524387 100000000000000 8361 6313 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (278251321/1250000000 : ℝ)^8361 ≤ (3418208663983/25000000000000 : ℝ)^6313 := by
    have hnat : (278251321 : ℕ)^8361*25000000000000^6313 ≤ 3418208663983^6313*1250000000^8361 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      278251321 1250000000 3418208663983 25000000000000 8361 6313 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (657314507/1250000000 : ℝ)^8361 ≤ (42688259798517/100000000000000 : ℝ)^6313 := by
    have hnat : (657314507 : ℕ)^8361*100000000000000^6313 ≤ 42688259798517^6313*1250000000^8361 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      657314507 1250000000 42688259798517 100000000000000 8361 6313 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8361/2048 : ℝ)) 8361 6313 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2673348601/5000000000 : ℝ), (-278251321/1250000000 : ℝ), (657314507/1250000000 : ℝ)] ![(43638905524387/100000000000000 : ℝ), (3418208663983/25000000000000 : ℝ), (42688259798517/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2673348601/5000000000 : ℝ)|^8361 ≤ (43638905524387/100000000000000 : ℝ)^6313
        have hw : |(2673348601/5000000000 : ℝ)|=(2673348601/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-278251321/1250000000 : ℝ)|^8361 ≤ (3418208663983/25000000000000 : ℝ)^6313
        have hw : |(-278251321/1250000000 : ℝ)|=(278251321/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(657314507/1250000000 : ℝ)|^8361 ≤ (42688259798517/100000000000000 : ℝ)^6313
        have hw : |(657314507/1250000000 : ℝ)|=(657314507/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1168_s4_2 (p : ℝ) (hpa : (1045/256 : ℝ) ≤ p) (hpb : p ≤ (8361/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (106933963/200000000 : ℝ)*x 0 + (5258514987/10000000000 : ℝ)*x 1 + (-1113005361/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (106933963/200000000 : ℝ)^8361 ≤ (43638915771913/100000000000000 : ℝ)^6313 := by
    have hnat : (106933963 : ℕ)^8361*100000000000000^6313 ≤ 43638915771913^6313*200000000^8361 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      106933963 200000000 43638915771913 100000000000000 8361 6313 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5258514987/10000000000 : ℝ)^8361 ≤ (106720620763/250000000000 : ℝ)^6313 := by
    have hnat : (5258514987 : ℕ)^8361*250000000000^6313 ≤ 106720620763^6313*10000000000^8361 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5258514987 10000000000 106720620763 250000000000 8361 6313 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1113005361/5000000000 : ℝ)^8361 ≤ (13672835908711/100000000000000 : ℝ)^6313 := by
    have hnat : (1113005361 : ℕ)^8361*100000000000000^6313 ≤ 13672835908711^6313*5000000000^8361 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1113005361 5000000000 13672835908711 100000000000000 8361 6313 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8361/2048 : ℝ)) 8361 6313 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(106933963/200000000 : ℝ), (5258514987/10000000000 : ℝ), (-1113005361/5000000000 : ℝ)] ![(43638915771913/100000000000000 : ℝ), (106720620763/250000000000 : ℝ), (13672835908711/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(106933963/200000000 : ℝ)|^8361 ≤ (43638915771913/100000000000000 : ℝ)^6313
        have hw : |(106933963/200000000 : ℝ)|=(106933963/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5258514987/10000000000 : ℝ)|^8361 ≤ (106720620763/250000000000 : ℝ)^6313
        have hw : |(5258514987/10000000000 : ℝ)|=(5258514987/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1113005361/5000000000 : ℝ)|^8361 ≤ (13672835908711/100000000000000 : ℝ)^6313
        have hw : |(-1113005361/5000000000 : ℝ)|=(1113005361/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1168_s4_3 (p : ℝ) (hpa : (1045/256 : ℝ) ≤ p) (hpb : p ≤ (8361/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1090149717/2500000000 : ℝ)*x 0 + (4220756097/10000000000 : ℝ)*x 1 + (4505022823/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1090149717/2500000000 : ℝ)^8361 ≤ (3331281393277/10000000000000 : ℝ)^6313 := by
    have hnat : (1090149717 : ℕ)^8361*10000000000000^6313 ≤ 3331281393277^6313*2500000000^8361 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1090149717 2500000000 3331281393277 10000000000000 8361 6313 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4220756097/10000000000 : ℝ)^8361 ≤ (15952660895197/50000000000000 : ℝ)^6313 := by
    have hnat : (4220756097 : ℕ)^8361*50000000000000^6313 ≤ 15952660895197^6313*10000000000^8361 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4220756097 10000000000 15952660895197 50000000000000 8361 6313 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4505022823/10000000000 : ℝ)^8361 ≤ (34781864263947/100000000000000 : ℝ)^6313 := by
    have hnat : (4505022823 : ℕ)^8361*100000000000000^6313 ≤ 34781864263947^6313*10000000000^8361 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4505022823 10000000000 34781864263947 100000000000000 8361 6313 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8361/2048 : ℝ)) 8361 6313 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1090149717/2500000000 : ℝ), (4220756097/10000000000 : ℝ), (4505022823/10000000000 : ℝ)] ![(3331281393277/10000000000000 : ℝ), (15952660895197/50000000000000 : ℝ), (34781864263947/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1090149717/2500000000 : ℝ)|^8361 ≤ (3331281393277/10000000000000 : ℝ)^6313
        have hw : |(1090149717/2500000000 : ℝ)|=(1090149717/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4220756097/10000000000 : ℝ)|^8361 ≤ (15952660895197/50000000000000 : ℝ)^6313
        have hw : |(4220756097/10000000000 : ℝ)|=(4220756097/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4505022823/10000000000 : ℝ)|^8361 ≤ (34781864263947/100000000000000 : ℝ)^6313
        have hw : |(4505022823/10000000000 : ℝ)|=(4505022823/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1168_s4_4 (p : ℝ) (hpa : (1045/256 : ℝ) ≤ p) (hpb : p ≤ (8361/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2153791867/10000000000 : ℝ)*x 0 + (525891747/1000000000 : ℝ)*x 1 + (1080054417/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2153791867/10000000000 : ℝ)^8361 ≤ (6544227594621/50000000000000 : ℝ)^6313 := by
    have hnat : (2153791867 : ℕ)^8361*50000000000000^6313 ≤ 6544227594621^6313*10000000000^8361 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2153791867 10000000000 6544227594621 50000000000000 8361 6313 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (525891747/1000000000 : ℝ)^8361 ≤ (42692575640877/100000000000000 : ℝ)^6313 := by
    have hnat : (525891747 : ℕ)^8361*100000000000000^6313 ≤ 42692575640877^6313*1000000000^8361 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      525891747 1000000000 42692575640877 100000000000000 8361 6313 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1080054417/2000000000 : ℝ)^8361 ≤ (44218969157149/100000000000000 : ℝ)^6313 := by
    have hnat : (1080054417 : ℕ)^8361*100000000000000^6313 ≤ 44218969157149^6313*2000000000^8361 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1080054417 2000000000 44218969157149 100000000000000 8361 6313 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8361/2048 : ℝ)) 8361 6313 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2153791867/10000000000 : ℝ), (525891747/1000000000 : ℝ), (1080054417/2000000000 : ℝ)] ![(6544227594621/50000000000000 : ℝ), (42692575640877/100000000000000 : ℝ), (44218969157149/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2153791867/10000000000 : ℝ)|^8361 ≤ (6544227594621/50000000000000 : ℝ)^6313
        have hw : |(-2153791867/10000000000 : ℝ)|=(2153791867/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(525891747/1000000000 : ℝ)|^8361 ≤ (42692575640877/100000000000000 : ℝ)^6313
        have hw : |(525891747/1000000000 : ℝ)|=(525891747/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1080054417/2000000000 : ℝ)|^8361 ≤ (44218969157149/100000000000000 : ℝ)^6313
        have hw : |(1080054417/2000000000 : ℝ)|=(1080054417/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1168_s4_5 (p : ℝ) (hpa : (1045/256 : ℝ) ≤ p) (hpb : p ≤ (8361/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5310613903/10000000000 : ℝ)*x 0 + (-2084254297/10000000000 : ℝ)*x 1 + (67503401/125000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5310613903/10000000000 : ℝ)^8361 ≤ (21624643079411/50000000000000 : ℝ)^6313 := by
    have hnat : (5310613903 : ℕ)^8361*50000000000000^6313 ≤ 21624643079411^6313*10000000000^8361 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5310613903 10000000000 21624643079411 50000000000000 8361 6313 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2084254297/10000000000 : ℝ)^8361 ≤ (12531744722411/100000000000000 : ℝ)^6313 := by
    have hnat : (2084254297 : ℕ)^8361*100000000000000^6313 ≤ 12531744722411^6313*10000000000^8361 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2084254297 10000000000 12531744722411 100000000000000 8361 6313 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (67503401/125000000 : ℝ)^8361 ≤ (22109484551463/50000000000000 : ℝ)^6313 := by
    have hnat : (67503401 : ℕ)^8361*50000000000000^6313 ≤ 22109484551463^6313*125000000^8361 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      67503401 125000000 22109484551463 50000000000000 8361 6313 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8361/2048 : ℝ)) 8361 6313 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5310613903/10000000000 : ℝ), (-2084254297/10000000000 : ℝ), (67503401/125000000 : ℝ)] ![(21624643079411/50000000000000 : ℝ), (12531744722411/100000000000000 : ℝ), (22109484551463/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5310613903/10000000000 : ℝ)|^8361 ≤ (21624643079411/50000000000000 : ℝ)^6313
        have hw : |(5310613903/10000000000 : ℝ)|=(5310613903/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2084254297/10000000000 : ℝ)|^8361 ≤ (12531744722411/100000000000000 : ℝ)^6313
        have hw : |(-2084254297/10000000000 : ℝ)|=(2084254297/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(67503401/125000000 : ℝ)|^8361 ≤ (22109484551463/50000000000000 : ℝ)^6313
        have hw : |(67503401/125000000 : ℝ)|=(67503401/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1168_s4_6 (p : ℝ) (hpa : (1045/256 : ℝ) ≤ p) (hpb : p ≤ (8361/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5310613801/10000000000 : ℝ)*x 0 + (216010897/400000000 : ℝ)*x 1 + (-416850793/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5310613801/10000000000 : ℝ)^8361 ≤ (2162464252933/5000000000000 : ℝ)^6313 := by
    have hnat : (5310613801 : ℕ)^8361*5000000000000^6313 ≤ 2162464252933^6313*10000000000^8361 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5310613801 10000000000 2162464252933 5000000000000 8361 6313 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (216010897/400000000 : ℝ)^8361 ≤ (44218972844329/100000000000000 : ℝ)^6313 := by
    have hnat : (216010897 : ℕ)^8361*100000000000000^6313 ≤ 44218972844329^6313*400000000^8361 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      216010897 400000000 44218972844329 100000000000000 8361 6313 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (416850793/2000000000 : ℝ)^8361 ≤ (2506348415731/20000000000000 : ℝ)^6313 := by
    have hnat : (416850793 : ℕ)^8361*20000000000000^6313 ≤ 2506348415731^6313*2000000000^8361 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      416850793 2000000000 2506348415731 20000000000000 8361 6313 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8361/2048 : ℝ)) 8361 6313 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5310613801/10000000000 : ℝ), (216010897/400000000 : ℝ), (-416850793/2000000000 : ℝ)] ![(2162464252933/5000000000000 : ℝ), (44218972844329/100000000000000 : ℝ), (2506348415731/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5310613801/10000000000 : ℝ)|^8361 ≤ (2162464252933/5000000000000 : ℝ)^6313
        have hw : |(5310613801/10000000000 : ℝ)|=(5310613801/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(216010897/400000000 : ℝ)|^8361 ≤ (44218972844329/100000000000000 : ℝ)^6313
        have hw : |(216010897/400000000 : ℝ)|=(216010897/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-416850793/2000000000 : ℝ)|^8361 ≤ (2506348415731/20000000000000 : ℝ)^6313
        have hw : |(-416850793/2000000000 : ℝ)|=(416850793/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1168_s4_7 (p : ℝ) (hpa : (1045/256 : ℝ) ≤ p) (hpb : p ≤ (8361/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4360612887/10000000000 : ℝ)*x 0 + (2252109777/5000000000 : ℝ)*x 1 + (844312463/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4360612887/10000000000 : ℝ)^8361 ≤ (1665647788739/5000000000000 : ℝ)^6313 := by
    have hnat : (4360612887 : ℕ)^8361*5000000000000^6313 ≤ 1665647788739^6313*10000000000^8361 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4360612887 10000000000 1665647788739 5000000000000 8361 6313 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2252109777/5000000000 : ℝ)^8361 ≤ (34773650792721/100000000000000 : ℝ)^6313 := by
    have hnat : (2252109777 : ℕ)^8361*100000000000000^6313 ≤ 34773650792721^6313*5000000000^8361 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2252109777 5000000000 34773650792721 100000000000000 8361 6313 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (844312463/2000000000 : ℝ)^8361 ≤ (31913393420509/100000000000000 : ℝ)^6313 := by
    have hnat : (844312463 : ℕ)^8361*100000000000000^6313 ≤ 31913393420509^6313*2000000000^8361 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      844312463 2000000000 31913393420509 100000000000000 8361 6313 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8361/2048 : ℝ)) 8361 6313 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4360612887/10000000000 : ℝ), (2252109777/5000000000 : ℝ), (844312463/2000000000 : ℝ)] ![(1665647788739/5000000000000 : ℝ), (34773650792721/100000000000000 : ℝ), (31913393420509/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4360612887/10000000000 : ℝ)|^8361 ≤ (1665647788739/5000000000000 : ℝ)^6313
        have hw : |(4360612887/10000000000 : ℝ)|=(4360612887/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2252109777/5000000000 : ℝ)|^8361 ≤ (34773650792721/100000000000000 : ℝ)^6313
        have hw : |(2252109777/5000000000 : ℝ)|=(2252109777/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(844312463/2000000000 : ℝ)|^8361 ≤ (31913393420509/100000000000000 : ℝ)^6313
        have hw : |(844312463/2000000000 : ℝ)|=(844312463/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1168_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (1045/256 : ℝ) ≤ p) (hpb : p ≤ (8361/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (149981253/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1847/12500 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10711/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (1403/12500 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (7117/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (1847/12500 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (10711/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (1847/12500 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (10711/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (1847/12500 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (10711/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (1847/12500 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (10711/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (1847/12500 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (10711/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (1847/12500 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (10711/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (10711/100000 : ℝ) ^ (1045/256 : ℝ) ≤ (1369764271503741/12500000000000000000 : ℝ) := by
    have hpowers : (10711/100000 : ℝ)^1045 ≤ (1369764271503741/12500000000000000000 : ℝ)^256 := by
      have hnat : (10711 : ℕ)^1045*12500000000000000000^256 ≤ 1369764271503741^256*100000^1045 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10711 100000 1369764271503741 12500000000000000000 1045 256 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (10711/100000 : ℝ)) (X := (1369764271503741/12500000000000000000 : ℝ)) (by norm_num) (by norm_num) 1045 256 (by norm_num) hpowers
    exact h
  have hpowhi : (1847/12500 : ℝ) ^ (1045/256 : ℝ) ≤ (20373950518920249/50000000000000000000 : ℝ) := by
    have hpowers : (1847/12500 : ℝ)^1045 ≤ (20373950518920249/50000000000000000000 : ℝ)^256 := by
      have hnat : (1847 : ℕ)^1045*50000000000000000000^256 ≤ 20373950518920249^256*12500^1045 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1847 12500 20373950518920249 50000000000000000000 1045 256 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1847/12500 : ℝ)) (X := (20373950518920249/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 1045 256 (by norm_num) hpowers
    exact h
  have hcorner00 : (6251369764271503741/6250000000000000000 : ℝ) ≤ (312516776585881/312500000000000 : ℝ) ^ (1045/256 : ℝ) := by
    have hpowers : (6251369764271503741/6250000000000000000 : ℝ)^256 ≤ (312516776585881/312500000000000 : ℝ)^1045 := by
      have hnat : (6251369764271503741 : ℕ)^256*312500000000000^1045 ≤ 312516776585881^1045*6250000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6251369764271503741 6250000000000000000 312516776585881 312500000000000 256 1045 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (312516776585881/312500000000000 : ℝ)) (X := (6251369764271503741/6250000000000000000 : ℝ)) (by norm_num) 1045 256 (by norm_num) hpowers
    exact h
  have hcorner10 : (50025853007604935213/50000000000000000000 : ℝ) ≤ (10001266426498673/10000000000000000 : ℝ) ^ (1045/256 : ℝ) := by
    have hpowers : (50025853007604935213/50000000000000000000 : ℝ)^256 ≤ (10001266426498673/10000000000000000 : ℝ)^1045 := by
      have hnat : (50025853007604935213 : ℕ)^256*10000000000000000^1045 ≤ 10001266426498673^1045*50000000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50025853007604935213 50000000000000000000 10001266426498673 10000000000000000 256 1045 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001266426498673/10000000000000000 : ℝ)) (X := (50025853007604935213/50000000000000000000 : ℝ)) (by norm_num) 1045 256 (by norm_num) hpowers
    exact h
  have hcorner11 : (25020373950518920249/25000000000000000000 : ℝ) ≤ (5000998001124577/5000000000000000 : ℝ) ^ (1045/256 : ℝ) := by
    have hpowers : (25020373950518920249/25000000000000000000 : ℝ)^256 ≤ (5000998001124577/5000000000000000 : ℝ)^1045 := by
      have hnat : (25020373950518920249 : ℕ)^256*5000000000000000^1045 ≤ 5000998001124577^1045*25000000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25020373950518920249 25000000000000000000 5000998001124577 5000000000000000 256 1045 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000998001124577/5000000000000000 : ℝ)) (X := (25020373950518920249/25000000000000000000 : ℝ)) (by norm_num) 1045 256 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(1369764271503741/12500000000000000000 : ℝ) ≤ ((6772758887760766083/6775000000000000000 : ℝ)+2*(243191916827/135500000000000 : ℝ)*(10711/100000 : ℝ))^(1045/256 : ℝ) := by
    rw [show (6772758887760766083/6775000000000000000 : ℝ)+2*(243191916827/135500000000000 : ℝ)*(10711/100000 : ℝ)=(312516776585881/312500000000000 : ℝ) by norm_num, show 1+2*(1369764271503741/12500000000000000000 : ℝ)=(6251369764271503741/6250000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(20373950518920249/50000000000000000000 : ℝ)+(1369764271503741/12500000000000000000 : ℝ) ≤ ((6772758887760766083/6775000000000000000 : ℝ)+(243191916827/135500000000000 : ℝ)*((1847/12500 : ℝ)+(10711/100000 : ℝ)))^(1045/256 : ℝ) := by
    rw [show (6772758887760766083/6775000000000000000 : ℝ)+(243191916827/135500000000000 : ℝ)*((1847/12500 : ℝ)+(10711/100000 : ℝ))=(10001266426498673/10000000000000000 : ℝ) by norm_num, show 1+(20373950518920249/50000000000000000000 : ℝ)+(1369764271503741/12500000000000000000 : ℝ)=(50025853007604935213/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(20373950518920249/50000000000000000000 : ℝ) ≤ ((6772758887760766083/6775000000000000000 : ℝ)+2*(243191916827/135500000000000 : ℝ)*(1847/12500 : ℝ))^(1045/256 : ℝ) := by
    rw [show (6772758887760766083/6775000000000000000 : ℝ)+2*(243191916827/135500000000000 : ℝ)*(1847/12500 : ℝ)=(5000998001124577/5000000000000000 : ℝ) by norm_num, show 1+2*(20373950518920249/50000000000000000000 : ℝ)=(25020373950518920249/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (6772758887760766083/6775000000000000000 : ℝ)*(X 1 0+X 2 0)+(243191916827/135500000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1045/256 : ℝ)) (lo := (10711/100000 : ℝ)) (hi := (1847/12500 : ℝ)) (c := (6772758887760766083/6775000000000000000 : ℝ)) (alpha := (243191916827/135500000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (6772758887760766083/6775000000000000000 : ℝ)*(X 0 1+X 2 1)+(243191916827/135500000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1045/256 : ℝ)) (lo := (10711/100000 : ℝ)) (hi := (1847/12500 : ℝ)) (c := (6772758887760766083/6775000000000000000 : ℝ)) (alpha := (243191916827/135500000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (6772758887760766083/6775000000000000000 : ℝ)*(X 0 2+X 1 2)+(243191916827/135500000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1045/256 : ℝ)) (lo := (10711/100000 : ℝ)) (hi := (1847/12500 : ℝ)) (c := (6772758887760766083/6775000000000000000 : ℝ)) (alpha := (243191916827/135500000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1076892207/5000000000 : ℝ)*X 0 0+(1350168859/2500000000 : ℝ)*X 0 1+(2629258101/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1168_s4_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2673348601/5000000000 : ℝ)*X 1 0+(-278251321/1250000000 : ℝ)*X 1 1+(657314507/1250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1168_s4_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((106933963/200000000 : ℝ)*X 2 0+(5258514987/10000000000 : ℝ)*X 2 1+(-1113005361/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1168_s4_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((1090149717/2500000000 : ℝ)*X 0 0+(4220756097/10000000000 : ℝ)*X 0 1+(4505022823/10000000000 : ℝ)*X 0 2+(1090149717/2500000000 : ℝ)*X 1 0+(4220756097/10000000000 : ℝ)*X 1 1+(4505022823/10000000000 : ℝ)*X 1 2+(1090149717/2500000000 : ℝ)*X 2 0+(4220756097/10000000000 : ℝ)*X 2 1+(4505022823/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1168_s4_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2153791867/10000000000 : ℝ)*X 0 0+(525891747/1000000000 : ℝ)*X 0 1+(1080054417/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1168_s4_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5310613903/10000000000 : ℝ)*X 1 0+(-2084254297/10000000000 : ℝ)*X 1 1+(67503401/125000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1168_s4_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5310613801/10000000000 : ℝ)*X 2 0+(216010897/400000000 : ℝ)*X 2 1+(-416850793/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1168_s4_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4360612887/10000000000 : ℝ)*X 0 0+(2252109777/5000000000 : ℝ)*X 0 1+(844312463/2000000000 : ℝ)*X 0 2+(4360612887/10000000000 : ℝ)*X 1 0+(2252109777/5000000000 : ℝ)*X 1 1+(844312463/2000000000 : ℝ)*X 1 2+(4360612887/10000000000 : ℝ)*X 2 0+(2252109777/5000000000 : ℝ)*X 2 1+(844312463/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1168_s4_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (2728002130465880670879944559/338750000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1599359/100000000000000 : ℝ)*(base23) + (497531661/100000000000000 : ℝ)*(lower2) + (12837667/12500000000000 : ℝ)*(lower3) + (59626259/100000000000000 : ℝ)*(upper4) + (37645957/100000000000000 : ℝ)*(lower5) + (5276083505209603/100000000000000 : ℝ)*(major0) + (5276083505209603/100000000000000 : ℝ)*(major1) + (5276083505209603/100000000000000 : ℝ)*(major2) + (7034338080281883/100000000000000 : ℝ)*(sp0) + (7034338080281883/100000000000000 : ℝ)*(sp1) + (879288489426661/12500000000000 : ℝ)*(sp2) + (439727660662881/12500000000000 : ℝ)*(sp3) + (7540817309/25000000000000 : ℝ)*(sp6) + (7376396159/100000000000000 : ℝ)*(sp7) + (439728582712401/12500000000000 : ℝ)*(f.failure) + (7034338080281883/100000000000000 : ℝ)*(f.sum) + (49345135193757/846875000000000000000000000 : ℝ)*base65 + (7832354115677345049/677500000000000000000000000000000 : ℝ)*base67 + (4129221618239845049/677500000000000000000000000000000 : ℝ)*base69 + (59601321967569845049/677500000000000000000000000000000 : ℝ)*base71 + (32884225673231/6775000000000000000000000000 : ℝ)*base73 + (3940304075184845049/677500000000000000000000000000000 : ℝ)*base75 + (7970434575644845049/677500000000000000000000000000000 : ℝ)*base77 + (4583986485857345049/677500000000000000000000000000000 : ℝ)*base79 + (14301955664553/3387500000000000000000000000 : ℝ)*base81 + (3118453/1250000000000000000000 : ℝ)*base89 + (3118453/1250000000000000000000 : ℝ)*base91 + (3118453/1250000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1604911094634251160109352049/338750000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (9769913/25000000000000 : ℝ)*(base19) + (21179749/50000000000000 : ℝ)*(lower2) + (3609593/25000000000000 : ℝ)*(upper3) + (3053157/5000000000000 : ℝ)*(lower4) + (48385899/20000000000000 : ℝ)*(upper5) + (5306143468346201/100000000000000 : ℝ)*(major0) + (5306143468346201/100000000000000 : ℝ)*(major1) + (5306143468346201/100000000000000 : ℝ)*(major2) + (9062572131/100000000000000 : ℝ)*(sp2) + (10903195433/100000000000000 : ℝ)*(sp3) + (7074415636734763/100000000000000 : ℝ)*(sp4) + (7074415597655111/100000000000000 : ℝ)*(sp5) + (884300821770329/12500000000000 : ℝ)*(sp6) + (1768930119418683/50000000000000 : ℝ)*(sp7) + (3537871142032799/100000000000000 : ℝ)*(f.failure) + (7074415636734763/100000000000000 : ℝ)*(f.sum) + (1492674536647/423437500000000000000000000 : ℝ)*base65 + (10604694519528449317/677500000000000000000000000000000 : ℝ)*base68 + (9328183659425949317/677500000000000000000000000000000 : ℝ)*base70 + (11930524312588449317/677500000000000000000000000000000 : ℝ)*base72 + (45963433342777/6775000000000000000000000000 : ℝ)*base73 + (12199643048636550683/677500000000000000000000000000000 : ℝ)*base75 + (1023677859785949317/677500000000000000000000000000000 : ℝ)*base78 + (1732553186029050683/677500000000000000000000000000000 : ℝ)*base79 + (16496233358849/3387500000000000000000000000 : ℝ)*base82 + (61117147/10000000000000000000000 : ℝ)*base89 + (61117147/10000000000000000000000 : ℝ)*base91 + (61117147/10000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1168_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (1045/256 : ℝ) ≤ p) (hpb : p ≤ (8361/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (149981253/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1847/12500 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10711/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (1403/12500 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7117/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1168_s4 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1168_s5_0 (p : ℝ) (hpa : (1045/256 : ℝ) ≤ p) (hpb : p ≤ (8361/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2154370251/10000000000 : ℝ)*x 0 + (5394236671/10000000000 : ℝ)*x 1 + (210582799/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2154370251/10000000000 : ℝ)^8361 ≤ (1309311043141/10000000000000 : ℝ)^6313 := by
    have hnat : (2154370251 : ℕ)^8361*10000000000000^6313 ≤ 1309311043141^6313*10000000000^8361 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2154370251 10000000000 1309311043141 10000000000000 8361 6313 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5394236671/10000000000 : ℝ)^8361 ≤ (22076764546571/50000000000000 : ℝ)^6313 := by
    have hnat : (5394236671 : ℕ)^8361*50000000000000^6313 ≤ 22076764546571^6313*10000000000^8361 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5394236671 10000000000 22076764546571 50000000000000 8361 6313 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (210582799/400000000 : ℝ)^8361 ≤ (21376680226769/50000000000000 : ℝ)^6313 := by
    have hnat : (210582799 : ℕ)^8361*50000000000000^6313 ≤ 21376680226769^6313*400000000^8361 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      210582799 400000000 21376680226769 50000000000000 8361 6313 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8361/2048 : ℝ)) 8361 6313 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2154370251/10000000000 : ℝ), (5394236671/10000000000 : ℝ), (210582799/400000000 : ℝ)] ![(1309311043141/10000000000000 : ℝ), (22076764546571/50000000000000 : ℝ), (21376680226769/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2154370251/10000000000 : ℝ)|^8361 ≤ (1309311043141/10000000000000 : ℝ)^6313
        have hw : |(-2154370251/10000000000 : ℝ)|=(2154370251/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5394236671/10000000000 : ℝ)|^8361 ≤ (22076764546571/50000000000000 : ℝ)^6313
        have hw : |(5394236671/10000000000 : ℝ)|=(5394236671/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(210582799/400000000 : ℝ)|^8361 ≤ (21376680226769/50000000000000 : ℝ)^6313
        have hw : |(210582799/400000000 : ℝ)|=(210582799/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1168_s5_1 (p : ℝ) (hpa : (1045/256 : ℝ) ≤ p) (hpb : p ≤ (8361/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2672539141/5000000000 : ℝ)*x 0 + (-2220156449/10000000000 : ℝ)*x 1 + (5264570061/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2672539141/5000000000 : ℝ)^8361 ≤ (2726337903947/6250000000000 : ℝ)^6313 := by
    have hnat : (2672539141 : ℕ)^8361*6250000000000^6313 ≤ 2726337903947^6313*5000000000^8361 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2672539141 5000000000 2726337903947 6250000000000 8361 6313 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2220156449/10000000000 : ℝ)^8361 ≤ (13625232139603/100000000000000 : ℝ)^6313 := by
    have hnat : (2220156449 : ℕ)^8361*100000000000000^6313 ≤ 13625232139603^6313*10000000000^8361 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2220156449 10000000000 13625232139603 100000000000000 8361 6313 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5264570061/10000000000 : ℝ)^8361 ≤ (42753361378509/100000000000000 : ℝ)^6313 := by
    have hnat : (5264570061 : ℕ)^8361*100000000000000^6313 ≤ 42753361378509^6313*10000000000^8361 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5264570061 10000000000 42753361378509 100000000000000 8361 6313 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8361/2048 : ℝ)) 8361 6313 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2672539141/5000000000 : ℝ), (-2220156449/10000000000 : ℝ), (5264570061/10000000000 : ℝ)] ![(2726337903947/6250000000000 : ℝ), (13625232139603/100000000000000 : ℝ), (42753361378509/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2672539141/5000000000 : ℝ)|^8361 ≤ (2726337903947/6250000000000 : ℝ)^6313
        have hw : |(2672539141/5000000000 : ℝ)|=(2672539141/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2220156449/10000000000 : ℝ)|^8361 ≤ (13625232139603/100000000000000 : ℝ)^6313
        have hw : |(-2220156449/10000000000 : ℝ)|=(2220156449/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5264570061/10000000000 : ℝ)|^8361 ≤ (42753361378509/100000000000000 : ℝ)^6313
        have hw : |(5264570061/10000000000 : ℝ)|=(5264570061/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1168_s5_2 (p : ℝ) (hpa : (1045/256 : ℝ) ≤ p) (hpb : p ≤ (8361/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5345078521/10000000000 : ℝ)*x 0 + (5264570121/10000000000 : ℝ)*x 1 + (-555039013/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5345078521/10000000000 : ℝ)^8361 ≤ (43621409046399/100000000000000 : ℝ)^6313 := by
    have hnat : (5345078521 : ℕ)^8361*100000000000000^6313 ≤ 43621409046399^6313*10000000000^8361 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5345078521 10000000000 43621409046399 100000000000000 8361 6313 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5264570121/10000000000 : ℝ)^8361 ≤ (21376681011919/50000000000000 : ℝ)^6313 := by
    have hnat : (5264570121 : ℕ)^8361*50000000000000^6313 ≤ 21376681011919^6313*10000000000^8361 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5264570121 10000000000 21376681011919 50000000000000 8361 6313 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (555039013/2500000000 : ℝ)^8361 ≤ (6812614456397/50000000000000 : ℝ)^6313 := by
    have hnat : (555039013 : ℕ)^8361*50000000000000^6313 ≤ 6812614456397^6313*2500000000^8361 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      555039013 2500000000 6812614456397 50000000000000 8361 6313 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8361/2048 : ℝ)) 8361 6313 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5345078521/10000000000 : ℝ), (5264570121/10000000000 : ℝ), (-555039013/2500000000 : ℝ)] ![(43621409046399/100000000000000 : ℝ), (21376681011919/50000000000000 : ℝ), (6812614456397/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5345078521/10000000000 : ℝ)|^8361 ≤ (43621409046399/100000000000000 : ℝ)^6313
        have hw : |(5345078521/10000000000 : ℝ)|=(5345078521/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5264570121/10000000000 : ℝ)|^8361 ≤ (21376681011919/50000000000000 : ℝ)^6313
        have hw : |(5264570121/10000000000 : ℝ)|=(5264570121/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-555039013/2500000000 : ℝ)|^8361 ≤ (6812614456397/50000000000000 : ℝ)^6313
        have hw : |(-555039013/2500000000 : ℝ)|=(555039013/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1168_s5_3 (p : ℝ) (hpa : (1045/256 : ℝ) ≤ p) (hpb : p ≤ (8361/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2180469841/5000000000 : ℝ)*x 0 + (4233203233/10000000000 : ℝ)*x 1 + (140390231/312500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2180469841/5000000000 : ℝ)^8361 ≤ (8329065569121/25000000000000 : ℝ)^6313 := by
    have hnat : (2180469841 : ℕ)^8361*25000000000000^6313 ≤ 8329065569121^6313*5000000000^8361 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2180469841 5000000000 8329065569121 25000000000000 8361 6313 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4233203233/10000000000 : ℝ)^8361 ≤ (8007498689543/25000000000000 : ℝ)^6313 := by
    have hnat : (4233203233 : ℕ)^8361*25000000000000^6313 ≤ 8007498689543^6313*10000000000^8361 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4233203233 10000000000 8007498689543 25000000000000 8361 6313 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (140390231/312500000 : ℝ)^8361 ≤ (34653742950479/100000000000000 : ℝ)^6313 := by
    have hnat : (140390231 : ℕ)^8361*100000000000000^6313 ≤ 34653742950479^6313*312500000^8361 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      140390231 312500000 34653742950479 100000000000000 8361 6313 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8361/2048 : ℝ)) 8361 6313 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2180469841/5000000000 : ℝ), (4233203233/10000000000 : ℝ), (140390231/312500000 : ℝ)] ![(8329065569121/25000000000000 : ℝ), (8007498689543/25000000000000 : ℝ), (34653742950479/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2180469841/5000000000 : ℝ)|^8361 ≤ (8329065569121/25000000000000 : ℝ)^6313
        have hw : |(2180469841/5000000000 : ℝ)|=(2180469841/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4233203233/10000000000 : ℝ)|^8361 ≤ (8007498689543/25000000000000 : ℝ)^6313
        have hw : |(4233203233/10000000000 : ℝ)|=(4233203233/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(140390231/312500000 : ℝ)|^8361 ≤ (34653742950479/100000000000000 : ℝ)^6313
        have hw : |(140390231/312500000 : ℝ)|=(140390231/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1168_s5_4 (p : ℝ) (hpa : (1045/256 : ℝ) ≤ p) (hpb : p ≤ (8361/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-1077187531/5000000000 : ℝ)*x 0 + (5264904631/10000000000 : ℝ)*x 1 + (1348475267/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1077187531/5000000000 : ℝ)^8361 ≤ (1309314915543/10000000000000 : ℝ)^6313 := by
    have hnat : (1077187531 : ℕ)^8361*10000000000000^6313 ≤ 1309314915543^6313*5000000000^8361 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1077187531 5000000000 1309314915543 10000000000000 8361 6313 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5264904631/10000000000 : ℝ)^8361 ≤ (4275695987649/10000000000000 : ℝ)^6313 := by
    have hnat : (5264904631 : ℕ)^8361*10000000000000^6313 ≤ 4275695987649^6313*10000000000^8361 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5264904631 10000000000 4275695987649 10000000000000 8361 6313 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1348475267/2500000000 : ℝ)^8361 ≤ (11037472738489/25000000000000 : ℝ)^6313 := by
    have hnat : (1348475267 : ℕ)^8361*25000000000000^6313 ≤ 11037472738489^6313*2500000000^8361 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1348475267 2500000000 11037472738489 25000000000000 8361 6313 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8361/2048 : ℝ)) 8361 6313 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1077187531/5000000000 : ℝ), (5264904631/10000000000 : ℝ), (1348475267/2500000000 : ℝ)] ![(1309314915543/10000000000000 : ℝ), (4275695987649/10000000000000 : ℝ), (11037472738489/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1077187531/5000000000 : ℝ)|^8361 ≤ (1309314915543/10000000000000 : ℝ)^6313
        have hw : |(-1077187531/5000000000 : ℝ)|=(1077187531/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5264904631/10000000000 : ℝ)|^8361 ≤ (4275695987649/10000000000000 : ℝ)^6313
        have hw : |(5264904631/10000000000 : ℝ)|=(5264904631/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1348475267/2500000000 : ℝ)|^8361 ≤ (11037472738489/25000000000000 : ℝ)^6313
        have hw : |(1348475267/2500000000 : ℝ)|=(1348475267/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1168_s5_5 (p : ℝ) (hpa : (1045/256 : ℝ) ≤ p) (hpb : p ≤ (8361/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2656082251/5000000000 : ℝ)*x 0 + (-2090825399/10000000000 : ℝ)*x 1 + (215756041/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2656082251/5000000000 : ℝ)^8361 ≤ (21633005783319/50000000000000 : ℝ)^6313 := by
    have hnat : (2656082251 : ℕ)^8361*50000000000000^6313 ≤ 21633005783319^6313*5000000000^8361 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2656082251 5000000000 21633005783319 50000000000000 8361 6313 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2090825399/10000000000 : ℝ)^8361 ≤ (786506121083/6250000000000 : ℝ)^6313 := by
    have hnat : (2090825399 : ℕ)^8361*6250000000000^6313 ≤ 786506121083^6313*10000000000^8361 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2090825399 10000000000 786506121083 6250000000000 8361 6313 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (215756041/400000000 : ℝ)^8361 ≤ (8829978097563/20000000000000 : ℝ)^6313 := by
    have hnat : (215756041 : ℕ)^8361*20000000000000^6313 ≤ 8829978097563^6313*400000000^8361 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      215756041 400000000 8829978097563 20000000000000 8361 6313 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8361/2048 : ℝ)) 8361 6313 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2656082251/5000000000 : ℝ), (-2090825399/10000000000 : ℝ), (215756041/400000000 : ℝ)] ![(21633005783319/50000000000000 : ℝ), (786506121083/6250000000000 : ℝ), (8829978097563/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2656082251/5000000000 : ℝ)|^8361 ≤ (21633005783319/50000000000000 : ℝ)^6313
        have hw : |(2656082251/5000000000 : ℝ)|=(2656082251/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2090825399/10000000000 : ℝ)|^8361 ≤ (786506121083/6250000000000 : ℝ)^6313
        have hw : |(-2090825399/10000000000 : ℝ)|=(2090825399/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(215756041/400000000 : ℝ)|^8361 ≤ (8829978097563/20000000000000 : ℝ)^6313
        have hw : |(215756041/400000000 : ℝ)|=(215756041/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1168_s5_6 (p : ℝ) (hpa : (1045/256 : ℝ) ≤ p) (hpb : p ≤ (8361/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5312164481/10000000000 : ℝ)*x 0 + (5393901047/10000000000 : ℝ)*x 1 + (-522706349/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5312164481/10000000000 : ℝ)^8361 ≤ (2704125708757/6250000000000 : ℝ)^6313 := by
    have hnat : (5312164481 : ℕ)^8361*6250000000000^6313 ≤ 2704125708757^6313*10000000000^8361 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5312164481 10000000000 2704125708757 6250000000000 8361 6313 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5393901047/10000000000 : ℝ)^8361 ≤ (22074945363153/50000000000000 : ℝ)^6313 := by
    have hnat : (5393901047 : ℕ)^8361*50000000000000^6313 ≤ 22074945363153^6313*10000000000^8361 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5393901047 10000000000 22074945363153 50000000000000 8361 6313 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (522706349/2500000000 : ℝ)^8361 ≤ (6292048956707/50000000000000 : ℝ)^6313 := by
    have hnat : (522706349 : ℕ)^8361*50000000000000^6313 ≤ 6292048956707^6313*2500000000^8361 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      522706349 2500000000 6292048956707 50000000000000 8361 6313 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8361/2048 : ℝ)) 8361 6313 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5312164481/10000000000 : ℝ), (5393901047/10000000000 : ℝ), (-522706349/2500000000 : ℝ)] ![(2704125708757/6250000000000 : ℝ), (22074945363153/50000000000000 : ℝ), (6292048956707/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5312164481/10000000000 : ℝ)|^8361 ≤ (2704125708757/6250000000000 : ℝ)^6313
        have hw : |(5312164481/10000000000 : ℝ)|=(5312164481/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5393901047/10000000000 : ℝ)|^8361 ≤ (22074945363153/50000000000000 : ℝ)^6313
        have hw : |(5393901047/10000000000 : ℝ)|=(5393901047/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-522706349/2500000000 : ℝ)|^8361 ≤ (6292048956707/50000000000000 : ℝ)^6313
        have hw : |(-522706349/2500000000 : ℝ)|=(522706349/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1168_s5_7 (p : ℝ) (hpa : (1045/256 : ℝ) ≤ p) (hpb : p ≤ (8361/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4360949951/10000000000 : ℝ)*x 0 + (4491818883/10000000000 : ℝ)*x 1 + (4233874357/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4360949951/10000000000 : ℝ)^8361 ≤ (33316366179211/100000000000000 : ℝ)^6313 := by
    have hnat : (4360949951 : ℕ)^8361*100000000000000^6313 ≤ 33316366179211^6313*10000000000^8361 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4360949951 10000000000 33316366179211 100000000000000 8361 6313 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4491818883/10000000000 : ℝ)^8361 ≤ (1082716048481/3125000000000 : ℝ)^6313 := by
    have hnat : (4491818883 : ℕ)^8361*3125000000000^6313 ≤ 1082716048481^6313*10000000000^8361 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4491818883 10000000000 1082716048481 3125000000000 8361 6313 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4233874357/10000000000 : ℝ)^8361 ≤ (6407344050219/20000000000000 : ℝ)^6313 := by
    have hnat : (4233874357 : ℕ)^8361*20000000000000^6313 ≤ 6407344050219^6313*10000000000^8361 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4233874357 10000000000 6407344050219 20000000000000 8361 6313 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8361/2048 : ℝ)) 8361 6313 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4360949951/10000000000 : ℝ), (4491818883/10000000000 : ℝ), (4233874357/10000000000 : ℝ)] ![(33316366179211/100000000000000 : ℝ), (1082716048481/3125000000000 : ℝ), (6407344050219/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4360949951/10000000000 : ℝ)|^8361 ≤ (33316366179211/100000000000000 : ℝ)^6313
        have hw : |(4360949951/10000000000 : ℝ)|=(4360949951/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4491818883/10000000000 : ℝ)|^8361 ≤ (1082716048481/3125000000000 : ℝ)^6313
        have hw : |(4491818883/10000000000 : ℝ)|=(4491818883/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4233874357/10000000000 : ℝ)|^8361 ≤ (6407344050219/20000000000000 : ℝ)^6313
        have hw : |(4233874357/10000000000 : ℝ)|=(4233874357/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1168_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (1045/256 : ℝ) ≤ p) (hpb : p ≤ (8361/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (149981253/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7117/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1403/12500 : ℝ)*pair X i i ≤ pair X i h) :
    (11353/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (14099/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (7117/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (1403/12500 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (7117/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (1403/12500 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (7117/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (1403/12500 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (7117/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (1403/12500 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (7117/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (1403/12500 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (7117/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (1403/12500 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (1403/12500 : ℝ) ^ (1045/256 : ℝ) ≤ (13263955530048147/100000000000000000000 : ℝ) := by
    have hpowers : (1403/12500 : ℝ)^1045 ≤ (13263955530048147/100000000000000000000 : ℝ)^256 := by
      have hnat : (1403 : ℕ)^1045*100000000000000000000^256 ≤ 13263955530048147^256*12500^1045 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1403 12500 13263955530048147 100000000000000000000 1045 256 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1403/12500 : ℝ)) (X := (13263955530048147/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 1045 256 (by norm_num) hpowers
    exact h
  have hpowhi : (7117/50000 : ℝ) ^ (1045/256 : ℝ) ≤ (273302892849121/781250000000000000 : ℝ) := by
    have hpowers : (7117/50000 : ℝ)^1045 ≤ (273302892849121/781250000000000000 : ℝ)^256 := by
      have hnat : (7117 : ℕ)^1045*781250000000000000^256 ≤ 273302892849121^256*50000^1045 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        7117 50000 273302892849121 781250000000000000 1045 256 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (7117/50000 : ℝ)) (X := (273302892849121/781250000000000000 : ℝ)) (by norm_num) (by norm_num) 1045 256 (by norm_num) hpowers
    exact h
  have hcorner00 : (50013263955530048147/50000000000000000000 : ℝ) ≤ (2500162451321307/2500000000000000 : ℝ) ^ (1045/256 : ℝ) := by
    have hpowers : (50013263955530048147/50000000000000000000 : ℝ)^256 ≤ (2500162451321307/2500000000000000 : ℝ)^1045 := by
      have hnat : (50013263955530048147 : ℕ)^256*2500000000000000^1045 ≤ 2500162451321307^1045*50000000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50013263955530048147 50000000000000000000 2500162451321307 2500000000000000 256 1045 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500162451321307/2500000000000000 : ℝ)) (X := (50013263955530048147/50000000000000000000 : ℝ)) (by norm_num) 1045 256 (by norm_num) hpowers
    exact h
  have hcorner10 : (20009649345162947127/20000000000000000000 : ℝ) ≤ (5000590857073577/5000000000000000 : ℝ) ^ (1045/256 : ℝ) := by
    have hpowers : (20009649345162947127/20000000000000000000 : ℝ)^256 ≤ (5000590857073577/5000000000000000 : ℝ)^1045 := by
      have hnat : (20009649345162947127 : ℕ)^256*5000000000000000^1045 ≤ 5000590857073577^1045*20000000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        20009649345162947127 20000000000000000000 5000590857073577 5000000000000000 256 1045 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000590857073577/5000000000000000 : ℝ)) (X := (20009649345162947127/20000000000000000000 : ℝ)) (by norm_num) 1045 256 (by norm_num) hpowers
    exact h
  have hcorner11 : (390898302892849121/390625000000000000 : ℝ) ≤ (250042840575227/250000000000000 : ℝ) ^ (1045/256 : ℝ) := by
    have hpowers : (390898302892849121/390625000000000000 : ℝ)^256 ≤ (250042840575227/250000000000000 : ℝ)^1045 := by
      have hnat : (390898302892849121 : ℕ)^256*250000000000000^1045 ≤ 250042840575227^1045*390625000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        390898302892849121 390625000000000000 250042840575227 250000000000000 256 1045 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (250042840575227/250000000000000 : ℝ)) (X := (390898302892849121/390625000000000000 : ℝ)) (by norm_num) 1045 256 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(13263955530048147/100000000000000000000 : ℝ) ≤ ((3761251952972002679/3762500000000000000 : ℝ)+2*(265954430963/150500000000000 : ℝ)*(1403/12500 : ℝ))^(1045/256 : ℝ) := by
    rw [show (3761251952972002679/3762500000000000000 : ℝ)+2*(265954430963/150500000000000 : ℝ)*(1403/12500 : ℝ)=(2500162451321307/2500000000000000 : ℝ) by norm_num, show 1+2*(13263955530048147/100000000000000000000 : ℝ)=(50013263955530048147/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(273302892849121/781250000000000000 : ℝ)+(13263955530048147/100000000000000000000 : ℝ) ≤ ((3761251952972002679/3762500000000000000 : ℝ)+(265954430963/150500000000000 : ℝ)*((7117/50000 : ℝ)+(1403/12500 : ℝ)))^(1045/256 : ℝ) := by
    rw [show (3761251952972002679/3762500000000000000 : ℝ)+(265954430963/150500000000000 : ℝ)*((7117/50000 : ℝ)+(1403/12500 : ℝ))=(5000590857073577/5000000000000000 : ℝ) by norm_num, show 1+(273302892849121/781250000000000000 : ℝ)+(13263955530048147/100000000000000000000 : ℝ)=(20009649345162947127/20000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(273302892849121/781250000000000000 : ℝ) ≤ ((3761251952972002679/3762500000000000000 : ℝ)+2*(265954430963/150500000000000 : ℝ)*(7117/50000 : ℝ))^(1045/256 : ℝ) := by
    rw [show (3761251952972002679/3762500000000000000 : ℝ)+2*(265954430963/150500000000000 : ℝ)*(7117/50000 : ℝ)=(250042840575227/250000000000000 : ℝ) by norm_num, show 1+2*(273302892849121/781250000000000000 : ℝ)=(390898302892849121/390625000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (3761251952972002679/3762500000000000000 : ℝ)*(X 1 0+X 2 0)+(265954430963/150500000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1045/256 : ℝ)) (lo := (1403/12500 : ℝ)) (hi := (7117/50000 : ℝ)) (c := (3761251952972002679/3762500000000000000 : ℝ)) (alpha := (265954430963/150500000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (3761251952972002679/3762500000000000000 : ℝ)*(X 0 1+X 2 1)+(265954430963/150500000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1045/256 : ℝ)) (lo := (1403/12500 : ℝ)) (hi := (7117/50000 : ℝ)) (c := (3761251952972002679/3762500000000000000 : ℝ)) (alpha := (265954430963/150500000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (3761251952972002679/3762500000000000000 : ℝ)*(X 0 2+X 1 2)+(265954430963/150500000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1045/256 : ℝ)) (lo := (1403/12500 : ℝ)) (hi := (7117/50000 : ℝ)) (c := (3761251952972002679/3762500000000000000 : ℝ)) (alpha := (265954430963/150500000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2154370251/10000000000 : ℝ)*X 0 0+(5394236671/10000000000 : ℝ)*X 0 1+(210582799/400000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1168_s5_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2672539141/5000000000 : ℝ)*X 1 0+(-2220156449/10000000000 : ℝ)*X 1 1+(5264570061/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1168_s5_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5345078521/10000000000 : ℝ)*X 2 0+(5264570121/10000000000 : ℝ)*X 2 1+(-555039013/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1168_s5_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2180469841/5000000000 : ℝ)*X 0 0+(4233203233/10000000000 : ℝ)*X 0 1+(140390231/312500000 : ℝ)*X 0 2+(2180469841/5000000000 : ℝ)*X 1 0+(4233203233/10000000000 : ℝ)*X 1 1+(140390231/312500000 : ℝ)*X 1 2+(2180469841/5000000000 : ℝ)*X 2 0+(4233203233/10000000000 : ℝ)*X 2 1+(140390231/312500000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1168_s5_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1077187531/5000000000 : ℝ)*X 0 0+(5264904631/10000000000 : ℝ)*X 0 1+(1348475267/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1168_s5_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2656082251/5000000000 : ℝ)*X 1 0+(-2090825399/10000000000 : ℝ)*X 1 1+(215756041/400000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1168_s5_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5312164481/10000000000 : ℝ)*X 2 0+(5393901047/10000000000 : ℝ)*X 2 1+(-522706349/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1168_s5_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4360949951/10000000000 : ℝ)*X 0 0+(4491818883/10000000000 : ℝ)*X 0 1+(4233874357/10000000000 : ℝ)*X 0 2+(4360949951/10000000000 : ℝ)*X 1 0+(4491818883/10000000000 : ℝ)*X 1 1+(4233874357/10000000000 : ℝ)*X 1 2+(4360949951/10000000000 : ℝ)*X 2 0+(4491818883/10000000000 : ℝ)*X 2 1+(4233874357/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1168_s5_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (19271761913701318131897/7525000000000000000000000000 : ℝ) := by norm_num
    linear_combination (411778273/25000000000000 : ℝ)*(base19) + (317671529/20000000000000 : ℝ)*(base23) + (1528429/6250000000000 : ℝ)*(upper3) + (215726261/100000000000000 : ℝ)*(upper4) + (105886667/25000000000000 : ℝ)*(upper5) + (2892247513362233/50000000000000 : ℝ)*(major0) + (2892247513362233/50000000000000 : ℝ)*(major1) + (2892247513362233/50000000000000 : ℝ)*(major2) + (3856057189895043/50000000000000 : ℝ)*(sp0) + (964022034847847/12500000000000 : ℝ)*(sp1) + (7712176337538223/100000000000000 : ℝ)*(sp2) + (3856794241260827/100000000000000 : ℝ)*(sp3) + (31773052891/50000000000000 : ℝ)*(sp4) + (4450231129/25000000000000 : ℝ)*(sp7) + (3856812042185343/100000000000000 : ℝ)*(f.failure) + (1928044481473967/25000000000000 : ℝ)*(f.sum) + (635366150371/3762500000000000000000000000 : ℝ)*base66 + (458876410696477793/188125000000000000000000000000000 : ℝ)*base68 + (1915690629105852793/188125000000000000000000000000000 : ℝ)*base70 + (1937460385806647207/188125000000000000000000000000000 : ℝ)*base71 + (12928245844117/7525000000000000000000000000 : ℝ)*base74 + (734834953674602793/188125000000000000000000000000000 : ℝ)*base76 + (2242121796649772207/188125000000000000000000000000000 : ℝ)*base77 + (923820735969147207/188125000000000000000000000000000 : ℝ)*base79 + (11801932402121/3762500000000000000000000000 : ℝ)*base82 + (1374779/10000000000000000000000 : ℝ)*base89 + (1374779/10000000000000000000000 : ℝ)*base91 + (1374779/10000000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (124208667578718317890234761/47031250000000000000000000000000 : ℝ) := by norm_num
    linear_combination (107452831/25000000000000 : ℝ)*(base19) + (238734051/50000000000000 : ℝ)*(base23) + (45022983/100000000000000 : ℝ)*(upper3) + (17587621/50000000000000 : ℝ)*(lower4) + (41402051/100000000000000 : ℝ)*(upper5) + (1453619130381203/25000000000000 : ℝ)*(major0) + (1453619130381203/25000000000000 : ℝ)*(major1) + (1453619130381203/25000000000000 : ℝ)*(major2) + (9248993059/100000000000000 : ℝ)*(sp1) + (1399944737/12500000000000 : ℝ)*(sp2) + (775215075126093/10000000000000 : ℝ)*(sp4) + (7752141072456547/100000000000000 : ℝ)*(sp5) + (7752139074234933/100000000000000 : ℝ)*(sp6) + (3876802203755967/100000000000000 : ℝ)*(sp7) + (3876802203755967/100000000000000 : ℝ)*(f.failure) + (775215075126093/10000000000000 : ℝ)*(f.sum) + (41027496122469/7525000000000000000000000000 : ℝ)*base66 + (717920341865219663/94062500000000000000000000000000 : ℝ)*base68 + (116468611207280337/94062500000000000000000000000000 : ℝ)*base69 + (1066558780164594663/94062500000000000000000000000000 : ℝ)*base72 + (25603655326469/7525000000000000000000000000 : ℝ)*base74 + (279592359884155337/94062500000000000000000000000000 : ℝ)*base75 + (972216665932407163/94062500000000000000000000000000 : ℝ)*base78 + (160838330783032163/94062500000000000000000000000000 : ℝ)*base80 + (1159059532481/7525000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base87 + (36886651/10000000000000000000000 : ℝ)*base89 + (36886651/10000000000000000000000 : ℝ)*base91 + (36886651/10000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1168_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (1045/256 : ℝ) ≤ p) (hpb : p ≤ (8361/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (149981253/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7117/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1403/12500 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11353/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14099/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1168_s5 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1168_b1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (1045/256 : ℝ) ≤ p) (hpb : p ≤ (8361/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (149981253/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (8213/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (4593/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11353/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14099/100000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1168_s3 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1168_s4 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1168_s5 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (1045/256 : ℝ) ≤ p) (hpb : p ≤ (8361/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (149981253/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (8213/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (4593/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11353/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14099/100000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1168_b1 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
