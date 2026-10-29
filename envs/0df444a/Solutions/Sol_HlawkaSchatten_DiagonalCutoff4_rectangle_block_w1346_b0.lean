-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1346_b0
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T21:06:00.48423+00:00
-- url     : https://prove2.me/submissions/fc1c92c5-6e34-406e-9511-743594fca320

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
theorem support_rectangle_w1346_s0_0 (p : ℝ) (hpa : (4305/1024 : ℝ) ≤ p) (hpb : p ≤ (2153/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-451695981/2500000000 : ℝ)*x 0 + (5995190977/10000000000 : ℝ)*x 1 + (601482807/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (451695981/2500000000 : ℝ)^2153 ≤ (662120984879/6250000000000 : ℝ)^1641 := by
    have hnat : (451695981 : ℕ)^2153*6250000000000^1641 ≤ 662120984879^1641*2500000000^2153 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      451695981 2500000000 662120984879 6250000000000 2153 1641 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5995190977/10000000000 : ℝ)^2153 ≤ (12776635068291/25000000000000 : ℝ)^1641 := by
    have hnat : (5995190977 : ℕ)^2153*25000000000000^1641 ≤ 12776635068291^1641*10000000000^2153 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5995190977 10000000000 12776635068291 25000000000000 2153 1641 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (601482807/1250000000 : ℝ)^2153 ≤ (1196860123717/3125000000000 : ℝ)^1641 := by
    have hnat : (601482807 : ℕ)^2153*3125000000000^1641 ≤ 1196860123717^1641*1250000000^2153 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      601482807 1250000000 1196860123717 3125000000000 2153 1641 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2153/512 : ℝ)) 2153 1641 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-451695981/2500000000 : ℝ), (5995190977/10000000000 : ℝ), (601482807/1250000000 : ℝ)] ![(662120984879/6250000000000 : ℝ), (12776635068291/25000000000000 : ℝ), (1196860123717/3125000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-451695981/2500000000 : ℝ)|^2153 ≤ (662120984879/6250000000000 : ℝ)^1641
        have hw : |(-451695981/2500000000 : ℝ)|=(451695981/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5995190977/10000000000 : ℝ)|^2153 ≤ (12776635068291/25000000000000 : ℝ)^1641
        have hw : |(5995190977/10000000000 : ℝ)|=(5995190977/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(601482807/1250000000 : ℝ)|^2153 ≤ (1196860123717/3125000000000 : ℝ)^1641
        have hw : |(601482807/1250000000 : ℝ)|=(601482807/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1346_s0_1 (p : ℝ) (hpa : (4305/1024 : ℝ) ≤ p) (hpb : p ≤ (2153/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5501364687/10000000000 : ℝ)*x 0 + (-309898393/1250000000 : ℝ)*x 1 + (2405931441/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5501364687/10000000000 : ℝ)^2153 ≤ (89171482107/195312500000 : ℝ)^1641 := by
    have hnat : (5501364687 : ℕ)^2153*195312500000^1641 ≤ 89171482107^1641*10000000000^2153 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5501364687 10000000000 89171482107 195312500000 2153 1641 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (309898393/1250000000 : ℝ)^2153 ≤ (8022336373071/50000000000000 : ℝ)^1641 := by
    have hnat : (309898393 : ℕ)^2153*50000000000000^1641 ≤ 8022336373071^1641*1250000000^2153 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      309898393 1250000000 8022336373071 50000000000000 2153 1641 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2405931441/5000000000 : ℝ)^2153 ≤ (38299528407563/100000000000000 : ℝ)^1641 := by
    have hnat : (2405931441 : ℕ)^2153*100000000000000^1641 ≤ 38299528407563^1641*5000000000^2153 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2405931441 5000000000 38299528407563 100000000000000 2153 1641 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2153/512 : ℝ)) 2153 1641 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5501364687/10000000000 : ℝ), (-309898393/1250000000 : ℝ), (2405931441/5000000000 : ℝ)] ![(89171482107/195312500000 : ℝ), (8022336373071/50000000000000 : ℝ), (38299528407563/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5501364687/10000000000 : ℝ)|^2153 ≤ (89171482107/195312500000 : ℝ)^1641
        have hw : |(5501364687/10000000000 : ℝ)|=(5501364687/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-309898393/1250000000 : ℝ)|^2153 ≤ (8022336373071/50000000000000 : ℝ)^1641
        have hw : |(-309898393/1250000000 : ℝ)|=(309898393/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2405931441/5000000000 : ℝ)|^2153 ≤ (38299528407563/100000000000000 : ℝ)^1641
        have hw : |(2405931441/5000000000 : ℝ)|=(2405931441/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1346_s0_2 (p : ℝ) (hpa : (4305/1024 : ℝ) ≤ p) (hpb : p ≤ (2153/512 : ℝ)) (x : Fin 3 → ℝ) :
    (1375341109/2500000000 : ℝ)*x 0 + (4811862611/10000000000 : ℝ)*x 1 + (-1239593899/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1375341109/2500000000 : ℝ)^2153 ≤ (9131159221163/20000000000000 : ℝ)^1641 := by
    have hnat : (1375341109 : ℕ)^2153*20000000000000^1641 ≤ 9131159221163^1641*2500000000^2153 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1375341109 2500000000 9131159221163 20000000000000 2153 1641 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4811862611/10000000000 : ℝ)^2153 ≤ (38299525577573/100000000000000 : ℝ)^1641 := by
    have hnat : (4811862611 : ℕ)^2153*100000000000000^1641 ≤ 38299525577573^1641*10000000000^2153 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4811862611 10000000000 38299525577573 100000000000000 2153 1641 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1239593899/5000000000 : ℝ)^2153 ≤ (16044678299233/100000000000000 : ℝ)^1641 := by
    have hnat : (1239593899 : ℕ)^2153*100000000000000^1641 ≤ 16044678299233^1641*5000000000^2153 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1239593899 5000000000 16044678299233 100000000000000 2153 1641 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2153/512 : ℝ)) 2153 1641 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1375341109/2500000000 : ℝ), (4811862611/10000000000 : ℝ), (-1239593899/5000000000 : ℝ)] ![(9131159221163/20000000000000 : ℝ), (38299525577573/100000000000000 : ℝ), (16044678299233/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1375341109/2500000000 : ℝ)|^2153 ≤ (9131159221163/20000000000000 : ℝ)^1641
        have hw : |(1375341109/2500000000 : ℝ)|=(1375341109/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4811862611/10000000000 : ℝ)|^2153 ≤ (38299525577573/100000000000000 : ℝ)^1641
        have hw : |(4811862611/10000000000 : ℝ)|=(4811862611/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1239593899/5000000000 : ℝ)|^2153 ≤ (16044678299233/100000000000000 : ℝ)^1641
        have hw : |(-1239593899/5000000000 : ℝ)|=(1239593899/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1346_s0_3 (p : ℝ) (hpa : (4305/1024 : ℝ) ≤ p) (hpb : p ≤ (2153/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2089074241/5000000000 : ℝ)*x 0 + (388296161/1250000000 : ℝ)*x 1 + (2794333163/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2089074241/5000000000 : ℝ)^2153 ≤ (795552780709/2500000000000 : ℝ)^1641 := by
    have hnat : (2089074241 : ℕ)^2153*2500000000000^1641 ≤ 795552780709^1641*5000000000^2153 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2089074241 5000000000 795552780709 2500000000000 2153 1641 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (388296161/1250000000 : ℝ)^2153 ≤ (10784588407413/50000000000000 : ℝ)^1641 := by
    have hnat : (388296161 : ℕ)^2153*50000000000000^1641 ≤ 10784588407413^1641*1250000000^2153 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      388296161 1250000000 10784588407413 50000000000000 2153 1641 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2794333163/5000000000 : ℝ)^2153 ≤ (23304355969319/50000000000000 : ℝ)^1641 := by
    have hnat : (2794333163 : ℕ)^2153*50000000000000^1641 ≤ 23304355969319^1641*5000000000^2153 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2794333163 5000000000 23304355969319 50000000000000 2153 1641 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2153/512 : ℝ)) 2153 1641 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2089074241/5000000000 : ℝ), (388296161/1250000000 : ℝ), (2794333163/5000000000 : ℝ)] ![(795552780709/2500000000000 : ℝ), (10784588407413/50000000000000 : ℝ), (23304355969319/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2089074241/5000000000 : ℝ)|^2153 ≤ (795552780709/2500000000000 : ℝ)^1641
        have hw : |(2089074241/5000000000 : ℝ)|=(2089074241/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(388296161/1250000000 : ℝ)|^2153 ≤ (10784588407413/50000000000000 : ℝ)^1641
        have hw : |(388296161/1250000000 : ℝ)|=(388296161/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2794333163/5000000000 : ℝ)|^2153 ≤ (23304355969319/50000000000000 : ℝ)^1641
        have hw : |(2794333163/5000000000 : ℝ)|=(2794333163/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1346_s0_4 (p : ℝ) (hpa : (4305/1024 : ℝ) ≤ p) (hpb : p ≤ (2153/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-905609793/5000000000 : ℝ)*x 0 + (4842311311/10000000000 : ℝ)*x 1 + (5963654863/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (905609793/5000000000 : ℝ)^2153 ≤ (10628071646851/100000000000000 : ℝ)^1641 := by
    have hnat : (905609793 : ℕ)^2153*100000000000000^1641 ≤ 10628071646851^1641*5000000000^2153 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      905609793 5000000000 10628071646851 100000000000000 2153 1641 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4842311311/10000000000 : ℝ)^2153 ≤ (38617807714871/100000000000000 : ℝ)^1641 := by
    have hnat : (4842311311 : ℕ)^2153*100000000000000^1641 ≤ 38617807714871^1641*10000000000^2153 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4842311311 10000000000 38617807714871 100000000000000 2153 1641 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5963654863/10000000000 : ℝ)^2153 ≤ (203016482473/400000000000 : ℝ)^1641 := by
    have hnat : (5963654863 : ℕ)^2153*400000000000^1641 ≤ 203016482473^1641*10000000000^2153 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5963654863 10000000000 203016482473 400000000000 2153 1641 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2153/512 : ℝ)) 2153 1641 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-905609793/5000000000 : ℝ), (4842311311/10000000000 : ℝ), (5963654863/10000000000 : ℝ)] ![(10628071646851/100000000000000 : ℝ), (38617807714871/100000000000000 : ℝ), (203016482473/400000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-905609793/5000000000 : ℝ)|^2153 ≤ (10628071646851/100000000000000 : ℝ)^1641
        have hw : |(-905609793/5000000000 : ℝ)|=(905609793/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4842311311/10000000000 : ℝ)|^2153 ≤ (38617807714871/100000000000000 : ℝ)^1641
        have hw : |(4842311311/10000000000 : ℝ)|=(4842311311/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5963654863/10000000000 : ℝ)|^2153 ≤ (203016482473/400000000000 : ℝ)^1641
        have hw : |(5963654863/10000000000 : ℝ)|=(5963654863/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1346_s0_5 (p : ℝ) (hpa : (4305/1024 : ℝ) ≤ p) (hpb : p ≤ (2153/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2589421851/5000000000 : ℝ)*x 0 + (-1327396207/10000000000 : ℝ)*x 1 + (5963654587/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2589421851/5000000000 : ℝ)^2153 ≤ (21088323262937/50000000000000 : ℝ)^1641 := by
    have hnat : (2589421851 : ℕ)^2153*50000000000000^1641 ≤ 21088323262937^1641*5000000000^2153 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2589421851 5000000000 21088323262937 50000000000000 2153 1641 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1327396207/10000000000 : ℝ)^2153 ≤ (1767308979733/25000000000000 : ℝ)^1641 := by
    have hnat : (1327396207 : ℕ)^2153*25000000000000^1641 ≤ 1767308979733^1641*10000000000^2153 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1327396207 10000000000 1767308979733 25000000000000 2153 1641 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5963654587/10000000000 : ℝ)^2153 ≤ (25377058768229/50000000000000 : ℝ)^1641 := by
    have hnat : (5963654587 : ℕ)^2153*50000000000000^1641 ≤ 25377058768229^1641*10000000000^2153 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5963654587 10000000000 25377058768229 50000000000000 2153 1641 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2153/512 : ℝ)) 2153 1641 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2589421851/5000000000 : ℝ), (-1327396207/10000000000 : ℝ), (5963654587/10000000000 : ℝ)] ![(21088323262937/50000000000000 : ℝ), (1767308979733/25000000000000 : ℝ), (25377058768229/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2589421851/5000000000 : ℝ)|^2153 ≤ (21088323262937/50000000000000 : ℝ)^1641
        have hw : |(2589421851/5000000000 : ℝ)|=(2589421851/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1327396207/10000000000 : ℝ)|^2153 ≤ (1767308979733/25000000000000 : ℝ)^1641
        have hw : |(-1327396207/10000000000 : ℝ)|=(1327396207/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5963654587/10000000000 : ℝ)|^2153 ≤ (25377058768229/50000000000000 : ℝ)^1641
        have hw : |(5963654587/10000000000 : ℝ)|=(5963654587/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1346_s0_6 (p : ℝ) (hpa : (4305/1024 : ℝ) ≤ p) (hpb : p ≤ (2153/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2589421837/5000000000 : ℝ)*x 0 + (5963654881/10000000000 : ℝ)*x 1 + (-663697891/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2589421837/5000000000 : ℝ)^2153 ≤ (42176646226693/100000000000000 : ℝ)^1641 := by
    have hnat : (2589421837 : ℕ)^2153*100000000000000^1641 ≤ 42176646226693^1641*5000000000^2153 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2589421837 5000000000 42176646226693 100000000000000 2153 1641 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5963654881/10000000000 : ℝ)^2153 ≤ (12688530204809/25000000000000 : ℝ)^1641 := by
    have hnat : (5963654881 : ℕ)^2153*25000000000000^1641 ≤ 12688530204809^1641*10000000000^2153 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5963654881 10000000000 12688530204809 25000000000000 2153 1641 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (663697891/5000000000 : ℝ)^2153 ≤ (7069232949343/100000000000000 : ℝ)^1641 := by
    have hnat : (663697891 : ℕ)^2153*100000000000000^1641 ≤ 7069232949343^1641*5000000000^2153 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      663697891 5000000000 7069232949343 100000000000000 2153 1641 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2153/512 : ℝ)) 2153 1641 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2589421837/5000000000 : ℝ), (5963654881/10000000000 : ℝ), (-663697891/5000000000 : ℝ)] ![(42176646226693/100000000000000 : ℝ), (12688530204809/25000000000000 : ℝ), (7069232949343/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2589421837/5000000000 : ℝ)|^2153 ≤ (42176646226693/100000000000000 : ℝ)^1641
        have hw : |(2589421837/5000000000 : ℝ)|=(2589421837/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5963654881/10000000000 : ℝ)|^2153 ≤ (12688530204809/25000000000000 : ℝ)^1641
        have hw : |(5963654881/10000000000 : ℝ)|=(5963654881/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-663697891/5000000000 : ℝ)|^2153 ≤ (7069232949343/100000000000000 : ℝ)^1641
        have hw : |(-663697891/5000000000 : ℝ)|=(663697891/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1346_s0_7 (p : ℝ) (hpa : (4305/1024 : ℝ) ≤ p) (hpb : p ≤ (2153/512 : ℝ)) (x : Fin 3 → ℝ) :
    (4187451107/10000000000 : ℝ)*x 0 + (5524793979/10000000000 : ℝ)*x 1 + (3172522843/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4187451107/10000000000 : ℝ)^2153 ≤ (15957550676187/50000000000000 : ℝ)^1641 := by
    have hnat : (4187451107 : ℕ)^2153*50000000000000^1641 ≤ 15957550676187^1641*10000000000^2153 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4187451107 10000000000 15957550676187 50000000000000 2153 1641 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5524793979/10000000000 : ℝ)^2153 ≤ (9182214767941/20000000000000 : ℝ)^1641 := by
    have hnat : (5524793979 : ℕ)^2153*20000000000000^1641 ≤ 9182214767941^1641*10000000000^2153 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5524793979 10000000000 9182214767941 20000000000000 2153 1641 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3172522843/10000000000 : ℝ)^2153 ≤ (2771728098757/12500000000000 : ℝ)^1641 := by
    have hnat : (3172522843 : ℕ)^2153*12500000000000^1641 ≤ 2771728098757^1641*10000000000^2153 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3172522843 10000000000 2771728098757 12500000000000 2153 1641 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2153/512 : ℝ)) 2153 1641 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4187451107/10000000000 : ℝ), (5524793979/10000000000 : ℝ), (3172522843/10000000000 : ℝ)] ![(15957550676187/50000000000000 : ℝ), (9182214767941/20000000000000 : ℝ), (2771728098757/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4187451107/10000000000 : ℝ)|^2153 ≤ (15957550676187/50000000000000 : ℝ)^1641
        have hw : |(4187451107/10000000000 : ℝ)|=(4187451107/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5524793979/10000000000 : ℝ)|^2153 ≤ (9182214767941/20000000000000 : ℝ)^1641
        have hw : |(5524793979/10000000000 : ℝ)|=(5524793979/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3172522843/10000000000 : ℝ)|^2153 ≤ (2771728098757/12500000000000 : ℝ)^1641
        have hw : |(3172522843/10000000000 : ℝ)|=(3172522843/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1346_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4305/1024 : ℝ) ≤ p) (hpb : p ≤ (2153/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (9680391/6250000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    (361/25000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (13421/50000 : ℝ)*pair X 0 0 := by
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
  have hpowlo : (0 : ℝ) ^ (4305/1024 : ℝ) ≤ (0 : ℝ) := by
    have hpowers : (0 : ℝ)^4305 ≤ (0 : ℝ)^1024 := by
      have hnat : (0 : ℕ)^4305*1^1024 ≤ 0^1024*1^4305 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        0 1 0 1 4305 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (0 : ℝ)) (X := (0 : ℝ)) (by norm_num) (by norm_num) 4305 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (2/5 : ℝ) ^ (4305/1024 : ℝ) ≤ (265417650699647883/12500000000000000000 : ℝ) := by
    have hpowers : (2/5 : ℝ)^4305 ≤ (265417650699647883/12500000000000000000 : ℝ)^1024 := by
      have hnat : (2 : ℕ)^4305*12500000000000000000^1024 ≤ 265417650699647883^1024*5^4305 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 5 265417650699647883 12500000000000000000 4305 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2/5 : ℝ)) (X := (265417650699647883/12500000000000000000 : ℝ)) (by norm_num) (by norm_num) 4305 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (1 : ℝ) ≤ (1 : ℝ) ^ (4305/1024 : ℝ) := by
    have hpowers : (1 : ℝ)^1024 ≤ (1 : ℝ)^4305 := by
      have hnat : (1 : ℕ)^1024*1^4305 ≤ 1^4305*1^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 1024 4305 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) 4305 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (12765417650699647883/12500000000000000000 : ℝ) ≤ (314065711774419/312500000000000 : ℝ) ^ (4305/1024 : ℝ) := by
    have hpowers : (12765417650699647883/12500000000000000000 : ℝ)^1024 ≤ (314065711774419/312500000000000 : ℝ)^4305 := by
      have hnat : (12765417650699647883 : ℕ)^1024*312500000000000^4305 ≤ 314065711774419^4305*12500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12765417650699647883 12500000000000000000 314065711774419 312500000000000 1024 4305 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (314065711774419/312500000000000 : ℝ)) (X := (12765417650699647883/12500000000000000000 : ℝ)) (by norm_num) 4305 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (6515417650699647883/6250000000000000000 : ℝ) ≤ (157815711774419/156250000000000 : ℝ) ^ (4305/1024 : ℝ) := by
    have hpowers : (6515417650699647883/6250000000000000000 : ℝ)^1024 ≤ (157815711774419/156250000000000 : ℝ)^4305 := by
      have hnat : (6515417650699647883 : ℕ)^1024*156250000000000^4305 ≤ 157815711774419^4305*6250000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6515417650699647883 6250000000000000000 157815711774419 156250000000000 1024 4305 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (157815711774419/156250000000000 : ℝ)) (X := (6515417650699647883/6250000000000000000 : ℝ)) (by norm_num) 4305 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(0 : ℝ) ≤ ((1 : ℝ)+2*(1565711774419/125000000000000 : ℝ)*(0 : ℝ))^(4305/1024 : ℝ) := by
    rw [show (1 : ℝ)+2*(1565711774419/125000000000000 : ℝ)*(0 : ℝ)=(1 : ℝ) by norm_num, show 1+2*(0 : ℝ)=(1 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(265417650699647883/12500000000000000000 : ℝ)+(0 : ℝ) ≤ ((1 : ℝ)+(1565711774419/125000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ)))^(4305/1024 : ℝ) := by
    rw [show (1 : ℝ)+(1565711774419/125000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ))=(314065711774419/312500000000000 : ℝ) by norm_num, show 1+(265417650699647883/12500000000000000000 : ℝ)+(0 : ℝ)=(12765417650699647883/12500000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(265417650699647883/12500000000000000000 : ℝ) ≤ ((1 : ℝ)+2*(1565711774419/125000000000000 : ℝ)*(2/5 : ℝ))^(4305/1024 : ℝ) := by
    rw [show (1 : ℝ)+2*(1565711774419/125000000000000 : ℝ)*(2/5 : ℝ)=(157815711774419/156250000000000 : ℝ) by norm_num, show 1+2*(265417650699647883/12500000000000000000 : ℝ)=(6515417650699647883/6250000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1 : ℝ)*(X 1 0+X 2 0)+(1565711774419/125000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4305/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (1565711774419/125000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1 : ℝ)*(X 0 1+X 2 1)+(1565711774419/125000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4305/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (1565711774419/125000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1 : ℝ)*(X 0 2+X 1 2)+(1565711774419/125000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4305/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (1565711774419/125000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-451695981/2500000000 : ℝ)*X 0 0+(5995190977/10000000000 : ℝ)*X 0 1+(601482807/1250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1346_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5501364687/10000000000 : ℝ)*X 1 0+(-309898393/1250000000 : ℝ)*X 1 1+(2405931441/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1346_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1375341109/2500000000 : ℝ)*X 2 0+(4811862611/10000000000 : ℝ)*X 2 1+(-1239593899/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1346_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2089074241/5000000000 : ℝ)*X 0 0+(388296161/1250000000 : ℝ)*X 0 1+(2794333163/5000000000 : ℝ)*X 0 2+(2089074241/5000000000 : ℝ)*X 1 0+(388296161/1250000000 : ℝ)*X 1 1+(2794333163/5000000000 : ℝ)*X 1 2+(2089074241/5000000000 : ℝ)*X 2 0+(388296161/1250000000 : ℝ)*X 2 1+(2794333163/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1346_s0_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-905609793/5000000000 : ℝ)*X 0 0+(4842311311/10000000000 : ℝ)*X 0 1+(5963654863/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1346_s0_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2589421851/5000000000 : ℝ)*X 1 0+(-1327396207/10000000000 : ℝ)*X 1 1+(5963654587/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1346_s0_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2589421837/5000000000 : ℝ)*X 2 0+(5963654881/10000000000 : ℝ)*X 2 1+(-663697891/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1346_s0_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4187451107/10000000000 : ℝ)*X 0 0+(5524793979/10000000000 : ℝ)*X 0 1+(3172522843/10000000000 : ℝ)*X 0 2+(4187451107/10000000000 : ℝ)*X 1 0+(5524793979/10000000000 : ℝ)*X 1 1+(3172522843/10000000000 : ℝ)*X 1 2+(4187451107/10000000000 : ℝ)*X 2 0+(5524793979/10000000000 : ℝ)*X 2 1+(3172522843/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1346_s0_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (38682093550444547138397/6250000000000000000000000000 : ℝ) := by norm_num
    linear_combination (122317029/100000000000000 : ℝ)*(base1) + (146355093/10000000000000 : ℝ)*(base19) + (1424994037/100000000000000 : ℝ)*(base23) + (48792561/20000000000000 : ℝ)*(upper3) + (32203997/50000000000000 : ℝ)*(upper5) + (623970255100021/100000000000000 : ℝ)*(major0) + (623970255100021/100000000000000 : ℝ)*(major1) + (623970255100021/100000000000000 : ℝ)*(major2) + (422539532960737/50000000000000 : ℝ)*(sp0) + (845081755917429/100000000000000 : ℝ)*(sp1) + (422540897237161/50000000000000 : ℝ)*(sp2) + (50356815400487/12500000000000 : ℝ)*(sp3) + (2137931957/50000000000000 : ℝ)*(sp4) + (2438906257/100000000000000 : ℝ)*(sp7) + (201428542213591/50000000000000 : ℝ)*(f.failure) + (845083219468359/100000000000000 : ℝ)*(f.sum) + (7634258280951/6250000000000000000000000000 : ℝ)*base66 + (28843684125299/12500000000000000000000000000 : ℝ)*base67 + (38941124249701/12500000000000000000000000000 : ℝ)*base70 + (20199332987799/12500000000000000000000000000 : ℝ)*base71 + (7617265055951/6250000000000000000000000000 : ℝ)*base74 + (5747920100299/12500000000000000000000000000 : ℝ)*base75 + (30479549625299/12500000000000000000000000000 : ℝ)*base77 + (629891750299/12500000000000000000000000000 : ℝ)*base79 + (35964589530951/6250000000000000000000000000 : ℝ)*base82 + (769081/312500000000000000000 : ℝ)*base89 + (769081/312500000000000000000 : ℝ)*base91 + (769081/312500000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (8907573926639753577039/3125000000000000000000000000 : ℝ) := by norm_num
    linear_combination (364055471/100000000000000 : ℝ)*(base19) + (34309711/6250000000000 : ℝ)*(base23) + (97376787/50000000000000 : ℝ)*(base39) + (22563/100000000000 : ℝ)*(upper3) + (118537407/100000000000000 : ℝ)*(upper5) + (658453690983827/100000000000000 : ℝ)*(major0) + (658453690983827/100000000000000 : ℝ)*(major1) + (658453496230253/100000000000000 : ℝ)*(major2) + (54137969/6250000000000 : ℝ)*(sp1) + (430520701/50000000000000 : ℝ)*(sp2) + (891786291950367/100000000000000 : ℝ)*(sp4) + (27868283177731/3125000000000 : ℝ)*(sp5) + (891785076707163/100000000000000 : ℝ)*(sp6) + (425120800249589/100000000000000 : ℝ)*(sp7) + (425120800249589/100000000000000 : ℝ)*(f.failure) + (891786486703941/100000000000000 : ℝ)*(f.sum) + (731234569649/625000000000000000000000000 : ℝ)*base66 + (46512947198007/12500000000000000000000000000 : ℝ)*base67 + (61301576778487/12500000000000000000000000000 : ℝ)*base70 + (26172501110507/12500000000000000000000000000 : ℝ)*base71 + (360432663399/625000000000000000000000000 : ℝ)*base74 + (10728438165987/12500000000000000000000000000 : ℝ)*base76 + (26751986859013/12500000000000000000000000000 : ℝ)*base77 + (4625778121513/12500000000000000000000000000 : ℝ)*base79 + (29683887834737/6250000000000000000000000000 : ℝ)*base82 + (359299/625000000000000000000 : ℝ)*base89 + (359299/625000000000000000000 : ℝ)*base91 + (359299/625000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1346_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4305/1024 : ℝ) ≤ p) (hpb : p ≤ (2153/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (9680391/6250000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (361/25000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (13421/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1346_s0 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1346_s1_0 (p : ℝ) (hpa : (4305/1024 : ℝ) ≤ p) (hpb : p ≤ (2153/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-1991025513/10000000000 : ℝ)*x 0 + (1128067569/2000000000 : ℝ)*x 1 + (631090167/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1991025513/10000000000 : ℝ)^2153 ≤ (6016658774217/50000000000000 : ℝ)^1641 := by
    have hnat : (1991025513 : ℕ)^2153*50000000000000^1641 ≤ 6016658774217^1641*10000000000^2153 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1991025513 10000000000 6016658774217 50000000000000 2153 1641 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1128067569/2000000000 : ℝ)^2153 ≤ (23587456210911/50000000000000 : ℝ)^1641 := by
    have hnat : (1128067569 : ℕ)^2153*50000000000000^1641 ≤ 23587456210911^1641*2000000000^2153 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1128067569 2000000000 23587456210911 50000000000000 2153 1641 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (631090167/1250000000 : ℝ)^2153 ≤ (40791770017223/100000000000000 : ℝ)^1641 := by
    have hnat : (631090167 : ℕ)^2153*100000000000000^1641 ≤ 40791770017223^1641*1250000000^2153 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      631090167 1250000000 40791770017223 100000000000000 2153 1641 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2153/512 : ℝ)) 2153 1641 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1991025513/10000000000 : ℝ), (1128067569/2000000000 : ℝ), (631090167/1250000000 : ℝ)] ![(6016658774217/50000000000000 : ℝ), (23587456210911/50000000000000 : ℝ), (40791770017223/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1991025513/10000000000 : ℝ)|^2153 ≤ (6016658774217/50000000000000 : ℝ)^1641
        have hw : |(-1991025513/10000000000 : ℝ)|=(1991025513/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1128067569/2000000000 : ℝ)|^2153 ≤ (23587456210911/50000000000000 : ℝ)^1641
        have hw : |(1128067569/2000000000 : ℝ)|=(1128067569/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(631090167/1250000000 : ℝ)|^2153 ≤ (40791770017223/100000000000000 : ℝ)^1641
        have hw : |(631090167/1250000000 : ℝ)|=(631090167/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1346_s1_1 (p : ℝ) (hpa : (4305/1024 : ℝ) ≤ p) (hpb : p ≤ (2153/512 : ℝ)) (x : Fin 3 → ℝ) :
    (675662339/1250000000 : ℝ)*x 0 + (-2306617723/10000000000 : ℝ)*x 1 + (126218039/250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (675662339/1250000000 : ℝ)^2153 ≤ (44612662507279/100000000000000 : ℝ)^1641 := by
    have hnat : (675662339 : ℕ)^2153*100000000000000^1641 ≤ 44612662507279^1641*1250000000^2153 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      675662339 1250000000 44612662507279 100000000000000 2153 1641 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2306617723/10000000000 : ℝ)^2153 ≤ (7297782543841/50000000000000 : ℝ)^1641 := by
    have hnat : (2306617723 : ℕ)^2153*50000000000000^1641 ≤ 7297782543841^1641*10000000000^2153 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2306617723 10000000000 7297782543841 50000000000000 2153 1641 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (126218039/250000000 : ℝ)^2153 ≤ (5098971548967/12500000000000 : ℝ)^1641 := by
    have hnat : (126218039 : ℕ)^2153*12500000000000^1641 ≤ 5098971548967^1641*250000000^2153 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      126218039 250000000 5098971548967 12500000000000 2153 1641 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2153/512 : ℝ)) 2153 1641 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(675662339/1250000000 : ℝ), (-2306617723/10000000000 : ℝ), (126218039/250000000 : ℝ)] ![(44612662507279/100000000000000 : ℝ), (7297782543841/50000000000000 : ℝ), (5098971548967/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(675662339/1250000000 : ℝ)|^2153 ≤ (44612662507279/100000000000000 : ℝ)^1641
        have hw : |(675662339/1250000000 : ℝ)|=(675662339/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2306617723/10000000000 : ℝ)|^2153 ≤ (7297782543841/50000000000000 : ℝ)^1641
        have hw : |(-2306617723/10000000000 : ℝ)|=(2306617723/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(126218039/250000000 : ℝ)|^2153 ≤ (5098971548967/12500000000000 : ℝ)^1641
        have hw : |(126218039/250000000 : ℝ)|=(126218039/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1346_s1_2 (p : ℝ) (hpa : (4305/1024 : ℝ) ≤ p) (hpb : p ≤ (2153/512 : ℝ)) (x : Fin 3 → ℝ) :
    (1081059737/2000000000 : ℝ)*x 0 + (504872127/1000000000 : ℝ)*x 1 + (-2306618129/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1081059737/2000000000 : ℝ)^2153 ≤ (22306331107453/50000000000000 : ℝ)^1641 := by
    have hnat : (1081059737 : ℕ)^2153*50000000000000^1641 ≤ 22306331107453^1641*2000000000^2153 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1081059737 2000000000 22306331107453 50000000000000 2153 1641 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (504872127/1000000000 : ℝ)^2153 ≤ (40791769317589/100000000000000 : ℝ)^1641 := by
    have hnat : (504872127 : ℕ)^2153*100000000000000^1641 ≤ 40791769317589^1641*1000000000^2153 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      504872127 1000000000 40791769317589 100000000000000 2153 1641 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2306618129/10000000000 : ℝ)^2153 ≤ (14595568458279/100000000000000 : ℝ)^1641 := by
    have hnat : (2306618129 : ℕ)^2153*100000000000000^1641 ≤ 14595568458279^1641*10000000000^2153 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2306618129 10000000000 14595568458279 100000000000000 2153 1641 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2153/512 : ℝ)) 2153 1641 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1081059737/2000000000 : ℝ), (504872127/1000000000 : ℝ), (-2306618129/10000000000 : ℝ)] ![(22306331107453/50000000000000 : ℝ), (40791769317589/100000000000000 : ℝ), (14595568458279/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1081059737/2000000000 : ℝ)|^2153 ≤ (22306331107453/50000000000000 : ℝ)^1641
        have hw : |(1081059737/2000000000 : ℝ)|=(1081059737/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(504872127/1000000000 : ℝ)|^2153 ≤ (40791769317589/100000000000000 : ℝ)^1641
        have hw : |(504872127/1000000000 : ℝ)|=(504872127/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2306618129/10000000000 : ℝ)|^2153 ≤ (14595568458279/100000000000000 : ℝ)^1641
        have hw : |(-2306618129/10000000000 : ℝ)|=(2306618129/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1346_s1_3 (p : ℝ) (hpa : (4305/1024 : ℝ) ≤ p) (hpb : p ≤ (2153/512 : ℝ)) (x : Fin 3 → ℝ) :
    (858319199/2000000000 : ℝ)*x 0 + (3712574239/10000000000 : ℝ)*x 1 + (4953621593/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (858319199/2000000000 : ℝ)^2153 ≤ (32960524628491/100000000000000 : ℝ)^1641 := by
    have hnat : (858319199 : ℕ)^2153*100000000000000^1641 ≤ 32960524628491^1641*2000000000^2153 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      858319199 2000000000 32960524628491 100000000000000 2153 1641 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3712574239/10000000000 : ℝ)^2153 ≤ (425825554683/1562500000000 : ℝ)^1641 := by
    have hnat : (3712574239 : ℕ)^2153*1562500000000^1641 ≤ 425825554683^1641*10000000000^2153 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3712574239 10000000000 425825554683 1562500000000 2153 1641 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4953621593/10000000000 : ℝ)^2153 ≤ (9946659964259/25000000000000 : ℝ)^1641 := by
    have hnat : (4953621593 : ℕ)^2153*25000000000000^1641 ≤ 9946659964259^1641*10000000000^2153 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4953621593 10000000000 9946659964259 25000000000000 2153 1641 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2153/512 : ℝ)) 2153 1641 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(858319199/2000000000 : ℝ), (3712574239/10000000000 : ℝ), (4953621593/10000000000 : ℝ)] ![(32960524628491/100000000000000 : ℝ), (425825554683/1562500000000 : ℝ), (9946659964259/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(858319199/2000000000 : ℝ)|^2153 ≤ (32960524628491/100000000000000 : ℝ)^1641
        have hw : |(858319199/2000000000 : ℝ)|=(858319199/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3712574239/10000000000 : ℝ)|^2153 ≤ (425825554683/1562500000000 : ℝ)^1641
        have hw : |(3712574239/10000000000 : ℝ)|=(3712574239/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4953621593/10000000000 : ℝ)|^2153 ≤ (9946659964259/25000000000000 : ℝ)^1641
        have hw : |(4953621593/10000000000 : ℝ)|=(4953621593/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1346_s1_4 (p : ℝ) (hpa : (4305/1024 : ℝ) ≤ p) (hpb : p ≤ (2153/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-995777401/5000000000 : ℝ)*x 0 + (632015237/1250000000 : ℝ)*x 1 + (5632803083/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (995777401/5000000000 : ℝ)^2153 ≤ (6018757351093/50000000000000 : ℝ)^1641 := by
    have hnat : (995777401 : ℕ)^2153*50000000000000^1641 ≤ 6018757351093^1641*5000000000^2153 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      995777401 5000000000 6018757351093 50000000000000 2153 1641 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (632015237/1250000000 : ℝ)^2153 ≤ (20435118815823/50000000000000 : ℝ)^1641 := by
    have hnat : (632015237 : ℕ)^2153*50000000000000^1641 ≤ 20435118815823^1641*1250000000^2153 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      632015237 1250000000 20435118815823 50000000000000 2153 1641 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5632803083/10000000000 : ℝ)^2153 ≤ (9418449531637/20000000000000 : ℝ)^1641 := by
    have hnat : (5632803083 : ℕ)^2153*20000000000000^1641 ≤ 9418449531637^1641*10000000000^2153 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5632803083 10000000000 9418449531637 20000000000000 2153 1641 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2153/512 : ℝ)) 2153 1641 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-995777401/5000000000 : ℝ), (632015237/1250000000 : ℝ), (5632803083/10000000000 : ℝ)] ![(6018757351093/50000000000000 : ℝ), (20435118815823/50000000000000 : ℝ), (9418449531637/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-995777401/5000000000 : ℝ)|^2153 ≤ (6018757351093/50000000000000 : ℝ)^1641
        have hw : |(-995777401/5000000000 : ℝ)|=(995777401/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(632015237/1250000000 : ℝ)|^2153 ≤ (20435118815823/50000000000000 : ℝ)^1641
        have hw : |(632015237/1250000000 : ℝ)|=(632015237/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5632803083/10000000000 : ℝ)|^2153 ≤ (9418449531637/20000000000000 : ℝ)^1641
        have hw : |(5632803083/10000000000 : ℝ)|=(5632803083/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1346_s1_5 (p : ℝ) (hpa : (4305/1024 : ℝ) ≤ p) (hpb : p ≤ (2153/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5251731441/10000000000 : ℝ)*x 0 + (-430633969/2500000000 : ℝ)*x 1 + (2816401563/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5251731441/10000000000 : ℝ)^2153 ≤ (42957156770019/100000000000000 : ℝ)^1641 := by
    have hnat : (5251731441 : ℕ)^2153*100000000000000^1641 ≤ 42957156770019^1641*10000000000^2153 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5251731441 10000000000 42957156770019 100000000000000 2153 1641 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (430633969/2500000000 : ℝ)^2153 ≤ (9950595089751/100000000000000 : ℝ)^1641 := by
    have hnat : (430633969 : ℕ)^2153*100000000000000^1641 ≤ 9950595089751^1641*2500000000^2153 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      430633969 2500000000 9950595089751 100000000000000 2153 1641 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2816401563/5000000000 : ℝ)^2153 ≤ (11773062032461/25000000000000 : ℝ)^1641 := by
    have hnat : (2816401563 : ℕ)^2153*25000000000000^1641 ≤ 11773062032461^1641*5000000000^2153 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2816401563 5000000000 11773062032461 25000000000000 2153 1641 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2153/512 : ℝ)) 2153 1641 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5251731441/10000000000 : ℝ), (-430633969/2500000000 : ℝ), (2816401563/5000000000 : ℝ)] ![(42957156770019/100000000000000 : ℝ), (9950595089751/100000000000000 : ℝ), (11773062032461/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5251731441/10000000000 : ℝ)|^2153 ≤ (42957156770019/100000000000000 : ℝ)^1641
        have hw : |(5251731441/10000000000 : ℝ)|=(5251731441/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-430633969/2500000000 : ℝ)|^2153 ≤ (9950595089751/100000000000000 : ℝ)^1641
        have hw : |(-430633969/2500000000 : ℝ)|=(430633969/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2816401563/5000000000 : ℝ)|^2153 ≤ (11773062032461/25000000000000 : ℝ)^1641
        have hw : |(2816401563/5000000000 : ℝ)|=(2816401563/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1346_s1_6 (p : ℝ) (hpa : (4305/1024 : ℝ) ≤ p) (hpb : p ≤ (2153/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5251731341/10000000000 : ℝ)*x 0 + (5632803193/10000000000 : ℝ)*x 1 + (-1722535921/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5251731341/10000000000 : ℝ)^2153 ≤ (42957155696849/100000000000000 : ℝ)^1641 := by
    have hnat : (5251731341 : ℕ)^2153*100000000000000^1641 ≤ 42957155696849^1641*10000000000^2153 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5251731341 10000000000 42957155696849 100000000000000 2153 1641 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5632803193/10000000000 : ℝ)^2153 ≤ (11773062216189/25000000000000 : ℝ)^1641 := by
    have hnat : (5632803193 : ℕ)^2153*25000000000000^1641 ≤ 11773062216189^1641*10000000000^2153 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5632803193 10000000000 11773062216189 25000000000000 2153 1641 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1722535921/10000000000 : ℝ)^2153 ≤ (9950595430809/100000000000000 : ℝ)^1641 := by
    have hnat : (1722535921 : ℕ)^2153*100000000000000^1641 ≤ 9950595430809^1641*10000000000^2153 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1722535921 10000000000 9950595430809 100000000000000 2153 1641 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2153/512 : ℝ)) 2153 1641 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5251731341/10000000000 : ℝ), (5632803193/10000000000 : ℝ), (-1722535921/10000000000 : ℝ)] ![(42957155696849/100000000000000 : ℝ), (11773062216189/25000000000000 : ℝ), (9950595430809/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5251731341/10000000000 : ℝ)|^2153 ≤ (42957155696849/100000000000000 : ℝ)^1641
        have hw : |(5251731341/10000000000 : ℝ)|=(5251731341/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5632803193/10000000000 : ℝ)|^2153 ≤ (11773062216189/25000000000000 : ℝ)^1641
        have hw : |(5632803193/10000000000 : ℝ)|=(5632803193/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1722535921/10000000000 : ℝ)|^2153 ≤ (9950595430809/100000000000000 : ℝ)^1641
        have hw : |(-1722535921/10000000000 : ℝ)|=(1722535921/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1346_s1_7 (p : ℝ) (hpa : (4305/1024 : ℝ) ≤ p) (hpb : p ≤ (2153/512 : ℝ)) (x : Fin 3 → ℝ) :
    (85854131/200000000 : ℝ)*x 0 + (1234524427/2500000000 : ℝ)*x 1 + (466047371/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (85854131/200000000 : ℝ)^2153 ≤ (1648585780703/5000000000000 : ℝ)^1641 := by
    have hnat : (85854131 : ℕ)^2153*5000000000000^1641 ≤ 1648585780703^1641*200000000^2153 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      85854131 200000000 1648585780703 5000000000000 2153 1641 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1234524427/2500000000 : ℝ)^2153 ≤ (39623132320757/100000000000000 : ℝ)^1641 := by
    have hnat : (1234524427 : ℕ)^2153*100000000000000^1641 ≤ 39623132320757^1641*2500000000^2153 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1234524427 2500000000 39623132320757 100000000000000 2153 1641 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (466047371/1250000000 : ℝ)^2153 ≤ (5481030409997/20000000000000 : ℝ)^1641 := by
    have hnat : (466047371 : ℕ)^2153*20000000000000^1641 ≤ 5481030409997^1641*1250000000^2153 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      466047371 1250000000 5481030409997 20000000000000 2153 1641 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2153/512 : ℝ)) 2153 1641 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(85854131/200000000 : ℝ), (1234524427/2500000000 : ℝ), (466047371/1250000000 : ℝ)] ![(1648585780703/5000000000000 : ℝ), (39623132320757/100000000000000 : ℝ), (5481030409997/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(85854131/200000000 : ℝ)|^2153 ≤ (1648585780703/5000000000000 : ℝ)^1641
        have hw : |(85854131/200000000 : ℝ)|=(85854131/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1234524427/2500000000 : ℝ)|^2153 ≤ (39623132320757/100000000000000 : ℝ)^1641
        have hw : |(1234524427/2500000000 : ℝ)|=(1234524427/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(466047371/1250000000 : ℝ)|^2153 ≤ (5481030409997/20000000000000 : ℝ)^1641
        have hw : |(466047371/1250000000 : ℝ)|=(466047371/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1346_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4305/1024 : ℝ) ≤ p) (hpb : p ≤ (2153/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (9680391/6250000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (13421/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (361/25000 : ℝ)*pair X i i ≤ pair X i h) :
    (6927/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (19431/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (13421/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (361/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (13421/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (361/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (13421/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (361/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (13421/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (361/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (13421/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (361/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (13421/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (361/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (361/25000 : ℝ) ^ (4305/1024 : ℝ) ≤ (1830769048017/100000000000000000000 : ℝ) := by
    have hpowers : (361/25000 : ℝ)^4305 ≤ (1830769048017/100000000000000000000 : ℝ)^1024 := by
      have hnat : (361 : ℕ)^4305*100000000000000000000^1024 ≤ 1830769048017^1024*25000^4305 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        361 25000 1830769048017 100000000000000000000 4305 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (361/25000 : ℝ)) (X := (1830769048017/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4305 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (13421/50000 : ℝ) ^ (4305/1024 : ℝ) ≤ (19844936580342653/5000000000000000000 : ℝ) := by
    have hpowers : (13421/50000 : ℝ)^4305 ≤ (19844936580342653/5000000000000000000 : ℝ)^1024 := by
      have hnat : (13421 : ℕ)^4305*5000000000000000000^1024 ≤ 19844936580342653^1024*50000^4305 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        13421 50000 19844936580342653 5000000000000000000 4305 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (13421/50000 : ℝ)) (X := (19844936580342653/5000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4305 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50000001830769048017/50000000000000000000 : ℝ) ≤ (400000003483777/400000000000000 : ℝ) ^ (4305/1024 : ℝ) := by
    have hpowers : (50000001830769048017/50000000000000000000 : ℝ)^1024 ≤ (400000003483777/400000000000000 : ℝ)^4305 := by
      have hnat : (50000001830769048017 : ℕ)^1024*400000000000000^4305 ≤ 400000003483777^4305*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50000001830769048017 50000000000000000000 400000003483777 400000000000000 1024 4305 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (400000003483777/400000000000000 : ℝ)) (X := (50000001830769048017/50000000000000000000 : ℝ)) (by norm_num) 4305 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100396900562375901077/100000000000000000000 : ℝ) ≤ (10009426548209591/10000000000000000 : ℝ) ^ (4305/1024 : ℝ) := by
    have hpowers : (100396900562375901077/100000000000000000000 : ℝ)^1024 ≤ (10009426548209591/10000000000000000 : ℝ)^4305 := by
      have hnat : (100396900562375901077 : ℕ)^1024*10000000000000000^4305 ≤ 10009426548209591^4305*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100396900562375901077 100000000000000000000 10009426548209591 10000000000000000 1024 4305 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10009426548209591/10000000000000000 : ℝ)) (X := (100396900562375901077/100000000000000000000 : ℝ)) (by norm_num) 4305 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (2519844936580342653/2500000000000000000 : ℝ) ≤ (10018853009324757/10000000000000000 : ℝ) ^ (4305/1024 : ℝ) := by
    have hpowers : (2519844936580342653/2500000000000000000 : ℝ)^1024 ≤ (10018853009324757/10000000000000000 : ℝ)^4305 := by
      have hnat : (2519844936580342653 : ℕ)^1024*10000000000000000^4305 ≤ 10018853009324757^4305*2500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2519844936580342653 2500000000000000000 10018853009324757 10000000000000000 1024 4305 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10018853009324757/10000000000000000 : ℝ)) (X := (2519844936580342653/2500000000000000000 : ℝ)) (by norm_num) 4305 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(1830769048017/100000000000000000000 : ℝ) ≤ ((126976389296161803371/126990000000000000000 : ℝ)+2*(4713230557583/1269900000000000 : ℝ)*(361/25000 : ℝ))^(4305/1024 : ℝ) := by
    rw [show (126976389296161803371/126990000000000000000 : ℝ)+2*(4713230557583/1269900000000000 : ℝ)*(361/25000 : ℝ)=(400000003483777/400000000000000 : ℝ) by norm_num, show 1+2*(1830769048017/100000000000000000000 : ℝ)=(50000001830769048017/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(19844936580342653/5000000000000000000 : ℝ)+(1830769048017/100000000000000000000 : ℝ) ≤ ((126976389296161803371/126990000000000000000 : ℝ)+(4713230557583/1269900000000000 : ℝ)*((13421/50000 : ℝ)+(361/25000 : ℝ)))^(4305/1024 : ℝ) := by
    rw [show (126976389296161803371/126990000000000000000 : ℝ)+(4713230557583/1269900000000000 : ℝ)*((13421/50000 : ℝ)+(361/25000 : ℝ))=(10009426548209591/10000000000000000 : ℝ) by norm_num, show 1+(19844936580342653/5000000000000000000 : ℝ)+(1830769048017/100000000000000000000 : ℝ)=(100396900562375901077/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(19844936580342653/5000000000000000000 : ℝ) ≤ ((126976389296161803371/126990000000000000000 : ℝ)+2*(4713230557583/1269900000000000 : ℝ)*(13421/50000 : ℝ))^(4305/1024 : ℝ) := by
    rw [show (126976389296161803371/126990000000000000000 : ℝ)+2*(4713230557583/1269900000000000 : ℝ)*(13421/50000 : ℝ)=(10018853009324757/10000000000000000 : ℝ) by norm_num, show 1+2*(19844936580342653/5000000000000000000 : ℝ)=(2519844936580342653/2500000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (126976389296161803371/126990000000000000000 : ℝ)*(X 1 0+X 2 0)+(4713230557583/1269900000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4305/1024 : ℝ)) (lo := (361/25000 : ℝ)) (hi := (13421/50000 : ℝ)) (c := (126976389296161803371/126990000000000000000 : ℝ)) (alpha := (4713230557583/1269900000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (126976389296161803371/126990000000000000000 : ℝ)*(X 0 1+X 2 1)+(4713230557583/1269900000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4305/1024 : ℝ)) (lo := (361/25000 : ℝ)) (hi := (13421/50000 : ℝ)) (c := (126976389296161803371/126990000000000000000 : ℝ)) (alpha := (4713230557583/1269900000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (126976389296161803371/126990000000000000000 : ℝ)*(X 0 2+X 1 2)+(4713230557583/1269900000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4305/1024 : ℝ)) (lo := (361/25000 : ℝ)) (hi := (13421/50000 : ℝ)) (c := (126976389296161803371/126990000000000000000 : ℝ)) (alpha := (4713230557583/1269900000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1991025513/10000000000 : ℝ)*X 0 0+(1128067569/2000000000 : ℝ)*X 0 1+(631090167/1250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1346_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((675662339/1250000000 : ℝ)*X 1 0+(-2306617723/10000000000 : ℝ)*X 1 1+(126218039/250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1346_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1081059737/2000000000 : ℝ)*X 2 0+(504872127/1000000000 : ℝ)*X 2 1+(-2306618129/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1346_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((858319199/2000000000 : ℝ)*X 0 0+(3712574239/10000000000 : ℝ)*X 0 1+(4953621593/10000000000 : ℝ)*X 0 2+(858319199/2000000000 : ℝ)*X 1 0+(3712574239/10000000000 : ℝ)*X 1 1+(4953621593/10000000000 : ℝ)*X 1 2+(858319199/2000000000 : ℝ)*X 2 0+(3712574239/10000000000 : ℝ)*X 2 1+(4953621593/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1346_s1_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-995777401/5000000000 : ℝ)*X 0 0+(632015237/1250000000 : ℝ)*X 0 1+(5632803083/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1346_s1_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5251731441/10000000000 : ℝ)*X 1 0+(-430633969/2500000000 : ℝ)*X 1 1+(2816401563/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1346_s1_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5251731341/10000000000 : ℝ)*X 2 0+(5632803193/10000000000 : ℝ)*X 2 1+(-1722535921/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1346_s1_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((85854131/200000000 : ℝ)*X 0 0+(1234524427/2500000000 : ℝ)*X 0 1+(466047371/1250000000 : ℝ)*X 0 2+(85854131/200000000 : ℝ)*X 1 0+(1234524427/2500000000 : ℝ)*X 1 1+(466047371/1250000000 : ℝ)*X 1 2+(85854131/200000000 : ℝ)*X 2 0+(1234524427/2500000000 : ℝ)*X 2 1+(466047371/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1346_s1_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (2778872701246055616410643/415000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (41862629/100000000000000 : ℝ)*(base1) + (1019958111/100000000000000 : ℝ)*(base19) + (252878729/25000000000000 : ℝ)*(base23) + (202269717/100000000000000 : ℝ)*(upper3) + (8271107/25000000000000 : ℝ)*(upper5) + (12480366643083/1000000000000 : ℝ)*(major0) + (12480366643083/1000000000000 : ℝ)*(major1) + (12480366643083/1000000000000 : ℝ)*(major2) + (422572857097967/25000000000000 : ℝ)*(sp0) + (1690295836136293/100000000000000 : ℝ)*(sp1) + (52821745143109/3125000000000 : ℝ)*(sp2) + (805773181342711/100000000000000 : ℝ)*(sp3) + (2734782583/50000000000000 : ℝ)*(sp4) + (121044569/4000000000000 : ℝ)*(sp7) + (161155249863913/20000000000000 : ℝ)*(f.failure) + (422574214023601/25000000000000 : ℝ)*(f.sum) + (53568968397/83000000000000000000000000 : ℝ)*base66 + (153342359616881/830000000000000000000000000000 : ℝ)*base67 + (591203682303119/830000000000000000000000000000 : ℝ)*base70 + (2375363350763119/830000000000000000000000000000 : ℝ)*base72 + (22666919289/8300000000000000000000000 : ℝ)*base73 + (352889645123119/830000000000000000000000000000 : ℝ)*base76 + (5077028841883119/830000000000000000000000000000 : ℝ)*base78 + (2403314191496881/830000000000000000000000000000 : ℝ)*base79 + (212920817167/83000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base83 + (370017/125000000000000000000 : ℝ)*base90 + (370017/125000000000000000000 : ℝ)*base92 + (370017/125000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (3368673964690023018786762011/1058250000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (18554593/50000000000000 : ℝ)*(base1) + (330089679/50000000000000 : ℝ)*(base19) + (624061319/100000000000000 : ℝ)*(base23) + (36933923/50000000000000 : ℝ)*(upper3) + (65941281/100000000000000 : ℝ)*(upper5) + (640174686787841/50000000000000 : ℝ)*(major0) + (640174686787841/50000000000000 : ℝ)*(major1) + (640174686787841/50000000000000 : ℝ)*(major2) + (688256827/20000000000000 : ℝ)*(sp1) + (833823643/25000000000000 : ℝ)*(sp2) + (433515052564733/25000000000000 : ℝ)*(sp4) + (1734056071686253/100000000000000 : ℝ)*(sp5) + (346811242758771/20000000000000 : ℝ)*(sp6) + (413319215392053/50000000000000 : ℝ)*(sp7) + (206659616973323/25000000000000 : ℝ)*(f.failure) + (867030086574873/50000000000000 : ℝ)*(f.sum) + (62261324962393/31747500000000000000000000000 : ℝ)*base65 + (27016328107274087989/6349500000000000000000000000000000 : ℝ)*base68 + (29135574333752087989/6349500000000000000000000000000000 : ℝ)*base70 + (43577124948387587989/6349500000000000000000000000000000 : ℝ)*base72 + (224267645203181/63495000000000000000000000000 : ℝ)*base73 + (21329044486608912011/6349500000000000000000000000000000 : ℝ)*base75 + (53906699062746587989/6349500000000000000000000000000000 : ℝ)*base78 + (7620509435867412011/6349500000000000000000000000000000 : ℝ)*base79 + (91002462925931/63495000000000000000000000000 : ℝ)*base81 + (84293/156250000000000000000 : ℝ)*base89 + (84293/156250000000000000000 : ℝ)*base91 + (84293/156250000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1346_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4305/1024 : ℝ) ≤ p) (hpb : p ≤ (2153/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (9680391/6250000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (13421/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (361/25000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (6927/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (19431/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1346_s1 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1346_s2_0 (p : ℝ) (hpa : (4305/1024 : ℝ) ≤ p) (hpb : p ≤ (2153/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-2030831787/10000000000 : ℝ)*x 0 + (1095730481/2000000000 : ℝ)*x 1 + (5184902843/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2030831787/10000000000 : ℝ)^2153 ≤ (12349940080143/100000000000000 : ℝ)^1641 := by
    have hnat : (2030831787 : ℕ)^2153*100000000000000^1641 ≤ 12349940080143^1641*10000000000^2153 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2030831787 10000000000 12349940080143 100000000000000 2153 1641 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1095730481/2000000000 : ℝ)^2153 ≤ (22704329810741/50000000000000 : ℝ)^1641 := by
    have hnat : (1095730481 : ℕ)^2153*50000000000000^1641 ≤ 22704329810741^1641*2000000000^2153 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1095730481 2000000000 22704329810741 50000000000000 2153 1641 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5184902843/10000000000 : ℝ)^2153 ≤ (2112070014271/5000000000000 : ℝ)^1641 := by
    have hnat : (5184902843 : ℕ)^2153*5000000000000^1641 ≤ 2112070014271^1641*10000000000^2153 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5184902843 10000000000 2112070014271 5000000000000 2153 1641 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2153/512 : ℝ)) 2153 1641 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2030831787/10000000000 : ℝ), (1095730481/2000000000 : ℝ), (5184902843/10000000000 : ℝ)] ![(12349940080143/100000000000000 : ℝ), (22704329810741/50000000000000 : ℝ), (2112070014271/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2030831787/10000000000 : ℝ)|^2153 ≤ (12349940080143/100000000000000 : ℝ)^1641
        have hw : |(-2030831787/10000000000 : ℝ)|=(2030831787/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1095730481/2000000000 : ℝ)|^2153 ≤ (22704329810741/50000000000000 : ℝ)^1641
        have hw : |(1095730481/2000000000 : ℝ)|=(1095730481/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5184902843/10000000000 : ℝ)|^2153 ≤ (2112070014271/5000000000000 : ℝ)^1641
        have hw : |(5184902843/10000000000 : ℝ)|=(5184902843/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1346_s2_1 (p : ℝ) (hpa : (4305/1024 : ℝ) ≤ p) (hpb : p ≤ (2153/512 : ℝ)) (x : Fin 3 → ℝ) :
    (1073134069/2000000000 : ℝ)*x 0 + (-136411299/625000000 : ℝ)*x 1 + (1296225809/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1073134069/2000000000 : ℝ)^2153 ≤ (44184032830563/100000000000000 : ℝ)^1641 := by
    have hnat : (1073134069 : ℕ)^2153*100000000000000^1641 ≤ 44184032830563^1641*2000000000^2153 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1073134069 2000000000 44184032830563 100000000000000 2153 1641 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (136411299/625000000 : ℝ)^2153 ≤ (1696820333357/12500000000000 : ℝ)^1641 := by
    have hnat : (136411299 : ℕ)^2153*12500000000000^1641 ≤ 1696820333357^1641*625000000^2153 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      136411299 625000000 1696820333357 12500000000000 2153 1641 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1296225809/2500000000 : ℝ)^2153 ≤ (42241404486159/100000000000000 : ℝ)^1641 := by
    have hnat : (1296225809 : ℕ)^2153*100000000000000^1641 ≤ 42241404486159^1641*2500000000^2153 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1296225809 2500000000 42241404486159 100000000000000 2153 1641 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2153/512 : ℝ)) 2153 1641 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1073134069/2000000000 : ℝ), (-136411299/625000000 : ℝ), (1296225809/2500000000 : ℝ)] ![(44184032830563/100000000000000 : ℝ), (1696820333357/12500000000000 : ℝ), (42241404486159/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1073134069/2000000000 : ℝ)|^2153 ≤ (44184032830563/100000000000000 : ℝ)^1641
        have hw : |(1073134069/2000000000 : ℝ)|=(1073134069/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-136411299/625000000 : ℝ)|^2153 ≤ (1696820333357/12500000000000 : ℝ)^1641
        have hw : |(-136411299/625000000 : ℝ)|=(136411299/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1296225809/2500000000 : ℝ)|^2153 ≤ (42241404486159/100000000000000 : ℝ)^1641
        have hw : |(1296225809/2500000000 : ℝ)|=(1296225809/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1346_s2_2 (p : ℝ) (hpa : (4305/1024 : ℝ) ≤ p) (hpb : p ≤ (2153/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2682835213/5000000000 : ℝ)*x 0 + (5184903143/10000000000 : ℝ)*x 1 + (-2182580799/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2682835213/5000000000 : ℝ)^2153 ≤ (44184033705671/100000000000000 : ℝ)^1641 := by
    have hnat : (2682835213 : ℕ)^2153*100000000000000^1641 ≤ 44184033705671^1641*5000000000^2153 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2682835213 5000000000 44184033705671 100000000000000 2153 1641 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5184903143/10000000000 : ℝ)^2153 ≤ (42241403492091/100000000000000 : ℝ)^1641 := by
    have hnat : (5184903143 : ℕ)^2153*100000000000000^1641 ≤ 42241403492091^1641*10000000000^2153 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5184903143 10000000000 42241403492091 100000000000000 2153 1641 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2182580799/10000000000 : ℝ)^2153 ≤ (1696820348657/12500000000000 : ℝ)^1641 := by
    have hnat : (2182580799 : ℕ)^2153*12500000000000^1641 ≤ 1696820348657^1641*10000000000^2153 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2182580799 10000000000 1696820348657 12500000000000 2153 1641 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2153/512 : ℝ)) 2153 1641 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2682835213/5000000000 : ℝ), (5184903143/10000000000 : ℝ), (-2182580799/10000000000 : ℝ)] ![(44184033705671/100000000000000 : ℝ), (42241403492091/100000000000000 : ℝ), (1696820348657/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2682835213/5000000000 : ℝ)|^2153 ≤ (44184033705671/100000000000000 : ℝ)^1641
        have hw : |(2682835213/5000000000 : ℝ)|=(2682835213/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5184903143/10000000000 : ℝ)|^2153 ≤ (42241403492091/100000000000000 : ℝ)^1641
        have hw : |(5184903143/10000000000 : ℝ)|=(5184903143/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2182580799/10000000000 : ℝ)|^2153 ≤ (1696820348657/12500000000000 : ℝ)^1641
        have hw : |(-2182580799/10000000000 : ℝ)|=(2182580799/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1346_s2_3 (p : ℝ) (hpa : (4305/1024 : ℝ) ≤ p) (hpb : p ≤ (2153/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2159722321/5000000000 : ℝ)*x 0 + (2010783827/5000000000 : ℝ)*x 1 + (4637772719/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2159722321/5000000000 : ℝ)^2153 ≤ (8115582479/24414062500 : ℝ)^1641 := by
    have hnat : (2159722321 : ℕ)^2153*24414062500^1641 ≤ 8115582479^1641*5000000000^2153 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2159722321 5000000000 8115582479 24414062500 2153 1641 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2010783827/5000000000 : ℝ)^2153 ≤ (30266681652847/100000000000000 : ℝ)^1641 := by
    have hnat : (2010783827 : ℕ)^2153*100000000000000^1641 ≤ 30266681652847^1641*5000000000^2153 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2010783827 5000000000 30266681652847 100000000000000 2153 1641 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4637772719/10000000000 : ℝ)^2153 ≤ (36491892499359/100000000000000 : ℝ)^1641 := by
    have hnat : (4637772719 : ℕ)^2153*100000000000000^1641 ≤ 36491892499359^1641*10000000000^2153 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4637772719 10000000000 36491892499359 100000000000000 2153 1641 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2153/512 : ℝ)) 2153 1641 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2159722321/5000000000 : ℝ), (2010783827/5000000000 : ℝ), (4637772719/10000000000 : ℝ)] ![(8115582479/24414062500 : ℝ), (30266681652847/100000000000000 : ℝ), (36491892499359/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2159722321/5000000000 : ℝ)|^2153 ≤ (8115582479/24414062500 : ℝ)^1641
        have hw : |(2159722321/5000000000 : ℝ)|=(2159722321/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2010783827/5000000000 : ℝ)|^2153 ≤ (30266681652847/100000000000000 : ℝ)^1641
        have hw : |(2010783827/5000000000 : ℝ)|=(2010783827/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4637772719/10000000000 : ℝ)|^2153 ≤ (36491892499359/100000000000000 : ℝ)^1641
        have hw : |(4637772719/10000000000 : ℝ)|=(4637772719/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1346_s2_4 (p : ℝ) (hpa : (4305/1024 : ℝ) ≤ p) (hpb : p ≤ (2153/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-101544829/500000000 : ℝ)*x 0 + (2593368713/5000000000 : ℝ)*x 1 + (68460017/125000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (101544829/500000000 : ℝ)^2153 ≤ (6175228519867/50000000000000 : ℝ)^1641 := by
    have hnat : (101544829 : ℕ)^2153*50000000000000^1641 ≤ 6175228519867^1641*500000000^2153 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      101544829 500000000 6175228519867 50000000000000 2153 1641 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2593368713/5000000000 : ℝ)^2153 ≤ (42261011047333/100000000000000 : ℝ)^1641 := by
    have hnat : (2593368713 : ℕ)^2153*100000000000000^1641 ≤ 42261011047333^1641*5000000000^2153 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2593368713 5000000000 42261011047333 100000000000000 2153 1641 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (68460017/125000000 : ℝ)^2153 ≤ (45388531906791/100000000000000 : ℝ)^1641 := by
    have hnat : (68460017 : ℕ)^2153*100000000000000^1641 ≤ 45388531906791^1641*125000000^2153 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      68460017 125000000 45388531906791 100000000000000 2153 1641 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2153/512 : ℝ)) 2153 1641 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-101544829/500000000 : ℝ), (2593368713/5000000000 : ℝ), (68460017/125000000 : ℝ)] ![(6175228519867/50000000000000 : ℝ), (42261011047333/100000000000000 : ℝ), (45388531906791/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-101544829/500000000 : ℝ)|^2153 ≤ (6175228519867/50000000000000 : ℝ)^1641
        have hw : |(-101544829/500000000 : ℝ)|=(101544829/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2593368713/5000000000 : ℝ)|^2153 ≤ (42261011047333/100000000000000 : ℝ)^1641
        have hw : |(2593368713/5000000000 : ℝ)|=(2593368713/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(68460017/125000000 : ℝ)|^2153 ≤ (45388531906791/100000000000000 : ℝ)^1641
        have hw : |(68460017/125000000 : ℝ)|=(68460017/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1346_s2_5 (p : ℝ) (hpa : (4305/1024 : ℝ) ≤ p) (hpb : p ≤ (2153/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2644961851/5000000000 : ℝ)*x 0 + (-1890682361/10000000000 : ℝ)*x 1 + (1369200337/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2644961851/5000000000 : ℝ)^2153 ≤ (8673497765331/20000000000000 : ℝ)^1641 := by
    have hnat : (2644961851 : ℕ)^2153*20000000000000^1641 ≤ 8673497765331^1641*5000000000^2153 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2644961851 5000000000 8673497765331 20000000000000 2153 1641 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1890682361/10000000000 : ℝ)^2153 ≤ (11243979382111/100000000000000 : ℝ)^1641 := by
    have hnat : (1890682361 : ℕ)^2153*100000000000000^1641 ≤ 11243979382111^1641*10000000000^2153 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1890682361 10000000000 11243979382111 100000000000000 2153 1641 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1369200337/2500000000 : ℝ)^2153 ≤ (45388531776313/100000000000000 : ℝ)^1641 := by
    have hnat : (1369200337 : ℕ)^2153*100000000000000^1641 ≤ 45388531776313^1641*2500000000^2153 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1369200337 2500000000 45388531776313 100000000000000 2153 1641 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2153/512 : ℝ)) 2153 1641 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2644961851/5000000000 : ℝ), (-1890682361/10000000000 : ℝ), (1369200337/2500000000 : ℝ)] ![(8673497765331/20000000000000 : ℝ), (11243979382111/100000000000000 : ℝ), (45388531776313/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2644961851/5000000000 : ℝ)|^2153 ≤ (8673497765331/20000000000000 : ℝ)^1641
        have hw : |(2644961851/5000000000 : ℝ)|=(2644961851/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1890682361/10000000000 : ℝ)|^2153 ≤ (11243979382111/100000000000000 : ℝ)^1641
        have hw : |(-1890682361/10000000000 : ℝ)|=(1890682361/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1369200337/2500000000 : ℝ)|^2153 ≤ (45388531776313/100000000000000 : ℝ)^1641
        have hw : |(1369200337/2500000000 : ℝ)|=(1369200337/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1346_s2_6 (p : ℝ) (hpa : (4305/1024 : ℝ) ≤ p) (hpb : p ≤ (2153/512 : ℝ)) (x : Fin 3 → ℝ) :
    (1057984741/2000000000 : ℝ)*x 0 + (5476801367/10000000000 : ℝ)*x 1 + (-1890682331/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1057984741/2000000000 : ℝ)^2153 ≤ (43367488858923/100000000000000 : ℝ)^1641 := by
    have hnat : (1057984741 : ℕ)^2153*100000000000000^1641 ≤ 43367488858923^1641*2000000000^2153 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1057984741 2000000000 43367488858923 100000000000000 2153 1641 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5476801367/10000000000 : ℝ)^2153 ≤ (45388531982903/100000000000000 : ℝ)^1641 := by
    have hnat : (5476801367 : ℕ)^2153*100000000000000^1641 ≤ 45388531982903^1641*10000000000^2153 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5476801367 10000000000 45388531982903 100000000000000 2153 1641 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1890682331/10000000000 : ℝ)^2153 ≤ (5621989574017/50000000000000 : ℝ)^1641 := by
    have hnat : (1890682331 : ℕ)^2153*50000000000000^1641 ≤ 5621989574017^1641*10000000000^2153 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1890682331 10000000000 5621989574017 50000000000000 2153 1641 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2153/512 : ℝ)) 2153 1641 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1057984741/2000000000 : ℝ), (5476801367/10000000000 : ℝ), (-1890682331/10000000000 : ℝ)] ![(43367488858923/100000000000000 : ℝ), (45388531982903/100000000000000 : ℝ), (5621989574017/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1057984741/2000000000 : ℝ)|^2153 ≤ (43367488858923/100000000000000 : ℝ)^1641
        have hw : |(1057984741/2000000000 : ℝ)|=(1057984741/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5476801367/10000000000 : ℝ)|^2153 ≤ (45388531982903/100000000000000 : ℝ)^1641
        have hw : |(5476801367/10000000000 : ℝ)|=(5476801367/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1890682331/10000000000 : ℝ)|^2153 ≤ (5621989574017/50000000000000 : ℝ)^1641
        have hw : |(-1890682331/10000000000 : ℝ)|=(1890682331/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1346_s2_7 (p : ℝ) (hpa : (4305/1024 : ℝ) ≤ p) (hpb : p ≤ (2153/512 : ℝ)) (x : Fin 3 → ℝ) :
    (1079895227/2500000000 : ℝ)*x 0 + (289620307/625000000 : ℝ)*x 1 + (4025450031/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1079895227/2500000000 : ℝ)^2153 ≤ (33242801702159/100000000000000 : ℝ)^1641 := by
    have hnat : (1079895227 : ℕ)^2153*100000000000000^1641 ≤ 33242801702159^1641*2500000000^2153 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1079895227 2500000000 33242801702159 100000000000000 2153 1641 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (289620307/625000000 : ℝ)^2153 ≤ (18226087612849/50000000000000 : ℝ)^1641 := by
    have hnat : (289620307 : ℕ)^2153*50000000000000^1641 ≤ 18226087612849^1641*625000000^2153 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      289620307 625000000 18226087612849 50000000000000 2153 1641 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4025450031/10000000000 : ℝ)^2153 ≤ (3788127881649/12500000000000 : ℝ)^1641 := by
    have hnat : (4025450031 : ℕ)^2153*12500000000000^1641 ≤ 3788127881649^1641*10000000000^2153 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4025450031 10000000000 3788127881649 12500000000000 2153 1641 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2153/512 : ℝ)) 2153 1641 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1079895227/2500000000 : ℝ), (289620307/625000000 : ℝ), (4025450031/10000000000 : ℝ)] ![(33242801702159/100000000000000 : ℝ), (18226087612849/50000000000000 : ℝ), (3788127881649/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1079895227/2500000000 : ℝ)|^2153 ≤ (33242801702159/100000000000000 : ℝ)^1641
        have hw : |(1079895227/2500000000 : ℝ)|=(1079895227/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(289620307/625000000 : ℝ)|^2153 ≤ (18226087612849/50000000000000 : ℝ)^1641
        have hw : |(289620307/625000000 : ℝ)|=(289620307/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4025450031/10000000000 : ℝ)|^2153 ≤ (3788127881649/12500000000000 : ℝ)^1641
        have hw : |(4025450031/10000000000 : ℝ)|=(4025450031/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1346_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4305/1024 : ℝ) ≤ p) (hpb : p ≤ (2153/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (9680391/6250000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (19431/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (6927/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (4939/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (2011/12500 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (19431/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (6927/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (19431/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (6927/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (19431/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (6927/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (19431/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (6927/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (19431/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (6927/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (19431/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (6927/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (6927/100000 : ℝ) ^ (4305/1024 : ℝ) ≤ (166895345415211/12500000000000000000 : ℝ) := by
    have hpowers : (6927/100000 : ℝ)^4305 ≤ (166895345415211/12500000000000000000 : ℝ)^1024 := by
      have hnat : (6927 : ℕ)^4305*12500000000000000000^1024 ≤ 166895345415211^1024*100000^4305 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6927 100000 166895345415211 12500000000000000000 4305 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (6927/100000 : ℝ)) (X := (166895345415211/12500000000000000000 : ℝ)) (by norm_num) (by norm_num) 4305 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (19431/100000 : ℝ) ^ (4305/1024 : ℝ) ≤ (102037863312660613/100000000000000000000 : ℝ) := by
    have hpowers : (19431/100000 : ℝ)^4305 ≤ (102037863312660613/100000000000000000000 : ℝ)^1024 := by
      have hnat : (19431 : ℕ)^4305*100000000000000000000^1024 ≤ 102037863312660613^1024*100000^4305 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        19431 100000 102037863312660613 100000000000000000000 4305 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (19431/100000 : ℝ)) (X := (102037863312660613/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4305 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (6250166895345415211/6250000000000000000 : ℝ) ≤ (10000063516504413/10000000000000000 : ℝ) ^ (4305/1024 : ℝ) := by
    have hpowers : (6250166895345415211/6250000000000000000 : ℝ)^1024 ≤ (10000063516504413/10000000000000000 : ℝ)^4305 := by
      have hnat : (6250166895345415211 : ℕ)^1024*10000000000000000^4305 ≤ 10000063516504413^4305*6250000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6250166895345415211 6250000000000000000 10000063516504413 10000000000000000 1024 4305 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000063516504413/10000000000000000 : ℝ)) (X := (6250166895345415211/6250000000000000000 : ℝ)) (by norm_num) 4305 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100103373026075982301/100000000000000000000 : ℝ) ≤ (10002457893281873/10000000000000000 : ℝ) ^ (4305/1024 : ℝ) := by
    have hpowers : (100103373026075982301/100000000000000000000 : ℝ)^1024 ≤ (10002457893281873/10000000000000000 : ℝ)^4305 := by
      have hnat : (100103373026075982301 : ℕ)^1024*10000000000000000^4305 ≤ 10002457893281873^4305*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100103373026075982301 100000000000000000000 10002457893281873 10000000000000000 1024 4305 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10002457893281873/10000000000000000 : ℝ)) (X := (100103373026075982301/100000000000000000000 : ℝ)) (by norm_num) 4305 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50102037863312660613/50000000000000000000 : ℝ) ≤ (10004852270059333/10000000000000000 : ℝ) ^ (4305/1024 : ℝ) := by
    have hpowers : (50102037863312660613/50000000000000000000 : ℝ)^1024 ≤ (10004852270059333/10000000000000000 : ℝ)^4305 := by
      have hnat : (50102037863312660613 : ℕ)^1024*10000000000000000^4305 ≤ 10004852270059333^4305*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50102037863312660613 50000000000000000000 10004852270059333 10000000000000000 1024 4305 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10004852270059333/10000000000000000 : ℝ)) (X := (50102037863312660613/50000000000000000000 : ℝ)) (by norm_num) 4305 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(166895345415211/12500000000000000000 : ℝ) ≤ ((1302162734526002597/1302500000000000000 : ℝ)+2*(119718838873/62520000000000 : ℝ)*(6927/100000 : ℝ))^(4305/1024 : ℝ) := by
    rw [show (1302162734526002597/1302500000000000000 : ℝ)+2*(119718838873/62520000000000 : ℝ)*(6927/100000 : ℝ)=(10000063516504413/10000000000000000 : ℝ) by norm_num, show 1+2*(166895345415211/12500000000000000000 : ℝ)=(6250166895345415211/6250000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(102037863312660613/100000000000000000000 : ℝ)+(166895345415211/12500000000000000000 : ℝ) ≤ ((1302162734526002597/1302500000000000000 : ℝ)+(119718838873/62520000000000 : ℝ)*((19431/100000 : ℝ)+(6927/100000 : ℝ)))^(4305/1024 : ℝ) := by
    rw [show (1302162734526002597/1302500000000000000 : ℝ)+(119718838873/62520000000000 : ℝ)*((19431/100000 : ℝ)+(6927/100000 : ℝ))=(10002457893281873/10000000000000000 : ℝ) by norm_num, show 1+(102037863312660613/100000000000000000000 : ℝ)+(166895345415211/12500000000000000000 : ℝ)=(100103373026075982301/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(102037863312660613/100000000000000000000 : ℝ) ≤ ((1302162734526002597/1302500000000000000 : ℝ)+2*(119718838873/62520000000000 : ℝ)*(19431/100000 : ℝ))^(4305/1024 : ℝ) := by
    rw [show (1302162734526002597/1302500000000000000 : ℝ)+2*(119718838873/62520000000000 : ℝ)*(19431/100000 : ℝ)=(10004852270059333/10000000000000000 : ℝ) by norm_num, show 1+2*(102037863312660613/100000000000000000000 : ℝ)=(50102037863312660613/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1302162734526002597/1302500000000000000 : ℝ)*(X 1 0+X 2 0)+(119718838873/62520000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4305/1024 : ℝ)) (lo := (6927/100000 : ℝ)) (hi := (19431/100000 : ℝ)) (c := (1302162734526002597/1302500000000000000 : ℝ)) (alpha := (119718838873/62520000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1302162734526002597/1302500000000000000 : ℝ)*(X 0 1+X 2 1)+(119718838873/62520000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4305/1024 : ℝ)) (lo := (6927/100000 : ℝ)) (hi := (19431/100000 : ℝ)) (c := (1302162734526002597/1302500000000000000 : ℝ)) (alpha := (119718838873/62520000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1302162734526002597/1302500000000000000 : ℝ)*(X 0 2+X 1 2)+(119718838873/62520000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4305/1024 : ℝ)) (lo := (6927/100000 : ℝ)) (hi := (19431/100000 : ℝ)) (c := (1302162734526002597/1302500000000000000 : ℝ)) (alpha := (119718838873/62520000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2030831787/10000000000 : ℝ)*X 0 0+(1095730481/2000000000 : ℝ)*X 0 1+(5184902843/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1346_s2_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1073134069/2000000000 : ℝ)*X 1 0+(-136411299/625000000 : ℝ)*X 1 1+(1296225809/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1346_s2_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2682835213/5000000000 : ℝ)*X 2 0+(5184903143/10000000000 : ℝ)*X 2 1+(-2182580799/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1346_s2_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2159722321/5000000000 : ℝ)*X 0 0+(2010783827/5000000000 : ℝ)*X 0 1+(4637772719/10000000000 : ℝ)*X 0 2+(2159722321/5000000000 : ℝ)*X 1 0+(2010783827/5000000000 : ℝ)*X 1 1+(4637772719/10000000000 : ℝ)*X 1 2+(2159722321/5000000000 : ℝ)*X 2 0+(2010783827/5000000000 : ℝ)*X 2 1+(4637772719/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1346_s2_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-101544829/500000000 : ℝ)*X 0 0+(2593368713/5000000000 : ℝ)*X 0 1+(68460017/125000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1346_s2_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2644961851/5000000000 : ℝ)*X 1 0+(-1890682361/10000000000 : ℝ)*X 1 1+(1369200337/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1346_s2_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1057984741/2000000000 : ℝ)*X 2 0+(5476801367/10000000000 : ℝ)*X 2 1+(-1890682331/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1346_s2_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((1079895227/2500000000 : ℝ)*X 0 0+(289620307/625000000 : ℝ)*X 0 1+(4025450031/10000000000 : ℝ)*X 0 2+(1079895227/2500000000 : ℝ)*X 1 0+(289620307/625000000 : ℝ)*X 1 1+(4025450031/10000000000 : ℝ)*X 1 2+(1079895227/2500000000 : ℝ)*X 2 0+(289620307/625000000 : ℝ)*X 2 1+(4025450031/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1346_s2_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (191265529504168164825219073/32562500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (971957191/100000000000000 : ℝ)*(base19) + (504733763/50000000000000 : ℝ)*(base23) + (465497/6250000000000 : ℝ)*(lower2) + (12986697/10000000000000 : ℝ)*(upper3) + (58726441/50000000000000 : ℝ)*(upper5) + (2513571215543953/100000000000000 : ℝ)*(major0) + (2513571215543953/100000000000000 : ℝ)*(major1) + (2513571215543953/100000000000000 : ℝ)*(major2) + (10638363498459/312500000000 : ℝ)*(sp0) + (1702145757552091/50000000000000 : ℝ)*(sp1) + (3404291477593847/100000000000000 : ℝ)*(sp2) + (1622842897838457/100000000000000 : ℝ)*(sp3) + (16167554493/100000000000000 : ℝ)*(sp4) + (6850394823/100000000000000 : ℝ)*(sp7) + (5071405463229/312500000000 : ℝ)*(f.failure) + (3404292487061373/100000000000000 : ℝ)*(f.sum) + (7218628079459/3126000000000000000000000000 : ℝ)*base66 + (1871693747036499677/390750000000000000000000000000000 : ℝ)*base68 + (1642172098604499677/390750000000000000000000000000000 : ℝ)*base70 + (3190442797673499677/390750000000000000000000000000000 : ℝ)*base72 + (6706756795547/3126000000000000000000000000 : ℝ)*base74 + (1279714702941500323/390750000000000000000000000000000 : ℝ)*base75 + (2230989789677499677/390750000000000000000000000000000 : ℝ)*base78 + (1529459150983749677/390750000000000000000000000000000 : ℝ)*base80 + (19947675587249/3126000000000000000000000000 : ℝ)*base82 + (42031/7812500000000000000 : ℝ)*base89 + (42031/7812500000000000000 : ℝ)*base91 + (42031/7812500000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (180453590072815180278023889/32562500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (234528369/20000000000000 : ℝ)*(base19) + (666721523/50000000000000 : ℝ)*(base23) + (280479/195312500000 : ℝ)*(upper3) + (62010747/100000000000000 : ℝ)*(lower4) + (19157689/25000000000000 : ℝ)*(upper5) + (1272741868750007/50000000000000 : ℝ)*(major0) + (1272741868750007/50000000000000 : ℝ)*(major1) + (1272741868750007/50000000000000 : ℝ)*(major2) + (6554803201/50000000000000 : ℝ)*(sp1) + (3203266733/20000000000000 : ℝ)*(sp2) + (344751369843367/10000000000000 : ℝ)*(sp4) + (1723749708092711/50000000000000 : ℝ)*(sp5) + (3447496348656959/100000000000000 : ℝ)*(sp6) + (821726795920489/50000000000000 : ℝ)*(sp7) + (821726795920489/50000000000000 : ℝ)*(f.failure) + (344751369843367/10000000000000 : ℝ)*(f.sum) + (8593448522399/1563000000000000000000000000 : ℝ)*base65 + (1577556887430742037/195375000000000000000000000000000 : ℝ)*base67 + (1938827894279992037/195375000000000000000000000000000 : ℝ)*base69 + (3343025640689992037/195375000000000000000000000000000 : ℝ)*base71 + (4801104107273/1563000000000000000000000000 : ℝ)*base73 + (977998158371992037/195375000000000000000000000000000 : ℝ)*base75 + (1493257448950867037/195375000000000000000000000000000 : ℝ)*base77 + (230849002985242037/195375000000000000000000000000000 : ℝ)*base79 + (9705708816209/1563000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base86 + (5318801/312500000000000000000 : ℝ)*base90 + (5318801/312500000000000000000 : ℝ)*base92 + (5318801/312500000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1346_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4305/1024 : ℝ) ≤ p) (hpb : p ≤ (2153/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (9680391/6250000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (19431/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (6927/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (4939/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (2011/12500 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1346_s2 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1346_b0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4305/1024 : ℝ) ≤ p) (hpb : p ≤ (2153/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (9680391/6250000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (4939/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (2011/12500 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1346_s0 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1346_s1 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1346_s2 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4305/1024 : ℝ) ≤ p) (hpb : p ≤ (2153/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (9680391/6250000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (4939/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (2011/12500 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1346_b0 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
