-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.wide_coarse_distinct_p020_b015
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T01:38:39.06005+00:00
-- url     : https://prove2.me/submissions/a239c663-fa65-4392-b33f-7bbb6e49272e

import Definitions.Def_HlawkaSchatten_DiagonalCutoff4_FiniteCharts
import Definitions.Def_HlawkaSchatten_DiagonalCutoff4_Localization
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_ordered_majorant
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
theorem raw_linear_data {p k A : ℝ} (hp : 1 ≤ p) (X : Fin 3 → Fin 3 → ℝ)
    (h : RawFrame p k A X) :
    RawLinearData k A X (fun j => lpNorm p (X j))
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

theorem raw_linear_data_bounds {k A T : ℝ} {X : Fin 3 → Fin 3 → ℝ} {N P : Fin 3 → ℝ}
    (h : RawLinearData k A X N P T) (hA : A ≤ 3) :
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



theorem abs_signValue (b : Bool) : |signValue b|=1 := by
  cases b <;> norm_num [signValue]

theorem abs_signedPair (X : Fin 3 → Fin 3 → ℝ) (signs : Fin 3 → Fin 3 → Bool) (i h : Fin 3) :
    |signedPair X signs i h|=|pair X i h| := by
  simp [signedPair,abs_mul,abs_signValue]

theorem chart_majorant {p k A d a rho alpha beta : ℝ}
    (hp : 1 ≤ p) (ha : 0 < a) (hap : a ≤ p)
    (hrho : 0 < rho) (hrho1 : rho ≤ 1) (halpha : 0 ≤ alpha) (hbeta : 0 ≤ beta)
    (hcorner1 : 1+rho^a ≤ (1+alpha*rho)^a)
    (hcorner2 : 1+2*rho^a ≤ (1+(alpha+beta)*rho)^a)
    (X : Fin 3 → Fin 3 → ℝ) (orders : Fin 3 → Fin 3 → Fin 3)
    (signs : Fin 3 → Fin 3 → Bool) (hX : OrderedChart p k A d X orders signs)
    (i : Fin 3)
    (hratio : signedPair X signs i (orders i 1) ≤ rho*signedPair X signs i (orders i 0)) :
    lpNorm p (pair X i) ≤ signedPair X signs i (orders i 0)+
      alpha*signedPair X signs i (orders i 1)+beta*signedPair X signs i (orders i 2) := by
  obtain ⟨h2,h21,h10⟩ := hX.ordered i
  have h1 : 0 ≤ signedPair X signs i (orders i 1) := h2.trans h21
  have h0 : 0 ≤ signedPair X signs i (orders i 0) := h1.trans h10
  have hh := ordered_majorant (M := signedPair X signs i (orders i 0))
    (u := signedPair X signs i (orders i 1)) (v := signedPair X signs i (orders i 2)) hp ha hap hrho hrho1 halpha hbeta hcorner1 hcorner2 h0
    (by simpa only [abs_of_nonneg h1,abs_of_nonneg h2] using h21)
    (by simpa only [abs_of_nonneg h1] using hratio)
  have he := HlawkaSchatten.DiagonalRealBundle.lpNorm_eq3 p (pair X i)
    (i := orders i 0) (j := orders i 1) (k := orders i 2)
    ((hX.permutation i).1.ne (by decide)) ((hX.permutation i).1.ne (by decide))
    ((hX.permutation i).1.ne (by decide))
  rw [he]
  calc
    _ ≤ signedPair X signs i (orders i 0)+alpha*|signedPair X signs i (orders i 1)|+
        beta*|signedPair X signs i (orders i 2)| := by
      simpa only [abs_signedPair] using hh
    _ = _ := by rw [abs_of_nonneg h1,abs_of_nonneg h2]

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
theorem collision_support_c320030_s0_1 (p : ℝ) (hpa : (5 : ℝ) ≤ p) (hpb : p ≤ (41/8 : ℝ)) (x : Fin 3 → ℝ) :
    (3449378657/5000000000 : ℝ)*x 0 + (-1067260717/10000000000 : ℝ)*x 1 + (-9675377/25000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3449378657/5000000000 : ℝ)^41 ≤ (63049989300181/100000000000000 : ℝ)^33 := by
    have hnat : (3449378657 : ℕ)^41*100000000000000^33 ≤ 63049989300181^33*5000000000^41 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3449378657 5000000000 63049989300181 100000000000000 41 33 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1067260717/10000000000 : ℝ)^41 ≤ (3102199667111/50000000000000 : ℝ)^33 := by
    have hnat : (1067260717 : ℕ)^41*50000000000000^33 ≤ 3102199667111^33*10000000000^41 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1067260717 10000000000 3102199667111 50000000000000 41 33 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (9675377/25000000 : ℝ)^41 ≤ (30745611351579/100000000000000 : ℝ)^33 := by
    have hnat : (9675377 : ℕ)^41*100000000000000^33 ≤ 30745611351579^33*25000000^41 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      9675377 25000000 30745611351579 100000000000000 41 33 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (41/8 : ℝ)) 41 33 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3449378657/5000000000 : ℝ), (-1067260717/10000000000 : ℝ), (-9675377/25000000 : ℝ)] ![(63049989300181/100000000000000 : ℝ), (3102199667111/50000000000000 : ℝ), (30745611351579/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3449378657/5000000000 : ℝ)|^41 ≤ (63049989300181/100000000000000 : ℝ)^33
        have hw : |(3449378657/5000000000 : ℝ)|=(3449378657/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1067260717/10000000000 : ℝ)|^41 ≤ (3102199667111/50000000000000 : ℝ)^33
        have hw : |(-1067260717/10000000000 : ℝ)|=(1067260717/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-9675377/25000000 : ℝ)|^41 ≤ (30745611351579/100000000000000 : ℝ)^33
        have hw : |(-9675377/25000000 : ℝ)|=(9675377/25000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c320030_s0_2 (p : ℝ) (hpa : (5 : ℝ) ≤ p) (hpb : p ≤ (41/8 : ℝ)) (x : Fin 3 → ℝ) :
    (1275961037/5000000000 : ℝ)*x 0 + (5457140469/10000000000 : ℝ)*x 1 + (132861749/312500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1275961037/5000000000 : ℝ)^41 ≤ (18326422279597/100000000000000 : ℝ)^33 := by
    have hnat : (1275961037 : ℕ)^41*100000000000000^33 ≤ 18326422279597^33*5000000000^41 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1275961037 5000000000 18326422279597 100000000000000 41 33 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5457140469/10000000000 : ℝ)^41 ≤ (23559664888537/50000000000000 : ℝ)^33 := by
    have hnat : (5457140469 : ℕ)^41*50000000000000^33 ≤ 23559664888537^33*10000000000^41 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5457140469 10000000000 23559664888537 50000000000000 41 33 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (132861749/312500000 : ℝ)^41 ≤ (17277123964103/50000000000000 : ℝ)^33 := by
    have hnat : (132861749 : ℕ)^41*50000000000000^33 ≤ 17277123964103^33*312500000^41 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      132861749 312500000 17277123964103 50000000000000 41 33 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (41/8 : ℝ)) 41 33 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1275961037/5000000000 : ℝ), (5457140469/10000000000 : ℝ), (132861749/312500000 : ℝ)] ![(18326422279597/100000000000000 : ℝ), (23559664888537/50000000000000 : ℝ), (17277123964103/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1275961037/5000000000 : ℝ)|^41 ≤ (18326422279597/100000000000000 : ℝ)^33
        have hw : |(1275961037/5000000000 : ℝ)|=(1275961037/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5457140469/10000000000 : ℝ)|^41 ≤ (23559664888537/50000000000000 : ℝ)^33
        have hw : |(5457140469/10000000000 : ℝ)|=(5457140469/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(132861749/312500000 : ℝ)|^41 ≤ (17277123964103/50000000000000 : ℝ)^33
        have hw : |(132861749/312500000 : ℝ)|=(132861749/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c320030_s0_6 (p : ℝ) (hpa : (5 : ℝ) ≤ p) (hpb : p ≤ (41/8 : ℝ)) (x : Fin 3 → ℝ) :
    (3579157937/10000000000 : ℝ)*x 0 + (6494668023/10000000000 : ℝ)*x 1 + (-2007880597/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3579157937/10000000000 : ℝ)^41 ≤ (2790014925513/10000000000000 : ℝ)^33 := by
    have hnat : (3579157937 : ℕ)^41*10000000000000^33 ≤ 2790014925513^33*10000000000^41 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3579157937 10000000000 2790014925513 10000000000000 41 33 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (6494668023/10000000000 : ℝ)^41 ≤ (7311832469173/12500000000000 : ℝ)^33 := by
    have hnat : (6494668023 : ℕ)^41*12500000000000^33 ≤ 7311832469173^33*10000000000^41 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6494668023 10000000000 7311832469173 12500000000000 41 33 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2007880597/10000000000 : ℝ)^41 ≤ (6802595490073/50000000000000 : ℝ)^33 := by
    have hnat : (2007880597 : ℕ)^41*50000000000000^33 ≤ 6802595490073^33*10000000000^41 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2007880597 10000000000 6802595490073 50000000000000 41 33 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (41/8 : ℝ)) 41 33 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3579157937/10000000000 : ℝ), (6494668023/10000000000 : ℝ), (-2007880597/10000000000 : ℝ)] ![(2790014925513/10000000000000 : ℝ), (7311832469173/12500000000000 : ℝ), (6802595490073/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3579157937/10000000000 : ℝ)|^41 ≤ (2790014925513/10000000000000 : ℝ)^33
        have hw : |(3579157937/10000000000 : ℝ)|=(3579157937/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(6494668023/10000000000 : ℝ)|^41 ≤ (7311832469173/12500000000000 : ℝ)^33
        have hw : |(6494668023/10000000000 : ℝ)|=(6494668023/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2007880597/10000000000 : ℝ)|^41 ≤ (6802595490073/50000000000000 : ℝ)^33
        have hw : |(-2007880597/10000000000 : ℝ)|=(2007880597/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c320030_s0_7 (p : ℝ) (hpa : (5 : ℝ) ≤ p) (hpb : p ≤ (41/8 : ℝ)) (x : Fin 3 → ℝ) :
    (-351528273/1250000000 : ℝ)*x 0 + (4139011869/10000000000 : ℝ)*x 1 + (-267167627/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (351528273/1250000000 : ℝ)^41 ≤ (5169239804631/25000000000000 : ℝ)^33 := by
    have hnat : (351528273 : ℕ)^41*25000000000000^33 ≤ 5169239804631^33*1250000000^41 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      351528273 1250000000 5169239804631 25000000000000 41 33 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4139011869/10000000000 : ℝ)^41 ≤ (16710642261309/50000000000000 : ℝ)^33 := by
    have hnat : (4139011869 : ℕ)^41*50000000000000^33 ≤ 16710642261309^33*10000000000^41 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4139011869 10000000000 16710642261309 50000000000000 41 33 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (267167627/500000000 : ℝ)^41 ≤ (11475439060121/25000000000000 : ℝ)^33 := by
    have hnat : (267167627 : ℕ)^41*25000000000000^33 ≤ 11475439060121^33*500000000^41 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      267167627 500000000 11475439060121 25000000000000 41 33 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (41/8 : ℝ)) 41 33 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-351528273/1250000000 : ℝ), (4139011869/10000000000 : ℝ), (-267167627/500000000 : ℝ)] ![(5169239804631/25000000000000 : ℝ), (16710642261309/50000000000000 : ℝ), (11475439060121/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-351528273/1250000000 : ℝ)|^41 ≤ (5169239804631/25000000000000 : ℝ)^33
        have hw : |(-351528273/1250000000 : ℝ)|=(351528273/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4139011869/10000000000 : ℝ)|^41 ≤ (16710642261309/50000000000000 : ℝ)^33
        have hw : |(4139011869/10000000000 : ℝ)|=(4139011869/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-267167627/500000000 : ℝ)|^41 ≤ (11475439060121/25000000000000 : ℝ)^33
        have hw : |(-267167627/500000000 : ℝ)|=(267167627/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c320030_s0_8 (p : ℝ) (hpa : (5 : ℝ) ≤ p) (hpb : p ≤ (41/8 : ℝ)) (x : Fin 3 → ℝ) :
    (3590438303/5000000000 : ℝ)*x 0 + (-591627477/10000000000 : ℝ)*x 1 + (-3870579547/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3590438303/5000000000 : ℝ)^41 ≤ (16567287290893/25000000000000 : ℝ)^33 := by
    have hnat : (3590438303 : ℕ)^41*25000000000000^33 ≤ 16567287290893^33*5000000000^41 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3590438303 5000000000 16567287290893 25000000000000 41 33 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (591627477/10000000000 : ℝ)^41 ≤ (2981007603933/100000000000000 : ℝ)^33 := by
    have hnat : (591627477 : ℕ)^41*100000000000000^33 ≤ 2981007603933^33*10000000000^41 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      591627477 10000000000 2981007603933 100000000000000 41 33 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3870579547/10000000000 : ℝ)^41 ≤ (30749843219339/100000000000000 : ℝ)^33 := by
    have hnat : (3870579547 : ℕ)^41*100000000000000^33 ≤ 30749843219339^33*10000000000^41 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3870579547 10000000000 30749843219339 100000000000000 41 33 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (41/8 : ℝ)) 41 33 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3590438303/5000000000 : ℝ), (-591627477/10000000000 : ℝ), (-3870579547/10000000000 : ℝ)] ![(16567287290893/25000000000000 : ℝ), (2981007603933/100000000000000 : ℝ), (30749843219339/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3590438303/5000000000 : ℝ)|^41 ≤ (16567287290893/25000000000000 : ℝ)^33
        have hw : |(3590438303/5000000000 : ℝ)|=(3590438303/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-591627477/10000000000 : ℝ)|^41 ≤ (2981007603933/100000000000000 : ℝ)^33
        have hw : |(-591627477/10000000000 : ℝ)|=(591627477/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-3870579547/10000000000 : ℝ)|^41 ≤ (30749843219339/100000000000000 : ℝ)^33
        have hw : |(-3870579547/10000000000 : ℝ)|=(3870579547/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c320030_s0_9 (p : ℝ) (hpa : (5 : ℝ) ≤ p) (hpb : p ≤ (41/8 : ℝ)) (x : Fin 3 → ℝ) :
    (201206623/1000000000 : ℝ)*x 0 + (6277862783/10000000000 : ℝ)*x 1 + (3823013691/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (201206623/1000000000 : ℝ)^41 ≤ (682021839477/5000000000000 : ℝ)^33 := by
    have hnat : (201206623 : ℕ)^41*5000000000000^33 ≤ 682021839477^33*1000000000^41 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      201206623 1000000000 682021839477 5000000000000 41 33 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (6277862783/10000000000 : ℝ)^41 ≤ (28039257350413/50000000000000 : ℝ)^33 := by
    have hnat : (6277862783 : ℕ)^41*50000000000000^33 ≤ 28039257350413^33*10000000000^41 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6277862783 10000000000 28039257350413 50000000000000 41 33 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3823013691/10000000000 : ℝ)^41 ≤ (1514052424537/5000000000000 : ℝ)^33 := by
    have hnat : (3823013691 : ℕ)^41*5000000000000^33 ≤ 1514052424537^33*10000000000^41 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3823013691 10000000000 1514052424537 5000000000000 41 33 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (41/8 : ℝ)) 41 33 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(201206623/1000000000 : ℝ), (6277862783/10000000000 : ℝ), (3823013691/10000000000 : ℝ)] ![(682021839477/5000000000000 : ℝ), (28039257350413/50000000000000 : ℝ), (1514052424537/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(201206623/1000000000 : ℝ)|^41 ≤ (682021839477/5000000000000 : ℝ)^33
        have hw : |(201206623/1000000000 : ℝ)|=(201206623/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(6277862783/10000000000 : ℝ)|^41 ≤ (28039257350413/50000000000000 : ℝ)^33
        have hw : |(6277862783/10000000000 : ℝ)|=(6277862783/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3823013691/10000000000 : ℝ)|^41 ≤ (1514052424537/5000000000000 : ℝ)^33
        have hw : |(3823013691/10000000000 : ℝ)|=(3823013691/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c320030_s0_12 (p : ℝ) (hpa : (5 : ℝ) ≤ p) (hpb : p ≤ (41/8 : ℝ)) (x : Fin 3 → ℝ) :
    (3033400649/10000000000 : ℝ)*x 0 + (7222179977/10000000000 : ℝ)*x 1 + (-65401589/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3033400649/10000000000 : ℝ)^41 ≤ (2271626851737/10000000000000 : ℝ)^33 := by
    have hnat : (3033400649 : ℕ)^41*10000000000000^33 ≤ 2271626851737^33*10000000000^41 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3033400649 10000000000 2271626851737 10000000000000 41 33 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (7222179977/10000000000 : ℝ)^41 ≤ (16685763622447/25000000000000 : ℝ)^33 := by
    have hnat : (7222179977 : ℕ)^41*25000000000000^33 ≤ 16685763622447^33*10000000000^41 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7222179977 10000000000 16685763622447 25000000000000 41 33 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (65401589/400000000 : ℝ)^41 ≤ (10540676986909/100000000000000 : ℝ)^33 := by
    have hnat : (65401589 : ℕ)^41*100000000000000^33 ≤ 10540676986909^33*400000000^41 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      65401589 400000000 10540676986909 100000000000000 41 33 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (41/8 : ℝ)) 41 33 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3033400649/10000000000 : ℝ), (7222179977/10000000000 : ℝ), (-65401589/400000000 : ℝ)] ![(2271626851737/10000000000000 : ℝ), (16685763622447/25000000000000 : ℝ), (10540676986909/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3033400649/10000000000 : ℝ)|^41 ≤ (2271626851737/10000000000000 : ℝ)^33
        have hw : |(3033400649/10000000000 : ℝ)|=(3033400649/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(7222179977/10000000000 : ℝ)|^41 ≤ (16685763622447/25000000000000 : ℝ)^33
        have hw : |(7222179977/10000000000 : ℝ)|=(7222179977/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-65401589/400000000 : ℝ)|^41 ≤ (10540676986909/100000000000000 : ℝ)^33
        have hw : |(-65401589/400000000 : ℝ)|=(65401589/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c320030_s0_13 (p : ℝ) (hpa : (5 : ℝ) ≤ p) (hpb : p ≤ (41/8 : ℝ)) (x : Fin 3 → ℝ) :
    (-3035995819/10000000000 : ℝ)*x 0 + (4663598961/10000000000 : ℝ)*x 1 + (-579736243/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3035995819/10000000000 : ℝ)^41 ≤ (11370208447867/50000000000000 : ℝ)^33 := by
    have hnat : (3035995819 : ℕ)^41*50000000000000^33 ≤ 11370208447867^33*10000000000^41 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3035995819 10000000000 11370208447867 50000000000000 41 33 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4663598961/10000000000 : ℝ)^41 ≤ (7752489374283/20000000000000 : ℝ)^33 := by
    have hnat : (4663598961 : ℕ)^41*20000000000000^33 ≤ 7752489374283^33*10000000000^41 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4663598961 10000000000 7752489374283 20000000000000 41 33 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (579736243/1250000000 : ℝ)^41 ≤ (7699427245333/20000000000000 : ℝ)^33 := by
    have hnat : (579736243 : ℕ)^41*20000000000000^33 ≤ 7699427245333^33*1250000000^41 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      579736243 1250000000 7699427245333 20000000000000 41 33 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (41/8 : ℝ)) 41 33 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-3035995819/10000000000 : ℝ), (4663598961/10000000000 : ℝ), (-579736243/1250000000 : ℝ)] ![(11370208447867/50000000000000 : ℝ), (7752489374283/20000000000000 : ℝ), (7699427245333/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-3035995819/10000000000 : ℝ)|^41 ≤ (11370208447867/50000000000000 : ℝ)^33
        have hw : |(-3035995819/10000000000 : ℝ)|=(3035995819/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4663598961/10000000000 : ℝ)|^41 ≤ (7752489374283/20000000000000 : ℝ)^33
        have hw : |(4663598961/10000000000 : ℝ)|=(4663598961/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-579736243/1250000000 : ℝ)|^41 ≤ (7699427245333/20000000000000 : ℝ)^33
        have hw : |(-579736243/1250000000 : ℝ)|=(579736243/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c320030_s0_14 (p : ℝ) (hpa : (5 : ℝ) ≤ p) (hpb : p ≤ (41/8 : ℝ)) (x : Fin 3 → ℝ) :
    (3492686749/5000000000 : ℝ)*x 0 + (-272683759/2500000000 : ℝ)*x 1 + (-3752695313/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3492686749/5000000000 : ℝ)^41 ≤ (32017500585359/50000000000000 : ℝ)^33 := by
    have hnat : (3492686749 : ℕ)^41*50000000000000^33 ≤ 32017500585359^33*5000000000^41 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3492686749 5000000000 32017500585359 50000000000000 41 33 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (272683759/2500000000 : ℝ)^41 ≤ (1274879332423/20000000000000 : ℝ)^33 := by
    have hnat : (272683759 : ℕ)^41*20000000000000^33 ≤ 1274879332423^33*2500000000^41 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      272683759 2500000000 1274879332423 20000000000000 41 33 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3752695313/10000000000 : ℝ)^41 ≤ (7397650539027/25000000000000 : ℝ)^33 := by
    have hnat : (3752695313 : ℕ)^41*25000000000000^33 ≤ 7397650539027^33*10000000000^41 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3752695313 10000000000 7397650539027 25000000000000 41 33 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (41/8 : ℝ)) 41 33 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3492686749/5000000000 : ℝ), (-272683759/2500000000 : ℝ), (-3752695313/10000000000 : ℝ)] ![(32017500585359/50000000000000 : ℝ), (1274879332423/20000000000000 : ℝ), (7397650539027/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3492686749/5000000000 : ℝ)|^41 ≤ (32017500585359/50000000000000 : ℝ)^33
        have hw : |(3492686749/5000000000 : ℝ)|=(3492686749/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-272683759/2500000000 : ℝ)|^41 ≤ (1274879332423/20000000000000 : ℝ)^33
        have hw : |(-272683759/2500000000 : ℝ)|=(272683759/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-3752695313/10000000000 : ℝ)|^41 ≤ (7397650539027/25000000000000 : ℝ)^33
        have hw : |(-3752695313/10000000000 : ℝ)|=(3752695313/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c320030_s0_15 (p : ℝ) (hpa : (5 : ℝ) ≤ p) (hpb : p ≤ (41/8 : ℝ)) (x : Fin 3 → ℝ) :
    (2369699957/10000000000 : ℝ)*x 0 + (5411876433/10000000000 : ℝ)*x 1 + (2229004059/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2369699957/10000000000 : ℝ)^41 ≤ (4178725862623/25000000000000 : ℝ)^33 := by
    have hnat : (2369699957 : ℕ)^41*25000000000000^33 ≤ 4178725862623^33*10000000000^41 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2369699957 10000000000 4178725862623 25000000000000 41 33 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5411876433/10000000000 : ℝ)^41 ≤ (46634243051239/100000000000000 : ℝ)^33 := by
    have hnat : (5411876433 : ℕ)^41*100000000000000^33 ≤ 46634243051239^33*10000000000^41 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5411876433 10000000000 46634243051239 100000000000000 41 33 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2229004059/5000000000 : ℝ)^41 ≤ (36650853493093/100000000000000 : ℝ)^33 := by
    have hnat : (2229004059 : ℕ)^41*100000000000000^33 ≤ 36650853493093^33*5000000000^41 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2229004059 5000000000 36650853493093 100000000000000 41 33 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (41/8 : ℝ)) 41 33 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2369699957/10000000000 : ℝ), (5411876433/10000000000 : ℝ), (2229004059/5000000000 : ℝ)] ![(4178725862623/25000000000000 : ℝ), (46634243051239/100000000000000 : ℝ), (36650853493093/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2369699957/10000000000 : ℝ)|^41 ≤ (4178725862623/25000000000000 : ℝ)^33
        have hw : |(2369699957/10000000000 : ℝ)|=(2369699957/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5411876433/10000000000 : ℝ)|^41 ≤ (46634243051239/100000000000000 : ℝ)^33
        have hw : |(5411876433/10000000000 : ℝ)|=(5411876433/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2229004059/5000000000 : ℝ)|^41 ≤ (36650853493093/100000000000000 : ℝ)^33
        have hw : |(2229004059/5000000000 : ℝ)|=(2229004059/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c320030_s0_17 (p : ℝ) (hpa : (5 : ℝ) ≤ p) (hpb : p ≤ (41/8 : ℝ)) (x : Fin 3 → ℝ) :
    (-683/5000000000 : ℝ)*x 0 + (1249999997/1250000000 : ℝ)*x 1 + (0 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (683/5000000000 : ℝ)^41 ≤ (148009/50000000000000 : ℝ)^33 := by
    have hnat : (683 : ℕ)^41*50000000000000^33 ≤ 148009^33*5000000000^41 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      683 5000000000 148009 50000000000000 41 33 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1249999997/1250000000 : ℝ)^41 ≤ (99999999701819/100000000000000 : ℝ)^33 := by
    have hnat : (1249999997 : ℕ)^41*100000000000000^33 ≤ 99999999701819^33*1250000000^41 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1249999997 1250000000 99999999701819 100000000000000 41 33 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (0 : ℝ)^41 ≤ (0 : ℝ)^33 := by
    have hnat : (0 : ℕ)^41*1^33 ≤ 0^33*1^41 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      0 1 0 1 41 33 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (41/8 : ℝ)) 41 33 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-683/5000000000 : ℝ), (1249999997/1250000000 : ℝ), (0 : ℝ)] ![(148009/50000000000000 : ℝ), (99999999701819/100000000000000 : ℝ), (0 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-683/5000000000 : ℝ)|^41 ≤ (148009/50000000000000 : ℝ)^33
        have hw : |(-683/5000000000 : ℝ)|=(683/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1249999997/1250000000 : ℝ)|^41 ≤ (99999999701819/100000000000000 : ℝ)^33
        have hw : |(1249999997/1250000000 : ℝ)|=(1249999997/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(0 : ℝ)|^41 ≤ (0 : ℝ)^33
        have hw : |(0 : ℝ)|=(0 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c320030_s0_19 (p : ℝ) (hpa : (5 : ℝ) ≤ p) (hpb : p ≤ (41/8 : ℝ)) (x : Fin 3 → ℝ) :
    (682807859/2000000000 : ℝ)*x 0 + (3262998069/5000000000 : ℝ)*x 1 + (-2153833657/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (682807859/2000000000 : ℝ)^41 ≤ (210480310573/800000000000 : ℝ)^33 := by
    have hnat : (682807859 : ℕ)^41*800000000000^33 ≤ 210480310573^33*2000000000^41 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      682807859 2000000000 210480310573 800000000000 41 33 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3262998069/5000000000 : ℝ)^41 ≤ (29422712673489/50000000000000 : ℝ)^33 := by
    have hnat : (3262998069 : ℕ)^41*50000000000000^33 ≤ 29422712673489^33*5000000000^41 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3262998069 5000000000 29422712673489 50000000000000 41 33 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2153833657/10000000000 : ℝ)^41 ≤ (14844535821161/100000000000000 : ℝ)^33 := by
    have hnat : (2153833657 : ℕ)^41*100000000000000^33 ≤ 14844535821161^33*10000000000^41 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2153833657 10000000000 14844535821161 100000000000000 41 33 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (41/8 : ℝ)) 41 33 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(682807859/2000000000 : ℝ), (3262998069/5000000000 : ℝ), (-2153833657/10000000000 : ℝ)] ![(210480310573/800000000000 : ℝ), (29422712673489/50000000000000 : ℝ), (14844535821161/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(682807859/2000000000 : ℝ)|^41 ≤ (210480310573/800000000000 : ℝ)^33
        have hw : |(682807859/2000000000 : ℝ)|=(682807859/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3262998069/5000000000 : ℝ)|^41 ≤ (29422712673489/50000000000000 : ℝ)^33
        have hw : |(3262998069/5000000000 : ℝ)|=(3262998069/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2153833657/10000000000 : ℝ)|^41 ≤ (14844535821161/100000000000000 : ℝ)^33
        have hw : |(-2153833657/10000000000 : ℝ)|=(2153833657/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c320030_s0_20 (p : ℝ) (hpa : (5 : ℝ) ≤ p) (hpb : p ≤ (41/8 : ℝ)) (x : Fin 3 → ℝ) :
    (-2327493651/10000000000 : ℝ)*x 0 + (642822469/1250000000 : ℝ)*x 1 + (-38176309/80000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2327493651/10000000000 : ℝ)^41 ≤ (1634582821481/10000000000000 : ℝ)^33 := by
    have hnat : (2327493651 : ℕ)^41*10000000000000^33 ≤ 1634582821481^33*10000000000^41 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2327493651 10000000000 1634582821481 10000000000000 41 33 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (642822469/1250000000 : ℝ)^41 ≤ (5471095931669/12500000000000 : ℝ)^33 := by
    have hnat : (642822469 : ℕ)^41*12500000000000^33 ≤ 5471095931669^33*1250000000^41 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      642822469 1250000000 5471095931669 12500000000000 41 33 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (38176309/80000000 : ℝ)^41 ≤ (19942702153857/50000000000000 : ℝ)^33 := by
    have hnat : (38176309 : ℕ)^41*50000000000000^33 ≤ 19942702153857^33*80000000^41 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      38176309 80000000 19942702153857 50000000000000 41 33 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (41/8 : ℝ)) 41 33 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2327493651/10000000000 : ℝ), (642822469/1250000000 : ℝ), (-38176309/80000000 : ℝ)] ![(1634582821481/10000000000000 : ℝ), (5471095931669/12500000000000 : ℝ), (19942702153857/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2327493651/10000000000 : ℝ)|^41 ≤ (1634582821481/10000000000000 : ℝ)^33
        have hw : |(-2327493651/10000000000 : ℝ)|=(2327493651/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(642822469/1250000000 : ℝ)|^41 ≤ (5471095931669/12500000000000 : ℝ)^33
        have hw : |(642822469/1250000000 : ℝ)|=(642822469/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-38176309/80000000 : ℝ)|^41 ≤ (19942702153857/50000000000000 : ℝ)^33
        have hw : |(-38176309/80000000 : ℝ)|=(38176309/80000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c320030_s0_21 (p : ℝ) (hpa : (5 : ℝ) ≤ p) (hpb : p ≤ (41/8 : ℝ)) (x : Fin 3 → ℝ) :
    (1917579719/2500000000 : ℝ)*x 0 + (-659277039/10000000000 : ℝ)*x 1 + (-3240962941/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1917579719/2500000000 : ℝ)^41 ≤ (71926578140751/100000000000000 : ℝ)^33 := by
    have hnat : (1917579719 : ℕ)^41*100000000000000^33 ≤ 71926578140751^33*2500000000^41 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1917579719 2500000000 71926578140751 100000000000000 41 33 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (659277039/10000000000 : ℝ)^41 ≤ (1705106058447/50000000000000 : ℝ)^33 := by
    have hnat : (659277039 : ℕ)^41*50000000000000^33 ≤ 1705106058447^33*10000000000^41 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      659277039 10000000000 1705106058447 50000000000000 41 33 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3240962941/10000000000 : ℝ)^41 ≤ (1233160486351/5000000000000 : ℝ)^33 := by
    have hnat : (3240962941 : ℕ)^41*5000000000000^33 ≤ 1233160486351^33*10000000000^41 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3240962941 10000000000 1233160486351 5000000000000 41 33 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (41/8 : ℝ)) 41 33 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1917579719/2500000000 : ℝ), (-659277039/10000000000 : ℝ), (-3240962941/10000000000 : ℝ)] ![(71926578140751/100000000000000 : ℝ), (1705106058447/50000000000000 : ℝ), (1233160486351/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1917579719/2500000000 : ℝ)|^41 ≤ (71926578140751/100000000000000 : ℝ)^33
        have hw : |(1917579719/2500000000 : ℝ)|=(1917579719/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-659277039/10000000000 : ℝ)|^41 ≤ (1705106058447/50000000000000 : ℝ)^33
        have hw : |(-659277039/10000000000 : ℝ)|=(659277039/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-3240962941/10000000000 : ℝ)|^41 ≤ (1233160486351/5000000000000 : ℝ)^33
        have hw : |(-3240962941/10000000000 : ℝ)|=(3240962941/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c320030_s0_22 (p : ℝ) (hpa : (5 : ℝ) ≤ p) (hpb : p ≤ (41/8 : ℝ)) (x : Fin 3 → ℝ) :
    (1100799517/5000000000 : ℝ)*x 0 + (5494696403/10000000000 : ℝ)*x 1 + (225695903/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1100799517/5000000000 : ℝ)^41 ≤ (15254642646413/100000000000000 : ℝ)^33 := by
    have hnat : (1100799517 : ℕ)^41*100000000000000^33 ≤ 15254642646413^33*5000000000^41 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1100799517 5000000000 15254642646413 100000000000000 41 33 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5494696403/10000000000 : ℝ)^41 ≤ (23761275766691/50000000000000 : ℝ)^33 := by
    have hnat : (5494696403 : ℕ)^41*50000000000000^33 ≤ 23761275766691^33*10000000000^41 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5494696403 10000000000 23761275766691 50000000000000 41 33 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (225695903/500000000 : ℝ)^41 ≤ (37222805809397/100000000000000 : ℝ)^33 := by
    have hnat : (225695903 : ℕ)^41*100000000000000^33 ≤ 37222805809397^33*500000000^41 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      225695903 500000000 37222805809397 100000000000000 41 33 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (41/8 : ℝ)) 41 33 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1100799517/5000000000 : ℝ), (5494696403/10000000000 : ℝ), (225695903/500000000 : ℝ)] ![(15254642646413/100000000000000 : ℝ), (23761275766691/50000000000000 : ℝ), (37222805809397/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1100799517/5000000000 : ℝ)|^41 ≤ (15254642646413/100000000000000 : ℝ)^33
        have hw : |(1100799517/5000000000 : ℝ)|=(1100799517/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5494696403/10000000000 : ℝ)|^41 ≤ (23761275766691/50000000000000 : ℝ)^33
        have hw : |(5494696403/10000000000 : ℝ)|=(5494696403/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(225695903/500000000 : ℝ)|^41 ≤ (37222805809397/100000000000000 : ℝ)^33
        have hw : |(225695903/500000000 : ℝ)|=(225695903/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c320030_s0_25 (p : ℝ) (hpa : (5 : ℝ) ≤ p) (hpb : p ≤ (41/8 : ℝ)) (x : Fin 3 → ℝ) :
    (61592827/156250000 : ℝ)*x 0 + (6428773943/10000000000 : ℝ)*x 1 + (-66624007/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (61592827/156250000 : ℝ)^41 ≤ (15727889394711/50000000000000 : ℝ)^33 := by
    have hnat : (61592827 : ℕ)^41*50000000000000^33 ≤ 15727889394711^33*156250000^41 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      61592827 156250000 15727889394711 50000000000000 41 33 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (6428773943/10000000000 : ℝ)^41 ≤ (28879107835803/50000000000000 : ℝ)^33 := by
    have hnat : (6428773943 : ℕ)^41*50000000000000^33 ≤ 28879107835803^33*10000000000^41 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6428773943 10000000000 28879107835803 50000000000000 41 33 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (66624007/400000000 : ℝ)^41 ≤ (5393002763249/50000000000000 : ℝ)^33 := by
    have hnat : (66624007 : ℕ)^41*50000000000000^33 ≤ 5393002763249^33*400000000^41 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      66624007 400000000 5393002763249 50000000000000 41 33 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (41/8 : ℝ)) 41 33 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(61592827/156250000 : ℝ), (6428773943/10000000000 : ℝ), (-66624007/400000000 : ℝ)] ![(15727889394711/50000000000000 : ℝ), (28879107835803/50000000000000 : ℝ), (5393002763249/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(61592827/156250000 : ℝ)|^41 ≤ (15727889394711/50000000000000 : ℝ)^33
        have hw : |(61592827/156250000 : ℝ)|=(61592827/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(6428773943/10000000000 : ℝ)|^41 ≤ (28879107835803/50000000000000 : ℝ)^33
        have hw : |(6428773943/10000000000 : ℝ)|=(6428773943/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-66624007/400000000 : ℝ)|^41 ≤ (5393002763249/50000000000000 : ℝ)^33
        have hw : |(-66624007/400000000 : ℝ)|=(66624007/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c320030_s1_0 (p : ℝ) (hpa : (5 : ℝ) ≤ p) (hpb : p ≤ (41/8 : ℝ)) (x : Fin 3 → ℝ) :
    (-26399227/78125000 : ℝ)*x 0 + (4592921989/10000000000 : ℝ)*x 1 + (-2196604081/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (26399227/78125000 : ℝ)^41 ≤ (25975933458321/100000000000000 : ℝ)^33 := by
    have hnat : (26399227 : ℕ)^41*100000000000000^33 ≤ 25975933458321^33*78125000^41 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      26399227 78125000 25975933458321 100000000000000 41 33 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4592921989/10000000000 : ℝ)^41 ≤ (38033935661969/100000000000000 : ℝ)^33 := by
    have hnat : (4592921989 : ℕ)^41*100000000000000^33 ≤ 38033935661969^33*10000000000^41 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4592921989 10000000000 38033935661969 100000000000000 41 33 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2196604081/5000000000 : ℝ)^41 ≤ (35990130869383/100000000000000 : ℝ)^33 := by
    have hnat : (2196604081 : ℕ)^41*100000000000000^33 ≤ 35990130869383^33*5000000000^41 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2196604081 5000000000 35990130869383 100000000000000 41 33 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (41/8 : ℝ)) 41 33 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-26399227/78125000 : ℝ), (4592921989/10000000000 : ℝ), (-2196604081/5000000000 : ℝ)] ![(25975933458321/100000000000000 : ℝ), (38033935661969/100000000000000 : ℝ), (35990130869383/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-26399227/78125000 : ℝ)|^41 ≤ (25975933458321/100000000000000 : ℝ)^33
        have hw : |(-26399227/78125000 : ℝ)|=(26399227/78125000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4592921989/10000000000 : ℝ)|^41 ≤ (38033935661969/100000000000000 : ℝ)^33
        have hw : |(4592921989/10000000000 : ℝ)|=(4592921989/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2196604081/5000000000 : ℝ)|^41 ≤ (35990130869383/100000000000000 : ℝ)^33
        have hw : |(-2196604081/5000000000 : ℝ)|=(2196604081/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c320030_s1_1 (p : ℝ) (hpa : (5 : ℝ) ≤ p) (hpb : p ≤ (41/8 : ℝ)) (x : Fin 3 → ℝ) :
    (1149233603/2000000000 : ℝ)*x 0 + (-2309537183/10000000000 : ℝ)*x 1 + (-2076971767/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1149233603/2000000000 : ℝ)^41 ≤ (50239555930409/100000000000000 : ℝ)^33 := by
    have hnat : (1149233603 : ℕ)^41*100000000000000^33 ≤ 50239555930409^33*2000000000^41 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1149233603 2000000000 50239555930409 100000000000000 41 33 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2309537183/10000000000 : ℝ)^41 ≤ (3237859314223/20000000000000 : ℝ)^33 := by
    have hnat : (2309537183 : ℕ)^41*20000000000000^33 ≤ 3237859314223^33*10000000000^41 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2309537183 10000000000 3237859314223 20000000000000 41 33 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2076971767/5000000000 : ℝ)^41 ≤ (33571147485189/100000000000000 : ℝ)^33 := by
    have hnat : (2076971767 : ℕ)^41*100000000000000^33 ≤ 33571147485189^33*5000000000^41 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2076971767 5000000000 33571147485189 100000000000000 41 33 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (41/8 : ℝ)) 41 33 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1149233603/2000000000 : ℝ), (-2309537183/10000000000 : ℝ), (-2076971767/5000000000 : ℝ)] ![(50239555930409/100000000000000 : ℝ), (3237859314223/20000000000000 : ℝ), (33571147485189/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1149233603/2000000000 : ℝ)|^41 ≤ (50239555930409/100000000000000 : ℝ)^33
        have hw : |(1149233603/2000000000 : ℝ)|=(1149233603/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2309537183/10000000000 : ℝ)|^41 ≤ (3237859314223/20000000000000 : ℝ)^33
        have hw : |(-2309537183/10000000000 : ℝ)|=(2309537183/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2076971767/5000000000 : ℝ)|^41 ≤ (33571147485189/100000000000000 : ℝ)^33
        have hw : |(-2076971767/5000000000 : ℝ)|=(2076971767/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c320030_s1_2 (p : ℝ) (hpa : (5 : ℝ) ≤ p) (hpb : p ≤ (41/8 : ℝ)) (x : Fin 3 → ℝ) :
    (13011379/40000000 : ℝ)*x 0 + (4869249551/10000000000 : ℝ)*x 1 + (2114530443/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (13011379/40000000 : ℝ)^41 ≤ (387118717891/1562500000000 : ℝ)^33 := by
    have hnat : (13011379 : ℕ)^41*1562500000000^33 ≤ 387118717891^33*40000000^41 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      13011379 40000000 387118717891 1562500000000 41 33 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4869249551/10000000000 : ℝ)^41 ≤ (40897357982297/100000000000000 : ℝ)^33 := by
    have hnat : (4869249551 : ℕ)^41*100000000000000^33 ≤ 40897357982297^33*10000000000^41 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4869249551 10000000000 40897357982297 100000000000000 41 33 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2114530443/5000000000 : ℝ)^41 ≤ (34327044064331/100000000000000 : ℝ)^33 := by
    have hnat : (2114530443 : ℕ)^41*100000000000000^33 ≤ 34327044064331^33*5000000000^41 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2114530443 5000000000 34327044064331 100000000000000 41 33 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (41/8 : ℝ)) 41 33 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(13011379/40000000 : ℝ), (4869249551/10000000000 : ℝ), (2114530443/5000000000 : ℝ)] ![(387118717891/1562500000000 : ℝ), (40897357982297/100000000000000 : ℝ), (34327044064331/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(13011379/40000000 : ℝ)|^41 ≤ (387118717891/1562500000000 : ℝ)^33
        have hw : |(13011379/40000000 : ℝ)|=(13011379/40000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4869249551/10000000000 : ℝ)|^41 ≤ (40897357982297/100000000000000 : ℝ)^33
        have hw : |(4869249551/10000000000 : ℝ)|=(4869249551/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2114530443/5000000000 : ℝ)|^41 ≤ (34327044064331/100000000000000 : ℝ)^33
        have hw : |(2114530443/5000000000 : ℝ)|=(2114530443/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c320030_s1_6 (p : ℝ) (hpa : (5 : ℝ) ≤ p) (hpb : p ≤ (41/8 : ℝ)) (x : Fin 3 → ℝ) :
    (976114027/2500000000 : ℝ)*x 0 + (1110492179/2000000000 : ℝ)*x 1 + (-3528197/12500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (976114027/2500000000 : ℝ)^41 ≤ (31084573977803/100000000000000 : ℝ)^33 := by
    have hnat : (976114027 : ℕ)^41*100000000000000^33 ≤ 31084573977803^33*2500000000^41 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      976114027 2500000000 31084573977803 100000000000000 41 33 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1110492179/2000000000 : ℝ)^41 ≤ (24072023898453/50000000000000 : ℝ)^33 := by
    have hnat : (1110492179 : ℕ)^41*50000000000000^33 ≤ 24072023898453^33*2000000000^41 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1110492179 2000000000 24072023898453 50000000000000 41 33 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3528197/12500000 : ℝ)^41 ≤ (4154275642121/20000000000000 : ℝ)^33 := by
    have hnat : (3528197 : ℕ)^41*20000000000000^33 ≤ 4154275642121^33*12500000^41 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3528197 12500000 4154275642121 20000000000000 41 33 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (41/8 : ℝ)) 41 33 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(976114027/2500000000 : ℝ), (1110492179/2000000000 : ℝ), (-3528197/12500000 : ℝ)] ![(31084573977803/100000000000000 : ℝ), (24072023898453/50000000000000 : ℝ), (4154275642121/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(976114027/2500000000 : ℝ)|^41 ≤ (31084573977803/100000000000000 : ℝ)^33
        have hw : |(976114027/2500000000 : ℝ)|=(976114027/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1110492179/2000000000 : ℝ)|^41 ≤ (24072023898453/50000000000000 : ℝ)^33
        have hw : |(1110492179/2000000000 : ℝ)|=(1110492179/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-3528197/12500000 : ℝ)|^41 ≤ (4154275642121/20000000000000 : ℝ)^33
        have hw : |(-3528197/12500000 : ℝ)|=(3528197/12500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_c320030 (p : ℝ) (hpa : (5 : ℝ) ≤ p) (hpb : p ≤ (41/8 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (4693/2500 : ℝ) (1059/625 : ℝ) (80273/100000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![false, true, true], ![true, true, false]]) : False := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : RawLinearData _ _ X N P T := raw_linear_data (by linarith : (1 : ℝ) ≤ p) X hX.raw
  have bounds := raw_linear_data_bounds f (by norm_num)
  have main0 : (80273/100000 : ℝ)*P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.main 0
    change (80273/100000 : ℝ)*P 0 ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order0 : 0 ≤ ((1 : ℝ)*(X 1 2+X 2 2)) ∧ ((1 : ℝ)*(X 1 2+X 2 2)) ≤ ((1 : ℝ)*(X 1 1+X 2 1)) ∧ ((1 : ℝ)*(X 1 1+X 2 1)) ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.ordered 0
    change 0 ≤ ((1 : ℝ)*pair X 0 2) ∧ ((1 : ℝ)*pair X 0 2) ≤ ((1 : ℝ)*pair X 0 1) ∧ ((1 : ℝ)*pair X 0 1) ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main1 : (80273/100000 : ℝ)*P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.main 1
    change (80273/100000 : ℝ)*P 1 ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order1 : 0 ≤ ((1 : ℝ)*(X 0 2+X 2 2)) ∧ ((1 : ℝ)*(X 0 2+X 2 2)) ≤ ((-1 : ℝ)*(X 0 0+X 2 0)) ∧ ((-1 : ℝ)*(X 0 0+X 2 0)) ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.ordered 1
    change 0 ≤ ((1 : ℝ)*pair X 1 2) ∧ ((1 : ℝ)*pair X 1 2) ≤ ((-1 : ℝ)*pair X 1 0) ∧ ((-1 : ℝ)*pair X 1 0) ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main2 : (80273/100000 : ℝ)*P 2 ≤ ((-1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.main 2
    change (80273/100000 : ℝ)*P 2 ≤ ((-1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order2 : 0 ≤ ((1 : ℝ)*(X 0 1+X 1 1)) ∧ ((1 : ℝ)*(X 0 1+X 1 1)) ≤ ((1 : ℝ)*(X 0 0+X 1 0)) ∧ ((1 : ℝ)*(X 0 0+X 1 0)) ≤ ((-1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.ordered 2
    change 0 ≤ ((1 : ℝ)*pair X 2 1) ∧ ((1 : ℝ)*pair X 2 1) ≤ ((1 : ℝ)*pair X 2 0) ∧ ((1 : ℝ)*pair X 2 0) ≤ ((-1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have base11 : ((1 : ℝ)*X 0 1+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    linarith only [(f.coord 0 1).2]
  have base25 : ((1 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    linarith only [(f.coord 2 2).2]
  have base39 : ((-1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.1]
  have base40 : ((-1 : ℝ)*X 1 1+(1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 1+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.2.1]
  have base49 : ((-1 : ℝ)*X 0 2+(-1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order1.1]
  have base50 : ((1 : ℝ)*X 0 0+(1 : ℝ)*X 0 2+(1 : ℝ)*X 2 0+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order1.2.1]
  have base60 : ((-1 : ℝ)*X 0 0+(1 : ℝ)*X 0 1+(-1 : ℝ)*X 1 0+(1 : ℝ)*X 1 1) ≤ (0 : ℝ) := by
    linarith only [order2.2.1]
  have base62 : ((-1 : ℝ)*X 0 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 0 0).1]
  have base63 : ((1 : ℝ)*X 0 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 0 0).2]
  have base64 : ((-1 : ℝ)*X 0 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 0 1).1]
  have base65 : ((1 : ℝ)*X 0 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 0 1).2]
  have base66 : ((-1 : ℝ)*X 0 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 0 2).1]
  have base67 : ((1 : ℝ)*X 0 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 0 2).2]
  have base68 : ((-1 : ℝ)*X 1 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 1 0).1]
  have base69 : ((1 : ℝ)*X 1 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 1 0).2]
  have base70 : ((-1 : ℝ)*X 1 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 1 1).1]
  have base71 : ((1 : ℝ)*X 1 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 1 1).2]
  have base72 : ((-1 : ℝ)*X 1 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 1 2).1]
  have base73 : ((1 : ℝ)*X 1 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 1 2).2]
  have base74 : ((-1 : ℝ)*X 2 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 2 0).1]
  have base75 : ((1 : ℝ)*X 2 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 2 0).2]
  have base76 : ((-1 : ℝ)*X 2 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 2 1).1]
  have base77 : ((1 : ℝ)*X 2 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 2 1).2]
  have base78 : ((-1 : ℝ)*X 2 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 2 2).1]
  have base79 : ((1 : ℝ)*X 2 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 2 2).2]
  have base80 : ((-1 : ℝ)*N 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.1 0).1]
  have base81 : ((1 : ℝ)*N 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.1 0).2]
  have base82 : ((-1 : ℝ)*N 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.1 1).1]
  have base83 : ((1 : ℝ)*N 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.1 1).2]
  have base84 : ((-1 : ℝ)*N 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.1 2).1]
  have base85 : ((1 : ℝ)*N 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.1 2).2]
  have base86 : ((-1 : ℝ)*P 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.2.1 0).1]
  have base87 : ((1 : ℝ)*P 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.2.1 0).2]
  have base88 : ((-1 : ℝ)*P 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.2.1 1).1]
  have base89 : ((1 : ℝ)*P 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.2.1 1).2]
  have base90 : ((-1 : ℝ)*P 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.2.1 2).1]
  have base91 : ((1 : ℝ)*P 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.2.1 2).2]
  have base92 : ((-1 : ℝ)*T) ≤ (3 : ℝ) := by
    linarith only [bounds.2.2.2.1]
  have base93 : ((1 : ℝ)*T) ≤ (3 : ℝ) := by
    linarith only [bounds.2.2.2.2]
  have s0_pow0 : (1 : ℝ) ^ (5 : ℝ) ≤ (1 : ℝ) := by
    have hpowers : (1 : ℝ)^5 ≤ (1 : ℝ)^1 := by
      have hnat : (1 : ℕ)^5*1^1 ≤ 1^1*1^5 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 5 1 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) (by norm_num) 5 1 (by norm_num) hpowers
    simpa only [Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,div_one] using h
  have s0_corner0a : (2 : ℝ) ≤ (11486983549970351/10000000000000000 : ℝ) ^ (5 : ℝ) := by
    have hpowers : (2 : ℝ)^1 ≤ (11486983549970351/10000000000000000 : ℝ)^5 := by
      have hnat : (2 : ℕ)^1*10000000000000000^5 ≤ 11486983549970351^5*1^1 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 1 11486983549970351 10000000000000000 1 5 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (11486983549970351/10000000000000000 : ℝ)) (X := (2 : ℝ)) (by norm_num) 5 1 (by norm_num) hpowers
    simpa only [Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,div_one] using h
  have s0_corner0b : (3 : ℝ) ≤ (6228654698077587/5000000000000000 : ℝ) ^ (5 : ℝ) := by
    have hpowers : (3 : ℝ)^1 ≤ (6228654698077587/5000000000000000 : ℝ)^5 := by
      have hnat : (3 : ℕ)^1*5000000000000000^5 ≤ 6228654698077587^5*1^1 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3 1 6228654698077587 5000000000000000 1 5 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (6228654698077587/5000000000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 5 1 (by norm_num) hpowers
    simpa only [Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,div_one] using h
  have major_s0_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(1486983549970351/10000000000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(970325846184823/10000000000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (5 : ℝ)) (rho := (1 : ℝ)) (alpha := (1486983549970351/10000000000000000 : ℝ)) (beta := (970325846184823/10000000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow0,s0_corner0a]) (by linarith only [s0_pow0,s0_corner0b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![false, true, true], ![true, true, false]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (1 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order0.2.2])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(1486983549970351/10000000000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(970325846184823/10000000000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s0_pow1 : (1 : ℝ) ^ (5 : ℝ) ≤ (1 : ℝ) := by
    have hpowers : (1 : ℝ)^5 ≤ (1 : ℝ)^1 := by
      have hnat : (1 : ℕ)^5*1^1 ≤ 1^1*1^5 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 5 1 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) (by norm_num) 5 1 (by norm_num) hpowers
    simpa only [Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,div_one] using h
  have s0_corner1a : (2 : ℝ) ≤ (11486983549970351/10000000000000000 : ℝ) ^ (5 : ℝ) := by
    have hpowers : (2 : ℝ)^1 ≤ (11486983549970351/10000000000000000 : ℝ)^5 := by
      have hnat : (2 : ℕ)^1*10000000000000000^5 ≤ 11486983549970351^5*1^1 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 1 11486983549970351 10000000000000000 1 5 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (11486983549970351/10000000000000000 : ℝ)) (X := (2 : ℝ)) (by norm_num) 5 1 (by norm_num) hpowers
    simpa only [Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,div_one] using h
  have s0_corner1b : (3 : ℝ) ≤ (6228654698077587/5000000000000000 : ℝ) ^ (5 : ℝ) := by
    have hpowers : (3 : ℝ)^1 ≤ (6228654698077587/5000000000000000 : ℝ)^5 := by
      have hnat : (3 : ℕ)^1*5000000000000000^5 ≤ 6228654698077587^5*1^1 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3 1 6228654698077587 5000000000000000 1 5 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (6228654698077587/5000000000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 5 1 (by norm_num) hpowers
    simpa only [Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,div_one] using h
  have major_s0_1 : P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1))+(1486983549970351/10000000000000000 : ℝ)*((-1 : ℝ)*(X 0 0+X 2 0))+(970325846184823/10000000000000000 : ℝ)*((1 : ℝ)*(X 0 2+X 2 2)) := by
    have hh := chart_majorant (a := (5 : ℝ)) (rho := (1 : ℝ)) (alpha := (1486983549970351/10000000000000000 : ℝ)) (beta := (970325846184823/10000000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow1,s0_corner1a]) (by linarith only [s0_pow1,s0_corner1b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![false, true, true], ![true, true, false]] hX 1 (by
        change ((-1 : ℝ)*pair X 1 0) ≤ (1 : ℝ)*((1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order1.2.2])
    change lpNorm p (pair X 1) ≤ ((1 : ℝ)*pair X 1 1)+(1486983549970351/10000000000000000 : ℝ)*((-1 : ℝ)*pair X 1 0)+(970325846184823/10000000000000000 : ℝ)*((1 : ℝ)*pair X 1 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s0_pow2 : (1 : ℝ) ^ (5 : ℝ) ≤ (1 : ℝ) := by
    have hpowers : (1 : ℝ)^5 ≤ (1 : ℝ)^1 := by
      have hnat : (1 : ℕ)^5*1^1 ≤ 1^1*1^5 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 5 1 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) (by norm_num) 5 1 (by norm_num) hpowers
    simpa only [Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,div_one] using h
  have s0_corner2a : (2 : ℝ) ≤ (11486983549970351/10000000000000000 : ℝ) ^ (5 : ℝ) := by
    have hpowers : (2 : ℝ)^1 ≤ (11486983549970351/10000000000000000 : ℝ)^5 := by
      have hnat : (2 : ℕ)^1*10000000000000000^5 ≤ 11486983549970351^5*1^1 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 1 11486983549970351 10000000000000000 1 5 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (11486983549970351/10000000000000000 : ℝ)) (X := (2 : ℝ)) (by norm_num) 5 1 (by norm_num) hpowers
    simpa only [Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,div_one] using h
  have s0_corner2b : (3 : ℝ) ≤ (6228654698077587/5000000000000000 : ℝ) ^ (5 : ℝ) := by
    have hpowers : (3 : ℝ)^1 ≤ (6228654698077587/5000000000000000 : ℝ)^5 := by
      have hnat : (3 : ℕ)^1*5000000000000000^5 ≤ 6228654698077587^5*1^1 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3 1 6228654698077587 5000000000000000 1 5 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (6228654698077587/5000000000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 5 1 (by norm_num) hpowers
    simpa only [Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,div_one] using h
  have major_s0_2 : P 2 ≤ ((-1 : ℝ)*(X 0 2+X 1 2))+(1486983549970351/10000000000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 1 0))+(970325846184823/10000000000000000 : ℝ)*((1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (5 : ℝ)) (rho := (1 : ℝ)) (alpha := (1486983549970351/10000000000000000 : ℝ)) (beta := (970325846184823/10000000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow2,s0_corner2a]) (by linarith only [s0_pow2,s0_corner2b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![false, true, true], ![true, true, false]] hX 2 (by
        change ((1 : ℝ)*pair X 2 0) ≤ (1 : ℝ)*((-1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order2.2.2])
    change lpNorm p (pair X 2) ≤ ((-1 : ℝ)*pair X 2 2)+(1486983549970351/10000000000000000 : ℝ)*((1 : ℝ)*pair X 2 0)+(970325846184823/10000000000000000 : ℝ)*((1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s0_1 : ((3449378657/5000000000 : ℝ)*X 1 0+(-1067260717/10000000000 : ℝ)*X 1 1+(-9675377/25000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c320030_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_2 : ((1275961037/5000000000 : ℝ)*X 2 0+(5457140469/10000000000 : ℝ)*X 2 1+(132861749/312500000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c320030_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_6 : ((3579157937/10000000000 : ℝ)*X 0 0+(6494668023/10000000000 : ℝ)*X 0 1+(-2007880597/10000000000 : ℝ)*X 0 2+(3579157937/10000000000 : ℝ)*X 1 0+(6494668023/10000000000 : ℝ)*X 1 1+(-2007880597/10000000000 : ℝ)*X 1 2+(3579157937/10000000000 : ℝ)*X 2 0+(6494668023/10000000000 : ℝ)*X 2 1+(-2007880597/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c320030_s0_6 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_7 : ((-351528273/1250000000 : ℝ)*X 0 0+(4139011869/10000000000 : ℝ)*X 0 1+(-267167627/500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c320030_s0_7 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_8 : ((3590438303/5000000000 : ℝ)*X 1 0+(-591627477/10000000000 : ℝ)*X 1 1+(-3870579547/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c320030_s0_8 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_9 : ((201206623/1000000000 : ℝ)*X 2 0+(6277862783/10000000000 : ℝ)*X 2 1+(3823013691/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c320030_s0_9 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_12 : ((3033400649/10000000000 : ℝ)*X 0 0+(7222179977/10000000000 : ℝ)*X 0 1+(-65401589/400000000 : ℝ)*X 0 2+(3033400649/10000000000 : ℝ)*X 1 0+(7222179977/10000000000 : ℝ)*X 1 1+(-65401589/400000000 : ℝ)*X 1 2+(3033400649/10000000000 : ℝ)*X 2 0+(7222179977/10000000000 : ℝ)*X 2 1+(-65401589/400000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c320030_s0_12 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_13 : ((-3035995819/10000000000 : ℝ)*X 0 0+(4663598961/10000000000 : ℝ)*X 0 1+(-579736243/1250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c320030_s0_13 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_14 : ((3492686749/5000000000 : ℝ)*X 1 0+(-272683759/2500000000 : ℝ)*X 1 1+(-3752695313/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c320030_s0_14 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_15 : ((2369699957/10000000000 : ℝ)*X 2 0+(5411876433/10000000000 : ℝ)*X 2 1+(2229004059/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c320030_s0_15 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_17 : ((-683/5000000000 : ℝ)*X 0 0+(1249999997/1250000000 : ℝ)*X 0 1+(-683/5000000000 : ℝ)*X 2 0+(1249999997/1250000000 : ℝ)*X 2 1+(-1 : ℝ)*P 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c320030_s0_17 p hpa hpb (pair X 1)
    change _ ≤ P 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_19 : ((682807859/2000000000 : ℝ)*X 0 0+(3262998069/5000000000 : ℝ)*X 0 1+(-2153833657/10000000000 : ℝ)*X 0 2+(682807859/2000000000 : ℝ)*X 1 0+(3262998069/5000000000 : ℝ)*X 1 1+(-2153833657/10000000000 : ℝ)*X 1 2+(682807859/2000000000 : ℝ)*X 2 0+(3262998069/5000000000 : ℝ)*X 2 1+(-2153833657/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c320030_s0_19 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_20 : ((-2327493651/10000000000 : ℝ)*X 0 0+(642822469/1250000000 : ℝ)*X 0 1+(-38176309/80000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c320030_s0_20 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_21 : ((1917579719/2500000000 : ℝ)*X 1 0+(-659277039/10000000000 : ℝ)*X 1 1+(-3240962941/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c320030_s0_21 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_22 : ((1100799517/5000000000 : ℝ)*X 2 0+(5494696403/10000000000 : ℝ)*X 2 1+(225695903/500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c320030_s0_22 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_25 : ((61592827/156250000 : ℝ)*X 0 0+(6428773943/10000000000 : ℝ)*X 0 1+(-66624007/400000000 : ℝ)*X 0 2+(61592827/156250000 : ℝ)*X 1 0+(6428773943/10000000000 : ℝ)*X 1 1+(-66624007/400000000 : ℝ)*X 1 2+(61592827/156250000 : ℝ)*X 2 0+(6428773943/10000000000 : ℝ)*X 2 1+(-66624007/400000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c320030_s0_25 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have ratio_s0_0 : (0 : ℝ) ≤ ((24463/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(24463/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (41100955819654912542549/5000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1577454169071/1000000000000 : ℝ)*(base39) + (771854960517/1000000000000 : ℝ)*(base50) + (667951032193/1000000000000 : ℝ)*(base60) + (6362222742491/1000000000000 : ℝ)*(major_s0_0) + (8202324566457/500000000000 : ℝ)*(major_s0_1) + (6362222742491/1000000000000 : ℝ)*(major_s0_2) + (116798729/1000000000000 : ℝ)*(sp_s0_1) + (4667603770663/500000000000 : ℝ)*(sp_s0_7) + (933511715517/100000000000 : ℝ)*(sp_s0_8) + (2333793979153/250000000000 : ℝ)*(sp_s0_9) + (1694604395507/500000000000 : ℝ)*(sp_s0_12) + (10042426390423/1000000000000 : ℝ)*(sp_s0_17) + (6603143/250000000000 : ℝ)*(sp_s0_20) + (58037287/1000000000000 : ℝ)*(sp_s0_22) + (1694604395507/500000000000 : ℝ)*(f.failure) + (4667616976949/500000000000 : ℝ)*(f.sum) + (6178431512348473/10000000000000000000000000000 : ℝ)*base62 + (3862419357414093/10000000000000000000000000000 : ℝ)*base65 + (3890172686717889/5000000000000000000000000000 : ℝ)*base66 + (2483094054115659/10000000000000000000000000000 : ℝ)*base68 + (256097307850783/5000000000000000000000000000 : ℝ)*base70 + (4676511338585907/10000000000000000000000000000 : ℝ)*base72 + (860083172116407/5000000000000000000000000000 : ℝ)*base74 + (2590505425115659/10000000000000000000000000000 : ℝ)*base76 + (1635045740804337/2000000000000000000000000000 : ℝ)*base78 + (1/1000000000000 : ℝ)*base83 + (1/1000000000000 : ℝ)*base85 + (601/1250000000000000 : ℝ)*base87 + (601/1250000000000000 : ℝ)*base89 + (601/1250000000000000 : ℝ)*base91 + hcertificate_margin
  have ratio_s0_1 : (0 : ℝ) ≤ ((1 : ℝ)*X 0 0+(271/12500 : ℝ)*X 0 1+(1 : ℝ)*X 2 0+(271/12500 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (6387650219273858817927/625000000000000000000000000 : ℝ) := by norm_num
    linear_combination (369262229043/500000000000 : ℝ)*(base39) + (970681/1000000000000 : ℝ)*(base40) + (10463566173/31250000000 : ℝ)*(base49) + (180678380909/1000000000000 : ℝ)*(base60) + (3108275787499/1000000000000 : ℝ)*(major_s0_0) + (3108275787499/1000000000000 : ℝ)*(major_s0_1) + (3108275787499/1000000000000 : ℝ)*(major_s0_2) + (1074057141/500000000000 : ℝ)*(sp_s0_1) + (68897021/500000000000 : ℝ)*(sp_s0_2) + (1225375479/1000000000000 : ℝ)*(sp_s0_6) + (2280371945963/500000000000 : ℝ)*(sp_s0_13) + (4558595777643/1000000000000 : ℝ)*(sp_s0_14) + (4560606097883/1000000000000 : ℝ)*(sp_s0_15) + (1654578900837/1000000000000 : ℝ)*(sp_s0_19) + (331160855263/200000000000 : ℝ)*(f.failure) + (2280371945963/500000000000 : ℝ)*(f.sum) + (14340041/625000000000000000000 : ℝ)*base63 + (10602209382072323/10000000000000000000000000000 : ℝ)*base64 + (6902199042927677/10000000000000000000000000000 : ℝ)*base67 + (1111507873557851/10000000000000000000000000000 : ℝ)*base68 + (4785043763815087/5000000000000000000000000000 : ℝ)*base70 + (3334019757927677/10000000000000000000000000000 : ℝ)*base73 + (3774163503442149/10000000000000000000000000000 : ℝ)*base74 + (8109379933557851/10000000000000000000000000000 : ℝ)*base76 + (2215432537927677/5000000000000000000000000000 : ℝ)*base79 + (1/1000000000000 : ℝ)*base82 + (1/1000000000000 : ℝ)*base84 + (241/500000000000000 : ℝ)*base86 + (241/500000000000000 : ℝ)*base88 + (241/500000000000000 : ℝ)*base90 + (1/1000000000000 : ℝ)*base93 + hcertificate_margin
  have ratio_s0_2 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(-19601/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(-19601/100000 : ℝ)*X 1 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (3640392088706135243643/312500000000000000000000000 : ℝ) := by norm_num
    linear_combination (1617620623589/1000000000000 : ℝ)*(base39) + (422046406539/1000000000000 : ℝ)*(base50) + (107095070209/20000000000 : ℝ)*(major_s0_0) + (1747212044263/125000000000 : ℝ)*(major_s0_1) + (107095070209/20000000000 : ℝ)*(major_s0_2) + (157035637/500000000000 : ℝ)*(sp_s0_2) + (15852661/1000000000000 : ℝ)*(sp_s0_9) + (12834467/500000000000 : ℝ)*(sp_s0_12) + (10717517/200000000000 : ℝ)*(sp_s0_14) + (4311471421827/500000000000 : ℝ)*(sp_s0_17) + (7856981557557/1000000000000 : ℝ)*(sp_s0_20) + (1964231992493/250000000000 : ℝ)*(sp_s0_21) + (7856651633623/1000000000000 : ℝ)*(sp_s0_22) + (2852495911319/1000000000000 : ℝ)*(sp_s0_25) + (2852521580253/1000000000000 : ℝ)*(f.failure) + (7856981557557/1000000000000 : ℝ)*(f.sum) + (1102279777751277/5000000000000000000000000000 : ℝ)*base62 + (73330694821993/200000000000000000000000000 : ℝ)*base64 + (205383542320449/1250000000000000000000000000 : ℝ)*base67 + (32258106626641/200000000000000000000000000 : ℝ)*base68 + (32287849364317/100000000000000000000000000 : ℝ)*base70 + (5514410121993/200000000000000000000000000 : ℝ)*base72 + (631937664896313/1250000000000000000000000000 : ℝ)*base74 + (187891962166641/200000000000000000000000000 : ℝ)*base76 + (2328064193768029/5000000000000000000000000000 : ℝ)*base78 + (1/1000000000000 : ℝ)*base85 + (2329/2500000000000000 : ℝ)*base87 + (2329/2500000000000000 : ℝ)*base89 + (2329/2500000000000000 : ℝ)*base91 + hcertificate_margin
  have s1_pow0 : (24463/100000 : ℝ) ^ (5 : ℝ) ≤ (87608970427236329/100000000000000000000 : ℝ) := by
    have hpowers : (24463/100000 : ℝ)^5 ≤ (87608970427236329/100000000000000000000 : ℝ)^1 := by
      have hnat : (24463 : ℕ)^5*100000000000000000000^1 ≤ 87608970427236329^1*100000^5 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        24463 100000 87608970427236329 100000000000000000000 5 1 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (24463/100000 : ℝ)) (X := (87608970427236329/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 5 1 (by norm_num) hpowers
    simpa only [Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,div_one] using h
  have s1_corner0a : (100087608970427236329/100000000000000000000 : ℝ) ≤ (10001751565704577/10000000000000000 : ℝ) ^ (5 : ℝ) := by
    have hpowers : (100087608970427236329/100000000000000000000 : ℝ)^1 ≤ (10001751565704577/10000000000000000 : ℝ)^5 := by
      have hnat : (100087608970427236329 : ℕ)^1*10000000000000000^5 ≤ 10001751565704577^5*100000000000000000000^1 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100087608970427236329 100000000000000000000 10001751565704577 10000000000000000 1 5 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001751565704577/10000000000000000 : ℝ)) (X := (100087608970427236329/100000000000000000000 : ℝ)) (by norm_num) 5 1 (by norm_num) hpowers
    simpa only [Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,div_one] using h
  have s1_corner0b : (50087608970427236329/50000000000000000000 : ℝ) ≤ (10003501905289907/10000000000000000 : ℝ) ^ (5 : ℝ) := by
    have hpowers : (50087608970427236329/50000000000000000000 : ℝ)^1 ≤ (10003501905289907/10000000000000000 : ℝ)^5 := by
      have hnat : (50087608970427236329 : ℕ)^1*10000000000000000^5 ≤ 10003501905289907^5*50000000000000000000^1 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50087608970427236329 50000000000000000000 10003501905289907 10000000000000000 1 5 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10003501905289907/10000000000000000 : ℝ)) (X := (50087608970427236329/50000000000000000000 : ℝ)) (by norm_num) 5 1 (by norm_num) hpowers
    simpa only [Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,div_one] using h
  have major_s1_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(1751565704577/2446300000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(175033958533/244630000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (5 : ℝ)) (rho := (24463/100000 : ℝ)) (alpha := (1751565704577/2446300000000000 : ℝ)) (beta := (175033958533/244630000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow0,s1_corner0a]) (by linarith only [s1_pow0,s1_corner0b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![false, true, true], ![true, true, false]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (24463/100000 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_0])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(1751565704577/2446300000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(175033958533/244630000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s1_pow1 : (271/12500 : ℝ) ^ (5 : ℝ) ≤ (7483700789/1562500000000000000 : ℝ) := by
    have hpowers : (271/12500 : ℝ)^5 ≤ (7483700789/1562500000000000000 : ℝ)^1 := by
      have hnat : (271 : ℕ)^5*1562500000000000000^1 ≤ 7483700789^1*12500^5 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        271 12500 7483700789 1562500000000000000 5 1 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (271/12500 : ℝ)) (X := (7483700789/1562500000000000000 : ℝ)) (by norm_num) (by norm_num) 5 1 (by norm_num) hpowers
    simpa only [Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,div_one] using h
  have s1_corner1a : (1562500007483700789/1562500000000000000 : ℝ) ≤ (10000000009579137/10000000000000000 : ℝ) ^ (5 : ℝ) := by
    have hpowers : (1562500007483700789/1562500000000000000 : ℝ)^1 ≤ (10000000009579137/10000000000000000 : ℝ)^5 := by
      have hnat : (1562500007483700789 : ℕ)^1*10000000000000000^5 ≤ 10000000009579137^5*1562500000000000000^1 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1562500007483700789 1562500000000000000 10000000009579137 10000000000000000 1 5 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000000009579137/10000000000000000 : ℝ)) (X := (1562500007483700789/1562500000000000000 : ℝ)) (by norm_num) 5 1 (by norm_num) hpowers
    simpa only [Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,div_one] using h
  have s1_corner1b : (781250007483700789/781250000000000000 : ℝ) ≤ (5000000009579137/5000000000000000 : ℝ) ^ (5 : ℝ) := by
    have hpowers : (781250007483700789/781250000000000000 : ℝ)^1 ≤ (5000000009579137/5000000000000000 : ℝ)^5 := by
      have hnat : (781250007483700789 : ℕ)^1*5000000000000000^5 ≤ 5000000009579137^5*781250000000000000^1 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        781250007483700789 781250000000000000 5000000009579137 5000000000000000 1 5 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000000009579137/5000000000000000 : ℝ)) (X := (781250007483700789/781250000000000000 : ℝ)) (by norm_num) 5 1 (by norm_num) hpowers
    simpa only [Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,div_one] using h
  have major_s1_1 : P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1))+(9579137/216800000000000 : ℝ)*((-1 : ℝ)*(X 0 0+X 2 0))+(9579137/216800000000000 : ℝ)*((1 : ℝ)*(X 0 2+X 2 2)) := by
    have hh := chart_majorant (a := (5 : ℝ)) (rho := (271/12500 : ℝ)) (alpha := (9579137/216800000000000 : ℝ)) (beta := (9579137/216800000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow1,s1_corner1a]) (by linarith only [s1_pow1,s1_corner1b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![false, true, true], ![true, true, false]] hX 1 (by
        change ((-1 : ℝ)*pair X 1 0) ≤ (271/12500 : ℝ)*((1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_1])
    change lpNorm p (pair X 1) ≤ ((1 : ℝ)*pair X 1 1)+(9579137/216800000000000 : ℝ)*((-1 : ℝ)*pair X 1 0)+(9579137/216800000000000 : ℝ)*((1 : ℝ)*pair X 1 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s1_pow2 : (19601/100000 : ℝ) ^ (5 : ℝ) ≤ (28932845195872017/100000000000000000000 : ℝ) := by
    have hpowers : (19601/100000 : ℝ)^5 ≤ (28932845195872017/100000000000000000000 : ℝ)^1 := by
      have hnat : (19601 : ℕ)^5*100000000000000000000^1 ≤ 28932845195872017^1*100000^5 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        19601 100000 28932845195872017 100000000000000000000 5 1 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (19601/100000 : ℝ)) (X := (28932845195872017/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 5 1 (by norm_num) hpowers
    simpa only [Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,div_one] using h
  have s1_corner2a : (100028932845195872017/100000000000000000000 : ℝ) ≤ (10000578589946779/10000000000000000 : ℝ) ^ (5 : ℝ) := by
    have hpowers : (100028932845195872017/100000000000000000000 : ℝ)^1 ≤ (10000578589946779/10000000000000000 : ℝ)^5 := by
      have hnat : (100028932845195872017 : ℕ)^1*10000000000000000^5 ≤ 10000578589946779^5*100000000000000000000^1 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100028932845195872017 100000000000000000000 10000578589946779 10000000000000000 1 5 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000578589946779/10000000000000000 : ℝ)) (X := (100028932845195872017/100000000000000000000 : ℝ)) (by norm_num) 5 1 (by norm_num) hpowers
    simpa only [Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,div_one] using h
  have s1_corner2b : (50028932845195872017/50000000000000000000 : ℝ) ≤ (1250144630753219/1250000000000000 : ℝ) ^ (5 : ℝ) := by
    have hpowers : (50028932845195872017/50000000000000000000 : ℝ)^1 ≤ (1250144630753219/1250000000000000 : ℝ)^5 := by
      have hnat : (50028932845195872017 : ℕ)^1*1250000000000000^5 ≤ 1250144630753219^5*50000000000000000000^1 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50028932845195872017 50000000000000000000 1250144630753219 1250000000000000 1 5 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1250144630753219/1250000000000000 : ℝ)) (X := (50028932845195872017/50000000000000000000 : ℝ)) (by norm_num) 5 1 (by norm_num) hpowers
    simpa only [Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,div_one] using h
  have major_s1_2 : P 2 ≤ ((-1 : ℝ)*(X 0 2+X 1 2))+(578589946779/1960100000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 1 0))+(578456078973/1960100000000000 : ℝ)*((1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (5 : ℝ)) (rho := (19601/100000 : ℝ)) (alpha := (578589946779/1960100000000000 : ℝ)) (beta := (578456078973/1960100000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow2,s1_corner2a]) (by linarith only [s1_pow2,s1_corner2b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![false, true, true], ![true, true, false]] hX 2 (by
        change ((1 : ℝ)*pair X 2 0) ≤ (19601/100000 : ℝ)*((-1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_2])
    change lpNorm p (pair X 2) ≤ ((-1 : ℝ)*pair X 2 2)+(578589946779/1960100000000000 : ℝ)*((1 : ℝ)*pair X 2 0)+(578456078973/1960100000000000 : ℝ)*((1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s1_0 : ((-26399227/78125000 : ℝ)*X 0 0+(4592921989/10000000000 : ℝ)*X 0 1+(-2196604081/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c320030_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_1 : ((1149233603/2000000000 : ℝ)*X 1 0+(-2309537183/10000000000 : ℝ)*X 1 1+(-2076971767/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c320030_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_2 : ((13011379/40000000 : ℝ)*X 2 0+(4869249551/10000000000 : ℝ)*X 2 1+(2114530443/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c320030_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_6 : ((976114027/2500000000 : ℝ)*X 0 0+(1110492179/2000000000 : ℝ)*X 0 1+(-3528197/12500000 : ℝ)*X 0 2+(976114027/2500000000 : ℝ)*X 1 0+(1110492179/2000000000 : ℝ)*X 1 1+(-3528197/12500000 : ℝ)*X 1 2+(976114027/2500000000 : ℝ)*X 2 0+(1110492179/2000000000 : ℝ)*X 2 1+(-3528197/12500000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c320030_s1_6 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have hsep : (-10329/1250 : ℝ) < ((-4693/2500 : ℝ)*P 0+(-4693/2500 : ℝ)*P 1+(-4693/2500 : ℝ)*P 2+(1 : ℝ)*T) := by
    have hcertificate_margin : (-10329/1250 : ℝ) < (-155799193346585006880701616168693/19109455922500000000000000000000 : ℝ) := by norm_num
    linear_combination (4881/1000000000000 : ℝ)*(base11) + (20081/1000000000000 : ℝ)*(base25) + (232349584509/500000000000 : ℝ)*(base39) + (3649/500000000000 : ℝ)*(base40) + (1003758837269/1000000000000 : ℝ)*(base49) + (60274067719/100000000000 : ℝ)*(base50) + (37153204147/500000000000 : ℝ)*(base60) + (43/25000000000 : ℝ)*(ratio_s0_2) + (4693/2500 : ℝ)*(major_s1_0) + (4693/2500 : ℝ)*(major_s1_1) + (4693/2500 : ℝ)*(major_s1_2) + (339707894917/125000000000 : ℝ)*(sp_s1_0) + (2717663164217/1000000000000 : ℝ)*(sp_s1_1) + (339707893017/125000000000 : ℝ)*(sp_s1_2) + (1 : ℝ)*(sp_s1_6) + (2717663164217/1000000000000 : ℝ)*(f.sum) + (12228409721801/829979843750000000000000000 : ℝ)*base62 + (3520158075287/24501250000000000000000000 : ℝ)*base65 + (106085863567/169375000000000000000000 : ℝ)*base67 + (24012951063451/39202000000000000000000000 : ℝ)*base68 + (49671535644971529/282058390000000000000000000000 : ℝ)*base71 + (62581921782257/122315000000000000000000000 : ℝ)*base73 + (366587447/1355000000000000000000 : ℝ)*base75 + (3863904932921/30578750000000000000000000 : ℝ)*base76 + (1647813278819337/4143420625000000000000000000 : ℝ)*base79 + hcertificate_margin
  linarith only [hsep,f.failure]

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
namespace HlawkaSchatten.DiagonalCutoff4
theorem wide_coarse_distinct_p020_b015 (p : ℝ) (hpa : (5 : ℝ) ≤ p) (hpb : p ≤ (41/8 : ℝ))
    (c : Fin 88) (hlo : 30 ≤ c.val) (hhi : c.val < 31)
    (hn63 : c ≠ 63) (hn87 : c ≠ 87)
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (4693/2500 : ℝ) (1059/625 : ℝ) (80273/100000 : ℝ) X (distinctOrders c) (distinctSigns c)) : False := by
  have hc : c=30 := by omega
  rcases hc with rfl
  · exact collision_c320030 p hpa (by linarith only [hpb]) X hX

end HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p : ℝ) (hpa : (5 : ℝ) ≤ p) (hpb : p ≤ (41/8 : ℝ))
    (c : Fin 88) (hlo : 30 ≤ c.val) (hhi : c.val < 31)
    (hn63 : c ≠ 63) (hn87 : c ≠ 87)
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (4693/2500 : ℝ) (1059/625 : ℝ) (80273/100000 : ℝ) X (distinctOrders c) (distinctSigns c)) : False := by
  exact HlawkaSchatten.DiagonalCutoff4.wide_coarse_distinct_p020_b015 p hpa hpb c hlo hhi hn63 hn87 X hX

#print axioms solution
