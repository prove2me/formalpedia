-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.coarse_distinct_p027_b022
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T02:15:05.897839+00:00
-- url     : https://prove2.me/submissions/c92ded93-9046-4c59-9f4c-752d8c9ad146

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
theorem collision_support_c327049_s0_0 (p : ℝ) (hpa : (89/16 : ℝ) ≤ p) (hpb : p ≤ (91/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-126323107/400000000 : ℝ)*x 0 + (1579038341/5000000000 : ℝ)*x 1 + (1140905087/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (126323107/400000000 : ℝ)^91 ≤ (6174090842431/25000000000000 : ℝ)^75 := by
    have hnat : (126323107 : ℕ)^91*25000000000000^75 ≤ 6174090842431^75*400000000^91 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      126323107 400000000 6174090842431 25000000000000 91 75 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1579038341/5000000000 : ℝ)^91 ≤ (123481769739/500000000000 : ℝ)^75 := by
    have hnat : (1579038341 : ℕ)^91*500000000000^75 ≤ 123481769739^75*5000000000^91 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1579038341 5000000000 123481769739 500000000000 91 75 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1140905087/2000000000 : ℝ)^91 ≤ (50607282662093/100000000000000 : ℝ)^75 := by
    have hnat : (1140905087 : ℕ)^91*100000000000000^75 ≤ 50607282662093^75*2000000000^91 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1140905087 2000000000 50607282662093 100000000000000 91 75 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (91/16 : ℝ)) 91 75 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-126323107/400000000 : ℝ), (1579038341/5000000000 : ℝ), (1140905087/2000000000 : ℝ)] ![(6174090842431/25000000000000 : ℝ), (123481769739/500000000000 : ℝ), (50607282662093/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-126323107/400000000 : ℝ)|^91 ≤ (6174090842431/25000000000000 : ℝ)^75
        have hw : |(-126323107/400000000 : ℝ)|=(126323107/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1579038341/5000000000 : ℝ)|^91 ≤ (123481769739/500000000000 : ℝ)^75
        have hw : |(1579038341/5000000000 : ℝ)|=(1579038341/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1140905087/2000000000 : ℝ)|^91 ≤ (50607282662093/100000000000000 : ℝ)^75
        have hw : |(1140905087/2000000000 : ℝ)|=(1140905087/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c327049_s0_1 (p : ℝ) (hpa : (89/16 : ℝ) ≤ p) (hpb : p ≤ (91/16 : ℝ)) (x : Fin 3 → ℝ) :
    (2439273067/10000000000 : ℝ)*x 0 + (-24392723/100000000 : ℝ)*x 1 + (6913024177/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2439273067/10000000000 : ℝ)^91 ≤ (9026359946117/50000000000000 : ℝ)^75 := by
    have hnat : (2439273067 : ℕ)^91*50000000000000^75 ≤ 9026359946117^75*10000000000^91 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2439273067 10000000000 9026359946117 50000000000000 91 75 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (24392723/100000000 : ℝ)^91 ≤ (4513178251199/25000000000000 : ℝ)^75 := by
    have hnat : (24392723 : ℕ)^91*25000000000000^75 ≤ 4513178251199^75*100000000^91 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      24392723 100000000 4513178251199 25000000000000 91 75 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (6913024177/10000000000 : ℝ)^91 ≤ (63894567080179/100000000000000 : ℝ)^75 := by
    have hnat : (6913024177 : ℕ)^91*100000000000000^75 ≤ 63894567080179^75*10000000000^91 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6913024177 10000000000 63894567080179 100000000000000 91 75 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (91/16 : ℝ)) 91 75 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2439273067/10000000000 : ℝ), (-24392723/100000000 : ℝ), (6913024177/10000000000 : ℝ)] ![(9026359946117/50000000000000 : ℝ), (4513178251199/25000000000000 : ℝ), (63894567080179/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2439273067/10000000000 : ℝ)|^91 ≤ (9026359946117/50000000000000 : ℝ)^75
        have hw : |(2439273067/10000000000 : ℝ)|=(2439273067/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-24392723/100000000 : ℝ)|^91 ≤ (4513178251199/25000000000000 : ℝ)^75
        have hw : |(-24392723/100000000 : ℝ)|=(24392723/100000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(6913024177/10000000000 : ℝ)|^91 ≤ (63894567080179/100000000000000 : ℝ)^75
        have hw : |(6913024177/10000000000 : ℝ)|=(6913024177/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c327049_s0_7 (p : ℝ) (hpa : (89/16 : ℝ) ≤ p) (hpb : p ≤ (91/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-1405609959/5000000000 : ℝ)*x 0 + (889172803/5000000000 : ℝ)*x 1 + (7122546727/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1405609959/5000000000 : ℝ)^91 ≤ (10722491749639/50000000000000 : ℝ)^75 := by
    have hnat : (1405609959 : ℕ)^91*50000000000000^75 ≤ 10722491749639^75*5000000000^91 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1405609959 5000000000 10722491749639 50000000000000 91 75 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (889172803/5000000000 : ℝ)^91 ≤ (1537905421689/12500000000000 : ℝ)^75 := by
    have hnat : (889172803 : ℕ)^91*12500000000000^75 ≤ 1537905421689^75*5000000000^91 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      889172803 5000000000 1537905421689 12500000000000 91 75 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (7122546727/10000000000 : ℝ)^91 ≤ (66251773117209/100000000000000 : ℝ)^75 := by
    have hnat : (7122546727 : ℕ)^91*100000000000000^75 ≤ 66251773117209^75*10000000000^91 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7122546727 10000000000 66251773117209 100000000000000 91 75 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (91/16 : ℝ)) 91 75 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1405609959/5000000000 : ℝ), (889172803/5000000000 : ℝ), (7122546727/10000000000 : ℝ)] ![(10722491749639/50000000000000 : ℝ), (1537905421689/12500000000000 : ℝ), (66251773117209/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1405609959/5000000000 : ℝ)|^91 ≤ (10722491749639/50000000000000 : ℝ)^75
        have hw : |(-1405609959/5000000000 : ℝ)|=(1405609959/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(889172803/5000000000 : ℝ)|^91 ≤ (1537905421689/12500000000000 : ℝ)^75
        have hw : |(889172803/5000000000 : ℝ)|=(889172803/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(7122546727/10000000000 : ℝ)|^91 ≤ (66251773117209/100000000000000 : ℝ)^75
        have hw : |(7122546727/10000000000 : ℝ)|=(7122546727/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c327049_s0_8 (p : ℝ) (hpa : (89/16 : ℝ) ≤ p) (hpb : p ≤ (91/16 : ℝ)) (x : Fin 3 → ℝ) :
    (167870311/1000000000 : ℝ)*x 0 + (-1073303717/10000000000 : ℝ)*x 1 + (4239648117/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (167870311/1000000000 : ℝ)^91 ≤ (11471890490569/100000000000000 : ℝ)^75 := by
    have hnat : (167870311 : ℕ)^91*100000000000000^75 ≤ 11471890490569^75*1000000000^91 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      167870311 1000000000 11471890490569 100000000000000 91 75 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1073303717/10000000000 : ℝ)^91 ≤ (666719967343/10000000000000 : ℝ)^75 := by
    have hnat : (1073303717 : ℕ)^91*10000000000000^75 ≤ 666719967343^75*10000000000^91 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1073303717 10000000000 666719967343 10000000000000 91 75 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4239648117/5000000000 : ℝ)^91 ≤ (5116306863661/6250000000000 : ℝ)^75 := by
    have hnat : (4239648117 : ℕ)^91*6250000000000^75 ≤ 5116306863661^75*5000000000^91 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4239648117 5000000000 5116306863661 6250000000000 91 75 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (91/16 : ℝ)) 91 75 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(167870311/1000000000 : ℝ), (-1073303717/10000000000 : ℝ), (4239648117/5000000000 : ℝ)] ![(11471890490569/100000000000000 : ℝ), (666719967343/10000000000000 : ℝ), (5116306863661/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(167870311/1000000000 : ℝ)|^91 ≤ (11471890490569/100000000000000 : ℝ)^75
        have hw : |(167870311/1000000000 : ℝ)|=(167870311/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1073303717/10000000000 : ℝ)|^91 ≤ (666719967343/10000000000000 : ℝ)^75
        have hw : |(-1073303717/10000000000 : ℝ)|=(1073303717/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4239648117/5000000000 : ℝ)|^91 ≤ (5116306863661/6250000000000 : ℝ)^75
        have hw : |(4239648117/5000000000 : ℝ)|=(4239648117/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c327049_s0_9 (p : ℝ) (hpa : (89/16 : ℝ) ≤ p) (hpb : p ≤ (91/16 : ℝ)) (x : Fin 3 → ℝ) :
    (1872878491/5000000000 : ℝ)*x 0 + (922477627/1250000000 : ℝ)*x 1 + (-14689129/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1872878491/5000000000 : ℝ)^91 ≤ (15189076970159/50000000000000 : ℝ)^75 := by
    have hnat : (1872878491 : ℕ)^91*50000000000000^75 ≤ 15189076970159^75*5000000000^91 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1872878491 5000000000 15189076970159 50000000000000 91 75 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (922477627/1250000000 : ℝ)^91 ≤ (69166469093871/100000000000000 : ℝ)^75 := by
    have hnat : (922477627 : ℕ)^91*100000000000000^75 ≤ 69166469093871^75*1250000000^91 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      922477627 1250000000 69166469093871 100000000000000 91 75 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (14689129/1250000000 : ℝ)^91 ≤ (455376958347/100000000000000 : ℝ)^75 := by
    have hnat : (14689129 : ℕ)^91*100000000000000^75 ≤ 455376958347^75*1250000000^91 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      14689129 1250000000 455376958347 100000000000000 91 75 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (91/16 : ℝ)) 91 75 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1872878491/5000000000 : ℝ), (922477627/1250000000 : ℝ), (-14689129/1250000000 : ℝ)] ![(15189076970159/50000000000000 : ℝ), (69166469093871/100000000000000 : ℝ), (455376958347/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1872878491/5000000000 : ℝ)|^91 ≤ (15189076970159/50000000000000 : ℝ)^75
        have hw : |(1872878491/5000000000 : ℝ)|=(1872878491/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(922477627/1250000000 : ℝ)|^91 ≤ (69166469093871/100000000000000 : ℝ)^75
        have hw : |(922477627/1250000000 : ℝ)|=(922477627/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-14689129/1250000000 : ℝ)|^91 ≤ (455376958347/100000000000000 : ℝ)^75
        have hw : |(-14689129/1250000000 : ℝ)|=(14689129/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c327049_s0_12 (p : ℝ) (hpa : (89/16 : ℝ) ≤ p) (hpb : p ≤ (91/16 : ℝ)) (x : Fin 3 → ℝ) :
    (3738630209/10000000000 : ℝ)*x 0 + (7367669933/10000000000 : ℝ)*x 1 + (160285113/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3738630209/10000000000 : ℝ)^91 ≤ (15154019816799/50000000000000 : ℝ)^75 := by
    have hnat : (3738630209 : ℕ)^91*50000000000000^75 ≤ 15154019816799^75*10000000000^91 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3738630209 10000000000 15154019816799 50000000000000 91 75 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (7367669933/10000000000 : ℝ)^91 ≤ (69028313466767/100000000000000 : ℝ)^75 := by
    have hnat : (7367669933 : ℕ)^91*100000000000000^75 ≤ 69028313466767^75*10000000000^91 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7367669933 10000000000 69028313466767 100000000000000 91 75 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (160285113/10000000000 : ℝ)^91 ≤ (165911724117/25000000000000 : ℝ)^75 := by
    have hnat : (160285113 : ℕ)^91*25000000000000^75 ≤ 165911724117^75*10000000000^91 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      160285113 10000000000 165911724117 25000000000000 91 75 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (91/16 : ℝ)) 91 75 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3738630209/10000000000 : ℝ), (7367669933/10000000000 : ℝ), (160285113/10000000000 : ℝ)] ![(15154019816799/50000000000000 : ℝ), (69028313466767/100000000000000 : ℝ), (165911724117/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3738630209/10000000000 : ℝ)|^91 ≤ (15154019816799/50000000000000 : ℝ)^75
        have hw : |(3738630209/10000000000 : ℝ)|=(3738630209/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(7367669933/10000000000 : ℝ)|^91 ≤ (69028313466767/100000000000000 : ℝ)^75
        have hw : |(7367669933/10000000000 : ℝ)|=(7367669933/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(160285113/10000000000 : ℝ)|^91 ≤ (165911724117/25000000000000 : ℝ)^75
        have hw : |(160285113/10000000000 : ℝ)|=(160285113/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c327049_s0_13 (p : ℝ) (hpa : (89/16 : ℝ) ≤ p) (hpb : p ≤ (91/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-71559201/400000000 : ℝ)*x 0 + (175102127/625000000 : ℝ)*x 1 + (3561245319/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (71559201/400000000 : ℝ)^91 ≤ (247851370839/2000000000000 : ℝ)^75 := by
    have hnat : (71559201 : ℕ)^91*2000000000000^75 ≤ 247851370839^75*400000000^91 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      71559201 400000000 247851370839 2000000000000 91 75 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (175102127/625000000 : ℝ)^91 ≤ (5339072838867/25000000000000 : ℝ)^75 := by
    have hnat : (175102127 : ℕ)^91*25000000000000^75 ≤ 5339072838867^75*625000000^91 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      175102127 625000000 5339072838867 25000000000000 91 75 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3561245319/5000000000 : ℝ)^91 ≤ (1656278502349/2500000000000 : ℝ)^75 := by
    have hnat : (3561245319 : ℕ)^91*2500000000000^75 ≤ 1656278502349^75*5000000000^91 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3561245319 5000000000 1656278502349 2500000000000 91 75 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (91/16 : ℝ)) 91 75 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-71559201/400000000 : ℝ), (175102127/625000000 : ℝ), (3561245319/5000000000 : ℝ)] ![(247851370839/2000000000000 : ℝ), (5339072838867/25000000000000 : ℝ), (1656278502349/2500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-71559201/400000000 : ℝ)|^91 ≤ (247851370839/2000000000000 : ℝ)^75
        have hw : |(-71559201/400000000 : ℝ)|=(71559201/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(175102127/625000000 : ℝ)|^91 ≤ (5339072838867/25000000000000 : ℝ)^75
        have hw : |(175102127/625000000 : ℝ)|=(175102127/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3561245319/5000000000 : ℝ)|^91 ≤ (1656278502349/2500000000000 : ℝ)^75
        have hw : |(3561245319/5000000000 : ℝ)|=(3561245319/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c327049_s0_14 (p : ℝ) (hpa : (89/16 : ℝ) ≤ p) (hpb : p ≤ (91/16 : ℝ)) (x : Fin 3 → ℝ) :
    (1063364659/10000000000 : ℝ)*x 0 + (-1688110897/10000000000 : ℝ)*x 1 + (1695804341/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1063364659/10000000000 : ℝ)^91 ≤ (6592362746639/100000000000000 : ℝ)^75 := by
    have hnat : (1063364659 : ℕ)^91*100000000000000^75 ≤ 6592362746639^75*10000000000^91 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1063364659 10000000000 6592362746639 100000000000000 91 75 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1688110897/10000000000 : ℝ)^91 ≤ (5774971588727/50000000000000 : ℝ)^75 := by
    have hnat : (1688110897 : ℕ)^91*50000000000000^75 ≤ 5774971588727^75*10000000000^91 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1688110897 10000000000 5774971588727 50000000000000 91 75 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1695804341/2000000000 : ℝ)^91 ≤ (81857694058669/100000000000000 : ℝ)^75 := by
    have hnat : (1695804341 : ℕ)^91*100000000000000^75 ≤ 81857694058669^75*2000000000^91 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1695804341 2000000000 81857694058669 100000000000000 91 75 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (91/16 : ℝ)) 91 75 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1063364659/10000000000 : ℝ), (-1688110897/10000000000 : ℝ), (1695804341/2000000000 : ℝ)] ![(6592362746639/100000000000000 : ℝ), (5774971588727/50000000000000 : ℝ), (81857694058669/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1063364659/10000000000 : ℝ)|^91 ≤ (6592362746639/100000000000000 : ℝ)^75
        have hw : |(1063364659/10000000000 : ℝ)|=(1063364659/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1688110897/10000000000 : ℝ)|^91 ≤ (5774971588727/50000000000000 : ℝ)^75
        have hw : |(-1688110897/10000000000 : ℝ)|=(1688110897/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1695804341/2000000000 : ℝ)|^91 ≤ (81857694058669/100000000000000 : ℝ)^75
        have hw : |(1695804341/2000000000 : ℝ)|=(1695804341/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c327049_s0_15 (p : ℝ) (hpa : (89/16 : ℝ) ≤ p) (hpb : p ≤ (91/16 : ℝ)) (x : Fin 3 → ℝ) :
    (3690419977/5000000000 : ℝ)*x 0 + (3747003803/10000000000 : ℝ)*x 1 + (-11241523/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3690419977/5000000000 : ℝ)^91 ≤ (17294514110537/25000000000000 : ℝ)^75 := by
    have hnat : (3690419977 : ℕ)^91*25000000000000^75 ≤ 17294514110537^75*5000000000^91 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3690419977 5000000000 17294514110537 25000000000000 91 75 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3747003803/10000000000 : ℝ)^91 ≤ (3798802910869/12500000000000 : ℝ)^75 := by
    have hnat : (3747003803 : ℕ)^91*12500000000000^75 ≤ 3798802910869^75*10000000000^91 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3747003803 10000000000 3798802910869 12500000000000 91 75 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (11241523/1000000000 : ℝ)^91 ≤ (215760127673/50000000000000 : ℝ)^75 := by
    have hnat : (11241523 : ℕ)^91*50000000000000^75 ≤ 215760127673^75*1000000000^91 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      11241523 1000000000 215760127673 50000000000000 91 75 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (91/16 : ℝ)) 91 75 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3690419977/5000000000 : ℝ), (3747003803/10000000000 : ℝ), (-11241523/1000000000 : ℝ)] ![(17294514110537/25000000000000 : ℝ), (3798802910869/12500000000000 : ℝ), (215760127673/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3690419977/5000000000 : ℝ)|^91 ≤ (17294514110537/25000000000000 : ℝ)^75
        have hw : |(3690419977/5000000000 : ℝ)|=(3690419977/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3747003803/10000000000 : ℝ)|^91 ≤ (3798802910869/12500000000000 : ℝ)^75
        have hw : |(3747003803/10000000000 : ℝ)|=(3747003803/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-11241523/1000000000 : ℝ)|^91 ≤ (215760127673/50000000000000 : ℝ)^75
        have hw : |(-11241523/1000000000 : ℝ)|=(11241523/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c327049_s0_18 (p : ℝ) (hpa : (89/16 : ℝ) ≤ p) (hpb : p ≤ (91/16 : ℝ)) (x : Fin 3 → ℝ) :
    (1473063189/2000000000 : ℝ)*x 0 + (3737897623/10000000000 : ℝ)*x 1 + (167016133/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1473063189/2000000000 : ℝ)^91 ≤ (69001554664381/100000000000000 : ℝ)^75 := by
    have hnat : (1473063189 : ℕ)^91*100000000000000^75 ≤ 69001554664381^75*2000000000^91 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1473063189 2000000000 69001554664381 100000000000000 91 75 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3737897623/10000000000 : ℝ)^91 ≤ (30300833953099/100000000000000 : ℝ)^75 := by
    have hnat : (3737897623 : ℕ)^91*100000000000000^75 ≤ 30300833953099^75*10000000000^91 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3737897623 10000000000 30300833953099 100000000000000 91 75 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (167016133/10000000000 : ℝ)^91 ≤ (21800355523/3125000000000 : ℝ)^75 := by
    have hnat : (167016133 : ℕ)^91*3125000000000^75 ≤ 21800355523^75*10000000000^91 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      167016133 10000000000 21800355523 3125000000000 91 75 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (91/16 : ℝ)) 91 75 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1473063189/2000000000 : ℝ), (3737897623/10000000000 : ℝ), (167016133/10000000000 : ℝ)] ![(69001554664381/100000000000000 : ℝ), (30300833953099/100000000000000 : ℝ), (21800355523/3125000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1473063189/2000000000 : ℝ)|^91 ≤ (69001554664381/100000000000000 : ℝ)^75
        have hw : |(1473063189/2000000000 : ℝ)|=(1473063189/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3737897623/10000000000 : ℝ)|^91 ≤ (30300833953099/100000000000000 : ℝ)^75
        have hw : |(3737897623/10000000000 : ℝ)|=(3737897623/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(167016133/10000000000 : ℝ)|^91 ≤ (21800355523/3125000000000 : ℝ)^75
        have hw : |(167016133/10000000000 : ℝ)|=(167016133/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c327049_s0_19 (p : ℝ) (hpa : (89/16 : ℝ) ≤ p) (hpb : p ≤ (91/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-4008568619/10000000000 : ℝ)*x 0 + (1271950827/5000000000 : ℝ)*x 1 + (546307943/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4008568619/10000000000 : ℝ)^91 ≤ (1319330803441/4000000000000 : ℝ)^75 := by
    have hnat : (4008568619 : ℕ)^91*4000000000000^75 ≤ 1319330803441^75*10000000000^91 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4008568619 10000000000 1319330803441 4000000000000 91 75 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1271950827/5000000000 : ℝ)^91 ≤ (1187281596719/6250000000000 : ℝ)^75 := by
    have hnat : (1271950827 : ℕ)^91*6250000000000^75 ≤ 1187281596719^75*5000000000^91 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1271950827 5000000000 1187281596719 6250000000000 91 75 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (546307943/1000000000 : ℝ)^91 ≤ (4802022435671/10000000000000 : ℝ)^75 := by
    have hnat : (546307943 : ℕ)^91*10000000000000^75 ≤ 4802022435671^75*1000000000^91 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      546307943 1000000000 4802022435671 10000000000000 91 75 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (91/16 : ℝ)) 91 75 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-4008568619/10000000000 : ℝ), (1271950827/5000000000 : ℝ), (546307943/1000000000 : ℝ)] ![(1319330803441/4000000000000 : ℝ), (1187281596719/6250000000000 : ℝ), (4802022435671/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-4008568619/10000000000 : ℝ)|^91 ≤ (1319330803441/4000000000000 : ℝ)^75
        have hw : |(-4008568619/10000000000 : ℝ)|=(4008568619/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1271950827/5000000000 : ℝ)|^91 ≤ (1187281596719/6250000000000 : ℝ)^75
        have hw : |(1271950827/5000000000 : ℝ)|=(1271950827/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(546307943/1000000000 : ℝ)|^91 ≤ (4802022435671/10000000000000 : ℝ)^75
        have hw : |(546307943/1000000000 : ℝ)|=(546307943/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c327049_s0_20 (p : ℝ) (hpa : (89/16 : ℝ) ≤ p) (hpb : p ≤ (91/16 : ℝ)) (x : Fin 3 → ℝ) :
    (862018389/5000000000 : ℝ)*x 0 + (-3188703179/10000000000 : ℝ)*x 1 + (3423901769/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (862018389/5000000000 : ℝ)^91 ≤ (11848856825523/100000000000000 : ℝ)^75 := by
    have hnat : (862018389 : ℕ)^91*100000000000000^75 ≤ 11848856825523^75*5000000000^91 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      862018389 5000000000 11848856825523 100000000000000 91 75 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3188703179/10000000000 : ℝ)^91 ≤ (24987248444879/100000000000000 : ℝ)^75 := by
    have hnat : (3188703179 : ℕ)^91*100000000000000^75 ≤ 24987248444879^75*10000000000^91 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3188703179 10000000000 24987248444879 100000000000000 91 75 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3423901769/5000000000 : ℝ)^91 ≤ (3947743420047/6250000000000 : ℝ)^75 := by
    have hnat : (3423901769 : ℕ)^91*6250000000000^75 ≤ 3947743420047^75*5000000000^91 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3423901769 5000000000 3947743420047 6250000000000 91 75 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (91/16 : ℝ)) 91 75 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(862018389/5000000000 : ℝ), (-3188703179/10000000000 : ℝ), (3423901769/5000000000 : ℝ)] ![(11848856825523/100000000000000 : ℝ), (24987248444879/100000000000000 : ℝ), (3947743420047/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(862018389/5000000000 : ℝ)|^91 ≤ (11848856825523/100000000000000 : ℝ)^75
        have hw : |(862018389/5000000000 : ℝ)|=(862018389/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-3188703179/10000000000 : ℝ)|^91 ≤ (24987248444879/100000000000000 : ℝ)^75
        have hw : |(-3188703179/10000000000 : ℝ)|=(3188703179/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3423901769/5000000000 : ℝ)|^91 ≤ (3947743420047/6250000000000 : ℝ)^75
        have hw : |(3423901769/5000000000 : ℝ)|=(3423901769/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c327049_s0_21 (p : ℝ) (hpa : (89/16 : ℝ) ≤ p) (hpb : p ≤ (91/16 : ℝ)) (x : Fin 3 → ℝ) :
    (5629004021/10000000000 : ℝ)*x 0 + (562900409/1000000000 : ℝ)*x 1 + (-21509509/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5629004021/10000000000 : ℝ)^91 ≤ (9959104447529/20000000000000 : ℝ)^75 := by
    have hnat : (5629004021 : ℕ)^91*20000000000000^75 ≤ 9959104447529^75*10000000000^91 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5629004021 10000000000 9959104447529 20000000000000 91 75 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (562900409/1000000000 : ℝ)^91 ≤ (12448880744563/25000000000000 : ℝ)^75 := by
    have hnat : (562900409 : ℕ)^91*25000000000000^75 ≤ 12448880744563^75*1000000000^91 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      562900409 1000000000 12448880744563 25000000000000 91 75 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (21509509/2000000000 : ℝ)^91 ≤ (51119345851/12500000000000 : ℝ)^75 := by
    have hnat : (21509509 : ℕ)^91*12500000000000^75 ≤ 51119345851^75*2000000000^91 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      21509509 2000000000 51119345851 12500000000000 91 75 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (91/16 : ℝ)) 91 75 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5629004021/10000000000 : ℝ), (562900409/1000000000 : ℝ), (-21509509/2000000000 : ℝ)] ![(9959104447529/20000000000000 : ℝ), (12448880744563/25000000000000 : ℝ), (51119345851/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5629004021/10000000000 : ℝ)|^91 ≤ (9959104447529/20000000000000 : ℝ)^75
        have hw : |(5629004021/10000000000 : ℝ)|=(5629004021/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(562900409/1000000000 : ℝ)|^91 ≤ (12448880744563/25000000000000 : ℝ)^75
        have hw : |(562900409/1000000000 : ℝ)|=(562900409/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-21509509/2000000000 : ℝ)|^91 ≤ (51119345851/12500000000000 : ℝ)^75
        have hw : |(-21509509/2000000000 : ℝ)|=(21509509/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c327049_s1_0 (p : ℝ) (hpa : (89/16 : ℝ) ≤ p) (hpb : p ≤ (91/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-221771393/625000000 : ℝ)*x 0 + (1774179883/5000000000 : ℝ)*x 1 + (2499018261/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (221771393/625000000 : ℝ)^91 ≤ (28446638157467/100000000000000 : ℝ)^75 := by
    have hnat : (221771393 : ℕ)^91*100000000000000^75 ≤ 28446638157467^75*625000000^91 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      221771393 625000000 28446638157467 100000000000000 91 75 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1774179883/5000000000 : ℝ)^91 ≤ (28446808168667/100000000000000 : ℝ)^75 := by
    have hnat : (1774179883 : ℕ)^91*100000000000000^75 ≤ 28446808168667^75*5000000000^91 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1774179883 5000000000 28446808168667 100000000000000 91 75 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2499018261/5000000000 : ℝ)^91 ≤ (43106553661817/100000000000000 : ℝ)^75 := by
    have hnat : (2499018261 : ℕ)^91*100000000000000^75 ≤ 43106553661817^75*5000000000^91 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2499018261 5000000000 43106553661817 100000000000000 91 75 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (91/16 : ℝ)) 91 75 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-221771393/625000000 : ℝ), (1774179883/5000000000 : ℝ), (2499018261/5000000000 : ℝ)] ![(28446638157467/100000000000000 : ℝ), (28446808168667/100000000000000 : ℝ), (43106553661817/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-221771393/625000000 : ℝ)|^91 ≤ (28446638157467/100000000000000 : ℝ)^75
        have hw : |(-221771393/625000000 : ℝ)|=(221771393/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1774179883/5000000000 : ℝ)|^91 ≤ (28446808168667/100000000000000 : ℝ)^75
        have hw : |(1774179883/5000000000 : ℝ)|=(1774179883/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2499018261/5000000000 : ℝ)|^91 ≤ (43106553661817/100000000000000 : ℝ)^75
        have hw : |(2499018261/5000000000 : ℝ)|=(2499018261/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c327049_s1_1 (p : ℝ) (hpa : (89/16 : ℝ) ≤ p) (hpb : p ≤ (91/16 : ℝ)) (x : Fin 3 → ℝ) :
    (2955314227/10000000000 : ℝ)*x 0 + (-184708049/625000000 : ℝ)*x 1 + (1514299917/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2955314227/10000000000 : ℝ)^91 ≤ (11392939310783/50000000000000 : ℝ)^75 := by
    have hnat : (2955314227 : ℕ)^91*50000000000000^75 ≤ 11392939310783^75*10000000000^91 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2955314227 10000000000 11392939310783 50000000000000 91 75 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (184708049/625000000 : ℝ)^91 ≤ (22786014801887/100000000000000 : ℝ)^75 := by
    have hnat : (184708049 : ℕ)^91*100000000000000^75 ≤ 22786014801887^75*625000000^91 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      184708049 625000000 22786014801887 100000000000000 91 75 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1514299917/2500000000 : ℝ)^91 ≤ (54428106559499/100000000000000 : ℝ)^75 := by
    have hnat : (1514299917 : ℕ)^91*100000000000000^75 ≤ 54428106559499^75*2500000000^91 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1514299917 2500000000 54428106559499 100000000000000 91 75 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (91/16 : ℝ)) 91 75 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2955314227/10000000000 : ℝ), (-184708049/625000000 : ℝ), (1514299917/2500000000 : ℝ)] ![(11392939310783/50000000000000 : ℝ), (22786014801887/100000000000000 : ℝ), (54428106559499/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2955314227/10000000000 : ℝ)|^91 ≤ (11392939310783/50000000000000 : ℝ)^75
        have hw : |(2955314227/10000000000 : ℝ)|=(2955314227/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-184708049/625000000 : ℝ)|^91 ≤ (22786014801887/100000000000000 : ℝ)^75
        have hw : |(-184708049/625000000 : ℝ)|=(184708049/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1514299917/2500000000 : ℝ)|^91 ≤ (54428106559499/100000000000000 : ℝ)^75
        have hw : |(1514299917/2500000000 : ℝ)|=(1514299917/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c327049_s1_2 (p : ℝ) (hpa : (89/16 : ℝ) ≤ p) (hpb : p ≤ (91/16 : ℝ)) (x : Fin 3 → ℝ) :
    (2587040737/5000000000 : ℝ)*x 0 + (1034811373/2000000000 : ℝ)*x 1 + (-755029113/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2587040737/5000000000 : ℝ)^91 ≤ (44955658056059/100000000000000 : ℝ)^75 := by
    have hnat : (2587040737 : ℕ)^91*100000000000000^75 ≤ 44955658056059^75*5000000000^91 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2587040737 5000000000 44955658056059 100000000000000 91 75 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1034811373/2000000000 : ℝ)^91 ≤ (22477699311603/50000000000000 : ℝ)^75 := by
    have hnat : (1034811373 : ℕ)^91*50000000000000^75 ≤ 22477699311603^75*2000000000^91 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1034811373 2000000000 22477699311603 50000000000000 91 75 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (755029113/5000000000 : ℝ)^91 ≤ (2017788660571/20000000000000 : ℝ)^75 := by
    have hnat : (755029113 : ℕ)^91*20000000000000^75 ≤ 2017788660571^75*5000000000^91 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      755029113 5000000000 2017788660571 20000000000000 91 75 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (91/16 : ℝ)) 91 75 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2587040737/5000000000 : ℝ), (1034811373/2000000000 : ℝ), (-755029113/5000000000 : ℝ)] ![(44955658056059/100000000000000 : ℝ), (22477699311603/50000000000000 : ℝ), (2017788660571/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2587040737/5000000000 : ℝ)|^91 ≤ (44955658056059/100000000000000 : ℝ)^75
        have hw : |(2587040737/5000000000 : ℝ)|=(2587040737/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1034811373/2000000000 : ℝ)|^91 ≤ (22477699311603/50000000000000 : ℝ)^75
        have hw : |(1034811373/2000000000 : ℝ)|=(1034811373/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-755029113/5000000000 : ℝ)|^91 ≤ (2017788660571/20000000000000 : ℝ)^75
        have hw : |(-755029113/5000000000 : ℝ)|=(755029113/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c327049_s1_6 (p : ℝ) (hpa : (89/16 : ℝ) ≤ p) (hpb : p ≤ (91/16 : ℝ)) (x : Fin 3 → ℝ) :
    (4938599/10000000 : ℝ)*x 0 + (4938575511/10000000000 : ℝ)*x 1 + (83891603/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4938599/10000000 : ℝ)^91 ≤ (21242676635419/50000000000000 : ℝ)^75 := by
    have hnat : (4938599 : ℕ)^91*50000000000000^75 ≤ 21242676635419^75*10000000^91 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4938599 10000000 21242676635419 50000000000000 91 75 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4938575511/10000000000 : ℝ)^91 ≤ (42485108093737/100000000000000 : ℝ)^75 := by
    have hnat : (4938575511 : ℕ)^91*100000000000000^75 ≤ 42485108093737^75*10000000000^91 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4938575511 10000000000 42485108093737 100000000000000 91 75 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (83891603/400000000 : ℝ)^91 ≤ (15029538617707/100000000000000 : ℝ)^75 := by
    have hnat : (83891603 : ℕ)^91*100000000000000^75 ≤ 15029538617707^75*400000000^91 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      83891603 400000000 15029538617707 100000000000000 91 75 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (91/16 : ℝ)) 91 75 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4938599/10000000 : ℝ), (4938575511/10000000000 : ℝ), (83891603/400000000 : ℝ)] ![(21242676635419/50000000000000 : ℝ), (42485108093737/100000000000000 : ℝ), (15029538617707/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4938599/10000000 : ℝ)|^91 ≤ (21242676635419/50000000000000 : ℝ)^75
        have hw : |(4938599/10000000 : ℝ)|=(4938599/10000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4938575511/10000000000 : ℝ)|^91 ≤ (42485108093737/100000000000000 : ℝ)^75
        have hw : |(4938575511/10000000000 : ℝ)|=(4938575511/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(83891603/400000000 : ℝ)|^91 ≤ (15029538617707/100000000000000 : ℝ)^75
        have hw : |(83891603/400000000 : ℝ)|=(83891603/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_c327049 (p : ℝ) (hpa : (89/16 : ℝ) ≤ p) (hpb : p ≤ (91/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (211611/100000 : ℝ) (32523/20000 : ℝ) (20519/25000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![false, false, true]]) : False := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : RawLinearData _ _ X N P T := raw_linear_data (by linarith : (1 : ℝ) ≤ p) X hX.raw
  have bounds := raw_linear_data_bounds f (by norm_num)
  have main0 : (20519/25000 : ℝ)*P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.main 0
    change (20519/25000 : ℝ)*P 0 ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order0 : 0 ≤ ((1 : ℝ)*(X 1 2+X 2 2)) ∧ ((1 : ℝ)*(X 1 2+X 2 2)) ≤ ((1 : ℝ)*(X 1 1+X 2 1)) ∧ ((1 : ℝ)*(X 1 1+X 2 1)) ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.ordered 0
    change 0 ≤ ((1 : ℝ)*pair X 0 2) ∧ ((1 : ℝ)*pair X 0 2) ≤ ((1 : ℝ)*pair X 0 1) ∧ ((1 : ℝ)*pair X 0 1) ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main1 : (20519/25000 : ℝ)*P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.main 1
    change (20519/25000 : ℝ)*P 1 ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order1 : 0 ≤ ((-1 : ℝ)*(X 0 2+X 2 2)) ∧ ((-1 : ℝ)*(X 0 2+X 2 2)) ≤ ((1 : ℝ)*(X 0 0+X 2 0)) ∧ ((1 : ℝ)*(X 0 0+X 2 0)) ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.ordered 1
    change 0 ≤ ((-1 : ℝ)*pair X 1 2) ∧ ((-1 : ℝ)*pair X 1 2) ≤ ((1 : ℝ)*pair X 1 0) ∧ ((1 : ℝ)*pair X 1 0) ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main2 : (20519/25000 : ℝ)*P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.main 2
    change (20519/25000 : ℝ)*P 2 ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order2 : 0 ≤ ((-1 : ℝ)*(X 0 1+X 1 1)) ∧ ((-1 : ℝ)*(X 0 1+X 1 1)) ≤ ((-1 : ℝ)*(X 0 0+X 1 0)) ∧ ((-1 : ℝ)*(X 0 0+X 1 0)) ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.ordered 2
    change 0 ≤ ((-1 : ℝ)*pair X 2 1) ∧ ((-1 : ℝ)*pair X 2 1) ≤ ((-1 : ℝ)*pair X 2 0) ∧ ((-1 : ℝ)*pair X 2 0) ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have base5 : ((1 : ℝ)*N 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    linarith only [f.Ntotal 2]
  have base7 : ((1 : ℝ)*T) ≤ (32523/20000 : ℝ) := by
    linarith only [f.Tcap]
  have base8 : ((-1 : ℝ)*X 0 0+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    linarith only [(f.coord 0 0).1]
  have base11 : ((1 : ℝ)*X 0 1+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    linarith only [(f.coord 0 1).2]
  have base16 : ((-1 : ℝ)*X 1 1+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    linarith only [(f.coord 1 1).1]
  have base19 : ((1 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    linarith only [(f.coord 1 2).2]
  have base21 : ((1 : ℝ)*X 2 0+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    linarith only [(f.coord 2 0).2]
  have base39 : ((-1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.1]
  have base40 : ((-1 : ℝ)*X 1 1+(1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 1+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.2.1]
  have base49 : ((1 : ℝ)*X 0 2+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order1.1]
  have base59 : ((1 : ℝ)*X 0 1+(1 : ℝ)*X 1 1) ≤ (0 : ℝ) := by
    linarith only [order2.1]
  have base60 : ((1 : ℝ)*X 0 0+(-1 : ℝ)*X 0 1+(1 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1) ≤ (0 : ℝ) := by
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
  have s0_pow0 : (1 : ℝ) ^ (89/16 : ℝ) ≤ (1 : ℝ) := by
    have hpowers : (1 : ℝ)^89 ≤ (1 : ℝ)^16 := by
      have hnat : (1 : ℕ)^89*1^16 ≤ 1^16*1^89 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 89 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) (by norm_num) 89 16 (by norm_num) hpowers
    exact h
  have s0_corner0a : (2 : ℝ) ≤ (2831768592948963/2500000000000000 : ℝ) ^ (89/16 : ℝ) := by
    have hpowers : (2 : ℝ)^16 ≤ (2831768592948963/2500000000000000 : ℝ)^89 := by
      have hnat : (2 : ℕ)^16*2500000000000000^89 ≤ 2831768592948963^89*1^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 1 2831768592948963 2500000000000000 16 89 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2831768592948963/2500000000000000 : ℝ)) (X := (2 : ℝ)) (by norm_num) 89 16 (by norm_num) hpowers
    exact h
  have s0_corner0b : (3 : ℝ) ≤ (6091785627482579/5000000000000000 : ℝ) ^ (89/16 : ℝ) := by
    have hpowers : (3 : ℝ)^16 ≤ (6091785627482579/5000000000000000 : ℝ)^89 := by
      have hnat : (3 : ℕ)^16*5000000000000000^89 ≤ 6091785627482579^89*1^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3 1 6091785627482579 5000000000000000 16 89 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (6091785627482579/5000000000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 89 16 (by norm_num) hpowers
    exact h
  have major_s0_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(331768592948963/2500000000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(428248441584653/5000000000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (89/16 : ℝ)) (rho := (1 : ℝ)) (alpha := (331768592948963/2500000000000000 : ℝ)) (beta := (428248441584653/5000000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow0,s0_corner0a]) (by linarith only [s0_pow0,s0_corner0b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![false, false, true]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (1 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order0.2.2])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(331768592948963/2500000000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(428248441584653/5000000000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s0_pow1 : (1 : ℝ) ^ (89/16 : ℝ) ≤ (1 : ℝ) := by
    have hpowers : (1 : ℝ)^89 ≤ (1 : ℝ)^16 := by
      have hnat : (1 : ℕ)^89*1^16 ≤ 1^16*1^89 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 89 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) (by norm_num) 89 16 (by norm_num) hpowers
    exact h
  have s0_corner1a : (2 : ℝ) ≤ (2831768592948963/2500000000000000 : ℝ) ^ (89/16 : ℝ) := by
    have hpowers : (2 : ℝ)^16 ≤ (2831768592948963/2500000000000000 : ℝ)^89 := by
      have hnat : (2 : ℕ)^16*2500000000000000^89 ≤ 2831768592948963^89*1^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 1 2831768592948963 2500000000000000 16 89 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2831768592948963/2500000000000000 : ℝ)) (X := (2 : ℝ)) (by norm_num) 89 16 (by norm_num) hpowers
    exact h
  have s0_corner1b : (3 : ℝ) ≤ (6091785627482579/5000000000000000 : ℝ) ^ (89/16 : ℝ) := by
    have hpowers : (3 : ℝ)^16 ≤ (6091785627482579/5000000000000000 : ℝ)^89 := by
      have hnat : (3 : ℕ)^16*5000000000000000^89 ≤ 6091785627482579^89*1^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3 1 6091785627482579 5000000000000000 16 89 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (6091785627482579/5000000000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 89 16 (by norm_num) hpowers
    exact h
  have major_s0_1 : P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1))+(331768592948963/2500000000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 2 0))+(428248441584653/5000000000000000 : ℝ)*((-1 : ℝ)*(X 0 2+X 2 2)) := by
    have hh := chart_majorant (a := (89/16 : ℝ)) (rho := (1 : ℝ)) (alpha := (331768592948963/2500000000000000 : ℝ)) (beta := (428248441584653/5000000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow1,s0_corner1a]) (by linarith only [s0_pow1,s0_corner1b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![false, false, true]] hX 1 (by
        change ((1 : ℝ)*pair X 1 0) ≤ (1 : ℝ)*((1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order1.2.2])
    change lpNorm p (pair X 1) ≤ ((1 : ℝ)*pair X 1 1)+(331768592948963/2500000000000000 : ℝ)*((1 : ℝ)*pair X 1 0)+(428248441584653/5000000000000000 : ℝ)*((-1 : ℝ)*pair X 1 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s0_pow2 : (1 : ℝ) ^ (89/16 : ℝ) ≤ (1 : ℝ) := by
    have hpowers : (1 : ℝ)^89 ≤ (1 : ℝ)^16 := by
      have hnat : (1 : ℕ)^89*1^16 ≤ 1^16*1^89 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 89 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) (by norm_num) 89 16 (by norm_num) hpowers
    exact h
  have s0_corner2a : (2 : ℝ) ≤ (2831768592948963/2500000000000000 : ℝ) ^ (89/16 : ℝ) := by
    have hpowers : (2 : ℝ)^16 ≤ (2831768592948963/2500000000000000 : ℝ)^89 := by
      have hnat : (2 : ℕ)^16*2500000000000000^89 ≤ 2831768592948963^89*1^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 1 2831768592948963 2500000000000000 16 89 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2831768592948963/2500000000000000 : ℝ)) (X := (2 : ℝ)) (by norm_num) 89 16 (by norm_num) hpowers
    exact h
  have s0_corner2b : (3 : ℝ) ≤ (6091785627482579/5000000000000000 : ℝ) ^ (89/16 : ℝ) := by
    have hpowers : (3 : ℝ)^16 ≤ (6091785627482579/5000000000000000 : ℝ)^89 := by
      have hnat : (3 : ℕ)^16*5000000000000000^89 ≤ 6091785627482579^89*1^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3 1 6091785627482579 5000000000000000 16 89 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (6091785627482579/5000000000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 89 16 (by norm_num) hpowers
    exact h
  have major_s0_2 : P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2))+(331768592948963/2500000000000000 : ℝ)*((-1 : ℝ)*(X 0 0+X 1 0))+(428248441584653/5000000000000000 : ℝ)*((-1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (89/16 : ℝ)) (rho := (1 : ℝ)) (alpha := (331768592948963/2500000000000000 : ℝ)) (beta := (428248441584653/5000000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow2,s0_corner2a]) (by linarith only [s0_pow2,s0_corner2b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![false, false, true]] hX 2 (by
        change ((-1 : ℝ)*pair X 2 0) ≤ (1 : ℝ)*((1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order2.2.2])
    change lpNorm p (pair X 2) ≤ ((1 : ℝ)*pair X 2 2)+(331768592948963/2500000000000000 : ℝ)*((-1 : ℝ)*pair X 2 0)+(428248441584653/5000000000000000 : ℝ)*((-1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s0_0 : ((-126323107/400000000 : ℝ)*X 0 0+(1579038341/5000000000 : ℝ)*X 0 1+(1140905087/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c327049_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_1 : ((2439273067/10000000000 : ℝ)*X 1 0+(-24392723/100000000 : ℝ)*X 1 1+(6913024177/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c327049_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_7 : ((-1405609959/5000000000 : ℝ)*X 0 0+(889172803/5000000000 : ℝ)*X 0 1+(7122546727/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c327049_s0_7 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_8 : ((167870311/1000000000 : ℝ)*X 1 0+(-1073303717/10000000000 : ℝ)*X 1 1+(4239648117/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c327049_s0_8 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_9 : ((1872878491/5000000000 : ℝ)*X 2 0+(922477627/1250000000 : ℝ)*X 2 1+(-14689129/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c327049_s0_9 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_12 : ((3738630209/10000000000 : ℝ)*X 0 0+(7367669933/10000000000 : ℝ)*X 0 1+(160285113/10000000000 : ℝ)*X 0 2+(3738630209/10000000000 : ℝ)*X 1 0+(7367669933/10000000000 : ℝ)*X 1 1+(160285113/10000000000 : ℝ)*X 1 2+(3738630209/10000000000 : ℝ)*X 2 0+(7367669933/10000000000 : ℝ)*X 2 1+(160285113/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c327049_s0_12 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_13 : ((-71559201/400000000 : ℝ)*X 0 0+(175102127/625000000 : ℝ)*X 0 1+(3561245319/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c327049_s0_13 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_14 : ((1063364659/10000000000 : ℝ)*X 1 0+(-1688110897/10000000000 : ℝ)*X 1 1+(1695804341/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c327049_s0_14 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_15 : ((3690419977/5000000000 : ℝ)*X 2 0+(3747003803/10000000000 : ℝ)*X 2 1+(-11241523/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c327049_s0_15 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_18 : ((1473063189/2000000000 : ℝ)*X 0 0+(3737897623/10000000000 : ℝ)*X 0 1+(167016133/10000000000 : ℝ)*X 0 2+(1473063189/2000000000 : ℝ)*X 1 0+(3737897623/10000000000 : ℝ)*X 1 1+(167016133/10000000000 : ℝ)*X 1 2+(1473063189/2000000000 : ℝ)*X 2 0+(3737897623/10000000000 : ℝ)*X 2 1+(167016133/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c327049_s0_18 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_19 : ((-4008568619/10000000000 : ℝ)*X 0 0+(1271950827/5000000000 : ℝ)*X 0 1+(546307943/1000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c327049_s0_19 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_20 : ((862018389/5000000000 : ℝ)*X 1 0+(-3188703179/10000000000 : ℝ)*X 1 1+(3423901769/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c327049_s0_20 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_21 : ((5629004021/10000000000 : ℝ)*X 2 0+(562900409/1000000000 : ℝ)*X 2 1+(-21509509/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c327049_s0_21 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have ratio_s0_0 : (0 : ℝ) ≤ ((59223/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(59223/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (57700980516328707/10000000000000000000000 : ℝ) := by norm_num
    linear_combination (40427119517/1000000000000 : ℝ)*(base5) + (963292982243/1000000000000 : ℝ)*(base7) + (3201164851/500000000000 : ℝ)*(base60) + (985707275123/500000000000 : ℝ)*(major_s0_0) + (985707275123/500000000000 : ℝ)*(major_s0_1) + (985707275123/500000000000 : ℝ)*(major_s0_2) + (948649/500000000000 : ℝ)*(sp_s0_0) + (144701/100000000000 : ℝ)*(sp_s0_1) + (77782627073/31250000000 : ℝ)*(sp_s0_7) + (2489023854639/1000000000000 : ℝ)*(sp_s0_8) + (2529479373501/1000000000000 : ℝ)*(sp_s0_9) + (1854487824839/1000000000000 : ℝ)*(sp_s0_12) + (125807/20000000000 : ℝ)*(sp_s0_13) + (5390467/200000000000 : ℝ)*(sp_s0_14) + (931621962113/1000000000000 : ℝ)*(f.failure) + (77782882937/31250000000 : ℝ)*(f.sum) + (2647399997/10000000000000000000000 : ℝ)*base63 + (348244225237319/2500000000000000000000000000 : ℝ)*base64 + (1423179267737319/2500000000000000000000000000 : ℝ)*base66 + (301619373047449/1250000000000000000000000000 : ℝ)*base68 + (813451929357579/2500000000000000000000000000 : ℝ)*base71 + (1585262054012681/2500000000000000000000000000 : ℝ)*base72 + (653742178077551/1250000000000000000000000000 : ℝ)*base74 + (643950611827551/1250000000000000000000000000 : ℝ)*base76 + (4785729/400000000000000000000 : ℝ)*base79 + (94043/100000000000000000 : ℝ)*base87 + (94043/100000000000000000 : ℝ)*base89 + (94043/100000000000000000 : ℝ)*base91 + hcertificate_margin
  have ratio_s0_1 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(59227/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(59227/100000 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (1236051327933948750981/78125000000000000000000000 : ℝ) := by norm_num
    linear_combination (130676010987/1000000000000 : ℝ)*(base5) + (240707083309/250000000000 : ℝ)*(base7) + (146216682349/1000000000000 : ℝ)*(base60) + (61624713659/31250000000 : ℝ)*(major_s0_0) + (61624713659/31250000000 : ℝ)*(major_s0_1) + (61624713659/31250000000 : ℝ)*(major_s0_2) + (3805073/500000000000 : ℝ)*(sp_s0_0) + (682409/100000000000 : ℝ)*(sp_s0_1) + (8071397/250000000000 : ℝ)*(sp_s0_7) + (7312993/200000000000 : ℝ)*(sp_s0_8) + (2490141111353/1000000000000 : ℝ)*(sp_s0_13) + (155633601127/62500000000 : ℝ)*(sp_s0_14) + (1310428509037/500000000000 : ℝ)*(sp_s0_15) + (441011654371/250000000000 : ℝ)*(sp_s0_18) + (465947147617/500000000000 : ℝ)*(f.failure) + (2490181007087/1000000000000 : ℝ)*(f.sum) + (6167226221/10000000000000000000000 : ℝ)*base62 + (62671482874673/156250000000000000000000000 : ℝ)*base65 + (8932907187173/156250000000000000000000000 : ℝ)*base67 + (39305952923117/78125000000000000000000000 : ℝ)*base68 + (5461878974879/19531250000000000000000000 : ℝ)*base71 + (13914964000327/156250000000000000000000000 : ℝ)*base73 + (34112403514383/78125000000000000000000000 : ℝ)*base74 + (173053299297/1220703125000000000000000 : ℝ)*base76 + (312647/625000000000000000000 : ℝ)*base78 + (19013/50000000000000000 : ℝ)*base86 + (19013/50000000000000000 : ℝ)*base88 + (19013/50000000000000000 : ℝ)*base90 + (1/1000000000000 : ℝ)*base93 + hcertificate_margin
  have ratio_s0_2 : (0 : ℝ) ≤ ((1 : ℝ)*X 0 0+(191/2000 : ℝ)*X 0 2+(1 : ℝ)*X 1 0+(191/2000 : ℝ)*X 1 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (7276853175159218925189/2500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (823397998341/1000000000000 : ℝ)*(base5) + (22090417103/500000000000 : ℝ)*(base7) + (2642643/1000000000000 : ℝ)*(base8) + (561497/200000000000 : ℝ)*(base16) + (13649037467/1000000000000 : ℝ)*(base39) + (154168287/3125000000 : ℝ)*(base49) + (218266595121/250000000000 : ℝ)*(base59) + (1648909233197/1000000000000 : ℝ)*(major_s0_0) + (1648909233197/1000000000000 : ℝ)*(major_s0_1) + (1648909233197/1000000000000 : ℝ)*(major_s0_2) + (15751/250000000000 : ℝ)*(sp_s0_15) + (498929893637/200000000000 : ℝ)*(sp_s0_19) + (2494649303343/1000000000000 : ℝ)*(sp_s0_20) + (663610009233/200000000000 : ℝ)*(sp_s0_21) + (155843432827/200000000000 : ℝ)*(f.failure) + (623663027707/250000000000 : ℝ)*(f.sum) + (285977303/2000000000000000000000 : ℝ)*base63 + (818635211674359/5000000000000000000000000000 : ℝ)*base65 + (2883106931674359/5000000000000000000000000000 : ℝ)*base67 + (325211500175289/2500000000000000000000000000 : ℝ)*base69 + (463690477823781/5000000000000000000000000000 : ℝ)*base71 + (445112026325641/5000000000000000000000000000 : ℝ)*base73 + (293071533925289/2500000000000000000000000000 : ℝ)*base74 + (103153479175289/2500000000000000000000000000 : ℝ)*base76 + (958313169/2000000000000000000000 : ℝ)*base79 + (14297/20000000000000000 : ℝ)*base87 + (14297/20000000000000000 : ℝ)*base89 + (14297/20000000000000000 : ℝ)*base91 + hcertificate_margin
  have s1_pow0 : (59223/100000 : ℝ) ^ (89/16 : ℝ) ≤ (5425975993658023607/100000000000000000000 : ℝ) := by
    have hpowers : (59223/100000 : ℝ)^89 ≤ (5425975993658023607/100000000000000000000 : ℝ)^16 := by
      have hnat : (59223 : ℕ)^89*100000000000000000000^16 ≤ 5425975993658023607^16*100000^89 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        59223 100000 5425975993658023607 100000000000000000000 89 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (59223/100000 : ℝ)) (X := (5425975993658023607/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 89 16 (by norm_num) hpowers
    exact h
  have s1_corner0a : (105425975993658023607/100000000000000000000 : ℝ) ≤ (252386095699029/250000000000000 : ℝ) ^ (89/16 : ℝ) := by
    have hpowers : (105425975993658023607/100000000000000000000 : ℝ)^16 ≤ (252386095699029/250000000000000 : ℝ)^89 := by
      have hnat : (105425975993658023607 : ℕ)^16*250000000000000^89 ≤ 252386095699029^89*100000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        105425975993658023607 100000000000000000000 252386095699029 250000000000000 16 89 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (252386095699029/250000000000000 : ℝ)) (X := (105425975993658023607/100000000000000000000 : ℝ)) (by norm_num) 89 16 (by norm_num) hpowers
    exact h
  have s1_corner0b : (55425975993658023607/50000000000000000000 : ℝ) ≤ (10186939981160307/10000000000000000 : ℝ) ^ (89/16 : ℝ) := by
    have hpowers : (55425975993658023607/50000000000000000000 : ℝ)^16 ≤ (10186939981160307/10000000000000000 : ℝ)^89 := by
      have hnat : (55425975993658023607 : ℕ)^16*10000000000000000^89 ≤ 10186939981160307^89*50000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        55425975993658023607 50000000000000000000 10186939981160307 10000000000000000 16 89 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10186939981160307/10000000000000000 : ℝ)) (X := (55425975993658023607/50000000000000000000 : ℝ)) (by norm_num) 89 16 (by norm_num) hpowers
    exact h
  have major_s1_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(2386095699029/148057500000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(30498717733049/1974100000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (89/16 : ℝ)) (rho := (59223/100000 : ℝ)) (alpha := (2386095699029/148057500000000 : ℝ)) (beta := (30498717733049/1974100000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow0,s1_corner0a]) (by linarith only [s1_pow0,s1_corner0b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![false, false, true]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (59223/100000 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_0])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(2386095699029/148057500000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(30498717733049/1974100000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s1_pow1 : (59227/100000 : ℝ) ^ (89/16 : ℝ) ≤ (5428014839527924259/100000000000000000000 : ℝ) := by
    have hpowers : (59227/100000 : ℝ)^89 ≤ (5428014839527924259/100000000000000000000 : ℝ)^16 := by
      have hnat : (59227 : ℕ)^89*100000000000000000000^16 ≤ 5428014839527924259^16*100000^89 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        59227 100000 5428014839527924259 100000000000000000000 89 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (59227/100000 : ℝ)) (X := (5428014839527924259/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 89 16 (by norm_num) hpowers
    exact h
  have s1_corner1a : (105428014839527924259/100000000000000000000 : ℝ) ≤ (10095478926473871/10000000000000000 : ℝ) ^ (89/16 : ℝ) := by
    have hpowers : (105428014839527924259/100000000000000000000 : ℝ)^16 ≤ (10095478926473871/10000000000000000 : ℝ)^89 := by
      have hnat : (105428014839527924259 : ℕ)^16*10000000000000000^89 ≤ 10095478926473871^89*100000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        105428014839527924259 100000000000000000000 10095478926473871 10000000000000000 16 89 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10095478926473871/10000000000000000 : ℝ)) (X := (105428014839527924259/100000000000000000000 : ℝ)) (by norm_num) 89 16 (by norm_num) hpowers
    exact h
  have s1_corner1b : (55428014839527924259/50000000000000000000 : ℝ) ≤ (10187007346765887/10000000000000000 : ℝ) ^ (89/16 : ℝ) := by
    have hpowers : (55428014839527924259/50000000000000000000 : ℝ)^16 ≤ (10187007346765887/10000000000000000 : ℝ)^89 := by
      have hnat : (55428014839527924259 : ℕ)^16*10000000000000000^89 ≤ 10187007346765887^89*50000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        55428014839527924259 50000000000000000000 10187007346765887 10000000000000000 16 89 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10187007346765887/10000000000000000 : ℝ)) (X := (55428014839527924259/50000000000000000000 : ℝ)) (by norm_num) 89 16 (by norm_num) hpowers
    exact h
  have major_s1_1 : P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1))+(95478926473871/5922700000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 2 0))+(5720526268251/370168750000000 : ℝ)*((-1 : ℝ)*(X 0 2+X 2 2)) := by
    have hh := chart_majorant (a := (89/16 : ℝ)) (rho := (59227/100000 : ℝ)) (alpha := (95478926473871/5922700000000000 : ℝ)) (beta := (5720526268251/370168750000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow1,s1_corner1a]) (by linarith only [s1_pow1,s1_corner1b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![false, false, true]] hX 1 (by
        change ((1 : ℝ)*pair X 1 0) ≤ (59227/100000 : ℝ)*((1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_1])
    change lpNorm p (pair X 1) ≤ ((1 : ℝ)*pair X 1 1)+(95478926473871/5922700000000000 : ℝ)*((1 : ℝ)*pair X 1 0)+(5720526268251/370168750000000 : ℝ)*((-1 : ℝ)*pair X 1 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s1_pow2 : (191/2000 : ℝ) ^ (89/16 : ℝ) ≤ (105983622313571/50000000000000000000 : ℝ) := by
    have hpowers : (191/2000 : ℝ)^89 ≤ (105983622313571/50000000000000000000 : ℝ)^16 := by
      have hnat : (191 : ℕ)^89*50000000000000000000^16 ≤ 105983622313571^16*2000^89 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        191 2000 105983622313571 50000000000000000000 89 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (191/2000 : ℝ)) (X := (105983622313571/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 89 16 (by norm_num) hpowers
    exact h
  have s1_corner2a : (50000105983622313571/50000000000000000000 : ℝ) ≤ (5000001905321891/5000000000000000 : ℝ) ^ (89/16 : ℝ) := by
    have hpowers : (50000105983622313571/50000000000000000000 : ℝ)^16 ≤ (5000001905321891/5000000000000000 : ℝ)^89 := by
      have hnat : (50000105983622313571 : ℕ)^16*5000000000000000^89 ≤ 5000001905321891^89*50000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50000105983622313571 50000000000000000000 5000001905321891 5000000000000000 16 89 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000001905321891/5000000000000000 : ℝ)) (X := (50000105983622313571/50000000000000000000 : ℝ)) (by norm_num) 89 16 (by norm_num) hpowers
    exact h
  have s1_corner2b : (25000105983622313571/25000000000000000000 : ℝ) ≤ (10000007621280939/10000000000000000 : ℝ) ^ (89/16 : ℝ) := by
    have hpowers : (25000105983622313571/25000000000000000000 : ℝ)^16 ≤ (10000007621280939/10000000000000000 : ℝ)^89 := by
      have hnat : (25000105983622313571 : ℕ)^16*10000000000000000^89 ≤ 10000007621280939^89*25000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25000105983622313571 25000000000000000000 10000007621280939 10000000000000000 16 89 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000007621280939/10000000000000000 : ℝ)) (X := (25000105983622313571/25000000000000000000 : ℝ)) (by norm_num) 89 16 (by norm_num) hpowers
    exact h
  have major_s1_2 : P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2))+(1905321891/477500000000000 : ℝ)*((-1 : ℝ)*(X 0 0+X 1 0))+(3810637157/955000000000000 : ℝ)*((-1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (89/16 : ℝ)) (rho := (191/2000 : ℝ)) (alpha := (1905321891/477500000000000 : ℝ)) (beta := (3810637157/955000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow2,s1_corner2a]) (by linarith only [s1_pow2,s1_corner2b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![false, false, true]] hX 2 (by
        change ((-1 : ℝ)*pair X 2 0) ≤ (191/2000 : ℝ)*((1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_2])
    change lpNorm p (pair X 2) ≤ ((1 : ℝ)*pair X 2 2)+(1905321891/477500000000000 : ℝ)*((-1 : ℝ)*pair X 2 0)+(3810637157/955000000000000 : ℝ)*((-1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s1_0 : ((-221771393/625000000 : ℝ)*X 0 0+(1774179883/5000000000 : ℝ)*X 0 1+(2499018261/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c327049_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_1 : ((2955314227/10000000000 : ℝ)*X 1 0+(-184708049/625000000 : ℝ)*X 1 1+(1514299917/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c327049_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_2 : ((2587040737/5000000000 : ℝ)*X 2 0+(1034811373/2000000000 : ℝ)*X 2 1+(-755029113/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c327049_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_6 : ((4938599/10000000 : ℝ)*X 0 0+(4938575511/10000000000 : ℝ)*X 0 1+(83891603/400000000 : ℝ)*X 0 2+(4938599/10000000 : ℝ)*X 1 0+(4938575511/10000000000 : ℝ)*X 1 1+(83891603/400000000 : ℝ)*X 1 2+(4938599/10000000 : ℝ)*X 2 0+(4938575511/10000000000 : ℝ)*X 2 1+(83891603/400000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c327049_s1_6 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have hsep : (-484833/50000 : ℝ) < ((-211611/100000 : ℝ)*P 0+(-211611/100000 : ℝ)*P 1+(-211611/100000 : ℝ)*P 2+(1 : ℝ)*T) := by
    have hcertificate_margin : (-484833/50000 : ℝ) < (-473972146268282136157667463/49352500000000000000000000 : ℝ) := by norm_num
    linear_combination (21897/500000000000 : ℝ)*(base8) + (25281/1000000000000 : ℝ)*(base11) + (78541/500000000000 : ℝ)*(base19) + (197/20000000000 : ℝ)*(base21) + (3/10000000000 : ℝ)*(base40) + (273672195237/1000000000000 : ℝ)*(base49) + (232496713071/200000000000 : ℝ)*(base59) + (84520699891/125000000000 : ℝ)*(base60) + (211611/100000 : ℝ)*(major_s1_0) + (211611/100000 : ℝ)*(major_s1_1) + (211611/100000 : ℝ)*(major_s1_2) + (3201270695783/1000000000000 : ℝ)*(sp_s1_0) + (100039706493/31250000000 : ℝ)*(sp_s1_1) + (50019855547/15625000000 : ℝ)*(sp_s1_2) + (1 : ℝ)*(sp_s1_6) + (1600635382429/500000000000 : ℝ)*(f.sum) + (737531332399683/7070223125000000000000000000 : ℝ)*base63 + (696102147299/955000000000000000000000 : ℝ)*base64 + (17279562189599/296135000000000000000000000 : ℝ)*base67 + (1276100251/59687500000000000000000 : ℝ)*base68 + (160775643108997/1178290937500000000000000000 : ℝ)*base71 + (1768274453167/3084531250000000000000000 : ℝ)*base72 + (2758103408981/9254218750000000000000000 : ℝ)*base74 + (59709637029/616906250000000000000000 : ℝ)*base77 + (24796419257852621/182687532343750000000000000000 : ℝ)*base78 + hcertificate_margin
  linarith only [hsep,f.failure]

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
namespace HlawkaSchatten.DiagonalCutoff4
theorem coarse_distinct_p027_b022 (p : ℝ) (hpa : (89/16 : ℝ) ≤ p) (hpb : p ≤ (91/16 : ℝ))
    (c : Fin 88) (hlo : 49 ≤ c.val) (hhi : c.val < 50)
    (hn63 : c ≠ 63) (hn87 : c ≠ 87)
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (211611/100000 : ℝ) (32523/20000 : ℝ) (20519/25000 : ℝ) X (distinctOrders c) (distinctSigns c)) : False := by
  have hc : c=49 := by omega
  rcases hc with rfl
  · exact collision_c327049 p hpa (by linarith only [hpb]) X hX

end HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p : ℝ) (hpa : (89/16 : ℝ) ≤ p) (hpb : p ≤ (91/16 : ℝ))
    (c : Fin 88) (hlo : 49 ≤ c.val) (hhi : c.val < 50)
    (hn63 : c ≠ 63) (hn87 : c ≠ 87)
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (211611/100000 : ℝ) (32523/20000 : ℝ) (20519/25000 : ℝ) X (distinctOrders c) (distinctSigns c)) : False := by
  exact HlawkaSchatten.DiagonalCutoff4.coarse_distinct_p027_b022 p hpa hpb c hlo hhi hn63 hn87 X hX

#print axioms solution
