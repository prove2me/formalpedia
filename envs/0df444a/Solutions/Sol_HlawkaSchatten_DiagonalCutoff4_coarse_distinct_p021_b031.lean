-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.coarse_distinct_p021_b031
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T01:40:10.950646+00:00
-- url     : https://prove2.me/submissions/2031a9e8-21cc-4808-a74b-39ec920851c1

import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_collision_c320053_s0
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_collision_c320053_s1
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_collision_c320053_s2
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_collision_c320053_s3
import Definitions.Def_HlawkaSchatten_DiagonalCutoff4_Localization
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_collision_c321054_s0
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_collision_c321054_s1
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_collision_c321054_s2
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_collision_c321054_s3
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_collision_c321055_s0
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_collision_c321055_s1
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_collision_c321055_s2
import Definitions.Def_HlawkaSchatten_DiagonalCutoff4_FiniteCharts
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
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6 HlawkaSchatten.DiagonalCutoff4
theorem HlawkaSchatten.DiagonalCutoff4.collision_c320053 (p : ℝ) (hpa : (5 : ℝ) ≤ p) (hpb : p ≤ (41/8 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (4693/2500 : ℝ) (1059/625 : ℝ) (80273/100000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![true, false, true]]) : False := by
  have h0 := collision_c320053_s0 p hpa hpb X hX
  have h1 := collision_c320053_s1 p hpa hpb X hX h0
  have h2 := collision_c320053_s2 p hpa hpb X hX h1
  exact collision_c320053_s3 p hpa hpb X hX h2

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6 HlawkaSchatten.DiagonalCutoff4
theorem HlawkaSchatten.DiagonalCutoff4.collision_c321054 (p : ℝ) (hpa : (81/16 : ℝ) ≤ p) (hpb : p ≤ (83/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (11897/6250 : ℝ) (168549/100000 : ℝ) (80491/100000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![true, true, false]]) : False := by
  have h0 := collision_c321054_s0 p hpa hpb X hX
  have h1 := collision_c321054_s1 p hpa hpb X hX h0
  have h2 := collision_c321054_s2 p hpa hpb X hX h1
  exact collision_c321054_s3 p hpa hpb X hX h2

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6 HlawkaSchatten.DiagonalCutoff4
theorem HlawkaSchatten.DiagonalCutoff4.collision_c321055 (p : ℝ) (hpa : (81/16 : ℝ) ≤ p) (hpb : p ≤ (41/8 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (11897/6250 : ℝ) (168549/100000 : ℝ) (80491/100000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![true, true, true]]) : False := by
  have h0 := collision_c321055_s0 p hpa hpb X hX
  have h1 := collision_c321055_s1 p hpa hpb X hX h0
  exact collision_c321055_s2 p hpa hpb X hX h1

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
theorem collision_support_c321052_s0_0 (p : ℝ) (hpa : (81/16 : ℝ) ≤ p) (hpb : p ≤ (83/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-324734873/5000000000 : ℝ)*x 0 + (1683534489/5000000000 : ℝ)*x 1 + (-7554926133/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (324734873/5000000000 : ℝ)^83 ≤ (3380577584451/100000000000000 : ℝ)^67 := by
    have hnat : (324734873 : ℕ)^83*100000000000000^67 ≤ 3380577584451^67*5000000000^83 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      324734873 5000000000 3380577584451 100000000000000 83 67 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1683534489/5000000000 : ℝ)^83 ≤ (811347670517/3125000000000 : ℝ)^67 := by
    have hnat : (1683534489 : ℕ)^83*3125000000000^67 ≤ 811347670517^67*5000000000^83 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1683534489 5000000000 811347670517 3125000000000 83 67 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (7554926133/10000000000 : ℝ)^83 ≤ (35328148473937/50000000000000 : ℝ)^67 := by
    have hnat : (7554926133 : ℕ)^83*50000000000000^67 ≤ 35328148473937^67*10000000000^83 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7554926133 10000000000 35328148473937 50000000000000 83 67 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (83/16 : ℝ)) 83 67 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-324734873/5000000000 : ℝ), (1683534489/5000000000 : ℝ), (-7554926133/10000000000 : ℝ)] ![(3380577584451/100000000000000 : ℝ), (811347670517/3125000000000 : ℝ), (35328148473937/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-324734873/5000000000 : ℝ)|^83 ≤ (3380577584451/100000000000000 : ℝ)^67
        have hw : |(-324734873/5000000000 : ℝ)|=(324734873/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1683534489/5000000000 : ℝ)|^83 ≤ (811347670517/3125000000000 : ℝ)^67
        have hw : |(1683534489/5000000000 : ℝ)|=(1683534489/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-7554926133/10000000000 : ℝ)|^83 ≤ (35328148473937/50000000000000 : ℝ)^67
        have hw : |(-7554926133/10000000000 : ℝ)|=(7554926133/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c321052_s0_1 (p : ℝ) (hpa : (81/16 : ℝ) ≤ p) (hpb : p ≤ (83/16 : ℝ)) (x : Fin 3 → ℝ) :
    (309492867/625000000 : ℝ)*x 0 + (-2234286657/10000000000 : ℝ)*x 1 + (-1002644779/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (309492867/625000000 : ℝ)^83 ≤ (8373557865319/20000000000000 : ℝ)^67 := by
    have hnat : (309492867 : ℕ)^83*20000000000000^67 ≤ 8373557865319^67*625000000^83 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      309492867 625000000 8373557865319 20000000000000 83 67 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2234286657/10000000000 : ℝ)^83 ≤ (781050973343/5000000000000 : ℝ)^67 := by
    have hnat : (2234286657 : ℕ)^83*5000000000000^67 ≤ 781050973343^67*10000000000^83 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2234286657 10000000000 781050973343 5000000000000 83 67 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1002644779/2000000000 : ℝ)^83 ≤ (42511191195861/100000000000000 : ℝ)^67 := by
    have hnat : (1002644779 : ℕ)^83*100000000000000^67 ≤ 42511191195861^67*2000000000^83 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1002644779 2000000000 42511191195861 100000000000000 83 67 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (83/16 : ℝ)) 83 67 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(309492867/625000000 : ℝ), (-2234286657/10000000000 : ℝ), (-1002644779/2000000000 : ℝ)] ![(8373557865319/20000000000000 : ℝ), (781050973343/5000000000000 : ℝ), (42511191195861/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(309492867/625000000 : ℝ)|^83 ≤ (8373557865319/20000000000000 : ℝ)^67
        have hw : |(309492867/625000000 : ℝ)|=(309492867/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2234286657/10000000000 : ℝ)|^83 ≤ (781050973343/5000000000000 : ℝ)^67
        have hw : |(-2234286657/10000000000 : ℝ)|=(2234286657/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1002644779/2000000000 : ℝ)|^83 ≤ (42511191195861/100000000000000 : ℝ)^67
        have hw : |(-1002644779/2000000000 : ℝ)|=(1002644779/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c321052_s0_7 (p : ℝ) (hpa : (81/16 : ℝ) ≤ p) (hpb : p ≤ (83/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-91390013/1000000000 : ℝ)*x 0 + (12996147/125000000 : ℝ)*x 1 + (-9084313309/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (91390013/1000000000 : ℝ)^83 ≤ (645156634053/12500000000000 : ℝ)^67 := by
    have hnat : (91390013 : ℕ)^83*12500000000000^67 ≤ 645156634053^67*1000000000^83 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      91390013 1000000000 645156634053 12500000000000 83 67 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (12996147/125000000 : ℝ)^83 ≤ (3027649214501/50000000000000 : ℝ)^67 := by
    have hnat : (12996147 : ℕ)^83*50000000000000^67 ≤ 3027649214501^67*125000000^83 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      12996147 125000000 3027649214501 50000000000000 83 67 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (9084313309/10000000000 : ℝ)^83 ≤ (44391724241887/50000000000000 : ℝ)^67 := by
    have hnat : (9084313309 : ℕ)^83*50000000000000^67 ≤ 44391724241887^67*10000000000^83 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      9084313309 10000000000 44391724241887 50000000000000 83 67 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (83/16 : ℝ)) 83 67 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-91390013/1000000000 : ℝ), (12996147/125000000 : ℝ), (-9084313309/10000000000 : ℝ)] ![(645156634053/12500000000000 : ℝ), (3027649214501/50000000000000 : ℝ), (44391724241887/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-91390013/1000000000 : ℝ)|^83 ≤ (645156634053/12500000000000 : ℝ)^67
        have hw : |(-91390013/1000000000 : ℝ)|=(91390013/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(12996147/125000000 : ℝ)|^83 ≤ (3027649214501/50000000000000 : ℝ)^67
        have hw : |(12996147/125000000 : ℝ)|=(12996147/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-9084313309/10000000000 : ℝ)|^83 ≤ (44391724241887/50000000000000 : ℝ)^67
        have hw : |(-9084313309/10000000000 : ℝ)|=(9084313309/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c321052_s0_8 (p : ℝ) (hpa : (81/16 : ℝ) ≤ p) (hpb : p ≤ (83/16 : ℝ)) (x : Fin 3 → ℝ) :
    (601136287/2000000000 : ℝ)*x 0 + (-318681511/2500000000 : ℝ)*x 1 + (-7467864131/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (601136287/2000000000 : ℝ)^83 ≤ (2255654650791/10000000000000 : ℝ)^67 := by
    have hnat : (601136287 : ℕ)^83*10000000000000^67 ≤ 2255654650791^67*2000000000^83 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      601136287 2000000000 2255654650791 10000000000000 83 67 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (318681511/2500000000 : ℝ)^83 ≤ (3897221308729/50000000000000 : ℝ)^67 := by
    have hnat : (318681511 : ℕ)^83*50000000000000^67 ≤ 3897221308729^67*2500000000^83 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      318681511 2500000000 3897221308729 50000000000000 83 67 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (7467864131/10000000000 : ℝ)^83 ≤ (34824505428931/50000000000000 : ℝ)^67 := by
    have hnat : (7467864131 : ℕ)^83*50000000000000^67 ≤ 34824505428931^67*10000000000^83 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7467864131 10000000000 34824505428931 50000000000000 83 67 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (83/16 : ℝ)) 83 67 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(601136287/2000000000 : ℝ), (-318681511/2500000000 : ℝ), (-7467864131/10000000000 : ℝ)] ![(2255654650791/10000000000000 : ℝ), (3897221308729/50000000000000 : ℝ), (34824505428931/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(601136287/2000000000 : ℝ)|^83 ≤ (2255654650791/10000000000000 : ℝ)^67
        have hw : |(601136287/2000000000 : ℝ)|=(601136287/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-318681511/2500000000 : ℝ)|^83 ≤ (3897221308729/50000000000000 : ℝ)^67
        have hw : |(-318681511/2500000000 : ℝ)|=(318681511/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-7467864131/10000000000 : ℝ)|^83 ≤ (34824505428931/50000000000000 : ℝ)^67
        have hw : |(-7467864131/10000000000 : ℝ)|=(7467864131/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c321052_s0_9 (p : ℝ) (hpa : (81/16 : ℝ) ≤ p) (hpb : p ≤ (83/16 : ℝ)) (x : Fin 3 → ℝ) :
    (300568171/1000000000 : ℝ)*x 0 + (2019630743/2500000000 : ℝ)*x 1 + (3523593/200000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (300568171/1000000000 : ℝ)^83 ≤ (22556549064527/100000000000000 : ℝ)^67 := by
    have hnat : (300568171 : ℕ)^83*100000000000000^67 ≤ 22556549064527^67*1000000000^83 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      300568171 1000000000 22556549064527 100000000000000 83 67 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2019630743/2500000000 : ℝ)^83 ≤ (76771899144449/100000000000000 : ℝ)^67 := by
    have hnat : (2019630743 : ℕ)^83*100000000000000^67 ≤ 76771899144449^67*2500000000^83 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2019630743 2500000000 76771899144449 100000000000000 83 67 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3523593/200000000 : ℝ)^83 ≤ (335775888299/50000000000000 : ℝ)^67 := by
    have hnat : (3523593 : ℕ)^83*50000000000000^67 ≤ 335775888299^67*200000000^83 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3523593 200000000 335775888299 50000000000000 83 67 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (83/16 : ℝ)) 83 67 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(300568171/1000000000 : ℝ), (2019630743/2500000000 : ℝ), (3523593/200000000 : ℝ)] ![(22556549064527/100000000000000 : ℝ), (76771899144449/100000000000000 : ℝ), (335775888299/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(300568171/1000000000 : ℝ)|^83 ≤ (22556549064527/100000000000000 : ℝ)^67
        have hw : |(300568171/1000000000 : ℝ)|=(300568171/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2019630743/2500000000 : ℝ)|^83 ≤ (76771899144449/100000000000000 : ℝ)^67
        have hw : |(2019630743/2500000000 : ℝ)|=(2019630743/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3523593/200000000 : ℝ)|^83 ≤ (335775888299/50000000000000 : ℝ)^67
        have hw : |(3523593/200000000 : ℝ)|=(3523593/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c321052_s0_13 (p : ℝ) (hpa : (81/16 : ℝ) ≤ p) (hpb : p ≤ (83/16 : ℝ)) (x : Fin 3 → ℝ) :
    (60089361/156250000 : ℝ)*x 0 + (295097683/400000000 : ℝ)*x 1 + (-199606817/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (60089361/156250000 : ℝ)^83 ≤ (6122061933923/20000000000000 : ℝ)^67 := by
    have hnat : (60089361 : ℕ)^83*20000000000000^67 ≤ 6122061933923^67*156250000^83 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      60089361 156250000 6122061933923 20000000000000 83 67 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (295097683/400000000 : ℝ)^83 ≤ (6860581480559/10000000000000 : ℝ)^67 := by
    have hnat : (295097683 : ℕ)^83*10000000000000^67 ≤ 6860581480559^67*400000000^83 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      295097683 400000000 6860581480559 10000000000000 83 67 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (199606817/10000000000 : ℝ)^83 ≤ (783875515287/100000000000000 : ℝ)^67 := by
    have hnat : (199606817 : ℕ)^83*100000000000000^67 ≤ 783875515287^67*10000000000^83 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      199606817 10000000000 783875515287 100000000000000 83 67 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (83/16 : ℝ)) 83 67 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(60089361/156250000 : ℝ), (295097683/400000000 : ℝ), (-199606817/10000000000 : ℝ)] ![(6122061933923/20000000000000 : ℝ), (6860581480559/10000000000000 : ℝ), (783875515287/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(60089361/156250000 : ℝ)|^83 ≤ (6122061933923/20000000000000 : ℝ)^67
        have hw : |(60089361/156250000 : ℝ)|=(60089361/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(295097683/400000000 : ℝ)|^83 ≤ (6860581480559/10000000000000 : ℝ)^67
        have hw : |(295097683/400000000 : ℝ)|=(295097683/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-199606817/10000000000 : ℝ)|^83 ≤ (783875515287/100000000000000 : ℝ)^67
        have hw : |(-199606817/10000000000 : ℝ)|=(199606817/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c321052_s0_14 (p : ℝ) (hpa : (81/16 : ℝ) ≤ p) (hpb : p ≤ (83/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-105486509/10000000000 : ℝ)*x 0 + (1353371673/10000000000 : ℝ)*x 1 + (-2321870413/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (105486509/10000000000 : ℝ)^83 ≤ (355733317537/100000000000000 : ℝ)^67 := by
    have hnat : (105486509 : ℕ)^83*100000000000000^67 ≤ 355733317537^67*10000000000^83 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      105486509 10000000000 355733317537 100000000000000 83 67 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1353371673/10000000000 : ℝ)^83 ≤ (8394489608041/100000000000000 : ℝ)^67 := by
    have hnat : (1353371673 : ℕ)^83*100000000000000^67 ≤ 8394489608041^67*10000000000^83 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1353371673 10000000000 8394489608041 100000000000000 83 67 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2321870413/2500000000 : ℝ)^83 ≤ (11406222133003/12500000000000 : ℝ)^67 := by
    have hnat : (2321870413 : ℕ)^83*12500000000000^67 ≤ 11406222133003^67*2500000000^83 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2321870413 2500000000 11406222133003 12500000000000 83 67 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (83/16 : ℝ)) 83 67 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-105486509/10000000000 : ℝ), (1353371673/10000000000 : ℝ), (-2321870413/2500000000 : ℝ)] ![(355733317537/100000000000000 : ℝ), (8394489608041/100000000000000 : ℝ), (11406222133003/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-105486509/10000000000 : ℝ)|^83 ≤ (355733317537/100000000000000 : ℝ)^67
        have hw : |(-105486509/10000000000 : ℝ)|=(105486509/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1353371673/10000000000 : ℝ)|^83 ≤ (8394489608041/100000000000000 : ℝ)^67
        have hw : |(1353371673/10000000000 : ℝ)|=(1353371673/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2321870413/2500000000 : ℝ)|^83 ≤ (11406222133003/12500000000000 : ℝ)^67
        have hw : |(-2321870413/2500000000 : ℝ)|=(2321870413/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c321052_s0_15 (p : ℝ) (hpa : (81/16 : ℝ) ≤ p) (hpb : p ≤ (83/16 : ℝ)) (x : Fin 3 → ℝ) :
    (113934097/625000000 : ℝ)*x 0 + (-585291427/2500000000 : ℝ)*x 1 + (-7611076027/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (113934097/625000000 : ℝ)^83 ≤ (1517581612649/12500000000000 : ℝ)^67 := by
    have hnat : (113934097 : ℕ)^83*12500000000000^67 ≤ 1517581612649^67*625000000^83 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      113934097 625000000 1517581612649 12500000000000 83 67 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (585291427/2500000000 : ℝ)^83 ≤ (16551935604809/100000000000000 : ℝ)^67 := by
    have hnat : (585291427 : ℕ)^83*100000000000000^67 ≤ 16551935604809^67*2500000000^83 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      585291427 2500000000 16551935604809 100000000000000 83 67 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (7611076027/10000000000 : ℝ)^83 ≤ (71307411484829/100000000000000 : ℝ)^67 := by
    have hnat : (7611076027 : ℕ)^83*100000000000000^67 ≤ 71307411484829^67*10000000000^83 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7611076027 10000000000 71307411484829 100000000000000 83 67 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (83/16 : ℝ)) 83 67 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(113934097/625000000 : ℝ), (-585291427/2500000000 : ℝ), (-7611076027/10000000000 : ℝ)] ![(1517581612649/12500000000000 : ℝ), (16551935604809/100000000000000 : ℝ), (71307411484829/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(113934097/625000000 : ℝ)|^83 ≤ (1517581612649/12500000000000 : ℝ)^67
        have hw : |(113934097/625000000 : ℝ)|=(113934097/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-585291427/2500000000 : ℝ)|^83 ≤ (16551935604809/100000000000000 : ℝ)^67
        have hw : |(-585291427/2500000000 : ℝ)|=(585291427/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-7611076027/10000000000 : ℝ)|^83 ≤ (71307411484829/100000000000000 : ℝ)^67
        have hw : |(-7611076027/10000000000 : ℝ)|=(7611076027/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c321052_s0_16 (p : ℝ) (hpa : (81/16 : ℝ) ≤ p) (hpb : p ≤ (83/16 : ℝ)) (x : Fin 3 → ℝ) :
    (7374044903/10000000000 : ℝ)*x 0 + (757673293/2000000000 : ℝ)*x 1 + (316490773/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (7374044903/10000000000 : ℝ)^83 ≤ (34283340500963/50000000000000 : ℝ)^67 := by
    have hnat : (7374044903 : ℕ)^83*50000000000000^67 ≤ 34283340500963^67*10000000000^83 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7374044903 10000000000 34283340500963 50000000000000 83 67 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (757673293/2000000000 : ℝ)^83 ≤ (30045801969449/100000000000000 : ℝ)^67 := by
    have hnat : (757673293 : ℕ)^83*100000000000000^67 ≤ 30045801969449^67*2000000000^83 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      757673293 2000000000 30045801969449 100000000000000 83 67 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (316490773/10000000000 : ℝ)^83 ≤ (693758510603/50000000000000 : ℝ)^67 := by
    have hnat : (316490773 : ℕ)^83*50000000000000^67 ≤ 693758510603^67*10000000000^83 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      316490773 10000000000 693758510603 50000000000000 83 67 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (83/16 : ℝ)) 83 67 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(7374044903/10000000000 : ℝ), (757673293/2000000000 : ℝ), (316490773/10000000000 : ℝ)] ![(34283340500963/50000000000000 : ℝ), (30045801969449/100000000000000 : ℝ), (693758510603/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(7374044903/10000000000 : ℝ)|^83 ≤ (34283340500963/50000000000000 : ℝ)^67
        have hw : |(7374044903/10000000000 : ℝ)|=(7374044903/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(757673293/2000000000 : ℝ)|^83 ≤ (30045801969449/100000000000000 : ℝ)^67
        have hw : |(757673293/2000000000 : ℝ)|=(757673293/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(316490773/10000000000 : ℝ)|^83 ≤ (693758510603/50000000000000 : ℝ)^67
        have hw : |(316490773/10000000000 : ℝ)|=(316490773/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c321052_s0_20 (p : ℝ) (hpa : (81/16 : ℝ) ≤ p) (hpb : p ≤ (83/16 : ℝ)) (x : Fin 3 → ℝ) :
    (209627379/250000000 : ℝ)*x 0 + (2525644021/10000000000 : ℝ)*x 1 + (-322491339/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (209627379/250000000 : ℝ)^83 ≤ (16079452015967/20000000000000 : ℝ)^67 := by
    have hnat : (209627379 : ℕ)^83*20000000000000^67 ≤ 16079452015967^67*250000000^83 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      209627379 250000000 16079452015967 20000000000000 83 67 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2525644021/10000000000 : ℝ)^83 ≤ (18182560332037/100000000000000 : ℝ)^67 := by
    have hnat : (2525644021 : ℕ)^83*100000000000000^67 ≤ 18182560332037^67*10000000000^83 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2525644021 10000000000 18182560332037 100000000000000 83 67 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (322491339/10000000000 : ℝ)^83 ≤ (1420179576377/100000000000000 : ℝ)^67 := by
    have hnat : (322491339 : ℕ)^83*100000000000000^67 ≤ 1420179576377^67*10000000000^83 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      322491339 10000000000 1420179576377 100000000000000 83 67 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (83/16 : ℝ)) 83 67 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(209627379/250000000 : ℝ), (2525644021/10000000000 : ℝ), (-322491339/10000000000 : ℝ)] ![(16079452015967/20000000000000 : ℝ), (18182560332037/100000000000000 : ℝ), (1420179576377/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(209627379/250000000 : ℝ)|^83 ≤ (16079452015967/20000000000000 : ℝ)^67
        have hw : |(209627379/250000000 : ℝ)|=(209627379/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2525644021/10000000000 : ℝ)|^83 ≤ (18182560332037/100000000000000 : ℝ)^67
        have hw : |(2525644021/10000000000 : ℝ)|=(2525644021/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-322491339/10000000000 : ℝ)|^83 ≤ (1420179576377/100000000000000 : ℝ)^67
        have hw : |(-322491339/10000000000 : ℝ)|=(322491339/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c321052_s0_21 (p : ℝ) (hpa : (81/16 : ℝ) ≤ p) (hpb : p ≤ (83/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-516431/5000000000 : ℝ)*x 0 + (2471986991/5000000000 : ℝ)*x 1 + (-6461343281/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (516431/5000000000 : ℝ)^83 ≤ (1153909647/100000000000000 : ℝ)^67 := by
    have hnat : (516431 : ℕ)^83*100000000000000^67 ≤ 1153909647^67*5000000000^83 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      516431 5000000000 1153909647 100000000000000 83 67 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2471986991/5000000000 : ℝ)^83 ≤ (8356987196613/20000000000000 : ℝ)^67 := by
    have hnat : (2471986991 : ℕ)^83*20000000000000^67 ≤ 8356987196613^67*5000000000^83 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2471986991 5000000000 8356987196613 20000000000000 83 67 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (6461343281/10000000000 : ℝ)^83 ≤ (909592345307/1562500000000 : ℝ)^67 := by
    have hnat : (6461343281 : ℕ)^83*1562500000000^67 ≤ 909592345307^67*10000000000^83 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6461343281 10000000000 909592345307 1562500000000 83 67 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (83/16 : ℝ)) 83 67 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-516431/5000000000 : ℝ), (2471986991/5000000000 : ℝ), (-6461343281/10000000000 : ℝ)] ![(1153909647/100000000000000 : ℝ), (8356987196613/20000000000000 : ℝ), (909592345307/1562500000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-516431/5000000000 : ℝ)|^83 ≤ (1153909647/100000000000000 : ℝ)^67
        have hw : |(-516431/5000000000 : ℝ)|=(516431/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2471986991/5000000000 : ℝ)|^83 ≤ (8356987196613/20000000000000 : ℝ)^67
        have hw : |(2471986991/5000000000 : ℝ)|=(2471986991/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-6461343281/10000000000 : ℝ)|^83 ≤ (909592345307/1562500000000 : ℝ)^67
        have hw : |(-6461343281/10000000000 : ℝ)|=(6461343281/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c321052_s0_22 (p : ℝ) (hpa : (81/16 : ℝ) ≤ p) (hpb : p ≤ (83/16 : ℝ)) (x : Fin 3 → ℝ) :
    (3530983293/5000000000 : ℝ)*x 0 + (-1059513319/5000000000 : ℝ)*x 1 + (-2769383209/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3530983293/5000000000 : ℝ)^83 ≤ (8123781175961/12500000000000 : ℝ)^67 := by
    have hnat : (3530983293 : ℕ)^83*12500000000000^67 ≤ 8123781175961^67*5000000000^83 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3530983293 5000000000 8123781175961 12500000000000 83 67 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1059513319/5000000000 : ℝ)^83 ≤ (2925794134963/20000000000000 : ℝ)^67 := by
    have hnat : (1059513319 : ℕ)^83*20000000000000^67 ≤ 2925794134963^67*5000000000^83 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1059513319 5000000000 2925794134963 20000000000000 83 67 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2769383209/10000000000 : ℝ)^83 ≤ (2547597488831/12500000000000 : ℝ)^67 := by
    have hnat : (2769383209 : ℕ)^83*12500000000000^67 ≤ 2547597488831^67*10000000000^83 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2769383209 10000000000 2547597488831 12500000000000 83 67 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (83/16 : ℝ)) 83 67 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3530983293/5000000000 : ℝ), (-1059513319/5000000000 : ℝ), (-2769383209/10000000000 : ℝ)] ![(8123781175961/12500000000000 : ℝ), (2925794134963/20000000000000 : ℝ), (2547597488831/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3530983293/5000000000 : ℝ)|^83 ≤ (8123781175961/12500000000000 : ℝ)^67
        have hw : |(3530983293/5000000000 : ℝ)|=(3530983293/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1059513319/5000000000 : ℝ)|^83 ≤ (2925794134963/20000000000000 : ℝ)^67
        have hw : |(-1059513319/5000000000 : ℝ)|=(1059513319/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2769383209/10000000000 : ℝ)|^83 ≤ (2547597488831/12500000000000 : ℝ)^67
        have hw : |(-2769383209/10000000000 : ℝ)|=(2769383209/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c321052_s0_23 (p : ℝ) (hpa : (81/16 : ℝ) ≤ p) (hpb : p ≤ (83/16 : ℝ)) (x : Fin 3 → ℝ) :
    (2094570843/10000000000 : ℝ)*x 0 + (804051401/1000000000 : ℝ)*x 1 + (1464323421/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2094570843/10000000000 : ℝ)^83 ≤ (2884021509349/20000000000000 : ℝ)^67 := by
    have hnat : (2094570843 : ℕ)^83*20000000000000^67 ≤ 2884021509349^67*10000000000^83 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2094570843 10000000000 2884021509349 20000000000000 83 67 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (804051401/1000000000 : ℝ)^83 ≤ (76324685259659/100000000000000 : ℝ)^67 := by
    have hnat : (804051401 : ℕ)^83*100000000000000^67 ≤ 76324685259659^67*1000000000^83 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      804051401 1000000000 76324685259659 100000000000000 83 67 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1464323421/10000000000 : ℝ)^83 ≤ (1851041436627/20000000000000 : ℝ)^67 := by
    have hnat : (1464323421 : ℕ)^83*20000000000000^67 ≤ 1851041436627^67*10000000000^83 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1464323421 10000000000 1851041436627 20000000000000 83 67 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (83/16 : ℝ)) 83 67 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2094570843/10000000000 : ℝ), (804051401/1000000000 : ℝ), (1464323421/10000000000 : ℝ)] ![(2884021509349/20000000000000 : ℝ), (76324685259659/100000000000000 : ℝ), (1851041436627/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2094570843/10000000000 : ℝ)|^83 ≤ (2884021509349/20000000000000 : ℝ)^67
        have hw : |(2094570843/10000000000 : ℝ)|=(2094570843/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(804051401/1000000000 : ℝ)|^83 ≤ (76324685259659/100000000000000 : ℝ)^67
        have hw : |(804051401/1000000000 : ℝ)|=(804051401/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1464323421/10000000000 : ℝ)|^83 ≤ (1851041436627/20000000000000 : ℝ)^67
        have hw : |(1464323421/10000000000 : ℝ)|=(1464323421/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c321052_s0_27 (p : ℝ) (hpa : (81/16 : ℝ) ≤ p) (hpb : p ≤ (83/16 : ℝ)) (x : Fin 3 → ℝ) :
    (8938492893/10000000000 : ℝ)*x 0 + (877037087/5000000000 : ℝ)*x 1 + (-159724359/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (8938492893/10000000000 : ℝ)^83 ≤ (21755342832357/25000000000000 : ℝ)^67 := by
    have hnat : (8938492893 : ℕ)^83*25000000000000^67 ≤ 21755342832357^67*10000000000^83 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      8938492893 10000000000 21755342832357 25000000000000 83 67 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (877037087/5000000000 : ℝ)^83 ≤ (5787514564851/50000000000000 : ℝ)^67 := by
    have hnat : (877037087 : ℕ)^83*50000000000000^67 ≤ 5787514564851^67*5000000000^83 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      877037087 5000000000 5787514564851 50000000000000 83 67 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (159724359/5000000000 : ℝ)^83 ≤ (701799766663/50000000000000 : ℝ)^67 := by
    have hnat : (159724359 : ℕ)^83*50000000000000^67 ≤ 701799766663^67*5000000000^83 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      159724359 5000000000 701799766663 50000000000000 83 67 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (83/16 : ℝ)) 83 67 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(8938492893/10000000000 : ℝ), (877037087/5000000000 : ℝ), (-159724359/5000000000 : ℝ)] ![(21755342832357/25000000000000 : ℝ), (5787514564851/50000000000000 : ℝ), (701799766663/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(8938492893/10000000000 : ℝ)|^83 ≤ (21755342832357/25000000000000 : ℝ)^67
        have hw : |(8938492893/10000000000 : ℝ)|=(8938492893/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(877037087/5000000000 : ℝ)|^83 ≤ (5787514564851/50000000000000 : ℝ)^67
        have hw : |(877037087/5000000000 : ℝ)|=(877037087/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-159724359/5000000000 : ℝ)|^83 ≤ (701799766663/50000000000000 : ℝ)^67
        have hw : |(-159724359/5000000000 : ℝ)|=(159724359/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c321052_s1_0 (p : ℝ) (hpa : (81/16 : ℝ) ≤ p) (hpb : p ≤ (83/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-1938493709/10000000000 : ℝ)*x 0 + (1789965397/5000000000 : ℝ)*x 1 + (-6521616919/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1938493709/10000000000 : ℝ)^83 ≤ (3275266539329/25000000000000 : ℝ)^67 := by
    have hnat : (1938493709 : ℕ)^83*25000000000000^67 ≤ 3275266539329^67*10000000000^83 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1938493709 10000000000 3275266539329 25000000000000 83 67 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1789965397/5000000000 : ℝ)^83 ≤ (28011555720091/100000000000000 : ℝ)^67 := by
    have hnat : (1789965397 : ℕ)^83*100000000000000^67 ≤ 28011555720091^67*5000000000^83 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1789965397 5000000000 28011555720091 100000000000000 83 67 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (6521616919/10000000000 : ℝ)^83 ≤ (5888737811359/10000000000000 : ℝ)^67 := by
    have hnat : (6521616919 : ℕ)^83*10000000000000^67 ≤ 5888737811359^67*10000000000^83 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6521616919 10000000000 5888737811359 10000000000000 83 67 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (83/16 : ℝ)) 83 67 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1938493709/10000000000 : ℝ), (1789965397/5000000000 : ℝ), (-6521616919/10000000000 : ℝ)] ![(3275266539329/25000000000000 : ℝ), (28011555720091/100000000000000 : ℝ), (5888737811359/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1938493709/10000000000 : ℝ)|^83 ≤ (3275266539329/25000000000000 : ℝ)^67
        have hw : |(-1938493709/10000000000 : ℝ)|=(1938493709/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1789965397/5000000000 : ℝ)|^83 ≤ (28011555720091/100000000000000 : ℝ)^67
        have hw : |(1789965397/5000000000 : ℝ)|=(1789965397/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-6521616919/10000000000 : ℝ)|^83 ≤ (5888737811359/10000000000000 : ℝ)^67
        have hw : |(-6521616919/10000000000 : ℝ)|=(6521616919/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c321052_s1_1 (p : ℝ) (hpa : (81/16 : ℝ) ≤ p) (hpb : p ≤ (83/16 : ℝ)) (x : Fin 3 → ℝ) :
    (183011299/400000000 : ℝ)*x 0 + (-2947901201/10000000000 : ℝ)*x 1 + (-596833399/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (183011299/400000000 : ℝ)^83 ≤ (148280389133/390625000000 : ℝ)^67 := by
    have hnat : (183011299 : ℕ)^83*390625000000^67 ≤ 148280389133^67*400000000^83 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      183011299 400000000 148280389133 390625000000 83 67 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2947901201/10000000000 : ℝ)^83 ≤ (11010307481411/50000000000000 : ℝ)^67 := by
    have hnat : (2947901201 : ℕ)^83*50000000000000^67 ≤ 11010307481411^67*10000000000^83 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2947901201 10000000000 11010307481411 50000000000000 83 67 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (596833399/1250000000 : ℝ)^83 ≤ (20009802705123/50000000000000 : ℝ)^67 := by
    have hnat : (596833399 : ℕ)^83*50000000000000^67 ≤ 20009802705123^67*1250000000^83 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      596833399 1250000000 20009802705123 50000000000000 83 67 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (83/16 : ℝ)) 83 67 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(183011299/400000000 : ℝ), (-2947901201/10000000000 : ℝ), (-596833399/1250000000 : ℝ)] ![(148280389133/390625000000 : ℝ), (11010307481411/50000000000000 : ℝ), (20009802705123/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(183011299/400000000 : ℝ)|^83 ≤ (148280389133/390625000000 : ℝ)^67
        have hw : |(183011299/400000000 : ℝ)|=(183011299/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2947901201/10000000000 : ℝ)|^83 ≤ (11010307481411/50000000000000 : ℝ)^67
        have hw : |(-2947901201/10000000000 : ℝ)|=(2947901201/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-596833399/1250000000 : ℝ)|^83 ≤ (20009802705123/50000000000000 : ℝ)^67
        have hw : |(-596833399/1250000000 : ℝ)|=(596833399/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c321052_s1_2 (p : ℝ) (hpa : (81/16 : ℝ) ≤ p) (hpb : p ≤ (83/16 : ℝ)) (x : Fin 3 → ℝ) :
    (4715622137/10000000000 : ℝ)*x 0 + (5615763263/10000000000 : ℝ)*x 1 + (882449857/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4715622137/10000000000 : ℝ)^83 ≤ (19703717207091/50000000000000 : ℝ)^67 := by
    have hnat : (4715622137 : ℕ)^83*50000000000000^67 ≤ 19703717207091^67*10000000000^83 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4715622137 10000000000 19703717207091 50000000000000 83 67 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5615763263/10000000000 : ℝ)^83 ≤ (2446448732407/5000000000000 : ℝ)^67 := by
    have hnat : (5615763263 : ℕ)^83*5000000000000^67 ≤ 2446448732407^67*10000000000^83 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5615763263 10000000000 2446448732407 5000000000000 83 67 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (882449857/5000000000 : ℝ)^83 ≤ (182243608221/1562500000000 : ℝ)^67 := by
    have hnat : (882449857 : ℕ)^83*1562500000000^67 ≤ 182243608221^67*5000000000^83 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      882449857 5000000000 182243608221 1562500000000 83 67 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (83/16 : ℝ)) 83 67 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4715622137/10000000000 : ℝ), (5615763263/10000000000 : ℝ), (882449857/5000000000 : ℝ)] ![(19703717207091/50000000000000 : ℝ), (2446448732407/5000000000000 : ℝ), (182243608221/1562500000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4715622137/10000000000 : ℝ)|^83 ≤ (19703717207091/50000000000000 : ℝ)^67
        have hw : |(4715622137/10000000000 : ℝ)|=(4715622137/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5615763263/10000000000 : ℝ)|^83 ≤ (2446448732407/5000000000000 : ℝ)^67
        have hw : |(5615763263/10000000000 : ℝ)|=(5615763263/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(882449857/5000000000 : ℝ)|^83 ≤ (182243608221/1562500000000 : ℝ)^67
        have hw : |(882449857/5000000000 : ℝ)|=(882449857/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c321052_s1_6 (p : ℝ) (hpa : (81/16 : ℝ) ≤ p) (hpb : p ≤ (83/16 : ℝ)) (x : Fin 3 → ℝ) :
    (204685639/312500000 : ℝ)*x 0 + (995956647/2500000000 : ℝ)*x 1 + (-44006027/312500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (204685639/312500000 : ℝ)^83 ≤ (3700272867111/6250000000000 : ℝ)^67 := by
    have hnat : (204685639 : ℕ)^83*6250000000000^67 ≤ 3700272867111^67*312500000^83 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      204685639 312500000 3700272867111 6250000000000 83 67 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (995956647/2500000000 : ℝ)^83 ≤ (31977888298983/100000000000000 : ℝ)^67 := by
    have hnat : (995956647 : ℕ)^83*100000000000000^67 ≤ 31977888298983^67*2500000000^83 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      995956647 2500000000 31977888298983 100000000000000 83 67 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (44006027/312500000 : ℝ)^83 ≤ (4408872907151/50000000000000 : ℝ)^67 := by
    have hnat : (44006027 : ℕ)^83*50000000000000^67 ≤ 4408872907151^67*312500000^83 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      44006027 312500000 4408872907151 50000000000000 83 67 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (83/16 : ℝ)) 83 67 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(204685639/312500000 : ℝ), (995956647/2500000000 : ℝ), (-44006027/312500000 : ℝ)] ![(3700272867111/6250000000000 : ℝ), (31977888298983/100000000000000 : ℝ), (4408872907151/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(204685639/312500000 : ℝ)|^83 ≤ (3700272867111/6250000000000 : ℝ)^67
        have hw : |(204685639/312500000 : ℝ)|=(204685639/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(995956647/2500000000 : ℝ)|^83 ≤ (31977888298983/100000000000000 : ℝ)^67
        have hw : |(995956647/2500000000 : ℝ)|=(995956647/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-44006027/312500000 : ℝ)|^83 ≤ (4408872907151/50000000000000 : ℝ)^67
        have hw : |(-44006027/312500000 : ℝ)|=(44006027/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_c321052 (p : ℝ) (hpa : (81/16 : ℝ) ≤ p) (hpb : p ≤ (83/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (11897/6250 : ℝ) (168549/100000 : ℝ) (80491/100000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![true, false, false]]) : False := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : RawLinearData _ _ X N P T := raw_linear_data (by linarith : (1 : ℝ) ≤ p) X hX.raw
  have bounds := raw_linear_data_bounds f (by norm_num)
  have main0 : (80491/100000 : ℝ)*P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.main 0
    change (80491/100000 : ℝ)*P 0 ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order0 : 0 ≤ ((1 : ℝ)*(X 1 2+X 2 2)) ∧ ((1 : ℝ)*(X 1 2+X 2 2)) ≤ ((1 : ℝ)*(X 1 1+X 2 1)) ∧ ((1 : ℝ)*(X 1 1+X 2 1)) ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.ordered 0
    change 0 ≤ ((1 : ℝ)*pair X 0 2) ∧ ((1 : ℝ)*pair X 0 2) ≤ ((1 : ℝ)*pair X 0 1) ∧ ((1 : ℝ)*pair X 0 1) ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main1 : (80491/100000 : ℝ)*P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.main 1
    change (80491/100000 : ℝ)*P 1 ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order1 : 0 ≤ ((-1 : ℝ)*(X 0 2+X 2 2)) ∧ ((-1 : ℝ)*(X 0 2+X 2 2)) ≤ ((1 : ℝ)*(X 0 0+X 2 0)) ∧ ((1 : ℝ)*(X 0 0+X 2 0)) ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.ordered 1
    change 0 ≤ ((-1 : ℝ)*pair X 1 2) ∧ ((-1 : ℝ)*pair X 1 2) ≤ ((1 : ℝ)*pair X 1 0) ∧ ((1 : ℝ)*pair X 1 0) ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main2 : (80491/100000 : ℝ)*P 2 ≤ ((-1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.main 2
    change (80491/100000 : ℝ)*P 2 ≤ ((-1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order2 : 0 ≤ ((-1 : ℝ)*(X 0 1+X 1 1)) ∧ ((-1 : ℝ)*(X 0 1+X 1 1)) ≤ ((1 : ℝ)*(X 0 0+X 1 0)) ∧ ((1 : ℝ)*(X 0 0+X 1 0)) ≤ ((-1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.ordered 2
    change 0 ≤ ((-1 : ℝ)*pair X 2 1) ∧ ((-1 : ℝ)*pair X 2 1) ≤ ((1 : ℝ)*pair X 2 0) ∧ ((1 : ℝ)*pair X 2 0) ≤ ((-1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have base7 : ((1 : ℝ)*T) ≤ (168549/100000 : ℝ) := by
    linarith only [f.Tcap]
  have base12 : ((-1 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    linarith only [(f.coord 0 2).1]
  have base15 : ((1 : ℝ)*X 1 0+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    linarith only [(f.coord 1 0).2]
  have base16 : ((-1 : ℝ)*X 1 1+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    linarith only [(f.coord 1 1).1]
  have base39 : ((-1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.1]
  have base40 : ((-1 : ℝ)*X 1 1+(1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 1+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.2.1]
  have base43 : ((-1 : ℝ)*N 0+(-1 : ℝ)*N 2+(1 : ℝ)*P 1) ≤ (0 : ℝ) := by
    linarith only [f.Ptriangle 1,f.sum]
  have base49 : ((1 : ℝ)*X 0 2+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order1.1]
  have base53 : ((-1 : ℝ)*N 0+(-1 : ℝ)*N 1+(1 : ℝ)*P 2) ≤ (0 : ℝ) := by
    linarith only [f.Ptriangle 2,f.sum]
  have base59 : ((1 : ℝ)*X 0 1+(1 : ℝ)*X 1 1) ≤ (0 : ℝ) := by
    linarith only [order2.1]
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
  have s0_pow0 : (1 : ℝ) ^ (81/16 : ℝ) ≤ (1 : ℝ) := by
    have hpowers : (1 : ℝ)^81 ≤ (1 : ℝ)^16 := by
      have hnat : (1 : ℕ)^81*1^16 ≤ 1^16*1^81 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 81 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) (by norm_num) 81 16 (by norm_num) hpowers
    exact h
  have s0_corner0a : (2 : ℝ) ≤ (11467340684240883/10000000000000000 : ℝ) ^ (81/16 : ℝ) := by
    have hpowers : (2 : ℝ)^16 ≤ (11467340684240883/10000000000000000 : ℝ)^81 := by
      have hnat : (2 : ℕ)^16*10000000000000000^81 ≤ 11467340684240883^81*1^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 1 11467340684240883 10000000000000000 16 81 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (11467340684240883/10000000000000000 : ℝ)) (X := (2 : ℝ)) (by norm_num) 81 16 (by norm_num) hpowers
    exact h
  have s0_corner0b : (3 : ℝ) ≤ (12423563204019309/10000000000000000 : ℝ) ^ (81/16 : ℝ) := by
    have hpowers : (3 : ℝ)^16 ≤ (12423563204019309/10000000000000000 : ℝ)^81 := by
      have hnat : (3 : ℕ)^16*10000000000000000^81 ≤ 12423563204019309^81*1^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3 1 12423563204019309 10000000000000000 16 81 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (12423563204019309/10000000000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 81 16 (by norm_num) hpowers
    exact h
  have major_s0_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(1467340684240883/10000000000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(478111259889213/5000000000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (81/16 : ℝ)) (rho := (1 : ℝ)) (alpha := (1467340684240883/10000000000000000 : ℝ)) (beta := (478111259889213/5000000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow0,s0_corner0a]) (by linarith only [s0_pow0,s0_corner0b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![true, false, false]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (1 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order0.2.2])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(1467340684240883/10000000000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(478111259889213/5000000000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s0_pow1 : (1 : ℝ) ^ (81/16 : ℝ) ≤ (1 : ℝ) := by
    have hpowers : (1 : ℝ)^81 ≤ (1 : ℝ)^16 := by
      have hnat : (1 : ℕ)^81*1^16 ≤ 1^16*1^81 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 81 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) (by norm_num) 81 16 (by norm_num) hpowers
    exact h
  have s0_corner1a : (2 : ℝ) ≤ (11467340684240883/10000000000000000 : ℝ) ^ (81/16 : ℝ) := by
    have hpowers : (2 : ℝ)^16 ≤ (11467340684240883/10000000000000000 : ℝ)^81 := by
      have hnat : (2 : ℕ)^16*10000000000000000^81 ≤ 11467340684240883^81*1^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 1 11467340684240883 10000000000000000 16 81 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (11467340684240883/10000000000000000 : ℝ)) (X := (2 : ℝ)) (by norm_num) 81 16 (by norm_num) hpowers
    exact h
  have s0_corner1b : (3 : ℝ) ≤ (12423563204019309/10000000000000000 : ℝ) ^ (81/16 : ℝ) := by
    have hpowers : (3 : ℝ)^16 ≤ (12423563204019309/10000000000000000 : ℝ)^81 := by
      have hnat : (3 : ℕ)^16*10000000000000000^81 ≤ 12423563204019309^81*1^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3 1 12423563204019309 10000000000000000 16 81 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (12423563204019309/10000000000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 81 16 (by norm_num) hpowers
    exact h
  have major_s0_1 : P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1))+(1467340684240883/10000000000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 2 0))+(478111259889213/5000000000000000 : ℝ)*((-1 : ℝ)*(X 0 2+X 2 2)) := by
    have hh := chart_majorant (a := (81/16 : ℝ)) (rho := (1 : ℝ)) (alpha := (1467340684240883/10000000000000000 : ℝ)) (beta := (478111259889213/5000000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow1,s0_corner1a]) (by linarith only [s0_pow1,s0_corner1b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![true, false, false]] hX 1 (by
        change ((1 : ℝ)*pair X 1 0) ≤ (1 : ℝ)*((1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order1.2.2])
    change lpNorm p (pair X 1) ≤ ((1 : ℝ)*pair X 1 1)+(1467340684240883/10000000000000000 : ℝ)*((1 : ℝ)*pair X 1 0)+(478111259889213/5000000000000000 : ℝ)*((-1 : ℝ)*pair X 1 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s0_pow2 : (1 : ℝ) ^ (81/16 : ℝ) ≤ (1 : ℝ) := by
    have hpowers : (1 : ℝ)^81 ≤ (1 : ℝ)^16 := by
      have hnat : (1 : ℕ)^81*1^16 ≤ 1^16*1^81 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 81 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) (by norm_num) 81 16 (by norm_num) hpowers
    exact h
  have s0_corner2a : (2 : ℝ) ≤ (11467340684240883/10000000000000000 : ℝ) ^ (81/16 : ℝ) := by
    have hpowers : (2 : ℝ)^16 ≤ (11467340684240883/10000000000000000 : ℝ)^81 := by
      have hnat : (2 : ℕ)^16*10000000000000000^81 ≤ 11467340684240883^81*1^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 1 11467340684240883 10000000000000000 16 81 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (11467340684240883/10000000000000000 : ℝ)) (X := (2 : ℝ)) (by norm_num) 81 16 (by norm_num) hpowers
    exact h
  have s0_corner2b : (3 : ℝ) ≤ (12423563204019309/10000000000000000 : ℝ) ^ (81/16 : ℝ) := by
    have hpowers : (3 : ℝ)^16 ≤ (12423563204019309/10000000000000000 : ℝ)^81 := by
      have hnat : (3 : ℕ)^16*10000000000000000^81 ≤ 12423563204019309^81*1^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3 1 12423563204019309 10000000000000000 16 81 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (12423563204019309/10000000000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 81 16 (by norm_num) hpowers
    exact h
  have major_s0_2 : P 2 ≤ ((-1 : ℝ)*(X 0 2+X 1 2))+(1467340684240883/10000000000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 1 0))+(478111259889213/5000000000000000 : ℝ)*((-1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (81/16 : ℝ)) (rho := (1 : ℝ)) (alpha := (1467340684240883/10000000000000000 : ℝ)) (beta := (478111259889213/5000000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow2,s0_corner2a]) (by linarith only [s0_pow2,s0_corner2b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![true, false, false]] hX 2 (by
        change ((1 : ℝ)*pair X 2 0) ≤ (1 : ℝ)*((-1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order2.2.2])
    change lpNorm p (pair X 2) ≤ ((-1 : ℝ)*pair X 2 2)+(1467340684240883/10000000000000000 : ℝ)*((1 : ℝ)*pair X 2 0)+(478111259889213/5000000000000000 : ℝ)*((-1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s0_0 : ((-324734873/5000000000 : ℝ)*X 0 0+(1683534489/5000000000 : ℝ)*X 0 1+(-7554926133/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c321052_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_1 : ((309492867/625000000 : ℝ)*X 1 0+(-2234286657/10000000000 : ℝ)*X 1 1+(-1002644779/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c321052_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_7 : ((-91390013/1000000000 : ℝ)*X 0 0+(12996147/125000000 : ℝ)*X 0 1+(-9084313309/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c321052_s0_7 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_8 : ((601136287/2000000000 : ℝ)*X 1 0+(-318681511/2500000000 : ℝ)*X 1 1+(-7467864131/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c321052_s0_8 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_9 : ((300568171/1000000000 : ℝ)*X 2 0+(2019630743/2500000000 : ℝ)*X 2 1+(3523593/200000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c321052_s0_9 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_13 : ((60089361/156250000 : ℝ)*X 0 0+(295097683/400000000 : ℝ)*X 0 1+(-199606817/10000000000 : ℝ)*X 0 2+(60089361/156250000 : ℝ)*X 1 0+(295097683/400000000 : ℝ)*X 1 1+(-199606817/10000000000 : ℝ)*X 1 2+(60089361/156250000 : ℝ)*X 2 0+(295097683/400000000 : ℝ)*X 2 1+(-199606817/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c321052_s0_13 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_14 : ((-105486509/10000000000 : ℝ)*X 0 0+(1353371673/10000000000 : ℝ)*X 0 1+(-2321870413/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c321052_s0_14 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_15 : ((113934097/625000000 : ℝ)*X 1 0+(-585291427/2500000000 : ℝ)*X 1 1+(-7611076027/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c321052_s0_15 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_16 : ((7374044903/10000000000 : ℝ)*X 2 0+(757673293/2000000000 : ℝ)*X 2 1+(316490773/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c321052_s0_16 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_20 : ((209627379/250000000 : ℝ)*X 0 0+(2525644021/10000000000 : ℝ)*X 0 1+(-322491339/10000000000 : ℝ)*X 0 2+(209627379/250000000 : ℝ)*X 1 0+(2525644021/10000000000 : ℝ)*X 1 1+(-322491339/10000000000 : ℝ)*X 1 2+(209627379/250000000 : ℝ)*X 2 0+(2525644021/10000000000 : ℝ)*X 2 1+(-322491339/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c321052_s0_20 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_21 : ((-516431/5000000000 : ℝ)*X 0 0+(2471986991/5000000000 : ℝ)*X 0 1+(-6461343281/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c321052_s0_21 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_22 : ((3530983293/5000000000 : ℝ)*X 1 0+(-1059513319/5000000000 : ℝ)*X 1 1+(-2769383209/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c321052_s0_22 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_23 : ((2094570843/10000000000 : ℝ)*X 2 0+(804051401/1000000000 : ℝ)*X 2 1+(1464323421/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c321052_s0_23 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_27 : ((8938492893/10000000000 : ℝ)*X 0 0+(877037087/5000000000 : ℝ)*X 0 1+(-159724359/5000000000 : ℝ)*X 0 2+(8938492893/10000000000 : ℝ)*X 1 0+(877037087/5000000000 : ℝ)*X 1 1+(-159724359/5000000000 : ℝ)*X 1 2+(8938492893/10000000000 : ℝ)*X 2 0+(877037087/5000000000 : ℝ)*X 2 1+(-159724359/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c321052_s0_27 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have ratio_s0_0 : (0 : ℝ) ≤ ((33613/50000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(33613/50000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (534174195890064839787/78125000000000000000000000 : ℝ) := by norm_num
    linear_combination (447770388729/500000000000 : ℝ)*(base7) + (2603/1000000000000 : ℝ)*(base39) + (18940190643/1000000000000 : ℝ)*(base59) + (1725798082107/1000000000000 : ℝ)*(major_s0_0) + (1725798082107/1000000000000 : ℝ)*(major_s0_1) + (1725798082107/1000000000000 : ℝ)*(major_s0_2) + (6586927/1000000000000 : ℝ)*(sp_s0_0) + (601287/250000000000 : ℝ)*(sp_s0_1) + (510446327923/250000000000 : ℝ)*(sp_s0_7) + (510452800691/250000000000 : ℝ)*(sp_s0_8) + (2041817090861/1000000000000 : ℝ)*(sp_s0_9) + (1802175896661/1000000000000 : ℝ)*(sp_s0_13) + (12596121/500000000000 : ℝ)*(sp_s0_14) + (69659/20000000000 : ℝ)*(sp_s0_15) + (226658779801/250000000000 : ℝ)*(f.failure) + (2041817090861/1000000000000 : ℝ)*(f.sum) + (1158901568180481/5000000000000000000000000000 : ℝ)*base63 + (843926818888209/5000000000000000000000000000 : ℝ)*base65 + (3941105727611791/5000000000000000000000000000 : ℝ)*base66 + (3564355060180481/10000000000000000000000000000 : ℝ)*base69 + (932141918043101/10000000000000000000000000000 : ℝ)*base70 + (2835056313111791/5000000000000000000000000000 : ℝ)*base73 + (6635596546180481/10000000000000000000000000000 : ℝ)*base75 + (9975790133180481/10000000000000000000000000000 : ℝ)*base77 + (4713959387/10000000000000000000000 : ℝ)*base79 + (1/1000000000000 : ℝ)*base83 + (619/3125000000000000 : ℝ)*base87 + (619/3125000000000000 : ℝ)*base89 + (619/3125000000000000 : ℝ)*base91 + (1/1000000000000 : ℝ)*base92 + hcertificate_margin
  have ratio_s0_1 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(13637/20000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(13637/20000 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (3419662944491058593883/500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (117293700923/125000000000 : ℝ)*(base7) + (33143/100000000000 : ℝ)*(base39) + (82679/1000000000000 : ℝ)*(base49) + (109071/1000000000000 : ℝ)*(base53) + (27972515907/500000000000 : ℝ)*(base59) + (1579109007801/1000000000000 : ℝ)*(major_s0_0) + (1579109007801/1000000000000 : ℝ)*(major_s0_1) + (157910889873/100000000000 : ℝ)*(major_s0_2) + (11036197/500000000000 : ℝ)*(sp_s0_8) + (1801449556071/1000000000000 : ℝ)*(sp_s0_14) + (1801427483677/1000000000000 : ℝ)*(sp_s0_15) + (1801449665141/1000000000000 : ℝ)*(sp_s0_16) + (55247019031/31250000000 : ℝ)*(sp_s0_20) + (4527289/250000000000 : ℝ)*(sp_s0_27) + (207393277691/250000000000 : ℝ)*(f.failure) + (1801449665141/1000000000000 : ℝ)*(f.sum) + (2179749706093127/10000000000000000000000000000 : ℝ)*base62 + (244633761589949/500000000000000000000000000 : ℝ)*base64 + (1722556181249387/5000000000000000000000000000 : ℝ)*base67 + (378204694922141/1000000000000000000000000000 : ℝ)*base68 + (3507529786670697/10000000000000000000000000000 : ℝ)*base70 + (719286207250613/5000000000000000000000000000 : ℝ)*base73 + (897457659128283/10000000000000000000000000000 : ℝ)*base75 + (177120469128283/10000000000000000000000000000 : ℝ)*base77 + (6296461697/10000000000000000000000 : ℝ)*base78 + (1/1000000000000 : ℝ)*base81 + (1/1000000000000 : ℝ)*base83 + (1529/3125000000000000 : ℝ)*base87 + (1529/3125000000000000 : ℝ)*base89 + (1529/3125000000000000 : ℝ)*base91 + hcertificate_margin
  have ratio_s0_2 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(-28163/50000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(-28163/50000 : ℝ)*X 1 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (29684241481777448712591/2500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (395335580329/500000000000 : ℝ)*(base7) + (116639/250000000000 : ℝ)*(base15) + (3330549503/10000000000 : ℝ)*(base39) + (45749551991/500000000000 : ℝ)*(base49) + (21951509861/100000000000 : ℝ)*(base59) + (833199433461/500000000000 : ℝ)*(major_s0_0) + (833199433461/500000000000 : ℝ)*(major_s0_1) + (833199433461/500000000000 : ℝ)*(major_s0_2) + (2348473/31250000000 : ℝ)*(sp_s0_9) + (5456131/500000000000 : ℝ)*(sp_s0_20) + (402628162427/200000000000 : ℝ)*(sp_s0_21) + (2013140345579/1000000000000 : ℝ)*(sp_s0_22) + (2013065660999/1000000000000 : ℝ)*(sp_s0_23) + (1666090434011/1000000000000 : ℝ)*(sp_s0_27) + (175086037123/200000000000 : ℝ)*(f.failure) + (402628162427/200000000000 : ℝ)*(f.sum) + (683192611136063/2500000000000000000000000000 : ℝ)*base63 + (429772528343807/2500000000000000000000000000 : ℝ)*base65 + (460464812406193/2500000000000000000000000000 : ℝ)*base66 + (1139476935886063/5000000000000000000000000000 : ℝ)*base69 + (747553997073677/5000000000000000000000000000 : ℝ)*base71 + (532437343093807/2500000000000000000000000000 : ℝ)*base72 + (840601224386063/5000000000000000000000000000 : ℝ)*base75 + (109701655386063/5000000000000000000000000000 : ℝ)*base77 + (5658093263/10000000000000000000000 : ℝ)*base78 + (169/1250000000000000 : ℝ)*base86 + (169/1250000000000000 : ℝ)*base88 + (169/1250000000000000 : ℝ)*base90 + hcertificate_margin
  have s1_pow0 : (33613/50000 : ℝ) ^ (81/16 : ℝ) ≤ (13393911815403035731/100000000000000000000 : ℝ) := by
    have hpowers : (33613/50000 : ℝ)^81 ≤ (13393911815403035731/100000000000000000000 : ℝ)^16 := by
      have hnat : (33613 : ℕ)^81*100000000000000000000^16 ≤ 13393911815403035731^16*50000^81 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        33613 50000 13393911815403035731 100000000000000000000 81 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (33613/50000 : ℝ)) (X := (13393911815403035731/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 81 16 (by norm_num) hpowers
    exact h
  have s1_corner0a : (113393911815403035731/100000000000000000000 : ℝ) ≤ (10251399491193757/10000000000000000 : ℝ) ^ (81/16 : ℝ) := by
    have hpowers : (113393911815403035731/100000000000000000000 : ℝ)^16 ≤ (10251399491193757/10000000000000000 : ℝ)^81 := by
      have hnat : (113393911815403035731 : ℕ)^16*10000000000000000^81 ≤ 10251399491193757^81*100000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        113393911815403035731 100000000000000000000 10251399491193757 10000000000000000 16 81 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10251399491193757/10000000000000000 : ℝ)) (X := (113393911815403035731/100000000000000000000 : ℝ)) (by norm_num) 81 16 (by norm_num) hpowers
    exact h
  have s1_corner0b : (63393911815403035731/50000000000000000000 : ℝ) ≤ (10479993105751893/10000000000000000 : ℝ) ^ (81/16 : ℝ) := by
    have hpowers : (63393911815403035731/50000000000000000000 : ℝ)^16 ≤ (10479993105751893/10000000000000000 : ℝ)^81 := by
      have hnat : (63393911815403035731 : ℕ)^16*10000000000000000^81 ≤ 10479993105751893^81*50000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        63393911815403035731 50000000000000000000 10479993105751893 10000000000000000 16 81 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10479993105751893/10000000000000000 : ℝ)) (X := (63393911815403035731/50000000000000000000 : ℝ)) (by norm_num) 81 16 (by norm_num) hpowers
    exact h
  have major_s1_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(251399491193757/6722600000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(28574201819767/840325000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (81/16 : ℝ)) (rho := (33613/50000 : ℝ)) (alpha := (251399491193757/6722600000000000 : ℝ)) (beta := (28574201819767/840325000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow0,s1_corner0a]) (by linarith only [s1_pow0,s1_corner0b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![true, false, false]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (33613/50000 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_0])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(251399491193757/6722600000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(28574201819767/840325000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s1_pow1 : (13637/20000 : ℝ) ^ (81/16 : ℝ) ≤ (1798704370841999713/12500000000000000000 : ℝ) := by
    have hpowers : (13637/20000 : ℝ)^81 ≤ (1798704370841999713/12500000000000000000 : ℝ)^16 := by
      have hnat : (13637 : ℕ)^81*12500000000000000000^16 ≤ 1798704370841999713^16*20000^81 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        13637 20000 1798704370841999713 12500000000000000000 81 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (13637/20000 : ℝ)) (X := (1798704370841999713/12500000000000000000 : ℝ)) (by norm_num) (by norm_num) 81 16 (by norm_num) hpowers
    exact h
  have s1_corner1a : (14298704370841999713/12500000000000000000 : ℝ) ≤ (10269118613169229/10000000000000000 : ℝ) ^ (81/16 : ℝ) := by
    have hpowers : (14298704370841999713/12500000000000000000 : ℝ)^16 ≤ (10269118613169229/10000000000000000 : ℝ)^81 := by
      have hnat : (14298704370841999713 : ℕ)^16*10000000000000000^81 ≤ 10269118613169229^81*12500000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14298704370841999713 12500000000000000000 10269118613169229 10000000000000000 16 81 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10269118613169229/10000000000000000 : ℝ)) (X := (14298704370841999713/12500000000000000000 : ℝ)) (by norm_num) 81 16 (by norm_num) hpowers
    exact h
  have s1_corner1b : (8048704370841999713/6250000000000000000 : ℝ) ≤ (1051230534604577/1000000000000000 : ℝ) ^ (81/16 : ℝ) := by
    have hpowers : (8048704370841999713/6250000000000000000 : ℝ)^16 ≤ (1051230534604577/1000000000000000 : ℝ)^81 := by
      have hnat : (8048704370841999713 : ℕ)^16*1000000000000000^81 ≤ 1051230534604577^81*6250000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        8048704370841999713 6250000000000000000 1051230534604577 1000000000000000 16 81 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1051230534604577/1000000000000000 : ℝ)) (X := (8048704370841999713/6250000000000000000 : ℝ)) (by norm_num) 81 16 (by norm_num) hpowers
    exact h
  have major_s1_1 : P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1))+(269118613169229/6818500000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 2 0))+(243186732876541/6818500000000000 : ℝ)*((-1 : ℝ)*(X 0 2+X 2 2)) := by
    have hh := chart_majorant (a := (81/16 : ℝ)) (rho := (13637/20000 : ℝ)) (alpha := (269118613169229/6818500000000000 : ℝ)) (beta := (243186732876541/6818500000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow1,s1_corner1a]) (by linarith only [s1_pow1,s1_corner1b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![true, false, false]] hX 1 (by
        change ((1 : ℝ)*pair X 1 0) ≤ (13637/20000 : ℝ)*((1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_1])
    change lpNorm p (pair X 1) ≤ ((1 : ℝ)*pair X 1 1)+(269118613169229/6818500000000000 : ℝ)*((1 : ℝ)*pair X 1 0)+(243186732876541/6818500000000000 : ℝ)*((-1 : ℝ)*pair X 1 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s1_pow2 : (28163/50000 : ℝ) ^ (81/16 : ℝ) ≤ (5469704460262211817/100000000000000000000 : ℝ) := by
    have hpowers : (28163/50000 : ℝ)^81 ≤ (5469704460262211817/100000000000000000000 : ℝ)^16 := by
      have hnat : (28163 : ℕ)^81*100000000000000000000^16 ≤ 5469704460262211817^16*50000^81 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        28163 50000 5469704460262211817 100000000000000000000 81 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (28163/50000 : ℝ)) (X := (5469704460262211817/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 81 16 (by norm_num) hpowers
    exact h
  have s1_corner2a : (105469704460262211817/100000000000000000000 : ℝ) ≤ (2021149488170039/2000000000000000 : ℝ) ^ (81/16 : ℝ) := by
    have hpowers : (105469704460262211817/100000000000000000000 : ℝ)^16 ≤ (2021149488170039/2000000000000000 : ℝ)^81 := by
      have hnat : (105469704460262211817 : ℕ)^16*2000000000000000^81 ≤ 2021149488170039^81*100000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        105469704460262211817 100000000000000000000 2021149488170039 2000000000000000 16 81 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2021149488170039/2000000000000000 : ℝ)) (X := (105469704460262211817/100000000000000000000 : ℝ)) (by norm_num) 81 16 (by norm_num) hpowers
    exact h
  have s1_corner2b : (55469704460262211817/50000000000000000000 : ℝ) ≤ (10207181715283509/10000000000000000 : ℝ) ^ (81/16 : ℝ) := by
    have hpowers : (55469704460262211817/50000000000000000000 : ℝ)^16 ≤ (10207181715283509/10000000000000000 : ℝ)^81 := by
      have hnat : (55469704460262211817 : ℕ)^16*10000000000000000^81 ≤ 10207181715283509^81*50000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        55469704460262211817 50000000000000000000 10207181715283509 10000000000000000 16 81 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10207181715283509/10000000000000000 : ℝ)) (X := (55469704460262211817/50000000000000000000 : ℝ)) (by norm_num) 81 16 (by norm_num) hpowers
    exact h
  have major_s1_2 : P 2 ≤ ((-1 : ℝ)*(X 0 2+X 1 2))+(21149488170039/1126520000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 1 0))+(50717137216657/2816300000000000 : ℝ)*((-1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (81/16 : ℝ)) (rho := (28163/50000 : ℝ)) (alpha := (21149488170039/1126520000000000 : ℝ)) (beta := (50717137216657/2816300000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow2,s1_corner2a]) (by linarith only [s1_pow2,s1_corner2b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![true, false, false]] hX 2 (by
        change ((1 : ℝ)*pair X 2 0) ≤ (28163/50000 : ℝ)*((-1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_2])
    change lpNorm p (pair X 2) ≤ ((-1 : ℝ)*pair X 2 2)+(21149488170039/1126520000000000 : ℝ)*((1 : ℝ)*pair X 2 0)+(50717137216657/2816300000000000 : ℝ)*((-1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s1_0 : ((-1938493709/10000000000 : ℝ)*X 0 0+(1789965397/5000000000 : ℝ)*X 0 1+(-6521616919/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c321052_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_1 : ((183011299/400000000 : ℝ)*X 1 0+(-2947901201/10000000000 : ℝ)*X 1 1+(-596833399/1250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c321052_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_2 : ((4715622137/10000000000 : ℝ)*X 2 0+(5615763263/10000000000 : ℝ)*X 2 1+(882449857/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c321052_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_6 : ((204685639/312500000 : ℝ)*X 0 0+(995956647/2500000000 : ℝ)*X 0 1+(-44006027/312500000 : ℝ)*X 0 2+(204685639/312500000 : ℝ)*X 1 0+(995956647/2500000000 : ℝ)*X 1 1+(-44006027/312500000 : ℝ)*X 1 2+(204685639/312500000 : ℝ)*X 2 0+(995956647/2500000000 : ℝ)*X 2 1+(-44006027/312500000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c321052_s1_6 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have hsep : (-26316/3125 : ℝ) < ((-11897/6250 : ℝ)*P 0+(-11897/6250 : ℝ)*P 1+(-11897/6250 : ℝ)*P 2+(1 : ℝ)*T) := by
    have hcertificate_margin : (-26316/3125 : ℝ) < (-271770527552697846291154034980868547/32273423716007500000000000000000000 : ℝ) := by norm_num
    linear_combination (20569/250000000000 : ℝ)*(base12) + (39683/1000000000000 : ℝ)*(base16) + (71548883989/200000000000 : ℝ)*(base39) + (589/100000000000 : ℝ)*(base40) + (1953/125000000000 : ℝ)*(base43) + (7437/250000000000 : ℝ)*(base53) + (232993043879/500000000000 : ℝ)*(base59) + (11897/6250 : ℝ)*(major_s1_0) + (237939998047/125000000000 : ℝ)*(major_s1_1) + (475879992563/250000000000 : ℝ)*(major_s1_2) + (2806958827801/1000000000000 : ℝ)*(sp_s1_0) + (1403479443009/500000000000 : ℝ)*(sp_s1_1) + (2806958941809/1000000000000 : ℝ)*(sp_s1_2) + (1 : ℝ)*(sp_s1_6) + (350869869431/125000000000 : ℝ)*(f.sum) + (488731584794150853/12001838468750000000000000000000 : ℝ)*base62 + (70226342535277/352037500000000000000000000 : ℝ)*base65 + (2828364689733367/3409250000000000000000000000 : ℝ)*base67 + (54285871311693/281630000000000000000000000 : ℝ)*base68 + (3900734063010430043/5916518243750000000000000000000 : ℝ)*base71 + (15466773406283/21008125000000000000000000 : ℝ)*base73 + (349658905132473/3409250000000000000000000000 : ℝ)*base74 + (667243810097487171/336130000000000000000000000 : ℝ)*base76 + (4528809237844765673/57297560125000000000000000000000 : ℝ)*base79 + (1/1000000000000 : ℝ)*base81 + (1/1000000000000 : ℝ)*base83 + (397/200000000000 : ℝ)*base85 + hcertificate_margin
  linarith only [hsep,f.failure]

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
namespace HlawkaSchatten.DiagonalCutoff4
theorem rawFrame_weaken_k {p k k' A : ℝ} {X : Fin 3 → Fin 3 → ℝ}
    (hp : 1 ≤ p) (hX : RawFrame p k A X) (hk : k' ≤ k) : RawFrame p k' A X := by
  have f := raw_linear_data hp X hX
  have hs : (∑ i, lpNorm p (pair X i)) ≤ 6 := by
    rw [Fin.sum_univ_three]
    have hh := f.sum
    linarith only [f.Ptriangle 0,f.Ptriangle 1,f.Ptriangle 2,hh]
  refine ⟨hX.sum,hX.row_total,hX.total_one,hX.total_cap,?_⟩
  have hh := mul_le_mul_of_nonneg_right hk (sub_nonneg.mpr hs)
  linarith only [hh,hX.linear_failure]
theorem orderedChart_weaken {p k k' A A' d d' : ℝ}
    {X : Fin 3 → Fin 3 → ℝ} {orders : Fin 3 → Fin 3 → Fin 3}
    {signs : Fin 3 → Fin 3 → Bool} (hp : 1 ≤ p)
    (hX : OrderedChart p k A d X orders signs)
    (hk : k' ≤ k) (hA : A ≤ A') (hd : d' ≤ d) :
    OrderedChart p k' A' d' X orders signs := by
  have hr := rawFrame_weaken_k hp hX.raw hk
  refine ⟨⟨hr.sum,hr.row_total,hr.total_one,hr.total_cap.trans hA,hr.linear_failure⟩,
    hX.permutation,?_,hX.ordered⟩
  intro i
  exact (mul_le_mul_of_nonneg_right hd (lpNorm_nonneg p (pair X i))).trans (hX.main i)
end HlawkaSchatten.DiagonalCutoff4

namespace HlawkaSchatten.DiagonalCutoff4
theorem coarse_distinct_p021_b031 (p : ℝ) (hpa : (81/16 : ℝ) ≤ p) (hpb : p ≤ (41/8 : ℝ))
    (c : Fin 88) (hlo : 52 ≤ c.val) (hhi : c.val < 56)
    (hn63 : c ≠ 63) (hn87 : c ≠ 87)
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (11897/6250 : ℝ) (168549/100000 : ℝ) (80491/100000 : ℝ) X (distinctOrders c) (distinctSigns c)) : False := by
  have hc : c=52 ∨ c=53 ∨ c=54 ∨ c=55 := by omega
  rcases hc with rfl|rfl|rfl|rfl
  · exact collision_c321052 p hpa (by linarith only [hpb]) X hX
  · exact collision_c320053 p (by linarith only [hpa]) (by linarith only [hpb]) X (orderedChart_weaken
      (by linarith only [hpa]) hX (by norm_num) (by norm_num) (by norm_num))
  · exact collision_c321054 p hpa (by linarith only [hpb]) X hX
  · exact collision_c321055 p hpa (by linarith only [hpb]) X hX

end HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p : ℝ) (hpa : (81/16 : ℝ) ≤ p) (hpb : p ≤ (41/8 : ℝ))
    (c : Fin 88) (hlo : 52 ≤ c.val) (hhi : c.val < 56)
    (hn63 : c ≠ 63) (hn87 : c ≠ 87)
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (11897/6250 : ℝ) (168549/100000 : ℝ) (80491/100000 : ℝ) X (distinctOrders c) (distinctSigns c)) : False := by
  exact HlawkaSchatten.DiagonalCutoff4.coarse_distinct_p021_b031 p hpa hpb c hlo hhi hn63 hn87 X hX

#print axioms solution
