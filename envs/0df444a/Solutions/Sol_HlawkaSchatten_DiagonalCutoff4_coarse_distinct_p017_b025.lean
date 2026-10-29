-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.coarse_distinct_p017_b025
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T01:13:43.861462+00:00
-- url     : https://prove2.me/submissions/6797497c-a0ad-4efb-b169-ca88c1dcc7ac

import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_collision_c316052_s0
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_collision_c316052_s1
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_collision_c316052_s2
import Definitions.Def_HlawkaSchatten_DiagonalCutoff4_Localization
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_collision_c316053_s0
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_collision_c316053_s1
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_collision_c316053_s2
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_collision_c316053_s3
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_collision_c316053_s4
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_collision_c317054_s0
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_collision_c317054_s1
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_collision_c317054_s2
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_collision_c317054_s3
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_collision_c317055_s0
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_collision_c317055_s1
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_collision_c317055_s2
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_collision_c317055_s3
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
theorem HlawkaSchatten.DiagonalCutoff4.collision_c316052 (p : ℝ) (hpa : (19/4 : ℝ) ≤ p) (hpb : p ≤ (39/8 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (177257/100000 : ℝ) (173433/100000 : ℝ) (1587/2000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![true, false, false]]) : False := by
  have h0 := collision_c316052_s0 p hpa hpb X hX
  have h1 := collision_c316052_s1 p hpa hpb X hX h0
  exact collision_c316052_s2 p hpa hpb X hX h1

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6 HlawkaSchatten.DiagonalCutoff4
theorem HlawkaSchatten.DiagonalCutoff4.collision_c316053 (p : ℝ) (hpa : (19/4 : ℝ) ≤ p) (hpb : p ≤ (39/8 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (177257/100000 : ℝ) (173433/100000 : ℝ) (1587/2000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![true, false, true]]) : False := by
  have h0 := collision_c316053_s0 p hpa hpb X hX
  have h1 := collision_c316053_s1 p hpa hpb X hX h0
  have h2 := collision_c316053_s2 p hpa hpb X hX h1
  have h3 := collision_c316053_s3 p hpa hpb X hX h2
  exact collision_c316053_s4 p hpa hpb X hX h3

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6 HlawkaSchatten.DiagonalCutoff4
theorem HlawkaSchatten.DiagonalCutoff4.collision_c317054 (p : ℝ) (hpa : (77/16 : ℝ) ≤ p) (hpb : p ≤ (39/8 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (89931/50000 : ℝ) (34473/20000 : ℝ) (19897/25000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![true, true, false]]) : False := by
  have h0 := collision_c317054_s0 p hpa hpb X hX
  have h1 := collision_c317054_s1 p hpa hpb X hX h0
  have h2 := collision_c317054_s2 p hpa hpb X hX h1
  exact collision_c317054_s3 p hpa hpb X hX h2

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6 HlawkaSchatten.DiagonalCutoff4
theorem HlawkaSchatten.DiagonalCutoff4.collision_c317055 (p : ℝ) (hpa : (77/16 : ℝ) ≤ p) (hpb : p ≤ (39/8 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (89931/50000 : ℝ) (34473/20000 : ℝ) (19897/25000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![true, true, true]]) : False := by
  have h0 := collision_c317055_s0 p hpa hpb X hX
  have h1 := collision_c317055_s1 p hpa hpb X hX h0
  have h2 := collision_c317055_s2 p hpa hpb X hX h1
  exact collision_c317055_s3 p hpa hpb X hX h2

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
theorem collision_support_c317051_s0_0 (p : ℝ) (hpa : (77/16 : ℝ) ≤ p) (hpb : p ≤ (79/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-837148217/2500000000 : ℝ)*x 0 + (669718583/2000000000 : ℝ)*x 1 + (5686946317/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (837148217/2500000000 : ℝ)^79 ≤ (25362523826017/100000000000000 : ℝ)^63 := by
    have hnat : (837148217 : ℕ)^79*100000000000000^63 ≤ 25362523826017^63*2500000000^79 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      837148217 2500000000 25362523826017 100000000000000 79 63 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (669718583/2000000000 : ℝ)^79 ≤ (25362524272407/100000000000000 : ℝ)^63 := by
    have hnat : (669718583 : ℕ)^79*100000000000000^63 ≤ 25362524272407^63*2000000000^79 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      669718583 2000000000 25362524272407 100000000000000 79 63 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5686946317/10000000000 : ℝ)^79 ≤ (12318737973597/25000000000000 : ℝ)^63 := by
    have hnat : (5686946317 : ℕ)^79*25000000000000^63 ≤ 12318737973597^63*10000000000^79 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5686946317 10000000000 12318737973597 25000000000000 79 63 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (79/16 : ℝ)) 79 63 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-837148217/2500000000 : ℝ), (669718583/2000000000 : ℝ), (5686946317/10000000000 : ℝ)] ![(25362523826017/100000000000000 : ℝ), (25362524272407/100000000000000 : ℝ), (12318737973597/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-837148217/2500000000 : ℝ)|^79 ≤ (25362523826017/100000000000000 : ℝ)^63
        have hw : |(-837148217/2500000000 : ℝ)|=(837148217/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(669718583/2000000000 : ℝ)|^79 ≤ (25362524272407/100000000000000 : ℝ)^63
        have hw : |(669718583/2000000000 : ℝ)|=(669718583/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5686946317/10000000000 : ℝ)|^79 ≤ (12318737973597/25000000000000 : ℝ)^63
        have hw : |(5686946317/10000000000 : ℝ)|=(5686946317/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c317051_s0_1 (p : ℝ) (hpa : (77/16 : ℝ) ≤ p) (hpb : p ≤ (79/16 : ℝ)) (x : Fin 3 → ℝ) :
    (2357211867/10000000000 : ℝ)*x 0 + (-1178605953/5000000000 : ℝ)*x 1 + (3647664499/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2357211867/10000000000 : ℝ)^79 ≤ (16330812473751/100000000000000 : ℝ)^63 := by
    have hnat : (2357211867 : ℕ)^79*100000000000000^63 ≤ 16330812473751^63*10000000000^79 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2357211867 10000000000 16330812473751 100000000000000 79 63 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1178605953/5000000000 : ℝ)^79 ≤ (3266162562513/20000000000000 : ℝ)^63 := by
    have hnat : (1178605953 : ℕ)^79*20000000000000^63 ≤ 3266162562513^63*5000000000^79 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1178605953 5000000000 3266162562513 20000000000000 79 63 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3647664499/5000000000 : ℝ)^79 ≤ (16834593675029/25000000000000 : ℝ)^63 := by
    have hnat : (3647664499 : ℕ)^79*25000000000000^63 ≤ 16834593675029^63*5000000000^79 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3647664499 5000000000 16834593675029 25000000000000 79 63 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (79/16 : ℝ)) 79 63 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2357211867/10000000000 : ℝ), (-1178605953/5000000000 : ℝ), (3647664499/5000000000 : ℝ)] ![(16330812473751/100000000000000 : ℝ), (3266162562513/20000000000000 : ℝ), (16834593675029/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2357211867/10000000000 : ℝ)|^79 ≤ (16330812473751/100000000000000 : ℝ)^63
        have hw : |(2357211867/10000000000 : ℝ)|=(2357211867/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1178605953/5000000000 : ℝ)|^79 ≤ (3266162562513/20000000000000 : ℝ)^63
        have hw : |(-1178605953/5000000000 : ℝ)|=(1178605953/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3647664499/5000000000 : ℝ)|^79 ≤ (16834593675029/25000000000000 : ℝ)^63
        have hw : |(3647664499/5000000000 : ℝ)|=(3647664499/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c317051_s0_7 (p : ℝ) (hpa : (77/16 : ℝ) ≤ p) (hpb : p ≤ (79/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-663078557/2500000000 : ℝ)*x 0 + (1722893721/10000000000 : ℝ)*x 1 + (7528073479/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (663078557/2500000000 : ℝ)^79 ≤ (9467035826117/50000000000000 : ℝ)^63 := by
    have hnat : (663078557 : ℕ)^79*50000000000000^63 ≤ 9467035826117^63*2500000000^79 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      663078557 2500000000 9467035826117 50000000000000 79 63 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1722893721/10000000000 : ℝ)^79 ≤ (11022811737661/100000000000000 : ℝ)^63 := by
    have hnat : (1722893721 : ℕ)^79*100000000000000^63 ≤ 11022811737661^63*10000000000^79 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1722893721 10000000000 11022811737661 100000000000000 79 63 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (7528073479/10000000000 : ℝ)^79 ≤ (70043116604793/100000000000000 : ℝ)^63 := by
    have hnat : (7528073479 : ℕ)^79*100000000000000^63 ≤ 70043116604793^63*10000000000^79 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7528073479 10000000000 70043116604793 100000000000000 79 63 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (79/16 : ℝ)) 79 63 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-663078557/2500000000 : ℝ), (1722893721/10000000000 : ℝ), (7528073479/10000000000 : ℝ)] ![(9467035826117/50000000000000 : ℝ), (11022811737661/100000000000000 : ℝ), (70043116604793/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-663078557/2500000000 : ℝ)|^79 ≤ (9467035826117/50000000000000 : ℝ)^63
        have hw : |(-663078557/2500000000 : ℝ)|=(663078557/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1722893721/10000000000 : ℝ)|^79 ≤ (11022811737661/100000000000000 : ℝ)^63
        have hw : |(1722893721/10000000000 : ℝ)|=(1722893721/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(7528073479/10000000000 : ℝ)|^79 ≤ (70043116604793/100000000000000 : ℝ)^63
        have hw : |(7528073479/10000000000 : ℝ)|=(7528073479/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c317051_s0_8 (p : ℝ) (hpa : (77/16 : ℝ) ≤ p) (hpb : p ≤ (79/16 : ℝ)) (x : Fin 3 → ℝ) :
    (265624123/2500000000 : ℝ)*x 0 + (-153699943/2500000000 : ℝ)*x 1 + (9272233031/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (265624123/2500000000 : ℝ)^79 ≤ (1503092161407/25000000000000 : ℝ)^63 := by
    have hnat : (265624123 : ℕ)^79*25000000000000^63 ≤ 1503092161407^63*2500000000^79 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      265624123 2500000000 1503092161407 25000000000000 79 63 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (153699943/2500000000 : ℝ)^79 ≤ (3027683749801/100000000000000 : ℝ)^63 := by
    have hnat : (153699943 : ℕ)^79*100000000000000^63 ≤ 3027683749801^63*2500000000^79 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      153699943 2500000000 3027683749801 100000000000000 79 63 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (9272233031/10000000000 : ℝ)^79 ≤ (11369993448053/12500000000000 : ℝ)^63 := by
    have hnat : (9272233031 : ℕ)^79*12500000000000^63 ≤ 11369993448053^63*10000000000^79 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      9272233031 10000000000 11369993448053 12500000000000 79 63 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (79/16 : ℝ)) 79 63 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(265624123/2500000000 : ℝ), (-153699943/2500000000 : ℝ), (9272233031/10000000000 : ℝ)] ![(1503092161407/25000000000000 : ℝ), (3027683749801/100000000000000 : ℝ), (11369993448053/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(265624123/2500000000 : ℝ)|^79 ≤ (1503092161407/25000000000000 : ℝ)^63
        have hw : |(265624123/2500000000 : ℝ)|=(265624123/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-153699943/2500000000 : ℝ)|^79 ≤ (3027683749801/100000000000000 : ℝ)^63
        have hw : |(-153699943/2500000000 : ℝ)|=(153699943/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(9272233031/10000000000 : ℝ)|^79 ≤ (11369993448053/12500000000000 : ℝ)^63
        have hw : |(9272233031/10000000000 : ℝ)|=(9272233031/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c317051_s0_9 (p : ℝ) (hpa : (77/16 : ℝ) ≤ p) (hpb : p ≤ (79/16 : ℝ)) (x : Fin 3 → ℝ) :
    (3967492621/10000000000 : ℝ)*x 0 + (7346669007/10000000000 : ℝ)*x 1 + (-189945241/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3967492621/10000000000 : ℝ)^79 ≤ (15686352638817/50000000000000 : ℝ)^63 := by
    have hnat : (3967492621 : ℕ)^79*50000000000000^63 ≤ 15686352638817^63*10000000000^79 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3967492621 10000000000 15686352638817 50000000000000 79 63 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (7346669007/10000000000 : ℝ)^79 ≤ (67933142545371/100000000000000 : ℝ)^63 := by
    have hnat : (7346669007 : ℕ)^79*100000000000000^63 ≤ 67933142545371^63*10000000000^79 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7346669007 10000000000 67933142545371 100000000000000 79 63 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (189945241/10000000000 : ℝ)^79 ≤ (694152163493/100000000000000 : ℝ)^63 := by
    have hnat : (189945241 : ℕ)^79*100000000000000^63 ≤ 694152163493^63*10000000000^79 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      189945241 10000000000 694152163493 100000000000000 79 63 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (79/16 : ℝ)) 79 63 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3967492621/10000000000 : ℝ), (7346669007/10000000000 : ℝ), (-189945241/10000000000 : ℝ)] ![(15686352638817/50000000000000 : ℝ), (67933142545371/100000000000000 : ℝ), (694152163493/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3967492621/10000000000 : ℝ)|^79 ≤ (15686352638817/50000000000000 : ℝ)^63
        have hw : |(3967492621/10000000000 : ℝ)|=(3967492621/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(7346669007/10000000000 : ℝ)|^79 ≤ (67933142545371/100000000000000 : ℝ)^63
        have hw : |(7346669007/10000000000 : ℝ)|=(7346669007/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-189945241/10000000000 : ℝ)|^79 ≤ (694152163493/100000000000000 : ℝ)^63
        have hw : |(-189945241/10000000000 : ℝ)|=(189945241/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c317051_s0_13 (p : ℝ) (hpa : (77/16 : ℝ) ≤ p) (hpb : p ≤ (79/16 : ℝ)) (x : Fin 3 → ℝ) :
    (672076149/2500000000 : ℝ)*x 0 + (522836853/625000000 : ℝ)*x 1 + (21198033/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (672076149/2500000000 : ℝ)^79 ≤ (19256799954763/100000000000000 : ℝ)^63 := by
    have hnat : (672076149 : ℕ)^79*100000000000000^63 ≤ 19256799954763^63*2500000000^79 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      672076149 2500000000 19256799954763 100000000000000 79 63 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (522836853/625000000 : ℝ)^79 ≤ (79946623022081/100000000000000 : ℝ)^63 := by
    have hnat : (522836853 : ℕ)^79*100000000000000^63 ≤ 79946623022081^63*625000000^79 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      522836853 625000000 79946623022081 100000000000000 79 63 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (21198033/1000000000 : ℝ)^79 ≤ (398288507317/50000000000000 : ℝ)^63 := by
    have hnat : (21198033 : ℕ)^79*50000000000000^63 ≤ 398288507317^63*1000000000^79 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      21198033 1000000000 398288507317 50000000000000 79 63 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (79/16 : ℝ)) 79 63 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(672076149/2500000000 : ℝ), (522836853/625000000 : ℝ), (21198033/1000000000 : ℝ)] ![(19256799954763/100000000000000 : ℝ), (79946623022081/100000000000000 : ℝ), (398288507317/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(672076149/2500000000 : ℝ)|^79 ≤ (19256799954763/100000000000000 : ℝ)^63
        have hw : |(672076149/2500000000 : ℝ)|=(672076149/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(522836853/625000000 : ℝ)|^79 ≤ (79946623022081/100000000000000 : ℝ)^63
        have hw : |(522836853/625000000 : ℝ)|=(522836853/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(21198033/1000000000 : ℝ)|^79 ≤ (398288507317/50000000000000 : ℝ)^63
        have hw : |(21198033/1000000000 : ℝ)|=(21198033/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c317051_s0_14 (p : ℝ) (hpa : (77/16 : ℝ) ≤ p) (hpb : p ≤ (79/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-462542487/2500000000 : ℝ)*x 0 + (1363543661/5000000000 : ℝ)*x 1 + (7381812373/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (462542487/2500000000 : ℝ)^79 ≤ (12053318642153/100000000000000 : ℝ)^63 := by
    have hnat : (462542487 : ℕ)^79*100000000000000^63 ≤ 12053318642153^63*2500000000^79 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      462542487 2500000000 12053318642153 100000000000000 79 63 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1363543661/5000000000 : ℝ)^79 ≤ (19605797648383/100000000000000 : ℝ)^63 := by
    have hnat : (1363543661 : ℕ)^79*100000000000000^63 ≤ 19605797648383^63*5000000000^79 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1363543661 5000000000 19605797648383 100000000000000 79 63 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (7381812373/10000000000 : ℝ)^79 ≤ (2733635347793/4000000000000 : ℝ)^63 := by
    have hnat : (7381812373 : ℕ)^79*4000000000000^63 ≤ 2733635347793^63*10000000000^79 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7381812373 10000000000 2733635347793 4000000000000 79 63 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (79/16 : ℝ)) 79 63 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-462542487/2500000000 : ℝ), (1363543661/5000000000 : ℝ), (7381812373/10000000000 : ℝ)] ![(12053318642153/100000000000000 : ℝ), (19605797648383/100000000000000 : ℝ), (2733635347793/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-462542487/2500000000 : ℝ)|^79 ≤ (12053318642153/100000000000000 : ℝ)^63
        have hw : |(-462542487/2500000000 : ℝ)|=(462542487/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1363543661/5000000000 : ℝ)|^79 ≤ (19605797648383/100000000000000 : ℝ)^63
        have hw : |(1363543661/5000000000 : ℝ)|=(1363543661/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(7381812373/10000000000 : ℝ)|^79 ≤ (2733635347793/4000000000000 : ℝ)^63
        have hw : |(7381812373/10000000000 : ℝ)|=(7381812373/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c317051_s0_15 (p : ℝ) (hpa : (77/16 : ℝ) ≤ p) (hpb : p ≤ (79/16 : ℝ)) (x : Fin 3 → ℝ) :
    (815579841/10000000000 : ℝ)*x 0 + (-37671609/312500000 : ℝ)*x 1 + (9083216641/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (815579841/10000000000 : ℝ)^79 ≤ (2157662582091/50000000000000 : ℝ)^63 := by
    have hnat : (815579841 : ℕ)^79*50000000000000^63 ≤ 2157662582091^63*10000000000^79 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      815579841 10000000000 2157662582091 50000000000000 79 63 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (37671609/312500000 : ℝ)^79 ≤ (7043832356431/100000000000000 : ℝ)^63 := by
    have hnat : (37671609 : ℕ)^79*100000000000000^63 ≤ 7043832356431^63*312500000^79 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      37671609 312500000 7043832356431 100000000000000 79 63 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (9083216641/10000000000 : ℝ)^79 ≤ (44320421236157/50000000000000 : ℝ)^63 := by
    have hnat : (9083216641 : ℕ)^79*50000000000000^63 ≤ 44320421236157^63*10000000000^79 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      9083216641 10000000000 44320421236157 50000000000000 79 63 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (79/16 : ℝ)) 79 63 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(815579841/10000000000 : ℝ), (-37671609/312500000 : ℝ), (9083216641/10000000000 : ℝ)] ![(2157662582091/50000000000000 : ℝ), (7043832356431/100000000000000 : ℝ), (44320421236157/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(815579841/10000000000 : ℝ)|^79 ≤ (2157662582091/50000000000000 : ℝ)^63
        have hw : |(815579841/10000000000 : ℝ)|=(815579841/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-37671609/312500000 : ℝ)|^79 ≤ (7043832356431/100000000000000 : ℝ)^63
        have hw : |(-37671609/312500000 : ℝ)|=(37671609/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(9083216641/10000000000 : ℝ)|^79 ≤ (44320421236157/50000000000000 : ℝ)^63
        have hw : |(9083216641/10000000000 : ℝ)|=(9083216641/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c317051_s0_16 (p : ℝ) (hpa : (77/16 : ℝ) ≤ p) (hpb : p ≤ (79/16 : ℝ)) (x : Fin 3 → ℝ) :
    (7715779031/10000000000 : ℝ)*x 0 + (355336043/1000000000 : ℝ)*x 1 + (-26302641/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (7715779031/10000000000 : ℝ)^79 ≤ (14448002795441/20000000000000 : ℝ)^63 := by
    have hnat : (7715779031 : ℕ)^79*20000000000000^63 ≤ 14448002795441^63*10000000000^79 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7715779031 10000000000 14448002795441 20000000000000 79 63 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (355336043/1000000000 : ℝ)^79 ≤ (27322214695901/100000000000000 : ℝ)^63 := by
    have hnat : (355336043 : ℕ)^79*100000000000000^63 ≤ 27322214695901^63*1000000000^79 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      355336043 1000000000 27322214695901 100000000000000 79 63 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (26302641/2000000000 : ℝ)^79 ≤ (437771308833/100000000000000 : ℝ)^63 := by
    have hnat : (26302641 : ℕ)^79*100000000000000^63 ≤ 437771308833^63*2000000000^79 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      26302641 2000000000 437771308833 100000000000000 79 63 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (79/16 : ℝ)) 79 63 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(7715779031/10000000000 : ℝ), (355336043/1000000000 : ℝ), (-26302641/2000000000 : ℝ)] ![(14448002795441/20000000000000 : ℝ), (27322214695901/100000000000000 : ℝ), (437771308833/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(7715779031/10000000000 : ℝ)|^79 ≤ (14448002795441/20000000000000 : ℝ)^63
        have hw : |(7715779031/10000000000 : ℝ)|=(7715779031/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(355336043/1000000000 : ℝ)|^79 ≤ (27322214695901/100000000000000 : ℝ)^63
        have hw : |(355336043/1000000000 : ℝ)|=(355336043/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-26302641/2000000000 : ℝ)|^79 ≤ (437771308833/100000000000000 : ℝ)^63
        have hw : |(-26302641/2000000000 : ℝ)|=(26302641/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c317051_s0_20 (p : ℝ) (hpa : (77/16 : ℝ) ≤ p) (hpb : p ≤ (79/16 : ℝ)) (x : Fin 3 → ℝ) :
    (478947269/625000000 : ℝ)*x 0 + (3583036787/10000000000 : ℝ)*x 1 + (12876489/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (478947269/625000000 : ℝ)^79 ≤ (71622735680319/100000000000000 : ℝ)^63 := by
    have hnat : (478947269 : ℕ)^79*100000000000000^63 ≤ 71622735680319^63*625000000^79 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      478947269 625000000 71622735680319 100000000000000 79 63 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3583036787/10000000000 : ℝ)^79 ≤ (13804327178267/50000000000000 : ℝ)^63 := by
    have hnat : (3583036787 : ℕ)^79*50000000000000^63 ≤ 13804327178267^63*10000000000^79 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3583036787 10000000000 13804327178267 50000000000000 79 63 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (12876489/625000000 : ℝ)^79 ≤ (768609947691/100000000000000 : ℝ)^63 := by
    have hnat : (12876489 : ℕ)^79*100000000000000^63 ≤ 768609947691^63*625000000^79 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      12876489 625000000 768609947691 100000000000000 79 63 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (79/16 : ℝ)) 79 63 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(478947269/625000000 : ℝ), (3583036787/10000000000 : ℝ), (12876489/625000000 : ℝ)] ![(71622735680319/100000000000000 : ℝ), (13804327178267/50000000000000 : ℝ), (768609947691/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(478947269/625000000 : ℝ)|^79 ≤ (71622735680319/100000000000000 : ℝ)^63
        have hw : |(478947269/625000000 : ℝ)|=(478947269/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3583036787/10000000000 : ℝ)|^79 ≤ (13804327178267/50000000000000 : ℝ)^63
        have hw : |(3583036787/10000000000 : ℝ)|=(3583036787/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(12876489/625000000 : ℝ)|^79 ≤ (768609947691/100000000000000 : ℝ)^63
        have hw : |(12876489/625000000 : ℝ)|=(12876489/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c317051_s0_21 (p : ℝ) (hpa : (77/16 : ℝ) ≤ p) (hpb : p ≤ (79/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-5344762903/10000000000 : ℝ)*x 0 + (2168718507/5000000000 : ℝ)*x 1 + (674130501/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5344762903/10000000000 : ℝ)^79 ≤ (142456059849/312500000000 : ℝ)^63 := by
    have hnat : (5344762903 : ℕ)^79*312500000000^63 ≤ 142456059849^63*10000000000^79 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5344762903 10000000000 142456059849 312500000000 79 63 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2168718507/5000000000 : ℝ)^79 ≤ (35083420247353/100000000000000 : ℝ)^63 := by
    have hnat : (2168718507 : ℕ)^79*100000000000000^63 ≤ 35083420247353^63*5000000000^79 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2168718507 5000000000 35083420247353 100000000000000 79 63 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (674130501/2500000000 : ℝ)^79 ≤ (19330640594369/100000000000000 : ℝ)^63 := by
    have hnat : (674130501 : ℕ)^79*100000000000000^63 ≤ 19330640594369^63*2500000000^79 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      674130501 2500000000 19330640594369 100000000000000 79 63 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (79/16 : ℝ)) 79 63 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-5344762903/10000000000 : ℝ), (2168718507/5000000000 : ℝ), (674130501/2500000000 : ℝ)] ![(142456059849/312500000000 : ℝ), (35083420247353/100000000000000 : ℝ), (19330640594369/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-5344762903/10000000000 : ℝ)|^79 ≤ (142456059849/312500000000 : ℝ)^63
        have hw : |(-5344762903/10000000000 : ℝ)|=(5344762903/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2168718507/5000000000 : ℝ)|^79 ≤ (35083420247353/100000000000000 : ℝ)^63
        have hw : |(2168718507/5000000000 : ℝ)|=(2168718507/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(674130501/2500000000 : ℝ)|^79 ≤ (19330640594369/100000000000000 : ℝ)^63
        have hw : |(674130501/2500000000 : ℝ)|=(674130501/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c317051_s0_22 (p : ℝ) (hpa : (77/16 : ℝ) ≤ p) (hpb : p ≤ (79/16 : ℝ)) (x : Fin 3 → ℝ) :
    (739845117/10000000000 : ℝ)*x 0 + (-1747171007/10000000000 : ℝ)*x 1 + (1756279873/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (739845117/10000000000 : ℝ)^79 ≤ (3818901688329/100000000000000 : ℝ)^63 := by
    have hnat : (739845117 : ℕ)^79*100000000000000^63 ≤ 3818901688329^63*10000000000^79 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      739845117 10000000000 3818901688329 100000000000000 79 63 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1747171007/10000000000 : ℝ)^79 ≤ (2804482091143/25000000000000 : ℝ)^63 := by
    have hnat : (1747171007 : ℕ)^79*25000000000000^63 ≤ 2804482091143^63*10000000000^79 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1747171007 10000000000 2804482091143 25000000000000 79 63 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1756279873/2000000000 : ℝ)^79 ≤ (21240792484859/25000000000000 : ℝ)^63 := by
    have hnat : (1756279873 : ℕ)^79*25000000000000^63 ≤ 21240792484859^63*2000000000^79 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1756279873 2000000000 21240792484859 25000000000000 79 63 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (79/16 : ℝ)) 79 63 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(739845117/10000000000 : ℝ), (-1747171007/10000000000 : ℝ), (1756279873/2000000000 : ℝ)] ![(3818901688329/100000000000000 : ℝ), (2804482091143/25000000000000 : ℝ), (21240792484859/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(739845117/10000000000 : ℝ)|^79 ≤ (3818901688329/100000000000000 : ℝ)^63
        have hw : |(739845117/10000000000 : ℝ)|=(739845117/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1747171007/10000000000 : ℝ)|^79 ≤ (2804482091143/25000000000000 : ℝ)^63
        have hw : |(-1747171007/10000000000 : ℝ)|=(1747171007/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1756279873/2000000000 : ℝ)|^79 ≤ (21240792484859/25000000000000 : ℝ)^63
        have hw : |(1756279873/2000000000 : ℝ)|=(1756279873/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c317051_s0_23 (p : ℝ) (hpa : (77/16 : ℝ) ≤ p) (hpb : p ≤ (79/16 : ℝ)) (x : Fin 3 → ℝ) :
    (1725271041/2500000000 : ℝ)*x 0 + (4516515943/10000000000 : ℝ)*x 1 + (-93104027/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1725271041/2500000000 : ℝ)^79 ≤ (62806911545811/100000000000000 : ℝ)^63 := by
    have hnat : (1725271041 : ℕ)^79*100000000000000^63 ≤ 62806911545811^63*2500000000^79 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1725271041 2500000000 62806911545811 100000000000000 79 63 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4516515943/10000000000 : ℝ)^79 ≤ (36909197897771/100000000000000 : ℝ)^63 := by
    have hnat : (4516515943 : ℕ)^79*100000000000000^63 ≤ 36909197897771^63*10000000000^79 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4516515943 10000000000 36909197897771 100000000000000 79 63 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (93104027/10000000000 : ℝ)^79 ≤ (35486318513/12500000000000 : ℝ)^63 := by
    have hnat : (93104027 : ℕ)^79*12500000000000^63 ≤ 35486318513^63*10000000000^79 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      93104027 10000000000 35486318513 12500000000000 79 63 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (79/16 : ℝ)) 79 63 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1725271041/2500000000 : ℝ), (4516515943/10000000000 : ℝ), (-93104027/10000000000 : ℝ)] ![(62806911545811/100000000000000 : ℝ), (36909197897771/100000000000000 : ℝ), (35486318513/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1725271041/2500000000 : ℝ)|^79 ≤ (62806911545811/100000000000000 : ℝ)^63
        have hw : |(1725271041/2500000000 : ℝ)|=(1725271041/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4516515943/10000000000 : ℝ)|^79 ≤ (36909197897771/100000000000000 : ℝ)^63
        have hw : |(4516515943/10000000000 : ℝ)|=(4516515943/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-93104027/10000000000 : ℝ)|^79 ≤ (35486318513/12500000000000 : ℝ)^63
        have hw : |(-93104027/10000000000 : ℝ)|=(93104027/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c317051_s0_27 (p : ℝ) (hpa : (77/16 : ℝ) ≤ p) (hpb : p ≤ (79/16 : ℝ)) (x : Fin 3 → ℝ) :
    (519214979/2000000000 : ℝ)*x 0 + (33112533/39062500 : ℝ)*x 1 + (93104027/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (519214979/2000000000 : ℝ)^79 ≤ (18431996689313/100000000000000 : ℝ)^63 := by
    have hnat : (519214979 : ℕ)^79*100000000000000^63 ≤ 18431996689313^63*2000000000^79 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      519214979 2000000000 18431996689313 100000000000000 79 63 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (33112533/39062500 : ℝ)^79 ≤ (81284112754039/100000000000000 : ℝ)^63 := by
    have hnat : (33112533 : ℕ)^79*100000000000000^63 ≤ 81284112754039^63*39062500^79 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      33112533 39062500 81284112754039 100000000000000 79 63 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (93104027/10000000000 : ℝ)^79 ≤ (35486318513/12500000000000 : ℝ)^63 := by
    have hnat : (93104027 : ℕ)^79*12500000000000^63 ≤ 35486318513^63*10000000000^79 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      93104027 10000000000 35486318513 12500000000000 79 63 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (79/16 : ℝ)) 79 63 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(519214979/2000000000 : ℝ), (33112533/39062500 : ℝ), (93104027/10000000000 : ℝ)] ![(18431996689313/100000000000000 : ℝ), (81284112754039/100000000000000 : ℝ), (35486318513/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(519214979/2000000000 : ℝ)|^79 ≤ (18431996689313/100000000000000 : ℝ)^63
        have hw : |(519214979/2000000000 : ℝ)|=(519214979/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(33112533/39062500 : ℝ)|^79 ≤ (81284112754039/100000000000000 : ℝ)^63
        have hw : |(33112533/39062500 : ℝ)|=(33112533/39062500 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(93104027/10000000000 : ℝ)|^79 ≤ (35486318513/12500000000000 : ℝ)^63
        have hw : |(93104027/10000000000 : ℝ)|=(93104027/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c317051_s1_0 (p : ℝ) (hpa : (77/16 : ℝ) ≤ p) (hpb : p ≤ (79/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-729901771/2000000000 : ℝ)*x 0 + (1821157423/5000000000 : ℝ)*x 1 + (2577468507/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (729901771/2000000000 : ℝ)^79 ≤ (28252433553283/100000000000000 : ℝ)^63 := by
    have hnat : (729901771 : ℕ)^79*100000000000000^63 ≤ 28252433553283^63*2000000000^79 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      729901771 2000000000 28252433553283 100000000000000 79 63 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1821157423/5000000000 : ℝ)^79 ≤ (28182615106681/100000000000000 : ℝ)^63 := by
    have hnat : (1821157423 : ℕ)^79*100000000000000^63 ≤ 28182615106681^63*5000000000^79 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1821157423 5000000000 28182615106681 100000000000000 79 63 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2577468507/5000000000 : ℝ)^79 ≤ (1089123783309/2500000000000 : ℝ)^63 := by
    have hnat : (2577468507 : ℕ)^79*2500000000000^63 ≤ 1089123783309^63*5000000000^79 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2577468507 5000000000 1089123783309 2500000000000 79 63 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (79/16 : ℝ)) 79 63 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-729901771/2000000000 : ℝ), (1821157423/5000000000 : ℝ), (2577468507/5000000000 : ℝ)] ![(28252433553283/100000000000000 : ℝ), (28182615106681/100000000000000 : ℝ), (1089123783309/2500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-729901771/2000000000 : ℝ)|^79 ≤ (28252433553283/100000000000000 : ℝ)^63
        have hw : |(-729901771/2000000000 : ℝ)|=(729901771/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1821157423/5000000000 : ℝ)|^79 ≤ (28182615106681/100000000000000 : ℝ)^63
        have hw : |(1821157423/5000000000 : ℝ)|=(1821157423/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2577468507/5000000000 : ℝ)|^79 ≤ (1089123783309/2500000000000 : ℝ)^63
        have hw : |(2577468507/5000000000 : ℝ)|=(2577468507/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c317051_s1_1 (p : ℝ) (hpa : (77/16 : ℝ) ≤ p) (hpb : p ≤ (79/16 : ℝ)) (x : Fin 3 → ℝ) :
    (2908622023/10000000000 : ℝ)*x 0 + (-290288847/1000000000 : ℝ)*x 1 + (6435571579/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2908622023/10000000000 : ℝ)^79 ≤ (21255967877763/100000000000000 : ℝ)^63 := by
    have hnat : (2908622023 : ℕ)^79*100000000000000^63 ≤ 21255967877763^63*10000000000^79 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2908622023 10000000000 21255967877763 100000000000000 79 63 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (290288847/1000000000 : ℝ)^79 ≤ (10601719677163/50000000000000 : ℝ)^63 := by
    have hnat : (290288847 : ℕ)^79*50000000000000^63 ≤ 10601719677163^63*1000000000^79 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      290288847 1000000000 10601719677163 50000000000000 79 63 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (6435571579/10000000000 : ℝ)^79 ≤ (57540592750809/100000000000000 : ℝ)^63 := by
    have hnat : (6435571579 : ℕ)^79*100000000000000^63 ≤ 57540592750809^63*10000000000^79 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6435571579 10000000000 57540592750809 100000000000000 79 63 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (79/16 : ℝ)) 79 63 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2908622023/10000000000 : ℝ), (-290288847/1000000000 : ℝ), (6435571579/10000000000 : ℝ)] ![(21255967877763/100000000000000 : ℝ), (10601719677163/50000000000000 : ℝ), (57540592750809/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2908622023/10000000000 : ℝ)|^79 ≤ (21255967877763/100000000000000 : ℝ)^63
        have hw : |(2908622023/10000000000 : ℝ)|=(2908622023/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-290288847/1000000000 : ℝ)|^79 ≤ (10601719677163/50000000000000 : ℝ)^63
        have hw : |(-290288847/1000000000 : ℝ)|=(290288847/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(6435571579/10000000000 : ℝ)|^79 ≤ (57540592750809/100000000000000 : ℝ)^63
        have hw : |(6435571579/10000000000 : ℝ)|=(6435571579/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c317051_s1_2 (p : ℝ) (hpa : (77/16 : ℝ) ≤ p) (hpb : p ≤ (79/16 : ℝ)) (x : Fin 3 → ℝ) :
    (2670804927/5000000000 : ℝ)*x 0 + (267553731/500000000 : ℝ)*x 1 + (-1438914439/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2670804927/5000000000 : ℝ)^79 ≤ (45552219181337/100000000000000 : ℝ)^63 := by
    have hnat : (2670804927 : ℕ)^79*100000000000000^63 ≤ 45552219181337^63*5000000000^79 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2670804927 5000000000 45552219181337 100000000000000 79 63 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (267553731/500000000 : ℝ)^79 ≤ (22826727180911/50000000000000 : ℝ)^63 := by
    have hnat : (267553731 : ℕ)^79*50000000000000^63 ≤ 22826727180911^63*500000000^79 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      267553731 500000000 22826727180911 50000000000000 79 63 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1438914439/10000000000 : ℝ)^79 ≤ (8794326437147/100000000000000 : ℝ)^63 := by
    have hnat : (1438914439 : ℕ)^79*100000000000000^63 ≤ 8794326437147^63*10000000000^79 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1438914439 10000000000 8794326437147 100000000000000 79 63 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (79/16 : ℝ)) 79 63 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2670804927/5000000000 : ℝ), (267553731/500000000 : ℝ), (-1438914439/10000000000 : ℝ)] ![(45552219181337/100000000000000 : ℝ), (22826727180911/50000000000000 : ℝ), (8794326437147/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2670804927/5000000000 : ℝ)|^79 ≤ (45552219181337/100000000000000 : ℝ)^63
        have hw : |(2670804927/5000000000 : ℝ)|=(2670804927/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(267553731/500000000 : ℝ)|^79 ≤ (22826727180911/50000000000000 : ℝ)^63
        have hw : |(267553731/500000000 : ℝ)|=(267553731/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1438914439/10000000000 : ℝ)|^79 ≤ (8794326437147/100000000000000 : ℝ)^63
        have hw : |(-1438914439/10000000000 : ℝ)|=(1438914439/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c317051_s1_6 (p : ℝ) (hpa : (77/16 : ℝ) ≤ p) (hpb : p ≤ (79/16 : ℝ)) (x : Fin 3 → ℝ) :
    (507448627/1000000000 : ℝ)*x 0 + (5083477721/10000000000 : ℝ)*x 1 + (2141242149/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (507448627/1000000000 : ℝ)^79 ≤ (2669629793841/6250000000000 : ℝ)^63 := by
    have hnat : (507448627 : ℕ)^79*6250000000000^63 ≤ 2669629793841^63*1000000000^79 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      507448627 1000000000 2669629793841 6250000000000 79 63 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5083477721/10000000000 : ℝ)^79 ≤ (42809004394881/100000000000000 : ℝ)^63 := by
    have hnat : (5083477721 : ℕ)^79*100000000000000^63 ≤ 42809004394881^63*10000000000^79 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5083477721 10000000000 42809004394881 100000000000000 79 63 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2141242149/10000000000 : ℝ)^79 ≤ (14476918895651/100000000000000 : ℝ)^63 := by
    have hnat : (2141242149 : ℕ)^79*100000000000000^63 ≤ 14476918895651^63*10000000000^79 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2141242149 10000000000 14476918895651 100000000000000 79 63 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (79/16 : ℝ)) 79 63 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(507448627/1000000000 : ℝ), (5083477721/10000000000 : ℝ), (2141242149/10000000000 : ℝ)] ![(2669629793841/6250000000000 : ℝ), (42809004394881/100000000000000 : ℝ), (14476918895651/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(507448627/1000000000 : ℝ)|^79 ≤ (2669629793841/6250000000000 : ℝ)^63
        have hw : |(507448627/1000000000 : ℝ)|=(507448627/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5083477721/10000000000 : ℝ)|^79 ≤ (42809004394881/100000000000000 : ℝ)^63
        have hw : |(5083477721/10000000000 : ℝ)|=(5083477721/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2141242149/10000000000 : ℝ)|^79 ≤ (14476918895651/100000000000000 : ℝ)^63
        have hw : |(2141242149/10000000000 : ℝ)|=(2141242149/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_c317051 (p : ℝ) (hpa : (77/16 : ℝ) ≤ p) (hpb : p ≤ (79/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (89931/50000 : ℝ) (34473/20000 : ℝ) (19897/25000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![false, true, true]]) : False := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : RawLinearData _ _ X N P T := raw_linear_data (by linarith : (1 : ℝ) ≤ p) X hX.raw
  have bounds := raw_linear_data_bounds f (by norm_num)
  have main0 : (19897/25000 : ℝ)*P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.main 0
    change (19897/25000 : ℝ)*P 0 ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order0 : 0 ≤ ((1 : ℝ)*(X 1 2+X 2 2)) ∧ ((1 : ℝ)*(X 1 2+X 2 2)) ≤ ((1 : ℝ)*(X 1 1+X 2 1)) ∧ ((1 : ℝ)*(X 1 1+X 2 1)) ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.ordered 0
    change 0 ≤ ((1 : ℝ)*pair X 0 2) ∧ ((1 : ℝ)*pair X 0 2) ≤ ((1 : ℝ)*pair X 0 1) ∧ ((1 : ℝ)*pair X 0 1) ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main1 : (19897/25000 : ℝ)*P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.main 1
    change (19897/25000 : ℝ)*P 1 ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order1 : 0 ≤ ((-1 : ℝ)*(X 0 2+X 2 2)) ∧ ((-1 : ℝ)*(X 0 2+X 2 2)) ≤ ((1 : ℝ)*(X 0 0+X 2 0)) ∧ ((1 : ℝ)*(X 0 0+X 2 0)) ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.ordered 1
    change 0 ≤ ((-1 : ℝ)*pair X 1 2) ∧ ((-1 : ℝ)*pair X 1 2) ≤ ((1 : ℝ)*pair X 1 0) ∧ ((1 : ℝ)*pair X 1 0) ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main2 : (19897/25000 : ℝ)*P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.main 2
    change (19897/25000 : ℝ)*P 2 ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order2 : 0 ≤ ((1 : ℝ)*(X 0 1+X 1 1)) ∧ ((1 : ℝ)*(X 0 1+X 1 1)) ≤ ((-1 : ℝ)*(X 0 0+X 1 0)) ∧ ((-1 : ℝ)*(X 0 0+X 1 0)) ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.ordered 2
    change 0 ≤ ((1 : ℝ)*pair X 2 1) ∧ ((1 : ℝ)*pair X 2 1) ≤ ((-1 : ℝ)*pair X 2 0) ∧ ((-1 : ℝ)*pair X 2 0) ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have base5 : ((1 : ℝ)*N 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    linarith only [f.Ntotal 2]
  have base7 : ((1 : ℝ)*T) ≤ (34473/20000 : ℝ) := by
    linarith only [f.Tcap]
  have base19 : ((1 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    linarith only [(f.coord 1 2).2]
  have base21 : ((1 : ℝ)*X 2 0+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    linarith only [(f.coord 2 0).2]
  have base39 : ((-1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.1]
  have base40 : ((-1 : ℝ)*X 1 1+(1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 1+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.2.1]
  have base44 : ((-1 : ℝ)*N 1+(1 : ℝ)*P 1+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    linarith only [f.Ptotal 1]
  have base49 : ((1 : ℝ)*X 0 2+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order1.1]
  have base53 : ((-1 : ℝ)*N 0+(-1 : ℝ)*N 1+(1 : ℝ)*P 2) ≤ (0 : ℝ) := by
    linarith only [f.Ptriangle 2,f.sum]
  have base59 : ((-1 : ℝ)*X 0 1+(-1 : ℝ)*X 1 1) ≤ (0 : ℝ) := by
    linarith only [order2.1]
  have base60 : ((1 : ℝ)*X 0 0+(1 : ℝ)*X 0 1+(1 : ℝ)*X 1 0+(1 : ℝ)*X 1 1) ≤ (0 : ℝ) := by
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
  have s0_pow0 : (1 : ℝ) ^ (77/16 : ℝ) ≤ (1 : ℝ) := by
    have hpowers : (1 : ℝ)^77 ≤ (1 : ℝ)^16 := by
      have hnat : (1 : ℕ)^77*1^16 ≤ 1^16*1^77 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 77 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) (by norm_num) 77 16 (by norm_num) hpowers
    exact h
  have s0_corner0a : (2 : ℝ) ≤ (11549194288550923/10000000000000000 : ℝ) ^ (77/16 : ℝ) := by
    have hpowers : (2 : ℝ)^16 ≤ (11549194288550923/10000000000000000 : ℝ)^77 := by
      have hnat : (2 : ℕ)^16*10000000000000000^77 ≤ 11549194288550923^77*1^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 1 11549194288550923 10000000000000000 16 77 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (11549194288550923/10000000000000000 : ℝ)) (X := (2 : ℝ)) (by norm_num) 77 16 (by norm_num) hpowers
    exact h
  have s0_corner0b : (3 : ℝ) ≤ (3141102348914959/2500000000000000 : ℝ) ^ (77/16 : ℝ) := by
    have hpowers : (3 : ℝ)^16 ≤ (3141102348914959/2500000000000000 : ℝ)^77 := by
      have hnat : (3 : ℕ)^16*2500000000000000^77 ≤ 3141102348914959^77*1^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3 1 3141102348914959 2500000000000000 16 77 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (3141102348914959/2500000000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 77 16 (by norm_num) hpowers
    exact h
  have major_s0_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(1549194288550923/10000000000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(1015215107108913/10000000000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (77/16 : ℝ)) (rho := (1 : ℝ)) (alpha := (1549194288550923/10000000000000000 : ℝ)) (beta := (1015215107108913/10000000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow0,s0_corner0a]) (by linarith only [s0_pow0,s0_corner0b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![false, true, true]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (1 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order0.2.2])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(1549194288550923/10000000000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(1015215107108913/10000000000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s0_pow1 : (1 : ℝ) ^ (77/16 : ℝ) ≤ (1 : ℝ) := by
    have hpowers : (1 : ℝ)^77 ≤ (1 : ℝ)^16 := by
      have hnat : (1 : ℕ)^77*1^16 ≤ 1^16*1^77 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 77 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) (by norm_num) 77 16 (by norm_num) hpowers
    exact h
  have s0_corner1a : (2 : ℝ) ≤ (11549194288550923/10000000000000000 : ℝ) ^ (77/16 : ℝ) := by
    have hpowers : (2 : ℝ)^16 ≤ (11549194288550923/10000000000000000 : ℝ)^77 := by
      have hnat : (2 : ℕ)^16*10000000000000000^77 ≤ 11549194288550923^77*1^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 1 11549194288550923 10000000000000000 16 77 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (11549194288550923/10000000000000000 : ℝ)) (X := (2 : ℝ)) (by norm_num) 77 16 (by norm_num) hpowers
    exact h
  have s0_corner1b : (3 : ℝ) ≤ (3141102348914959/2500000000000000 : ℝ) ^ (77/16 : ℝ) := by
    have hpowers : (3 : ℝ)^16 ≤ (3141102348914959/2500000000000000 : ℝ)^77 := by
      have hnat : (3 : ℕ)^16*2500000000000000^77 ≤ 3141102348914959^77*1^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3 1 3141102348914959 2500000000000000 16 77 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (3141102348914959/2500000000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 77 16 (by norm_num) hpowers
    exact h
  have major_s0_1 : P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1))+(1549194288550923/10000000000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 2 0))+(1015215107108913/10000000000000000 : ℝ)*((-1 : ℝ)*(X 0 2+X 2 2)) := by
    have hh := chart_majorant (a := (77/16 : ℝ)) (rho := (1 : ℝ)) (alpha := (1549194288550923/10000000000000000 : ℝ)) (beta := (1015215107108913/10000000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow1,s0_corner1a]) (by linarith only [s0_pow1,s0_corner1b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![false, true, true]] hX 1 (by
        change ((1 : ℝ)*pair X 1 0) ≤ (1 : ℝ)*((1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order1.2.2])
    change lpNorm p (pair X 1) ≤ ((1 : ℝ)*pair X 1 1)+(1549194288550923/10000000000000000 : ℝ)*((1 : ℝ)*pair X 1 0)+(1015215107108913/10000000000000000 : ℝ)*((-1 : ℝ)*pair X 1 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s0_pow2 : (1 : ℝ) ^ (77/16 : ℝ) ≤ (1 : ℝ) := by
    have hpowers : (1 : ℝ)^77 ≤ (1 : ℝ)^16 := by
      have hnat : (1 : ℕ)^77*1^16 ≤ 1^16*1^77 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 77 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) (by norm_num) 77 16 (by norm_num) hpowers
    exact h
  have s0_corner2a : (2 : ℝ) ≤ (11549194288550923/10000000000000000 : ℝ) ^ (77/16 : ℝ) := by
    have hpowers : (2 : ℝ)^16 ≤ (11549194288550923/10000000000000000 : ℝ)^77 := by
      have hnat : (2 : ℕ)^16*10000000000000000^77 ≤ 11549194288550923^77*1^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 1 11549194288550923 10000000000000000 16 77 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (11549194288550923/10000000000000000 : ℝ)) (X := (2 : ℝ)) (by norm_num) 77 16 (by norm_num) hpowers
    exact h
  have s0_corner2b : (3 : ℝ) ≤ (3141102348914959/2500000000000000 : ℝ) ^ (77/16 : ℝ) := by
    have hpowers : (3 : ℝ)^16 ≤ (3141102348914959/2500000000000000 : ℝ)^77 := by
      have hnat : (3 : ℕ)^16*2500000000000000^77 ≤ 3141102348914959^77*1^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3 1 3141102348914959 2500000000000000 16 77 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (3141102348914959/2500000000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 77 16 (by norm_num) hpowers
    exact h
  have major_s0_2 : P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2))+(1549194288550923/10000000000000000 : ℝ)*((-1 : ℝ)*(X 0 0+X 1 0))+(1015215107108913/10000000000000000 : ℝ)*((1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (77/16 : ℝ)) (rho := (1 : ℝ)) (alpha := (1549194288550923/10000000000000000 : ℝ)) (beta := (1015215107108913/10000000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow2,s0_corner2a]) (by linarith only [s0_pow2,s0_corner2b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![false, true, true]] hX 2 (by
        change ((-1 : ℝ)*pair X 2 0) ≤ (1 : ℝ)*((1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order2.2.2])
    change lpNorm p (pair X 2) ≤ ((1 : ℝ)*pair X 2 2)+(1549194288550923/10000000000000000 : ℝ)*((-1 : ℝ)*pair X 2 0)+(1015215107108913/10000000000000000 : ℝ)*((1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s0_0 : ((-837148217/2500000000 : ℝ)*X 0 0+(669718583/2000000000 : ℝ)*X 0 1+(5686946317/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c317051_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_1 : ((2357211867/10000000000 : ℝ)*X 1 0+(-1178605953/5000000000 : ℝ)*X 1 1+(3647664499/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c317051_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_7 : ((-663078557/2500000000 : ℝ)*X 0 0+(1722893721/10000000000 : ℝ)*X 0 1+(7528073479/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c317051_s0_7 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_8 : ((265624123/2500000000 : ℝ)*X 1 0+(-153699943/2500000000 : ℝ)*X 1 1+(9272233031/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c317051_s0_8 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_9 : ((3967492621/10000000000 : ℝ)*X 2 0+(7346669007/10000000000 : ℝ)*X 2 1+(-189945241/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c317051_s0_9 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_13 : ((672076149/2500000000 : ℝ)*X 0 0+(522836853/625000000 : ℝ)*X 0 1+(21198033/1000000000 : ℝ)*X 0 2+(672076149/2500000000 : ℝ)*X 1 0+(522836853/625000000 : ℝ)*X 1 1+(21198033/1000000000 : ℝ)*X 1 2+(672076149/2500000000 : ℝ)*X 2 0+(522836853/625000000 : ℝ)*X 2 1+(21198033/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c317051_s0_13 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_14 : ((-462542487/2500000000 : ℝ)*X 0 0+(1363543661/5000000000 : ℝ)*X 0 1+(7381812373/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c317051_s0_14 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_15 : ((815579841/10000000000 : ℝ)*X 1 0+(-37671609/312500000 : ℝ)*X 1 1+(9083216641/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c317051_s0_15 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_16 : ((7715779031/10000000000 : ℝ)*X 2 0+(355336043/1000000000 : ℝ)*X 2 1+(-26302641/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c317051_s0_16 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_20 : ((478947269/625000000 : ℝ)*X 0 0+(3583036787/10000000000 : ℝ)*X 0 1+(12876489/625000000 : ℝ)*X 0 2+(478947269/625000000 : ℝ)*X 1 0+(3583036787/10000000000 : ℝ)*X 1 1+(12876489/625000000 : ℝ)*X 1 2+(478947269/625000000 : ℝ)*X 2 0+(3583036787/10000000000 : ℝ)*X 2 1+(12876489/625000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c317051_s0_20 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_21 : ((-5344762903/10000000000 : ℝ)*X 0 0+(2168718507/5000000000 : ℝ)*X 0 1+(674130501/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c317051_s0_21 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_22 : ((739845117/10000000000 : ℝ)*X 1 0+(-1747171007/10000000000 : ℝ)*X 1 1+(1756279873/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c317051_s0_22 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_23 : ((1725271041/2500000000 : ℝ)*X 2 0+(4516515943/10000000000 : ℝ)*X 2 1+(-93104027/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c317051_s0_23 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_27 : ((519214979/2000000000 : ℝ)*X 0 0+(33112533/39062500 : ℝ)*X 0 1+(93104027/10000000000 : ℝ)*X 0 2+(519214979/2000000000 : ℝ)*X 1 0+(33112533/39062500 : ℝ)*X 1 1+(93104027/10000000000 : ℝ)*X 1 2+(519214979/2000000000 : ℝ)*X 2 0+(33112533/39062500 : ℝ)*X 2 1+(93104027/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c317051_s0_27 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have ratio_s0_0 : (0 : ℝ) ≤ ((3601/5000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(3601/5000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (7461231199549278788343/500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (850238532837/1000000000000 : ℝ)*(base7) + (6647077/1000000000000 : ℝ)*(base19) + (1240113/500000000000 : ℝ)*(base49) + (49466911619/1000000000000 : ℝ)*(base60) + (1745387632581/1000000000000 : ℝ)*(major_s0_0) + (1745387632581/1000000000000 : ℝ)*(major_s0_1) + (1745387632581/1000000000000 : ℝ)*(major_s0_2) + (2109081/500000000000 : ℝ)*(sp_s0_0) + (2031799498333/1000000000000 : ℝ)*(sp_s0_7) + (1015927661391/500000000000 : ℝ)*(sp_s0_8) + (2031861969859/1000000000000 : ℝ)*(sp_s0_9) + (1820451793243/1000000000000 : ℝ)*(sp_s0_13) + (14563341/250000000000 : ℝ)*(sp_s0_14) + (95255849/500000000000 : ℝ)*(sp_s0_27) + (121300471513/125000000000 : ℝ)*(f.failure) + (2031861969859/1000000000000 : ℝ)*(f.sum) + (2264944537/5000000000000000000000 : ℝ)*base63 + (1522790695294453/10000000000000000000000000000 : ℝ)*base65 + (4465815063294453/10000000000000000000000000000 : ℝ)*base66 + (2714964685577737/10000000000000000000000000000 : ℝ)*base69 + (869081240679179/2500000000000000000000000000 : ℝ)*base71 + (2152525883705547/10000000000000000000000000000 : ℝ)*base72 + (2185088944577737/10000000000000000000000000000 : ℝ)*base74 + (2259145148577737/10000000000000000000000000000 : ℝ)*base76 + (3414827017/10000000000000000000000 : ℝ)*base78 + (4353/6250000000000000 : ℝ)*base87 + (4353/6250000000000000 : ℝ)*base89 + (4353/6250000000000000 : ℝ)*base91 + hcertificate_margin
  have ratio_s0_1 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(71311/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(71311/100000 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (14315485138971173732913/1250000000000000000000000000 : ℝ) := by norm_num
    linear_combination (266896780489/1000000000000 : ℝ)*(base5) + (165564173323/200000000000 : ℝ)*(base7) + (2229/50000000000 : ℝ)*(base49) + (180635076431/1000000000000 : ℝ)*(base60) + (1897709631731/1000000000000 : ℝ)*(major_s0_0) + (1897709631731/1000000000000 : ℝ)*(major_s0_1) + (1897709631731/1000000000000 : ℝ)*(major_s0_2) + (936839/100000000000 : ℝ)*(sp_s0_0) + (53512241/1000000000000 : ℝ)*(sp_s0_7) + (1132318026909/500000000000 : ℝ)*(sp_s0_14) + (566167225483/250000000000 : ℝ)*(sp_s0_15) + (1265797857469/500000000000 : ℝ)*(sp_s0_16) + (808008059379/500000000000 : ℝ)*(sp_s0_20) + (30032517/1000000000000 : ℝ)*(sp_s0_22) + (1055092032631/1000000000000 : ℝ)*(f.failure) + (2264698934449/1000000000000 : ℝ)*(f.sum) + (4981963/20000000000000000000 : ℝ)*base62 + (4956267784718403/10000000000000000000000000000 : ℝ)*base65 + (9548733887281597/10000000000000000000000000000 : ℝ)*base67 + (1880191296862287/10000000000000000000000000000 : ℝ)*base69 + (142821049214029/2500000000000000000000000000 : ℝ)*base71 + (7589116628718403/10000000000000000000000000000 : ℝ)*base73 + (1686420460137713/10000000000000000000000000000 : ℝ)*base75 + (2616782084137713/10000000000000000000000000000 : ℝ)*base77 + (1800732849/5000000000000000000000 : ℝ)*base79 + (11539/50000000000000000 : ℝ)*base86 + (11539/50000000000000000 : ℝ)*base88 + (11539/50000000000000000 : ℝ)*base90 + (1/1000000000000 : ℝ)*base93 + hcertificate_margin
  have ratio_s0_2 : (0 : ℝ) ≤ ((1 : ℝ)*X 0 0+(16407/50000 : ℝ)*X 0 2+(1 : ℝ)*X 1 0+(16407/50000 : ℝ)*X 1 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (1581519122618098145307/250000000000000000000000000 : ℝ) := by norm_num
    linear_combination (21429773969/200000000000 : ℝ)*(base5) + (162801172467/1000000000000 : ℝ)*(base7) + (537799246327/1000000000000 : ℝ)*(base39) + (1073031/500000000000 : ℝ)*(base44) + (34464639013/62500000000 : ℝ)*(base49) + (848219980563/500000000000 : ℝ)*(major_s0_0) + (212054726883/125000000000 : ℝ)*(major_s0_1) + (848219980563/500000000000 : ℝ)*(major_s0_2) + (22461311/1000000000000 : ℝ)*(sp_s0_1) + (13383901/1000000000000 : ℝ)*(sp_s0_16) + (2356150642693/1000000000000 : ℝ)*(sp_s0_21) + (2356126035321/1000000000000 : ℝ)*(sp_s0_22) + (1231643064319/500000000000 : ℝ)*(sp_s0_23) + (998839913777/1000000000000 : ℝ)*(sp_s0_27) + (943189757217/1000000000000 : ℝ)*(f.failure) + (2356150642693/1000000000000 : ℝ)*(f.sum) + (1136593403457613/5000000000000000000000000000 : ℝ)*base62 + (1299865414941981/5000000000000000000000000000 : ℝ)*base64 + (649612543883179/1250000000000000000000000000 : ℝ)*base66 + (2016162300209649/5000000000000000000000000000 : ℝ)*base68 + (34856984566917/1250000000000000000000000000 : ℝ)*base71 + (6933775776941981/5000000000000000000000000000 : ℝ)*base72 + (1092004019686991/1250000000000000000000000000 : ℝ)*base74 + (3502230084290351/5000000000000000000000000000 : ℝ)*base76 + (3627274839974697/5000000000000000000000000000 : ℝ)*base78 + (1/1000000000000 : ℝ)*base83 + (1/1000000000000 : ℝ)*base85 + (17973/50000000000000000 : ℝ)*base86 + (17973/50000000000000000 : ℝ)*base88 + (17973/50000000000000000 : ℝ)*base90 + hcertificate_margin
  have s1_pow0 : (3601/5000 : ℝ) ^ (77/16 : ℝ) ≤ (2060597296669280281/10000000000000000000 : ℝ) := by
    have hpowers : (3601/5000 : ℝ)^77 ≤ (2060597296669280281/10000000000000000000 : ℝ)^16 := by
      have hnat : (3601 : ℕ)^77*10000000000000000000^16 ≤ 2060597296669280281^16*5000^77 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3601 5000 2060597296669280281 10000000000000000000 77 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (3601/5000 : ℝ)) (X := (2060597296669280281/10000000000000000000 : ℝ)) (by norm_num) (by norm_num) 77 16 (by norm_num) hpowers
    exact h
  have s1_corner0a : (12060597296669280281/10000000000000000000 : ℝ) ≤ (10396994304134943/10000000000000000 : ℝ) ^ (77/16 : ℝ) := by
    have hpowers : (12060597296669280281/10000000000000000000 : ℝ)^16 ≤ (10396994304134943/10000000000000000 : ℝ)^77 := by
      have hnat : (12060597296669280281 : ℕ)^16*10000000000000000^77 ≤ 10396994304134943^77*10000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12060597296669280281 10000000000000000000 10396994304134943 10000000000000000 16 77 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10396994304134943/10000000000000000 : ℝ)) (X := (12060597296669280281/10000000000000000000 : ℝ)) (by norm_num) 77 16 (by norm_num) hpowers
    exact h
  have s1_corner0b : (7060597296669280281/5000000000000000000 : ℝ) ≤ (10743409182092739/10000000000000000 : ℝ) ^ (77/16 : ℝ) := by
    have hpowers : (7060597296669280281/5000000000000000000 : ℝ)^16 ≤ (10743409182092739/10000000000000000 : ℝ)^77 := by
      have hnat : (7060597296669280281 : ℕ)^16*10000000000000000^77 ≤ 10743409182092739^77*5000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        7060597296669280281 5000000000000000000 10743409182092739 10000000000000000 16 77 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10743409182092739/10000000000000000 : ℝ)) (X := (7060597296669280281/5000000000000000000 : ℝ)) (by norm_num) 77 16 (by norm_num) hpowers
    exact h
  have major_s1_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(396994304134943/7202000000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(86603719489449/1800500000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (77/16 : ℝ)) (rho := (3601/5000 : ℝ)) (alpha := (396994304134943/7202000000000000 : ℝ)) (beta := (86603719489449/1800500000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow0,s1_corner0a]) (by linarith only [s1_pow0,s1_corner0b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![false, true, true]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (3601/5000 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_0])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(396994304134943/7202000000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(86603719489449/1800500000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s1_pow1 : (71311/100000 : ℝ) ^ (77/16 : ℝ) ≤ (9823941977952038999/50000000000000000000 : ℝ) := by
    have hpowers : (71311/100000 : ℝ)^77 ≤ (9823941977952038999/50000000000000000000 : ℝ)^16 := by
      have hnat : (71311 : ℕ)^77*50000000000000000000^16 ≤ 9823941977952038999^16*100000^77 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        71311 100000 9823941977952038999 50000000000000000000 77 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (71311/100000 : ℝ)) (X := (9823941977952038999/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 77 16 (by norm_num) hpowers
    exact h
  have s1_corner1a : (59823941977952038999/50000000000000000000 : ℝ) ≤ (2075955559558979/2000000000000000 : ℝ) ^ (77/16 : ℝ) := by
    have hpowers : (59823941977952038999/50000000000000000000 : ℝ)^16 ≤ (2075955559558979/2000000000000000 : ℝ)^77 := by
      have hnat : (59823941977952038999 : ℕ)^16*2000000000000000^77 ≤ 2075955559558979^77*50000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        59823941977952038999 50000000000000000000 2075955559558979 2000000000000000 16 77 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2075955559558979/2000000000000000 : ℝ)) (X := (59823941977952038999/50000000000000000000 : ℝ)) (by norm_num) 77 16 (by norm_num) hpowers
    exact h
  have s1_corner1b : (34823941977952038999/25000000000000000000 : ℝ) ≤ (2678238120478631/2500000000000000 : ℝ) ^ (77/16 : ℝ) := by
    have hpowers : (34823941977952038999/25000000000000000000 : ℝ)^16 ≤ (2678238120478631/2500000000000000 : ℝ)^77 := by
      have hnat : (34823941977952038999 : ℕ)^16*2500000000000000^77 ≤ 2678238120478631^77*25000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        34823941977952038999 25000000000000000000 2678238120478631 2500000000000000 16 77 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2678238120478631/2500000000000000 : ℝ)) (X := (34823941977952038999/25000000000000000000 : ℝ)) (by norm_num) 77 16 (by norm_num) hpowers
    exact h
  have major_s1_1 : P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1))+(75955559558979/1426220000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 2 0))+(333174684119629/7131100000000000 : ℝ)*((-1 : ℝ)*(X 0 2+X 2 2)) := by
    have hh := chart_majorant (a := (77/16 : ℝ)) (rho := (71311/100000 : ℝ)) (alpha := (75955559558979/1426220000000000 : ℝ)) (beta := (333174684119629/7131100000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow1,s1_corner1a]) (by linarith only [s1_pow1,s1_corner1b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![false, true, true]] hX 1 (by
        change ((1 : ℝ)*pair X 1 0) ≤ (71311/100000 : ℝ)*((1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_1])
    change lpNorm p (pair X 1) ≤ ((1 : ℝ)*pair X 1 1)+(75955559558979/1426220000000000 : ℝ)*((1 : ℝ)*pair X 1 0)+(333174684119629/7131100000000000 : ℝ)*((-1 : ℝ)*pair X 1 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s1_pow2 : (16407/50000 : ℝ) ^ (77/16 : ℝ) ≤ (93770184253704599/20000000000000000000 : ℝ) := by
    have hpowers : (16407/50000 : ℝ)^77 ≤ (93770184253704599/20000000000000000000 : ℝ)^16 := by
      have hnat : (16407 : ℕ)^77*20000000000000000000^16 ≤ 93770184253704599^16*50000^77 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        16407 50000 93770184253704599 20000000000000000000 77 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (16407/50000 : ℝ)) (X := (93770184253704599/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 77 16 (by norm_num) hpowers
    exact h
  have s1_corner2a : (20093770184253704599/20000000000000000000 : ℝ) ≤ (10009724314428171/10000000000000000 : ℝ) ^ (77/16 : ℝ) := by
    have hpowers : (20093770184253704599/20000000000000000000 : ℝ)^16 ≤ (10009724314428171/10000000000000000 : ℝ)^77 := by
      have hnat : (20093770184253704599 : ℕ)^16*10000000000000000^77 ≤ 10009724314428171^77*20000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        20093770184253704599 20000000000000000000 10009724314428171 10000000000000000 16 77 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10009724314428171/10000000000000000 : ℝ)) (X := (20093770184253704599/20000000000000000000 : ℝ)) (by norm_num) 77 16 (by norm_num) hpowers
    exact h
  have s1_corner2b : (10093770184253704599/10000000000000000000 : ℝ) ≤ (5009706372417559/5000000000000000 : ℝ) ^ (77/16 : ℝ) := by
    have hpowers : (10093770184253704599/10000000000000000000 : ℝ)^16 ≤ (5009706372417559/5000000000000000 : ℝ)^77 := by
      have hnat : (10093770184253704599 : ℕ)^16*5000000000000000^77 ≤ 5009706372417559^77*10000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10093770184253704599 10000000000000000000 5009706372417559 5000000000000000 16 77 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5009706372417559/5000000000000000 : ℝ)) (X := (10093770184253704599/10000000000000000000 : ℝ)) (by norm_num) 77 16 (by norm_num) hpowers
    exact h
  have major_s1_2 : P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2))+(9724314428171/3281400000000000 : ℝ)*((-1 : ℝ)*(X 0 0+X 1 0))+(9688430406947/3281400000000000 : ℝ)*((1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (77/16 : ℝ)) (rho := (16407/50000 : ℝ)) (alpha := (9724314428171/3281400000000000 : ℝ)) (beta := (9688430406947/3281400000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow2,s1_corner2a]) (by linarith only [s1_pow2,s1_corner2b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![false, true, true]] hX 2 (by
        change ((-1 : ℝ)*pair X 2 0) ≤ (16407/50000 : ℝ)*((1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_2])
    change lpNorm p (pair X 2) ≤ ((1 : ℝ)*pair X 2 2)+(9724314428171/3281400000000000 : ℝ)*((-1 : ℝ)*pair X 2 0)+(9688430406947/3281400000000000 : ℝ)*((1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s1_0 : ((-729901771/2000000000 : ℝ)*X 0 0+(1821157423/5000000000 : ℝ)*X 0 1+(2577468507/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c317051_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_1 : ((2908622023/10000000000 : ℝ)*X 1 0+(-290288847/1000000000 : ℝ)*X 1 1+(6435571579/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c317051_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_2 : ((2670804927/5000000000 : ℝ)*X 2 0+(267553731/500000000 : ℝ)*X 2 1+(-1438914439/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c317051_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_6 : ((507448627/1000000000 : ℝ)*X 0 0+(5083477721/10000000000 : ℝ)*X 0 1+(2141242149/10000000000 : ℝ)*X 0 2+(507448627/1000000000 : ℝ)*X 1 0+(5083477721/10000000000 : ℝ)*X 1 1+(2141242149/10000000000 : ℝ)*X 1 2+(507448627/1000000000 : ℝ)*X 2 0+(5083477721/10000000000 : ℝ)*X 2 1+(2141242149/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c317051_s1_6 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have hsep : (-194793/25000 : ℝ) < ((-89931/50000 : ℝ)*P 0+(-89931/50000 : ℝ)*P 1+(-89931/50000 : ℝ)*P 2+(1 : ℝ)*T) := by
    have hcertificate_margin : (-194793/25000 : ℝ) < (-2279078346207757340192834950314971/292581144220625000000000000000000 : ℝ) := by norm_num
    linear_combination (27227/500000000000 : ℝ)*(base19) + (23329/1000000000000 : ℝ)*(base21) + (21453/1000000000000 : ℝ)*(base40) + (161972087049/1000000000000 : ℝ)*(base49) + (17111/200000000000 : ℝ)*(base53) + (180763335359/1000000000000 : ℝ)*(base59) + (530611751917/1000000000000 : ℝ)*(base60) + (89931/50000 : ℝ)*(major_s1_0) + (89931/50000 : ℝ)*(major_s1_1) + (359723982889/200000000000 : ℝ)*(major_s1_2) + (2596519875089/1000000000000 : ℝ)*(sp_s1_0) + (1298259909471/500000000000 : ℝ)*(sp_s1_1) + (519303987463/200000000000 : ℝ)*(sp_s1_2) + (1000000001693/1000000000000 : ℝ)*(sp_s1_6) + (649129990161/250000000000 : ℝ)*(f.sum) + (34987047270111691529/46799983080000000000000000000000 : ℝ)*base62 + (729535964075833/656280000000000000000000000 : ℝ)*base64 + (135617378091433/713110000000000000000000000 : ℝ)*base66 + (443513805285347/656280000000000000000000000 : ℝ)*base68 + (3532157390230816081/2363264280000000000000000000000 : ℝ)*base70 + (1014971838493/1440400000000000000000000 : ℝ)*base73 + (285533780913/1114234375000000000000000 : ℝ)*base74 + (15825538957753/36010000000000000000000000 : ℝ)*base76 + (32081388543802127/641977277500000000000000000000 : ℝ)*base79 + (1693/1000000000000 : ℝ)*base82 + (1693/1000000000000 : ℝ)*base93 + hcertificate_margin
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
theorem coarse_distinct_p017_b025 (p : ℝ) (hpa : (77/16 : ℝ) ≤ p) (hpb : p ≤ (39/8 : ℝ))
    (c : Fin 88) (hlo : 51 ≤ c.val) (hhi : c.val < 56)
    (hn63 : c ≠ 63) (hn87 : c ≠ 87)
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (89931/50000 : ℝ) (34473/20000 : ℝ) (19897/25000 : ℝ) X (distinctOrders c) (distinctSigns c)) : False := by
  have hc : c=51 ∨ c=52 ∨ c=53 ∨ c=54 ∨ c=55 := by omega
  rcases hc with rfl|rfl|rfl|rfl|rfl
  · exact collision_c317051 p hpa (by linarith only [hpb]) X hX
  · exact collision_c316052 p (by linarith only [hpa]) (by linarith only [hpb]) X (orderedChart_weaken
      (by linarith only [hpa]) hX (by norm_num) (by norm_num) (by norm_num))
  · exact collision_c316053 p (by linarith only [hpa]) (by linarith only [hpb]) X (orderedChart_weaken
      (by linarith only [hpa]) hX (by norm_num) (by norm_num) (by norm_num))
  · exact collision_c317054 p hpa (by linarith only [hpb]) X hX
  · exact collision_c317055 p hpa (by linarith only [hpb]) X hX

end HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p : ℝ) (hpa : (77/16 : ℝ) ≤ p) (hpb : p ≤ (39/8 : ℝ))
    (c : Fin 88) (hlo : 51 ≤ c.val) (hhi : c.val < 56)
    (hn63 : c ≠ 63) (hn87 : c ≠ 87)
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (89931/50000 : ℝ) (34473/20000 : ℝ) (19897/25000 : ℝ) X (distinctOrders c) (distinctSigns c)) : False := by
  exact HlawkaSchatten.DiagonalCutoff4.coarse_distinct_p017_b025 p hpa hpb c hlo hhi hn63 hn87 X hX

#print axioms solution
