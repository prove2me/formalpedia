-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.coarse_distinct_p014_b024
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T00:40:28.053643+00:00
-- url     : https://prove2.me/submissions/90f9aef7-5348-4b97-bb41-34c77fdce814

import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_collision_c314048_s0
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_collision_c314048_s1
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_collision_c314048_s2
import Definitions.Def_HlawkaSchatten_DiagonalCutoff4_Localization
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_collision_c314049_s0
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_collision_c314049_s1
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_collision_c314049_s2
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_collision_c314050_s0
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_collision_c314050_s1
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_collision_c314050_s2
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_collision_c314051_s0
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_collision_c314051_s1
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_collision_c314051_s2
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_collision_c314052_s0
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_collision_c314052_s1
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_collision_c314052_s2
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_collision_c314053_s0
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_collision_c314053_s1
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_collision_c314053_s2
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_collision_c314053_s3
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_collision_c314054_s0
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_collision_c314054_s1
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_collision_c314054_s2
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_collision_c314054_s3
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
theorem HlawkaSchatten.DiagonalCutoff4.collision_c314048 (p : ℝ) (hpa : (37/8 : ℝ) ≤ p) (hpb : p ≤ (19/4 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (172069/100000 : ℝ) (87867/50000 : ℝ) (15771/20000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![false, false, false]]) : False := by
  have h0 := collision_c314048_s0 p hpa hpb X hX
  have h1 := collision_c314048_s1 p hpa hpb X hX h0
  exact collision_c314048_s2 p hpa hpb X hX h1

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6 HlawkaSchatten.DiagonalCutoff4
theorem HlawkaSchatten.DiagonalCutoff4.collision_c314049 (p : ℝ) (hpa : (37/8 : ℝ) ≤ p) (hpb : p ≤ (19/4 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (172069/100000 : ℝ) (87867/50000 : ℝ) (15771/20000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![false, false, true]]) : False := by
  have h0 := collision_c314049_s0 p hpa hpb X hX
  have h1 := collision_c314049_s1 p hpa hpb X hX h0
  exact collision_c314049_s2 p hpa hpb X hX h1

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6 HlawkaSchatten.DiagonalCutoff4
theorem HlawkaSchatten.DiagonalCutoff4.collision_c314050 (p : ℝ) (hpa : (37/8 : ℝ) ≤ p) (hpb : p ≤ (19/4 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (172069/100000 : ℝ) (87867/50000 : ℝ) (15771/20000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![false, true, false]]) : False := by
  have h0 := collision_c314050_s0 p hpa hpb X hX
  have h1 := collision_c314050_s1 p hpa hpb X hX h0
  exact collision_c314050_s2 p hpa hpb X hX h1

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6 HlawkaSchatten.DiagonalCutoff4
theorem HlawkaSchatten.DiagonalCutoff4.collision_c314051 (p : ℝ) (hpa : (37/8 : ℝ) ≤ p) (hpb : p ≤ (19/4 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (172069/100000 : ℝ) (87867/50000 : ℝ) (15771/20000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![false, true, true]]) : False := by
  have h0 := collision_c314051_s0 p hpa hpb X hX
  have h1 := collision_c314051_s1 p hpa hpb X hX h0
  exact collision_c314051_s2 p hpa hpb X hX h1

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6 HlawkaSchatten.DiagonalCutoff4
theorem HlawkaSchatten.DiagonalCutoff4.collision_c314052 (p : ℝ) (hpa : (37/8 : ℝ) ≤ p) (hpb : p ≤ (19/4 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (172069/100000 : ℝ) (87867/50000 : ℝ) (15771/20000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![true, false, false]]) : False := by
  have h0 := collision_c314052_s0 p hpa hpb X hX
  have h1 := collision_c314052_s1 p hpa hpb X hX h0
  exact collision_c314052_s2 p hpa hpb X hX h1

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6 HlawkaSchatten.DiagonalCutoff4
theorem HlawkaSchatten.DiagonalCutoff4.collision_c314053 (p : ℝ) (hpa : (37/8 : ℝ) ≤ p) (hpb : p ≤ (75/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (172069/100000 : ℝ) (87867/50000 : ℝ) (15771/20000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![true, false, true]]) : False := by
  have h0 := collision_c314053_s0 p hpa hpb X hX
  have h1 := collision_c314053_s1 p hpa hpb X hX h0
  have h2 := collision_c314053_s2 p hpa hpb X hX h1
  exact collision_c314053_s3 p hpa hpb X hX h2

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6 HlawkaSchatten.DiagonalCutoff4
theorem HlawkaSchatten.DiagonalCutoff4.collision_c314054 (p : ℝ) (hpa : (37/8 : ℝ) ≤ p) (hpb : p ≤ (75/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (172069/100000 : ℝ) (87867/50000 : ℝ) (15771/20000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![true, true, false]]) : False := by
  have h0 := collision_c314054_s0 p hpa hpb X hX
  have h1 := collision_c314054_s1 p hpa hpb X hX h0
  have h2 := collision_c314054_s2 p hpa hpb X hX h1
  exact collision_c314054_s3 p hpa hpb X hX h2

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
theorem collision_support_c314047_s0_0 (p : ℝ) (hpa : (37/8 : ℝ) ≤ p) (hpb : p ≤ (19/4 : ℝ)) (x : Fin 3 → ℝ) :
    (-355341/10000000 : ℝ)*x 0 + (-6264960709/10000000000 : ℝ)*x 1 + (1031663883/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (355341/10000000 : ℝ)^19 ≤ (1459320686823/100000000000000 : ℝ)^15 := by
    have hnat : (355341 : ℕ)^19*100000000000000^15 ≤ 1459320686823^15*10000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      355341 10000000 1459320686823 100000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (6264960709/10000000000 : ℝ)^19 ≤ (11060970678951/20000000000000 : ℝ)^15 := by
    have hnat : (6264960709 : ℕ)^19*20000000000000^15 ≤ 11060970678951^15*10000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6264960709 10000000000 11060970678951 20000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1031663883/2000000000 : ℝ)^19 ≤ (5404478238453/12500000000000 : ℝ)^15 := by
    have hnat : (1031663883 : ℕ)^19*12500000000000^15 ≤ 5404478238453^15*2000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1031663883 2000000000 5404478238453 12500000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (19/4 : ℝ)) 19 15 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-355341/10000000 : ℝ), (-6264960709/10000000000 : ℝ), (1031663883/2000000000 : ℝ)] ![(1459320686823/100000000000000 : ℝ), (11060970678951/20000000000000 : ℝ), (5404478238453/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-355341/10000000 : ℝ)|^19 ≤ (1459320686823/100000000000000 : ℝ)^15
        have hw : |(-355341/10000000 : ℝ)|=(355341/10000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-6264960709/10000000000 : ℝ)|^19 ≤ (11060970678951/20000000000000 : ℝ)^15
        have hw : |(-6264960709/10000000000 : ℝ)|=(6264960709/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1031663883/2000000000 : ℝ)|^19 ≤ (5404478238453/12500000000000 : ℝ)^15
        have hw : |(1031663883/2000000000 : ℝ)|=(1031663883/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c314047_s0_1 (p : ℝ) (hpa : (37/8 : ℝ) ≤ p) (hpb : p ≤ (19/4 : ℝ)) (x : Fin 3 → ℝ) :
    (2562822483/5000000000 : ℝ)*x 0 + (1933807793/5000000000 : ℝ)*x 1 + (222890853/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2562822483/5000000000 : ℝ)^19 ≤ (5361152234383/12500000000000 : ℝ)^15 := by
    have hnat : (2562822483 : ℕ)^19*12500000000000^15 ≤ 5361152234383^15*5000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2562822483 5000000000 5361152234383 12500000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1933807793/5000000000 : ℝ)^19 ≤ (30021209291029/100000000000000 : ℝ)^15 := by
    have hnat : (1933807793 : ℕ)^19*100000000000000^15 ≤ 30021209291029^15*5000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1933807793 5000000000 30021209291029 100000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (222890853/625000000 : ℝ)^19 ≤ (27089572820033/100000000000000 : ℝ)^15 := by
    have hnat : (222890853 : ℕ)^19*100000000000000^15 ≤ 27089572820033^15*625000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      222890853 625000000 27089572820033 100000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (19/4 : ℝ)) 19 15 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2562822483/5000000000 : ℝ), (1933807793/5000000000 : ℝ), (222890853/625000000 : ℝ)] ![(5361152234383/12500000000000 : ℝ), (30021209291029/100000000000000 : ℝ), (27089572820033/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2562822483/5000000000 : ℝ)|^19 ≤ (5361152234383/12500000000000 : ℝ)^15
        have hw : |(2562822483/5000000000 : ℝ)|=(2562822483/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1933807793/5000000000 : ℝ)|^19 ≤ (30021209291029/100000000000000 : ℝ)^15
        have hw : |(1933807793/5000000000 : ℝ)|=(1933807793/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(222890853/625000000 : ℝ)|^19 ≤ (27089572820033/100000000000000 : ℝ)^15
        have hw : |(222890853/625000000 : ℝ)|=(222890853/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c314047_s0_2 (p : ℝ) (hpa : (37/8 : ℝ) ≤ p) (hpb : p ≤ (19/4 : ℝ)) (x : Fin 3 → ℝ) :
    (2760944119/5000000000 : ℝ)*x 0 + (-1944678851/5000000000 : ℝ)*x 1 + (-618901877/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2760944119/5000000000 : ℝ)^19 ≤ (47131468948567/100000000000000 : ℝ)^15 := by
    have hnat : (2760944119 : ℕ)^19*100000000000000^15 ≤ 47131468948567^15*5000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2760944119 5000000000 47131468948567 100000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1944678851/5000000000 : ℝ)^19 ≤ (6047028084281/20000000000000 : ℝ)^15 := by
    have hnat : (1944678851 : ℕ)^19*20000000000000^15 ≤ 6047028084281^15*5000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1944678851 5000000000 6047028084281 20000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (618901877/2000000000 : ℝ)^19 ≤ (22633390609847/100000000000000 : ℝ)^15 := by
    have hnat : (618901877 : ℕ)^19*100000000000000^15 ≤ 22633390609847^15*2000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      618901877 2000000000 22633390609847 100000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (19/4 : ℝ)) 19 15 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2760944119/5000000000 : ℝ), (-1944678851/5000000000 : ℝ), (-618901877/2000000000 : ℝ)] ![(47131468948567/100000000000000 : ℝ), (6047028084281/20000000000000 : ℝ), (22633390609847/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2760944119/5000000000 : ℝ)|^19 ≤ (47131468948567/100000000000000 : ℝ)^15
        have hw : |(2760944119/5000000000 : ℝ)|=(2760944119/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1944678851/5000000000 : ℝ)|^19 ≤ (6047028084281/20000000000000 : ℝ)^15
        have hw : |(-1944678851/5000000000 : ℝ)|=(1944678851/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-618901877/2000000000 : ℝ)|^19 ≤ (22633390609847/100000000000000 : ℝ)^15
        have hw : |(-618901877/2000000000 : ℝ)|=(618901877/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c314047_s0_6 (p : ℝ) (hpa : (37/8 : ℝ) ≤ p) (hpb : p ≤ (19/4 : ℝ)) (x : Fin 3 → ℝ) :
    (333409703/500000000 : ℝ)*x 0 + (965243/10000000000 : ℝ)*x 1 + (30407307/62500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (333409703/500000000 : ℝ)^19 ≤ (59851782870749/100000000000000 : ℝ)^15 := by
    have hnat : (333409703 : ℕ)^19*100000000000000^15 ≤ 59851782870749^15*500000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      333409703 500000000 59851782870749 100000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (965243/10000000000 : ℝ)^19 ≤ (410055941/50000000000000 : ℝ)^15 := by
    have hnat : (965243 : ℕ)^19*50000000000000^15 ≤ 410055941^15*10000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      965243 10000000000 410055941 50000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (30407307/62500000 : ℝ)^19 ≤ (802947940087/2000000000000 : ℝ)^15 := by
    have hnat : (30407307 : ℕ)^19*2000000000000^15 ≤ 802947940087^15*62500000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      30407307 62500000 802947940087 2000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (19/4 : ℝ)) 19 15 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(333409703/500000000 : ℝ), (965243/10000000000 : ℝ), (30407307/62500000 : ℝ)] ![(59851782870749/100000000000000 : ℝ), (410055941/50000000000000 : ℝ), (802947940087/2000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(333409703/500000000 : ℝ)|^19 ≤ (59851782870749/100000000000000 : ℝ)^15
        have hw : |(333409703/500000000 : ℝ)|=(333409703/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(965243/10000000000 : ℝ)|^19 ≤ (410055941/50000000000000 : ℝ)^15
        have hw : |(965243/10000000000 : ℝ)|=(965243/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(30407307/62500000 : ℝ)|^19 ≤ (802947940087/2000000000000 : ℝ)^15
        have hw : |(30407307/62500000 : ℝ)|=(30407307/62500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c314047_s0_7 (p : ℝ) (hpa : (37/8 : ℝ) ≤ p) (hpb : p ≤ (19/4 : ℝ)) (x : Fin 3 → ℝ) :
    (-45183161/10000000000 : ℝ)*x 0 + (-7979750143/10000000000 : ℝ)*x 1 + (415181149/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (45183161/10000000000 : ℝ)^19 ≤ (107062416179/100000000000000 : ℝ)^15 := by
    have hnat : (45183161 : ℕ)^19*100000000000000^15 ≤ 107062416179^15*10000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      45183161 10000000000 107062416179 100000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (7979750143/10000000000 : ℝ)^19 ≤ (37568435446427/50000000000000 : ℝ)^15 := by
    have hnat : (7979750143 : ℕ)^19*50000000000000^15 ≤ 37568435446427^15*10000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7979750143 10000000000 37568435446427 50000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (415181149/1250000000 : ℝ)^19 ≤ (12378033337739/50000000000000 : ℝ)^15 := by
    have hnat : (415181149 : ℕ)^19*50000000000000^15 ≤ 12378033337739^15*1250000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      415181149 1250000000 12378033337739 50000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (19/4 : ℝ)) 19 15 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-45183161/10000000000 : ℝ), (-7979750143/10000000000 : ℝ), (415181149/1250000000 : ℝ)] ![(107062416179/100000000000000 : ℝ), (37568435446427/50000000000000 : ℝ), (12378033337739/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-45183161/10000000000 : ℝ)|^19 ≤ (107062416179/100000000000000 : ℝ)^15
        have hw : |(-45183161/10000000000 : ℝ)|=(45183161/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-7979750143/10000000000 : ℝ)|^19 ≤ (37568435446427/50000000000000 : ℝ)^15
        have hw : |(-7979750143/10000000000 : ℝ)|=(7979750143/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(415181149/1250000000 : ℝ)|^19 ≤ (12378033337739/50000000000000 : ℝ)^15
        have hw : |(415181149/1250000000 : ℝ)|=(415181149/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c314047_s0_8 (p : ℝ) (hpa : (37/8 : ℝ) ≤ p) (hpb : p ≤ (19/4 : ℝ)) (x : Fin 3 → ℝ) :
    (2930812617/10000000000 : ℝ)*x 0 + (5611613289/10000000000 : ℝ)*x 1 + (1971722311/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2930812617/10000000000 : ℝ)^19 ≤ (21127666511233/100000000000000 : ℝ)^15 := by
    have hnat : (2930812617 : ℕ)^19*100000000000000^15 ≤ 21127666511233^15*10000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2930812617 10000000000 21127666511233 100000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5611613289/10000000000 : ℝ)^19 ≤ (48103624163907/100000000000000 : ℝ)^15 := by
    have hnat : (5611613289 : ℕ)^19*100000000000000^15 ≤ 48103624163907^15*10000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5611613289 10000000000 48103624163907 100000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1971722311/5000000000 : ℝ)^19 ≤ (30768709307753/100000000000000 : ℝ)^15 := by
    have hnat : (1971722311 : ℕ)^19*100000000000000^15 ≤ 30768709307753^15*5000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1971722311 5000000000 30768709307753 100000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (19/4 : ℝ)) 19 15 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2930812617/10000000000 : ℝ), (5611613289/10000000000 : ℝ), (1971722311/5000000000 : ℝ)] ![(21127666511233/100000000000000 : ℝ), (48103624163907/100000000000000 : ℝ), (30768709307753/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2930812617/10000000000 : ℝ)|^19 ≤ (21127666511233/100000000000000 : ℝ)^15
        have hw : |(2930812617/10000000000 : ℝ)|=(2930812617/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5611613289/10000000000 : ℝ)|^19 ≤ (48103624163907/100000000000000 : ℝ)^15
        have hw : |(5611613289/10000000000 : ℝ)|=(5611613289/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1971722311/5000000000 : ℝ)|^19 ≤ (30768709307753/100000000000000 : ℝ)^15
        have hw : |(1971722311/5000000000 : ℝ)|=(1971722311/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c314047_s0_9 (p : ℝ) (hpa : (37/8 : ℝ) ≤ p) (hpb : p ≤ (19/4 : ℝ)) (x : Fin 3 → ℝ) :
    (2271540303/5000000000 : ℝ)*x 0 + (-1705566823/5000000000 : ℝ)*x 1 + (-4618160561/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2271540303/5000000000 : ℝ)^19 ≤ (9202741766943/25000000000000 : ℝ)^15 := by
    have hnat : (2271540303 : ℕ)^19*25000000000000^15 ≤ 9202741766943^15*5000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2271540303 5000000000 9202741766943 25000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1705566823/5000000000 : ℝ)^19 ≤ (12802901438709/50000000000000 : ℝ)^15 := by
    have hnat : (1705566823 : ℕ)^19*50000000000000^15 ≤ 12802901438709^15*5000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1705566823 5000000000 12802901438709 50000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4618160561/10000000000 : ℝ)^19 ≤ (37583230042499/100000000000000 : ℝ)^15 := by
    have hnat : (4618160561 : ℕ)^19*100000000000000^15 ≤ 37583230042499^15*10000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4618160561 10000000000 37583230042499 100000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (19/4 : ℝ)) 19 15 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2271540303/5000000000 : ℝ), (-1705566823/5000000000 : ℝ), (-4618160561/10000000000 : ℝ)] ![(9202741766943/25000000000000 : ℝ), (12802901438709/50000000000000 : ℝ), (37583230042499/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2271540303/5000000000 : ℝ)|^19 ≤ (9202741766943/25000000000000 : ℝ)^15
        have hw : |(2271540303/5000000000 : ℝ)|=(2271540303/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1705566823/5000000000 : ℝ)|^19 ≤ (12802901438709/50000000000000 : ℝ)^15
        have hw : |(-1705566823/5000000000 : ℝ)|=(1705566823/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-4618160561/10000000000 : ℝ)|^19 ≤ (37583230042499/100000000000000 : ℝ)^15
        have hw : |(-4618160561/10000000000 : ℝ)|=(4618160561/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c314047_s0_13 (p : ℝ) (hpa : (37/8 : ℝ) ≤ p) (hpb : p ≤ (19/4 : ℝ)) (x : Fin 3 → ℝ) :
    (2513262303/5000000000 : ℝ)*x 0 + (9821911/2000000000 : ℝ)*x 1 + (6508290511/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2513262303/5000000000 : ℝ)^19 ≤ (41841370021929/100000000000000 : ℝ)^15 := by
    have hnat : (2513262303 : ℕ)^19*100000000000000^15 ≤ 41841370021929^15*5000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2513262303 5000000000 41841370021929 100000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (9821911/2000000000 : ℝ)^19 ≤ (29745203231/25000000000000 : ℝ)^15 := by
    have hnat : (9821911 : ℕ)^19*25000000000000^15 ≤ 29745203231^15*2000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      9821911 2000000000 29745203231 25000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (6508290511/10000000000 : ℝ)^19 ≤ (29019824572071/50000000000000 : ℝ)^15 := by
    have hnat : (6508290511 : ℕ)^19*50000000000000^15 ≤ 29019824572071^15*10000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6508290511 10000000000 29019824572071 50000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (19/4 : ℝ)) 19 15 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2513262303/5000000000 : ℝ), (9821911/2000000000 : ℝ), (6508290511/10000000000 : ℝ)] ![(41841370021929/100000000000000 : ℝ), (29745203231/25000000000000 : ℝ), (29019824572071/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2513262303/5000000000 : ℝ)|^19 ≤ (41841370021929/100000000000000 : ℝ)^15
        have hw : |(2513262303/5000000000 : ℝ)|=(2513262303/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(9821911/2000000000 : ℝ)|^19 ≤ (29745203231/25000000000000 : ℝ)^15
        have hw : |(9821911/2000000000 : ℝ)|=(9821911/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(6508290511/10000000000 : ℝ)|^19 ≤ (29019824572071/50000000000000 : ℝ)^15
        have hw : |(6508290511/10000000000 : ℝ)|=(6508290511/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c314047_s0_14 (p : ℝ) (hpa : (37/8 : ℝ) ≤ p) (hpb : p ≤ (19/4 : ℝ)) (x : Fin 3 → ℝ) :
    (2691201/10000000000 : ℝ)*x 0 + (-915509733/2000000000 : ℝ)*x 1 + (3464484679/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2691201/10000000000 : ℝ)^19 ≤ (3005604081/100000000000000 : ℝ)^15 := by
    have hnat : (2691201 : ℕ)^19*100000000000000^15 ≤ 3005604081^15*10000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2691201 10000000000 3005604081 100000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (915509733/2000000000 : ℝ)^19 ≤ (37165082007381/100000000000000 : ℝ)^15 := by
    have hnat : (915509733 : ℕ)^19*100000000000000^15 ≤ 37165082007381^15*2000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      915509733 2000000000 37165082007381 100000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3464484679/5000000000 : ℝ)^19 ≤ (12566382475827/20000000000000 : ℝ)^15 := by
    have hnat : (3464484679 : ℕ)^19*20000000000000^15 ≤ 12566382475827^15*5000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3464484679 5000000000 12566382475827 20000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (19/4 : ℝ)) 19 15 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2691201/10000000000 : ℝ), (-915509733/2000000000 : ℝ), (3464484679/5000000000 : ℝ)] ![(3005604081/100000000000000 : ℝ), (37165082007381/100000000000000 : ℝ), (12566382475827/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2691201/10000000000 : ℝ)|^19 ≤ (3005604081/100000000000000 : ℝ)^15
        have hw : |(2691201/10000000000 : ℝ)|=(2691201/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-915509733/2000000000 : ℝ)|^19 ≤ (37165082007381/100000000000000 : ℝ)^15
        have hw : |(-915509733/2000000000 : ℝ)|=(915509733/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3464484679/5000000000 : ℝ)|^19 ≤ (12566382475827/20000000000000 : ℝ)^15
        have hw : |(3464484679/5000000000 : ℝ)|=(3464484679/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c314047_s0_15 (p : ℝ) (hpa : (37/8 : ℝ) ≤ p) (hpb : p ≤ (19/4 : ℝ)) (x : Fin 3 → ℝ) :
    (2905334741/10000000000 : ℝ)*x 0 + (2330705433/5000000000 : ℝ)*x 1 + (2476853713/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2905334741/10000000000 : ℝ)^19 ≤ (1305955890343/6250000000000 : ℝ)^15 := by
    have hnat : (2905334741 : ℕ)^19*6250000000000^15 ≤ 1305955890343^15*10000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2905334741 10000000000 1305955890343 6250000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2330705433/5000000000 : ℝ)^19 ≤ (38029622987031/100000000000000 : ℝ)^15 := by
    have hnat : (2330705433 : ℕ)^19*100000000000000^15 ≤ 38029622987031^15*5000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2330705433 5000000000 38029622987031 100000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2476853713/5000000000 : ℝ)^19 ≤ (41075082743379/100000000000000 : ℝ)^15 := by
    have hnat : (2476853713 : ℕ)^19*100000000000000^15 ≤ 41075082743379^15*5000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2476853713 5000000000 41075082743379 100000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (19/4 : ℝ)) 19 15 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2905334741/10000000000 : ℝ), (2330705433/5000000000 : ℝ), (2476853713/5000000000 : ℝ)] ![(1305955890343/6250000000000 : ℝ), (38029622987031/100000000000000 : ℝ), (41075082743379/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2905334741/10000000000 : ℝ)|^19 ≤ (1305955890343/6250000000000 : ℝ)^15
        have hw : |(2905334741/10000000000 : ℝ)|=(2905334741/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2330705433/5000000000 : ℝ)|^19 ≤ (38029622987031/100000000000000 : ℝ)^15
        have hw : |(2330705433/5000000000 : ℝ)|=(2330705433/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2476853713/5000000000 : ℝ)|^19 ≤ (41075082743379/100000000000000 : ℝ)^15
        have hw : |(2476853713/5000000000 : ℝ)|=(2476853713/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c314047_s0_16 (p : ℝ) (hpa : (37/8 : ℝ) ≤ p) (hpb : p ≤ (19/4 : ℝ)) (x : Fin 3 → ℝ) :
    (890351231/1250000000 : ℝ)*x 0 + (-1203505327/5000000000 : ℝ)*x 1 + (-2635606753/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (890351231/1250000000 : ℝ)^19 ≤ (65066639499401/100000000000000 : ℝ)^15 := by
    have hnat : (890351231 : ℕ)^19*100000000000000^15 ≤ 65066639499401^15*1250000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      890351231 1250000000 65066639499401 100000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1203505327/5000000000 : ℝ)^19 ≤ (16464131111553/100000000000000 : ℝ)^15 := by
    have hnat : (1203505327 : ℕ)^19*100000000000000^15 ≤ 16464131111553^15*5000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1203505327 5000000000 16464131111553 100000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2635606753/10000000000 : ℝ)^19 ≤ (9234614682633/50000000000000 : ℝ)^15 := by
    have hnat : (2635606753 : ℕ)^19*50000000000000^15 ≤ 9234614682633^15*10000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2635606753 10000000000 9234614682633 50000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (19/4 : ℝ)) 19 15 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(890351231/1250000000 : ℝ), (-1203505327/5000000000 : ℝ), (-2635606753/10000000000 : ℝ)] ![(65066639499401/100000000000000 : ℝ), (16464131111553/100000000000000 : ℝ), (9234614682633/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(890351231/1250000000 : ℝ)|^19 ≤ (65066639499401/100000000000000 : ℝ)^15
        have hw : |(890351231/1250000000 : ℝ)|=(890351231/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1203505327/5000000000 : ℝ)|^19 ≤ (16464131111553/100000000000000 : ℝ)^15
        have hw : |(-1203505327/5000000000 : ℝ)|=(1203505327/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2635606753/10000000000 : ℝ)|^19 ≤ (9234614682633/50000000000000 : ℝ)^15
        have hw : |(-2635606753/10000000000 : ℝ)|=(2635606753/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c314047_s0_20 (p : ℝ) (hpa : (37/8 : ℝ) ≤ p) (hpb : p ≤ (19/4 : ℝ)) (x : Fin 3 → ℝ) :
    (8251060537/10000000000 : ℝ)*x 0 + (-15997653/1000000000 : ℝ)*x 1 + (2925771469/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (8251060537/10000000000 : ℝ)^19 ≤ (9798412666451/12500000000000 : ℝ)^15 := by
    have hnat : (8251060537 : ℕ)^19*12500000000000^15 ≤ 9798412666451^15*10000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      8251060537 10000000000 9798412666451 12500000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (15997653/1000000000 : ℝ)^19 ≤ (13276327399/2500000000000 : ℝ)^15 := by
    have hnat : (15997653 : ℕ)^19*2500000000000^15 ≤ 13276327399^15*1000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      15997653 1000000000 13276327399 2500000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2925771469/10000000000 : ℝ)^19 ≤ (164700355917/781250000000 : ℝ)^15 := by
    have hnat : (2925771469 : ℕ)^19*781250000000^15 ≤ 164700355917^15*10000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2925771469 10000000000 164700355917 781250000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (19/4 : ℝ)) 19 15 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(8251060537/10000000000 : ℝ), (-15997653/1000000000 : ℝ), (2925771469/10000000000 : ℝ)] ![(9798412666451/12500000000000 : ℝ), (13276327399/2500000000000 : ℝ), (164700355917/781250000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(8251060537/10000000000 : ℝ)|^19 ≤ (9798412666451/12500000000000 : ℝ)^15
        have hw : |(8251060537/10000000000 : ℝ)|=(8251060537/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-15997653/1000000000 : ℝ)|^19 ≤ (13276327399/2500000000000 : ℝ)^15
        have hw : |(-15997653/1000000000 : ℝ)|=(15997653/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2925771469/10000000000 : ℝ)|^19 ≤ (164700355917/781250000000 : ℝ)^15
        have hw : |(2925771469/10000000000 : ℝ)|=(2925771469/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c314047_s0_21 (p : ℝ) (hpa : (37/8 : ℝ) ≤ p) (hpb : p ≤ (19/4 : ℝ)) (x : Fin 3 → ℝ) :
    (-84749159/2500000000 : ℝ)*x 0 + (-2157243517/2500000000 : ℝ)*x 1 + (2314028867/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (84749159/2500000000 : ℝ)^19 ≤ (1374825225877/100000000000000 : ℝ)^15 := by
    have hnat : (84749159 : ℕ)^19*100000000000000^15 ≤ 1374825225877^15*2500000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      84749159 2500000000 1374825225877 100000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2157243517/2500000000 : ℝ)^19 ≤ (20740614344411/25000000000000 : ℝ)^15 := by
    have hnat : (2157243517 : ℕ)^19*25000000000000^15 ≤ 20740614344411^15*2500000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2157243517 2500000000 20740614344411 25000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2314028867/10000000000 : ℝ)^19 ≤ (15662717385053/100000000000000 : ℝ)^15 := by
    have hnat : (2314028867 : ℕ)^19*100000000000000^15 ≤ 15662717385053^15*10000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2314028867 10000000000 15662717385053 100000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (19/4 : ℝ)) 19 15 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-84749159/2500000000 : ℝ), (-2157243517/2500000000 : ℝ), (2314028867/10000000000 : ℝ)] ![(1374825225877/100000000000000 : ℝ), (20740614344411/25000000000000 : ℝ), (15662717385053/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-84749159/2500000000 : ℝ)|^19 ≤ (1374825225877/100000000000000 : ℝ)^15
        have hw : |(-84749159/2500000000 : ℝ)|=(84749159/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2157243517/2500000000 : ℝ)|^19 ≤ (20740614344411/25000000000000 : ℝ)^15
        have hw : |(-2157243517/2500000000 : ℝ)|=(2157243517/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2314028867/10000000000 : ℝ)|^19 ≤ (15662717385053/100000000000000 : ℝ)^15
        have hw : |(2314028867/10000000000 : ℝ)|=(2314028867/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c314047_s0_22 (p : ℝ) (hpa : (37/8 : ℝ) ≤ p) (hpb : p ≤ (19/4 : ℝ)) (x : Fin 3 → ℝ) :
    (107516937/156250000 : ℝ)*x 0 + (3175165271/10000000000 : ℝ)*x 1 + (2157663329/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (107516937/156250000 : ℝ)^19 ≤ (31141200959869/50000000000000 : ℝ)^15 := by
    have hnat : (107516937 : ℕ)^19*50000000000000^15 ≤ 31141200959869^15*156250000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      107516937 156250000 31141200959869 50000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3175165271/10000000000 : ℝ)^19 ≤ (5845801090473/25000000000000 : ℝ)^15 := by
    have hnat : (3175165271 : ℕ)^19*25000000000000^15 ≤ 5845801090473^15*10000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3175165271 10000000000 5845801090473 25000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2157663329/10000000000 : ℝ)^19 ≤ (14334393708299/100000000000000 : ℝ)^15 := by
    have hnat : (2157663329 : ℕ)^19*100000000000000^15 ≤ 14334393708299^15*10000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2157663329 10000000000 14334393708299 100000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (19/4 : ℝ)) 19 15 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(107516937/156250000 : ℝ), (3175165271/10000000000 : ℝ), (2157663329/10000000000 : ℝ)] ![(31141200959869/50000000000000 : ℝ), (5845801090473/25000000000000 : ℝ), (14334393708299/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(107516937/156250000 : ℝ)|^19 ≤ (31141200959869/50000000000000 : ℝ)^15
        have hw : |(107516937/156250000 : ℝ)|=(107516937/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3175165271/10000000000 : ℝ)|^19 ≤ (5845801090473/25000000000000 : ℝ)^15
        have hw : |(3175165271/10000000000 : ℝ)|=(3175165271/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2157663329/10000000000 : ℝ)|^19 ≤ (14334393708299/100000000000000 : ℝ)^15
        have hw : |(2157663329/10000000000 : ℝ)|=(2157663329/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c314047_s0_23 (p : ℝ) (hpa : (37/8 : ℝ) ≤ p) (hpb : p ≤ (19/4 : ℝ)) (x : Fin 3 → ℝ) :
    (1075824201/5000000000 : ℝ)*x 0 + (-7393326807/10000000000 : ℝ)*x 1 + (-2526220673/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1075824201/5000000000 : ℝ)^19 ≤ (7141898236553/50000000000000 : ℝ)^15 := by
    have hnat : (1075824201 : ℕ)^19*50000000000000^15 ≤ 7141898236553^15*5000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1075824201 5000000000 7141898236553 50000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (7393326807/10000000000 : ℝ)^19 ≤ (34106243031317/50000000000000 : ℝ)^15 := by
    have hnat : (7393326807 : ℕ)^19*50000000000000^15 ≤ 34106243031317^15*10000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7393326807 10000000000 34106243031317 50000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2526220673/10000000000 : ℝ)^19 ≤ (2187964680687/12500000000000 : ℝ)^15 := by
    have hnat : (2526220673 : ℕ)^19*12500000000000^15 ≤ 2187964680687^15*10000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2526220673 10000000000 2187964680687 12500000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (19/4 : ℝ)) 19 15 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1075824201/5000000000 : ℝ), (-7393326807/10000000000 : ℝ), (-2526220673/10000000000 : ℝ)] ![(7141898236553/50000000000000 : ℝ), (34106243031317/50000000000000 : ℝ), (2187964680687/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1075824201/5000000000 : ℝ)|^19 ≤ (7141898236553/50000000000000 : ℝ)^15
        have hw : |(1075824201/5000000000 : ℝ)|=(1075824201/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-7393326807/10000000000 : ℝ)|^19 ≤ (34106243031317/50000000000000 : ℝ)^15
        have hw : |(-7393326807/10000000000 : ℝ)|=(7393326807/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2526220673/10000000000 : ℝ)|^19 ≤ (2187964680687/12500000000000 : ℝ)^15
        have hw : |(-2526220673/10000000000 : ℝ)|=(2526220673/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c314047_s0_27 (p : ℝ) (hpa : (37/8 : ℝ) ≤ p) (hpb : p ≤ (19/4 : ℝ)) (x : Fin 3 → ℝ) :
    (4189374577/5000000000 : ℝ)*x 0 + (54573/1250000000 : ℝ)*x 1 + (4397899/15625000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4189374577/5000000000 : ℝ)^19 ≤ (39963511638001/50000000000000 : ℝ)^15 := by
    have hnat : (4189374577 : ℕ)^19*50000000000000^15 ≤ 39963511638001^15*5000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4189374577 5000000000 39963511638001 50000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (54573/1250000000 : ℝ)^19 ≤ (300205907/100000000000000 : ℝ)^15 := by
    have hnat : (54573 : ℕ)^19*100000000000000^15 ≤ 300205907^15*1250000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      54573 1250000000 300205907 100000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4397899/15625000 : ℝ)^19 ≤ (10036338250911/50000000000000 : ℝ)^15 := by
    have hnat : (4397899 : ℕ)^19*50000000000000^15 ≤ 10036338250911^15*15625000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4397899 15625000 10036338250911 50000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (19/4 : ℝ)) 19 15 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4189374577/5000000000 : ℝ), (54573/1250000000 : ℝ), (4397899/15625000 : ℝ)] ![(39963511638001/50000000000000 : ℝ), (300205907/100000000000000 : ℝ), (10036338250911/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4189374577/5000000000 : ℝ)|^19 ≤ (39963511638001/50000000000000 : ℝ)^15
        have hw : |(4189374577/5000000000 : ℝ)|=(4189374577/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(54573/1250000000 : ℝ)|^19 ≤ (300205907/100000000000000 : ℝ)^15
        have hw : |(54573/1250000000 : ℝ)|=(54573/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4397899/15625000 : ℝ)|^19 ≤ (10036338250911/50000000000000 : ℝ)^15
        have hw : |(4397899/15625000 : ℝ)|=(4397899/15625000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c314047_s1_0 (p : ℝ) (hpa : (37/8 : ℝ) ≤ p) (hpb : p ≤ (19/4 : ℝ)) (x : Fin 3 → ℝ) :
    (-1482300007/10000000000 : ℝ)*x 0 + (-345957731/625000000 : ℝ)*x 1 + (5212677153/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1482300007/10000000000 : ℝ)^19 ≤ (8909481016903/100000000000000 : ℝ)^15 := by
    have hnat : (1482300007 : ℕ)^19*100000000000000^15 ≤ 8909481016903^15*10000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1482300007 10000000000 8909481016903 100000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (345957731/625000000 : ℝ)^19 ≤ (5909596676991/12500000000000 : ℝ)^15 := by
    have hnat : (345957731 : ℕ)^19*12500000000000^15 ≤ 5909596676991^15*625000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      345957731 625000000 5909596676991 12500000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5212677153/10000000000 : ℝ)^19 ≤ (4381374555733/10000000000000 : ℝ)^15 := by
    have hnat : (5212677153 : ℕ)^19*10000000000000^15 ≤ 4381374555733^15*10000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5212677153 10000000000 4381374555733 10000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (19/4 : ℝ)) 19 15 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1482300007/10000000000 : ℝ), (-345957731/625000000 : ℝ), (5212677153/10000000000 : ℝ)] ![(8909481016903/100000000000000 : ℝ), (5909596676991/12500000000000 : ℝ), (4381374555733/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1482300007/10000000000 : ℝ)|^19 ≤ (8909481016903/100000000000000 : ℝ)^15
        have hw : |(-1482300007/10000000000 : ℝ)|=(1482300007/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-345957731/625000000 : ℝ)|^19 ≤ (5909596676991/12500000000000 : ℝ)^15
        have hw : |(-345957731/625000000 : ℝ)|=(345957731/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5212677153/10000000000 : ℝ)|^19 ≤ (4381374555733/10000000000000 : ℝ)^15
        have hw : |(5212677153/10000000000 : ℝ)|=(5212677153/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c314047_s1_1 (p : ℝ) (hpa : (37/8 : ℝ) ≤ p) (hpb : p ≤ (19/4 : ℝ)) (x : Fin 3 → ℝ) :
    (318869619/625000000 : ℝ)*x 0 + (3947718133/10000000000 : ℝ)*x 1 + (1755090803/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (318869619/625000000 : ℝ)^19 ≤ (21318924750029/50000000000000 : ℝ)^15 := by
    have hnat : (318869619 : ℕ)^19*50000000000000^15 ≤ 21318924750029^15*625000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      318869619 625000000 21318924750029 50000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3947718133/10000000000 : ℝ)^19 ≤ (3081095120657/10000000000000 : ℝ)^15 := by
    have hnat : (3947718133 : ℕ)^19*10000000000000^15 ≤ 3081095120657^15*10000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3947718133 10000000000 3081095120657 10000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1755090803/5000000000 : ℝ)^19 ≤ (26551199284717/100000000000000 : ℝ)^15 := by
    have hnat : (1755090803 : ℕ)^19*100000000000000^15 ≤ 26551199284717^15*5000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1755090803 5000000000 26551199284717 100000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (19/4 : ℝ)) 19 15 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(318869619/625000000 : ℝ), (3947718133/10000000000 : ℝ), (1755090803/5000000000 : ℝ)] ![(21318924750029/50000000000000 : ℝ), (3081095120657/10000000000000 : ℝ), (26551199284717/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(318869619/625000000 : ℝ)|^19 ≤ (21318924750029/50000000000000 : ℝ)^15
        have hw : |(318869619/625000000 : ℝ)|=(318869619/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3947718133/10000000000 : ℝ)|^19 ≤ (3081095120657/10000000000000 : ℝ)^15
        have hw : |(3947718133/10000000000 : ℝ)|=(3947718133/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1755090803/5000000000 : ℝ)|^19 ≤ (26551199284717/100000000000000 : ℝ)^15
        have hw : |(1755090803/5000000000 : ℝ)|=(1755090803/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c314047_s1_2 (p : ℝ) (hpa : (37/8 : ℝ) ≤ p) (hpb : p ≤ (19/4 : ℝ)) (x : Fin 3 → ℝ) :
    (1243033013/2500000000 : ℝ)*x 0 + (-813086761/2000000000 : ℝ)*x 1 + (-1765562757/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1243033013/2500000000 : ℝ)^19 ≤ (10317172790889/25000000000000 : ℝ)^15 := by
    have hnat : (1243033013 : ℕ)^19*25000000000000^15 ≤ 10317172790889^15*2500000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1243033013 2500000000 10317172790889 25000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (813086761/2000000000 : ℝ)^19 ≤ (399741046913/1250000000000 : ℝ)^15 := by
    have hnat : (813086761 : ℕ)^19*1250000000000^15 ≤ 399741046913^15*2000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      813086761 2000000000 399741046913 1250000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1765562757/5000000000 : ℝ)^19 ≤ (13376012537023/50000000000000 : ℝ)^15 := by
    have hnat : (1765562757 : ℕ)^19*50000000000000^15 ≤ 13376012537023^15*5000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1765562757 5000000000 13376012537023 50000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (19/4 : ℝ)) 19 15 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1243033013/2500000000 : ℝ), (-813086761/2000000000 : ℝ), (-1765562757/5000000000 : ℝ)] ![(10317172790889/25000000000000 : ℝ), (399741046913/1250000000000 : ℝ), (13376012537023/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1243033013/2500000000 : ℝ)|^19 ≤ (10317172790889/25000000000000 : ℝ)^15
        have hw : |(1243033013/2500000000 : ℝ)|=(1243033013/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-813086761/2000000000 : ℝ)|^19 ≤ (399741046913/1250000000000 : ℝ)^15
        have hw : |(-813086761/2000000000 : ℝ)|=(813086761/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1765562757/5000000000 : ℝ)|^19 ≤ (13376012537023/50000000000000 : ℝ)^15
        have hw : |(-1765562757/5000000000 : ℝ)|=(1765562757/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c314047_s1_6 (p : ℝ) (hpa : (37/8 : ℝ) ≤ p) (hpb : p ≤ (19/4 : ℝ)) (x : Fin 3 → ℝ) :
    (1560329013/2500000000 : ℝ)*x 0 + (-276966083/2000000000 : ℝ)*x 1 + (4540587443/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1560329013/2500000000 : ℝ)^19 ≤ (27520299732789/50000000000000 : ℝ)^15 := by
    have hnat : (1560329013 : ℕ)^19*50000000000000^15 ≤ 27520299732789^15*2500000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1560329013 2500000000 27520299732789 50000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (276966083/2000000000 : ℝ)^19 ≤ (1021752473979/12500000000000 : ℝ)^15 := by
    have hnat : (276966083 : ℕ)^19*12500000000000^15 ≤ 1021752473979^15*2000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      276966083 2000000000 1021752473979 12500000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4540587443/10000000000 : ℝ)^19 ≤ (18392690368311/50000000000000 : ℝ)^15 := by
    have hnat : (4540587443 : ℕ)^19*50000000000000^15 ≤ 18392690368311^15*10000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4540587443 10000000000 18392690368311 50000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (19/4 : ℝ)) 19 15 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1560329013/2500000000 : ℝ), (-276966083/2000000000 : ℝ), (4540587443/10000000000 : ℝ)] ![(27520299732789/50000000000000 : ℝ), (1021752473979/12500000000000 : ℝ), (18392690368311/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1560329013/2500000000 : ℝ)|^19 ≤ (27520299732789/50000000000000 : ℝ)^15
        have hw : |(1560329013/2500000000 : ℝ)|=(1560329013/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-276966083/2000000000 : ℝ)|^19 ≤ (1021752473979/12500000000000 : ℝ)^15
        have hw : |(-276966083/2000000000 : ℝ)|=(276966083/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4540587443/10000000000 : ℝ)|^19 ≤ (18392690368311/50000000000000 : ℝ)^15
        have hw : |(4540587443/10000000000 : ℝ)|=(4540587443/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_c314047 (p : ℝ) (hpa : (37/8 : ℝ) ≤ p) (hpb : p ≤ (19/4 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (172069/100000 : ℝ) (87867/50000 : ℝ) (15771/20000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, false, true], ![true, true, true]]) : False := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : RawLinearData _ _ X N P T := raw_linear_data (by linarith : (1 : ℝ) ≤ p) X hX.raw
  have bounds := raw_linear_data_bounds f (by norm_num)
  have main0 : (15771/20000 : ℝ)*P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.main 0
    change (15771/20000 : ℝ)*P 0 ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order0 : 0 ≤ ((1 : ℝ)*(X 1 2+X 2 2)) ∧ ((1 : ℝ)*(X 1 2+X 2 2)) ≤ ((1 : ℝ)*(X 1 1+X 2 1)) ∧ ((1 : ℝ)*(X 1 1+X 2 1)) ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.ordered 0
    change 0 ≤ ((1 : ℝ)*pair X 0 2) ∧ ((1 : ℝ)*pair X 0 2) ≤ ((1 : ℝ)*pair X 0 1) ∧ ((1 : ℝ)*pair X 0 1) ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main1 : (15771/20000 : ℝ)*P 1 ≤ ((-1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.main 1
    change (15771/20000 : ℝ)*P 1 ≤ ((-1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order1 : 0 ≤ ((1 : ℝ)*(X 0 2+X 2 2)) ∧ ((1 : ℝ)*(X 0 2+X 2 2)) ≤ ((1 : ℝ)*(X 0 0+X 2 0)) ∧ ((1 : ℝ)*(X 0 0+X 2 0)) ≤ ((-1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.ordered 1
    change 0 ≤ ((1 : ℝ)*pair X 1 2) ∧ ((1 : ℝ)*pair X 1 2) ≤ ((1 : ℝ)*pair X 1 0) ∧ ((1 : ℝ)*pair X 1 0) ≤ ((-1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main2 : (15771/20000 : ℝ)*P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.main 2
    change (15771/20000 : ℝ)*P 2 ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order2 : 0 ≤ ((1 : ℝ)*(X 0 1+X 1 1)) ∧ ((1 : ℝ)*(X 0 1+X 1 1)) ≤ ((1 : ℝ)*(X 0 0+X 1 0)) ∧ ((1 : ℝ)*(X 0 0+X 1 0)) ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.ordered 2
    change 0 ≤ ((1 : ℝ)*pair X 2 1) ∧ ((1 : ℝ)*pair X 2 1) ≤ ((1 : ℝ)*pair X 2 0) ∧ ((1 : ℝ)*pair X 2 0) ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have base3 : ((1 : ℝ)*N 1+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    linarith only [f.Ntotal 1]
  have base7 : ((1 : ℝ)*T) ≤ (87867/50000 : ℝ) := by
    linarith only [f.Tcap]
  have base13 : ((1 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    linarith only [(f.coord 0 2).2]
  have base21 : ((1 : ℝ)*X 2 0+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    linarith only [(f.coord 2 0).2]
  have base31 : ((1 : ℝ)*X 0 2+(1 : ℝ)*X 1 2+(1 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    linarith only [(f.column 2).2]
  have base34 : ((-1 : ℝ)*N 0+(1 : ℝ)*P 0+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    linarith only [f.Ptotal 0]
  have base40 : ((-1 : ℝ)*X 1 1+(1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 1+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.2.1]
  have base43 : ((-1 : ℝ)*N 0+(-1 : ℝ)*N 2+(1 : ℝ)*P 1) ≤ (0 : ℝ) := by
    linarith only [f.Ptriangle 1,f.sum]
  have base50 : ((-1 : ℝ)*X 0 0+(1 : ℝ)*X 0 2+(-1 : ℝ)*X 2 0+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order1.2.1]
  have base53 : ((-1 : ℝ)*N 0+(-1 : ℝ)*N 1+(1 : ℝ)*P 2) ≤ (0 : ℝ) := by
    linarith only [f.Ptriangle 2,f.sum]
  have base54 : ((-1 : ℝ)*N 2+(1 : ℝ)*P 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    linarith only [f.Ptotal 2]
  have base59 : ((-1 : ℝ)*X 0 1+(-1 : ℝ)*X 1 1) ≤ (0 : ℝ) := by
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
  have s0_pow0 : (1 : ℝ) ^ (37/8 : ℝ) ≤ (1 : ℝ) := by
    have hpowers : (1 : ℝ)^37 ≤ (1 : ℝ)^8 := by
      have hnat : (1 : ℕ)^37*1^8 ≤ 1^8*1^37 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 37 8 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) (by norm_num) 37 8 (by norm_num) hpowers
    exact h
  have s0_corner0a : (2 : ℝ) ≤ (464673127956063/400000000000000 : ℝ) ^ (37/8 : ℝ) := by
    have hpowers : (2 : ℝ)^8 ≤ (464673127956063/400000000000000 : ℝ)^37 := by
      have hnat : (2 : ℕ)^8*400000000000000^37 ≤ 464673127956063^37*1^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 1 464673127956063 400000000000000 8 37 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (464673127956063/400000000000000 : ℝ)) (X := (2 : ℝ)) (by norm_num) 37 8 (by norm_num) hpowers
    exact h
  have s0_corner0b : (3 : ℝ) ≤ (3170307302424381/2500000000000000 : ℝ) ^ (37/8 : ℝ) := by
    have hpowers : (3 : ℝ)^8 ≤ (3170307302424381/2500000000000000 : ℝ)^37 := by
      have hnat : (3 : ℕ)^8*2500000000000000^37 ≤ 3170307302424381^37*1^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3 1 3170307302424381 2500000000000000 8 37 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (3170307302424381/2500000000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 37 8 (by norm_num) hpowers
    exact h
  have major_s0_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(64673127956063/400000000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(1064401010795949/10000000000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (37/8 : ℝ)) (rho := (1 : ℝ)) (alpha := (64673127956063/400000000000000 : ℝ)) (beta := (1064401010795949/10000000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow0,s0_corner0a]) (by linarith only [s0_pow0,s0_corner0b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, false, true], ![true, true, true]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (1 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order0.2.2])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(64673127956063/400000000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(1064401010795949/10000000000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s0_pow1 : (1 : ℝ) ^ (37/8 : ℝ) ≤ (1 : ℝ) := by
    have hpowers : (1 : ℝ)^37 ≤ (1 : ℝ)^8 := by
      have hnat : (1 : ℕ)^37*1^8 ≤ 1^8*1^37 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 37 8 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) (by norm_num) 37 8 (by norm_num) hpowers
    exact h
  have s0_corner1a : (2 : ℝ) ≤ (464673127956063/400000000000000 : ℝ) ^ (37/8 : ℝ) := by
    have hpowers : (2 : ℝ)^8 ≤ (464673127956063/400000000000000 : ℝ)^37 := by
      have hnat : (2 : ℕ)^8*400000000000000^37 ≤ 464673127956063^37*1^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 1 464673127956063 400000000000000 8 37 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (464673127956063/400000000000000 : ℝ)) (X := (2 : ℝ)) (by norm_num) 37 8 (by norm_num) hpowers
    exact h
  have s0_corner1b : (3 : ℝ) ≤ (3170307302424381/2500000000000000 : ℝ) ^ (37/8 : ℝ) := by
    have hpowers : (3 : ℝ)^8 ≤ (3170307302424381/2500000000000000 : ℝ)^37 := by
      have hnat : (3 : ℕ)^8*2500000000000000^37 ≤ 3170307302424381^37*1^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3 1 3170307302424381 2500000000000000 8 37 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (3170307302424381/2500000000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 37 8 (by norm_num) hpowers
    exact h
  have major_s0_1 : P 1 ≤ ((-1 : ℝ)*(X 0 1+X 2 1))+(64673127956063/400000000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 2 0))+(1064401010795949/10000000000000000 : ℝ)*((1 : ℝ)*(X 0 2+X 2 2)) := by
    have hh := chart_majorant (a := (37/8 : ℝ)) (rho := (1 : ℝ)) (alpha := (64673127956063/400000000000000 : ℝ)) (beta := (1064401010795949/10000000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow1,s0_corner1a]) (by linarith only [s0_pow1,s0_corner1b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, false, true], ![true, true, true]] hX 1 (by
        change ((1 : ℝ)*pair X 1 0) ≤ (1 : ℝ)*((-1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order1.2.2])
    change lpNorm p (pair X 1) ≤ ((-1 : ℝ)*pair X 1 1)+(64673127956063/400000000000000 : ℝ)*((1 : ℝ)*pair X 1 0)+(1064401010795949/10000000000000000 : ℝ)*((1 : ℝ)*pair X 1 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s0_pow2 : (1 : ℝ) ^ (37/8 : ℝ) ≤ (1 : ℝ) := by
    have hpowers : (1 : ℝ)^37 ≤ (1 : ℝ)^8 := by
      have hnat : (1 : ℕ)^37*1^8 ≤ 1^8*1^37 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 37 8 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) (by norm_num) 37 8 (by norm_num) hpowers
    exact h
  have s0_corner2a : (2 : ℝ) ≤ (464673127956063/400000000000000 : ℝ) ^ (37/8 : ℝ) := by
    have hpowers : (2 : ℝ)^8 ≤ (464673127956063/400000000000000 : ℝ)^37 := by
      have hnat : (2 : ℕ)^8*400000000000000^37 ≤ 464673127956063^37*1^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 1 464673127956063 400000000000000 8 37 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (464673127956063/400000000000000 : ℝ)) (X := (2 : ℝ)) (by norm_num) 37 8 (by norm_num) hpowers
    exact h
  have s0_corner2b : (3 : ℝ) ≤ (3170307302424381/2500000000000000 : ℝ) ^ (37/8 : ℝ) := by
    have hpowers : (3 : ℝ)^8 ≤ (3170307302424381/2500000000000000 : ℝ)^37 := by
      have hnat : (3 : ℕ)^8*2500000000000000^37 ≤ 3170307302424381^37*1^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3 1 3170307302424381 2500000000000000 8 37 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (3170307302424381/2500000000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 37 8 (by norm_num) hpowers
    exact h
  have major_s0_2 : P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2))+(64673127956063/400000000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 1 0))+(1064401010795949/10000000000000000 : ℝ)*((1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (37/8 : ℝ)) (rho := (1 : ℝ)) (alpha := (64673127956063/400000000000000 : ℝ)) (beta := (1064401010795949/10000000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow2,s0_corner2a]) (by linarith only [s0_pow2,s0_corner2b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, false, true], ![true, true, true]] hX 2 (by
        change ((1 : ℝ)*pair X 2 0) ≤ (1 : ℝ)*((1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order2.2.2])
    change lpNorm p (pair X 2) ≤ ((1 : ℝ)*pair X 2 2)+(64673127956063/400000000000000 : ℝ)*((1 : ℝ)*pair X 2 0)+(1064401010795949/10000000000000000 : ℝ)*((1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s0_0 : ((-355341/10000000 : ℝ)*X 0 0+(-6264960709/10000000000 : ℝ)*X 0 1+(1031663883/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c314047_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_1 : ((2562822483/5000000000 : ℝ)*X 1 0+(1933807793/5000000000 : ℝ)*X 1 1+(222890853/625000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c314047_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_2 : ((2760944119/5000000000 : ℝ)*X 2 0+(-1944678851/5000000000 : ℝ)*X 2 1+(-618901877/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c314047_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_6 : ((333409703/500000000 : ℝ)*X 0 0+(965243/10000000000 : ℝ)*X 0 1+(30407307/62500000 : ℝ)*X 0 2+(333409703/500000000 : ℝ)*X 1 0+(965243/10000000000 : ℝ)*X 1 1+(30407307/62500000 : ℝ)*X 1 2+(333409703/500000000 : ℝ)*X 2 0+(965243/10000000000 : ℝ)*X 2 1+(30407307/62500000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c314047_s0_6 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_7 : ((-45183161/10000000000 : ℝ)*X 0 0+(-7979750143/10000000000 : ℝ)*X 0 1+(415181149/1250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c314047_s0_7 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_8 : ((2930812617/10000000000 : ℝ)*X 1 0+(5611613289/10000000000 : ℝ)*X 1 1+(1971722311/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c314047_s0_8 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_9 : ((2271540303/5000000000 : ℝ)*X 2 0+(-1705566823/5000000000 : ℝ)*X 2 1+(-4618160561/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c314047_s0_9 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_13 : ((2513262303/5000000000 : ℝ)*X 0 0+(9821911/2000000000 : ℝ)*X 0 1+(6508290511/10000000000 : ℝ)*X 0 2+(2513262303/5000000000 : ℝ)*X 1 0+(9821911/2000000000 : ℝ)*X 1 1+(6508290511/10000000000 : ℝ)*X 1 2+(2513262303/5000000000 : ℝ)*X 2 0+(9821911/2000000000 : ℝ)*X 2 1+(6508290511/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c314047_s0_13 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_14 : ((2691201/10000000000 : ℝ)*X 0 0+(-915509733/2000000000 : ℝ)*X 0 1+(3464484679/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c314047_s0_14 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_15 : ((2905334741/10000000000 : ℝ)*X 1 0+(2330705433/5000000000 : ℝ)*X 1 1+(2476853713/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c314047_s0_15 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_16 : ((890351231/1250000000 : ℝ)*X 2 0+(-1203505327/5000000000 : ℝ)*X 2 1+(-2635606753/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c314047_s0_16 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_20 : ((8251060537/10000000000 : ℝ)*X 0 0+(-15997653/1000000000 : ℝ)*X 0 1+(2925771469/10000000000 : ℝ)*X 0 2+(8251060537/10000000000 : ℝ)*X 1 0+(-15997653/1000000000 : ℝ)*X 1 1+(2925771469/10000000000 : ℝ)*X 1 2+(8251060537/10000000000 : ℝ)*X 2 0+(-15997653/1000000000 : ℝ)*X 2 1+(2925771469/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c314047_s0_20 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_21 : ((-84749159/2500000000 : ℝ)*X 0 0+(-2157243517/2500000000 : ℝ)*X 0 1+(2314028867/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c314047_s0_21 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_22 : ((107516937/156250000 : ℝ)*X 1 0+(3175165271/10000000000 : ℝ)*X 1 1+(2157663329/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c314047_s0_22 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_23 : ((1075824201/5000000000 : ℝ)*X 2 0+(-7393326807/10000000000 : ℝ)*X 2 1+(-2526220673/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c314047_s0_23 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_27 : ((4189374577/5000000000 : ℝ)*X 0 0+(54573/1250000000 : ℝ)*X 0 1+(4397899/15625000 : ℝ)*X 0 2+(4189374577/5000000000 : ℝ)*X 1 0+(54573/1250000000 : ℝ)*X 1 1+(4397899/15625000 : ℝ)*X 1 2+(4189374577/5000000000 : ℝ)*X 2 0+(54573/1250000000 : ℝ)*X 2 1+(4397899/15625000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c314047_s0_27 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have ratio_s0_0 : (0 : ℝ) ≤ ((70149/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(70149/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (15986361615983102786709/2500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (176633047517/500000000000 : ℝ)*(base3) + (272838831621/250000000000 : ℝ)*(base7) + (291842175767/1000000000000 : ℝ)*(base50) + (315191/62500000000 : ℝ)*(base54) + (1089492114393/500000000000 : ℝ)*(major_s0_0) + (1089492114393/500000000000 : ℝ)*(major_s0_1) + (217897918573/100000000000 : ℝ)*(major_s0_2) + (246097/500000000000 : ℝ)*(sp_s0_0) + (1333333/100000000000 : ℝ)*(sp_s0_2) + (2452328424713/1000000000000 : ℝ)*(sp_s0_7) + (2805595011941/1000000000000 : ℝ)*(sp_s0_8) + (490460861063/200000000000 : ℝ)*(sp_s0_9) + (2004427474393/1000000000000 : ℝ)*(sp_s0_13) + (3117603/500000000000 : ℝ)*(sp_s0_23) + (1266343285999/1000000000000 : ℝ)*(f.failure) + (2452328916907/1000000000000 : ℝ)*(f.sum) + (25952147547373/100000000000000000000000000 : ℝ)*base62 + (27054440739223/1000000000000000000000000000 : ℝ)*base64 + (1549789274493957/5000000000000000000000000000 : ℝ)*base67 + (234000638099/40000000000000000000000000 : ℝ)*base69 + (2292604141357/250000000000000000000000000 : ℝ)*base70 + (84912173506043/5000000000000000000000000000 : ℝ)*base72 + (36984694085241/200000000000000000000000000 : ℝ)*base74 + (36811839454759/200000000000000000000000000 : ℝ)*base77 + (1048449033993957/2500000000000000000000000000 : ℝ)*base79 + (38069/100000000000000000 : ℝ)*base86 + (38069/100000000000000000 : ℝ)*base88 + (38069/100000000000000000 : ℝ)*base90 + hcertificate_margin
  have ratio_s0_1 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(-61717/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(-61717/100000 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (28914359770730308215753/5000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (830060682977/1000000000000 : ℝ)*(base7) + (9367079071/20000000000 : ℝ)*(base40) + (148607/62500000000 : ℝ)*(base53) + (32475642273/500000000000 : ℝ)*(base59) + (2013850445213/1000000000000 : ℝ)*(major_s0_0) + (2013850445213/1000000000000 : ℝ)*(major_s0_1) + (1006924033751/500000000000 : ℝ)*(major_s0_2) + (5760487/500000000000 : ℝ)*(sp_s0_1) + (18601461/1000000000000 : ℝ)*(sp_s0_6) + (1185544933259/500000000000 : ℝ)*(sp_s0_14) + (296384793193/125000000000 : ℝ)*(sp_s0_15) + (2371092244229/1000000000000 : ℝ)*(sp_s0_16) + (2000109557587/1000000000000 : ℝ)*(sp_s0_20) + (306295621/1000000000000 : ℝ)*(sp_s0_27) + (292593442923/250000000000 : ℝ)*(f.failure) + (2371092244229/1000000000000 : ℝ)*(f.sum) + (15863164320209/80000000000000000000000000 : ℝ)*base63 + (3501222696574699/5000000000000000000000000000 : ℝ)*base65 + (1763609519842137/10000000000000000000000000000 : ℝ)*base67 + (63919772937687/200000000000000000000000000 : ℝ)*base68 + (1339503627940127/10000000000000000000000000000 : ℝ)*base70 + (4632942067842137/10000000000000000000000000000 : ℝ)*base73 + (17101744476419/400000000000000000000000000 : ℝ)*base75 + (29950460236419/400000000000000000000000000 : ℝ)*base77 + (881278273842137/5000000000000000000000000000 : ℝ)*base79 + (1/1000000000000 : ℝ)*base81 + (1/1000000000000 : ℝ)*base83 + (7313/25000000000000000 : ℝ)*base86 + (7313/25000000000000000 : ℝ)*base88 + (32313/25000000000000000 : ℝ)*base90 + hcertificate_margin
  have ratio_s0_2 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(20031/25000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(20031/25000 : ℝ)*X 1 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (18159789787797836062893/2500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (16240901143/250000000000 : ℝ)*(base3) + (1127250647833/1000000000000 : ℝ)*(base7) + (178193/62500000000 : ℝ)*(base34) + (25059266721/200000000000 : ℝ)*(base40) + (5833637/1000000000000 : ℝ)*(base43) + (111414274227/1000000000000 : ℝ)*(base50) + (1722991399821/1000000000000 : ℝ)*(major_s0_0) + (1722988417273/1000000000000 : ℝ)*(major_s0_1) + (172299425091/100000000000 : ℝ)*(major_s0_2) + (388957/62500000000 : ℝ)*(sp_s0_2) + (7137269471/4000000000 : ℝ)*(sp_s0_21) + (1849289657047/1000000000000 : ℝ)*(sp_s0_22) + (892156997763/500000000000 : ℝ)*(sp_s0_23) + (2063623335719/1000000000000 : ℝ)*(sp_s0_27) + (1001339143547/1000000000000 : ℝ)*(f.failure) + (71373042099/40000000000 : ℝ)*(f.sum) + (310372223003529/400000000000000000000000000 : ℝ)*base63 + (58093322156359/1000000000000000000000000000 : ℝ)*base65 + (424089619972923/10000000000000000000000000000 : ℝ)*base66 + (8098190888733/40000000000000000000000000 : ℝ)*base69 + (833507067236333/2000000000000000000000000000 : ℝ)*base71 + (338367603125129/10000000000000000000000000000 : ℝ)*base73 + (178538436916199/400000000000000000000000000 : ℝ)*base75 + (31904221535277/400000000000000000000000000 : ℝ)*base76 + (3434628672923897/5000000000000000000000000000 : ℝ)*base78 + (88743/100000000000000000 : ℝ)*base87 + (11257/100000000000000000 : ℝ)*base88 + (11257/100000000000000000 : ℝ)*base90 + (1/1000000000000 : ℝ)*base92 + hcertificate_margin
  have s1_pow0 : (70149/100000 : ℝ) ^ (37/8 : ℝ) ≤ (9701063996943110149/50000000000000000000 : ℝ) := by
    have hpowers : (70149/100000 : ℝ)^37 ≤ (9701063996943110149/50000000000000000000 : ℝ)^8 := by
      have hnat : (70149 : ℕ)^37*50000000000000000000^8 ≤ 9701063996943110149^8*100000^37 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        70149 100000 9701063996943110149 50000000000000000000 37 8 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (70149/100000 : ℝ)) (X := (9701063996943110149/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 37 8 (by norm_num) hpowers
    exact h
  have s1_corner0a : (59701063996943110149/50000000000000000000 : ℝ) ≤ (10390854359702651/10000000000000000 : ℝ) ^ (37/8 : ℝ) := by
    have hpowers : (59701063996943110149/50000000000000000000 : ℝ)^8 ≤ (10390854359702651/10000000000000000 : ℝ)^37 := by
      have hnat : (59701063996943110149 : ℕ)^8*10000000000000000^37 ≤ 10390854359702651^37*50000000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        59701063996943110149 50000000000000000000 10390854359702651 10000000000000000 8 37 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10390854359702651/10000000000000000 : ℝ)) (X := (59701063996943110149/50000000000000000000 : ℝ)) (by norm_num) 37 8 (by norm_num) hpowers
    exact h
  have s1_corner0b : (34701063996943110149/25000000000000000000 : ℝ) ≤ (5367348504645923/5000000000000000 : ℝ) ^ (37/8 : ℝ) := by
    have hpowers : (34701063996943110149/25000000000000000000 : ℝ)^8 ≤ (5367348504645923/5000000000000000 : ℝ)^37 := by
      have hnat : (34701063996943110149 : ℕ)^8*5000000000000000^37 ≤ 5367348504645923^37*25000000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        34701063996943110149 25000000000000000000 5367348504645923 5000000000000000 8 37 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5367348504645923/5000000000000000 : ℝ)) (X := (34701063996943110149/25000000000000000000 : ℝ)) (by norm_num) 37 8 (by norm_num) hpowers
    exact h
  have major_s1_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(390854359702651/7014900000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(68768529917839/1402980000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (37/8 : ℝ)) (rho := (70149/100000 : ℝ)) (alpha := (390854359702651/7014900000000000 : ℝ)) (beta := (68768529917839/1402980000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow0,s1_corner0a]) (by linarith only [s1_pow0,s1_corner0b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, false, true], ![true, true, true]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (70149/100000 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_0])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(390854359702651/7014900000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(68768529917839/1402980000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s1_pow1 : (61717/100000 : ℝ) ^ (37/8 : ℝ) ≤ (5365278103471502901/50000000000000000000 : ℝ) := by
    have hpowers : (61717/100000 : ℝ)^37 ≤ (5365278103471502901/50000000000000000000 : ℝ)^8 := by
      have hnat : (61717 : ℕ)^37*50000000000000000000^8 ≤ 5365278103471502901^8*100000^37 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        61717 100000 5365278103471502901 50000000000000000000 37 8 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (61717/100000 : ℝ)) (X := (5365278103471502901/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 37 8 (by norm_num) hpowers
    exact h
  have s1_corner1a : (55365278103471502901/50000000000000000000 : ℝ) ≤ (2555708727285941/2500000000000000 : ℝ) ^ (37/8 : ℝ) := by
    have hpowers : (55365278103471502901/50000000000000000000 : ℝ)^8 ≤ (2555708727285941/2500000000000000 : ℝ)^37 := by
      have hnat : (55365278103471502901 : ℕ)^8*2500000000000000^37 ≤ 2555708727285941^37*50000000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        55365278103471502901 50000000000000000000 2555708727285941 2500000000000000 8 37 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2555708727285941/2500000000000000 : ℝ)) (X := (55365278103471502901/50000000000000000000 : ℝ)) (by norm_num) 37 8 (by norm_num) hpowers
    exact h
  have s1_corner1b : (30365278103471502901/25000000000000000000 : ℝ) ≤ (2085867413109771/2000000000000000 : ℝ) ^ (37/8 : ℝ) := by
    have hpowers : (30365278103471502901/25000000000000000000 : ℝ)^8 ≤ (2085867413109771/2000000000000000 : ℝ)^37 := by
      have hnat : (30365278103471502901 : ℕ)^8*2000000000000000^37 ≤ 2085867413109771^37*25000000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        30365278103471502901 25000000000000000000 2085867413109771 2000000000000000 8 37 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2085867413109771/2000000000000000 : ℝ)) (X := (30365278103471502901/25000000000000000000 : ℝ)) (by norm_num) 37 8 (by norm_num) hpowers
    exact h
  have major_s1_1 : P 1 ≤ ((-1 : ℝ)*(X 0 1+X 2 1))+(55708727285941/1542925000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 2 0))+(206502156405091/6171700000000000 : ℝ)*((1 : ℝ)*(X 0 2+X 2 2)) := by
    have hh := chart_majorant (a := (37/8 : ℝ)) (rho := (61717/100000 : ℝ)) (alpha := (55708727285941/1542925000000000 : ℝ)) (beta := (206502156405091/6171700000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow1,s1_corner1a]) (by linarith only [s1_pow1,s1_corner1b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, false, true], ![true, true, true]] hX 1 (by
        change ((1 : ℝ)*pair X 1 0) ≤ (61717/100000 : ℝ)*((-1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_1])
    change lpNorm p (pair X 1) ≤ ((-1 : ℝ)*pair X 1 1)+(55708727285941/1542925000000000 : ℝ)*((1 : ℝ)*pair X 1 0)+(206502156405091/6171700000000000 : ℝ)*((1 : ℝ)*pair X 1 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s1_pow2 : (20031/25000 : ℝ) ^ (37/8 : ℝ) ≤ (560689152581683639/1562500000000000000 : ℝ) := by
    have hpowers : (20031/25000 : ℝ)^37 ≤ (560689152581683639/1562500000000000000 : ℝ)^8 := by
      have hnat : (20031 : ℕ)^37*1562500000000000000^8 ≤ 560689152581683639^8*25000^37 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        20031 25000 560689152581683639 1562500000000000000 37 8 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (20031/25000 : ℝ)) (X := (560689152581683639/1562500000000000000 : ℝ)) (by norm_num) (by norm_num) 37 8 (by norm_num) hpowers
    exact h
  have s1_corner2a : (2123189152581683639/1562500000000000000 : ℝ) ≤ (10685460025120767/10000000000000000 : ℝ) ^ (37/8 : ℝ) := by
    have hpowers : (2123189152581683639/1562500000000000000 : ℝ)^8 ≤ (10685460025120767/10000000000000000 : ℝ)^37 := by
      have hnat : (2123189152581683639 : ℕ)^8*10000000000000000^37 ≤ 10685460025120767^37*1562500000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2123189152581683639 1562500000000000000 10685460025120767 10000000000000000 8 37 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10685460025120767/10000000000000000 : ℝ)) (X := (2123189152581683639/1562500000000000000 : ℝ)) (by norm_num) 37 8 (by norm_num) hpowers
    exact h
  have s1_corner2b : (1341939152581683639/781250000000000000 : ℝ) ≤ (11240831606181203/10000000000000000 : ℝ) ^ (37/8 : ℝ) := by
    have hpowers : (1341939152581683639/781250000000000000 : ℝ)^8 ≤ (11240831606181203/10000000000000000 : ℝ)^37 := by
      have hnat : (1341939152581683639 : ℕ)^8*10000000000000000^37 ≤ 11240831606181203^37*781250000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1341939152581683639 781250000000000000 11240831606181203 10000000000000000 8 37 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (11240831606181203/10000000000000000 : ℝ)) (X := (1341939152581683639/781250000000000000 : ℝ)) (by norm_num) 37 8 (by norm_num) hpowers
    exact h
  have major_s1_2 : P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2))+(685460025120767/8012400000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 1 0))+(138842895265109/2003100000000000 : ℝ)*((1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (37/8 : ℝ)) (rho := (20031/25000 : ℝ)) (alpha := (685460025120767/8012400000000000 : ℝ)) (beta := (138842895265109/2003100000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow2,s1_corner2a]) (by linarith only [s1_pow2,s1_corner2b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, false, true], ![true, true, true]] hX 2 (by
        change ((1 : ℝ)*pair X 2 0) ≤ (20031/25000 : ℝ)*((1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_2])
    change lpNorm p (pair X 2) ≤ ((1 : ℝ)*pair X 2 2)+(685460025120767/8012400000000000 : ℝ)*((1 : ℝ)*pair X 2 0)+(138842895265109/2003100000000000 : ℝ)*((1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s1_0 : ((-1482300007/10000000000 : ℝ)*X 0 0+(-345957731/625000000 : ℝ)*X 0 1+(5212677153/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c314047_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_1 : ((318869619/625000000 : ℝ)*X 1 0+(3947718133/10000000000 : ℝ)*X 1 1+(1755090803/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c314047_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_2 : ((1243033013/2500000000 : ℝ)*X 2 0+(-813086761/2000000000 : ℝ)*X 2 1+(-1765562757/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c314047_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_6 : ((1560329013/2500000000 : ℝ)*X 0 0+(-276966083/2000000000 : ℝ)*X 0 1+(4540587443/10000000000 : ℝ)*X 0 2+(1560329013/2500000000 : ℝ)*X 1 0+(-276966083/2000000000 : ℝ)*X 1 1+(4540587443/10000000000 : ℝ)*X 1 2+(1560329013/2500000000 : ℝ)*X 2 0+(-276966083/2000000000 : ℝ)*X 2 1+(4540587443/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c314047_s1_6 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have hsep : (-366207/50000 : ℝ) < ((-172069/100000 : ℝ)*P 0+(-172069/100000 : ℝ)*P 1+(-172069/100000 : ℝ)*P 2+(1 : ℝ)*T) := by
    have hcertificate_margin : (-366207/50000 : ℝ) < (-3523564916101917299856521454598263573/481788486782350000000000000000000000 : ℝ) := by norm_num
    linear_combination (12661/1000000000000 : ℝ)*(base7) + (747/100000000000 : ℝ)*(base13) + (47411/500000000000 : ℝ)*(base21) + (1043/200000000000 : ℝ)*(base31) + (495247684969/1000000000000 : ℝ)*(base40) + (10687828087/200000000000 : ℝ)*(base50) + (15217/250000000000 : ℝ)*(base53) + (11351757133/100000000000 : ℝ)*(base59) + (172069/100000 : ℝ)*(major_s1_0) + (172069/100000 : ℝ)*(major_s1_1) + (430172484783/250000000000 : ℝ)*(major_s1_2) + (1218918295501/500000000000 : ℝ)*(sp_s1_0) + (304729574809/125000000000 : ℝ)*(sp_s1_1) + (1218918282259/500000000000 : ℝ)*(sp_s1_2) + (500000003723/500000000000 : ℝ)*(sp_s1_6) + (121891832967/50000000000 : ℝ)*(f.sum) + (4117195890624885059/41208440900000000000000000000000 : ℝ)*base63 + (42811784653133/83462500000000000000000000 : ℝ)*base64 + (97938087341707/154292500000000000000000000 : ℝ)*base66 + (16517357548587/667700000000000000000000000 : ℝ)*base69 + (4119248145670385147/5854810912500000000000000000000 : ℝ)*base70 + (6750620248489/70149000000000000000000000 : ℝ)*base72 + (4181357851111/38573125000000000000000000 : ℝ)*base74 + (10053619830977/17537250000000000000000000 : ℝ)*base76 + (6333868945705692779/21646929165000000000000000000000 : ℝ)*base78 + hcertificate_margin
  linarith only [hsep,f.failure]

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
namespace HlawkaSchatten.DiagonalCutoff4
theorem coarse_distinct_p014_b024 (p : ℝ) (hpa : (37/8 : ℝ) ≤ p) (hpb : p ≤ (75/16 : ℝ))
    (c : Fin 88) (hlo : 47 ≤ c.val) (hhi : c.val < 55)
    (hn63 : c ≠ 63) (hn87 : c ≠ 87)
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (172069/100000 : ℝ) (87867/50000 : ℝ) (15771/20000 : ℝ) X (distinctOrders c) (distinctSigns c)) : False := by
  have hc : c=47 ∨ c=48 ∨ c=49 ∨ c=50 ∨ c=51 ∨ c=52 ∨ c=53 ∨ c=54 := by omega
  rcases hc with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  · exact collision_c314047 p hpa (by linarith only [hpb]) X hX
  · exact collision_c314048 p hpa (by linarith only [hpb]) X hX
  · exact collision_c314049 p hpa (by linarith only [hpb]) X hX
  · exact collision_c314050 p hpa (by linarith only [hpb]) X hX
  · exact collision_c314051 p hpa (by linarith only [hpb]) X hX
  · exact collision_c314052 p hpa (by linarith only [hpb]) X hX
  · exact collision_c314053 p hpa (by linarith only [hpb]) X hX
  · exact collision_c314054 p hpa (by linarith only [hpb]) X hX

end HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p : ℝ) (hpa : (37/8 : ℝ) ≤ p) (hpb : p ≤ (75/16 : ℝ))
    (c : Fin 88) (hlo : 47 ≤ c.val) (hhi : c.val < 55)
    (hn63 : c ≠ 63) (hn87 : c ≠ 87)
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (172069/100000 : ℝ) (87867/50000 : ℝ) (15771/20000 : ℝ) X (distinctOrders c) (distinctSigns c)) : False := by
  exact HlawkaSchatten.DiagonalCutoff4.coarse_distinct_p014_b024 p hpa hpb c hlo hhi hn63 hn87 X hX

#print axioms solution
