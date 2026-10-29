-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.coarse_distinct_p015_b023
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T00:54:27.231885+00:00
-- url     : https://prove2.me/submissions/583abd77-c54a-46e2-bd80-a4462278ea86

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
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_collision_c315053_s0
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_collision_c315053_s1
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_collision_c315053_s2
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_collision_c315053_s3
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_collision_c315054_s0
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_collision_c315054_s1
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_collision_c315054_s2
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_collision_c315054_s3
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
theorem HlawkaSchatten.DiagonalCutoff4.collision_c315053 (p : ℝ) (hpa : (75/16 : ℝ) ≤ p) (hpb : p ≤ (19/4 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (174659/100000 : ℝ) (34911/20000 : ℝ) (15821/20000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![true, false, true]]) : False := by
  have h0 := collision_c315053_s0 p hpa hpb X hX
  have h1 := collision_c315053_s1 p hpa hpb X hX h0
  have h2 := collision_c315053_s2 p hpa hpb X hX h1
  exact collision_c315053_s3 p hpa hpb X hX h2

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6 HlawkaSchatten.DiagonalCutoff4
theorem HlawkaSchatten.DiagonalCutoff4.collision_c315054 (p : ℝ) (hpa : (75/16 : ℝ) ≤ p) (hpb : p ≤ (19/4 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (174659/100000 : ℝ) (34911/20000 : ℝ) (15821/20000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![true, true, false]]) : False := by
  have h0 := collision_c315054_s0 p hpa hpb X hX
  have h1 := collision_c315054_s1 p hpa hpb X hX h0
  have h2 := collision_c315054_s2 p hpa hpb X hX h1
  exact collision_c315054_s3 p hpa hpb X hX h2

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
theorem collision_support_c315047_s0_1 (p : ℝ) (hpa : (75/16 : ℝ) ≤ p) (hpb : p ≤ (77/16 : ℝ)) (x : Fin 3 → ℝ) :
    (2562834577/5000000000 : ℝ)*x 0 + (769394259/2000000000 : ℝ)*x 1 + (3548583931/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2562834577/5000000000 : ℝ)^77 ≤ (21507482430741/50000000000000 : ℝ)^61 := by
    have hnat : (2562834577 : ℕ)^77*50000000000000^61 ≤ 21507482430741^61*5000000000^77 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2562834577 5000000000 21507482430741 50000000000000 77 61 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (769394259/2000000000 : ℝ)^77 ≤ (2994316376827/10000000000000 : ℝ)^61 := by
    have hnat : (769394259 : ℕ)^77*10000000000000^61 ≤ 2994316376827^61*2000000000^77 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      769394259 2000000000 2994316376827 10000000000000 77 61 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3548583931/10000000000 : ℝ)^77 ≤ (27041871351537/100000000000000 : ℝ)^61 := by
    have hnat : (3548583931 : ℕ)^77*100000000000000^61 ≤ 27041871351537^61*10000000000^77 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3548583931 10000000000 27041871351537 100000000000000 77 61 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (77/16 : ℝ)) 77 61 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2562834577/5000000000 : ℝ), (769394259/2000000000 : ℝ), (3548583931/10000000000 : ℝ)] ![(21507482430741/50000000000000 : ℝ), (2994316376827/10000000000000 : ℝ), (27041871351537/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2562834577/5000000000 : ℝ)|^77 ≤ (21507482430741/50000000000000 : ℝ)^61
        have hw : |(2562834577/5000000000 : ℝ)|=(2562834577/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(769394259/2000000000 : ℝ)|^77 ≤ (2994316376827/10000000000000 : ℝ)^61
        have hw : |(769394259/2000000000 : ℝ)|=(769394259/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3548583931/10000000000 : ℝ)|^77 ≤ (27041871351537/100000000000000 : ℝ)^61
        have hw : |(3548583931/10000000000 : ℝ)|=(3548583931/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c315047_s0_2 (p : ℝ) (hpa : (75/16 : ℝ) ≤ p) (hpb : p ≤ (77/16 : ℝ)) (x : Fin 3 → ℝ) :
    (110385077/200000000 : ℝ)*x 0 + (-3859481131/10000000000 : ℝ)*x 1 + (-1545023401/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (110385077/200000000 : ℝ)^77 ≤ (47225532062311/100000000000000 : ℝ)^61 := by
    have hnat : (110385077 : ℕ)^77*100000000000000^61 ≤ 47225532062311^61*200000000^77 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      110385077 200000000 47225532062311 100000000000000 77 61 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3859481131/10000000000 : ℝ)^77 ≤ (7516531821179/25000000000000 : ℝ)^61 := by
    have hnat : (3859481131 : ℕ)^77*25000000000000^61 ≤ 7516531821179^61*10000000000^77 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3859481131 10000000000 7516531821179 25000000000000 77 61 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1545023401/5000000000 : ℝ)^77 ≤ (1419271289737/6250000000000 : ℝ)^61 := by
    have hnat : (1545023401 : ℕ)^77*6250000000000^61 ≤ 1419271289737^61*5000000000^77 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1545023401 5000000000 1419271289737 6250000000000 77 61 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (77/16 : ℝ)) 77 61 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(110385077/200000000 : ℝ), (-3859481131/10000000000 : ℝ), (-1545023401/5000000000 : ℝ)] ![(47225532062311/100000000000000 : ℝ), (7516531821179/25000000000000 : ℝ), (1419271289737/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(110385077/200000000 : ℝ)|^77 ≤ (47225532062311/100000000000000 : ℝ)^61
        have hw : |(110385077/200000000 : ℝ)|=(110385077/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-3859481131/10000000000 : ℝ)|^77 ≤ (7516531821179/25000000000000 : ℝ)^61
        have hw : |(-3859481131/10000000000 : ℝ)|=(3859481131/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1545023401/5000000000 : ℝ)|^77 ≤ (1419271289737/6250000000000 : ℝ)^61
        have hw : |(-1545023401/5000000000 : ℝ)|=(1545023401/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c315047_s0_6 (p : ℝ) (hpa : (75/16 : ℝ) ≤ p) (hpb : p ≤ (77/16 : ℝ)) (x : Fin 3 → ℝ) :
    (6665652849/10000000000 : ℝ)*x 0 + (211411/5000000000 : ℝ)*x 1 + (4845692341/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (6665652849/10000000000 : ℝ)^77 ≤ (59929064169679/100000000000000 : ℝ)^61 := by
    have hnat : (6665652849 : ℕ)^77*100000000000000^61 ≤ 59929064169679^61*10000000000^77 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6665652849 10000000000 59929064169679 100000000000000 77 61 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (211411/5000000000 : ℝ)^77 ≤ (150622629/50000000000000 : ℝ)^61 := by
    have hnat : (211411 : ℕ)^77*50000000000000^61 ≤ 150622629^61*5000000000^77 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      211411 5000000000 150622629 50000000000000 77 61 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4845692341/10000000000 : ℝ)^77 ≤ (20035317289753/50000000000000 : ℝ)^61 := by
    have hnat : (4845692341 : ℕ)^77*50000000000000^61 ≤ 20035317289753^61*10000000000^77 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4845692341 10000000000 20035317289753 50000000000000 77 61 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (77/16 : ℝ)) 77 61 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(6665652849/10000000000 : ℝ), (211411/5000000000 : ℝ), (4845692341/10000000000 : ℝ)] ![(59929064169679/100000000000000 : ℝ), (150622629/50000000000000 : ℝ), (20035317289753/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(6665652849/10000000000 : ℝ)|^77 ≤ (59929064169679/100000000000000 : ℝ)^61
        have hw : |(6665652849/10000000000 : ℝ)|=(6665652849/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(211411/5000000000 : ℝ)|^77 ≤ (150622629/50000000000000 : ℝ)^61
        have hw : |(211411/5000000000 : ℝ)|=(211411/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4845692341/10000000000 : ℝ)|^77 ≤ (20035317289753/50000000000000 : ℝ)^61
        have hw : |(4845692341/10000000000 : ℝ)|=(4845692341/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c315047_s0_7 (p : ℝ) (hpa : (75/16 : ℝ) ≤ p) (hpb : p ≤ (77/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-11658053/2000000000 : ℝ)*x 0 + (-992854439/1250000000 : ℝ)*x 1 + (668539813/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (11658053/2000000000 : ℝ)^77 ≤ (75594963473/50000000000000 : ℝ)^61 := by
    have hnat : (11658053 : ℕ)^77*50000000000000^61 ≤ 75594963473^61*2000000000^77 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      11658053 2000000000 75594963473 50000000000000 77 61 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (992854439/1250000000 : ℝ)^77 ≤ (4673257050083/6250000000000 : ℝ)^61 := by
    have hnat : (992854439 : ℕ)^77*6250000000000^61 ≤ 4673257050083^61*1250000000^77 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      992854439 1250000000 4673257050083 6250000000000 77 61 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (668539813/2000000000 : ℝ)^77 ≤ (1003067890329/4000000000000 : ℝ)^61 := by
    have hnat : (668539813 : ℕ)^77*4000000000000^61 ≤ 1003067890329^61*2000000000^77 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      668539813 2000000000 1003067890329 4000000000000 77 61 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (77/16 : ℝ)) 77 61 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-11658053/2000000000 : ℝ), (-992854439/1250000000 : ℝ), (668539813/2000000000 : ℝ)] ![(75594963473/50000000000000 : ℝ), (4673257050083/6250000000000 : ℝ), (1003067890329/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-11658053/2000000000 : ℝ)|^77 ≤ (75594963473/50000000000000 : ℝ)^61
        have hw : |(-11658053/2000000000 : ℝ)|=(11658053/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-992854439/1250000000 : ℝ)|^77 ≤ (4673257050083/6250000000000 : ℝ)^61
        have hw : |(-992854439/1250000000 : ℝ)|=(992854439/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(668539813/2000000000 : ℝ)|^77 ≤ (1003067890329/4000000000000 : ℝ)^61
        have hw : |(668539813/2000000000 : ℝ)|=(668539813/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c315047_s0_8 (p : ℝ) (hpa : (75/16 : ℝ) ≤ p) (hpb : p ≤ (77/16 : ℝ)) (x : Fin 3 → ℝ) :
    (2954727407/10000000000 : ℝ)*x 0 + (2777941441/5000000000 : ℝ)*x 1 + (3945873817/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2954727407/10000000000 : ℝ)^77 ≤ (21460347198743/100000000000000 : ℝ)^61 := by
    have hnat : (2954727407 : ℕ)^77*100000000000000^61 ≤ 21460347198743^61*10000000000^77 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2954727407 10000000000 21460347198743 100000000000000 77 61 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2777941441/5000000000 : ℝ)^77 ≤ (11905375004449/25000000000000 : ℝ)^61 := by
    have hnat : (2777941441 : ℕ)^77*25000000000000^61 ≤ 11905375004449^61*5000000000^77 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2777941441 5000000000 11905375004449 25000000000000 77 61 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3945873817/10000000000 : ℝ)^77 ≤ (30918152772941/100000000000000 : ℝ)^61 := by
    have hnat : (3945873817 : ℕ)^77*100000000000000^61 ≤ 30918152772941^61*10000000000^77 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3945873817 10000000000 30918152772941 100000000000000 77 61 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (77/16 : ℝ)) 77 61 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2954727407/10000000000 : ℝ), (2777941441/5000000000 : ℝ), (3945873817/10000000000 : ℝ)] ![(21460347198743/100000000000000 : ℝ), (11905375004449/25000000000000 : ℝ), (30918152772941/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2954727407/10000000000 : ℝ)|^77 ≤ (21460347198743/100000000000000 : ℝ)^61
        have hw : |(2954727407/10000000000 : ℝ)|=(2954727407/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2777941441/5000000000 : ℝ)|^77 ≤ (11905375004449/25000000000000 : ℝ)^61
        have hw : |(2777941441/5000000000 : ℝ)|=(2777941441/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3945873817/10000000000 : ℝ)|^77 ≤ (30918152772941/100000000000000 : ℝ)^61
        have hw : |(3945873817/10000000000 : ℝ)|=(3945873817/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c315047_s0_9 (p : ℝ) (hpa : (75/16 : ℝ) ≤ p) (hpb : p ≤ (77/16 : ℝ)) (x : Fin 3 → ℝ) :
    (2290761439/5000000000 : ℝ)*x 0 + (-3383243229/10000000000 : ℝ)*x 1 + (-456912227/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2290761439/5000000000 : ℝ)^77 ≤ (37333130886421/100000000000000 : ℝ)^61 := by
    have hnat : (2290761439 : ℕ)^77*100000000000000^61 ≤ 37333130886421^61*5000000000^77 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2290761439 5000000000 37333130886421 100000000000000 77 61 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3383243229/10000000000 : ℝ)^77 ≤ (5092249048407/20000000000000 : ℝ)^61 := by
    have hnat : (3383243229 : ℕ)^77*20000000000000^61 ≤ 5092249048407^61*10000000000^77 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3383243229 10000000000 5092249048407 20000000000000 77 61 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (456912227/1000000000 : ℝ)^77 ≤ (37205623856293/100000000000000 : ℝ)^61 := by
    have hnat : (456912227 : ℕ)^77*100000000000000^61 ≤ 37205623856293^61*1000000000^77 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      456912227 1000000000 37205623856293 100000000000000 77 61 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (77/16 : ℝ)) 77 61 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2290761439/5000000000 : ℝ), (-3383243229/10000000000 : ℝ), (-456912227/1000000000 : ℝ)] ![(37333130886421/100000000000000 : ℝ), (5092249048407/20000000000000 : ℝ), (37205623856293/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2290761439/5000000000 : ℝ)|^77 ≤ (37333130886421/100000000000000 : ℝ)^61
        have hw : |(2290761439/5000000000 : ℝ)|=(2290761439/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-3383243229/10000000000 : ℝ)|^77 ≤ (5092249048407/20000000000000 : ℝ)^61
        have hw : |(-3383243229/10000000000 : ℝ)|=(3383243229/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-456912227/1000000000 : ℝ)|^77 ≤ (37205623856293/100000000000000 : ℝ)^61
        have hw : |(-456912227/1000000000 : ℝ)|=(456912227/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c315047_s0_13 (p : ℝ) (hpa : (75/16 : ℝ) ≤ p) (hpb : p ≤ (77/16 : ℝ)) (x : Fin 3 → ℝ) :
    (1006934457/2000000000 : ℝ)*x 0 + (38428767/10000000000 : ℝ)*x 1 + (6482443711/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1006934457/2000000000 : ℝ)^77 ≤ (42053265024071/100000000000000 : ℝ)^61 := by
    have hnat : (1006934457 : ℕ)^77*100000000000000^61 ≤ 42053265024071^61*2000000000^77 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1006934457 2000000000 42053265024071 100000000000000 77 61 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (38428767/10000000000 : ℝ)^77 ≤ (17871199851/20000000000000 : ℝ)^61 := by
    have hnat : (38428767 : ℕ)^77*20000000000000^61 ≤ 17871199851^61*10000000000^77 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      38428767 10000000000 17871199851 20000000000000 77 61 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (6482443711/10000000000 : ℝ)^77 ≤ (57857378963723/100000000000000 : ℝ)^61 := by
    have hnat : (6482443711 : ℕ)^77*100000000000000^61 ≤ 57857378963723^61*10000000000^77 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6482443711 10000000000 57857378963723 100000000000000 77 61 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (77/16 : ℝ)) 77 61 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1006934457/2000000000 : ℝ), (38428767/10000000000 : ℝ), (6482443711/10000000000 : ℝ)] ![(42053265024071/100000000000000 : ℝ), (17871199851/20000000000000 : ℝ), (57857378963723/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1006934457/2000000000 : ℝ)|^77 ≤ (42053265024071/100000000000000 : ℝ)^61
        have hw : |(1006934457/2000000000 : ℝ)|=(1006934457/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(38428767/10000000000 : ℝ)|^77 ≤ (17871199851/20000000000000 : ℝ)^61
        have hw : |(38428767/10000000000 : ℝ)|=(38428767/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(6482443711/10000000000 : ℝ)|^77 ≤ (57857378963723/100000000000000 : ℝ)^61
        have hw : |(6482443711/10000000000 : ℝ)|=(6482443711/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c315047_s0_14 (p : ℝ) (hpa : (75/16 : ℝ) ≤ p) (hpb : p ≤ (77/16 : ℝ)) (x : Fin 3 → ℝ) :
    (135813/1000000000 : ℝ)*x 0 + (-2295974683/5000000000 : ℝ)*x 1 + (6896285159/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (135813/1000000000 : ℝ)^77 ≤ (1314107443/100000000000000 : ℝ)^61 := by
    have hnat : (135813 : ℕ)^77*100000000000000^61 ≤ 1314107443^61*1000000000^77 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      135813 1000000000 1314107443 100000000000000 77 61 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2295974683/5000000000 : ℝ)^77 ≤ (936010236681/2500000000000 : ℝ)^61 := by
    have hnat : (2295974683 : ℕ)^77*2500000000000^61 ≤ 936010236681^61*5000000000^77 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2295974683 5000000000 936010236681 2500000000000 77 61 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (6896285159/10000000000 : ℝ)^77 ≤ (62558276415983/100000000000000 : ℝ)^61 := by
    have hnat : (6896285159 : ℕ)^77*100000000000000^61 ≤ 62558276415983^61*10000000000^77 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6896285159 10000000000 62558276415983 100000000000000 77 61 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (77/16 : ℝ)) 77 61 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(135813/1000000000 : ℝ), (-2295974683/5000000000 : ℝ), (6896285159/10000000000 : ℝ)] ![(1314107443/100000000000000 : ℝ), (936010236681/2500000000000 : ℝ), (62558276415983/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(135813/1000000000 : ℝ)|^77 ≤ (1314107443/100000000000000 : ℝ)^61
        have hw : |(135813/1000000000 : ℝ)|=(135813/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2295974683/5000000000 : ℝ)|^77 ≤ (936010236681/2500000000000 : ℝ)^61
        have hw : |(-2295974683/5000000000 : ℝ)|=(2295974683/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(6896285159/10000000000 : ℝ)|^77 ≤ (62558276415983/100000000000000 : ℝ)^61
        have hw : |(6896285159/10000000000 : ℝ)|=(6896285159/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c315047_s0_15 (p : ℝ) (hpa : (75/16 : ℝ) ≤ p) (hpb : p ≤ (77/16 : ℝ)) (x : Fin 3 → ℝ) :
    (1464728259/5000000000 : ℝ)*x 0 + (4660493713/10000000000 : ℝ)*x 1 + (4898613017/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1464728259/5000000000 : ℝ)^77 ≤ (21228921119433/100000000000000 : ℝ)^61 := by
    have hnat : (1464728259 : ℕ)^77*100000000000000^61 ≤ 21228921119433^61*5000000000^77 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1464728259 5000000000 21228921119433 100000000000000 77 61 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4660493713/10000000000 : ℝ)^77 ≤ (9536812848867/25000000000000 : ℝ)^61 := by
    have hnat : (4660493713 : ℕ)^77*25000000000000^61 ≤ 9536812848867^61*10000000000^77 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4660493713 10000000000 9536812848867 25000000000000 77 61 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4898613017/10000000000 : ℝ)^77 ≤ (40623827463977/100000000000000 : ℝ)^61 := by
    have hnat : (4898613017 : ℕ)^77*100000000000000^61 ≤ 40623827463977^61*10000000000^77 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4898613017 10000000000 40623827463977 100000000000000 77 61 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (77/16 : ℝ)) 77 61 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1464728259/5000000000 : ℝ), (4660493713/10000000000 : ℝ), (4898613017/10000000000 : ℝ)] ![(21228921119433/100000000000000 : ℝ), (9536812848867/25000000000000 : ℝ), (40623827463977/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1464728259/5000000000 : ℝ)|^77 ≤ (21228921119433/100000000000000 : ℝ)^61
        have hw : |(1464728259/5000000000 : ℝ)|=(1464728259/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4660493713/10000000000 : ℝ)|^77 ≤ (9536812848867/25000000000000 : ℝ)^61
        have hw : |(4660493713/10000000000 : ℝ)|=(4660493713/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4898613017/10000000000 : ℝ)|^77 ≤ (40623827463977/100000000000000 : ℝ)^61
        have hw : |(4898613017/10000000000 : ℝ)|=(4898613017/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c315047_s0_16 (p : ℝ) (hpa : (75/16 : ℝ) ≤ p) (hpb : p ≤ (77/16 : ℝ)) (x : Fin 3 → ℝ) :
    (1767931581/2500000000 : ℝ)*x 0 + (-152749933/625000000 : ℝ)*x 1 + (-2631107479/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1767931581/2500000000 : ℝ)^77 ≤ (64573854294297/100000000000000 : ℝ)^61 := by
    have hnat : (1767931581 : ℕ)^77*100000000000000^61 ≤ 64573854294297^61*2500000000^77 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1767931581 2500000000 64573854294297 100000000000000 77 61 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (152749933/625000000 : ℝ)^77 ≤ (16888960331059/100000000000000 : ℝ)^61 := by
    have hnat : (152749933 : ℕ)^77*100000000000000^61 ≤ 16888960331059^61*625000000^77 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      152749933 625000000 16888960331059 100000000000000 77 61 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2631107479/10000000000 : ℝ)^77 ≤ (18537185366963/100000000000000 : ℝ)^61 := by
    have hnat : (2631107479 : ℕ)^77*100000000000000^61 ≤ 18537185366963^61*10000000000^77 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2631107479 10000000000 18537185366963 100000000000000 77 61 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (77/16 : ℝ)) 77 61 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1767931581/2500000000 : ℝ), (-152749933/625000000 : ℝ), (-2631107479/10000000000 : ℝ)] ![(64573854294297/100000000000000 : ℝ), (16888960331059/100000000000000 : ℝ), (18537185366963/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1767931581/2500000000 : ℝ)|^77 ≤ (64573854294297/100000000000000 : ℝ)^61
        have hw : |(1767931581/2500000000 : ℝ)|=(1767931581/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-152749933/625000000 : ℝ)|^77 ≤ (16888960331059/100000000000000 : ℝ)^61
        have hw : |(-152749933/625000000 : ℝ)|=(152749933/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2631107479/10000000000 : ℝ)|^77 ≤ (18537185366963/100000000000000 : ℝ)^61
        have hw : |(-2631107479/10000000000 : ℝ)|=(2631107479/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c315047_s0_20 (p : ℝ) (hpa : (75/16 : ℝ) ≤ p) (hpb : p ≤ (77/16 : ℝ)) (x : Fin 3 → ℝ) :
    (2063897407/2500000000 : ℝ)*x 0 + (-80095599/5000000000 : ℝ)*x 1 + (2899007933/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2063897407/2500000000 : ℝ)^77 ≤ (3140302777273/4000000000000 : ℝ)^61 := by
    have hnat : (2063897407 : ℕ)^77*4000000000000^61 ≤ 3140302777273^61*2500000000^77 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2063897407 2500000000 3140302777273 4000000000000 77 61 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (80095599/5000000000 : ℝ)^77 ≤ (27082839811/5000000000000 : ℝ)^61 := by
    have hnat : (80095599 : ℕ)^77*5000000000000^61 ≤ 27082839811^61*5000000000^77 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      80095599 5000000000 27082839811 5000000000000 77 61 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2899007933/10000000000 : ℝ)^77 ≤ (10475386879601/50000000000000 : ℝ)^61 := by
    have hnat : (2899007933 : ℕ)^77*50000000000000^61 ≤ 10475386879601^61*10000000000^77 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2899007933 10000000000 10475386879601 50000000000000 77 61 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (77/16 : ℝ)) 77 61 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2063897407/2500000000 : ℝ), (-80095599/5000000000 : ℝ), (2899007933/10000000000 : ℝ)] ![(3140302777273/4000000000000 : ℝ), (27082839811/5000000000000 : ℝ), (10475386879601/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2063897407/2500000000 : ℝ)|^77 ≤ (3140302777273/4000000000000 : ℝ)^61
        have hw : |(2063897407/2500000000 : ℝ)|=(2063897407/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-80095599/5000000000 : ℝ)|^77 ≤ (27082839811/5000000000000 : ℝ)^61
        have hw : |(-80095599/5000000000 : ℝ)|=(80095599/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2899007933/10000000000 : ℝ)|^77 ≤ (10475386879601/50000000000000 : ℝ)^61
        have hw : |(2899007933/10000000000 : ℝ)|=(2899007933/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c315047_s0_21 (p : ℝ) (hpa : (75/16 : ℝ) ≤ p) (hpb : p ≤ (77/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-17584039/500000000 : ℝ)*x 0 + (-1714162473/2000000000 : ℝ)*x 1 + (295992017/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (17584039/500000000 : ℝ)^77 ≤ (73076977277/5000000000000 : ℝ)^61 := by
    have hnat : (17584039 : ℕ)^77*5000000000000^61 ≤ 73076977277^61*500000000^77 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      17584039 500000000 73076977277 5000000000000 77 61 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1714162473/2000000000 : ℝ)^77 ≤ (20577565505971/25000000000000 : ℝ)^61 := by
    have hnat : (1714162473 : ℕ)^77*25000000000000^61 ≤ 20577565505971^61*2000000000^77 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1714162473 2000000000 20577565505971 25000000000000 77 61 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (295992017/1250000000 : ℝ)^77 ≤ (3245639683961/20000000000000 : ℝ)^61 := by
    have hnat : (295992017 : ℕ)^77*20000000000000^61 ≤ 3245639683961^61*1250000000^77 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      295992017 1250000000 3245639683961 20000000000000 77 61 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (77/16 : ℝ)) 77 61 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-17584039/500000000 : ℝ), (-1714162473/2000000000 : ℝ), (295992017/1250000000 : ℝ)] ![(73076977277/5000000000000 : ℝ), (20577565505971/25000000000000 : ℝ), (3245639683961/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-17584039/500000000 : ℝ)|^77 ≤ (73076977277/5000000000000 : ℝ)^61
        have hw : |(-17584039/500000000 : ℝ)|=(17584039/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1714162473/2000000000 : ℝ)|^77 ≤ (20577565505971/25000000000000 : ℝ)^61
        have hw : |(-1714162473/2000000000 : ℝ)|=(1714162473/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(295992017/1250000000 : ℝ)|^77 ≤ (3245639683961/20000000000000 : ℝ)^61
        have hw : |(295992017/1250000000 : ℝ)|=(295992017/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c315047_s0_22 (p : ℝ) (hpa : (75/16 : ℝ) ≤ p) (hpb : p ≤ (77/16 : ℝ)) (x : Fin 3 → ℝ) :
    (3423910707/5000000000 : ℝ)*x 0 + (3169034411/10000000000 : ℝ)*x 1 + (2172081621/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3423910707/5000000000 : ℝ)^77 ≤ (62003846977521/100000000000000 : ℝ)^61 := by
    have hnat : (3423910707 : ℕ)^77*100000000000000^61 ≤ 62003846977521^61*5000000000^77 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3423910707 5000000000 62003846977521 100000000000000 77 61 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3169034411/10000000000 : ℝ)^77 ≤ (2930438171611/12500000000000 : ℝ)^61 := by
    have hnat : (3169034411 : ℕ)^77*12500000000000^61 ≤ 2930438171611^61*10000000000^77 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3169034411 10000000000 2930438171611 12500000000000 77 61 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2172081621/10000000000 : ℝ)^77 ≤ (7276323817579/50000000000000 : ℝ)^61 := by
    have hnat : (2172081621 : ℕ)^77*50000000000000^61 ≤ 7276323817579^61*10000000000^77 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2172081621 10000000000 7276323817579 50000000000000 77 61 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (77/16 : ℝ)) 77 61 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3423910707/5000000000 : ℝ), (3169034411/10000000000 : ℝ), (2172081621/10000000000 : ℝ)] ![(62003846977521/100000000000000 : ℝ), (2930438171611/12500000000000 : ℝ), (7276323817579/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3423910707/5000000000 : ℝ)|^77 ≤ (62003846977521/100000000000000 : ℝ)^61
        have hw : |(3423910707/5000000000 : ℝ)|=(3423910707/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3169034411/10000000000 : ℝ)|^77 ≤ (2930438171611/12500000000000 : ℝ)^61
        have hw : |(3169034411/10000000000 : ℝ)|=(3169034411/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2172081621/10000000000 : ℝ)|^77 ≤ (7276323817579/50000000000000 : ℝ)^61
        have hw : |(2172081621/10000000000 : ℝ)|=(2172081621/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c315047_s0_23 (p : ℝ) (hpa : (75/16 : ℝ) ≤ p) (hpb : p ≤ (77/16 : ℝ)) (x : Fin 3 → ℝ) :
    (2159317563/10000000000 : ℝ)*x 0 + (-3651134573/5000000000 : ℝ)*x 1 + (-2605841789/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2159317563/10000000000 : ℝ)^77 ≤ (7222391358689/50000000000000 : ℝ)^61 := by
    have hnat : (2159317563 : ℕ)^77*50000000000000^61 ≤ 7222391358689^61*10000000000^77 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2159317563 10000000000 7222391358689 50000000000000 77 61 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3651134573/5000000000 : ℝ)^77 ≤ (67242445243727/100000000000000 : ℝ)^61 := by
    have hnat : (3651134573 : ℕ)^77*100000000000000^61 ≤ 67242445243727^61*5000000000^77 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3651134573 5000000000 67242445243727 100000000000000 77 61 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2605841789/10000000000 : ℝ)^77 ≤ (4578193005749/25000000000000 : ℝ)^61 := by
    have hnat : (2605841789 : ℕ)^77*25000000000000^61 ≤ 4578193005749^61*10000000000^77 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2605841789 10000000000 4578193005749 25000000000000 77 61 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (77/16 : ℝ)) 77 61 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2159317563/10000000000 : ℝ), (-3651134573/5000000000 : ℝ), (-2605841789/10000000000 : ℝ)] ![(7222391358689/50000000000000 : ℝ), (67242445243727/100000000000000 : ℝ), (4578193005749/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2159317563/10000000000 : ℝ)|^77 ≤ (7222391358689/50000000000000 : ℝ)^61
        have hw : |(2159317563/10000000000 : ℝ)|=(2159317563/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-3651134573/5000000000 : ℝ)|^77 ≤ (67242445243727/100000000000000 : ℝ)^61
        have hw : |(-3651134573/5000000000 : ℝ)|=(3651134573/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2605841789/10000000000 : ℝ)|^77 ≤ (4578193005749/25000000000000 : ℝ)^61
        have hw : |(-2605841789/10000000000 : ℝ)|=(2605841789/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c315047_s0_27 (p : ℝ) (hpa : (75/16 : ℝ) ≤ p) (hpb : p ≤ (77/16 : ℝ)) (x : Fin 3 → ℝ) :
    (4175208951/5000000000 : ℝ)*x 0 + (50533/2000000000 : ℝ)*x 1 + (566640169/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4175208951/5000000000 : ℝ)^77 ≤ (39823796826633/50000000000000 : ℝ)^61 := by
    have hnat : (4175208951 : ℕ)^77*50000000000000^61 ≤ 39823796826633^61*5000000000^77 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4175208951 5000000000 39823796826633 50000000000000 77 61 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (50533/2000000000 : ℝ)^77 ≤ (157273399/100000000000000 : ℝ)^61 := by
    have hnat : (50533 : ℕ)^77*100000000000000^61 ≤ 157273399^61*2000000000^77 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      50533 2000000000 157273399 100000000000000 77 61 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (566640169/2000000000 : ℝ)^77 ≤ (5088062264189/25000000000000 : ℝ)^61 := by
    have hnat : (566640169 : ℕ)^77*25000000000000^61 ≤ 5088062264189^61*2000000000^77 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      566640169 2000000000 5088062264189 25000000000000 77 61 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (77/16 : ℝ)) 77 61 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4175208951/5000000000 : ℝ), (50533/2000000000 : ℝ), (566640169/2000000000 : ℝ)] ![(39823796826633/50000000000000 : ℝ), (157273399/100000000000000 : ℝ), (5088062264189/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4175208951/5000000000 : ℝ)|^77 ≤ (39823796826633/50000000000000 : ℝ)^61
        have hw : |(4175208951/5000000000 : ℝ)|=(4175208951/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(50533/2000000000 : ℝ)|^77 ≤ (157273399/100000000000000 : ℝ)^61
        have hw : |(50533/2000000000 : ℝ)|=(50533/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(566640169/2000000000 : ℝ)|^77 ≤ (5088062264189/25000000000000 : ℝ)^61
        have hw : |(566640169/2000000000 : ℝ)|=(566640169/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c315047_s1_0 (p : ℝ) (hpa : (75/16 : ℝ) ≤ p) (hpb : p ≤ (77/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-383510189/2500000000 : ℝ)*x 0 + (-1362817821/2500000000 : ℝ)*x 1 + (209209943/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (383510189/2500000000 : ℝ)^77 ≤ (9381794598059/100000000000000 : ℝ)^61 := by
    have hnat : (383510189 : ℕ)^77*100000000000000^61 ≤ 9381794598059^61*2500000000^77 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      383510189 2500000000 9381794598059 100000000000000 77 61 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1362817821/2500000000 : ℝ)^77 ≤ (929849064867/2000000000000 : ℝ)^61 := by
    have hnat : (1362817821 : ℕ)^77*2000000000000^61 ≤ 929849064867^61*2500000000^77 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1362817821 2500000000 929849064867 2000000000000 77 61 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (209209943/400000000 : ℝ)^77 ≤ (22062876073937/50000000000000 : ℝ)^61 := by
    have hnat : (209209943 : ℕ)^77*50000000000000^61 ≤ 22062876073937^61*400000000^77 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      209209943 400000000 22062876073937 50000000000000 77 61 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (77/16 : ℝ)) 77 61 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-383510189/2500000000 : ℝ), (-1362817821/2500000000 : ℝ), (209209943/400000000 : ℝ)] ![(9381794598059/100000000000000 : ℝ), (929849064867/2000000000000 : ℝ), (22062876073937/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-383510189/2500000000 : ℝ)|^77 ≤ (9381794598059/100000000000000 : ℝ)^61
        have hw : |(-383510189/2500000000 : ℝ)|=(383510189/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1362817821/2500000000 : ℝ)|^77 ≤ (929849064867/2000000000000 : ℝ)^61
        have hw : |(-1362817821/2500000000 : ℝ)|=(1362817821/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(209209943/400000000 : ℝ)|^77 ≤ (22062876073937/50000000000000 : ℝ)^61
        have hw : |(209209943/400000000 : ℝ)|=(209209943/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c315047_s1_1 (p : ℝ) (hpa : (75/16 : ℝ) ≤ p) (hpb : p ≤ (77/16 : ℝ)) (x : Fin 3 → ℝ) :
    (2538741297/5000000000 : ℝ)*x 0 + (31620609/80000000 : ℝ)*x 1 + (3493219433/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2538741297/5000000000 : ℝ)^77 ≤ (21252571303101/50000000000000 : ℝ)^61 := by
    have hnat : (2538741297 : ℕ)^77*50000000000000^61 ≤ 21252571303101^61*5000000000^77 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2538741297 5000000000 21252571303101 50000000000000 77 61 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (31620609/80000000 : ℝ)^77 ≤ (15492229346887/50000000000000 : ℝ)^61 := by
    have hnat : (31620609 : ℕ)^77*50000000000000^61 ≤ 15492229346887^61*80000000^77 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      31620609 80000000 15492229346887 50000000000000 77 61 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3493219433/10000000000 : ℝ)^77 ≤ (5302079736017/20000000000000 : ℝ)^61 := by
    have hnat : (3493219433 : ℕ)^77*20000000000000^61 ≤ 5302079736017^61*10000000000^77 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3493219433 10000000000 5302079736017 20000000000000 77 61 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (77/16 : ℝ)) 77 61 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2538741297/5000000000 : ℝ), (31620609/80000000 : ℝ), (3493219433/10000000000 : ℝ)] ![(21252571303101/50000000000000 : ℝ), (15492229346887/50000000000000 : ℝ), (5302079736017/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2538741297/5000000000 : ℝ)|^77 ≤ (21252571303101/50000000000000 : ℝ)^61
        have hw : |(2538741297/5000000000 : ℝ)|=(2538741297/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(31620609/80000000 : ℝ)|^77 ≤ (15492229346887/50000000000000 : ℝ)^61
        have hw : |(31620609/80000000 : ℝ)|=(31620609/80000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3493219433/10000000000 : ℝ)|^77 ≤ (5302079736017/20000000000000 : ℝ)^61
        have hw : |(3493219433/10000000000 : ℝ)|=(3493219433/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c315047_s1_2 (p : ℝ) (hpa : (75/16 : ℝ) ≤ p) (hpb : p ≤ (77/16 : ℝ)) (x : Fin 3 → ℝ) :
    (4945771069/10000000000 : ℝ)*x 0 + (-4070113577/10000000000 : ℝ)*x 1 + (-351611053/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4945771069/10000000000 : ℝ)^77 ≤ (41118105290687/100000000000000 : ℝ)^61 := by
    have hnat : (4945771069 : ℕ)^77*100000000000000^61 ≤ 41118105290687^61*10000000000^77 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4945771069 10000000000 41118105290687 100000000000000 77 61 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4070113577/10000000000 : ℝ)^77 ≤ (803800458309/2500000000000 : ℝ)^61 := by
    have hnat : (4070113577 : ℕ)^77*2500000000000^61 ≤ 803800458309^61*10000000000^77 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4070113577 10000000000 803800458309 2500000000000 77 61 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (351611053/1000000000 : ℝ)^77 ≤ (13364938181163/50000000000000 : ℝ)^61 := by
    have hnat : (351611053 : ℕ)^77*50000000000000^61 ≤ 13364938181163^61*1000000000^77 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      351611053 1000000000 13364938181163 50000000000000 77 61 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (77/16 : ℝ)) 77 61 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4945771069/10000000000 : ℝ), (-4070113577/10000000000 : ℝ), (-351611053/1000000000 : ℝ)] ![(41118105290687/100000000000000 : ℝ), (803800458309/2500000000000 : ℝ), (13364938181163/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4945771069/10000000000 : ℝ)|^77 ≤ (41118105290687/100000000000000 : ℝ)^61
        have hw : |(4945771069/10000000000 : ℝ)|=(4945771069/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-4070113577/10000000000 : ℝ)|^77 ≤ (803800458309/2500000000000 : ℝ)^61
        have hw : |(-4070113577/10000000000 : ℝ)|=(4070113577/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-351611053/1000000000 : ℝ)|^77 ≤ (13364938181163/50000000000000 : ℝ)^61
        have hw : |(-351611053/1000000000 : ℝ)|=(351611053/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c315047_s1_6 (p : ℝ) (hpa : (75/16 : ℝ) ≤ p) (hpb : p ≤ (77/16 : ℝ)) (x : Fin 3 → ℝ) :
    (3102367587/5000000000 : ℝ)*x 0 + (-1440631933/10000000000 : ℝ)*x 1 + (4508838287/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3102367587/5000000000 : ℝ)^77 ≤ (13686600366539/25000000000000 : ℝ)^61 := by
    have hnat : (3102367587 : ℕ)^77*25000000000000^61 ≤ 13686600366539^61*5000000000^77 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3102367587 5000000000 13686600366539 25000000000000 77 61 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1440631933/10000000000 : ℝ)^77 ≤ (2166634457097/25000000000000 : ℝ)^61 := by
    have hnat : (1440631933 : ℕ)^77*25000000000000^61 ≤ 2166634457097^61*10000000000^77 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1440631933 10000000000 2166634457097 25000000000000 77 61 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4508838287/10000000000 : ℝ)^77 ≤ (4573382585561/12500000000000 : ℝ)^61 := by
    have hnat : (4508838287 : ℕ)^77*12500000000000^61 ≤ 4573382585561^61*10000000000^77 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4508838287 10000000000 4573382585561 12500000000000 77 61 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (77/16 : ℝ)) 77 61 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3102367587/5000000000 : ℝ), (-1440631933/10000000000 : ℝ), (4508838287/10000000000 : ℝ)] ![(13686600366539/25000000000000 : ℝ), (2166634457097/25000000000000 : ℝ), (4573382585561/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3102367587/5000000000 : ℝ)|^77 ≤ (13686600366539/25000000000000 : ℝ)^61
        have hw : |(3102367587/5000000000 : ℝ)|=(3102367587/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1440631933/10000000000 : ℝ)|^77 ≤ (2166634457097/25000000000000 : ℝ)^61
        have hw : |(-1440631933/10000000000 : ℝ)|=(1440631933/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4508838287/10000000000 : ℝ)|^77 ≤ (4573382585561/12500000000000 : ℝ)^61
        have hw : |(4508838287/10000000000 : ℝ)|=(4508838287/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_c315047 (p : ℝ) (hpa : (75/16 : ℝ) ≤ p) (hpb : p ≤ (77/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (174659/100000 : ℝ) (34911/20000 : ℝ) (15821/20000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, false, true], ![true, true, true]]) : False := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : RawLinearData _ _ X N P T := raw_linear_data (by linarith : (1 : ℝ) ≤ p) X hX.raw
  have bounds := raw_linear_data_bounds f (by norm_num)
  have main0 : (15821/20000 : ℝ)*P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.main 0
    change (15821/20000 : ℝ)*P 0 ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order0 : 0 ≤ ((1 : ℝ)*(X 1 2+X 2 2)) ∧ ((1 : ℝ)*(X 1 2+X 2 2)) ≤ ((1 : ℝ)*(X 1 1+X 2 1)) ∧ ((1 : ℝ)*(X 1 1+X 2 1)) ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.ordered 0
    change 0 ≤ ((1 : ℝ)*pair X 0 2) ∧ ((1 : ℝ)*pair X 0 2) ≤ ((1 : ℝ)*pair X 0 1) ∧ ((1 : ℝ)*pair X 0 1) ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main1 : (15821/20000 : ℝ)*P 1 ≤ ((-1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.main 1
    change (15821/20000 : ℝ)*P 1 ≤ ((-1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order1 : 0 ≤ ((1 : ℝ)*(X 0 2+X 2 2)) ∧ ((1 : ℝ)*(X 0 2+X 2 2)) ≤ ((1 : ℝ)*(X 0 0+X 2 0)) ∧ ((1 : ℝ)*(X 0 0+X 2 0)) ≤ ((-1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.ordered 1
    change 0 ≤ ((1 : ℝ)*pair X 1 2) ∧ ((1 : ℝ)*pair X 1 2) ≤ ((1 : ℝ)*pair X 1 0) ∧ ((1 : ℝ)*pair X 1 0) ≤ ((-1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main2 : (15821/20000 : ℝ)*P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.main 2
    change (15821/20000 : ℝ)*P 2 ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order2 : 0 ≤ ((1 : ℝ)*(X 0 1+X 1 1)) ∧ ((1 : ℝ)*(X 0 1+X 1 1)) ≤ ((1 : ℝ)*(X 0 0+X 1 0)) ∧ ((1 : ℝ)*(X 0 0+X 1 0)) ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.ordered 2
    change 0 ≤ ((1 : ℝ)*pair X 2 1) ∧ ((1 : ℝ)*pair X 2 1) ≤ ((1 : ℝ)*pair X 2 0) ∧ ((1 : ℝ)*pair X 2 0) ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have base3 : ((1 : ℝ)*N 1+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    linarith only [f.Ntotal 1]
  have base7 : ((1 : ℝ)*T) ≤ (34911/20000 : ℝ) := by
    linarith only [f.Tcap]
  have base8 : ((-1 : ℝ)*X 0 0+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    linarith only [(f.coord 0 0).1]
  have base13 : ((1 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    linarith only [(f.coord 0 2).2]
  have base21 : ((1 : ℝ)*X 2 0+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    linarith only [(f.coord 2 0).2]
  have base34 : ((-1 : ℝ)*N 0+(1 : ℝ)*P 0+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    linarith only [f.Ptotal 0]
  have base39 : ((-1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.1]
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
  have s0_pow0 : (1 : ℝ) ^ (75/16 : ℝ) ≤ (1 : ℝ) := by
    have hpowers : (1 : ℝ)^75 ≤ (1 : ℝ)^16 := by
      have hnat : (1 : ℕ)^75*1^16 ≤ 1^16*1^75 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 75 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) (by norm_num) 75 16 (by norm_num) hpowers
    exact h
  have s0_corner0a : (2 : ℝ) ≤ (5796818954377947/5000000000000000 : ℝ) ^ (75/16 : ℝ) := by
    have hpowers : (2 : ℝ)^16 ≤ (5796818954377947/5000000000000000 : ℝ)^75 := by
      have hnat : (2 : ℕ)^16*5000000000000000^75 ≤ 5796818954377947^75*1^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 1 5796818954377947 5000000000000000 16 75 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5796818954377947/5000000000000000 : ℝ)) (X := (2 : ℝ)) (by norm_num) 75 16 (by norm_num) hpowers
    exact h
  have s0_corner0b : (3 : ℝ) ≤ (3160282282318219/2500000000000000 : ℝ) ^ (75/16 : ℝ) := by
    have hpowers : (3 : ℝ)^16 ≤ (3160282282318219/2500000000000000 : ℝ)^75 := by
      have hnat : (3 : ℕ)^16*2500000000000000^75 ≤ 3160282282318219^75*1^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3 1 3160282282318219 2500000000000000 16 75 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (3160282282318219/2500000000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 75 16 (by norm_num) hpowers
    exact h
  have major_s0_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(796818954377947/5000000000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(523745610258491/5000000000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (75/16 : ℝ)) (rho := (1 : ℝ)) (alpha := (796818954377947/5000000000000000 : ℝ)) (beta := (523745610258491/5000000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow0,s0_corner0a]) (by linarith only [s0_pow0,s0_corner0b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, false, true], ![true, true, true]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (1 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order0.2.2])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(796818954377947/5000000000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(523745610258491/5000000000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s0_pow1 : (1 : ℝ) ^ (75/16 : ℝ) ≤ (1 : ℝ) := by
    have hpowers : (1 : ℝ)^75 ≤ (1 : ℝ)^16 := by
      have hnat : (1 : ℕ)^75*1^16 ≤ 1^16*1^75 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 75 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) (by norm_num) 75 16 (by norm_num) hpowers
    exact h
  have s0_corner1a : (2 : ℝ) ≤ (5796818954377947/5000000000000000 : ℝ) ^ (75/16 : ℝ) := by
    have hpowers : (2 : ℝ)^16 ≤ (5796818954377947/5000000000000000 : ℝ)^75 := by
      have hnat : (2 : ℕ)^16*5000000000000000^75 ≤ 5796818954377947^75*1^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 1 5796818954377947 5000000000000000 16 75 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5796818954377947/5000000000000000 : ℝ)) (X := (2 : ℝ)) (by norm_num) 75 16 (by norm_num) hpowers
    exact h
  have s0_corner1b : (3 : ℝ) ≤ (3160282282318219/2500000000000000 : ℝ) ^ (75/16 : ℝ) := by
    have hpowers : (3 : ℝ)^16 ≤ (3160282282318219/2500000000000000 : ℝ)^75 := by
      have hnat : (3 : ℕ)^16*2500000000000000^75 ≤ 3160282282318219^75*1^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3 1 3160282282318219 2500000000000000 16 75 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (3160282282318219/2500000000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 75 16 (by norm_num) hpowers
    exact h
  have major_s0_1 : P 1 ≤ ((-1 : ℝ)*(X 0 1+X 2 1))+(796818954377947/5000000000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 2 0))+(523745610258491/5000000000000000 : ℝ)*((1 : ℝ)*(X 0 2+X 2 2)) := by
    have hh := chart_majorant (a := (75/16 : ℝ)) (rho := (1 : ℝ)) (alpha := (796818954377947/5000000000000000 : ℝ)) (beta := (523745610258491/5000000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow1,s0_corner1a]) (by linarith only [s0_pow1,s0_corner1b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, false, true], ![true, true, true]] hX 1 (by
        change ((1 : ℝ)*pair X 1 0) ≤ (1 : ℝ)*((-1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order1.2.2])
    change lpNorm p (pair X 1) ≤ ((-1 : ℝ)*pair X 1 1)+(796818954377947/5000000000000000 : ℝ)*((1 : ℝ)*pair X 1 0)+(523745610258491/5000000000000000 : ℝ)*((1 : ℝ)*pair X 1 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s0_pow2 : (1 : ℝ) ^ (75/16 : ℝ) ≤ (1 : ℝ) := by
    have hpowers : (1 : ℝ)^75 ≤ (1 : ℝ)^16 := by
      have hnat : (1 : ℕ)^75*1^16 ≤ 1^16*1^75 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 75 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) (by norm_num) 75 16 (by norm_num) hpowers
    exact h
  have s0_corner2a : (2 : ℝ) ≤ (5796818954377947/5000000000000000 : ℝ) ^ (75/16 : ℝ) := by
    have hpowers : (2 : ℝ)^16 ≤ (5796818954377947/5000000000000000 : ℝ)^75 := by
      have hnat : (2 : ℕ)^16*5000000000000000^75 ≤ 5796818954377947^75*1^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 1 5796818954377947 5000000000000000 16 75 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5796818954377947/5000000000000000 : ℝ)) (X := (2 : ℝ)) (by norm_num) 75 16 (by norm_num) hpowers
    exact h
  have s0_corner2b : (3 : ℝ) ≤ (3160282282318219/2500000000000000 : ℝ) ^ (75/16 : ℝ) := by
    have hpowers : (3 : ℝ)^16 ≤ (3160282282318219/2500000000000000 : ℝ)^75 := by
      have hnat : (3 : ℕ)^16*2500000000000000^75 ≤ 3160282282318219^75*1^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3 1 3160282282318219 2500000000000000 16 75 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (3160282282318219/2500000000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 75 16 (by norm_num) hpowers
    exact h
  have major_s0_2 : P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2))+(796818954377947/5000000000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 1 0))+(523745610258491/5000000000000000 : ℝ)*((1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (75/16 : ℝ)) (rho := (1 : ℝ)) (alpha := (796818954377947/5000000000000000 : ℝ)) (beta := (523745610258491/5000000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow2,s0_corner2a]) (by linarith only [s0_pow2,s0_corner2b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, false, true], ![true, true, true]] hX 2 (by
        change ((1 : ℝ)*pair X 2 0) ≤ (1 : ℝ)*((1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order2.2.2])
    change lpNorm p (pair X 2) ≤ ((1 : ℝ)*pair X 2 2)+(796818954377947/5000000000000000 : ℝ)*((1 : ℝ)*pair X 2 0)+(523745610258491/5000000000000000 : ℝ)*((1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s0_1 : ((2562834577/5000000000 : ℝ)*X 1 0+(769394259/2000000000 : ℝ)*X 1 1+(3548583931/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c315047_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_2 : ((110385077/200000000 : ℝ)*X 2 0+(-3859481131/10000000000 : ℝ)*X 2 1+(-1545023401/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c315047_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_6 : ((6665652849/10000000000 : ℝ)*X 0 0+(211411/5000000000 : ℝ)*X 0 1+(4845692341/10000000000 : ℝ)*X 0 2+(6665652849/10000000000 : ℝ)*X 1 0+(211411/5000000000 : ℝ)*X 1 1+(4845692341/10000000000 : ℝ)*X 1 2+(6665652849/10000000000 : ℝ)*X 2 0+(211411/5000000000 : ℝ)*X 2 1+(4845692341/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c315047_s0_6 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_7 : ((-11658053/2000000000 : ℝ)*X 0 0+(-992854439/1250000000 : ℝ)*X 0 1+(668539813/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c315047_s0_7 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_8 : ((2954727407/10000000000 : ℝ)*X 1 0+(2777941441/5000000000 : ℝ)*X 1 1+(3945873817/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c315047_s0_8 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_9 : ((2290761439/5000000000 : ℝ)*X 2 0+(-3383243229/10000000000 : ℝ)*X 2 1+(-456912227/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c315047_s0_9 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_13 : ((1006934457/2000000000 : ℝ)*X 0 0+(38428767/10000000000 : ℝ)*X 0 1+(6482443711/10000000000 : ℝ)*X 0 2+(1006934457/2000000000 : ℝ)*X 1 0+(38428767/10000000000 : ℝ)*X 1 1+(6482443711/10000000000 : ℝ)*X 1 2+(1006934457/2000000000 : ℝ)*X 2 0+(38428767/10000000000 : ℝ)*X 2 1+(6482443711/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c315047_s0_13 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_14 : ((135813/1000000000 : ℝ)*X 0 0+(-2295974683/5000000000 : ℝ)*X 0 1+(6896285159/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c315047_s0_14 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_15 : ((1464728259/5000000000 : ℝ)*X 1 0+(4660493713/10000000000 : ℝ)*X 1 1+(4898613017/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c315047_s0_15 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_16 : ((1767931581/2500000000 : ℝ)*X 2 0+(-152749933/625000000 : ℝ)*X 2 1+(-2631107479/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c315047_s0_16 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_20 : ((2063897407/2500000000 : ℝ)*X 0 0+(-80095599/5000000000 : ℝ)*X 0 1+(2899007933/10000000000 : ℝ)*X 0 2+(2063897407/2500000000 : ℝ)*X 1 0+(-80095599/5000000000 : ℝ)*X 1 1+(2899007933/10000000000 : ℝ)*X 1 2+(2063897407/2500000000 : ℝ)*X 2 0+(-80095599/5000000000 : ℝ)*X 2 1+(2899007933/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c315047_s0_20 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_21 : ((-17584039/500000000 : ℝ)*X 0 0+(-1714162473/2000000000 : ℝ)*X 0 1+(295992017/1250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c315047_s0_21 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_22 : ((3423910707/5000000000 : ℝ)*X 1 0+(3169034411/10000000000 : ℝ)*X 1 1+(2172081621/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c315047_s0_22 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_23 : ((2159317563/10000000000 : ℝ)*X 2 0+(-3651134573/5000000000 : ℝ)*X 2 1+(-2605841789/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c315047_s0_23 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_27 : ((4175208951/5000000000 : ℝ)*X 0 0+(50533/2000000000 : ℝ)*X 0 1+(566640169/2000000000 : ℝ)*X 0 2+(4175208951/5000000000 : ℝ)*X 1 0+(50533/2000000000 : ℝ)*X 1 1+(566640169/2000000000 : ℝ)*X 1 2+(4175208951/5000000000 : ℝ)*X 2 0+(50533/2000000000 : ℝ)*X 2 1+(566640169/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c315047_s0_27 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have ratio_s0_0 : (0 : ℝ) ≤ ((34209/50000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(34209/50000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (5819428250810543738943/1250000000000000000000000000 : ℝ) := by norm_num
    linear_combination (72768796559/200000000000 : ℝ)*(base3) + (1102453937931/1000000000000 : ℝ)*(base7) + (291517632611/1000000000000 : ℝ)*(base50) + (112729/200000000000 : ℝ)*(base54) + (2167697486809/1000000000000 : ℝ)*(major_s0_0) + (2167697486809/1000000000000 : ℝ)*(major_s0_1) + (541924230791/250000000000 : ℝ)*(major_s0_2) + (2452827341077/1000000000000 : ℝ)*(sp_s0_7) + (1408331025079/500000000000 : ℝ)*(sp_s0_8) + (245282323267/100000000000 : ℝ)*(sp_s0_9) + (989856023421/500000000000 : ℝ)*(sp_s0_13) + (2468817/250000000000 : ℝ)*(sp_s0_15) + (601553/1000000000000 : ℝ)*(sp_s0_21) + (829263/200000000000 : ℝ)*(sp_s0_23) + (1241102655351/1000000000000 : ℝ)*(f.failure) + (245282794263/100000000000 : ℝ)*(f.sum) + (288735695565431/5000000000000000000000000000 : ℝ)*base63 + (49607966728619/1250000000000000000000000000 : ℝ)*base64 + (3158411884754781/5000000000000000000000000000 : ℝ)*base66 + (654656518733923/1250000000000000000000000000 : ℝ)*base68 + (901649388413353/5000000000000000000000000000 : ℝ)*base70 + (2535244099254781/5000000000000000000000000000 : ℝ)*base72 + (330274454498877/5000000000000000000000000000 : ℝ)*base74 + (640382136001123/5000000000000000000000000000 : ℝ)*base77 + (1691648504004781/2500000000000000000000000000 : ℝ)*base78 + (1/1000000000000 : ℝ)*base83 + (50309/100000000000000000 : ℝ)*base87 + (50309/100000000000000000 : ℝ)*base89 + (50309/100000000000000000 : ℝ)*base91 + hcertificate_margin
  have ratio_s0_1 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(-30133/50000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(-30133/50000 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (4323980447727132916017/312500000000000000000000000 : ℝ) := by norm_num
    linear_combination (416138897253/500000000000 : ℝ)*(base7) + (60283848071/125000000000 : ℝ)*(base40) + (1180393/250000000000 : ℝ)*(base53) + (74619953329/1000000000000 : ℝ)*(base59) + (507618971121/250000000000 : ℝ)*(major_s0_0) + (507618971121/250000000000 : ℝ)*(major_s0_1) + (63452223841/31250000000 : ℝ)*(major_s0_2) + (7198321/250000000000 : ℝ)*(sp_s0_1) + (27182039/1000000000000 : ℝ)*(sp_s0_6) + (241414437961/100000000000 : ℝ)*(sp_s0_14) + (1207057793163/500000000000 : ℝ)*(sp_s0_15) + (1207074550591/500000000000 : ℝ)*(sp_s0_16) + (1994054868057/1000000000000 : ℝ)*(sp_s0_20) + (366482607/500000000000 : ℝ)*(sp_s0_27) + (290634305201/250000000000 : ℝ)*(f.failure) + (1207074550591/500000000000 : ℝ)*(f.sum) + (25560902830997/1250000000000000000000000000 : ℝ)*base62 + (3244131834819/156250000000000000000000000 : ℝ)*base64 + (546467611538411/1250000000000000000000000000 : ℝ)*base67 + (1939208764847/9765625000000000000000000 : ℝ)*base69 + (21923869568007/250000000000000000000000000 : ℝ)*base71 + (1002877992038411/1250000000000000000000000000 : ℝ)*base73 + (519811224393587/1250000000000000000000000000 : ℝ)*base75 + (838704560981413/1250000000000000000000000000 : ℝ)*base76 + (100537703288411/625000000000000000000000000 : ℝ)*base79 + (1459/25000000000000000 : ℝ)*base87 + (1459/25000000000000000 : ℝ)*base89 + (1459/25000000000000000 : ℝ)*base91 + hcertificate_margin
  have ratio_s0_2 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(78431/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(78431/100000 : ℝ)*X 1 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (2239272067441730352207/312500000000000000000000000 : ℝ) := by norm_num
    linear_combination (238931897/4000000000 : ℝ)*(base3) + (1137812065367/1000000000000 : ℝ)*(base7) + (1394567/500000000000 : ℝ)*(base34) + (33670973231/250000000000 : ℝ)*(base40) + (5320363/1000000000000 : ℝ)*(base43) + (350893329/3125000000 : ℝ)*(base50) + (432269031007/250000000000 : ℝ)*(major_s0_0) + (1729073592799/1000000000000 : ℝ)*(major_s0_1) + (864539456581/500000000000 : ℝ)*(major_s0_2) + (3255077/500000000000 : ℝ)*(sp_s0_2) + (451534312373/250000000000 : ℝ)*(sp_s0_21) + (1865878333239/1000000000000 : ℝ)*(sp_s0_22) + (1806133528473/1000000000000 : ℝ)*(sp_s0_23) + (51701260763/25000000000 : ℝ)*(sp_s0_27) + (989974128537/1000000000000 : ℝ)*(f.failure) + (1806145358989/1000000000000 : ℝ)*(f.sum) + (2985852675557933/5000000000000000000000000000 : ℝ)*base62 + (165913723920729/2500000000000000000000000000 : ℝ)*base64 + (2537708310206309/5000000000000000000000000000 : ℝ)*base67 + (65906976080793/2500000000000000000000000000 : ℝ)*base68 + (443647396165471/2500000000000000000000000000 : ℝ)*base70 + (304897136655437/1250000000000000000000000000 : ℝ)*base73 + (3607327195896347/5000000000000000000000000000 : ℝ)*base74 + (590585444002629/1250000000000000000000000000 : ℝ)*base77 + (3602556074828057/5000000000000000000000000000 : ℝ)*base79 + (1/1000000000000 : ℝ)*base85 + (56117/100000000000000000 : ℝ)*base86 + (56117/100000000000000000 : ℝ)*base88 + (56117/100000000000000000 : ℝ)*base90 + hcertificate_margin
  have s1_pow0 : (34209/50000 : ℝ) ^ (75/16 : ℝ) ≤ (4219890094897538077/25000000000000000000 : ℝ) := by
    have hpowers : (34209/50000 : ℝ)^75 ≤ (4219890094897538077/25000000000000000000 : ℝ)^16 := by
      have hnat : (34209 : ℕ)^75*25000000000000000000^16 ≤ 4219890094897538077^16*50000^75 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        34209 50000 4219890094897538077 25000000000000000000 75 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (34209/50000 : ℝ)) (X := (4219890094897538077/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 75 16 (by norm_num) hpowers
    exact h
  have s1_corner0a : (29219890094897538077/25000000000000000000 : ℝ) ≤ (10338341998953163/10000000000000000 : ℝ) ^ (75/16 : ℝ) := by
    have hpowers : (29219890094897538077/25000000000000000000 : ℝ)^16 ≤ (10338341998953163/10000000000000000 : ℝ)^75 := by
      have hnat : (29219890094897538077 : ℕ)^16*10000000000000000^75 ≤ 10338341998953163^75*25000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        29219890094897538077 25000000000000000000 10338341998953163 10000000000000000 16 75 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10338341998953163/10000000000000000 : ℝ)) (X := (29219890094897538077/25000000000000000000 : ℝ)) (by norm_num) 75 16 (by norm_num) hpowers
    exact h
  have s1_corner0b : (16719890094897538077/12500000000000000000 : ℝ) ≤ (2128036088970663/2000000000000000 : ℝ) ^ (75/16 : ℝ) := by
    have hpowers : (16719890094897538077/12500000000000000000 : ℝ)^16 ≤ (2128036088970663/2000000000000000 : ℝ)^75 := by
      have hnat : (16719890094897538077 : ℕ)^16*2000000000000000^75 ≤ 2128036088970663^75*12500000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        16719890094897538077 12500000000000000000 2128036088970663 2000000000000000 16 75 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2128036088970663/2000000000000000 : ℝ)) (X := (16719890094897538077/12500000000000000000 : ℝ)) (by norm_num) 75 16 (by norm_num) hpowers
    exact h
  have major_s1_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(112780666317721/2280600000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(5389972248217/122175000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (75/16 : ℝ)) (rho := (34209/50000 : ℝ)) (alpha := (112780666317721/2280600000000000 : ℝ)) (beta := (5389972248217/122175000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow0,s1_corner0a]) (by linarith only [s1_pow0,s1_corner0b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, false, true], ![true, true, true]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (34209/50000 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_0])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(112780666317721/2280600000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(5389972248217/122175000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s1_pow1 : (30133/50000 : ℝ) ^ (75/16 : ℝ) ≤ (2328247954955048399/25000000000000000000 : ℝ) := by
    have hpowers : (30133/50000 : ℝ)^75 ≤ (2328247954955048399/25000000000000000000 : ℝ)^16 := by
      have hnat : (30133 : ℕ)^75*25000000000000000000^16 ≤ 2328247954955048399^16*50000^75 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        30133 50000 2328247954955048399 25000000000000000000 75 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (30133/50000 : ℝ)) (X := (2328247954955048399/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 75 16 (by norm_num) hpowers
    exact h
  have s1_corner1a : (27328247954955048399/25000000000000000000 : ℝ) ≤ (10191778580275261/10000000000000000 : ℝ) ^ (75/16 : ℝ) := by
    have hpowers : (27328247954955048399/25000000000000000000 : ℝ)^16 ≤ (10191778580275261/10000000000000000 : ℝ)^75 := by
      have hnat : (27328247954955048399 : ℕ)^16*10000000000000000^75 ≤ 10191778580275261^75*25000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        27328247954955048399 25000000000000000000 10191778580275261 10000000000000000 16 75 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10191778580275261/10000000000000000 : ℝ)) (X := (27328247954955048399/25000000000000000000 : ℝ)) (by norm_num) 75 16 (by norm_num) hpowers
    exact h
  have s1_corner1b : (14828247954955048399/12500000000000000000 : ℝ) ≤ (518555248171957/500000000000000 : ℝ) ^ (75/16 : ℝ) := by
    have hpowers : (14828247954955048399/12500000000000000000 : ℝ)^16 ≤ (518555248171957/500000000000000 : ℝ)^75 := by
      have hnat : (14828247954955048399 : ℕ)^16*500000000000000^75 ≤ 518555248171957^75*12500000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14828247954955048399 12500000000000000000 518555248171957 500000000000000 16 75 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (518555248171957/500000000000000 : ℝ)) (X := (14828247954955048399/12500000000000000000 : ℝ)) (by norm_num) 75 16 (by norm_num) hpowers
    exact h
  have major_s1_1 : P 1 ≤ ((-1 : ℝ)*(X 0 1+X 2 1))+(191778580275261/6026600000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 2 0))+(179326383163879/6026600000000000 : ℝ)*((1 : ℝ)*(X 0 2+X 2 2)) := by
    have hh := chart_majorant (a := (75/16 : ℝ)) (rho := (30133/50000 : ℝ)) (alpha := (191778580275261/6026600000000000 : ℝ)) (beta := (179326383163879/6026600000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow1,s1_corner1a]) (by linarith only [s1_pow1,s1_corner1b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, false, true], ![true, true, true]] hX 1 (by
        change ((1 : ℝ)*pair X 1 0) ≤ (30133/50000 : ℝ)*((-1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_1])
    change lpNorm p (pair X 1) ≤ ((-1 : ℝ)*pair X 1 1)+(191778580275261/6026600000000000 : ℝ)*((1 : ℝ)*pair X 1 0)+(179326383163879/6026600000000000 : ℝ)*((1 : ℝ)*pair X 1 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s1_pow2 : (78431/100000 : ℝ) ^ (75/16 : ℝ) ≤ (16009631782326538091/50000000000000000000 : ℝ) := by
    have hpowers : (78431/100000 : ℝ)^75 ≤ (16009631782326538091/50000000000000000000 : ℝ)^16 := by
      have hnat : (78431 : ℕ)^75*50000000000000000000^16 ≤ 16009631782326538091^16*100000^75 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        78431 100000 16009631782326538091 50000000000000000000 75 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (78431/100000 : ℝ)) (X := (16009631782326538091/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 75 16 (by norm_num) hpowers
    exact h
  have s1_corner2a : (66009631782326538091/50000000000000000000 : ℝ) ≤ (5305251329999807/5000000000000000 : ℝ) ^ (75/16 : ℝ) := by
    have hpowers : (66009631782326538091/50000000000000000000 : ℝ)^16 ≤ (5305251329999807/5000000000000000 : ℝ)^75 := by
      have hnat : (66009631782326538091 : ℕ)^16*5000000000000000^75 ≤ 5305251329999807^75*50000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        66009631782326538091 50000000000000000000 5305251329999807 5000000000000000 16 75 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5305251329999807/5000000000000000 : ℝ)) (X := (66009631782326538091/50000000000000000000 : ℝ)) (by norm_num) 75 16 (by norm_num) hpowers
    exact h
  have s1_corner2b : (41009631782326538091/25000000000000000000 : ℝ) ≤ (11113609095262311/10000000000000000 : ℝ) ^ (75/16 : ℝ) := by
    have hpowers : (41009631782326538091/25000000000000000000 : ℝ)^16 ≤ (11113609095262311/10000000000000000 : ℝ)^75 := by
      have hnat : (41009631782326538091 : ℕ)^16*10000000000000000^75 ≤ 11113609095262311^75*25000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        41009631782326538091 25000000000000000000 11113609095262311 10000000000000000 16 75 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (11113609095262311/10000000000000000 : ℝ)) (X := (41009631782326538091/25000000000000000000 : ℝ)) (by norm_num) 75 16 (by norm_num) hpowers
    exact h
  have major_s1_2 : P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2))+(305251329999807/3921550000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 1 0))+(503106435262697/7843100000000000 : ℝ)*((1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (75/16 : ℝ)) (rho := (78431/100000 : ℝ)) (alpha := (305251329999807/3921550000000000 : ℝ)) (beta := (503106435262697/7843100000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow2,s1_corner2a]) (by linarith only [s1_pow2,s1_corner2b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, false, true], ![true, true, true]] hX 2 (by
        change ((1 : ℝ)*pair X 2 0) ≤ (78431/100000 : ℝ)*((1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_2])
    change lpNorm p (pair X 2) ≤ ((1 : ℝ)*pair X 2 2)+(305251329999807/3921550000000000 : ℝ)*((1 : ℝ)*pair X 2 0)+(503106435262697/7843100000000000 : ℝ)*((1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s1_0 : ((-383510189/2500000000 : ℝ)*X 0 0+(-1362817821/2500000000 : ℝ)*X 0 1+(209209943/400000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c315047_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_1 : ((2538741297/5000000000 : ℝ)*X 1 0+(31620609/80000000 : ℝ)*X 1 1+(3493219433/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c315047_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_2 : ((4945771069/10000000000 : ℝ)*X 2 0+(-4070113577/10000000000 : ℝ)*X 2 1+(-351611053/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c315047_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_6 : ((3102367587/5000000000 : ℝ)*X 0 0+(-1440631933/10000000000 : ℝ)*X 0 1+(4508838287/10000000000 : ℝ)*X 0 2+(3102367587/5000000000 : ℝ)*X 1 0+(-1440631933/10000000000 : ℝ)*X 1 1+(4508838287/10000000000 : ℝ)*X 1 2+(3102367587/5000000000 : ℝ)*X 2 0+(-1440631933/10000000000 : ℝ)*X 2 1+(4508838287/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c315047_s1_6 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have hsep : (-373977/50000 : ℝ) < ((-174659/100000 : ℝ)*P 0+(-174659/100000 : ℝ)*P 1+(-174659/100000 : ℝ)*P 2+(1 : ℝ)*T) := by
    have hcertificate_margin : (-373977/50000 : ℝ) < (-502395285028072754282613847685307407/67373522915422500000000000000000000 : ℝ) := by norm_num
    linear_combination (5953/500000000000 : ℝ)*(base8) + (123853/1000000000000 : ℝ)*(base13) + (465261/1000000000000 : ℝ)*(base21) + (32737/500000000000 : ℝ)*(base39) + (252239002227/500000000000 : ℝ)*(base40) + (47635354087/1000000000000 : ℝ)*(base50) + (33877407447/250000000000 : ℝ)*(base59) + (22103/1000000000000 : ℝ)*(base60) + (174659/100000 : ℝ)*(major_s1_0) + (174659/100000 : ℝ)*(major_s1_1) + (174659/100000 : ℝ)*(major_s1_2) + (1242810815109/500000000000 : ℝ)*(sp_s1_0) + (2485621765977/1000000000000 : ℝ)*(sp_s1_1) + (621405325179/250000000000 : ℝ)*(sp_s1_2) + (1 : ℝ)*(sp_s1_6) + (2485621765977/1000000000000 : ℝ)*(f.sum) + (1682029948315697377/2954201653750000000000000000000 : ℝ)*base62 + (411728505241/98038750000000000000000000 : ℝ)*base64 + (449519028671/6026600000000000000000000 : ℝ)*base66 + (182737500066839/392155000000000000000000000 : ℝ)*base68 + (21333246035031149/71547895440000000000000000000 : ℝ)*base70 + (18404570102633/48870000000000000000000000 : ℝ)*base73 + (58064130019683/75332500000000000000000000 : ℝ)*base74 + (1911988832951/28507500000000000000000000 : ℝ)*base76 + (30741787181856377/36814992750000000000000000000 : ℝ)*base79 + hcertificate_margin
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
theorem coarse_distinct_p015_b023 (p : ℝ) (hpa : (75/16 : ℝ) ≤ p) (hpb : p ≤ (19/4 : ℝ))
    (c : Fin 88) (hlo : 47 ≤ c.val) (hhi : c.val < 55)
    (hn63 : c ≠ 63) (hn87 : c ≠ 87)
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (174659/100000 : ℝ) (34911/20000 : ℝ) (15821/20000 : ℝ) X (distinctOrders c) (distinctSigns c)) : False := by
  have hc : c=47 ∨ c=48 ∨ c=49 ∨ c=50 ∨ c=51 ∨ c=52 ∨ c=53 ∨ c=54 := by omega
  rcases hc with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  · exact collision_c315047 p hpa (by linarith only [hpb]) X hX
  · exact collision_c314048 p (by linarith only [hpa]) (by linarith only [hpb]) X (orderedChart_weaken
      (by linarith only [hpa]) hX (by norm_num) (by norm_num) (by norm_num))
  · exact collision_c314049 p (by linarith only [hpa]) (by linarith only [hpb]) X (orderedChart_weaken
      (by linarith only [hpa]) hX (by norm_num) (by norm_num) (by norm_num))
  · exact collision_c314050 p (by linarith only [hpa]) (by linarith only [hpb]) X (orderedChart_weaken
      (by linarith only [hpa]) hX (by norm_num) (by norm_num) (by norm_num))
  · exact collision_c314051 p (by linarith only [hpa]) (by linarith only [hpb]) X (orderedChart_weaken
      (by linarith only [hpa]) hX (by norm_num) (by norm_num) (by norm_num))
  · exact collision_c314052 p (by linarith only [hpa]) (by linarith only [hpb]) X (orderedChart_weaken
      (by linarith only [hpa]) hX (by norm_num) (by norm_num) (by norm_num))
  · exact collision_c315053 p hpa (by linarith only [hpb]) X hX
  · exact collision_c315054 p hpa (by linarith only [hpb]) X hX

end HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p : ℝ) (hpa : (75/16 : ℝ) ≤ p) (hpb : p ≤ (19/4 : ℝ))
    (c : Fin 88) (hlo : 47 ≤ c.val) (hhi : c.val < 55)
    (hn63 : c ≠ 63) (hn87 : c ≠ 87)
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (174659/100000 : ℝ) (34911/20000 : ℝ) (15821/20000 : ℝ) X (distinctOrders c) (distinctSigns c)) : False := by
  exact HlawkaSchatten.DiagonalCutoff4.coarse_distinct_p015_b023 p hpa hpb c hlo hhi hn63 hn87 X hX

#print axioms solution
