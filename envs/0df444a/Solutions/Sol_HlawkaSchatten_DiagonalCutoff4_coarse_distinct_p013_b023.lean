-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.coarse_distinct_p013_b023
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T00:32:08.823129+00:00
-- url     : https://prove2.me/submissions/f50c3dbc-9a8b-4c68-84b0-37e429487261

import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_collision_c312047_s0
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_collision_c312047_s1
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_collision_c312047_s2
import Definitions.Def_HlawkaSchatten_DiagonalCutoff4_Localization
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_collision_c312048_s0
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_collision_c312048_s1
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_collision_c312048_s2
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_collision_c312049_s0
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_collision_c312049_s1
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_collision_c312049_s2
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_collision_c312050_s0
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_collision_c312050_s1
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_collision_c312050_s2
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_collision_c312051_s0
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_collision_c312051_s1
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_collision_c312051_s2
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_collision_c312052_s0
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_collision_c312052_s1
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_collision_c312052_s2
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_collision_c313053_s0
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_collision_c313053_s1
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_collision_c313053_s2
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_collision_c313053_s3
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
theorem HlawkaSchatten.DiagonalCutoff4.collision_c312047 (p : ℝ) (hpa : (9/2 : ℝ) ≤ p) (hpb : p ≤ (37/8 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (166913/100000 : ℝ) (178281/100000 : ℝ) (78337/100000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, false, true], ![true, true, true]]) : False := by
  have h0 := collision_c312047_s0 p hpa hpb X hX
  have h1 := collision_c312047_s1 p hpa hpb X hX h0
  exact collision_c312047_s2 p hpa hpb X hX h1

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6 HlawkaSchatten.DiagonalCutoff4
theorem HlawkaSchatten.DiagonalCutoff4.collision_c312048 (p : ℝ) (hpa : (9/2 : ℝ) ≤ p) (hpb : p ≤ (37/8 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (166913/100000 : ℝ) (178281/100000 : ℝ) (78337/100000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![false, false, false]]) : False := by
  have h0 := collision_c312048_s0 p hpa hpb X hX
  have h1 := collision_c312048_s1 p hpa hpb X hX h0
  exact collision_c312048_s2 p hpa hpb X hX h1

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6 HlawkaSchatten.DiagonalCutoff4
theorem HlawkaSchatten.DiagonalCutoff4.collision_c312049 (p : ℝ) (hpa : (9/2 : ℝ) ≤ p) (hpb : p ≤ (37/8 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (166913/100000 : ℝ) (178281/100000 : ℝ) (78337/100000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![false, false, true]]) : False := by
  have h0 := collision_c312049_s0 p hpa hpb X hX
  have h1 := collision_c312049_s1 p hpa hpb X hX h0
  exact collision_c312049_s2 p hpa hpb X hX h1

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6 HlawkaSchatten.DiagonalCutoff4
theorem HlawkaSchatten.DiagonalCutoff4.collision_c312050 (p : ℝ) (hpa : (9/2 : ℝ) ≤ p) (hpb : p ≤ (37/8 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (166913/100000 : ℝ) (178281/100000 : ℝ) (78337/100000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![false, true, false]]) : False := by
  have h0 := collision_c312050_s0 p hpa hpb X hX
  have h1 := collision_c312050_s1 p hpa hpb X hX h0
  exact collision_c312050_s2 p hpa hpb X hX h1

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6 HlawkaSchatten.DiagonalCutoff4
theorem HlawkaSchatten.DiagonalCutoff4.collision_c312051 (p : ℝ) (hpa : (9/2 : ℝ) ≤ p) (hpb : p ≤ (37/8 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (166913/100000 : ℝ) (178281/100000 : ℝ) (78337/100000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![false, true, true]]) : False := by
  have h0 := collision_c312051_s0 p hpa hpb X hX
  have h1 := collision_c312051_s1 p hpa hpb X hX h0
  exact collision_c312051_s2 p hpa hpb X hX h1

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6 HlawkaSchatten.DiagonalCutoff4
theorem HlawkaSchatten.DiagonalCutoff4.collision_c312052 (p : ℝ) (hpa : (9/2 : ℝ) ≤ p) (hpb : p ≤ (37/8 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (166913/100000 : ℝ) (178281/100000 : ℝ) (78337/100000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![true, false, false]]) : False := by
  have h0 := collision_c312052_s0 p hpa hpb X hX
  have h1 := collision_c312052_s1 p hpa hpb X hX h0
  exact collision_c312052_s2 p hpa hpb X hX h1

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6 HlawkaSchatten.DiagonalCutoff4
theorem HlawkaSchatten.DiagonalCutoff4.collision_c313053 (p : ℝ) (hpa : (73/16 : ℝ) ≤ p) (hpb : p ≤ (37/8 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (169487/100000 : ℝ) (176973/100000 : ℝ) (78599/100000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![true, false, true]]) : False := by
  have h0 := collision_c313053_s0 p hpa hpb X hX
  have h1 := collision_c313053_s1 p hpa hpb X hX h0
  have h2 := collision_c313053_s2 p hpa hpb X hX h1
  exact collision_c313053_s3 p hpa hpb X hX h2

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
theorem collision_support_c313046_s0_0 (p : ℝ) (hpa : (73/16 : ℝ) ≤ p) (hpb : p ≤ (75/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-537522217/5000000000 : ℝ)*x 0 + (-5527342521/10000000000 : ℝ)*x 1 + (-5527342519/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (537522217/5000000000 : ℝ)^75 ≤ (5871680175027/100000000000000 : ℝ)^59 := by
    have hnat : (537522217 : ℕ)^75*100000000000000^59 ≤ 5871680175027^59*5000000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      537522217 5000000000 5871680175027 100000000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5527342521/10000000000 : ℝ)^75 ≤ (1176603997779/2500000000000 : ℝ)^59 := by
    have hnat : (5527342521 : ℕ)^75*2500000000000^59 ≤ 1176603997779^59*10000000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5527342521 10000000000 1176603997779 2500000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5527342519/10000000000 : ℝ)^75 ≤ (5883019986189/12500000000000 : ℝ)^59 := by
    have hnat : (5527342519 : ℕ)^75*12500000000000^59 ≤ 5883019986189^59*10000000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5527342519 10000000000 5883019986189 12500000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (75/16 : ℝ)) 75 59 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-537522217/5000000000 : ℝ), (-5527342521/10000000000 : ℝ), (-5527342519/10000000000 : ℝ)] ![(5871680175027/100000000000000 : ℝ), (1176603997779/2500000000000 : ℝ), (5883019986189/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-537522217/5000000000 : ℝ)|^75 ≤ (5871680175027/100000000000000 : ℝ)^59
        have hw : |(-537522217/5000000000 : ℝ)|=(537522217/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-5527342521/10000000000 : ℝ)|^75 ≤ (1176603997779/2500000000000 : ℝ)^59
        have hw : |(-5527342521/10000000000 : ℝ)|=(5527342521/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-5527342519/10000000000 : ℝ)|^75 ≤ (5883019986189/12500000000000 : ℝ)^59
        have hw : |(-5527342519/10000000000 : ℝ)|=(5527342519/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c313046_s0_1 (p : ℝ) (hpa : (73/16 : ℝ) ≤ p) (hpb : p ≤ (75/16 : ℝ)) (x : Fin 3 → ℝ) :
    (48150881/100000000 : ℝ)*x 0 + (390425347/1000000000 : ℝ)*x 1 + (-3904253471/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (48150881/100000000 : ℝ)^75 ≤ (19746985848307/50000000000000 : ℝ)^59 := by
    have hnat : (48150881 : ℕ)^75*50000000000000^59 ≤ 19746985848307^59*100000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      48150881 100000000 19746985848307 50000000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (390425347/1000000000 : ℝ)^75 ≤ (30253014140513/100000000000000 : ℝ)^59 := by
    have hnat : (390425347 : ℕ)^75*100000000000000^59 ≤ 30253014140513^59*1000000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      390425347 1000000000 30253014140513 100000000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3904253471/10000000000 : ℝ)^75 ≤ (30253014150363/100000000000000 : ℝ)^59 := by
    have hnat : (3904253471 : ℕ)^75*100000000000000^59 ≤ 30253014150363^59*10000000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3904253471 10000000000 30253014150363 100000000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (75/16 : ℝ)) 75 59 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(48150881/100000000 : ℝ), (390425347/1000000000 : ℝ), (-3904253471/10000000000 : ℝ)] ![(19746985848307/50000000000000 : ℝ), (30253014140513/100000000000000 : ℝ), (30253014150363/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(48150881/100000000 : ℝ)|^75 ≤ (19746985848307/50000000000000 : ℝ)^59
        have hw : |(48150881/100000000 : ℝ)|=(48150881/100000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(390425347/1000000000 : ℝ)|^75 ≤ (30253014140513/100000000000000 : ℝ)^59
        have hw : |(390425347/1000000000 : ℝ)|=(390425347/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-3904253471/10000000000 : ℝ)|^75 ≤ (30253014150363/100000000000000 : ℝ)^59
        have hw : |(-3904253471/10000000000 : ℝ)|=(3904253471/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c313046_s0_2 (p : ℝ) (hpa : (73/16 : ℝ) ≤ p) (hpb : p ≤ (75/16 : ℝ)) (x : Fin 3 → ℝ) :
    (48150881/100000000 : ℝ)*x 0 + (-390425347/1000000000 : ℝ)*x 1 + (3904253471/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (48150881/100000000 : ℝ)^75 ≤ (19746985848307/50000000000000 : ℝ)^59 := by
    have hnat : (48150881 : ℕ)^75*50000000000000^59 ≤ 19746985848307^59*100000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      48150881 100000000 19746985848307 50000000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (390425347/1000000000 : ℝ)^75 ≤ (30253014140513/100000000000000 : ℝ)^59 := by
    have hnat : (390425347 : ℕ)^75*100000000000000^59 ≤ 30253014140513^59*1000000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      390425347 1000000000 30253014140513 100000000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3904253471/10000000000 : ℝ)^75 ≤ (30253014150363/100000000000000 : ℝ)^59 := by
    have hnat : (3904253471 : ℕ)^75*100000000000000^59 ≤ 30253014150363^59*10000000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3904253471 10000000000 30253014150363 100000000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (75/16 : ℝ)) 75 59 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(48150881/100000000 : ℝ), (-390425347/1000000000 : ℝ), (3904253471/10000000000 : ℝ)] ![(19746985848307/50000000000000 : ℝ), (30253014140513/100000000000000 : ℝ), (30253014150363/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(48150881/100000000 : ℝ)|^75 ≤ (19746985848307/50000000000000 : ℝ)^59
        have hw : |(48150881/100000000 : ℝ)|=(48150881/100000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-390425347/1000000000 : ℝ)|^75 ≤ (30253014140513/100000000000000 : ℝ)^59
        have hw : |(-390425347/1000000000 : ℝ)|=(390425347/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3904253471/10000000000 : ℝ)|^75 ≤ (30253014150363/100000000000000 : ℝ)^59
        have hw : |(3904253471/10000000000 : ℝ)|=(3904253471/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c313046_s0_3 (p : ℝ) (hpa : (73/16 : ℝ) ≤ p) (hpb : p ≤ (75/16 : ℝ)) (x : Fin 3 → ℝ) :
    (1 : ℝ)*x 0 + (0 : ℝ)*x 1 + (0 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1 : ℝ)^75 ≤ (1 : ℝ)^59 := by
    have hnat : (1 : ℕ)^75*1^59 ≤ 1^59*1^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1 1 1 1 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (0 : ℝ)^75 ≤ (0 : ℝ)^59 := by
    have hnat : (0 : ℕ)^75*1^59 ≤ 0^59*1^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      0 1 0 1 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (0 : ℝ)^75 ≤ (0 : ℝ)^59 := by
    have hnat : (0 : ℕ)^75*1^59 ≤ 0^59*1^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      0 1 0 1 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (75/16 : ℝ)) 75 59 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1 : ℝ), (0 : ℝ), (0 : ℝ)] ![(1 : ℝ), (0 : ℝ), (0 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1 : ℝ)|^75 ≤ (1 : ℝ)^59
        have hw : |(1 : ℝ)|=(1 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(0 : ℝ)|^75 ≤ (0 : ℝ)^59
        have hw : |(0 : ℝ)|=(0 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(0 : ℝ)|^75 ≤ (0 : ℝ)^59
        have hw : |(0 : ℝ)|=(0 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c313046_s0_6 (p : ℝ) (hpa : (73/16 : ℝ) ≤ p) (hpb : p ≤ (75/16 : ℝ)) (x : Fin 3 → ℝ) :
    (8147429049/10000000000 : ℝ)*x 0 + (-363962907/2000000000 : ℝ)*x 1 + (-363962907/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (8147429049/10000000000 : ℝ)^75 ≤ (9633865746831/12500000000000 : ℝ)^59 := by
    have hnat : (8147429049 : ℕ)^75*12500000000000^59 ≤ 9633865746831^59*10000000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      8147429049 10000000000 9633865746831 12500000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (363962907/2000000000 : ℝ)^75 ≤ (11464537006053/100000000000000 : ℝ)^59 := by
    have hnat : (363962907 : ℕ)^75*100000000000000^59 ≤ 11464537006053^59*2000000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      363962907 2000000000 11464537006053 100000000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (363962907/2000000000 : ℝ)^75 ≤ (11464537006053/100000000000000 : ℝ)^59 := by
    have hnat : (363962907 : ℕ)^75*100000000000000^59 ≤ 11464537006053^59*2000000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      363962907 2000000000 11464537006053 100000000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (75/16 : ℝ)) 75 59 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(8147429049/10000000000 : ℝ), (-363962907/2000000000 : ℝ), (-363962907/2000000000 : ℝ)] ![(9633865746831/12500000000000 : ℝ), (11464537006053/100000000000000 : ℝ), (11464537006053/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(8147429049/10000000000 : ℝ)|^75 ≤ (9633865746831/12500000000000 : ℝ)^59
        have hw : |(8147429049/10000000000 : ℝ)|=(8147429049/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-363962907/2000000000 : ℝ)|^75 ≤ (11464537006053/100000000000000 : ℝ)^59
        have hw : |(-363962907/2000000000 : ℝ)|=(363962907/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-363962907/2000000000 : ℝ)|^75 ≤ (11464537006053/100000000000000 : ℝ)^59
        have hw : |(-363962907/2000000000 : ℝ)|=(363962907/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c313046_s0_7 (p : ℝ) (hpa : (73/16 : ℝ) ≤ p) (hpb : p ≤ (75/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-222758273/2000000000 : ℝ)*x 0 + (-1154118589/2000000000 : ℝ)*x 1 + (-5255851/10000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (222758273/2000000000 : ℝ)^75 ≤ (3071001147983/50000000000000 : ℝ)^59 := by
    have hnat : (222758273 : ℕ)^75*50000000000000^59 ≤ 3071001147983^59*2000000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      222758273 2000000000 3071001147983 50000000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1154118589/2000000000 : ℝ)^75 ≤ (6214077632591/12500000000000 : ℝ)^59 := by
    have hnat : (1154118589 : ℕ)^75*12500000000000^59 ≤ 6214077632591^59*2000000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1154118589 2000000000 6214077632591 12500000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5255851/10000000 : ℝ)^75 ≤ (137954301967/312500000000 : ℝ)^59 := by
    have hnat : (5255851 : ℕ)^75*312500000000^59 ≤ 137954301967^59*10000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5255851 10000000 137954301967 312500000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (75/16 : ℝ)) 75 59 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-222758273/2000000000 : ℝ), (-1154118589/2000000000 : ℝ), (-5255851/10000000 : ℝ)] ![(3071001147983/50000000000000 : ℝ), (6214077632591/12500000000000 : ℝ), (137954301967/312500000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-222758273/2000000000 : ℝ)|^75 ≤ (3071001147983/50000000000000 : ℝ)^59
        have hw : |(-222758273/2000000000 : ℝ)|=(222758273/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1154118589/2000000000 : ℝ)|^75 ≤ (6214077632591/12500000000000 : ℝ)^59
        have hw : |(-1154118589/2000000000 : ℝ)|=(1154118589/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-5255851/10000000 : ℝ)|^75 ≤ (137954301967/312500000000 : ℝ)^59
        have hw : |(-5255851/10000000 : ℝ)|=(5255851/10000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c313046_s0_8 (p : ℝ) (hpa : (73/16 : ℝ) ≤ p) (hpb : p ≤ (75/16 : ℝ)) (x : Fin 3 → ℝ) :
    (467043923/1000000000 : ℝ)*x 0 + (179335091/400000000 : ℝ)*x 1 + (-1729642131/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (467043923/1000000000 : ℝ)^75 ≤ (37991988405697/100000000000000 : ℝ)^59 := by
    have hnat : (467043923 : ℕ)^75*100000000000000^59 ≤ 37991988405697^59*1000000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      467043923 1000000000 37991988405697 100000000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (179335091/400000000 : ℝ)^75 ≤ (36068274294909/100000000000000 : ℝ)^59 := by
    have hnat : (179335091 : ℕ)^75*100000000000000^59 ≤ 36068274294909^59*400000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      179335091 400000000 36068274294909 100000000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1729642131/5000000000 : ℝ)^75 ≤ (6484934322411/25000000000000 : ℝ)^59 := by
    have hnat : (1729642131 : ℕ)^75*25000000000000^59 ≤ 6484934322411^59*5000000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1729642131 5000000000 6484934322411 25000000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (75/16 : ℝ)) 75 59 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(467043923/1000000000 : ℝ), (179335091/400000000 : ℝ), (-1729642131/5000000000 : ℝ)] ![(37991988405697/100000000000000 : ℝ), (36068274294909/100000000000000 : ℝ), (6484934322411/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(467043923/1000000000 : ℝ)|^75 ≤ (37991988405697/100000000000000 : ℝ)^59
        have hw : |(467043923/1000000000 : ℝ)|=(467043923/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(179335091/400000000 : ℝ)|^75 ≤ (36068274294909/100000000000000 : ℝ)^59
        have hw : |(179335091/400000000 : ℝ)|=(179335091/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1729642131/5000000000 : ℝ)|^75 ≤ (6484934322411/25000000000000 : ℝ)^59
        have hw : |(-1729642131/5000000000 : ℝ)|=(1729642131/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c313046_s0_9 (p : ℝ) (hpa : (73/16 : ℝ) ≤ p) (hpb : p ≤ (75/16 : ℝ)) (x : Fin 3 → ℝ) :
    (934087843/2000000000 : ℝ)*x 0 + (-844046109/2500000000 : ℝ)*x 1 + (1140100397/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (934087843/2000000000 : ℝ)^75 ≤ (37991988250589/100000000000000 : ℝ)^59 := by
    have hnat : (934087843 : ℕ)^75*100000000000000^59 ≤ 37991988250589^59*2000000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      934087843 2000000000 37991988250589 100000000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (844046109/2500000000 : ℝ)^75 ≤ (25150216806467/100000000000000 : ℝ)^59 := by
    have hnat : (844046109 : ℕ)^75*100000000000000^59 ≤ 25150216806467^59*2500000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      844046109 2500000000 25150216806467 100000000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1140100397/2500000000 : ℝ)^75 ≤ (1474311797431/4000000000000 : ℝ)^59 := by
    have hnat : (1140100397 : ℕ)^75*4000000000000^59 ≤ 1474311797431^59*2500000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1140100397 2500000000 1474311797431 4000000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (75/16 : ℝ)) 75 59 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(934087843/2000000000 : ℝ), (-844046109/2500000000 : ℝ), (1140100397/2500000000 : ℝ)] ![(37991988250589/100000000000000 : ℝ), (25150216806467/100000000000000 : ℝ), (1474311797431/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(934087843/2000000000 : ℝ)|^75 ≤ (37991988250589/100000000000000 : ℝ)^59
        have hw : |(934087843/2000000000 : ℝ)|=(934087843/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-844046109/2500000000 : ℝ)|^75 ≤ (25150216806467/100000000000000 : ℝ)^59
        have hw : |(-844046109/2500000000 : ℝ)|=(844046109/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1140100397/2500000000 : ℝ)|^75 ≤ (1474311797431/4000000000000 : ℝ)^59
        have hw : |(1140100397/2500000000 : ℝ)|=(1140100397/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c313046_s0_13 (p : ℝ) (hpa : (73/16 : ℝ) ≤ p) (hpb : p ≤ (75/16 : ℝ)) (x : Fin 3 → ℝ) :
    (4111612709/5000000000 : ℝ)*x 0 + (-331218603/2500000000 : ℝ)*x 1 + (-2172318001/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4111612709/5000000000 : ℝ)^75 ≤ (77983512183603/100000000000000 : ℝ)^59 := by
    have hnat : (4111612709 : ℕ)^75*100000000000000^59 ≤ 77983512183603^59*5000000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4111612709 5000000000 77983512183603 100000000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (331218603/2500000000 : ℝ)^75 ≤ (7658088785903/100000000000000 : ℝ)^59 := by
    have hnat : (331218603 : ℕ)^75*100000000000000^59 ≤ 7658088785903^59*2500000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      331218603 2500000000 7658088785903 100000000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2172318001/10000000000 : ℝ)^75 ≤ (179479987761/1250000000000 : ℝ)^59 := by
    have hnat : (2172318001 : ℕ)^75*1250000000000^59 ≤ 179479987761^59*10000000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2172318001 10000000000 179479987761 1250000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (75/16 : ℝ)) 75 59 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4111612709/5000000000 : ℝ), (-331218603/2500000000 : ℝ), (-2172318001/10000000000 : ℝ)] ![(77983512183603/100000000000000 : ℝ), (7658088785903/100000000000000 : ℝ), (179479987761/1250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4111612709/5000000000 : ℝ)|^75 ≤ (77983512183603/100000000000000 : ℝ)^59
        have hw : |(4111612709/5000000000 : ℝ)|=(4111612709/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-331218603/2500000000 : ℝ)|^75 ≤ (7658088785903/100000000000000 : ℝ)^59
        have hw : |(-331218603/2500000000 : ℝ)|=(331218603/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2172318001/10000000000 : ℝ)|^75 ≤ (179479987761/1250000000000 : ℝ)^59
        have hw : |(-2172318001/10000000000 : ℝ)|=(2172318001/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c313046_s0_14 (p : ℝ) (hpa : (73/16 : ℝ) ≤ p) (hpb : p ≤ (75/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-316116813/10000000000 : ℝ)*x 0 + (-2753162551/5000000000 : ℝ)*x 1 + (-2985807799/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (316116813/10000000000 : ℝ)^75 ≤ (77429529623/6250000000000 : ℝ)^59 := by
    have hnat : (316116813 : ℕ)^75*6250000000000^59 ≤ 77429529623^59*10000000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      316116813 10000000000 77429529623 6250000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2753162551/5000000000 : ℝ)^75 ≤ (5854598397009/12500000000000 : ℝ)^59 := by
    have hnat : (2753162551 : ℕ)^75*12500000000000^59 ≤ 5854598397009^59*5000000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2753162551 5000000000 5854598397009 12500000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2985807799/5000000000 : ℝ)^75 ≤ (51924340336307/100000000000000 : ℝ)^59 := by
    have hnat : (2985807799 : ℕ)^75*100000000000000^59 ≤ 51924340336307^59*5000000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2985807799 5000000000 51924340336307 100000000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (75/16 : ℝ)) 75 59 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-316116813/10000000000 : ℝ), (-2753162551/5000000000 : ℝ), (-2985807799/5000000000 : ℝ)] ![(77429529623/6250000000000 : ℝ), (5854598397009/12500000000000 : ℝ), (51924340336307/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-316116813/10000000000 : ℝ)|^75 ≤ (77429529623/6250000000000 : ℝ)^59
        have hw : |(-316116813/10000000000 : ℝ)|=(316116813/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2753162551/5000000000 : ℝ)|^75 ≤ (5854598397009/12500000000000 : ℝ)^59
        have hw : |(-2753162551/5000000000 : ℝ)|=(2753162551/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2985807799/5000000000 : ℝ)|^75 ≤ (51924340336307/100000000000000 : ℝ)^59
        have hw : |(-2985807799/5000000000 : ℝ)|=(2985807799/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c313046_s0_15 (p : ℝ) (hpa : (73/16 : ℝ) ≤ p) (hpb : p ≤ (75/16 : ℝ)) (x : Fin 3 → ℝ) :
    (4344297703/10000000000 : ℝ)*x 0 + (802635357/2000000000 : ℝ)*x 1 + (-4281652683/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4344297703/10000000000 : ℝ)^75 ≤ (1386079911249/4000000000000 : ℝ)^59 := by
    have hnat : (4344297703 : ℕ)^75*4000000000000^59 ≤ 1386079911249^59*10000000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4344297703 10000000000 1386079911249 4000000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (802635357/2000000000 : ℝ)^75 ≤ (15664974659961/50000000000000 : ℝ)^59 := by
    have hnat : (802635357 : ℕ)^75*50000000000000^59 ≤ 15664974659961^59*2000000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      802635357 2000000000 15664974659961 50000000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4281652683/10000000000 : ℝ)^75 ≤ (6803610575991/20000000000000 : ℝ)^59 := by
    have hnat : (4281652683 : ℕ)^75*20000000000000^59 ≤ 6803610575991^59*10000000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4281652683 10000000000 6803610575991 20000000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (75/16 : ℝ)) 75 59 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4344297703/10000000000 : ℝ), (802635357/2000000000 : ℝ), (-4281652683/10000000000 : ℝ)] ![(1386079911249/4000000000000 : ℝ), (15664974659961/50000000000000 : ℝ), (6803610575991/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4344297703/10000000000 : ℝ)|^75 ≤ (1386079911249/4000000000000 : ℝ)^59
        have hw : |(4344297703/10000000000 : ℝ)|=(4344297703/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(802635357/2000000000 : ℝ)|^75 ≤ (15664974659961/50000000000000 : ℝ)^59
        have hw : |(802635357/2000000000 : ℝ)|=(802635357/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-4281652683/10000000000 : ℝ)|^75 ≤ (6803610575991/20000000000000 : ℝ)^59
        have hw : |(-4281652683/10000000000 : ℝ)|=(4281652683/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c313046_s0_16 (p : ℝ) (hpa : (73/16 : ℝ) ≤ p) (hpb : p ≤ (75/16 : ℝ)) (x : Fin 3 → ℝ) :
    (5612529671/10000000000 : ℝ)*x 0 + (-1676780107/5000000000 : ℝ)*x 1 + (3577908689/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5612529671/10000000000 : ℝ)^75 ≤ (2399406778223/5000000000000 : ℝ)^59 := by
    have hnat : (5612529671 : ℕ)^75*5000000000000^59 ≤ 2399406778223^59*10000000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5612529671 10000000000 2399406778223 5000000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1676780107/5000000000 : ℝ)^75 ≤ (24936172815829/100000000000000 : ℝ)^59 := by
    have hnat : (1676780107 : ℕ)^75*100000000000000^59 ≤ 24936172815829^59*5000000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1676780107 5000000000 24936172815829 100000000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3577908689/10000000000 : ℝ)^75 ≤ (13537845799491/50000000000000 : ℝ)^59 := by
    have hnat : (3577908689 : ℕ)^75*50000000000000^59 ≤ 13537845799491^59*10000000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3577908689 10000000000 13537845799491 50000000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (75/16 : ℝ)) 75 59 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5612529671/10000000000 : ℝ), (-1676780107/5000000000 : ℝ), (3577908689/10000000000 : ℝ)] ![(2399406778223/5000000000000 : ℝ), (24936172815829/100000000000000 : ℝ), (13537845799491/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5612529671/10000000000 : ℝ)|^75 ≤ (2399406778223/5000000000000 : ℝ)^59
        have hw : |(5612529671/10000000000 : ℝ)|=(5612529671/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1676780107/5000000000 : ℝ)|^75 ≤ (24936172815829/100000000000000 : ℝ)^59
        have hw : |(-1676780107/5000000000 : ℝ)|=(1676780107/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3577908689/10000000000 : ℝ)|^75 ≤ (13537845799491/50000000000000 : ℝ)^59
        have hw : |(3577908689/10000000000 : ℝ)|=(3577908689/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c313046_s0_19 (p : ℝ) (hpa : (73/16 : ℝ) ≤ p) (hpb : p ≤ (75/16 : ℝ)) (x : Fin 3 → ℝ) :
    (46738679/50000000 : ℝ)*x 0 + (-389341357/5000000000 : ℝ)*x 1 + (-168896451/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (46738679/50000000 : ℝ)^75 ≤ (91783034057/100000000000 : ℝ)^59 := by
    have hnat : (46738679 : ℕ)^75*100000000000^59 ≤ 91783034057^59*50000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      46738679 50000000 91783034057 100000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (389341357/5000000000 : ℝ)^75 ≤ (3896839718041/100000000000000 : ℝ)^59 := by
    have hnat : (389341357 : ℕ)^75*100000000000000^59 ≤ 3896839718041^59*5000000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      389341357 5000000000 3896839718041 100000000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (168896451/2000000000 : ℝ)^75 ≤ (4320126205263/100000000000000 : ℝ)^59 := by
    have hnat : (168896451 : ℕ)^75*100000000000000^59 ≤ 4320126205263^59*2000000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      168896451 2000000000 4320126205263 100000000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (75/16 : ℝ)) 75 59 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(46738679/50000000 : ℝ), (-389341357/5000000000 : ℝ), (-168896451/2000000000 : ℝ)] ![(91783034057/100000000000 : ℝ), (3896839718041/100000000000000 : ℝ), (4320126205263/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(46738679/50000000 : ℝ)|^75 ≤ (91783034057/100000000000 : ℝ)^59
        have hw : |(46738679/50000000 : ℝ)|=(46738679/50000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-389341357/5000000000 : ℝ)|^75 ≤ (3896839718041/100000000000000 : ℝ)^59
        have hw : |(-389341357/5000000000 : ℝ)|=(389341357/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-168896451/2000000000 : ℝ)|^75 ≤ (4320126205263/100000000000000 : ℝ)^59
        have hw : |(-168896451/2000000000 : ℝ)|=(168896451/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c313046_s0_20 (p : ℝ) (hpa : (73/16 : ℝ) ≤ p) (hpb : p ≤ (75/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-39514681/1250000000 : ℝ)*x 0 + (-5971614161/10000000000 : ℝ)*x 1 + (-5506326279/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (39514681/1250000000 : ℝ)^75 ≤ (1238875637427/100000000000000 : ℝ)^59 := by
    have hnat : (39514681 : ℕ)^75*100000000000000^59 ≤ 1238875637427^59*1250000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      39514681 1250000000 1238875637427 100000000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5971614161/10000000000 : ℝ)^75 ≤ (25962162226423/50000000000000 : ℝ)^59 := by
    have hnat : (5971614161 : ℕ)^75*50000000000000^59 ≤ 25962162226423^59*10000000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5971614161 10000000000 25962162226423 50000000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5506326279/10000000000 : ℝ)^75 ≤ (4683679990263/10000000000000 : ℝ)^59 := by
    have hnat : (5506326279 : ℕ)^75*10000000000000^59 ≤ 4683679990263^59*10000000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5506326279 10000000000 4683679990263 10000000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (75/16 : ℝ)) 75 59 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-39514681/1250000000 : ℝ), (-5971614161/10000000000 : ℝ), (-5506326279/10000000000 : ℝ)] ![(1238875637427/100000000000000 : ℝ), (25962162226423/50000000000000 : ℝ), (4683679990263/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-39514681/1250000000 : ℝ)|^75 ≤ (1238875637427/100000000000000 : ℝ)^59
        have hw : |(-39514681/1250000000 : ℝ)|=(39514681/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-5971614161/10000000000 : ℝ)|^75 ≤ (25962162226423/50000000000000 : ℝ)^59
        have hw : |(-5971614161/10000000000 : ℝ)|=(5971614161/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-5506326279/10000000000 : ℝ)|^75 ≤ (4683679990263/10000000000000 : ℝ)^59
        have hw : |(-5506326279/10000000000 : ℝ)|=(5506326279/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c313046_s0_21 (p : ℝ) (hpa : (73/16 : ℝ) ≤ p) (hpb : p ≤ (75/16 : ℝ)) (x : Fin 3 → ℝ) :
    (1403132069/2500000000 : ℝ)*x 0 + (1788954517/5000000000 : ℝ)*x 1 + (-3353561467/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1403132069/2500000000 : ℝ)^75 ≤ (2999257525149/6250000000000 : ℝ)^59 := by
    have hnat : (1403132069 : ℕ)^75*6250000000000^59 ≤ 2999257525149^59*2500000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1403132069 2500000000 2999257525149 6250000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1788954517/5000000000 : ℝ)^75 ≤ (27075694917763/100000000000000 : ℝ)^59 := by
    have hnat : (1788954517 : ℕ)^75*100000000000000^59 ≤ 27075694917763^59*5000000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1788954517 5000000000 27075694917763 100000000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3353561467/10000000000 : ℝ)^75 ≤ (24936184659437/100000000000000 : ℝ)^59 := by
    have hnat : (3353561467 : ℕ)^75*100000000000000^59 ≤ 24936184659437^59*10000000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3353561467 10000000000 24936184659437 100000000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (75/16 : ℝ)) 75 59 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1403132069/2500000000 : ℝ), (1788954517/5000000000 : ℝ), (-3353561467/10000000000 : ℝ)] ![(2999257525149/6250000000000 : ℝ), (27075694917763/100000000000000 : ℝ), (24936184659437/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1403132069/2500000000 : ℝ)|^75 ≤ (2999257525149/6250000000000 : ℝ)^59
        have hw : |(1403132069/2500000000 : ℝ)|=(1403132069/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1788954517/5000000000 : ℝ)|^75 ≤ (27075694917763/100000000000000 : ℝ)^59
        have hw : |(1788954517/5000000000 : ℝ)|=(1788954517/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-3353561467/10000000000 : ℝ)|^75 ≤ (24936184659437/100000000000000 : ℝ)^59
        have hw : |(-3353561467/10000000000 : ℝ)|=(3353561467/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c313046_s0_22 (p : ℝ) (hpa : (73/16 : ℝ) ≤ p) (hpb : p ≤ (75/16 : ℝ)) (x : Fin 3 → ℝ) :
    (543036989/1250000000 : ℝ)*x 0 + (-4281653051/10000000000 : ℝ)*x 1 + (4013178241/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (543036989/1250000000 : ℝ)^75 ≤ (34651979621323/100000000000000 : ℝ)^59 := by
    have hnat : (543036989 : ℕ)^75*100000000000000^59 ≤ 34651979621323^59*1250000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      543036989 1250000000 34651979621323 100000000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4281653051/10000000000 : ℝ)^75 ≤ (17009028298317/50000000000000 : ℝ)^59 := by
    have hnat : (4281653051 : ℕ)^75*50000000000000^59 ≤ 17009028298317^59*10000000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4281653051 10000000000 17009028298317 50000000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4013178241/10000000000 : ℝ)^75 ≤ (31329963769063/100000000000000 : ℝ)^59 := by
    have hnat : (4013178241 : ℕ)^75*100000000000000^59 ≤ 31329963769063^59*10000000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4013178241 10000000000 31329963769063 100000000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (75/16 : ℝ)) 75 59 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(543036989/1250000000 : ℝ), (-4281653051/10000000000 : ℝ), (4013178241/10000000000 : ℝ)] ![(34651979621323/100000000000000 : ℝ), (17009028298317/50000000000000 : ℝ), (31329963769063/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(543036989/1250000000 : ℝ)|^75 ≤ (34651979621323/100000000000000 : ℝ)^59
        have hw : |(543036989/1250000000 : ℝ)|=(543036989/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-4281653051/10000000000 : ℝ)|^75 ≤ (17009028298317/50000000000000 : ℝ)^59
        have hw : |(-4281653051/10000000000 : ℝ)|=(4281653051/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4013178241/10000000000 : ℝ)|^75 ≤ (31329963769063/100000000000000 : ℝ)^59
        have hw : |(4013178241/10000000000 : ℝ)|=(4013178241/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c313046_s0_25 (p : ℝ) (hpa : (73/16 : ℝ) ≤ p) (hpb : p ≤ (75/16 : ℝ)) (x : Fin 3 → ℝ) :
    (584233551/625000000 : ℝ)*x 0 + (-105560131/1250000000 : ℝ)*x 1 + (-155736391/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (584233551/625000000 : ℝ)^75 ≤ (91783046738159/100000000000000 : ℝ)^59 := by
    have hnat : (584233551 : ℕ)^75*100000000000000^59 ≤ 91783046738159^59*625000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      584233551 625000000 91783046738159 100000000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (105560131/1250000000 : ℝ)^75 ≤ (2160059178059/50000000000000 : ℝ)^59 := by
    have hnat : (105560131 : ℕ)^75*50000000000000^59 ≤ 2160059178059^59*1250000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      105560131 1250000000 2160059178059 50000000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (155736391/2000000000 : ℝ)^75 ≤ (974208722411/25000000000000 : ℝ)^59 := by
    have hnat : (155736391 : ℕ)^75*25000000000000^59 ≤ 974208722411^59*2000000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      155736391 2000000000 974208722411 25000000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (75/16 : ℝ)) 75 59 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(584233551/625000000 : ℝ), (-105560131/1250000000 : ℝ), (-155736391/2000000000 : ℝ)] ![(91783046738159/100000000000000 : ℝ), (2160059178059/50000000000000 : ℝ), (974208722411/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(584233551/625000000 : ℝ)|^75 ≤ (91783046738159/100000000000000 : ℝ)^59
        have hw : |(584233551/625000000 : ℝ)|=(584233551/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-105560131/1250000000 : ℝ)|^75 ≤ (2160059178059/50000000000000 : ℝ)^59
        have hw : |(-105560131/1250000000 : ℝ)|=(105560131/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-155736391/2000000000 : ℝ)|^75 ≤ (974208722411/25000000000000 : ℝ)^59
        have hw : |(-155736391/2000000000 : ℝ)|=(155736391/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c313046_s1_0 (p : ℝ) (hpa : (73/16 : ℝ) ≤ p) (hpb : p ≤ (75/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-323217923/1250000000 : ℝ)*x 0 + (-1240714797/2500000000 : ℝ)*x 1 + (-1240714797/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (323217923/1250000000 : ℝ)^75 ≤ (17917877107217/100000000000000 : ℝ)^59 := by
    have hnat : (323217923 : ℕ)^75*100000000000000^59 ≤ 17917877107217^59*1250000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      323217923 1250000000 17917877107217 100000000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1240714797/2500000000 : ℝ)^75 ≤ (41041061444747/100000000000000 : ℝ)^59 := by
    have hnat : (1240714797 : ℕ)^75*100000000000000^59 ≤ 41041061444747^59*2500000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1240714797 2500000000 41041061444747 100000000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1240714797/2500000000 : ℝ)^75 ≤ (41041061444747/100000000000000 : ℝ)^59 := by
    have hnat : (1240714797 : ℕ)^75*100000000000000^59 ≤ 41041061444747^59*2500000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1240714797 2500000000 41041061444747 100000000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (75/16 : ℝ)) 75 59 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-323217923/1250000000 : ℝ), (-1240714797/2500000000 : ℝ), (-1240714797/2500000000 : ℝ)] ![(17917877107217/100000000000000 : ℝ), (41041061444747/100000000000000 : ℝ), (41041061444747/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-323217923/1250000000 : ℝ)|^75 ≤ (17917877107217/100000000000000 : ℝ)^59
        have hw : |(-323217923/1250000000 : ℝ)|=(323217923/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1240714797/2500000000 : ℝ)|^75 ≤ (41041061444747/100000000000000 : ℝ)^59
        have hw : |(-1240714797/2500000000 : ℝ)|=(1240714797/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1240714797/2500000000 : ℝ)|^75 ≤ (41041061444747/100000000000000 : ℝ)^59
        have hw : |(-1240714797/2500000000 : ℝ)|=(1240714797/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c313046_s1_1 (p : ℝ) (hpa : (73/16 : ℝ) ≤ p) (hpb : p ≤ (75/16 : ℝ)) (x : Fin 3 → ℝ) :
    (4532861173/10000000000 : ℝ)*x 0 + (4051671409/10000000000 : ℝ)*x 1 + (-4051671409/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4532861173/10000000000 : ℝ)^75 ≤ (731501587653/2000000000000 : ℝ)^59 := by
    have hnat : (4532861173 : ℕ)^75*2000000000000^59 ≤ 731501587653^59*10000000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4532861173 10000000000 731501587653 2000000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4051671409/10000000000 : ℝ)^75 ≤ (31712460303207/100000000000000 : ℝ)^59 := by
    have hnat : (4051671409 : ℕ)^75*100000000000000^59 ≤ 31712460303207^59*10000000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4051671409 10000000000 31712460303207 100000000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4051671409/10000000000 : ℝ)^75 ≤ (31712460303207/100000000000000 : ℝ)^59 := by
    have hnat : (4051671409 : ℕ)^75*100000000000000^59 ≤ 31712460303207^59*10000000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4051671409 10000000000 31712460303207 100000000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (75/16 : ℝ)) 75 59 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4532861173/10000000000 : ℝ), (4051671409/10000000000 : ℝ), (-4051671409/10000000000 : ℝ)] ![(731501587653/2000000000000 : ℝ), (31712460303207/100000000000000 : ℝ), (31712460303207/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4532861173/10000000000 : ℝ)|^75 ≤ (731501587653/2000000000000 : ℝ)^59
        have hw : |(4532861173/10000000000 : ℝ)|=(4532861173/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4051671409/10000000000 : ℝ)|^75 ≤ (31712460303207/100000000000000 : ℝ)^59
        have hw : |(4051671409/10000000000 : ℝ)|=(4051671409/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-4051671409/10000000000 : ℝ)|^75 ≤ (31712460303207/100000000000000 : ℝ)^59
        have hw : |(-4051671409/10000000000 : ℝ)|=(4051671409/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c313046_s1_2 (p : ℝ) (hpa : (73/16 : ℝ) ≤ p) (hpb : p ≤ (75/16 : ℝ)) (x : Fin 3 → ℝ) :
    (4532861173/10000000000 : ℝ)*x 0 + (-4051671409/10000000000 : ℝ)*x 1 + (4051671409/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4532861173/10000000000 : ℝ)^75 ≤ (731501587653/2000000000000 : ℝ)^59 := by
    have hnat : (4532861173 : ℕ)^75*2000000000000^59 ≤ 731501587653^59*10000000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4532861173 10000000000 731501587653 2000000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4051671409/10000000000 : ℝ)^75 ≤ (31712460303207/100000000000000 : ℝ)^59 := by
    have hnat : (4051671409 : ℕ)^75*100000000000000^59 ≤ 31712460303207^59*10000000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4051671409 10000000000 31712460303207 100000000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4051671409/10000000000 : ℝ)^75 ≤ (31712460303207/100000000000000 : ℝ)^59 := by
    have hnat : (4051671409 : ℕ)^75*100000000000000^59 ≤ 31712460303207^59*10000000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4051671409 10000000000 31712460303207 100000000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (75/16 : ℝ)) 75 59 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4532861173/10000000000 : ℝ), (-4051671409/10000000000 : ℝ), (4051671409/10000000000 : ℝ)] ![(731501587653/2000000000000 : ℝ), (31712460303207/100000000000000 : ℝ), (31712460303207/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4532861173/10000000000 : ℝ)|^75 ≤ (731501587653/2000000000000 : ℝ)^59
        have hw : |(4532861173/10000000000 : ℝ)|=(4532861173/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-4051671409/10000000000 : ℝ)|^75 ≤ (31712460303207/100000000000000 : ℝ)^59
        have hw : |(-4051671409/10000000000 : ℝ)|=(4051671409/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4051671409/10000000000 : ℝ)|^75 ≤ (31712460303207/100000000000000 : ℝ)^59
        have hw : |(4051671409/10000000000 : ℝ)|=(4051671409/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c313046_s1_6 (p : ℝ) (hpa : (73/16 : ℝ) ≤ p) (hpb : p ≤ (75/16 : ℝ)) (x : Fin 3 → ℝ) :
    (6364978607/10000000000 : ℝ)*x 0 + (-3021943997/10000000000 : ℝ)*x 1 + (-3021943997/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (6364978607/10000000000 : ℝ)^75 ≤ (56310494484647/100000000000000 : ℝ)^59 := by
    have hnat : (6364978607 : ℕ)^75*100000000000000^59 ≤ 56310494484647^59*10000000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6364978607 10000000000 56310494484647 100000000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3021943997/10000000000 : ℝ)^75 ≤ (5461188187361/25000000000000 : ℝ)^59 := by
    have hnat : (3021943997 : ℕ)^75*25000000000000^59 ≤ 5461188187361^59*10000000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3021943997 10000000000 5461188187361 25000000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3021943997/10000000000 : ℝ)^75 ≤ (5461188187361/25000000000000 : ℝ)^59 := by
    have hnat : (3021943997 : ℕ)^75*25000000000000^59 ≤ 5461188187361^59*10000000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3021943997 10000000000 5461188187361 25000000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (75/16 : ℝ)) 75 59 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(6364978607/10000000000 : ℝ), (-3021943997/10000000000 : ℝ), (-3021943997/10000000000 : ℝ)] ![(56310494484647/100000000000000 : ℝ), (5461188187361/25000000000000 : ℝ), (5461188187361/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(6364978607/10000000000 : ℝ)|^75 ≤ (56310494484647/100000000000000 : ℝ)^59
        have hw : |(6364978607/10000000000 : ℝ)|=(6364978607/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-3021943997/10000000000 : ℝ)|^75 ≤ (5461188187361/25000000000000 : ℝ)^59
        have hw : |(-3021943997/10000000000 : ℝ)|=(3021943997/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-3021943997/10000000000 : ℝ)|^75 ≤ (5461188187361/25000000000000 : ℝ)^59
        have hw : |(-3021943997/10000000000 : ℝ)|=(3021943997/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_c313046 (p : ℝ) (hpa : (73/16 : ℝ) ≤ p) (hpb : p ≤ (75/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (169487/100000 : ℝ) (176973/100000 : ℝ) (78599/100000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, false, true], ![true, true, false]]) : False := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : RawLinearData _ _ X N P T := raw_linear_data (by linarith : (1 : ℝ) ≤ p) X hX.raw
  have bounds := raw_linear_data_bounds f (by norm_num)
  have main0 : (78599/100000 : ℝ)*P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.main 0
    change (78599/100000 : ℝ)*P 0 ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order0 : 0 ≤ ((1 : ℝ)*(X 1 2+X 2 2)) ∧ ((1 : ℝ)*(X 1 2+X 2 2)) ≤ ((1 : ℝ)*(X 1 1+X 2 1)) ∧ ((1 : ℝ)*(X 1 1+X 2 1)) ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.ordered 0
    change 0 ≤ ((1 : ℝ)*pair X 0 2) ∧ ((1 : ℝ)*pair X 0 2) ≤ ((1 : ℝ)*pair X 0 1) ∧ ((1 : ℝ)*pair X 0 1) ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main1 : (78599/100000 : ℝ)*P 1 ≤ ((-1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.main 1
    change (78599/100000 : ℝ)*P 1 ≤ ((-1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order1 : 0 ≤ ((1 : ℝ)*(X 0 2+X 2 2)) ∧ ((1 : ℝ)*(X 0 2+X 2 2)) ≤ ((1 : ℝ)*(X 0 0+X 2 0)) ∧ ((1 : ℝ)*(X 0 0+X 2 0)) ≤ ((-1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.ordered 1
    change 0 ≤ ((1 : ℝ)*pair X 1 2) ∧ ((1 : ℝ)*pair X 1 2) ≤ ((1 : ℝ)*pair X 1 0) ∧ ((1 : ℝ)*pair X 1 0) ≤ ((-1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main2 : (78599/100000 : ℝ)*P 2 ≤ ((-1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.main 2
    change (78599/100000 : ℝ)*P 2 ≤ ((-1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order2 : 0 ≤ ((1 : ℝ)*(X 0 1+X 1 1)) ∧ ((1 : ℝ)*(X 0 1+X 1 1)) ≤ ((1 : ℝ)*(X 0 0+X 1 0)) ∧ ((1 : ℝ)*(X 0 0+X 1 0)) ≤ ((-1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.ordered 2
    change 0 ≤ ((1 : ℝ)*pair X 2 1) ∧ ((1 : ℝ)*pair X 2 1) ≤ ((1 : ℝ)*pair X 2 0) ∧ ((1 : ℝ)*pair X 2 0) ≤ ((-1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have base1 : ((1 : ℝ)*N 0+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    linarith only [f.Ntotal 0]
  have base3 : ((1 : ℝ)*N 1+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    linarith only [f.Ntotal 1]
  have base12 : ((-1 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    linarith only [(f.coord 0 2).1]
  have base18 : ((-1 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    linarith only [(f.coord 1 2).1]
  have base22 : ((-1 : ℝ)*X 2 1+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    linarith only [(f.coord 2 1).1]
  have base39 : ((-1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.1]
  have base40 : ((-1 : ℝ)*X 1 1+(1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 1+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.2.1]
  have base49 : ((-1 : ℝ)*X 0 2+(-1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order1.1]
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
  have s0_pow0 : (1 : ℝ) ^ (73/16 : ℝ) ≤ (1 : ℝ) := by
    have hpowers : (1 : ℝ)^73 ≤ (1 : ℝ)^16 := by
      have hnat : (1 : ℕ)^73*1^16 ≤ 1^16*1^73 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 73 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) (by norm_num) 73 16 (by norm_num) hpowers
    exact h
  have s0_corner0a : (2 : ℝ) ≤ (5820351075331079/5000000000000000 : ℝ) ^ (73/16 : ℝ) := by
    have hpowers : (2 : ℝ)^16 ≤ (5820351075331079/5000000000000000 : ℝ)^73 := by
      have hnat : (2 : ℕ)^16*5000000000000000^73 ≤ 5820351075331079^73*1^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 1 5820351075331079 5000000000000000 16 73 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5820351075331079/5000000000000000 : ℝ)) (X := (2 : ℝ)) (by norm_num) 73 16 (by norm_num) hpowers
    exact h
  have s0_corner0b : (3 : ℝ) ≤ (12722560406774351/10000000000000000 : ℝ) ^ (73/16 : ℝ) := by
    have hpowers : (3 : ℝ)^16 ≤ (12722560406774351/10000000000000000 : ℝ)^73 := by
      have hnat : (3 : ℕ)^16*10000000000000000^73 ≤ 12722560406774351^73*1^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3 1 12722560406774351 10000000000000000 16 73 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (12722560406774351/10000000000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 73 16 (by norm_num) hpowers
    exact h
  have major_s0_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(820351075331079/5000000000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(1081858256112193/10000000000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (73/16 : ℝ)) (rho := (1 : ℝ)) (alpha := (820351075331079/5000000000000000 : ℝ)) (beta := (1081858256112193/10000000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow0,s0_corner0a]) (by linarith only [s0_pow0,s0_corner0b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, false, true], ![true, true, false]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (1 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order0.2.2])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(820351075331079/5000000000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(1081858256112193/10000000000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s0_pow1 : (1 : ℝ) ^ (73/16 : ℝ) ≤ (1 : ℝ) := by
    have hpowers : (1 : ℝ)^73 ≤ (1 : ℝ)^16 := by
      have hnat : (1 : ℕ)^73*1^16 ≤ 1^16*1^73 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 73 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) (by norm_num) 73 16 (by norm_num) hpowers
    exact h
  have s0_corner1a : (2 : ℝ) ≤ (5820351075331079/5000000000000000 : ℝ) ^ (73/16 : ℝ) := by
    have hpowers : (2 : ℝ)^16 ≤ (5820351075331079/5000000000000000 : ℝ)^73 := by
      have hnat : (2 : ℕ)^16*5000000000000000^73 ≤ 5820351075331079^73*1^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 1 5820351075331079 5000000000000000 16 73 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5820351075331079/5000000000000000 : ℝ)) (X := (2 : ℝ)) (by norm_num) 73 16 (by norm_num) hpowers
    exact h
  have s0_corner1b : (3 : ℝ) ≤ (12722560406774351/10000000000000000 : ℝ) ^ (73/16 : ℝ) := by
    have hpowers : (3 : ℝ)^16 ≤ (12722560406774351/10000000000000000 : ℝ)^73 := by
      have hnat : (3 : ℕ)^16*10000000000000000^73 ≤ 12722560406774351^73*1^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3 1 12722560406774351 10000000000000000 16 73 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (12722560406774351/10000000000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 73 16 (by norm_num) hpowers
    exact h
  have major_s0_1 : P 1 ≤ ((-1 : ℝ)*(X 0 1+X 2 1))+(820351075331079/5000000000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 2 0))+(1081858256112193/10000000000000000 : ℝ)*((1 : ℝ)*(X 0 2+X 2 2)) := by
    have hh := chart_majorant (a := (73/16 : ℝ)) (rho := (1 : ℝ)) (alpha := (820351075331079/5000000000000000 : ℝ)) (beta := (1081858256112193/10000000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow1,s0_corner1a]) (by linarith only [s0_pow1,s0_corner1b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, false, true], ![true, true, false]] hX 1 (by
        change ((1 : ℝ)*pair X 1 0) ≤ (1 : ℝ)*((-1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order1.2.2])
    change lpNorm p (pair X 1) ≤ ((-1 : ℝ)*pair X 1 1)+(820351075331079/5000000000000000 : ℝ)*((1 : ℝ)*pair X 1 0)+(1081858256112193/10000000000000000 : ℝ)*((1 : ℝ)*pair X 1 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s0_pow2 : (1 : ℝ) ^ (73/16 : ℝ) ≤ (1 : ℝ) := by
    have hpowers : (1 : ℝ)^73 ≤ (1 : ℝ)^16 := by
      have hnat : (1 : ℕ)^73*1^16 ≤ 1^16*1^73 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 73 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) (by norm_num) 73 16 (by norm_num) hpowers
    exact h
  have s0_corner2a : (2 : ℝ) ≤ (5820351075331079/5000000000000000 : ℝ) ^ (73/16 : ℝ) := by
    have hpowers : (2 : ℝ)^16 ≤ (5820351075331079/5000000000000000 : ℝ)^73 := by
      have hnat : (2 : ℕ)^16*5000000000000000^73 ≤ 5820351075331079^73*1^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 1 5820351075331079 5000000000000000 16 73 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5820351075331079/5000000000000000 : ℝ)) (X := (2 : ℝ)) (by norm_num) 73 16 (by norm_num) hpowers
    exact h
  have s0_corner2b : (3 : ℝ) ≤ (12722560406774351/10000000000000000 : ℝ) ^ (73/16 : ℝ) := by
    have hpowers : (3 : ℝ)^16 ≤ (12722560406774351/10000000000000000 : ℝ)^73 := by
      have hnat : (3 : ℕ)^16*10000000000000000^73 ≤ 12722560406774351^73*1^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3 1 12722560406774351 10000000000000000 16 73 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (12722560406774351/10000000000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 73 16 (by norm_num) hpowers
    exact h
  have major_s0_2 : P 2 ≤ ((-1 : ℝ)*(X 0 2+X 1 2))+(820351075331079/5000000000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 1 0))+(1081858256112193/10000000000000000 : ℝ)*((1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (73/16 : ℝ)) (rho := (1 : ℝ)) (alpha := (820351075331079/5000000000000000 : ℝ)) (beta := (1081858256112193/10000000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow2,s0_corner2a]) (by linarith only [s0_pow2,s0_corner2b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, false, true], ![true, true, false]] hX 2 (by
        change ((1 : ℝ)*pair X 2 0) ≤ (1 : ℝ)*((-1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order2.2.2])
    change lpNorm p (pair X 2) ≤ ((-1 : ℝ)*pair X 2 2)+(820351075331079/5000000000000000 : ℝ)*((1 : ℝ)*pair X 2 0)+(1081858256112193/10000000000000000 : ℝ)*((1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s0_0 : ((-537522217/5000000000 : ℝ)*X 0 0+(-5527342521/10000000000 : ℝ)*X 0 1+(-5527342519/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c313046_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_1 : ((48150881/100000000 : ℝ)*X 1 0+(390425347/1000000000 : ℝ)*X 1 1+(-3904253471/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c313046_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_2 : ((48150881/100000000 : ℝ)*X 2 0+(-390425347/1000000000 : ℝ)*X 2 1+(3904253471/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c313046_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_3 : ((1 : ℝ)*X 1 0+(1 : ℝ)*X 2 0+(-1 : ℝ)*P 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c313046_s0_3 p hpa hpb (pair X 0)
    change _ ≤ P 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_6 : ((8147429049/10000000000 : ℝ)*X 0 0+(-363962907/2000000000 : ℝ)*X 0 1+(-363962907/2000000000 : ℝ)*X 0 2+(8147429049/10000000000 : ℝ)*X 1 0+(-363962907/2000000000 : ℝ)*X 1 1+(-363962907/2000000000 : ℝ)*X 1 2+(8147429049/10000000000 : ℝ)*X 2 0+(-363962907/2000000000 : ℝ)*X 2 1+(-363962907/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c313046_s0_6 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_7 : ((-222758273/2000000000 : ℝ)*X 0 0+(-1154118589/2000000000 : ℝ)*X 0 1+(-5255851/10000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c313046_s0_7 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_8 : ((467043923/1000000000 : ℝ)*X 1 0+(179335091/400000000 : ℝ)*X 1 1+(-1729642131/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c313046_s0_8 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_9 : ((934087843/2000000000 : ℝ)*X 2 0+(-844046109/2500000000 : ℝ)*X 2 1+(1140100397/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c313046_s0_9 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_13 : ((4111612709/5000000000 : ℝ)*X 0 0+(-331218603/2500000000 : ℝ)*X 0 1+(-2172318001/10000000000 : ℝ)*X 0 2+(4111612709/5000000000 : ℝ)*X 1 0+(-331218603/2500000000 : ℝ)*X 1 1+(-2172318001/10000000000 : ℝ)*X 1 2+(4111612709/5000000000 : ℝ)*X 2 0+(-331218603/2500000000 : ℝ)*X 2 1+(-2172318001/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c313046_s0_13 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_14 : ((-316116813/10000000000 : ℝ)*X 0 0+(-2753162551/5000000000 : ℝ)*X 0 1+(-2985807799/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c313046_s0_14 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_15 : ((4344297703/10000000000 : ℝ)*X 1 0+(802635357/2000000000 : ℝ)*X 1 1+(-4281652683/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c313046_s0_15 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_16 : ((5612529671/10000000000 : ℝ)*X 2 0+(-1676780107/5000000000 : ℝ)*X 2 1+(3577908689/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c313046_s0_16 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_19 : ((46738679/50000000 : ℝ)*X 0 0+(-389341357/5000000000 : ℝ)*X 0 1+(-168896451/2000000000 : ℝ)*X 0 2+(46738679/50000000 : ℝ)*X 1 0+(-389341357/5000000000 : ℝ)*X 1 1+(-168896451/2000000000 : ℝ)*X 1 2+(46738679/50000000 : ℝ)*X 2 0+(-389341357/5000000000 : ℝ)*X 2 1+(-168896451/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c313046_s0_19 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_20 : ((-39514681/1250000000 : ℝ)*X 0 0+(-5971614161/10000000000 : ℝ)*X 0 1+(-5506326279/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c313046_s0_20 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_21 : ((1403132069/2500000000 : ℝ)*X 1 0+(1788954517/5000000000 : ℝ)*X 1 1+(-3353561467/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c313046_s0_21 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_22 : ((543036989/1250000000 : ℝ)*X 2 0+(-4281653051/10000000000 : ℝ)*X 2 1+(4013178241/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c313046_s0_22 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_25 : ((584233551/625000000 : ℝ)*X 0 0+(-105560131/1250000000 : ℝ)*X 0 1+(-155736391/2000000000 : ℝ)*X 0 2+(584233551/625000000 : ℝ)*X 1 0+(-105560131/1250000000 : ℝ)*X 1 1+(-155736391/2000000000 : ℝ)*X 1 2+(584233551/625000000 : ℝ)*X 2 0+(-105560131/1250000000 : ℝ)*X 2 1+(-155736391/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c313046_s0_25 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have ratio_s0_0 : (0 : ℝ) ≤ ((1807/25000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(1807/25000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (3098405150673721437243/1000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1149/50000000000 : ℝ)*(base3) + (979295391117/1000000000000 : ℝ)*(base39) + (80141087611/1000000000000 : ℝ)*(base49) + (3549593284417/1000000000000 : ℝ)*(major_s0_0) + (3549593284417/1000000000000 : ℝ)*(major_s0_1) + (3549593284417/1000000000000 : ℝ)*(major_s0_2) + (491957/50000000000 : ℝ)*(sp_s0_1) + (338697/31250000000 : ℝ)*(sp_s0_6) + (2502434789993/500000000000 : ℝ)*(sp_s0_7) + (312801096309/62500000000 : ℝ)*(sp_s0_8) + (250241614019/50000000000 : ℝ)*(sp_s0_9) + (2094305094759/1000000000000 : ℝ)*(sp_s0_13) + (42222881/1000000000000 : ℝ)*(sp_s0_15) + (18649803/500000000000 : ℝ)*(sp_s0_22) + (1047157978021/500000000000 : ℝ)*(f.failure) + (2502434789993/500000000000 : ℝ)*(f.sum) + (1131320780504057/2500000000000000000000000000 : ℝ)*base62 + (159729771403519/10000000000000000000000000000 : ℝ)*base64 + (65607509596481/10000000000000000000000000000 : ℝ)*base67 + (446650024004057/5000000000000000000000000000 : ℝ)*base68 + (4416977046588367/10000000000000000000000000000 : ℝ)*base71 + (1598360499403519/10000000000000000000000000000 : ℝ)*base72 + (1763001478504057/5000000000000000000000000000 : ℝ)*base74 + (344252753495943/5000000000000000000000000000 : ℝ)*base77 + (1092160567096481/5000000000000000000000000000 : ℝ)*base79 + (1/1000000000000 : ℝ)*base82 + (4773/50000000000000000 : ℝ)*base86 + (4773/50000000000000000 : ℝ)*base88 + (4773/50000000000000000 : ℝ)*base90 + (1/1000000000000 : ℝ)*base93 + hcertificate_margin
  have ratio_s0_1 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(-1943/5000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(-1943/5000 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (10194974570510401497069/1000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1723373/125000000000 : ℝ)*(base12) + (419334638751/1000000000000 : ℝ)*(base39) + (1637227/500000000000 : ℝ)*(base59) + (1754175595073/125000000000 : ℝ)*(major_s0_0) + (5592285871359/1000000000000 : ℝ)*(major_s0_1) + (5592285871359/1000000000000 : ℝ)*(major_s0_2) + (2483049/31250000000 : ℝ)*(sp_s0_0) + (619499/25000000000 : ℝ)*(sp_s0_1) + (337644755569/40000000000 : ℝ)*(sp_s0_3) + (39758013/1000000000000 : ℝ)*(sp_s0_9) + (3942469169051/500000000000 : ℝ)*(sp_s0_14) + (3942503401347/500000000000 : ℝ)*(sp_s0_15) + (7884991824641/1000000000000 : ℝ)*(sp_s0_16) + (3299536761733/1000000000000 : ℝ)*(sp_s0_19) + (3299536761733/1000000000000 : ℝ)*(f.failure) + (3942515791327/500000000000 : ℝ)*(f.sum) + (881810938166361/2500000000000000000000000000 : ℝ)*base63 + (4245512636619713/10000000000000000000000000000 : ℝ)*base64 + (4851384627619713/10000000000000000000000000000 : ℝ)*base66 + (2622260287666361/5000000000000000000000000000 : ℝ)*base69 + (2390232899839441/10000000000000000000000000000 : ℝ)*base70 + (188365139349911/1250000000000000000000000000 : ℝ)*base72 + (2805152775666361/5000000000000000000000000000 : ℝ)*base75 + (138850796076233/625000000000000000000000000 : ℝ)*base76 + (2319398099580999/10000000000000000000000000000 : ℝ)*base79 + (59029/100000000000000000 : ℝ)*base86 + (59029/100000000000000000 : ℝ)*base88 + (59029/100000000000000000 : ℝ)*base90 + hcertificate_margin
  have ratio_s0_2 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(-1943/5000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(-1943/5000 : ℝ)*X 1 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (50580400129182985920087/5000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (2717506405069/1000000000000 : ℝ)*(base39) + (1020032450837/1000000000000 : ℝ)*(base40) + (3010961/1000000000000 : ℝ)*(base49) + (3556427/500000000000 : ℝ)*(base59) + (5592334811379/1000000000000 : ℝ)*(major_s0_0) + (5592334811379/1000000000000 : ℝ)*(major_s0_1) + (5592334811379/1000000000000 : ℝ)*(major_s0_2) + (5926647/125000000000 : ℝ)*(sp_s0_2) + (44440207/250000000000 : ℝ)*(sp_s0_7) + (3896587/31250000000 : ℝ)*(sp_s0_8) + (394246142639/50000000000 : ℝ)*(sp_s0_20) + (315399036913/40000000000 : ℝ)*(sp_s0_21) + (492815825027/62500000000 : ℝ)*(sp_s0_22) + (824891409279/250000000000 : ℝ)*(sp_s0_25) + (824891409279/250000000000 : ℝ)*(f.failure) + (7885100613609/1000000000000 : ℝ)*(f.sum) + (4077307452059/2500000000000000000000000000 : ℝ)*base62 + (5977531874955853/10000000000000000000000000000 : ℝ)*base64 + (9931010082955853/10000000000000000000000000000 : ℝ)*base66 + (465190103547941/5000000000000000000000000000 : ℝ)*base69 + (2560743681859971/10000000000000000000000000000 : ℝ)*base70 + (304418019955853/10000000000000000000000000000 : ℝ)*base72 + (2927348321547941/5000000000000000000000000000 : ℝ)*base75 + (3602292398452059/5000000000000000000000000000 : ℝ)*base76 + (106768403044147/5000000000000000000000000000 : ℝ)*base79 + (1/1000000000000 : ℝ)*base80 + (1/1000000000000 : ℝ)*base84 + (5127/25000000000000000 : ℝ)*base86 + (5127/25000000000000000 : ℝ)*base88 + (5127/25000000000000000 : ℝ)*base90 + hcertificate_margin
  have s1_pow0 : (1807/25000 : ℝ) ^ (73/16 : ℝ) ≤ (311343845942823/50000000000000000000 : ℝ) := by
    have hpowers : (1807/25000 : ℝ)^73 ≤ (311343845942823/50000000000000000000 : ℝ)^16 := by
      have hnat : (1807 : ℕ)^73*50000000000000000000^16 ≤ 311343845942823^16*25000^73 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1807 25000 311343845942823 50000000000000000000 73 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1807/25000 : ℝ)) (X := (311343845942823/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 73 16 (by norm_num) hpowers
    exact h
  have s1_corner0a : (50000311343845942823/50000000000000000000 : ℝ) ≤ (10000013647916233/10000000000000000 : ℝ) ^ (73/16 : ℝ) := by
    have hpowers : (50000311343845942823/50000000000000000000 : ℝ)^16 ≤ (10000013647916233/10000000000000000 : ℝ)^73 := by
      have hnat : (50000311343845942823 : ℕ)^16*10000000000000000^73 ≤ 10000013647916233^73*50000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50000311343845942823 50000000000000000000 10000013647916233 10000000000000000 16 73 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000013647916233/10000000000000000 : ℝ)) (X := (50000311343845942823/50000000000000000000 : ℝ)) (by norm_num) 73 16 (by norm_num) hpowers
    exact h
  have s1_corner0b : (25000311343845942823/25000000000000000000 : ℝ) ≤ (10000027295766109/10000000000000000 : ℝ) ^ (73/16 : ℝ) := by
    have hpowers : (25000311343845942823/25000000000000000000 : ℝ)^16 ≤ (10000027295766109/10000000000000000 : ℝ)^73 := by
      have hnat : (25000311343845942823 : ℕ)^16*10000000000000000^73 ≤ 10000027295766109^73*25000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25000311343845942823 25000000000000000000 10000027295766109 10000000000000000 16 73 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000027295766109/10000000000000000 : ℝ)) (X := (25000311343845942823/25000000000000000000 : ℝ)) (by norm_num) 73 16 (by norm_num) hpowers
    exact h
  have major_s1_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(13647916233/722800000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(3411962469/180700000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (73/16 : ℝ)) (rho := (1807/25000 : ℝ)) (alpha := (13647916233/722800000000000 : ℝ)) (beta := (3411962469/180700000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow0,s1_corner0a]) (by linarith only [s1_pow0,s1_corner0b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, false, true], ![true, true, false]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (1807/25000 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_0])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(13647916233/722800000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(3411962469/180700000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s1_pow1 : (1943/5000 : ℝ) ^ (73/16 : ℝ) ≤ (134000527488454861/10000000000000000000 : ℝ) := by
    have hpowers : (1943/5000 : ℝ)^73 ≤ (134000527488454861/10000000000000000000 : ℝ)^16 := by
      have hnat : (1943 : ℕ)^73*10000000000000000000^16 ≤ 134000527488454861^16*5000^73 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1943 5000 134000527488454861 10000000000000000000 73 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1943/5000 : ℝ)) (X := (134000527488454861/10000000000000000000 : ℝ)) (by norm_num) (by norm_num) 73 16 (by norm_num) hpowers
    exact h
  have s1_corner1a : (10134000527488454861/10000000000000000000 : ℝ) ≤ (200584350793891/200000000000000 : ℝ) ^ (73/16 : ℝ) := by
    have hpowers : (10134000527488454861/10000000000000000000 : ℝ)^16 ≤ (200584350793891/200000000000000 : ℝ)^73 := by
      have hnat : (10134000527488454861 : ℕ)^16*200000000000000^73 ≤ 200584350793891^73*10000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10134000527488454861 10000000000000000000 200584350793891 200000000000000 16 73 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (200584350793891/200000000000000 : ℝ)) (X := (10134000527488454861/10000000000000000000 : ℝ)) (by norm_num) 73 16 (by norm_num) hpowers
    exact h
  have s1_corner1b : (5134000527488454861/5000000000000000000 : ℝ) ≤ (5029067478401897/5000000000000000 : ℝ) ^ (73/16 : ℝ) := by
    have hpowers : (5134000527488454861/5000000000000000000 : ℝ)^16 ≤ (5029067478401897/5000000000000000 : ℝ)^73 := by
      have hnat : (5134000527488454861 : ℕ)^16*5000000000000000^73 ≤ 5029067478401897^73*5000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5134000527488454861 5000000000000000000 5029067478401897 5000000000000000 16 73 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5029067478401897/5000000000000000 : ℝ)) (X := (5134000527488454861/5000000000000000000 : ℝ)) (by norm_num) 73 16 (by norm_num) hpowers
    exact h
  have major_s1_1 : P 1 ≤ ((-1 : ℝ)*(X 0 1+X 2 1))+(584350793891/77720000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 2 0))+(7229354277311/971500000000000 : ℝ)*((1 : ℝ)*(X 0 2+X 2 2)) := by
    have hh := chart_majorant (a := (73/16 : ℝ)) (rho := (1943/5000 : ℝ)) (alpha := (584350793891/77720000000000 : ℝ)) (beta := (7229354277311/971500000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow1,s1_corner1a]) (by linarith only [s1_pow1,s1_corner1b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, false, true], ![true, true, false]] hX 1 (by
        change ((1 : ℝ)*pair X 1 0) ≤ (1943/5000 : ℝ)*((-1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_1])
    change lpNorm p (pair X 1) ≤ ((-1 : ℝ)*pair X 1 1)+(584350793891/77720000000000 : ℝ)*((1 : ℝ)*pair X 1 0)+(7229354277311/971500000000000 : ℝ)*((1 : ℝ)*pair X 1 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s1_pow2 : (1943/5000 : ℝ) ^ (73/16 : ℝ) ≤ (134000527488454861/10000000000000000000 : ℝ) := by
    have hpowers : (1943/5000 : ℝ)^73 ≤ (134000527488454861/10000000000000000000 : ℝ)^16 := by
      have hnat : (1943 : ℕ)^73*10000000000000000000^16 ≤ 134000527488454861^16*5000^73 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1943 5000 134000527488454861 10000000000000000000 73 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1943/5000 : ℝ)) (X := (134000527488454861/10000000000000000000 : ℝ)) (by norm_num) (by norm_num) 73 16 (by norm_num) hpowers
    exact h
  have s1_corner2a : (10134000527488454861/10000000000000000000 : ℝ) ≤ (200584350793891/200000000000000 : ℝ) ^ (73/16 : ℝ) := by
    have hpowers : (10134000527488454861/10000000000000000000 : ℝ)^16 ≤ (200584350793891/200000000000000 : ℝ)^73 := by
      have hnat : (10134000527488454861 : ℕ)^16*200000000000000^73 ≤ 200584350793891^73*10000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10134000527488454861 10000000000000000000 200584350793891 200000000000000 16 73 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (200584350793891/200000000000000 : ℝ)) (X := (10134000527488454861/10000000000000000000 : ℝ)) (by norm_num) 73 16 (by norm_num) hpowers
    exact h
  have s1_corner2b : (5134000527488454861/5000000000000000000 : ℝ) ≤ (5029067478401897/5000000000000000 : ℝ) ^ (73/16 : ℝ) := by
    have hpowers : (5134000527488454861/5000000000000000000 : ℝ)^16 ≤ (5029067478401897/5000000000000000 : ℝ)^73 := by
      have hnat : (5134000527488454861 : ℕ)^16*5000000000000000^73 ≤ 5029067478401897^73*5000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5134000527488454861 5000000000000000000 5029067478401897 5000000000000000 16 73 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5029067478401897/5000000000000000 : ℝ)) (X := (5134000527488454861/5000000000000000000 : ℝ)) (by norm_num) 73 16 (by norm_num) hpowers
    exact h
  have major_s1_2 : P 2 ≤ ((-1 : ℝ)*(X 0 2+X 1 2))+(584350793891/77720000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 1 0))+(7229354277311/971500000000000 : ℝ)*((1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (73/16 : ℝ)) (rho := (1943/5000 : ℝ)) (alpha := (584350793891/77720000000000 : ℝ)) (beta := (7229354277311/971500000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow2,s1_corner2a]) (by linarith only [s1_pow2,s1_corner2b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, false, true], ![true, true, false]] hX 2 (by
        change ((1 : ℝ)*pair X 2 0) ≤ (1943/5000 : ℝ)*((-1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_2])
    change lpNorm p (pair X 2) ≤ ((-1 : ℝ)*pair X 2 2)+(584350793891/77720000000000 : ℝ)*((1 : ℝ)*pair X 2 0)+(7229354277311/971500000000000 : ℝ)*((1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s1_0 : ((-323217923/1250000000 : ℝ)*X 0 0+(-1240714797/2500000000 : ℝ)*X 0 1+(-1240714797/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c313046_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_1 : ((4532861173/10000000000 : ℝ)*X 1 0+(4051671409/10000000000 : ℝ)*X 1 1+(-4051671409/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c313046_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_2 : ((4532861173/10000000000 : ℝ)*X 2 0+(-4051671409/10000000000 : ℝ)*X 2 1+(4051671409/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c313046_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_6 : ((6364978607/10000000000 : ℝ)*X 0 0+(-3021943997/10000000000 : ℝ)*X 0 1+(-3021943997/10000000000 : ℝ)*X 0 2+(6364978607/10000000000 : ℝ)*X 1 0+(-3021943997/10000000000 : ℝ)*X 1 1+(-3021943997/10000000000 : ℝ)*X 1 2+(6364978607/10000000000 : ℝ)*X 2 0+(-3021943997/10000000000 : ℝ)*X 2 1+(-3021943997/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c313046_s1_6 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have hsep : (-358461/50000 : ℝ) < ((-169487/100000 : ℝ)*P 0+(-169487/100000 : ℝ)*P 1+(-169487/100000 : ℝ)*P 2+(1 : ℝ)*T) := by
    have hcertificate_margin : (-358461/50000 : ℝ) < (-31111876556450252257223801919/4388751250000000000000000000 : ℝ) := by norm_num
    linear_combination (531/500000000000 : ℝ)*(base1) + (980449/1000000000000 : ℝ)*(base18) + (980449/1000000000000 : ℝ)*(base22) + (108808119499/125000000000 : ℝ)*(base39) + (217616238959/500000000000 : ℝ)*(base40) + (51834748653/250000000000 : ℝ)*(base49) + (51834748653/250000000000 : ℝ)*(base59) + (169487/100000 : ℝ)*(major_s1_0) + (169487/100000 : ℝ)*(major_s1_1) + (169487/100000 : ℝ)*(major_s1_2) + (2363001439979/1000000000000 : ℝ)*(sp_s1_0) + (2363000458469/1000000000000 : ℝ)*(sp_s1_1) + (2363000458469/1000000000000 : ℝ)*(sp_s1_2) + (499999999469/500000000000 : ℝ)*(sp_s1_6) + (2363001438917/1000000000000 : ℝ)*(f.sum) + (121540525451/1943000000000000000000000 : ℝ)*base63 + (1887472599217/9715000000000000000000000 : ℝ)*base65 + (1887472599217/9715000000000000000000000 : ℝ)*base67 + (1362250573671/19430000000000000000000000 : ℝ)*base69 + (792077633565473/7022002000000000000000000000 : ℝ)*base71 + (11539884228649/18070000000000000000000000 : ℝ)*base73 + (1362250573671/19430000000000000000000000 : ℝ)*base75 + (4282098978649/18070000000000000000000000 : ℝ)*base77 + (3612452981715473/7022002000000000000000000000 : ℝ)*base79 + (1/1000000000000 : ℝ)*base83 + (1/1000000000000 : ℝ)*base85 + hcertificate_margin
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
theorem coarse_distinct_p013_b023 (p : ℝ) (hpa : (73/16 : ℝ) ≤ p) (hpb : p ≤ (37/8 : ℝ))
    (c : Fin 88) (hlo : 46 ≤ c.val) (hhi : c.val < 54)
    (hn63 : c ≠ 63) (hn87 : c ≠ 87)
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (169487/100000 : ℝ) (176973/100000 : ℝ) (78599/100000 : ℝ) X (distinctOrders c) (distinctSigns c)) : False := by
  have hc : c=46 ∨ c=47 ∨ c=48 ∨ c=49 ∨ c=50 ∨ c=51 ∨ c=52 ∨ c=53 := by omega
  rcases hc with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  · exact collision_c313046 p hpa (by linarith only [hpb]) X hX
  · exact collision_c312047 p (by linarith only [hpa]) (by linarith only [hpb]) X (orderedChart_weaken
      (by linarith only [hpa]) hX (by norm_num) (by norm_num) (by norm_num))
  · exact collision_c312048 p (by linarith only [hpa]) (by linarith only [hpb]) X (orderedChart_weaken
      (by linarith only [hpa]) hX (by norm_num) (by norm_num) (by norm_num))
  · exact collision_c312049 p (by linarith only [hpa]) (by linarith only [hpb]) X (orderedChart_weaken
      (by linarith only [hpa]) hX (by norm_num) (by norm_num) (by norm_num))
  · exact collision_c312050 p (by linarith only [hpa]) (by linarith only [hpb]) X (orderedChart_weaken
      (by linarith only [hpa]) hX (by norm_num) (by norm_num) (by norm_num))
  · exact collision_c312051 p (by linarith only [hpa]) (by linarith only [hpb]) X (orderedChart_weaken
      (by linarith only [hpa]) hX (by norm_num) (by norm_num) (by norm_num))
  · exact collision_c312052 p (by linarith only [hpa]) (by linarith only [hpb]) X (orderedChart_weaken
      (by linarith only [hpa]) hX (by norm_num) (by norm_num) (by norm_num))
  · exact collision_c313053 p hpa (by linarith only [hpb]) X hX

end HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p : ℝ) (hpa : (73/16 : ℝ) ≤ p) (hpb : p ≤ (37/8 : ℝ))
    (c : Fin 88) (hlo : 46 ≤ c.val) (hhi : c.val < 54)
    (hn63 : c ≠ 63) (hn87 : c ≠ 87)
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (169487/100000 : ℝ) (176973/100000 : ℝ) (78599/100000 : ℝ) X (distinctOrders c) (distinctSigns c)) : False := by
  exact HlawkaSchatten.DiagonalCutoff4.coarse_distinct_p013_b023 p hpa hpb c hlo hhi hn63 hn87 X hX

#print axioms solution
