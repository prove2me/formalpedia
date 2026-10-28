-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff16.real_three_w001_s002_003
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-26T00:23:18.781183+00:00
-- url     : https://prove2.me/submissions/4ac8a9f3-80a6-4b53-9e14-5310eab8a76a

import Theorems.Thm_HlawkaSchatten_DiagonalCutoff16_nonnegative_of_curvature_margins
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff16_coarse_failure_window01
import Mathlib.Analysis.Normed.Lp.PiLp
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Definitions.Def_HlawkaSchatten_GapComparison
import Definitions.Def_HlawkaSchatten_DiagonalConstruction_Basic
import Definitions.Def_HlawkaSchatten_DiagonalConstruction_Normalization
import Mathlib.Tactic.Abel
import Mathlib.Analysis.Convex.Function
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Analysis.Convex.SpecificFunctions.Pow
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Analysis.Normed.Module.Convex
import Definitions.Def_HlawkaSchatten_DiagonalConstruction_ScalarBounds
import Mathlib.Analysis.Convex.Jensen
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Tactic.Ring
import Mathlib.Analysis.MeanInequalities
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Definitions.Def_HlawkaSchatten_DiagonalConstruction_Coordinates
import Definitions.Def_HlawkaSchatten_DiagonalConstruction_Localization
import Mathlib.Tactic.FinCases
import Definitions.Def_HlawkaSchatten_DiagonalConstruction_Cyclic
import Definitions.Def_HlawkaSchatten_DiagonalConstruction_NormHessian
import Mathlib.Analysis.InnerProductSpace.NormPow
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Definitions.Def_HlawkaSchatten_DiagonalConstruction_BoxGeometry
import Definitions.Def_HlawkaSchatten_DiagonalConstruction_BoxCoordinates
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.GCongr
import Definitions.Def_HlawkaSchatten_DiagonalConstruction_BoxConvexity
import Definitions.Def_HlawkaSchatten_DiagonalConstruction_BoxHessian
import Mathlib.Topology.Order.Compact

/- Generic proofs reused from accepted Prove2Me submissions 4753aff4-c621-4df6-9535-63c865f87fd0 and de577b6b-0253-45ac-9b17-ccf002bb69a6. Original authors Ezzeri Esa, bwdaugherty and Yuxuan Xu; Apache-2.0. -/
open HlawkaSchatten HlawkaSchatten.DiagonalConstruction
set_option maxHeartbeats 4000000
namespace HlawkaSchatten.DiagonalFailureBundle
def coordinateBox (ell u v w : ℝ) (X : Fin 3 → Fin 3 → ℝ) : Prop :=
  ∀ j i, if j = i then -u ≤ X j i ∧ X j i ≤ -ell
    else v ≤ X j i ∧ X j i ≤ w
end HlawkaSchatten.DiagonalFailureBundle

/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

/-!
# Coordinate norms for the diagonal construction

The explicit finite power sum keeps coordinate arguments independent of
the exponent-indexed `PiLp` type. Its norm laws are inherited from `PiLp`.
-/

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
/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

/-! # Relabeling and normalization of a strict counterexample -/

namespace HlawkaSchatten.DiagonalConstruction

variable {ι : Type*} [Fintype ι]

/-- The deficit expressed in terms of gap functions. -/
theorem hlawkaDeficit_eq (p K : ℝ) (x y z : ι → ℝ) :
    hlawkaDeficit p K x y z =
      K * pairGapSum (lpNorm p) x y z - tripleGap (lpNorm p) x y z := by
  unfold hlawkaDeficit pairGapSum pairGap tripleGap
  ring

/-- The deficit is symmetric in the first two arguments. -/
theorem hlawkaDeficit_swap_left (p K : ℝ) (x y z : ι → ℝ) :
    hlawkaDeficit p K y x z = hlawkaDeficit p K x y z := by
  simp only [hlawkaDeficit, add_comm, add_left_comm, add_assoc]

/-- The deficit is symmetric in the last two arguments. -/
theorem hlawkaDeficit_swap_right (p K : ℝ) (x y z : ι → ℝ) :
    hlawkaDeficit p K x z y = hlawkaDeficit p K x y z := by
  simp only [hlawkaDeficit, add_comm, add_left_comm, add_assoc]

/-- Flipping to `(-(x+y+z), y, z)` exchanges the total norm with a singleton norm. -/
theorem lpNorm_flip_total (p : ℝ) (x y z : ι → ℝ) :
    lpNorm p (-(x + y + z) + y + z) = lpNorm p x := by
  have h : -(x + y + z) + y + z = -x := by abel
  rw [h, lpNorm_neg]

/-- The deficit of `(-(x+y+z), y, z)` differs from that of `(x, y, z)` by
`(2K - 2)(N(x+y+z) - N(x))`. -/
theorem hlawkaDeficit_flip (p K : ℝ) (x y z : ι → ℝ) :
    hlawkaDeficit p K (-(x + y + z)) y z = hlawkaDeficit p K x y z +
      (2 * K - 2) * (lpNorm p (x + y + z) - lpNorm p x) := by
  have hxy : -(x + y + z) + y = -(x + z) := by abel
  have hxz : -(x + y + z) + z = -(x + y) := by abel
  unfold hlawkaDeficit
  rw [lpNorm_flip_total, hxy, hxz]
  simp only [lpNorm_neg]
  ring

/-- A failed inequality can be relabeled so that its total norm is largest. -/
theorem exists_failure_total_largest {p K : ℝ} (hK : 1 ≤ K)
    (x y z : ι → ℝ) (hfail : hlawkaDeficit p K x y z < 0) :
    ∃ u v w : ι → ℝ, hlawkaDeficit p K u v w < 0 ∧
      lpNorm p u ≤ lpNorm p (u + v + w) ∧
      lpNorm p v ≤ lpNorm p (u + v + w) ∧
      lpNorm p w ≤ lpNorm p (u + v + w) := by
  have hmax : ∃ u v w : ι → ℝ, hlawkaDeficit p K u v w < 0 ∧
      lpNorm p v ≤ lpNorm p u ∧ lpNorm p w ≤ lpNorm p u := by
    rcases le_total (lpNorm p y) (lpNorm p x) with hxy | hxy
    · rcases le_total (lpNorm p z) (lpNorm p x) with hxz | hxz
      · exact ⟨x, y, z, hfail, hxy, hxz⟩
      · refine ⟨z, x, y, ?_, hxz, hxy.trans hxz⟩
        rw [hlawkaDeficit_swap_left, hlawkaDeficit_swap_right]
        exact hfail
    · rcases le_total (lpNorm p z) (lpNorm p y) with hyz | hyz
      · refine ⟨y, x, z, ?_, hxy, hyz⟩
        rw [hlawkaDeficit_swap_left]
        exact hfail
      · refine ⟨z, x, y, ?_, hxy.trans hyz, hyz⟩
        rw [hlawkaDeficit_swap_left, hlawkaDeficit_swap_right]
        exact hfail
  obtain ⟨u, v, w, hf, hv, hw⟩ := hmax
  rcases le_total (lpNorm p u) (lpNorm p (u + v + w)) with hu | hu
  · exact ⟨u, v, w, hf, hu, hv.trans hu, hw.trans hu⟩
  · refine ⟨-(u + v + w), v, w, ?_, ?_, ?_, ?_⟩
    · rw [hlawkaDeficit_flip]
      have hprod := mul_nonpos_of_nonneg_of_nonpos
        (by linarith : 0 ≤ 2 * K - 2) (sub_nonpos.mpr hu)
      linarith
    · simpa only [lpNorm_neg, lpNorm_flip_total] using hu
    · simpa only [lpNorm_flip_total] using hv
    · simpa only [lpNorm_flip_total] using hw

/-- The deficit scales linearly with `|c|` under scalar multiplication. -/
theorem hlawkaDeficit_smul {p : ℝ} (hp : 0 < p) (K c : ℝ) (x y z : ι → ℝ) :
    hlawkaDeficit p K (c • x) (c • y) (c • z) = |c| * hlawkaDeficit p K x y z := by
  simp only [hlawkaDeficit, ← smul_add, lpNorm_smul hp]
  ring

/-- A failure triple has positive norm sum. -/
theorem failure_sum_pos {p K : ℝ} (hp : 0 < p) (x y z : ι → ℝ)
    (hfail : hlawkaDeficit p K x y z < 0) :
    0 < lpNorm p x + lpNorm p y + lpNorm p z := by
  have hx := lpNorm_nonneg p x
  have hy := lpNorm_nonneg p y
  have hz := lpNorm_nonneg p z
  by_contra hn
  have hnx : lpNorm p x = 0 := by linarith
  have hny : lpNorm p y = 0 := by linarith
  have hnz : lpNorm p z = 0 := by linarith
  have hx0 := (lpNorm_eq_zero_iff hp x).mp hnx
  have hy0 := (lpNorm_eq_zero_iff hp y).mp hny
  have hz0 := (lpNorm_eq_zero_iff hp z).mp hnz
  subst x; subst y; subst z
  simp [hlawkaDeficit, lpNorm_zero hp] at hfail

/-- Normalize after relabeling. No positivity of a pair-gap denominator is assumed. -/
theorem exists_normalized_failure {p K : ℝ} (hp : 0 < p) (hK : 1 ≤ K)
    (x y z : ι → ℝ) (hfail : hlawkaDeficit p K x y z < 0) :
    ∃ u v w : ι → ℝ, hlawkaDeficit p K u v w < 0 ∧
      lpNorm p u + lpNorm p v + lpNorm p w = 1 ∧
      lpNorm p u ≤ lpNorm p (u + v + w) ∧
      lpNorm p v ≤ lpNorm p (u + v + w) ∧
      lpNorm p w ≤ lpNorm p (u + v + w) := by
  obtain ⟨u, v, w, hf, hu, hv, hw⟩ := exists_failure_total_largest hK x y z hfail
  let s := lpNorm p u + lpNorm p v + lpNorm p w
  have hs : 0 < s := failure_sum_pos hp u v w hf
  refine ⟨s⁻¹ • u, s⁻¹ • v, s⁻¹ • w, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hlawkaDeficit_smul hp, abs_of_pos (inv_pos.mpr hs)]
    exact mul_neg_of_pos_of_neg (inv_pos.mpr hs) hf
  · simp only [lpNorm_smul hp, abs_of_pos (inv_pos.mpr hs)]
    rw [← mul_add, ← mul_add]
    exact inv_mul_cancel₀ hs.ne'
  all_goals
    simp only [← smul_add, lpNorm_smul hp, abs_of_pos (inv_pos.mpr hs)]
  · exact mul_le_mul_of_nonneg_left hu (inv_nonneg.mpr hs.le)
  · exact mul_le_mul_of_nonneg_left hv (inv_nonneg.mpr hs.le)
  · exact mul_le_mul_of_nonneg_left hw (inv_nonneg.mpr hs.le)

end HlawkaSchatten.DiagonalConstruction

namespace HlawkaSchatten.DiagonalConstruction

variable {ι : Type*} [Fintype ι]

/-- The power sum is nonneg. -/
theorem powerSum_nonneg (p : ℝ) (v : ι → ℝ) : 0 ≤ powerSum p v :=
  Finset.sum_nonneg fun i _ ↦ Real.rpow_nonneg (abs_nonneg (v i)) p

/-- The power sum equals the `p`-norm raised to `p`. -/
theorem powerSum_eq_lpNorm_rpow {p : ℝ} (hp : 0 < p) (v : ι → ℝ) :
    powerSum p v = lpNorm p v ^ p := by
  rw [lpNorm_rpow hp]
  rfl

/-- The power sum is strictly positive for nonzero `v`. -/
theorem powerSum_pos {p : ℝ} (hp : 0 < p) {v : ι → ℝ} (hv : v ≠ 0) : 0 < powerSum p v := by
  rw [powerSum_eq_lpNorm_rpow hp]
  exact Real.rpow_pos_of_pos (lpNorm_pos hp hv) p

omit [Fintype ι] in
private theorem abs_rpow_mul_sq {q : ℝ} (hq : 0 < q) (x : ℝ) :
    |x| ^ q * x ^ 2 = |x| ^ (q + 2) := by
  by_cases hx : x = 0
  · simp [hx, hq.ne', show q + 2 ≠ 0 by linarith]
  · rw [← sq_abs, ← Real.rpow_two, ← Real.rpow_add (abs_pos.mpr hx)]

/-- The quadratic form at `h = v` equals the power sum. -/
theorem powerQuad_self {p : ℝ} (hp : 2 < p) (v : ι → ℝ) :
    powerQuad p v v = powerSum p v := by
  unfold powerQuad powerSum
  apply Finset.sum_congr rfl
  intro i _
  simpa only [sub_add_cancel] using abs_rpow_mul_sq (by linarith : 0 < p - 2) (v i)

/-- The power residual decomposes into radial and tangential parts. -/
theorem powerResidual_eq {p : ℝ} (hp : 2 < p) (v h : ι → ℝ) (a : ℝ) :
    powerResidual p v h a = powerQuad p v h - 2 * a * powerPair p v h + a ^ 2 * powerSum p v := by
  rw [← powerQuad_self hp v]
  simp only [powerResidual, powerQuad, powerPair, Finset.mul_sum, ← Finset.sum_sub_distrib,
    ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  ring

/-- The optimal radial coefficient minimizes the residual. -/
theorem powerResidual_radial {p : ℝ} (hp : 2 < p) (v h : ι → ℝ) (hv : v ≠ 0) :
    powerResidual p v h (radialCoefficient p v h) =
      powerQuad p v h - powerPair p v h ^ 2 / powerSum p v := by
  rw [powerResidual_eq hp, radialCoefficient]
  field_simp [(powerSum_pos (by linarith : 0 < p) hv).ne']
  ring

/-- The residual at the optimal coefficient is minimal. -/
theorem powerResidual_min {p : ℝ} (hp : 2 < p) (v h : ι → ℝ) (hv : v ≠ 0) (a : ℝ) :
    powerResidual p v h (radialCoefficient p v h) ≤ powerResidual p v h a := by
  have hS := powerSum_pos (by linarith : 0 < p) hv
  rw [powerResidual_radial hp v h hv, powerResidual_eq hp]
  have hn := mul_nonneg hS.le (sq_nonneg (a - powerPair p v h / powerSum p v))
  have hmul : powerSum p v * (powerPair p v h / powerSum p v) = powerPair p v h :=
    mul_div_cancel₀ _ hS.ne'
  have hmul2 : powerSum p v * (powerPair p v h / powerSum p v) ^ 2 =
      powerPair p v h ^ 2 / powerSum p v := by field_simp
  nlinarith [congrArg (fun x : ℝ ↦ a * x) hmul]

/-- The power residual is nonneg. -/
theorem powerResidual_nonneg (p : ℝ) (v h : ι → ℝ) (a : ℝ) : 0 ≤ powerResidual p v h a :=
  Finset.sum_nonneg fun i _ ↦ mul_nonneg
    (Real.rpow_nonneg (abs_nonneg (v i)) (p - 2)) (sq_nonneg (h i - a * v i))

/-- The norm Hessian is nonneg for `p ≥ 1`. -/
theorem normHessian_nonneg {p : ℝ} (hp : 1 ≤ p) (v h : ι → ℝ) : 0 ≤ normHessian p v h :=
  mul_nonneg (mul_nonneg (sub_nonneg.mpr hp) (Real.rpow_nonneg (powerSum_nonneg p v) _))
    (powerResidual_nonneg p v h _)

/-- The norm Hessian is bounded by the power residual. -/
theorem normHessian_le_residual {p : ℝ} (hp : 2 < p) (v h : ι → ℝ) (hv : v ≠ 0) (a : ℝ) :
    normHessian p v h ≤ (p - 1) * powerSum p v ^ (1 / p - 1) * powerResidual p v h a := by
  exact mul_le_mul_of_nonneg_left (powerResidual_min hp v h hv a)
    (mul_nonneg (by linarith) (Real.rpow_nonneg (powerSum_nonneg p v) _))

omit [Fintype ι] in
private theorem hasDerivAt_abs_power_slope {p : ℝ} (hp : 4 < p) (x : ℝ) :
    HasDerivAt (fun x : ℝ ↦ |x| ^ (p - 2) * x) ((p - 1) * |x| ^ (p - 2)) x := by
  have h := (hasDerivAt_abs_rpow x (by linarith : 1 < p - 2)).mul (hasDerivAt_id x)
  have heq : ((p - 2) * |x| ^ (p - 2 - 2) * x) * x + |x| ^ (p - 2) * 1 =
      (p - 1) * |x| ^ (p - 2) := by
    have hh := abs_rpow_mul_sq (by linarith : 0 < p - 2 - 2) x
    have hcancel : p - 2 - 2 + 2 = p - 2 := by ring
    rw [hcancel] at hh
    nlinarith
  convert! h using 1
  simpa only [id_eq] using heq.symm

/-- Differentiability of the power sum along a line. -/
theorem hasDerivAt_powerSum_line {p : ℝ} (hp : 1 < p) (v h : ι → ℝ) (t : ℝ) :
    HasDerivAt (fun s : ℝ ↦ powerSum p (v + s • h))
      (p * powerPair p (v + t • h) h) t := by
  have hi (i : ι) : HasDerivAt (fun s : ℝ ↦ |v i + s * h i| ^ p)
      (p * |v i + t * h i| ^ (p - 2) * (v i + t * h i) * h i) t := by
    simpa only [one_mul, id_eq, Function.comp_def] using
      (hasDerivAt_abs_rpow _ hp).comp t (((hasDerivAt_id t).mul_const (h i)).const_add (v i))
  simpa only [powerSum, powerPair, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum,
    mul_assoc] using HasDerivAt.fun_sum (u := Finset.univ) (fun i _ ↦ hi i)

/-- Differentiability of the first-order form along a line. -/
theorem hasDerivAt_powerPair_line {p : ℝ} (hp : 4 < p) (v h : ι → ℝ) (t : ℝ) :
    HasDerivAt (fun s : ℝ ↦ powerPair p (v + s • h) h)
      ((p - 1) * powerQuad p (v + t • h) h) t := by
  have hi (i : ι) := ((hasDerivAt_abs_power_slope hp (v i + t * h i)).comp t
    (((hasDerivAt_id t).mul_const (h i)).const_add (v i))).mul_const (h i)
  simpa only [powerPair, powerQuad, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum,
    pow_two, mul_assoc, Function.comp_def, id_eq, one_mul] using
      HasDerivAt.fun_sum (u := Finset.univ) (fun i _ ↦ hi i)

/-- Differentiability of the `p`-norm along a line. -/
theorem hasDerivAt_lpNorm_line {p : ℝ} (hp : 1 < p) (v h : ι → ℝ) (t : ℝ)
    (hv : v + t • h ≠ 0) :
    HasDerivAt (fun s : ℝ ↦ lpNorm p (v + s • h)) (normSlope p (v + t • h) h) t := by
  have hp0 := zero_lt_one.trans hp
  have hh := (hasDerivAt_powerSum_line hp v h t).rpow_const (p := 1 / p)
    (Or.inl (powerSum_pos hp0 hv).ne')
  have he : p * powerPair p (v + t • h) h * (1 / p) * powerSum p (v + t • h) ^ (1 / p - 1) =
      normSlope p (v + t • h) h := by
    unfold normSlope
    field_simp
  convert hh using 1
  · rfl
  · exact he.symm

/-- Differentiability of the norm slope along a line. -/
theorem hasDerivAt_normSlope_line {p : ℝ} (hp : 4 < p) (v h : ι → ℝ) (t : ℝ)
    (hv : v + t • h ≠ 0) :
    HasDerivAt (fun s : ℝ ↦ normSlope p (v + s • h) h) (normHessian p (v + t • h) h) t := by
  have hp0 : 0 < p := by linarith
  have hS := powerSum_pos hp0 hv
  have hh := ((hasDerivAt_powerSum_line (by linarith) v h t).rpow_const (p := 1 / p - 1)
    (Or.inl hS.ne')).mul (hasDerivAt_powerPair_line hp v h t)
  have hpow : powerSum p (v + t • h) ^ (1 / p - 1 - 1) =
      powerSum p (v + t • h) ^ (1 / p - 1) / powerSum p (v + t • h) := by
    rw [Real.rpow_sub hS, Real.rpow_one]
  have he : (p * powerPair p (v + t • h) h * (1 / p - 1) *
      powerSum p (v + t • h) ^ (1 / p - 1 - 1)) * powerPair p (v + t • h) h +
      powerSum p (v + t • h) ^ (1 / p - 1) * ((p - 1) * powerQuad p (v + t • h) h) =
        normHessian p (v + t • h) h := by
    rw [normHessian, powerResidual_radial (by linarith) _ _ hv, hpow]
    field_simp
    ring
  rwa [he] at hh

/-- The first-order form with a radial correction. -/
theorem powerPair_sub_smul {p : ℝ} (hp : 2 < p) (v h : ι → ℝ) (a : ℝ) :
    powerPair p v (h - a • v) = powerPair p v h - a * powerSum p v := by
  rw [← powerQuad_self hp v]
  simp only [powerPair, powerQuad, Pi.sub_apply, Pi.smul_apply, smul_eq_mul,
    Finset.mul_sum, ← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun i _ ↦ by ring

/-- The norm Hessian with a radial correction. -/
theorem normHessian_sub_smul {p : ℝ} (hp : 2 < p) (v h : ι → ℝ) (hv : v ≠ 0) (a : ℝ) :
    normHessian p v (h - a • v) = normHessian p v h := by
  simp only [normHessian, powerResidual_radial hp v _ hv, powerPair_sub_smul hp]
  congr 1
  have hquad : powerQuad p v (h - a • v) = powerResidual p v h a := rfl
  rw [hquad, powerResidual_eq hp]
  field_simp [(powerSum_pos (by linarith : 0 < p) hv).ne']
  ring

/-- The `(p-1)/p`-th power of the power sum root. -/
theorem powerSum_root_pred {p : ℝ} (hp : 0 < p) (v : ι → ℝ) :
    powerSum p v ^ (1 / p - 1) = (lpNorm p v ^ (p - 1))⁻¹ := by
  rw [powerSum_eq_lpNorm_rpow hp, ← Real.rpow_mul (lpNorm_nonneg p v),
    show p * (1 / p - 1) = -(p - 1) by field_simp; ring,
    Real.rpow_neg (lpNorm_nonneg p v)]

/-- The norm Hessian as a ratio of quadratic form to power sum. -/
theorem normHessian_eq_div {p : ℝ} (hp : 0 < p) (v h : ι → ℝ) :
    normHessian p v h = (p - 1) / lpNorm p v ^ (p - 1) *
      powerResidual p v h (radialCoefficient p v h) := by
  rw [normHessian, powerSum_root_pred hp]
  rfl

end HlawkaSchatten.DiagonalConstruction

open HlawkaSchatten HlawkaSchatten.DiagonalConstruction


/- Adapted from @bwdaugherty's accepted cutoff-32 contribution,
   submission d75400b0-5a0e-4167-8192-7fd299469c2e (2026-10-16),
   https://prove2.me/theorems/4e05427b-74d9-4e61-8d14-a52384a5ca10 .
   Public Prove2Me contribution under Apache-2.0; see sources/NOTICE.md.
   These generic lemmas do not assume p >= 32. -/
set_option autoImplicit false

namespace HlawkaSchatten.DiagonalRealBundle

/-- Increments of `x ↦ x ^ p` over intervals of equal length grow to the right. -/
theorem rpow_swap_le {p : ℝ} (hp : 1 ≤ p) {x y c : ℝ} (hx : 0 ≤ x) (hxy : x ≤ y)
    (hc : 0 ≤ c) : (x + c) ^ p + y ^ p ≤ x ^ p + (y + c) ^ p := by
  rcases eq_or_lt_of_le (show (0:ℝ) ≤ y - x + c by linarith) with h | h
  · have hc0 : c = 0 := by linarith
    have hy : y = x := by linarith
    subst hc0 hy; simp
  · have hconv := (convexOn_rpow hp).2
    have hxm : x ∈ Set.Ici (0:ℝ) := Set.mem_Ici.2 hx
    have hym : y + c ∈ Set.Ici (0:ℝ) := Set.mem_Ici.2 (by linarith)
    have hl : 0 ≤ (y - x) / (y - x + c) := div_nonneg (by linarith) h.le
    have hm : 0 ≤ c / (y - x + c) := div_nonneg hc h.le
    have hs : (y - x) / (y - x + c) + c / (y - x + c) = 1 := by
      rw [← add_div, div_self h.ne']
    have h1 := hconv hxm hym hl hm hs
    have h2 := hconv hxm hym hm hl (by linarith)
    simp only [smul_eq_mul] at h1 h2
    have e1 : (y - x) / (y - x + c) * x + c / (y - x + c) * (y + c) = x + c := by
      field_simp; ring
    have e2 : c / (y - x + c) * x + (y - x) / (y - x + c) * (y + c) = y := by
      field_simp; ring
    rw [e1] at h1
    rw [e2] at h2
    calc (x + c) ^ p + y ^ p ≤ _ := add_le_add h1 h2
      _ = ((y - x) / (y - x + c) + c / (y - x + c)) * (x ^ p + (y + c) ^ p) := by ring
      _ = _ := by rw [hs, one_mul]

/-- Power mean for two terms. -/
theorem add_rpow_le_two {p : ℝ} (hp : 1 ≤ p) {u v : ℝ} (hu : 0 ≤ u) (hv : 0 ≤ v) :
    (u + v) ^ p ≤ 2 ^ p / 2 * (u ^ p + v ^ p) := by
  have h := (convexOn_rpow hp).2 (Set.mem_Ici.2 hu) (Set.mem_Ici.2 hv)
    (by norm_num : (0:ℝ) ≤ 1/2) (by norm_num : (0:ℝ) ≤ 1/2) (by norm_num)
  simp only [smul_eq_mul] at h
  have e : 1/2 * u + 1/2 * v = (u + v) / 2 := by ring
  rw [e, Real.div_rpow (by linarith) (by norm_num)] at h
  have h2p : 0 < (2:ℝ) ^ p := Real.rpow_pos_of_pos (by norm_num) p
  rw [div_le_iff₀ h2p] at h
  calc (u + v) ^ p ≤ _ := h
    _ = _ := by ring

/-- The two-coordinate constant `2 ^ (1 - 1/p)`. -/
noncomputable def cp (p : ℝ) : ℝ := 2 * (1/2 : ℝ) ^ (1/p)

theorem cp_pos (p : ℝ) : 0 < cp p := by unfold cp; positivity

theorem cp_rpow {p : ℝ} (hp : 0 < p) : cp p ^ p = 2 ^ p / 2 := by
  unfold cp
  rw [Real.mul_rpow (by norm_num) (by positivity), ← Real.rpow_mul (by norm_num),
    one_div_mul_cancel hp.ne', Real.rpow_one]; ring

theorem sum_div_cp_rpow_le {p : ℝ} (hp : 1 ≤ p) {u v : ℝ} (hu : 0 ≤ u) (hv : 0 ≤ v) :
    ((u + v) / cp p) ^ p ≤ u ^ p + v ^ p := by
  have hp0 : 0 < p := by linarith
  rw [Real.div_rpow (by linarith) (cp_pos p).le, cp_rpow hp0, div_le_iff₀ (by positivity)]
  rw [mul_comm]; exact add_rpow_le_two hp hu hv

theorem sum_le_cp_mul {p : ℝ} (hp : 1 ≤ p) {u v S : ℝ} (hu : 0 ≤ u) (hv : 0 ≤ v)
    (hS : 0 ≤ S) (h : u ^ p + v ^ p ≤ S ^ p) : u + v ≤ cp p * S := by
  have hp0 : 0 < p := by linarith
  have h1 := (sum_div_cp_rpow_le hp hu hv).trans h
  have h2 : (u + v) / cp p ≤ S :=
    (Real.rpow_le_rpow_iff (div_nonneg (by linarith) (cp_pos p).le) hS hp0).1 h1
  rw [div_le_iff₀ (cp_pos p)] at h2; linarith

/-- Diagonal certificate: a row with nearly extremal two-coordinate mass has a small
diagonal entry. -/
theorem diag_cert {p : ℝ} (hp : 1 ≤ p) {a w c N D δ U Ab : ℝ} (ha : 0 ≤ a) (hc : 0 < c)
    (hrow : a ^ p + (w / c) ^ p ≤ N ^ p) (hw : c * N - D ≤ w) (hDc : D / c ≤ δ)
    (hδ : 0 ≤ δ) (hδN : δ ≤ N) (hNU : N ≤ U) (hU : 0 < U) (hAb : 0 ≤ Ab)
    (hcert : 1 ≤ (Ab / U) ^ p + (1 - δ / U) ^ p) : a ≤ Ab := by
  have hp0 : 0 < p := by linarith
  have h1 : N - δ ≤ w / c := by
    have e : w / c = N - D / c + (w - (c * N - D)) / c := by field_simp; ring
    rw [e]
    have : 0 ≤ (w - (c * N - D)) / c := div_nonneg (by linarith) hc.le
    linarith
  have h2 : (N - δ) ^ p ≤ (w / c) ^ p := Real.rpow_le_rpow (by linarith) h1 hp0.le
  have h3 := rpow_swap_le hp (x := N - δ) (y := U - δ) (c := δ) (by linarith) (by linarith) hδ
  rw [sub_add_cancel, sub_add_cancel] at h3
  have h4 : U ^ p ≤ Ab ^ p + (U - δ) ^ p := by
    have e : 1 - δ / U = (U - δ) / U := by field_simp
    rw [e, Real.div_rpow hAb hU.le, Real.div_rpow (by linarith) hU.le, ← add_div,
      le_div_iff₀ (by positivity), one_mul] at hcert
    exact hcert
  have h5 : a ^ p ≤ Ab ^ p := by linarith
  exact (Real.rpow_le_rpow_iff ha hAb hp0).1 h5

/-- Two-dimensional Minkowski inequality in power form. -/
theorem mink2 {p : ℝ} (hp : 1 ≤ p) {x1 y1 x2 y2 N1 N2 : ℝ} (hx1 : 0 ≤ x1) (hy1 : 0 ≤ y1)
    (hx2 : 0 ≤ x2) (hy2 : 0 ≤ y2) (hN1 : 0 ≤ N1) (hN2 : 0 ≤ N2)
    (h1 : x1 ^ p + y1 ^ p ≤ N1 ^ p) (h2 : x2 ^ p + y2 ^ p ≤ N2 ^ p) :
    (x1 + x2) ^ p + (y1 + y2) ^ p ≤ (N1 + N2) ^ p := by
  have hp0 : 0 < p := by linarith
  have hM := Real.Lp_add_le (Finset.univ : Finset (Fin 2)) ![x1, y1] ![x2, y2] hp
  simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_fin_one] at hM
  rw [abs_of_nonneg (by linarith : 0 ≤ x1 + x2), abs_of_nonneg (by linarith : 0 ≤ y1 + y2),
    abs_of_nonneg hx1, abs_of_nonneg hy1, abs_of_nonneg hx2, abs_of_nonneg hy2] at hM
  have hr1 : (x1 ^ p + y1 ^ p) ^ (1/p) ≤ N1 := by
    calc (x1 ^ p + y1 ^ p) ^ (1/p) ≤ (N1 ^ p) ^ (1/p) :=
          Real.rpow_le_rpow (by positivity) h1 (by positivity)
      _ = N1 := by rw [one_div, Real.rpow_rpow_inv hN1 hp0.ne']
  have hr2 : (x2 ^ p + y2 ^ p) ^ (1/p) ≤ N2 := by
    calc (x2 ^ p + y2 ^ p) ^ (1/p) ≤ (N2 ^ p) ^ (1/p) :=
          Real.rpow_le_rpow (by positivity) h2 (by positivity)
      _ = N2 := by rw [one_div, Real.rpow_rpow_inv hN2 hp0.ne']
  have h3 : ((x1 + x2) ^ p + (y1 + y2) ^ p) ^ (1/p) ≤ N1 + N2 := by linarith
  have hS : 0 ≤ (x1 + x2) ^ p + (y1 + y2) ^ p := by positivity
  calc (x1 + x2) ^ p + (y1 + y2) ^ p
      = (((x1 + x2) ^ p + (y1 + y2) ^ p) ^ (1/p)) ^ p := by
        rw [← Real.rpow_mul hS, one_div_mul_cancel hp0.ne', Real.rpow_one]
    _ ≤ (N1 + N2) ^ p := Real.rpow_le_rpow (by positivity) h3 hp0.le

/-- Ratio lower bound from a convexity certificate. -/
theorem ratio_lower {p x y s τ : ℝ} (hp : 1 ≤ p) (hx : 0 ≤ x) (_hy : 0 ≤ y)
    (hxy : x ^ p + y ^ p ≤ 1) (hs : s ≤ x + y) (hτ0 : 0 ≤ τ) (hτs : 2 * τ ≤ s)
    (hc : 1 < τ ^ p + (s - τ) ^ p) : τ < x := by
  have hp0 : 0 < p := by linarith
  by_contra hle
  push Not at hle
  have h1 := rpow_swap_le hp (x := x) (y := s - τ) (c := τ - x) hx (by linarith) (by linarith)
  have e1 : x + (τ - x) = τ := by ring
  have e2 : s - τ + (τ - x) = s - x := by ring
  rw [e1, e2] at h1
  have h2 : (s - x) ^ p ≤ y ^ p := Real.rpow_le_rpow (by linarith) (by linarith) hp0.le
  linarith

/-- Ratio upper bound from a convexity certificate. -/
theorem ratio_upper {p x y s σ : ℝ} (hp : 1 ≤ p) (_hx : 0 ≤ x) (hy : 0 ≤ y)
    (hxy : x ^ p + y ^ p ≤ 1) (hs : s ≤ x + y) (hs1 : 1 ≤ s) (hσs : s ≤ 2 * σ)
    (hc : 1 < σ ^ p + (s - σ) ^ p) : x < σ := by
  have hp0 : 0 < p := by linarith
  by_contra hle
  push Not at hle
  have hx1 : x ≤ 1 := by
    by_contra h
    push Not at h
    have : 1 < x ^ p := Real.one_lt_rpow h hp0
    have : 0 ≤ y ^ p := Real.rpow_nonneg hy p
    linarith
  have h1 := rpow_swap_le hp (x := s - x) (y := σ) (c := x - σ) (by linarith) (by linarith)
    (by linarith)
  have e1 : s - x + (x - σ) = s - σ := by ring
  have e2 : σ + (x - σ) = x := by ring
  rw [e1, e2] at h1
  have h2 : (s - x) ^ p ≤ y ^ p := Real.rpow_le_rpow (by linarith) (by linarith) hp0.le
  linarith

/-! ## Turning integer-power checks into real-exponent certificates -/

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

theorem cert_le {x y X Y : ℝ} (m k : ℕ) (hk : 0 < k) (hx0 : 0 ≤ x) (hx1 : x ≤ 1)
    (hy0 : 0 ≤ y) (hy1 : y ≤ 1) (hX : X ^ k ≤ x ^ m) (hY : Y ^ k ≤ y ^ m)
    (hXY : 1 ≤ X + Y) : ∀ p : ℝ, 0 ≤ p → p ≤ (m : ℝ) / k → 1 ≤ x ^ p + y ^ p := by
  intro p hp0 hpb
  have h1 := le_rpow_of_pow_le hx0 m k hk hX
  have h2 := le_rpow_of_pow_le hy0 m k hk hY
  have h3 : x ^ ((m : ℝ) / k) ≤ x ^ p := Real.rpow_le_rpow_of_exponent_ge' hx0 hx1 hp0 hpb
  have h4 : y ^ ((m : ℝ) / k) ≤ y ^ p := Real.rpow_le_rpow_of_exponent_ge' hy0 hy1 hp0 hpb
  linarith

theorem cert_lt {x y X Y : ℝ} (m k : ℕ) (hk : 0 < k) (hx0 : 0 ≤ x) (hx1 : x ≤ 1)
    (hy0 : 0 ≤ y) (hy1 : y ≤ 1) (hX : X ^ k ≤ x ^ m) (hY : Y ^ k ≤ y ^ m)
    (hXY : 1 < X + Y) : ∀ p : ℝ, 0 ≤ p → p ≤ (m : ℝ) / k → 1 < x ^ p + y ^ p := by
  intro p hp0 hpb
  have h1 := le_rpow_of_pow_le hx0 m k hk hX
  have h2 := le_rpow_of_pow_le hy0 m k hk hY
  have h3 : x ^ ((m : ℝ) / k) ≤ x ^ p := Real.rpow_le_rpow_of_exponent_ge' hx0 hx1 hp0 hpb
  have h4 : y ^ ((m : ℝ) / k) ≤ y ^ p := Real.rpow_le_rpow_of_exponent_ge' hy0 hy1 hp0 hpb
  linarith


end HlawkaSchatten.DiagonalRealBundle


/- Generic contraction lemmas adapted from accepted Prove2Me submission 3735254f-536b-45fe-a0c1-2ea9ffc9d938 (Yuxuan Xu, bwdaugherty; Apache-2.0). The gap budget is now an arbitrary certified bound. -/
open HlawkaSchatten HlawkaSchatten.DiagonalConstruction
set_option autoImplicit false
set_option maxHeartbeats 4000000
namespace HlawkaSchatten.DiagonalRealBundle

theorem others (i : Fin 3) : ∃ j k : Fin 3, i ≠ j ∧ i ≠ k ∧ j ≠ k := by
  fin_cases i <;> decide

theorem third {i j : Fin 3} (h : i ≠ j) : ∃ k : Fin 3, i ≠ k ∧ j ≠ k := by
  fin_cases i <;> fin_cases j <;> simp_all <;> decide

structure Facts (p c D δ h A cmax tlo : ℝ) (X : Fin 3 → Fin 3 → ℝ) (N : Fin 3 → ℝ) : Prop where
  Nnonneg : ∀ i, 0 ≤ N i
  hp : 1 ≤ p
  hc : 0 < c
  hcm : c ≤ cmax
  hct : 2 * tlo ≤ c
  hDc : D / c ≤ δ
  hA : 0 < A
  diag : ∀ i, 0 ≤ -X i i
  off : ∀ i j, i ≠ j → 0 ≤ X i j
  nsum : ∀ i j k, i ≠ j → i ≠ k → j ≠ k →
    N i + N j + N k = 3
  rowfull : ∀ i j k, i ≠ j → i ≠ k → j ≠ k →
    (-X i i) ^ p + X i j ^ p + X i k ^ p = N i ^ p
  row : ∀ i j k, i ≠ j → i ≠ k → j ≠ k →
    (-X i i) ^ p + ((X i j + X i k) / c) ^ p ≤ N i ^ p
  wD : ∀ i j k, i ≠ j → i ≠ k → j ≠ k → c * N i - D ≤ X i j + X i k
  wD2 : ∀ i j k, i ≠ j → i ≠ k → j ≠ k →
    c * (N j + N k) - D ≤ (X j i + X j k) + (X k i + X k j)
  offsum : ∀ i j k, i ≠ j → i ≠ k → j ≠ k →
    6 - h < (X i j + X i k) + (X j i + X j k) + (X k i + X k j)
  T1 : ∀ i j k, i ≠ j → i ≠ k → j ≠ k → X i i + X j i + X k i < A
  T2 : ∀ i j k, i ≠ j → i ≠ k → j ≠ k →
    (X i j + X j j + X k j) + (X i k + X j k + X k k) < cmax * A

section Rounds

variable {p c D δ h A cmax tlo : ℝ} {X : Fin 3 → Fin 3 → ℝ} {N : Fin 3 → ℝ}

theorem ratio_round (F : Facts p c D δ h A cmax tlo X N) {n s τ σ : ℝ}
    (hn : ∀ i, n ≤ N i) (hn0 : 0 < n) (hD0 : 0 ≤ D) (hs : s ≤ 2 * tlo - D / n)
    (hτ0 : 0 ≤ τ) (hτs : 2 * τ ≤ s) (hs1 : 1 ≤ s) (hσs : s ≤ 2 * σ)
    (hτc : 1 < τ ^ p + (s - τ) ^ p) (hσc : 1 < σ ^ p + (s - σ) ^ p) :
    ∀ i j k, i ≠ j → i ≠ k → j ≠ k →
      τ * N i < X i j ∧ X i j < σ * N i := by
  intro i j k hij hik hjk
  have hp0 : 0 < p := by linarith [F.hp]
  have hN : 0 < N i := lt_of_lt_of_le hn0 (hn i)
  set Ni := N i with hNdef
  have hbj := F.off i j hij
  have hbk := F.off i k hik
  have hxy : (X i j / Ni) ^ p + (X i k / Ni) ^ p ≤ 1 := by
    rw [Real.div_rpow (by linarith) hN.le, Real.div_rpow (by linarith) hN.le, ← add_div,
      div_le_one (by positivity)]
    have := F.rowfull i j k hij hik hjk
    have := Real.rpow_nonneg (F.diag i) p
    linarith
  have hsum : s ≤ X i j / Ni + X i k / Ni := by
    rw [← add_div, le_div_iff₀ hN]
    have a1 : s * Ni ≤ (2 * tlo - D / n) * Ni := mul_le_mul_of_nonneg_right hs hN.le
    have a2 : D ≤ D / n * Ni := by
      rw [div_mul_eq_mul_div, le_div_iff₀ hn0]; exact mul_le_mul_of_nonneg_left (hn i) hD0
    have a3 : 2 * tlo * Ni ≤ c * Ni := mul_le_mul_of_nonneg_right F.hct hN.le
    have a4 := F.wD i j k hij hik hjk
    have e : (2 * tlo - D / n) * Ni = 2 * tlo * Ni - D / n * Ni := by ring
    linarith
  have h1 := ratio_lower F.hp (by positivity) (by positivity) hxy hsum hτ0 hτs hτc
  have h2 := ratio_upper F.hp (by positivity) (by positivity) hxy hsum hs1 hσs hσc
  exact ⟨(lt_div_iff₀ hN).1 h1, (div_lt_iff₀ hN).1 h2⟩

theorem lower_round (F : Facts p c D δ h A cmax tlo X N) {n τ n' Ab : ℝ}
    (hn : ∀ i, n ≤ N i) (hδn : δ ≤ n) (hδ0 : 0 ≤ δ) (hτ0 : 0 ≤ τ)
    (hr : ∀ i j k, i ≠ j → i ≠ k → j ≠ k → τ * N i < X i j)
    (hn'0 : 0 < n') (hAb : 0 ≤ Ab) (hcert : 1 ≤ (Ab / n') ^ p + (1 - δ / n') ^ p)
    (hchk : A ≤ τ * (3 - n') - Ab) : ∀ i, n' ≤ N i := by
  intro i
  obtain ⟨j, k, hij, hik, hjk⟩ := others i
  by_contra hlt
  push Not at hlt
  have ha := diag_cert F.hp (F.diag i) F.hc (F.row i j k hij hik hjk) (F.wD i j k hij hik hjk)
    F.hDc hδ0 (hδn.trans (hn i)) hlt.le hn'0 hAb hcert
  have t1 := F.T1 i j k hij hik hjk
  have r1 := hr j i k (Ne.symm hij) hjk hik
  have r2 := hr k i j (Ne.symm hik) (Ne.symm hjk) hij
  have ns := F.nsum i j k hij hik hjk
  have m1 : τ * (3 - n') ≤ τ * (N j + N k) :=
    mul_le_mul_of_nonneg_left (by linarith) hτ0
  rw [mul_add] at m1
  linarith

theorem upper_round (F : Facts p c D δ h A cmax tlo X N) {n σ U Ab : ℝ}
    (hn : ∀ i, n ≤ N i) (hδn : δ ≤ n) (hδ0 : 0 ≤ δ) (hσ0 : 0 ≤ σ)
    (hr : ∀ i j k, i ≠ j → i ≠ k → j ≠ k → X i j < σ * N i)
    (hU3 : U < 3) (hAb : 0 ≤ Ab) (hcert : 1 ≤ (Ab / (3 - U)) ^ p + (1 - δ / (3 - U)) ^ p)
    (hchk : cmax * A ≤ 6 - h - σ * (3 - U) - Ab) : ∀ i, N i ≤ U := by
  intro i
  obtain ⟨j, k, hij, hik, hjk⟩ := others i
  by_contra hlt
  push Not at hlt
  have ns := F.nsum i j k hij hik hjk
  have rj := F.row j i k (Ne.symm hij) hjk hik
  have rk := F.row k i j (Ne.symm hik) (Ne.symm hjk) hij
  have hbji := F.off j i (Ne.symm hij)
  have hbjk := F.off j k hjk
  have hbki := F.off k i (Ne.symm hik)
  have hbkj := F.off k j (Ne.symm hjk)
  have hm := mink2 F.hp (F.diag j) (div_nonneg (by linarith) F.hc.le) (F.diag k)
    (div_nonneg (by linarith) F.hc.le) (F.Nnonneg j) (F.Nnonneg k) rj rk
  rw [← add_div] at hm
  have hNj := hn j
  have hNk := hn k
  have ha := diag_cert F.hp (by linarith [F.diag j, F.diag k]) F.hc hm (F.wD2 i j k hij hik hjk)
    F.hDc hδ0 (by linarith) (by linarith : N j + N k ≤ 3 - U)
    (by linarith) hAb hcert
  have t2 := F.T2 i j k hij hik hjk
  have os := F.offsum i j k hij hik hjk
  have r1 := hr j i k (Ne.symm hij) hjk hik
  have r2 := hr k i j (Ne.symm hik) (Ne.symm hjk) hij
  have m1 : σ * (N j + N k) ≤ σ * (3 - U) :=
    mul_le_mul_of_nonneg_left (by linarith) hσ0
  rw [mul_add] at m1
  linarith

theorem final_round (F : Facts p c D δ h A cmax tlo X N) {n U τ σ Ab ell u v w : ℝ}
    (hn : ∀ i, n ≤ N i) (hU : ∀ i, N i ≤ U) (hδn : δ ≤ n)
    (hδ0 : 0 ≤ δ) (hτ0 : 0 ≤ τ) (hσ0 : 0 ≤ σ)
    (hr : ∀ i j k, i ≠ j → i ≠ k → j ≠ k →
      τ * N i < X i j ∧ X i j < σ * N i)
    (hU0 : 0 < U) (hAb : 0 ≤ Ab) (hcert : 1 ≤ (Ab / U) ^ p + (1 - δ / U) ^ p)
    (h1 : v ≤ τ * n) (h2 : σ * U ≤ w) (h3 : Ab ≤ u)
    (h4 : ell ≤ τ * (3 - U) - A) : (∀ j i, if j = i then -u ≤ X j i ∧ X j i ≤ -ell
      else v ≤ X j i ∧ X j i ≤ w) := by
  intro j i
  by_cases hji : j = i
  · subst hji
    rw [if_pos rfl]
    obtain ⟨k, l, hjk, hjl, hkl⟩ := others j
    have ha := diag_cert F.hp (F.diag j) F.hc (F.row j k l hjk hjl hkl)
      (F.wD j k l hjk hjl hkl) F.hDc hδ0 (hδn.trans (hn j)) (hU j) hU0 hAb hcert
    have t1 := F.T1 j k l hjk hjl hkl
    have r1 := (hr k j l (Ne.symm hjk) hkl hjl).1
    have r2 := (hr l j k (Ne.symm hjl) (Ne.symm hkl) hjk).1
    have ns := F.nsum j k l hjk hjl hkl
    have m1 : τ * (3 - U) ≤ τ * (N k + N l) :=
      mul_le_mul_of_nonneg_left (by linarith [hU j]) hτ0
    rw [mul_add] at m1
    constructor <;> linarith
  · rw [if_neg hji]
    obtain ⟨k, hjk, hik⟩ := third hji
    have r := hr j i k hji hjk hik
    have m1 : τ * n ≤ τ * N j := mul_le_mul_of_nonneg_left (hn j) hτ0
    have m2 : σ * N j ≤ σ * U := mul_le_mul_of_nonneg_left (hU j) hσ0
    constructor <;> linarith [r.1, r.2]

end Rounds


end HlawkaSchatten.DiagonalRealBundle

namespace HlawkaSchatten.DiagonalRealBundle
open HlawkaSchatten.DiagonalConstruction
abbrev Triple := Fin 3 → Fin 3 → ℝ

theorem sum3 (f : Fin 3 → ℝ) {i j k : Fin 3} (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
    ∑ l, f l = f i + f j + f k := by
  rw [Fin.sum_univ_three]
  fin_cases i <;> fin_cases j <;> fin_cases k <;> simp_all <;> ring

theorem offperm (X : Triple) {i j k : Fin 3} (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
    (X i j + X i k) + (X j i + X j k) + (X k i + X k j) =
      X 0 1 + X 0 2 + X 1 0 + X 1 2 + X 2 0 + X 2 1 := by
  fin_cases i <;> fin_cases j <;> fin_cases k <;> simp_all <;> ring

theorem lpNorm_nonneg3 (p : ℝ) (x : Fin 3 → ℝ) : 0 ≤ lpNorm p x :=
  Real.rpow_nonneg (Finset.sum_nonneg fun _ _ ↦ Real.rpow_nonneg (norm_nonneg _) _) _

theorem lpNorm_pow3 {p : ℝ} (hp : 0 < p) (x : Fin 3 → ℝ) :
    lpNorm p x ^ p = ∑ l, |x l| ^ p := by
  unfold lpNorm
  rw [← Real.rpow_mul (Finset.sum_nonneg fun _ _ ↦ Real.rpow_nonneg (norm_nonneg _) _),
    one_div_mul_cancel hp.ne', Real.rpow_one]
  simp [Real.norm_eq_abs]

theorem lpNorm_eq3 (p : ℝ) (x : Fin 3 → ℝ) {i j k : Fin 3} (hij : i ≠ j) (hik : i ≠ k)
    (hjk : j ≠ k) : lpNorm p x = (|x i| ^ p + |x j| ^ p + |x k| ^ p) ^ (1/p) := by
  unfold lpNorm
  rw [sum3 (fun l ↦ ‖x l‖ ^ p) hij hik hjk]
  simp [Real.norm_eq_abs]

theorem coord_le {p : ℝ} (hp : 0 < p) (x : Fin 3 → ℝ) {i j k : Fin 3} (hij : i ≠ j)
    (hik : i ≠ k) (hjk : j ≠ k) : |x i| ≤ lpNorm p x := by
  have h := lpNorm_pow3 hp x
  rw [sum3 _ hij hik hjk] at h
  have : |x i| ^ p ≤ lpNorm p x ^ p := by
    rw [h]; have := Real.rpow_nonneg (abs_nonneg (x j)) p
    have := Real.rpow_nonneg (abs_nonneg (x k)) p; linarith
  exact (Real.rpow_le_rpow_iff (abs_nonneg _) (lpNorm_nonneg3 p x) hp).1 this

theorem two_coord_le {p : ℝ} (hp : 1 ≤ p) (x : Fin 3 → ℝ) {i j k : Fin 3} (hij : i ≠ j)
    (hik : i ≠ k) (hjk : j ≠ k) : |x j| + |x k| ≤ cp p * lpNorm p x := by
  have hp0 : 0 < p := by linarith
  have h := lpNorm_pow3 hp0 x
  rw [sum3 _ hij hik hjk] at h
  apply sum_le_cp_mul hp (abs_nonneg _) (abs_nonneg _) (lpNorm_nonneg3 p x)
  rw [h]; have := Real.rpow_nonneg (abs_nonneg (x i)) p; linarith


end HlawkaSchatten.DiagonalRealBundle

set_option autoImplicit false

namespace HlawkaSchatten.DiagonalRealBundle
open HlawkaSchatten HlawkaSchatten.DiagonalConstruction

def coordinateBox (ell u v w : ℝ) (X : Triple) : Prop :=
  ∀ j i, if j = i then -u ≤ X j i ∧ X j i ≤ -ell
    else v ≤ X j i ∧ X j i ≤ w

theorem facts_of {p α β tlo thib D δ h A g eps ell u v w : ℝ} {X : Triple}
    (hα : 0 < α) (hαp : α ≤ p) (hpβ : p ≤ β) (hp1 : 1 ≤ p)
    (hell : 0 < ell) (hv : 0 < v) (hA : 0 < A)
    (htlo0 : 0 < tlo) (htlo : tlo ≤ (1/2 : ℝ) ^ (1/α))
    (hthib : (1/2 : ℝ) ^ (1/β) ≤ thib)
    (hD : g + 3 * eps - 6 + 6 * thib ≤ D) (hD0 : 0 ≤ D)
    (hδ : D / (2 * tlo) ≤ δ) (hh : g + 3 * eps ≤ h)
    (hB : coordinateBox ell u v w X)
    (hS : lpNorm p (X 0) + lpNorm p (X 1) + lpNorm p (X 2) = 3)
    (hT : lpNorm p (X 0 + X 1 + X 2) < A)
    (hG : pairGapSum (lpNorm p) (X 0) (X 1) (X 2) < g)
    (htail : ∀ i j k : Fin 3, i ≠ j → i ≠ k → j ≠ k →
      lpNorm p (X j + X k) ≤ (X j i + X k i) + eps) :
    Facts p (cp p) D δ h A (2 * thib) tlo X (fun i ↦ lpNorm p (X i)) := by
  have hp : 1 ≤ p := hp1
  have hp0 : 0 < p := by linarith
  have hdiag : ∀ i, -(u : ℝ) ≤ X i i ∧ X i i ≤ -(ell : ℝ) := fun i ↦ by
    simpa using hB i i
  have hoff : ∀ i j, i ≠ j → (v : ℝ) ≤ X i j ∧ X i j ≤ w := fun i j h ↦ by
    have := hB i j; rwa [if_neg h] at this
  have hrowfull : ∀ i j k, i ≠ j → i ≠ k → j ≠ k →
      (-X i i) ^ p + X i j ^ p + X i k ^ p = lpNorm p (X i) ^ p := by
    intro i j k hij hik hjk
    rw [lpNorm_pow3 hp0, sum3 _ hij hik hjk, abs_of_neg (by linarith [(hdiag i).2]),
      abs_of_pos (by linarith [(hoff i j hij).1]), abs_of_pos (by linarith [(hoff i k hik).1])]
  have hdn : ∀ i, 0 ≤ -X i i := fun i ↦ by linarith [(hdiag i).2]
  have hrow : ∀ i j k, i ≠ j → i ≠ k → j ≠ k →
      (-X i i) ^ p + ((X i j + X i k) / cp p) ^ p ≤ lpNorm p (X i) ^ p := by
    intro i j k hij hik hjk
    have := sum_div_cp_rpow_le hp (u := X i j) (v := X i k) (by linarith [(hoff i j hij).1])
      (by linarith [(hoff i k hik).1])
    have := hrowfull i j k hij hik hjk
    linarith
  have hwle : ∀ i j k, i ≠ j → i ≠ k → j ≠ k → X i j + X i k ≤ cp p * lpNorm p (X i) := by
    intro i j k hij hik hjk
    apply sum_le_cp_mul hp (by linarith [(hoff i j hij).1]) (by linarith [(hoff i k hik).1])
      (lpNorm_nonneg3 p _)
    have := hrowfull i j k hij hik hjk
    have := Real.rpow_nonneg (hdn i) p
    linarith
  have hoffsum0 : 6 - g - 3 * eps <
      X 0 1 + X 0 2 + X 1 0 + X 1 2 + X 2 0 + X 2 1 := by
    unfold pairGapSum pairGap at hG
    have t01 := htail 2 0 1 (by decide) (by decide) (by decide)
    have t02 := htail 1 0 2 (by decide) (by decide) (by decide)
    have t12 := htail 0 1 2 (by decide) (by decide) (by decide)
    linarith
  have hct : 2 * tlo ≤ cp p := by
    unfold cp
    have : (1/2 : ℝ) ^ (1/α) ≤ (1/2 : ℝ) ^ (1/p) :=
      Real.rpow_le_rpow_of_exponent_ge (by norm_num) (by norm_num)
        (one_div_le_one_div_of_le hα hαp)
    linarith
  have hcm : cp p ≤ 2 * thib := by
    unfold cp
    have : (1/2 : ℝ) ^ (1/p) ≤ (1/2 : ℝ) ^ (1/β) :=
      Real.rpow_le_rpow_of_exponent_ge (by norm_num) (by norm_num)
        (one_div_le_one_div_of_le hp0 hpβ)
    linarith
  have hnsum : ∀ i j k, i ≠ j → i ≠ k → j ≠ k →
      lpNorm p (X i) + lpNorm p (X j) + lpNorm p (X k) = 3 := by
    intro i j k hij hik hjk
    have := sum3 (fun l ↦ lpNorm p (X l)) hij hik hjk
    rw [Fin.sum_univ_three] at this
    linarith
  have hoffperm : ∀ i j k, i ≠ j → i ≠ k → j ≠ k →
      (X i j + X i k) + (X j i + X j k) + (X k i + X k j) =
        X 0 1 + X 0 2 + X 1 0 + X 1 2 + X 2 0 + X 2 1 := by
    intro i j k hij hik hjk
    exact offperm X hij hik hjk
  have key : cp p * 3 - (X 0 1 + X 0 2 + X 1 0 + X 1 2 + X 2 0 + X 2 1) < D := by
    linarith only [hoffsum0, hcm, hD]
  have hcN : ∀ i j k, i ≠ j → i ≠ k → j ≠ k →
      cp p * lpNorm p (X i) + cp p * lpNorm p (X j) + cp p * lpNorm p (X k) = cp p * 3 := by
    intro i j k hij hik hjk
    rw [← hnsum i j k hij hik hjk]; ring
  have hcpos := cp_pos p
  set vtotal : Fin 3 → ℝ := X 0 + X 1 + X 2 with hvtotal
  have hvc : ∀ i j k, i ≠ j → i ≠ k → j ≠ k → vtotal i = X i i + X j i + X k i := by
    intro i j k hij hik hjk
    have := sum3 (fun l ↦ X l i) hij hik hjk
    rw [Fin.sum_univ_three] at this
    simp only [hvtotal, Pi.add_apply]
    linarith
  refine ⟨fun i ↦ lpNorm_nonneg3 p (X i), hp, hcpos, hcm, hct, ?_, by linarith, hdn, fun i j h ↦ hv.le.trans (hoff i j h).1, hnsum,
    hrowfull, hrow, ?_, ?_, ?_, ?_, ?_⟩
  · calc D / cp p ≤ D / (2 * tlo) := div_le_div_of_nonneg_left hD0 (by positivity) hct
      _ ≤ δ := hδ
  · intro i j k hij hik hjk
    have := hwle j i k (Ne.symm hij) hjk hik
    have := hwle k i j (Ne.symm hik) (Ne.symm hjk) hij
    have := hcN i j k hij hik hjk
    have := hoffperm i j k hij hik hjk
    linarith
  · intro i j k hij hik hjk
    have := hwle i j k hij hik hjk
    have := hcN i j k hij hik hjk
    have := hoffperm i j k hij hik hjk
    rw [mul_add]
    linarith
  · intro i j k hij hik hjk
    have := hoffperm i j k hij hik hjk
    linarith
  · intro i j k hij hik hjk
    have h1 := coord_le hp0 vtotal hij hik hjk
    rw [hvc i j k hij hik hjk] at h1
    linarith [le_abs_self (X i i + X j i + X k i)]
  · intro i j k hij hik hjk
    have h1 := two_coord_le hp vtotal hij hik hjk
    rw [hvc j i k (Ne.symm hij) hjk hik, hvc k i j (Ne.symm hik) (Ne.symm hjk) hij] at h1
    have h2 : cp p * lpNorm p vtotal < cp p * (A) := mul_lt_mul_of_pos_left hT hcpos
    have h3 : cp p * (A) ≤ 2 * thib * (A) :=
      mul_le_mul_of_nonneg_right hcm (by linarith)
    have := le_abs_self (X j j + X i j + X k j)
    have := le_abs_self (X k k + X i k + X j k)
    linarith


end HlawkaSchatten.DiagonalRealBundle



set_option autoImplicit false
namespace HlawkaSchatten.DiagonalRealBundle

theorem coordinateBox_weaken {ell u v w ell' u' v' w' : ℝ} {X : Triple}
    (hB : coordinateBox ell' u' v' w' X)
    (hell : ell ≤ ell') (hu : u' ≤ u) (hv : v ≤ v') (hw : w' ≤ w) :
    coordinateBox ell u v w X := by
  intro j i
  have hh := hB j i
  by_cases hji : j = i
  · rw [if_pos hji] at hh ⊢
    constructor <;> linarith
  · rw [if_neg hji] at hh ⊢
    constructor <;> linarith

end HlawkaSchatten.DiagonalRealBundle

open HlawkaSchatten.DiagonalConstruction
namespace HlawkaSchatten.DiagonalRealBundle
def offsum (X : Triple) : ℝ :=
  X 0 1 + X 0 2 + X 1 0 + X 1 2 + X 2 0 + X 2 1

def normCappedDomain (p ell u v w U A J W0 : ℝ) : Set Triple :=
  {X | coordinateBox ell u v w X ∧
    (∀ i, lpNorm p (X i) ≤ U) ∧ lpNorm p (X 0 + X 1 + X 2) ≤ A ∧
    (∀ i j k : Fin 3, i ≠ j → i ≠ k → j ≠ k → J ≤ X j i + X k i) ∧
    W0 ≤ offsum X}

noncomputable def shapeFactor (m s t : ℝ) : ℝ := (s^2+t^2)/(m^2*(s+t)^2)

noncomputable def pairTotalFactor (m M s t eps1 eps2 : ℝ) : ℝ :=
  4*M^2*(1+eps2)*shapeFactor m s t*(1+eps1)

noncomputable def pairColumnFactor (m M s t eta L eps1 eps2 : ℝ) : ℝ :=
  12*M^2*(1+eps2)*shapeFactor m s t*(1+1/eps1) + (7/4+2*(eta/L))^2*(1+1/eps2)


end HlawkaSchatten.DiagonalRealBundle



set_option autoImplicit false
set_option maxHeartbeats 4000000

open HlawkaSchatten.DiagonalRealBundle

namespace HlawkaSchatten.DiagonalCutoff16

/-- Minkowski combines the three two-coordinate row budgets. -/
theorem aggregate_rows {p γ : ℝ} (hp : 1 ≤ p) (hγ : 0 < γ)
    (a w N : Fin 3 → ℝ)
    (ha : ∀ i, 0 ≤ a i) (hw : ∀ i, 0 ≤ w i) (hN : ∀ i, 0 ≤ N i)
    (hrow : ∀ i, a i ^ p + (w i / γ) ^ p ≤ N i ^ p)
    (hS : ∑ i, N i = 3) :
    (∑ i, a i) ^ p + ((∑ i, w i) / γ) ^ p ≤ (3 : ℝ) ^ p := by
  have h01 := mink2 hp (ha 0) (div_nonneg (hw 0) hγ.le)
    (ha 1) (div_nonneg (hw 1) hγ.le) (hN 0) (hN 1) (hrow 0) (hrow 1)
  have h012 := mink2 hp (add_nonneg (ha 0) (ha 1))
    (add_nonneg (div_nonneg (hw 0) hγ.le) (div_nonneg (hw 1) hγ.le))
    (ha 2) (div_nonneg (hw 2) hγ.le) (add_nonneg (hN 0) (hN 1)) (hN 2)
    h01 (hrow 2)
  simp only [Fin.sum_univ_three] at hS ⊢
  rw [← hS]
  simpa only [add_div] using h012

/-- A scalar certificate bounds the diagonal sum and improves the total norm. -/
theorem aggregate_bootstrap {p β A W γ Γ H T W0 B t' : ℝ}
    (hp : 0 < p) (hpβ : p ≤ β) (hA : 0 ≤ A) (hW : 0 ≤ W)
    (hγ : 0 < γ) (hγΓ : γ ≤ Γ) (hH : 0 < H)
    (hbudget : A ^ p + (W / γ) ^ p ≤ (3 : ℝ) ^ p)
    (hHolder : W - A ≤ H * T) (hW0 : 0 ≤ W0) (hWstrict : W0 < W)
    (hB0 : 0 ≤ B) (hB3 : B ≤ 3) (hWbase : W0 / (3 * Γ) ≤ 1)
    (hcert : 1 ≤ (B / 3) ^ β + (W0 / (3 * Γ)) ^ β)
    (hnext : H * t' ≤ W0 - B) : t' < T := by
  have hΓ : 0 < Γ := hγ.trans_le hγΓ
  have hthree : 0 < (3 : ℝ) ^ p := Real.rpow_pos_of_pos (by norm_num) p
  have hnormalized : (A / 3) ^ p + ((W / γ) / 3) ^ p ≤ 1 := by
    rw [Real.div_rpow hA (by norm_num),
      Real.div_rpow (div_nonneg hW hγ.le) (by norm_num), ← add_div]
    exact (div_le_iff₀ hthree).2 (by simpa using hbudget)
  have hBx0 : 0 ≤ B / 3 := by positivity
  have hBx1 : B / 3 ≤ 1 := by linarith
  have hWx0 : 0 ≤ W0 / (3 * Γ) := by positivity
  have hcertp : 1 ≤ (B / 3) ^ p + (W0 / (3 * Γ)) ^ p :=
    hcert.trans (add_le_add
      (Real.rpow_le_rpow_of_exponent_ge' hBx0 hBx1 hp.le hpβ)
      (Real.rpow_le_rpow_of_exponent_ge' hWx0 hWbase hp.le hpβ))
  have hWcompare : W0 / (3 * Γ) ≤ (W / γ) / 3 := by
    have h1 : W0 / Γ ≤ W / γ := calc
      W0 / Γ ≤ W / Γ := div_le_div_of_nonneg_right hWstrict.le hΓ.le
      _ ≤ W / γ := div_le_div_of_nonneg_left hW hγ hγΓ
    calc W0 / (3 * Γ) = (W0 / Γ) / 3 := by ring
         _ ≤ (W / γ) / 3 := div_le_div_of_nonneg_right h1 (by norm_num)
  have hApow : A ≤ B := by
    by_contra hn
    have hBA : B < A := lt_of_not_ge hn
    have hr := Real.rpow_lt_rpow hBx0 (div_lt_div_of_pos_right hBA (by norm_num)) hp
    have hw := Real.rpow_le_rpow hWx0 hWcompare hp.le
    linarith
  have hmul : H * t' < H * T := by linarith
  nlinarith only [hmul, hH]

/-- The total-norm bootstrap for normalized three-row Hlawka data.

The two-coordinate row budgets come from Holder. The sum-coordinate bound
is the three-coordinate Holder inequality. The strict gap inequality and
pair-tail estimate are precisely the consequences of a normalized strict
Hlawka counterexample used in bootstrap.tex.
-/
theorem total_norm_bootstrap {p α β c γ Γ H T G ε t B t' : ℝ}
    (hp : 1 ≤ p) (hα : 0 < α) (hαp : α ≤ p) (hpβ : p ≤ β)
    (hc : 0 < c) (hγ : 0 < γ) (hγΓ : γ ≤ Γ) (hH : 0 < H)
    (a w N : Fin 3 → ℝ)
    (ha : ∀ i, 0 ≤ a i) (hw : ∀ i, 0 ≤ w i) (hN : ∀ i, 0 ≤ N i)
    (hrow : ∀ i, a i ^ p + (w i / γ) ^ p ≤ N i ^ p)
    (hS : ∑ i, N i = 3)
    (hHolder : (∑ i, w i) - (∑ i, a i) ≤ H * T)
    (hG : 0 ≤ G) (hfailure : (c * p) * G + T < 3)
    (ht : t ≤ T) (htail : 6 - G ≤ (∑ i, w i) + 3 * ε)
    (hW0 : 0 ≤ 6 - (3 - t) / (c * α) - 3 * ε)
    (hWbase : (6 - (3 - t) / (c * α) - 3 * ε) / (3 * Γ) ≤ 1)
    (hB0 : 0 ≤ B) (hB3 : B ≤ 3)
    (hcert : 1 ≤ (B / 3) ^ β +
      ((6 - (3 - t) / (c * α) - 3 * ε) / (3 * Γ)) ^ β)
    (hnext : H * t' ≤ 6 - (3 - t) / (c * α) - 3 * ε - B) : t' < T := by
  have hcmp : (c * α) * G ≤ (c * p) * G :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hαp hc.le) hG
  have hGupper : G < (3 - t) / (c * α) := by
    apply (lt_div_iff₀ (mul_pos hc hα)).2
    nlinarith only [hcmp, hfailure, ht]
  have hWstrict : 6 - (3 - t) / (c * α) - 3 * ε < ∑ i, w i := by
    linarith
  exact aggregate_bootstrap (lt_of_lt_of_le zero_lt_one hp) hpβ
    (Finset.sum_nonneg fun i _ ↦ ha i) (Finset.sum_nonneg fun i _ ↦ hw i)
    hγ hγΓ hH (aggregate_rows hp hγ a w N ha hw hN hrow hS)
    hHolder hW0 hWstrict hB0 hB3 hWbase hcert hnext

end HlawkaSchatten.DiagonalCutoff16



set_option autoImplicit false
set_option maxHeartbeats 4000000

namespace HlawkaSchatten.DiagonalCutoff16

theorem rpow_tangent_lower {p x y : ℝ} (hp : 1 ≤ p) (hx : 0 < x) (hy : 0 ≤ y) :
    x ^ p + p * x ^ (p - 1) * (y - x) ≤ y ^ p := by
  have hb := one_add_mul_self_le_rpow_one_add
    (show -1 ≤ (y - x) / x by apply (le_div_iff₀ hx).2; linarith) hp
  have he : 1 + (y - x) / x = y / x := by field_simp; ring
  rw [he, Real.div_rpow hy hx.le] at hb
  have hm := (le_div_iff₀ (Real.rpow_pos_of_pos hx p)).1 hb
  have hpowers : x ^ p = x ^ (p - 1) * x := by
    conv_lhs => rw [show p = (p - 1) + 1 by ring]
    rw [Real.rpow_add hx, Real.rpow_one]
  have hid : (1 + p * ((y - x) / x)) * x ^ p =
      x ^ p + p * x ^ (p - 1) * (y - x) := by
    rw [hpowers]
    field_simp <;> ring
  rwa [hid] at hm

/-- A pair of power checks controls an entire ray, rather than an iteration. -/
theorem power_barrier {p β x y k l d : ℝ}
    (hp : 1 ≤ p) (hpβ : p ≤ β)
    (hx : 0 < x) (hx1 : x ≤ 1) (hy : 0 < y) (hy1 : y ≤ 1)
    (hk : 0 ≤ k) (hl : 0 ≤ l) (hd : 0 ≤ d) (hyd : 0 ≤ y - l * d)
    (hvalue : 1 < x ^ β + y ^ β) (hslope : l ≤ k * x ^ (β - 1)) :
    1 < (x + k * d) ^ p + (y - l * d) ^ p := by
  have hp0 : 0 ≤ p := by linarith
  have hp1 : 0 ≤ p - 1 := by linarith
  have hv : 1 < x ^ p + y ^ p := hvalue.trans_le (add_le_add
    (Real.rpow_le_rpow_of_exponent_ge' hx.le hx1 hp0 hpβ)
    (Real.rpow_le_rpow_of_exponent_ge' hy.le hy1 hp0 hpβ))
  have hxp : x ^ (β - 1) ≤ x ^ (p - 1) :=
    Real.rpow_le_rpow_of_exponent_ge' hx.le hx1 hp1 (by linarith)
  have hyp : y ^ (p - 1) ≤ 1 := by
    simpa using Real.rpow_le_rpow hy.le hy1 hp1
  have hcoeff : l * y ^ (p - 1) ≤ k * x ^ (p - 1) := calc
    l * y ^ (p - 1) ≤ l := by nlinarith only [mul_le_mul_of_nonneg_left hyp hl]
    _ ≤ k * x ^ (β - 1) := hslope
    _ ≤ k * x ^ (p - 1) := mul_le_mul_of_nonneg_left hxp hk
  have h1 := rpow_tangent_lower hp hx (show 0 ≤ x + k * d by positivity)
  have h2 := rpow_tangent_lower hp hy hyd
  have h3 := mul_nonneg (mul_nonneg hp0 hd) (sub_nonneg.mpr hcoeff)
  nlinarith only [hv, h1, h2, h3]

theorem aggregate_barrier {p β A W γ Γ H T u v t x y k l : ℝ}
    (hp : 1 ≤ p) (hpβ : p ≤ β) (hA : 0 ≤ A) (hW : 0 ≤ W)
    (hγ : 0 < γ) (hγΓ : γ ≤ Γ) (hH : 0 < H)
    (hbudget : A ^ p + (W / γ) ^ p ≤ (3 : ℝ) ^ p)
    (hHolder : W - A ≤ H * T) (hT : 1 ≤ T)
    (hv : 0 ≤ v) (huv : 0 ≤ u + v) (hWlower : u + v * T ≤ W)
    (hxdef : x = (u + (v - H) * t) / 3)
    (hydef : y = (u + v * t) / (3 * Γ))
    (hkdef : k = (H - v) / 3) (hldef : l = v / (3 * Γ))
    (hx : 0 < x) (hx1 : x ≤ 1) (hy : 0 < y) (hy1 : y ≤ 1)
    (hk : 0 ≤ k) (hvalue : 1 < x ^ β + y ^ β)
    (hslope : l ≤ k * x ^ (β - 1)) : t < T := by
  by_contra hn
  have hTt : T ≤ t := le_of_not_gt hn
  have hΓ : 0 < Γ := hγ.trans_le hγΓ
  have hp0 : 0 < p := by linarith
  have hthree : 0 < (3 : ℝ) ^ p := Real.rpow_pos_of_pos (by norm_num) p
  have hnormalized : (A / 3) ^ p + ((W / γ) / 3) ^ p ≤ 1 := by
    rw [Real.div_rpow hA (by norm_num),
      Real.div_rpow (div_nonneg hW hγ.le) (by norm_num), ← add_div]
    exact (div_le_iff₀ hthree).2 (by simpa using hbudget)
  have hld : 0 ≤ l := by rw [hldef]; positivity
  have hyt : y - l * (t - T) = (u + v * T) / (3 * Γ) := by
    rw [hydef, hldef]; ring
  have hxt : x + k * (t - T) = (u + (v - H) * T) / 3 := by
    rw [hxdef, hkdef]; ring
  have hupos : 0 ≤ u + v * T := by nlinarith only [hv, huv, hT]
  have hyd : 0 ≤ y - l * (t - T) := by rw [hyt]; positivity
  have hxmin : x + k * (t - T) ≤ A / 3 := by
    rw [hxt]
    apply div_le_div_of_nonneg_right _ (by norm_num)
    nlinarith only [hWlower, hHolder]
  have hymin : y - l * (t - T) ≤ (W / γ) / 3 := by
    rw [hyt]
    have h1 : (u + v * T) / Γ ≤ W / γ := calc
      (u + v * T) / Γ ≤ W / Γ := div_le_div_of_nonneg_right hWlower hΓ.le
      _ ≤ W / γ := div_le_div_of_nonneg_left hW hγ hγΓ
    calc (u + v * T) / (3 * Γ) = ((u + v * T) / Γ) / 3 := by ring
         _ ≤ (W / γ) / 3 := div_le_div_of_nonneg_right h1 (by norm_num)
  have hb := power_barrier hp hpβ hx hx1 hy hy1 hk hld
    (sub_nonneg.mpr hTt) hyd hvalue hslope
  have hxnonneg : 0 ≤ x + k * (t - T) := by positivity
  have h1 := Real.rpow_le_rpow hxnonneg hxmin hp0.le
  have h2 := Real.rpow_le_rpow hyd hymin hp0.le
  linarith

end HlawkaSchatten.DiagonalCutoff16



set_option autoImplicit false
set_option maxHeartbeats 4000000
open HlawkaSchatten HlawkaSchatten.DiagonalConstruction
open HlawkaSchatten.DiagonalRealBundle

namespace HlawkaSchatten.DiagonalCutoff16

theorem cp_upper_interval {p β B : ℝ} (hp : 0 < p) (hpβ : p ≤ β)
    (hB : (1/2 : ℝ) ^ (1/β) ≤ B) : cp p ≤ 2*B := by
  have he := one_div_le_one_div_of_le hp hpβ
  have h := Real.rpow_le_rpow_of_exponent_ge (by norm_num : (0 : ℝ) < 1/2)
    (by norm_num : (1/2 : ℝ) ≤ 1) he
  unfold cp
  linarith

theorem holder_upper_interval {p β H : ℝ} (hp : 0 < p) (hpβ : p ≤ β)
    (hH : (3 : ℝ) ^ (1 - 1/β) ≤ H) : (3 : ℝ) ^ (1 - 1/p) ≤ H := by
  have he := one_div_le_one_div_of_le hp hpβ
  exact (Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 3)
    (by linarith : 1 - 1/p ≤ 1 - 1/β)).trans hH

theorem sum_le_three_holder {p : ℝ} (hp : 1 ≤ p) (v : Fin 3 → ℝ) :
    (∑ i, v i) ≤ (3 : ℝ) ^ (1 - 1 / p) * lpNorm p v := by
  have hp0 : 0 < p := by linarith
  have hpow := Real.rpow_sum_le_const_mul_sum_rpow Finset.univ v hp
  have he : ((3 : ℝ) ^ (1 - 1 / p) * lpNorm p v) ^ p =
      (3 : ℝ) ^ (p - 1) * ∑ i, |v i| ^ p := by
    rw [Real.mul_rpow (by positivity) (lpNorm_nonneg p v),
      ← Real.rpow_mul (by norm_num), lpNorm_pow3 hp0]
    congr 2
    field_simp
  have hright : 0 ≤ (3 : ℝ) ^ (1 - 1 / p) * lpNorm p v :=
    mul_nonneg (Real.rpow_nonneg (by norm_num) _) (lpNorm_nonneg p v)
  have hleft : 0 ≤ ∑ i, |v i| := Finset.sum_nonneg fun i _ ↦ abs_nonneg _
  have hsum : (∑ i, |v i|) ≤ (3 : ℝ) ^ (1 - 1 / p) * lpNorm p v := by
    apply (Real.rpow_le_rpow_iff hleft hright hp0).mp
    rw [he]
    simpa using hpow
  exact (Finset.sum_le_sum fun i _ ↦ le_abs_self (v i)).trans hsum

theorem oriented_aggregate_budget {p ell u v w : ℝ} (hp : 1 ≤ p)
    (hell : 0 < ell) (hv : 0 < v) (X : Fin 3 → Fin 3 → ℝ)
    (hB : coordinateBox ell u v w X)
    (hS : lpNorm p (X 0) + lpNorm p (X 1) + lpNorm p (X 2) = 3) :
    (-X 0 0 - X 1 1 - X 2 2) ^ p + (offsum X / cp p) ^ p ≤ (3 : ℝ) ^ p := by
  have hp0 : 0 < p := by linarith
  have hd (i : Fin 3) : 0 ≤ -X i i := by
    have hi := hB i i
    simp only [coordinateBox, if_pos rfl] at hi
    linarith [hi.2]
  have ho (i j : Fin 3) (hij : i ≠ j) : 0 ≤ X i j := by
    have hi := hB i j
    rw [if_neg hij] at hi
    linarith [hi.1]
  have row (i j k : Fin 3) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
      (-X i i) ^ p + ((X i j + X i k) / cp p) ^ p ≤ lpNorm p (X i) ^ p := by
    have hf := lpNorm_pow3 hp0 (X i)
    rw [sum3 _ hij hik hjk, abs_of_nonpos (by linarith [hd i]),
      abs_of_nonneg (ho i j hij), abs_of_nonneg (ho i k hik)] at hf
    have ht := sum_div_cp_rpow_le hp (ho i j hij) (ho i k hik)
    linarith
  let a : Fin 3 → ℝ := fun i ↦ -X i i
  let b : Fin 3 → ℝ := ![X 0 1 + X 0 2, X 1 0 + X 1 2, X 2 0 + X 2 1]
  have hb : ∀ i, 0 ≤ b i := by
    intro i
    fin_cases i
    · exact add_nonneg (ho 0 1 (by decide)) (ho 0 2 (by decide))
    · exact add_nonneg (ho 1 0 (by decide)) (ho 1 2 (by decide))
    · exact add_nonneg (ho 2 0 (by decide)) (ho 2 1 (by decide))
  have hr : ∀ i, a i ^ p + (b i / cp p) ^ p ≤ lpNorm p (X i) ^ p := by
    intro i
    fin_cases i
    · exact row 0 1 2 (by decide) (by decide) (by decide)
    · exact row 1 0 2 (by decide) (by decide) (by decide)
    · exact row 2 0 1 (by decide) (by decide) (by decide)
  have h := aggregate_rows hp (cp_pos p) a b (fun i ↦ lpNorm p (X i))
    hd hb (fun i ↦ lpNorm_nonneg p _) hr (by simpa only [Fin.sum_univ_three] using hS)
  simpa [Fin.sum_univ_three, a, b, offsum, sub_eq_add_neg, add_assoc, add_comm, add_left_comm] using h

theorem norm_barrier {p α β c H Γ ell ub vb wb ε t x y k l : ℝ}
    (hp : 1 ≤ p) (hα : 0 < α) (hαp : α ≤ p) (hpβ : p ≤ β)
    (hc : 0 < c) (hH : 0 < H) (hΓ : cp p ≤ Γ)
    (hHolder : (3 : ℝ) ^ (1 - 1 / p) ≤ H)
    (hell : 0 < ell) (hv : 0 < vb) (X : Fin 3 → Fin 3 → ℝ)
    (hB : coordinateBox ell ub vb wb X)
    (hS : lpNorm p (X 0) + lpNorm p (X 1) + lpNorm p (X 2) = 3)
    (hT : 1 ≤ lpNorm p (X 0 + X 1 + X 2))
    (hfailure : (c * p) * pairGapSum (lpNorm p) (X 0) (X 1) (X 2) +
      lpNorm p (X 0 + X 1 + X 2) < 3)
    (htail : ∀ i j k : Fin 3, i ≠ j → i ≠ k → j ≠ k →
      lpNorm p (X j + X k) ≤ X j i + X k i + ε)
    (huv : 0 ≤ 6 - 2 / (c * α) - 3 * ε)
    (hxdef : x = (6 - 3 / (c * α) - 3 * ε + (1 / (c * α) - H) * t) / 3)
    (hydef : y = (6 - 3 / (c * α) - 3 * ε + t / (c * α)) / (3 * Γ))
    (hkdef : k = (H - 1 / (c * α)) / 3)
    (hldef : l = (1 / (c * α)) / (3 * Γ))
    (hx : 0 < x) (hx1 : x ≤ 1) (hy : 0 < y) (hy1 : y ≤ 1) (hk : 0 ≤ k)
    (hvalue : 1 < x ^ β + y ^ β) (hslope : l ≤ k * x ^ (β - 1)) :
    t < lpNorm p (X 0 + X 1 + X 2) := by
  have hA : 0 ≤ -X 0 0 - X 1 1 - X 2 2 := by
    have h0 := hB 0 0; have h1 := hB 1 1; have h2 := hB 2 2
    simp only [if_pos rfl] at h0 h1 h2
    linarith [h0.2, h1.2, h2.2]
  have hW : 0 ≤ offsum X := by
    have ho (i j : Fin 3) (hij : i ≠ j) : 0 ≤ X i j := by
      have hi := hB i j
      rw [if_neg hij] at hi
      linarith [hi.1]
    dsimp [offsum]
    linarith [ho 0 1 (by decide), ho 0 2 (by decide), ho 1 0 (by decide),
      ho 1 2 (by decide), ho 2 0 (by decide), ho 2 1 (by decide)]
  have hHnorm := mul_le_mul_of_nonneg_right hHolder
    (lpNorm_nonneg p (X 0 + X 1 + X 2))
  have hh := sum_le_three_holder hp (X 0 + X 1 + X 2)
  have holder : offsum X - (-X 0 0 - X 1 1 - X 2 2) ≤
      H * lpNorm p (X 0 + X 1 + X 2) := by
    simp only [Fin.sum_univ_three, Pi.add_apply] at hh
    dsimp [offsum]
    linarith
  have hG0 := pairGapSum_nonneg hp (X 0) (X 1) (X 2)
  have hcmp := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hαp hc.le) hG0
  have hG : pairGapSum (lpNorm p) (X 0) (X 1) (X 2) <
      (3 - lpNorm p (X 0 + X 1 + X 2)) / (c * α) := by
    apply (lt_div_iff₀ (mul_pos hc hα)).2
    nlinarith only [hcmp, hfailure]
  have ht0 := htail 0 1 2 (by decide) (by decide) (by decide)
  have ht1 := htail 1 0 2 (by decide) (by decide) (by decide)
  have ht2 := htail 2 0 1 (by decide) (by decide) (by decide)
  have hwlower : 6 - 3 / (c * α) - 3 * ε +
      (1 / (c * α)) * lpNorm p (X 0 + X 1 + X 2) ≤ offsum X := by
    dsimp [pairGapSum, pairGap] at hG
    dsimp [offsum]
    rw [sub_div] at hG
    simp only [div_eq_mul_inv, one_mul] at hG ⊢
    linarith
  exact aggregate_barrier hp hpβ hA hW (cp_pos p) hΓ hH
    (oriented_aggregate_budget hp hell hv X hB hS) holder hT
    (by positivity) (by convert huv using 1 <;> ring) hwlower hxdef
    (by simpa only [one_div_mul_eq_div] using hydef)
    hkdef hldef hx hx1 hy hy1 hk hvalue hslope

end HlawkaSchatten.DiagonalCutoff16


set_option autoImplicit false
set_option maxHeartbeats 4000000
open HlawkaSchatten HlawkaSchatten.DiagonalConstruction
open HlawkaSchatten.DiagonalRealBundle

namespace HlawkaSchatten.DiagonalCutoff16

theorem failure_linear_bound {p c : ℝ} (hp : 1 ≤ p) (X : Fin 3 → Fin 3 → ℝ)
    (hK : c*p ≤ cyclicConstant p)
    (hS : lpNorm p (X 0) + lpNorm p (X 1) + lpNorm p (X 2) = 3)
    (hf : tripleDeficit p (cyclicConstant p) X < 0) :
    (c*p)*pairGapSum (lpNorm p) (X 0) (X 1) (X 2) + lpNorm p (X 0 + X 1 + X 2) < 3 := by
  change hlawkaDeficit p (cyclicConstant p) (X 0) (X 1) (X 2) < 0 at hf
  rw [hlawkaDeficit_eq, tripleGap, hS] at hf
  have h := mul_le_mul_of_nonneg_right hK (pairGapSum_nonneg hp (X 0) (X 1) (X 2))
  linarith

theorem gap_of_total_lower {p α c G T t : ℝ} (hα : 0 < α) (hαp : α ≤ p)
    (hc : 0 < c) (hG : 0 ≤ G) (hf : (c*p)*G+T < 3) (ht : t ≤ T) :
    G < (3-t)/(c*α) := by
  apply (lt_div_iff₀ (mul_pos hc hα)).2
  have h := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hαp hc.le) hG
  nlinarith only [h, hf, ht]

theorem initial_norm_lower {p ell u v w : ℝ} (hp : 1 ≤ p) (X : Fin 3 → Fin 3 → ℝ)
    (hB : coordinateBox ell u v w X) : ∀ i, v ≤ lpNorm p (X i) := by
  intro i
  obtain ⟨j, k, hij, hik, hjk⟩ := others i
  have hx : v ≤ X i j := by
    have h : v ≤ X i j ∧ X i j ≤ w := by simpa [coordinateBox, hij] using hB i j
    exact h.1
  have hc := norm_apply_le_lpNorm hp (X i) j
  rw [Real.norm_eq_abs] at hc
  exact hx.trans ((le_abs_self _).trans hc)

theorem pairGapSum_perm (p : ℝ) (X : Fin 3 → Fin 3 → ℝ) {i j k : Fin 3}
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
    pairGapSum (lpNorm p) (X i) (X j) (X k) =
      pairGapSum (lpNorm p) (X 0) (X 1) (X 2) := by
  have h10 : lpNorm p (X 1 + X 0) = lpNorm p (X 0 + X 1) := by rw [add_comm]
  have h20 : lpNorm p (X 2 + X 0) = lpNorm p (X 0 + X 2) := by rw [add_comm]
  have h21 : lpNorm p (X 2 + X 1) = lpNorm p (X 1 + X 2) := by rw [add_comm]
  fin_cases i <;> fin_cases j <;> fin_cases k <;> simp_all
  all_goals simp only [pairGapSum, pairGap, h10, h20, h21]; ring

theorem pair_floor_of_gap {p g U eps : ℝ} (hp : 1 ≤ p) (X : Fin 3 → Fin 3 → ℝ)
    (hS : lpNorm p (X 0) + lpNorm p (X 1) + lpNorm p (X 2) = 3)
    (hU : ∀ i, lpNorm p (X i) ≤ U)
    (hG : pairGapSum (lpNorm p) (X 0) (X 1) (X 2) < g)
    (htail : ∀ i j k : Fin 3, i ≠ j → i ≠ k → j ≠ k →
      lpNorm p (X j + X k) ≤ X j i + X k i + eps) :
    ∀ i j k : Fin 3, i ≠ j → i ≠ k → j ≠ k →
      3 - U - g - eps ≤ X j i + X k i := by
  intro i j k hij hik hjk
  have hperm := pairGapSum_perm p X hij hik hjk
  have hg := hG
  rw [← hperm] at hg
  have h1 := pairGap_nonneg hp (X i) (X j)
  have h2 := pairGap_nonneg hp (X i) (X k)
  have hsum := sum3 (fun l ↦ lpNorm p (X l)) hij hik hjk
  rw [Fin.sum_univ_three] at hsum
  have ht := htail i j k hij hik hjk
  have hi := hU i
  dsimp only [pairGapSum, pairGap] at hg h1 h2
  linarith

theorem offsum_floor_of_gap {p g eps : ℝ} (X : Fin 3 → Fin 3 → ℝ)
    (hS : lpNorm p (X 0) + lpNorm p (X 1) + lpNorm p (X 2) = 3)
    (hG : pairGapSum (lpNorm p) (X 0) (X 1) (X 2) < g)
    (htail : ∀ i j k : Fin 3, i ≠ j → i ≠ k → j ≠ k →
      lpNorm p (X j + X k) ≤ X j i + X k i + eps) :
    6-g-3*eps ≤ offsum X := by
  have t0 := htail 0 1 2 (by decide) (by decide) (by decide)
  have t1 := htail 1 0 2 (by decide) (by decide) (by decide)
  have t2 := htail 2 0 1 (by decide) (by decide) (by decide)
  dsimp only [pairGapSum, pairGap] at hG
  dsimp only [offsum]
  linarith

end HlawkaSchatten.DiagonalCutoff16

/- Exact certificates for the non-iterative total-norm barrier. -/
open HlawkaSchatten HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle
set_option autoImplicit false
set_option maxHeartbeats 200000000
set_option maxRecDepth 10000
set_option exponentiation.threshold 20000
namespace HlawkaSchatten.DiagonalCutoff16

theorem roots_w001_s002 :
    (478847119/500000000 : ℝ) ≤ (1/2 : ℝ) ^ (256/4105 : ℝ) ∧
    (1/2 : ℝ) ^ (512/8211 : ℝ) ≤ (957699281/1000000000 : ℝ) ∧
    (3 : ℝ) ^ (7699/8211 : ℝ) ≤ (2801368101/1000000000 : ℝ) := by

  have htlo : (478847119/500000000 : ℝ) ≤ (1/2 : ℝ) ^ (256/4105 : ℝ) := by
    have h := le_rpow_of_pow_le (x := (1/2 : ℝ)) (X := (478847119/500000000 : ℝ)) (by norm_num) 256 4105 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num

  have hthi : (1/2 : ℝ) ^ (512/8211 : ℝ) ≤ (957699281/1000000000 : ℝ) := by
    have h := rpow_le_of_pow_le (x := (1/2 : ℝ)) (X := (957699281/1000000000 : ℝ)) (by norm_num) (by norm_num) 512 8211 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num

  have hH : (3 : ℝ) ^ (7699/8211 : ℝ) ≤ (2801368101/1000000000 : ℝ) := by
    have h := rpow_le_of_pow_le (x := (3 : ℝ)) (X := (2801368101/1000000000 : ℝ)) (by norm_num) (by norm_num) 7699 8211 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num

  exact ⟨htlo, hthi, hH⟩


theorem barrier_w001_s002 (p : ℝ) (hpa : (4105/256 : ℝ) ≤ p) (hpb : p ≤ (8211/512 : ℝ))
    (Z : Fin 3 → Fin 3 → ℝ) (hB : coordinateBox (1137/5000 : ℝ) (6297/5000 : ℝ) (1541/2500 : ℝ) (6297/5000 : ℝ) Z)
    (hS : lpNorm p (Z 0) + lpNorm p (Z 1) + lpNorm p (Z 2) = 3)
    (hT : 1 ≤ lpNorm p (Z 0 + Z 1 + Z 2))
    (hfailure : ((42773/100000 : ℝ)*p) * pairGapSum (lpNorm p) (Z 0) (Z 1) (Z 2) + lpNorm p (Z 0 + Z 1 + Z 2) < 3)
    (htail : ∀ i j k : Fin 3, i ≠ j → i ≠ k → j ≠ k →
      lpNorm p (Z j + Z k) ≤ Z j i + Z k i + (1/100000000 : ℝ)) :
    (1197670429/1000000000 : ℝ) < lpNorm p (Z 0 + Z 1 + Z 2) := by
  have hvalue : 1 < (83651501593518927353322743/105349899000000000000000000 : ℝ) ^ (8211/512 : ℝ) + (100735934771490505/100893522525722619 : ℝ) ^ (8211/512 : ℝ) := by
    exact cert_lt (x := (83651501593518927353322743/105349899000000000000000000 : ℝ)) (y := (100735934771490505/100893522525722619 : ℝ)) (X := (154738011/6250000000 : ℝ)) (Y := (487621656589/500000000000 : ℝ)) 8211 512
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (8211/512 : ℝ) (by norm_num) (by norm_num)

  have hs : (2560000000000000000000000/89309878214974765613592173 : ℝ) ≤ (83651501593518927353322743/105349899000000000000000000 : ℝ) ^ (7699/512 : ℝ) := by
    have h := le_rpow_of_pow_le (x := (83651501593518927353322743/105349899000000000000000000 : ℝ)) (X := (2560000000000000000000000/89309878214974765613592173 : ℝ)) (by norm_num) 7699 512 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num

  have hslope : (2560000000000000/100893522525722619 : ℝ) ≤ (93254615500723933/105349899000000000 : ℝ) * (83651501593518927353322743/105349899000000000000000000 : ℝ) ^ ((8211/512 : ℝ)-1) := by
    have h := mul_le_mul_of_nonneg_left hs (show (0 : ℝ) ≤ (93254615500723933/105349899000000000 : ℝ) by norm_num)
    norm_num at h ⊢
    exact h
  have hthi : (1/2 : ℝ) ^ (1/(8211/512 : ℝ)) ≤ (957699281/1000000000 : ℝ) := by
    convert roots_w001_s002.2.1 using 1 <;> norm_num
  have hH : (3 : ℝ) ^ (1-1/(8211/512 : ℝ)) ≤ (2801368101/1000000000 : ℝ) := by
    convert roots_w001_s002.2.2 using 1 <;> norm_num
  apply norm_barrier (α := (4105/256 : ℝ)) (β := (8211/512 : ℝ)) (c := (42773/100000 : ℝ)) (H := (2801368101/1000000000 : ℝ)) (Γ := (957699281/500000000 : ℝ))
    (x := (83651501593518927353322743/105349899000000000000000000 : ℝ)) (y := (100735934771490505/100893522525722619 : ℝ)) (k := (93254615500723933/105349899000000000 : ℝ)) (l := (2560000000000000/100893522525722619 : ℝ))
    (by linarith) (by norm_num) hpa hpb (by norm_num) (by norm_num)
    (by have h := cp_upper_interval (by linarith : 0 < p) hpb hthi; norm_num at h ⊢; exact h)
    (holder_upper_interval (by linarith) hpb hH)
    (by norm_num) (by norm_num) Z hB hS hT hfailure htail
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hvalue hslope


theorem roots_w001_s003 :
    (11971241/12500000 : ℝ) ≤ (1/2 : ℝ) ^ (512/8211 : ℝ) ∧
    (1/2 : ℝ) ^ (128/2053 : ℝ) ≤ (478852161/500000000 : ℝ) ∧
    (3 : ℝ) ^ (1925/2053 : ℝ) ≤ (280139147/100000000 : ℝ) := by

  have htlo : (11971241/12500000 : ℝ) ≤ (1/2 : ℝ) ^ (512/8211 : ℝ) := by
    have h := le_rpow_of_pow_le (x := (1/2 : ℝ)) (X := (11971241/12500000 : ℝ)) (by norm_num) 512 8211 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num

  have hthi : (1/2 : ℝ) ^ (128/2053 : ℝ) ≤ (478852161/500000000 : ℝ) := by
    have h := rpow_le_of_pow_le (x := (1/2 : ℝ)) (X := (478852161/500000000 : ℝ)) (by norm_num) (by norm_num) 128 2053 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num

  have hH : (3 : ℝ) ^ (1925/2053 : ℝ) ≤ (280139147/100000000 : ℝ) := by
    have h := rpow_le_of_pow_le (x := (3 : ℝ)) (X := (280139147/100000000 : ℝ)) (by norm_num) (by norm_num) 1925 2053 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num

  exact ⟨htlo, hthi, hH⟩


theorem barrier_w001_s003 (p : ℝ) (hpa : (8211/512 : ℝ) ≤ p) (hpb : p ≤ (2053/128 : ℝ))
    (Z : Fin 3 → Fin 3 → ℝ) (hB : coordinateBox (1137/5000 : ℝ) (6297/5000 : ℝ) (1541/2500 : ℝ) (6297/5000 : ℝ) Z)
    (hS : lpNorm p (Z 0) + lpNorm p (Z 1) + lpNorm p (Z 2) = 3)
    (hT : 1 ≤ lpNorm p (Z 0 + Z 1 + Z 2))
    (hfailure : ((42773/100000 : ℝ)*p) * pairGapSum (lpNorm p) (Z 0) (Z 1) (Z 2) + lpNorm p (Z 0 + Z 1 + Z 2) < 3)
    (htail : ∀ i j k : Fin 3, i ≠ j → i ≠ k → j ≠ k →
      lpNorm p (Z j + Z k) ≤ Z j i + Z k i + (1/100000000 : ℝ)) :
    (1197486923/1000000000 : ℝ) < lpNorm p (Z 0 + Z 1 + Z 2) := by
  have hvalue : 1 < (4922290983004195083210521/6197807700000000000000000 : ℝ) ^ (2053/128 : ℝ) + (59263704056509615/59356672212148794 : ℝ) ^ (2053/128 : ℝ) := by
    exact cert_lt (x := (4922290983004195083210521/6197807700000000000000000 : ℝ)) (y := (59263704056509615/59356672212148794 : ℝ)) (X := (12414463911/500000000000 : ℝ)) (Y := (975172322059/1000000000000 : ℝ)) 2053 128
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (2053/128 : ℝ) (by norm_num) (by norm_num)

  have hs : (1280000000000000000000000/44661304915444904200009701 : ℝ) ≤ (4922290983004195083210521/6197807700000000000000000 : ℝ) ^ (1925/128 : ℝ) := by
    have h := le_rpow_of_pow_le (x := (4922290983004195083210521/6197807700000000000000000 : ℝ)) (X := (1280000000000000000000000/44661304915444904200009701 : ℝ)) (by norm_num) 1925 128 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num

  have hslope : (12800000000000000/504531713803264749 : ℝ) ≤ (93267418533055141/105362730900000000 : ℝ) * (4922290983004195083210521/6197807700000000000000000 : ℝ) ^ ((2053/128 : ℝ)-1) := by
    have h := mul_le_mul_of_nonneg_left hs (show (0 : ℝ) ≤ (93267418533055141/105362730900000000 : ℝ) by norm_num)
    norm_num at h ⊢
    exact h
  have hthi : (1/2 : ℝ) ^ (1/(2053/128 : ℝ)) ≤ (478852161/500000000 : ℝ) := by
    convert roots_w001_s003.2.1 using 1 <;> norm_num
  have hH : (3 : ℝ) ^ (1-1/(2053/128 : ℝ)) ≤ (280139147/100000000 : ℝ) := by
    convert roots_w001_s003.2.2 using 1 <;> norm_num
  apply norm_barrier (α := (8211/512 : ℝ)) (β := (2053/128 : ℝ)) (c := (42773/100000 : ℝ)) (H := (280139147/100000000 : ℝ)) (Γ := (478852161/250000000 : ℝ))
    (x := (4922290983004195083210521/6197807700000000000000000 : ℝ)) (y := (59263704056509615/59356672212148794 : ℝ)) (k := (93267418533055141/105362730900000000 : ℝ)) (l := (12800000000000000/504531713803264749 : ℝ))
    (by linarith) (by norm_num) hpa hpb (by norm_num) (by norm_num)
    (by have h := cp_upper_interval (by linarith : 0 < p) hpb hthi; norm_num at h ⊢; exact h)
    (holder_upper_interval (by linarith) hpb hH)
    (by norm_num) (by norm_num) Z hB hS hT hfailure htail
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hvalue hslope


end HlawkaSchatten.DiagonalCutoff16

/- Generated finite power inequalities; all witnesses are checked by Lean.
Contraction proof structure adapted from Yuxuan Xu's accepted cutoff-21
submission 3735254f-536b-45fe-a0c1-2ea9ffc9d938, Apache-2.0. -/
set_option autoImplicit false
set_option maxHeartbeats 200000000
set_option maxRecDepth 10000
set_option exponentiation.threshold 20000
namespace HlawkaSchatten.DiagonalRealBundle
theorem contract_w001_s002 (p : ℝ) (hpa : (4105/256 : ℝ) ≤ p) (hpb : p ≤ (8211/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (N : Fin 3 → ℝ)
    (F : Facts p (cp p) (78793877116057/8779158250000000 : ℝ) (4685789/1000000000 : ℝ) (922792845701899/3511663300000000 : ℝ) (62967/50000 : ℝ) (957699281/500000000 : ℝ) (478847119/500000000 : ℝ) X N)
    (hn0 : ∀ i, (1541/2500 : ℝ) ≤ N i) :
    (∀ i, N i ≤ (1149243281/1000000000 : ℝ)) ∧ coordinateBox (1137/2500 : ℝ) (9677/10000 : ℝ) (7889/10000 : ℝ) (703/625 : ℝ) X := by
  have hp0 : 0 ≤ p := by linarith
  have hD0 : (0 : ℝ) ≤ (78793877116057/8779158250000000 : ℝ) := by norm_num
  have hd0 : (0 : ℝ) ≤ (4685789/1000000000 : ℝ) := by norm_num
  have pc0 : 1 < (459712519/500000000 : ℝ) ^ p + (196280583/200000000 : ℝ) ^ p := by
    exact cert_lt (x := (459712519/500000000 : ℝ)) (y := (196280583/200000000 : ℝ)) (X := (12998024169029/50000000000000 : ℝ)) (Y := (14800791930433/20000000000000 : ℝ)) 8211 512
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc1 : 1 < (196280583/200000000 : ℝ) ^ p + (459712519/500000000 : ℝ) ^ p := by simpa only [add_comm] using pc0
  have R0 := ratio_round F hn0 (by norm_num) hD0
    (s := (1900827953/1000000000 : ℝ)) (τ := (459712519/500000000 : ℝ)) (σ := (196280583/200000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc0) (by norm_num; exact pc1)
  have pc2 : 1 < (723486213/843406147 : ℝ) ^ p + (838720358/843406147 : ℝ) ^ p := by
    exact cert_lt (x := (723486213/843406147 : ℝ)) (y := (838720358/843406147 : ℝ)) (X := (8547207245173/100000000000000 : ℝ)) (Y := (91452793078033/100000000000000 : ℝ)) 8211 512
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L0 := lower_round F hn0 (by norm_num) hd0
    (τ := (459712519/500000000 : ℝ)) (n' := (843406147/1000000000 : ℝ)) (Ab := (723486213/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R0 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc2.le) (by norm_num)
  have pc3 : 1 < (115749967/125000000 : ℝ) ^ p + (24468681/25000000 : ℝ) ^ p := by
    exact cert_lt (x := (115749967/125000000 : ℝ)) (y := (24468681/25000000 : ℝ)) (X := (29143033521313/100000000000000 : ℝ)) (Y := (4428560820207/6250000000000 : ℝ)) 8211 512
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc4 : 1 < (24468681/25000000 : ℝ) ^ p + (115749967/125000000 : ℝ) ^ p := by simpa only [add_comm] using pc3
  have R1 := ratio_round F L0 (by norm_num) hD0
    (s := (59523343/31250000 : ℝ)) (τ := (115749967/125000000 : ℝ)) (σ := (24468681/25000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc3) (by norm_num; exact pc4)
  have pc5 : 1 < (730085785/851591227 : ℝ) ^ p + (846905438/851591227 : ℝ) ^ p := by
    exact cert_lt (x := (730085785/851591227 : ℝ)) (y := (846905438/851591227 : ℝ)) (X := (1058552504251/12500000000000 : ℝ)) (Y := (22882895071271/25000000000000 : ℝ)) 8211 512
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L1 := lower_round F L0 (by norm_num) hd0
    (τ := (115749967/125000000 : ℝ)) (n' := (851591227/1000000000 : ℝ)) (Ab := (146017157/200000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R1 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc5.le) (by norm_num)
  have pc6 : 1 < (185236193/200000000 : ℝ) ^ p + (244667073/250000000 : ℝ) ^ p := by
    exact cert_lt (x := (185236193/200000000 : ℝ)) (y := (244667073/250000000 : ℝ)) (X := (14617319014413/50000000000000 : ℝ)) (Y := (70765368813903/100000000000000 : ℝ)) 8211 512
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc7 : 1 < (244667073/250000000 : ℝ) ^ p + (185236193/200000000 : ℝ) ^ p := by simpa only [add_comm] using pc6
  have R2 := ratio_round F L1 (by norm_num) hD0
    (s := (1904849257/1000000000 : ℝ)) (τ := (185236193/200000000 : ℝ)) (σ := (244667073/250000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc6) (by norm_num; exact pc7)
  have pc8 : 1 < (121711160/141969333 : ℝ) ^ p + (847130209/851815998 : ℝ) ^ p := by
    exact cert_lt (x := (121711160/141969333 : ℝ)) (y := (847130209/851815998 : ℝ)) (X := (8466276893089/100000000000000 : ℝ)) (Y := (91533723393349/100000000000000 : ℝ)) 8211 512
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L2 := lower_round F L1 (by norm_num) hd0
    (τ := (185236193/200000000 : ℝ)) (n' := (425907999/500000000 : ℝ)) (Ab := (9128337/12500000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R2 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc8.le) (by norm_num)
  have pc9 : 1 < (926185901/1000000000 : ℝ) ^ p + (978666137/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (926185901/1000000000 : ℝ)) (y := (978666137/1000000000 : ℝ)) (X := (29237136765633/100000000000000 : ℝ)) (Y := (70762869899201/100000000000000 : ℝ)) 8211 512
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc10 : 1 < (978666137/1000000000 : ℝ) ^ p + (926185901/1000000000 : ℝ) ^ p := by simpa only [add_comm] using pc9
  have R3 := ratio_round F L2 (by norm_num) hD0
    (s := (952426019/500000000 : ℝ)) (τ := (926185901/1000000000 : ℝ)) (σ := (978666137/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc9) (by norm_num; exact pc10)
  have pc11 : 1 < (730271894/851822119 : ℝ) ^ p + (847136330/851822119 : ℝ) ^ p := by
    exact cert_lt (x := (730271894/851822119 : ℝ)) (y := (847136330/851822119 : ℝ)) (X := (1693243718663/20000000000000 : ℝ)) (Y := (11441722717457/12500000000000 : ℝ)) 8211 512
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L3 := lower_round F L2 (by norm_num) hd0
    (τ := (926185901/1000000000 : ℝ)) (n' := (851822119/1000000000 : ℝ)) (Ab := (365135947/500000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R3 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc11.le) (by norm_num)
  have pc12 : 1 < (231546509/250000000 : ℝ) ^ p + (489333039/500000000 : ℝ) ^ p := by
    exact cert_lt (x := (231546509/250000000 : ℝ)) (y := (489333039/500000000 : ℝ)) (X := (292372051091/1000000000000 : ℝ)) (Y := (35381400742301/50000000000000 : ℝ)) 8211 512
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc13 : 1 < (489333039/500000000 : ℝ) ^ p + (231546509/250000000 : ℝ) ^ p := by simpa only [add_comm] using pc12
  have R4 := ratio_round F L3 (by norm_num) hD0
    (s := (952426057/500000000 : ℝ)) (τ := (231546509/250000000 : ℝ)) (σ := (489333039/500000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc12) (by norm_num; exact pc13)
  have pc14 : 1 < (365136014/425911143 : ℝ) ^ p + (847136497/851822286 : ℝ) ^ p := by
    exact cert_lt (x := (365136014/425911143 : ℝ)) (y := (847136497/851822286 : ℝ)) (X := (8466216888403/100000000000000 : ℝ)) (Y := (18306756666303/20000000000000 : ℝ)) 8211 512
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L4 := lower_round F L3 (by norm_num) hd0
    (τ := (231546509/250000000 : ℝ)) (n' := (425911143/500000000 : ℝ)) (Ab := (182568007/250000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R4 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc14.le) (by norm_num)
  have pc15 : 1 < (926186039/1000000000 : ℝ) ^ p + (978666077/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (926186039/1000000000 : ℝ)) (y := (978666077/1000000000 : ℝ)) (X := (14618603313923/50000000000000 : ℝ)) (Y := (70762800325033/100000000000000 : ℝ)) 8211 512
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc16 : 1 < (978666077/1000000000 : ℝ) ^ p + (926186039/1000000000 : ℝ) ^ p := by simpa only [add_comm] using pc15
  have R5 := ratio_round F L4 (by norm_num) hD0
    (s := (476213029/250000000 : ℝ)) (τ := (926186039/1000000000 : ℝ)) (σ := (978666077/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have pc17 : 1 < (365136016/425911145 : ℝ) ^ p + (847136501/851822290 : ℝ) ^ p := by
    exact cert_lt (x := (365136016/425911145 : ℝ)) (y := (847136501/851822290 : ℝ)) (X := (8466216994523/100000000000000 : ℝ)) (Y := (91533783369643/100000000000000 : ℝ)) 8211 512
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L5 := lower_round F L4 (by norm_num) hd0
    (τ := (926186039/1000000000 : ℝ)) (n' := (85182229/100000000 : ℝ)) (Ab := (22821001/31250000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R5 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have Rf := ratio_round F L5 (by norm_num) hD0
    (s := (476213029/250000000 : ℝ)) (τ := (926186039/1000000000 : ℝ)) (σ := (978666077/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have pc18 : 1 < (216258509/264393817 : ℝ) ^ p + (1846070930/1850756719 : ℝ) ^ p := by
    exact cert_lt (x := (216258509/264393817 : ℝ)) (y := (1846070930/1850756719 : ℝ)) (X := (3983930191087/100000000000000 : ℝ)) (Y := (96016069854159/100000000000000 : ℝ)) 8211 512
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc19 : 1 < (967664477/1149243281 : ℝ) ^ p + (1144557492/1149243281 : ℝ) ^ p := by
    exact cert_lt (x := (967664477/1149243281 : ℝ)) (y := (1144557492/1149243281 : ℝ)) (X := (6342107601541/100000000000000 : ℝ)) (Y := (936578925157/1000000000000 : ℝ)) 8211 512
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have V := upper_round F L5 (by norm_num) hd0
    (σ := (978666077/1000000000 : ℝ)) (U := (1149243281/1000000000 : ℝ)) (Ab := (1513809563/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (Rf i j k a b c).2) (by norm_num) (by norm_num)
    (by norm_num; exact pc18.le) (by norm_num)
  refine ⟨V, ?_⟩
  exact final_round F L5 V (by norm_num) hd0
    (τ := (926186039/1000000000 : ℝ)) (σ := (978666077/1000000000 : ℝ)) (Ab := (967664477/1000000000 : ℝ))
    (by norm_num) (by norm_num) Rf (by norm_num) (by norm_num)
    (by norm_num; exact pc19.le) (by norm_num) (by norm_num) (by norm_num) (by norm_num)


theorem contract_w001_s003 (p : ℝ) (hpa : (8211/512 : ℝ) ≤ p) (hpb : p ≤ (2053/128 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (N : Fin 3 → ℝ)
    (F : Facts p (cp p) (92968155639179/10329679500000000 : ℝ) (2349407/500000000 : ℝ) (542874588698077/2065935900000000 : ℝ) (62967/50000 : ℝ) (478852161/250000000 : ℝ) (11971241/12500000 : ℝ) X N)
    (hn0 : ∀ i, (1541/2500 : ℝ) ≤ N i) :
    (∀ i, N i ≤ (287362877/250000000 : ℝ)) ∧ coordinateBox (909/2000 : ℝ) (9681/10000 : ℝ) (7887/10000 : ℝ) (9/8 : ℝ) X := by
  have hp0 : 0 ≤ p := by linarith
  have hD0 : (0 : ℝ) ≤ (92968155639179/10329679500000000 : ℝ) := by norm_num
  have hd0 : (0 : ℝ) ≤ (2349407/500000000 : ℝ) := by norm_num
  have pc0 : 1 < (114920887/125000000 : ℝ) ^ p + (122678799/125000000 : ℝ) ^ p := by
    exact cert_lt (x := (114920887/125000000 : ℝ)) (y := (122678799/125000000 : ℝ)) (X := (12982761934857/50000000000000 : ℝ)) (Y := (14806896824833/20000000000000 : ℝ)) 2053 128
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc1 : 1 < (122678799/125000000 : ℝ) ^ p + (114920887/125000000 : ℝ) ^ p := by simpa only [add_comm] using pc0
  have R0 := ratio_round F hn0 (by norm_num) hD0
    (s := (118799843/62500000 : ℝ)) (τ := (114920887/125000000 : ℝ)) (σ := (122678799/125000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc0) (by norm_num; exact pc1)
  have pc2 : 1 < (120583624/140542223 : ℝ) ^ p + (419277262/421626669 : ℝ) ^ p := by
    exact cert_lt (x := (120583624/140542223 : ℝ)) (y := (419277262/421626669 : ℝ)) (X := (1071558406231/12500000000000 : ℝ)) (Y := (91427532986051/100000000000000 : ℝ)) 2053 128
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L0 := lower_round F hn0 (by norm_num) hd0
    (τ := (114920887/125000000 : ℝ)) (n' := (421626669/500000000 : ℝ)) (Ab := (45218859/62500000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R0 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc2.le) (by norm_num)
  have pc3 : 1 < (925950561/1000000000 : ℝ) ^ p + (97877493/100000000 : ℝ) ^ p := by
    exact cert_lt (x := (925950561/1000000000 : ℝ)) (y := (97877493/100000000 : ℝ)) (X := (2911384880247/10000000000000 : ℝ)) (Y := (35443079096473/50000000000000 : ℝ)) 2053 128
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc4 : 1 < (97877493/100000000 : ℝ) ^ p + (925950561/1000000000 : ℝ) ^ p := by simpa only [add_comm] using pc3
  have R1 := ratio_round F L0 (by norm_num) hD0
    (s := (1904725491/1000000000 : ℝ)) (τ := (925950561/1000000000 : ℝ)) (σ := (97877493/100000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc3) (by norm_num; exact pc4)
  have pc5 : 1 < (243370514/283816437 : ℝ) ^ p + (846750497/851449311 : ℝ) ^ p := by
    exact cert_lt (x := (243370514/283816437 : ℝ)) (y := (846750497/851449311 : ℝ)) (X := (8493339101663/100000000000000 : ℝ)) (Y := (4575333054911/5000000000000 : ℝ)) 2053 128
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L1 := lower_round F L0 (by norm_num) hd0
    (τ := (925950561/1000000000 : ℝ)) (n' := (851449311/1000000000 : ℝ)) (Ab := (365055771/500000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R1 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc5.le) (by norm_num)
  have pc6 : 1 < (463066207/500000000 : ℝ) ^ p + (195739163/200000000 : ℝ) ^ p := by
    exact cert_lt (x := (463066207/500000000 : ℝ)) (y := (195739163/200000000 : ℝ)) (X := (2920569321853/10000000000000 : ℝ)) (Y := (35397156919187/50000000000000 : ℝ)) 2053 128
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc7 : 1 < (195739163/200000000 : ℝ) ^ p + (463066207/500000000 : ℝ) ^ p := by simpa only [add_comm] using pc6
  have R2 := ratio_round F L1 (by norm_num) hD0
    (s := (1904828229/1000000000 : ℝ)) (τ := (463066207/500000000 : ℝ)) (σ := (195739163/200000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc6) (by norm_num; exact pc7)
  have pc8 : 1 < (146058676/170334971 : ℝ) ^ p + (846976041/851674855 : ℝ) ^ p := by
    exact cert_lt (x := (146058676/170334971 : ℝ)) (y := (846976041/851674855 : ℝ)) (X := (8491182242263/100000000000000 : ℝ)) (Y := (178728160121/195312500000 : ℝ)) 2053 128
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L2 := lower_round F L1 (by norm_num) hd0
    (τ := (463066207/500000000 : ℝ)) (n' := (170334971/200000000 : ℝ)) (Ab := (36514669/50000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R2 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc8.le) (by norm_num)
  have pc9 : 1 < (926137377/1000000000 : ℝ) ^ p + (978693651/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (926137377/1000000000 : ℝ)) (y := (978693651/1000000000 : ℝ)) (X := (29208203573811/100000000000000 : ℝ)) (Y := (8848975403253/12500000000000 : ℝ)) 2053 128
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc10 : 1 < (978693651/1000000000 : ℝ) ^ p + (926137377/1000000000 : ℝ) ^ p := by simpa only [add_comm] using pc9
  have R3 := ratio_round F L2 (by norm_num) hD0
    (s := (476207757/250000000 : ℝ)) (τ := (926137377/1000000000 : ℝ)) (σ := (978693651/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc9) (by norm_num; exact pc10)
  have pc11 : 1 < (243432781/283893670 : ℝ) ^ p + (423491098/425840505 : ℝ) ^ p := by
    exact cert_lt (x := (243432781/283893670 : ℝ)) (y := (423491098/425840505 : ℝ)) (X := (4245561769813/50000000000000 : ℝ)) (Y := (91508876827049/100000000000000 : ℝ)) 2053 128
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L3 := lower_round F L2 (by norm_num) hd0
    (τ := (926137377/1000000000 : ℝ)) (n' := (85168101/100000000 : ℝ)) (Ab := (730298343/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R3 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc11.le) (by norm_num)
  have pc12 : 1 < (926137513/1000000000 : ℝ) ^ p + (122336699/125000000 : ℝ) ^ p := by
    exact cert_lt (x := (926137513/1000000000 : ℝ)) (y := (122336699/125000000 : ℝ)) (X := (14604136183687/50000000000000 : ℝ)) (Y := (70791734777041/100000000000000 : ℝ)) 2053 128
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc13 : 1 < (122336699/125000000 : ℝ) ^ p + (926137513/1000000000 : ℝ) ^ p := by simpa only [add_comm] using pc12
  have R4 := ratio_round F L3 (by norm_num) hD0
    (s := (380966221/200000000 : ℝ)) (τ := (926137513/1000000000 : ℝ)) (σ := (122336699/125000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc12) (by norm_num; exact pc13)
  have pc14 : 1 < (121716413/141946863 : ℝ) ^ p + (423491182/425840589 : ℝ) ^ p := by
    exact cert_lt (x := (121716413/141946863 : ℝ)) (y := (423491182/425840589 : ℝ)) (X := (424556092537/5000000000000 : ℝ)) (Y := (91508878433207/100000000000000 : ℝ)) 2053 128
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L4 := lower_round F L3 (by norm_num) hd0
    (τ := (926137513/1000000000 : ℝ)) (n' := (425840589/500000000 : ℝ)) (Ab := (365149239/500000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R4 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc14.le) (by norm_num)
  have pc15 : 1 < (926137517/1000000000 : ℝ) ^ p + (97869359/100000000 : ℝ) ^ p := by
    exact cert_lt (x := (926137517/1000000000 : ℝ)) (y := (97869359/100000000 : ℝ)) (X := (7302068597679/25000000000000 : ℝ)) (Y := (35395866228369/50000000000000 : ℝ)) 2053 128
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc16 : 1 < (97869359/100000000 : ℝ) ^ p + (926137517/1000000000 : ℝ) ^ p := by simpa only [add_comm] using pc15
  have R5 := ratio_round F L4 (by norm_num) hD0
    (s := (1904831107/1000000000 : ℝ)) (τ := (926137517/1000000000 : ℝ)) (σ := (97869359/100000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have pc17 : 1 < (730298482/851681183 : ℝ) ^ p + (846982369/851681183 : ℝ) ^ p := by
    exact cert_lt (x := (730298482/851681183 : ℝ)) (y := (846982369/851681183 : ℝ)) (X := (1698224359429/20000000000000 : ℝ)) (Y := (91508878481009/100000000000000 : ℝ)) 2053 128
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L5 := lower_round F L4 (by norm_num) hd0
    (τ := (926137517/1000000000 : ℝ)) (n' := (851681183/1000000000 : ℝ)) (Ab := (365149241/500000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R5 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have Rf := ratio_round F L5 (by norm_num) hD0
    (s := (1904831107/1000000000 : ℝ)) (τ := (926137517/1000000000 : ℝ)) (σ := (97869359/100000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have pc18 : 1 < (29114519/35587471 : ℝ) ^ p + (922924839/925274246 : ℝ) ^ p := by
    exact cert_lt (x := (29114519/35587471 : ℝ)) (y := (922924839/925274246 : ℝ)) (X := (1997855782371/50000000000000 : ℝ)) (Y := (48002144255961/50000000000000 : ℝ)) 2053 128
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc19 : 1 < (484009499/574725754 : ℝ) ^ p + (572376347/574725754 : ℝ) ^ p := by
    exact cert_lt (x := (484009499/574725754 : ℝ)) (y := (572376347/574725754 : ℝ)) (X := (3179415582849/50000000000000 : ℝ)) (Y := (93641168954497/100000000000000 : ℝ)) 2053 128
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have V := upper_round F L5 (by norm_num) hd0
    (σ := (97869359/100000000 : ℝ)) (U := (287362877/250000000 : ℝ)) (Ab := (378488747/250000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (Rf i j k a b c).2) (by norm_num) (by norm_num)
    (by norm_num; exact pc18.le) (by norm_num)
  refine ⟨V, ?_⟩
  exact final_round F L5 V (by norm_num) hd0
    (τ := (926137517/1000000000 : ℝ)) (σ := (97869359/100000000 : ℝ)) (Ab := (484009499/500000000 : ℝ))
    (by norm_num) (by norm_num) Rf (by norm_num) (by norm_num)
    (by norm_num; exact pc19.le) (by norm_num) (by norm_num) (by norm_num) (by norm_num)


end HlawkaSchatten.DiagonalRealBundle

/- The proof uses original lpNorm data and previously checked finite certificates. -/
open HlawkaSchatten HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle
set_option autoImplicit false
set_option maxHeartbeats 4000000
namespace HlawkaSchatten.DiagonalCutoff16

theorem localize_w001_s002 (p : ℝ) (hpa : (4105/256 : ℝ) ≤ p) (hpb : p ≤ (8211/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hB : coordinateBox (1137/5000 : ℝ) (6297/5000 : ℝ) (1541/2500 : ℝ) (6297/5000 : ℝ) X)
    (hS : lpNorm p (X 0) + lpNorm p (X 1) + lpNorm p (X 2) = 3)
    (hT1 : 1 ≤ lpNorm p (X 0 + X 1 + X 2))
    (hT : lpNorm p (X 0 + X 1 + X 2) < (62967/50000 : ℝ))
    (hfailure : ((42773/100000 : ℝ)*p) * pairGapSum (lpNorm p) (X 0) (X 1) (X 2) + lpNorm p (X 0 + X 1 + X 2) < 3)
    (htail : ∀ i j k : Fin 3, i ≠ j → i ≠ k → j ≠ k →
      lpNorm p (X j + X k) ≤ X j i + X k i + (1/100000000 : ℝ)) :
    X ∈ normCappedDomain p (1137/2500 : ℝ) (9677/10000 : ℝ) (7889/10000 : ℝ) (703/625 : ℝ) (1149243281/1000000000 : ℝ) (62967/50000 : ℝ) (55764416718720797/35116633000000000 : ℝ) (20147186954298101/3511663300000000 : ℝ) := by
  have htotal := barrier_w001_s002 p hpa hpb X hB hS hT1 hfailure htail
  have hg := gap_of_total_lower (by norm_num : (0 : ℝ) < (4105/256 : ℝ)) hpa
    (by norm_num : (0 : ℝ) < (42773/100000 : ℝ)) (pairGapSum_nonneg (by linarith) (X 0) (X 1) (X 2))
    hfailure htotal.le
  have hG : pairGapSum (lpNorm p) (X 0) (X 1) (X 2) < (28837273136/109739478125 : ℝ) := by
    convert hg using 1 <;> norm_num
  have hlo : (478847119/500000000 : ℝ) ≤ (1/2 : ℝ) ^ (1/(4105/256 : ℝ)) := by
    convert roots_w001_s002.1 using 1 <;> norm_num
  have hhi : (1/2 : ℝ) ^ (1/(8211/512 : ℝ)) ≤ (957699281/1000000000 : ℝ) := by
    convert roots_w001_s002.2.1 using 1 <;> norm_num
  have facts := facts_of (α := (4105/256 : ℝ)) (β := (8211/512 : ℝ))
    (D := (78793877116057/8779158250000000 : ℝ)) (δ := (4685789/1000000000 : ℝ)) (h := (922792845701899/3511663300000000 : ℝ))
    (A := (62967/50000 : ℝ)) (g := (28837273136/109739478125 : ℝ)) (eps := (1/100000000 : ℝ))
    (tlo := (478847119/500000000 : ℝ)) (thib := (957699281/1000000000 : ℝ))
    (by norm_num) hpa hpb (by linarith)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) hlo hhi
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) hB hS hT hG htail
  have hcontract := contract_w001_s002 p hpa hpb X (fun i ↦ lpNorm p (X i))
    (by convert facts using 1 <;> norm_num) (initial_norm_lower (by linarith) X hB)
  have hJ := pair_floor_of_gap (by linarith) X hS hcontract.1 hG htail
  have hW := offsum_floor_of_gap X hS hG htail
  refine ⟨hcontract.2, hcontract.1, hT.le, ?_, ?_⟩
  · intro i j k hij hik hjk
    have h := hJ i j k hij hik hjk
    convert h using 1 <;> norm_num
  · convert hW using 1 <;> norm_num


theorem localize_w001_s003 (p : ℝ) (hpa : (8211/512 : ℝ) ≤ p) (hpb : p ≤ (2053/128 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hB : coordinateBox (1137/5000 : ℝ) (6297/5000 : ℝ) (1541/2500 : ℝ) (6297/5000 : ℝ) X)
    (hS : lpNorm p (X 0) + lpNorm p (X 1) + lpNorm p (X 2) = 3)
    (hT1 : 1 ≤ lpNorm p (X 0 + X 1 + X 2))
    (hT : lpNorm p (X 0 + X 1 + X 2) < (62967/50000 : ℝ))
    (hfailure : ((42773/100000 : ℝ)*p) * pairGapSum (lpNorm p) (X 0) (X 1) (X 2) + lpNorm p (X 0 + X 1 + X 2) < 3)
    (htail : ∀ i j k : Fin 3, i ≠ j → i ≠ k → j ≠ k →
      lpNorm p (X j + X k) ≤ X j i + X k i + (1/100000000 : ℝ)) :
    X ∈ normCappedDomain p (909/2000 : ℝ) (9681/10000 : ℝ) (7887/10000 : ℝ) (9/8 : ℝ) (287362877/250000000 : ℝ) (62967/50000 : ℝ) (16401200084671519/10329679500000000 : ℝ) (11852740811301923/2065935900000000 : ℝ) := by
  have htotal := barrier_w001_s003 p hpa hpb X hB hS hT1 hfailure htail
  have hg := gap_of_total_lower (by norm_num : (0 : ℝ) < (8211/512 : ℝ)) hpa
    (by norm_num : (0 : ℝ) < (42773/100000 : ℝ)) (pairGapSum_nonneg (by linarith) (X 0) (X 1) (X 2))
    hfailure htotal.le
  have hG : pairGapSum (lpNorm p) (X 0) (X 1) (X 2) < (3392965792/12912099375 : ℝ) := by
    convert hg using 1 <;> norm_num
  have hlo : (11971241/12500000 : ℝ) ≤ (1/2 : ℝ) ^ (1/(8211/512 : ℝ)) := by
    convert roots_w001_s003.1 using 1 <;> norm_num
  have hhi : (1/2 : ℝ) ^ (1/(2053/128 : ℝ)) ≤ (478852161/500000000 : ℝ) := by
    convert roots_w001_s003.2.1 using 1 <;> norm_num
  have facts := facts_of (α := (8211/512 : ℝ)) (β := (2053/128 : ℝ))
    (D := (92968155639179/10329679500000000 : ℝ)) (δ := (2349407/500000000 : ℝ)) (h := (542874588698077/2065935900000000 : ℝ))
    (A := (62967/50000 : ℝ)) (g := (3392965792/12912099375 : ℝ)) (eps := (1/100000000 : ℝ))
    (tlo := (11971241/12500000 : ℝ)) (thib := (478852161/500000000 : ℝ))
    (by norm_num) hpa hpb (by linarith)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) hlo hhi
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) hB hS hT hG htail
  have hcontract := contract_w001_s003 p hpa hpb X (fun i ↦ lpNorm p (X i))
    (by convert facts using 1 <;> norm_num) (initial_norm_lower (by linarith) X hB)
  have hJ := pair_floor_of_gap (by linarith) X hS hcontract.1 hG htail
  have hW := offsum_floor_of_gap X hS hG htail
  refine ⟨hcontract.2, hcontract.1, hT.le, ?_, ?_⟩
  · intro i j k hij hik hjk
    have h := hJ i j k hij hik hjk
    convert h using 1 <;> norm_num
  · convert hW using 1 <;> norm_num


end HlawkaSchatten.DiagonalCutoff16

/- The generic Hessian and averaging proofs are from accepted submission
de577b6b-0253-45ac-9b17-ccf002bb69a6 (Ezzeri Esa, bwdaugherty, Yuxuan Xu;
Apache-2.0). All geometry and finite margins below are checked anew. -/
set_option autoImplicit false
set_option maxHeartbeats 200000000
set_option maxRecDepth 10000
set_option exponentiation.threshold 20000
namespace HlawkaSchatten.DiagonalRealBundle
open HlawkaSchatten.DiagonalConstruction


theorem curvature_w001_s002 (p : ℝ) (hpa : (4105/256 : ℝ) ≤ p) (hpb : p ≤ (8211/512 : ℝ)) :
    p * (550811365018069580013922815840092817854214208405544800000/11632657539645208700983662097268788137053425976431402431 : ℝ) * (243529581387387499837104800000000/404887788993176145248810007538403 : ℝ) ^ (p-2) < 1 ∧
    (109505918251847524950304374128065440760218403101996187957790527426909225337229338614363104325/3472677904500772169763836350082632462111780823743397327853165530431355168673752752211815584 : ℝ) * (474645198787258779353/634041418091855461890 : ℝ) ^ (p-2) < 2*(42773/100000 : ℝ)-1/p := by
  have hp0 : 0 < p := by linarith

  have hrT : (243529581387387499837104800000000/404887788993176145248810007538403 : ℝ) ^ (p-2) ≤ (243529581387387499837104800000000/404887788993176145248810007538403 : ℝ) ^ (14 : ℕ) := by
    have h := Real.rpow_le_rpow_of_exponent_ge' (x := (243529581387387499837104800000000/404887788993176145248810007538403 : ℝ))
      (by norm_num) (by norm_num) (by norm_num : (0 : ℝ) ≤ 14) (by linarith : (14 : ℝ) ≤ p-2)
    calc _ ≤ (243529581387387499837104800000000/404887788993176145248810007538403 : ℝ) ^ ((14 : ℕ) : ℝ) := h
         _ = _ := Real.rpow_natCast _ _

  have hrC : (474645198787258779353/634041418091855461890 : ℝ) ^ (p-2) ≤ (474645198787258779353/634041418091855461890 : ℝ) ^ (14 : ℕ) := by
    have h := Real.rpow_le_rpow_of_exponent_ge' (x := (474645198787258779353/634041418091855461890 : ℝ))
      (by norm_num) (by norm_num) (by norm_num : (0 : ℝ) ≤ 14) (by linarith : (14 : ℝ) ≤ p-2)
    calc _ ≤ (474645198787258779353/634041418091855461890 : ℝ) ^ ((14 : ℕ) : ℝ) := h
         _ = _ := Real.rpow_natCast _ _

  constructor
  · have h1 := mul_le_mul_of_nonneg_left hrT (show 0 ≤ p*(550811365018069580013922815840092817854214208405544800000/11632657539645208700983662097268788137053425976431402431 : ℝ) by positivity)
    have h2 := mul_le_mul_of_nonneg_right hpb (show 0 ≤ (550811365018069580013922815840092817854214208405544800000/11632657539645208700983662097268788137053425976431402431 : ℝ)*((243529581387387499837104800000000/404887788993176145248810007538403 : ℝ) ^ (14 : ℕ)) by norm_num)
    have hend : (8211/512 : ℝ)*(550811365018069580013922815840092817854214208405544800000/11632657539645208700983662097268788137053425976431402431 : ℝ)*((243529581387387499837104800000000/404887788993176145248810007538403 : ℝ) ^ (14 : ℕ)) < 1 := by norm_num
    nlinarith only [h1,h2,hend]
  · have h1 := mul_le_mul_of_nonneg_left hrC (show 0 ≤ (109505918251847524950304374128065440760218403101996187957790527426909225337229338614363104325/3472677904500772169763836350082632462111780823743397327853165530431355168673752752211815584 : ℝ) by norm_num)
    have hinv : 1/p ≤ 1/(4105/256 : ℝ) := one_div_le_one_div_of_le (by norm_num) hpa
    have hend : (109505918251847524950304374128065440760218403101996187957790527426909225337229338614363104325/3472677904500772169763836350082632462111780823743397327853165530431355168673752752211815584 : ℝ)*((474645198787258779353/634041418091855461890 : ℝ) ^ (14 : ℕ)) < 2*(42773/100000 : ℝ)-1/(4105/256 : ℝ) := by norm_num
    linarith only [h1,hinv,hend]


theorem nonneg_w001_s002 (p : ℝ) (hpa : (4105/256 : ℝ) ≤ p) (hpb : p ≤ (8211/512 : ℝ))
    (hKlo : (42773/100000 : ℝ)*p ≤ cyclicConstant p) (hKhi : cyclicConstant p ≤ p/2)
    (X : Triple) (hX : X ∈ normCappedDomain p (1137/2500 : ℝ) (9677/10000 : ℝ) (7889/10000 : ℝ) (703/625 : ℝ) (1149243281/1000000000 : ℝ) (62967/50000 : ℝ) (55764416718720797/35116633000000000 : ℝ) (20147186954298101/3511663300000000 : ℝ)) :
    0 ≤ tripleDeficit p (cyclicConstant p) X := by
  let GT : ℝ := pairTotalFactor (1137/2500 : ℝ) (703/625 : ℝ) (21782050964620797/35116633000000000 : ℝ) (62967/50000 : ℝ) (6 : ℝ) (1/4 : ℝ)
  let GC : ℝ := pairColumnFactor (1137/2500 : ℝ) (703/625 : ℝ) (21782050964620797/35116633000000000 : ℝ) (62967/50000 : ℝ) (11761/25000 : ℝ) (55764416718720797/35116633000000000 : ℝ) (6 : ℝ) (1/4 : ℝ)
  have hmarg := curvature_w001_s002 p hpa hpb
  have hNT : (p/2) * GT * ((62967/50000 : ℝ)/(55764416718720797/35116633000000000 : ℝ)) *
      (((11761/25000 : ℝ)*(62967/50000 : ℝ))/((55764416718720797/35116633000000000 : ℝ)*(21782050964620797/35116633000000000 : ℝ))) ^ (p-2) ≤ 1 := by
    have hbase : (((11761/25000 : ℝ)*(62967/50000 : ℝ))/((55764416718720797/35116633000000000 : ℝ)*(21782050964620797/35116633000000000 : ℝ))) = (243529581387387499837104800000000/404887788993176145248810007538403 : ℝ) := by norm_num
    have hconst : GT * ((62967/50000 : ℝ)/(55764416718720797/35116633000000000 : ℝ)) / 2 = (550811365018069580013922815840092817854214208405544800000/11632657539645208700983662097268788137053425976431402431 : ℝ) := by
      norm_num [GT, pairTotalFactor, shapeFactor]
    have hprod : (p/2) * GT * ((62967/50000 : ℝ)/(55764416718720797/35116633000000000 : ℝ)) = p * (550811365018069580013922815840092817854214208405544800000/11632657539645208700983662097268788137053425976431402431 : ℝ) := by
      calc _ = p * (GT * ((62967/50000 : ℝ)/(55764416718720797/35116633000000000 : ℝ)) / 2) := by ring
           _ = _ := by rw [hconst]
    rw [hbase, hprod]
    exact hmarg.1.le
  have hNC : (GC/2) * ((1149243281/1000000000 : ℝ)/(55764416718720797/35116633000000000 : ℝ)) *
      (((11761/25000 : ℝ)*(1149243281/1000000000 : ℝ))/((55764416718720797/35116633000000000 : ℝ)*(1137/2500 : ℝ))) ^ (p-2) ≤ 2*(42773/100000 : ℝ)-1/p := by
    have hbase : (((11761/25000 : ℝ)*(1149243281/1000000000 : ℝ))/((55764416718720797/35116633000000000 : ℝ)*(1137/2500 : ℝ))) = (474645198787258779353/634041418091855461890 : ℝ) := by norm_num
    have hconst : (GC/2) * ((1149243281/1000000000 : ℝ)/(55764416718720797/35116633000000000 : ℝ)) = (109505918251847524950304374128065440760218403101996187957790527426909225337229338614363104325/3472677904500772169763836350082632462111780823743397327853165530431355168673752752211815584 : ℝ) := by
      norm_num [GC, pairColumnFactor, shapeFactor]
    rw [hbase, hconst]
    exact hmarg.2.le
  exact HlawkaSchatten.DiagonalCutoff16.nonnegative_of_curvature_margins
    (p := p) (c := (42773/100000 : ℝ)) (ell := (1137/2500 : ℝ)) (u := (9677/10000 : ℝ)) (v := (7889/10000 : ℝ)) (w := (703/625 : ℝ)) (U := (1149243281/1000000000 : ℝ)) (A := (62967/50000 : ℝ)) (J := (55764416718720797/35116633000000000 : ℝ)) (W0 := (20147186954298101/3511663300000000 : ℝ)) (m := (1137/2500 : ℝ)) (M := (703/625 : ℝ)) (L := (55764416718720797/35116633000000000 : ℝ)) (s := (21782050964620797/35116633000000000 : ℝ)) (t := (62967/50000 : ℝ)) (eta := (11761/25000 : ℝ)) (eps1 := (6 : ℝ)) (eps2 := (1/4 : ℝ)) (gT := GT) (gC := GC)
    (by linarith) (by nlinarith [hKlo]) hKlo hKhi
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [GT, pairTotalFactor, shapeFactor])
    (by norm_num [GC, pairColumnFactor, shapeFactor])
    hNT hNC X hX.1 hX.2.1 hX.2.2.1 hX.2.2.2.1 hX.2.2.2.2

theorem curvature_w001_s003 (p : ℝ) (hpa : (8211/512 : ℝ) ≤ p) (hpb : p ≤ (2053/128 : ℝ)) :
    p * (2990702241393083237359469129982660364879546298437500000/63030718610847952643224958357779670834447007629113159 : ℝ) * (63241989970350246721016400000000/104984694502651333930841949717361 : ℝ) ^ (p-2) < 1 ∧
    (84844620291296583533085221914506279491833700627347921467522228140104821342584640386235/2685975957621508360680379675286474157645384620319662437098175734056894827497095255984 : ℝ) * (307377771556495528/410030002116787975 : ℝ) ^ (p-2) < 2*(42773/100000 : ℝ)-1/p := by
  have hp0 : 0 < p := by linarith

  have hrT : (63241989970350246721016400000000/104984694502651333930841949717361 : ℝ) ^ (p-2) ≤ (63241989970350246721016400000000/104984694502651333930841949717361 : ℝ) ^ (14 : ℕ) := by
    have h := Real.rpow_le_rpow_of_exponent_ge' (x := (63241989970350246721016400000000/104984694502651333930841949717361 : ℝ))
      (by norm_num) (by norm_num) (by norm_num : (0 : ℝ) ≤ 14) (by linarith : (14 : ℝ) ≤ p-2)
    calc _ ≤ (63241989970350246721016400000000/104984694502651333930841949717361 : ℝ) ^ ((14 : ℕ) : ℝ) := h
         _ = _ := Real.rpow_natCast _ _

  have hrC : (307377771556495528/410030002116787975 : ℝ) ^ (p-2) ≤ (307377771556495528/410030002116787975 : ℝ) ^ (14 : ℕ) := by
    have h := Real.rpow_le_rpow_of_exponent_ge' (x := (307377771556495528/410030002116787975 : ℝ))
      (by norm_num) (by norm_num) (by norm_num : (0 : ℝ) ≤ 14) (by linarith : (14 : ℝ) ≤ p-2)
    calc _ ≤ (307377771556495528/410030002116787975 : ℝ) ^ ((14 : ℕ) : ℝ) := h
         _ = _ := Real.rpow_natCast _ _

  constructor
  · have h1 := mul_le_mul_of_nonneg_left hrT (show 0 ≤ p*(2990702241393083237359469129982660364879546298437500000/63030718610847952643224958357779670834447007629113159 : ℝ) by positivity)
    have h2 := mul_le_mul_of_nonneg_right hpb (show 0 ≤ (2990702241393083237359469129982660364879546298437500000/63030718610847952643224958357779670834447007629113159 : ℝ)*((63241989970350246721016400000000/104984694502651333930841949717361 : ℝ) ^ (14 : ℕ)) by norm_num)
    have hend : (2053/128 : ℝ)*(2990702241393083237359469129982660364879546298437500000/63030718610847952643224958357779670834447007629113159 : ℝ)*((63241989970350246721016400000000/104984694502651333930841949717361 : ℝ) ^ (14 : ℕ)) < 1 := by norm_num
    nlinarith only [h1,h2,hend]
  · have h1 := mul_le_mul_of_nonneg_left hrC (show 0 ≤ (84844620291296583533085221914506279491833700627347921467522228140104821342584640386235/2685975957621508360680379675286474157645384620319662437098175734056894827497095255984 : ℝ) by norm_num)
    have hinv : 1/p ≤ 1/(8211/512 : ℝ) := one_div_le_one_div_of_le (by norm_num) hpa
    have hend : (84844620291296583533085221914506279491833700627347921467522228140104821342584640386235/2685975957621508360680379675286474157645384620319662437098175734056894827497095255984 : ℝ)*((307377771556495528/410030002116787975 : ℝ) ^ (14 : ℕ)) < 2*(42773/100000 : ℝ)-1/(8211/512 : ℝ) := by norm_num
    linarith only [h1,hinv,hend]


theorem nonneg_w001_s003 (p : ℝ) (hpa : (8211/512 : ℝ) ≤ p) (hpb : p ≤ (2053/128 : ℝ))
    (hKlo : (42773/100000 : ℝ)*p ≤ cyclicConstant p) (hKhi : cyclicConstant p ≤ p/2)
    (X : Triple) (hX : X ∈ normCappedDomain p (909/2000 : ℝ) (9681/10000 : ℝ) (7887/10000 : ℝ) (9/8 : ℝ) (287362877/250000000 : ℝ) (62967/50000 : ℝ) (16401200084671519/10329679500000000 : ℝ) (11852740811301923/2065935900000000 : ℝ)) :
    0 ≤ tripleDeficit p (cyclicConstant p) X := by
  let GT : ℝ := pairTotalFactor (909/2000 : ℝ) (9/8 : ℝ) (6401037360721519/10329679500000000 : ℝ) (62967/50000 : ℝ) (6 : ℝ) (1/4 : ℝ)
  let GC : ℝ := pairColumnFactor (909/2000 : ℝ) (9/8 : ℝ) (6401037360721519/10329679500000000 : ℝ) (62967/50000 : ℝ) (5883/12500 : ℝ) (16401200084671519/10329679500000000 : ℝ) (6 : ℝ) (1/4 : ℝ)
  have hmarg := curvature_w001_s003 p hpa hpb
  have hNT : (p/2) * GT * ((62967/50000 : ℝ)/(16401200084671519/10329679500000000 : ℝ)) *
      (((5883/12500 : ℝ)*(62967/50000 : ℝ))/((16401200084671519/10329679500000000 : ℝ)*(6401037360721519/10329679500000000 : ℝ))) ^ (p-2) ≤ 1 := by
    have hbase : (((5883/12500 : ℝ)*(62967/50000 : ℝ))/((16401200084671519/10329679500000000 : ℝ)*(6401037360721519/10329679500000000 : ℝ))) = (63241989970350246721016400000000/104984694502651333930841949717361 : ℝ) := by norm_num
    have hconst : GT * ((62967/50000 : ℝ)/(16401200084671519/10329679500000000 : ℝ)) / 2 = (2990702241393083237359469129982660364879546298437500000/63030718610847952643224958357779670834447007629113159 : ℝ) := by
      norm_num [GT, pairTotalFactor, shapeFactor]
    have hprod : (p/2) * GT * ((62967/50000 : ℝ)/(16401200084671519/10329679500000000 : ℝ)) = p * (2990702241393083237359469129982660364879546298437500000/63030718610847952643224958357779670834447007629113159 : ℝ) := by
      calc _ = p * (GT * ((62967/50000 : ℝ)/(16401200084671519/10329679500000000 : ℝ)) / 2) := by ring
           _ = _ := by rw [hconst]
    rw [hbase, hprod]
    exact hmarg.1.le
  have hNC : (GC/2) * ((287362877/250000000 : ℝ)/(16401200084671519/10329679500000000 : ℝ)) *
      (((5883/12500 : ℝ)*(287362877/250000000 : ℝ))/((16401200084671519/10329679500000000 : ℝ)*(909/2000 : ℝ))) ^ (p-2) ≤ 2*(42773/100000 : ℝ)-1/p := by
    have hbase : (((5883/12500 : ℝ)*(287362877/250000000 : ℝ))/((16401200084671519/10329679500000000 : ℝ)*(909/2000 : ℝ))) = (307377771556495528/410030002116787975 : ℝ) := by norm_num
    have hconst : (GC/2) * ((287362877/250000000 : ℝ)/(16401200084671519/10329679500000000 : ℝ)) = (84844620291296583533085221914506279491833700627347921467522228140104821342584640386235/2685975957621508360680379675286474157645384620319662437098175734056894827497095255984 : ℝ) := by
      norm_num [GC, pairColumnFactor, shapeFactor]
    rw [hbase, hconst]
    exact hmarg.2.le
  exact HlawkaSchatten.DiagonalCutoff16.nonnegative_of_curvature_margins
    (p := p) (c := (42773/100000 : ℝ)) (ell := (909/2000 : ℝ)) (u := (9681/10000 : ℝ)) (v := (7887/10000 : ℝ)) (w := (9/8 : ℝ)) (U := (287362877/250000000 : ℝ)) (A := (62967/50000 : ℝ)) (J := (16401200084671519/10329679500000000 : ℝ)) (W0 := (11852740811301923/2065935900000000 : ℝ)) (m := (909/2000 : ℝ)) (M := (9/8 : ℝ)) (L := (16401200084671519/10329679500000000 : ℝ)) (s := (6401037360721519/10329679500000000 : ℝ)) (t := (62967/50000 : ℝ)) (eta := (5883/12500 : ℝ)) (eps1 := (6 : ℝ)) (eps2 := (1/4 : ℝ)) (gT := GT) (gC := GC)
    (by linarith) (by nlinarith [hKlo]) hKlo hKhi
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [GT, pairTotalFactor, shapeFactor])
    (by norm_num [GC, pairColumnFactor, shapeFactor])
    hNT hNC X hX.1 hX.2.1 hX.2.2.1 hX.2.2.2.1 hX.2.2.2.2

end HlawkaSchatten.DiagonalRealBundle


open HlawkaSchatten HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle
namespace HlawkaSchatten.DiagonalCutoff16

theorem no_failure_w001_s002 (p : ℝ) (hpa : (4105/256 : ℝ) ≤ p) (hpb : p ≤ (8211/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hKlo : (42773/100000 : ℝ)*p ≤ cyclicConstant p) (hKhi : cyclicConstant p ≤ p/2)
    (hB : coordinateBox (1137/5000 : ℝ) (6297/5000 : ℝ) (1541/2500 : ℝ) (6297/5000 : ℝ) X)
    (hS : lpNorm p (X 0) + lpNorm p (X 1) + lpNorm p (X 2) = 3)
    (hT1 : 1 ≤ lpNorm p (X 0 + X 1 + X 2)) (hT : lpNorm p (X 0 + X 1 + X 2) < (62967/50000 : ℝ))
    (hf : ((42773/100000 : ℝ)*p)*pairGapSum (lpNorm p) (X 0) (X 1) (X 2) + lpNorm p (X 0 + X 1 + X 2) < 3)
    (htail : ∀ i j k : Fin 3, i ≠ j → i ≠ k → j ≠ k → lpNorm p (X j + X k) ≤ X j i + X k i + (1/100000000 : ℝ))
    (hneg : tripleDeficit p (cyclicConstant p) X < 0) : False := by
  have hloc := localize_w001_s002 p hpa hpb X hB hS hT1 hT hf htail
  have hn := nonneg_w001_s002 p hpa hpb hKlo hKhi X hloc
  linarith

theorem no_failure_w001_s003 (p : ℝ) (hpa : (8211/512 : ℝ) ≤ p) (hpb : p ≤ (2053/128 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hKlo : (42773/100000 : ℝ)*p ≤ cyclicConstant p) (hKhi : cyclicConstant p ≤ p/2)
    (hB : coordinateBox (1137/5000 : ℝ) (6297/5000 : ℝ) (1541/2500 : ℝ) (6297/5000 : ℝ) X)
    (hS : lpNorm p (X 0) + lpNorm p (X 1) + lpNorm p (X 2) = 3)
    (hT1 : 1 ≤ lpNorm p (X 0 + X 1 + X 2)) (hT : lpNorm p (X 0 + X 1 + X 2) < (62967/50000 : ℝ))
    (hf : ((42773/100000 : ℝ)*p)*pairGapSum (lpNorm p) (X 0) (X 1) (X 2) + lpNorm p (X 0 + X 1 + X 2) < 3)
    (htail : ∀ i j k : Fin 3, i ≠ j → i ≠ k → j ≠ k → lpNorm p (X j + X k) ≤ X j i + X k i + (1/100000000 : ℝ))
    (hneg : tripleDeficit p (cyclicConstant p) X < 0) : False := by
  have hloc := localize_w001_s003 p hpa hpb X hB hS hT1 hT hf htail
  have hn := nonneg_w001_s003 p hpa hpb hKlo hKhi X hloc
  linarith

theorem real_three_w001_s002_003 (p : ℝ) (hpa : (4105/256 : ℝ) ≤ p) (hpb : p ≤ (2053/128 : ℝ)) :
    HasHlawkaConstant (lpNorm p : (Fin 3 → ℝ) → ℝ) (cyclicConstant p) := by
  intro x y z
  by_contra hn
  have hf : hlawkaDeficit p (cyclicConstant p) x y z < 0 := by
    rw [hlawkaDeficit_eq]
    exact sub_neg.mpr (lt_of_not_ge hn)
  obtain ⟨X,hKlo,hKhi,hB,hS,hT1,hT,hfailure,htail,hneg⟩ :=
    coarse_failure_window01 p (by linarith) (by linarith) x y z hf

  by_cases hb2 : p ≤ (8211/512 : ℝ)
  · exact no_failure_w001_s002 p (by linarith) hb2 X hKlo hKhi hB hS hT1 hT hfailure htail hneg

  exact no_failure_w001_s003 p (by linarith) hpb X hKlo hKhi hB hS hT1 hT hfailure htail hneg

end HlawkaSchatten.DiagonalCutoff16


theorem solution :
    ∀ p : ℝ, (4105/256 : ℝ) ≤ p → p ≤ (2053/128 : ℝ) →
      HasHlawkaConstant (lpNorm p : (Fin 3 → ℝ) → ℝ) (cyclicConstant p) := by
  intro p hpa hpb
  exact HlawkaSchatten.DiagonalCutoff16.real_three_w001_s002_003 p hpa hpb

#print axioms solution
