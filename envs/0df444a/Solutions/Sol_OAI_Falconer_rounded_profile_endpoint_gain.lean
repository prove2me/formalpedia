-- Prove2me | solution 1 for OAI.Falconer.rounded_profile_endpoint_gain
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-29T22:31:53.99003+00:00
-- url     : https://prove2.me/submissions/ab2a3ec3-f2f8-4204-b39d-b41c3157a3e0

import Mathlib
import Definitions.Def_OAIQ088F002
import Theorems.Thm_OAI_Falconer_block_cell_power

section
-- module Solutions.OAIQ088_FD.Falconer_Angular_AngularGainFinite
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.sphereMeasure_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Finite labelled incidence obstruction

The sampling argument in `ang:planar-measures` ends with finite point
and line families. Their counting contradiction follows
from the precise published Furstenberg input. All line families must use
a common separated grid before cardinalities replace covering numbers.
Direction labels remain distinct throughout the upper counting estimate.
-/

namespace Falconer
open Set
open scoped BigOperators

/-- A labelled family bounds a union even when two labels have the same
geometric coordinate. No identification of their fibers is required. -/
theorem labelled_line_union_card_le {ι : Type*} [DecidableEq ι]
    (P : Finset (Space 2)) (T : Space 2 → Finset (Space 2))
    (D : Finset ι) (U : ι → Finset (Space 2)) {L : ℝ}
    (hcover : ∀ x ∈ P, ∀ l ∈ T x, ∃ i ∈ D, l ∈ U i)
    (hU : ∀ i ∈ D, ((U i).card : ℝ) ≤ L) :
    ((P.biUnion T).card : ℝ) ≤ (D.card : ℝ) * L := by
  classical
  have hsub : P.biUnion T ⊆ D.biUnion U := by
    intro l hl
    obtain ⟨x, hx, hl⟩ := Finset.mem_biUnion.mp hl
    obtain ⟨i, hi, hli⟩ := hcover x hx l hl
    exact Finset.mem_biUnion.mpr ⟨i, hi, hli⟩
  calc
    ((P.biUnion T).card : ℝ) ≤ ((D.biUnion U).card : ℝ) := by
      exact_mod_cast Finset.card_le_card hsub
    _ ≤ ∑ i ∈ D, ((U i).card : ℝ) := by
      exact_mod_cast (Finset.card_biUnion_le (s := D) (t := U))
    _ ≤ ∑ _i ∈ D, L := Finset.sum_le_sum hU
    _ = (D.card : ℝ) * L := by simp

theorem lineGridRound_error {δ : ℝ} (hδ : 0 < δ) (a : ℝ) :
    |a - lineGridRound δ a| ≤ δ / 2 := by
  have h := abs_sub_round (a / δ)
  calc
    |a - lineGridRound δ a| = |δ * (a / δ - (round (a / δ) : ℝ))| := by
      congr 1
      simp only [lineGridRound]
      field_simp
    _ = δ * |a / δ - (round (a / δ) : ℝ)| := by rw [abs_mul, abs_of_pos hδ]
    _ ≤ δ * (1 / 2) := mul_le_mul_of_nonneg_left h hδ.le
    _ = δ / 2 := by ring

theorem roundedIncidentLine_incident {δ : ℝ} (hδ : 0 < δ) (x : Space 2) (m : ℝ) :
    TubeIncident δ x (roundedIncidentLine δ x m) := by
  have herr := lineGridRound_error hδ (x 1 - lineGridRound δ m * x 0)
  have hsqrt : 1 ≤ Real.sqrt (1 + (lineGridRound δ m) ^ 2) := by
    rw [Real.le_sqrt (by norm_num) (by positivity)]
    nlinarith [sq_nonneg (lineGridRound δ m)]
  change |x 1 - lineGridRound δ m * x 0 -
      lineGridRound δ (x 1 - lineGridRound δ m * x 0)| /
      Real.sqrt (1 + (lineGridRound δ m) ^ 2) ≤ δ
  exact (div_le_self (abs_nonneg _) hsqrt).trans (herr.trans (by linarith))

/-- A strip in one original direction contains only a bounded interval of
grid intercepts after rounding that direction. The interval is uniform
in its original label, so coincident directions need not share covers. -/
theorem roundedIncidentLine_near_strip {δ C a m : ℝ} (hδ : 0 < δ)
    (x : Space 2) (hx : |x 0| ≤ 1)
    (hstrip : |x 1 - m * x 0 - a| ≤ C * δ) :
    |roundedIncidentLine δ x m 1 - a| ≤ (C + 1) * δ := by
  have hms := lineGridRound_error hδ m
  have hi := lineGridRound_error hδ (x 1 - lineGridRound δ m * x 0)
  have htilt : |(m - lineGridRound δ m) * x 0| ≤ δ / 2 := by
    rw [abs_mul]
    exact (mul_le_mul hms hx (abs_nonneg _) (by positivity)).trans_eq (mul_one _)
  calc
    |roundedIncidentLine δ x m 1 - a| ≤
        |roundedIncidentLine δ x m 1 - (x 1 - lineGridRound δ m * x 0)| +
        |(x 1 - lineGridRound δ m * x 0) - a| := abs_sub_le _ _ _
    _ = |(x 1 - lineGridRound δ m * x 0) - roundedIncidentLine δ x m 1| +
        |(x 1 - m * x 0 - a) + (m - lineGridRound δ m) * x 0| := by
      rw [abs_sub_comm (roundedIncidentLine δ x m 1)]
      congr 2
      ring
    _ ≤ δ / 2 + (C * δ + δ / 2) := by
      apply add_le_add hi
      exact (abs_add_le _ _).trans (add_le_add hstrip htilt)
    _ = (C + 1) * δ := by ring

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Angular_AngularGrid
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.sphereMeasure_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# A common line grid for the planar incidence obstruction

Each original strip gives a bounded list of common-grid line parameters.
The list is attached to its original direction label. Rounding therefore
turns the manuscript's covering-number upper bound into the cardinality
upper bound needed by `published_furstenberg_labelled_obstruction`.
-/

namespace Falconer
open Set

private theorem integer_grid_separation {δ : ℝ} (hδ : 0 < δ) {i j : ℤ}
    (hij : i ≠ j) : δ ≤ |δ * (i : ℝ) - δ * (j : ℝ)| := by
  have hzpos : (0 : ℤ) < |i - j| := abs_pos.mpr (sub_ne_zero.mpr hij)
  have hz : (1 : ℤ) ≤ |i - j| := by omega
  have hr : (1 : ℝ) ≤ |(i : ℝ) - (j : ℝ)| := by exact_mod_cast hz
  calc
    δ = δ * 1 := (mul_one _).symm
    _ ≤ δ * |(i : ℝ) - (j : ℝ)| := mul_le_mul_of_nonneg_left hr hδ.le
    _ = |δ * (i : ℝ) - δ * (j : ℝ)| := by
      rw [← mul_sub, abs_mul, abs_of_pos hδ]

theorem gridLine_dist_ge {δ : ℝ} (hδ : 0 < δ) {p q : ℤ × ℤ} (hpq : p ≠ q) :
    δ ≤ dist (gridLine δ p) (gridLine δ q) := by
  by_cases hfst : p.1 = q.1
  · have hsnd : p.2 ≠ q.2 := by
      intro h
      exact hpq (Prod.ext hfst h)
    calc
      δ ≤ |δ * (p.2 : ℝ) - δ * (q.2 : ℝ)| := integer_grid_separation hδ hsnd
      _ = dist (gridLine δ p 1) (gridLine δ q 1) := by
        rw [gridLine_snd, gridLine_snd, Real.dist_eq]
      _ ≤ dist (gridLine δ p) (gridLine δ q) := PiLp.dist_apply_le _ _ 1
  · calc
      δ ≤ |δ * (p.1 : ℝ) - δ * (q.1 : ℝ)| := integer_grid_separation hδ hfst
      _ = dist (gridLine δ p 0) (gridLine δ q 0) := by
        rw [gridLine_fst, gridLine_fst, Real.dist_eq]
      _ ≤ dist (gridLine δ p) (gridLine δ q) := PiLp.dist_apply_le _ _ 0

theorem roundedIncidentLine_family_separated {ι : Type*} [DecidableEq ι]
    {δ : ℝ} (hδ : 0 < δ) (x : Space 2) (m : ι → ℝ) (D : Finset ι) :
    FiniteSeparatedAt δ (D.image (fun i => roundedIncidentLine δ x (m i))) := by
  intro l hl l' hl' hll'
  obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hl
  obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hl'
  apply gridLine_dist_ge hδ
    (p := (round (m i / δ), round ((x 1 - lineGridRound δ (m i) * x 0) / δ)))
    (q := (round (m j / δ), round ((x 1 - lineGridRound δ (m j) * x 0) / δ)))
  intro heq
  exact hll' (congrArg (gridLine δ) heq)

/-- A fixed smaller chart leaves room for rounding while staying inside
the unit chart used by the published finite theorem. -/
theorem roundedIncidentLine_in_chart {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1 / 2)
    (x : Space 2) (hx0 : |x 0| ≤ 1 / 4) (hx1 : |x 1| ≤ 1 / 4)
    (m : ℝ) (hm : |m| ≤ 1 / 2) :
    |roundedIncidentLine δ x m 0| ≤ 1 ∧ |roundedIncidentLine δ x m 1| ≤ 1 := by
  have hM : |lineGridRound δ m| ≤ 1 := by
    have hsum := abs_sub_le (lineGridRound δ m) m 0
    have herr := lineGridRound_error hδ m
    rw [sub_zero, sub_zero, abs_sub_comm (lineGridRound δ m)] at hsum
    linarith
  constructor
  · exact hM
  · have ht : |x 1 - lineGridRound δ m * x 0| ≤ 1 / 2 := by
      have hprod : |lineGridRound δ m * x 0| ≤ 1 / 4 := by
        rw [abs_mul]
        exact (mul_le_mul hM hx0 (abs_nonneg _) (by norm_num)).trans_eq (one_mul _)
      have htri : |x 1 - lineGridRound δ m * x 0| ≤
          |x 1| + |lineGridRound δ m * x 0| := by
        simpa using abs_sub_le (x 1) 0 (lineGridRound δ m * x 0)
      exact htri.trans (by linarith)
    have hsum := abs_sub_le
      (lineGridRound δ (x 1 - lineGridRound δ m * x 0))
      (x 1 - lineGridRound δ m * x 0) 0
    have herr := lineGridRound_error hδ (x 1 - lineGridRound δ m * x 0)
    rw [sub_zero, sub_zero, abs_sub_comm (lineGridRound δ (x 1 - lineGridRound δ m * x 0))]
      at hsum
    change |lineGridRound δ (x 1 - lineGridRound δ m * x 0)| ≤ 1
    linarith

theorem roundedStripCandidates_card_le (δ m a : ℝ) (L : ℕ) :
    (roundedStripCandidates δ m a L).card ≤ 2 * L + 1 := by
  classical
  calc
    (roundedStripCandidates δ m a L).card ≤
        (Finset.Icc (round (a / δ) - (L : ℤ)) (round (a / δ) + (L : ℤ))).card :=
      Finset.card_image_le
    _ = 2 * L + 1 := by
      rw [Int.card_Icc]
      omega

/-- A rounded line through any point of a strip belongs to that strip's
bounded candidate list. This is the fixed-width loss in `ang:planar-measures`. -/
theorem roundedIncidentLine_mem_candidates {δ C a m : ℝ} (hδ : 0 < δ)
    (x : Space 2) (hx : |x 0| ≤ 1)
    (hstrip : |x 1 - m * x 0 - a| ≤ C * δ)
    (L : ℕ) (hL : C + 2 ≤ (L : ℝ)) :
    roundedIncidentLine δ x m ∈ roundedStripCandidates δ m a L := by
  classical
  let j : ℤ := round ((x 1 - lineGridRound δ m * x 0) / δ)
  let j₀ : ℤ := round (a / δ)
  have hnear : |δ * (j : ℝ) - a| ≤ (C + 1) * δ :=
    roundedIncidentLine_near_strip hδ x hx hstrip
  have hcenter : |a - δ * (j₀ : ℝ)| ≤ δ / 2 := lineGridRound_error hδ a
  have hsum : |δ * (j : ℝ) - δ * (j₀ : ℝ)| ≤ δ * (L : ℝ) := by
    have htri := (abs_sub_le (δ * (j : ℝ)) a (δ * (j₀ : ℝ))).trans
      (add_le_add hnear hcenter)
    exact htri.trans (by nlinarith)
  have habs : |(j : ℝ) - (j₀ : ℝ)| ≤ (L : ℝ) := by
    apply (mul_le_mul_iff_right₀ hδ).mp
    calc
      δ * |(j : ℝ) - (j₀ : ℝ)| = |δ * (j : ℝ) - δ * (j₀ : ℝ)| := by
        rw [← mul_sub, abs_mul, abs_of_pos hδ]
      _ ≤ δ * (L : ℝ) := hsum
  have hint : |j - j₀| ≤ (L : ℤ) := by exact_mod_cast habs
  have hbounds := abs_le.mp hint
  have hmem : round (a / δ) - (L : ℤ) ≤ j ∧ j ≤ round (a / δ) + (L : ℤ) := by
    change j₀ - (L : ℤ) ≤ j ∧ j ≤ j₀ + (L : ℤ)
    omega
  apply Finset.mem_image.mpr
  exact ⟨j, Finset.mem_Icc.mpr hmem, rfl⟩

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Estimates_TubeSecondMoment
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.sphereMeasure_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact finite incidence identities before the geometric common-tube bound. -/
namespace Falconer
open scoped BigOperators
attribute [local instance] Classical.propDecidable

theorem sum_tube_membership (U S : Finset (Space 2)) (hS : S ⊆ U) :
    (∑ l ∈ U, if l ∈ S then (1 : ℝ) else 0) = S.card := by
  rw [← Finset.sum_filter]
  have he : U.filter (fun l => l ∈ S) = S := by
    ext l
    simp only [Finset.mem_filter]
    exact and_iff_right_of_imp (fun hl => hS hl)
  rw [he]
  simp

theorem sum_tubeDegree (P : Finset (Space 2)) (T : Space 2 → Finset (Space 2)) :
    (∑ l ∈ P.biUnion T, tubeDegree P T l) = ∑ x ∈ P, ((T x).card : ℝ) := by
  unfold tubeDegree
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro x hx
  exact sum_tube_membership _ _ (Finset.subset_biUnion_of_mem T hx)

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Geometry_TwoPointTubeGeometry
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.sphereMeasure_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Two-point localization of actual bounded-chart tube parameters.
This is the elementary incidence kernel used in the multiscale Furstenberg proof. -/
namespace Falconer
open Set

theorem planar_dist_le_coordinate_sum (x y : Space 2) :
    dist x y ≤ |x 0-y 0| + |x 1-y 1| := by
  have he := EuclideanSpace.dist_sq_eq x y
  simp only [Fin.sum_univ_two, Real.dist_eq, sq_abs] at he
  nlinarith [dist_nonneg (x := x) (y := y), abs_nonneg (x 0-y 0),
    abs_nonneg (x 1-y 1), sq_abs (x 0-y 0), sq_abs (x 1-y 1),
    mul_nonneg (abs_nonneg (x 0-y 0)) (abs_nonneg (x 1-y 1))]

theorem tube_residual_le {δ : ℝ} (hδ : 0 ≤ δ) {x l : Space 2}
    (hl : |l 0| ≤ 1) (hi : TubeIncident δ x l) :
    |x 1-l 0*x 0-l 1| ≤ 2*δ := by
  have hs : 0 < Real.sqrt (1+(l 0)^2) := Real.sqrt_pos.2 (by positivity)
  have hs2 : Real.sqrt (1+(l 0)^2) ≤ 2 := by
    apply (Real.sqrt_le_left (by norm_num)).2
    have hsq := (sq_le_sq₀ (abs_nonneg (l 0)) zero_le_one).mpr hl
    nlinarith [sq_abs (l 0)]
  exact ((div_le_iff₀ hs).mp hi).trans (by nlinarith)

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Incidence_FiniteBallBounds
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.sphereMeasure_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Restriction and nonemptiness consequences for the normalized finite sets
appearing in the published planar incidence statement. -/
namespace Falconer
open Set
attribute [local instance] Classical.propDecidable

theorem normalized_finite_ball_bound_subset {δ s K C : ℝ}
    {P S : Finset (Space 2)} (hδ : 0 ≤ δ) (hK : 0 ≤ K)
    (hS : S ⊆ P) (hsize : (P.card : ℝ) ≤ C*(S.card : ℝ))
    (hball : NormalizedFiniteBallBound δ s K P) :
    NormalizedFiniteBallBound δ s (K*C) S := by
  intro z r hdr hr1
  have hsub : S.filter (fun x => dist x z ≤ r) ⊆ P.filter (fun x => dist x z ≤ r) := by
    intro x hx
    exact Finset.mem_filter.mpr ⟨hS (Finset.mem_filter.mp hx).1,(Finset.mem_filter.mp hx).2⟩
  calc
    _ ≤ ((P.filter (fun x => dist x z ≤ r)).card : ℝ) := by
      exact_mod_cast Finset.card_le_card hsub
    _ ≤ K*r^s*(P.card : ℝ) := hball z r hdr hr1
    _ ≤ K*r^s*(C*(S.card : ℝ)) :=
      mul_le_mul_of_nonneg_left hsize (mul_nonneg hK (Real.rpow_nonneg (hδ.trans hdr) _))
    _ = _ := by ring

theorem finiteSeparatedAt_subset {δ : ℝ} {P S : Finset (Space 2)}
    (hS : S ⊆ P) (hP : FiniteSeparatedAt δ P) : FiniteSeparatedAt δ S :=
  fun x hx y hy hxy => hP x (hS hx) y (hS hy) hxy

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Graphs_GraphBallCover
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Actual graph edges in a narrow Cartesian strip are covered by planar
balls. The count retains every neighbor, rather than only one witness. -/
namespace Falconer
attribute [local instance] Classical.propDecidable

 theorem rowPoint_dist_le_sum {x y z w R S : ℝ}
    (hR : 0 ≤ R) (hS : 0 ≤ S) (hx : |x-z| ≤ R) (hy : |y-w| ≤ S) :
    dist (rowPoint x y) (rowPoint z w) ≤ R+S := by
  have he := EuclideanSpace.dist_sq_eq (rowPoint x y) (rowPoint z w)
  simp only [Fin.sum_univ_two,rowPoint_zero,rowPoint_one,Real.dist_eq,sq_abs] at he
  have hx2 := mul_le_mul hx hx (abs_nonneg _) hR
  have hy2 := mul_le_mul hy hy (abs_nonneg _) hS
  nlinarith [sq_abs (x-z),sq_abs (y-w),mul_nonneg hR hS,
    dist_nonneg (x := rowPoint x y) (y := rowPoint z w)]

 theorem normalized_ball_bound_all_radii {δ t K : ℝ} {G : Finset (Space 2)}
    (ht : 0 ≤ t) (hK : 1 ≤ K) (hG : NormalizedFiniteBallBound δ t K G)
    (z : Space 2) (r : ℝ) (hr : δ ≤ r) :
    ((G.filter fun p => dist p z ≤ r).card:ℝ) ≤ K*r^t*(G.card:ℝ) := by
  by_cases hr1 : r ≤ 1
  · exact hG z r hr hr1
  · have hrpos : 1 ≤ r := le_of_lt (lt_of_not_ge hr1)
    have hp : 1 ≤ r^t := Real.one_le_rpow hrpos ht
    have hc : ((G.filter fun p => dist p z ≤ r).card:ℝ) ≤ (G.card:ℝ) :=
      Nat.cast_le.mpr (Finset.card_filter_le _ _)
    have hk : 1 ≤ K*r^t := by nlinarith
    exact hc.trans (by nlinarith [Nat.cast_nonneg (α := ℝ) G.card])

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Estimates_IncidentCoarseRounding
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Incident coarse pencils use a common grid. Their global union is
controlled by thirteen translates of the original coarse grid cover. -/
namespace Falconer
attribute [local instance] Classical.propDecidable

theorem moved_point_residual {δ Δ : ℝ} (hδ : 0 ≤ δ) (_hΔ : 0 < Δ) (hδΔ : δ ≤ Δ)
    (p c l : Space 2) (hc : dist p c ≤ Δ) (hl0 : |l 0| ≤ 1)
    (hi : TubeIncident δ p l) : |c 1-l 0*c 0-l 1| ≤ 4*Δ := by
  have hres := tube_residual_le hδ hl0 hi
  have h0 : |p 0-c 0| ≤ Δ := (show |p 0-c 0| ≤ dist p c by
    simpa only [Real.dist_eq] using PiLp.dist_apply_le p c 0).trans hc
  have h1 : |c 1-p 1| ≤ Δ := by
    rw [abs_sub_comm]
    exact (show |p 1-c 1| ≤ dist p c by simpa only [Real.dist_eq] using PiLp.dist_apply_le p c 1).trans hc
  have h2 : |l 0*(p 0-c 0)| ≤ Δ := by
    rw [abs_mul]
    exact (mul_le_mul hl0 h0 (abs_nonneg _) (by norm_num : (0:ℝ) ≤ 1)).trans_eq (one_mul _)
  calc
    _ = |(p 1-l 0*p 0-l 1)+(c 1-p 1)+l 0*(p 0-c 0)| := by congr 1; ring
    _ ≤ |(p 1-l 0*p 0-l 1)+(c 1-p 1)|+|l 0*(p 0-c 0)| := abs_add_le _ _
    _ ≤ (|p 1-l 0*p 0-l 1|+|c 1-p 1|)+|l 0*(p 0-c 0)| :=
      add_le_add (abs_add_le _ _) le_rfl
    _ ≤ (2*δ+Δ)+Δ := add_le_add (add_le_add hres h1) h2
    _ ≤ _ := by linarith only [hδΔ]

theorem rounded_incident_near_line {Δ : ℝ} (hΔ : 0 < Δ) (c l : Space 2)
    (hc0 : |c 0| ≤ 1) (hres : |c 1-l 0*c 0-l 1| ≤ 4*Δ) :
    dist l (roundedIncidentLine Δ c (l 0)) ≤ 6*Δ := by
  have hi := roundedIncidentLine_near_strip hΔ c hc0 hres
  have hh := planar_dist_le_coordinate_sum l (roundedIncidentLine Δ c (l 0))
  rw [roundedIncidentLine_fst,roundedIncidentLine_snd] at hh
  rw [abs_sub_comm (l 1)] at hh
  have he := lineGridRound_error hΔ (l 0)
  change |lineGridRound Δ (c 1-lineGridRound Δ (l 0)*c 0)-l 1| ≤ (4+1)*Δ at hi
  linarith only [hi,hh,he,hΔ]

theorem round_lineGridRound {Δ : ℝ} (hΔ : 0 < Δ) (a : ℝ) :
    round (lineGridRound Δ a/Δ) = round (a/Δ) := by
  unfold lineGridRound
  rw [mul_div_cancel_left₀ _ hΔ.ne',round_intCast]

theorem rounded_candidates_coarse {Δ : ℝ} (hΔ : 0 < Δ) (l : Space 2) (L : ℕ) :
    roundedStripCandidates Δ (l 0) (l 1) L =
      roundedStripCandidates Δ (coarsePlanarRound Δ l 0) (coarsePlanarRound Δ l 1) L := by
  simp only [roundedStripCandidates,coarsePlanarRound_zero,coarsePlanarRound_one,round_lineGridRound hΔ]

theorem incident_coarse_union_card {Δ : ℝ} (hΔ : 0 < Δ)
    (C : Finset (Space 2)) (T : Space 2 → Finset (Space 2))
    (hc : ∀ c ∈ C, |c 0| ≤ 1)
    (hres : ∀ c ∈ C, ∀ l ∈ T c, |c 1-l 0*c 0-l 1| ≤ 4*Δ) :
    ((C.biUnion fun c => (T c).image (fun l => roundedIncidentLine Δ c (l 0))).card:ℝ) ≤
      13*(((C.biUnion T).image (coarsePlanarRound Δ)).card:ℝ) := by
  have hh := labelled_line_union_card_le C
    (fun c => (T c).image (fun l => roundedIncidentLine Δ c (l 0)))
    ((C.biUnion T).image (coarsePlanarRound Δ))
    (fun b => roundedStripCandidates Δ (b 0) (b 1) 6)
    (L := 13) (by
      intro c hC a ha
      obtain ⟨l,hl,rfl⟩ := Finset.mem_image.mp ha
      refine ⟨coarsePlanarRound Δ l,
        Finset.mem_image_of_mem _ (Finset.mem_biUnion.mpr ⟨c,hC,hl⟩),?_⟩
      rw [← rounded_candidates_coarse hΔ]
      exact roundedIncidentLine_mem_candidates hΔ c (hc c hC) (hres c hC l hl) 6 (by norm_num)) (by
      intro b _
      exact_mod_cast roundedStripCandidates_card_le Δ (b 0) (b 1) 6)
  simpa only [mul_comm] using hh

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Estimates_WeightedDyadicRegularity
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.sphereMeasure_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Dyadic weight selection preserves regularity with a logarithmic loss.
This is used for coarse tubes weighted by original fine incidences. -/
namespace Falconer
open scoped BigOperators
attribute [local instance] Classical.propDecidable

theorem weighted_dyadic_regular_subset {δ s K : ℝ} (hδ : 0 ≤ δ) (hK : 0 ≤ K)
    (P : Finset (Space 2)) (w : Space 2 → ℕ) (hP : P.Nonempty) (M : ℕ)
    (hw : ∀ x ∈ P, 0 < w x ∧ w x ≤ M)
    (hball : ∀ z r, δ ≤ r → r ≤ 1 →
      (∑ x ∈ P.filter (fun x => dist x z ≤ r), (w x:ℝ)) ≤
        K*r^s*(∑ x ∈ P, (w x:ℝ))) :
    let J := Nat.log 2 M+1
    ∃ k : ℕ, ∃ S ⊆ P, S.Nonempty ∧
      (∑ x ∈ P, (w x:ℝ)) ≤ (J:ℝ)*(∑ x ∈ S, (w x:ℝ)) ∧
      (∀ x ∈ S, 2^k ≤ w x ∧ w x < 2^(k+1)) ∧
      NormalizedFiniteBallBound δ s (2*K*(J:ℝ)) S := by
  let J := Nat.log 2 M+1
  let f := fun x => Nat.log 2 (w x)
  let W := ∑ x ∈ P, (w x:ℝ)
  have hJ : 0 < (J:ℝ) := by dsimp [J]; positivity
  have hW : 0 < W := Finset.sum_pos (fun x hx => Nat.cast_pos.mpr (hw x hx).1) hP
  have hmap : ∀ x ∈ P, f x ∈ Finset.range J := by
    intro x hx
    exact Finset.mem_range.mpr (Nat.lt_succ_of_le (Nat.log_mono_right (hw x hx).2))
  have hdiv : (Finset.range J).card • (W/(J:ℝ)) ≤ W := by
    simp only [Finset.card_range,nsmul_eq_mul]
    rw [mul_div_cancel₀ _ hJ.ne']
  obtain ⟨k,_,hk⟩ := Finset.exists_le_sum_fiber_of_maps_to_of_nsmul_le_sum hmap
    (show (Finset.range J).Nonempty from ⟨0,Finset.mem_range.mpr (by dsimp [J]; omega)⟩) hdiv
  let S := P.filter fun x => f x = k
  have hSP : S ⊆ P := Finset.filter_subset _ _
  have hsum : W ≤ (J:ℝ)*(∑ x ∈ S, (w x:ℝ)) := by
    simpa only [mul_comm] using (div_le_iff₀ hJ).mp hk
  have hS : S.Nonempty := by
    by_contra hn
    rw [Finset.not_nonempty_iff_eq_empty.mp hn,Finset.sum_empty,mul_zero] at hsum
    exact hW.not_ge hsum
  have hband (x : Space 2) (hx : x ∈ S) : 2^k ≤ w x ∧ w x < 2^(k+1) := by
    obtain ⟨hxP,hxk⟩ := Finset.mem_filter.mp hx
    dsimp [f] at hxk
    rw [← hxk]
    exact ⟨Nat.pow_log_le_self 2 (hw x hxP).1.ne',Nat.lt_pow_succ_log_self (by norm_num) _⟩
  have ha : (0:ℝ) < (2:ℝ)^k := by positivity
  have hupper : (∑ x ∈ S, (w x:ℝ)) ≤ (2*(2:ℝ)^k)*(S.card:ℝ) := by
    calc
      _ ≤ ∑ _x ∈ S, 2*(2:ℝ)^k := Finset.sum_le_sum fun x hx => by
        have hh : (w x:ℝ) < (2:ℝ)^(k+1) := by exact_mod_cast (hband x hx).2
        simpa only [pow_succ,mul_comm] using hh.le
      _ = _ := by simp; ring
  refine ⟨k,S,hSP,hS,hsum,hband,?_⟩
  intro z r hr hr1
  have hr0 : 0 ≤ r := hδ.trans hr
  let F := S.filter fun x => dist x z ≤ r
  have hlo : (2:ℝ)^k*(F.card:ℝ) ≤ (∑ x ∈ F, (w x:ℝ)) := by
    calc
      _ = ∑ _x ∈ F, (2:ℝ)^k := by simp; ring
      _ ≤ _ := Finset.sum_le_sum fun x hx => by
        exact_mod_cast (hband x (Finset.mem_filter.mp hx).1).1
  have hsub : F ⊆ P.filter (fun x => dist x z ≤ r) := by
    intro x hx
    exact Finset.mem_filter.mpr ⟨hSP (Finset.mem_filter.mp hx).1,(Finset.mem_filter.mp hx).2⟩
  have hh : (2:ℝ)^k*(F.card:ℝ) ≤ (2:ℝ)^k*((2*K*(J:ℝ))*r^s*(S.card:ℝ)) := by
    calc
      _ ≤ ∑ x ∈ F, (w x:ℝ) := hlo
      _ ≤ ∑ x ∈ P.filter (fun x => dist x z ≤ r), (w x:ℝ) :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub (fun x _ _ => Nat.cast_nonneg _)
      _ ≤ K*r^s*W := hball z r hr hr1
      _ ≤ K*r^s*((J:ℝ)*(∑ x ∈ S, (w x:ℝ))) :=
        mul_le_mul_of_nonneg_left hsum (mul_nonneg hK (Real.rpow_nonneg hr0 _))
      _ ≤ K*r^s*((J:ℝ)*((2*(2:ℝ)^k)*(S.card:ℝ))) := by gcongr
      _ = _ := by ring
  exact (mul_le_mul_iff_right₀ ha).mp hh

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Incidence_CoarsePencilWeights
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Push original fine incidences to coarse line parameters, preserving their
multiplicities and the weighted ball bound. -/
namespace Falconer
open scoped BigOperators
attribute [local instance] Classical.propDecidable

theorem sum_coarsePencilWeight (P A : Finset (Space 2))
    (T : Space 2 → Finset (Space 2)) (q : Space 2 → Space 2) :
    (∑ a ∈ A, coarsePencilWeight P T q a) =
      ∑ x ∈ P, ((T x).filter fun l => q l ∈ A).card := by
  unfold coarsePencilWeight
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun x _ => Finset.sum_card_fiberwise_eq_card_filter (T x) A q

theorem sum_coarsePencilWeight_union (P : Finset (Space 2))
    (T : Space 2 → Finset (Space 2)) (q : Space 2 → Space 2) :
    (∑ a ∈ (P.biUnion T).image q, coarsePencilWeight P T q a) =
      ∑ x ∈ P, (T x).card := by
  rw [sum_coarsePencilWeight]
  apply Finset.sum_congr rfl
  intro x hx
  congr 1
  apply Finset.filter_eq_self.mpr
  intro l hl
  exact Finset.mem_image_of_mem q (Finset.mem_biUnion.mpr ⟨x,hx,hl⟩)

theorem coarsePencilWeight_pos (P : Finset (Space 2))
    (T : Space 2 → Finset (Space 2)) (q : Space 2 → Space 2)
    {a : Space 2} (ha : a ∈ (P.biUnion T).image q) :
    0 < coarsePencilWeight P T q a := by
  obtain ⟨l,hl,rfl⟩ := Finset.mem_image.mp ha
  obtain ⟨x,hx,hl⟩ := Finset.mem_biUnion.mp hl
  have hf : 0 < ((T x).filter fun z => q z = q l).card :=
    Finset.card_pos.mpr ⟨l,Finset.mem_filter.mpr ⟨hl,rfl⟩⟩
  unfold coarsePencilWeight
  exact hf.trans_le (Finset.single_le_sum
    (f := fun y => ((T y).filter fun z => q z = q l).card)
    (fun _ _ => Nat.zero_le _) hx)

theorem coarsePencilWeight_le (P : Finset (Space 2))
    (T : Space 2 → Finset (Space 2)) (q : Space 2 → Space 2) (a : Space 2) :
    coarsePencilWeight P T q a ≤ ∑ x ∈ P, (T x).card :=
  Finset.sum_le_sum fun _ _ => Finset.card_filter_le _ _

theorem coarse_pencil_weight_ball_mul {δ Δ s K C : ℝ}
    (hΔ : 0 < Δ) (hδΔ : δ ≤ Δ) (hs : 0 ≤ s) (hK : 1 ≤ K) (hC : 0 ≤ C)
    (P : Finset (Space 2)) (T : Space 2 → Finset (Space 2))
    (q : Space 2 → Space 2)
    (hnear : ∀ x ∈ P, ∀ l ∈ T x, dist l (q l) ≤ C*Δ)
    (hball : ∀ x ∈ P, NormalizedFiniteBallBound δ s K (T x)) :
    ∀ z r, Δ ≤ r → r ≤ 1 →
      (∑ a ∈ ((P.biUnion T).image q).filter (fun a => dist a z ≤ r),
        (coarsePencilWeight P T q a:ℝ)) ≤
      (K*(C+1)^s)*r^s*
        (∑ a ∈ (P.biUnion T).image q, (coarsePencilWeight P T q a:ℝ)) := by
  intro z r hr _
  have hr0 : 0 < r := hΔ.trans_le hr
  have he (A : Finset (Space 2)) : (∑ a ∈ A, (coarsePencilWeight P T q a:ℝ)) =
      ∑ x ∈ P, (((T x).filter fun l => q l ∈ A).card:ℝ) := by
    exact_mod_cast sum_coarsePencilWeight P A T q
  have htotal : (∑ a ∈ (P.biUnion T).image q, (coarsePencilWeight P T q a:ℝ)) =
      ∑ x ∈ P, ((T x).card:ℝ) := by
    exact_mod_cast sum_coarsePencilWeight_union P T q
  rw [he,htotal]
  calc
    _ ≤ ∑ x ∈ P, K*((C+1)*r)^s*((T x).card:ℝ) := by
      apply Finset.sum_le_sum
      intro x hx
      have hsub : (T x).filter (fun l => q l ∈ ((P.biUnion T).image q).filter
          (fun a => dist a z ≤ r)) ⊆ (T x).filter (fun l => dist l z ≤ (C+1)*r) := by
        intro l hl
        obtain ⟨hlT,hlq⟩ := Finset.mem_filter.mp hl
        have hqr := (Finset.mem_filter.mp hlq).2
        exact Finset.mem_filter.mpr ⟨hlT,(dist_triangle l (q l) z).trans
          ((add_le_add (hnear x hx l hlT) hqr).trans (by nlinarith only [hr,hC]))⟩
      exact (Nat.cast_le.mpr (Finset.card_le_card hsub)).trans
        (normalized_ball_bound_all_radii hs hK (hball x hx) z ((C+1)*r)
          (hδΔ.trans (by nlinarith only [hr,hΔ,hC])))
    _ = _ := by rw [← Finset.mul_sum,Real.mul_rpow (by linarith : (0:ℝ) ≤ C+1) hr0.le]; ring

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Incidence_CoarsePacketPoints
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Extract many original points that retain many fine tubes in one coarse
packet. Both losses follow from the actual incidence count. -/
namespace Falconer
open scoped BigOperators
attribute [local instance] Classical.propDecidable

theorem finite_large_weight_subset (P : Finset (Space 2)) (w : Space 2 → ℝ)
    {H B : ℝ} (hP : P.Nonempty) (hH : 0 < H) (hB : 0 < B)
    (hcap : ∀ x ∈ P, w x ≤ B) (hsum : H ≤ ∑ x ∈ P, w x) :
    ∃ A ⊆ P, A.Nonempty ∧ H/(2*B) ≤ (A.card:ℝ) ∧
      ∀ x ∈ A, H/(2*(P.card:ℝ)) ≤ w x := by
  let c := H/(2*(P.card:ℝ))
  let A := P.filter fun x => c ≤ w x
  have hPc : 0 < (P.card:ℝ) := Nat.cast_pos.mpr hP.card_pos
  have hc : 0 < c := by dsimp [c]; positivity
  have hbound (x : Space 2) (hx : x ∈ P) :
      w x ≤ (if c ≤ w x then B else 0)+c := by
    by_cases h : c ≤ w x
    · rw [ite_eq_left h]
      exact (hcap x hx).trans (le_add_of_nonneg_right hc.le)
    · rw [ite_eq_right h,zero_add]
      exact (lt_of_not_ge h).le
  have htotal : H ≤ B*(A.card:ℝ)+H/2 := by
    calc
      _ ≤ ∑ x ∈ P, w x := hsum
      _ ≤ ∑ x ∈ P, ((if c ≤ w x then B else 0)+c) := Finset.sum_le_sum hbound
      _ = B*(A.card:ℝ)+H/2 := by
        rw [Finset.sum_add_distrib,← Finset.sum_filter]
        simp only [Finset.sum_const,nsmul_eq_mul]
        dsimp [A,c]
        field_simp
  have hsize : H/(2*B) ≤ (A.card:ℝ) := (div_le_iff₀ (by positivity)).2 (by linarith only [htotal])
  have hAc : 0 < (A.card:ℝ) := (div_pos hH (by positivity)).trans_le hsize
  exact ⟨A,Finset.filter_subset _ _,Finset.card_pos.mp (Nat.cast_pos.mp hAc),hsize,
    fun x hx => (Finset.mem_filter.mp hx).2⟩

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Incidence_PencilEnergyPruning
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Discard high-energy tubes while preserving a positive fraction of every
retained cell's pencil. All energy and incidence budgets are explicit. -/
namespace Falconer
open scoped BigOperators
attribute [local instance] Classical.propDecidable

theorem sum_pencil_intersection (P B : Finset (Space 2))
    (T : Space 2 → Finset (Space 2)) :
    (∑ x ∈ P, ((T x ∩ B).card:ℝ)) = ∑ l ∈ B, tubeDegree P T l := by
  unfold tubeDegree
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro x _
  rw [← Finset.sum_filter]
  simp only [Finset.sum_const,nsmul_eq_mul,mul_one]
  congr 2
  ext l
  simp only [Finset.mem_inter,Finset.mem_filter,and_comm]

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Incidence_FrozenPacketSelection
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Freeze fine-packet cardinalities by weighting the dyadic selection with
actual coarse incidences, then retain cells with large coarse pencils. -/
namespace Falconer
open scoped BigOperators
attribute [local instance] Classical.propDecidable

theorem weighted_dyadic_size_band (P : Finset (Space 2))
    (b : Space 2 → ℕ) (w : Space 2 → ℝ) (M : ℕ)
    (hb : ∀ x ∈ P, 0 < b x ∧ b x ≤ M)
    (hW : 0 < ∑ x ∈ P, w x) :
    let J := Nat.log 2 M+1
    ∃ k : ℕ, ∃ B ⊆ P, B.Nonempty ∧
      (∑ x ∈ P, w x) ≤ (J:ℝ)*(∑ x ∈ B, w x) ∧
      ∀ x ∈ B, 2^k ≤ b x ∧ b x < 2^(k+1) := by
  let J := Nat.log 2 M+1
  let f := fun x => Nat.log 2 (b x)
  let W := ∑ x ∈ P, w x
  have hJ : 0 < (J:ℝ) := by dsimp [J]; positivity
  have hmap : ∀ x ∈ P, f x ∈ Finset.range J := fun x hx =>
    Finset.mem_range.mpr (Nat.lt_succ_of_le (Nat.log_mono_right (hb x hx).2))
  have hdiv : (Finset.range J).card • (W/(J:ℝ)) ≤ W := by
    simp only [Finset.card_range,nsmul_eq_mul]
    rw [mul_div_cancel₀ _ hJ.ne']
  obtain ⟨k,_,hk⟩ := Finset.exists_le_sum_fiber_of_maps_to_of_nsmul_le_sum hmap
    (show (Finset.range J).Nonempty from ⟨0,Finset.mem_range.mpr (by dsimp [J]; omega)⟩) hdiv
  let B := P.filter fun x => f x = k
  have hsum : W ≤ (J:ℝ)*(∑ x ∈ B, w x) := by
    simpa only [mul_comm] using (div_le_iff₀ hJ).mp hk
  have hB : B.Nonempty := by
    by_contra hn
    rw [Finset.not_nonempty_iff_eq_empty.mp hn,Finset.sum_empty,mul_zero] at hsum
    exact hW.not_ge hsum
  refine ⟨k,B,Finset.filter_subset _ _,hB,hsum,?_⟩
  intro x hx
  obtain ⟨hxP,hxk⟩ := Finset.mem_filter.mp hx
  dsimp [f] at hxk
  rw [← hxk]
  exact ⟨Nat.pow_log_le_self 2 (hb x hxP).1.ne',Nat.lt_pow_succ_log_self (by norm_num) _⟩

theorem freeze_coarse_packet_sizes (P : Finset (Space 2))
    (T : Space 2 → Finset (Space 2)) (b : Space 2 → ℕ) (D : ℕ)
    {m M : ℝ} (hP : P.Nonempty) (hm : 0 < m) (hM : 0 < M)
    (hcard : ∀ x ∈ P, m ≤ ((T x).card:ℝ) ∧ ((T x).card:ℝ) ≤ M)
    (hb : ∀ l ∈ P.biUnion T, 0 < b l ∧ b l ≤ D) :
    let J := Nat.log 2 D+1
    ∃ k : ℕ, ∃ B ⊆ P.biUnion T, B.Nonempty ∧
      (∀ l ∈ B, 2^k ≤ b l ∧ b l < 2^(k+1)) ∧
      ∃ R ⊆ P, R.Nonempty ∧ m*(P.card:ℝ)/(2*(J:ℝ)*M) ≤ (R.card:ℝ) ∧
        ∀ x ∈ R, m/(2*(J:ℝ)) ≤ ((T x ∩ B).card:ℝ) := by
  let J := Nat.log 2 D+1
  have hJ : 0 < (J:ℝ) := by dsimp [J]; positivity
  have hPc : 0 < (P.card:ℝ) := Nat.cast_pos.mpr hP.card_pos
  have hI : m*(P.card:ℝ) ≤ ∑ l ∈ P.biUnion T, tubeDegree P T l := by
    rw [sum_tubeDegree]
    calc
      _ = ∑ _x ∈ P, m := by simp; ring
      _ ≤ _ := Finset.sum_le_sum fun x hx => (hcard x hx).1
  obtain ⟨k,B,hBU,hB,hmass,hband⟩ := weighted_dyadic_size_band (P.biUnion T) b
    (tubeDegree P T) D hb ((mul_pos hm hPc).trans_le hI)
  have hretained : m*(P.card:ℝ)/(J:ℝ) ≤ ∑ x ∈ P, ((T x ∩ B).card:ℝ) := by
    rw [sum_pencil_intersection]
    apply (div_le_iff₀ hJ).2
    simpa only [mul_comm] using hI.trans hmass
  obtain ⟨R,hRP,hR,hsize,hlarge⟩ := finite_large_weight_subset P
    (fun x => ((T x ∩ B).card:ℝ)) hP (div_pos (mul_pos hm hPc) hJ) hM
    (fun x hx => (Nat.cast_le.mpr (Finset.card_le_card Finset.inter_subset_left)).trans
      (hcard x hx).2) hretained
  refine ⟨k,B,hBU,hB,hband,R,hRP,hR,?_,?_⟩
  · convert hsize using 1
    all_goals try with_reducible_and_instances rfl
    dsimp [J]
    field_simp
  · intro x hx
    have hh := hlarge x hx
    convert hh using 1
    all_goals try with_reducible_and_instances rfl
    dsimp [J]
    field_simp

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Estimates_FinePacketCounts
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Original fine tubes have bounded multiplicity among cell-dependent
coarse packets. Thus freezing packet sizes preserves the needed total bound. -/
namespace Falconer
open scoped BigOperators
attribute [local instance] Classical.propDecidable

theorem fineCoarsePacket_nonempty {Δ : ℝ} (C : Finset (Space 2))
    (T : Space 2 → Finset (Space 2)) {a : Space 2}
    (ha : a ∈ C.biUnion fun c => (T c).image (fun l => roundedIncidentLine Δ c (l 0))) :
    (fineCoarsePacket Δ C T a).Nonempty := by
  obtain ⟨c,hc,ha⟩ := Finset.mem_biUnion.mp ha
  obtain ⟨l,hl,he⟩ := Finset.mem_image.mp ha
  exact ⟨l,Finset.mem_filter.mpr ⟨Finset.mem_biUnion.mpr ⟨c,hc,hl⟩,c,hc,hl,he⟩⟩

theorem fineCoarsePacket_card_le (Δ : ℝ) (C : Finset (Space 2))
    (T : Space 2 → Finset (Space 2)) (a : Space 2) :
    (fineCoarsePacket Δ C T a).card ≤ (C.biUnion T).card :=
  Finset.card_filter_le _ _

theorem sum_fineCoarsePacket_card {Δ : ℝ} (hΔ : 0 < Δ)
    (C : Finset (Space 2)) (T : Space 2 → Finset (Space 2))
    (hc : ∀ c ∈ C, |c 0| ≤ 1)
    (hres : ∀ c ∈ C, ∀ l ∈ T c, |c 1-l 0*c 0-l 1| ≤ 4*Δ) :
    (∑ a ∈ C.biUnion (fun c => (T c).image (fun l => roundedIncidentLine Δ c (l 0))),
      (fineCoarsePacket Δ C T a).card) ≤ 13*(C.biUnion T).card := by
  let V := C.biUnion fun c => (T c).image (fun l => roundedIncidentLine Δ c (l 0))
  have hswap : (∑ a ∈ V, (fineCoarsePacket Δ C T a).card) =
      ∑ l ∈ C.biUnion T, (V.filter fun a =>
        ∃ c ∈ C, l ∈ T c ∧ roundedIncidentLine Δ c (l 0) = a).card := by
    simp only [fineCoarsePacket,Finset.card_eq_sum_ones,Finset.sum_filter]
    rw [Finset.sum_comm]
  rw [hswap]
  calc
    _ ≤ ∑ _l ∈ C.biUnion T, 13 := by
      apply Finset.sum_le_sum
      intro l _
      have hsub : (V.filter fun a => ∃ c ∈ C, l ∈ T c ∧
          roundedIncidentLine Δ c (l 0) = a) ⊆ roundedStripCandidates Δ (l 0) (l 1) 6 := by
        intro a ha
        obtain ⟨_,c,hcC,hl,he⟩ := Finset.mem_filter.mp ha
        rw [← he]
        exact roundedIncidentLine_mem_candidates hΔ c (hc c hcC) (hres c hcC l hl) 6 (by norm_num)
      exact (Finset.card_le_card hsub).trans (roundedStripCandidates_card_le Δ (l 0) (l 1) 6)
    _ = _ := by simp; omega

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Incidence_RegularCoarsePencils
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A regular coarse pencil with a lower fine-incidence count in every
retained coarse tube, obtained directly from the original fine pencils. -/
namespace Falconer
open scoped BigOperators
attribute [local instance] Classical.propDecidable

theorem regular_coarse_pencil_mul {δ Δ s K C : ℝ}
    (hΔ : 0 < Δ) (hδΔ : δ ≤ Δ) (hs : 0 ≤ s) (hK : 1 ≤ K) (hC : 0 ≤ C)
    (P : Finset (Space 2)) (T : Space 2 → Finset (Space 2)) (hP : P.Nonempty)
    (hT : ∀ x ∈ P, (T x).Nonempty)
    (q : Space 2 → Space 2)
    (hnear : ∀ x ∈ P, ∀ l ∈ T x, dist l (q l) ≤ C*Δ)
    (hball : ∀ x ∈ P, NormalizedFiniteBallBound δ s K (T x)) :
    let W := ∑ x ∈ P, (T x).card
    let J := Nat.log 2 W+1
    ∃ A ⊆ (P.biUnion T).image q, A.Nonempty ∧
      NormalizedFiniteBallBound Δ s (2*(K*(C+1)^s)*(J:ℝ)) A ∧
      ∀ a ∈ A, (W:ℝ) ≤ 2*(J:ℝ)*(A.card:ℝ)*(coarsePencilWeight P T q a:ℝ) := by
  let W := ∑ x ∈ P, (T x).card
  let J := Nat.log 2 W+1
  let V := (P.biUnion T).image q
  have hV : V.Nonempty := by
    obtain ⟨x,hx⟩ := hP
    obtain ⟨l,hl⟩ := hT x hx
    exact ⟨q l,Finset.mem_image_of_mem q (Finset.mem_biUnion.mpr ⟨x,hx,hl⟩)⟩
  have hW : ∑ a ∈ V, (coarsePencilWeight P T q a:ℝ) = (W:ℝ) := by
    exact_mod_cast sum_coarsePencilWeight_union P T q
  obtain ⟨k,A,hAV,hA,hweight,hband,hreg⟩ := weighted_dyadic_regular_subset hΔ.le
    (show 0 ≤ K*(C+1)^s by positivity) V (coarsePencilWeight P T q) hV W
    (fun a ha => ⟨coarsePencilWeight_pos P T q ha,coarsePencilWeight_le P T q a⟩)
    (coarse_pencil_weight_ball_mul hΔ hδΔ hs hK hC P T q hnear hball)
  refine ⟨A,hAV,hA,hreg,?_⟩
  intro a ha
  have hmass : (W:ℝ) ≤ (J:ℝ)*(∑ b ∈ A, (coarsePencilWeight P T q b:ℝ)) := by
    rwa [hW] at hweight
  have hbound : (∑ b ∈ A, (coarsePencilWeight P T q b:ℝ)) ≤
      2*(coarsePencilWeight P T q a:ℝ)*(A.card:ℝ) := by
    calc
      _ ≤ ∑ _b ∈ A, 2*(coarsePencilWeight P T q a:ℝ) := by
        apply Finset.sum_le_sum
        intro b hb
        have hab : coarsePencilWeight P T q b ≤ 2*coarsePencilWeight P T q a := by
          have hlo := (hband a ha).1
          have hhi := (hband b hb).2
          rw [pow_succ] at hhi
          omega
        exact_mod_cast hab
      _ = _ := by simp; ring
  calc
    _ ≤ (J:ℝ)*(∑ b ∈ A, (coarsePencilWeight P T q b:ℝ)) := hmass
    _ ≤ (J:ℝ)*(2*(coarsePencilWeight P T q a:ℝ)*(A.card:ℝ)) :=
      mul_le_mul_of_nonneg_left hbound (Nat.cast_nonneg _)
    _ = _ := by ring

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Estimates_PacketRepresentativeBand
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A weighted image can be thinned to representatives with comparable
numbers of original witnesses, retaining both regularity and total mass. -/
namespace Falconer
open scoped BigOperators
attribute [local instance] Classical.propDecidable

theorem packet_representative_band {δ ρ s K C : ℝ}
    (hρ : 0 < ρ) (hδρ : δ ≤ ρ) (hs : 0 ≤ s) (hK : 1 ≤ K) (hC : 0 ≤ C)
    (T : Finset (Space 2)) (hT : T.Nonempty) (q : Space 2 → Space 2)
    (hnear : ∀ l ∈ T, dist l (q l) ≤ C*ρ)
    (hball : NormalizedFiniteBallBound δ s K T) (D : ℕ) (hD : T.card ≤ D) :
    let J := Nat.log 2 D+1
    ∃ k : ℕ, k < J ∧ ∃ A ⊆ T.image q, A.Nonempty ∧
      NormalizedFiniteBallBound ρ s (2*(K*(C+1)^s)*(J:ℝ)) A ∧
      (T.card:ℝ) ≤ (J:ℝ)*(∑ a ∈ A, (((T.filter fun l => q l = a).card):ℝ)) ∧
      ∀ a ∈ A, 2^k ≤ (T.filter fun l => q l = a).card ∧
        (T.filter fun l => q l = a).card < 2^(k+1) := by
  let w := fun a => (T.filter fun l => q l = a).card
  have htotal : (∑ a ∈ T.image q, (w a:ℝ)) = (T.card:ℝ) := by
    exact_mod_cast Finset.sum_card_fiberwise_eq_card_filter T (T.image q) q |>.trans (by
      congr 1
      exact Finset.filter_eq_self.mpr fun l hl => Finset.mem_image_of_mem q hl)
  have hwb : ∀ a ∈ T.image q, 0 < w a ∧ w a ≤ D := by
    intro a ha
    obtain ⟨l,hl,rfl⟩ := Finset.mem_image.mp ha
    exact ⟨Finset.card_pos.mpr ⟨l,Finset.mem_filter.mpr ⟨hl,rfl⟩⟩,
      (Finset.card_filter_le _ _).trans hD⟩
  have hwr : ∀ z r, ρ ≤ r → r ≤ 1 →
      (∑ a ∈ (T.image q).filter (fun a => dist a z ≤ r), (w a:ℝ)) ≤
        (K*(C+1)^s)*r^s*(∑ a ∈ T.image q, (w a:ℝ)) := by
    have hh := coarse_pencil_weight_ball_mul hρ hδρ hs hK hC
      {0} (fun _ => T) q (fun _ _ l hl => hnear l hl) (fun _ _ => hball)
    simpa only [Finset.singleton_biUnion,coarsePencilWeight,Finset.sum_singleton] using hh
  obtain ⟨k,A,hA,hne,hweight,hband,hreg⟩ := weighted_dyadic_regular_subset hρ.le
    (by positivity : 0 ≤ K*(C+1)^s) (T.image q) w (hT.image q) D hwb hwr
  refine ⟨k,?_,A,hA,hne,hreg,?_,hband⟩
  · obtain ⟨a,ha⟩ := hne
    exact Nat.lt_succ_of_le (Nat.le_log_of_pow_le (by norm_num) ((hband a ha).1.trans (hwb a (hA ha)).2))
  · rwa [htotal] at hweight

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Angular_LocalDirectionPackets
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Comparable original packets give separated local pencils. The total
number of representatives is controlled by the original tube union. -/
namespace Falconer
open scoped BigOperators
attribute [local instance] Classical.propDecidable

theorem local_direction_packet_refinement {δ ρ s K : ℝ}
    (hρ : 0 < ρ) (hρ1 : ρ ≤ 1/2) (hδρ : δ ≤ ρ) (hs : 0 ≤ s) (hK : 1 ≤ K)
    (P : Finset (Space 2)) (T : Space 2 → Finset (Space 2)) (hP : P.Nonempty)
    (hPsmall : ∀ p ∈ P, |p 0| ≤ 1/4 ∧ |p 1| ≤ 1/4)
    (hT : ∀ p ∈ P, (T p).Nonempty ∧ NormalizedFiniteBallBound δ s K (T p) ∧
      ∀ l ∈ T p, |l 0| ≤ 1/2 ∧ TubeIncident ρ p l)
    (D : ℕ) (hD : ∀ p ∈ P, (T p).card ≤ D) :
    let J := Nat.log 2 D+1
    let q := fun p l : Space 2 => roundedIncidentLine ρ p (l 0)
    ∃ k : ℕ, ∃ R ⊆ P, R.Nonempty ∧ (P.card:ℝ) ≤ (J:ℝ)*(R.card:ℝ) ∧
      ∃ U : Space 2 → Finset (Space 2),
        (∀ p ∈ R, U p ⊆ (T p).image (q p) ∧ (U p).Nonempty ∧
          InBoundedLineChart (U p) ∧ FiniteSeparatedAt ρ (U p) ∧
          NormalizedFiniteBallBound ρ s (2*(K*7^s)*(J:ℝ)) (U p) ∧
          (∀ a ∈ U p, TubeIncident ρ p a) ∧
          (T p).card ≤ J*((T p).filter fun l => q p l ∈ U p).card ∧
          (T p).card ≤ J*(2*2^k)*(U p).card ∧
          2^k*(U p).card ≤ (T p).card ∧
          ∀ a ∈ U p, 2^k ≤ ((T p).filter fun l => q p l = a).card ∧
            ((T p).filter fun l => q p l = a).card < 2^(k+1)) ∧
        (2:ℝ)^k*((R.biUnion U).card:ℝ) ≤ 13*((P.biUnion T).card:ℝ) := by
  let J := Nat.log 2 D+1
  let q := fun p l : Space 2 => roundedIncidentLine ρ p (l 0)
  have hJ : 0 < (J:ℝ) := by dsimp [J]; positivity
  have hlocal (p : Space 2) (hp : p ∈ P) :
      ∃ k : ℕ, k < J ∧ ∃ A ⊆ (T p).image (q p), A.Nonempty ∧
        NormalizedFiniteBallBound ρ s (2*(K*7^s)*(J:ℝ)) A ∧
        ((T p).card:ℝ) ≤ (J:ℝ)*(∑ a ∈ A, (((T p).filter fun l => q p l = a).card:ℝ)) ∧
        ∀ a ∈ A, 2^k ≤ ((T p).filter fun l => q p l = a).card ∧
          ((T p).filter fun l => q p l = a).card < 2^(k+1) := by
    have hn : ∀ l ∈ T p, dist l (q p l) ≤ 6*ρ := by
      intro l hl
      have ht := (hT p hp).2.2 l hl
      apply rounded_incident_near_line hρ p l ((hPsmall p hp).1.trans (by norm_num))
      exact (tube_residual_le hρ.le (ht.1.trans (by norm_num)) ht.2).trans (by linarith)
    simpa only [show (6:ℝ)+1=7 by norm_num] using
      packet_representative_band hρ hδρ hs hK (C := 6) (by norm_num)
        (T p) (hT p hp).1 (q p) hn (hT p hp).2.1 D (hD p hp)
  let level := fun p => if hp : p ∈ P then (hlocal p hp).choose else 0
  let U := fun p => if hp : p ∈ P then ((hlocal p hp).choose_spec.2).choose else ∅
  have hlevel (p : Space 2) (hp : p ∈ P) : level p < J := by
    simpa only [level,dite_eq_left hp] using (hlocal p hp).choose_spec.1
  have hdata (p : Space 2) (hp : p ∈ P) : U p ⊆ (T p).image (q p) ∧ (U p).Nonempty ∧
      NormalizedFiniteBallBound ρ s (2*(K*7^s)*(J:ℝ)) (U p) ∧
      ((T p).card:ℝ) ≤ (J:ℝ)*(∑ a ∈ U p, (((T p).filter fun l => q p l = a).card:ℝ)) ∧
      ∀ a ∈ U p, 2^(level p) ≤ ((T p).filter fun l => q p l = a).card ∧
        ((T p).filter fun l => q p l = a).card < 2^(level p+1) := by
    simpa only [level,U,dite_eq_left hp] using ((hlocal p hp).choose_spec.2).choose_spec
  have hmap : ∀ p ∈ P, level p ∈ Finset.range J := fun p hp => Finset.mem_range.mpr (hlevel p hp)
  have hdiv : (Finset.range J).card • ((P.card:ℝ)/(J:ℝ)) ≤ (P.card:ℝ) := by
    simp only [Finset.card_range,nsmul_eq_mul]
    rw [mul_div_cancel₀ _ hJ.ne']
  obtain ⟨k,_,hk⟩ := Finset.exists_le_card_fiber_of_nsmul_le_card_of_maps_to
    (M := ℝ) hmap (show (Finset.range J).Nonempty from ⟨0,Finset.mem_range.mpr (by dsimp [J]; omega)⟩) hdiv
  let R := P.filter fun p => level p = k
  have hRP : R ⊆ P := Finset.filter_subset _ _
  have hR : R.Nonempty := by
    apply Finset.card_pos.mp
    exact Nat.cast_pos.mp ((div_pos (Nat.cast_pos.mpr hP.card_pos) hJ).trans_le hk)
  have hmass : (P.card:ℝ) ≤ (J:ℝ)*(R.card:ℝ) := by
    simpa only [mul_comm] using (div_le_iff₀ hJ).mp hk
  have hband (p : Space 2) (hp : p ∈ R) (a : Space 2) (ha : a ∈ U p) :
      2^k ≤ ((T p).filter fun l => q p l = a).card ∧
        ((T p).filter fun l => q p l = a).card < 2^(k+1) := by
    simpa only [(Finset.mem_filter.mp hp).2] using (hdata p (hRP hp)).2.2.2.2 a ha
  have hUsub : R.biUnion U ⊆ P.biUnion (fun p => (T p).image (q p)) := by
    intro a ha
    obtain ⟨p,hp,ha⟩ := Finset.mem_biUnion.mp ha
    exact Finset.mem_biUnion.mpr ⟨p,hRP hp,(hdata p (hRP hp)).1 ha⟩
  refine ⟨k,R,hRP,hR,hmass,U,?_,?_⟩
  · intro p hp
    obtain ⟨hsub,hne,hreg,hweight,_⟩ := hdata p (hRP hp)
    have hsum : (∑ a ∈ U p, ((T p).filter fun l => q p l = a).card) =
        ((T p).filter fun l => q p l ∈ U p).card :=
      Finset.sum_card_fiberwise_eq_card_filter _ _ _
    have hw : (T p).card ≤ J*(∑ a ∈ U p, ((T p).filter fun l => q p l = a).card) := by
      exact_mod_cast hweight
    refine ⟨hsub,hne,?_,?_,hreg,?_,by rwa [hsum] at hw,?_,?_,hband p hp⟩
    · intro a ha
      obtain ⟨l,hl,rfl⟩ := Finset.mem_image.mp (hsub ha)
      exact roundedIncidentLine_in_chart hρ hρ1 p (hPsmall p (hRP hp)).1
        (hPsmall p (hRP hp)).2 (l 0) ((hT p (hRP hp)).2.2 l hl).1
    · exact finiteSeparatedAt_subset hsub (roundedIncidentLine_family_separated hρ p
        (fun l : Space 2 => l 0) (T p))
    · intro a ha
      obtain ⟨l,_,rfl⟩ := Finset.mem_image.mp (hsub ha)
      exact roundedIncidentLine_incident hρ p (l 0)
    · apply hw.trans
      rw [Nat.mul_assoc]
      apply Nat.mul_le_mul_left
      calc
        _ ≤ ∑ _a ∈ U p, 2*2^k := Finset.sum_le_sum fun a ha => by
          have hh := (hband p hp a ha).2
          rw [pow_succ] at hh
          omega
        _ = _ := by simp; ring
    · calc
        _ = ∑ _a ∈ U p, 2^k := by simp; ring
        _ ≤ ∑ a ∈ U p, ((T p).filter fun l => q p l = a).card :=
          Finset.sum_le_sum fun a ha => (hband p hp a ha).1
        _ = _ := hsum
        _ ≤ _ := Finset.card_filter_le _ _
  · have hlower : 2^k*(R.biUnion U).card ≤
        ∑ a ∈ R.biUnion U, (fineCoarsePacket ρ P T a).card := by
      calc
        _ = ∑ _a ∈ R.biUnion U, 2^k := by simp; ring
        _ ≤ _ := by
          apply Finset.sum_le_sum
          intro a ha
          obtain ⟨p,hp,ha⟩ := Finset.mem_biUnion.mp ha
          apply ((hband p hp a ha).1).trans
          apply Finset.card_le_card
          intro l hl
          obtain ⟨hl,he⟩ := Finset.mem_filter.mp hl
          exact Finset.mem_filter.mpr ⟨Finset.mem_biUnion.mpr ⟨p,hRP hp,hl⟩,p,hRP hp,hl,he⟩
    have hres : ∀ p ∈ P, ∀ l ∈ T p, |p 1-l 0*p 0-l 1| ≤ 4*ρ := by
      intro p hp l hl
      have ht := (hT p hp).2.2 l hl
      exact (tube_residual_le hρ.le (ht.1.trans (by norm_num)) ht.2).trans (by linarith)
    have htotal := sum_fineCoarsePacket_card hρ P T
      (fun p hp => (hPsmall p hp).1.trans (by norm_num)) hres
    have hh := hlower.trans ((Finset.sum_le_sum_of_subset_of_nonneg hUsub
      (fun _ _ _ => Nat.zero_le _)).trans htotal)
    exact_mod_cast hh

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Estimates_DyadicTree
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Finite dyadic trees in the original ambient dimension

All descendants use half-open carriers. Equal-depth cells are disjoint and
partition the parent, so restriction to them is an exact measure splitting.
-/

namespace Falconer
open Set MeasureTheory
attribute [local instance] Classical.propDecidable

theorem card_cubePaths (d n : ℕ) : (cubePaths d n).card = 2^(d*n) := by
  induction n with
  | zero => simp [cubePaths]
  | succ n ih =>
    rw [cubePaths, Finset.card_biUnion]
    · have hc (b : Fin d → Bool) : Function.Injective (List.cons b) :=
        fun _ _ h => (List.cons.inj h).2
      simp only [Finset.card_image_of_injective _ (hc _), ih,
        Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_bool,
        Fintype.card_fin, smul_eq_mul]
      rw [Nat.mul_succ, pow_add]
      exact Nat.mul_comm _ _
    · intro b _ c _ hbc
      apply Finset.disjoint_left.mpr
      intro p hp hq
      obtain ⟨p', _, hp'⟩ := Finset.mem_image.mp hp
      obtain ⟨q', _, hq'⟩ := Finset.mem_image.mp hq
      exact hbc (List.cons.inj (hp'.trans hq'.symm)).1

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Estimates_AllDimensionalRegularizationLabels
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Upward regularization labels in arbitrary dimension

The label-preservation argument applies to all-dimensional dyadic paths.
Each extension retains or removes a whole previous child group.
-/

namespace Falconer.Regularization

variable {d : ℕ}

theorem labeledChildren_eq {L : Finset (CellPath d)} {f : CellPath d → List ℕ}
    {a b : ℕ} {p q : CellPath d} (ha : p.take a = q.take a) (hf : f p = f q) :
    labeledChildren L f a b p = labeledChildren L f a b q := by
  classical
  simp only [labeledChildren, ha, hf]

theorem labeledChildren_nonempty {L : Finset (CellPath d)} (f : CellPath d → List ℕ)
    (a b : ℕ) {p : CellPath d} (hp : p ∈ L) :
    (labeledChildren L f a b p).Nonempty := by
  classical
  exact Finset.image_nonempty.mpr ⟨p, by simp [hp]⟩

theorem extendLabel_old {L : Finset (CellPath d)} {f : CellPath d → List ℕ}
    {a b : ℕ} {p q : CellPath d} (h : extendLabel L a b f p = extendLabel L a b f q) :
    f p = f q := (List.cons.inj h).2

theorem extendLabel_local {L : Finset (CellPath d)} {f : CellPath d → List ℕ}
    {a b : ℕ} {p q : CellPath d} (ha : p.take a = q.take a) :
    extendLabel L a b f p = extendLabel L a b f q ↔ f p = f q := by
  constructor
  · exact extendLabel_old
  · intro hf
    simp only [extendLabel, labeledChildren_eq ha hf, hf]

end Falconer.Regularization

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Estimates_AllDimensionalRegularizationCardinality
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Dimension-dependent counts for regularization labels

A selected-depth gap of length b-a has at most 2^(d*(b-a))
children, so its logarithmic count bin has d*(b-a)+1 possibilities.
The number of final labels is polynomial in terminal depth when the
number of selected blocks is fixed.
-/

namespace Falconer.Regularization
variable {d : ℕ}

theorem labeledChildren_subset_extensions {N a b : ℕ} (hab : a ≤ b) (hbN : b ≤ N)
    {L : Finset (CellPath d)} (hL : L ⊆ cubePaths d N) (f : CellPath d → List ℕ)
    (p : CellPath d) :
    labeledChildren L f a b p ⊆ (cubePaths d (b-a)).image (fun q => p.take a ++ q) := by
  classical
  intro c hc
  obtain ⟨q,hq,rfl⟩ := Finset.mem_image.mp hc
  obtain ⟨hq,ha,_⟩ := Finset.mem_filter.mp hq
  have hlen : q.length = N := (mem_cubePaths d N q).mp (hL hq)
  refine Finset.mem_image.mpr ⟨(q.take b).drop a, ?_, ?_⟩
  · simp only [mem_cubePaths, List.length_drop, List.length_take, hlen,
      Nat.min_eq_left hbN]
  · have he := List.take_append_drop a (q.take b)
    simpa only [List.take_take, Nat.min_eq_left hab, ha] using he

theorem labeledChildren_card_le {N a b : ℕ} (hab : a ≤ b) (hbN : b ≤ N)
    {L : Finset (CellPath d)} (hL : L ⊆ cubePaths d N) (f : CellPath d → List ℕ)
    (p : CellPath d) : (labeledChildren L f a b p).card ≤ 2 ^ (d*(b-a)) :=
  (Finset.card_le_card (labeledChildren_subset_extensions hab hbN hL f p)).trans
    (Finset.card_image_le.trans_eq (card_cubePaths d (b-a)))

theorem child_bin_le {N a b : ℕ} (hab : a ≤ b) (hbN : b ≤ N)
    {L : Finset (CellPath d)} (hL : L ⊆ cubePaths d N) (f : CellPath d → List ℕ)
    (p : CellPath d) : Nat.log 2 (labeledChildren L f a b p).card ≤ d*(b-a) := by
  have hc := labeledChildren_card_le hab hbN hL f p
  have := Nat.log_mono_right (b := 2) hc
  simpa only [Nat.log_pow (by decide : 1 < 2)] using this

theorem extendLabel_card_le {N a b : ℕ} (hab : a ≤ b) (hbN : b ≤ N)
    {L : Finset (CellPath d)} (hL : L ⊆ cubePaths d N) (f : CellPath d → List ℕ) :
    (L.image (extendLabel L a b f)).card ≤ (d*(b-a)+1) * (L.image f).card := by
  classical
  let S := (Finset.range (d*(b-a)+1)).product (L.image f)
  have hs : L.image (extendLabel L a b f) ⊆ S.image (fun z => z.1 :: z.2) := by
    intro T hT
    obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp hT
    exact Finset.mem_image.mpr ⟨(Nat.log 2 (labeledChildren L f a b p).card, f p),
      Finset.mem_product.mpr ⟨Finset.mem_range.mpr
        (Nat.lt_succ_of_le (child_bin_le hab hbN hL f p)),
        Finset.mem_image.mpr ⟨p,hp,rfl⟩⟩,rfl⟩
  calc
    _ ≤ (S.image (fun z => z.1 :: z.2)).card := Finset.card_le_card hs
    _ ≤ S.card := Finset.card_image_le
    _ = _ := by simp [S]

end Falconer.Regularization

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Estimates_DyadicSlopeEnergy
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Dyadic slope energies for the quantitative differentiation of the
planar branching profile. Only the Lipschitz constant two is needed. -/
namespace Falconer

theorem intervalSecantSlope_abs_le {f : ℝ → ℝ} (hf : LipschitzWith 2 f)
    (a : ℝ) {h : ℝ} (hh : 0 < h) : |intervalSecantSlope f a h| ≤ 2 := by
  have hd := hf.dist_le_mul (a+h) a
  rw [Real.dist_eq,Real.dist_eq,add_sub_cancel_left,abs_of_pos hh] at hd
  unfold intervalSecantSlope
  rw [abs_div,abs_of_pos hh]
  exact (div_le_iff₀ hh).2 hd

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Estimates_DyadicLinearApproximation
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A finite energy bound gives uniform linear approximation on the whole interval. -/
namespace Falconer
open Set

theorem intervalSecantError_abs_sub_le {f : ℝ → ℝ} (hf : LipschitzWith 2 f)
    (a : ℝ) {h : ℝ} (hh : 0 < h) (x y : ℝ) :
    |intervalSecantError f a h x-intervalSecantError f a h y| ≤ 4*|x-y| := by
  have hfxy : |f x-f y| ≤ 2*|x-y| := by
    simpa only [Real.dist_eq,NNReal.coe_ofNat] using hf.dist_le_mul x y
  have hs := intervalSecantSlope_abs_le hf a hh
  have he : intervalSecantError f a h x-intervalSecantError f a h y =
      (f x-f y)-intervalSecantSlope f a h*(x-y) := by
    unfold intervalSecantError
    ring
  rw [he]
  calc
    _ ≤ |f x-f y|+|intervalSecantSlope f a h*(x-y)| := by
      simpa only [sub_eq_add_neg,abs_neg] using
        abs_add_le (f x-f y) (-(intervalSecantSlope f a h*(x-y)))
    _ ≤ 2*|x-y|+2*|x-y| := add_le_add hfxy (by
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_right hs (abs_nonneg _))
    _ = _ := by ring

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Estimates_PrefixCounting
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # All-dimensional prefix counts for regularized original measures -/

namespace Falconer.Regularization
variable {d : ℕ}


theorem prefixFiber_leaf {N : ℕ} {C : Finset (CellPath d)} (hC : C ⊆ cubePaths d N)
    {p : CellPath d} (hp : p ∈ C) : prefixFiber C N p = {p} := by
  classical
  ext q
  have hlen {path : CellPath d} (hpath : path ∈ C) : path.length = N :=
    (mem_cubePaths d N path).mp (hC hpath)
  simp only [prefixFiber, Finset.mem_filter, Finset.mem_singleton]
  constructor
  · rintro ⟨hq,he⟩
    simpa only [← hlen hq, List.take_length] using he
  · intro he; subst q
    exact ⟨hp,by rw [← hlen hp,List.take_length]⟩

theorem prefixFiber_nonempty {C : Finset (CellPath d)} {a : ℕ} {P : CellPath d}
    (hP : P ∈ C.image (List.take a)) : (prefixFiber C a P).Nonempty := by
  classical
  obtain ⟨q,hq,rfl⟩ := Finset.mem_image.mp hP
  exact ⟨q,by simp [prefixFiber,hq]⟩

theorem prefixFiber_card_sum {C : Finset (CellPath d)} {a b : ℕ} (hab : a ≤ b)
    (P : CellPath d) :
    (prefixFiber C a P).card =
      ∑ c ∈ prefixChildren C a b P, (prefixFiber C b c).card := by
  classical
  rw [Finset.card_eq_sum_card_image (List.take b) (prefixFiber C a P)]
  apply Finset.sum_congr rfl
  intro c hc
  rw [prefixFiber_parent_filter hab hc]

theorem prefixFiber_count_bounds {C : Finset (CellPath d)} {a b lo hi B : ℕ}
    (hab : a ≤ b) (P : CellPath d)
    (hbranch : B ≤ (prefixChildren C a b P).card ∧ (prefixChildren C a b P).card ≤ 2*B)
    (hchild : ∀ c ∈ prefixChildren C a b P,
      lo ≤ (prefixFiber C b c).card ∧ (prefixFiber C b c).card ≤ hi) :
    B*lo ≤ (prefixFiber C a P).card ∧ (prefixFiber C a P).card ≤ 2*B*hi := by
  classical
  rw [prefixFiber_card_sum hab]
  constructor
  · calc
      B*lo ≤ (prefixChildren C a b P).card*lo := Nat.mul_le_mul_right _ hbranch.1
      _ = ∑ _c ∈ prefixChildren C a b P, lo := by simp
      _ ≤ _ := Finset.sum_le_sum (fun c hc => (hchild c hc).1)
  · calc
      _ ≤ ∑ _c ∈ prefixChildren C a b P, hi := Finset.sum_le_sum (fun c hc => (hchild c hc).2)
      _ = (prefixChildren C a b P).card*hi := by simp
      _ ≤ 2*B*hi := Nat.mul_le_mul_right _ hbranch.2

theorem prefixChildren_class_eq (L : Finset (CellPath d)) (F : CellPath d → List ℕ)
    (a b : ℕ) {T : List ℕ} {p : CellPath d} (hp : p ∈ classLeaves L F T) :
    prefixChildren (classLeaves L F T) a b (p.take a) = labeledChildren L F a b p := by
  classical
  have hFp := (Finset.mem_filter.mp hp).2
  apply congrArg (Finset.image (List.take b))
  ext q
  simp only [prefixFiber, classLeaves, Finset.mem_filter, hFp]
  tauto

end Falconer.Regularization

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Incidence_BlockRegularization
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# All-dimensional block regularization

The upward labels preserve complete child groups at every selected depth.
Count bins cost d*N+1 possibilities and leaf mass bins cost (d+2)*N+1.
-/

namespace Falconer.Regularization
variable {d : ℕ}

theorem blockDepth_antitone (N B : ℕ) : Antitone (blockDepth N B) := by
  intro i j hij
  exact Nat.sub_le_sub_left (Nat.mul_le_mul_right B hij) N

theorem blockDepth_gap (N B i : ℕ) : blockDepth N B i - blockDepth N B (i+1) ≤ B := by
  dsimp only [blockDepth]
  rw [Nat.add_mul, one_mul]
  omega

theorem blockLabel_old (L : Finset (CellPath d)) (N B : ℕ) (f : CellPath d → List ℕ)
    {i j : ℕ} (hij : i ≤ j) {p q : CellPath d}
    (he : blockLabel L N B f j p = blockLabel L N B f j q) :
    blockLabel L N B f i p = blockLabel L N B f i q := by
  induction j with
  | zero =>
    have : i = 0 := by omega
    subst i
    exact he
  | succ j ih =>
    by_cases heq : i = j+1
    · simpa only [heq] using he
    · exact ih (by omega) (extendLabel_old he)

theorem blockLabel_local (L : Finset (CellPath d)) (N B : ℕ) (f : CellPath d → List ℕ)
    {i j a : ℕ} (hij : i ≤ j) (ha : blockDepth N B i ≤ a)
    {p q : CellPath d} (hpq : p.take a = q.take a) :
    blockLabel L N B f j p = blockLabel L N B f j q ↔
      blockLabel L N B f i p = blockLabel L N B f i q := by
  induction j with
  | zero =>
    have : i = 0 := by omega
    subst i
    rfl
  | succ j ih =>
    by_cases heq : i = j+1
    · subst i; rfl
    · have hji : i ≤ j := by omega
      rw [blockLabel, extendLabel_local (take_eq_of_take_eq
        ((blockDepth_antitone N B (by omega : i ≤ j+1)).trans ha) hpq)]
      exact ih hji

theorem block_final_children (L : Finset (CellPath d)) (N B : ℕ) (f : CellPath d → List ℕ)
    {i K : ℕ} (hi : i < K) (p : CellPath d) :
    labeledChildren L (blockLabel L N B f K)
      (blockDepth N B (i+1)) (blockDepth N B i) p =
    labeledChildren L (blockLabel L N B f i)
      (blockDepth N B (i+1)) (blockDepth N B i) p := by
  classical
  apply congrArg (Finset.image (List.take (blockDepth N B i)))
  apply Finset.filter_congr
  intro q _
  constructor
  · rintro ⟨ha,hf⟩
    exact ⟨ha,blockLabel_old L N B f (by omega) hf⟩
  · rintro ⟨ha,hf⟩
    refine ⟨ha,(blockLabel_local L N B f (by omega : i+1 ≤ K) le_rfl ha).mpr ?_⟩
    exact (extendLabel_local ha).mpr hf

theorem block_final_bin_eq (L : Finset (CellPath d)) (N B : ℕ) (f : CellPath d → List ℕ)
    {i K : ℕ} (hi : i < K) {p q : CellPath d}
    (hclass : blockLabel L N B f K p = blockLabel L N B f K q) :
    Nat.log 2 (labeledChildren L (blockLabel L N B f K)
      (blockDepth N B (i+1)) (blockDepth N B i) p).card =
    Nat.log 2 (labeledChildren L (blockLabel L N B f K)
      (blockDepth N B (i+1)) (blockDepth N B i) q).card := by
  rw [block_final_children L N B f hi,block_final_children L N B f hi]
  exact (List.cons.inj (blockLabel_old L N B f (by omega : i+1 ≤ K) hclass)).1

end Falconer.Regularization

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Incidence_BlockLeafCounts
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # All-dimensional block-leaf counts for regularized original measures -/

namespace Falconer.Regularization
variable {d : ℕ}


theorem blockBin_pos (L : Finset (CellPath d)) (F : CellPath d → List ℕ)
    (N B i : ℕ) (p : CellPath d) : 0 < blockBin L F N B i p := by
  unfold blockBin; positivity

theorem blockProduct_pos (L : Finset (CellPath d)) (F : CellPath d → List ℕ)
    (N B i : ℕ) (p : CellPath d) : 0 < blockProduct L F N B i p := by
  exact Finset.prod_pos (fun j _ => blockBin_pos L F N B j p)

theorem blockClass_child_bounds (L : Finset (CellPath d)) (N B : ℕ) (f : CellPath d → List ℕ)
    {K i : ℕ} (hi : i < K) (p : CellPath d)
    {P : CellPath d}
    (hP : P ∈ (classLeaves L (blockLabel L N B f K) (blockLabel L N B f K p)).image
      (List.take (blockDepth N B (i+1)))) :
    let F := blockLabel L N B f K
    let C := classLeaves L F (F p)
    blockBin L F N B i p ≤ (prefixChildren C (blockDepth N B (i+1)) (blockDepth N B i) P).card ∧
      (prefixChildren C (blockDepth N B (i+1)) (blockDepth N B i) P).card ≤ 2*blockBin L F N B i p := by
  classical
  dsimp only
  obtain ⟨q,hq,rfl⟩ := Finset.mem_image.mp hP
  rw [prefixChildren_class_eq L _ _ _ hq]
  have hqL := (Finset.mem_filter.mp hq).1
  have hclass := (Finset.mem_filter.mp hq).2
  unfold blockBin
  rw [block_final_bin_eq L N B f hi hclass.symm]
  have hpos := Finset.card_pos.mpr (labeledChildren_nonempty
    (blockLabel L N B f K) (blockDepth N B (i+1)) (blockDepth N B i) hqL)
  refine ⟨Nat.pow_log_le_self 2 (Nat.ne_of_gt hpos), ?_⟩
  have hu := Nat.lt_pow_succ_log_self (by decide : 1 < 2)
    (labeledChildren L (blockLabel L N B f K) (blockDepth N B (i+1)) (blockDepth N B i) q).card
  simpa only [pow_succ, Nat.mul_comm] using hu.le

theorem blockClass_leaf_count {N : ℕ} {L : Finset (CellPath d)} (hL : L ⊆ cubePaths d N)
    (B : ℕ) (f : CellPath d → List ℕ) (K : ℕ) (p : CellPath d)
    {i : ℕ} (hi : i ≤ K) {P : CellPath d}
    (hP : P ∈ (classLeaves L (blockLabel L N B f K) (blockLabel L N B f K p)).image
      (List.take (blockDepth N B i))) :
    let F := blockLabel L N B f K
    let C := classLeaves L F (F p)
    blockProduct L F N B i p ≤ (prefixFiber C (blockDepth N B i) P).card ∧
      (prefixFiber C (blockDepth N B i) P).card ≤ 2^i * blockProduct L F N B i p := by
  classical
  let F := blockLabel L N B f K
  let C := classLeaves L F (F p)
  have hC : C ⊆ cubePaths d N := fun q hq => hL (Finset.mem_filter.mp hq).1
  change blockProduct L F N B i p ≤ (prefixFiber C (blockDepth N B i) P).card ∧
    (prefixFiber C (blockDepth N B i) P).card ≤ 2^i * blockProduct L F N B i p
  change P ∈ C.image (List.take (blockDepth N B i)) at hP
  induction i generalizing P with
  | zero =>
    obtain ⟨q,hq,rfl⟩ := Finset.mem_image.mp hP
    have hlen : q.length = N := (mem_cubePaths _ _ _).mp (hC hq)
    simp only [blockDepth, Nat.zero_mul, Nat.sub_zero, ← hlen, List.take_length]
    rw [show q.length = N from hlen, prefixFiber_leaf hC hq]
    simp [blockProduct]
  | succ i ih =>
    have hb := blockClass_child_bounds L N B f (by omega : i < K) p hP
    have hc := prefixFiber_count_bounds (blockDepth_antitone N B (Nat.le_succ i)) P hb
      (fun c hc => ih (by omega) (prefixChildren_mem_image hc))
    dsimp only [blockProduct] at hc ⊢
    rw [Finset.prod_range_succ]
    constructor
    · simpa only [Nat.mul_comm] using hc.1
    · have hh := hc.2
      convert hh using 1
      all_goals try with_reducible_and_instances rfl
      ring

end Falconer.Regularization

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Recursion_ProfileInterpolation
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Profiles with the correct all-dimensional slope

The logarithmic child counts are linearly interpolated. Their exact slope
bound is d/N; after rescaling the depth interval to [0,1] it is d.
-/

namespace Falconer.Regularization
variable {d : ℕ}

theorem intervalRamp_increment {a b u v : ℝ} (hab : a ≤ b) (huv : u ≤ v) :
    0 ≤ intervalRamp a b v - intervalRamp a b u ∧
      intervalRamp a b v - intervalRamp a b u ≤ v-u := by
  unfold intervalRamp
  simp only [min_def]
  split_ifs <;> constructor <;> linarith

theorem intervalRamp_sum (d : ℕ → ℝ) (K : ℕ) (u : ℝ) :
    (∑ i ∈ Finset.range K, intervalRamp (d (i+1)) (d i) u) = min u (d 0)-min u (d K) := by
  induction K with
  | zero => simp
  | succ K ih => rw [Finset.sum_range_succ,ih]; unfold intervalRamp; ring

theorem finiteRampProfile_zero (d c : ℕ → ℝ) (K : ℕ) (hd : ∀ i, 0 ≤ d i) :
    finiteRampProfile d c K 0 = 0 := by
  simp [finiteRampProfile,intervalRamp, min_eq_left (hd _)]

theorem blockSlope_bounds {N : ℕ} (hN : 0 < N) {L : Finset (CellPath d)}
    (hL : L ⊆ cubePaths d N) (F : CellPath d → List ℕ) (B i : ℕ) (p : CellPath d) :
    0 ≤ blockSlope L F N B i p ∧ blockSlope L F N B i p ≤ (d:ℝ)/(N:ℝ) := by
  have hN' : 0 < (N:ℝ) := by exact_mod_cast hN
  have hd := blockDepth_antitone N B (Nat.le_succ i)
  have hd' : (blockDepth N B (i+1):ℝ) ≤ (blockDepth N B i:ℝ) := by exact_mod_cast hd
  have hb := child_bin_le hd (Nat.sub_le _ _) hL F p
  have hb' : (Nat.log 2 (labeledChildren L F (blockDepth N B (i+1))
      (blockDepth N B i) p).card:ℝ) ≤ (d:ℝ)*((blockDepth N B i:ℝ)-(blockDepth N B (i+1):ℝ)) := by
    have hbR : (Nat.log 2 (labeledChildren L F (blockDepth N B (i+1))
        (blockDepth N B i) p).card:ℝ) ≤ ((d*(blockDepth N B i-blockDepth N B (i+1)):ℕ):ℝ) := by
      exact_mod_cast hb
    simpa only [Nat.cast_mul,Nat.cast_ofNat,Nat.cast_sub hd] using hbR
  unfold blockSlope
  constructor
  · positivity
  · by_cases he : (blockDepth N B i:ℝ)-(blockDepth N B (i+1):ℝ) = 0
    · rw [he,div_zero]; positivity
    · have hp : 0 < (blockDepth N B i:ℝ)-(blockDepth N B (i+1):ℝ) := lt_of_le_of_ne (sub_nonneg.mpr hd') (Ne.symm he)
      apply (div_le_iff₀ hp).mpr
      apply (div_le_iff₀ hN').mpr
      have heq : (d:ℝ)/(N:ℝ)*((blockDepth N B i:ℝ)-(blockDepth N B (i+1):ℝ))*(N:ℝ) =
          (d:ℝ)*((blockDepth N B i:ℝ)-(blockDepth N B (i+1):ℝ)) := by
        field_simp [hN'.ne']
      rw [heq]
      exact hb'

theorem regularizedProfile_zero (L : Finset (CellPath d)) (F : CellPath d → List ℕ)
    (N B K : ℕ) (p : CellPath d) : regularizedProfile L F N B K p 0 = 0 :=
  finiteRampProfile_zero _ _ _ (fun _ => Nat.cast_nonneg _)

end Falconer.Regularization

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Recursion_ProfileLipschitz
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual regularized branching profile has the global Lipschitz bound
required by quantitative differentiation, including its constant tails. -/
namespace Falconer.Regularization

theorem finiteRampProfile_increment_all (d c : ℕ → ℝ) (K : ℕ) {C u v : ℝ}
    (hd : Antitone d) (hC : 0 ≤ C) (hc : ∀ i < K, 0 ≤ c i ∧ c i ≤ C)
    (huv : u ≤ v) :
    0 ≤ finiteRampProfile d c K v-finiteRampProfile d c K u ∧
      finiteRampProfile d c K v-finiteRampProfile d c K u ≤ C*(v-u) := by
  have he : finiteRampProfile d c K v-finiteRampProfile d c K u =
      ∑ i ∈ Finset.range K, c i*(intervalRamp (d (i+1)) (d i) v-
        intervalRamp (d (i+1)) (d i) u) := by
    simp only [finiteRampProfile,← Finset.sum_sub_distrib,mul_sub]
  have hr (i : ℕ) := intervalRamp_increment (hd (Nat.le_succ i)) huv
  rw [he]
  constructor
  · exact Finset.sum_nonneg fun i hi =>
      mul_nonneg (hc i (Finset.mem_range.mp hi)).1 (hr i).1
  · calc
      _ ≤ ∑ i ∈ Finset.range K, C*(intervalRamp (d (i+1)) (d i) v-
          intervalRamp (d (i+1)) (d i) u) :=
        Finset.sum_le_sum fun i hi => mul_le_mul_of_nonneg_right
          (hc i (Finset.mem_range.mp hi)).2 (hr i).1
      _ = C*(intervalRamp (d K) (d 0) v-intervalRamp (d K) (d 0) u) := by
        rw [← Finset.mul_sum,Finset.sum_sub_distrib,intervalRamp_sum,intervalRamp_sum]
        unfold intervalRamp
        ring
      _ ≤ C*(v-u) := mul_le_mul_of_nonneg_left
        (intervalRamp_increment (hd (Nat.zero_le K)) huv).2 hC

theorem planarProfile_lipschitz {N : ℕ} (hN : 0 < N) {L : Finset (CellPath 2)}
    (hL : L ⊆ cubePaths 2 N) (F : CellPath 2 → List ℕ) (B K : ℕ) (p : CellPath 2) :
    LipschitzWith 2 (fun x : ℝ => regularizedProfile L F N B K p ((N : ℝ)*x)) := by
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  have hi {u v : ℝ} (huv : u ≤ v) :
      0 ≤ regularizedProfile L F N B K p ((N : ℝ)*v)-
        regularizedProfile L F N B K p ((N : ℝ)*u) ∧
      regularizedProfile L F N B K p ((N : ℝ)*v)-
        regularizedProfile L F N B K p ((N : ℝ)*u) ≤ 2*(v-u) := by
    have hstep := finiteRampProfile_increment_all
      (fun i => (blockDepth N B i : ℝ)) (fun i => blockSlope L F N B i p) K
      (show Antitone (fun i => (blockDepth N B i : ℝ)) from fun _ _ h =>
        Nat.cast_le.mpr (blockDepth_antitone N B h))
      (show 0 ≤ (2 : ℝ)/(N : ℝ) by positivity)
      (fun i _ => blockSlope_bounds hN hL F B i p)
      (mul_le_mul_of_nonneg_left huv hNR.le)
    refine ⟨hstep.1,hstep.2.trans_eq ?_⟩
    field_simp
  rw [lipschitzWith_iff_dist_le_mul]
  intro x y
  simp only [Real.dist_eq,NNReal.coe_ofNat]
  by_cases hxy : x ≤ y
  · have hb := hi hxy
    rw [abs_of_nonpos (by linarith [hb.1]),abs_of_nonpos (sub_nonpos.mpr hxy)]
    linarith [hb.2]
  · have hb := hi (le_of_not_ge hxy)
    rw [abs_of_nonneg hb.1,abs_of_nonneg (sub_nonneg.mpr (le_of_not_ge hxy))]
    exact hb.2

end Falconer.Regularization

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Estimates_PrefixRetention
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A large uniform subset retains mass in every one of its occupied parent
cells. This makes the original profile estimates hereditary after thinning. -/
namespace Falconer.Regularization
open scoped BigOperators
attribute [local instance] Classical.propDecidable

theorem prefix_fiber_local_retention (C S : Finset (CellPath 2)) (a : ℕ)
    (hSC : S ⊆ C) {M A D b d : ℝ} (hM : 0 ≤ M) (hA : 0 ≤ A) (hD : 0 ≤ D)
    (hd : 0 ≤ d) (hmass : (C.card:ℝ) ≤ M*(S.card:ℝ))
    (hC : ∀ q ∈ C.image (List.take a), b ≤ ((prefixFiber C a q).card:ℝ) ∧
      ((prefixFiber C a q).card:ℝ) ≤ A*b)
    (hS : ∀ q ∈ S.image (List.take a), d ≤ ((prefixFiber S a q).card:ℝ) ∧
      ((prefixFiber S a q).card:ℝ) ≤ D*d)
    {p : CellPath 2} (hp : p ∈ S.image (List.take a)) :
    ((prefixFiber C a p).card:ℝ) ≤ (A*M*D)*((prefixFiber S a p).card:ℝ) := by
  let B := C.image (List.take a)
  have hBC : p ∈ B := Finset.image_subset_image hSC hp
  have hB : 0 < (B.card:ℝ) := Nat.cast_pos.mpr (Finset.card_pos.mpr ⟨p,hBC⟩)
  have hCsum : (C.card:ℝ) = ∑ q ∈ B, ((prefixFiber C a q).card:ℝ) := by
    exact_mod_cast Finset.card_eq_sum_card_image (List.take a) C
  have hSsum : (S.card:ℝ) = ∑ q ∈ B, ((prefixFiber S a q).card:ℝ) := by
    have hmap : ∀ q ∈ S, q.take a ∈ B := fun q hq => Finset.mem_image_of_mem _ (hSC hq)
    exact_mod_cast Finset.card_eq_sum_card_fiberwise hmap
  have hCmass : b*(B.card:ℝ) ≤ (C.card:ℝ) := by
    rw [hCsum]
    calc
      _ = ∑ _q ∈ B, b := by simp; ring
      _ ≤ _ := Finset.sum_le_sum (fun q hq => (hC q hq).1)
  have hSmass : (S.card:ℝ) ≤ (D*d)*(B.card:ℝ) := by
    rw [hSsum]
    calc
      _ ≤ ∑ _q ∈ B, D*d := by
        apply Finset.sum_le_sum
        intro q _
        by_cases hq : (prefixFiber S a q).Nonempty
        · obtain ⟨v,hv⟩ := hq
          obtain ⟨hv,hvq⟩ := Finset.mem_filter.mp hv
          exact (hS q (Finset.mem_image.mpr ⟨v,hv,hvq⟩)).2
        · rw [Finset.not_nonempty_iff_eq_empty.mp hq,Finset.card_empty,Nat.cast_zero]
          exact mul_nonneg hD hd
      _ = _ := by simp; ring
  have hbd : b ≤ M*D*d := by
    apply (mul_le_mul_iff_left₀ hB).1
    calc
      _ ≤ (C.card:ℝ) := hCmass
      _ ≤ M*(S.card:ℝ) := hmass
      _ ≤ M*((D*d)*(B.card:ℝ)) := mul_le_mul_of_nonneg_left hSmass hM
      _ = _ := by ring
  calc
    _ ≤ A*b := (hC p hBC).2
    _ ≤ A*(M*D*d) := mul_le_mul_of_nonneg_left hbd hA
    _ = (A*M*D)*d := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (hS p hp).1 (by positivity)

end Falconer.Regularization

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Estimates_ChildRetention
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Local retention also controls the number of endpoint cells, not just
the fine mass. This is needed when the next incidence argument uses centers. -/
namespace Falconer.Regularization
open scoped BigOperators
attribute [local instance] Classical.propDecidable

theorem prefix_children_mass_bounds (C : Finset (CellPath 2)) {a b : ℕ}
    (hab : a ≤ b) (p : CellPath 2) {u v : ℝ}
    (hchild : ∀ q ∈ prefixChildren C a b p,
      u ≤ ((prefixFiber C b q).card:ℝ) ∧ ((prefixFiber C b q).card:ℝ) ≤ v) :
    ((prefixChildren C a b p).card:ℝ)*u ≤ (prefixFiber C a p).card ∧
      ((prefixFiber C a p).card:ℝ) ≤ (prefixChildren C a b p).card*v := by
  have he : ((prefixFiber C a p).card:ℝ) =
      ∑ q ∈ prefixChildren C a b p, ((prefixFiber C b q).card:ℝ) := by
    exact_mod_cast prefixFiber_card_sum (C := C) hab p
  rw [he]
  constructor
  · calc
      _ = ∑ _q ∈ prefixChildren C a b p, u := by simp
      _ ≤ _ := Finset.sum_le_sum (fun q hq => (hchild q hq).1)
  · calc
      _ ≤ ∑ _q ∈ prefixChildren C a b p, v := Finset.sum_le_sum (fun q hq => (hchild q hq).2)
      _ = _ := by simp

end Falconer.Regularization

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Estimates_PlanarQuarter
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A fixed contraction puts the actual two projection coordinates inside
one bounded square without changing their finite combinatorics. -/
namespace Falconer
attribute [local instance] Classical.propDecidable

 theorem planarQuarter_apply (p : Space 2) (i : Fin 2) : planarQuarter p i = p i / 4 := by
  change (1/4:ℝ) * p i = p i / 4
  ring

 theorem planarQuarter_dist (p q : Space 2) :
    dist (planarQuarter p) (planarQuarter q) = dist p q / 4 := by
  rw [planarQuarter,planarQuarter,dist_smul₀]
  norm_num
  ring

 theorem planarQuarter_injective : Function.Injective planarQuarter := by
  intro p q h
  have hh : dist p q / 4 = 0 := by rw [← planarQuarter_dist,h,dist_self]
  exact dist_eq_zero.mp (by linarith)

 theorem planarQuarter_separated {δ : ℝ} (G : Finset (Space 2))
    (hsep : FiniteSeparatedAt δ G) :
    FiniteSeparatedAt (δ/4) (G.image planarQuarter) := by
  intro p hp q hq hpq
  obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hp
  obtain ⟨y,hy,rfl⟩ := Finset.mem_image.mp hq
  rw [planarQuarter_dist]
  exact div_le_div_of_nonneg_right (hsep x hx y hy (fun h => hpq (congrArg _ h))) (by norm_num)

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Geometry_HalfSlopeGrid
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Dyadic nearest-grid rounding preserves the slope interval used by the
recursive cell construction. The endpoints are actual points of the grid. -/
namespace Falconer

theorem lineGridRound_monotone {δ : ℝ} (hδ : 0 < δ) :
    Monotone (lineGridRound δ) := by
  intro a b hab
  apply mul_le_mul_of_nonneg_left _ hδ.le
  apply Int.cast_le.mpr
  rw [round_eq,round_eq]
  apply Int.floor_mono
  linarith only [div_le_div_of_nonneg_right hab hδ.le]

theorem lineGridRound_grid {δ : ℝ} (hδ : 0 < δ) (k : ℤ) :
    lineGridRound δ (δ*(k:ℝ)) = δ*(k:ℝ) := by
  simp [lineGridRound,hδ.ne']

theorem lineGridRound_half_interval {δ : ℝ} (hδ : 0 < δ)
    (hk : ∃ k : ℤ, δ*(k:ℝ) = 1/2) {a : ℝ} (ha : |a| ≤ 1/2) :
    |lineGridRound δ a| ≤ 1/2 := by
  obtain ⟨k,hk⟩ := hk
  have hhi : lineGridRound δ (1/2) = 1/2 := by
    rw [← hk]
    exact lineGridRound_grid hδ k
  have hlo : lineGridRound δ (-(1/2)) = -(1/2) := by
    have he : δ*((-k:ℤ):ℝ) = -(1/2) := by simp only [Int.cast_neg,mul_neg,hk]
    rw [← he]
    exact lineGridRound_grid hδ (-k)
  rw [abs_le] at ha ⊢
  exact ⟨hlo ▸ lineGridRound_monotone hδ ha.1,
    hhi ▸ lineGridRound_monotone hδ ha.2⟩

theorem lineGridRound_dyadic_half (n : ℕ) {a : ℝ} (ha : |a| ≤ 1/2) :
    |lineGridRound (1/(2:ℝ)^(n+1)) a| ≤ 1/2 := by
  apply lineGridRound_half_interval (by positivity) _ ha
  refine ⟨(2:ℤ)^n,?_⟩
  push_cast
  rw [pow_succ]
  field_simp

theorem dyadic_local_mesh (a b : ℕ) (hab : a ≤ b) :
    (1/(2:ℝ)^b)/(4*(1/(2:ℝ)^a)) = 1/(2:ℝ)^(b-a+2) := by
  have hp : (2:ℝ)^b = (2:ℝ)^a*(2:ℝ)^(b-a) := by
    rw [← pow_add,Nat.add_sub_of_le hab]
  rw [hp,pow_add]
  norm_num
  field_simp

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Estimates_LocalPacketRows
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The robust projection theorem in the original coordinates of one
coarse cell. No projected point or fine-scale witness is replaced. -/
namespace Falconer
attribute [local instance] Classical.propDecidable

theorem localPacketPoint_injective {Δ : ℝ} (hΔ : 0 < Δ) (y a : ℝ) :
    Function.Injective (localPacketPoint Δ y a) := by
  intro p q he
  have h0 := congrArg (fun z : Space 2 => z 0) he
  have h1 := congrArg (fun z : Space 2 => z 1) he
  change (p 0-y)/Δ = (q 0-y)/Δ at h0
  change (p 1-a)/Δ = (q 1-a)/Δ at h1
  have he0 := (div_left_inj' hΔ.ne').1 h0
  have he1 := (div_left_inj' hΔ.ne').1 h1
  ext i
  fin_cases i
  · change p 0 = q 0
    linarith only [he0]
  · change p 1 = q 1
    linarith only [he1]

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Estimates_LocalPacketRegularity
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact similarity and regularity of the original points in a local
packet chart. The only cost is the explicit cardinality restriction. -/
namespace Falconer
attribute [local instance] Classical.propDecidable

theorem localPacketPoint_eq_smul {Δ : ℝ} (y a : ℝ) (p : Space 2) :
    localPacketPoint Δ y a p = Δ⁻¹ • (p-rowPoint y a) := by
  ext i
  fin_cases i <;> simp [localPacketPoint,div_eq_mul_inv,mul_comm]

theorem localPacketPoint_dist {Δ : ℝ} (hΔ : 0 < Δ) (y a : ℝ) (p q : Space 2) :
    dist (localPacketPoint Δ y a p) (localPacketPoint Δ y a q) = dist p q/Δ := by
  rw [localPacketPoint_eq_smul,localPacketPoint_eq_smul,dist_smul₀,
    dist_sub_right,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr hΔ),div_eq_mul_inv,mul_comm]

theorem localPacketPoint_inverse {Δ : ℝ} (hΔ : 0 < Δ) (y a : ℝ) (z : Space 2) :
    localPacketPoint Δ y a (Δ • z+rowPoint y a) = z := by
  rw [localPacketPoint_eq_smul,add_sub_cancel_right,smul_smul,inv_mul_cancel₀ hΔ.ne',one_smul]

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Estimates_PrefixCenters
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Actual dyadic parent centers and the original finite fibers over them. -/
namespace Falconer
open Set Regularization
attribute [local instance] Classical.propDecidable

theorem DyadicCube.center_coordinate_bound (Q : DyadicCube 2) {x : Space 2}
    (hx : x ∈ Q.carrier) (i : Fin 2) : |x i-Q.center i| ≤ Q.side/2 := by
  have hi := hx i
  change |x i-(Q.origin i+Q.side/2)| ≤ Q.side/2
  rw [abs_le]
  constructor <;> linarith

theorem DyadicCube.center_distance_bound (Q : DyadicCube 2) (hQ : 0 ≤ Q.side)
    {x : Space 2} (hx : x ∈ Q.carrier) : dist x Q.center ≤ Q.side := by
  have h := EuclideanSpace.dist_sq_eq x Q.center
  simp only [Fin.sum_univ_two,Real.dist_eq,sq_abs] at h
  have h0 := (sq_le_sq₀ (abs_nonneg _) (by positivity : 0 ≤ Q.side/2)).mpr
    (Q.center_coordinate_bound hx 0)
  have h1 := (sq_le_sq₀ (abs_nonneg _) (by positivity : 0 ≤ Q.side/2)).mpr
    (Q.center_coordinate_bound hx 1)
  rw [sq_abs] at h0 h1
  nlinarith [dist_nonneg (x := x) (y := Q.center)]

theorem DyadicCube.center_injective_at_depth (Q : DyadicCube 2) (hQ : 0 < Q.side)
    {n : ℕ} {p q : CellPath 2} (hp : p.length = n) (hq : q.length = n)
    (he : (Q.descendant p).center = (Q.descendant q).center) : p = q := by
  by_contra hne
  have hh := Q.centers_separated hQ hp hq hne
  rw [he,dist_self] at hh
  exact (not_le_of_gt (by positivity : 0 < Q.side/(2:ℝ)^n)) hh

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Estimates_PlanarPathCenters
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Realize a finite planar path set by its actual dyadic centers, with an
exact inverse coding. Prefix masses and cardinalities are unchanged. -/
namespace Falconer
open Set Regularization
attribute [local instance] Classical.propDecidable

theorem planar_path_center_realization {N : ℕ} (Q : DyadicCube 2) (hQ : 0 < Q.side)
    (L : Finset (CellPath 2)) (hL : L ⊆ cubePaths 2 N) :
    ∃ l : Space 2 → CellPath 2,
      let P := L.image (fun p => (Q.descendant p).center)
      (∀ x ∈ P, l x ∈ cubePaths 2 N ∧ x ∈ (Q.descendant (l x)).carrier) ∧
      Set.InjOn l (P : Set (Space 2)) ∧ P.image l = L ∧
      FiniteSeparatedAt (Q.side/(2:ℝ)^N) P := by
  let C := fun p : CellPath 2 => (Q.descendant p).center
  have hC : Set.InjOn C (L : Set (CellPath 2)) := by
    intro p hp q hq he
    exact Q.center_injective_at_depth hQ ((mem_cubePaths _ _ _).mp (hL hp))
      ((mem_cubePaths _ _ _).mp (hL hq)) he
  let l := Function.invFunOn C (L : Set (CellPath 2))
  have hl (p : CellPath 2) (hp : p ∈ L) : l (C p) = p := hC.leftInvOn_invFunOn hp
  refine ⟨l,?_,?_,?_,?_⟩
  · intro x hx
    obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp hx
    rw [hl p hp]
    exact ⟨hL hp,(Q.descendant p).center_mem (Q.descendant_side_pos hQ p)⟩
  · intro x hx y hy he
    obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨q,hq,rfl⟩ := Finset.mem_image.mp hy
    rw [hl p hp,hl q hq] at he
    exact congrArg C he
  · ext p
    constructor
    · intro hp
      obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hp
      obtain ⟨q,hq,rfl⟩ := Finset.mem_image.mp hx
      rwa [hl q hq]
    · intro hp
      exact Finset.mem_image.mpr ⟨C p,Finset.mem_image_of_mem C hp,hl p hp⟩
  · intro x hx y hy hxy
    obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨q,hq,rfl⟩ := Finset.mem_image.mp hy
    exact Q.centers_separated hQ ((mem_cubePaths _ _ _).mp (hL hp))
      ((mem_cubePaths _ _ _).mp (hL hq)) (fun he => hxy (congrArg C he))

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Estimates_PlanarPrefixTruncation
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact planar prefix identities at the endpoint of a profile interval. -/
namespace Falconer.Regularization

theorem planar_prefixFiber_image_take (L : Finset (CellPath 2)) {a t : ℕ}
    (hat : a ≤ t) (p : CellPath 2) :
    prefixFiber (L.image (List.take t)) a p = (prefixFiber L a p).image (List.take t) := by
  classical
  ext c
  constructor
  · intro hc
    obtain ⟨u,hu,rfl⟩ := Finset.mem_image.mp (Finset.mem_filter.mp hc).1
    have hparent := (Finset.mem_filter.mp hc).2
    simp only [List.take_take,min_eq_left hat] at hparent
    exact Finset.mem_image.mpr ⟨u,Finset.mem_filter.mpr ⟨hu,hparent⟩,rfl⟩
  · intro hc
    obtain ⟨u,hu,rfl⟩ := Finset.mem_image.mp hc
    exact Finset.mem_filter.mpr ⟨Finset.mem_image_of_mem _ (Finset.mem_filter.mp hu).1,
      by simpa only [List.take_take,min_eq_left hat] using (Finset.mem_filter.mp hu).2⟩

theorem planar_prefix_image_take_cubePaths {N t : ℕ} {L : Finset (CellPath 2)}
    (hL : L ⊆ cubePaths 2 N) (ht : t ≤ N) : L.image (List.take t) ⊆ cubePaths 2 t := by
  classical
  intro p hp
  obtain ⟨q,hq,rfl⟩ := Finset.mem_image.mp hp
  have hlen := (mem_cubePaths 2 N q).mp (hL hq)
  simp only [mem_cubePaths,List.length_take,hlen,min_eq_left ht]

end Falconer.Regularization

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Estimates_LocalPrefixCenters
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Geometric realization of the endpoint cells inside their actual parent.
The local similarity preserves the number of cells and gives the separation
at the relative depth, as well as a bounded point chart. -/
namespace Falconer
open Set Regularization
attribute [local instance] Classical.propDecidable

theorem localPacketPoint_separated {δ Δ : ℝ} (hΔ : 0 < Δ) (y c : ℝ)
    (P : Finset (Space 2)) (hP : FiniteSeparatedAt δ P) :
    FiniteSeparatedAt (δ/Δ) (P.image (localPacketPoint Δ y c)) := by
  intro x hx z hz hxz
  obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp hx
  obtain ⟨q,hq,rfl⟩ := Finset.mem_image.mp hz
  rw [localPacketPoint_dist hΔ]
  exact div_le_div_of_nonneg_right
    (hP p hp q hq (fun he => hxz (congrArg (localPacketPoint Δ y c) he))) hΔ.le

theorem local_prefix_centers_geometry {N a b : ℕ} (Q : DyadicCube 2)
    (hQ : Q.side = 1) (C : Finset (CellPath 2)) (hC : C ⊆ cubePaths 2 N)
    (hab : a ≤ b) (hbN : b ≤ N) (p₀ : CellPath 2) :
    let D := prefixChildren C a b p₀
    let P := D.image (fun q => (Q.descendant q).center)
    let Z := P.image (localPacketPoint (1/(2:ℝ)^a)
      ((Q.descendant p₀).center 0) ((Q.descendant p₀).center 1))
    Z.card = D.card ∧ InBoundedLineChart Z ∧
      FiniteSeparatedAt (1/(2:ℝ)^(b-a)) Z := by
  let D := prefixChildren C a b p₀
  let P := D.image (fun q => (Q.descendant q).center)
  have hQpos : 0 < Q.side := by rw [hQ]; norm_num
  have hD : D ⊆ cubePaths 2 b :=
    (Finset.image_subset_image (Finset.filter_subset _ _)).trans
      (planar_prefix_image_take_cubePaths hC hbN)
  obtain ⟨_,_,_,_,hsep⟩ := planar_path_center_realization Q hQpos D hD
  have hcard : P.card = D.card := by
    apply Finset.card_image_iff.mpr
    intro q hq r hr he
    exact Q.center_injective_at_depth hQpos ((mem_cubePaths _ _ _).mp (hD hq))
      ((mem_cubePaths _ _ _).mp (hD hr)) he
  refine ⟨?_,?_,?_⟩
  · rw [Finset.card_image_of_injective _ (localPacketPoint_injective (by positivity) _ _)]
    exact hcard
  · intro x hx
    obtain ⟨z,hz,rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨q,hq,rfl⟩ := Finset.mem_image.mp hz
    obtain ⟨u,hu,rfl⟩ := Finset.mem_image.mp hq
    obtain ⟨hu,hup⟩ := Finset.mem_filter.mp hu
    have hulen := (mem_cubePaths _ _ _).mp (hC hu)
    have hplen : p₀.length = a := by
      rw [← hup,List.length_take,hulen,Nat.min_eq_left (hab.trans hbN)]
    have htake : (u.take b).take a = p₀ := by
      simpa only [List.take_take,Nat.min_eq_left hab] using hup
    have hm := Q.center_mem_ancestor hQpos (u.take b) a
    rw [htake] at hm
    have hside : (Q.descendant p₀).side = 1/(2:ℝ)^a := by
      rw [Q.descendant_side,hplen,hQ]
    have hc (i : Fin 2) :
        |localPacketPoint (1/(2:ℝ)^a) ((Q.descendant p₀).center 0)
          ((Q.descendant p₀).center 1) (Q.descendant (u.take b)).center i| ≤ 1/2 := by
      have hh := (Q.descendant p₀).center_coordinate_bound hm i
      rw [hside] at hh
      fin_cases i
      · change |(Q.descendant (u.take b)).center 0-(Q.descendant p₀).center 0| ≤
          (1/(2:ℝ)^a)/2 at hh
        change |((Q.descendant (u.take b)).center 0-(Q.descendant p₀).center 0)/
          (1/(2:ℝ)^a)| ≤ 1/2
        rw [abs_div,abs_of_pos (by positivity : 0 < 1/(2:ℝ)^a)]
        exact (div_le_iff₀ (by positivity : 0 < 1/(2:ℝ)^a)).2 (by linarith only [hh])
      · change |(Q.descendant (u.take b)).center 1-(Q.descendant p₀).center 1| ≤
          (1/(2:ℝ)^a)/2 at hh
        change |((Q.descendant (u.take b)).center 1-(Q.descendant p₀).center 1)/
          (1/(2:ℝ)^a)| ≤ 1/2
        rw [abs_div,abs_of_pos (by positivity : 0 < 1/(2:ℝ)^a)]
        exact (div_le_iff₀ (by positivity : 0 < 1/(2:ℝ)^a)).2 (by linarith only [hh])
    exact ⟨(hc 0).trans (by norm_num),(hc 1).trans (by norm_num)⟩
  · have hh := localPacketPoint_separated (by positivity : 0 < 1/(2:ℝ)^a)
      ((Q.descendant p₀).center 0) ((Q.descendant p₀).center 1) P hsep
    have he : (Q.side/(2:ℝ)^b)/(1/(2:ℝ)^a) = 1/(2:ℝ)^(b-a) := by
      rw [hQ,show b = (b-a)+a by omega,pow_add]
      field_simp
      congr 1
      omega
    rw [he] at hh
    exact hh

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Recursion_RetainedProfileBounds
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Profile estimates on the actual endpoint centers after a retained class
is regularized again. The original profile remains the reference profile. -/
namespace Falconer
open Set Regularization
attribute [local instance] Classical.propDecidable

theorem normalizedFiniteBallBound_mono_constant {δ s A B : ℝ} {P : Finset (Space 2)}
    (hδ : 0 ≤ δ) (hAB : A ≤ B) (h : NormalizedFiniteBallBound δ s A P) :
    NormalizedFiniteBallBound δ s B P := by
  intro z r hr hr1
  exact (h z r hr hr1).trans (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right hAB (Real.rpow_nonneg (hδ.trans hr) _)) (Nat.cast_nonneg _))

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Estimates_QuarterEndpointMap
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A fixed quarter chart closes under the actual local cell map. Its
contraction does not accumulate with the number of selected intervals. -/
namespace Falconer
open Set Regularization
attribute [local instance] Classical.propDecidable

theorem quarterEndpointPoint_eq (Q : DyadicCube 2) (a : ℕ) (p₀ r : CellPath 2) :
    quarterEndpointPoint Q a p₀ r = planarQuarter
      (localPacketPoint (1/(2:ℝ)^a) ((Q.descendant p₀).center 0) ((Q.descendant p₀).center 1)
        (Q.descendant r).center) := by
  ext i
  rw [planarQuarter_apply]
  fin_cases i <;> dsimp [quarterEndpointPoint,localPacketPoint] <;> ring

theorem quarterEndpointSet_eq (Q : DyadicCube 2) (C : Finset (CellPath 2))
    (a b : ℕ) (p₀ : CellPath 2) :
    quarterEndpointSet Q C a b p₀ = (blockEndpointSet Q C a b p₀).image planarQuarter := by
  simp only [quarterEndpointSet,blockEndpointSet,Finset.image_image,Function.comp_def]
  congr 1
  funext r
  exact quarterEndpointPoint_eq Q a p₀ r

theorem quarterEndpointPoint_dist (Q : DyadicCube 2) (a : ℕ) (p₀ r t : CellPath 2) :
    dist (quarterEndpointPoint Q a p₀ r) (quarterEndpointPoint Q a p₀ t) =
      dist (Q.descendant r).center (Q.descendant t).center/(4/(2:ℝ)^a) := by
  exact localPacketPoint_dist (by positivity) _ _ _ _

theorem quarterEndpointPoint_injOn {N : ℕ} (Q : DyadicCube 2) (hQ : 0 < Q.side)
    (a : ℕ) (p₀ : CellPath 2) : Set.InjOn (quarterEndpointPoint Q a p₀) (cubePaths 2 N) := by
  intro r hr t ht he
  have hh := localPacketPoint_injective (by positivity : 0 < 4/(2:ℝ)^a)
    ((Q.descendant p₀).center 0) ((Q.descendant p₀).center 1) he
  exact Q.center_injective_at_depth hQ ((mem_cubePaths _ _ _).mp hr)
    ((mem_cubePaths _ _ _).mp ht) hh

theorem quarterEndpointSet_geometry {N a b : ℕ} (Q : DyadicCube 2) (hQ : Q.side = 1)
    (C : Finset (CellPath 2)) (hC : C ⊆ cubePaths 2 N)
    (hab : a ≤ b) (hbN : b ≤ N) (p₀ : CellPath 2) :
    (quarterEndpointSet Q C a b p₀).card = (prefixChildren C a b p₀).card ∧
    (∀ x ∈ quarterEndpointSet Q C a b p₀, |x 0| ≤ 1/4 ∧ |x 1| ≤ 1/4) ∧
    FiniteSeparatedAt (1/(2:ℝ)^(b-a+2)) (quarterEndpointSet Q C a b p₀) := by
  obtain ⟨hcard,hchart,hsep⟩ := local_prefix_centers_geometry Q hQ C hC hab hbN p₀
  rw [quarterEndpointSet_eq]
  refine ⟨?_,?_,?_⟩
  · rw [Finset.card_image_of_injective _ planarQuarter_injective]
    exact hcard
  · intro x hx
    obtain ⟨z,hz,rfl⟩ := Finset.mem_image.mp hx
    have hz' := hchart z hz
    constructor
    · rw [planarQuarter_apply,abs_div]
      norm_num
      linarith only [hz'.1]
    · rw [planarQuarter_apply,abs_div]
      norm_num
      linarith only [hz'.2]
  · have he : (1/(2:ℝ)^(b-a))/4 = 1/(2:ℝ)^(b-a+2) := by
      rw [pow_add]
      norm_num
      ring
    rw [← he]
    exact planarQuarter_separated _ hsep

theorem quarterEndpointPoint_local {a b : ℕ} (hab : a ≤ b) (Q : DyadicCube 2)
    (p₀ q r : CellPath 2) :
    localPacketPoint (4*(1/(2:ℝ)^(b-a+2)))
      (quarterEndpointPoint Q a p₀ q 0) (quarterEndpointPoint Q a p₀ q 1)
      (quarterEndpointPoint Q a p₀ r) = quarterEndpointPoint Q b q r := by
  have hp : (2:ℝ)^b = (2:ℝ)^a*(2:ℝ)^(b-a) := by
    rw [← pow_add,Nat.add_sub_of_le hab]
  ext i
  fin_cases i <;> dsimp [quarterEndpointPoint,localPacketPoint] <;>
    rw [hp,pow_add] <;> norm_num <;> field_simp <;> ring

theorem quarterEndpointPoint_near {b c : ℕ} (hcb : c ≤ b)
    (Q : DyadicCube 2) (hQ : Q.side = 1) (a : ℕ) (p₀ r : CellPath 2)
    (hr : r ∈ cubePaths 2 b) :
    dist (quarterEndpointPoint Q a p₀ r) (quarterEndpointPoint Q a p₀ (r.take c)) ≤
      (1/(2:ℝ)^c)/(4/(2:ℝ)^a) := by
  have hQpos : 0 < Q.side := by rw [hQ]; norm_num
  have hside : (Q.descendant (r.take c)).side = 1/(2:ℝ)^c := by
    rw [Q.descendant_side,List.length_take,(mem_cubePaths _ _ _).mp hr,Nat.min_eq_left hcb,hQ]
  have hh := (Q.descendant (r.take c)).center_distance_bound
    (Q.descendant_side_pos hQpos _).le (Q.center_mem_ancestor hQpos r c)
  rw [hside] at hh
  rw [quarterEndpointPoint_dist]
  exact div_le_div_of_nonneg_right hh (by positivity)

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Estimates_EndpointCoarsening
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Coarsen actual endpoint centers by their original dyadic prefixes.
The point fibers are exact, not geometric enlargements. -/
namespace Falconer
open Set Regularization
attribute [local instance] Classical.propDecidable

theorem planar_prefixChildren_filter (C : Finset (CellPath 2)) {a c b : ℕ}
    (hac : a ≤ c) (hcb : c ≤ b) {p₀ r : CellPath 2}
    (hr : r ∈ prefixChildren C a c p₀) :
    (prefixChildren C a b p₀).filter (fun u => u.take c = r) = prefixChildren C c b r := by
  change prefixFiber ((prefixFiber C a p₀).image (List.take b)) c r = _
  rw [planar_prefixFiber_image_take _ hcb]
  have he : prefixFiber (prefixFiber C a p₀) c r = prefixFiber C c r :=
    prefixFiber_parent_filter hac hr
  rw [he]
  rfl

theorem exists_quarterEndpoint_prefix_map {N a b c : ℕ}
    (Q : DyadicCube 2) (hQ : 0 < Q.side) (C : Finset (CellPath 2))
    (hC : C ⊆ cubePaths 2 N) (hbN : b ≤ N) (p₀ : CellPath 2) :
    ∃ q : Space 2 → Space 2, ∀ r ∈ prefixChildren C a b p₀,
      q (quarterEndpointPoint Q a p₀ r) = quarterEndpointPoint Q a p₀ (r.take c) := by
  let D := prefixChildren C a b p₀
  let F := quarterEndpointPoint Q a p₀
  let P := D.image F
  have hD : D ⊆ cubePaths 2 b :=
    (Finset.image_subset_image (Finset.filter_subset _ _)).trans
      (planar_prefix_image_take_cubePaths hC hbN)
  let pick := fun x : Space 2 => if hx : x ∈ P then (Finset.mem_image.mp hx).choose else []
  have hpick (x : Space 2) (hx : x ∈ P) : pick x ∈ D ∧ F (pick x) = x := by
    simpa only [pick,dite_eq_left hx] using (Finset.mem_image.mp hx).choose_spec
  refine ⟨fun x => F ((pick x).take c),?_⟩
  intro r hr
  have hx : F r ∈ P := Finset.mem_image_of_mem _ hr
  have he : pick (F r) = r := quarterEndpointPoint_injOn Q hQ a p₀
    (hD (hpick _ hx).1) (hD hr) (hpick _ hx).2
  change F ((pick (F r)).take c) = F (r.take c)
  rw [he]

theorem quarterEndpoint_prefix_image {a b c : ℕ} (hcb : c ≤ b)
    (Q : DyadicCube 2) (C : Finset (CellPath 2)) (p₀ : CellPath 2)
    (q : Space 2 → Space 2)
    (hq : ∀ r ∈ prefixChildren C a b p₀,
      q (quarterEndpointPoint Q a p₀ r) = quarterEndpointPoint Q a p₀ (r.take c)) :
    (quarterEndpointSet Q C a b p₀).image q = quarterEndpointSet Q C a c p₀ := by
  unfold quarterEndpointSet
  rw [Finset.image_image]
  calc
    _ = (prefixChildren C a b p₀).image
        (fun r => quarterEndpointPoint Q a p₀ (r.take c)) := Finset.image_congr hq
    _ = _ := by
      simp only [prefixChildren,Finset.image_image,Function.comp_def,List.take_take,
        Nat.min_eq_left hcb]

theorem quarterEndpoint_prefix_fiber {N a b c : ℕ} (hac : a ≤ c) (hcb : c ≤ b)
    (Q : DyadicCube 2) (hQ : 0 < Q.side) (C : Finset (CellPath 2))
    (hC : C ⊆ cubePaths 2 N) (hbN : b ≤ N) (p₀ : CellPath 2)
    (q : Space 2 → Space 2)
    (hq : ∀ r ∈ prefixChildren C a b p₀,
      q (quarterEndpointPoint Q a p₀ r) = quarterEndpointPoint Q a p₀ (r.take c))
    {r : CellPath 2} (hr : r ∈ prefixChildren C a c p₀) :
    (quarterEndpointSet Q C a b p₀).filter (fun x => q x = quarterEndpointPoint Q a p₀ r) =
      (prefixChildren C c b r).image (quarterEndpointPoint Q a p₀) := by
  have hD : prefixChildren C a b p₀ ⊆ cubePaths 2 b :=
    (Finset.image_subset_image (Finset.filter_subset _ _)).trans
      (planar_prefix_image_take_cubePaths hC hbN)
  have hrC : r ∈ cubePaths 2 c :=
    planar_prefix_image_take_cubePaths hC (hcb.trans hbN) (prefixChildren_mem_image hr)
  unfold quarterEndpointSet
  rw [Finset.filter_image]
  have hf : (prefixChildren C a b p₀).filter
      (fun u => q (quarterEndpointPoint Q a p₀ u) = quarterEndpointPoint Q a p₀ r) =
      (prefixChildren C a b p₀).filter (fun u => u.take c = r) := by
    apply Finset.filter_congr
    intro u hu
    rw [hq u hu]
    constructor
    · intro he
      have huc : u.take c ∈ cubePaths 2 c := by
        rw [mem_cubePaths,List.length_take,(mem_cubePaths _ _ _).mp (hD hu),Nat.min_eq_left hcb]
      exact quarterEndpointPoint_injOn Q hQ a p₀ huc hrC he
    · intro he
      rw [he]
  rw [hf,planar_prefixChildren_filter C hac hcb hr]

theorem quarterEndpoint_prefix_local_fiber {N a b c : ℕ} (hac : a ≤ c) (hcb : c ≤ b)
    (Q : DyadicCube 2) (hQ : 0 < Q.side) (C : Finset (CellPath 2))
    (hC : C ⊆ cubePaths 2 N) (hbN : b ≤ N) (p₀ : CellPath 2)
    (q : Space 2 → Space 2)
    (hq : ∀ r ∈ prefixChildren C a b p₀,
      q (quarterEndpointPoint Q a p₀ r) = quarterEndpointPoint Q a p₀ (r.take c))
    {r : CellPath 2} (hr : r ∈ prefixChildren C a c p₀) :
    ((quarterEndpointSet Q C a b p₀).filter
      (fun x => q x = quarterEndpointPoint Q a p₀ r)).image
        (localPacketPoint (4*(1/(2:ℝ)^(c-a+2)))
          (quarterEndpointPoint Q a p₀ r 0) (quarterEndpointPoint Q a p₀ r 1)) =
      quarterEndpointSet Q C c b r := by
  rw [quarterEndpoint_prefix_fiber hac hcb Q hQ C hC hbN p₀ q hq hr,Finset.image_image]
  exact Finset.image_congr fun u _ => quarterEndpointPoint_local hac Q p₀ r u

theorem quarterEndpoint_prefix_near {N a b c : ℕ} (hac : a ≤ c) (hcb : c ≤ b)
    (Q : DyadicCube 2) (hQ : Q.side = 1) (C : Finset (CellPath 2))
    (hC : C ⊆ cubePaths 2 N) (hbN : b ≤ N) (p₀ : CellPath 2)
    (q : Space 2 → Space 2)
    (hq : ∀ r ∈ prefixChildren C a b p₀,
      q (quarterEndpointPoint Q a p₀ r) = quarterEndpointPoint Q a p₀ (r.take c)) :
    ∀ x ∈ quarterEndpointSet Q C a b p₀, dist x (q x) ≤ 1/(2:ℝ)^(c-a+2) := by
  intro x hx
  obtain ⟨r,hr,rfl⟩ := Finset.mem_image.mp hx
  rw [hq r hr]
  have hrC : r ∈ cubePaths 2 b :=
    planar_prefix_image_take_cubePaths hC hbN (prefixChildren_mem_image hr)
  have hh := quarterEndpointPoint_near hcb Q hQ a p₀ r hrC
  rw [show 4/(2:ℝ)^a = 4*(1/(2:ℝ)^a) by ring,dyadic_local_mesh a c hac] at hh
  exact hh

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Estimates_EndpointScaleInputs
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! All geometric inputs of the scale-product step from the actual dyadic
endpoint configuration. Local regularity is tested on the original child. -/
namespace Falconer
open Set Regularization
attribute [local instance] Classical.propDecidable

theorem dyadic_endpoint_local_mesh {a b c : ℕ} (hac : a ≤ c) (hcb : c ≤ b) :
    (1/(2:ℝ)^(b-a+2))/(4*(1/(2:ℝ)^(c-a+2))) = 1/(2:ℝ)^(b-c+2) := by
  rw [dyadic_local_mesh _ _ (by omega)]
  congr 2
  omega

theorem quarter_endpoint_scale_inputs {N a b c : ℕ} (hac : a ≤ c) (hcb : c ≤ b)
    (Q : DyadicCube 2) (hQ : Q.side = 1) (C : Finset (CellPath 2))
    (hC : C ⊆ cubePaths 2 N) (hbN : b ≤ N) (p₀ : CellPath 2)
    (hp₀ : p₀ ∈ C.image (List.take a)) {t KP : ℝ}
    (hball : ∀ r ∈ prefixChildren C a c p₀,
      NormalizedFiniteBallBound (1/(2:ℝ)^(b-c+2)) t KP (quarterEndpointSet Q C c b r)) :
    let P := quarterEndpointSet Q C a b p₀
    let D := quarterEndpointSet Q C a c p₀
    let δ := 1/(2:ℝ)^(b-a+2)
    let ρ := 1/(2:ℝ)^(c-a+2)
    ∃ q : Space 2 → Space 2,
      D.Nonempty ∧ D = P.image q ∧
      (∀ x ∈ P, dist x (q x) ≤ ρ) ∧
      (∀ z ∈ D, |z 0| ≤ 1/4 ∧ |z 1| ≤ 1/4) ∧
      FiniteSeparatedAt δ P ∧
      (∀ z ∈ D, NormalizedFiniteBallBound (δ/(4*ρ)) t KP
        ((P.filter fun x => q x = z).image (localPacketPoint (4*ρ) (z 0) (z 1)))) ∧
      (∀ r ∈ prefixChildren C a c p₀,
        ((P.filter fun x => q x = quarterEndpointPoint Q a p₀ r).image
          (localPacketPoint (4*ρ) (quarterEndpointPoint Q a p₀ r 0)
            (quarterEndpointPoint Q a p₀ r 1))) = quarterEndpointSet Q C c b r) ∧
      0 < δ ∧ 0 < ρ ∧ ρ ≤ 1/4 ∧ δ ≤ ρ := by
  have hQpos : 0 < Q.side := by rw [hQ]; norm_num
  obtain ⟨q,hq⟩ := exists_quarterEndpoint_prefix_map (c := c) Q hQpos C hC hbN p₀
  have hlocal (r : CellPath 2) (hr : r ∈ prefixChildren C a c p₀) :=
    quarterEndpoint_prefix_local_fiber hac hcb Q hQpos C hC hbN p₀ q hq hr
  have hgeom := quarterEndpointSet_geometry Q hQ C hC hac (hcb.trans hbN) p₀
  have hfine := quarterEndpointSet_geometry Q hQ C hC (hac.trans hcb) hbN p₀
  refine ⟨q,((prefixFiber_nonempty hp₀).image _).image _,
    (quarterEndpoint_prefix_image hcb Q C p₀ q hq).symm,
    quarterEndpoint_prefix_near hac hcb Q hQ C hC hbN p₀ q hq,
    hgeom.2.1,hfine.2.2,?_,hlocal,by positivity,by positivity,?_,?_⟩
  · intro z hz
    obtain ⟨r,hr,rfl⟩ := Finset.mem_image.mp hz
    rw [hlocal r hr,dyadic_endpoint_local_mesh hac hcb]
    exact hball r hr
  · apply (div_le_iff₀ (by positivity : 0 < (2:ℝ)^(c-a+2))).2
    have hh : (2:ℝ)^2 ≤ (2:ℝ)^(c-a+2) := pow_le_pow_right₀ (by norm_num) (by omega)
    norm_num at hh ⊢
    linarith only [hh]
  · apply one_div_le_one_div_of_le (by positivity)
    exact pow_le_pow_right₀ (by norm_num) (by omega)

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Estimates_EndpointSelectionLift
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Lift a retained set of endpoint cells to its actual original leaves.
The cost is measured inside the active parent and uses the existing block
fiber bounds, rather than the cardinality of the whole configuration. -/
namespace Falconer
open Set Regularization
open scoped BigOperators
attribute [local instance] Classical.propDecidable

theorem quarter_endpoint_subset_paths {N a b : ℕ}
    (Q : DyadicCube 2) (hQ : 0 < Q.side) (C : Finset (CellPath 2))
    (hC : C ⊆ cubePaths 2 N) (hbN : b ≤ N) (p₀ : CellPath 2)
    (P : Finset (Space 2)) (hP : P ⊆ quarterEndpointSet Q C a b p₀) :
    ∃ D ⊆ prefixChildren C a b p₀,
      D.image (quarterEndpointPoint Q a p₀) = P ∧ D.card = P.card := by
  let F := quarterEndpointPoint Q a p₀
  let D := (prefixChildren C a b p₀).filter (fun r => F r ∈ P)
  have hD : D ⊆ prefixChildren C a b p₀ := Finset.filter_subset _ _
  have he : D.image F = P := by
    ext x
    constructor
    · intro hx
      obtain ⟨r,hr,rfl⟩ := Finset.mem_image.mp hx
      exact (Finset.mem_filter.mp hr).2
    · intro hx
      obtain ⟨r,hr,rfl⟩ := Finset.mem_image.mp (hP hx)
      exact Finset.mem_image_of_mem _ (Finset.mem_filter.mpr ⟨hr,hx⟩)
  have hinj : Set.InjOn F (D:Set (CellPath 2)) := by
    apply (quarterEndpointPoint_injOn Q hQ a p₀).mono
    intro r hr
    exact planar_prefix_image_take_cubePaths hC hbN (prefixChildren_mem_image (hD hr))
  refine ⟨D,hD,he,?_⟩
  rw [← he,Finset.card_image_iff.mpr hinj]

theorem blockClass_lift_endpoint_selection {N : ℕ} {L : Finset (CellPath 2)}
    (hL : L ⊆ cubePaths 2 N) (B : ℕ) (f : CellPath 2 → List ℕ) (K : ℕ) (p : CellPath 2)
    {i j : ℕ} (hji : j ≤ i) (hi : i ≤ K) (p₀ : CellPath 2)
    (D : Finset (CellPath 2))
    (hD : D ⊆ prefixChildren
      (classLeaves L (blockLabel L N B f K) (blockLabel L N B f K p))
      (blockDepth N B i) (blockDepth N B j) p₀)
    (hDne : D.Nonempty) {H : ℝ} (hH : 0 ≤ H)
    (hsize : ((prefixChildren
      (classLeaves L (blockLabel L N B f K) (blockLabel L N B f K p))
      (blockDepth N B i) (blockDepth N B j) p₀).card:ℝ) ≤ H*(D.card:ℝ)) :
    let C := classLeaves L (blockLabel L N B f K) (blockLabel L N B f K p)
    let E := (prefixFiber C (blockDepth N B i) p₀).filter
      (fun r => r.take (blockDepth N B j) ∈ D)
    E ⊆ prefixFiber C (blockDepth N B i) p₀ ∧ E.Nonempty ∧
      ((prefixFiber C (blockDepth N B i) p₀).card:ℝ) ≤
        (H*(2:ℝ)^j)*(E.card:ℝ) ∧ E.image (List.take (blockDepth N B j)) = D := by
  let C := classLeaves L (blockLabel L N B f K) (blockLabel L N B f K p)
  let A := prefixFiber C (blockDepth N B i) p₀
  let E := A.filter (fun r => r.take (blockDepth N B j) ∈ D)
  let u : ℝ := blockProduct L (blockLabel L N B f K) N B j p
  have hu : 0 < u := Nat.cast_pos.mpr (blockProduct_pos _ _ _ _ _ _)
  have hfiber (q : CellPath 2) (hq : q ∈ D) :
      A.filter (fun r => r.take (blockDepth N B j) = q) =
        prefixFiber C (blockDepth N B j) q :=
    prefixFiber_parent_filter (blockDepth_antitone N B hji) (hD hq)
  have hcount : (E.card:ℝ) = ∑ q ∈ D, ((prefixFiber C (blockDepth N B j) q).card:ℝ) := by
    have he := Finset.sum_card_fiberwise_eq_card_filter A D (List.take (blockDepth N B j))
    rw [show A.filter (fun x => x.take (blockDepth N B j) ∈ D) = E from rfl] at he
    rw [← he]
    push_cast
    apply Finset.sum_congr rfl
    intro q hq
    rw [hfiber q hq]
  have hbounds (q : CellPath 2) (hq : q ∈ prefixChildren C (blockDepth N B i) (blockDepth N B j) p₀) :
      u ≤ ((prefixFiber C (blockDepth N B j) q).card:ℝ) ∧
        ((prefixFiber C (blockDepth N B j) q).card:ℝ) ≤ (2:ℝ)^j*u := by
    dsimp only [C,u]
    exact_mod_cast blockClass_leaf_count hL B f K p (hji.trans hi) (prefixChildren_mem_image hq)
  have hElow : (D.card:ℝ)*u ≤ (E.card:ℝ) := by
    rw [hcount]
    calc
      _ = ∑ _q ∈ D, u := by simp
      _ ≤ _ := Finset.sum_le_sum fun q hq => (hbounds q (hD hq)).1
  have hE : E.Nonempty := Finset.card_pos.mp (Nat.cast_pos.mp
    ((mul_pos (Nat.cast_pos.mpr hDne.card_pos) hu).trans_le hElow))
  have hupper := (prefix_children_mass_bounds C (blockDepth_antitone N B hji) p₀ hbounds).2
  refine ⟨Finset.filter_subset _ _,hE,?_,?_⟩
  · calc
      _ ≤ ((prefixChildren C (blockDepth N B i) (blockDepth N B j) p₀).card:ℝ)*((2:ℝ)^j*u) := hupper
      _ ≤ (H*(D.card:ℝ))*((2:ℝ)^j*u) := mul_le_mul_of_nonneg_right hsize (by positivity)
      _ = (H*(2:ℝ)^j)*((D.card:ℝ)*u) := by ring
      _ ≤ (H*(2:ℝ)^j)*(E.card:ℝ) := mul_le_mul_of_nonneg_left hElow (by positivity)
  · ext q
    constructor
    · intro hq
      obtain ⟨r,hr,rfl⟩ := Finset.mem_image.mp hq
      exact (Finset.mem_filter.mp hr).2
    · intro hq
      obtain ⟨r,hr,he⟩ := Finset.mem_image.mp (hD hq)
      exact Finset.mem_image.mpr ⟨r,Finset.mem_filter.mpr ⟨hr,by rwa [he]⟩,he⟩

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Estimates_LocalCellLines
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The exact line map for an isotropically rescaled point cell. It preserves
the original line witnesses and their cardinalities; no direction thinning
is needed for the elementary local incidence estimate. -/
namespace Falconer
attribute [local instance] Classical.propDecidable

theorem localCellLine_leftInverse {Δ : ℝ} (hΔ : 0 < Δ) (y a : ℝ) :
    Function.LeftInverse (unlocalCellLine Δ y a) (localCellLine Δ y a) := by
  intro l
  ext i
  fin_cases i
  · rfl
  · change Δ*((l 0*y+l 1-a)/Δ)-l 0*y+a = l 1
    field_simp
    ring

theorem localCellLine_injective {Δ : ℝ} (hΔ : 0 < Δ) (y a : ℝ) :
    Function.Injective (localCellLine Δ y a) :=
  (localCellLine_leftInverse hΔ y a).injective

theorem unlocalCellLine_dist {Δ y a : ℝ} (hΔ : 0 ≤ Δ) (hΔ1 : Δ ≤ 1)
    (hy : |y| ≤ 1) (l m : Space 2) :
    dist (unlocalCellLine Δ y a l) (unlocalCellLine Δ y a m) ≤ 3*dist l m := by
  have h0 : |l 0-m 0| ≤ dist l m := by
    simpa only [Real.dist_eq] using PiLp.dist_apply_le l m 0
  have h1 : |l 1-m 1| ≤ dist l m := by
    simpa only [Real.dist_eq] using PiLp.dist_apply_le l m 1
  have hb : |(Δ*l 1-l 0*y+a)-(Δ*m 1-m 0*y+a)| ≤ 2*dist l m := by
    calc
      _ = |Δ*(l 1-m 1)-(l 0-m 0)*y| := by congr 1; ring
      _ ≤ |Δ*(l 1-m 1)|+|(l 0-m 0)*y| := abs_sub _ _
      _ = Δ*|l 1-m 1|+|l 0-m 0| * |y| := by rw [abs_mul,abs_mul,abs_of_nonneg hΔ]
      _ ≤ 1*dist l m+dist l m*1 := by gcongr
      _ = _ := by ring
  exact (rowPoint_dist_le_sum (dist_nonneg (x := l) (y := m))
    (by positivity) h0 hb).trans_eq (by ring)

theorem localCellLine_residual {Δ : ℝ} (hΔ : 0 < Δ) (y a : ℝ)
    (p l : Space 2) :
    localPacketPoint Δ y a p 1-localCellLine Δ y a l 0*localPacketPoint Δ y a p 0-
      localCellLine Δ y a l 1 = (p 1-l 0*p 0-l 1)/Δ := by
  change (p 1-a)/Δ-l 0*((p 0-y)/Δ)-(l 0*y+l 1-a)/Δ = _
  field_simp
  ring

theorem localCellLine_incident {δ Δ : ℝ} (hΔ : 0 < Δ) (y a : ℝ)
    (p l : Space 2) (hi : TubeIncident δ p l) :
    TubeIncident (δ/Δ) (localPacketPoint Δ y a p) (localCellLine Δ y a l) := by
  unfold TubeIncident at hi ⊢
  rw [localCellLine_residual hΔ,abs_div,abs_of_pos hΔ]
  change (|p 1-l 0*p 0-l 1|/Δ)/Real.sqrt (1+(l 0)^2) ≤ δ/Δ
  calc
    _ = (|p 1-l 0*p 0-l 1|/Real.sqrt (1+(l 0)^2))/Δ := by ring
    _ ≤ _ := div_le_div_of_nonneg_right hi hΔ.le

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Estimates_LocalLineResolution
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The local line map preserves regularity at each required coarser resolution. -/
namespace Falconer
attribute [local instance] Classical.propDecidable

theorem localCellLine_regular_at {δ Δ ρ s K y a : ℝ}
    (hΔ : 0 < Δ) (hΔ1 : Δ ≤ 1) (hy : |y| ≤ 1)
    (hρ : 0 < ρ) (hδρ : δ ≤ ρ) (hs : 0 ≤ s) (hK : 1 ≤ K)
    (T : Finset (Space 2)) (hT : NormalizedFiniteBallBound δ s K T) :
    NormalizedFiniteBallBound ρ s (K*3^s) (T.image (localCellLine Δ y a)) := by
  intro z r hr _
  have hr0 : 0 ≤ r := hρ.le.trans hr
  let w := unlocalCellLine Δ y a z
  have hsub : (T.image (localCellLine Δ y a)).filter (fun l => dist l z ≤ r) ⊆
      (T.filter (fun l => dist l w ≤ 3*r)).image (localCellLine Δ y a) := by
    intro l hl
    obtain ⟨hl,hlr⟩ := Finset.mem_filter.mp hl
    obtain ⟨m,hm,rfl⟩ := Finset.mem_image.mp hl
    refine Finset.mem_image.mpr ⟨m,Finset.mem_filter.mpr ⟨hm,?_⟩,rfl⟩
    have hh := unlocalCellLine_dist (a := a) hΔ.le hΔ1 hy (localCellLine Δ y a m) z
    rw [localCellLine_leftInverse hΔ y a m] at hh
    exact hh.trans (mul_le_mul_of_nonneg_left hlr (by norm_num))
  rw [Finset.card_image_of_injective _ (localCellLine_injective hΔ y a)]
  calc
    _ ≤ ((T.filter (fun l => dist l w ≤ 3*r)).card:ℝ) :=
      Nat.cast_le.mpr ((Finset.card_le_card hsub).trans Finset.card_image_le)
    _ ≤ K*(3*r)^s*(T.card:ℝ) := normalized_ball_bound_all_radii hs hK hT w (3*r)
      (hδρ.trans (by linarith only [hr,hr0]))
    _ = _ := by rw [Real.mul_rpow (by norm_num : (0:ℝ) ≤ 3) hr0]; ring

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Incidence_OriginalCoarsePackets
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Cell-dependent packets retain original fine tubes, and both their total
size and their common coarse cover are bounded by the original configuration. -/
namespace Falconer
open scoped BigOperators
attribute [local instance] Classical.propDecidable

theorem original_coarse_packets {δ ρ : ℝ} (hδ : 0 ≤ δ) (hρ : 0 < ρ) (hδρ : δ ≤ ρ)
    (P C : Finset (Space 2)) (V T : Space 2 → Finset (Space 2)) (q : Space 2 → Space 2)
    (hnear : ∀ p ∈ P, dist p (q p) ≤ ρ)
    (hCchart : ∀ c ∈ C, |c 0| ≤ 1)
    (hV : ∀ p ∈ P, ∀ l ∈ V p, |l 0| ≤ 1 ∧ TubeIncident δ p l)
    (hT : ∀ c ∈ C, T c ⊆ ((P.filter fun p => q p = c).biUnion V).image
      (fun l => roundedIncidentLine ρ c (l 0))) :
    let U := fun c => (P.filter fun p => q p = c).biUnion V
    let G := fineCoarsePacket ρ C U
    (∀ a ∈ C.biUnion T, (G a).Nonempty) ∧
    (∀ a, G a ⊆ P.biUnion V) ∧
    (∀ c ∈ C, ∀ p ∈ P, q p = c → ∀ l ∈ V p,
      l ∈ G (roundedIncidentLine ρ c (l 0))) ∧
    (∑ a ∈ C.biUnion T, ((G a).card:ℝ)) ≤ 13*((P.biUnion V).card:ℝ) ∧
    ((C.biUnion T).card:ℝ) ≤ 13*(((P.biUnion V).image (coarsePlanarRound ρ)).card:ℝ) := by
  let U := fun c => (P.filter fun p => q p = c).biUnion V
  let W := C.biUnion fun c => (U c).image (fun l => roundedIncidentLine ρ c (l 0))
  have hUU : C.biUnion U ⊆ P.biUnion V := by
    intro l hl
    obtain ⟨c,_,hlc⟩ := Finset.mem_biUnion.mp hl
    obtain ⟨p,hp,hlp⟩ := Finset.mem_biUnion.mp hlc
    exact Finset.mem_biUnion.mpr ⟨p,(Finset.mem_filter.mp hp).1,hlp⟩
  have hTW : C.biUnion T ⊆ W := by
    intro a ha
    obtain ⟨c,hc,ha⟩ := Finset.mem_biUnion.mp ha
    exact Finset.mem_biUnion.mpr ⟨c,hc,hT c hc ha⟩
  have hres : ∀ c ∈ C, ∀ l ∈ U c, |c 1-l 0*c 0-l 1| ≤ 4*ρ := by
    intro c _ l hl
    obtain ⟨p,hp,hl⟩ := Finset.mem_biUnion.mp hl
    obtain ⟨hp,hpc⟩ := Finset.mem_filter.mp hp
    have hc : dist p c ≤ ρ := by simpa only [hpc] using hnear p hp
    exact moved_point_residual hδ hρ hδρ p c l hc (hV p hp l hl).1 (hV p hp l hl).2
  refine ⟨fun a ha => fineCoarsePacket_nonempty C U (hTW ha),?_,?_,?_,?_⟩
  · intro a
    exact (Finset.filter_subset _ _).trans hUU
  · intro c hc p hp hpc l hl
    have hlU : l ∈ U c := Finset.mem_biUnion.mpr ⟨p,Finset.mem_filter.mpr ⟨hp,hpc⟩,hl⟩
    exact Finset.mem_filter.mpr ⟨Finset.mem_biUnion.mpr ⟨c,hc,hlU⟩,c,hc,hlU,rfl⟩
  · calc
      _ ≤ ∑ a ∈ W, ((fineCoarsePacket ρ C U a).card:ℝ) :=
        Finset.sum_le_sum_of_subset_of_nonneg hTW (fun a _ _ => Nat.cast_nonneg _)
      _ ≤ 13*((C.biUnion U).card:ℝ) := by
        exact_mod_cast sum_fineCoarsePacket_card hρ C U hCchart hres
      _ ≤ _ := mul_le_mul_of_nonneg_left (Nat.cast_le.mpr (Finset.card_le_card hUU)) (by norm_num)
  · calc
      _ ≤ (W.card:ℝ) := Nat.cast_le.mpr (Finset.card_le_card hTW)
      _ ≤ 13*(((C.biUnion U).image (coarsePlanarRound ρ)).card:ℝ) :=
        incident_coarse_union_card hρ C U hCchart hres
      _ ≤ _ := mul_le_mul_of_nonneg_left
        (Nat.cast_le.mpr (Finset.card_le_card (Finset.image_subset_image hUU))) (by norm_num)

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Estimates_PacketLogBounds
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Linear depth bounds for the dyadic losses used in packet preparation. -/
namespace Falconer
open scoped BigOperators
attribute [local instance] Classical.propDecidable

theorem bounded_planar_card_dyadic (N : ℕ) (P : Finset (Space 2))
    (hP : InBoundedLineChart P) (hsep : FiniteSeparatedAt (1/(2:ℝ)^N) P) :
    P.card ≤ 2^(2*N+5) := by
  have hball : ∀ p ∈ P, dist p 0 ≤ 2 := by
    intro p hp
    have hd := planar_dist_le_coordinate_sum p 0
    simp only [PiLp.zero_apply,sub_zero] at hd
    linarith only [hd,(hP p hp).1,(hP p hp).2]
  have hb := separated_ball_card P 0 (by positivity : 0 < 1/(2:ℝ)^N)
    (by norm_num : (0:ℝ) ≤ 2) hsep hball
  have hpow : (1:ℝ) ≤ 2^N := one_le_pow₀ (by norm_num)
  have hcalc : (2*(2:ℝ)/(1/2^N)+1)^2 ≤ (2:ℝ)^(2*N+5) := by
    calc
      _ = (4*(2:ℝ)^N+1)^2 := by field_simp; ring
      _ ≤ (5*(2:ℝ)^N)^2 := by gcongr; linarith only [hpow]
      _ ≤ 32*((2:ℝ)^N)^2 := by nlinarith only [sq_nonneg ((2:ℝ)^N)]
      _ = _ := by
        rw [show 2*N = N*2 by omega,pow_add,pow_mul]
        norm_num
        ring
  exact_mod_cast hb.trans hcalc

theorem packet_log_of_card_bound {m a : ℕ} (h : m ≤ 2^a) :
    Nat.log 2 m+1 ≤ a+1 :=
  Nat.add_le_add_right ((Nat.log_le_clog 2 m).trans (Nat.clog_le_of_le_pow h)) 1

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Estimates_ParentPrefixRetention
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A recursive restriction pays for its loss within the current parent,
not for the number of unrelated parents in the original configuration. -/
namespace Falconer.Regularization
attribute [local instance] Classical.propDecidable

theorem blockClass_parent_prefix_retention {N a : ℕ}
    {L L' : Finset (CellPath 2)} (hL : L ⊆ cubePaths 2 N) (hL' : L' ⊆ cubePaths 2 N)
    (B : ℕ) (f g : CellPath 2 → List ℕ) (K : ℕ) (p q r : CellPath 2)
    (hsub : classLeaves L' (blockLabel L' N B g K) (blockLabel L' N B g K q) ⊆
      prefixFiber (classLeaves L (blockLabel L N B f K) (blockLabel L N B f K p)) a r)
    {M : ℝ} (hM : 0 ≤ M)
    (hmass : ((prefixFiber
      (classLeaves L (blockLabel L N B f K) (blockLabel L N B f K p)) a r).card:ℝ) ≤
        M*((classLeaves L' (blockLabel L' N B g K) (blockLabel L' N B g K q)).card:ℝ))
    {i : ℕ} (hi : i ≤ K) (ha : a ≤ blockDepth N B i) {p₀ : CellPath 2}
    (hp₀ : p₀ ∈ (classLeaves L' (blockLabel L' N B g K) (blockLabel L' N B g K q)).image
      (List.take (blockDepth N B i))) :
    let C := classLeaves L (blockLabel L N B f K) (blockLabel L N B f K p)
    let S := classLeaves L' (blockLabel L' N B g K) (blockLabel L' N B g K q)
    ((prefixFiber C (blockDepth N B i) p₀).card:ℝ) ≤
      (M*(2:ℝ)^(2*i))*((prefixFiber S (blockDepth N B i) p₀).card:ℝ) := by
  let C := classLeaves L (blockLabel L N B f K) (blockLabel L N B f K p)
  let S := classLeaves L' (blockLabel L' N B g K) (blockLabel L' N B g K q)
  let C₀ := prefixFiber C a r
  have hC₀ : C₀ ⊆ C := Finset.filter_subset _ _
  have hprefix (u : CellPath 2) (hu : u ∈ C₀.image (List.take (blockDepth N B i))) :
      prefixFiber C₀ (blockDepth N B i) u = prefixFiber C (blockDepth N B i) u :=
    prefixFiber_parent_filter ha hu
  have hret := prefix_fiber_local_retention
    (b := (blockProduct L (blockLabel L N B f K) N B i p:ℝ))
    C₀ S (blockDepth N B i) hsub hM
    (by positivity : 0 ≤ (2:ℝ)^i) (by positivity : 0 ≤ (2:ℝ)^i)
    (Nat.cast_nonneg (blockProduct L' (blockLabel L' N B g K) N B i q)) hmass
    (fun u hu => by
      rw [hprefix u hu]
      exact_mod_cast blockClass_leaf_count hL B f K p hi (Finset.image_subset_image hC₀ hu))
    (fun u hu => by exact_mod_cast blockClass_leaf_count hL' B g K q hi hu) hp₀
  rw [hprefix p₀ (Finset.image_subset_image hsub hp₀)] at hret
  convert hret using 1
  all_goals try with_reducible_and_instances rfl
  rw [show 2*i = i+i by omega,pow_add]
  ring

end Falconer.Regularization

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Estimates_PlanarTreeUniformization
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A logarithmic-cost planar block regularization. The existing exact
prefix classes preserve the local child counts; only the sharper block-width
count and the cardinality selection are needed here. -/
namespace Falconer.Regularization
attribute [local instance] Classical.propDecidable

theorem planar_blockLabel_card_le {L : Finset (CellPath 2)} {N : ℕ}
    (hL : L ⊆ cubePaths 2 N) (B : ℕ) (f : CellPath 2 → List ℕ) (K : ℕ) :
    (L.image (blockLabel L N B f K)).card ≤ (2*B+1)^K*(L.image f).card := by
  induction K with
  | zero => simp [blockLabel]
  | succ K ih =>
    have hs := extendLabel_card_le (blockDepth_antitone N B (Nat.le_succ K))
      (Nat.sub_le N (K*B)) hL (blockLabel L N B f K)
    have hb : 2*(blockDepth N B K-blockDepth N B (K+1))+1 ≤ 2*B+1 :=
      Nat.add_le_add_right (Nat.mul_le_mul_left 2 (blockDepth_gap N B K)) 1
    calc
      _ ≤ (2*B+1)*(L.image (blockLabel L N B f K)).card :=
        hs.trans (Nat.mul_le_mul_right _ hb)
      _ ≤ (2*B+1)*((2*B+1)^K*(L.image f).card) := Nat.mul_le_mul_left _ ih
      _ = _ := by rw [pow_succ]; ac_rfl

theorem exists_large_planar_block_class {L : Finset (CellPath 2)} {N : ℕ}
    (hL : L ⊆ cubePaths 2 N) (hLne : L.Nonempty) (B K : ℕ) :
    let F := blockLabel L N B (fun _ => []) K
    ∃ p ∈ L, L.card ≤ (2*B+1)^K*(classLeaves L F (F p)).card := by
  dsimp only
  let F := blockLabel L N B (fun _ => []) K
  obtain ⟨T,hT,hmax⟩ := (L.image F).exists_max_image
    (fun T => (classLeaves L F T).card) (hLne.image F)
  obtain ⟨p,hp,hpT⟩ := Finset.mem_image.mp hT
  refine ⟨p,hp,?_⟩
  have hc : (L.image F).card ≤ (2*B+1)^K := by
    have h := planar_blockLabel_card_le hL B (fun _ => []) K
    have hi : (L.image (fun _ : CellPath 2 => ([] : List ℕ))).card ≤ 1 :=
      Finset.card_le_one.mpr (by intro a ha b hb; simp_all)
    exact h.trans ((Nat.mul_le_mul_left _ hi).trans_eq (Nat.mul_one _))
  calc
    L.card = ∑ t ∈ L.image F, (classLeaves L F t).card := by
      simpa only [classLeaves] using Finset.card_eq_sum_card_image F L
    _ ≤ ∑ _t ∈ L.image F, (classLeaves L F T).card := Finset.sum_le_sum hmax
    _ = (L.image F).card*(classLeaves L F T).card := by simp
    _ ≤ (2*B+1)^K*(classLeaves L F T).card := Nat.mul_le_mul_right _ hc
    _ = _ := by rw [← hpT]

end Falconer.Regularization

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Estimates_RefinedEndpointSelection
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Re-regularize the actual leaves of a retained endpoint selection.
Every later occupied prefix retains its original local mass. -/
namespace Falconer
open Set Regularization
attribute [local instance] Classical.propDecidable

theorem blockClass_refine_endpoint_selection {N : ℕ} {L : Finset (CellPath 2)}
    (hL : L ⊆ cubePaths 2 N) (B : ℕ) (f : CellPath 2 → List ℕ) (K : ℕ) (p : CellPath 2)
    {i j : ℕ} (hji : j ≤ i) (hi : i ≤ K) (p₀ : CellPath 2)
    (D : Finset (CellPath 2))
    (hD : D ⊆ prefixChildren
      (classLeaves L (blockLabel L N B f K) (blockLabel L N B f K p))
      (blockDepth N B i) (blockDepth N B j) p₀)
    (hDne : D.Nonempty) {H : ℝ} (hH : 0 ≤ H)
    (hsize : ((prefixChildren
      (classLeaves L (blockLabel L N B f K) (blockLabel L N B f K p))
      (blockDepth N B i) (blockDepth N B j) p₀).card:ℝ) ≤ H*(D.card:ℝ)) :
    let C := classLeaves L (blockLabel L N B f K) (blockLabel L N B f K p)
    let M := (H*(2:ℝ)^j)*((2*B+1:ℕ):ℝ)^K
    ∃ E ⊆ prefixFiber C (blockDepth N B i) p₀, E ⊆ cubePaths 2 N ∧
      E.image (List.take (blockDepth N B j)) = D ∧
      ∃ q ∈ E,
        let T := classLeaves E (blockLabel E N B (fun _ => []) K)
          (blockLabel E N B (fun _ => []) K q)
        T ⊆ E ∧ T.Nonempty ∧
          ((prefixFiber C (blockDepth N B i) p₀).card:ℝ) ≤ M*(T.card:ℝ) ∧
          ∀ k, k ≤ K → blockDepth N B i ≤ blockDepth N B k →
            ∀ r ∈ T.image (List.take (blockDepth N B k)),
              ((prefixFiber C (blockDepth N B k) r).card:ℝ) ≤
                (M*(2:ℝ)^(2*k))*((prefixFiber T (blockDepth N B k) r).card:ℝ) := by
  let C := classLeaves L (blockLabel L N B f K) (blockLabel L N B f K p)
  let E := (prefixFiber C (blockDepth N B i) p₀).filter
    (fun r => r.take (blockDepth N B j) ∈ D)
  obtain ⟨hEsub,hEne,hEmass,hEimage⟩ :=
    blockClass_lift_endpoint_selection hL B f K p hji hi p₀ D hD hDne hH hsize
  have hEN : E ⊆ cubePaths 2 N :=
    hEsub.trans ((Finset.filter_subset _ _).trans ((Finset.filter_subset _ _).trans hL))
  obtain ⟨q,hq,hregular⟩ := exists_large_planar_block_class hEN hEne B K
  let T := classLeaves E (blockLabel E N B (fun _ => []) K)
    (blockLabel E N B (fun _ => []) K q)
  have hTsub : T ⊆ E := Finset.filter_subset _ _
  have hTne : T.Nonempty := ⟨q,by simp [T,classLeaves,hq]⟩
  have hreg : (E.card:ℝ) ≤ ((2*B+1:ℕ):ℝ)^K*(T.card:ℝ) := by exact_mod_cast hregular
  have hmass : ((prefixFiber C (blockDepth N B i) p₀).card:ℝ) ≤
      ((H*(2:ℝ)^j)*((2*B+1:ℕ):ℝ)^K)*(T.card:ℝ) := by
    calc
      _ ≤ (H*(2:ℝ)^j)*(E.card:ℝ) := hEmass
      _ ≤ (H*(2:ℝ)^j)*(((2*B+1:ℕ):ℝ)^K*(T.card:ℝ)) :=
        mul_le_mul_of_nonneg_left hreg (by positivity)
      _ = _ := by ring
  refine ⟨E,hEsub,hEN,hEimage,q,hq,hTsub,hTne,hmass,?_⟩
  intro k hk hik r hr
  exact blockClass_parent_prefix_retention hL hEN B f (fun _ => []) K p q p₀
    (hTsub.trans hEsub) (by positivity) hmass hk hik hr

theorem blockClass_refine_quarter_endpoint_subset {N : ℕ} {L : Finset (CellPath 2)}
    (hL : L ⊆ cubePaths 2 N) (B : ℕ) (f : CellPath 2 → List ℕ) (K : ℕ) (p : CellPath 2)
    (Q : DyadicCube 2) (hQ : Q.side = 1)
    {i j : ℕ} (hji : j ≤ i) (hi : i ≤ K) (p₀ : CellPath 2)
    (P : Finset (Space 2)) (hP : P.Nonempty)
    (hsub : P ⊆ quarterEndpointSet Q
      (classLeaves L (blockLabel L N B f K) (blockLabel L N B f K p))
      (blockDepth N B i) (blockDepth N B j) p₀)
    {H : ℝ} (hH : 0 ≤ H)
    (hsize : ((quarterEndpointSet Q
      (classLeaves L (blockLabel L N B f K) (blockLabel L N B f K p))
      (blockDepth N B i) (blockDepth N B j) p₀).card:ℝ) ≤ H*(P.card:ℝ)) :
    let C := classLeaves L (blockLabel L N B f K) (blockLabel L N B f K p)
    let M := (H*(2:ℝ)^j)*((2*B+1:ℕ):ℝ)^K
    ∃ E ⊆ prefixFiber C (blockDepth N B i) p₀, E ⊆ cubePaths 2 N ∧
      ∃ q ∈ E,
        let T := classLeaves E (blockLabel E N B (fun _ => []) K)
          (blockLabel E N B (fun _ => []) K q)
        T ⊆ E ∧ T.Nonempty ∧
          ((prefixFiber C (blockDepth N B i) p₀).card:ℝ) ≤ M*(T.card:ℝ) ∧
          quarterEndpointSet Q T (blockDepth N B i) (blockDepth N B j) p₀ ⊆ P := by
  let C := classLeaves L (blockLabel L N B f K) (blockLabel L N B f K p)
  have hCN : C ⊆ cubePaths 2 N := (Finset.filter_subset _ _).trans hL
  obtain ⟨D,hD,himage,hcard⟩ := quarter_endpoint_subset_paths Q
    (by rw [hQ]; norm_num) C hCN (Nat.sub_le _ _) p₀ P hsub
  have hDne : D.Nonempty := Finset.card_pos.mp (by rw [hcard]; exact hP.card_pos)
  have hcount := (quarterEndpointSet_geometry Q hQ C hCN
    (blockDepth_antitone N B hji) (Nat.sub_le _ _) p₀).1
  have hsizeD : ((prefixChildren C (blockDepth N B i) (blockDepth N B j) p₀).card:ℝ) ≤
      H*(D.card:ℝ) := by
    have hh : ((quarterEndpointSet Q C (blockDepth N B i) (blockDepth N B j) p₀).card:ℝ) ≤
        H*(P.card:ℝ) := hsize
    simpa only [hcount,hcard] using hh
  obtain ⟨E,hE,hEN,hED,q,hq,hT,hTne,hmass,_⟩ :=
    blockClass_refine_endpoint_selection hL B f K p hji hi p₀ D hD hDne hH hsizeD
  let T := classLeaves E (blockLabel E N B (fun _ => []) K)
    (blockLabel E N B (fun _ => []) K q)
  refine ⟨E,hE,hEN,q,hq,hT,hTne,hmass,?_⟩
  have hprefix : prefixFiber T (blockDepth N B i) p₀ = T :=
    Finset.filter_eq_self.mpr fun r hr => (Finset.mem_filter.mp (hE (hT hr))).2
  change ((prefixFiber T (blockDepth N B i) p₀).image (List.take (blockDepth N B j))).image
    (quarterEndpointPoint Q (blockDepth N B i) p₀) ⊆ P
  rw [hprefix,← himage,← hED]
  exact Finset.image_subset_image (Finset.image_subset_image hT)

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Estimates_ParentRefinedEndpointSelection
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A selected endpoint configuration can be regularized again while keeping
the original reference profile and an explicit loss in the new active parent. -/
namespace Falconer
open Set Regularization
attribute [local instance] Classical.propDecidable

theorem blockClass_parent_refine_quarter_endpoint_subset {N a₀ : ℕ}
    {L L' : Finset (CellPath 2)} (hL : L ⊆ cubePaths 2 N) (hL' : L' ⊆ cubePaths 2 N)
    (B : ℕ) (f g : CellPath 2 → List ℕ) (K : ℕ) (p q r₀ : CellPath 2)
    (hsub : classLeaves L' (blockLabel L' N B g K) (blockLabel L' N B g K q) ⊆
      prefixFiber (classLeaves L (blockLabel L N B f K) (blockLabel L N B f K p)) a₀ r₀)
    {M : ℝ} (hM : 0 ≤ M)
    (hmass : ((prefixFiber (classLeaves L (blockLabel L N B f K)
      (blockLabel L N B f K p)) a₀ r₀).card:ℝ) ≤
        M*((classLeaves L' (blockLabel L' N B g K) (blockLabel L' N B g K q)).card:ℝ))
    (Q : DyadicCube 2) (hQ : Q.side = 1)
    {i j : ℕ} (hji : j ≤ i) (hi : i ≤ K) (ha₀ : a₀ ≤ blockDepth N B i) (p₀ : CellPath 2)
    (hp₀ : p₀ ∈ (classLeaves L' (blockLabel L' N B g K) (blockLabel L' N B g K q)).image
      (List.take (blockDepth N B i)))
    (P : Finset (Space 2)) (hP : P.Nonempty)
    (hPsub : P ⊆ quarterEndpointSet Q
      (classLeaves L' (blockLabel L' N B g K) (blockLabel L' N B g K q))
      (blockDepth N B i) (blockDepth N B j) p₀)
    {H : ℝ} (hH : 0 ≤ H)
    (hsize : ((quarterEndpointSet Q
      (classLeaves L' (blockLabel L' N B g K) (blockLabel L' N B g K q))
      (blockDepth N B i) (blockDepth N B j) p₀).card:ℝ) ≤ H*(P.card:ℝ)) :
    let C := classLeaves L (blockLabel L N B f K) (blockLabel L N B f K p)
    let S := classLeaves L' (blockLabel L' N B g K) (blockLabel L' N B g K q)
    let M' := (M*(2:ℝ)^(2*i))*((H*(2:ℝ)^j)*((2*B+1:ℕ):ℝ)^K)
    ∃ E ⊆ prefixFiber S (blockDepth N B i) p₀, E ⊆ cubePaths 2 N ∧
      E ⊆ prefixFiber C (blockDepth N B i) p₀ ∧ ∃ u ∈ E,
        let T := classLeaves E (blockLabel E N B (fun _ => []) K)
          (blockLabel E N B (fun _ => []) K u)
        T ⊆ E ∧ T.Nonempty ∧
          ((prefixFiber C (blockDepth N B i) p₀).card:ℝ) ≤ M'*(T.card:ℝ) ∧
          quarterEndpointSet Q T (blockDepth N B i) (blockDepth N B j) p₀ ⊆ P := by
  obtain ⟨E,hE,hEN,u,hu,hT,hTne,hmassT,hTP⟩ :=
    blockClass_refine_quarter_endpoint_subset hL' B g K q Q hQ hji hi p₀ P hP hPsub hH hsize
  have hEC := hE.trans (Finset.filter_subset_filter _ (hsub.trans (Finset.filter_subset _ _)))
  have hparent := blockClass_parent_prefix_retention hL hL' B f g K p q r₀
    hsub hM hmass hi ha₀ hp₀
  refine ⟨E,hE,hEN,hEC,u,hu,hT,hTne,?_,hTP⟩
  calc
    _ ≤ (M*(2:ℝ)^(2*i))*
        ((prefixFiber (classLeaves L' (blockLabel L' N B g K) (blockLabel L' N B g K q))
          (blockDepth N B i) p₀).card:ℝ) := hparent
    _ ≤ (M*(2:ℝ)^(2*i))*(((H*(2:ℝ)^j)*((2*B+1:ℕ):ℝ)^K)*
        ((classLeaves E (blockLabel E N B (fun _ => []) K)
          (blockLabel E N B (fun _ => []) K u)).card:ℝ)) :=
      mul_le_mul_of_nonneg_left hmassT (by positivity)
    _ = _ := by ring

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Estimates_RescaledCellPackets
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Local packet thinning after the actual cell similarity, with preserved
point mass, point regularity, and the original global tube count. -/
namespace Falconer
attribute [local instance] Classical.propDecidable

theorem rescaled_cell_packet_refinement {δ Δ s t K KP y a m M : ℝ}
    (hδ : 0 < δ) (hΔ : 0 < Δ) (hΔ1 : Δ ≤ 1) (hρ1 : δ/Δ ≤ 1/2)
    (hs : 0 ≤ s) (hK : 1 ≤ K) (hKP : 0 ≤ KP) (hy : |y| ≤ 1)
    (P : Finset (Space 2)) (T : Space 2 → Finset (Space 2)) (hP : P.Nonempty)
    (hcell : ∀ p ∈ P, |p 0-y| ≤ Δ/4 ∧ |p 1-a| ≤ Δ/4)
    (hPsep : FiniteSeparatedAt δ P)
    (hPball : NormalizedFiniteBallBound (δ/Δ) t KP
      (P.image (localPacketPoint Δ y a)))
    (hT : ∀ p ∈ P, (T p).Nonempty ∧ m ≤ ((T p).card:ℝ) ∧ ((T p).card:ℝ) ≤ M ∧
      NormalizedFiniteBallBound δ s K (T p) ∧
      ∀ l ∈ T p, |l 0| ≤ 1/2 ∧ TubeIncident δ p l)
    (D : ℕ) (hD : ∀ p ∈ P, (T p).card ≤ D) :
    let J := Nat.log 2 D+1
    ∃ k : ℕ, ∃ Q ⊆ P.image (localPacketPoint Δ y a), Q.Nonempty ∧
      (P.card:ℝ) ≤ (J:ℝ)*(Q.card:ℝ) ∧
      (∀ p ∈ Q, |p 0| ≤ 1/4 ∧ |p 1| ≤ 1/4) ∧
      FiniteSeparatedAt (δ/Δ) Q ∧ NormalizedFiniteBallBound (δ/Δ) t (KP*(J:ℝ)) Q ∧
      ∃ U : Space 2 → Finset (Space 2),
        (∀ p ∈ Q, (U p).Nonempty ∧ InBoundedLineChart (U p) ∧
          FiniteSeparatedAt (δ/Δ) (U p) ∧
          NormalizedFiniteBallBound (δ/Δ) s (2*((K*3^s)*7^s)*(J:ℝ)) (U p) ∧
          (∀ l ∈ U p, TubeIncident (δ/Δ) p l) ∧
          m/(2*(J:ℝ)*(2:ℝ)^k) ≤ ((U p).card:ℝ) ∧
          ((U p).card:ℝ) ≤ M/(2:ℝ)^k) ∧
        (2:ℝ)^k*((Q.biUnion U).card:ℝ) ≤ 13*((P.biUnion T).card:ℝ) ∧
        ((∀ a : ℝ, |a| ≤ 1/2 → |lineGridRound (δ/Δ) a| ≤ 1/2) →
          ∀ p ∈ Q, ∀ l ∈ U p, |l 0| ≤ 1/2) := by
  let ρ := δ/Δ
  let F := localPacketPoint Δ y a
  let L := localCellLine Δ y a
  let G := fun z : Space 2 => Δ • z+rowPoint y a
  let P' := P.image F
  let V := fun z => (T (G z)).image L
  let J := Nat.log 2 D+1
  have hρ : 0 < ρ := div_pos hδ hΔ
  have hδρ : δ ≤ ρ := by
    apply (le_div_iff₀ hΔ).2
    nlinarith only [hΔ1,hδ]
  have hG (p : Space 2) : G (F p) = p := by
    apply localPacketPoint_injective hΔ y a
    exact localPacketPoint_inverse hΔ y a (F p)
  have hV (p : Space 2) : V (F p) = (T p).image L := by
    dsimp only [V]
    rw [hG]
  have hVc (p : Space 2) : (V (F p)).card = (T p).card := by
    rw [hV,Finset.card_image_of_injective _ (localCellLine_injective hΔ y a)]
  have hP' : P'.Nonempty := hP.image F
  have hsmall : ∀ p ∈ P', |p 0| ≤ 1/4 ∧ |p 1| ≤ 1/4 := by
    intro z hz
    obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp hz
    constructor
    · change |(p 0-y)/Δ| ≤ 1/4
      rw [abs_div,abs_of_pos hΔ]
      exact (div_le_iff₀ hΔ).2 (by linarith only [(hcell p hp).1])
    · change |(p 1-a)/Δ| ≤ 1/4
      rw [abs_div,abs_of_pos hΔ]
      exact (div_le_iff₀ hΔ).2 (by linarith only [(hcell p hp).2])
  have hK' : 1 ≤ K*3^s := by
    have hh := Real.one_le_rpow (by norm_num : (1:ℝ) ≤ 3) hs
    nlinarith only [hK,hh,mul_le_mul hK hh (by norm_num : (0:ℝ) ≤ 1) (zero_le_one.trans hK)]
  have hVdata : ∀ z ∈ P', (V z).Nonempty ∧ NormalizedFiniteBallBound δ s (K*3^s) (V z) ∧
      ∀ l ∈ V z, |l 0| ≤ 1/2 ∧ TubeIncident ρ z l := by
    intro z hz
    obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp hz
    rw [hV]
    refine ⟨(hT p hp).1.image L,?_,?_⟩
    · exact localCellLine_regular_at hΔ hΔ1 hy hδ le_rfl hs hK (T p) (hT p hp).2.2.2.1
    · intro l hl
      obtain ⟨b,hb,rfl⟩ := Finset.mem_image.mp hl
      exact ⟨((hT p hp).2.2.2.2 b hb).1,
        localCellLine_incident hΔ y a p b ((hT p hp).2.2.2.2 b hb).2⟩
  have hVD : ∀ z ∈ P', (V z).card ≤ D := by
    intro z hz
    obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp hz
    rw [hVc]
    exact hD p hp
  obtain ⟨k,Q,hQP',hQ,hmass,U,hU,hunion⟩ := local_direction_packet_refinement
    hρ hρ1 hδρ hs hK' P' V hP' hsmall hVdata D hVD
  have hPcard : P'.card = P.card := Finset.card_image_of_injective _ (localPacketPoint_injective hΔ y a)
  have hP'sep : FiniteSeparatedAt ρ P' := by
    intro z hz w hw hzw
    obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp hz
    obtain ⟨q,hq,rfl⟩ := Finset.mem_image.mp hw
    rw [localPacketPoint_dist hΔ]
    exact div_le_div_of_nonneg_right (hPsep p hp q hq (fun he => hzw (congrArg F he))) hΔ.le
  have hVU : P'.biUnion V ⊆ (P.biUnion T).image L := by
    intro l hl
    obtain ⟨z,hz,hl⟩ := Finset.mem_biUnion.mp hl
    obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp hz
    rw [hV] at hl
    obtain ⟨b,hb,rfl⟩ := Finset.mem_image.mp hl
    exact Finset.mem_image_of_mem L (Finset.mem_biUnion.mpr ⟨p,hp,hb⟩)
  have hVUcard : ((P'.biUnion V).card:ℝ) ≤ ((P.biUnion T).card:ℝ) :=
    Nat.cast_le.mpr ((Finset.card_le_card hVU).trans Finset.card_image_le)
  refine ⟨k,Q,hQP',hQ,by simpa only [hPcard] using hmass,
    fun p hp => hsmall p (hQP' hp),finiteSeparatedAt_subset hQP' hP'sep,
    normalized_finite_ball_bound_subset hρ.le hKP hQP' hmass hPball,U,?_,
    hunion.trans (mul_le_mul_of_nonneg_left hVUcard (by norm_num)),?_⟩
  · intro z hz
    obtain ⟨p,hp,hpEq⟩ := Finset.mem_image.mp (hQP' hz)
    have hsize : m ≤ ((V z).card:ℝ) ∧ ((V z).card:ℝ) ≤ M := by
      rw [← hpEq,hVc]
      exact ⟨(hT p hp).2.1,(hT p hp).2.2.1⟩
    obtain ⟨_,hne,hchart,hsep,hball,hinc,_,hlo,hhi,_⟩ := hU z hz
    refine ⟨hne,hchart,hsep,hball,hinc,?_,?_⟩
    · apply (div_le_iff₀ (by positivity : 0 < 2*(J:ℝ)*(2:ℝ)^k)).2
      have hh : ((V z).card:ℝ) ≤ (J:ℝ)*(2*(2:ℝ)^k)*((U z).card:ℝ) := by exact_mod_cast hlo
      nlinarith only [hsize.1,hh]
    · apply (le_div_iff₀ (by positivity : 0 < (2:ℝ)^k)).2
      have hh : (2:ℝ)^k*((U z).card:ℝ) ≤ ((V z).card:ℝ) := by exact_mod_cast hhi
      nlinarith only [hh,hsize.2]
  · intro hround z hz l hl
    obtain ⟨b,hb,rfl⟩ := Finset.mem_image.mp ((hU z hz).1 hl)
    exact hround (b 0) (((hVdata z (hQP' hz)).2.2 b hb).1)

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Recursion_ProfileEndpointStability
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Endpoint stability for moving the selected profile intervals onto the
actual integer block grid. -/
namespace Falconer
open Set

theorem intervalSecantError_change_interval (f : ℝ → ℝ) (a h u x : ℝ)
    {k : ℝ} (hk : k ≠ 0) :
    intervalSecantError f u k x-intervalSecantError f a h x =
      -((1-(x-u)/k)*intervalSecantError f a h u+
        ((x-u)/k)*intervalSecantError f a h (u+k)) := by
  unfold intervalSecantError intervalSecantSlope
  field_simp [hk]
  ring

theorem intervalSecantError_change_bound (f : ℝ → ℝ) (a h u : ℝ)
    {k A : ℝ} (hk : 0 < k)
    (hleft : |intervalSecantError f a h u| ≤ A)
    (hright : |intervalSecantError f a h (u+k)| ≤ A)
    {x : ℝ} (hx : x ∈ Icc u (u+k)) :
    |intervalSecantError f u k x-intervalSecantError f a h x| ≤ A := by
  have ht0 : 0 ≤ (x-u)/k := div_nonneg (sub_nonneg.mpr hx.1) hk.le
  have ht1 : (x-u)/k ≤ 1 := (div_le_iff₀ hk).2 (by linarith [hx.2])
  have hs0 : 0 ≤ 1-(x-u)/k := sub_nonneg.mpr ht1
  rw [intervalSecantError_change_interval f a h u x hk.ne',abs_neg]
  calc
    _ ≤ |(1-(x-u)/k)*intervalSecantError f a h u|+
        |((x-u)/k)*intervalSecantError f a h (u+k)| := abs_add_le _ _
    _ = (1-(x-u)/k)*|intervalSecantError f a h u|+
        ((x-u)/k)*|intervalSecantError f a h (u+k)| := by
      rw [abs_mul,abs_mul,abs_of_nonneg hs0,abs_of_nonneg ht0]
    _ ≤ (1-(x-u)/k)*A+((x-u)/k)*A := add_le_add
      (mul_le_mul_of_nonneg_left hleft hs0) (mul_le_mul_of_nonneg_left hright ht0)
    _ = A := by ring

theorem intervalSecantError_at_end (f : ℝ → ℝ) (a : ℝ) {h : ℝ} (hh : h ≠ 0) :
    intervalSecantError f a h (a+h) = 0 := by
  unfold intervalSecantError intervalSecantSlope
  field_simp [hh]
  ring

theorem intervalSecantError_near_endpoints {f : ℝ → ℝ} (hf : LipschitzWith 2 f)
    (a : ℝ) {h u k ρ : ℝ} (hh : 0 < h)
    (hu : |u-a| ≤ ρ) (hv : |u+k-(a+h)| ≤ ρ) :
    |intervalSecantError f a h u| ≤ 4*ρ ∧
      |intervalSecantError f a h (u+k)| ≤ 4*ρ := by
  have hleft := intervalSecantError_abs_sub_le hf a hh u a
  have hright := intervalSecantError_abs_sub_le hf a hh (u+k) (a+h)
  have ha : intervalSecantError f a h a = 0 := by simp [intervalSecantError]
  rw [ha,sub_zero] at hleft
  rw [intervalSecantError_at_end f a hh.ne',sub_zero] at hright
  constructor
  · exact hleft.trans (mul_le_mul_of_nonneg_left hu (by norm_num))
  · exact hright.trans (mul_le_mul_of_nonneg_left hv (by norm_num))

theorem intervalSecantError_grid_stability {f : ℝ → ℝ} (hf : LipschitzWith 2 f)
    (a : ℝ) {h u k ρ : ℝ} (hh : 0 < h) (hk : 0 < k)
    (hu : |u-a| ≤ ρ) (hv : |u+k-(a+h)| ≤ ρ)
    {x : ℝ} (hx : x ∈ Icc u (u+k)) :
    |intervalSecantError f u k x-intervalSecantError f a h x| ≤ 4*ρ := by
  have he := intervalSecantError_near_endpoints hf a hh hu hv
  exact intervalSecantError_change_bound f a h u hk he.1 he.2 hx

theorem intervalSecantSlope_change_interval (f : ℝ → ℝ) (a h u : ℝ)
    {k : ℝ} (hk : k ≠ 0) :
    intervalSecantSlope f u k-intervalSecantSlope f a h =
      (intervalSecantError f a h (u+k)-intervalSecantError f a h u)/k := by
  unfold intervalSecantError intervalSecantSlope
  field_simp [hk]
  ring

theorem intervalSecantSlope_change_bound (f : ℝ → ℝ) (a h u : ℝ)
    {k A : ℝ} (hk : 0 < k)
    (hleft : |intervalSecantError f a h u| ≤ A)
    (hright : |intervalSecantError f a h (u+k)| ≤ A) :
    |intervalSecantSlope f u k-intervalSecantSlope f a h| ≤ 2*A/k := by
  rw [intervalSecantSlope_change_interval f a h u hk.ne',abs_div,abs_of_pos hk]
  apply div_le_div_of_nonneg_right _ hk.le
  have he : |intervalSecantError f a h (u+k)-intervalSecantError f a h u| ≤
      |intervalSecantError f a h (u+k)|+|intervalSecantError f a h u| := by
    simpa only [sub_eq_add_neg,abs_neg] using
      abs_add_le (intervalSecantError f a h (u+k)) (-intervalSecantError f a h u)
  linarith

theorem intervalSecantSlope_grid_stability {f : ℝ → ℝ} (hf : LipschitzWith 2 f)
    (a : ℝ) {h u k ρ : ℝ} (hh : 0 < h) (hk : 0 < k)
    (hu : |u-a| ≤ ρ) (hv : |u+k-(a+h)| ≤ ρ) :
    |intervalSecantSlope f u k-intervalSecantSlope f a h| ≤ 8*ρ/k := by
  have he := intervalSecantError_near_endpoints hf a hh hu hv
  convert intervalSecantSlope_change_bound f a h u hk he.1 he.2 using 1 <;> first | rfl | ring

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Recursion_InnerProfileGrid
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Inward rounding of profile intervals to a fixed finite scale grid. -/
namespace Falconer

theorem profileGridLeft_bounds {n : ℕ} (hn : 0 < n) (a : ℝ) :
    a ≤ profileGridLeft n a ∧ profileGridLeft n a ≤ a+1/(n : ℝ) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  constructor
  · apply (le_div_iff₀ hnR).2
    simpa only [mul_comm] using Int.le_ceil ((n : ℝ)*a)
  · apply (div_le_iff₀ hnR).2
    have hb := (Int.ceil_lt_add_one ((n : ℝ)*a)).le
    have he : (a+1/(n : ℝ))*(n : ℝ) = (n : ℝ)*a+1 := by field_simp
    rw [he]
    exact hb

theorem profileGridRight_bounds {n : ℕ} (hn : 0 < n) (b : ℝ) :
    b-1/(n : ℝ) ≤ profileGridRight n b ∧ profileGridRight n b ≤ b := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  constructor
  · apply (le_div_iff₀ hnR).2
    have hb := (Int.lt_floor_add_one ((n : ℝ)*b)).le
    have he : (b-1/(n : ℝ))*(n : ℝ) = (n : ℝ)*b-1 := by field_simp
    rw [he]
    linarith
  · apply (div_le_iff₀ hnR).2
    simpa only [mul_comm] using Int.floor_le ((n : ℝ)*b)

theorem profileGrid_interval_bounds {n : ℕ} (hn : 0 < n) (a h : ℝ) :
    profileGridRight n (a+h)-profileGridLeft n a ≤ h ∧
    h-2/(n : ℝ) ≤ profileGridRight n (a+h)-profileGridLeft n a ∧
    |profileGridLeft n a-a| ≤ 1/(n : ℝ) ∧
    |profileGridRight n (a+h)-(a+h)| ≤ 1/(n : ℝ) := by
  have hl := profileGridLeft_bounds hn a
  have hr := profileGridRight_bounds hn (a+h)
  have he : 2/(n : ℝ) = 2*(1/(n : ℝ)) := by ring
  refine ⟨by linarith,by rw [he]; linarith,?_,?_⟩
  · rw [abs_of_nonneg (sub_nonneg.mpr hl.1)]
    linarith
  · rw [abs_of_nonpos (sub_nonpos.mpr hr.2)]
    linarith

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Recursion_OrderedProfileIntervals
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Length and endpoint accounting for ordered profile intervals. -/
namespace Falconer
open Set

 theorem ordered_interval_length_le {S : List (ℝ × ℝ)} {a b : ℝ} (hab : a ≤ b)
    (hord : S.Pairwise (fun c d => c.1+c.2 ≤ d.1))
    (hb : ∀ c ∈ S, a ≤ c.1 ∧ c.1+c.2 ≤ b ∧ 0 ≤ c.2) :
    (S.map Prod.snd).sum ≤ b-a := by
  induction S generalizing a with
  | nil => simpa using sub_nonneg.mpr hab
  | cons c S ih =>
    rw [List.pairwise_cons] at hord
    have hc := hb c (by simp)
    have hs := ih (a := c.1+c.2) hc.2.1 hord.2 (by
      intro d hd
      exact ⟨hord.1 d hd,(hb d (by simp [hd])).2⟩)
    simp only [List.map_cons,List.sum_cons]
    linarith

 theorem ordered_profile_increment_lower {f : ℝ → ℝ} (hf : LipschitzWith 2 f)
    {S : List (ℝ × ℝ)} {a b : ℝ} (hab : a ≤ b)
    (hord : S.Pairwise (fun c d => c.1+c.2 ≤ d.1))
    (hb : ∀ c ∈ S, a ≤ c.1 ∧ c.1+c.2 ≤ b ∧ 0 ≤ c.2) :
    f b-f a-2*((b-a)-(S.map Prod.snd).sum) ≤
      (S.map (fun c => f (c.1+c.2)-f c.1)).sum := by
  have hinc {u v : ℝ} (huv : u ≤ v) : f v-f u ≤ 2*(v-u) := by
    have hd := hf.dist_le_mul v u
    simp only [Real.dist_eq,NNReal.coe_ofNat,abs_of_nonneg (sub_nonneg.mpr huv)] at hd
    exact (le_abs_self _).trans hd
  induction S generalizing a with
  | nil => simpa using sub_nonpos.mpr (hinc hab)
  | cons c S ih =>
    rw [List.pairwise_cons] at hord
    have hc := hb c (by simp)
    have hs := ih (a := c.1+c.2) hc.2.1 hord.2 (by
      intro d hd
      exact ⟨hord.1 d hd,(hb d (by simp [hd])).2⟩)
    simp only [List.map_cons,List.sum_cons]
    linarith [hinc hc.1]

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Recursion_ProfileGridCells
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Finite interval accounting after inward rounding to the block grid. -/
namespace Falconer

theorem innerProfileCell_length_bounds {n : ℕ} (hn : 0 < n) (c : ℝ × ℝ) :
    c.2-2/(n : ℝ) ≤ (innerProfileCell n c).2 ∧ (innerProfileCell n c).2 ≤ c.2 := by
  exact ⟨(profileGrid_interval_bounds hn c.1 c.2).2.1,(profileGrid_interval_bounds hn c.1 c.2).1⟩

theorem innerProfileCells_ordered {n : ℕ} (hn : 0 < n) {S : List (ℝ × ℝ)}
    (hS : S.Pairwise (fun c d => c.1+c.2 ≤ d.1)) :
    (S.map (innerProfileCell n)).Pairwise (fun c d => c.1+c.2 ≤ d.1) := by
  rw [List.pairwise_map]
  apply hS.imp
  intro c d hcd
  rw [innerProfileCell_end]
  exact (profileGridRight_bounds hn (c.1+c.2)).2.trans
    (hcd.trans (profileGridLeft_bounds hn d.1).1)

theorem innerProfileCells_length_lower {n : ℕ} (hn : 0 < n) (S : List (ℝ × ℝ)) :
    (S.map Prod.snd).sum-(2/(n : ℝ))*(S.length : ℝ) ≤
      ((S.map (innerProfileCell n)).map Prod.snd).sum := by
  induction S with
  | nil => simp
  | cons c S ih =>
    have hc := (innerProfileCell_length_bounds hn c).1
    simp only [List.map_cons,List.sum_cons,List.length_cons,Nat.cast_add,Nat.cast_one]
    linarith

theorem innerProfileCells_min_length {n : ℕ} (hn : 0 < n) {τ : ℝ}
    (hmesh : 2/(n : ℝ) ≤ τ/2) {S : List (ℝ × ℝ)}
    (hmin : ∀ c ∈ S, τ ≤ c.2) :
    ∀ c ∈ S.map (innerProfileCell n), τ/2 ≤ c.2 := by
  intro c hc
  obtain ⟨d,hd,rfl⟩ := List.mem_map.mp hc
  have hh := (innerProfileCell_length_bounds hn d).1
  linarith [hmin d hd]

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Recursion_RoundedProfileError
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Preserve the analytic bounds when the chosen profile intervals are
rounded inward to the finite scale grid. -/
namespace Falconer
open Set

private theorem rounded_error_change {f : ℝ → ℝ} (hf : LipschitzWith 2 f)
    {n : ℕ} (hn : 0 < n) (c : ℝ × ℝ) (hc : 0 < c.2)
    (hd : 0 < (innerProfileCell n c).2) {x : ℝ}
    (hx : x ∈ Icc (innerProfileCell n c).1
      ((innerProfileCell n c).1+(innerProfileCell n c).2)) :
    |intervalSecantError f (innerProfileCell n c).1 (innerProfileCell n c).2 x-
      intervalSecantError f c.1 c.2 x| ≤ 4/(n : ℝ) := by
  have hb := profileGrid_interval_bounds hn c.1 c.2
  have hend : profileGridLeft n c.1+(innerProfileCell n c).2 =
      profileGridRight n (c.1+c.2) := innerProfileCell_end n c
  have he := intervalSecantError_grid_stability hf c.1 hc hd hb.2.2.1
    (by rw [hend]; exact hb.2.2.2) hx
  exact he.trans_eq (by ring)

private theorem rounded_interval_subset {n : ℕ} (hn : 0 < n) (c : ℝ × ℝ) :
    Icc (innerProfileCell n c).1 ((innerProfileCell n c).1+(innerProfileCell n c).2) ⊆
      Icc c.1 (c.1+c.2) := by
  intro x hx
  rw [innerProfileCell_end] at hx
  exact ⟨(profileGridLeft_bounds hn c.1).1.trans hx.1,
    hx.2.trans (profileGridRight_bounds hn (c.1+c.2)).2⟩

theorem rounded_profile_linear_error {f : ℝ → ℝ} (hf : LipschitzWith 2 f)
    {n : ℕ} (hn : 0 < n) (c : ℝ × ℝ) (hc : 0 < c.2)
    (hd : 0 < (innerProfileCell n c).2) {ε : ℝ}
    (herr : ∀ x ∈ Icc c.1 (c.1+c.2), |intervalSecantError f c.1 c.2 x| ≤ ε*c.2)
    {x : ℝ} (hx : x ∈ Icc (innerProfileCell n c).1
      ((innerProfileCell n c).1+(innerProfileCell n c).2)) :
    |intervalSecantError f (innerProfileCell n c).1 (innerProfileCell n c).2 x| ≤
      ε*c.2+4/(n : ℝ) := by
  have he := rounded_error_change hf hn c hc hd hx
  have ho := herr x (rounded_interval_subset hn c hx)
  have ht := abs_add_le
    (intervalSecantError f (innerProfileCell n c).1 (innerProfileCell n c).2 x-
      intervalSecantError f c.1 c.2 x) (intervalSecantError f c.1 c.2 x)
  rw [sub_add_cancel] at ht
  linarith

theorem rounded_profile_superlinear_error {f : ℝ → ℝ} (hf : LipschitzWith 2 f)
    {n : ℕ} (hn : 0 < n) (c : ℝ × ℝ) (hc : 0 < c.2)
    (hd : 0 < (innerProfileCell n c).2) {ε : ℝ}
    (herr : ∀ x ∈ Icc c.1 (c.1+c.2), -ε*c.2 ≤ intervalSecantError f c.1 c.2 x)
    {x : ℝ} (hx : x ∈ Icc (innerProfileCell n c).1
      ((innerProfileCell n c).1+(innerProfileCell n c).2)) :
    -ε*c.2-4/(n : ℝ) ≤ intervalSecantError f (innerProfileCell n c).1 (innerProfileCell n c).2 x := by
  have he := (abs_le.mp (rounded_error_change hf hn c hc hd hx)).1
  have ho := herr x (rounded_interval_subset hn c hx)
  linarith

theorem rounded_profile_slope_error {f : ℝ → ℝ} (hf : LipschitzWith 2 f)
    {n : ℕ} (hn : 0 < n) (c : ℝ × ℝ) (hc : 0 < c.2)
    (hd : 0 < (innerProfileCell n c).2) :
    |intervalSecantSlope f (innerProfileCell n c).1 (innerProfileCell n c).2-
      intervalSecantSlope f c.1 c.2| ≤ 8/((n : ℝ)*(innerProfileCell n c).2) := by
  have hb := profileGrid_interval_bounds hn c.1 c.2
  have hend : profileGridLeft n c.1+(innerProfileCell n c).2 =
      profileGridRight n (c.1+c.2) := innerProfileCell_end n c
  have he := intervalSecantSlope_grid_stability hf c.1 hc hd hb.2.2.1
    (by rw [hend]; exact hb.2.2.2)
  exact he.trans_eq (by ring)

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Geometry_RelativeGridError
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Relative error bounds on the rounded intervals, uniform in their positions. -/
namespace Falconer
open Set

theorem innerProfileCell_relative_bounds {n : ℕ} (hn : 0 < n) {τ ε : ℝ}
    (_hτ : 0 < τ) (hε : 0 ≤ ε) (hmesh : 2/(n : ℝ) ≤ τ/2)
    (herror : 4/(n : ℝ) ≤ ε*(τ/2)) (c : ℝ × ℝ) (hc : τ ≤ c.2) :
    τ/2 ≤ (innerProfileCell n c).2 ∧ c.2 ≤ 2*(innerProfileCell n c).2 ∧
      ε*c.2+4/(n : ℝ) ≤ (3*ε)*(innerProfileCell n c).2 := by
  have hb := (innerProfileCell_length_bounds hn c).1
  have hmin : τ/2 ≤ (innerProfileCell n c).2 := by linarith
  have hhalf : c.2 ≤ 2*(innerProfileCell n c).2 := by linarith
  have hm1 := mul_le_mul_of_nonneg_left hhalf hε
  have hm2 := mul_le_mul_of_nonneg_left hmin hε
  exact ⟨hmin,hhalf,by nlinarith⟩

theorem rounded_profile_relative_linear {f : ℝ → ℝ} (hf : LipschitzWith 2 f)
    {n : ℕ} (hn : 0 < n) {τ ε : ℝ} (hτ : 0 < τ) (hε : 0 ≤ ε)
    (hmesh : 2/(n : ℝ) ≤ τ/2) (herror : 4/(n : ℝ) ≤ ε*(τ/2))
    (c : ℝ × ℝ) (hc : τ ≤ c.2)
    (herr : ∀ x ∈ Icc c.1 (c.1+c.2), |intervalSecantError f c.1 c.2 x| ≤ ε*c.2) :
    ∀ x ∈ Icc (innerProfileCell n c).1 ((innerProfileCell n c).1+(innerProfileCell n c).2),
      |intervalSecantError f (innerProfileCell n c).1 (innerProfileCell n c).2 x| ≤
        (3*ε)*(innerProfileCell n c).2 := by
  have hb := innerProfileCell_relative_bounds hn hτ hε hmesh herror c hc
  intro x hx
  exact (rounded_profile_linear_error hf hn c (hτ.trans_le hc)
    ((half_pos hτ).trans_le hb.1) herr hx).trans hb.2.2

theorem rounded_profile_relative_superlinear {f : ℝ → ℝ} (hf : LipschitzWith 2 f)
    {n : ℕ} (hn : 0 < n) {τ ε : ℝ} (hτ : 0 < τ) (hε : 0 ≤ ε)
    (hmesh : 2/(n : ℝ) ≤ τ/2) (herror : 4/(n : ℝ) ≤ ε*(τ/2))
    (c : ℝ × ℝ) (hc : τ ≤ c.2)
    (herr : ∀ x ∈ Icc c.1 (c.1+c.2), -ε*c.2 ≤ intervalSecantError f c.1 c.2 x) :
    ∀ x ∈ Icc (innerProfileCell n c).1 ((innerProfileCell n c).1+(innerProfileCell n c).2),
      -(3*ε)*(innerProfileCell n c).2 ≤
        intervalSecantError f (innerProfileCell n c).1 (innerProfileCell n c).2 x := by
  have hb := innerProfileCell_relative_bounds hn hτ hε hmesh herror c hc
  intro x hx
  have he := rounded_profile_superlinear_error hf hn c (hτ.trans_le hc)
    ((half_pos hτ).trans_le hb.1) herr hx
  linarith [hb.2.2]

theorem rounded_profile_uniform_slope {f : ℝ → ℝ} (hf : LipschitzWith 2 f)
    {n : ℕ} (hn : 0 < n) {τ : ℝ} (hτ : 0 < τ) (hmesh : 2/(n : ℝ) ≤ τ/2)
    (c : ℝ × ℝ) (hc : τ ≤ c.2) :
    |intervalSecantSlope f (innerProfileCell n c).1 (innerProfileCell n c).2-
      intervalSecantSlope f c.1 c.2| ≤ 16/((n : ℝ)*τ) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hb := (innerProfileCell_length_bounds hn c).1
  have hd : τ/2 ≤ (innerProfileCell n c).2 := by linarith
  have he := rounded_profile_slope_error hf hn c (hτ.trans_le hc) ((half_pos hτ).trans_le hd)
  apply he.trans
  have hm := mul_le_mul_of_nonneg_left hd hnR.le
  have hr := div_le_div_of_nonneg_left (by norm_num : (0 : ℝ) ≤ 8)
    (mul_pos hnR (half_pos hτ)) hm
  exact hr.trans_eq (by ring)

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Recursion_RoundedProfilePieces
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The structured profile decomposition on the actual finite grid, with
explicit slope slack and preserved linear or superlinear control. -/
namespace Falconer
open Set

theorem rounded_structured_profile_pieces {f : ℝ → ℝ} (hf : LipschitzWith 2 f)
    {n : ℕ} (hn : 0 < n) {τ ε s : ℝ} (hτ : 0 < τ) (hε : 0 ≤ ε)
    (hmesh : 2/(n : ℝ) ≤ τ/2) (herror : 4/(n : ℝ) ≤ ε*(τ/2))
    {S : List (ℝ × ℝ)} (hS : StructuredProfilePieces f τ ε s 1 S) :
    (S.map (innerProfileCell n)).Pairwise (fun c d => c.1+c.2 ≤ d.1) ∧
    ∀ c ∈ S.map (innerProfileCell n),
      0 ≤ c.1 ∧ c.1+c.2 ≤ 1 ∧ τ/2 ≤ c.2 ∧
      s-16/((n : ℝ)*τ) ≤ intervalSecantSlope f c.1 c.2 ∧
      ((∀ x ∈ Icc c.1 (c.1+c.2), |intervalSecantError f c.1 c.2 x| ≤ (3*ε)*c.2) ∨
       (intervalSecantSlope f c.1 c.2 ≤ s+16/((n : ℝ)*τ) ∧
        ∀ x ∈ Icc c.1 (c.1+c.2), -(3*ε)*c.2 ≤ intervalSecantError f c.1 c.2 x)) := by
  refine ⟨innerProfileCells_ordered hn hS.ordered,?_⟩
  intro c hc
  obtain ⟨d,hd,rfl⟩ := List.mem_map.mp hc
  have hb := hS.bounds d hd
  have hrel := innerProfileCell_relative_bounds hn hτ hε hmesh herror d hb.2.2
  have hslope := abs_le.mp (rounded_profile_uniform_slope hf hn hτ hmesh d hb.2.2)
  refine ⟨hb.1.trans (profileGridLeft_bounds hn d.1).1,?_,hrel.1,?_,?_⟩
  · rw [innerProfileCell_end]
    exact (profileGridRight_bounds hn (d.1+d.2)).2.trans hb.2.1
  · rcases hS.alternatives d hd with hlin | hsup
    · linarith [hlin.1]
    · rw [hsup.1] at hslope
      linarith
  · rcases hS.alternatives d hd with hlin | hsup
    · exact Or.inl (rounded_profile_relative_linear hf hn hτ hε hmesh herror d hb.2.2 hlin.2)
    · refine Or.inr ⟨?_,rounded_profile_relative_superlinear hf hn hτ hε hmesh herror d hb.2.2 hsup.2⟩
      rw [hsup.1] at hslope
      linarith

theorem innerProfileCell_integer_endpoints {n : ℕ} (hn : 0 < n) (c : ℝ × ℝ)
    (ha : 0 ≤ c.1) (hb : c.1+c.2 ≤ 1) (hd : 0 < (innerProfileCell n c).2) :
    ∃ i j : ℤ, 0 ≤ i ∧ i < j ∧ j ≤ (n : ℤ) ∧
      (innerProfileCell n c).1 = (i : ℝ)/(n : ℝ) ∧
      (innerProfileCell n c).1+(innerProfileCell n c).2 = (j : ℝ)/(n : ℝ) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  let i : ℤ := ⌈(n : ℝ)*c.1⌉
  let j : ℤ := ⌊(n : ℝ)*(c.1+c.2)⌋
  have hi : (n : ℝ)*(innerProfileCell n c).1 = (i : ℝ) := by
    change (n : ℝ)*((i : ℝ)/(n : ℝ)) = i
    exact mul_div_cancel₀ _ hnR.ne'
  have hj : (n : ℝ)*((innerProfileCell n c).1+(innerProfileCell n c).2) = (j : ℝ) := by
    rw [innerProfileCell_end]
    change (n : ℝ)*((j : ℝ)/(n : ℝ)) = j
    exact mul_div_cancel₀ _ hnR.ne'
  have ha' : 0 ≤ (innerProfileCell n c).1 := ha.trans (profileGridLeft_bounds hn c.1).1
  have hb' : (innerProfileCell n c).1+(innerProfileCell n c).2 ≤ 1 := by
    rw [innerProfileCell_end]
    exact (profileGridRight_bounds hn (c.1+c.2)).2.trans hb
  have hi0 : (0 : ℝ) ≤ i := by rw [← hi]; positivity
  have hij : (i : ℝ) < j := by rw [← hi,← hj]; nlinarith [mul_pos hnR hd]
  have hjn : (j : ℝ) ≤ n := by
    rw [← hj]
    nlinarith [mul_le_mul_of_nonneg_left hb' hnR.le]
  refine ⟨i,j,by exact_mod_cast hi0,by exact_mod_cast hij,by exact_mod_cast hjn,rfl,?_⟩
  rw [innerProfileCell_end]
  rfl

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Incidence_BlockGrid
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact identification of the normalized integer grid with block depths.
This lets the rounded analytic intervals select genuine scales of the tree. -/
namespace Falconer.Regularization

theorem blockDepth_multiple {m j B : ℕ} (hj : j ≤ m) :
    blockDepth (m*B) B (m-j) = j*B := by
  dsimp only [blockDepth]
  rw [Nat.sub_mul]
  exact Nat.sub_sub_self (Nat.mul_le_mul_right B hj)

theorem normalized_blockDepth {m j B : ℕ} (hm : 0 < m) (hB : 0 < B) (hj : j ≤ m) :
    (blockDepth (m*B) B (m-j) : ℝ)/(m*B : ℕ) = (j : ℝ)/m := by
  rw [blockDepth_multiple hj]
  push_cast
  have hm' : (m : ℝ) ≠ 0 := (Nat.cast_pos.mpr hm).ne'
  have hB' : (B : ℝ) ≠ 0 := (Nat.cast_pos.mpr hB).ne'
  field_simp

theorem innerProfileCell_natural_endpoints {n : ℕ} (hn : 0 < n) (c : ℝ × ℝ)
    (ha : 0 ≤ c.1) (hb : c.1+c.2 ≤ 1) (hd : 0 < (innerProfileCell n c).2) :
    ∃ i j : ℕ, i < j ∧ j ≤ n ∧
      (innerProfileCell n c).1 = (i : ℝ)/(n : ℝ) ∧
      (innerProfileCell n c).1+(innerProfileCell n c).2 = (j : ℝ)/(n : ℝ) := by
  obtain ⟨i,j,hi,hij,hjn,ha',hb'⟩ := innerProfileCell_integer_endpoints hn c ha hb hd
  have hj : 0 ≤ j := hi.trans hij.le
  have hiR : (i.toNat : ℝ) = (i : ℝ) := by exact_mod_cast Int.toNat_of_nonneg hi
  have hjR : (j.toNat : ℝ) = (j : ℝ) := by exact_mod_cast Int.toNat_of_nonneg hj
  refine ⟨i.toNat,j.toNat,?_,?_,?_,?_⟩
  · omega
  · omega
  · rw [hiR]
    exact ha'
  · rw [hjR]
    exact hb'

theorem innerProfileCell_block_endpoints {m B : ℕ} (hm : 0 < m) (hB : 0 < B)
    (c : ℝ × ℝ) (ha : 0 ≤ c.1) (hb : c.1+c.2 ≤ 1)
    (hd : 0 < (innerProfileCell m c).2) :
    ∃ i j : ℕ, j < i ∧ i ≤ m ∧
      (innerProfileCell m c).1 = (blockDepth (m*B) B i : ℝ)/(m*B : ℕ) ∧
      (innerProfileCell m c).1+(innerProfileCell m c).2 =
        (blockDepth (m*B) B j : ℝ)/(m*B : ℕ) := by
  obtain ⟨a,b,hab,hbm,ha',hb'⟩ := innerProfileCell_natural_endpoints hm c ha hb hd
  refine ⟨m-a,m-b,by omega,Nat.sub_le _ _,?_,?_⟩
  · rw [normalized_blockDepth hm hB (hab.le.trans hbm)]
    exact ha'
  · rw [normalized_blockDepth hm hB hbm]
    exact hb'

end Falconer.Regularization

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Incidence_IncidentCoarsePencils
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Actual coarse pencils incident to a cell center, with original fine
incidence weights and a common separated line grid. -/
namespace Falconer
open scoped BigOperators
attribute [local instance] Classical.propDecidable

theorem incident_regular_coarse_pencil {δ Δ s K : ℝ}
    (hδ : 0 ≤ δ) (hΔ : 0 < Δ) (hΔ1 : Δ ≤ 1/2) (hδΔ : δ ≤ Δ)
    (hs : 0 ≤ s) (hK : 1 ≤ K)
    (P : Finset (Space 2)) (T : Space 2 → Finset (Space 2)) (hP : P.Nonempty)
    (c : Space 2) (hc0 : |c 0| ≤ 1/4) (hc1 : |c 1| ≤ 1/4)
    (hcell : ∀ x ∈ P, dist x c ≤ Δ)
    (hT : ∀ x ∈ P, (T x).Nonempty ∧
      NormalizedFiniteBallBound δ s K (T x) ∧
      ∀ l ∈ T x, |l 0| ≤ 1/2 ∧ TubeIncident δ x l) :
    let W := ∑ x ∈ P, (T x).card
    let J := Nat.log 2 W+1
    let q := fun l : Space 2 => roundedIncidentLine Δ c (l 0)
    ∃ A ⊆ (P.biUnion T).image q, A.Nonempty ∧ InBoundedLineChart A ∧
      FiniteSeparatedAt Δ A ∧ NormalizedFiniteBallBound Δ s (2*(K*(7:ℝ)^s)*(J:ℝ)) A ∧
      ∀ a ∈ A, TubeIncident Δ c a ∧
        (W:ℝ) ≤ 2*(J:ℝ)*(A.card:ℝ)*(coarsePencilWeight P T q a:ℝ) := by
  let q := fun l : Space 2 => roundedIncidentLine Δ c (l 0)
  have hc : |c 0| ≤ 1 := hc0.trans (by norm_num)
  have hnear : ∀ x ∈ P, ∀ l ∈ T x, dist l (q l) ≤ 6*Δ := by
    intro x hx l hl
    have ht := (hT x hx).2.2 l hl
    exact rounded_incident_near_line hΔ c l hc (moved_point_residual hδ hΔ hδΔ
      x c l (hcell x hx) (ht.1.trans (by norm_num)) ht.2)
  obtain ⟨A,hAV,hA,hreg,hweight⟩ := regular_coarse_pencil_mul hΔ hδΔ hs hK
    (C := 6) (by norm_num) P T hP (fun x hx => (hT x hx).1) q hnear
    (fun x hx => (hT x hx).2.1)
  refine ⟨A,hAV,hA,?_,?_,by simpa only [show (6:ℝ)+1=7 by norm_num] using hreg,?_⟩
  · intro a ha
    obtain ⟨l,hl,rfl⟩ := Finset.mem_image.mp (hAV ha)
    obtain ⟨x,hx,hl⟩ := Finset.mem_biUnion.mp hl
    exact roundedIncidentLine_in_chart hΔ hΔ1 c hc0 hc1 (l 0) ((hT x hx).2.2 l hl).1
  · exact finiteSeparatedAt_subset hAV (roundedIncidentLine_family_separated hΔ c
      (fun l : Space 2 => l 0) (P.biUnion T))
  · intro a ha
    obtain ⟨l,_,he⟩ := Finset.mem_image.mp (hAV ha)
    exact ⟨he ▸ roundedIncidentLine_incident hΔ c (l 0),hweight a ha⟩

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Incidence_CoarseCellPencils
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Construct all coarse cell pencils from the original fine incidences,
with one common logarithmic loss and their original fine witnesses. -/
namespace Falconer
open scoped BigOperators
attribute [local instance] Classical.propDecidable

theorem coarse_cell_pencils {δ ρ s K : ℝ}
    (hδ : 0 ≤ δ) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1/2) (hδρ : δ ≤ ρ)
    (hs : 0 ≤ s) (hK : 1 ≤ K)
    (P C : Finset (Space 2)) (V : Space 2 → Finset (Space 2))
    (q : Space 2 → Space 2) (hC : C ⊆ P.image q)
    (hnear : ∀ p ∈ P, dist p (q p) ≤ ρ)
    (hchart : ∀ c ∈ C, |c 0| ≤ 1/4 ∧ |c 1| ≤ 1/4)
    (hV : ∀ p ∈ P, (V p).Nonempty ∧ NormalizedFiniteBallBound δ s K (V p) ∧
      ∀ l ∈ V p, |l 0| ≤ 1/2 ∧ TubeIncident δ p l) :
    let S := fun c => P.filter fun p => q p = c
    let ql := fun c (l : Space 2) => roundedIncidentLine ρ c (l 0)
    let J := Nat.log 2 (∑ p ∈ P, (V p).card)+1
    ∃ T : Space 2 → Finset (Space 2), ∀ c ∈ C,
      T c ⊆ ((S c).biUnion V).image (ql c) ∧ (T c).Nonempty ∧
      InBoundedLineChart (T c) ∧ FiniteSeparatedAt ρ (T c) ∧
      NormalizedFiniteBallBound ρ s (2*(K*(7:ℝ)^s)*(J:ℝ)) (T c) ∧
      (∀ a ∈ T c, TubeIncident ρ c a ∧
        ((∑ p ∈ S c, (V p).card):ℝ) ≤ 2*(J:ℝ)*((T c).card:ℝ)*
          (coarsePencilWeight (S c) V (ql c) a:ℝ)) ∧
      ∀ p ∈ S c, ∀ l ∈ V p, dist l (ql c l) ≤ 6*ρ := by
  dsimp only
  let S := fun c => P.filter fun p => q p = c
  let ql := fun c (l : Space 2) => roundedIncidentLine ρ c (l 0)
  let J := Nat.log 2 (∑ p ∈ P, (V p).card)+1
  have hS (c : Space 2) (hc : c ∈ C) : (S c).Nonempty := by
    obtain ⟨p,hp,hpc⟩ := Finset.mem_image.mp (hC hc)
    exact ⟨p,Finset.mem_filter.mpr ⟨hp,hpc⟩⟩
  have hcell (c : Space 2) (p : Space 2) (hp : p ∈ S c) : dist p c ≤ ρ := by
    obtain ⟨hp,hpc⟩ := Finset.mem_filter.mp hp
    simpa only [hpc] using hnear p hp
  have hchoice (c : Space 2) (hc : c ∈ C) := incident_regular_coarse_pencil hδ hρ hρ1 hδρ hs hK
    (S c) V (hS c hc) c (hchart c hc).1 (hchart c hc).2 (hcell c)
    (fun p hp => hV p (Finset.mem_filter.mp hp).1)
  let T := fun c => if hc : c ∈ C then Classical.choose (hchoice c hc) else ∅
  refine ⟨T,?_⟩
  intro c hc
  have hh := Classical.choose_spec (hchoice c hc)
  have he : T c = Classical.choose (hchoice c hc) := dite_eq_left hc
  rw [← he] at hh
  obtain ⟨hsub,hne,hch,hsep,hreg,hweight⟩ := hh
  have hsum : ∑ p ∈ S c, (V p).card ≤ ∑ p ∈ P, (V p).card :=
    Finset.sum_le_sum_of_subset (Finset.filter_subset _ _)
  have hJ : (Nat.log 2 (∑ p ∈ S c, (V p).card)+1:ℕ) ≤ J :=
    Nat.add_le_add_right (Nat.log_mono_right hsum) 1
  have hJR : ((Nat.log 2 (∑ p ∈ S c, (V p).card)+1:ℕ):ℝ) ≤ (J:ℝ) := Nat.cast_le.mpr hJ
  refine ⟨hsub,hne,hch,hsep,?_,?_,?_⟩
  · intro z r hr hr1
    have hr0 : 0 ≤ r := hρ.le.trans hr
    exact (hreg z r hr hr1).trans (by gcongr)
  · intro a ha
    refine ⟨(hweight a ha).1,?_⟩
    have hw : (∑ p ∈ S c, ((V p).card:ℝ)) ≤
        2*((Nat.log 2 (∑ p ∈ S c, (V p).card)+1:ℕ):ℝ)*((T c).card:ℝ)*
          (coarsePencilWeight (S c) V (ql c) a:ℝ) := by
      simpa only [Nat.cast_sum,ql] using (hweight a ha).2
    have hb : (∑ p ∈ S c, ((V p).card:ℝ)) ≤ 2*(J:ℝ)*((T c).card:ℝ)*
        (coarsePencilWeight (S c) V (ql c) a:ℝ) := by
      calc
        _ ≤ _ := hw
        _ ≤ _ := by gcongr
    simpa only [S,ql,Nat.cast_sum] using hb
  · intro p hp l hl
    have ht := (hV p (Finset.mem_filter.mp hp).1).2.2 l hl
    exact rounded_incident_near_line hρ c l ((hchart c hc).1.trans (by norm_num))
      (moved_point_residual hδ hρ hδρ p c l (hcell c p hp) (ht.1.trans (by norm_num)) ht.2)

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Incidence_CoarsePencilSize
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Uniform coarse pencils, and their size when the total coarse cover is small. -/
namespace Falconer
open scoped BigOperators
attribute [local instance] Classical.propDecidable

theorem uniform_pencil_size_band {δ t K : ℝ} (hδ : 0 ≤ δ) (hK : 0 ≤ K)
    (P : Finset (Space 2)) (T : Space 2 → Finset (Space 2)) (hP : P.Nonempty)
    (hPball : NormalizedFiniteBallBound δ t K P)
    (hT : ∀ x ∈ P, (T x).Nonempty) :
    let J := Nat.log 2 (P.biUnion T).card+1
    ∃ k : ℕ, ∃ R ⊆ P, R.Nonempty ∧ (P.card:ℝ) ≤ (J:ℝ)*(R.card:ℝ) ∧
      NormalizedFiniteBallBound δ t (K*(J:ℝ)) R ∧
      ∀ x ∈ R, (2:ℝ)^k ≤ ((T x).card:ℝ) ∧ ((T x).card:ℝ) ≤ 2*(2:ℝ)^k := by
  obtain ⟨k,R,hRP,hR,hmass,hband⟩ := weighted_dyadic_size_band P
    (fun x => (T x).card) (fun _ => 1) (P.biUnion T).card (fun x hx =>
      ⟨(hT x hx).card_pos,Finset.card_le_card (Finset.subset_biUnion_of_mem T hx)⟩)
    (by simpa using (Nat.cast_pos.mpr hP.card_pos : (0:ℝ) < P.card))
  have hsize : (P.card:ℝ) ≤ (Nat.log 2 (P.biUnion T).card+1:ℕ)*(R.card:ℝ) := by
    simpa using hmass
  refine ⟨k,R,hRP,hR,hsize,normalized_finite_ball_bound_subset hδ hK hRP hsize hPball,?_⟩
  intro x hx
  have hlo : (2:ℝ)^k ≤ ((T x).card:ℝ) := by exact_mod_cast (hband x hx).1
  have hup : ((T x).card:ℝ) < (2:ℝ)^(k+1) := by exact_mod_cast (hband x hx).2
  exact ⟨hlo,by simpa only [pow_succ,mul_comm] using hup.le⟩

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Incidence_FrozenPacketRegularity
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! All geometric properties retained by the packet-size freezing step. -/
namespace Falconer
open scoped BigOperators
attribute [local instance] Classical.propDecidable

theorem freeze_regular_packets {δ s t K m M : ℝ}
    (hδ : 0 < δ) (hK : 0 ≤ K) (hm : 0 < m) (hM : 0 < M)
    (P : Finset (Space 2)) (T : Space 2 → Finset (Space 2)) (hP : P.Nonempty)
    (hPball : NormalizedFiniteBallBound δ t K P)
    (hT : ∀ x ∈ P, m ≤ ((T x).card:ℝ) ∧ ((T x).card:ℝ) ≤ M ∧
      InBoundedLineChart (T x) ∧ FiniteSeparatedAt δ (T x) ∧
      NormalizedFiniteBallBound δ s K (T x) ∧ ∀ l ∈ T x, TubeIncident δ x l)
    (b : Space 2 → ℕ) (D : ℕ) (hb : ∀ l ∈ P.biUnion T, 0 < b l ∧ b l ≤ D) :
    let J := Nat.log 2 D+1
    let F := 2*(J:ℝ)*M/m
    ∃ k : ℕ, ∃ B ⊆ P.biUnion T, B.Nonempty ∧
      (∀ l ∈ B, 2^k ≤ b l ∧ b l < 2^(k+1)) ∧
      ∃ R ⊆ P, R.Nonempty ∧ (P.card:ℝ) ≤ F*(R.card:ℝ) ∧
        NormalizedFiniteBallBound δ t (K*F) R ∧
        ∀ x ∈ R, (T x ∩ B).Nonempty ∧ m/(2*(J:ℝ)) ≤ ((T x ∩ B).card:ℝ) ∧
          InBoundedLineChart (T x ∩ B) ∧ FiniteSeparatedAt δ (T x ∩ B) ∧
          NormalizedFiniteBallBound δ s (K*F) (T x ∩ B) ∧
          ∀ l ∈ T x ∩ B, TubeIncident δ x l := by
  let J := Nat.log 2 D+1
  let F := 2*(J:ℝ)*M/m
  have hJ : 0 < (J:ℝ) := by dsimp [J]; positivity
  have hF : 0 < F := by dsimp [F]; positivity
  obtain ⟨k,B,hBU,hB,hband,R,hRP,hR,hsize,hlarge⟩ := freeze_coarse_packet_sizes
    P T b D hP hm hM (fun x hx => ⟨(hT x hx).1,(hT x hx).2.1⟩) hb
  have hPsize : (P.card:ℝ) ≤ F*(R.card:ℝ) := by
    have hh := (div_le_iff₀ (show 0 < 2*(J:ℝ)*M by positivity)).1 hsize
    calc
      _ ≤ (2*(J:ℝ)*M)*(R.card:ℝ)/m := (le_div_iff₀ hm).2 (by nlinarith only [hh])
      _ = _ := by dsimp [F]; ring
  refine ⟨k,B,hBU,hB,hband,R,hRP,hR,hPsize,
    normalized_finite_ball_bound_subset hδ.le hK hRP hPsize hPball,?_⟩
  intro x hx
  have hxP := hRP hx
  have ht := hT x hxP
  have hcard : 0 < ((T x ∩ B).card:ℝ) := (div_pos hm (by positivity)).trans_le (hlarge x hx)
  have hTsize : ((T x).card:ℝ) ≤ F*((T x ∩ B).card:ℝ) := by
    calc
      _ ≤ M := ht.2.1
      _ = F*(m/(2*(J:ℝ))) := by dsimp [F]; field_simp
      _ ≤ _ := mul_le_mul_of_nonneg_left (hlarge x hx) hF.le
  refine ⟨Finset.card_pos.mp (Nat.cast_pos.mp hcard),hlarge x hx,
    (fun l hl => ht.2.2.1 l (Finset.mem_inter.mp hl).1),
    finiteSeparatedAt_subset Finset.inter_subset_left ht.2.2.2.1,
    normalized_finite_ball_bound_subset hδ.le hK Finset.inter_subset_left hTsize ht.2.2.2.2.1,
    fun l hl => ht.2.2.2.2.2 l (Finset.mem_inter.mp hl).1⟩

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Incidence_FrozenCoarseConfiguration
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The packet-size freezing step as an actual retained coarse configuration.
Its point set, pencils, fine-packet band and total fine count are explicit. -/
namespace Falconer
open scoped BigOperators
attribute [local instance] Classical.propDecidable

theorem frozen_coarse_configuration {δ s t K m M : ℝ}
    (hδ : 0 < δ) (hK : 0 ≤ K) (hm : 0 < m) (hM : 0 < M)
    (P : Finset (Space 2)) (T G : Space 2 → Finset (Space 2)) (hP : P.Nonempty)
    (hPball : NormalizedFiniteBallBound δ t K P)
    (hT : ∀ x ∈ P, m ≤ ((T x).card:ℝ) ∧ ((T x).card:ℝ) ≤ M ∧
      InBoundedLineChart (T x) ∧ FiniteSeparatedAt δ (T x) ∧
      NormalizedFiniteBallBound δ s K (T x) ∧ ∀ l ∈ T x, TubeIncident δ x l)
    (D : ℕ) (hG : ∀ a ∈ P.biUnion T, (G a).Nonempty ∧ (G a).card ≤ D) :
    let J := Nat.log 2 D+1
    let F := 2*(J:ℝ)*M/m
    ∃ R ⊆ P, R.Nonempty ∧ (P.card:ℝ) ≤ F*(R.card:ℝ) ∧
      NormalizedFiniteBallBound δ t (K*F) R ∧
      ∃ U : Space 2 → Finset (Space 2),
        (∀ x ∈ R, U x ⊆ T x ∧ (U x).Nonempty ∧
          m/(2*(J:ℝ)) ≤ ((U x).card:ℝ) ∧ ((U x).card:ℝ) ≤ M ∧
          InBoundedLineChart (U x) ∧ FiniteSeparatedAt δ (U x) ∧
          NormalizedFiniteBallBound δ s (K*F) (U x) ∧ ∀ l ∈ U x, TubeIncident δ x l) ∧
        R.biUnion U ⊆ P.biUnion T ∧
        (∑ a ∈ R.biUnion U, ((G a).card:ℝ)) ≤ ∑ a ∈ P.biUnion T, ((G a).card:ℝ) ∧
        ∃ k : ℕ, ∀ a ∈ R.biUnion U, 2^k ≤ (G a).card ∧ (G a).card < 2^(k+1) := by
  obtain ⟨k,B,hBU,_,hband,R,hRP,hR,hsize,hRball,hU⟩ := freeze_regular_packets
    hδ hK hm hM P T hP hPball hT (fun a => (G a).card) D
    (fun a ha => ⟨(hG a ha).1.card_pos,(hG a ha).2⟩)
  let U := fun x => T x ∩ B
  have hcover : R.biUnion U ⊆ P.biUnion T := by
    intro a ha
    obtain ⟨x,hx,ha⟩ := Finset.mem_biUnion.mp ha
    exact Finset.mem_biUnion.mpr ⟨x,hRP hx,(Finset.mem_inter.mp ha).1⟩
  refine ⟨R,hRP,hR,hsize,hRball,U,?_,hcover,?_,k,?_⟩
  · intro x hx
    obtain ⟨hne,hlo,hchart,hsep,hball,hinc⟩ := hU x hx
    exact ⟨Finset.inter_subset_left,hne,hlo,
      (Nat.cast_le.mpr (Finset.card_le_card Finset.inter_subset_left)).trans (hT x (hRP hx)).2.1,
      hchart,hsep,hball,hinc⟩
  · exact Finset.sum_le_sum_of_subset_of_nonneg hcover (fun a _ _ => Nat.cast_nonneg _)
  · intro a ha
    obtain ⟨x,_,ha⟩ := Finset.mem_biUnion.mp ha
    exact hband a (Finset.mem_inter.mp ha).2

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Incidence_ComparableFrozenPencils
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Select comparable original coarse pencils and then freeze their fine
packet sizes. Both selections retain explicit coarse-point mass. -/
namespace Falconer
open scoped BigOperators
attribute [local instance] Classical.propDecidable

theorem comparable_frozen_pencils {δ s t K : ℝ}
    (hδ : 0 < δ) (hK : 1 ≤ K)
    (P : Finset (Space 2)) (T G : Space 2 → Finset (Space 2)) (hP : P.Nonempty)
    (hPball : NormalizedFiniteBallBound δ t K P)
    (hT : ∀ x ∈ P, (T x).Nonempty ∧ InBoundedLineChart (T x) ∧
      FiniteSeparatedAt δ (T x) ∧ NormalizedFiniteBallBound δ s K (T x) ∧
      ∀ l ∈ T x, TubeIncident δ x l)
    (D : ℕ) (hG : ∀ a ∈ P.biUnion T, (G a).Nonempty ∧ (G a).card ≤ D) :
    let J₁ := Nat.log 2 (P.biUnion T).card+1
    let J₂ := Nat.log 2 D+1
    let F := 4*(J₁:ℝ)*(J₂:ℝ)
    ∃ m : ℝ, 0 < m ∧ ∃ R ⊆ P, R.Nonempty ∧ (P.card:ℝ) ≤ F*(R.card:ℝ) ∧
      NormalizedFiniteBallBound δ t (K*F) R ∧
      ∃ U : Space 2 → Finset (Space 2),
        (∀ x ∈ R, m ≤ ((T x).card:ℝ) ∧ ((T x).card:ℝ) ≤ 2*m ∧
          U x ⊆ T x ∧ (U x).Nonempty ∧
          m/(2*(J₂:ℝ)) ≤ ((U x).card:ℝ) ∧ ((U x).card:ℝ) ≤ 2*m ∧
          InBoundedLineChart (U x) ∧ FiniteSeparatedAt δ (U x) ∧
          NormalizedFiniteBallBound δ s (K*F) (U x) ∧
          ∀ l ∈ U x, TubeIncident δ x l) ∧
        R.biUnion U ⊆ P.biUnion T ∧
        (∑ a ∈ R.biUnion U, ((G a).card:ℝ)) ≤ ∑ a ∈ P.biUnion T, ((G a).card:ℝ) ∧
        ∃ k : ℕ, ∀ a ∈ R.biUnion U, 2^k ≤ (G a).card ∧ (G a).card < 2^(k+1) := by
  let J₁ := Nat.log 2 (P.biUnion T).card+1
  let J₂ := Nat.log 2 D+1
  let F := 4*(J₁:ℝ)*(J₂:ℝ)
  have hJ₁ : 1 ≤ (J₁:ℝ) := by dsimp [J₁]; exact_mod_cast Nat.le_add_left 1 _
  have hJ₂ : 0 < (J₂:ℝ) := by dsimp [J₂]; positivity
  have hK0 := zero_le_one.trans hK
  have hKJ : 0 ≤ K*(J₁:ℝ) := by positivity
  obtain ⟨j,Q,hQP,hQ,hsize,hQball,hband⟩ := uniform_pencil_size_band hδ.le hK0 P T hP hPball
    (fun x hx => (hT x hx).1)
  let m : ℝ := 2^j
  have hm : 0 < m := by dsimp [m]; positivity
  have hTQ (x : Space 2) (hx : x ∈ Q) : m ≤ ((T x).card:ℝ) ∧ ((T x).card:ℝ) ≤ 2*m ∧
      InBoundedLineChart (T x) ∧ FiniteSeparatedAt δ (T x) ∧
      NormalizedFiniteBallBound δ s (K*(J₁:ℝ)) (T x) ∧ ∀ l ∈ T x, TubeIncident δ x l := by
    refine ⟨(hband x hx).1,(hband x hx).2,(hT x (hQP hx)).2.1,(hT x (hQP hx)).2.2.1,?_,
      (hT x (hQP hx)).2.2.2.2⟩
    intro z r hr hr1
    exact ((hT x (hQP hx)).2.2.2.1 z r hr hr1).trans (by
      apply mul_le_mul_of_nonneg_right _ (Nat.cast_nonneg _)
      apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg (hδ.le.trans hr) _)
      exact le_mul_of_one_le_right hK0 hJ₁)
  have hQT : Q.biUnion T ⊆ P.biUnion T := Finset.biUnion_subset_biUnion_of_subset_left T hQP
  obtain ⟨R,hRQ,hR,hsizeR,hRb,U,hU,hUT,hGsum,k,hGband⟩ := frozen_coarse_configuration hδ hKJ hm
    (mul_pos (by norm_num) hm) Q T G hQ hQball hTQ D (fun a ha => hG a (hQT ha))
  have he : 2*(J₂:ℝ)*(2*m)/m = 4*(J₂:ℝ) := by field_simp; ring
  rw [he] at hsizeR hRb hU
  have hconst : (K*(J₁:ℝ))*(4*(J₂:ℝ)) = K*F := by dsimp [F]; ring
  rw [hconst] at hRb hU
  refine ⟨m,hm,R,hRQ.trans hQP,hR,?_,hRb,U,?_,hUT.trans hQT,?_,k,hGband⟩
  · calc
      (P.card:ℝ) ≤ (J₁:ℝ)*(Q.card:ℝ) := hsize
      _ ≤ (J₁:ℝ)*((4*(J₂:ℝ))*(R.card:ℝ)) :=
        mul_le_mul_of_nonneg_left hsizeR (zero_le_one.trans hJ₁)
      _ = _ := by ring
  · intro x hx
    obtain ⟨hsub,hne,hlo,hup,hchart,hsep,hball,hinc⟩ := hU x hx
    exact ⟨(hband x (hRQ hx)).1,(hband x (hRQ hx)).2,hsub,hne,hlo,hup,hchart,hsep,hball,hinc⟩
  · exact hGsum.trans (Finset.sum_le_sum_of_subset_of_nonneg hQT (fun _ _ _ => Nat.cast_nonneg _))

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Incidence_RetainedCoarseIncidences
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Retain the original fine pencils whose coarse labels survive a packet
selection. The point and pencil losses follow from the actual weighted
incidences, rather than being extra regularity assumptions. -/
namespace Falconer
open scoped BigOperators
attribute [local instance] Classical.propDecidable

theorem retain_coarse_incidences {δ s t K m M H B b : ℝ}
    (hδ : 0 ≤ δ) (hK : 0 ≤ K) (hm : 0 < m) (hM : 0 < M)
    (hH : 0 < H) (hB : 0 < B) (hb : 0 < b)
    (P D : Finset (Space 2)) (T : Space 2 → Finset (Space 2)) (q : Space 2 → Space 2)
    (hP : P.Nonempty) (hD : b ≤ (D.card:ℝ))
    (hPball : NormalizedFiniteBallBound δ t K P)
    (hT : ∀ p ∈ P, m ≤ ((T p).card:ℝ) ∧ ((T p).card:ℝ) ≤ M ∧
      NormalizedFiniteBallBound δ s K (T p))
    (hw : ∀ a ∈ D, (∑ p ∈ P, ((T p).card:ℝ)) ≤
      H*B*(coarsePencilWeight P T q a:ℝ)) :
    let E := H*B/b
    let F := 2*E*M/m
    let V := fun p => (T p).filter fun l => q l ∈ D
    ∃ R ⊆ P, R.Nonempty ∧ (P.card:ℝ) ≤ F*(R.card:ℝ) ∧
      NormalizedFiniteBallBound δ t (K*F) R ∧
      ∀ p ∈ R, V p ⊆ T p ∧ m/(2*E) ≤ ((V p).card:ℝ) ∧
        ((V p).card:ℝ) ≤ M ∧ NormalizedFiniteBallBound δ s (K*F) (V p) := by
  let E := H*B/b
  let F := 2*E*M/m
  let V := fun p => (T p).filter fun l => q l ∈ D
  have hE : 0 < E := by dsimp [E]; positivity
  have hPc : 0 < (P.card:ℝ) := Nat.cast_pos.mpr hP.card_pos
  let I := ∑ p ∈ P, ((T p).card:ℝ)
  have hIlow : m*(P.card:ℝ) ≤ I := by
    calc
      _ = ∑ _p ∈ P, m := by simp; ring
      _ ≤ _ := Finset.sum_le_sum fun p hp => (hT p hp).1
  have hI0 : 0 ≤ I := (mul_pos hm hPc).le.trans hIlow
  have hsum : b*I ≤ (H*B)*∑ a ∈ D, (coarsePencilWeight P T q a:ℝ) := by
    calc
      _ ≤ (D.card:ℝ)*I := mul_le_mul_of_nonneg_right hD hI0
      _ = ∑ _a ∈ D, I := by simp
      _ ≤ ∑ a ∈ D, H*B*(coarsePencilWeight P T q a:ℝ) := Finset.sum_le_sum hw
      _ = _ := by rw [Finset.mul_sum]
  have hcounts : (∑ a ∈ D, (coarsePencilWeight P T q a:ℝ)) =
      ∑ p ∈ P, ((V p).card:ℝ) := by
    exact_mod_cast sum_coarsePencilWeight P D T q
  have hretain : (m/E)*(P.card:ℝ) ≤ ∑ p ∈ P, ((V p).card:ℝ) := by
    have hrel : I ≤ E*∑ p ∈ P, ((V p).card:ℝ) := by
      rw [hcounts] at hsum
      calc
        I ≤ ((H*B)*∑ p ∈ P, ((V p).card:ℝ))/b :=
          (le_div_iff₀ hb).2 (by simpa only [mul_comm I b] using hsum)
        _ = _ := by dsimp [E]; ring
    calc
      (m/E)*(P.card:ℝ) = (m*(P.card:ℝ))/E := by ring
      _ ≤ _ := (div_le_iff₀ hE).2 (by simpa only [mul_comm E] using hIlow.trans hrel)
  obtain ⟨R,hRP,hR,hRsize,hRV⟩ := finite_large_weight_subset P
    (fun p => ((V p).card:ℝ)) hP (mul_pos (div_pos hm hE) hPc) hM
    (fun p hp => (Nat.cast_le.mpr (Finset.card_filter_le _ _)).trans (hT p hp).2.1) hretain
  have hsize : (P.card:ℝ) ≤ F*(R.card:ℝ) := by
    have hh := (div_le_iff₀ (mul_pos (by norm_num) hM)).1 hRsize
    have hh' := mul_le_mul_of_nonneg_left hh hE.le
    have hc : m*(P.card:ℝ) ≤ (2*E*M)*(R.card:ℝ) := by
      convert hh' using 1 <;> first | (with_reducible_and_instances rfl) | (field_simp)
    calc
      (P.card:ℝ) = (m*(P.card:ℝ))/m := by field_simp
      _ ≤ ((2*E*M)*(R.card:ℝ))/m := div_le_div_of_nonneg_right hc hm.le
      _ = _ := by dsimp [F]; ring
  refine ⟨R,hRP,hR,hsize,normalized_finite_ball_bound_subset hδ hK hRP hsize hPball,?_⟩
  intro p hp
  have hlo : m/(2*E) ≤ ((V p).card:ℝ) := by
    have hh := hRV p hp
    convert hh using 1
    all_goals try with_reducible_and_instances rfl
    field_simp
  have hcard : ((T p).card:ℝ) ≤ F*((V p).card:ℝ) := by
    have hh := (div_le_iff₀ (mul_pos (by norm_num) hE)).1 hlo
    have hh' := mul_le_mul_of_nonneg_left hh hM.le
    apply (hT p (hRP hp)).2.1.trans
    have hc : m*M ≤ (2*E*M)*((V p).card:ℝ) := by
      first | (convert hh' using 1 <;> ring) | exact (le_of_eq (by ring)).trans (hh'.trans (le_of_eq (by ring)))
    calc
      M = (m*M)/m := by field_simp
      _ ≤ ((2*E*M)*((V p).card:ℝ))/m := div_le_div_of_nonneg_right hc hm.le
      _ = _ := by dsimp [F]; ring
  exact ⟨Finset.filter_subset _ _,hlo,
    (Nat.cast_le.mpr (Finset.card_filter_le _ _)).trans (hT p (hRP hp)).2.1,
    normalized_finite_ball_bound_subset hδ hK (Finset.filter_subset _ _) hcard
      (hT p (hRP hp)).2.2⟩

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Incidence_UniformFrozenCells
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Original uniform fine pencils produce frozen coarse cells at every
intermediate scale. The point restrictions have explicit logarithmic costs. -/
namespace Falconer
open scoped BigOperators
attribute [local instance] Classical.propDecidable

theorem uniform_frozen_cells {δ ρ s K m M : ℝ}
    (hδ : 0 < δ) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1/2) (hδρ : δ ≤ ρ)
    (hs : 0 ≤ s) (hK : 1 ≤ K) (hm : 0 < m) (hM : 0 < M)
    (P C : Finset (Space 2)) (V : Space 2 → Finset (Space 2))
    (q : Space 2 → Space 2) (hC : C.Nonempty) (hCP : C ⊆ P.image q)
    (hnear : ∀ p ∈ P, dist p (q p) ≤ ρ)
    (hchart : ∀ c ∈ C, |c 0| ≤ 1/4 ∧ |c 1| ≤ 1/4)
    (hV : ∀ p ∈ P, m ≤ ((V p).card:ℝ) ∧ ((V p).card:ℝ) ≤ M ∧
      NormalizedFiniteBallBound δ s K (V p) ∧
      ∀ l ∈ V p, |l 0| ≤ 1/2 ∧ TubeIncident δ p l) :
    let Jv := Nat.log 2 (∑ p ∈ P, (V p).card)+1
    let Jg := Nat.log 2 (P.biUnion V).card+1
    let S := fun c => P.filter fun p => q p = c
    ∃ L E F : ℝ, 0 < L ∧ L ≤ 20*(Jg:ℝ)^2 ∧ E = 8*(Jv:ℝ)*(Jg:ℝ) ∧ F = 2*E*M/m ∧
      ∃ w : ℝ, 0 < w ∧ ∃ R ⊆ C, R.Nonempty ∧ (C.card:ℝ) ≤ L*(R.card:ℝ) ∧
      ∃ U A : Space 2 → Finset (Space 2),
      let W := fun p => (V p).filter fun l => roundedIncidentLine ρ (q p) (l 0) ∈ U (q p)
      let G := fineCoarsePacket ρ C (fun c => (S c).biUnion V)
      (∀ c ∈ R,
        w/(2*(Jg:ℝ)) ≤ ((U c).card:ℝ) ∧ ((U c).card:ℝ) ≤ 2*w ∧
        InBoundedLineChart (U c) ∧ FiniteSeparatedAt ρ (U c) ∧
        NormalizedFiniteBallBound ρ s ((2*(K*7^s)*(Jv:ℝ))*L) (U c) ∧
        (∀ a ∈ U c, TubeIncident ρ c a) ∧
        A c ⊆ S c ∧ (A c).Nonempty ∧ ((S c).card:ℝ) ≤ F*((A c).card:ℝ) ∧
        ∀ p ∈ A c, W p ⊆ V p ∧ m/(2*E) ≤ ((W p).card:ℝ) ∧
          ((W p).card:ℝ) ≤ M ∧ NormalizedFiniteBallBound δ s (K*F) (W p) ∧
          ∀ l ∈ W p, ∃ a ∈ U c, l ∈ G a) ∧
      (∑ a ∈ R.biUnion U, ((G a).card:ℝ)) ≤ 13*((P.biUnion V).card:ℝ) ∧
      (∃ k : ℕ, ∀ a ∈ R.biUnion U, 2^k ≤ (G a).card ∧ (G a).card < 2^(k+1)) ∧
      ((∀ a : ℝ, |a| ≤ 1/2 → |lineGridRound ρ a| ≤ 1/2) →
        ∀ c ∈ R, ∀ a ∈ U c, |a 0| ≤ 1/2) := by
  let Jv := Nat.log 2 (∑ p ∈ P, (V p).card)+1
  let Jg := Nat.log 2 (P.biUnion V).card+1
  let S := fun c => P.filter fun p => q p = c
  let ql := fun c (l : Space 2) => roundedIncidentLine ρ c (l 0)
  let G := fineCoarsePacket ρ C (fun c => (S c).biUnion V)
  have hJv : 0 < (Jv:ℝ) := by dsimp [Jv]; positivity
  have hJg : 0 < (Jg:ℝ) := by dsimp [Jg]; positivity
  have hS (c : Space 2) (hc : c ∈ C) : (S c).Nonempty := by
    obtain ⟨p,hp,he⟩ := Finset.mem_image.mp (hCP hc)
    exact ⟨p,Finset.mem_filter.mpr ⟨hp,he⟩⟩
  have hVne (p : Space 2) (hp : p ∈ P) : (V p).Nonempty :=
    Finset.card_pos.mp (Nat.cast_pos.mp (hm.trans_le (hV p hp).1))
  obtain ⟨T,hT⟩ := coarse_cell_pencils hδ.le hρ hρ1 hδρ hs hK P C V q hCP hnear hchart
    (fun p hp => ⟨hVne p hp,(hV p hp).2.2.1,(hV p hp).2.2.2⟩)
  obtain ⟨hGne,_,hGmem,hGsum,hTsum⟩ := original_coarse_packets hδ.le hρ hδρ P C V T q hnear
    (fun c hc => (hchart c hc).1.trans (by norm_num))
    (fun p hp l hl => ⟨((hV p hp).2.2.2 l hl).1.trans (by norm_num),((hV p hp).2.2.2 l hl).2⟩)
    (fun c hc => (hT c hc).1)
  let Kc := 2*(K*7^s)*(Jv:ℝ)
  have hJv1 : 1 ≤ (Jv:ℝ) := by dsimp [Jv]; exact_mod_cast Nat.le_add_left 1 _
  have hKc : 1 ≤ Kc := by
    have h7 := Real.one_le_rpow (by norm_num : (1:ℝ) ≤ 7) hs
    have h1 : 1 ≤ K*7^s := by
      simpa using mul_le_mul hK h7 (by norm_num : (0:ℝ) ≤ 1) (zero_le_one.trans hK)
    dsimp [Kc]
    nlinarith only [mul_le_mul h1 hJv1 (by norm_num : (0:ℝ) ≤ 1) (by positivity : 0 ≤ K*7^s)]
  have hCball : NormalizedFiniteBallBound ρ 0 Kc C := by
    intro z r _ _
    simp only [Real.rpow_zero,mul_one]
    exact (Nat.cast_le.mpr (Finset.card_filter_le _ _)).trans
      (le_mul_of_one_le_left (Nat.cast_nonneg _) hKc)
  have hGmax : ∀ a ∈ C.biUnion T, (G a).Nonempty ∧ (G a).card ≤ (P.biUnion V).card := by
    intro a ha
    exact ⟨hGne a ha,(fineCoarsePacket_card_le _ _ _ _).trans (Finset.card_le_card (by
      intro l hl
      obtain ⟨c,_,hl⟩ := Finset.mem_biUnion.mp hl
      obtain ⟨p,hp,hl⟩ := Finset.mem_biUnion.mp hl
      exact Finset.mem_biUnion.mpr ⟨p,(Finset.mem_filter.mp hp).1,hl⟩))⟩
  obtain ⟨w,hw,R,hRC,hR,hmass,_,U,hU,_,hsum,k,hband⟩ := comparable_frozen_pencils
    hρ hKc C T G hC hCball (fun c hc => ⟨(hT c hc).2.1,(hT c hc).2.2.1,
      (hT c hc).2.2.2.1,(hT c hc).2.2.2.2.1,fun a ha => ((hT c hc).2.2.2.2.2.1 a ha).1⟩)
    (P.biUnion V).card hGmax
  let L := 4*((Nat.log 2 (C.biUnion T).card+1:ℕ):ℝ)*(Jg:ℝ)
  let E := 8*(Jv:ℝ)*(Jg:ℝ)
  let F := 2*E*M/m
  have hL : 0 < L := by dsimp [L]; positivity
  have hE : 0 < E := by dsimp [E]; positivity
  have hcoarse : (C.biUnion T).card ≤ 13*(P.biUnion V).card := by
    exact_mod_cast hTsum.trans (mul_le_mul_of_nonneg_left
      (Nat.cast_le.mpr Finset.card_image_le) (by norm_num : (0:ℝ) ≤ 13))
  have hpow : (P.biUnion V).card < 2^Jg := Nat.lt_pow_succ_log_self (by norm_num) _
  have hlt : (C.biUnion T).card < 2^(Jg+4) := by
    calc
      _ ≤ 13*(P.biUnion V).card := hcoarse
      _ ≤ 16*(P.biUnion V).card := Nat.mul_le_mul_right _ (by norm_num)
      _ < 16*2^Jg := Nat.mul_lt_mul_of_pos_left hpow (by norm_num)
      _ = _ := by rw [pow_add]; norm_num; ring
  have hlog : Nat.log 2 (C.biUnion T).card+1 ≤ 5*Jg := by
    have hh := Nat.log_lt_of_lt_pow' (by omega : Jg+4 ≠ 0) hlt
    have hj : 1 ≤ Jg := by dsimp [Jg]; omega
    omega
  have hLbound : L ≤ 20*(Jg:ℝ)^2 := by
    dsimp [L]
    have hh : ((Nat.log 2 (C.biUnion T).card+1:ℕ):ℝ) ≤ 5*(Jg:ℝ) := by exact_mod_cast hlog
    calc
      _ ≤ 4*(5*(Jg:ℝ))*(Jg:ℝ) := by gcongr
      _ = _ := by ring
  have he : (2*(Jv:ℝ))*(2*w)/(w/(2*(Jg:ℝ))) = E := by dsimp [E]; field_simp; ring
  have hzero (c : Space 2) : NormalizedFiniteBallBound δ 0 K (S c) := by
    intro z r _ _
    simp only [Real.rpow_zero,mul_one]
    exact (Nat.cast_le.mpr (Finset.card_filter_le _ _)).trans
      (le_mul_of_one_le_left (Nat.cast_nonneg _) hK)
  have hretain (c : Space 2) (hc : c ∈ R) := retain_coarse_incidences (H := 2*(Jv:ℝ)) (B := 2*w) (b := w/(2*(Jg:ℝ))) hδ.le
    (zero_le_one.trans hK) hm hM (mul_pos (by norm_num) hJv) (mul_pos (by norm_num) hw)
    (div_pos hw (mul_pos (by norm_num) hJg)) (S c) (U c) V (ql c)
    (hS c (hRC hc)) (hU c hc).2.2.2.2.1 (hzero c)
    (fun p hp => ⟨(hV p (Finset.mem_filter.mp hp).1).1,(hV p (Finset.mem_filter.mp hp).1).2.1,
      (hV p (Finset.mem_filter.mp hp).1).2.2.1⟩) (by
        intro a ha
        have haT := (hU c hc).2.2.1 ha
        have hh := ((hT c (hRC hc)).2.2.2.2.2.1 a haT).2
        exact hh.trans (by
          apply mul_le_mul_of_nonneg_right _ (Nat.cast_nonneg _)
          exact mul_le_mul_of_nonneg_left (hU c hc).2.1 (by positivity)))
  let A := fun c => if hc : c ∈ R then (hretain c hc).choose else ∅
  refine ⟨L,E,F,hL,hLbound,rfl,rfl,w,hw,R,hRC,hR,hmass,U,A,?_,hsum.trans hGsum,
    ⟨k,hband⟩,?_⟩
  · intro c hc
    have ha := (hretain c hc).choose_spec
    have hA : A c = (hretain c hc).choose := dite_eq_left hc
    rw [← hA] at ha
    rw [he] at ha
    refine ⟨(hU c hc).2.2.2.2.1,(hU c hc).2.2.2.2.2.1,
      (hU c hc).2.2.2.2.2.2.1,(hU c hc).2.2.2.2.2.2.2.1,
      (hU c hc).2.2.2.2.2.2.2.2.1,(hU c hc).2.2.2.2.2.2.2.2.2,
      ha.1,ha.2.1,ha.2.2.1,?_⟩
    intro p hp
    have hpc := (Finset.mem_filter.mp (ha.1 hp)).2
    simp only [hpc]
    obtain ⟨hsub,hlo,hup,hball⟩ := ha.2.2.2.2 p hp
    refine ⟨hsub,hlo,hup,hball,?_⟩
    intro l hl
    have hlV := hsub hl
    refine ⟨ql c l,(Finset.mem_filter.mp hl).2,?_⟩
    exact hGmem c (hRC hc) p (Finset.mem_filter.mp (ha.1 hp)).1 hpc l hlV
  · intro hround c hc a ha
    have haT := (hU c hc).2.2.1 ha
    obtain ⟨l,hl,rfl⟩ := Finset.mem_image.mp ((hT c (hRC hc)).1 haT)
    obtain ⟨p,hp,hl⟩ := Finset.mem_biUnion.mp hl
    exact hround (l 0) (((hV p (Finset.mem_filter.mp hp).1).2.2.2 l hl).1)

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Incidence_FrozenPacketProduct
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Product counting for a local union carried by globally frozen packets.
The local factor is arbitrary; no local incidence estimate is assumed. -/
namespace Falconer
open scoped BigOperators
attribute [local instance] Classical.propDecidable

theorem frozen_packet_card_product {n H M : ℝ}
    (hn : 0 < n) (_hH : 0 ≤ H) (hM : 0 ≤ M)
    (A B F V : Finset (Space 2)) (G : Space 2 → Finset (Space 2))
    (hBA : B ⊆ A) (hB : (B.card:ℝ) ≤ M) (hF : F ⊆ B.biUnion G)
    (hband : ∀ a ∈ A, n ≤ ((G a).card:ℝ) ∧ ((G a).card:ℝ) ≤ 2*n)
    (htotal : (∑ a ∈ A, ((G a).card:ℝ)) ≤ H*(V.card:ℝ)) :
    (A.card:ℝ)*(F.card:ℝ) ≤ 2*H*M*(V.card:ℝ) := by
  have hlocal : (F.card:ℝ) ≤ 2*n*M := by
    calc
      _ ≤ ∑ a ∈ B, ((G a).card:ℝ) := by
        exact_mod_cast (Finset.card_le_card hF).trans Finset.card_biUnion_le
      _ ≤ ∑ _a ∈ B, 2*n := Finset.sum_le_sum fun a ha => (hband a (hBA ha)).2
      _ = 2*n*(B.card:ℝ) := by simp; ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hB (by positivity)
  have hglobal : n*(A.card:ℝ) ≤ H*(V.card:ℝ) := by
    calc
      _ = ∑ _a ∈ A, n := by simp; ring
      _ ≤ ∑ a ∈ A, ((G a).card:ℝ) := Finset.sum_le_sum fun a ha => (hband a ha).1
      _ ≤ _ := htotal
  calc
    _ ≤ (A.card:ℝ)*(2*n*M) := mul_le_mul_of_nonneg_left hlocal (Nat.cast_nonneg _)
    _ = 2*M*(n*(A.card:ℝ)) := by ring
    _ ≤ 2*M*(H*(V.card:ℝ)) := mul_le_mul_of_nonneg_left hglobal (by positivity)
    _ = _ := by ring

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Measures_RescaledScaleProduct
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Pencil-normalized scale combination for actual rescaled cell pencils. -/
namespace Falconer
open scoped BigOperators
attribute [local instance] Classical.propDecidable

theorem rescaled_cell_scale_product {δ Δ s t K KP y a m M n H MC mc : ℝ}
    (hδ : 0 < δ) (hΔ : 0 < Δ) (hΔ1 : Δ ≤ 1) (hρ1 : δ/Δ ≤ 1/2)
    (hs : 0 ≤ s) (hK : 1 ≤ K) (hKP : 0 ≤ KP) (hy : |y| ≤ 1)
    (P : Finset (Space 2)) (T : Space 2 → Finset (Space 2)) (hP : P.Nonempty)
    (hcell : ∀ p ∈ P, |p 0-y| ≤ Δ/4 ∧ |p 1-a| ≤ Δ/4)
    (hPsep : FiniteSeparatedAt δ P)
    (hPball : NormalizedFiniteBallBound (δ/Δ) t KP
      (P.image (localPacketPoint Δ y a)))
    (hT : ∀ p ∈ P, (T p).Nonempty ∧ m ≤ ((T p).card:ℝ) ∧ ((T p).card:ℝ) ≤ M ∧
      NormalizedFiniteBallBound δ s K (T p) ∧
      ∀ l ∈ T p, |l 0| ≤ 1/2 ∧ TubeIncident δ p l)
    (D : ℕ) (hD : ∀ p ∈ P, (T p).card ≤ D)
    (hm : 0 < m) (hmc : 0 < mc) (hn : 0 < n) (hH : 0 ≤ H) (hMC : 0 ≤ MC)
    (A B V : Finset (Space 2)) (G : Space 2 → Finset (Space 2))
    (hBA : B ⊆ A) (hB : (B.card:ℝ) ≤ MC)
    (hcover : ∀ p ∈ P, ∀ l ∈ T p, ∃ b ∈ B, l ∈ G b)
    (hband : ∀ b ∈ A, n ≤ ((G b).card:ℝ) ∧ ((G b).card:ℝ) ≤ 2*n)
    (htotal : (∑ b ∈ A, ((G b).card:ℝ)) ≤ H*(V.card:ℝ)) :
    let J := Nat.log 2 D+1
    ∃ k : ℕ, ∃ Q ⊆ P.image (localPacketPoint Δ y a), Q.Nonempty ∧
      (P.card:ℝ) ≤ (J:ℝ)*(Q.card:ℝ) ∧
      (∀ p ∈ Q, |p 0| ≤ 1/4 ∧ |p 1| ≤ 1/4) ∧
      FiniteSeparatedAt (δ/Δ) Q ∧ NormalizedFiniteBallBound (δ/Δ) t (KP*(J:ℝ)) Q ∧
      ∃ U : Space 2 → Finset (Space 2),
        (∀ p ∈ Q, (U p).Nonempty ∧ InBoundedLineChart (U p) ∧
          FiniteSeparatedAt (δ/Δ) (U p) ∧
          NormalizedFiniteBallBound (δ/Δ) s (2*((K*3^s)*7^s)*(J:ℝ)) (U p) ∧
          (∀ l ∈ U p, TubeIncident (δ/Δ) p l) ∧
          m/(2*(J:ℝ)*(2:ℝ)^k) ≤ ((U p).card:ℝ) ∧
          ((U p).card:ℝ) ≤ M/(2:ℝ)^k) ∧
        ((A.card:ℝ)/mc)*(((Q.biUnion U).card:ℝ)/(m/(2*(J:ℝ)*(2:ℝ)^k))) ≤
          (52*(J:ℝ)*H*(MC/mc))*((V.card:ℝ)/m) ∧
        ((∀ a : ℝ, |a| ≤ 1/2 → |lineGridRound (δ/Δ) a| ≤ 1/2) →
          ∀ p ∈ Q, ∀ l ∈ U p, |l 0| ≤ 1/2) := by
  obtain ⟨k,Q,hQP,hQ,hmass,hsmall,hsep,hball,U,hU,hlocal,hslopes⟩ :=
    rescaled_cell_packet_refinement hδ hΔ hΔ1 hρ1 hs hK hKP hy P T hP hcell hPsep hPball hT D hD
  refine ⟨k,Q,hQP,hQ,hmass,hsmall,hsep,hball,U,hU,?_,hslopes⟩
  let J := Nat.log 2 D+1
  have hJ : 0 < (J:ℝ) := by dsimp [J]; positivity
  have hF : P.biUnion T ⊆ B.biUnion G := by
    intro l hl
    obtain ⟨p,hp,hl⟩ := Finset.mem_biUnion.mp hl
    obtain ⟨b,hb,hl⟩ := hcover p hp l hl
    exact Finset.mem_biUnion.mpr ⟨b,hb,hl⟩
  have hprod := frozen_packet_card_product hn hH hMC A B (P.biUnion T) V G hBA hB hF hband htotal
  have hraw : (A.card:ℝ)*((2:ℝ)^k*((Q.biUnion U).card:ℝ)) ≤ 26*H*MC*(V.card:ℝ) := calc
    _ ≤ (A.card:ℝ)*(13*((P.biUnion T).card:ℝ)) := mul_le_mul_of_nonneg_left hlocal (Nat.cast_nonneg _)
    _ = 13*((A.card:ℝ)*((P.biUnion T).card:ℝ)) := by ring
    _ ≤ 13*(2*H*MC*(V.card:ℝ)) := mul_le_mul_of_nonneg_left hprod (by norm_num)
    _ = _ := by ring
  have hfactor : 0 ≤ 2*(J:ℝ)/(mc*m) := by positivity
  calc
    _ = ((A.card:ℝ)*((2:ℝ)^k*((Q.biUnion U).card:ℝ)))*(2*(J:ℝ)/(mc*m)) := by field_simp; ring
    _ ≤ (26*H*MC*(V.card:ℝ))*(2*(J:ℝ)/(mc*m)) := mul_le_mul_of_nonneg_right hraw hfactor
    _ = _ := by ring

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Estimates_UniformScaleCombination
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The scale-product construction for original cell configurations. Coarse
pencils and every local pencil are constructed, with explicit logarithmic losses. -/
namespace Falconer
open scoped BigOperators
attribute [local instance] Classical.propDecidable

theorem uniform_scale_combination {δ ρ s t K KP m M : ℝ}
    (hδ : 0 < δ) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1/4) (hδρ : δ ≤ ρ)
    (hs : 0 ≤ s) (hK : 1 ≤ K) (hKP : 0 ≤ KP) (hm : 0 < m) (hM : 0 < M)
    (P C : Finset (Space 2)) (V : Space 2 → Finset (Space 2))
    (q : Space 2 → Space 2) (hC : C.Nonempty) (hCP : C ⊆ P.image q)
    (hnear : ∀ p ∈ P, dist p (q p) ≤ ρ)
    (hchart : ∀ c ∈ C, |c 0| ≤ 1/4 ∧ |c 1| ≤ 1/4)
    (hPsep : FiniteSeparatedAt δ P)
    (hPball : ∀ c ∈ C, NormalizedFiniteBallBound (δ/(4*ρ)) t KP
      ((P.filter fun p => q p = c).image (localPacketPoint (4*ρ) (c 0) (c 1))))
    (hV : ∀ p ∈ P, m ≤ ((V p).card:ℝ) ∧ ((V p).card:ℝ) ≤ M ∧
      NormalizedFiniteBallBound δ s K (V p) ∧
      ∀ l ∈ V p, |l 0| ≤ 1/2 ∧ TubeIncident δ p l) :
    let Jv := Nat.log 2 (∑ p ∈ P, (V p).card)+1
    let Jg := Nat.log 2 (P.biUnion V).card+1
    let S := fun c => P.filter fun p => q p = c
    ∃ L E F w : ℝ, 0 < L ∧ L ≤ 20*(Jg:ℝ)^2 ∧ E = 8*(Jv:ℝ)*(Jg:ℝ) ∧
      F = 2*E*M/m ∧ 0 < w ∧
      ∃ R ⊆ C, R.Nonempty ∧ (C.card:ℝ) ≤ L*(R.card:ℝ) ∧
      ∃ U : Space 2 → Finset (Space 2),
        (∀ c ∈ R, w/(2*(Jg:ℝ)) ≤ ((U c).card:ℝ) ∧ ((U c).card:ℝ) ≤ 2*w ∧
          InBoundedLineChart (U c) ∧ FiniteSeparatedAt ρ (U c) ∧
          NormalizedFiniteBallBound ρ s ((2*(K*7^s)*(Jv:ℝ))*L) (U c) ∧
          ∀ a ∈ U c, TubeIncident ρ c a) ∧
        ((∀ a : ℝ, |a| ≤ 1/2 → |lineGridRound ρ a| ≤ 1/2) →
          ∀ c ∈ R, ∀ a ∈ U c, |a 0| ≤ 1/2) ∧
        ∀ c ∈ R, ∃ j : ℕ, ∃ Q ⊆ (S c).image (localPacketPoint (4*ρ) (c 0) (c 1)),
          Q.Nonempty ∧ ((S c).card:ℝ) ≤ (F*(Jg:ℝ))*(Q.card:ℝ) ∧
          (∀ p ∈ Q, |p 0| ≤ 1/4 ∧ |p 1| ≤ 1/4) ∧
          FiniteSeparatedAt (δ/(4*ρ)) Q ∧
          NormalizedFiniteBallBound (δ/(4*ρ)) t ((KP*F)*(Jg:ℝ)) Q ∧
          ∃ T : Space 2 → Finset (Space 2),
            (∀ p ∈ Q, (T p).Nonempty ∧ InBoundedLineChart (T p) ∧
              FiniteSeparatedAt (δ/(4*ρ)) (T p) ∧
              NormalizedFiniteBallBound (δ/(4*ρ)) s (2*(((K*F)*3^s)*7^s)*(Jg:ℝ)) (T p) ∧
              (∀ l ∈ T p, TubeIncident (δ/(4*ρ)) p l) ∧
              (m/(2*E))/(2*(Jg:ℝ)*(2:ℝ)^j) ≤ ((T p).card:ℝ) ∧
              ((T p).card:ℝ) ≤ M/(2:ℝ)^j) ∧
            (((R.biUnion U).card:ℝ)/(w/(2*(Jg:ℝ))))*
              (((Q.biUnion T).card:ℝ)/((m/(2*E))/(2*(Jg:ℝ)*(2:ℝ)^j))) ≤
                (43264*(Jv:ℝ)*(Jg:ℝ)^3)*(((P.biUnion V).card:ℝ)/m) ∧
            ((∀ a : ℝ, |a| ≤ 1/2 → |lineGridRound (δ/(4*ρ)) a| ≤ 1/2) →
              ∀ p ∈ Q, ∀ l ∈ T p, |l 0| ≤ 1/2) := by
  let Jv := Nat.log 2 (∑ p ∈ P, (V p).card)+1
  let Jg := Nat.log 2 (P.biUnion V).card+1
  let S := fun c => P.filter fun p => q p = c
  obtain ⟨L,E,F,hL,hLb,hEeq,hFeq,w,hw,R,hRC,hR,hcount,U,A,hdata,hGsum,⟨k,hGband⟩,hslopes⟩ :=
    uniform_frozen_cells hδ hρ (hρ1.trans (by norm_num)) hδρ hs hK hm hM P C V q hC hCP hnear hchart hV
  let W := fun p => (V p).filter fun l => roundedIncidentLine ρ (q p) (l 0) ∈ U (q p)
  let G := fineCoarsePacket ρ C (fun c => (S c).biUnion V)
  have hJv : 0 < (Jv:ℝ) := by dsimp [Jv]; positivity
  have hJg : 0 < (Jg:ℝ) := by dsimp [Jg]; positivity
  have hE : 0 < E := by rw [hEeq]; positivity
  have hF : 0 < F := by rw [hFeq]; positivity
  refine ⟨L,E,F,w,hL,hLb,hEeq,hFeq,hw,R,hRC,hR,hcount,U,?_,hslopes,?_⟩
  · intro c hc
    obtain ⟨hl,hu,hch,hsep,hreg,hinc,_⟩ := hdata c hc
    exact ⟨hl,hu,hch,hsep,hreg,hinc⟩
  intro c hc
  obtain ⟨_,hUmax,_,_,_,_,hAS,hA,hAmass,hfine⟩ := hdata c hc
  have hAP : A c ⊆ P := hAS.trans (Finset.filter_subset _ _)
  have hF1 : 1 ≤ F := by
    have ha : 0 < ((A c).card:ℝ) := Nat.cast_pos.mpr hA.card_pos
    have hs : ((A c).card:ℝ) ≤ ((S c).card:ℝ) := Nat.cast_le.mpr (Finset.card_le_card hAS)
    nlinarith only [ha,hs,hAmass]
  have hKF : 1 ≤ K*F := by
    simpa using mul_le_mul hK hF1 (by norm_num : (0:ℝ) ≤ 1) (zero_le_one.trans hK)
  have hpoint : NormalizedFiniteBallBound (δ/(4*ρ)) t (KP*F)
      ((A c).image (localPacketPoint (4*ρ) (c 0) (c 1))) := by
    have himass : (((S c).image (localPacketPoint (4*ρ) (c 0) (c 1))).card:ℝ) ≤
        F*(((A c).image (localPacketPoint (4*ρ) (c 0) (c 1))).card:ℝ) := by
      simpa only [Finset.card_image_of_injective _ (localPacketPoint_injective (by positivity : 0 < 4*ρ) _ _)] using hAmass
    exact normalized_finite_ball_bound_subset (by positivity) hKP (Finset.image_subset_image hAS) himass (hPball c (hRC hc))
  have hcell : ∀ p ∈ A c, |p 0-c 0| ≤ (4*ρ)/4 ∧ |p 1-c 1| ≤ (4*ρ)/4 := by
    intro p hp
    have hh : dist p c ≤ ρ := by simpa only [(Finset.mem_filter.mp (hAS hp)).2] using hnear p (hAP hp)
    constructor
    · exact (show |p 0-c 0| ≤ dist p c by simpa only [Real.dist_eq] using PiLp.dist_apply_le p c 0).trans (by linarith only [hh])
    · exact (show |p 1-c 1| ≤ dist p c by simpa only [Real.dist_eq] using PiLp.dist_apply_le p c 1).trans (by linarith only [hh])
  have hWdata : ∀ p ∈ A c, (W p).Nonempty ∧ m/(2*E) ≤ ((W p).card:ℝ) ∧
      ((W p).card:ℝ) ≤ M ∧ NormalizedFiniteBallBound δ s (K*F) (W p) ∧
      ∀ l ∈ W p, |l 0| ≤ 1/2 ∧ TubeIncident δ p l := by
    intro p hp
    obtain ⟨hsub,hlo,hup,hreg,_⟩ := hfine p hp
    exact ⟨Finset.card_pos.mp (Nat.cast_pos.mp ((by positivity : 0 < m/(2*E)).trans_le hlo)),
      hlo,hup,hreg,fun l hl => (hV p (hAP hp)).2.2.2 l (hsub hl)⟩
  have hWD : ∀ p ∈ A c, (W p).card ≤ (P.biUnion V).card := by
    intro p hp
    exact Finset.card_le_card (((hfine p hp).1).trans (Finset.subset_biUnion_of_mem V (hAP hp)))
  have hGbandR : ∀ b ∈ R.biUnion U, (2:ℝ)^k ≤ ((G b).card:ℝ) ∧ ((G b).card:ℝ) ≤ 2*(2:ℝ)^k := by
    intro b hb
    have hh := hGband b hb
    constructor
    · exact_mod_cast hh.1
    · have hi : ((G b).card:ℝ) < (2:ℝ)^(k+1) := by exact_mod_cast hh.2
      simpa only [pow_succ,mul_comm] using hi.le
  obtain ⟨j,Q,hQA,hQ,hsize,hsmall,hsep,hreg,T,hT,hproduct,hlocalSlopes⟩ := rescaled_cell_scale_product
    hδ (by positivity : 0 < 4*ρ) (by linarith only [hρ1])
    ((div_le_iff₀ (by positivity : 0 < 4*ρ)).2 (by linarith only [hδρ,hρ])) hs hKF
    (mul_nonneg hKP hF.le) ((hchart c (hRC hc)).1.trans (by norm_num)) (A c) W hA hcell
    (finiteSeparatedAt_subset hAP hPsep) hpoint hWdata (P.biUnion V).card hWD
    (by positivity : 0 < m/(2*E)) (by positivity : 0 < w/(2*(Jg:ℝ)))
    (by positivity : 0 < (2:ℝ)^k) (by norm_num : (0:ℝ) ≤ 13) (by positivity : 0 ≤ 2*w)
    (R.biUnion U) (U c) (P.biUnion V) G (Finset.subset_biUnion_of_mem U hc) hUmax
    (fun p hp l hl => (hfine p hp).2.2.2.2 l hl) hGbandR hGsum
  refine ⟨j,Q,hQA.trans (Finset.image_subset_image hAS),hQ,?_,hsmall,hsep,hreg,T,hT,?_,hlocalSlopes⟩
  · calc
      _ ≤ F*((A c).card:ℝ) := hAmass
      _ ≤ F*((Jg:ℝ)*(Q.card:ℝ)) := mul_le_mul_of_nonneg_left hsize hF.le
      _ = _ := by ring
  · convert hproduct using 1
    all_goals try with_reducible_and_instances rfl
    rw [hEeq]
    field_simp
    ring

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Measures_EndpointScaleProduct
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual scale-product step on dyadic endpoint configurations. Both
outputs stay in the same fixed quarter chart, with the same slope interval. -/
namespace Falconer
open Set Regularization
open scoped BigOperators
attribute [local instance] Classical.propDecidable

theorem quarter_endpoint_scale_product {N a b c : ℕ} (hac : a ≤ c) (hcb : c ≤ b)
    (Q : DyadicCube 2) (hQ : Q.side = 1) (C : Finset (CellPath 2))
    (hC : C ⊆ cubePaths 2 N) (hbN : b ≤ N) (p₀ : CellPath 2)
    (hp₀ : p₀ ∈ C.image (List.take a)) {s t K KP m M : ℝ}
    (hs : 0 ≤ s) (hK : 1 ≤ K) (hKP : 0 ≤ KP) (hm : 0 < m) (hM : 0 < M)
    (hball : ∀ r ∈ prefixChildren C a c p₀,
      NormalizedFiniteBallBound (1/(2:ℝ)^(b-c+2)) t KP (quarterEndpointSet Q C c b r))
    (V : Space 2 → Finset (Space 2))
    (hV : ∀ x ∈ quarterEndpointSet Q C a b p₀,
      m ≤ ((V x).card:ℝ) ∧ ((V x).card:ℝ) ≤ M ∧
      NormalizedFiniteBallBound (1/(2:ℝ)^(b-a+2)) s K (V x) ∧
      ∀ l ∈ V x, |l 0| ≤ 1/2 ∧ TubeIncident (1/(2:ℝ)^(b-a+2)) x l) :
    let P := quarterEndpointSet Q C a b p₀
    let D := quarterEndpointSet Q C a c p₀
    let ρ := 1/(2:ℝ)^(c-a+2)
    let δ' := 1/(2:ℝ)^(b-c+2)
    let Jv := Nat.log 2 (∑ x ∈ P, (V x).card)+1
    let Jg := Nat.log 2 (P.biUnion V).card+1
    ∃ L E F w : ℝ, 0 < L ∧ L ≤ 20*(Jg:ℝ)^2 ∧ E = 8*(Jv:ℝ)*(Jg:ℝ) ∧
      F = 2*E*M/m ∧ 0 < w ∧ ∃ R ⊆ D, R.Nonempty ∧ (D.card:ℝ) ≤ L*(R.card:ℝ) ∧
      ∃ U : Space 2 → Finset (Space 2),
        (∀ z ∈ R, w/(2*(Jg:ℝ)) ≤ ((U z).card:ℝ) ∧ ((U z).card:ℝ) ≤ 2*w ∧
          InBoundedLineChart (U z) ∧ FiniteSeparatedAt ρ (U z) ∧
          NormalizedFiniteBallBound ρ s ((2*(K*7^s)*(Jv:ℝ))*L) (U z) ∧
          ∀ l ∈ U z, |l 0| ≤ 1/2 ∧ TubeIncident ρ z l) ∧
        ∀ r ∈ prefixChildren C a c p₀, quarterEndpointPoint Q a p₀ r ∈ R →
          ∃ j : ℕ, ∃ P' ⊆ quarterEndpointSet Q C c b r,
            P'.Nonempty ∧ ((quarterEndpointSet Q C c b r).card:ℝ) ≤ (F*(Jg:ℝ))*(P'.card:ℝ) ∧
            (∀ x ∈ P', |x 0| ≤ 1/4 ∧ |x 1| ≤ 1/4) ∧ FiniteSeparatedAt δ' P' ∧
            NormalizedFiniteBallBound δ' t ((KP*F)*(Jg:ℝ)) P' ∧
            ∃ T : Space 2 → Finset (Space 2),
              (∀ x ∈ P', (T x).Nonempty ∧ InBoundedLineChart (T x) ∧
                FiniteSeparatedAt δ' (T x) ∧
                NormalizedFiniteBallBound δ' s (2*(((K*F)*3^s)*7^s)*(Jg:ℝ)) (T x) ∧
                (∀ l ∈ T x, |l 0| ≤ 1/2 ∧ TubeIncident δ' x l) ∧
                (m/(2*E))/(2*(Jg:ℝ)*(2:ℝ)^j) ≤ ((T x).card:ℝ) ∧
                ((T x).card:ℝ) ≤ M/(2:ℝ)^j) ∧
              (((R.biUnion U).card:ℝ)/(w/(2*(Jg:ℝ))))*
                (((P'.biUnion T).card:ℝ)/((m/(2*E))/(2*(Jg:ℝ)*(2:ℝ)^j))) ≤
                  (43264*(Jv:ℝ)*(Jg:ℝ)^3)*(((P.biUnion V).card:ℝ)/m) := by
  let P := quarterEndpointSet Q C a b p₀
  let D := quarterEndpointSet Q C a c p₀
  let δ := 1/(2:ℝ)^(b-a+2)
  let ρ := 1/(2:ℝ)^(c-a+2)
  let Jv := Nat.log 2 (∑ x ∈ P, (V x).card)+1
  let Jg := Nat.log 2 (P.biUnion V).card+1
  obtain ⟨q,hD,himage,hnear,hsmall,hsep,hlocal,hfibers,hδ,hρ,hρ1,hδρ⟩ :=
    quarter_endpoint_scale_inputs hac hcb Q hQ C hC hbN p₀ hp₀ hball
  obtain ⟨L,E,F,w,hL,hLb,hE,hF,hw,R,hRD,hR,hmass,U,hU,hUslope,hcells⟩ :=
    uniform_scale_combination hδ hρ hρ1 hδρ hs hK hKP hm hM P D V q hD
      (show D ⊆ P.image q from himage.subset) hnear hsmall hsep hlocal hV
  refine ⟨L,E,F,w,hL,hLb,hE,hF,hw,R,hRD,hR,hmass,U,?_,?_⟩
  · intro z hz
    obtain ⟨hlo,hhi,hch,hsp,hb,hinc⟩ := hU z hz
    refine ⟨hlo,hhi,hch,hsp,hb,?_⟩
    intro l hl
    exact ⟨hUslope (fun x hx => lineGridRound_dyadic_half (c-a+1) hx) z hz l hl,hinc l hl⟩
  · intro r hr hrR
    obtain ⟨j,P',hsub,hP',hcount,hch,hsp,hb,T,hT,hproduct,hTslope⟩ := hcells _ hrR
    have heq := hfibers r hr
    have hcard : ((P.filter fun x => q x = quarterEndpointPoint Q a p₀ r).card:ℝ) =
        ((quarterEndpointSet Q C c b r).card:ℝ) := by
      rw [← heq,Finset.card_image_of_injective _ (localPacketPoint_injective (by positivity) _ _)]
    rw [heq] at hsub
    rw [hcard] at hcount
    have hmesh : δ/(4*ρ) = 1/(2:ℝ)^(b-c+2) := dyadic_endpoint_local_mesh hac hcb
    rw [hmesh] at hsp hb hT
    refine ⟨j,P',hsub,hP',hcount,hch,hsp,hb,T,?_,hproduct⟩
    intro x hx
    obtain ⟨hne,hchart,hseparated,hregular,hinc,hlo,hhi⟩ := hT x hx
    refine ⟨hne,hchart,hseparated,hregular,?_,hlo,hhi⟩
    intro l hl
    refine ⟨hTslope ?_ x hx l hl,hinc l hl⟩
    intro u hu
    rw [hmesh]
    exact lineGridRound_dyadic_half (b-c+1) hu

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Recursion_UniformScaleBudgets
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Uniform depth bounds for the actual scale-product costs. Each pencil
is separated individually; separation of their entire union is not assumed. -/
namespace Falconer
open scoped BigOperators
attribute [local instance] Classical.propDecidable

theorem separated_pencil_configuration_logs (N : ℕ)
    (P : Finset (Space 2)) (V : Space 2 → Finset (Space 2))
    (hP : InBoundedLineChart P) (hPsep : FiniteSeparatedAt (1/(2:ℝ)^N) P)
    (hV : ∀ x ∈ P, InBoundedLineChart (V x) ∧ FiniteSeparatedAt (1/(2:ℝ)^N) (V x)) :
    Nat.log 2 (∑ x ∈ P, (V x).card)+1 ≤ 4*N+11 ∧
      Nat.log 2 (P.biUnion V).card+1 ≤ 4*N+11 := by
  have hPcard := bounded_planar_card_dyadic N P hP hPsep
  have hsum : ∑ x ∈ P, (V x).card ≤ 2^(4*N+10) := by
    calc
      _ ≤ ∑ _x ∈ P, 2^(2*N+5) := Finset.sum_le_sum fun x hx =>
        bounded_planar_card_dyadic N (V x) (hV x hx).1 (hV x hx).2
      _ = P.card*2^(2*N+5) := by simp
      _ ≤ 2^(2*N+5)*2^(2*N+5) := Nat.mul_le_mul_right _ hPcard
      _ = _ := by rw [← pow_add]; congr 1; omega
  constructor
  · simpa only [Nat.add_assoc] using packet_log_of_card_bound hsum
  · have hcard : (P.biUnion V).card ≤ 2^(4*N+10) := Finset.card_biUnion_le.trans hsum
    simpa only [Nat.add_assoc] using packet_log_of_card_bound hcard

theorem uniform_scale_cost_bounds {α β H L E F K KP R s : ℝ}
    (hα : 0 ≤ α) (hβ : 0 ≤ β) (hH : 0 ≤ H) (hαH : α ≤ H) (hβH : β ≤ H)
    (hL : 0 ≤ L) (hLb : L ≤ 20*β^2) (hE : E = 8*α*β) (hF : F = 2*E*R)
    (hK : 0 ≤ K) (hKP : 0 ≤ KP) (hR : 0 ≤ R) (hs : s ≤ 1) :
    L ≤ 20*H^2 ∧ E ≤ 8*H^2 ∧ F ≤ 16*R*H^2 ∧
      (2*(K*7^s)*α)*L ≤ 280*K*H^3 ∧
      2*(((K*F)*3^s)*7^s)*β ≤ 672*K*R*H^3 ∧
      (KP*F)*β ≤ 16*KP*R*H^3 ∧
      4*E*β*R ≤ 32*R*H^3 ∧
      43264*α*β^3 ≤ 43264*H^4 := by
  have h7 : (7:ℝ)^s ≤ 7 := by
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le (by norm_num : (1:ℝ) ≤ 7) hs
  have h3 : (3:ℝ)^s ≤ 3 := by
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le (by norm_num : (1:ℝ) ≤ 3) hs
  have hE0 : 0 ≤ E := by rw [hE]; positivity
  have hF0 : 0 ≤ F := by rw [hF]; positivity
  have hLH : L ≤ 20*H^2 := hLb.trans (by gcongr)
  have hEH : E ≤ 8*H^2 := by rw [hE]; nlinarith only [mul_le_mul hαH hβH hβ hH]
  have hFH : F ≤ 16*R*H^2 := by
    rw [hF]
    calc
      _ ≤ 2*(8*H^2)*R := by gcongr
      _ = _ := by ring
  refine ⟨hLH,hEH,hFH,?_,?_,?_,?_,?_⟩
  · calc
      _ ≤ (2*(K*7)*H)*(20*H^2) := by gcongr
      _ = _ := by ring
  · calc
      _ ≤ 2*(((K*(16*R*H^2))*3)*7)*H := by gcongr
      _ = _ := by ring
  · calc
      _ ≤ (KP*(16*R*H^2))*H := by gcongr
      _ = _ := by ring
  · calc
      _ ≤ 4*(8*H^2)*H*R := by gcongr
      _ = _ := by ring
  · calc
      _ ≤ 43264*H*H^3 := by gcongr
      _ = _ := by ring

theorem rescaled_pencil_size_ratio {m M E β : ℝ}
    (hm : 0 < m) (hE : 0 < E) (hβ : 0 < β) (j : ℕ) :
    (M/(2:ℝ)^j)/((m/(2*E))/(2*β*(2:ℝ)^j)) = 4*E*β*(M/m) := by
  field_simp
  ring

theorem coarse_pencil_size_ratio {w β : ℝ} (hw : 0 < w) (hβ : 0 < β) :
    (2*w)/(w/(2*β)) = 4*β := by
  field_simp
  ring

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Incidence_IncidenceProductChain
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Finite composition of the actual pencil-normalized scale ratios.
The terminal estimate needs only a single nonempty pencil. -/
namespace Falconer
open scoped BigOperators

theorem pencil_union_ratio_one_le {m : ℝ} (hm : 0 < m)
    (P : Finset (Space 2)) (V : Space 2 → Finset (Space 2)) (hP : P.Nonempty)
    (hV : ∀ x ∈ P, m ≤ ((V x).card:ℝ)) :
    1 ≤ ((P.biUnion V).card:ℝ)/m := by
  classical
  obtain ⟨x,hx⟩ := hP
  apply (le_div_iff₀ hm).2
  simpa only [one_mul] using (hV x hx).trans
    (Nat.cast_le.mpr (Finset.card_le_card (Finset.subset_biUnion_of_mem V hx)))

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Recursion_ProfileEndpointBound
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The induction statement retains the original reference profile. Its
single budget bounds parent mass loss, pencil regularity and pencil size ratio. -/
namespace Falconer
open Set Regularization
attribute [local instance] Classical.propDecidable

theorem QuarterPencilData.mono {δ s U W m : ℝ} {P P' : Finset (Space 2)}
    {V : Space 2 → Finset (Space 2)} (h : QuarterPencilData δ s U m P V)
    (hδ : 0 ≤ δ) (hm : 0 ≤ m) (hUW : U ≤ W) (hP : P' ⊆ P) :
    QuarterPencilData δ s W m P' V := by
  intro x hx
  obtain ⟨hlo,hhi,hch,hsep,hball,hinc⟩ := h x (hP hx)
  exact ⟨hlo,hhi.trans (mul_le_mul_of_nonneg_right hUW hm),hch,hsep,
    normalizedFiniteBallBound_mono_constant hδ hUW hball,hinc⟩

theorem profileEndpointBound_trivial (N B K : ℕ) (L : Finset (CellPath 2))
    (f : CellPath 2 → List ℕ) (p : CellPath 2) (Q : DyadicCube 2)
    (i j : ℕ) (s W : ℝ) : ProfileEndpointBound N B K L f p Q i j s W 1 := by
  intro L' g q a₀ r₀ hL' C S hsub hmass ha₀ p₀ hp₀ m hm V Z hV
  apply pencil_union_ratio_one_le hm Z V
  · exact ((prefixFiber_nonempty hp₀).image _).image _
  · intro x hx
    exact (hV x hx).1

theorem ProfileEndpointBound.mono_budget {N B K i j : ℕ} {L : Finset (CellPath 2)}
    {f : CellPath 2 → List ℕ} {p : CellPath 2} {Q : DyadicCube 2} {s U W A : ℝ}
    (h : ProfileEndpointBound N B K L f p Q i j s W A) (hUW : U ≤ W) :
    ProfileEndpointBound N B K L f p Q i j s U A := by
  intro L' g q a₀ r₀ hL' C S hsub hmass ha₀ p₀ hp₀ m hm V Z hV
  exact h L' g q a₀ r₀ hL' hsub
    (hmass.trans (mul_le_mul_of_nonneg_right hUW (Nat.cast_nonneg _))) ha₀ p₀ hp₀ m hm V
    (hV.mono (by positivity) hm.le hUW Finset.Subset.rfl)

theorem ProfileEndpointBound.mono_value {N B K i j : ℕ} {L : Finset (CellPath 2)}
    {f : CellPath 2 → List ℕ} {p : CellPath 2} {Q : DyadicCube 2} {s W A D : ℝ}
    (h : ProfileEndpointBound N B K L f p Q i j s W A) (hDA : D ≤ A) :
    ProfileEndpointBound N B K L f p Q i j s W D := by
  intro L' g q a₀ r₀ hL' C S hsub hmass ha₀ p₀ hp₀ m hm V Z hV
  exact hDA.trans (h L' g q a₀ r₀ hL' hsub hmass ha₀ p₀ hp₀ m hm V hV)

theorem profileEndpointBound_retained_subset {N B K : ℕ} {L L' : Finset (CellPath 2)}
    (hL : L ⊆ cubePaths 2 N) (hL' : L' ⊆ cubePaths 2 N)
    (f g : CellPath 2 → List ℕ) (p q : CellPath 2) (Q : DyadicCube 2) (hQ : Q.side = 1)
    {i j : ℕ} (hji : j ≤ i) (hi : i ≤ K) {a₀ : ℕ} (r₀ : CellPath 2)
    (hsub : classLeaves L' (blockLabel L' N B g K) (blockLabel L' N B g K q) ⊆
      prefixFiber (classLeaves L (blockLabel L N B f K) (blockLabel L N B f K p)) a₀ r₀)
    {W U H W' A s m : ℝ} (hW : 0 ≤ W) (hH : 0 ≤ H) (hm : 0 < m)
    (hmass : ((prefixFiber (classLeaves L (blockLabel L N B f K)
      (blockLabel L N B f K p)) a₀ r₀).card:ℝ) ≤
        W*((classLeaves L' (blockLabel L' N B g K) (blockLabel L' N B g K q)).card:ℝ))
    (ha₀ : a₀ ≤ blockDepth N B i) (p₀ : CellPath 2)
    (hp₀ : p₀ ∈ (classLeaves L' (blockLabel L' N B g K) (blockLabel L' N B g K q)).image
      (List.take (blockDepth N B i)))
    (P : Finset (Space 2)) (hP : P.Nonempty)
    (hPsub : P ⊆ quarterEndpointSet Q
      (classLeaves L' (blockLabel L' N B g K) (blockLabel L' N B g K q))
      (blockDepth N B i) (blockDepth N B j) p₀)
    (hsize : ((quarterEndpointSet Q
      (classLeaves L' (blockLabel L' N B g K) (blockLabel L' N B g K q))
      (blockDepth N B i) (blockDepth N B j) p₀).card:ℝ) ≤ H*(P.card:ℝ))
    (hbudget : (W*(2:ℝ)^(2*i))*((H*(2:ℝ)^j)*((2*B+1:ℕ):ℝ)^K) ≤ W')
    (hUW : U ≤ W') (hbound : ProfileEndpointBound N B K L f p Q i j s W' A)
    (V : Space 2 → Finset (Space 2))
    (hV : QuarterPencilData (1/(2:ℝ)^(blockDepth N B j-blockDepth N B i+2)) s U m P V) :
    A ≤ ((P.biUnion V).card:ℝ)/m := by
  obtain ⟨E,hES,hEN,hEC,u,hu,hT,hTne,hmassT,hTP⟩ :=
    blockClass_parent_refine_quarter_endpoint_subset hL hL' B f g K p q r₀
      hsub hW hmass Q hQ hji hi ha₀ p₀ hp₀ P hP hPsub hH hsize
  let T := classLeaves E (blockLabel E N B (fun _ => []) K)
    (blockLabel E N B (fun _ => []) K u)
  have hparent : p₀ ∈ T.image (List.take (blockDepth N B i)) := by
    obtain ⟨v,hv⟩ := hTne
    refine Finset.mem_image.mpr ⟨v,hv,?_⟩
    exact (Finset.mem_filter.mp (hES (hT hv))).2
  have hh := hbound E (fun _ => []) u (blockDepth N B i) p₀ hEN
    (hT.trans hEC) (hmassT.trans (mul_le_mul_of_nonneg_right hbudget (Nat.cast_nonneg _)))
    le_rfl p₀ hparent m hm V (hV.mono (by positivity) hm.le hUW hTP)
  exact hh.trans (div_le_div_of_nonneg_right
    (Nat.cast_le.mpr (Finset.card_le_card (Finset.biUnion_subset_biUnion_of_subset_left V hTP))) hm.le)

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Recursion_ProfileStepBudget
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! One explicit budget for the two branches of the endpoint scale product. -/
namespace Falconer

theorem profile_retention_cost_le {W H : ℝ} (hW : 0 ≤ W) (hH : 0 ≤ H)
    {i j K : ℕ} (hi : i ≤ K) (hj : j ≤ K) (B : ℕ) :
    (W*(2:ℝ)^(2*i))*((H*(2:ℝ)^j)*((2*B+1:ℕ):ℝ)^K) ≤
      W*H*((2:ℝ)^(3*K)*((2*B+1:ℕ):ℝ)^K) := by
  calc
    _ = W*H*((2:ℝ)^(2*i+j)*((2*B+1:ℕ):ℝ)^K) := by rw [pow_add]; ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right
      (pow_le_pow_right₀ (by norm_num) (by omega : 2*i+j ≤ 3*K)) (by positivity))
      (mul_nonneg hW hH)

theorem profile_step_budget_bounds {H G W : ℝ} (hH : 1 ≤ H) (hG : 1 ≤ G) (hW : 1 ≤ W) :
    W ≤ profileStepBudget H G W ∧ 4*H ≤ profileStepBudget H G W ∧
      280*W*H^3 ≤ profileStepBudget H G W ∧
      672*W^2*H^3 ≤ profileStepBudget H G W ∧
      32*W*H^3 ≤ profileStepBudget H G W ∧
      W*(20*H^2)*G ≤ profileStepBudget H G W ∧
      W*(16*W*H^3)*G ≤ profileStepBudget H G W := by
  have hH0 : 0 ≤ H := zero_le_one.trans hH
  have hG0 : 0 ≤ G := zero_le_one.trans hG
  have hW0 : 0 ≤ W := zero_le_one.trans hW
  have hW2 : W ≤ W^2 := by nlinarith only [hW]
  have hH2 : H^2 ≤ H^3 := by nlinarith only [sq_nonneg H,mul_le_mul_of_nonneg_left hH (sq_nonneg H)]
  have hH3 : 1 ≤ H^3 := one_le_pow₀ hH
  have hW21 : 1 ≤ W^2 := one_le_pow₀ hW
  have hHH3 : H ≤ H^3 := (show H ≤ H^2 by nlinarith only [hH]).trans hH2
  have hcore : W^2*H^3 ≤ profileStepBudget H G W := by
    dsimp [profileStepBudget]
    calc
      _ ≤ 1024*(W^2*H^3) := by nlinarith only [mul_nonneg (sq_nonneg W) (pow_nonneg hH0 3)]
      _ ≤ _ := by
        convert le_mul_of_one_le_right (show 0 ≤ 1024*(W^2*H^3) by positivity) hG using 1 <;> first | rfl | ring
  have bound {c : ℝ} (_hc : 0 ≤ c) (hc' : c ≤ 1024) :
      c*W^2*H^3*G ≤ profileStepBudget H G W := by
    dsimp [profileStepBudget]
    gcongr
  refine ⟨?_,?_,?_,?_,?_,?_,?_⟩
  · exact (hW2.trans (le_mul_of_one_le_right (sq_nonneg W) hH3)).trans hcore
  · calc
      4*H ≤ 4*W^2*H^3*G := by
        calc
          _ ≤ 4*W^2*H^3 := by
            calc
              _ ≤ 4*H^3 := mul_le_mul_of_nonneg_left hHH3 (by norm_num)
              _ ≤ _ := by nlinarith only [mul_le_mul_of_nonneg_right hW21 (pow_nonneg hH0 3)]
          _ ≤ _ := le_mul_of_one_le_right (by positivity) hG
      _ ≤ _ := bound (by norm_num) (by norm_num)
  · calc
      _ ≤ 280*W^2*H^3 := by gcongr
      _ ≤ 280*W^2*H^3*G := le_mul_of_one_le_right (by positivity) hG
      _ ≤ _ := bound (by norm_num) (by norm_num)
  · exact (le_mul_of_one_le_right (by positivity) hG).trans
      (bound (c := 672) (by norm_num) (by norm_num))
  · calc
      _ ≤ 32*W^2*H^3 := by gcongr
      _ ≤ 32*W^2*H^3*G := le_mul_of_one_le_right (by positivity) hG
      _ ≤ _ := bound (by norm_num) (by norm_num)
  · calc
      _ = 20*W*H^2*G := by ring
      _ ≤ 20*W^2*H^3*G := by gcongr
      _ ≤ _ := bound (by norm_num) (by norm_num)
  · calc
      _ = 16*W^2*H^3*G := by ring
      _ ≤ _ := bound (by norm_num) (by norm_num)

theorem profile_label_cost_one_le (B K : ℕ) :
    1 ≤ (2:ℝ)^(3*K)*((2*B+1:ℕ):ℝ)^K := by
  apply one_le_mul_of_one_le_of_one_le
  · exact one_le_pow₀ (by norm_num)
  · apply one_le_pow₀
    exact_mod_cast (show 1 ≤ 2*B+1 by omega)

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Measures_BudgetedEndpointProduct
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual geometric scale product with uniform depth and pencil budgets.
Both outputs retain their original dyadic endpoints and half-slope chart. -/
namespace Falconer
open Set Regularization
open scoped BigOperators
attribute [local instance] Classical.propDecidable

theorem quarter_endpoint_budgeted_scale_product {N a b c : ℕ}
    (hac : a ≤ c) (hcb : c ≤ b) (Q : DyadicCube 2) (hQ : Q.side = 1)
    (C : Finset (CellPath 2)) (hC : C ⊆ cubePaths 2 N) (hbN : b ≤ N)
    (p₀ : CellPath 2) (hp₀ : p₀ ∈ C.image (List.take a))
    {s W m : ℝ} (hs : 0 ≤ s) (hs1 : s ≤ 1) (hW : 1 ≤ W) (hm : 0 < m)
    (V : Space 2 → Finset (Space 2))
    (hV : QuarterPencilData (1/(2:ℝ)^(b-a+2)) s W m (quarterEndpointSet Q C a b p₀) V) :
    let H : ℝ := (4*(N+2)+11:ℕ)
    let U0 := profileStepBudget H 1 W
    let P := quarterEndpointSet Q C a b p₀
    let D := quarterEndpointSet Q C a c p₀
    ∃ R ⊆ D, R.Nonempty ∧ (D.card:ℝ) ≤ (20*H^2)*(R.card:ℝ) ∧
      ∃ m₀ : ℝ, 0 < m₀ ∧ ∃ U : Space 2 → Finset (Space 2),
        QuarterPencilData (1/(2:ℝ)^(c-a+2)) s U0 m₀ R U ∧
        ∀ r ∈ prefixChildren C a c p₀, quarterEndpointPoint Q a p₀ r ∈ R →
          ∃ P' ⊆ quarterEndpointSet Q C c b r, P'.Nonempty ∧
            ((quarterEndpointSet Q C c b r).card:ℝ) ≤ (16*W*H^3)*(P'.card:ℝ) ∧
            ∃ m₁ : ℝ, 0 < m₁ ∧ ∃ T : Space 2 → Finset (Space 2),
              QuarterPencilData (1/(2:ℝ)^(b-c+2)) s U0 m₁ P' T ∧
              (((R.biUnion U).card:ℝ)/m₀)*(((P'.biUnion T).card:ℝ)/m₁) ≤
                (43264*H^4)*(((P.biUnion V).card:ℝ)/m) := by
  let H : ℝ := (4*(N+2)+11:ℕ)
  let P := quarterEndpointSet Q C a b p₀
  let Jv := Nat.log 2 (∑ x ∈ P, (V x).card)+1
  let Jg := Nat.log 2 (P.biUnion V).card+1
  have hH : 1 ≤ H := by dsimp [H]; exact_mod_cast (show 1 ≤ 4*(N+2)+11 by omega)
  have hW0 : 0 ≤ W := zero_le_one.trans hW
  have hδ : 0 ≤ 1/(2:ℝ)^(b-a+2) := by positivity
  obtain ⟨_,hchart,hsep⟩ := quarterEndpointSet_geometry Q hQ C hC (hac.trans hcb) hbN p₀
  have hmesh : 1/(2:ℝ)^(N+2) ≤ 1/(2:ℝ)^(b-a+2) := by
    apply one_div_le_one_div_of_le (by positivity)
    exact pow_le_pow_right₀ (by norm_num) (by omega)
  have hlogs := separated_pencil_configuration_logs (N+2) P V
    (fun x hx => ⟨(hchart x hx).1.trans (by norm_num),(hchart x hx).2.trans (by norm_num)⟩)
    (fun x hx y hy hxy => hmesh.trans (hsep x hx y hy hxy))
    (fun x hx => ⟨(hV x hx).2.2.1,
      fun u hu v hv huv => hmesh.trans ((hV x hx).2.2.2.1 u hu v hv huv)⟩)
  have hJvH : (Jv:ℝ) ≤ H := by dsimp [Jv,H]; exact_mod_cast hlogs.1
  have hJgH : (Jg:ℝ) ≤ H := by dsimp [Jg,H]; exact_mod_cast hlogs.2
  have hJv : 0 < (Jv:ℝ) := by dsimp [Jv]; positivity
  have hJg : 0 < (Jg:ℝ) := by dsimp [Jg]; positivity
  have hball : ∀ r ∈ prefixChildren C a c p₀,
      NormalizedFiniteBallBound (1/(2:ℝ)^(b-c+2)) 0 1 (quarterEndpointSet Q C c b r) := by
    intro r hr z ρ hρ hρ1
    simp only [Real.rpow_zero,mul_one,one_mul]
    exact Nat.cast_le.mpr (Finset.card_filter_le _ _)
  obtain ⟨L,E,F,w,hL,hLb,hE,hF,hw,R,hRD,hR,hRcount,U,hU,hcells⟩ :=
    quarter_endpoint_scale_product hac hcb Q hQ C hC hbN p₀ hp₀ hs hW
      (by norm_num) hm (mul_pos (zero_lt_one.trans_le hW) hm) hball V
      (fun x hx => ⟨(hV x hx).1,(hV x hx).2.1,(hV x hx).2.2.2.2.1,(hV x hx).2.2.2.2.2⟩)
  have hE0 : 0 < E := by rw [hE]; positivity
  have hFE : F = 2*E*W := by rw [hF]; field_simp
  obtain ⟨hLH,_,_,hcoarse,hfine,hpoint,hratio,hprod⟩ :=
    uniform_scale_cost_bounds hJv.le hJg.le (zero_le_one.trans hH) hJvH hJgH hL.le hLb hE hFE
      hW0 (by norm_num : (0:ℝ) ≤ 1) hW0 hs1
  obtain ⟨_,hsizeC,hballC,hballF,hsizeF,_,_⟩ := profile_step_budget_bounds (G := 1) hH (by norm_num) hW
  have hpoint' : F*(Jg:ℝ) ≤ 16*W*H^3 := by simpa only [one_mul,mul_one] using hpoint
  have hfine' : 2*(((W*F)*3^s)*7^s)*(Jg:ℝ) ≤ 672*W^2*H^3 := by
    convert hfine using 1 <;> first | rfl | ring
  let m₀ := w/(2*(Jg:ℝ))
  have hm₀ : 0 < m₀ := by dsimp [m₀]; positivity
  have hratioC : 2*w ≤ profileStepBudget H 1 W*m₀ := by
    apply (div_le_iff₀ hm₀).mp
    rw [coarse_pencil_size_ratio hw hJg]
    exact (mul_le_mul_of_nonneg_left hJgH (by norm_num)).trans hsizeC
  refine ⟨R,hRD,hR,hRcount.trans (mul_le_mul_of_nonneg_right hLH (Nat.cast_nonneg _)),
    m₀,hm₀,U,?_,?_⟩
  · intro z hz
    obtain ⟨hlo,hhi,hch,hsp,hb,hinc⟩ := hU z hz
    exact ⟨hlo,hhi.trans hratioC,hch,hsp,
      normalizedFiniteBallBound_mono_constant (by positivity) (hcoarse.trans hballC) hb,hinc⟩
  · intro r hr hrR
    obtain ⟨j,P',hPsub,hP,hPcount,_,_,_,T,hT,hproduct⟩ := hcells r hr hrR
    let m₁ := (m/(2*E))/(2*(Jg:ℝ)*(2:ℝ)^j)
    have hm₁ : 0 < m₁ := by dsimp [m₁]; positivity
    have hratioF : (W*m)/(2:ℝ)^j ≤ profileStepBudget H 1 W*m₁ := by
      apply (div_le_iff₀ hm₁).mp
      rw [rescaled_pencil_size_ratio hm hE0 hJg]
      have he : (W*m)/m = W := by field_simp
      rw [he]
      exact hratio.trans hsizeF
    refine ⟨P',hPsub,hP,hPcount.trans
      (mul_le_mul_of_nonneg_right hpoint' (Nat.cast_nonneg _)),m₁,hm₁,T,?_,?_⟩
    · intro x hx
      obtain ⟨_,hch,hsp,hb,hinc,hlo,hhi⟩ := hT x hx
      exact ⟨hlo,hhi.trans hratioF,hch,hsp,
        normalizedFiniteBallBound_mono_constant (by positivity) (hfine'.trans hballF) hb,hinc⟩
    · exact hproduct.trans (mul_le_mul_of_nonneg_right hprod (by positivity))

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Recursion_ProfileScaleInduction
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The two-scale induction step uses the actual coarse and local packets,
then lifts both selected point sets back to the original reference profile. -/
namespace Falconer
open Set Regularization
attribute [local instance] Classical.propDecidable

theorem profileEndpointBound_split {N B K : ℕ} {L : Finset (CellPath 2)}
    (hL : L ⊆ cubePaths 2 N) (f : CellPath 2 → List ℕ) (p : CellPath 2)
    (Q : DyadicCube 2) (hQ : Q.side = 1)
    {i j k : ℕ} (hjk : j ≤ k) (hki : k ≤ i) (hi : i ≤ K)
    {s W A D : ℝ} (hs : 0 ≤ s) (hs1 : s ≤ 1) (hW : 1 ≤ W) (hA : 0 ≤ A) (hD : 0 ≤ D)
    (hleft : ProfileEndpointBound N B K L f p Q i k s
      (profileStepBudget (4*(N+2)+11:ℕ) ((2:ℝ)^(3*K)*((2*B+1:ℕ):ℝ)^K) W) A)
    (hright : ProfileEndpointBound N B K L f p Q k j s
      (profileStepBudget (4*(N+2)+11:ℕ) ((2:ℝ)^(3*K)*((2*B+1:ℕ):ℝ)^K) W) D) :
    ProfileEndpointBound N B K L f p Q i j s W (A*D/(43264*((4*(N+2)+11:ℕ):ℝ)^4)) := by
  let H : ℝ := (4*(N+2)+11:ℕ)
  let G := (2:ℝ)^(3*K)*((2*B+1:ℕ):ℝ)^K
  let W' := profileStepBudget H G W
  have hH : 1 ≤ H := by dsimp [H]; exact_mod_cast (show 1 ≤ 4*(N+2)+11 by omega)
  have hG : 1 ≤ G := profile_label_cost_one_le B K
  have hW0 : 0 ≤ W := zero_le_one.trans hW
  have hU : profileStepBudget H 1 W ≤ W' := by
    dsimp [W',profileStepBudget]
    gcongr
  obtain ⟨_,_,_,_,_,hcoarseCost,hfineCost⟩ := profile_step_budget_bounds hH hG hW
  intro L' g q a₀ r₀ hL' C S hsub hmass ha₀ p₀ hp₀ m hm V Z hV
  have hSN : S ⊆ cubePaths 2 N := (Finset.filter_subset _ _).trans hL'
  obtain ⟨R,hRD,hR,hRcount,m₀,hm₀,U,hUdata,hcells⟩ :=
    quarter_endpoint_budgeted_scale_product (blockDepth_antitone N B hki)
      (blockDepth_antitone N B hjk) Q hQ S hSN (Nat.sub_le _ _) p₀ hp₀ hs hs1 hW hm V hV
  have hcoarseBudget : (W*(2:ℝ)^(2*i))*
      (((20*H^2)*(2:ℝ)^k)*((2*B+1:ℕ):ℝ)^K) ≤ W' := by
    exact (profile_retention_cost_le hW0 (by positivity) hi (hki.trans hi) B).trans hcoarseCost
  have hleftValue : A ≤ ((R.biUnion U).card:ℝ)/m₀ :=
    profileEndpointBound_retained_subset hL hL' f g p q Q hQ hki hi r₀ hsub
      hW0 (by positivity) hm₀ hmass ha₀ p₀ hp₀ R hR hRD hRcount hcoarseBudget hU hleft U hUdata
  obtain ⟨z,hz⟩ := hR
  obtain ⟨r,hr,he⟩ := Finset.mem_image.mp (hRD hz)
  have hrR : quarterEndpointPoint Q (blockDepth N B i) p₀ r ∈ R := by rw [he]; exact hz
  obtain ⟨P',hPsub,hP,hPcount,m₁,hm₁,T,hT,hproduct⟩ := hcells r hr hrR
  have hfineBudget : (W*(2:ℝ)^(2*k))*
      (((16*W*H^3)*(2:ℝ)^j)*((2*B+1:ℕ):ℝ)^K) ≤ W' := by
    exact (profile_retention_cost_le hW0 (by positivity) (hki.trans hi)
      (hjk.trans (hki.trans hi)) B).trans hfineCost
  have hrightValue : D ≤ ((P'.biUnion T).card:ℝ)/m₁ :=
    profileEndpointBound_retained_subset hL hL' f g p q Q hQ hjk (hki.trans hi) r₀ hsub
      hW0 (by positivity) hm₁ hmass (ha₀.trans (blockDepth_antitone N B hki)) r
      (prefixChildren_mem_image hr) P' hP hPsub hPcount hfineBudget hU hright T hT
  apply (div_le_iff₀ (show 0 < 43264*H^4 by positivity)).2
  calc
    A*D ≤ (((R.biUnion U).card:ℝ)/m₀)*(((P'.biUnion T).card:ℝ)/m₁) :=
      mul_le_mul hleftValue hrightValue hD (hA.trans hleftValue)
    _ ≤ (43264*H^4)*(((Z.biUnion V).card:ℝ)/m) := hproduct
    _ = _ := mul_comm _ _

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Recursion_ProfileIntervalChain
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Finite composition of actual profile interval estimates. Every splitting
step uses the proved endpoint construction and its explicit next budget. -/
namespace Falconer
open Set Regularization
open scoped BigOperators

theorem profileBudgetSequence_one_le {H G W : ℝ}
    (hH : 1 ≤ H) (hG : 1 ≤ G) (hW : 1 ≤ W) (n : ℕ) :
    1 ≤ profileBudgetSequence H G W n := by
  induction n with
  | zero => exact hW
  | succ n ih => exact ih.trans (profile_step_budget_bounds hH hG ih).1

theorem profileBudgetSequence_monotone {H G W : ℝ}
    (hH : 1 ≤ H) (hG : 1 ≤ G) (hW : 1 ≤ W) :
    Monotone (profileBudgetSequence H G W) := by
  apply monotone_nat_of_le_succ
  intro n
  exact (profile_step_budget_bounds hH hG (profileBudgetSequence_one_le hH hG hW n)).1

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Recursion_OrderedEndpointIntervals
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Apply interval gains to an ordered subfamily; omitted gaps use the
nonempty-pencil estimate. No gain or profile hypothesis is imposed on a gap. -/
namespace Falconer
open Set Regularization
open scoped BigOperators

theorem OrderedBlockIntervals.end_le {i j : ℕ} {R : List (ℕ × ℕ)}
    (h : OrderedBlockIntervals i j R) : j ≤ i := by
  induction R generalizing i with
  | nil => exact h
  | cons c R ih => exact (ih h.2.2).trans (h.2.1.trans h.1)

theorem profileEndpointBound_ordered_intervals {N B K : ℕ} {L : Finset (CellPath 2)}
    (hL : L ⊆ cubePaths 2 N) (f : CellPath 2 → List ℕ) (p : CellPath 2)
    (Q : DyadicCube 2) (hQ : Q.side = 1) {s : ℝ} (hs : 0 ≤ s) (hs1 : s ≤ 1)
    (R : List (ℕ × ℕ)) (i j : ℕ) (hR : OrderedBlockIntervals i j R) (hi : i ≤ K)
    (F : ℕ × ℕ → ℝ) (hF : ∀ c ∈ R, 0 ≤ F c)
    (W : ℕ → ℝ) (hW : ∀ k, 1 ≤ W k) (hWmono : Monotone W)
    (hWstep : ∀ k, W (k+1) = profileStepBudget (4*(N+2)+11:ℕ)
      ((2:ℝ)^(3*K)*((2*B+1:ℕ):ℝ)^K) (W k))
    (hbase : ∀ c ∈ R, ProfileEndpointBound N B K L f p Q c.1 c.2 s (W (2*R.length)) (F c)) :
    ProfileEndpointBound N B K L f p Q i j s (W 0)
      ((R.map F).prod/(43264*((4*(N+2)+11:ℕ):ℝ)^4)^(2*R.length)) := by
  induction R generalizing i W with
  | nil => simpa using profileEndpointBound_trivial N B K L f p Q i j s (W 0)
  | cons c R ih =>
    obtain ⟨hci,hcc,hrest⟩ := hR
    have hcK : c.1 ≤ K := hci.trans hi
    have hdK : c.2 ≤ K := hcc.trans hcK
    have hhead := (hbase c (by simp)).mono_budget
      (hWmono (show 2 ≤ 2*(c::R).length by simp))
    have htail := ih c.2 hrest hdK (fun c hc => hF c (by simp [hc]))
      (fun k => W (k+2)) (fun k => hW (k+2))
      (fun a b hab => hWmono (Nat.add_le_add_right hab 2))
      (fun k => by simpa only [Nat.add_assoc] using hWstep (k+2)) (by
        intro d hd
        have hh := hbase d (by simp [hd])
        exact hh)
    have htail0 : 0 ≤ (R.map F).prod/(43264*((4*(N+2)+11:ℕ):ℝ)^4)^(2*R.length) := by
      apply div_nonneg
      · apply List.prod_nonneg
        intro x hx
        obtain ⟨d,hd,rfl⟩ := List.mem_map.mp hx
        exact hF d (by simp [hd])
      · positivity
    have hFc : 0 ≤ F c := hF c (by simp)
    rw [hWstep 1] at hhead htail
    have hmid := profileEndpointBound_split hL f p Q hQ hrest.end_le hcc hcK
      hs hs1 (hW 1) hFc htail0 hhead htail
    have hmid0 : 0 ≤ F c*((R.map F).prod/(43264*((4*(N+2)+11:ℕ):ℝ)^4)^(2*R.length))/
        (43264*((4*(N+2)+11:ℕ):ℝ)^4) := by positivity
    have hgap := profileEndpointBound_trivial N B K L f p Q i c.1 s (W 1)
    rw [hWstep 0] at hgap hmid
    have hh := profileEndpointBound_split hL f p Q hQ (hrest.end_le.trans hcc) hci hi
      hs hs1 (hW 0) (by norm_num : (0:ℝ) ≤ 1) hmid0 hgap hmid
    have he : 1*(F c*((R.map F).prod/(43264*((4*(N+2)+11:ℕ):ℝ)^4)^(2*R.length))/
        (43264*((4*(N+2)+11:ℕ):ℝ)^4))/(43264*((4*(N+2)+11:ℕ):ℝ)^4) =
        (((c::R).map F).prod)/(43264*((4*(N+2)+11:ℕ):ℝ)^4)^(2*(c::R).length) := by
      rw [List.map_cons,List.prod_cons,List.length_cons,
        show 2*(R.length+1) = 2*R.length+2 by omega,pow_add]
      ring
    simpa only [he] using hh

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Incidence_RoundedBlockIntervals
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Real profile intervals select an ordered family of actual block intervals.
The selected endpoints and their normalized lengths remain exact. -/
namespace Falconer
open Regularization

theorem OrderedBlockIntervals.of_pairwise {i j : ℕ} {R : List (ℕ × ℕ)}
    (hji : j ≤ i) (hp : R.Pairwise (fun c d => d.1 ≤ c.2))
    (hb : ∀ c ∈ R, j ≤ c.2 ∧ c.2 ≤ c.1 ∧ c.1 ≤ i) :
    OrderedBlockIntervals i j R := by
  induction R generalizing i with
  | nil => exact hji
  | cons c R ih =>
    have hh := hb c (by simp)
    obtain ⟨hhead,htail⟩ := List.pairwise_cons.mp hp
    refine ⟨hh.2.2,hh.2.1,ih hh.1 htail ?_⟩
    intro d hd
    have hd' := hb d (by simp [hd])
    exact ⟨hd'.1,hd'.2.1,hhead d hd⟩

theorem normalized_blockDepth_le_imp {m B i j : ℕ} (hm : 0 < m) (hB : 0 < B)
    (hi : i ≤ m) (hj : j ≤ m)
    (h : (blockDepth (m*B) B i:ℝ)/(m*B:ℕ) ≤ (blockDepth (m*B) B j:ℝ)/(m*B:ℕ)) :
    j ≤ i := by
  have hN : (0:ℝ) < (m*B:ℕ) := Nat.cast_pos.mpr (Nat.mul_pos hm hB)
  have hh := (div_le_div_iff_of_pos_right hN).mp h
  have hiB : i*B ≤ m*B := Nat.mul_le_mul_right B hi
  have hjB : j*B ≤ m*B := Nat.mul_le_mul_right B hj
  simp only [blockDepth,Nat.cast_sub hiB,Nat.cast_sub hjB,Nat.cast_mul] at hh
  have hB' : (0:ℝ) < B := Nat.cast_pos.mpr hB
  have hji : (j:ℝ) ≤ i := by nlinarith only [hh,hB']
  exact_mod_cast hji

theorem exists_rounded_block_interval_map {m B : ℕ} (hm : 0 < m) (hB : 0 < B)
    (S : List (ℝ × ℝ))
    (hbound : ∀ c ∈ S, 0 ≤ c.1 ∧ c.1+c.2 ≤ 1)
    (hpos : ∀ c ∈ S, 0 < (innerProfileCell m c).2)
    (hordered : (S.map (innerProfileCell m)).Pairwise (fun c d => c.1+c.2 ≤ d.1)) :
    ∃ I : (ℝ × ℝ) → (ℕ × ℕ),
      (∀ c ∈ S, (I c).2 < (I c).1 ∧ (I c).1 ≤ m ∧
        (innerProfileCell m c).1 = (blockDepth (m*B) B (I c).1:ℝ)/(m*B:ℕ) ∧
        (innerProfileCell m c).1+(innerProfileCell m c).2 =
          (blockDepth (m*B) B (I c).2:ℝ)/(m*B:ℕ)) ∧
      (S.map I).Pairwise (fun c d => d.1 ≤ c.2) ∧ OrderedBlockIntervals m 0 (S.map I) := by
  classical
  have hex (c : ℝ × ℝ) (hc : c ∈ S) : ∃ r : ℕ × ℕ,
      r.2 < r.1 ∧ r.1 ≤ m ∧
      (innerProfileCell m c).1 = (blockDepth (m*B) B r.1:ℝ)/(m*B:ℕ) ∧
      (innerProfileCell m c).1+(innerProfileCell m c).2 =
        (blockDepth (m*B) B r.2:ℝ)/(m*B:ℕ) := by
    obtain ⟨i,j,hji,hi,ha,hb⟩ := innerProfileCell_block_endpoints hm hB c
      (hbound c hc).1 (hbound c hc).2 (hpos c hc)
    exact ⟨(i,j),hji,hi,ha,hb⟩
  let I := fun c => if hc : c ∈ S then Classical.choose (hex c hc) else (0,0)
  have hI (c : ℝ × ℝ) (hc : c ∈ S) :
      (I c).2 < (I c).1 ∧ (I c).1 ≤ m ∧
      (innerProfileCell m c).1 = (blockDepth (m*B) B (I c).1:ℝ)/(m*B:ℕ) ∧
      (innerProfileCell m c).1+(innerProfileCell m c).2 =
        (blockDepth (m*B) B (I c).2:ℝ)/(m*B:ℕ) := by
    simpa only [I,dite_eq_left hc] using Classical.choose_spec (hex c hc)
  have hp : (S.map I).Pairwise (fun c d => d.1 ≤ c.2) := by
    apply List.pairwise_map.mpr
    apply (List.pairwise_map.mp hordered).imp_of_mem
    intro c d hc hd hcd
    have hc' := hI c hc
    have hd' := hI d hd
    rw [hc'.2.2.2,hd'.2.2.1] at hcd
    exact normalized_blockDepth_le_imp hm hB (hc'.1.le.trans hc'.2.1) hd'.2.1 hcd
  refine ⟨I,hI,hp,OrderedBlockIntervals.of_pairwise (Nat.zero_le _) hp ?_⟩
  intro r hr
  obtain ⟨c,hc,rfl⟩ := List.mem_map.mp hr
  exact ⟨Nat.zero_le _,(hI c hc).1.le,(hI c hc).2.1⟩

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Incidence_BlockIntervalLengths
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact length accounting and even scales for the selected block intervals. -/
namespace Falconer
open Regularization

theorem exists_half_block_length {m B i j : ℕ} (hB : Even B) :
    ∃ n : ℕ, blockDepth (m*B) B j-blockDepth (m*B) B i = 2*n := by
  have sub_even {a b : ℕ} (ha : Even a) (hb : Even b) : Even (a-b) := by
    rcases le_total b a with h | h
    · exact (Nat.even_sub h).2 ⟨fun _ => hb,fun _ => ha⟩
    · simp [Nat.sub_eq_zero_of_le h]
  have hN : Even (m*B) := hB.mul_left m
  have hi : Even (blockDepth (m*B) B i) := by
    dsimp [blockDepth]
    exact sub_even hN (hB.mul_left i)
  have hj : Even (blockDepth (m*B) B j) := by
    dsimp [blockDepth]
    exact sub_even hN (hB.mul_left j)
  obtain ⟨n,hn⟩ := sub_even hj hi
  exact ⟨n,by omega⟩

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Recursion_OrderedProfilePower
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Power accounting for the actual ordered-interval induction. -/
namespace Falconer
open Regularization

theorem list_prod_two_rpow {α : Type*} (S : List α) (e : α → ℝ) :
    (S.map fun c => (2:ℝ)^(e c)).prod = (2:ℝ)^((S.map e).sum) := by
  induction S with
  | nil => simp
  | cons c S ih =>
    simp only [List.map_cons,List.prod_cons,List.sum_cons,ih]
    exact (Real.rpow_add (by norm_num) _ _).symm

theorem profileEndpointBound_ordered_power {N B K : ℕ} {L : Finset (CellPath 2)}
    (hL : L ⊆ cubePaths 2 N) (f : CellPath 2 → List ℕ) (p : CellPath 2)
    (Q : DyadicCube 2) (hQ : Q.side = 1) {s : ℝ} (hs : 0 ≤ s) (hs1 : s ≤ 1)
    (R : List (ℕ × ℕ)) (i j : ℕ) (hR : OrderedBlockIntervals i j R) (hi : i ≤ K)
    (e : ℕ × ℕ → ℝ) (W : ℕ → ℝ) (hW : ∀ k, 1 ≤ W k) (hWmono : Monotone W)
    (hWstep : ∀ k, W (k+1) = profileStepBudget (4*(N+2)+11:ℕ)
      ((2:ℝ)^(3*K)*((2*B+1:ℕ):ℝ)^K) (W k))
    (hbase : ∀ c ∈ R, ProfileEndpointBound N B K L f p Q c.1 c.2 s (W (2*R.length)) ((2:ℝ)^(e c)))
    {target loss : ℝ} (hgain : target+loss ≤ (R.map e).sum)
    (hcost : (43264*((4*(N+2)+11:ℕ):ℝ)^4)^(2*R.length) ≤ (2:ℝ)^loss) :
    ProfileEndpointBound N B K L f p Q i j s (W 0) ((2:ℝ)^target) := by
  have hh := profileEndpointBound_ordered_intervals hL f p Q hQ hs hs1 R i j hR hi
    (fun c => (2:ℝ)^(e c)) (fun _ _ => by positivity) W hW hWmono hWstep hbase
  apply hh.mono_value
  apply (le_div_iff₀ (show 0 < (43264*((4*(N+2)+11:ℕ):ℝ)^4)^(2*R.length) by positivity)).2
  calc
    _ ≤ (2:ℝ)^target*(2:ℝ)^loss := mul_le_mul_of_nonneg_left hcost (by positivity)
    _ = (2:ℝ)^(target+loss) := (Real.rpow_add (by norm_num) _ _).symm
    _ ≤ (2:ℝ)^((R.map e).sum) := Real.rpow_le_rpow_of_exponent_le (by norm_num) hgain
    _ = _ := (list_prod_two_rpow R e).symm

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Recursion_ProfileHighMass
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A profile with large total growth spends positive total length in the
linear intervals whose slope exceeds a prescribed intermediate threshold. -/
namespace Falconer
open Set

private theorem profileHighLength_cons (f : ℝ → ℝ) (u : ℝ) (c : ℝ × ℝ)
    (S : List (ℝ × ℝ)) :
    profileHighLength f u (c::S) =
      (if u ≤ intervalSecantSlope f c.1 c.2 then c.2 else 0)+profileHighLength f u S := by
  by_cases hc : u ≤ intervalSecantSlope f c.1 c.2 <;> simp [profileHighLength,hc]

theorem profile_increment_le_high_length {f : ℝ → ℝ} (hf : LipschitzWith 2 f)
    (u : ℝ) (S : List (ℝ × ℝ)) (hpos : ∀ c ∈ S, 0 < c.2) :
    (S.map (fun c => f (c.1+c.2)-f c.1)).sum ≤
      u*(S.map Prod.snd).sum+(2-u)*profileHighLength f u S := by
  induction S with
  | nil => simp [profileHighLength]
  | cons c S ih =>
    have hp := hpos c (by simp)
    have ht := ih (fun d hd => hpos d (by simp [hd]))
    have he : f (c.1+c.2)-f c.1 = intervalSecantSlope f c.1 c.2*c.2 := by
      unfold intervalSecantSlope
      rw [div_mul_cancel₀ _ hp.ne']
    have hbound := (le_abs_self (intervalSecantSlope f c.1 c.2)).trans
      (intervalSecantSlope_abs_le hf c.1 hp)
    rw [List.map_cons,List.sum_cons,List.map_cons,List.sum_cons,profileHighLength_cons]
    by_cases hc : u ≤ intervalSecantSlope f c.1 c.2
    · rw [ite_eq_left hc]
      have hm := mul_le_mul_of_nonneg_right hbound hp.le
      rw [← he] at hm
      nlinarith
    · rw [ite_eq_right hc]
      have hm := mul_le_mul_of_nonneg_right (le_of_not_ge hc) hp.le
      rw [← he] at hm
      nlinarith

theorem structured_profile_high_length_lower {f : ℝ → ℝ} (hf : LipschitzWith 2 f)
    {r θ s u t m κ ε : ℝ} (hr : 0 < r) (hm : 0 < m) (hu : 0 ≤ u)
    {S : List (ℝ × ℝ)} (hS : StructuredProfilePieces f r θ s m S)
    (hf0 : f 0 = 0) (hfm : t*m-ε*m ≤ f m)
    (hcover : m*(1-κ) ≤ (S.map Prod.snd).sum) :
    (t-u-ε-2*κ)*m ≤ (2-u)*profileHighLength f u S := by
  have hb : ∀ c ∈ S, 0 ≤ c.1 ∧ c.1+c.2 ≤ m ∧ 0 ≤ c.2 := by
    intro c hc
    have h := hS.bounds c hc
    exact ⟨h.1,h.2.1,hr.le.trans h.2.2⟩
  have hlen := ordered_interval_length_le hm.le hS.ordered hb
  have hinc := ordered_profile_increment_lower hf hm.le hS.ordered hb
  have hup := profile_increment_le_high_length hf u S (by
    intro c hc
    exact hr.trans_le (hS.bounds c hc).2.2)
  rw [hf0,sub_zero] at hinc
  have hw := mul_le_mul_of_nonneg_left hlen hu
  nlinarith

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Recursion_RoundedHighProfile
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! High-slope length survives inward rounding, with the same explicit
endpoint loss as the total retained interval length. -/
namespace Falconer

theorem profileHighLength_eq_sum (f : ℝ → ℝ) (u : ℝ) (S : List (ℝ × ℝ)) :
    profileHighLength f u S =
      (S.map fun c => if u ≤ intervalSecantSlope f c.1 c.2 then c.2 else 0).sum := by
  induction S with
  | nil => simp [profileHighLength]
  | cons c S ih =>
    by_cases hc : u ≤ intervalSecantSlope f c.1 c.2 <;>
      simp [profileHighLength,hc,← ih]

theorem rounded_profile_high_length_lower {f : ℝ → ℝ} (hf : LipschitzWith 2 f)
    {n : ℕ} (hn : 0 < n) {τ : ℝ} (hτ : 0 < τ) (hmesh : 2/(n:ℝ) ≤ τ/2)
    (S : List (ℝ × ℝ)) (hmin : ∀ c ∈ S, τ ≤ c.2) (u : ℝ) :
    profileHighLength f u S-(2/(n:ℝ))*(S.length:ℝ) ≤
      profileHighLength f (u-16/((n:ℝ)*τ)) (S.map (innerProfileCell n)) := by
  have hpoint (c : ℝ × ℝ) (hc : c ∈ S) :
      (if u ≤ intervalSecantSlope f c.1 c.2 then c.2 else 0)-2/(n:ℝ) ≤
        if u-16/((n:ℝ)*τ) ≤ intervalSecantSlope f (innerProfileCell n c).1 (innerProfileCell n c).2
          then (innerProfileCell n c).2 else 0 := by
    have hslope := (abs_le.mp (rounded_profile_uniform_slope hf hn hτ hmesh c (hmin c hc))).1
    have hlength := (innerProfileCell_length_bounds hn c).1
    have hpos : 0 < (innerProfileCell n c).2 := by
      have hh := hmin c hc
      linarith
    by_cases hu : u ≤ intervalSecantSlope f c.1 c.2
    · have hu' : u-16/((n:ℝ)*τ) ≤
          intervalSecantSlope f (innerProfileCell n c).1 (innerProfileCell n c).2 := by linarith
      simpa only [ite_eq_left hu,ite_eq_left hu'] using hlength
    · rw [ite_eq_right hu]
      split_ifs <;> have hnonneg : (0:ℝ) ≤ 2/(n:ℝ) := by positivity
      all_goals linarith
  rw [profileHighLength_eq_sum,profileHighLength_eq_sum,List.map_map]
  induction S with
  | nil => simp
  | cons c S ih =>
    have hh := hpoint c (by simp)
    have ht := ih (fun d hd => hmin d (by simp [hd])) (fun d hd => hpoint d (by simp [hd]))
    simp only [List.map_cons,List.sum_cons,List.length_cons,Nat.cast_add,Nat.cast_one,Function.comp_apply]
    linarith

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Recursion_ProfileGainAccounting
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Add normal and good interval gains while charging the actual chord-error
length and one fixed weak loss per interval. -/
namespace Falconer
attribute [local instance] Classical.propDecidable

theorem profile_gain_exponent_sum (S : List (ℝ × ℝ)) (f : ℝ → ℝ) (u s η a loss N : ℝ) :
    (S.map (profileGainExponent f u s η a loss N)).sum =
      N*((s-a)*(S.map Prod.snd).sum+η*profileHighLength f u S-loss*(S.length:ℝ)) := by
  rw [profileHighLength_eq_sum]
  induction S with
  | nil => simp
  | cons c S ih =>
    simp only [List.map_cons,List.sum_cons,List.length_cons,Nat.cast_add,Nat.cast_one]
    rw [ih]
    dsimp [profileGainExponent]
    ring

theorem profile_gain_exponent_lower (S : List (ℝ × ℝ)) (f : ℝ → ℝ)
    {u s η a loss N κ h J target : ℝ} (hN : 0 ≤ N) (hs : 0 ≤ s)
    (hη : 0 ≤ η) (ha : 0 ≤ a) (hloss : 0 ≤ loss)
    (hcover : 1-κ ≤ (S.map Prod.snd).sum) (hlength : (S.map Prod.snd).sum ≤ 1)
    (hhigh : h ≤ profileHighLength f u S) (hcount : (S.length:ℝ) ≤ J)
    (hgap : target ≤ s*(1-κ)+η*h-a-loss*J) :
    target*N ≤ (S.map (profileGainExponent f u s η a loss N)).sum := by
  rw [profile_gain_exponent_sum]
  have hbase := mul_le_mul_of_nonneg_left hcover hs
  have herror := mul_le_mul_of_nonneg_left hlength ha
  have hbonus := mul_le_mul_of_nonneg_left hhigh hη
  have htotal := mul_le_mul_of_nonneg_left hcount hloss
  have hsum : target ≤ (s-a)*(S.map Prod.snd).sum+
      η*profileHighLength f u S-loss*(S.length:ℝ) := by
    nlinarith only [hgap,hbase,herror,hbonus,htotal]
  simpa only [mul_comm N] using mul_le_mul_of_nonneg_right hsum hN

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Incidence_BlockProfileCells
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Transfer the rounded real profile cells and their gains to the exact
block-index pairs used by the recursive incidence estimates. -/
namespace Falconer
open Set Regularization

theorem blockProfileCell_eq_of_endpoints {N B : ℕ} {r : ℕ × ℕ} {c : ℝ × ℝ}
    (ha : c.1 = (blockDepth N B r.1:ℝ)/N)
    (hb : c.1+c.2 = (blockDepth N B r.2:ℝ)/N) : c = blockProfileCell N B r := by
  apply Prod.ext ha
  change c.2 = ((blockDepth N B r.2:ℝ)-(blockDepth N B r.1:ℝ))/N
  calc
    c.2 = (blockDepth N B r.2:ℝ)/N-(blockDepth N B r.1:ℝ)/N := by linarith only [ha,hb]
    _ = _ := by ring

theorem rounded_block_gain_sum {m B : ℕ} (S : List (ℝ × ℝ))
    (I : (ℝ × ℝ) → (ℕ × ℕ))
    (hI : ∀ c ∈ S,
      (innerProfileCell m c).1 = (blockDepth (m*B) B (I c).1:ℝ)/(m*B:ℕ) ∧
      (innerProfileCell m c).1+(innerProfileCell m c).2 =
        (blockDepth (m*B) B (I c).2:ℝ)/(m*B:ℕ))
    (g : ℝ → ℝ) (u s η a loss N : ℝ) :
    ((S.map I).map fun r => profileGainExponent g u s η a loss N (blockProfileCell (m*B) B r)).sum =
      ((S.map (innerProfileCell m)).map (profileGainExponent g u s η a loss N)).sum := by
  rw [List.map_map,List.map_map]
  congr 1
  apply List.map_congr_left
  intro c hc
  dsimp only [Function.comp_apply]
  rw [blockProfileCell_eq_of_endpoints (hI c hc).1 (hI c hc).2]

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Recursion_RoundedProfileGain
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The rounded decomposition supplies the actual normal/good cell hypotheses
and retains a definite length of good cells. -/
namespace Falconer
open Set
attribute [local instance] Classical.propDecidable

theorem profileHighLength_nonneg {f : ℝ → ℝ} (u : ℝ) {S : List (ℝ × ℝ)}
    (hS : ∀ c ∈ S, 0 ≤ c.2) : 0 ≤ profileHighLength f u S := by
  rw [profileHighLength_eq_sum]
  apply List.sum_nonneg
  intro a ha
  obtain ⟨c,hc,rfl⟩ := List.mem_map.mp ha
  split_ifs
  · exact hS c hc
  · rfl

theorem profileHighLength_antitone {f : ℝ → ℝ} {u v : ℝ} (huv : u ≤ v)
    {S : List (ℝ × ℝ)} (hS : ∀ c ∈ S, 0 ≤ c.2) :
    profileHighLength f v S ≤ profileHighLength f u S := by
  rw [profileHighLength_eq_sum,profileHighLength_eq_sum]
  induction S with
  | nil => simp
  | cons c S ih =>
    have ht := ih (fun d hd => hS d (by simp [hd]))
    have hc := hS c (by simp)
    simp only [List.map_cons,List.sum_cons]
    have hh : (if v ≤ intervalSecantSlope f c.1 c.2 then c.2 else 0) ≤
        if u ≤ intervalSecantSlope f c.1 c.2 then c.2 else 0 := by
      by_cases hv : v ≤ intervalSecantSlope f c.1 c.2
      · simp only [ite_eq_left hv,ite_eq_left (huv.trans hv),le_refl]
      · rw [ite_eq_right hv]
        split_ifs <;> linarith
    linarith

theorem rounded_profile_gain_cells {f : ℝ → ℝ} (hf : LipschitzWith 2 f)
    {m : ℕ} (hm : 0 < m) {τ ε s κ : ℝ} (hτ : 0 < τ) (hε : 0 ≤ ε) (hκ : 0 < κ)
    (hmesh : 2/(m:ℝ) ≤ τ/2) (herror : 4/(m:ℝ) ≤ ε*(τ/2))
    (hslack : 16/((m:ℝ)*τ) ≤ κ/2)
    {S : List (ℝ × ℝ)} (hS : StructuredProfilePieces f τ ε (s+κ) 1 S) :
    ∀ c ∈ S.map (innerProfileCell m),
      0 ≤ c.1 ∧ c.1+c.2 ≤ 1 ∧ τ/2 ≤ c.2 ∧
      s ≤ intervalSecantSlope f c.1 c.2 ∧ intervalSecantSlope f c.1 c.2 ≤ 2 ∧
      (∀ x ∈ Icc c.1 (c.1+c.2), -(3*ε)*c.2 ≤ intervalSecantError f c.1 c.2 x) ∧
      (s+2*κ ≤ intervalSecantSlope f c.1 c.2 →
        ∀ x ∈ Icc c.1 (c.1+c.2), |intervalSecantError f c.1 c.2 x| ≤ (3*ε)*c.2) := by
  intro c hc
  obtain ⟨ha,hb,hlen,hslope,halt⟩ :=
    (rounded_structured_profile_pieces hf hm hτ hε hmesh herror hS).2 c hc
  have hpos : 0 < c.2 := (half_pos hτ).trans_le hlen
  refine ⟨ha,hb,hlen,by linarith,?_,?_,?_⟩
  · exact (le_abs_self _).trans (intervalSecantSlope_abs_le hf c.1 hpos)
  · rcases halt with hlin | hsup
    · intro x hx
      simpa only [neg_mul] using (abs_le.mp (hlin x hx)).1
    · exact hsup.2
  · intro hh
    rcases halt with hlin | hsup
    · exact hlin
    · exfalso
      linarith [hsup.1]

theorem rounded_profile_good_length {f : ℝ → ℝ} (hf : LipschitzWith 2 f)
    {m : ℕ} (hm : 0 < m) {τ ε s κ t χ weak : ℝ}
    (hτ : 0 < τ) (hκ : 0 < κ) (hs : 0 ≤ s)
    (hmesh : 2/(m:ℝ) ≤ τ/2) (hslack : 16/((m:ℝ)*τ) ≤ κ)
    {S : List (ℝ × ℝ)} (hS : StructuredProfilePieces f τ ε (s+κ) 1 S)
    (hf0 : f 0 = 0) (hgrowth : t-weak ≤ f 1)
    (hcover : 1-χ ≤ (S.map Prod.snd).sum)
    (hgap : s+8*κ ≤ t) (hweak : weak+2*χ ≤ κ)
    (hround : (2/(m:ℝ))*(S.length:ℝ) ≤ κ) :
    κ ≤ profileHighLength f (s+2*κ) (S.map (innerProfileCell m)) := by
  have hraw := structured_profile_high_length_lower (κ := χ) (ε := weak) (t := t) hf hτ (by norm_num : (0:ℝ) < 1)
    (show 0 ≤ s+3*κ by positivity) hS hf0 (by simpa only [mul_one] using hgrowth)
    (by simpa only [mul_one,one_mul] using hcover)
  have hnonneg := profileHighLength_nonneg (f := f) (s+3*κ)
    (fun c hc => hτ.le.trans (hS.bounds c hc).2.2)
  have hhigh : 2*κ ≤ profileHighLength f (s+3*κ) S := by
    have hh : 0 ≤ (s+3*κ)*profileHighLength f (s+3*κ) S := mul_nonneg (by positivity) hnonneg
    simp only [mul_one] at hraw
    nlinarith only [hraw,hgap,hweak,hh]
  have hrounded := rounded_profile_high_length_lower hf hm hτ hmesh S
    (fun c hc => (hS.bounds c hc).2.2) (s+3*κ)
  have hmono := profileHighLength_antitone (f := f)
    (show s+2*κ ≤ s+3*κ-16/((m:ℝ)*τ) by linarith)
    (fun c hc => (half_pos hτ).le.trans (innerProfileCells_min_length hm hmesh
      (fun d hd => (hS.bounds d hd).2.2) c hc))
  linarith

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Estimates_RoundedEndpointGain
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Apply the actual normal/good cell estimates to an inward-rounded profile
partition and close the finite endpoint induction. -/
namespace Falconer
open Set Regularization

theorem rounded_profile_endpoint_gain_oai {κ : ℝ} (hκ : 0 < κ) (hκ1 : κ ≤ 1/100) :
    ∃ eg η : ℝ, ∃ Ng : ℕ, 0 < eg ∧ eg ≤ 1 ∧ 0 < η ∧ 0 < Ng ∧
    ∀ m B : ℕ, 0 < m → 0 < B → Even B →
    ∀ L : Finset (CellPath 2), L ⊆ cubePaths 2 (m*B) →
    ∀ (f : CellPath 2 → List ℕ) (p : CellPath 2) (Q : DyadicCube 2), Q.side = 1 →
    ∀ s t α τ β lam χ r ζ : ℝ, κ ≤ s → s ≤ 1-8*κ → 0 ≤ α → 0 < τ → 0 < β → 0 < lam →
    ∀ J : ℕ, ∀ S : List (ℝ × ℝ),
      (let N := m*B;
       let g := fun x => regularizedProfile L (blockLabel L N B f (m+1)) N B (m+1) p ((N:ℝ)*x);
       StructuredProfilePieces g τ α (s+κ) 1 S) →
      (let N := m*B;
       let g := fun x => regularizedProfile L (blockLabel L N B f (m+1)) N B (m+1) p ((N:ℝ)*x);
       t-lam ≤ g 1) →
      1-χ ≤ (S.map Prod.snd).sum → s+8*κ ≤ t → lam+2*χ ≤ κ →
      2/(m:ℝ) ≤ τ/2 → 4/(m:ℝ) ≤ α*(τ/2) → 16/((m:ℝ)*τ) ≤ κ/2 →
      (2/(m:ℝ))*(S.length:ℝ) ≤ r → r ≤ κ → S.length ≤ J →
      4*(Ng:ℝ) ≤ τ*(m*B:ℕ) → 4*β ≤ eg*τ/8 → 3*α ≤ eg/4 →
      s+ζ+β ≤ s*(1-χ-r)+η*κ-9*α-13*β*(J:ℝ) →
      (let N := m*B;
       let H : ℝ := (4*(N+2)+11:ℕ);
       let G := (2:ℝ)^(3*(m+1))*((2*B+1:ℕ):ℝ)^(m+1);
       let W := profileBudgetSequence H G ((2:ℝ)^(lam*(N:ℝ)));
       (∀ j ≤ 2*J, ∀ A : ℝ,
         profileGeometryConstant (m+1) B (W j) A ≤ (2:ℝ)^((4*β)*(N:ℝ)+A)) ∧
       640*((N:ℝ)+3) ≤ (2:ℝ)^(β*(N:ℝ)) ∧
       (43264*H^4)^(2*J) ≤ (2:ℝ)^(β*(N:ℝ))) →
      ProfileEndpointBound (m*B) B (m+1) L f p Q m 0 s ((2:ℝ)^(lam*(m*B:ℕ)))
        ((2:ℝ)^((s+ζ)*(m*B:ℕ))) := by
  obtain ⟨eg,η,Ng,heg,heg1,hη,hNg,hcell⟩ := block_cell_power hκ hκ1
  refine ⟨eg,η,Ng,heg,heg1,hη,hNg,?_⟩
  intro m B hm hB hBeven L hL f p Q hQ s t α τ β lam χ r ζ hs hs1 hα hτ hβ hlam J S
    hS hgrowth hcover hgap hweak hmesh herror hslack hround hr hcount hlarge hbeta halpha hgain hbudget
  let N := m*B
  let K := m+1
  let g := fun x => regularizedProfile L (blockLabel L N B f K) N B K p ((N:ℝ)*x)
  let H : ℝ := (4*(N+2)+11:ℕ)
  let G := (2:ℝ)^(3*K)*((2*B+1:ℕ):ℝ)^K
  let W := profileBudgetSequence H G ((2:ℝ)^(lam*(N:ℝ)))
  have hN : 0 < N := Nat.mul_pos hm hB
  have hNR : (0:ℝ) < N := Nat.cast_pos.mpr hN
  have hf : LipschitzWith 2 g := planarProfile_lipschitz hN hL _ B K p
  have hg0 : g 0 = 0 := by simp [g,regularizedProfile_zero]
  obtain ⟨hgeom,hpoly,hcost⟩ := hbudget
  have hrounded := rounded_profile_gain_cells hf hm hτ hα hκ hmesh herror hslack hS
  have hhigh : κ ≤ profileHighLength g (s+2*κ) (S.map (innerProfileCell m)) :=
    rounded_profile_good_length hf hm hτ hκ (hκ.le.trans hs) hmesh
      (by linarith only [hslack,hκ]) hS hg0 hgrowth hcover hgap hweak (hround.trans hr)
  have hord := (rounded_structured_profile_pieces hf hm hτ hα hmesh herror hS).1
  obtain ⟨I,hI,_,hordered⟩ := exists_rounded_block_interval_map hm hB S
    (fun c hc => ⟨(hS.bounds c hc).1,(hS.bounds c hc).2.1⟩)
    (fun c hc => (half_pos hτ).trans_le (hrounded _ (List.mem_map.mpr ⟨c,hc,rfl⟩)).2.2.1) hord
  let R := S.map I
  let e := fun c : ℕ × ℕ => profileGainExponent g (s+2*κ) s η (9*α) (13*β) N
    (blockProfileCell N B c)
  have hRlen : R.length = S.length := by simp [R]
  have hH : 1 ≤ H := by dsimp [H]; exact_mod_cast (show 1 ≤ 4*(N+2)+11 by omega)
  have hG : 1 ≤ G := profile_label_cost_one_le B K
  have hW0 : 1 ≤ (2:ℝ)^(lam*(N:ℝ)) := Real.one_le_rpow (by norm_num) (by positivity)
  have hW (k : ℕ) : 1 ≤ W k := profileBudgetSequence_one_le hH hG hW0 k
  have hWmono : Monotone W := profileBudgetSequence_monotone hH hG hW0
  have hbase (c : ℕ × ℕ) (hc : c ∈ R) :
      ProfileEndpointBound N B K L f p Q c.1 c.2 s (W (2*R.length)) ((2:ℝ)^(e c)) := by
    obtain ⟨a,ha,rfl⟩ := List.mem_map.mp hc
    have hi := hI a ha
    have heq : innerProfileCell m a = blockProfileCell N B (I a) :=
      blockProfileCell_eq_of_endpoints hi.2.2.1 hi.2.2.2
    have hh := hrounded (innerProfileCell m a) (List.mem_map.mpr ⟨a,ha,rfl⟩)
    rw [heq] at hh
    obtain ⟨n,hn⟩ := exists_half_block_length (m := m) (i := (I a).1) (j := (I a).2) hBeven
    have hcast : ((blockDepth N B (I a).2-blockDepth N B (I a).1:ℕ):ℝ) =
        (blockDepth N B (I a).2:ℝ)-(blockDepth N B (I a).1:ℝ) :=
      Nat.cast_sub (blockDepth_antitone N B hi.1.le)
    have hd : τ*(N:ℝ)/2 ≤ (2*n:ℕ) := by
      have hl := hh.2.2.1
      change τ/2 ≤ ((blockDepth N B (I a).2:ℝ)-(blockDepth N B (I a).1:ℝ))/N at hl
      have hl' := (le_div_iff₀ hNR).mp hl
      rw [← hcast,hn] at hl'
      linarith only [hl']
    have hnlarge : Ng ≤ n+3 := by
      have hnn : (Ng:ℝ) ≤ n := by
        push_cast at hd
        nlinarith only [hd,hlarge]
      have : Ng ≤ n := Nat.cast_le.mp hnn
      omega
    have hscale : (4*β)*(N:ℝ)+(3*α)*
        ((blockDepth N B (I a).2:ℝ)-(blockDepth N B (I a).1:ℝ)) ≤ eg*((n+3:ℕ):ℝ) := by
      rw [← hcast,hn]
      have hn0 : (0:ℝ) ≤ n := Nat.cast_nonneg n
      have h1 := mul_le_mul_of_nonneg_right hbeta hNR.le
      have h2 := mul_le_mul_of_nonneg_left hd heg.le
      have h3 := mul_le_mul_of_nonneg_right halpha (show (0:ℝ) ≤ (2*n:ℕ) by positivity)
      push_cast at h1 h2 h3 ⊢
      nlinarith only [h1,h2,h3,heg]
    have hgeometry := hgeom (2*R.length) (by rw [hRlen]; omega)
      ((3*α)*((blockDepth N B (I a).2:ℝ)-(blockDepth N B (I a).1:ℝ)))
    have hdata : s ≤ intervalSecantSlope g (blockProfileCell N B (I a)).1 (blockProfileCell N B (I a)).2 ∧
        intervalSecantSlope g (blockProfileCell N B (I a)).1 (blockProfileCell N B (I a)).2 ≤ 2 ∧
        (∀ x ∈ Icc (blockProfileCell N B (I a)).1
          ((blockProfileCell N B (I a)).1+(blockProfileCell N B (I a)).2),
          -(3*α)*(blockProfileCell N B (I a)).2 ≤ intervalSecantError g
            (blockProfileCell N B (I a)).1 (blockProfileCell N B (I a)).2 x) ∧
        (s+2*κ ≤ intervalSecantSlope g (blockProfileCell N B (I a)).1 (blockProfileCell N B (I a)).2 →
          ∀ x ∈ Icc (blockProfileCell N B (I a)).1
            ((blockProfileCell N B (I a)).1+(blockProfileCell N B (I a)).2),
            |intervalSecantError g (blockProfileCell N B (I a)).1 (blockProfileCell N B (I a)).2 x| ≤
              (3*α)*(blockProfileCell N B (I a)).2) := hh.2.2.2
    have hb := hcell n hnlarge s (W (2*R.length)) (3*α) (4*β) β hs hs1
      (hW _) (by positivity) (by positivity) N B K hN L hL f p Q hQ (I a).1 (I a).2
      hi.1.le (by dsimp [K]; omega) hn hdata hgeometry hscale hpoly
    convert hb using 1
    all_goals try with_reducible_and_instances rfl
    dsimp [e,g]
    ring_nf
  have hcover' : 1-χ-r ≤ ((S.map (innerProfileCell m)).map Prod.snd).sum := by
    have hh := innerProfileCells_length_lower hm S
    linarith only [hh,hcover,hround]
  have hlength : ((S.map (innerProfileCell m)).map Prod.snd).sum ≤ 1 := by
    simpa only [sub_zero] using ordered_interval_length_le (by norm_num : (0:ℝ) ≤ 1) hord
      (fun c hc => ⟨(hrounded c hc).1,(hrounded c hc).2.1,
        (half_pos hτ).le.trans (hrounded c hc).2.2.1⟩)
  have hsum : ((s+ζ)+β)*(N:ℝ) ≤ (R.map e).sum := by
    have hh := profile_gain_exponent_lower (S.map (innerProfileCell m)) g
      hNR.le (hκ.le.trans hs) hη.le (by positivity : 0 ≤ 9*α) (by positivity : 0 ≤ 13*β)
      (κ := χ+r) (h := κ) (J := J) (target := (s+ζ)+β)
      (by convert hcover' using 1; ring) hlength hhigh
      (by simpa only [List.length_map] using (Nat.cast_le.mpr hcount : (S.length:ℝ) ≤ J))
      (by convert hgain using 1; ring)
    have he := rounded_block_gain_sum S I (fun a ha => ⟨(hI a ha).2.2.1,(hI a ha).2.2.2⟩)
      g (s+2*κ) s η (9*α) (13*β) N
    change ((s+ζ)+β)*(N:ℝ) ≤ ((S.map I).map fun c =>
      profileGainExponent g (s+2*κ) s η (9*α) (13*β) N (blockProfileCell N B c)).sum
    rw [he]
    exact hh
  have hcost' : (43264*H^4)^(2*R.length) ≤ (2:ℝ)^(β*(N:ℝ)) := by
    apply le_trans _ hcost
    apply pow_le_pow_right₀
    · have hh : (1:ℝ) ≤ H^4 := one_le_pow₀ hH
      linarith
    · rw [hRlen]
      omega
  exact profileEndpointBound_ordered_power hL f p Q hQ (hκ.le.trans hs) (by linarith) R m 0 hordered
    (by dsimp [K]; omega) e W hW hWmono (fun _ => rfl) hbase
    (target := (s+ζ)*(N:ℝ)) (loss := β*(N:ℝ)) (by nlinarith only [hsum]) hcost'

end Falconer

end OAI
end

theorem solution : type_of% @OAI.Falconer.rounded_profile_endpoint_gain_oai := @OAI.Falconer.rounded_profile_endpoint_gain_oai
