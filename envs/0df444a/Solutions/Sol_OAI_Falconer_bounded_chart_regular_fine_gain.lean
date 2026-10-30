-- Prove2me | solution 1 for OAI.Falconer.bounded_chart_regular_fine_gain
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-29T22:03:52.819996+00:00
-- url     : https://prove2.me/submissions/61242c3d-ee57-49cf-8c6e-0da5ec09bfd2

import Mathlib
import Definitions.Def_OAIQ088F002
import Theorems.Thm_OAI_Falconer_frozen_coarse_packet_impossible

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

theorem sum_tubeDegree_sq (P : Finset (Space 2)) (T : Space 2 → Finset (Space 2)) :
    (∑ l ∈ P.biUnion T, (tubeDegree P T l)^2) =
      ∑ x ∈ P, ∑ y ∈ P, ((T x ∩ T y).card : ℝ) := by
  let U := P.biUnion T
  calc
    _ = ∑ l ∈ U, ∑ x ∈ P, ∑ y ∈ P,
        (if l ∈ T x then (1 : ℝ) else 0)*(if l ∈ T y then 1 else 0) := by
      simp only [tubeDegree, pow_two, Finset.sum_mul_sum, U]
    _ = ∑ x ∈ P, ∑ y ∈ P, ∑ l ∈ U,
        (if l ∈ T x then (1 : ℝ) else 0)*(if l ∈ T y then 1 else 0) := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro x _
      rw [Finset.sum_comm]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro x hx
      apply Finset.sum_congr rfl
      intro y _
      have he (l : Space 2) :
          (if l ∈ T x then (1 : ℝ) else 0)*(if l ∈ T y then 1 else 0) =
          if l ∈ T x ∩ T y then 1 else 0 := by
        by_cases hx : l ∈ T x <;> by_cases hy : l ∈ T y <;> simp [hx,hy]
      simp_rw [he]
      exact sum_tube_membership U _ (fun l hl =>
        Finset.mem_biUnion.mpr ⟨x,hx,(Finset.mem_inter.mp hl).1⟩)

theorem tube_union_second_moment (P : Finset (Space 2)) (T : Space 2 → Finset (Space 2)) :
    (∑ x ∈ P, ((T x).card : ℝ))^2 ≤
      ((P.biUnion T).card : ℝ) * (∑ x ∈ P, ∑ y ∈ P, ((T x ∩ T y).card : ℝ)) := by
  have hh := Finset.sum_mul_sq_le_sq_mul_sq (P.biUnion T)
    (fun _ => (1 : ℝ)) (tubeDegree P T)
  simpa only [one_mul, one_pow, Finset.sum_const, nsmul_eq_mul, mul_one,
    sum_tubeDegree, sum_tubeDegree_sq] using hh

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

theorem tube_pair_residual_le {δ : ℝ} (hδ : 0 ≤ δ) {x l m : Space 2}
    (hl : |l 0| ≤ 1) (hm : |m 0| ≤ 1)
    (hil : TubeIncident δ x l) (him : TubeIncident δ x m) :
    |(l 0-m 0)*x 0+(l 1-m 1)| ≤ 4*δ := by
  calc
    _ = |(x 1-m 0*x 0-m 1)-(x 1-l 0*x 0-l 1)| := by congr 1; ring
    _ ≤ |x 1-m 0*x 0-m 1|+|x 1-l 0*x 0-l 1| := abs_sub _ _
    _ ≤ _ := by linarith [tube_residual_le hδ hm him, tube_residual_le hδ hl hil]

theorem tube_point_coordinate_lower {δ r : ℝ} (hδ : 0 ≤ δ) (_hr : 0 < r)
    (hsmall : 16*δ ≤ r) {x y l : Space 2} (hl : |l 0| ≤ 1)
    (hx : TubeIncident δ x l) (hy : TubeIncident δ y l) (hxy : r ≤ dist x y) :
    r/4 ≤ |x 0-y 0| := by
  have he : |x 1-y 1| ≤ |x 0-y 0|+4*δ := by
    calc
      _ = |l 0*(x 0-y 0)+(x 1-l 0*x 0-l 1)-(y 1-l 0*y 0-l 1)| := by congr 1; ring
      _ ≤ |l 0*(x 0-y 0)+(x 1-l 0*x 0-l 1)|+|y 1-l 0*y 0-l 1| := abs_sub _ _
      _ ≤ |l 0| * |x 0-y 0|+|x 1-l 0*x 0-l 1|+|y 1-l 0*y 0-l 1| := by
        rw [← abs_mul]
        linarith [abs_add_le (l 0*(x 0-y 0)) (x 1-l 0*x 0-l 1)]
      _ ≤ _ := by
        have hh := mul_le_mul_of_nonneg_right hl (abs_nonneg (x 0-y 0))
        linarith [tube_residual_le hδ hl hx, tube_residual_le hδ hl hy]
  linarith [planar_dist_le_coordinate_sum x y]

theorem two_point_tube_parameters_close {δ r : ℝ} (hδ : 0 ≤ δ)
    (hr : 0 < r) (hr1 : r ≤ 1) (hsmall : 16*δ ≤ r)
    {x y l m : Space 2} (hx0 : |x 0| ≤ 1)
    (hl : |l 0| ≤ 1) (hm : |m 0| ≤ 1)
    (hxl : TubeIncident δ x l) (hyl : TubeIncident δ y l)
    (hxm : TubeIncident δ x m) (hym : TubeIncident δ y m)
    (hxy : r ≤ dist x y) : dist l m ≤ 80*δ/r := by
  have hcoord := tube_point_coordinate_lower hδ hr hsmall hl hxl hyl hxy
  have hs : |l 0-m 0| * |x 0-y 0| ≤ 8*δ := by
    calc
      _ = |((l 0-m 0)*x 0+(l 1-m 1))-((l 0-m 0)*y 0+(l 1-m 1))| := by
        rw [← abs_mul]; congr 1; ring
      _ ≤ |(l 0-m 0)*x 0+(l 1-m 1)|+|(l 0-m 0)*y 0+(l 1-m 1)| := abs_sub _ _
      _ ≤ _ := by linarith [tube_pair_residual_le hδ hl hm hxl hxm,
        tube_pair_residual_le hδ hl hm hyl hym]
  have hslope : |l 0-m 0| ≤ 32*δ/r := by
    apply (le_div_iff₀ hr).2
    have hh := mul_le_mul_of_nonneg_left hcoord (abs_nonneg (l 0-m 0))
    nlinarith
  have hinter : |l 1-m 1| ≤ |l 0-m 0|+4*δ := by
    calc
      _ = |((l 0-m 0)*x 0+(l 1-m 1))-(l 0-m 0)*x 0| := by congr 1; ring
      _ ≤ |(l 0-m 0)*x 0+(l 1-m 1)|+|(l 0-m 0)*x 0| := abs_sub _ _
      _ ≤ _ := by
        rw [abs_mul]
        have hh := mul_le_mul_of_nonneg_left hx0 (abs_nonneg (l 0-m 0))
        linarith [tube_pair_residual_le hδ hl hm hxl hxm]
  apply (le_div_iff₀ hr).2
  have hdist : dist l m ≤ 2*|l 0-m 0|+4*δ :=
    (planar_dist_le_coordinate_sum l m).trans (by linarith [hinter])
  have hsum := mul_le_mul_of_nonneg_right hdist hr.le
  have hsl := (le_div_iff₀ hr).mp hslope
  have hd := mul_le_mul_of_nonneg_left hr1 hδ
  nlinarith

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

theorem finite_ball_bound_card_lower {δ s K : ℝ} {P : Finset (Space 2)}
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hP : P.Nonempty)
    (hball : NormalizedFiniteBallBound δ s K P) :
    1 ≤ K*δ^s*(P.card : ℝ) := by
  obtain ⟨x,hx⟩ := hP
  have hx' : x ∈ P.filter (fun y => dist y x ≤ δ) := by simp [hx,hδ.le]
  have hc : 1 ≤ (P.filter (fun y => dist y x ≤ δ)).card :=
    Finset.one_le_card.mpr ⟨x,hx'⟩
  have hcR : (1 : ℝ) ≤ (P.filter (fun y => dist y x ≤ δ)).card := by exact_mod_cast hc
  exact hcR.trans (hball x δ le_rfl hδ1)

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
-- module Solutions.OAIQ088_FD.Falconer_Estimates_InversePowerSum
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Finite dyadic inverse-power sums at the critical ambient exponent -/

namespace Falconer

theorem inverse_power_dyadic {r s : ℝ} (hr : 0 < r) (hs : 0 ≤ s) (g k : ℕ)
    (hmin : 1/(2:ℝ)^(g+k) ≤ r) :
    (1/r)^s ≤ ((2:ℝ)^g)^s + ∑ j ∈ Finset.range k,
      if r < 1/(2:ℝ)^(g+j) then ((2:ℝ)^(g+j+1))^s else 0 := by
  induction k with
  | zero =>
    simp only [Finset.range_zero,Finset.sum_empty,add_zero] at *
    apply Real.rpow_le_rpow (by positivity) _ hs
    apply (div_le_iff₀ hr).mpr
    have hh := (div_le_iff₀ (by positivity : 0 < (2:ℝ)^g)).mp hmin
    nlinarith
  | succ k ih =>
    rw [Finset.sum_range_succ]
    by_cases hc : 1/(2:ℝ)^(g+k) ≤ r
    · have hh := ih hc
      have hn : 0 ≤ (if r < 1/(2:ℝ)^(g+k) then ((2:ℝ)^(g+k+1))^s else 0) := by
        split_ifs <;> positivity
      linarith
    · rw [ite_eq_left (lt_of_not_ge hc)]
      have hinv : 1/r ≤ (2:ℝ)^(g+k+1) := by
        apply (div_le_iff₀ hr).mpr
        have hh := (div_le_iff₀ (by positivity : 0 < (2:ℝ)^(g+(k+1)))).mp hmin
        simpa only [Nat.add_assoc,mul_comm] using hh
      have hp := Real.rpow_le_rpow (by positivity : 0 ≤ 1/r) hinv hs
      have hsum : 0 ≤ ∑ j ∈ Finset.range k,
          if r < 1/(2:ℝ)^(g+j) then ((2:ℝ)^(g+j+1))^s else 0 := by
        apply Finset.sum_nonneg
        intro j _
        split_ifs <;> positivity
      have hz : 0 ≤ ((2:ℝ)^g)^s := by positivity
      linarith

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Recursion_RegularizedPotential
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Finite-scale inverse-distance potentials for the slicing kernels -/

namespace Falconer
open Set Metric MeasureTheory
open scoped ENNReal
variable {X : Type*} [PseudoMetricSpace X] [MeasurableSpace X] [OpensMeasurableSpace X]

theorem regularized_potential_dyadic (μ : Measure X)
    (x : X) {s : ℝ} (hs : 0 ≤ s) (g k : ℕ) :
    (∫⁻ y in ball x (1/(2:ℝ)^g),
      ENNReal.ofReal ((1/(dist x y+1/(2:ℝ)^(g+k)))^s) ∂μ) ≤
    ENNReal.ofReal (((2:ℝ)^g)^s)*μ (ball x (1/(2:ℝ)^g))+
      ∑ j ∈ Finset.range k, ENNReal.ofReal (((2:ℝ)^(g+j+1))^s)*
        μ (ball x (1/(2:ℝ)^(g+j))) := by
  let B := ball x (1/(2:ℝ)^g)
  let f : X → ℝ≥0∞ := fun y =>
    ENNReal.ofReal ((1/(dist x y+1/(2:ℝ)^(g+k)))^s)
  let F : X → ℝ≥0∞ := fun y =>
    B.indicator (fun _ => ENNReal.ofReal (((2:ℝ)^g)^s)) y+
      ∑ j ∈ Finset.range k,
        (ball x (1/(2:ℝ)^(g+j))).indicator
          (fun _ => ENNReal.ofReal (((2:ℝ)^(g+j+1))^s)) y
  have hpoint : B.indicator f ≤ F := by
    intro y
    change B.indicator f y ≤ B.indicator (fun _ => ENNReal.ofReal (((2:ℝ)^g)^s)) y+
      ∑ j ∈ Finset.range k, (ball x (1/(2:ℝ)^(g+j))).indicator
        (fun _ => ENNReal.ofReal (((2:ℝ)^(g+j+1))^s)) y
    by_cases hy : y ∈ B
    · rw [indicator_of_mem hy,show B.indicator (fun _ => ENNReal.ofReal (((2:ℝ)^g)^s)) y =
        ENNReal.ofReal (((2:ℝ)^g)^s) from indicator_of_mem hy _]
      have hi := inverse_power_dyadic (s := s)
        (by positivity : 0 < dist x y+1/(2:ℝ)^(g+k)) hs g k
        (by linarith [dist_nonneg (x := x) (y := y)])
      have hh := ENNReal.ofReal_le_ofReal hi
      rw [ENNReal.ofReal_add (by positivity) (Finset.sum_nonneg (fun j _ => by split_ifs <;> positivity)),
        ENNReal.ofReal_sum_of_nonneg (fun j _ => by split_ifs <;> positivity)] at hh
      apply hh.trans
      apply add_le_add le_rfl
      apply Finset.sum_le_sum
      intro j hj
      by_cases hdist : dist x y+1/(2:ℝ)^(g+k) < 1/(2:ℝ)^(g+j)
      · rw [ite_eq_left hdist]
        have hyj : y ∈ ball x (1/(2:ℝ)^(g+j)) := by
          rw [mem_ball,dist_comm]
          linarith [show (0:ℝ) < 1/(2:ℝ)^(g+k) by positivity]
        rw [indicator_of_mem hyj]
      · rw [ite_eq_right hdist,ENNReal.ofReal_zero]
        exact bot_le
    · rw [indicator_of_notMem hy]
      exact bot_le
  rw [← lintegral_indicator measurableSet_ball]
  apply (lintegral_mono hpoint).trans_eq
  change (∫⁻ y, B.indicator (fun _ => ENNReal.ofReal (((2:ℝ)^g)^s)) y+
      ∑ j ∈ Finset.range k, (ball x (1/(2:ℝ)^(g+j))).indicator
        (fun _ => ENNReal.ofReal (((2:ℝ)^(g+j+1))^s)) y ∂μ) = _
  rw [lintegral_add_left (measurable_const.indicator measurableSet_ball),
    lintegral_indicator_const measurableSet_ball,
    lintegral_finsetSum _ (fun j _ => measurable_const.indicator measurableSet_ball)]
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  exact lintegral_indicator_const measurableSet_ball _

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Recursion_PotentialScale
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Geometric summation above the inverse-kernel exponent -/

namespace Falconer

theorem dyadic_potential_weight (n : ℕ) (s q : ℝ) :
    (((2:ℝ)^(n+1))^s)*(1/(2:ℝ)^n)^q =
      (2:ℝ)^s*(((2:ℝ)^n)^(s-q)) := by
  rw [pow_succ,Real.mul_rpow (by positivity) (by norm_num : (0:ℝ) ≤ 2),
    one_div,Real.inv_rpow (by positivity),Real.rpow_sub (by positivity)]
  ring

theorem dyadic_potential_start (n : ℕ) (s q : ℝ) :
    (((2:ℝ)^n)^s)*(1/(2:ℝ)^n)^q = (((2:ℝ)^n)^(s-q)) := by
  rw [one_div,Real.inv_rpow (by positivity),Real.rpow_sub (by positivity)]
  ring

theorem dyadic_potential_series (g k : ℕ) {s q : ℝ} (hsq : s < q) :
    (∑ j ∈ Finset.range k, (((2:ℝ)^(g+j))^(s-q))) ≤
      (((2:ℝ)^g)^(s-q))/(1-(2:ℝ)^(s-q)) := by
  let a := (2:ℝ)^(s-q)
  have ha : 0 ≤ a := by positivity
  have ha1 : a < 1 := Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (sub_neg.mpr hsq)
  have hsum : ∑ j ∈ Finset.range k, a^j ≤ (1-a)⁻¹ := by
    rw [← tsum_geometric_of_lt_one ha ha1]
    exact (summable_geometric_of_lt_one ha ha1).sum_le_tsum _ (fun _ _ => pow_nonneg ha _)
  have he (j : ℕ) : (((2:ℝ)^(g+j))^(s-q)) = (((2:ℝ)^g)^(s-q))*a^j := by
    rw [pow_add,Real.mul_rpow (by positivity) (by positivity)]
    congr 1
    dsimp [a]
    rw [← Real.rpow_natCast_mul (by norm_num),← Real.rpow_mul_natCast (by norm_num)]
    congr 1
    ring
  simp_rw [he]
  rw [← Finset.mul_sum]
  exact (mul_le_mul_of_nonneg_left hsum (by positivity)).trans_eq (by rw [div_eq_mul_inv])

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Recursion_PotentialFrostman
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Finite-scale ball bounds control the regularized slicing potential -/

namespace Falconer
open Set Metric MeasureTheory
open scoped ENNReal
variable {X : Type*} [PseudoMetricSpace X] [MeasurableSpace X] [OpensMeasurableSpace X]

theorem regularized_potential_frostman (μ : Measure X) (x : X)
    {K s q : ℝ} (hK : 0 ≤ K) (hs : 0 ≤ s) (hsq : s < q) (g k : ℕ)
    (hball : ∀ n : ℕ, n ≤ g+k →
      μ (ball x (1/(2:ℝ)^n)) ≤ ENNReal.ofReal (K*(1/(2:ℝ)^n)^q)) :
    (∫⁻ y in ball x (1/(2:ℝ)^g),
      ENNReal.ofReal ((1/(dist x y+1/(2:ℝ)^(g+k)))^s) ∂μ) ≤
      ENNReal.ofReal (K*(((2:ℝ)^g)^(s-q))*(1+(2:ℝ)^s/(1-(2:ℝ)^(s-q)))) := by
  apply (regularized_potential_dyadic μ x hs g k).trans
  have hstart : ENNReal.ofReal (((2:ℝ)^g)^s)*μ (ball x (1/(2:ℝ)^g)) ≤
      ENNReal.ofReal (K*(((2:ℝ)^g)^(s-q))) := by
    calc
      _ ≤ ENNReal.ofReal (((2:ℝ)^g)^s)*ENNReal.ofReal (K*(1/(2:ℝ)^g)^q) :=
        mul_le_mul_right (hball g (by omega)) _
      _ = _ := by
        rw [← ENNReal.ofReal_mul (by positivity)]
        congr 1
        calc
          _ = K*((((2:ℝ)^g)^s)*(1/(2:ℝ)^g)^q) := by ring
          _ = _ := by rw [dyadic_potential_start]
  have hterm (j : ℕ) (hj : j ∈ Finset.range k) :
      ENNReal.ofReal (((2:ℝ)^(g+j+1))^s)*μ (ball x (1/(2:ℝ)^(g+j))) ≤
      ENNReal.ofReal (K*(2:ℝ)^s*(((2:ℝ)^(g+j))^(s-q))) := by
    calc
      _ ≤ ENNReal.ofReal (((2:ℝ)^(g+j+1))^s)*ENNReal.ofReal (K*(1/(2:ℝ)^(g+j))^q) :=
        mul_le_mul_right (hball (g+j) (by have := Finset.mem_range.mp hj; omega)) _
      _ = _ := by
        rw [← ENNReal.ofReal_mul (by positivity)]
        congr 1
        calc
          _ = K*((((2:ℝ)^(g+j+1))^s)*(1/(2:ℝ)^(g+j))^q) := by ring
          _ = _ := by rw [dyadic_potential_weight]; ring
  calc
    _ ≤ ENNReal.ofReal (K*(((2:ℝ)^g)^(s-q)))+
        ∑ j ∈ Finset.range k, ENNReal.ofReal (K*(2:ℝ)^s*(((2:ℝ)^(g+j))^(s-q))) :=
      add_le_add hstart (Finset.sum_le_sum hterm)
    _ = ENNReal.ofReal (K*(((2:ℝ)^g)^(s-q))+
        K*(2:ℝ)^s*(∑ j ∈ Finset.range k, (((2:ℝ)^(g+j))^(s-q)))) := by
      rw [← ENNReal.ofReal_sum_of_nonneg (fun _ _ => by positivity),
        ← ENNReal.ofReal_add (by positivity) (by positivity),Finset.mul_sum]
    _ ≤ _ := by
      apply ENNReal.ofReal_le_ofReal
      have hh := mul_le_mul_of_nonneg_left (dyadic_potential_series g k hsq)
        (show 0 ≤ K*(2:ℝ)^s by positivity)
      calc
        _ ≤ K*(((2:ℝ)^g)^(s-q))+K*(2:ℝ)^s*
            ((((2:ℝ)^g)^(s-q))/(1-(2:ℝ)^(s-q))) := add_le_add le_rfl hh
        _ = _ := by ring

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Recursion_ScalarPotential
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Dyadic inverse potentials of a nonnegative measurable geometric statistic -/

namespace Falconer
open Set Metric MeasureTheory
open scoped ENNReal
variable {X : Type*} [MeasurableSpace X]

theorem regularized_scalar_potential (μ : Measure X) (a : X → ℝ)
    (ha : Measurable a) (ha0 : ∀ x, 0 ≤ a x)
    {K s q : ℝ} (hK : 0 ≤ K) (hs : 0 ≤ s) (hsq : s < q) (g k : ℕ)
    (hsmall : ∀ j : ℕ, j ≤ g+k →
      μ {x | a x < 1/(2:ℝ)^j} ≤ ENNReal.ofReal (K*(1/(2:ℝ)^j)^q)) :
    (∫⁻ x in {x | a x < 1/(2:ℝ)^g},
      ENNReal.ofReal ((1/(a x+1/(2:ℝ)^(g+k)))^s) ∂μ) ≤
      ENNReal.ofReal (K*(((2:ℝ)^g)^(s-q))*(1+(2:ℝ)^s/(1-(2:ℝ)^(s-q)))) := by
  have hpre (j : ℕ) : a ⁻¹' ball (0:ℝ) (1/(2:ℝ)^j) = {x | a x < 1/(2:ℝ)^j} := by
    ext x
    simp only [mem_preimage,mem_ball,Real.dist_eq,sub_zero,abs_of_nonneg (ha0 x),mem_ofPred_eq]
  have hball (j : ℕ) (hj : j ≤ g+k) :
      (Measure.map a μ) (ball (0:ℝ) (1/(2:ℝ)^j)) ≤
        ENNReal.ofReal (K*(1/(2:ℝ)^j)^q) := by
    rw [Measure.map_apply ha measurableSet_ball,hpre]
    exact hsmall j hj
  have hh := regularized_potential_frostman (Measure.map a μ) (0:ℝ) hK hs hsq g k hball
  have hf : Measurable (fun z : ℝ =>
      ENNReal.ofReal ((1/(dist 0 z+1/(2:ℝ)^(g+k)))^s)) := by fun_prop
  have he : (∫⁻ z in ball (0:ℝ) (1/(2:ℝ)^g),
      ENNReal.ofReal ((1/(dist 0 z+1/(2:ℝ)^(g+k)))^s) ∂Measure.map a μ) =
      ∫⁻ x in {x | a x < 1/(2:ℝ)^g},
        ENNReal.ofReal ((1/(a x+1/(2:ℝ)^(g+k)))^s) ∂μ := by
    rw [← lintegral_indicator measurableSet_ball,lintegral_map
      (hf.indicator measurableSet_ball) ha,
      ← lintegral_indicator (measurableSet_lt ha measurable_const)]
    apply lintegral_congr
    intro x
    by_cases hx : a x < 1/(2:ℝ)^g
    · have hz : a x ∈ ball (0:ℝ) (1/(2:ℝ)^g) := by
        change x ∈ a ⁻¹' ball (0:ℝ) (1/(2:ℝ)^g)
        rw [hpre]
        exact hx
      rw [indicator_of_mem hz,indicator_of_mem (show x ∈ {x | a x < 1/(2:ℝ)^g} from hx)]
      simp only [Real.dist_eq,zero_sub,abs_neg,abs_of_nonneg (ha0 x)]
    · have hz : a x ∉ ball (0:ℝ) (1/(2:ℝ)^g) := by
        change x ∉ a ⁻¹' ball (0:ℝ) (1/(2:ℝ)^g)
        rw [hpre]
        exact hx
      rw [indicator_of_notMem hz,indicator_of_notMem (show x ∉ {x | a x < 1/(2:ℝ)^g} from hx)]
  rw [he] at hh
  exact hh

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Recursion_TruncatedScalarPotential
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The maximum-truncated kernel and its dyadic sublevel bound -/

namespace Falconer
open Set MeasureTheory
open scoped ENNReal
variable {X : Type*} [MeasurableSpace X]

theorem inverse_max_le_two_inverse_add {x r : ℝ} (hx : 0 ≤ x) (hr : 0 < r) :
    1/max x r ≤ 2/(x+r) := by
  apply (div_le_div_iff₀ (hr.trans_le (le_max_right x r)) (by positivity)).mpr
  have h₁ := le_max_left x r
  have h₂ := le_max_right x r
  linarith

theorem truncated_scalar_potential (μ : Measure X) (a : X → ℝ)
    (ha : Measurable a) (ha0 : ∀ x, 0 ≤ a x)
    {K s q : ℝ} (hK : 0 ≤ K) (hs : 0 ≤ s) (hsq : s < q) (g k : ℕ)
    (hsmall : ∀ j : ℕ, j ≤ g+k →
      μ {x | a x < 1/(2:ℝ)^j} ≤ ENNReal.ofReal (K*(1/(2:ℝ)^j)^q)) :
    (∫⁻ x in {x | a x < 1/(2:ℝ)^g},
      ENNReal.ofReal ((1/max (a x) (1/(2:ℝ)^(g+k)))^s) ∂μ) ≤
      ENNReal.ofReal ((2:ℝ)^s*(K*(((2:ℝ)^g)^(s-q))*(1+(2:ℝ)^s/(1-(2:ℝ)^(s-q))))) := by
  have hp (x : X) : (1/max (a x) (1/(2:ℝ)^(g+k)))^s ≤
      (2:ℝ)^s*(1/(a x+1/(2:ℝ)^(g+k)))^s := by
    have hax := ha0 x
    calc
      _ ≤ (2/(a x+1/(2:ℝ)^(g+k)))^s := Real.rpow_le_rpow (by positivity)
        (inverse_max_le_two_inverse_add (ha0 x) (by positivity)) hs
      _ = _ := by
        rw [show 2/(a x+1/(2:ℝ)^(g+k)) = 2*(1/(a x+1/(2:ℝ)^(g+k))) by ring,
          Real.mul_rpow (by norm_num) (by positivity)]
  calc
    _ ≤ ∫⁻ x in {x | a x < 1/(2:ℝ)^g},
        ENNReal.ofReal ((2:ℝ)^s)*ENNReal.ofReal ((1/(a x+1/(2:ℝ)^(g+k)))^s) ∂μ := by
      apply lintegral_mono
      intro x
      dsimp only
      rw [← ENNReal.ofReal_mul (by positivity)]
      exact ENNReal.ofReal_le_ofReal (hp x)
    _ = ENNReal.ofReal ((2:ℝ)^s)*(∫⁻ x in {x | a x < 1/(2:ℝ)^g},
        ENNReal.ofReal ((1/(a x+1/(2:ℝ)^(g+k)))^s) ∂μ) :=
      lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ ≤ ENNReal.ofReal ((2:ℝ)^s)*ENNReal.ofReal
        (K*(((2:ℝ)^g)^(s-q))*(1+(2:ℝ)^s/(1-(2:ℝ)^(s-q)))) :=
      mul_le_mul' le_rfl (regularized_scalar_potential μ a ha ha0 hK hs hsq g k hsmall)
    _ = _ := by rw [← ENNReal.ofReal_mul (by positivity)]

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Recursion_FiniteCountingPotential
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The finite point potential needed by the elementary planar incidence bound. -/
namespace Falconer
open Set MeasureTheory
open scoped ENNReal BigOperators
attribute [local instance] Classical.propDecidable

theorem planarCountingMeasure_apply (P : Finset (Space 2)) (A : Set (Space 2)) :
    planarCountingMeasure P A = (P.filter (fun x => x ∈ A)).card := by
  rw [planarCountingMeasure,Measure.finsetSum_apply]
  simp_rw [Measure.dirac_apply,Set.indicator_apply,Pi.one_apply]
  rw [← Finset.sum_filter]
  simp

theorem planarCountingMeasure_lintegral (P : Finset (Space 2)) (f : Space 2 → ℝ≥0∞) :
    (∫⁻ x, f x ∂planarCountingMeasure P) = ∑ x ∈ P, f x := by
  rw [planarCountingMeasure,lintegral_finsetSum_measure]
  simp only [lintegral_dirac]

theorem finite_dyadic_truncated_potential (P : Finset (Space 2)) (x : Space 2)
    (N : ℕ) {K b f : ℝ} (hK : 0 ≤ K) (hb : 0 ≤ b) (hbf : b < f)
    (hball : NormalizedFiniteBallBound (1/(2:ℝ)^N) f K P) :
    (∑ y ∈ P, ENNReal.ofReal ((1/max (dist x y) (1/(2:ℝ)^N))^b)) ≤
      P.card + ENNReal.ofReal ((2:ℝ)^b*(K*(P.card : ℝ))*(1+(2:ℝ)^b/(1-(2:ℝ)^(b-f)))) := by
  let μ := planarCountingMeasure P
  have hsmall (j : ℕ) (hj : j ≤ 0+N) :
      μ {y | dist x y < 1/(2:ℝ)^j} ≤
        ENNReal.ofReal ((K*(P.card : ℝ))*(1/(2:ℝ)^j)^f) := by
    rw [planarCountingMeasure_apply]
    have hr0 : 1/(2:ℝ)^N ≤ 1/(2:ℝ)^j := by
      apply one_div_le_one_div_of_le (by positivity)
      exact pow_le_pow_right₀ (by norm_num) (by simpa using hj)
    have hr1 : 1/(2:ℝ)^j ≤ 1 := by
      apply (div_le_one (by positivity)).2
      exact one_le_pow₀ (by norm_num)
    have hs : P.filter (fun y => dist x y < 1/(2:ℝ)^j) ⊆
        P.filter (fun y => dist y x ≤ 1/(2:ℝ)^j) := by
      intro y hy
      obtain ⟨hyP,hy⟩ := Finset.mem_filter.mp hy
      exact Finset.mem_filter.mpr ⟨hyP,by simpa only [dist_comm] using hy.le⟩
    have hc := (show ((P.filter (fun y => dist x y < 1/(2:ℝ)^j)).card : ℝ) ≤
      (P.filter (fun y => dist y x ≤ 1/(2:ℝ)^j)).card from by exact_mod_cast Finset.card_le_card hs)
    have hh := hc.trans (hball x _ hr0 hr1)
    rw [show (K*(P.card : ℝ))*(1/(2:ℝ)^j)^f = K*(1/(2:ℝ)^j)^f*(P.card : ℝ) by ring]
    exact_mod_cast ENNReal.ofReal_le_ofReal hh
  have hlocal := truncated_scalar_potential μ (fun y => dist x y) (by fun_prop)
    (fun _ => dist_nonneg) (mul_nonneg hK (Nat.cast_nonneg _)) hb hbf 0 N hsmall
  simp only [pow_zero,one_div_one,zero_add,Real.one_rpow,mul_one] at hlocal
  let A := {y : Space 2 | dist x y < 1}
  let F := fun y : Space 2 => ENNReal.ofReal ((1/max (dist x y) (1/(2:ℝ)^N))^b)
  have hfar : (∫⁻ y in Aᶜ, F y ∂μ) ≤ P.card := by
    calc
      _ ≤ ∫⁻ _ in Aᶜ, (1 : ℝ≥0∞) ∂μ := by
        apply setLIntegral_mono' (by measurability)
        intro y hy
        change ¬ dist x y < 1 at hy
        have hd : 1 ≤ max (dist x y) (1/(2:ℝ)^N) :=
          (le_of_not_gt hy).trans (le_max_left _ _)
        have hinv : 1/max (dist x y) (1/(2:ℝ)^N) ≤ 1 :=
          (div_le_one (zero_lt_one.trans_le hd)).2 hd
        exact ENNReal.ofReal_le_one.mpr ((Real.rpow_le_rpow (by positivity) hinv hb).trans_eq (Real.one_rpow _))
      _ ≤ μ univ := by
        simp only [lintegral_one,Measure.restrict_apply_univ]
        exact measure_mono (subset_univ _)
      _ = P.card := by rw [planarCountingMeasure_apply]; simp
  rw [← planarCountingMeasure_lintegral]
  change (∫⁻ y, F y ∂μ) ≤ _
  rw [← lintegral_add_compl F (show MeasurableSet A from by dsimp [A]; measurability)]
  simpa only [mul_assoc,add_comm] using add_le_add hlocal hfar

theorem planarPotentialConstant_pos {b f : ℝ} (hbf : b < f) :
    0 < planarPotentialConstant b f := by
  have hd : 0 < 1-(2:ℝ)^(b-f) := sub_pos.mpr
    (Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (sub_neg.mpr hbf))
  unfold planarPotentialConstant
  positivity

theorem finite_dyadic_truncated_potential_real (P : Finset (Space 2)) (x : Space 2)
    (N : ℕ) {K b f : ℝ} (hK : 1 ≤ K) (hb : 0 ≤ b) (hbf : b < f)
    (hball : NormalizedFiniteBallBound (1/(2:ℝ)^N) f K P) :
    (∑ y ∈ P, (1/max (dist x y) (1/(2:ℝ)^N))^b) ≤
      K*planarPotentialConstant b f*(P.card : ℝ) := by
  have hK0 : 0 ≤ K := zero_le_one.trans hK
  have hd : 0 < 1-(2:ℝ)^(b-f) := sub_pos.mpr
    (Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (sub_neg.mpr hbf))
  have hR : 0 ≤ (P.card : ℝ)+(2:ℝ)^b*(K*(P.card : ℝ))*(1+(2:ℝ)^b/(1-(2:ℝ)^(b-f))) := by
    positivity
  have hh := finite_dyadic_truncated_potential P x N hK0 hb hbf hball
  rw [← ENNReal.ofReal_sum_of_nonneg (fun y _ => by positivity),
    ← ENNReal.ofReal_natCast P.card, ← ENNReal.ofReal_add (Nat.cast_nonneg _) (by positivity)] at hh
  have hh' := (ENNReal.ofReal_le_ofReal_iff hR).mp hh
  apply hh'.trans
  unfold planarPotentialConstant
  have hC : 0 ≤ (2:ℝ)^b*(1+(2:ℝ)^b/(1-(2:ℝ)^(b-f))) := by positivity
  nlinarith [Nat.cast_nonneg (α := ℝ) P.card]

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
-- module Solutions.OAIQ088_FD.Falconer_Estimates_CoarsePlanarRounding
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A common coarse grid inside the original chart and the resulting
point-line incidence error. -/
namespace Falconer
attribute [local instance] Classical.propDecidable

theorem coarsePlanarRound_near {Δ : ℝ} (hΔ : 0 < Δ) (p : Space 2) :
    dist p (coarsePlanarRound Δ p) ≤ Δ := by
  have hh := planar_dist_le_coordinate_sum p (coarsePlanarRound Δ p)
  simp only [coarsePlanarRound_zero,coarsePlanarRound_one] at hh
  linarith only [hh,lineGridRound_error hΔ (p 0),lineGridRound_error hΔ (p 1)]

theorem coarsePlanarRound_separated {Δ : ℝ} (hΔ : 0 < Δ) (P : Finset (Space 2)) :
    FiniteSeparatedAt Δ (P.image (coarsePlanarRound Δ)) := by
  intro x hx y hy hxy
  obtain ⟨p,_,rfl⟩ := Finset.mem_image.mp hx
  obtain ⟨q,_,rfl⟩ := Finset.mem_image.mp hy
  apply gridLine_dist_ge hΔ
    (p := (round (p 0/Δ),round (p 1/Δ)))
    (q := (round (q 0/Δ),round (q 1/Δ)))
  intro he
  exact hxy (congrArg (gridLine Δ) he)

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

theorem coarse_pencil_weight_ball {δ Δ s K : ℝ}
    (hΔ : 0 < Δ) (hδΔ : δ ≤ Δ) (hs : 0 ≤ s) (hK : 1 ≤ K)
    (P : Finset (Space 2)) (T : Space 2 → Finset (Space 2))
    (q : Space 2 → Space 2)
    (hnear : ∀ x ∈ P, ∀ l ∈ T x, dist l (q l) ≤ Δ)
    (hball : ∀ x ∈ P, NormalizedFiniteBallBound δ s K (T x)) :
    ∀ z r, Δ ≤ r → r ≤ 1 →
      (∑ a ∈ ((P.biUnion T).image q).filter (fun a => dist a z ≤ r),
        (coarsePencilWeight P T q a:ℝ)) ≤
      (K*(2:ℝ)^s)*r^s*
        (∑ a ∈ (P.biUnion T).image q, (coarsePencilWeight P T q a:ℝ)) := by
  simpa only [one_add_one_eq_two,one_mul] using
    coarse_pencil_weight_ball_mul hΔ hδΔ hs hK (C := 1) (by norm_num) P T q (by simpa only [one_mul] using hnear) hball

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
-- module Solutions.OAIQ088_FD.Falconer_Incidence_CommonTubeCount
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.sphereMeasure_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The normalized two-point common-tube kernel in the actual line chart. -/
namespace Falconer
open Set
attribute [local instance] Classical.propDecidable

theorem common_tube_card_bound {δ r b K : ℝ} (hδ : 0 < δ)
    (hr : 0 < r) (hr1 : r ≤ 1) (hsmall : 16*δ ≤ r)
    (hR1 : 80*δ/r ≤ 1) (hK : 0 ≤ K)
    (T : Finset (Space 2)) (x y : Space 2) (hx0 : |x 0| ≤ 1)
    (hxy : r ≤ dist x y) (hchart : InBoundedLineChart T)
    (hinc : ∀ l ∈ T, TubeIncident δ x l)
    (hball : NormalizedFiniteBallBound δ b K T) :
    ((T.filter (fun l => TubeIncident δ y l)).card : ℝ) ≤
      K*(80*δ/r)^b*(T.card : ℝ) := by
  let S := T.filter (fun l => TubeIncident δ y l)
  by_cases hS : S.Nonempty
  · obtain ⟨m,hm⟩ := hS
    have hmT := (Finset.mem_filter.mp hm).1
    have hmy := (Finset.mem_filter.mp hm).2
    have hsub : S ⊆ T.filter (fun l => dist l m ≤ 80*δ/r) := by
      intro l hl
      obtain ⟨hlT,hly⟩ := Finset.mem_filter.mp hl
      exact Finset.mem_filter.mpr ⟨hlT,two_point_tube_parameters_close hδ.le hr hr1 hsmall
        hx0 (hchart l hlT).1 (hchart m hmT).1 (hinc l hlT) hly (hinc m hmT) hmy hxy⟩
    have hR0 : δ ≤ 80*δ/r := by
      apply (le_div_iff₀ hr).2
      nlinarith [mul_le_mul_of_nonneg_left hr1 hδ.le]
    exact (show (S.card : ℝ) ≤ (T.filter (fun l => dist l m ≤ 80*δ/r)).card by
      exact_mod_cast Finset.card_le_card hsub).trans (hball m _ hR0 hR1)
  · have he : S = ∅ := Finset.not_nonempty_iff_eq_empty.mp hS
    change (S.card : ℝ) ≤ _
    rw [he,Finset.card_empty,Nat.cast_zero]
    exact mul_nonneg (mul_nonneg hK (Real.rpow_nonneg (by positivity) _)) (Nat.cast_nonneg _)

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Estimates_CommonTubeKernel
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.sphereMeasure_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A common-tube kernel valid at all point separations, including the diagonal. -/
namespace Falconer
open Set
attribute [local instance] Classical.propDecidable

theorem truncatedPlanarDistance_bounds {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (x y : Space 2) :
    0 < truncatedPlanarDistance δ x y ∧ truncatedPlanarDistance δ x y ≤ 1 :=
  ⟨hδ.trans_le (le_max_left _ _),max_le hδ1 (min_le_left _ _)⟩

theorem common_tube_kernel_bound {δ b K : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hb : 0 ≤ b) (hK : 1 ≤ K) (T : Finset (Space 2)) (x y : Space 2)
    (hx0 : |x 0| ≤ 1) (hchart : InBoundedLineChart T)
    (hinc : ∀ l ∈ T, TubeIncident δ x l)
    (hball : NormalizedFiniteBallBound δ b K T) :
    ((T.filter (fun l => TubeIncident δ y l)).card : ℝ) ≤
      K*(80*δ/truncatedPlanarDistance δ x y)^b*(T.card : ℝ) := by
  let r := truncatedPlanarDistance δ x y
  obtain ⟨hr,hr1⟩ := truncatedPlanarDistance_bounds hδ hδ1 x y
  change 0 < r at hr
  change r ≤ 1 at hr1
  by_cases hsmall : 80*δ ≤ r
  · have hlow : 16*δ ≤ r := by linarith
    have hR : 80*δ/r ≤ 1 := (div_le_one hr).2 hsmall
    have hrδ : δ < r := by linarith
    have hdist : r ≤ dist x y := by
      have hm : δ < min 1 (dist x y) := (lt_max_iff.mp hrδ).resolve_left (lt_irrefl _)
      change max δ (min 1 (dist x y)) ≤ dist x y
      rw [max_eq_right hm.le]
      exact min_le_right _ _
    exact common_tube_card_bound hδ hr hr1 hlow hR (zero_le_one.trans hK)
      T x y hx0 hdist hchart hinc hball
  · have hR : 1 ≤ 80*δ/r := (le_div_iff₀ hr).2 (by linarith)
    have hp : 1 ≤ (80*δ/r)^b := by
      simpa only [Real.one_rpow] using Real.rpow_le_rpow (by norm_num : (0:ℝ) ≤ 1) hR hb
    have hm : 1 ≤ K*(80*δ/r)^b := by nlinarith
    calc
      _ ≤ (T.card : ℝ) := by exact_mod_cast Finset.card_filter_le T _
      _ ≤ _ := by nlinarith [Nat.cast_nonneg (α := ℝ) T.card]

theorem intersect_tube_kernel_bound {δ b K : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hb : 0 ≤ b) (hK : 1 ≤ K) (T U : Finset (Space 2)) (x y : Space 2)
    (hx0 : |x 0| ≤ 1) (hchart : InBoundedLineChart T)
    (hx : ∀ l ∈ T, TubeIncident δ x l) (hy : ∀ l ∈ U, TubeIncident δ y l)
    (hball : NormalizedFiniteBallBound δ b K T) :
    ((T ∩ U).card : ℝ) ≤ K*(80*δ/truncatedPlanarDistance δ x y)^b*(T.card : ℝ) := by
  have hsub : T ∩ U ⊆ T.filter (fun l => TubeIncident δ y l) := by
    intro l hl
    obtain ⟨hlT,hlU⟩ := Finset.mem_inter.mp hl
    exact Finset.mem_filter.mpr ⟨hlT,hy l hlU⟩
  exact (show ((T ∩ U).card : ℝ) ≤ (T.filter (fun l => TubeIncident δ y l)).card by
    exact_mod_cast Finset.card_le_card hsub).trans
      (common_tube_kernel_bound hδ hδ1 hb hK T x y hx0 hchart hx hball)

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Estimates_CommonTubePower
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.sphereMeasure_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Separating the scale power from the truncated common-tube kernel. -/
namespace Falconer
open Set
attribute [local instance] Classical.propDecidable

theorem truncatedPlanarDistance_inverse_power_le {δ b : ℝ} (_hδ : 0 < δ)
    (hδ1 : δ ≤ 1) (x y : Space 2) :
    (1/truncatedPlanarDistance δ x y)^b ≤
      1+(1/max (dist x y) δ)^b := by
  rcases le_total (dist x y) 1 with hd | hd
  · simp only [truncatedPlanarDistance,min_eq_right hd,max_comm δ (dist x y)]
    linarith
  · simp only [truncatedPlanarDistance,min_eq_left hd,max_eq_right hδ1,
      div_one,Real.one_rpow]
    have hp : 0 ≤ (1/max (dist x y) δ)^b := by positivity
    linarith

theorem intersect_tube_power_bound {δ b K : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hb : 0 ≤ b) (hK : 1 ≤ K) (T U : Finset (Space 2)) (x y : Space 2)
    (hx0 : |x 0| ≤ 1) (hchart : InBoundedLineChart T)
    (hx : ∀ l ∈ T, TubeIncident δ x l) (hy : ∀ l ∈ U, TubeIncident δ y l)
    (hball : NormalizedFiniteBallBound δ b K T) :
    ((T ∩ U).card : ℝ) ≤
      (K*(80*δ)^b*(T.card : ℝ))*(1+(1/max (dist x y) δ)^b) := by
  have hr := (truncatedPlanarDistance_bounds hδ hδ1 x y).1
  have he : (80*δ/truncatedPlanarDistance δ x y)^b =
      (80*δ)^b*(1/truncatedPlanarDistance δ x y)^b := by
    rw [← Real.mul_rpow (by positivity) (by positivity)]
    congr 1
    ring
  have hh := intersect_tube_kernel_bound hδ hδ1 hb hK T U x y hx0 hchart hx hy hball
  rw [he] at hh
  apply hh.trans
  have hp := mul_le_mul_of_nonneg_left (truncatedPlanarDistance_inverse_power_le hδ hδ1 x y (b := b))
    (show 0 ≤ K*(80*δ)^b*(T.card : ℝ) by positivity)
  convert hp using 1
  all_goals try with_reducible_and_instances rfl
  ring

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

theorem localPacketPoint_chart {Δ y a : ℝ} (hΔ : 0 < Δ)
    (P : Finset (Space 2))
    (hP : ∀ p ∈ P, |p 0-y| ≤ Δ ∧ |p 1-a| ≤ Δ) :
    InBoundedLineChart (P.image (localPacketPoint Δ y a)) := by
  intro q hq
  obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp hq
  constructor
  · change |(p 0-y)/Δ| ≤ 1
    rw [abs_div,abs_of_pos hΔ]
    exact (div_le_one hΔ).2 (hP p hp).1
  · change |(p 1-a)/Δ| ≤ 1
    rw [abs_div,abs_of_pos hΔ]
    exact (div_le_one hΔ).2 (hP p hp).2

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

theorem localPacketPoint_regular {δ Δ t K : ℝ} (hδ : 0 < δ) (hΔ : 0 < Δ)
    (hΔ1 : Δ ≤ 1) (y a : ℝ) (P : Finset (Space 2))
    (hreg : NormalizedFiniteBallBound δ t K P) :
    NormalizedFiniteBallBound (δ/Δ) t (K*Δ^t) (P.image (localPacketPoint Δ y a)) := by
  intro z r hr hr1
  have hr0 : 0 < r := (div_pos hδ hΔ).trans_le hr
  have hδr : δ ≤ Δ*r := by nlinarith only [(div_le_iff₀ hΔ).1 hr]
  have hΔr : Δ*r ≤ 1 := (mul_le_mul hΔ1 hr1 hr0.le (by norm_num)).trans_eq (by norm_num)
  have hsub : (P.image (localPacketPoint Δ y a)).filter (fun p => dist p z ≤ r) ⊆
      (P.filter (fun p => dist p (Δ • z+rowPoint y a) ≤ Δ*r)).image (localPacketPoint Δ y a) := by
    intro p hp
    obtain ⟨hp,hpr⟩ := Finset.mem_filter.mp hp
    obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hp
    refine Finset.mem_image.mpr ⟨x,Finset.mem_filter.mpr ⟨hx,?_⟩,rfl⟩
    have he := localPacketPoint_dist hΔ y a x (Δ • z+rowPoint y a)
    rw [localPacketPoint_inverse hΔ] at he
    rw [he] at hpr
    nlinarith only [(div_le_iff₀ hΔ).1 hpr]
  rw [Finset.card_image_of_injective _ (localPacketPoint_injective hΔ y a)]
  calc
    _ ≤ ((P.filter (fun p => dist p (Δ • z+rowPoint y a) ≤ Δ*r)).card:ℝ) := by
      exact_mod_cast (Finset.card_le_card hsub).trans Finset.card_image_le
    _ ≤ K*(Δ*r)^t*(P.card:ℝ) := hreg _ _ hδr hΔr
    _ = _ := by rw [Real.mul_rpow hΔ.le hr0.le]; ring

theorem local_packet_subset_regular {δ Δ t K C : ℝ}
    (hδ : 0 < δ) (hΔ : 0 < Δ) (hΔ1 : Δ ≤ 1) (hK : 0 ≤ K)
    (y a : ℝ) (P S : Finset (Space 2)) (hSP : S ⊆ P)
    (hsize : (P.card:ℝ) ≤ C*(S.card:ℝ)) (hreg : NormalizedFiniteBallBound δ t K P) :
    NormalizedFiniteBallBound (δ/Δ) t ((K*C)*Δ^t) (S.image (localPacketPoint Δ y a)) :=
  localPacketPoint_regular hδ hΔ hΔ1 y a S
    (normalized_finite_ball_bound_subset hδ.le hK hSP hsize hreg)

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Estimates_RegularCoarseCells
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Heavy coarse cells selected by their original point counts. Both the
coarse regularity and the fine mass retained in their union are quantitative. -/
namespace Falconer
open scoped BigOperators
attribute [local instance] Classical.propDecidable

theorem regular_coarse_cells {δ Δ t K : ℝ}
    (hΔ : 0 < Δ) (hδΔ : δ ≤ Δ) (ht : 0 ≤ t) (hK : 1 ≤ K)
    (P : Finset (Space 2)) (hP : P.Nonempty) (q : Space 2 → Space 2)
    (hnear : ∀ x ∈ P, dist x (q x) ≤ Δ)
    (hball : NormalizedFiniteBallBound δ t K P) :
    let J := Nat.log 2 P.card+1
    ∃ k : ℕ, ∃ C ⊆ P.image q, C.Nonempty ∧
      NormalizedFiniteBallBound Δ t (2*(K*(2:ℝ)^t)*(J:ℝ)) C ∧
      (P.card:ℝ) ≤ (J:ℝ)*∑ c ∈ C, ((P.filter fun x => q x = c).card:ℝ) ∧
      ∀ c ∈ C, 2^k ≤ (P.filter fun x => q x = c).card ∧
        (P.filter fun x => q x = c).card < 2^(k+1) := by
  let w := fun c => (P.filter fun x => q x = c).card
  have hw (c : Space 2) (hc : c ∈ P.image q) : 0 < w c ∧ w c ≤ P.card := by
    obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hc
    exact ⟨Finset.card_pos.mpr ⟨x,Finset.mem_filter.mpr ⟨hx,rfl⟩⟩,Finset.card_filter_le _ _⟩
  have htotal : (∑ c ∈ P.image q, (w c:ℝ)) = (P.card:ℝ) := by
    exact_mod_cast (Finset.card_eq_sum_card_image q P).symm
  have hb : ∀ z r, Δ ≤ r → r ≤ 1 →
      (∑ c ∈ (P.image q).filter (fun c => dist c z ≤ r), (w c:ℝ)) ≤
        (K*(2:ℝ)^t)*r^t*(∑ c ∈ P.image q, (w c:ℝ)) := by
    have hh := coarse_pencil_weight_ball hΔ hδΔ ht hK ({0}:Finset (Space 2))
      (fun _ => P) q (fun _ _ x hx => hnear x hx) (fun _ _ => hball)
    simpa only [coarsePencilWeight,Finset.singleton_biUnion,Finset.sum_singleton] using hh
  obtain ⟨k,C,hCP,hC,hmass,hband,hreg⟩ := weighted_dyadic_regular_subset hΔ.le
    (show 0 ≤ K*(2:ℝ)^t by positivity) (P.image q) w (hP.image q) P.card hw hb
  refine ⟨k,C,hCP,hC,hreg,?_,hband⟩
  rwa [htotal] at hmass

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Radial_HeavyCellRegularity
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Heavy-cell selection supplies the local point regularity used in the
coarse-direction projection argument, with the complete loss displayed. -/
namespace Falconer
open scoped BigOperators
attribute [local instance] Classical.propDecidable

theorem heavy_cells_local_regular {δ Δ t K J : ℝ}
    (hδ : 0 < δ) (hΔ : 0 < Δ) (hΔ1 : Δ ≤ 1) (hK : 0 ≤ K) (hJ : 0 ≤ J)
    (P C : Finset (Space 2)) (S : Space 2 → Finset (Space 2)) (k : ℕ)
    (hPball : NormalizedFiniteBallBound δ t K P)
    (hS : ∀ c ∈ C, S c ⊆ P ∧ 2^k ≤ (S c).card ∧ (S c).card < 2^(k+1))
    (hmass : (P.card:ℝ) ≤ J*(∑ c ∈ C, ((S c).card:ℝ))) :
    ∀ c ∈ C, (S c).Nonempty ∧
      NormalizedFiniteBallBound (δ/Δ) t
        ((K*(2*J*(C.card:ℝ)))*Δ^t) ((S c).image (localPacketPoint Δ (c 0) (c 1))) := by
  have hsum : (∑ c ∈ C, ((S c).card:ℝ)) ≤ (2*(2:ℝ)^k)*(C.card:ℝ) := by
    calc
      _ ≤ ∑ _c ∈ C, 2*(2:ℝ)^k := Finset.sum_le_sum fun c hc => by
        have hh : ((S c).card:ℝ) < (2:ℝ)^(k+1) := by exact_mod_cast (hS c hc).2.2
        simpa only [pow_succ,mul_comm] using hh.le
      _ = _ := by simp; ring
  intro c hc
  have hlo : (2:ℝ)^k ≤ ((S c).card:ℝ) := by exact_mod_cast (hS c hc).2.1
  have hSc : 0 < ((S c).card:ℝ) := (by positivity : (0:ℝ) < 2^k).trans_le hlo
  have hsize : (P.card:ℝ) ≤ (2*J*(C.card:ℝ))*((S c).card:ℝ) := by
    calc
      _ ≤ J*(∑ c ∈ C, ((S c).card:ℝ)) := hmass
      _ ≤ J*((2*(2:ℝ)^k)*(C.card:ℝ)) := mul_le_mul_of_nonneg_left hsum hJ
      _ = (2*J*(C.card:ℝ))*(2:ℝ)^k := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hlo (by positivity)
  exact ⟨Finset.card_pos.mp (Nat.cast_pos.mp hSc),local_packet_subset_regular
    hδ hΔ hΔ1 hK (c 0) (c 1) P (S c) (hS c hc).1 hsize hPball⟩

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Radial_HeavyPacketCells
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A regular coarse cover gives heavy cells whose original fine points
remain regular in the normalized packet chart. -/
namespace Falconer
open scoped BigOperators
attribute [local instance] Classical.propDecidable

theorem heavy_regular_packet_cells {Δ ρ t K H : ℝ}
    (hΔ : 0 < Δ) (hΔ1 : Δ ≤ 1) (hρ : 0 < ρ) (hδρ : Δ^2 ≤ ρ) (hρΔ : ρ ≤ Δ)
    (ht : 0 ≤ t) (ht1 : t ≤ 2) (hK : 1 ≤ K) (_hH : 0 ≤ H)
    (P : Finset (Space 2)) (hP : P.Nonempty) (q : Space 2 → Space 2)
    (hnear : ∀ p ∈ P, dist p (q p) ≤ ρ)
    (hball : NormalizedFiniteBallBound (Δ^2) t K P)
    (hcover : ((P.image q).card:ℝ) ≤ H/Δ^t) :
    let J := Nat.log 2 P.card+1
    let S := fun c => P.filter fun p => q p = c
    ∃ k : ℕ, ∃ C ⊆ P.image q, C.Nonempty ∧
      NormalizedFiniteBallBound ρ t (8*K*(J:ℝ)) C ∧
      (P.card:ℝ) ≤ (J:ℝ)*(∑ c ∈ C, ((S c).card:ℝ)) ∧
      ∀ c ∈ C, S c ⊆ P ∧ (S c).Nonempty ∧
        2^k ≤ (S c).card ∧ (S c).card < 2^(k+1) ∧
        (∀ p ∈ S c, |p 0-c 0| ≤ Δ ∧ |p 1-c 1| ≤ Δ) ∧
        NormalizedFiniteBallBound Δ t (2*K*(J:ℝ)*H)
          ((S c).image (localPacketPoint Δ (c 0) (c 1))) := by
  let J := Nat.log 2 P.card+1
  let S := fun c => P.filter fun p => q p = c
  have hJ : 0 ≤ (J:ℝ) := Nat.cast_nonneg _
  have hK0 : 0 ≤ K := zero_le_one.trans hK
  have hΔt : 0 < Δ^t := Real.rpow_pos_of_pos hΔ _
  obtain ⟨k,C,hCP,hC,hCball,hmass,hband⟩ := regular_coarse_cells hρ hδρ ht hK P hP q hnear hball
  have hlocal := heavy_cells_local_regular (pow_pos hΔ 2) hΔ hΔ1 hK0 hJ P C S k hball
    (fun c hc => ⟨Finset.filter_subset _ _,hband c hc⟩) hmass
  have hCsize : (C.card:ℝ) ≤ H/Δ^t :=
    (Nat.cast_le.mpr (Finset.card_le_card hCP)).trans hcover
  have hCloss : (K*(2*(J:ℝ)*(C.card:ℝ)))*Δ^t ≤ 2*K*(J:ℝ)*H := by
    have hh := (le_div_iff₀ hΔt).1 hCsize
    have hh' := mul_le_mul_of_nonneg_left hh (show 0 ≤ 2*K*(J:ℝ) by positivity)
    nlinarith only [hh']
  have h2 : (2:ℝ)^t ≤ 4 := by
    calc
      _ ≤ (2:ℝ)^(2:ℝ) := Real.rpow_le_rpow_of_exponent_le (by norm_num) ht1
      _ = 4 := by norm_num
  refine ⟨k,C,hCP,hC,?_,hmass,?_⟩
  · intro z r hr hr1
    have hr0 : 0 ≤ r := hρ.le.trans hr
    have hconstant : 2*(K*(2:ℝ)^t)*(J:ℝ) ≤ 8*K*(J:ℝ) := by
      calc
        _ ≤ 2*(K*4)*(J:ℝ) := by gcongr
        _ = _ := by ring
    exact (hCball z r hr hr1).trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hconstant (Real.rpow_nonneg hr0 _)) (Nat.cast_nonneg _))
  · intro c hc
    refine ⟨Finset.filter_subset _ _,(hlocal c hc).1,(hband c hc).1,(hband c hc).2,?_,?_⟩
    · intro p hp
      have hh := hnear p (Finset.mem_filter.mp hp).1
      rw [(Finset.mem_filter.mp hp).2] at hh
      exact ⟨(show |p 0-c 0| ≤ dist p c by simpa only [Real.dist_eq] using PiLp.dist_apply_le p c 0).trans
        (hh.trans hρΔ),
        (show |p 1-c 1| ≤ dist p c by simpa only [Real.dist_eq] using PiLp.dist_apply_le p c 1).trans
          (hh.trans hρΔ)⟩
    · have hscale : Δ^2/Δ = Δ := by field_simp
      have hb := (hlocal c hc).2
      rw [hscale] at hb
      intro z r hr hr1
      exact (hb z r hr hr1).trans (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hCloss (Real.rpow_nonneg (hΔ.le.trans hr) _)) (Nat.cast_nonneg _))

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Estimates_RegularCellConfiguration
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The regular coarse configuration with its original cell occupancies and
fine mass retained. No small coarse-tube cover is assumed here. -/
namespace Falconer
open scoped BigOperators
attribute [local instance] Classical.propDecidable

theorem regular_cell_configuration (n : ℕ) {s t K : ℝ}
    (hn : 3 ≤ n) (hs : 0 ≤ s) (ht : 0 ≤ t) (ht1 : t ≤ 2) (hK : 1 ≤ K)
    (P : Finset (Space 2)) (V : Space 2 → Finset (Space 2)) (hP : P.Nonempty)
    (hPchart : ∀ p ∈ P, |p 0| ≤ 1/8 ∧ |p 1| ≤ 1/8)
    (hPball : NormalizedFiniteBallBound ((1/(2:ℝ)^n)^2) t K P)
    (hV : ∀ p ∈ P, (V p).Nonempty ∧
      NormalizedFiniteBallBound ((1/(2:ℝ)^n)^2) s K (V p) ∧
      ∀ l ∈ V p, |l 0| ≤ 1/2 ∧ TubeIncident ((1/(2:ℝ)^n)^2) p l)
    (hpoint : ((P.image (coarsePlanarRound (1/(2:ℝ)^(n+3)))).card:ℝ) ≤
      K/(1/(2:ℝ)^n)^t) :
    let Δ := 1/(2:ℝ)^n
    let ρ := 1/(2:ℝ)^(n+3)
    let q := coarsePlanarRound ρ
    let S := fun c => P.filter fun p => q p = c
    let Jp := Nat.log 2 P.card+1
    let Jv := Nat.log 2 (∑ p ∈ P, (V p).card)+1
    ∃ k : ℕ, ∃ C ⊆ P.image q, C.Nonempty ∧
      (∀ c ∈ C, |c 0| ≤ 1/4 ∧ |c 1| ≤ 1/4) ∧ FiniteSeparatedAt ρ C ∧
      NormalizedFiniteBallBound ρ t (8*K*(Jp:ℝ)) C ∧
      (P.card:ℝ) ≤ (Jp:ℝ)*(∑ c ∈ C, ((S c).card:ℝ)) ∧
      (∀ c ∈ C, (S c).Nonempty ∧ 2^k ≤ (S c).card ∧ (S c).card < 2^(k+1) ∧
        (∀ p ∈ S c, |p 0-c 0| ≤ Δ/4 ∧ |p 1-c 1| ≤ Δ/4) ∧
        NormalizedFiniteBallBound Δ t (2*K*(Jp:ℝ)*K)
          ((S c).image (localPacketPoint Δ (c 0) (c 1)))) ∧
      ∃ T : Space 2 → Finset (Space 2),
        (∀ c ∈ C, (T c).Nonempty ∧ InBoundedLineChart (T c) ∧ FiniteSeparatedAt ρ (T c) ∧
          NormalizedFiniteBallBound ρ s (2*(K*7^s)*(Jv:ℝ)) (T c) ∧
          ∀ a ∈ T c, TubeIncident ρ c a ∧
            ((∑ p ∈ S c, (V p).card):ℝ) ≤ 2*(Jv:ℝ)*((T c).card:ℝ)*
              (coarsePencilWeight (S c) V (fun l => roundedIncidentLine ρ c (l 0)) a:ℝ)) ∧
        ((C.biUnion T).card:ℝ) ≤ 13*(((P.biUnion V).image q).card:ℝ) ∧
        let G := fineCoarsePacket ρ C (fun c => (S c).biUnion V)
        (∀ a ∈ C.biUnion T, (G a).Nonempty ∧ (G a).card ≤ (P.biUnion V).card) ∧
        (∑ a ∈ C.biUnion T, ((G a).card:ℝ)) ≤ 13*((P.biUnion V).card:ℝ) ∧
        (∀ c ∈ C, ∀ p ∈ S c, ∀ l ∈ V p, l ∈ G (roundedIncidentLine ρ c (l 0))) := by
  let Δ := 1/(2:ℝ)^n
  let ρ := 1/(2:ℝ)^(n+3)
  let q := coarsePlanarRound ρ
  let S := fun c => P.filter fun p => q p = c
  have hΔ : 0 < Δ := by dsimp [Δ]; positivity
  have hρ : 0 < ρ := by dsimp [ρ]; positivity
  have hscale : ρ = Δ/8 := by dsimp [ρ,Δ]; rw [pow_add]; norm_num; ring
  have hΔ8 : Δ ≤ 1/8 := by
    apply one_div_le_one_div_of_le (by norm_num : (0:ℝ) < 8)
    have hh := pow_le_pow_right₀ (by norm_num : (1:ℝ) ≤ 2) hn
    norm_num at hh
    exact hh
  have hδρ : Δ^2 ≤ ρ := by rw [hscale]; nlinarith only [hΔ8,hΔ]
  have hρΔ : ρ ≤ Δ := by rw [hscale]; linarith only [hΔ]
  have hρ8 : ρ ≤ 1/8 := hρΔ.trans hΔ8
  have hnear : ∀ p ∈ P, dist p (q p) ≤ ρ := fun p _ => coarsePlanarRound_near hρ p
  have hqchart : ∀ c ∈ P.image q, |c 0| ≤ 1/4 ∧ |c 1| ≤ 1/4 := by
    intro c hc
    obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp hc
    have bound (i : Fin 2) (hi : |p i| ≤ 1/8) : |q p i| ≤ 1/4 := by
      have hd : |q p i-p i| ≤ ρ := (show |q p i-p i| ≤ dist (q p) p by
        simpa only [Real.dist_eq] using PiLp.dist_apply_le (q p) p i).trans
          (by simpa only [dist_comm] using hnear p hp)
      calc
        _ ≤ |q p i-p i|+|p i| := by simpa using abs_add_le (q p i-p i) (p i)
        _ ≤ 1/4 := by linarith only [hd,hi,hρ8]
    exact ⟨bound 0 (hPchart p hp).1,bound 1 (hPchart p hp).2⟩
  obtain ⟨k,C,hCP,hC,hCb,hmass,hcells⟩ := heavy_regular_packet_cells hΔ
    (hΔ8.trans (by norm_num)) hρ hδρ hρΔ ht ht1 hK (zero_le_one.trans hK)
    P hP q hnear hPball hpoint
  have hCchart := fun c hc => hqchart c (hCP hc)
  obtain ⟨T,hT⟩ := coarse_cell_pencils (sq_nonneg Δ) hρ (hρ8.trans (by norm_num)) hδρ
    hs hK P C V q hCP hnear hCchart hV
  obtain ⟨hGne,hGsub,hGmem,hGsum,hTsum⟩ := original_coarse_packets (sq_nonneg Δ)
    hρ hδρ P C V T q hnear (fun c hc => (hCchart c hc).1.trans (by norm_num))
    (fun p hp l hl => ⟨((hV p hp).2.2 l hl).1.trans (by norm_num),(hV p hp).2.2 l hl |>.2⟩)
    (fun c hc => (hT c hc).1)
  refine ⟨k,C,hCP,hC,hCchart,finiteSeparatedAt_subset hCP (coarsePlanarRound_separated hρ P),
    hCb,hmass,?_,T,?_,hTsum,?_,hGsum,?_⟩
  · intro c hc
    obtain ⟨_,hne,hlo,hup,_,hball⟩ := hcells c hc
    refine ⟨hne,hlo,hup,?_,hball⟩
    intro p hp
    have hd := hnear p (Finset.mem_filter.mp hp).1
    have hpc : q p = c := (Finset.mem_filter.mp hp).2
    rw [hpc] at hd
    have h0 : |p 0-c 0| ≤ dist p c := by simpa only [Real.dist_eq] using PiLp.dist_apply_le p c 0
    have h1 : |p 1-c 1| ≤ dist p c := by simpa only [Real.dist_eq] using PiLp.dist_apply_le p c 1
    rw [hscale] at hd
    constructor <;> linarith only [h0,h1,hd,hΔ]
  · intro c hc
    obtain ⟨_,hne,hchart,hsep,hreg,hweight,_⟩ := hT c hc
    exact ⟨hne,hchart,hsep,hreg,hweight⟩
  · exact fun a ha => ⟨hGne a ha,Finset.card_le_card (hGsub a)⟩
  · exact fun c hc p hp l hl => hGmem c hc p (Finset.mem_filter.mp hp).1
      (Finset.mem_filter.mp hp).2 l hl

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
-- module Solutions.OAIQ088_FD.Falconer_Measures_CellRefinementMass
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Uniform coarse-cell occupancy converts a retained proportion of cells
and a retained proportion inside each cell into original fine-point mass. -/
namespace Falconer
open scoped BigOperators
attribute [local instance] Classical.propDecidable

theorem cell_refinement_mass {J L F w : ℝ}
    (hJ : 0 ≤ J) (hL : 0 ≤ L) (_hF : 0 ≤ F) (hw : 0 ≤ w)
    (P C R : Finset (Space 2)) (q : Space 2 → Space 2)
    (A : Space 2 → Finset (Space 2)) (hRC : R ⊆ C)
    (hmass : (P.card:ℝ) ≤ J*∑ c ∈ C, ((P.filter fun p => q p = c).card:ℝ))
    (hband : ∀ c ∈ C, w ≤ ((P.filter fun p => q p = c).card:ℝ) ∧
      ((P.filter fun p => q p = c).card:ℝ) ≤ 2*w)
    (hcount : (C.card:ℝ) ≤ L*(R.card:ℝ))
    (hA : ∀ c ∈ R, A c ⊆ P.filter (fun p => q p = c) ∧
      ((P.filter fun p => q p = c).card:ℝ) ≤ F*((A c).card:ℝ)) :
    R.biUnion A ⊆ P ∧ (P.card:ℝ) ≤ (2*J*L*F)*((R.biUnion A).card:ℝ) := by
  have hsub : R.biUnion A ⊆ P := by
    intro p hp
    obtain ⟨c,hc,hp⟩ := Finset.mem_biUnion.mp hp
    exact (Finset.mem_filter.mp ((hA c hc).1 hp)).1
  have hd : (R : Set (Space 2)).PairwiseDisjoint A := by
    intro c hc d hd hcd
    apply Finset.disjoint_left.mpr
    intro p hpc hpd
    have hqc := (Finset.mem_filter.mp ((hA c hc).1 hpc)).2
    have hqd := (Finset.mem_filter.mp ((hA d hd).1 hpd)).2
    exact hcd (hqc.symm.trans hqd)
  have hcard : ((R.biUnion A).card:ℝ) = ∑ c ∈ R, ((A c).card:ℝ) := by
    exact_mod_cast Finset.card_biUnion hd
  have hlocal : w*(R.card:ℝ) ≤ F*((R.biUnion A).card:ℝ) := by
    calc
      _ = ∑ _c ∈ R, w := by simp; ring
      _ ≤ ∑ c ∈ R, F*((A c).card:ℝ) := Finset.sum_le_sum fun c hc =>
        ((hband c (hRC hc)).1.trans (hA c hc).2)
      _ = _ := by rw [← Finset.mul_sum,hcard]
  refine ⟨hsub,?_⟩
  calc
    (P.card:ℝ) ≤ J*∑ c ∈ C, ((P.filter fun p => q p = c).card:ℝ) := hmass
    _ ≤ J*∑ _c ∈ C, 2*w := mul_le_mul_of_nonneg_left
      (Finset.sum_le_sum fun c hc => (hband c hc).2) hJ
    _ = 2*J*w*(C.card:ℝ) := by simp; ring
    _ ≤ 2*J*w*(L*(R.card:ℝ)) := mul_le_mul_of_nonneg_left hcount (by positivity)
    _ = (2*J*L)*(w*(R.card:ℝ)) := by ring
    _ ≤ (2*J*L)*(F*((R.biUnion A).card:ℝ)) :=
      mul_le_mul_of_nonneg_left hlocal (by positivity)
    _ = _ := by ring

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Estimates_RetainedRegularCells
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Simultaneous fine-point and pencil refinement in the retained coarse
cells, with global mass and local regularity inherited from the originals. -/
namespace Falconer
open scoped BigOperators
attribute [local instance] Classical.propDecidable

theorem retained_regular_cells {δ Δ s t K m M H B b J L w : ℝ}
    (hδ : 0 ≤ δ) (hΔ : 0 ≤ Δ) (hK : 1 ≤ K) (hm : 0 < m) (hM : 0 < M)
    (hH : 0 < H) (hB : 0 < B) (hb : 0 < b) (hJ : 0 ≤ J) (hL : 0 ≤ L) (hw : 0 ≤ w)
    (P C R : Finset (Space 2)) (q : Space 2 → Space 2)
    (T U : Space 2 → Finset (Space 2)) (ql X : Space 2 → Space 2 → Space 2)
    (hR : R.Nonempty) (hRC : R ⊆ C)
    (hPball : NormalizedFiniteBallBound δ t K P)
    (hmass : (P.card:ℝ) ≤ J*∑ c ∈ C, ((P.filter fun p => q p = c).card:ℝ))
    (hband : ∀ c ∈ C, w ≤ ((P.filter fun p => q p = c).card:ℝ) ∧
      ((P.filter fun p => q p = c).card:ℝ) ≤ 2*w)
    (hcount : (C.card:ℝ) ≤ L*(R.card:ℝ))
    (hcell : ∀ c ∈ R, (P.filter fun p => q p = c).Nonempty ∧
      Function.Injective (X c) ∧
      NormalizedFiniteBallBound Δ t K ((P.filter fun p => q p = c).image (X c)))
    (hT : ∀ p ∈ P, m ≤ ((T p).card:ℝ) ∧ ((T p).card:ℝ) ≤ M ∧
      NormalizedFiniteBallBound δ s K (T p))
    (hU : ∀ c ∈ R, b ≤ ((U c).card:ℝ) ∧
      ∀ a ∈ U c, (∑ p ∈ P.filter (fun p => q p = c), ((T p).card:ℝ)) ≤
        H*B*(coarsePencilWeight (P.filter (fun p => q p = c)) T (ql c) a:ℝ)) :
    let E := H*B/b
    let F := 2*E*M/m
    let V := fun p => (T p).filter fun l => ql (q p) l ∈ U (q p)
    ∃ A : Space 2 → Finset (Space 2),
      (∀ c ∈ R, A c ⊆ P.filter (fun p => q p = c) ∧ (A c).Nonempty ∧
        ((P.filter fun p => q p = c).card:ℝ) ≤ F*((A c).card:ℝ) ∧
        NormalizedFiniteBallBound Δ t (K*F) ((A c).image (X c)) ∧
        ∀ p ∈ A c, V p ⊆ T p ∧ m/(2*E) ≤ ((V p).card:ℝ) ∧
          ((V p).card:ℝ) ≤ M ∧ NormalizedFiniteBallBound δ s (K*F) (V p) ∧
          ∀ l ∈ V p, ql c l ∈ U c) ∧
      R.biUnion A ⊆ P ∧ (R.biUnion A).Nonempty ∧
      (P.card:ℝ) ≤ (2*J*L*F)*((R.biUnion A).card:ℝ) ∧
      NormalizedFiniteBallBound δ t (K*(2*J*L*F)) (R.biUnion A) := by
  let S := fun c => P.filter fun p => q p = c
  let E := H*B/b
  let F := 2*E*M/m
  let V := fun p => (T p).filter fun l => ql (q p) l ∈ U (q p)
  have hK0 : 0 ≤ K := zero_le_one.trans hK
  have hF : 0 ≤ F := by dsimp [F,E]; positivity
  have hzero (c : Space 2) : NormalizedFiniteBallBound δ 0 K (S c) := by
    intro z r _ _
    simp only [Real.rpow_zero,mul_one]
    exact (Nat.cast_le.mpr (Finset.card_filter_le _ _)).trans
      (le_mul_of_one_le_left (Nat.cast_nonneg _) hK)
  have hchoice (c : Space 2) (hc : c ∈ R) := retain_coarse_incidences hδ hK0 hm hM hH hB hb
    (S c) (U c) T (ql c) (hcell c hc).1 (hU c hc).1 (hzero c)
    (fun p hp => hT p (Finset.mem_filter.mp hp).1) (hU c hc).2
  let A := fun c => if hc : c ∈ R then Classical.choose (hchoice c hc) else ∅
  have hdata (c : Space 2) (hc : c ∈ R) :
      A c ⊆ S c ∧ (A c).Nonempty ∧ ((S c).card:ℝ) ≤ F*((A c).card:ℝ) ∧
      NormalizedFiniteBallBound Δ t (K*F) ((A c).image (X c)) ∧
      ∀ p ∈ A c, V p ⊆ T p ∧ m/(2*E) ≤ ((V p).card:ℝ) ∧
        ((V p).card:ℝ) ≤ M ∧ NormalizedFiniteBallBound δ s (K*F) (V p) ∧
        ∀ l ∈ V p, ql c l ∈ U c := by
    have hh := Classical.choose_spec (hchoice c hc)
    have he : A c = Classical.choose (hchoice c hc) := dite_eq_left hc
    rw [← he] at hh
    obtain ⟨hAS,hA,hsize,_,hfine⟩ := hh
    refine ⟨hAS,hA,hsize,?_,?_⟩
    · have hi := (hcell c hc).2.1
      have himage : (((S c).image (X c)).card:ℝ) ≤ F*(((A c).image (X c)).card:ℝ) := by
        simpa only [Finset.card_image_of_injective _ hi] using hsize
      exact normalized_finite_ball_bound_subset hΔ hK0 (Finset.image_subset_image hAS)
        himage (hcell c hc).2.2
    · intro p hp
      have hpc : q p = c := (Finset.mem_filter.mp (hAS hp)).2
      have hv : V p = (T p).filter (fun l => ql c l ∈ U c) := by dsimp [V]; rw [hpc]
      rw [hv]
      obtain ⟨hsub,hlo,hup,hreg⟩ := hfine p hp
      exact ⟨hsub,hlo,hup,hreg,fun l hl => (Finset.mem_filter.mp hl).2⟩
  obtain ⟨hsub,hmass'⟩ := cell_refinement_mass hJ hL hF hw P C R q A hRC hmass hband hcount
    (fun c hc => ⟨(hdata c hc).1,(hdata c hc).2.2.1⟩)
  have hne : (R.biUnion A).Nonempty := by
    obtain ⟨c,hc⟩ := hR
    obtain ⟨p,hp⟩ := (hdata c hc).2.1
    exact ⟨p,Finset.mem_biUnion.mpr ⟨c,hc,hp⟩⟩
  exact ⟨A,hdata,hsub,hne,hmass',normalized_finite_ball_bound_subset hδ hK0 hsub hmass' hPball⟩

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Geometry_RetainedCoarseCover
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The common-grid cover of retained fine lines is bounded by the
retained incident coarse pencils, in the reverse direction needed when
applying the regular-set alternative after refinement. -/
namespace Falconer
attribute [local instance] Classical.propDecidable

theorem rounded_candidates_reverse {δ : ℝ} (hδ : 0 < δ)
    (l a : Space 2) (L : ℕ) (ha : a ∈ roundedStripCandidates δ (l 0) (l 1) L) :
    coarsePlanarRound δ l ∈ roundedStripCandidates δ (a 0) (a 1) L := by
  obtain ⟨j,hj,rfl⟩ := Finset.mem_image.mp ha
  have hjb := Finset.mem_Icc.mp hj
  apply Finset.mem_image.mpr
  refine ⟨round (l 1/δ),?_,?_⟩
  · simp only [gridLine_snd,mul_div_cancel_left₀ _ hδ.ne',round_intCast]
    exact Finset.mem_Icc.mpr ⟨by omega,by omega⟩
  · simp only [gridLine_fst,mul_div_cancel_left₀ _ hδ.ne',round_intCast]
    rfl

theorem retained_coarse_cover_card {δ : ℝ} (hδ : 0 < δ)
    (C : Finset (Space 2)) (T D : Space 2 → Finset (Space 2))
    (hc : ∀ c ∈ C, |c 0| ≤ 1)
    (hres : ∀ c ∈ C, ∀ l ∈ T c, |c 1-l 0*c 0-l 1| ≤ 4*δ)
    (hretain : ∀ c ∈ C, ∀ l ∈ T c, roundedIncidentLine δ c (l 0) ∈ D c) :
    (((C.biUnion T).image (coarsePlanarRound δ)).card:ℝ) ≤
      13*((C.biUnion D).card:ℝ) := by
  have hsub : (C.biUnion T).image (coarsePlanarRound δ) ⊆
      (C.biUnion D).biUnion (fun a => roundedStripCandidates δ (a 0) (a 1) 6) := by
    intro b hb
    obtain ⟨l,hl,rfl⟩ := Finset.mem_image.mp hb
    obtain ⟨c,hcC,hl⟩ := Finset.mem_biUnion.mp hl
    refine Finset.mem_biUnion.mpr ⟨roundedIncidentLine δ c (l 0),
      Finset.mem_biUnion.mpr ⟨c,hcC,hretain c hcC l hl⟩,?_⟩
    exact rounded_candidates_reverse hδ l _ 6
      (roundedIncidentLine_mem_candidates hδ c (hc c hcC) (hres c hcC l hl) 6 (by norm_num))
  calc
    _ ≤ ∑ a ∈ C.biUnion D, ((roundedStripCandidates δ (a 0) (a 1) 6).card:ℝ) := by
      exact_mod_cast (Finset.card_le_card hsub).trans Finset.card_biUnion_le
    _ ≤ ∑ _a ∈ C.biUnion D, (13:ℝ) := Finset.sum_le_sum fun a _ => by
      exact_mod_cast roundedStripCandidates_card_le δ (a 0) (a 1) 6
    _ = _ := by simp; ring

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Geometry_ProjectionSampleBudget
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Uniform polynomial costs for the robust projection step. These bounds
keep every loss explicit before the dyadic exponential absorption. -/
namespace Falconer

theorem projectionGapConstant_pos {κ : ℝ} (hκ : 0 < κ) :
    0 < projectionGapConstant κ := by
  have hd : 0 < 1-(2:ℝ)^(-κ) := sub_pos.mpr
    (Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith only [hκ]))
  unfold projectionGapConstant
  positivity

theorem planarPotentialConstant_gap {κ s t : ℝ} (hκ : 0 < κ)
    (hs : s ≤ 1) (hgap : κ ≤ t-s) :
    planarPotentialConstant s t ≤ projectionGapConstant κ := by
  have hp : (2:ℝ)^s ≤ 2 := by
    simpa only [Real.rpow_one] using
      Real.rpow_le_rpow_of_exponent_le (by norm_num : (1:ℝ) ≤ 2) hs
  have hq : (2:ℝ)^(s-t) ≤ (2:ℝ)^(-κ) :=
    Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith only [hgap])
  have hd : 0 < 1-(2:ℝ)^(-κ) := sub_pos.mpr
    (Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith only [hκ]))
  have hden : 1-(2:ℝ)^(-κ) ≤ 1-(2:ℝ)^(s-t) := by linarith only [hq]
  have hquot : (2:ℝ)^s/(1-(2:ℝ)^(s-t)) ≤ 2/(1-(2:ℝ)^(-κ)) :=
    (div_le_div_of_nonneg_right hp (hd.le.trans hden)).trans
      (div_le_div_of_nonneg_left (by norm_num) hd hden)
  have hden0 : 0 < 1-(2:ℝ)^(s-t) := hd.trans_le hden
  have hq0 : 0 ≤ (2:ℝ)^s/(1-(2:ℝ)^(s-t)) := by positivity
  unfold planarPotentialConstant projectionGapConstant
  gcongr

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Incidence_PencilSecondMoment
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The geometric second-moment bound, allowing unequal pencil sizes. -/
namespace Falconer
open scoped BigOperators
attribute [local instance] Classical.propDecidable

theorem pencil_second_moment_bound (N : ℕ) {s t K M : ℝ}
    (hs : 0 ≤ s) (hst : s < t) (hK : 1 ≤ K)
    (P : Finset (Space 2)) (T : Space 2 → Finset (Space 2))
    (hPchart : InBoundedLineChart P)
    (hPball : NormalizedFiniteBallBound (1/(2:ℝ)^N) t K P)
    (hT : ∀ x ∈ P, InBoundedLineChart (T x) ∧
      NormalizedFiniteBallBound (1/(2:ℝ)^N) s K (T x) ∧
      ((T x).card:ℝ) ≤ M ∧ ∀ l ∈ T x, TubeIncident (1/(2:ℝ)^N) x l) :
    (∑ l ∈ P.biUnion T, (tubeDegree P T l)^2) ≤
      (K*(80*(1/(2:ℝ)^N))^s*M)*(1+K*planarPotentialConstant s t)*(P.card:ℝ)^2 := by
  let δ := 1/(2:ℝ)^N
  let C := K*(80*δ)^s*M
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hδ1 : δ ≤ 1 := (div_le_one (by positivity)).2 (one_le_pow₀ (by norm_num))
  have hK0 : 0 ≤ K := zero_le_one.trans hK
  have hrow (x : Space 2) (hx : x ∈ P) :
      (∑ y ∈ P, ((T x ∩ T y).card:ℝ)) ≤ C*(1+K*planarPotentialConstant s t)*(P.card:ℝ) := by
    have hM : 0 ≤ M := (Nat.cast_nonneg (T x).card).trans (hT x hx).2.2.1
    have hC : 0 ≤ C := by dsimp [C]; positivity
    have hpot := finite_dyadic_truncated_potential_real P x N hK hs hst hPball
    calc
      _ ≤ ∑ y ∈ P, C*(1+(1/max (dist x y) δ)^s) := by
        apply Finset.sum_le_sum
        intro y hy
        apply (intersect_tube_power_bound hδ hδ1 hs hK (T x) (T y) x y
          (hPchart x hx).1 (hT x hx).1 (hT x hx).2.2.2
          (hT y hy).2.2.2 (hT x hx).2.1).trans
        exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (hT x hx).2.2.1
          (by positivity)) (by positivity)
      _ = C*((P.card:ℝ)+∑ y ∈ P, (1/max (dist x y) δ)^s) := by
        simp only [mul_add,Finset.sum_add_distrib,Finset.sum_const,nsmul_eq_mul,mul_one]
        rw [← Finset.mul_sum]
        ring
      _ ≤ C*((P.card:ℝ)+K*planarPotentialConstant s t*(P.card:ℝ)) :=
        mul_le_mul_of_nonneg_left (add_le_add le_rfl hpot) hC
      _ = _ := by ring
  rw [sum_tubeDegree_sq]
  calc
    _ ≤ ∑ _x ∈ P, C*(1+K*planarPotentialConstant s t)*(P.card:ℝ) :=
      Finset.sum_le_sum hrow
    _ = _ := by simp only [Finset.sum_const,nsmul_eq_mul]; dsimp [C]; ring

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Incidence_VariableBaselineIncidence
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The baseline incidence estimate for unequal pencil sizes, as needed
before and after weighted packet freezing. -/
namespace Falconer
open scoped BigOperators
attribute [local instance] Classical.propDecidable

theorem planar_variable_baseline_incidence (N : ℕ) {s t K m M : ℝ}
    (hs : 0 ≤ s) (hst : s < t) (hK : 1 ≤ K) (hm : 0 ≤ m)
    (P : Finset (Space 2)) (T : Space 2 → Finset (Space 2)) (hP : P.Nonempty)
    (hPchart : InBoundedLineChart P)
    (hPball : NormalizedFiniteBallBound (1/(2:ℝ)^N) t K P)
    (hT : ∀ x ∈ P, m ≤ ((T x).card:ℝ) ∧ ((T x).card:ℝ) ≤ M ∧
      InBoundedLineChart (T x) ∧ NormalizedFiniteBallBound (1/(2:ℝ)^N) s K (T x) ∧
      ∀ l ∈ T x, TubeIncident (1/(2:ℝ)^N) x l) :
    m^2 ≤ ((P.biUnion T).card:ℝ)*
      ((K*(80*(1/(2:ℝ)^N))^s*M)*(1+K*planarPotentialConstant s t)) := by
  let C := (K*(80*(1/(2:ℝ)^N))^s*M)*(1+K*planarPotentialConstant s t)
  have hI : m*(P.card:ℝ) ≤ ∑ x ∈ P, ((T x).card:ℝ) := by
    calc
      _ = ∑ _x ∈ P, m := by simp; ring
      _ ≤ _ := Finset.sum_le_sum fun x hx => (hT x hx).1
  have hH := pencil_second_moment_bound N hs hst hK P T hPchart hPball
    (fun x hx => ⟨(hT x hx).2.2.1,(hT x hx).2.2.2.1,(hT x hx).2.1,(hT x hx).2.2.2.2⟩)
  have hh : (m*(P.card:ℝ))^2 ≤ ((P.biUnion T).card:ℝ)*(C*(P.card:ℝ)^2) := by
    calc
      _ ≤ (∑ x ∈ P, ((T x).card:ℝ))^2 :=
        (sq_le_sq₀ (by positivity) (Finset.sum_nonneg fun x _ => Nat.cast_nonneg _)).2 hI
      _ ≤ ((P.biUnion T).card:ℝ)*(∑ x ∈ P, ∑ y ∈ P, ((T x ∩ T y).card:ℝ)) :=
        tube_union_second_moment P T
      _ = ((P.biUnion T).card:ℝ)*(∑ l ∈ P.biUnion T, (tubeDegree P T l)^2) := by
        rw [sum_tubeDegree_sq]
      _ ≤ _ := mul_le_mul_of_nonneg_left hH (Nat.cast_nonneg _)
  have hPc : 0 < (P.card:ℝ) := Nat.cast_pos.mpr hP.card_pos
  apply (mul_le_mul_iff_left₀ (sq_pos_of_pos hPc)).1
  first | (convert hh using 1 <;> ring) | exact (le_of_eq (by ring)).trans (hh.trans (le_of_eq (by ring)))

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

theorem comparable_pencil_size_upper (N : ℕ) {s t K m L : ℝ}
    (hs : 0 ≤ s) (hst : s < t) (hK : 1 ≤ K) (hm : 0 < m) (_hL : 0 ≤ L)
    (P : Finset (Space 2)) (T : Space 2 → Finset (Space 2)) (hP : P.Nonempty)
    (hPchart : InBoundedLineChart P)
    (hPball : NormalizedFiniteBallBound (1/(2:ℝ)^N) t K P)
    (hT : ∀ x ∈ P, m ≤ ((T x).card:ℝ) ∧ ((T x).card:ℝ) ≤ 2*m ∧
      InBoundedLineChart (T x) ∧ NormalizedFiniteBallBound (1/(2:ℝ)^N) s K (T x) ∧
      ∀ l ∈ T x, TubeIncident (1/(2:ℝ)^N) x l)
    (hunion : ((P.biUnion T).card:ℝ) ≤ L) :
    m ≤ 2*L*K*(80*(1/(2:ℝ)^N))^s*(1+K*planarPotentialConstant s t) := by
  have hp := planarPotentialConstant_pos hst
  have hK0 : 0 ≤ K := zero_le_one.trans hK
  have hb := planar_variable_baseline_incidence N hs hst hK hm.le P T hP hPchart hPball hT
  have hh : m^2 ≤ L*((K*(80*(1/(2:ℝ)^N))^s*(2*m))*(1+K*planarPotentialConstant s t)) :=
    hb.trans (mul_le_mul_of_nonneg_right hunion (by positivity))
  apply (mul_le_mul_iff_left₀ hm).1
  nlinarith only [hh]

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
-- module Solutions.OAIQ088_FD.Falconer_Estimates_BuildRegularRefinement
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Assemble the retained regular refinement from coarse cells and original
weighted pencils. All selection costs fit a fixed polynomial budget. -/
namespace Falconer
open scoped BigOperators
attribute [local instance] Classical.propDecidable

private theorem ball_constant_mono {δ s A B : ℝ} {P : Finset (Space 2)}
    (hδ : 0 ≤ δ) (hAB : A ≤ B) (h : NormalizedFiniteBallBound δ s A P) :
    NormalizedFiniteBallBound δ s B P := by
  intro z r hr hr1
  exact (h z r hr hr1).trans (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right hAB (Real.rpow_nonneg (hδ.trans hr) _)) (Nat.cast_nonneg _))

theorem build_regular_refinement (n k : ℕ) {s t D : ℝ}
    (hn : 3 ≤ n) (hD : 80 ≤ D)
    (P C : Finset (Space 2)) (V T G : Space 2 → Finset (Space 2))
    (hC : C.Nonempty) (hCchart : InBoundedLineChart C)
    (hPball : NormalizedFiniteBallBound ((1/(2:ℝ)^n)^2) t (D^4) P)
    (hCb : NormalizedFiniteBallBound (1/(2:ℝ)^(n+3)) t (D^4) C)
    (hJp : (Nat.log 2 P.card+1:ℕ) ≤ D)
    (hJv : (Nat.log 2 (∑ p ∈ P, (V p).card)+1:ℕ) ≤ D)
    (hJc : (Nat.log 2 (C.biUnion T).card+1:ℕ) ≤ D)
    (hJg : (Nat.log 2 (P.biUnion V).card+1:ℕ) ≤ D)
    (hmass : (P.card:ℝ) ≤ (Nat.log 2 P.card+1:ℕ)*
      ∑ c ∈ C, ((P.filter fun p => coarsePlanarRound (1/(2:ℝ)^(n+3)) p = c).card:ℝ))
    (hcell : ∀ c ∈ C,
      let S := P.filter fun p => coarsePlanarRound (1/(2:ℝ)^(n+3)) p = c
      S.Nonempty ∧ 2^k ≤ S.card ∧ S.card < 2^(k+1) ∧
      (∀ p ∈ S, |p 0-c 0| ≤ (1/(2:ℝ)^n)/4 ∧ |p 1-c 1| ≤ (1/(2:ℝ)^n)/4) ∧
      NormalizedFiniteBallBound (1/(2:ℝ)^n) t (D^4)
        (S.image (localPacketPoint (1/(2:ℝ)^n) (c 0) (c 1))))
    (hV : ∀ p ∈ P,
      1/(D*((1/(2:ℝ)^n)^s)^2) ≤ ((V p).card:ℝ) ∧
      ((V p).card:ℝ) ≤ D/((1/(2:ℝ)^n)^s)^2 ∧
      NormalizedFiniteBallBound ((1/(2:ℝ)^n)^2) s (D^4) (V p) ∧
      ∀ l ∈ V p, |l 0| ≤ 1/2 ∧ TubeIncident ((1/(2:ℝ)^n)^2) p l)
    (hT : ∀ c ∈ C, (T c).Nonempty ∧ InBoundedLineChart (T c) ∧
      FiniteSeparatedAt (1/(2:ℝ)^(n+3)) (T c) ∧
      NormalizedFiniteBallBound (1/(2:ℝ)^(n+3)) s (D^4) (T c) ∧
      ∀ a ∈ T c, TubeIncident (1/(2:ℝ)^(n+3)) c a ∧
        ((∑ p ∈ P.filter (fun p => coarsePlanarRound (1/(2:ℝ)^(n+3)) p = c), (V p).card):ℝ) ≤
          2*(Nat.log 2 (∑ p ∈ P, (V p).card)+1:ℕ)*((T c).card:ℝ)*
            (coarsePencilWeight (P.filter (fun p => coarsePlanarRound (1/(2:ℝ)^(n+3)) p = c))
              V (fun l => roundedIncidentLine (1/(2:ℝ)^(n+3)) c (l 0)) a:ℝ))
    (hG : ∀ a ∈ C.biUnion T, (G a).Nonempty ∧ (G a).card ≤ (P.biUnion V).card)
    (hGsum : (∑ a ∈ C.biUnion T, ((G a).card:ℝ)) ≤ 13*((P.biUnion V).card:ℝ))
    (hGcap : ∀ c ∈ C, ∀ p ∈ P.filter (fun p => coarsePlanarRound (1/(2:ℝ)^(n+3)) p = c),
      ∀ l ∈ V p, l ∈ G (roundedIncidentLine (1/(2:ℝ)^(n+3)) c (l 0))) :
    Nonempty (RegularRefinementData n s t (D^40) P V) := by
  let Δ := 1/(2:ℝ)^n
  let ρ := 1/(2:ℝ)^(n+3)
  let q := coarsePlanarRound ρ
  let S := fun c => P.filter fun p => q p = c
  let Jp : ℝ := ((Nat.log 2 P.card+1:ℕ):ℝ)
  let Jv : ℝ := ((Nat.log 2 (∑ p ∈ P, (V p).card)+1:ℕ):ℝ)
  let Jc : ℝ := ((Nat.log 2 (C.biUnion T).card+1:ℕ):ℝ)
  let Jg : ℝ := ((Nat.log 2 (P.biUnion V).card+1:ℕ):ℝ)
  let L := 4*Jc*Jg
  let mF := 1/(D*(Δ^s)^2)
  let MF := D/(Δ^s)^2
  have hΔ : 0 < Δ := by dsimp [Δ]; positivity
  have hρ : 0 < ρ := by dsimp [ρ]; positivity
  have hD1 : 1 ≤ D := by linarith only [hD]
  have hD0 : 0 < D := zero_lt_one.trans_le hD1
  have hΔs : 0 < Δ^s := Real.rpow_pos_of_pos hΔ _
  have hmF : 0 < mF := by dsimp [mF]; positivity
  have hMF : 0 < MF := by dsimp [MF]; positivity
  have hJp0 : 0 ≤ Jp := by dsimp [Jp]; positivity
  have hJv0 : 0 < Jv := by dsimp [Jv]; positivity
  have hJg0 : 0 < Jg := by dsimp [Jg]; positivity
  have hJc0 : 0 < Jc := by dsimp [Jc]; positivity
  have hL0 : 0 ≤ L := by dsimp [L]; positivity
  have hJpR : Jp ≤ D := by
    simpa only [Jp,Nat.cast_add,Nat.cast_one] using hJp
  have hJvR : Jv ≤ D := by
    simpa only [Jv,Nat.cast_add,Nat.cast_one] using hJv
  have hJcR : Jc ≤ D := by
    simpa only [Jc,Nat.cast_add,Nat.cast_one] using hJc
  have hJgR : Jg ≤ D := by
    simpa only [Jg,Nat.cast_add,Nat.cast_one] using hJg
  have hL : L ≤ D^3 := by
    calc
      L ≤ 4*D*D := by dsimp [L]; gcongr
      _ ≤ D*D*D := by gcongr; linarith only [hD]
      _ = _ := by ring
  have pow40 (a : ℕ) (ha : a ≤ 40) : D^a ≤ D^40 := pow_le_pow_right₀ hD1 ha
  obtain ⟨m,hm,R,hRC,hR,hRsize,hRb,U,hU,hUT,hGsumR,j,hGband⟩ := comparable_frozen_pencils
    hρ (one_le_pow₀ hD1 (n := 4)) C T G hC hCb
    (fun c hc => ⟨(hT c hc).1,(hT c hc).2.1,(hT c hc).2.2.1,
      (hT c hc).2.2.2.1,fun l hl => ((hT c hc).2.2.2.2 l hl).1⟩) (P.biUnion V).card hG
  let E := (2*Jv)*(2*m)/(m/(2*Jg))
  let F := 2*E*MF/mF
  have hEeq : E = 8*Jv*Jg := by dsimp [E]; field_simp; ring
  have hE : E ≤ D^3 := by
    rw [hEeq]
    calc
      8*Jv*Jg ≤ 8*D*D := by gcongr
      _ ≤ D*D*D := by gcongr; linarith only [hD]
      _ = _ := by ring
  have hE0 : 0 < E := by rw [hEeq]; positivity
  have hF0 : 0 ≤ F := by dsimp [F]; positivity
  have hFeq : F = 2*E*D^2 := by dsimp [F,MF,mF]; field_simp
  have hF : F ≤ D^7 := by
    rw [hFeq]
    calc
      _ ≤ D*D^3*D^2 := by gcongr; linarith only [hD]
      _ = D^6 := by ring
      _ ≤ D^7 := pow_le_pow_right₀ hD1 (by norm_num)
  have hmassbound : 2*Jp*L*F ≤ D^40 := by
    calc
      _ ≤ D*D*D^3*D^7 := by gcongr; linarith only [hD]
      _ = D^12 := by ring
      _ ≤ _ := pow40 12 (by norm_num)
  have hregbound : D^4*F ≤ D^40 := by
    calc
      _ ≤ D^4*D^7 := mul_le_mul_of_nonneg_left hF (pow_nonneg hD0.le _)
      _ = D^11 := by ring
      _ ≤ _ := pow40 11 (by norm_num)
  have hcregbound : D^4*L ≤ D^40 := by
    calc
      _ ≤ D^4*D^3 := mul_le_mul_of_nonneg_left hL (pow_nonneg hD0.le _)
      _ = D^7 := by ring
      _ ≤ _ := pow40 7 (by norm_num)
  let W := fun p => (V p).filter fun l => roundedIncidentLine ρ (q p) (l 0) ∈ U (q p)
  obtain ⟨A,hA,hAP,hAne,hAsize,_⟩ := retained_regular_cells (sq_nonneg Δ) hΔ.le
    (one_le_pow₀ hD1 (n := 4)) hmF hMF (mul_pos (by norm_num : (0:ℝ) < 2) hJv0)
    (mul_pos (by norm_num : (0:ℝ) < 2) hm) (div_pos hm (mul_pos (by norm_num : (0:ℝ) < 2) hJg0)) hJp0 hL0
    (by positivity : 0 ≤ (2:ℝ)^k) P C R q V U
    (fun c l => roundedIncidentLine ρ c (l 0)) (fun c => localPacketPoint Δ (c 0) (c 1)) hR hRC
    hPball hmass (fun c hc => ⟨by
      have hh : 2^k ≤ (S c).card := (hcell c hc).2.1
      exact_mod_cast hh,by
      have hhN : (S c).card < 2^(k+1) := (hcell c hc).2.2.1
      have hh : ((S c).card:ℝ) < (2:ℝ)^(k+1) := by exact_mod_cast hhN
      simpa only [pow_succ,mul_comm] using hh.le⟩) hRsize
    (fun c hc => ⟨(hcell c (hRC hc)).1,localPacketPoint_injective hΔ _ _,(hcell c (hRC hc)).2.2.2.2⟩)
    (fun p hp => ⟨(hV p hp).1,(hV p hp).2.1,(hV p hp).2.2.1⟩) (fun c hc => by
      refine ⟨(hU c hc).2.2.2.2.1,?_⟩
      intro a ha
      have hh := ((hT c (hRC hc)).2.2.2.2 a ((hU c hc).2.2.1 ha)).2
      have hupper := (hU c hc).2.1
      have hweight0 : 0 ≤ (coarsePencilWeight (S c) V
        (fun l => roundedIncidentLine ρ c (l 0)) a:ℝ) := Nat.cast_nonneg _
      apply (show (∑ p ∈ S c, ((V p).card:ℝ)) ≤ _ by simpa only [Nat.cast_sum] using hh).trans
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hupper (show 0 ≤ 2*Jv by positivity)) hweight0)
  have hRchart : InBoundedLineChart R := fun c hc => hCchart c (hRC hc)
  have hmin : ∀ c ∈ R, m/(D^40) ≤ ((U c).card:ℝ) := by
    intro c hc
    apply le_trans _ (hU c hc).2.2.2.2.1
    apply div_le_div_of_nonneg_left hm.le (by positivity)
    exact (show 2*Jg ≤ D^2 by nlinarith only [hJgR,hD]).trans (pow40 2 (by norm_num))
  have hfinemin : 1/(D^40*(Δ^s)^2) ≤ mF/(2*E) := by
    have hcoef : 2*D*E ≤ D^40 := by
      calc
        _ ≤ D*D*D^3 := by gcongr; linarith only [hD]
        _ = D^5 := by ring
        _ ≤ _ := pow40 5 (by norm_num)
    calc
      _ ≤ 1/((2*D*E)*(Δ^s)^2) := div_le_div_of_nonneg_left (by norm_num) (by positivity)
        (mul_le_mul_of_nonneg_right hcoef (sq_nonneg _))
      _ = _ := by dsimp [mF]; field_simp
  refine ⟨{
    cells := R
    pencils := U
    points := A
    fine := W
    packets := G
    width := m
    level := j
    width_pos := hm
    cells_nonempty := hR
    cells_chart := hRchart
    cells_regular := ball_constant_mono hρ.le hcregbound hRb
    pencil_data := ?_
    point_data := ?_
    point_mass := ?_
    fine_data := ?_
    packet_cover := ?_
    packet_sum := hGsumR.trans hGsum
    packet_band := hGband
    coarse_cover := ?_ }⟩
  · intro c hc
    obtain ⟨_,hmax,hsub,hne,hlo,hup,hchart,hsep,hball,hinc⟩ := hU c hc
    refine ⟨hmin c hc,hup.trans ?_,hchart,hsep,ball_constant_mono hρ.le hcregbound hball,hinc⟩
    exact mul_le_mul_of_nonneg_right (show 2 ≤ D^40 from
      (show (2:ℝ) ≤ D by linarith only [hD]).trans (by simpa using pow40 1 (by norm_num))) hm.le
  · intro c hc
    refine ⟨(hA c hc).1,(hA c hc).2.1,?_,ball_constant_mono hΔ.le hregbound (hA c hc).2.2.2.1⟩
    exact fun p hp => (hcell c (hRC hc)).2.2.2.1 p ((hA c hc).1 hp)
  · exact hAsize.trans (mul_le_mul_of_nonneg_right hmassbound (Nat.cast_nonneg _))
  · intro c hc p hp
    obtain ⟨hsub,hlo,hup,hball,_⟩ := (hA c hc).2.2.2.2 p hp
    refine ⟨hsub,hfinemin.trans hlo,hup.trans ?_,ball_constant_mono (sq_nonneg Δ) hregbound hball⟩
    exact div_le_div_of_nonneg_right (by simpa using pow40 1 (by norm_num)) (sq_nonneg _)
  · intro c hc p hp l hl
    have hd := (hA c hc).2.2.2.2 p hp
    refine ⟨roundedIncidentLine ρ c (l 0),hd.2.2.2.2 l hl,?_⟩
    exact hGcap c (hRC hc) p ((hA c hc).1 hp) l (hd.1 hl)
  · have hδρ : Δ^2 ≤ ρ := by
      have he : ρ = Δ/8 := by dsimp [ρ,Δ]; rw [pow_add]; norm_num; ring
      have hd : Δ ≤ 1/8 := by
        apply one_div_le_one_div_of_le (by norm_num : (0:ℝ) < 8)
        have hh := pow_le_pow_right₀ (by norm_num : (1:ℝ) ≤ 2) hn
        norm_num at hh
        exact hh
      rw [he]
      nlinarith only [hd,hΔ]
    have hres : ∀ c ∈ R, ∀ l ∈ (A c).biUnion W, |c 1-l 0*c 0-l 1| ≤ 4*ρ := by
      intro c hc l hl
      obtain ⟨p,hp,hl⟩ := Finset.mem_biUnion.mp hl
      have hpc : q p = c := (Finset.mem_filter.mp ((hA c hc).1 hp)).2
      have hpP := (Finset.mem_filter.mp ((hA c hc).1 hp)).1
      have hVpl := (hA c hc).2.2.2.2 p hp |>.1 hl
      exact moved_point_residual (sq_nonneg Δ) hρ hδρ p c l
        (by simpa only [← hpc] using coarsePlanarRound_near hρ p)
        (((hV p hpP).2.2.2 l hVpl).1.trans (by norm_num)) ((hV p hpP).2.2.2 l hVpl).2
    have hc := retained_coarse_cover_card hρ R (fun c => (A c).biUnion W) U
      (fun c hc => (hRchart c hc).1) hres (fun c hc l hl => by
        obtain ⟨p,hp,hl⟩ := Finset.mem_biUnion.mp hl
        exact (hA c hc).2.2.2.2 p hp |>.2.2.2.2 l hl)
    simpa only [Finset.biUnion_biUnion] using hc

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Estimates_CoarseFreezingBudget
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The fixed polynomial losses in coarse pencil uniformization and
fine-packet freezing, before the common exponential absorption. -/
namespace Falconer

theorem coarse_comparable_size_bound {ρ κ s t K L m D : ℝ}
    (hρ : 0 < ρ) (hκ : 0 < κ) (_hs : 0 ≤ s) (hs1 : s ≤ 1) (hgap : κ ≤ t-s)
    (hD : 80 ≤ D) (hK : 0 ≤ K) (hKD : K ≤ D^6)
    (_hL : 0 ≤ L) (hLD : L ≤ D/(ρ^s)^2) (hH : projectionGapConstant κ ≤ D)
    (hm : m ≤ 2*L*K*(80*ρ)^s*(1+K*planarPotentialConstant s t)) :
    2*m ≤ D^20/ρ^s := by
  have hD1 : 1 ≤ D := by linarith only [hD]
  have hD0 : 0 ≤ D := zero_le_one.trans hD1
  have hρs : 0 < ρ^s := Real.rpow_pos_of_pos hρ _
  have hst : s < t := by linarith only [hκ,hgap]
  have hp := planarPotentialConstant_pos hst
  have hpD : planarPotentialConstant s t ≤ D := (planarPotentialConstant_gap hκ hs1 hgap).trans hH
  have hD7 : 1 ≤ D^7 := one_le_pow₀ hD1
  have h80 : (80:ℝ)^s ≤ 80 := by
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le
      (by norm_num : (1:ℝ) ≤ 80) hs1
  have hpot : 1+K*planarPotentialConstant s t ≤ 2*D^7 := by
    calc
      _ ≤ 1+D^6*D := by gcongr
      _ ≤ _ := by nlinarith only [hD7]
  have h640 : 640 ≤ D^6 := by
    have hh := pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 80) hD 6
    norm_num at hh
    linarith only [hh]
  calc
    2*m ≤ 2*(2*L*K*(80*ρ)^s*(1+K*planarPotentialConstant s t)) := mul_le_mul_of_nonneg_left hm (by norm_num)
    _ = 4*L*K*((80:ℝ)^s*ρ^s)*(1+K*planarPotentialConstant s t) := by
      rw [Real.mul_rpow (by norm_num : (0:ℝ) ≤ 80) hρ.le]
      ring
    _ ≤ 4*(D/(ρ^s)^2)*D^6*(80*ρ^s)*(2*D^7) := by gcongr
    _ = 640*D^14/ρ^s := by field_simp; ring
    _ ≤ _ := by
      apply div_le_div_of_nonneg_right _ hρs.le
      calc
        _ ≤ D^6*D^14 := mul_le_mul_of_nonneg_right h640 (pow_nonneg hD0 _)
        _ = _ := by ring

theorem coarse_weight_scale_bound {Δ s B D : ℝ}
    (hΔ : 0 < Δ) (hs1 : s ≤ 1) (hD : 80 ≤ D)
    (hB : B ≤ D^20/(Δ/8)^s) : B ≤ D^21/Δ^s := by
  have hD0 : 0 ≤ D := by linarith only [hD]
  have hΔs : 0 < Δ^s := Real.rpow_pos_of_pos hΔ _
  have h8 : (8:ℝ)^s ≤ D := by
    have hh : (8:ℝ)^s ≤ 8 := by
      simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le (by norm_num : (1:ℝ) ≤ 8) hs1
    exact hh.trans (by linarith only [hD])
  calc
    B ≤ D^20/(Δ/8)^s := hB
    _ = D^20*(8:ℝ)^s/Δ^s := by
      rw [Real.div_rpow hΔ.le (by norm_num : (0:ℝ) ≤ 8),div_div_eq_mul_div]
    _ ≤ D^20*D/Δ^s := div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_left h8 (pow_nonneg hD0 _)) hΔs.le
    _ = _ := by ring

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Estimates_CommonTubePacking
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Separation supplies a second common-tube bound, independent of the
pencil cardinality. Interpolating it with regularity detects large pencils. -/
namespace Falconer
attribute [local instance] Classical.propDecidable

theorem common_tube_packing_bound {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (T : Finset (Space 2)) (x y : Space 2) (hx0 : |x 0| ≤ 1)
    (hchart : InBoundedLineChart T) (hsep : FiniteSeparatedAt δ T)
    (hinc : ∀ l ∈ T, TubeIncident δ x l) :
    ((T.filter (fun l => TubeIncident δ y l)).card:ℝ) ≤
      (25921:ℝ)*(1/truncatedPlanarDistance δ x y)^2 := by
  let r := truncatedPlanarDistance δ x y
  obtain ⟨hr,hr1⟩ := truncatedPlanarDistance_bounds hδ hδ1 x y
  change 0 < r at hr
  change r ≤ 1 at hr1
  let S := T.filter fun l => TubeIncident δ y l
  by_cases hsmall : 16*δ ≤ r
  · have hrδ : δ < r := by linarith only [hδ,hsmall]
    have hxy : r ≤ dist x y := by
      have hh : δ < min 1 (dist x y) := (lt_max_iff.mp hrδ).resolve_left (lt_irrefl _)
      exact (max_eq_right hh.le).trans_le (min_le_right _ _)
    by_cases hS : S.Nonempty
    · obtain ⟨m,hm⟩ := hS
      have hmT := (Finset.mem_filter.mp hm).1
      have hmy := (Finset.mem_filter.mp hm).2
      have hball : ∀ l ∈ S, dist l m ≤ 80*δ/r := by
        intro l hl
        obtain ⟨hlT,hly⟩ := Finset.mem_filter.mp hl
        exact two_point_tube_parameters_close hδ.le hr hr1 hsmall hx0
          (hchart l hlT).1 (hchart m hmT).1 (hinc l hlT) hly (hinc m hmT) hmy hxy
      have hb := separated_ball_card S m hδ (by positivity : 0 ≤ 80*δ/r)
        (finiteSeparatedAt_subset (Finset.filter_subset _ _) hsep) hball
      have he : 2*(80*δ/r)/δ+1 = (160+r)/r := by field_simp; ring
      rw [he] at hb
      calc
        _ ≤ ((160+r)/r)^2 := hb
        _ ≤ (161/r)^2 := by gcongr; linarith only [hr1]
        _ = _ := by change (161/r)^2 = 25921*(1/r)^2; ring
    · change (S.card:ℝ) ≤ _
      rw [show S = ∅ from Finset.not_nonempty_iff_eq_empty.mp hS]
      simp only [Finset.card_empty,Nat.cast_zero]
      positivity
  · have hball : ∀ l ∈ T, dist l 0 ≤ 2 := by
      intro l hl
      have hh := planar_dist_le_coordinate_sum l 0
      simp only [PiLp.zero_apply,sub_zero] at hh
      linarith only [hh,(hchart l hl).1,(hchart l hl).2]
    have hb := separated_ball_card T 0 hδ (by norm_num : (0:ℝ) ≤ 2) hsep hball
    have hratio : 4/δ+1 ≤ 80/r := by
      apply (le_div_iff₀ hr).2
      have hrδ : r ≤ 16*δ := (lt_of_not_ge hsmall).le
      have hrd : r/δ ≤ 16 := (div_le_iff₀ hδ).2 hrδ
      calc
        (4/δ+1)*r = 4*(r/δ)+r := by ring
        _ ≤ 4*16+1 := by gcongr
        _ ≤ 80 := by norm_num
    calc
      _ ≤ (T.card:ℝ) := Nat.cast_le.mpr (Finset.card_filter_le _ _)
      _ ≤ (4/δ+1)^2 := by norm_num only [show (2:ℝ)*2 = 4 by norm_num] at hb; exact hb
      _ ≤ (80/r)^2 := by gcongr
      _ ≤ (161/r)^2 := by gcongr; norm_num
      _ = _ := by change (161/r)^2 = 25921*(1/r)^2; ring

theorem intersect_tube_packing_bound {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (T U : Finset (Space 2)) (x y : Space 2) (hx0 : |x 0| ≤ 1)
    (hchart : InBoundedLineChart T) (hsep : FiniteSeparatedAt δ T)
    (hx : ∀ l ∈ T, TubeIncident δ x l) (hy : ∀ l ∈ U, TubeIncident δ y l) :
    ((T ∩ U).card:ℝ) ≤ (25921:ℝ)*(1/truncatedPlanarDistance δ x y)^2 := by
  have hsub : T ∩ U ⊆ T.filter (fun l => TubeIncident δ y l) := by
    intro l hl
    exact Finset.mem_filter.mpr ⟨(Finset.mem_inter.mp hl).1,hy l (Finset.mem_inter.mp hl).2⟩
  exact (Nat.cast_le.mpr (Finset.card_le_card hsub)).trans
    (common_tube_packing_bound hδ hδ1 T x y hx0 hchart hsep hx)

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Estimates_RegularCoarsePreparation
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Construct the regular coarse cells, their pencils and their original
fine packets from the two covering assumptions in the regular-set alternative. -/
namespace Falconer
open scoped BigOperators
attribute [local instance] Classical.propDecidable

theorem regular_coarse_preparation (n : ℕ) {s t K D : ℝ}
    (hn : 3 ≤ n) (hs : 0 ≤ s) (hs1 : s ≤ 1) (ht : 0 ≤ t) (ht1 : t ≤ 2)
    (hK : 1 ≤ K) (hKD : K ≤ D) (hD : 80 ≤ D) (h13 : 13*K ≤ D)
    (P : Finset (Space 2)) (V : Space 2 → Finset (Space 2)) (hP : P.Nonempty)
    (hPchart : ∀ p ∈ P, |p 0| ≤ 1/8 ∧ |p 1| ≤ 1/8)
    (hPball : NormalizedFiniteBallBound ((1/(2:ℝ)^n)^2) t K P)
    (hV : ∀ p ∈ P, (V p).Nonempty ∧
      NormalizedFiniteBallBound ((1/(2:ℝ)^n)^2) s K (V p) ∧
      ∀ l ∈ V p, |l 0| ≤ 1/2 ∧ TubeIncident ((1/(2:ℝ)^n)^2) p l)
    (hJp : (Nat.log 2 P.card+1:ℕ) ≤ D)
    (hJv : (Nat.log 2 (∑ p ∈ P, (V p).card)+1:ℕ) ≤ D)
    (hpoint : ((P.image (coarsePlanarRound (1/(2:ℝ)^(n+3)))).card:ℝ) ≤ K/(1/(2:ℝ)^n)^t)
    (hline : (((P.biUnion V).image (coarsePlanarRound (1/(2:ℝ)^(n+3)))).card:ℝ) ≤
      K/((1/(2:ℝ)^(n+3))^s)^2)
    (hsize : ((P.biUnion V).card:ℝ) ≤ K/((1/(2:ℝ)^n)^s)^4) :
    let Δ := 1/(2:ℝ)^n
    let ρ := 1/(2:ℝ)^(n+3)
    let S := fun c => P.filter fun p => coarsePlanarRound ρ p = c
    let J := Nat.log 2 (∑ p ∈ P, (V p).card)+1
    ∃ C ⊆ P.image (coarsePlanarRound ρ), C.Nonempty ∧ InBoundedLineChart C ∧
      FiniteSeparatedAt ρ C ∧ NormalizedFiniteBallBound ρ t (D^5) C ∧
      (∀ c ∈ C, (S c).Nonempty ∧
        (∀ p ∈ S c, |p 0-c 0| ≤ Δ ∧ |p 1-c 1| ≤ Δ) ∧
        NormalizedFiniteBallBound Δ t (D^5) ((S c).image (localPacketPoint Δ (c 0) (c 1)))) ∧
      ∃ T : Space 2 → Finset (Space 2),
        (∀ c ∈ C, (T c).Nonempty ∧ InBoundedLineChart (T c) ∧ FiniteSeparatedAt ρ (T c) ∧
          NormalizedFiniteBallBound ρ s (D^5) (T c) ∧
          ∀ a ∈ T c, TubeIncident ρ c a ∧
            ((∑ p ∈ S c, (V p).card):ℝ) ≤ 2*(J:ℝ)*((T c).card:ℝ)*
              (coarsePencilWeight (S c) V (fun l => roundedIncidentLine ρ c (l 0)) a:ℝ)) ∧
        ((C.biUnion T).card:ℝ) ≤ D/(ρ^s)^2 ∧
        ((C.biUnion T).card:ℝ) ≤ 13*((P.biUnion V).card:ℝ) ∧
        let G := fineCoarsePacket ρ C (fun c => (S c).biUnion V)
        (∀ a ∈ C.biUnion T, (G a).Nonempty ∧ (G a).card ≤ (P.biUnion V).card) ∧
        (∑ a ∈ C.biUnion T, ((G a).card:ℝ)) ≤ D/(Δ^s)^4 ∧
        (∀ c ∈ C, ∀ p ∈ S c, ∀ l ∈ V p, l ∈ G (roundedIncidentLine ρ c (l 0))) ∧
        (∀ c ∈ C, ∀ p ∈ S c, ∀ l ∈ V p, dist l (roundedIncidentLine ρ c (l 0)) ≤ Δ) := by
  let Δ := 1/(2:ℝ)^n
  let ρ := 1/(2:ℝ)^(n+3)
  let q := coarsePlanarRound ρ
  let S := fun c => P.filter fun p => q p = c
  let Jp := Nat.log 2 P.card+1
  let J := Nat.log 2 (∑ p ∈ P, (V p).card)+1
  have hΔ : 0 < Δ := by dsimp [Δ]; positivity
  have hρ : 0 < ρ := by dsimp [ρ]; positivity
  have hscale : ρ = Δ/8 := by dsimp [ρ,Δ]; rw [pow_add]; norm_num; ring
  have hΔ8 : Δ ≤ 1/8 := by
    apply one_div_le_one_div_of_le (by norm_num : (0:ℝ) < 8)
    have hh := pow_le_pow_right₀ (by norm_num : (1:ℝ) ≤ 2) hn
    norm_num at hh
    exact hh
  have hΔ1 : Δ ≤ 1 := hΔ8.trans (by norm_num)
  have hρΔ : ρ ≤ Δ := by rw [hscale]; linarith only [hΔ]
  have hρ8 : ρ ≤ 1/8 := hρΔ.trans hΔ8
  have hδρ : Δ^2 ≤ ρ := by rw [hscale]; nlinarith only [hΔ8,hΔ]
  have hnear : ∀ p ∈ P, dist p (q p) ≤ ρ := fun p _ => coarsePlanarRound_near hρ p
  have hD1 : 1 ≤ D := by linarith only [hD]
  have hD0 : 0 ≤ D := zero_le_one.trans hD1
  have hD35 : D^3 ≤ D^5 := pow_le_pow_right₀ hD1 (by norm_num)
  have hD45 : D^4 ≤ D^5 := pow_le_pow_right₀ hD1 (by norm_num)
  have hquad (a : ℝ) (ha : a ≤ D) : a*D^2 ≤ D^3 := by
    calc
      _ ≤ D*D^2 := mul_le_mul_of_nonneg_right ha (sq_nonneg _)
      _ = _ := by ring
  have hcube : 2*D^3 ≤ D^5 := by
    calc
      _ ≤ D*D^3 := mul_le_mul_of_nonneg_right (by linarith only [hD]) (pow_nonneg hD0 _)
      _ = D^4 := by ring
      _ ≤ _ := hD45
  have hcp : 8*K*(Jp:ℝ) ≤ D^5 := by
    calc
      _ ≤ 8*D*D := by gcongr
      _ = 8*D^2 := by ring
      _ ≤ D^3 := hquad 8 (by linarith only [hD])
      _ ≤ _ := hD35
  have hcl : 2*K*(Jp:ℝ)*K ≤ D^5 := by
    calc
      _ ≤ 2*D*D*D := by gcongr
      _ = 2*D^3 := by ring
      _ ≤ _ := hcube
  have h7 : (7:ℝ)^s ≤ 7 := by
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le (by norm_num : (1:ℝ) ≤ 7) hs1
  have hct : 2*(K*(7:ℝ)^s)*(J:ℝ) ≤ D^5 := by
    calc
      _ ≤ 2*(D*7)*D := by gcongr
      _ = 14*D^2 := by ring
      _ ≤ D^3 := hquad 14 (by linarith only [hD])
      _ ≤ _ := hD35
  have hqchart : ∀ c ∈ P.image q, |c 0| ≤ 1/4 ∧ |c 1| ≤ 1/4 := by
    intro c hc
    obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp hc
    have bound (i : Fin 2) (hi : |p i| ≤ 1/8) : |q p i| ≤ 1/4 := by
      have hd : |q p i-p i| ≤ ρ := (show |q p i-p i| ≤ dist (q p) p by
        simpa only [Real.dist_eq] using PiLp.dist_apply_le (q p) p i).trans
          (by simpa only [dist_comm] using hnear p hp)
      calc
        _ = |(q p i-p i)+p i| := by congr 1; ring
        _ ≤ |q p i-p i|+|p i| := abs_add_le _ _
        _ ≤ 1/4 := by linarith only [hd,hi,hρ8]
    exact ⟨bound 0 (hPchart p hp).1,bound 1 (hPchart p hp).2⟩
  obtain ⟨_,C,hCsub,hC,hCball,_,hcell⟩ := heavy_regular_packet_cells hΔ hΔ1 hρ hδρ hρΔ
    ht ht1 hK (zero_le_one.trans hK) P hP q hnear hPball hpoint
  have hCchart : InBoundedLineChart C := fun c hc =>
    ⟨((hqchart c (hCsub hc)).1.trans (by norm_num)),((hqchart c (hCsub hc)).2.trans (by norm_num))⟩
  have hCsep := finiteSeparatedAt_subset hCsub (coarsePlanarRound_separated hρ P)
  obtain ⟨T,hT⟩ := coarse_cell_pencils (sq_nonneg Δ) hρ (hρ8.trans (by norm_num)) hδρ hs hK P C V q
    hCsub hnear (fun c hc => hqchart c (hCsub hc)) hV
  obtain ⟨hGne,hGsub,hGmem,hGsum,hTsum⟩ := original_coarse_packets (sq_nonneg Δ) hρ hδρ P C V T q
    hnear (fun c hc => (hCchart c hc).1)
    (fun p hp l hl => ⟨((hV p hp).2.2 l hl).1.trans (by norm_num),(hV p hp).2.2 l hl |>.2⟩)
    (fun c hc => (hT c hc).1)
  refine ⟨C,hCsub,hC,hCchart,hCsep,?_,?_,T,?_,?_,?_,?_,?_,?_,?_⟩
  · intro z r hr hr1
    exact (hCball z r hr hr1).trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hcp (Real.rpow_nonneg (hρ.le.trans hr) _)) (Nat.cast_nonneg _))
  · intro c hc
    obtain ⟨_,hne,_,_,hrect,hball⟩ := hcell c hc
    refine ⟨hne,hrect,?_⟩
    intro z r hr hr1
    exact (hball z r hr hr1).trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hcl (Real.rpow_nonneg (hΔ.le.trans hr) _)) (Nat.cast_nonneg _))
  · intro c hc
    obtain ⟨_,hne,hchart,hsep,hball,hinc,_⟩ := hT c hc
    refine ⟨hne,hchart,hsep,?_,hinc⟩
    intro z r hr hr1
    exact (hball z r hr hr1).trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hct (Real.rpow_nonneg (hρ.le.trans hr) _)) (Nat.cast_nonneg _))
  · calc
      _ ≤ 13*(((P.biUnion V).image (coarsePlanarRound ρ)).card:ℝ) := hTsum
      _ ≤ 13*(K/(ρ^s)^2) := mul_le_mul_of_nonneg_left hline (by norm_num)
      _ ≤ _ := by rw [← mul_div_assoc]; exact div_le_div_of_nonneg_right h13 (sq_nonneg _)
  · exact hTsum.trans (mul_le_mul_of_nonneg_left
      (by exact_mod_cast Finset.card_image_le : (((P.biUnion V).image (coarsePlanarRound ρ)).card:ℝ) ≤ (P.biUnion V).card)
      (by norm_num))
  · exact fun a ha => ⟨hGne a ha,Finset.card_le_card (hGsub a)⟩
  · calc
      _ ≤ 13*((P.biUnion V).card:ℝ) := hGsum
      _ ≤ 13*(K/(Δ^s)^4) := mul_le_mul_of_nonneg_left hsize (by norm_num)
      _ ≤ _ := by rw [← mul_div_assoc]; exact div_le_div_of_nonneg_right h13 (pow_nonneg (Real.rpow_nonneg hΔ.le s) _)
  · exact fun c hc p hp l hl => hGmem c hc p (Finset.mem_filter.mp hp).1 (Finset.mem_filter.mp hp).2 l hl
  · intro c hc p hp l hl
    have hh := (hT c hc).2.2.2.2.2.2 p hp l hl
    exact hh.trans (by rw [hscale]; linarith only [hΔ])

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

theorem packet_incidence_log {a b : ℕ} (P : Finset (Space 2))
    (T : Space 2 → Finset (Space 2)) (hP : P.card ≤ 2^a)
    (hT : (P.biUnion T).card ≤ 2^b) :
    Nat.log 2 (∑ p ∈ P, (T p).card)+1 ≤ a+b+1 := by
  apply packet_log_of_card_bound
  calc
    _ ≤ ∑ _p ∈ P, 2^b := Finset.sum_le_sum fun p hp =>
      (Finset.card_le_card (Finset.subset_biUnion_of_mem T hp)).trans hT
    _ = P.card*2^b := by simp
    _ ≤ 2^a*2^b := Nat.mul_le_mul_right _ hP
    _ = _ := (pow_add _ _ _).symm

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Estimates_SampledRowCardinality
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Convert the sampler's exact cardinality bounds to the dyadic lower
and upper powers used by the regular product theorem. -/
namespace Falconer

theorem half_power_rpow_exp (N : ℕ) (s : ℝ) :
    ((1/2:ℝ)^N)^s = Real.exp (-s*(N:ℝ)*Real.log 2) := by
  rw [Real.rpow_def_of_pos (by positivity),Real.log_pow,
    Real.log_div (by norm_num) (by norm_num),Real.log_one]
  congr 1
  ring

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Estimates_SmallUnionLogs
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A putative small fine-tube union bounds all its incidence-selection
logarithms linearly in the original dyadic depth. -/
namespace Falconer
open scoped BigOperators
attribute [local instance] Classical.propDecidable

theorem small_union_card_dyadic (n : ℕ) {ε s : ℝ} (hε : ε ≤ 1) (hs : s ≤ 1)
    (m : ℕ) (hm : (m:ℝ) ≤ Real.exp (ε*((n+2:ℕ):ℝ)*Real.log 2)/((1/(2:ℝ)^n)^s)^4) :
    m ≤ 2^(5*n+2) := by
  have hpow : (1/(2:ℝ)^n)^s = Real.exp (-s*(n:ℝ)*Real.log 2) := by
    simpa only [div_pow,one_pow] using half_power_rpow_exp n s
  have hbound : Real.exp (ε*((n+2:ℕ):ℝ)*Real.log 2)/((1/(2:ℝ)^n)^s)^4 ≤
      (2:ℝ)^(5*n+2) := by
    rw [hpow,← Real.exp_nat_mul,← Real.exp_sub]
    have heq : (2:ℝ)^(5*n+2) = Real.exp (((5*n+2:ℕ):ℝ)*Real.log 2) := by
      rw [Real.exp_nat_mul,Real.exp_log (by norm_num : (0:ℝ) < 2)]
    rw [heq]
    apply Real.exp_le_exp.mpr
    have he := mul_le_mul_of_nonneg_right hε (show 0 ≤ ((n+2:ℕ):ℝ) by positivity)
    have hs' := mul_le_mul_of_nonneg_right hs (Nat.cast_nonneg (α := ℝ) n)
    have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
    push_cast at he ⊢
    nlinarith only [mul_le_mul_of_nonneg_right he hlog.le,mul_le_mul_of_nonneg_right hs' hlog.le]
  exact_mod_cast hm.trans hbound

theorem small_union_selection_logs (n : ℕ) {ε s : ℝ} (hε : ε ≤ 1) (hs : s ≤ 1)
    (P : Finset (Space 2)) (T : Space 2 → Finset (Space 2))
    (hP : InBoundedLineChart P) (hsep : FiniteSeparatedAt ((1/(2:ℝ)^n)^2) P)
    (hsmall : ((P.biUnion T).card:ℝ) ≤
      Real.exp (ε*((n+2:ℕ):ℝ)*Real.log 2)/((1/(2:ℝ)^n)^s)^4) :
    Nat.log 2 P.card+1 ≤ 4*n+6 ∧
    Nat.log 2 (P.biUnion T).card+1 ≤ 5*n+3 ∧
    Nat.log 2 (∑ p ∈ P, (T p).card)+1 ≤ 9*n+8 := by
  have hscale : (1/(2:ℝ)^n)^2 = 1/(2:ℝ)^(2*n) := by
    rw [div_pow,one_pow,show 2*n = n*2 by omega,pow_mul]
  have hp := bounded_planar_card_dyadic (2*n) P hP (hscale ▸ hsep)
  have hu := small_union_card_dyadic n hε hs (P.biUnion T).card hsmall
  refine ⟨?_,?_,?_⟩
  · convert packet_log_of_card_bound hp using 1
    all_goals try with_reducible_and_instances rfl
    omega
  · simpa only [Nat.add_assoc] using packet_log_of_card_bound hu
  · convert packet_incidence_log P T hp hu using 1
    all_goals try with_reducible_and_instances rfl
    omega

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Geometry_ProjectionPowerBudget
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The explicit quadratic depth loss in projection sampling fits into
any prescribed positive dyadic power, uniformly over a fixed exponent gap. -/
namespace Falconer

theorem dyadic_quadratic_loss {η C : ℝ} (hη : 0 < η) (hC : 0 ≤ C) :
    ∃ N0 : ℕ, 0 < N0 ∧ ∀ N : ℕ, N0 ≤ N →
      C*((N:ℝ)+1)^2 ≤ Real.exp (η*(N:ℝ)*Real.log 2) := by
  let a := η*Real.log 2
  have ha : 0 < a := mul_pos hη (Real.log_pos (by norm_num))
  obtain ⟨N0,hN0⟩ := exists_nat_gt (max 1 (24*C/a^3))
  have hN01 : (1:ℝ) ≤ N0 := (le_max_left _ _).trans hN0.le
  refine ⟨N0,by exact_mod_cast (lt_of_lt_of_le zero_lt_one hN01),?_⟩
  intro N hN
  have hNN : (N0:ℝ) ≤ N := Nat.cast_le.mpr hN
  have hN1 : (1:ℝ) ≤ N := hN01.trans hNN
  have hscale : 24*C ≤ a^3*(N:ℝ) := by
    have hh := (le_max_right _ _).trans (hN0.le.trans hNN)
    have he := (div_le_iff₀ (pow_pos ha 3)).1 hh
    nlinarith only [he]
  have hsize : ((N:ℝ)+1)^2 ≤ (2*(N:ℝ))^2 := by
    exact pow_le_pow_left₀ (by positivity) (by linarith only [hN1]) 2
  have hcub := mul_le_mul_of_nonneg_right hscale (sq_nonneg (N:ℝ))
  calc
    _ ≤ C*(2*(N:ℝ))^2 := mul_le_mul_of_nonneg_left hsize hC
    _ ≤ (a*(N:ℝ))^3/6 := by nlinarith only [hcub]
    _ ≤ Real.exp (a*(N:ℝ)) := by
      simpa only [Nat.factorial_succ,Nat.factorial_zero,Nat.reduceAdd,Nat.reduceMul,
        Nat.cast_ofNat] using Real.pow_div_factorial_le_exp (a*(N:ℝ))
          (by positivity : 0 ≤ a*(N:ℝ)) 3
    _ = _ := by congr 1; dsimp [a]; ring

end Falconer

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

 theorem planarQuarter_right_inverse (z : Space 2) : planarQuarter ((4:ℝ) • z) = z := by
  ext i
  rw [planarQuarter_apply]
  change 4 * z i / 4 = z i
  ring

 theorem planarQuarter_separated {δ : ℝ} (G : Finset (Space 2))
    (hsep : FiniteSeparatedAt δ G) :
    FiniteSeparatedAt (δ/4) (G.image planarQuarter) := by
  intro p hp q hq hpq
  obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hp
  obtain ⟨y,hy,rfl⟩ := Finset.mem_image.mp hq
  rw [planarQuarter_dist]
  exact div_le_div_of_nonneg_right (hsep x hx y hy (fun h => hpq (congrArg _ h))) (by norm_num)

 theorem planarQuarter_regular {δ t K : ℝ} (hδ : 0 < δ) (ht : 0 ≤ t) (hK : 1 ≤ K)
    (G : Finset (Space 2)) (hreg : NormalizedFiniteBallBound δ t K G) :
    NormalizedFiniteBallBound (δ/4) t (K*4^t) (G.image planarQuarter) := by
  classical
  intro z r hr _
  have hr0 : 0 < r := (by linarith : 0 < δ/4).trans_le hr
  have hsub : (G.image planarQuarter).filter (fun p => dist p z ≤ r) ⊆
      (G.filter (fun p => dist p ((4:ℝ) • z) ≤ 4*r)).image planarQuarter := by
    intro p hp
    obtain ⟨hp,hpr⟩ := Finset.mem_filter.mp hp
    obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hp
    refine Finset.mem_image.mpr ⟨x,Finset.mem_filter.mpr ⟨hx,?_⟩,rfl⟩
    have hh := planarQuarter_dist x ((4:ℝ) • z)
    rw [planarQuarter_right_inverse] at hh
    linarith
  have hc : (((G.image planarQuarter).filter (fun p => dist p z ≤ r)).card:ℝ) ≤
      ((G.filter (fun p => dist p ((4:ℝ) • z) ≤ 4*r)).card:ℝ) := by
    exact_mod_cast (Finset.card_le_card hsub).trans Finset.card_image_le
  have hb := normalized_ball_bound_all_radii ht hK hreg ((4:ℝ) • z) (4*r) (by linarith)
  rw [Real.mul_rpow (by norm_num : (0:ℝ) ≤ 4) hr0.le] at hb
  rw [Finset.card_image_of_injective _ planarQuarter_injective]
  exact hc.trans (by nlinarith)

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Incidence_UniformSmallCoverPencils
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A small total cover forces comparable pencils to have the critical
cardinality. The point restriction and all geometric properties are retained. -/
namespace Falconer
attribute [local instance] Classical.propDecidable

theorem uniform_small_cover_pencils (N : ℕ) {s t K L : ℝ}
    (hs : 0 ≤ s) (hst : s < t) (hK : 1 ≤ K) (hL : 0 ≤ L)
    (P : Finset (Space 2)) (T : Space 2 → Finset (Space 2)) (hP : P.Nonempty)
    (hPchart : InBoundedLineChart P)
    (hPball : NormalizedFiniteBallBound (1/(2:ℝ)^N) t K P)
    (hT : ∀ x ∈ P, (T x).Nonempty ∧ InBoundedLineChart (T x) ∧
      NormalizedFiniteBallBound (1/(2:ℝ)^N) s K (T x) ∧
      ∀ l ∈ T x, TubeIncident (1/(2:ℝ)^N) x l)
    (hunion : ((P.biUnion T).card:ℝ) ≤ L) :
    let J := Nat.log 2 (P.biUnion T).card+1
    ∃ k : ℕ, ∃ R ⊆ P, R.Nonempty ∧ (P.card:ℝ) ≤ (J:ℝ)*(R.card:ℝ) ∧
      NormalizedFiniteBallBound (1/(2:ℝ)^N) t (K*(J:ℝ)) R ∧
      1/(2*K*(1/(2:ℝ)^N)^s) ≤ (2:ℝ)^k ∧
      (2:ℝ)^k ≤ 2*L*(K*(J:ℝ))*(80*(1/(2:ℝ)^N))^s*
        (1+(K*(J:ℝ))*planarPotentialConstant s t) ∧
      ∀ x ∈ R, (2:ℝ)^k ≤ ((T x).card:ℝ) ∧ ((T x).card:ℝ) ≤ 2*(2:ℝ)^k := by
  let J := Nat.log 2 (P.biUnion T).card+1
  have hδ : 0 < 1/(2:ℝ)^N := by positivity
  have hδ1 : 1/(2:ℝ)^N ≤ 1 := (div_le_one (by positivity)).2 (one_le_pow₀ (by norm_num))
  have hK0 : 0 ≤ K := zero_le_one.trans hK
  have hJ : (1:ℝ) ≤ J := by dsimp [J]; exact_mod_cast Nat.succ_le_succ (Nat.zero_le _)
  have hKJ : 1 ≤ K*(J:ℝ) := hK.trans (le_mul_of_one_le_right hK0 hJ)
  obtain ⟨k,R,hRP,hR,hsize,hRball,hband⟩ := uniform_pencil_size_band hδ.le hK0 P T hP hPball
    (fun x hx => (hT x hx).1)
  have hTball (x : Space 2) (hx : x ∈ R) :
      NormalizedFiniteBallBound (1/(2:ℝ)^N) s (K*(J:ℝ)) (T x) := by
    intro z r hr hr1
    have hr0 : 0 ≤ r := hδ.le.trans hr
    have hk : K ≤ K*(J:ℝ) := le_mul_of_one_le_right hK0 hJ
    exact ((hT x (hRP hx)).2.2.1 z r hr hr1).trans
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hk (Real.rpow_nonneg hr0 _)) (Nat.cast_nonneg _))
  have hlarge := comparable_pencil_size_upper N hs hst hKJ (by positivity : 0 < (2:ℝ)^k) hL
    R T hR (fun x hx => hPchart x (hRP hx)) hRball (by
      intro x hx
      exact ⟨(hband x hx).1,(hband x hx).2,(hT x (hRP hx)).2.1,hTball x hx,(hT x (hRP hx)).2.2.2⟩)
    ((Nat.cast_le.mpr (Finset.card_le_card (Finset.biUnion_subset_biUnion_of_subset_left T hRP))).trans hunion)
  refine ⟨k,R,hRP,hR,hsize,hRball,?_,hlarge,hband⟩
  obtain ⟨x,hx⟩ := hR
  have hlow := finite_ball_bound_card_lower hδ hδ1 (hT x (hRP hx)).1 (hT x (hRP hx)).2.2.1
  have hh := mul_le_mul_of_nonneg_left (hband x hx).2 (show 0 ≤ K*(1/(2:ℝ)^N)^s by positivity)
  apply (div_le_iff₀ (by positivity : 0 < 2*K*(1/(2:ℝ)^N)^s)).2
  nlinarith only [hlow,hh]

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Recursion_RegularPacketScaleBudget
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Reserve one fixed weak power for all regular-packet preparation losses:
the logarithmic selections, fixed grid constants and the exponent gap. -/
namespace Falconer

theorem regular_packet_scale_budget {κ θ : ℝ} (hκ : 0 < κ) (hθ : 0 < θ) :
    ∃ ε : ℝ, ∃ N0 : ℕ, 0 < ε ∧ ε ≤ 1 ∧ 0 < N0 ∧ ∀ n : ℕ, N0 ≤ n+2 →
      let N := n+2
      let K := Real.exp (ε*(N:ℝ)*Real.log 2)
      let D := K^2
      3 ≤ n ∧ 80 ≤ D ∧ projectionGapConstant κ ≤ D ∧
        13*K ≤ D ∧ 8*K ≤ D ∧ 10*(N:ℝ) ≤ D ∧
        D^40 ≤ Real.exp (θ*(N:ℝ)*Real.log 2) := by
  let ε := min (θ/80) 1
  let C := 80+projectionGapConstant κ
  have hε : 0 < ε := lt_min (by positivity) zero_lt_one
  have hH := projectionGapConstant_pos hκ
  have hC : 0 ≤ C := by dsimp [C]; positivity
  obtain ⟨N1,hN1,hpoly⟩ := dyadic_quadratic_loss hε hC
  refine ⟨ε,max N1 5,hε,min_le_right _ _,by omega,?_⟩
  intro n hn
  dsimp only
  let N := n+2
  let K := Real.exp (ε*(N:ℝ)*Real.log 2)
  have hN : 0 ≤ (N:ℝ) := Nat.cast_nonneg _
  have hpoly' : C*((N:ℝ)+1)^2 ≤ K := hpoly N ((le_max_left _ _).trans hn)
  have hpoly1 : (1:ℝ) ≤ ((N:ℝ)+1)^2 := one_le_pow₀ (by linarith only [hN])
  have hCK : C ≤ K := (le_mul_of_one_le_right hC hpoly1).trans hpoly'
  have hK80 : 80 ≤ K := (show 80 ≤ C by dsimp [C]; linarith only [hH]).trans hCK
  have hK1 : 1 ≤ K := by linarith only [hK80]
  have hK0 : 0 ≤ K := zero_le_one.trans hK1
  have hKD : K ≤ K^2 := by nlinarith only [mul_le_mul_of_nonneg_left hK1 hK0]
  have h80poly : 80*((N:ℝ)+1)^2 ≤ K :=
    (mul_le_mul_of_nonneg_right (show 80 ≤ C by dsimp [C]; linarith only [hH]) (sq_nonneg _)).trans hpoly'
  have h13 : 13*K ≤ K^2 := by nlinarith only [mul_le_mul_of_nonneg_right hK80 hK0]
  have h8 : 8*K ≤ K^2 := by nlinarith only [mul_le_mul_of_nonneg_right hK80 hK0]
  refine ⟨by omega,hK80.trans hKD,?_,h13,h8,?_,?_⟩
  · exact (show projectionGapConstant κ ≤ C by dsimp [C]; linarith).trans (hCK.trans hKD)
  · have hh : 10*(N:ℝ) ≤ K := by nlinarith only [h80poly,hN,sq_nonneg (N:ℝ)]
    exact hh.trans hKD
  · change (K^2)^40 ≤ _
    rw [← pow_mul]
    change (Real.exp (ε*(N:ℝ)*Real.log 2))^(2*40) ≤ _
    rw [← Real.exp_nat_mul]
    apply Real.exp_le_exp.mpr
    have he : 80*ε ≤ θ := by
      have hh := min_le_left (θ/80) (1:ℝ)
      dsimp [ε]
      linarith only [hh]
    have hh := mul_le_mul_of_nonneg_right he (mul_nonneg hN (Real.log_nonneg (by norm_num : (1:ℝ) ≤ 2)))
    convert hh using 1 <;> first | (with_reducible_and_instances rfl) | (dsimp [N] <;> push_cast <;> ring)

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Estimates_RegularSetAlternative
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The regular-set alternative at adjacent square-root scales. All coarse
cells, pencils and frozen packets in the contradiction are constructed from
the original finite point and tube configuration. -/
namespace Falconer
open scoped BigOperators
attribute [local instance] Classical.propDecidable

theorem regular_coarse_cover_alternative {κ : ℝ} (hκ : 0 < κ) (hκ1 : κ ≤ 1) :
    ∃ ε : ℝ, ∃ N0 : ℕ, 0 < ε ∧ ε ≤ 1 ∧ 0 < N0 ∧ ∀ n : ℕ, N0 ≤ n+2 →
      let Δ := 1/(2:ℝ)^n
      let ρ := 1/(2:ℝ)^(n+3)
      let K := Real.exp (ε*((n+2:ℕ):ℝ)*Real.log 2)
      ∀ s t : ℝ, κ ≤ s → s ≤ 1-8*κ → 2*κ ≤ t-s → t ≤ 2 →
      ∀ P : Finset (Space 2), P.Nonempty →
        (∀ p ∈ P, |p 0| ≤ 1/8 ∧ |p 1| ≤ 1/8) →
        FiniteSeparatedAt (Δ^2) P → NormalizedFiniteBallBound (Δ^2) t K P →
        ((P.image (coarsePlanarRound ρ)).card:ℝ) ≤ K/Δ^t →
      ∀ V : Space 2 → Finset (Space 2),
        (∀ p ∈ P, (V p).Nonempty ∧ FiniteSeparatedAt (Δ^2) (V p) ∧
          NormalizedFiniteBallBound (Δ^2) s K (V p) ∧
          1/(K*(Δ^s)^2) ≤ ((V p).card:ℝ) ∧ ((V p).card:ℝ) ≤ K/(Δ^s)^2 ∧
          ∀ l ∈ V p, |l 0| ≤ 1/2 ∧ TubeIncident (Δ^2) p l) →
        ¬ (((P.biUnion V).card:ℝ) ≤ K/(Δ^s)^4 ∧
          (((P.biUnion V).image (coarsePlanarRound ρ)).card:ℝ) ≤ K/(ρ^s)^2) := by
  obtain ⟨θ,N1,hθ,hN1,hfalse⟩ := frozen_coarse_packet_impossible hκ hκ1
  obtain ⟨ε,N2,hε,hε1,hN2,hreserve⟩ := regular_packet_scale_budget hκ hθ
  refine ⟨ε,max N1 N2,hε,hε1,lt_of_lt_of_le hN1 (le_max_left _ _),?_⟩
  intro n hn
  dsimp only
  intro s t hs hs1 hgap ht P hP hPsmall hPsep hPball hpoint V hV hsmall
  let Δ := 1/(2:ℝ)^n
  let ρ := 1/(2:ℝ)^(n+3)
  let K := Real.exp (ε*((n+2:ℕ):ℝ)*Real.log 2)
  let D := K^2
  let E := Real.exp (θ*((n+2:ℕ):ℝ)*Real.log 2)
  let S := fun c => P.filter fun p => coarsePlanarRound ρ p = c
  let Jv := Nat.log 2 (∑ p ∈ P, (V p).card)+1
  let Jf := Nat.log 2 (P.biUnion V).card+1
  obtain ⟨hn3,hD80,hHD,h13,h8,hdepth,hDE⟩ := hreserve n ((le_max_right _ _).trans hn)
  have hdepth' : 10*((n:ℝ)+2) ≤ D := by
    change 10*((n+2:ℕ):ℝ) ≤ D at hdepth
    simpa only [Nat.cast_add,Nat.cast_ofNat] using hdepth
  have hn0 : 0 ≤ (n:ℝ) := Nat.cast_nonneg _
  have hΔ : 0 < Δ := by dsimp [Δ]; positivity
  have hρ : 0 < ρ := by dsimp [ρ]; positivity
  have hΔs : 0 < Δ^s := Real.rpow_pos_of_pos hΔ _
  have hρs : 0 < ρ^s := Real.rpow_pos_of_pos hρ _
  have hK0 : 0 < K := Real.exp_pos _
  have hK1 : 1 ≤ K := Real.one_le_exp_iff.mpr (by positivity)
  have hD1 : 1 ≤ D := by change 1 ≤ K^2; exact one_le_pow₀ hK1
  have hD0 : 0 ≤ D := zero_le_one.trans hD1
  have hKD : K ≤ D := by change K ≤ K^2; nlinarith only [mul_le_mul_of_nonneg_right hK1 hK0.le]
  have hs0 : 0 ≤ s := hκ.le.trans hs
  have hsone : s ≤ 1 := by linarith only [hs1,hκ]
  have hst : s < t := by linarith only [hgap,hκ]
  have ht0 : 0 ≤ t := hs0.trans hst.le
  have hge : κ ≤ t-s := by linarith only [hgap,hκ]
  have powE (a : ℕ) (ha : a ≤ 40) : D^a ≤ E :=
    (pow_le_pow_right₀ hD1 ha).trans hDE
  have hDE' : D ≤ E := by simpa only [pow_one] using powE 1 (by norm_num)
  have hKE : K ≤ E := hKD.trans hDE'
  have hPchart : InBoundedLineChart P := fun p hp =>
    ⟨(hPsmall p hp).1.trans (by norm_num),(hPsmall p hp).2.trans (by norm_num)⟩
  obtain ⟨hJp,hJf,hJv⟩ := small_union_selection_logs n hε1 hsone P V hPchart hPsep hsmall.1
  have hJpD : (Nat.log 2 P.card+1:ℕ) ≤ D :=
    (Nat.cast_le.mpr hJp).trans (by push_cast; linarith only [hdepth',hn0])
  have hJvD : (Jv:ℝ) ≤ D :=
    (Nat.cast_le.mpr hJv).trans (by push_cast; linarith only [hdepth',hn0])
  have hJfD : (Jf:ℝ) ≤ D :=
    (Nat.cast_le.mpr hJf).trans (by push_cast; linarith only [hdepth',hn0])
  have hJv0 : 0 < (Jv:ℝ) := by dsimp [Jv]; positivity
  have hJf0 : 0 < (Jf:ℝ) := by dsimp [Jf]; positivity
  obtain ⟨C,hCP,hC,hCchart,hCsep,hCball,hcells,T,hT,hTU,hTUorig,hG,hGsum,hGmem,hnear⟩ :=
    regular_coarse_preparation n hn3 hs0 hsone ht0 ht hK1 hKD hD80 h13 P V hP hPsmall hPball
      (fun p hp => ⟨(hV p hp).1,(hV p hp).2.2.1,(hV p hp).2.2.2.2.2⟩)
      hJpD hJvD hpoint hsmall.2 hsmall.1
  let G := fineCoarsePacket ρ C (fun c => (S c).biUnion V)
  let Jc := Nat.log 2 (C.biUnion T).card+1
  have hCpow : (C.biUnion T).card ≤ 2^(5*n+6) := by
    have hu := small_union_card_dyadic n hε1 hsone (P.biUnion V).card hsmall.1
    have hc : (C.biUnion T).card ≤ 13*(P.biUnion V).card := by exact_mod_cast hTUorig
    calc
      _ ≤ 13*2^(5*n+2) := hc.trans (Nat.mul_le_mul_left _ hu)
      _ ≤ 16*2^(5*n+2) := Nat.mul_le_mul_right _ (by norm_num)
      _ = _ := by rw [show 5*n+6 = (5*n+2)+4 by omega,pow_add]; norm_num; ring
  have hJcD : (Jc:ℝ) ≤ D := by
    have hh := packet_log_of_card_bound hCpow
    have hh' : Jc ≤ 5*n+7 := by dsimp [Jc]; omega
    exact (Nat.cast_le.mpr hh').trans (by push_cast; linarith only [hdepth',hn0])
  have hJc1 : (1:ℝ) ≤ Jc := by dsimp [Jc]; exact_mod_cast Nat.succ_le_succ (Nat.zero_le _)
  have hD5 : 1 ≤ D^5 := one_le_pow₀ hD1
  obtain ⟨k,R,hRC,hR,_,hRball,hmlow,hmup,hband⟩ := uniform_small_cover_pencils (n+3) hs0 hst hD5
    (show 0 ≤ D/(ρ^s)^2 by positivity) C T hC hCchart hCball
    (fun c hc => ⟨(hT c hc).1,(hT c hc).2.1,(hT c hc).2.2.2.1,
      fun a ha => ((hT c hc).2.2.2.2 a ha).1⟩) hTU
  let m := (2:ℝ)^k
  let Kc := D^5*(Jc:ℝ)
  have hm : 0 < m := by dsimp [m]; positivity
  have hKc : 1 ≤ Kc := hD5.trans (le_mul_of_one_le_right (pow_nonneg hD0 _) hJc1)
  have hKc6 : Kc ≤ D^6 := by
    calc
      _ ≤ D^5*D := mul_le_mul_of_nonneg_left hJcD (pow_nonneg hD0 _)
      _ = _ := by ring
  have hMM : 2*m ≤ D^20/ρ^s := coarse_comparable_size_bound hρ hκ hs0 hsone hge hD80
    (zero_le_one.trans hKc) hKc6 (by positivity) le_rfl hHD hmup
  have hmlow6 : 1/(D^6*ρ^s) ≤ m := by
    apply le_trans _ hmlow
    apply div_le_div_of_nonneg_left (by norm_num) (by positivity)
    have hh : 2*D^5 ≤ D^6 := by
      calc
        _ ≤ D*D^5 := mul_le_mul_of_nonneg_right (by linarith only [hD80]) (pow_nonneg hD0 _)
        _ = _ := by ring
    exact mul_le_mul_of_nonneg_right hh hρs.le
  have mono_ball {d u A B : ℝ} (hd : 0 ≤ d) (hAB : A ≤ B) {F : Finset (Space 2)}
      (hb : NormalizedFiniteBallBound d u A F) : NormalizedFiniteBallBound d u B F := by
    intro z r hr hr1
    exact (hb z r hr hr1).trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hAB (Real.rpow_nonneg (hd.trans hr) _)) (Nat.cast_nonneg _))
  have hTreg (c : Space 2) (hc : c ∈ R) : NormalizedFiniteBallBound ρ s Kc (T c) :=
    mono_ball hρ.le (le_mul_of_one_le_right (pow_nonneg hD0 _) hJc1) (hT c (hRC hc)).2.2.2.1
  have hRu : R.biUnion T ⊆ C.biUnion T := Finset.biUnion_subset_biUnion_of_subset_left T hRC
  obtain ⟨Q,hQR,hQ,_,hQball,U,hU,hUsub,hUsum,hUband⟩ := frozen_coarse_configuration hρ
    (zero_le_one.trans hKc) hm (show 0 < 2*m by positivity) R T G hR hRball (by
      intro c hc
      exact ⟨(hband c hc).1,(hband c hc).2,(hT c (hRC hc)).2.1,(hT c (hRC hc)).2.2.1,
        hTreg c hc,fun a ha => ((hT c (hRC hc)).2.2.2.2 a ha).1⟩)
    (P.biUnion V).card (fun a ha => hG a (hRu ha))
  have hQC : Q ⊆ C := hQR.trans hRC
  have hUC : Q.biUnion U ⊆ C.biUnion T := hUsub.trans hRu
  have hF : 2*(Jf:ℝ)*(2*m)/m = 4*(Jf:ℝ) := by field_simp; norm_num
  have hF2 : 2*(Jf:ℝ)*(2*m)/m ≤ D^2 := by
    rw [hF]
    have hh : 4*D ≤ D^2 := by nlinarith only [hD80,hD0]
    exact (mul_le_mul_of_nonneg_left hJfD (by norm_num)).trans hh
  have hKF : Kc*(2*(Jf:ℝ)*(2*m)/m) ≤ E := by
    calc
      _ ≤ D^6*D^2 := mul_le_mul hKc6 hF2 (by positivity) (pow_nonneg hD0 _)
      _ = D^8 := by ring
      _ ≤ _ := powE 8 (by norm_num)
  have hm8 : 1/(D^8*ρ^s) ≤ m/(2*(Jf:ℝ)) := by
    calc
      _ ≤ (1/(D^6*ρ^s))/(2*D) := by
        rw [div_div]
        apply div_le_div_of_nonneg_left (by norm_num) (by positivity)
        have hh : 2*D ≤ D^2 := by nlinarith only [hD80,hD0]
        calc
          _ = (2*D)*(D^6*ρ^s) := by ring
          _ ≤ D^2*(D^6*ρ^s) := mul_le_mul_of_nonneg_right hh (by positivity)
          _ = _ := by ring
      _ ≤ _ := by gcongr
  have hMfinal : 2*m ≤ E/ρ^s := hMM.trans (div_le_div_of_nonneg_right (powE 20 (by norm_num)) hρs.le)
  have hmfinal : 1/(E*ρ^s) ≤ m/(2*(Jf:ℝ)) := by
    apply le_trans _ hm8
    apply div_le_div_of_nonneg_left (by norm_num) (by positivity)
    exact mul_le_mul_of_nonneg_right (powE 8 (by norm_num)) hρs.le
  have hρeq : ρ = Δ/8 := by dsimp [ρ,Δ]; rw [pow_add]; norm_num; ring
  have hBfinal : 2*m ≤ E/Δ^s := by
    have hh := coarse_weight_scale_bound hΔ hsone hD80 (B := 2*m) (by simpa only [hρeq] using hMM)
    exact hh.trans (div_le_div_of_nonneg_right (powE 21 (by norm_num)) hΔs.le)
  apply hfalse n ((le_max_left _ _).trans hn) s t (m/(2*(Jf:ℝ))) (2*m)
    (1/(K*(Δ^s)^2)) (K/(Δ^s)^2) (D/(ρ^s)^2) (Jv:ℝ) (2*m) Q U S
    (fun _ p => V p) (fun c l => roundedIncidentLine ρ c (l 0)) G hs hs1 hgap ht
    (by positivity) (by positivity) hMfinal hmfinal (by positivity)
    (div_le_div_of_nonneg_right hDE' (sq_nonneg _)) hJv0 (hJvD.trans hDE') (by positivity) hBfinal
    (by gcongr) (by positivity) (by gcongr) hQ
    (fun c hc => hCchart c (hQC hc)) (finiteSeparatedAt_subset hQC hCsep)
    (mono_ball hρ.le hKF hQball)
  · intro c hc
    obtain ⟨_,_,hlo,hup,hchart,hsep,hball,hinc⟩ := hU c hc
    exact ⟨hlo,hup,hchart,hsep,mono_ball hρ.le hKF hball,hinc⟩
  · exact (Nat.cast_le.mpr (Finset.card_le_card hUC)).trans hTU
  · intro c hc
    obtain ⟨hne,hrect,hball⟩ := hcells c (hQC hc)
    exact ⟨hne,hrect,mono_ball hΔ.le (powE 5 (by norm_num)) hball⟩
  · intro c hc p hp
    have hpP := (Finset.mem_filter.mp hp).1
    obtain ⟨_,hsep,hball,hlo,hup,hinc⟩ := hV p hpP
    exact ⟨hlo,hup,hsep,mono_ball (sq_nonneg Δ) hKE hball,
      fun l hl => ⟨(hinc l hl).1.trans (by norm_num),(hinc l hl).2⟩⟩
  · exact fun c hc p hp l hl => hnear c (hQC hc) p hp l hl
  · intro c hc a ha
    have haT := (hU c hc).1 ha
    have hw := ((hT c (hQC hc)).2.2.2.2 a haT).2
    have hcard := (hband c (hQR hc)).2
    exact hw.trans (by gcongr)
  · exact fun c hc p hp l hl => hGmem c (hQC hc) p hp l hl
  · exact hUband
  · exact (hUsum.trans (Finset.sum_le_sum_of_subset_of_nonneg hRu (fun a _ _ => Nat.cast_nonneg _))).trans
      (hGsum.trans (div_le_div_of_nonneg_right hDE' (pow_nonneg (Real.rpow_nonneg hΔ.le _) _)))

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Estimates_UniformPacketBounds
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Polynomial bounds for the uniform pencils selected from a small cover. -/
namespace Falconer
attribute [local instance] Classical.propDecidable

theorem uniform_packet_bounds (N : ℕ) {κ s t K D : ℝ}
    (hκ : 0 < κ) (hs : 0 ≤ s) (hs1 : s ≤ 1) (hgap : κ ≤ t-s)
    (hK : 1 ≤ K) (hKD : K ≤ D) (hD : 80 ≤ D) (hH : projectionGapConstant κ ≤ D)
    (P : Finset (Space 2)) (T : Space 2 → Finset (Space 2)) (hP : P.Nonempty)
    (hPchart : InBoundedLineChart P)
    (hPball : NormalizedFiniteBallBound (1/(2:ℝ)^N) t K P)
    (hT : ∀ x ∈ P, (T x).Nonempty ∧ InBoundedLineChart (T x) ∧
      NormalizedFiniteBallBound (1/(2:ℝ)^N) s K (T x) ∧
      ∀ l ∈ T x, TubeIncident (1/(2:ℝ)^N) x l)
    (hunion : ((P.biUnion T).card:ℝ) ≤ D/((1/(2:ℝ)^N)^s)^2)
    (hlog : (Nat.log 2 (P.biUnion T).card+1:ℕ) ≤ D) :
    ∃ k : ℕ, ∃ R ⊆ P, R.Nonempty ∧ (P.card:ℝ) ≤ D*(R.card:ℝ) ∧
      NormalizedFiniteBallBound (1/(2:ℝ)^N) t (D^2) R ∧
      1/(D^2*(1/(2:ℝ)^N)^s) ≤ (2:ℝ)^k ∧
      (2:ℝ)^k ≤ D^9/(1/(2:ℝ)^N)^s ∧
      ∀ x ∈ R, (2:ℝ)^k ≤ ((T x).card:ℝ) ∧ ((T x).card:ℝ) ≤ 2*(2:ℝ)^k := by
  let J := Nat.log 2 (P.biUnion T).card+1
  let δ := 1/(2:ℝ)^N
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hδs : 0 < δ^s := Real.rpow_pos_of_pos hδ _
  have hD1 : 1 ≤ D := by linarith only [hD]
  have hD0 : 0 ≤ D := zero_le_one.trans hD1
  have hK0 : 0 ≤ K := zero_le_one.trans hK
  have hJ0 : 0 ≤ (J:ℝ) := Nat.cast_nonneg _
  have hKJ : K*(J:ℝ) ≤ D^2 := by
    calc
      _ ≤ D*D := mul_le_mul hKD hlog hJ0 hD0
      _ = _ := by ring
  have hst : s < t := by linarith only [hκ,hgap]
  have hp := planarPotentialConstant_pos hst
  have hpot : planarPotentialConstant s t ≤ D := (planarPotentialConstant_gap hκ hs1 hgap).trans hH
  have hD3 : 1 ≤ D^3 := one_le_pow₀ hD1
  have h320 : 320 ≤ D^3 := by
    have hh := pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 80) hD 3
    norm_num at hh
    linarith only [hh]
  have h80 : (80:ℝ)^s ≤ 80 := by
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le
      (by norm_num : (1:ℝ) ≤ 80) hs1
  obtain ⟨k,R,hRP,hR,hsize,hRball,hlo,hup,hband⟩ := uniform_small_cover_pencils N hs hst hK
    (show 0 ≤ D/((1/(2:ℝ)^N)^s)^2 by positivity) P T hP hPchart hPball hT hunion
  refine ⟨k,R,hRP,hR,hsize.trans (mul_le_mul_of_nonneg_right hlog (Nat.cast_nonneg _)),?_,?_,?_,hband⟩
  · intro z r hr hr1
    exact (hRball z r hr hr1).trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hKJ (Real.rpow_nonneg (hδ.le.trans hr) _)) (Nat.cast_nonneg _))
  · apply le_trans _ hlo
    apply div_le_div_of_nonneg_left (by norm_num) (by positivity)
    have hh : 2*K ≤ D^2 := by
      have hd : 2 ≤ D := by linarith only [hD]
      have hh := mul_le_mul_of_nonneg_right hd hD0
      nlinarith only [hh,hKD]
    nlinarith only [mul_le_mul_of_nonneg_right hh hδs.le]
  · have hp' : 1+(K*(J:ℝ))*planarPotentialConstant s t ≤ 2*D^3 := by
      calc
        _ ≤ 1+D^2*D := by gcongr
        _ ≤ _ := by nlinarith only [hD3]
    calc
      (2:ℝ)^k ≤ 2*(D/(δ^s)^2)*(K*(J:ℝ))*(80*δ)^s*(1+(K*(J:ℝ))*planarPotentialConstant s t) := hup
      _ = 2*(D/(δ^s)^2)*(K*(J:ℝ))*((80:ℝ)^s*δ^s)*(1+(K*(J:ℝ))*planarPotentialConstant s t) := by
        rw [Real.mul_rpow (by norm_num : (0:ℝ) ≤ 80) hδ.le]
      _ ≤ 2*(D/(δ^s)^2)*D^2*(80*δ^s)*(2*D^3) := by gcongr
      _ = 320*D^6/δ^s := by field_simp; ring
      _ ≤ D^9/δ^s := by
        apply div_le_div_of_nonneg_right _ hδs.le
        calc
          _ ≤ D^3*D^6 := mul_le_mul_of_nonneg_right h320 (pow_nonneg hD0 _)
          _ = _ := by ring

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Estimates_GeneralRegularSetAlternative
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Remove the auxiliary fine-pencil cardinality normalization from the
regular-set alternative by selecting comparable original pencils. -/
namespace Falconer
attribute [local instance] Classical.propDecidable

theorem general_regular_coarse_cover_alternative {κ : ℝ} (hκ : 0 < κ) (hκ1 : κ ≤ 1) :
    ∃ ε : ℝ, ∃ N0 : ℕ, 0 < ε ∧ ε ≤ 1 ∧ 0 < N0 ∧ ∀ n : ℕ, N0 ≤ n+2 →
      let Δ := 1/(2:ℝ)^n
      let ρ := 1/(2:ℝ)^(n+3)
      let K := Real.exp (ε*((n+2:ℕ):ℝ)*Real.log 2)
      ∀ s t : ℝ, κ ≤ s → s ≤ 1-8*κ → 2*κ ≤ t-s → t ≤ 2 →
      ∀ P : Finset (Space 2), P.Nonempty →
        (∀ p ∈ P, |p 0| ≤ 1/8 ∧ |p 1| ≤ 1/8) →
        FiniteSeparatedAt (Δ^2) P → NormalizedFiniteBallBound (Δ^2) t K P →
        ((P.image (coarsePlanarRound ρ)).card:ℝ) ≤ K/Δ^t →
      ∀ V : Space 2 → Finset (Space 2),
        (∀ p ∈ P, (V p).Nonempty ∧ InBoundedLineChart (V p) ∧
          FiniteSeparatedAt (Δ^2) (V p) ∧ NormalizedFiniteBallBound (Δ^2) s K (V p) ∧
          ∀ l ∈ V p, |l 0| ≤ 1/2 ∧ TubeIncident (Δ^2) p l) →
        ¬ (((P.biUnion V).card:ℝ) ≤ K/(Δ^s)^4 ∧
          (((P.biUnion V).image (coarsePlanarRound ρ)).card:ℝ) ≤ K/(ρ^s)^2) := by
  obtain ⟨θ,N1,hθ,_,hN1,hmain⟩ := regular_coarse_cover_alternative hκ hκ1
  obtain ⟨ε,N2,hε,hε1,hN2,hreserve⟩ := regular_packet_scale_budget hκ hθ
  refine ⟨ε,max N1 N2,hε,hε1,lt_of_lt_of_le hN1 (le_max_left _ _),?_⟩
  intro n hn
  dsimp only
  intro s t hs hs1 hgap ht P hP hPsmall hPsep hPball hpoint V hV hsmall
  let Δ := 1/(2:ℝ)^n
  let ρ := 1/(2:ℝ)^(n+3)
  let δ := 1/(2:ℝ)^(2*n)
  let K := Real.exp (ε*((n+2:ℕ):ℝ)*Real.log 2)
  let D := K^2
  let E := Real.exp (θ*((n+2:ℕ):ℝ)*Real.log 2)
  obtain ⟨_,hD80,hHD,_,_,hdepth,hDE⟩ := hreserve n ((le_max_right _ _).trans hn)
  have hΔ : 0 < Δ := by dsimp [Δ]; positivity
  have hδ : δ = Δ^2 := by
    dsimp [δ,Δ]
    rw [show 2*n = n*2 by omega,pow_mul,div_pow,one_pow]
  have hδ0 : 0 < δ := by dsimp [δ]; positivity
  have hδs : δ^s = (Δ^s)^2 := by
    rw [hδ,← Real.rpow_natCast_mul hΔ.le 2 s]
    norm_num only [Nat.cast_ofNat]
    rw [show (2:ℝ)*s = s*2 by ring]
    simpa only [Nat.cast_ofNat] using Real.rpow_mul_natCast hΔ.le s 2
  have hδs2 : (δ^s)^2 = (Δ^s)^4 := by rw [hδs]; ring
  have hK0 : 0 < K := Real.exp_pos _
  have hK1 : 1 ≤ K := Real.one_le_exp_iff.mpr (by positivity)
  have hD1 : 1 ≤ D := by change 1 ≤ K^2; exact one_le_pow₀ hK1
  have hD0 : 0 ≤ D := zero_le_one.trans hD1
  have hKD : K ≤ D := by change K ≤ K^2; nlinarith only [mul_le_mul_of_nonneg_right hK1 hK0.le]
  have powE (a : ℕ) (ha : a ≤ 40) : D^a ≤ E := (pow_le_pow_right₀ hD1 ha).trans hDE
  have hKE : K ≤ E := hKD.trans (by simpa only [pow_one] using powE 1 (by norm_num))
  have hs0 : 0 ≤ s := hκ.le.trans hs
  have hsone : s ≤ 1 := by linarith only [hs1,hκ]
  have hge : κ ≤ t-s := by linarith only [hgap,hκ]
  have hPchart : InBoundedLineChart P := fun p hp =>
    ⟨(hPsmall p hp).1.trans (by norm_num),(hPsmall p hp).2.trans (by norm_num)⟩
  have hlog : (Nat.log 2 (P.biUnion V).card+1:ℕ) ≤ D := by
    have hh := (small_union_selection_logs n hε1 hsone P V hPchart hPsep hsmall.1).2.1
    have hd : 10*((n:ℝ)+2) ≤ D := by
      change 10*((n+2:ℕ):ℝ) ≤ D at hdepth
      simpa only [Nat.cast_add,Nat.cast_ofNat] using hdepth
    exact (Nat.cast_le.mpr hh).trans (by push_cast; have := Nat.cast_nonneg (α := ℝ) n; linarith only [hd,this])
  have hunion : ((P.biUnion V).card:ℝ) ≤ D/(δ^s)^2 := by
    rw [hδs2]
    exact hsmall.1.trans (div_le_div_of_nonneg_right hKD (pow_nonneg (Real.rpow_nonneg hΔ.le _) _))
  have hPballδ : NormalizedFiniteBallBound δ t K P := by rw [hδ]; exact hPball
  have hVδ (p : Space 2) (hp : p ∈ P) : (V p).Nonempty ∧ InBoundedLineChart (V p) ∧
      NormalizedFiniteBallBound δ s K (V p) ∧ ∀ l ∈ V p, TubeIncident δ p l := by
    rw [hδ]
    exact ⟨(hV p hp).1,(hV p hp).2.1,(hV p hp).2.2.2.1,
      fun l hl => ((hV p hp).2.2.2.2 l hl).2⟩
  obtain ⟨k,R,hRP,hR,_,hRball,hlo,hup,hband⟩ := uniform_packet_bounds (2*n) hκ hs0 hsone hge
    hK1 hKD hD80 hHD P V hP hPchart hPballδ hVδ hunion hlog
  have hRU : R.biUnion V ⊆ P.biUnion V := Finset.biUnion_subset_biUnion_of_subset_left V hRP
  have mono_ball {d u A B : ℝ} (hd : 0 ≤ d) (hAB : A ≤ B) {F : Finset (Space 2)}
      (hb : NormalizedFiniteBallBound d u A F) : NormalizedFiniteBallBound d u B F := by
    intro z r hr hr1
    exact (hb z r hr hr1).trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hAB (Real.rpow_nonneg (hd.trans hr) _)) (Nat.cast_nonneg _))
  have hRball' : NormalizedFiniteBallBound (Δ^2) t E R := by
    rw [← hδ]
    exact mono_ball hδ0.le (powE 2 (by norm_num)) hRball
  refine hmain n ((le_max_left _ _).trans hn) s t hs hs1 hgap ht R hR
    (fun p hp => hPsmall p (hRP hp)) (finiteSeparatedAt_subset hRP hPsep) hRball' ?_ V ?_ ?_
  · calc
      _ ≤ ((P.image (coarsePlanarRound ρ)).card:ℝ) := Nat.cast_le.mpr (Finset.card_le_card (Finset.image_subset_image hRP))
      _ ≤ K/Δ^t := hpoint
      _ ≤ _ := div_le_div_of_nonneg_right hKE (Real.rpow_nonneg hΔ.le _)
  · intro p hp
    have htube := hV p (hRP hp)
    refine ⟨htube.1,htube.2.2.1,mono_ball (sq_nonneg Δ) hKE htube.2.2.2.1,?_,?_,htube.2.2.2.2⟩
    · have hc := (hband p hp).1
      have hl : 1/(E*δ^s) ≤ (2:ℝ)^k := by
        apply le_trans _ hlo
        exact div_le_div_of_nonneg_left (by norm_num) (by positivity)
          (mul_le_mul_of_nonneg_right (powE 2 (by norm_num)) (Real.rpow_nonneg hδ0.le _))
      rw [hδs] at hl
      exact hl.trans hc
    · have hu : 2*(2:ℝ)^k ≤ E/δ^s := by
        calc
          _ ≤ 2*(D^9/δ^s) := mul_le_mul_of_nonneg_left hup (by norm_num)
          _ ≤ D^10/δ^s := by
            rw [← mul_div_assoc]
            apply div_le_div_of_nonneg_right _ (Real.rpow_nonneg hδ0.le _)
            calc
              _ ≤ D*D^9 := mul_le_mul_of_nonneg_right (by linarith only [hD80]) (pow_nonneg hD0 _)
              _ = _ := by ring
          _ ≤ _ := div_le_div_of_nonneg_right (powE 10 (by norm_num)) (Real.rpow_nonneg hδ0.le _)
      rw [hδs] at hu
      exact (hband p hp).2.trans hu
  · constructor
    · exact (Nat.cast_le.mpr (Finset.card_le_card hRU)).trans
        (hsmall.1.trans (div_le_div_of_nonneg_right hKE (pow_nonneg (Real.rpow_nonneg hΔ.le _) _)))
    · exact (Nat.cast_le.mpr (Finset.card_le_card (Finset.image_subset_image hRU))).trans
        (hsmall.2.trans (div_le_div_of_nonneg_right hKE (sq_nonneg _)))

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

theorem localCellLine_regular {δ Δ s K y a : ℝ}
    (hΔ : 0 < Δ) (hΔ1 : Δ ≤ 1) (hy : |y| ≤ 1)
    (hδΔ : δ ≤ Δ) (hs : 0 ≤ s) (hK : 1 ≤ K)
    (T : Finset (Space 2)) (hT : NormalizedFiniteBallBound δ s K T) :
    NormalizedFiniteBallBound Δ s (K*3^s) (T.image (localCellLine Δ y a)) := by
  intro z r hr _
  have hr0 : 0 ≤ r := hΔ.le.trans hr
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
      (hδΔ.trans (by linarith only [hr,hr0]))
    _ = _ := by rw [Real.mul_rpow (by norm_num : (0:ℝ) ≤ 3) hr0]; ring

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

theorem localCellLine_chart {Δ y a : ℝ} (hΔ : 0 < Δ) (hΔsmall : Δ ≤ 1/8)
    (p l : Space 2) (hp0 : |p 0-y| ≤ Δ/4) (hp1 : |p 1-a| ≤ Δ/4)
    (hl0 : |l 0| ≤ 1/2) (hi : TubeIncident (Δ^2) p l) :
    |localCellLine Δ y a l 0| ≤ 1 ∧ |localCellLine Δ y a l 1| ≤ 1 := by
  have hres := tube_residual_le (sq_nonneg Δ) (hl0.trans (by norm_num)) hi
  have hb : |l 0*y+l 1-a| ≤ Δ/4+Δ/8+2*Δ^2 := by
    calc
      _ = |(p 1-a)-l 0*(p 0-y)-(p 1-l 0*p 0-l 1)| := by congr 1; ring
      _ ≤ |(p 1-a)-l 0*(p 0-y)|+|p 1-l 0*p 0-l 1| := abs_sub _ _
      _ ≤ (|p 1-a|+|l 0*(p 0-y)|)+|p 1-l 0*p 0-l 1| :=
        add_le_add (abs_sub _ _) le_rfl
      _ ≤ Δ/4+(1/2)*(Δ/4)+2*Δ^2 := by rw [abs_mul]; gcongr
      _ = _ := by ring
  refine ⟨hl0.trans (by norm_num),?_⟩
  change |(l 0*y+l 1-a)/Δ| ≤ 1
  rw [abs_div,abs_of_pos hΔ,div_le_one hΔ]
  exact hb.trans (by nlinarith only [hΔsmall,mul_nonneg hΔ.le (sub_nonneg.mpr hΔsmall)])

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Incidence_LocalCellIncidence
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The fine union inside a regular coarse cell retains the original pencil
size in the elementary incidence bound. This is the local factor needed
in the scale-combination argument. -/
namespace Falconer
open scoped BigOperators
attribute [local instance] Classical.propDecidable

theorem local_cell_variable_incidence (N : ℕ) {s t K m M y a : ℝ}
    (hN : 3 ≤ N) (hs : 0 ≤ s) (hst : s < t) (hK : 1 ≤ K) (hm : 0 ≤ m)
    (hy : |y| ≤ 1) (P : Finset (Space 2)) (T : Space 2 → Finset (Space 2))
    (hP : P.Nonempty)
    (hcell : ∀ p ∈ P, |p 0-y| ≤ (1/(2:ℝ)^N)/4 ∧ |p 1-a| ≤ (1/(2:ℝ)^N)/4)
    (hPball : NormalizedFiniteBallBound (1/(2:ℝ)^N) t K
      (P.image (localPacketPoint (1/(2:ℝ)^N) y a)))
    (hT : ∀ p ∈ P, m ≤ ((T p).card:ℝ) ∧ ((T p).card:ℝ) ≤ M ∧
      NormalizedFiniteBallBound ((1/(2:ℝ)^N)^2) s K (T p) ∧
      ∀ l ∈ T p, |l 0| ≤ 1/2 ∧ TubeIncident ((1/(2:ℝ)^N)^2) p l) :
    m^2 ≤ ((P.biUnion T).card:ℝ)*
      (((K*3^s)*(80*(1/(2:ℝ)^N))^s*M)*(1+(K*3^s)*planarPotentialConstant s t)) := by
  let Δ := 1/(2:ℝ)^N
  let F := localPacketPoint Δ y a
  let L := localCellLine Δ y a
  let R := P.image F
  let V := fun q => (T (Δ • q+rowPoint y a)).image L
  let C := K*3^s
  have hΔ : 0 < Δ := by dsimp [Δ]; positivity
  have hΔsmall : Δ ≤ 1/8 := by
    change 1/(2:ℝ)^N ≤ 1/8
    have hp : (2:ℝ)^3 ≤ (2:ℝ)^N := pow_le_pow_right₀ (by norm_num) hN
    norm_num at hp
    exact (div_le_div_iff_of_pos_left (by norm_num) (by positivity) (by norm_num)).2 hp
  have hΔ1 : Δ ≤ 1 := hΔsmall.trans (by norm_num)
  have hinv (p : Space 2) : Δ • F p+rowPoint y a = p := by
    apply localPacketPoint_injective hΔ y a
    exact localPacketPoint_inverse hΔ y a (F p)
  have hV (p : Space 2) : V (F p) = (T p).image L := by
    change (T (Δ • F p+rowPoint y a)).image L = _
    rw [hinv]
  have hC : 1 ≤ C := by
    have hh : 1 ≤ (3:ℝ)^s := Real.one_le_rpow (by norm_num) hs
    dsimp [C]
    nlinarith only [hh,hK]
  have hKC : K ≤ C := by
    dsimp [C]
    exact le_mul_of_one_le_right (zero_le_one.trans hK) (Real.one_le_rpow (by norm_num) hs)
  have hRb : NormalizedFiniteBallBound Δ t C R := by
    intro z r hr hr1
    exact (hPball z r hr hr1).trans (by
      apply mul_le_mul_of_nonneg_right _ (Nat.cast_nonneg _)
      exact mul_le_mul_of_nonneg_right hKC (Real.rpow_nonneg (hΔ.le.trans hr) _))
  have hRchart : InBoundedLineChart R := localPacketPoint_chart hΔ P (fun p hp =>
    ⟨(hcell p hp).1.trans (by linarith only [hΔ]),
      (hcell p hp).2.trans (by linarith only [hΔ])⟩)
  have hdata (q : Space 2) (hq : q ∈ R) :
      m ≤ ((V q).card:ℝ) ∧ ((V q).card:ℝ) ≤ M ∧ InBoundedLineChart (V q) ∧
      NormalizedFiniteBallBound Δ s C (V q) ∧ ∀ l ∈ V q, TubeIncident Δ q l := by
    obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp hq
    rw [hV]
    have hcard : ((T p).image L).card = (T p).card :=
      Finset.card_image_of_injective _ (localCellLine_injective hΔ y a)
    refine ⟨by simpa only [hcard] using (hT p hp).1,
      by simpa only [hcard] using (hT p hp).2.1,?_,?_,?_⟩
    · intro l hl
      obtain ⟨b,hb,rfl⟩ := Finset.mem_image.mp hl
      exact localCellLine_chart hΔ hΔsmall p b (hcell p hp).1 (hcell p hp).2
        ((hT p hp).2.2.2 b hb).1 ((hT p hp).2.2.2 b hb).2
    · exact localCellLine_regular hΔ hΔ1 hy (by nlinarith only [hΔ1,hΔ]) hs hK
        (T p) (hT p hp).2.2.1
    · intro l hl
      obtain ⟨b,hb,rfl⟩ := Finset.mem_image.mp hl
      have hi := localCellLine_incident hΔ y a p b ((hT p hp).2.2.2 b hb).2
      change TubeIncident (Δ^2/Δ) (F p) (L b) at hi
      simpa only [sq, mul_div_cancel_right₀ _ hΔ.ne'] using hi
  have hU : R.biUnion V ⊆ (P.biUnion T).image L := by
    intro l hl
    obtain ⟨q,hq,hl⟩ := Finset.mem_biUnion.mp hl
    obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp hq
    rw [hV] at hl
    obtain ⟨b,hb,rfl⟩ := Finset.mem_image.mp hl
    exact Finset.mem_image_of_mem _ (Finset.mem_biUnion.mpr ⟨p,hp,hb⟩)
  have hcount : ((R.biUnion V).card:ℝ) ≤ ((P.biUnion T).card:ℝ) := by
    exact_mod_cast (Finset.card_le_card hU).trans Finset.card_image_le
  have hconst : 0 ≤ (C*(80*Δ)^s*M)*(1+C*planarPotentialConstant s t) := by
    obtain ⟨p,hp⟩ := hP
    have hM : 0 ≤ M := (Nat.cast_nonneg _).trans (hT p hp).2.1
    have hpot := planarPotentialConstant_pos hst
    have hc0 := zero_le_one.trans hC
    positivity
  exact (planar_variable_baseline_incidence N hs hst hC hm R V (hP.image F)
    hRchart hRb hdata).trans (mul_le_mul_of_nonneg_right hcount hconst)

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Estimates_PacketScaleCombination
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Counting the original fine packets produces the pencil-normalized
product estimate used in the regular-set argument. -/
namespace Falconer
open scoped BigOperators
attribute [local instance] Classical.propDecidable

theorem finite_packet_scale_combination {m B H J n : ℝ}
    (hB : 0 ≤ B) (hH : 0 ≤ H) (hn : 0 ≤ n)
    (A D F U : Finset (Space 2)) (G : Space 2 → Finset (Space 2))
    (hDA : D ⊆ A) (hD : (D.card:ℝ) ≤ H)
    (hcover : F ⊆ D.biUnion G)
    (hband : ∀ a ∈ A, n ≤ ((G a).card:ℝ) ∧ ((G a).card:ℝ) ≤ 2*n)
    (htotal : (∑ a ∈ A, ((G a).card:ℝ)) ≤ J*(U.card:ℝ))
    (hlocal : m^2 ≤ (F.card:ℝ)*B) :
    m^2*(A.card:ℝ) ≤ 2*J*(U.card:ℝ)*H*B := by
  have hF : (F.card:ℝ) ≤ 2*n*H := by
    calc
      _ ≤ ∑ a ∈ D, ((G a).card:ℝ) := by
        exact_mod_cast (Finset.card_le_card hcover).trans Finset.card_biUnion_le
      _ ≤ ∑ _a ∈ D, 2*n := Finset.sum_le_sum fun a ha => (hband a (hDA ha)).2
      _ = 2*n*(D.card:ℝ) := by simp; ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hD (by positivity)
  have hA : n*(A.card:ℝ) ≤ J*(U.card:ℝ) := by
    calc
      _ = ∑ _a ∈ A, n := by simp; ring
      _ ≤ ∑ a ∈ A, ((G a).card:ℝ) := Finset.sum_le_sum fun a ha => (hband a ha).1
      _ ≤ _ := htotal
  calc
    _ ≤ ((2*n*H)*B)*(A.card:ℝ) :=
      mul_le_mul_of_nonneg_right (hlocal.trans (mul_le_mul_of_nonneg_right hF hB))
        (Nat.cast_nonneg _)
    _ = 2*(n*(A.card:ℝ))*H*B := by ring
    _ ≤ 2*(J*(U.card:ℝ))*H*B :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hA (by norm_num)) hH) hB
    _ = _ := by ring

theorem local_cell_packet_scale_combination (N : ℕ) {s t K m M y a H J n : ℝ}
    (hN : 3 ≤ N) (hs : 0 ≤ s) (hst : s < t) (hK : 1 ≤ K) (hm : 0 ≤ m)
    (hH : 0 ≤ H) (hn : 0 ≤ n) (hy : |y| ≤ 1)
    (P A D U : Finset (Space 2)) (T G : Space 2 → Finset (Space 2))
    (hP : P.Nonempty)
    (hcell : ∀ p ∈ P, |p 0-y| ≤ (1/(2:ℝ)^N)/4 ∧ |p 1-a| ≤ (1/(2:ℝ)^N)/4)
    (hPball : NormalizedFiniteBallBound (1/(2:ℝ)^N) t K
      (P.image (localPacketPoint (1/(2:ℝ)^N) y a)))
    (hT : ∀ p ∈ P, m ≤ ((T p).card:ℝ) ∧ ((T p).card:ℝ) ≤ M ∧
      NormalizedFiniteBallBound ((1/(2:ℝ)^N)^2) s K (T p) ∧
      ∀ l ∈ T p, |l 0| ≤ 1/2 ∧ TubeIncident ((1/(2:ℝ)^N)^2) p l)
    (hDA : D ⊆ A) (hD : (D.card:ℝ) ≤ H)
    (hcover : ∀ p ∈ P, ∀ l ∈ T p, ∃ b ∈ D, l ∈ G b)
    (hband : ∀ b ∈ A, n ≤ ((G b).card:ℝ) ∧ ((G b).card:ℝ) ≤ 2*n)
    (htotal : (∑ b ∈ A, ((G b).card:ℝ)) ≤ J*(U.card:ℝ)) :
    m^2*(A.card:ℝ) ≤ 2*J*(U.card:ℝ)*H*
      (((K*3^s)*(80*(1/(2:ℝ)^N))^s*M)*(1+(K*3^s)*planarPotentialConstant s t)) := by
  have hM : 0 ≤ M := by
    obtain ⟨p,hp⟩ := hP
    exact (Nat.cast_nonneg _).trans (hT p hp).2.1
  have hpot := planarPotentialConstant_pos hst
  have hk0 := zero_le_one.trans hK
  apply finite_packet_scale_combination (by positivity) hH hn A D (P.biUnion T) U G
    hDA hD ?_ hband htotal
    (local_cell_variable_incidence N hN hs hst hK hm hy P T hP hcell hPball hT)
  intro l hl
  obtain ⟨p,hp,hl⟩ := Finset.mem_biUnion.mp hl
  obtain ⟨b,hb,hlb⟩ := hcover p hp l hl
  exact Finset.mem_biUnion.mpr ⟨b,hb,hlb⟩

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Estimates_InterpolatedTubeKernel
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Interpolation of the regularity and separation bounds on a common
pencil. The intermediate potential exponent stays strictly below the point
dimension, so only the already proved finite geometric-series bound is used. -/
namespace Falconer
attribute [local instance] Classical.propDecidable

theorem interpolate_two_power_bounds {z A B r s u θ : ℝ}
    (hz : 0 ≤ z) (hA : 0 ≤ A) (hB : 0 ≤ B) (hr : 0 < r)
    (hθ : 0 < θ) (hθ1 : θ < 1) (he : s*θ+2*(1-θ) = u)
    (hfirst : z ≤ A*r^s) (hsecond : z ≤ B*r^2) :
    z ≤ A^θ*B^(1-θ)*r^u := by
  by_cases hz0 : z = 0
  · rw [hz0]
    positivity
  have hzpos : 0 < z := lt_of_le_of_ne hz (Ne.symm hz0)
  calc
    z = z^θ*z^(1-θ) := by rw [← Real.rpow_add hzpos]; norm_num
    _ ≤ (A*r^s)^θ*(B*r^2)^(1-θ) := by
      exact mul_le_mul (Real.rpow_le_rpow hz hfirst hθ.le)
        (Real.rpow_le_rpow hz hsecond (by linarith only [hθ1]))
        (Real.rpow_nonneg hz _) (by positivity)
    _ = A^θ*B^(1-θ)*r^u := by
      rw [Real.mul_rpow hA (Real.rpow_nonneg hr.le _),
        Real.mul_rpow hB (sq_nonneg r),← Real.rpow_mul hr.le,
        ← Real.rpow_natCast_mul hr.le 2 (1-θ)]
      norm_num only [Nat.cast_ofNat]
      rw [show A^θ*r^(s*θ)*(B^(1-θ)*r^(2*(1-θ))) =
        (A^θ*B^(1-θ))*(r^(s*θ)*r^(2*(1-θ))) by ring,
        ← Real.rpow_add hr,he]

theorem intersect_tube_interpolated_bound {δ s u θ K M : ℝ}
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hs : 0 ≤ s) (hK : 1 ≤ K)
    (hθ : 0 < θ) (hθ1 : θ < 1) (he : s*θ+2*(1-θ) = u)
    (T U : Finset (Space 2)) (x y : Space 2) (hx0 : |x 0| ≤ 1)
    (hchart : InBoundedLineChart T) (hsep : FiniteSeparatedAt δ T)
    (hball : NormalizedFiniteBallBound δ s K T) (hM : (T.card:ℝ) ≤ M)
    (hx : ∀ l ∈ T, TubeIncident δ x l) (hy : ∀ l ∈ U, TubeIncident δ y l) :
    ((T ∩ U).card:ℝ) ≤
      (K*(80*δ)^s*M)^θ*(25921:ℝ)^(1-θ)*(1/truncatedPlanarDistance δ x y)^u := by
  have hr := (truncatedPlanarDistance_bounds hδ hδ1 x y).1
  have hm0 : 0 ≤ M := (Nat.cast_nonneg _).trans hM
  have hfirst : ((T ∩ U).card:ℝ) ≤
      (K*(80*δ)^s*M)*(1/truncatedPlanarDistance δ x y)^s := by
    have hh := intersect_tube_kernel_bound hδ hδ1 hs hK T U x y hx0 hchart hx hy hball
    rw [show 80*δ/truncatedPlanarDistance δ x y =
      (80*δ)*(1/truncatedPlanarDistance δ x y) by ring,
      Real.mul_rpow (by positivity : 0 ≤ 80*δ) (by positivity)] at hh
    calc
      _ ≤ _ := hh
      _ = (K*(80*δ)^s*(T.card:ℝ))*(1/truncatedPlanarDistance δ x y)^s := by ring
      _ ≤ _ := by gcongr
  exact interpolate_two_power_bounds (Nat.cast_nonneg _) (by positivity)
    (by norm_num) (by positivity) hθ hθ1 he hfirst
    (intersect_tube_packing_bound hδ hδ1 T U x y hx0 hchart hsep hx hy)

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Incidence_InterpolatedIncidence
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A large pencil improves the elementary incidence estimate. The exponent
is obtained by interpolating the actual packing and regularity kernels. -/
namespace Falconer
open scoped BigOperators
attribute [local instance] Classical.propDecidable

theorem pencil_interpolated_second_moment (N : ℕ) {s t u θ K M : ℝ}
    (hs : 0 ≤ s) (hu : 0 ≤ u) (hut : u < t) (hK : 1 ≤ K) (hM0 : 0 ≤ M)
    (hθ : 0 < θ) (hθ1 : θ < 1) (he : s*θ+2*(1-θ) = u)
    (P : Finset (Space 2)) (T : Space 2 → Finset (Space 2))
    (hPchart : InBoundedLineChart P)
    (hPball : NormalizedFiniteBallBound (1/(2:ℝ)^N) t K P)
    (hT : ∀ x ∈ P, InBoundedLineChart (T x) ∧ FiniteSeparatedAt (1/(2:ℝ)^N) (T x) ∧
      NormalizedFiniteBallBound (1/(2:ℝ)^N) s K (T x) ∧
      ((T x).card:ℝ) ≤ M ∧ ∀ l ∈ T x, TubeIncident (1/(2:ℝ)^N) x l) :
    (∑ x ∈ P, ∑ y ∈ P, ((T x ∩ T y).card:ℝ)) ≤
      ((K*(80*(1/(2:ℝ)^N))^s*M)^θ*(25921:ℝ)^(1-θ))*
        (1+K*planarPotentialConstant u t)*(P.card:ℝ)^2 := by
  let δ := 1/(2:ℝ)^N
  let A := (K*(80*δ)^s*M)^θ*(25921:ℝ)^(1-θ)
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hδ1 : δ ≤ 1 := (div_le_one (by positivity)).2 (one_le_pow₀ (by norm_num))
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hrow (x : Space 2) (hx : x ∈ P) :
      (∑ y ∈ P, ((T x ∩ T y).card:ℝ)) ≤ A*(1+K*planarPotentialConstant u t)*(P.card:ℝ) := by
    have hpot := finite_dyadic_truncated_potential_real P x N hK hu hut hPball
    calc
      _ ≤ ∑ y ∈ P, A*(1+(1/max (dist x y) δ)^u) := by
        apply Finset.sum_le_sum
        intro y hy
        exact (intersect_tube_interpolated_bound hδ hδ1 hs hK hθ hθ1 he (T x) (T y)
          x y (hPchart x hx).1 (hT x hx).1 (hT x hx).2.1 (hT x hx).2.2.1
          (hT x hx).2.2.2.1 (hT x hx).2.2.2.2 (hT y hy).2.2.2.2).trans
          (mul_le_mul_of_nonneg_left (truncatedPlanarDistance_inverse_power_le hδ hδ1 x y) hA)
      _ = A*((P.card:ℝ)+∑ y ∈ P, (1/max (dist x y) δ)^u) := by
        simp only [mul_add,Finset.sum_add_distrib,Finset.sum_const,nsmul_eq_mul,mul_one]
        rw [← Finset.mul_sum]
        ring
      _ ≤ A*((P.card:ℝ)+K*planarPotentialConstant u t*(P.card:ℝ)) :=
        mul_le_mul_of_nonneg_left (add_le_add le_rfl hpot) hA
      _ = _ := by ring
  calc
    _ ≤ ∑ _x ∈ P, A*(1+K*planarPotentialConstant u t)*(P.card:ℝ) := Finset.sum_le_sum hrow
    _ = _ := by simp only [Finset.sum_const,nsmul_eq_mul]; dsimp [A]; ring

theorem planar_interpolated_incidence (N : ℕ) {s t u θ K m M : ℝ}
    (hs : 0 ≤ s) (hu : 0 ≤ u) (hut : u < t) (hK : 1 ≤ K) (hm : 0 ≤ m)
    (hθ : 0 < θ) (hθ1 : θ < 1) (he : s*θ+2*(1-θ) = u)
    (P : Finset (Space 2)) (T : Space 2 → Finset (Space 2)) (hP : P.Nonempty)
    (hPchart : InBoundedLineChart P)
    (hPball : NormalizedFiniteBallBound (1/(2:ℝ)^N) t K P)
    (hT : ∀ x ∈ P, m ≤ ((T x).card:ℝ) ∧ ((T x).card:ℝ) ≤ M ∧
      InBoundedLineChart (T x) ∧ FiniteSeparatedAt (1/(2:ℝ)^N) (T x) ∧
      NormalizedFiniteBallBound (1/(2:ℝ)^N) s K (T x) ∧
      ∀ l ∈ T x, TubeIncident (1/(2:ℝ)^N) x l) :
    m^2 ≤ ((P.biUnion T).card:ℝ)*
      (((K*(80*(1/(2:ℝ)^N))^s*M)^θ*(25921:ℝ)^(1-θ))*
        (1+K*planarPotentialConstant u t)) := by
  let B := ((K*(80*(1/(2:ℝ)^N))^s*M)^θ*(25921:ℝ)^(1-θ))*
    (1+K*planarPotentialConstant u t)
  have hI : m*(P.card:ℝ) ≤ ∑ x ∈ P, ((T x).card:ℝ) := by
    calc
      _ = ∑ _x ∈ P, m := by simp; ring
      _ ≤ _ := Finset.sum_le_sum fun x hx => (hT x hx).1
  have hM0 : 0 ≤ M := by
    obtain ⟨p,hp⟩ := hP
    exact (Nat.cast_nonneg _).trans (hT p hp).2.1
  have hE := pencil_interpolated_second_moment N hs hu hut hK hM0 hθ hθ1 he P T hPchart hPball
    (fun x hx => ⟨(hT x hx).2.2.1,(hT x hx).2.2.2.1,(hT x hx).2.2.2.2.1,
      (hT x hx).2.1,(hT x hx).2.2.2.2.2⟩)
  have hh : (m*(P.card:ℝ))^2 ≤ ((P.biUnion T).card:ℝ)*(B*(P.card:ℝ)^2) := by
    calc
      _ ≤ (∑ x ∈ P, ((T x).card:ℝ))^2 :=
        (sq_le_sq₀ (by positivity) (Finset.sum_nonneg fun _ _ => Nat.cast_nonneg _)).2 hI
      _ ≤ ((P.biUnion T).card:ℝ)*(∑ x ∈ P, ∑ y ∈ P, ((T x ∩ T y).card:ℝ)) :=
        tube_union_second_moment P T
      _ ≤ _ := mul_le_mul_of_nonneg_left hE (Nat.cast_nonneg _)
  have hPc : 0 < (P.card:ℝ) := Nat.cast_pos.mpr hP.card_pos
  apply (mul_le_mul_iff_left₀ (sq_pos_of_pos hPc)).1
  first | (convert hh using 1 <;> ring) | exact (le_of_eq (by ring)).trans (hh.trans (le_of_eq (by ring)))

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Estimates_TwoScaleRatio
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The numerical compatibility of the normalized local factor and the
large-pencil improvement. A large coarse union forces a fine-scale gain. -/
namespace Falconer

theorem two_scale_ratio_bound {x a C F β : ℝ}
    (hx : 0 < x) (ha : 0 ≤ a) (hC : 0 ≤ C) (hF : 1 ≤ F)
    (hβ : 0 < β) (hβ1 : β ≤ 1)
    (hcoarse : x^2 ≤ C*a*x^(1-β)) (hlocal : a ≤ F*x) :
    a^β ≤ C*F^2 := by
  have hF0 : 0 ≤ F := zero_le_one.trans hF
  have hfac : 0 < x*x^(1-β) := mul_pos hx (Real.rpow_pos_of_pos hx _)
  have hxeq : x^β*(x*x^(1-β)) = x^2 := by
    rw [mul_left_comm,← Real.rpow_add hx]
    norm_num
    ring
  have hxp : x^β ≤ C*F := by
    apply (mul_le_mul_iff_left₀ hfac).1
    calc
      x^β*(x*x^(1-β)) = x^2 := hxeq
      _ ≤ C*a*x^(1-β) := hcoarse
      _ ≤ C*(F*x)*x^(1-β) := by gcongr
      _ = (C*F)*(x*x^(1-β)) := by ring
  have hFp : F^β ≤ F := by
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hF hβ1
  calc
    a^β ≤ (F*x)^β := Real.rpow_le_rpow ha hlocal hβ.le
    _ = F^β*x^β := Real.mul_rpow hF0 hx.le
    _ ≤ F*(C*F) := mul_le_mul hFp hxp (Real.rpow_nonneg hx.le _) hF0
    _ = C*F^2 := by ring

theorem normalize_interpolated_incidence {ρ s m B K L A H β : ℝ}
    (hρ : 0 < ρ) (hB : 0 < B) (hm : 0 < m) (hK : 0 ≤ K) (hL : 0 ≤ L)
    (hraw : (m/B)^2 ≤ A*
      (((K*(80*ρ)^s*(L*m))^(1-β)*(25921:ℝ)^β)*H)) :
    (m*ρ^s)^2 ≤
      (B^2*(L*K*80^s)^(1-β)*(25921:ℝ)^β*H)*(A*(ρ^s)^2)*(m*ρ^s)^(1-β) := by
  have hr : 0 < ρ^s := Real.rpow_pos_of_pos hρ _
  have hbase : K*(80*ρ)^s*(L*m) = (L*K*80^s)*(m*ρ^s) := by
    rw [Real.mul_rpow (by norm_num : (0:ℝ) ≤ 80) hρ.le]
    ring
  rw [hbase,Real.mul_rpow (by positivity : 0 ≤ L*K*80^s) (mul_pos hm hr).le] at hraw
  have hh := mul_le_mul_of_nonneg_right hraw (sq_nonneg (B*ρ^s))
  convert hh using 1 <;> first | (with_reducible_and_instances rfl) | (field_simp)

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Estimates_RegularScaleCoefficients
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Polynomial bounds for the two factors in the regular-cell scale
comparison. The exponents leave room for the finite selection losses. -/
namespace Falconer

theorem regular_local_coefficient_bound {D Δ s p : ℝ}
    (hD : 80 ≤ D) (hΔ : 0 < Δ) (_hs : 0 ≤ s) (hs1 : s ≤ 1)
    (hp : 0 ≤ p) (hpD : p ≤ D) :
    ((D*3^s)*(80*Δ)^s*(D/(Δ^s)^2))*(1+(D*3^s)*p) ≤ D^8/Δ^s := by
  have hD1 : 1 ≤ D := by linarith only [hD]
  have hD0 : 0 ≤ D := zero_le_one.trans hD1
  have hΔs : 0 < Δ^s := Real.rpow_pos_of_pos hΔ _
  have h3 : (3:ℝ)^s ≤ D := by
    apply le_trans _ (show (3:ℝ) ≤ D by linarith only [hD])
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le (by norm_num) hs1
  have h80 : (80:ℝ)^s ≤ D := by
    apply le_trans _ hD
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le (by norm_num) hs1
  have hpterm : 1+(D*3^s)*p ≤ D^4 := by
    calc
      _ ≤ 1+(D*D)*D := by gcongr
      _ = 1+D^3 := by ring
      _ ≤ D^4 := by
        have hh : 2 ≤ D := by linarith only [hD]
        have hpow := one_le_pow₀ hD1 (n := 3)
        nlinarith only [mul_le_mul_of_nonneg_right hh (pow_nonneg hD0 3),hpow]
  rw [Real.mul_rpow (by norm_num : (0:ℝ) ≤ 80) hΔ.le]
  calc
    _ ≤ ((D*D)*(D*Δ^s)*(D/(Δ^s)^2))*D^4 := by gcongr
    _ = _ := by field_simp

theorem regular_coarse_coefficient_bound {D s p β : ℝ}
    (hD : 80 ≤ D) (hs : 0 ≤ s) (hs1 : s ≤ 1)
    (hp : 0 ≤ p) (hpD : p ≤ D) (hβ : 0 ≤ β) (hβ1 : β ≤ 1) :
    D^2*(D^2*80^s)^(1-β)*(25921:ℝ)^β*(1+D*p) ≤ D^11 := by
  have hD1 : 1 ≤ D := by linarith only [hD]
  have hD0 : 0 ≤ D := zero_le_one.trans hD1
  have h80 : (80:ℝ)^s ≤ D := by
    apply le_trans _ hD
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le (by norm_num) hs1
  have hbase : 1 ≤ D^2*80^s := by
    have hpow : 1 ≤ (80:ℝ)^s := Real.one_le_rpow (by norm_num) hs
    nlinarith only [one_le_pow₀ hD1 (n := 2),hpow]
  have hfirst : (D^2*80^s)^(1-β) ≤ D^3 := by
    calc
      _ ≤ D^2*80^s := by
        simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le (y := 1-β) (z := 1) hbase (by linarith only [hβ])
      _ ≤ D^2*D := mul_le_mul_of_nonneg_left h80 (sq_nonneg D)
      _ = _ := by ring
  have hsecond : (25921:ℝ)^β ≤ D^3 := by
    calc
      (25921:ℝ)^β ≤ (25921:ℝ) := by
        simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le (by norm_num : (1:ℝ) ≤ 25921) hβ1
      _ ≤ 80^3 := by norm_num
      _ ≤ _ := pow_le_pow_left₀ (by norm_num) hD 3
  have hlast : 1+D*p ≤ D^3 := by
    have hpow := one_le_pow₀ hD1 (n := 2)
    have hh : 2 ≤ D := by linarith only [hD]
    have hp2 : D*p ≤ D^2 := by nlinarith only [mul_le_mul_of_nonneg_left hpD hD0]
    nlinarith only [hp2,hpow,mul_le_mul_of_nonneg_right hh (sq_nonneg D)]
  calc
    _ ≤ D^2*D^3*D^3*D^3 := by gcongr
    _ = _ := by ring

theorem regular_local_ratio_bound {D Δ ρ s p A U m : ℝ}
    (hD : 80 ≤ D) (hΔ : 0 < Δ) (hρ : 0 < ρ) (hρΔ : ρ ≤ Δ)
    (hs : 0 ≤ s) (hs1 : s ≤ 1) (hp : 0 ≤ p) (hpD : p ≤ D)
    (hU : 0 ≤ U) (hm : 0 ≤ m) (hsmall : U ≤ D/(Δ^s)^4)
    (hproduct : (1/(D*(Δ^s)^2))^2*A ≤ 26*U*(D*m)*
      (((D*3^s)*(80*Δ)^s*(D/(Δ^s)^2))*(1+(D*3^s)*p))) :
    A*(ρ^s)^2 ≤ D^13*(m*ρ^s) := by
  have hD0 : 0 < D := by linarith only [hD]
  have hΔs : 0 < Δ^s := Real.rpow_pos_of_pos hΔ _
  have hρs : 0 < ρ^s := Real.rpow_pos_of_pos hρ _
  have hscale : ρ^s ≤ Δ^s := Real.rpow_le_rpow hρ.le hρΔ hs
  have hcoeff := regular_local_coefficient_bound hD hΔ hs hs1 hp hpD
  have hraw : (1/(D*(Δ^s)^2))^2*A ≤ D^11*m/(Δ^s)^5 := by
    calc
      _ ≤ _ := hproduct
      _ ≤ D*U*(D*m)*(D^8/Δ^s) := by gcongr; linarith only [hD]
      _ ≤ D*(D/(Δ^s)^4)*(D*m)*(D^8/Δ^s) := by gcongr
      _ = _ := by field_simp
  have hh := mul_le_mul_of_nonneg_right hraw (sq_nonneg (D*(Δ^s)^2))
  have hA : A ≤ D^13*m/Δ^s := by
    convert hh using 1 <;> first | (with_reducible_and_instances rfl) | (field_simp)
  calc
    A*(ρ^s)^2 ≤ (D^13*m/Δ^s)*(ρ^s)^2 := mul_le_mul_of_nonneg_right hA (sq_nonneg _)
    _ = (D^13*m*ρ^s)*(ρ^s/Δ^s) := by ring
    _ ≤ (D^13*m*ρ^s)*1 := mul_le_mul_of_nonneg_left
      ((div_le_one hΔs).2 hscale) (by positivity)
    _ = _ := by ring

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Estimates_RegularRefinementBound
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A frozen regular refinement with a small fine union cannot have a large
coarse union. This combines the actual local and coarse incidence estimates. -/
namespace Falconer
open scoped BigOperators
attribute [local instance] Classical.propDecidable

theorem regular_refinement_coarse_bound (N k : ℕ) {s t u β D m : ℝ}
    (hN : 3 ≤ N) (hD : 80 ≤ D) (hm : 0 < m)
    (hs : 0 ≤ s) (hs1 : s ≤ 1) (hst : s < t) (hu : 0 ≤ u) (hut : u < t)
    (hβ : 0 < β) (hβ1 : β < 1) (huEq : u = s*(1-β)+2*β)
    (hp : planarPotentialConstant s t ≤ D) (hpu : planarPotentialConstant u t ≤ D)
    (C P U₀ : Finset (Space 2)) (T V G : Space 2 → Finset (Space 2))
    (c : Space 2) (hc : c ∈ C) (hP : P.Nonempty)
    (hCchart : InBoundedLineChart C)
    (hCball : NormalizedFiniteBallBound (1/(2:ℝ)^(N+3)) t D C)
    (hT : ∀ x ∈ C, m/D ≤ ((T x).card:ℝ) ∧ ((T x).card:ℝ) ≤ D*m ∧
      InBoundedLineChart (T x) ∧ FiniteSeparatedAt (1/(2:ℝ)^(N+3)) (T x) ∧
      NormalizedFiniteBallBound (1/(2:ℝ)^(N+3)) s D (T x) ∧
      ∀ l ∈ T x, TubeIncident (1/(2:ℝ)^(N+3)) x l)
    (hcell : ∀ p ∈ P, |p 0-c 0| ≤ (1/(2:ℝ)^N)/4 ∧ |p 1-c 1| ≤ (1/(2:ℝ)^N)/4)
    (hPball : NormalizedFiniteBallBound (1/(2:ℝ)^N) t D
      (P.image (localPacketPoint (1/(2:ℝ)^N) (c 0) (c 1))))
    (hV : ∀ p ∈ P, 1/(D*((1/(2:ℝ)^N)^s)^2) ≤ ((V p).card:ℝ) ∧
      ((V p).card:ℝ) ≤ D/((1/(2:ℝ)^N)^s)^2 ∧
      NormalizedFiniteBallBound ((1/(2:ℝ)^N)^2) s D (V p) ∧
      ∀ l ∈ V p, |l 0| ≤ 1/2 ∧ TubeIncident ((1/(2:ℝ)^N)^2) p l)
    (hcover : ∀ p ∈ P, ∀ l ∈ V p, ∃ a ∈ T c, l ∈ G a)
    (hband : ∀ a ∈ C.biUnion T, 2^k ≤ (G a).card ∧ (G a).card < 2^(k+1))
    (htotal : (∑ a ∈ C.biUnion T, ((G a).card:ℝ)) ≤ 13*(U₀.card:ℝ))
    (hsmall : (U₀.card:ℝ) ≤ D/((1/(2:ℝ)^N)^s)^4) :
    (((C.biUnion T).card:ℝ)*((1/(2:ℝ)^(N+3))^s)^2)^β ≤ D^37 := by
  let Δ := 1/(2:ℝ)^N
  let ρ := 1/(2:ℝ)^(N+3)
  let A : ℝ := (C.biUnion T).card
  let a := A*(ρ^s)^2
  let x := m*ρ^s
  have hΔ : 0 < Δ := by dsimp [Δ]; positivity
  have hρ : 0 < ρ := by dsimp [ρ]; positivity
  have hD1 : 1 ≤ D := by linarith only [hD]
  have hD0 : 0 < D := zero_lt_one.trans_le hD1
  have hρΔ : ρ ≤ Δ := by
    apply one_div_le_one_div_of_le (by positivity)
    exact pow_le_pow_right₀ (by norm_num) (by omega)
  have hpot := planarPotentialConstant_pos hst
  have hpotu := planarPotentialConstant_pos hut
  have hbandR : ∀ b ∈ C.biUnion T, (2:ℝ)^k ≤ ((G b).card:ℝ) ∧
      ((G b).card:ℝ) ≤ 2*(2:ℝ)^k := by
    intro b hb
    constructor
    · exact_mod_cast (hband b hb).1
    · have hh : ((G b).card:ℝ) < (2:ℝ)^(k+1) := by exact_mod_cast (hband b hb).2
      simpa only [pow_succ,mul_comm] using hh.le
  have hlocal := local_cell_packet_scale_combination N hN hs hst hD1
    (by positivity : 0 ≤ 1/(D*(Δ^s)^2)) (mul_pos hD0 hm).le
    (by positivity : 0 ≤ (2:ℝ)^k) (hCchart c hc).1 P (C.biUnion T) (T c) U₀ V G hP
    hcell hPball hV (Finset.subset_biUnion_of_mem T hc) (hT c hc).2.1 hcover hbandR htotal
  have hlocal' : a ≤ D^13*x := by
    exact regular_local_ratio_bound hD hΔ hρ hρΔ hs hs1 hpot.le hp
      (Nat.cast_nonneg _) hm.le hsmall (by
        convert hlocal using 1
        all_goals try with_reducible_and_instances rfl
        simp only [Δ]
        ring)
  have hθ : 0 < 1-β := sub_pos.mpr hβ1
  have hθ1 : 1-β < 1 := by linarith only [hβ]
  have he : s*(1-β)+2*(1-(1-β)) = u := by rw [huEq]; ring
  have hcoarse := planar_interpolated_incidence (N+3) hs hu hut hD1
    (div_pos hm hD0).le hθ hθ1 he C T ⟨c,hc⟩ hCchart hCball hT
  rw [show 1-(1-β) = β by ring] at hcoarse
  have hnorm := normalize_interpolated_incidence hρ hD0 hm hD0.le hD0.le hcoarse
  have hcoef := regular_coarse_coefficient_bound hD hs hs1 hpotu.le hpu hβ.le hβ1.le
  have hcoarse' : x^2 ≤ D^11*a*x^(1-β) := by
    have heq : D*D*80^s = D^2*80^s := by ring
    rw [heq] at hnorm
    exact hnorm.trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hcoef (by positivity))
      (by positivity))
  have hh := two_scale_ratio_bound (by positivity) (by positivity)
    (pow_nonneg hD0.le 11) (one_le_pow₀ hD1 (n := 13)) hβ hβ1.le hcoarse' hlocal'
  calc
    a^β ≤ D^11*(D^13)^2 := hh
    _ = D^37 := by ring

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Estimates_RegularRefinementContradiction
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The regular-set alternative and the normalized scale comparison
exclude a small fine union once the original configuration is refined. -/
namespace Falconer
attribute [local instance] Classical.propDecidable

theorem regular_refinement_contradiction {κ : ℝ} (hκ : 0 < κ) (hκ1 : κ ≤ 1/100) :
    ∃ ε : ℝ, ∃ N₀ : ℕ, 0 < ε ∧ 0 < N₀ ∧
      ∀ n : ℕ, N₀ ≤ n+2 → 3 ≤ n →
      let Δ := 1/(2:ℝ)^n
      let E := Real.exp (ε*((n+2:ℕ):ℝ)*Real.log 2)
      ∀ s t u β D : ℝ, κ ≤ s → s ≤ 1-8*κ → 2*κ ≤ t-s → t ≤ 2 →
        0 ≤ u → u < t → 0 < β → β < 1 → u = s*(1-β)+2*β →
        80 ≤ D → D^2 ≤ E → D^40 < E^β →
        planarPotentialConstant s t ≤ D → planarPotentialConstant u t ≤ D →
      ∀ P : Finset (Space 2), P.Nonempty →
        (∀ p ∈ P, |p 0| ≤ 1/8 ∧ |p 1| ≤ 1/8) →
        FiniteSeparatedAt (Δ^2) P → NormalizedFiniteBallBound (Δ^2) t D P →
        ((P.image (coarsePlanarRound (1/(2:ℝ)^(n+3)))).card:ℝ) ≤ D/Δ^t →
      ∀ V : Space 2 → Finset (Space 2),
        (∀ p ∈ P, InBoundedLineChart (V p) ∧ FiniteSeparatedAt (Δ^2) (V p) ∧
          ∀ l ∈ V p, |l 0| ≤ 1/2 ∧ TubeIncident (Δ^2) p l) →
        RegularRefinementData n s t D P V → ¬ ((P.biUnion V).card:ℝ) ≤ D/(Δ^s)^4 := by
  obtain ⟨ε,N₀,hε,_,hN₀,hmain⟩ := general_regular_coarse_cover_alternative hκ (hκ1.trans (by norm_num))
  refine ⟨ε,N₀,hε,hN₀,?_⟩
  intro n hn hn3
  dsimp only
  intro s t u β D hs hs1 hgap ht hu hut hβ hβ1 huEq hD hDE hpower hp hpu
    P hP hPsmall hPsep hPball hPcover V hV F hsmall
  let Δ := 1/(2:ℝ)^n
  let ρ := 1/(2:ℝ)^(n+3)
  let E := Real.exp (ε*((n+2:ℕ):ℝ)*Real.log 2)
  let Q := F.cells.biUnion F.points
  have hΔ : 0 < Δ := by dsimp [Δ]; positivity
  have hρ : 0 < ρ := by dsimp [ρ]; positivity
  have hD1 : 1 ≤ D := by linarith only [hD]
  have hD0 : 0 < D := zero_lt_one.trans_le hD1
  have hDle : D ≤ E := (by nlinarith only [hD1] : D ≤ D^2).trans hDE
  have hs0 : 0 ≤ s := hκ.le.trans hs
  have hsone : s ≤ 1 := by linarith only [hs1,hκ]
  have hst : s < t := by linarith only [hgap,hκ]
  have hQP : Q ⊆ P := by
    intro p hp
    obtain ⟨c,hc,hp⟩ := Finset.mem_biUnion.mp hp
    exact (Finset.mem_filter.mp ((F.point_data c hc).1 hp)).1
  have hQ : Q.Nonempty := by
    obtain ⟨c,hc⟩ := F.cells_nonempty
    obtain ⟨p,hp⟩ := (F.point_data c hc).2.1
    exact ⟨p,Finset.mem_biUnion.mpr ⟨c,hc,hp⟩⟩
  have mono {d v A B : ℝ} (hd : 0 ≤ d) (hAB : A ≤ B) {S : Finset (Space 2)}
      (hb : NormalizedFiniteBallBound d v A S) : NormalizedFiniteBallBound d v B S := by
    intro z r hr hr1
    exact (hb z r hr hr1).trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hAB (Real.rpow_nonneg (hd.trans hr) _)) (Nat.cast_nonneg _))
  have hQball : NormalizedFiniteBallBound (Δ^2) t E Q := by
    have hb := normalized_finite_ball_bound_subset (sq_nonneg Δ) hD0.le hQP F.point_mass hPball
    exact mono (sq_nonneg Δ) (by simpa only [pow_two] using hDE) hb
  have hQunion : Q.biUnion F.fine ⊆ P.biUnion V := by
    intro l hl
    obtain ⟨p,hp,hl⟩ := Finset.mem_biUnion.mp hl
    obtain ⟨c,hc,hpc⟩ := Finset.mem_biUnion.mp hp
    exact Finset.mem_biUnion.mpr ⟨p,hQP hp,(F.fine_data c hc p hpc).1 hl⟩
  have hAupper : ¬ ((F.cells.biUnion F.pencils).card:ℝ) ≤ E/(13*(ρ^s)^2) := by
    intro hA
    apply hmain n hn s t hs hs1 hgap ht Q hQ (fun p hp => hPsmall p (hQP hp))
      (finiteSeparatedAt_subset hQP hPsep) hQball
    · exact (Nat.cast_le.mpr (Finset.card_le_card (Finset.image_subset_image hQP))).trans
        (hPcover.trans (div_le_div_of_nonneg_right hDle (Real.rpow_nonneg hΔ.le _)))
    · intro p hp
      obtain ⟨c,hc,hpc⟩ := Finset.mem_biUnion.mp hp
      obtain ⟨hsub,hlo,_,hb⟩ := F.fine_data c hc p hpc
      have hpos : 0 < ((F.fine p).card:ℝ) := (by positivity : 0 < 1/(D*(Δ^s)^2)).trans_le hlo
      exact ⟨Finset.card_pos.mp (Nat.cast_pos.mp hpos),
        fun l hl => (hV p (hQP hp)).1 l (hsub hl),
        finiteSeparatedAt_subset hsub (hV p (hQP hp)).2.1,
        mono (sq_nonneg Δ) hDle hb,
        fun l hl => (hV p (hQP hp)).2.2 l (hsub hl)⟩
    · constructor
      · exact (Nat.cast_le.mpr (Finset.card_le_card hQunion)).trans
          (hsmall.trans (div_le_div_of_nonneg_right hDle (pow_nonneg (Real.rpow_nonneg hΔ.le _) _)))
      · apply F.coarse_cover.trans
        have hh := mul_le_mul_of_nonneg_left hA (by norm_num : (0:ℝ) ≤ 13)
        change 13*((F.cells.biUnion F.pencils).card:ℝ) ≤ E/(ρ^s)^2
        exact hh.trans_eq (by field_simp)
  have ha : E/13 ≤ ((F.cells.biUnion F.pencils).card:ℝ)*(ρ^s)^2 := by
    have hh := (div_lt_iff₀ (by positivity : 0 < 13*(ρ^s)^2)).1 (lt_of_not_ge hAupper)
    apply (div_le_iff₀ (by norm_num : (0:ℝ) < 13)).2
    nlinarith only [hh]
  obtain ⟨c,hc⟩ := F.cells_nonempty
  have hbounded := regular_refinement_coarse_bound n F.level hn3 hD F.width_pos hs0 hsone hst
    hu hut hβ hβ1 huEq hp hpu F.cells (F.points c) (P.biUnion V) F.pencils F.fine F.packets c hc
    (F.point_data c hc).2.1 F.cells_chart F.cells_regular F.pencil_data
    (F.point_data c hc).2.2.1 (F.point_data c hc).2.2.2
    (fun p hp => ⟨(F.fine_data c hc p hp).2.1,(F.fine_data c hc p hp).2.2.1,
      (F.fine_data c hc p hp).2.2.2,
      fun l hl => (hV p (Finset.mem_filter.mp ((F.point_data c hc).1 hp)).1).2.2 l
        ((F.fine_data c hc p hp).1 hl)⟩)
    (F.packet_cover c hc) F.packet_band F.packet_sum hsmall
  have hEp : E^β ≤ 13^β*D^37 := by
    have hEE : E ≤ 13*(((F.cells.biUnion F.pencils).card:ℝ)*(ρ^s)^2) :=
      by
        convert (div_le_iff₀ (by norm_num : (0:ℝ) < 13)).1 ha using 1
        all_goals try with_reducible_and_instances rfl
        ring
    calc
      E^β ≤ (13*(((F.cells.biUnion F.pencils).card:ℝ)*(ρ^s)^2))^β :=
        Real.rpow_le_rpow (Real.exp_pos _).le hEE hβ.le
      _ = 13^β*(((F.cells.biUnion F.pencils).card:ℝ)*(ρ^s)^2)^β :=
        Real.mul_rpow (by norm_num) (by positivity)
      _ ≤ _ := mul_le_mul_of_nonneg_left hbounded (by positivity)
  have h13 : (13:ℝ)^β ≤ D := by
    apply le_trans _ (show (13:ℝ) ≤ D by linarith only [hD])
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le
      (by norm_num : (1:ℝ) ≤ 13) hβ1.le
  have hh : E^β ≤ D^40 := calc
    E^β ≤ 13^β*D^37 := hEp
    _ ≤ D*D^37 := mul_le_mul_of_nonneg_right h13 (pow_nonneg hD0.le _)
    _ = D^38 := by ring
    _ ≤ D^40 := pow_le_pow_right₀ hD1 (by norm_num)
  exact (not_lt_of_ge hh) hpower

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Estimates_RegularRefinementPreparation
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Construct the frozen refinement from the original regular point set and
fine pencils. No coarse-cover smallness is used in this preparation. -/
namespace Falconer
open scoped BigOperators
attribute [local instance] Classical.propDecidable

theorem regular_refinement_preparation (n : ℕ) {s t K D : ℝ}
    (hn : 3 ≤ n) (hs : 0 ≤ s) (hs1 : s ≤ 1) (ht : 0 ≤ t) (ht1 : t ≤ 2)
    (hK : 1 ≤ K) (hKD : K ≤ D) (hD : 80 ≤ D)
    (P : Finset (Space 2)) (V : Space 2 → Finset (Space 2)) (hP : P.Nonempty)
    (hPsmall : ∀ p ∈ P, |p 0| ≤ 1/8 ∧ |p 1| ≤ 1/8)
    (hPball : NormalizedFiniteBallBound ((1/(2:ℝ)^n)^2) t K P)
    (hV : ∀ p ∈ P, 1/(D*((1/(2:ℝ)^n)^s)^2) ≤ ((V p).card:ℝ) ∧
      ((V p).card:ℝ) ≤ D/((1/(2:ℝ)^n)^s)^2 ∧
      NormalizedFiniteBallBound ((1/(2:ℝ)^n)^2) s K (V p) ∧
      ∀ l ∈ V p, |l 0| ≤ 1/2 ∧ TubeIncident ((1/(2:ℝ)^n)^2) p l)
    (hJp : (Nat.log 2 P.card+1:ℕ) ≤ D)
    (hJv : (Nat.log 2 (∑ p ∈ P, (V p).card)+1:ℕ) ≤ D)
    (hJall : (Nat.log 2 (13*(P.biUnion V).card)+1:ℕ) ≤ D)
    (hpoint : ((P.image (coarsePlanarRound (1/(2:ℝ)^(n+3)))).card:ℝ) ≤ K/(1/(2:ℝ)^n)^t) :
    Nonempty (RegularRefinementData n s t (D^40) P V) := by
  let Δ := 1/(2:ℝ)^n
  let ρ := 1/(2:ℝ)^(n+3)
  let q := coarsePlanarRound ρ
  let S := fun c => P.filter fun p => q p = c
  let Jp : ℝ := ((Nat.log 2 P.card+1:ℕ):ℝ)
  let Jv : ℝ := ((Nat.log 2 (∑ p ∈ P, (V p).card)+1:ℕ):ℝ)
  have hΔ : 0 < Δ := by dsimp [Δ]; positivity
  have hρ : 0 < ρ := by dsimp [ρ]; positivity
  have hD1 : 1 ≤ D := by linarith only [hD]
  have hD0 : 0 < D := zero_lt_one.trans_le hD1
  have hJpR : Jp ≤ D := hJp
  have hJvR : Jv ≤ D := hJv
  have hK4 : K ≤ D^4 := hKD.trans (by simpa using pow_le_pow_right₀ hD1 (show 1 ≤ 4 by norm_num))
  have mono {δ v A B : ℝ} (hd : 0 ≤ δ) (hAB : A ≤ B) {F : Finset (Space 2)}
      (hb : NormalizedFiniteBallBound δ v A F) : NormalizedFiniteBallBound δ v B F := by
    intro z r hr hr1
    exact (hb z r hr hr1).trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hAB (Real.rpow_nonneg (hd.trans hr) _)) (Nat.cast_nonneg _))
  have hVne (p : Space 2) (hp : p ∈ P) : (V p).Nonempty := by
    have hh : 0 < ((V p).card:ℝ) := (by positivity : 0 < 1/(D*(Δ^s)^2)).trans_le (hV p hp).1
    exact Finset.card_pos.mp (Nat.cast_pos.mp hh)
  obtain ⟨k,C,_,hC,hCsmall,_,hCb,hmass,hcell,T,hT,hTU,hG,hGsum,hGcap⟩ :=
    regular_cell_configuration n hn hs ht ht1 hK P V hP hPsmall hPball
      (fun p hp => ⟨hVne p hp,(hV p hp).2.2.1,(hV p hp).2.2.2⟩) hpoint
  have hCp : 8*K*Jp ≤ D^4 := by
    calc
      _ ≤ 8*D*D := by gcongr
      _ ≤ D*D*D := by gcongr; linarith only [hD]
      _ = D^3 := by ring
      _ ≤ D^4 := pow_le_pow_right₀ hD1 (by norm_num)
  have hCl : 2*K*Jp*K ≤ D^4 := by
    calc
      _ ≤ 2*D*D*D := by gcongr
      _ ≤ D*D*D*D := by gcongr; linarith only [hD]
      _ = _ := by ring
  have h7 : (7:ℝ)^s ≤ 7 := by
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le (by norm_num) hs1
  have hCt : 2*(K*7^s)*Jv ≤ D^4 := by
    calc
      _ ≤ 2*(D*7)*D := by gcongr
      _ = 14*D*D := by ring
      _ ≤ D*D*D := by gcongr; linarith only [hD]
      _ = D^3 := by ring
      _ ≤ D^4 := pow_le_pow_right₀ hD1 (by norm_num)
  have hTcard : (C.biUnion T).card ≤ 13*(P.biUnion V).card := by
    have hh := hTU.trans (mul_le_mul_of_nonneg_left
      (show (((P.biUnion V).image q).card:ℝ) ≤ ((P.biUnion V).card:ℝ) by
        exact_mod_cast Finset.card_image_le) (by norm_num : (0:ℝ) ≤ 13))
    exact_mod_cast hh
  have hJc : (Nat.log 2 (C.biUnion T).card+1:ℕ) ≤ D :=
    (Nat.cast_le.mpr (Nat.add_le_add_right (Nat.log_mono_right hTcard) 1)).trans hJall
  have hJg : (Nat.log 2 (P.biUnion V).card+1:ℕ) ≤ D :=
    (Nat.cast_le.mpr (Nat.add_le_add_right (Nat.log_mono_right
      (show (P.biUnion V).card ≤ 13*(P.biUnion V).card by omega)) 1)).trans hJall
  apply build_regular_refinement n k hn hD P C V T
    (fineCoarsePacket ρ C (fun c => (S c).biUnion V)) hC
    (fun c hc => ⟨(hCsmall c hc).1.trans (by norm_num),(hCsmall c hc).2.trans (by norm_num)⟩)
    (mono (sq_nonneg Δ) hK4 hPball) (mono hρ.le hCp hCb) hJp hJv hJc hJg hmass
  · intro c hc
    exact ⟨(hcell c hc).1,(hcell c hc).2.1,(hcell c hc).2.2.1,(hcell c hc).2.2.2.1,
      mono hΔ.le hCl (hcell c hc).2.2.2.2⟩
  · intro p hp
    exact ⟨(hV p hp).1,(hV p hp).2.1,mono (sq_nonneg Δ) hK4 (hV p hp).2.2.1,(hV p hp).2.2.2⟩
  · intro c hc
    exact ⟨(hT c hc).1,(hT c hc).2.1,(hT c hc).2.2.1,
      mono hρ.le hCt (hT c hc).2.2.2.1,(hT c hc).2.2.2.2⟩
  · exact hG
  · exact hGsum
  · exact hGcap

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Estimates_RegularFineGain
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Fine-scale growth for a regular point set. The frozen refinement and
all its numerical budgets are obtained from the original configuration. -/
namespace Falconer
open scoped BigOperators
attribute [local instance] Classical.propDecidable

theorem regular_fine_gain {κ : ℝ} (hκ : 0 < κ) (hκ1 : κ ≤ 1/100) :
    ∃ ε : ℝ, ∃ N0 : ℕ, 0 < ε ∧ ε ≤ 1 ∧ 0 < N0 ∧ ∀ n : ℕ, N0 ≤ n+2 →
      let Δ := 1/(2:ℝ)^n
      let ρ := 1/(2:ℝ)^(n+3)
      let K := Real.exp (ε*((n+2:ℕ):ℝ)*Real.log 2)
      ∀ s t : ℝ, κ ≤ s → s ≤ 1-8*κ → 2*κ ≤ t-s → t ≤ 2 →
      ∀ P : Finset (Space 2), P.Nonempty →
        (∀ p ∈ P, |p 0| ≤ 1/8 ∧ |p 1| ≤ 1/8) →
        FiniteSeparatedAt (Δ^2) P → NormalizedFiniteBallBound (Δ^2) t K P →
        ((P.image (coarsePlanarRound ρ)).card:ℝ) ≤ K/Δ^t →
      ∀ V : Space 2 → Finset (Space 2),
        (∀ p ∈ P, InBoundedLineChart (V p) ∧ FiniteSeparatedAt (Δ^2) (V p) ∧
          NormalizedFiniteBallBound (Δ^2) s K (V p) ∧
          1/(K*(Δ^s)^2) ≤ ((V p).card:ℝ) ∧ ((V p).card:ℝ) ≤ K/(Δ^s)^2 ∧
          ∀ l ∈ V p, |l 0| ≤ 1/2 ∧ TubeIncident (Δ^2) p l) →
        ¬ ((P.biUnion V).card:ℝ) ≤ K/(Δ^s)^4 := by
  obtain ⟨η,N1,hη,hN1,hfalse⟩ := regular_refinement_contradiction hκ hκ1
  let β := κ/4
  have hβ : 0 < β := by dsimp [β]; positivity
  have hβ1 : β < 1 := by dsimp [β]; linarith only [hκ1]
  let θ := η*β/80
  have hθ : 0 < θ := by dsimp [θ]; positivity
  obtain ⟨ε,N2,hε,hε1,_,hreserve⟩ := regular_packet_scale_budget hκ hθ
  refine ⟨ε,max N1 N2,hε,hε1,lt_of_lt_of_le hN1 (le_max_left _ _),?_⟩
  intro n hn
  dsimp only
  intro s t hs hs1 hgap ht P hP hPsmall hPsep hPball hpoint V hV hsmall
  let Δ := 1/(2:ℝ)^n
  let ρ := 1/(2:ℝ)^(n+3)
  let K := Real.exp (ε*((n+2:ℕ):ℝ)*Real.log 2)
  let D := K^2
  let B := D^40
  let E := Real.exp (η*((n+2:ℕ):ℝ)*Real.log 2)
  let u := s*(1-β)+2*β
  obtain ⟨hn3,hD80,hHD,_,_,hdepth,hDB⟩ := hreserve n ((le_max_right _ _).trans hn)
  have hΔ : 0 < Δ := by dsimp [Δ]; positivity
  have hK0 : 0 < K := Real.exp_pos _
  have hK1 : 1 ≤ K := Real.one_le_exp_iff.mpr (by positivity)
  have hKD : K ≤ D := by change K ≤ K^2; nlinarith only [mul_le_mul_of_nonneg_right hK1 hK0.le]
  have hD1 : 1 ≤ D := by linarith only [hD80]
  have hDB' : D ≤ B := by simpa only [pow_one] using pow_le_pow_right₀ hD1 (show 1 ≤ 40 by norm_num)
  have hKB : K ≤ B := hKD.trans hDB'
  have hB80 : 80 ≤ B := hD80.trans hDB'
  have hs0 : 0 ≤ s := hκ.le.trans hs
  have hsone : s ≤ 1 := by linarith only [hs1,hκ]
  have hst : s < t := by linarith only [hgap,hκ]
  have ht0 : 0 ≤ t := hs0.trans hst.le
  have hu0 : 0 ≤ u := by dsimp [u]; positivity
  have hu1 : u ≤ 1 := by
    have hh := mul_le_mul_of_nonneg_right hs1 (show 0 ≤ 1-β by linarith only [hβ1])
    dsimp [u,β] at hh ⊢
    nlinarith only [hh,hκ,hκ1,sq_nonneg κ]
  have hgu : κ ≤ t-u := by
    have hh := mul_nonneg hs0 hβ.le
    dsimp [u,β] at hh ⊢
    nlinarith only [hgap,hκ,hh]
  have hut : u < t := by linarith only [hgu,hκ]
  have hp : planarPotentialConstant s t ≤ B :=
    (planarPotentialConstant_gap hκ hsone (by linarith only [hgap,hκ])).trans (hHD.trans hDB')
  have hpu : planarPotentialConstant u t ≤ B :=
    (planarPotentialConstant_gap hκ hu1 hgu).trans (hHD.trans hDB')
  have hN : 0 < ((n+2:ℕ):ℝ)*Real.log 2 := mul_pos (by positivity) (Real.log_pos (by norm_num))
  have hB2 : B^2 ≤ E := by
    calc
      B^2 ≤ (Real.exp (θ*((n+2:ℕ):ℝ)*Real.log 2))^2 := pow_le_pow_left₀ (by positivity) hDB _
      _ = Real.exp (2*(θ*((n+2:ℕ):ℝ)*Real.log 2)) := (Real.exp_nat_mul _ 2).symm
      _ ≤ E := by
        apply Real.exp_le_exp.mpr
        have hh : 2*θ ≤ η := by dsimp [θ]; nlinarith only [hη,hβ1]
        nlinarith only [mul_le_mul_of_nonneg_right hh hN.le]
  have hB40 : B^40 < E^β := by
    calc
      B^40 ≤ (Real.exp (θ*((n+2:ℕ):ℝ)*Real.log 2))^40 := pow_le_pow_left₀ (by positivity) hDB _
      _ = Real.exp (40*(θ*((n+2:ℕ):ℝ)*Real.log 2)) := (Real.exp_nat_mul _ 40).symm
      _ < Real.exp ((η*((n+2:ℕ):ℝ)*Real.log 2)*β) := by
        apply Real.exp_lt_exp.mpr
        have hh : 40*θ < η*β := by dsimp [θ]; nlinarith only [mul_pos hη hβ]
        nlinarith only [mul_lt_mul_of_pos_right hh hN]
      _ = E^β := Real.exp_mul _ _
  have hdepth' : 10*((n:ℝ)+2) ≤ D := by
    change 10*((n+2:ℕ):ℝ) ≤ D at hdepth
    simpa only [Nat.cast_add,Nat.cast_ofNat] using hdepth
  have hn0 : 0 ≤ (n:ℝ) := Nat.cast_nonneg _
  have hPchart : InBoundedLineChart P := fun p hp =>
    ⟨(hPsmall p hp).1.trans (by norm_num),(hPsmall p hp).2.trans (by norm_num)⟩
  obtain ⟨hJp,_,hJv⟩ := small_union_selection_logs n hε1 hsone P V hPchart hPsep hsmall
  have hJpD : (Nat.log 2 P.card+1:ℕ) ≤ D :=
    (Nat.cast_le.mpr hJp).trans (by push_cast; linarith only [hdepth',hn0])
  have hJvD : (Nat.log 2 (∑ p ∈ P, (V p).card)+1:ℕ) ≤ D :=
    (Nat.cast_le.mpr hJv).trans (by push_cast; linarith only [hdepth',hn0])
  have hUpow : 13*(P.biUnion V).card ≤ 2^(5*n+6) := by
    have hh := small_union_card_dyadic n hε1 hsone (P.biUnion V).card hsmall
    calc
      _ ≤ 13*2^(5*n+2) := Nat.mul_le_mul_left _ hh
      _ ≤ 16*2^(5*n+2) := Nat.mul_le_mul_right _ (by norm_num)
      _ = _ := by rw [show 5*n+6 = (5*n+2)+4 by omega,pow_add]; norm_num; ring
  have hJall : (Nat.log 2 (13*(P.biUnion V).card)+1:ℕ) ≤ D := by
    have hh := packet_log_of_card_bound hUpow
    exact (Nat.cast_le.mpr hh).trans (by push_cast; linarith only [hdepth',hn0])
  obtain ⟨F⟩ := regular_refinement_preparation n hn3 hs0 hsone ht0 ht hK1 hKD hD80 P V hP hPsmall hPball
    (fun p hp => ⟨(div_le_div_of_nonneg_left (by norm_num) (by positivity)
      (mul_le_mul_of_nonneg_right hKD (sq_nonneg _))).trans (hV p hp).2.2.2.1,
      (hV p hp).2.2.2.2.1.trans (div_le_div_of_nonneg_right hKD (sq_nonneg _)),
      (hV p hp).2.2.1,(hV p hp).2.2.2.2.2⟩) hJpD hJvD hJall hpoint
  have hPballB : NormalizedFiniteBallBound (Δ^2) t B P := by
    intro z r hr hr1
    exact (hPball z r hr hr1).trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hKB (Real.rpow_nonneg ((sq_nonneg Δ).trans hr) _))
      (Nat.cast_nonneg _))
  exact hfalse n ((le_max_left _ _).trans hn) hn3 s t u β B hs hs1 hgap ht
    hu0 hut hβ hβ1 rfl hB80 hB2 hB40 hp hpu P hP hPsmall hPsep hPballB
    (hpoint.trans (div_le_div_of_nonneg_right hKB (Real.rpow_nonneg hΔ.le _))) V
    (fun p hp => ⟨(hV p hp).1,(hV p hp).2.1,(hV p hp).2.2.2.2.2⟩) F
    (hsmall.trans (div_le_div_of_nonneg_right hKB (pow_nonneg (Real.rpow_nonneg hΔ.le _) _)))

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Estimates_GeneralRegularFineGain
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Remove the auxiliary fine-pencil cardinality normalization from the
fine-scale regular-set gain by selecting comparable original pencils. -/
namespace Falconer
attribute [local instance] Classical.propDecidable

theorem general_regular_fine_gain {κ : ℝ} (hκ : 0 < κ) (hκ1 : κ ≤ 1/100) :
    ∃ ε : ℝ, ∃ N0 : ℕ, 0 < ε ∧ ε ≤ 1 ∧ 0 < N0 ∧ ∀ n : ℕ, N0 ≤ n+2 →
      let Δ := 1/(2:ℝ)^n
      let ρ := 1/(2:ℝ)^(n+3)
      let K := Real.exp (ε*((n+2:ℕ):ℝ)*Real.log 2)
      ∀ s t : ℝ, κ ≤ s → s ≤ 1-8*κ → 2*κ ≤ t-s → t ≤ 2 →
      ∀ P : Finset (Space 2), P.Nonempty →
        (∀ p ∈ P, |p 0| ≤ 1/8 ∧ |p 1| ≤ 1/8) →
        FiniteSeparatedAt (Δ^2) P → NormalizedFiniteBallBound (Δ^2) t K P →
        ((P.image (coarsePlanarRound ρ)).card:ℝ) ≤ K/Δ^t →
      ∀ V : Space 2 → Finset (Space 2),
        (∀ p ∈ P, (V p).Nonempty ∧ InBoundedLineChart (V p) ∧
          FiniteSeparatedAt (Δ^2) (V p) ∧ NormalizedFiniteBallBound (Δ^2) s K (V p) ∧
          ∀ l ∈ V p, |l 0| ≤ 1/2 ∧ TubeIncident (Δ^2) p l) →
        ¬ ((P.biUnion V).card:ℝ) ≤ K/(Δ^s)^4 := by
  obtain ⟨θ,N1,hθ,_,hN1,hmain⟩ := regular_fine_gain hκ hκ1
  obtain ⟨ε,N2,hε,hε1,hN2,hreserve⟩ := regular_packet_scale_budget hκ hθ
  refine ⟨ε,max N1 N2,hε,hε1,lt_of_lt_of_le hN1 (le_max_left _ _),?_⟩
  intro n hn
  dsimp only
  intro s t hs hs1 hgap ht P hP hPsmall hPsep hPball hpoint V hV hsmall
  let Δ := 1/(2:ℝ)^n
  let ρ := 1/(2:ℝ)^(n+3)
  let δ := 1/(2:ℝ)^(2*n)
  let K := Real.exp (ε*((n+2:ℕ):ℝ)*Real.log 2)
  let D := K^2
  let E := Real.exp (θ*((n+2:ℕ):ℝ)*Real.log 2)
  obtain ⟨_,hD80,hHD,_,_,hdepth,hDE⟩ := hreserve n ((le_max_right _ _).trans hn)
  have hΔ : 0 < Δ := by dsimp [Δ]; positivity
  have hδ : δ = Δ^2 := by
    dsimp [δ,Δ]
    rw [show 2*n = n*2 by omega,pow_mul,div_pow,one_pow]
  have hδ0 : 0 < δ := by dsimp [δ]; positivity
  have hδs : δ^s = (Δ^s)^2 := by
    rw [hδ,← Real.rpow_natCast_mul hΔ.le 2 s]
    norm_num only [Nat.cast_ofNat]
    rw [show (2:ℝ)*s = s*2 by ring]
    simpa only [Nat.cast_ofNat] using Real.rpow_mul_natCast hΔ.le s 2
  have hδs2 : (δ^s)^2 = (Δ^s)^4 := by rw [hδs]; ring
  have hK0 : 0 < K := Real.exp_pos _
  have hK1 : 1 ≤ K := Real.one_le_exp_iff.mpr (by positivity)
  have hD1 : 1 ≤ D := by change 1 ≤ K^2; exact one_le_pow₀ hK1
  have hD0 : 0 ≤ D := zero_le_one.trans hD1
  have hKD : K ≤ D := by change K ≤ K^2; nlinarith only [mul_le_mul_of_nonneg_right hK1 hK0.le]
  have powE (a : ℕ) (ha : a ≤ 40) : D^a ≤ E := (pow_le_pow_right₀ hD1 ha).trans hDE
  have hKE : K ≤ E := hKD.trans (by simpa only [pow_one] using powE 1 (by norm_num))
  have hs0 : 0 ≤ s := hκ.le.trans hs
  have hsone : s ≤ 1 := by linarith only [hs1,hκ]
  have hge : κ ≤ t-s := by linarith only [hgap,hκ]
  have hPchart : InBoundedLineChart P := fun p hp =>
    ⟨(hPsmall p hp).1.trans (by norm_num),(hPsmall p hp).2.trans (by norm_num)⟩
  have hlog : (Nat.log 2 (P.biUnion V).card+1:ℕ) ≤ D := by
    have hh := (small_union_selection_logs n hε1 hsone P V hPchart hPsep hsmall).2.1
    have hd : 10*((n:ℝ)+2) ≤ D := by
      change 10*((n+2:ℕ):ℝ) ≤ D at hdepth
      simpa only [Nat.cast_add,Nat.cast_ofNat] using hdepth
    exact (Nat.cast_le.mpr hh).trans (by push_cast; have := Nat.cast_nonneg (α := ℝ) n; linarith only [hd,this])
  have hunion : ((P.biUnion V).card:ℝ) ≤ D/(δ^s)^2 := by
    rw [hδs2]
    exact hsmall.trans (div_le_div_of_nonneg_right hKD (pow_nonneg (Real.rpow_nonneg hΔ.le _) _))
  have hPballδ : NormalizedFiniteBallBound δ t K P := by rw [hδ]; exact hPball
  have hVδ (p : Space 2) (hp : p ∈ P) : (V p).Nonempty ∧ InBoundedLineChart (V p) ∧
      NormalizedFiniteBallBound δ s K (V p) ∧ ∀ l ∈ V p, TubeIncident δ p l := by
    rw [hδ]
    exact ⟨(hV p hp).1,(hV p hp).2.1,(hV p hp).2.2.2.1,
      fun l hl => ((hV p hp).2.2.2.2 l hl).2⟩
  obtain ⟨k,R,hRP,hR,_,hRball,hlo,hup,hband⟩ := uniform_packet_bounds (2*n) hκ hs0 hsone hge
    hK1 hKD hD80 hHD P V hP hPchart hPballδ hVδ hunion hlog
  have hRU : R.biUnion V ⊆ P.biUnion V := Finset.biUnion_subset_biUnion_of_subset_left V hRP
  have mono_ball {d u A B : ℝ} (hd : 0 ≤ d) (hAB : A ≤ B) {F : Finset (Space 2)}
      (hb : NormalizedFiniteBallBound d u A F) : NormalizedFiniteBallBound d u B F := by
    intro z r hr hr1
    exact (hb z r hr hr1).trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hAB (Real.rpow_nonneg (hd.trans hr) _)) (Nat.cast_nonneg _))
  have hRball' : NormalizedFiniteBallBound (Δ^2) t E R := by
    rw [← hδ]
    exact mono_ball hδ0.le (powE 2 (by norm_num)) hRball
  refine hmain n ((le_max_left _ _).trans hn) s t hs hs1 hgap ht R hR
    (fun p hp => hPsmall p (hRP hp)) (finiteSeparatedAt_subset hRP hPsep) hRball' ?_ V ?_ ?_
  · calc
      _ ≤ ((P.image (coarsePlanarRound ρ)).card:ℝ) := Nat.cast_le.mpr (Finset.card_le_card (Finset.image_subset_image hRP))
      _ ≤ K/Δ^t := hpoint
      _ ≤ _ := div_le_div_of_nonneg_right hKE (Real.rpow_nonneg hΔ.le _)
  · intro p hp
    have htube := hV p (hRP hp)
    refine ⟨htube.2.1,htube.2.2.1,mono_ball (sq_nonneg Δ) hKE htube.2.2.2.1,?_,?_,htube.2.2.2.2⟩
    · have hc := (hband p hp).1
      have hl : 1/(E*δ^s) ≤ (2:ℝ)^k := by
        apply le_trans _ hlo
        exact div_le_div_of_nonneg_left (by norm_num) (by positivity)
          (mul_le_mul_of_nonneg_right (powE 2 (by norm_num)) (Real.rpow_nonneg hδ0.le _))
      rw [hδs] at hl
      exact hl.trans hc
    · have hu : 2*(2:ℝ)^k ≤ E/δ^s := by
        calc
          _ ≤ 2*(D^9/δ^s) := mul_le_mul_of_nonneg_left hup (by norm_num)
          _ ≤ D^10/δ^s := by
            rw [← mul_div_assoc]
            apply div_le_div_of_nonneg_right _ (Real.rpow_nonneg hδ0.le _)
            calc
              _ ≤ D*D^9 := mul_le_mul_of_nonneg_right (by linarith only [hD80]) (pow_nonneg hD0 _)
              _ = _ := by ring
          _ ≤ _ := div_le_div_of_nonneg_right (powE 10 (by norm_num)) (Real.rpow_nonneg hδ0.le _)
      rw [hδs] at hu
      exact (hband p hp).2.trans hu
  · exact (Nat.cast_le.mpr (Finset.card_le_card hRU)).trans
      (hsmall.trans (div_le_div_of_nonneg_right hKE (pow_nonneg (Real.rpow_nonneg hΔ.le _) _)))

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Geometry_ChartGainBudget
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The fixed chart costs fit in the reserved weak exponent after a
single dyadic shift. -/
namespace Falconer

theorem chart_gain_budget {θ : ℝ} (hθ : 0 < θ) :
    ∃ ε : ℝ, ∃ N0 : ℕ, 0 < ε ∧ ε ≤ 1 ∧ 0 < N0 ∧ ∀ n : ℕ, N0 ≤ n+2 →
      400*Real.exp (ε*((n+2:ℕ):ℝ)*Real.log 2) ≤
        Real.exp (θ*((n+3:ℕ):ℝ)*Real.log 2) := by
  let ε := min (θ/2) 1
  have hε : 0 < ε := lt_min (by positivity) zero_lt_one
  obtain ⟨N0,hN0,hpoly⟩ := dyadic_quadratic_loss (by positivity : 0 < θ/2)
    (by norm_num : (0:ℝ) ≤ 400)
  refine ⟨ε,N0,hε,min_le_right _ _,hN0,?_⟩
  intro n hn
  have hN : 0 ≤ ((n+2:ℕ):ℝ) := Nat.cast_nonneg _
  have hsq : (1:ℝ) ≤ (((n+2:ℕ):ℝ)+1)^2 := one_le_pow₀ (by linarith only [hN])
  have h400 : (400:ℝ) ≤ Real.exp ((θ/2)*((n+2:ℕ):ℝ)*Real.log 2) :=
    (by nlinarith only [hsq] : (400:ℝ) ≤ 400*(((n+2:ℕ):ℝ)+1)^2).trans (hpoly (n+2) hn)
  have hexp : Real.exp (ε*((n+2:ℕ):ℝ)*Real.log 2) ≤
      Real.exp ((θ/2)*((n+2:ℕ):ℝ)*Real.log 2) := by
    apply Real.exp_le_exp.mpr
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (min_le_left _ _) hN)
      (Real.log_nonneg (by norm_num : (1:ℝ) ≤ 2))
  calc
    _ ≤ Real.exp ((θ/2)*((n+2:ℕ):ℝ)*Real.log 2)*
        Real.exp ((θ/2)*((n+2:ℕ):ℝ)*Real.log 2) :=
      mul_le_mul h400 hexp (Real.exp_pos _).le (Real.exp_pos _).le
    _ = Real.exp (θ*((n+2:ℕ):ℝ)*Real.log 2) := by rw [← Real.exp_add]; congr 1; ring
    _ ≤ _ := by
      apply Real.exp_le_exp.mpr
      have hlog : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
      have hstep : ((n+2:ℕ):ℝ) ≤ ((n+3:ℕ):ℝ) := by exact_mod_cast (by omega : n+2 ≤ n+3)
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hstep hθ.le) hlog

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Incidence_QuarterPencilGeometry
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A fixed point contraction and its exact line map. This preserves the
original incidence witnesses and the dyadic scale needed by regular gain. -/
namespace Falconer
attribute [local instance] Classical.propDecidable

theorem unlocalCellLine_four_dist (l m : Space 2) :
    dist (unlocalCellLine 4 0 0 l) (unlocalCellLine 4 0 0 m) ≤ 4*dist l m := by
  have h := EuclideanSpace.dist_sq_eq l m
  have h' := EuclideanSpace.dist_sq_eq (unlocalCellLine 4 0 0 l) (unlocalCellLine 4 0 0 m)
  simp only [Fin.sum_univ_two,Real.dist_eq,sq_abs] at h h'
  change dist (unlocalCellLine 4 0 0 l) (unlocalCellLine 4 0 0 m)^2 =
    (l 0-m 0)^2+((4*l 1-l 0*0+0)-(4*m 1-m 0*0+0))^2 at h'
  nlinarith [sq_nonneg (l 0-m 0),dist_nonneg (x := l) (y := m),
    dist_nonneg (x := unlocalCellLine 4 0 0 l) (y := unlocalCellLine 4 0 0 m)]

theorem localCellLine_four_separated {δ : ℝ} (T : Finset (Space 2))
    (hT : FiniteSeparatedAt δ T) :
    FiniteSeparatedAt (δ/4) (T.image (localCellLine 4 0 0)) := by
  intro l hl m hm hlm
  obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp hl
  obtain ⟨b,hb,rfl⟩ := Finset.mem_image.mp hm
  have hsep := hT a ha b hb (fun he => hlm (congrArg (localCellLine 4 0 0) he))
  have hd := unlocalCellLine_four_dist (localCellLine 4 0 0 a) (localCellLine 4 0 0 b)
  rw [localCellLine_leftInverse (by norm_num) 0 0 a,
    localCellLine_leftInverse (by norm_num) 0 0 b] at hd
  linarith

theorem localCellLine_four_regular {δ s K : ℝ} (hδ : 0 < δ)
    (hs : 0 ≤ s) (hK : 1 ≤ K) (T : Finset (Space 2))
    (hT : NormalizedFiniteBallBound δ s K T) :
    NormalizedFiniteBallBound (δ/4) s (K*4^s) (T.image (localCellLine 4 0 0)) := by
  intro z r hr _
  have hr0 : 0 < r := (by linarith : 0 < δ/4).trans_le hr
  let w := unlocalCellLine 4 0 0 z
  have hsub : (T.image (localCellLine 4 0 0)).filter (fun l => dist l z ≤ r) ⊆
      (T.filter (fun l => dist l w ≤ 4*r)).image (localCellLine 4 0 0) := by
    intro l hl
    obtain ⟨hl,hlr⟩ := Finset.mem_filter.mp hl
    obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp hl
    refine Finset.mem_image.mpr ⟨a,Finset.mem_filter.mpr ⟨ha,?_⟩,rfl⟩
    have hh := unlocalCellLine_four_dist (localCellLine 4 0 0 a) z
    rw [localCellLine_leftInverse (by norm_num) 0 0 a] at hh
    exact hh.trans (mul_le_mul_of_nonneg_left hlr (by norm_num))
  rw [Finset.card_image_of_injective _ (localCellLine_injective (by norm_num) 0 0)]
  calc
    _ ≤ ((T.filter (fun l => dist l w ≤ 4*r)).card:ℝ) :=
      Nat.cast_le.mpr ((Finset.card_le_card hsub).trans Finset.card_image_le)
    _ ≤ K*(4*r)^s*(T.card:ℝ) := normalized_ball_bound_all_radii hs hK hT w (4*r)
      (by linarith only [hr])
    _ = _ := by rw [Real.mul_rpow (by norm_num : (0:ℝ) ≤ 4) hr0.le]; ring

theorem planarQuarter_eq_local (p : Space 2) : planarQuarter p = localPacketPoint 4 0 0 p := by
  ext i
  fin_cases i <;> simp [planarQuarter_apply,localPacketPoint]

theorem planarQuarter_incident {δ : ℝ} {p l : Space 2} (h : TubeIncident δ p l) :
    TubeIncident (δ/4) (planarQuarter p) (localCellLine 4 0 0 l) := by
  rw [planarQuarter_eq_local]
  exact localCellLine_incident (by norm_num) 0 0 p l h

theorem localCellLine_four_chart (T : Finset (Space 2)) (hT : InBoundedLineChart T) :
    InBoundedLineChart (T.image (localCellLine 4 0 0)) := by
  intro l hl
  obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp hl
  constructor
  · exact (hT a ha).1
  · change |(a 0*0+a 1-0)/(4:ℝ)| ≤ 1
    rw [abs_div]
    norm_num only [mul_zero,zero_add,sub_zero,abs_of_pos (by norm_num : (0:ℝ) < 4)]
    linarith only [(hT a ha).2]

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Geometry_QuarterCoarseCover
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A fixed contraction changes the actual rounded point cover by at most
25 per original grid cell. No covering hypothesis is added. -/
namespace Falconer
open scoped BigOperators
attribute [local instance] Classical.propDecidable

theorem planarQuarter_coarse_cover {ρ : ℝ} (hρ : 0 < ρ) (P : Finset (Space 2)) :
    (((P.image planarQuarter).image (coarsePlanarRound (ρ/2))).card:ℝ) ≤
      25*((P.image (coarsePlanarRound ρ)).card:ℝ) := by
  let C := P.image (coarsePlanarRound ρ)
  let S := fun c => P.filter fun p => coarsePlanarRound ρ p = c
  let A := fun c => ((S c).image planarQuarter).image (coarsePlanarRound (ρ/2))
  have hρ' : 0 < ρ/2 := by positivity
  have hA (c : Space 2) (_hc : c ∈ C) : ((A c).card:ℝ) ≤ 25 := by
    have hwithin : ∀ z ∈ A c, dist z (planarQuarter c) ≤ 2*(ρ/2) := by
      intro z hz
      obtain ⟨v,hv,rfl⟩ := Finset.mem_image.mp hz
      obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp hv
      have hpc := (Finset.mem_filter.mp hp).2
      have hd := coarsePlanarRound_near hρ p
      rw [hpc] at hd
      have hquarter : dist (planarQuarter p) (planarQuarter c) ≤ ρ/4 := by
        rw [planarQuarter_dist]
        exact div_le_div_of_nonneg_right hd (by norm_num)
      have hnear := coarsePlanarRound_near hρ' (planarQuarter p)
      rw [dist_comm] at hnear
      have htri := dist_triangle (coarsePlanarRound (ρ/2) (planarQuarter p))
        (planarQuarter p) (planarQuarter c)
      linarith
    have hh := separated_ball_card (A c) (planarQuarter c) hρ'
      (r := 2*(ρ/2)) (by positivity)
      (coarsePlanarRound_separated hρ' ((S c).image planarQuarter)) hwithin
    have he : (2*(2*(ρ/2))/(ρ/2)+1)^2 = (25:ℝ) := by field_simp; ring
    rwa [he] at hh
  have hcover : (P.image planarQuarter).image (coarsePlanarRound (ρ/2)) ⊆ C.biUnion A := by
    intro z hz
    obtain ⟨v,hv,rfl⟩ := Finset.mem_image.mp hz
    obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp hv
    refine Finset.mem_biUnion.mpr ⟨coarsePlanarRound ρ p,Finset.mem_image_of_mem _ hp,?_⟩
    exact Finset.mem_image_of_mem _ (Finset.mem_image_of_mem _ (Finset.mem_filter.mpr ⟨hp,rfl⟩))
  calc
    _ ≤ ((C.biUnion A).card:ℝ) := Nat.cast_le.mpr (Finset.card_le_card hcover)
    _ ≤ ∑ c ∈ C, ((A c).card:ℝ) := by exact_mod_cast Finset.card_biUnion_le
    _ ≤ ∑ _c ∈ C, (25:ℝ) := Finset.sum_le_sum hA
    _ = _ := by simp; ring

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Incidence_QuarterPencils
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact transport of a finite pencil family under the fixed contraction. -/
namespace Falconer
attribute [local instance] Classical.propDecidable

theorem planarQuarter_left_inverse (p : Space 2) : (4:ℝ) • planarQuarter p = p := by
  rw [planarQuarter,smul_smul]
  norm_num

theorem quarterPencils_at (V : Space 2 → Finset (Space 2)) (p : Space 2) :
    quarterPencils V (planarQuarter p) = (V p).image (localCellLine 4 0 0) := by
  rw [quarterPencils,planarQuarter_left_inverse]

theorem quarterPencils_union (P : Finset (Space 2)) (V : Space 2 → Finset (Space 2)) :
    (P.image planarQuarter).biUnion (quarterPencils V) =
      (P.biUnion V).image (localCellLine 4 0 0) := by
  ext l
  constructor
  · intro hl
    obtain ⟨z,hz,hl⟩ := Finset.mem_biUnion.mp hl
    obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp hz
    rw [quarterPencils_at] at hl
    obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp hl
    exact Finset.mem_image_of_mem _ (Finset.mem_biUnion.mpr ⟨p,hp,ha⟩)
  · intro hl
    obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp hl
    obtain ⟨p,hp,ha⟩ := Finset.mem_biUnion.mp ha
    refine Finset.mem_biUnion.mpr ⟨planarQuarter p,Finset.mem_image_of_mem _ hp,?_⟩
    rw [quarterPencils_at]
    exact Finset.mem_image_of_mem _ ha

theorem quarterPencils_union_card (P : Finset (Space 2)) (V : Space 2 → Finset (Space 2)) :
    ((P.image planarQuarter).biUnion (quarterPencils V)).card = (P.biUnion V).card := by
  rw [quarterPencils_union,Finset.card_image_of_injective _ (localCellLine_injective (by norm_num) 0 0)]

theorem quarterPencils_data {δ s K : ℝ} (hδ : 0 < δ) (hs : 0 ≤ s) (hK : 1 ≤ K)
    (P : Finset (Space 2)) (V : Space 2 → Finset (Space 2))
    (hV : ∀ p ∈ P, (V p).Nonempty ∧ InBoundedLineChart (V p) ∧
      FiniteSeparatedAt δ (V p) ∧ NormalizedFiniteBallBound δ s K (V p) ∧
      ∀ l ∈ V p, |l 0| ≤ 1/2 ∧ TubeIncident δ p l) :
    ∀ z ∈ P.image planarQuarter,
      (quarterPencils V z).Nonempty ∧ InBoundedLineChart (quarterPencils V z) ∧
      FiniteSeparatedAt (δ/4) (quarterPencils V z) ∧
      NormalizedFiniteBallBound (δ/4) s (K*4^s) (quarterPencils V z) ∧
      ∀ l ∈ quarterPencils V z, |l 0| ≤ 1/2 ∧ TubeIncident (δ/4) z l := by
  intro z hz
  obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp hz
  rw [quarterPencils_at]
  have hv := hV p hp
  refine ⟨hv.1.image _,localCellLine_four_chart _ hv.2.1,
    localCellLine_four_separated _ hv.2.2.1,
    localCellLine_four_regular hδ hs hK _ hv.2.2.2.1,?_⟩
  intro l hl
  obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp hl
  exact ⟨(hv.2.2.2.2 a ha).1,planarQuarter_incident (hv.2.2.2.2 a ha).2⟩

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Geometry_QuarterChartFineGain
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Apply the proved regular gain to the quarter chart arising from the
scale-product construction. Both point and line witnesses are transported. -/
namespace Falconer
attribute [local instance] Classical.propDecidable

theorem quarter_chart_regular_fine_gain {κ : ℝ} (hκ : 0 < κ) (hκ1 : κ ≤ 1/100) :
    ∃ ε : ℝ, ∃ N0 : ℕ, 0 < ε ∧ ε ≤ 1 ∧ 0 < N0 ∧ ∀ n : ℕ, N0 ≤ n+2 →
      let Δ := 1/(2:ℝ)^n
      let ρ := 1/(2:ℝ)^(n+3)
      let K := Real.exp (ε*((n+2:ℕ):ℝ)*Real.log 2)
      ∀ s t : ℝ, κ ≤ s → s ≤ 1-8*κ → 2*κ ≤ t-s → t ≤ 2 →
      ∀ P : Finset (Space 2), P.Nonempty →
        (∀ p ∈ P, |p 0| ≤ 1/4 ∧ |p 1| ≤ 1/4) →
        FiniteSeparatedAt (Δ^2) P → NormalizedFiniteBallBound (Δ^2) t K P →
        ((P.image (coarsePlanarRound ρ)).card:ℝ) ≤ K/Δ^t →
      ∀ V : Space 2 → Finset (Space 2),
        (∀ p ∈ P, (V p).Nonempty ∧ InBoundedLineChart (V p) ∧
          FiniteSeparatedAt (Δ^2) (V p) ∧ NormalizedFiniteBallBound (Δ^2) s K (V p) ∧
          ∀ l ∈ V p, |l 0| ≤ 1/2 ∧ TubeIncident (Δ^2) p l) →
        ¬ ((P.biUnion V).card:ℝ) ≤ K/(Δ^s)^4 := by
  obtain ⟨θ,N1,hθ,_,hN1,hgain⟩ := general_regular_fine_gain hκ hκ1
  obtain ⟨ε,N2,hε,hε1,_,hbudget⟩ := chart_gain_budget hθ
  refine ⟨ε,max N1 N2,hε,hε1,lt_of_lt_of_le hN1 (le_max_left _ _),?_⟩
  intro n hn
  dsimp only
  intro s t hs hs1 hgap ht P hP hPsmall hPsep hPball hPcover V hV hsmall
  let Δ := 1/(2:ℝ)^n
  let Δ' := 1/(2:ℝ)^(n+1)
  let ρ := 1/(2:ℝ)^(n+3)
  let K := Real.exp (ε*((n+2:ℕ):ℝ)*Real.log 2)
  let E := Real.exp (θ*((n+3:ℕ):ℝ)*Real.log 2)
  have hΔ : 0 < Δ := by dsimp [Δ]; positivity
  have hΔ' : 0 < Δ' := by dsimp [Δ']; positivity
  have hρ : 0 < ρ := by dsimp [ρ]; positivity
  have hK : 0 < K := Real.exp_pos _
  have hK1 : 1 ≤ K := Real.one_le_exp_iff.mpr (by positivity)
  have hEK : 400*K ≤ E := hbudget n ((le_max_right _ _).trans hn)
  have hKE : K ≤ E := (by linarith only [hK] : K ≤ 400*K).trans hEK
  have hs0 : 0 ≤ s := hκ.le.trans hs
  have hsone : s ≤ 1 := by linarith only [hs1,hκ]
  have ht0 : 0 ≤ t := by linarith only [hs0,hgap,hκ]
  have h4s : (4:ℝ)^s ≤ 4 := by
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le (by norm_num) hsone
  have h4t : (4:ℝ)^t ≤ 16 := by
    calc
      _ ≤ (4:ℝ)^(2:ℝ) := Real.rpow_le_rpow_of_exponent_le (by norm_num) ht
      _ = 16 := by norm_num
  have hKs : K*4^s ≤ E := (mul_le_mul_of_nonneg_left h4s hK.le).trans
    ((by linarith only [hK] : K*4 ≤ 400*K).trans hEK)
  have hKt : K*4^t ≤ E := (mul_le_mul_of_nonneg_left h4t hK.le).trans
    ((by linarith only [hK] : K*16 ≤ 400*K).trans hEK)
  have h25 : 25*K ≤ E := (by linarith only [hK] : 25*K ≤ 400*K).trans hEK
  have hΔeq : Δ' = Δ/2 := by dsimp [Δ',Δ]; rw [pow_succ]; ring
  have hδeq : Δ^2/4 = Δ'^2 := by rw [hΔeq]; ring
  have hρeq : 1/(2:ℝ)^((n+1)+3) = ρ/2 := by
    dsimp [ρ]
    rw [show (n+1)+3 = (n+3)+1 by omega,pow_succ]
    ring
  have hΔle : Δ' ≤ Δ := by rw [hΔeq]; linarith only [hΔ]
  have mono {δ u A B : ℝ} (hd : 0 ≤ δ) (hAB : A ≤ B) {F : Finset (Space 2)}
      (hb : NormalizedFiniteBallBound δ u A F) : NormalizedFiniteBallBound δ u B F := by
    intro z r hr hr1
    exact (hb z r hr hr1).trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hAB (Real.rpow_nonneg (hd.trans hr) _)) (Nat.cast_nonneg _))
  have hPball' : NormalizedFiniteBallBound (Δ'^2) t E (P.image planarQuarter) := by
    rw [← hδeq]
    exact mono (by positivity) hKt (planarQuarter_regular (by positivity) ht0 hK1 P hPball)
  have hPcover' : (((P.image planarQuarter).image (coarsePlanarRound (ρ/2))).card:ℝ) ≤ E/Δ'^t := by
    calc
      _ ≤ 25*((P.image (coarsePlanarRound ρ)).card:ℝ) := planarQuarter_coarse_cover hρ P
      _ ≤ 25*(K/Δ^t) := mul_le_mul_of_nonneg_left hPcover (by norm_num)
      _ = (25*K)/Δ^t := by ring
      _ ≤ E/Δ'^t := by gcongr
  have hV' := quarterPencils_data (by positivity : 0 < Δ^2) hs0 hK1 P V hV
  refine hgain (n+1) (by omega) s t hs hs1 hgap ht (P.image planarQuarter) (hP.image _) ?_ ?_
    hPball' ?_ (quarterPencils V) ?_ ?_
  · intro z hz
    obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp hz
    rw [planarQuarter_apply,planarQuarter_apply,abs_div,abs_div]
    norm_num only [abs_of_pos (by norm_num : (0:ℝ) < 4)]
    constructor <;> linarith only [(hPsmall p hp).1,(hPsmall p hp).2]
  · rw [← hδeq]
    exact planarQuarter_separated P hPsep
  · rw [hρeq]
    exact hPcover'
  · intro z hz
    obtain ⟨hne,hch,hsep,hball,hinc⟩ := hV' z hz
    rw [hδeq] at hsep hball hinc
    exact ⟨hne,hch,hsep,mono (by positivity) hKs hball,hinc⟩
  · rw [quarterPencils_union_card]
    exact hsmall.trans (by gcongr)

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Geometry_BoundedChartFineGain
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Extend the checked regular gain to the full bounded point chart by
a second fixed contraction, preserving the original finite union. -/
namespace Falconer
attribute [local instance] Classical.propDecidable

theorem bounded_chart_regular_fine_gain_oai {κ : ℝ} (hκ : 0 < κ) (hκ1 : κ ≤ 1/100) :
    ∃ ε : ℝ, ∃ N0 : ℕ, 0 < ε ∧ ε ≤ 1 ∧ 0 < N0 ∧ ∀ n : ℕ, N0 ≤ n+2 →
      let Δ := 1/(2:ℝ)^n
      let ρ := 1/(2:ℝ)^(n+3)
      let K := Real.exp (ε*((n+2:ℕ):ℝ)*Real.log 2)
      ∀ s t : ℝ, κ ≤ s → s ≤ 1-8*κ → 2*κ ≤ t-s → t ≤ 2 →
      ∀ P : Finset (Space 2), P.Nonempty →
        InBoundedLineChart P →
        FiniteSeparatedAt (Δ^2) P → NormalizedFiniteBallBound (Δ^2) t K P →
        ((P.image (coarsePlanarRound ρ)).card:ℝ) ≤ K/Δ^t →
      ∀ V : Space 2 → Finset (Space 2),
        (∀ p ∈ P, (V p).Nonempty ∧ InBoundedLineChart (V p) ∧
          FiniteSeparatedAt (Δ^2) (V p) ∧ NormalizedFiniteBallBound (Δ^2) s K (V p) ∧
          ∀ l ∈ V p, |l 0| ≤ 1/2 ∧ TubeIncident (Δ^2) p l) →
        ¬ ((P.biUnion V).card:ℝ) ≤ K/(Δ^s)^4 := by
  obtain ⟨θ,N1,hθ,_,hN1,hgain⟩ := quarter_chart_regular_fine_gain hκ hκ1
  obtain ⟨ε,N2,hε,hε1,_,hbudget⟩ := chart_gain_budget hθ
  refine ⟨ε,max N1 N2,hε,hε1,lt_of_lt_of_le hN1 (le_max_left _ _),?_⟩
  intro n hn
  dsimp only
  intro s t hs hs1 hgap ht P hP hPsmall hPsep hPball hPcover V hV hsmall
  let Δ := 1/(2:ℝ)^n
  let Δ' := 1/(2:ℝ)^(n+1)
  let ρ := 1/(2:ℝ)^(n+3)
  let K := Real.exp (ε*((n+2:ℕ):ℝ)*Real.log 2)
  let E := Real.exp (θ*((n+3:ℕ):ℝ)*Real.log 2)
  have hΔ : 0 < Δ := by dsimp [Δ]; positivity
  have hΔ' : 0 < Δ' := by dsimp [Δ']; positivity
  have hρ : 0 < ρ := by dsimp [ρ]; positivity
  have hK : 0 < K := Real.exp_pos _
  have hK1 : 1 ≤ K := Real.one_le_exp_iff.mpr (by positivity)
  have hEK : 400*K ≤ E := hbudget n ((le_max_right _ _).trans hn)
  have hKE : K ≤ E := (by linarith only [hK] : K ≤ 400*K).trans hEK
  have hs0 : 0 ≤ s := hκ.le.trans hs
  have hsone : s ≤ 1 := by linarith only [hs1,hκ]
  have ht0 : 0 ≤ t := by linarith only [hs0,hgap,hκ]
  have h4s : (4:ℝ)^s ≤ 4 := by
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le (by norm_num) hsone
  have h4t : (4:ℝ)^t ≤ 16 := by
    calc
      _ ≤ (4:ℝ)^(2:ℝ) := Real.rpow_le_rpow_of_exponent_le (by norm_num) ht
      _ = 16 := by norm_num
  have hKs : K*4^s ≤ E := (mul_le_mul_of_nonneg_left h4s hK.le).trans
    ((by linarith only [hK] : K*4 ≤ 400*K).trans hEK)
  have hKt : K*4^t ≤ E := (mul_le_mul_of_nonneg_left h4t hK.le).trans
    ((by linarith only [hK] : K*16 ≤ 400*K).trans hEK)
  have h25 : 25*K ≤ E := (by linarith only [hK] : 25*K ≤ 400*K).trans hEK
  have hΔeq : Δ' = Δ/2 := by dsimp [Δ',Δ]; rw [pow_succ]; ring
  have hδeq : Δ^2/4 = Δ'^2 := by rw [hΔeq]; ring
  have hρeq : 1/(2:ℝ)^((n+1)+3) = ρ/2 := by
    dsimp [ρ]
    rw [show (n+1)+3 = (n+3)+1 by omega,pow_succ]
    ring
  have hΔle : Δ' ≤ Δ := by rw [hΔeq]; linarith only [hΔ]
  have mono {δ u A B : ℝ} (hd : 0 ≤ δ) (hAB : A ≤ B) {F : Finset (Space 2)}
      (hb : NormalizedFiniteBallBound δ u A F) : NormalizedFiniteBallBound δ u B F := by
    intro z r hr hr1
    exact (hb z r hr hr1).trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hAB (Real.rpow_nonneg (hd.trans hr) _)) (Nat.cast_nonneg _))
  have hPball' : NormalizedFiniteBallBound (Δ'^2) t E (P.image planarQuarter) := by
    rw [← hδeq]
    exact mono (by positivity) hKt (planarQuarter_regular (by positivity) ht0 hK1 P hPball)
  have hPcover' : (((P.image planarQuarter).image (coarsePlanarRound (ρ/2))).card:ℝ) ≤ E/Δ'^t := by
    calc
      _ ≤ 25*((P.image (coarsePlanarRound ρ)).card:ℝ) := planarQuarter_coarse_cover hρ P
      _ ≤ 25*(K/Δ^t) := mul_le_mul_of_nonneg_left hPcover (by norm_num)
      _ = (25*K)/Δ^t := by ring
      _ ≤ E/Δ'^t := by gcongr
  have hV' := quarterPencils_data (by positivity : 0 < Δ^2) hs0 hK1 P V hV
  refine hgain (n+1) (by omega) s t hs hs1 hgap ht (P.image planarQuarter) (hP.image _) ?_ ?_
    hPball' ?_ (quarterPencils V) ?_ ?_
  · intro z hz
    obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp hz
    rw [planarQuarter_apply,planarQuarter_apply,abs_div,abs_div]
    norm_num only [abs_of_pos (by norm_num : (0:ℝ) < 4)]
    constructor <;> linarith only [(hPsmall p hp).1,(hPsmall p hp).2]
  · rw [← hδeq]
    exact planarQuarter_separated P hPsep
  · rw [hρeq]
    exact hPcover'
  · intro z hz
    obtain ⟨hne,hch,hsep,hball,hinc⟩ := hV' z hz
    rw [hδeq] at hsep hball hinc
    exact ⟨hne,hch,hsep,mono (by positivity) hKs hball,hinc⟩
  · rw [quarterPencils_union_card]
    exact hsmall.trans (by gcongr)

end Falconer

end OAI
end

theorem solution : type_of% @OAI.Falconer.bounded_chart_regular_fine_gain_oai := @OAI.Falconer.bounded_chart_regular_fine_gain_oai
