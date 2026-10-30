-- Prove2me | solution 1 for OAI.Falconer.controlled_dyadic_angular_gain
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-29T22:07:10.712248+00:00
-- url     : https://prove2.me/submissions/76d95b59-6f21-496d-a226-7fcf27f0eed7

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_OAIQ088F002
import Theorems.Thm_OAI_Falconer_dyadic_original_slice_selection

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

/-- After the two sampling steps, fewer than `δ^(-b-ε/4)` labels with
fewer than that many line cells per label contradict the published
Furstenberg estimate. This is the final quantitative contradiction in
the planar measure-incidence argument. -/
theorem published_furstenberg_labelled_obstruction
    (hpublished : PublishedPlanarFurstenberg) {b f : ℝ}
    (hb : 0 < b) (hb' : b ≤ 1 / 2) (hbf : b < f) (hf : f < 1) :
    ∃ ε δ₀ : ℝ, 0 < ε ∧ 0 < δ₀ ∧ δ₀ ≤ 1 ∧
    ∀ δ : ℝ, 0 < δ → δ < δ₀ →
    ∀ P : Finset (Space 2), P.Nonempty → InBoundedLineChart P →
      FiniteSeparatedAt δ P → NormalizedFiniteBallBound δ f (δ ^ (-ε)) P →
    ∀ T : Space 2 → Finset (Space 2),
      (∀ x ∈ P, (T x).Nonempty ∧ InBoundedLineChart (T x) ∧
        FiniteSeparatedAt δ (T x) ∧ NormalizedFiniteBallBound δ b (δ ^ (-ε)) (T x) ∧
        ∀ l ∈ T x, TubeIncident δ x l) →
    ∀ (ι : Type) [DecidableEq ι] (D : Finset ι) (U : ι → Finset (Space 2)),
      (D.card : ℝ) ≤ δ ^ (-b - ε / 4) →
      (∀ i ∈ D, ((U i).card : ℝ) ≤ δ ^ (-b - ε / 4)) →
      (∀ x ∈ P, ∀ l ∈ T x, ∃ i ∈ D, l ∈ U i) → False := by
  obtain ⟨ε, δ₀, hε, hδ₀, hδ₀1, hF⟩ := hpublished b f hb hb' hbf hf
  refine ⟨ε, δ₀, hε, hδ₀, hδ₀1, ?_⟩
  intro δ hδ hδsmall P hP hchart hsep hball T hT ι _ D U hD hU hcover
  have hδ1 : δ < 1 := hδsmall.trans_le hδ₀1
  have hlower := hF δ hδ hδsmall P hP hchart hsep hball T hT
  have hupper := labelled_line_union_card_le P T D U hcover hU
  have hcard : ((P.biUnion T).card : ℝ) ≤ δ ^ (-2 * b - ε / 2) := by
    calc
      ((P.biUnion T).card : ℝ) ≤ (D.card : ℝ) * δ ^ (-b - ε / 4) := hupper
      _ ≤ δ ^ (-b - ε / 4) * δ ^ (-b - ε / 4) :=
        mul_le_mul_of_nonneg_right hD (Real.rpow_nonneg hδ.le _)
      _ = δ ^ (-2 * b - ε / 2) := by
        rw [← Real.rpow_add hδ]
        congr 1
        ring
  have hstrict : δ ^ (-2 * b - ε / 2) < δ ^ (-2 * b - ε) :=
    Real.rpow_lt_rpow_of_exponent_gt hδ hδ1 (by linarith)
  exact (not_lt_of_ge (hlower.trans hcard)) hstrict

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
-- module Solutions.OAIQ088_FD.Falconer_Angular_AngularSamples
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.sphereMeasure_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Finite sampled direction families

Ball counts for the sampled direction labels control both multiplicities
and normalized ball counts of the rounded incident line families. The
estimates below retain the original labels, including repeated directions.
-/

namespace Falconer
open Set
open scoped BigOperators

theorem roundedLineFamily_nonempty {ι : Type*} [DecidableEq ι]
    (δ : ℝ) (x : Space 2) (m : ι → ℝ) {S : Finset ι} (hS : S.Nonempty) :
    (roundedLineFamily δ x m S).Nonempty := hS.image _

/-- The coordinate error from rounding is at most half the grid width. -/
theorem slope_close_of_roundedLine_close {δ r m : ℝ} (hδ : 0 < δ) (hδr : δ ≤ r)
    (x l : Space 2) (hclose : dist (roundedIncidentLine δ x m) l ≤ r) :
    |m - l 0| ≤ 2 * r := by
  have herr := lineGridRound_error hδ m
  have hcoord : |lineGridRound δ m - l 0| ≤ r := by
    have h := (PiLp.dist_apply_le (roundedIncidentLine δ x m) l 0).trans hclose
    simpa only [roundedIncidentLine_fst, Real.dist_eq] using h
  have htri := abs_sub_le m (lineGridRound δ m) (l 0)
  linarith

/-- Raw ball counts for the rounded line family follow from the original
direction-label counts. -/
theorem roundedLineFamily_ball_count {ι : Type*} [DecidableEq ι]
    {δ K b : ℝ} (hδ : 0 < δ) (x : Space 2) (m : ι → ℝ)
    (D S : Finset ι) (hSD : S ⊆ D)
    (hcount : ∀ a r : ℝ, δ ≤ r →
      ((D.filter (fun i => |m i - a| ≤ r)).card : ℝ) ≤ K * r ^ b)
    (l : Space 2) (r : ℝ) (hδr : δ ≤ r) :
    (((roundedLineFamily δ x m S).filter (fun z => dist z l ≤ r)).card : ℝ) ≤
      K * 2 ^ b * r ^ b := by
  classical
  let A := D.filter (fun i => |m i - l 0| ≤ 2 * r)
  have hsub : (roundedLineFamily δ x m S).filter (fun z => dist z l ≤ r) ⊆
      A.image (fun i => roundedIncidentLine δ x (m i)) := by
    intro z hz
    obtain ⟨hzS, hzdist⟩ := Finset.mem_filter.mp hz
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hzS
    apply Finset.mem_image.mpr
    refine ⟨i, Finset.mem_filter.mpr ⟨hSD hi, ?_⟩, rfl⟩
    exact slope_close_of_roundedLine_close hδ hδr x l hzdist
  calc
    (((roundedLineFamily δ x m S).filter (fun z => dist z l ≤ r)).card : ℝ) ≤
        ((A.image (fun i => roundedIncidentLine δ x (m i))).card : ℝ) := by
      exact_mod_cast Finset.card_le_card hsub
    _ ≤ (A.card : ℝ) := by exact_mod_cast Finset.card_image_le
    _ ≤ K * (2 * r) ^ b := hcount _ _ (by linarith)
    _ = K * 2 ^ b * r ^ b := by
      rw [Real.mul_rpow (by norm_num) ((hδ.trans_le hδr).le)]
      ring

/-- A finite map can lose only the maximum multiplicity of its fibers. -/
theorem card_le_image_card_mul_fiber_bound {ι α : Type*}
    [DecidableEq ι] [DecidableEq α] (S : Finset ι) (F : ι → α) {L : ℝ}
    (hF : ∀ a ∈ S.image F, ((S.filter (fun i => F i = a)).card : ℝ) ≤ L) :
    (S.card : ℝ) ≤ ((S.image F).card : ℝ) * L := by
  rw [Finset.card_eq_sum_card_image F S, Nat.cast_sum]
  exact (Finset.sum_le_sum hF).trans_eq (by simp)

/-- Even repeated original direction labels give enough distinct rounded
lines: their multiplicity is controlled by one δ-ball count. -/
theorem roundedLineFamily_card_lower {ι : Type*} [DecidableEq ι]
    {δ K b : ℝ} (hδ : 0 < δ) (x : Space 2) (m : ι → ℝ)
    (D S : Finset ι) (hSD : S ⊆ D)
    (hcount : ∀ a : ℝ,
      ((D.filter (fun i => |m i - a| ≤ δ)).card : ℝ) ≤ K * δ ^ b) :
    (S.card : ℝ) ≤ ((roundedLineFamily δ x m S).card : ℝ) * (K * δ ^ b) := by
  apply card_le_image_card_mul_fiber_bound
  intro l _
  have hsub : S.filter (fun i => roundedIncidentLine δ x (m i) = l) ⊆
      D.filter (fun i => |m i - l 0| ≤ δ) := by
    intro i hi
    obtain ⟨hiS, hiL⟩ := Finset.mem_filter.mp hi
    refine Finset.mem_filter.mpr ⟨hSD hiS, ?_⟩
    have herr := lineGridRound_error hδ (m i)
    have heq : lineGridRound δ (m i) = l 0 := congrArg (fun z : Space 2 => z 0) hiL
    rw [heq] at herr
    exact herr.trans (by linarith)
  exact (show ((S.filter (fun i => roundedIncidentLine δ x (m i) = l)).card : ℝ) ≤
      ((D.filter (fun i => |m i - l 0| ≤ δ)).card : ℝ) from
        Nat.cast_le.mpr (Finset.card_le_card hsub)).trans (hcount (l 0))

/-- The raw sampled-family bound yields exactly the normalized finite
ball bound required by the published theorem. -/
theorem roundedLineFamily_normalized_ball_bound {ι : Type*} [DecidableEq ι]
    {δ K b L : ℝ} (hδ : 0 < δ) (x : Space 2) (m : ι → ℝ)
    (D S : Finset ι) (hSD : S ⊆ D)
    (hcount : ∀ a r : ℝ, δ ≤ r →
      ((D.filter (fun i => |m i - a| ≤ r)).card : ℝ) ≤ K * r ^ b)
    (hL : K * 2 ^ b ≤ L * ((roundedLineFamily δ x m S).card : ℝ)) :
    NormalizedFiniteBallBound δ b L (roundedLineFamily δ x m S) := by
  intro l r hδr _
  calc
    (((roundedLineFamily δ x m S).filter (fun z => dist z l ≤ r)).card : ℝ) ≤
        K * 2 ^ b * r ^ b := roundedLineFamily_ball_count hδ x m D S hSD hcount l r hδr
    _ ≤ (L * ((roundedLineFamily δ x m S).card : ℝ)) * r ^ b :=
      mul_le_mul_of_nonneg_right hL (Real.rpow_nonneg (hδ.trans_le hδr).le _)
    _ = L * r ^ b * ((roundedLineFamily δ x m S).card : ℝ) := by ring

/-- If a point retains an `I` fraction of the sampled labels, the line
family has normalized loss at most `2 * 2^b * K^2 / I`. The sample-size
assumption is the one supplied by `n = ceil (δ^(-b))`. -/
theorem roundedLineFamily_normalized_of_large_sample {ι : Type*} [DecidableEq ι]
    {δ K I b : ℝ} (hδ : 0 < δ) (hK : 0 < K) (hI : 0 < I)
    (x : Space 2) (m : ι → ℝ) (D S : Finset ι) (hD : D.Nonempty) (hSD : S ⊆ D)
    (hsize : (D.card : ℝ) * δ ^ b ≤ 2)
    (hretained : I * (D.card : ℝ) ≤ (S.card : ℝ))
    (hcount : ∀ a r : ℝ, δ ≤ r →
      ((D.filter (fun i => |m i - a| ≤ r)).card : ℝ) ≤
        (K * (D.card : ℝ)) * r ^ b) :
    NormalizedFiniteBallBound δ b (2 * 2 ^ b * K ^ 2 / I)
      (roundedLineFamily δ x m S) := by
  have hn : 0 < (D.card : ℝ) := by exact_mod_cast hD.card_pos
  have ha : 0 < δ ^ b := Real.rpow_pos_of_pos hδ _
  have hT : 0 ≤ ((roundedLineFamily δ x m S).card : ℝ) := Nat.cast_nonneg _
  have hlow := roundedLineFamily_card_lower hδ x m D S hSD (fun a => hcount a δ le_rfl)
  have hbase : I ≤ ((roundedLineFamily δ x m S).card : ℝ) * K * δ ^ b := by
    apply (mul_le_mul_iff_right₀ hn).mp
    nlinarith [hretained.trans hlow]
  apply roundedLineFamily_normalized_ball_bound hδ x m D S hSD hcount
  have hprod : I * ((K * (D.card : ℝ)) * 2 ^ b) ≤
      (2 * 2 ^ b * K ^ 2) * ((roundedLineFamily δ x m S).card : ℝ) := by
    calc
      I * ((K * (D.card : ℝ)) * 2 ^ b) ≤
          (((roundedLineFamily δ x m S).card : ℝ) * K * δ ^ b) *
            ((K * (D.card : ℝ)) * 2 ^ b) :=
        mul_le_mul_of_nonneg_right hbase (by positivity)
      _ = (K ^ 2 * 2 ^ b * ((roundedLineFamily δ x m S).card : ℝ)) *
          ((D.card : ℝ) * δ ^ b) := by ring
      _ ≤ (K ^ 2 * 2 ^ b * ((roundedLineFamily δ x m S).card : ℝ)) * 2 :=
        mul_le_mul_of_nonneg_left hsize (by positivity)
      _ = _ := by ring
  rw [div_mul_eq_mul_div]
  apply (le_div_iff₀ hI).2
  nlinarith

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Graphs_AllDimensionalGraphGeometry
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Geometry of the retained graph in arbitrary dimension

The graph tests use orthogonal distance to a line and one scalar longitudinal
constraint. Each longitudinal constraint is in the unknown endpoint's own
cap direction. In particular these bounds do not divide by the angle between
the two endpoint directions.
-/

namespace Falconer

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Orthogonal projection is a contraction. -/
theorem norm_perpendicularPart_le {w : E} (hw : ‖w‖ = 1) (v : E) :
    ‖perpendicularPart w v‖ ≤ ‖v‖ := by
  have hn := norm_sub_sq_real v (inner ℝ w v • w)
  rw [real_inner_smul_right, real_inner_comm v w, norm_smul, hw,
    mul_one, Real.norm_eq_abs, sq_abs] at hn
  change ‖v - inner ℝ w v • w‖ ≤ ‖v‖
  rw [real_inner_comm v w]
  nlinarith [norm_nonneg (v - inner ℝ v w • w), norm_nonneg v, sq_nonneg (inner ℝ v w)]

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Angular_AngularTubes
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# A perpendicular tube test occupies two small direction caps

The centers are the two directions of the actual tested displacement.
This gives the angular measure bound used in the parallel-test average.
-/

namespace Falconer
open MeasureTheory Set Metric
open scoped ENNReal
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem perpendicularPart_smul (w v : E) (a : ℝ) :
    perpendicularPart w (a • v) = a • perpendicularPart w v := by
  simp only [perpendicularPart,inner_smul_right,smul_sub,smul_smul]

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Geometry_TubeAnchorNet
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Finite bounded anchor nets for the original direction-wise tube covers -/

namespace Falconer
open Set Metric
variable {d : ℕ}

theorem bounded_anchor_longitudinal (w : Sphere d) {x a : Space d} {D : ℝ}
    (hx : ‖x‖ ≤ D) (ha : ‖a‖ ≤ D) : |inner ℝ (w:Space d) (x-a)| ≤ 2*D := by
  calc
    _ ≤ ‖(w:Space d)‖*‖x-a‖ := abs_real_inner_le_norm _ _
    _ = ‖x-a‖ := by rw [sphere_norm,one_mul]
    _ ≤ ‖x‖+‖a‖ := norm_sub_le _ _
    _ ≤ 2*D := by linarith

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Estimates_RescaledConditional
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The actual affine rescaling of a conditional class probability -/

namespace Falconer.Regularization
open Set MeasureTheory Metric
open scoped ENNReal
variable {d : ℕ}

theorem dyadic_radius_bracket {m : ℕ} {r : ℝ}
    (hmin : 1/(2:ℝ)^m ≤ r) (hmax : r ≤ 1) :
    ∃ j ≤ m, r ≤ 1/(2:ℝ)^j ∧ 1/(2:ℝ)^j ≤ 2*r := by
  induction m with
  | zero =>
    refine ⟨0,le_rfl,?_,?_⟩
    · simpa using hmax
    · norm_num at hmin ⊢
      linarith
  | succ m ih =>
    by_cases hcoarse : 1/(2:ℝ)^m ≤ r
    · obtain ⟨j,hj,hr,hjr⟩ := ih hcoarse
      exact ⟨j,hj.trans (Nat.le_succ m),hr,hjr⟩
    · refine ⟨m,Nat.le_succ m,(lt_of_not_ge hcoarse).le,?_⟩
      have he : 1/(2:ℝ)^m = 2*(1/(2:ℝ)^(m+1)) := by rw [pow_succ]; field_simp
      rw [he]
      linarith

end Falconer.Regularization

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Slicing_SliceGeometry
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Actual orthogonal-band geometry for the angular slicing argument -/

namespace Falconer
open Set MeasureTheory NormedSpace
variable {d : ℕ}

theorem directionSliceBand_projection_lower (V : Submodule ℝ (Space d))
    {w : Sphere d} {δ : ℝ} (hw : w ∈ directionSliceBand V δ) :
    1-δ ≤ ‖V.starProjection (w:Space d)‖ := by
  have he : (w:Space d) = V.starProjection (w:Space d)+Vᗮ.starProjection (w:Space d) := by
    rw [Submodule.starProjection_orthogonal_val]
    abel
  have hh := norm_add_le (V.starProjection (w:Space d)) (Vᗮ.starProjection (w:Space d))
  rw [← he,sphere_norm] at hh
  change ‖Vᗮ.starProjection (w:Space d)‖ ≤ δ at hw
  linarith

theorem norm_sub_normalize (v : Space d) (hv : v ≠ 0) :
    ‖v-normalize v‖ = |‖v‖-1| := by
  calc
    _ = ‖(‖v‖-1) • normalize v‖ := by
      congr 1
      rw [sub_smul,norm_smul_normalize,one_smul]
    _ = _ := by rw [norm_smul,norm_normalize hv,Real.norm_eq_abs,mul_one]

theorem directionSliceBand_normalize_error (V : Submodule ℝ (Space d))
    {w : Sphere d} {δ : ℝ} (hδ : δ < 1) (hw : w ∈ directionSliceBand V δ) :
    ‖normalize (V.starProjection (w:Space d))-(w:Space d)‖ ≤ 2*δ := by
  have hp : V.starProjection (w:Space d) ≠ 0 := norm_pos_iff.mp
    ((sub_pos.mpr hδ).trans_le (directionSliceBand_projection_lower V hw))
  have herr : ‖V.starProjection (w:Space d)-(w:Space d)‖ ≤ δ := by
    change ‖Vᗮ.starProjection (w:Space d)‖ ≤ δ at hw
    simpa only [Submodule.starProjection_orthogonal_val,norm_sub_rev] using hw
  have hnorm : |‖V.starProjection (w:Space d)‖-1| ≤ δ := by
    simpa only [sphere_norm] using (abs_norm_sub_norm_le _ (w:Space d)).trans herr
  calc
    _ ≤ ‖normalize (V.starProjection (w:Space d))-V.starProjection (w:Space d)‖+
        ‖V.starProjection (w:Space d)-(w:Space d)‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ ≤ δ+δ := add_le_add (by rw [norm_sub_rev,norm_sub_normalize _ hp]; exact hnorm) herr
    _ = _ := by ring

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Slicing_GaussianBox
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Gaussian bounds for nonsingular systems of linear bands -/

namespace Falconer
open Set MeasureTheory ProbabilityTheory
open scoped ENNReal
variable {j : ℕ}

theorem coordinateBox_measurable (r : ℝ) : MeasurableSet (coordinateBox j r) := by
  simp only [coordinateBox,ofPred_forall]
  apply MeasurableSet.iInter
  intro i
  exact measurableSet_le (by fun_prop) measurable_const

theorem coordinateBox_volume {r : ℝ} (hr : 0 ≤ r) :
    (volume : Measure (Space j)) (coordinateBox j r) = ENNReal.ofReal ((2*r)^j) := by
  rw [← (PiLp.volume_preserving_toLp (Fin j)).measure_preimage
    (coordinateBox_measurable r).nullMeasurableSet]
  have he : (@WithLp.toLp 2 (Fin j → ℝ)) ⁻¹' coordinateBox j r =
      Set.pi univ (fun _ : Fin j => Icc (-r) r) := by
    ext x
    simp [coordinateBox,abs_le,Pi.le_def,forall_and]
  rw [he,volume_pi_pi]
  simp only [Real.volume_Icc,sub_neg_eq_add,← two_mul,Finset.prod_const,
    Finset.card_univ,Fintype.card_fin,← ENNReal.ofReal_pow (by positivity : 0 ≤ 2*r)]

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Slicing_GaussianSliceMoment
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Second moments of the actual Gaussian direction bands -/

namespace Falconer
open Set MeasureTheory ProbabilityTheory
open scoped ENNReal
variable {d h : ℕ}

theorem gaussianDirectionBand_measurable (A : Fin h → Space d) (r : ℝ) :
    MeasurableSet (gaussianDirectionBand A r) := by
  simp only [gaussianDirectionBand,ofPred_forall]
  apply MeasurableSet.iInter
  intro i
  exact measurableSet_le (by fun_prop) measurable_const

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Slicing_GaussianPointBand
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Point bands in the actual Gaussian row coordinates -/

namespace Falconer
open Set MeasureTheory ProbabilityTheory
open scoped ENNReal
variable {d h : ℕ}

theorem gaussianPointBand_measurable (A : Fin h → Space d) (z : Space h) (r : ℝ) :
    MeasurableSet (gaussianPointBand A z r) := by
  simp only [gaussianPointBand,ofPred_forall]
  apply MeasurableSet.iInter
  intro i
  exact measurableSet_le (by fun_prop) measurable_const

theorem gaussianPointBand_pair_difference (A : Fin h → Space d) (z : Space h) {r : ℝ}
    {x y : Space d} (hx : x ∈ gaussianPointBand A z r) (hy : y ∈ gaussianPointBand A z r) :
    ∀ i, |inner ℝ (x-y) (A i)| ≤ 2*r := by
  intro i
  calc
    _ = |(inner ℝ x (A i)-z i)-(inner ℝ y (A i)-z i)| := by rw [inner_sub_left]; congr 1; ring
    _ ≤ |inner ℝ x (A i)-z i|+|inner ℝ y (A i)-z i| := by
      simpa only [Real.norm_eq_abs] using norm_sub_le (inner ℝ x (A i)-z i) (inner ℝ y (A i)-z i)
    _ ≤ 2*r := by linarith [hx i,hy i]

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Slicing_GaussianActiveCount
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Active original tube-anchor counts in the Gaussian point parameter -/

namespace Falconer
open Set MeasureTheory ProbabilityTheory
open scoped ENNReal
variable {d h : ℕ} {ι : Type*}

theorem gaussianActiveAnchorCount_eq_sum (A : Fin h → Space d)
    (S : Finset ι) (a : ι → Space d) (r : ℝ) (z : Space h) :
    (gaussianActiveAnchorCount A S a r z : ℝ≥0∞) =
      ∑ i ∈ S, {v : Space h | a i ∈ gaussianPointBand A v r}.indicator (fun _ => (1:ℝ≥0∞)) z := by
  classical
  simp only [gaussianActiveAnchorCount,Finset.natCast_card_filter,Set.indicator_apply,mem_ofPred_eq]

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Slicing_GaussianActiveFamily
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Active counts for measurable original-label tube lists -/

namespace Falconer
open Set MeasureTheory
open scoped ENNReal
variable {d h : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem gaussianActiveFamily_measurable (J : Sphere d → Finset ι)
    (hJ : ∀ i, MeasurableSet {w | i ∈ J w}) (a : ι → Space d) (r : ℝ) :
    Measurable (fun p : ((Fin h → Space d) × Space h) × Sphere d =>
      (gaussianActiveAnchorCount p.1.1 (J p.2) a r p.1.2 : ℝ≥0∞)) := by
  classical
  have he (p : ((Fin h → Space d) × Space h) × Sphere d) :
      (gaussianActiveAnchorCount p.1.1 (J p.2) a r p.1.2 : ℝ≥0∞) =
      ∑ i : ι, {q : ((Fin h → Space d) × Space h) × Sphere d |
        i ∈ J q.2 ∧ a i ∈ gaussianPointBand q.1.1 q.1.2 r}.indicator (fun _ => (1:ℝ≥0∞)) p := by
    rw [gaussianActiveAnchorCount_eq_sum]
    simp only [Set.indicator_apply,mem_ofPred_eq]
    calc
      _ = ∑ i ∈ J p.2, (if i ∈ J p.2 ∧ a i ∈ gaussianPointBand p.1.1 p.1.2 r then
          (1:ℝ≥0∞) else 0) := by
        apply Finset.sum_congr rfl
        intro i hi
        simp only [hi,true_and]
      _ = _ := Finset.sum_subset (Finset.subset_univ _) (fun i _ hi => by
        simp only [hi,false_and,ite_false, if_false])
  simp_rw [he]
  apply Finset.measurable_sum
  intro i _
  apply measurable_const.indicator
  apply ((hJ i).preimage measurable_snd).inter
  change MeasurableSet {q : ((Fin h → Space d) × Space h) × Sphere d |
    ∀ j, |inner ℝ (a i) (q.1.1 j)-q.1.2 j| ≤ r}
  simp only [ofPred_forall]
  exact MeasurableSet.iInter (fun _ => measurableSet_le (by fun_prop) measurable_const)

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Geometry_BallTruncation
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Enforcing ball bounds by deleting points of excessive local mass -/

namespace Falconer
open Set Metric MeasureTheory
open scoped ENNReal
variable {X : Type*} [PseudoMetricSpace X] [SecondCountableTopology X]
  [MeasurableSpace X] [BorelSpace X]

omit [SecondCountableTopology X] in
theorem restricted_good_ball_bound (μ : Measure X) [SFinite μ] (r : ℝ) (B : ℝ≥0∞) :
    ∀ a : X, (μ.restrict {x | μ (ball x (2*r)) ≤ B}) (ball a r) ≤ B := by
  intro a
  rw [Measure.restrict_apply measurableSet_ball]
  by_cases hne : (ball a r ∩ {x | μ (ball x (2*r)) ≤ B}).Nonempty
  · obtain ⟨x,hxa,hx⟩ := hne
    have hsub : ball a r ∩ {x | μ (ball x (2*r)) ≤ B} ⊆ ball x (2*r) := by
      rintro y ⟨hy,_⟩
      rw [mem_ball] at hxa hy ⊢
      have htri := dist_triangle y a x
      rw [dist_comm a x] at htri
      linarith
    exact (measure_mono hsub).trans hx
  · rw [Set.not_nonempty_iff_eq_empty.mp hne,measure_empty]
    exact bot_le

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Incidence_FiniteBallPruning
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Simultaneously enforcing the finitely many slice ball bounds -/

namespace Falconer
open Set Metric MeasureTheory
open scoped ENNReal
variable {X ι : Type*} [PseudoMetricSpace X] [SecondCountableTopology X]
  [MeasurableSpace X] [BorelSpace X] [Fintype ι]

omit [SecondCountableTopology X] [Fintype ι] in
theorem finiteBallGood_ball_bound (μ : Measure X) [SFinite μ]
    (r : ι → ℝ) (B : ι → ℝ≥0∞) (i : ι) (a : X) :
    (μ.restrict (finiteBallGood μ r B)) (ball a (r i)) ≤ B i := by
  calc
    _ ≤ (μ.restrict {x | μ (ball x (2*r i)) ≤ B i}) (ball a (r i)) :=
      Measure.restrict_mono_set μ (s := finiteBallGood μ r B)
        (t := {x | μ (ball x (2*r i)) ≤ B i}) (fun _ hx => hx i) _
    _ ≤ _ := restricted_good_ball_bound μ (r i) (B i) a

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Slicing_GaussianPruningSets
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The actual measurable restrictions used in Gaussian slice selection -/

namespace Falconer
open Set Metric MeasureTheory
open scoped ENNReal
variable {d h : ℕ} {ι : Type*} [Fintype ι]

omit [Fintype ι] in
theorem gaussianPointGood_ball (μ : Measure (Space d)) [IsFiniteMeasure μ]
    (δ : ℝ) (r : ι → ℝ) (T : ι → ℝ≥0∞) (p : (Fin h → Space d) × Space h) (i : ι) (a : Space d) :
    ((gaussianPointSliceMeasure μ p.1 p.2 δ).restrict (gaussianPointGood μ δ r T p))
      (ball a (r i)) ≤ T i := finiteBallGood_ball_bound _ r T i a

omit [Fintype ι] in
theorem gaussianDirectionGood_ball (ν : Measure (Sphere d)) [IsFiniteMeasure ν]
    (δ : ℝ) (r : ι → ℝ) (T : ι → ℝ≥0∞) (M : ℝ≥0∞)
    (A : Fin h → Space d) (i : ι) (a : Sphere d) :
    ((gaussianDirectionSliceMeasure ν A δ).restrict (gaussianDirectionGood ν δ r T M A))
      (ball a (r i)) ≤ T i := by
  calc
    _ ≤ ((gaussianDirectionSliceMeasure ν A δ).restrict
        (finiteBallGood (gaussianDirectionSliceMeasure ν A δ) r T)) (ball a (r i)) :=
      Measure.restrict_mono_set _ (s := gaussianDirectionGood ν δ r T M A)
        (t := finiteBallGood (gaussianDirectionSliceMeasure ν A δ) r T) (fun _ hw => hw.2) _
    _ ≤ _ := finiteBallGood_ball_bound _ r T i a

omit [Fintype ι] in
theorem gaussianDirectionGood_mass (ν : Measure (Sphere d)) [IsFiniteMeasure ν]
    (δ : ℝ) (r : ι → ℝ) (T : ι → ℝ≥0∞) (M : ℝ≥0∞) (A : Fin h → Space d) :
    ((gaussianDirectionSliceMeasure ν A δ).restrict (gaussianDirectionGood ν δ r T M A)) univ ≤ M := by
  by_cases hm : gaussianDirectionMass ν δ A ≤ M
  · calc
      _ ≤ gaussianDirectionSliceMeasure ν A δ univ := Measure.restrict_le_self _
      _ = gaussianDirectionMass ν δ A := by
        simp [gaussianDirectionSliceMeasure,gaussianDirectionMass,Measure.smul_apply]
      _ ≤ _ := hm
  · have he : gaussianDirectionGood ν δ r T M A = ∅ := by ext w; simp [gaussianDirectionGood,hm]
    simp only [he,Measure.restrict_empty,Measure.coe_zero,Pi.zero_apply]
    exact zero_le

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Slicing_GaussianPrunedMass
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Uniform masses and support of the pruned original slice laws -/

namespace Falconer
open Set Metric MeasureTheory
open scoped ENNReal
variable {d h : ℕ} {ι : Type*}

theorem gaussianPointSliceMeasure_ae_of_ae
    (μ : Measure (Space d)) (A : Fin h → Space d) (z : Space h) (δ : ℝ)
    {P : Space d → Prop} (hP : ∀ᵐ x ∂μ, P x) :
    ∀ᵐ x ∂gaussianPointSliceMeasure μ A z δ, P x := by
  exact Measure.ae_smul_measure (ae_restrict_of_ae hP) _

theorem gaussianPointGood_mass
    (μ : Measure (Space d)) [IsFiniteMeasure μ]
    (δ : ℝ) (r : ι → ℝ) (T : ι → ℝ≥0∞)
    (p : (Fin h → Space d) × Space h) {D : ℝ}
    (hμ : ∀ᵐ x ∂μ, ‖x‖ ≤ D) (i : ι) (hi : D < r i) :
    ((gaussianPointSliceMeasure μ p.1 p.2 δ).restrict (gaussianPointGood μ δ r T p)) univ ≤ T i := by
  let α := (gaussianPointSliceMeasure μ p.1 p.2 δ).restrict (gaussianPointGood μ δ r T p)
  have ha : ∀ᵐ x ∂α, x ∈ ball 0 (r i) := by
    filter_upwards [ae_restrict_of_ae (gaussianPointSliceMeasure_ae_of_ae μ p.1 p.2 δ hμ)] with x hx
    simpa only [mem_ball,dist_zero_right] using hx.trans_lt hi
  have he : α (ball 0 (r i)) = α univ := measure_congr (by
    filter_upwards [ha] with x hx
    exact propext ⟨fun _ => mem_univ x,fun _ => hx⟩)
  rw [← he]
  exact gaussianPointGood_ball μ δ r T p i 0

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Slicing_GaussianRowMap
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Linear maps and kernel planes for the Gaussian slicing parameters -/

namespace Falconer
open Set MeasureTheory
open scoped ENNReal
variable {d h : ℕ}

theorem gaussianRowMap_adjoint_basis (A : Fin h → Space d) (i : Fin h) :
    (gaussianRowMap A).adjoint (EuclideanSpace.basisFun (Fin h) ℝ i) = A i := by
  apply ext_inner_right ℝ
  intro x
  rw [ContinuousLinearMap.adjoint_inner_left,EuclideanSpace.basisFun_inner,gaussianRowMap_apply]
  exact real_inner_comm _ _

theorem coordinate_norm_le_card_mul (x : Space h) {r : ℝ}
    (hx : ∀ i, |x i| ≤ r) : ‖x‖ ≤ (h:ℝ)*r := by
  calc
    _ = ‖∑ i : Fin h, x i • EuclideanSpace.basisFun (Fin h) ℝ i‖ := by
      exact congrArg norm ((EuclideanSpace.basisFun (Fin h) ℝ).sum_repr x).symm
    _ ≤ ∑ i : Fin h, ‖x i • EuclideanSpace.basisFun (Fin h) ℝ i‖ := norm_sum_le _ _
    _ = ∑ i : Fin h, |x i| := by
      apply Finset.sum_congr rfl
      intro i _
      rw [norm_smul,Real.norm_eq_abs,(EuclideanSpace.basisFun (Fin h) ℝ).norm_eq_one,mul_one]
    _ ≤ ∑ _ : Fin h, r := Finset.sum_le_sum (fun i _ => hx i)
    _ = _ := by simp

theorem gaussianRowMap_norm_le_of_bands (A : Fin h → Space d) (x : Space d) {r : ℝ}
    (hx : ∀ i, |inner ℝ x (A i)| ≤ r) : ‖gaussianRowMap A x‖ ≤ (h:ℝ)*r :=
  coordinate_norm_le_card_mul _ (by simpa only [gaussianRowMap_apply] using hx)

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Slicing_GaussianKernelGeometry
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Passing from Gaussian row bands to their actual kernel planes -/

namespace Falconer
open Set MeasureTheory
open scoped ENNReal
variable {d h : ℕ}

theorem linearMap_orthogonal_kernel_projection (L : Space d →L[ℝ] Space h) (x : Space d) :
    L (L.kerᗮ.starProjection x) = L x := by
  rw [Submodule.starProjection_orthogonal_val,map_sub]
  have hz : L (L.ker.starProjection x) = 0 := (L.ker.orthogonalProjectionOnto x).property
  rw [hz,sub_zero]

theorem gaussian_direction_band_kernel_distance (A : Fin h → Space d)
    {K r : ℝ} (hK : 0 ≤ K)
    (hbound : ∀ x : Space d, ‖(gaussianRowMap A).kerᗮ.starProjection x‖ ≤ K*‖gaussianRowMap A x‖)
    {w : Sphere d} (hw : w ∈ gaussianDirectionBand A r) :
    ‖(gaussianRowMap A).kerᗮ.starProjection (w:Space d)‖ ≤ K*((h:ℝ)*r) := by
  exact (hbound w).trans (mul_le_mul_of_nonneg_left (gaussianRowMap_norm_le_of_bands A w hw) hK)

theorem gaussian_point_band_kernel_difference (A : Fin h → Space d) (z : Space h)
    {K r : ℝ} (hK : 0 ≤ K)
    (hbound : ∀ x : Space d, ‖(gaussianRowMap A).kerᗮ.starProjection x‖ ≤ K*‖gaussianRowMap A x‖)
    {x y : Space d} (hx : x ∈ gaussianPointBand A z r) (hy : y ∈ gaussianPointBand A z r) :
    ‖(gaussianRowMap A).kerᗮ.starProjection (x-y)‖ ≤ K*((h:ℝ)*(2*r)) :=
  (hbound (x-y)).trans (mul_le_mul_of_nonneg_left
    (gaussianRowMap_norm_le_of_bands A (x-y) (gaussianPointBand_pair_difference A z hx hy)) hK)

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Slicing_GaussianRowStability
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Quantitative kernel geometry near a fixed orthonormal row frame -/

namespace Falconer
open Set MeasureTheory
variable {d h : ℕ}

theorem gaussianRowMap_adjoint_apply (A : Fin h → Space d) (a : Space h) :
    (gaussianRowMap A).adjoint a = ∑ i, a i • A i := by
  calc
    _ = (gaussianRowMap A).adjoint
        (∑ i, a i • EuclideanSpace.basisFun (Fin h) ℝ i) := by
      congr 1
      exact (EuclideanSpace.basisFun (Fin h) ℝ).sum_repr a |>.symm
    _ = _ := by simp only [map_sum,map_smul,gaussianRowMap_adjoint_basis]

theorem row_adjoint_near_isometry (A : Fin h → Space d)
    (e : Space h →ₗᵢ[ℝ] Space d) {ε : ℝ}
    (hA : ∀ i, ‖A i-e (EuclideanSpace.basisFun (Fin h) ℝ i)‖ ≤ ε)
    (a : Space h) :
    ‖(gaussianRowMap A).adjoint a-e a‖ ≤ (h:ℝ)*ε*‖a‖ := by
  have he : e a = ∑ i, a i • e (EuclideanSpace.basisFun (Fin h) ℝ i) := by
    conv_lhs => rw [← (EuclideanSpace.basisFun (Fin h) ℝ).sum_repr a]
    simp only [map_sum,map_smul]
    rfl
  rw [gaussianRowMap_adjoint_apply,he,← Finset.sum_sub_distrib]
  calc
    _ ≤ ∑ i : Fin h, ‖a i • A i-a i • e (EuclideanSpace.basisFun (Fin h) ℝ i)‖ :=
      norm_sum_le _ _
    _ ≤ ∑ _ : Fin h, ‖a‖*ε := by
      apply Finset.sum_le_sum
      intro i _
      rw [← smul_sub,norm_smul]
      exact mul_le_mul (PiLp.norm_apply_le a i) (hA i) (norm_nonneg _) (norm_nonneg _)
    _ = _ := by simp; ring

theorem row_adjoint_lower_near_isometry (A : Fin h → Space d)
    (e : Space h →ₗᵢ[ℝ] Space d) {ε : ℝ}
    (hA : ∀ i, ‖A i-e (EuclideanSpace.basisFun (Fin h) ℝ i)‖ ≤ ε)
    (hε : (h:ℝ)*ε ≤ 1/2) (a : Space h) :
    ‖a‖ ≤ 2*‖(gaussianRowMap A).adjoint a‖ := by
  have h1 := row_adjoint_near_isometry A e hA a
  have h2 := norm_sub_norm_le (e a) ((gaussianRowMap A).adjoint a)
  rw [e.norm_map,norm_sub_rev] at h2
  have h3 := mul_le_mul_of_nonneg_right hε (norm_nonneg a)
  nlinarith

theorem kernel_projection_bound_of_adjoint_lower (L : Space d →L[ℝ] Space h)
    {K : ℝ} (hK : 0 ≤ K) (hL : ∀ a : Space h, ‖a‖ ≤ K*‖L.adjoint a‖)
    (x : Space d) : ‖L.kerᗮ.starProjection x‖ ≤ K*‖L x‖ := by
  let y := L.kerᗮ.starProjection x
  have hy : y ∈ L.kerᗮ := L.kerᗮ.starProjection_apply_mem x
  have hr : y ∈ L.adjoint.range := by
    rw [← ContinuousLinearMap.adjoint_toLinearMap,← LinearMap.orthogonal_ker]
    exact hy
  obtain ⟨a,ha⟩ := hr
  change L.adjoint a = y at ha
  have hnorm : ‖y‖^2 ≤ ‖a‖*‖L x‖ := by
    calc
      _ = inner ℝ y y := (real_inner_self_eq_norm_sq y).symm
      _ = inner ℝ (L.adjoint a) y := by rw [ha]
      _ = inner ℝ a (L y) := ContinuousLinearMap.adjoint_inner_left _ _ _
      _ = inner ℝ a (L x) := congrArg (inner ℝ a)
        (linearMap_orthogonal_kernel_projection L x)
      _ ≤ _ := real_inner_le_norm _ _
  have hla := hL a
  rw [ha] at hla
  have hh := mul_le_mul_of_nonneg_right hla (norm_nonneg (L x))
  by_cases hz : ‖y‖ = 0
  · change ‖y‖ ≤ _
    rw [hz]
    exact mul_nonneg hK (norm_nonneg _)
  · have hp : 0 < ‖y‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hz)
    change ‖y‖ ≤ _
    nlinarith

theorem row_kernel_projection_bound (A : Fin h → Space d)
    (e : Space h →ₗᵢ[ℝ] Space d) {ε : ℝ}
    (hA : ∀ i, ‖A i-e (EuclideanSpace.basisFun (Fin h) ℝ i)‖ ≤ ε)
    (hε : (h:ℝ)*ε ≤ 1/2) (x : Space d) :
    ‖(gaussianRowMap A).kerᗮ.starProjection x‖ ≤ 2*‖gaussianRowMap A x‖ :=
  kernel_projection_bound_of_adjoint_lower _ (by norm_num)
    (row_adjoint_lower_near_isometry A e hA hε) x

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Slicing_GaussianRowDimension
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The dimension of kernel slices in the controlled row chart -/

namespace Falconer
variable {d h : ℕ}

theorem adjoint_injective_of_lower (L : Space d →L[ℝ] Space h)
    {K : ℝ} (hL : ∀ a : Space h, ‖a‖ ≤ K*‖L.adjoint a‖) :
    Function.Injective L.adjoint := by
  apply LinearMap.ker_eq_bot.mp
  apply (LinearMap.ker_eq_bot').mpr
  intro a ha
  change L.adjoint a = 0 at ha
  have hn := hL a
  rw [ha,norm_zero,mul_zero] at hn
  exact norm_eq_zero.mp (le_antisymm hn (norm_nonneg _))

theorem kernel_finrank_of_adjoint_lower (L : Space d →L[ℝ] Space h)
    {K : ℝ} (hL : ∀ a : Space h, ‖a‖ ≤ K*‖L.adjoint a‖) :
    Module.finrank ℝ L.ker = d-h := by
  have hr := LinearMap.finrank_range_of_inj (adjoint_injective_of_lower L hL)
  have ha := LinearMap.finrank_range_adjoint L.toLinearMap
  rw [ContinuousLinearMap.adjoint_toLinearMap] at ha
  have hn := L.toLinearMap.finrank_range_add_finrank_ker
  simp only [finrank_euclideanSpace, Fintype.card_fin] at hr hn
  omega

theorem row_kernel_finrank (A : Fin h → Space d)
    (e : Space h →ₗᵢ[ℝ] Space d) {ε : ℝ}
    (hA : ∀ i, ‖A i-e (EuclideanSpace.basisFun (Fin h) ℝ i)‖ ≤ ε)
    (hε : (h:ℝ)*ε ≤ 1/2) :
    Module.finrank ℝ (gaussianRowMap A).ker = d-h :=
  kernel_finrank_of_adjoint_lower _ (row_adjoint_lower_near_isometry A e hA hε)

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Slicing_GaussianParameterSupport
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A bounded point-parameter region for bounded original source laws -/

namespace Falconer
open Set MeasureTheory
open scoped ENNReal
variable {d h : ℕ}

theorem gaussianRowNeighborhood_norm {n : ℕ} (B : Fin h → Space (n+1))
    (hB : ∀ i, ‖B i‖ ≤ 1) {ε : ℝ} {A : Fin h → Space (n+1)}
    (hA : A ∈ gaussianRowNeighborhood B ε) (i : Fin h) : ‖A i‖ ≤ ε+1 := by
  calc
    _ ≤ ‖A i-B i‖+‖B i‖ := by simpa only [sub_add_cancel] using norm_add_le (A i-B i) (B i)
    _ ≤ _ := add_le_add (hA i) (hB i)

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Slicing_GaussianActiveRelation
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Original-pair incidence after the active-cover deletion -/

namespace Falconer
open Set MeasureTheory ProbabilityTheory
open scoped ENNReal
variable {d h : ℕ} {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq κ]

omit [Fintype ι] in
theorem gaussianActiveRelation_measurable (E : Set (Space d × Sphere d)) (hE : MeasurableSet E)
    (J : Sphere d → Finset κ) (hJ : ∀ i, MeasurableSet {w | i ∈ J w})
    (a : κ → Space d) (R : ℝ) (T : ℝ≥0∞) (good : Bool) :
    MeasurableSet (gaussianActiveRelation (h := h) E J a R T good) := by
  have hm := (gaussianActiveFamily_measurable (h := h) J hJ a R).comp
    (show Measurable (fun q : ((Fin h → Space d) × Space h) × (Space d × Sphere d) =>
      (q.1,q.2.2)) from by fun_prop)
  cases good
  · exact (hE.preimage measurable_snd).inter (measurableSet_lt measurable_const hm)
  · exact (hE.preimage measurable_snd).inter (measurableSet_le hm measurable_const)

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Slicing_GaussianKernelCoordinates
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Metric control in the kernel coordinates of a Gaussian slice -/

namespace Falconer
open Set MeasureTheory NormedSpace
variable {d h : ℕ}

theorem gaussian_point_kernel_pair_distance (A : Fin h → Space d) (z : Space h)
    {K r s : ℝ} (hK : 0 ≤ K)
    (hbound : ∀ x : Space d, ‖(gaussianRowMap A).kerᗮ.starProjection x‖ ≤ K*‖gaussianRowMap A x‖)
    {x y : Space d} (hx : x ∈ gaussianPointBand A z r) (hy : y ∈ gaussianPointBand A z r)
    (hxy : ‖(gaussianRowMap A).ker.starProjection x-
      (gaussianRowMap A).ker.starProjection y‖ ≤ s) :
    ‖x-y‖ ≤ s+K*((h:ℝ)*(2*r)) := by
  have he : x-y = (gaussianRowMap A).ker.starProjection (x-y)+
      (gaussianRowMap A).kerᗮ.starProjection (x-y) := by
    rw [Submodule.starProjection_orthogonal_val]
    abel
  calc
    _ ≤ ‖(gaussianRowMap A).ker.starProjection (x-y)‖+
        ‖(gaussianRowMap A).kerᗮ.starProjection (x-y)‖ := by
      conv_lhs => rw [he]
      exact norm_add_le _ _
    _ ≤ _ := add_le_add (by simpa only [map_sub] using hxy)
      (gaussian_point_band_kernel_difference A z hK hbound hx hy)

theorem gaussian_direction_kernel_normalize_error (A : Fin h → Space d)
    {K r : ℝ} (hK : 0 ≤ K)
    (hbound : ∀ x : Space d, ‖(gaussianRowMap A).kerᗮ.starProjection x‖ ≤ K*‖gaussianRowMap A x‖)
    (hr : K*((h:ℝ)*r) < 1) {w : Sphere d} (hw : w ∈ gaussianDirectionBand A r) :
    ‖normalize ((gaussianRowMap A).ker.starProjection (w:Space d))-(w:Space d)‖ ≤
      2*(K*((h:ℝ)*r)) :=
  directionSliceBand_normalize_error _ hr (gaussian_direction_band_kernel_distance A hK hbound hw)

theorem gaussian_direction_kernel_nonzero (A : Fin h → Space d)
    {K r : ℝ} (hK : 0 ≤ K)
    (hbound : ∀ x : Space d, ‖(gaussianRowMap A).kerᗮ.starProjection x‖ ≤ K*‖gaussianRowMap A x‖)
    (hr : K*((h:ℝ)*r) < 1) {w : Sphere d} (hw : w ∈ gaussianDirectionBand A r) :
    (gaussianRowMap A).ker.starProjection (w:Space d) ≠ 0 := by
  apply norm_pos_iff.mp
  exact (sub_pos.mpr hr).trans_le (directionSliceBand_projection_lower _
    (gaussian_direction_band_kernel_distance A hK hbound hw))

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Slicing_SliceTubeGeometry
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Original tube anchors and projected tube widths in an orthogonal slice -/

namespace Falconer
open NormedSpace
variable {d : ℕ}

theorem slice_projected_tube_width (V : Submodule ℝ (Space d)) {w : Sphere d}
    {δ : ℝ} (hδ : δ < 1) (hw : w ∈ directionSliceBand V δ) (x a : Space d) :
    ‖perpendicularPart (normalize (V.starProjection (w:Space d)))
      (V.starProjection x-V.starProjection a)‖ ≤ ‖perpendicularPart (w:Space d) (x-a)‖ := by
  let v := V.starProjection (w:Space d)
  let u := normalize v
  let t := inner ℝ (w:Space d) (x-a)
  let e := perpendicularPart (w:Space d) (x-a)
  have hv : v ≠ 0 := norm_pos_iff.mp
    ((sub_pos.mpr hδ).trans_le (directionSliceBand_projection_lower V hw))
  have hu : ‖u‖ = 1 := norm_normalize hv
  have hperp : perpendicularPart u v = 0 := by
    have hv' : v = ‖v‖ • u := (norm_smul_normalize v).symm
    rw [hv',perpendicularPart_smul]
    simp [perpendicularPart,hu]
  have hsplit : V.starProjection x-V.starProjection a = t • v+V.starProjection e := by
    dsimp [v,t,e,perpendicularPart]
    simp only [map_sub,map_smul]
    module
  change ‖perpendicularPart u (V.starProjection x-V.starProjection a)‖ ≤ ‖e‖
  rw [hsplit]
  have he : perpendicularPart u (t • v+V.starProjection e) = perpendicularPart u (V.starProjection e) := by
    calc
      _ = t • perpendicularPart u v+perpendicularPart u (V.starProjection e) := by
        simp only [perpendicularPart,inner_add_right,inner_smul_right,add_smul]
        module
      _ = _ := by rw [hperp,smul_zero,zero_add]
  rw [he]
  exact (norm_perpendicularPart_le hu _).trans (V.norm_starProjection_apply_le e)

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Slicing_GaussianTubeGeometry
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Original tube labels and active anchors for Gaussian row slices -/

namespace Falconer
variable {d h : ℕ}

theorem gaussian_active_anchor (A : Fin h → Space d) (z : Space h)
    {w : Sphere d} {x a : Space d} {δ ε L M : ℝ} (_hM : 0 ≤ M)
    (hA : ∀ i, ‖A i‖ ≤ M) (hw : w ∈ gaussianDirectionBand A δ)
    (hx : x ∈ gaussianPointBand A z δ)
    (htube : ‖perpendicularPart (w:Space d) (x-a)‖ ≤ ε)
    (hlength : |inner ℝ (w:Space d) (x-a)| ≤ L) :
    a ∈ gaussianPointBand A z (δ+L*δ+ε*M) := by
  let t := inner ℝ (w:Space d) (x-a)
  let e := perpendicularPart (w:Space d) (x-a)
  have he : a = x-t • (w:Space d)-e := by dsimp [t,e,perpendicularPart]; module
  intro i
  have hi : inner ℝ a (A i)-z i =
      (inner ℝ x (A i)-z i)-t*inner ℝ (w:Space d) (A i)-inner ℝ e (A i) := by
    rw [he,inner_sub_left,inner_sub_left,real_inner_smul_left]
    ring
  have ht : |t*inner ℝ (w:Space d) (A i)| ≤ L*δ := by
    rw [abs_mul]
    exact mul_le_mul hlength (hw i) (abs_nonneg _) ((abs_nonneg _).trans hlength)
  have hp : |inner ℝ e (A i)| ≤ ε*M :=
    (abs_real_inner_le_norm _ _).trans (mul_le_mul htube (hA i) (norm_nonneg _)
      ((norm_nonneg _).trans htube))
  rw [hi]
  exact ((abs_sub _ _).trans (add_le_add (abs_sub _ _) le_rfl)).trans
    (add_le_add (add_le_add (hx i) ht) hp)

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Slicing_GaussianActiveCover
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The projected fiber cover keeps the original direction label -/

namespace Falconer
open Set NormedSpace
open scoped ENNReal
variable {d h : ℕ} {ι : Type*}

theorem gaussianActiveAnchors_card (A : Fin h → Space d) (z : Space h)
    (J : Finset ι) (a : ι → Space d) (R : ℝ) :
    (gaussianActiveAnchors A z J a R).card = gaussianActiveAnchorCount A J a R z := rfl

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Slicing_TransverseFrame
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A uniformly transverse row frame for each fixed spherical chart -/

namespace Falconer
variable {n h : ℕ}

theorem transverse_frame_chart_bound (e : Space h →ₗᵢ[ℝ] Space (n+1))
    (w₀ : Space (n+1))
    (he : ∀ i, inner ℝ w₀ (e (EuclideanSpace.basisFun (Fin h) ℝ i)) = 0)
    {w : Space (n+1)} {ρ : ℝ} (hw : dist w w₀ ≤ ρ) (i : Fin h) :
    |inner ℝ w (e (EuclideanSpace.basisFun (Fin h) ℝ i))| ≤ ρ := by
  let b := e (EuclideanSpace.basisFun (Fin h) ℝ i)
  have hi : inner ℝ w b = inner ℝ (w-w₀) b := by rw [inner_sub_left,he i,sub_zero]
  rw [hi]
  calc
    _ ≤ ‖w-w₀‖*‖b‖ := abs_real_inner_le_norm _ _
    _ = dist w w₀ := by
      rw [show ‖b‖ = 1 from (e.norm_map _).trans
        ((EuclideanSpace.basisFun (Fin h) ℝ).norm_eq_one i),mul_one,dist_eq_norm]
    _ ≤ _ := hw

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Slicing_PlanarSliceGeometry
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Oriented planar coordinates and the strip equations of sliced tubes -/

namespace Falconer
open NormedSpace

theorem exists_unit_axis_isometry {m : ℕ} (hm : 0 < m)
    {v : Space m} (hv : ‖v‖ = 1) :
    ∃ R : Space m ≃ₗᵢ[ℝ] Space m,
      R v = EuclideanSpace.basisFun (Fin m) ℝ ⟨0,hm⟩ := by
  let u := EuclideanSpace.basisFun (Fin m) ℝ ⟨0,hm⟩
  let S : Space m ≃ₗᵢ[ℝ] Space m := (ℝ ∙ (u-v))ᗮ.reflection
  have he : S u = v := Submodule.reflection_sub
    (((EuclideanSpace.basisFun (Fin m) ℝ).norm_eq_one ⟨0,hm⟩).trans hv.symm)
  exact ⟨S.symm,by rw [← he,S.symm_apply_apply]⟩

theorem planarSlope_small_of_axis_close {w : Space 2}
    (hw : dist w (EuclideanSpace.basisFun (Fin 2) ℝ 0) ≤ 1/4) :
    0 < w 0 ∧ |planarSlope w| ≤ 1/2 := by
  have hzero := (PiLp.dist_apply_le w (EuclideanSpace.basisFun (Fin 2) ℝ 0) 0).trans hw
  have hone := (PiLp.dist_apply_le w (EuclideanSpace.basisFun (Fin 2) ℝ 0) 1).trans hw
  have hz : |w 0-1| ≤ 1/4 := by simpa [Real.dist_eq] using hzero
  have ho : |w 1| ≤ 1/4 := by simpa [Real.dist_eq] using hone
  have hpos : 0 < w 0 := by have := (abs_le.mp hz).1; linarith
  refine ⟨hpos,?_⟩
  rw [planarSlope,abs_div,abs_of_pos hpos]
  apply (div_le_iff₀ hpos).mpr
  have := (abs_le.mp hz).1
  linarith

theorem planarIntercept_sub (w x a : Space 2) :
    planarIntercept w (x-a) = planarIntercept w x-planarIntercept w a := by
  simp only [planarIntercept,PiLp.sub_apply]
  ring

theorem planarIntercept_perpendicular {w : Space 2} (hw : w 0 ≠ 0) (x : Space 2) :
    planarIntercept w (perpendicularPart w x) = planarIntercept w x := by
  simp only [planarIntercept,planarSlope,perpendicularPart,PiLp.sub_apply,PiLp.smul_apply,
    smul_eq_mul]
  field_simp
  ring

theorem planarIntercept_norm_bound (w x : Space 2) :
    |planarIntercept w x| ≤ (1+|planarSlope w|)*‖x‖ := by
  calc
    _ ≤ |x 1|+|planarSlope w*x 0| := abs_sub _ _
    _ = |x 1|+|planarSlope w| * |x 0| := by rw [abs_mul]
    _ ≤ ‖x‖+|planarSlope w| * ‖x‖ :=
      add_le_add (PiLp.norm_apply_le x 1)
        (mul_le_mul_of_nonneg_left (PiLp.norm_apply_le x 0) (abs_nonneg _))
    _ = _ := by ring

theorem planar_tube_strip {w x a : Space 2} {ε : ℝ}
    (hw : w 0 ≠ 0) (hslope : |planarSlope w| ≤ 1/2)
    (htube : ‖perpendicularPart w (x-a)‖ ≤ ε) :
    |x 1-planarSlope w*x 0-planarIntercept w a| ≤ (3/2)*ε := by
  change |planarIntercept w x-planarIntercept w a| ≤ _
  rw [← planarIntercept_sub,← planarIntercept_perpendicular hw]
  exact (planarIntercept_norm_bound w _).trans
    (mul_le_mul (by linarith) htube (norm_nonneg _) (by norm_num))

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Slicing_OrientedSlice
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Isometric slice coordinates aligned with the center of a direction chart -/

namespace Falconer
open NormedSpace
variable {d m : ℕ}

theorem slice_isometry_normalize (V : Submodule ℝ (Space d))
    (e : V ≃ₗᵢ[ℝ] Space m) (x : V) : e (normalize x) = normalize (e x) := by
  simp only [NormedSpace.normalize,map_smul,e.norm_map]

theorem slice_isometry_perpendicular (V : Submodule ℝ (Space d))
    (e : V ≃ₗᵢ[ℝ] Space m) (w x : V) :
    e (perpendicularPart w x) = perpendicularPart (e w) (e x) := by
  simp only [perpendicularPart,map_sub,map_smul,e.inner_map_map]

theorem exists_oriented_slice_coordinates (V : Submodule ℝ (Space d))
    (hm : Module.finrank ℝ V = m) (hmpos : 0 < m) (w₀ : Space d)
    (hw₀ : V.starProjection w₀ ≠ 0) :
    ∃ e : V ≃ₗᵢ[ℝ] Space m,
      normalize (e (V.orthogonalProjectionOnto w₀)) =
        EuclideanSpace.basisFun (Fin m) ℝ ⟨0,hmpos⟩ := by
  let e₀ := sliceCoordinates V hm
  have hv : e₀ (V.orthogonalProjectionOnto w₀) ≠ 0 := by
    intro hzero
    have hp : V.orthogonalProjectionOnto w₀ = 0 := e₀.injective (by simpa using hzero)
    exact hw₀ (congrArg Subtype.val hp)
  obtain ⟨R,hR⟩ := exists_unit_axis_isometry hmpos (norm_normalize hv)
  refine ⟨e₀.trans R,?_⟩
  change normalize (R (e₀ (V.orthogonalProjectionOnto w₀))) = _
  have hRN (v : Space m) : R (normalize v) = normalize (R v) := by
    simp only [NormedSpace.normalize,map_smul,R.norm_map]
  rw [← hRN]
  exact hR

theorem oriented_slice_direction_distance (V : Submodule ℝ (Space d))
    (e : V ≃ₗᵢ[ℝ] Space m) {w w₀ : Sphere d} {δ δ₀ ρ : ℝ}
    (hδ : δ < 1) (hδ₀ : δ₀ < 1)
    (hw : w ∈ directionSliceBand V δ) (hw₀ : w₀ ∈ directionSliceBand V δ₀)
    (hclose : dist (w:Space d) (w₀:Space d) ≤ ρ) :
    dist (normalize (e (V.orthogonalProjectionOnto (w:Space d))))
      (normalize (e (V.orthogonalProjectionOnto (w₀:Space d)))) ≤ 2*δ+ρ+2*δ₀ := by
  rw [← slice_isometry_normalize V e,← slice_isometry_normalize V e,e.dist_map,dist_eq_norm]
  change ‖normalize (V.starProjection (w:Space d))-
    normalize (V.starProjection (w₀:Space d))‖ ≤ _
  calc
    _ ≤ ‖normalize (V.starProjection (w:Space d))-(w:Space d)‖+
        ‖(w:Space d)-normalize (V.starProjection (w₀:Space d))‖ :=
      norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ ≤ 2*δ+(‖(w:Space d)-(w₀:Space d)‖+
        ‖(w₀:Space d)-normalize (V.starProjection (w₀:Space d))‖) :=
      add_le_add (directionSliceBand_normalize_error V hδ hw)
        (norm_sub_le_norm_sub_add_norm_sub _ _ _)
    _ ≤ 2*δ+(ρ+2*δ₀) := add_le_add le_rfl
      (add_le_add hclose (by simpa only [norm_sub_rev] using
        directionSliceBand_normalize_error V hδ₀ hw₀))
    _ = _ := by ring

theorem oriented_slice_tube_width (V : Submodule ℝ (Space d))
    (e : V ≃ₗᵢ[ℝ] Space m) {w : Sphere d} {δ : ℝ}
    (hδ : δ < 1) (hw : w ∈ directionSliceBand V δ) (x a : Space d) :
    ‖perpendicularPart (normalize (e (V.orthogonalProjectionOnto (w:Space d))))
      (e (V.orthogonalProjectionOnto x)-e (V.orthogonalProjectionOnto a))‖ ≤
      ‖perpendicularPart (w:Space d) (x-a)‖ := by
  rw [← slice_isometry_normalize V e,← map_sub,← slice_isometry_perpendicular V e,e.norm_map]
  exact slice_projected_tube_width V hδ hw x a

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Angular_CappedActiveCover
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Bounded anchor lists for every original direction label -/

namespace Falconer
open Set NormedSpace
open scoped ENNReal
variable {d h m : ℕ} {κ : Type*}

theorem cappedActiveAnchors_card (A : Fin h → Space d) (z : Space h)
    (J : Finset κ) (a : κ → Space d) (R : ℝ) {t : ℝ} (ht : 0 ≤ t) :
    ((cappedActiveAnchors A z J a R t).card : ℝ) ≤ t := by
  unfold cappedActiveAnchors
  split_ifs with hc
  · exact hc
  · simpa only [Finset.card_empty,Nat.cast_zero] using ht

theorem cappedActiveAnchors_eq (A : Fin h → Space d) (z : Space h)
    (J : Finset κ) (a : κ → Space d) (R : ℝ) {t : ℝ} (ht : 0 ≤ t)
    (hc : (gaussianActiveAnchorCount A J a R z : ℝ≥0∞) ≤ ENNReal.ofReal t) :
    cappedActiveAnchors A z J a R t = gaussianActiveAnchors A z J a R := by
  apply ite_eq_left
  apply (ENNReal.ofReal_le_ofReal_iff ht).mp
  simpa only [ENNReal.ofReal_natCast,gaussianActiveAnchors_card] using hc

theorem gaussian_capped_coordinate_cover
    (A : Fin h → Space d) (z : Space h)
    (e : (gaussianRowMap A).ker ≃ₗᵢ[ℝ] Space m)
    (E : Set (Space d × Sphere d)) (J : Sphere d → Finset κ) (a : κ → Space d)
    {δ ε D M K t : ℝ} (hM : 0 ≤ M) (hK : 0 ≤ K) (ht : 0 ≤ t)
    (hA : ∀ i, ‖A i‖ ≤ M)
    (hbound : ∀ x : Space d, ‖(gaussianRowMap A).kerᗮ.starProjection x‖ ≤ K*‖gaussianRowMap A x‖)
    (hsmall : K*((h:ℝ)*δ) < 1)
    (hbounded : ∀ u ∈ E, ‖u.1‖ ≤ D)
    (hanchor : ∀ w, ∀ i ∈ J w, ‖a i‖ ≤ D)
    (hcover : ∀ u ∈ E, ∃ i ∈ J u.2, ‖perpendicularPart (u.2:Space d) (u.1-a i)‖ ≤ ε)
    {x : Space d} {w : Sphere d}
    (hx : x ∈ gaussianPointBand A z δ) (hw : w ∈ gaussianDirectionBand A δ)
    (hE : ((A,z),(x,w)) ∈ gaussianActiveRelation E J a (δ+(2*D)*δ+ε*M) (ENNReal.ofReal t) true) :
    ∃ i ∈ cappedActiveAnchors A z (J w) a (δ+(2*D)*δ+ε*M) t,
      ‖perpendicularPart (normalize (e ((gaussianRowMap A).ker.orthogonalProjectionOnto (w:Space d))))
        (e ((gaussianRowMap A).ker.orthogonalProjectionOnto x)-
          e ((gaussianRowMap A).ker.orthogonalProjectionOnto (a i)))‖ ≤ ε := by
  classical
  obtain ⟨i,hi,hperp⟩ := hcover (x,w) hE.1
  have hlength := bounded_anchor_longitudinal (w := w) (hbounded (x,w) hE.1) (hanchor w i hi)
  have hactive : i ∈ gaussianActiveAnchors A z (J w) a (δ+(2*D)*δ+ε*M) :=
    Finset.mem_filter.mpr ⟨hi,gaussian_active_anchor A z hM hA hw hx hperp hlength⟩
  refine ⟨i,?_,?_⟩
  · rw [cappedActiveAnchors_eq A z (J w) a _ ht hE.2]
    exact hactive
  · exact (oriented_slice_tube_width (gaussianRowMap A).ker e hsmall
      (gaussian_direction_band_kernel_distance A hK hbound hw) x (a i)).trans hperp

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Slicing_DyadicSliceSelection
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Selecting a slice directly from the two original finite-scale ball bounds -/

namespace Falconer
open Set Metric MeasureTheory
open scoped ENNReal
variable {n h : ℕ} {κ : Type*} [Fintype κ] [DecidableEq κ]

theorem gaussianPruningWeight_eq (h : ℕ) (s : ℝ) {N : ℕ} (g : Fin (N+1)) :
    gaussianPruningWeight h s g = (1/(2:ℝ)^g.val)^(s-(h:ℝ)) := by
  unfold gaussianPruningWeight
  rw [one_div,Real.inv_rpow (by positivity),← Real.rpow_neg (by positivity)]
  congr 1
  ring

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Slicing_GaussianPlanarChart
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Every selected codimension-h slice in dimension h+2 has a controlled planar chart -/

namespace Falconer
open NormedSpace
variable {h : ℕ}

theorem gaussian_two_dimensional_slice_chart
    (B : Space h →ₗᵢ[ℝ] Space (h+2)) (A : Fin h → Space (h+2)) (w₀ : Sphere (h+2))
    {ε δ ρ : ℝ} (hε : 0 ≤ ε) (hδ : 0 ≤ δ) (hρ : 0 ≤ ρ)
    (hB : ∀ i, inner ℝ (w₀:Space (h+2)) (B (EuclideanSpace.basisFun (Fin h) ℝ i)) = 0)
    (hA : ∀ i, ‖A i-B (EuclideanSpace.basisFun (Fin h) ℝ i)‖ ≤ ε)
    (hstable : (h:ℝ)*ε ≤ 1/2)
    (hchart : 4*(h:ℝ)*δ+ρ+4*(h:ℝ)*ε ≤ 1/4) :
    ∃ e : (gaussianRowMap A).ker ≃ₗᵢ[ℝ] Space 2,
      normalize (e ((gaussianRowMap A).ker.orthogonalProjectionOnto (w₀:Space (h+2)))) =
        EuclideanSpace.basisFun (Fin 2) ℝ 0 ∧
      ∀ w : Sphere (h+2), w ∈ gaussianDirectionBand A δ → dist w w₀ ≤ ρ →
        ‖normalize (e ((gaussianRowMap A).ker.orthogonalProjectionOnto (w:Space (h+2))))‖ = 1 ∧
        dist (normalize (e ((gaussianRowMap A).ker.orthogonalProjectionOnto (w:Space (h+2)))))
          (EuclideanSpace.basisFun (Fin 2) ℝ 0) ≤ 1/4 := by
  have hpδ : 0 ≤ (h:ℝ)*δ := by positivity
  have hpε : 0 ≤ (h:ℝ)*ε := by positivity
  have hsδ : 2*((h:ℝ)*δ) < 1 := by nlinarith
  have hsε : 2*((h:ℝ)*ε) < 1 := by nlinarith
  have hbound := row_kernel_projection_bound A B hA hstable
  have hw₀ : w₀ ∈ gaussianDirectionBand A ε := by
    intro i
    have he : inner ℝ (w₀:Space (h+2)) (A i) =
        inner ℝ (w₀:Space (h+2)) (A i-B (EuclideanSpace.basisFun (Fin h) ℝ i)) := by
      rw [inner_sub_right,hB i,sub_zero]
    rw [he]
    exact (abs_real_inner_le_norm _ _).trans (by simpa only [sphere_norm,one_mul] using hA i)
  have hdim : Module.finrank ℝ (gaussianRowMap A).ker = 2 := by
    simpa only [Nat.add_sub_cancel_left] using row_kernel_finrank A B hA hstable
  obtain ⟨e,he⟩ := exists_oriented_slice_coordinates (gaussianRowMap A).ker hdim (by norm_num)
    (w₀:Space (h+2)) (gaussian_direction_kernel_nonzero A (by norm_num) hbound hsε hw₀)
  refine ⟨e,he,?_⟩
  intro w hw hclose
  have hn := gaussian_direction_kernel_nonzero A (by norm_num) hbound hsδ hw
  have hv : (gaussianRowMap A).ker.orthogonalProjectionOnto (w:Space (h+2)) ≠ 0 :=
    fun hz => hn (congrArg Subtype.val hz)
  have hev : e ((gaussianRowMap A).ker.orthogonalProjectionOnto (w:Space (h+2))) ≠ 0 :=
    fun hz => hv (e.injective (by simpa only [map_zero] using hz))
  refine ⟨norm_normalize hev,?_⟩
  have hd := oriented_slice_direction_distance (gaussianRowMap A).ker e hsδ hsε
    (gaussian_direction_band_kernel_distance A (by norm_num) hbound hw)
    (gaussian_direction_band_kernel_distance A (by norm_num) hbound hw₀) hclose
  rw [he] at hd
  exact hd.trans (by nlinarith)

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Geometry_PlanarChartRepair
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Choosing bounded representatives of almost-everywhere planar chart maps -/

namespace Falconer
open Set MeasureTheory

theorem boundedPlanarPoint_measurable : Measurable boundedPlanarPoint := by
  apply Measurable.ite (measurableSet_le (by fun_prop) measurable_const) measurable_id measurable_const

theorem chartedPlanarDirection_measurable : Measurable chartedPlanarDirection := by
  have hn : Measurable (fun w : Space 2 => ‖w‖) := continuous_norm.measurable
  have hd : Measurable (fun w : Space 2 => dist w (EuclideanSpace.basisFun (Fin 2) ℝ 0)) :=
    (continuous_id.dist continuous_const).measurable
  have hQ : MeasurableSet {w : Space 2 | ‖w‖ = 1 ∧
      dist w (EuclideanSpace.basisFun (Fin 2) ℝ 0) ≤ 1/4} :=
    (measurableSet_eq_fun hn measurable_const).inter
      (measurableSet_le hd measurable_const)
  exact Measurable.ite hQ measurable_id measurable_const

theorem boundedPlanarPoint_norm (x : Space 2) : ‖boundedPlanarPoint x‖ ≤ 1/4 := by
  unfold boundedPlanarPoint
  split_ifs with hx
  · exact hx
  · simp

theorem chartedPlanarDirection_unit (w : Space 2) : ‖chartedPlanarDirection w‖ = 1 := by
  unfold chartedPlanarDirection
  split_ifs with hw
  · exact hw.1
  · exact (EuclideanSpace.basisFun (Fin 2) ℝ).norm_eq_one 0

theorem chartedPlanarDirection_chart (w : Space 2) :
    dist (chartedPlanarDirection w) (EuclideanSpace.basisFun (Fin 2) ℝ 0) ≤ 1/4 := by
  unfold chartedPlanarDirection
  split_ifs with hw
  · exact hw.2
  · simp

theorem boundedPlanarPoint_eq {x : Space 2} (hx : ‖x‖ ≤ 1/4) : boundedPlanarPoint x = x :=
  ite_eq_left hx

theorem chartedPlanarDirection_eq {w : Space 2}
    (hw : ‖w‖ = 1 ∧ dist w (EuclideanSpace.basisFun (Fin 2) ℝ 0) ≤ 1/4) :
    chartedPlanarDirection w = w := ite_eq_left hw

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Estimates_PointSamples
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.sphereMeasure_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Separated point sets from samples with repeated coordinates

A maximal separated subfamily covers the sampled coordinates. The bound
on the multiplicity in a small ball then controls the loss in cardinality.
This is the point-selection step of `ang:planar-measures`.
-/

namespace Falconer
open Set
attribute [local instance] Classical.propDecidable

theorem exists_separated_cover (S : Finset (Space 2)) {δ : ℝ} (hδ : 0 ≤ δ) :
    ∃ P : Finset (Space 2), P ⊆ S ∧ FiniteSeparatedAt δ P ∧
      ∀ x ∈ S, ∃ y ∈ P, dist x y ≤ δ := by
  classical
  induction S using Finset.induction_on with
  | empty => exact ⟨∅, by simp, by simp [FiniteSeparatedAt], by simp⟩
  | @insert x S _ ih =>
    obtain ⟨P, hPS, hsep, hcover⟩ := ih
    by_cases hx : ∃ y ∈ P, dist x y ≤ δ
    · refine ⟨P, hPS.trans (Finset.subset_insert _ _), hsep, ?_⟩
      intro z hz
      rcases Finset.mem_insert.mp hz with rfl | hz
      · exact hx
      · exact hcover z hz
    · refine ⟨insert x P, Finset.insert_subset_insert x hPS, ?_, ?_⟩
      · intro u hu v hv hne
        rcases Finset.mem_insert.mp hu with hue | huP
        · rcases Finset.mem_insert.mp hv with hve | hvP
          · exact (hne (hue.trans hve.symm)).elim
          · rw [hue]
            exact (lt_of_not_ge (fun h => hx ⟨v, hvP, h⟩)).le
        · rcases Finset.mem_insert.mp hv with hve | hvP
          · rw [hve, dist_comm]
            exact (lt_of_not_ge (fun h => hx ⟨u, huP, h⟩)).le
          · exact hsep u huP v hvP hne
      · intro z hz
        rcases Finset.mem_insert.mp hz with hzx | hz
        · exact ⟨x, Finset.mem_insert_self _ _, by simpa only [hzx, dist_self] using hδ⟩
        · obtain ⟨y, hy, hdist⟩ := hcover z hz
          exact ⟨y, Finset.mem_insert_of_mem hy, hdist⟩

/-- Distinct selected coordinates in a ball cannot outnumber the original
sample labels in that ball. -/
theorem selected_points_ball_count {ι : Type*} [DecidableEq ι]
    (D : Finset ι) (p : ι → Space 2) (P : Finset (Space 2))
    (hP : P ⊆ D.image p) (z : Space 2) (r : ℝ) :
    (P.filter (fun x => dist x z ≤ r)).card ≤
      (D.filter (fun i => dist (p i) z ≤ r)).card := by
  classical
  have hsub : P.filter (fun x => dist x z ≤ r) ⊆
      (D.filter (fun i => dist (p i) z ≤ r)).image p := by
    intro x hx
    obtain ⟨hxP, hdist⟩ := Finset.mem_filter.mp hx
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp (hP hxP)
    exact Finset.mem_image.mpr ⟨i, Finset.mem_filter.mpr ⟨hi, hdist⟩, rfl⟩
  exact (Finset.card_le_card hsub).trans Finset.card_image_le

/-- Covering the original labels by the selected point balls gives the
lower cardinality bound, with all repeated labels counted. -/
theorem selected_points_card_lower {ι : Type*} [DecidableEq ι]
    (D : Finset ι) (p : ι → Space 2) (P : Finset (Space 2))
    {δ L : ℝ} (hcover : ∀ i ∈ D, ∃ x ∈ P, dist (p i) x ≤ δ)
    (hcount : ∀ x ∈ P, ((D.filter (fun i => dist (p i) x ≤ δ)).card : ℝ) ≤ L) :
    (D.card : ℝ) ≤ (P.card : ℝ) * L := by
  classical
  have hsub : D ⊆ P.biUnion (fun x => D.filter (fun i => dist (p i) x ≤ δ)) := by
    intro i hi
    obtain ⟨x, hx, hdist⟩ := hcover i hi
    exact Finset.mem_biUnion.mpr ⟨x, hx, Finset.mem_filter.mpr ⟨hi, hdist⟩⟩
  calc
    (D.card : ℝ) ≤ ((P.biUnion (fun x => D.filter
        (fun i => dist (p i) x ≤ δ))).card : ℝ) := by
      exact_mod_cast Finset.card_le_card hsub
    _ ≤ ∑ x ∈ P, ((D.filter (fun i => dist (p i) x ≤ δ)).card : ℝ) := by
      exact_mod_cast Finset.card_biUnion_le
    _ ≤ ∑ _x ∈ P, L := Finset.sum_le_sum hcount
    _ = (P.card : ℝ) * L := by simp

/-- The selected separated point set has the normalized finite ball
bound required by the published Furstenberg theorem. -/
theorem selected_points_normalized_ball_bound {ι : Type*} [DecidableEq ι]
    (D : Finset ι) (p : ι → Space 2) (P : Finset (Space 2))
    {δ K f : ℝ} (hδ : 0 < δ) (hK : 0 < K) (hD : D.Nonempty)
    (hP : P ⊆ D.image p)
    (hcover : ∀ i ∈ D, ∃ x ∈ P, dist (p i) x ≤ δ)
    (hsize : (D.card : ℝ) * δ ^ f ≤ 2)
    (hcount : ∀ z r, δ ≤ r → ((D.filter (fun i => dist (p i) z ≤ r)).card : ℝ) ≤
      K * (D.card : ℝ) * r ^ f) :
    NormalizedFiniteBallBound δ f (2 * K^2) P := by
  have hn : 0 < (D.card : ℝ) := by exact_mod_cast hD.card_pos
  have hlow := selected_points_card_lower D p P hcover (fun x _ => hcount x δ le_rfl)
  have hbase : 1 ≤ (P.card : ℝ) * K * δ ^ f := by
    apply (mul_le_mul_iff_right₀ hn).mp
    nlinarith [hlow]
  have hcoef : K * (D.card : ℝ) ≤ (2 * K^2) * (P.card : ℝ) := by
    have hmul := mul_le_mul_of_nonneg_right hbase (show 0 ≤ K * (D.card : ℝ) by positivity)
    have hupper := mul_le_mul_of_nonneg_left hsize
      (show 0 ≤ (P.card : ℝ) * K^2 by positivity)
    nlinarith
  intro z r hδr _
  calc
    ((P.filter (fun x => dist x z ≤ r)).card : ℝ) ≤
        ((D.filter (fun i => dist (p i) z ≤ r)).card : ℝ) := by
      exact_mod_cast selected_points_ball_count D p P hP z r
    _ ≤ K * (D.card : ℝ) * r ^ f := hcount z r hδr
    _ ≤ ((2 * K^2) * (P.card : ℝ)) * r ^ f :=
      mul_le_mul_of_nonneg_right hcoef (Real.rpow_nonneg (hδ.trans_le hδr).le _)
    _ = _ := by ring

theorem exists_separated_point_sample {ι : Type*} [DecidableEq ι]
    (D : Finset ι) (p : ι → Space 2) {δ K f : ℝ}
    (hδ : 0 < δ) (hK : 0 < K) (hD : D.Nonempty)
    (hsize : (D.card : ℝ) * δ ^ f ≤ 2)
    (hcount : ∀ z r, δ ≤ r → ((D.filter (fun i => dist (p i) z ≤ r)).card : ℝ) ≤
      K * (D.card : ℝ) * r ^ f) :
    ∃ P : Finset (Space 2), P.Nonempty ∧ P ⊆ D.image p ∧
      FiniteSeparatedAt δ P ∧ NormalizedFiniteBallBound δ f (2 * K^2) P := by
  obtain ⟨P, hP, hsep, hcover⟩ := exists_separated_cover (D.image p) hδ.le
  have hcover' : ∀ i ∈ D, ∃ x ∈ P, dist (p i) x ≤ δ :=
    fun i hi => hcover (p i) (Finset.mem_image.mpr ⟨i, hi, rfl⟩)
  obtain ⟨i, hi⟩ := hD
  obtain ⟨x, hx, _⟩ := hcover' i hi
  exact ⟨P, ⟨x, hx⟩, hP, hsep,
    selected_points_normalized_ball_bound D p P hδ hK ⟨i, hi⟩ hP hcover' hsize hcount⟩

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Estimates_SamplingTail
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Exponential tails for sampled incidence counts

The sample-count estimate in `ang:planar-measures` needs an exponential
tail even when the expected count is bounded. Applying Chernoff at the
fixed parameter one gives a sufficient bound without an asymptotic
binomial formula.
-/

namespace Falconer
open Set MeasureTheory ProbabilityTheory Real
open scoped BigOperators

private theorem exp_indicator_one {Ω : Type*} (A : Set Ω) (ω : Ω) :
    exp (A.indicator (fun _ => (1 : ℝ)) ω) =
      1 + (exp 1 - 1) * A.indicator (fun _ => (1 : ℝ)) ω := by
  classical
  by_cases h : ω ∈ A <;> simp [h]

/-- The exponential moment of a Bernoulli indicator at parameter one. -/
theorem indicator_mgf_one {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (A : Set Ω) (hA : MeasurableSet A) :
    mgf (A.indicator (fun _ => (1 : ℝ))) μ 1 = 1 + (exp 1 - 1) * μ.real A := by
  classical
  have hI : Integrable (A.indicator (fun _ => (1 : ℝ))) μ :=
    (integrable_const 1).indicator hA
  simp only [mgf, one_mul, exp_indicator_one]
  rw [integral_add (integrable_const 1) (hI.const_mul (exp 1 - 1)),
    integral_const_mul, integral_indicator_const (1 : ℝ) hA]
  simp

/-- The tail bound retains the actual small mean of each indicator. -/
theorem independent_indicator_sum_tail {Ω ι : Type*} [MeasurableSpace Ω]
    [DecidableEq ι] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (A : ι → Set Ω) (hA : ∀ i, MeasurableSet (A i))
    (hindep : iIndepFun (fun i => (A i).indicator (fun _ => (1 : ℝ))) μ)
    (S : Finset ι) {p T : ℝ} (_hp : 0 ≤ p) (hprob : ∀ i ∈ S, μ.real (A i) ≤ p) :
    μ.real {ω | T ≤ ∑ i ∈ S, (A i).indicator (fun _ => (1 : ℝ)) ω} ≤
      exp ((S.card : ℝ) * (exp 1 - 1) * p - T) := by
  classical
  let X : ι → Ω → ℝ := fun i => (A i).indicator (fun _ => (1 : ℝ))
  have hmeas : ∀ i, Measurable (X i) := fun i => measurable_const.indicator (hA i)
  have hint : ∀ i ∈ S, Integrable (fun ω => exp (1 * X i ω)) μ := by
    intro i _
    apply integrable_exp_mul_of_le 1 1 (by norm_num) (hmeas i).aemeasurable
    exact ae_of_all _ fun ω => by
      by_cases h : ω ∈ A i <;> simp [X, h]
  have hsumint := hindep.integrable_exp_mul_sum hmeas hint
  have hexp : 0 ≤ exp 1 - 1 := by
    have := exp_lt_exp.mpr (show (0 : ℝ) < 1 by norm_num)
    rw [exp_zero] at this
    linarith
  have hbound : ∀ i ∈ S, mgf (X i) μ 1 ≤ exp ((exp 1 - 1) * p) := by
    intro i hi
    rw [indicator_mgf_one μ (A i) (hA i)]
    calc
      1 + (exp 1 - 1) * μ.real (A i) ≤ 1 + (exp 1 - 1) * p := by
        gcongr
        exact hprob i hi
      _ ≤ exp ((exp 1 - 1) * p) := by simpa [add_comm] using add_one_le_exp ((exp 1 - 1) * p)
  have hprod : mgf (∑ i ∈ S, X i) μ 1 ≤ exp ((S.card : ℝ) * (exp 1 - 1) * p) := by
    rw [hindep.mgf_sum hmeas]
    calc
      ∏ i ∈ S, mgf (X i) μ 1 ≤ ∏ _i ∈ S, exp ((exp 1 - 1) * p) :=
        Finset.prod_le_prod (fun _ _ => mgf_nonneg) hbound
      _ = exp ((S.card : ℝ) * (exp 1 - 1) * p) := by
        rw [← exp_sum]
        simp [mul_assoc]
  have htail := measure_ge_le_exp_mul_mgf (μ := μ) (X := ∑ i ∈ S, X i) T
    (show (0 : ℝ) ≤ 1 by norm_num) hsumint
  calc
    μ.real {ω | T ≤ ∑ i ∈ S, (A i).indicator (fun _ => (1 : ℝ)) ω} ≤
        exp (-1 * T) * mgf (∑ i ∈ S, X i) μ 1 := by
      simpa only [Finset.sum_apply, X] using htail
    _ ≤ exp (-1 * T) * exp ((S.card : ℝ) * (exp 1 - 1) * p) :=
      mul_le_mul_of_nonneg_left hprod (exp_pos _).le
    _ = exp ((S.card : ℝ) * (exp 1 - 1) * p - T) := by
      rw [← exp_add]
      congr 1
      ring

/-- A threshold exceeding the exponential-moment mean by `L` fails with
probability at most `exp (-L)`. -/
theorem independent_indicator_sum_tail_le {Ω ι : Type*} [MeasurableSpace Ω]
    [DecidableEq ι] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (A : ι → Set Ω) (hA : ∀ i, MeasurableSet (A i))
    (hindep : iIndepFun (fun i => (A i).indicator (fun _ => (1 : ℝ))) μ)
    (S : Finset ι) {p T L : ℝ} (hp : 0 ≤ p) (hprob : ∀ i ∈ S, μ.real (A i) ≤ p)
    (hT : (S.card : ℝ) * (exp 1 - 1) * p + L ≤ T) :
    μ {ω | T ≤ ∑ i ∈ S, (A i).indicator (fun _ => (1 : ℝ)) ω} ≤
      ENNReal.ofReal (exp (-L)) := by
  have h := (independent_indicator_sum_tail μ A hA hindep S hp hprob).trans
    (exp_le_exp.mpr (by linarith : (S.card : ℝ) * (exp 1 - 1) * p - T ≤ -L))
  rw [← ENNReal.ofReal_toReal (measure_ne_top μ _)]
  exact ENNReal.ofReal_le_ofReal h

/-- Simultaneous sample-count bounds over any fixed finite collection of
cells. Independence is required only among the draws for each cell. -/
theorem finite_sample_count_failure {Ω ι κ : Type*} [MeasurableSpace Ω]
    [DecidableEq ι] [DecidableEq κ] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (B : Finset κ) (S : Finset ι) (A : κ → ι → Set Ω)
    (hA : ∀ j i, MeasurableSet (A j i))
    (hindep : ∀ j ∈ B,
      iIndepFun (fun i => (A j i).indicator (fun _ => (1 : ℝ))) μ)
    (p T : κ → ℝ) (L : ℝ) (hp : ∀ j ∈ B, 0 ≤ p j)
    (hprob : ∀ j ∈ B, ∀ i ∈ S, μ.real (A j i) ≤ p j)
    (hT : ∀ j ∈ B, (S.card : ℝ) * (exp 1 - 1) * p j + L ≤ T j) :
    μ (⋃ j ∈ B, {ω | T j ≤ ∑ i ∈ S, (A j i).indicator (fun _ => (1 : ℝ)) ω}) ≤
      ENNReal.ofReal ((B.card : ℝ) * exp (-L)) := by
  calc
    _ ≤ ∑ j ∈ B,
        μ {ω | T j ≤ ∑ i ∈ S, (A j i).indicator (fun _ => (1 : ℝ)) ω} :=
      measure_biUnion_finset_le _ _
    _ ≤ ∑ _j ∈ B, ENNReal.ofReal (exp (-L)) := by
      apply Finset.sum_le_sum
      intro j hj
      exact independent_indicator_sum_tail_le μ (A j) (hA j) (hindep j hj) S
        (hp j hj) (hprob j hj) (hT j hj)
    _ = _ := by simp [ENNReal.ofReal_mul, Nat.cast_nonneg]

/-- A small exceptional family of samples cannot carry all the expected
incidence. This is the probabilistic-method selection used after the
simultaneous count bound. -/
theorem exists_good_sample_incidence {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (J : Ω → ℝ) (hJ : Integrable J μ)
    (hJone : ∀ ω, J ω ≤ 1) (B : Set Ω) (hB : MeasurableSet B)
    {I : ℝ} (hI : 0 < I) (hmean : I ≤ ∫ ω, J ω ∂μ)
    (hbad : μ.real B ≤ I / 4) :
    ∃ ω ∉ B, I / 2 ≤ J ω := by
  classical
  by_contra h
  push Not at h
  have hpoint : ∀ ω, J ω ≤ I / 2 + B.indicator (fun _ => (1 : ℝ)) ω := by
    intro ω
    by_cases hω : ω ∈ B
    · simp only [indicator_of_mem hω]
      linarith [hJone ω]
    · simp only [indicator_of_notMem hω, add_zero]
      exact (h ω hω).le
  have hbound : (∫ ω, J ω ∂μ) ≤ I / 2 + μ.real B := by
    calc
      (∫ ω, J ω ∂μ) ≤ ∫ ω, I / 2 + B.indicator (fun _ => (1 : ℝ)) ω ∂μ :=
        integral_mono hJ ((integrable_const _).add ((integrable_const 1).indicator hB)) hpoint
      _ = _ := by
        rw [integral_add (integrable_const _) ((integrable_const 1).indicator hB),
          integral_indicator_const (1 : ℝ) hB]
        simp
  linarith

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Estimates_IidSampling
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Independent sampling of direction and point labels

The finite product law below samples the original labels, before their
geometric coordinates are taken. Repeated coordinates therefore retain
their original incidence fibers, as required by `ang:planar-measures`.
-/

namespace Falconer
open Set MeasureTheory ProbabilityTheory Real
open scoped BigOperators

theorem measurable_iidCount {X : Type*} [MeasurableSpace X] {A : Set X}
    (hA : MeasurableSet A) (n : ℕ) : Measurable (iidCount A (n := n)) := by
  apply Finset.measurable_sum
  intro i _
  exact (measurable_const.indicator hA).comp (measurable_pi_apply i)

private theorem iid_cell_mass {X : Type*} [MeasurableSpace X]
    (ν : ProbabilityMeasure X) (n : ℕ) (i : Fin n) (A : Set X) (hA : MeasurableSet A) :
    (iidLaw ν n).real {ω | ω i ∈ A} = (ν : Measure X).real A := by
  have hmass : iidLaw ν n {ω | ω i ∈ A} = (ν : Measure X) A := by
    calc
      iidLaw ν n {ω | ω i ∈ A} =
          ((iidLaw ν n).map (Function.eval i)) A :=
        (Measure.map_apply (measurable_pi_apply i) hA).symm
      _ = (ν : Measure X) A := by
        simpa only [iidLaw] using congrArg (fun μ : Measure X => μ A)
          (measurePreserving_eval (fun _ : Fin n => (ν : Measure X)) i).map_eq
  exact congrArg ENNReal.toReal hmass

private theorem iid_indicators_independent {X : Type*} [MeasurableSpace X]
    (ν : ProbabilityMeasure X) (n : ℕ) (A : Set X) (hA : MeasurableSet A) :
    iIndepFun (fun i : Fin n => {ω : Fin n → X | ω i ∈ A}.indicator
      (fun _ => (1 : ℝ))) (iidLaw ν n) := by
  have h := iIndepFun_pi (μ := fun _ : Fin n => (ν : Measure X))
    (X := fun _ : Fin n => A.indicator (fun _ => (1 : ℝ)))
    (fun _ => (measurable_const.indicator hA).aemeasurable)
  have heq : (fun (i : Fin n) (ω : Fin n → X) =>
      {ω : Fin n → X | ω i ∈ A}.indicator (fun _ => (1 : ℝ)) ω) =
      (fun (i : Fin n) (ω : Fin n → X) => A.indicator (fun _ => (1 : ℝ)) (ω i)) := by
    funext i ω
    by_cases hω : ω i ∈ A <;> simp [hω]
  rw [heq]
  exact h

/-- Counts are simultaneously controlled on every prescribed measurable
cell, with an exponentially small failure probability. -/
theorem iid_finite_cells_tail {X κ : Type*} [MeasurableSpace X] [DecidableEq κ]
    (ν : ProbabilityMeasure X) (n : ℕ) (B : Finset κ) (A : κ → Set X)
    (hA : ∀ j, MeasurableSet (A j)) (p T : κ → ℝ) (L : ℝ)
    (hp : ∀ j ∈ B, 0 ≤ p j)
    (hprob : ∀ j ∈ B, (ν : Measure X).real (A j) ≤ p j)
    (hT : ∀ j ∈ B, (n : ℝ) * (exp 1 - 1) * p j + L ≤ T j) :
    iidLaw ν n (⋃ j ∈ B, {ω | T j ≤ iidCount (A j) ω}) ≤
      ENNReal.ofReal ((B.card : ℝ) * exp (-L)) := by
  classical
  have h := finite_sample_count_failure (iidLaw ν n) B (Finset.univ : Finset (Fin n))
    (fun j i => {ω : Fin n → X | ω i ∈ A j})
    (fun j i => (hA j).preimage (measurable_pi_apply i))
    (fun j _ => iid_indicators_independent ν n (A j) (hA j)) p T L hp
    (fun j hj i _ => (iid_cell_mass ν n i (A j) (hA j)).trans_le (hprob j hj))
    (by simpa using hT)
  have heq : ∀ j (ω : Fin n → X),
      (∑ i : Fin n, {ω : Fin n → X | ω i ∈ A j}.indicator (fun _ => (1 : ℝ)) ω) =
      iidCount (A j) ω := by
    intro j ω
    apply Finset.sum_congr rfl
    intro i _
    by_cases hω : ω i ∈ A j <;> simp [hω]
  simpa only [heq] using h

theorem integrable_iidAverage {X : Type*} [MeasurableSpace X]
    (ν : ProbabilityMeasure X) {f : X → ℝ} (hf : Integrable f (ν : Measure X)) (n : ℕ) :
    Integrable (iidAverage f (n := n)) (iidLaw ν n) := by
  apply Integrable.const_mul
  apply integrable_finsetSum
  intro i _
  exact integrable_comp_eval hf

theorem integral_iidAverage {X : Type*} [MeasurableSpace X]
    (ν : ProbabilityMeasure X) {f : X → ℝ} (hf : Integrable f (ν : Measure X))
    {n : ℕ} (hn : 0 < n) :
    (∫ ω, iidAverage f ω ∂iidLaw ν n) = ∫ x, f x ∂(ν : Measure X) := by
  have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  have heval (i : Fin n) : (∫ ω, f (ω i) ∂iidLaw ν n) = ∫ x, f x ∂(ν : Measure X) := by
    exact integral_comp_eval (μ := fun _ : Fin n => (ν : Measure X)) hf.aestronglyMeasurable
  simp only [iidAverage]
  rw [integral_const_mul, integral_finsetSum]
  · simp_rw [heval]
    simp [hnR]
  · intro i _
    exact integrable_comp_eval hf

theorem iidAverage_le_one {X : Type*} (f : X → ℝ) (hf : ∀ x, f x ≤ 1)
    {n : ℕ} (hn : 0 < n) (ω : Fin n → X) : iidAverage f ω ≤ 1 := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  unfold iidAverage
  calc
    (n : ℝ)⁻¹ * ∑ i : Fin n, f (ω i) ≤ (n : ℝ)⁻¹ * ∑ _i : Fin n, (1 : ℝ) :=
      mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun _ _ => hf _)) (inv_nonneg.mpr hnR.le)
    _ = 1 := by simp [hnR.ne']

/-- Simultaneous cell bounds and at least half the expected incidence can
be achieved by one sample of the original labels. -/
theorem exists_iid_sample_with_counts_and_incidence {X κ : Type*}
    [MeasurableSpace X] [DecidableEq κ] (ν : ProbabilityMeasure X)
    {n : ℕ} (hn : 0 < n) (B : Finset κ) (A : κ → Set X)
    (hA : ∀ j, MeasurableSet (A j)) (p T : κ → ℝ) (L : ℝ)
    (hp : ∀ j ∈ B, 0 ≤ p j)
    (hprob : ∀ j ∈ B, (ν : Measure X).real (A j) ≤ p j)
    (hT : ∀ j ∈ B, (n : ℝ) * (exp 1 - 1) * p j + L ≤ T j)
    (f : X → ℝ) (hf : Integrable f (ν : Measure X)) (hf1 : ∀ x, f x ≤ 1)
    {I : ℝ} (hI : 0 < I) (hmean : I ≤ ∫ x, f x ∂(ν : Measure X))
    (hsmall : (B.card : ℝ) * exp (-L) ≤ I / 4) :
    ∃ ω : Fin n → X,
      (∀ j ∈ B, iidCount (A j) ω < T j) ∧ I / 2 ≤ iidAverage f ω := by
  classical
  let Bad : Set (Fin n → X) := ⋃ j ∈ B, {ω | T j ≤ iidCount (A j) ω}
  have hBad : MeasurableSet Bad := MeasurableSet.biUnion B.countable_toSet fun j _ =>
    measurableSet_le measurable_const (measurable_iidCount (hA j) n)
  have hmass : (iidLaw ν n).real Bad ≤ I / 4 := by
    have h := (iid_finite_cells_tail ν n B A hA p T L hp hprob hT).trans
      (ENNReal.ofReal_le_ofReal hsmall)
    have hr := ENNReal.toReal_mono ENNReal.ofReal_ne_top h
    simpa only [Bad, measureReal_def,
      ENNReal.toReal_ofReal (by positivity : (0 : ℝ) ≤ I / 4)] using hr
  obtain ⟨ω, hω, hinc⟩ := exists_good_sample_incidence (iidLaw ν n) (iidAverage f)
    (integrable_iidAverage ν hf n) (iidAverage_le_one f hf1 hn) Bad hBad hI
    (by simpa only [integral_iidAverage ν hf hn] using hmean) hmass
  refine ⟨ω, ?_, hinc⟩
  intro j hj
  apply lt_of_not_ge
  intro hbad
  exact hω (Set.mem_iUnion.mpr ⟨j, Set.mem_iUnion.mpr ⟨hj, hbad⟩⟩)

/-- For cell masses at most `K * s`, only the additive term `L` in the
sampling constant is needed to pay for simultaneous control, provided
the expected scale count `n * s` is at least one. -/
theorem exists_iid_sample_scale_counts {X κ : Type*}
    [MeasurableSpace X] [DecidableEq κ] (ν : ProbabilityMeasure X)
    {n : ℕ} (hn : 0 < n) (B : Finset κ) (A : κ → Set X)
    (hA : ∀ j, MeasurableSet (A j)) (s : κ → ℝ) {K L : ℝ}
    (hK : 0 ≤ K) (hL : 0 ≤ L)
    (hscale : ∀ j ∈ B, 1 ≤ (n : ℝ) * s j)
    (hprob : ∀ j ∈ B, (ν : Measure X).real (A j) ≤ K * s j)
    (f : X → ℝ) (hf : Integrable f (ν : Measure X)) (hf1 : ∀ x, f x ≤ 1)
    {I : ℝ} (hI : 0 < I) (hmean : I ≤ ∫ x, f x ∂(ν : Measure X))
    (hsmall : (B.card : ℝ) * exp (-L) ≤ I / 4) :
    ∃ ω : Fin n → X,
      (∀ j ∈ B, iidCount (A j) ω < ((exp 1 - 1) * K + L) * (n : ℝ) * s j) ∧
      I / 2 ≤ iidAverage f ω := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  apply exists_iid_sample_with_counts_and_incidence ν hn B A hA (fun j => K * s j)
    (fun j => ((exp 1 - 1) * K + L) * (n : ℝ) * s j) L _ hprob _ f hf hf1 hI hmean hsmall
  · intro j hj
    have hs : 0 ≤ s j := by nlinarith [hscale j hj]
    exact mul_nonneg hK hs
  · intro j hj
    have hLs := mul_le_mul_of_nonneg_left (hscale j hj) hL
    nlinarith

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Geometry_SamplingGrid
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.sphereMeasure_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Finite planar query balls for simultaneous iid estimates

Rounding one point of a ball to the spatial mesh and rounding its radius
up to an integer mesh multiple gives a query ball with radius at most
eight times the original radius. The number of queries is polynomial in
the reciprocal mesh. This is the finite-grid step in `ang:sample-caps`.
-/

namespace Falconer
open Set Metric MeasureTheory
attribute [local instance] Classical.propDecidable

theorem planarGrid_card (L : ℕ) : (planarGrid L).card = (2*L+1)^2 := by
  have hc : (Finset.Icc (-(L : ℤ)) (L : ℤ)).card = 2*L+1 := by
    rw [Int.card_Icc]
    omega
  simp [planarGrid, Fintype.card_piFinset, hc]

theorem planar_mesh_approximation {δ : ℝ} (hδ : 0 < δ) {L : ℕ}
    (hL : δ⁻¹ + 1 ≤ L) (x : Space 2) (hx : ∀ i, |x i| ≤ 1) :
    ∃ z ∈ planarGrid L, dist x (planarMesh δ z) ≤ 2*δ := by
  let z : Fin 2 → ℤ := fun i => ⌊x i / δ⌋
  have hcoord (i : Fin 2) : 0 ≤ x i - δ * (z i : ℝ) ∧
      x i - δ * (z i : ℝ) ≤ δ := by
    have hf := Int.floor_le (x i / δ)
    have hg := Int.lt_floor_add_one (x i / δ)
    have hf' := (le_div_iff₀ hδ).mp hf
    have hg' := (div_lt_iff₀ hδ).mp hg
    change 0 ≤ x i - δ * (⌊x i / δ⌋ : ℝ) ∧ _
    constructor <;> nlinarith
  have hz : z ∈ planarGrid L := by
    apply Fintype.mem_piFinset.mpr
    intro i
    apply Finset.mem_Icc.mpr
    have hf := Int.floor_le (x i / δ)
    have hg := Int.lt_floor_add_one (x i / δ)
    have hxb := abs_le.mp (hx i)
    have hd := (div_le_div_iff_of_pos_right hδ).mpr hxb.2
    have hd' := (div_le_div_iff_of_pos_right hδ).mpr hxb.1
    have hr : (-(L : ℝ)) ≤ (z i : ℝ) ∧ (z i : ℝ) ≤ L := by
      dsimp [z]
      rw [one_div] at hd
      norm_num only [neg_div, one_div] at hd'
      constructor <;> linarith
    exact_mod_cast hr
  refine ⟨z, hz, ?_⟩
  have hsq (i : Fin 2) : dist (x i) (planarMesh δ z i)^2 ≤ δ^2 := by
    rw [Real.dist_eq, sq_abs]
    change (x i - δ * (z i : ℝ))^2 ≤ δ^2
    exact (sq_le_sq₀ (hcoord i).1 hδ.le).mpr (hcoord i).2
  have hd := EuclideanSpace.dist_sq_eq x (planarMesh δ z)
  simp only [Fin.sum_univ_two] at hd
  nlinarith [hsq 0, hsq 1, dist_nonneg (x := x) (y := planarMesh δ z)]

theorem planarQueries_card (L H : ℕ) :
    (planarQueries L H).card = (2*L+1)^2 * H := by
  simp [planarQueries, planarGrid_card, Int.card_Icc]

theorem planar_ball_query {δ r : ℝ} (hδ : 0 < δ) (hδr : δ ≤ r) (hr : r ≤ 1)
    {L H : ℕ} (hL : δ⁻¹+1 ≤ L) (hH : δ⁻¹ ≤ H)
    {X : Type*} (p : X → Space 2) (hp : ∀ x i, |p x i| ≤ 1)
    (c : Space 2) (x₀ : X) (hx₀ : dist (p x₀) c ≤ r) :
    ∃ j ∈ planarQueries L H,
      {x | dist (p x) c ≤ r} ⊆ {x | dist (p x) (planarMesh δ j.1) ≤ 4*(j.2 : ℝ)*δ} ∧
      δ ≤ 4*(j.2 : ℝ)*δ ∧ 4*(j.2 : ℝ)*δ ≤ 8*r := by
  obtain ⟨z, hz, hclose⟩ := planar_mesh_approximation hδ hL (p x₀) (hp x₀)
  let m : ℤ := ⌈r/δ⌉
  have hmlo : (1 : ℤ) ≤ m := by
    have hh : (0 : ℝ) < r/δ := div_pos (hδ.trans_le hδr) hδ
    exact Int.add_one_le_iff.mpr (Int.ceil_pos.mpr hh)
  have hmhi : m ≤ (H : ℤ) := by
    apply Int.ceil_le.mpr
    have hh := (div_le_div_iff_of_pos_right hδ).mpr hr
    rw [one_div] at hh
    exact hh.trans hH
  have hmr : r ≤ (m : ℝ)*δ :=
    (div_le_iff₀ hδ).mp (Int.le_ceil (r/δ))
  have hmr' : (m : ℝ)*δ ≤ 2*r := by
    have hh := mul_lt_mul_of_pos_right (Int.ceil_lt_add_one (r/δ)) hδ
    rw [add_mul, div_mul_cancel₀ _ hδ.ne', one_mul] at hh
    change (⌈r/δ⌉ : ℝ)*δ ≤ 2*r
    nlinarith
  refine ⟨(z,m), Finset.mem_product.mpr ⟨hz, Finset.mem_Icc.mpr ⟨hmlo,hmhi⟩⟩, ?_, ?_, ?_⟩
  · intro x hx
    change dist (p x) c ≤ r at hx
    have ht := dist_triangle (p x) c (planarMesh δ z)
    have ht' := dist_triangle c (p x₀) (planarMesh δ z)
    rw [dist_comm c (p x₀)] at ht'
    change dist (p x) (planarMesh δ z) ≤ 4*(m : ℝ)*δ
    nlinarith
  · dsimp only
    nlinarith
  · dsimp only
    nlinarith

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Estimates_UniformSamples
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.sphereMeasure_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Uniform ball bounds for the original sampled labels

The finite query estimate is transferred to every ball, without identifying
labels that happen to have the same spatial coordinate.
-/

namespace Falconer
open Set Metric MeasureTheory Real
attribute [local instance] Classical.propDecidable

theorem iidCount_mono {X : Type*} {A B : Set X} (hAB : A ⊆ B)
    {n : ℕ} (ω : Fin n → X) : iidCount A ω ≤ iidCount B ω := by
  apply Finset.sum_le_sum
  intro i _
  by_cases h : ω i ∈ A
  · simp [h, hAB h]
  · simp only [Set.indicator_of_notMem h]
    by_cases h' : ω i ∈ B <;> simp [h']

theorem iidCount_le_card {X : Type*} (A : Set X) {n : ℕ} (ω : Fin n → X) :
    iidCount A ω ≤ n := by
  have hh : iidCount A ω ≤ iidCount Set.univ ω := iidCount_mono (subset_univ A) ω
  simpa [iidCount] using hh

theorem iidCount_eq_card_filter {X : Type*} (A : Set X) {n : ℕ} (ω : Fin n → X) :
    iidCount A ω = ((Finset.univ.filter (fun i => ω i ∈ A)).card : ℝ) := by
  simp [iidCount, Set.indicator_apply]

theorem uniform_ball_count_of_queries {X : Type*} {n L H : ℕ}
    (ω : Fin n → X) (p : X → Space 2) (hp : ∀ x i, |p x i| ≤ 1)
    {δ s T : ℝ} (hδ : 0 < δ) (hs : 0 ≤ s) (hT : 1 ≤ T)
    (hL : δ⁻¹+1 ≤ L) (hH : δ⁻¹ ≤ H)
    (hq : ∀ j ∈ planarQueries L H,
      iidCount {x | dist (p x) (planarMesh δ j.1) ≤ 4*(j.2 : ℝ)*δ} ω ≤
        T * (n : ℝ) * (4*(j.2 : ℝ)*δ)^s) :
    ∀ c r, δ ≤ r → iidCount {x | dist (p x) c ≤ r} ω ≤
      (T * 8^s) * (n : ℝ) * r^s := by
  intro c r hδr
  have hr0 : 0 < r := hδ.trans_le hδr
  have h8 : (1 : ℝ) ≤ 8^s := Real.one_le_rpow (by norm_num) hs
  by_cases hr : r ≤ 1
  · by_cases hex : ∃ i : Fin n, dist (p (ω i)) c ≤ r
    · obtain ⟨i, hi⟩ := hex
      obtain ⟨j, hj, hsub, hjpos, hjrad⟩ := planar_ball_query hδ hδr hr hL hH p hp c (ω i) hi
      have hh := (iidCount_mono hsub ω).trans (hq j hj)
      have hrpow := Real.rpow_le_rpow (hδ.le.trans hjpos) hjrad hs
      have he : (8*r)^s = (8 : ℝ)^s * r^s := Real.mul_rpow (by norm_num) hr0.le
      calc
        _ ≤ T * (n : ℝ) * (4*(j.2 : ℝ)*δ)^s := hh
        _ ≤ T * (n : ℝ) * (8*r)^s :=
          mul_le_mul_of_nonneg_left hrpow (by positivity)
        _ = _ := by rw [he]; ring
    · have hz : iidCount {x | dist (p x) c ≤ r} ω = 0 := by
        apply Finset.sum_eq_zero
        intro i _
        apply Set.indicator_of_notMem
        exact fun hi => hex ⟨i,hi⟩
      rw [hz]
      positivity
  · have hr1 : 1 ≤ r := le_of_not_ge hr
    have hrpow : 1 ≤ r^s := Real.one_le_rpow hr1 hs
    have hcoef : 1 ≤ (T * 8^s) * r^s := by
      have hh : (1 : ℝ) ≤ T * 8^s := one_le_mul_of_one_le_of_one_le hT h8
      exact one_le_mul_of_one_le_of_one_le hh hrpow
    calc
      _ ≤ (n : ℝ) := iidCount_le_card _ ω
      _ ≤ (n : ℝ) * ((T * 8^s) * r^s) := by
        exact le_mul_of_one_le_right (Nat.cast_nonneg n) hcoef
      _ = _ := by ring

/-- Simultaneous ball control and retained empirical incidence. The explicit
failure budget depends only on the polynomial number of grid queries. -/
theorem exists_uniform_ball_sample {X : Type*} [MeasurableSpace X]
    (ν : ProbabilityMeasure X) (p : X → Space 2) (hp : Measurable p)
    (hpbound : ∀ x i, |p x i| ≤ 1)
    {n L H : ℕ} (hn : 0 < n) {δ s K B I : ℝ}
    (hδ : 0 < δ) (hs : 0 ≤ s) (hK : 0 ≤ K) (hB : 1 ≤ B)
    (hL : δ⁻¹+1 ≤ L) (hH : δ⁻¹ ≤ H)
    (hsize : 1 ≤ (n : ℝ) * δ^s)
    (hprob : ∀ c r, δ ≤ r →
      (ν : Measure X).real {x | dist (p x) c ≤ r} ≤ K * r^s)
    (f : X → ℝ) (hf : Integrable f (ν : Measure X)) (hf1 : ∀ x, f x ≤ 1)
    (hI : 0 < I) (hmean : I ≤ ∫ x, f x ∂(ν : Measure X))
    (hsmall : (((2*L+1)^2 * H : ℕ) : ℝ) * exp (-B) ≤ I/4) :
    ∃ ω : Fin n → X,
      (∀ c r, δ ≤ r → iidCount {x | dist (p x) c ≤ r} ω ≤
        (((exp 1 - 1)*K+B) * 8^s) * (n : ℝ) * r^s) ∧
      I/2 ≤ iidAverage f ω := by
  let radius := fun j : (Fin 2 → ℤ) × ℤ => 4*(j.2 : ℝ)*δ
  let A := fun j => {x | dist (p x) (planarMesh δ j.1) ≤ radius j}
  have hrad (j) (hj : j ∈ planarQueries L H) : δ ≤ radius j := by
    have hm : (1 : ℤ) ≤ j.2 := (Finset.mem_Icc.mp (Finset.mem_product.mp hj).2).1
    have hm' : (1 : ℝ) ≤ j.2 := by exact_mod_cast hm
    dsimp [radius]
    nlinarith
  have hA (j) : MeasurableSet (A j) :=
    measurableSet_le (hp.dist measurable_const) measurable_const
  obtain ⟨ω, hω, hinc⟩ := exists_iid_sample_scale_counts ν hn
    (planarQueries L H) A hA (fun j => radius j ^ s) hK (zero_le_one.trans hB)
    (fun j hj => hsize.trans (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow hδ.le (hrad j hj) hs) (Nat.cast_nonneg n)))
    (fun j hj => hprob _ _ (hrad j hj)) f hf hf1 hI hmean
    (by simpa only [planarQueries_card] using hsmall)
  refine ⟨ω, ?_, hinc⟩
  have he : 0 ≤ exp 1 - 1 := sub_nonneg.mpr (Real.one_le_exp_iff.mpr (by norm_num))
  have hT : 1 ≤ (exp 1 - 1)*K+B := le_add_of_nonneg_left (mul_nonneg he hK) |>.trans' hB
  exact uniform_ball_count_of_queries ω p hpbound hδ hs hT hL hH
    (fun j hj => (hω j hj).le)

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Incidence_IncidenceSampling
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Incidence retained by the sampled labels

The first sample must preserve incidence as well as its direction counts.
The retained point set then consists of points with many incident sampled
labels. These assertions concern the original label spaces.
-/

namespace Falconer
open Set MeasureTheory

/-- At least a quarter of the incidence remains on the points whose
empirical incidence is at least a quarter. -/
theorem high_value_set_mass {X : Type*} [MeasurableSpace X]
    (μ : Measure X) [IsProbabilityMeasure μ] (f : X → ℝ)
    (hf : Measurable f) (hfi : Integrable f μ) (hf1 : ∀ x, f x ≤ 1)
    {I : ℝ} (hI : 0 < I) (hmean : I / 2 ≤ ∫ x, f x ∂μ) :
    I / 4 ≤ μ.real {x | I / 4 ≤ f x} := by
  classical
  let G := {x | I / 4 ≤ f x}
  have hG : MeasurableSet G := measurableSet_le measurable_const hf
  have hpoint : ∀ x, f x ≤ I / 4 + G.indicator (fun _ => (1 : ℝ)) x := by
    intro x
    by_cases hx : x ∈ G
    · simp only [indicator_of_mem hx]
      linarith [hf1 x]
    · simp only [indicator_of_notMem hx, add_zero]
      exact (lt_of_not_ge hx).le
  have hb : (∫ x, f x ∂μ) ≤ I / 4 + μ.real G := by
    calc
      _ ≤ ∫ x, I / 4 + G.indicator (fun _ => (1 : ℝ)) x ∂μ :=
        integral_mono hfi ((integrable_const _).add ((integrable_const 1).indicator hG)) hpoint
      _ = _ := by
        rw [integral_add (integrable_const _) ((integrable_const 1).indicator hG),
          integral_indicator_const (1 : ℝ) hG]
        simp
  change I / 4 ≤ μ.real G
  linarith

theorem integral_empirical_kernel {X W : Type*} [MeasurableSpace X]
    (μ : Measure X) (F : X → W → ℝ) (hF : ∀ w, Integrable (fun x => F x w) μ)
    {n : ℕ} (ω : Fin n → W) :
    (∫ x, iidAverage (F x) ω ∂μ) = iidAverage (fun w => ∫ x, F x w ∂μ) ω := by
  simp only [iidAverage]
  rw [integral_const_mul, integral_finsetSum _ (fun i _ => hF (ω i))]

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Incidence_IncidenceSamples
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.sphereMeasure_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Uniform sampling with incidence and good point labels

Both sampling stages use original probability laws. In the point stage,
the good labels are selected after sampling, so no measurable selection or
identification of coincident spatial coordinates is required.
-/

namespace Falconer
open Set MeasureTheory Real
attribute [local instance] Classical.propDecidable

theorem exists_uniform_incidence_sample {X W : Type*}
    [MeasurableSpace X] [MeasurableSpace W]
    (μ : ProbabilityMeasure X) (ν : ProbabilityMeasure W)
    (p : W → Space 2) (hp : Measurable p) (hpbound : ∀ w i, |p w i| ≤ 1)
    (F : X → W → ℝ) (hF : Measurable (Function.uncurry F))
    (hF0 : ∀ x w, 0 ≤ F x w) (hF1 : ∀ x w, F x w ≤ 1)
    {n L H : ℕ} (hn : 0 < n) {δ s K B I : ℝ}
    (hδ : 0 < δ) (hs : 0 ≤ s) (hK : 0 ≤ K) (hB : 1 ≤ B)
    (hL : δ⁻¹+1 ≤ L) (hH : δ⁻¹ ≤ H)
    (hsize : 1 ≤ (n : ℝ) * δ^s)
    (hprob : ∀ c r, δ ≤ r →
      (ν : Measure W).real {w | dist (p w) c ≤ r} ≤ K * r^s)
    (hI : 0 < I) (hmean : I ≤ ∫ w, ∫ x, F x w ∂(μ : Measure X) ∂(ν : Measure W))
    (hsmall : (((2*L+1)^2 * H : ℕ) : ℝ) * exp (-B) ≤ I/4) :
    ∃ ω : Fin n → W,
      (∀ c r, δ ≤ r → iidCount {w | dist (p w) c ≤ r} ω ≤
        (((exp 1 - 1)*K+B) * 8^s) * (n : ℝ) * r^s) ∧
      I/4 ≤ (μ : Measure X).real {x | I/4 ≤ iidAverage (F x) ω} := by
  have hFx (w : W) : Measurable (fun x => F x w) :=
    hF.comp (measurable_id.prodMk measurable_const)
  have hFi (w : W) : Integrable (fun x => F x w) (μ : Measure X) := by
    apply Integrable.of_bound (hFx w).aestronglyMeasurable 1
    filter_upwards with x
    simpa only [Real.norm_eq_abs, abs_of_nonneg (hF0 x w)] using hF1 x w
  have hIntegral : Measurable (fun w => ∫ x, F x w ∂(μ : Measure X)) :=
    hF.stronglyMeasurable.integral_prod_left.measurable
  have hIntegral0 (w : W) : 0 ≤ ∫ x, F x w ∂(μ : Measure X) :=
    integral_nonneg (fun x => hF0 x w)
  have hIntegral1 (w : W) : (∫ x, F x w ∂(μ : Measure X)) ≤ 1 := by
    simpa using integral_mono (hFi w) (integrable_const (1 : ℝ)) (fun x => hF1 x w)
  have hIntegrable : Integrable (fun w => ∫ x, F x w ∂(μ : Measure X)) (ν : Measure W) := by
    apply Integrable.of_bound hIntegral.aestronglyMeasurable 1
    filter_upwards with w
    simpa only [Real.norm_eq_abs, abs_of_nonneg (hIntegral0 w)] using hIntegral1 w
  obtain ⟨ω, hcounts, hmass⟩ := exists_uniform_ball_sample ν p hp hpbound hn
    hδ hs hK hB hL hH hsize hprob (fun w => ∫ x, F x w ∂(μ : Measure X))
    hIntegrable hIntegral1 hI hmean hsmall
  refine ⟨ω, hcounts, ?_⟩
  apply high_value_set_mass (μ : Measure X) (fun x => iidAverage (F x) ω)
  · unfold iidAverage
    exact measurable_const.mul (Finset.measurable_sum _ (fun i _ => hFx (ω i)))
  · unfold iidAverage
    exact (integrable_finsetSum _ (fun i _ => hFi (ω i))).const_mul _
  · intro x
    exact iidAverage_le_one (F x) (hF1 x) hn ω
  · exact hI
  · simpa only [integral_empirical_kernel (μ : Measure X) F hFi ω] using hmass

/-- Sample from the original point law, retain the labels in a positive
mass set, and extract a separated point set. Repeated coordinates cost only
the proved ball-count factor. -/
theorem exists_good_separated_point_sample {X : Type*} [MeasurableSpace X]
    (μ : ProbabilityMeasure X) (p : X → Space 2) (hp : Measurable p)
    (hpbound : ∀ x i, |p x i| ≤ 1)
    (G : Set X) (hG : MeasurableSet G) {J : ℝ} (hJ : 0 < J)
    (hGmass : J ≤ (μ : Measure X).real G)
    {n L H : ℕ} (hn : 0 < n) {δ s K B : ℝ}
    (hδ : 0 < δ) (hs : 0 ≤ s) (hK : 0 ≤ K) (hB : 1 ≤ B)
    (hL : δ⁻¹+1 ≤ L) (hH : δ⁻¹ ≤ H)
    (hsize : 1 ≤ (n : ℝ) * δ^s) (hsize' : (n : ℝ) * δ^s ≤ 2)
    (hprob : ∀ c r, δ ≤ r →
      (μ : Measure X).real {x | dist (p x) c ≤ r} ≤ K * r^s)
    (hsmall : (((2*L+1)^2 * H : ℕ) : ℝ) * exp (-B) ≤ J/4) :
    ∃ (ω : Fin n → X) (D : Finset (Fin n)) (P : Finset (Space 2)),
      D.Nonempty ∧ (∀ i ∈ D, ω i ∈ G) ∧ P.Nonempty ∧ P ⊆ D.image (p ∘ ω) ∧
      FiniteSeparatedAt δ P ∧
      NormalizedFiniteBallBound δ s
        (2 * (2 * (((exp 1-1)*K+B) * 8^s) / J)^2) P := by
  classical
  let f := G.indicator (fun _ => (1 : ℝ))
  have hf : Integrable f (μ : Measure X) := (integrable_const 1).indicator hG
  have hf1 (x : X) : f x ≤ 1 := by
    by_cases hx : x ∈ G <;> simp [f, hx]
  have hmean : J ≤ ∫ x, f x ∂(μ : Measure X) := by
    simpa only [f, integral_indicator_const (1 : ℝ) hG, smul_eq_mul, mul_one] using hGmass
  obtain ⟨ω, hcount, havg⟩ := exists_uniform_ball_sample μ p hp hpbound hn
    hδ hs hK hB hL hH hsize hprob f hf hf1 hJ hmean hsmall
  let D := Finset.univ.filter (fun i => ω i ∈ G)
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hDlow : J / 2 * n ≤ (D.card : ℝ) := by
    have he : iidAverage f ω = (n : ℝ)⁻¹ * (D.card : ℝ) := by
      change (n : ℝ)⁻¹ * iidCount G ω = _
      rw [iidCount_eq_card_filter]
    rw [he] at havg
    have hh := mul_le_mul_of_nonneg_left havg hnR.le
    simpa only [← mul_assoc, mul_inv_cancel₀ hnR.ne', one_mul, mul_comm] using hh
  have hDn : D.Nonempty := by
    apply Finset.card_pos.mp
    exact_mod_cast (mul_pos (div_pos hJ (by norm_num)) hnR).trans_le hDlow
  let T : ℝ := ((exp 1-1)*K+B)*8^s
  have hT : 0 < T := by
    have he : 0 ≤ exp 1 - 1 := sub_nonneg.mpr (Real.one_le_exp_iff.mpr (by norm_num))
    have hh : 0 < (exp 1-1)*K+B := lt_of_lt_of_le zero_lt_one
      (hB.trans (le_add_of_nonneg_left (mul_nonneg he hK)))
    exact mul_pos hh (Real.rpow_pos_of_pos (by norm_num) _)
  have hcoef : T * n ≤ (2*T/J) * (D.card : ℝ) := by
    rw [div_mul_eq_mul_div]
    apply (le_div_iff₀ hJ).mpr
    have hh := mul_le_mul_of_nonneg_left hDlow (by positivity : 0 ≤ 2*T)
    nlinarith
  have hDC (c : Space 2) (r : ℝ) (hr : δ ≤ r) :
      ((D.filter (fun i => dist ((p ∘ ω) i) c ≤ r)).card : ℝ) ≤
        (2*T/J) * (D.card : ℝ) * r^s := by
    have hsub : D.filter (fun i => dist ((p ∘ ω) i) c ≤ r) ⊆
        Finset.univ.filter (fun i => dist (p (ω i)) c ≤ r) := by
      intro i hi
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hi).2⟩
    calc
      _ ≤ iidCount {x | dist (p x) c ≤ r} ω := by
        rw [iidCount_eq_card_filter]
        exact_mod_cast Finset.card_le_card hsub
      _ ≤ T * (n : ℝ) * r^s := hcount c r hr
      _ ≤ _ := mul_le_mul_of_nonneg_right hcoef (Real.rpow_nonneg (hδ.le.trans hr) _)
  have hDs : (D.card : ℝ) * δ^s ≤ 2 := by
    have hcard : (D.card : ℝ) ≤ n := by
      have hh := Finset.card_filter_le (Finset.univ : Finset (Fin n)) (fun i => ω i ∈ G)
      have hh' : D.card ≤ n := by simpa only [Finset.card_univ, Fintype.card_fin] using hh
      exact_mod_cast hh'
    exact (mul_le_mul_of_nonneg_right hcard (Real.rpow_nonneg hδ.le _)).trans hsize'
  obtain ⟨P, hPn, hPD, hsep, hballs⟩ := exists_separated_point_sample D (p ∘ ω)
    hδ (div_pos (mul_pos (by norm_num) hT) hJ) hDn hDs hDC
  exact ⟨ω, D, P, hDn, fun i hi => (Finset.mem_filter.mp hi).2, hPn, hPD, hsep, hballs⟩

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Incidence_SampledFurstenberg
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.sphereMeasure_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# The published Furstenberg input applied to sampled incidence lists

The original direction labels may repeat their coordinates and may have
different covering families. All geometric lines are rounded to one grid
before applying the published cardinality bound.
-/

namespace Falconer
open Set
attribute [local instance] Classical.propDecidable

theorem sampled_furstenberg_obstruction
    (hpublished : PublishedPlanarFurstenberg) {b f : ℝ}
    (hb : 0 < b) (hb' : b ≤ 1 / 2) (hbf : b < f) (hf : f < 1) :
    ∃ ε δ₀ : ℝ, 0 < ε ∧ 0 < δ₀ ∧ δ₀ ≤ 1 / 2 ∧
    ∀ δ : ℝ, 0 < δ → δ < δ₀ →
    ∀ P : Finset (Space 2), P.Nonempty →
      (∀ x ∈ P, |x 0| ≤ 1 / 4 ∧ |x 1| ≤ 1 / 4) →
      FiniteSeparatedAt δ P → NormalizedFiniteBallBound δ f (δ^(-ε)) P →
    ∀ (ι : Type) [DecidableEq ι] (D : Finset ι) (m : ι → ℝ)
      (S : Space 2 → Finset ι) (U : ι → Finset (Space 2)) (K I : ℝ),
      0 < K → 0 < I → D.Nonempty →
      (D.card : ℝ) * δ^b ≤ 2 →
      (∀ i ∈ D, |m i| ≤ 1 / 2) →
      (∀ a r : ℝ, δ ≤ r → ((D.filter (fun i => |m i-a| ≤ r)).card : ℝ) ≤
        (K * (D.card : ℝ)) * r^b) →
      (∀ x ∈ P, S x ⊆ D ∧ I * (D.card : ℝ) ≤ ((S x).card : ℝ)) →
      2 * 2^b * K^2 / I ≤ δ^(-ε) →
      (D.card : ℝ) ≤ δ^(-b-ε/4) →
      (∀ i ∈ D, ((U i).card : ℝ) ≤ δ^(-b-ε/4)) →
      (∀ x ∈ P, ∀ i ∈ S x, roundedIncidentLine δ x (m i) ∈ U i) → False := by
  obtain ⟨ε, δ₁, hε, hδ₁, _, hF⟩ :=
    published_furstenberg_labelled_obstruction hpublished hb hb' hbf hf
  refine ⟨ε, min δ₁ (1/2), hε, lt_min hδ₁ (by norm_num), min_le_right _ _, ?_⟩
  intro δ hδ hδsmall P hP hchart hsep hpoint ι _ D m S U K I hK hI hD
    hsize hm hcount hS hloss hDcard hU hcover
  have hδ1 : δ ≤ 1 / 2 := hδsmall.le.trans (min_le_right _ _)
  let T : Space 2 → Finset (Space 2) := fun x => roundedLineFamily δ x m (S x)
  have hT (x : Space 2) (hx : x ∈ P) :
      (T x).Nonempty ∧ InBoundedLineChart (T x) ∧ FiniteSeparatedAt δ (T x) ∧
      NormalizedFiniteBallBound δ b (δ^(-ε)) (T x) ∧
      ∀ l ∈ T x, TubeIncident δ x l := by
    have hSn : (S x).Nonempty := by
      apply Finset.card_pos.mp
      have hn : (0 : ℝ) < D.card := by exact_mod_cast hD.card_pos
      have hspos := (mul_pos hI hn).trans_le (hS x hx).2
      exact_mod_cast hspos
    refine ⟨roundedLineFamily_nonempty δ x m hSn, ?_,
      roundedIncidentLine_family_separated hδ x m (S x), ?_, ?_⟩
    · intro l hl
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hl
      exact roundedIncidentLine_in_chart hδ hδ1 x (hchart x hx).1 (hchart x hx).2
        (m i) (hm i ((hS x hx).1 hi))
    · have hn := roundedLineFamily_normalized_of_large_sample hδ hK hI x m D (S x)
        hD (hS x hx).1 hsize (hS x hx).2 hcount
      intro z r hδr hr
      apply (hn z r hδr hr).trans
      apply mul_le_mul_of_nonneg_right _ (Nat.cast_nonneg _)
      exact mul_le_mul_of_nonneg_right hloss (Real.rpow_nonneg (hδ.trans_le hδr).le _)
    · intro l hl
      obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hl
      exact roundedIncidentLine_incident hδ x (m i)
  have hPchart : InBoundedLineChart P := by
    intro x hx
    exact ⟨(hchart x hx).1.trans (by norm_num), (hchart x hx).2.trans (by norm_num)⟩
  apply hF δ hδ (hδsmall.trans_le (min_le_left _ _)) P hP hPchart hsep hpoint T hT
    ι D U hDcard hU
  intro x hx l hl
  obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hl
  exact ⟨i, (hS x hx).1 hi, hcover x hx i hi⟩

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Estimates_PlanarSampling
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.sphereMeasure_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Original labels, slope coordinates and prescribed strip covers

These adapters connect the two uniform sampling stages to the exact finite
Furstenberg obstruction. Every strip list remains indexed by its original
direction label, including when slope coordinates coincide.
-/

namespace Falconer
open Set MeasureTheory
attribute [local instance] Classical.propDecidable

theorem continuous_slopePoint : Continuous slopePoint := by
  change Continuous (fun m : ℝ => WithLp.toLp 2 ![m,0])
  apply (PiLp.continuous_toLp 2 _).comp
  fun_prop

theorem slopePoint_dist (s t : ℝ) : dist (slopePoint s) (slopePoint t) = |s-t| := by
  have hh := EuclideanSpace.dist_sq_eq (slopePoint s) (slopePoint t)
  simp only [Fin.sum_univ_two, slopePoint_zero, slopePoint_one, Real.dist_eq, sq_abs] at hh
  nlinarith [dist_nonneg (x := slopePoint s) (y := slopePoint t), abs_nonneg (s-t), sq_abs (s-t)]

theorem slopePoint_ball_mass_le {W : Type*} [MeasurableSpace W]
    (ν : ProbabilityMeasure W) (m : W → ℝ) {δ b K : ℝ}
    (hb : ∀ a r, δ ≤ r → (ν : Measure W).real {w | |m w-a| ≤ r} ≤ K*r^b)
    (c : Space 2) (r : ℝ) (hr : δ ≤ r) :
    (ν : Measure W).real {w | dist (slopePoint (m w)) c ≤ r} ≤ K*r^b := by
  apply le_trans (measureReal_mono (μ := (ν : Measure W)) ?_) (hb (c 0) r hr)
  intro w hw
  exact (show |m w-c 0| ≤ dist (slopePoint (m w)) c by
    simpa only [slopePoint_zero, Real.dist_eq] using
      PiLp.dist_apply_le (slopePoint (m w)) c 0).trans hw

theorem empirical_incidence_eq_card {X W : Type*} (E : X → W → Prop)
    {n : ℕ} (ω : Fin n → W) (x : X) :
    iidAverage (fun w => if E x w then (1 : ℝ) else 0) ω =
      (n : ℝ)⁻¹ * ((incidentLabels E ω x).card : ℝ) := by
  change (n : ℝ)⁻¹ * iidCount {w | E x w} ω = _
  rw [iidCount_eq_card_filter]
  rfl

theorem empirical_incidence_card_lower {X W : Type*} (E : X → W → Prop)
    {n : ℕ} (hn : 0 < n) (ω : Fin n → W) (x : X) {I : ℝ}
    (hI : I ≤ iidAverage (fun w => if E x w then (1 : ℝ) else 0) ω) :
    I * (n : ℝ) ≤ ((incidentLabels E ω x).card : ℝ) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  rw [empirical_incidence_eq_card] at hI
  have hh := mul_le_mul_of_nonneg_left hI hnR.le
  simpa only [← mul_assoc, mul_inv_cancel₀ hnR.ne', one_mul, mul_one, mul_comm] using hh

theorem stripLineCandidates_card_le (δ m : ℝ) (A : Finset ℝ) (L : ℕ) :
    (stripLineCandidates δ m A L).card ≤ A.card * (2*L+1) := by
  calc
    _ ≤ ∑ a ∈ A, (roundedStripCandidates δ m a L).card := Finset.card_biUnion_le
    _ ≤ ∑ _a ∈ A, (2*L+1) := Finset.sum_le_sum (fun a _ => roundedStripCandidates_card_le δ m a L)
    _ = _ := by simp

theorem roundedIncidentLine_mem_stripLineCandidates {δ C m : ℝ}
    (hδ : 0 < δ) (A : Finset ℝ) (L : ℕ) (hL : C+2 ≤ (L : ℝ))
    (x : Space 2) (hx : |x 0| ≤ 1)
    (hcover : ∃ a ∈ A, |x 1-m*x 0-a| ≤ C*δ) :
    roundedIncidentLine δ x m ∈ stripLineCandidates δ m A L := by
  obtain ⟨a, ha, hb⟩ := hcover
  exact Finset.mem_biUnion.mpr ⟨a, ha, roundedIncidentLine_mem_candidates hδ x hx hb L hL⟩

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Incidence_PlanarIncidence
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.sphereMeasure_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Quantitative planar measure incidence obstruction

This is the measure-to-finite-set step of `ang:planar-measures`. The only
published input is the finite-set specialization of the planar
Furstenberg theorem. All losses from the two original-label sampling steps
are explicit; no geometric gain is assumed.
-/

namespace Falconer
open Set MeasureTheory Real
attribute [local instance] Classical.propDecidable

theorem samplingBallLoss_pos {K B s : ℝ} (hK : 0 ≤ K) (hB : 1 ≤ B) :
    0 < samplingBallLoss K B s := by
  have he : 0 ≤ exp 1-1 := sub_nonneg.mpr (Real.one_le_exp_iff.mpr (by norm_num))
  apply mul_pos
  · exact lt_of_lt_of_le zero_lt_one (hB.trans (le_add_of_nonneg_left (mul_nonneg he hK)))
  · exact Real.rpow_pos_of_pos (by norm_num) _

theorem planar_measure_incidence_obstruction
    (hpublished : PublishedPlanarFurstenberg) {b f : ℝ}
    (hb : 0 < b) (hb' : b ≤ 1/2) (hbf : b < f) (hf : f < 1) :
    ∃ ε δ₀ : ℝ, 0 < ε ∧ 0 < δ₀ ∧ δ₀ ≤ 1/2 ∧
    ∀ δ : ℝ, 0 < δ → δ < δ₀ →
    ∀ (X W : Type) [MeasurableSpace X] [MeasurableSpace W]
      (μ : ProbabilityMeasure X) (ν : ProbabilityMeasure W)
      (p : X → Space 2) (m : W → ℝ) (E : X → W → Prop),
      Measurable p → Measurable m → MeasurableSet {z : X × W | E z.1 z.2} →
      (∀ x, |p x 0| ≤ 1/4 ∧ |p x 1| ≤ 1/4) → (∀ w, |m w| ≤ 1/2) →
    ∀ (K B I : ℝ) (n l L H J : ℕ) (A : W → Finset ℝ),
      0 ≤ K → 1 ≤ B → 0 < I → 0 < n → 0 < l →
      δ⁻¹+1 ≤ L → δ⁻¹ ≤ H →
      1 ≤ (n : ℝ)*δ^b → (n : ℝ)*δ^b ≤ 2 →
      1 ≤ (l : ℝ)*δ^f → (l : ℝ)*δ^f ≤ 2 →
      (∀ c r, δ ≤ r → (μ : Measure X).real {x | dist (p x) c ≤ r} ≤ K*r^f) →
      (∀ a r, δ ≤ r → (ν : Measure W).real {w | |m w-a| ≤ r} ≤ K*r^b) →
      I ≤ (∫ w, ∫ x, if E x w then (1 : ℝ) else 0 ∂(μ : Measure X) ∂(ν : Measure W)) →
      (((2*L+1)^2*H : ℕ) : ℝ)*exp (-B) ≤ I/16 →
      2*(8*samplingBallLoss K B f/I)^2 ≤ δ^(-ε) →
      8*2^b*(samplingBallLoss K B b)^2/I ≤ δ^(-ε) →
      (n : ℝ) ≤ δ^(-b-ε/4) →
      (∀ w, ((A w).card * (2*J+1) : ℕ) ≤ δ^(-b-ε/4)) →
      (∀ x w, E x w → ∃ a ∈ A w, |p x 1-m w*p x 0-a| ≤ ((J : ℝ)-2)*δ) →
      False := by
  obtain ⟨ε, δ₀, hε, hδ₀, hδ₀', hFurst⟩ :=
    sampled_furstenberg_obstruction hpublished hb hb' hbf hf
  refine ⟨ε, δ₀, hε, hδ₀, hδ₀', ?_⟩
  intro δ hδ hδsmall X W _ _ μ ν p m E hp hm hE hpchart hmchart
    K B I n l L H J A hK hB hI hn hl hL hH hnsize hnsize' hlsize hlsize'
    hpball hmball hmean hfail hPloss hTloss hnc hAc hcover
  let F : X → W → ℝ := fun x w => if E x w then 1 else 0
  have hF : Measurable (Function.uncurry F) := by
    exact measurable_const.indicator hE
  have hF0 (x : X) (w : W) : 0 ≤ F x w := by simp only [F]; split <;> norm_num
  have hF1 (x : X) (w : W) : F x w ≤ 1 := by simp only [F]; split <;> norm_num
  have hmbound (w : W) (i : Fin 2) : |slopePoint (m w) i| ≤ 1 := by
    fin_cases i
    · exact (hmchart w).trans (by norm_num)
    · simp
  obtain ⟨ω, hω, hgood⟩ := exists_uniform_incidence_sample μ ν (slopePoint ∘ m)
    (continuous_slopePoint.measurable.comp hm) hmbound F hF hF0 hF1 hn hδ hb.le hK hB
    hL hH hnsize (slopePoint_ball_mass_le ν m hmball) hI hmean (hfail.trans (by linarith))
  let G := {x | I/4 ≤ iidAverage (F x) ω}
  have hG : MeasurableSet G := by
    apply measurableSet_le measurable_const
    unfold iidAverage
    apply measurable_const.mul
    apply Finset.measurable_sum
    intro i _
    exact hF.comp (measurable_id.prodMk measurable_const)
  have hpbound (x : X) (i : Fin 2) : |p x i| ≤ 1 := by
    fin_cases i
    · exact (hpchart x).1.trans (by norm_num)
    · exact (hpchart x).2.trans (by norm_num)
  obtain ⟨ξ, D, P, hDn, hDG, hPn, hPD, hPsep, hPball⟩ :=
    exists_good_separated_point_sample μ p hp hpbound G hG (by positivity : 0 < I/4)
      hgood hl hδ (hb.trans hbf).le hK hB hL hH hlsize hlsize' hpball
      (by convert hfail using 1; ring)
  have hrep : ∀ x ∈ P, ∃ y : X, p y = x ∧ y ∈ G := by
    intro x hx
    obtain ⟨i, hi, hix⟩ := Finset.mem_image.mp (hPD hx)
    exact ⟨ξ i, hix, hDG i hi⟩
  let rep : {x // x ∈ P} → X := fun x => Classical.choose (hrep x.val x.property)
  have hrep' (x : Space 2) (hx : x ∈ P) : p (rep ⟨x,hx⟩) = x ∧ rep ⟨x,hx⟩ ∈ G :=
    Classical.choose_spec (hrep x hx)
  let S : Space 2 → Finset (Fin n) := fun x =>
    if hx : x ∈ P then incidentLabels E ω (rep ⟨x,hx⟩) else ∅
  let U : Fin n → Finset (Space 2) := fun i =>
    stripLineCandidates δ (m (ω i)) (A (ω i)) J
  have hPchart (x : Space 2) (hx : x ∈ P) : |x 0| ≤ 1/4 ∧ |x 1| ≤ 1/4 := by
    rw [← (hrep' x hx).1]
    exact hpchart _
  have hPbound : NormalizedFiniteBallBound δ f (δ^(-ε)) P := by
    have he : 2*(2*samplingBallLoss K B f/(I/4))^2 =
        2*(8*samplingBallLoss K B f/I)^2 := by ring
    change NormalizedFiniteBallBound δ f (2*(2*samplingBallLoss K B f/(I/4))^2) P at hPball
    rw [he] at hPball
    intro c r hdr hr1
    apply (hPball c r hdr hr1).trans
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hPloss
      (Real.rpow_nonneg (hδ.le.trans hdr) _)) (Nat.cast_nonneg _)
  have hcount (a r : ℝ) (hdr : δ ≤ r) :
      (((Finset.univ : Finset (Fin n)).filter (fun i => |m (ω i)-a| ≤ r)).card : ℝ) ≤
        (samplingBallLoss K B b * ((Finset.univ : Finset (Fin n)).card : ℝ))*r^b := by
    have hh := hω (slopePoint a) r hdr
    simpa only [Function.comp_apply, slopePoint_dist, iidCount_eq_card_filter,
      Finset.card_univ, Fintype.card_fin, Set.mem_ofPred_eq, samplingBallLoss] using hh
  apply hFurst δ hδ hδsmall P hPn hPchart hPsep hPbound (Fin n) Finset.univ
    (m ∘ ω) S U (samplingBallLoss K B b) (I/4)
    (samplingBallLoss_pos hK hB) (by positivity) ⟨⟨0,hn⟩, Finset.mem_univ _⟩
    (by simpa using hnsize') (fun i _ => hmchart (ω i)) hcount
  · intro x hx
    constructor
    · exact Finset.subset_univ _
    · simp only [S, dite_eq_left hx, Finset.card_univ, Fintype.card_fin]
      exact empirical_incidence_card_lower E hn ω _ (hrep' x hx).2
  · convert hTloss using 1; ring
  · simpa using hnc
  · intro i _
    exact (show ((U i).card : ℝ) ≤ ((A (ω i)).card * (2*J+1) : ℕ) by
      exact_mod_cast stripLineCandidates_card_le δ (m (ω i)) (A (ω i)) J).trans (hAc (ω i))
  · intro x hx i hi
    have hiy : E (rep ⟨x,hx⟩) (ω i) := by
      simpa only [S, dite_eq_left hx, incidentLabels, Finset.mem_filter, Finset.mem_univ, true_and] using hi
    apply roundedIncidentLine_mem_stripLineCandidates (C := (J : ℝ)-2) hδ _ J (by linarith)
      x ((hPchart x hx).1.trans (by norm_num))
    obtain ⟨a, ha, he⟩ := hcover _ _ hiy
    rw [(hrep' x hx).1] at he
    exact ⟨a,ha,he⟩

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Estimates_SamplingScales
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Rounding and scale budgets for planar sampling

The sample sizes are ceilings of the reciprocal dimension powers. Query
counts grow at most cubically in the reciprocal scale, while the chosen
exponential tail decays with the tenth power of that scale.
-/

namespace Falconer
open Real Filter
open scoped Topology

theorem sampling_ceil_size {δ s : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hs : 0 ≤ s) :
    0 < Nat.ceil (δ^(-s)) ∧
      1 ≤ (Nat.ceil (δ^(-s)) : ℝ)*δ^s ∧
      (Nat.ceil (δ^(-s)) : ℝ)*δ^s ≤ 2 := by
  have hp : 0 < δ^(-s) := Real.rpow_pos_of_pos hδ _
  have hδs : δ^s ≤ 1 := Real.rpow_le_one hδ.le hδ1 hs
  have hprod : δ^(-s)*δ^s = 1 := by
    rw [← Real.rpow_add hδ, neg_add_cancel, Real.rpow_zero]
  refine ⟨Nat.ceil_pos.mpr hp, ?_, ?_⟩
  · exact hprod ▸ mul_le_mul_of_nonneg_right (Nat.le_ceil _) (Real.rpow_nonneg hδ.le _)
  · have hh := mul_le_mul_of_nonneg_right (Nat.ceil_lt_add_one hp.le).le
      (Real.rpow_nonneg hδ.le s)
    rw [add_mul, hprod, one_mul] at hh
    linarith

theorem sampling_query_card_bound {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    (((2 * Nat.ceil (δ⁻¹+1)+1)^2 * Nat.ceil δ⁻¹ : ℕ) : ℝ) ≤ 98*δ⁻¹^3 := by
  have hi : (1 : ℝ) ≤ δ⁻¹ := (one_le_inv₀ hδ).mpr hδ1
  have hL := (Nat.ceil_lt_add_one (by positivity : 0 ≤ δ⁻¹+1)).le
  have hH := (Nat.ceil_lt_add_one (inv_nonneg.mpr hδ.le)).le
  have hLb : (2 * Nat.ceil (δ⁻¹+1)+1 : ℝ) ≤ 7*δ⁻¹ := by linarith
  have hHb : (Nat.ceil δ⁻¹ : ℝ) ≤ 2*δ⁻¹ := by linarith
  push_cast
  calc
    _ ≤ (7*δ⁻¹)^2 * (2*δ⁻¹) := mul_le_mul
      (pow_le_pow_left₀ (by positivity) hLb 2) hHb (by positivity) (by positivity)
    _ = _ := by ring

theorem sampling_exponential_tail {δ : ℝ} (hδ : 0 < δ) :
    exp (-(-10*log δ)) = δ^10 := by
  rw [show -(-10*log δ) = (10 : ℕ)*log δ by ring, Real.exp_nat_mul, Real.exp_log hδ]

theorem sampling_failure_bound {δ : ℝ} (hδ : 0 < δ) (hδsmall : δ ≤ 1/4) :
    (((2 * Nat.ceil (δ⁻¹+1)+1)^2 * Nat.ceil δ⁻¹ : ℕ) : ℝ) *
      exp (-(-10*log δ)) ≤ δ/16 := by
  rw [sampling_exponential_tail hδ]
  have hb := mul_le_mul_of_nonneg_right (sampling_query_card_bound hδ (by linarith))
    (pow_nonneg hδ.le 10)
  have he : (98*δ⁻¹^3)*δ^10 = 98*δ^7 := by
    field_simp
  rw [he] at hb
  have hh := pow_le_pow_left₀ hδ.le hδsmall 6
  have hf : 98*δ^7 ≤ δ/16 := by nlinarith [mul_le_mul_of_nonneg_left hh hδ.le]
  exact hb.trans hf

theorem sampling_log_budget {η : ℝ} (hη : 0 < η) :
    ∀ᶠ δ in 𝓝[>] (0 : ℝ), -10*log δ ≤ δ^(-η) := by
  have h := (isLittleO_log_rpow_nhdsGT_zero (neg_neg_of_pos hη)).def
    (show (0 : ℝ) < 1/10 by norm_num)
  filter_upwards [h, self_mem_nhdsWithin] with δ hbound hδ
  have hδp : 0 < δ := hδ
  rw [Real.norm_eq_abs, Real.norm_eq_abs,
    abs_of_pos (Real.rpow_pos_of_pos hδp _)] at hbound
  have hh := neg_le_abs (log δ)
  nlinarith

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Estimates_PlanarGainNumerics
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Absorbing the explicit losses in the planar measure obstruction

Only fixed constants, logarithms and ceilings are absorbed here. The
underlying incidence estimate has already been proved from the cited
published input.
-/

namespace Falconer
open Real Filter
open scoped Topology

theorem samplingBallLoss_le {δ η B s : ℝ} (hB : B ≤ δ^(-η)) :
    samplingBallLoss (δ^(-η)) B s ≤ (exp 1 * 8^s) * δ^(-η) := by
  unfold samplingBallLoss
  have hh : (exp 1-1)*δ^(-η)+B ≤ exp 1*δ^(-η) := by linarith
  calc
    _ ≤ (exp 1*δ^(-η))*8^s := mul_le_mul_of_nonneg_right hh (by positivity)
    _ = _ := by ring

theorem rpow_absorb_constant {δ t u C : ℝ} (hδ : 0 < δ)
    (hC : C ≤ δ^(-(u-t))) : C * δ^(-t) ≤ δ^(-u) := by
  calc
    _ ≤ δ^(-(u-t)) * δ^(-t) := mul_le_mul_of_nonneg_right hC (by positivity)
    _ = _ := by rw [← Real.rpow_add hδ]; congr 1; ring

theorem sampling_point_loss_le {δ η Tf C : ℝ} (hδ : 0 < δ)
    (hTf : 0 ≤ Tf) (hT : Tf ≤ C*δ^(-η)) :
    2*(8*Tf/δ^η)^2 ≤ (128*C^2)*δ^(-4*η) := by
  have hh : 0 ≤ 8*Tf/δ^η := by positivity
  have hq : 8*Tf/δ^η ≤ 8*(C*δ^(-η))/δ^η := by gcongr
  have he : (δ^(-η)/δ^η)^2 = δ^(-4*η) := by
    rw [← Real.rpow_sub hδ, ← Real.rpow_natCast, ← Real.rpow_mul hδ.le]
    congr 1
    ring
  calc
    _ ≤ 2*(8*(C*δ^(-η))/δ^η)^2 :=
      mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hh hq 2) (by norm_num)
    _ = (128*C^2)*(δ^(-η)/δ^η)^2 := by ring
    _ = _ := by rw [he]

theorem sampling_direction_loss_le {δ η Tb C b : ℝ} (hδ : 0 < δ)
    (hTb : 0 ≤ Tb) (hT : Tb ≤ C*δ^(-η)) :
    8*2^b*Tb^2/δ^η ≤ (8*2^b*C^2)*δ^(-3*η) := by
  have he : (δ^(-η))^2/δ^η = δ^(-3*η) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hδ.le, ← Real.rpow_sub hδ]
    congr 1
    ring
  calc
    _ ≤ 8*2^b*(C*δ^(-η))^2/δ^η := by gcongr
    _ = (8*2^b*C^2)*((δ^(-η))^2/δ^η) := by ring
    _ = _ := by rw [he]

theorem eventually_planarSamplingReady {b f η ε : ℝ} (hb : 0 < b)
    (hη : 0 < η) (hη1 : η ≤ 1) (hmargin : 4*η < ε)
    (J : ℕ) : ∀ᶠ δ in 𝓝[>] (0 : ℝ), PlanarSamplingReady δ b f η ε J := by
  let Cf := exp 1 * (8 : ℝ)^f
  let Cb := exp 1 * (8 : ℝ)^b
  have hp := (tendsto_rpow_neg_nhdsGT_zero (show -(ε-4*η) < 0 by linarith)).eventually
    (eventually_ge_atTop (128*Cf^2))
  have ht := (tendsto_rpow_neg_nhdsGT_zero (show -(ε-3*η) < 0 by linarith)).eventually
    (eventually_ge_atTop (8*2^b*Cb^2))
  have hn := (tendsto_rpow_neg_nhdsGT_zero (show -(ε/4) < 0 by linarith)).eventually
    (eventually_ge_atTop (2 : ℝ))
  have hc := (tendsto_rpow_neg_nhdsGT_zero (show -(ε/4-η) < 0 by linarith)).eventually
    (eventually_ge_atTop (2*J+1 : ℝ))
  filter_upwards [sampling_log_budget hη, hp, ht, hn, hc,
    Ioc_mem_nhdsGT (show (0 : ℝ) < 1/4 by norm_num),
    Ioc_mem_nhdsGT (exp_pos (-1 : ℝ))] with δ hlog hp ht hn hc hδsmall hδexp
  have hδ : 0 < δ := hδsmall.1
  have hδ1 : δ ≤ 1 := hδsmall.2.trans (by norm_num)
  have hB : 1 ≤ -10*log δ := by
    have hh := Real.log_le_log hδ hδexp.2
    rw [Real.log_exp] at hh
    linarith
  have hT (s : ℝ) : 0 < samplingBallLoss (δ^(-η)) (-10*log δ) s :=
    samplingBallLoss_pos (by positivity) hB
  refine ⟨hδ, hδsmall.2, hB, ?_, ?_, ?_, ?_, ?_⟩
  · apply (sampling_point_loss_le hδ (hT f).le (samplingBallLoss_le hlog)).trans
    simpa only [Cf, neg_mul] using rpow_absorb_constant hδ hp
  · apply (sampling_direction_loss_le hδ (hT b).le (samplingBallLoss_le hlog)).trans
    simpa only [Cb, neg_mul] using rpow_absorb_constant hδ ht
  · have hsize := (sampling_ceil_size hδ hδ1 hb.le).2.2
    have hN : (Nat.ceil (δ^(-b)) : ℝ) ≤ 2*δ^(-b) := by
      have hh := (le_div_iff₀ (Real.rpow_pos_of_pos hδ b)).mpr hsize
      simpa only [Real.rpow_neg hδ.le, div_eq_mul_inv] using hh
    apply hN.trans
    have hh := rpow_absorb_constant (t := b) (u := b+ε/4) hδ
      (by simpa only [add_sub_cancel_left] using hn)
    convert hh using 1 <;> first | (with_reducible_and_instances rfl) | (ring_nf)
  · have hh := rpow_absorb_constant (t := b+η) (u := b+ε/4) hδ
      (by convert hc using 1 <;> first | (with_reducible_and_instances rfl) | ring_nf)
    convert hh using 1 <;> first | (with_reducible_and_instances rfl) | (ring_nf)
  · apply (sampling_failure_bound hδ hδsmall.2).trans
    apply div_le_div_of_nonneg_right _ (by norm_num)
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_ge hδ hδ1 hη1

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Estimates_PlanarGain
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.sphereMeasure_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Planar measure projection gain from the published Furstenberg input

This gives a fixed positive power bound for incidence with small parallel
strip covers. Both coordinate maps may identify original labels. The
conclusion is proved from the cited finite Furstenberg theorem through the
two-stage sampling argument.
-/

namespace Falconer
open Set MeasureTheory
open scoped Topology
attribute [local instance] Classical.propDecidable

theorem planar_measure_projection_gain
    (hpublished : PublishedPlanarFurstenberg) {b f : ℝ}
    (hb : 0 < b) (hb' : b ≤ 1/2) (hbf : b < f) (hf : f < 1) (C : ℝ) :
    ∃ η δ₀ : ℝ, 0 < η ∧ 0 < δ₀ ∧
    ∀ δ : ℝ, 0 < δ → δ < δ₀ →
    ∀ (X W : Type) [MeasurableSpace X] [MeasurableSpace W]
      (μ : ProbabilityMeasure X) (ν : ProbabilityMeasure W)
      (p : X → Space 2) (m : W → ℝ) (E : X → W → Prop),
      Measurable p → Measurable m → MeasurableSet {z : X × W | E z.1 z.2} →
      (∀ x, |p x 0| ≤ 1/4 ∧ |p x 1| ≤ 1/4) → (∀ w, |m w| ≤ 1/2) →
      (∀ c r, δ ≤ r → (μ : Measure X).real {x | dist (p x) c ≤ r} ≤ δ^(-η)*r^f) →
      (∀ a r, δ ≤ r → (ν : Measure W).real {w | |m w-a| ≤ r} ≤ δ^(-η)*r^b) →
    ∀ A : W → Finset ℝ,
      (∀ w, ((A w).card : ℝ) ≤ δ^(-b-η)) →
      (∀ x w, E x w → ∃ a ∈ A w, |p x 1-m w*p x 0-a| ≤ C*δ) →
      (∫ w, ∫ x, if E x w then (1 : ℝ) else 0 ∂(μ : Measure X) ∂(ν : Measure W)) ≤ δ^η := by
  obtain ⟨ε, δF, hε, hδF, _, hObs⟩ :=
    planar_measure_incidence_obstruction hpublished hb hb' hbf hf
  obtain ⟨J, hJ⟩ := exists_nat_ge (C+2)
  let η := min (ε/100) (1/2)
  have hη : 0 < η := lt_min (by positivity) (by norm_num)
  have hη1 : η ≤ 1 := (min_le_right _ _).trans (by norm_num)
  have hηε : η ≤ ε/100 := min_le_left _ _
  have hmargin : 4*η < ε := by linarith
  have hready := eventually_planarSamplingReady (f := f) hb hη hη1 hmargin J
  obtain ⟨δ₁, hδ₁, hδready⟩ :=
    (mem_nhdsGT_iff_exists_Ioo_subset' (show (0 : ℝ) < 1 by norm_num)).mp hready
  refine ⟨η, min δF δ₁, hη, lt_min hδF hδ₁, ?_⟩
  intro δ hδ hδsmall X W _ _ μ ν p m E hp hm hE hpchart hmchart hpball hmball A hA hcover
  have hr : PlanarSamplingReady δ b f η ε J := hδready ⟨hδ, hδsmall.trans_le (min_le_right _ _)⟩
  have hδ1 : δ ≤ 1 := hr.scale_small.trans (by norm_num)
  obtain ⟨hn, hnsize, hnsize'⟩ := sampling_ceil_size hδ hδ1 hb.le
  obtain ⟨hl, hlsize, hlsize'⟩ := sampling_ceil_size hδ hδ1 (hb.trans hbf).le
  by_contra hnot
  have hmean : δ^η ≤ (∫ w, ∫ x, if E x w then (1 : ℝ) else 0
      ∂(μ : Measure X) ∂(ν : Measure W)) := (lt_of_not_ge hnot).le
  apply hObs δ hδ (hδsmall.trans_le (min_le_left _ _)) X W μ ν p m E hp hm hE hpchart hmchart
    (δ^(-η)) (-10*Real.log δ) (δ^η) (Nat.ceil (δ^(-b))) (Nat.ceil (δ^(-f)))
    (Nat.ceil (δ⁻¹+1)) (Nat.ceil δ⁻¹) J A
    (Real.rpow_nonneg hδ.le _) hr.budget (Real.rpow_pos_of_pos hδ _) hn hl
    (Nat.le_ceil _) (Nat.le_ceil _) hnsize hnsize' hlsize hlsize' hpball hmball
    hmean hr.tail hr.point_loss hr.direction_loss hr.count
  · intro w
    calc
      (((A w).card * (2*J+1) : ℕ) : ℝ) = ((A w).card : ℝ)*(2*J+1) := by norm_cast
      _ ≤ δ^(-b-η)*(2*J+1) := mul_le_mul_of_nonneg_right (hA w) (by positivity)
      _ ≤ δ^(-b-ε/4) := hr.cover
  · intro x w hx
    obtain ⟨a, ha, he⟩ := hcover x w hx
    refine ⟨a, ha, he.trans ?_⟩
    exact mul_le_mul_of_nonneg_right (by linarith : C ≤ (J : ℝ)-2) hδ.le

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Geometry_PlanarSlopeBalls
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Direction-ball control transfers to the slope coordinate -/

namespace Falconer
open Set MeasureTheory NormedSpace

theorem normalize_dist_le_twice {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {x y : E} (hx : 1 ≤ ‖x‖) (hy : y ≠ 0) :
    dist (normalize x) (normalize y) ≤ 2*dist x y := by
  have he : ‖x‖ • (normalize x-normalize y) =
      x-y+(‖y‖-‖x‖) • normalize y := by
    rw [smul_sub,norm_smul_normalize,sub_smul,norm_smul_normalize]
    abel
  have hb := norm_add_le (x-y) ((‖y‖-‖x‖) • normalize y)
  rw [← he,norm_smul,Real.norm_eq_abs,abs_of_nonneg (norm_nonneg _),
    norm_smul,Real.norm_eq_abs,norm_normalize hy,mul_one] at hb
  have hn := abs_norm_sub_norm_le y x
  rw [norm_sub_rev y x] at hn
  rw [dist_eq_norm,dist_eq_norm]
  nlinarith [norm_nonneg (normalize x-normalize y)]

theorem slopeVector_norm_lower (m : ℝ) : 1 ≤ ‖slopeVector m‖ := by
  simpa only [slopeVector_zero,Real.norm_eq_abs,abs_one] using
    PiLp.norm_apply_le (slopeVector m) 0

theorem slopeVector_dist (m t : ℝ) : dist (slopeVector m) (slopeVector t) = |m-t| := by
  have hh := EuclideanSpace.dist_sq_eq (slopeVector m) (slopeVector t)
  simp only [Fin.sum_univ_two,slopeVector_zero,slopeVector_one,Real.dist_eq,sq_abs,sub_self,
    zero_pow (by omega : 2 ≠ 0),zero_add] at hh
  nlinarith [dist_nonneg (x := slopeVector m) (y := slopeVector t),abs_nonneg (m-t),sq_abs (m-t)]

theorem slopeDirection_dist (m t : ℝ) :
    dist (normalize (slopeVector m)) (normalize (slopeVector t)) ≤ 2*|m-t| := by
  have ht : slopeVector t ≠ 0 := norm_pos_iff.mp (lt_of_lt_of_le zero_lt_one (slopeVector_norm_lower t))
  simpa only [slopeVector_dist] using normalize_dist_le_twice (slopeVector_norm_lower m) ht

theorem planar_unit_eq_slopeDirection {w : Space 2} (hw : ‖w‖ = 1) (hpos : 0 < w 0) :
    w = normalize (slopeVector (planarSlope w)) := by
  have he : w = w 0 • slopeVector (planarSlope w) := by
    apply PiLp.ext
    intro i
    fin_cases i
    · change w 0 = w 0 * 1
      ring
    · change w 1 = w 0 * (w 1 / w 0)
      field_simp
  have hn := normalize_eq_self_of_norm_eq_one hw
  rw [he,normalize_smul_of_pos hpos] at hn
  exact he.trans hn.symm

theorem planar_slope_ball_subset {W : Type*} (q : W → Space 2)
    (hunit : ∀ w, ‖q w‖ = 1) (hpos : ∀ w, 0 < q w 0) (a r : ℝ) :
    {w | |planarSlope (q w)-a| ≤ r} ⊆
      {w | dist (q w) (normalize (slopeVector a)) ≤ 2*r} := by
  intro w hw
  change dist (q w) (normalize (slopeVector a)) ≤ 2*r
  rw [planar_unit_eq_slopeDirection (hunit w) (hpos w)]
  exact (slopeDirection_dist _ a).trans (mul_le_mul_of_nonneg_left hw (by norm_num))

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Radial_PlanarUnitTubeGain
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The planar Furstenberg consequence for unit-direction tube covers -/

namespace Falconer
open Set MeasureTheory
open scoped Topology
attribute [local instance] Classical.propDecidable

theorem planar_unit_tube_gain
    (hpublished : PublishedPlanarFurstenberg) {b f : ℝ}
    (hb : 0 < b) (hb' : b ≤ 1/2) (hbf : b < f) (hf : f < 1) (C : ℝ) :
    ∃ η δ₀ : ℝ, 0 < η ∧ 0 < δ₀ ∧
    ∀ δ : ℝ, 0 < δ → δ < δ₀ →
    ∀ (X W : Type) [MeasurableSpace X] [MeasurableSpace W]
      (μ : ProbabilityMeasure X) (ν : ProbabilityMeasure W)
      (p : X → Space 2) (q : W → Space 2) (E : X → W → Prop),
      Measurable p → Measurable q → MeasurableSet {z : X × W | E z.1 z.2} →
      (∀ x, ‖p x‖ ≤ 1/4) → (∀ w, ‖q w‖ = 1) →
      (∀ w, dist (q w) (EuclideanSpace.basisFun (Fin 2) ℝ 0) ≤ 1/4) →
      (∀ c r, δ ≤ r → (μ : Measure X).real {x | dist (p x) c ≤ r} ≤ δ^(-η)*r^f) →
      (∀ c r, δ ≤ r → (ν : Measure W).real {w | dist (q w) c ≤ 2*r} ≤ δ^(-η)*r^b) →
    ∀ (κ : Type) (J : W → Finset κ) (a : κ → Space 2),
      (∀ w, ((J w).card : ℝ) ≤ δ^(-b-η)) →
      (∀ x w, E x w → ∃ i ∈ J w, ‖perpendicularPart (q w) (p x-a i)‖ ≤ C*δ) →
      (∫ w, ∫ x, if E x w then (1 : ℝ) else 0 ∂(μ : Measure X) ∂(ν : Measure W)) ≤ δ^η := by
  classical
  obtain ⟨η,δ₀,hη,hδ₀,hgain⟩ := planar_measure_projection_gain hpublished hb hb' hbf hf ((3/2)*C)
  refine ⟨η,δ₀,hη,hδ₀,?_⟩
  intro δ hδ hδsmall X W _ _ μ ν p q E hp hq hE hpbound hqunit hqchart hpball hqball κ J a hJ hcover
  have hpos (w : W) : 0 < q w 0 := (planarSlope_small_of_axis_close (hqchart w)).1
  have hslope (w : W) : |planarSlope (q w)| ≤ 1/2 :=
    (planarSlope_small_of_axis_close (hqchart w)).2
  let A : W → Finset ℝ := fun w => (J w).image (fun i => planarIntercept (q w) (a i))
  refine hgain δ hδ hδsmall X W μ ν p (fun w => planarSlope (q w)) E hp
    (by unfold planarSlope; fun_prop) hE
    (fun x => ⟨(PiLp.norm_apply_le (p x) 0).trans (hpbound x),
      (PiLp.norm_apply_le (p x) 1).trans (hpbound x)⟩) hslope hpball ?_ A ?_ ?_
  · intro c r hr
    exact (measureReal_mono (μ := (ν : Measure W))
      (planar_slope_ball_subset q hqunit hpos c r)).trans (hqball _ r hr)
  · intro w
    exact (Nat.cast_le.mpr (Finset.card_image_le)).trans (hJ w)
  · intro x w hx
    obtain ⟨i,hi,ht⟩ := hcover x w hx
    refine ⟨planarIntercept (q w) (a i),Finset.mem_image.mpr ⟨i,hi,rfl⟩,?_⟩
    simpa only [mul_assoc] using planar_tube_strip (hpos w).ne' (hslope w) ht

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Radial_PlanarAETubeGain
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The planar tube gain on the actual supports of the two laws -/

namespace Falconer
open Set MeasureTheory
open scoped Topology
attribute [local instance] Classical.propDecidable

theorem planar_ae_tube_gain
    (hpublished : PublishedPlanarFurstenberg) {b f : ℝ}
    (hb : 0 < b) (hb' : b ≤ 1/2) (hbf : b < f) (hf : f < 1) (C : ℝ) :
    ∃ η δ₀ : ℝ, 0 < η ∧ 0 < δ₀ ∧
    ∀ δ : ℝ, 0 < δ → δ < δ₀ →
    ∀ (X W : Type) [MeasurableSpace X] [MeasurableSpace W]
      (μ : ProbabilityMeasure X) (ν : ProbabilityMeasure W)
      (p : X → Space 2) (q : W → Space 2) (E : X → W → Prop),
      Measurable p → Measurable q → MeasurableSet {z : X × W | E z.1 z.2} →
      (∀ᵐ x ∂(μ : Measure X), ‖p x‖ ≤ 1/4) →
      (∀ᵐ w ∂(ν : Measure W), ‖q w‖ = 1 ∧
        dist (q w) (EuclideanSpace.basisFun (Fin 2) ℝ 0) ≤ 1/4) →
      (∀ c r, δ ≤ r → (μ : Measure X).real {x | dist (p x) c ≤ r} ≤ δ^(-η)*r^f) →
      (∀ c r, δ ≤ r → (ν : Measure W).real {w | dist (q w) c ≤ 2*r} ≤ δ^(-η)*r^b) →
    ∀ (κ : Type) (J : W → Finset κ) (a : κ → Space 2),
      (∀ w, ((J w).card : ℝ) ≤ δ^(-b-η)) →
      (∀ x w, E x w → ∃ i ∈ J w, ‖perpendicularPart (q w) (p x-a i)‖ ≤ C*δ) →
      (∫ w, ∫ x, if E x w then (1 : ℝ) else 0 ∂(μ : Measure X) ∂(ν : Measure W)) ≤ δ^η := by
  classical
  obtain ⟨η,δ₀,hη,hδ₀,hgain⟩ := planar_unit_tube_gain hpublished hb hb' hbf hf C
  refine ⟨η,δ₀,hη,hδ₀,?_⟩
  intro δ hδ hδsmall X W _ _ μ ν p q E hp hq hE hpb hqb hpball hqball κ J a hJ hcover
  let F : X → W → Prop := fun x w => E x w ∧ ‖p x‖ ≤ 1/4 ∧
    (‖q w‖ = 1 ∧ dist (q w) (EuclideanSpace.basisFun (Fin 2) ℝ 0) ≤ 1/4)
  have hP : MeasurableSet {x | ‖p x‖ ≤ 1/4} := measurableSet_le hp.norm measurable_const
  have hQ : MeasurableSet {w | ‖q w‖ = 1 ∧
      dist (q w) (EuclideanSpace.basisFun (Fin 2) ℝ 0) ≤ 1/4} :=
    (measurableSet_eq_fun hq.norm measurable_const).inter
      (measurableSet_le (hq.dist measurable_const) measurable_const)
  have hF : MeasurableSet {z : X × W | F z.1 z.2} :=
    hE.inter ((hP.preimage measurable_fst).inter (hQ.preimage measurable_snd))
  have hpb' (c : Space 2) (r : ℝ) (hr : δ ≤ r) :
      (μ : Measure X).real {x | dist (boundedPlanarPoint (p x)) c ≤ r} ≤ δ^(-η)*r^f := by
    have he : {x | dist (boundedPlanarPoint (p x)) c ≤ r} =ᵐ[(μ : Measure X)]
        {x | dist (p x) c ≤ r} := by
      filter_upwards [hpb] with x hx
      change (dist (boundedPlanarPoint (p x)) c ≤ r) = (dist (p x) c ≤ r)
      simp only [boundedPlanarPoint_eq hx]
    rw [measureReal_congr he]
    exact hpball c r hr
  have hqb' (c : Space 2) (r : ℝ) (hr : δ ≤ r) :
      (ν : Measure W).real {w | dist (chartedPlanarDirection (q w)) c ≤ 2*r} ≤ δ^(-η)*r^b := by
    have he : {w | dist (chartedPlanarDirection (q w)) c ≤ 2*r} =ᵐ[(ν : Measure W)]
        {w | dist (q w) c ≤ 2*r} := by
      filter_upwards [hqb] with w hw
      change (dist (chartedPlanarDirection (q w)) c ≤ 2*r) = (dist (q w) c ≤ 2*r)
      simp only [chartedPlanarDirection_eq hw]
    rw [measureReal_congr he]
    exact hqball c r hr
  have hsmall : (∫ w, ∫ x, @ite ℝ (F x w) (Classical.propDecidable (F x w)) 1 0
      ∂(μ : Measure X) ∂(ν : Measure W)) ≤ δ^η := by
    apply hgain δ hδ hδsmall X W μ ν (fun x => boundedPlanarPoint (p x))
      (fun w => chartedPlanarDirection (q w)) F
      (boundedPlanarPoint_measurable.comp hp) (chartedPlanarDirection_measurable.comp hq) hF
      (fun x => boundedPlanarPoint_norm (p x)) (fun w => chartedPlanarDirection_unit (q w))
      (fun w => chartedPlanarDirection_chart (q w)) hpb' hqb' κ J a hJ
    intro x w hx
    obtain ⟨i,hi,ht⟩ := hcover x w hx.1
    refine ⟨i,hi,?_⟩
    rw [boundedPlanarPoint_eq hx.2.1,chartedPlanarDirection_eq hx.2.2]
    exact ht
  have he : (∫ w, ∫ x, @ite ℝ (F x w) (Classical.propDecidable (F x w)) 1 0
      ∂(μ : Measure X) ∂(ν : Measure W)) =
      (∫ w, ∫ x, if E x w then (1 : ℝ) else 0 ∂(μ : Measure X) ∂(ν : Measure W)) := by
    apply integral_congr_ae
    filter_upwards [hqb] with w hw
    apply integral_congr_ae
    filter_upwards [hpb] with x hx
    simp only [F,hx,hw,and_true]
  rw [he] at hsmall
  exact hsmall

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Slicing_SliceNormalization
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Normalizing the retained original-label slice laws -/

namespace Falconer
open Set MeasureTheory
open scoped ENNReal
variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]

theorem normalizedSliceLaw_apply (μ : Measure X) [IsFiniteMeasure μ]
    (hμ : μ univ ≠ 0) (S : Set X) :
    (normalizedSliceLaw μ hμ : Measure X) S = (μ univ)⁻¹*μ S := rfl

theorem normalizedSliceLaw_bound (μ : Measure X) [IsFiniteMeasure μ]
    (hμ : μ univ ≠ 0) (S : Set X) {L B : ℝ≥0∞}
    (hL : L ≤ μ univ) (hS : μ S ≤ B) :
    (normalizedSliceLaw μ hμ : Measure X) S ≤ L⁻¹*B := by
  rw [normalizedSliceLaw_apply]
  exact mul_le_mul' (ENNReal.inv_le_inv.mpr hL) hS

theorem normalizedSliceLaw_ae (μ : Measure X) [IsFiniteMeasure μ]
    (hμ : μ univ ≠ 0) {P : X → Prop} (hP : ∀ᵐ x ∂μ, P x) :
    ∀ᵐ x ∂(normalizedSliceLaw μ hμ : Measure X), P x :=
  Measure.ae_smul_measure hP _

theorem positive_incidence_marginals (μ : Measure X) (ν : Measure Y)
    [SFinite μ] [SFinite ν] (E : Set (X × Y)) (hE : 0 < (μ.prod ν) E) :
    μ univ ≠ 0 ∧ ν univ ≠ 0 := by
  have hu : 0 < μ univ*ν univ := hE.trans_le (by
    calc
      _ ≤ (μ.prod ν) univ := measure_mono (subset_univ _)
      _ = _ := by rw [← univ_prod_univ,Measure.prod_prod])
  exact ⟨fun h => by simp only [h,zero_mul,lt_self_iff_false] at hu,
    fun h => by simp only [h,mul_zero,lt_self_iff_false] at hu⟩

theorem incidence_marginal_lower_bounds (μ : Measure X) (ν : Measure Y)
    [SFinite μ] [SFinite ν] (E : Set (X × Y))
    {P M I : ℝ≥0∞} (hP : μ univ ≤ P) (hM : ν univ ≤ M)
    (hP0 : P ≠ 0) (hPtop : P ≠ ∞) (hM0 : M ≠ 0) (hMtop : M ≠ ∞)
    (hI : I ≤ (μ.prod ν) E) : I/M ≤ μ univ ∧ I/P ≤ ν univ := by
  have hi : I ≤ μ univ*ν univ := hI.trans (by
    calc
      _ ≤ (μ.prod ν) univ := measure_mono (subset_univ _)
      _ = _ := by rw [← univ_prod_univ,Measure.prod_prod])
  constructor
  · calc
      I/M ≤ (μ univ*M)*M⁻¹ := mul_le_mul_left (hi.trans (mul_le_mul_right hM _)) _
      _ = μ univ := by rw [mul_assoc,ENNReal.mul_inv_cancel hM0 hMtop,mul_one]
  · calc
      I/P ≤ (ν univ*P)*P⁻¹ := mul_le_mul_left
        (hi.trans ((mul_le_mul_left hP _).trans_eq (mul_comm _ _))) _
      _ = ν univ := by rw [mul_assoc,ENNReal.mul_inv_cancel hP0 hPtop,mul_one]

theorem normalizedSliceLaw_incidence (μ : Measure X) (ν : Measure Y)
    [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (hμ : μ univ ≠ 0) (hν : ν univ ≠ 0) (E : Set (X × Y)) :
    ((normalizedSliceLaw μ hμ : Measure X).prod (normalizedSliceLaw ν hν : Measure Y)) E =
      (μ univ*ν univ)⁻¹*(μ.prod ν) E := by
  change (((μ univ)⁻¹ • μ).prod ((ν univ)⁻¹ • ν)) E = _
  rw [Measure.prod_smul_left,Measure.prod_smul_right,Measure.smul_apply,Measure.smul_apply,
    smul_eq_mul,smul_eq_mul,← mul_assoc,← ENNReal.mul_inv (Or.inl hμ) (Or.inr hν)]

theorem normalizedSliceLaw_incidence_lower (μ : Measure X) (ν : Measure Y)
    [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (hμ : μ univ ≠ 0) (hν : ν univ ≠ 0) (E : Set (X × Y))
    {P M I : ℝ≥0∞} (hP : μ univ ≤ P) (hM : ν univ ≤ M) (hI : I ≤ (μ.prod ν) E) :
    (P*M)⁻¹*I ≤
      ((normalizedSliceLaw μ hμ : Measure X).prod (normalizedSliceLaw ν hν : Measure Y)) E := by
  rw [normalizedSliceLaw_incidence]
  exact mul_le_mul' (ENNReal.inv_le_inv.mpr (mul_le_mul' hP hM)) hI

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Slicing_SliceIncidence
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The real incidence integral of the normalized original slice laws -/

namespace Falconer
open Set MeasureTheory
attribute [local instance] Classical.propDecidable
variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]

theorem slice_iterated_incidence (μ : Measure X) (ν : Measure Y)
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] (E : Set (X × Y)) (hE : MeasurableSet E) :
    (∫ y, ∫ x, if (x,y) ∈ E then (1 : ℝ) else 0 ∂μ ∂ν) = (μ.prod ν).real E := by
  have hi : Integrable (E.indicator (fun _ : X × Y => (1 : ℝ))) (μ.prod ν) :=
    (integrable_const 1).indicator hE
  have he := integral_prod_symm (E.indicator (fun _ : X × Y => (1 : ℝ))) hi
  rw [integral_indicator_const (1 : ℝ) hE,smul_eq_mul,mul_one] at he
  exact he.symm

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Estimates_PlanarSelectedGain
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Applying the published planar consequence to a selected original-label slice -/

namespace Falconer
open Set MeasureTheory NormedSpace
open scoped ENNReal Topology
variable {d h : ℕ} {κ : Type*}

theorem selectedActiveRelation_measurable [Fintype κ] [DecidableEq κ]
    (A : Fin h → Space d) (z : Space h) (δ : ℝ)
    (E : Set (Space d × Sphere d)) (hE : MeasurableSet E)
    (J : Sphere d → Finset κ) (hJ : ∀ i, MeasurableSet {w | i ∈ J w})
    (a : κ → Space d) (R T : ℝ) :
    MeasurableSet (selectedActiveRelation A z δ E J a R T) := by
  have hs := (gaussianActiveRelation_measurable E hE J hJ a R (ENNReal.ofReal T) true).preimage
    (show Measurable (fun u : Space d × Sphere d => ((A,z),u)) from by fun_prop)
  exact hs.inter ((gaussianPointBand_measurable A z δ).prod (gaussianDirectionBand_measurable A δ))

theorem planar_selected_slice_gain
    (hpublished : PublishedPlanarFurstenberg) {b f : ℝ}
    (hb : 0 < b) (hb' : b ≤ 1/2) (hbf : b < f) (hf : f < 1) (C : ℝ) :
    ∃ η δ₀ : ℝ, 0 < η ∧ 0 < δ₀ ∧
    ∀ δ : ℝ, 0 < δ → δ < δ₀ →
    ∀ (d h : ℕ) (κ : Type) [Fintype κ] [DecidableEq κ]
      (A : Fin h → Space d) (z : Space h) (e : (gaussianRowMap A).ker ≃ₗᵢ[ℝ] Space 2)
      (α : ProbabilityMeasure (Space d)) (β : ProbabilityMeasure (Sphere d))
      (E : Set (Space d × Sphere d)) (J : Sphere d → Finset κ) (a : κ → Space d)
      (M K T : ℝ),
    MeasurableSet E → (∀ i, MeasurableSet {w | i ∈ J w}) →
    0 ≤ M → 0 ≤ K → 0 ≤ T → T ≤ δ^(-b-η) →
    (∀ i, ‖A i‖ ≤ M) →
    (∀ x : Space d, ‖(gaussianRowMap A).kerᗮ.starProjection x‖ ≤ K*‖gaussianRowMap A x‖) →
    K*((h:ℝ)*δ) < 1 →
    (∀ u ∈ E, ‖u.1‖ ≤ 1/4) → (∀ w, ∀ i ∈ J w, ‖a i‖ ≤ 1/4) →
    (∀ u ∈ E, ∃ i ∈ J u.2, ‖perpendicularPart (u.2:Space d) (u.1-a i)‖ ≤ C*δ) →
    (∀ᵐ x ∂(α : Measure (Space d)), ‖x‖ ≤ 1/4) →
    (∀ᵐ w : Sphere d ∂(β : Measure (Sphere d)),
      ‖normalize (e ((gaussianRowMap A).ker.orthogonalProjectionOnto (w:Space d)))‖ = 1 ∧
      dist (normalize (e ((gaussianRowMap A).ker.orthogonalProjectionOnto (w:Space d))))
        (EuclideanSpace.basisFun (Fin 2) ℝ 0) ≤ 1/4) →
    (∀ c r, δ ≤ r → (α : Measure (Space d)).real
      {x | dist (e ((gaussianRowMap A).ker.orthogonalProjectionOnto x)) c ≤ r} ≤ δ^(-η)*r^f) →
    (∀ c r, δ ≤ r → (β : Measure (Sphere d)).real
      {w | dist (normalize (e ((gaussianRowMap A).ker.orthogonalProjectionOnto (w:Space d)))) c ≤ 2*r}
        ≤ δ^(-η)*r^b) →
    ((α : Measure (Space d)).prod (β : Measure (Sphere d))).real
      (selectedActiveRelation A z δ E J a (δ+(2*(1/4))*δ+(C*δ)*M) T) ≤ δ^η := by
  classical
  obtain ⟨η,δ₀,hη,hδ₀,hgain⟩ := planar_ae_tube_gain hpublished hb hb' hbf hf C
  refine ⟨η,δ₀,hη,hδ₀,?_⟩
  intro δ hδ hδsmall d h κ _ _ A z e α β E J a M K T hE hJ hM hK hT hTbound
    hA hbound hsmall hbounded hanchors hcover hα hβ hpball hqball
  let R := δ+(2*(1/4))*δ+(C*δ)*M
  let F := selectedActiveRelation A z δ E J a R T
  have hF : MeasurableSet F := selectedActiveRelation_measurable A z δ E hE J hJ a R T
  rw [← slice_iterated_incidence (α : Measure (Space d)) (β : Measure (Sphere d)) F hF]
  refine hgain δ hδ hδsmall (Space d) (Sphere d) α β
    (fun x => e ((gaussianRowMap A).ker.orthogonalProjectionOnto x))
    (fun w : Sphere d => normalize (e ((gaussianRowMap A).ker.orthogonalProjectionOnto (w:Space d))))
    (fun x w => (x,w) ∈ F) (by fun_prop)
    (by unfold NormedSpace.normalize; fun_prop) hF ?_ hβ hpball hqball κ
    (fun w => cappedActiveAnchors A z (J w) a R T)
    (fun i => e ((gaussianRowMap A).ker.orthogonalProjectionOnto (a i))) ?_ ?_
  · filter_upwards [hα] with x hx
    rw [e.norm_map]
    exact ((gaussianRowMap A).ker.norm_starProjection_apply_le x).trans hx
  · intro w
    exact (cappedActiveAnchors_card A z (J w) a R hT).trans hTbound
  · intro x w hx
    exact gaussian_capped_coordinate_cover A z e E J a hM hK hT hA hbound hsmall
      hbounded hanchors hcover hx.2.1 hx.2.2 hx.1

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Geometry_PolynomialNormalization
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # One common polynomial loss for both normalized slice laws -/

namespace Falconer
open Set MeasureTheory
open scoped ENNReal
variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]

theorem polynomial_slice_normalization
    (α : Measure X) (β : Measure Y) [IsFiniteMeasure α] [IsFiniteMeasure β]
    (E : Set (X × Y)) {K V : ℝ} (hK : 0 < K) (hV : 0 < V)
    (hα : α univ ≤ ENNReal.ofReal (K^6)) (hβ : β univ ≤ ENNReal.ofReal (K^3))
    (hI : ENNReal.ofReal (1/(4*K*V)) ≤ (α.prod β) E) :
    ∃ ha : α univ ≠ 0, ∃ hb : β univ ≠ 0,
      ENNReal.ofReal (K^6) / α univ ≤ ENNReal.ofReal (4*K^10*V) ∧
      ENNReal.ofReal (K^3) / β univ ≤ ENNReal.ofReal (4*K^10*V) ∧
      (∀ (S : Set X) (w : ℝ), α S ≤ ENNReal.ofReal (K^6*w) →
        (normalizedSliceLaw α ha : Measure X) S ≤ ENNReal.ofReal (4*K^10*V*w)) ∧
      (∀ (S : Set Y) (w : ℝ), β S ≤ ENNReal.ofReal (K^3*w) →
        (normalizedSliceLaw β hb : Measure Y) S ≤ ENNReal.ofReal (4*K^10*V*w)) ∧
      ENNReal.ofReal (1/(4*K^10*V)) ≤
        ((normalizedSliceLaw α ha : Measure X).prod (normalizedSliceLaw β hb : Measure Y)) E := by
  have hIp : 0 < ENNReal.ofReal (1/(4*K*V)) := ENNReal.ofReal_pos.mpr (by positivity)
  obtain ⟨ha,hb⟩ := positive_incidence_marginals α β E (hIp.trans_le hI)
  have hlo := incidence_marginal_lower_bounds α β E hα hβ
    (ne_of_gt (ENNReal.ofReal_pos.mpr (pow_pos hK 6))) ENNReal.ofReal_ne_top
    (ne_of_gt (ENNReal.ofReal_pos.mpr (pow_pos hK 3))) ENNReal.ofReal_ne_top hI
  have hla : ENNReal.ofReal (1/(4*K^4*V)) ≤ α univ := by
    convert hlo.1 using 1
    all_goals try with_reducible_and_instances rfl
    rw [← ENNReal.ofReal_div_of_pos (pow_pos hK 3)]
    congr 1
    field_simp
  have hlb : ENNReal.ofReal (1/(4*K^7*V)) ≤ β univ := by
    convert hlo.2 using 1
    all_goals try with_reducible_and_instances rfl
    rw [← ENNReal.ofReal_div_of_pos (pow_pos hK 6)]
    congr 1
    field_simp
  have hra : ENNReal.ofReal (K^6) / α univ ≤ ENNReal.ofReal (4*K^10*V) := by
    apply (mul_le_mul' le_rfl (ENNReal.inv_le_inv.mpr hla)).trans_eq
    change ENNReal.ofReal (K^6) / ENNReal.ofReal (1/(4*K^4*V)) = _
    rw [← ENNReal.ofReal_div_of_pos (by positivity)]
    congr 1
    field_simp
  have hrb : ENNReal.ofReal (K^3) / β univ ≤ ENNReal.ofReal (4*K^10*V) := by
    apply (mul_le_mul' le_rfl (ENNReal.inv_le_inv.mpr hlb)).trans_eq
    change ENNReal.ofReal (K^3) / ENNReal.ofReal (1/(4*K^7*V)) = _
    rw [← ENNReal.ofReal_div_of_pos (by positivity)]
    congr 1
    field_simp
  refine ⟨ha,hb,hra,hrb,?_,?_,?_⟩
  · intro S w hS
    apply (normalizedSliceLaw_bound α ha S hla hS).trans_eq
    rw [mul_comm]
    change ENNReal.ofReal (K^6*w) / ENNReal.ofReal (1/(4*K^4*V)) = _
    rw [← ENNReal.ofReal_div_of_pos (by positivity)]
    congr 1
    field_simp
  · intro S w hS
    apply (normalizedSliceLaw_bound β hb S hlb hS).trans_eq
    rw [mul_comm]
    change ENNReal.ofReal (K^3*w) / ENNReal.ofReal (1/(4*K^7*V)) = _
    rw [← ENNReal.ofReal_div_of_pos (by positivity)]
    congr 1
    field_simp
  · have hi := normalizedSliceLaw_incidence_lower α β ha hb E hα hβ hI
    convert hi using 1
    all_goals try with_reducible_and_instances rfl
    symm
    rw [mul_comm,← ENNReal.ofReal_mul (by positivity : 0 ≤ K^6)]
    change ENNReal.ofReal (1/(4*K*V)) / ENNReal.ofReal (K^6*K^3) = _
    rw [← ENNReal.ofReal_div_of_pos (by positivity)]
    congr 1
    field_simp

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Slicing_GaussianBandRestriction
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Making the two slice bands explicit in the original-label relation -/

namespace Falconer
open Set MeasureTheory
open scoped ENNReal
variable {d h : ℕ} {ι : Type*}

theorem gaussian_pruned_incidence_inter_bands
    (μ : Measure (Space d)) (ν : Measure (Sphere d)) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (δ : ℝ) (r : ι → ℝ) (TP TD : ι → ℝ≥0∞) (M : ℝ≥0∞)
    (E : Set (Space d × Sphere d)) (p : (Fin h → Space d) × Space h) :
    gaussianPrunedIncidence μ ν δ r TP TD M
      (E ∩ (gaussianPointBand p.1 p.2 δ ×ˢ gaussianDirectionBand p.1 δ)) p =
      gaussianPrunedIncidence μ ν δ r TP TD M E p := by
  let α := (gaussianPointSliceMeasure μ p.1 p.2 δ).restrict (gaussianPointGood μ δ r TP p)
  let β := (gaussianDirectionSliceMeasure ν p.1 δ).restrict (gaussianDirectionGood ν δ r TD M p.1)
  have hp : ∀ᵐ x ∂α, x ∈ gaussianPointBand p.1 p.2 δ :=
    ae_restrict_of_ae (Measure.ae_smul_measure (ae_restrict_mem (gaussianPointBand_measurable _ _ _)) _)
  have hw : ∀ᵐ w ∂β, w ∈ gaussianDirectionBand p.1 δ :=
    ae_restrict_of_ae (Measure.ae_smul_measure (ae_restrict_mem (gaussianDirectionBand_measurable _ _)) _)
  change (α.prod β) _ = (α.prod β) E
  apply measure_congr
  filter_upwards [Measure.quasiMeasurePreserving_fst.ae hp,Measure.quasiMeasurePreserving_snd.ae hw] with t ht hu
  exact propext ⟨fun h => h.1,fun h => ⟨h,ht,hu⟩⟩

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Geometry_TruncatedDyadicBalls
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.sphereMeasure_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Only the dyadic ball tests above the slice thickness are needed -/

namespace Falconer
open Set MeasureTheory
open scoped ENNReal
variable {X : Type*} [MeasurableSpace X] {m : ℕ}

theorem truncated_dyadic_ball_bound
    (μ : Measure X) (p : X → Space m) (N : ℕ) {a H s : ℝ}
    (ha : 1 ≤ a) (hH : 1 ≤ H) (hs : 0 ≤ s) (hmass : μ univ ≤ 1)
    (hdyadic : ∀ g ≤ N, 2*a*(1/(2:ℝ)^N) ≤ 1/(2:ℝ)^g → ∀ c : Space m,
      μ {x | dist (p x) c ≤ (1/(2:ℝ)^g)/(2*a)} ≤
        ENNReal.ofReal (H*(1/(2:ℝ)^g)^s)) :
    ∀ (c : Space m) (r : ℝ), 1/(2:ℝ)^N ≤ r →
      μ {x | dist (p x) c ≤ r} ≤ ENNReal.ofReal (H*(4*a*r)^s) := by
  intro c r hr
  have hap : 0 < a := lt_of_lt_of_le zero_lt_one ha
  have hrp : 0 < r := (by positivity : 0 < 1/(2:ℝ)^N).trans_le hr
  by_cases hsmall : 2*a*r ≤ 1
  · have hmin : 1/(2:ℝ)^N ≤ 2*a*r := hr.trans (by nlinarith)
    obtain ⟨g,hg,hgr,hrg⟩ := Regularization.dyadic_radius_bracket hmin hsmall
    have hcut : 2*a*(1/(2:ℝ)^N) ≤ 1/(2:ℝ)^g :=
      (mul_le_mul_of_nonneg_left hr (by positivity : 0 ≤ 2*a)).trans hgr
    have hrad : r ≤ (1/(2:ℝ)^g)/(2*a) := (le_div_iff₀ (by positivity)).mpr (by
      simpa only [mul_assoc,mul_comm,mul_left_comm] using hgr)
    calc
      _ ≤ μ {x | dist (p x) c ≤ (1/(2:ℝ)^g)/(2*a)} := measure_mono (fun x hx => hx.trans hrad)
      _ ≤ ENNReal.ofReal (H*(1/(2:ℝ)^g)^s) := hdyadic g hg hcut c
      _ ≤ _ := ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow (by positivity) (by nlinarith [hrg]) hs) (by linarith))
  · apply (measure_mono (subset_univ _) |>.trans hmass).trans
    rw [← ENNReal.ofReal_one]
    apply ENNReal.ofReal_le_ofReal
    have hpow : 1 ≤ (4*a*r)^s := Real.one_le_rpow (by linarith) hs
    nlinarith

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Slicing_SliceMapBalls
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Ball transport by pairwise metric control on a full-measure support -/

namespace Falconer
open Set Metric MeasureTheory
open scoped ENNReal
variable {X Y : Type*} [PseudoMetricSpace X] [PseudoMetricSpace Y]
  [MeasurableSpace X] [MeasurableSpace Y] [BorelSpace X] [BorelSpace Y]

omit [BorelSpace X] in
theorem map_ball_bound_of_pair_control (μ : Measure X) (f : X → Y) (hf : Measurable f)
    (S : Set X) (hS : ∀ᵐ x ∂μ, x ∈ S) {r R : ℝ} {C : ℝ≥0∞}
    (hpair : ∀ x ∈ S, ∀ y ∈ S, dist (f x) (f y) < 2*r → dist x y < R)
    (hball : ∀ x, μ (ball x R) ≤ C) (a : Y) :
    (Measure.map f μ) (ball a r) ≤ C := by
  rw [Measure.map_apply hf measurableSet_ball]
  by_cases he : (S ∩ f ⁻¹' ball a r).Nonempty
  · obtain ⟨x,hxS,hxa⟩ := he
    apply (measure_mono_ae ?_).trans (hball x)
    filter_upwards [hS] with y hy hya
    exact hpair y hy x hxS ((dist_triangle (f y) a (f x)).trans_lt
      (by linarith [show dist (f y) a < r from hya,show dist (f x) a < r from hxa,
        dist_comm a (f x)]))
  · have hz : μ (f ⁻¹' ball a r) = 0 := by
      apply measure_mono_null (t := Sᶜ)
      · intro x hx hxS
        exact he ⟨x,hxS,hx⟩
      · exact ae_iff.mp hS
    rw [hz]
    exact zero_le

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Slicing_GaussianMapBalls
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Finite-scale ball bounds on the actual kernel-coordinate pushforwards -/

namespace Falconer
open Set Metric MeasureTheory NormedSpace
open scoped ENNReal
variable {d h : ℕ}

theorem gaussian_point_kernel_ball_bound (A : Fin h → Space d) (z : Space h)
    (μ : Measure (Space d)) {δ K s R : ℝ} {C : ℝ≥0∞} (hK : 0 ≤ K)
    (hbound : ∀ x : Space d, ‖(gaussianRowMap A).kerᗮ.starProjection x‖ ≤ K*‖gaussianRowMap A x‖)
    (hμ : ∀ᵐ x ∂μ, x ∈ gaussianPointBand A z δ)
    (hball : ∀ x, μ (ball x R) ≤ C) (hR : 2*s+K*((h:ℝ)*(2*δ)) ≤ R) (a : Space d) :
    (Measure.map (gaussianRowMap A).ker.starProjection μ) (ball a s) ≤ C := by
  apply map_ball_bound_of_pair_control μ _
    (gaussianRowMap A).ker.starProjection.continuous.measurable _ hμ _ hball a
  intro x hx y hy hxy
  have hp := gaussian_point_kernel_pair_distance A z hK hbound hx hy
    (le_refl ‖(gaussianRowMap A).ker.starProjection x-(gaussianRowMap A).ker.starProjection y‖)
  rw [dist_eq_norm] at hxy ⊢
  exact hp.trans_lt (by linarith)

theorem gaussian_direction_kernel_ball_bound (A : Fin h → Space d)
    (ν : Measure (Sphere d)) {δ K s R : ℝ} {C : ℝ≥0∞} (hK : 0 ≤ K)
    (hbound : ∀ x : Space d, ‖(gaussianRowMap A).kerᗮ.starProjection x‖ ≤ K*‖gaussianRowMap A x‖)
    (hsmall : K*((h:ℝ)*δ) < 1)
    (hν : ∀ᵐ w ∂ν, w ∈ gaussianDirectionBand A δ)
    (hball : ∀ w, ν (ball w R) ≤ C) (hR : 2*s+4*(K*((h:ℝ)*δ)) ≤ R) (a : Space d) :
    (Measure.map (fun w : Sphere d => normalize ((gaussianRowMap A).ker.starProjection (w:Space d))) ν)
      (ball a s) ≤ C := by
  apply map_ball_bound_of_pair_control ν _ (by unfold NormedSpace.normalize; fun_prop) _ hν _ hball a
  intro w hw v hv hdist
  have hwe := gaussian_direction_kernel_normalize_error A hK hbound hsmall hw
  have hve := gaussian_direction_kernel_normalize_error A hK hbound hsmall hv
  change ‖(w:Space d)-(v:Space d)‖ < R
  rw [dist_eq_norm] at hdist
  have htriangle : ‖(w:Space d)-(v:Space d)‖ ≤
      ‖(w:Space d)-normalize ((gaussianRowMap A).ker.starProjection (w:Space d))‖ +
      ‖normalize ((gaussianRowMap A).ker.starProjection (w:Space d))-
        normalize ((gaussianRowMap A).ker.starProjection (v:Space d))‖ +
      ‖normalize ((gaussianRowMap A).ker.starProjection (v:Space d))-(v:Space d)‖ := by
    calc
      _ ≤ ‖(w:Space d)-normalize ((gaussianRowMap A).ker.starProjection (w:Space d))‖ +
          ‖normalize ((gaussianRowMap A).ker.starProjection (w:Space d))-(v:Space d)‖ :=
        norm_sub_le_norm_sub_add_norm_sub _ _ _
      _ ≤ _ := by
        have ht := norm_sub_le_norm_sub_add_norm_sub
          (normalize ((gaussianRowMap A).ker.starProjection (w:Space d)))
          (normalize ((gaussianRowMap A).ker.starProjection (v:Space d))) (v:Space d)
        exact (add_le_add le_rfl ht).trans_eq (add_assoc _ _ _).symm
  have hwe' : ‖(w:Space d)-normalize ((gaussianRowMap A).ker.starProjection (w:Space d))‖ ≤
      2*(K*((h:ℝ)*δ)) := (norm_sub_rev _ _).le.trans hwe
  linarith

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Slicing_GaussianPrunedBalls
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Coordinate ball estimates for the actual retained slice laws -/

namespace Falconer
open Set Metric MeasureTheory NormedSpace
open scoped ENNReal
variable {d h m : ℕ} {ι : Type*}

theorem gaussian_pruned_point_kernel_ball
    (μ : Measure (Space d)) [IsFiniteMeasure μ] (A : Fin h → Space d) (z : Space h)
    (δ : ℝ) (r : ι → ℝ) (TP : ι → ℝ≥0∞) (i : ι)
    {K s : ℝ} (hK : 0 ≤ K)
    (hbound : ∀ x : Space d, ‖(gaussianRowMap A).kerᗮ.starProjection x‖ ≤ K*‖gaussianRowMap A x‖)
    (hs : 2*s+K*((h:ℝ)*(2*δ)) ≤ r i) (a : Space d) :
    (Measure.map (gaussianRowMap A).ker.starProjection
      ((gaussianPointSliceMeasure μ A z δ).restrict (gaussianPointGood μ δ r TP (A,z))))
        (ball a s) ≤ TP i := by
  apply gaussian_point_kernel_ball_bound A z _ hK hbound _ (fun x => gaussianPointGood_ball μ δ r TP (A,z) i x) hs a
  exact ae_restrict_of_ae (Measure.ae_smul_measure (ae_restrict_mem (gaussianPointBand_measurable _ _ _)) _)

theorem gaussian_pruned_direction_kernel_ball
    (ν : Measure (Sphere d)) [IsFiniteMeasure ν] (A : Fin h → Space d)
    (δ : ℝ) (r : ι → ℝ) (TD : ι → ℝ≥0∞) (M : ℝ≥0∞) (i : ι)
    {K s : ℝ} (hK : 0 ≤ K)
    (hbound : ∀ x : Space d, ‖(gaussianRowMap A).kerᗮ.starProjection x‖ ≤ K*‖gaussianRowMap A x‖)
    (hsmall : K*((h:ℝ)*δ) < 1) (hs : 2*s+4*(K*((h:ℝ)*δ)) ≤ r i) (a : Space d) :
    (Measure.map (fun w : Sphere d => normalize ((gaussianRowMap A).ker.starProjection (w:Space d)))
      ((gaussianDirectionSliceMeasure ν A δ).restrict (gaussianDirectionGood ν δ r TD M A)))
        (ball a s) ≤ TD i := by
  apply gaussian_direction_kernel_ball_bound A _ hK hbound hsmall _
    (fun w => gaussianDirectionGood_ball ν δ r TD M A i w) hs a
  exact ae_restrict_of_ae (Measure.ae_smul_measure (ae_restrict_mem (gaussianDirectionBand_measurable _ _)) _)

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Slicing_OrientedSliceBalls
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Closed-ball bounds in the oriented coordinates of the actual slice -/

namespace Falconer
open Set Metric MeasureTheory NormedSpace
open scoped ENNReal
variable {d h m : ℕ} {ι : Type*}

theorem oriented_point_ball_eq (V : Submodule ℝ (Space d))
    (e : V ≃ₗᵢ[ℝ] Space m) (μ : Measure (Space d)) (c : Space m) (r : ℝ) :
    μ {x | dist (e (V.orthogonalProjectionOnto x)) c < r} =
      (Measure.map V.starProjection μ) (ball (e.symm c : Space d) r) := by
  rw [Measure.map_apply V.starProjection.continuous.measurable measurableSet_ball]
  congr 1
  ext x
  change dist (e (V.orthogonalProjectionOnto x)) c < r ↔
    dist (V.orthogonalProjectionOnto x) (e.symm c) < r
  rw [← e.dist_map (V.orthogonalProjectionOnto x) (e.symm c),e.apply_symm_apply]

theorem oriented_direction_ball_eq (V : Submodule ℝ (Space d))
    (e : V ≃ₗᵢ[ℝ] Space m) (ν : Measure (Sphere d)) (c : Space m) (r : ℝ) :
    ν {w | dist (normalize (e (V.orthogonalProjectionOnto (w:Space d)))) c < r} =
      (Measure.map (fun w : Sphere d => normalize (V.starProjection (w:Space d))) ν)
        (ball (e.symm c : Space d) r) := by
  rw [Measure.map_apply (show Measurable
    (fun w : Sphere d => normalize (V.starProjection (w:Space d))) from
      by unfold NormedSpace.normalize; fun_prop) measurableSet_ball]
  congr 1
  ext w
  change dist (normalize (e (V.orthogonalProjectionOnto (w:Space d)))) c < r ↔
    dist (normalize (V.orthogonalProjectionOnto (w:Space d))) (e.symm c) < r
  rw [← slice_isometry_normalize V e]
  rw [← e.dist_map (normalize (V.orthogonalProjectionOnto (w:Space d))) (e.symm c),e.apply_symm_apply]

theorem gaussian_pruned_oriented_point_closed_ball
    (μ : Measure (Space d)) [IsFiniteMeasure μ] (A : Fin h → Space d) (z : Space h)
    (e : (gaussianRowMap A).ker ≃ₗᵢ[ℝ] Space m)
    (δ : ℝ) (r : ι → ℝ) (TP : ι → ℝ≥0∞) (i : ι)
    {K s : ℝ} (hK : 0 ≤ K) (hspos : 0 < s)
    (hbound : ∀ x : Space d, ‖(gaussianRowMap A).kerᗮ.starProjection x‖ ≤ K*‖gaussianRowMap A x‖)
    (hs : 4*s+K*((h:ℝ)*(2*δ)) ≤ r i) (c : Space m) :
    ((gaussianPointSliceMeasure μ A z δ).restrict (gaussianPointGood μ δ r TP (A,z)))
      {x | dist (e ((gaussianRowMap A).ker.orthogonalProjectionOnto x)) c ≤ s} ≤ TP i := by
  have hss : s < 2*s := by linarith
  calc
    _ ≤ ((gaussianPointSliceMeasure μ A z δ).restrict (gaussianPointGood μ δ r TP (A,z)))
      {x | dist (e ((gaussianRowMap A).ker.orthogonalProjectionOnto x)) c < 2*s} :=
      measure_mono (show {x | dist (e ((gaussianRowMap A).ker.orthogonalProjectionOnto x)) c ≤ s} ⊆
        {x | dist (e ((gaussianRowMap A).ker.orthogonalProjectionOnto x)) c < 2*s} from
          fun x hx => lt_of_le_of_lt hx hss)
    _ = _ := oriented_point_ball_eq (gaussianRowMap A).ker e _ c (2*s)
    _ ≤ _ := gaussian_pruned_point_kernel_ball μ A z δ r TP i hK hbound (by linarith) _

theorem gaussian_pruned_oriented_direction_closed_ball
    (ν : Measure (Sphere d)) [IsFiniteMeasure ν] (A : Fin h → Space d)
    (e : (gaussianRowMap A).ker ≃ₗᵢ[ℝ] Space m)
    (δ : ℝ) (r : ι → ℝ) (TD : ι → ℝ≥0∞) (M : ℝ≥0∞) (i : ι)
    {K s : ℝ} (hK : 0 ≤ K) (hspos : 0 < s)
    (hbound : ∀ x : Space d, ‖(gaussianRowMap A).kerᗮ.starProjection x‖ ≤ K*‖gaussianRowMap A x‖)
    (hsmall : K*((h:ℝ)*δ) < 1) (hs : 4*s+4*(K*((h:ℝ)*δ)) ≤ r i) (c : Space m) :
    ((gaussianDirectionSliceMeasure ν A δ).restrict (gaussianDirectionGood ν δ r TD M A))
      {w | dist (normalize (e ((gaussianRowMap A).ker.orthogonalProjectionOnto (w:Space d)))) c ≤ s} ≤ TD i := by
  have hss : s < 2*s := by linarith
  calc
    _ ≤ ((gaussianDirectionSliceMeasure ν A δ).restrict (gaussianDirectionGood ν δ r TD M A))
      {w | dist (normalize (e ((gaussianRowMap A).ker.orthogonalProjectionOnto (w:Space d)))) c < 2*s} :=
      measure_mono (show {w : Sphere d | dist (normalize (e ((gaussianRowMap A).ker.orthogonalProjectionOnto (w:Space d)))) c ≤ s} ⊆
        {w : Sphere d | dist (normalize (e ((gaussianRowMap A).ker.orthogonalProjectionOnto (w:Space d)))) c < 2*s} from
          fun w hw => lt_of_le_of_lt hw hss)
    _ = _ := oriented_direction_ball_eq (gaussianRowMap A).ker e _ c (2*s)
    _ ≤ _ := gaussian_pruned_direction_kernel_ball ν A δ r TD M i hK hbound hsmall (by linarith) _

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Slicing_SliceScaling
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The fixed spatial rescaling of a selected planar slice -/

namespace Falconer
open NormedSpace
variable {m : ℕ}

theorem slice_scaled_distance {L : ℝ} (hL : 0 < L) (x c : Space m) :
    dist (L⁻¹ • x) c = L⁻¹*dist x (L • c) := by
  have he : L⁻¹ • x-c = L⁻¹ • (x-L • c) := by
    rw [smul_sub,smul_smul,inv_mul_cancel₀ hL.ne',one_smul]
  rw [dist_eq_norm,he,norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr hL),dist_eq_norm]

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Slicing_GaussianDyadicGeometry
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The dyadic tests controlling scaled point and normalized direction balls -/

namespace Falconer
open Set MeasureTheory NormedSpace
open scoped ENNReal
variable {d h m : ℕ} {ι : Type*}

theorem gaussian_scaled_point_test
    (μ : Measure (Space d)) [IsFiniteMeasure μ] (A : Fin h → Space d) (z : Space h)
    (e : (gaussianRowMap A).ker ≃ₗᵢ[ℝ] Space m)
    (δ : ℝ) (r : ι → ℝ) (TP : ι → ℝ≥0∞) (i : ι)
    {K L a u : ℝ} (hK : 0 ≤ K) (hL : 0 < L) (ha : 0 < a) (hu : 0 < u)
    (hbound : ∀ x : Space d, ‖(gaussianRowMap A).kerᗮ.starProjection x‖ ≤ K*‖gaussianRowMap A x‖)
    (haK : 4*L+2*K*(h:ℝ) ≤ a) (hδ : δ ≤ u/(2*a)) (hr : r i = u/2) (c : Space m) :
    ((gaussianPointSliceMeasure μ A z δ).restrict (gaussianPointGood μ δ r TP (A,z)))
      {x | dist (L⁻¹ • e ((gaussianRowMap A).ker.orthogonalProjectionOnto x)) c ≤ u/(2*a)} ≤ TP i := by
  have hs : 0 < u/(2*a) := by positivity
  have he : a*(u/(2*a)) = u/2 := by field_simp
  have h₁ := mul_le_mul_of_nonneg_right haK hs.le
  have h₂ := mul_le_mul_of_nonneg_left hδ (by positivity : 0 ≤ 2*K*(h:ℝ))
  have hrad : 4*(L*(u/(2*a)))+K*((h:ℝ)*(2*δ)) ≤ r i := by
    rw [hr]
    nlinarith
  apply (measure_mono (show
    {x | dist (L⁻¹ • e ((gaussianRowMap A).ker.orthogonalProjectionOnto x)) c ≤ u/(2*a)} ⊆
    {x | dist (e ((gaussianRowMap A).ker.orthogonalProjectionOnto x)) (L • c) ≤ L*(u/(2*a))} from ?_)).trans
      (gaussian_pruned_oriented_point_closed_ball μ A z e δ r TP i hK (mul_pos hL hs) hbound hrad _)
  intro x hx
  change dist (L⁻¹ • e ((gaussianRowMap A).ker.orthogonalProjectionOnto x)) c ≤ u/(2*a) at hx
  rw [slice_scaled_distance hL,mul_comm,← div_eq_mul_inv] at hx
  change dist (e ((gaussianRowMap A).ker.orthogonalProjectionOnto x)) (L • c) ≤ L*(u/(2*a))
  simpa only [mul_comm] using (div_le_iff₀ hL).mp hx

theorem gaussian_normalized_direction_test
    (ν : Measure (Sphere d)) [IsFiniteMeasure ν] (A : Fin h → Space d)
    (e : (gaussianRowMap A).ker ≃ₗᵢ[ℝ] Space m)
    (δ : ℝ) (r : ι → ℝ) (TD : ι → ℝ≥0∞) (M : ℝ≥0∞) (i : ι)
    {K a u : ℝ} (hK : 0 ≤ K) (ha : 0 < a) (hu : 0 < u)
    (hbound : ∀ x : Space d, ‖(gaussianRowMap A).kerᗮ.starProjection x‖ ≤ K*‖gaussianRowMap A x‖)
    (hsmall : K*((h:ℝ)*δ) < 1) (haK : 4+4*K*(h:ℝ) ≤ a)
    (hδ : δ ≤ u/(2*a)) (hr : r i = u/2) (c : Space m) :
    ((gaussianDirectionSliceMeasure ν A δ).restrict (gaussianDirectionGood ν δ r TD M A))
      {w | dist (normalize (e ((gaussianRowMap A).ker.orthogonalProjectionOnto (w:Space d)))) c ≤ u/(2*a)} ≤ TD i := by
  have hs : 0 < u/(2*a) := by positivity
  have he : a*(u/(2*a)) = u/2 := by field_simp
  have h₁ := mul_le_mul_of_nonneg_right haK hs.le
  have h₂ := mul_le_mul_of_nonneg_left hδ (by positivity : 0 ≤ 4*K*(h:ℝ))
  have hrad : 4*(u/(2*a))+4*(K*((h:ℝ)*δ)) ≤ r i := by
    rw [hr]
    nlinarith
  exact gaussian_pruned_oriented_direction_closed_ball ν A e δ r TD M i hK hs hbound hsmall hrad c

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Slicing_GaussianFrostmanTransfer
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Frostman bounds for the actual normalized and oriented slice laws -/

namespace Falconer
open Set MeasureTheory NormedSpace
open scoped ENNReal
variable {d h m : ℕ}

theorem gaussian_point_normalized_frostman
    (μ : Measure (Space d)) [IsFiniteMeasure μ] (A : Fin h → Space d) (z : Space h)
    (e : (gaussianRowMap A).ker ≃ₗᵢ[ℝ] Space m) (N : ℕ)
    (r : Fin (N+1) → ℝ) (TP : Fin (N+1) → ℝ≥0∞)
    (hr : ∀ g, r g = (1/(2:ℝ)^g.val)/2)
    {K L a H P f : ℝ} (hK : 0 ≤ K) (hL : 0 < L) (ha : 1 ≤ a) (hH : 1 ≤ H)
    (hP : 0 ≤ P) (hf : 0 ≤ f)
    (hbound : ∀ x : Space d, ‖(gaussianRowMap A).kerᗮ.starProjection x‖ ≤ K*‖gaussianRowMap A x‖)
    (haK : 4*L+2*K*(h:ℝ) ≤ a)
    (hTP : ∀ g, TP g ≤ ENNReal.ofReal (P*(1/(2:ℝ)^g.val)^f))
    (hα : ((gaussianPointSliceMeasure μ A z (1/(2:ℝ)^N)).restrict
      (gaussianPointGood μ (1/(2:ℝ)^N) r TP (A,z))) univ ≠ 0)
    (hratio : ENNReal.ofReal P /
      (((gaussianPointSliceMeasure μ A z (1/(2:ℝ)^N)).restrict
        (gaussianPointGood μ (1/(2:ℝ)^N) r TP (A,z))) univ) ≤ ENNReal.ofReal H) :
    ∀ (c : Space m) (s : ℝ), 1/(2:ℝ)^N ≤ s →
      (normalizedSliceLaw ((gaussianPointSliceMeasure μ A z (1/(2:ℝ)^N)).restrict
        (gaussianPointGood μ (1/(2:ℝ)^N) r TP (A,z))) hα : Measure (Space d))
        {x | dist (L⁻¹ • e ((gaussianRowMap A).ker.orthogonalProjectionOnto x)) c ≤ s} ≤
      ENNReal.ofReal (H*(4*a*s)^f) := by
  let α := (gaussianPointSliceMeasure μ A z (1/(2:ℝ)^N)).restrict
    (gaussianPointGood μ (1/(2:ℝ)^N) r TP (A,z))
  apply truncated_dyadic_ball_bound (normalizedSliceLaw α hα : Measure (Space d))
    (fun x => L⁻¹ • e ((gaussianRowMap A).ker.orthogonalProjectionOnto x)) N ha hH hf (by simp)
  intro g hg hcut c
  let j : Fin (N+1) := ⟨g,by omega⟩
  have hδ : 1/(2:ℝ)^N ≤ (1/(2:ℝ)^g)/(2*a) :=
    (le_div_iff₀ (by positivity)).mpr (by simpa only [mul_comm,mul_left_comm,mul_assoc] using hcut)
  have hball := gaussian_scaled_point_test μ A z e (1/(2:ℝ)^N) r TP j hK hL
    (by linarith) (by positivity) hbound haK hδ (hr j) c
  rw [normalizedSliceLaw_apply]
  calc
    _ ≤ (α univ)⁻¹*ENNReal.ofReal (P*(1/(2:ℝ)^g)^f) :=
      mul_le_mul' le_rfl (hball.trans (hTP j))
    _ = (ENNReal.ofReal P / α univ)*ENNReal.ofReal ((1/(2:ℝ)^g)^f) := by
      rw [ENNReal.ofReal_mul hP]
      simp only [div_eq_mul_inv]
      ac_rfl
    _ ≤ ENNReal.ofReal H*ENNReal.ofReal ((1/(2:ℝ)^g)^f) := mul_le_mul' hratio le_rfl
    _ = _ := by rw [← ENNReal.ofReal_mul (by linarith : 0 ≤ H)]

theorem gaussian_direction_normalized_frostman
    (ν : Measure (Sphere d)) [IsFiniteMeasure ν] (A : Fin h → Space d)
    (e : (gaussianRowMap A).ker ≃ₗᵢ[ℝ] Space m) (N : ℕ)
    (r : Fin (N+1) → ℝ) (TD : Fin (N+1) → ℝ≥0∞) (M : ℝ≥0∞)
    (hr : ∀ g, r g = (1/(2:ℝ)^g.val)/2)
    {K a H P b : ℝ} (hK : 0 ≤ K) (ha : 1 ≤ a) (hH : 1 ≤ H) (hP : 0 ≤ P) (hb : 0 ≤ b)
    (hbound : ∀ x : Space d, ‖(gaussianRowMap A).kerᗮ.starProjection x‖ ≤ K*‖gaussianRowMap A x‖)
    (hsmall : K*((h:ℝ)*(1/(2:ℝ)^N)) < 1) (haK : 4+4*K*(h:ℝ) ≤ a)
    (hTD : ∀ g, TD g ≤ ENNReal.ofReal (P*(1/(2:ℝ)^g.val)^b))
    (hβ : ((gaussianDirectionSliceMeasure ν A (1/(2:ℝ)^N)).restrict
      (gaussianDirectionGood ν (1/(2:ℝ)^N) r TD M A)) univ ≠ 0)
    (hratio : ENNReal.ofReal P /
      (((gaussianDirectionSliceMeasure ν A (1/(2:ℝ)^N)).restrict
        (gaussianDirectionGood ν (1/(2:ℝ)^N) r TD M A)) univ) ≤ ENNReal.ofReal H) :
    ∀ (c : Space m) (s : ℝ), 1/(2:ℝ)^N ≤ s →
      (normalizedSliceLaw ((gaussianDirectionSliceMeasure ν A (1/(2:ℝ)^N)).restrict
        (gaussianDirectionGood ν (1/(2:ℝ)^N) r TD M A)) hβ : Measure (Sphere d))
        {w | dist (normalize (e ((gaussianRowMap A).ker.orthogonalProjectionOnto (w:Space d)))) c ≤ s} ≤
      ENNReal.ofReal (H*(4*a*s)^b) := by
  let β := (gaussianDirectionSliceMeasure ν A (1/(2:ℝ)^N)).restrict
    (gaussianDirectionGood ν (1/(2:ℝ)^N) r TD M A)
  apply truncated_dyadic_ball_bound (normalizedSliceLaw β hβ : Measure (Sphere d))
    (fun w : Sphere d => normalize (e ((gaussianRowMap A).ker.orthogonalProjectionOnto (w:Space d))))
    N ha hH hb (by simp)
  intro g hg hcut c
  let j : Fin (N+1) := ⟨g,by omega⟩
  have hδ : 1/(2:ℝ)^N ≤ (1/(2:ℝ)^g)/(2*a) :=
    (le_div_iff₀ (by positivity)).mpr (by simpa only [mul_comm,mul_left_comm,mul_assoc] using hcut)
  have hball := gaussian_normalized_direction_test ν A e (1/(2:ℝ)^N) r TD M j hK
    (by linarith) (by positivity) hbound hsmall haK hδ (hr j) c
  rw [normalizedSliceLaw_apply]
  calc
    _ ≤ (β univ)⁻¹*ENNReal.ofReal (P*(1/(2:ℝ)^g)^b) :=
      mul_le_mul' le_rfl (hball.trans (hTD j))
    _ = (ENNReal.ofReal P / β univ)*ENNReal.ofReal ((1/(2:ℝ)^g)^b) := by
      rw [ENNReal.ofReal_mul hP]
      simp only [div_eq_mul_inv]
      ac_rfl
    _ ≤ ENNReal.ofReal H*ENNReal.ofReal ((1/(2:ℝ)^g)^b) := mul_le_mul' hratio le_rfl
    _ = _ := by rw [← ENNReal.ofReal_mul (by linarith : 0 ≤ H)]

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Slicing_GaussianPlanarExclusion
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Excluding a large actual Gaussian slice using the published planar input -/

namespace Falconer
open Set MeasureTheory NormedSpace
open scoped ENNReal

theorem gaussian_planar_slice_exclusion
    (hpublished : PublishedPlanarFurstenberg) {b f : ℝ}
    (hb : 0 < b) (hb' : b ≤ 1/2) (hbf : b < f) (hf : f < 1) (C : ℝ) :
    ∃ η δ₀ : ℝ, 0 < η ∧ 0 < δ₀ ∧
    ∀ (N d h : ℕ) (κ : Type) [Fintype κ] [DecidableEq κ]
      (A : Fin h → Space d) (z : Space h) (e : (gaussianRowMap A).ker ≃ₗᵢ[ℝ] Space 2)
      (μ : Measure (Space d)) (ν : Measure (Sphere d)) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
      (E : Set (Space d × Sphere d)) (J : Sphere d → Finset κ) (a : κ → Space d)
      (K V M T a₀ : ℝ),
    1/(2:ℝ)^N < δ₀ → 0 < K → 0 < V → 0 ≤ M → 0 ≤ T →
    T ≤ (1/(2:ℝ)^N)^(-b-η) →
    1 ≤ a₀ → 1 ≤ 4*K^10*V → 4+8*(h:ℝ) ≤ a₀ →
    (4*K^10*V)*(4*a₀)^f ≤ (1/(2:ℝ)^N)^(-η) →
    (4*K^10*V)*(8*a₀)^b ≤ (1/(2:ℝ)^N)^(-η) →
    (1/(2:ℝ)^N)^η < 1/(4*K^10*V) →
    MeasurableSet E → (∀ i, MeasurableSet {w | i ∈ J w}) →
    (∀ i, ‖A i‖ ≤ M) →
    (∀ x : Space d, ‖(gaussianRowMap A).kerᗮ.starProjection x‖ ≤ 2*‖gaussianRowMap A x‖) →
    2*((h:ℝ)*(1/(2:ℝ)^N)) < 1 →
    (∀ u ∈ E, ‖u.1‖ ≤ 1/4) → (∀ w, ∀ i ∈ J w, ‖a i‖ ≤ 1/4) →
    (∀ u ∈ E, ∃ i ∈ J u.2, ‖perpendicularPart (u.2:Space d) (u.1-a i)‖ ≤ C*(1/(2:ℝ)^N)) →
    (∀ᵐ x ∂μ, ‖x‖ ≤ 1/4) →
    (∀ᵐ w : Sphere d ∂ν, w ∈ gaussianDirectionBand A (1/(2:ℝ)^N) →
      ‖normalize (e ((gaussianRowMap A).ker.orthogonalProjectionOnto (w:Space d)))‖ = 1 ∧
      dist (normalize (e ((gaussianRowMap A).ker.orthogonalProjectionOnto (w:Space d))))
        (EuclideanSpace.basisFun (Fin 2) ℝ 0) ≤ 1/4) →
    gaussianPrunedPairMass μ ν (1/(2:ℝ)^N)
      (fun g : Fin (N+1) => (1/(2:ℝ)^g.val)/2)
      (fun g => ENNReal.ofReal (K^6*(1/(2:ℝ)^g.val)^f))
      (fun g => ENNReal.ofReal (K^3*(1/(2:ℝ)^g.val)^b)) (ENNReal.ofReal (K^3))
      (gaussianActiveRelation E J a
        ((1/(2:ℝ)^N)+(2*(1/4))*(1/(2:ℝ)^N)+(C*(1/(2:ℝ)^N))*M)
        (ENNReal.ofReal T) true) (A,z) ≤ ENNReal.ofReal (1/(4*K*V)) := by
  classical
  obtain ⟨η,δ₀,hη,hδ₀,hgain⟩ := planar_selected_slice_gain hpublished hb hb' hbf hf C
  refine ⟨η,δ₀,hη,hδ₀,?_⟩
  intro N d h κ _ _ A z e μ ν _ _ E J a K V M T a₀ hδsmall hK hV hM hT hTbound
    ha₀ hH haK hpcoef hqcoef hlow hE hJ hA hbound hsmall hEb hanchors hcover hμ hν
  let δ : ℝ := 1/(2:ℝ)^N
  let r : Fin (N+1) → ℝ := fun g => (1/(2:ℝ)^g.val)/2
  let TP : Fin (N+1) → ℝ≥0∞ := fun g => ENNReal.ofReal (K^6*(1/(2:ℝ)^g.val)^f)
  let TD : Fin (N+1) → ℝ≥0∞ := fun g => ENNReal.ofReal (K^3*(1/(2:ℝ)^g.val)^b)
  let α := (gaussianPointSliceMeasure μ A z δ).restrict (gaussianPointGood μ δ r TP (A,z))
  let β := (gaussianDirectionSliceMeasure ν A δ).restrict
    (gaussianDirectionGood ν δ r TD (ENNReal.ofReal (K^3)) A)
  let R := δ+(2*(1/4))*δ+(C*δ)*M
  let F := selectedActiveRelation A z δ E J a R T
  have hδ : 0 < δ := by dsimp [δ]; positivity
  by_contra hnot
  have hmass : ENNReal.ofReal (1/(4*K*V)) ≤ (α.prod β) F := by
    have hi := (lt_of_not_ge hnot).le
    change _ ≤ gaussianPrunedIncidence μ ν δ r TP TD (ENNReal.ofReal (K^3)) F (A,z)
    rw [show F = {u | ((A,z),u) ∈ gaussianActiveRelation E J a R (ENNReal.ofReal T) true} ∩
      (gaussianPointBand A z δ ×ˢ gaussianDirectionBand A δ) from rfl,
      gaussian_pruned_incidence_inter_bands μ ν δ r TP TD (ENNReal.ofReal (K^3))
        {u | ((A,z),u) ∈ gaussianActiveRelation E J a R (ENNReal.ofReal T) true} (A,z)]
    exact hi
  have hαmass : α univ ≤ ENNReal.ofReal (K^6) := by
    have hm := gaussianPointGood_mass μ δ r TP (A,z) hμ 0 (by norm_num [r])
    simpa only [TP,Fin.val_zero,pow_zero,div_one,Real.one_rpow,mul_one] using hm
  have hβmass : β univ ≤ ENNReal.ofReal (K^3) := gaussianDirectionGood_mass ν δ r TD _ A
  obtain ⟨hα,hβ,hαratio,hβratio,_,_,hinc⟩ :=
    polynomial_slice_normalization α β F hK hV hαmass hβmass hmass
  let α' := normalizedSliceLaw α hα
  let β' := normalizedSliceLaw β hβ
  have hpball (c : Space 2) (s : ℝ) (hs : δ ≤ s) :
      (α' : Measure (Space d)).real {x | dist (e ((gaussianRowMap A).ker.orthogonalProjectionOnto x)) c ≤ s}
        ≤ δ^(-η)*s^f := by
    have hh := gaussian_point_normalized_frostman μ A z e N r TP (fun _ => rfl)
      (by norm_num) (by norm_num : (0:ℝ) < 1) ha₀ hH (pow_nonneg hK.le 6)
      (hb.le.trans hbf.le) hbound (by linarith) (fun _ => le_rfl) hα hαratio c s hs
    simp only [inv_one,one_smul] at hh
    have hs0 : 0 ≤ s := hδ.le.trans hs
    have hc : (4*K^10*V)*(4*a₀*s)^f ≤ δ^(-η)*s^f := by
      rw [Real.mul_rpow (by positivity) hs0]
      simpa only [mul_assoc] using mul_le_mul_of_nonneg_right hpcoef (Real.rpow_nonneg hs0 f)
    exact (ENNReal.toReal_mono ENNReal.ofReal_ne_top hh).trans (by
      simpa only [ENNReal.toReal_ofReal (by positivity : 0 ≤ (4*K^10*V)*(4*a₀*s)^f)] using hc)
  have hqball (c : Space 2) (s : ℝ) (hs : δ ≤ s) :
      (β' : Measure (Sphere d)).real
        {w | dist (normalize (e ((gaussianRowMap A).ker.orthogonalProjectionOnto (w:Space d)))) c ≤ 2*s}
        ≤ δ^(-η)*s^b := by
    have hs0 : 0 ≤ s := hδ.le.trans hs
    have hh := gaussian_direction_normalized_frostman ν A e N r TD (ENNReal.ofReal (K^3))
      (fun _ => rfl) (by norm_num) ha₀ hH (pow_nonneg hK.le 3) hb.le hbound hsmall
      (by linarith) (fun _ => le_rfl) hβ hβratio c (2*s) (by linarith)
    have hc : (4*K^10*V)*(4*a₀*(2*s))^b ≤ δ^(-η)*s^b := by
      rw [show 4*a₀*(2*s) = (8*a₀)*s by ring,Real.mul_rpow (by positivity) hs0]
      simpa only [mul_assoc] using mul_le_mul_of_nonneg_right hqcoef (Real.rpow_nonneg hs0 b)
    exact (ENNReal.toReal_mono ENNReal.ofReal_ne_top hh).trans (by
      simpa only [ENNReal.toReal_ofReal (by positivity : 0 ≤ (4*K^10*V)*(4*a₀*(2*s))^b)] using hc)
  have hαsupport : ∀ᵐ x ∂(α' : Measure (Space d)), ‖x‖ ≤ 1/4 :=
    normalizedSliceLaw_ae α hα (ae_restrict_of_ae (gaussianPointSliceMeasure_ae_of_ae μ A z δ hμ))
  have hβsupport : ∀ᵐ (w : Sphere d) ∂(β' : Measure (Sphere d)),
      ‖normalize (e ((gaussianRowMap A).ker.orthogonalProjectionOnto (w:Space d)))‖ = 1 ∧
      dist (normalize (e ((gaussianRowMap A).ker.orthogonalProjectionOnto (w:Space d))))
        (EuclideanSpace.basisFun (Fin 2) ℝ 0) ≤ 1/4 := by
    apply normalizedSliceLaw_ae β hβ
    have hc : ∀ᵐ (w : Sphere d) ∂β, w ∈ gaussianDirectionBand A δ →
        ‖normalize (e ((gaussianRowMap A).ker.orthogonalProjectionOnto (w:Space d)))‖ = 1 ∧
        dist (normalize (e ((gaussianRowMap A).ker.orthogonalProjectionOnto (w:Space d))))
          (EuclideanSpace.basisFun (Fin 2) ℝ 0) ≤ 1/4 :=
      ae_restrict_of_ae (Measure.ae_smul_measure (ae_restrict_of_ae hν) _)
    have hbnd : ∀ᵐ (w : Sphere d) ∂β, w ∈ gaussianDirectionBand A δ :=
      ae_restrict_of_ae (Measure.ae_smul_measure (ae_restrict_mem (gaussianDirectionBand_measurable A δ)) _)
    filter_upwards [hc,hbnd] with w hw hbnd
    exact hw hbnd
  have hu := hgain δ hδ hδsmall d h κ A z e α' β' E J a M 2 T hE hJ hM (by norm_num)
    hT hTbound hA hbound hsmall hEb hanchors hcover hαsupport hβsupport hpball hqball
  have hl : 1/(4*K^10*V) ≤ ((α' : Measure (Space d)).prod (β' : Measure (Sphere d))).real F := by
    have hh := ENNReal.toReal_mono (measure_ne_top _ _) hinc
    simpa only [α',β',Measure.real,ENNReal.toReal_ofReal (by positivity : 0 ≤ 1/(4*K^10*V))] using hh
  exact (not_lt_of_ge (hl.trans hu)) hlow

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Slicing_GaussianThreshold
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A uniform positive incidence threshold on the bounded parameter box -/

namespace Falconer
open MeasureTheory
open scoped ENNReal

theorem gaussianSelectionThreshold_budget (h : ℕ) {K Z : ℝ} (hK : 0 < K) (hZ : 0 < Z) :
    gaussianSelectionThreshold h K Z * volume (coordinateBox h Z) =
      ENNReal.ofReal (1/(4*K)) := by
  rw [gaussianSelectionThreshold,coordinateBox_volume hZ.le,
    ← ENNReal.ofReal_mul (by positivity)]
  congr 1
  field_simp

theorem gaussianSelectionThreshold_uniform (h : ℕ) {K Z Z₀ : ℝ}
    (hK : 0 < K) (hZ₀ : 0 < Z₀) (hZZ : Z ≤ Z₀) :
    gaussianSelectionThreshold h K Z₀ * volume (coordinateBox h Z) ≤
      ENNReal.ofReal (1/(4*K)) := by
  have hsub : coordinateBox h Z ⊆ coordinateBox h Z₀ := fun x hx i => (hx i).trans hZZ
  exact (mul_le_mul' le_rfl (measure_mono hsub)).trans_eq (gaussianSelectionThreshold_budget h hK hZ₀)

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Angular_ControlledAngularGain
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A finite-scale angular gain on each controlled original direction chart -/

namespace Falconer
open Set MeasureTheory NormedSpace
open scoped ENNReal

theorem controlled_dyadic_angular_gain_oai
    (hpublished : PublishedPlanarFurstenberg) {h : ℕ} {t q : ℝ}
    (hq : (h:ℝ) < q) (hq' : q-(h:ℝ) ≤ 1/2) (hqt : q < t) (ht : t-(h:ℝ) < 1)
    {C : ℝ} (hC : 0 ≤ C) :
    ∃ η δ₀ : ℝ, 0 < η ∧ 0 < δ₀ ∧
    ∀ (N : ℕ) (κ : Type) [Fintype κ] [DecidableEq κ]
      (μ : Measure (Space (h+2))) (ν : Measure (Sphere (h+2)))
      [IsFiniteMeasure μ] [IsFiniteMeasure ν]
      (w₀ : Sphere (h+2)) (B : Space h →ₗᵢ[ℝ] Space (h+2))
      (E : Set (Space (h+2) × Sphere (h+2)))
      (J : Sphere (h+2) → Finset κ) (a : κ → Space (h+2))
      (ρ Lt Lq K C₀ Nc Z a₀ : ℝ),
    1/(2:ℝ)^N < δ₀ → 0 ≤ ρ → 1/(2:ℝ)^N ≤ ρ →
    (∀ i, inner ℝ (w₀:Space (h+2)) (B (EuclideanSpace.basisFun (Fin h) ℝ i)) = 0) →
    (∀ᵐ w ∂ν, dist w w₀ ≤ ρ) →
    (h:ℝ)*((h+2:ℝ)*(2*ρ)) ≤ 1/2 →
    4*(h:ℝ)*(1/(2:ℝ)^N)+ρ+4*(h:ℝ)*((h+2:ℝ)*(2*ρ)) ≤ 1/4 →
    (∀ᵐ x ∂μ, ‖x‖ ≤ 1/4) → μ univ ≤ 1 → ν univ ≤ 1 →
    0 ≤ Lt → 0 ≤ Lq →
    (∀ x : Space (h+2), ∀ j : ℕ, j ≤ N →
      μ (Metric.ball x (1/(2:ℝ)^j)) ≤ ENNReal.ofReal (Lt*(1/(2:ℝ)^j)^t)) →
    (∀ x : Sphere (h+2), ∀ j : ℕ, j ≤ N →
      ν (Metric.ball x (1/(2:ℝ)^j)) ≤ ENNReal.ofReal (Lq*(1/(2:ℝ)^j)^q)) →
    (∀ᵐ u : Sphere (h+2) × Sphere (h+2) ∂ν.prod ν,
      0 ≤ inner ℝ (u.1:Space (h+2)) (u.2:Space (h+2))) →
    0 < K → 0 < Nc → 0 < Z →
    (4*gaussianVectorBandConstant)^h*Lt*gaussianFrostmanFactor h t ≤ C₀ →
    (2*gaussianPairBandConstant)^h*Lq*gaussianFrostmanFactor h q ≤ C₀ →
    (2*gaussianPairBandConstant)^h*(|Lq*gaussianFrostmanFactor h q|+1) ≤ C₀ →
    ((N+1:ℕ):ℝ)*C₀ ≤ K → C₀ ≤ K → 4*(1+2*(2:ℝ)^h+1) ≤ K →
    (1/4)*((h+2:ℝ)*(2*ρ)+1)+1/(2:ℝ)^N ≤ Z →
    1 ≤ a₀ → 1 ≤ 4*K^10*(2*Z)^h → 4+8*(h:ℝ) ≤ a₀ →
    (4*K^10*(2*Z)^h)*(4*a₀)^(t-(h:ℝ)) ≤ (1/(2:ℝ)^N)^(-η) →
    (4*K^10*(2*Z)^h)*(8*a₀)^(q-(h:ℝ)) ≤ (1/(2:ℝ)^N)^(-η) →
    (1/(2:ℝ)^N)^η < 1/(4*K^10*(2*Z)^h) →
    K^11*(Nc*(2*((1/(2:ℝ)^N)+(2*(1/4))*(1/(2:ℝ)^N)+
      (C*(1/(2:ℝ)^N))*((h+2:ℝ)*(2*ρ)+1)))^h) ≤ (1/(2:ℝ)^N)^(-(q-(h:ℝ))-η) →
    MeasurableSet E → (∀ i, MeasurableSet {w | i ∈ J w}) →
    (∀ w, ((J w).card : ℝ≥0∞) ≤ ENNReal.ofReal Nc) →
    (∀ u ∈ E, ‖u.1‖ ≤ 1/4) → (∀ w, ∀ i ∈ J w, ‖a i‖ ≤ 1/4) →
    (∀ u ∈ E, ∃ i ∈ J u.2,
      ‖perpendicularPart (u.2:Space (h+2)) (u.1-a i)‖ ≤ C*(1/(2:ℝ)^N)) →
    ENNReal.ofReal ((2:ℝ)^h)*ENNReal.ofReal (gaussianLocalBandConstant (h+1) ρ^h)*
      (μ.prod ν) E < ENNReal.ofReal (1/K) := by
  classical
  obtain ⟨η,δ₀,hη,hδ₀,hgain⟩ := gaussian_planar_slice_exclusion hpublished
    (sub_pos.mpr hq) hq' (by linarith : q-(h:ℝ) < t-(h:ℝ)) ht C
  refine ⟨η,δ₀,hη,hδ₀,?_⟩
  intro N κ _ _ μ ν _ _ w₀ B E J a ρ Lt Lq K C₀ Nc Z a₀ hδsmall hρ hδρ
    hB hν hstable hchart hμ hμmass hνmass hLt hLq hμball hνball hpair
    hK hNc hZ hCpoint hCdir hCmass hcard hC₀ hlarge hZbox ha₀ hH haK hpcoef hqcoef hlow
    hTbound hE hJ hJN hEb hanchors hcover
  let δ : ℝ := 1/(2:ℝ)^N
  let ε : ℝ := (h+2:ℝ)*(2*ρ)
  let M : ℝ := ε+1
  let R : ℝ := δ+(2*(1/4))*δ+(C*δ)*M
  let T : ℝ := K^11*(Nc*(2*R)^h)
  let rows : Fin h → Space (h+2) := fun i => B (EuclideanSpace.basisFun (Fin h) ℝ i)
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hε : 0 ≤ ε := by dsimp [ε]; positivity
  have hM : 0 ≤ M := by dsimp [M]; positivity
  have hR : 0 < R := by dsimp [R]; positivity
  have hrows (i : Fin h) : ‖rows i‖ ≤ 1 := by
    rw [show rows i = B (EuclideanSpace.basisFun (Fin h) ℝ i) from rfl,B.norm_map]
    exact ((EuclideanSpace.basisFun (Fin h) ℝ).norm_eq_one i).le
  have hwB : ∀ᵐ (w : Sphere (h+2)) ∂ν, ∀ i, |inner ℝ (w:Space (h+2)) (rows i)| ≤ ρ := by
    filter_upwards [hν] with w hw i
    exact transverse_frame_chart_bound B (w₀:Space (h+2)) hB hw i
  by_contra hnot
  have hmean := le_of_not_gt hnot
  have hfactor : ENNReal.ofReal ((2:ℝ)^h)*μ univ ≤ ENNReal.ofReal ((2:ℝ)^h) := by
    simpa only [mul_one] using mul_le_mul' le_rfl hμmass
  have hcast : ((h+1:ℕ):ℝ)+1 = (h+2:ℝ) := by push_cast; ring
  obtain ⟨A,hA,z,_,hbig⟩ := dyadic_original_slice_selection rows hrows μ ν N
    (by norm_num : (1/4:ℝ) < 1/2) hμ hδρ hwB hLt hLq (hq.trans hqt) hq hμmass hνmass
    hμball hνball hpair hK (by positivity : 0 ≤ (2:ℝ)^h) hNc hR hCpoint hCdir hCmass
    hcard hC₀ hlarge hfactor E hE J hJ a hJN hmean
    (by rw [hcast]; exact gaussianSelectionThreshold_uniform h hK hZ hZbox)
  rw [hcast] at hA
  obtain ⟨e,_,he⟩ := gaussian_two_dimensional_slice_chart B A w₀ hε hδ.le hρ hB hA hstable hchart
  have hbound := row_kernel_projection_bound A B hA hstable
  have hsmall : 2*((h:ℝ)*δ) < 1 := by
    have hpos : 0 ≤ 4*(h:ℝ)*ε := by positivity
    change 4*(h:ℝ)*δ+ρ+4*(h:ℝ)*ε ≤ 1/4 at hchart
    nlinarith
  have hchartAE : ∀ᵐ (w : Sphere (h+2)) ∂ν, w ∈ gaussianDirectionBand A δ →
      ‖normalize (e ((gaussianRowMap A).ker.orthogonalProjectionOnto (w:Space (h+2))))‖ = 1 ∧
      dist (normalize (e ((gaussianRowMap A).ker.orthogonalProjectionOnto (w:Space (h+2)))))
        (EuclideanSpace.basisFun (Fin 2) ℝ 0) ≤ 1/4 := by
    filter_upwards [hν] with w hw hband
    exact he w hband hw
  have hupper := hgain N (h+2) h κ A z e μ ν E J a K ((2*Z)^h) M T a₀ hδsmall
    hK (by positivity) hM (by dsimp [T]; positivity) hTbound ha₀ hH haK hpcoef hqcoef hlow
    hE hJ (gaussianRowNeighborhood_norm rows hrows hA) hbound hsmall hEb hanchors hcover hμ hchartAE
  simp only [gaussianSelectionThreshold,gaussianPruningWeight_eq] at hbig
  exact (not_lt_of_ge hupper) hbig

end Falconer

end OAI
end

theorem solution : type_of% @OAI.Falconer.controlled_dyadic_angular_gain_oai := @OAI.Falconer.controlled_dyadic_angular_gain_oai
