-- Prove2me | solution 1 for GlobalTheory.GlueCover.glueMeas_finite
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T17:27:48.961135+00:00
-- url     : https://prove2.me/submissions/0f4f4317-1c6e-4bf5-802e-72d9a06a98bc

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_ChartMeasApplyOfSubset
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ChartDensityChangeFormula
import Theorems.Thm_GlobalTheory_GlueCover_chartMeas_finite

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open MeasureTheory Set Topology
open ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Y
open scoped ENNReal
open GlobalTheory GlobalTheory.GlueCover
open GlobalTheory.ChartGlue
variable {n : ℕ}
variable {X ι : Type} [TopologicalSpace X] [T2Space X] [MeasurableSpace X] [BorelSpace X]
namespace GlobalTheory.GlueCover
theorem _root_.solution (hn : n ≠ 0) (e : ι → OpenPartialHomeomorph X (V n)) (ρ : ι → X → ℝ≥0∞)
    {F : Set X} (hF : F.Finite) : glueMeas e ρ F = 0 := by
  have hle : glueMeas e ρ ≤ (glueMeas e ρ).restrict Fᶜ := by
    refine iSup_le fun i => Measure.le_iff.2 fun B hB => ?_
    rw [Measure.restrict_apply hB]
    calc chartMeas (e i) (ρ i) B ≤ chartMeas (e i) (ρ i) (B ∩ Fᶜ ∪ F) :=
          measure_mono fun y hy => by
            by_cases h : y ∈ F
            · exact Or.inr h
            · exact Or.inl ⟨hy, h⟩
      _ ≤ chartMeas (e i) (ρ i) (B ∩ Fᶜ) + chartMeas (e i) (ρ i) F := measure_union_le _ _
      _ = chartMeas (e i) (ρ i) (B ∩ Fᶜ) := by rw [chartMeas_finite hn _ _ hF, add_zero]
      _ ≤ glueMeas e ρ (B ∩ Fᶜ) :=
          Measure.le_iff'.1 (le_iSup (fun i => chartMeas (e i) (ρ i)) i) _
  have h := Measure.le_iff'.1 hle F
  rw [Measure.restrict_apply hF.measurableSet, inter_compl_self, measure_empty] at h
  exact nonpos_iff_eq_zero.1 h
end GlobalTheory.GlueCover
