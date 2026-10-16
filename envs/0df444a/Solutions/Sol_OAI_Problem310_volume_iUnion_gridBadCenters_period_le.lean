-- Prove2me | solution 1 for OAI.Problem310.volume_iUnion_gridBadCenters_period_le
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-16T07:24:59.087133+00:00
-- url     : https://prove2.me/submissions/8308b600-a5a9-426d-8022-ab7d2fd31e71

-- Generated from openai/math@1581d4c lean/OAI/MeasureTheory/DyadicAvoidance/GridMeasure.lean:L102-L123
-- (upload_full_project.md Phase 4): solution for node OAI.Problem310.volume_iUnion_gridBadCenters_period_le. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_DyadicAvoidance
import Definitions.Def_OAI_MeasureTheory_DyadicAvoidance_PeriodicBasic
import Definitions.Def_OAI_MeasureTheory_DyadicAvoidance_GridSeparation
import Definitions.Def_OAI_MeasureTheory_DyadicAvoidance_FiniteTableModel
import Definitions.Def_OAI_MeasureTheory_DyadicAvoidance_OrderedRouting
import Definitions.Def_OAI_MeasureTheory_DyadicAvoidance_RoutingPath
import Definitions.Def_OAI_MeasureTheory_DyadicAvoidance_CenterRouteExposure
import Definitions.Def_OAI_MeasureTheory_DyadicAvoidance_ExceptionalCenters
import Definitions.Def_OAI_MeasureTheory_DyadicAvoidance_CenterFailureBound
import Definitions.Def_OAI_MeasureTheory_DyadicAvoidance_FirstDefault
import Definitions.Def_OAI_MeasureTheory_DyadicAvoidance_ConcreteLabelMeasures
import Definitions.Def_OAI_MeasureTheory_DyadicAvoidance_CenterFirstDefault
import Definitions.Def_OAI_MeasureTheory_DyadicAvoidance_RandomSetDensity
import Definitions.Def_OAI_MeasureTheory_DyadicAvoidance_RoutedSetDensity
import Definitions.Def_OAI_MeasureTheory_DyadicAvoidance_RoutedExposure
import Definitions.Def_OAI_MeasureTheory_DyadicAvoidance_FirstDefaultSelection
import Definitions.Def_OAI_MeasureTheory_DyadicAvoidance_FiniteLocalPredicate
import Definitions.Def_OAI_MeasureTheory_DyadicAvoidance_WindowData
import Definitions.Def_OAI_MeasureTheory_DyadicAvoidance_WindowTableModel
import Definitions.Def_OAI_MeasureTheory_DyadicAvoidance_StableRoutingBridge
import Definitions.Def_OAI_MeasureTheory_DyadicAvoidance_WindowExceptionalTransfer
import Definitions.Def_OAI_MeasureTheory_DyadicAvoidance_TrialAddresses
import Definitions.Def_OAI_MeasureTheory_DyadicAvoidance_WindowTrialAddresses
import Definitions.Def_OAI_MeasureTheory_DyadicAvoidance_ConcreteWindowAtom
import Definitions.Def_OAI_MeasureTheory_DyadicAvoidance_PeriodicEnvelope
import Definitions.Def_OAI_MeasureTheory_DyadicAvoidance_GlobalFromPeriodic
import Definitions.Def_OAI_MeasureTheory_DyadicAvoidance_GridGeometry
import Definitions.Def_OAI_MeasureTheory_DyadicAvoidance_GridMeasure
import Theorems.Thm_OAI_Problem310_gridBadCenters_period_subset

-- ---- from OAI.MeasureTheory.DyadicAvoidance.GridMeasure ----
namespace OAI

universe u_ι

noncomputable section
namespace Problem310
open MeasureTheory Set

theorem volume_gridBadCenters_period_le (q : ℕ) (hq : 0 < q) {δ : ℝ}
    (_hδ0 : 0 ≤ δ) (hδ : δ ≤ (q : ℝ)⁻¹) :
    volume (gridBadCenters q δ ∩ Icc (0 : ℝ) 1) ≤ ENNReal.ofReal ((q : ℝ) * δ) := by
  have hae : (gridBadCenters q δ ∩ Icc (0 : ℝ) 1 : Set ℝ) =ᵐ[volume]
      (gridBadCenters q δ ∩ Ico (0 : ℝ) 1 : Set ℝ) := by
    exact Filter.EventuallyEq.inter Filter.EventuallyEq.rfl
      (Ico_ae_eq_Icc (μ := volume) (a := (0 : ℝ)) (b := 1)).symm
  rw [measure_congr hae]
  calc
    volume (gridBadCenters q δ ∩ Ico (0 : ℝ) 1)
      ≤ volume (⋃ i : Fin q, Ico (((i.val + 1 : ℕ) : ℝ) / q - δ)
          (((i.val + 1 : ℕ) : ℝ) / q)) :=
        measure_mono (gridBadCenters_period_subset q hq hδ)
    _ ≤ ∑ i : Fin q, volume (Ico (((i.val + 1 : ℕ) : ℝ) / q - δ)
          (((i.val + 1 : ℕ) : ℝ) / q)) := measure_iUnion_fintype_le _ _
    _ = ENNReal.ofReal ((q : ℝ) * δ) := by
      simp only [Real.volume_Ico, sub_sub_cancel]
      simp [ENNReal.ofReal_mul]

/-- The exceptional density for any finite family of stability requirements
is bounded by the sum of its grid-width budgets. -/
theorem volume_iUnion_gridBadCenters_period_le {ι : Type u_ι} [Fintype ι]
    (q : ι → ℕ) (δ : ι → ℝ) (hq : ∀ i, 0 < q i)
    (hδ0 : ∀ i, 0 ≤ δ i) (hδ : ∀ i, δ i ≤ (q i : ℝ)⁻¹) :
    volume ((⋃ i, gridBadCenters (q i) (δ i)) ∩ Icc (0 : ℝ) 1) ≤
      ENNReal.ofReal (∑ i, (q i : ℝ) * δ i) := by
  classical
  rw [iUnion_inter]
  calc
    volume (⋃ i, gridBadCenters (q i) (δ i) ∩ Icc (0 : ℝ) 1)
      ≤ ∑ i, volume (gridBadCenters (q i) (δ i) ∩ Icc (0 : ℝ) 1) :=
        measure_iUnion_fintype_le _ _
    _ ≤ ∑ i, ENNReal.ofReal ((q i : ℝ) * δ i) := by
      apply Finset.sum_le_sum
      intro i hi
      exact volume_gridBadCenters_period_le (q i) (hq i) (hδ0 i) (hδ i)
    _ = ENNReal.ofReal (∑ i, (q i : ℝ) * δ i) := by
      symm
      apply ENNReal.ofReal_sum_of_nonneg
      intro i hi
      exact mul_nonneg (Nat.cast_nonneg _) (hδ0 i)

end Problem310

end

end OAI

-- ---- platform node ----
open OAI OAI.Problem310
open MeasureTheory Set


theorem solution.{u_ι} : type_of% @_root_.OAI.Problem310.volume_iUnion_gridBadCenters_period_le.{u_ι} := @_root_.OAI.Problem310.volume_iUnion_gridBadCenters_period_le.{u_ι}
