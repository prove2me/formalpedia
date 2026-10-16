-- Prove2me | solution 1 for OAI.Problem310.Aux.volume_integerPeriodize_le
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-16T06:49:57.250263+00:00
-- url     : https://prove2.me/submissions/07309b5a-0351-4834-b054-9f9d0f68ab09

-- Generated from openai/math@1581d4c lean/OAI/MeasureTheory/DyadicAvoidance/PeriodicEnvelope.lean:L34-L75
-- (upload_full_project.md Phase 4): solution for node OAI.Problem310.Aux.volume_integerPeriodize_le. The node keeps its source
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

-- ---- from OAI.MeasureTheory.DyadicAvoidance.PeriodicEnvelope ----
namespace OAI

noncomputable section

namespace Problem310.Aux
open Set MeasureTheory

/-- Periodization cannot increase the measure within a fundamental interval
beyond the measure of the original subset. -/
theorem volume_integerPeriodize_le (U : Set ℝ) (hU : MeasurableSet U) :
    volume (integerPeriodize U ∩ Icc (0 : ℝ) 1) ≤ volume U := by
  have hae : (integerPeriodize U ∩ Icc (0 : ℝ) 1 : Set ℝ) =ᵐ[volume]
      (integerPeriodize U ∩ Ico (0 : ℝ) 1 : Set ℝ) :=
    Filter.EventuallyEq.inter Filter.EventuallyEq.rfl Ico_ae_eq_Icc.symm
  rw [measure_congr hae]
  have hpiece (k : ℤ) :
      volume (((fun x : ℝ => x + (k : ℝ)) ⁻¹' U) ∩ Ico (0 : ℝ) 1) =
        volume (U ∩ Ico (k : ℝ) ((k : ℝ) + 1)) := by
    have hI : (fun x : ℝ => x + (k : ℝ)) ⁻¹' Ico (k : ℝ) ((k : ℝ) + 1) =
        Ico (0 : ℝ) 1 := by
      ext x
      simp only [mem_preimage, mem_Ico]
      constructor <;> rintro ⟨h1, h2⟩ <;> constructor <;> linarith
    rw [← hI, ← preimage_inter]
    exact measure_preimage_add_right volume (k : ℝ) _
  have hdisj : Pairwise (Function.onFun Disjoint
      (fun k : ℤ => U ∩ Ico (k : ℝ) ((k : ℝ) + 1))) := by
    intro i j hij
    apply Set.disjoint_left.2
    intro x hx hy
    rcases lt_or_gt_of_ne hij with h | h
    · have hcast : (i : ℝ) + 1 ≤ (j : ℝ) := by
        exact_mod_cast (show i + 1 ≤ j by omega)
      linarith [hx.2.2, hy.2.1]
    · have hcast : (j : ℝ) + 1 ≤ (i : ℝ) := by
        exact_mod_cast (show j + 1 ≤ i by omega)
      linarith [hy.2.2, hx.2.1]
  have hunion : (⋃ k : ℤ, U ∩ Ico (k : ℝ) ((k : ℝ) + 1)) = U := by
    rw [← inter_iUnion, iUnion_Ico_intCast, inter_univ]
  calc
    volume (integerPeriodize U ∩ Ico (0 : ℝ) 1)
        = volume (⋃ k : ℤ, ((fun x : ℝ => x + (k : ℝ)) ⁻¹' U) ∩ Ico (0 : ℝ) 1) := by
          rw [integerPeriodize, iUnion_inter]
    _ ≤ ∑' k : ℤ, volume (((fun x : ℝ => x + (k : ℝ)) ⁻¹' U) ∩ Ico (0 : ℝ) 1) :=
      measure_iUnion_le _
    _ = ∑' k : ℤ, volume (U ∩ Ico (k : ℝ) ((k : ℝ) + 1)) := tsum_congr hpiece
    _ = volume (⋃ k : ℤ, U ∩ Ico (k : ℝ) ((k : ℝ) + 1)) :=
      (measure_iUnion hdisj (fun k => hU.inter measurableSet_Ico)).symm
    _ = volume U := congrArg volume hunion

end Problem310.Aux

end

end OAI

-- ---- platform node ----
open OAI OAI.Problem310 OAI.Problem310.Aux
open Set MeasureTheory


theorem solution : type_of% @_root_.OAI.Problem310.Aux.volume_integerPeriodize_le := @_root_.OAI.Problem310.Aux.volume_integerPeriodize_le
