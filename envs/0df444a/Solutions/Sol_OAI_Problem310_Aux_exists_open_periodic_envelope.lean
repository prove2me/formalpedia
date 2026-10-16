-- Prove2me | solution 1 for OAI.Problem310.Aux.exists_open_periodic_envelope
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-16T06:51:39.239634+00:00
-- url     : https://prove2.me/submissions/93102ff1-821a-4e69-9155-59e15742b6e4

-- Generated from openai/math@1581d4c lean/OAI/MeasureTheory/DyadicAvoidance/PeriodicEnvelope.lean:L77-L99
-- (upload_full_project.md Phase 4): solution for node OAI.Problem310.Aux.exists_open_periodic_envelope. The node keeps its source
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
import Theorems.Thm_OAI_Problem310_Aux_volume_integerPeriodize_le

-- ---- from OAI.MeasureTheory.DyadicAvoidance.PeriodicEnvelope ----
namespace OAI

noncomputable section

namespace Problem310.Aux
open Set MeasureTheory

theorem isOpen_integerPeriodize (U : Set ℝ) (hU : IsOpen U) :
    IsOpen (integerPeriodize U) := by
  exact isOpen_iUnion fun k => hU.preimage (continuous_id.add continuous_const)

theorem integerPeriodize_onePeriodic (U : Set ℝ) :
    ∀ x : ℝ, x + 1 ∈ integerPeriodize U ↔ x ∈ integerPeriodize U := by
  intro x
  simp only [integerPeriodize, mem_iUnion, mem_preimage]
  constructor
  · rintro ⟨k, hk⟩
    refine ⟨k + 1, ?_⟩
    convert hk using 1
    push_cast
    ring
  · rintro ⟨k, hk⟩
    refine ⟨k - 1, ?_⟩
    convert hk using 1
    push_cast
    ring

/-- An arbitrarily small open periodic enlargement of a periodic set. -/
theorem exists_open_periodic_envelope (R : Set ℝ)
    (hR : ∀ x : ℝ, x + 1 ∈ R ↔ x ∈ R) (ε : ENNReal) (hε : ε ≠ 0) :
    ∃ V : Set ℝ, R ⊆ V ∧ IsOpen V ∧
      (∀ x : ℝ, x + 1 ∈ V ↔ x ∈ V) ∧
      volume (V ∩ Icc (0 : ℝ) 1) ≤ volume (R ∩ Icc (0 : ℝ) 1) + ε := by
  obtain ⟨U, hRU, hU, hμU⟩ :=
    (R ∩ Icc (0 : ℝ) 1).exists_isOpen_le_add volume hε
  refine ⟨integerPeriodize U, ?_, isOpen_integerPeriodize U hU,
    integerPeriodize_onePeriodic U, (volume_integerPeriodize_le U hU.measurableSet).trans hμU⟩
  intro x hx
  have hper : Function.Periodic (fun y : ℝ => y ∈ R) 1 := fun y => propext (hR y)
  have hmem : x - (⌊x⌋ : ℝ) ∈ R := by
    have heq := hper.sub_int_mul_eq (x := x) ⌊x⌋
    simpa using heq.mpr hx
  have hfrac : x - (⌊x⌋ : ℝ) ∈ Icc (0 : ℝ) 1 := by
    constructor
    · exact sub_nonneg.mpr (Int.floor_le x)
    · have h := Int.lt_floor_add_one x
      linarith
  apply mem_iUnion.2
  refine ⟨-⌊x⌋, ?_⟩
  simpa only [mem_preimage, Int.cast_neg, ← sub_eq_add_neg] using hRU ⟨hmem, hfrac⟩

end Problem310.Aux

end

end OAI

-- ---- platform node ----
open OAI OAI.Problem310 OAI.Problem310.Aux
open Set MeasureTheory


theorem solution : type_of% @_root_.OAI.Problem310.Aux.exists_open_periodic_envelope := @_root_.OAI.Problem310.Aux.exists_open_periodic_envelope
