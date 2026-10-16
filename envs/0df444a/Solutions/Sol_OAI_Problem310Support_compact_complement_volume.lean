-- Prove2me | solution 1 for OAI.Problem310Support.compact_complement_volume
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-16T07:08:53.679927+00:00
-- url     : https://prove2.me/submissions/86a080fd-5481-489f-a5cb-84a080bc5636

-- Generated from openai/math@1581d4c lean/OAI/MeasureTheory/DyadicAvoidance/GlobalFromPeriodic.lean:L11-L34
-- (upload_full_project.md Phase 4): solution for node OAI.Problem310Support.compact_complement_volume. The node keeps its source
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

-- ---- from OAI.MeasureTheory.DyadicAvoidance.GlobalFromPeriodic ----
namespace OAI

noncomputable section

open Set MeasureTheory

namespace Problem310Support

/-- A small open deletion from the unit interval leaves a compact set
whose volume is strictly greater than the requested threshold. -/
theorem compact_complement_volume {C : Set ℝ} (hC : IsOpen C)
    {η : ℝ} (hη : 0 < η) (hη1 : η < 1)
    (hsmall : volume (C ∩ Icc (0 : ℝ) 1) ≤ ENNReal.ofReal (η / 2)) :
    IsCompact (Icc (0 : ℝ) 1 \ C) ∧
      ENNReal.ofReal (1 - η) < volume (Icc (0 : ℝ) 1 \ C) := by
  refine ⟨isCompact_Icc.diff hC, ?_⟩
  have hfinite : volume (C ∩ Icc (0 : ℝ) 1) ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top hsmall
  have hdiff : Icc (0 : ℝ) 1 \ C =
      Icc (0 : ℝ) 1 \ (C ∩ Icc (0 : ℝ) 1) := by
    ext x
    simp only [mem_sdiff, mem_inter_iff]
    tauto
  rw [hdiff, measure_sdiff inter_subset_right
    (hC.measurableSet.inter measurableSet_Icc).nullMeasurableSet hfinite,
    Real.volume_Icc]
  norm_num only [sub_zero, ENNReal.ofReal_one]
  have hstrict : ENNReal.ofReal (1 - η) < ENNReal.ofReal (1 - η / 2) :=
    (ENNReal.ofReal_lt_ofReal_iff (by linarith)).mpr (by linarith)
  refine hstrict.trans_le ?_
  rw [ENNReal.ofReal_sub 1 (by positivity), ENNReal.ofReal_one]
  exact tsub_le_tsub_left hsmall 1

end Problem310Support

end

end OAI

-- ---- platform node ----
open OAI OAI.Problem310Support
open Set MeasureTheory


theorem solution : type_of% @_root_.OAI.Problem310Support.compact_complement_volume := @_root_.OAI.Problem310Support.compact_complement_volume
