-- Prove2me | solution 1 for GlobalTheory.SgLoc.Top.t2Space_of_isNonarchimedeanLocalField_flag_measures
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T20:47:03.593891+00:00
-- url     : https://prove2.me/submissions/7cf98fec-5de0-4ac0-bcc7-eb46d35fd19e

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_RowRawRange
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_T2SpaceOfIsNonarchimedeanLocalFieldFlagMeasures
import Theorems.Thm_Formalism_MainNotions_S_Loc_Pt_cast_blocks
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.MainNotions.S.Loc.Pt.cast_blocks



set_option autoImplicit false
open ValuativeRel MeasureTheory Formalism.MainNotions.S.Loc
open GlobalTheory GlobalTheory.SgLoc GlobalTheory.SgLoc.Top
variable (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
namespace GlobalTheory.SgLoc.Top
theorem _root_.solution : T2Space F := by
  refine IsTopologicalAddGroup.t2Space_of_zero_sep fun x hx => ?_
  refine ⟨{y | valuation F y < valuation F x},
    (IsValuativeTopology.hasBasis_nhds_zero' F).mem_of_mem (by simpa using hx), ?_⟩
  exact lt_irrefl (valuation F x)
end GlobalTheory.SgLoc.Top
