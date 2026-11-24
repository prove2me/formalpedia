-- Prove2me | solution 1 for GlobalTheory.SgLoc.Top.isCompact_mul_integer
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T21:01:11.239553+00:00
-- url     : https://prove2.me/submissions/7ff60919-a1df-4822-b02b-d4655faa79f6

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_RowRawRange
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_T2SpaceOfIsNonarchimedeanLocalFieldFlagMeasures
import Theorems.Thm_GlobalTheory_SgLoc_Top_localField_isCompact_integer

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ValuativeRel MeasureTheory Formalism.MainNotions.S.Loc
open GlobalTheory GlobalTheory.SgLoc GlobalTheory.SgLoc.Top
variable (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
variable {F}
namespace GlobalTheory.SgLoc.Top
theorem _root_.solution (c : F) : IsCompact ((fun x => c * x) '' (𝒪[F] : Set F)) := (localField_isCompact_integer F).image (continuous_const.mul continuous_id)
end GlobalTheory.SgLoc.Top
