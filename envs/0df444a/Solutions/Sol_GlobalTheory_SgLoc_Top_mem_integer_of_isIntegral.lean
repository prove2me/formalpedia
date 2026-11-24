-- Prove2me | solution 1 for GlobalTheory.SgLoc.Top.mem_integer_of_isIntegral
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T20:47:02.634824+00:00
-- url     : https://prove2.me/submissions/077cdb65-224c-4872-af7b-52c8fb3176f1

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_RowRawRange
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_T2SpaceOfIsNonarchimedeanLocalFieldFlagMeasures

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
omit [TopologicalSpace F] [IsNonarchimedeanLocalField F]
namespace GlobalTheory.SgLoc.Top
theorem _root_.solution {a : F} (h : IsIntegral 𝒪[F] a) : a ∈ 𝒪[F] := (Valuation.integer.integers (valuation F)).mem_of_integral h
end GlobalTheory.SgLoc.Top
