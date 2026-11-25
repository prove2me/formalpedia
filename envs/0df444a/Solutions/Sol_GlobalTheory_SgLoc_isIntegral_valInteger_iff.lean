-- Prove2me | solution 1 for GlobalTheory.SgLoc.isIntegral_valInteger_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T07:54:33.117953+00:00
-- url     : https://prove2.me/submissions/bf10c70a-44f8-4d4c-a04f-96b36d43beed

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_RowRawRange
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_IsIntegralValIntegerIff

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ValuativeRel MeasureTheory ComplexConjugate Formalism.MainNotions.S.Loc GlobalTheory.SgLoc
open scoped ComplexOrder
open GlobalTheory GlobalTheory.SgLoc
namespace GlobalTheory.SgLoc
theorem _root_.solution {F : Type} [Field F] [ValuativeRel F] (a : F) :
    IsIntegral 𝒪[F] a ↔ a ∈ 𝒪[F] :=
  ⟨fun h => (Valuation.integer.integers (valuation F)).mem_of_integral h,
    fun h => isIntegral_algebraMap (R := 𝒪[F]) (A := F) (x := ⟨a, h⟩)⟩
end GlobalTheory.SgLoc
