-- Prove2me | solution 1 for GlobalTheory.SgLoc.idemPairHom_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T18:13:41.360747+00:00
-- url     : https://prove2.me/submissions/3a0852e4-e681-4e9d-b028-e78ce85f63c3

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
theorem _root_.solution {F E : Type} [Field F] [CommRing E] [Algebra F E] (p q : E)
    (h1 : p + q = 1) (h0 : p * q = 0) (y : F × F) :
    idemPairHom p q h1 h0 y = y.1 • p + y.2 • q := rfl
end GlobalTheory.SgLoc
