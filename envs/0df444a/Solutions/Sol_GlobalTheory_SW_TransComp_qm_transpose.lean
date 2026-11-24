-- Prove2me | solution 1 for GlobalTheory.SW.TransComp.qm_transpose
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T20:32:55.665961+00:00
-- url     : https://prove2.me/submissions/be3b7084-2dcd-4fb5-8d9c-e6178658c864

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_IMemSiegel
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_SymplecticSiegelActionMemUpperHalfSpaceAndCocyclStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_SiegelThetaTransformationLawMul

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Complex GlobalTheory.SW
open scoped ComplexConjugate Real
open GlobalTheory GlobalTheory.SW GlobalTheory.SW.TransComp
namespace GlobalTheory.SW.TransComp
theorem _root_.solution {α β : Type} (A : Matrix α β ℚ) : qm Aᵀ = (qm A)ᵀ := rfl
end GlobalTheory.SW.TransComp
