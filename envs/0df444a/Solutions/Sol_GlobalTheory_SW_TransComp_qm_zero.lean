-- Prove2me | solution 1 for GlobalTheory.SW.TransComp.qm_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T20:32:56.444195+00:00
-- url     : https://prove2.me/submissions/f6161f65-a5bd-41e2-ba6c-0e646ebfc8b0

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
theorem _root_.solution {α β : Type} : qm (0 : Matrix α β ℚ) = 0 := by
  ext i j
  simp [qm]
end GlobalTheory.SW.TransComp
