-- Prove2me | solution 1 for GlobalTheory.SW.TransComp.qm_sub
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T20:29:40.031937+00:00
-- url     : https://prove2.me/submissions/78766f00-19f8-4c8b-a5a0-a41dbd59d35a

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
theorem _root_.solution {α β : Type} (A B : Matrix α β ℚ) : qm (A - B) = qm A - qm B := by
  ext i j
  simp [qm]
end GlobalTheory.SW.TransComp
