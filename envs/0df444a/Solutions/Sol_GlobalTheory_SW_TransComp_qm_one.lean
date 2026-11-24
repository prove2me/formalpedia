-- Prove2me | solution 1 for GlobalTheory.SW.TransComp.qm_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T20:29:39.217316+00:00
-- url     : https://prove2.me/submissions/2d0df398-10ab-4206-90bc-bf3f088855e0

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
theorem _root_.solution {α : Type} [DecidableEq α] : qm (1 : Matrix α α ℚ) = 1 := by
  ext i j
  by_cases hij : i = j <;> simp [qm, Matrix.one_apply, hij]
end GlobalTheory.SW.TransComp
