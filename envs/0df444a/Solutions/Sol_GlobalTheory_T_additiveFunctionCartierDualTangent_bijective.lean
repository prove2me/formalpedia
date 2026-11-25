-- Prove2me | solution 1 for GlobalTheory.T.additiveFunctionCartierDualTangent_bijective
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T04:09:51.700527+00:00
-- url     : https://prove2.me/submissions/1105a218-18a4-45e5-9031-8ed03de78bdf

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_AdditiveFunctionCartierDualTangentBijective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_RigOfOmegaInjectiveOfEqZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_AdditiveFunctionCartierDualTangentBijectiveStatement
import Theorems.Thm_GlobalTheory_PDiv_primTangent_bijective


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open TensorProduct Coalgebra Bialgebra CategoryTheory WithConv GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ {R A : Type} [CommRing R] [CommRing A] [Bialgebra R A] [Module.Finite R A] [Module.Projective R A] [IsCocomm R A], Function.Bijective (primTangent R A) := by
  first | exact @GlobalTheory.PDiv.primTangent_bijective | exact GlobalTheory.PDiv.primTangent_bijective | (intros; apply GlobalTheory.PDiv.primTangent_bijective <;> assumption)
end _root_.GlobalTheory.T
