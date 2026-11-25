-- Prove2me | solution 1 for GlobalTheory.T.additiveFunctions_flatBaseChange_bijective
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T05:53:08.361806+00:00
-- url     : https://prove2.me/submissions/e59a9227-66b3-43d0-b61e-784e5650aa9f

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_AdditiveFunctionsFlatBaseChangeBijective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_RigOfOmegaInjectiveOfEqZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_AdditiveFunctionsFlatBaseChangeBijectiveStatement
import Theorems.Thm_GlobalTheory_PDiv_liftSemi_prim_baseChange_bijective


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
theorem _root_.solution : ∀ {R A : Type} (R' : Type) [CommRing R] [CommRing A] [Bialgebra R A] [CommRing R'] [Algebra R R'] [Module.Flat R R'], Function.Bijective (liftSemi (toBaseChange R R' A).prim) := by
  first | exact @GlobalTheory.PDiv.liftSemi_prim_baseChange_bijective | exact GlobalTheory.PDiv.liftSemi_prim_baseChange_bijective | (intros; apply GlobalTheory.PDiv.liftSemi_prim_baseChange_bijective <;> assumption)
end _root_.GlobalTheory.T
