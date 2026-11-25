-- Prove2me | solution 1 for GlobalTheory.T.primitive_semilinearLift_baseChange_bijective
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T07:03:15.183748+00:00
-- url     : https://prove2.me/submissions/0979dff8-eede-46d6-8fed-413873a2483a

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_PrimitiveSemilinearLiftBaseChangeBijective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_RigOfOmegaInjectiveOfEqZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_PrimitiveSemilinearLiftBaseChangeBijectiveStatement
import Theorems.Thm_GlobalTheory_PDiv_liftSemi_prim_toBaseChange_bijective


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
theorem _root_.solution : ∀ {R A : Type} (R' : Type) [CommRing R] [CommRing A] [Bialgebra R A] [Module.Finite R A] [Module.Projective R A] [IsCocomm R A] [CommRing R'] [Algebra R R'], Module.Projective R (Cot R (CartierDual R A)) → Function.Bijective (liftSemi (toBaseChange R R' A).prim) := by
  first | exact @GlobalTheory.PDiv.liftSemi_prim_toBaseChange_bijective | exact GlobalTheory.PDiv.liftSemi_prim_toBaseChange_bijective | (intros; apply GlobalTheory.PDiv.liftSemi_prim_toBaseChange_bijective <;> assumption)
end _root_.GlobalTheory.T
