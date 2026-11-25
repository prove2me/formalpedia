-- Prove2me | solution 1 for GlobalTheory.PDiv.CocycleSum.mul_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T02:17:12.69232+00:00
-- url     : https://prove2.me/submissions/f98ab40f-9313-4536-bf95-800f72ec2eee

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_RigOfOmegaInjectiveOfEqZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_BialgebraPullbackTwoConvMulSymmetricCocycle

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open TensorProduct Coalgebra Bialgebra CategoryTheory WithConv
open GlobalTheory
open GlobalTheory.PDiv
open GlobalTheory.PDiv.CocycleSum
variable {R A X : Type} [CommRing R] [CommRing A] [CommRing X] [Bialgebra R A] [Algebra R X]
namespace GlobalTheory.PDiv.CocycleSum
theorem _root_.solution (x y : WithConv (A →ₐ[R] X)) (a : A) :
    (x * y).ofConv a = val x y (comul a) := by
  rw [val]
  exact AlgHom.convMul_apply x y a
end GlobalTheory.PDiv.CocycleSum
