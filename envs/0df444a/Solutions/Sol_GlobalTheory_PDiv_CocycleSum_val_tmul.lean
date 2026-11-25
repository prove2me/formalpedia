-- Prove2me | solution 1 for GlobalTheory.PDiv.CocycleSum.val_tmul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T01:47:29.924254+00:00
-- url     : https://prove2.me/submissions/2a8445c5-0287-4c2e-898d-a1209774b37d

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
theorem _root_.solution (x y : WithConv (A →ₐ[R] X)) (a b : A) :
    val x y (a ⊗ₜ b) = x.ofConv a * y.ofConv b := rfl
end GlobalTheory.PDiv.CocycleSum
