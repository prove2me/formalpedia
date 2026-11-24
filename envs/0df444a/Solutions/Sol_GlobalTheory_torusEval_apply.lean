-- Prove2me | solution 1 for GlobalTheory.torusEval_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T23:37:31.066452+00:00
-- url     : https://prove2.me/submissions/0be64092-efe6-409c-bcef-42369067daa6

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_FiniteOfIsClosedTorusZariskiOfPowEqOne

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Topology
open GlobalTheory
open AddMonoidAlgebra
variable {R : Type*} [CommRing R] {X : Type*} [AddCommGroup X]
namespace GlobalTheory
theorem _root_.solution (t : Multiplicative X →* Rˣ) (f : AddMonoidAlgebra R X) :
    torusEval t f = f.coeff.sum fun x a => a * t (Multiplicative.ofAdd x) := by
  simp [torusEval, lift_apply]
end GlobalTheory
