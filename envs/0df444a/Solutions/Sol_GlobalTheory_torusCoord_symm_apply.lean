-- Prove2me | solution 1 for GlobalTheory.torusCoord_symm_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T23:37:48.036876+00:00
-- url     : https://prove2.me/submissions/f20fa624-13dc-42c9-a7fb-0050c603af5a

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
variable {R : Type*} [CommRing R] {X : Type*} [AddCommGroup X] {ι : Type*}
namespace GlobalTheory
theorem _root_.solution (b : Module.Basis ι ℤ X) (u : ι → Rˣ) (x : X) :
    (torusCoord R b).symm u (Multiplicative.ofAdd x) = (b.repr x).prod fun i m => u i ^ m := by
  change Additive.toMul ((b.constr ℤ fun i => Additive.ofMul (u i)) x) = _
  rw [Module.Basis.constr_apply, Finsupp.sum, Finsupp.prod, toMul_sum]
  rfl
end GlobalTheory
