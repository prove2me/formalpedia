-- Prove2me | solution 1 for GlobalTheory.laurentEval_single
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T23:43:48.938794+00:00
-- url     : https://prove2.me/submissions/da128648-3967-4a17-b875-282ad970659d

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_FiniteOfIsClosedTorusZariskiOfPowEqOne
import Theorems.Thm_GlobalTheory_torusCoord_symm_apply

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
theorem _root_.solution (u : ι → Rˣ) (x : ι →₀ ℤ) (a : R) :
    laurentEval u (single x a) = a * ((x.prod fun i m => u i ^ m : Rˣ) : R) := by
  rw [laurentEval, torusEval_single, torusCoord_symm_apply]
  rfl
end GlobalTheory
