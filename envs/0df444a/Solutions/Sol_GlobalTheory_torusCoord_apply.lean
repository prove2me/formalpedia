-- Prove2me | solution 1 for GlobalTheory.torusCoord_apply
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:49:46.514796+00:00
-- url     : https://prove2.me/submissions/a31dd247-d07f-434e-b388-2843041d885c

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
theorem _root_.solution (b : Module.Basis ι ℤ X) (t : Multiplicative X →* Rˣ) (i : ι) :
    torusCoord R b t i = t (Multiplicative.ofAdd (b i)) := rfl
end GlobalTheory
