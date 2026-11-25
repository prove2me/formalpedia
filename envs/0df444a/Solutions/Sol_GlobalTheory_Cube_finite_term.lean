-- Prove2me | solution 1 for GlobalTheory.Cube.finite_term
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T17:39:04.654082+00:00
-- url     : https://prove2.me/submissions/b8fd3ab0-c394-4e61-9844-cd51060600ef

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_IsIsoTermComparisonRestrictScalars

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits
universe v v' u u'
open GlobalTheory
open TensorProduct
variable {ι : Type} {R : Type u} [CommRing R]
variable (S : Type u') [CommRing S] [Algebra R S]
namespace GlobalTheory
namespace Cube
theorem _root_.solution {R : Type u} [Ring R] [Finite ι] (A : Cube.{v} ι R) (p : ℕ)
    (h : ∀ s : Finset ι, s.card = p → Module.Finite R (A.obj s)) :
    Module.Finite R (Cube.Term A p) :=
  haveI := fun s : {s : Finset ι // s.card = p} => h s.1 s.2
  inferInstance
end Cube
end GlobalTheory
