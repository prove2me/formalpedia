-- Prove2me | solution 1 for GlobalTheory.Cube.termBaseChangeEquiv_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T17:40:38.227653+00:00
-- url     : https://prove2.me/submissions/f9e4514f-6ff9-4396-8b4f-8a13ec783e25

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
theorem _root_.solution [Finite ι] (A : Cube.{v} ι R) (p : ℕ)
    (x : S ⊗[R] Cube.Term A p) :
    Cube.termBaseChangeEquiv S A p x = Cube.termBaseChange S A p x := rfl
end Cube
end GlobalTheory
