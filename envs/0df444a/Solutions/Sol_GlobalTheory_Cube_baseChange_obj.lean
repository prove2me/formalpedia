-- Prove2me | solution 1 for GlobalTheory.Cube.baseChange_obj
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T17:38:31.26393+00:00
-- url     : https://prove2.me/submissions/b18f6242-7dd0-4c04-8266-887ed1320568

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
theorem _root_.solution (A : Cube.{v} ι R) (s : Finset ι) :
    (Cube.baseChange S A).obj s = ModuleCat.of S (S ⊗[R] A.obj s) := rfl
end Cube
end GlobalTheory
