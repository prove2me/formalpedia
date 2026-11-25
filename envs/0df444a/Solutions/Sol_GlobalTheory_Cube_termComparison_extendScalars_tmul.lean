-- Prove2me | solution 1 for GlobalTheory.Cube.termComparison_extendScalars_tmul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T17:39:10.09007+00:00
-- url     : https://prove2.me/submissions/3f9e0aac-a189-417a-a71a-38c199430b91

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
open ChangeOfRings
namespace GlobalTheory
namespace Cube
theorem _root_.solution {S : Type u'} [CommRing S] (f : R →+* S)
    (A : Cube.{v} ι R) (p : ℕ) (c : S) (x : Cube.Term A p) (s : {s : Finset ι // s.card = p}) :
    (Cube.termComparison (ModuleCat.extendScalars f) A p).hom (c ⊗ₜ[R,f] x) s =
      c ⊗ₜ[R,f] x s := rfl
end Cube
end GlobalTheory
