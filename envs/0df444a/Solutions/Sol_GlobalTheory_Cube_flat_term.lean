-- Prove2me | solution 1 for GlobalTheory.Cube.flat_term
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T14:02:44.596417+00:00
-- url     : https://prove2.me/submissions/960848cd-57b3-4aea-9393-f40c0be22646

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
    (h : ∀ s : Finset ι, s.card = p → Module.Flat R (A.obj s)) :
    Module.Flat R (Cube.Term A p) := by
  classical
  haveI := fun s : {s : Finset ι // s.card = p} => h s.1 s.2
  have := Fintype.ofFinite {s : Finset ι // s.card = p}
  exact Module.Flat.of_linearEquiv (DirectSum.linearEquivFunOnFintype R _
    fun s : {s : Finset ι // s.card = p} => A.obj s.1).symm
end Cube
end GlobalTheory
