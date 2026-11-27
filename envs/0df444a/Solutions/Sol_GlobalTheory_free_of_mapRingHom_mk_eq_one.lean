-- Prove2me | solution 1 for GlobalTheory.free_of_mapRingHom_mk_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-27T04:38:14.761723+00:00
-- url     : https://prove2.me/submissions/b646ea2a-0e8f-40a5-9d6d-03905f6b09c4

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_UniqueFactorizationMonoidAddMonoidAlgebraOfFree

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped TensorProduct AlgebraMonoidAlgebra
open AddMonoidAlgebra CommRing
open GlobalTheory
variable (A X : Type*) [CommRing A] [IsDomain A] [IsIntegrallyClosed A]
variable [AddCommGroup X] [Module.Free ℤ X]
variable {X} (N : Type*) [AddCommGroup N] [Module (AddMonoidAlgebra A X) N]
  [Module.Invertible (AddMonoidAlgebra A X) N]
namespace GlobalTheory
theorem _root_.solution (ε : AddMonoidAlgebra A X →ₐ[A] A)
    (h : Pic.mapRingHom (ε : AddMonoidAlgebra A X →+* A) (Pic.mk _ N) = 1) :
    Module.Free (AddMonoidAlgebra A X) N := by
  obtain ⟨M, hM⟩ := (pic_mapAlgebra_groupAlgebra_bijective A X).2 (Pic.mk _ N)
  rw [← hM, ← Pic.mapRingHom_algebraMap, Pic.mapRingHom_mapRingHom, ε.comp_algebraMap,
    Pic.mapRingHom_algebraMap, Pic.mapAlgebra_self_apply] at h
  rw [← Pic.mk_eq_one_iff_free, ← hM, h, map_one]
end GlobalTheory
