-- Prove2me | solution 1 for GroundTheory.Arith.Etale.bijective_map_of_isIso_counit
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T23:45:38.071101+00:00
-- url     : https://prove2.me/submissions/83b7873d-a425-43cb-a24f-e83e0db67075

import Mathlib
import Definitions.Def_GroundTheory_ArithmeticGeometry_EtaleCompletion_ModulesPullback
import Definitions.Def_GroundTheory_ArithmeticGeometry_EtaleCompletion_PullbackAffine

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Arith GroundTheory.Arith.Etale
open CategoryTheory Limits Opposite AlgebraicGeometry
universe u
namespace GroundTheory.Arith.Etale
theorem _root_.solution {C D : Type*} [Category C] [Category D] {F : C ⥤ D} {G : D ⥤ C}
    (adj : F ⊣ G) (X Y : D) [IsIso (adj.counit.app X)] :
    Function.Bijective (fun h : X ⟶ Y => G.map h) := by
  have : (fun h : X ⟶ Y => G.map h) =
      (adj.homEquiv (G.obj X) Y) ∘ (fun h => adj.counit.app X ≫ h) := by
    funext h
    simp [Adjunction.homEquiv_unit]
  rw [this]
  exact (adj.homEquiv _ _).bijective.comp
    ⟨fun a b h => (cancel_epi _).mp h,
      fun b => ⟨inv (adj.counit.app X) ≫ b, by simp⟩⟩
end GroundTheory.Arith.Etale
