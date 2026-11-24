-- Prove2me | solution 1 for GroundTheory.Arith.Etale.bijective_pullbackSection_of_isIso
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T23:45:38.827363+00:00
-- url     : https://prove2.me/submissions/d5159cd3-bd32-4d34-bc6e-020f31387c17

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
theorem _root_.solution {T U : Scheme.{u}} (g : T ⟶ U) [IsIso g] (N : U.Modules) :
    Function.Bijective (pullbackSection g N) := by
  have h := Adjunction.unit_leftAdjointUniq_hom_app (Scheme.Modules.restrictAdjunction g)
    (Scheme.Modules.pullbackPushforwardAdjunction g) N
  have hU : (⊤ : U.Opens) ≤ g ''ᵁ (g ⁻¹ᵁ (⊤ : U.Opens)) := by
    simp [Scheme.Hom.opensRange_of_isIso]
  have h1 : IsIso (((Scheme.Modules.restrictAdjunction g).unit.app N).app ⊤) := by
    rw [Scheme.Modules.restrictAdjunction_unit_app_app]
    have : IsIso (homOfLE (g.image_preimage_le (⊤ : U.Opens))).op :=
      ⟨(homOfLE hU).op, Subsingleton.elim _ _, Subsingleton.elim _ _⟩
    exact Functor.map_isIso N.presheaf _
  have h2 : IsIso (((Scheme.Modules.pullbackPushforwardAdjunction g).unit.app N).app ⊤) := by
    rw [← h, Scheme.Modules.Hom.comp_app]
    have : IsIso (((Scheme.Modules.pushforward g).map
        (((Scheme.Modules.restrictAdjunction g).leftAdjointUniq
          (Scheme.Modules.pullbackPushforwardAdjunction g)).hom.app N)).app ⊤) :=
      inferInstanceAs (IsIso (Scheme.Modules.Hom.app _ _))
    infer_instance
  exact ConcreteCategory.bijective_of_isIso
    (((Scheme.Modules.pullbackPushforwardAdjunction g).unit.app N).app ⊤)
end GroundTheory.Arith.Etale
