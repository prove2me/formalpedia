-- Prove2me | solution 1 for GlobalTheory.existsUnique_lift_of_etale_of_surjective
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-27T04:38:02.955397+00:00
-- url     : https://prove2.me/submissions/210f7cb8-318f-406e-b45f-c86e873ecc98

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_BijectiveRestrictPointsOfEtaleOfHenselian
import Theorems.Thm_GlobalTheory_existsUnique_lift_of_etale
import Theorems.Thm_GlobalTheory_isNilpotent_ker_specMap

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace
universe u
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution {X S : Scheme.{u}} (f : X ⟶ S) [Etale f]
    {R R₀ : CommRingCat.{u}} (π : R ⟶ R₀) (hπ : Function.Surjective π)
    (hπ' : IsNilpotent (RingHom.ker π.hom))
    (g : Spec R₀ ⟶ X) (h : Spec R ⟶ S) (w : g ≫ f = Spec.map π ≫ h) :
    ∃! l : Spec R ⟶ X, Spec.map π ≫ l = g ∧ l ≫ f = h :=
  have := IsClosedImmersion.spec_of_surjective π hπ
  existsUnique_lift_of_etale f _ (isNilpotent_ker_specMap π hπ') g h w
end GlobalTheory
