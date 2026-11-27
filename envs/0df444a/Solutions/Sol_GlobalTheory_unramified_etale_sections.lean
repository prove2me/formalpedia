-- Prove2me | solution 1 for GlobalTheory.unramified_etale_sections
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-27T04:42:46.758719+00:00
-- url     : https://prove2.me/submissions/06099ed7-deef-4088-9288-4439f8bf8b7a

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_BijectiveRestrictPointsOfEtaleOfHenselian
import Theorems.Thm_P2M_GlobalTheory_isOpenImmersion_equalizer___of_unramified_d71f398b7582
import Theorems.Thm_P2M_GlobalTheory_isClosedImmersion_equalizer___of_isSeparated_bdcf708e7a7d
import Theorems.Thm_GlobalTheory_eq_of_connected_of_unramified_of_point
import Theorems.Thm_GlobalTheory_isOpenImmersion_and_isClosedImmersion_of_section_of_etale
import Theorems.Thm_GlobalTheory_existsUnique_lift_of_etale
import Theorems.Thm_GlobalTheory_bijective_restrictPoints_of_etale_of_henselian

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
theorem _root_.solution :
    (∀ {X S T : Scheme.{u}} (f : X ⟶ S) [FormallyUnramified f] [LocallyOfFiniteType f]
      [IsSeparated f] (a b : T ⟶ X), a ≫ f = b ≫ f →
        IsOpenImmersion (equalizer.ι a b) ∧ IsClosedImmersion (equalizer.ι a b)) ∧
    (∀ {X S T : Scheme.{u}} (f : X ⟶ S) [FormallyUnramified f] [LocallyOfFiniteType f]
      [IsSeparated f] [ConnectedSpace T] (a b : T ⟶ X), a ≫ f = b ≫ f →
        ∀ (k : Type u) [Field k] (j : Spec (.of k) ⟶ T), j ≫ a = j ≫ b → a = b) ∧
    (∀ {X S : Scheme.{u}} (f : X ⟶ S) [Etale f] [IsSeparated f] (s : S ⟶ X), s ≫ f = 𝟙 S →
        IsOpenImmersion s ∧ IsClosedImmersion s) ∧
    (∀ {X S T₀ T : Scheme.{u}} (f : X ⟶ S) [Etale f] (i : T₀ ⟶ T) [IsClosedImmersion i],
      IsNilpotent i.ker → ∀ (g : T₀ ⟶ X) (h : T ⟶ S), g ≫ f = i ≫ h →
        ∃! l : T ⟶ X, i ≫ l = g ∧ l ≫ f = h) ∧
    (∀ (R : Type u) [CommRing R] [HenselianLocalRing R] {X : Scheme.{u}} (f : X ⟶ Spec (.of R))
      [Etale f], Function.Bijective (restrictPoints f (𝟙 _)
        (Spec.map (CommRingCat.ofHom (IsLocalRing.residue R))))) :=
  ⟨fun f _ _ _ _ _ hab ↦ ⟨isOpenImmersion_equalizer_ι_of_unramified f hab,
      isClosedImmersion_equalizer_ι_of_isSeparated f hab⟩,
    fun f _ _ _ _ _ _ hab _ _ j hj ↦ eq_of_connected_of_unramified_of_point f hab j hj,
    fun f _ _ s hs ↦ isOpenImmersion_and_isClosedImmersion_of_section_of_etale f s hs,
    fun f _ i _ hi g h w ↦ existsUnique_lift_of_etale f i hi g h w,
    fun R _ _ _ f _ ↦ bijective_restrictPoints_of_etale_of_henselian f R _⟩
end GlobalTheory
