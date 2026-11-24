-- Prove2me | solution 1 for GlobalTheory.TangentCrit.locallyOfFinitePresentation_of_comp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T21:27:45.294783+00:00
-- url     : https://prove2.me/submissions/1149bbfe-4a22-4cd3-ba90-1897368bbee5

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsLieBasis
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_FormallyUnramifiedOfTangentMapInjective

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open TensorProduct
noncomputable section
open GlobalTheory GlobalTheory.TangentCrit
open AlgebraicGeometry CategoryTheory Limits
universe u
namespace GlobalTheory.TangentCrit
theorem _root_.solution {X Y S : Scheme.{u}} (f : X ⟶ Y) (π : Y ⟶ S)
    [LocallyOfFinitePresentation (f ≫ π)] [LocallyOfFiniteType π] :
    LocallyOfFinitePresentation f := by
  rw [HasRingHomProperty.iff_exists_appLE (P := @LocallyOfFinitePresentation)
    (RingHom.finitePresentation_stableUnderComposition.stableUnderCompositionWithLocalizationAway
      RingHom.finitePresentation_holdsForLocalizationAway).1]
  intro x
  obtain ⟨_, ⟨W, hW, rfl⟩, hxW, -⟩ :=
    S.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ (π (f x))) isOpen_univ
  obtain ⟨_, ⟨U, hU, rfl⟩, hxU, hUW : U ≤ π ⁻¹ᵁ W⟩ :=
    Y.isBasis_affineOpens.exists_subset_of_mem_open hxW (π ⁻¹ᵁ W).isOpen
  obtain ⟨_, ⟨V, hV, rfl⟩, hxV, hVU : V ≤ f ⁻¹ᵁ U⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open hxU (f ⁻¹ᵁ U).isOpen
  refine ⟨⟨U, hU⟩, ⟨V, hV⟩, hxV, hVU, RingHom.FinitePresentation.of_comp_finiteType
    (π.appLE W U hUW).hom ?_ (π.finiteType_appLE hW hU hUW)⟩
  rw [← CommRingCat.hom_comp, Scheme.Hom.appLE_comp_appLE]
  exact (f ≫ π).finitePresentation_appLE hW hV _
end GlobalTheory.TangentCrit
