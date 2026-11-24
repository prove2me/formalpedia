-- Prove2me | solution 1 for GlobalTheory.ProperFunctions.isIso_appTop_of_isAffine
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T21:13:42.702358+00:00
-- url     : https://prove2.me/submissions/463bdf53-1bba-47ba-8136-5e527b9c6e3c

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_IsIsoAppTopOfIsPullbackOfSurjective
import Theorems.Thm_GlobalTheory_ProperFunctions_isIso_appTop_of_isPullback_of_surjective
import Theorems.Thm_GlobalTheory_ProperFunctions_isIso_appTop_of_section

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits AlgebraicGeometry TensorProduct Opposite
universe u
open GlobalTheory
open GlobalTheory.ProperFunctions
variable {X Y S T : Scheme.{u}}
namespace GlobalTheory.ProperFunctions
theorem _root_.solution (p : X ⟶ S) [IsAffine S] [IsLocallyNoetherian S] [Flat p]
    [UniversallyClosed p] [LocallyOfFiniteType p] [GeometricallyIntegral p] :
    IsIso p.appTop := by
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace p
  have := HasRingHomProperty.instIsZariskiLocalAtSource (P := @Etale)
  have : MorphismProperty.ContainsIdentities @Etale.{u} := ⟨fun _ ↦ inferInstance⟩
  obtain ⟨T, i, _, hi, _⟩ := X.exists_hom_isAffine_of_isZariskiLocalAtSource @Etale
  have : IsLocallyNoetherian T := LocallyOfFiniteType.isLocallyNoetherian (i ≫ p)
  have := isIso_appTop_of_section (pullback.snd p (i ≫ p)) (e := pullback.lift i (𝟙 T) (by simp))
    (pullback.lift_snd _ _ _)
  exact isIso_appTop_of_isPullback_of_surjective (.of_hasPullback p (i ≫ p))
end GlobalTheory.ProperFunctions
