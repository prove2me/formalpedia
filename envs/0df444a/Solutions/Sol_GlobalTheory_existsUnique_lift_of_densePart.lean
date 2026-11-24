-- Prove2me | solution 1 for GlobalTheory.existsUnique_lift_of_densePart
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T23:23:41.838814+00:00
-- url     : https://prove2.me/submissions/b713d259-bf45-4c40-83d8-fe36e954bffe

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_RigidSys
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_Splits
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GtBaseChangeSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsUniqueLiftSpecOfIsLocalizationAway
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_IsIsoStalkMapOfFlatOfSurjectiveOnStalks
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsUniqueLiftOfDensePart
import Theorems.Thm_GlobalTheory_isIntegral_of_densePart
import Theorems.Thm_GlobalTheory_existsUnique_lift_of_birational
import Theorems.Thm_GlobalTheory_isIso_stalkMap_of_flat_of_surjectiveOnStalks
import Theorems.Thm_GlobalTheory_lift_unique_of_isDominant


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution : ∀ (T U X Y : Scheme.{0}) [IsLocallyNoetherian T] (j : U ⟶ T), ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme T → IsPreimmersion j → Flat j → IsDominant j → QuasiCompact j → ∀ (q : Y ⟶ X) (f : T ⟶ X) (g : U ⟶ Y), IsIntegralHom q → g ≫ q = j ≫ f → ∃! h : T ⟶ Y, j ≫ h = g ∧ h ≫ q = f := by
  intro T U Y Z _ j hT _ _ _ _ p b a _ h
  have := GlobalTheory.IsNormalScheme.of_pred hT
  have H (W : irreducibleComponents T) := by
    have : IsDominant (j ∣_ GlobalTheory.IsNormalScheme.component W) :=
      IsZariskiLocalAtTarget.restrict (P := @IsDominant) ‹IsDominant j› _
    have : IsIntegral (j ⁻¹ᵁ GlobalTheory.IsNormalScheme.component W).toScheme :=
      isIntegral_of_densePart (j ∣_ GlobalTheory.IsNormalScheme.component W)
    have := isIso_stalkMap_of_flat_of_surjectiveOnStalks (j ∣_ GlobalTheory.IsNormalScheme.component W)
    exact existsUnique_lift_of_birational (j ∣_ GlobalTheory.IsNormalScheme.component W) p
      ((j ⁻¹ᵁ GlobalTheory.IsNormalScheme.component W).ι ≫ a) ((GlobalTheory.IsNormalScheme.component W).ι ≫ b)
      (by rw [Category.assoc, h, morphismRestrict_ι_assoc])
  choose c hc _ using H
  obtain ⟨hT⟩ := GlobalTheory.IsNormalScheme.nonempty_isColimit_component T
  let c₀ : T ⟶ Z := Cofan.IsColimit.desc hT c
  have hc₀ (W) : (GlobalTheory.IsNormalScheme.component W).ι ≫ c₀ = c W := Cofan.IsColimit.fac hT c W
  have h₂ : c₀ ≫ p = b := Cofan.IsColimit.hom_ext hT _ _ fun W ↦ by
    change (GlobalTheory.IsNormalScheme.component W).ι ≫ _ = (GlobalTheory.IsNormalScheme.component W).ι ≫ _
    rw [reassoc_of% hc₀ W, (hc W).2]
  have h₁ : j ≫ c₀ = a := by
    refine Scheme.Cover.hom_ext (U.openCoverOfIsOpenCover _
      (.comap (GlobalTheory.IsNormalScheme.iSup_component T) j.base.1)) _ _ fun W ↦ ?_
    change (j ⁻¹ᵁ GlobalTheory.IsNormalScheme.component W).ι ≫ _ =
      (j ⁻¹ᵁ GlobalTheory.IsNormalScheme.component W).ι ≫ _
    rw [← morphismRestrict_ι_assoc, hc₀ W, (hc W).1]
  exact ⟨c₀, ⟨h₁, h₂⟩, fun c' hc' ↦
    lift_unique_of_isDominant j p (hc'.1.trans h₁.symm) (hc'.2.trans h₂.symm)⟩
end GlobalTheory
