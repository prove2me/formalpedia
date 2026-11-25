-- Prove2me | solution 1 for GroundTheory.Arith.SchemeCoh.ProjHom.toSpecAway_SpecMap
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T05:53:04.672429+00:00
-- url     : https://prove2.me/submissions/a68f632a-2a4f-4dfc-89b3-25d8cd607ace

import Mathlib
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_ProjectiveCohomology_TwistingSheaf
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_ProperCohomology_ProjHom
import Theorems.Thm_GroundTheory_Arith_SchemeCoh_ProjTwist_val_add
import Theorems.Thm_GroundTheory_Arith_SchemeCoh_ProjTwist_val_mkSection
import Theorems.Thm_GroundTheory_Arith_SchemeCoh_ProjTwist_val_neg
import Theorems.Thm_GroundTheory_Arith_SchemeCoh_ProjTwist_val_sub
import Theorems.Thm_GroundTheory_Arith_SchemeCoh_ProjTwist_val_zero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GroundTheory.Arith.SchemeCoh.ProjTwist.val_add
attribute [local simp] GroundTheory.Arith.SchemeCoh.ProjTwist.val_mkSection
attribute [local simp] GroundTheory.Arith.SchemeCoh.ProjTwist.val_neg
attribute [local simp] GroundTheory.Arith.SchemeCoh.ProjTwist.val_sub
attribute [local simp] GroundTheory.Arith.SchemeCoh.ProjTwist.val_zero



set_option autoImplicit false
set_option maxSynthPendingDepth 1
open AlgebraicGeometry CategoryTheory Limits Opposite HomogeneousLocalization
open GroundTheory GroundTheory.Arith GroundTheory.Arith.SchemeCoh
universe u
noncomputable section
variable {σ : Type*} {A : Type u} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
  (𝒜 : ℕ → σ) [GradedRing 𝒜]
open GroundTheory.Arith.SchemeCoh.ProjHom
variable {X : Scheme.{u}}
namespace GroundTheory.Arith.SchemeCoh.ProjHom
theorem _root_.solution (x : Γ(X, ⊤)) :
    toSpecAway x ≫ Spec.map (CommRingCat.ofHom (algebraMap Γ(X, ⊤) (Localization.Away x))) =
      (X.basicOpen x).ι ≫ X.toSpecΓ := by
  simp only [toSpecAway, Category.assoc, basicOpenIsoSpecAway_hom_SpecMap]
  have h1 := morphismRestrict_ι X.toSpecΓ (PrimeSpectrum.basicOpen x)
  calc _ = (X.isoOfEq (X.toSpecΓ_preimage_basicOpen x)).inv ≫
        (X.toSpecΓ ⁻¹ᵁ PrimeSpectrum.basicOpen x).ι ≫ X.toSpecΓ := by
          congr 1
    _ = _ := Scheme.isoOfEq_inv_ι_assoc _ _ _
end GroundTheory.Arith.SchemeCoh.ProjHom
