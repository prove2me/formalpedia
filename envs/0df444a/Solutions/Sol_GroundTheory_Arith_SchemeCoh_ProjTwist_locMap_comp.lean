-- Prove2me | solution 1 for GroundTheory.Arith.SchemeCoh.ProjTwist.locMap_comp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T23:45:41.348657+00:00
-- url     : https://prove2.me/submissions/9f572c50-0a11-4a11-a3d3-1fec5ba18358

import Mathlib
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_ProjTwist
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_ProjTwistAway
import Theorems.Thm_GroundTheory_Arith_SchemeCoh_ProjTwist_locMap_algebraMap
import Theorems.Thm_GroundTheory_Arith_SchemeCoh_ProjTwist_ext
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
open GroundTheory GroundTheory.Arith GroundTheory.Arith.SchemeCoh
open AlgebraicGeometry TopologicalSpace CategoryTheory Opposite
universe u
variable {A σ : Type u} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
variable {𝒜 : ℕ → σ} [GradedRing 𝒜]
noncomputable section
open GroundTheory.Arith.SchemeCoh.ProjTwist
namespace GroundTheory.Arith.SchemeCoh.ProjTwist
theorem _root_.solution {f f' : A} (φ : Localization.Away f →+* Localization.Away f')
    (hφ : φ.comp (algebraMap A _) = algebraMap A _) (x : ProjectiveSpectrum 𝒜)
    (hx : f' ∉ x.asHomogeneousIdeal) (hx' : f ∉ x.asHomogeneousIdeal) (z : Localization.Away f) :
    locMap x hx (φ z) = locMap x hx' z := by
  have : (locMap x hx).comp φ = locMap x hx' := by
    apply IsLocalization.ringHom_ext (Submonoid.powers f)
    ext a
    simp only [RingHom.comp_apply]
    rw [← RingHom.comp_apply φ, hφ, locMap_algebraMap, locMap_algebraMap]
  exact congrArg (fun F => F z) this
end GroundTheory.Arith.SchemeCoh.ProjTwist
