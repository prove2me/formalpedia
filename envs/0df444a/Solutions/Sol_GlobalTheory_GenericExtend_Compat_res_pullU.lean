-- Prove2me | solution 1 for GlobalTheory.GenericExtend.Compat.res_pullU
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T01:21:32.206308+00:00
-- url     : https://prove2.me/submissions/c5f94d45-beb3-47a9-b8ce-8084871812cb

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_RigidSys
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_Splits
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GtBaseChangeSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_ExistsUniqueLbIsoPullEqOfCoheightLeOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_IsDiscreteValuationRingStalkGeneric
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_GeometricallyIntegralIffGeometricallyConnectedOf
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_IsIsoStalkMapOfFlatOfSurjectiveOnStalks
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsLineBundleGeneratorExtendingDensePart
import Theorems.Thm_GlobalTheory_GenericExtend_gm_res_pullU
import Theorems.Thm_P2M_GlobalTheory_normal_domain_height_one__5612c3bf64ed
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_gm_pull
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_gm_res
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_unit_ext


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
open TopologicalSpace Opposite
set_option backward.isDefEq.respectTransparency false
open GlobalTheory GlobalTheory.GenericExtend
namespace GlobalTheory.GenericExtend
namespace Compat
theorem _root_.solution {Q Y H Z : Scheme.{0}} {N : LB Y} {J : Q ⟶ Y}
    {τ : ∀ a, Γ(Q, J ⁻¹ᵁ N.U a)ˣ} (hτ : Compat N J τ) {φ : H ⟶ Y} {k : Z ⟶ H} {ψ : Z ⟶ Q}
    (hψ : ψ ≫ J = k ≫ φ) (hW : ∀ A : Y.Opens, k ⁻¹ᵁ φ ⁻¹ᵁ A ≤ ψ ⁻¹ᵁ J ⁻¹ᵁ A) (a b : N.ι) :
    res (inf_le_left : k ⁻¹ᵁ φ ⁻¹ᵁ N.U a ⊓ k ⁻¹ᵁ φ ⁻¹ᵁ N.U b ≤ _)
      (res (hW _) (pullU ψ _ (τ a))) =
      res (le_rfl : k ⁻¹ᵁ φ ⁻¹ᵁ N.U a ⊓ k ⁻¹ᵁ φ ⁻¹ᵁ N.U b ≤ k ⁻¹ᵁ φ ⁻¹ᵁ (N.U a ⊓ N.U b))
        (pullU k _ (pullU φ _ (N.g a b))) *
        res (inf_le_right : k ⁻¹ᵁ φ ⁻¹ᵁ N.U a ⊓ k ⁻¹ᵁ φ ⁻¹ᵁ N.U b ≤ _)
          (res (hW _) (pullU ψ _ (τ b))) := by
  refine unit_ext fun z hz ↦ ?_
  rw [map_mul, gm_res _ z inf_le_left hz, gm_res _ z inf_le_right hz,
    gm_res_pullU (𝟙 Z) ψ z (hW _) hz.1,
    gm_res_pullU (𝟙 Z) ψ z (hW _) hz.2, hτ _ (𝟙 Z ≫ ψ) z a b (hW _ hz.1) (hW _ hz.2)]
  have h₁ := gm_res_pullU (𝟙 Z) k z (le_rfl : k ⁻¹ᵁ φ ⁻¹ᵁ N.U a ⊓ k ⁻¹ᵁ φ ⁻¹ᵁ N.U b ≤
    k ⁻¹ᵁ φ ⁻¹ᵁ (N.U a ⊓ N.U b)) hz (pullU φ _ (N.g a b))
  rw [gm_pull (𝟙 Z ≫ k) φ z (N.U a ⊓ N.U b) hz, Category.assoc, ← hψ, ← Category.assoc] at h₁
  exact congrArg (· * _) h₁.symm
end Compat
end GlobalTheory.GenericExtend
