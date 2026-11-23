-- Prove2me | solution 1 for GlobalTheory.ZM.IsGaloisCover.existsUnique_desc
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T12:36:59.815806+00:00
-- url     : https://prove2.me/submissions/f99e520f-eac8-4e61-a880-2d063afd987c

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ModuliSpaces_IsGaloisCover
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_BijectiveRestrictPointsOfEtaleOfHenselian
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_GaloisCoverDescentAndCartesianSquares
import Theorems.Thm_GlobalTheory_ZM_IsGaloisCover_exists_local_geom
import Theorems.Thm_GlobalTheory_restrictPoints_val
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.restrictPoints_val



set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM
open GlobalTheory GlobalTheory.ZM GlobalTheory.ZM.IsGaloisCover
variable {X Y : Scheme.{0}} {π : X ⟶ Y} {Ga : Type} [Group Ga] {ρ : Ga → (X ⟶ X)}
namespace GlobalTheory.ZM.IsGaloisCover
theorem _root_.solution (h : IsGaloisCover Ga ρ π) {Z : Scheme.{0}} (f : X ⟶ Z) (hf : ∀ a, ρ a ≫ f = f) :
    ∃! f' : Y ⟶ Z, π ≫ f' = f := by
  have := h.fin
  have := h.etale
  have := h.onto
  have key : ∀ {W : Scheme.{0}} (g₁ g₂ : W ⟶ X), g₁ ≫ π = g₂ ≫ π → g₁ ≫ f = g₂ ≫ f := by
    intro W g₁ g₂ hg
    apply Scheme.hom_ext_of_forall
    intro p
    obtain ⟨V, a, hp, hV⟩ := h.exists_local_geom g₁ g₂ hg p
    refine ⟨V, hp, ?_⟩
    calc V.ι ≫ g₁ ≫ f = V.ι ≫ g₁ ≫ ρ a ≫ f := by rw [hf]
      _ = (V.ι ≫ g₁ ≫ ρ a) ≫ f := by simp only [Category.assoc]
      _ = V.ι ≫ g₂ ≫ f := by rw [hV, Category.assoc]
  refine ⟨EffectiveEpi.desc π f key, EffectiveEpi.fac π f key, ?_⟩
  intro f' hf'
  apply (cancel_epi π).1
  rw [hf', EffectiveEpi.fac]
end GlobalTheory.ZM.IsGaloisCover
