-- Prove2me | solution 1 for GlobalTheory.ZM.IsGaloisCover.of_isPullback
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T09:42:31.296646+00:00
-- url     : https://prove2.me/submissions/e1e4cff6-c3b6-4617-8394-eb07250b1dd1

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ModuliSpaces_IsGaloisCover
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_BijectiveRestrictPointsOfEtaleOfHenselian
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_GaloisCoverDescentAndCartesianSquares
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
variable {X' Y' : Scheme.{0}} {π' : X' ⟶ Y'} {ρ' : Ga → (X' ⟶ X')} {u : X' ⟶ X} {v : Y' ⟶ Y}
namespace GlobalTheory.ZM.IsGaloisCover
theorem _root_.solution (h : IsGaloisCover Ga ρ π) (hp : IsPullback u π' π v) (hu : ∀ a, ρ' a ≫ u = u ≫ ρ a)
    (hπ : ∀ a, ρ' a ≫ π' = π') : IsGaloisCover Ga ρ' π' where
  finite := h.finite
  one := by
    apply hp.hom_ext
    · rw [hu 1, h.one, Category.id_comp, Category.comp_id]
    · rw [hπ 1, Category.id_comp]
  mul := by
    intro a c
    apply hp.hom_ext
    · rw [hu, h.mul, Category.assoc, hu c, reassoc_of% (hu a)]
    · rw [hπ, Category.assoc, hπ c, hπ a]
  inv := hπ
  fin := by
    have := h.fin
    exact MorphismProperty.of_isPullback hp h.fin
  etale := by
    have := h.etale
    exact MorphismProperty.of_isPullback hp h.etale
  onto := by
    have := h.onto
    exact MorphismProperty.of_isPullback hp h.onto
  fibre := by
    intro K _ _ y y' hy
    have hyu : (y ≫ u) ≫ π = (y' ≫ u) ≫ π := by
      simp only [Category.assoc, hp.w]
      simp only [← Category.assoc, hy]
    obtain ⟨a, ha, hauniq⟩ := h.fibre K (y ≫ u) (y' ≫ u) hyu
    refine ⟨a, ?_, ?_⟩
    · apply hp.hom_ext
      · rw [Category.assoc, hu, ← Category.assoc, ha]
      · rw [Category.assoc, hπ, hy]
    · intro b hb
      apply hauniq
      rw [Category.assoc, ← hu, ← Category.assoc, hb]
end GlobalTheory.ZM.IsGaloisCover
