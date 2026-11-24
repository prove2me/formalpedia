-- Prove2me | solution 1 for GlobalTheory.TameDescent.isPullback_of_isPushout_app
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T21:48:21.386352+00:00
-- url     : https://prove2.me/submissions/41f35725-94f1-4b8c-8e48-772f328cbe4b

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_RigidSys
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_Splits
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GtBaseChangeSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_IsIsoNormalizationPullbackOfToIntegralClosure
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsFinsumSmulEqOneOfTame
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_InvariantTowerAlgebraMapInjectiveStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_FlatOfTameDescent
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_MemMapKerOfOneTmulEqZeroOfFlat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_QuotientIsFiniteLocallyOfFiniteTypeDescendStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_IsPullbackFlatOfTame
import Theorems.Thm_GlobalTheory_TameDescent_isPullback_specMap_app
import Theorems.Thm_GlobalTheory_FreeQuotient_coe_toInvariantsTensor
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.FreeQuotient.coe_toInvariantsTensor



set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory GlobalTheory.TameDescent
namespace GlobalTheory.TameDescent
theorem _root_.solution {X X' Y Y' : Scheme.{0}} (π : X ⟶ X') (φ : Y ⟶ Y')
    (p : Y ⟶ X) (p' : Y' ⟶ X') [IsAffineHom π] [IsAffineHom φ] (w : φ ≫ p' = p ≫ π)
    (H : ∀ (V : X'.Opens) (W : Y'.Opens), IsAffineOpen V → IsAffineOpen W →
      ∀ (e : W ≤ p' ⁻¹ᵁ V) (e' : φ ⁻¹ᵁ W ≤ p ⁻¹ᵁ π ⁻¹ᵁ V),
      IsPushout (p'.appLE V W e) (π.app V) (φ.app W) (p.appLE _ _ e')) :
    IsPullback φ p p' π := by
  have h : ∀ y : Y', ∃ (V : X'.Opens) (W : Y'.Opens), IsAffineOpen V ∧ IsAffineOpen W ∧
      y ∈ W ∧ W ≤ p' ⁻¹ᵁ V := fun y => by
    obtain ⟨_, ⟨V, hV, rfl⟩, hx, -⟩ := X'.isBasis_affineOpens.exists_subset_of_mem_open
      (Set.mem_univ (p' y)) isOpen_univ
    obtain ⟨_, ⟨W, hW, rfl⟩, hy, hle⟩ := Y'.isBasis_affineOpens.exists_subset_of_mem_open
      (show y ∈ p' ⁻¹ᵁ V from hx) (p' ⁻¹ᵁ V).isOpen
    exact ⟨V, W, hV, hW, hy, hle⟩
  choose V W hV hW hy hle using h
  let 𝒰 : Y'.OpenCover := Scheme.Cover.mkOfCovers Y' (fun y => Spec Γ(Y', W y))
    (fun y => (hW y).fromSpec) (fun y => ⟨y, by
      have : y ∈ Set.range (hW y).fromSpec := by
        rw [IsAffineOpen.range_fromSpec]; exact hy y
      exact this⟩)
  refine Scheme.isPullback_of_openCover φ p p' π 𝒰 fun y => ?_
  have e' : φ ⁻¹ᵁ W y ≤ p ⁻¹ᵁ π ⁻¹ᵁ V y := by
    rw [← Scheme.Hom.comp_preimage, ← w, Scheme.Hom.comp_preimage]
    exact φ.preimage_mono (hle y)
  have H1 := isPullback_specMap_app φ (hW y)
  have H2 := (isPullback_SpecMap_of_isPushout _ _ _ _
    (H _ _ (hV y) (hW y) (hle y) e')).paste_vert (isPullback_specMap_app π (hV y)).flip.flip
  rw [IsAffineOpen.SpecMap_appLE_fromSpec p _ ((hW y).preimage φ),
    IsAffineOpen.SpecMap_appLE_fromSpec p' _ (hW y)] at H2
  refine H2.of_iso H1.flip.isoPullback (Iso.refl _) (Iso.refl _) (Iso.refl _) ?_ ?_ ((Category.comp_id _).trans (Category.id_comp _).symm)
    (by simp)
  · exact (Category.comp_id _).trans (H1.flip.isoPullback_hom_snd).symm
  · rw [Iso.refl_hom, Category.comp_id, ← Category.assoc]
    congr 1
    exact (H1.flip.isoPullback_hom_fst).symm
end GlobalTheory.TameDescent
