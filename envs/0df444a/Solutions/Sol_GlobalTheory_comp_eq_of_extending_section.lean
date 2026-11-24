-- Prove2me | solution 1 for GlobalTheory.comp_eq_of_extending_section
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T22:31:58.98125+00:00
-- url     : https://prove2.me/submissions/9ca0df3d-11bf-47fe-90ba-cee30b7ab076

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_RigidSys
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_Splits
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GtBaseChangeSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_FormallyUnramifiedOfTangentMapInjective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsIsDominantGeometricPointOfIsPreimmersion
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_TorsionPointFixedOfGenericSectionsFixed
import Theorems.Thm_GlobalTheory_isDominant_pullback_fst_of_isOpenMap


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
theorem _root_.solution {X U W G T : Scheme.{0}} [IsReduced X] (j : U ⟶ X)
    [IsDominant j] (g : G ⟶ X) [IsSeparated g] (a : W ⟶ G) [IsOpenImmersion (a ≫ g)]
    (s : U ⟶ G) (hs : pullback.fst (a ≫ g) j ≫ a = pullback.snd (a ≫ g) j ≫ s)
    (r : X ⟶ X) (r₀ : U ⟶ U) (φ : G ⟶ G) (hr : r₀ ≫ j = j ≫ r) (hφ : φ ≫ g = g ≫ r)
    (hsφ : s ≫ φ = r₀ ≫ s) (w : T ⟶ W) (hw : w ≫ (a ≫ g) ≫ r = w ≫ a ≫ g) :
    w ≫ a ≫ φ = w ≫ a := by
  have key : ∀ {V : Scheme.{0}} (v : V ⟶ W) (u : V ⟶ U), v ≫ a ≫ g = u ≫ j → v ≫ a = u ≫ s := by
    intro V v u h
    have := congrArg (pullback.lift v u h ≫ ·) hs
    simpa only [pullback.lift_fst_assoc, pullback.lift_snd_assoc] using this
  let f₁ := pullback.fst (a ≫ g) ((a ≫ g) ≫ r)
  let f₂ := pullback.snd (a ≫ g) ((a ≫ g) ≫ r)
  have hc : f₁ ≫ a ≫ g = f₂ ≫ (a ≫ g) ≫ r := pullback.condition
  let t := f₂ ≫ a ≫ g
  have : IsOpenImmersion t := inferInstance
  have : IsReduced (pullback (a ≫ g) ((a ≫ g) ≫ r)) := isReduced_of_isOpenImmersion t
  have := isDominant_pullback_fst_of_isOpenMap j t t.isOpenEmbedding.isOpenMap
  have hd : pullback.fst t j ≫ f₂ ≫ a ≫ g = pullback.snd t j ≫ j := pullback.condition
  have he : f₂ ≫ a ≫ φ = f₁ ≫ a := by
    refine ext_of_isDominant_of_isSeparated g ?_ (pullback.fst t j) ?_
    · simp only [Category.assoc, hφ, hc]
    · have h₁ := key (pullback.fst t j ≫ f₂) (pullback.snd t j) ((Category.assoc _ _ _).trans hd)
      have h₂ := key (pullback.fst t j ≫ f₁) (pullback.snd t j ≫ r₀) (by
        simp only [Category.assoc, hc, hr, reassoc_of% hd])
      simp only [Category.assoc] at h₁ h₂
      rw [h₂, reassoc_of% h₁, hsφ]
  have := congrArg (pullback.lift w w hw.symm ≫ ·) he
  simpa only [f₁, f₂, pullback.lift_fst_assoc, pullback.lift_snd_assoc] using this
end GlobalTheory
