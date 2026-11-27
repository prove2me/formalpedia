-- Prove2me | solution 1 for GlobalTheory.exists_desc_of_isFinite_of_densePart
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-27T04:37:10.988904+00:00
-- url     : https://prove2.me/submissions/eb06ee04-55ca-42b2-81b8-77c2a3eff92f

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_RigidSys
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_Splits
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GtBaseChangeSt
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ModuliSpaces_AuxiliaryInertOddPrime
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ShimuraVarieties_FlatImageOfOverFractionFieldOfValuationRing
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsUniqueLiftOfDensePart
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsDescOfIsFiniteOfDensePart
import Theorems.Thm_GlobalTheory_isFinite_graphClosure_fst_of_isFinite
import Theorems.Thm_GlobalTheory_existsUnique_lift_of_densePart
import Theorems.Thm_GlobalTheory_isIso_stalkMap_of_flat_of_surjectiveOnStalks


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
open GlobalTheory.Models
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution : ∀ (S X X' U U' Y : Scheme.{0}) [IsLocallyNoetherian X'] (π : X ⟶ X') (j : U ⟶ X) (j' : U' ⟶ X') (r : U ⟶ U') (s' : X' ⟶ S) (p : Y ⟶ S) (f : X ⟶ Y) (f₀ : U' ⟶ Y), ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme X' → IsReduced X → IsFinite π → Surjective π → Surjective r → IsDominant j → QuasiCompact j → IsPreimmersion j' → Flat j' → IsDominant j' → QuasiCompact j' → IsSeparated p → LocallyOfFiniteType p → j ≫ π = r ≫ j' → j ≫ f = r ≫ f₀ → f ≫ p = π ≫ s' → f₀ ≫ p = j' ≫ s' → ∃ f' : X' ⟶ Y, j' ≫ f' = f₀ ∧ π ≫ f' = f := by
  intro S X X' U U' Y _ π j j' r s' p f f₀ hX' _ _ _ _ _ _ _ _ _ _ _ _ h₁ h₂ h₃ h₄
  have := GlobalTheory.IsNormalScheme.of_pred hX'
  have := isIso_stalkMap_of_flat_of_surjectiveOnStalks j'
  have : GlobalTheory.IsNormalScheme U' := GlobalTheory.IsNormalScheme.of_isIso_stalkMap j'
  have := IsSchemeTheoreticallyDominant.of_isDominant r
  have := isFinite_graphClosure_fst_of_isFinite π s' p f h₃.symm
  let g := graphClosure.lift s' p π f h₃.symm j' f₀ h₄.symm r j h₁.symm h₂.symm
  have hg₁ : g ≫ graphClosure.fst s' p π f h₃.symm = j' := graphClosure.lift_fst ..
  have hg₂ : g ≫ graphClosure.snd s' p π f h₃.symm = f₀ := graphClosure.lift_snd ..
  obtain ⟨σ, ⟨hσ₁, hσ₂⟩, -⟩ := existsUnique_lift_of_densePart X' U' X' _ j' hX' ‹_› ‹_› ‹_› ‹_›
    (graphClosure.fst s' p π f h₃.symm) (𝟙 X') g inferInstance (by rw [hg₁, Category.comp_id])
  have h₅ : j' ≫ σ ≫ graphClosure.snd s' p π f h₃.symm = f₀ := by rw [reassoc_of% hσ₁, hg₂]
  refine ⟨σ ≫ graphClosure.snd s' p π f h₃.symm, h₅,
    ext_of_isDominant_of_isSeparated p ?_ j ?_⟩
  · rw [Category.assoc, Category.assoc, ← graphClosure.condition, reassoc_of% hσ₂, h₃]
  · rw [reassoc_of% h₁, h₅, h₂]
end GlobalTheory
