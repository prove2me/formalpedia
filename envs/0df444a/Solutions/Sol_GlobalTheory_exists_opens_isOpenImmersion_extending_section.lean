-- Prove2me | solution 1 for GlobalTheory.exists_opens_isOpenImmersion_extending_section
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T00:00:15.863082+00:00
-- url     : https://prove2.me/submissions/b55fc6a3-5399-4e80-921a-65d82468d192

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_RigidSys
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_Splits
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GtBaseChangeSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_GeometricallyIntegralIffGeometricallyConnectedOf
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_IsIsoStalkMapOfFlatOfSurjectiveOnStalks
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsIsDominantGeometricPointOfIsPreimmersion
import Theorems.Thm_GlobalTheory_exists_isDominant_geometricPoint_of_isPreimmersion
import Theorems.Thm_GlobalTheory_isOpenImmersion_of_etale_of_mono_pullback_snd
import Theorems.Thm_GlobalTheory_isDominant_pullback_fst_of_isOpenMap
import Theorems.Thm_GlobalTheory_isIso_stalkMap_of_flat_of_surjectiveOnStalks
import Theorems.Thm_GlobalTheory_isNormalScheme_of_smooth


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
theorem _root_.solution : ∀ (X U : Scheme.{0}) [IsLocallyNoetherian X] (j : U ⟶ X), ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme X → IsPreimmersion j → Flat j → IsDominant j → QuasiCompact j → ∀ (Y : Scheme.{0}) (p : Y ⟶ X) (I : Type) [Finite I] (σ : I → (U ⟶ Y)), Etale p → IsSeparated p → (∀ i, σ i ≫ p = j) → (∀ (k : Type) [Field k] [IsAlgClosed k] (u : Sp k ⟶ U) (y : Sp k ⟶ Y), y ≫ p = u ≫ j → ∃ i, y = u ≫ σ i) → ∀ y : Y, ∃ (i : I) (W : Y.Opens), y ∈ W ∧ IsOpenImmersion (W.ι ≫ p) ∧ pullback.fst (W.ι ≫ p) j ≫ W.ι = pullback.snd (W.ι ≫ p) j ≫ σ i := by
  intro X U _ j hN _ _ _ _ Y p I _ σ _ _ hσ hgeo y
  have := IsNormalScheme.of_pred hN
  have := isNormalScheme_of_smooth p
  have : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian p
  let W : Y.Opens :=
    IsNormalScheme.component ⟨_, irreducibleComponent_mem_irreducibleComponents y⟩
  have hy : y ∈ W := mem_irreducibleComponent
  have : IsIntegral W.toScheme := inferInstance
  let q : W.toScheme ⟶ X := W.ι ≫ p
  have := isDominant_pullback_fst_of_isOpenMap j q q.isOpenMap
  have : ∀ z, IsIso ((pullback.fst q j).stalkMap z) :=
    isIso_stalkMap_of_flat_of_surjectiveOnStalks _
  have := IsNormalScheme.of_isIso_stalkMap (pullback.fst q j)
  obtain ⟨k, _, _, t, _⟩ := exists_isDominant_geometricPoint_of_isPreimmersion (pullback.fst q j)
  obtain ⟨i, hi⟩ := hgeo k (t ≫ pullback.snd q j) (t ≫ pullback.fst q j ≫ W.ι)
    (by simp only [Category.assoc]; rw [← pullback.condition])
  have he : pullback.fst q j ≫ W.ι = pullback.snd q j ≫ σ i :=
    ext_of_isDominant_of_isSeparated p
      (by simp only [Category.assoc]; rw [hσ, ← pullback.condition]) t
      (by rw [hi, Category.assoc])
  have : Mono (pullback.snd q j ≫ σ i) := by rw [← he]; infer_instance
  have : Mono (pullback.snd q j) := mono_of_mono _ (σ i)
  exact ⟨i, W, hy, isOpenImmersion_of_etale_of_mono_pullback_snd j q, he⟩
end GlobalTheory
