-- Prove2me | solution 1 for GlobalTheory.TorusUnit.IsMulLeft.exists_isCharNear
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T22:27:07.738247+00:00
-- url     : https://prove2.me/submissions/75de8e46-81ec-4813-bde4-9486f7653735

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_DegExp
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_WeightedChartPullback_TorusInj
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_PrecompleteBases_Torus2GammaBijective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsUniqueCharacterOfMul
import Theorems.Thm_GlobalTheory_TorusUnit_IsMultiplicative_eq_single
import Theorems.Thm_GlobalTheory_TorusUnit_exists_coeff_notMem
import Theorems.Thm_GlobalTheory_TorusUnit_expand_map
import Theorems.Thm_GlobalTheory_TorusUnit_IsMulLeft_isMultiplicative
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Semi_Rosenlicht_ringHom_ext_ZU
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Semi_Rosenlicht_ringHom_uliftInt_ext


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open scoped CategoryTheory.Obj TensorProduct AlgebraMonoidAlgebra
attribute [local instance] Over.cartesianMonoidalCategory
noncomputable section
open GlobalTheory
open GlobalTheory.TorusUnit
open ReciprocityTheory.ChartRestriction.G.Semi.Rosenlicht (torusFst ringHom_ext_ZU ringHom_uliftInt_ext)
open AddMonoidAlgebra (single)
variable {S : Scheme.{0}} {X : Type} [AddCommGroup X]
variable {Y : Over S}
attribute [local instance] TorusInj.zuAlg
namespace GlobalTheory.TorusUnit
namespace IsMulLeft
theorem _root_.solution {ρ : Γ((splitTorus S X ⊗ Y).left, ⊤)} (hρ : IsMulLeft ρ)
    (hu : IsUnit ρ) (p : Y.left) : ∃ χ, IsCharNear ρ χ p := by
  obtain ⟨R, y, hy, q, hq⟩ : ∃ (R : CommRingCat.{0}) (y : Spec R ⟶ Y.left), IsOpenImmersion y ∧
      p ∈ Set.range y :=
    ⟨_, Y.left.affineOpenCover.f (Y.left.affineOpenCover.idx p), inferInstance,
      Y.left.affineOpenCover.covers p⟩
  obtain ⟨χ, hχ⟩ := exists_coeff_notMem (hu.map (expand y).hom) q.asIdeal q.2.ne_top
  set a := ((expand y).hom ρ).coeff χ with ha
  let g : R ⟶ CommRingCat.of (Localization.Away a) :=
    CommRingCat.ofHom (algebraMap R (Localization.Away a))
  refine ⟨χ, _, Spec.map g ≫ y, inferInstance, ?_, ?_⟩
  · have := PrimeSpectrum.localization_away_comap_range (Localization.Away a) a
    obtain ⟨r, hr⟩ : q ∈ Set.range (PrimeSpectrum.comap (algebraMap R (Localization.Away a))) := by
      rw [this]; exact hχ
    refine ⟨r, ?_⟩
    rw [← hq, ← hr]
    exact Scheme.Hom.comp_apply _ _ _
  · apply (hρ.isMultiplicative _).eq_single
    rw [expand_map, AddMonoidAlgebra.coeff_mapRingHom]
    exact IsLocalization.Away.algebraMap_isUnit a
end IsMulLeft
end GlobalTheory.TorusUnit
