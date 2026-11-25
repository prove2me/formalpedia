-- Prove2me | solution 1 for GlobalTheory.LieLoc.exists_standardSmooth_chart
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T14:47:24.056518+00:00
-- url     : https://prove2.me/submissions/44b905fa-3fb9-4817-9f12-5db39e30ba11

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_FlagBasis
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_SabComp
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_EigLatBasis
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsLieBasisBaseChange
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_Biextensions_CubicalExtendsSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_SpanEqTopOfForallMaximal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_UnivChartOfStandardSmooth
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_symm


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.LieLoc
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.Obj TensorProduct
open ReciprocityTheory.ChartRestriction.G.Chart
variable {R : Type} [CommRing R]
namespace GlobalTheory.LieLoc
theorem _root_.solution (X : Over (Spec (CommRingCat.of R))) (n : ℕ)
    (h : SmoothOfRelativeDimension n X.hom) (x : X.left) :
    ∃ (S : Type) (_ : CommRing S) (_ : Algebra R S) (j : sp (R₀ := R) S ⟶ X),
      Algebra.IsStandardSmoothOfRelativeDimension n R S ∧ IsOpenImmersion j.left ∧
        x ∈ Set.range j.left := by
  obtain ⟨B, j₀, hj₀, ⟨q, hq⟩, -⟩ := Scheme.exists_affine_mem_range_and_range_subset
    (X := X.left) (x := x) (U := ⊤) trivial
  letI : Algebra R B := (Spec.preimage (j₀ ≫ X.hom)).hom.toAlgebra
  let j : sp (R₀ := R) B ⟶ X := Over.homMk j₀ (Spec.map_preimage (j₀ ≫ X.hom)).symm
  have h1 : SmoothOfRelativeDimension n (Spec.map (CommRingCat.ofHom (algebraMap R B))) := by
    have e : j₀ ≫ X.hom = Spec.map (CommRingCat.ofHom (algebraMap R B)) := Over.w j
    rw [← e, ← zero_add n]
    infer_instance
  obtain ⟨s, hs, H⟩ := (HasRingHomProperty.Spec_iff (P := @SmoothOfRelativeDimension n)
    (φ := CommRingCat.ofHom (algebraMap R B))).1 h1
  obtain ⟨t, hts, htq⟩ : ∃ t ∈ s, t ∉ (q : PrimeSpectrum B).asIdeal := by
    by_contra! hc
    exact (q : PrimeSpectrum B).2.ne_top (top_le_iff.1 (hs ▸ Ideal.span_le.2 hc))
  have hq' : (q : PrimeSpectrum B) ∈
      Set.range (PrimeSpectrum.comap (algebraMap B (Localization.Away t))) := by
    rw [PrimeSpectrum.localization_away_comap_range (Localization.Away t) t]
    exact htq
  obtain ⟨q', hq'⟩ := hq'
  have Ht := H t hts
  rw [CommRingCat.hom_ofHom, ← IsScalarTower.algebraMap_eq,
    RingHom.isStandardSmoothOfRelativeDimension_algebraMap] at Ht
  refine ⟨Localization.Away t, inferInstance, inferInstance, spMap (SqZero.awayHom R t) ≫ j, Ht, ?_,
    q', ?_⟩
  · change IsOpenImmersion
      (Spec.map (CommRingCat.ofHom (algebraMap B (Localization.Away t))) ≫ j₀)
    infer_instance
  · rw [← hq, ← hq']
    rfl
end GlobalTheory.LieLoc
