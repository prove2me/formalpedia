-- Prove2me | solution 1 for GlobalTheory.exists_finset_isProjOver_descends
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T22:42:43.159893+00:00
-- url     : https://prove2.me/submissions/c9020813-b31f-4adb-a32a-e79b173bcb50

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_TwistingSheafOneChartEqPreimageStandardChart
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsUniqueComapEqVanishingIdeal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsFinsetIsProjOverDescends
import Theorems.Thm_GlobalTheory_ProjSpace_comap_map_baseChange
import Theorems.Thm_GlobalTheory_GaloisDescent_contract_smul
import Theorems.Thm_GlobalTheory_GaloisDescent_mem_rationalPart
import Theorems.Thm_GlobalTheory_GaloisDescent_quotientEquivOfMapEq_tmul
import Theorems.Thm_GlobalTheory_GaloisDescent_rationalPart_baseChange
import Theorems.Thm_GlobalTheory_GaloisDescent_twist_id
import Theorems.Thm_GlobalTheory_ProjSpace_gradedMap_apply
import Theorems.Thm_GlobalTheory_ProjSpace_isAffineOpen_chart
import Theorems.Thm_GlobalTheory_ProjSpace_isPullback_baseChange
import Theorems.Thm_GlobalTheory_QCoh_Qcqs_appLinearBase_apply
import Theorems.Thm_GlobalTheory_QCoh_germLinear_apply
import Theorems.Thm_GlobalTheory_QCoh_resBasicOpen_apply
import Theorems.Thm_GlobalTheory_QCoh_resLinear_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.GaloisDescent.contract_smul
attribute [local simp] GlobalTheory.GaloisDescent.mem_rationalPart
attribute [local simp] GlobalTheory.GaloisDescent.quotientEquivOfMapEq_tmul
attribute [local simp] GlobalTheory.GaloisDescent.rationalPart_baseChange
attribute [local simp] GlobalTheory.GaloisDescent.twist_id
attribute [local simp] GlobalTheory.ProjSpace.gradedMap_apply
attribute [local simp] GlobalTheory.QCoh.Qcqs.appLinearBase_apply
attribute [local simp] GlobalTheory.QCoh.germLinear_apply
attribute [local simp] GlobalTheory.QCoh.resBasicOpen_apply
attribute [local simp] GlobalTheory.QCoh.resLinear_apply



set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
attribute [local instance] MvPolynomial.gradedAlgebra
open GlobalTheory
open ProjSpace
namespace GlobalTheory
theorem _root_.solution : ∀ (K : Type) [Field K] (K₀ : Subfield K) (X : Scheme.{0}) (p : X ⟶ Sp K), IsProjOver p → ∃ s : Finset K, ∀ K₁ : Subfield K, K₀ ≤ K₁ → (s : Set K) ⊆ K₁ → ∃ (X₁ : Scheme.{0}) (p₁ : X₁ ⟶ Sp K₁) (φ : X ⟶ X₁), IsProjOver p₁ ∧ IsPullback φ p p₁ (spMap K₁.subtype) := by
  classical
  rintro K _ K₀ X p ⟨N, e, he, rfl⟩
  have hT : ∀ i : Fin (N + 1), ∃ T : Finset (MvPolynomial {j // j ≠ i} K),
      Ideal.span (chartAlgEquiv K N i '' T) = e.ker.ideal ⟨_, isAffineOpen_chart K N i⟩ := fun i => by
    obtain ⟨T, hT⟩ := (IsNoetherian.noetherian
      ((e.ker.ideal ⟨_, isAffineOpen_chart K N i⟩).comap (chartAlgEquiv K N i)))
    refine ⟨T, ?_⟩
    have := congrArg (Ideal.map (chartAlgEquiv K N i)) hT
    rw [Ideal.map_comap_of_surjective _ (chartAlgEquiv K N i).surjective] at this
    rw [← this]
    exact (Ideal.map_span _ _).symm
  choose T hT using hT
  refine ⟨Finset.univ.biUnion fun i => (T i).biUnion MvPolynomial.coeffs, fun K₁ _ hs => ?_⟩
  have key := comap_map_baseChange N K₁.subtype e.ker (fun i => T i) hT fun i t ht => by
    apply MvPolynomial.mem_range_map_iff_coeffs_subset.2
    intro c hc
    refine ⟨⟨c, hs ?_⟩, rfl⟩
    simp only [Finset.coe_biUnion, Set.mem_iUnion]
    exact ⟨i, Finset.mem_univ i, t, ht, hc⟩
  rw [Scheme.IdealSheafData.map_ker] at key
  refine ⟨(e ≫ baseChange N K₁.subtype).image, (e ≫ baseChange N K₁.subtype).imageι ≫ PSpace.str K₁ N,
    (e ≫ baseChange N K₁.subtype).toImage, ⟨N, _, inferInstance, rfl⟩, ?_⟩
  have h := isPullback_of_isClosedImmersion e (e ≫ baseChange N K₁.subtype).imageι
    (e ≫ baseChange N K₁.subtype).toImage (baseChange N K₁.subtype) (by simp)
    (by rw [← key]; congr 1; exact Scheme.IdealSheafData.ker_subschemeι _)
  exact h.flip.paste_vert (isPullback_baseChange N K₁.subtype)
end GlobalTheory
