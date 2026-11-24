-- Prove2me | solution 1 for GlobalTheory.ProjSpace.baseChange_appLE_chartAlgEquiv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T21:18:25.086704+00:00
-- url     : https://prove2.me/submissions/f89003e7-1d98-4402-bd6e-b1ba3e063d29

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_TwistingSheafOneChartEqPreimageStandardChart
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsUniqueComapEqVanishingIdeal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsFinsetIsProjOverDescends
import Theorems.Thm_GlobalTheory_GaloisDescent_contract_smul
import Theorems.Thm_GlobalTheory_GaloisDescent_mem_rationalPart
import Theorems.Thm_GlobalTheory_GaloisDescent_quotientEquivOfMapEq_tmul
import Theorems.Thm_GlobalTheory_GaloisDescent_rationalPart_baseChange
import Theorems.Thm_GlobalTheory_GaloisDescent_twist_id
import Theorems.Thm_GlobalTheory_ProjSpace_baseChange_app_formOn
import Theorems.Thm_GlobalTheory_ProjSpace_baseChange_app_ratioOn
import Theorems.Thm_GlobalTheory_ProjSpace_formOn_C
import Theorems.Thm_GlobalTheory_ProjSpace_gradedMap_apply
import Theorems.Thm_GlobalTheory_ProjSpace_resG_formOn
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
open GlobalTheory GlobalTheory.ProjSpace
namespace GlobalTheory.ProjSpace
theorem _root_.solution {R R' : Type} [CommRing R] [CommRing R'] (N : ℕ) (φ : R →+* R')
    (i : Fin (N + 1)) (q : MvPolynomial {j // j ≠ i} R) :
    ((baseChange N φ).appLE (chart R N i) (chart R' N i) (baseChange_preimage_chart N φ i).ge).hom
      (chartAlgEquiv R N i q) = chartAlgEquiv R' N i (MvPolynomial.map φ q) := by
  have h : ((baseChange N φ).appLE (chart R N i) (chart R' N i)
      (baseChange_preimage_chart N φ i).ge).hom.comp (RingHomClass.toRingHom (chartAlgEquiv R N i)) =
      (RingHomClass.toRingHom (chartAlgEquiv R' N i)).comp (MvPolynomial.map φ) := by
    refine MvPolynomial.ringHom_ext (fun r => ?_) (fun j => ?_)
    · simp only [RingHom.comp_apply, RingHom.coe_coe, MvPolynomial.map_C]
      have h1 : chartAlgEquiv R N i (MvPolynomial.C r) = _ := (chartAlgEquiv R N i).commutes r
      have h2 : chartAlgEquiv R' N i (MvPolynomial.C (φ r)) = _ := (chartAlgEquiv R' N i).commutes (φ r)
      rw [h1, h2, ← formOn_C (i := i) (hi := le_rfl), ← formOn_C (i := i) (hi := le_rfl)]
      have h3 := baseChange_app_formOn φ (le_refl (chart R N i)) (MvPolynomial.isHomogeneous_C _ r)
      refine (congrArg (resG _ (baseChange_preimage_chart N φ i).ge) h3).trans ?_
      rw [resG_formOn]
      congr 1
      exact MvPolynomial.map_C _ _
    · simp only [RingHom.comp_apply, RingHom.coe_coe, MvPolynomial.map_X, chartAlgEquiv_X]
      have h3 := baseChange_app_ratioOn φ (le_refl (chart R N i)) j.1
      exact congrArg (resG _ (baseChange_preimage_chart N φ i).ge) h3
  exact congrArg (fun ψ => ψ q) h
end GlobalTheory.ProjSpace
