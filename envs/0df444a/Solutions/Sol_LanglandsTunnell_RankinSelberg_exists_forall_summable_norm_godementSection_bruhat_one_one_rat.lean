-- Prove2me | solution 1 for LanglandsTunnell.RankinSelberg.exists_forall_summable_norm_godementSection_bruhat_one_one_rat
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.670037+00:00
-- url     : https://prove2.me/submissions/5300f4ab-3c18-5303-8849-7d21cb00cfc3

import Mathlib
import Definitions.Def_LanglandsTunnell_RS22GlobalIntegral
import Definitions.Def_AutomorphicForm_WhittakerCoefficient
import Definitions.Def_NumberField_AdelicBox
import Definitions.Def_NumberField_NormPowChar
import Definitions.Def_AutomorphicForm_InducedSection
import Theorems.Thm_NumberField_TateGlobal_exists_setIntegral_eq_entirePart_add_polarPart_and_fe_of_thetaInversion
import Theorems.Thm_NumberField_TateGlobal_exists_setIntegral_comp_ideleNorm_eq_mul_integral_Ioi_and_setIntegral_ideleNorm_cpow_eq_div
import Theorems.Thm_AutomorphicForm_summable_godementSection_and_bruhatSeries_eq_mul_setIntegral_tsum_of_lintegral_tsum_enorm_lt_top
import Theorems.Thm_MeasureTheory_differentiable_and_continuous_integral_mul_cpow_of_eventually_norm_mul_rpow_add_rpow_neg_le
import Theorems.Thm_AutomorphicForm_isInducedSection_godementSection_of_forall_coe_eq_ideleNorm
import Theorems.Thm_NumberField_AdelicFourier_tsum_apply_smul_vecMul_add_eq_ideleNorm_cpow_neg_two_mul_tsum_reflectPair_of_mem_schwartzBruhat2
import Theorems.Thm_NumberField_AdelicFourier_exists_forall_tsum_norm_apply_smul_vecMul_le_and_continuous_tsum_of_mem_schwartzBruhat2
import Theorems.Thm_NumberField_AdelicFourier_exists_forall_setIntegral_tsum_norm_apply_smul_vecMul_mul_rpow_le_mul_archHeight_pow_of_mem_integralWindowedSiegelSet
import Theorems.Thm_NumberField_AdelicFourier_fourierTransform2_mem_schwartzBruhat2_and_reflectPair_mem_schwartzBruhat2
import Theorems.Thm_NumberField_AdelicFourier_continuous_integrable_comp_vecMul_mem_and_bottomRowVec_mem_schwartzBruhat_of_mem_schwartzBruhat2
import Theorems.Thm_NumberField_TateGlobal_exists_measurableSet_forall_isFundamentalDomain_range_unitsMap_algebraMap
import Theorems.Thm_NumberField_TateGlobal_exists_continuous_monoidHom_ideleNorm_apply_eq
import Theorems.Thm_NumberField_TateGlobal_continuous_ideleNorm
import Theorems.Thm_NumberField_TateGlobal_continuous_ideleNorm_det
import Theorems.Thm_NumberField_AdeleRing_distribHaarChar_algebraMap
import Theorems.Thm_NumberField_AdeleRing_secondCountableTopology_generalLinearGroup_finTwo
import Definitions.Def_AutomorphicForm_ProductionPinsGeneral
import Definitions.Def_LanglandsTunnell_RankinSelbergEuler
import Definitions.Def_AutomorphicForm_GodementSection
import Definitions.Def_LanglandsTunnell_RSCarrier
import Definitions.Def_LanglandsTunnell_RSCarrierSplit
import Definitions.Def_LanglandsTunnell_DeltaLift
import Definitions.Def_AutomorphicForm_SiegelCoordinates
import Definitions.Def_AutomorphicForm_RowIsometryInvariance
import Definitions.Def_NumberField_StandardGlobalAddCharRat
import Definitions.Def_UnramifiedWhittaker_HeckeRecursion
import Definitions.Def_AdelicDock_LocalEmbedding
import Definitions.Def_AutomorphicForm_LocalOrbitalBase
import Definitions.Def_AutomorphicForm_UnipotentQuotient
import Definitions.Def_NumberField_IdeleProductMeasure
import Mathlib.MeasureTheory.Group.FundamentalDomain
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LanglandsTunnell_RankinSelberg_exists_forall_summable_norm_godementSection_bruhat_one_one_rat
p2m_attr_erase "instance" "instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions instCountableOfNumberField_definitions RestrictedProduct.SecondCountableTopology_of_principal instCountableElemSetSetsCofinite_definitions Submodule.instIsTopologicalModuleSubtypeMem Pi.instTopologicalModule IsTopologicalModule.toContinuousSMul IsTopologicalModule.toContinuousAdd instMeasurableSpaceRestrictedProduct_definitions instBorelSpaceRestrictedProduct_definitions MeasureTheory.instMeasurableNegSubtypeMemAddSubgroup_definitions MeasureTheory.instMeasurableMulSubtypeMemSubgroup_definitions MeasureTheory.instMeasurableMul₂SubtypeMemSubgroup_definitions MeasureTheory.instMeasurableMul₂SubtypeMemAddSubgroup_definitions MeasureTheory.instMeasurableAddSubtypeMemAddSubgroup_definitions MeasureTheory.instMeasurableInvSubtypeMemSubgroup_definitions AutomorphicForm.compactSpace_maximalCompactAway AutomorphicForm.compactSpace_adelicMaximalCompact AutomorphicForm.isProbabilityMeasure_maximalCompactHaar AutomorphicForm.isHaarMeasure_maximalCompactHaar AutomorphicForm.compactSpace_maximalCompactAt AutomorphicForm.isProbabilityMeasure_maximalCompactAwayHaar AutomorphicForm.isHaarMeasure_maximalCompactAwayHaar AutomorphicForm.isProbabilityMeasure_maximalCompactAtHaar AutomorphicForm.isHaarMeasure_maximalCompactAtHaar"
p2m_attr_erase "simp" "M4aHerbrand.IdeleGaloisDescent.mk.sizeOf_spec M4aHerbrand.IdeleGaloisDescent.mk.injEq ContinuousAddEquiv.restrictedProductPi_apply RestrictedProduct.flatten_homeomorph_apply RestrictedProduct.flatten_homeomorph'_symm_apply ContinuousMulEquiv.restrictedProductPi_symm_apply RestrictedProduct.flatten_homeomorph'_apply RestrictedProduct.flatten_homeomorph_symm_apply ContinuousMulEquiv.restrictedProductPi_apply ContinuousAddEquiv.restrictedProductPi_symm_apply RingEquiv.restrictedProductCongr_symm_apply RingEquiv.restrictedProductCongrRight_apply MulEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductProd_symm_apply_coe Equiv.restrictedProductCongrRight_apply AddEquiv.restrictedProductCongr_apply Equiv.restrictedProductCongrLeft'_symm_apply_apply Equiv.restrictedProductCongr_apply_apply Equiv.restrictedProductCongrLeft_apply_apply RestrictedProduct.flatten_equiv'_apply AddEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductCongr_symm_apply Equiv.restrictedProductCongrRight_symm_apply RestrictedProduct.flatten_equiv'_symm_apply AddEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductCongrLeft'_apply RestrictedProduct.flatten_apply RingEquiv.restrictedProductCongr_apply_apply RingEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductProd_apply RestrictedProduct.flatten_equiv_apply RestrictedProduct.flatten_equiv_symm_apply LinearEquiv.restrictedProductCongrLeft'_apply RestrictedProduct.not_mem_support RestrictedProduct.mem_structureSubring_iff RestrictedProduct.not_mem_mulSupport RestrictedProduct.support_neg RestrictedProduct.mem_indexSupport_iff RestrictedProduct.mulSupport_inv RestrictedProduct.mapAlongLinearMap_apply"
p2m_attr_erase "simp" "ContinuousAddEquiv.preimage_mulLeft_smul IsModuleTopology.continuousLinearEquiv_apply AlgEquiv.extendScalars_symm_apply IsModuleTopology.Module.Basis.equivFun_homeo_symm_apply IsModuleTopology.Module.Basis.equivFun_homeo_apply IsModuleTopology.continuousAlgEquivOfIsBiscalar_apply AlgEquiv.extendScalars_apply IsModuleTopology.continuousLinearEquiv_symm_apply LocalGL2.coe_localRepSome LocalGL2.coe_diagPi LocalGL2.coe_localRepInf LocalGL2.coe_localRepSome_inv LocalGL2.coe_unipotentInt LocalGL2.coe_weylInt LocalGL2.coe_diagPi_inv LocalGL2.transposeGL_val LocalGL2.transposeGL_one LocalGL2.swapUnit_val"

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicFourier NumberField.AdelicBox NumberField.AdelicLevel
p2m_open "NumberField.TateGlobal AutomorphicForm AutomorphicForm.WindowedSiegel LanglandsTunnell.RankinSelberg P2MW.S_LanglandsTunnell_RankinSelberg_exists_forall_summable_norm_godementSection_bruhat_one_one_rat.LanglandsTunnell.RankinSelberg"
open Set Complex Filter Topology
open scoped NNReal

noncomputable section

namespace LanglandsTunnell
p2m_export "LanglandsTunnell" "ratArchGL2"
namespace RankinSelberg
p2m_export "LanglandsTunnell.RankinSelberg" "moduleChar val_moduleChar_apply moduleChar_pos godementEisenstein godementEisenstein_def IsRapidlyDecreasingOnSiegelSets"
namespace GodementAssembly
p2m_open "LanglandsTunnell.RankinSelberg LanglandsTunnell"

variable {F : Type} [Field F] [NumberField F]

theorem ideleNorm_inv (t : (AdeleRing (𝓞 F) F)ˣ) : ideleNorm F t⁻¹ = (ideleNorm F t)⁻¹ := by
  unfold ideleNorm; rw [map_inv, NNReal.coe_inv]

theorem ideleNorm_ne_zero (t : (AdeleRing (𝓞 F) F)ˣ) : ideleNorm F t ≠ 0 := (ideleNorm_pos t).ne'

theorem ofReal_ideleNorm_ne_zero (t : (AdeleRing (𝓞 F) F)ˣ) : ((ideleNorm F t : ℝ) : ℂ) ≠ 0 :=
  ofReal_ne_zero.mpr (ideleNorm_ne_zero t)

theorem ideleNorm_principal (u : Fˣ) :
    ideleNorm F (Units.map (algebraMap F (AdeleRing (𝓞 F) F) : F →* AdeleRing (𝓞 F) F) u) = 1 := by
  letI : MeasurableSpace (AdeleRing (𝓞 F) F) := borel _
  haveI : BorelSpace (AdeleRing (𝓞 F) F) := ⟨rfl⟩
  have h := NumberField.AdeleRing.distribHaarChar_algebraMap F u
  unfold ideleNorm
  have h' : distribHaarChar (AdeleRing (𝓞 F) F)
      (Units.map (algebraMap F (AdeleRing (𝓞 F) F) : F →* AdeleRing (𝓞 F) F) u) = 1 := h
  rw [h']; rfl

theorem norm_norm_cpow (t : (AdeleRing (𝓞 F) F)ˣ) (w : ℂ) :
    ‖((ideleNorm F t : ℝ) : ℂ) ^ w‖ = (ideleNorm F t) ^ w.re :=
  norm_cpow_eq_rpow_re_of_pos (ideleNorm_pos t) w

theorem continuous_norm_cpow (w : ℂ) :
    Continuous fun t : (AdeleRing (𝓞 F) F)ˣ => ((ideleNorm F t : ℝ) : ℂ) ^ w :=
  (continuous_ofReal.comp (NumberField.TateGlobal.continuous_ideleNorm F)).cpow continuous_const
    fun t => ofReal_mem_slitPlane.mpr (ideleNorm_pos t)

section Chars

variable {χ μ ν : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ}

theorem coe_inv_apply (t : (AdeleRing (𝓞 F) F)ˣ) : ((χ⁻¹ t : ℂˣ) : ℂ) = ((χ t : ℂˣ) : ℂ)⁻¹ := by
  rw [MonoidHom.inv_apply, Units.val_inv_eq_inv_val]

theorem coe_mul_apply (t : (AdeleRing (𝓞 F) F)ˣ) : (((μ * ν) t : ℂˣ) : ℂ) = ((μ t : ℂˣ) : ℂ) * ((ν t : ℂˣ) : ℂ) := by
  rw [MonoidHom.mul_apply, Units.val_mul]

theorem isIdeleClassChar_mul (hμ : IsIdeleClassChar (𝓞 F) F μ) (hν : IsIdeleClassChar (𝓞 F) F ν) :
    IsIdeleClassChar (𝓞 F) F (μ * ν) := fun u => by rw [MonoidHom.mul_apply, hμ u, hν u, one_mul]

theorem isIdeleClassChar_inv (hχ : IsIdeleClassChar (𝓞 F) F χ) : IsIdeleClassChar (𝓞 F) F χ⁻¹ :=
  fun u => by rw [MonoidHom.inv_apply, hχ u, inv_one]

theorem isUnitaryChar_mul (hμ : IsUnitaryChar (𝓞 F) F μ) (hν : IsUnitaryChar (𝓞 F) F ν) :
    IsUnitaryChar (𝓞 F) F (μ * ν) := fun x => by rw [coe_mul_apply, norm_mul, hμ x, hν x, one_mul]

theorem isUnitaryChar_inv (hχ : IsUnitaryChar (𝓞 F) F χ) : IsUnitaryChar (𝓞 F) F χ⁻¹ :=
  fun x => by rw [coe_inv_apply, norm_inv, hχ x, inv_one]

theorem continuous_coe_mul (hμ : Continuous fun x : (AdeleRing (𝓞 F) F)ˣ => ((μ x : ℂˣ) : ℂ))
    (hν : Continuous fun x : (AdeleRing (𝓞 F) F)ˣ => ((ν x : ℂˣ) : ℂ)) :
    Continuous fun x : (AdeleRing (𝓞 F) F)ˣ => (((μ * ν) x : ℂˣ) : ℂ) := by
  simp_rw [coe_mul_apply]; exact hμ.mul hν

theorem continuous_coe_inv (hχ : Continuous fun x : (AdeleRing (𝓞 F) F)ˣ => ((χ x : ℂˣ) : ℂ)) :
    Continuous fun x : (AdeleRing (𝓞 F) F)ˣ => ((χ⁻¹ x : ℂˣ) : ℂ) := by
  have h : (fun x : (AdeleRing (𝓞 F) F)ˣ => ((χ⁻¹ x : ℂˣ) : ℂ)) = fun x => ((χ x⁻¹ : ℂˣ) : ℂ) := by
    funext x; rw [coe_inv_apply, map_inv, Units.val_inv_eq_inv_val]
  rw [h]; exact hχ.comp continuous_inv

theorem coe_swap_inv (t : (AdeleRing (𝓞 F) F)ˣ) :
    (((ν * μ⁻¹) t : ℂˣ) : ℂ) = (((μ * ν⁻¹) t : ℂˣ) : ℂ)⁻¹ := by
  rw [MonoidHom.mul_apply, MonoidHom.mul_apply, Units.val_mul, Units.val_mul, coe_inv_apply, coe_inv_apply,
    mul_inv, inv_inv, mul_comm]

end Chars

theorem centralScalar_coe (z : (AdeleRing (𝓞 F) F)ˣ) :
    ((centralScalar (𝓞 F) F z : AdelicGL2 (𝓞 F) F) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) =
      (z : AdeleRing (𝓞 F) F) • (1 : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) := by
  show ((Units.map (Matrix.scalar (Fin 2)).toMonoidHom z : (Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F))ˣ) :
      Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) = _
  rw [Units.coe_map, RingHom.toMonoidHom_eq_coe, MonoidHom.coe_coe, Matrix.scalar_apply,
    Matrix.smul_one_eq_diagonal]

theorem centralScalar_apply (z : (AdeleRing (𝓞 F) F)ˣ) (i j : Fin 2) :
    ((centralScalar (𝓞 F) F z : AdelicGL2 (𝓞 F) F) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) i j =
      if i = j then (z : AdeleRing (𝓞 F) F) else 0 := by
  rw [centralScalar_coe, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul, mul_ite, mul_one, mul_zero]

theorem centralScalar_mul_coe (z : (AdeleRing (𝓞 F) F)ˣ) (g : AdelicGL2 (𝓞 F) F) :
    ((centralScalar (𝓞 F) F z * g : AdelicGL2 (𝓞 F) F) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) =
      (z : AdeleRing (𝓞 F) F) • (g : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) := by
  rw [Matrix.GeneralLinearGroup.coe_mul, centralScalar_coe, Matrix.smul_mul, Matrix.one_mul]

theorem centralScalar_comm (z : (AdeleRing (𝓞 F) F)ˣ) (g : AdelicGL2 (𝓞 F) F) :
    centralScalar (𝓞 F) F z * g = g * centralScalar (𝓞 F) F z := by
  apply Units.ext
  rw [Matrix.GeneralLinearGroup.coe_mul, Matrix.GeneralLinearGroup.coe_mul, centralScalar_coe, Matrix.smul_mul,
    Matrix.mul_smul, Matrix.one_mul, Matrix.mul_one]

theorem det_centralScalar_mul (z : (AdeleRing (𝓞 F) F)ˣ) (g : AdelicGL2 (𝓞 F) F) :
    Matrix.GeneralLinearGroup.det (centralScalar (𝓞 F) F z * g) = z * z * Matrix.GeneralLinearGroup.det g := by
  apply Units.ext
  rw [map_mul, Units.val_mul, Units.val_mul, Units.val_mul, Matrix.GeneralLinearGroup.val_det_apply,
    Matrix.GeneralLinearGroup.val_det_apply, centralScalar_coe, Matrix.det_smul, Matrix.det_one, mul_one,
    Fintype.card_fin, pow_two]

theorem continuous_centralScalar : Continuous (centralScalar (𝓞 F) F : (AdeleRing (𝓞 F) F)ˣ → AdelicGL2 (𝓞 F) F) := by
  refine Units.continuous_iff.mpr ⟨?_, ?_⟩
  · have h1 : Continuous fun z : (AdeleRing (𝓞 F) F)ˣ =>
        (z : AdeleRing (𝓞 F) F) • (1 : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) :=
      Units.continuous_val.smul continuous_const
    exact h1.congr fun z => (centralScalar_coe z).symm
  · have h1 : Continuous fun z : (AdeleRing (𝓞 F) F)ˣ =>
        ((z⁻¹ : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F) • (1 : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) :=
      (Units.continuous_val.comp continuous_inv).smul continuous_const
    refine h1.congr fun z => ?_
    show _ = ((↑(centralScalar (𝓞 F) F z)⁻¹ : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)))
    rw [← map_inv]
    exact (centralScalar_coe z⁻¹).symm

theorem continuous_det : Continuous (Matrix.GeneralLinearGroup.det : AdelicGL2 (𝓞 F) F → (AdeleRing (𝓞 F) F)ˣ) := by
  refine Units.continuous_iff.mpr ⟨?_, ?_⟩
  · exact (continuous_id.matrix_det).comp Units.continuous_val
  · have : (fun g : AdelicGL2 (𝓞 F) F => ((↑(Matrix.GeneralLinearGroup.det g)⁻¹ : AdeleRing (𝓞 F) F))) =
        fun g : AdelicGL2 (𝓞 F) F => ((g⁻¹ : AdelicGL2 (𝓞 F) F) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)).det := by
      funext g; rw [← map_inv]; rfl
    rw [this]
    exact (continuous_id.matrix_det).comp (Units.continuous_val.comp continuous_inv)

theorem centralScalar_mul_mem_siegel {c u : ℝ} {z : (AdeleRing (𝓞 F) F)ˣ} (hz : ((z : AdeleRing (𝓞 F) F)).2 = 1)
    {h : AdelicGL2 (𝓞 F) F} (hh : h ∈ integralWindowedSiegelSet F c u) :
    centralScalar (𝓞 F) F z * h ∈ integralWindowedSiegelSet F c u := by
  refine scalar_smul_mem_integralWindowedSiegelSet F hz (fun v => ?_) ?_ ?_ ?_ ?_ hh
  · intro h0
    have hzu : IsUnit ((z : AdeleRing (𝓞 F) F).1 v) :=
      (Units.isUnit z).map ((Pi.evalRingHom _ v).comp (RingHom.fst _ _))
    exact not_isUnit_zero (h0 ▸ hzu)
  all_goals simp [centralScalar_apply]

theorem archHeight_centralScalar_mul (z : (AdeleRing (𝓞 F) F)ˣ) (h : AdelicGL2 (𝓞 F) F) :
    archHeight F (glArch (𝓞 F) F (centralScalar (𝓞 F) F z * h)) = archHeight F (glArch (𝓞 F) F h) := by
  rw [map_mul]
  refine archHeight_scalar_entries_mul F (z := (z : AdeleRing (𝓞 F) F).1) (fun v h0 => ?_) ?_ ?_ ?_ ?_ _
  · have hzu : IsUnit ((z : AdeleRing (𝓞 F) F).1 v) :=
      (Units.isUnit z).map ((Pi.evalRingHom _ v).comp (RingHom.fst _ _))
    exact not_isUnit_zero (h0 ▸ hzu)
  all_goals simp [glArch_apply, centralScalar_apply]; try rfl

variable (F) in

def rowOf (ξ : Fin 2 → F) : Fin 2 → AdeleRing (𝓞 F) F := fun i => algebraMap F (AdeleRing (𝓞 F) F) (ξ i)

def theta (Φ : (Fin 2 → AdeleRing (𝓞 F) F) → ℂ) (m : AdelicGL2 (𝓞 F) F) (t : (AdeleRing (𝓞 F) F)ˣ) : ℂ :=
  ∑' ξ : {ξ : Fin 2 → F // ξ ≠ 0},
    Φ ((t : AdeleRing (𝓞 F) F) • Matrix.vecMul (rowOf F ξ.1) (m : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)))

def thetaAbs (Φ : (Fin 2 → AdeleRing (𝓞 F) F) → ℂ) (m : AdelicGL2 (𝓞 F) F) (t : (AdeleRing (𝓞 F) F)ˣ) : ℝ :=
  ∑' ξ : {ξ : Fin 2 → F // ξ ≠ 0},
    ‖Φ ((t : AdeleRing (𝓞 F) F) • Matrix.vecMul (rowOf F ξ.1) (m : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)))‖

def thetaG (Φ : (Fin 2 → AdeleRing (𝓞 F) F) → ℂ) (m : AdelicGL2 (𝓞 F) F) : ℂ :=
  ∑' ξ : {ξ : Fin 2 → F // ξ ≠ 0}, Φ (Matrix.vecMul (rowOf F ξ.1) (m : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)))

theorem rowOf_smul (u : F) (ξ : Fin 2 → F) : rowOf F (u • ξ) = algebraMap F (AdeleRing (𝓞 F) F) u • rowOf F ξ := by
  funext i; simp [rowOf, Pi.smul_apply, smul_eq_mul, map_mul]

theorem smul_vecMul_eq (t : (AdeleRing (𝓞 F) F)ˣ) (v : Fin 2 → AdeleRing (𝓞 F) F) (m : AdelicGL2 (𝓞 F) F) :
    (t : AdeleRing (𝓞 F) F) • Matrix.vecMul v (m : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) =
      Matrix.vecMul v ((centralScalar (𝓞 F) F t * m : AdelicGL2 (𝓞 F) F) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) := by
  rw [centralScalar_mul_coe, Matrix.vecMul_smul]

theorem theta_eq_thetaG (Φ : (Fin 2 → AdeleRing (𝓞 F) F) → ℂ) (m : AdelicGL2 (𝓞 F) F) (t : (AdeleRing (𝓞 F) F)ˣ) :
    theta Φ m t = thetaG Φ (centralScalar (𝓞 F) F t * m) := by
  unfold theta thetaG; simp_rw [smul_vecMul_eq]

def scaleEquiv (u : Fˣ) : {ξ : Fin 2 → F // ξ ≠ 0} ≃ {ξ : Fin 2 → F // ξ ≠ 0} where
  toFun ξ := ⟨(u : F) • ξ.1, smul_ne_zero (Units.ne_zero u) ξ.2⟩
  invFun ξ := ⟨((u⁻¹ : Fˣ) : F) • ξ.1, smul_ne_zero (Units.ne_zero u⁻¹) ξ.2⟩
  left_inv ξ := by
    apply Subtype.ext
    show ((u⁻¹ : Fˣ) : F) • ((u : F) • ξ.1) = ξ.1
    rw [smul_smul, Units.inv_mul, one_smul]
  right_inv ξ := by
    apply Subtype.ext
    show (u : F) • (((u⁻¹ : Fˣ) : F) • ξ.1) = ξ.1
    rw [smul_smul, Units.mul_inv, one_smul]

theorem arg_principal (u : Fˣ) (t : (AdeleRing (𝓞 F) F)ˣ) (ξ : Fin 2 → F)
    (M : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) :
    ((Units.map (algebraMap F (AdeleRing (𝓞 F) F) : F →* AdeleRing (𝓞 F) F) u * t : (AdeleRing (𝓞 F) F)ˣ) :
        AdeleRing (𝓞 F) F) • Matrix.vecMul (rowOf F ξ) M =
      (t : AdeleRing (𝓞 F) F) • Matrix.vecMul (rowOf F ((u : F) • ξ)) M := by
  rw [rowOf_smul, Matrix.smul_vecMul, smul_smul, Units.val_mul, Units.coe_map, MonoidHom.coe_coe, mul_comm]

theorem theta_principal_mul (Φ : (Fin 2 → AdeleRing (𝓞 F) F) → ℂ) (m : AdelicGL2 (𝓞 F) F) (u : Fˣ)
    (t : (AdeleRing (𝓞 F) F)ˣ) :
    theta Φ m (Units.map (algebraMap F (AdeleRing (𝓞 F) F) : F →* AdeleRing (𝓞 F) F) u * t) = theta Φ m t := by
  unfold theta
  conv_rhs => rw [← (scaleEquiv u).tsum_eq]
  refine tsum_congr fun ξ => ?_
  rw [arg_principal]
  rfl

theorem thetaAbs_nonneg (Φ : (Fin 2 → AdeleRing (𝓞 F) F) → ℂ) (m : AdelicGL2 (𝓞 F) F) (t : (AdeleRing (𝓞 F) F)ˣ) :
    0 ≤ thetaAbs Φ m t := tsum_nonneg fun _ => norm_nonneg _

variable (F) in

def normSec : ℝ≥0ˣ →* (AdeleRing (𝓞 F) F)ˣ :=
  (NumberField.TateGlobal.exists_continuous_monoidHom_ideleNorm_apply_eq F).choose

theorem continuous_normSec : Continuous (normSec F) :=
  (NumberField.TateGlobal.exists_continuous_monoidHom_ideleNorm_apply_eq F).choose_spec.1

theorem ideleNorm_normSec (r : ℝ≥0ˣ) : ideleNorm F (normSec F r) = ((r : ℝ≥0) : ℝ) :=
  (NumberField.TateGlobal.exists_continuous_monoidHom_ideleNorm_apply_eq F).choose_spec.2.1 r

theorem normSec_snd (r : ℝ≥0ˣ) : ((normSec F r : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F).2 = 1 :=
  (NumberField.TateGlobal.exists_continuous_monoidHom_ideleNorm_apply_eq F).choose_spec.2.2 r

def rootDet (g : AdelicGL2 (𝓞 F) F) : ℝ≥0ˣ :=
  Units.mk0 ⟨Real.sqrt (ideleNorm F (Matrix.GeneralLinearGroup.det g)), Real.sqrt_nonneg _⟩
    (by
      intro h
      have h' := congrArg (fun x : ℝ≥0 => (x : ℝ)) h
      exact (Real.sqrt_ne_zero'.mpr (ideleNorm_pos _)) h')

theorem coe_rootDet (g : AdelicGL2 (𝓞 F) F) :
    (((rootDet g : ℝ≥0ˣ) : ℝ≥0) : ℝ) = Real.sqrt (ideleNorm F (Matrix.GeneralLinearGroup.det g)) := rfl

def zed (g : AdelicGL2 (𝓞 F) F) : (AdeleRing (𝓞 F) F)ˣ := normSec F (rootDet g)

def gone (g : AdelicGL2 (𝓞 F) F) : AdelicGL2 (𝓞 F) F := centralScalar (𝓞 F) F (zed g)⁻¹ * g

theorem ideleNorm_zed (g : AdelicGL2 (𝓞 F) F) :
    ideleNorm F (zed g) = Real.sqrt (ideleNorm F (Matrix.GeneralLinearGroup.det g)) := by
  rw [zed, ideleNorm_normSec, coe_rootDet]

theorem ideleNorm_zed_mul_self (g : AdelicGL2 (𝓞 F) F) :
    ideleNorm F (zed g) * ideleNorm F (zed g) = ideleNorm F (Matrix.GeneralLinearGroup.det g) := by
  rw [ideleNorm_zed, Real.mul_self_sqrt (ideleNorm_pos _).le]

theorem zed_inv_snd (g : AdelicGL2 (𝓞 F) F) : (((zed g)⁻¹ : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F).2 = 1 := by
  rw [zed, ← map_inv]; exact normSec_snd _

theorem eq_zed_mul_gone (g : AdelicGL2 (𝓞 F) F) : g = centralScalar (𝓞 F) F (zed g) * gone g := by
  rw [gone, ← mul_assoc, ← map_mul, mul_inv_cancel, map_one, one_mul]

theorem det_gone (g : AdelicGL2 (𝓞 F) F) :
    Matrix.GeneralLinearGroup.det (gone g) = (zed g)⁻¹ * (zed g)⁻¹ * Matrix.GeneralLinearGroup.det g := by
  rw [gone, det_centralScalar_mul]

theorem ideleNorm_det_gone (g : AdelicGL2 (𝓞 F) F) : ideleNorm F (Matrix.GeneralLinearGroup.det (gone g)) = 1 := by
  rw [det_gone, ideleNorm_mul, ideleNorm_mul, ideleNorm_inv, ← mul_inv, ideleNorm_zed_mul_self,
    inv_mul_cancel₀ (ideleNorm_ne_zero _)]

theorem continuous_rootDet : Continuous (rootDet : AdelicGL2 (𝓞 F) F → ℝ≥0ˣ) := by
  have hc : Continuous fun g : AdelicGL2 (𝓞 F) F => Real.sqrt (ideleNorm F (Matrix.GeneralLinearGroup.det g)) :=
    Real.continuous_sqrt.comp (NumberField.TateGlobal.continuous_ideleNorm_det F)
  have hne : ∀ g : AdelicGL2 (𝓞 F) F, Real.sqrt (ideleNorm F (Matrix.GeneralLinearGroup.det g)) ≠ 0 := fun g =>
    Real.sqrt_ne_zero'.mpr (ideleNorm_pos _)
  have hc' : Continuous fun g : AdelicGL2 (𝓞 F) F =>
      (⟨Real.sqrt (ideleNorm F (Matrix.GeneralLinearGroup.det g)), Real.sqrt_nonneg _⟩ : ℝ≥0) := hc.subtype_mk _
  have hci : Continuous fun g : AdelicGL2 (𝓞 F) F =>
      (⟨(Real.sqrt (ideleNorm F (Matrix.GeneralLinearGroup.det g)))⁻¹, inv_nonneg.mpr (Real.sqrt_nonneg _)⟩ : ℝ≥0) :=
    (hc.inv₀ hne).subtype_mk _
  refine Units.continuous_iff.mpr ⟨hc', hci.congr fun g => ?_⟩
  show _ = ((↑(rootDet g)⁻¹ : ℝ≥0))
  rw [rootDet, Units.val_inv_eq_inv_val, Units.val_mk0]
  apply NNReal.eq
  rfl

theorem continuous_zed : Continuous (zed : AdelicGL2 (𝓞 F) F → (AdeleRing (𝓞 F) F)ˣ) :=
  continuous_normSec.comp continuous_rootDet

theorem continuous_gone : Continuous (gone : AdelicGL2 (𝓞 F) F → AdelicGL2 (𝓞 F) F) :=
  ((continuous_centralScalar.comp continuous_zed.inv).mul continuous_id)

theorem gone_mul (h t₀ : AdelicGL2 (𝓞 F) F) :
    gone (h * t₀) = (centralScalar (𝓞 F) F (zed (h * t₀))⁻¹ * h) * t₀ := by
  rw [gone, mul_assoc]

variable (F) in

def principalUnits : Subgroup (AdeleRing (𝓞 F) F)ˣ :=
  (Units.map (algebraMap F (AdeleRing (𝓞 F) F) : F →* AdeleRing (𝓞 F) F)).range

scoped instance countable_principalUnits : Countable (principalUnits F) := by
  haveI : Countable F :=
    (Module.Free.chooseBasis ℚ F).equivFun.toEquiv.countable_iff.2 inferInstance
  haveI : Countable Fˣ :=
    Function.Injective.countable (f := (Units.val : Fˣ → F)) Units.val_injective
  exact Function.Surjective.countable (MonoidHom.rangeRestrict_surjective _)

theorem smul_def (γ : principalUnits F) (t : (AdeleRing (𝓞 F) F)ˣ) :
    γ • t = (γ : (AdeleRing (𝓞 F) F)ˣ) * t := rfl

section Idele

variable [MeasurableSpace (AdeleRing (𝓞 F) F)ˣ] [BorelSpace (AdeleRing (𝓞 F) F)ˣ]

theorem measurable_ideleNorm : Measurable (ideleNorm F) :=
  (NumberField.TateGlobal.continuous_ideleNorm F).measurable

theorem measurableSet_le_one : MeasurableSet {t : (AdeleRing (𝓞 F) F)ˣ | ideleNorm F t ≤ 1} :=
  measurableSet_le measurable_ideleNorm measurable_const

theorem measurableSet_one_le : MeasurableSet {t : (AdeleRing (𝓞 F) F)ˣ | 1 ≤ ideleNorm F t} :=
  measurableSet_le measurable_const measurable_ideleNorm

variable (ν : Measure (AdeleRing (𝓞 F) F)ˣ) [ν.IsHaarMeasure] {Ω : Set (AdeleRing (𝓞 F) F)ˣ}

theorem isFundamentalDomain_translate (hΩ : IsFundamentalDomain (principalUnits F) Ω ν) (d : (AdeleRing (𝓞 F) F)ˣ) :
    IsFundamentalDomain (principalUnits F) ((fun u : (AdeleRing (𝓞 F) F)ˣ => u * d) ⁻¹' Ω) ν := by
  refine hΩ.preimage_of_equiv (measurePreserving_mul_right ν d).quasiMeasurePreserving
    (e := fun γ : principalUnits F => γ) Function.bijective_id fun γ t => ?_
  show (γ • t) * d = γ • (t * d)
  rw [smul_def, smul_def, mul_assoc]

theorem measurableEmbedding_mulRight (d : (AdeleRing (𝓞 F) F)ˣ) :
    MeasurableEmbedding (fun u : (AdeleRing (𝓞 F) F)ˣ => u * d) :=
  (MeasurableEquiv.mulRight d).measurableEmbedding

theorem setIntegral_translate (d : (AdeleRing (𝓞 F) F)ˣ) (G : (AdeleRing (𝓞 F) F)ˣ → ℂ) :
    ∫ u in (fun u : (AdeleRing (𝓞 F) F)ˣ => u * d) ⁻¹' Ω, G u ∂ν = ∫ t in Ω, G (t * d⁻¹) ∂ν := by
  have h := (measurePreserving_mul_right ν d).setIntegral_preimage_emb (measurableEmbedding_mulRight d)
    (fun t => G (t * d⁻¹)) Ω
  simp only [mul_inv_cancel_right] at h
  exact h

theorem setIntegral_translate_real (d : (AdeleRing (𝓞 F) F)ˣ) (G : (AdeleRing (𝓞 F) F)ˣ → ℝ) :
    ∫ u in (fun u : (AdeleRing (𝓞 F) F)ˣ => u * d) ⁻¹' Ω, G u ∂ν = ∫ t in Ω, G (t * d⁻¹) ∂ν := by
  have h := (measurePreserving_mul_right ν d).setIntegral_preimage_emb (measurableEmbedding_mulRight d)
    (fun t => G (t * d⁻¹)) Ω
  simp only [mul_inv_cancel_right] at h
  exact h

theorem integrableOn_translate_iff_real (d : (AdeleRing (𝓞 F) F)ˣ) (G : (AdeleRing (𝓞 F) F)ˣ → ℝ) :
    IntegrableOn G ((fun u : (AdeleRing (𝓞 F) F)ˣ => u * d) ⁻¹' Ω) ν ↔
      IntegrableOn (fun t => G (t * d⁻¹)) Ω ν := by
  have h := (measurePreserving_mul_right ν d).integrableOn_comp_preimage (measurableEmbedding_mulRight d)
    (f := fun t => G (t * d⁻¹)) (s := Ω)
  simp only [Function.comp_def, mul_inv_cancel_right] at h
  have h' : IntegrableOn G ((fun u : (AdeleRing (𝓞 F) F)ˣ => u * d) ⁻¹' Ω) ν ↔ IntegrableOn (fun t => G (t * d⁻¹)) Ω ν := h
  exact h'

omit [MeasurableSpace (AdeleRing (𝓞 F) F)ˣ] [BorelSpace (AdeleRing (𝓞 F) F)ˣ] in

theorem translate_inter_upper {d : (AdeleRing (𝓞 F) F)ˣ} (hd : ideleNorm F d = 1) :
    (fun u : (AdeleRing (𝓞 F) F)ˣ => u * d) ⁻¹' (Ω ∩ {t | 1 ≤ ideleNorm F t}) =
      ((fun u : (AdeleRing (𝓞 F) F)ˣ => u * d) ⁻¹' Ω) ∩ {t | 1 ≤ ideleNorm F t} := by
  ext u
  simp only [mem_preimage, mem_inter_iff, mem_setOf_eq, ideleNorm_mul, hd, mul_one]

end Idele

section Bounds

variable [MeasurableSpace (AdeleRing (𝓞 F) F)ˣ] [BorelSpace (AdeleRing (𝓞 F) F)ˣ]
variable (ν : Measure (AdeleRing (𝓞 F) F)ˣ) [ν.IsHaarMeasure] {Ω : Set (AdeleRing (𝓞 F) F)ˣ}

theorem integrableOn_pow_halves (hΩ : IsFundamentalDomain (principalUnits F) Ω ν) {k : ℝ} (hk : 0 < k) :
    IntegrableOn (fun x => ((ideleNorm F x : ℝ) : ℂ) ^ (-(k : ℂ))) (Ω ∩ {t | 1 ≤ ideleNorm F t}) ν ∧
    IntegrableOn (fun x => ((ideleNorm F x : ℝ) : ℂ) ^ (k : ℂ)) (Ω ∩ {t | ideleNorm F t ≤ 1}) ν := by
  obtain ⟨C, -, hC⟩ :=
    NumberField.TateGlobal.exists_setIntegral_comp_ideleNorm_eq_mul_integral_Ioi_and_setIntegral_ideleNorm_cpow_eq_div F ν
  have h := ((hC Ω hΩ).2.1 (k : ℂ) (by rwa [ofReal_re]))
  exact ⟨h.2.2.1, h.1⟩

omit [ν.IsHaarMeasure] in
theorem nullMeasurableSet_upper (hΩ : IsFundamentalDomain (principalUnits F) Ω ν) :
    NullMeasurableSet (Ω ∩ {t | 1 ≤ ideleNorm F t}) ν :=
  hΩ.nullMeasurableSet.inter measurableSet_one_le.nullMeasurableSet

theorem integrableOn_upper_of_le (hΩ : IsFundamentalDomain (principalUnits F) Ω ν)
    {f : (AdeleRing (𝓞 F) F)ˣ → ℂ} (hf : AEStronglyMeasurable f (ν.restrict (Ω ∩ {t | 1 ≤ ideleNorm F t})))
    {C k : ℝ} (hk : 0 < k) (hb : ∀ t, 1 ≤ ideleNorm F t → ‖f t‖ ≤ C * (ideleNorm F t) ^ (-k)) :
    IntegrableOn f (Ω ∩ {t | 1 ≤ ideleNorm F t}) ν := by
  have hint := (integrableOn_pow_halves ν hΩ hk).1
  refine Integrable.mono' (g := fun t => C * ‖((ideleNorm F t : ℝ) : ℂ) ^ (-(k : ℂ))‖) (hint.norm.const_mul C) hf ?_
  refine (ae_restrict_iff'₀ (nullMeasurableSet_upper ν hΩ)).mpr (ae_of_all _ fun t ht => ?_)
  show ‖f t‖ ≤ C * ‖((ideleNorm F t : ℝ) : ℂ) ^ (-(k : ℂ))‖
  rw [norm_norm_cpow, neg_re, ofReal_re]
  exact hb t ht.2

theorem majorant_upper {C x : ℝ} (hC : 0 ≤ C) (hx : 1 ≤ x) (N : ℕ) :
    C * (1 + x⁻¹ ^ 2) * min 1 (x⁻¹ ^ N) ≤ 2 * C * x ^ (-(N : ℝ)) := by
  have hx0 : 0 < x := lt_of_lt_of_le one_pos hx
  have hinv : x⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hx
  have h1 : 1 + x⁻¹ ^ 2 ≤ 2 := by nlinarith [pow_le_one₀ (inv_nonneg.mpr hx0.le) hinv (n := 2)]
  have h2 : min 1 (x⁻¹ ^ N) ≤ x ^ (-(N : ℝ)) := by
    rw [Real.rpow_neg hx0.le, Real.rpow_natCast, ← inv_pow]; exact min_le_right _ _
  have h3 : 0 ≤ min 1 (x⁻¹ ^ N) := le_min zero_le_one (pow_nonneg (inv_nonneg.mpr hx0.le) _)
  calc C * (1 + x⁻¹ ^ 2) * min 1 (x⁻¹ ^ N) ≤ C * 2 * x ^ (-(N : ℝ)) := by
        apply mul_le_mul (mul_le_mul_of_nonneg_left h1 hC) h2 h3 (by positivity)
    _ = 2 * C * x ^ (-(N : ℝ)) := by ring

theorem majorant_lower {C x : ℝ} (hC : 0 ≤ C) (hx0 : 0 < x) (hx : x ≤ 1) (N : ℕ) :
    C * (1 + x⁻¹ ^ 2) * min 1 (x⁻¹ ^ N) ≤ 2 * C * x ^ (-(2 : ℝ)) := by
  have hinv : 1 ≤ x⁻¹ := one_le_inv_iff₀.mpr ⟨hx0, hx⟩
  have hsq : 1 ≤ x⁻¹ ^ 2 := one_le_pow₀ hinv
  have h1 : 1 + x⁻¹ ^ 2 ≤ 2 * x⁻¹ ^ 2 := by linarith
  have h2 : min 1 (x⁻¹ ^ N) ≤ 1 := min_le_left _ _
  have h3 : 0 ≤ min 1 (x⁻¹ ^ N) := le_min zero_le_one (pow_nonneg (inv_nonneg.mpr hx0.le) _)
  have hx2 : x ^ (-(2 : ℝ)) = x⁻¹ ^ 2 := by
    rw [Real.rpow_neg hx0.le, inv_pow]; norm_num
  calc C * (1 + x⁻¹ ^ 2) * min 1 (x⁻¹ ^ N) ≤ C * (2 * x⁻¹ ^ 2) * 1 :=
        mul_le_mul (mul_le_mul_of_nonneg_left h1 hC) h2 h3 (by positivity)
    _ = 2 * C * x ^ (-(2 : ℝ)) := by rw [hx2]; ring

theorem lintegral_thetaAbs_lt_top (hΩ : IsFundamentalDomain (principalUnits F) Ω ν) (hΩm : MeasurableSet Ω)
    {Φ : (Fin 2 → AdeleRing (𝓞 F) F) → ℂ} {m : AdelicGL2 (𝓞 F) F} {C : ℝ} (hC : 0 ≤ C) {N : ℕ} {s : ℂ}
    (hs : 2 < s.re) (hN : s.re < N)
    (hsum : ∀ t : (AdeleRing (𝓞 F) F)ˣ, Summable (fun ξ : Fin 2 → F =>
      ‖Φ ((t : AdeleRing (𝓞 F) F) • Matrix.vecMul (rowOf F ξ) (m : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)))‖))
    (hb : ∀ t : (AdeleRing (𝓞 F) F)ˣ, thetaAbs Φ m t ≤ C * (1 + (ideleNorm F t)⁻¹ ^ 2) * min 1 ((ideleNorm F t)⁻¹ ^ N))
    {χ : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ} (hχu : IsUnitaryChar (𝓞 F) F χ) :
    ∫⁻ t in Ω, ∑' ξ : {ξ : Fin 2 → F // ξ ≠ 0},
        ‖Φ ((t : AdeleRing (𝓞 F) F) • Matrix.vecMul (rowOf F ξ.1) (m : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)))
          * ((χ t : ℂˣ) : ℂ) * ((ideleNorm F t : ℝ) : ℂ) ^ s‖ₑ ∂ν < ⊤ := by
  set σ : ℝ := s.re with hσ

  have hpt : ∀ t : (AdeleRing (𝓞 F) F)ˣ,
      (∑' ξ : {ξ : Fin 2 → F // ξ ≠ 0},
        ‖Φ ((t : AdeleRing (𝓞 F) F) • Matrix.vecMul (rowOf F ξ.1) (m : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)))
          * ((χ t : ℂˣ) : ℂ) * ((ideleNorm F t : ℝ) : ℂ) ^ s‖ₑ) =
        ENNReal.ofReal (thetaAbs Φ m t * (ideleNorm F t) ^ σ) := by
    intro t
    have hsub : Summable (fun ξ : {ξ : Fin 2 → F // ξ ≠ 0} =>
        ‖Φ ((t : AdeleRing (𝓞 F) F) • Matrix.vecMul (rowOf F ξ.1) (m : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)))‖) :=
      (hsum t).subtype _
    simp_rw [enorm_mul, ENNReal.tsum_mul_right]
    rw [ENNReal.ofReal_mul (thetaAbs_nonneg Φ m t), thetaAbs, ENNReal.ofReal_tsum_of_nonneg (fun _ => norm_nonneg _) hsub]
    simp_rw [ofReal_norm]
    have hχ1 : ‖((χ t : ℂˣ) : ℂ)‖ₑ = 1 := by rw [← ofReal_norm, hχu t, ENNReal.ofReal_one]
    rw [hχ1, mul_one, ← ofReal_norm, norm_norm_cpow]
  simp_rw [hpt]

  set G : (AdeleRing (𝓞 F) F)ˣ → ℝ := fun t =>
    if ideleNorm F t ≤ 1 then 2 * C * (ideleNorm F t) ^ (σ - 2) else 2 * C * (ideleNorm F t) ^ (σ - N) with hG
  have hle : ∀ t, thetaAbs Φ m t * (ideleNorm F t) ^ σ ≤ G t := by
    intro t
    have hx0 := ideleNorm_pos t
    by_cases ht : ideleNorm F t ≤ 1
    · rw [hG]; simp only; rw [if_pos ht]
      calc thetaAbs Φ m t * ideleNorm F t ^ σ ≤ 2 * C * (ideleNorm F t) ^ (-(2 : ℝ)) * ideleNorm F t ^ σ :=
            mul_le_mul_of_nonneg_right ((hb t).trans (majorant_lower hC hx0 ht N)) (Real.rpow_nonneg hx0.le _)
        _ = 2 * C * ideleNorm F t ^ (σ - 2) := by
            rw [mul_assoc, ← Real.rpow_add hx0]; congr 2; ring
    · rw [hG]; simp only; rw [if_neg ht]
      have ht' : 1 ≤ ideleNorm F t := (not_le.mp ht).le
      calc thetaAbs Φ m t * ideleNorm F t ^ σ ≤ 2 * C * (ideleNorm F t) ^ (-(N : ℝ)) * ideleNorm F t ^ σ :=
            mul_le_mul_of_nonneg_right ((hb t).trans (majorant_upper hC ht' N)) (Real.rpow_nonneg hx0.le _)
        _ = 2 * C * ideleNorm F t ^ (σ - N) := by
            rw [mul_assoc, ← Real.rpow_add hx0]; congr 2; ring
  have hmono : ∫⁻ t in Ω, ENNReal.ofReal (thetaAbs Φ m t * (ideleNorm F t) ^ σ) ∂ν ≤ ∫⁻ t in Ω, ENNReal.ofReal (G t) ∂ν :=
    lintegral_mono fun t => ENNReal.ofReal_le_ofReal (hle t)
  refine lt_of_le_of_lt hmono ?_

  have hcover : Ω ⊆ (Ω ∩ {t | ideleNorm F t ≤ 1}) ∪ (Ω ∩ {t | 1 ≤ ideleNorm F t}) := by
    intro t ht
    rcases le_total (ideleNorm F t) 1 with h | h
    · exact Or.inl ⟨ht, h⟩
    · exact Or.inr ⟨ht, h⟩
  refine lt_of_le_of_lt ((lintegral_mono_set hcover).trans (lintegral_union_le _ _ _)) ?_
  refine ENNReal.add_lt_top.mpr ⟨?_, ?_⟩
  ·
    have hk : 0 < σ - 2 := by linarith
    have hint := (integrableOn_pow_halves ν hΩ hk).2
    have hI : IntegrableOn (fun t => 2 * C * (ideleNorm F t) ^ (σ - 2)) (Ω ∩ {t | ideleNorm F t ≤ 1}) ν := by
      refine (hint.norm.const_mul (2 * C)).congr (ae_of_all _ fun t => ?_)
      show 2 * C * ‖((ideleNorm F t : ℝ) : ℂ) ^ ((σ - 2 : ℝ) : ℂ)‖ = 2 * C * ideleNorm F t ^ (σ - 2)
      rw [norm_norm_cpow, ofReal_re]
    have hae : ∀ᵐ t ∂ν.restrict (Ω ∩ {t | ideleNorm F t ≤ 1}),
        ENNReal.ofReal (G t) = ENNReal.ofReal (2 * C * (ideleNorm F t) ^ (σ - 2)) :=
      ae_restrict_of_forall_mem (hΩm.inter measurableSet_le_one) fun t ht => by
        have h1 : ideleNorm F t ≤ 1 := ht.2
        rw [hG]; simp only; rw [if_pos h1]
    rw [lintegral_congr_ae hae]
    exact hI.lintegral_lt_top
  ·
    have hk : 0 < (N : ℝ) - σ := by linarith
    have hint := (integrableOn_pow_halves ν hΩ hk).1
    have hI : IntegrableOn (fun t => 2 * C * (ideleNorm F t) ^ (σ - N)) (Ω ∩ {t | 1 ≤ ideleNorm F t}) ν := by
      refine (hint.norm.const_mul (2 * C)).congr (ae_of_all _ fun t => ?_)
      show 2 * C * ‖((ideleNorm F t : ℝ) : ℂ) ^ (-(((N : ℝ) - σ : ℝ) : ℂ))‖ = 2 * C * ideleNorm F t ^ (σ - N)
      rw [norm_norm_cpow, neg_re, ofReal_re, neg_sub]
    have hae : ∀ᵐ t ∂ν.restrict (Ω ∩ {t | 1 ≤ ideleNorm F t}),
        ENNReal.ofReal (G t) = ENNReal.ofReal (2 * C * (ideleNorm F t) ^ (σ - N)) :=
      ae_restrict_of_forall_mem (hΩm.inter measurableSet_one_le) fun t ht => by
        have h2 : 1 ≤ ideleNorm F t := ht.2
        rw [hG]; simp only
        by_cases h1 : ideleNorm F t ≤ 1
        · have heq : ideleNorm F t = 1 := le_antisymm h1 h2
          rw [if_pos h1, heq, Real.one_rpow, Real.one_rpow]
        · rw [if_neg h1]
    rw [lintegral_congr_ae hae]
    exact hI.lintegral_lt_top

end Bounds

section Pointwise

variable [MeasurableSpace (AdeleRing (𝓞 F) F)ˣ] [BorelSpace (AdeleRing (𝓞 F) F)ˣ]

def tateC (ν₀ : Measure (AdeleRing (𝓞 F) F)ˣ) [ν₀.IsHaarMeasure] : ℝ :=
  (NumberField.TateGlobal.exists_setIntegral_eq_entirePart_add_polarPart_and_fe_of_thetaInversion F ν₀).choose

def thetaDual (Φ' : (Fin 2 → AdeleRing (𝓞 F) F) → ℂ) (m : AdelicGL2 (𝓞 F) F) (u : (AdeleRing (𝓞 F) F)ˣ) : ℂ :=
  (((ideleNorm F (Matrix.GeneralLinearGroup.det m))⁻¹ : ℝ) : ℂ) *
    theta Φ' m (u * (Matrix.GeneralLinearGroup.det m)⁻¹)

def upA (ν₀ : Measure (AdeleRing (𝓞 F) F)ˣ) (Ω : Set (AdeleRing (𝓞 F) F)ˣ) (χ : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ)
    (Φ : (Fin 2 → AdeleRing (𝓞 F) F) → ℂ) (m : AdelicGL2 (𝓞 F) F) (s' : ℂ) : ℂ :=
  ∫ t in Ω ∩ {t | 1 ≤ ideleNorm F t}, theta Φ m t * ((χ t : ℂˣ) : ℂ) * ((ideleNorm F t : ℝ) : ℂ) ^ s' ∂ν₀

def upB (ν₀ : Measure (AdeleRing (𝓞 F) F)ˣ) (Ω : Set (AdeleRing (𝓞 F) F)ˣ) (χ : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ)
    (Φ' : (Fin 2 → AdeleRing (𝓞 F) F) → ℂ) (m : AdelicGL2 (𝓞 F) F) (s' : ℂ) : ℂ :=
  ∫ t in Ω ∩ {t | 1 ≤ ideleNorm F t}, thetaDual Φ' m t * ((χ t : ℂˣ) : ℂ)⁻¹ * ((ideleNorm F t : ℝ) : ℂ) ^ s' ∂ν₀

open scoped Classical in

def tau0 (χ : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ) : ℝ :=
  if h : ∃ τ : ℝ, χ = normPowChar F τ then h.choose else 0

omit [MeasurableSpace (AdeleRing (𝓞 F) F)ˣ] [BorelSpace (AdeleRing (𝓞 F) F)ˣ] in
open scoped Classical in
theorem tau0_spec {χ : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ} (h : ∃ τ : ℝ, χ = normPowChar F τ) : χ = normPowChar F (tau0 χ) := by
  rw [tau0, dif_pos h]; exact h.choose_spec

open scoped Classical in

def cOne (ν₀ : Measure (AdeleRing (𝓞 F) F)ˣ) [ν₀.IsHaarMeasure] (χ : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ) (b : ℂ) : ℂ :=
  if ∃ τ : ℝ, χ = normPowChar F τ then (tateC ν₀ : ℂ) * b / 2 else 0

open scoped Classical in
def cZero (ν₀ : Measure (AdeleRing (𝓞 F) F)ˣ) [ν₀.IsHaarMeasure] (χ : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ) (a : ℂ) : ℂ :=
  if ∃ τ : ℝ, χ = normPowChar F τ then -((tateC ν₀ : ℂ) * a) / 2 else 0

def pOne (χ : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ) : ℂ := (1 - (tau0 χ : ℂ) * I) / 2

def pZero (χ : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ) : ℂ := -(1 + (tau0 χ : ℂ) * I) / 2

open scoped Classical in
theorem cOne_cZero_of_ne (ν₀ : Measure (AdeleRing (𝓞 F) F)ˣ) [ν₀.IsHaarMeasure] {χ : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ}
    (h : ∀ τ : ℝ, χ ≠ normPowChar F τ) (a b : ℂ) : cOne ν₀ χ b = 0 ∧ cZero ν₀ χ a = 0 := by
  have h' : ¬ ∃ τ : ℝ, χ = normPowChar F τ := fun ⟨τ, hτ⟩ => h τ hτ
  exact ⟨by rw [cOne, if_neg h'], by rw [cZero, if_neg h']⟩

variable (ν₀ : Measure (AdeleRing (𝓞 F) F)ˣ) [ν₀.IsHaarMeasure]
variable {Ω : Set (AdeleRing (𝓞 F) F)ˣ}

omit [MeasurableSpace (AdeleRing (𝓞 F) F)ˣ] [BorelSpace (AdeleRing (𝓞 F) F)ˣ] in

theorem continuous_theta_mul {Φ : (Fin 2 → AdeleRing (𝓞 F) F) → ℂ} (hc : Continuous (thetaG Φ))
    (m : AdelicGL2 (𝓞 F) F) (e : (AdeleRing (𝓞 F) F)ˣ) : Continuous fun t : (AdeleRing (𝓞 F) F)ˣ => theta Φ m (t * e) := by
  have h : (fun t : (AdeleRing (𝓞 F) F)ˣ => theta Φ m (t * e)) = fun t => thetaG Φ (centralScalar (𝓞 F) F (t * e) * m) := by
    funext t; exact theta_eq_thetaG Φ m (t * e)
  rw [h]
  exact hc.comp ((continuous_centralScalar.comp (continuous_id.mul continuous_const)).mul continuous_const)

omit [MeasurableSpace (AdeleRing (𝓞 F) F)ˣ] [BorelSpace (AdeleRing (𝓞 F) F)ˣ] in
theorem norm_theta_le_thetaAbs {Φ : (Fin 2 → AdeleRing (𝓞 F) F) → ℂ} {m : AdelicGL2 (𝓞 F) F} {t : (AdeleRing (𝓞 F) F)ˣ}
    (hsum : Summable (fun ξ : Fin 2 → F =>
      ‖Φ ((t : AdeleRing (𝓞 F) F) • Matrix.vecMul (rowOf F ξ) (m : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)))‖)) :
    ‖theta Φ m t‖ ≤ thetaAbs Φ m t :=
  norm_tsum_le_tsum_norm (hsum.subtype _)

theorem integrableOn_theta_mul_cpow_upper (hΩ : IsFundamentalDomain (principalUnits F) Ω ν₀)
    {Φ : (Fin 2 → AdeleRing (𝓞 F) F) → ℂ} {m : AdelicGL2 (𝓞 F) F} (hc : Continuous (thetaG Φ))
    (hTP : ∀ N : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ t : (AdeleRing (𝓞 F) F)ˣ,
      Summable (fun ξ : Fin 2 → F =>
        ‖Φ ((t : AdeleRing (𝓞 F) F) • Matrix.vecMul (rowOf F ξ) (m : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)))‖) ∧
      thetaAbs Φ m t ≤ C * (1 + (ideleNorm F t)⁻¹ ^ 2) * min 1 ((ideleNorm F t)⁻¹ ^ N))
    {e : (AdeleRing (𝓞 F) F)ˣ} (he : ideleNorm F e = 1) (c : ℂ) (σ : ℝ) :
    IntegrableOn (fun t => c * theta Φ m (t * e) * ((ideleNorm F t : ℝ) : ℂ) ^ (σ : ℂ))
      (Ω ∩ {t | 1 ≤ ideleNorm F t}) ν₀ := by
  set N : ℕ := ⌈|σ|⌉₊ + 1 with hN
  obtain ⟨C, hC, hb⟩ := hTP N
  have hk : 0 < (N : ℝ) - σ := by
    have h1 : |σ| ≤ ⌈|σ|⌉₊ := Nat.le_ceil _
    have h2 : σ ≤ |σ| := le_abs_self σ
    rw [hN]; push_cast; linarith
  refine integrableOn_upper_of_le ν₀ hΩ ?_ hk (C := ‖c‖ * (2 * C)) fun t ht => ?_
  · exact ((continuous_const.mul (continuous_theta_mul hc m e)).mul (continuous_norm_cpow _)).aestronglyMeasurable
  · have hte : 1 ≤ ideleNorm F (t * e) := by rwa [ideleNorm_mul, he, mul_one]
    have h1 := (norm_theta_le_thetaAbs (hb (t * e)).1).trans ((hb (t * e)).2.trans (majorant_upper hC hte N))
    rw [ideleNorm_mul, he, mul_one] at h1
    rw [norm_mul, norm_mul, norm_norm_cpow, ofReal_re]
    have hx0 := ideleNorm_pos t
    calc ‖c‖ * ‖theta Φ m (t * e)‖ * ideleNorm F t ^ σ ≤ ‖c‖ * (2 * C * ideleNorm F t ^ (-(N : ℝ))) * ideleNorm F t ^ σ := by
          gcongr
      _ = ‖c‖ * (2 * C) * ideleNorm F t ^ (-((N : ℝ) - σ)) := by
          rw [show -((N : ℝ) - σ) = -(N : ℝ) + σ by ring, Real.rpow_add hx0]; ring

variable [MeasurableSpace (AdeleRing (𝓞 F) F)] [BorelSpace (AdeleRing (𝓞 F) F)]
variable (μ₁ : Measure (AdeleRing (𝓞 F) F)) [μ₁.IsAddHaarMeasure] (hμ₁ : μ₁ (adelicBox F) = 1)
variable {ψ : AddChar (AdeleRing (𝓞 F) F) ℂ} (hψ : IsGlobalAddChar F ψ)
variable {μ ν : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ}
variable (hμ : IsUnitaryChar (𝓞 F) F μ) (hν : IsUnitaryChar (𝓞 F) F ν)
variable (hμic : IsIdeleClassChar (𝓞 F) F μ) (hνic : IsIdeleClassChar (𝓞 F) F ν)
variable (hμc : Continuous fun x : (AdeleRing (𝓞 F) F)ˣ => ((μ x : ℂˣ) : ℂ))
variable (hνc : Continuous fun x : (AdeleRing (𝓞 F) F)ˣ => ((ν x : ℂˣ) : ℂ))
variable {Φ : (Fin 2 → AdeleRing (𝓞 F) F) → ℂ} (hΦ : Φ ∈ schwartzBruhat2 F)
variable (hα : ∀ x, 0 < ((moduleChar F x : ℝˣ) : ℝ))

omit [MeasurableSpace (AdeleRing (𝓞 F) F)ˣ] [BorelSpace (AdeleRing (𝓞 F) F)ˣ]
  [MeasurableSpace (AdeleRing (𝓞 F) F)] [BorelSpace (AdeleRing (𝓞 F) F)] in

theorem tsum_mul_mul {ι : Type*} (f : ι → ℂ) (c d : ℂ) : ∑' i, f i * c * d = (∑' i, f i) * c * d := by
  rw [← tsum_mul_right, ← tsum_mul_right]

omit [MeasurableSpace (AdeleRing (𝓞 F) F)ˣ] [BorelSpace (AdeleRing (𝓞 F) F)ˣ]
  [MeasurableSpace (AdeleRing (𝓞 F) F)] [BorelSpace (AdeleRing (𝓞 F) F)] in
theorem ne_zero_of_re_pos {z : ℂ} (hz : 0 < z.re) : z ≠ 0 := fun h => by rw [h, zero_re] at hz; exact lt_irrefl _ hz

omit [MeasurableSpace (AdeleRing (𝓞 F) F)ˣ] [BorelSpace (AdeleRing (𝓞 F) F)ˣ]
  [MeasurableSpace (AdeleRing (𝓞 F) F)] [BorelSpace (AdeleRing (𝓞 F) F)] in

theorem polar_alg (C a b m X τ s : ℂ) :
    m * (X + C * b / (2 * s + 1 - 2 + τ * I) - C * a / (2 * s + 1 + τ * I)) =
      m * X + (C * b / 2 / (s - (1 - τ * I) / 2) + -(C * a) / 2 / (s - -(1 + τ * I) / 2)) * m := by
  have e1 : 2 * s + 1 - 2 + τ * I = 2 * (s - (1 - τ * I) / 2) := by ring
  have e2 : 2 * s + 1 + τ * I = 2 * (s - -(1 + τ * I) / 2) := by ring
  rw [e1, e2, ← div_div, ← div_div]
  ring

omit [MeasurableSpace (AdeleRing (𝓞 F) F)ˣ] [BorelSpace (AdeleRing (𝓞 F) F)ˣ]
  [MeasurableSpace (AdeleRing (𝓞 F) F)] [BorelSpace (AdeleRing (𝓞 F) F)] in

theorem polar_alg' (C a b m X τ s : ℂ) :
    m * (X + C * a / (2 * s + 1 - 2 - τ * I) - C * b / (2 * s + 1 - τ * I)) =
      m * X - (C * b / 2 / (s + (1 - τ * I) / 2) + -(C * a) / 2 / (s + -(1 + τ * I) / 2)) * m := by
  have e1 : 2 * s + 1 - 2 - τ * I = 2 * (s + -(1 + τ * I) / 2) := by ring
  have e2 : 2 * s + 1 - τ * I = 2 * (s + (1 - τ * I) / 2) := by ring
  rw [e1, e2, ← div_div, ← div_div]
  ring

include hμ₁ hψ hμ hν hμic hνic hμc hνc hΦ in
set_option maxHeartbeats 4000000 in

theorem pointwise (hΩ : IsFundamentalDomain (principalUnits F) Ω ν₀) (hΩm : MeasurableSet Ω)
    (m : AdelicGL2 (𝓞 F) F) (hm : ideleNorm F (Matrix.GeneralLinearGroup.det m) = 1)
    (s : ℂ) (hs : (1 / 2 : ℝ) < s.re) :
    godementEisenstein F ν₀ μ ν (moduleChar F) hα Φ s m =
      ((μ (Matrix.GeneralLinearGroup.det m) : ℂˣ) : ℂ) *
          (upA ν₀ Ω (μ * ν⁻¹) Φ m (2 * s + 1) + upB ν₀ Ω (μ * ν⁻¹) (reflectPair ψ μ₁ Φ) m (1 - 2 * s)) +
        (cOne ν₀ (μ * ν⁻¹) (reflectPair ψ μ₁ Φ 0) / (s - pOne (μ * ν⁻¹)) +
            cZero ν₀ (μ * ν⁻¹) (Φ 0) / (s - pZero (μ * ν⁻¹))) * ((μ (Matrix.GeneralLinearGroup.det m) : ℂˣ) : ℂ) ∧
    godementEisenstein F ν₀ ν μ (moduleChar F) hα (reflectPair ψ μ₁ Φ) s m =
      ((μ (Matrix.GeneralLinearGroup.det m) : ℂˣ) : ℂ) *
          (upB ν₀ Ω (μ * ν⁻¹) (reflectPair ψ μ₁ Φ) m (2 * s + 1) + upA ν₀ Ω (μ * ν⁻¹) Φ m (1 - 2 * s)) -
        (cOne ν₀ (μ * ν⁻¹) (reflectPair ψ μ₁ Φ 0) / (s + pOne (μ * ν⁻¹)) +
            cZero ν₀ (μ * ν⁻¹) (Φ 0) / (s + pZero (μ * ν⁻¹))) * ((μ (Matrix.GeneralLinearGroup.det m) : ℂˣ) : ℂ) := by
  set χ : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ := μ * ν⁻¹ with hχdef
  set Φ' : (Fin 2 → AdeleRing (𝓞 F) F) → ℂ := reflectPair ψ μ₁ Φ with hΦ'def
  set d : (AdeleRing (𝓞 F) F)ˣ := Matrix.GeneralLinearGroup.det m with hddef
  have hχ : IsIdeleClassChar (𝓞 F) F χ := isIdeleClassChar_mul hμic (isIdeleClassChar_inv hνic)
  have hχu : IsUnitaryChar (𝓞 F) F χ := isUnitaryChar_mul hμ (isUnitaryChar_inv hν)
  have hχc : Continuous fun x : (AdeleRing (𝓞 F) F)ˣ => ((χ x : ℂˣ) : ℂ) := continuous_coe_mul hμc (continuous_coe_inv hνc)
  have hχ'u : IsUnitaryChar (𝓞 F) F (ν * μ⁻¹) := isUnitaryChar_mul hν (isUnitaryChar_inv hμ)
  have hΦ' : Φ' ∈ schwartzBruhat2 F :=
    (NumberField.AdelicFourier.fourierTransform2_mem_schwartzBruhat2_and_reflectPair_mem_schwartzBruhat2 F μ₁ hψ hΦ).2
  have hΦc : Continuous Φ :=
    (NumberField.AdelicFourier.continuous_integrable_comp_vecMul_mem_and_bottomRowVec_mem_schwartzBruhat_of_mem_schwartzBruhat2
      F Φ hΦ).1
  have hΦ'c : Continuous Φ' :=
    (NumberField.AdelicFourier.continuous_integrable_comp_vecMul_mem_and_bottomRowVec_mem_schwartzBruhat_of_mem_schwartzBruhat2
      F Φ' hΦ').1

  have TPΦ := NumberField.AdelicFourier.exists_forall_tsum_norm_apply_smul_vecMul_le_and_continuous_tsum_of_mem_schwartzBruhat2 F hΦ
  have TPΦ' := NumberField.AdelicFourier.exists_forall_tsum_norm_apply_smul_vecMul_le_and_continuous_tsum_of_mem_schwartzBruhat2 F hΦ'
  have hTPm : ∀ N : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ t : (AdeleRing (𝓞 F) F)ˣ,
      Summable (fun ξ : Fin 2 → F =>
        ‖Φ ((t : AdeleRing (𝓞 F) F) • Matrix.vecMul (rowOf F ξ) (m : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)))‖) ∧
      thetaAbs Φ m t ≤ C * (1 + (ideleNorm F t)⁻¹ ^ 2) * min 1 ((ideleNorm F t)⁻¹ ^ N) := fun N => by
    obtain ⟨C, hC, h⟩ := TPΦ.1 {m} isCompact_singleton N
    exact ⟨C, hC, fun t => h m (mem_singleton m) t⟩
  have hTPm' : ∀ N : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ t : (AdeleRing (𝓞 F) F)ˣ,
      Summable (fun ξ : Fin 2 → F =>
        ‖Φ' ((t : AdeleRing (𝓞 F) F) • Matrix.vecMul (rowOf F ξ) (m : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)))‖) ∧
      thetaAbs Φ' m t ≤ C * (1 + (ideleNorm F t)⁻¹ ^ 2) * min 1 ((ideleNorm F t)⁻¹ ^ N) := fun N => by
    obtain ⟨C, hC, h⟩ := TPΦ'.1 {m} isCompact_singleton N
    exact ⟨C, hC, fun t => h m (mem_singleton m) t⟩
  have hcG : Continuous (thetaG Φ) := TPΦ.2
  have hcG' : Continuous (thetaG Φ') := TPΦ'.2

  set θ : (AdeleRing (𝓞 F) F)ˣ → ℂ := theta Φ m with hθdef
  set θ' : (AdeleRing (𝓞 F) F)ˣ → ℂ := thetaDual Φ' m with hθ'def
  set a : ℂ := Φ 0 with hadef
  set b : ℂ := (((ideleNorm F d)⁻¹ : ℝ) : ℂ) * Φ' 0 with hbdef
  have hd1 : ideleNorm F d⁻¹ = 1 := by rw [ideleNorm_inv, hm, inv_one]
  have hθ' : ∀ (u : Fˣ) (t : (AdeleRing (𝓞 F) F)ˣ),
      θ' (Units.map (algebraMap F (AdeleRing (𝓞 F) F) : F →* AdeleRing (𝓞 F) F) u * t) = θ' t := by
    intro u t
    show thetaDual Φ' m _ = thetaDual Φ' m t
    unfold thetaDual
    rw [mul_assoc, theta_principal_mul]
  have hrel : ∀ t : (AdeleRing (𝓞 F) F)ˣ,
      θ t + a = ((ideleNorm F t : ℝ) : ℂ) ^ (-((2 : ℝ) : ℂ)) * (θ' t⁻¹ + b) := by
    intro t
    have h := NumberField.AdelicFourier.tsum_apply_smul_vecMul_add_eq_ideleNorm_cpow_neg_two_mul_tsum_reflectPair_of_mem_schwartzBruhat2
      F μ₁ hμ₁ hψ hΦ m t
    have h2 : ((2 : ℝ) : ℂ) = (2 : ℂ) := by norm_num
    rw [h2]
    exact h
  have hdec : ∀ σ : ℝ, IntegrableOn (fun t => θ t * ((ideleNorm F t : ℝ) : ℂ) ^ (σ : ℂ))
      (Ω ∩ {t | 1 ≤ ideleNorm F t}) ν₀ := fun σ => by
    have h := integrableOn_theta_mul_cpow_upper ν₀ hΩ hcG hTPm (e := 1) (ideleNorm_one F) 1 σ
    exact h.congr (ae_of_all _ fun t => by simp only [one_mul, mul_one, hθdef])
  have hdec' : ∀ σ : ℝ, IntegrableOn (fun t => θ' t * ((ideleNorm F t : ℝ) : ℂ) ^ (σ : ℂ))
      (Ω ∩ {t | 1 ≤ ideleNorm F t}) ν₀ := fun σ =>
    integrableOn_theta_mul_cpow_upper ν₀ hΩ hcG' hTPm' hd1 _ σ

  obtain ⟨R, R', hR, hR', -, hnon, hexc, -⟩ :=
    (NumberField.TateGlobal.exists_setIntegral_eq_entirePart_add_polarPart_and_fe_of_thetaInversion F ν₀).choose_spec.2
      Ω hΩ χ hχ hχu hχc θ θ' hθ' a b 2 two_pos hrel hdec hdec'
  have h2c : ((2 : ℝ) : ℂ) = (2 : ℂ) := by norm_num
  have hRA : R (2 * s + 1) = upA ν₀ Ω χ Φ m (2 * s + 1) + upB ν₀ Ω χ Φ' m (1 - 2 * s) := by
    rw [hR, upA, upB, h2c, show (2 : ℂ) - (2 * s + 1) = 1 - 2 * s by ring]
  have hR'B : R' (2 * s + 1) = upB ν₀ Ω χ Φ' m (2 * s + 1) + upA ν₀ Ω χ Φ m (1 - 2 * s) := by
    rw [hR', upA, upB, h2c, show (2 : ℂ) - (2 * s + 1) = 1 - 2 * s by ring]

  have hs' : 2 < (2 * s + 1).re := by
    simp only [add_re, mul_re, re_ofNat, im_ofNat, one_re, zero_mul, sub_zero]; linarith
  have hs'd : (2 : ℝ) < (2 * s + 1).re := hs'
  have hs'N : (2 * s + 1).re < ((⌈(2 * s + 1).re⌉₊ + 1 : ℕ) : ℝ) := by
    have := Nat.le_ceil ((2 * s + 1).re); push_cast; linarith

  obtain ⟨C₁, hC₁, hb₁⟩ := hTPm (⌈(2 * s + 1).re⌉₊ + 1)
  have habs := lintegral_thetaAbs_lt_top ν₀ hΩ hΩm hC₁ hs' hs'N (fun t => (hb₁ t).1) (fun t => (hb₁ t).2) hχu
  have hU := AutomorphicForm.summable_godementSection_and_bruhatSeries_eq_mul_setIntegral_tsum_of_lintegral_tsum_enorm_lt_top
    F ν₀ Ω hΩ μ ν hμic hνic hμc hνc (moduleChar F) hα Φ hΦc s m habs
  have hZ : (∫ t in Ω, ∑' ξ : {ξ : Fin 2 → F // ξ ≠ 0},
        Φ ((t : AdeleRing (𝓞 F) F) • Matrix.vecMul (fun i => algebraMap F (AdeleRing (𝓞 F) F) (ξ.1 i))
              (m : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)))
          * ((χ t : ℂˣ) : ℂ) * ((ideleNorm F t : ℝ) : ℂ) ^ (2 * s + 1) ∂ν₀) =
      ∫ t in Ω, θ t * ((χ t : ℂˣ) : ℂ) * ((ideleNorm F t : ℝ) : ℂ) ^ (2 * s + 1) ∂ν₀ := by
    congr 1; funext t; exact tsum_mul_mul _ _ _
  have hcpow : ((cpowChar (moduleChar F) hα (s + 1 / 2) d : ℂˣ) : ℂ) = 1 := by
    rw [cpowChar_apply_val, val_moduleChar_apply, hm, ofReal_one, one_cpow]
  have hE : godementEisenstein F ν₀ μ ν (moduleChar F) hα Φ s m =
      ((μ d : ℂˣ) : ℂ) * ∫ t in Ω, θ t * ((χ t : ℂˣ) : ℂ) * ((ideleNorm F t : ℝ) : ℂ) ^ (2 * s + 1) ∂ν₀ := by
    rw [godementEisenstein_def, hU.2.2, ← hddef, hcpow, mul_one, hZ]

  set Ω' : Set (AdeleRing (𝓞 F) F)ˣ := (fun u : (AdeleRing (𝓞 F) F)ˣ => u * d) ⁻¹' Ω with hΩ'def
  have hΩ' : IsFundamentalDomain (principalUnits F) Ω' ν₀ := isFundamentalDomain_translate ν₀ hΩ d
  have hΩ'm : MeasurableSet Ω' := hΩm.preimage (measurable_mul_const d)
  obtain ⟨C₂, hC₂, hb₂⟩ := hTPm' (⌈(2 * s + 1).re⌉₊ + 1)
  have habs' := lintegral_thetaAbs_lt_top ν₀ hΩ' hΩ'm hC₂ hs' hs'N (fun t => (hb₂ t).1) (fun t => (hb₂ t).2) hχ'u
  have hU' := AutomorphicForm.summable_godementSection_and_bruhatSeries_eq_mul_setIntegral_tsum_of_lintegral_tsum_enorm_lt_top
    F ν₀ Ω' hΩ' ν μ hνic hμic hνc hμc (moduleChar F) hα Φ' hΦ'c s m habs'
  have hpt' : ∀ t : (AdeleRing (𝓞 F) F)ˣ,
      theta Φ' m (t * d⁻¹) * (((ν * μ⁻¹) (t * d⁻¹) : ℂˣ) : ℂ) * ((ideleNorm F (t * d⁻¹) : ℝ) : ℂ) ^ (2 * s + 1) =
        ((χ d : ℂˣ) : ℂ) * (θ' t * ((χ t : ℂˣ) : ℂ)⁻¹ * ((ideleNorm F t : ℝ) : ℂ) ^ (2 * s + 1)) := by
    intro t
    have hth : θ' t = theta Φ' m (t * d⁻¹) := by
      show thetaDual Φ' m t = _
      rw [thetaDual, ← hddef, hm, inv_one, ofReal_one, one_mul]
    rw [hth, ideleNorm_mul, hd1, mul_one, coe_swap_inv, ← hχdef, map_mul, map_inv, Units.val_mul,
      Units.val_inv_eq_inv_val, mul_inv, inv_inv]
    ring
  have hZ' : (∫ u in Ω', ∑' ξ : {ξ : Fin 2 → F // ξ ≠ 0},
        Φ' ((u : AdeleRing (𝓞 F) F) • Matrix.vecMul (fun i => algebraMap F (AdeleRing (𝓞 F) F) (ξ.1 i))
              (m : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)))
          * (((ν * μ⁻¹) u : ℂˣ) : ℂ) * ((ideleNorm F u : ℝ) : ℂ) ^ (2 * s + 1) ∂ν₀) =
      ((χ d : ℂˣ) : ℂ) * ∫ t in Ω, θ' t * ((χ t : ℂˣ) : ℂ)⁻¹ * ((ideleNorm F t : ℝ) : ℂ) ^ (2 * s + 1) ∂ν₀ := by
    have h1 : (fun u : (AdeleRing (𝓞 F) F)ˣ => ∑' ξ : {ξ : Fin 2 → F // ξ ≠ 0},
        Φ' ((u : AdeleRing (𝓞 F) F) • Matrix.vecMul (fun i => algebraMap F (AdeleRing (𝓞 F) F) (ξ.1 i))
              (m : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)))
          * (((ν * μ⁻¹) u : ℂˣ) : ℂ) * ((ideleNorm F u : ℝ) : ℂ) ^ (2 * s + 1)) =
        fun u => theta Φ' m u * (((ν * μ⁻¹) u : ℂˣ) : ℂ) * ((ideleNorm F u : ℝ) : ℂ) ^ (2 * s + 1) := by
      funext u; exact tsum_mul_mul _ _ _
    rw [h1, setIntegral_translate ν₀ d, ← integral_const_mul]
    congr 1; funext t; exact hpt' t
  have hcpow' : ((cpowChar (moduleChar F) hα (s + 1 / 2) d : ℂˣ) : ℂ) = 1 := hcpow
  have hνχ : ((ν d : ℂˣ) : ℂ) * ((χ d : ℂˣ) : ℂ) = ((μ d : ℂˣ) : ℂ) := by
    rw [hχdef, coe_mul_apply, coe_inv_apply, mul_comm, mul_assoc, inv_mul_cancel₀ (Units.ne_zero _), mul_one]
  have hE' : godementEisenstein F ν₀ ν μ (moduleChar F) hα Φ' s m =
      ((μ d : ℂˣ) : ℂ) * ∫ t in Ω, θ' t * ((χ t : ℂˣ) : ℂ)⁻¹ * ((ideleNorm F t : ℝ) : ℂ) ^ (2 * s + 1) ∂ν₀ := by
    rw [godementEisenstein_def, hU'.2.2, ← hddef, hcpow', mul_one, hZ', ← mul_assoc, hνχ]
  have hb1 : b = Φ' 0 := by rw [hbdef, hm, inv_one, ofReal_one, one_mul]

  by_cases hex : ∃ τ : ℝ, χ = normPowChar F τ
  · have hτ := tau0_spec hex
    obtain ⟨hZe, hZ'e⟩ := hexc (tau0 χ) hτ
    have h1 := hZe (2 * s + 1) hs'd
    have h2 := hZ'e (2 * s + 1) hs'd
    have hc1 : cOne ν₀ χ (Φ' 0) = (tateC ν₀ : ℂ) * Φ' 0 / 2 := by rw [cOne, if_pos hex]
    have hc0 : cZero ν₀ χ (Φ 0) = -((tateC ν₀ : ℂ) * Φ 0) / 2 := by rw [cZero, if_pos hex]
    refine ⟨?_, ?_⟩
    · rw [hE, h1, hRA, hc1, hc0, pOne, pZero, hb1]
      exact polar_alg _ _ _ _ _ _ _
    · rw [hE', h2, hR'B, hc1, hc0, pOne, pZero, hb1]
      exact polar_alg' _ _ _ _ _ _ _
  · have hne : ∀ τ : ℝ, χ ≠ normPowChar F τ := fun τ h => hex ⟨τ, h⟩
    obtain ⟨hZn, hZ'n⟩ := hnon hne
    obtain ⟨hc1, hc0⟩ := cOne_cZero_of_ne ν₀ hne (Φ 0) (Φ' 0)
    refine ⟨?_, ?_⟩
    · rw [hE, hZn _ hs'd, hRA, hc1, hc0]; simp
    · rw [hE', hZ'n _ hs'd, hR'B, hc1, hc0]; simp

end Pointwise

section Family

variable [MeasurableSpace (AdeleRing (𝓞 F) F)ˣ] [BorelSpace (AdeleRing (𝓞 F) F)ˣ]
variable (ν₀ : Measure (AdeleRing (𝓞 F) F)ˣ) [ν₀.IsHaarMeasure] {Ω : Set (AdeleRing (𝓞 F) F)ˣ}

omit [MeasurableSpace (AdeleRing (𝓞 F) F)ˣ] [BorelSpace (AdeleRing (𝓞 F) F)ˣ] in
theorem pow_add_pow_neg_le {x M : ℝ} (hx : 1 ≤ x) : x ^ M + x ^ (-M) ≤ 2 * x ^ |M| := by
  have h1 : x ^ M ≤ x ^ |M| := Real.rpow_le_rpow_of_exponent_le hx (le_abs_self M)
  have h2 : x ^ (-M) ≤ x ^ |M| := Real.rpow_le_rpow_of_exponent_le hx (neg_le_abs M)
  linarith

theorem mellin_hyps (hΩ : IsFundamentalDomain (principalUnits F) Ω ν₀) (hΩm : MeasurableSet Ω)
    {Ψ : (Fin 2 → AdeleRing (𝓞 F) F) → ℂ}
    (hTP : ∀ K : Set (AdelicGL2 (𝓞 F) F), IsCompact K → ∀ N : ℕ, ∃ C : ℝ, 0 ≤ C ∧
      ∀ m ∈ K, ∀ t : (AdeleRing (𝓞 F) F)ˣ,
        Summable (fun ξ : Fin 2 → F =>
          ‖Ψ ((t : AdeleRing (𝓞 F) F) • Matrix.vecMul (rowOf F ξ) (m : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)))‖) ∧
        thetaAbs Ψ m t ≤ C * (1 + (ideleNorm F t)⁻¹ ^ 2) * min 1 ((ideleNorm F t)⁻¹ ^ N))
    (hcG : Continuous (thetaG Ψ))
    (e : AdelicGL2 (𝓞 F) F → (AdeleRing (𝓞 F) F)ˣ) (he : Continuous e) (he1 : ∀ g, ideleNorm F (e g) = 1)
    (c : AdelicGL2 (𝓞 F) F → (AdeleRing (𝓞 F) F)ˣ → ℂ) (hc : ∀ t, Continuous fun g => c g t) (hct : ∀ g, Continuous (c g))
    (hc1 : ∀ g t, ‖c g t‖ = 1) :
    (∀ g, AEStronglyMeasurable (fun t => c g t * theta Ψ (gone g) (t * e g))
      (ν₀.restrict (Ω ∩ {t | 1 ≤ ideleNorm F t}))) ∧
    (∀ᵐ t ∂(ν₀.restrict (Ω ∩ {t | 1 ≤ ideleNorm F t})), Continuous fun g => c g t * theta Ψ (gone g) (t * e g)) ∧
    (∀ (g₀ : AdelicGL2 (𝓞 F) F) (M : ℝ), ∃ bound : (AdeleRing (𝓞 F) F)ˣ → ℝ,
      Integrable bound (ν₀.restrict (Ω ∩ {t | 1 ≤ ideleNorm F t})) ∧
      ∀ᶠ g in 𝓝 g₀, ∀ᵐ t ∂(ν₀.restrict (Ω ∩ {t | 1 ≤ ideleNorm F t})),
        ‖c g t * theta Ψ (gone g) (t * e g)‖ * (ideleNorm F t ^ M + ideleNorm F t ^ (-M)) ≤ bound t) := by
  refine ⟨fun g => ?_, ae_of_all _ fun t => ?_, fun g₀ M => ?_⟩
  · exact ((hct g).mul (continuous_theta_mul hcG (gone g) (e g))).aestronglyMeasurable
  · have h : (fun g => c g t * theta Ψ (gone g) (t * e g)) =
        fun g => c g t * thetaG Ψ (centralScalar (𝓞 F) F (t * e g) * gone g) := by
      funext g; rw [theta_eq_thetaG]
    rw [h]
    exact (hc t).mul (hcG.comp ((continuous_centralScalar.comp (continuous_const.mul he)).mul continuous_gone))
  · obtain ⟨K₀, hK₀, hK₀n⟩ := exists_compact_mem_nhds g₀
    set N : ℕ := ⌈|M|⌉₊ + 1 with hN
    obtain ⟨C, hC, hb⟩ := hTP (gone '' K₀) (hK₀.image continuous_gone) N
    have hk : 0 < (N : ℝ) - |M| := by
      have h1 : |M| ≤ ⌈|M|⌉₊ := Nat.le_ceil _
      rw [hN]; push_cast; linarith
    refine ⟨fun t => 4 * C * ‖((ideleNorm F t : ℝ) : ℂ) ^ (-(((N : ℝ) - |M| : ℝ) : ℂ))‖,
      ((integrableOn_pow_halves ν₀ hΩ hk).1.norm.const_mul (4 * C)), ?_⟩
    refine Filter.eventually_of_mem hK₀n fun g hg => ?_
    refine ae_restrict_of_forall_mem (hΩm.inter measurableSet_one_le) fun t ht => ?_
    have ht1 : 1 ≤ ideleNorm F t := ht.2
    have hx0 := ideleNorm_pos t
    have hmem : gone g ∈ gone '' K₀ := mem_image_of_mem _ hg
    obtain ⟨hsum, hbd⟩ := hb (gone g) hmem (t * e g)
    have hte : 1 ≤ ideleNorm F (t * e g) := by rwa [ideleNorm_mul, he1, mul_one]
    have h1 := (norm_theta_le_thetaAbs hsum).trans (hbd.trans (majorant_upper hC hte N))
    rw [ideleNorm_mul, he1, mul_one] at h1
    show ‖c g t * theta Ψ (gone g) (t * e g)‖ * (ideleNorm F t ^ M + ideleNorm F t ^ (-M)) ≤
      4 * C * ‖((ideleNorm F t : ℝ) : ℂ) ^ (-(((N : ℝ) - |M| : ℝ) : ℂ))‖
    rw [norm_mul, hc1, one_mul, norm_norm_cpow, neg_re, ofReal_re]
    calc ‖theta Ψ (gone g) (t * e g)‖ * (ideleNorm F t ^ M + ideleNorm F t ^ (-M))
        ≤ (2 * C * ideleNorm F t ^ (-(N : ℝ))) * (2 * ideleNorm F t ^ |M|) :=
          mul_le_mul h1 (pow_add_pow_neg_le ht1) (by positivity) (by positivity)
      _ = 4 * C * ideleNorm F t ^ (-((N : ℝ) - |M|)) := by
          rw [show -((N : ℝ) - |M|) = -(N : ℝ) + |M| by ring, Real.rpow_add hx0]; ring

theorem mellin (hΩ : IsFundamentalDomain (principalUnits F) Ω ν₀) (hΩm : MeasurableSet Ω)
    {Ψ : (Fin 2 → AdeleRing (𝓞 F) F) → ℂ}
    (hTP : ∀ K : Set (AdelicGL2 (𝓞 F) F), IsCompact K → ∀ N : ℕ, ∃ C : ℝ, 0 ≤ C ∧
      ∀ m ∈ K, ∀ t : (AdeleRing (𝓞 F) F)ˣ,
        Summable (fun ξ : Fin 2 → F =>
          ‖Ψ ((t : AdeleRing (𝓞 F) F) • Matrix.vecMul (rowOf F ξ) (m : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)))‖) ∧
        thetaAbs Ψ m t ≤ C * (1 + (ideleNorm F t)⁻¹ ^ 2) * min 1 ((ideleNorm F t)⁻¹ ^ N))
    (hcG : Continuous (thetaG Ψ))
    (e : AdelicGL2 (𝓞 F) F → (AdeleRing (𝓞 F) F)ˣ) (he : Continuous e) (he1 : ∀ g, ideleNorm F (e g) = 1)
    (c : AdelicGL2 (𝓞 F) F → (AdeleRing (𝓞 F) F)ˣ → ℂ) (hc : ∀ t, Continuous fun g => c g t) (hct : ∀ g, Continuous (c g))
    (hc1 : ∀ g t, ‖c g t‖ = 1) :
    (∀ g, Differentiable ℂ fun s' : ℂ =>
      ∫ t in Ω ∩ {t | 1 ≤ ideleNorm F t}, c g t * theta Ψ (gone g) (t * e g) * ((ideleNorm F t : ℝ) : ℂ) ^ s' ∂ν₀) ∧
    (Continuous fun q : ℂ × AdelicGL2 (𝓞 F) F =>
      ∫ t in Ω ∩ {t | 1 ≤ ideleNorm F t}, c q.2 t * theta Ψ (gone q.2) (t * e q.2) * ((ideleNorm F t : ℝ) : ℂ) ^ q.1 ∂ν₀) ∧
    (∀ (g : AdelicGL2 (𝓞 F) F) (M : ℝ) (s' : ℂ), |s'.re| ≤ M →
      IntegrableOn (fun t => ‖c g t * theta Ψ (gone g) (t * e g)‖ * (ideleNorm F t ^ M + ideleNorm F t ^ (-M)))
        (Ω ∩ {t | 1 ≤ ideleNorm F t}) ν₀ ∧
      ‖∫ t in Ω ∩ {t | 1 ≤ ideleNorm F t}, c g t * theta Ψ (gone g) (t * e g) * ((ideleNorm F t : ℝ) : ℂ) ^ s' ∂ν₀‖ ≤
        ∫ t in Ω ∩ {t | 1 ≤ ideleNorm F t}, ‖c g t * theta Ψ (gone g) (t * e g)‖ * (ideleNorm F t ^ M + ideleNorm F t ^ (-M)) ∂ν₀) := by
  haveI := NumberField.AdeleRing.secondCountableTopology_generalLinearGroup_finTwo F
  obtain ⟨hh, hcont, hdom⟩ := mellin_hyps ν₀ hΩ hΩm hTP hcG e he he1 c hc hct hc1
  exact MeasureTheory.differentiable_and_continuous_integral_mul_cpow_of_eventually_norm_mul_rpow_add_rpow_neg_le
    (ν₀.restrict (Ω ∩ {t | 1 ≤ ideleNorm F t})) (ideleNorm F) measurable_ideleNorm.aemeasurable ideleNorm_pos
    (fun g t => c g t * theta Ψ (gone g) (t * e g)) hh hcont hdom

theorem siegel (hΩ : IsFundamentalDomain (principalUnits F) Ω ν₀) (hΩm : MeasurableSet Ω)
    {Ψ : (Fin 2 → AdeleRing (𝓞 F) F) → ℂ}
    (hTP : ∀ K : Set (AdelicGL2 (𝓞 F) F), IsCompact K → ∀ N : ℕ, ∃ C : ℝ, 0 ≤ C ∧
      ∀ m ∈ K, ∀ t : (AdeleRing (𝓞 F) F)ˣ,
        Summable (fun ξ : Fin 2 → F =>
          ‖Ψ ((t : AdeleRing (𝓞 F) F) • Matrix.vecMul (rowOf F ξ) (m : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)))‖) ∧
        thetaAbs Ψ m t ≤ C * (1 + (ideleNorm F t)⁻¹ ^ 2) * min 1 ((ideleNorm F t)⁻¹ ^ N))
    (hcG : Continuous (thetaG Ψ))
    (e : AdelicGL2 (𝓞 F) F → (AdeleRing (𝓞 F) F)ˣ) (he : Continuous e) (he1 : ∀ g, ideleNorm F (e g) = 1)
    (c : AdelicGL2 (𝓞 F) F → (AdeleRing (𝓞 F) F)ˣ → ℂ) (hc : ∀ t, Continuous fun g => c g t) (hct : ∀ g, Continuous (c g))
    (hc1 : ∀ g t, ‖c g t‖ = 1)
    {cc u : ℝ} (t₀ : AdelicGL2 (𝓞 F) F) (M' : ℝ)
    (hTS : ∃ (A : ℝ) (N : ℕ), 0 ≤ A ∧
      ∀ Ω : Set (AdeleRing (𝓞 F) F)ˣ,
        IsFundamentalDomain
          (Units.map (algebraMap F (AdeleRing (𝓞 F) F) : F →* AdeleRing (𝓞 F) F)).range Ω ν₀ →
      ∀ h ∈ integralWindowedSiegelSet F cc u,
        ideleNorm F (Matrix.GeneralLinearGroup.det (h * t₀)) = 1 →
        IntegrableOn (fun t : (AdeleRing (𝓞 F) F)ˣ => thetaAbs Ψ (h * t₀) t * (ideleNorm F t) ^ M')
          (Ω ∩ {t | 1 ≤ ideleNorm F t}) ν₀ ∧
        ∫ t in Ω ∩ {t | 1 ≤ ideleNorm F t}, thetaAbs Ψ (h * t₀) t * (ideleNorm F t) ^ M' ∂ν₀
          ≤ A * (1 + archHeight F (glArch (𝓞 F) F h)) ^ N) :
    ∃ (A : ℝ) (N : ℕ), 0 ≤ A ∧ ∀ s' : ℂ, |s'.re| ≤ M' → ∀ h ∈ integralWindowedSiegelSet F cc u,
      ‖∫ t in Ω ∩ {t | 1 ≤ ideleNorm F t}, c (h * t₀) t * theta Ψ (gone (h * t₀)) (t * e (h * t₀)) *
          ((ideleNorm F t : ℝ) : ℂ) ^ s' ∂ν₀‖ ≤ A * (1 + archHeight F (glArch (𝓞 F) F h)) ^ N := by
  obtain ⟨A, N, hA, hTS'⟩ := hTS
  obtain ⟨-, -, hstrip⟩ := mellin ν₀ hΩ hΩm hTP hcG e he he1 c hc hct hc1
  refine ⟨2 * A, N, by positivity, fun s' hs' h hh => ?_⟩
  set g : AdelicGL2 (𝓞 F) F := h * t₀ with hgdef
  set h' : AdelicGL2 (𝓞 F) F := centralScalar (𝓞 F) F (zed g)⁻¹ * h with hh'def
  have hh' : h' ∈ integralWindowedSiegelSet F cc u := centralScalar_mul_mem_siegel (zed_inv_snd g) hh
  have hg1 : gone g = h' * t₀ := gone_mul h t₀
  have hdet : ideleNorm F (Matrix.GeneralLinearGroup.det (h' * t₀)) = 1 := by rw [← hg1]; exact ideleNorm_det_gone g
  have hH : archHeight F (glArch (𝓞 F) F h') = archHeight F (glArch (𝓞 F) F h) := archHeight_centralScalar_mul _ _

  set d : (AdeleRing (𝓞 F) F)ˣ := (e g)⁻¹ with hddef
  have hd1 : ideleNorm F d = 1 := by rw [hddef, ideleNorm_inv, he1, inv_one]
  set Ω'' : Set (AdeleRing (𝓞 F) F)ˣ := (fun u : (AdeleRing (𝓞 F) F)ˣ => u * d) ⁻¹' Ω with hΩ''def
  have hΩ'' : IsFundamentalDomain (principalUnits F) Ω'' ν₀ := isFundamentalDomain_translate ν₀ hΩ d
  obtain ⟨hGint, hGle⟩ := hTS' Ω'' hΩ'' h' hh' hdet

  set G : (AdeleRing (𝓞 F) F)ˣ → ℝ := fun u => thetaAbs Ψ (h' * t₀) u * (ideleNorm F u) ^ M' with hGdef
  have hpre : (fun u : (AdeleRing (𝓞 F) F)ˣ => u * d) ⁻¹' (Ω ∩ {t | 1 ≤ ideleNorm F t}) = Ω'' ∩ {t | 1 ≤ ideleNorm F t} :=
    translate_inter_upper hd1
  have hGt : ∀ t, G (t * d⁻¹) = thetaAbs Ψ (gone g) (t * e g) * (ideleNorm F t) ^ M' := by
    intro t; rw [hGdef, hg1, hddef, inv_inv]; simp only; rw [ideleNorm_mul, he1, mul_one]
  have hGint' : IntegrableOn (fun t => thetaAbs Ψ (gone g) (t * e g) * (ideleNorm F t) ^ M')
      (Ω ∩ {t | 1 ≤ ideleNorm F t}) ν₀ := by
    have h1 := (integrableOn_translate_iff_real ν₀ (Ω := Ω ∩ {t | 1 ≤ ideleNorm F t}) d G).mp (by rw [hpre]; exact hGint)
    refine h1.congr (ae_of_all _ fun t => hGt t)
  have hGeq : ∫ t in Ω ∩ {t | 1 ≤ ideleNorm F t}, thetaAbs Ψ (gone g) (t * e g) * (ideleNorm F t) ^ M' ∂ν₀ =
      ∫ u in Ω'' ∩ {t | 1 ≤ ideleNorm F t}, G u ∂ν₀ := by
    rw [← hpre, setIntegral_translate_real ν₀ d G]
    exact integral_congr_ae (ae_of_all _ fun t => (hGt t).symm)

  obtain ⟨hmomint, hmom⟩ := hstrip g M' s' hs'
  have hcmp : ∫ t in Ω ∩ {t | 1 ≤ ideleNorm F t},
        ‖c g t * theta Ψ (gone g) (t * e g)‖ * (ideleNorm F t ^ M' + ideleNorm F t ^ (-M')) ∂ν₀ ≤
      ∫ t in Ω ∩ {t | 1 ≤ ideleNorm F t}, 2 * (thetaAbs Ψ (gone g) (t * e g) * (ideleNorm F t) ^ M') ∂ν₀ := by
    refine integral_mono_ae hmomint (hGint'.const_mul 2) ?_
    refine ae_restrict_of_forall_mem (hΩm.inter measurableSet_one_le) fun t ht => ?_
    have ht1 : 1 ≤ ideleNorm F t := ht.2
    obtain ⟨C, -, hb⟩ := hTP {gone g} isCompact_singleton 0
    have hsum := (hb (gone g) (mem_singleton _) (t * e g)).1
    show ‖c g t * theta Ψ (gone g) (t * e g)‖ * (ideleNorm F t ^ M' + ideleNorm F t ^ (-M')) ≤
      2 * (thetaAbs Ψ (gone g) (t * e g) * ideleNorm F t ^ M')
    rw [norm_mul, hc1, one_mul]
    calc ‖theta Ψ (gone g) (t * e g)‖ * (ideleNorm F t ^ M' + ideleNorm F t ^ (-M'))
        ≤ thetaAbs Ψ (gone g) (t * e g) * (2 * ideleNorm F t ^ |M'|) :=
          mul_le_mul (norm_theta_le_thetaAbs hsum) (pow_add_pow_neg_le ht1) (by positivity) (thetaAbs_nonneg _ _ _)
      _ = 2 * (thetaAbs Ψ (gone g) (t * e g) * ideleNorm F t ^ M') := by
          rw [abs_of_nonneg (le_trans (abs_nonneg _) hs')]; ring
  rw [integral_const_mul, hGeq] at hcmp
  calc ‖∫ t in Ω ∩ {t | 1 ≤ ideleNorm F t}, c g t * theta Ψ (gone g) (t * e g) * ((ideleNorm F t : ℝ) : ℂ) ^ s' ∂ν₀‖
      ≤ 2 * ∫ u in Ω'' ∩ {t | 1 ≤ ideleNorm F t}, G u ∂ν₀ := hmom.trans hcmp
    _ ≤ 2 * (A * (1 + archHeight F (glArch (𝓞 F) F h')) ^ N) := by gcongr
    _ = 2 * A * (1 + archHeight F (glArch (𝓞 F) F h)) ^ N := by rw [hH]; ring

end Family

section Assembly

variable [MeasurableSpace (AdeleRing (𝓞 F) F)ˣ] [BorelSpace (AdeleRing (𝓞 F) F)ˣ]

theorem godementEisenstein_centralScalar_mul (ν₀ : Measure (AdeleRing (𝓞 F) F)ˣ) [ν₀.IsHaarMeasure]
    (μ ν : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ) (hα : ∀ x, 0 < ((moduleChar F x : ℝˣ) : ℝ))
    (Φ : (Fin 2 → AdeleRing (𝓞 F) F) → ℂ) (s : ℂ) (z : (AdeleRing (𝓞 F) F)ˣ) (g : AdelicGL2 (𝓞 F) F) :
    godementEisenstein F ν₀ μ ν (moduleChar F) hα Φ s (centralScalar (𝓞 F) F z * g) =
      (((μ * ν) z : ℂˣ) : ℂ) * godementEisenstein F ν₀ μ ν (moduleChar F) hα Φ s g := by
  have hind := AutomorphicForm.isInducedSection_godementSection_of_forall_coe_eq_ideleNorm F ν₀ μ ν (moduleChar F) hα
    (val_moduleChar_apply F) Φ s
  have hz : ∀ x : AdelicGL2 (𝓞 F) F, godementSection F ν₀ μ ν (moduleChar F) hα Φ s (centralScalar (𝓞 F) F z * x) =
      (((μ * ν) z : ℂˣ) : ℂ) * godementSection F ν₀ μ ν (moduleChar F) hα Φ s x := by
    intro x
    rw [isInducedSection_centralScalar_mul hind z x, ← Units.val_mul, etaFst_mul_etaSnd, coe_mul_apply, Units.val_mul]
  rw [godementEisenstein_def, godementEisenstein_def, hz, mul_add, ← tsum_mul_left]
  congr 1
  refine tsum_congr fun ξ => ?_
  rw [← hz, ← mul_assoc, ← centralScalar_comm, mul_assoc]

end Assembly

section Factor

variable (μ ν : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ)

def cfac (g : AdelicGL2 (𝓞 F) F) : ℂ :=
  (((μ * ν) (zed g) : ℂˣ) : ℂ) * ((μ (Matrix.GeneralLinearGroup.det (gone g)) : ℂˣ) : ℂ)

variable {μ ν}

theorem norm_cfac (hμ : IsUnitaryChar (𝓞 F) F μ) (hν : IsUnitaryChar (𝓞 F) F ν) (g : AdelicGL2 (𝓞 F) F) : ‖cfac μ ν g‖ = 1 := by
  rw [cfac, norm_mul, isUnitaryChar_mul hμ hν _, hμ _, one_mul]

theorem continuous_cfac (hμc : Continuous fun x : (AdeleRing (𝓞 F) F)ˣ => ((μ x : ℂˣ) : ℂ))
    (hνc : Continuous fun x : (AdeleRing (𝓞 F) F)ˣ => ((ν x : ℂˣ) : ℂ)) : Continuous (cfac μ ν) :=
  ((continuous_coe_mul hμc hνc).comp continuous_zed).mul (hμc.comp (continuous_det.comp continuous_gone))

theorem cfac_eq_of_exc (hα : ∀ x, 0 < ((moduleChar F x : ℝˣ) : ℝ)) {τ : ℝ} (hτ : μ * ν⁻¹ = normPowChar F τ)
    (g : AdelicGL2 (𝓞 F) F) :
    cfac μ ν g = ((μ (Matrix.GeneralLinearGroup.det g) : ℂˣ) : ℂ) *
      ((cpowChar (moduleChar F) hα (-(τ : ℂ) * I / 2) (Matrix.GeneralLinearGroup.det g) : ℂˣ) : ℂ) := by
  set z := zed g with hz
  have hdet : Matrix.GeneralLinearGroup.det g = z * z * Matrix.GeneralLinearGroup.det (gone g) := by
    rw [det_gone, ← hz, ← mul_assoc, show z * z * (z⁻¹ * z⁻¹) = 1 by group, one_mul]
  have hν : ((ν z : ℂˣ) : ℂ) = ((μ z : ℂˣ) : ℂ) * ((ideleNorm F z : ℝ) : ℂ) ^ (-((τ : ℂ) * I)) := by
    have h1 : (((μ * ν⁻¹) z : ℂˣ) : ℂ) = ((ideleNorm F z : ℝ) : ℂ) ^ (I * τ) := by rw [hτ, coe_normPowChar_apply]
    rw [coe_mul_apply, coe_inv_apply] at h1
    have hμz : ((μ z : ℂˣ) : ℂ) ≠ 0 := Units.ne_zero _
    have hνz : ((ν z : ℂˣ) : ℂ) ≠ 0 := Units.ne_zero _
    rw [cpow_neg, mul_comm ((τ : ℂ)) I, ← h1]
    field_simp
  rw [cfac, ← hz, coe_mul_apply, hν, hdet, map_mul, map_mul, Units.val_mul, Units.val_mul, cpowChar_apply_val,
    val_moduleChar_apply, ideleNorm_mul, ideleNorm_mul, ideleNorm_det_gone, mul_one, ofReal_mul,
    mul_cpow_ofReal_nonneg (ideleNorm_pos z).le (ideleNorm_pos z).le, ← cpow_add _ _ (ofReal_ideleNorm_ne_zero z)]
  rw [show -(τ : ℂ) * I / 2 + -(τ : ℂ) * I / 2 = -((τ : ℂ) * I) by ring]
  ring

end Factor

section Assembly2

variable [MeasurableSpace (AdeleRing (𝓞 F) F)ˣ] [BorelSpace (AdeleRing (𝓞 F) F)ˣ]
variable [MeasurableSpace (AdeleRing (𝓞 F) F)] [BorelSpace (AdeleRing (𝓞 F) F)]
variable (ν₀ : Measure (AdeleRing (𝓞 F) F)ˣ) (Ω : Set (AdeleRing (𝓞 F) F)ˣ)
variable (μ₁ : Measure (AdeleRing (𝓞 F) F))
variable (ψ : AddChar (AdeleRing (𝓞 F) F) ℂ) (μ ν : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ) (Φ : (Fin 2 → AdeleRing (𝓞 F) F) → ℂ)

def bigR (s : ℂ) (g : AdelicGL2 (𝓞 F) F) : ℂ :=
  cfac μ ν g * (upA ν₀ Ω (μ * ν⁻¹) Φ (gone g) (2 * s + 1) + upB ν₀ Ω (μ * ν⁻¹) (reflectPair ψ μ₁ Φ) (gone g) (1 - 2 * s))

def bigR' (s : ℂ) (g : AdelicGL2 (𝓞 F) F) : ℂ :=
  cfac μ ν g * (upB ν₀ Ω (μ * ν⁻¹) (reflectPair ψ μ₁ Φ) (gone g) (2 * s + 1) + upA ν₀ Ω (μ * ν⁻¹) Φ (gone g) (1 - 2 * s))

omit [MeasurableSpace (AdeleRing (𝓞 F) F)ˣ] [BorelSpace (AdeleRing (𝓞 F) F)ˣ]
  [MeasurableSpace (AdeleRing (𝓞 F) F)] [BorelSpace (AdeleRing (𝓞 F) F)] in
theorem abs_re_le {σ₁ σ₂ : ℝ} {s : ℂ} (h1 : σ₁ ≤ s.re) (h2 : s.re ≤ σ₂) :
    |(2 * s + 1).re| ≤ 2 * max |σ₁| |σ₂| + 1 ∧ |(1 - 2 * s).re| ≤ 2 * max |σ₁| |σ₂| + 1 := by
  have hs : |s.re| ≤ max |σ₁| |σ₂| := abs_le_max_abs_abs h1 h2
  have e1 : (2 * s + 1).re = 2 * s.re + 1 := by simp
  have e2 : (1 - 2 * s).re = 1 - 2 * s.re := by simp
  rw [e1, e2]
  constructor
  · calc |2 * s.re + 1| ≤ |2 * s.re| + |1| := abs_add_le _ _
      _ = 2 * |s.re| + 1 := by rw [abs_mul, abs_two, abs_one]
      _ ≤ 2 * max |σ₁| |σ₂| + 1 := by linarith
  · calc |1 - 2 * s.re| ≤ |1| + |2 * s.re| := abs_sub _ _
      _ = 2 * |s.re| + 1 := by rw [abs_mul, abs_two, abs_one]; ring
      _ ≤ 2 * max |σ₁| |σ₂| + 1 := by linarith

end Assembly2

end LanglandsTunnell.RankinSelberg.GodementAssembly
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_exists_forall_summable_norm_godementSection_bruhat_one_one_rat.LanglandsTunnell P2MW.S_LanglandsTunnell_RankinSelberg_exists_forall_summable_norm_godementSection_bruhat_one_one_rat.LanglandsTunnell.RankinSelberg P2MW.S_LanglandsTunnell_RankinSelberg_exists_forall_summable_norm_godementSection_bruhat_one_one_rat.LanglandsTunnell.RankinSelberg.GodementAssembly"
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_exists_forall_summable_norm_godementSection_bruhat_one_one_rat.LanglandsTunnell P2MW.S_LanglandsTunnell_RankinSelberg_exists_forall_summable_norm_godementSection_bruhat_one_one_rat.LanglandsTunnell.RankinSelberg"
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_exists_forall_summable_norm_godementSection_bruhat_one_one_rat.LanglandsTunnell"

end
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_exists_forall_summable_norm_godementSection_bruhat_one_one_rat.LanglandsTunnell P2MW.S_LanglandsTunnell_RankinSelberg_exists_forall_summable_norm_godementSection_bruhat_one_one_rat.LanglandsTunnell.RankinSelberg P2MW.S_LanglandsTunnell_RankinSelberg_exists_forall_summable_norm_godementSection_bruhat_one_one_rat.LanglandsTunnell.RankinSelberg.GodementAssembly"

theorem Ws46.summable_norm_of_summable_complex {ι : Type*} {f : ι → ℂ} (h : Summable f) :
    Summable (fun i => ‖f i‖) := by
  have hre : Summable fun i => (f i).re := Complex.reCLM.summable h
  have him : Summable fun i => (f i).im := Complex.imCLM.summable h
  have hre' := summable_abs_iff.mpr hre
  have him' := summable_abs_iff.mpr him
  refine Summable.of_nonneg_of_le (fun i => norm_nonneg _) (fun i => ?_) (hre'.add him')
  exact Complex.norm_le_abs_re_add_abs_im (f i)

attribute [local instance] NumberField.AdelicHaar.glBorel NumberField.AdelicHaar.borelSpace_glBorel
  NumberField.AdelicHaar.adeleBorel NumberField.AdelicHaar.borelSpace_adeleBorel
  NumberField.Idele.ideleBorel NumberField.Idele.borelSpace_ideleBorel

open MeasureTheory NumberField NumberField.AdelicHaar NumberField.AdelicLevel NumberField.AdelicBox NumberField.AdelicFourier IsDedekindDomain
open AutomorphicForm AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering AutomorphicForm.SiegelCoordinates
p2m_open "LanglandsTunnell P2MW.S_LanglandsTunnell_RankinSelberg_exists_forall_summable_norm_godementSection_bruhat_one_one_rat.LanglandsTunnell LanglandsTunnell.RankinSelberg P2MW.S_LanglandsTunnell_RankinSelberg_exists_forall_summable_norm_godementSection_bruhat_one_one_rat.LanglandsTunnell.RankinSelberg RSCarrier UnramifiedWhittaker"

open LanglandsTunnell.RankinSelberg.GodementAssembly in
theorem solution
    (c u d₁ d₂ : ℝ) (T : Finset (AdelicGL2 (𝓞 ℚ) ℚ))
    (S : Finset (HeightOneSpectrum (𝓞 ℚ)))
    (φ φ' : AdelicGL2 (𝓞 ℚ) ℚ → ℂ)
    (WA WA' FA : GL (Fin 2) ℝ → ℂ) (Wf Wf' Ff : finiteAdelicGL2Subgroup ℚ → ℂ)
    (Φ : (Fin 2 → AdeleRing (𝓞 ℚ) ℚ) → ℂ) (P : ℝ → ℝ) (x₀ : ℝ)
    (D : Set (AdelicGL2 (𝓞 ℚ) ℚ)) (e₁ e₂ cS uS : ℝ) (tS : Finset (AdelicGL2 (𝓞 ℚ) ℚ))
    (_hφc : Continuous φ) (_hφ'c : Continuous φ')
    (_hφd : IsRapidlyDecreasingOnSiegelSets ℚ φ) (_hφ'd : IsRapidlyDecreasingOnSiegelSets ℚ φ')
    (_hφG : ∀ (γ : GL (Fin 2) ℚ) (g : AdelicGL2 (𝓞 ℚ) ℚ), φ (globalPoints (𝓞 ℚ) ℚ γ * g) = φ g)
    (_hφ'G : ∀ (γ : GL (Fin 2) ℚ) (g : AdelicGL2 (𝓞 ℚ) ℚ), φ' (globalPoints (𝓞 ℚ) ℚ γ * g) = φ' g)
    (_hΦ : Φ ∈ schwartzBruhat2 ℚ)
    (_he₁ : 0 < e₁) (_he : e₁ < e₂) (_hcS : 0 < cS) (_hDm : MeasurableSet D)
    (_hDμ : adelicGLHaar (Fin 2) (𝓞 ℚ) ℚ D < ⊤)
    (_hDs : D ⊆ {g | TateGlobal.ideleNorm ℚ (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc e₁ e₂})
    (_hDS : D ⊆ ⋃ t ∈ tS, (· * t) '' integralWindowedSiegelSet ℚ cS uS)
    (_hW : ∀ g : AdelicGL2 (𝓞 ℚ) ℚ,
      whittakerCoefficient ℚ (productionPinsOf ℚ (⋃ x ∈ T, (· * x) '' centreCutSiegelSet ℚ c u d₁ d₂)
            (fun N => levelOne (𝓞 ℚ) ℚ N ⊓ finiteAdelicGL2Subgroup ℚ) (fun v => heckeGen (𝓞 ℚ) ℚ v) (adelicBox ℚ)) NumberField.StandardAddChar.psiQ φ 1 g = WA (ratArchGL2 g) * Wf (finFactor g))
    (_hW' : ∀ g : AdelicGL2 (𝓞 ℚ) ℚ,
      whittakerCoefficient ℚ (productionPinsOf ℚ (⋃ x ∈ T, (· * x) '' centreCutSiegelSet ℚ c u d₁ d₂)
            (fun N => levelOne (𝓞 ℚ) ℚ N ⊓ finiteAdelicGL2Subgroup ℚ) (fun v => heckeGen (𝓞 ℚ) ℚ v) (adelicBox ℚ)) NumberField.StandardAddChar.psiQ⁻¹ φ' 1 g = WA' (ratArchGL2 g) * Wf' (finFactor g))
    (_hΦsplit : ∀ g : AdelicGL2 (𝓞 ℚ) ℚ, Φ (bottomRowVec ℚ g 1) = FA (ratArchGL2 g) * Ff (finFactor g))
    (_hFA : ∀ g : GL (Fin 2) ℝ, FA g = Complex.exp (-(Real.pi *
        (((g : Matrix (Fin 2) (Fin 2) ℝ) 1 0) ^ 2 + ((g : Matrix (Fin 2) (Fin 2) ℝ) 1 1) ^ 2) : ℝ)))
    (_hT : ∀ (a₁ a₂ : ℝ) (h₁ : a₁ ≠ 0) (h₂ : 0 < a₂),
      WA (upperUnit a₁ 0 a₂ h₁ h₂.ne') * WA' (upperUnit a₁ 0 a₂ h₁ h₂.ne') = ((P (a₁ / a₂) : ℝ) : ℂ))
    (_hP0 : ∀ y : ℝ, 0 ≤ P y)
    (_hPint : ∀ σ' : ℝ, x₀ < σ' → Integrable (fun y : ℝ => P y * |y| ^ (σ' - 2)))
    (_hWfm : Measurable Wf) (_hWf'm : Measurable Wf') (_hFfm : Measurable Ff)
    (_harch : @Measurable (GL (Fin 2) ℝ) ℂ (borel _) _ WA ∧ @Measurable (GL (Fin 2) ℝ) ℂ (borel _) _ WA' ∧ Measurable P ∧
      (∀ n ∈ realUnipotent, ∀ g : GL (Fin 2) ℝ, WA (n * g) * WA' (n * g) = WA g * WA' g) ∧
      (∀ κ' ∈ rowIsometrySubgroup ℝ, Matrix.GeneralLinearGroup.det κ' = 1 →
        ∀ g : GL (Fin 2) ℝ, WA (g * κ') * WA' (g * κ') = WA g * WA' g))
    (ϖ : ∀ v : HeightOneSpectrum (𝓞 ℚ), v.adicCompletionIntegers ℚ)
    (hπ : ∀ v : HeightOneSpectrum (𝓞 ℚ), v ∉ S →
      algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) (ϖ v) ≠ 0)
    (lam om lam' om' : HeightOneSpectrum (𝓞 ℚ) → ℂ) (κ : ℝ)
    (_hfin :
      (∀ v : HeightOneSpectrum (𝓞 ℚ), v ∉ S →
        Valued.v (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) (ϖ v)) = WithZero.exp (-1 : ℤ)) ∧
      (∀ v : HeightOneSpectrum (𝓞 ℚ), v ∉ S →
        ‖lam v‖ ≤ ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ^ κ ∧ ‖om v‖ ≤ ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ^ κ ∧
        ‖lam' v‖ ≤ ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ^ κ ∧ ‖om' v‖ ≤ ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ^ κ) ∧
      (∀ (n : RSCarrier.finUnipotent) (g : finiteAdelicGL2Subgroup ℚ),
        Wf ((n : finiteAdelicGL2Subgroup ℚ) * g) * (Wf' ((n : finiteAdelicGL2Subgroup ℚ) * g) * Ff ((n : finiteAdelicGL2Subgroup ℚ) * g)) =
          Wf g * (Wf' g * Ff g)) ∧
      (∀ v : HeightOneSpectrum (𝓞 ℚ), v ∉ S → ∃ ψ : AddChar (v.adicCompletion ℚ) ℂ,
        (∀ r : v.adicCompletionIntegers ℚ, ψ (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) r) = 1) ∧
        (∃ r : v.adicCompletionIntegers ℚ,
          ψ (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) r /
            algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) (ϖ v)) ≠ 1) ∧
        ∀ (x : v.adicCompletion ℚ) (g : AdelicGL2 (𝓞 ℚ) ℚ),
          Wf (finFactor (placeEmbed ℚ v (unipotent x) * g)) = ψ x * Wf (finFactor g)) ∧
      (∀ v : HeightOneSpectrum (𝓞 ℚ), v ∉ S → ∀ (x : GL (Fin 2) (v.adicCompletion ℚ)) (g : AdelicGL2 (𝓞 ℚ) ℚ),
        x ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ v ⊤ → Wf (finFactor (g * placeEmbed ℚ v x)) = Wf (finFactor g)) ∧
      (∀ v : HeightOneSpectrum (𝓞 ℚ), v ∉ S → ∀ (x : GL (Fin 2) (v.adicCompletion ℚ)) (g : AdelicGL2 (𝓞 ℚ) ℚ),
        x ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ v ⊤ →
          Wf' (finFactor (g * placeEmbed ℚ v x)) * Ff (finFactor (g * placeEmbed ℚ v x)) = Wf' (finFactor g) * Ff (finFactor g)) ∧
      (∀ v : HeightOneSpectrum (𝓞 ℚ), ∀ hv : v ∉ S, ∀ (g : AdelicGL2 (𝓞 ℚ) ℚ) (m n : ℤ), localAt ℚ v g = 1 →
        Wf (finFactor (g * placeEmbed ℚ v
              (diagZ (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) (ϖ v)) (hπ v hv) m *
                scalarPi (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) (ϖ v)) (hπ v hv) ^ n))) *
          (Wf' (finFactor (g * placeEmbed ℚ v
              (diagZ (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) (ϖ v)) (hπ v hv) m *
                scalarPi (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) (ϖ v)) (hπ v hv) ^ n))) *
            Ff (finFactor (g * placeEmbed ℚ v
              (diagZ (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) (ϖ v)) (hπ v hv) m *
                scalarPi (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) (ϖ v)) (hπ v hv) ^ n)))) =
        (if 0 ≤ m ∧ 0 ≤ n then
          (om v * om' v) ^ n.toNat *
            heckeRecursionSeq ((Ideal.absNorm v.asIdeal : ℕ) : ℂ) (lam v) (om v) m.toNat *
            heckeRecursionSeq ((Ideal.absNorm v.asIdeal : ℕ) : ℂ) (lam' v) (om' v) m.toNat
         else 0) * (Wf (finFactor g) * (Wf' (finFactor g) * Ff (finFactor g)))))
    (_hsupp :
      (∃ (Cpt : Set (finiteAdelicGL2Subgroup ℚ)) (B₀ : ℝ), IsCompact Cpt ∧
        (∀ g : finiteAdelicGL2Subgroup ℚ, ‖Wf g * (Wf' g * Ff g)‖ ≤ B₀) ∧
        ∀ g : finiteAdelicGL2Subgroup ℚ,
          (∀ v : HeightOneSpectrum (𝓞 ℚ), v ∉ S →
            ∃ n' ∈ (AutomorphicForm.unipotentGL2Hom (R := v.adicCompletion ℚ)).range,
              ∃ k' ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ v ⊤, localAt ℚ v (g : AdelicGL2 (𝓞 ℚ) ℚ) = n' * k') →
          Wf g * (Wf' g * Ff g) ≠ 0 →
            ∃ (n : RSCarrier.finUnipotent) (h : finiteAdelicGL2Subgroup ℚ), h ∈ Cpt ∧
              ∀ v : HeightOneSpectrum (𝓞 ℚ), v ∈ S →
                localAt ℚ v ((((n : finiteAdelicGL2Subgroup ℚ) * g : finiteAdelicGL2Subgroup ℚ)) : AdelicGL2 (𝓞 ℚ) ℚ) =
                  localAt ℚ v (h : AdelicGL2 (𝓞 ℚ) ℚ)))
    :
    letI : MeasurableSpace (GL (Fin 2) ℝ) := borel _
    ∃ σd : ℝ, ∀ s : ℂ, σd < s.re →
      ∀ (ν₀ : Measure (AdeleRing (𝓞 ℚ) ℚ)ˣ) [ν₀.IsHaarMeasure]
        (μf : Measure (finiteAdelicGL2Subgroup ℚ)) [μf.IsHaarMeasure]
        (μNArch : Measure realUnipotent) [μNArch.IsHaarMeasure]
        (μNFin : Measure finUnipotent) [μNFin.IsHaarMeasure],
      (∀ g ∈ D, Summable fun ξ : ℚ =>
        ‖godementSection ℚ ν₀ 1 1 (moduleChar ℚ) (moduleChar_pos ℚ) Φ (s - 1 / 2)
          (adelicWeyl (𝓞 ℚ) ℚ * unipotentGL2 (algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ) ξ) * g)‖) := by
  refine ⟨1, fun s hs ν₀ _ μf _ μNArch _ μNFin _ g _ => ?_⟩

  obtain ⟨Ω, hΩm, hΩall⟩ :=
    NumberField.TateGlobal.exists_measurableSet_forall_isFundamentalDomain_range_unitsMap_algebraMap ℚ
  have hΩ : IsFundamentalDomain (principalUnits ℚ) Ω ν₀ := hΩall ν₀
  have hΦc : Continuous Φ :=
    (NumberField.AdelicFourier.continuous_integrable_comp_vecMul_mem_and_bottomRowVec_mem_schwartzBruhat_of_mem_schwartzBruhat2
      ℚ Φ _hΦ).1
  have TPΦ := NumberField.AdelicFourier.exists_forall_tsum_norm_apply_smul_vecMul_le_and_continuous_tsum_of_mem_schwartzBruhat2 ℚ _hΦ
  have hχu : IsUnitaryChar (𝓞 ℚ) ℚ ((1 : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ) * 1⁻¹) := fun x => by simp
  set s' : ℂ := s - 1 / 2 with hs'
  have hre : 2 < (2 * s' + 1).re := by
    rw [hs']; simp; linarith
  have hreN : (2 * s' + 1).re < ((⌈(2 * s' + 1).re⌉₊ + 1 : ℕ) : ℝ) := by
    have := Nat.le_ceil ((2 * s' + 1).re); push_cast; linarith
  obtain ⟨C₁, hC₁, hb₁⟩ := TPΦ.1 {g} isCompact_singleton (⌈(2 * s' + 1).re⌉₊ + 1)
  have habs := lintegral_thetaAbs_lt_top ν₀ hΩ hΩm hC₁ hre hreN
    (fun t => (hb₁ g (Set.mem_singleton g) t).1) (fun t => (hb₁ g (Set.mem_singleton g) t).2) hχu
  have hU := AutomorphicForm.summable_godementSection_and_bruhatSeries_eq_mul_setIntegral_tsum_of_lintegral_tsum_enorm_lt_top
    ℚ ν₀ Ω hΩ 1 1 (fun _ => rfl) (fun _ => rfl)
    (by simp only [MonoidHom.one_apply, Units.val_one]; exact continuous_const)
    (by simp only [MonoidHom.one_apply, Units.val_one]; exact continuous_const)
    (moduleChar ℚ) (moduleChar_pos ℚ) Φ hΦc s' g habs
  exact Ws46.summable_norm_of_summable_complex hU.1

end S_LanglandsTunnell_RankinSelberg_exists_forall_summable_norm_godementSection_bruhat_one_one_rat
end P2MW
export P2MW.S_LanglandsTunnell_RankinSelberg_exists_forall_summable_norm_godementSection_bruhat_one_one_rat (solution)
