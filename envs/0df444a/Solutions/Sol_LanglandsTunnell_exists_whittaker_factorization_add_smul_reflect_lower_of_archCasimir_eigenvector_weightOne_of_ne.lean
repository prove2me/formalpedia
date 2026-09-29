-- Prove2me | solution 1 for LanglandsTunnell.exists_whittaker_factorization_add_smul_reflect_lower_of_archCasimir_eigenvector_weightOne_of_ne
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.670037+00:00
-- url     : https://prove2.me/submissions/6d286748-4ab4-5d0f-917c-a1c31d7ab6a7

import Definitions.Def_AutomorphicForm_IsotypicCuspSpace
import Definitions.Def_AutomorphicForm_ArchWeightCharTransport
import Definitions.Def_AutomorphicForm_FactorizableTestFn
import Definitions.Def_AutomorphicForm_WhittakerCoefficient
import Definitions.Def_LanglandsTunnell_ConverseData
import Definitions.Def_AutomorphicForm_ArchDerivCasimir
import Definitions.Def_AutomorphicForm_RightConvolution
import Definitions.Def_AutomorphicForm_AdelicLsXi
import Definitions.Def_AutomorphicForm_SmoothAutomorphicFnAt
import Definitions.Def_AutomorphicForm_SiegelCovering
import Mathlib.Analysis.MellinTransform
import Mathlib.Tactic.Module
import Theorems.Thm_AutomorphicForm_isArchSmoothAt_reflectedLowering_and_archCasimirAt_eq_and_reflectedLowering_reflectedLowering_eq_smul
import Theorems.Thm_AutomorphicForm_exists_rightConv_eq_self_and_isIsotypicCuspFormAt_add_smul_archDerivAt_and_whittakerCoefficient_bounds_of_mem_archCutSubmodule
import Theorems.Thm_AutomorphicForm_whittakerCoefficient_torus_peel_ode_growth_and_separation_of_isIsotypicCuspFormAt_of_archCasimirAt_eq_smul
import Theorems.Thm_LanglandsTunnell_isArchSmoothAt_whittakerCoefficient_and_archDerivAt_comm
import Theorems.Thm_AutomorphicForm_isKfSmooth_rightConv
import Theorems.Thm_LanglandsTunnell_exists_mellin_whittakerProfile_eq_archFactor_of_whittaker_ode_weightOne
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LanglandsTunnell_exists_whittaker_factorization_add_smul_reflect_lower_of_archCasimir_eigenvector_weightOne_of_ne
p2m_attr_erase "instance" "IsDedekindDomain.HeightOneSpectrum.Extension.instAlgebraSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnder IsDedekindDomain.HeightOneSpectrum.Extension.instAlgebraSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnder_1 IsDedekindDomain.HeightOneSpectrum.instMulActionHomClassAlgHomTensorProductAdicCompletionForallValEqUnder_definitions IsDedekindDomain.HeightOneSpectrum.Extension.instAlgebraAdicCompletionValEqUnder IsDedekindDomain.HeightOneSpectrum.adicCompletion.instFiniteForallValEqUnderOfFiniteDimensional_definitions IsDedekindDomain.HeightOneSpectrum.instIsBiscalarSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersTensorProductCoeAlgHomTensorAdicCompletionIntegersTo IsDedekindDomain.HeightOneSpectrum.Extension.instContinuousSMulAdicCompletionValEqUnder IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsModuleTopology IsDedekindDomain.HeightOneSpectrum.Extension.instFiniteSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnderOfFiniteDimensional IsDedekindDomain.HeightOneSpectrum.adicCompletion.instFiniteValEqUnderOfFiniteDimensional_definitions instIsBiscalarTensorProductCoeAlgHomBaseChange_of_algebraMap IsDedekindDomain.HeightOneSpectrum.instIsScalarTowerSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnder_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsModuleTopologyPi IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions Submodule.instIsTopologicalModuleSubtypeMem Pi.instTopologicalModule IsTopologicalModule.toContinuousSMul IsTopologicalModule.toContinuousAdd instFunLike SemialgHomClass.toSemilinearMapClass instCoeTCSemialgHom SemialgHomClass.toRingHomClass SemialgHomClass.instSemialgHom FLT.InfiniteAdeleBaseChange.uniqueSelfExtension NumberField.InfinitePlace.RamifiedExtension.instCoeExtension NumberField.InfinitePlace.UnramifiedExtension.instCoeExtension instCountableOfNumberField_definitions RestrictedProduct.SecondCountableTopology_of_principal instCountableElemSetSetsCofinite_definitions AutomorphicForm.compactSpace_maximalCompactAway AutomorphicForm.compactSpace_adelicMaximalCompact AutomorphicForm.isProbabilityMeasure_maximalCompactHaar AutomorphicForm.isHaarMeasure_maximalCompactHaar AutomorphicForm.compactSpace_maximalCompactAt AutomorphicForm.isProbabilityMeasure_maximalCompactAwayHaar"
p2m_attr_erase "instance" "AutomorphicForm.isHaarMeasure_maximalCompactAwayHaar AutomorphicForm.isProbabilityMeasure_maximalCompactAtHaar AutomorphicForm.isHaarMeasure_maximalCompactAtHaar instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions"
p2m_attr_erase "simp" "AutomorphicForm.mem_borelSubgroup_iff AutomorphicForm.borelDiagFst_apply_val AutomorphicForm.borelDiagSnd_apply_val SemialgHom.baseChange_of_algebraMap_tmul_left SemialgHom.baseChangeRightOfAlgebraMap_apply Pi.semialgHomPi_apply Pi.semialgHom_apply Module.Basis.rightBaseChange_apply LinearEquiv.coe_mulLeft LinearEquiv.coe_mulRight WithVal.semialgebraMap_toFun_ofVal Module.Basis.rightBaseChange_repr IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers.tensorCoe_tmul IsDedekindDomain.HeightOneSpectrum.tensorAdicCompletionIntegersTo_tmul SemialgHom.baseChangeRightOfAlgebraMap_coe IsDedekindDomain.HeightOneSpectrum.adicCompletion.integerBaseChangeLinearEquiv_tmul_apply SemialgHom.baseChange_of_algebraMap_tmul_right IsLocalization.map_moduleTensorEquiv_symm_tmul IsLocalization.leftModuleTensorEquiv_apply IsLocalization.moduleLid_symm_apply IsLocalization.leftModuleTensorEquiv_symm_apply IsLocalization.map_moduleTensorEquiv_tmul IsModuleTopology.continuousLinearEquiv_apply AlgEquiv.extendScalars_symm_apply IsModuleTopology.Module.Basis.equivFun_homeo_symm_apply IsModuleTopology.Module.Basis.equivFun_homeo_apply IsModuleTopology.continuousAlgEquivOfIsBiscalar_apply AlgEquiv.extendScalars_apply IsModuleTopology.continuousLinearEquiv_symm_apply SemialgHom.restrictScalars_toFun SemialgHom.mk.sizeOf_spec SemialgHom.mk.injEq SemialgHom.coe_coe coe_mk TensorProduct.RightActions.smul_def TensorProduct.RightActions.Module.TensorProduct.comm_symm_apply_tmul TensorProduct.RightActions.LinearMap.baseChange_id TensorProduct.RightActions.algebraMap_eval TensorProduct.RightActions.Module.TensorProduct.comm_apply_tmul TensorProduct.RightActions.Algebra.TensorProduct.comm_symm_apply_tmul"
p2m_attr_erase "simp" "TensorProduct.RightActions.Algebra.TensorProduct.comm_apply_tmul AutomorphicForm.mem_sigmaCentralizer_iff M4aHerbrand.ArchSemilocal.psiFactor_tmul M4aHerbrand.ArchSemilocal.psi_apply FLT.InfiniteAdeleBaseChange.evalAlgHom_apply FLT.InfiniteAdeleBaseChange.BaseChangeData.mk.sizeOf_spec FLT.InfiniteAdeleBaseChange.tensorPiAlgHom_tmul_apply FLT.InfiniteAdeleBaseChange.collapsePlaces_apply FLT.InfiniteAdeleBaseChange.tensorPiAlgEquiv_tmul_apply FLT.InfiniteAdeleBaseChange.InfinitePlaceData.mk.sizeOf_spec FLT.InfiniteAdeleBaseChange.InfinitePlaceData.mk.injEq FLT.InfiniteAdeleBaseChange.BaseChangeData.mk.injEq ContinuousAddEquiv.restrictedProductPi_apply RestrictedProduct.flatten_homeomorph_apply RestrictedProduct.flatten_homeomorph'_symm_apply ContinuousMulEquiv.restrictedProductPi_symm_apply RestrictedProduct.flatten_homeomorph'_apply RestrictedProduct.flatten_homeomorph_symm_apply ContinuousMulEquiv.restrictedProductPi_apply ContinuousAddEquiv.restrictedProductPi_symm_apply RingEquiv.restrictedProductCongr_symm_apply RingEquiv.restrictedProductCongrRight_apply MulEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductProd_symm_apply_coe Equiv.restrictedProductCongrRight_apply AddEquiv.restrictedProductCongr_apply Equiv.restrictedProductCongrLeft'_symm_apply_apply Equiv.restrictedProductCongr_apply_apply Equiv.restrictedProductCongrLeft_apply_apply RestrictedProduct.flatten_equiv'_apply AddEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductCongr_symm_apply Equiv.restrictedProductCongrRight_symm_apply RestrictedProduct.flatten_equiv'_symm_apply AddEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductCongrLeft'_apply RestrictedProduct.flatten_apply RingEquiv.restrictedProductCongr_apply_apply RingEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductProd_apply"
p2m_attr_erase "simp" "RestrictedProduct.flatten_equiv_apply RestrictedProduct.flatten_equiv_symm_apply LinearEquiv.restrictedProductCongrLeft'_apply RestrictedProduct.not_mem_support RestrictedProduct.mem_structureSubring_iff RestrictedProduct.not_mem_mulSupport RestrictedProduct.support_neg RestrictedProduct.mem_indexSupport_iff RestrictedProduct.mulSupport_inv RestrictedProduct.mapAlongLinearMap_apply AutomorphicForm.CuspidalConstituent.rightRegular_apply LocalGL2.coe_localRepSome LocalGL2.coe_diagPi LocalGL2.coe_localRepInf LocalGL2.coe_localRepSome_inv LocalGL2.coe_unipotentInt LocalGL2.coe_weylInt LocalGL2.coe_diagPi_inv LocalGL2.transposeGL_val LocalGL2.transposeGL_one LocalGL2.swapUnit_val AdelicDock.coe_finEmbed AdelicDock.splice_apply_self AdelicDock.coe_localEmbed AutomorphicForm.CuspidalSpectrum.fdPins_μ AutomorphicForm.CuspidalSpectrum.fdPins_nS AutomorphicForm.CuspidalSpectrum.fdPins_ν AutomorphicForm.CuspidalSpectrum.fdPins_gen AutomorphicForm.CuspidalSpectrum.fdPins_U AutomorphicForm.CuspidalSpectrum.fdPins_D AutomorphicForm.CuspidalSpectrum.fdPins_Z AutomorphicForm.CuspidalSpectrum.mem_detNormSlab AutomorphicForm.CuspidalSpectrum.fdPins_eq AutomorphicForm.CuspidalSpectrum.fdPins_mS AutomorphicForm.fnTwist_zero AutomorphicForm.fnTwist_apply AutomorphicForm.iotaZsqrtdNegTwo_apply"

set_option autoImplicit false

open IsDedekindDomain NumberField MeasureTheory Matrix
open NumberField.AdelicHaar NumberField.AdelicLevel NumberField.AdelicBox
open NumberField.InfinitePlace.Completion
open AutomorphicForm AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering
open LanglandsTunnell LanglandsTunnell.Converse NumberField.TateGlobal
open scoped Real

namespace P2M
namespace WeightOneOdd

noncomputable section

section Operators

variable {F : Type} [Field F] [NumberField F]

private def archRotDerivAt {w : InfinitePlace F} (hw : w.IsReal) (φ : AdelicGL2 (𝓞 F) F → ℂ) : AdelicGL2 (𝓞 F) F → ℂ :=
  archDerivAt hw .E φ - archDerivAt hw .Fm φ

private def archLowerAt {w : InfinitePlace F} (hw : w.IsReal) (φ : AdelicGL2 (𝓞 F) F → ℂ) : AdelicGL2 (𝓞 F) F → ℂ :=
  archDerivAt hw .H φ - Complex.I • (archDerivAt hw .E φ + archDerivAt hw .Fm φ)

private def reflJ : GL (Fin 2) ℝ := UpperHalfPlane.J

private theorem reflJ_coe : (reflJ : Matrix (Fin 2) (Fin 2) ℝ) = !![(-1 : ℝ), 0; 0, 1] := UpperHalfPlane.val_J

private theorem reflJ_mul_reflJ : reflJ * reflJ = 1 := by
  refine Units.ext ?_
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [reflJ_coe, Matrix.mul_apply, Fin.sum_univ_two, Matrix.one_fin_two]

private def reflAt {w : InfinitePlace F} (hw : w.IsReal) (φ : AdelicGL2 (𝓞 F) F → ℂ) : AdelicGL2 (𝓞 F) F → ℂ :=
  fun g => φ (g * archRealGLAt hw reflJ)

private theorem reflAt_reflAt {w : InfinitePlace F} (hw : w.IsReal) (φ : AdelicGL2 (𝓞 F) F → ℂ) :
    reflAt hw (reflAt hw φ) = φ := by
  funext g
  simp only [reflAt]
  rw [mul_assoc, ← map_mul, reflJ_mul_reflJ, map_one, mul_one]

private theorem reflAt_smul {w : InfinitePlace F} (hw : w.IsReal) (c : ℂ) (φ : AdelicGL2 (𝓞 F) F → ℂ) :
    reflAt hw (c • φ) = c • reflAt hw φ := rfl

private theorem reflAt_add {w : InfinitePlace F} (hw : w.IsReal) (φ ψ : AdelicGL2 (𝓞 F) F → ℂ) :
    reflAt hw (φ + ψ) = reflAt hw φ + reflAt hw ψ := rfl

private def archT {w : InfinitePlace F} (hw : w.IsReal) (φ : AdelicGL2 (𝓞 F) F → ℂ) : AdelicGL2 (𝓞 F) F → ℂ :=
  reflAt hw (archLowerAt hw φ)

private theorem archT_eq {w : InfinitePlace F} (hw : w.IsReal) :
    (archT hw : (AdelicGL2 (𝓞 F) F → ℂ) → AdelicGL2 (𝓞 F) F → ℂ) =
      fun (θ : AdelicGL2 (𝓞 F) F → ℂ) (g : AdelicGL2 (𝓞 F) F) =>
        (archDerivAt hw ArchDir.H θ - Complex.I • (archDerivAt hw ArchDir.E θ + archDerivAt hw ArchDir.Fm θ))
          (g * archRealGLAt hw UpperHalfPlane.J) := rfl

private theorem isArchSmoothAt_archLowerAt {w : InfinitePlace F} {hw : w.IsReal} {φ : AdelicGL2 (𝓞 F) F → ℂ}
    (hφ : IsArchSmoothAt hw φ) : IsArchSmoothAt hw (archLowerAt hw φ) :=
  (hφ.archDerivAt .H).sub (((hφ.archDerivAt .E).add (hφ.archDerivAt .Fm)).smul Complex.I)

private theorem archLowerAt_add {w : InfinitePlace F} {hw : w.IsReal} {φ ψ : AdelicGL2 (𝓞 F) F → ℂ}
    (hφ : IsArchSmoothAt hw φ) (hψ : IsArchSmoothAt hw ψ) :
    archLowerAt hw (φ + ψ) = archLowerAt hw φ + archLowerAt hw ψ := by
  simp only [archLowerAt, archDerivAt_add hφ hψ]
  module

private theorem archLowerAt_smul {w : InfinitePlace F} (hw : w.IsReal) (c : ℂ) (φ : AdelicGL2 (𝓞 F) F → ℂ) :
    archLowerAt hw (c • φ) = c • archLowerAt hw φ := by
  simp only [archLowerAt, archDerivAt_smul]
  module

private theorem archT_add {w : InfinitePlace F} {hw : w.IsReal} {φ ψ : AdelicGL2 (𝓞 F) F → ℂ}
    (hφ : IsArchSmoothAt hw φ) (hψ : IsArchSmoothAt hw ψ) : archT hw (φ + ψ) = archT hw φ + archT hw ψ := by
  simp only [archT, archLowerAt_add hφ hψ, reflAt_add]

private theorem archT_smul {w : InfinitePlace F} (hw : w.IsReal) (c : ℂ) (φ : AdelicGL2 (𝓞 F) F → ℂ) :
    archT hw (c • φ) = c • archT hw φ := by
  simp only [archT, archLowerAt_smul, reflAt_smul]

private theorem archT_facts {w : InfinitePlace F} {hw : w.IsReal} {φ : AdelicGL2 (𝓞 F) F → ℂ}
    (hφ : IsArchSmoothAt hw φ) :
    (HasArchCharacterAt₀ F w (archWeightCharAt hw 1) φ → archRotDerivAt hw φ = Complex.I • φ) ∧
      IsArchSmoothAt hw (archT hw φ) ∧
      (HasArchCharacterAt₀ F w (archWeightCharAt hw 1) φ → HasArchCharacterAt₀ F w (archWeightCharAt hw 1) (archT hw φ)) ∧
      (∀ lam : ℂ, archCasimirAt hw φ = lam • φ → archCasimirAt hw (archT hw φ) = lam • archT hw φ) ∧
      (∀ lam : ℂ, archCasimirAt hw φ = lam • φ → HasArchCharacterAt₀ F w (archWeightCharAt hw 1) φ →
        archT hw (archT hw φ) = (1 - 4 * lam) • φ) :=
  isArchSmoothAt_reflectedLowering_and_archCasimirAt_eq_and_reflectedLowering_reflectedLowering_eq_smul F w hw
    (archT hw) (archT_eq hw) φ hφ

private theorem isArchSmoothAt_archT {w : InfinitePlace F} {hw : w.IsReal} {φ : AdelicGL2 (𝓞 F) F → ℂ}
    (hφ : IsArchSmoothAt hw φ) : IsArchSmoothAt hw (archT hw φ) :=
  (archT_facts hφ).2.1

section Eigenvectors

variable {w : InfinitePlace F} {hw : w.IsReal} {φ : AdelicGL2 (𝓞 F) F → ℂ}

private theorem isArchSmoothAt_add_smul_archT (hφ : IsArchSmoothAt hw φ) (c : ℂ) :
    IsArchSmoothAt hw (φ + c • archT hw φ) :=
  hφ.add ((isArchSmoothAt_archT hφ).smul c)

private theorem isArchSmoothAt_archCasimirAt_add_smul_archT (hφ : IsArchSmoothAt hw φ) {lam : ℂ}
    (hlam : archCasimirAt hw φ = lam • φ) (c : ℂ) :
    archCasimirAt hw (φ + c • archT hw φ) = lam • (φ + c • archT hw φ) := by
  rw [archCasimirAt_add hφ ((isArchSmoothAt_archT hφ).smul c), archCasimirAt_smul,
      (archT_facts hφ).2.2.2.1 lam hlam, hlam]
  module

private theorem hasArchCharacterAt₀_add {χ : rowIsometrySubgroup₀ w.Completion →* ℂˣ} {φ ψ : AdelicGL2 (𝓞 F) F → ℂ}
    (h₁ : HasArchCharacterAt₀ F w χ φ) (h₂ : HasArchCharacterAt₀ F w χ ψ) : HasArchCharacterAt₀ F w χ (φ + ψ) := by
  intro k g
  rw [Pi.add_apply, Pi.add_apply, h₁ k g, h₂ k g]
  ring

private theorem hasArchCharacterAt₀_smul {χ : rowIsometrySubgroup₀ w.Completion →* ℂˣ} {φ : AdelicGL2 (𝓞 F) F → ℂ}
    (c : ℂ) (h : HasArchCharacterAt₀ F w χ φ) : HasArchCharacterAt₀ F w χ (c • φ) := by
  intro k g
  rw [Pi.smul_apply, Pi.smul_apply, smul_eq_mul, smul_eq_mul, h k g]
  ring

private theorem isArchSmoothAt_hasArchCharacterAt₀_one_add_smul_archT (hφ : IsArchSmoothAt hw φ)
    (hwt : HasArchCharacterAt₀ F w (archWeightCharAt hw 1) φ) (c : ℂ) :
    HasArchCharacterAt₀ F w (archWeightCharAt hw 1) (φ + c • archT hw φ) :=
  hasArchCharacterAt₀_add hwt (hasArchCharacterAt₀_smul c ((archT_facts hφ).2.2.1 hwt))

private theorem isArchSmoothAt_archT_add_inv_smul_archT (hφ : IsArchSmoothAt hw φ) {lam : ℂ}
    (hlam : archCasimirAt hw φ = lam • φ) (hwt : HasArchCharacterAt₀ F w (archWeightCharAt hw 1) φ) {μ : ℂ}
    (hμ : μ * μ = 1 - 4 * lam) (hμ0 : μ ≠ 0) :
    archT hw (φ + μ⁻¹ • archT hw φ) = μ • (φ + μ⁻¹ • archT hw φ) := by
  rw [archT_add hφ ((isArchSmoothAt_archT hφ).smul μ⁻¹), archT_smul, (archT_facts hφ).2.2.2.2 lam hlam hwt,
      ← hμ, smul_smul,
    inv_mul_cancel_left₀ hμ0, smul_add, smul_smul, mul_inv_cancel₀ hμ0, one_smul, add_comm]

end Eigenvectors

private theorem mul_self_sub_eq_one_sub_four_mul_laplaceEigenvalue (u₁ : ℂ) (a₁ : ZMod 2) (u₂ : ℂ) (a₂ : ZMod 2) :
    (u₁ - u₂) * (u₁ - u₂) =
      1 - 4 * LanglandsTunnell.RealArchParam.laplaceEigenvalue
        (LanglandsTunnell.RealArchParam.principal u₁ a₁ u₂ a₂) := by
  rw [LanglandsTunnell.RealArchParam.laplaceEigenvalue_principal]
  ring

end Operators

section CoefficientIdentities

open MeasureTheory

variable {F : Type} [Field F] [NumberField F]

private theorem whittakerCoefficient_apply_mul (pins : CarrierPins F) (ψ : AddChar (AdeleRing (𝓞 F) F) ℂ)
    (φ : AdelicGL2 (𝓞 F) F → ℂ) (α : F) (g t : AdelicGL2 (𝓞 F) F) :
    whittakerCoefficient F pins ψ φ α (g * t) = whittakerCoefficient F pins ψ (fun h => φ (h * t)) α g := by
  unfold whittakerCoefficient
  simp only [mul_assoc]

private theorem whittakerCoefficient_const_mul (pins : CarrierPins F) (ψ : AddChar (AdeleRing (𝓞 F) F) ℂ) (c : ℂ)
    (φ : AdelicGL2 (𝓞 F) F → ℂ) (α : F) (g : AdelicGL2 (𝓞 F) F) :
    whittakerCoefficient F pins ψ (fun h => c * φ h) α g = c * whittakerCoefficient F pins ψ φ α g := by
  simp only [whittakerCoefficient, mul_assoc, integral_const_mul]

private theorem whittakerCoefficient_smul (pins : CarrierPins F) (ψ : AddChar (AdeleRing (𝓞 F) F) ℂ) (c : ℂ)
    (φ : AdelicGL2 (𝓞 F) F → ℂ) (α : F) (g : AdelicGL2 (𝓞 F) F) :
    whittakerCoefficient F pins ψ (c • φ) α g = c * whittakerCoefficient F pins ψ φ α g :=
  whittakerCoefficient_const_mul pins ψ c φ α g

private theorem whittakerCoefficient_add (pins : CarrierPins F) (ψ : AddChar (AdeleRing (𝓞 F) F) ℂ)
    {φ₁ φ₂ : AdelicGL2 (𝓞 F) F → ℂ} {α : F} {g : AdelicGL2 (𝓞 F) F}
    (h₁ : WhittakerCoefficientIntegrable F pins ψ φ₁ α g) (h₂ : WhittakerCoefficientIntegrable F pins ψ φ₂ α g) :
    whittakerCoefficient F pins ψ (φ₁ + φ₂) α g =
      whittakerCoefficient F pins ψ φ₁ α g + whittakerCoefficient F pins ψ φ₂ α g := by
  unfold WhittakerCoefficientIntegrable at h₁ h₂
  unfold whittakerCoefficient
  simp only [Pi.add_apply, add_mul]
  exact integral_add h₁ h₂

private theorem whittakerCoefficient_sub (pins : CarrierPins F) (ψ : AddChar (AdeleRing (𝓞 F) F) ℂ)
    {φ₁ φ₂ : AdelicGL2 (𝓞 F) F → ℂ} {α : F} {g : AdelicGL2 (𝓞 F) F}
    (h₁ : WhittakerCoefficientIntegrable F pins ψ φ₁ α g) (h₂ : WhittakerCoefficientIntegrable F pins ψ φ₂ α g) :
    whittakerCoefficient F pins ψ (φ₁ - φ₂) α g =
      whittakerCoefficient F pins ψ φ₁ α g - whittakerCoefficient F pins ψ φ₂ α g := by
  unfold WhittakerCoefficientIntegrable at h₁ h₂
  unfold whittakerCoefficient
  simp only [Pi.sub_apply, sub_mul]
  exact integral_sub h₁ h₂

private theorem hasArchCharacterAt₀_whittakerCoefficient (pins : CarrierPins F) (ψ : AddChar (AdeleRing (𝓞 F) F) ℂ)
    {w : InfinitePlace F} {χ : rowIsometrySubgroup₀ w.Completion →* ℂˣ} {φ : AdelicGL2 (𝓞 F) F → ℂ}
    (hφ : HasArchCharacterAt₀ F w χ φ) (α : F) : HasArchCharacterAt₀ F w χ (whittakerCoefficient F pins ψ φ α) := by
  intro k g
  rw [whittakerCoefficient_apply_mul, funext (hφ k), whittakerCoefficient_const_mul]

private theorem whittakerCoefficientIntegrable_sub (pins : CarrierPins F) (ψ : AddChar (AdeleRing (𝓞 F) F) ℂ)
    {φ₁ φ₂ : AdelicGL2 (𝓞 F) F → ℂ} {α : F} {g : AdelicGL2 (𝓞 F) F}
    (h₁ : WhittakerCoefficientIntegrable F pins ψ φ₁ α g) (h₂ : WhittakerCoefficientIntegrable F pins ψ φ₂ α g) :
    WhittakerCoefficientIntegrable F pins ψ (φ₁ - φ₂) α g := by
  unfold WhittakerCoefficientIntegrable at h₁ h₂ ⊢
  simp only [Pi.sub_apply, sub_mul]
  exact h₁.sub h₂

private theorem whittakerCoefficientIntegrable_smul (pins : CarrierPins F) (ψ : AddChar (AdeleRing (𝓞 F) F) ℂ)
    {φ : AdelicGL2 (𝓞 F) F → ℂ} {α : F} {g : AdelicGL2 (𝓞 F) F} (c : ℂ)
    (h : WhittakerCoefficientIntegrable F pins ψ φ α g) : WhittakerCoefficientIntegrable F pins ψ (c • φ) α g := by
  unfold WhittakerCoefficientIntegrable at h ⊢
  simp only [Pi.smul_apply, smul_eq_mul, mul_assoc]
  exact h.const_mul c

private theorem inv_sqrt_cpow_mul_sqrt_cpow (u : ℂ) {y : ℝ} (hy : 0 < y) :
    (((Real.sqrt y)⁻¹ : ℝ) : ℂ) ^ u * ((Real.sqrt y : ℝ) : ℂ) ^ u = 1 := by
  rw [← Complex.mul_cpow_ofReal_nonneg (inv_nonneg.mpr (Real.sqrt_nonneg y)) (Real.sqrt_nonneg y) u,
    ← Complex.ofReal_mul, inv_mul_cancel₀ (Real.sqrt_pos.mpr hy).ne', Complex.ofReal_one, Complex.one_cpow]

end CoefficientIdentities

section TorusCalculus

variable {F : Type} [Field F] [NumberField F] {w : InfinitePlace F} {hw : w.IsReal}

private theorem archLowerAt_eq_of_archRotDerivAt_eq {φ : AdelicGL2 (𝓞 F) F → ℂ} (hW : archRotDerivAt hw φ =
    Complex.I • φ) :
    archLowerAt hw φ = archDerivAt hw .H φ - (2 * Complex.I) • archDerivAt hw .E φ - φ := by
  have hF : archDerivAt hw .Fm φ = archDerivAt hw .E φ - Complex.I • φ := by
    rw [← hW, archRotDerivAt, sub_sub_cancel]
  rw [archLowerAt, hF]
  funext g
  simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  linear_combination (φ g) * Complex.I_mul_I

private theorem archDerivAt_H_apply_eq_of_forall_flow {Wc : AdelicGL2 (𝓞 F) F → ℂ} {h : AdelicGL2 (𝓞 F) F} {u :
    ℂ} {s : ℝ}
    {P : ℝ → ℂ} {P' : ℂ} (hP : HasDerivAt P P' s)
    (hflow : ∀ t : ℝ, Wc (h * archFlowAt hw .H t) = Complex.exp (-(t : ℂ) * u) * P (s * Real.exp (2 * t))) :
    archDerivAt hw .H Wc h = 2 * s * P' - u * P s := by
  show deriv (fun t : ℝ => Wc (h * archFlowAt hw .H t)) 0 = _
  rw [funext hflow]
  have h1 : HasDerivAt (fun t : ℝ => Complex.exp (-(t : ℂ) * u))
      (Complex.exp (-((0 : ℝ) : ℂ) * u) * (-((1 : ℝ) : ℂ) * u)) 0 :=
    (((hasDerivAt_id (0 : ℝ)).ofReal_comp).neg.mul_const u).cexp
  have hc : HasDerivAt (fun t : ℝ => s * Real.exp (2 * t)) (s * (Real.exp (2 * 0) * (2 * 1))) 0 :=
    (((hasDerivAt_id' (0 : ℝ)).const_mul (2 : ℝ)).exp).const_mul s
  have hs0 : s * Real.exp (2 * 0) = s := by simp
  have hP₀ : HasDerivAt P P' (s * Real.exp (2 * 0)) := by rwa [hs0]
  have h2 : HasDerivAt (fun t : ℝ => P (s * Real.exp (2 * t))) ((s * (Real.exp (2 * 0) * (2 * 1))) • P') 0 :=
    hP₀.scomp (0 : ℝ) hc
  rw [show (fun t : ℝ => Complex.exp (-(t : ℂ) * u) * P (s * Real.exp (2 * t)))
      = (fun t : ℝ => Complex.exp (-(t : ℂ) * u)) * (fun t : ℝ => P (s * Real.exp (2 * t))) from rfl,
    (h1.mul h2).deriv]
  simp only [Complex.ofReal_zero, neg_zero, zero_mul, Complex.exp_zero, Complex.ofReal_one, mul_zero, Real.exp_zero,
    mul_one, one_mul, Complex.real_smul]
  push_cast
  ring

private theorem archDerivAt_E_apply_eq_of_forall_flow {Wc : AdelicGL2 (𝓞 F) F → ℂ} {h : AdelicGL2 (𝓞 F) F} {s : ℝ}
    (hflow : ∀ x : ℝ, Wc (h * archFlowAt hw .E x) =
      Complex.exp (2 * (Real.pi : ℂ) * Complex.I * ((s * x : ℝ) : ℂ)) * Wc h) :
    archDerivAt hw .E Wc h = 2 * (Real.pi : ℂ) * Complex.I * (s : ℂ) * Wc h := by
  show deriv (fun x : ℝ => Wc (h * archFlowAt hw .E x)) 0 = _
  rw [funext hflow]
  have h1 : HasDerivAt (fun x : ℝ => Complex.exp (2 * (Real.pi : ℂ) * Complex.I * ((s * x : ℝ) : ℂ)))
      (Complex.exp (2 * (Real.pi : ℂ) * Complex.I * ((s * 0 : ℝ) : ℂ)) *
        (2 * (Real.pi : ℂ) * Complex.I * ((s * 1 : ℝ) : ℂ))) 0 :=
    ((((hasDerivAt_id' (0 : ℝ)).const_mul s).ofReal_comp).const_mul (2 * (Real.pi : ℂ) * Complex.I)).cexp
  rw [(h1.mul_const (Wc h)).deriv]
  norm_num

end TorusCalculus

section WeightOneDevice

open MeasureTheory

private theorem weight_eq_one_of_parity {k : ℤ} {a₁ a₂ : ZMod 2} (hne : a₁ ≠ a₂) (h01 : k = 0 ∨ k = 1)
    (hpar : (k : ZMod 2) = a₁ + a₂) : k = 1 := by
  rcases h01 with rfl | rfl
  · exfalso
    simp only [Int.cast_zero] at hpar
    have key : ∀ a b : ZMod 2, (0 : ZMod 2) = a + b → a = b := by decide
    exact hne (key a₁ a₂ hpar)
  · rfl

private theorem isKfSmooth_of_exists_rightConv_eq (F : Type) [Field F] [NumberField F]
    (φ : AdelicGL2 (𝓞 F) F → ℂ)
    (hconv : ∃ α : AdelicGL2 (𝓞 F) F → ℂ, IsFactorizableTestFn F α ∧ rightConv F φ α = φ) :
    IsKfSmooth F φ := by
  obtain ⟨α, hα, hαφ⟩ := hconv
  have h := isKfSmooth_rightConv F φ α hα
  rwa [hαφ] at h

private theorem archRotDerivAt_and_archLowerAt_whittakerCoefficient
    (D : Set (AdelicGL2 (𝓞 ℚ) ℚ)) (U : Ideal (𝓞 ℚ) → Subgroup (AdelicGL2 (𝓞 ℚ) ℚ))
    (gen : HeightOneSpectrum (𝓞 ℚ) → AdelicGL2 (𝓞 ℚ) ℚ)
    (ψ : AddChar (AdeleRing (𝓞 ℚ) ℚ) ℂ) (hψ : IsGlobalAddChar ℚ ψ) {w : InfinitePlace ℚ} (hw : w.IsReal)
    {φ : AdelicGL2 (𝓞 ℚ) ℚ → ℂ}
    (hconv : ∃ α : AdelicGL2 (𝓞 ℚ) ℚ → ℂ, IsFactorizableTestFn ℚ α ∧ rightConv ℚ φ α = φ)
    (hsm : IsArchSmoothAt hw φ) (hwt : HasArchCharacterAt₀ ℚ w (archWeightCharAt hw 1) φ) {c' : ℂ}
    (hT : archT hw φ = c' • φ)
    (hint : ∀ (α : ℚ) (g : AdelicGL2 (𝓞 ℚ) ℚ),
      WhittakerCoefficientIntegrable ℚ (productionPinsOf ℚ D U gen (adelicBox ℚ)) ψ φ α g)
    (hintd : ∀ (d : ArchDir) (α : ℚ) (g : AdelicGL2 (𝓞 ℚ) ℚ),
      WhittakerCoefficientIntegrable ℚ (productionPinsOf ℚ D U gen (adelicBox ℚ)) ψ (archDerivAt hw d φ) α g)
    (Wc : AdelicGL2 (𝓞 ℚ) ℚ → ℂ)
    (hWc : Wc = whittakerCoefficient ℚ (productionPinsOf ℚ D U gen (adelicBox ℚ)) ψ φ 1) :
    IsArchSmoothAt hw Wc ∧ archRotDerivAt hw Wc = Complex.I • Wc ∧ archLowerAt hw Wc = c' • reflAt hw Wc := by
  subst hWc
  obtain ⟨hWsm, hcomm, -⟩ := isArchSmoothAt_whittakerCoefficient_and_archDerivAt_comm D U gen ψ hψ.continuous w hw φ
    hsm (isKfSmooth_of_exists_rightConv_eq ℚ φ hconv) 1
  have hWrot : archRotDerivAt hw (whittakerCoefficient ℚ (productionPinsOf ℚ D U gen (adelicBox ℚ)) ψ φ 1)
      = Complex.I • whittakerCoefficient ℚ (productionPinsOf ℚ D U gen (adelicBox ℚ)) ψ φ 1 :=
    (archT_facts hWsm).1 (hasArchCharacterAt₀_whittakerCoefficient _ ψ hwt 1)
  refine ⟨hWsm, hWrot, ?_⟩
  have hφrot : archRotDerivAt hw φ = Complex.I • φ := (archT_facts hsm).1 hwt
  have hlow : archDerivAt hw .H φ - (2 * Complex.I) • archDerivAt hw .E φ - φ = c' • reflAt hw φ := by
    rw [← archLowerAt_eq_of_archRotDerivAt_eq hφrot]
    have h1 : reflAt hw (archT hw φ) = archLowerAt hw φ := reflAt_reflAt hw _
    rw [← h1, hT, reflAt_smul]
  funext g
  rw [archLowerAt_eq_of_archRotDerivAt_eq hWrot]
  simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  rw [hcomm .H, hcomm .E]
  have hvalue := congrArg (fun f => whittakerCoefficient ℚ (productionPinsOf ℚ D U gen (adelicBox ℚ)) ψ f 1 g) hlow
  beta_reduce at hvalue
  rw [whittakerCoefficient_sub _ ψ (whittakerCoefficientIntegrable_sub _ ψ (hintd .H 1 g)
      (whittakerCoefficientIntegrable_smul _ ψ _ (hintd .E 1 g))) (hint 1 g),
    whittakerCoefficient_sub _ ψ (hintd .H 1 g) (whittakerCoefficientIntegrable_smul _ ψ _ (hintd .E 1 g)),
    whittakerCoefficient_smul, whittakerCoefficient_smul] at hvalue
  have hrefl : whittakerCoefficient ℚ (productionPinsOf ℚ D U gen (adelicBox ℚ)) ψ (reflAt hw φ) 1 g
      = whittakerCoefficient ℚ (productionPinsOf ℚ D U gen (adelicBox ℚ)) ψ φ 1 (g * archRealGLAt hw reflJ) :=
    (whittakerCoefficient_apply_mul _ ψ φ 1 g _).symm
  rw [hrefl] at hvalue
  exact hvalue

private theorem archFlowAt_H_eq {w : InfinitePlace ℚ} (hw : w.IsReal) (t : ℝ) :
    archFlowAt hw .H t = archRealGLAt hw (splitTorusGL2 t) := rfl

private theorem archFlowAt_E_eq {w : InfinitePlace ℚ} (hw : w.IsReal) (x : ℝ) :
    archFlowAt hw .E x = archRealGLAt hw (unipotentGL2 x) := rfl

private theorem splitTorusGL2_mul_splitTorusGL2 (a t : ℝ) :
    splitTorusGL2 a * splitTorusGL2 t = splitTorusGL2 (a + t) := by
  apply Units.ext
  show (!![Real.exp a, 0; 0, Real.exp (-a)] : Matrix (Fin 2) (Fin 2) ℝ) * !![Real.exp t, 0; 0, Real.exp (-t)]
    = !![Real.exp (a + t), 0; 0, Real.exp (-(a + t))]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, Real.exp_add, Real.exp_neg, mul_comm]

private theorem splitTorusGL2_mul_unipotentGL2 (a x : ℝ) :
    splitTorusGL2 a * unipotentGL2 x = unipotentGL2 (Real.exp (2 * a) * x) * splitTorusGL2 a := by
  apply Units.ext
  show (!![Real.exp a, 0; 0, Real.exp (-a)] : Matrix (Fin 2) (Fin 2) ℝ) * !![1, x; 0, 1]
    = !![1, Real.exp (2 * a) * x; 0, 1] * !![Real.exp a, 0; 0, Real.exp (-a)]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, Real.exp_neg, two_mul, Real.exp_add]
  field_simp

private theorem splitTorusGL2_mul_reflJ (a : ℝ) : splitTorusGL2 a * reflJ = UpperHalfPlane.J * splitTorusGL2 a := by
  apply Units.ext
  show (!![Real.exp a, 0; 0, Real.exp (-a)] : Matrix (Fin 2) (Fin 2) ℝ) * !![(-1 : ℝ), 0; 0, 1]
    = !![(-1 : ℝ), 0; 0, 1] * !![Real.exp a, 0; 0, Real.exp (-a)]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

private theorem exp_two_mul_half_log {s : ℝ} (hs : 0 < s) : Real.exp (2 * (Real.log s / 2)) = s := by
  rw [mul_div_cancel₀ _ two_ne_zero, Real.exp_log hs]

private theorem half_log_mul_exp {s : ℝ} (hs : 0 < s) (t : ℝ) :
    Real.log (s * Real.exp (2 * t)) / 2 = Real.log s / 2 + t := by
  rw [Real.log_mul hs.ne' (Real.exp_pos _).ne', Real.log_exp]
  ring

private theorem torus_flow_laws {w : InfinitePlace ℚ} (hw : w.IsReal) (Wc : AdelicGL2 (𝓞 ℚ) ℚ → ℂ)
    (hWreal : ∀ (x : ℝ) (g : AdelicGL2 (𝓞 ℚ) ℚ),
      Wc (archRealGLAt hw (unipotentGL2 x) * g) = Complex.exp (2 * Real.pi * Complex.I * x) * Wc g)
    {g : AdelicGL2 (𝓞 ℚ) ℚ} (hg : glArch (𝓞 ℚ) ℚ g = 1) {s : ℝ} (hs : 0 < s) :
    (∀ t : ℝ, Wc (archRealGLAt hw (splitTorusGL2 (Real.log s / 2)) * g * archFlowAt hw .H t)
        = Wc (archRealGLAt hw (splitTorusGL2 (Real.log (s * Real.exp (2 * t)) / 2)) * g)) ∧
      (∀ x : ℝ, Wc (archRealGLAt hw (splitTorusGL2 (Real.log s / 2)) * g * archFlowAt hw .E x)
        = Complex.exp (2 * (Real.pi : ℂ) * Complex.I * ((s * x : ℝ) : ℂ))
            * Wc (archRealGLAt hw (splitTorusGL2 (Real.log s / 2)) * g)) ∧
      reflAt hw Wc (archRealGLAt hw (splitTorusGL2 (Real.log s / 2)) * g)
        = Wc (archRealGLAt hw (UpperHalfPlane.J * splitTorusGL2 (Real.log s / 2)) * g) := by
  refine ⟨fun t => ?_, fun x => ?_, ?_⟩
  · rw [archFlowAt_H_eq, mul_assoc, ← archRealGLAt_mul_comm_of_glArch_eq_one hw _ hg, ← mul_assoc, ← map_mul,
      splitTorusGL2_mul_splitTorusGL2, half_log_mul_exp hs]
  · rw [archFlowAt_E_eq, mul_assoc, ← archRealGLAt_mul_comm_of_glArch_eq_one hw _ hg, ← mul_assoc, ← map_mul,
      splitTorusGL2_mul_unipotentGL2, exp_two_mul_half_log hs, map_mul, mul_assoc]
    exact hWreal (s * x) _
  · show Wc (archRealGLAt hw (splitTorusGL2 (Real.log s / 2)) * g * archRealGLAt hw reflJ) = _
    rw [mul_assoc, ← archRealGLAt_mul_comm_of_glArch_eq_one hw _ hg, ← mul_assoc, ← map_mul, splitTorusGL2_mul_reflJ]

private theorem lowering_relation_of_profiles {w : InfinitePlace ℚ} (hw : w.IsReal) (Wc : AdelicGL2 (𝓞 ℚ) ℚ → ℂ)
    (hWreal : ∀ (x : ℝ) (g : AdelicGL2 (𝓞 ℚ) ℚ),
      Wc (archRealGLAt hw (unipotentGL2 x) * g) = Complex.exp (2 * Real.pi * Complex.I * x) * Wc g)
    (hWrot : archRotDerivAt hw Wc = Complex.I • Wc) {c' : ℂ} (hWlow : archLowerAt hw Wc = c' • reflAt hw Wc)
    {g : AdelicGL2 (𝓞 ℚ) ℚ} (hg : glArch (𝓞 ℚ) ℚ g = 1)
    (hf : DifferentiableOn ℝ (fun y : ℝ => Wc (archRealGLAt hw (splitTorusGL2 (Real.log y / 2)) * g)) (Set.Ioi 0))
    {t : ℝ} (ht : 0 < t) :
    c' * Wc (archRealGLAt hw (UpperHalfPlane.J * splitTorusGL2 (Real.log t / 2)) * g)
      = 2 * (t : ℂ) * deriv (fun y : ℝ => Wc (archRealGLAt hw (splitTorusGL2 (Real.log y / 2)) * g)) t
        + (4 * (Real.pi : ℂ) * (t : ℂ) - 1) * Wc (archRealGLAt hw (splitTorusGL2 (Real.log t / 2)) * g) := by
  obtain ⟨hflowH, hflowE, hreflv⟩ := torus_flow_laws hw Wc hWreal hg ht
  have hderiv : HasDerivAt (fun y : ℝ => Wc (archRealGLAt hw (splitTorusGL2 (Real.log y / 2)) * g))
      (deriv (fun y : ℝ => Wc (archRealGLAt hw (splitTorusGL2 (Real.log y / 2)) * g)) t) t :=
    (hf.differentiableAt (Ioi_mem_nhds ht)).hasDerivAt
  have hH := archDerivAt_H_apply_eq_of_forall_flow (Wc := Wc)
    (h := archRealGLAt hw (splitTorusGL2 (Real.log t / 2)) * g) (u := 0) hderiv (fun τ => by
      rw [hflowH τ]
      simp only [mul_zero, Complex.exp_zero, one_mul])
  have hE := archDerivAt_E_apply_eq_of_forall_flow hflowE
  have hX := congrFun hWlow (archRealGLAt hw (splitTorusGL2 (Real.log t / 2)) * g)
  rw [Pi.smul_apply, smul_eq_mul, hreflv, archLowerAt_eq_of_archRotDerivAt_eq hWrot] at hX
  simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at hX
  rw [hH, hE] at hX
  linear_combination (-1 : ℂ) * hX
    + (-(4 * (Real.pi : ℂ) * (t : ℂ) * Wc (archRealGLAt hw (splitTorusGL2 (Real.log t / 2)) * g))) * Complex.I_sq

end WeightOneDevice

end

end P2M.WeightOneOdd

open P2M.WeightOneOdd in

theorem solution
    (c u d₁ d₂ : ℝ) (T : Finset (AdelicGL2 (𝓞 ℚ) ℚ))
    (_hd : d₁ < d₂)
    (_hcov : CoversModCentre ℚ (⋃ x ∈ T, (· * x) '' centreCutSiegelSet ℚ c u d₁ d₂))
    (Φ : HeckeEigensystem ℚ ℂ)
    (R : SmoothCuspRealizationAt ℚ
      (productionPinsOf ℚ (⋃ x ∈ T, (· * x) '' centreCutSiegelSet ℚ c u d₁ d₂)
        (fun N => levelOne (𝓞 ℚ) ℚ N ⊓ finiteAdelicGL2Subgroup ℚ) (fun v => heckeGen (𝓞 ℚ) ℚ v)
        (adelicBox ℚ))
      Φ.toRawCentral)
    (_hR : Continuous R.toFun)
    (ψ : AddChar (AdeleRing (𝓞 ℚ) ℚ) ℂ) (_hψ : IsGlobalAddChar ℚ ψ)
    (_hψr : ∀ (w : InfinitePlace ℚ), w.IsReal → ∀ x : InfiniteAdeleRing ℚ,
      (∀ w' : InfinitePlace ℚ, w' ≠ w → x w' = 0) →
        ψ (⟨x, 0⟩ : AdeleRing (𝓞 ℚ) ℚ)
          = Complex.exp (2 * Real.pi * Complex.I * extensionEmbedding w (x w)))
    (S : Finset (HeightOneSpectrum (𝓞 ℚ))) (archR : ∀ w : InfinitePlace ℚ, w.IsReal → RealArchParam)
    (_hS : R.exceptionalSet ⊆ S)
    (_htype : ∀ (w : InfinitePlace ℚ) (hw : w.IsReal) (u₁ u₂ : ℂ) (a₁ a₂ : ZMod 2),
      archR w hw = RealArchParam.principal u₁ a₁ u₂ a₂ → |(u₁ - u₂).re| < 1)
    (_hcen : ∀ (w : InfinitePlace ℚ) (hw : w.IsReal),
      IsArchCompAt ℚ (R.centralChar.comp Subgroup.topEquiv.symm.toMonoidHom) w
        ((archR w hw).centralExponent + 1) ((archR w hw).centralSign.val : ℤ))
    (φ₁ : AdelicGL2 (𝓞 ℚ) ℚ → ℂ) (k₁ : InfinitePlace ℚ → ℤ)
    (_hiso : IsIsotypicCuspFormAt ℚ
        (productionPinsOf ℚ (⋃ x ∈ T, (· * x) '' centreCutSiegelSet ℚ c u d₁ d₂)
          (fun N => levelOne (𝓞 ℚ) ℚ N ⊓ finiteAdelicGL2Subgroup ℚ)
          (fun v => heckeGen (𝓞 ℚ) ℚ v) (adelicBox ℚ))
        R.centralChar Φ.level S Φ φ₁)
    (_hne : φ₁ ≠ 0)
    (_hconv : ∃ α : AdelicGL2 (𝓞 ℚ) ℚ → ℂ, IsFactorizableTestFn ℚ α ∧ rightConv ℚ φ₁ α = φ₁)
    (_hwt : ∀ (w : InfinitePlace ℚ) (hw : w.IsReal),
      HasArchCharacterAt₀ ℚ w (archWeightCharAt hw (k₁ w)) φ₁)
    (_hminp : ∀ (w : InfinitePlace ℚ) (hw : w.IsReal) (u₁ u₂ : ℂ) (a₁ a₂ : ZMod 2),
      archR w hw = RealArchParam.principal u₁ a₁ u₂ a₂ →
        (k₁ w = 0 ∨ k₁ w = 1) ∧ ((k₁ w : ZMod 2) = a₁ + a₂))
    (_hmind : ∀ (w : InfinitePlace ℚ) (hw : w.IsReal) (u₀ : ℂ) (n : ℕ) (hn : 1 ≤ n),
      archR w hw = RealArchParam.discrete u₀ n hn → k₁ w = (n : ℤ) + 1)
    (_hpair : ∀ (w : InfinitePlace ℚ) (hw : w.IsReal),
      IsArchSmoothAt hw φ₁ ∧ archCasimirAt hw φ₁ = (archR w hw).laplaceEigenvalue • φ₁)
    (_hne₂ : ∀ (w : InfinitePlace ℚ) (hw : w.IsReal), ∃ (u₁ u₂ : ℂ) (a₁ a₂ : ZMod 2),
      archR w hw = RealArchParam.principal u₁ a₁ u₂ a₂ ∧ a₁ ≠ a₂ ∧ u₁ ≠ u₂) :
    ∀ (w₀ : InfinitePlace ℚ) (hw₀ : w₀.IsReal) (μ : ℂ),
      (∃ (u₁ u₂ : ℂ) (a₁ a₂ : ZMod 2), archR w₀ hw₀ = RealArchParam.principal u₁ a₁ u₂ a₂ ∧
        (μ = u₁ - u₂ ∨ μ = u₂ - u₁)) →
      φ₁ + μ⁻¹ • (fun g : AdelicGL2 (𝓞 ℚ) ℚ =>
          (archDerivAt hw₀ ArchDir.H φ₁
            - Complex.I • (archDerivAt hw₀ ArchDir.E φ₁ + archDerivAt hw₀ ArchDir.Fm φ₁))
              (g * archRealGLAt hw₀ UpperHalfPlane.J)) ≠ 0 →
    ∃ archR' : ∀ w : InfinitePlace ℚ, w.IsReal → RealArchParam,
      (∀ (w : InfinitePlace ℚ) (hw : w.IsReal), archR' w hw = archR w hw ∨
        ∃ (u₁ u₂ : ℂ) (a₁ a₂ : ZMod 2), archR w hw = RealArchParam.principal u₁ a₁ u₂ a₂ ∧
          archR' w hw = RealArchParam.principal u₁ a₂ u₂ a₁) ∧
      (∀ (w : InfinitePlace ℚ) (hw : w.IsReal) (u₁ u₂ : ℂ) (a₁ a₂ : ZMod 2),
        archR' w hw = RealArchParam.principal u₁ a₁ u₂ a₂ → |(u₁ - u₂).re| < 1) ∧
      (∀ (w : InfinitePlace ℚ) (hw : w.IsReal) (u₁ u₂ : ℂ) (a₁ a₂ : ZMod 2),
        archR' w hw = RealArchParam.principal u₁ a₁ u₂ a₂ →
          ∀ p : ℤ, p ≠ 0 → u₁ - u₂ = (p : ℂ) → a₁ - a₂ ≠ ((p + 1 : ℤ) : ZMod 2)) ∧
      (∀ (w : InfinitePlace ℚ) (hw : w.IsReal),
        IsArchCompAt ℚ (R.centralChar.comp Subgroup.topEquiv.symm.toMonoidHom) w
          ((archR' w hw).centralExponent + 1) ((archR' w hw).centralSign.val : ℤ)) ∧
      ∃ C : FiniteAdeleRing (𝓞 ℚ) ℚ → AdelicGL2 (𝓞 ℚ) ℚ → ℂ,
      ∀ par : InfinitePlace ℚ → ZMod 2,
        ∃ (φ : AdelicGL2 (𝓞 ℚ) ℚ → ℂ) (Wr : InfinitePlace ℚ → ℂ → ℂ) (k : InfinitePlace ℚ → ℤ),

          φ = φ₁ + μ⁻¹ • (fun g : AdelicGL2 (𝓞 ℚ) ℚ =>
            (archDerivAt hw₀ ArchDir.H φ₁
              - Complex.I • (archDerivAt hw₀ ArchDir.E φ₁ + archDerivAt hw₀ ArchDir.Fm φ₁))
                (g * archRealGLAt hw₀ UpperHalfPlane.J)) ∧
          IsIsotypicCuspFormAt ℚ
              (productionPinsOf ℚ (⋃ x ∈ T, (· * x) '' centreCutSiegelSet ℚ c u d₁ d₂)
                (fun N => levelOne (𝓞 ℚ) ℚ N ⊓ finiteAdelicGL2Subgroup ℚ)
                (fun v => heckeGen (𝓞 ℚ) ℚ v) (adelicBox ℚ))
              R.centralChar Φ.level S Φ φ ∧
          φ ≠ 0 ∧
          (∃ α : AdelicGL2 (𝓞 ℚ) ℚ → ℂ, IsFactorizableTestFn ℚ α ∧ rightConv ℚ φ α = φ) ∧
          (∀ (w : InfinitePlace ℚ) (hw : w.IsReal),
            HasArchCharacterAt₀ ℚ w (archWeightCharAt hw (k w)) φ) ∧
          (∀ (w : InfinitePlace ℚ) (hw : w.IsReal) (u₁ u₂ : ℂ) (a₁ a₂ : ZMod 2),
            archR' w hw = RealArchParam.principal u₁ a₁ u₂ a₂ →
              (k w : ℂ) = signShift (a₁ + par w) + signShift (a₂ + par w)) ∧
          (∀ (w : InfinitePlace ℚ) (hw : w.IsReal) (u₀ : ℂ) (n : ℕ) (hn : 1 ≤ n),
            archR' w hw = RealArchParam.discrete u₀ n hn → k w = (n : ℤ) + 1) ∧
          (∀ a : (AdeleRing (𝓞 ℚ) ℚ)ˣ, ∀ g : AdelicGL2 (𝓞 ℚ) ℚ, g ∈ finiteAdelicGL2Subgroup ℚ →
              whittakerCoefficient ℚ
                  (productionPinsOf ℚ (⋃ x ∈ T, (· * x) '' centreCutSiegelSet ℚ c u d₁ d₂)
                    (fun N => levelOne (𝓞 ℚ) ℚ N ⊓ finiteAdelicGL2Subgroup ℚ)
                    (fun v => heckeGen (𝓞 ℚ) ℚ v) (adelicBox ℚ))
                  ψ φ 1 (diagOne a * g)
                = (∏ w : InfinitePlace ℚ, Wr w (extensionEmbedding w ((a : AdeleRing (𝓞 ℚ) ℚ).1 w)))
                    * C (a : AdeleRing (𝓞 ℚ) ℚ).2 g) ∧
          (∀ (w : InfinitePlace ℚ) (hw : w.IsReal) (u₁ u₂ : ℂ) (a₁ : ZMod 2),
            archR' w hw = RealArchParam.principal u₁ a₁ u₂ a₁ → par w = a₁ →
              ∀ t : ℝ, Wr w (-t) = (-1 : ℂ) ^ a₁.val * Wr w t) ∧
          (∀ (w : InfinitePlace ℚ) (hw : w.IsReal) (u₀ : ℂ) (n : ℕ) (hn : 1 ≤ n),
            archR' w hw = RealArchParam.discrete u₀ n hn → ∀ t : ℝ, t < 0 → Wr w t = 0) ∧
          (∀ (w : InfinitePlace ℚ) (hw : w.IsReal) (u₁ u₂ : ℂ) (a₁ : ZMod 2),
            archR' w hw = RealArchParam.principal u₁ a₁ u₂ a₁ → par w = a₁ + 1 →
              ∃ s₀ : ℝ, ∀ s : ℂ, s₀ < s.re →
                MellinConvergent
                    (fun t : ℝ => (Wr w t + (-1 : ℂ) ^ a₁.val * Wr w (-t)) / (t : ℂ)) s ∧
                  mellin (fun t : ℝ => (Wr w t + (-1 : ℂ) ^ a₁.val * Wr w (-t)) / (t : ℂ)) s
                    = (2 * s + u₁ + u₂ - 1) / (4 * (Real.pi : ℂ))
                        * ((archR' w hw).twist 0 a₁).archFactor s) ∧
          (∀ (w : InfinitePlace ℚ) (hw : w.IsReal) (b : ZMod 2),
            (b = par w ∨ b = par w + (archR' w hw).centralSign) →
              ∃ s₀ : ℝ, ∀ s : ℂ, s₀ < s.re →
                MellinConvergent
                    (fun t : ℝ => (Wr w t + (-1 : ℂ) ^ b.val * Wr w (-t)) / (t : ℂ)) s ∧
                  mellin (fun t : ℝ => (Wr w t + (-1 : ℂ) ^ b.val * Wr w (-t)) / (t : ℂ)) s
                    = ((archR' w hw).twist 0 b).archFactor s) := by
  intro w₀ hw₀ μ hμex hne0

  obtain ⟨u₁, u₂, a₁, a₂, hP, hapar, huu⟩ := _hne₂ w₀ hw₀
  obtain ⟨hk01, hkpar⟩ := _hminp w₀ hw₀ u₁ u₂ a₁ a₂ hP
  have hk1 : k₁ w₀ = 1 := weight_eq_one_of_parity hapar hk01 hkpar
  obtain ⟨hsm₁, hΩ₁⟩ := _hpair w₀ hw₀
  rw [hP] at hΩ₁
  have hwt₁ : HasArchCharacterAt₀ ℚ w₀ (archWeightCharAt hw₀ 1) φ₁ := by
    have h := _hwt w₀ hw₀
    rwa [hk1] at h
  have hc : μ = u₁ - u₂ ∨ μ = u₂ - u₁ := by
    obtain ⟨v₁, v₂, b₁, b₂, hP', hμ'⟩ := hμex
    rw [hP] at hP'
    simp only [RealArchParam.principal.injEq] at hP'
    obtain ⟨rfl, -, rfl, -⟩ := hP'
    exact hμ'
  have hμ : μ * μ = 1 - 4 * (RealArchParam.principal u₁ a₁ u₂ a₂).laplaceEigenvalue := by
    rcases hc with rfl | rfl
    · exact mul_self_sub_eq_one_sub_four_mul_laplaceEigenvalue u₁ a₁ u₂ a₂
    · rw [← mul_self_sub_eq_one_sub_four_mul_laplaceEigenvalue u₁ a₁ u₂ a₂]
      ring
  have hμ0 : μ ≠ 0 := by
    rcases hc with rfl | rfl
    · exact sub_ne_zero.mpr huu
    · exact sub_ne_zero.mpr (Ne.symm huu)
  have hψr₀ := _hψr w₀ hw₀
  have hcen₀ : IsArchCompAt ℚ (R.centralChar.comp Subgroup.topEquiv.symm.toMonoidHom) w₀ (u₁ + u₂ + 1)
      ((archR w₀ hw₀).centralSign.val : ℤ) := by
    have h := _hcen w₀ hw₀
    have he : (archR w₀ hw₀).centralExponent = u₁ + u₂ := congrArg RealArchParam.centralExponent hP
    rw [he] at h
    exact h

  set φ : AdelicGL2 (𝓞 ℚ) ℚ → ℂ := φ₁ + μ⁻¹ • archT hw₀ φ₁ with hφdef
  have hneφ : φ ≠ 0 := hne0
  have hW₁ : archRotDerivAt hw₀ φ₁ = Complex.I • φ₁ := (archT_facts hsm₁).1 hwt₁
  have hTφ : archT hw₀ φ = μ • φ := isArchSmoothAt_archT_add_inv_smul_archT hsm₁ hΩ₁ hwt₁ hμ hμ0
  have hsmφ : IsArchSmoothAt hw₀ φ := isArchSmoothAt_add_smul_archT hsm₁ _
  have hwtφ : HasArchCharacterAt₀ ℚ w₀ (archWeightCharAt hw₀ 1) φ :=
    isArchSmoothAt_hasArchCharacterAt₀_one_add_smul_archT hsm₁ hwt₁ _
  have hΩφ : archCasimirAt hw₀ φ = (RealArchParam.principal u₁ a₁ u₂ a₂).laplaceEigenvalue • φ :=
    isArchSmoothAt_archCasimirAt_add_smul_archT hsm₁ hΩ₁ _
  have hΩν : archCasimirAt hw₀ φ = (1 / 4 - ((u₁ - u₂) / 2) ^ 2) • φ := hΩφ

  obtain ⟨-, hstab, -, -⟩ :=
    exists_rightConv_eq_self_and_isIsotypicCuspFormAt_add_smul_archDerivAt_and_whittakerCoefficient_bounds_of_mem_archCutSubmodule
      c u d₁ d₂ T _hd _hcov Φ R.centralChar S φ₁ _hiso _hne
      (fun w' => archWeightCharAt (isReal_infinitePlace_rat w') (k₁ w')) (fun w' => _hwt w' _)
  have hisoφ : IsIsotypicCuspFormAt ℚ
      (productionPinsOf ℚ (⋃ x ∈ T, (· * x) '' centreCutSiegelSet ℚ c u d₁ d₂)
        (fun N => levelOne (𝓞 ℚ) ℚ N ⊓ finiteAdelicGL2Subgroup ℚ) (fun v => heckeGen (𝓞 ℚ) ℚ v) (adelicBox ℚ))
      R.centralChar Φ.level S Φ φ := by
    have hJ : glFin (𝓞 ℚ) ℚ (archRealGLAt hw₀ reflJ) = 1 := glFin_adelicArchGLIncl ℚ _
    have h := hstab w₀ hw₀ 1 (-Complex.I) (-Complex.I) μ⁻¹ (archRealGLAt hw₀ reflJ) hJ
    have hbr : (fun g => ((1 : ℂ) • archDerivAt hw₀ .H φ₁ + (-Complex.I) • archDerivAt hw₀ .E φ₁
        + (-Complex.I) • archDerivAt hw₀ .Fm φ₁) (g * archRealGLAt hw₀ reflJ)) = archT hw₀ φ₁ := by
      funext g
      simp only [archT, reflAt, archLowerAt, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
      ring
    rwa [hbr] at h

  have harchφ : ∀ w' : InfinitePlace ℚ, HasArchCharacterAt₀ ℚ w' (archWeightCharAt (isReal_infinitePlace_rat w') 1) φ := by
    intro w'
    obtain rfl : w' = w₀ := Subsingleton.elim _ _
    exact hwtφ
  obtain ⟨⟨γ, hγ, -, hγrep⟩, -, hana, hgrowth⟩ :=
    exists_rightConv_eq_self_and_isIsotypicCuspFormAt_add_smul_archDerivAt_and_whittakerCoefficient_bounds_of_mem_archCutSubmodule
      c u d₁ d₂ T _hd _hcov Φ R.centralChar S φ hisoφ hneφ
      (fun w' => archWeightCharAt (isReal_infinitePlace_rat w') 1) harchφ
  have hconvφ : ∃ α : AdelicGL2 (𝓞 ℚ) ℚ → ℂ, IsFactorizableTestFn ℚ α ∧ rightConv ℚ φ α = φ := ⟨γ, hγ, hγrep⟩
  obtain ⟨hint, hintd, g₀, hg₀⟩ := hana ψ _hψ w₀ hw₀ hsmφ

  obtain ⟨Wc, hWc⟩ : ∃ Wc : AdelicGL2 (𝓞 ℚ) ℚ → ℂ, Wc = whittakerCoefficient ℚ
      (productionPinsOf ℚ (⋃ x ∈ T, (· * x) '' centreCutSiegelSet ℚ c u d₁ d₂)
        (fun N => levelOne (𝓞 ℚ) ℚ N ⊓ finiteAdelicGL2Subgroup ℚ) (fun v => heckeGen (𝓞 ℚ) ℚ v) (adelicBox ℚ))
      ψ φ 1 := ⟨_, rfl⟩
  obtain ⟨-, hWrot, hWlow⟩ := archRotDerivAt_and_archLowerAt_whittakerCoefficient _ _ _ ψ _hψ hw₀ hconvφ hsmφ hwtφ hTφ
    hint hintd Wc hWc
  have hgrW : ∀ t : AdelicGL2 (𝓞 ℚ) ℚ, t ∈ finiteAdelicGL2Subgroup ℚ →
      ∃ C M : ℝ, ∀ a : (AdeleRing (𝓞 ℚ) ℚ)ˣ, ((a : AdeleRing (𝓞 ℚ) ℚ)).2 = 1 →
        ‖Wc (diagOne a * t)‖ ≤ C * ideleNorm ℚ a ^ M := by
    intro t ht
    rw [hWc]
    exact hgrowth ψ _hψ t ht

  obtain ⟨⟨-, hWreal⟩, hpeel0, hpeelm0, hode, hgrp, -, hrefd, hsep, hpack⟩ :=
    whittakerCoefficient_torus_peel_ode_growth_and_separation_of_isIsotypicCuspFormAt_of_archCasimirAt_eq_smul
      _ _ _ ψ _hψ w₀ hw₀ hψr₀ R.centralChar Φ.level S Φ φ hisoφ hconvφ hsmφ ((u₁ - u₂) / 2) hΩν 1 hwtφ
      (u₁ + u₂ + 1) _ hcen₀ Wc hWc hgrW
  have hprofile : ∀ g : AdelicGL2 (𝓞 ℚ) ℚ, g ∈ finiteAdelicGL2Subgroup ℚ →
      DifferentiableOn ℝ (fun y : ℝ => Wc (archRealGLAt hw₀ (splitTorusGL2 (Real.log y / 2)) * g)) (Set.Ioi 0) ∧
      DifferentiableOn ℝ (deriv (fun y : ℝ => Wc (archRealGLAt hw₀ (splitTorusGL2 (Real.log y / 2)) * g)))
        (Set.Ioi 0) ∧
      (∀ y : ℝ, 0 < y →
        (y : ℂ) ^ 2 * deriv (deriv (fun y : ℝ => Wc (archRealGLAt hw₀ (splitTorusGL2 (Real.log y / 2)) * g))) y
          + (1 / 4 - ((u₁ - u₂) / 2) ^ 2 + 2 * (Real.pi : ℂ) * (y : ℂ) - 4 * (Real.pi : ℂ) ^ 2 * (y : ℂ) ^ 2)
            * Wc (archRealGLAt hw₀ (splitTorusGL2 (Real.log y / 2)) * g) = 0) := by
    intro g hg
    obtain ⟨hf, hf', hodeg⟩ := (hode g hg).1
    refine ⟨hf, hf', fun y hy => ?_⟩
    have h := hodeg y hy
    simp only [Int.cast_one, Complex.ofReal_one, mul_one] at h
    exact h
  have hpeel : ∀ g : AdelicGL2 (𝓞 ℚ) ℚ, ∀ y : ℝ, ∀ hy : 0 < y,
      Wc (archRealGLAt hw₀ (diagOne (Units.mk0 y hy.ne')) * g)
        = ((Real.sqrt y : ℝ) : ℂ) ^ (u₁ + u₂ + 1) * Wc (archRealGLAt hw₀ (splitTorusGL2 (Real.log y / 2)) * g) := by
    intro g y hy
    rw [hpeel0 y hy g, ← mul_assoc, mul_comm (((Real.sqrt y : ℝ) : ℂ) ^ (u₁ + u₂ + 1)),
      inv_sqrt_cpow_mul_sqrt_cpow _ hy, one_mul]
  have hpeelm : ∀ g : AdelicGL2 (𝓞 ℚ) ℚ, ∀ y : ℝ, ∀ hy : 0 < y,
      Wc (archRealGLAt hw₀ (diagOne (Units.mk0 (-y) (neg_ne_zero.mpr hy.ne'))) * g)
        = ((Real.sqrt y : ℝ) : ℂ) ^ (u₁ + u₂ + 1)
            * Wc (archRealGLAt hw₀ (UpperHalfPlane.J * splitTorusGL2 (Real.log y / 2)) * g) := by
    intro g y hy
    rw [hpeelm0 y hy g, ← mul_assoc, mul_comm (((Real.sqrt y : ℝ) : ℂ) ^ (u₁ + u₂ + 1)),
      inv_sqrt_cpow_mul_sqrt_cpow _ hy, one_mul]
  have hlower : ∀ g : AdelicGL2 (𝓞 ℚ) ℚ, g ∈ finiteAdelicGL2Subgroup ℚ → ∀ t : ℝ, 0 < t →
      μ * Wc (archRealGLAt hw₀ (UpperHalfPlane.J * splitTorusGL2 (Real.log t / 2)) * g)
        = 2 * (t : ℂ) * deriv (fun y : ℝ => Wc (archRealGLAt hw₀ (splitTorusGL2 (Real.log y / 2)) * g)) t
          + (4 * (Real.pi : ℂ) * (t : ℂ) - 1) * Wc (archRealGLAt hw₀ (splitTorusGL2 (Real.log t / 2)) * g) :=
    fun g hg t ht => lowering_relation_of_profiles hw₀ Wc hWreal hWrot hWlow hg (hprofile g hg).1 ht

  rw [← hWc] at hg₀
  obtain ⟨r, hr, t₀, ht₀, href⟩ := hrefd g₀ hg₀
  have hsqrt_ne : ∀ y : ℝ, 0 < y → ((Real.sqrt y : ℝ) : ℂ) ^ (u₁ + u₂ + 1) ≠ 0 :=
    fun y hy => right_ne_zero_of_mul_eq_one (inv_sqrt_cpow_mul_sqrt_cpow (u₁ + u₂ + 1) hy)

  have hfne : ∃ y : ℝ, 0 < y ∧ Wc (archRealGLAt hw₀ (splitTorusGL2 (Real.log y / 2)) * t₀) ≠ 0 := by
    by_contra hall
    push Not at hall
    rcases Ne.lt_or_gt hr with hneg | hpos
    ·
      have hy : 0 < -r := neg_pos.mpr hneg
      have hzero : Wc (archRealGLAt hw₀ (UpperHalfPlane.J * splitTorusGL2 (Real.log (-r) / 2)) * t₀) = 0 := by
        have hrel := hlower t₀ ht₀ (-r) hy
        have hd : deriv (fun y : ℝ => Wc (archRealGLAt hw₀ (splitTorusGL2 (Real.log y / 2)) * t₀)) (-r) = 0 := by
          have hev : (fun y : ℝ => Wc (archRealGLAt hw₀ (splitTorusGL2 (Real.log y / 2)) * t₀))
              =ᶠ[nhds (-r)] fun _ => (0 : ℂ) :=
            Filter.eventuallyEq_of_mem (Ioi_mem_nhds hy) fun y hy' => hall y hy'
          rw [hev.deriv_eq, deriv_const]
        rw [hd, hall (-r) hy] at hrel
        simp only [mul_zero, add_zero] at hrel
        exact (mul_eq_zero.mp hrel).resolve_left hμ0
      apply href
      have h := hpeelm t₀ (-r) hy
      simp only [neg_neg] at h
      rw [h, hzero, mul_zero]
    · apply href
      rw [hpeel t₀ r hpos, hall r hpos, mul_zero]
  obtain ⟨y₀, hy₀, hfy₀⟩ := hfne
  have href₀ : Wc (archRealGLAt hw₀ (diagOne (Units.mk0 y₀ hy₀.ne')) * t₀) ≠ 0 := by
    rw [hpeel t₀ y₀ hy₀]
    exact mul_ne_zero (hsqrt_ne y₀ hy₀) hfy₀

  have hG1 := hsep t₀ ht₀ y₀ hy₀ href₀
  have hprop : ∀ h : AdelicGL2 (𝓞 ℚ) ℚ, h ∈ finiteAdelicGL2Subgroup ℚ → ∀ (s : ℝ) (hs : s ≠ 0),
      Wc (archRealGLAt hw₀ (diagOne (Units.mk0 s hs)) * h)
        = (Wc (archRealGLAt hw₀ (diagOne (Units.mk0 y₀ hy₀.ne')) * h)
            / Wc (archRealGLAt hw₀ (diagOne (Units.mk0 y₀ hy₀.ne')) * t₀))
          * (if hs' : (s : ℂ).re ≠ 0 then Wc (archRealGLAt hw₀ (diagOne (Units.mk0 (s : ℂ).re hs')) * t₀)
            else 0) := by
    intro h hh s hs
    have hre : (s : ℂ).re ≠ 0 := by simpa using hs
    rw [dif_pos hre]
    simp only [Complex.ofReal_re]
    obtain ⟨κ, hκ⟩ : ∃ κ : ℂ, κ = Wc (archRealGLAt hw₀ (diagOne (Units.mk0 y₀ hy₀.ne')) * h)
        / Wc (archRealGLAt hw₀ (diagOne (Units.mk0 y₀ hy₀.ne')) * t₀) := ⟨_, rfl⟩
    rw [← hκ]

    have hfprop : ∀ y : ℝ, 0 < y →
        Wc (archRealGLAt hw₀ (splitTorusGL2 (Real.log y / 2)) * h)
          = κ * Wc (archRealGLAt hw₀ (splitTorusGL2 (Real.log y / 2)) * t₀) := by
      intro y hy'
      have h1 := hG1 h hh y hy'
      rw [← hκ, hpeel h y hy', hpeel t₀ y hy'] at h1
      have h2 : ((Real.sqrt y : ℝ) : ℂ) ^ (u₁ + u₂ + 1) * Wc (archRealGLAt hw₀ (splitTorusGL2 (Real.log y / 2)) * h)
          = ((Real.sqrt y : ℝ) : ℂ) ^ (u₁ + u₂ + 1)
            * (κ * Wc (archRealGLAt hw₀ (splitTorusGL2 (Real.log y / 2)) * t₀)) := by
        rw [h1]
        ring
      exact mul_left_cancel₀ (hsqrt_ne y hy') h2
    rcases Ne.lt_or_gt hs with hneg | hpos
    ·
      have hy : 0 < -s := neg_pos.mpr hneg
      have hderiv : deriv (fun y : ℝ => Wc (archRealGLAt hw₀ (splitTorusGL2 (Real.log y / 2)) * h)) (-s)
          = κ * deriv (fun y : ℝ => Wc (archRealGLAt hw₀ (splitTorusGL2 (Real.log y / 2)) * t₀)) (-s) := by
        have hd₀ : HasDerivAt (fun y : ℝ => Wc (archRealGLAt hw₀ (splitTorusGL2 (Real.log y / 2)) * t₀))
            (deriv (fun y : ℝ => Wc (archRealGLAt hw₀ (splitTorusGL2 (Real.log y / 2)) * t₀)) (-s)) (-s) :=
          ((hprofile t₀ ht₀).1.differentiableAt (Ioi_mem_nhds hy)).hasDerivAt
        have hev : (fun y : ℝ => κ * Wc (archRealGLAt hw₀ (splitTorusGL2 (Real.log y / 2)) * t₀))
            =ᶠ[nhds (-s)] fun y : ℝ => Wc (archRealGLAt hw₀ (splitTorusGL2 (Real.log y / 2)) * h) :=
          Filter.eventuallyEq_of_mem (Ioi_mem_nhds hy) fun y hy' => (hfprop y hy').symm
        exact ((hd₀.const_mul κ).congr_of_eventuallyEq hev.symm).deriv
      have hrel_h := hlower h hh (-s) hy
      have hrel₀ := hlower t₀ ht₀ (-s) hy
      rw [hderiv, hfprop (-s) hy] at hrel_h
      have hJ : Wc (archRealGLAt hw₀ (UpperHalfPlane.J * splitTorusGL2 (Real.log (-s) / 2)) * h)
          = κ * Wc (archRealGLAt hw₀ (UpperHalfPlane.J * splitTorusGL2 (Real.log (-s) / 2)) * t₀) := by
        apply mul_left_cancel₀ hμ0
        linear_combination hrel_h - κ * hrel₀
      have hh' := hpeelm h (-s) hy
      have ht' := hpeelm t₀ (-s) hy
      simp only [neg_neg] at hh' ht'
      rw [hh', ht', hJ]
      ring
    · have h1 := hG1 h hh s hpos
      rwa [← hκ] at h1

  have hgr₀ := hgrp t₀ ht₀
  subst hWc
  obtain ⟨hf₀, hf₀', hode₀⟩ := hprofile t₀ ht₀
  obtain ⟨P', hP', ρ, hρ, hmellin⟩ := exists_mellin_whittakerProfile_eq_archFactor_of_whittaker_ode_weightOne
    u₁ u₂ a₁ a₂ hapar huu
    (fun z : ℂ => if hz : z.re ≠ 0 then whittakerCoefficient ℚ
      (productionPinsOf ℚ (⋃ x ∈ T, (· * x) '' centreCutSiegelSet ℚ c u d₁ d₂)
        (fun N => levelOne (𝓞 ℚ) ℚ N ⊓ finiteAdelicGL2Subgroup ℚ) (fun v => heckeGen (𝓞 ℚ) ℚ v) (adelicBox ℚ))
      ψ φ 1 (archRealGLAt hw₀ (diagOne (Units.mk0 z.re hz)) * t₀) else 0)
    (fun y : ℝ => whittakerCoefficient ℚ
      (productionPinsOf ℚ (⋃ x ∈ T, (· * x) '' centreCutSiegelSet ℚ c u d₁ d₂)
        (fun N => levelOne (𝓞 ℚ) ℚ N ⊓ finiteAdelicGL2Subgroup ℚ) (fun v => heckeGen (𝓞 ℚ) ℚ v) (adelicBox ℚ))
      ψ φ 1 (archRealGLAt hw₀ (splitTorusGL2 (Real.log y / 2)) * t₀))
    μ hc hf₀ hf₀' hode₀ hgr₀ ⟨y₀, hy₀, hfy₀⟩
    (fun t ht => by
      have hre : (t : ℂ).re ≠ 0 := by simpa using ht.ne'
      simp only [dif_pos hre]
      exact hpeel t₀ t ht)
    (fun t ht => by
      have hre : (-(t : ℂ)).re ≠ 0 := by simpa using ht.ne'
      simp only [dif_pos hre]
      refine (congrArg (fun x => μ * x) (hpeelm t₀ t ht)).trans ?_
      linear_combination ((Real.sqrt t : ℝ) : ℂ) ^ (u₁ + u₂ + 1) * hlower t₀ ht₀ t ht)
  obtain ⟨C, hC⟩ := hpack
    (fun z : ℂ => if hz : z.re ≠ 0 then whittakerCoefficient ℚ
      (productionPinsOf ℚ (⋃ x ∈ T, (· * x) '' centreCutSiegelSet ℚ c u d₁ d₂)
        (fun N => levelOne (𝓞 ℚ) ℚ N ⊓ finiteAdelicGL2Subgroup ℚ) (fun v => heckeGen (𝓞 ℚ) ℚ v) (adelicBox ℚ))
      ψ φ 1 (archRealGLAt hw₀ (diagOne (Units.mk0 z.re hz)) * t₀) else 0)
    (fun h => whittakerCoefficient ℚ
      (productionPinsOf ℚ (⋃ x ∈ T, (· * x) '' centreCutSiegelSet ℚ c u d₁ d₂)
        (fun N => levelOne (𝓞 ℚ) ℚ N ⊓ finiteAdelicGL2Subgroup ℚ) (fun v => heckeGen (𝓞 ℚ) ℚ v) (adelicBox ℚ))
      ψ φ 1 (archRealGLAt hw₀ (diagOne (Units.mk0 y₀ hy₀.ne')) * h)
      / whittakerCoefficient ℚ
      (productionPinsOf ℚ (⋃ x ∈ T, (· * x) '' centreCutSiegelSet ℚ c u d₁ d₂)
        (fun N => levelOne (𝓞 ℚ) ℚ N ⊓ finiteAdelicGL2Subgroup ℚ) (fun v => heckeGen (𝓞 ℚ) ℚ v) (adelicBox ℚ))
      ψ φ 1 (archRealGLAt hw₀ (diagOne (Units.mk0 y₀ hy₀.ne')) * t₀))
    hprop ρ hρ

  have hP'cases : P' = RealArchParam.principal u₁ a₁ u₂ a₂ ∨ P' = RealArchParam.principal u₁ a₂ u₂ a₁ := hP'

  have hext : ∀ (v₁ v₂ : ℂ) (b₁ b₂ : ZMod 2), P' = RealArchParam.principal v₁ b₁ v₂ b₂ →
      b₁ ≠ b₂ ∧ v₁ = u₁ ∧ v₂ = u₂ := by
    intro v₁ v₂ b₁ b₂ hv
    rcases hP'cases with h' | h' <;> rw [h'] at hv <;> simp only [RealArchParam.principal.injEq] at hv <;>
      obtain ⟨h1, h2, h3, h4⟩ := hv
    · exact ⟨by rw [← h2, ← h4]; exact hapar, h1.symm, h3.symm⟩
    · exact ⟨by rw [← h2, ← h4]; exact hapar.symm, h1.symm, h3.symm⟩
  have hnotd : ∀ (u₀ : ℂ) (n : ℕ) (hn : 1 ≤ n), P' ≠ RealArchParam.discrete u₀ n hn := by
    intro u₀ n hn hdis
    rcases hP'cases with h' | h' <;> rw [h'] at hdis <;> cases hdis
  have hce : P'.centralExponent = (archR w₀ hw₀).centralExponent ∧ P'.centralSign = (archR w₀ hw₀).centralSign := by
    rcases hP'cases with h' | h' <;> rw [h', hP]
    · exact ⟨rfl, rfl⟩
    · exact ⟨rfl, add_comm a₂ a₁⟩
  have hsplit : ∀ a b : ZMod 2, a ≠ b → (a = 0 ∧ b = 1) ∨ (a = 1 ∧ b = 0) := by decide
  refine ⟨fun _ _ => P', ?_, ?_, ?_, ?_, C, fun par => ⟨φ, fun _ z => ρ * (if hz : z.re ≠ 0 then
      whittakerCoefficient ℚ
        (productionPinsOf ℚ (⋃ x ∈ T, (· * x) '' centreCutSiegelSet ℚ c u d₁ d₂)
        (fun N => levelOne (𝓞 ℚ) ℚ N ⊓ finiteAdelicGL2Subgroup ℚ) (fun v => heckeGen (𝓞 ℚ) ℚ v) (adelicBox ℚ))
        ψ φ 1 (archRealGLAt hw₀ (diagOne (Units.mk0 z.re hz)) * t₀) else 0), k₁,
    rfl, hisoφ, hneφ, hconvφ, ?_, ?_, ?_, hC, ?_, ?_, ?_, ?_⟩⟩
  ·
    intro w' hw'
    obtain rfl : w' = w₀ := Subsingleton.elim _ _
    rcases hP'cases with h1 | h2
    · exact Or.inl (h1.trans hP.symm)
    · exact Or.inr ⟨u₁, u₂, a₁, a₂, hP, h2⟩
  ·
    intro w' hw' v₁ v₂ b₁ b₂ hv
    obtain ⟨-, hv₁, hv₂⟩ := hext v₁ v₂ b₁ b₂ hv
    rw [hv₁, hv₂]
    exact _htype w₀ hw₀ u₁ u₂ a₁ a₂ hP
  ·
    intro w' hw' v₁ v₂ b₁ b₂ hv p hp hu _
    obtain ⟨-, hv₁, hv₂⟩ := hext v₁ v₂ b₁ b₂ hv
    rw [hv₁, hv₂] at hu
    have h1 := _htype w₀ hw₀ u₁ u₂ a₁ a₂ hP
    rw [hu, Complex.intCast_re] at h1
    have h2 : (1 : ℝ) ≤ |(p : ℝ)| := by exact_mod_cast Int.one_le_abs hp
    exact absurd h1 (not_lt.mpr h2)
  ·
    intro w' hw'
    obtain rfl : w' = w₀ := Subsingleton.elim _ _
    show IsArchCompAt ℚ (R.centralChar.comp Subgroup.topEquiv.symm.toMonoidHom) w' (P'.centralExponent + 1)
      (P'.centralSign.val : ℤ)
    rw [hce.1, hce.2]
    exact _hcen w' hw'
  ·
    intro w' hw'
    obtain rfl : w' = w₀ := Subsingleton.elim _ _
    rw [hk1]
    exact hwtφ
  ·
    intro w' hw' v₁ v₂ b₁ b₂ hv
    obtain rfl : w' = w₀ := Subsingleton.elim _ _
    obtain ⟨hb, -, -⟩ := hext v₁ v₂ b₁ b₂ hv
    have hb' : b₁ + par w' ≠ b₂ + par w' := fun h => hb (add_right_cancel h)
    rw [hk1]
    rcases hsplit _ _ hb' with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rw [h1, h2] <;> simp
  ·
    intro w' hw' u₀ n hn hdis
    exact (hnotd u₀ n hn hdis).elim
  ·
    intro w' hw' v₁ v₂ b₁ hv
    exact ((hext v₁ v₂ b₁ b₁ hv).1 rfl).elim
  ·
    intro w' hw' u₀ n hn hdis
    exact (hnotd u₀ n hn hdis).elim
  ·
    intro w' hw' v₁ v₂ b₁ hv
    exact ((hext v₁ v₂ b₁ b₁ hv).1 rfl).elim
  ·
    intro w' hw' b _
    obtain rfl : w' = w₀ := Subsingleton.elim _ _
    exact ⟨max (-u₁.re) (-u₂.re), fun s hs => hmellin b s hs⟩

end S_LanglandsTunnell_exists_whittaker_factorization_add_smul_reflect_lower_of_archCasimir_eigenvector_weightOne_of_ne
end P2MW
export P2MW.S_LanglandsTunnell_exists_whittaker_factorization_add_smul_reflect_lower_of_archCasimir_eigenvector_weightOne_of_ne (solution)
