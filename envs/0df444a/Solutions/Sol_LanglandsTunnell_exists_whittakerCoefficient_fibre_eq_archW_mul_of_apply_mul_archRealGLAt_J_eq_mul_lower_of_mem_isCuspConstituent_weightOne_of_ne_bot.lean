-- Prove2me | solution 1 for LanglandsTunnell.exists_whittakerCoefficient_fibre_eq_archW_mul_of_apply_mul_archRealGLAt_J_eq_mul_lower_of_mem_isCuspConstituent_weightOne_of_ne_bot
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.670037+00:00
-- url     : https://prove2.me/submissions/a156c01d-dad6-5ec3-a3fd-435fff1af9e4

import Mathlib
import Definitions.Def_AutomorphicForm_TranslateSpanOccurrence
import Definitions.Def_AutomorphicForm_ArchDerivCasimir
import Definitions.Def_LanglandsTunnell_JLConverse
import Definitions.Def_LanglandsTunnell_ArchCasimirCompanion
import Definitions.Def_NumberField_AdelicTraceFin
import Definitions.Def_NumberField_TateGlobalZeta
import Definitions.Def_AutomorphicForm_ArchWeightChar
import Definitions.Def_AutomorphicForm_WhittakerCoefficient
import Theorems.Thm_LanglandsTunnell_Converse_ArchDatumR_W_mul_diag_eq_neg_one_pow_mul_of_principal_of_archWeightChar_zero_of_isCasimirEigen
import Theorems.Thm_LanglandsTunnell_Converse_ArchDatumR_W_eq_zero_of_det_neg_of_discrete_of_archWeightChar_of_isCasimirEigen
import Theorems.Thm_LanglandsTunnell_Converse_ArchDatumR_W_eq_zero_of_det_neg_of_principal_of_ne_of_archWeightChar_one_of_isCasimirEigen
import Theorems.Thm_LanglandsTunnell_Converse_ArchDatumR_exists_W_mul_diag_eq_mul_lower_of_principal_of_ne_of_ne_of_archWeightChar_one_of_isCasimirEigen
import Theorems.Thm_AutomorphicForm_archOccursInClassOf_archWeightChar_zero_apply_mul_archRealGLAt_J_eq_of_coversModCentre
import Theorems.Thm_AutomorphicForm_archOccursInClassOf_archWeightChar_one_apply_mul_archRealGLAt_J_eq_mul_lower_of_ne_of_coversModCentre_rat
import Theorems.Thm_LanglandsTunnell_Converse_ArchR_eq_mul_of_unip_law_of_central_law_of_archWeightChar_of_torus_eq_of_sign_det
import Theorems.Thm_AutomorphicForm_whittakerCoefficient_archRealLiftAt_mul_laws_and_torus_ode_of_archCasimirAt_eq_smul_rat
import Theorems.Thm_LanglandsTunnell_Converse_ArchDatumR_laws_and_torus_ode_of_archWeightChar_of_isCasimirEigen
import Theorems.Thm_AutomorphicForm_archDerivAt_E_sub_archDerivAt_Fm_eq_smul_of_hasArchCharacterAtZero_of_isArchSmoothAt
import Theorems.Thm_AutomorphicForm_SmoothCuspRealizationAt_exists_whittakerCoefficient_one_ne_zero_of_continuous_foldr_archDerivAt_rat
import Theorems.Thm_LanglandsTunnell_Converse_ArchDatumR_exists_twist_sign_W_eq_sign_det_mul
import Theorems.Thm_LanglandsTunnell_linearDependent_of_whittaker_ode_of_moderateGrowth_complexParam
import Theorems.Thm_AutomorphicForm_whittakerCoefficient_detOneTorus_eq_zero_of_iterate_lower_eq_zero
import Theorems.Thm_AutomorphicForm_archOccursInClassOf_lower_eq_zero_of_archCasimirAt_eq_smul_of_coversModCentre
import Theorems.Thm_LanglandsTunnell_isArchSmoothAt_whittakerCoefficient_and_archDerivAt_comm
import Theorems.Thm_NumberField_StandardAddChar_isGlobalAddChar_stdAddChar
import Theorems.Thm_AutomorphicForm_whittakerCoefficient_sum_smul_of_continuous
import Definitions.Def_AutomorphicForm_CuspidalConstituent
import Definitions.Def_AutomorphicForm_CuspidalSpectrumCarrier
import Theorems.Thm_AutomorphicForm_CuspidalConstituent_isArchSmoothAt_and_continuous_foldr_archDerivAt_of_mem_cut
import Theorems.Thm_AutomorphicForm_CuspidalSpectrum_exists_hasModulus_of_isAutomorphicFnAt_of_continuous
import Theorems.Thm_AutomorphicForm_CuspidalConstituent_exists_forall_norm_foldr_archDerivAt_le_of_mem_cut
import Definitions.Def_LanglandsTunnell_RankinSelbergEuler
import Definitions.Def_AutomorphicForm_IsotypicCuspSpace
import Definitions.Def_AutomorphicForm_ProductionPinsGeneral
import Definitions.Def_AutomorphicForm_FormalBaseChange
import Definitions.Def_AutomorphicForm_ArchWeightCharTransport
import Definitions.Def_AutomorphicForm_FactorizableTestFn
import Mathlib.Analysis.MellinTransform
import Definitions.Def_NumberField_StandardGlobalAddCharRat
import Definitions.Def_LanglandsTunnell_ConverseData
import Definitions.Def_LanglandsTunnell_ArchBaseChange
import Definitions.Def_AutomorphicForm_WhittakerModelLocal
import Theorems.Thm_AutomorphicForm_eq_stdAddChar_of_isGlobalAddChar_of_apply_infinitePlace_eq_exp
import Theorems.Thm_AutomorphicForm_SiegelCovering_coversModCentre_productionPinsGeneral_D_rat
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

p2m_attr_erase "ext" "IsDedekindDomain.HeightOneSpectrum.adicCompletion.ext"
p2m_attr_erase "ext" "NumberField.InfinitePlace.Completion.ext"
namespace P2MW.S_LanglandsTunnell_exists_whittakerCoefficient_fibre_eq_archW_mul_of_apply_mul_archRealGLAt_J_eq_mul_lower_of_mem_isCuspConstituent_weightOne_of_ne_bot
p2m_attr_erase "instance" "instCountableOfNumberField_definitions RestrictedProduct.SecondCountableTopology_of_principal instCountableElemSetSetsCofinite_definitions instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions AutomorphicForm.compactSpace_maximalCompactAway AutomorphicForm.compactSpace_adelicMaximalCompact AutomorphicForm.isProbabilityMeasure_maximalCompactHaar AutomorphicForm.isHaarMeasure_maximalCompactHaar AutomorphicForm.compactSpace_maximalCompactAt AutomorphicForm.isProbabilityMeasure_maximalCompactAwayHaar AutomorphicForm.isHaarMeasure_maximalCompactAwayHaar AutomorphicForm.isProbabilityMeasure_maximalCompactAtHaar AutomorphicForm.isHaarMeasure_maximalCompactAtHaar IsDedekindDomain.HeightOneSpectrum.Extension.instAlgebraSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnder IsDedekindDomain.HeightOneSpectrum.Extension.instAlgebraSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnder_1 IsDedekindDomain.HeightOneSpectrum.instMulActionHomClassAlgHomTensorProductAdicCompletionForallValEqUnder_definitions IsDedekindDomain.HeightOneSpectrum.Extension.instAlgebraAdicCompletionValEqUnder IsDedekindDomain.HeightOneSpectrum.adicCompletion.instFiniteForallValEqUnderOfFiniteDimensional_definitions IsDedekindDomain.HeightOneSpectrum.instIsBiscalarSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersTensorProductCoeAlgHomTensorAdicCompletionIntegersTo IsDedekindDomain.HeightOneSpectrum.Extension.instContinuousSMulAdicCompletionValEqUnder IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsModuleTopology IsDedekindDomain.HeightOneSpectrum.Extension.instFiniteSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnderOfFiniteDimensional IsDedekindDomain.HeightOneSpectrum.adicCompletion.instFiniteValEqUnderOfFiniteDimensional_definitions instIsBiscalarTensorProductCoeAlgHomBaseChange_of_algebraMap IsDedekindDomain.HeightOneSpectrum.instIsScalarTowerSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnder_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsModuleTopologyPi Submodule.instIsTopologicalModuleSubtypeMem Pi.instTopologicalModule IsTopologicalModule.toContinuousSMul"
p2m_attr_erase "instance" "IsTopologicalModule.toContinuousAdd instFunLike SemialgHomClass.toSemilinearMapClass instCoeTCSemialgHom SemialgHomClass.toRingHomClass SemialgHomClass.instSemialgHom FLT.InfiniteAdeleBaseChange.uniqueSelfExtension NumberField.InfinitePlace.RamifiedExtension.instCoeExtension NumberField.InfinitePlace.UnramifiedExtension.instCoeExtension"
p2m_attr_erase "simp" "ContinuousAddEquiv.restrictedProductPi_apply RestrictedProduct.flatten_homeomorph_apply RestrictedProduct.flatten_homeomorph'_symm_apply ContinuousMulEquiv.restrictedProductPi_symm_apply RestrictedProduct.flatten_homeomorph'_apply RestrictedProduct.flatten_homeomorph_symm_apply ContinuousMulEquiv.restrictedProductPi_apply ContinuousAddEquiv.restrictedProductPi_symm_apply RingEquiv.restrictedProductCongr_symm_apply RingEquiv.restrictedProductCongrRight_apply MulEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductProd_symm_apply_coe Equiv.restrictedProductCongrRight_apply AddEquiv.restrictedProductCongr_apply Equiv.restrictedProductCongrLeft'_symm_apply_apply Equiv.restrictedProductCongr_apply_apply Equiv.restrictedProductCongrLeft_apply_apply RestrictedProduct.flatten_equiv'_apply AddEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductCongr_symm_apply Equiv.restrictedProductCongrRight_symm_apply RestrictedProduct.flatten_equiv'_symm_apply AddEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductCongrLeft'_apply RestrictedProduct.flatten_apply RingEquiv.restrictedProductCongr_apply_apply RingEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductProd_apply RestrictedProduct.flatten_equiv_apply RestrictedProduct.flatten_equiv_symm_apply LinearEquiv.restrictedProductCongrLeft'_apply RestrictedProduct.not_mem_support RestrictedProduct.mem_structureSubring_iff RestrictedProduct.not_mem_mulSupport RestrictedProduct.support_neg RestrictedProduct.mem_indexSupport_iff RestrictedProduct.mulSupport_inv RestrictedProduct.mapAlongLinearMap_apply LocalGL2.coe_localRepSome LocalGL2.coe_diagPi"
p2m_attr_erase "simp" "LocalGL2.coe_localRepInf LocalGL2.coe_localRepSome_inv LocalGL2.coe_unipotentInt LocalGL2.coe_weylInt LocalGL2.coe_diagPi_inv LocalGL2.transposeGL_val LocalGL2.transposeGL_one LocalGL2.swapUnit_val AutomorphicForm.fnTwist_zero AutomorphicForm.fnTwist_apply SemialgHom.baseChange_of_algebraMap_tmul_left SemialgHom.baseChangeRightOfAlgebraMap_apply Pi.semialgHomPi_apply Pi.semialgHom_apply Module.Basis.rightBaseChange_apply LinearEquiv.coe_mulLeft LinearEquiv.coe_mulRight WithVal.semialgebraMap_toFun_ofVal Module.Basis.rightBaseChange_repr IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers.tensorCoe_tmul IsDedekindDomain.HeightOneSpectrum.tensorAdicCompletionIntegersTo_tmul SemialgHom.baseChangeRightOfAlgebraMap_coe IsDedekindDomain.HeightOneSpectrum.adicCompletion.integerBaseChangeLinearEquiv_tmul_apply SemialgHom.baseChange_of_algebraMap_tmul_right IsLocalization.map_moduleTensorEquiv_symm_tmul IsLocalization.leftModuleTensorEquiv_apply IsLocalization.moduleLid_symm_apply IsLocalization.leftModuleTensorEquiv_symm_apply IsLocalization.map_moduleTensorEquiv_tmul IsModuleTopology.continuousLinearEquiv_apply AlgEquiv.extendScalars_symm_apply IsModuleTopology.Module.Basis.equivFun_homeo_symm_apply IsModuleTopology.Module.Basis.equivFun_homeo_apply IsModuleTopology.continuousAlgEquivOfIsBiscalar_apply AlgEquiv.extendScalars_apply IsModuleTopology.continuousLinearEquiv_symm_apply SemialgHom.restrictScalars_toFun SemialgHom.mk.sizeOf_spec SemialgHom.mk.injEq SemialgHom.coe_coe"
p2m_attr_erase "simp" "coe_mk TensorProduct.RightActions.smul_def TensorProduct.RightActions.Module.TensorProduct.comm_symm_apply_tmul TensorProduct.RightActions.LinearMap.baseChange_id TensorProduct.RightActions.algebraMap_eval TensorProduct.RightActions.Module.TensorProduct.comm_apply_tmul TensorProduct.RightActions.Algebra.TensorProduct.comm_symm_apply_tmul TensorProduct.RightActions.Algebra.TensorProduct.comm_apply_tmul AutomorphicForm.mem_sigmaCentralizer_iff M4aHerbrand.ArchSemilocal.psiFactor_tmul M4aHerbrand.ArchSemilocal.psi_apply FLT.InfiniteAdeleBaseChange.evalAlgHom_apply FLT.InfiniteAdeleBaseChange.BaseChangeData.mk.sizeOf_spec FLT.InfiniteAdeleBaseChange.tensorPiAlgHom_tmul_apply FLT.InfiniteAdeleBaseChange.collapsePlaces_apply FLT.InfiniteAdeleBaseChange.tensorPiAlgEquiv_tmul_apply FLT.InfiniteAdeleBaseChange.InfinitePlaceData.mk.sizeOf_spec FLT.InfiniteAdeleBaseChange.InfinitePlaceData.mk.injEq FLT.InfiniteAdeleBaseChange.BaseChangeData.mk.injEq AutomorphicForm.mem_borelSubgroup_iff AutomorphicForm.borelDiagFst_apply_val AutomorphicForm.borelDiagSnd_apply_val AutomorphicForm.mem_inducedSectionSubmodule_iff"

set_option autoImplicit false

noncomputable section

namespace Ws1
namespace WM

p2m_open "IsDedekindDomain NumberField NumberField.AdelicLevel NumberField.AdelicBox AutomorphicForm P2MW.S_LanglandsTunnell_exists_whittakerCoefficient_fibre_eq_archW_mul_of_apply_mul_archRealGLAt_J_eq_mul_lower_of_mem_isCuspConstituent_weightOne_of_ne_bot.AutomorphicForm AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering NumberField.InfinitePlace NumberField.InfinitePlace.Completion"

open NumberField.TateGlobal NumberField.AdelicVolume Matrix
open LanglandsTunnell LanglandsTunnell.RealArchParam LanglandsTunnell.Converse
open scoped Classical

theorem rat_isReal (w : InfinitePlace ℚ) : w.IsReal :=
  (Subsingleton.elim w Rat.infinitePlace) ▸ Rat.isReal_infinitePlace

abbrev hwQ : Rat.infinitePlace.IsReal := Rat.isReal_infinitePlace

theorem eq_of_glArch_eq_of_glFin_eq' {F : Type} [Field F] [NumberField F] {a b : AdelicGL2 (𝓞 F) F}
    (hA : glArch (𝓞 F) F a = glArch (𝓞 F) F b) (hF : glFin (𝓞 F) F a = glFin (𝓞 F) F b) : a = b := by
  apply Units.ext
  ext i j
  refine Prod.ext ?_ ?_
  · have := congrArg (fun m : GL (Fin 2) (InfiniteAdeleRing F) => (m : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing F)) i j) hA
    simpa only [glArch_apply] using this
  · have := congrArg (fun m : GL (Fin 2) (FiniteAdeleRing (𝓞 F) F) => (m : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 F) F)) i j) hF
    simpa only [glFin_apply] using this

def finPart {F : Type} [Field F] [NumberField F] (g : AdelicGL2 (𝓞 F) F) : AdelicGL2 (𝓞 F) F :=
  (adelicArchGLIncl F (glArch (𝓞 F) F g))⁻¹ * g

theorem glArch_finPart {F : Type} [Field F] [NumberField F] (g : AdelicGL2 (𝓞 F) F) :
    glArch (𝓞 F) F (finPart g) = 1 := by
  simp only [finPart, map_mul, map_inv, glArch_adelicArchGLIncl, inv_mul_cancel]

theorem glFin_finPart {F : Type} [Field F] [NumberField F] (g : AdelicGL2 (𝓞 F) F) :
    glFin (𝓞 F) F (finPart g) = glFin (𝓞 F) F g := by
  simp only [finPart, map_mul, map_inv, glFin_adelicArchGLIncl, inv_one, one_mul]

theorem finPart_congr {F : Type} [Field F] [NumberField F] {g g' : AdelicGL2 (𝓞 F) F}
    (h : glFin (𝓞 F) F g = glFin (𝓞 F) F g') : finPart g = finPart g' :=
  eq_of_glArch_eq_of_glFin_eq' (by rw [glArch_finPart, glArch_finPart]) (by rw [glFin_finPart, glFin_finPart, h])

theorem archLift_mul_finPart {F : Type} [Field F] [NumberField F] (g : AdelicGL2 (𝓞 F) F) :
    adelicArchGLIncl F (glArch (𝓞 F) F g) * finPart g = g := by
  rw [finPart, mul_inv_cancel_left]

theorem abs_det_realComponent {K : Type} [Field K] [NumberField K] {w : InfinitePlace K} (hw : w.IsReal)
    (g : AdelicGL2 (𝓞 K) K) : |(realComponent w hw g).det| = archDetNorm w g := by
  have e : realComponent w hw g = (ringEquivRealOfIsReal hw).toRingHom.mapMatrix
      ((archComponent K w (glArch (𝓞 K) K g) : GL (Fin 2) w.Completion) : Matrix (Fin 2) (Fin 2) w.Completion) := by
    ext i j; rfl
  rw [e, ← RingHom.map_det, ← Real.norm_eq_abs]
  exact norm_ringEquivRealOfIsReal hw _

def archC0 : ∀ w : InfinitePlace ℚ, w.IsComplex → ComplexArchParam :=
  fun w hwc => (not_isReal_iff_isComplex.mpr hwc (rat_isReal w)).elim

def dC0 : ∀ (w : InfinitePlace ℚ) (hwc : w.IsComplex), ArchDatumC (archC0 w hwc) :=
  fun w hwc => (not_isReal_iff_isComplex.mpr hwc (rat_isReal w)).elim

theorem archW_rat (P : RealArchParam) (D : ArchDatumR P) (g : AdelicGL2 (𝓞 ℚ) ℚ) :
    archW (fun _ _ => P) archC0 (fun _ _ => D) dC0 g = D.W (realComponent Rat.infinitePlace hwQ g) := by
  unfold archW
  rw [Fintype.prod_subsingleton _ Rat.infinitePlace, dif_pos hwQ]

theorem prod_archDetNorm_rat (g : AdelicGL2 (𝓞 ℚ) ℚ) :
    (∏ v : InfinitePlace ℚ, archDetNorm v g ^ v.mult) = |(realComponent Rat.infinitePlace hwQ g).det| := by
  rw [Fintype.prod_subsingleton _ Rat.infinitePlace, abs_det_realComponent, NumberField.InfinitePlace.mult,
    if_pos hwQ, pow_one]

theorem glArch_ext_rat {k k' : GL (Fin 2) (InfiniteAdeleRing ℚ)}
    (h : archComponent ℚ Rat.infinitePlace k = archComponent ℚ Rat.infinitePlace k') : k = k' := by
  apply Units.ext
  ext i j
  funext w
  obtain rfl : w = Rat.infinitePlace := Subsingleton.elim _ _
  have := congrArg (fun m : GL (Fin 2) Rat.infinitePlace.Completion =>
    (m : Matrix (Fin 2) (Fin 2) Rat.infinitePlace.Completion) i j) h
  simpa only [archComponent_apply] using this

def realGL (g : AdelicGL2 (𝓞 ℚ) ℚ) : GL (Fin 2) ℝ :=
  Matrix.GeneralLinearGroup.map (ringEquivRealOfIsReal hwQ).toRingHom
    (archComponent ℚ Rat.infinitePlace (glArch (𝓞 ℚ) ℚ g))

theorem coe_realGL (g : AdelicGL2 (𝓞 ℚ) ℚ) :
    ((realGL g : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) = realComponent Rat.infinitePlace hwQ g := by
  ext i j
  rfl

theorem glEquiv_symm_realGL (g : AdelicGL2 (𝓞 ℚ) ℚ) :
    glEquivOfRingEquiv (ringEquivRealOfIsReal hwQ).symm (realGL g) =
      archComponent ℚ Rat.infinitePlace (glArch (𝓞 ℚ) ℚ g) := by
  apply Units.ext
  ext i j
  show (ringEquivRealOfIsReal hwQ).symm ((ringEquivRealOfIsReal hwQ).toRingHom
    ((archComponent ℚ Rat.infinitePlace (glArch (𝓞 ℚ) ℚ g) : Matrix (Fin 2) (Fin 2) _) i j)) = _
  exact (ringEquivRealOfIsReal hwQ).symm_apply_apply _

theorem archRealGLAt_realGL_eq (g : AdelicGL2 (𝓞 ℚ) ℚ) :
    archRealGLAt hwQ (realGL g) = adelicArchGLIncl ℚ (glArch (𝓞 ℚ) ℚ g) := by
  apply eq_of_glArch_eq_of_glFin_eq'
  · rw [glArch_adelicArchGLIncl]
    unfold archRealGLAt adelicArchGLInclAt
    rw [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MonoidHom.comp_apply, glArch_adelicArchGLIncl,
      glEquiv_symm_realGL]
    apply glArch_ext_rat
    rw [archComponent_archGLIncl_self]
  · rw [glFin_adelicArchGLIncl]
    unfold archRealGLAt adelicArchGLInclAt
    rw [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MonoidHom.comp_apply, glFin_adelicArchGLIncl]

theorem archRealGLAt_realGL_mul_finPart (g : AdelicGL2 (𝓞 ℚ) ℚ) :
    archRealGLAt hwQ (realGL g) * finPart g = g := by
  rw [archRealGLAt_realGL_eq, archLift_mul_finPart]

theorem archRealLiftAt_realComponent_mul_finPart (g : AdelicGL2 (𝓞 ℚ) ℚ) :
    archRealLiftAt hwQ (Matrix.of.symm (realComponent Rat.infinitePlace hwQ g)) * finPart g = g := by
  have hdet : (Matrix.of (Matrix.of.symm (realComponent Rat.infinitePlace hwQ g))).det ≠ 0 := by
    rw [Equiv.apply_symm_apply, ← coe_realGL]
    exact (Matrix.GeneralLinearGroup.det_ne_zero (realGL g))
  rw [archRealLiftAt_of_det_ne_zero hwQ hdet]
  have : Matrix.GeneralLinearGroup.mkOfDetNeZero (Matrix.of (Matrix.of.symm (realComponent Rat.infinitePlace hwQ g))) hdet
      = realGL g := by
    apply Units.ext
    simp only [Equiv.apply_symm_apply, ← coe_realGL]
    rfl
  rw [this, archRealGLAt_realGL_mul_finPart]

theorem realComponent_det_ne_zero (g : AdelicGL2 (𝓞 ℚ) ℚ) :
    (realComponent Rat.infinitePlace hwQ g).det ≠ 0 := by
  rw [← coe_realGL]; exact Matrix.GeneralLinearGroup.det_ne_zero _

theorem coe_UpperHalfPlane_J_eq_diagonal :
    ((UpperHalfPlane.J : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) = Matrix.diagonal ![(-1 : ℝ), 1] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [UpperHalfPlane.J, Matrix.diagonal]

abbrev Dset (c u d₁ d₂ : ℝ) (T : Finset (AdelicGL2 (𝓞 ℚ) ℚ)) : Set (AdelicGL2 (𝓞 ℚ) ℚ) :=
  ⋃ x ∈ T, (· * x) '' centreCutSiegelSet ℚ c u d₁ d₂

abbrev pinsQ (c u d₁ d₂ : ℝ) (T : Finset (AdelicGL2 (𝓞 ℚ) ℚ)) : CarrierPins ℚ :=
  productionPinsOf ℚ (Dset c u d₁ d₂ T) (fun N => levelOne (𝓞 ℚ) ℚ N ⊓ finiteAdelicGL2Subgroup ℚ)
    (fun v => heckeGen (𝓞 ℚ) ℚ v) (adelicBox ℚ)

abbrev W1 (c u d₁ d₂ : ℝ) (T : Finset (AdelicGL2 (𝓞 ℚ) ℚ)) (φ : AdelicGL2 (𝓞 ℚ) ℚ → ℂ)
    (g : AdelicGL2 (𝓞 ℚ) ℚ) : ℂ :=
  whittakerCoefficient ℚ (pinsQ c u d₁ d₂ T) (NumberField.StandardAddChar.stdAddChar ℚ) φ 1 g

def FIB (c u d₁ d₂ : ℝ) (T : Finset (AdelicGL2 (𝓞 ℚ) ℚ)) (P : RealArchParam)
    (archC : ∀ w : InfinitePlace ℚ, w.IsComplex → ComplexArchParam)
    (dR : ∀ (w : InfinitePlace ℚ) (_hw : w.IsReal), ArchDatumR P)
    (dC : ∀ (w : InfinitePlace ℚ) (hw : w.IsComplex), ArchDatumC (archC w hw))
    (φ : AdelicGL2 (𝓞 ℚ) ℚ → ℂ) : Prop :=
  ∃ g₀ : AdelicGL2 (𝓞 ℚ) ℚ,
    (∃ g : AdelicGL2 (𝓞 ℚ) ℚ, glFin (𝓞 ℚ) ℚ g = glFin (𝓞 ℚ) ℚ g₀ ∧ W1 c u d₁ d₂ T φ g ≠ 0) ∧
    ∃ z : ℂ, ∀ g : AdelicGL2 (𝓞 ℚ) ℚ, glFin (𝓞 ℚ) ℚ g = glFin (𝓞 ℚ) ℚ g₀ →
      W1 c u d₁ d₂ T φ g =
        (((∏ v : InfinitePlace ℚ, NumberField.AdelicVolume.archDetNorm v g ^ v.mult) ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) *
          archW (fun _ _ => P) archC dR dC g * z

theorem fib_of_match (c u d₁ d₂ : ℝ) (T : Finset (AdelicGL2 (𝓞 ℚ) ℚ)) (P : RealArchParam) (D : ArchDatumR P)
    (φ : AdelicGL2 (𝓞 ℚ) ℚ → ℂ) (g₁ : AdelicGL2 (𝓞 ℚ) ℚ) (hg₁ : W1 c u d₁ d₂ T φ g₁ ≠ 0) (z : ℂ)
    (hAB : ∀ x : Matrix (Fin 2) (Fin 2) ℝ, x.det ≠ 0 →
      W1 c u d₁ d₂ T φ (archRealLiftAt hwQ (Matrix.of.symm x) * finPart g₁) =
        z * ((((|x.det| ^ (-(1 / 2 : ℝ)) : ℝ)) : ℂ) * D.W x)) :
    FIB c u d₁ d₂ T P archC0 (fun _ _ => D) dC0 φ := by
  refine ⟨finPart g₁, ⟨g₁, (glFin_finPart g₁).symm, hg₁⟩, z, fun g hg => ?_⟩
  have hfp : finPart g = finPart g₁ := finPart_congr (hg.trans (glFin_finPart g₁))
  have hx := realComponent_det_ne_zero g
  conv_lhs => rw [← archRealLiftAt_realComponent_mul_finPart g, hfp]
  rw [hAB _ hx, archW_rat, prod_archDetNorm_rat]
  ring

theorem fib_of_match_twist (c u d₁ d₂ : ℝ) (T : Finset (AdelicGL2 (𝓞 ℚ) ℚ)) (P : RealArchParam) (D : ArchDatumR P)
    (D' : ArchDatumR (P.twist 0 1)) (hD' : ∀ x : Matrix (Fin 2) (Fin 2) ℝ, D'.W x = (((SignType.sign x.det : ℝ)) : ℂ) * D.W x)
    (φ : AdelicGL2 (𝓞 ℚ) ℚ → ℂ) (g₁ : AdelicGL2 (𝓞 ℚ) ℚ) (hg₁ : W1 c u d₁ d₂ T φ g₁ ≠ 0) (z : ℂ)
    (hAB : ∀ x : Matrix (Fin 2) (Fin 2) ℝ, x.det ≠ 0 →
      W1 c u d₁ d₂ T φ (archRealLiftAt hwQ (Matrix.of.symm x) * finPart g₁) =
        z * ((((SignType.sign x.det : ℝ)) : ℂ) * ((((|x.det| ^ (-(1 / 2 : ℝ)) : ℝ)) : ℂ) * D.W x))) :
    FIB c u d₁ d₂ T (P.twist 0 1) archC0 (fun _ _ => D') dC0 φ := by
  refine ⟨finPart g₁, ⟨g₁, (glFin_finPart g₁).symm, hg₁⟩, z, fun g hg => ?_⟩
  have hfp : finPart g = finPart g₁ := finPart_congr (hg.trans (glFin_finPart g₁))
  have hx := realComponent_det_ne_zero g
  conv_lhs => rw [← archRealLiftAt_realComponent_mul_finPart g, hfp]
  rw [hAB _ hx, archW_rat, hD', prod_archDetNorm_rat]
  ring

abbrev ray (ε y : ℝ) : Matrix (Fin 2) (Fin 2) ℝ := !![ε * Real.sqrt y, 0; 0, (Real.sqrt y)⁻¹]

abbrev Jm : Matrix (Fin 2) (Fin 2) ℝ := Matrix.diagonal ![(-1 : ℝ), 1]

theorem ray_mul_Jm (y : ℝ) : ray 1 y * Jm = ray (-1) y := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [ray, Jm, Matrix.mul_apply, Fin.sum_univ_two]

theorem det_ray (ε y : ℝ) (hε : ε = 1 ∨ ε = -1) (hy : 0 < y) : (ray ε y).det = ε := by
  rw [ray, Matrix.det_fin_two_of]
  have hs : Real.sqrt y ≠ 0 := (Real.sqrt_pos.mpr hy).ne'
  rcases hε with rfl | rfl <;> field_simp <;> ring

structure Laws (A : Matrix (Fin 2) (Fin 2) ℝ → ℂ) (k : ℤ) (e : ℂ) : Prop where
  unip : ∀ (t : ℝ) (x : Matrix (Fin 2) (Fin 2) ℝ), x.det ≠ 0 → A (ArchR.unip t * x) = ArchR.psi t * A x
  cent : ∀ (t : ℝ) (x : Matrix (Fin 2) (Fin 2) ℝ), 0 < t → x.det ≠ 0 → A (t • x) = ((t : ℂ) ^ e) * A x
  wt : ∀ (r : rowIsometrySubgroup₀ ℝ) (x : GL (Fin 2) ℝ),
      A ((x * (r : GL (Fin 2) ℝ) : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) =
        (archWeightCharℝ k r : ℂ) * A (x : Matrix (Fin 2) (Fin 2) ℝ)

private structure _root_.Ws1.WM.Sheet (A : Matrix (Fin 2) (Fin 2) ℝ → ℂ) (ν : ℂ) (kk ε : ℝ) : Prop where
  d1 : DifferentiableOn ℝ (fun y : ℝ => A (ray ε y)) (Set.Ioi 0)
  d2 : DifferentiableOn ℝ (deriv (fun y : ℝ => A (ray ε y))) (Set.Ioi 0)
  ode : ∀ y : ℝ, 0 < y →
        (y : ℂ) ^ 2 * deriv (deriv (fun y : ℝ => A (ray ε y))) y
            + (1 / 4 - ν ^ 2 + 2 * (Real.pi : ℂ) * ((ε * kk : ℝ) : ℂ) * (y : ℂ) - 4 * (Real.pi : ℂ) ^ 2 * (y : ℂ) ^ 2)
              * A (ray ε y) = 0
  bdd : ∃ C N : ℝ, ∀ y : ℝ, 1 ≤ y → ‖A (ray ε y)‖ ≤ C * y ^ N

p2m_export "Ws1.WM" "Sheet"
p2m_export_all "Ws1.WM" "Sheet"

theorem ray_prop {A B : Matrix (Fin 2) (Fin 2) ℝ → ℂ} {ν : ℂ} {kk ε : ℝ}
    (hA : Sheet A ν kk ε) (hB : Sheet B ν kk ε) (hB0 : ∃ y : ℝ, 0 < y ∧ B (ray ε y) ≠ 0) :
    ∃ z : ℂ, ∀ y : ℝ, 0 < y → A (ray ε y) = z * B (ray ε y) := by
  obtain ⟨c₁, c₂, hc, hlin⟩ :=
    LanglandsTunnell.linearDependent_of_whittaker_ode_of_moderateGrowth_complexParam ν (ε * kk)
      (fun y => A (ray ε y)) (fun y => B (ray ε y)) hA.d1 hA.d2 hA.ode hA.bdd hB.d1 hB.d2 hB.ode hB.bdd
  have hc₁ : c₁ ≠ 0 := by
    intro h0
    obtain ⟨y, hy, hBy⟩ := hB0
    have := hlin y hy
    rw [h0, zero_mul, zero_add] at this
    rcases mul_eq_zero.mp this with h2 | h2
    · exact hc (Prod.ext h0 h2)
    · exact hBy h2
  refine ⟨-c₂ / c₁, fun y hy => ?_⟩
  have := hlin y hy
  field_simp
  linear_combination this

theorem ext_component {A B : Matrix (Fin 2) (Fin 2) ℝ → ℂ} {k : ℤ} {e : ℂ} (hA : Laws A k e) (hB : Laws B k e)
    (z : ℂ) (ε : ℝ) (hε : ε = 1 ∨ ε = -1) (htor : ∀ y : ℝ, 0 < y → A (ray ε y) = z * B (ray ε y))
    (x : Matrix (Fin 2) (Fin 2) ℝ) (hx : 0 < ε * x.det) : A x = z * B x :=
  LanglandsTunnell.Converse.ArchR.eq_mul_of_unip_law_of_central_law_of_archWeightChar_of_torus_eq_of_sign_det
    A B k e z hA.unip hB.unip hA.cent hB.cent hA.wt hB.wt ε hε htor x hx

theorem Laws.signTwist {B : Matrix (Fin 2) (Fin 2) ℝ → ℂ} {k : ℤ} {e : ℂ} (hB : Laws B k e) :
    Laws (fun x => (((SignType.sign x.det : ℝ)) : ℂ) * B x) k e := by
  refine ⟨fun t x hx => ?_, fun t x ht hx => ?_, fun r x => ?_⟩
  · rw [hB.unip t x hx, Matrix.det_mul]
    simp [ArchR.unip, Matrix.det_fin_two_of]
    ring
  · rw [hB.cent t x ht hx, Matrix.det_smul, Fintype.card_fin]
    have : SignType.sign (t ^ 2 * x.det) = SignType.sign x.det := by
      rw [_root_.sign_mul, sign_pos (by positivity), one_mul]
    rw [this]; ring
  · rw [hB.wt r x]
    have hr : ((r : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ).det = 1 := ((mem_rowIsometrySubgroup₀_iff ℝ).mp r.2).1
    rw [Units.val_mul, Matrix.det_mul, hr, mul_one]
    ring

theorem eq_zero_of_rays {B : Matrix (Fin 2) (Fin 2) ℝ → ℂ} {k : ℤ} {e : ℂ} (hB : Laws B k e)
    (h1 : ∀ y : ℝ, 0 < y → B (ray 1 y) = 0) (h2 : ∀ y : ℝ, 0 < y → B (ray (-1) y) = 0)
    (x : Matrix (Fin 2) (Fin 2) ℝ) (hx : x.det ≠ 0) : B x = 0 := by
  rcases lt_or_gt_of_ne hx with hlt | hgt
  · have := ext_component hB hB 0 (-1) (Or.inr rfl) (fun y hy => by rw [h2 y hy, zero_mul]) x (by linarith)
    rwa [zero_mul] at this
  · have := ext_component hB hB 0 1 (Or.inl rfl) (fun y hy => by rw [h1 y hy, zero_mul]) x (by linarith)
    rwa [zero_mul] at this

theorem match_of_vanishing {A B : Matrix (Fin 2) (Fin 2) ℝ → ℂ} {k : ℤ} {e ν : ℂ} {kk : ℝ}
    (hA : Laws A k e) (hB : Laws B k e) (hA1 : Sheet A ν kk 1) (hB1 : Sheet B ν kk 1)
    (hAm : ∀ y : ℝ, 0 < y → A (ray (-1) y) = 0) (hBm : ∀ x : Matrix (Fin 2) (Fin 2) ℝ, x.det < 0 → B x = 0)
    (hB0 : ∃ x : Matrix (Fin 2) (Fin 2) ℝ, x.det ≠ 0 ∧ B x ≠ 0) :
    ∃ z : ℂ, ∀ x : Matrix (Fin 2) (Fin 2) ℝ, x.det ≠ 0 → A x = z * B x := by
  have hBray : ∃ y : ℝ, 0 < y ∧ B (ray 1 y) ≠ 0 := by
    by_contra h
    push Not at h
    obtain ⟨x, hx, hBx⟩ := hB0
    exact hBx (eq_zero_of_rays hB h (fun y hy => hBm _ (by rw [det_ray _ _ (Or.inr rfl) hy]; norm_num)) x hx)
  obtain ⟨z, hz⟩ := ray_prop hA1 hB1 hBray
  refine ⟨z, fun x hx => ?_⟩
  rcases lt_or_gt_of_ne hx with hlt | hgt
  · exact ext_component hA hB z (-1) (Or.inr rfl)
      (fun y hy => by rw [hAm y hy, hBm _ (by rw [det_ray _ _ (Or.inr rfl) hy]; norm_num), mul_zero]) x (by linarith)
  · exact ext_component hA hB z 1 (Or.inl rfl) hz x (by linarith)

theorem match_of_parity {A B : Matrix (Fin 2) (Fin 2) ℝ → ℂ} {k : ℤ} {e ν : ℂ} {kk : ℝ}
    (hA : Laws A k e) (hB : Laws B k e) (hA1 : Sheet A ν kk 1) (hB1 : Sheet B ν kk 1)
    (εA : ℂ) (hεA : εA = 1 ∨ εA = -1) (hAJ : ∀ x : Matrix (Fin 2) (Fin 2) ℝ, x.det ≠ 0 → A (x * Jm) = εA * A x)
    (η : ℂ) (hη : η = 1 ∨ η = -1) (hBJ : ∀ x : Matrix (Fin 2) (Fin 2) ℝ, x.det ≠ 0 → B (x * Jm) = η * B x)
    (hB0 : ∃ x : Matrix (Fin 2) (Fin 2) ℝ, x.det ≠ 0 ∧ B x ≠ 0) :
    ∃ z : ℂ, (∀ x : Matrix (Fin 2) (Fin 2) ℝ, x.det ≠ 0 → A x = z * B x) ∨
      (∀ x : Matrix (Fin 2) (Fin 2) ℝ, x.det ≠ 0 → A x = z * ((((SignType.sign x.det : ℝ)) : ℂ) * B x)) := by
  have hd1 : ∀ y : ℝ, 0 < y → (ray 1 y).det ≠ 0 := fun y hy => by rw [det_ray _ _ (Or.inl rfl) hy]; norm_num

  have hBray : ∃ y : ℝ, 0 < y ∧ B (ray 1 y) ≠ 0 := by
    by_contra h
    push Not at h
    obtain ⟨x, hx, hBx⟩ := hB0
    refine hBx (eq_zero_of_rays hB h (fun y hy => ?_) x hx)
    rw [← ray_mul_Jm, hBJ _ (hd1 y hy), h y hy, mul_zero]
  obtain ⟨z, hz⟩ := ray_prop hA1 hB1 hBray
  have hpos : ∀ x : Matrix (Fin 2) (Fin 2) ℝ, 0 < x.det → A x = z * B x :=
    fun x hx => ext_component hA hB z 1 (Or.inl rfl) hz x (by linarith)

  have hneg_ray : ∀ y : ℝ, 0 < y → A (ray (-1) y) = (εA * η) * (z * B (ray (-1) y)) := by
    intro y hy
    rw [← ray_mul_Jm, hAJ _ (hd1 y hy), hBJ _ (hd1 y hy), hz y hy]
    have hη2 : η * η = 1 := by rcases hη with rfl | rfl <;> norm_num
    linear_combination (-(εA * z * B (ray 1 y))) * hη2
  by_cases hs : εA * η = 1
  · refine ⟨z, Or.inl fun x hx => ?_⟩
    rcases lt_or_gt_of_ne hx with hlt | hgt
    · exact ext_component hA hB z (-1) (Or.inr rfl) (fun y hy => by rw [hneg_ray y hy, hs, one_mul]) x (by linarith)
    · exact hpos x hgt
  · have hs' : εA * η = -1 := by
      rcases hεA with rfl | rfl <;> rcases hη with rfl | rfl <;> simp_all
    refine ⟨z, Or.inr fun x hx => ?_⟩
    rcases lt_or_gt_of_ne hx with hlt | hgt
    · have := ext_component hA hB.signTwist z (-1) (Or.inr rfl) (fun y hy => by
        rw [hneg_ray y hy, hs', det_ray _ _ (Or.inr rfl) hy]
        simp) x (by linarith)
      simpa using this
    · rw [hpos x hgt, sign_pos hgt]
      simp

theorem occ_mono {Ds : Set (AdelicGL2 (𝓞 ℚ) ℚ)} {Θ : HeckeEigensystem ℚ ℂ} {P Q : (AdelicGL2 (𝓞 ℚ) ℚ → ℂ) → Prop}
    (h : ArchOccursInClassOf ℚ Ds Θ P) (hPQ : ∀ φ, P φ → Q φ) : ArchOccursInClassOf ℚ Ds Θ Q := by
  obtain ⟨Θ', hΘ', R', hR', hP⟩ := h
  exact ⟨Θ', hΘ', R', hR', hPQ _ hP⟩

theorem W1_mul_right (c u d₁ d₂ : ℝ) (T : Finset (AdelicGL2 (𝓞 ℚ) ℚ)) (φ : AdelicGL2 (𝓞 ℚ) ℚ → ℂ)
    (g h : AdelicGL2 (𝓞 ℚ) ℚ) : W1 c u d₁ d₂ T φ (g * h) = W1 c u d₁ d₂ T (fun y => φ (y * h)) g := by
  simp only [W1, whittakerCoefficient, mul_assoc]

theorem W1_const_mul (c u d₁ d₂ : ℝ) (T : Finset (AdelicGL2 (𝓞 ℚ) ℚ)) (φ : AdelicGL2 (𝓞 ℚ) ℚ → ℂ) (a : ℂ)
    (g : AdelicGL2 (𝓞 ℚ) ℚ) : W1 c u d₁ d₂ T (fun y => a * φ y) g = a * W1 c u d₁ d₂ T φ g := by
  simp only [W1, whittakerCoefficient, mul_assoc]
  exact MeasureTheory.integral_const_mul _ _

theorem globalPoints_unipotentGL2 (β : ℚ) :
    globalPoints (𝓞 ℚ) ℚ (unipotentGL2 β) = unipotentGL2 (algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ) β) := by
  apply Units.ext; ext i j
  change algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ) (((unipotentGL2 β : GL (Fin 2) ℚ) : Matrix (Fin 2) (Fin 2) ℚ) i j) =
    ((unipotentGL2 (algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ) β) : GL (Fin 2) _) : Matrix (Fin 2) (Fin 2) _) i j
  rw [unipotentGL2_coe, unipotentGL2_coe]
  fin_cases i <;> fin_cases j <;> simp

theorem det_mul_Jm (x : Matrix (Fin 2) (Fin 2) ℝ) : (x * Jm).det = -x.det := by
  rw [Matrix.det_mul]; simp [Jm, Matrix.det_diagonal, Fin.prod_univ_two]

theorem A_parity (c u d₁ d₂ : ℝ) (T : Finset (AdelicGL2 (𝓞 ℚ) ℚ)) {φ : AdelicGL2 (𝓞 ℚ) ℚ → ℂ} {ε : ℂ}
    (hJ : ∀ g, φ (g * archRealGLAt hwQ UpperHalfPlane.J) = ε * φ g)
    (g₀ : AdelicGL2 (𝓞 ℚ) ℚ) (hg₀ : glArch (𝓞 ℚ) ℚ g₀ = 1) (x : Matrix (Fin 2) (Fin 2) ℝ) (hx : x.det ≠ 0) :
    W1 c u d₁ d₂ T φ (archRealLiftAt hwQ (Matrix.of.symm (x * Jm)) * g₀) =
      ε * W1 c u d₁ d₂ T φ (archRealLiftAt hwQ (Matrix.of.symm x) * g₀) := by
  have hx' : (Matrix.of (Matrix.of.symm x)).det ≠ 0 := by rwa [Equiv.apply_symm_apply]
  have : archRealLiftAt hwQ (Matrix.of.symm (x * Jm)) =
      archRealLiftAt hwQ (Matrix.of.symm x) * archRealGLAt hwQ UpperHalfPlane.J := by
    rw [archRealLiftAt_mul_archRealGLAt hwQ hx', coe_UpperHalfPlane_J_eq_diagonal, Equiv.apply_symm_apply]
  rw [this, mul_assoc, archRealGLAt_mul_comm_of_glArch_eq_one hwQ _ hg₀, ← mul_assoc, W1_mul_right,
    show (fun y => φ (y * archRealGLAt hwQ UpperHalfPlane.J)) = fun y => ε * φ y from funext hJ, W1_const_mul]

theorem B_ne_zero {P : RealArchParam} (D : ArchDatumR P) (hDnv : ∃ g : GL (Fin 2) ℝ, D.W g ≠ 0) :
    ∃ x : Matrix (Fin 2) (Fin 2) ℝ, x.det ≠ 0 ∧ (((|x.det| ^ (-(1 / 2 : ℝ)) : ℝ)) : ℂ) * D.W x ≠ 0 := by
  obtain ⟨g, hg⟩ := hDnv
  refine ⟨g, Matrix.GeneralLinearGroup.det_ne_zero g, mul_ne_zero ?_ hg⟩
  exact Complex.ofReal_ne_zero.mpr (Real.rpow_pos_of_pos (abs_pos.mpr (Matrix.GeneralLinearGroup.det_ne_zero g)) _).ne'

theorem bdd_nat {f : ℝ → ℂ} (h : ∃ C N : ℝ, ∀ y : ℝ, 1 ≤ y → ‖f y‖ ≤ C * y ^ N) :
    ∃ (C : ℝ) (N : ℕ), ∀ y : ℝ, 1 ≤ y → ‖f y‖ ≤ C * y ^ N := by
  obtain ⟨C, N, hC⟩ := h
  refine ⟨max C 0, ⌈max N 0⌉₊, fun y hy => (hC y hy).trans ?_⟩
  have hy0 : 0 ≤ y := zero_le_one.trans hy
  calc C * y ^ N ≤ max C 0 * y ^ N := mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.rpow_nonneg hy0 _)
    _ ≤ max C 0 * y ^ (⌈max N 0⌉₊ : ℝ) :=
        mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hy ((le_max_left _ _).trans (Nat.le_ceil _)))
          (le_max_right _ _)
    _ = max C 0 * y ^ ⌈max N 0⌉₊ := by rw [Real.rpow_natCast]

theorem exists_sq_eq (z : ℂ) : ∃ ν : ℂ, ν ^ 2 = z := IsAlgClosed.exists_pow_nat_eq z (by norm_num)

def Concl (c u d₁ d₂ : ℝ) (T : Finset (AdelicGL2 (𝓞 ℚ) ℚ)) (Φ : HeckeEigensystem ℚ ℂ) (P : RealArchParam)
    (D : ArchDatumR P) : Prop :=
  (∃ (archC : ∀ w : InfinitePlace ℚ, w.IsComplex → ComplexArchParam)
      (dC : ∀ (w : InfinitePlace ℚ) (hw : w.IsComplex), ArchDatumC (archC w hw)),
      ArchOccursInClassOf ℚ (Dset c u d₁ d₂ T) Φ (FIB c u d₁ d₂ T P archC (fun _ _ => D) dC)) ∨
  (∃ (D' : ArchDatumR (P.twist 0 1)) (archC : ∀ w : InfinitePlace ℚ, w.IsComplex → ComplexArchParam)
      (dC : ∀ (w : InfinitePlace ℚ) (hw : w.IsComplex), ArchDatumC (archC w hw)),
      (∀ x : Matrix (Fin 2) (Fin 2) ℝ, D'.W x = (((SignType.sign x.det : ℝ)) : ℂ) * D.W x) ∧
      ArchOccursInClassOf ℚ (Dset c u d₁ d₂ T) Φ (FIB c u d₁ d₂ T (P.twist 0 1) archC (fun _ _ => D') dC))

def Wit (k : ℤ) (lam e : ℂ) (φ : AdelicGL2 (𝓞 ℚ) ℚ → ℂ) : Prop :=
  HasArchCharacterAt₀ ℚ Rat.infinitePlace ((archWeightCharℝ k).comp (rowIsometrySubgroup₀Map (ringEquivRealOfIsReal Rat.isReal_infinitePlace) (norm_ringEquivRealOfIsReal Rat.isReal_infinitePlace))) φ ∧
    IsArchSmoothAt Rat.isReal_infinitePlace φ ∧
    (∀ l : List ArchDir, Continuous (l.foldr (archDerivAt Rat.isReal_infinitePlace) φ) ∧
      ∀ e₁ e₂ : ℝ, 0 < e₁ → e₁ < e₂ → ∃ B : ℝ, ∀ g : AdelicGL2 (𝓞 ℚ) ℚ,
        NumberField.TateGlobal.ideleNorm ℚ (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc e₁ e₂ →
          ‖l.foldr (archDerivAt Rat.isReal_infinitePlace) φ g‖ ≤ B) ∧
    archCasimirAt Rat.isReal_infinitePlace φ = lam • φ ∧
    (∀ t : ℝˣ, (0 : ℝ) < (t : ℝ) → ∀ g : AdelicGL2 (𝓞 ℚ) ℚ,
      φ (adelicArchGLInclAt ℚ Rat.infinitePlace (Matrix.GeneralLinearGroup.map (InfinitePlace.Completion.ringEquivRealOfIsReal Rat.isReal_infinitePlace).symm.toRingHom
        (Matrix.GeneralLinearGroup.scalar (Fin 2) t)) * g) = ((t : ℝ) : ℂ) ^ e * φ g)

abbrev Afun (c u d₁ d₂ : ℝ) (T : Finset (AdelicGL2 (𝓞 ℚ) ℚ)) (φ : AdelicGL2 (𝓞 ℚ) ℚ → ℂ) (g₁ : AdelicGL2 (𝓞 ℚ) ℚ)
    (x : Matrix (Fin 2) (Fin 2) ℝ) : ℂ :=
  W1 c u d₁ d₂ T φ (archRealLiftAt hwQ (Matrix.of.symm x) * finPart g₁)

abbrev Bfun {P : RealArchParam} (D : ArchDatumR P) (x : Matrix (Fin 2) (Fin 2) ℝ) : ℂ :=
  (((|x.det| ^ (-(1 / 2 : ℝ)) : ℝ)) : ℂ) * D.W x

theorem phi_pkg (c u d₁ d₂ : ℝ) (T : Finset (AdelicGL2 (𝓞 ℚ) ℚ)) {Θ' : HeckeEigensystem ℚ ℂ}
    (R : SmoothCuspRealizationAt ℚ (pinsQ c u d₁ d₂ T) Θ'.toRawCentral)
    (hR : IsGenuineCuspRealizationAt ℚ (pinsQ c u d₁ d₂ T) Θ'.toRawCentral R)
    (k : ℤ) (lam e ν : ℂ) (hν : ν ^ 2 = 1 / 4 - lam) (hw : Wit k lam e R.toFun) :
    ∃ g₁ : AdelicGL2 (𝓞 ℚ) ℚ, W1 c u d₁ d₂ T R.toFun g₁ ≠ 0 ∧
      Laws (Afun c u d₁ d₂ T R.toFun g₁) k e ∧ ∀ ε : ℝ, (ε = 1 ∨ ε = -1) → Sheet (Afun c u d₁ d₂ T R.toFun g₁) ν k ε := by
  obtain ⟨hk, hsm, hreg, hΩ, hcent⟩ := hw
  obtain ⟨g₁, hg₁⟩ :=
    AutomorphicForm.SmoothCuspRealizationAt.exists_whittakerCoefficient_one_ne_zero_of_continuous_foldr_archDerivAt_rat
      (Dset c u d₁ d₂ T) Θ'.toRawCentral R hR hsm (fun l => (hreg l).1)
  obtain ⟨hN, hZ, hK, hT⟩ :=
    AutomorphicForm.whittakerCoefficient_archRealLiftAt_mul_laws_and_torus_ode_of_archCasimirAt_eq_smul_rat
      (Dset c u d₁ d₂ T) k lam e ν hν R.toFun hR (fun γ g => R.left_invariant γ g) hk hsm hreg hΩ hcent
      (finPart g₁) (glArch_finPart g₁)
  exact ⟨g₁, hg₁, ⟨hN, hZ, hK⟩, fun ε hε => let h := hT ε hε; ⟨h.1, h.2.1, h.2.2.1, h.2.2.2⟩⟩

theorem B_pkg {P : RealArchParam} (D : ArchDatumR P) (k : ℤ) (ν : ℂ) (hν : ν ^ 2 = 1 / 4 - P.laplaceEigenvalue)
    (hDW : ∀ (r : rowIsometrySubgroup₀ ℝ) (x : GL (Fin 2) ℝ),
      D.W ((x * (r : GL (Fin 2) ℝ) : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) =
        (archWeightCharℝ k r : ℂ) * D.W (x : Matrix (Fin 2) (Fin 2) ℝ))
    (hDE : ArchCasimir.IsCasimirEigen D) :
    Laws (Bfun D) k P.centralExponent ∧ ∀ ε : ℝ, (ε = 1 ∨ ε = -1) → Sheet (Bfun D) ν k ε := by
  obtain ⟨hN, hZ, hK, hT⟩ :=
    LanglandsTunnell.Converse.ArchDatumR.laws_and_torus_ode_of_archWeightChar_of_isCasimirEigen P D k ν hν hDW hDE
  exact ⟨⟨hN, hZ, hK⟩, fun ε hε => let h := hT ε hε; ⟨h.1, h.2.1, h.2.2.1, h.2.2.2⟩⟩

theorem concl_of_match (c u d₁ d₂ : ℝ) (T : Finset (AdelicGL2 (𝓞 ℚ) ℚ)) (Φ : HeckeEigensystem ℚ ℂ) (P : RealArchParam)
    (D : ArchDatumR P) {Θ' : HeckeEigensystem ℚ ℂ} (hΘ' : Θ'.AgreesAwayFromFinite Φ)
    (R : SmoothCuspRealizationAt ℚ (pinsQ c u d₁ d₂ T) Θ'.toRawCentral)
    (hR : IsGenuineCuspRealizationAt ℚ (pinsQ c u d₁ d₂ T) Θ'.toRawCentral R)
    (g₁ : AdelicGL2 (𝓞 ℚ) ℚ) (hg₁ : W1 c u d₁ d₂ T R.toFun g₁ ≠ 0) (z : ℂ)
    (hAB : ∀ x : Matrix (Fin 2) (Fin 2) ℝ, x.det ≠ 0 → Afun c u d₁ d₂ T R.toFun g₁ x = z * Bfun D x) :
    Concl c u d₁ d₂ T Φ P D :=
  Or.inl ⟨archC0, dC0, Θ', hΘ', R, hR, fib_of_match c u d₁ d₂ T P D R.toFun g₁ hg₁ z hAB⟩

theorem concl_of_match_twist (c u d₁ d₂ : ℝ) (T : Finset (AdelicGL2 (𝓞 ℚ) ℚ)) (Φ : HeckeEigensystem ℚ ℂ)
    (P : RealArchParam) (D : ArchDatumR P) {Θ' : HeckeEigensystem ℚ ℂ} (hΘ' : Θ'.AgreesAwayFromFinite Φ)
    (R : SmoothCuspRealizationAt ℚ (pinsQ c u d₁ d₂ T) Θ'.toRawCentral)
    (hR : IsGenuineCuspRealizationAt ℚ (pinsQ c u d₁ d₂ T) Θ'.toRawCentral R)
    (g₁ : AdelicGL2 (𝓞 ℚ) ℚ) (hg₁ : W1 c u d₁ d₂ T R.toFun g₁ ≠ 0) (z : ℂ)
    (hAB : ∀ x : Matrix (Fin 2) (Fin 2) ℝ, x.det ≠ 0 →
      Afun c u d₁ d₂ T R.toFun g₁ x = z * ((((SignType.sign x.det : ℝ)) : ℂ) * Bfun D x)) :
    Concl c u d₁ d₂ T Φ P D := by
  obtain ⟨D', hD', -, -, -⟩ := LanglandsTunnell.Converse.ArchDatumR.exists_twist_sign_W_eq_sign_det_mul P D
  exact Or.inr ⟨D', archC0, dC0, hD', Θ', hΘ', R, hR, fib_of_match_twist c u d₁ d₂ T P D D' hD' R.toFun g₁ hg₁ z hAB⟩

theorem A_ray_neg_eq_zero (c u d₁ d₂ : ℝ) (T : Finset (AdelicGL2 (𝓞 ℚ) ℚ)) {Θ' : HeckeEigensystem ℚ ℂ}
    (R : SmoothCuspRealizationAt ℚ (pinsQ c u d₁ d₂ T) Θ'.toRawCentral)
    (hR : IsGenuineCuspRealizationAt ℚ (pinsQ c u d₁ d₂ T) Θ'.toRawCentral R)
    (k₀ : ℕ) (hk₀ : 1 ≤ k₀) (lam e _ν : ℂ) (hw : Wit (k₀ : ℤ) lam e R.toFun)
    (hlam : lam = ((k₀ : ℂ) / 2) * (1 - (k₀ : ℂ) / 2))
    (hL : archDerivAt hwQ ArchDir.H R.toFun - Complex.I • (archDerivAt hwQ ArchDir.E R.toFun + archDerivAt hwQ ArchDir.Fm R.toFun) = 0)
    (g₁ : AdelicGL2 (𝓞 ℚ) ℚ) (hbdd : ∃ C N : ℝ, ∀ y : ℝ, 1 ≤ y → ‖Afun c u d₁ d₂ T R.toFun g₁ (ray (-1) y)‖ ≤ C * y ^ N)
    (y : ℝ) (hy : 0 < y) : Afun c u d₁ d₂ T R.toFun g₁ (ray (-1) y) = 0 := by
  obtain ⟨hk, hsm, hreg, hΩ, -⟩ := hw
  obtain ⟨C, N, hC⟩ := bdd_nat hbdd
  have hg₀ : archComponent ℚ Rat.infinitePlace (glArch (𝓞 ℚ) ℚ (finPart g₁)) = 1 := by
    rw [glArch_finPart, map_one]
  have hm := AutomorphicForm.archDerivAt_E_sub_archDerivAt_Fm_eq_smul_of_hasArchCharacterAtZero_of_isArchSmoothAt hwQ (k₀ : ℤ)
    R.toFun hsm hk
  have hcomm : ∀ t : ℝ, archRealLiftAt hwQ (Matrix.of.symm (ray (-1) t)) * finPart g₁ =
      finPart g₁ * archRealLiftAt hwQ (Matrix.of.symm !![-(1 : ℝ) * Real.sqrt t, 0; 0, (Real.sqrt t)⁻¹]) := by
    intro t
    rw [archRealLiftAt_mul_comm_of_glArch_eq_one hwQ _ (glArch_finPart g₁)]
  have h := AutomorphicForm.whittakerCoefficient_detOneTorus_eq_zero_of_iterate_lower_eq_zero ℚ (Dset c u d₁ d₂ T)
    Rat.infinitePlace hwQ R.toFun hR
    (fun β g => by rw [← globalPoints_unipotentGL2]; exact R.left_invariant _ g)
    hsm (fun l => (hreg l).1) 1 (Or.inl rfl) k₀ 0 hk₀ (k₀ : ℤ) (by simp)
    (by rw [hm]) (by rw [hΩ, hlam]) (by
      rw [zero_add, Function.iterate_one]
      simpa using hL)
    (finPart g₁) hg₀ C N (fun t ht => by
      have := hC t ht
      rw [Function.iterate_zero, id]
      rw [Afun, hcomm t] at this
      simpa using this) y hy
  rw [Afun, hcomm y]
  simpa using h

theorem concl_vanishing (c u d₁ d₂ : ℝ) (T : Finset (AdelicGL2 (𝓞 ℚ) ℚ)) (Φ : HeckeEigensystem ℚ ℂ) (P : RealArchParam)
    (D : ArchDatumR P) (k₀ : ℕ) (hk₀ : 1 ≤ k₀)
    (hlam : P.laplaceEigenvalue = ((k₀ : ℂ) / 2) * (1 - (k₀ : ℂ) / 2))
    (hDW : ∀ (r : rowIsometrySubgroup₀ ℝ) (x : GL (Fin 2) ℝ),
      D.W ((x * (r : GL (Fin 2) ℝ) : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) =
        (archWeightCharℝ (k₀ : ℤ) r : ℂ) * D.W (x : Matrix (Fin 2) (Fin 2) ℝ))
    (hDE : ArchCasimir.IsCasimirEigen D) (hDnv : ∃ g : GL (Fin 2) ℝ, D.W g ≠ 0)
    (hBm : ∀ x : Matrix (Fin 2) (Fin 2) ℝ, x.det < 0 → D.W x = 0)
    {Θ' : HeckeEigensystem ℚ ℂ} (hΘ' : Θ'.AgreesAwayFromFinite Φ)
    (R : SmoothCuspRealizationAt ℚ (pinsQ c u d₁ d₂ T) Θ'.toRawCentral)
    (hR : IsGenuineCuspRealizationAt ℚ (pinsQ c u d₁ d₂ T) Θ'.toRawCentral R)
    (hw : Wit (k₀ : ℤ) P.laplaceEigenvalue P.centralExponent R.toFun)
    (hL : archDerivAt hwQ ArchDir.H R.toFun - Complex.I • (archDerivAt hwQ ArchDir.E R.toFun + archDerivAt hwQ ArchDir.Fm R.toFun) = 0) :
    Concl c u d₁ d₂ T Φ P D := by
  obtain ⟨ν, hν⟩ := exists_sq_eq (1 / 4 - P.laplaceEigenvalue)
  obtain ⟨lawsB, sheetB⟩ := B_pkg D (k₀ : ℤ) ν hν hDW hDE
  obtain ⟨g₁, hg₁, lawsA, sheetA⟩ := phi_pkg c u d₁ d₂ T R hR (k₀ : ℤ) _ _ ν hν hw
  have hAm := A_ray_neg_eq_zero c u d₁ d₂ T R hR k₀ hk₀ _ _ ν hw hlam hL g₁ (sheetA (-1) (Or.inr rfl)).bdd
  have hBm' : ∀ x : Matrix (Fin 2) (Fin 2) ℝ, x.det < 0 → Bfun D x = 0 := fun x hx => by
    rw [Bfun, hBm x hx, mul_zero]
  obtain ⟨z, hz⟩ := match_of_vanishing lawsA lawsB (sheetA 1 (Or.inl rfl)) (sheetB 1 (Or.inl rfl)) hAm hBm'
    (B_ne_zero D hDnv)
  exact concl_of_match c u d₁ d₂ T Φ P D hΘ' R hR g₁ hg₁ z hz

theorem neg_one_pow_val (a : ZMod 2) : ((-1 : ℂ) ^ a.val = 1) ∨ ((-1 : ℂ) ^ a.val = -1) := by
  have : a.val < 2 := a.val_lt
  interval_cases h : a.val <;> simp

theorem concl_parity (c u d₁ d₂ : ℝ) (T : Finset (AdelicGL2 (𝓞 ℚ) ℚ)) (Φ : HeckeEigensystem ℚ ℂ)
    (u₁ u₂ : ℂ) (a : ZMod 2) (hgen : ∀ p : ℤ, Odd p → u₁ - u₂ ≠ (p : ℂ))
    (D : ArchDatumR (RealArchParam.principal u₁ a u₂ a))
    (hDW : ∀ (r : rowIsometrySubgroup₀ ℝ) (x : GL (Fin 2) ℝ),
      D.W ((x * (r : GL (Fin 2) ℝ) : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) =
        (archWeightCharℝ 0 r : ℂ) * D.W (x : Matrix (Fin 2) (Fin 2) ℝ))
    (hDE : ArchCasimir.IsCasimirEigen D) (hDnv : ∃ g : GL (Fin 2) ℝ, D.W g ≠ 0)
    {Θ' : HeckeEigensystem ℚ ℂ} (hΘ' : Θ'.AgreesAwayFromFinite Φ)
    (R : SmoothCuspRealizationAt ℚ (pinsQ c u d₁ d₂ T) Θ'.toRawCentral)
    (hR : IsGenuineCuspRealizationAt ℚ (pinsQ c u d₁ d₂ T) Θ'.toRawCentral R)
    (hw : Wit 0 (RealArchParam.principal u₁ a u₂ a).laplaceEigenvalue (RealArchParam.principal u₁ a u₂ a).centralExponent R.toFun)
    (ε : ℂ) (hε : ε = 1 ∨ ε = -1) (hJ : ∀ g, R.toFun (g * archRealGLAt hwQ UpperHalfPlane.J) = ε * R.toFun g) :
    Concl c u d₁ d₂ T Φ (RealArchParam.principal u₁ a u₂ a) D := by
  obtain ⟨ν, hν⟩ := exists_sq_eq (1 / 4 - (RealArchParam.principal u₁ a u₂ a).laplaceEigenvalue)
  obtain ⟨lawsB, sheetB⟩ := B_pkg D 0 ν hν hDW hDE
  obtain ⟨g₁, hg₁, lawsA, sheetA⟩ := phi_pkg c u d₁ d₂ T R hR 0 _ _ ν hν hw
  have hAJ : ∀ x : Matrix (Fin 2) (Fin 2) ℝ, x.det ≠ 0 →
      Afun c u d₁ d₂ T R.toFun g₁ (x * Jm) = ε * Afun c u d₁ d₂ T R.toFun g₁ x :=
    fun x hx => A_parity c u d₁ d₂ T hJ (finPart g₁) (glArch_finPart g₁) x hx
  have hBJ : ∀ x : Matrix (Fin 2) (Fin 2) ℝ, x.det ≠ 0 → Bfun D (x * Jm) = (-1 : ℂ) ^ a.val * Bfun D x := by
    intro x hx
    rw [Bfun, Bfun, det_mul_Jm, abs_neg,
      LanglandsTunnell.Converse.ArchDatumR.W_mul_diag_eq_neg_one_pow_mul_of_principal_of_archWeightChar_zero_of_isCasimirEigen
        u₁ u₂ a hgen D hDW hDE x hx]
    ring
  obtain ⟨z, hz | hz⟩ := match_of_parity lawsA lawsB (sheetA 1 (Or.inl rfl)) (sheetB 1 (Or.inl rfl)) ε hε hAJ
    _ (neg_one_pow_val a) hBJ (B_ne_zero D hDnv)
  · exact concl_of_match c u d₁ d₂ T Φ _ D hΘ' R hR g₁ hg₁ z hz
  · exact concl_of_match_twist c u d₁ d₂ T Φ _ D hΘ' R hR g₁ hg₁ z hz

abbrev Lm (W : Matrix (Fin 2) (Fin 2) ℝ → ℂ) (x : Matrix (Fin 2) (Fin 2) ℝ) : ℂ :=
  ArchCasimir.matrixFlowDeriv ArchDir.H W x -
    Complex.I * (ArchCasimir.matrixFlowDeriv ArchDir.E W x + ArchCasimir.matrixFlowDeriv ArchDir.Fm W x)

theorem det_archFlowMatrix (d : ArchDir) (t : ℝ) :
    ((archFlowMatrix d t : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ).det = 1 := by
  cases d
  · simp [archFlowMatrix, splitTorusGL2, Matrix.det_fin_two_of, ← Real.exp_add]
  · simp [archFlowMatrix, unipotentGL2, Matrix.det_fin_two_of]
  · simp [archFlowMatrix, lowerUnipotentGL2, Matrix.det_fin_two_of]

theorem Jm_mul_Jm : Jm * Jm = 1 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [Jm]

theorem mfd_prop {A B : Matrix (Fin 2) (Fin 2) ℝ → ℂ} {z : ℂ} {s : ℝ}
    (h : ∀ y : Matrix (Fin 2) (Fin 2) ℝ, 0 < s * y.det → A y = z * B y) (d : ArchDir)
    (x : Matrix (Fin 2) (Fin 2) ℝ) (hx : 0 < s * x.det) :
    ArchCasimir.matrixFlowDeriv d A x = z * ArchCasimir.matrixFlowDeriv d B x := by
  unfold ArchCasimir.matrixFlowDeriv
  have : (fun t : ℝ => A (x * (archFlowMatrix d t : Matrix (Fin 2) (Fin 2) ℝ))) =
      fun t : ℝ => z * B (x * (archFlowMatrix d t : Matrix (Fin 2) (Fin 2) ℝ)) := by
    funext t
    apply h
    rwa [Matrix.det_mul, det_archFlowMatrix, mul_one]
  rw [this, deriv_const_mul_field']

theorem Lm_prop {A B : Matrix (Fin 2) (Fin 2) ℝ → ℂ} {z : ℂ} {s : ℝ}
    (h : ∀ y : Matrix (Fin 2) (Fin 2) ℝ, 0 < s * y.det → A y = z * B y)
    (x : Matrix (Fin 2) (Fin 2) ℝ) (hx : 0 < s * x.det) : Lm A x = z * Lm B x := by
  simp only [Lm, mfd_prop h _ x hx]
  ring

theorem mfd_Bfun {P : RealArchParam} (D : ArchDatumR P) (d : ArchDir) (x : Matrix (Fin 2) (Fin 2) ℝ) :
    ArchCasimir.matrixFlowDeriv d (Bfun D) x =
      (((|x.det| ^ (-(1 / 2 : ℝ)) : ℝ)) : ℂ) * ArchCasimir.matrixFlowDeriv d D.W x := by
  unfold ArchCasimir.matrixFlowDeriv
  have : (fun t : ℝ => Bfun D (x * (archFlowMatrix d t : Matrix (Fin 2) (Fin 2) ℝ))) =
      fun t : ℝ => (((|x.det| ^ (-(1 / 2 : ℝ)) : ℝ)) : ℂ) * D.W (x * (archFlowMatrix d t : Matrix (Fin 2) (Fin 2) ℝ)) := by
    funext t
    simp only [Bfun, Matrix.det_mul, det_archFlowMatrix, mul_one]
  rw [this, deriv_const_mul_field']

theorem Lm_Bfun {P : RealArchParam} (D : ArchDatumR P) (x : Matrix (Fin 2) (Fin 2) ℝ) :
    Lm (Bfun D) x = (((|x.det| ^ (-(1 / 2 : ℝ)) : ℝ)) : ℂ) * Lm D.W x := by
  simp only [Lm, mfd_Bfun]
  ring

theorem A_transport (c u d₁ d₂ : ℝ) (T : Finset (AdelicGL2 (𝓞 ℚ) ℚ)) {φ ψf : AdelicGL2 (𝓞 ℚ) ℚ → ℂ}
    (hJ : ∀ g, φ (g * archRealGLAt hwQ UpperHalfPlane.J) = ψf g)
    (g₀ : AdelicGL2 (𝓞 ℚ) ℚ) (hg₀ : glArch (𝓞 ℚ) ℚ g₀ = 1) (x : Matrix (Fin 2) (Fin 2) ℝ) (hx : x.det ≠ 0) :
    W1 c u d₁ d₂ T φ (archRealLiftAt hwQ (Matrix.of.symm (x * Jm)) * g₀) =
      W1 c u d₁ d₂ T ψf (archRealLiftAt hwQ (Matrix.of.symm x) * g₀) := by
  have hx' : (Matrix.of (Matrix.of.symm x)).det ≠ 0 := by rwa [Equiv.apply_symm_apply]
  have : archRealLiftAt hwQ (Matrix.of.symm (x * Jm)) =
      archRealLiftAt hwQ (Matrix.of.symm x) * archRealGLAt hwQ UpperHalfPlane.J := by
    rw [archRealLiftAt_mul_archRealGLAt hwQ hx', coe_UpperHalfPlane_J_eq_diagonal, Equiv.apply_symm_apply]
  rw [this, mul_assoc, archRealGLAt_mul_comm_of_glArch_eq_one hwQ _ hg₀, ← mul_assoc, W1_mul_right,
    show (fun y => φ (y * archRealGLAt hwQ UpperHalfPlane.J)) = ψf from funext hJ]

theorem mfd_Afun (c u d₁ d₂ : ℝ) (T : Finset (AdelicGL2 (𝓞 ℚ) ℚ)) {φ : AdelicGL2 (𝓞 ℚ) ℚ → ℂ}
    (hsm : IsArchSmoothAt hwQ φ) (hKf : IsKfSmooth ℚ φ) (g₁ : AdelicGL2 (𝓞 ℚ) ℚ) (d : ArchDir)
    (x : Matrix (Fin 2) (Fin 2) ℝ) (hx : x.det ≠ 0) :
    ArchCasimir.matrixFlowDeriv d (Afun c u d₁ d₂ T φ g₁) x = Afun c u d₁ d₂ T (archDerivAt hwQ d φ) g₁ x := by
  have hx' : (Matrix.of (Matrix.of.symm x)).det ≠ 0 := by rwa [Equiv.apply_symm_apply]
  unfold ArchCasimir.matrixFlowDeriv
  have hfun : (fun t : ℝ => Afun c u d₁ d₂ T φ g₁ (x * (archFlowMatrix d t : Matrix (Fin 2) (Fin 2) ℝ))) =
      fun t : ℝ => W1 c u d₁ d₂ T φ ((archRealLiftAt hwQ (Matrix.of.symm x) * finPart g₁) * archFlowAt hwQ d t) := by
    funext t
    simp only [Afun]
    rw [show archRealLiftAt hwQ (Matrix.of.symm (x * (archFlowMatrix d t : Matrix (Fin 2) (Fin 2) ℝ))) =
        archRealLiftAt hwQ (Matrix.of.symm x) * archFlowAt hwQ d t by
      rw [archFlowAt, archRealLiftAt_mul_archRealGLAt hwQ hx', Equiv.apply_symm_apply],
      mul_assoc, archFlowAt_mul_comm_of_glArch_eq_one hwQ d t (glArch_finPart g₁), ← mul_assoc]
  rw [hfun]
  have hcomm := (LanglandsTunnell.isArchSmoothAt_whittakerCoefficient_and_archDerivAt_comm (Dset c u d₁ d₂ T)
    (fun N => levelOne (𝓞 ℚ) ℚ N ⊓ finiteAdelicGL2Subgroup ℚ) (fun v => heckeGen (𝓞 ℚ) ℚ v)
    (NumberField.StandardAddChar.stdAddChar ℚ) (NumberField.StandardAddChar.isGlobalAddChar_stdAddChar ℚ).continuous
    Rat.infinitePlace hwQ φ hsm hKf 1).2.1 d
  exact congrFun hcomm _

theorem Afun_lower (c u d₁ d₂ : ℝ) (T : Finset (AdelicGL2 (𝓞 ℚ) ℚ)) {φ : AdelicGL2 (𝓞 ℚ) ℚ → ℂ}
    (hsm : IsArchSmoothAt hwQ φ) (hKf : IsKfSmooth ℚ φ) (hD : ∀ d : ArchDir, Continuous (archDerivAt hwQ d φ))
    (g₁ : AdelicGL2 (𝓞 ℚ) ℚ) (x : Matrix (Fin 2) (Fin 2) ℝ) (hx : x.det ≠ 0) :
    Afun c u d₁ d₂ T (archDerivAt hwQ ArchDir.H φ - Complex.I • (archDerivAt hwQ ArchDir.E φ + archDerivAt hwQ ArchDir.Fm φ)) g₁ x =
      Lm (Afun c u d₁ d₂ T φ g₁) x := by

  set φs : Fin 3 → (AdelicGL2 (𝓞 ℚ) ℚ → ℂ) := ![archDerivAt hwQ ArchDir.H φ, archDerivAt hwQ ArchDir.E φ, archDerivAt hwQ ArchDir.Fm φ]
  set cs : Fin 3 → ℂ := ![1, -Complex.I, -Complex.I]
  have hsum : (archDerivAt hwQ ArchDir.H φ - Complex.I • (archDerivAt hwQ ArchDir.E φ + archDerivAt hwQ ArchDir.Fm φ)) =
      fun g => ∑ j, cs j * φs j g := by
    funext g
    simp only [φs, cs, Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.head_cons, Matrix.tail_cons, Pi.sub_apply, Pi.smul_apply, Pi.add_apply, smul_eq_mul]
    ring
  have hcont : ∀ j, Continuous (φs j) := by
    intro j; fin_cases j <;> simp [φs] <;> exact hD _
  have hlin := AutomorphicForm.whittakerCoefficient_sum_smul_of_continuous ℚ (Dset c u d₁ d₂ T)
    (fun N => levelOne (𝓞 ℚ) ℚ N ⊓ finiteAdelicGL2Subgroup ℚ) (fun v => heckeGen (𝓞 ℚ) ℚ v)
    (NumberField.StandardAddChar.stdAddChar ℚ) (NumberField.StandardAddChar.isGlobalAddChar_stdAddChar ℚ).continuous
    3 φs hcont cs 1 (archRealLiftAt hwQ (Matrix.of.symm x) * finPart g₁)
  rw [Afun, hsum]
  change whittakerCoefficient ℚ (productionPinsOf ℚ (Dset c u d₁ d₂ T) (fun N => levelOne (𝓞 ℚ) ℚ N ⊓ finiteAdelicGL2Subgroup ℚ)
    (fun v => heckeGen (𝓞 ℚ) ℚ v) (adelicBox ℚ)) (NumberField.StandardAddChar.stdAddChar ℚ)
    (fun g => ∑ j, cs j * φs j g) 1 (archRealLiftAt hwQ (Matrix.of.symm x) * finPart g₁) = _
  rw [hlin]
  simp only [Lm, mfd_Afun c u d₁ d₂ T hsm hKf g₁ _ x hx, φs, cs, Fin.sum_univ_three, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Afun]
  ring

theorem concl_maass (c u d₁ d₂ : ℝ) (T : Finset (AdelicGL2 (𝓞 ℚ) ℚ)) (hc : 0 < c) (hd₁ : 0 < d₁) (hd : d₁ < d₂)
    (hcov : CoversModCentre ℚ (Dset c u d₁ d₂ T)) (Φ : HeckeEigensystem ℚ ℂ)
    (u₁ u₂ : ℂ) (a₁ a₂ : ZMod 2) (ha : a₁ ≠ a₂) (hu : u₁ ≠ u₂)
    (hgen : ∀ p : ℤ, p ≠ 0 → u₁ - u₂ = (p : ℂ) → a₁ - a₂ ≠ ((p + 1 : ℤ) : ZMod 2))
    (htype : |(u₁ - u₂).re| < 1)
    (D : ArchDatumR (RealArchParam.principal u₁ a₁ u₂ a₂))
    (hDW : ∀ (r : rowIsometrySubgroup₀ ℝ) (x : GL (Fin 2) ℝ),
      D.W ((x * (r : GL (Fin 2) ℝ) : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) =
        (archWeightCharℝ 1 r : ℂ) * D.W (x : Matrix (Fin 2) (Fin 2) ℝ))
    (hDE : ArchCasimir.IsCasimirEigen D) (hDnv : ∃ g : GL (Fin 2) ℝ, D.W g ≠ 0)
    (hocc : ArchOccursInClassOf ℚ (Dset c u d₁ d₂ T) Φ
      (Wit 1 (RealArchParam.principal u₁ a₁ u₂ a₂).laplaceEigenvalue (RealArchParam.principal u₁ a₁ u₂ a₂).centralExponent)) :
    Concl c u d₁ d₂ T Φ (RealArchParam.principal u₁ a₁ u₂ a₂) D := by
  have hlam : (RealArchParam.principal u₁ a₁ u₂ a₂).laplaceEigenvalue ≠ 1 / 4 := by
    rw [laplaceEigenvalue_principal]
    intro h
    have : ((u₁ - u₂) / 2) ^ 2 = 0 := by linear_combination -h
    apply hu
    have := pow_eq_zero_iff (n := 2) (by norm_num) |>.mp this
    linear_combination 2 * this
  obtain ⟨Θ', hΘ', R, hR, hw, cJ, hcJ⟩ :=
    AutomorphicForm.archOccursInClassOf_archWeightChar_one_apply_mul_archRealGLAt_J_eq_mul_lower_of_ne_of_coversModCentre_rat c u d₁ d₂ T
      hc hd₁ hd hcov Φ _ _ hlam hocc
  obtain ⟨κ, hκ⟩ :=
    LanglandsTunnell.Converse.ArchDatumR.exists_W_mul_diag_eq_mul_lower_of_principal_of_ne_of_ne_of_archWeightChar_one_of_isCasimirEigen
      u₁ u₂ a₁ a₂ ha hu hgen htype D hDW hDE
  obtain ⟨ν, hν⟩ := exists_sq_eq (1 / 4 - (RealArchParam.principal u₁ a₁ u₂ a₂).laplaceEigenvalue)
  obtain ⟨lawsB, sheetB⟩ := B_pkg D 1 ν hν hDW hDE
  obtain ⟨g₁, hg₁, lawsA, sheetA⟩ := phi_pkg c u d₁ d₂ T R hR 1 _ _ ν hν hw
  obtain ⟨hk, hsm, hreg, hΩ, hcent⟩ := hw
  have hD1 : ∀ d : ArchDir, Continuous (archDerivAt hwQ d R.toFun) := fun d => (hreg [d]).1

  set A := Afun c u d₁ d₂ T R.toFun g₁ with hA
  set B := Bfun D with hB

  have hBJ : ∀ x : Matrix (Fin 2) (Fin 2) ℝ, x.det ≠ 0 → B (x * Jm) = κ * Lm B x := by
    intro x hx
    rw [hB, Lm_Bfun, Bfun, det_mul_Jm, abs_neg, hκ x hx]
    ring

  have hAJ : ∀ x : Matrix (Fin 2) (Fin 2) ℝ, x.det ≠ 0 → A (x * Jm) = cJ * Lm A x := by
    intro x hx
    rw [hA, Afun, A_transport c u d₁ d₂ T hcJ (finPart g₁) (glArch_finPart g₁) x hx,
      show (fun g => cJ * (archDerivAt hwQ ArchDir.H R.toFun - Complex.I • (archDerivAt hwQ ArchDir.E R.toFun +
        archDerivAt hwQ ArchDir.Fm R.toFun)) g) = fun g => cJ * ((archDerivAt hwQ ArchDir.H R.toFun -
          Complex.I • (archDerivAt hwQ ArchDir.E R.toFun + archDerivAt hwQ ArchDir.Fm R.toFun)) g) from rfl,
      W1_const_mul, ← Afun_lower c u d₁ d₂ T hsm R.isKfSmooth hD1 g₁ x hx]
  clear_value A B

  have hκ0 : κ ≠ 0 := by
    intro h0
    obtain ⟨g, hg⟩ := hDnv
    apply hg
    have hgd : ((g : Matrix (Fin 2) (Fin 2) ℝ) * Jm).det ≠ 0 := by
      rw [det_mul_Jm, neg_ne_zero]; exact Matrix.GeneralLinearGroup.det_ne_zero g
    have := hκ ((g : Matrix (Fin 2) (Fin 2) ℝ) * Jm) hgd
    rwa [Matrix.mul_assoc, Jm_mul_Jm, Matrix.mul_one, h0, zero_mul] at this

  have hBpos : ∃ x : Matrix (Fin 2) (Fin 2) ℝ, 0 < x.det ∧ B x ≠ 0 := by
    by_contra h
    push Not at h
    have h' : ∀ y : Matrix (Fin 2) (Fin 2) ℝ, 0 < (1 : ℝ) * y.det → B y = 0 * B y := fun y hy => by
      rw [zero_mul]; exact h y (by linarith)
    obtain ⟨x, hx, hBx⟩ := B_ne_zero D hDnv
    have hb : B x = 0 := by
      rcases lt_or_gt_of_ne hx with hlt | hgt
      · have hxJ : 0 < (x * Jm).det := by rw [det_mul_Jm]; linarith
        have := hBJ (x * Jm) hxJ.ne'
        rw [Matrix.mul_assoc, Jm_mul_Jm, Matrix.mul_one, Lm_prop h' (x * Jm) (by linarith), zero_mul, mul_zero] at this
        exact this
      · exact h x hgt
    rw [hB] at hb
    exact hBx hb
  have hBray : ∃ y : ℝ, 0 < y ∧ B (ray 1 y) ≠ 0 := by
    by_contra h
    push Not at h
    obtain ⟨x, hx, hBx⟩ := hBpos
    have := ext_component lawsB lawsB 0 1 (Or.inl rfl) (fun y hy => by rw [h y hy, zero_mul]) x (by linarith)
    exact hBx (by rwa [zero_mul] at this)

  obtain ⟨z, hz⟩ := ray_prop (sheetA 1 (Or.inl rfl)) (sheetB 1 (Or.inl rfl)) hBray
  have hpos : ∀ x : Matrix (Fin 2) (Fin 2) ℝ, 0 < (1 : ℝ) * x.det → A x = z * B x :=
    fun x hx => ext_component lawsA lawsB z 1 (Or.inl rfl) hz x hx

  have hneg : ∀ x : Matrix (Fin 2) (Fin 2) ℝ, 0 < (-1 : ℝ) * x.det → A x = (cJ / κ * z) * B x := by
    intro x hx
    have hxd : x.det ≠ 0 := by intro h0; rw [h0] at hx; simp at hx
    have hy : 0 < (1 : ℝ) * (x * Jm).det := by rw [det_mul_Jm]; linarith
    have hyd : (x * Jm).det ≠ 0 := by intro h0; rw [h0] at hy; simp at hy
    have h1 := hAJ (x * Jm) hyd
    have h2 := hBJ (x * Jm) hyd
    rw [Matrix.mul_assoc, Jm_mul_Jm, Matrix.mul_one] at h1 h2
    rw [h1, Lm_prop hpos _ hy, h2]
    field_simp

  have hpos' : ∀ x : Matrix (Fin 2) (Fin 2) ℝ, 0 < x.det → A x = (cJ / κ) ^ 2 * z * B x := by
    intro x hx
    have hy : 0 < (-1 : ℝ) * (x * Jm).det := by rw [det_mul_Jm]; linarith
    have hyd : (x * Jm).det ≠ 0 := by intro h0; rw [h0] at hy; simp at hy
    have h1 := hAJ (x * Jm) hyd
    have h2 := hBJ (x * Jm) hyd
    rw [Matrix.mul_assoc, Jm_mul_Jm, Matrix.mul_one] at h1 h2
    rw [h1, Lm_prop hneg _ hy, h2]
    field_simp

  obtain ⟨x₀, hx₀, hBx₀⟩ := hBpos
  have hsq : z = 0 ∨ (cJ / κ) * (cJ / κ) = 1 := by
    by_cases hz0 : z = 0
    · exact Or.inl hz0
    · right
      have := (hpos x₀ (by linarith)).symm.trans (hpos' x₀ hx₀)
      have h' : ((cJ / κ) ^ 2 - 1) * (z * B x₀) = 0 := by linear_combination -this
      rcases mul_eq_zero.mp h' with h'' | h''
      · linear_combination h''
      · exact absurd (mul_eq_zero.mp h'') (not_or.mpr ⟨hz0, hBx₀⟩)
  rcases hsq with hz0 | hsq
  ·
    refine concl_of_match c u d₁ d₂ T Φ _ D hΘ' R hR g₁ hg₁ 0 fun x hx => ?_
    rw [← hA, ← hB]
    rcases lt_or_gt_of_ne hx with hlt | hgt
    · have := hneg x (by linarith); rw [hz0] at this; simpa using this
    · have := hpos x (by linarith); rwa [hz0] at this
  · rcases mul_self_eq_one_iff.mp hsq with h1 | h1
    · refine concl_of_match c u d₁ d₂ T Φ _ D hΘ' R hR g₁ hg₁ z fun x hx => ?_
      rw [← hA, ← hB]
      rcases lt_or_gt_of_ne hx with hlt | hgt
      · have := hneg x (by linarith); rwa [h1, one_mul] at this
      · exact hpos x (by linarith)
    · refine concl_of_match_twist c u d₁ d₂ T Φ _ D hΘ' R hR g₁ hg₁ z fun x hx => ?_
      rw [← hA, ← hB]
      rcases lt_or_gt_of_ne hx with hlt | hgt
      · have := hneg x (by linarith)
        rw [h1] at this
        rw [this, sign_neg hlt]
        simp
      · rw [hpos x (by linarith), sign_pos hgt]
        simp

end Ws1.WM

p2m_open "IsDedekindDomain NumberField NumberField.AdelicLevel NumberField.AdelicBox AutomorphicForm P2MW.S_LanglandsTunnell_exists_whittakerCoefficient_fibre_eq_archW_mul_of_apply_mul_archRealGLAt_J_eq_mul_lower_of_mem_isCuspConstituent_weightOne_of_ne_bot.AutomorphicForm AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering NumberField.InfinitePlace NumberField.InfinitePlace.Completion"

open LanglandsTunnell LanglandsTunnell.RealArchParam
open LanglandsTunnell.Converse
open AutomorphicForm.CuspidalConstituent NumberField.AdelicVolume

namespace AutomorphicForm
p2m_export "AutomorphicForm" "ArchOccursInClassOf SmoothCuspRealizationAt finiteAdelicGL2Subgroup mem_finiteAdelicGL2Subgroup_iff IsKfSmooth lsXiMemberAt_iff IsAutomorphicFnAt CarrierPins productionPinsOf AdelicGL2 globalPoints centralScalar unipotentGL2 unipotentGL2_coe HeckeEigensystem glEquivOfRingEquiv rowIsometrySubgroup₀Map norm_ringEquivRealOfIsReal archWeightCharAt rowIsometrySubgroup₀ mem_rowIsometrySubgroup₀_iff archWeightCharℝ HasArchCharacterAt₀ archMatrixUpdate archMatrixUpdate_apply_self archMatrixUpdate_apply_of_ne archGLIncl archComponent_archGLIncl_self adelicArchGLIncl adelicArchGLInclAt glArch_adelicArchGLIncl glFin_adelicArchGLIncl classRepTranslates productionPinsGeneral IsGenuineCuspRealizationAt archRealGLAt archRealLiftAt archRealLiftAt_of_det_ne_zero IsArchSmoothAt ArchDir lowerUnipotentGL2 splitTorusGL2 archFlowMatrix archFlowAt archDerivAt archCasimirAt archRealLiftAt_mul_archRealGLAt eq_of_glArch_eq_of_glFin_eq archRealGLAt_mul_comm_of_glArch_eq_one archRealLiftAt_mul_comm_of_glArch_eq_one archFlowAt_mul_comm_of_glArch_eq_one ArchDir.H ArchDir.Fm ArchDir.E whittakerCoefficient archOccursInClassOf_archWeightChar_one_apply_mul_archRealGLAt_J_eq_mul_lower_of_ne_of_coversModCentre_rat whittakerCoefficient_archRealLiftAt_mul_laws_and_torus_ode_of_archCasimirAt_eq_smul_rat archDerivAt_E_sub_archDerivAt_Fm_eq_smul_of_hasArchCharacterAtZero_of_isArchSmoothAt SmoothCuspRealizationAt.exists_whittakerCoefficient_one_ne_zero_of_continuous_foldr_archDerivAt_rat whittakerCoefficient_detOneTorus_eq_zero_of_iterate_lower_eq_zero whittakerCoefficient_sum_smul_of_continuous CuspidalConstituent.IsCuspConstituent CuspidalConstituent.levelInvariantSubmodule IsIsotypicCuspFormAt ArchTypeFamily ArchTypeFamily.ofChar archCutSubmodule mem_archCutSubmodule_ofChar_iff CuspidalConstituent.isArchSmoothAt_and_continuous_foldr_archDerivAt_of_mem_cut CuspidalSpectrum.exists_hasModulus_of_isAutomorphicFnAt_of_continuous CuspidalConstituent.exists_forall_norm_foldr_archDerivAt_le_of_mem_cut eq_stdAddChar_of_isGlobalAddChar_of_apply_infinitePlace_eq_exp SiegelCovering.coversModCentre_productionPinsGeneral_D_rat"
namespace RJClose
namespace K4
p2m_open "AutomorphicForm"

variable {F : Type} [Field F] [NumberField F]

theorem adelicArchGLInclAt_scalar_eq_centralScalar {w : InfinitePlace F} (hw : w.IsReal) (t : ℝˣ) :
    adelicArchGLInclAt F w (Matrix.GeneralLinearGroup.map (ringEquivRealOfIsReal hw).symm.toRingHom
        (Matrix.GeneralLinearGroup.scalar (Fin 2) t))
      = centralScalar (𝓞 F) F
          (archCentralUnit F w (Units.map (ringEquivRealOfIsReal hw).symm.toRingHom.toMonoidHom t)) := by
  apply eq_of_glArch_eq_of_glFin_eq
  · show glArch (𝓞 F) F (adelicArchGLIncl F (archGLIncl F w _)) = _
    rw [glArch_adelicArchGLIncl]
    apply Units.ext
    apply Matrix.ext
    intro i j
    funext v
    show archMatrixUpdate F w _ i j v = _
    rw [show ((glArch (𝓞 F) F (centralScalar (𝓞 F) F
        (archCentralUnit F w (Units.map (ringEquivRealOfIsReal hw).symm.toRingHom.toMonoidHom t))) :
          GL (Fin 2) (InfiniteAdeleRing F)) : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing F)) i j v
        = (((centralScalar (𝓞 F) F
          (archCentralUnit F w (Units.map (ringEquivRealOfIsReal hw).symm.toRingHom.toMonoidHom t)) :
            AdelicGL2 (𝓞 F) F) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) i j).1 v from rfl,
      centralScalar_val]
    by_cases hv : v = w
    · subst hv
      rw [archMatrixUpdate_apply_self]
      fin_cases i <;> fin_cases j <;>
        simp [Matrix.diagonal, Matrix.GeneralLinearGroup.map, Matrix.GeneralLinearGroup.scalar,
          archCentralUnit_fst_self]
      all_goals rfl
    · rw [archMatrixUpdate_apply_of_ne F w _ i j hv]
      fin_cases i <;> fin_cases j <;>
        simp [Matrix.diagonal, archCentralUnit_fst_of_ne _ _ hv]
      all_goals rfl
  · show glFin (𝓞 F) F (adelicArchGLIncl F (archGLIncl F w _)) = _
    rw [glFin_adelicArchGLIncl]
    apply Units.ext
    apply Matrix.ext
    intro i j
    show (1 : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 F) F)) i j
      = (((centralScalar (𝓞 F) F
          (archCentralUnit F w (Units.map (ringEquivRealOfIsReal hw).symm.toRingHom.toMonoidHom t)) :
            AdelicGL2 (𝓞 F) F) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) i j).2
    rw [centralScalar_val]
    fin_cases i <;> fin_cases j <;> simp [Matrix.diagonal, archCentralUnit_snd]
    all_goals rfl

theorem apply_centralScalar_mul_of_isAutomorphicFnAt (D : Set (AdelicGL2 (𝓞 F) F))
    (ξ : (productionPinsOf F D (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F)
      (fun v => heckeGen (𝓞 F) F v) (adelicBox F)).Z →* ℂˣ)
    (φ : AdelicGL2 (𝓞 F) F → ℂ)
    (hφ : IsAutomorphicFnAt F (productionPinsOf F D (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F)
      (fun v => heckeGen (𝓞 F) F v) (adelicBox F)) ξ φ)
    (z : (AdeleRing (𝓞 F) F)ˣ) (g : AdelicGL2 (𝓞 F) F) :
    φ (centralScalar (𝓞 F) F z * g) = ((ξ ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) * φ g := by
  unfold IsAutomorphicFnAt at hφ
  rw [lsXiMemberAt_iff] at hφ
  exact hφ.1.central_transform ⟨z, Subgroup.mem_top z⟩ g

end AutomorphicForm.RJClose.K4

p2m_open "IsDedekindDomain NumberField NumberField.InfinitePlace.NumberField NumberField.AdelicLevel NumberField.AdelicBox AutomorphicForm P2MW.S_LanglandsTunnell_exists_whittakerCoefficient_fibre_eq_archW_mul_of_apply_mul_archRealGLAt_J_eq_mul_lower_of_mem_isCuspConstituent_weightOne_of_ne_bot.AutomorphicForm AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering NumberField.InfinitePlace NumberField.InfinitePlace.NumberField.InfinitePlace NumberField.InfinitePlace.Completion"

open NumberField.TateGlobal NumberField.AdelicVolume Matrix
open LanglandsTunnell LanglandsTunnell.RealArchParam LanglandsTunnell.Converse
open scoped Classical
open Ws1.WM AutomorphicForm.RJClose.K4

namespace Ws47
namespace JRL

theorem psiQ_apply_single_real : ∀ (w : InfinitePlace ℚ), w.IsReal → ∀ x : InfiniteAdeleRing ℚ,
      (∀ w' : InfinitePlace ℚ, w' ≠ w → x w' = 0) →
        NumberField.StandardAddChar.psiQ (⟨x, 0⟩ : AdeleRing (𝓞 ℚ) ℚ)
          = Complex.exp (2 * Real.pi * Complex.I * extensionEmbedding w (x w)) := by
  intro w hw x _
  rw [NumberField.StandardAddChar.psiQ_apply]
  rw [show ((⟨x, 0⟩ : AdeleRing (𝓞 ℚ) ℚ).2) = 0 from rfl, AddChar.map_zero_eq_one, mul_one,
      show ((⟨x, 0⟩ : AdeleRing (𝓞 ℚ) ℚ).1) = x from rfl,
      NumberField.StandardAddChar.psiArch_apply, finprod_eq_prod_of_fintype, Fintype.prod_subsingleton _ w,
      NumberField.StandardAddChar.psiArchPlace_apply]
  congr 1
  congr 1
  exact extensionEmbeddingOfIsReal_apply _ _

theorem psiQ_eq_stdAddChar : NumberField.StandardAddChar.psiQ = NumberField.StandardAddChar.stdAddChar ℚ :=
  AutomorphicForm.eq_stdAddChar_of_isGlobalAddChar_of_apply_infinitePlace_eq_exp ℚ _
    NumberField.StandardAddChar.isGlobalAddChar_psiQ Rat.infinitePlace Rat.isReal_infinitePlace
    (psiQ_apply_single_real _ Rat.isReal_infinitePlace)

namespace Sheet

private theorem _root_.Ws47.JRL.Sheet.congr {B B' : Matrix (Fin 2) (Fin 2) ℝ → ℂ} {ν : ℂ} {kk ε : ℝ} (hB : Sheet B ν kk ε)
    (h : ∀ y : ℝ, 0 < y → B' (ray ε y) = B (ray ε y)) : Sheet B' ν kk ε := by
  have hEq : Set.EqOn (fun y : ℝ => B' (ray ε y)) (fun y : ℝ => B (ray ε y)) (Set.Ioi 0) := fun y hy => h y hy
  have hEv : ∀ y : ℝ, 0 < y → (fun y : ℝ => B' (ray ε y)) =ᶠ[nhds y] (fun y : ℝ => B (ray ε y)) := fun y hy =>
    hEq.eventuallyEq_of_mem (isOpen_Ioi.mem_nhds hy)
  have hD : ∀ y : ℝ, 0 < y → deriv (fun y : ℝ => B' (ray ε y)) y = deriv (fun y : ℝ => B (ray ε y)) y := fun y hy =>
    (hEv y hy).deriv_eq
  have hDEq : Set.EqOn (deriv fun y : ℝ => B' (ray ε y)) (deriv fun y : ℝ => B (ray ε y)) (Set.Ioi 0) := fun y hy => hD y hy
  have hDEv : ∀ y : ℝ, 0 < y → (deriv fun y : ℝ => B' (ray ε y)) =ᶠ[nhds y] (deriv fun y : ℝ => B (ray ε y)) := fun y hy =>
    hDEq.eventuallyEq_of_mem (isOpen_Ioi.mem_nhds hy)
  refine ⟨hB.d1.congr hEq, hB.d2.congr hDEq, fun y hy => ?_, ?_⟩
  · rw [(hDEv y hy).deriv_eq, h y hy]; exact hB.ode y hy
  · obtain ⟨C, N, hC⟩ := hB.bdd
    exact ⟨C, N, fun y hy => by rw [h y (by linarith)]; exact hC y hy⟩

end Sheet
p2m_export "Ws47.JRL" "Sheet.congr"

theorem laws_DW {P : RealArchParam} (D : ArchDatumR P) {k : ℤ} {e : ℂ} (hB : Laws (Bfun D) k e)
    (hDW : ∀ (r : rowIsometrySubgroup₀ ℝ) (x : GL (Fin 2) ℝ),
      D.W ((x * (r : GL (Fin 2) ℝ) : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) =
        (archWeightCharℝ k r : ℂ) * D.W (x : Matrix (Fin 2) (Fin 2) ℝ)) :
    Laws D.W k (e + 1) := by
  have hfac : ∀ x : Matrix (Fin 2) (Fin 2) ℝ, x.det ≠ 0 → ((((|x.det| ^ (-(1 / 2 : ℝ)) : ℝ)) : ℂ)) ≠ 0 := fun x hx =>
    Complex.ofReal_ne_zero.mpr (Real.rpow_pos_of_pos (abs_pos.mpr hx) _).ne'
  refine ⟨fun t x hx => ?_, fun t x ht hx => ?_, hDW⟩
  · have h := hB.unip t x hx
    have hdet : (ArchR.unip t * x).det = x.det := by
      rw [Matrix.det_mul]; simp [ArchR.unip, Matrix.det_fin_two_of]
    simp only [Bfun, hdet] at h
    exact mul_left_cancel₀ (hfac x hx) (h.trans (by ring))
  · have h := hB.cent t x ht hx
    have ht0 : ((t : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht.ne'
    have hdet : (t • x).det = t ^ 2 * x.det := by rw [Matrix.det_smul, Fintype.card_fin]
    have hpow : (|(t • x).det| ^ (-(1 / 2 : ℝ)) : ℝ) = t⁻¹ * (|x.det| ^ (-(1 / 2 : ℝ)) : ℝ) := by
      rw [hdet, abs_mul, abs_of_pos (by positivity : (0:ℝ) < t ^ 2), Real.mul_rpow (by positivity) (abs_nonneg _)]
      congr 1
      rw [← Real.rpow_natCast t 2, ← Real.rpow_mul ht.le, show ((2 : ℕ) : ℝ) * (-(1 / 2 : ℝ)) = -1 by norm_num,
        Real.rpow_neg_one]
    simp only [Bfun] at h
    rw [hpow] at h
    push_cast at h

    have h2 : (((|x.det| ^ (-(1 / 2 : ℝ)) : ℝ)) : ℂ) * D.W (t • x)
        = (((|x.det| ^ (-(1 / 2 : ℝ)) : ℝ)) : ℂ) * ((t : ℂ) * (t : ℂ) ^ e * D.W x) := by
      have h' := congrArg (fun z => ((t : ℝ) : ℂ) * z) h
      simp only [← mul_assoc, mul_inv_cancel₀ ht0, one_mul] at h'
      rw [h']; ring
    have h3 : D.W (t • x) = (t : ℂ) * (t : ℂ) ^ e * D.W x := mul_left_cancel₀ (hfac x hx) h2
    rw [h3, Complex.cpow_add _ _ ht0, Complex.cpow_one]; ring

end Ws47.JRL

theorem solution
    (u₁ u₂ : ℂ) (a₁ a₂ : ZMod 2) (ha : a₁ ≠ a₂) (hu : u₁ ≠ u₂)
    (hgen : ∀ p : ℤ, p ≠ 0 → u₁ - u₂ = (p : ℂ) → a₁ - a₂ ≠ ((p + 1 : ℤ) : ZMod 2))
    (htype : |(u₁ - u₂).re| < 1)
    (archC : ∀ w : InfinitePlace ℚ, w.IsComplex → ComplexArchParam)
    (dR : ∀ (w : InfinitePlace ℚ) (hw : w.IsReal), ArchDatumR (RealArchParam.principal u₁ a₁ u₂ a₂))
    (dC : ∀ (w : InfinitePlace ℚ) (hw : w.IsComplex), ArchDatumC (archC w hw))
    (hDW : ∀ (w : InfinitePlace ℚ) (hw : w.IsReal) (r : rowIsometrySubgroup₀ ℝ) (x : GL (Fin 2) ℝ),
      (dR w hw).W ((x * (r : GL (Fin 2) ℝ) : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) =
        (archWeightCharℝ 1 r : ℂ) * (dR w hw).W (x : Matrix (Fin 2) (Fin 2) ℝ))
    (hDE : ∀ (w : InfinitePlace ℚ) (hw : w.IsReal), ArchCasimir.IsCasimirEigen (dR w hw))
    (hnv : ∀ (w : InfinitePlace ℚ) (hw : w.IsReal), ∃ g : GL (Fin 2) ℝ, (dR w hw).W g ≠ 0)
    (κ : ℂ) (hκ : κ ^ 2 * (u₁ - u₂) ^ 2 = 1)
    (hDJ : ∀ (w : InfinitePlace ℚ) (hw : w.IsReal) (x : Matrix (Fin 2) (Fin 2) ℝ), x.det ≠ 0 →
      (dR w hw).W (x * Matrix.diagonal ![(-1 : ℝ), 1]) =
        κ * (ArchCasimir.matrixFlowDeriv ArchDir.H (dR w hw).W x -
              Complex.I * (ArchCasimir.matrixFlowDeriv ArchDir.E (dR w hw).W x +
                ArchCasimir.matrixFlowDeriv ArchDir.Fm (dR w hw).W x)))
    (ξ : (productionPinsGeneral ℚ).Z →* ℂˣ)
    (hcen : ∀ (w : InfinitePlace ℚ) (hw : w.IsReal),
      IsArchCompAt ℚ (ξ.comp Subgroup.topEquiv.symm.toMonoidHom) w
        ((RealArchParam.principal u₁ a₁ u₂ a₂).centralExponent + 1)
        ((RealArchParam.principal u₁ a₁ u₂ a₂).centralSign.val : ℤ))
    (N : Ideal (𝓞 ℚ)) (hN : N ≠ ⊥) (S : Finset (HeightOneSpectrum (𝓞 ℚ))) (Φ : HeckeEigensystem ℚ ℂ)
    (φ : AdelicGL2 (𝓞 ℚ) ℚ → ℂ)
    (hiso : IsIsotypicCuspFormAt ℚ (productionPinsGeneral ℚ) ξ N S Φ φ)
    (V : Submodule ℂ (AdelicGL2 (𝓞 ℚ) ℚ → ℂ))
    (hV : CuspidalConstituent.IsCuspConstituent ℚ (productionPinsGeneral ℚ) ξ V) (hφV : φ ∈ V)
    (hwt : ∀ (w : InfinitePlace ℚ) (hw : w.IsReal), HasArchCharacterAt₀ ℚ w (archWeightCharAt hw 1) φ)
    (hpair : ∀ (w : InfinitePlace ℚ) (hw : w.IsReal),
      IsArchSmoothAt hw φ ∧ archCasimirAt hw φ = (RealArchParam.principal u₁ a₁ u₂ a₂).laplaceEigenvalue • φ)
    (hcont : ∀ (w : InfinitePlace ℚ) (hw : w.IsReal) (d : ArchDir), Continuous (archDerivAt hw d φ))
    (hJ : ∀ (w : InfinitePlace ℚ) (hw : w.IsReal) (g : AdelicGL2 (𝓞 ℚ) ℚ),
      φ (g * archRealGLAt hw UpperHalfPlane.J)
        = κ * (archDerivAt hw ArchDir.H φ - Complex.I • (archDerivAt hw ArchDir.E φ + archDerivAt hw ArchDir.Fm φ)) g) :
    ∀ g₀ : AdelicGL2 (𝓞 ℚ) ℚ, g₀ ∈ finiteAdelicGL2Subgroup ℚ →
      ∃ z : ℂ, ∀ g : AdelicGL2 (𝓞 ℚ) ℚ, glFin (𝓞 ℚ) ℚ g = glFin (𝓞 ℚ) ℚ g₀ →
        whittakerCoefficient ℚ (productionPinsGeneral ℚ) NumberField.StandardAddChar.psiQ φ 1 g
          = archW (fun _ _ => RealArchParam.principal u₁ a₁ u₂ a₂) archC dR dC g * z := by
  intro g₀ hg₀
  classical

  have harchW : ∀ g : AdelicGL2 (𝓞 ℚ) ℚ, archW (fun _ _ => RealArchParam.principal u₁ a₁ u₂ a₂) archC dR dC g =
      (dR Rat.infinitePlace hwQ).W (realComponent Rat.infinitePlace hwQ g) := by
    intro g; unfold archW; rw [Fintype.prod_subsingleton _ Rat.infinitePlace, dif_pos Rat.isReal_infinitePlace]
  by_cases hφ0 : φ = 0
  · refine ⟨0, fun g hg => ?_⟩
    subst hφ0
    simp [whittakerCoefficient]

  have hcov : CoversModCentre ℚ (Dset (1/2 : ℝ) 1 (1/2) 2 (classRepTranslates ℚ)) :=
    AutomorphicForm.SiegelCovering.coversModCentre_productionPinsGeneral_D_rat
  have hpins : productionPinsGeneral ℚ = pinsQ (1/2 : ℝ) 1 (1/2) 2 (classRepTranslates ℚ) := rfl
  set D : ArchDatumR (RealArchParam.principal u₁ a₁ u₂ a₂) := dR Rat.infinitePlace hwQ with hDdef
  have hDW' := hDW Rat.infinitePlace hwQ
  have hDE' := hDE Rat.infinitePlace hwQ
  have hDnv : ∃ g : GL (Fin 2) ℝ, D.W g ≠ 0 := hnv Rat.infinitePlace hwQ
  have hκD : ∀ x : Matrix (Fin 2) (Fin 2) ℝ, x.det ≠ 0 → D.W (x * Jm) = κ * Lm D.W x := fun x hx => hDJ Rat.infinitePlace hwQ x hx
  obtain ⟨ν, hν⟩ := exists_sq_eq (1 / 4 - (RealArchParam.principal u₁ a₁ u₂ a₂).laplaceEigenvalue)
  obtain ⟨lawsB, sheetB⟩ := B_pkg D 1 ν hν hDW' hDE'

  have lawsD : Laws D.W 1 ((RealArchParam.principal u₁ a₁ u₂ a₂).centralExponent + 1) := Ws47.JRL.laws_DW D lawsB hDW'
  have hBD : ∀ (ε : ℝ), (ε = 1 ∨ ε = -1) → ∀ y : ℝ, 0 < y → D.W (ray ε y) = Bfun D (ray ε y) := by
    intro ε hε y hy
    simp only [Bfun, det_ray ε y hε hy]
    rcases hε with rfl | rfl <;> simp
  have sheetD : ∀ ε : ℝ, (ε = 1 ∨ ε = -1) → Sheet D.W ν ((1 : ℤ) : ℝ) ε := fun ε hε =>
    Ws47.JRL.Sheet.congr (sheetB ε hε) (hBD ε hε)

  have hg₀' : glArch (𝓞 ℚ) ℚ g₀ = 1 := (mem_finiteAdelicGL2Subgroup_iff ℚ g₀).mp hg₀
  let χ : ∀ v : InfinitePlace ℚ, rowIsometrySubgroup₀ v.Completion →* ℂˣ :=
    fun v => archWeightCharAt (isReal_infinitePlace_rat v) 1
  have hcut : φ ∈ archCutSubmodule ℚ (ArchTypeFamily.ofChar ℚ χ) := by
    refine (mem_archCutSubmodule_ofChar_iff (F := ℚ) χ φ).mpr fun v => ?_
    obtain rfl : v = Rat.infinitePlace := Subsingleton.elim _ _
    exact hwt _ _
  have hmem : φ ∈ V ⊓ CuspidalConstituent.levelInvariantSubmodule ℚ (pinsQ (1/2 : ℝ) 1 (1/2) 2 (classRepTranslates ℚ)) N ⊓
      archCutSubmodule ℚ (ArchTypeFamily.ofChar ℚ χ) :=
    ⟨⟨hφV, fun g u' hu' => hiso.level_invariant g u' hu'⟩, hcut⟩
  obtain ⟨w₀, hw₀⟩ := AutomorphicForm.CuspidalSpectrum.exists_hasModulus_of_isAutomorphicFnAt_of_continuous ℚ _
    ξ φ hiso.smoothCusp.1.1 hiso.continuous hφ0
  have hξ : ∀ z : (AdeleRing (𝓞 ℚ) ℚ)ˣ,
      ‖((ξ ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ)‖ = NumberField.TateGlobal.ideleNorm ℚ z ^ w₀ :=
    fun z => hw₀ ⟨z, Subgroup.mem_top z⟩
  have hreg : ∀ l : List ArchDir, Continuous (l.foldr (archDerivAt hwQ) φ) ∧
      ∀ e₁ e₂ : ℝ, 0 < e₁ → e₁ < e₂ → ∃ B : ℝ, ∀ g : AdelicGL2 (𝓞 ℚ) ℚ,
        NumberField.TateGlobal.ideleNorm ℚ (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc e₁ e₂ →
          ‖l.foldr (archDerivAt hwQ) φ g‖ ≤ B := fun l =>
    ⟨(AutomorphicForm.CuspidalConstituent.isArchSmoothAt_and_continuous_foldr_archDerivAt_of_mem_cut
        ℚ (1/2 : ℝ) 1 (1/2) 2 (classRepTranslates ℚ) (by norm_num) (by norm_num) (by norm_num) hcov ξ V hV N hN _ φ hmem Rat.infinitePlace hwQ l).2,
      fun e₁ e₂ he₁ he =>
        AutomorphicForm.CuspidalConstituent.exists_forall_norm_foldr_archDerivAt_le_of_mem_cut
          ℚ (1/2 : ℝ) 1 (1/2) 2 (classRepTranslates ℚ) (by norm_num) (by norm_num) (by norm_num) hcov ξ V hV w₀ hξ N hN _ φ hmem Rat.infinitePlace hwQ e₁ e₂ he₁ he l⟩
  have hD1 : ∀ d : ArchDir, Continuous (archDerivAt hwQ d φ) := fun d => (hreg [d]).1

  have hleft : ∀ (γ : Matrix.GeneralLinearGroup (Fin 2) ℚ) (g : AdelicGL2 (𝓞 ℚ) ℚ), φ (globalPoints (𝓞 ℚ) ℚ γ * g) = φ g := by
    intro γ g
    have h := hiso.smoothCusp.1.1
    unfold IsAutomorphicFnAt at h
    rw [lsXiMemberAt_iff] at h
    exact h.1.left_invariant γ g
  have hmult : ((Rat.infinitePlace.mult : ℕ) : ℂ) = 1 := by
    rw [NumberField.InfinitePlace.mult_isReal ⟨Rat.infinitePlace, hwQ⟩]; norm_num
  have hcent : ∀ t : ℝˣ, (0 : ℝ) < (t : ℝ) → ∀ g : AdelicGL2 (𝓞 ℚ) ℚ,
      φ (adelicArchGLInclAt ℚ Rat.infinitePlace (Matrix.GeneralLinearGroup.map (InfinitePlace.Completion.ringEquivRealOfIsReal hwQ).symm.toRingHom
        (Matrix.GeneralLinearGroup.scalar (Fin 2) t)) * g) = ((t : ℝ) : ℂ) ^ ((RealArchParam.principal u₁ a₁ u₂ a₂).centralExponent + 1) * φ g := by
    intro t ht g
    rw [adelicArchGLInclAt_scalar_eq_centralScalar hwQ t, apply_centralScalar_mul_of_isAutomorphicFnAt _ ξ φ hiso.smoothCusp.1.1]
    congr 1
    set x : (Rat.infinitePlace.Completion)ˣ := Units.map (ringEquivRealOfIsReal hwQ).symm.toRingHom.toMonoidHom t with hx
    have h := hcen Rat.infinitePlace hwQ x
    have hnorm : ‖(x : Rat.infinitePlace.Completion)‖ = (t : ℝ) := by
      rw [hx, Units.coe_map, RingHom.toMonoidHom_eq_coe, MonoidHom.coe_coe, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom,
        ← norm_ringEquivRealOfIsReal hwQ, RingEquiv.apply_symm_apply, Real.norm_eq_abs, abs_of_pos ht]
    have hemb : extensionEmbedding Rat.infinitePlace (x : Rat.infinitePlace.Completion) = ((t : ℝ) : ℂ) := by
      rw [← extensionEmbeddingOfIsReal_apply hwQ, hx]
      congr 1
      exact (ringEquivRealOfIsReal hwQ).apply_symm_apply t
    have ht0 : ((t : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht.ne'
    rw [archLocalChar, MonoidHom.comp_apply, MonoidHom.comp_apply, archUnitHom_apply, hnorm, hemb, hmult, one_mul,
      div_self ht0, _root_.one_zpow, mul_one] at h
    exact h

  obtain ⟨hAN, hAZ, hAK, hAT⟩ :=
    AutomorphicForm.whittakerCoefficient_archRealLiftAt_mul_laws_and_torus_ode_of_archCasimirAt_eq_smul_rat
      (Dset (1/2 : ℝ) 1 (1/2) 2 (classRepTranslates ℚ)) 1 _ _ ν hν φ hiso.continuous hleft (hwt _ _) (hpair _ hwQ).1 hreg (hpair _ hwQ).2
      hcent (finPart g₀) (glArch_finPart g₀)
  have lawsA : Laws (Afun (1/2 : ℝ) 1 (1/2) 2 (classRepTranslates ℚ) φ g₀) 1
      ((RealArchParam.principal u₁ a₁ u₂ a₂).centralExponent + 1) := ⟨hAN, hAZ, hAK⟩
  have sheetA : ∀ ε : ℝ, (ε = 1 ∨ ε = -1) → Sheet (Afun (1/2 : ℝ) 1 (1/2) 2 (classRepTranslates ℚ) φ g₀) ν ((1 : ℤ) : ℝ) ε :=
    fun ε hε => let h := hAT ε hε; ⟨h.1, h.2.1, h.2.2.1, h.2.2.2⟩
  set A := Afun (1/2 : ℝ) 1 (1/2) 2 (classRepTranslates ℚ) φ g₀ with hA

  have hAJ : ∀ x : Matrix (Fin 2) (Fin 2) ℝ, x.det ≠ 0 → A (x * Jm) = κ * Lm A x := by
    intro x hx
    rw [hA, Afun, A_transport (1/2 : ℝ) 1 (1/2) 2 (classRepTranslates ℚ) (hJ _ hwQ) (finPart g₀) (glArch_finPart g₀) x hx,
      show (fun g => κ * (archDerivAt hwQ ArchDir.H φ - Complex.I • (archDerivAt hwQ ArchDir.E φ +
        archDerivAt hwQ ArchDir.Fm φ)) g) = fun g => κ * ((archDerivAt hwQ ArchDir.H φ -
          Complex.I • (archDerivAt hwQ ArchDir.E φ + archDerivAt hwQ ArchDir.Fm φ)) g) from rfl,
      W1_const_mul, ← Afun_lower (1/2 : ℝ) 1 (1/2) 2 (classRepTranslates ℚ) (hpair _ hwQ).1 hiso.smoothCusp.2 hD1 g₀ x hx]
  clear_value A

  have hκ0 : κ ≠ 0 := by rintro rfl; simp at hκ
  have hBpos : ∃ x : Matrix (Fin 2) (Fin 2) ℝ, 0 < x.det ∧ D.W x ≠ 0 := by
    by_contra h
    push Not at h
    obtain ⟨g, hg⟩ := hDnv
    apply hg
    rcases lt_or_gt_of_ne (Matrix.GeneralLinearGroup.det_ne_zero g) with hlt | hgt
    · have hxJ : 0 < ((g : Matrix (Fin 2) (Fin 2) ℝ) * Jm).det := by rw [det_mul_Jm]; linarith
      have h' : ∀ y : Matrix (Fin 2) (Fin 2) ℝ, 0 < (1 : ℝ) * y.det → D.W y = 0 * D.W y := fun y hy => by
        rw [zero_mul]; exact h y (by linarith)
      have := hκD ((g : Matrix (Fin 2) (Fin 2) ℝ) * Jm) hxJ.ne'
      rw [Matrix.mul_assoc, Jm_mul_Jm, Matrix.mul_one, Lm_prop h' _ (by linarith), zero_mul, mul_zero] at this
      exact this
    · exact h _ hgt
  have hBray : ∃ y : ℝ, 0 < y ∧ D.W (ray 1 y) ≠ 0 := by
    by_contra h
    push Not at h
    obtain ⟨x, hx, hBx⟩ := hBpos
    have := ext_component lawsD lawsD 0 1 (Or.inl rfl) (fun y hy => by rw [h y hy, zero_mul]) x (by linarith)
    exact hBx (by rwa [zero_mul] at this)

  obtain ⟨z, hz⟩ := ray_prop (sheetA 1 (Or.inl rfl)) (sheetD 1 (Or.inl rfl)) hBray
  have hpos : ∀ x : Matrix (Fin 2) (Fin 2) ℝ, 0 < (1 : ℝ) * x.det → A x = z * D.W x :=
    fun x hx => ext_component lawsA lawsD z 1 (Or.inl rfl) hz x hx
  have hneg : ∀ x : Matrix (Fin 2) (Fin 2) ℝ, x.det < 0 → A x = z * D.W x := by
    intro x hx
    have hxd : x.det ≠ 0 := hx.ne
    have hy : 0 < (1 : ℝ) * (x * Jm).det := by rw [det_mul_Jm]; linarith
    have hyd : (x * Jm).det ≠ 0 := by intro h0; rw [h0] at hy; simp at hy
    have h1 := hAJ (x * Jm) hyd
    have h2 := hκD (x * Jm) hyd
    rw [Matrix.mul_assoc, Jm_mul_Jm, Matrix.mul_one] at h1 h2
    rw [h1, Lm_prop hpos _ hy, h2]
    ring
  have hmatch : ∀ x : Matrix (Fin 2) (Fin 2) ℝ, x.det ≠ 0 → A x = z * D.W x := by
    intro x hx
    rcases lt_or_gt_of_ne hx with hlt | hgt
    · exact hneg x hlt
    · exact hpos x (by linarith)

  refine ⟨z, fun g hg => ?_⟩
  have hfp : finPart g = finPart g₀ := finPart_congr hg
  have hx := realComponent_det_ne_zero g
  rw [Ws47.JRL.psiQ_eq_stdAddChar, harchW g]
  conv_lhs => rw [← archRealLiftAt_realComponent_mul_finPart g, hfp]
  have := hmatch _ hx
  rw [hA] at this
  exact (this.trans (mul_comm _ _))

end

end S_LanglandsTunnell_exists_whittakerCoefficient_fibre_eq_archW_mul_of_apply_mul_archRealGLAt_J_eq_mul_lower_of_mem_isCuspConstituent_weightOne_of_ne_bot
end P2MW
export P2MW.S_LanglandsTunnell_exists_whittakerCoefficient_fibre_eq_archW_mul_of_apply_mul_archRealGLAt_J_eq_mul_lower_of_mem_isCuspConstituent_weightOne_of_ne_bot (solution)
