-- Prove2me | solution 1 for LanglandsTunnell.RankinSelberg.exists_forall_integrable_rsFinCellIntegrand_translate_and_dual
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.670037+00:00
-- url     : https://prove2.me/submissions/26ed4186-3712-5164-8ff3-5fc763fd4956

import Theorems.Thm_AutomorphicForm_continuous_whittakerCoefficient_and_exists_norm_le_mul_ideleNorm_det_rpow_of_isCuspAutomorphicFnAt_of_rightConv_eq
import Theorems.Thm_LanglandsTunnell_CubicInduction_exists_gauge_whittakerLoc_of_isGaugeMajorised3_of_form_ne_zero
import Theorems.Thm_LanglandsTunnell_RankinSelberg_exists_forall_integrable_bigCell_indicator_mul_finprod_iotaGL_of_gauge
import Theorems.Thm_AutomorphicForm_whittakerCoefficient_one_ne_zero_of_isIsotypicCuspFormAt_of_ne_zero
import Theorems.Thm_LanglandsTunnell_CubicInduction_forall_mem_gl3CyclicSubspace_exists_gauge_and_exists_gauge_dualWhittakerFn3
import Theorems.Thm_AutomorphicForm_SiegelCovering_coversModCentre_productionPinsGeneral_D_rat
import Theorems.Thm_NumberField_TateGlobal_continuous_ideleNorm
import Theorems.Thm_NumberField_AdeleRing_distribHaarChar_algebraMap
import Definitions.Def_AutomorphicForm_ProductionPinsGeneral
import Definitions.Def_AutomorphicForm_FormalBaseChange
import Definitions.Def_AutomorphicForm_IsotypicCuspSpace
import Definitions.Def_AutomorphicForm_ArchWeightCharTransport
import Definitions.Def_AutomorphicForm_FactorizableTestFn
import Definitions.Def_AutomorphicForm_WhittakerCoefficient
import Definitions.Def_NumberField_StandardGlobalAddCharRat
import Definitions.Def_LanglandsTunnell_ConverseData
import Definitions.Def_LanglandsTunnell_RankinSelbergEuler
import Definitions.Def_LanglandsTunnell_ArchBaseChange
import Definitions.Def_LanglandsTunnell_RSGlobalIntegral
import Definitions.Def_LanglandsTunnell_CubicInduction_MirabolicMajorant
import Definitions.Def_LanglandsTunnell_StandardLocalConstantsAt
import Definitions.Def_LanglandsTunnell_HonestLDatum
import Definitions.Def_AutomorphicForm_SmoothingKernel
import Definitions.Def_LanglandsTunnell_CubicInduction_Structure
import Definitions.Def_LanglandsTunnell_CubicInduction_AutomorphyDatum31
import Definitions.Def_LanglandsTunnell_CubicInduction_ArchZeta31
import Definitions.Def_LanglandsTunnell_CubicLambda
import Definitions.Def_LanglandsTunnell_HeckeTate
import Definitions.Def_M4aHerbrand_SIdeleClassGroup
import Definitions.Def_RatIdele_Normalizer
import Definitions.Def_AutomorphicForm_CuspidalConstituent
import Definitions.Def_NumberField_TateGlobalZeta
import Definitions.Def_AutomorphicForm_SiegelCoordinates
import Definitions.Def_UnramifiedWhittaker_HeckeRecursion
import Definitions.Def_LanglandsTunnell_RSCarrierSplit
import Definitions.Def_AutomorphicForm_UnipotentQuotient
import Definitions.Def_AutomorphicForm_LocalOrbitalBase
import Definitions.Def_AdelicDock_LocalEmbedding
import Definitions.Def_LanglandsTunnell_CubicInduction_GlobalZeta31
import Definitions.Def_LanglandsTunnell_RSCarrier
import Definitions.Def_LanglandsTunnell_DeltaLift
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LanglandsTunnell_RankinSelberg_exists_forall_integrable_rsFinCellIntegrand_translate_and_dual
p2m_attr_erase "instance" "RestrictedProduct.SecondCountableTopology_of_principal instCountableElemSetSetsCofinite_definitions instCountableOfNumberField_definitions instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions FLT.InfiniteAdeleBaseChange.uniqueSelfExtension NumberField.InfinitePlace.RamifiedExtension.instCoeExtension NumberField.InfinitePlace.UnramifiedExtension.instCoeExtension IsDedekindDomain.HeightOneSpectrum.Extension.instAlgebraSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnder IsDedekindDomain.HeightOneSpectrum.Extension.instAlgebraSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnder_1 IsDedekindDomain.HeightOneSpectrum.instMulActionHomClassAlgHomTensorProductAdicCompletionForallValEqUnder_definitions IsDedekindDomain.HeightOneSpectrum.Extension.instAlgebraAdicCompletionValEqUnder IsDedekindDomain.HeightOneSpectrum.adicCompletion.instFiniteForallValEqUnderOfFiniteDimensional_definitions IsDedekindDomain.HeightOneSpectrum.instIsBiscalarSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersTensorProductCoeAlgHomTensorAdicCompletionIntegersTo IsDedekindDomain.HeightOneSpectrum.Extension.instContinuousSMulAdicCompletionValEqUnder IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsModuleTopology IsDedekindDomain.HeightOneSpectrum.Extension.instFiniteSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnderOfFiniteDimensional IsDedekindDomain.HeightOneSpectrum.adicCompletion.instFiniteValEqUnderOfFiniteDimensional_definitions instIsBiscalarTensorProductCoeAlgHomBaseChange_of_algebraMap IsDedekindDomain.HeightOneSpectrum.instIsScalarTowerSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnder_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsModuleTopologyPi Submodule.instIsTopologicalModuleSubtypeMem Pi.instTopologicalModule IsTopologicalModule.toContinuousSMul IsTopologicalModule.toContinuousAdd instFunLike SemialgHomClass.toSemilinearMapClass instCoeTCSemialgHom SemialgHomClass.toRingHomClass SemialgHomClass.instSemialgHom"
p2m_attr_erase "instance" "IsDirectLimit.Module.instDirectLimitCoeLinearMapIdOfOfNonempty RestrictedProduct.instIsDirectLimit' RestrictedProduct.instIsDirectLimit RestrictedProduct.instNonemptyOrderDualElemSetSets_definitions RestrictedProduct.instDirectedSystem RestrictedProduct.instDirectedSystemCoeSubmoduleCoeLinearMapIdInclusionLinearMap RestrictedProduct.directed RestrictedProduct.instDirectedSystemOrderDualElemSetSetsCoeSubmodulePrincipalValMemCoeLinearMapIdInclusionLinearMap M4aHerbrand.Bridge.sigmaCompactSpace_finiteAdeleRing M4aHerbrand.Bridge.sigmaCompactSpace_adeleRing M4aHerbrand.Bridge.sigmaCompactSpace_infiniteAdeleRing M4aHerbrand.Bridge.sigmaCompactSpace_completion M4aHerbrand.Bridge.instT2SpaceAdeleRing"
p2m_attr_erase "simp" "ContinuousAddEquiv.restrictedProductPi_apply RestrictedProduct.flatten_homeomorph_apply RestrictedProduct.flatten_homeomorph'_symm_apply ContinuousMulEquiv.restrictedProductPi_symm_apply RestrictedProduct.flatten_homeomorph'_apply RestrictedProduct.flatten_homeomorph_symm_apply ContinuousMulEquiv.restrictedProductPi_apply ContinuousAddEquiv.restrictedProductPi_symm_apply RingEquiv.restrictedProductCongr_symm_apply RingEquiv.restrictedProductCongrRight_apply MulEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductProd_symm_apply_coe Equiv.restrictedProductCongrRight_apply AddEquiv.restrictedProductCongr_apply Equiv.restrictedProductCongrLeft'_symm_apply_apply Equiv.restrictedProductCongr_apply_apply Equiv.restrictedProductCongrLeft_apply_apply RestrictedProduct.flatten_equiv'_apply AddEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductCongr_symm_apply Equiv.restrictedProductCongrRight_symm_apply RestrictedProduct.flatten_equiv'_symm_apply AddEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductCongrLeft'_apply RestrictedProduct.flatten_apply RingEquiv.restrictedProductCongr_apply_apply RingEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductProd_apply RestrictedProduct.flatten_equiv_apply RestrictedProduct.flatten_equiv_symm_apply LinearEquiv.restrictedProductCongrLeft'_apply RestrictedProduct.not_mem_support RestrictedProduct.mem_structureSubring_iff RestrictedProduct.not_mem_mulSupport RestrictedProduct.support_neg RestrictedProduct.mem_indexSupport_iff RestrictedProduct.mulSupport_inv RestrictedProduct.mapAlongLinearMap_apply LocalGL2.coe_localRepSome LocalGL2.coe_diagPi"
p2m_attr_erase "simp" "LocalGL2.coe_localRepInf LocalGL2.coe_localRepSome_inv LocalGL2.coe_unipotentInt LocalGL2.coe_weylInt LocalGL2.coe_diagPi_inv LocalGL2.transposeGL_val LocalGL2.transposeGL_one LocalGL2.swapUnit_val M4aHerbrand.AdeleBaseChange.mk.sizeOf_spec M4aHerbrand.AdeleBaseChange.mk.injEq M4aHerbrand.Bridge.prodTensorAlgEquiv_tmul M4aHerbrand.Bridge.genuineβ_fst M4aHerbrand.Bridge.genuineβ_snd M4aHerbrand.ArchSemilocal.psiFactor_tmul M4aHerbrand.ArchSemilocal.psi_apply FLT.InfiniteAdeleBaseChange.evalAlgHom_apply FLT.InfiniteAdeleBaseChange.BaseChangeData.mk.sizeOf_spec FLT.InfiniteAdeleBaseChange.tensorPiAlgHom_tmul_apply FLT.InfiniteAdeleBaseChange.collapsePlaces_apply FLT.InfiniteAdeleBaseChange.tensorPiAlgEquiv_tmul_apply FLT.InfiniteAdeleBaseChange.InfinitePlaceData.mk.sizeOf_spec FLT.InfiniteAdeleBaseChange.InfinitePlaceData.mk.injEq FLT.InfiniteAdeleBaseChange.BaseChangeData.mk.injEq M4aHerbrand.Bridge.finiteConorm_apply SemialgHom.baseChange_of_algebraMap_tmul_left SemialgHom.baseChangeRightOfAlgebraMap_apply Pi.semialgHomPi_apply Pi.semialgHom_apply Module.Basis.rightBaseChange_apply LinearEquiv.coe_mulLeft LinearEquiv.coe_mulRight WithVal.semialgebraMap_toFun_ofVal Module.Basis.rightBaseChange_repr IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers.tensorCoe_tmul IsDedekindDomain.HeightOneSpectrum.tensorAdicCompletionIntegersTo_tmul SemialgHom.baseChangeRightOfAlgebraMap_coe IsDedekindDomain.HeightOneSpectrum.adicCompletion.integerBaseChangeLinearEquiv_tmul_apply SemialgHom.baseChange_of_algebraMap_tmul_right IsLocalization.map_moduleTensorEquiv_symm_tmul IsLocalization.leftModuleTensorEquiv_apply"
p2m_attr_erase "simp" "IsLocalization.moduleLid_symm_apply IsLocalization.leftModuleTensorEquiv_symm_apply IsLocalization.map_moduleTensorEquiv_tmul IsModuleTopology.continuousLinearEquiv_apply AlgEquiv.extendScalars_symm_apply IsModuleTopology.Module.Basis.equivFun_homeo_symm_apply IsModuleTopology.Module.Basis.equivFun_homeo_apply IsModuleTopology.continuousAlgEquivOfIsBiscalar_apply AlgEquiv.extendScalars_apply IsModuleTopology.continuousLinearEquiv_symm_apply SemialgHom.restrictScalars_toFun SemialgHom.mk.sizeOf_spec SemialgHom.mk.injEq SemialgHom.coe_coe coe_mk TensorProduct.RightActions.smul_def TensorProduct.RightActions.Module.TensorProduct.comm_symm_apply_tmul TensorProduct.RightActions.LinearMap.baseChange_id TensorProduct.RightActions.algebraMap_eval TensorProduct.RightActions.Module.TensorProduct.comm_apply_tmul TensorProduct.RightActions.Algebra.TensorProduct.comm_symm_apply_tmul TensorProduct.RightActions.Algebra.TensorProduct.comm_apply_tmul M4aHerbrand.Bridge.tensorAdeleRingEquiv_apply M4aHerbrand.Bridge.flattenPlaces_apply M4aHerbrand.Bridge.congrPlaces_apply M4aHerbrand.Bridge.integralTensorRingEquiv_tmul M4aHerbrand.Bridge.moduleStructureBridge_apply RestrictedProduct.lTensorEquivLeft_tmul RestrictedProduct.lTensorEquiv_tmul RestrictedProduct.lTensorLeft_tmul RestrictedProduct.lTensor_tmul IsDirectLimit.Module.linearEquiv_symm_apply IsDirectLimit.linearEquiv_symm_apply IsDirectLimit.lift_of IsDirectLimit.Module.linearEquiv_apply IsDirectLimit.Module.lift_of IsDirectLimit.Equiv_apply LanglandsTunnell.CubicInduction.diagonal3_coe LanglandsTunnell.CubicInduction.halfModulus3_one LanglandsTunnell.CubicInduction.torusChar3_one"

set_option autoImplicit false

open IsDedekindDomain NumberField AutomorphicForm LanglandsTunnell LanglandsTunnell.Converse
open NumberField.TateGlobal NumberField.AdelicLevel NumberField.AdelicBox NumberField.InfinitePlace.Completion
open LanglandsTunnell.RankinSelberg LanglandsTunnell.CubicInduction MeasureTheory UnramifiedWhittaker AdelicDock
open LanglandsTunnell.TateLocal NumberField.StandardAddChar Topology
open AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering
open scoped nonZeroDivisors NNReal ENNReal Matrix

attribute [local instance] NumberField.AdelicHaar.glBorel NumberField.AdelicHaar.borelSpace_glBorel

noncomputable section

namespace KcCellIntA59

section MatrixFurniture

variable {A : Type*} [CommRing A]

theorem transposeInv3_mul (g h : GL (Fin 3) A) : transposeInv3 (g * h) = transposeInv3 g * transposeInv3 h :=
  Units.ext (by
    show (((g * h)⁻¹ : GL (Fin 3) A) : Matrix (Fin 3) (Fin 3) A)ᵀ =
      ((g⁻¹ : GL (Fin 3) A) : Matrix (Fin 3) (Fin 3) A)ᵀ * ((h⁻¹ : GL (Fin 3) A) : Matrix (Fin 3) (Fin 3) A)ᵀ
    rw [mul_inv_rev, Units.val_mul, Matrix.transpose_mul])

theorem transposeInv3_one : transposeInv3 (1 : GL (Fin 3) A) = 1 :=
  Units.ext (by
    show (((1 : GL (Fin 3) A)⁻¹ : GL (Fin 3) A) : Matrix (Fin 3) (Fin 3) A)ᵀ = 1
    rw [inv_one, Units.val_one, Matrix.transpose_one])

theorem transposeInv3_map {B : Type*} [CommRing B] (f : A →+* B) (g : GL (Fin 3) A) :
    transposeInv3 (Matrix.GeneralLinearGroup.map f g) = Matrix.GeneralLinearGroup.map f (transposeInv3 g) := by
  refine Units.ext ?_
  show (((Matrix.GeneralLinearGroup.map f g)⁻¹ : GL (Fin 3) B) : Matrix (Fin 3) (Fin 3) B)ᵀ =
    f.mapMatrix (((g⁻¹ : GL (Fin 3) A) : Matrix (Fin 3) (Fin 3) A)ᵀ)
  rw [← map_inv]
  show (f.mapMatrix ((g⁻¹ : GL (Fin 3) A) : Matrix (Fin 3) (Fin 3) A))ᵀ = _
  rw [RingHom.mapMatrix_apply, RingHom.mapMatrix_apply, Matrix.transpose_map]

theorem longWeyl3_mul_transposeInv3_iotaGL_unipotentGL2 {F : Type*} [Field F] (x : F) :
    (longWeyl3 : GL (Fin 3) F) * transposeInv3 (iotaGL (unipotentGL2 x)) = upperUnipotent3 0 (-x) 0 * longWeyl3 := by
  refine Units.ext ?_
  have hinv : ((iotaGL (unipotentGL2 x))⁻¹ : GL (Fin 3) F) = iotaGL (unipotentGL2 (-x)) := by
    rw [← map_inv]
    congr 1
    refine inv_eq_of_mul_eq_one_right ?_
    rw [← unipotentGL2_add, add_neg_cancel, unipotentGL2_zero]
  show ((longWeyl3 : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) *
      (((iotaGL (unipotentGL2 x))⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F)ᵀ =
    ((upperUnipotent3 0 (-x) 0 : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) *
      ((longWeyl3 : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F)
  rw [hinv]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [embedMat2, Matrix.mul_apply, Fin.sum_univ_three]

end MatrixFurniture

section AddChars

theorem norm_psiPadicFun {p : ℕ} [Fact p.Prime] (x : ℚ_[p]) : ‖psiPadicFun x‖ = 1 := by
  unfold psiPadicFun
  set a : ℤ := (exists_pPow_approx x).choose
  set k : ℕ := (exists_pPow_approx x).choose_spec.choose
  have h : -(2 * (Real.pi : ℂ) * Complex.I) * ((a : ℂ) / (p : ℂ) ^ k) =
      ((-(2 * Real.pi * ((a : ℝ) / (p : ℝ) ^ k)) : ℝ) : ℂ) * Complex.I := by
    push_cast
    ring
  rw [h, Complex.norm_exp_ofReal_mul_I]

local instance (q : Nat.Primes) : Fact q.1.Prime := ⟨q.2⟩ in
theorem norm_psiV (v : HeightOneSpectrum (𝓞 ℚ)) (x : v.adicCompletion ℚ) : ‖psiV v x‖ = 1 := by
  rw [psiV_apply, psiPadic_apply, norm_psiPadicFun]

theorem norm_psiFin (t : FiniteAdeleRing (𝓞 ℚ) ℚ) : ‖psiFin t‖ = 1 := by
  rw [psiFin_apply, finprod_eq_prod_of_mulSupport_subset _ (s := (mulSupport_psiV_finite t).toFinset)
    (by simp), norm_prod]
  exact Finset.prod_eq_one fun v _ => norm_psiV v _

theorem norm_psiArchPlace (v : InfinitePlace ℚ) (x : v.Completion) : ‖psiArchPlace v x‖ = 1 := by
  rw [psiArchPlace_apply]
  have h : (2 * (Real.pi : ℂ) * Complex.I) *
      ((InfinitePlace.Completion.extensionEmbeddingOfIsReal (IsTotallyReal.isReal v) x : ℝ) : ℂ) =
      ((2 * Real.pi * (InfinitePlace.Completion.extensionEmbeddingOfIsReal (IsTotallyReal.isReal v) x : ℝ) : ℝ) : ℂ) *
        Complex.I := by
    push_cast
    ring
  rw [h, Complex.norm_exp_ofReal_mul_I]

theorem norm_psiArch (x : InfiniteAdeleRing ℚ) : ‖psiArch x‖ = 1 := by
  rw [psiArch_apply, finprod_eq_prod_of_fintype, norm_prod]
  exact Finset.prod_eq_one fun v _ => norm_psiArchPlace v _

theorem norm_psiQ (t : AdeleRing (𝓞 ℚ) ℚ) : ‖psiQ t‖ = 1 := by
  rw [psiQ_apply, norm_mul, norm_psiArch, norm_psiFin, one_mul]

theorem psiQ_adeleSingleAt (v : HeightOneSpectrum (𝓞 ℚ)) (x : v.adicCompletion ℚ) :
    psiQ (adeleSingleAt ℚ v x) = psiV v x := by
  rw [adeleSingleAt_apply, psiQ_apply, AddChar.map_zero_eq_one, one_mul, psiFin_apply]
  rw [finprod_eq_single _ v]
  · rw [finAdeleSingleAt_apply_self]
  · intro w hw
    rw [finAdeleSingleAt_apply_of_ne ℚ v x hw, AddChar.map_zero_eq_one]

theorem psiLoc_eq_of_inv_eq_psiQ {ψ : AddChar (AdeleRing (𝓞 ℚ) ℚ) ℂ} (hψQ : ψ⁻¹ = psiQ)
    (v : HeightOneSpectrum (𝓞 ℚ)) (x : v.adicCompletion ℚ) : psiLoc ψ v x = psiV v (-x) := by
  have hψ : ψ = psiQ⁻¹ := by rw [← hψQ, inv_inv]
  show ψ (adeleSingleAt ℚ v x) = _
  rw [hψ, AddChar.inv_apply, ← map_neg, psiQ_adeleSingleAt]

theorem norm_psiLoc {ψ : AddChar (AdeleRing (𝓞 ℚ) ℚ) ℂ} (hψQ : ψ⁻¹ = psiQ)
    (v : HeightOneSpectrum (𝓞 ℚ)) (x : v.adicCompletion ℚ) : ‖psiLoc ψ v x‖ = 1 := by
  rw [psiLoc_eq_of_inv_eq_psiQ hψQ, norm_psiV]

end AddChars

section FinAdelic

theorem ratArchGL2_mul (g h : AdelicGL2 (𝓞 ℚ) ℚ) : ratArchGL2 (g * h) = ratArchGL2 g * ratArchGL2 h := by
  simp only [ratArchGL2, map_mul]

theorem ratArchGL2_of_mem {g : AdelicGL2 (𝓞 ℚ) ℚ} (hg : g ∈ finiteAdelicGL2Subgroup ℚ) : ratArchGL2 g = 1 := by
  simp only [ratArchGL2, (mem_finiteAdelicGL2Subgroup_iff ℚ g).1 hg, map_one]

theorem ratArchGL2_archRealGLAt (m : GL (Fin 2) ℝ) :
    ratArchGL2 (archRealGLAt (IsTotallyReal.isReal (default : InfinitePlace ℚ)) m) = m := by
  have h := archRealProjAt_archRealGLAt (F := ℚ) (IsTotallyReal.isReal (default : InfinitePlace ℚ)) m
  refine Eq.trans ?_ h
  exact Units.ext (Matrix.ext fun i j => rfl)

theorem finFactor_coe (g : finiteAdelicGL2Subgroup ℚ) : RSCarrier.finFactor (g : AdelicGL2 (𝓞 ℚ) ℚ) = g := by
  refine Subtype.ext ?_
  show (archRealGLAt (IsTotallyReal.isReal (default : InfinitePlace ℚ)) (ratArchGL2 (g : AdelicGL2 (𝓞 ℚ) ℚ)))⁻¹ *
      (g : AdelicGL2 (𝓞 ℚ) ℚ) = g
  rw [ratArchGL2_of_mem g.2, map_one, inv_one, one_mul]

theorem finFactor_mul_coe (Y : AdelicGL2 (𝓞 ℚ) ℚ) (X : finiteAdelicGL2Subgroup ℚ) :
    RSCarrier.finFactor (Y * (X : AdelicGL2 (𝓞 ℚ) ℚ)) = RSCarrier.finFactor Y * X := by
  refine Subtype.ext ?_
  show (archRealGLAt (IsTotallyReal.isReal (default : InfinitePlace ℚ)) (ratArchGL2 (Y * (X : AdelicGL2 (𝓞 ℚ) ℚ))))⁻¹ *
      (Y * (X : AdelicGL2 (𝓞 ℚ) ℚ)) =
    (archRealGLAt (IsTotallyReal.isReal (default : InfinitePlace ℚ)) (ratArchGL2 Y))⁻¹ * Y * (X : AdelicGL2 (𝓞 ℚ) ℚ)
  rw [ratArchGL2_mul, ratArchGL2_of_mem X.2, mul_one, mul_assoc]

theorem finFactor_archRealGLAt (m : GL (Fin 2) ℝ) :
    RSCarrier.finFactor (archRealGLAt (IsTotallyReal.isReal (default : InfinitePlace ℚ)) m) = 1 := by
  refine Subtype.ext ?_
  show (archRealGLAt (IsTotallyReal.isReal (default : InfinitePlace ℚ))
      (ratArchGL2 (archRealGLAt (IsTotallyReal.isReal (default : InfinitePlace ℚ)) m)))⁻¹ *
      archRealGLAt (IsTotallyReal.isReal (default : InfinitePlace ℚ)) m = 1
  rw [ratArchGL2_archRealGLAt, inv_mul_cancel]

theorem coe_finFactor (Y : AdelicGL2 (𝓞 ℚ) ℚ) :
    ((RSCarrier.finFactor Y : finiteAdelicGL2Subgroup ℚ) : AdelicGL2 (𝓞 ℚ) ℚ) =
      (archRealGLAt (IsTotallyReal.isReal (default : InfinitePlace ℚ)) (ratArchGL2 Y))⁻¹ * Y := rfl

theorem transposeInvN_mem (g : finiteAdelicGL2Subgroup ℚ) :
    transposeInvN (Fin 2) (g : AdelicGL2 (𝓞 ℚ) ℚ) ∈ finiteAdelicGL2Subgroup ℚ := by
  rw [mem_finiteAdelicGL2Subgroup_iff]
  show Matrix.GeneralLinearGroup.map (adeleArch (𝓞 ℚ) ℚ) (transposeInvN (Fin 2) (g : AdelicGL2 (𝓞 ℚ) ℚ)) = 1
  have htr : transposeInvN (Fin 2) (Matrix.GeneralLinearGroup.map (adeleArch (𝓞 ℚ) ℚ) (g : AdelicGL2 (𝓞 ℚ) ℚ)) =
      Matrix.GeneralLinearGroup.map (adeleArch (𝓞 ℚ) ℚ) (transposeInvN (Fin 2) (g : AdelicGL2 (𝓞 ℚ) ℚ)) := by
    refine Units.ext ?_
    rw [coe_transposeInvN, ← map_inv]
    show (((adeleArch (𝓞 ℚ) ℚ).mapMatrix (((g : AdelicGL2 (𝓞 ℚ) ℚ)⁻¹ : AdelicGL2 (𝓞 ℚ) ℚ) :
        Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 ℚ) ℚ))))ᵀ =
      (adeleArch (𝓞 ℚ) ℚ).mapMatrix ((((g : AdelicGL2 (𝓞 ℚ) ℚ)⁻¹ : AdelicGL2 (𝓞 ℚ) ℚ) :
        Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 ℚ) ℚ))ᵀ)
    rw [RingHom.mapMatrix_apply, RingHom.mapMatrix_apply, Matrix.transpose_map]
  rw [← htr]
  have hg : Matrix.GeneralLinearGroup.map (adeleArch (𝓞 ℚ) ℚ) (g : AdelicGL2 (𝓞 ℚ) ℚ) = 1 :=
    (mem_finiteAdelicGL2Subgroup_iff ℚ _).1 g.2
  rw [hg]
  refine Units.ext ?_
  rw [coe_transposeInvN, inv_one, Units.val_one, Matrix.transpose_one]

theorem continuous_transposeInvN_adelic :
    Continuous fun g : AdelicGL2 (𝓞 ℚ) ℚ => transposeInvN (Fin 2) g := by
  refine Units.continuous_iff.2 ⟨?_, ?_⟩
  · exact (Units.continuous_coe_inv.matrix_transpose :
      Continuous fun g : AdelicGL2 (𝓞 ℚ) ℚ =>
        (((g⁻¹ : AdelicGL2 (𝓞 ℚ) ℚ)) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 ℚ) ℚ))ᵀ)
  · exact (Units.continuous_val.matrix_transpose :
      Continuous fun g : AdelicGL2 (𝓞 ℚ) ℚ => ((g : AdelicGL2 (𝓞 ℚ) ℚ) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 ℚ) ℚ))ᵀ)

def tInv (g : finiteAdelicGL2Subgroup ℚ) : finiteAdelicGL2Subgroup ℚ :=
  ⟨transposeInvN (Fin 2) (g : AdelicGL2 (𝓞 ℚ) ℚ), transposeInvN_mem g⟩

theorem continuous_tInv : Continuous (tInv : finiteAdelicGL2Subgroup ℚ → finiteAdelicGL2Subgroup ℚ) :=
  (continuous_transposeInvN_adelic.comp continuous_subtype_val).subtype_mk _

theorem det_transposeInvN (g : AdelicGL2 (𝓞 ℚ) ℚ) :
    Matrix.GeneralLinearGroup.det (transposeInvN (Fin 2) g) = (Matrix.GeneralLinearGroup.det g)⁻¹ := by
  rw [← map_inv]
  refine Units.ext ?_
  simp only [Matrix.GeneralLinearGroup.val_det_apply, coe_transposeInvN, Matrix.det_transpose]

theorem continuous_det_adelic : Continuous fun g : AdelicGL2 (𝓞 ℚ) ℚ => Matrix.GeneralLinearGroup.det g :=
  Units.continuous_iff.2 ⟨(Units.continuous_val.matrix_det :
      Continuous fun g : AdelicGL2 (𝓞 ℚ) ℚ => (g : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 ℚ) ℚ)).det),
    (Units.continuous_coe_inv.matrix_det :
      Continuous fun g : AdelicGL2 (𝓞 ℚ) ℚ => ((g⁻¹ : AdelicGL2 (𝓞 ℚ) ℚ) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 ℚ) ℚ)).det)⟩

theorem continuous_ideleNorm_det_coe :
    Continuous fun g : finiteAdelicGL2Subgroup ℚ => ideleNorm ℚ (Matrix.GeneralLinearGroup.det (g : AdelicGL2 (𝓞 ℚ) ℚ)) :=
  ((NumberField.TateGlobal.continuous_ideleNorm ℚ).comp continuous_det_adelic).comp continuous_subtype_val

theorem ideleNorm_det_globalPoints (γ : GL (Fin 2) ℚ) :
    ideleNorm ℚ (Matrix.GeneralLinearGroup.det (globalPoints (𝓞 ℚ) ℚ γ)) = 1 := by
  letI : MeasurableSpace (AdeleRing (𝓞 ℚ) ℚ) := NumberField.AdelicHaar.adeleBorel (𝓞 ℚ) ℚ
  haveI : BorelSpace (AdeleRing (𝓞 ℚ) ℚ) := NumberField.AdelicHaar.borelSpace_adeleBorel (𝓞 ℚ) ℚ
  have h := NumberField.AdeleRing.distribHaarChar_algebraMap ℚ (Matrix.GeneralLinearGroup.det γ)
  unfold ideleNorm
  rw [show globalPoints (𝓞 ℚ) ℚ γ = Matrix.GeneralLinearGroup.map (algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ)) γ from rfl,
    Matrix.GeneralLinearGroup.map_det]
  rw [show (Units.map ((algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ) : ℚ →* AdeleRing (𝓞 ℚ) ℚ)))
      (Matrix.GeneralLinearGroup.det γ) =
      Units.map (algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ)).toMonoidHom (Matrix.GeneralLinearGroup.det γ) from rfl]
  rw [h]
  rfl

theorem componentAt3_iota (v : HeightOneSpectrum (𝓞 ℚ)) (g : AdelicGL2 (𝓞 ℚ) ℚ) :
    componentAt3 (𝓞 ℚ) ℚ v (iota (𝓞 ℚ) ℚ g) = iotaGL (localAt ℚ v g) := by
  refine Units.ext (Matrix.ext fun i j => ?_)
  show ((finAdeleEval (𝓞 ℚ) ℚ v).comp (adeleFin (𝓞 ℚ) ℚ)) (embedMat2 (g : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 ℚ) ℚ)) i j) =
    embedMat2 (localAt ℚ v g : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)) i j
  fin_cases i <;> fin_cases j <;> simp [embedMat2] <;> rfl

theorem componentAt3_transposeInv3 (v : HeightOneSpectrum (𝓞 ℚ)) (k : AdelicGL 3 (𝓞 ℚ) ℚ) :
    componentAt3 (𝓞 ℚ) ℚ v (transposeInv3 k) = transposeInv3 (componentAt3 (𝓞 ℚ) ℚ v k) :=
  (transposeInv3_map _ k).symm

theorem localAt_placeEmbed_of_ne (p : HeightOneSpectrum (𝓞 ℚ)) {q : HeightOneSpectrum (𝓞 ℚ)} (hq : q ≠ p)
    (x : GL (Fin 2) (p.adicCompletion ℚ)) : localAt ℚ q (placeEmbed ℚ p x) = 1 := by
  show finComponent (𝓞 ℚ) ℚ q (glFin (𝓞 ℚ) ℚ (finEmbed (𝓞 ℚ) ℚ (localEmbed (𝓞 ℚ) ℚ p x))) = 1
  rw [glFin_finEmbed, finComponent_localEmbed_of_ne (𝓞 ℚ) ℚ p x hq]

theorem localAt_listProd_eq_one {ι : Type*} (L : List ι) (f : ι → AdelicGL2 (𝓞 ℚ) ℚ) (p : HeightOneSpectrum (𝓞 ℚ))
    (h : ∀ q ∈ L, localAt ℚ p (f q) = 1) : localAt ℚ p (L.map f).prod = 1 := by
  rw [map_list_prod, List.map_map]
  exact List.prod_eq_one fun x hx => by
    obtain ⟨q, hq, rfl⟩ := List.mem_map.1 hx
    exact h q hq

end FinAdelic

section GL3Local

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] {Y : Type*}

theorem isLocallyConstant_of_rightInvariant (U : Subgroup G) (hU : IsOpen (U : Set G)) (W : G → Y)
    (h : ∀ k ∈ U, ∀ g, W (g * k) = W g) : IsLocallyConstant W := by
  refine (IsLocallyConstant.iff_exists_open W).2 fun g =>
    ⟨(fun k => g * k) '' (U : Set G), ?_, ⟨1, U.one_mem, mul_one g⟩, ?_⟩
  · exact (Homeomorph.mulLeft g).isOpenMap _ hU
  · rintro _ ⟨k, hk, rfl⟩
    exact h k hk g

end GL3Local

section GL3LocalQ

variable (v : HeightOneSpectrum (𝓞 ℚ))

theorem continuous_transposeInv3_local : Continuous (transposeInv3 : LocalGL3 v → LocalGL3 v) := by
  refine Units.continuous_iff.2 ⟨?_, ?_⟩
  · exact (Units.continuous_coe_inv.matrix_transpose :
      Continuous fun g : LocalGL3 v => (((g⁻¹ : LocalGL3 v)) : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ))ᵀ)
  · exact (Units.continuous_val.matrix_transpose :
      Continuous fun g : LocalGL3 v => ((g : LocalGL3 v) : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ))ᵀ)

theorem isOpen_localMaximalCompact3 : IsOpen (localMaximalCompact3 (𝓞 ℚ) ℚ v : Set (LocalGL3 v)) := by
  have hO : IsOpen {y : v.adicCompletion ℚ | Valued.v y ≤ 1} := by
    have : {y : v.adicCompletion ℚ | Valued.v y ≤ 1} = (v.adicCompletionIntegers ℚ : Set (v.adicCompletion ℚ)) := by
      ext y; simp [HeightOneSpectrum.mem_adicCompletionIntegers]
    rw [this]; exact Valued.isOpen_valuationSubring _
  have h1 : ∀ i j : Fin 3, IsOpen {k : LocalGL3 v | Valued.v ((k : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) i j) ≤ 1} :=
    fun i j => hO.preimage (Units.continuous_val.matrix_elem i j)
  have h2 : ∀ i j : Fin 3, IsOpen {k : LocalGL3 v |
      Valued.v (((k⁻¹ : LocalGL3 v) : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) i j) ≤ 1} :=
    fun i j => hO.preimage (Units.continuous_coe_inv.matrix_elem i j)
  have heq : (localMaximalCompact3 (𝓞 ℚ) ℚ v : Set (LocalGL3 v)) =
      (⋂ i, ⋂ j, {k : LocalGL3 v | Valued.v ((k : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) i j) ≤ 1}) ∩
        ⋂ i, ⋂ j, {k : LocalGL3 v | Valued.v (((k⁻¹ : LocalGL3 v) : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) i j) ≤ 1} := by
    ext k
    simp only [SetLike.mem_coe, mem_localMaximalCompact3_iff, Set.mem_inter_iff, Set.mem_iInter, Set.mem_setOf_eq]
  rw [heq]
  exact (isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun j => h1 i j).inter
    (isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun j => h2 i j)

theorem mem_localLevelOne_top_iff (k : GL (Fin 2) (v.adicCompletion ℚ)) :
    k ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ v ⊤ ↔ k ∈ localIntegralSet ℚ v := by
  have aux : ∀ m : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ), (∀ i j, m i j ∈ v.adicCompletionIntegers ℚ) →
      AdelicDock.IsLocalLevelOne (𝓞 ℚ) ℚ v ⊤ m := by
    intro m h
    refine ⟨h, ?_, ?_⟩
    · rw [AdelicLevel.idealBound_top]
      exact (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).mp (h 1 0)
    · rw [AdelicLevel.idealBound_top]
      calc Valued.v (m 1 1 - 1) ≤ max (Valued.v (m 1 1)) (Valued.v (1 : v.adicCompletion ℚ)) := Valuation.map_sub _ _ _
        _ ≤ 1 := max_le ((HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).mp (h 1 1)) (by simp)
  rw [AdelicDock.mem_localLevelOne_iff, mem_localIntegralSet]
  constructor
  · rintro ⟨h1, h2⟩; exact ⟨h1.integral, h2.integral⟩
  · rintro ⟨h1, h2⟩; exact ⟨aux _ h1, aux _ h2⟩

theorem iotaGL_mem_localMaximalCompact3 {g : GL (Fin 2) (v.adicCompletion ℚ)} (hg : g ∈ localIntegralSet ℚ v) :
    iotaGL g ∈ localMaximalCompact3 (𝓞 ℚ) ℚ v := by
  rw [mem_localIntegralSet] at hg
  have aux : ∀ (M : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)), (∀ i j, M i j ∈ v.adicCompletionIntegers ℚ) →
      ∀ i j, Valued.v (embedMat2 M i j) ≤ 1 := by
    intro M hM i j
    have hM' : ∀ i j, Valued.v (M i j) ≤ 1 := fun i j => (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).1 (hM i j)
    fin_cases i <;> fin_cases j <;> simp [embedMat2, hM']
  refine ⟨fun i j => aux _ hg.1 i j, fun i j => ?_⟩
  rw [← map_inv]
  exact aux _ hg.2 i j

theorem transposeInv3_mem_localMaximalCompact3 {k : LocalGL3 v} (hk : k ∈ localMaximalCompact3 (𝓞 ℚ) ℚ v) :
    transposeInv3 k ∈ localMaximalCompact3 (𝓞 ℚ) ℚ v := by
  refine ⟨fun i j => ?_, fun i j => ?_⟩
  · show Valued.v ((((k⁻¹ : LocalGL3 v)) : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ))ᵀ i j) ≤ 1
    rw [Matrix.transpose_apply]; exact hk.2 j i
  · show Valued.v (((k : LocalGL3 v) : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ))ᵀ i j) ≤ 1
    rw [Matrix.transpose_apply]; exact hk.1 j i

theorem longWeyl3_mem_localMaximalCompact3 : (longWeyl3 : LocalGL3 v) ∈ localMaximalCompact3 (𝓞 ℚ) ℚ v := by
  have h : ∀ i j : Fin 3, Valued.v ((!![0, 0, 1; 0, 1, 0; 1, 0, 0] : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) i j) ≤ 1 := by
    intro i j; fin_cases i <;> fin_cases j <;> simp
  refine ⟨fun i j => ?_, fun i j => ?_⟩
  · exact h i j
  · have : ((longWeyl3 : LocalGL3 v)⁻¹ : LocalGL3 v) = longWeyl3 := inv_eq_of_mul_eq_one_right (Units.ext (by
      show (!![0, 0, 1; 0, 1, 0; 1, 0, 0] : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) * !![0, 0, 1; 0, 1, 0; 1, 0, 0] = 1
      ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three]))
    rw [this]; exact h i j

variable {v}

theorem norm_apply_iotaGL_unipotentGL2_mul {ψ : AddChar (AdeleRing (𝓞 ℚ) ℚ) ℂ} (hψQ : ψ⁻¹ = psiQ)
    {W : LocalGL3 v → ℂ} (hW : IsGL3PsiWhittakerFn (psiLoc ψ v) W)
    (x : v.adicCompletion ℚ) (h : LocalGL3 v) : ‖W (iotaGL (unipotentGL2 x) * h)‖ = ‖W h‖ := by
  rw [iotaGL_unipotentGL2, hW x 0 0 h, norm_mul, add_zero, norm_psiLoc hψQ, one_mul]

theorem norm_dualWhittakerFn3_iotaGL_unipotentGL2_mul {ψ : AddChar (AdeleRing (𝓞 ℚ) ℚ) ℂ} (hψQ : ψ⁻¹ = psiQ)
    {W : LocalGL3 v → ℂ} (hW : IsGL3PsiWhittakerFn (psiLoc ψ v) W)
    (x : v.adicCompletion ℚ) (h : LocalGL3 v) :
    ‖dualWhittakerFn3 W (iotaGL (unipotentGL2 x) * h)‖ = ‖dualWhittakerFn3 W h‖ := by
  rw [dualWhittakerFn3_apply, dualWhittakerFn3_apply, transposeInv3_mul, ← mul_assoc,
    longWeyl3_mul_transposeInv3_iotaGL_unipotentGL2, mul_assoc, hW 0 (-x) 0, norm_mul, zero_add,
    norm_psiLoc hψQ, one_mul]

theorem translate_mem_gl3CyclicSubspace (W : LocalGL3 v → ℂ) (m : LocalGL3 v) :
    (fun h => W (h * m)) ∈ gl3CyclicSubspace W :=
  Submodule.subset_span ⟨m, rfl⟩

theorem isGL3PsiWhittakerFn_translate {ψ : AddChar (v.adicCompletion ℚ) ℂ} {W : LocalGL3 v → ℂ}
    (hW : IsGL3PsiWhittakerFn ψ W) (m : LocalGL3 v) : IsGL3PsiWhittakerFn ψ (fun h => W (h * m)) := by
  intro x y z g
  show W (upperUnipotent3 x y z * g * m) = ψ (x + y) * W (g * m)
  rw [mul_assoc, hW]

theorem dualWhittakerFn3_mul_eq (W : LocalGL3 v → ℂ) (m h : LocalGL3 v) :
    dualWhittakerFn3 W (h * m) = dualWhittakerFn3 (fun x => W (x * transposeInv3 m)) h := by
  rw [dualWhittakerFn3_apply, dualWhittakerFn3_apply, transposeInv3_mul, mul_assoc]

variable {K : Type} [Field K] [NumberField K] [Algebra (𝓞 ℚ) (𝓞 K)] [Algebra.IsIntegral (𝓞 ℚ) (𝓞 K)]
variable {pins : CarrierPins ℚ} {ψ : AddChar (AdeleRing (𝓞 ℚ) ℚ) ℂ} {μ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ}

theorem exists_open_stabiliser (F : CubicInductionForm K pins ψ μ)
    (hBad : ∀ T : Finset (HeightOneSpectrum (𝓞 ℚ)),
      (∀ v ∈ T, IsBadPlace K μ v → ∃ Uv : Subgroup (LocalGL3 v), IsOpen (Uv : Set (LocalGL3 v)) ∧
        ∀ k ∈ Uv, ∀ g : LocalGL3 v, F.whittakerLoc v (g * k) = F.whittakerLoc v g) ∧
      (∀ v ∈ T, IsBadPlace K μ v → ∀ W ∈ gl3CyclicSubspace (F.whittakerLoc v), W ≠ 0 →
        F.whittakerLoc v ∈ gl3CyclicSubspace W))
    (v : HeightOneSpectrum (𝓞 ℚ)) :
    ∃ Uv : Subgroup (LocalGL3 v), IsOpen (Uv : Set (LocalGL3 v)) ∧
      ∀ k ∈ Uv, ∀ g : LocalGL3 v, F.whittakerLoc v (g * k) = F.whittakerLoc v g := by
  by_cases hb : IsBadPlace K μ v
  · exact (hBad {v}).1 v (Finset.mem_singleton_self v) hb
  · exact ⟨localMaximalCompact3 (𝓞 ℚ) ℚ v, isOpen_localMaximalCompact3 v, fun k hk g => (F.spherical v hb).1 g k hk⟩

theorem isLocallyConstant_whittakerLoc (F : CubicInductionForm K pins ψ μ)
    (hBad : ∀ T : Finset (HeightOneSpectrum (𝓞 ℚ)),
      (∀ v ∈ T, IsBadPlace K μ v → ∃ Uv : Subgroup (LocalGL3 v), IsOpen (Uv : Set (LocalGL3 v)) ∧
        ∀ k ∈ Uv, ∀ g : LocalGL3 v, F.whittakerLoc v (g * k) = F.whittakerLoc v g) ∧
      (∀ v ∈ T, IsBadPlace K μ v → ∀ W ∈ gl3CyclicSubspace (F.whittakerLoc v), W ≠ 0 →
        F.whittakerLoc v ∈ gl3CyclicSubspace W))
    (v : HeightOneSpectrum (𝓞 ℚ)) : IsLocallyConstant (F.whittakerLoc v) := by
  obtain ⟨Uv, hUo, hU⟩ := exists_open_stabiliser F hBad v
  exact isLocallyConstant_of_rightInvariant Uv hUo _ hU

theorem whittakerLoc_iotaGL_eq_one_of_good (F : CubicInductionForm K pins ψ μ)
    (hF0 : ∀ v, ¬ IsRamifiedIn K v → addCharLevel (psiLoc ψ v) = 0 → F.whittakerLoc v 1 = 1)
    (hlev : ∀ v : HeightOneSpectrum (𝓞 ℚ), addCharLevel (psiLoc ψ v) = 0)
    {v : HeightOneSpectrum (𝓞 ℚ)} (hgood : ¬ IsBadPlace K μ v)
    {g : GL (Fin 2) (v.adicCompletion ℚ)} (hg : g ∈ localIntegralSet ℚ v) :
    F.whittakerLoc v (iotaGL g) = 1 := by
  have hnr : ¬ IsRamifiedIn K v := fun h => hgood (Or.inl h)
  have h1 : F.whittakerLoc v 1 = 1 := hF0 v hnr (hlev v)
  have hsph := (F.spherical v hgood).1
  rw [← one_mul (iotaGL g), hsph, h1]
  exact iotaGL_mem_localMaximalCompact3 v hg

theorem dualWhittakerFn3_iotaGL_eq_one_of_good (F : CubicInductionForm K pins ψ μ)
    (hF0 : ∀ v, ¬ IsRamifiedIn K v → addCharLevel (psiLoc ψ v) = 0 → F.whittakerLoc v 1 = 1)
    (hlev : ∀ v : HeightOneSpectrum (𝓞 ℚ), addCharLevel (psiLoc ψ v) = 0)
    {v : HeightOneSpectrum (𝓞 ℚ)} (hgood : ¬ IsBadPlace K μ v)
    {g : GL (Fin 2) (v.adicCompletion ℚ)} (hg : g ∈ localIntegralSet ℚ v) :
    dualWhittakerFn3 (F.whittakerLoc v) (iotaGL g) = 1 := by
  have hnr : ¬ IsRamifiedIn K v := fun h => hgood (Or.inl h)
  have h1 : F.whittakerLoc v 1 = 1 := hF0 v hnr (hlev v)
  have hsph := (F.spherical v hgood).1
  rw [dualWhittakerFn3_apply, ← one_mul (longWeyl3 * transposeInv3 (iotaGL g)), hsph, h1]
  exact Subgroup.mul_mem _ (longWeyl3_mem_localMaximalCompact3 v)
    (transposeInv3_mem_localMaximalCompact3 v (iotaGL_mem_localMaximalCompact3 v hg))

end GL3LocalQ

section GL2Side

theorem ideleNorm_inv (x : (AdeleRing (𝓞 ℚ) ℚ)ˣ) : ideleNorm ℚ x⁻¹ = (ideleNorm ℚ x)⁻¹ := by
  simp only [ideleNorm, map_inv, NNReal.coe_inv]

theorem finWhittaker_continuous_and_growth [SecondCountableTopology (AdelicGL2 (𝓞 ℚ) ℚ)]
    (χ : (productionPinsGeneral ℚ).Z →* ℂˣ) (φ : AdelicGL2 (𝓞 ℚ) ℚ → ℂ)
    (hφ : IsCuspAutomorphicFnAt ℚ (productionPinsGeneral ℚ) χ φ) (hcont : Continuous φ)
    (hsmooth : ∃ f : AdelicGL2 (𝓞 ℚ) ℚ → ℂ, IsFactorizableTestFn ℚ f ∧ rightConv ℚ φ f = φ)
    (hne : whittakerCoefficient ℚ (productionPinsGeneral ℚ) psiQ φ 1 ≠ 0)
    (WA : GL (Fin 2) ℝ → ℂ) (Wf : finiteAdelicGL2Subgroup ℚ → ℂ)
    (hWAf : ∀ g : AdelicGL2 (𝓞 ℚ) ℚ,
      whittakerCoefficient ℚ (productionPinsGeneral ℚ) psiQ φ 1 g = WA (ratArchGL2 g) * Wf (RSCarrier.finFactor g)) :
    Continuous Wf ∧ ∃ M r : ℝ, ∀ g : finiteAdelicGL2Subgroup ℚ,
      ‖Wf g‖ ≤ M * ideleNorm ℚ (Matrix.GeneralLinearGroup.det (g : AdelicGL2 (𝓞 ℚ) ℚ)) ^ r := by

  have hcov : CoversModCentre ℚ (⋃ x ∈ classRepTranslates ℚ, (· * x) '' centreCutSiegelSet ℚ (1 / 2) 1 (1 / 2) 2) :=
    AutomorphicForm.SiegelCovering.coversModCentre_productionPinsGeneral_D_rat
  obtain ⟨hWc, M, r, hWgr⟩ :=
    AutomorphicForm.continuous_whittakerCoefficient_and_exists_norm_le_mul_ideleNorm_det_rpow_of_isCuspAutomorphicFnAt_of_rightConv_eq
      ℚ (1 / 2) 1 (1 / 2) 2 (classRepTranslates ℚ) (by norm_num) (by norm_num) (by norm_num) hcov χ φ hφ hcont hsmooth
      psiQ continuous_psiQ norm_psiQ 1
  set W : AdelicGL2 (𝓞 ℚ) ℚ → ℂ := whittakerCoefficient ℚ (productionPinsGeneral ℚ) psiQ φ 1 with hWdef
  have hWc' : Continuous W := hWc
  have hWgr' : ∀ g : AdelicGL2 (𝓞 ℚ) ℚ, ‖W g‖ ≤ M * ideleNorm ℚ (Matrix.GeneralLinearGroup.det g) ^ r := hWgr

  obtain ⟨g₀, hg₀⟩ := Function.ne_iff.1 hne
  have hg₀' : W g₀ ≠ 0 := hg₀
  set a₀ : GL (Fin 2) ℝ := ratArchGL2 g₀ with ha₀
  have hA0 : WA a₀ ≠ 0 := by
    intro h0
    apply hg₀'
    rw [hWAf g₀, ← ha₀, h0, zero_mul]
  set A₀ : AdelicGL2 (𝓞 ℚ) ℚ := archRealGLAt (IsTotallyReal.isReal (default : InfinitePlace ℚ)) a₀ with hA₀

  have hkey : ∀ gf : finiteAdelicGL2Subgroup ℚ, Wf gf = W (A₀ * (gf : AdelicGL2 (𝓞 ℚ) ℚ)) / WA a₀ := by
    intro gf
    have h1 : W (A₀ * (gf : AdelicGL2 (𝓞 ℚ) ℚ)) = WA a₀ * Wf gf := by
      rw [hWAf, ratArchGL2_mul, ratArchGL2_of_mem gf.2, mul_one, hA₀, ratArchGL2_archRealGLAt,
        finFactor_mul_coe, finFactor_archRealGLAt, one_mul]
    rw [h1, mul_div_cancel_left₀ _ hA0]
  have hfun : Wf = fun gf : finiteAdelicGL2Subgroup ℚ => W (A₀ * (gf : AdelicGL2 (𝓞 ℚ) ℚ)) / WA a₀ := funext hkey
  refine ⟨?_, ?_⟩
  · rw [hfun]
    exact (hWc'.comp (continuous_const.mul continuous_subtype_val)).div_const _
  · refine ⟨M * ‖WA a₀‖⁻¹ * ideleNorm ℚ (Matrix.GeneralLinearGroup.det A₀) ^ r, r, fun gf => ?_⟩
    rw [hkey gf, norm_div]
    have h2 := hWgr' (A₀ * (gf : AdelicGL2 (𝓞 ℚ) ℚ))
    rw [map_mul, ideleNorm_mul, Real.mul_rpow (ideleNorm_pos _).le (ideleNorm_pos _).le] at h2
    rw [div_eq_mul_inv]
    calc ‖W (A₀ * (gf : AdelicGL2 (𝓞 ℚ) ℚ))‖ * ‖WA a₀‖⁻¹
        ≤ (M * (ideleNorm ℚ (Matrix.GeneralLinearGroup.det A₀) ^ r *
            ideleNorm ℚ (Matrix.GeneralLinearGroup.det (gf : AdelicGL2 (𝓞 ℚ) ℚ)) ^ r)) * ‖WA a₀‖⁻¹ :=
          mul_le_mul_of_nonneg_right h2 (inv_nonneg.2 (norm_nonneg _))
      _ = M * ‖WA a₀‖⁻¹ * ideleNorm ℚ (Matrix.GeneralLinearGroup.det A₀) ^ r *
            ideleNorm ℚ (Matrix.GeneralLinearGroup.det (gf : AdelicGL2 (𝓞 ℚ) ℚ)) ^ r := by ring

theorem dualFinWhittaker_continuous_and_growth
    (Wf Wfd : finiteAdelicGL2Subgroup ℚ → ℂ) (hWfc : Continuous Wf) (M r : ℝ)
    (hWf : ∀ g : finiteAdelicGL2Subgroup ℚ, ‖Wf g‖ ≤ M * ideleNorm ℚ (Matrix.GeneralLinearGroup.det (g : AdelicGL2 (𝓞 ℚ) ℚ)) ^ r)
    (w₀ : GL (Fin 2) ℚ)
    (hWfd : ∀ gf : finiteAdelicGL2Subgroup ℚ, Wfd gf =
      ((ideleNorm ℚ (Matrix.GeneralLinearGroup.det (gf : AdelicGL2 (𝓞 ℚ) ℚ)) : ℝ) : ℂ) *
        Wf (RSCarrier.finFactor (globalPoints (𝓞 ℚ) ℚ w₀ * transposeInvN (Fin 2) (gf : AdelicGL2 (𝓞 ℚ) ℚ)))) :
    Continuous Wfd ∧ ∃ M' r' : ℝ, ∀ g : finiteAdelicGL2Subgroup ℚ,
      ‖Wfd g‖ ≤ M' * ideleNorm ℚ (Matrix.GeneralLinearGroup.det (g : AdelicGL2 (𝓞 ℚ) ℚ)) ^ r' := by
  set c₀ : finiteAdelicGL2Subgroup ℚ := RSCarrier.finFactor (globalPoints (𝓞 ℚ) ℚ w₀) with hc₀
  have hkey : ∀ gf : finiteAdelicGL2Subgroup ℚ, Wfd gf =
      ((ideleNorm ℚ (Matrix.GeneralLinearGroup.det (gf : AdelicGL2 (𝓞 ℚ) ℚ)) : ℝ) : ℂ) * Wf (c₀ * tInv gf) := by
    intro gf
    rw [hWfd, hc₀, ← finFactor_mul_coe]
    rfl
  have hfun : Wfd = fun gf : finiteAdelicGL2Subgroup ℚ =>
      ((ideleNorm ℚ (Matrix.GeneralLinearGroup.det (gf : AdelicGL2 (𝓞 ℚ) ℚ)) : ℝ) : ℂ) * Wf (c₀ * tInv gf) := funext hkey
  refine ⟨?_, ?_⟩
  · rw [hfun]
    exact (Complex.continuous_ofReal.comp continuous_ideleNorm_det_coe).mul
      (hWfc.comp (continuous_const.mul continuous_tInv))
  · set κ : ℝ := ideleNorm ℚ (Matrix.GeneralLinearGroup.det (c₀ : AdelicGL2 (𝓞 ℚ) ℚ)) with hκ
    refine ⟨M * κ ^ r, 1 - r, fun gf => ?_⟩
    set N : ℝ := ideleNorm ℚ (Matrix.GeneralLinearGroup.det (gf : AdelicGL2 (𝓞 ℚ) ℚ)) with hN
    have hNpos : 0 < N := ideleNorm_pos _
    have hκpos : 0 < κ := ideleNorm_pos _
    have hdet : ideleNorm ℚ (Matrix.GeneralLinearGroup.det ((c₀ * tInv gf : finiteAdelicGL2Subgroup ℚ) : AdelicGL2 (𝓞 ℚ) ℚ)) =
        κ * N⁻¹ := by
      rw [Subgroup.coe_mul, map_mul, ideleNorm_mul]
      show κ * ideleNorm ℚ (Matrix.GeneralLinearGroup.det (transposeInvN (Fin 2) (gf : AdelicGL2 (𝓞 ℚ) ℚ))) = κ * N⁻¹
      rw [det_transposeInvN, ideleNorm_inv]
    rw [hkey gf, norm_mul, Complex.norm_real, Real.norm_of_nonneg hNpos.le]
    have h2 := hWf (c₀ * tInv gf)
    rw [hdet, Real.mul_rpow hκpos.le (inv_nonneg.2 hNpos.le), Real.inv_rpow hNpos.le] at h2
    calc N * ‖Wf (c₀ * tInv gf)‖ ≤ N * (M * (κ ^ r * (N ^ r)⁻¹)) := mul_le_mul_of_nonneg_left h2 hNpos.le
      _ = M * κ ^ r * (N * (N ^ r)⁻¹) := by ring
      _ = M * κ ^ r * N ^ (1 - r) := by
          rw [Real.rpow_sub hNpos, Real.rpow_one, div_eq_mul_inv]

end GL2Side

section Families

variable {K : Type} [Field K] [NumberField K] [Algebra (𝓞 ℚ) (𝓞 K)] [Algebra.IsIntegral (𝓞 ℚ) (𝓞 K)]
variable {pins : CarrierPins ℚ} {ψ : AddChar (AdeleRing (𝓞 ℚ) ℚ) ℂ} {μ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ}

def Lone (F : CubicInductionForm K pins ψ μ) (k : AdelicGL 3 (𝓞 ℚ) ℚ) (v : HeightOneSpectrum (𝓞 ℚ))
    (h : LocalGL3 v) : ℂ :=
  F.whittakerLoc v (h * componentAt3 (𝓞 ℚ) ℚ v k)

def mtwo (hμf : finiteAdelicGL2Subgroup ℚ) (k : AdelicGL 3 (𝓞 ℚ) ℚ) (v : HeightOneSpectrum (𝓞 ℚ)) : LocalGL3 v :=
  iotaGL (localAt ℚ v (hμf : AdelicGL2 (𝓞 ℚ) ℚ)) * componentAt3 (𝓞 ℚ) ℚ v (transposeInv3 k)

def Ltwo (F : CubicInductionForm K pins ψ μ) (hμf : finiteAdelicGL2Subgroup ℚ) (k : AdelicGL 3 (𝓞 ℚ) ℚ)
    (v : HeightOneSpectrum (𝓞 ℚ)) (h : LocalGL3 v) : ℂ :=
  dualWhittakerFn3 (F.whittakerLoc v) (h * mtwo hμf k v)

theorem Lone_apply (F : CubicInductionForm K pins ψ μ) (k : AdelicGL 3 (𝓞 ℚ) ℚ) (v : HeightOneSpectrum (𝓞 ℚ))
    (h : LocalGL3 v) : Lone F k v h = F.whittakerLoc v (h * componentAt3 (𝓞 ℚ) ℚ v k) := rfl

theorem Ltwo_apply (F : CubicInductionForm K pins ψ μ) (hμf : finiteAdelicGL2Subgroup ℚ) (k : AdelicGL 3 (𝓞 ℚ) ℚ)
    (v : HeightOneSpectrum (𝓞 ℚ)) (h : LocalGL3 v) :
    Ltwo F hμf k v h = dualWhittakerFn3 (F.whittakerLoc v) (h * mtwo hμf k v) := rfl

theorem Ltwo_eq_comp (F : CubicInductionForm K pins ψ μ) (hμf : finiteAdelicGL2Subgroup ℚ) (k : AdelicGL 3 (𝓞 ℚ) ℚ)
    (v : HeightOneSpectrum (𝓞 ℚ)) :
    Ltwo F hμf k v = F.whittakerLoc v ∘ fun h => longWeyl3 * transposeInv3 (h * mtwo hμf k v) := rfl

theorem Lone_eq_comp (F : CubicInductionForm K pins ψ μ) (k : AdelicGL 3 (𝓞 ℚ) ℚ) (v : HeightOneSpectrum (𝓞 ℚ)) :
    Lone F k v = F.whittakerLoc v ∘ fun h => h * componentAt3 (𝓞 ℚ) ℚ v k := rfl

end Families

end KcCellIntA59

open KcCellIntA59

set_option linter.unusedVariables false in
open scoped Classical in

theorem solution
    (K : Type) [Field K] [NumberField K]
    [Algebra (𝓞 ℚ) (𝓞 K)] [Algebra.IsIntegral (𝓞 ℚ) (𝓞 K)]
    (_hdeg : Module.finrank ℚ K = 3)
    (Φ : AutomorphicForm.HeckeEigensystem ℚ ℂ)
    (SQ : Finset (HeightOneSpectrum (𝓞 ℚ)))
    (hSQ : (∀ p : HeightOneSpectrum (𝓞 ℚ), Φ.level ≤ p.asIdeal → p ∈ SQ) ∧
      ∀ 𝔓 : HeightOneSpectrum (𝓞 K), 𝔓.under (𝓞 ℚ) ∉ SQ →
        Ideal.ramificationIdx' (𝔓.under (𝓞 ℚ)).asIdeal 𝔓.asIdeal = 1)
    (hb : ∀ p : HeightOneSpectrum (𝓞 ℚ), p ∉ SQ → ‖Φ.b p‖ = 1)
    (ha : ∀ σ : ℝ, 1 < σ →
      Summable fun p : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ℚ) =>
        ‖Φ.a p‖ * (Ideal.absNorm p.asIdeal : ℝ) ^ (-σ))
    (SK : Finset (HeightOneSpectrum (𝓞 K)))
    (hSK : ∀ 𝔓 : HeightOneSpectrum (𝓞 K), 𝔓 ∈ SK ↔ 𝔓.under (𝓞 ℚ) ∈ SQ)
    (S : Finset (HeightOneSpectrum (𝓞 ℚ))) (hS : S ⊆ SQ)
    (R : SmoothCuspRealizationAt ℚ (productionPinsGeneral ℚ) Φ.toRawCentral) (hRc : Continuous R.toFun)
    (Cfin : FiniteAdeleRing (𝓞 ℚ) ℚ → AdelicGL2 (𝓞 ℚ) ℚ → ℂ) (hRS : R.exceptionalSet ⊆ S)
    (φv : (InfinitePlace ℚ → ZMod 2) → AdelicGL2 (𝓞 ℚ) ℚ → ℂ)
    (hiso : ∀ par, IsIsotypicCuspFormAt ℚ (productionPinsGeneral ℚ) R.centralChar Φ.level S Φ (φv par))
    (hφne : ∀ par, φv par ≠ 0)
    (hφKf : ∀ par, ∃ α : AdelicGL2 (𝓞 ℚ) ℚ → ℂ, IsFactorizableTestFn ℚ α ∧ rightConv ℚ (φv par) α = φv par)
    (μ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ) (hμ : IsAdmissibleTwist K μ)

    (ψ : AddChar (AdeleRing (𝓞 ℚ) ℚ) ℂ) (hψ : IsGlobalAddChar ℚ ψ)
    (hlev : ∀ v : HeightOneSpectrum (𝓞 ℚ), LanglandsTunnell.TateLocal.addCharLevel (psiLoc ψ v) = 0)
    (hψQ : ψ⁻¹ = NumberField.StandardAddChar.psiQ)

    (F : CubicInductionForm K (productionPinsOf ℚ (classRepSiegelSet ℚ (1 / 2) 1 (1 / 2) 2) (fun N => levelOne (𝓞 ℚ) ℚ N ⊓ finiteAdelicGL2Subgroup ℚ) (fun v => heckeGen (𝓞 ℚ) ℚ v) (adelicBox ℚ)) ψ μ)
    (hF0 : F.form ≠ 0 ∧ ∀ v, ¬ IsRamifiedIn K v →
      LanglandsTunnell.TateLocal.addCharLevel (psiLoc ψ v) = 0 →
        F.whittakerLoc v 1 = 1 ∧ HasSphericalTorusValuesAt (inducedCoeff K μ) v (F.whittakerLoc v))
    (hFc : Continuous F.form) (hFw : Continuous F.whittaker) (hFdw : Continuous F.dualWhittaker)
    (hFg : IsGaugeMajorised3 ℚ F.whittaker) (hFdg : IsGaugeMajorised3 ℚ F.dualWhittaker)
    (hBad :
        ∀ T : Finset (HeightOneSpectrum (𝓞 ℚ)),
          (∀ v ∈ T, IsBadPlace K μ v → ∃ Uv : Subgroup (LocalGL3 v), IsOpen (Uv : Set (LocalGL3 v)) ∧
            ∀ k ∈ Uv, ∀ g : LocalGL3 v, F.whittakerLoc v (g * k) = F.whittakerLoc v g) ∧
          (∀ v ∈ T, IsBadPlace K μ v → ∀ W ∈ gl3CyclicSubspace (F.whittakerLoc v), W ≠ 0 →
            F.whittakerLoc v ∈ gl3CyclicSubspace W))

    (S' : Finset (HeightOneSpectrum (𝓞 ℚ))) (hSS' : SQ ⊆ S')
    (hgood : ∀ p : HeightOneSpectrum (𝓞 ℚ), p ∉ S' → ¬ IsBadPlace K μ p)
    (ϖ : ∀ p : HeightOneSpectrum (𝓞 ℚ), p.adicCompletionIntegers ℚ)
    (hπ : ∀ p : HeightOneSpectrum (𝓞 ℚ), p ∉ SQ →
      algebraMap (p.adicCompletionIntegers ℚ) (p.adicCompletion ℚ) (ϖ p) ≠ 0)
    (hϖ : ∀ p : HeightOneSpectrum (𝓞 ℚ), p ∉ SQ →
      Valued.v (algebraMap (p.adicCompletionIntegers ℚ) (p.adicCompletion ℚ) (ϖ p)) = WithZero.exp (-1 : ℤ))
    (hμf : finiteAdelicGL2Subgroup ℚ)
    (hhμf : (hμf : AdelicGL2 (𝓞 ℚ) ℚ) =
      ((S' \ SQ).toList.map (fun p => if hp : p ∉ SQ then
          UnramifiedWhittaker.placeEmbed ℚ p
            ((UnramifiedWhittaker.scalarPi (algebraMap (p.adicCompletionIntegers ℚ) (p.adicCompletion ℚ) (ϖ p))
              (hπ p hp)) ^ (-(inducedLevelAt K μ p : ℤ)))
        else 1)).prod)

    (WA : (InfinitePlace ℚ → ZMod 2) → GL (Fin 2) ℝ → ℂ)
    (Wf : (InfinitePlace ℚ → ZMod 2) → finiteAdelicGL2Subgroup ℚ → ℂ)
    (hWAf : ∀ par (g : AdelicGL2 (𝓞 ℚ) ℚ),
      whittakerCoefficient ℚ (productionPinsOf ℚ (classRepSiegelSet ℚ (1 / 2) 1 (1 / 2) 2) (fun N => levelOne (𝓞 ℚ) ℚ N ⊓ finiteAdelicGL2Subgroup ℚ) (fun v => heckeGen (𝓞 ℚ) ℚ v) (adelicBox ℚ)) NumberField.StandardAddChar.psiQ (φv par) 1 g = WA par (ratArchGL2 g) * Wf par (RSCarrier.finFactor g))
    (hWfC : ∀ par (g : finiteAdelicGL2Subgroup ℚ), Wf par g = Cfin 1 (g : AdelicGL2 (𝓞 ℚ) ℚ))

    (hWf1 : ∀ par, Wf par 1 ≠ 0)

    (w₀ : GL (Fin 2) ℚ) (hw₀ : (w₀ : Matrix (Fin 2) (Fin 2) ℚ) = !![0, 1; 1, 0])
    (Wfd : (InfinitePlace ℚ → ZMod 2) → finiteAdelicGL2Subgroup ℚ → ℂ)
    (hWfd : ∀ par (gf : finiteAdelicGL2Subgroup ℚ), Wfd par gf =
      ((NumberField.TateGlobal.ideleNorm ℚ (Matrix.GeneralLinearGroup.det (gf : AdelicGL2 (𝓞 ℚ) ℚ)) : ℝ) : ℂ) *
        Wf par (RSCarrier.finFactor (globalPoints (𝓞 ℚ) ℚ w₀ * transposeInvN (Fin 2) (gf : AdelicGL2 (𝓞 ℚ) ℚ))))

    [SecondCountableTopology (AdelicGL2 (𝓞 ℚ) ℚ)]
    (μf : MeasureTheory.Measure (finiteAdelicGL2Subgroup ℚ)) [μf.IsHaarMeasure]
    (μNFin : MeasureTheory.Measure RSCarrier.finUnipotent) [μNFin.IsHaarMeasure]

    (k : AdelicGL 3 (𝓞 ℚ) ℚ) (_hk : archComponent3 (𝓞 ℚ) ℚ k = 1 ∧
      ∀ v : HeightOneSpectrum (𝓞 ℚ), v ∉ SQ → componentAt3 (𝓞 ℚ) ℚ v k = 1)
    (par : InfinitePlace ℚ → ZMod 2) :
    ∃ σ : ℝ, ∀ s' : ℂ, σ < s'.re →
      Integrable (fun g : finiteAdelicGL2Subgroup ℚ =>
          {g : finiteAdelicGL2Subgroup ℚ | ∀ p : HeightOneSpectrum (𝓞 ℚ), p ∉ SQ →
              ∃ n ∈ (AutomorphicForm.unipotentGL2Hom (R := p.adicCompletion ℚ)).range,
                ∃ k ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ p ⊤,
                  localAt ℚ p (g : AdelicGL2 (𝓞 ℚ) ℚ) = n * k}.indicator (fun g => Wf par (RSCarrier.finFactor (g : AdelicGL2 (𝓞 ℚ) ℚ))) g *
            {g : finiteAdelicGL2Subgroup ℚ | ∀ p : HeightOneSpectrum (𝓞 ℚ), p ∉ SQ →
              ∃ n ∈ (AutomorphicForm.unipotentGL2Hom (R := p.adicCompletion ℚ)).range,
                ∃ k ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ p ⊤,
                  localAt ℚ p (g : AdelicGL2 (𝓞 ℚ) ℚ) = n * k}.indicator (fun g => ∏ᶠ v, F.whittakerLoc v
              (componentAt3 (𝓞 ℚ) ℚ v
                (iota (𝓞 ℚ) ℚ ((RSCarrier.finFactor (g : AdelicGL2 (𝓞 ℚ) ℚ) : finiteAdelicGL2Subgroup ℚ) :
                  AdelicGL2 (𝓞 ℚ) ℚ) * k))) g *
            ((ideleNorm ℚ (Matrix.GeneralLinearGroup.det (g : AdelicGL2 (𝓞 ℚ) ℚ)) : ℝ) : ℂ) ^ (s' - 1 / 2))
        (μf.withDensity (HaarQuotient.density RSCarrier.finUnipotent μNFin)) ∧
      Integrable (fun g : finiteAdelicGL2Subgroup ℚ =>
          {g : finiteAdelicGL2Subgroup ℚ | ∀ p : HeightOneSpectrum (𝓞 ℚ), p ∉ SQ →
              ∃ n ∈ (AutomorphicForm.unipotentGL2Hom (R := p.adicCompletion ℚ)).range,
                ∃ k ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ p ⊤,
                  localAt ℚ p (g : AdelicGL2 (𝓞 ℚ) ℚ) = n * k}.indicator (fun g => Wfd par (RSCarrier.finFactor (g : AdelicGL2 (𝓞 ℚ) ℚ) * hμf)) g *
            {g : finiteAdelicGL2Subgroup ℚ | ∀ p : HeightOneSpectrum (𝓞 ℚ), p ∉ SQ →
              ∃ n ∈ (AutomorphicForm.unipotentGL2Hom (R := p.adicCompletion ℚ)).range,
                ∃ k ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ p ⊤,
                  localAt ℚ p (g : AdelicGL2 (𝓞 ℚ) ℚ) = n * k}.indicator (fun g => ∏ᶠ v, dualWhittakerFn3 (F.whittakerLoc v)
              (componentAt3 (𝓞 ℚ) ℚ v
                (iota (𝓞 ℚ) ℚ ((RSCarrier.finFactor (g : AdelicGL2 (𝓞 ℚ) ℚ) * hμf : finiteAdelicGL2Subgroup ℚ) :
                  AdelicGL2 (𝓞 ℚ) ℚ) * transposeInv3 k))) g *
            ((ideleNorm ℚ (Matrix.GeneralLinearGroup.det (g : AdelicGL2 (𝓞 ℚ) ℚ)) : ℝ) : ℂ) ^ (s' - 1 / 2))
        (μf.withDensity (HaarQuotient.density RSCarrier.finUnipotent μNFin)) := by

  have hne : whittakerCoefficient ℚ (productionPinsGeneral ℚ) psiQ (φv par) 1 ≠ 0 :=
    AutomorphicForm.whittakerCoefficient_one_ne_zero_of_isIsotypicCuspFormAt_of_ne_zero
      (classRepSiegelSet ℚ (1 / 2) 1 (1 / 2) 2) R.centralChar Φ.level S Φ (φv par) (hiso par) (hφne par)
  obtain ⟨hWfc, M₁, r₁, hWfgr⟩ := finWhittaker_continuous_and_growth R.centralChar (φv par)
    (hiso par).smoothCusp.1 (hiso par).continuous (hφKf par) hne (WA par) (Wf par) (hWAf par)
  obtain ⟨hWfdc, M₂, r₂, hWfdgr⟩ :=
    dualFinWhittaker_continuous_and_growth (Wf par) (Wfd par) hWfc M₁ r₁ hWfgr w₀ (hWfd par)

  have hB₁eq : (fun g : finiteAdelicGL2Subgroup ℚ => Wf par (RSCarrier.finFactor (g : AdelicGL2 (𝓞 ℚ) ℚ))) = Wf par :=
    funext fun g => by rw [finFactor_coe]
  have hB₁m : Measurable fun g : finiteAdelicGL2Subgroup ℚ => Wf par (RSCarrier.finFactor (g : AdelicGL2 (𝓞 ℚ) ℚ)) := by
    rw [hB₁eq]; exact hWfc.measurable
  have hB₁gr : ∃ M r : ℝ, ∀ g : finiteAdelicGL2Subgroup ℚ,
      ‖Wf par (RSCarrier.finFactor (g : AdelicGL2 (𝓞 ℚ) ℚ))‖ ≤
        M * ideleNorm ℚ (Matrix.GeneralLinearGroup.det (g : AdelicGL2 (𝓞 ℚ) ℚ)) ^ r :=
    ⟨M₁, r₁, fun g => by rw [finFactor_coe]; exact hWfgr g⟩
  have hB₂eq : (fun g : finiteAdelicGL2Subgroup ℚ => Wfd par (RSCarrier.finFactor (g : AdelicGL2 (𝓞 ℚ) ℚ) * hμf)) =
      fun g => Wfd par (g * hμf) :=
    funext fun g => by rw [finFactor_coe]
  have hB₂m : Measurable fun g : finiteAdelicGL2Subgroup ℚ => Wfd par (RSCarrier.finFactor (g : AdelicGL2 (𝓞 ℚ) ℚ) * hμf) := by
    rw [hB₂eq]; exact (hWfdc.comp (continuous_id.mul continuous_const)).measurable
  have hB₂gr : ∃ M r : ℝ, ∀ g : finiteAdelicGL2Subgroup ℚ,
      ‖Wfd par (RSCarrier.finFactor (g : AdelicGL2 (𝓞 ℚ) ℚ) * hμf)‖ ≤
        M * ideleNorm ℚ (Matrix.GeneralLinearGroup.det (g : AdelicGL2 (𝓞 ℚ) ℚ)) ^ r := by
    refine ⟨M₂ * ideleNorm ℚ (Matrix.GeneralLinearGroup.det (hμf : AdelicGL2 (𝓞 ℚ) ℚ)) ^ r₂, r₂, fun g => ?_⟩
    rw [finFactor_coe]
    refine (hWfdgr (g * hμf)).trans (le_of_eq ?_)
    rw [Subgroup.coe_mul, map_mul, ideleNorm_mul, Real.mul_rpow (ideleNorm_pos _).le (ideleNorm_pos _).le]
    ring

  have hgauge := fun v =>
    LanglandsTunnell.CubicInduction.exists_gauge_whittakerLoc_of_isGaugeMajorised3_of_form_ne_zero K _ ψ μ F hF0.1 hFg
      S' hgood v
  have hlc : ∀ v : HeightOneSpectrum (𝓞 ℚ), IsLocallyConstant (F.whittakerLoc v) :=
    fun v => isLocallyConstant_whittakerLoc F hBad v
  have hF01 : ∀ v, ¬ IsRamifiedIn K v → addCharLevel (psiLoc ψ v) = 0 → F.whittakerLoc v 1 = 1 :=
    fun v h1 h2 => (hF0.2 v h1 h2).1
  have hμ1 : ∀ v : HeightOneSpectrum (𝓞 ℚ), v ∉ S' → localAt ℚ v (hμf : AdelicGL2 (𝓞 ℚ) ℚ) = 1 := by
    intro v hv
    rw [hhμf]
    refine localAt_listProd_eq_one _ _ _ fun q hq => ?_
    have hqS : q ∈ S' := (Finset.mem_sdiff.1 (Finset.mem_toList.1 hq)).1
    have hvq : v ≠ q := fun h => hv (h ▸ hqS)
    by_cases hq' : q ∉ SQ
    · rw [dif_pos hq']
      exact localAt_placeEmbed_of_ne q hvq _
    · rw [dif_neg hq', map_one]

  have h1lc : ∀ v : HeightOneSpectrum (𝓞 ℚ), IsLocallyConstant (Lone F k v) := fun v => by
    rw [Lone_eq_comp]; exact (hlc v).comp_continuous (continuous_id.mul continuous_const)
  have h1ph : ∀ (v : HeightOneSpectrum (𝓞 ℚ)) (x : v.adicCompletion ℚ) (h : LocalGL3 v),
      ‖Lone F k v (iotaGL (unipotentGL2 x) * h)‖ = ‖Lone F k v h‖ := fun v x h => by
    rw [Lone_apply, Lone_apply, mul_assoc]
    exact norm_apply_iotaGL_unipotentGL2_mul hψQ (F.whittakerLoc_law v) x _
  have h1one : ∀ v : HeightOneSpectrum (𝓞 ℚ), v ∉ S' →
      ∀ κ ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ v ⊤, Lone F k v (iotaGL κ) = 1 := by
    intro v hv κ hκ
    have hvSQ : v ∉ SQ := fun h => hv (hSS' h)
    rw [Lone_apply, _hk.2 v hvSQ, mul_one]
    exact whittakerLoc_iotaGL_eq_one_of_good F hF01 hlev (hgood v hv) ((mem_localLevelOne_top_iff v κ).1 hκ)
  have h1gauge : ∀ v ∈ S', ∃ (B : ℝ) (t : ℕ) (C : ℝ), ∀ h : LocalGL3 v,
      (¬ (detSize h * lastRowSup h / minorSup h ^ 2 ≤ B ∧ minorSup h / lastRowSup h ^ 2 ≤ B) → Lone F k v h = 0) ∧
      (detSize h * lastRowSup h / minorSup h ^ 2 ≤ B ∧ minorSup h / lastRowSup h ^ 2 ≤ B →
        ‖Lone F k v h‖ ≤ C / ((detSize h * lastRowSup h / minorSup h ^ 2) * (minorSup h / lastRowSup h ^ 2)) ^ t) := by
    intro v _
    obtain ⟨B, t, C, hW⟩ := hgauge v
    exact (LanglandsTunnell.CubicInduction.forall_mem_gl3CyclicSubspace_exists_gauge_and_exists_gauge_dualWhittakerFn3
      (F.whittakerLoc v) ⟨B, t, C, hW⟩ _ (translate_mem_gl3CyclicSubspace (F.whittakerLoc v) (componentAt3 (𝓞 ℚ) ℚ v k))).1

  have h2lc : ∀ v : HeightOneSpectrum (𝓞 ℚ), IsLocallyConstant (Ltwo F hμf k v) := fun v => by
    rw [Ltwo_eq_comp]
    exact (hlc v).comp_continuous
      (continuous_const.mul ((continuous_transposeInv3_local v).comp (continuous_id.mul continuous_const)))
  have h2ph : ∀ (v : HeightOneSpectrum (𝓞 ℚ)) (x : v.adicCompletion ℚ) (h : LocalGL3 v),
      ‖Ltwo F hμf k v (iotaGL (unipotentGL2 x) * h)‖ = ‖Ltwo F hμf k v h‖ := fun v x h => by
    rw [Ltwo_apply, Ltwo_apply, mul_assoc]
    exact norm_dualWhittakerFn3_iotaGL_unipotentGL2_mul hψQ (F.whittakerLoc_law v) x _
  have h2one : ∀ v : HeightOneSpectrum (𝓞 ℚ), v ∉ S' →
      ∀ κ ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ v ⊤, Ltwo F hμf k v (iotaGL κ) = 1 := by
    intro v hv κ hκ
    have hvSQ : v ∉ SQ := fun h => hv (hSS' h)
    have hm : mtwo hμf k v = 1 := by
      show iotaGL (localAt ℚ v (hμf : AdelicGL2 (𝓞 ℚ) ℚ)) * componentAt3 (𝓞 ℚ) ℚ v (transposeInv3 k) = 1
      rw [hμ1 v hv, map_one, one_mul, componentAt3_transposeInv3, _hk.2 v hvSQ, transposeInv3_one]
    rw [Ltwo_apply, hm, mul_one]
    exact dualWhittakerFn3_iotaGL_eq_one_of_good F hF01 hlev (hgood v hv) ((mem_localLevelOne_top_iff v κ).1 hκ)
  have h2gauge : ∀ v ∈ S', ∃ (B : ℝ) (t : ℕ) (C : ℝ), ∀ h : LocalGL3 v,
      (¬ (detSize h * lastRowSup h / minorSup h ^ 2 ≤ B ∧ minorSup h / lastRowSup h ^ 2 ≤ B) → Ltwo F hμf k v h = 0) ∧
      (detSize h * lastRowSup h / minorSup h ^ 2 ≤ B ∧ minorSup h / lastRowSup h ^ 2 ≤ B →
        ‖Ltwo F hμf k v h‖ ≤ C / ((detSize h * lastRowSup h / minorSup h ^ 2) * (minorSup h / lastRowSup h ^ 2)) ^ t) := by
    intro v _
    obtain ⟨B, t, C, hW⟩ := hgauge v
    obtain ⟨B', t', C', hg⟩ :=
      (LanglandsTunnell.CubicInduction.forall_mem_gl3CyclicSubspace_exists_gauge_and_exists_gauge_dualWhittakerFn3
        (F.whittakerLoc v) ⟨B, t, C, hW⟩ _
        (translate_mem_gl3CyclicSubspace (F.whittakerLoc v) (transposeInv3 (mtwo hμf k v)))).2
    refine ⟨B', t', C', fun h => ?_⟩
    rw [Ltwo_apply, dualWhittakerFn3_mul_eq]
    exact hg h

  obtain ⟨σ₁, hI₁⟩ :=
    LanglandsTunnell.RankinSelberg.exists_forall_integrable_bigCell_indicator_mul_finprod_iotaGL_of_gauge SQ S' hSS'
      (Lone F k) h1lc h1ph h1one h1gauge
      (fun g : finiteAdelicGL2Subgroup ℚ => Wf par (RSCarrier.finFactor (g : AdelicGL2 (𝓞 ℚ) ℚ))) hB₁m hB₁gr μf μNFin
  obtain ⟨σ₂, hI₂⟩ :=
    LanglandsTunnell.RankinSelberg.exists_forall_integrable_bigCell_indicator_mul_finprod_iotaGL_of_gauge SQ S' hSS'
      (Ltwo F hμf k) h2lc h2ph h2one h2gauge
      (fun g : finiteAdelicGL2Subgroup ℚ => Wfd par (RSCarrier.finFactor (g : AdelicGL2 (𝓞 ℚ) ℚ) * hμf)) hB₂m hB₂gr
      μf μNFin

  have hprod₁ : (fun g : finiteAdelicGL2Subgroup ℚ => ∏ᶠ v : HeightOneSpectrum (𝓞 ℚ),
      Lone F k v (iotaGL (localAt ℚ v (g : AdelicGL2 (𝓞 ℚ) ℚ)))) =
      fun g : finiteAdelicGL2Subgroup ℚ => ∏ᶠ v, F.whittakerLoc v (componentAt3 (𝓞 ℚ) ℚ v
        (iota (𝓞 ℚ) ℚ ((RSCarrier.finFactor (g : AdelicGL2 (𝓞 ℚ) ℚ) : finiteAdelicGL2Subgroup ℚ) :
          AdelicGL2 (𝓞 ℚ) ℚ) * k)) := by
    funext g
    refine finprod_congr fun v => ?_
    rw [Lone_apply, map_mul, finFactor_coe, componentAt3_iota]
  have hprod₂ : (fun g : finiteAdelicGL2Subgroup ℚ => ∏ᶠ v : HeightOneSpectrum (𝓞 ℚ),
      Ltwo F hμf k v (iotaGL (localAt ℚ v (g : AdelicGL2 (𝓞 ℚ) ℚ)))) =
      fun g : finiteAdelicGL2Subgroup ℚ => ∏ᶠ v, dualWhittakerFn3 (F.whittakerLoc v) (componentAt3 (𝓞 ℚ) ℚ v
        (iota (𝓞 ℚ) ℚ ((RSCarrier.finFactor (g : AdelicGL2 (𝓞 ℚ) ℚ) * hμf : finiteAdelicGL2Subgroup ℚ) :
          AdelicGL2 (𝓞 ℚ) ℚ) * transposeInv3 k)) := by
    funext g
    refine finprod_congr fun v => ?_
    rw [Ltwo_apply, map_mul, finFactor_coe, componentAt3_iota, Subgroup.coe_mul, map_mul, map_mul]
    show dualWhittakerFn3 (F.whittakerLoc v) (iotaGL (localAt ℚ v (g : AdelicGL2 (𝓞 ℚ) ℚ)) *
        (iotaGL (localAt ℚ v (hμf : AdelicGL2 (𝓞 ℚ) ℚ)) * componentAt3 (𝓞 ℚ) ℚ v (transposeInv3 k))) = _
    rw [mul_assoc]
  refine ⟨max σ₁ σ₂, fun s' hs' => ⟨?_, ?_⟩⟩
  · have hint := hI₁ s' ((le_max_left _ _).trans_lt hs')
    rw [hprod₁] at hint
    exact hint
  · have hint := hI₂ s' ((le_max_right _ _).trans_lt hs')
    rw [hprod₂] at hint
    exact hint

end
end S_LanglandsTunnell_RankinSelberg_exists_forall_integrable_rsFinCellIntegrand_translate_and_dual
end P2MW
export P2MW.S_LanglandsTunnell_RankinSelberg_exists_forall_integrable_rsFinCellIntegrand_translate_and_dual (solution)
