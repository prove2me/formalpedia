-- Prove2me | solution 1 for LanglandsTunnell.exists_isAdmissibleTwist_eq_twist_formalBaseChange_b_isArchCompAt_archOfParam_of_whittakerCoefficient_fibre_eq_archW
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.670037+00:00
-- url     : https://prove2.me/submissions/9f725c2e-d954-5541-b8b1-2fd775a55334

import Definitions.Def_AutomorphicForm_TranslateSpanOccurrence
import Definitions.Def_AutomorphicForm_FormalBaseChange
import Definitions.Def_LanglandsTunnell_JLConverse
import Definitions.Def_LanglandsTunnell_ArchBaseChange
import Definitions.Def_NumberField_AdelicTraceFin
import Theorems.Thm_LanglandsTunnell_Converse_ArchDatumR_exists_twist_W_eq_abs_det_rpow_mul
import Theorems.Thm_LanglandsTunnell_archOccursInClassOf_whittakerCoefficient_fibre_eq_archW_twist_of_archOccursInClassOf_rat
import Theorems.Thm_AutomorphicForm_exists_smoothCuspRealizationAt_productionPinsGeneral_toFun_eq_of_coversModCentre
import Theorems.Thm_LanglandsTunnell_Converse_exists_isAdmissibleTwist_eq_formalBaseChange_b_isArchCompAt_archOfParam
import Theorems.Thm_LanglandsTunnell_exists_finset_norm_b_eq_absNorm_of_whittakerCoefficient_fibre_eq_archW_of_re_centralExponent_eq_zero
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

p2m_attr_erase "ext" "IsDedekindDomain.HeightOneSpectrum.adicCompletion.ext"
p2m_attr_erase "ext" "NumberField.InfinitePlace.Completion.ext"
namespace P2MW.S_LanglandsTunnell_exists_isAdmissibleTwist_eq_twist_formalBaseChange_b_isArchCompAt_archOfParam_of_whittakerCoefficient_fibre_eq_archW
p2m_attr_erase "instance" "Deep.NTSupply.instNormalRayClassSubgroup LanglandsTunnell.isScalarTower_fixFldDetKer_fixFldQuatH_L LanglandsTunnell.isScalarTower_rat_fixFldSylowH_fixFldQuatH LanglandsTunnell.detKer_normal LanglandsTunnell.isScalarTower_rat_fixFldDetKer_fixFldQuatH LanglandsTunnell.algebra_fixFldDetKer_fixFldQuatH LanglandsTunnell.isScalarTower_fixFldSylowH_fixFldQuatH_L LanglandsTunnell.algebra_fixFldSylowH_fixFldQuatH LanglandsTunnell.Lift48.instDecidablePredMatIsProjOrder LanglandsTunnell.Lift48.instDecidablePredMatIsPM1 instCountableOfNumberField_definitions instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions FLT.InfiniteAdeleBaseChange.uniqueSelfExtension NumberField.InfinitePlace.RamifiedExtension.instCoeExtension NumberField.InfinitePlace.UnramifiedExtension.instCoeExtension IsDedekindDomain.HeightOneSpectrum.Extension.instAlgebraSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnder IsDedekindDomain.HeightOneSpectrum.Extension.instAlgebraSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnder_1 IsDedekindDomain.HeightOneSpectrum.instMulActionHomClassAlgHomTensorProductAdicCompletionForallValEqUnder_definitions IsDedekindDomain.HeightOneSpectrum.Extension.instAlgebraAdicCompletionValEqUnder IsDedekindDomain.HeightOneSpectrum.adicCompletion.instFiniteForallValEqUnderOfFiniteDimensional_definitions IsDedekindDomain.HeightOneSpectrum.instIsBiscalarSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersTensorProductCoeAlgHomTensorAdicCompletionIntegersTo IsDedekindDomain.HeightOneSpectrum.Extension.instContinuousSMulAdicCompletionValEqUnder IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsModuleTopology IsDedekindDomain.HeightOneSpectrum.Extension.instFiniteSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnderOfFiniteDimensional IsDedekindDomain.HeightOneSpectrum.adicCompletion.instFiniteValEqUnderOfFiniteDimensional_definitions instIsBiscalarTensorProductCoeAlgHomBaseChange_of_algebraMap IsDedekindDomain.HeightOneSpectrum.instIsScalarTowerSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnder_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsModuleTopologyPi Submodule.instIsTopologicalModuleSubtypeMem"
p2m_attr_erase "instance" "Pi.instTopologicalModule IsTopologicalModule.toContinuousSMul IsTopologicalModule.toContinuousAdd instFunLike SemialgHomClass.toSemilinearMapClass instCoeTCSemialgHom SemialgHomClass.toRingHomClass SemialgHomClass.instSemialgHom IsDirectLimit.Module.instDirectLimitCoeLinearMapIdOfOfNonempty RestrictedProduct.instIsDirectLimit' RestrictedProduct.instIsDirectLimit RestrictedProduct.instNonemptyOrderDualElemSetSets_definitions RestrictedProduct.instDirectedSystem RestrictedProduct.instDirectedSystemCoeSubmoduleCoeLinearMapIdInclusionLinearMap RestrictedProduct.directed RestrictedProduct.instDirectedSystemOrderDualElemSetSetsCoeSubmodulePrincipalValMemCoeLinearMapIdInclusionLinearMap M4aHerbrand.Bridge.sigmaCompactSpace_finiteAdeleRing M4aHerbrand.Bridge.sigmaCompactSpace_adeleRing M4aHerbrand.Bridge.sigmaCompactSpace_infiniteAdeleRing M4aHerbrand.Bridge.sigmaCompactSpace_completion M4aHerbrand.Bridge.instT2SpaceAdeleRing instHenselianLocalRingOfCompactSpaceOfIsNoetherianRing NumberField.instHenselianLocalRingAdicCompletionIntegers instIsAdicCompleteMaximalIdealOfCompactSpace NumberField.instIsAdicCompleteMaximalIdealAdicCompletionIntegers"
p2m_attr_erase "simp" "LanglandsTunnell.RankinSelberg.mem_primeFibre AutomorphicForm.fnTwist_zero AutomorphicForm.fnTwist_apply AutomorphicForm.CuspidalSpectrum.fdPins_μ AutomorphicForm.CuspidalSpectrum.fdPins_nS AutomorphicForm.CuspidalSpectrum.fdPins_ν AutomorphicForm.CuspidalSpectrum.fdPins_gen AutomorphicForm.CuspidalSpectrum.fdPins_U AutomorphicForm.CuspidalSpectrum.fdPins_D AutomorphicForm.CuspidalSpectrum.fdPins_Z AutomorphicForm.CuspidalSpectrum.mem_detNormSlab AutomorphicForm.CuspidalSpectrum.fdPins_eq AutomorphicForm.CuspidalSpectrum.fdPins_mS AutomorphicForm.CuspidalConstituent.rightRegular_apply AutomorphicForm.IsStableLinearOn.coe_toEnd_apply AutomorphicForm.ArchRepAt.mk.sizeOf_spec AutomorphicForm.IsIsotypicCuspFormAt.toRealization_toFun AutomorphicForm.ArchTypeFamily.mk.sizeOf_spec AutomorphicForm.charRep_apply AutomorphicForm.ArchRepAt.mk.injEq AutomorphicForm.ArchTypeFamily.mk.injEq M4aHerbrand.IdeleGaloisDescent.mk.sizeOf_spec M4aHerbrand.IdeleGaloisDescent.mk.injEq NumberField.AdeleRing.val_finiteUnitsComponent IsDedekindDomain.FiniteAdeleRing.val_unitsComponent NumberField.AdeleRing.val_finitePartUnits NumberField.AdeleRing.val_infiniteUnitsComponent FLT.InfiniteAdeleBaseChange.evalAlgHom_apply FLT.InfiniteAdeleBaseChange.BaseChangeData.mk.sizeOf_spec FLT.InfiniteAdeleBaseChange.tensorPiAlgHom_tmul_apply FLT.InfiniteAdeleBaseChange.collapsePlaces_apply FLT.InfiniteAdeleBaseChange.tensorPiAlgEquiv_tmul_apply FLT.InfiniteAdeleBaseChange.InfinitePlaceData.mk.sizeOf_spec FLT.InfiniteAdeleBaseChange.InfinitePlaceData.mk.injEq FLT.InfiniteAdeleBaseChange.BaseChangeData.mk.injEq M4aHerbrand.ArchSemilocal.psiFactor_tmul M4aHerbrand.ArchSemilocal.psi_apply M4aHerbrand.AdeleBaseChange.mk.sizeOf_spec M4aHerbrand.AdeleBaseChange.mk.injEq M4aHerbrand.Bridge.prodTensorAlgEquiv_tmul"
p2m_attr_erase "simp" "M4aHerbrand.Bridge.genuineβ_fst M4aHerbrand.Bridge.genuineβ_snd M4aHerbrand.Bridge.finiteConorm_apply SemialgHom.baseChange_of_algebraMap_tmul_left SemialgHom.baseChangeRightOfAlgebraMap_apply Pi.semialgHomPi_apply Pi.semialgHom_apply Module.Basis.rightBaseChange_apply LinearEquiv.coe_mulLeft LinearEquiv.coe_mulRight WithVal.semialgebraMap_toFun_ofVal Module.Basis.rightBaseChange_repr IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers.tensorCoe_tmul IsDedekindDomain.HeightOneSpectrum.tensorAdicCompletionIntegersTo_tmul SemialgHom.baseChangeRightOfAlgebraMap_coe IsDedekindDomain.HeightOneSpectrum.adicCompletion.integerBaseChangeLinearEquiv_tmul_apply SemialgHom.baseChange_of_algebraMap_tmul_right IsLocalization.map_moduleTensorEquiv_symm_tmul IsLocalization.leftModuleTensorEquiv_apply IsLocalization.moduleLid_symm_apply IsLocalization.leftModuleTensorEquiv_symm_apply IsLocalization.map_moduleTensorEquiv_tmul IsModuleTopology.continuousLinearEquiv_apply AlgEquiv.extendScalars_symm_apply IsModuleTopology.Module.Basis.equivFun_homeo_symm_apply IsModuleTopology.Module.Basis.equivFun_homeo_apply IsModuleTopology.continuousAlgEquivOfIsBiscalar_apply AlgEquiv.extendScalars_apply IsModuleTopology.continuousLinearEquiv_symm_apply SemialgHom.restrictScalars_toFun SemialgHom.mk.sizeOf_spec SemialgHom.mk.injEq SemialgHom.coe_coe coe_mk TensorProduct.RightActions.smul_def TensorProduct.RightActions.Module.TensorProduct.comm_symm_apply_tmul TensorProduct.RightActions.LinearMap.baseChange_id TensorProduct.RightActions.algebraMap_eval TensorProduct.RightActions.Module.TensorProduct.comm_apply_tmul TensorProduct.RightActions.Algebra.TensorProduct.comm_symm_apply_tmul"
p2m_attr_erase "simp" "TensorProduct.RightActions.Algebra.TensorProduct.comm_apply_tmul M4aHerbrand.Bridge.tensorAdeleRingEquiv_apply M4aHerbrand.Bridge.flattenPlaces_apply M4aHerbrand.Bridge.congrPlaces_apply M4aHerbrand.Bridge.integralTensorRingEquiv_tmul M4aHerbrand.Bridge.moduleStructureBridge_apply RestrictedProduct.lTensorEquivLeft_tmul RestrictedProduct.lTensorEquiv_tmul RestrictedProduct.lTensorLeft_tmul RestrictedProduct.lTensor_tmul IsDirectLimit.Module.linearEquiv_symm_apply IsDirectLimit.linearEquiv_symm_apply IsDirectLimit.lift_of IsDirectLimit.Module.linearEquiv_apply IsDirectLimit.Module.lift_of IsDirectLimit.Equiv_apply RestrictedProduct.not_mem_support RestrictedProduct.mem_structureSubring_iff RestrictedProduct.not_mem_mulSupport RestrictedProduct.support_neg RestrictedProduct.mem_indexSupport_iff RestrictedProduct.mulSupport_inv RestrictedProduct.mapAlongLinearMap_apply RingEquiv.restrictedProductCongr_symm_apply RingEquiv.restrictedProductCongrRight_apply MulEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductProd_symm_apply_coe Equiv.restrictedProductCongrRight_apply AddEquiv.restrictedProductCongr_apply Equiv.restrictedProductCongrLeft'_symm_apply_apply Equiv.restrictedProductCongr_apply_apply Equiv.restrictedProductCongrLeft_apply_apply RestrictedProduct.flatten_equiv'_apply AddEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductCongr_symm_apply Equiv.restrictedProductCongrRight_symm_apply RestrictedProduct.flatten_equiv'_symm_apply AddEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductCongrLeft'_apply RestrictedProduct.flatten_apply"
p2m_attr_erase "simp" "RingEquiv.restrictedProductCongr_apply_apply RingEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductProd_apply RestrictedProduct.flatten_equiv_apply RestrictedProduct.flatten_equiv_symm_apply LinearEquiv.restrictedProductCongrLeft'_apply"

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 80000

open IsDedekindDomain NumberField NumberField.AdelicLevel NumberField.AdelicBox AutomorphicForm AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering NumberField.InfinitePlace NumberField.InfinitePlace.Completion

open NumberField.TateGlobal
open LanglandsTunnell LanglandsTunnell.RealArchParam LanglandsTunnell.Converse

namespace Ws47
namespace CER

open NumberField.AdelicVolume MeasureTheory Matrix

theorem unipotentGL2_mul_centralScalar {F : Type} [Field F] [NumberField F]
    (x : AdeleRing (𝓞 F) F) (w : (AdeleRing (𝓞 F) F)ˣ) (g : AdelicGL2 (𝓞 F) F) :
    unipotentGL2 x * (centralScalar (𝓞 F) F w * g) = centralScalar (𝓞 F) F w * (unipotentGL2 x * g) := by
  rw [← mul_assoc, ← mul_assoc]
  congr 1
  apply Units.ext
  rw [Units.val_mul, Units.val_mul, centralScalar_val, ← Matrix.scalar_apply]
  exact ((Matrix.scalar_commute (w : AdeleRing (𝓞 F) F) (Commute.all _) _).eq).symm

theorem whittakerCoefficient_centralScalar_mul {F : Type} [Field F] [NumberField F]
    (pins : CarrierPins F) (ψ : AddChar (AdeleRing (𝓞 F) F) ℂ) {ξ : pins.Z →* ℂˣ}
    {φ : AdelicGL2 (𝓞 F) F → ℂ}
    (hφ : ∀ (zz : pins.Z) (g : AdelicGL2 (𝓞 F) F),
      φ (centralScalar (𝓞 F) F (zz : (AdeleRing (𝓞 F) F)ˣ) * g) = ((ξ zz : ℂˣ) : ℂ) * φ g)
    (zz : pins.Z) (α : F) (g : AdelicGL2 (𝓞 F) F) :
    whittakerCoefficient F pins ψ φ α (centralScalar (𝓞 F) F (zz : (AdeleRing (𝓞 F) F)ˣ) * g)
      = ((ξ zz : ℂˣ) : ℂ) * whittakerCoefficient F pins ψ φ α g := by
  letI := pins.nS
  simp only [whittakerCoefficient]
  simp_rw [unipotentGL2_mul_centralScalar, hφ, mul_assoc]
  exact integral_const_mul _ _

private theorem _root_.Ws47.CER.central_transform {F : Type} [Field F] [NumberField F] {pins : CarrierPins F}
    {Ψ : HeckeEigensystem F ℂ} (R : SmoothCuspRealizationAt F pins Ψ)
    (zz : pins.Z) (g : AdelicGL2 (𝓞 F) F) :
    R.toFun (centralScalar (𝓞 F) F (zz : (AdeleRing (𝓞 F) F)ˣ) * g) = ((R.centralChar zz : ℂˣ) : ℂ) * R.toFun g := by
  letI := pins.mS
  exact (((lsXiMemberAt_iff (𝓞 F) F pins.μ pins.Z R.centralChar pins.D R.toFun).mp
    R.smoothCusp.1.1).1).central_transform zz g

p2m_export "Ws47.CER" "central_transform"

variable {w : InfinitePlace ℚ} (hw : w.IsReal) (a : (w.Completion)ˣ)

noncomputable def archScalar (a : (w.Completion)ˣ) : AdelicGL2 (𝓞 ℚ) ℚ :=
  centralScalar (𝓞 ℚ) ℚ (archCentralUnit ℚ w a)

theorem glFin_archScalar : glFin (𝓞 ℚ) ℚ (archScalar a) = 1 := by
  refine Units.ext (Matrix.ext fun i j => ?_)
  rw [archScalar, glFin_apply, centralScalar_val, Matrix.diagonal_apply, Units.val_one]
  by_cases h : i = j
  · subst h
    rw [if_pos rfl, Matrix.one_apply_eq]
    exact archCentralUnit_snd w a
  · rw [if_neg h, Matrix.one_apply_ne h]
    rfl

theorem glFin_archScalar_mul (g : AdelicGL2 (𝓞 ℚ) ℚ) :
    glFin (𝓞 ℚ) ℚ (archScalar a * g) = glFin (𝓞 ℚ) ℚ g := by
  rw [map_mul, glFin_archScalar, one_mul]

theorem archComponent_glArch_archScalar :
    ((archComponent ℚ w (glArch (𝓞 ℚ) ℚ (archScalar a)) : GL (Fin 2) w.Completion) :
        Matrix (Fin 2) (Fin 2) w.Completion) = Matrix.diagonal (fun _ => (a : w.Completion)) := by
  ext i j : 1
  rw [archComponent_apply, glArch_apply, archScalar]
  by_cases h : i = j
  · subst h
    rw [centralScalar_apply_eq, Matrix.diagonal_apply_eq]
    exact archCentralUnit_fst_self w a
  · rw [centralScalar_apply_ne _ h, Matrix.diagonal_apply_ne _ h]
    rfl

include hw in
theorem realComponent_eq (g : AdelicGL2 (𝓞 ℚ) ℚ) :
    realComponent w hw g = (ringEquivRealOfIsReal hw).toRingHom.mapMatrix
      ((archComponent ℚ w (glArch (𝓞 ℚ) ℚ g) : GL (Fin 2) w.Completion) : Matrix (Fin 2) (Fin 2) w.Completion) := by
  ext i j; rfl

include hw in
theorem realComponent_archScalar_mul (g : AdelicGL2 (𝓞 ℚ) ℚ) :
    realComponent w hw (archScalar a * g)
      = (ringEquivRealOfIsReal hw (a : w.Completion)) • realComponent w hw g := by
  rw [realComponent_eq, realComponent_eq, map_mul, map_mul, Units.val_mul, archComponent_glArch_archScalar,
    map_mul, Matrix.smul_eq_diagonal_mul]
  congr 1
  rw [RingHom.mapMatrix_apply, Matrix.diagonal_map (map_zero _)]
  rfl

include hw in
theorem prod_archDetNorm_archScalar_mul (g : AdelicGL2 (𝓞 ℚ) ℚ) :
    ∏ v : InfinitePlace ℚ, archDetNorm v (archScalar a * g) ^ v.mult
      = (‖(a : w.Completion)‖ * ‖(a : w.Completion)‖) * ∏ v : InfinitePlace ℚ, archDetNorm v g ^ v.mult := by
  rw [Fintype.prod_subsingleton _ w, Fintype.prod_subsingleton _ w, NumberField.InfinitePlace.mult, if_pos hw,
    pow_one, pow_one, archScalar, archDetNorm_centralScalar_mul]

include hw in
theorem archW_archScalar_mul (P : RealArchParam) (archC : ∀ w : InfinitePlace ℚ, w.IsComplex → ComplexArchParam)
    (dR : ∀ (w : InfinitePlace ℚ) (hw : w.IsReal), ArchDatumR P)
    (dC : ∀ (w : InfinitePlace ℚ) (hw : w.IsComplex), ArchDatumC (archC w hw))
    (ht : ringEquivRealOfIsReal hw (a : w.Completion) ≠ 0) (g : AdelicGL2 (𝓞 ℚ) ℚ) :
    archW (fun _ _ => P) archC dR dC (archScalar a * g)
      = ArchR.centralChar P (ringEquivRealOfIsReal hw (a : w.Completion)) *
          ((|ringEquivRealOfIsReal hw (a : w.Completion)| : ℝ) : ℂ) * archW (fun _ _ => P) archC dR dC g := by
  unfold archW
  rw [Fintype.prod_subsingleton _ w, Fintype.prod_subsingleton _ w, dif_pos hw, dif_pos hw,
    realComponent_archScalar_mul hw a g, (dR w hw).central_law _ _ ht]

theorem norm_centralChar_of_pos (P : RealArchParam) {t : ℝ} (ht : 0 < t) :
    ‖ArchR.centralChar P t‖ = t ^ (RealArchParam.centralExponent P).re := by
  unfold ArchR.centralChar ArchR.quasiChar
  rw [norm_mul, abs_of_pos ht, Complex.norm_cpow_eq_rpow_re_of_pos ht]
  split_ifs
  · rw [norm_one, mul_one]
  · rw [sign_pos ht, SignType.coe_one, Complex.ofReal_one, norm_one, mul_one]

theorem abs_mul_abs_mul_rpow (t X : ℝ) (hX : 0 ≤ X) :
    (|t| * |t| * X) ^ (-(1 / 2 : ℝ)) = |t|⁻¹ * X ^ (-(1 / 2 : ℝ)) := by
  rw [Real.mul_rpow (mul_nonneg (abs_nonneg t) (abs_nonneg t)) hX]
  congr 1
  rw [show |t| * |t| = |t| ^ (2 : ℝ) by rw [Real.rpow_two, sq], ← Real.rpow_mul (abs_nonneg t),
    show (2 : ℝ) * -(1 / 2 : ℝ) = -1 by norm_num, Real.rpow_neg_one]

theorem prod_archDetNorm_nonneg (g : AdelicGL2 (𝓞 ℚ) ℚ) :
    0 ≤ ∏ v : InfinitePlace ℚ, archDetNorm v g ^ v.mult :=
  Finset.prod_nonneg fun v _ => pow_nonneg (archDetNorm_pos v g).le _

theorem det_diagOne_adele (F : Type) [Field F] [NumberField F] (a : (AdeleRing (𝓞 F) F)ˣ) :
    Matrix.GeneralLinearGroup.det (diagOne a) = a := by
  ext
  show (Matrix.diagonal ![((a : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F), 1]).det
    = ((a : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F)
  rw [Matrix.det_diagonal, Fin.prod_univ_two]
  simp

theorem det_heckeGen_eq_uniformizerIdele (F : Type) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) :
    Matrix.GeneralLinearGroup.det (heckeGen (𝓞 F) F v) = uniformizerIdele F v := by
  show Matrix.GeneralLinearGroup.det (diagOne (uniformizerIdele F v)) = uniformizerIdele F v
  exact det_diagOne_adele F _

include hw in

theorem centralChar_archCentralUnit_eq
    (D : Set (AdelicGL2 (𝓞 ℚ) ℚ)) (Ψ : HeckeEigensystem ℚ ℂ)
    (R' : SmoothCuspRealizationAt ℚ
      (productionPinsOf ℚ D (fun N => levelOne (𝓞 ℚ) ℚ N ⊓ finiteAdelicGL2Subgroup ℚ)
        (fun v => heckeGen (𝓞 ℚ) ℚ v) (adelicBox ℚ)) Ψ)
    (P : RealArchParam) (archC : ∀ w : InfinitePlace ℚ, w.IsComplex → ComplexArchParam)
    (dR : ∀ (w : InfinitePlace ℚ) (hw : w.IsReal), ArchDatumR P)
    (dC : ∀ (w : InfinitePlace ℚ) (hw : w.IsComplex), ArchDatumC (archC w hw))
    (g₀ g₁ : AdelicGL2 (𝓞 ℚ) ℚ) (z₀ : ℂ)
    (hg₁ : glFin (𝓞 ℚ) ℚ g₁ = glFin (𝓞 ℚ) ℚ g₀)
    (hW₁ : whittakerCoefficient ℚ
        (productionPinsOf ℚ D (fun N => levelOne (𝓞 ℚ) ℚ N ⊓ finiteAdelicGL2Subgroup ℚ)
          (fun v => heckeGen (𝓞 ℚ) ℚ v) (adelicBox ℚ))
        (NumberField.StandardAddChar.stdAddChar ℚ) R'.toFun 1 g₁ ≠ 0)
    (hfac : ∀ g : AdelicGL2 (𝓞 ℚ) ℚ, glFin (𝓞 ℚ) ℚ g = glFin (𝓞 ℚ) ℚ g₀ →
      whittakerCoefficient ℚ
        (productionPinsOf ℚ D (fun N => levelOne (𝓞 ℚ) ℚ N ⊓ finiteAdelicGL2Subgroup ℚ)
          (fun v => heckeGen (𝓞 ℚ) ℚ v) (adelicBox ℚ))
        (NumberField.StandardAddChar.stdAddChar ℚ) R'.toFun 1 g =
        (((∏ v : InfinitePlace ℚ, NumberField.AdelicVolume.archDetNorm v g ^ v.mult) ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) *
          archW (fun _ _ => P) archC dR dC g * z₀) :
    ((R'.centralChar ⟨archCentralUnit ℚ w a, Subgroup.mem_top _⟩ : ℂˣ) : ℂ)
      = ArchR.centralChar P (ringEquivRealOfIsReal hw (a : w.Completion)) := by
  set t : ℝ := ringEquivRealOfIsReal hw (a : w.Completion) with ht_def
  have ht : t ≠ 0 := by
    rw [ht_def, map_ne_zero_iff _ (ringEquivRealOfIsReal hw).injective]
    exact a.ne_zero
  have hta : ‖(a : w.Completion)‖ = |t| := by
    rw [ht_def, ← Real.norm_eq_abs, norm_ringEquivRealOfIsReal hw]
  have e1 := whittakerCoefficient_centralScalar_mul _ (NumberField.StandardAddChar.stdAddChar ℚ)
    (central_transform R') ⟨archCentralUnit ℚ w a, Subgroup.mem_top _⟩ 1 g₁
  have e2 := hfac (archScalar a * g₁) (by rw [glFin_archScalar_mul, hg₁])
  rw [prod_archDetNorm_archScalar_mul hw, archW_archScalar_mul hw a P archC dR dC ht, hta,
    abs_mul_abs_mul_rpow t _ (prod_archDetNorm_nonneg g₁)] at e2
  have e3 := hfac g₁ hg₁
  apply mul_right_cancel₀ hW₁
  rw [← e1, show centralScalar (𝓞 ℚ) ℚ
      ((⟨archCentralUnit ℚ w a, Subgroup.mem_top _⟩ :
        (productionPinsOf ℚ D (fun N => levelOne (𝓞 ℚ) ℚ N ⊓ finiteAdelicGL2Subgroup ℚ)
          (fun v => heckeGen (𝓞 ℚ) ℚ v) (adelicBox ℚ)).Z) : (AdeleRing (𝓞 ℚ) ℚ)ˣ) * g₁ = archScalar a * g₁ from rfl,
    e2, e3]
  have ht' : ((|t| : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 (abs_ne_zero.2 ht)
  push_cast
  field_simp
  ring

end Ws47.CER

namespace Ws47
namespace OMG

open NumberField.AdelicVolume MeasureTheory Matrix

theorem absNorm_eq_pow_inertiaDeg (K : Type) [Field K] [NumberField K]
    [Algebra (𝓞 ℚ) (𝓞 K)] [Algebra.IsIntegral (𝓞 ℚ) (𝓞 K)] (𝔓 : HeightOneSpectrum (𝓞 K)) :
    Ideal.absNorm 𝔓.asIdeal =
      Ideal.absNorm (𝔓.under (𝓞 ℚ)).asIdeal ^ ((𝔓.under (𝓞 ℚ)).asIdeal.inertiaDeg' 𝔓.asIdeal) := by

  classical
  haveI : 𝔓.asIdeal.LiesOver (𝔓.under (𝓞 ℚ)).asIdeal := ⟨rfl⟩
  haveI : (𝔓.under (𝓞 ℚ)).asIdeal.IsMaximal := (𝔓.under (𝓞 ℚ)).isMaximal
  letI : Field (𝓞 ℚ ⧸ (𝔓.under (𝓞 ℚ)).asIdeal) := Ideal.Quotient.field _
  haveI : Finite (𝓞 K ⧸ 𝔓.asIdeal) := Ideal.finiteQuotientOfFreeOfNeBot _ 𝔓.ne_bot
  haveI : Module.Finite (𝓞 ℚ ⧸ (𝔓.under (𝓞 ℚ)).asIdeal) (𝓞 K ⧸ 𝔓.asIdeal) := Module.Finite.of_finite
  rw [Ideal.inertiaDeg_algebraMap, Ideal.absNorm_apply, Ideal.absNorm_apply, Submodule.cardQuot_apply,
    Submodule.cardQuot_apply]
  exact Module.natCard_eq_pow_finrank

theorem rpow_neg_half_sq {x : ℝ} (hx : 0 ≤ x) : (x ^ (-(1 / 2 : ℝ))) ^ 2 = x⁻¹ := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul hx]
  norm_num
  exact Real.rpow_neg_one x

theorem twist_pow_bookkeeping (q : ℕ) (f : ℕ) :
    (((((q : ℝ) ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ)) ^ 2) ^ f
      = ((((((q ^ f : ℕ) : ℝ)) ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ)) ^ 2 := by
  have hq : (0 : ℝ) ≤ q := Nat.cast_nonneg q
  have hqf : (0 : ℝ) ≤ ((q ^ f : ℕ) : ℝ) := Nat.cast_nonneg _
  rw [← Complex.ofReal_pow, ← Complex.ofReal_pow, ← Complex.ofReal_pow, rpow_neg_half_sq hq,
    rpow_neg_half_sq hqf, Nat.cast_pow, inv_pow]

theorem centralExponent_twist_half (P : RealArchParam) :
    (P.twist (((1 / 2 : ℝ)) : ℂ) 0).centralExponent = P.centralExponent + 1 := by
  cases P <;> simp [RealArchParam.twist, RealArchParam.centralExponent] <;> ring

theorem centralSign_twist_zero (P : RealArchParam) (t : ℂ) : (P.twist t 0).centralSign = P.centralSign := by
  cases P <;> simp [RealArchParam.twist, RealArchParam.centralSign]

theorem centralChar_eq_isArchCompAt_rhs (P : RealArchParam) {w : InfinitePlace ℚ} (hw : w.IsReal)
    (a : (w.Completion)ˣ) :
    ArchR.centralChar P (ringEquivRealOfIsReal hw (a : w.Completion))
      = ((‖(a : w.Completion)‖ : ℂ) ^ ((w.mult : ℂ) * P.centralExponent)) *
        (extensionEmbedding w (a : w.Completion) / (‖(a : w.Completion)‖ : ℂ)) ^ (P.centralSign.val : ℤ) := by
  set t : ℝ := ringEquivRealOfIsReal hw (a : w.Completion) with ht_def
  have ht : t ≠ 0 := by
    rw [ht_def, map_ne_zero_iff _ (ringEquivRealOfIsReal hw).injective]
    exact a.ne_zero
  have ht' : ((|t| : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 (abs_ne_zero.2 ht)
  have hn : ‖(a : w.Completion)‖ = |t| := by
    rw [ht_def, ← Real.norm_eq_abs, norm_ringEquivRealOfIsReal hw]
  have he : (extensionEmbedding w (a : w.Completion) : ℂ) = (t : ℂ) :=
    (extensionEmbeddingOfIsReal_apply hw _).symm
  have hmult : w.mult = 1 := by rw [NumberField.InfinitePlace.mult, if_pos hw]
  rw [hn, he, hmult, Nat.cast_one, one_mul]
  unfold ArchR.centralChar ArchR.quasiChar
  congr 1
  have h01 : ∀ s : ZMod 2, s = 0 ∨ s = 1 := by decide
  rcases h01 P.centralSign with h0 | h1
  · rw [h0, if_pos rfl, ZMod.val_zero, Int.ofNat_zero, zpow_zero]
  · rw [h1, if_neg (by decide), show (((1 : ZMod 2).val : ℕ) : ℤ) = 1 from rfl, zpow_one, eq_div_iff ht']
    exact_mod_cast sign_mul_abs t

theorem centralChar_eq_of_toFun_eq {pins pins' : CarrierPins ℚ} (hZ : pins.Z = ⊤) (hZ' : pins'.Z = ⊤)
    {Θ Θ' : HeckeEigensystem ℚ ℂ}
    (R : SmoothCuspRealizationAt ℚ pins Θ) (R' : SmoothCuspRealizationAt ℚ pins' Θ') (h : R.toFun = R'.toFun)
    (zz : (AdeleRing (𝓞 ℚ) ℚ)ˣ) :
    ((R.centralChar ⟨zz, hZ ▸ Subgroup.mem_top zz⟩ : ℂˣ) : ℂ) = ((R'.centralChar ⟨zz, hZ' ▸ Subgroup.mem_top zz⟩ : ℂˣ) : ℂ) := by
  obtain ⟨g, hg⟩ := R'.exists_ne_zero
  have hg' : R.toFun g ≠ 0 := by rw [h]; exact hg
  rw [R.centralChar_apply_eq _ hg', R'.centralChar_apply_eq _ hg, h]

end Ws47.OMG

open Ws47.OMG in
theorem solution
    (K : Type) [Field K] [NumberField K]
    [Algebra (𝓞 ℚ) (𝓞 K)] [Algebra.IsIntegral (𝓞 ℚ) (𝓞 K)]
    (c u d₁ d₂ : ℝ) (T : Finset (AdelicGL2 (𝓞 ℚ) ℚ))
    (hc : 0 < c) (hd₁ : 0 < d₁) (hd : d₁ < d₂)
    (hcov : CoversModCentre ℚ (⋃ x ∈ T, (· * x) '' centreCutSiegelSet ℚ c u d₁ d₂))
    (Φ : HeckeEigensystem ℚ ℂ)
    (P : RealArchParam) (archC : ∀ w : InfinitePlace ℚ, w.IsComplex → ComplexArchParam)
    (dR : ∀ (w : InfinitePlace ℚ) (hw : w.IsReal), ArchDatumR P)
    (dC : ∀ (w : InfinitePlace ℚ) (hw : w.IsComplex), ArchDatumC (archC w hw))
    (hWF : ArchOccursInClassOf ℚ (⋃ x ∈ T, (· * x) '' centreCutSiegelSet ℚ c u d₁ d₂) Φ
        (fun φ => ∃ g₀ : AdelicGL2 (𝓞 ℚ) ℚ,
          (∃ g : AdelicGL2 (𝓞 ℚ) ℚ, glFin (𝓞 ℚ) ℚ g = glFin (𝓞 ℚ) ℚ g₀ ∧
            whittakerCoefficient ℚ
              (productionPinsOf ℚ (⋃ x ∈ T, (· * x) '' centreCutSiegelSet ℚ c u d₁ d₂)
            (fun N => levelOne (𝓞 ℚ) ℚ N ⊓ finiteAdelicGL2Subgroup ℚ) (fun v => heckeGen (𝓞 ℚ) ℚ v) (adelicBox ℚ))
              (NumberField.StandardAddChar.stdAddChar ℚ) φ 1 g ≠ 0) ∧
          ∃ z : ℂ, ∀ g : AdelicGL2 (𝓞 ℚ) ℚ, glFin (𝓞 ℚ) ℚ g = glFin (𝓞 ℚ) ℚ g₀ →
            whittakerCoefficient ℚ
              (productionPinsOf ℚ (⋃ x ∈ T, (· * x) '' centreCutSiegelSet ℚ c u d₁ d₂)
            (fun N => levelOne (𝓞 ℚ) ℚ N ⊓ finiteAdelicGL2Subgroup ℚ) (fun v => heckeGen (𝓞 ℚ) ℚ v) (adelicBox ℚ))
              (NumberField.StandardAddChar.stdAddChar ℚ) φ 1 g =
              (((∏ v : InfinitePlace ℚ, NumberField.AdelicVolume.archDetNorm v g ^ v.mult) ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) *
                archW (fun _ _ => P) archC dR dC g * z))
    (hP0 : (RealArchParam.centralExponent P).re = 0) :
    ∃ (Tq : Finset (HeightOneSpectrum (𝓞 ℚ))) (ω : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ),
      IsAdmissibleTwist K ω ∧
      (∀ v : HeightOneSpectrum (𝓞 K), v.under (𝓞 ℚ) ∉ Tq →
        IsUnramifiedCharAt ω v ∧
          ((ω (uniformizerIdele K v) : ℂˣ) : ℂ) = ((formalBaseChange ℚ K Φ).twist fun v => (((Ideal.absNorm v.asIdeal : ℝ) ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ)).b v) ∧
      (∀ (w : InfinitePlace K) (hw : w.IsReal),
        IsArchCompAt K ω w (archOfParamR K P w hw).centralExponent ((archOfParamR K P w hw).centralSign.val : ℤ)) ∧
      (∀ (w : InfinitePlace K) (hw : w.IsComplex),
        IsArchCompAt K ω w (archOfParamC K P w hw).centralExponent (archOfParamC K P w hw).centralTwist) := by
  classical

  choose dR' hdR' using fun (w : InfinitePlace ℚ) (hw : w.IsReal) =>
    LanglandsTunnell.Converse.ArchDatumR.exists_twist_W_eq_abs_det_rpow_mul P (dR w hw) (1 / 2 : ℝ)

  have hocc := LanglandsTunnell.archOccursInClassOf_whittakerCoefficient_fibre_eq_archW_twist_of_archOccursInClassOf_rat
    c u d₁ d₂ T hd₁ Φ P archC dR dC (1 / 2 : ℝ) dR' (fun w hw g => (hdR' w hw).1 g) hWF
  obtain ⟨Θ'', hΘ'', R'', hR''gen, g₀, ⟨g₁, hg₁, hW₁⟩, z₀, hfac⟩ := hocc

  obtain ⟨Rg, hRg⟩ := AutomorphicForm.exists_smoothCuspRealizationAt_productionPinsGeneral_toFun_eq_of_coversModCentre
    c u d₁ d₂ T hc hd₁ hd hcov Θ''.toRawCentral R'' hR''gen
  have hcont : Continuous Rg.toFun := by rw [hRg]; exact hR''gen

  have hP : ∀ (w : InfinitePlace ℚ) (hw : w.IsReal),
      IsArchCompAt ℚ (Rg.centralChar.comp Subgroup.topEquiv.symm.toMonoidHom) w
        (P.centralExponent + 1) (P.centralSign.val : ℤ) := by
    intro w hw x
    rw [archLocalChar_apply]
    have e1 : (Rg.centralChar.comp Subgroup.topEquiv.symm.toMonoidHom) (AdelicVolume.archCentralUnit ℚ w x)
        = Rg.centralChar ⟨AdelicVolume.archCentralUnit ℚ w x, Subgroup.mem_top _⟩ := rfl
    rw [e1, centralChar_eq_of_toFun_eq rfl rfl Rg R'' hRg,
      Ws47.CER.centralChar_archCentralUnit_eq hw x _ _ R'' _ archC dR' dC g₀ g₁ z₀ hg₁ hW₁ hfac,
      centralChar_eq_isArchCompAt_rhs, centralExponent_twist_half, centralSign_twist_zero]

  obtain ⟨S₀, hS₀⟩ :=
    LanglandsTunnell.exists_finset_norm_b_eq_absNorm_of_whittakerCoefficient_fibre_eq_archW_of_re_centralExponent_eq_zero
      c u d₁ d₂ T hd hcov Φ P archC dR dC hWF hP0
  obtain ⟨S₁, hS₁⟩ := hΘ''
  have hb : ∀ p : HeightOneSpectrum (𝓞 ℚ), p ∉ S₀ ∪ S₁ → ‖Θ''.b p‖ = 1 := by
    intro p hp
    rw [Finset.notMem_union] at hp
    rw [(hS₁ p hp.2).2, HeckeEigensystem.twist_b, norm_mul, hS₀ p hp.1, norm_pow, Complex.norm_real,
      Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg _) _), rpow_neg_half_sq (Nat.cast_nonneg _)]
    exact inv_mul_cancel₀ (Nat.cast_ne_zero.2 (Ideal.absNorm_eq_zero_iff.not.2 p.ne_bot))

  obtain ⟨Tq, ω, hadm, hfin, hreal, hcx⟩ :=
    LanglandsTunnell.Converse.exists_isAdmissibleTwist_eq_formalBaseChange_b_isArchCompAt_archOfParam
      K Θ'' Rg hcont P hP (S₀ ∪ S₁) hb

  refine ⟨Tq ∪ S₁, ω, hadm, fun 𝔓 h𝔓 => ?_, hreal, hcx⟩
  rw [Finset.notMem_union] at h𝔓
  obtain ⟨hunr, hval⟩ := hfin 𝔓 h𝔓.1
  refine ⟨hunr, ?_⟩
  rw [hval, formalBaseChange_b, HeckeEigensystem.twist_b, formalBaseChange_b, (hS₁ _ h𝔓.2).2,
    HeckeEigensystem.twist_b, mul_pow, absNorm_eq_pow_inertiaDeg K 𝔓]
  congr 1
  exact twist_pow_bookkeeping _ _

end S_LanglandsTunnell_exists_isAdmissibleTwist_eq_twist_formalBaseChange_b_isArchCompAt_archOfParam_of_whittakerCoefficient_fibre_eq_archW
end P2MW
export P2MW.S_LanglandsTunnell_exists_isAdmissibleTwist_eq_twist_formalBaseChange_b_isArchCompAt_archOfParam_of_whittakerCoefficient_fibre_eq_archW (solution)
