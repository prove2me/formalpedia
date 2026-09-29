-- Prove2me | solution 1 for LanglandsTunnell.RankinSelberg.forall_exists_rational_rsLocalIntegral_translate_of_shellRecurrence_of_centralChar_of_rationalTorusShell_of_gauge
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.670037+00:00
-- url     : https://prove2.me/submissions/2020682b-79e6-5b23-854c-39f560a7c57a

import Definitions.Def_LanglandsTunnell_CubicInduction_MirabolicMajorant
import Definitions.Def_UnramifiedWhittaker_HeckeRecursion
import Definitions.Def_LanglandsTunnell_CubicInduction_LocalZeta31
import Definitions.Def_LanglandsTunnell_RSCarrier
import Definitions.Def_LanglandsTunnell_StandardLocalConstantsAt
import Definitions.Def_LanglandsTunnell_CubicInduction_Structure
import Definitions.Def_LanglandsTunnell_CubicInduction_GlobalZeta31
import Definitions.Def_AutomorphicForm_SmoothingKernel
import Definitions.Def_AdelicDock_LocalEmbedding
import Definitions.Def_AutomorphicForm_LocalOrbitalBase
import Theorems.Thm_LanglandsTunnell_RankinSelberg_exists_rational_rsLocalIntegral_of_shellGauge_of_rationalTorusShell_of_shellRecurrence_of_central
import Theorems.Thm_LanglandsTunnell_TateLocal_modulus_adicCompletion_eq_nnnorm
import Theorems.Thm_AdelicDock_isCompact_and_isOpen_localLevelOne
import Theorems.Thm_LanglandsTunnell_CubicInduction_forall_mem_gl3CyclicSubspace_exists_gauge_and_exists_gauge_dualWhittakerFn3
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LanglandsTunnell_RankinSelberg_forall_exists_rational_rsLocalIntegral_translate_of_shellRecurrence_of_centralChar_of_rationalTorusShell_of_gauge
p2m_attr_erase "instance" "instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions instCountableOfNumberField_definitions FLT.InfiniteAdeleBaseChange.uniqueSelfExtension NumberField.InfinitePlace.RamifiedExtension.instCoeExtension NumberField.InfinitePlace.UnramifiedExtension.instCoeExtension IsDedekindDomain.HeightOneSpectrum.Extension.instAlgebraSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnder IsDedekindDomain.HeightOneSpectrum.Extension.instAlgebraSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnder_1 IsDedekindDomain.HeightOneSpectrum.instMulActionHomClassAlgHomTensorProductAdicCompletionForallValEqUnder_definitions IsDedekindDomain.HeightOneSpectrum.Extension.instAlgebraAdicCompletionValEqUnder IsDedekindDomain.HeightOneSpectrum.adicCompletion.instFiniteForallValEqUnderOfFiniteDimensional_definitions IsDedekindDomain.HeightOneSpectrum.instIsBiscalarSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersTensorProductCoeAlgHomTensorAdicCompletionIntegersTo IsDedekindDomain.HeightOneSpectrum.Extension.instContinuousSMulAdicCompletionValEqUnder IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsModuleTopology IsDedekindDomain.HeightOneSpectrum.Extension.instFiniteSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnderOfFiniteDimensional IsDedekindDomain.HeightOneSpectrum.adicCompletion.instFiniteValEqUnderOfFiniteDimensional_definitions instIsBiscalarTensorProductCoeAlgHomBaseChange_of_algebraMap IsDedekindDomain.HeightOneSpectrum.instIsScalarTowerSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnder_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsModuleTopologyPi Submodule.instIsTopologicalModuleSubtypeMem Pi.instTopologicalModule IsTopologicalModule.toContinuousSMul IsTopologicalModule.toContinuousAdd instFunLike SemialgHomClass.toSemilinearMapClass instCoeTCSemialgHom SemialgHomClass.toRingHomClass SemialgHomClass.instSemialgHom IsDirectLimit.Module.instDirectLimitCoeLinearMapIdOfOfNonempty RestrictedProduct.instIsDirectLimit'"
p2m_attr_erase "instance" "RestrictedProduct.instIsDirectLimit RestrictedProduct.instNonemptyOrderDualElemSetSets_definitions RestrictedProduct.instDirectedSystem RestrictedProduct.instDirectedSystemCoeSubmoduleCoeLinearMapIdInclusionLinearMap RestrictedProduct.directed RestrictedProduct.instDirectedSystemOrderDualElemSetSetsCoeSubmodulePrincipalValMemCoeLinearMapIdInclusionLinearMap M4aHerbrand.Bridge.sigmaCompactSpace_finiteAdeleRing M4aHerbrand.Bridge.sigmaCompactSpace_adeleRing M4aHerbrand.Bridge.sigmaCompactSpace_infiniteAdeleRing M4aHerbrand.Bridge.sigmaCompactSpace_completion M4aHerbrand.Bridge.instT2SpaceAdeleRing"
p2m_attr_erase "simp" "LocalGL2.coe_localRepSome LocalGL2.coe_diagPi LocalGL2.coe_localRepInf LocalGL2.coe_localRepSome_inv LocalGL2.coe_unipotentInt LocalGL2.coe_weylInt LocalGL2.coe_diagPi_inv LocalGL2.transposeGL_val LocalGL2.transposeGL_one LocalGL2.swapUnit_val LanglandsTunnell.CubicLambda.ResolventDatum.s3.injEq LanglandsTunnell.CubicLambda.ResolventDatum.s3.sizeOf_spec LanglandsTunnell.CubicLambda.ResolventDatum.cyclic.sizeOf_spec LanglandsTunnell.CubicLambda.ResolventDatum.cyclic.injEq M4aHerbrand.IdeleGaloisDescent.mk.sizeOf_spec M4aHerbrand.IdeleGaloisDescent.mk.injEq M4aHerbrand.AdeleBaseChange.mk.sizeOf_spec M4aHerbrand.AdeleBaseChange.mk.injEq M4aHerbrand.Bridge.prodTensorAlgEquiv_tmul M4aHerbrand.Bridge.genuineβ_fst M4aHerbrand.Bridge.genuineβ_snd M4aHerbrand.ArchSemilocal.psiFactor_tmul M4aHerbrand.ArchSemilocal.psi_apply FLT.InfiniteAdeleBaseChange.evalAlgHom_apply FLT.InfiniteAdeleBaseChange.BaseChangeData.mk.sizeOf_spec FLT.InfiniteAdeleBaseChange.tensorPiAlgHom_tmul_apply FLT.InfiniteAdeleBaseChange.collapsePlaces_apply FLT.InfiniteAdeleBaseChange.tensorPiAlgEquiv_tmul_apply FLT.InfiniteAdeleBaseChange.InfinitePlaceData.mk.sizeOf_spec FLT.InfiniteAdeleBaseChange.InfinitePlaceData.mk.injEq FLT.InfiniteAdeleBaseChange.BaseChangeData.mk.injEq M4aHerbrand.Bridge.finiteConorm_apply SemialgHom.baseChange_of_algebraMap_tmul_left SemialgHom.baseChangeRightOfAlgebraMap_apply Pi.semialgHomPi_apply Pi.semialgHom_apply Module.Basis.rightBaseChange_apply LinearEquiv.coe_mulLeft LinearEquiv.coe_mulRight WithVal.semialgebraMap_toFun_ofVal"
p2m_attr_erase "simp" "Module.Basis.rightBaseChange_repr IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers.tensorCoe_tmul IsDedekindDomain.HeightOneSpectrum.tensorAdicCompletionIntegersTo_tmul SemialgHom.baseChangeRightOfAlgebraMap_coe IsDedekindDomain.HeightOneSpectrum.adicCompletion.integerBaseChangeLinearEquiv_tmul_apply SemialgHom.baseChange_of_algebraMap_tmul_right IsLocalization.map_moduleTensorEquiv_symm_tmul IsLocalization.leftModuleTensorEquiv_apply IsLocalization.moduleLid_symm_apply IsLocalization.leftModuleTensorEquiv_symm_apply IsLocalization.map_moduleTensorEquiv_tmul IsModuleTopology.continuousLinearEquiv_apply AlgEquiv.extendScalars_symm_apply IsModuleTopology.Module.Basis.equivFun_homeo_symm_apply IsModuleTopology.Module.Basis.equivFun_homeo_apply IsModuleTopology.continuousAlgEquivOfIsBiscalar_apply AlgEquiv.extendScalars_apply IsModuleTopology.continuousLinearEquiv_symm_apply SemialgHom.restrictScalars_toFun SemialgHom.mk.sizeOf_spec SemialgHom.mk.injEq SemialgHom.coe_coe coe_mk TensorProduct.RightActions.smul_def TensorProduct.RightActions.Module.TensorProduct.comm_symm_apply_tmul TensorProduct.RightActions.LinearMap.baseChange_id TensorProduct.RightActions.algebraMap_eval TensorProduct.RightActions.Module.TensorProduct.comm_apply_tmul TensorProduct.RightActions.Algebra.TensorProduct.comm_symm_apply_tmul TensorProduct.RightActions.Algebra.TensorProduct.comm_apply_tmul M4aHerbrand.Bridge.tensorAdeleRingEquiv_apply M4aHerbrand.Bridge.flattenPlaces_apply M4aHerbrand.Bridge.congrPlaces_apply M4aHerbrand.Bridge.integralTensorRingEquiv_tmul M4aHerbrand.Bridge.moduleStructureBridge_apply RestrictedProduct.lTensorEquivLeft_tmul RestrictedProduct.lTensorEquiv_tmul RestrictedProduct.lTensorLeft_tmul RestrictedProduct.lTensor_tmul IsDirectLimit.Module.linearEquiv_symm_apply"
p2m_attr_erase "simp" "IsDirectLimit.linearEquiv_symm_apply IsDirectLimit.lift_of IsDirectLimit.Module.linearEquiv_apply IsDirectLimit.Module.lift_of IsDirectLimit.Equiv_apply RestrictedProduct.not_mem_support RestrictedProduct.mem_structureSubring_iff RestrictedProduct.not_mem_mulSupport RestrictedProduct.support_neg RestrictedProduct.mem_indexSupport_iff RestrictedProduct.mulSupport_inv RestrictedProduct.mapAlongLinearMap_apply RingEquiv.restrictedProductCongr_symm_apply RingEquiv.restrictedProductCongrRight_apply MulEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductProd_symm_apply_coe Equiv.restrictedProductCongrRight_apply AddEquiv.restrictedProductCongr_apply Equiv.restrictedProductCongrLeft'_symm_apply_apply Equiv.restrictedProductCongr_apply_apply Equiv.restrictedProductCongrLeft_apply_apply RestrictedProduct.flatten_equiv'_apply AddEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductCongr_symm_apply Equiv.restrictedProductCongrRight_symm_apply RestrictedProduct.flatten_equiv'_symm_apply AddEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductCongrLeft'_apply RestrictedProduct.flatten_apply RingEquiv.restrictedProductCongr_apply_apply RingEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductProd_apply RestrictedProduct.flatten_equiv_apply RestrictedProduct.flatten_equiv_symm_apply LinearEquiv.restrictedProductCongrLeft'_apply LanglandsTunnell.CubicInduction.diagonal3_coe LanglandsTunnell.CubicInduction.halfModulus3_one LanglandsTunnell.CubicInduction.torusChar3_one"

set_option autoImplicit false

open IsDedekindDomain NumberField AutomorphicForm LanglandsTunnell.RankinSelberg MeasureTheory LanglandsTunnell.TateLocal UnramifiedWhittaker LanglandsTunnell.CubicInduction

open scoped nonZeroDivisors

open MeasureTheory IsDedekindDomain NumberField AutomorphicForm UnramifiedWhittaker
open scoped ENNReal NNReal

noncomputable section

namespace Ws31J3pGauge

section Density

variable {G : Type*} [Group G] [TopologicalSpace G] [MeasurableSpace G]

theorem measurable_weight [BorelSpace G] (H : Subgroup G) (μH : Measure H) :
    Measurable (HaarQuotient.weight H μH) := by
  unfold HaarQuotient.weight
  split_ifs with h
  · exact Measurable.tsum fun n =>
      (measurable_const.mul measurable_const).mul
        (measurable_const.indicator isOpen_interior.measurableSet)
  · exact measurable_const

theorem measurable_density [IsTopologicalGroup G] [SecondCountableTopology G] [BorelSpace G]
    (H : Subgroup G) (μH : Measure H) [SFinite μH] :
    Measurable (HaarQuotient.density H μH) := by
  have hw := measurable_weight H μH
  have h2 : Measurable fun z : G × H => HaarQuotient.weight H μH ((z.2 : G) * z.1) :=
    hw.comp ((continuous_subtype_val.comp continuous_snd).mul continuous_fst).measurable
  unfold HaarQuotient.density
  exact hw.div h2.lintegral_prod_right'

theorem integrable_withDensity_of_lintegral_lt_top [IsTopologicalGroup G] [SecondCountableTopology G]
    [BorelSpace G] {E : Type*} [NormedAddCommGroup E] [MeasurableSpace E] [BorelSpace E]
    [SecondCountableTopology E]
    (μ : Measure G) (H : Subgroup G) (μH : Measure H) [SFinite μH]
    (Φ : G → E) (hΦ : Measurable Φ)
    (hfin : ∫⁻ g, (‖Φ g‖ₑ) * HaarQuotient.density H μH g ∂μ < ∞) :
    Integrable Φ (μ.withDensity (HaarQuotient.density H μH)) := by
  have hD := measurable_density H μH
  refine ⟨(hΦ.aestronglyMeasurable).mono_ac (withDensity_absolutelyContinuous μ _), ?_⟩
  rw [HasFiniteIntegral, lintegral_withDensity_eq_lintegral_mul₀ hD.aemeasurable hΦ.enorm.aemeasurable]
  calc ∫⁻ g, (HaarQuotient.density H μH * fun g => ‖Φ g‖ₑ) g ∂μ
      = ∫⁻ g, ‖Φ g‖ₑ * HaarQuotient.density H μH g ∂μ := by
        refine lintegral_congr fun g => ?_
        rw [Pi.mul_apply, mul_comm]
    _ < ∞ := hfin

end Density

section LocalField

variable (v : HeightOneSpectrum (𝓞 ℚ))

local notation "F" => (HeightOneSpectrum.adicCompletion ℚ v)
local notation "O" => (HeightOneSpectrum.adicCompletionIntegers ℚ v)

def qR : ℝ := ((Ideal.absNorm v.asIdeal : ℝ≥0) : ℝ)

theorem one_lt_qR : 1 < qR v := by
  have := NumberField.HeightOneSpectrum.one_lt_absNorm_nnreal v
  rw [qR]; exact_mod_cast this

theorem qR_pos : 0 < qR v := zero_lt_one.trans (one_lt_qR v)

theorem qR_ne_zero : qR v ≠ 0 := (qR_pos v).ne'

theorem norm_le_one_iff (x : F) : ‖x‖ ≤ 1 ↔ Valued.v x ≤ 1 := by
  rw [NumberField.FinitePlace.norm_def, ← NNReal.coe_one, NNReal.coe_le_coe]
  exact WithZeroMulInt.toNNReal_le_one_iff (NumberField.HeightOneSpectrum.one_lt_absNorm_nnreal v)

theorem norm_eq_one_iff (x : F) : ‖x‖ = 1 ↔ Valued.v x = 1 := by
  rw [NumberField.FinitePlace.norm_def, ← NNReal.coe_one, NNReal.coe_inj]
  exact WithZeroMulInt.toNNReal_eq_one_iff _ (NumberField.HeightOneSpectrum.absNorm_ne_zero v)
    (NumberField.HeightOneSpectrum.one_lt_absNorm_nnreal v).ne'

theorem norm_eq_zpow_of_v_eq_exp (x : F) (m : ℤ) (hx : Valued.v x = WithZero.exp m) : ‖x‖ = qR v ^ m := by
  rw [NumberField.FinitePlace.norm_def, hx, WithZeroMulInt.toNNReal_neg_apply _ WithZero.exp_ne_zero,
    NNReal.coe_zpow, qR]
  congr 1

theorem coe_modulus_eq_norm (x : F) : ((LanglandsTunnell.TateLocal.modulus x : ℝ≥0) : ℝ) = ‖x‖ := by
  rw [LanglandsTunnell.TateLocal.modulus_adicCompletion_eq_nnnorm ℚ v x, coe_nnnorm]

variable {v}

theorem uniformizer_ne_zero {ϖ : F} (hϖ : Valued.v ϖ = WithZero.exp (-1 : ℤ)) : ϖ ≠ 0 := by
  intro h
  rw [h, map_zero] at hϖ
  exact WithZero.exp_ne_zero hϖ.symm

theorem v_uniformizer_zpow {ϖ : F} (hϖ : Valued.v ϖ = WithZero.exp (-1 : ℤ)) (k : ℤ) :
    Valued.v (ϖ ^ k) = WithZero.exp (-k) := by
  rw [map_zpow₀, hϖ, ← WithZero.exp_zsmul, smul_neg, zsmul_one, Int.cast_id]

theorem norm_uniformizer_zpow {ϖ : F} (hϖ : Valued.v ϖ = WithZero.exp (-1 : ℤ)) (k : ℤ) :
    ‖ϖ ^ k‖ = qR v ^ (-k) :=
  norm_eq_zpow_of_v_eq_exp v _ _ (v_uniformizer_zpow hϖ k)

end LocalField

section Kzero

variable (v : HeightOneSpectrum (𝓞 ℚ))

local notation "F" => (HeightOneSpectrum.adicCompletion ℚ v)
local notation "O" => (HeightOneSpectrum.adicCompletionIntegers ℚ v)
local notation "G" => (GL (Fin 2) (HeightOneSpectrum.adicCompletion ℚ v))
local notation "Mat" => (Matrix (Fin 2) (Fin 2) (HeightOneSpectrum.adicCompletion ℚ v))

abbrev kzero : Subgroup G := AdelicDock.localLevelOne (𝓞 ℚ) ℚ v ⊤

theorem isLocalLevelOne_top_of_integral {m : Mat} (h : ∀ i j, m i j ∈ (O)) :
    AdelicDock.IsLocalLevelOne (𝓞 ℚ) ℚ v ⊤ m := by
  refine ⟨h, ?_, ?_⟩
  · rw [AdelicLevel.idealBound_top]
    exact (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).mp (h 1 0)
  · rw [AdelicLevel.idealBound_top]
    calc Valued.v (m 1 1 - 1) ≤ max (Valued.v (m 1 1)) (Valued.v (1 : F)) := Valuation.map_sub _ _ _
      _ ≤ 1 := max_le ((HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).mp (h 1 1)) (by simp)

theorem mem_kzero_iff (k : G) :
    k ∈ kzero v ↔ (∀ i j, (k : Mat) i j ∈ (O)) ∧ ∀ i j, ((k⁻¹ : G) : Mat) i j ∈ (O) := by
  rw [AdelicDock.mem_localLevelOne_iff]
  constructor
  · rintro ⟨h1, h2⟩; exact ⟨h1.integral, h2.integral⟩
  · rintro ⟨h1, h2⟩
    exact ⟨isLocalLevelOne_top_of_integral v h1, isLocalLevelOne_top_of_integral v h2⟩

theorem coe_kzero_eq_localIntegralSet : ((kzero v : Subgroup G) : Set G) = localIntegralSet ℚ v := by
  ext k
  rw [SetLike.mem_coe, mem_kzero_iff, mem_localIntegralSet]

theorem isOpen_kzero : IsOpen ((kzero v : Subgroup G) : Set G) := by
  rw [coe_kzero_eq_localIntegralSet]; exact isOpen_localIntegralSet ℚ v

theorem isCompact_kzero : IsCompact ((kzero v : Subgroup G) : Set G) := by
  rw [coe_kzero_eq_localIntegralSet]; exact isCompact_localIntegralSet ℚ v

variable {v}

theorem v_entry_le_one {k : G} (hk : k ∈ kzero v) (i j : Fin 2) : Valued.v ((k : Mat) i j) ≤ 1 :=
  (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).mp (((mem_kzero_iff v k).mp hk).1 i j)

theorem norm_entry_le_one {k : G} (hk : k ∈ kzero v) (i j : Fin 2) : ‖(k : Mat) i j‖ ≤ 1 :=
  (norm_le_one_iff v _).mpr (v_entry_le_one hk i j)

theorem v_det_le_one_of_integral {m : Mat} (h : ∀ i j, Valued.v (m i j) ≤ 1) : Valued.v m.det ≤ 1 := by
  rw [Matrix.det_fin_two]
  calc Valued.v (m 0 0 * m 1 1 - m 0 1 * m 1 0)
      ≤ max (Valued.v (m 0 0 * m 1 1)) (Valued.v (m 0 1 * m 1 0)) := Valuation.map_sub _ _ _
    _ ≤ 1 := by
        refine max_le ?_ ?_
        · rw [map_mul]; exact mul_le_one' (h 0 0) (h 1 1)
        · rw [map_mul]; exact mul_le_one' (h 0 1) (h 1 0)

theorem v_det_eq_one {k : G} (hk : k ∈ kzero v) : Valued.v (k : Mat).det = 1 := by
  have h1 : Valued.v (k : Mat).det ≤ 1 := v_det_le_one_of_integral (v_entry_le_one hk)
  have h2 : Valued.v ((k⁻¹ : G) : Mat).det ≤ 1 := v_det_le_one_of_integral (v_entry_le_one (inv_mem hk))
  have hprod : Valued.v (k : Mat).det * Valued.v ((k⁻¹ : G) : Mat).det = 1 := by
    rw [← map_mul, ← Matrix.det_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.det_one, map_one]
  refine le_antisymm h1 ?_
  calc (1 : WithZero (Multiplicative ℤ)) = Valued.v (k : Mat).det * Valued.v ((k⁻¹ : G) : Mat).det := hprod.symm
    _ ≤ Valued.v (k : Mat).det * 1 := by gcongr
    _ = Valued.v (k : Mat).det := mul_one _

theorem norm_det_eq_one {k : G} (hk : k ∈ kzero v) : ‖(k : Mat).det‖ = 1 :=
  (norm_eq_one_iff v _).mpr (v_det_eq_one hk)

theorem max_norm_bottom_row_eq_one {k : G} (hk : k ∈ kzero v) :
    max ‖(k : Mat) 1 0‖ ‖(k : Mat) 1 1‖ = 1 := by
  have hle := v_entry_le_one hk

  have hdet : (1 : WithZero (Multiplicative ℤ)) ≤ max (Valued.v ((k : Mat) 1 0)) (Valued.v ((k : Mat) 1 1)) := by
    rw [← v_det_eq_one hk, Matrix.det_fin_two]
    calc Valued.v ((k : Mat) 0 0 * (k : Mat) 1 1 - (k : Mat) 0 1 * (k : Mat) 1 0)
        ≤ max (Valued.v ((k : Mat) 0 0 * (k : Mat) 1 1)) (Valued.v ((k : Mat) 0 1 * (k : Mat) 1 0)) :=
          Valuation.map_sub _ _ _
      _ ≤ max (Valued.v ((k : Mat) 1 1)) (Valued.v ((k : Mat) 1 0)) := by
          refine max_le_max ?_ ?_
          · rw [map_mul]; exact mul_le_of_le_one_left' (hle 0 0)
          · rw [map_mul]; exact mul_le_of_le_one_left' (hle 0 1)
      _ = max (Valued.v ((k : Mat) 1 0)) (Valued.v ((k : Mat) 1 1)) := max_comm _ _
  have hn0 : ‖(k : Mat) 1 0‖ ≤ 1 := norm_entry_le_one hk 1 0
  have hn1 : ‖(k : Mat) 1 1‖ ≤ 1 := norm_entry_le_one hk 1 1
  rcases le_max_iff.mp hdet with h | h
  · have h' : Valued.v ((k : Mat) 1 0) = 1 := le_antisymm (hle 1 0) h
    rw [(norm_eq_one_iff v _).mpr h']
    exact max_eq_left hn1
  · have h' : Valued.v ((k : Mat) 1 1) = 1 := le_antisymm (hle 1 1) h
    rw [(norm_eq_one_iff v _).mpr h']
    exact max_eq_right hn0

end Kzero

section Iota

open LanglandsTunnell.CubicInduction

variable {L : Type*} [NormedField L]

theorem lastRowSup_iotaGL (g : GL (Fin 2) L) : lastRowSup (iotaGL g) = 1 := by
  simp [lastRowSup, coe_iotaGL, embedMat2]

theorem minorSup_iotaGL (g : GL (Fin 2) L) :
    minorSup (iotaGL g) = max ‖(g : Matrix (Fin 2) (Fin 2) L) 1 0‖ ‖(g : Matrix (Fin 2) (Fin 2) L) 1 1‖ := by
  simp [minorSup, bottomMinor, coe_iotaGL, embedMat2]

theorem detSize_iotaGL (g : GL (Fin 2) L) : detSize (iotaGL g) = ‖(g : Matrix (Fin 2) (Fin 2) L).det‖ := by
  rw [detSize, coe_iotaGL]
  congr 1
  simp [embedMat2, Matrix.det_fin_three, Matrix.det_fin_two]

end Iota

section Torus

open LanglandsTunnell.CubicInduction

variable (v : HeightOneSpectrum (𝓞 ℚ))

local notation "F" => (HeightOneSpectrum.adicCompletion ℚ v)
local notation "O" => (HeightOneSpectrum.adicCompletionIntegers ℚ v)
local notation "G" => (GL (Fin 2) (HeightOneSpectrum.adicCompletion ℚ v))
local notation "Mat" => (Matrix (Fin 2) (Fin 2) (HeightOneSpectrum.adicCompletion ℚ v))

def diagU (a b : (HeightOneSpectrum.adicCompletion ℚ v)ˣ) : G where
  val := !![(a : F), 0; 0, (b : F)]
  inv := !![((a⁻¹ : (HeightOneSpectrum.adicCompletion ℚ v)ˣ) : F), 0;
    0, ((b⁻¹ : (HeightOneSpectrum.adicCompletion ℚ v)ˣ) : F)]
  val_inv := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
  inv_val := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

@[scoped simp] theorem coe_diagU (a b : (HeightOneSpectrum.adicCompletion ℚ v)ˣ) :
    ((diagU v a b : G) : Mat) = !![(a : F), 0; 0, (b : F)] := rfl

theorem diagU_inv (a b : (HeightOneSpectrum.adicCompletion ℚ v)ˣ) :
    (diagU v a b)⁻¹ = diagU v a⁻¹ b⁻¹ := by
  refine inv_eq_of_mul_eq_one_right (Units.ext ?_)
  change ((diagU v a b : G) : Mat) * ((diagU v a⁻¹ b⁻¹ : G) : Mat) = 1
  ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

theorem diagU_mul (a b a' b' : (HeightOneSpectrum.adicCompletion ℚ v)ˣ) :
    diagU v a b * diagU v a' b' = diagU v (a * a') (b * b') := by
  refine Units.ext ?_
  change ((diagU v a b : G) : Mat) * ((diagU v a' b' : G) : Mat) = ((diagU v (a * a') (b * b') : G) : Mat)
  ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

def diagUHom : (HeightOneSpectrum.adicCompletion ℚ v)ˣ × (HeightOneSpectrum.adicCompletion ℚ v)ˣ →* G where
  toFun p := diagU v p.1 p.2
  map_one' := by
    refine Units.ext ?_
    change ((diagU v 1 1 : G) : Mat) = 1
    rw [coe_diagU]
    ext i j; fin_cases i <;> fin_cases j <;> simp
  map_mul' p p' := (diagU_mul v p.1 p.2 p'.1 p'.2).symm

theorem diagU_zpow (a b : (HeightOneSpectrum.adicCompletion ℚ v)ˣ) (n : ℤ) :
    (diagU v a b) ^ n = diagU v (a ^ n) (b ^ n) := by
  change (diagUHom v (a, b)) ^ n = diagUHom v ((a, b) ^ n)
  rw [map_zpow]

variable {v}
variable {ϖ : HeightOneSpectrum.adicCompletionIntegers ℚ v}

def piUnit (hπ : algebraMap (O) (F) ϖ ≠ 0) : (HeightOneSpectrum.adicCompletion ℚ v)ˣ :=
  Units.mk0 (algebraMap (O) (F) ϖ) hπ

@[scoped simp] theorem coe_piUnit (hπ : algebraMap (O) (F) ϖ ≠ 0) : ((piUnit hπ : _ˣ) : F) = algebraMap (O) (F) ϖ := rfl

theorem coe_piUnit_zpow (hπ : algebraMap (O) (F) ϖ ≠ 0) (k : ℤ) :
    (((piUnit hπ) ^ k : _ˣ) : F) = (algebraMap (O) (F) ϖ) ^ k := by
  rw [Units.val_zpow_eq_zpow_val, coe_piUnit]

theorem scalarPi_eq_diagU (hπ : algebraMap (O) (F) ϖ ≠ 0) :
    scalarPi (algebraMap (O) (F) ϖ) hπ = diagU v (piUnit hπ) (piUnit hπ) := by
  refine Units.ext ?_
  rw [coe_diagU]
  simp [scalarPi, piUnit]

theorem diagZ_eq_diagU (hπ : algebraMap (O) (F) ϖ ≠ 0) (d : ℤ) :
    diagZ (algebraMap (O) (F) ϖ) hπ d = diagU v (piUnit hπ ^ d) 1 := by
  refine Units.ext ?_
  rw [coe_diagU]
  simp [diagZ, piUnit, Units.val_zpow_eq_zpow_val]

theorem shellRep_eq_diagU (hπ : algebraMap (O) (F) ϖ ≠ 0) (dn : ℤ × ℤ) :
    scalarPi (algebraMap (O) (F) ϖ) hπ ^ dn.2 * diagZ (algebraMap (O) (F) ϖ) hπ dn.1 =
      diagU v (piUnit hπ ^ (dn.2 + dn.1)) (piUnit hπ ^ dn.2) := by
  rw [scalarPi_eq_diagU hπ, diagZ_eq_diagU hπ, diagU_zpow, diagU_mul, zpow_add, mul_one]

theorem shellRep_eq_diagZ_mul (hπ : algebraMap (O) (F) ϖ ≠ 0) (dn : ℤ × ℤ) :
    scalarPi (algebraMap (O) (F) ϖ) hπ ^ dn.2 * diagZ (algebraMap (O) (F) ϖ) hπ dn.1 =
      diagZ (algebraMap (O) (F) ϖ) hπ dn.1 * scalarPi (algebraMap (O) (F) ϖ) hπ ^ dn.2 := by
  rw [scalarPi_eq_diagU hπ, diagZ_eq_diagU hπ, diagU_zpow, diagU_mul, diagU_mul, mul_one, one_mul, mul_comm]

theorem scalarPi_eq_scalar (hπ : algebraMap (O) (F) ϖ ≠ 0) :
    scalarPi (algebraMap (O) (F) ϖ) hπ = Matrix.GeneralLinearGroup.scalar (Fin 2) (piUnit hπ) := by
  refine Units.ext ?_
  ext i j
  fin_cases i <;> fin_cases j <;> simp [scalarPi, piUnit, Matrix.GeneralLinearGroup.scalar, Matrix.diagonal]

theorem scalarPi_zpow_eq_scalar (hπ : algebraMap (O) (F) ϖ ≠ 0) (n : ℤ) :
    scalarPi (algebraMap (O) (F) ϖ) hπ ^ n = Matrix.GeneralLinearGroup.scalar (Fin 2) (piUnit hπ ^ n) := by
  rw [scalarPi_eq_scalar hπ, map_zpow]

theorem shell_mul_apply_one (hπ : algebraMap (O) (F) ϖ ≠ 0) (dn : ℤ × ℤ) (k : G) (j : Fin 2) :
    ((scalarPi (algebraMap (O) (F) ϖ) hπ ^ dn.2 * diagZ (algebraMap (O) (F) ϖ) hπ dn.1 * k : G) : Mat) 1 j =
      (algebraMap (O) (F) ϖ) ^ dn.2 * (k : Mat) 1 j := by
  rw [shellRep_eq_diagU hπ, Units.val_mul, coe_diagU, Matrix.mul_apply, Fin.sum_univ_two, coe_piUnit_zpow]
  simp

theorem det_shell_mul (hπ : algebraMap (O) (F) ϖ ≠ 0) (dn : ℤ × ℤ) (k : G) :
    ((scalarPi (algebraMap (O) (F) ϖ) hπ ^ dn.2 * diagZ (algebraMap (O) (F) ϖ) hπ dn.1 * k : G) : Mat).det =
      (algebraMap (O) (F) ϖ) ^ (dn.2 + dn.1) * (algebraMap (O) (F) ϖ) ^ dn.2 * (k : Mat).det := by
  rw [shellRep_eq_diagU hπ, Units.val_mul, Matrix.det_mul, coe_diagU, Matrix.det_fin_two_of, coe_piUnit_zpow,
    coe_piUnit_zpow]
  ring

theorem minorSup_iotaGL_shell
    (hϖ : Valued.v (algebraMap (HeightOneSpectrum.adicCompletionIntegers ℚ v) (HeightOneSpectrum.adicCompletion ℚ v) ϖ) =
      WithZero.exp (-1 : ℤ))
    (hπ : algebraMap (O) (F) ϖ ≠ 0) (dn : ℤ × ℤ) {k : G} (hk : k ∈ kzero v) :
    minorSup (iotaGL (scalarPi (algebraMap (O) (F) ϖ) hπ ^ dn.2 * diagZ (algebraMap (O) (F) ϖ) hπ dn.1 * k)) =
      qR v ^ (-dn.2) := by
  rw [minorSup_iotaGL, shell_mul_apply_one hπ, shell_mul_apply_one hπ, norm_mul, norm_mul,
    ← mul_max_of_nonneg _ _ (norm_nonneg _), max_norm_bottom_row_eq_one hk, mul_one, norm_uniformizer_zpow hϖ]

theorem detSize_iotaGL_shell
    (hϖ : Valued.v (algebraMap (HeightOneSpectrum.adicCompletionIntegers ℚ v) (HeightOneSpectrum.adicCompletion ℚ v) ϖ) =
      WithZero.exp (-1 : ℤ))
    (hπ : algebraMap (O) (F) ϖ ≠ 0) (dn : ℤ × ℤ) {k : G} (hk : k ∈ kzero v) :
    detSize (iotaGL (scalarPi (algebraMap (O) (F) ϖ) hπ ^ dn.2 * diagZ (algebraMap (O) (F) ϖ) hπ dn.1 * k)) =
      qR v ^ (-(dn.2 + dn.1)) * qR v ^ (-dn.2) := by
  rw [detSize_iotaGL, det_shell_mul hπ, norm_mul, norm_mul, norm_det_eq_one hk, mul_one,
    norm_uniformizer_zpow hϖ, norm_uniformizer_zpow hϖ]

theorem rootOne_shell
    (hϖ : Valued.v (algebraMap (HeightOneSpectrum.adicCompletionIntegers ℚ v) (HeightOneSpectrum.adicCompletion ℚ v) ϖ) =
      WithZero.exp (-1 : ℤ))
    (hπ : algebraMap (O) (F) ϖ ≠ 0) (dn : ℤ × ℤ) {k : G} (hk : k ∈ kzero v) :
    detSize (iotaGL (scalarPi (algebraMap (O) (F) ϖ) hπ ^ dn.2 * diagZ (algebraMap (O) (F) ϖ) hπ dn.1 * k)) *
        lastRowSup (iotaGL (scalarPi (algebraMap (O) (F) ϖ) hπ ^ dn.2 * diagZ (algebraMap (O) (F) ϖ) hπ dn.1 * k)) /
        minorSup (iotaGL (scalarPi (algebraMap (O) (F) ϖ) hπ ^ dn.2 * diagZ (algebraMap (O) (F) ϖ) hπ dn.1 * k)) ^ 2 =
      qR v ^ (-dn.1) := by
  rw [detSize_iotaGL_shell hϖ hπ dn hk, lastRowSup_iotaGL, minorSup_iotaGL_shell hϖ hπ dn hk, mul_one]
  have hq := qR_ne_zero v
  rw [div_eq_iff (pow_ne_zero _ (zpow_ne_zero _ hq)), ← zpow_natCast, ← zpow_mul, ← zpow_add₀ hq, ← zpow_add₀ hq]
  congr 1
  push_cast
  ring

theorem rootTwo_shell
    (hϖ : Valued.v (algebraMap (HeightOneSpectrum.adicCompletionIntegers ℚ v) (HeightOneSpectrum.adicCompletion ℚ v) ϖ) =
      WithZero.exp (-1 : ℤ))
    (hπ : algebraMap (O) (F) ϖ ≠ 0) (dn : ℤ × ℤ) {k : G} (hk : k ∈ kzero v) :
    minorSup (iotaGL (scalarPi (algebraMap (O) (F) ϖ) hπ ^ dn.2 * diagZ (algebraMap (O) (F) ϖ) hπ dn.1 * k)) /
        lastRowSup (iotaGL (scalarPi (algebraMap (O) (F) ϖ) hπ ^ dn.2 * diagZ (algebraMap (O) (F) ϖ) hπ dn.1 * k)) ^ 2 =
      qR v ^ (-dn.2) := by
  rw [minorSup_iotaGL_shell hϖ hπ dn hk, lastRowSup_iotaGL, one_pow, div_one]

theorem coe_modulus_det_shell
    (hϖ : Valued.v (algebraMap (HeightOneSpectrum.adicCompletionIntegers ℚ v) (HeightOneSpectrum.adicCompletion ℚ v) ϖ) =
      WithZero.exp (-1 : ℤ))
    (hπ : algebraMap (O) (F) ϖ ≠ 0) (dn : ℤ × ℤ) {k : G} (hk : k ∈ kzero v) :
    ((LanglandsTunnell.TateLocal.modulus
        ((Matrix.GeneralLinearGroup.det
            (scalarPi (algebraMap (O) (F) ϖ) hπ ^ dn.2 * diagZ (algebraMap (O) (F) ϖ) hπ dn.1 * k) :
              (HeightOneSpectrum.adicCompletion ℚ v)ˣ) : F) : ℝ≥0) : ℝ) =
      qR v ^ (-(2 * dn.2 + dn.1)) := by
  rw [coe_modulus_eq_norm, Matrix.GeneralLinearGroup.val_det_apply, det_shell_mul hπ, norm_mul, norm_mul,
    norm_det_eq_one hk, mul_one, norm_uniformizer_zpow hϖ, norm_uniformizer_zpow hϖ, ← zpow_add₀ (qR_ne_zero v)]
  congr 1
  ring

end Torus

section RealBounds

variable (v : HeightOneSpectrum (𝓞 ℚ))

theorem qR_eq_natCast : qR v = (Ideal.absNorm v.asIdeal : ℝ) := NNReal.coe_natCast _

theorem one_le_qR : 1 ≤ qR v := (one_lt_qR v).le

theorem exists_cutoff (B : ℝ) : ∃ m₀ : ℤ, m₀ ≤ 0 ∧ ∀ d : ℤ, qR v ^ (-d) ≤ B → m₀ ≤ d := by
  obtain ⟨j, hj⟩ := pow_unbounded_of_one_lt B (one_lt_qR v)
  refine ⟨-(j : ℤ), by omega, fun d hd => ?_⟩
  by_contra hlt
  have hlt : d < -(j : ℤ) := lt_of_not_ge hlt
  have h1 : qR v ^ (j : ℤ) ≤ qR v ^ (-d) := zpow_le_zpow_right₀ (one_le_qR v) (by omega)
  rw [zpow_natCast] at h1
  linarith

theorem summable_indicator_zpow {r : ℝ} (hr0 : 0 < r) (hr1 : r < 1) (m₀ : ℤ) :
    Summable fun d : ℤ => if m₀ ≤ d then r ^ d else 0 := by
  set f : ℤ → ℝ := fun d => if m₀ ≤ d then r ^ d else 0 with hf
  have hinj : Function.Injective fun j : ℕ => m₀ + (j : ℤ) := fun a b h => by
    simpa using h
  have hzero : ∀ x ∉ Set.range (fun j : ℕ => m₀ + (j : ℤ)), f x = 0 := by
    intro x hx
    have hlt : ¬ m₀ ≤ x := fun hle => hx ⟨(x - m₀).toNat, by simp; omega⟩
    simp [hf, hlt]
  rw [← hinj.summable_iff hzero]
  have hcomp : (f ∘ fun j : ℕ => m₀ + (j : ℤ)) = fun j : ℕ => r ^ m₀ * r ^ j := by
    funext j
    simp only [Function.comp_apply, hf]
    rw [if_pos (by omega), zpow_add₀ hr0.ne', zpow_natCast]
  rw [hcomp]
  exact (summable_geometric_of_lt_one hr0.le hr1).mul_left _

theorem indicator_zpow_nonneg {r : ℝ} (hr0 : 0 < r) (m₀ d : ℤ) : 0 ≤ (if m₀ ≤ d then r ^ d else 0) := by
  split_ifs
  · exact (zpow_pos hr0 _).le
  · exact le_rfl

end RealBounds

section GaugeBound

open LanglandsTunnell.CubicInduction

variable {v : HeightOneSpectrum (𝓞 ℚ)}

local notation "F" => (HeightOneSpectrum.adicCompletion ℚ v)
local notation "O" => (HeightOneSpectrum.adicCompletionIntegers ℚ v)
local notation "G" => (GL (Fin 2) (HeightOneSpectrum.adicCompletion ℚ v))

variable {ϖ : HeightOneSpectrum.adicCompletionIntegers ℚ v}

theorem gauge_shell
    (hϖ : Valued.v (algebraMap (HeightOneSpectrum.adicCompletionIntegers ℚ v) (HeightOneSpectrum.adicCompletion ℚ v) ϖ) =
      WithZero.exp (-1 : ℤ))
    (hπ : algebraMap (O) (F) ϖ ≠ 0) {W' : LocalGL3 v → ℂ} {B : ℝ} {t : ℕ} {C : ℝ}
    (hg : ∀ h : LocalGL3 v,
      (¬ (detSize h * lastRowSup h / minorSup h ^ 2 ≤ B ∧ minorSup h / lastRowSup h ^ 2 ≤ B) → W' h = 0) ∧
      (detSize h * lastRowSup h / minorSup h ^ 2 ≤ B ∧ minorSup h / lastRowSup h ^ 2 ≤ B →
        ‖W' h‖ ≤ C / ((detSize h * lastRowSup h / minorSup h ^ 2) * (minorSup h / lastRowSup h ^ 2)) ^ t))
    {m₀ : ℤ} (hm₀ : ∀ d : ℤ, qR v ^ (-d) ≤ B → m₀ ≤ d) (dn : ℤ × ℤ) {k : G} (hk : k ∈ kzero v) :
    (¬ (m₀ ≤ dn.1 ∧ m₀ ≤ dn.2) →
        W' (iotaGL (scalarPi (algebraMap (O) (F) ϖ) hπ ^ dn.2 * diagZ (algebraMap (O) (F) ϖ) hπ dn.1 * k)) = 0) ∧
      ‖W' (iotaGL (scalarPi (algebraMap (O) (F) ϖ) hπ ^ dn.2 * diagZ (algebraMap (O) (F) ϖ) hπ dn.1 * k))‖ ≤
        |C| * qR v ^ ((t : ℤ) * (dn.1 + dn.2)) := by
  have hq := qR_ne_zero v
  obtain ⟨hvan, hbd⟩ := hg (iotaGL (scalarPi (algebraMap (O) (F) ϖ) hπ ^ dn.2 * diagZ (algebraMap (O) (F) ϖ) hπ dn.1 * k))
  rw [rootOne_shell hϖ hπ dn hk, rootTwo_shell hϖ hπ dn hk] at hvan hbd
  have hpow : qR v ^ (-dn.1) * qR v ^ (-dn.2) = qR v ^ (-(dn.1 + dn.2)) := by
    rw [← zpow_add₀ hq]; congr 1; ring
  refine ⟨fun hmn => hvan fun hB => hmn ⟨hm₀ _ hB.1, hm₀ _ hB.2⟩, ?_⟩
  have hnn : 0 ≤ |C| * qR v ^ ((t : ℤ) * (dn.1 + dn.2)) := mul_nonneg (abs_nonneg C) (zpow_nonneg (qR_pos v).le _)
  by_cases hB : qR v ^ (-dn.1) ≤ B ∧ qR v ^ (-dn.2) ≤ B
  · calc ‖W' (iotaGL (scalarPi (algebraMap (O) (F) ϖ) hπ ^ dn.2 * diagZ (algebraMap (O) (F) ϖ) hπ dn.1 * k))‖
        ≤ C / (qR v ^ (-dn.1) * qR v ^ (-dn.2)) ^ t := hbd hB
      _ = C * qR v ^ ((t : ℤ) * (dn.1 + dn.2)) := by
          rw [hpow, ← zpow_natCast, ← zpow_mul, div_eq_mul_inv, ← zpow_neg]
          congr 2; ring
      _ ≤ |C| * qR v ^ ((t : ℤ) * (dn.1 + dn.2)) :=
          mul_le_mul_of_nonneg_right (le_abs_self C) (zpow_nonneg (qR_pos v).le _)
  · rw [hvan hB, norm_zero]
    exact hnn

end GaugeBound

end Ws31J3pGauge
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_forall_exists_rational_rsLocalIntegral_translate_of_shellRecurrence_of_centralChar_of_rationalTorusShell_of_gauge.Ws31J3pGauge"

end
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_forall_exists_rational_rsLocalIntegral_translate_of_shellRecurrence_of_centralChar_of_rationalTorusShell_of_gauge.Ws31J3pGauge"

open MeasureTheory IsDedekindDomain NumberField AutomorphicForm UnramifiedWhittaker LanglandsTunnell.TateLocal LanglandsTunnell.CubicInduction

open scoped Topology

namespace Ws31J3pPair

noncomputable section

variable (K : Type) [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))

local notation "F" => (HeightOneSpectrum.adicCompletion K v)
local notation "O" => (HeightOneSpectrum.adicCompletionIntegers K v)
local notation "G₂" => (GL (Fin 2) (HeightOneSpectrum.adicCompletion K v))
local notation "G₃" => (GL (Fin 3) (HeightOneSpectrum.adicCompletion K v))
local notation "Mat" => (Matrix (Fin 2) (Fin 2) (HeightOneSpectrum.adicCompletion K v))

theorem idealBound_pow (b : ℕ) :
    AdelicLevel.idealBound (𝓞 K) (v.asIdeal ^ b) v = WithZero.exp (-(b : ℤ)) := by
  classical
  have hne : v.asIdeal ^ b ≠ ⊥ := pow_ne_zero _ v.ne_bot
  rw [AdelicLevel.idealBound_of_ne_bot hne, Associates.mk_pow,
    Associates.count_pow (Associates.mk_ne_zero.mpr v.ne_bot) v.associates_irreducible,
    Associates.count_self v.associates_irreducible, mul_one]

theorem localLevelOne_pow_le (b : ℕ) :
    AdelicDock.localLevelOne (𝓞 K) K v (v.asIdeal ^ b) ≤ AdelicDock.localLevelOne (𝓞 K) K v ⊤ := by
  intro k hk
  rw [AdelicDock.mem_localLevelOne_iff] at hk ⊢
  have key : ∀ m : Mat, AdelicDock.IsLocalLevelOne (𝓞 K) K v (v.asIdeal ^ b) m →
      AdelicDock.IsLocalLevelOne (𝓞 K) K v ⊤ m := by
    intro m hm
    refine ⟨hm.integral, ?_, ?_⟩
    · rw [AdelicLevel.idealBound_top]
      exact hm.lowerLeft.trans (AdelicLevel.idealBound_le_one _ _)
    · rw [AdelicLevel.idealBound_top]
      exact hm.lowerRight.trans (AdelicLevel.idealBound_le_one _ _)
  exact ⟨key _ hk.1, key _ hk.2⟩

theorem mem_localLevelOne_pow_of_cong (b : ℕ) (k : G₂) (hk : k ∈ AdelicDock.localLevelOne (𝓞 K) K v ⊤)
    (hc : ∀ i j : Fin 2, Valued.v (((k : Mat) - 1) i j) ≤ WithZero.exp (-(b : ℤ))) :
    k ∈ AdelicDock.localLevelOne (𝓞 K) K v (v.asIdeal ^ b) := by
  rw [AdelicDock.mem_localLevelOne_iff] at hk ⊢
  obtain ⟨hk1, hk2⟩ := hk
  have hint := fun i j => (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).mp (hk1.integral i j)
  have hiint := fun i j => (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).mp (hk2.integral i j)

  have hc' : ∀ i j : Fin 2, Valued.v ((((k⁻¹ : G₂) : Mat) - 1) i j) ≤ WithZero.exp (-(b : ℤ)) := by
    intro i j
    have hexp : ((k⁻¹ : G₂) : Mat) - 1 = -(((k⁻¹ : G₂) : Mat) * ((k : Mat) - 1)) := by
      rw [Matrix.mul_sub, Matrix.mul_one, ← Units.val_mul, inv_mul_cancel, Units.val_one]
      abel
    rw [hexp]
    simp only [Matrix.neg_apply, Valuation.map_neg, Matrix.mul_apply, Fin.sum_univ_two]
    have hterm : ∀ l, Valued.v (((k⁻¹ : G₂) : Mat) i l * ((k : Mat) - 1) l j) ≤ WithZero.exp (-(b : ℤ)) := by
      intro l
      rw [map_mul]
      calc Valued.v (((k⁻¹ : G₂) : Mat) i l) * Valued.v (((k : Mat) - 1) l j)
          ≤ 1 * WithZero.exp (-(b : ℤ)) := by
            gcongr
            · exact hiint i l
            · exact hc l j
        _ = WithZero.exp (-(b : ℤ)) := one_mul _
    exact (Valuation.map_add _ _ _).trans (max_le (hterm 0) (hterm 1))
  have key : ∀ m : Mat, (∀ i j, m i j ∈ (O)) → (∀ i j : Fin 2, Valued.v ((m - 1) i j) ≤ WithZero.exp (-(b : ℤ))) →
      AdelicDock.IsLocalLevelOne (𝓞 K) K v (v.asIdeal ^ b) m := by
    intro m hm hmc
    refine ⟨hm, ?_, ?_⟩
    · rw [idealBound_pow]
      have := hmc 1 0
      simpa [Matrix.sub_apply, Matrix.one_apply] using this
    · rw [idealBound_pow]
      have := hmc 1 1
      simpa [Matrix.sub_apply, Matrix.one_apply] using this
  exact ⟨key _ hk1.integral hc, key _ hk2.integral hc'⟩

theorem continuous_iotaGL : Continuous (iotaGL : G₂ → G₃) := by
  have hemb : ∀ (f : G₂ → Mat), Continuous f → Continuous fun h => (embedMat2 (f h) : Matrix (Fin 3) (Fin 3) F) := by
    intro f hf
    refine continuous_matrix fun i j => ?_
    fin_cases i <;> fin_cases j <;>
      simp [embedMat2] <;> first
        | exact hf.matrix_elem _ _
        | exact continuous_const
  refine Units.continuous_iff.mpr ⟨?_, ?_⟩
  · exact hemb _ Units.continuous_val
  · change Continuous fun h : G₂ => (embedMat2 ((h⁻¹ : G₂) : Mat) : Matrix (Fin 3) (Fin 3) F)
    exact hemb _ Units.continuous_coe_inv

variable {K v}

theorem smooth_A {W₃ : G₃ → ℂ}
    (hW₃sm : ∃ Uv : Subgroup G₃, IsOpen (Uv : Set G₃) ∧ ∀ k ∈ Uv, ∀ g : G₃, W₃ (g * k) = W₃ g) (g₃ : G₃) :
    ∃ U : Subgroup G₂, IsOpen (U : Set G₂) ∧ ∀ k ∈ U, ∀ g : G₂, W₃ (iotaGL (g * k) * g₃) = W₃ (iotaGL g * g₃) := by
  obtain ⟨Uv, hUv, hinv⟩ := hW₃sm

  let φ : G₂ →* G₃ := (MulAut.conj g₃⁻¹).toMonoidHom.comp iotaGL
  refine ⟨Uv.comap φ, ?_, ?_⟩
  · have hφ : Continuous φ := by
      change Continuous fun h : G₂ => g₃⁻¹ * iotaGL h * g₃⁻¹⁻¹
      exact (continuous_const.mul (continuous_iotaGL K v)).mul continuous_const
    exact hUv.preimage hφ
  · intro k hk g
    have hk' : g₃⁻¹ * iotaGL k * g₃ ∈ Uv := by
      have := hk
      rw [Subgroup.mem_comap] at this
      simpa [φ] using this
    have : iotaGL (g * k) * g₃ = iotaGL g * g₃ * (g₃⁻¹ * iotaGL k * g₃) := by
      rw [map_mul]; group
    rw [this, hinv _ hk']

theorem iotaGL_unipotent (x : F) : iotaGL (unipotent x : G₂) = (upperUnipotent3 x 0 0 : G₃) := by
  have : (unipotent x : G₂) = AutomorphicForm.unipotentGL2 x := by
    refine Units.ext ?_
    simp [unipotent, unipotentGL2_coe]
  rw [this, iotaGL_unipotentGL2]

theorem prod_unipotent {θ : AddChar F ℂ} {W₃ : G₃ → ℂ} (hW₃law : IsGL3PsiWhittakerFn θ⁻¹ W₃) (g₃ : G₃)
    {w₂ : G₂ → ℂ} (hw₂law : ∀ (x : F) (g : G₂), w₂ (unipotent x * g) = θ x * w₂ g) (x : F) (g : G₂) :
    W₃ (iotaGL (unipotent x * g) * g₃) * w₂ (unipotent x * g) = W₃ (iotaGL g * g₃) * w₂ g := by
  rw [map_mul, iotaGL_unipotent, mul_assoc, hW₃law x 0 0, hw₂law, add_zero, AddChar.inv_apply]
  have h1 : θ (-x) * θ x = 1 := by rw [← AddChar.map_add_eq_mul, neg_add_cancel, AddChar.map_zero_eq_one]
  calc θ (-x) * W₃ (iotaGL g * g₃) * (θ x * w₂ g) = (θ (-x) * θ x) * (W₃ (iotaGL g * g₃) * w₂ g) := by ring
    _ = W₃ (iotaGL g * g₃) * w₂ g := by rw [h1, one_mul]

end
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_forall_exists_rational_rsLocalIntegral_translate_of_shellRecurrence_of_centralChar_of_rationalTorusShell_of_gauge.Ws31J3pGauge"

end Ws31J3pPair
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_forall_exists_rational_rsLocalIntegral_translate_of_shellRecurrence_of_centralChar_of_rationalTorusShell_of_gauge.Ws31J3pGauge"

open MeasureTheory IsDedekindDomain NumberField AutomorphicForm UnramifiedWhittaker LanglandsTunnell.TateLocal LanglandsTunnell.CubicInduction LanglandsTunnell.RankinSelberg

open scoped nonZeroDivisors

theorem solution
    (p : HeightOneSpectrum (𝓞 ℚ))

    (W₃base : LocalGL3 p → ℂ)
    (hW₃law : IsGL3PsiWhittakerFn (NumberField.StandardAddChar.psiLocal ℚ p)⁻¹ W₃base)
    (hW₃sm : ∃ Uv : Subgroup (LocalGL3 p), IsOpen (Uv : Set (LocalGL3 p)) ∧
      ∀ k ∈ Uv, ∀ g : LocalGL3 p, W₃base (g * k) = W₃base g)

    (hWgauge : ∃ (B : ℝ) (t : ℕ) (C : ℝ), ∀ h : LocalGL3 p,
      (¬ (detSize h * lastRowSup h / minorSup h ^ 2 ≤ B ∧ minorSup h / lastRowSup h ^ 2 ≤ B) → W₃base h = 0) ∧
      (detSize h * lastRowSup h / minorSup h ^ 2 ≤ B ∧ minorSup h / lastRowSup h ^ 2 ≤ B →
        ‖W₃base h‖ ≤ C / ((detSize h * lastRowSup h / minorSup h ^ 2) * (minorSup h / lastRowSup h ^ 2)) ^ t))

    (b : ℕ)
    {ϖ : p.adicCompletionIntegers ℚ}
    (hπ : algebraMap (p.adicCompletionIntegers ℚ) (p.adicCompletion ℚ) ϖ ≠ 0)
    (hϖ : Valued.v (algebraMap (p.adicCompletionIntegers ℚ) (p.adicCompletion ℚ) ϖ) = WithZero.exp (-1 : ℤ))

    (hβrat :
      ∀ (g₃ : LocalGL3 p) (k₀ : GL (Fin 2) (p.adicCompletion ℚ)) (η : (p.adicCompletion ℚ)ˣ →* ℂˣ) (c : ℕ),
        LanglandsTunnell.TateLocal.HasConductorExponentAt ℚ p η c → c ≤ b →
        letI := localBorel ℚ p
        letI := localGLBorel ℚ p
        haveI := borelSpace_localGLBorel ℚ p
        ∀ (μ₂ : Measure (GL (Fin 2) (p.adicCompletion ℚ))) [μ₂.IsHaarMeasure],
          let A : ℤ × ℤ → ℂ := fun n =>
            ∫ u in {u : (p.adicCompletion ℚ)ˣ | Valued.v (u : p.adicCompletion ℚ) = 1},
              (∫ k in ((AdelicDock.localLevelOne (𝓞 ℚ) ℚ p (p.asIdeal ^ b) :
                    Subgroup (GL (Fin 2) (p.adicCompletion ℚ))) : Set (GL (Fin 2) (p.adicCompletion ℚ))),
                  W₃base (iotaGL (UnramifiedWhittaker.scalarPi
                        (algebraMap (p.adicCompletionIntegers ℚ) (p.adicCompletion ℚ) ϖ) hπ ^ n.2 *
                      diagUnitGL2 (Units.mk0 (algebraMap (p.adicCompletionIntegers ℚ) (p.adicCompletion ℚ) ϖ) hπ
                        ^ n.1 * u) * (k₀ * k)) * g₃) ∂μ₂) * ((η u : ℂˣ) : ℂ)
            ∂(Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ p)))
          let Ad : ℤ × ℤ → ℂ := fun n =>
            ∫ u in {u : (p.adicCompletion ℚ)ˣ | Valued.v (u : p.adicCompletion ℚ) = 1},
              (∫ k in ((AdelicDock.localLevelOne (𝓞 ℚ) ℚ p (p.asIdeal ^ b) :
                    Subgroup (GL (Fin 2) (p.adicCompletion ℚ))) : Set (GL (Fin 2) (p.adicCompletion ℚ))),
                  dualWhittakerFn3 (fun x => W₃base (x * g₃)) (iotaGL (UnramifiedWhittaker.scalarPi
                        (algebraMap (p.adicCompletionIntegers ℚ) (p.adicCompletion ℚ) ϖ) hπ ^ n.2 *
                      diagUnitGL2 (Units.mk0 (algebraMap (p.adicCompletionIntegers ℚ) (p.adicCompletion ℚ) ϖ) hπ
                        ^ n.1 * u) * (k₀ * AutomorphicForm.transposeInvN (Fin 2) k))) ∂μ₂) * ((η u : ℂˣ) : ℂ)
            ∂(Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ p)))
          (∃ (N₁ : ℤ) (D₁ D₂ : Polynomial ℂ) (M : ℕ), D₁.eval 0 ≠ 0 ∧ D₂.eval 0 ≠ 0 ∧
            (∀ n : ℤ × ℤ, (n.1 < N₁ ∨ n.2 < N₁) → A n = 0) ∧
            (∀ m₁ m₂ : ℕ, (M ≤ m₁ ∨ M ≤ m₂) →
              ∑ i ∈ Finset.range (D₁.natDegree + 1), ∑ l ∈ Finset.range (D₂.natDegree + 1),
                D₁.coeff i * D₂.coeff l * A (N₁ + (m₁ : ℤ) - (i : ℤ), N₁ + (m₂ : ℤ) - (l : ℤ)) = 0)) ∧
          (∃ (N₁ : ℤ) (D₁ D₂ : Polynomial ℂ) (M : ℕ), D₁.eval 0 ≠ 0 ∧ D₂.eval 0 ≠ 0 ∧
            (∀ n : ℤ × ℤ, (n.1 < N₁ ∨ n.2 < N₁) → Ad n = 0) ∧
            (∀ m₁ m₂ : ℕ, (M ≤ m₁ ∨ M ≤ m₂) →
              ∑ i ∈ Finset.range (D₁.natDegree + 1), ∑ l ∈ Finset.range (D₂.natDegree + 1),
                D₁.coeff i * D₂.coeff l * Ad (N₁ + (m₁ : ℤ) - (i : ℤ), N₁ + (m₂ : ℤ) - (l : ℤ)) = 0)))

    (w₂base : GL (Fin 2) (p.adicCompletion ℚ) → ℂ)
    (hw₂law : ∀ (x : p.adicCompletion ℚ) (g : GL (Fin 2) (p.adicCompletion ℚ)),
      w₂base (unipotent x * g) = NumberField.StandardAddChar.psiLocal ℚ p x * w₂base g)
    (hw₂K : ∀ k ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ p (p.asIdeal ^ b), ∀ g : GL (Fin 2) (p.adicCompletion ℚ),
      w₂base (g * k) = w₂base g)

    (ω : (p.adicCompletion ℚ)ˣ →* ℂˣ)
    (hcentral : ∀ (z : (p.adicCompletion ℚ)ˣ) (g : GL (Fin 2) (p.adicCompletion ℚ)),
      w₂base (Matrix.GeneralLinearGroup.scalar (Fin 2) z * g) = ((ω z : ℂˣ) : ℂ) * w₂base g)

    (hw₂gr : ∃ (C A : ℝ), ∀ (m : ℤ), 0 ≤ m → ∀ k ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ p ⊤,
      ‖w₂base (UnramifiedWhittaker.diagZ (algebraMap (p.adicCompletionIntegers ℚ) (p.adicCompletion ℚ) ϖ) hπ m * k)‖ ≤
        C * (Ideal.absNorm p.asIdeal : ℝ) ^ (A * m))

    (hw₂rec : ∃ (N₁ : ℤ) (D : Polynomial ℂ) (M : ℕ), D.eval 0 ≠ 0 ∧
      ∀ k ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ p ⊤,
        (∀ m : ℤ, m < N₁ →
          w₂base (UnramifiedWhittaker.diagZ (algebraMap (p.adicCompletionIntegers ℚ) (p.adicCompletion ℚ) ϖ) hπ m * k) = 0) ∧
        (∀ m : ℕ, M ≤ m →
          ∑ i ∈ Finset.range (D.natDegree + 1),
            D.coeff i *
              w₂base (UnramifiedWhittaker.diagZ (algebraMap (p.adicCompletionIntegers ℚ) (p.adicCompletion ℚ) ϖ) hπ
                (N₁ + (m : ℤ) - (i : ℤ)) * k) = 0)) :
    ∀ g₃ : LocalGL3 p,
      letI := localGLBorel ℚ p
      haveI := borelSpace_localGLBorel ℚ p
      ∀ (μ₂ : Measure (GL (Fin 2) (p.adicCompletion ℚ))) [μ₂.IsHaarMeasure]
          (μN₂ : Measure ↥(unipotentGL2Hom (R := p.adicCompletion ℚ)).range) [μN₂.IsHaarMeasure],
        ∃ (P Q : Polynomial ℂ) (m : ℤ) (σ₂ : ℝ), Q ≠ 0 ∧
          ∀ s : ℂ, σ₂ < s.re →
            Integrable (fun g : GL (Fin 2) (p.adicCompletion ℚ) =>
                (W₃base (iotaGL g * g₃) * w₂base g) * ((modulus ((Matrix.GeneralLinearGroup.det g : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) : ℝ) : ℂ) ^ (s - 1 / 2))
              (μ₂.withDensity (HaarQuotient.density (unipotentGL2Hom (R := p.adicCompletion ℚ)).range μN₂)) ∧
            RSCarrier.rsLocalIntegral μ₂ (unipotentGL2Hom (R := p.adicCompletion ℚ)).range μN₂
                (fun g : GL (Fin 2) (p.adicCompletion ℚ) => (modulus ((Matrix.GeneralLinearGroup.det g : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) : ℝ))
                s (fun g => W₃base (iotaGL g * g₃)) w₂base * Q.eval ((Ideal.absNorm p.asIdeal : ℂ) ^ (-s)) =
              (Ideal.absNorm p.asIdeal : ℂ) ^ ((m : ℂ) * s) * P.eval ((Ideal.absNorm p.asIdeal : ℂ) ^ (-s)) := by
  intro g₃ μ₂ _ μN₂ _
  have hopen := (AdelicDock.isCompact_and_isOpen_localLevelOne ℚ p (p.asIdeal ^ b) (pow_ne_zero _ p.ne_bot)).2

  have hW'mem : gl3AmbientRightTranslate (R := ℂ) g₃ W₃base ∈ gl3CyclicSubspace W₃base :=
    Submodule.subset_span ⟨g₃, rfl⟩
  obtain ⟨⟨Bg, t, C, hg⟩, -⟩ :=
    forall_mem_gl3CyclicSubspace_exists_gauge_and_exists_gauge_dualWhittakerFn3 W₃base hWgauge _ hW'mem
  obtain ⟨m₀, -, hm₀⟩ := Ws31J3pGauge.exists_cutoff p Bg
  have hAshell : ∃ (m₀ : ℤ) (t : ℕ) (CA : ℝ), ∀ (dn : ℤ × ℤ), ∀ k ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ p ⊤,
      (¬ (m₀ ≤ dn.1 ∧ m₀ ≤ dn.2) →
        W₃base (iotaGL (scalarPi (algebraMap (p.adicCompletionIntegers ℚ) (p.adicCompletion ℚ) ϖ) hπ ^ dn.2 *
            diagZ (algebraMap (p.adicCompletionIntegers ℚ) (p.adicCompletion ℚ) ϖ) hπ dn.1 * k) * g₃) = 0) ∧
      ‖W₃base (iotaGL (scalarPi (algebraMap (p.adicCompletionIntegers ℚ) (p.adicCompletion ℚ) ϖ) hπ ^ dn.2 *
            diagZ (algebraMap (p.adicCompletionIntegers ℚ) (p.adicCompletion ℚ) ϖ) hπ dn.1 * k) * g₃)‖ ≤
        CA * (Ideal.absNorm p.asIdeal : ℝ) ^ ((t : ℤ) * (dn.1 + dn.2)) := by
    refine ⟨m₀, t, |C|, fun dn k hk => ?_⟩
    have key := Ws31J3pGauge.gauge_shell hϖ hπ hg hm₀ dn hk
    rw [Ws31J3pGauge.qR_eq_natCast] at key
    exact key
  have hArat := fun k₀ (hk₀ : k₀ ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ p ⊤)
      (η : (p.adicCompletion ℚ)ˣ →* ℂˣ) (c : ℕ) (hη : HasConductorExponentAt ℚ p η c) (hc : c ≤ b) =>
    (hβrat g₃ k₀ η c hη hc)
  obtain ⟨P, Q, m, σ₂, hQ, h⟩ :=
    LanglandsTunnell.RankinSelberg.exists_rational_rsLocalIntegral_of_shellGauge_of_rationalTorusShell_of_shellRecurrence_of_central
      p hπ hϖ b (AdelicDock.localLevelOne (𝓞 ℚ) ℚ p (p.asIdeal ^ b)) hopen (Ws31J3pPair.localLevelOne_pow_le ℚ p b)
      (fun k hk hc => Ws31J3pPair.mem_localLevelOne_pow_of_cong ℚ p b k hk hc)
      (fun g => W₃base (iotaGL g * g₃)) w₂base (Ws31J3pPair.smooth_A hW₃sm g₃) hw₂K
      (Ws31J3pPair.prod_unipotent hW₃law g₃ hw₂law) hAshell
      (fun k₀ hk₀ η c hη hc μ => ((hArat k₀ hk₀ η c hη hc) μ).1)
      ω hcentral hw₂gr hw₂rec μ₂ μN₂
  exact ⟨P, Q, m, σ₂, hQ, h⟩

end S_LanglandsTunnell_RankinSelberg_forall_exists_rational_rsLocalIntegral_translate_of_shellRecurrence_of_centralChar_of_rationalTorusShell_of_gauge
end P2MW
export P2MW.S_LanglandsTunnell_RankinSelberg_forall_exists_rational_rsLocalIntegral_translate_of_shellRecurrence_of_centralChar_of_rationalTorusShell_of_gauge (solution)
