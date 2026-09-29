-- Prove2me | solution 1 for LanglandsTunnell.RankinSelberg.forall_exists_rational_rsLocalIntegral_dual_translate_of_shellRecurrence_of_centralChar_of_rationalTorusShell_of_gauge
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.670037+00:00
-- url     : https://prove2.me/submissions/0c4bec7e-3266-54b3-97f0-575afb550434

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
import Definitions.Def_AutomorphicForm_ConstantTerm
import Definitions.Def_LanglandsTunnell_CubicInduction_IotaTorus
import Definitions.Def_LanglandsTunnell_TateLocalConstantsAt
import Definitions.Def_LanglandsTunnell_TateLocalZeta
import Mathlib
import Theorems.Thm_LanglandsTunnell_RankinSelberg_exists_rational_rsLocalIntegral_of_shellGauge_of_rationalTorusShell_of_shellRecurrence_of_central
import Theorems.Thm_LanglandsTunnell_CubicInduction_forall_mem_gl3CyclicSubspace_exists_gauge_and_exists_gauge_dualWhittakerFn3
import Theorems.Thm_LanglandsTunnell_TateLocal_modulus_adicCompletion_eq_nnnorm
import Theorems.Thm_AdelicDock_isCompact_and_isOpen_localLevelOne
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LanglandsTunnell_RankinSelberg_forall_exists_rational_rsLocalIntegral_dual_translate_of_shellRecurrence_of_centralChar_of_rationalTorusShell_of_gauge
p2m_attr_erase "instance" "instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions instCountableOfNumberField_definitions FLT.InfiniteAdeleBaseChange.uniqueSelfExtension NumberField.InfinitePlace.RamifiedExtension.instCoeExtension NumberField.InfinitePlace.UnramifiedExtension.instCoeExtension IsDedekindDomain.HeightOneSpectrum.Extension.instAlgebraSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnder IsDedekindDomain.HeightOneSpectrum.Extension.instAlgebraSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnder_1 IsDedekindDomain.HeightOneSpectrum.instMulActionHomClassAlgHomTensorProductAdicCompletionForallValEqUnder_definitions IsDedekindDomain.HeightOneSpectrum.Extension.instAlgebraAdicCompletionValEqUnder IsDedekindDomain.HeightOneSpectrum.adicCompletion.instFiniteForallValEqUnderOfFiniteDimensional_definitions IsDedekindDomain.HeightOneSpectrum.instIsBiscalarSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersTensorProductCoeAlgHomTensorAdicCompletionIntegersTo IsDedekindDomain.HeightOneSpectrum.Extension.instContinuousSMulAdicCompletionValEqUnder IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsModuleTopology IsDedekindDomain.HeightOneSpectrum.Extension.instFiniteSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnderOfFiniteDimensional IsDedekindDomain.HeightOneSpectrum.adicCompletion.instFiniteValEqUnderOfFiniteDimensional_definitions instIsBiscalarTensorProductCoeAlgHomBaseChange_of_algebraMap IsDedekindDomain.HeightOneSpectrum.instIsScalarTowerSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnder_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsModuleTopologyPi Submodule.instIsTopologicalModuleSubtypeMem Pi.instTopologicalModule IsTopologicalModule.toContinuousSMul IsTopologicalModule.toContinuousAdd instFunLike SemialgHomClass.toSemilinearMapClass instCoeTCSemialgHom SemialgHomClass.toRingHomClass SemialgHomClass.instSemialgHom IsDirectLimit.Module.instDirectLimitCoeLinearMapIdOfOfNonempty RestrictedProduct.instIsDirectLimit'"
p2m_attr_erase "instance" "RestrictedProduct.instIsDirectLimit RestrictedProduct.instNonemptyOrderDualElemSetSets_definitions RestrictedProduct.instDirectedSystem RestrictedProduct.instDirectedSystemCoeSubmoduleCoeLinearMapIdInclusionLinearMap RestrictedProduct.directed RestrictedProduct.instDirectedSystemOrderDualElemSetSetsCoeSubmodulePrincipalValMemCoeLinearMapIdInclusionLinearMap M4aHerbrand.Bridge.sigmaCompactSpace_finiteAdeleRing M4aHerbrand.Bridge.sigmaCompactSpace_adeleRing M4aHerbrand.Bridge.sigmaCompactSpace_infiniteAdeleRing M4aHerbrand.Bridge.sigmaCompactSpace_completion M4aHerbrand.Bridge.instT2SpaceAdeleRing"
p2m_attr_erase "simp" "LocalGL2.coe_localRepSome LocalGL2.coe_diagPi LocalGL2.coe_localRepInf LocalGL2.coe_localRepSome_inv LocalGL2.coe_unipotentInt LocalGL2.coe_weylInt LocalGL2.coe_diagPi_inv LocalGL2.transposeGL_val LocalGL2.transposeGL_one LocalGL2.swapUnit_val LanglandsTunnell.CubicLambda.ResolventDatum.s3.injEq LanglandsTunnell.CubicLambda.ResolventDatum.s3.sizeOf_spec LanglandsTunnell.CubicLambda.ResolventDatum.cyclic.sizeOf_spec LanglandsTunnell.CubicLambda.ResolventDatum.cyclic.injEq M4aHerbrand.IdeleGaloisDescent.mk.sizeOf_spec M4aHerbrand.IdeleGaloisDescent.mk.injEq M4aHerbrand.AdeleBaseChange.mk.sizeOf_spec M4aHerbrand.AdeleBaseChange.mk.injEq M4aHerbrand.Bridge.prodTensorAlgEquiv_tmul M4aHerbrand.Bridge.genuineβ_fst M4aHerbrand.Bridge.genuineβ_snd M4aHerbrand.ArchSemilocal.psiFactor_tmul M4aHerbrand.ArchSemilocal.psi_apply FLT.InfiniteAdeleBaseChange.evalAlgHom_apply FLT.InfiniteAdeleBaseChange.BaseChangeData.mk.sizeOf_spec FLT.InfiniteAdeleBaseChange.tensorPiAlgHom_tmul_apply FLT.InfiniteAdeleBaseChange.collapsePlaces_apply FLT.InfiniteAdeleBaseChange.tensorPiAlgEquiv_tmul_apply FLT.InfiniteAdeleBaseChange.InfinitePlaceData.mk.sizeOf_spec FLT.InfiniteAdeleBaseChange.InfinitePlaceData.mk.injEq FLT.InfiniteAdeleBaseChange.BaseChangeData.mk.injEq M4aHerbrand.Bridge.finiteConorm_apply SemialgHom.baseChange_of_algebraMap_tmul_left SemialgHom.baseChangeRightOfAlgebraMap_apply Pi.semialgHomPi_apply Pi.semialgHom_apply Module.Basis.rightBaseChange_apply LinearEquiv.coe_mulLeft LinearEquiv.coe_mulRight WithVal.semialgebraMap_toFun_ofVal"
p2m_attr_erase "simp" "Module.Basis.rightBaseChange_repr IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers.tensorCoe_tmul IsDedekindDomain.HeightOneSpectrum.tensorAdicCompletionIntegersTo_tmul SemialgHom.baseChangeRightOfAlgebraMap_coe IsDedekindDomain.HeightOneSpectrum.adicCompletion.integerBaseChangeLinearEquiv_tmul_apply SemialgHom.baseChange_of_algebraMap_tmul_right IsLocalization.map_moduleTensorEquiv_symm_tmul IsLocalization.leftModuleTensorEquiv_apply IsLocalization.moduleLid_symm_apply IsLocalization.leftModuleTensorEquiv_symm_apply IsLocalization.map_moduleTensorEquiv_tmul IsModuleTopology.continuousLinearEquiv_apply AlgEquiv.extendScalars_symm_apply IsModuleTopology.Module.Basis.equivFun_homeo_symm_apply IsModuleTopology.Module.Basis.equivFun_homeo_apply IsModuleTopology.continuousAlgEquivOfIsBiscalar_apply AlgEquiv.extendScalars_apply IsModuleTopology.continuousLinearEquiv_symm_apply SemialgHom.restrictScalars_toFun SemialgHom.mk.sizeOf_spec SemialgHom.mk.injEq SemialgHom.coe_coe coe_mk TensorProduct.RightActions.smul_def TensorProduct.RightActions.Module.TensorProduct.comm_symm_apply_tmul TensorProduct.RightActions.LinearMap.baseChange_id TensorProduct.RightActions.algebraMap_eval TensorProduct.RightActions.Module.TensorProduct.comm_apply_tmul TensorProduct.RightActions.Algebra.TensorProduct.comm_symm_apply_tmul TensorProduct.RightActions.Algebra.TensorProduct.comm_apply_tmul M4aHerbrand.Bridge.tensorAdeleRingEquiv_apply M4aHerbrand.Bridge.flattenPlaces_apply M4aHerbrand.Bridge.congrPlaces_apply M4aHerbrand.Bridge.integralTensorRingEquiv_tmul M4aHerbrand.Bridge.moduleStructureBridge_apply RestrictedProduct.lTensorEquivLeft_tmul RestrictedProduct.lTensorEquiv_tmul RestrictedProduct.lTensorLeft_tmul RestrictedProduct.lTensor_tmul IsDirectLimit.Module.linearEquiv_symm_apply"
p2m_attr_erase "simp" "IsDirectLimit.linearEquiv_symm_apply IsDirectLimit.lift_of IsDirectLimit.Module.linearEquiv_apply IsDirectLimit.Module.lift_of IsDirectLimit.Equiv_apply RestrictedProduct.not_mem_support RestrictedProduct.mem_structureSubring_iff RestrictedProduct.not_mem_mulSupport RestrictedProduct.support_neg RestrictedProduct.mem_indexSupport_iff RestrictedProduct.mulSupport_inv RestrictedProduct.mapAlongLinearMap_apply RingEquiv.restrictedProductCongr_symm_apply RingEquiv.restrictedProductCongrRight_apply MulEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductProd_symm_apply_coe Equiv.restrictedProductCongrRight_apply AddEquiv.restrictedProductCongr_apply Equiv.restrictedProductCongrLeft'_symm_apply_apply Equiv.restrictedProductCongr_apply_apply Equiv.restrictedProductCongrLeft_apply_apply RestrictedProduct.flatten_equiv'_apply AddEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductCongr_symm_apply Equiv.restrictedProductCongrRight_symm_apply RestrictedProduct.flatten_equiv'_symm_apply AddEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductCongrLeft'_apply RestrictedProduct.flatten_apply RingEquiv.restrictedProductCongr_apply_apply RingEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductProd_apply RestrictedProduct.flatten_equiv_apply RestrictedProduct.flatten_equiv_symm_apply LinearEquiv.restrictedProductCongrLeft'_apply LanglandsTunnell.CubicInduction.diagonal3_coe LanglandsTunnell.CubicInduction.halfModulus3_one LanglandsTunnell.CubicInduction.torusChar3_one"

set_option autoImplicit false

open IsDedekindDomain NumberField AutomorphicForm LanglandsTunnell.RankinSelberg MeasureTheory LanglandsTunnell.TateLocal UnramifiedWhittaker LanglandsTunnell.CubicInduction

open scoped nonZeroDivisors

set_option autoImplicit false

open MeasureTheory IsDedekindDomain NumberField AutomorphicForm UnramifiedWhittaker LanglandsTunnell.TateLocal LanglandsTunnell.CubicInduction

open scoped Topology ENNReal NNReal Matrix

namespace Ws31
namespace J3dQ

noncomputable section

section Algebra

variable {A : Type*} [CommRing A]

theorem transposeInv3_coe (g : GL (Fin 3) A) :
    ((transposeInv3 g : GL (Fin 3) A) : Matrix (Fin 3) (Fin 3) A) =
      (((g⁻¹ : GL (Fin 3) A) : Matrix (Fin 3) (Fin 3) A))ᵀ := rfl

theorem transposeInv3_mul (g h : GL (Fin 3) A) :
    transposeInv3 (g * h) = transposeInv3 g * transposeInv3 h := by
  refine Units.ext ?_
  rw [Units.val_mul, transposeInv3_coe, transposeInv3_coe, transposeInv3_coe, _root_.mul_inv_rev, Units.val_mul,
    Matrix.transpose_mul]

theorem transposeInv3_transposeInv3 (g : GL (Fin 3) A) : transposeInv3 (transposeInv3 g) = g := by
  refine Units.ext ?_
  show ((((g : GL (Fin 3) A) : Matrix (Fin 3) (Fin 3) A))ᵀ)ᵀ = _
  exact Matrix.transpose_transpose _

theorem embedMat2_transpose (M : Matrix (Fin 2) (Fin 2) A) : embedMat2 Mᵀ = (embedMat2 M)ᵀ := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [embedMat2]

theorem transposeInv3_iotaGL (h : GL (Fin 2) A) :
    transposeInv3 (iotaGL h) = iotaGL (transposeInvN (Fin 2) h) := by
  refine Units.ext ?_
  rw [transposeInv3_coe, ← map_inv, coe_iotaGL, coe_iotaGL, coe_transposeInvN, embedMat2_transpose]

theorem det_transposeInvN (h : GL (Fin 2) A) :
    Matrix.GeneralLinearGroup.det (transposeInvN (Fin 2) h) = (Matrix.GeneralLinearGroup.det h)⁻¹ := by
  refine Units.ext ?_
  rw [Matrix.GeneralLinearGroup.val_det_apply, coe_transposeInvN, Matrix.det_transpose,
    ← Matrix.GeneralLinearGroup.val_det_apply, map_inv]

theorem transposeInv3_upperUnipotent3 (x : A) :
    transposeInv3 (upperUnipotent3 x 0 0 : GL (Fin 3) A) = lowerUnipotent21 (-x) := by
  have h := transposeInv3_lowerUnipotent21 (A := A) (-x)
  rw [neg_neg] at h
  rw [← h, transposeInv3_transposeInv3]

theorem longWeyl3_mul_lowerUnipotent21 (x : A) :
    (longWeyl3 : GL (Fin 3) A) * lowerUnipotent21 x = upperUnipotent3 0 x 0 * longWeyl3 := by
  refine Units.ext ?_
  rw [Units.val_mul, Units.val_mul, longWeyl3_coe, lowerUnipotent21_coe, upperUnipotent3_coe]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three]

variable {L : Type*} [Field L]

theorem unipotent_eq_unipotentGL2 (x : L) : UnramifiedWhittaker.unipotent x = (unipotentGL2 x : GL (Fin 2) L) := by
  refine Units.ext ?_
  rw [unipotentGL2_coe]
  simp [UnramifiedWhittaker.unipotent]

theorem coe_inv_unipotentGL2 (x : L) :
    (((unipotentGL2 x : GL (Fin 2) L)⁻¹ : GL (Fin 2) L) : Matrix (Fin 2) (Fin 2) L) = !![1, -x; 0, 1] := rfl

theorem weyl_mul_transposeInvN_unipotentGL2 {w₀p : GL (Fin 2) L}
    (hw₀p : (w₀p : Matrix (Fin 2) (Fin 2) L) = !![0, 1; 1, 0]) (x : L) :
    w₀p * transposeInvN (Fin 2) (unipotentGL2 x) = unipotentGL2 (-x) * w₀p := by
  refine Units.ext ?_
  rw [Units.val_mul, Units.val_mul, coe_transposeInvN, coe_inv_unipotentGL2, hw₀p, unipotentGL2_coe]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

def tau : GL (Fin 2) A ≃* GL (Fin 2) A where
  toFun := transposeInvN (Fin 2)
  invFun := transposeInvN (Fin 2)
  left_inv := transposeInvN_transposeInvN (Fin 2)
  right_inv := transposeInvN_transposeInvN (Fin 2)
  map_mul' := transposeInvN_mul (Fin 2)

theorem tau_apply (g : GL (Fin 2) A) : tau g = transposeInvN (Fin 2) g := rfl

end Algebra

attribute [local instance] LanglandsTunnell.TateLocal.localBorel
attribute [local instance] LanglandsTunnell.TateLocal.borelSpace_localBorel
attribute [local instance] AutomorphicForm.localGLBorel
attribute [local instance] AutomorphicForm.borelSpace_localGLBorel

variable (K : Type) [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))

local notation "F" => (HeightOneSpectrum.adicCompletion K v)
local notation "O" => (HeightOneSpectrum.adicCompletionIntegers K v)
local notation "G₂" => (GL (Fin 2) (HeightOneSpectrum.adicCompletion K v))
local notation "G₃" => (GL (Fin 3) (HeightOneSpectrum.adicCompletion K v))
local notation "Mat" => (Matrix (Fin 2) (Fin 2) (HeightOneSpectrum.adicCompletion K v))

scoped instance : SecondCountableTopology (Matrix (Fin 2) (Fin 2) (HeightOneSpectrum.adicCompletion K v)) :=
  inferInstanceAs (SecondCountableTopology (Fin 2 → Fin 2 → HeightOneSpectrum.adicCompletion K v))

scoped instance : SecondCountableTopology (Matrix (Fin 2) (Fin 2) (HeightOneSpectrum.adicCompletion K v))ᵐᵒᵖ :=
  MulOpposite.opHomeomorph.symm.secondCountableTopology

scoped instance secondCountableTopology_localGL : SecondCountableTopology G₂ :=
  Units.isEmbedding_embedProduct.isInducing.secondCountableTopology

scoped instance locallyCompactSpace_localGL' : LocallyCompactSpace G₂ := locallyCompactSpace_localGL K v

theorem continuous_transposeInvN : Continuous (transposeInvN (Fin 2) : G₂ → G₂) := by
  refine Units.continuous_iff.mpr ⟨?_, ?_⟩
  · change Continuous fun g : G₂ => (((g⁻¹ : G₂) : Mat))ᵀ
    exact Units.continuous_coe_inv.matrix_transpose
  · change Continuous fun g : G₂ => ((g : G₂) : Mat)ᵀ
    exact Units.continuous_val.matrix_transpose

def tauHomeo : G₂ ≃ₜ G₂ where
  toEquiv := (tau : G₂ ≃* G₂).toEquiv
  continuous_toFun := continuous_transposeInvN K v
  continuous_invFun := continuous_transposeInvN K v

theorem map_transposeInvN_eq (μ : Measure G₂) [μ.IsHaarMeasure] : Measure.map (transposeInvN (Fin 2)) μ = μ := by
  have hcont := continuous_transposeInvN K v
  haveI : (Measure.map (transposeInvN (Fin 2)) μ).IsHaarMeasure :=
    (tau : G₂ ≃* G₂).isHaarMeasure_map μ hcont hcont
  set c := Measure.haarScalarFactor (Measure.map (transposeInvN (Fin 2)) μ) μ with hc
  have h1 : Measure.map (transposeInvN (Fin 2)) μ = c • μ := Measure.isMulLeftInvariant_eq_smul _ _

  have h2 : μ = (c * c) • μ := by
    have hmm : Measure.map (transposeInvN (Fin 2)) (Measure.map (transposeInvN (Fin 2)) μ) = μ := by
      rw [Measure.map_map hcont.measurable hcont.measurable]
      have : (transposeInvN (Fin 2) ∘ transposeInvN (Fin 2) : G₂ → G₂) = id :=
        funext (transposeInvN_transposeInvN (Fin 2))
      rw [this, Measure.map_id]
    calc μ = Measure.map (transposeInvN (Fin 2)) (Measure.map (transposeInvN (Fin 2)) μ) := hmm.symm
      _ = Measure.map (transposeInvN (Fin 2)) (c • μ) := by rw [h1]
      _ = c • Measure.map (transposeInvN (Fin 2)) μ := by rw [Measure.map_smul]
      _ = (c * c) • μ := by rw [h1, smul_smul]

  obtain ⟨K₀, hK₀c, hK₀i⟩ : ∃ S : Set G₂, IsCompact S ∧ (interior S).Nonempty :=
    ⟨localIntegralSet K v, isCompact_localIntegralSet K v,
      ⟨1, by rw [(isOpen_localIntegralSet K v).interior_eq]; exact one_mem_localIntegralSet K v⟩⟩
  have hpos : 0 < μ K₀ := hK₀i.mono interior_subset |>.elim (fun x hx => lt_of_lt_of_le (isOpen_interior.measure_pos μ hK₀i) (measure_mono interior_subset))
  have hfin : μ K₀ < ⊤ := hK₀c.measure_lt_top
  have hcc : (c * c : ℝ≥0) = 1 := by
    have h3 := congr_arg (fun m : Measure G₂ => m K₀) h2
    simp only [Measure.smul_apply] at h3
    rw [ENNReal.smul_def, smul_eq_mul] at h3
    have h4 : (1 : ℝ≥0∞) = ((c * c : ℝ≥0) : ℝ≥0∞) := by
      rw [← ENNReal.mul_left_inj hpos.ne' hfin.ne, one_mul]
      exact h3
    exact_mod_cast h4.symm
  have hc1 : c = 1 := by
    have h5 : ((c : ℝ) * c) = 1 := by exact_mod_cast hcc
    have h6 : (c : ℝ) = 1 := by
      have hn : (0 : ℝ) ≤ c := c.2
      nlinarith [h5, hn]
    exact_mod_cast h6
  rw [h1, hc1, one_smul]

abbrev kzero : Subgroup G₂ := AdelicDock.localLevelOne (𝓞 K) K v ⊤

theorem isLocalLevelOne_top_of_integral {m : Mat} (h : ∀ i j, m i j ∈ (O)) :
    AdelicDock.IsLocalLevelOne (𝓞 K) K v ⊤ m := by
  refine ⟨h, ?_, ?_⟩
  · rw [AdelicLevel.idealBound_top]
    exact (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).mp (h 1 0)
  · rw [AdelicLevel.idealBound_top]
    calc Valued.v (m 1 1 - 1) ≤ max (Valued.v (m 1 1)) (Valued.v (1 : F)) := Valuation.map_sub _ _ _
      _ ≤ 1 := max_le ((HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).mp (h 1 1)) (by simp)

theorem mem_kzero_iff (k : G₂) :
    k ∈ kzero K v ↔ (∀ i j, (k : Mat) i j ∈ (O)) ∧ ∀ i j, ((k⁻¹ : G₂) : Mat) i j ∈ (O) := by
  rw [AdelicDock.mem_localLevelOne_iff]
  constructor
  · rintro ⟨h1, h2⟩; exact ⟨h1.integral, h2.integral⟩
  · rintro ⟨h1, h2⟩
    exact ⟨isLocalLevelOne_top_of_integral K v h1, isLocalLevelOne_top_of_integral K v h2⟩

theorem transposeInvN_mem_kzero {k : G₂} (hk : k ∈ kzero K v) : transposeInvN (Fin 2) k ∈ kzero K v := by
  rw [mem_kzero_iff] at hk ⊢
  refine ⟨fun i j => ?_, fun i j => ?_⟩
  · rw [coe_transposeInvN, Matrix.transpose_apply]; exact hk.2 j i
  · rw [coe_inv_transposeInvN, Matrix.transpose_apply]; exact hk.1 j i

theorem valuation_det_of_mem_kzero {k : G₂} (hk : k ∈ kzero K v) :
    Valued.v ((Matrix.GeneralLinearGroup.det k : (HeightOneSpectrum.adicCompletion K v)ˣ) : F) = 1 := by
  rw [mem_kzero_iff] at hk
  have hint : ∀ (m : Mat), (∀ i j, m i j ∈ (O)) → Valued.v m.det ≤ 1 := by
    intro m hm
    rw [Matrix.det_fin_two]
    have h := fun i j => (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).mp (hm i j)
    calc Valued.v (m 0 0 * m 1 1 - m 0 1 * m 1 0)
        ≤ max (Valued.v (m 0 0 * m 1 1)) (Valued.v (m 0 1 * m 1 0)) := Valuation.map_sub _ _ _
      _ ≤ 1 := by
          refine max_le ?_ ?_
          · rw [map_mul]; exact mul_le_one' (h 0 0) (h 1 1)
          · rw [map_mul]; exact mul_le_one' (h 0 1) (h 1 0)
  have h1 := hint _ hk.1
  have h2 := hint _ hk.2
  have hprod : Valued.v ((k : Mat).det) * Valued.v (((k⁻¹ : G₂) : Mat).det) = 1 := by
    rw [← map_mul, ← Matrix.det_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.det_one, map_one]
  rw [Matrix.GeneralLinearGroup.val_det_apply]
  apply le_antisymm h1
  by_contra hlt
  push Not at hlt
  have : Valued.v ((k : Mat).det) * Valued.v (((k⁻¹ : G₂) : Mat).det) < 1 :=
    mul_lt_one_of_lt_of_le hlt h2
  rw [hprod] at this
  exact lt_irrefl _ this

theorem coe_modulus_eq_norm (x : F) : ((modulus x : NNReal) : ℝ) = ‖x‖ := by
  rw [modulus_adicCompletion_eq_nnnorm K v x, coe_nnnorm]

theorem modulus_det_of_mem_kzero {k : G₂} (hk : k ∈ kzero K v) :
    (modulus ((Matrix.GeneralLinearGroup.det k : (HeightOneSpectrum.adicCompletion K v)ˣ) : F) : ℝ) = 1 := by
  rw [coe_modulus_eq_norm, NumberField.FinitePlace.norm_def, valuation_det_of_mem_kzero K v hk, map_one, NNReal.coe_one]

variable (b : ℕ)

abbrev kone : Subgroup G₂ := AdelicDock.localLevelOne (𝓞 K) K v (v.asIdeal ^ b)

theorem idealBound_pow :
    AdelicLevel.idealBound (𝓞 K) (v.asIdeal ^ b) v = WithZero.exp (-(b : ℤ)) := by
  classical
  have hne : v.asIdeal ^ b ≠ ⊥ := pow_ne_zero _ v.ne_bot
  rw [AdelicLevel.idealBound_of_ne_bot hne, Associates.mk_pow,
    Associates.count_pow (Associates.mk_ne_zero.mpr v.ne_bot) v.associates_irreducible,
    Associates.count_self v.associates_irreducible, mul_one]

theorem kone_le : kone K v b ≤ kzero K v := by
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

theorem isOpen_kone : IsOpen ((kone K v b : Subgroup G₂) : Set G₂) :=
  (AdelicDock.isCompact_and_isOpen_localLevelOne K v (v.asIdeal ^ b) (pow_ne_zero _ v.ne_bot)).2

theorem cong_inv {k : G₂} (hk : k ∈ kzero K v)
    (hc : ∀ i j : Fin 2, Valued.v (((k : Mat) - 1) i j) ≤ WithZero.exp (-(b : ℤ))) :
    ∀ i j : Fin 2, Valued.v ((((k⁻¹ : G₂) : Mat) - 1) i j) ≤ WithZero.exp (-(b : ℤ)) := by
  rw [mem_kzero_iff] at hk
  have hiint := fun i j => (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).mp (hk.2 i j)
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

theorem mem_kone_of_cong (k : G₂) (hk : k ∈ kzero K v)
    (hc : ∀ i j : Fin 2, Valued.v (((k : Mat) - 1) i j) ≤ WithZero.exp (-(b : ℤ))) :
    k ∈ kone K v b := by
  have hc' := cong_inv K v b hk hc
  rw [AdelicDock.mem_localLevelOne_iff] at hk ⊢
  obtain ⟨hk1, hk2⟩ := hk
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

def koneT : Subgroup G₂ := (kone K v b).comap ((tau : G₂ ≃* G₂).toMonoidHom)

theorem mem_koneT_iff (k : G₂) : k ∈ koneT K v b ↔ transposeInvN (Fin 2) k ∈ kone K v b := Iff.rfl

theorem isOpen_koneT : IsOpen ((koneT K v b : Subgroup G₂) : Set G₂) :=
  (isOpen_kone K v b).preimage (continuous_transposeInvN K v)

theorem koneT_le : koneT K v b ≤ kzero K v := by
  intro k hk
  rw [mem_koneT_iff] at hk
  have h := transposeInvN_mem_kzero K v (kone_le K v b hk)
  rwa [transposeInvN_transposeInvN] at h

theorem mem_koneT_of_cong (k : G₂) (hk : k ∈ kzero K v)
    (hc : ∀ i j : Fin 2, Valued.v (((k : Mat) - 1) i j) ≤ WithZero.exp (-(b : ℤ))) :
    k ∈ koneT K v b := by
  rw [mem_koneT_iff]
  refine mem_kone_of_cong K v b _ (transposeInvN_mem_kzero K v hk) fun i j => ?_
  rw [coe_transposeInvN]
  have : ((((k⁻¹ : G₂) : Mat))ᵀ - 1) i j = ((((k⁻¹ : G₂) : Mat)) - 1) j i := by
    simp only [Matrix.sub_apply, Matrix.transpose_apply, Matrix.one_apply]
    by_cases hij : i = j
    · subst hij; simp
    · simp [hij, Ne.symm hij]
  rw [this]
  exact cong_inv K v b hk hc j i

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

variable {K v b}

section Pair

variable {θ : AddChar (HeightOneSpectrum.adicCompletion K v) ℂ} {W₃ : GL (Fin 3) (HeightOneSpectrum.adicCompletion K v) → ℂ}
  (g₃ : GL (Fin 3) (HeightOneSpectrum.adicCompletion K v)) {w₂ : GL (Fin 2) (HeightOneSpectrum.adicCompletion K v) → ℂ}
  {w₀p : GL (Fin 2) (HeightOneSpectrum.adicCompletion K v)}

def Afun (W₃ : G₃ → ℂ) (g₃ : G₃) : G₂ → ℂ := fun g => dualWhittakerFn3 (fun x => W₃ (x * g₃)) (iotaGL g)

def Bfun (w₂ : G₂ → ℂ) (w₀p : G₂) : G₂ → ℂ := fun g =>
  ((modulus ((Matrix.GeneralLinearGroup.det g : (HeightOneSpectrum.adicCompletion K v)ˣ) : F) : ℝ) : ℂ) *
    w₂ (w₀p * transposeInvN (Fin 2) g)

theorem Afun_apply (g : G₂) : Afun W₃ g₃ g = W₃ (longWeyl3 * transposeInv3 (iotaGL g) * g₃) := rfl

theorem smooth_Afun
    (hW₃sm : ∃ Uv : Subgroup G₃, IsOpen (Uv : Set G₃) ∧ ∀ k ∈ Uv, ∀ g : G₃, W₃ (g * k) = W₃ g) :
    ∃ U : Subgroup G₂, IsOpen (U : Set G₂) ∧ ∀ k ∈ U, ∀ g : G₂, Afun W₃ g₃ (g * k) = Afun W₃ g₃ g := by
  obtain ⟨Uv, hUv, hinv⟩ := hW₃sm
  let φ : G₂ →* G₃ := (MulAut.conj g₃⁻¹).toMonoidHom.comp (iotaGL.comp (tau : G₂ ≃* G₂).toMonoidHom)
  refine ⟨Uv.comap φ, ?_, ?_⟩
  · have hφ : Continuous φ := by
      change Continuous fun h : G₂ => g₃⁻¹ * iotaGL (transposeInvN (Fin 2) h) * g₃⁻¹⁻¹
      exact (continuous_const.mul ((continuous_iotaGL K v).comp (continuous_transposeInvN K v))).mul continuous_const
    exact hUv.preimage hφ
  · intro k hk g
    have hk' : g₃⁻¹ * iotaGL (transposeInvN (Fin 2) k) * g₃ ∈ Uv := by
      have := hk
      rw [Subgroup.mem_comap] at this
      simpa [φ, tau_apply] using this
    rw [Afun_apply, Afun_apply, map_mul, transposeInv3_mul, transposeInv3_iotaGL k]
    have : longWeyl3 * (transposeInv3 (iotaGL g) * iotaGL (transposeInvN (Fin 2) k)) * g₃ =
        longWeyl3 * transposeInv3 (iotaGL g) * g₃ * (g₃⁻¹ * iotaGL (transposeInvN (Fin 2) k) * g₃) := by group
    rw [this, hinv _ hk']

theorem Bfun_mul (hw₂K : ∀ k ∈ kone K v b, ∀ g : G₂, w₂ (g * k) = w₂ g) :
    ∀ k ∈ koneT K v b, ∀ g : G₂, Bfun w₂ w₀p (g * k) = Bfun w₂ w₀p g := by
  intro k hk g
  have hkK : k ∈ kzero K v := koneT_le K v b hk
  rw [mem_koneT_iff] at hk
  simp only [Bfun]
  rw [map_mul, Units.val_mul, modulus_mul, NNReal.coe_mul, modulus_det_of_mem_kzero K v hkK, mul_one,
    transposeInvN_mul, ← mul_assoc, hw₂K _ hk]

theorem prod_unipotent (hW₃law : IsGL3PsiWhittakerFn θ⁻¹ W₃)
    (hw₂law : ∀ (x : F) (g : G₂), w₂ (UnramifiedWhittaker.unipotent x * g) = θ x * w₂ g)
    (hw₀p : (w₀p : Mat) = !![0, 1; 1, 0]) (x : F) (g : G₂) :
    Afun W₃ g₃ (UnramifiedWhittaker.unipotent x * g) * Bfun w₂ w₀p (UnramifiedWhittaker.unipotent x * g) =
      Afun W₃ g₃ g * Bfun w₂ w₀p g := by
  have h1 : Afun W₃ g₃ (UnramifiedWhittaker.unipotent x * g) = θ x * Afun W₃ g₃ g := by
    rw [Afun_apply, Afun_apply, map_mul, transposeInv3_mul, unipotent_eq_unipotentGL2, iotaGL_unipotentGL2,
      transposeInv3_upperUnipotent3, ← mul_assoc (longWeyl3 : G₃), longWeyl3_mul_lowerUnipotent21, mul_assoc,
      mul_assoc, hW₃law, AddChar.inv_apply, zero_add, neg_neg, ← mul_assoc]
  have h2 : Bfun w₂ w₀p (UnramifiedWhittaker.unipotent x * g) = θ (-x) * Bfun w₂ w₀p g := by
    have hw₂law' : ∀ (y : F) (h : G₂), w₂ ((unipotentGL2 y : G₂) * h) = θ y * w₂ h := by
      intro y h; rw [← unipotent_eq_unipotentGL2]; exact hw₂law y h
    have hdet : Matrix.GeneralLinearGroup.det (unipotentGL2 x : G₂) = 1 := by
      refine Units.ext ?_
      rw [Matrix.GeneralLinearGroup.val_det_apply, unipotentGL2_coe, Matrix.det_fin_two_of]
      simp
    simp only [Bfun]
    rw [map_mul, unipotent_eq_unipotentGL2, transposeInvN_mul, ← mul_assoc, weyl_mul_transposeInvN_unipotentGL2 hw₀p,
      mul_assoc, hw₂law', hdet, one_mul]
    ring
  rw [h1, h2]
  have h3 : θ x * θ (-x) = 1 := by rw [← AddChar.map_add_eq_mul, add_neg_cancel, AddChar.map_zero_eq_one]
  calc θ x * Afun W₃ g₃ g * (θ (-x) * Bfun w₂ w₀p g) = (θ x * θ (-x)) * (Afun W₃ g₃ g * Bfun w₂ w₀p g) := by ring
    _ = Afun W₃ g₃ g * Bfun w₂ w₀p g := by rw [h3, one_mul]

theorem setIntegral_koneT_eq (μ₂ : Measure G₂) [μ₂.IsHaarMeasure] (G : G₂ → ℂ) (hG : Continuous G) :
    ∫ k in ((koneT K v b : Subgroup G₂) : Set G₂), G k ∂μ₂ =
      ∫ k in ((kone K v b : Subgroup G₂) : Set G₂), G (transposeInvN (Fin 2) k) ∂μ₂ := by
  have hτ := continuous_transposeInvN K v
  conv_lhs => rw [← map_transposeInvN_eq K v μ₂]
  rw [setIntegral_map (isOpen_koneT K v b).measurableSet hG.aestronglyMeasurable hτ.aemeasurable]
  have hset : (transposeInvN (Fin 2)) ⁻¹' ((koneT K v b : Subgroup G₂) : Set G₂) = ((kone K v b : Subgroup G₂) : Set G₂) := by
    ext k
    simp only [Set.mem_preimage, SetLike.mem_coe, mem_koneT_iff, transposeInvN_transposeInvN]
  rw [hset]

end Pair

end

end Ws31.J3dQ
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_forall_exists_rational_rsLocalIntegral_dual_translate_of_shellRecurrence_of_centralChar_of_rationalTorusShell_of_gauge.Ws31 P2MW.S_LanglandsTunnell_RankinSelberg_forall_exists_rational_rsLocalIntegral_dual_translate_of_shellRecurrence_of_centralChar_of_rationalTorusShell_of_gauge.Ws31.J3dQ"
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_forall_exists_rational_rsLocalIntegral_dual_translate_of_shellRecurrence_of_centralChar_of_rationalTorusShell_of_gauge.Ws31"

open MeasureTheory IsDedekindDomain NumberField AutomorphicForm UnramifiedWhittaker
open scoped ENNReal NNReal

namespace Ws31
namespace J3dG

noncomputable section

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
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_forall_exists_rational_rsLocalIntegral_dual_translate_of_shellRecurrence_of_centralChar_of_rationalTorusShell_of_gauge.Ws31 P2MW.S_LanglandsTunnell_RankinSelberg_forall_exists_rational_rsLocalIntegral_dual_translate_of_shellRecurrence_of_centralChar_of_rationalTorusShell_of_gauge.Ws31.J3dQ"

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
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_forall_exists_rational_rsLocalIntegral_dual_translate_of_shellRecurrence_of_centralChar_of_rationalTorusShell_of_gauge.Ws31 P2MW.S_LanglandsTunnell_RankinSelberg_forall_exists_rational_rsLocalIntegral_dual_translate_of_shellRecurrence_of_centralChar_of_rationalTorusShell_of_gauge.Ws31.J3dQ"

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
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_forall_exists_rational_rsLocalIntegral_dual_translate_of_shellRecurrence_of_centralChar_of_rationalTorusShell_of_gauge.Ws31 P2MW.S_LanglandsTunnell_RankinSelberg_forall_exists_rational_rsLocalIntegral_dual_translate_of_shellRecurrence_of_centralChar_of_rationalTorusShell_of_gauge.Ws31.J3dQ"

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
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_forall_exists_rational_rsLocalIntegral_dual_translate_of_shellRecurrence_of_centralChar_of_rationalTorusShell_of_gauge.Ws31 P2MW.S_LanglandsTunnell_RankinSelberg_forall_exists_rational_rsLocalIntegral_dual_translate_of_shellRecurrence_of_centralChar_of_rationalTorusShell_of_gauge.Ws31.J3dQ"

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
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_forall_exists_rational_rsLocalIntegral_dual_translate_of_shellRecurrence_of_centralChar_of_rationalTorusShell_of_gauge.Ws31 P2MW.S_LanglandsTunnell_RankinSelberg_forall_exists_rational_rsLocalIntegral_dual_translate_of_shellRecurrence_of_centralChar_of_rationalTorusShell_of_gauge.Ws31.J3dQ"

section PartnerBound

open LanglandsTunnell.CubicInduction

variable {v : HeightOneSpectrum (𝓞 ℚ)}

local notation "F" => (HeightOneSpectrum.adicCompletion ℚ v)
local notation "O" => (HeightOneSpectrum.adicCompletionIntegers ℚ v)
local notation "G" => (GL (Fin 2) (HeightOneSpectrum.adicCompletion ℚ v))
local notation "Mat" => (Matrix (Fin 2) (Fin 2) (HeightOneSpectrum.adicCompletion ℚ v))

variable {ϖ : HeightOneSpectrum.adicCompletionIntegers ℚ v}

theorem scalar_mul_comm (u : (HeightOneSpectrum.adicCompletion ℚ v)ˣ) (g : G) :
    Matrix.GeneralLinearGroup.scalar (Fin 2) u * g = g * Matrix.GeneralLinearGroup.scalar (Fin 2) u := by
  refine Units.ext ?_
  change Matrix.scalar (Fin 2) (u : F) * (g : Mat) = (g : Mat) * Matrix.scalar (Fin 2) (u : F)
  exact (Matrix.scalar_commute (u : F) (fun r => mul_comm _ _) (g : Mat)).eq

theorem partner_shell_eq (hπ : algebraMap (O) (F) ϖ ≠ 0) {W₂ : G → ℂ} (ω₂ : (HeightOneSpectrum.adicCompletion ℚ v)ˣ →* ℂˣ)
    (hW₂Z : ∀ (t : (HeightOneSpectrum.adicCompletion ℚ v)ˣ) (g : G),
      W₂ (g * Matrix.GeneralLinearGroup.scalar (Fin 2) t) = ((ω₂ t : ℂˣ) : ℂ) * W₂ g)
    (dn : ℤ × ℤ) (k : G) :
    W₂ (scalarPi (algebraMap (O) (F) ϖ) hπ ^ dn.2 * diagZ (algebraMap (O) (F) ϖ) hπ dn.1 * k) =
      ((ω₂ (piUnit hπ) : ℂˣ) : ℂ) ^ dn.2 * W₂ (diagZ (algebraMap (O) (F) ϖ) hπ dn.1 * k) := by
  rw [shellRep_eq_diagZ_mul hπ, scalarPi_zpow_eq_scalar hπ, mul_assoc, scalar_mul_comm, ← mul_assoc, hW₂Z, map_zpow,
    Units.val_zpow_eq_zpow_val]

theorem norm_partner_shell_eq (hπ : algebraMap (O) (F) ϖ ≠ 0) {W₂ : G → ℂ}
    (ω₂ : (HeightOneSpectrum.adicCompletion ℚ v)ˣ →* ℂˣ)
    (hW₂Z : ∀ (t : (HeightOneSpectrum.adicCompletion ℚ v)ˣ) (g : G),
      W₂ (g * Matrix.GeneralLinearGroup.scalar (Fin 2) t) = ((ω₂ t : ℂˣ) : ℂ) * W₂ g)
    (dn : ℤ × ℤ) (k : G) :
    ‖W₂ (scalarPi (algebraMap (O) (F) ϖ) hπ ^ dn.2 * diagZ (algebraMap (O) (F) ϖ) hπ dn.1 * k)‖ =
      ‖((ω₂ (piUnit hπ) : ℂˣ) : ℂ)‖ ^ dn.2 * ‖W₂ (diagZ (algebraMap (O) (F) ϖ) hπ dn.1 * k)‖ := by
  rw [partner_shell_eq hπ ω₂ hW₂Z, norm_mul, norm_zpow]

theorem exists_bound_on_shell (hπ : algebraMap (O) (F) ϖ ≠ 0) {W₂ : G → ℂ} (hW₂c : Continuous W₂) (d : ℤ) :
    ∃ M : ℝ, ∀ k ∈ kzero v, ‖W₂ (diagZ (algebraMap (O) (F) ϖ) hπ d * k)‖ ≤ M := by
  have hK : IsCompact ((fun k : G => diagZ (algebraMap (O) (F) ϖ) hπ d * k) '' ((kzero v : Subgroup G) : Set G)) :=
    (isCompact_kzero v).image (continuous_const.mul continuous_id)
  obtain ⟨M, hM⟩ := hK.exists_bound_of_continuousOn hW₂c.continuousOn
  exact ⟨M, fun k hk => hM _ ⟨k, hk, rfl⟩⟩

theorem exists_partner_shell_bound (hπ : algebraMap (O) (F) ϖ ≠ 0) {W₂ : G → ℂ} (hW₂c : Continuous W₂)
    (hW₂gr : ∃ (C A : ℝ), ∀ (m : ℤ), 0 ≤ m → ∀ k ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ v ⊤,
      ‖W₂ (diagZ (algebraMap (O) (F) ϖ) hπ m * k)‖ ≤ C * (Ideal.absNorm v.asIdeal : ℝ) ^ (A * m))
    (m₀ : ℤ) (hm₀ : m₀ ≤ 0) :
    ∃ (Cβ A' : ℝ), 0 ≤ Cβ ∧ 0 ≤ A' ∧ ∀ (d : ℤ), m₀ ≤ d → ∀ k ∈ kzero v,
      ‖W₂ (diagZ (algebraMap (O) (F) ϖ) hπ d * k)‖ ≤ Cβ * qR v ^ (A' * ((d : ℝ) - m₀)) := by
  obtain ⟨C, A, hgr⟩ := hW₂gr
  choose M hM using exists_bound_on_shell hπ hW₂c
  set M₀ : ℝ := ∑ d ∈ Finset.Ico m₀ 0, |M d| with hM₀
  have hM₀nn : 0 ≤ M₀ := Finset.sum_nonneg fun d _ => abs_nonneg _
  refine ⟨|C| + M₀, max A 0, by positivity, le_max_right _ _, fun d hd k hk => ?_⟩
  have hq1 := one_le_qR v
  have hexp_nn : 0 ≤ max A 0 * ((d : ℝ) - m₀) :=
    mul_nonneg (le_max_right _ _) (by exact_mod_cast sub_nonneg.mpr hd)
  have hpow1 : 1 ≤ qR v ^ (max A 0 * ((d : ℝ) - m₀)) := Real.one_le_rpow hq1 hexp_nn
  rcases lt_or_ge d 0 with hneg | hnn
  ·
    have hmem : d ∈ Finset.Ico m₀ 0 := Finset.mem_Ico.mpr ⟨hd, hneg⟩
    calc ‖W₂ (diagZ (algebraMap (O) (F) ϖ) hπ d * k)‖ ≤ M d := hM d k hk
      _ ≤ |M d| := le_abs_self _
      _ ≤ M₀ := Finset.single_le_sum (fun i _ => abs_nonneg (M i)) hmem
      _ ≤ (|C| + M₀) * 1 := by rw [mul_one]; linarith [abs_nonneg C]
      _ ≤ (|C| + M₀) * qR v ^ (max A 0 * ((d : ℝ) - m₀)) := by gcongr
  ·
    have h1 : ‖W₂ (diagZ (algebraMap (O) (F) ϖ) hπ d * k)‖ ≤ C * qR v ^ (A * (d : ℝ)) := by
      rw [qR_eq_natCast]; exact hgr d hnn k hk
    have hpos : 0 ≤ qR v ^ (A * (d : ℝ)) := Real.rpow_nonneg (qR_pos v).le _
    have h2 : qR v ^ (A * (d : ℝ)) ≤ qR v ^ (max A 0 * ((d : ℝ) - m₀)) := by
      refine Real.rpow_le_rpow_of_exponent_le hq1 ?_
      have hd0 : (0 : ℝ) ≤ d := by exact_mod_cast hnn
      have hm0 : ((m₀ : ℤ) : ℝ) ≤ 0 := by exact_mod_cast hm₀
      calc A * (d : ℝ) ≤ max A 0 * (d : ℝ) := mul_le_mul_of_nonneg_right (le_max_left _ _) hd0
        _ ≤ max A 0 * ((d : ℝ) - m₀) := mul_le_mul_of_nonneg_left (by linarith) (le_max_right _ _)
    calc ‖W₂ (diagZ (algebraMap (O) (F) ϖ) hπ d * k)‖ ≤ C * qR v ^ (A * (d : ℝ)) := h1
      _ ≤ |C| * qR v ^ (A * (d : ℝ)) := mul_le_mul_of_nonneg_right (le_abs_self C) hpos
      _ ≤ (|C| + M₀) * qR v ^ (max A 0 * ((d : ℝ) - m₀)) :=
          mul_le_mul (by linarith) h2 hpos (by positivity)

end PartnerBound
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_forall_exists_rational_rsLocalIntegral_dual_translate_of_shellRecurrence_of_centralChar_of_rationalTorusShell_of_gauge.Ws31 P2MW.S_LanglandsTunnell_RankinSelberg_forall_exists_rational_rsLocalIntegral_dual_translate_of_shellRecurrence_of_centralChar_of_rationalTorusShell_of_gauge.Ws31.J3dQ"

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
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_forall_exists_rational_rsLocalIntegral_dual_translate_of_shellRecurrence_of_centralChar_of_rationalTorusShell_of_gauge.Ws31 P2MW.S_LanglandsTunnell_RankinSelberg_forall_exists_rational_rsLocalIntegral_dual_translate_of_shellRecurrence_of_centralChar_of_rationalTorusShell_of_gauge.Ws31.J3dQ"

end
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_forall_exists_rational_rsLocalIntegral_dual_translate_of_shellRecurrence_of_centralChar_of_rationalTorusShell_of_gauge.Ws31 P2MW.S_LanglandsTunnell_RankinSelberg_forall_exists_rational_rsLocalIntegral_dual_translate_of_shellRecurrence_of_centralChar_of_rationalTorusShell_of_gauge.Ws31.J3dQ"

end Ws31.J3dG
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_forall_exists_rational_rsLocalIntegral_dual_translate_of_shellRecurrence_of_centralChar_of_rationalTorusShell_of_gauge.Ws31 P2MW.S_LanglandsTunnell_RankinSelberg_forall_exists_rational_rsLocalIntegral_dual_translate_of_shellRecurrence_of_centralChar_of_rationalTorusShell_of_gauge.Ws31.J3dQ P2MW.S_LanglandsTunnell_RankinSelberg_forall_exists_rational_rsLocalIntegral_dual_translate_of_shellRecurrence_of_centralChar_of_rationalTorusShell_of_gauge.Ws31.J3dG"
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_forall_exists_rational_rsLocalIntegral_dual_translate_of_shellRecurrence_of_centralChar_of_rationalTorusShell_of_gauge.Ws31 P2MW.S_LanglandsTunnell_RankinSelberg_forall_exists_rational_rsLocalIntegral_dual_translate_of_shellRecurrence_of_centralChar_of_rationalTorusShell_of_gauge.Ws31.J3dQ"

namespace Ws31
namespace J3dN

open LanglandsTunnell.CubicInduction LanglandsTunnell.TateLocal Ws31.J3dG

noncomputable section

variable {v : HeightOneSpectrum (𝓞 ℚ)} {ϖ : HeightOneSpectrum.adicCompletionIntegers ℚ v}

local notation "F" => (HeightOneSpectrum.adicCompletion ℚ v)
local notation "O" => (HeightOneSpectrum.adicCompletionIntegers ℚ v)
local notation "G" => (GL (Fin 2) (HeightOneSpectrum.adicCompletion ℚ v))
local notation "Mat" => (Matrix (Fin 2) (Fin 2) (HeightOneSpectrum.adicCompletion ℚ v))

theorem transposeInvN_scalar (z : (HeightOneSpectrum.adicCompletion ℚ v)ˣ) :
    transposeInvN (Fin 2) (Matrix.GeneralLinearGroup.scalar (Fin 2) z : G) =
      Matrix.GeneralLinearGroup.scalar (Fin 2) z⁻¹ := by
  apply Units.ext
  rw [coe_transposeInvN, ← map_inv]
  simp [Matrix.GeneralLinearGroup.scalar]

theorem diagZ_inv (hπ : algebraMap (O) (F) ϖ ≠ 0) (n : ℤ) :
    (diagZ (algebraMap (O) (F) ϖ) hπ n)⁻¹ = diagZ (algebraMap (O) (F) ϖ) hπ (-n) := by
  rw [diagZ_eq_diagU hπ, diagZ_eq_diagU hπ, diagU_inv, inv_one, zpow_neg]

theorem transposeInvN_diagZ (hπ : algebraMap (O) (F) ϖ ≠ 0) (n : ℤ) :
    transposeInvN (Fin 2) (diagZ (algebraMap (O) (F) ϖ) hπ n) = diagZ (algebraMap (O) (F) ϖ) hπ (-n) := by
  apply Units.ext
  rw [coe_transposeInvN, diagZ_inv hπ, diagZ_eq_diagU hπ, coe_diagU]
  ext i j
  fin_cases i <;> fin_cases j <;> simp

theorem det_diagZ (hπ : algebraMap (O) (F) ϖ ≠ 0) (n : ℤ) :
    ((Matrix.GeneralLinearGroup.det (diagZ (algebraMap (O) (F) ϖ) hπ n) : (HeightOneSpectrum.adicCompletion ℚ v)ˣ) : F) = (algebraMap (O) (F) ϖ) ^ n := by
  rw [Matrix.GeneralLinearGroup.val_det_apply, diagZ_eq_diagU hπ, coe_diagU, Matrix.det_fin_two_of, coe_piUnit_zpow]
  simp

theorem weyl_mul_diagZ_neg {w₀p : G} (hw₀p : (w₀p : Mat) = !![0, 1; 1, 0]) (hπ : algebraMap (O) (F) ϖ ≠ 0) (n : ℤ) :
    w₀p * diagZ (algebraMap (O) (F) ϖ) hπ (-n) =
      Matrix.GeneralLinearGroup.scalar (Fin 2) ((piUnit hπ) ^ (-n)) * (diagZ (algebraMap (O) (F) ϖ) hπ n * w₀p) := by
  have hπn : (algebraMap (O) (F) ϖ) ^ n ≠ 0 := zpow_ne_zero n hπ
  have hπn' : ((ϖ : HeightOneSpectrum.adicCompletionIntegers ℚ v) : HeightOneSpectrum.adicCompletion ℚ v) ^ n ≠ 0 := by
    simpa using hπn
  rw [← scalarPi_zpow_eq_scalar hπ (-n), scalarPi_eq_diagU hπ, diagU_zpow]
  apply Units.ext
  rw [Units.val_mul, Units.val_mul, Units.val_mul, hw₀p, diagZ_eq_diagU hπ, diagZ_eq_diagU hπ, coe_diagU, coe_diagU,
    coe_diagU, coe_piUnit_zpow, coe_piUnit_zpow]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, zpow_neg, hπn, hπn']

theorem weyl_mem_kzero {w₀p : G} (hw₀p : (w₀p : Mat) = !![0, 1; 1, 0]) : w₀p ∈ kzero v := by
  have hinv : w₀p⁻¹ = w₀p := by
    refine inv_eq_of_mul_eq_one_right (Units.ext ?_)
    rw [Units.val_mul, hw₀p, Units.val_one]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
  rw [mem_kzero_iff, hinv, hw₀p]
  refine ⟨?_, ?_⟩ <;> intro i j <;> fin_cases i <;> fin_cases j <;> simp

theorem Bfun_diagZ_mul {w₂ : G → ℂ} {w₀p : G} (hw₀p : (w₀p : Mat) = !![0, 1; 1, 0])
    (ω : (HeightOneSpectrum.adicCompletion ℚ v)ˣ →* ℂˣ)
    (hcentral : ∀ (z : (HeightOneSpectrum.adicCompletion ℚ v)ˣ) (g : G),
      w₂ (Matrix.GeneralLinearGroup.scalar (Fin 2) z * g) = ((ω z : ℂˣ) : ℂ) * w₂ g)
    (hπ : algebraMap (O) (F) ϖ ≠ 0) (n : ℤ) {k : G} (hk : k ∈ kzero v) :
    Ws31.J3dQ.Bfun w₂ w₀p (diagZ (algebraMap (O) (F) ϖ) hπ n * k) =
      ((((‖algebraMap (O) (F) ϖ‖ : ℝ) : ℂ) * (((ω (piUnit hπ))⁻¹ : ℂˣ) : ℂ)) ^ n) *
        w₂ (diagZ (algebraMap (O) (F) ϖ) hπ n * (w₀p * transposeInvN (Fin 2) k)) := by
  simp only [Ws31.J3dQ.Bfun]
  have hdet : ((modulus ((Matrix.GeneralLinearGroup.det (diagZ (algebraMap (O) (F) ϖ) hπ n * k) : (HeightOneSpectrum.adicCompletion ℚ v)ˣ) : F) : ℝ) : ℂ) =
      (((‖algebraMap (O) (F) ϖ‖ : ℝ) : ℂ)) ^ n := by
    rw [map_mul, Units.val_mul, modulus_mul, NNReal.coe_mul, Ws31.J3dQ.modulus_det_of_mem_kzero ℚ v hk, mul_one,
      coe_modulus_eq_norm v, det_diagZ hπ n, norm_zpow, Complex.ofReal_zpow]
  have hw : w₂ (w₀p * transposeInvN (Fin 2) (diagZ (algebraMap (O) (F) ϖ) hπ n * k)) =
      ((((ω (piUnit hπ))⁻¹ : ℂˣ) : ℂ)) ^ n * w₂ (diagZ (algebraMap (O) (F) ϖ) hπ n * (w₀p * transposeInvN (Fin 2) k)) := by
    rw [transposeInvN_mul, transposeInvN_diagZ hπ, ← mul_assoc, weyl_mul_diagZ_neg hw₀p hπ n, mul_assoc, mul_assoc,
      hcentral, map_zpow, zpow_neg, ← inv_zpow, Units.val_zpow_eq_zpow_val]
  rw [hdet, hw, ← mul_assoc, ← mul_zpow]

def modSq : (HeightOneSpectrum.adicCompletion ℚ v)ˣ →* ℂˣ where
  toFun z := Units.mk0 ((((modulus (z : F) : ℝ) : ℂ)) ^ 2)
    (pow_ne_zero _ (Complex.ofReal_ne_zero.2 (NNReal.coe_ne_zero.2 (modulus_ne_zero z.ne_zero))))
  map_one' := Units.ext (by simp)
  map_mul' z w := Units.ext (by simp [modulus_mul, mul_pow])

theorem modSq_apply (z : (HeightOneSpectrum.adicCompletion ℚ v)ˣ) : ((modSq (v := v) z : ℂˣ) : ℂ) = (((modulus (z : F) : ℝ) : ℂ)) ^ 2 := rfl

theorem det_scalar_two (z : (HeightOneSpectrum.adicCompletion ℚ v)ˣ) :
    Matrix.GeneralLinearGroup.det (Matrix.GeneralLinearGroup.scalar (Fin 2) z : G) = z ^ 2 := by
  apply Units.ext
  rw [Matrix.GeneralLinearGroup.val_det_apply, Units.val_pow_eq_pow_val]
  simp [Matrix.GeneralLinearGroup.scalar, Fin.prod_univ_two, pow_two]

theorem Bfun_central {w₂ : G → ℂ} {w₀p : G} (hw₀p : (w₀p : Mat) = !![0, 1; 1, 0])
    (ω : (HeightOneSpectrum.adicCompletion ℚ v)ˣ →* ℂˣ)
    (hcentral : ∀ (z : (HeightOneSpectrum.adicCompletion ℚ v)ˣ) (g : G),
      w₂ (Matrix.GeneralLinearGroup.scalar (Fin 2) z * g) = ((ω z : ℂˣ) : ℂ) * w₂ g)
    (z : (HeightOneSpectrum.adicCompletion ℚ v)ˣ) (g : G) :
    Ws31.J3dQ.Bfun w₂ w₀p (Matrix.GeneralLinearGroup.scalar (Fin 2) z * g) =
      (((modSq (v := v) * ω⁻¹) z : ℂˣ) : ℂ) * Ws31.J3dQ.Bfun w₂ w₀p g := by
  simp only [Ws31.J3dQ.Bfun]
  rw [map_mul, det_scalar_two, transposeInvN_mul, transposeInvN_scalar, ← mul_assoc w₀p, ← scalar_mul_comm, mul_assoc,
    hcentral]
  simp only [MonoidHom.mul_apply, MonoidHom.inv_apply, Units.val_mul, Units.val_pow_eq_pow_val, map_inv, modSq_apply,
    modulus_mul, pow_two, NNReal.coe_mul, Complex.ofReal_mul]
  ring

theorem exists_scalePoly (D : Polynomial ℂ) (ρ : ℂ) (hρ : ρ ≠ 0) :
    ∃ D' : Polynomial ℂ, (∀ i, D'.coeff i = D.coeff i * ρ ^ i) ∧ D'.natDegree = D.natDegree := by
  have hc : ∀ n, (∑ i ∈ Finset.range (D.natDegree + 1), Polynomial.monomial i (D.coeff i * ρ ^ i)).coeff n =
      D.coeff n * ρ ^ n := by
    intro n
    rw [Polynomial.finset_sum_coeff]
    simp only [Polynomial.coeff_monomial]
    rw [Finset.sum_ite_eq']
    split_ifs with h
    · rfl
    · rw [Polynomial.coeff_eq_zero_of_natDegree_lt (by simpa using h), zero_mul]
  refine ⟨∑ i ∈ Finset.range (D.natDegree + 1), Polynomial.monomial i (D.coeff i * ρ ^ i), hc, ?_⟩
  by_cases hD : D = 0
  · subst hD; simp
  apply le_antisymm
  · rw [Polynomial.natDegree_le_iff_coeff_eq_zero]
    intro N hN
    rw [hc, Polynomial.coeff_eq_zero_of_natDegree_lt hN, zero_mul]
  · apply Polynomial.le_natDegree_of_ne_zero
    rw [hc, Polynomial.coeff_natDegree]
    exact mul_ne_zero (Polynomial.leadingCoeff_ne_zero.2 hD) (pow_ne_zero _ hρ)

theorem rho_ne_zero (ω : (HeightOneSpectrum.adicCompletion ℚ v)ˣ →* ℂˣ) (hπ : algebraMap (O) (F) ϖ ≠ 0) :
    (((‖algebraMap (O) (F) ϖ‖ : ℝ) : ℂ) * (((ω (piUnit hπ))⁻¹ : ℂˣ) : ℂ)) ≠ 0 :=
  mul_ne_zero (Complex.ofReal_ne_zero.2 (norm_ne_zero_iff.2 hπ)) (Units.ne_zero _)

theorem Bfun_growth {w₂ : G → ℂ} {w₀p : G} (hw₀p : (w₀p : Mat) = !![0, 1; 1, 0])
    (ω : (HeightOneSpectrum.adicCompletion ℚ v)ˣ →* ℂˣ)
    (hcentral : ∀ (z : (HeightOneSpectrum.adicCompletion ℚ v)ˣ) (g : G),
      w₂ (Matrix.GeneralLinearGroup.scalar (Fin 2) z * g) = ((ω z : ℂˣ) : ℂ) * w₂ g)
    (hπ : algebraMap (O) (F) ϖ ≠ 0)
    (hw₂gr : ∃ (C A : ℝ), ∀ (m : ℤ), 0 ≤ m → ∀ k ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ v ⊤,
      ‖w₂ (diagZ (algebraMap (O) (F) ϖ) hπ m * k)‖ ≤ C * (Ideal.absNorm v.asIdeal : ℝ) ^ (A * m)) :
    ∃ (C A' : ℝ), ∀ (m : ℤ), 0 ≤ m → ∀ k ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ v ⊤,
      ‖Ws31.J3dQ.Bfun w₂ w₀p (diagZ (algebraMap (O) (F) ϖ) hπ m * k)‖ ≤ C * (Ideal.absNorm v.asIdeal : ℝ) ^ (A' * m) := by
  obtain ⟨C, A, hgr⟩ := hw₂gr
  have hq1 : 1 < (Ideal.absNorm v.asIdeal : ℝ) := by rw [← qR_eq_natCast]; exact one_lt_qR v
  have hq0 : 0 < (Ideal.absNorm v.asIdeal : ℝ) := zero_lt_one.trans hq1
  have hr0 : 0 < ‖(((‖algebraMap (O) (F) ϖ‖ : ℝ) : ℂ) * (((ω (piUnit hπ))⁻¹ : ℂˣ) : ℂ))‖ :=
    norm_pos_iff.2 (rho_ne_zero ω hπ)
  obtain ⟨γ, hγ0, hrle⟩ : ∃ γ : ℝ, 0 ≤ γ ∧
      ‖(((‖algebraMap (O) (F) ϖ‖ : ℝ) : ℂ) * (((ω (piUnit hπ))⁻¹ : ℂˣ) : ℂ))‖ ≤ (Ideal.absNorm v.asIdeal : ℝ) ^ γ := by
    refine ⟨max 0 (Real.logb (Ideal.absNorm v.asIdeal : ℝ)
      ‖(((‖algebraMap (O) (F) ϖ‖ : ℝ) : ℂ) * (((ω (piUnit hπ))⁻¹ : ℂˣ) : ℂ))‖), le_max_left _ _, ?_⟩
    calc ‖(((‖algebraMap (O) (F) ϖ‖ : ℝ) : ℂ) * (((ω (piUnit hπ))⁻¹ : ℂˣ) : ℂ))‖
        = (Ideal.absNorm v.asIdeal : ℝ) ^ (Real.logb (Ideal.absNorm v.asIdeal : ℝ)
            ‖(((‖algebraMap (O) (F) ϖ‖ : ℝ) : ℂ) * (((ω (piUnit hπ))⁻¹ : ℂˣ) : ℂ))‖) :=
          (Real.rpow_logb hq0 hq1.ne' hr0).symm
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hq1.le (le_max_right _ _)
  refine ⟨|C|, A + γ, fun m hm k hk => ?_⟩
  obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le hm
  have hk' : w₀p * transposeInvN (Fin 2) k ∈ kzero v :=
    mul_mem (weyl_mem_kzero hw₀p) (Ws31.J3dQ.transposeInvN_mem_kzero ℚ v hk)
  rw [Bfun_diagZ_mul hw₀p ω hcentral hπ (n : ℤ) hk, norm_mul, zpow_natCast, norm_pow]
  have h1 := hgr (n : ℤ) hm _ hk'
  have hXnn : 0 ≤ (Ideal.absNorm v.asIdeal : ℝ) ^ (A * ((n : ℤ) : ℝ)) := Real.rpow_nonneg hq0.le _
  have h2 : ‖w₂ (diagZ (algebraMap (O) (F) ϖ) hπ (n : ℤ) * (w₀p * transposeInvN (Fin 2) k))‖ ≤
      |C| * (Ideal.absNorm v.asIdeal : ℝ) ^ (A * ((n : ℤ) : ℝ)) :=
    h1.trans (mul_le_mul_of_nonneg_right (le_abs_self C) hXnn)
  have h3 : ‖(((‖algebraMap (O) (F) ϖ‖ : ℝ) : ℂ) * (((ω (piUnit hπ))⁻¹ : ℂˣ) : ℂ))‖ ^ n ≤
      (Ideal.absNorm v.asIdeal : ℝ) ^ (γ * ((n : ℤ) : ℝ)) := by
    rw [Int.cast_natCast, Real.rpow_mul hq0.le, Real.rpow_natCast]
    exact pow_le_pow_left₀ hr0.le hrle n
  calc ‖(((‖algebraMap (O) (F) ϖ‖ : ℝ) : ℂ) * (((ω (piUnit hπ))⁻¹ : ℂˣ) : ℂ))‖ ^ n *
        ‖w₂ (diagZ (algebraMap (O) (F) ϖ) hπ (n : ℤ) * (w₀p * transposeInvN (Fin 2) k))‖
      ≤ (Ideal.absNorm v.asIdeal : ℝ) ^ (γ * ((n : ℤ) : ℝ)) * (|C| * (Ideal.absNorm v.asIdeal : ℝ) ^ (A * ((n : ℤ) : ℝ))) :=
        mul_le_mul h3 h2 (norm_nonneg _) (Real.rpow_nonneg hq0.le _)
    _ = |C| * (Ideal.absNorm v.asIdeal : ℝ) ^ ((A + γ) * ((n : ℤ) : ℝ)) := by
        rw [add_mul, Real.rpow_add hq0]; ring

theorem Bfun_rec {w₂ : G → ℂ} {w₀p : G} (hw₀p : (w₀p : Mat) = !![0, 1; 1, 0])
    (ω : (HeightOneSpectrum.adicCompletion ℚ v)ˣ →* ℂˣ)
    (hcentral : ∀ (z : (HeightOneSpectrum.adicCompletion ℚ v)ˣ) (g : G),
      w₂ (Matrix.GeneralLinearGroup.scalar (Fin 2) z * g) = ((ω z : ℂˣ) : ℂ) * w₂ g)
    (hπ : algebraMap (O) (F) ϖ ≠ 0)
    (hw₂rec : ∃ (N₁ : ℤ) (D : Polynomial ℂ) (M : ℕ), D.eval 0 ≠ 0 ∧
      ∀ k ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ v ⊤,
        (∀ m : ℤ, m < N₁ → w₂ (diagZ (algebraMap (O) (F) ϖ) hπ m * k) = 0) ∧
        (∀ m : ℕ, M ≤ m →
          ∑ i ∈ Finset.range (D.natDegree + 1),
            D.coeff i * w₂ (diagZ (algebraMap (O) (F) ϖ) hπ (N₁ + (m : ℤ) - (i : ℤ)) * k) = 0)) :
    ∃ (N₁ : ℤ) (D : Polynomial ℂ) (M : ℕ), D.eval 0 ≠ 0 ∧
      ∀ k ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ v ⊤,
        (∀ m : ℤ, m < N₁ → Ws31.J3dQ.Bfun w₂ w₀p (diagZ (algebraMap (O) (F) ϖ) hπ m * k) = 0) ∧
        (∀ m : ℕ, M ≤ m →
          ∑ i ∈ Finset.range (D.natDegree + 1),
            D.coeff i * Ws31.J3dQ.Bfun w₂ w₀p (diagZ (algebraMap (O) (F) ϖ) hπ (N₁ + (m : ℤ) - (i : ℤ)) * k) = 0) := by
  obtain ⟨N₁, D, M, hD0, hrec⟩ := hw₂rec
  have hρ0 := rho_ne_zero ω hπ
  obtain ⟨D', hD'c, hD'd⟩ := exists_scalePoly D _ hρ0
  refine ⟨N₁, D', M, ?_, fun k hk => ?_⟩
  · rw [← Polynomial.coeff_zero_eq_eval_zero, hD'c, pow_zero, mul_one, Polynomial.coeff_zero_eq_eval_zero]
    exact hD0
  have hk' : w₀p * transposeInvN (Fin 2) k ∈ kzero v :=
    mul_mem (weyl_mem_kzero hw₀p) (Ws31.J3dQ.transposeInvN_mem_kzero ℚ v hk)
  obtain ⟨hvan, hrc⟩ := hrec _ hk'
  refine ⟨fun m hm => ?_, fun m hm => ?_⟩
  · rw [Bfun_diagZ_mul hw₀p ω hcentral hπ m hk, hvan m hm, mul_zero]
  · rw [hD'd]
    have key : ∀ i ∈ Finset.range (D.natDegree + 1),
        D'.coeff i * Ws31.J3dQ.Bfun w₂ w₀p (diagZ (algebraMap (O) (F) ϖ) hπ (N₁ + (m : ℤ) - (i : ℤ)) * k) =
          ((((‖algebraMap (O) (F) ϖ‖ : ℝ) : ℂ) * (((ω (piUnit hπ))⁻¹ : ℂˣ) : ℂ)) ^ (N₁ + (m : ℤ))) *
            (D.coeff i * w₂ (diagZ (algebraMap (O) (F) ϖ) hπ (N₁ + (m : ℤ) - (i : ℤ)) * (w₀p * transposeInvN (Fin 2) k))) := by
      intro i _
      rw [hD'c, Bfun_diagZ_mul hw₀p ω hcentral hπ _ hk]
      have hz : (((‖algebraMap (O) (F) ϖ‖ : ℝ) : ℂ) * (((ω (piUnit hπ))⁻¹ : ℂˣ) : ℂ)) ^ (i : ℕ) *
          (((‖algebraMap (O) (F) ϖ‖ : ℝ) : ℂ) * (((ω (piUnit hπ))⁻¹ : ℂˣ) : ℂ)) ^ (N₁ + (m : ℤ) - (i : ℤ)) =
          (((‖algebraMap (O) (F) ϖ‖ : ℝ) : ℂ) * (((ω (piUnit hπ))⁻¹ : ℂˣ) : ℂ)) ^ (N₁ + (m : ℤ)) := by
        rw [← zpow_natCast, ← zpow_add₀ hρ0]
        congr 1
        ring
      calc _ = ((((‖algebraMap (O) (F) ϖ‖ : ℝ) : ℂ) * (((ω (piUnit hπ))⁻¹ : ℂˣ) : ℂ)) ^ (i : ℕ) *
            (((‖algebraMap (O) (F) ϖ‖ : ℝ) : ℂ) * (((ω (piUnit hπ))⁻¹ : ℂˣ) : ℂ)) ^ (N₁ + (m : ℤ) - (i : ℤ))) *
            (D.coeff i * w₂ (diagZ (algebraMap (O) (F) ϖ) hπ (N₁ + (m : ℤ) - (i : ℤ)) * (w₀p * transposeInvN (Fin 2) k))) := by
              ring
        _ = _ := by rw [hz]
    rw [Finset.sum_congr rfl key, ← Finset.mul_sum, hrc m hm, mul_zero]

theorem Afun_shell
    (hϖ : Valued.v (algebraMap (HeightOneSpectrum.adicCompletionIntegers ℚ v) (HeightOneSpectrum.adicCompletion ℚ v) ϖ) =
      WithZero.exp (-1 : ℤ))
    (hπ : algebraMap (O) (F) ϖ ≠ 0) {W₃ : LocalGL3 v → ℂ}
    (hWgauge : ∃ (B : ℝ) (t : ℕ) (C : ℝ), ∀ h : LocalGL3 v,
      (¬ (detSize h * lastRowSup h / minorSup h ^ 2 ≤ B ∧ minorSup h / lastRowSup h ^ 2 ≤ B) → W₃ h = 0) ∧
      (detSize h * lastRowSup h / minorSup h ^ 2 ≤ B ∧ minorSup h / lastRowSup h ^ 2 ≤ B →
        ‖W₃ h‖ ≤ C / ((detSize h * lastRowSup h / minorSup h ^ 2) * (minorSup h / lastRowSup h ^ 2)) ^ t))
    (g₃ : LocalGL3 v) :
    ∃ (m₀ : ℤ) (t : ℕ) (CA : ℝ), ∀ (dn : ℤ × ℤ), ∀ k ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ v ⊤,
      (¬ (m₀ ≤ dn.1 ∧ m₀ ≤ dn.2) →
        Ws31.J3dQ.Afun W₃ g₃ (scalarPi (algebraMap (O) (F) ϖ) hπ ^ dn.2 * diagZ (algebraMap (O) (F) ϖ) hπ dn.1 * k) = 0) ∧
      ‖Ws31.J3dQ.Afun W₃ g₃ (scalarPi (algebraMap (O) (F) ϖ) hπ ^ dn.2 * diagZ (algebraMap (O) (F) ϖ) hπ dn.1 * k)‖ ≤
        CA * (Ideal.absNorm v.asIdeal : ℝ) ^ ((t : ℤ) * (dn.1 + dn.2)) := by
  have hmem : (fun x : LocalGL3 v => W₃ (x * g₃)) ∈ gl3CyclicSubspace W₃ :=
    Submodule.subset_span ⟨g₃, funext fun x => rfl⟩
  obtain ⟨-, B, t, C, hg⟩ :=
    LanglandsTunnell.CubicInduction.forall_mem_gl3CyclicSubspace_exists_gauge_and_exists_gauge_dualWhittakerFn3 W₃ hWgauge _ hmem
  obtain ⟨m₀, -, hm₀⟩ := exists_cutoff v B
  refine ⟨m₀, t, |C|, fun dn k hk => ?_⟩
  have h := gauge_shell hϖ hπ hg hm₀ dn hk
  rw [qR_eq_natCast] at h
  exact h

end
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_forall_exists_rational_rsLocalIntegral_dual_translate_of_shellRecurrence_of_centralChar_of_rationalTorusShell_of_gauge.Ws31 P2MW.S_LanglandsTunnell_RankinSelberg_forall_exists_rational_rsLocalIntegral_dual_translate_of_shellRecurrence_of_centralChar_of_rationalTorusShell_of_gauge.Ws31.J3dQ P2MW.S_LanglandsTunnell_RankinSelberg_forall_exists_rational_rsLocalIntegral_dual_translate_of_shellRecurrence_of_centralChar_of_rationalTorusShell_of_gauge.Ws31.J3dG"

end Ws31.J3dN
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_forall_exists_rational_rsLocalIntegral_dual_translate_of_shellRecurrence_of_centralChar_of_rationalTorusShell_of_gauge.Ws31 P2MW.S_LanglandsTunnell_RankinSelberg_forall_exists_rational_rsLocalIntegral_dual_translate_of_shellRecurrence_of_centralChar_of_rationalTorusShell_of_gauge.Ws31.J3dQ P2MW.S_LanglandsTunnell_RankinSelberg_forall_exists_rational_rsLocalIntegral_dual_translate_of_shellRecurrence_of_centralChar_of_rationalTorusShell_of_gauge.Ws31.J3dG"
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_forall_exists_rational_rsLocalIntegral_dual_translate_of_shellRecurrence_of_centralChar_of_rationalTorusShell_of_gauge.Ws31 P2MW.S_LanglandsTunnell_RankinSelberg_forall_exists_rational_rsLocalIntegral_dual_translate_of_shellRecurrence_of_centralChar_of_rationalTorusShell_of_gauge.Ws31.J3dQ P2MW.S_LanglandsTunnell_RankinSelberg_forall_exists_rational_rsLocalIntegral_dual_translate_of_shellRecurrence_of_centralChar_of_rationalTorusShell_of_gauge.Ws31.J3dG"

attribute [local instance] LanglandsTunnell.TateLocal.localBorel
attribute [local instance] LanglandsTunnell.TateLocal.borelSpace_localBorel
attribute [local instance] AutomorphicForm.localGLBorel
attribute [local instance] AutomorphicForm.borelSpace_localGLBorel

open Ws31.J3dQ Ws31.J3dN in
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
                (N₁ + (m : ℤ) - (i : ℤ)) * k) = 0))

    (w₀p : GL (Fin 2) (p.adicCompletion ℚ))
    (hw₀p : (w₀p : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) = !![0, 1; 1, 0]) :
    ∀ g₃ : LocalGL3 p,
      letI := localGLBorel ℚ p
      haveI := borelSpace_localGLBorel ℚ p
      ∀ (μ₂ : Measure (GL (Fin 2) (p.adicCompletion ℚ))) [μ₂.IsHaarMeasure]
          (μN₂ : Measure ↥(unipotentGL2Hom (R := p.adicCompletion ℚ)).range) [μN₂.IsHaarMeasure],
        ∃ (Pd Qd : Polynomial ℂ) (md : ℤ) (σ₃ : ℝ), Qd ≠ 0 ∧
          ∀ s : ℂ, σ₃ < s.re →
            Integrable (fun g : GL (Fin 2) (p.adicCompletion ℚ) =>
                (dualWhittakerFn3 (fun x => W₃base (x * g₃)) (iotaGL g) *
                  (fun g : GL (Fin 2) (p.adicCompletion ℚ) => ((modulus ((Matrix.GeneralLinearGroup.det g : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) : ℝ) : ℂ) * w₂base (w₀p * transposeInvN (Fin 2) g)) g) *
                  ((modulus ((Matrix.GeneralLinearGroup.det g : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) : ℝ) : ℂ) ^ (s - 1 / 2))
              (μ₂.withDensity (HaarQuotient.density (unipotentGL2Hom (R := p.adicCompletion ℚ)).range μN₂)) ∧
            RSCarrier.rsLocalIntegral μ₂ (unipotentGL2Hom (R := p.adicCompletion ℚ)).range μN₂
                (fun g : GL (Fin 2) (p.adicCompletion ℚ) => (modulus ((Matrix.GeneralLinearGroup.det g : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) : ℝ))
                s (fun g => dualWhittakerFn3 (fun x => W₃base (x * g₃)) (iotaGL g))
                (fun g : GL (Fin 2) (p.adicCompletion ℚ) => ((modulus ((Matrix.GeneralLinearGroup.det g : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) : ℝ) : ℂ) * w₂base (w₀p * transposeInvN (Fin 2) g)) *
                Qd.eval ((Ideal.absNorm p.asIdeal : ℂ) ^ (-s)) =
              (Ideal.absNorm p.asIdeal : ℂ) ^ ((md : ℂ) * s) * Pd.eval ((Ideal.absNorm p.asIdeal : ℂ) ^ (-s)) := by
  intro g₃ μ₂ _ μN₂ _

  have hAsm := smooth_Afun (K := ℚ) (v := p) g₃ hW₃sm
  obtain ⟨U, hU, hAU⟩ := hAsm
  have hAc : Continuous (Afun (K := ℚ) (v := p) W₃base g₃) := by
    have hlc : IsLocallyConstant (Afun (K := ℚ) (v := p) W₃base g₃) := by
      rw [IsLocallyConstant.iff_eventually_eq]
      intro x
      have hopen : IsOpen ((fun h => x * h) '' (U : Set (GL (Fin 2) (p.adicCompletion ℚ)))) :=
        isOpenMap_mul_left x _ hU
      have hmemx : x ∈ (fun h => x * h) '' (U : Set (GL (Fin 2) (p.adicCompletion ℚ))) := ⟨1, U.one_mem, mul_one x⟩
      filter_upwards [hopen.mem_nhds hmemx] with y hy
      obtain ⟨h, hh, rfl⟩ := hy
      exact hAU h hh x
    exact hlc.continuous

  have hArat : ∀ k₀ ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ p ⊤, ∀ (η : (p.adicCompletion ℚ)ˣ →* ℂˣ) (c : ℕ),
      HasConductorExponentAt ℚ p η c → c ≤ b →
      ∀ (μ₂ : Measure (GL (Fin 2) (p.adicCompletion ℚ))) [μ₂.IsHaarMeasure],
        let Arr : ℤ × ℤ → ℂ := fun n =>
          ∫ u in {u : (p.adicCompletion ℚ)ˣ | Valued.v (u : p.adicCompletion ℚ) = 1},
            (∫ k in ((koneT ℚ p b : Subgroup (GL (Fin 2) (p.adicCompletion ℚ))) : Set (GL (Fin 2) (p.adicCompletion ℚ))),
                Afun (K := ℚ) (v := p) W₃base g₃ (scalarPi (algebraMap (p.adicCompletionIntegers ℚ) (p.adicCompletion ℚ) ϖ) hπ ^ n.2 *
                  diagUnitGL2 (Units.mk0 (algebraMap (p.adicCompletionIntegers ℚ) (p.adicCompletion ℚ) ϖ) hπ ^ n.1 * u) * (k₀ * k)) ∂μ₂) * ((η u : ℂˣ) : ℂ)
          ∂(Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ p)))
        ∃ (N₁ : ℤ) (D₁ D₂ : Polynomial ℂ) (M : ℕ), D₁.eval 0 ≠ 0 ∧ D₂.eval 0 ≠ 0 ∧
          (∀ n : ℤ × ℤ, (n.1 < N₁ ∨ n.2 < N₁) → Arr n = 0) ∧
          (∀ m₁ m₂ : ℕ, (M ≤ m₁ ∨ M ≤ m₂) →
            ∑ i ∈ Finset.range (D₁.natDegree + 1), ∑ l ∈ Finset.range (D₂.natDegree + 1),
              D₁.coeff i * D₂.coeff l * Arr (N₁ + (m₁ : ℤ) - (i : ℤ), N₁ + (m₂ : ℤ) - (l : ℤ)) = 0) := by
    intro k₀ hk₀ η c hη hc μ _
    have hb := hβrat g₃ k₀ η c hη hc μ
    dsimp only at hb
    obtain ⟨-, N₁, D₁, D₂, M, h1, h2, h3, h4⟩ := hb
    have hcv : ∀ (a c : ℤ) (u : (p.adicCompletion ℚ)ˣ),
        (∫ k in ((koneT ℚ p b : Subgroup (GL (Fin 2) (p.adicCompletion ℚ))) : Set (GL (Fin 2) (p.adicCompletion ℚ))),
            Afun (K := ℚ) (v := p) W₃base g₃ (scalarPi (algebraMap (p.adicCompletionIntegers ℚ) (p.adicCompletion ℚ) ϖ) hπ ^ a *
              diagUnitGL2 (Units.mk0 (algebraMap (p.adicCompletionIntegers ℚ) (p.adicCompletion ℚ) ϖ) hπ ^ c * u) * (k₀ * k)) ∂μ) =
        ∫ k in ((kone ℚ p b : Subgroup (GL (Fin 2) (p.adicCompletion ℚ))) : Set (GL (Fin 2) (p.adicCompletion ℚ))),
            Afun (K := ℚ) (v := p) W₃base g₃ (scalarPi (algebraMap (p.adicCompletionIntegers ℚ) (p.adicCompletion ℚ) ϖ) hπ ^ a *
              diagUnitGL2 (Units.mk0 (algebraMap (p.adicCompletionIntegers ℚ) (p.adicCompletion ℚ) ϖ) hπ ^ c * u) *
                (k₀ * transposeInvN (Fin 2) k)) ∂μ := by
      intro a c u
      exact setIntegral_koneT_eq (b := b) μ _ (hAc.comp (continuous_const.mul (continuous_const.mul continuous_id)))
    dsimp only
    simp_rw [hcv]
    exact ⟨N₁, D₁, D₂, M, h1, h2, h3, h4⟩
  exact LanglandsTunnell.RankinSelberg.exists_rational_rsLocalIntegral_of_shellGauge_of_rationalTorusShell_of_shellRecurrence_of_central
    p hπ hϖ b (koneT ℚ p b) (isOpen_koneT ℚ p b) (koneT_le ℚ p b)
    (fun k hk hc => mem_koneT_of_cong ℚ p b k hk hc)
    (Afun (K := ℚ) (v := p) W₃base g₃) (Bfun w₂base w₀p) ⟨U, hU, hAU⟩ (Bfun_mul (w₀p := w₀p) hw₂K)
    (prod_unipotent g₃ hW₃law hw₂law hw₀p)
    (Afun_shell hϖ hπ hWgauge g₃)
    hArat
    (Ws31.J3dN.modSq (v := p) * ω⁻¹) (Bfun_central hw₀p ω hcentral)
    (Bfun_growth hw₀p ω hcentral hπ hw₂gr)
    (Bfun_rec hw₀p ω hcentral hπ hw₂rec)
    μ₂ μN₂

end S_LanglandsTunnell_RankinSelberg_forall_exists_rational_rsLocalIntegral_dual_translate_of_shellRecurrence_of_centralChar_of_rationalTorusShell_of_gauge
end P2MW
export P2MW.S_LanglandsTunnell_RankinSelberg_forall_exists_rational_rsLocalIntegral_dual_translate_of_shellRecurrence_of_centralChar_of_rationalTorusShell_of_gauge (solution)
