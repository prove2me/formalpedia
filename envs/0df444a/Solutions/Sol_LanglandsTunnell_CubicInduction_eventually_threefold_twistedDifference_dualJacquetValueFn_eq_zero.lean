-- Prove2me | solution 1 for LanglandsTunnell.CubicInduction.eventually_threefold_twistedDifference_dualJacquetValueFn_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.353894+00:00
-- url     : https://prove2.me/submissions/2ef5c43f-d98c-54af-93e6-c7840cc91019

import Definitions.Def_LanglandsTunnell_CubicInduction_GlobalZeta31
import Definitions.Def_LanglandsTunnell_CubicInduction_JacquetWhittaker
import Theorems.Thm_LanglandsTunnell_CubicInduction_dualJacquetValueSlices_eventually_eq_and_eq_zero_and_eq_mul_sum
import Definitions.Def_LanglandsTunnell_TateLocalZeta
import Definitions.Def_LanglandsTunnell_StandardLocalConstantsAt
import Definitions.Def_LanglandsTunnell_CubicInduction_LocalZeta31
import Definitions.Def_LanglandsTunnell_CubicInduction_PrincipalSeries3
import Definitions.Def_LanglandsTunnell_CubicInduction_IotaTorus
import Theorems.Thm_LanglandsTunnell_TateLocal_modulus_adicCompletion_eq_nnnorm
import Theorems.Thm_LanglandsTunnell_TateLocal_exists_hasConductorExponentAt_of_continuous
import Theorems.Thm_LanglandsTunnell_CubicInduction_exists_forall_le_integrableOn_and_jacquetTruncated3_eq_of_cellSectionOf
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Algebra.Polynomial.Eval.Defs
import Theorems.Thm_LanglandsTunnell_TateLocal_psiLocal_eq_one_of_mem_integers
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

p2m_attr_erase "ext" "IsDedekindDomain.HeightOneSpectrum.adicCompletion.ext"
namespace P2MW.S_LanglandsTunnell_CubicInduction_eventually_threefold_twistedDifference_dualJacquetValueFn_eq_zero
p2m_attr_erase "instance" "IsDedekindDomain.HeightOneSpectrum.Extension.instAlgebraSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnder IsDedekindDomain.HeightOneSpectrum.Extension.instAlgebraSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnder_1 IsDedekindDomain.HeightOneSpectrum.instMulActionHomClassAlgHomTensorProductAdicCompletionForallValEqUnder_definitions IsDedekindDomain.HeightOneSpectrum.Extension.instAlgebraAdicCompletionValEqUnder IsDedekindDomain.HeightOneSpectrum.adicCompletion.instFiniteForallValEqUnderOfFiniteDimensional_definitions IsDedekindDomain.HeightOneSpectrum.instIsBiscalarSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersTensorProductCoeAlgHomTensorAdicCompletionIntegersTo IsDedekindDomain.HeightOneSpectrum.Extension.instContinuousSMulAdicCompletionValEqUnder IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsModuleTopology IsDedekindDomain.HeightOneSpectrum.Extension.instFiniteSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnderOfFiniteDimensional IsDedekindDomain.HeightOneSpectrum.adicCompletion.instFiniteValEqUnderOfFiniteDimensional_definitions instIsBiscalarTensorProductCoeAlgHomBaseChange_of_algebraMap IsDedekindDomain.HeightOneSpectrum.instIsScalarTowerSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnder_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsModuleTopologyPi IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions Submodule.instIsTopologicalModuleSubtypeMem Pi.instTopologicalModule IsTopologicalModule.toContinuousSMul IsTopologicalModule.toContinuousAdd instFunLike SemialgHomClass.toSemilinearMapClass instCoeTCSemialgHom SemialgHomClass.toRingHomClass SemialgHomClass.instSemialgHom instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instCountableOfNumberField_definitions"
p2m_attr_erase "simp" "SemialgHom.baseChange_of_algebraMap_tmul_left SemialgHom.baseChangeRightOfAlgebraMap_apply Pi.semialgHomPi_apply Pi.semialgHom_apply Module.Basis.rightBaseChange_apply LinearEquiv.coe_mulLeft LinearEquiv.coe_mulRight WithVal.semialgebraMap_toFun_ofVal Module.Basis.rightBaseChange_repr IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers.tensorCoe_tmul IsDedekindDomain.HeightOneSpectrum.tensorAdicCompletionIntegersTo_tmul SemialgHom.baseChangeRightOfAlgebraMap_coe IsDedekindDomain.HeightOneSpectrum.adicCompletion.integerBaseChangeLinearEquiv_tmul_apply SemialgHom.baseChange_of_algebraMap_tmul_right IsLocalization.map_moduleTensorEquiv_symm_tmul IsLocalization.leftModuleTensorEquiv_apply IsLocalization.moduleLid_symm_apply IsLocalization.leftModuleTensorEquiv_symm_apply IsLocalization.map_moduleTensorEquiv_tmul IsModuleTopology.continuousLinearEquiv_apply AlgEquiv.extendScalars_symm_apply IsModuleTopology.Module.Basis.equivFun_homeo_symm_apply IsModuleTopology.Module.Basis.equivFun_homeo_apply IsModuleTopology.continuousAlgEquivOfIsBiscalar_apply AlgEquiv.extendScalars_apply IsModuleTopology.continuousLinearEquiv_symm_apply SemialgHom.restrictScalars_toFun SemialgHom.mk.sizeOf_spec SemialgHom.mk.injEq SemialgHom.coe_coe coe_mk TensorProduct.RightActions.smul_def TensorProduct.RightActions.Module.TensorProduct.comm_symm_apply_tmul TensorProduct.RightActions.LinearMap.baseChange_id TensorProduct.RightActions.algebraMap_eval TensorProduct.RightActions.Module.TensorProduct.comm_apply_tmul TensorProduct.RightActions.Algebra.TensorProduct.comm_symm_apply_tmul TensorProduct.RightActions.Algebra.TensorProduct.comm_apply_tmul LanglandsTunnell.CubicInduction.translateRepStep_apply_coe LanglandsTunnell.CubicInduction.translateFn_apply"

set_option autoImplicit false

section

open IsDedekindDomain NumberField MeasureTheory
open scoped NNReal ENNReal Pointwise

namespace WeylTranslateZeta
open LanglandsTunnell.TateLocal

variable (K : Type) [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))

section Scaling

private theorem modulus_coe_units_eq (u : (v.adicCompletion K)ˣ) :
    modulus (u : v.adicCompletion K) = distribHaarChar (v.adicCompletion K) u := by
  rw [modulus_of_ne_zero u.ne_zero, Units.mk0_val]

private theorem charExt_mul (χ : (v.adicCompletion K)ˣ →* ℂˣ) (a b : v.adicCompletion K) :
    charExt χ (a * b) = charExt χ a * charExt χ b := by
  by_cases ha : a = 0
  · simp [ha]
  by_cases hb : b = 0
  · simp [hb]
  rw [charExt_of_ne_zero χ (mul_ne_zero ha hb), charExt_of_ne_zero χ ha, charExt_of_ne_zero χ hb,
    ← Units.val_mul, ← map_mul]
  congr 2
  exact Units.ext (by simp)

private theorem selfDualHaarAt_smul_set (u : (v.adicCompletion K)ˣ) (S : Set (v.adicCompletion K)) :
    letI := localBorel K v
    selfDualHaarAt K v (u • S) = (modulus (u : v.adicCompletion K) : ℝ≥0∞) * selfDualHaarAt K v S := by
  letI := localBorel K v
  haveI : BorelSpace (v.adicCompletion K) := borelSpace_localBorel K v
  rw [modulus_coe_units_eq]
  unfold selfDualHaarAt
  simp only [Measure.smul_apply]
  rw [← distribHaarChar_mul (Measure.addHaarMeasure (integersPositiveCompacts K v)) u S]
  exact (mul_smul_comm _ _ _).symm

private theorem map_mul_left_selfDualHaarAt (u : (v.adicCompletion K)ˣ) :
    letI := localBorel K v
    Measure.map (fun x : v.adicCompletion K => (u : v.adicCompletion K) * x) (selfDualHaarAt K v) =
      (modulus (u : v.adicCompletion K) : ℝ≥0∞)⁻¹ • selfDualHaarAt K v := by
  letI := localBorel K v
  haveI : BorelSpace (v.adicCompletion K) := borelSpace_localBorel K v
  have hmul : Measurable fun x : v.adicCompletion K => (u : v.adicCompletion K) * x := measurable_id.const_mul _
  ext S hS
  rw [Measure.map_apply hmul hS, Measure.smul_apply, smul_eq_mul]
  have hpre : (fun x : v.adicCompletion K => (u : v.adicCompletion K) * x) ⁻¹' S = u⁻¹ • S :=
    Set.preimage_smul u S
  rw [hpre, selfDualHaarAt_smul_set, modulus_coe_units_eq, modulus_coe_units_eq, map_inv,
    ENNReal.coe_inv (distribHaarChar_pos (A := v.adicCompletion K) (g := u)).ne']

private theorem lintegral_mul_left_selfDualHaarAt (u : (v.adicCompletion K)ˣ) (g : v.adicCompletion K → ℝ≥0∞) :
    letI := localBorel K v
    ∫⁻ x, g ((u : v.adicCompletion K) * x) ∂(selfDualHaarAt K v) =
      (modulus (u : v.adicCompletion K) : ℝ≥0∞)⁻¹ * ∫⁻ x, g x ∂(selfDualHaarAt K v) := by
  letI := localBorel K v
  haveI : BorelSpace (v.adicCompletion K) := borelSpace_localBorel K v
  rw [← (measurableEmbedding_mulLeft₀ u.ne_zero).lintegral_map g, map_mul_left_selfDualHaarAt]
  simp only [lintegral_smul_measure, smul_eq_mul]

private theorem map_mul_left_mulMeasure (u : (v.adicCompletion K)ˣ) :
    letI := localBorel K v
    Measure.map (fun x : v.adicCompletion K => (u : v.adicCompletion K) * x) (mulMeasure (selfDualHaarAt K v)) =
      mulMeasure (selfDualHaarAt K v) := by
  letI := localBorel K v
  haveI : BorelSpace (v.adicCompletion K) := borelSpace_localBorel K v
  have hc : MeasurableSet ({0}ᶜ : Set (v.adicCompletion K)) := isClosed_singleton.measurableSet.compl
  have hmul : Measurable fun x : v.adicCompletion K => (u : v.adicCompletion K) * x := measurable_id.const_mul _
  ext S hS
  rw [Measure.map_apply hmul hS]
  unfold mulMeasure
  rw [withDensity_apply _ (hmul hS), withDensity_apply _ hS, Measure.restrict_restrict (hmul hS),
    Measure.restrict_restrict hS, ← lintegral_indicator (hmul hS |>.inter hc), ← lintegral_indicator (hS.inter hc)]
  have hpt : ∀ x : v.adicCompletion K,
      ((fun y => (u : v.adicCompletion K) * y) ⁻¹' S ∩ {0}ᶜ).indicator (fun y => ((modulus y : ℝ≥0∞))⁻¹) x =
        (modulus (u : v.adicCompletion K) : ℝ≥0∞) *
          (S ∩ {0}ᶜ).indicator (fun y => ((modulus y : ℝ≥0∞))⁻¹) ((u : v.adicCompletion K) * x) := by
    intro x
    by_cases hx : (u : v.adicCompletion K) * x ∈ S ∩ {0}ᶜ
    · have hx' : x ∈ (fun y => (u : v.adicCompletion K) * y) ⁻¹' S ∩ {0}ᶜ := by
        refine ⟨hx.1, ?_⟩
        intro h0
        exact hx.2 (by simp [Set.mem_singleton_iff.mp h0])
      rw [Set.indicator_of_mem hx', Set.indicator_of_mem hx, modulus_mul, ENNReal.coe_mul,
        ENNReal.mul_inv (Or.inl (ENNReal.coe_ne_zero.mpr (modulus_ne_zero u.ne_zero))) (Or.inl ENNReal.coe_ne_top),
        ← mul_assoc, ENNReal.mul_inv_cancel (ENNReal.coe_ne_zero.mpr (modulus_ne_zero u.ne_zero)) ENNReal.coe_ne_top,
        one_mul]
    · have hx' : x ∉ (fun y => (u : v.adicCompletion K) * y) ⁻¹' S ∩ {0}ᶜ := by
        intro h
        refine hx ⟨h.1, ?_⟩
        intro h0
        exact h.2 (by simp [mul_eq_zero, u.ne_zero] at h0; simp [h0])
      rw [Set.indicator_of_notMem hx', Set.indicator_of_notMem hx, mul_zero]
  simp only [hpt]
  rw [lintegral_const_mul' _ _ ENNReal.coe_ne_top, lintegral_mul_left_selfDualHaarAt,
    ← mul_assoc, ENNReal.mul_inv_cancel (ENNReal.coe_ne_zero.mpr (modulus_ne_zero u.ne_zero)) ENNReal.coe_ne_top,
    one_mul]

private theorem integral_mul_left_mulMeasure (c : v.adicCompletion K) (hc : c ≠ 0) (F : v.adicCompletion K → ℂ) :
    letI := localBorel K v
    ∫ x, F (c * x) ∂(mulMeasure (selfDualHaarAt K v)) = ∫ x, F x ∂(mulMeasure (selfDualHaarAt K v)) := by
  letI := localBorel K v
  haveI : BorelSpace (v.adicCompletion K) := borelSpace_localBorel K v
  have h := map_mul_left_mulMeasure K v (Units.mk0 c hc)
  simp only [Units.val_mk0] at h
  rw [← (measurableEmbedding_mulLeft₀ hc).integral_map F, h]

end Scaling

section MeasureClasses

private theorem selfDualConst_ne_zero :
    ((Ideal.absNorm v.asIdeal : ℝ≥0) ^ (-(addCharLevel (StandardAddChar.psiLocal K v) : ℝ) / 2)) ≠ 0 := by
  have hq : (0 : ℝ≥0) < (Ideal.absNorm v.asIdeal : ℝ≥0) := by
    have h : Ideal.absNorm v.asIdeal ≠ 0 := by
      rw [Ne, Ideal.absNorm_eq_zero_iff]
      exact v.ne_bot
    exact_mod_cast Nat.pos_of_ne_zero h
  exact (NNReal.rpow_pos hq).ne'

private theorem isAddHaarMeasure_selfDualHaarAt :
    letI := localBorel K v
    (selfDualHaarAt K v).IsAddHaarMeasure := by
  letI := localBorel K v
  haveI : BorelSpace (v.adicCompletion K) := borelSpace_localBorel K v
  unfold selfDualHaarAt
  exact Measure.IsAddHaarMeasure.nnreal_smul (Measure.addHaarMeasure (integersPositiveCompacts K v))
    (selfDualConst_ne_zero K v)

private theorem sFinite_selfDualHaarAt :
    letI := localBorel K v
    SFinite (selfDualHaarAt K v) := by
  letI := localBorel K v
  haveI : BorelSpace (v.adicCompletion K) := borelSpace_localBorel K v
  unfold selfDualHaarAt
  infer_instance

private theorem sFinite_mulMeasure_selfDualHaarAt :
    letI := localBorel K v
    SFinite (mulMeasure (selfDualHaarAt K v)) := by
  letI := localBorel K v
  haveI := sFinite_selfDualHaarAt K v
  unfold mulMeasure
  infer_instance

end MeasureClasses

end WeylTranslateZeta
end

section

open Matrix IsDedekindDomain NumberField

namespace WeylTranslateZeta
open LanglandsTunnell.CubicInduction

section TransposeInverse

variable {A : Type*} [CommRing A]

private theorem transposeInv3_mul (g h : GL (Fin 3) A) :
    transposeInv3 (g * h) = transposeInv3 g * transposeInv3 h := by
  refine Units.ext ?_
  change ((((g * h)⁻¹ : GL (Fin 3) A)) : Matrix (Fin 3) (Fin 3) A)ᵀ =
    (((g⁻¹ : GL (Fin 3) A) : Matrix (Fin 3) (Fin 3) A))ᵀ * (((h⁻¹ : GL (Fin 3) A) : Matrix (Fin 3) (Fin 3) A))ᵀ
  rw [_root_.mul_inv_rev, Units.val_mul, Matrix.transpose_mul]

private theorem transposeInv3_one : transposeInv3 (1 : GL (Fin 3) A) = 1 := by
  refine Units.ext ?_
  change ((((1 : GL (Fin 3) A)⁻¹ : GL (Fin 3) A)) : Matrix (Fin 3) (Fin 3) A)ᵀ = ((1 : GL (Fin 3) A) : Matrix _ _ _)
  rw [inv_one, Units.val_one, Matrix.transpose_one]

private theorem coe_inv_diagUnitGL2 (a : Aˣ) :
    (((diagUnitGL2 a)⁻¹ : GL (Fin 2) A) : Matrix (Fin 2) (Fin 2) A) = !![((a⁻¹ : Aˣ) : A), 0; 0, 1] :=
  rfl

private theorem transposeInv3_iotaGL_diagUnitGL2 (a : Aˣ) :
    transposeInv3 (iotaGL (diagUnitGL2 a)) = iotaGL (diagUnitGL2 a⁻¹) := by
  refine Units.ext ?_
  change ((((iotaGL (diagUnitGL2 a))⁻¹ : GL (Fin 3) A)) : Matrix (Fin 3) (Fin 3) A)ᵀ = _
  rw [← map_inv, coe_iotaGL, coe_iotaGL, coe_inv_diagUnitGL2, coe_diagUnitGL2]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [embedMat2, Matrix.transpose_apply]

private theorem coe_longWeyl3_mul_transposeInv3_mul_longWeyl3 (a : Aˣ) (x : A) :
    ((longWeyl3 * transposeInv3 (iotaGL (diagUnitGL2 a) * lowerUnipotent21 x * (weylPrime3 * transposeInv3 1)) *
          longWeyl3 : GL (Fin 3) A) : Matrix (Fin 3) (Fin 3) A) =
      !![0, 1, 0; 1, 0, 0; -(((a⁻¹ : Aˣ) : A) * x), 0, ((a⁻¹ : Aˣ) : A)] := by
  rw [transposeInv3_one, mul_one, transposeInv3_mul, transposeInv3_mul, transposeInv3_iotaGL_diagUnitGL2,
    transposeInv3_lowerUnipotent21, transposeInv3_weylPrime3]
  simp only [Units.val_mul, coe_iotaGL, coe_diagUnitGL2, longWeyl3_coe, weylPrime3_coe, upperUnipotent3_coe]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [embedMat2, Matrix.mul_apply, Fin.sum_univ_three]

end TransposeInverse

section Local

variable (v : HeightOneSpectrum (𝓞 ℚ))

private theorem longWeyl3_eq_antidiagonal3 : (longWeyl3 : LocalGL3 v) = antidiagonal3 v :=
  Units.ext (longWeyl3_coe.trans (antidiagonal3_coe v).symm)

private theorem coe_dualPoint_mul_antidiagonal3 (a : (v.adicCompletion ℚ)ˣ) (x : v.adicCompletion ℚ) :
    ((longWeyl3 * transposeInv3 (iotaGL (diagUnitGL2 a) * lowerUnipotent21 x * (weylPrime3 * transposeInv3 1)) *
          antidiagonal3 v : LocalGL3 v) : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) =
      !![0, 1, 0; 1, 0, 0; -(((a⁻¹ : (v.adicCompletion ℚ)ˣ) : v.adicCompletion ℚ) * x), 0,
        ((a⁻¹ : (v.adicCompletion ℚ)ˣ) : v.adicCompletion ℚ)] := by
  rw [← longWeyl3_eq_antidiagonal3]
  exact coe_longWeyl3_mul_transposeInv3_mul_longWeyl3 a x

end Local

end WeylTranslateZeta
end

section

open Matrix IsDedekindDomain NumberField LanglandsTunnell.TateLocal

namespace WeylTranslateZeta
open LanglandsTunnell.CubicInduction

variable (v : HeightOneSpectrum (𝓞 ℚ))

section DualPoint

private noncomputable def dualCellPoint
    (α β γ : v.adicCompletion ℚ) (a : (v.adicCompletion ℚ)ˣ) (x : v.adicCompletion ℚ) :
    LocalGL3 v :=
  antidiagonal3 v * upperUnipotent3 α β γ *
    (longWeyl3 * transposeInv3 (iotaGL (diagUnitGL2 a) * lowerUnipotent21 x * (weylPrime3 * transposeInv3 1)) *
      antidiagonal3 v)

private theorem dualCellPoint_coe (α β γ : v.adicCompletion ℚ) (a : (v.adicCompletion ℚ)ˣ) (x : v.adicCompletion ℚ) :
    (dualCellPoint v α β γ a x : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) =
      !![-(x * (a : v.adicCompletion ℚ)⁻¹), 0, (a : v.adicCompletion ℚ)⁻¹;
        1 - β * (x * (a : v.adicCompletion ℚ)⁻¹), 0, β * (a : v.adicCompletion ℚ)⁻¹;
        α - γ * (x * (a : v.adicCompletion ℚ)⁻¹), 1, γ * (a : v.adicCompletion ℚ)⁻¹] := by
  rw [dualCellPoint, Units.val_mul, coe_dualPoint_mul_antidiagonal3, Units.val_mul, antidiagonal3_coe,
    upperUnipotent3_coe]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three] <;> ring

private theorem gl3Entry_dualCellPoint
    (α β γ : v.adicCompletion ℚ) (a : (v.adicCompletion ℚ)ˣ) (x : v.adicCompletion ℚ)
    (i j : Fin 3) :
    gl3Entry v (dualCellPoint v α β γ a x) i j =
      !![-(x * (a : v.adicCompletion ℚ)⁻¹), 0, (a : v.adicCompletion ℚ)⁻¹;
        1 - β * (x * (a : v.adicCompletion ℚ)⁻¹), 0, β * (a : v.adicCompletion ℚ)⁻¹;
        α - γ * (x * (a : v.adicCompletion ℚ)⁻¹), 1, γ * (a : v.adicCompletion ℚ)⁻¹] i j := by
  rw [gl3Entry, dualCellPoint_coe]

private theorem cornerEntry_dualCellPoint (α β γ : v.adicCompletion ℚ) (a : (v.adicCompletion ℚ)ˣ)
    (x : v.adicCompletion ℚ) :
    cornerEntry v (dualCellPoint v α β γ a x) = α - γ * x / a := by
  simp only [cornerEntry, gl3Entry_dualCellPoint]
  simp
  ring

private theorem lowerMinor_dualCellPoint (α β γ : v.adicCompletion ℚ) (a : (v.adicCompletion ℚ)ˣ)
    (x : v.adicCompletion ℚ) :
    lowerMinor v (dualCellPoint v α β γ a x) = 1 - β * x / a := by
  simp only [lowerMinor, gl3Entry_dualCellPoint]
  simp
  ring

private theorem outerMinor_dualCellPoint (α β γ : v.adicCompletion ℚ) (a : (v.adicCompletion ℚ)ˣ)
    (x : v.adicCompletion ℚ) :
    outerMinor v (dualCellPoint v α β γ a x) = (γ - α * β) / a := by
  simp only [outerMinor, gl3Entry_dualCellPoint]
  simp
  ring

private theorem gl3Det_dualCellPoint
    (α β γ : v.adicCompletion ℚ) (a : (v.adicCompletion ℚ)ˣ) (x : v.adicCompletion ℚ) :
    gl3Det v (dualCellPoint v α β γ a x) = (a : v.adicCompletion ℚ)⁻¹ := by
  rw [gl3Det, dualCellPoint_coe, Matrix.det_fin_three]
  simp
  ring

private theorem cellRatio_dualCellPoint
    (α β γ : v.adicCompletion ℚ) (a : (v.adicCompletion ℚ)ˣ) (x : v.adicCompletion ℚ) :
    cellRatio v (dualCellPoint v α β γ a x) =
      ![1 / (α - γ * x / a), γ * (a : v.adicCompletion ℚ)⁻¹ / (α - γ * x / a),
        (γ - α * β) / a / (1 - β * x / a)] := by
  rw [cellRatio, cornerEntry_dualCellPoint, outerMinor_dualCellPoint, lowerMinor_dualCellPoint]
  simp [gl3Entry_dualCellPoint]

end DualPoint

end WeylTranslateZeta
end

section

open MeasureTheory
open IsDedekindDomain
open NumberField
open LanglandsTunnell.TateLocal
open NumberField.StandardAddChar
open scoped Topology

namespace WeylTranslateZeta
open LanglandsTunnell.CubicInduction

section TorusValues

variable (v : HeightOneSpectrum (𝓞 ℚ))
variable (ν : Fin 3 → ((v.adicCompletion ℚ)ˣ →* ℂˣ)) (Φ : (Fin 3 → v.adicCompletion ℚ) → ℂ)

private theorem exists_invariance_radius (hΦl : IsLocallyConstant Φ) (hΦc : HasCompactSupport Φ) :
    ∃ r : ℝ, 0 < r ∧ ∀ p q : Fin 3 → v.adicCompletion ℚ, (∀ i, ‖q i - p i‖ ≤ r) → Φ q = Φ p := by
  classical

  have hultra : ∀ a b c : v.adicCompletion ℚ, dist a c ≤ max (dist a b) (dist b c) :=
    fun a b c => IsUltrametricDist.dist_triangle_max a b c
  have hK : IsCompact (tsupport Φ) := hΦc

  have hball : ∀ x : tsupport Φ, ∃ ε : ℝ, 0 < ε ∧ ∀ q, dist q (x : Fin 3 → v.adicCompletion ℚ) < ε → Φ q = Φ x := by
    intro x
    have hopen : IsOpen {q : Fin 3 → v.adicCompletion ℚ | Φ q = Φ x} := hΦl.isOpen_fiber (Φ x)
    obtain ⟨ε, hε, hsub⟩ := Metric.isOpen_iff.mp hopen (x : Fin 3 → v.adicCompletion ℚ) rfl
    exact ⟨ε, hε, fun q hq => hsub hq⟩
  choose ε hεpos hε using hball
  obtain ⟨J, hJ⟩ := hK.elim_finite_subcover (fun x : tsupport Φ => Metric.ball (x : Fin 3 → v.adicCompletion ℚ) (ε x))
    (fun x => Metric.isOpen_ball) fun y hy => Set.mem_iUnion.mpr ⟨⟨y, hy⟩, Metric.mem_ball_self (hεpos ⟨y, hy⟩)⟩

  obtain ⟨r, hr, hrJ⟩ : ∃ r : ℝ, 0 < r ∧ ∀ x ∈ J, r < ε x := by
    by_cases hJne : J.Nonempty
    · have hinf : 0 < J.inf' hJne ε := (Finset.lt_inf'_iff hJne).mpr fun y _ => hεpos y
      exact ⟨J.inf' hJne ε / 2, half_pos hinf, fun x hx => (half_lt_self hinf).trans_le (Finset.inf'_le ε hx)⟩
    · exact ⟨1, one_pos, fun x hx => absurd ⟨x, hx⟩ hJne⟩
  refine ⟨r, hr, ?_⟩

  have key : ∀ p q : Fin 3 → v.adicCompletion ℚ, (∀ i, ‖q i - p i‖ ≤ r) → p ∈ tsupport Φ → Φ q = Φ p := by
    intro p q hpq hp
    obtain ⟨x, hxJ, hpx⟩ := Set.mem_iUnion₂.mp (hJ hp)
    have hpx' : dist p (x : Fin 3 → v.adicCompletion ℚ) < ε x := hpx
    have hqx : dist q (x : Fin 3 → v.adicCompletion ℚ) < ε x := by
      rw [dist_pi_lt_iff (hεpos x)] at hpx' ⊢
      intro i
      refine (hultra (q i) (p i) ((x : Fin 3 → v.adicCompletion ℚ) i)).trans_lt (max_lt ?_ (hpx' i))
      rw [dist_eq_norm]
      exact (hpq i).trans_lt (hrJ x hxJ)
    rw [hε x q hqx, hε x p hpx']
  intro p q hpq
  by_cases hp : p ∈ tsupport Φ
  · exact key p q hpq hp
  by_cases hq : q ∈ tsupport Φ
  · refine (key q p (fun i => ?_) hq).symm
    rw [norm_sub_rev]
    exact hpq i
  rw [image_eq_zero_of_notMem_tsupport hp, image_eq_zero_of_notMem_tsupport hq]

private theorem exists_support_radius (hΦc : HasCompactSupport Φ) :
    ∃ R : ℝ, ∀ p : Fin 3 → v.adicCompletion ℚ, Φ p ≠ 0 → ∀ i, ‖p i‖ ≤ R := by
  have hK : IsCompact (tsupport Φ) := hΦc
  choose C hC using fun i : Fin 3 =>
    hK.exists_bound_of_continuousOn
      ((continuous_apply i).continuousOn : ContinuousOn (fun p : Fin 3 → v.adicCompletion ℚ => p i) (tsupport Φ))
  refine ⟨∑ i, max (C i) 0, fun p hp i => ?_⟩
  have hpK : p ∈ tsupport Φ := subset_tsupport Φ hp
  calc ‖p i‖ ≤ C i := hC i p hpK
    _ ≤ max (C i) 0 := le_max_left _ _
    _ ≤ ∑ j, max (C j) 0 :=
        Finset.single_le_sum (f := fun j => max (C j) 0) (fun j _ => le_max_right _ _) (Finset.mem_univ i)

private theorem norm_le_zpow_of_valued_le {x : v.adicCompletion ℚ} {n : ℤ} (hx : Valued.v x ≤ WithZero.exp n) :
    ‖x‖ ≤ (Ideal.absNorm v.asIdeal : ℝ) ^ n := by
  have hexp : WithZeroMulInt.toNNReal (NumberField.HeightOneSpectrum.absNorm_ne_zero v) (WithZero.exp n) =
      (Ideal.absNorm v.asIdeal : NNReal) ^ n := by
    rw [WithZeroMulInt.toNNReal_neg_apply _ WithZero.exp_ne_zero]
    rfl
  have hkey : WithZeroMulInt.toNNReal (NumberField.HeightOneSpectrum.absNorm_ne_zero v) (Valued.v x) ≤
      WithZeroMulInt.toNNReal (NumberField.HeightOneSpectrum.absNorm_ne_zero v) (WithZero.exp n) :=
    (WithZeroMulInt.toNNReal_strictMono (NumberField.HeightOneSpectrum.one_lt_absNorm_nnreal (v := v))).monotone hx
  have h2 : (WithZeroMulInt.toNNReal (NumberField.HeightOneSpectrum.absNorm_ne_zero v) (Valued.v x) : ℝ) ≤
      (((Ideal.absNorm v.asIdeal : NNReal) ^ n : NNReal) : ℝ) :=
    NNReal.coe_le_coe.mpr (hkey.trans_eq hexp)
  rw [NumberField.FinitePlace.norm_def v x]
  exact_mod_cast h2

private theorem valued_le_of_norm_le_zpow
    {x : v.adicCompletion ℚ} {n : ℤ} (hx : ‖x‖ ≤ (Ideal.absNorm v.asIdeal : ℝ) ^ n) :
    Valued.v x ≤ WithZero.exp n := by
  have hexp : WithZeroMulInt.toNNReal (NumberField.HeightOneSpectrum.absNorm_ne_zero v) (WithZero.exp n) =
      (Ideal.absNorm v.asIdeal : NNReal) ^ n := by
    rw [WithZeroMulInt.toNNReal_neg_apply _ WithZero.exp_ne_zero]
    rfl
  have hx' : (WithZeroMulInt.toNNReal (NumberField.HeightOneSpectrum.absNorm_ne_zero v) (Valued.v x) : ℝ) ≤
      (((Ideal.absNorm v.asIdeal : NNReal) ^ n : NNReal) : ℝ) := by
    rw [NumberField.FinitePlace.norm_def v x] at hx
    exact_mod_cast hx
  have hkey : WithZeroMulInt.toNNReal (NumberField.HeightOneSpectrum.absNorm_ne_zero v) (Valued.v x) ≤
      WithZeroMulInt.toNNReal (NumberField.HeightOneSpectrum.absNorm_ne_zero v) (WithZero.exp n) := by
    rw [hexp]
    exact NNReal.coe_le_coe.mp hx'
  have hmono := WithZeroMulInt.toNNReal_strictMono (NumberField.HeightOneSpectrum.one_lt_absNorm_nnreal (v := v))
  exact hmono.le_iff_le.mp hkey

private theorem norm_eq_one_of_valued_eq_one {u : v.adicCompletion ℚ} (hu : Valued.v u = 1) : ‖u‖ = 1 := by
  rw [NumberField.FinitePlace.norm_def v u, hu, map_one, NNReal.coe_one]

private theorem modulus_real_eq_norm (x : v.adicCompletion ℚ) : (modulus x : ℝ) = ‖x‖ := by
  rw [modulus_adicCompletion_eq_nnnorm ℚ v x, coe_nnnorm]

private theorem one_lt_absNorm_real : (1 : ℝ) < (Ideal.absNorm v.asIdeal : ℝ) := by
  exact_mod_cast NumberField.HeightOneSpectrum.one_lt_absNorm (v := v)

private theorem valued_eq_one_of_valued_sub_one_le {u : v.adicCompletion ℚ} {k : ℕ} (hk : 1 ≤ k)
    (hu : Valued.v (u - 1) ≤ WithZero.exp (-(k : ℤ))) : Valued.v u = 1 := by
  have hlt : Valued.v (u - 1) < Valued.v (1 : v.adicCompletion ℚ) := by
    rw [Valuation.map_one]
    refine lt_of_le_of_lt hu ?_
    rw [← WithZero.exp_zero]
    exact WithZero.exp_lt_exp.mpr (by omega)
  have h := Valued.v.map_add_eq_of_lt_right hlt
  rwa [sub_add_cancel, Valuation.map_one] at h

private theorem isClosed_valued_le (n : ℤ) : IsClosed {x : v.adicCompletion ℚ | Valued.v x ≤ WithZero.exp n} := by
  obtain ⟨y₀, hy₀⟩ := HeightOneSpectrum.valuedAdicCompletion_surjective ℚ v (WithZero.exp n)
  have hset : {x : v.adicCompletion ℚ | Valued.v x ≤ WithZero.exp n}
      = {x | Valued.v.restrict x ≤ Valued.v.restrict y₀} := by
    ext x
    simp only [Set.mem_setOf_eq]
    rw [Valuation.restrict_le_iff, hy₀]
  rw [hset]
  exact Valued.isClosed_closedBall _ _

private theorem measurableSet_unipotentBall3 (c : ℤ) :
    letI := localBorel ℚ v
    MeasurableSet (unipotentBall3 v c) := by
  letI := localBorel ℚ v
  haveI : BorelSpace (v.adicCompletion ℚ) := borelSpace_localBorel ℚ v
  have hset : unipotentBall3 v c =
      (Prod.fst ⁻¹' {x : v.adicCompletion ℚ | Valued.v x ≤ WithZero.exp c}) ∩
        ((fun p : v.adicCompletion ℚ × v.adicCompletion ℚ × v.adicCompletion ℚ => p.2.1) ⁻¹'
          {x : v.adicCompletion ℚ | Valued.v x ≤ WithZero.exp c}) ∩
        ((fun p : v.adicCompletion ℚ × v.adicCompletion ℚ × v.adicCompletion ℚ => p.2.2) ⁻¹'
          {x : v.adicCompletion ℚ | Valued.v x ≤ WithZero.exp (2 * c)}) := by
    ext p
    simp only [unipotentBall3, Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_preimage, and_assoc]
  rw [hset]
  exact (((isClosed_valued_le v c).measurableSet.preimage measurable_fst).inter
    ((isClosed_valued_le v c).measurableSet.preimage (measurable_fst.comp measurable_snd))).inter
    ((isClosed_valued_le v (2 * c)).measurableSet.preimage (measurable_snd.comp measurable_snd))

end TorusValues

end WeylTranslateZeta
end

section

open NumberField NumberField.AdelicLevel IsDedekindDomain MeasureTheory
open LanglandsTunnell.TateLocal
open scoped NNReal ENNReal

open Polynomial in

private def IsLaurentInQPow (q : ℂ) (P : ℂ → ℂ) : Prop :=
  ∃ (Q : Polynomial ℂ) (m : ℕ), ∀ s : ℂ, P s = Q.eval (q ^ (-s)) * q ^ ((m : ℂ) * s)

namespace IsLaurentInQPow

variable {q : ℂ}

private theorem mul (hq : q ≠ 0) {P₁ P₂ : ℂ → ℂ} (h₁ : IsLaurentInQPow q P₁) (h₂ : IsLaurentInQPow q P₂) :
    IsLaurentInQPow q fun s => P₁ s * P₂ s := by
  obtain ⟨Q₁, m₁, e₁⟩ := h₁
  obtain ⟨Q₂, m₂, e₂⟩ := h₂
  refine ⟨Q₁ * Q₂, m₁ + m₂, fun s => ?_⟩
  show P₁ s * P₂ s = _
  rw [e₁ s, e₂ s, Polynomial.eval_mul, Nat.cast_add, add_mul, Complex.cpow_add _ _ hq]
  ring

private theorem qpow_add_nat_mul_mul_pow (hq : q ≠ 0) (m k : ℕ) (s : ℂ) :
    q ^ (((m + k : ℕ) : ℂ) * s) * (q ^ (-s)) ^ k = q ^ ((m : ℂ) * s) := by
  rw [← Complex.cpow_nat_mul, ← Complex.cpow_add _ _ hq]
  congr 1
  push_cast
  ring

private theorem add (hq : q ≠ 0) {P₁ P₂ : ℂ → ℂ} (h₁ : IsLaurentInQPow q P₁) (h₂ : IsLaurentInQPow q P₂) :
    IsLaurentInQPow q fun s => P₁ s + P₂ s := by
  obtain ⟨Q₁, m₁, e₁⟩ := h₁
  obtain ⟨Q₂, m₂, e₂⟩ := h₂
  refine ⟨Q₁ * Polynomial.X ^ m₂ + Q₂ * Polynomial.X ^ m₁, m₁ + m₂, fun s => ?_⟩
  show P₁ s + P₂ s = _
  rw [e₁ s, e₂ s, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_mul, Polynomial.eval_pow,
    Polynomial.eval_pow, Polynomial.eval_X, add_mul]
  have h₁' := qpow_add_nat_mul_mul_pow hq m₁ m₂ s
  have h₂' := qpow_add_nat_mul_mul_pow hq m₂ m₁ s
  rw [add_comm m₂ m₁] at h₂'
  rw [← h₁', ← h₂']
  ring

end IsLaurentInQPow

namespace LaurentZetaSlot

variable (v : HeightOneSpectrum (𝓞 ℚ))

attribute [local instance] LanglandsTunnell.TateLocal.localBorel
attribute [local instance] LanglandsTunnell.TateLocal.borelSpace_localBorel

private theorem one_lt_absNorm_real : (1 : ℝ) < (Ideal.absNorm v.asIdeal : ℝ) := by
  exact_mod_cast NumberField.HeightOneSpectrum.one_lt_absNorm (v := v)

private theorem _root_.LaurentZetaSlot.absNorm_ne_zero : (Ideal.absNorm v.asIdeal : ℕ) ≠ 0 := by
  intro h0
  have h := one_lt_absNorm_real v
  rw [h0] at h
  norm_num at h

p2m_export "LaurentZetaSlot" "absNorm_ne_zero"

private def shell (j : ℤ) : Set (v.adicCompletion ℚ) := {x | Valued.v x = WithZero.exp (-j)}

private theorem modulus_eq_of_mem_shell {j : ℤ} {x : v.adicCompletion ℚ} (hx : x ∈ shell v j) :
    modulus x = (Ideal.absNorm v.asIdeal : ℝ≥0) ^ (-j) := by
  have hnorm : ‖x‖ = ((WithZeroMulInt.toNNReal (HeightOneSpectrum.absNorm_ne_zero v) (Valued.v x) : ℝ≥0) : ℝ) :=
    FinitePlace.norm_def v x
  have hx' : Valued.v x = WithZero.exp (-j) := hx
  rw [modulus_adicCompletion_eq_nnnorm ℚ v x]
  apply NNReal.coe_injective
  rw [coe_nnnorm, hnorm, hx', WithZeroMulInt.toNNReal_neg_apply _ WithZero.exp_ne_zero]
  have htoAdd : ∀ h : WithZero.exp (-j) ≠ (0 : WithZero (Multiplicative ℤ)),
      Multiplicative.toAdd (WithZero.unzero h) = -j := fun _ => rfl
  rw [htoAdd]

private def unitShell : Set (v.adicCompletion ℚ) := {x | Valued.v x = 1}

private theorem isAddHaarMeasure_selfDualHaarAt' : (selfDualHaarAt ℚ v).IsAddHaarMeasure := by
  exact WeylTranslateZeta.isAddHaarMeasure_selfDualHaarAt ℚ v

private theorem sFinite_mulMeasure_selfDualHaarAt' : SFinite (mulMeasure (selfDualHaarAt ℚ v)) := by
  exact WeylTranslateZeta.sFinite_mulMeasure_selfDualHaarAt ℚ v

attribute [local instance] sFinite_mulMeasure_selfDualHaarAt'

private theorem continuousOn_charExt_compl (χ : (v.adicCompletion ℚ)ˣ →* ℂˣ) (hχ : IsLocallyConstant χ) :
    ContinuousOn (charExt χ) ({0}ᶜ : Set (v.adicCompletion ℚ)) := by
  rw [continuousOn_iff_continuous_restrict]
  have hmk : Continuous fun x : ({0}ᶜ : Set (v.adicCompletion ℚ)) => Units.mk0 (x : v.adicCompletion ℚ) x.2 :=
    Units.isEmbedding_val₀.continuous_iff.mpr continuous_subtype_val
  have hlc : IsLocallyConstant fun x : ({0}ᶜ : Set (v.adicCompletion ℚ)) =>
      ((χ (Units.mk0 (x : v.adicCompletion ℚ) x.2) : ℂˣ) : ℂ) :=
    IsLocallyConstant.comp (IsLocallyConstant.comp_continuous hχ hmk) fun u : ℂˣ => (u : ℂ)
  refine (IsLocallyConstant.continuous hlc).congr fun x => ?_
  simp only [Set.restrict_apply, charExt_of_ne_zero χ x.2]

private theorem measurable_charExt (χ : (v.adicCompletion ℚ)ˣ →* ℂˣ) (hχ : IsLocallyConstant χ) :
    Measurable (charExt χ) :=
  measurable_of_continuousOn_compl_singleton (0 : v.adicCompletion ℚ) (continuousOn_charExt_compl v χ hχ)

private theorem isClopen_shell (j : ℤ) : IsClopen (shell v j) := by
  obtain ⟨x₀, hx₀⟩ := HeightOneSpectrum.valuedAdicCompletion_surjective ℚ v (WithZero.exp (-j))
  have hset : shell v j = {x | Valued.v.restrict x = Valued.v.restrict x₀} := by
    ext x
    simp only [shell, Set.mem_setOf_eq, Valuation.restrict_inj, hx₀]
  have hne : Valued.v.restrict x₀ ≠ 0 := by
    intro h0
    have h1 : Valued.v x₀ = Valued.v (0 : v.adicCompletion ℚ) :=
      (Valuation.restrict_inj Valued.v).mp (by rw [h0, map_zero])
    rw [map_zero, hx₀] at h1
    exact WithZero.exp_ne_zero h1
  rw [hset]
  exact Valued.isClopen_sphere _ hne

private theorem unitShell_eq_shell_zero : unitShell v = shell v 0 := by
  simp only [unitShell, shell, neg_zero, WithZero.exp_zero]

private theorem modulus_eq_one_of_mem_unitShell {x : v.adicCompletion ℚ} (hx : x ∈ unitShell v) : modulus x = 1 := by
  rw [unitShell_eq_shell_zero] at hx
  rw [modulus_eq_of_mem_shell v hx, neg_zero, zpow_zero]

private theorem isClopen_unitShell : IsClopen (unitShell v) := by
  rw [unitShell_eq_shell_zero]
  exact isClopen_shell v 0

private theorem measurableSet_unitShell : MeasurableSet (unitShell v) :=
  (isClopen_unitShell v).isOpen.measurableSet

private theorem unitShell_subset_integers : unitShell v ⊆ (v.adicCompletionIntegers ℚ : Set (v.adicCompletion ℚ)) :=
  fun x hx => by
    rw [SetLike.mem_coe, HeightOneSpectrum.mem_adicCompletionIntegers]
    exact le_of_eq hx

private theorem isCompact_unitShell : IsCompact (unitShell v) := by
  have hO : IsCompact (v.adicCompletionIntegers ℚ : Set (v.adicCompletion ℚ)) := by
    rw [← coe_integersPositiveCompacts ℚ v]
    exact (integersPositiveCompacts ℚ v).isCompact
  exact hO.of_isClosed_subset (isClopen_unitShell v).isClosed (unitShell_subset_integers v)

private theorem shell_subset_compl_zero (j : ℤ) : shell v j ⊆ ({0}ᶜ : Set (v.adicCompletion ℚ)) := by
  intro x hx
  have hx' : Valued.v x = WithZero.exp (-j) := hx
  intro h0
  rw [Set.mem_singleton_iff.mp h0, map_zero] at hx'
  exact WithZero.exp_ne_zero hx'.symm

private theorem mulMeasure_unitShell
    : mulMeasure (selfDualHaarAt ℚ v) (unitShell v) = selfDualHaarAt ℚ v (unitShell v) := by
  rw [mulMeasure, withDensity_apply _ (measurableSet_unitShell v),
    Measure.restrict_restrict (measurableSet_unitShell v)]
  have hsub : unitShell v ∩ {(0 : v.adicCompletion ℚ)}ᶜ = unitShell v := by
    refine Set.inter_eq_left.mpr fun x hx => ?_
    rintro rfl
    simp [unitShell] at hx
  rw [hsub]
  calc ∫⁻ x in unitShell v, ((modulus x : ℝ≥0∞))⁻¹ ∂(selfDualHaarAt ℚ v)
      = ∫⁻ _ in unitShell v, (1 : ℝ≥0∞) ∂(selfDualHaarAt ℚ v) := by
        refine setLIntegral_congr_fun (measurableSet_unitShell v) fun x hx => ?_
        rw [modulus_eq_one_of_mem_unitShell v hx]
        simp
    _ = selfDualHaarAt ℚ v (unitShell v) := by simp

private theorem mulMeasure_unitShell_lt_top : mulMeasure (selfDualHaarAt ℚ v) (unitShell v) < ⊤ := by
  haveI := isAddHaarMeasure_selfDualHaarAt' v
  rw [mulMeasure_unitShell]
  exact (isCompact_unitShell v).measure_lt_top

private scoped instance isFiniteMeasure_restrict_unitShell :
    IsFiniteMeasure ((mulMeasure (selfDualHaarAt ℚ v)).restrict (unitShell v)) :=
  ⟨by rw [Measure.restrict_apply_univ]; exact mulMeasure_unitShell_lt_top v⟩

private noncomputable def twistedDiff (α : ℂ) (f : v.adicCompletion ℚ → ℂ) : v.adicCompletion ℚ → ℂ :=
  fun a => f a - α * f (a / (uniformizerUnit ℚ v : v.adicCompletion ℚ))

private theorem twistedDiff_comm (α β : ℂ) (f : v.adicCompletion ℚ → ℂ) :
    twistedDiff v α (twistedDiff v β f) = twistedDiff v β (twistedDiff v α f) := by
  funext a
  simp only [twistedDiff]
  ring

private theorem integral_mul_left_mulMeasure' (c : v.adicCompletion ℚ) (hc : c ≠ 0) (F : v.adicCompletion ℚ → ℂ) :
    ∫ x, F (c * x) ∂(mulMeasure (selfDualHaarAt ℚ v)) = ∫ x, F x ∂(mulMeasure (selfDualHaarAt ℚ v)) := by
  exact WeylTranslateZeta.integral_mul_left_mulMeasure ℚ v c hc F

private theorem charExt_mul' (χ : (v.adicCompletion ℚ)ˣ →* ℂˣ) (a b : v.adicCompletion ℚ) :
    charExt χ (a * b) = charExt χ a * charExt χ b := by
  exact WeylTranslateZeta.charExt_mul ℚ v χ a b

private noncomputable def slotScalar (η : (v.adicCompletion ℚ)ˣ →* ℂˣ) : ℂ :=
  by classical exact if HasConductorExponentAt ℚ v η 0 then (η (uniformizerUnit ℚ v) : ℂ) else 0

private noncomputable def twistedDiff₃ (α : Fin 3 → ℂ) (f : v.adicCompletion ℚ → ℂ) : v.adicCompletion ℚ → ℂ :=
  twistedDiff v (α 0) (twistedDiff v (α 1) (twistedDiff v (α 2) f))

private noncomputable def unitProj (χ : (v.adicCompletion ℚ)ˣ →* ℂˣ) (f : v.adicCompletion ℚ → ℂ) :
    v.adicCompletion ℚ → ℂ :=
  fun a => (∫ w in unitShell v, f (a * w) * charExt χ w ∂(mulMeasure (selfDualHaarAt ℚ v))) /
    (((mulMeasure (selfDualHaarAt ℚ v)).real (unitShell v) : ℝ) : ℂ)

private theorem measurable_of_eventually_eq {f : v.adicCompletion ℚ → ℂ}
    (hf : ∀ t : v.adicCompletion ℚ, t ≠ 0 → ∀ᶠ t' in nhds t, f t' = f t) : Measurable f :=
  measurable_of_continuousOn_compl_singleton (0 : v.adicCompletion ℚ) fun t ht =>
    (Filter.EventuallyEq.continuousAt (hf t ht)).continuousWithinAt

private theorem charExt_ne_zero (χ : (v.adicCompletion ℚ)ˣ →* ℂˣ) {x : v.adicCompletion ℚ} (hx : x ≠ 0) :
    charExt χ x ≠ 0 := by
  rw [charExt_of_ne_zero χ hx]
  exact Units.ne_zero _

private theorem mul_mem_unitShell_iff {u : v.adicCompletion ℚ} (hu : u ∈ unitShell v) (w : v.adicCompletion ℚ) :
    u * w ∈ unitShell v ↔ w ∈ unitShell v := by
  simp only [unitShell, Set.mem_setOf_eq, map_mul]
  rw [show Valued.v u = 1 from hu, one_mul]

private theorem unitProj_mul_of_mem_unitShell (χ : (v.adicCompletion ℚ)ˣ →* ℂˣ) (f : v.adicCompletion ℚ → ℂ)
    (t : v.adicCompletion ℚ) {u : v.adicCompletion ℚ} (hu : u ∈ unitShell v) :
    unitProj v χ f (t * u) = (charExt χ u)⁻¹ * unitProj v χ f t := by
  have hu0 : u ≠ 0 := fun h => by
    have := hu
    simp only [unitShell, Set.mem_setOf_eq, h, map_zero] at this
    exact zero_ne_one this
  have hcu : charExt χ u ≠ 0 := charExt_ne_zero v χ hu0
  set F : v.adicCompletion ℚ → ℂ :=
    fun w => (unitShell v).indicator (fun w' => f (t * w') * charExt χ w') w with hF
  have hsub : ∫ w, F (u * w) ∂(mulMeasure (selfDualHaarAt ℚ v)) = ∫ w, F w ∂(mulMeasure (selfDualHaarAt ℚ v)) :=
    integral_mul_left_mulMeasure' v u hu0 F
  have hFu : (fun w => F (u * w)) = fun w =>
      charExt χ u * (unitShell v).indicator (fun w' => f (t * u * w') * charExt χ w') w := by
    funext w
    by_cases hw : w ∈ unitShell v
    · have huw : u * w ∈ unitShell v := (mul_mem_unitShell_iff v hu w).mpr hw
      simp only [hF, Set.indicator_of_mem huw, Set.indicator_of_mem hw, charExt_mul', mul_assoc]
      ring
    · have huw : u * w ∉ unitShell v := fun h => hw ((mul_mem_unitShell_iff v hu w).mp h)
      simp only [hF, Set.indicator_of_notMem huw, Set.indicator_of_notMem hw, mul_zero]
  rw [hFu, integral_const_mul, hF, integral_indicator (measurableSet_unitShell v),
    integral_indicator (measurableSet_unitShell v)] at hsub
  simp only [unitProj]
  rw [div_eq_mul_inv, div_eq_mul_inv, ← hsub]
  field_simp

private theorem twistedDiff_eventually_eq (α : ℂ) {g : v.adicCompletion ℚ → ℂ}
    (hg : ∀ t : v.adicCompletion ℚ, t ≠ 0 → ∀ᶠ t' in nhds t, g t' = g t) (t : v.adicCompletion ℚ) (ht : t ≠ 0) :
    ∀ᶠ t' in nhds t, twistedDiff v α g t' = twistedDiff v α g t := by
  have hϖ : (uniformizerUnit ℚ v : v.adicCompletion ℚ) ≠ 0 := (uniformizerUnit ℚ v).ne_zero
  have hdiv : ContinuousAt (fun t' : v.adicCompletion ℚ => t' / (uniformizerUnit ℚ v : v.adicCompletion ℚ)) t :=
    continuousAt_id.div_const _
  have h2 := hdiv.tendsto.eventually (hg _ (div_ne_zero ht hϖ))
  filter_upwards [hg t ht, h2] with t' h1 h2
  simp only [twistedDiff, h1, h2]

private theorem twistedDiff₃_eventually_eq (α : Fin 3 → ℂ) {g : v.adicCompletion ℚ → ℂ}
    (hg : ∀ t : v.adicCompletion ℚ, t ≠ 0 → ∀ᶠ t' in nhds t, g t' = g t) (t : v.adicCompletion ℚ) (ht : t ≠ 0) :
    ∀ᶠ t' in nhds t, twistedDiff₃ v α g t' = twistedDiff₃ v α g t :=
  twistedDiff_eventually_eq v (α 0) (twistedDiff_eventually_eq v (α 1) (twistedDiff_eventually_eq v (α 2) hg)) t ht

private theorem integrableOn_unitShell_of_eventually_eq (χ : (v.adicCompletion ℚ)ˣ →* ℂˣ) (hχ : IsLocallyConstant χ)
    {f : v.adicCompletion ℚ → ℂ} (hf : ∀ t : v.adicCompletion ℚ, t ≠ 0 → ∀ᶠ t' in nhds t, f t' = f t)
    (a : v.adicCompletion ℚ) :
    IntegrableOn (fun w => f (a * w) * charExt χ w) (unitShell v) (mulMeasure (selfDualHaarAt ℚ v)) := by
  have hU : unitShell v ⊆ ({0}ᶜ : Set (v.adicCompletion ℚ)) := by
    rw [unitShell_eq_shell_zero]
    exact shell_subset_compl_zero v 0
  have hcont : ContinuousOn (fun w => f (a * w) * charExt χ w) (unitShell v) := by
    refine ContinuousOn.mul ?_ ((continuousOn_charExt_compl v χ hχ).mono hU)
    by_cases ha : a = 0
    · simp only [ha, zero_mul]
      exact continuousOn_const
    · intro w hw
      have haw : a * w ≠ 0 := mul_ne_zero ha (hU hw)
      exact ((Filter.EventuallyEq.continuousAt (hf (a * w) haw)).comp
        (continuous_const.mul continuous_id).continuousAt).continuousWithinAt
  obtain ⟨M, hM⟩ := (isCompact_unitShell v).exists_bound_of_continuousOn hcont
  refine Measure.integrableOn_of_bounded (mulMeasure_unitShell_lt_top v).ne ?_ (M := M)
    ((ae_restrict_mem (measurableSet_unitShell v)).mono hM)
  exact (((measurable_of_eventually_eq v hf).comp (measurable_const_mul a)).mul
    (measurable_charExt v χ hχ)).aestronglyMeasurable

private theorem unitProj_twistedDiff (χ : (v.adicCompletion ℚ)ˣ →* ℂˣ) (hχ : IsLocallyConstant χ) (α : ℂ)
    {f : v.adicCompletion ℚ → ℂ} (hf : ∀ t : v.adicCompletion ℚ, t ≠ 0 → ∀ᶠ t' in nhds t, f t' = f t) :
    unitProj v χ (twistedDiff v α f) = twistedDiff v α (unitProj v χ f) := by
  funext a
  have h₁ := integrableOn_unitShell_of_eventually_eq v χ hχ hf a
  have h₂ := integrableOn_unitShell_of_eventually_eq v χ hχ hf (a / (uniformizerUnit ℚ v : v.adicCompletion ℚ))
  have hint : (fun w => (f (a * w) - α * f (a * w / (uniformizerUnit ℚ v : v.adicCompletion ℚ))) * charExt χ w) =
      fun w => f (a * w) * charExt χ w -
        α * (f (a / (uniformizerUnit ℚ v : v.adicCompletion ℚ) * w) * charExt χ w) := by
    funext w
    rw [mul_div_right_comm]
    ring
  simp only [unitProj, twistedDiff]
  rw [hint, integral_sub h₁ (h₂.const_mul α), integral_const_mul, sub_div, mul_div_assoc]

private theorem unitProj_twistedDiff₃ (χ : (v.adicCompletion ℚ)ˣ →* ℂˣ) (hχ : IsLocallyConstant χ) (β : Fin 3 → ℂ)
    {f : v.adicCompletion ℚ → ℂ} (hf : ∀ t : v.adicCompletion ℚ, t ≠ 0 → ∀ᶠ t' in nhds t, f t' = f t) :
    unitProj v χ (twistedDiff₃ v β f) = twistedDiff₃ v β (unitProj v χ f) := by
  have hf₂ : ∀ t : v.adicCompletion ℚ, t ≠ 0 → ∀ᶠ t' in nhds t, twistedDiff v (β 2) f t' = twistedDiff v (β 2) f t :=
    fun t ht => twistedDiff_eventually_eq v (β 2) hf t ht
  have hf₁ : ∀ t : v.adicCompletion ℚ, t ≠ 0 → ∀ᶠ t' in nhds t,
      twistedDiff v (β 1) (twistedDiff v (β 2) f) t' = twistedDiff v (β 1) (twistedDiff v (β 2) f) t :=
    fun t ht => twistedDiff_eventually_eq v (β 1) hf₂ t ht
  simp only [twistedDiff₃]
  rw [unitProj_twistedDiff v χ hχ (β 0) hf₁, unitProj_twistedDiff v χ hχ (β 1) hf₂,
    unitProj_twistedDiff v χ hχ (β 2) hf]

end LaurentZetaSlot
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_eventually_threefold_twistedDifference_dualJacquetValueFn_eq_zero.LaurentZetaSlot"
end
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_eventually_threefold_twistedDifference_dualJacquetValueFn_eq_zero.LaurentZetaSlot"

section

namespace WeylTranslateZeta
open LanglandsTunnell.CubicInduction

open MeasureTheory IsDedekindDomain NumberField LanglandsTunnell.TateLocal NumberField.StandardAddChar
open NumberField.AdelicLevel
open LaurentZetaSlot (twistedDiff twistedDiff₃ unitProj slotScalar unitShell)
open scoped Topology NNReal ENNReal

section TorusCollapse

variable (v : HeightOneSpectrum (𝓞 ℚ))

attribute [local instance] LanglandsTunnell.TateLocal.localBorel
attribute [local instance] LanglandsTunnell.TateLocal.borelSpace_localBorel

private theorem valued_le_one_of_norm_le_one {x : v.adicCompletion ℚ} (hx : ‖x‖ ≤ 1) : Valued.v x ≤ 1 := by
  have h := valued_le_of_norm_le_zpow v (x := x) (n := 0) (by rw [zpow_zero]; exact hx)
  rwa [WithZero.exp_zero] at h

private theorem psiLocal_eq_one_of_norm_le_one {x : v.adicCompletion ℚ} (hx : ‖x‖ ≤ 1) : psiLocal ℚ v x = 1 := by
  refine psiLocal_eq_one_of_mem_integers ℚ v x ?_
  rw [HeightOneSpectrum.mem_adicCompletionIntegers]
  exact valued_le_one_of_norm_le_one v hx

private theorem norm_varpi_pos : 0 < ‖(uniformizerUnit ℚ v).val‖ :=
  norm_pos_iff.mpr (uniformizerUnit ℚ v).ne_zero

private theorem norm_varpi_le_one : ‖(uniformizerUnit ℚ v).val‖ ≤ 1 := by
  refine (norm_le_zpow_of_valued_le v (le_of_eq (valued_uniformizerUnit ℚ v))).trans ?_
  rw [zpow_neg_one]
  exact inv_le_one_of_one_le₀ (one_lt_absNorm_real v).le

private theorem norm_div_varpi_le {x : v.adicCompletion ℚ} {η : ℝ}
    (hx : ‖x‖ ≤ η * ‖(uniformizerUnit ℚ v).val‖) :
    ‖x / (uniformizerUnit ℚ v).val‖ ≤ η := by
  rw [norm_div, div_le_iff₀ (norm_varpi_pos v)]
  exact hx

private theorem norm_le_of_norm_le_mul_varpi {x : v.adicCompletion ℚ} {η : ℝ} (hη : 0 ≤ η)
    (hx : ‖x‖ ≤ η * ‖(uniformizerUnit ℚ v).val‖) : ‖x‖ ≤ η :=
  hx.trans (mul_le_of_le_one_right hη (norm_varpi_le_one v))

private theorem varpi_mul_div (x : v.adicCompletion ℚ) :
    (uniformizerUnit ℚ v).val * (x / (uniformizerUnit ℚ v).val) = x := by
  rw [mul_div_assoc', mul_div_cancel_left₀ _ (uniformizerUnit ℚ v).ne_zero]

private theorem norm_mul_of_valued_eq_one {u : v.adicCompletion ℚ} (hu : Valued.v u = 1) (x : v.adicCompletion ℚ) :
    ‖x * u‖ = ‖x‖ := by
  rw [norm_mul, norm_eq_one_of_valued_eq_one v hu, mul_one]

section CellPoint

variable (ν : Fin 3 → ((v.adicCompletion ℚ)ˣ →* ℂˣ))

end CellPoint
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_eventually_threefold_twistedDifference_dualJacquetValueFn_eq_zero.LaurentZetaSlot"

section Truncated

variable (ν : Fin 3 → ((v.adicCompletion ℚ)ˣ →* ℂˣ))

private theorem jacquetValue_eq_mul_of {u u' : LocalGL3 v → ℂ} {κ : ℂ}
    (hu : ∃ c₀ : ℕ, ∀ c : ℤ, (c₀ : ℤ) ≤ c → jacquetTruncated3 v c u = jacquetTruncated3 v c₀ u)
    (hu' : ∃ c₀ : ℕ, ∀ c : ℤ, (c₀ : ℤ) ≤ c → jacquetTruncated3 v c u' = jacquetTruncated3 v c₀ u')
    (h : ∃ c₁ : ℕ, ∀ c : ℤ, (c₁ : ℤ) ≤ c → jacquetTruncated3 v c u = κ * jacquetTruncated3 v c u') :
    jacquetValue v u = κ * jacquetValue v u' := by
  obtain ⟨c₁, h⟩ := h
  set C : ℕ := max c₁ (max (jacquetLevel v u) (jacquetLevel v u')) with hC
  have h₁ : c₁ ≤ C := le_max_left _ _
  have h₂ : jacquetLevel v u ≤ C := le_max_of_le_right (le_max_left _ _)
  have h₃ : jacquetLevel v u' ≤ C := le_max_of_le_right (le_max_right _ _)
  rw [← jacquetTruncated3_eq_jacquetValue v u hu (c := (C : ℤ)) (by exact_mod_cast h₂),
    ← jacquetTruncated3_eq_jacquetValue v u' hu' (c := (C : ℤ)) (by exact_mod_cast h₃)]
  exact h C (by exact_mod_cast h₁)

private theorem jacquetValue_add_of {u u' : LocalGL3 v → ℂ}
    (hu : letI := localBorel ℚ v
      ∃ c₀ : ℕ, ∀ c : ℤ,
          (c₀ : ℤ) ≤ c → IntegrableOn (fun p : v.adicCompletion ℚ × v.adicCompletion ℚ × v.adicCompletion ℚ =>
        psiLocal ℚ v (-(p.1 + p.2.1)) * u (antidiagonal3 v * upperUnipotent3 p.1 p.2.1 p.2.2))
          (unipotentBall3 v c) (jacquetHaar3 v) ∧ jacquetTruncated3 v c u = jacquetTruncated3 v c₀ u)
    (hu' : letI := localBorel ℚ v
      ∃ c₀ : ℕ, ∀ c : ℤ,
          (c₀ : ℤ) ≤ c → IntegrableOn (fun p : v.adicCompletion ℚ × v.adicCompletion ℚ × v.adicCompletion ℚ =>
        psiLocal ℚ v (-(p.1 + p.2.1)) * u' (antidiagonal3 v * upperUnipotent3 p.1 p.2.1 p.2.2))
          (unipotentBall3 v c) (jacquetHaar3 v) ∧ jacquetTruncated3 v c u' = jacquetTruncated3 v c₀ u')
    (huu' : ∃ c₀ : ℕ, ∀ c : ℤ, (c₀ : ℤ) ≤ c →
      jacquetTruncated3 v c (u + u') = jacquetTruncated3 v c₀ (u + u')) :
    jacquetValue v (u + u') = jacquetValue v u + jacquetValue v u' := by
  letI := localBorel ℚ v
  obtain ⟨c₀, h⟩ := hu
  obtain ⟨c₀', h'⟩ := hu'
  set C : ℕ := max (max c₀ c₀') (max (jacquetLevel v u) (max (jacquetLevel v u') (jacquetLevel v (u + u'))))
    with hC
  have hC₀ : c₀ ≤ C := le_max_of_le_left (le_max_left _ _)
  have hC₀' : c₀' ≤ C := le_max_of_le_left (le_max_right _ _)
  have hCu : jacquetLevel v u ≤ C := le_max_of_le_right (le_max_left _ _)
  have hCu' : jacquetLevel v u' ≤ C := le_max_of_le_right (le_max_of_le_right (le_max_left _ _))
  have hCuu' : jacquetLevel v (u + u') ≤ C := le_max_of_le_right (le_max_of_le_right (le_max_right _ _))
  rw [← jacquetTruncated3_eq_jacquetValue v (u + u') huu' (c := (C : ℤ)) (by exact_mod_cast hCuu'),
    ← jacquetTruncated3_eq_jacquetValue v u ⟨c₀, fun c hc => (h c hc).2⟩ (c := (C : ℤ)) (by exact_mod_cast hCu),
    ← jacquetTruncated3_eq_jacquetValue v u' ⟨c₀', fun c hc => (h' c hc).2⟩ (c := (C : ℤ))
      (by exact_mod_cast hCu')]
  exact jacquetTruncated3_add v C u u' (h C (by exact_mod_cast hC₀)).1 (h' C (by exact_mod_cast hC₀')).1

private theorem cellSectionOf_add (Φ Ψ : (Fin 3 → v.adicCompletion ℚ) → ℂ) :
    cellSectionOf v ν (Φ + Ψ) = cellSectionOf v ν Φ + cellSectionOf v ν Ψ := by
  funext g
  by_cases hg : g ∈ bigCell3 v
  · simp only [Pi.add_apply, cellSectionOf_apply_of_mem v ν _ hg, mul_add]
  · simp only [Pi.add_apply, cellSectionOf_apply_of_notMem v ν _ hg, add_zero]

end Truncated
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_eventually_threefold_twistedDifference_dualJacquetValueFn_eq_zero.LaurentZetaSlot"

private theorem twistedDiff_apply (β : ℂ) (f : v.adicCompletion ℚ → ℂ) (x : v.adicCompletion ℚ) :
    twistedDiff v β f x = f x - β * f (x / (uniformizerUnit ℚ v).val) := rfl

private theorem twistedDiff_zero_fun (f : v.adicCompletion ℚ → ℂ) : twistedDiff v 0 f = f := by
  funext x
  rw [twistedDiff_apply, zero_mul, sub_zero]

private theorem twistedDiff_eq_zero_of_ball {g : v.adicCompletion ℚ → ℂ} {η : ℝ} (hη : 0 < η)
    (h : ∀ x : v.adicCompletion ℚ,
        ‖x‖ ≤ η → g x = 0) (β : ℂ) (x : v.adicCompletion ℚ) (hx : ‖x‖ ≤ η * ‖(uniformizerUnit ℚ v).val‖) :
    twistedDiff v β g x = 0 := by
  rw [twistedDiff_apply, h x (norm_le_of_norm_le_mul_varpi v hη.le hx), h _ (norm_div_varpi_le v hx),
    mul_zero, sub_zero]

private theorem twistedDiff_eq_of_ball {f g : v.adicCompletion ℚ → ℂ} {c : ℂ} {η : ℝ} (hη : 0 < η)
    (h : ∀ x : v.adicCompletion ℚ,
        ‖x‖ ≤ η → f x = c * g (x / (uniformizerUnit ℚ v).val)) (β : ℂ) (x : v.adicCompletion ℚ)
    (hx : ‖x‖ ≤ η * ‖(uniformizerUnit ℚ v).val‖) :
    twistedDiff v β f x = c * twistedDiff v β g (x / (uniformizerUnit ℚ v).val) := by
  rw [twistedDiff_apply, twistedDiff_apply, h x (norm_le_of_norm_le_mul_varpi v hη.le hx),
    h _ (norm_div_varpi_le v hx)]
  ring

private theorem twistedDiff_eq_add {f g g' : v.adicCompletion ℚ → ℂ} (h : ∀ x : v.adicCompletion ℚ,
    f x = g x + g' x) (β : ℂ) (x : v.adicCompletion ℚ) :
    twistedDiff v β f x = twistedDiff v β g x + twistedDiff v β g' x := by
  rw [twistedDiff_apply, twistedDiff_apply, twistedDiff_apply, h x, h _]
  ring

private theorem twistedDiff_mul_eq_of_ball {f f' : v.adicCompletion ℚ → ℂ} {θ : ℂ}
    {u : v.adicCompletion ℚ} {η : ℝ} (hη : 0 < η)
    (h : ∀ x : v.adicCompletion ℚ, ‖x‖ ≤ η → f (x * u) = θ * (f x + f' x)) (β : ℂ) (x : v.adicCompletion ℚ)
    (hx : ‖x‖ ≤ η * ‖(uniformizerUnit ℚ v).val‖) :
    twistedDiff v β f (x * u) = θ * (twistedDiff v β f x + twistedDiff v β f' x) := by
  rw [twistedDiff_apply, twistedDiff_apply, twistedDiff_apply, mul_div_right_comm,
    h x (norm_le_of_norm_le_mul_varpi v hη.le hx), h _ (norm_div_varpi_le v hx)]
  ring

private theorem twistedDiff_mul_eq_of_ball'
    {f : v.adicCompletion ℚ → ℂ} {θ : ℂ} {u : v.adicCompletion ℚ} {η : ℝ} (hη : 0 < η)
    (h : ∀ x : v.adicCompletion ℚ,
        ‖x‖ ≤ η → f (x * u) = θ * f x) (β : ℂ) (x : v.adicCompletion ℚ) (hx : ‖x‖ ≤ η * ‖(uniformizerUnit ℚ v).val‖) :
    twistedDiff v β f (x * u) = θ * twistedDiff v β f x := by
  rw [twistedDiff_apply, twistedDiff_apply, mul_div_right_comm, h x (norm_le_of_norm_le_mul_varpi v hη.le hx),
    h _ (norm_div_varpi_le v hx)]
  ring

private theorem eventually_eq_zero_of_ball {g : v.adicCompletion ℚ → ℂ} {η : ℝ} (hη : 0 < η)
    (h : ∀ x : v.adicCompletion ℚ, ‖x‖ ≤ η → g x = 0) : ∀ᶠ x in nhds (0 : v.adicCompletion ℚ), g x = 0 := by
  filter_upwards [Metric.closedBall_mem_nhds (0 : v.adicCompletion ℚ) hη] with x hx
  rw [Metric.mem_closedBall, dist_zero_right] at hx
  exact h x hx

section Projection

variable (χ : (v.adicCompletion ℚ)ˣ →* ℂˣ)

private theorem unitProj_apply (f : v.adicCompletion ℚ → ℂ) (a : v.adicCompletion ℚ) :
    unitProj v χ f a = (∫ w in LaurentZetaSlot.unitShell v, f (a * w) * charExt χ w
      ∂(mulMeasure (selfDualHaarAt ℚ v))) /
        (((mulMeasure (selfDualHaarAt ℚ v)).real (LaurentZetaSlot.unitShell v) : ℝ) : ℂ) := rfl

private theorem unitProj_congr_of_ball {g g' : v.adicCompletion ℚ → ℂ} {η : ℝ}
    (h : ∀ x : v.adicCompletion ℚ, ‖x‖ ≤ η → g x = g' x)
    (a : v.adicCompletion ℚ) (ha : ‖a‖ ≤ η) : unitProj v χ g a = unitProj v χ g' a := by
  rw [unitProj_apply, unitProj_apply]
  congr 1
  refine setIntegral_congr_fun (LaurentZetaSlot.measurableSet_unitShell v) fun w hw => ?_
  have hn : ‖a * w‖ ≤ η := by
    rw [norm_mul_of_valued_eq_one v hw]
    exact ha
  rw [h (a * w) hn]

private theorem unitProj_eq_zero_of_ball
    {g : v.adicCompletion ℚ → ℂ} {η : ℝ} (h : ∀ x : v.adicCompletion ℚ, ‖x‖ ≤ η → g x = 0)
    (a : v.adicCompletion ℚ) (ha : ‖a‖ ≤ η) : unitProj v χ g a = 0 := by
  rw [unitProj_congr_of_ball v χ (g' := fun _ => 0) h a ha, unitProj_apply]
  simp

private theorem unitProj_const_mul (c : ℂ) (g : v.adicCompletion ℚ → ℂ) (a : v.adicCompletion ℚ) :
    unitProj v χ (fun x => c * g x) a = c * unitProj v χ g a := by
  rw [unitProj_apply, unitProj_apply, ← mul_div_assoc, ← integral_const_mul]
  congr 1
  refine setIntegral_congr_fun (LaurentZetaSlot.measurableSet_unitShell v) fun w _ => ?_
  show c * g (a * w) * charExt χ w = c * (g (a * w) * charExt χ w)
  ring

private theorem unitProj_dilate (c : ℂ) (g : v.adicCompletion ℚ → ℂ) (a : v.adicCompletion ℚ) :
    unitProj v χ (fun x => c * g (x / (uniformizerUnit ℚ v).val)) a = c * unitProj v χ g (a /
        (uniformizerUnit ℚ v).val) := by
  rw [unitProj_apply, unitProj_apply, ← mul_div_assoc, ← integral_const_mul]
  congr 1
  refine setIntegral_congr_fun (LaurentZetaSlot.measurableSet_unitShell v) fun w _ => ?_
  show c * g (a * w / (uniformizerUnit ℚ v).val) * charExt χ w = c * (g (a / (uniformizerUnit ℚ
      v).val * w) * charExt χ w)
  rw [mul_div_right_comm]
  ring

private theorem unitProj_eq_of_ball {f g : v.adicCompletion ℚ → ℂ} {c : ℂ} {η : ℝ}
    (h : ∀ x : v.adicCompletion ℚ,
        ‖x‖ ≤ η → f x = c * g (x / (uniformizerUnit ℚ v).val)) (a : v.adicCompletion ℚ) (ha : ‖a‖ ≤ η) :
    unitProj v χ f a = c * unitProj v χ g (a / (uniformizerUnit ℚ v).val) := by
  rw [unitProj_congr_of_ball v χ h a ha, unitProj_dilate]

private theorem unitProj_mul_eq (g : v.adicCompletion ℚ → ℂ) (a u : v.adicCompletion ℚ) :
    unitProj v χ g (a * u) = unitProj v χ (fun x => g (x * u)) a := by
  rw [unitProj_apply, unitProj_apply]
  congr 1
  refine setIntegral_congr_fun (LaurentZetaSlot.measurableSet_unitShell v) fun w _ => ?_
  show g (a * u * w) * charExt χ w = g (a * w * u) * charExt χ w
  rw [mul_right_comm]

private theorem unitProj_eq_add (hχ : IsLocallyConstant χ) {f g g' : v.adicCompletion ℚ → ℂ}
    (hg : ∀ t : v.adicCompletion ℚ, t ≠ 0 → ∀ᶠ t' in nhds t, g t' = g t)
    (hg' : ∀ t : v.adicCompletion ℚ, t ≠ 0 → ∀ᶠ t' in nhds t, g' t' = g' t)
    (h : ∀ x : v.adicCompletion ℚ, f x = g x + g' x) (a : v.adicCompletion ℚ) :
    unitProj v χ f a = unitProj v χ g a + unitProj v χ g' a := by
  rw [unitProj_apply, unitProj_apply, unitProj_apply, ← add_div, ← integral_add
    (LaurentZetaSlot.integrableOn_unitShell_of_eventually_eq v χ hχ hg a)
    (LaurentZetaSlot.integrableOn_unitShell_of_eventually_eq v χ hχ hg' a)]
  congr 1
  refine setIntegral_congr_fun (LaurentZetaSlot.measurableSet_unitShell v) fun w _ => ?_
  rw [h (a * w), add_mul]

private theorem unitProj_eq_zero_of_covariant (hχ : IsLocallyConstant χ) {g g' : v.adicCompletion ℚ → ℂ}
    (hg : ∀ t : v.adicCompletion ℚ, t ≠ 0 → ∀ᶠ t' in nhds t, g t' = g t)
    (hg' : ∀ t : v.adicCompletion ℚ, t ≠ 0 → ∀ᶠ t' in nhds t, g' t' = g' t)
    {θ : ℂ} {u : v.adicCompletion ℚ} (hu : Valued.v u = 1) (hne : θ * charExt χ u ≠ 1) {η η' : ℝ}
    (hcov : ∀ x : v.adicCompletion ℚ, ‖x‖ ≤ η → g (x * u) = θ * (g x + g' x))
    (hres : ∀ x : v.adicCompletion ℚ,
        ‖x‖ ≤ η' → unitProj v χ g' x = 0) (a : v.adicCompletion ℚ) (ha : ‖a‖ ≤ min η η') :
    unitProj v χ g a = 0 := by
  have hu0 : u ≠ 0 := fun h0 => by
    rw [h0, map_zero] at hu
    exact zero_ne_one hu
  have hcu : charExt χ u ≠ 0 := LaurentZetaSlot.charExt_ne_zero v χ hu0
  have h₁ : unitProj v χ g (a * u) = (charExt χ u)⁻¹ * unitProj v χ g a :=
    LaurentZetaSlot.unitProj_mul_of_mem_unitShell v χ g a hu
  have h₂ : unitProj v χ g (a * u) = θ * unitProj v χ g a := by
    rw [unitProj_mul_eq, unitProj_congr_of_ball v χ (g := fun x => g (x * u))
      (g' := fun x => θ * (g x + g' x)) (fun x hx => hcov x hx) a (ha.trans (min_le_left _ _)),
      unitProj_const_mul, unitProj_eq_add v χ hχ hg hg' (f := fun x => g x + g' x) (fun x => rfl) a,
      hres a (ha.trans (min_le_right _ _)), add_zero]
  have h₃ : ((charExt χ u)⁻¹ - θ) * unitProj v χ g a = 0 := by
    rw [sub_mul, ← h₁, ← h₂, sub_self]
  refine (mul_eq_zero.mp h₃).resolve_left ?_
  intro h0
  apply hne
  rw [sub_eq_zero] at h0
  rw [← h0, inv_mul_cancel₀ hcu]

private theorem unitProj_eq_zero_of_covariant' (hχ : IsLocallyConstant χ) {g : v.adicCompletion ℚ → ℂ}
    (hg : ∀ t : v.adicCompletion ℚ, t ≠ 0 → ∀ᶠ t' in nhds t,
        g t' = g t) {θ : ℂ} {u : v.adicCompletion ℚ} (hu : Valued.v u = 1)
    (hne : θ * charExt χ u ≠ 1) {η : ℝ} (hcov : ∀ x : v.adicCompletion ℚ,
        ‖x‖ ≤ η → g (x * u) = θ * g x) (a : v.adicCompletion ℚ)
    (ha : ‖a‖ ≤ η) : unitProj v χ g a = 0 := by
  refine unitProj_eq_zero_of_covariant v χ hχ hg (g' := fun _ => 0)
    (fun t _ => Filter.Eventually.of_forall fun _ => rfl) hu hne (η := η) (η' := η)
    (fun x hx => by simp only [hcov x hx, add_zero]) (fun x _ => ?_) a (le_min ha ha)
  rw [unitProj_apply]
  simp

end Projection
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_eventually_threefold_twistedDifference_dualJacquetValueFn_eq_zero.LaurentZetaSlot"

private theorem slot_dichotomy (χ η : (v.adicCompletion ℚ)ˣ →* ℂˣ) {αi : ℂ}
    (h : αi * (χ (uniformizerUnit ℚ v) : ℂ) = LaurentZetaSlot.slotScalar v (η * χ)) :
    (HasConductorExponentAt ℚ v (η * χ) 0 ∧ αi = (η (uniformizerUnit ℚ v) : ℂ)) ∨
      (¬ HasConductorExponentAt ℚ v (η * χ) 0 ∧ αi = 0) := by
  have hχ0 : (χ (uniformizerUnit ℚ v) : ℂ) ≠ 0 := Units.ne_zero _
  unfold LaurentZetaSlot.slotScalar at h
  by_cases H : HasConductorExponentAt ℚ v (η * χ) 0
  · rw [if_pos H, MonoidHom.mul_apply, Units.val_mul] at h
    exact Or.inl ⟨H, mul_right_cancel₀ hχ0 h⟩
  · rw [if_neg H] at h
    exact Or.inr ⟨H, (mul_eq_zero.mp h).resolve_right hχ0⟩

private theorem exists_unit_of_not_hasConductorExponentAt {η : (v.adicCompletion ℚ)ˣ →* ℂˣ}
    (h : ¬ HasConductorExponentAt ℚ v η 0) : ∃ u : (v.adicCompletion ℚ)ˣ, Valued.v u.val = 1 ∧ η u ≠ 1 := by
  by_contra hcon
  apply h
  rw [hasConductorExponentAt_zero_iff]
  intro u hu
  by_contra hne
  exact hcon ⟨u, hu, hne⟩

private theorem mul_charExt_ne_one
    {χ η : (v.adicCompletion ℚ)ˣ →* ℂˣ} {u : (v.adicCompletion ℚ)ˣ} (hne : (η * χ) u ≠ 1) :
    (η u : ℂ) * charExt χ u.val ≠ 1 := by
  rwa [charExt_coe_units, ← Units.val_mul, ← MonoidHom.mul_apply, ne_eq, Units.val_eq_one]

section Covariances

private def IsTestAdditive (T : ((Fin 3 → v.adicCompletion ℚ) → ℂ) → v.adicCompletion ℚ → ℂ) : Prop :=
  ∀ Φ Ψ : (Fin 3 → v.adicCompletion ℚ) → ℂ, IsLocallyConstant Φ → HasCompactSupport Φ → IsLocallyConstant Ψ →
    HasCompactSupport Ψ → ∀ t : v.adicCompletion ℚ, T (Φ + Ψ) t = T Φ t + T Ψ t

private def IsTestLocallyConstant (T : ((Fin 3 → v.adicCompletion ℚ) → ℂ) → v.adicCompletion ℚ → ℂ) : Prop :=
  ∀ Φ : (Fin 3 → v.adicCompletion ℚ) → ℂ, IsLocallyConstant Φ → HasCompactSupport Φ →
    ∀ t : v.adicCompletion ℚ, t ≠ 0 → ∀ᶠ t' in nhds t, T Φ t' = T Φ t

private def IsTestTransport
    (σ : (v.adicCompletion ℚ)ˣ → (Fin 3 → v.adicCompletion ℚ) → (Fin 3 → v.adicCompletion ℚ)) : Prop :=
  ∀ Φ : (Fin 3 → v.adicCompletion ℚ) → ℂ, IsLocallyConstant Φ → HasCompactSupport Φ →
    ∀ s : (v.adicCompletion ℚ)ˣ, ‖(uniformizerUnit ℚ v).val‖ ≤ ‖s.val‖ → ‖s.val‖ ≤ 1 →
      IsLocallyConstant (Φ ∘ σ s) ∧ HasCompactSupport (Φ ∘ σ s)

variable (φA φB : (Fin 3 → v.adicCompletion ℚ) → v.adicCompletion ℚ)

private def PullbackSubVanishesNear
    (σ : (v.adicCompletion ℚ)ˣ → (Fin 3 → v.adicCompletion ℚ) → (Fin 3 → v.adicCompletion ℚ)) : Prop :=
  ∀ Φ : (Fin 3 → v.adicCompletion ℚ) → ℂ, IsLocallyConstant Φ → HasCompactSupport Φ → ∃ δ : ℝ, 0 < δ ∧
    ∀ s : (v.adicCompletion ℚ)ˣ, ‖(uniformizerUnit ℚ v).val‖ ≤ ‖s.val‖ → ‖s.val‖ ≤ 1 →
      ∀ r, ‖φA r‖ ≤ δ → ‖φB r‖ ≤ δ → (Φ ∘ σ s - Φ) r = 0

variable (T : ((Fin 3 → v.adicCompletion ℚ) → ℂ) → v.adicCompletion ℚ → ℂ)

private def HasPullbackCovariance
    (σ : (v.adicCompletion ℚ)ˣ → (Fin 3 → v.adicCompletion ℚ) → (Fin 3 → v.adicCompletion ℚ))
    (χL : (v.adicCompletion ℚ)ˣ →* ℂˣ) : Prop :=
  ∀ Φ : (Fin 3 → v.adicCompletion ℚ) → ℂ, IsLocallyConstant Φ → HasCompactSupport Φ →
    ∀ s : (v.adicCompletion ℚ)ˣ, ‖(uniformizerUnit ℚ v).val‖ ≤ ‖s.val‖ → ‖s.val‖ ≤ 1 →
      ∃ ε : ℝ, 0 < ε ∧ ∀ t : v.adicCompletion ℚ, ‖t‖ ≤ ε → T Φ (s.val * t) = (χL s : ℂ) * T (Φ ∘ σ s) t

private def HasOuterCovariance (χA : (v.adicCompletion ℚ)ˣ →* ℂˣ) : Prop :=
  ∀ Ψ : (Fin 3 → v.adicCompletion ℚ) → ℂ, IsLocallyConstant Ψ → HasCompactSupport Ψ → ∀ ρ : ℝ, 0 < ρ →
    (∀ r, Ψ r ≠ 0 → ρ < ‖φA r‖) → ∀ s : (v.adicCompletion ℚ)ˣ, ‖(uniformizerUnit ℚ v).val‖ ≤ ‖s.val‖ → ‖s.val‖ ≤ 1 →
      ∃ ε : ℝ, 0 < ε ∧ ∀ t : v.adicCompletion ℚ, ‖t‖ ≤ ε → T Ψ (s.val * t) = (χA s : ℂ) * T Ψ t

private def HasNearDecomposition (χB : (v.adicCompletion ℚ)ˣ →* ℂˣ) : Prop :=
  ∀ Ψ : (Fin 3 → v.adicCompletion ℚ) → ℂ, IsLocallyConstant Ψ → HasCompactSupport Ψ → ∀ δ : ℝ, 0 < δ →
    (∀ r, ‖φA r‖ ≤ δ → ‖φB r‖ ≤ δ → Ψ r = 0) →
      ∃ Ψ₂ Ψ₃ : (Fin 3 → v.adicCompletion ℚ) → ℂ, IsLocallyConstant Ψ₂ ∧ HasCompactSupport Ψ₂ ∧
        IsLocallyConstant Ψ₃ ∧ HasCompactSupport Ψ₃ ∧ Ψ = Ψ₂ + Ψ₃ ∧
        (∃ ρ : ℝ, 0 < ρ ∧ ∀ r, Ψ₂ r ≠ 0 → ρ < ‖φA r‖) ∧
        ∀ s : (v.adicCompletion ℚ)ˣ, ‖(uniformizerUnit ℚ v).val‖ ≤ ‖s.val‖ → ‖s.val‖ ≤ 1 →
          ∃ Ψ₄ : (Fin 3 → v.adicCompletion ℚ) → ℂ, IsLocallyConstant Ψ₄ ∧ HasCompactSupport Ψ₄ ∧
            (∃ ρ : ℝ, 0 < ρ ∧ ∀ r, (Ψ₄ - Ψ₃) r ≠ 0 → ρ < ‖φA r‖) ∧
            ∃ ε : ℝ, 0 < ε ∧ ∀ t : v.adicCompletion ℚ, ‖t‖ ≤ ε → T Ψ₃ (s.val * t) = (χB s : ℂ) * T Ψ₄ t

variable {T}

variable {v} in

private theorem IsTestAdditive.sub (hadd : IsTestAdditive v T) {Φ Ψ : (Fin 3 → v.adicCompletion ℚ) → ℂ}
    (hΦl : IsLocallyConstant Φ) (hΦc : HasCompactSupport Φ) (hΨl : IsLocallyConstant Ψ)
    (hΨc : HasCompactSupport Ψ) (t : v.adicCompletion ℚ) : T (Φ - Ψ) t = T Φ t - T Ψ t := by
  have h := hadd (Φ - Ψ) Ψ (hΦl.sub hΨl) (hΦc.sub hΨc) hΨl hΨc t
  rw [sub_add_cancel] at h
  rw [h, add_sub_cancel_right]

end Covariances
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_eventually_threefold_twistedDifference_dualJacquetValueFn_eq_zero.LaurentZetaSlot"

section Strata

variable {φA φB : (Fin 3 → v.adicCompletion ℚ) → v.adicCompletion ℚ}
variable {T : ((Fin 3 → v.adicCompletion ℚ) → ℂ) → v.adicCompletion ℚ → ℂ}
variable {χA χB : (v.adicCompletion ℚ)ˣ →* ℂˣ}

private theorem twistedDiff_eq_zero_outer (h₂ : HasOuterCovariance v φA T χA) (Ψ : (Fin 3 → v.adicCompletion ℚ) → ℂ)
    (hΨl : IsLocallyConstant Ψ) (hΨc : HasCompactSupport Ψ) {ρ : ℝ} (hρ : 0 < ρ)
    (hsupp : ∀ r, Ψ r ≠ 0 → ρ < ‖φA r‖) :
    ∃ η : ℝ, 0 < η ∧ ∀ x : v.adicCompletion ℚ, ‖x‖ ≤ η → twistedDiff v (χA (uniformizerUnit ℚ v) : ℂ) (T Ψ) x = 0 := by
  obtain ⟨ε, hε, hcov⟩ := h₂ Ψ hΨl hΨc _ hρ hsupp (uniformizerUnit ℚ v) le_rfl (norm_varpi_le_one v)
  refine ⟨ε * ‖(uniformizerUnit ℚ v).val‖, mul_pos hε (norm_varpi_pos v), fun x hx => ?_⟩
  have h := hcov (x / (uniformizerUnit ℚ v).val) (norm_div_varpi_le v hx)
  rw [varpi_mul_div] at h
  rw [twistedDiff_apply, h, sub_self]

private theorem unitProj_twistedDiff_eq_zero_outer
    (hlc : IsTestLocallyConstant v T) (h₂ : HasOuterCovariance v φA T χA)
    (Ψ : (Fin 3 → v.adicCompletion ℚ) → ℂ) (hΨl : IsLocallyConstant Ψ) (hΨc : HasCompactSupport Ψ) {ρ : ℝ} (hρ : 0 < ρ)
    (hsupp : ∀ r, Ψ r ≠ 0 → ρ < ‖φA r‖) (χ : (v.adicCompletion ℚ)ˣ →* ℂˣ) (hχ : IsLocallyConstant χ)
    {α₂ : ℂ} (hα₂ : α₂ * (χ (uniformizerUnit ℚ v) : ℂ) = LaurentZetaSlot.slotScalar v (χA * χ)) :
    ∃ η : ℝ, 0 < η ∧ ∀ x : v.adicCompletion ℚ, ‖x‖ ≤ η → unitProj v χ (twistedDiff v α₂ (T Ψ)) x = 0 := by
  rcases slot_dichotomy v χ χA hα₂ with ⟨-, rfl⟩ | ⟨hram, rfl⟩
  · obtain ⟨η, hη, hz⟩ := twistedDiff_eq_zero_outer v h₂ Ψ hΨl hΨc hρ hsupp
    exact ⟨η, hη, fun x hx => unitProj_eq_zero_of_ball v χ hz x hx⟩
  · obtain ⟨u, hu, hne⟩ := exists_unit_of_not_hasConductorExponentAt v hram
    have hu1 : ‖u.val‖ ≤ 1 := le_of_eq (norm_eq_one_of_valued_eq_one v hu)
    have hϖu : ‖(uniformizerUnit ℚ v).val‖ ≤ ‖u.val‖ :=
      (norm_varpi_le_one v).trans_eq (norm_eq_one_of_valued_eq_one v hu).symm
    obtain ⟨ε, hε, hcov⟩ := h₂ Ψ hΨl hΨc _ hρ hsupp u hϖu hu1
    rw [twistedDiff_zero_fun]
    refine ⟨ε, hε, fun x hx => unitProj_eq_zero_of_covariant' v χ hχ (hlc Ψ hΨl hΨc) hu
      (mul_charExt_ne_one v hne) (η := ε) (fun t ht' => ?_) x hx⟩
    rw [mul_comm t u.val]
    exact hcov t ht'

private theorem twistedDiff₂_eq_zero_near (hadd : IsTestAdditive v T) (h₂ : HasOuterCovariance v φA T χA)
    (Ψ : (Fin 3 → v.adicCompletion ℚ) → ℂ) (hΨl : IsLocallyConstant Ψ) (hΨc : HasCompactSupport Ψ)
    (hB : ∀ s : (v.adicCompletion ℚ)ˣ, ‖(uniformizerUnit ℚ v).val‖ ≤ ‖s.val‖ → ‖s.val‖ ≤ 1 →
      ∃ Ψ₄ : (Fin 3 → v.adicCompletion ℚ) → ℂ, IsLocallyConstant Ψ₄ ∧ HasCompactSupport Ψ₄ ∧
      (∃ ρ : ℝ, 0 < ρ ∧ ∀ r, (Ψ₄ - Ψ) r ≠ 0 → ρ < ‖φA r‖) ∧
      ∃ ε : ℝ, 0 < ε ∧ ∀ t : v.adicCompletion ℚ, ‖t‖ ≤ ε → T Ψ (s.val * t) = (χB s : ℂ) * T Ψ₄ t) :
    ∃ η : ℝ, 0 < η ∧ ∀ x : v.adicCompletion ℚ, ‖x‖ ≤ η →
      twistedDiff v (χA (uniformizerUnit ℚ v) : ℂ) (twistedDiff v (χB (uniformizerUnit ℚ v) : ℂ) (T Ψ)) x = 0 := by
  obtain ⟨Ψ₄, h₄l, h₄c, ⟨ρ₄, hρ₄, h₄s⟩, ε, hε, hcov⟩ := hB (uniformizerUnit ℚ v) le_rfl (norm_varpi_le_one v)
  obtain ⟨η₄, hη₄, hz₄⟩ := twistedDiff_eq_zero_outer v h₂ _ (h₄l.sub hΨl) (h₄c.sub hΨc) hρ₄ h₄s
  have hstep : ∀ x, ‖x‖ ≤ ε * ‖(uniformizerUnit ℚ v).val‖ → twistedDiff v (χB (uniformizerUnit ℚ v) : ℂ) (T Ψ) x =
      (χB (uniformizerUnit ℚ v) : ℂ) * T (Ψ₄ - Ψ) (x / (uniformizerUnit ℚ v).val) := by
    intro x hx
    have h := hcov (x / (uniformizerUnit ℚ v).val) (norm_div_varpi_le v hx)
    rw [varpi_mul_div] at h
    rw [twistedDiff_apply, h, hadd.sub h₄l h₄c hΨl hΨc]
    ring
  refine ⟨min (ε * ‖(uniformizerUnit ℚ v).val‖ * ‖(uniformizerUnit ℚ v).val‖) (η₄ * ‖(uniformizerUnit ℚ v).val‖),
    lt_min (mul_pos (mul_pos hε (norm_varpi_pos v)) (norm_varpi_pos v)) (mul_pos hη₄ (norm_varpi_pos v)),
    fun x hx => ?_⟩
  rw [twistedDiff_eq_of_ball v (mul_pos hε (norm_varpi_pos v)) hstep _ x (hx.trans (min_le_left _ _)),
    hz₄ (x / (uniformizerUnit ℚ v).val) (norm_div_varpi_le v (hx.trans (min_le_right _ _))), mul_zero]

private theorem unitProj_twistedDiff₂_eq_zero_near (hadd : IsTestAdditive v T) (hlc : IsTestLocallyConstant v T)
    (h₂ : HasOuterCovariance v φA T χA) (Ψ : (Fin 3 → v.adicCompletion ℚ) → ℂ) (hΨl : IsLocallyConstant Ψ)
    (hΨc : HasCompactSupport Ψ)
    (hB : ∀ s : (v.adicCompletion ℚ)ˣ, ‖(uniformizerUnit ℚ v).val‖ ≤ ‖s.val‖ → ‖s.val‖ ≤ 1 →
      ∃ Ψ₄ : (Fin 3 → v.adicCompletion ℚ) → ℂ, IsLocallyConstant Ψ₄ ∧ HasCompactSupport Ψ₄ ∧
      (∃ ρ : ℝ, 0 < ρ ∧ ∀ r, (Ψ₄ - Ψ) r ≠ 0 → ρ < ‖φA r‖) ∧
      ∃ ε : ℝ, 0 < ε ∧ ∀ t : v.adicCompletion ℚ, ‖t‖ ≤ ε → T Ψ (s.val * t) = (χB s : ℂ) * T Ψ₄ t)
    (χ : (v.adicCompletion ℚ)ˣ →* ℂˣ) (hχ : IsLocallyConstant χ) {α₁ α₂ : ℂ}
    (hα₁ : α₁ * (χ (uniformizerUnit ℚ v) : ℂ) = LaurentZetaSlot.slotScalar v (χB * χ))
    (hα₂ : α₂ * (χ (uniformizerUnit ℚ v) : ℂ) = LaurentZetaSlot.slotScalar v (χA * χ)) :
    ∃ η : ℝ, 0 < η ∧
      ∀ x : v.adicCompletion ℚ, ‖x‖ ≤ η → unitProj v χ (twistedDiff v α₂ (twistedDiff v α₁ (T Ψ))) x = 0 := by
  rcases slot_dichotomy v χ χB hα₁ with ⟨-, rfl⟩ | ⟨hram, rfl⟩
  · obtain ⟨Ψ₄, h₄l, h₄c, ⟨ρ₄, hρ₄, h₄s⟩, ε, hε, hcov⟩ := hB (uniformizerUnit ℚ v) le_rfl (norm_varpi_le_one v)
    obtain ⟨η₄, hη₄, hz₄⟩ :=
      unitProj_twistedDiff_eq_zero_outer v hlc h₂ _ (h₄l.sub hΨl) (h₄c.sub hΨc) hρ₄ h₄s χ hχ hα₂
    have hstep : ∀ x, ‖x‖ ≤ ε * ‖(uniformizerUnit ℚ v).val‖ → twistedDiff v (χB (uniformizerUnit ℚ v) : ℂ) (T Ψ) x =
        (χB (uniformizerUnit ℚ v) : ℂ) * T (Ψ₄ - Ψ) (x / (uniformizerUnit ℚ v).val) := by
      intro x hx
      have h := hcov (x / (uniformizerUnit ℚ v).val) (norm_div_varpi_le v hx)
      rw [varpi_mul_div] at h
      rw [twistedDiff_apply, h, hadd.sub h₄l h₄c hΨl hΨc]
      ring
    have hstep₂ : ∀ x, ‖x‖ ≤ ε * ‖(uniformizerUnit ℚ v).val‖ * ‖(uniformizerUnit ℚ v).val‖ →
        twistedDiff v α₂ (twistedDiff v (χB (uniformizerUnit ℚ v) : ℂ) (T Ψ)) x =
          (χB (uniformizerUnit ℚ v) : ℂ) * twistedDiff v α₂ (T (Ψ₄ - Ψ)) (x / (uniformizerUnit ℚ v).val) :=
      fun x hx => twistedDiff_eq_of_ball v (mul_pos hε (norm_varpi_pos v)) hstep α₂ x hx
    refine ⟨min (ε * ‖(uniformizerUnit ℚ v).val‖ * ‖(uniformizerUnit ℚ v).val‖) (η₄ * ‖(uniformizerUnit ℚ v).val‖),
      lt_min (mul_pos (mul_pos hε (norm_varpi_pos v)) (norm_varpi_pos v)) (mul_pos hη₄ (norm_varpi_pos v)),
      fun x hx => ?_⟩
    rw [unitProj_eq_of_ball v χ hstep₂ x (hx.trans (min_le_left _ _)),
      hz₄ (x / (uniformizerUnit ℚ v).val) (norm_div_varpi_le v (hx.trans (min_le_right _ _))), mul_zero]
  · obtain ⟨u, hu, hne⟩ := exists_unit_of_not_hasConductorExponentAt v hram
    have hu1 : ‖u.val‖ ≤ 1 := le_of_eq (norm_eq_one_of_valued_eq_one v hu)
    have hϖu : ‖(uniformizerUnit ℚ v).val‖ ≤ ‖u.val‖ :=
      (norm_varpi_le_one v).trans_eq (norm_eq_one_of_valued_eq_one v hu).symm
    obtain ⟨Ψ₄, h₄l, h₄c, ⟨ρ₄, hρ₄, h₄s⟩, ε, hε, hcov⟩ := hB u hϖu hu1
    obtain ⟨η₄, hη₄, hz₄⟩ :=
      unitProj_twistedDiff_eq_zero_outer v hlc h₂ _ (h₄l.sub hΨl) (h₄c.sub hΨc) hρ₄ h₄s χ hχ hα₂
    rw [twistedDiff_zero_fun]
    have hcovu : ∀ x, ‖x‖ ≤ ε → T Ψ (x * u) = (χB u : ℂ) * (T Ψ x + T (Ψ₄ - Ψ) x) := fun x hx => by
      rw [mul_comm x u.val, hcov x hx, hadd.sub h₄l h₄c hΨl hΨc]
      ring
    have hcovT : ∀ x, ‖x‖ ≤ ε * ‖(uniformizerUnit ℚ v).val‖ →
        twistedDiff v α₂ (T Ψ) (x * u) = (χB u : ℂ) * (twistedDiff v α₂ (T Ψ) x + twistedDiff v α₂ (T (Ψ₄ - Ψ)) x) :=
      fun x hx => twistedDiff_mul_eq_of_ball v hε hcovu α₂ x hx
    refine ⟨min (ε * ‖(uniformizerUnit ℚ v).val‖) η₄, lt_min (mul_pos hε (norm_varpi_pos v)) hη₄, fun x hx => ?_⟩
    exact unitProj_eq_zero_of_covariant v χ hχ (LaurentZetaSlot.twistedDiff_eventually_eq v α₂ (hlc Ψ hΨl hΨc))
      (LaurentZetaSlot.twistedDiff_eventually_eq v α₂ (hlc _ (h₄l.sub hΨl) (h₄c.sub hΨc))) hu
      (mul_charExt_ne_one v hne) hcovT hz₄ x hx

private theorem twistedDiff₂_eq_zero_closed (hadd : IsTestAdditive v T) (h₁ : HasNearDecomposition v φA φB T χB)
    (h₂ : HasOuterCovariance v φA T χA) (Ψ : (Fin 3 → v.adicCompletion ℚ) → ℂ) (hΨl : IsLocallyConstant Ψ)
    (hΨc : HasCompactSupport Ψ) {δ : ℝ} (hδ : 0 < δ) (hvan : ∀ r, ‖φA r‖ ≤ δ → ‖φB r‖ ≤ δ → Ψ r = 0) :
    ∃ η : ℝ, 0 < η ∧ ∀ x : v.adicCompletion ℚ, ‖x‖ ≤ η →
      twistedDiff v (χA (uniformizerUnit ℚ v) : ℂ) (twistedDiff v (χB (uniformizerUnit ℚ v) : ℂ) (T Ψ)) x = 0 := by
  obtain ⟨Ψ₂, Ψ₃, h₂l, h₂c, h₃l, h₃c, hsplit, ⟨ρ₂, hρ₂, h₂s⟩, hB⟩ := h₁ Ψ hΨl hΨc δ hδ hvan
  have hsum : ∀ t : v.adicCompletion ℚ, T Ψ t = T Ψ₂ t + T Ψ₃ t := fun t => by
    rw [← hadd _ _ h₂l h₂c h₃l h₃c, ← hsplit]
  obtain ⟨η₂, hη₂, hz₂⟩ := twistedDiff_eq_zero_outer v h₂ _ h₂l h₂c hρ₂ h₂s
  obtain ⟨η₃, hη₃, hz₃⟩ := twistedDiff₂_eq_zero_near v hadd h₂ _ h₃l h₃c hB
  refine ⟨min (η₂ * ‖(uniformizerUnit ℚ v).val‖) η₃, lt_min (mul_pos hη₂ (norm_varpi_pos v)) hη₃, fun x hx => ?_⟩
  rw [twistedDiff_eq_add v (twistedDiff_eq_add v hsum _) _ x,
    LaurentZetaSlot.twistedDiff_comm v (χA (uniformizerUnit ℚ v) : ℂ) (χB (uniformizerUnit ℚ v) : ℂ) (T Ψ₂),
    twistedDiff_eq_zero_of_ball v hη₂ hz₂ _ x (hx.trans (min_le_left _ _)), hz₃ x (hx.trans (min_le_right _ _)),
    add_zero]

private theorem unitProj_twistedDiff₂_eq_zero_closed (hadd : IsTestAdditive v T) (hlc : IsTestLocallyConstant v T)
    (h₁ : HasNearDecomposition v φA φB T χB) (h₂ : HasOuterCovariance v φA T χA)
    (Ψ : (Fin 3 → v.adicCompletion ℚ) → ℂ) (hΨl : IsLocallyConstant Ψ) (hΨc : HasCompactSupport Ψ) {δ : ℝ} (hδ : 0 < δ)
    (hvan : ∀ r, ‖φA r‖ ≤ δ → ‖φB r‖ ≤ δ → Ψ r = 0) (χ : (v.adicCompletion ℚ)ˣ →* ℂˣ) (hχ : IsLocallyConstant χ)
    {α₁ α₂ : ℂ} (hα₁ : α₁ * (χ (uniformizerUnit ℚ v) : ℂ) = LaurentZetaSlot.slotScalar v (χB * χ))
    (hα₂ : α₂ * (χ (uniformizerUnit ℚ v) : ℂ) = LaurentZetaSlot.slotScalar v (χA * χ)) :
    ∃ η : ℝ, 0 < η ∧
      ∀ x : v.adicCompletion ℚ, ‖x‖ ≤ η → unitProj v χ (twistedDiff v α₂ (twistedDiff v α₁ (T Ψ))) x = 0 := by
  obtain ⟨Ψ₂, Ψ₃, h₂l, h₂c, h₃l, h₃c, hsplit, ⟨ρ₂, hρ₂, h₂s⟩, hB⟩ := h₁ Ψ hΨl hΨc δ hδ hvan
  have hsum : ∀ t : v.adicCompletion ℚ, T Ψ t = T Ψ₂ t + T Ψ₃ t := fun t => by
    rw [← hadd _ _ h₂l h₂c h₃l h₃c, ← hsplit]
  have h₂e : ∀ t : v.adicCompletion ℚ, t ≠ 0 → ∀ᶠ t' in nhds t, T Ψ₂ t' = T Ψ₂ t := hlc _ h₂l h₂c
  have h₃e : ∀ t : v.adicCompletion ℚ, t ≠ 0 → ∀ᶠ t' in nhds t, T Ψ₃ t' = T Ψ₃ t := hlc _ h₃l h₃c
  obtain ⟨η₂, hη₂, hz₂⟩ := unitProj_twistedDiff_eq_zero_outer v hlc h₂ _ h₂l h₂c hρ₂ h₂s χ hχ hα₂
  obtain ⟨η₃, hη₃, hz₃⟩ := unitProj_twistedDiff₂_eq_zero_near v hadd hlc h₂ _ h₃l h₃c hB χ hχ hα₁ hα₂
  refine ⟨min (η₂ * ‖(uniformizerUnit ℚ v).val‖) η₃, lt_min (mul_pos hη₂ (norm_varpi_pos v)) hη₃, fun x hx => ?_⟩
  rw [unitProj_eq_add v χ hχ
      (LaurentZetaSlot.twistedDiff_eventually_eq v α₂ (LaurentZetaSlot.twistedDiff_eventually_eq v α₁ h₂e))
      (LaurentZetaSlot.twistedDiff_eventually_eq v α₂ (LaurentZetaSlot.twistedDiff_eventually_eq v α₁ h₃e))
      (twistedDiff_eq_add v (twistedDiff_eq_add v hsum α₁) α₂) x,
    LaurentZetaSlot.twistedDiff_comm v α₂ α₁ (T Ψ₂),
    LaurentZetaSlot.unitProj_twistedDiff v χ hχ α₁ (LaurentZetaSlot.twistedDiff_eventually_eq v α₂ h₂e),
    twistedDiff_eq_zero_of_ball v hη₂ hz₂ α₁ x (hx.trans (min_le_left _ _)), hz₃ x (hx.trans (min_le_right _ _)),
    add_zero]

end Strata
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_eventually_threefold_twistedDifference_dualJacquetValueFn_eq_zero.LaurentZetaSlot"

section Covariant

variable {φA φB : (Fin 3 → v.adicCompletion ℚ) → v.adicCompletion ℚ}
variable {T : ((Fin 3 → v.adicCompletion ℚ) → ℂ) → v.adicCompletion ℚ → ℂ}
variable {σL : (v.adicCompletion ℚ)ˣ → (Fin 3 → v.adicCompletion ℚ) → (Fin 3 → v.adicCompletion ℚ)}
variable {χL χA χB : (v.adicCompletion ℚ)ˣ →* ℂˣ}

private theorem eventually_twistedDiff₃_eq_zero_of_covariance (hadd : IsTestAdditive v T) (hσL : IsTestTransport v σL)
    (hvL : PullbackSubVanishesNear v φA φB σL) (h₀ : HasPullbackCovariance v T σL χL)
    (h₁ : HasNearDecomposition v φA φB T χB) (h₂ : HasOuterCovariance v φA T χA)
    (Φ : (Fin 3 → v.adicCompletion ℚ) → ℂ) (hΦl : IsLocallyConstant Φ) (hΦc : HasCompactSupport Φ) :
    ∀ᶠ x in nhds (0 : v.adicCompletion ℚ),
      twistedDiff v (χA (uniformizerUnit ℚ v) : ℂ) (twistedDiff v (χB (uniformizerUnit ℚ v) : ℂ)
        (twistedDiff v (χL (uniformizerUnit ℚ v) : ℂ) (T Φ))) x = 0 := by
  obtain ⟨ε, hε, hcov⟩ := h₀ Φ hΦl hΦc (uniformizerUnit ℚ v) le_rfl (norm_varpi_le_one v)
  obtain ⟨δ, hδ, hvan⟩ := hvL Φ hΦl hΦc
  obtain ⟨h₁l, h₁c⟩ := hσL Φ hΦl hΦc (uniformizerUnit ℚ v) le_rfl (norm_varpi_le_one v)
  have h₁v : ∀ r, ‖φA r‖ ≤ δ → ‖φB r‖ ≤ δ → (Φ ∘ σL (uniformizerUnit ℚ v) - Φ) r = 0 :=
    hvan (uniformizerUnit ℚ v) le_rfl (norm_varpi_le_one v)
  have hstep : ∀ x, ‖x‖ ≤ ε * ‖(uniformizerUnit ℚ v).val‖ → twistedDiff v (χL (uniformizerUnit ℚ v) : ℂ) (T Φ) x =
      (χL (uniformizerUnit ℚ v) : ℂ) * T (Φ ∘ σL (uniformizerUnit ℚ v) - Φ) (x / (uniformizerUnit ℚ v).val) := by
    intro x hx
    have h := hcov (x / (uniformizerUnit ℚ v).val) (norm_div_varpi_le v hx)
    rw [varpi_mul_div] at h
    rw [twistedDiff_apply, h, hadd.sub h₁l h₁c hΦl hΦc]
    ring
  have hstep₁ : ∀ x, ‖x‖ ≤ ε * ‖(uniformizerUnit ℚ v).val‖ * ‖(uniformizerUnit ℚ v).val‖ →
      twistedDiff v (χB (uniformizerUnit ℚ v) : ℂ) (twistedDiff v (χL (uniformizerUnit ℚ v) : ℂ) (T Φ)) x =
        (χL (uniformizerUnit ℚ v) : ℂ) *
          twistedDiff v (χB (uniformizerUnit ℚ v) : ℂ) (T (Φ ∘ σL (uniformizerUnit ℚ v) - Φ))
            (x / (uniformizerUnit ℚ v).val) :=
    fun x hx => twistedDiff_eq_of_ball v (mul_pos hε (norm_varpi_pos v)) hstep _ x hx
  obtain ⟨η, hη, hz⟩ := twistedDiff₂_eq_zero_closed v hadd h₁ h₂ _ (h₁l.sub hΦl) (h₁c.sub hΦc) hδ h₁v
  refine eventually_eq_zero_of_ball v (lt_min (mul_pos (mul_pos (mul_pos hε (norm_varpi_pos v))
    (norm_varpi_pos v)) (norm_varpi_pos v)) (mul_pos hη (norm_varpi_pos v))) fun x hx => ?_
  rw [twistedDiff_eq_of_ball v (mul_pos (mul_pos hε (norm_varpi_pos v)) (norm_varpi_pos v)) hstep₁ _ x
      (hx.trans (min_le_left _ _)),
    hz (x / (uniformizerUnit ℚ v).val) (norm_div_varpi_le v (hx.trans (min_le_right _ _))), mul_zero]

private theorem eventually_unitProj_twistedDiff₃_eq_zero_of_covariance (hadd : IsTestAdditive v T)
    (hlc : IsTestLocallyConstant v T) (hσL : IsTestTransport v σL) (hvL : PullbackSubVanishesNear v φA φB σL)
    (h₀ : HasPullbackCovariance v T σL χL) (h₁ : HasNearDecomposition v φA φB T χB)
    (h₂ : HasOuterCovariance v φA T χA) (Φ : (Fin 3 → v.adicCompletion ℚ) → ℂ) (hΦl : IsLocallyConstant Φ)
    (hΦc : HasCompactSupport Φ) (χ : (v.adicCompletion ℚ)ˣ →* ℂˣ) (hχ : IsLocallyConstant χ) {αL αB αA : ℂ}
    (hαL : αL * (χ (uniformizerUnit ℚ v) : ℂ) = LaurentZetaSlot.slotScalar v (χL * χ))
    (hαB : αB * (χ (uniformizerUnit ℚ v) : ℂ) = LaurentZetaSlot.slotScalar v (χB * χ))
    (hαA : αA * (χ (uniformizerUnit ℚ v) : ℂ) = LaurentZetaSlot.slotScalar v (χA * χ)) :
    ∀ᶠ x in nhds (0 : v.adicCompletion ℚ),
      unitProj v χ (twistedDiff v αA (twistedDiff v αB (twistedDiff v αL (T Φ)))) x = 0 := by
  obtain ⟨δ, hδ, hvan⟩ := hvL Φ hΦl hΦc
  have hone : ∀ s : (v.adicCompletion ℚ)ˣ, ‖(uniformizerUnit ℚ v).val‖ ≤ ‖s.val‖ → ‖s.val‖ ≤ 1 →
      IsLocallyConstant (Φ ∘ σL s - Φ) ∧ HasCompactSupport (Φ ∘ σL s - Φ) ∧
        (∀ r, ‖φA r‖ ≤ δ → ‖φB r‖ ≤ δ → (Φ ∘ σL s - Φ) r = 0) ∧
        ∃ ε : ℝ, 0 < ε ∧ ∀ t : v.adicCompletion ℚ, ‖t‖ ≤ ε →
          T Φ (s.val * t) = (χL s : ℂ) * (T Φ t + T (Φ ∘ σL s - Φ) t) := fun s hs0 hs1 => by
    obtain ⟨hl, hc⟩ := hσL Φ hΦl hΦc s hs0 hs1
    obtain ⟨ε, hε, hcov⟩ := h₀ Φ hΦl hΦc s hs0 hs1
    refine ⟨hl.sub hΦl, hc.sub hΦc, hvan s hs0 hs1, ε, hε, fun t ht => ?_⟩
    rw [hcov t ht, hadd.sub hl hc hΦl hΦc]
    ring
  rcases slot_dichotomy v χ χL hαL with ⟨-, h0⟩ | ⟨hram, h0⟩
  · obtain ⟨hl, hc, hv, ε, hε, hcov⟩ := hone (uniformizerUnit ℚ v) le_rfl (norm_varpi_le_one v)
    obtain ⟨η, hη, hz⟩ := unitProj_twistedDiff₂_eq_zero_closed v hadd hlc h₁ h₂ _ hl hc hδ hv χ hχ hαB hαA
    have hstep : ∀ x, ‖x‖ ≤ ε * ‖(uniformizerUnit ℚ v).val‖ → twistedDiff v αL (T Φ) x =
        (χL (uniformizerUnit ℚ v) : ℂ) * T (Φ ∘ σL (uniformizerUnit ℚ v) - Φ) (x / (uniformizerUnit ℚ v).val) := by
      intro x hx
      have h := hcov (x / (uniformizerUnit ℚ v).val) (norm_div_varpi_le v hx)
      rw [varpi_mul_div] at h
      rw [twistedDiff_apply, h0, h]
      ring
    have hstep₁ : ∀ x, ‖x‖ ≤ ε * ‖(uniformizerUnit ℚ v).val‖ * ‖(uniformizerUnit ℚ v).val‖ →
        twistedDiff v αB (twistedDiff v αL (T Φ)) x = (χL (uniformizerUnit ℚ v) : ℂ) *
          twistedDiff v αB (T (Φ ∘ σL (uniformizerUnit ℚ v) - Φ)) (x / (uniformizerUnit ℚ v).val) :=
      fun x hx => twistedDiff_eq_of_ball v (mul_pos hε (norm_varpi_pos v)) hstep _ x hx
    have hstep₂ :
        ∀ x, ‖x‖ ≤ ε * ‖(uniformizerUnit ℚ v).val‖ * ‖(uniformizerUnit ℚ v).val‖ * ‖(uniformizerUnit ℚ v).val‖ →
          twistedDiff v αA (twistedDiff v αB (twistedDiff v αL (T Φ))) x = (χL (uniformizerUnit ℚ v) : ℂ) *
            twistedDiff v αA (twistedDiff v αB (T (Φ ∘ σL (uniformizerUnit ℚ v) - Φ)))
              (x / (uniformizerUnit ℚ v).val) :=
      fun x hx => twistedDiff_eq_of_ball v (mul_pos (mul_pos hε (norm_varpi_pos v)) (norm_varpi_pos v)) hstep₁ _
        x hx
    refine eventually_eq_zero_of_ball v (lt_min (mul_pos (mul_pos (mul_pos hε (norm_varpi_pos v))
      (norm_varpi_pos v)) (norm_varpi_pos v)) (mul_pos hη (norm_varpi_pos v))) fun x hx => ?_
    rw [unitProj_eq_of_ball v χ hstep₂ x (hx.trans (min_le_left _ _)),
      hz (x / (uniformizerUnit ℚ v).val) (norm_div_varpi_le v (hx.trans (min_le_right _ _))), mul_zero]
  · obtain ⟨u, hu, hne⟩ := exists_unit_of_not_hasConductorExponentAt v hram
    have hu1 : ‖u.val‖ ≤ 1 := le_of_eq (norm_eq_one_of_valued_eq_one v hu)
    have hϖu : ‖(uniformizerUnit ℚ v).val‖ ≤ ‖u.val‖ :=
      (norm_varpi_le_one v).trans_eq (norm_eq_one_of_valued_eq_one v hu).symm
    obtain ⟨hl, hc, hv, ε, hε, hcov⟩ := hone u hϖu hu1
    obtain ⟨η, hη, hz⟩ := unitProj_twistedDiff₂_eq_zero_closed v hadd hlc h₁ h₂ _ hl hc hδ hv χ hχ hαB hαA
    rw [h0, twistedDiff_zero_fun]
    have hcov₁ : ∀ x : v.adicCompletion ℚ, ‖x‖ ≤ ε → T Φ (x * u) = (χL u : ℂ) * (T Φ x + T (Φ ∘ σL u - Φ) x) :=
      fun x hx => by
        rw [mul_comm x u.val]
        exact hcov x hx
    have hcov₂ : ∀ x, ‖x‖ ≤ ε * ‖(uniformizerUnit ℚ v).val‖ →
        twistedDiff v αB (T Φ) (x * u) =
          (χL u : ℂ) * (twistedDiff v αB (T Φ) x + twistedDiff v αB (T (Φ ∘ σL u - Φ)) x) :=
      fun x hx => twistedDiff_mul_eq_of_ball v hε hcov₁ _ x hx
    have hcov₃ : ∀ x, ‖x‖ ≤ ε * ‖(uniformizerUnit ℚ v).val‖ * ‖(uniformizerUnit ℚ v).val‖ →
        twistedDiff v αA (twistedDiff v αB (T Φ)) (x * u) =
          (χL u : ℂ) *
            (twistedDiff v αA (twistedDiff v αB (T Φ)) x + twistedDiff v αA (twistedDiff v αB (T (Φ ∘ σL u - Φ))) x) :=
      fun x hx => twistedDiff_mul_eq_of_ball v (mul_pos hε (norm_varpi_pos v)) hcov₂ _ x hx
    have hl₁ : ∀ t : v.adicCompletion ℚ, t ≠ 0 → ∀ᶠ t' in nhds t, T (Φ ∘ σL u - Φ) t' = T (Φ ∘ σL u - Φ) t :=
      hlc _ hl hc
    refine eventually_eq_zero_of_ball v (lt_min (mul_pos (mul_pos hε (norm_varpi_pos v)) (norm_varpi_pos v)) hη)
      fun x hx => ?_
    exact unitProj_eq_zero_of_covariant v χ hχ
      (LaurentZetaSlot.twistedDiff_eventually_eq v αA (LaurentZetaSlot.twistedDiff_eventually_eq v αB
        (hlc Φ hΦl hΦc)))
      (LaurentZetaSlot.twistedDiff_eventually_eq v αA (LaurentZetaSlot.twistedDiff_eventually_eq v αB hl₁))
      hu (mul_charExt_ne_one v hne) hcov₃ hz x hx

end Covariant
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_eventually_threefold_twistedDifference_dualJacquetValueFn_eq_zero.LaurentZetaSlot"

section Torus

variable (ν : Fin 3 → ((v.adicCompletion ℚ)ˣ →* ℂˣ))

variable (Φ : (Fin 3 → v.adicCompletion ℚ) → ℂ)

end Torus
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_eventually_threefold_twistedDifference_dualJacquetValueFn_eq_zero.LaurentZetaSlot"

end TorusCollapse
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_eventually_threefold_twistedDifference_dualJacquetValueFn_eq_zero.LaurentZetaSlot"

end WeylTranslateZeta
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_eventually_threefold_twistedDifference_dualJacquetValueFn_eq_zero.LaurentZetaSlot"
end
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_eventually_threefold_twistedDifference_dualJacquetValueFn_eq_zero.LaurentZetaSlot"

section

open IsDedekindDomain
open NumberField

namespace WeylTranslateZeta
open LanglandsTunnell.TateLocal

section ConductorWitness

variable (K : Type) [Field K] [NumberField K] (w : HeightOneSpectrum (𝓞 K))

private theorem exists_hasConductorExponentAt_of_isLocallyConstant (η : (w.adicCompletion K)ˣ →* ℂˣ)
    (hη : IsLocallyConstant η) : ∃ c : ℕ, HasConductorExponentAt K w η c :=
  exists_hasConductorExponentAt_of_continuous K w η hη.continuous

end ConductorWitness
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_eventually_threefold_twistedDifference_dualJacquetValueFn_eq_zero.LaurentZetaSlot"

section NormPowerOfConductorSum

end NormPowerOfConductorSum
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_eventually_threefold_twistedDifference_dualJacquetValueFn_eq_zero.LaurentZetaSlot"

end WeylTranslateZeta
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_eventually_threefold_twistedDifference_dualJacquetValueFn_eq_zero.LaurentZetaSlot"
end
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_eventually_threefold_twistedDifference_dualJacquetValueFn_eq_zero.LaurentZetaSlot"

section

open MeasureTheory
open IsDedekindDomain
open NumberField
open LanglandsTunnell.TateLocal
open NumberField.StandardAddChar
open scoped Topology

namespace WeylTranslateZeta
open LanglandsTunnell.CubicInduction

section DualTorusValues

variable (v : HeightOneSpectrum (𝓞 ℚ))
variable (ν : Fin 3 → ((v.adicCompletion ℚ)ˣ →* ℂˣ)) (Φ : (Fin 3 → v.adicCompletion ℚ) → ℂ)

private noncomputable def dualPoint (a : (v.adicCompletion ℚ)ˣ) (x : v.adicCompletion ℚ) : LocalGL3 v :=
  longWeyl3 * transposeInv3 (iotaGL (diagUnitGL2 a) * lowerUnipotent21 x * (weylPrime3 * transposeInv3 1)) *
    antidiagonal3 v

private noncomputable def dualTranslate (a : (v.adicCompletion ℚ)ˣ) (x : v.adicCompletion ℚ) : LocalGL3 v → ℂ :=
  gl3AmbientRightTranslate (R := ℂ) (dualPoint v a x) (cellSectionOf v ν Φ)

private theorem jacquetTruncated3_dualTranslate (c : ℤ) (a : (v.adicCompletion ℚ)ˣ) (x : v.adicCompletion ℚ) :
    letI := localBorel ℚ v
    jacquetTruncated3 v c (dualTranslate v ν Φ a x) =
      ∫ p in unipotentBall3 v c,
        psiLocal ℚ v (-(p.1 + p.2.1)) * cellSectionOf v ν Φ (dualCellPoint v p.1 p.2.1 p.2.2 a x)
          ∂(jacquetHaar3 v) := by
  letI := localBorel ℚ v
  unfold jacquetTruncated3
  congr 1

private theorem exists_level_dualTranslate (hν : ∀ i, IsLocallyConstant (ν i)) (hΦl : IsLocallyConstant Φ)
    (hΦc : HasCompactSupport Φ) (a : (v.adicCompletion ℚ)ˣ) (x : v.adicCompletion ℚ) :
    ∃ c₀ : ℕ, ∀ c : ℤ, (c₀ : ℤ) ≤ c →
      jacquetTruncated3 v c (dualTranslate v ν Φ a x) = jacquetTruncated3 v c₀ (dualTranslate v ν Φ a x) := by
  obtain ⟨c₀, h⟩ := exists_forall_le_integrableOn_and_jacquetTruncated3_eq_of_cellSectionOf v ν hν Φ ⟨hΦl, hΦc⟩
    (dualPoint v a x)
  exact ⟨c₀, fun c hc => (h c hc).2⟩

open Classical in

private noncomputable def dualFn : v.adicCompletion ℚ → ℂ := fun t =>
  letI := localBorel ℚ v
  if h : t = 0 then 0 else
    (∫ x : v.adicCompletion ℚ, jacquetValue v (dualTranslate v ν Φ (Units.mk0 t h) x) ∂(selfDualHaarAt ℚ v)) *
      ((modulus t : ℝ) : ℂ)⁻¹

private theorem dualFn_zero : dualFn v ν Φ 0 = 0 := by
  simp [dualFn]

private theorem dualFn_coe_units (a : (v.adicCompletion ℚ)ˣ) :
    letI := localBorel ℚ v
    dualFn v ν Φ a =
      (∫ x : v.adicCompletion ℚ, jacquetValue v (dualTranslate v ν Φ a x) ∂(selfDualHaarAt ℚ v)) *
        ((modulus (a : v.adicCompletion ℚ) : ℝ) : ℂ)⁻¹ := by
  simp [dualFn, a.ne_zero]

end DualTorusValues
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_eventually_threefold_twistedDifference_dualJacquetValueFn_eq_zero.LaurentZetaSlot"

end WeylTranslateZeta
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_eventually_threefold_twistedDifference_dualJacquetValueFn_eq_zero.LaurentZetaSlot"
end
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_eventually_threefold_twistedDifference_dualJacquetValueFn_eq_zero.LaurentZetaSlot"

section

open MeasureTheory
open IsDedekindDomain
open NumberField
open LanglandsTunnell.TateLocal
open NumberField.StandardAddChar

namespace WeylTranslateZeta
open LanglandsTunnell.CubicInduction

private def lowerUnipotent3 {A : Type*} [CommRing A] (x y z : A) : GL (Fin 3) A where
  val := !![1, 0, 0; x, 1, 0; z, y, 1]
  inv := !![1, 0, 0; -x, 1, 0; x * y - z, -y, 1]
  val_inv := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three]
    ring
  inv_val := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three]
    ring

@[scoped simp] private theorem lowerUnipotent3_coe {A : Type*} [CommRing A] (x y z : A) :
    ((lowerUnipotent3 x y z : GL (Fin 3) A) : Matrix (Fin 3) (Fin 3) A) = !![1, 0, 0; x, 1, 0; z, y, 1] :=
  rfl

section RightLower

variable (v : HeightOneSpectrum (𝓞 ℚ))
variable (ν : Fin 3 → ((v.adicCompletion ℚ)ˣ →* ℂˣ)) (Φ : (Fin 3 → v.adicCompletion ℚ) → ℂ)

end RightLower
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_eventually_threefold_twistedDifference_dualJacquetValueFn_eq_zero.LaurentZetaSlot"

section DualValueLocallyConstant

variable (v : HeightOneSpectrum (𝓞 ℚ))
variable (ν : Fin 3 → ((v.adicCompletion ℚ)ˣ →* ℂˣ)) (Φ : (Fin 3 → v.adicCompletion ℚ) → ℂ)

end DualValueLocallyConstant
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_eventually_threefold_twistedDifference_dualJacquetValueFn_eq_zero.LaurentZetaSlot"

end WeylTranslateZeta
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_eventually_threefold_twistedDifference_dualJacquetValueFn_eq_zero.LaurentZetaSlot P2MW.S_LanglandsTunnell_CubicInduction_eventually_threefold_twistedDifference_dualJacquetValueFn_eq_zero.WeylTranslateZeta"
end
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_eventually_threefold_twistedDifference_dualJacquetValueFn_eq_zero.LaurentZetaSlot P2MW.S_LanglandsTunnell_CubicInduction_eventually_threefold_twistedDifference_dualJacquetValueFn_eq_zero.WeylTranslateZeta"

section

open MeasureTheory
open IsDedekindDomain
open NumberField
open LanglandsTunnell.TateLocal
open NumberField.StandardAddChar

namespace WeylTranslateZeta
open LanglandsTunnell.CubicInduction

private def dualConj3 {A : Type*} [CommRing A] (u x : A) : GL (Fin 3) A where
  val := !![1 - u * x, 0, u; 0, 1, 0; -(x ^ 2 * u), 0, 1 + x * u]
  inv := !![1 + u * x, 0, -u; 0, 1, 0; x ^ 2 * u, 0, 1 - x * u]
  val_inv := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three] <;> ring
  inv_val := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three] <;> ring

@[scoped simp] private theorem dualConj3_coe {A : Type*} [CommRing A] (u x : A) :
    ((dualConj3 u x : GL (Fin 3) A) : Matrix (Fin 3) (Fin 3) A) =
      !![1 - u * x, 0, u; 0, 1, 0; -(x ^ 2 * u), 0, 1 + x * u] :=
  rfl

section RightDiagonal

variable (v : HeightOneSpectrum (𝓞 ℚ))
variable (ν : Fin 3 → ((v.adicCompletion ℚ)ˣ →* ℂˣ)) (Φ : (Fin 3 → v.adicCompletion ℚ) → ℂ)

end RightDiagonal
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_eventually_threefold_twistedDifference_dualJacquetValueFn_eq_zero.LaurentZetaSlot P2MW.S_LanglandsTunnell_CubicInduction_eventually_threefold_twistedDifference_dualJacquetValueFn_eq_zero.WeylTranslateZeta"

section Shear

variable (v : HeightOneSpectrum (𝓞 ℚ))
variable (ν : Fin 3 → ((v.adicCompletion ℚ)ˣ →* ℂˣ)) (Φ : (Fin 3 → v.adicCompletion ℚ) → ℂ)

end Shear
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_eventually_threefold_twistedDifference_dualJacquetValueFn_eq_zero.LaurentZetaSlot P2MW.S_LanglandsTunnell_CubicInduction_eventually_threefold_twistedDifference_dualJacquetValueFn_eq_zero.WeylTranslateZeta"

section DualValueLargeModule

variable (v : HeightOneSpectrum (𝓞 ℚ))
variable (ν : Fin 3 → ((v.adicCompletion ℚ)ˣ →* ℂˣ)) (Φ : (Fin 3 → v.adicCompletion ℚ) → ℂ)

end DualValueLargeModule
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_eventually_threefold_twistedDifference_dualJacquetValueFn_eq_zero.LaurentZetaSlot P2MW.S_LanglandsTunnell_CubicInduction_eventually_threefold_twistedDifference_dualJacquetValueFn_eq_zero.WeylTranslateZeta"

end WeylTranslateZeta
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_eventually_threefold_twistedDifference_dualJacquetValueFn_eq_zero.LaurentZetaSlot P2MW.S_LanglandsTunnell_CubicInduction_eventually_threefold_twistedDifference_dualJacquetValueFn_eq_zero.WeylTranslateZeta"
end
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_eventually_threefold_twistedDifference_dualJacquetValueFn_eq_zero.LaurentZetaSlot P2MW.S_LanglandsTunnell_CubicInduction_eventually_threefold_twistedDifference_dualJacquetValueFn_eq_zero.WeylTranslateZeta"

section

open MeasureTheory
open IsDedekindDomain
open NumberField
open LanglandsTunnell.TateLocal
open NumberField.StandardAddChar

attribute [local instance] LanglandsTunnell.TateLocal.localBorel

namespace WeylTranslateZeta
open LanglandsTunnell.CubicInduction

variable (v : HeightOneSpectrum (𝓞 ℚ))
variable (ν : Fin 3 → ((v.adicCompletion ℚ)ˣ →* ℂˣ)) (Φ : (Fin 3 → v.adicCompletion ℚ) → ℂ)

open Classical in

private noncomputable def dualSlice (x t : v.adicCompletion ℚ) : ℂ :=
  if h : t = 0 then 0 else
    jacquetValue v (dualTranslate v ν Φ (Units.mk0 t h) x) * ((modulus t : ℝ) : ℂ)⁻¹

private theorem dualSlice_zero (x : v.adicCompletion ℚ) : dualSlice v ν Φ x 0 = 0 := by
  simp [dualSlice]
end WeylTranslateZeta
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_eventually_threefold_twistedDifference_dualJacquetValueFn_eq_zero.LaurentZetaSlot P2MW.S_LanglandsTunnell_CubicInduction_eventually_threefold_twistedDifference_dualJacquetValueFn_eq_zero.WeylTranslateZeta"
end
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_eventually_threefold_twistedDifference_dualJacquetValueFn_eq_zero.LaurentZetaSlot P2MW.S_LanglandsTunnell_CubicInduction_eventually_threefold_twistedDifference_dualJacquetValueFn_eq_zero.WeylTranslateZeta"

section

open IsDedekindDomain NumberField

namespace WeylTranslateZeta
open LanglandsTunnell.CubicInduction

section CellCoordinateTestFunctions

variable (v : HeightOneSpectrum (𝓞 ℚ))

private noncomputable def dualTailMap (x s : v.adicCompletion ℚ) (r : Fin 3 → v.adicCompletion ℚ) :
    Fin 3 → v.adicCompletion ℚ :=
  ![s * r 0, s * r 1 + (s - 1) / x, r 2]

private theorem dualTailMap_apply_zero (x s : v.adicCompletion ℚ) (r : Fin 3 → v.adicCompletion ℚ) :
    dualTailMap v x s r 0 = s * r 0 :=
  rfl

private theorem dualTailMap_apply_one (x s : v.adicCompletion ℚ) (r : Fin 3 → v.adicCompletion ℚ) :
    dualTailMap v x s r 1 = s * r 1 + (s - 1) / x :=
  rfl

private theorem dualTailMap_apply_two (x s : v.adicCompletion ℚ) (r : Fin 3 → v.adicCompletion ℚ) :
    dualTailMap v x s r 2 = r 2 :=
  rfl

private noncomputable def bulkGauge (x : v.adicCompletion ℚ) (r : Fin 3 → v.adicCompletion ℚ) : v.adicCompletion ℚ :=
  1 + x * (r 1 - r 2 * r 0)

private theorem bulkGauge_def (x : v.adicCompletion ℚ) (r : Fin 3 → v.adicCompletion ℚ) :
    bulkGauge v x r = 1 + x * (r 1 - r 2 * r 0) :=
  rfl

private theorem continuous_dualTailMap (x s : v.adicCompletion ℚ) : Continuous (dualTailMap v x s) := by
  refine continuous_pi fun i => ?_
  match i with
  | 0 =>
    show Continuous fun r : Fin 3 → v.adicCompletion ℚ => s * r 0
    exact continuous_const.mul (continuous_apply 0)
  | 1 =>
    show Continuous fun r : Fin 3 → v.adicCompletion ℚ => s * r 1 + (s - 1) / x
    exact (continuous_const.mul (continuous_apply 1)).add continuous_const
  | 2 =>
    show Continuous fun r : Fin 3 → v.adicCompletion ℚ => r 2
    exact continuous_apply 2

private theorem continuous_bulkGauge (x : v.adicCompletion ℚ) : Continuous (bulkGauge v x) := by
  show Continuous fun r : Fin 3 → v.adicCompletion ℚ => 1 + x * (r 1 - r 2 * r 0)
  exact continuous_const.add (continuous_const.mul ((continuous_apply 1).sub ((continuous_apply 2).mul
    (continuous_apply 0))))

private theorem isLocallyConstant_comp_dualTailMap {Φ : (Fin 3 → v.adicCompletion ℚ) → ℂ} (hΦ : IsLocallyConstant Φ)
    (x s : v.adicCompletion ℚ) : IsLocallyConstant fun r => Φ (dualTailMap v x s r) :=
  hΦ.comp_continuous (continuous_dualTailMap v x s)

private noncomputable def dualTailMapInv (x s : v.adicCompletion ℚ) (r : Fin 3 → v.adicCompletion ℚ) :
    Fin 3 → v.adicCompletion ℚ :=
  ![r 0 / s, (r 1 - (s - 1) / x) / s, r 2]

private theorem continuous_dualTailMapInv (x s : v.adicCompletion ℚ) : Continuous (dualTailMapInv v x s) := by
  refine continuous_pi fun i => ?_
  match i with
  | 0 =>
    show Continuous fun r : Fin 3 → v.adicCompletion ℚ => r 0 / s
    fun_prop
  | 1 =>
    show Continuous fun r : Fin 3 → v.adicCompletion ℚ => (r 1 - (s - 1) / x) / s
    fun_prop
  | 2 =>
    show Continuous fun r : Fin 3 → v.adicCompletion ℚ => r 2
    exact continuous_apply 2

private theorem dualTailMapInv_dualTailMap (x : v.adicCompletion ℚ) {s : v.adicCompletion ℚ} (hs : s ≠ 0)
    (r : Fin 3 → v.adicCompletion ℚ) :
    dualTailMapInv v x s (dualTailMap v x s r) = r := by
  funext i
  match i with
  | 0 =>
    show s * r 0 / s = r 0
    field_simp
  | 1 =>
    show (s * r 1 + (s - 1) / x - (s - 1) / x) / s = r 1
    rw [show s * r 1 + (s - 1) / x - (s - 1) / x = s * r 1 by ring]
    field_simp
  | 2 =>
    rfl

private theorem hasCompactSupport_comp_dualTailMap {Φ : (Fin 3 → v.adicCompletion ℚ) → ℂ} (hΦ : HasCompactSupport Φ)
    (x : v.adicCompletion ℚ) {s : v.adicCompletion ℚ} (hs : s ≠ 0) :
    HasCompactSupport fun r => Φ (dualTailMap v x s r) := by
  refine HasCompactSupport.intro (IsCompact.image hΦ (continuous_dualTailMapInv v x s)) fun r hr => ?_
  by_contra h
  exact hr ⟨dualTailMap v x s r, subset_tsupport Φ (Function.mem_support.2 h), dualTailMapInv_dualTailMap v x hs r⟩

private theorem exists_forall_dualTailMap_eq {Φ : (Fin 3 → v.adicCompletion ℚ) → ℂ} (hΦl : IsLocallyConstant Φ)
    (hΦc : HasCompactSupport Φ) (x : v.adicCompletion ℚ) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ s : v.adicCompletion ℚ, ‖s‖ ≤ 1 →
      ∀ r : Fin 3 → v.adicCompletion ℚ, ‖r 0‖ ≤ δ → ‖r 1 + 1 / x‖ ≤ δ → Φ (dualTailMap v x s r) = Φ r := by
  obtain ⟨δ, hδ, hΦδ⟩ := exists_invariance_radius v Φ hΦl hΦc
  refine ⟨δ, hδ, fun s hs r h0 h1 => hΦδ r _ fun i => ?_⟩
  have hs1 : ‖s - 1‖ ≤ 1 := by
    calc ‖s - 1‖ = ‖s + (-1 : v.adicCompletion ℚ)‖ := by rw [sub_eq_add_neg]
      _ ≤ max ‖s‖ ‖(-1 : v.adicCompletion ℚ)‖ := IsUltrametricDist.norm_add_le_max _ _
      _ ≤ 1 := by rw [norm_neg, norm_one]; exact max_le hs le_rfl
  match i with
  | 0 =>
    rw [dualTailMap_apply_zero, ← sub_one_mul, norm_mul]
    exact (mul_le_mul hs1 h0 (norm_nonneg _) zero_le_one).trans_eq (one_mul δ)
  | 1 =>
    rw [dualTailMap_apply_one, show s * r 1 + (s - 1) / x - r 1 = (s - 1) * (r 1 + 1 / x) by ring, norm_mul]
    exact (mul_le_mul hs1 h1 (norm_nonneg _) zero_le_one).trans_eq (one_mul δ)
  | 2 =>
    rw [dualTailMap_apply_two, sub_self, norm_zero]
    exact hδ.le

private theorem isClopen_setOf_lt_norm_bulkGauge (x : v.adicCompletion ℚ) {δ : ℝ} (hδ : 0 < δ) :
    IsClopen {r : Fin 3 → v.adicCompletion ℚ | δ < ‖bulkGauge v x r‖} := by
  have h : {r : Fin 3 → v.adicCompletion ℚ | δ < ‖bulkGauge v x r‖} =
      bulkGauge v x ⁻¹' (Metric.closedBall (0 : v.adicCompletion ℚ) δ)ᶜ := by
    ext r
    simp [not_le]
  rw [h]
  exact (IsUltrametricDist.isClopen_closedBall (0 : v.adicCompletion ℚ) hδ.ne').compl.preimage
    (continuous_bulkGauge v x)

private theorem isLocallyConstant_indicator_of_isClopen_T {S : Set (Fin 3 → v.adicCompletion ℚ)} (hS : IsClopen S)
    {Φ : (Fin 3 → v.adicCompletion ℚ) → ℂ} (hΦ : IsLocallyConstant Φ) : IsLocallyConstant (S.indicator Φ) := by
  refine (IsLocallyConstant.iff_exists_open _).2 fun r => ?_
  obtain ⟨U, hU, hrU, hUΦ⟩ := hΦ.exists_open r
  by_cases hr : r ∈ S
  · refine ⟨U ∩ S, hU.inter hS.isOpen, ⟨hrU, hr⟩, fun r' hr' => ?_⟩
    rw [Set.indicator_of_mem hr'.2, Set.indicator_of_mem hr, hUΦ r' hr'.1]
  · refine ⟨U ∩ Sᶜ, hU.inter hS.isClosed.isOpen_compl, ⟨hrU, hr⟩, fun r' hr' => ?_⟩
    have hr'S : r' ∉ S := hr'.2
    rw [Set.indicator_of_notMem hr'S, Set.indicator_of_notMem hr]

private theorem hasCompactSupport_indicator_T (S : Set (Fin 3 → v.adicCompletion ℚ))
    {Φ : (Fin 3 → v.adicCompletion ℚ) → ℂ} (hΦ : HasCompactSupport Φ) : HasCompactSupport (S.indicator Φ) :=
  hΦ.mono fun r hr h0 => hr (by simp [h0])

end CellCoordinateTestFunctions
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_eventually_threefold_twistedDifference_dualJacquetValueFn_eq_zero.LaurentZetaSlot P2MW.S_LanglandsTunnell_CubicInduction_eventually_threefold_twistedDifference_dualJacquetValueFn_eq_zero.WeylTranslateZeta"

end WeylTranslateZeta
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_eventually_threefold_twistedDifference_dualJacquetValueFn_eq_zero.LaurentZetaSlot P2MW.S_LanglandsTunnell_CubicInduction_eventually_threefold_twistedDifference_dualJacquetValueFn_eq_zero.WeylTranslateZeta"
end
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_eventually_threefold_twistedDifference_dualJacquetValueFn_eq_zero.LaurentZetaSlot P2MW.S_LanglandsTunnell_CubicInduction_eventually_threefold_twistedDifference_dualJacquetValueFn_eq_zero.WeylTranslateZeta"

section

open IsDedekindDomain NumberField

namespace WeylTranslateZeta
open LanglandsTunnell.CubicInduction

section CellCoordinateTransport

variable (v : HeightOneSpectrum (𝓞 ℚ))

private theorem isTestTransport_dualTailMap (x : v.adicCompletion ℚ) :
    IsTestTransport v fun s : (v.adicCompletion ℚ)ˣ => dualTailMap v x (s : v.adicCompletion ℚ) := by
  intro Φ hΦl hΦc s _ _
  exact ⟨isLocallyConstant_comp_dualTailMap v hΦl x (s : v.adicCompletion ℚ),
    hasCompactSupport_comp_dualTailMap v hΦc x s.ne_zero⟩

private theorem pullbackSubVanishesNear_dualTailMap {x : v.adicCompletion ℚ} (hx : x ≠ 0) :
    PullbackSubVanishesNear v (bulkGauge v x) (fun r => r 0)
      fun s : (v.adicCompletion ℚ)ˣ => dualTailMap v x (s : v.adicCompletion ℚ) := by
  intro Φ hΦl hΦc
  obtain ⟨δ, hδ, hδΦ⟩ := exists_forall_dualTailMap_eq v hΦl hΦc x
  obtain ⟨R, hR⟩ := exists_support_radius v Φ hΦc
  have hxpos : 0 < ‖x‖ := norm_pos_iff.2 hx
  set M : ℝ := max R 1 with hM
  have hMpos : 0 < M := lt_of_lt_of_le one_pos (le_max_right R 1)
  refine ⟨min δ (min (‖x‖ * δ) (δ / M)), lt_min hδ (lt_min (mul_pos hxpos hδ) (div_pos hδ hMpos)),
    fun s _ hs r hA hB => ?_⟩
  have hAδ : ‖bulkGauge v x r‖ ≤ min (‖x‖ * δ) (δ / M) := hA.trans (min_le_right _ _)
  have hB0 : ‖r 0‖ ≤ δ := hB.trans (min_le_left _ _)
  have hBM : ‖r 0‖ ≤ δ / M := hB.trans ((min_le_right _ _).trans (min_le_right _ _))
  show Φ (dualTailMap v x (s : v.adicCompletion ℚ) r) - Φ r = 0
  by_cases hr₂ : R < ‖r 2‖
  ·
    have h₁ : Φ r = 0 := by
      by_contra h
      exact absurd (hR r h 2) (not_le.2 hr₂)
    have h₂ : Φ (dualTailMap v x (s : v.adicCompletion ℚ) r) = 0 := by
      by_contra h
      have := hR _ h 2
      rw [dualTailMap_apply_two] at this
      exact absurd this (not_le.2 hr₂)
    rw [h₁, h₂, sub_self]
  ·
    rw [not_lt] at hr₂
    have hR0 : 0 ≤ R := (norm_nonneg _).trans hr₂
    have hu : x * (r 1 + 1 / x) = bulkGauge v x r + x * r 2 * r 0 := by
      rw [bulkGauge_def, mul_add, mul_one_div_cancel hx]; ring
    have h1 : ‖r 1 + 1 / x‖ ≤ δ := by
      have hmax : ‖x‖ * ‖r 1 + 1 / x‖ ≤ max ‖bulkGauge v x r‖ ‖x * r 2 * r 0‖ := by
        rw [← norm_mul, hu]; exact IsUltrametricDist.norm_add_le_max _ _
      rcases le_max_iff.1 hmax with h | h
      · have h' : ‖x‖ * ‖r 1 + 1 / x‖ ≤ ‖x‖ * δ := h.trans (hAδ.trans (min_le_left _ _))
        exact le_of_mul_le_mul_left h' hxpos
      · have h' : ‖x‖ * ‖r 1 + 1 / x‖ ≤ ‖x‖ * δ := by
          refine h.trans ?_
          rw [norm_mul, norm_mul, mul_assoc]
          refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg x)
          calc ‖r 2‖ * ‖r 0‖ ≤ R * (δ / M) := mul_le_mul hr₂ hBM (norm_nonneg _) hR0
            _ ≤ M * (δ / M) := mul_le_mul_of_nonneg_right (le_max_left R 1) (div_pos hδ hMpos).le
            _ = δ := by field_simp
        exact le_of_mul_le_mul_left h' hxpos
    rw [hδΦ (s : v.adicCompletion ℚ) hs r hB0 h1, sub_self]

end CellCoordinateTransport
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_eventually_threefold_twistedDifference_dualJacquetValueFn_eq_zero.LaurentZetaSlot P2MW.S_LanglandsTunnell_CubicInduction_eventually_threefold_twistedDifference_dualJacquetValueFn_eq_zero.WeylTranslateZeta"

end WeylTranslateZeta
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_eventually_threefold_twistedDifference_dualJacquetValueFn_eq_zero.LaurentZetaSlot P2MW.S_LanglandsTunnell_CubicInduction_eventually_threefold_twistedDifference_dualJacquetValueFn_eq_zero.WeylTranslateZeta"
end
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_eventually_threefold_twistedDifference_dualJacquetValueFn_eq_zero.LaurentZetaSlot P2MW.S_LanglandsTunnell_CubicInduction_eventually_threefold_twistedDifference_dualJacquetValueFn_eq_zero.WeylTranslateZeta"

section

open IsDedekindDomain NumberField MeasureTheory LanglandsTunnell.TateLocal
open scoped ENNReal

namespace WeylTranslateZeta
open LanglandsTunnell.CubicInduction

section UnipotentSubstitutions

variable (v : HeightOneSpectrum (𝓞 ℚ))

private theorem integral_jacquetHaar3_comp_scale_snd (s : v.adicCompletion ℚ) (hs : s ≠ 0)
    (G : v.adicCompletion ℚ × v.adicCompletion ℚ × v.adicCompletion ℚ → ℂ) :
    letI := localBorel ℚ v
    ∫ p, G p ∂(jacquetHaar3 v) = ((‖s‖ ^ 2 : ℝ) : ℂ) * ∫ p, G (p.1, s * p.2.1, s * p.2.2) ∂(jacquetHaar3 v) := by
  letI := localBorel ℚ v
  haveI : BorelSpace (v.adicCompletion ℚ) := borelSpace_localBorel ℚ v
  haveI := sFinite_selfDualHaarAt ℚ v
  set μ := selfDualHaarAt ℚ v with hμ
  have hmap1 : Measure.map (fun x : v.adicCompletion ℚ => s * x) μ = ((modulus s : ℝ≥0∞))⁻¹ • μ := by
    have h := map_mul_left_selfDualHaarAt ℚ v (Units.mk0 s hs)
    simpa only [Units.val_mk0] using h
  set e₁ : v.adicCompletion ℚ ≃ᵐ v.adicCompletion ℚ := MeasurableEquiv.mulLeft₀ s hs with he₁
  set e : v.adicCompletion ℚ × v.adicCompletion ℚ × v.adicCompletion ℚ ≃ᵐ
      v.adicCompletion ℚ × v.adicCompletion ℚ × v.adicCompletion ℚ :=
    (MeasurableEquiv.refl (v.adicCompletion ℚ)).prodCongr (e₁.prodCongr e₁) with he
  have hecoe : (⇑e) = Prod.map id (Prod.map (fun x => s * x) fun x => s * x) := rfl
  have hjac : jacquetHaar3 v = μ.prod (μ.prod μ) := rfl
  have hms : Measurable fun x : v.adicCompletion ℚ => s * x := measurable_const_mul s
  have hmap : Measure.map e (jacquetHaar3 v) =
      (((modulus s : ℝ≥0∞))⁻¹ * ((modulus s : ℝ≥0∞))⁻¹) • jacquetHaar3 v := by
    rw [hjac, hecoe, ← Measure.map_prod_map μ (μ.prod μ) measurable_id (hms.prodMap hms),
      ← Measure.map_prod_map μ μ hms hms, hmap1, Measure.map_id, Measure.prod_smul_left, Measure.prod_smul_right,
      Measure.prod_smul_right, Measure.prod_smul_right, smul_smul]
  have hint := integral_map_equiv (μ := jacquetHaar3 v) e G
  rw [hmap, integral_smul_measure] at hint
  have hs0 : (‖s‖ : ℝ) ≠ 0 := norm_ne_zero_iff.mpr hs
  have hmod : ((modulus s : ℝ≥0∞))⁻¹.toReal = ‖s‖⁻¹ := by
    rw [ENNReal.toReal_inv, ENNReal.coe_toReal, modulus_real_eq_norm v s]
  have hc : (((modulus s : ℝ≥0∞))⁻¹ * ((modulus s : ℝ≥0∞))⁻¹).toReal = (‖s‖ ^ 2)⁻¹ := by
    rw [ENNReal.toReal_mul, hmod, ← mul_inv, sq]
  rw [hc] at hint
  have hint' : ∫ x, G (e x) ∂(jacquetHaar3 v) = ∫ p, G (p.1, s * p.2.1, s * p.2.2) ∂(jacquetHaar3 v) := rfl
  have h2 : ((‖s‖ ^ 2 : ℝ) : ℂ) * (((‖s‖ ^ 2)⁻¹ : ℝ) : ℂ) = 1 := by
    rw [← Complex.ofReal_mul, mul_inv_cancel₀ (pow_ne_zero 2 hs0), Complex.ofReal_one]
  rw [← hint', ← hint, Complex.real_smul, ← mul_assoc, h2, one_mul]

private theorem integral_jacquetHaar3_comp_scale_third (s : v.adicCompletion ℚ) (hs : s ≠ 0)
    (G : v.adicCompletion ℚ × v.adicCompletion ℚ × v.adicCompletion ℚ → ℂ) :
    letI := localBorel ℚ v
    ∫ p, G p ∂(jacquetHaar3 v) = (‖s‖ : ℂ) * ∫ p, G (p.1, p.2.1, s * p.2.2) ∂(jacquetHaar3 v) := by
  letI := localBorel ℚ v
  haveI : BorelSpace (v.adicCompletion ℚ) := borelSpace_localBorel ℚ v
  haveI := sFinite_selfDualHaarAt ℚ v
  set μ := selfDualHaarAt ℚ v with hμ
  have hmap1 : Measure.map (fun x : v.adicCompletion ℚ => s * x) μ = ((modulus s : ℝ≥0∞))⁻¹ • μ := by
    have h := map_mul_left_selfDualHaarAt ℚ v (Units.mk0 s hs)
    simpa only [Units.val_mk0] using h
  set e₁ : v.adicCompletion ℚ ≃ᵐ v.adicCompletion ℚ := MeasurableEquiv.mulLeft₀ s hs with he₁
  set e : v.adicCompletion ℚ × v.adicCompletion ℚ × v.adicCompletion ℚ ≃ᵐ
      v.adicCompletion ℚ × v.adicCompletion ℚ × v.adicCompletion ℚ :=
    (MeasurableEquiv.refl (v.adicCompletion ℚ)).prodCongr
      ((MeasurableEquiv.refl (v.adicCompletion ℚ)).prodCongr e₁) with he
  have hecoe : (⇑e) = Prod.map id (Prod.map id fun x => s * x) := rfl
  have hjac : jacquetHaar3 v = μ.prod (μ.prod μ) := rfl
  have hms : Measurable fun x : v.adicCompletion ℚ => s * x := measurable_const_mul s
  have hmap : Measure.map e (jacquetHaar3 v) = ((modulus s : ℝ≥0∞))⁻¹ • jacquetHaar3 v := by
    rw [hjac, hecoe, ← Measure.map_prod_map μ (μ.prod μ) measurable_id (measurable_id.prodMap hms),
      ← Measure.map_prod_map μ μ measurable_id hms, hmap1, Measure.map_id, Measure.prod_smul_right,
      Measure.prod_smul_right]
  have hint := integral_map_equiv (μ := jacquetHaar3 v) e G
  rw [hmap, integral_smul_measure] at hint
  have hs0 : ((‖s‖ : ℝ) : ℂ) ≠ 0 := by exact_mod_cast norm_ne_zero_iff.mpr hs
  have hmod : ((modulus s : ℝ≥0∞))⁻¹.toReal = ‖s‖⁻¹ := by
    rw [ENNReal.toReal_inv, ENNReal.coe_toReal, modulus_real_eq_norm v s]
  rw [hmod] at hint
  have hint' : ∫ x, G (e x) ∂(jacquetHaar3 v) = ∫ p, G (p.1, p.2.1, s * p.2.2) ∂(jacquetHaar3 v) := rfl
  rw [← hint', ← hint, Complex.real_smul, ← mul_assoc]
  push_cast
  rw [mul_inv_cancel₀ hs0, one_mul]

private theorem integral_jacquetHaar3_comp_add_mul (k : v.adicCompletion ℚ)
    (G : v.adicCompletion ℚ × v.adicCompletion ℚ × v.adicCompletion ℚ → ℂ)
    (hG : letI := localBorel ℚ v
      Integrable G (jacquetHaar3 v))
    (hG' : letI := localBorel ℚ v
      Integrable (fun p : v.adicCompletion ℚ × v.adicCompletion ℚ × v.adicCompletion ℚ =>
        G (p.1, p.2.1 + k, p.2.2 + p.1 * k)) (jacquetHaar3 v)) :
    letI := localBorel ℚ v
    ∫ p, G p ∂(jacquetHaar3 v) = ∫ p, G (p.1, p.2.1 + k, p.2.2 + p.1 * k) ∂(jacquetHaar3 v) := by
  letI := localBorel ℚ v
  haveI : BorelSpace (v.adicCompletion ℚ) := borelSpace_localBorel ℚ v
  haveI := sFinite_selfDualHaarAt ℚ v
  haveI := isAddHaarMeasure_selfDualHaarAt ℚ v
  set μ := selfDualHaarAt ℚ v with hμ
  have hjac : jacquetHaar3 v = μ.prod (μ.prod μ) := rfl
  rw [hjac] at hG hG' ⊢
  rw [integral_prod G hG, integral_prod _ hG']
  refine integral_congr_ae (Filter.Eventually.of_forall fun α => ?_)
  exact (integral_add_right_eq_self (μ := μ.prod μ) (fun q : v.adicCompletion ℚ × v.adicCompletion ℚ => G (α, q))
    (k, α * k)).symm

end UnipotentSubstitutions
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_eventually_threefold_twistedDifference_dualJacquetValueFn_eq_zero.LaurentZetaSlot P2MW.S_LanglandsTunnell_CubicInduction_eventually_threefold_twistedDifference_dualJacquetValueFn_eq_zero.WeylTranslateZeta"

end WeylTranslateZeta
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_eventually_threefold_twistedDifference_dualJacquetValueFn_eq_zero.LaurentZetaSlot P2MW.S_LanglandsTunnell_CubicInduction_eventually_threefold_twistedDifference_dualJacquetValueFn_eq_zero.WeylTranslateZeta"
end
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_eventually_threefold_twistedDifference_dualJacquetValueFn_eq_zero.LaurentZetaSlot P2MW.S_LanglandsTunnell_CubicInduction_eventually_threefold_twistedDifference_dualJacquetValueFn_eq_zero.WeylTranslateZeta"

section

open IsDedekindDomain NumberField LanglandsTunnell.TateLocal

namespace WeylTranslateZeta
open LanglandsTunnell.CubicInduction

section DualSliceFunctional

variable (v : HeightOneSpectrum (𝓞 ℚ))
variable (ν : Fin 3 → ((v.adicCompletion ℚ)ˣ →* ℂˣ))

private theorem dualSlice_coe_units (Φ : (Fin 3 → v.adicCompletion ℚ) → ℂ) (x : v.adicCompletion ℚ)
    (a : (v.adicCompletion ℚ)ˣ) :
    dualSlice v ν Φ x a.val =
      jacquetValue v (dualTranslate v ν Φ a x) * (((modulus a.val : ℝ) : ℂ))⁻¹ := by
  simp only [dualSlice, dif_neg a.ne_zero, Units.mk0_val]

private theorem dualTranslate_add (Φ Ψ : (Fin 3 → v.adicCompletion ℚ) → ℂ) (a : (v.adicCompletion ℚ)ˣ)
    (x : v.adicCompletion ℚ) :
    dualTranslate v ν (Φ + Ψ) a x =
      dualTranslate v ν Φ a x + dualTranslate v ν Ψ a x := by
  unfold dualTranslate
  rw [cellSectionOf_add, map_add]

private theorem isTestAdditive_dualSlice (hν : ∀ i, IsLocallyConstant (ν i)) (x : v.adicCompletion ℚ) :
    IsTestAdditive v fun Ψ t => dualSlice v ν Ψ x t := by
  intro Φ Ψ hΦl hΦc hΨl hΨc t
  show dualSlice v ν (Φ + Ψ) x t = dualSlice v ν Φ x t + dualSlice v ν Ψ x t
  by_cases ht : t = 0
  · simp only [ht, dualSlice_zero, add_zero]
  · obtain ⟨a, rfl⟩ : ∃ a : (v.adicCompletion ℚ)ˣ, a.val = t := ⟨Units.mk0 t ht, rfl⟩
    rw [dualSlice_coe_units, dualSlice_coe_units, dualSlice_coe_units, dualTranslate_add, ← add_mul]
    congr 1
    have hsum := exists_level_dualTranslate v ν (Φ + Ψ) hν (hΦl.add hΨl) (hΦc.add hΨc) a x
    rw [dualTranslate_add] at hsum
    refine jacquetValue_add_of v ?_ ?_ hsum
    · exact exists_forall_le_integrableOn_and_jacquetTruncated3_eq_of_cellSectionOf v ν hν Φ ⟨hΦl, hΦc⟩
        (dualPoint v a x)
    · exact exists_forall_le_integrableOn_and_jacquetTruncated3_eq_of_cellSectionOf v ν hν Ψ ⟨hΨl, hΨc⟩
        (dualPoint v a x)

private theorem jacquetValue_mul_modulus_mul_inv_of_eq {J J' κ : ℂ} {a s : (v.adicCompletion ℚ)ˣ}
    (hJ : J = κ * ((‖s.val‖ : ℝ) : ℂ) * J') :
    J * (((modulus (a * s).val : ℝ) : ℂ))⁻¹ = κ * (J' * (((modulus a.val : ℝ) : ℂ))⁻¹) := by
  have hs0 : ((‖s.val‖ : ℝ) : ℂ) ≠ 0 := by exact_mod_cast norm_ne_zero_iff.mpr s.ne_zero
  rw [hJ, Units.val_mul, modulus_mul, NNReal.coe_mul, modulus_real_eq_norm v a.val, modulus_real_eq_norm v s.val,
    Complex.ofReal_mul, mul_inv]
  calc κ * ((‖s.val‖ : ℝ) : ℂ) * J' * ((((‖a.val‖ : ℝ) : ℂ))⁻¹ * (((‖s.val‖ : ℝ) : ℂ))⁻¹)
      = κ * (J' * (((‖a.val‖ : ℝ) : ℂ))⁻¹) * (((‖s.val‖ : ℝ) : ℂ) * (((‖s.val‖ : ℝ) : ℂ))⁻¹) := by ring
    _ = κ * (J' * (((‖a.val‖ : ℝ) : ℂ))⁻¹) := by rw [mul_inv_cancel₀ hs0, mul_one]

private theorem dualSlice_mul_eq_of_jacquetValue_eq (Ψ Ψ' : (Fin 3 → v.adicCompletion ℚ) → ℂ) (x : v.adicCompletion ℚ)
    (a s : (v.adicCompletion ℚ)ˣ) {κ : ℂ}
    (h : jacquetValue v (dualTranslate v ν Ψ (a * s) x) =
      κ * ((‖s.val‖ : ℝ) : ℂ) * jacquetValue v (dualTranslate v ν Ψ' a x)) :
    dualSlice v ν Ψ x (s.val * a.val) = κ * dualSlice v ν Ψ' x a.val := by
  have hsa : s.val * a.val = (a * s).val := by rw [Units.val_mul, mul_comm]
  rw [hsa, dualSlice_coe_units, dualSlice_coe_units]
  exact jacquetValue_mul_modulus_mul_inv_of_eq v h

end DualSliceFunctional
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_eventually_threefold_twistedDifference_dualJacquetValueFn_eq_zero.LaurentZetaSlot P2MW.S_LanglandsTunnell_CubicInduction_eventually_threefold_twistedDifference_dualJacquetValueFn_eq_zero.WeylTranslateZeta"

end WeylTranslateZeta
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_eventually_threefold_twistedDifference_dualJacquetValueFn_eq_zero.LaurentZetaSlot P2MW.S_LanglandsTunnell_CubicInduction_eventually_threefold_twistedDifference_dualJacquetValueFn_eq_zero.WeylTranslateZeta"
end
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_eventually_threefold_twistedDifference_dualJacquetValueFn_eq_zero.LaurentZetaSlot P2MW.S_LanglandsTunnell_CubicInduction_eventually_threefold_twistedDifference_dualJacquetValueFn_eq_zero.WeylTranslateZeta"

section

open IsDedekindDomain NumberField LanglandsTunnell.TateLocal

namespace WeylTranslateZeta
open LanglandsTunnell.CubicInduction

section DualCovariance

variable (v : HeightOneSpectrum (𝓞 ℚ)) (ν : Fin 3 → ((v.adicCompletion ℚ)ˣ →* ℂˣ))

private theorem charExt_div_units (χ : (v.adicCompletion ℚ)ˣ →* ℂˣ) (y : v.adicCompletion ℚ)
    (s : (v.adicCompletion ℚ)ˣ) : charExt χ (y / s.val) = charExt χ y * ((χ s : ℂ))⁻¹ := by
  rw [div_eq_mul_inv, ← Units.val_inv_eq_inv_val, charExt_mul ℚ v, charExt_coe_units, map_inv,
    Units.val_inv_eq_inv_val]

private theorem cornerEntry_dualCellPoint_scaleCoords (α β γ x : v.adicCompletion ℚ) (a s : (v.adicCompletion ℚ)ˣ) :
    cornerEntry v (dualCellPoint v α (s.val * β) (s.val * γ) (a * s) x) =
      cornerEntry v (dualCellPoint v α β γ a x) := by
  have ha : a.val ≠ 0 := a.ne_zero
  have hs : s.val ≠ 0 := s.ne_zero
  rw [cornerEntry_dualCellPoint, cornerEntry_dualCellPoint, Units.val_mul]
  field_simp

private theorem lowerMinor_dualCellPoint_scaleCoords (α β γ x : v.adicCompletion ℚ) (a s : (v.adicCompletion ℚ)ˣ) :
    lowerMinor v (dualCellPoint v α (s.val * β) (s.val * γ) (a * s) x) = lowerMinor v (dualCellPoint v α β γ a x) := by
  have ha : a.val ≠ 0 := a.ne_zero
  have hs : s.val ≠ 0 := s.ne_zero
  rw [lowerMinor_dualCellPoint, lowerMinor_dualCellPoint, Units.val_mul]
  field_simp

private theorem outerMinor_dualCellPoint_scaleCoords (α β γ x : v.adicCompletion ℚ) (a s : (v.adicCompletion ℚ)ˣ) :
    outerMinor v (dualCellPoint v α (s.val * β) (s.val * γ) (a * s) x) = outerMinor v (dualCellPoint v α β γ a x) := by
  have ha : a.val ≠ 0 := a.ne_zero
  have hs : s.val ≠ 0 := s.ne_zero
  rw [outerMinor_dualCellPoint, outerMinor_dualCellPoint, Units.val_mul]
  field_simp

private theorem gl3Det_dualCellPoint_scaleCoords (α β γ x : v.adicCompletion ℚ) (a s : (v.adicCompletion ℚ)ˣ) :
    gl3Det v (dualCellPoint v α (s.val * β) (s.val * γ) (a * s) x) = gl3Det v (dualCellPoint v α β γ a x) / s.val := by
  rw [gl3Det_dualCellPoint, gl3Det_dualCellPoint, Units.val_mul, mul_inv, div_eq_mul_inv]

private theorem dualCellPoint_scaleCoords_mem_bigCell3_iff (α β γ x : v.adicCompletion ℚ)
    (a s : (v.adicCompletion ℚ)ˣ) :
    dualCellPoint v α (s.val * β) (s.val * γ) (a * s) x ∈ bigCell3 v ↔ dualCellPoint v α β γ a x ∈ bigCell3 v := by
  simp only [bigCell3, Set.mem_setOf_eq, cornerEntry_dualCellPoint_scaleCoords, lowerMinor_dualCellPoint_scaleCoords]

private theorem cellRatio_dualCellPoint_scaleCoords (α β γ x : v.adicCompletion ℚ) (a s : (v.adicCompletion ℚ)ˣ) :
    cellRatio v (dualCellPoint v α (s.val * β) (s.val * γ) (a * s) x) = cellRatio v (dualCellPoint v α β γ a x) := by
  have ha : a.val ≠ 0 := a.ne_zero
  have hs : s.val ≠ 0 := s.ne_zero
  have h21 : gl3Entry v (dualCellPoint v α (s.val * β) (s.val * γ) (a * s) x) 2 1 =
      gl3Entry v (dualCellPoint v α β γ a x) 2 1 := by
    rw [gl3Entry_dualCellPoint, gl3Entry_dualCellPoint]
    simp
  have h22 : gl3Entry v (dualCellPoint v α (s.val * β) (s.val * γ) (a * s) x) 2 2 =
      gl3Entry v (dualCellPoint v α β γ a x) 2 2 := by
    rw [gl3Entry_dualCellPoint, gl3Entry_dualCellPoint, Units.val_mul]
    simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons,
      Matrix.empty_val']
    field_simp
  rw [cellRatio, cellRatio, h21, h22, cornerEntry_dualCellPoint_scaleCoords, outerMinor_dualCellPoint_scaleCoords,
    lowerMinor_dualCellPoint_scaleCoords]

private theorem cellValue_dualCellPoint_scaleCoords (α β γ x : v.adicCompletion ℚ) (a s : (v.adicCompletion ℚ)ˣ) :
    cellValue v ν (dualCellPoint v α (s.val * β) (s.val * γ) (a * s) x) =
      ((ν 0 s : ℂ))⁻¹ * ((‖s.val‖ : ℝ) : ℂ)⁻¹ * cellValue v ν (dualCellPoint v α β γ a x) := by
  have hs : s.val ≠ 0 := s.ne_zero
  rw [cellValue, cellValue, gl3Det_dualCellPoint_scaleCoords, lowerMinor_dualCellPoint_scaleCoords,
    cornerEntry_dualCellPoint_scaleCoords, div_right_comm, charExt_div_units, norm_div]
  push_cast
  ring

private theorem cellSectionOf_dualCellPoint_scaleCoords (Φ : (Fin 3 → v.adicCompletion ℚ) → ℂ)
    (α β γ x : v.adicCompletion ℚ) (a s : (v.adicCompletion ℚ)ˣ) :
    cellSectionOf v ν Φ (dualCellPoint v α (s.val * β) (s.val * γ) (a * s) x) =
      ((ν 0 s : ℂ))⁻¹ * ((‖s.val‖ : ℝ) : ℂ)⁻¹ * cellSectionOf v ν Φ (dualCellPoint v α β γ a x) := by
  by_cases hmem : dualCellPoint v α β γ a x ∈ bigCell3 v
  · have hmem' := (dualCellPoint_scaleCoords_mem_bigCell3_iff v α β γ x a s).mpr hmem
    rw [cellSectionOf_apply_of_mem v ν Φ hmem', cellSectionOf_apply_of_mem v ν Φ hmem,
      cellValue_dualCellPoint_scaleCoords, cellRatio_dualCellPoint_scaleCoords]
    ring
  · have hmem' : dualCellPoint v α (s.val * β) (s.val * γ) (a * s) x ∉ bigCell3 v := fun h =>
      hmem ((dualCellPoint_scaleCoords_mem_bigCell3_iff v α β γ x a s).mp h)
    rw [cellSectionOf_apply_of_notMem v ν Φ hmem', cellSectionOf_apply_of_notMem v ν Φ hmem, mul_zero]

private theorem cornerEntry_dualCellPoint_translateCoords {x : v.adicCompletion ℚ} (hx : x ≠ 0)
    (α β γ : v.adicCompletion ℚ) (a s : (v.adicCompletion ℚ)ˣ) :
    cornerEntry v (dualCellPoint v α (β + a.val * (s.val - 1) / x) (γ + a.val * α * (s.val - 1) / x) (a * s) x) =
      cornerEntry v (dualCellPoint v α β γ a x) / s.val := by
  have ha : a.val ≠ 0 := a.ne_zero
  have hs : s.val ≠ 0 := s.ne_zero
  rw [cornerEntry_dualCellPoint, cornerEntry_dualCellPoint, Units.val_mul]
  field_simp
  ring

private theorem lowerMinor_dualCellPoint_translateCoords {x : v.adicCompletion ℚ} (hx : x ≠ 0)
    (α β γ : v.adicCompletion ℚ) (a s : (v.adicCompletion ℚ)ˣ) :
    lowerMinor v (dualCellPoint v α (β + a.val * (s.val - 1) / x) (γ + a.val * α * (s.val - 1) / x) (a * s) x) =
      lowerMinor v (dualCellPoint v α β γ a x) / s.val := by
  have ha : a.val ≠ 0 := a.ne_zero
  have hs : s.val ≠ 0 := s.ne_zero
  rw [lowerMinor_dualCellPoint, lowerMinor_dualCellPoint, Units.val_mul]
  field_simp
  ring

private theorem outerMinor_dualCellPoint_translateCoords {x : v.adicCompletion ℚ} (hx : x ≠ 0)
    (α β γ : v.adicCompletion ℚ) (a s : (v.adicCompletion ℚ)ˣ) :
    outerMinor v (dualCellPoint v α (β + a.val * (s.val - 1) / x) (γ + a.val * α * (s.val - 1) / x) (a * s) x) =
      outerMinor v (dualCellPoint v α β γ a x) / s.val := by
  have ha : a.val ≠ 0 := a.ne_zero
  have hs : s.val ≠ 0 := s.ne_zero
  rw [outerMinor_dualCellPoint, outerMinor_dualCellPoint, Units.val_mul]
  field_simp
  ring

private theorem gl3Det_dualCellPoint_translateCoords (x α β γ : v.adicCompletion ℚ) (a s : (v.adicCompletion ℚ)ˣ) :
    gl3Det v (dualCellPoint v α (β + a.val * (s.val - 1) / x) (γ + a.val * α * (s.val - 1) / x) (a * s) x) =
      gl3Det v (dualCellPoint v α β γ a x) / s.val := by
  rw [gl3Det_dualCellPoint, gl3Det_dualCellPoint, Units.val_mul, mul_inv, div_eq_mul_inv]

private theorem dualCellPoint_translateCoords_mem_bigCell3_iff {x : v.adicCompletion ℚ} (hx : x ≠ 0)
    (α β γ : v.adicCompletion ℚ) (a s : (v.adicCompletion ℚ)ˣ) :
    dualCellPoint v α (β + a.val * (s.val - 1) / x) (γ + a.val * α * (s.val - 1) / x) (a * s) x ∈ bigCell3 v ↔
      dualCellPoint v α β γ a x ∈ bigCell3 v := by
  have hs : s.val ≠ 0 := s.ne_zero
  simp only [bigCell3, Set.mem_setOf_eq, cornerEntry_dualCellPoint_translateCoords v hx,
    lowerMinor_dualCellPoint_translateCoords v hx, div_ne_zero_iff]
  exact ⟨fun h => ⟨h.1.1, h.2.1⟩, fun h => ⟨⟨h.1, hs⟩, h.2, hs⟩⟩

private theorem cellRatio_dualCellPoint_translateCoords {x : v.adicCompletion ℚ} (hx : x ≠ 0)
    (α β γ : v.adicCompletion ℚ) (a s : (v.adicCompletion ℚ)ˣ) (hmem : dualCellPoint v α β γ a x ∈ bigCell3 v) :
    cellRatio v (dualCellPoint v α (β + a.val * (s.val - 1) / x) (γ + a.val * α * (s.val - 1) / x) (a * s) x) =
      ![s.val * cellRatio v (dualCellPoint v α β γ a x) 0,
        s.val * cellRatio v (dualCellPoint v α β γ a x) 1 + (s.val - 1) / x,
        cellRatio v (dualCellPoint v α β γ a x) 2] := by
  have ha : a.val ≠ 0 := a.ne_zero
  have hs : s.val ≠ 0 := s.ne_zero
  have hcorner : cornerEntry v (dualCellPoint v α β γ a x) ≠ 0 := hmem.1
  have hc' := cornerEntry_dualCellPoint_translateCoords v hx α β γ a s
  have hl' := lowerMinor_dualCellPoint_translateCoords v hx α β γ a s
  have ho' := outerMinor_dualCellPoint_translateCoords v hx α β γ a s
  have h21 : gl3Entry v (dualCellPoint v α (β + a.val * (s.val - 1) / x) (γ + a.val * α * (s.val - 1) / x)
      (a * s) x) 2 1 = 1 := by
    rw [gl3Entry_dualCellPoint]
    simp
  have h21' : gl3Entry v (dualCellPoint v α β γ a x) 2 1 = 1 := by
    rw [gl3Entry_dualCellPoint]
    simp
  have h22 : gl3Entry v (dualCellPoint v α (β + a.val * (s.val - 1) / x) (γ + a.val * α * (s.val - 1) / x)
      (a * s) x) 2 2 = (γ + a.val * α * (s.val - 1) / x) / (a.val * s.val) := by
    rw [gl3Entry_dualCellPoint, Units.val_mul]
    simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons,
      Matrix.empty_val']
    rw [div_eq_mul_inv _ (a.val * s.val)]
  have h22' : gl3Entry v (dualCellPoint v α β γ a x) 2 2 = γ / a.val := by
    rw [gl3Entry_dualCellPoint]
    simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons,
      Matrix.empty_val']
    rw [div_eq_mul_inv]
  have hαc : α = cornerEntry v (dualCellPoint v α β γ a x) + γ * x / a.val := by
    rw [cornerEntry_dualCellPoint]
    ring
  rw [cellRatio, cellRatio, h21, h21', h22, h22', hc', hl', ho']
  generalize cornerEntry v (dualCellPoint v α β γ a x) = c at hcorner hαc
  subst hαc
  ext i
  fin_cases i <;> simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.tail_cons, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk]
  · field_simp
  · field_simp
    try ring1
  · rw [div_div_div_cancel_right₀ hs]

private theorem cellValue_dualCellPoint_translateCoords (x α β γ : v.adicCompletion ℚ) (hx : x ≠ 0)
    (a s : (v.adicCompletion ℚ)ˣ) :
    cellValue v ν (dualCellPoint v α (β + a.val * (s.val - 1) / x) (γ + a.val * α * (s.val - 1) / x) (a * s) x) =
      ((ν 2 s : ℂ))⁻¹ * ((‖s.val‖ : ℝ) : ℂ) * cellValue v ν (dualCellPoint v α β γ a x) := by
  have hs : s.val ≠ 0 := s.ne_zero
  rw [cellValue, cellValue, gl3Det_dualCellPoint_translateCoords, lowerMinor_dualCellPoint_translateCoords v hx,
    cornerEntry_dualCellPoint_translateCoords v hx, div_div_div_cancel_right₀ hs, div_div_div_cancel_right₀ hs,
    charExt_div_units, norm_div (cornerEntry v (dualCellPoint v α β γ a x)) s.val, div_div_eq_mul_div]
  push_cast
  ring

private theorem cellSectionOf_dualCellPoint_translateCoords (Φ : (Fin 3 → v.adicCompletion ℚ) → ℂ)
    {x : v.adicCompletion ℚ} (hx : x ≠ 0) (α β γ : v.adicCompletion ℚ) (a s : (v.adicCompletion ℚ)ˣ) :
    cellSectionOf v ν Φ
        (dualCellPoint v α (β + a.val * (s.val - 1) / x) (γ + a.val * α * (s.val - 1) / x) (a * s) x) =
      ((ν 2 s : ℂ))⁻¹ * ((‖s.val‖ : ℝ) : ℂ) *
        cellSectionOf v ν (fun r => Φ ![s.val * r 0, s.val * r 1 + (s.val - 1) / x, r 2])
          (dualCellPoint v α β γ a x) := by
  by_cases hmem : dualCellPoint v α β γ a x ∈ bigCell3 v
  · have hmem' := (dualCellPoint_translateCoords_mem_bigCell3_iff v hx α β γ a s).mpr hmem
    rw [cellSectionOf_apply_of_mem v ν Φ hmem', cellSectionOf_apply_of_mem v ν _ hmem,
      cellValue_dualCellPoint_translateCoords v ν x α β γ hx,
      cellRatio_dualCellPoint_translateCoords v hx α β γ a s hmem]
    ring
  · have hmem' :
        dualCellPoint v α (β + a.val * (s.val - 1) / x) (γ + a.val * α * (s.val - 1) / x) (a * s) x ∉ bigCell3 v :=
      fun h => hmem ((dualCellPoint_translateCoords_mem_bigCell3_iff v hx α β γ a s).mp h)
    rw [cellSectionOf_apply_of_notMem v ν Φ hmem', cellSectionOf_apply_of_notMem v ν _ hmem, mul_zero]

end DualCovariance
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_eventually_threefold_twistedDifference_dualJacquetValueFn_eq_zero.LaurentZetaSlot P2MW.S_LanglandsTunnell_CubicInduction_eventually_threefold_twistedDifference_dualJacquetValueFn_eq_zero.WeylTranslateZeta"

end WeylTranslateZeta
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_eventually_threefold_twistedDifference_dualJacquetValueFn_eq_zero.LaurentZetaSlot P2MW.S_LanglandsTunnell_CubicInduction_eventually_threefold_twistedDifference_dualJacquetValueFn_eq_zero.WeylTranslateZeta"
end
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_eventually_threefold_twistedDifference_dualJacquetValueFn_eq_zero.LaurentZetaSlot P2MW.S_LanglandsTunnell_CubicInduction_eventually_threefold_twistedDifference_dualJacquetValueFn_eq_zero.WeylTranslateZeta"

section

open IsDedekindDomain NumberField LanglandsTunnell.TateLocal

namespace WeylTranslateZeta
open LanglandsTunnell.CubicInduction

section DualCovarianceThird

variable (v : HeightOneSpectrum (𝓞 ℚ)) (ν : Fin 3 → ((v.adicCompletion ℚ)ˣ →* ℂˣ))

private theorem exists_forall_charExt_one_sub_eq_one (η : (v.adicCompletion ℚ)ˣ →* ℂˣ) (hη : IsLocallyConstant η) :
    ∃ c : ℝ, 0 < c ∧ ∀ ε : v.adicCompletion ℚ, ‖ε‖ ≤ c → charExt η (1 - ε) = 1 := by
  obtain ⟨n, hn⟩ := exists_hasConductorExponentAt_of_isLocallyConstant ℚ v η hη
  have hq : (0 : ℝ) < (Ideal.absNorm v.asIdeal : ℝ) := zero_lt_one.trans (one_lt_absNorm_real v)
  refine ⟨(Ideal.absNorm v.asIdeal : ℝ) ^ (-((max n 1 : ℕ) : ℤ)), zpow_pos hq _, fun ε hε => ?_⟩
  have hval : Valued.v ε ≤ WithZero.exp (-((max n 1 : ℕ) : ℤ)) := valued_le_of_norm_le_zpow v hε
  have hsub : Valued.v ((1 - ε) - 1) ≤ WithZero.exp (-((max n 1 : ℕ) : ℤ)) := by
    rwa [sub_sub_cancel_left, Valuation.map_neg]
  have hone : Valued.v (1 - ε) = 1 := valued_eq_one_of_valued_sub_one_le v (le_max_right n 1) hsub
  have hne : (1 - ε) ≠ 0 := fun h => by simp [h] at hone
  rw [charExt_of_ne_zero η hne]
  have hmem : Units.mk0 (1 - ε) hne ∈ higherUnitsAt ℚ v n := by
    refine ⟨hone, ?_⟩
    rcases Nat.eq_zero_or_pos n with hn0 | hnpos
    · exact Or.inl hn0
    · right
      refine hsub.trans ?_
      rw [max_eq_left hnpos]
  rw [hn.1 _ hmem, Units.val_one]

private theorem norm_one_sub_le_one {s : v.adicCompletion ℚ} (hs : ‖s‖ ≤ 1) : ‖1 - s‖ ≤ 1 := by
  rw [sub_eq_add_neg]
  exact (IsUltrametricDist.norm_add_le_max 1 (-s)).trans (max_le (by simp) (by simpa using hs))

private theorem lower_ne_zero_of_mem (α β γ x : v.adicCompletion ℚ) (a : (v.adicCompletion ℚ)ˣ)
    (hmem : dualCellPoint v α β γ a x ∈ bigCell3 v) : a.val - β * x ≠ 0 := by
  have ha : a.val ≠ 0 := a.ne_zero
  have h := hmem.2
  rw [lowerMinor_dualCellPoint] at h
  intro h0
  apply h
  rw [← sub_eq_zero.mp h0, div_self ha, sub_self]

private theorem gauge_cellRatio_dualCellPoint (α β γ x : v.adicCompletion ℚ) (a : (v.adicCompletion ℚ)ˣ)
    (hmem : dualCellPoint v α β γ a x ∈ bigCell3 v) :
    1 + x * (cellRatio v (dualCellPoint v α β γ a x) 1 -
        cellRatio v (dualCellPoint v α β γ a x) 2 * cellRatio v (dualCellPoint v α β γ a x) 0) =
      a.val / (a.val - β * x) := by
  have ha : a.val ≠ 0 := a.ne_zero
  have hcorner : α - γ * x / a.val ≠ 0 := by
    have h := hmem.1
    rwa [cornerEntry_dualCellPoint] at h
  have hlower : a.val - β * x ≠ 0 := lower_ne_zero_of_mem v α β γ x a hmem
  have el : 1 - β * x / a.val = (a.val - β * x) / a.val := by rw [sub_div, div_self ha]
  have hαc : α = (α - γ * x / a.val) + γ * x / a.val := by ring
  rw [cellRatio_dualCellPoint]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons]
  rw [el]
  generalize α - γ * x / a.val = c at hcorner hαc ⊢
  subst hαc
  generalize hD : a.val - β * x = D at hlower ⊢
  field_simp
  subst hD
  ring

private theorem cornerEntry_dualCellPoint_scaleThird (α β γ x : v.adicCompletion ℚ) (a s : (v.adicCompletion ℚ)ˣ) :
    cornerEntry v (dualCellPoint v α β (s.val * γ) (a * s) x) = cornerEntry v (dualCellPoint v α β γ a x) := by
  have ha : a.val ≠ 0 := a.ne_zero
  have hs : s.val ≠ 0 := s.ne_zero
  rw [cornerEntry_dualCellPoint, cornerEntry_dualCellPoint, Units.val_mul]
  field_simp

private theorem lowerMinor_dualCellPoint_scaleThird (α β γ x : v.adicCompletion ℚ) (a s : (v.adicCompletion ℚ)ˣ) :
    lowerMinor v (dualCellPoint v α β (s.val * γ) (a * s) x) = (a.val * s.val - β * x) / (a.val * s.val) := by
  have ha : a.val ≠ 0 := a.ne_zero
  have hs : s.val ≠ 0 := s.ne_zero
  rw [lowerMinor_dualCellPoint, Units.val_mul]
  field_simp

private theorem gl3Det_dualCellPoint_scaleThird (α β γ x : v.adicCompletion ℚ) (a s : (v.adicCompletion ℚ)ˣ) :
    gl3Det v (dualCellPoint v α β (s.val * γ) (a * s) x) = (a.val * s.val)⁻¹ := by
  rw [gl3Det_dualCellPoint, Units.val_mul]

private theorem cellValue_dualCellPoint_scaleThird (α β γ x : v.adicCompletion ℚ) (a s : (v.adicCompletion ℚ)ˣ)
    (hlower : a.val - β * x ≠ 0) (hlower' : a.val * s.val - β * x ≠ 0)
    (hnorm : ‖a.val * s.val - β * x‖ = ‖a.val - β * x‖)
    (h0 : charExt (ν 0) (1 - a.val * (1 - s.val) / (a.val - β * x)) = 1)
    (h1 : charExt (ν 1) (1 - a.val * (1 - s.val) / (a.val - β * x)) = 1) :
    (ν 1 s : ℂ) * cellValue v ν (dualCellPoint v α β (s.val * γ) (a * s) x) =
      cellValue v ν (dualCellPoint v α β γ a x) := by
  have ha : a.val ≠ 0 := a.ne_zero
  have hs : s.val ≠ 0 := s.ne_zero

  have e0 : gl3Det v (dualCellPoint v α β γ a x) / lowerMinor v (dualCellPoint v α β γ a x) =
      (a.val * s.val)⁻¹ / ((a.val * s.val - β * x) / (a.val * s.val)) *
        (1 - a.val * (1 - s.val) / (a.val - β * x)) := by
    rw [gl3Det_dualCellPoint, lowerMinor_dualCellPoint]
    field_simp
    ring

  have e1 : s.val * (lowerMinor v (dualCellPoint v α β (s.val * γ) (a * s) x) /
        cornerEntry v (dualCellPoint v α β (s.val * γ) (a * s) x)) =
      lowerMinor v (dualCellPoint v α β γ a x) / cornerEntry v (dualCellPoint v α β γ a x) *
        (1 - a.val * (1 - s.val) / (a.val - β * x)) := by
    have el : 1 - β * x / a.val = (a.val - β * x) / a.val := by rw [sub_div, div_self ha]
    rw [lowerMinor_dualCellPoint_scaleThird, cornerEntry_dualCellPoint_scaleThird, lowerMinor_dualCellPoint,
      cornerEntry_dualCellPoint, el]
    by_cases hc : α - γ * x / a.val = 0
    · simp [hc]
    · generalize α - γ * x / a.val = c at hc ⊢
      generalize hD' : a.val * s.val - β * x = D' at hlower' ⊢
      generalize hD : a.val - β * x = D at hlower ⊢
      field_simp
      subst hD hD'
      ring
  have hν1 : (ν 1 s : ℂ) * charExt (ν 1) (lowerMinor v (dualCellPoint v α β (s.val * γ) (a * s) x) /
        cornerEntry v (dualCellPoint v α β (s.val * γ) (a * s) x)) =
      charExt (ν 1) (lowerMinor v (dualCellPoint v α β γ a x) / cornerEntry v (dualCellPoint v α β γ a x)) := by
    rw [← charExt_coe_units, ← charExt_mul ℚ v, e1, charExt_mul ℚ v, h1, mul_one]
  have enorm : ‖gl3Det v (dualCellPoint v α β γ a x) / lowerMinor v (dualCellPoint v α β γ a x)‖ =
      ‖gl3Det v (dualCellPoint v α β (s.val * γ) (a * s) x) /
        lowerMinor v (dualCellPoint v α β (s.val * γ) (a * s) x)‖ := by
    rw [gl3Det_dualCellPoint, lowerMinor_dualCellPoint, gl3Det_dualCellPoint_scaleThird,
      lowerMinor_dualCellPoint_scaleThird]
    have e : (a.val)⁻¹ / (1 - β * x / a.val) = (a.val - β * x)⁻¹ := by
      field_simp
    have e' : (a.val * s.val)⁻¹ / ((a.val * s.val - β * x) / (a.val * s.val)) = (a.val * s.val - β * x)⁻¹ := by
      field_simp
    rw [e, e', norm_inv, norm_inv, hnorm]
  rw [cellValue, cellValue, ← enorm, ← hν1, e0, charExt_mul ℚ v, h0, gl3Det_dualCellPoint_scaleThird,
    lowerMinor_dualCellPoint_scaleThird, cornerEntry_dualCellPoint_scaleThird]
  ring

private theorem cellRatio_dualCellPoint_scaleThird (α β γ x : v.adicCompletion ℚ) (a s : (v.adicCompletion ℚ)ˣ)
    (hlower : a.val - β * x ≠ 0) (hlower' : a.val * s.val - β * x ≠ 0) :
    cellRatio v (dualCellPoint v α β (s.val * γ) (a * s) x) =
      ![cellRatio v (dualCellPoint v α β γ a x) 0, cellRatio v (dualCellPoint v α β γ a x) 1,
        cellRatio v (dualCellPoint v α β γ a x) 2 +
          (s.val - 1) * β * a.val * (α - γ * x / a.val) / ((a.val * s.val - β * x) * (a.val - β * x))] := by
  have ha : a.val ≠ 0 := a.ne_zero
  have hs : s.val ≠ 0 := s.ne_zero
  have has : a.val * s.val ≠ 0 := mul_ne_zero ha hs
  have hcs : α - s.val * γ * x / (a.val * s.val) = α - γ * x / a.val := by
    have h := cornerEntry_dualCellPoint_scaleThird v α β γ x a s
    rwa [cornerEntry_dualCellPoint, cornerEntry_dualCellPoint, Units.val_mul] at h
  have hnum : s.val * γ * (a.val * s.val)⁻¹ = γ * (a.val)⁻¹ := by
    field_simp
    try ring1
  have el : 1 - β * x / a.val = (a.val - β * x) / a.val := by rw [sub_div, div_self ha]
  have el' : 1 - β * x / (a.val * s.val) = (a.val * s.val - β * x) / (a.val * s.val) := by
    rw [sub_div, div_self has]
  rw [cellRatio_dualCellPoint, cellRatio_dualCellPoint, Units.val_mul, hcs, hnum, el, el']
  ext i
  fin_cases i <;> simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.tail_cons, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk] <;> try rfl
  generalize hD' : a.val * s.val - β * x = D' at hlower' ⊢
  generalize hD : a.val - β * x = D at hlower ⊢
  field_simp
  subst hD hD'
  ring

private theorem norm_cellRatio_zero_dualCellPoint (α β γ x : v.adicCompletion ℚ) (a : (v.adicCompletion ℚ)ˣ) :
    ‖cellRatio v (dualCellPoint v α β γ a x) 0‖ = ‖α - γ * x / a.val‖⁻¹ := by
  rw [cellRatio_dualCellPoint]
  simp only [Matrix.cons_val_zero, one_div, norm_inv]

private theorem norm_move_le {ρ rad c₀ : ℝ} {α β γ x : v.adicCompletion ℚ} {a s : (v.adicCompletion ℚ)ˣ}
    (hρ : 0 < ρ) (hrad : 0 < rad) (hc₀rad : c₀ ≤ rad * ρ * ‖x‖)
    (hD : 0 < ‖a.val - β * x‖) (hnorm : ‖a.val * s.val - β * x‖ = ‖a.val - β * x‖) (hs1 : ‖s.val - 1‖ ≤ 1)
    (hβ : ‖β‖ * ‖x‖ ≤ ‖a.val - β * x‖) (hθ : ‖a.val‖ ≤ c₀ * ‖a.val - β * x‖)
    (hκ : ρ * ‖α - γ * x / a.val‖ ≤ 1) :
    ‖(s.val - 1) * β * a.val * (α - γ * x / a.val) / ((a.val * s.val - β * x) * (a.val - β * x))‖ ≤ rad := by
  simp only [norm_div, norm_mul, hnorm]
  rw [div_le_iff₀ (mul_pos hD hD)]
  calc ‖s.val - 1‖ * ‖β‖ * ‖a.val‖ * ‖α - γ * x / a.val‖
      ≤ 1 * ‖β‖ * (c₀ * ‖a.val - β * x‖) * ‖α - γ * x / a.val‖ := by gcongr
    _ ≤ 1 * ‖β‖ * (rad * ρ * ‖x‖ * ‖a.val - β * x‖) * ‖α - γ * x / a.val‖ := by gcongr
    _ = rad * ‖a.val - β * x‖ * ((‖β‖ * ‖x‖) * (ρ * ‖α - γ * x / a.val‖)) := by ring
    _ ≤ rad * ‖a.val - β * x‖ * (‖a.val - β * x‖ * 1) := by gcongr
    _ = rad * (‖a.val - β * x‖ * ‖a.val - β * x‖) := by ring

private theorem exists_forall_cellSectionOf_indicator_dualCellPoint_scaleThird (hν0 : IsLocallyConstant (ν 0))
    (hν1 : IsLocallyConstant (ν 1)) {x : v.adicCompletion ℚ} (hx : x ≠ 0) {ρ rad δ : ℝ} (hρ : 0 < ρ) (hrad : 0 < rad)
    (hδ : 0 < δ) :
    ∃ c₀ : ℝ, 0 < c₀ ∧ ∀ Ψ : (Fin 3 → v.adicCompletion ℚ) → ℂ,
      (∀ p q : Fin 3 → v.adicCompletion ℚ, (∀ i, ‖q i - p i‖ ≤ rad) → Ψ q = Ψ p) →
      (∀ r : Fin 3 → v.adicCompletion ℚ, Ψ r ≠ 0 → ‖1 + x * (r 1 - r 2 * r 0)‖ ≤ δ → ρ ≤ ‖r 0‖) →
      ∀ κ : ℝ, κ ≤ ‖(NumberField.AdelicLevel.uniformizerUnit ℚ v).val‖ * c₀ →
      ∀ (α β γ : v.adicCompletion ℚ) (a s : (v.adicCompletion ℚ)ˣ),
        ‖(NumberField.AdelicLevel.uniformizerUnit ℚ v).val‖ ≤ ‖s.val‖ → ‖s.val‖ ≤ 1 →
        cellSectionOf v ν ({r : Fin 3 → v.adicCompletion ℚ | ‖1 + x * (r 1 - r 2 * r 0)‖ ≤ κ}.indicator Ψ)
            (dualCellPoint v α β (s.val * γ) (a * s) x) =
          ((ν 1 s : ℂ))⁻¹ *
            cellSectionOf v ν
              ({r : Fin 3 → v.adicCompletion ℚ | ‖1 + x * (r 1 - r 2 * r 0)‖ ≤ κ / ‖s.val‖}.indicator Ψ)
              (dualCellPoint v α β γ a x) := by
  obtain ⟨e0, he0, h0⟩ := exists_forall_charExt_one_sub_eq_one v (ν 0) hν0
  obtain ⟨e1, he1, h1⟩ := exists_forall_charExt_one_sub_eq_one v (ν 1) hν1
  have hx' : 0 < ‖x‖ := norm_pos_iff.mpr hx
  have hϖ : 0 < ‖(NumberField.AdelicLevel.uniformizerUnit ℚ v).val‖ := norm_pos_iff.mpr (Units.ne_zero _)
  refine ⟨min (min (min (1 / 2) (rad * ρ * ‖x‖)) (min e0 e1)) δ,
    lt_min (lt_min (lt_min one_half_pos (by positivity)) (lt_min he0 he1)) hδ, ?_⟩
  set c₀ : ℝ := min (min (min (1 / 2) (rad * ρ * ‖x‖)) (min e0 e1)) δ with hc₀def
  have hc₀ : 0 < c₀ := lt_min (lt_min (lt_min one_half_pos (by positivity)) (lt_min he0 he1)) hδ
  have hc₀half : c₀ ≤ 1 / 2 := (min_le_left _ _).trans ((min_le_left _ _).trans (min_le_left _ _))
  have hc₀rad : c₀ ≤ rad * ρ * ‖x‖ := (min_le_left _ _).trans ((min_le_left _ _).trans (min_le_right _ _))
  have hc₀e0 : c₀ ≤ e0 := (min_le_left _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have hc₀e1 : c₀ ≤ e1 := (min_le_left _ _).trans ((min_le_right _ _).trans (min_le_right _ _))
  have hc₀δ : c₀ ≤ δ := min_le_right _ _
  have hc₀lt : c₀ < 1 := hc₀half.trans_lt (by norm_num)
  intro Ψ hΨ hbox κ hκ α β γ a s hsϖ hs1
  have ha : a.val ≠ 0 := a.ne_zero
  have ha' : 0 < ‖a.val‖ := norm_pos_iff.mpr ha
  have hs : s.val ≠ 0 := s.ne_zero
  have hs' : 0 < ‖s.val‖ := norm_pos_iff.mpr hs
  have hs1' : ‖s.val - 1‖ ≤ 1 := by rw [norm_sub_rev]; exact norm_one_sub_le_one v hs1
  have hκs : κ ≤ ‖s.val‖ * c₀ := hκ.trans (mul_le_mul_of_nonneg_right hsϖ hc₀.le)
  have hu : ((ν 1 s : ℂ)) ≠ 0 := Units.ne_zero _

  have hsplit : a.val * s.val - β * x = (a.val - β * x) + a.val * (s.val - 1) := by ring
  have hasm : ‖a.val * (s.val - 1)‖ ≤ ‖a.val‖ := by
    rw [norm_mul]
    exact mul_le_of_le_one_right (norm_nonneg _) hs1'
  by_cases hcase : dualCellPoint v α β γ a x ∈ bigCell3 v ∧ ‖a.val / (a.val - β * x)‖ ≤ c₀
  ·
    obtain ⟨hmem, hθ⟩ := hcase
    have hlower : a.val - β * x ≠ 0 := lower_ne_zero_of_mem v α β γ x a hmem
    have hD : 0 < ‖a.val - β * x‖ := norm_pos_iff.mpr hlower
    have hθ' : ‖a.val‖ ≤ c₀ * ‖a.val - β * x‖ := by
      rw [norm_div, div_le_iff₀ hD] at hθ
      exact hθ
    have halt : ‖a.val * (s.val - 1)‖ < ‖a.val - β * x‖ :=
      hasm.trans_lt (hθ'.trans_lt (by nlinarith))
    have hnorm : ‖a.val * s.val - β * x‖ = ‖a.val - β * x‖ := by
      rw [hsplit, IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm halt.ne', max_eq_left halt.le]
    have hlower' : a.val * s.val - β * x ≠ 0 := by
      intro h
      rw [h, norm_zero] at hnorm
      exact hD.ne hnorm
    have hmem' : dualCellPoint v α β (s.val * γ) (a * s) x ∈ bigCell3 v := by
      refine ⟨?_, ?_⟩
      · rw [cornerEntry_dualCellPoint_scaleThird]
        exact hmem.1
      · rw [lowerMinor_dualCellPoint_scaleThird]
        exact div_ne_zero hlower' (mul_ne_zero ha hs)
    have hε : ‖a.val * (1 - s.val) / (a.val - β * x)‖ ≤ c₀ := by
      rw [norm_div, div_le_iff₀ hD, norm_mul]
      exact (mul_le_of_le_one_right (norm_nonneg _) (norm_one_sub_le_one v hs1)).trans hθ'
    have hval := cellValue_dualCellPoint_scaleThird v ν α β γ x a s hlower hlower' hnorm (h0 _ (hε.trans hc₀e0))
      (h1 _ (hε.trans hc₀e1))

    have hgauge := gauge_cellRatio_dualCellPoint v α β γ x a hmem
    have hgauge' := gauge_cellRatio_dualCellPoint v α β (s.val * γ) x (a * s) hmem'
    have hscale : ‖(a * s).val / ((a * s).val - β * x)‖ = ‖s.val‖ * ‖a.val / (a.val - β * x)‖ := by
      rw [Units.val_mul, norm_div, norm_mul, hnorm, norm_div]
      ring

    have hzero : cellRatio v (dualCellPoint v α β (s.val * γ) (a * s) x) 0 =
        cellRatio v (dualCellPoint v α β γ a x) 0 := by
      rw [cellRatio_dualCellPoint_scaleThird v α β γ x a s hlower hlower']
      simp only [Matrix.cons_val_zero]
    have hβ : ‖β‖ * ‖x‖ ≤ ‖a.val - β * x‖ := by
      rw [← norm_mul]
      calc ‖β * x‖ = ‖a.val + -(a.val - β * x)‖ := by congr 1; ring
        _ ≤ max ‖a.val‖ ‖-(a.val - β * x)‖ := IsUltrametricDist.norm_add_le_max _ _
        _ ≤ ‖a.val - β * x‖ :=
            max_le (hθ'.trans (mul_le_of_le_one_left hD.le hc₀lt.le)) (norm_neg _).le
    have hsame : Ψ (cellRatio v (dualCellPoint v α β (s.val * γ) (a * s) x)) =
        Ψ (cellRatio v (dualCellPoint v α β γ a x)) := by
      by_cases hr0 : ρ ≤ ‖cellRatio v (dualCellPoint v α β γ a x) 0‖
      · have hκρ : ρ * ‖α - γ * x / a.val‖ ≤ 1 := by
          rw [norm_cellRatio_zero_dualCellPoint] at hr0
          have hκpos : 0 < ‖α - γ * x / a.val‖ := by
            rw [norm_pos_iff]
            have h := hmem.1
            rwa [cornerEntry_dualCellPoint] at h
          have := mul_le_mul_of_nonneg_right hr0 hκpos.le
          rwa [inv_mul_cancel₀ hκpos.ne'] at this
        refine hΨ _ _ ?_
        rw [cellRatio_dualCellPoint_scaleThird v α β γ x a s hlower hlower']
        intro i
        fin_cases i <;> simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
          Matrix.tail_cons, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk]
        · rw [sub_self, norm_zero]
          exact hrad.le
        · rw [sub_self, norm_zero]
          exact hrad.le
        · rw [add_sub_cancel_left]
          exact norm_move_le v hρ hrad hc₀rad hD hnorm hs1' hβ hθ' hκρ
      · have hb : Ψ (cellRatio v (dualCellPoint v α β γ a x)) = 0 := by
          by_contra hne
          exact hr0 (hbox _ hne (by rw [hgauge]; exact hθ.trans hc₀δ))
        have hb' : Ψ (cellRatio v (dualCellPoint v α β (s.val * γ) (a * s) x)) = 0 := by
          by_contra hne
          refine hr0 ?_
          rw [← hzero]
          refine hbox _ hne ?_
          rw [hgauge', hscale]
          exact ((mul_le_of_le_one_left (norm_nonneg _) hs1).trans hθ).trans hc₀δ
        rw [hb, hb']

    have hcut : cellRatio v (dualCellPoint v α β (s.val * γ) (a * s) x) ∈
          {r : Fin 3 → v.adicCompletion ℚ | ‖1 + x * (r 1 - r 2 * r 0)‖ ≤ κ} ↔
        cellRatio v (dualCellPoint v α β γ a x) ∈
          {r : Fin 3 → v.adicCompletion ℚ | ‖1 + x * (r 1 - r 2 * r 0)‖ ≤ κ / ‖s.val‖} := by
      simp only [Set.mem_setOf_eq]
      rw [hgauge', hgauge, hscale, le_div_iff₀ hs', mul_comm]
    rw [cellSectionOf_apply_of_mem v ν _ hmem', cellSectionOf_apply_of_mem v ν _ hmem]
    by_cases hin : cellRatio v (dualCellPoint v α β γ a x) ∈
        {r : Fin 3 → v.adicCompletion ℚ | ‖1 + x * (r 1 - r 2 * r 0)‖ ≤ κ / ‖s.val‖}
    · rw [Set.indicator_of_mem (hcut.mpr hin), Set.indicator_of_mem hin, hsame, ← hval, mul_assoc,
        inv_mul_cancel_left₀ hu]
    · rw [Set.indicator_of_notMem (fun h => hin (hcut.mp h)), Set.indicator_of_notMem hin]
      simp only [mul_zero]
  ·
    have hright : cellSectionOf v ν
        ({r : Fin 3 → v.adicCompletion ℚ | ‖1 + x * (r 1 - r 2 * r 0)‖ ≤ κ / ‖s.val‖}.indicator Ψ)
          (dualCellPoint v α β γ a x) = 0 := by
      by_cases hmem : dualCellPoint v α β γ a x ∈ bigCell3 v
      · rw [cellSectionOf_apply_of_mem v ν _ hmem, Set.indicator_of_notMem, mul_zero]
        simp only [Set.mem_setOf_eq, not_le]
        rw [gauge_cellRatio_dualCellPoint v α β γ x a hmem]
        have hθ : c₀ < ‖a.val / (a.val - β * x)‖ := not_le.mp fun h => hcase ⟨hmem, h⟩
        calc κ / ‖s.val‖ ≤ c₀ := by rw [div_le_iff₀ hs']; linarith [hκs, mul_comm ‖s.val‖ c₀]
          _ < _ := hθ
      · rw [cellSectionOf_apply_of_notMem v ν _ hmem]
    rw [hright, mul_zero]
    by_cases hmem' : dualCellPoint v α β (s.val * γ) (a * s) x ∈ bigCell3 v
    · rw [cellSectionOf_apply_of_mem v ν _ hmem', Set.indicator_of_notMem, mul_zero]
      simp only [Set.mem_setOf_eq, not_le]
      rw [gauge_cellRatio_dualCellPoint v α β (s.val * γ) x (a * s) hmem', Units.val_mul, norm_div, norm_mul]
      have hlower' : a.val * s.val - β * x ≠ 0 := by
        have h := hmem'.2
        rw [lowerMinor_dualCellPoint_scaleThird] at h
        exact fun h0 => h (by rw [h0, zero_div])
      have hD' : 0 < ‖a.val * s.val - β * x‖ := norm_pos_iff.mpr hlower'
      rw [lt_div_iff₀ hD']

      have hH : c₀ * ‖a.val - β * x‖ < ‖a.val‖ := by
        by_cases hmem : dualCellPoint v α β γ a x ∈ bigCell3 v
        · have hθ : c₀ < ‖a.val / (a.val - β * x)‖ := not_le.mp fun h => hcase ⟨hmem, h⟩
          have hD : 0 < ‖a.val - β * x‖ := norm_pos_iff.mpr (lower_ne_zero_of_mem v α β γ x a hmem)
          rw [norm_div, lt_div_iff₀ hD] at hθ
          exact hθ
        · have hD0 : a.val - β * x = 0 := by
            by_contra hD0
            apply hmem
            refine ⟨?_, ?_⟩
            · rw [← cornerEntry_dualCellPoint_scaleThird v α β γ x a s]
              exact hmem'.1
            · rw [lowerMinor_dualCellPoint]
              intro h
              apply hD0
              rw [sub_eq_zero] at h ⊢
              field_simp at h
              linear_combination h
          rw [hD0, norm_zero, mul_zero]
          exact ha'
      have hmax : ‖a.val * s.val - β * x‖ ≤ max ‖a.val - β * x‖ ‖a.val‖ := by
        rw [hsplit]
        exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le_max le_rfl hasm)
      have hcmax : c₀ * max ‖a.val - β * x‖ ‖a.val‖ < ‖a.val‖ := by
        rcases le_total ‖a.val - β * x‖ ‖a.val‖ with h | h
        · rw [max_eq_right h]
          nlinarith
        · rw [max_eq_left h]
          exact hH
      have hκ0 : κ ≤ ‖(NumberField.AdelicLevel.uniformizerUnit ℚ v).val‖ * c₀ := hκ
      calc κ * ‖a.val * s.val - β * x‖
          ≤ (‖(NumberField.AdelicLevel.uniformizerUnit ℚ v).val‖ * c₀) * max ‖a.val - β * x‖ ‖a.val‖ := by
            rcases le_or_gt 0 κ with hκpos | hκneg
            · exact mul_le_mul hκ0 hmax (norm_nonneg _) (by positivity)
            · exact (mul_nonpos_of_nonpos_of_nonneg hκneg.le (norm_nonneg _)).trans (by positivity)
        _ = ‖(NumberField.AdelicLevel.uniformizerUnit ℚ v).val‖ * (c₀ * max ‖a.val - β * x‖ ‖a.val‖) := by ring
        _ < ‖(NumberField.AdelicLevel.uniformizerUnit ℚ v).val‖ * ‖a.val‖ := by gcongr
        _ ≤ ‖s.val‖ * ‖a.val‖ := by gcongr
        _ = ‖a.val‖ * ‖s.val‖ := mul_comm _ _
    · rw [cellSectionOf_apply_of_notMem v ν _ hmem']

end DualCovarianceThird
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_eventually_threefold_twistedDifference_dualJacquetValueFn_eq_zero.LaurentZetaSlot P2MW.S_LanglandsTunnell_CubicInduction_eventually_threefold_twistedDifference_dualJacquetValueFn_eq_zero.WeylTranslateZeta"

end WeylTranslateZeta
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_eventually_threefold_twistedDifference_dualJacquetValueFn_eq_zero.LaurentZetaSlot P2MW.S_LanglandsTunnell_CubicInduction_eventually_threefold_twistedDifference_dualJacquetValueFn_eq_zero.WeylTranslateZeta"
end
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_eventually_threefold_twistedDifference_dualJacquetValueFn_eq_zero.LaurentZetaSlot P2MW.S_LanglandsTunnell_CubicInduction_eventually_threefold_twistedDifference_dualJacquetValueFn_eq_zero.WeylTranslateZeta"

section

open IsDedekindDomain NumberField LanglandsTunnell.TateLocal

namespace WeylTranslateZeta
open LanglandsTunnell.CubicInduction

section SmallSubstitutions

variable (v : HeightOneSpectrum (𝓞 ℚ))

private theorem valued_le_exp_of_norm_le_one {n : ℤ} (hn : 0 ≤ n) {y : v.adicCompletion ℚ} (hy : ‖y‖ ≤ 1) :
    Valued.v y ≤ WithZero.exp n := by
  have hy' : ‖y‖ ≤ (Ideal.absNorm v.asIdeal : ℝ) ^ (0 : ℤ) := by rwa [zpow_zero]
  exact (valued_le_of_norm_le_zpow v hy').trans (WithZero.exp_le_exp.mpr hn)

private theorem valued_mul_le_of_valued_le_of_norm_le_one {c : ℤ} {y : v.adicCompletion ℚ}
    (hy : Valued.v y ≤ WithZero.exp c)
    {k : v.adicCompletion ℚ} (hk : ‖k‖ ≤ 1) : Valued.v (y * k) ≤ WithZero.exp c := by
  apply valued_le_of_norm_le_zpow v
  have hq : (0 : ℝ) ≤ (Ideal.absNorm v.asIdeal : ℝ) ^ c := zpow_nonneg (Nat.cast_nonneg _) c
  calc ‖y * k‖ = ‖y‖ * ‖k‖ := norm_mul y k
    _ ≤ (Ideal.absNorm v.asIdeal : ℝ) ^ c * 1 :=
        mul_le_mul (norm_le_zpow_of_valued_le v hy) hk (norm_nonneg k) hq
    _ = (Ideal.absNorm v.asIdeal : ℝ) ^ c := mul_one _

private theorem mem_unipotentBall3_iff_of_small {c : ℤ} (hc : 0 ≤ c)
    {p : v.adicCompletion ℚ × v.adicCompletion ℚ × v.adicCompletion ℚ}
    (hβ : ‖p.2.1‖ ≤ 1) (hγ : ‖p.2.2‖ ≤ max 1 ‖p.1‖) :
    p ∈ unipotentBall3 v c ↔ Valued.v p.1 ≤ WithZero.exp c := by
  simp only [unipotentBall3, Set.mem_setOf_eq]
  refine ⟨fun h => h.1, fun h1 => ⟨h1, valued_le_exp_of_norm_le_one v hc hβ, ?_⟩⟩
  have hq1 : (1 : ℝ) ≤ (Ideal.absNorm v.asIdeal : ℝ) ^ c := one_le_zpow₀ (one_lt_absNorm_real v).le hc
  have hγ' : ‖p.2.2‖ ≤ (Ideal.absNorm v.asIdeal : ℝ) ^ c :=
    hγ.trans (max_le hq1 (norm_le_zpow_of_valued_le v h1))
  exact (valued_le_of_norm_le_zpow v hγ').trans (WithZero.exp_le_exp.mpr (by omega))

private theorem mem_unipotentBall3_scale_third_iff {c : ℤ} (hc : 0 ≤ c) {s : v.adicCompletion ℚ} (hs : ‖s‖ ≤ 1)
    {α β γ : v.adicCompletion ℚ} (hγ : ‖γ‖ ≤ 1) :
    (α, β, s * γ) ∈ unipotentBall3 v c ↔ (α, β, γ) ∈ unipotentBall3 v c := by
  have h2c : (0 : ℤ) ≤ 2 * c := by omega
  have hsγ : ‖s * γ‖ ≤ 1 := by
    rw [norm_mul]
    simpa using mul_le_mul hs hγ (norm_nonneg γ) zero_le_one
  have h3 : Valued.v (s * γ) ≤ WithZero.exp (2 * c) := valued_le_exp_of_norm_le_one v h2c hsγ
  have h3' : Valued.v γ ≤ WithZero.exp (2 * c) := valued_le_exp_of_norm_le_one v h2c hγ
  simp only [unipotentBall3, Set.mem_setOf_eq, h3, h3', and_true]

private theorem mem_unipotentBall3_translate_iff {c : ℤ} (hc : 0 ≤ c) {k : v.adicCompletion ℚ} (hk : ‖k‖ ≤ 1)
    (α β γ : v.adicCompletion ℚ) :
    (α, β + k, γ + α * k) ∈ unipotentBall3 v c ↔ (α, β, γ) ∈ unipotentBall3 v c := by
  have hk' : Valued.v k ≤ WithZero.exp c := valued_le_exp_of_norm_le_one v hc hk
  have hk'' : Valued.v (-k) ≤ WithZero.exp c := by rwa [Valuation.map_neg]
  simp only [unipotentBall3, Set.mem_setOf_eq]
  constructor
  · rintro ⟨h1, h2, h3⟩
    have hαk : Valued.v (-(α * k)) ≤ WithZero.exp (2 * c) := by
      rw [Valuation.map_neg]
      exact (valued_mul_le_of_valued_le_of_norm_le_one v h1 hk).trans (WithZero.exp_le_exp.mpr (by omega))
    refine ⟨h1, ?_, ?_⟩
    · have hβ : β = (β + k) + -k := by ring
      rw [hβ]
      exact (Valuation.map_add _ _ _).trans (max_le h2 hk'')
    · have hγ : γ = (γ + α * k) + -(α * k) := by ring
      rw [hγ]
      exact (Valuation.map_add _ _ _).trans (max_le h3 hαk)
  · rintro ⟨h1, h2, h3⟩
    have hαk : Valued.v (α * k) ≤ WithZero.exp (2 * c) :=
      (valued_mul_le_of_valued_le_of_norm_le_one v h1 hk).trans (WithZero.exp_le_exp.mpr (by omega))
    exact ⟨h1, (Valuation.map_add _ _ _).trans (max_le h2 hk'),
      (Valuation.map_add _ _ _).trans (max_le h3 hαk)⟩

end SmallSubstitutions
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_eventually_threefold_twistedDifference_dualJacquetValueFn_eq_zero.LaurentZetaSlot P2MW.S_LanglandsTunnell_CubicInduction_eventually_threefold_twistedDifference_dualJacquetValueFn_eq_zero.WeylTranslateZeta"

section DualPointCoordinates

variable (v : HeightOneSpectrum (𝓞 ℚ))

private theorem norm_coords_le_of_gauge_lt {x : v.adicCompletion ℚ} (hx : x ≠ 0) (α β γ : v.adicCompletion ℚ)
    (a : (v.adicCompletion ℚ)ˣ) (hmem : dualCellPoint v α β γ a x ∈ bigCell3 v) {ρ R : ℝ} (hρ : 0 < ρ)
    (hR : ∀ i, ‖cellRatio v (dualCellPoint v α β γ a x) i‖ ≤ R)
    (hgauge : ρ < ‖1 + x * (cellRatio v (dualCellPoint v α β γ a x) 1 -
      cellRatio v (dualCellPoint v α β γ a x) 2 * cellRatio v (dualCellPoint v α β γ a x) 0)‖) :
    ‖β‖ ≤ ‖a.val‖ * max 1 ρ⁻¹ / ‖x‖ ∧ ‖γ‖ ≤ max (R * (‖a.val‖ / ρ)) (‖α‖ * ‖β‖) := by
  have ha : a.val ≠ 0 := a.ne_zero
  have hlow : a.val - β * x ≠ 0 := lower_ne_zero_of_mem v α β γ x a hmem
  have hlow_pos : 0 < ‖a.val - β * x‖ := norm_pos_iff.mpr hlow
  rw [gauge_cellRatio_dualCellPoint v α β γ x a hmem, norm_div] at hgauge
  have hlow_lt : ‖a.val - β * x‖ < ‖a.val‖ / ρ := by
    rw [lt_div_iff₀ hρ]
    rw [lt_div_iff₀ hlow_pos] at hgauge
    linarith [hgauge]
  constructor
  · rw [le_div_iff₀ (norm_pos_iff.mpr hx), ← norm_mul]
    have hβx : β * x = a.val + -(a.val - β * x) := by ring
    rw [hβx]
    refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ ?_)
    · exact le_mul_of_one_le_right (norm_nonneg _) (le_max_left 1 ρ⁻¹)
    · rw [norm_neg]
      refine hlow_lt.le.trans ?_
      rw [div_eq_mul_inv]
      exact mul_le_mul_of_nonneg_left (le_max_right 1 ρ⁻¹) (norm_nonneg _)
  · have h1 : (1 : v.adicCompletion ℚ) - β * x / a.val ≠ 0 := by
      rw [← div_self ha, ← sub_div]
      exact div_ne_zero hlow ha
    have hr2 : γ - α * β = cellRatio v (dualCellPoint v α β γ a x) 2 * (a.val - β * x) := by
      rw [cellRatio_dualCellPoint]
      simp only [Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons]
      field_simp
    have hR0 : 0 ≤ R := (norm_nonneg _).trans (hR 2)
    have hdiff : ‖γ - α * β‖ ≤ R * (‖a.val‖ / ρ) := by
      rw [hr2, norm_mul]
      exact mul_le_mul (hR 2) hlow_lt.le (norm_nonneg _) hR0
    have hγ : γ = (γ - α * β) + α * β := by ring
    rw [hγ]
    refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ ?_)
    · exact hdiff.trans (le_max_left _ _)
    · rw [norm_mul]
      exact le_max_right _ _

private theorem norm_third_le_of_le_norm_cellRatio_zero (α β γ : v.adicCompletion ℚ) (a : (v.adicCompletion ℚ)ˣ)
    (x : v.adicCompletion ℚ) {ρ R : ℝ} (hρ : 0 < ρ) (hr0 : ρ ≤ ‖cellRatio v (dualCellPoint v α β γ a x) 0‖)
    (hr1 : ‖cellRatio v (dualCellPoint v α β γ a x) 1‖ ≤ R) : ‖γ‖ ≤ ‖a.val‖ * R / ρ := by
  have ha : a.val ≠ 0 := a.ne_zero
  have hkey : γ * cellRatio v (dualCellPoint v α β γ a x) 0 = a.val * cellRatio v (dualCellPoint v α β γ a x) 1 := by
    rw [cellRatio_dualCellPoint]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
    rw [mul_one_div, mul_div_assoc', mul_comm a.val (γ * a.val⁻¹), inv_mul_cancel_right₀ ha]
  have hnorm : ‖γ‖ * ‖cellRatio v (dualCellPoint v α β γ a x) 0‖ ≤ ‖a.val‖ * R := by
    rw [← norm_mul, hkey, norm_mul]
    exact mul_le_mul_of_nonneg_left hr1 (norm_nonneg _)
  rw [le_div_iff₀ hρ]
  calc ‖γ‖ * ρ ≤ ‖γ‖ * ‖cellRatio v (dualCellPoint v α β γ a x) 0‖ := mul_le_mul_of_nonneg_left hr0 (norm_nonneg γ)
    _ ≤ ‖a.val‖ * R := hnorm

private theorem norm_coords_le_of_mem_zero (α β γ : v.adicCompletion ℚ) (a : (v.adicCompletion ℚ)ˣ)
    (hmem : dualCellPoint v α β γ a 0 ∈ bigCell3 v) {R : ℝ}
    (hR : ∀ i, ‖cellRatio v (dualCellPoint v α β γ a 0) i‖ ≤ R) :
    ‖γ‖ ≤ ‖a.val‖ * R * ‖α‖ ∧ ‖β‖ ≤ ‖a.val‖ * (R * max 1 R) := by
  have ha : a.val ≠ 0 := a.ne_zero
  have hα : α ≠ 0 := by
    have h := hmem.1
    rw [cornerEntry_dualCellPoint] at h
    simpa using h
  have hR0 : 0 ≤ R := (norm_nonneg _).trans (hR 0)
  have e0 : ‖α‖⁻¹ ≤ R := by
    have h := hR 0
    rw [cellRatio_dualCellPoint] at h
    simpa using h
  have e1 : γ = cellRatio v (dualCellPoint v α β γ a 0) 1 * a.val * α := by
    rw [cellRatio_dualCellPoint]
    simp only [Matrix.cons_val_one, Matrix.cons_val_zero, mul_zero, zero_div, sub_zero]
    rw [div_mul_eq_mul_div, inv_mul_cancel_right₀ ha, div_mul_eq_mul_div, mul_div_assoc, div_self hα, mul_one]
  have e2 : α * β = γ - a.val * cellRatio v (dualCellPoint v α β γ a 0) 2 := by
    rw [cellRatio_dualCellPoint]
    simp only [Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons, mul_zero, zero_div, sub_zero, div_one]
    rw [mul_div_assoc', mul_comm a.val (γ - α * β), mul_div_assoc, div_self ha, mul_one, sub_sub_cancel]
  have hγ : ‖γ‖ ≤ ‖a.val‖ * R * ‖α‖ := by
    calc ‖γ‖ = ‖cellRatio v (dualCellPoint v α β γ a 0) 1 * a.val * α‖ := by rw [← e1]
      _ = ‖cellRatio v (dualCellPoint v α β γ a 0) 1‖ * ‖a.val‖ * ‖α‖ := by rw [norm_mul, norm_mul]
      _ ≤ R * ‖a.val‖ * ‖α‖ :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (hR 1) (norm_nonneg _)) (norm_nonneg _)
      _ = ‖a.val‖ * R * ‖α‖ := by ring
  refine ⟨hγ, ?_⟩
  have haR : 0 ≤ ‖a.val‖ * R := mul_nonneg (norm_nonneg _) hR0
  have hαβ : ‖α * β‖ ≤ ‖a.val‖ * R * max 1 ‖α‖ := by
    rw [e2, sub_eq_add_neg]
    refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ ?_)
    · exact hγ.trans (mul_le_mul_of_nonneg_left (le_max_right 1 ‖α‖) haR)
    · rw [norm_neg, norm_mul]
      calc ‖a.val‖ * ‖cellRatio v (dualCellPoint v α β γ a 0) 2‖ ≤ ‖a.val‖ * R :=
            mul_le_mul_of_nonneg_left (hR 2) (norm_nonneg _)
        _ = ‖a.val‖ * R * 1 := (mul_one _).symm
        _ ≤ ‖a.val‖ * R * max 1 ‖α‖ := mul_le_mul_of_nonneg_left (le_max_left 1 ‖α‖) haR
  have hαn : ‖α‖ ≠ 0 := norm_ne_zero_iff.mpr hα
  have hαpos : 0 < ‖α‖ := norm_pos_iff.mpr hα
  rcases le_or_gt 1 ‖α‖ with h1 | h1
  · rw [max_eq_right h1, norm_mul] at hαβ
    have hβ : ‖β‖ ≤ ‖a.val‖ * R := by
      refine le_of_mul_le_mul_left ?_ hαpos
      calc ‖α‖ * ‖β‖ ≤ ‖a.val‖ * R * ‖α‖ := hαβ
        _ = ‖α‖ * (‖a.val‖ * R) := by ring
    calc ‖β‖ ≤ ‖a.val‖ * R := hβ
      _ = ‖a.val‖ * (R * 1) := by ring
      _ ≤ ‖a.val‖ * (R * max 1 R) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (le_max_left 1 R) hR0) (norm_nonneg _)
  · rw [max_eq_left h1.le, mul_one] at hαβ
    calc ‖β‖ = ‖α * β‖ * ‖α‖⁻¹ := by
          rw [norm_mul, mul_comm ‖α‖ ‖β‖, mul_assoc, mul_inv_cancel₀ hαn, mul_one]
      _ ≤ ‖a.val‖ * R * R := mul_le_mul hαβ e0 (inv_nonneg.mpr (norm_nonneg _)) haR
      _ = ‖a.val‖ * (R * R) := by ring
      _ ≤ ‖a.val‖ * (R * max 1 R) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (le_max_right 1 R) hR0) (norm_nonneg _)

end DualPointCoordinates
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_eventually_threefold_twistedDifference_dualJacquetValueFn_eq_zero.LaurentZetaSlot P2MW.S_LanglandsTunnell_CubicInduction_eventually_threefold_twistedDifference_dualJacquetValueFn_eq_zero.WeylTranslateZeta"

end WeylTranslateZeta
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_eventually_threefold_twistedDifference_dualJacquetValueFn_eq_zero.LaurentZetaSlot P2MW.S_LanglandsTunnell_CubicInduction_eventually_threefold_twistedDifference_dualJacquetValueFn_eq_zero.WeylTranslateZeta"
end
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_eventually_threefold_twistedDifference_dualJacquetValueFn_eq_zero.LaurentZetaSlot P2MW.S_LanglandsTunnell_CubicInduction_eventually_threefold_twistedDifference_dualJacquetValueFn_eq_zero.WeylTranslateZeta"

section

open MeasureTheory
open IsDedekindDomain
open NumberField
open LanglandsTunnell.TateLocal
open NumberField.StandardAddChar

attribute [local instance] LanglandsTunnell.TateLocal.localBorel

namespace WeylTranslateZeta
open LanglandsTunnell.CubicInduction

section DualSliceCovariances

variable (v : HeightOneSpectrum (𝓞 ℚ)) (ν : Fin 3 → ((v.adicCompletion ℚ)ˣ →* ℂˣ))

private noncomputable def dualIntegrand (Ψ : (Fin 3 → v.adicCompletion ℚ) → ℂ) (a : (v.adicCompletion ℚ)ˣ)
    (x : v.adicCompletion ℚ) (p : v.adicCompletion ℚ × v.adicCompletion ℚ × v.adicCompletion ℚ) : ℂ :=
  psiLocal ℚ v (-(p.1 + p.2.1)) * cellSectionOf v ν Ψ (dualCellPoint v p.1 p.2.1 p.2.2 a x)

private theorem jacquetTruncated3_dualTranslate_eq_integral_indicator (Ψ : (Fin 3 → v.adicCompletion ℚ) → ℂ)
    (c : ℤ) (a : (v.adicCompletion ℚ)ˣ) (x : v.adicCompletion ℚ) :
    jacquetTruncated3 v c (dualTranslate v ν Ψ a x) =
      ∫ p, (unipotentBall3 v c).indicator (dualIntegrand v ν Ψ a x) p ∂(jacquetHaar3 v) := by
  rw [jacquetTruncated3_dualTranslate, integral_indicator (measurableSet_unipotentBall3 v c)]
  rfl

private theorem exists_forall_integrable_indicator_dualIntegrand (hν : ∀ i, IsLocallyConstant (ν i))
    {Ψ : (Fin 3 → v.adicCompletion ℚ) → ℂ} (hΨl : IsLocallyConstant Ψ) (hΨc : HasCompactSupport Ψ)
    (a : (v.adicCompletion ℚ)ˣ) (x : v.adicCompletion ℚ) :
    ∃ c₀ : ℕ, ∀ c : ℤ, (c₀ : ℤ) ≤ c →
      Integrable ((unipotentBall3 v c).indicator (dualIntegrand v ν Ψ a x)) (jacquetHaar3 v) := by
  obtain ⟨c₀, h⟩ := exists_forall_le_integrableOn_and_jacquetTruncated3_eq_of_cellSectionOf v ν hν Ψ ⟨hΨl, hΨc⟩
    (dualPoint v a x)
  exact ⟨c₀, fun c hc => (integrable_indicator_iff (measurableSet_unipotentBall3 v c)).mpr (h c hc).1⟩

private theorem coe_inv_apply (i : Fin 3) (s : (v.adicCompletion ℚ)ˣ) :
    (((ν i)⁻¹ s : ℂˣ) : ℂ) = ((ν i s : ℂ))⁻¹ := by
  rw [MonoidHom.inv_apply, Units.val_inv_eq_inv_val]

private theorem indicator_dualIntegrand_scaleCoords {x : v.adicCompletion ℚ} (hx : x ≠ 0)
    (Ψ : (Fin 3 → v.adicCompletion ℚ) → ℂ) {ρ R : ℝ} (hρ : 0 < ρ)
    (hR : ∀ r : Fin 3 → v.adicCompletion ℚ, Ψ r ≠ 0 → ∀ i, ‖r i‖ ≤ R)
    (hsupp : ∀ r : Fin 3 → v.adicCompletion ℚ, Ψ r ≠ 0 → ρ < ‖bulkGauge v x r‖) {c : ℤ} (hc : 0 ≤ c)
    {a s : (v.adicCompletion ℚ)ˣ} (hs1 : ‖s.val‖ ≤ 1) (ha1 : ‖a.val‖ * max 1 ρ⁻¹ ≤ ‖x‖)
    (ha2 : R * (‖a.val‖ / ρ) ≤ 1) (p : v.adicCompletion ℚ × v.adicCompletion ℚ × v.adicCompletion ℚ) :
    (unipotentBall3 v c).indicator (dualIntegrand v ν Ψ (a * s) x) (p.1, s.val * p.2.1, s.val * p.2.2) =
      ((ν 0 s : ℂ))⁻¹ * ((‖s.val‖ : ℝ) : ℂ)⁻¹ * (unipotentBall3 v c).indicator (dualIntegrand v ν Ψ a x) p := by
  obtain ⟨α, β, γ⟩ := p
  dsimp only
  have hsec := cellSectionOf_dualCellPoint_scaleCoords v ν Ψ α β γ x a s
  by_cases h0 : cellSectionOf v ν Ψ (dualCellPoint v α β γ a x) = 0
  · have h1 : dualIntegrand v ν Ψ (a * s) x (α, s.val * β, s.val * γ) = 0 := by
      simp only [dualIntegrand, hsec, h0, mul_zero]
    have h2 : dualIntegrand v ν Ψ a x (α, β, γ) = 0 := by
      simp only [dualIntegrand, h0, mul_zero]
    rw [Set.indicator_apply_eq_zero.mpr fun _ => h1, Set.indicator_apply_eq_zero.mpr fun _ => h2, mul_zero]
  · have hmem : dualCellPoint v α β γ a x ∈ bigCell3 v := by
      by_contra hn
      exact h0 (cellSectionOf_apply_of_notMem v ν Ψ hn)
    have hΨ : Ψ (cellRatio v (dualCellPoint v α β γ a x)) ≠ 0 := by
      intro hz
      apply h0
      simp [cellSectionOf_apply_of_mem v ν Ψ hmem, hz]
    have hgauge : ρ < ‖1 + x * (cellRatio v (dualCellPoint v α β γ a x) 1 -
        cellRatio v (dualCellPoint v α β γ a x) 2 * cellRatio v (dualCellPoint v α β γ a x) 0)‖ := by
      have h := hsupp _ hΨ
      rwa [bulkGauge_def] at h
    obtain ⟨hβ, hγ⟩ := norm_coords_le_of_gauge_lt v hx α β γ a hmem hρ (hR _ hΨ) hgauge
    have hxpos : 0 < ‖x‖ := norm_pos_iff.mpr hx
    have hβ1 : ‖β‖ ≤ 1 := by
      calc ‖β‖ ≤ ‖a.val‖ * max 1 ρ⁻¹ / ‖x‖ := hβ
        _ ≤ ‖x‖ / ‖x‖ := by gcongr
        _ = 1 := div_self hxpos.ne'
    have hγ1 : ‖γ‖ ≤ max 1 ‖α‖ :=
      hγ.trans (max_le_max ha2 (mul_le_of_le_one_right (norm_nonneg _) hβ1))
    have hm : (α, β, γ) ∈ unipotentBall3 v c ↔ Valued.v α ≤ WithZero.exp c :=
      mem_unipotentBall3_iff_of_small v hc hβ1 hγ1
    have hsβ : ‖s.val * β‖ ≤ 1 := by
      rw [norm_mul]
      exact mul_le_one₀ hs1 (norm_nonneg _) hβ1
    have hsγ : ‖s.val * γ‖ ≤ max 1 ‖α‖ := by
      rw [norm_mul]
      exact (mul_le_of_le_one_left (norm_nonneg _) hs1).trans hγ1
    have hm' : (α, s.val * β, s.val * γ) ∈ unipotentBall3 v c ↔ Valued.v α ≤ WithZero.exp c :=
      mem_unipotentBall3_iff_of_small v hc hsβ hsγ
    by_cases hα : Valued.v α ≤ WithZero.exp c
    · rw [Set.indicator_of_mem (hm'.mpr hα), Set.indicator_of_mem (hm.mpr hα)]
      simp only [dualIntegrand]
      rw [hsec]
      have hψ : psiLocal ℚ v (-(α + s.val * β)) = psiLocal ℚ v (-(α + β)) := by
        have e : -(α + s.val * β) = -(α + β) + (1 - s.val) * β := by ring
        have h1 : ‖(1 - s.val) * β‖ ≤ 1 := by
          rw [norm_mul]
          exact mul_le_one₀ (norm_one_sub_le_one v hs1) (norm_nonneg _) hβ1
        rw [e, AddChar.map_add_eq_mul, psiLocal_eq_one_of_norm_le_one v h1, mul_one]
      rw [hψ]
      ring
    · rw [Set.indicator_of_notMem fun h => hα (hm'.mp h), Set.indicator_of_notMem fun h => hα (hm.mp h),
        mul_zero]

private theorem exists_forall_jacquetValue_dualTranslate_mul_eq_of_gauge (hν : ∀ i, IsLocallyConstant (ν i))
    {x : v.adicCompletion ℚ} (hx : x ≠ 0) (Ψ : (Fin 3 → v.adicCompletion ℚ) → ℂ) (hΨl : IsLocallyConstant Ψ)
    (hΨc : HasCompactSupport Ψ) {ρ : ℝ} (hρ : 0 < ρ)
    (hsupp : ∀ r : Fin 3 → v.adicCompletion ℚ, Ψ r ≠ 0 → ρ < ‖bulkGauge v x r‖) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ a s : (v.adicCompletion ℚ)ˣ, ‖s.val‖ ≤ 1 → ‖a.val‖ ≤ ε →
      jacquetValue v (dualTranslate v ν Ψ (a * s) x) =
        ((ν 0 s : ℂ))⁻¹ * ((‖s.val‖ : ℝ) : ℂ) * jacquetValue v (dualTranslate v ν Ψ a x) := by
  obtain ⟨R, hR⟩ := exists_support_radius v Ψ hΨc
  have hxpos : 0 < ‖x‖ := norm_pos_iff.mpr hx
  have hM : 0 < max 1 ρ⁻¹ := lt_max_of_lt_left one_pos
  have hR' : 0 < max R 1 := lt_max_of_lt_right one_pos
  refine ⟨min (‖x‖ / max 1 ρ⁻¹) (ρ / max R 1), lt_min (div_pos hxpos hM) (div_pos hρ hR'), fun a s hs1 ha => ?_⟩
  have ha1 : ‖a.val‖ * max 1 ρ⁻¹ ≤ ‖x‖ := by
    have h := ha.trans (min_le_left _ _)
    rwa [le_div_iff₀ hM] at h
  have ha2 : R * (‖a.val‖ / ρ) ≤ 1 := by
    have h : ‖a.val‖ ≤ ρ / max R 1 := ha.trans (min_le_right _ _)
    have hRne : max R 1 ≠ 0 := hR'.ne'
    have hρne : ρ ≠ 0 := hρ.ne'
    calc R * (‖a.val‖ / ρ) ≤ max R 1 * (‖a.val‖ / ρ) := by
          gcongr
          exact le_max_left _ _
      _ ≤ max R 1 * (ρ / max R 1 / ρ) := by gcongr
      _ = 1 := by field_simp
  refine jacquetValue_eq_mul_of v (exists_level_dualTranslate v ν Ψ hν hΨl hΨc (a * s) x)
    (exists_level_dualTranslate v ν Ψ hν hΨl hΨc a x) ⟨0, fun c hc => ?_⟩
  have hc' : (0 : ℤ) ≤ c := by exact_mod_cast hc
  have hsne : ((‖s.val‖ : ℝ) : ℂ) ≠ 0 := by exact_mod_cast norm_ne_zero_iff.mpr s.ne_zero
  rw [jacquetTruncated3_dualTranslate_eq_integral_indicator, jacquetTruncated3_dualTranslate_eq_integral_indicator,
    integral_jacquetHaar3_comp_scale_snd v s.val s.ne_zero
      ((unipotentBall3 v c).indicator (dualIntegrand v ν Ψ (a * s) x))]
  have hpt : (fun p : v.adicCompletion ℚ × v.adicCompletion ℚ × v.adicCompletion ℚ =>
      (unipotentBall3 v c).indicator (dualIntegrand v ν Ψ (a * s) x) (p.1, s.val * p.2.1, s.val * p.2.2)) =
      fun p => ((ν 0 s : ℂ))⁻¹ * ((‖s.val‖ : ℝ) : ℂ)⁻¹ * (unipotentBall3 v c).indicator (dualIntegrand v ν Ψ a x) p :=
    funext fun p => indicator_dualIntegrand_scaleCoords v ν hx Ψ hρ hR hsupp hc' hs1 ha1 ha2 p
  rw [hpt, integral_const_mul]
  set J := ∫ p, (unipotentBall3 v c).indicator (dualIntegrand v ν Ψ a x) p ∂(jacquetHaar3 v)
  push_cast
  linear_combination (((ν 0 s : ℂ))⁻¹ * ((‖s.val‖ : ℝ) : ℂ) * J) * mul_inv_cancel₀ hsne

private theorem isClopen_setOf_norm_curve_le (x : v.adicCompletion ℚ) {κ : ℝ} (hκ : 0 < κ) :
    IsClopen {r : Fin 3 → v.adicCompletion ℚ | ‖1 + x * (r 1 - r 2 * r 0)‖ ≤ κ} := by
  have h : {r : Fin 3 → v.adicCompletion ℚ | ‖1 + x * (r 1 - r 2 * r 0)‖ ≤ κ} =
      {r : Fin 3 → v.adicCompletion ℚ | κ < ‖bulkGauge v x r‖}ᶜ := by
    ext r
    simp [bulkGauge_def]
  rw [h]
  exact (isClopen_setOf_lt_norm_bulkGauge v x hκ).compl

private theorem indicator_dualIntegrand_scaleThird {x : v.adicCompletion ℚ} {δ : ℝ} (hδ : 0 < δ)
    (Ψ : (Fin 3 → v.adicCompletion ℚ) → ℂ)
    (hvan : ∀ r : Fin 3 → v.adicCompletion ℚ, Ψ r ≠ 0 → ‖1 + x * (r 1 - r 2 * r 0)‖ ≤ δ → δ ≤ ‖r 0‖)
    {R : ℝ} (hR : ∀ r : Fin 3 → v.adicCompletion ℚ, Ψ r ≠ 0 → ∀ i, ‖r i‖ ≤ R) {c₀ : ℝ}
    (hc₀id : ∀ κ : ℝ, κ ≤ ‖(NumberField.AdelicLevel.uniformizerUnit ℚ v).val‖ * c₀ →
      ∀ (α β γ : v.adicCompletion ℚ) (a s : (v.adicCompletion ℚ)ˣ),
        ‖(NumberField.AdelicLevel.uniformizerUnit ℚ v).val‖ ≤ ‖s.val‖ → ‖s.val‖ ≤ 1 →
        cellSectionOf v ν ({r : Fin 3 → v.adicCompletion ℚ | ‖1 + x * (r 1 - r 2 * r 0)‖ ≤ κ}.indicator Ψ)
            (dualCellPoint v α β (s.val * γ) (a * s) x) =
          ((ν 1 s : ℂ))⁻¹ *
            cellSectionOf v ν
              ({r : Fin 3 → v.adicCompletion ℚ | ‖1 + x * (r 1 - r 2 * r 0)‖ ≤ κ / ‖s.val‖}.indicator Ψ)
              (dualCellPoint v α β γ a x))
    {κ : ℝ} (hκ : κ ≤ ‖(NumberField.AdelicLevel.uniformizerUnit ℚ v).val‖ * c₀) {c : ℤ} (hc : 0 ≤ c)
    {a s : (v.adicCompletion ℚ)ˣ} (hs0 : ‖(NumberField.AdelicLevel.uniformizerUnit ℚ v).val‖ ≤ ‖s.val‖)
    (hs1 : ‖s.val‖ ≤ 1) (hκs : κ / ‖s.val‖ ≤ δ) (ha : ‖a.val‖ * R ≤ δ)
    (p : v.adicCompletion ℚ × v.adicCompletion ℚ × v.adicCompletion ℚ) :
    (unipotentBall3 v c).indicator
        (dualIntegrand v ν ({r : Fin 3 → v.adicCompletion ℚ | ‖1 + x * (r 1 - r 2 * r 0)‖ ≤ κ}.indicator Ψ)
          (a * s) x) (p.1, p.2.1, s.val * p.2.2) =
      ((ν 1 s : ℂ))⁻¹ * (unipotentBall3 v c).indicator
        (dualIntegrand v ν
          ({r : Fin 3 → v.adicCompletion ℚ | ‖1 + x * (r 1 - r 2 * r 0)‖ ≤ κ / ‖s.val‖}.indicator Ψ) a x) p := by
  obtain ⟨α, β, γ⟩ := p
  dsimp only
  have hsec := hc₀id κ hκ α β γ a s hs0 hs1
  set Ψ₄ : (Fin 3 → v.adicCompletion ℚ) → ℂ :=
    {r : Fin 3 → v.adicCompletion ℚ | ‖1 + x * (r 1 - r 2 * r 0)‖ ≤ κ / ‖s.val‖}.indicator Ψ with hΨ₄
  by_cases h0 : cellSectionOf v ν Ψ₄ (dualCellPoint v α β γ a x) = 0
  · have h1 : dualIntegrand v ν ({r : Fin 3 → v.adicCompletion ℚ | ‖1 + x * (r 1 - r 2 * r 0)‖ ≤ κ}.indicator Ψ)
        (a * s) x (α, β, s.val * γ) = 0 := by
      simp only [dualIntegrand, hsec, h0, mul_zero]
    have h2 : dualIntegrand v ν Ψ₄ a x (α, β, γ) = 0 := by
      simp only [dualIntegrand, h0, mul_zero]
    rw [Set.indicator_apply_eq_zero.mpr fun _ => h1, Set.indicator_apply_eq_zero.mpr fun _ => h2, mul_zero]
  · have hmem : dualCellPoint v α β γ a x ∈ bigCell3 v := by
      by_contra hn
      exact h0 (cellSectionOf_apply_of_notMem v ν Ψ₄ hn)
    have hΨ₄r : Ψ₄ (cellRatio v (dualCellPoint v α β γ a x)) ≠ 0 := by
      intro hz
      apply h0
      simp [cellSectionOf_apply_of_mem v ν Ψ₄ hmem, hz]
    have hin : ‖1 + x * (cellRatio v (dualCellPoint v α β γ a x) 1 -
        cellRatio v (dualCellPoint v α β γ a x) 2 * cellRatio v (dualCellPoint v α β γ a x) 0)‖ ≤ κ / ‖s.val‖ :=
      by
        have h := hΨ₄r
        rw [hΨ₄] at h
        have hm := Set.mem_of_indicator_ne_zero h
        exact hm
    have hΨr : Ψ (cellRatio v (dualCellPoint v α β γ a x)) ≠ 0 := fun hz =>
      hΨ₄r (Set.indicator_apply_eq_zero.mpr fun _ => hz)
    have hr0 : δ ≤ ‖cellRatio v (dualCellPoint v α β γ a x) 0‖ := hvan _ hΨr (hin.trans hκs)
    have hγ : ‖γ‖ ≤ ‖a.val‖ * R / δ :=
      norm_third_le_of_le_norm_cellRatio_zero v α β γ a x hδ hr0 (hR _ hΨr 1)
    have hγ1 : ‖γ‖ ≤ 1 := hγ.trans ((div_le_one₀ hδ).mpr ha)
    have hm : (α, β, s.val * γ) ∈ unipotentBall3 v c ↔ (α, β, γ) ∈ unipotentBall3 v c :=
      mem_unipotentBall3_scale_third_iff v hc hs1 hγ1
    by_cases hαβ : (α, β, γ) ∈ unipotentBall3 v c
    · rw [Set.indicator_of_mem (hm.mpr hαβ), Set.indicator_of_mem hαβ]
      simp only [dualIntegrand]
      rw [hsec]
      ring
    · rw [Set.indicator_of_notMem fun h => hαβ (hm.mp h), Set.indicator_of_notMem hαβ, mul_zero]

private theorem exists_forall_jacquetValue_dualTranslate_mul_eq_near (hν : ∀ i, IsLocallyConstant (ν i))
    {x : v.adicCompletion ℚ} (hx : x ≠ 0) (Ψ : (Fin 3 → v.adicCompletion ℚ) → ℂ) (hΨl : IsLocallyConstant Ψ)
    (hΨc : HasCompactSupport Ψ) {δ : ℝ} (hδ : 0 < δ)
    (hvan : ∀ r : Fin 3 → v.adicCompletion ℚ, Ψ r ≠ 0 → ‖1 + x * (r 1 - r 2 * r 0)‖ ≤ δ → δ ≤ ‖r 0‖) :
    ∃ κ : ℝ, 0 < κ ∧ ∃ ε : ℝ, 0 < ε ∧ ∀ a s : (v.adicCompletion ℚ)ˣ,
      ‖(NumberField.AdelicLevel.uniformizerUnit ℚ v).val‖ ≤ ‖s.val‖ → ‖s.val‖ ≤ 1 → ‖a.val‖ ≤ ε →
      jacquetValue v (dualTranslate v ν
          ({r : Fin 3 → v.adicCompletion ℚ | ‖1 + x * (r 1 - r 2 * r 0)‖ ≤ κ}.indicator Ψ) (a * s) x) =
        ((ν 1 s : ℂ))⁻¹ * ((‖s.val‖ : ℝ) : ℂ) * jacquetValue v (dualTranslate v ν
          ({r : Fin 3 → v.adicCompletion ℚ | ‖1 + x * (r 1 - r 2 * r 0)‖ ≤ κ / ‖s.val‖}.indicator Ψ) a x) := by
  obtain ⟨rad, hrad, hinv⟩ := exists_invariance_radius v Ψ hΨl hΨc
  obtain ⟨R, hR⟩ := exists_support_radius v Ψ hΨc
  obtain ⟨c₀, hc₀, hc₀id⟩ := exists_forall_cellSectionOf_indicator_dualCellPoint_scaleThird v ν (hν 0) (hν 1) hx
    hδ hrad hδ
  have hϖ : 0 < ‖(NumberField.AdelicLevel.uniformizerUnit ℚ v).val‖ := norm_varpi_pos v
  have hR' : 0 < max R 1 := lt_max_of_lt_right one_pos
  set κ : ℝ := ‖(NumberField.AdelicLevel.uniformizerUnit ℚ v).val‖ * min c₀ δ
  have hκpos : 0 < κ := mul_pos hϖ (lt_min hc₀ hδ)
  have hκ : κ ≤ ‖(NumberField.AdelicLevel.uniformizerUnit ℚ v).val‖ * c₀ :=
    mul_le_mul_of_nonneg_left (min_le_left _ _) (norm_nonneg _)
  refine ⟨κ, hκpos, δ / max R 1, div_pos hδ hR', fun a s hs0 hs1 ha => ?_⟩
  have hspos : 0 < ‖s.val‖ := hϖ.trans_le hs0
  have hκs : κ / ‖s.val‖ ≤ δ := by
    rw [div_le_iff₀ hspos]
    calc κ ≤ ‖(NumberField.AdelicLevel.uniformizerUnit ℚ v).val‖ * δ :=
          mul_le_mul_of_nonneg_left (min_le_right _ _) (norm_nonneg _)
      _ ≤ ‖s.val‖ * δ := mul_le_mul_of_nonneg_right hs0 hδ.le
      _ = δ * ‖s.val‖ := mul_comm _ _
  have haR : ‖a.val‖ * R ≤ δ := by
    calc ‖a.val‖ * R ≤ ‖a.val‖ * max R 1 := mul_le_mul_of_nonneg_left (le_max_left _ _) (norm_nonneg _)
      _ ≤ δ / max R 1 * max R 1 := mul_le_mul_of_nonneg_right ha hR'.le
      _ = δ := div_mul_cancel₀ δ hR'.ne'
  refine jacquetValue_eq_mul_of v
    (exists_level_dualTranslate v ν _ hν (isLocallyConstant_indicator_of_isClopen_T v (isClopen_setOf_norm_curve_le v x
      hκpos) hΨl) (hasCompactSupport_indicator_T v _ hΨc) (a * s) x)
    (exists_level_dualTranslate v ν _ hν (isLocallyConstant_indicator_of_isClopen_T v (isClopen_setOf_norm_curve_le v x
      (div_pos hκpos hspos)) hΨl) (hasCompactSupport_indicator_T v _ hΨc) a x) ⟨0, fun c hc => ?_⟩
  have hc' : (0 : ℤ) ≤ c := by exact_mod_cast hc
  rw [jacquetTruncated3_dualTranslate_eq_integral_indicator, jacquetTruncated3_dualTranslate_eq_integral_indicator,
    integral_jacquetHaar3_comp_scale_third v s.val s.ne_zero _]
  have hpt : (fun p : v.adicCompletion ℚ × v.adicCompletion ℚ × v.adicCompletion ℚ =>
      (unipotentBall3 v c).indicator
        (dualIntegrand v ν ({r : Fin 3 → v.adicCompletion ℚ | ‖1 + x * (r 1 - r 2 * r 0)‖ ≤ κ}.indicator Ψ)
          (a * s) x) (p.1, p.2.1, s.val * p.2.2)) =
      fun p => ((ν 1 s : ℂ))⁻¹ * (unipotentBall3 v c).indicator
        (dualIntegrand v ν
          ({r : Fin 3 → v.adicCompletion ℚ | ‖1 + x * (r 1 - r 2 * r 0)‖ ≤ κ / ‖s.val‖}.indicator Ψ) a x) p :=
    funext fun p => indicator_dualIntegrand_scaleThird v ν hδ Ψ hvan hR (hc₀id Ψ hinv hvan) hκ hc' hs0 hs1 hκs haR p
  rw [hpt, integral_const_mul]
  ring

private theorem indicator_dualIntegrand_translateCoords {x : v.adicCompletion ℚ} (hx : x ≠ 0)
    (Ψ : (Fin 3 → v.adicCompletion ℚ) → ℂ) {c : ℤ} (hc : 0 ≤ c) {a s : (v.adicCompletion ℚ)ˣ} (hs1 : ‖s.val‖ ≤ 1)
    (ha : ‖a.val‖ ≤ ‖x‖) (p : v.adicCompletion ℚ × v.adicCompletion ℚ × v.adicCompletion ℚ) :
    (unipotentBall3 v c).indicator (dualIntegrand v ν Ψ (a * s) x)
        (p.1, p.2.1 + a.val * (s.val - 1) / x, p.2.2 + p.1 * (a.val * (s.val - 1) / x)) =
      ((ν 2 s : ℂ))⁻¹ * ((‖s.val‖ : ℝ) : ℂ) *
        (unipotentBall3 v c).indicator (dualIntegrand v ν (Ψ ∘ dualTailMap v x s.val) a x) p := by
  obtain ⟨α, β, γ⟩ := p
  dsimp only
  have hxpos : 0 < ‖x‖ := norm_pos_iff.mpr hx
  have hk : ‖a.val * (s.val - 1) / x‖ ≤ 1 := by
    rw [norm_div, norm_mul, div_le_one₀ hxpos, norm_sub_rev]
    exact (mul_le_of_le_one_right (norm_nonneg _) (norm_one_sub_le_one v hs1)).trans ha
  have hm := mem_unipotentBall3_translate_iff v hc hk α β γ
  have hsec : cellSectionOf v ν Ψ
      (dualCellPoint v α (β + a.val * (s.val - 1) / x) (γ + α * (a.val * (s.val - 1) / x)) (a * s) x) =
      ((ν 2 s : ℂ))⁻¹ * ((‖s.val‖ : ℝ) : ℂ) *
        cellSectionOf v ν (Ψ ∘ dualTailMap v x s.val) (dualCellPoint v α β γ a x) := by
    have e : γ + α * (a.val * (s.val - 1) / x) = γ + a.val * α * (s.val - 1) / x := by ring
    rw [e]
    exact cellSectionOf_dualCellPoint_translateCoords v ν Ψ hx α β γ a s
  have hψ : psiLocal ℚ v (-(α + (β + a.val * (s.val - 1) / x))) = psiLocal ℚ v (-(α + β)) := by
    have e : -(α + (β + a.val * (s.val - 1) / x)) = -(α + β) + -(a.val * (s.val - 1) / x) := by ring
    have hk' : ‖-(a.val * (s.val - 1) / x)‖ ≤ 1 := by rwa [norm_neg]
    rw [e, AddChar.map_add_eq_mul, psiLocal_eq_one_of_norm_le_one v hk', mul_one]
  by_cases hαβ : (α, β, γ) ∈ unipotentBall3 v c
  · rw [Set.indicator_of_mem (hm.mpr hαβ), Set.indicator_of_mem hαβ]
    simp only [dualIntegrand]
    rw [hsec, hψ]
    ring
  · rw [Set.indicator_of_notMem fun h => hαβ (hm.mp h), Set.indicator_of_notMem hαβ, mul_zero]

private theorem jacquetValue_dualTranslate_mul_eq_comp_dualTailMap (hν : ∀ i, IsLocallyConstant (ν i))
    {x : v.adicCompletion ℚ} (hx : x ≠ 0) (Ψ : (Fin 3 → v.adicCompletion ℚ) → ℂ) (hΨl : IsLocallyConstant Ψ)
    (hΨc : HasCompactSupport Ψ) (a s : (v.adicCompletion ℚ)ˣ) (hs1 : ‖s.val‖ ≤ 1) (ha : ‖a.val‖ ≤ ‖x‖) :
    jacquetValue v (dualTranslate v ν Ψ (a * s) x) =
      ((ν 2 s : ℂ))⁻¹ * ((‖s.val‖ : ℝ) : ℂ) * jacquetValue v (dualTranslate v ν (Ψ ∘ dualTailMap v x s.val) a x) := by
  have hσl : IsLocallyConstant (Ψ ∘ dualTailMap v x s.val) := isLocallyConstant_comp_dualTailMap v hΨl x s.val
  have hσc : HasCompactSupport (Ψ ∘ dualTailMap v x s.val) := hasCompactSupport_comp_dualTailMap v hΨc x s.ne_zero
  obtain ⟨c₁, hc₁⟩ := exists_forall_integrable_indicator_dualIntegrand v ν hν hΨl hΨc (a * s) x
  obtain ⟨c₂, hc₂⟩ := exists_forall_integrable_indicator_dualIntegrand v ν hν hσl hσc a x
  refine jacquetValue_eq_mul_of v (exists_level_dualTranslate v ν Ψ hν hΨl hΨc (a * s) x)
    (exists_level_dualTranslate v ν _ hν hσl hσc a x) ⟨max c₁ c₂, fun c hc => ?_⟩
  have hc' : (0 : ℤ) ≤ c := le_trans (by positivity) hc
  have hcc₁ : (c₁ : ℤ) ≤ c := le_trans (by exact_mod_cast le_max_left c₁ c₂) hc
  have hcc₂ : (c₂ : ℤ) ≤ c := le_trans (by exact_mod_cast le_max_right c₁ c₂) hc
  have hpt : (fun p : v.adicCompletion ℚ × v.adicCompletion ℚ × v.adicCompletion ℚ =>
      (unipotentBall3 v c).indicator (dualIntegrand v ν Ψ (a * s) x)
        (p.1, p.2.1 + a.val * (s.val - 1) / x, p.2.2 + p.1 * (a.val * (s.val - 1) / x))) =
      fun p => ((ν 2 s : ℂ))⁻¹ * ((‖s.val‖ : ℝ) : ℂ) *
        (unipotentBall3 v c).indicator (dualIntegrand v ν (Ψ ∘ dualTailMap v x s.val) a x) p :=
    funext fun p => indicator_dualIntegrand_translateCoords v ν hx Ψ hc' hs1 ha p
  have hG' : Integrable (fun p : v.adicCompletion ℚ × v.adicCompletion ℚ × v.adicCompletion ℚ =>
      (unipotentBall3 v c).indicator (dualIntegrand v ν Ψ (a * s) x)
        (p.1, p.2.1 + a.val * (s.val - 1) / x, p.2.2 + p.1 * (a.val * (s.val - 1) / x))) (jacquetHaar3 v) := by
    rw [hpt]
    exact (hc₂ c hcc₂).const_mul _
  rw [jacquetTruncated3_dualTranslate_eq_integral_indicator, jacquetTruncated3_dualTranslate_eq_integral_indicator,
    integral_jacquetHaar3_comp_add_mul v (a.val * (s.val - 1) / x) _ (hc₁ c hcc₁) hG', hpt, integral_const_mul]

private theorem hasPullbackCovariance_dualSlice (hν : ∀ i, IsLocallyConstant (ν i)) {x : v.adicCompletion ℚ}
    (hx : x ≠ 0) :
    HasPullbackCovariance v (fun Ψ t => dualSlice v ν Ψ x t)
      (fun s : (v.adicCompletion ℚ)ˣ => dualTailMap v x (s : v.adicCompletion ℚ)) (ν 2)⁻¹ := by
  intro Ψ hΨl hΨc s _ hs1
  refine ⟨‖x‖, norm_pos_iff.mpr hx, fun t ht => ?_⟩
  by_cases ht0 : t = 0
  · simp only [ht0, mul_zero, dualSlice_zero]
  · have h := dualSlice_mul_eq_of_jacquetValue_eq v ν Ψ (Ψ ∘ dualTailMap v x s.val) x (Units.mk0 t ht0) s
      (jacquetValue_dualTranslate_mul_eq_comp_dualTailMap v ν hν hx Ψ hΨl hΨc (Units.mk0 t ht0) s hs1 ht)
    rw [coe_inv_apply]
    exact h

private theorem hasOuterCovariance_dualSlice (hν : ∀ i, IsLocallyConstant (ν i)) {x : v.adicCompletion ℚ}
    (hx : x ≠ 0) :
    HasOuterCovariance v (bulkGauge v x) (fun Ψ t => dualSlice v ν Ψ x t) (ν 0)⁻¹ := by
  intro Ψ hΨl hΨc ρ hρ hsupp s _ hs1
  obtain ⟨ε, hε, h⟩ := exists_forall_jacquetValue_dualTranslate_mul_eq_of_gauge v ν hν hx Ψ hΨl hΨc hρ hsupp
  refine ⟨ε, hε, fun t ht => ?_⟩
  by_cases ht0 : t = 0
  · simp only [ht0, mul_zero, dualSlice_zero]
  · have h' := dualSlice_mul_eq_of_jacquetValue_eq v ν Ψ Ψ x (Units.mk0 t ht0) s (h (Units.mk0 t ht0) s hs1 ht)
    rw [coe_inv_apply]
    exact h'

private theorem hasNearDecomposition_dualSlice (hν : ∀ i, IsLocallyConstant (ν i)) {x : v.adicCompletion ℚ}
    (hx : x ≠ 0) :
    HasNearDecomposition v (bulkGauge v x) (fun r => r 0) (fun Ψ t => dualSlice v ν Ψ x t) (ν 1)⁻¹ := by
  intro Ψ hΨl hΨc δ hδ hvan
  have hvan' : ∀ r : Fin 3 → v.adicCompletion ℚ, Ψ r ≠ 0 → ‖1 + x * (r 1 - r 2 * r 0)‖ ≤ δ → δ ≤ ‖r 0‖ := by
    intro r hr hg
    by_contra hlt
    exact hr (hvan r (by rwa [bulkGauge_def]) (not_le.mp hlt).le)
  obtain ⟨κ, hκ, ε, hε, hid⟩ := exists_forall_jacquetValue_dualTranslate_mul_eq_near v ν hν hx Ψ hΨl hΨc hδ hvan'
  set S : ℝ → Set (Fin 3 → v.adicCompletion ℚ) :=
    fun κ' => {r : Fin 3 → v.adicCompletion ℚ | ‖1 + x * (r 1 - r 2 * r 0)‖ ≤ κ'}
  have hSκ : ∀ {κ' : ℝ}, 0 < κ' → IsClopen (S κ') := fun h => isClopen_setOf_norm_curve_le v x h
  have hoff : ∀ {κ' : ℝ} (r : Fin 3 → v.adicCompletion ℚ), r ∉ S κ' → κ' < ‖bulkGauge v x r‖ := by
    intro κ' r hr
    rw [bulkGauge_def]
    exact not_le.mp hr
  refine ⟨(S κ)ᶜ.indicator Ψ, (S κ).indicator Ψ,
    isLocallyConstant_indicator_of_isClopen_T v (hSκ hκ).compl hΨl, hasCompactSupport_indicator_T v _ hΨc,
    isLocallyConstant_indicator_of_isClopen_T v (hSκ hκ) hΨl, hasCompactSupport_indicator_T v _ hΨc,
    by rw [add_comm]; exact (Set.indicator_self_add_compl (S κ) Ψ).symm,
    ⟨κ, hκ, fun r hr => hoff r (Set.mem_of_indicator_ne_zero hr)⟩, fun s hs0 hs1 => ?_⟩
  have hspos : 0 < ‖s.val‖ := (norm_varpi_pos v).trans_le hs0
  have hκs : 0 < κ / ‖s.val‖ := div_pos hκ hspos
  refine ⟨(S (κ / ‖s.val‖)).indicator Ψ, isLocallyConstant_indicator_of_isClopen_T v (hSκ hκs) hΨl,
    hasCompactSupport_indicator_T v _ hΨc, ⟨κ, hκ, fun r hr => ?_⟩, ε, hε, fun t ht => ?_⟩
  ·
    refine hoff r fun hrκ => hr ?_
    have hrκ' : r ∈ S (κ / ‖s.val‖) :=
      le_trans (show ‖1 + x * (r 1 - r 2 * r 0)‖ ≤ κ from hrκ) (le_div_self hκ.le hspos hs1)
    simp only [Pi.sub_apply, Set.indicator_of_mem hrκ, Set.indicator_of_mem hrκ', sub_self]
  · by_cases ht0 : t = 0
    · simp only [ht0, mul_zero, dualSlice_zero]
    · have h' := dualSlice_mul_eq_of_jacquetValue_eq v ν _ _ x (Units.mk0 t ht0) s (hid (Units.mk0 t ht0) s hs0 hs1 ht)
      rw [coe_inv_apply]
      exact h'

end DualSliceCovariances
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_eventually_threefold_twistedDifference_dualJacquetValueFn_eq_zero.LaurentZetaSlot P2MW.S_LanglandsTunnell_CubicInduction_eventually_threefold_twistedDifference_dualJacquetValueFn_eq_zero.WeylTranslateZeta"

end WeylTranslateZeta
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_eventually_threefold_twistedDifference_dualJacquetValueFn_eq_zero.LaurentZetaSlot P2MW.S_LanglandsTunnell_CubicInduction_eventually_threefold_twistedDifference_dualJacquetValueFn_eq_zero.WeylTranslateZeta"
end
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_eventually_threefold_twistedDifference_dualJacquetValueFn_eq_zero.LaurentZetaSlot P2MW.S_LanglandsTunnell_CubicInduction_eventually_threefold_twistedDifference_dualJacquetValueFn_eq_zero.WeylTranslateZeta"

section

open MeasureTheory
open IsDedekindDomain
open NumberField
open LanglandsTunnell.TateLocal
open NumberField.StandardAddChar
open LaurentZetaSlot (twistedDiff)

attribute [local instance] LanglandsTunnell.TateLocal.localBorel

namespace WeylTranslateZeta
open LanglandsTunnell.CubicInduction

variable (v : HeightOneSpectrum (𝓞 ℚ))
variable (ν : Fin 3 → ((v.adicCompletion ℚ)ˣ →* ℂˣ)) (Φ : (Fin 3 → v.adicCompletion ℚ) → ℂ)

private theorem indicator_dualIntegrand_scaleCoords_zero (Ψ : (Fin 3 → v.adicCompletion ℚ) → ℂ) {R : ℝ}
    (hR : ∀ r : Fin 3 → v.adicCompletion ℚ, Ψ r ≠ 0 → ∀ i, ‖r i‖ ≤ R) {c : ℤ} (hc : 0 ≤ c)
    {a s : (v.adicCompletion ℚ)ˣ} (hs1 : ‖s.val‖ ≤ 1) (ha1 : ‖a.val‖ * R ≤ 1) (ha2 : ‖a.val‖ * (R * max 1 R) ≤ 1)
    (p : v.adicCompletion ℚ × v.adicCompletion ℚ × v.adicCompletion ℚ) :
    (unipotentBall3 v c).indicator (dualIntegrand v ν Ψ (a * s) 0) (p.1, s.val * p.2.1, s.val * p.2.2) =
      ((ν 0 s : ℂ))⁻¹ * ((‖s.val‖ : ℝ) : ℂ)⁻¹ * (unipotentBall3 v c).indicator (dualIntegrand v ν Ψ a 0) p := by
  obtain ⟨α, β, γ⟩ := p
  dsimp only
  have hsec := cellSectionOf_dualCellPoint_scaleCoords v ν Ψ α β γ 0 a s
  by_cases h0 : cellSectionOf v ν Ψ (dualCellPoint v α β γ a 0) = 0
  · have h1 : dualIntegrand v ν Ψ (a * s) 0 (α, s.val * β, s.val * γ) = 0 := by
      simp only [dualIntegrand, hsec, h0, mul_zero]
    have h2 : dualIntegrand v ν Ψ a 0 (α, β, γ) = 0 := by
      simp only [dualIntegrand, h0, mul_zero]
    rw [Set.indicator_apply_eq_zero.mpr fun _ => h1, Set.indicator_apply_eq_zero.mpr fun _ => h2, mul_zero]
  · have hmem : dualCellPoint v α β γ a 0 ∈ bigCell3 v := by
      by_contra hn
      exact h0 (cellSectionOf_apply_of_notMem v ν Ψ hn)
    have hΨ : Ψ (cellRatio v (dualCellPoint v α β γ a 0)) ≠ 0 := by
      intro hz
      apply h0
      simp [cellSectionOf_apply_of_mem v ν Ψ hmem, hz]
    obtain ⟨hγ, hβ⟩ := norm_coords_le_of_mem_zero v α β γ a hmem (hR _ hΨ)
    have hβ1 : ‖β‖ ≤ 1 := hβ.trans ha2
    have hγ1 : ‖γ‖ ≤ max 1 ‖α‖ := by
      calc ‖γ‖ ≤ ‖a.val‖ * R * ‖α‖ := hγ
        _ ≤ 1 * ‖α‖ := by gcongr
        _ = ‖α‖ := one_mul _
        _ ≤ max 1 ‖α‖ := le_max_right _ _
    have hm : (α, β, γ) ∈ unipotentBall3 v c ↔ Valued.v α ≤ WithZero.exp c :=
      mem_unipotentBall3_iff_of_small v hc hβ1 hγ1
    have hsβ : ‖s.val * β‖ ≤ 1 := by
      rw [norm_mul]
      exact mul_le_one₀ hs1 (norm_nonneg _) hβ1
    have hsγ : ‖s.val * γ‖ ≤ max 1 ‖α‖ := by
      rw [norm_mul]
      exact (mul_le_of_le_one_left (norm_nonneg _) hs1).trans hγ1
    have hm' : (α, s.val * β, s.val * γ) ∈ unipotentBall3 v c ↔ Valued.v α ≤ WithZero.exp c :=
      mem_unipotentBall3_iff_of_small v hc hsβ hsγ
    by_cases hα : Valued.v α ≤ WithZero.exp c
    · rw [Set.indicator_of_mem (hm'.mpr hα), Set.indicator_of_mem (hm.mpr hα)]
      simp only [dualIntegrand]
      rw [hsec]
      have hψ : psiLocal ℚ v (-(α + s.val * β)) = psiLocal ℚ v (-(α + β)) := by
        have e : -(α + s.val * β) = -(α + β) + (1 - s.val) * β := by ring
        have h1 : ‖(1 - s.val) * β‖ ≤ 1 := by
          rw [norm_mul]
          exact mul_le_one₀ (norm_one_sub_le_one v hs1) (norm_nonneg _) hβ1
        rw [e, AddChar.map_add_eq_mul, psiLocal_eq_one_of_norm_le_one v h1, mul_one]
      rw [hψ]
      ring
    · rw [Set.indicator_of_notMem fun h => hα (hm'.mp h), Set.indicator_of_notMem fun h => hα (hm.mp h),
        mul_zero]

private theorem exists_forall_jacquetValue_dualTranslate_zero_mul_eq (hν : ∀ i, IsLocallyConstant (ν i))
    (Ψ : (Fin 3 → v.adicCompletion ℚ) → ℂ) (hΨl : IsLocallyConstant Ψ) (hΨc : HasCompactSupport Ψ) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ a s : (v.adicCompletion ℚ)ˣ, ‖s.val‖ ≤ 1 → ‖a.val‖ ≤ ε →
      jacquetValue v (dualTranslate v ν Ψ (a * s) 0) =
        ((ν 0 s : ℂ))⁻¹ * ((‖s.val‖ : ℝ) : ℂ) * jacquetValue v (dualTranslate v ν Ψ a 0) := by
  obtain ⟨R₀, hR₀⟩ := exists_support_radius v Ψ hΨc
  set R : ℝ := max R₀ 0 with hRdef
  have hR : ∀ r : Fin 3 → v.adicCompletion ℚ, Ψ r ≠ 0 → ∀ i, ‖r i‖ ≤ R :=
    fun r hr i => (hR₀ r hr i).trans (le_max_left _ _)
  have hR0 : 0 ≤ R := le_max_right _ _
  have hK : 0 < max 1 (R * max 1 R) := lt_max_of_lt_left one_pos
  refine ⟨(max 1 (R * max 1 R))⁻¹, inv_pos.mpr hK, fun a s hs1 ha => ?_⟩
  have hRR : 0 ≤ R * max 1 R := mul_nonneg hR0 (le_max_of_le_left zero_le_one)
  have ha2 : ‖a.val‖ * (R * max 1 R) ≤ 1 := by
    calc ‖a.val‖ * (R * max 1 R) ≤ (max 1 (R * max 1 R))⁻¹ * (R * max 1 R) := by gcongr
      _ ≤ (max 1 (R * max 1 R))⁻¹ * max 1 (R * max 1 R) := by
          gcongr
          exact le_max_right _ _
      _ = 1 := inv_mul_cancel₀ hK.ne'
  have ha1 : ‖a.val‖ * R ≤ 1 := by
    refine le_trans ?_ ha2
    gcongr
    exact le_mul_of_one_le_right hR0 (le_max_left _ _)
  refine jacquetValue_eq_mul_of v (exists_level_dualTranslate v ν Ψ hν hΨl hΨc (a * s) 0)
    (exists_level_dualTranslate v ν Ψ hν hΨl hΨc a 0) ⟨0, fun c hc => ?_⟩
  have hc' : (0 : ℤ) ≤ c := by exact_mod_cast hc
  have hsne : ((‖s.val‖ : ℝ) : ℂ) ≠ 0 := by exact_mod_cast norm_ne_zero_iff.mpr s.ne_zero
  rw [jacquetTruncated3_dualTranslate_eq_integral_indicator, jacquetTruncated3_dualTranslate_eq_integral_indicator,
    integral_jacquetHaar3_comp_scale_snd v s.val s.ne_zero
      ((unipotentBall3 v c).indicator (dualIntegrand v ν Ψ (a * s) 0))]
  have hpt : (fun p : v.adicCompletion ℚ × v.adicCompletion ℚ × v.adicCompletion ℚ =>
      (unipotentBall3 v c).indicator (dualIntegrand v ν Ψ (a * s) 0) (p.1, s.val * p.2.1, s.val * p.2.2)) =
      fun p => ((ν 0 s : ℂ))⁻¹ * ((‖s.val‖ : ℝ) : ℂ)⁻¹ * (unipotentBall3 v c).indicator (dualIntegrand v ν Ψ a 0) p :=
    funext fun p => indicator_dualIntegrand_scaleCoords_zero v ν Ψ hR hc' hs1 ha1 ha2 p
  rw [hpt, integral_const_mul]
  set J := ∫ p, (unipotentBall3 v c).indicator (dualIntegrand v ν Ψ a 0) p ∂(jacquetHaar3 v)
  push_cast
  linear_combination (((ν 0 s : ℂ))⁻¹ * ((‖s.val‖ : ℝ) : ℂ) * J) * mul_inv_cancel₀ hsne

private theorem exists_forall_dualSlice_zero_mul_eq (hν : ∀ i, IsLocallyConstant (ν i)) (hΦl : IsLocallyConstant Φ)
    (hΦc : HasCompactSupport Φ) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ s : (v.adicCompletion ℚ)ˣ, ‖s.val‖ ≤ 1 → ∀ t : v.adicCompletion ℚ, ‖t‖ ≤ ε →
      dualSlice v ν Φ 0 (t * s.val) = ((ν 0 s : ℂ))⁻¹ * dualSlice v ν Φ 0 t := by
  obtain ⟨ε, hε, h⟩ := exists_forall_jacquetValue_dualTranslate_zero_mul_eq v ν hν Φ hΦl hΦc
  refine ⟨ε, hε, fun s hs1 t ht => ?_⟩
  by_cases ht0 : t = 0
  · simp only [ht0, zero_mul, dualSlice_zero, mul_zero]
  · have h' := dualSlice_mul_eq_of_jacquetValue_eq v ν Φ Φ 0 (Units.mk0 t ht0) s (h (Units.mk0 t ht0) s hs1 ht)
    rw [mul_comm]
    exact h'

private theorem exists_forall_twistedDiff₃_dualSlice_zero_mul_eq (hν : ∀ i, IsLocallyConstant (ν i))
    (hΦl : IsLocallyConstant Φ) (hΦc : HasCompactSupport Φ) (α : Fin 3 → ℂ) :
    ∃ η : ℝ, 0 < η ∧ ∀ s : (v.adicCompletion ℚ)ˣ, ‖s.val‖ ≤ 1 →
      (∀ t : v.adicCompletion ℚ, ‖t‖ ≤ η * ‖(NumberField.AdelicLevel.uniformizerUnit ℚ v).val‖ →
        twistedDiff v (α 1) (twistedDiff v (α 2) (dualSlice v ν Φ 0)) (t * s.val) =
          ((ν 0 s : ℂ))⁻¹ * twistedDiff v (α 1) (twistedDiff v (α 2) (dualSlice v ν Φ 0)) t) ∧
      ∀ t : v.adicCompletion ℚ, ‖t‖ ≤ η →
        LaurentZetaSlot.twistedDiff₃ v α (dualSlice v ν Φ 0) (t * s.val) =
          ((ν 0 s : ℂ))⁻¹ * LaurentZetaSlot.twistedDiff₃ v α (dualSlice v ν Φ 0) t := by
  obtain ⟨ε, hε, h⟩ := exists_forall_dualSlice_zero_mul_eq v ν Φ hν hΦl hΦc
  have hϖ : 0 < ‖(NumberField.AdelicLevel.uniformizerUnit ℚ v).val‖ := norm_varpi_pos v
  refine ⟨ε * ‖(NumberField.AdelicLevel.uniformizerUnit ℚ v).val‖ *
    ‖(NumberField.AdelicLevel.uniformizerUnit ℚ v).val‖ * ‖(NumberField.AdelicLevel.uniformizerUnit ℚ v).val‖,
    by positivity, fun s hs1 => ?_⟩
  have h2 : ∀ t : v.adicCompletion ℚ, ‖t‖ ≤ ε * ‖(NumberField.AdelicLevel.uniformizerUnit ℚ v).val‖ →
      twistedDiff v (α 2) (dualSlice v ν Φ 0) (t * s.val) =
        ((ν 0 s : ℂ))⁻¹ * twistedDiff v (α 2) (dualSlice v ν Φ 0) t :=
    fun t ht => twistedDiff_mul_eq_of_ball' v hε (h s hs1) (α 2) t ht
  have h1 : ∀ t : v.adicCompletion ℚ, ‖t‖ ≤ ε * ‖(NumberField.AdelicLevel.uniformizerUnit ℚ v).val‖ *
        ‖(NumberField.AdelicLevel.uniformizerUnit ℚ v).val‖ →
      twistedDiff v (α 1) (twistedDiff v (α 2) (dualSlice v ν Φ 0)) (t * s.val) =
        ((ν 0 s : ℂ))⁻¹ * twistedDiff v (α 1) (twistedDiff v (α 2) (dualSlice v ν Φ 0)) t :=
    fun t ht => twistedDiff_mul_eq_of_ball' v (mul_pos hε hϖ) h2 (α 1) t ht
  refine ⟨fun t ht => h1 t (ht.trans ?_),
    fun t ht => twistedDiff_mul_eq_of_ball' v (mul_pos (mul_pos hε hϖ) hϖ) h1 (α 0) t ht⟩
  exact (mul_le_of_le_one_right (by positivity) (norm_varpi_le_one v)).trans
    (mul_le_of_le_one_right (by positivity) (norm_varpi_le_one v))

private theorem exists_forall_twistedDiff₃_dualSlice_zero_eq_zero (hν : ∀ i, IsLocallyConstant (ν i))
    (hΦl : IsLocallyConstant Φ) (hΦc : HasCompactSupport Φ) (α : Fin 3 → ℂ)
    (hα0 : α 0 = ((ν 0 (NumberField.AdelicLevel.uniformizerUnit ℚ v) : ℂ))⁻¹) :
    ∃ η : ℝ, 0 < η ∧ ∀ t : v.adicCompletion ℚ, ‖t‖ ≤ η →
      LaurentZetaSlot.twistedDiff₃ v α (dualSlice v ν Φ 0) t = 0 := by
  obtain ⟨η, hη, hcov⟩ := exists_forall_twistedDiff₃_dualSlice_zero_mul_eq v ν Φ hν hΦl hΦc α
  obtain ⟨h1, -⟩ := hcov (NumberField.AdelicLevel.uniformizerUnit ℚ v) (norm_varpi_le_one v)
  have hϖ : 0 < ‖(NumberField.AdelicLevel.uniformizerUnit ℚ v).val‖ := norm_varpi_pos v
  refine ⟨η * ‖(NumberField.AdelicLevel.uniformizerUnit ℚ v).val‖ *
    ‖(NumberField.AdelicLevel.uniformizerUnit ℚ v).val‖, mul_pos (mul_pos hη hϖ) hϖ, fun t ht => ?_⟩
  have hg := h1 (t / (NumberField.AdelicLevel.uniformizerUnit ℚ v).val) (norm_div_varpi_le v ht)
  rw [div_mul_cancel₀ t (NumberField.AdelicLevel.uniformizerUnit ℚ v).ne_zero] at hg
  show twistedDiff v (α 0) (twistedDiff v (α 1) (twistedDiff v (α 2) (dualSlice v ν Φ 0))) t = 0
  rw [twistedDiff_apply, hg, hα0, sub_self]

private theorem twistedDiff_const_mul_sum (S : Finset (v.adicCompletion ℚ)) (c : ℂ)
    (g : v.adicCompletion ℚ → v.adicCompletion ℚ → ℂ) (β : ℂ) :
    twistedDiff v β (fun t => c * ∑ x ∈ S, g x t) = fun t => c * ∑ x ∈ S, twistedDiff v β (g x) t := by
  funext t
  simp only [twistedDiff_apply, Finset.sum_sub_distrib, ← Finset.mul_sum]
  ring

private theorem twistedDiff₃_const_mul_sum (S : Finset (v.adicCompletion ℚ)) (c : ℂ)
    (g : v.adicCompletion ℚ → v.adicCompletion ℚ → ℂ) (α : Fin 3 → ℂ) :
    LaurentZetaSlot.twistedDiff₃ v α (fun t => c * ∑ x ∈ S, g x t) =
      fun t => c * ∑ x ∈ S, LaurentZetaSlot.twistedDiff₃ v α (g x) t := by
  simp only [LaurentZetaSlot.twistedDiff₃, twistedDiff_const_mul_sum]

private theorem eventually_finset_sum_eq (S : Finset (v.adicCompletion ℚ))
    (F : v.adicCompletion ℚ → v.adicCompletion ℚ → ℂ)
    (hF : ∀ x ∈ S, ∀ t : v.adicCompletion ℚ, t ≠ 0 → ∀ᶠ t' in nhds t, F x t' = F x t) (t : v.adicCompletion ℚ)
    (ht : t ≠ 0) : ∀ᶠ t' in nhds t, (∑ x ∈ S, F x t') = ∑ x ∈ S, F x t := by
  have h : ∀ᶠ t' in nhds t, ∀ x ∈ S, F x t' = F x t :=
    (Filter.eventually_all_finset S).mpr fun x hx => hF x hx t ht
  filter_upwards [h] with t' ht'
  exact Finset.sum_congr rfl ht'

private theorem unitProj_finset_sum (χ : (v.adicCompletion ℚ)ˣ →* ℂˣ) (hχ : IsLocallyConstant χ)
    (S : Finset (v.adicCompletion ℚ)) (F : v.adicCompletion ℚ → v.adicCompletion ℚ → ℂ)
    (hF : ∀ x ∈ S, ∀ t : v.adicCompletion ℚ, t ≠ 0 → ∀ᶠ t' in nhds t, F x t' = F x t) (a : v.adicCompletion ℚ) :
    LaurentZetaSlot.unitProj v χ (fun t => ∑ x ∈ S, F x t) a = ∑ x ∈ S, LaurentZetaSlot.unitProj v χ (F x) a := by
  classical
  induction S using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    exact unitProj_eq_zero_of_ball v χ (η := ‖a‖) (fun _ _ => rfl) a le_rfl
  | insert y S hy ih =>
    have hF' : ∀ x ∈ S, ∀ t : v.adicCompletion ℚ, t ≠ 0 → ∀ᶠ t' in nhds t, F x t' = F x t :=
      fun x hx => hF x (Finset.mem_insert_of_mem hx)
    simp only [Finset.sum_insert hy]
    rw [unitProj_eq_add v χ hχ (f := fun t => F y t + ∑ x ∈ S, F x t) (g := F y) (g' := fun t => ∑ x ∈ S, F x t)
      (hF y (Finset.mem_insert_self y S)) (fun t ht => eventually_finset_sum_eq v S F hF' t ht) (fun _ => rfl) a,
      ih hF']

end WeylTranslateZeta
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_eventually_threefold_twistedDifference_dualJacquetValueFn_eq_zero.LaurentZetaSlot P2MW.S_LanglandsTunnell_CubicInduction_eventually_threefold_twistedDifference_dualJacquetValueFn_eq_zero.WeylTranslateZeta"
end
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_eventually_threefold_twistedDifference_dualJacquetValueFn_eq_zero.LaurentZetaSlot P2MW.S_LanglandsTunnell_CubicInduction_eventually_threefold_twistedDifference_dualJacquetValueFn_eq_zero.WeylTranslateZeta"

section

open MeasureTheory
open IsDedekindDomain
open NumberField
open LanglandsTunnell.TateLocal
open NumberField.StandardAddChar

attribute [local instance] LanglandsTunnell.TateLocal.localBorel

namespace WeylTranslateZeta
open LanglandsTunnell.CubicInduction

variable (v : HeightOneSpectrum (𝓞 ℚ))
variable (ν : Fin 3 → ((v.adicCompletion ℚ)ˣ →* ℂˣ)) (Φ : (Fin 3 → v.adicCompletion ℚ) → ℂ)

private theorem eventually_twistedDiff₃_dualSlice_eq_zero (hν : ∀ i, IsLocallyConstant (ν i))
    (hΦl : IsLocallyConstant Φ) (hΦc : HasCompactSupport Φ) (x : v.adicCompletion ℚ) :
    ∀ᶠ t in nhds (0 : v.adicCompletion ℚ),
      LaurentZetaSlot.twistedDiff₃ v
        (fun i => ((((ν i) (NumberField.AdelicLevel.uniformizerUnit ℚ v))⁻¹ : ℂˣ) : ℂ)) (dualSlice v ν Φ x) t = 0 := by
  by_cases hx : x = 0
  · subst hx
    obtain ⟨η, hη, h⟩ := exists_forall_twistedDiff₃_dualSlice_zero_eq_zero v ν Φ hν hΦl hΦc
      (fun i => ((((ν i) (NumberField.AdelicLevel.uniformizerUnit ℚ v))⁻¹ : ℂˣ) : ℂ)) (Units.val_inv_eq_inv_val _)
    exact Filter.eventually_of_mem (Metric.closedBall_mem_nhds (0 : v.adicCompletion ℚ) hη) fun t ht =>
      h t (mem_closedBall_zero_iff.mp ht)
  · have h := eventually_twistedDiff₃_eq_zero_of_covariance v (T := fun Ψ t => dualSlice v ν Ψ x t)
      (isTestAdditive_dualSlice v ν hν x) (isTestTransport_dualTailMap v x) (pullbackSubVanishesNear_dualTailMap v hx)
      (hasPullbackCovariance_dualSlice v ν hν hx) (hasNearDecomposition_dualSlice v ν hν hx)
      (hasOuterCovariance_dualSlice v ν hν hx) Φ hΦl hΦc
    simpa only [LaurentZetaSlot.twistedDiff₃, MonoidHom.inv_apply] using h

end WeylTranslateZeta
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_eventually_threefold_twistedDifference_dualJacquetValueFn_eq_zero.LaurentZetaSlot P2MW.S_LanglandsTunnell_CubicInduction_eventually_threefold_twistedDifference_dualJacquetValueFn_eq_zero.WeylTranslateZeta"
end
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_eventually_threefold_twistedDifference_dualJacquetValueFn_eq_zero.LaurentZetaSlot P2MW.S_LanglandsTunnell_CubicInduction_eventually_threefold_twistedDifference_dualJacquetValueFn_eq_zero.WeylTranslateZeta"

section

open MeasureTheory
open IsDedekindDomain
open NumberField
open LanglandsTunnell.TateLocal
open NumberField.StandardAddChar

attribute [local instance] LanglandsTunnell.TateLocal.localBorel

namespace WeylTranslateZeta
open LanglandsTunnell.CubicInduction

section DualFnOffZero

variable (v : HeightOneSpectrum (𝓞 ℚ))
variable (ν : Fin 3 → ((v.adicCompletion ℚ)ˣ →* ℂˣ)) (Φ : (Fin 3 → v.adicCompletion ℚ) → ℂ)

private theorem eventually_dualSlice_eq (hν : ∀ i, IsLocallyConstant (ν i)) (hΦl : IsLocallyConstant Φ)
    (hΦc : HasCompactSupport Φ) (x : v.adicCompletion ℚ) {t : v.adicCompletion ℚ} (ht : t ≠ 0) :
    ∀ᶠ t' in nhds t, dualSlice v ν Φ x t' = dualSlice v ν Φ x t := by
  obtain ⟨h1, -, -, -⟩ := dualJacquetValueSlices_eventually_eq_and_eq_zero_and_eq_mul_sum v ν hν Φ hΦl hΦc
  exact h1 x (dualSlice v ν Φ x) (dualSlice_zero v ν Φ x)
    (fun a => by rw [dualSlice, dif_neg a.ne_zero, Units.mk0_val]; rfl) t ht

private theorem eventually_dualFn_eq' (hν : ∀ i, IsLocallyConstant (ν i)) (hΦl : IsLocallyConstant Φ)
    (hΦc : HasCompactSupport Φ) (t : v.adicCompletion ℚ) (ht : t ≠ 0) :
    ∀ᶠ t' in nhds t, dualFn v ν Φ t' = dualFn v ν Φ t := by
  obtain ⟨-, h2, -, -⟩ := dualJacquetValueSlices_eventually_eq_and_eq_zero_and_eq_mul_sum v ν hν Φ hΦl hΦc
  exact h2 (dualFn v ν Φ) (dualFn_zero v ν Φ) (fun a => by rw [dualFn_coe_units]; rfl) t ht

end DualFnOffZero
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_eventually_threefold_twistedDifference_dualJacquetValueFn_eq_zero.LaurentZetaSlot P2MW.S_LanglandsTunnell_CubicInduction_eventually_threefold_twistedDifference_dualJacquetValueFn_eq_zero.WeylTranslateZeta"

end WeylTranslateZeta
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_eventually_threefold_twistedDifference_dualJacquetValueFn_eq_zero.LaurentZetaSlot P2MW.S_LanglandsTunnell_CubicInduction_eventually_threefold_twistedDifference_dualJacquetValueFn_eq_zero.WeylTranslateZeta"
end
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_eventually_threefold_twistedDifference_dualJacquetValueFn_eq_zero.LaurentZetaSlot P2MW.S_LanglandsTunnell_CubicInduction_eventually_threefold_twistedDifference_dualJacquetValueFn_eq_zero.WeylTranslateZeta"

section

open MeasureTheory
open IsDedekindDomain
open NumberField
open LanglandsTunnell.TateLocal
open NumberField.StandardAddChar

attribute [local instance] LanglandsTunnell.TateLocal.localBorel

namespace WeylTranslateZeta
open LanglandsTunnell.CubicInduction

section DualNet

variable (v : HeightOneSpectrum (𝓞 ℚ))
variable (ν : Fin 3 → ((v.adicCompletion ℚ)ˣ →* ℂˣ)) (Φ : (Fin 3 → v.adicCompletion ℚ) → ℂ)

private theorem exists_finset_forall_dualFn_eq_mul_sum_dualSlice' (hν : ∀ i, IsLocallyConstant (ν i))
    (hΦl : IsLocallyConstant Φ) (hΦc : HasCompactSupport Φ) :
    ∃ (S : Finset (v.adicCompletion ℚ)) (c : ℂ), ∀ t : v.adicCompletion ℚ,
      dualFn v ν Φ t = c * ∑ x ∈ S, dualSlice v ν Φ x t := by
  obtain ⟨-, -, -, S, c, h⟩ := dualJacquetValueSlices_eventually_eq_and_eq_zero_and_eq_mul_sum v ν hν Φ hΦl hΦc
  refine ⟨S, c, fun t => ?_⟩
  by_cases ht : t = 0
  · simp [ht, dualFn_zero, dualSlice_zero]
  · have h' := h (Units.mk0 t ht)
    simp only [Units.val_mk0] at h'
    simp only [dualFn, dualSlice, dif_neg ht]
    exact h'

end DualNet
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_eventually_threefold_twistedDifference_dualJacquetValueFn_eq_zero.LaurentZetaSlot P2MW.S_LanglandsTunnell_CubicInduction_eventually_threefold_twistedDifference_dualJacquetValueFn_eq_zero.WeylTranslateZeta"

end WeylTranslateZeta
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_eventually_threefold_twistedDifference_dualJacquetValueFn_eq_zero.LaurentZetaSlot P2MW.S_LanglandsTunnell_CubicInduction_eventually_threefold_twistedDifference_dualJacquetValueFn_eq_zero.WeylTranslateZeta"
end
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_eventually_threefold_twistedDifference_dualJacquetValueFn_eq_zero.LaurentZetaSlot P2MW.S_LanglandsTunnell_CubicInduction_eventually_threefold_twistedDifference_dualJacquetValueFn_eq_zero.WeylTranslateZeta"

section
namespace WeylTranslateZeta
open LanglandsTunnell.CubicInduction
open MeasureTheory
open IsDedekindDomain
open NumberField
open LanglandsTunnell.TateLocal
open NumberField.StandardAddChar

section

attribute [local instance] LanglandsTunnell.TateLocal.localBorel

variable (v : HeightOneSpectrum (𝓞 ℚ))
variable (ν : Fin 3 → ((v.adicCompletion ℚ)ˣ →* ℂˣ)) (Φ : (Fin 3 → v.adicCompletion ℚ) → ℂ)

private theorem exists_finset_forall_dualFn_eq_mul_sum_dualSlice (hν : ∀ i, IsLocallyConstant (ν i))
    (hΦl : IsLocallyConstant Φ) (hΦc : HasCompactSupport Φ) :
    ∃ (S : Finset (v.adicCompletion ℚ)) (c : ℂ), ∀ t : v.adicCompletion ℚ,
      dualFn v ν Φ t = c * ∑ x ∈ S, dualSlice v ν Φ x t := by
  apply exists_finset_forall_dualFn_eq_mul_sum_dualSlice' <;> assumption

end
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_eventually_threefold_twistedDifference_dualJacquetValueFn_eq_zero.LaurentZetaSlot P2MW.S_LanglandsTunnell_CubicInduction_eventually_threefold_twistedDifference_dualJacquetValueFn_eq_zero.WeylTranslateZeta"

end WeylTranslateZeta
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_eventually_threefold_twistedDifference_dualJacquetValueFn_eq_zero.LaurentZetaSlot P2MW.S_LanglandsTunnell_CubicInduction_eventually_threefold_twistedDifference_dualJacquetValueFn_eq_zero.WeylTranslateZeta"
end
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_eventually_threefold_twistedDifference_dualJacquetValueFn_eq_zero.LaurentZetaSlot P2MW.S_LanglandsTunnell_CubicInduction_eventually_threefold_twistedDifference_dualJacquetValueFn_eq_zero.WeylTranslateZeta"

section

open MeasureTheory
open IsDedekindDomain
open NumberField
open LanglandsTunnell.TateLocal
open NumberField.StandardAddChar

attribute [local instance] LanglandsTunnell.TateLocal.localBorel

namespace WeylTranslateZeta
open LanglandsTunnell.CubicInduction

variable (v : HeightOneSpectrum (𝓞 ℚ))
variable (ν : Fin 3 → ((v.adicCompletion ℚ)ˣ →* ℂˣ)) (Φ : (Fin 3 → v.adicCompletion ℚ) → ℂ)

private theorem eventually_twistedDiff₃_unitProj_dualFn_eq_zero (hν : ∀ i, IsLocallyConstant (ν i))
    (hΦl : IsLocallyConstant Φ) (hΦc : HasCompactSupport Φ) (χ : (v.adicCompletion ℚ)ˣ →* ℂˣ)
    (hχ : IsLocallyConstant χ) (α : Fin 3 → ℂ)
    (hα : ∀ i, α i * ((χ⁻¹ (NumberField.AdelicLevel.uniformizerUnit ℚ v) : ℂˣ) : ℂ) =
      LaurentZetaSlot.slotScalar v (ν i * χ)⁻¹) :
    ∀ᶠ t in nhds (0 : v.adicCompletion ℚ),
      LaurentZetaSlot.twistedDiff₃ v α (LaurentZetaSlot.unitProj v χ⁻¹ (dualFn v ν Φ)) t = 0 := by
  have hχ' : IsLocallyConstant (⇑χ⁻¹ : (v.adicCompletion ℚ)ˣ → ℂˣ) := by
    have h : (⇑χ⁻¹ : (v.adicCompletion ℚ)ˣ → ℂˣ) = fun y => (χ y)⁻¹ := by
      funext y
      simp
    rw [h]
    exact IsLocallyConstant.comp hχ fun y : ℂˣ => y⁻¹
  have hα' : ∀ i, α i * ((χ⁻¹ (NumberField.AdelicLevel.uniformizerUnit ℚ v) : ℂˣ) : ℂ) =
      LaurentZetaSlot.slotScalar v ((ν i)⁻¹ * χ⁻¹) := by
    intro i
    exact (hα i).trans (congrArg (LaurentZetaSlot.slotScalar v) (mul_inv (ν i) χ))

  have hslice : ∀ x : v.adicCompletion ℚ, ∀ᶠ t in nhds (0 : v.adicCompletion ℚ),
      LaurentZetaSlot.unitProj v χ⁻¹ (LaurentZetaSlot.twistedDiff₃ v α (dualSlice v ν Φ x)) t = 0 := by
    intro x
    by_cases hx : x = 0
    · subst hx
      rcases slot_dichotomy v χ⁻¹ (ν 0)⁻¹ (hα' 0) with ⟨-, hα0⟩ | ⟨hram, hα0⟩
      ·
        rw [coe_inv_apply] at hα0
        obtain ⟨η, hη, h⟩ := exists_forall_twistedDiff₃_dualSlice_zero_eq_zero v ν Φ hν hΦl hΦc α hα0
        exact Filter.eventually_of_mem (Metric.closedBall_mem_nhds (0 : v.adicCompletion ℚ) hη) fun t ht =>
          unitProj_eq_zero_of_ball v χ⁻¹ h t (mem_closedBall_zero_iff.mp ht)
      ·
        obtain ⟨u, hu, hune⟩ := exists_unit_of_not_hasConductorExponentAt v hram
        obtain ⟨η, hη, hcov⟩ := exists_forall_twistedDiff₃_dualSlice_zero_mul_eq v ν Φ hν hΦl hΦc α
        obtain ⟨-, h3⟩ := hcov u (norm_eq_one_of_valued_eq_one v hu).le
        have hne := mul_charExt_ne_one v hune
        rw [coe_inv_apply] at hne
        have hG : ∀ t : v.adicCompletion ℚ, t ≠ 0 → ∀ᶠ t' in nhds t,
            LaurentZetaSlot.twistedDiff₃ v α (dualSlice v ν Φ 0) t' =
              LaurentZetaSlot.twistedDiff₃ v α (dualSlice v ν Φ 0) t :=
          fun t ht => LaurentZetaSlot.twistedDiff₃_eventually_eq v α
            (fun t ht => eventually_dualSlice_eq v ν Φ hν hΦl hΦc 0 ht) t ht
        refine Filter.eventually_of_mem (Metric.closedBall_mem_nhds (0 : v.adicCompletion ℚ) (lt_min hη hη))
          fun t ht => ?_
        exact unitProj_eq_zero_of_covariant v χ⁻¹ hχ' (g' := fun _ => (0 : ℂ)) hG
          (fun _ _ => Filter.Eventually.of_forall fun _ => rfl) hu hne
          (fun y hy => by simpa only [add_zero] using h3 y hy)
          (fun y _ => unitProj_eq_zero_of_ball v χ⁻¹ (η := ‖y‖) (fun _ _ => rfl) y le_rfl) t
          (mem_closedBall_zero_iff.mp ht)
    · have h := eventually_unitProj_twistedDiff₃_eq_zero_of_covariance v (T := fun Ψ t => dualSlice v ν Ψ x t)
        (isTestAdditive_dualSlice v ν hν x) (fun Ψ hΨl hΨc t ht => eventually_dualSlice_eq v ν Ψ hν hΨl hΨc x ht)
        (isTestTransport_dualTailMap v x)
        (pullbackSubVanishesNear_dualTailMap v hx) (hasPullbackCovariance_dualSlice v ν hν hx)
        (hasNearDecomposition_dualSlice v ν hν hx) (hasOuterCovariance_dualSlice v ν hν hx) Φ hΦl hΦc χ⁻¹ hχ'
        (hα' 2) (hα' 1) (hα' 0)
      simpa only [LaurentZetaSlot.twistedDiff₃] using h
  obtain ⟨S, c, hS⟩ := exists_finset_forall_dualFn_eq_mul_sum_dualSlice v ν Φ hν hΦl hΦc
  have hfun : dualFn v ν Φ = fun t => c * ∑ x ∈ S, dualSlice v ν Φ x t := funext hS
  rw [← LaurentZetaSlot.unitProj_twistedDiff₃ v χ⁻¹ hχ' α (fun t ht => eventually_dualFn_eq' v ν Φ hν hΦl hΦc t ht),
    hfun, twistedDiff₃_const_mul_sum]
  have hlc : ∀ x ∈ S, ∀ t : v.adicCompletion ℚ, t ≠ 0 → ∀ᶠ t' in nhds t,
      LaurentZetaSlot.twistedDiff₃ v α (dualSlice v ν Φ x) t' =
        LaurentZetaSlot.twistedDiff₃ v α (dualSlice v ν Φ x) t :=
    fun x _ t ht =>
      LaurentZetaSlot.twistedDiff₃_eventually_eq v α (fun t ht => eventually_dualSlice_eq v ν Φ hν hΦl hΦc x ht) t ht
  have hall : ∀ᶠ t in nhds (0 : v.adicCompletion ℚ), ∀ x ∈ S,
      LaurentZetaSlot.unitProj v χ⁻¹ (LaurentZetaSlot.twistedDiff₃ v α (dualSlice v ν Φ x)) t = 0 :=
    (Filter.eventually_all_finset S).mpr fun x _ => hslice x
  filter_upwards [hall] with t ht
  rw [unitProj_const_mul, unitProj_finset_sum v χ⁻¹ hχ' S _ hlc t]
  exact mul_eq_zero_of_right c (Finset.sum_eq_zero fun x hx => ht x hx)
end WeylTranslateZeta
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_eventually_threefold_twistedDifference_dualJacquetValueFn_eq_zero.LaurentZetaSlot P2MW.S_LanglandsTunnell_CubicInduction_eventually_threefold_twistedDifference_dualJacquetValueFn_eq_zero.WeylTranslateZeta"
end
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_eventually_threefold_twistedDifference_dualJacquetValueFn_eq_zero.LaurentZetaSlot P2MW.S_LanglandsTunnell_CubicInduction_eventually_threefold_twistedDifference_dualJacquetValueFn_eq_zero.WeylTranslateZeta"

open IsDedekindDomain NumberField LanglandsTunnell.TateLocal MeasureTheory
open WeylTranslateZeta

open LanglandsTunnell.CubicInduction in

theorem solution
    (v : HeightOneSpectrum (𝓞 ℚ))
    (ν : Fin 3 → ((v.adicCompletion ℚ)ˣ →* ℂˣ)) (hν : ∀ i, IsLocallyConstant (ν i))
    (Φ : (Fin 3 → v.adicCompletion ℚ) → ℂ) (hΦl : IsLocallyConstant Φ) (hΦc : HasCompactSupport Φ)
    (D : ℂ → (v.adicCompletion ℚ → ℂ) → v.adicCompletion ℚ → ℂ)
    (hD : ∀ (α : ℂ) (f : v.adicCompletion ℚ → ℂ) (a : v.adicCompletion ℚ),
      D α f a = f a - α * f (a / (NumberField.AdelicLevel.uniformizerUnit ℚ v : v.adicCompletion ℚ))) :
    letI := localBorel ℚ v
    (∀ x : v.adicCompletion ℚ, ∀ F : v.adicCompletion ℚ → ℂ, F 0 = 0 →
      (∀ a : (v.adicCompletion ℚ)ˣ,
        F a = jacquetValue v (gl3AmbientRightTranslate (R := ℂ)
            (longWeyl3 * transposeInv3 (iotaGL (diagUnitGL2 a) * lowerUnipotent21 x * (weylPrime3 * transposeInv3 1)) *
              antidiagonal3 v)
            (cellSectionOf v ν Φ)) * ((modulus (a : v.adicCompletion ℚ) : ℝ) : ℂ)⁻¹) →
      ∀ᶠ t in nhds (0 : v.adicCompletion ℚ),
        D ((((ν 0) (NumberField.AdelicLevel.uniformizerUnit ℚ v))⁻¹ : ℂˣ) : ℂ)
          (D ((((ν 1) (NumberField.AdelicLevel.uniformizerUnit ℚ v))⁻¹ : ℂˣ) : ℂ)
            (D ((((ν 2) (NumberField.AdelicLevel.uniformizerUnit ℚ v))⁻¹ : ℂˣ) : ℂ) F)) t = 0) ∧
      ∀ χ : (v.adicCompletion ℚ)ˣ →* ℂˣ, IsLocallyConstant χ → ∀ c : Fin 3 → ℂ,
        (∀ i, HasConductorExponentAt ℚ v (ν i * χ)⁻¹ 0 →
          c i * (χ⁻¹ (NumberField.AdelicLevel.uniformizerUnit ℚ v) : ℂ) =
            ((ν i * χ)⁻¹ (NumberField.AdelicLevel.uniformizerUnit ℚ v) : ℂ)) →
        (∀ i, ¬ HasConductorExponentAt ℚ v (ν i * χ)⁻¹ 0 → c i = 0) →
        ∀ G : v.adicCompletion ℚ → ℂ, G 0 = 0 →
          (∀ a : (v.adicCompletion ℚ)ˣ,
            G a = (∫ x : v.adicCompletion ℚ, jacquetValue v (gl3AmbientRightTranslate (R := ℂ)
                  (longWeyl3 *
                    transposeInv3 (iotaGL (diagUnitGL2 a) * lowerUnipotent21 x * (weylPrime3 * transposeInv3 1)) *
                  antidiagonal3 v)
                (cellSectionOf v ν Φ)) ∂(selfDualHaarAt ℚ v)) * ((modulus (a : v.adicCompletion ℚ) : ℝ) : ℂ)⁻¹) →
          ∀ᶠ t in nhds (0 : v.adicCompletion ℚ),
            D (c 0) (D (c 1) (D (c 2) (fun a =>
              (∫ w in {x : v.adicCompletion ℚ | Valued.v x = 1}, G (a * w) * charExt χ⁻¹ w
                  ∂(mulMeasure (selfDualHaarAt ℚ v))) /
                (((mulMeasure (selfDualHaarAt ℚ v)).real {x : v.adicCompletion ℚ | Valued.v x = 1} : ℝ) : ℂ)))) t =
              0 := by
  obtain rfl : D = LaurentZetaSlot.twistedDiff v :=
    funext fun α => funext fun f => funext fun a => (hD α f a).trans rfl
  obtain ⟨h1, h2⟩ :=
    (⟨fun x => eventually_twistedDiff₃_dualSlice_eq_zero v ν Φ hν hΦl hΦc x,
      fun χ hχ α hα => eventually_twistedDiff₃_unitProj_dualFn_eq_zero v ν Φ hν hΦl hΦc χ hχ α hα⟩ :
      (∀ x, ∀ᶠ t in nhds (0 : v.adicCompletion ℚ), LaurentZetaSlot.twistedDiff₃ v
          (fun i => ((((ν i) (NumberField.AdelicLevel.uniformizerUnit ℚ v))⁻¹ : ℂˣ) : ℂ)) (dualSlice v ν Φ x) t = 0) ∧
        ∀ (χ : (v.adicCompletion ℚ)ˣ →* ℂˣ), IsLocallyConstant χ → ∀ α : Fin 3 → ℂ,
          (∀ i, α i * ((χ⁻¹ (NumberField.AdelicLevel.uniformizerUnit ℚ v) : ℂˣ) : ℂ) =
            LaurentZetaSlot.slotScalar v (ν i * χ)⁻¹) →
          ∀ᶠ t in nhds (0 : v.adicCompletion ℚ),
            LaurentZetaSlot.twistedDiff₃ v α (LaurentZetaSlot.unitProj v χ⁻¹ (dualFn v ν Φ)) t = 0)
  refine ⟨fun x F hF0 hFa => ?_, fun χ hχ c hc₀ hc₁ G hG0 hGa => ?_⟩
  · obtain rfl : F = dualSlice v ν Φ x := by
      funext t
      by_cases ht : t = 0
      · rw [ht, hF0, dualSlice_zero]
      · have h := hFa (Units.mk0 t ht)
        simp only [Units.val_mk0] at h
        rw [h, dualSlice, dif_neg ht]
        rfl
    simpa only [LaurentZetaSlot.twistedDiff₃] using h1 x
  · have hα : ∀ i, c i * ((χ⁻¹ (NumberField.AdelicLevel.uniformizerUnit ℚ v) : ℂˣ) : ℂ) =
        LaurentZetaSlot.slotScalar v (ν i * χ)⁻¹ := by
      intro i
      by_cases h : HasConductorExponentAt ℚ v (ν i * χ)⁻¹ 0
      · rw [LaurentZetaSlot.slotScalar, if_pos h]
        exact hc₀ i h
      · rw [LaurentZetaSlot.slotScalar, if_neg h, hc₁ i h, zero_mul]
    obtain rfl : G = dualFn v ν Φ := by
      funext t
      by_cases ht : t = 0
      · rw [ht, hG0, dualFn_zero]
      · have h := hGa (Units.mk0 t ht)
        have h' := dualFn_coe_units v ν Φ (Units.mk0 t ht)
        simp only [Units.val_mk0] at h h'
        rw [h, h']
        rfl
    have h__af := h2 χ hχ c hα
    simp only [LaurentZetaSlot.twistedDiff₃, LaurentZetaSlot.unitProj, LaurentZetaSlot.unitShell] at h__af
    exact h__af

end S_LanglandsTunnell_CubicInduction_eventually_threefold_twistedDifference_dualJacquetValueFn_eq_zero
end P2MW
export P2MW.S_LanglandsTunnell_CubicInduction_eventually_threefold_twistedDifference_dualJacquetValueFn_eq_zero (solution)
