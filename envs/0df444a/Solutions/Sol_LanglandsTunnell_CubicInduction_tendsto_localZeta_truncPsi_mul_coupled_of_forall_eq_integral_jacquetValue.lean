-- Prove2me | solution 1 for LanglandsTunnell.CubicInduction.tendsto_localZeta_truncPsi_mul_coupled_of_forall_eq_integral_jacquetValue
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.670037+00:00
-- url     : https://prove2.me/submissions/894caef4-d787-5028-b280-27cd742c6142

import Definitions.Def_LanglandsTunnell_CubicInduction_LocalZeta31
import Definitions.Def_LanglandsTunnell_CubicInduction_JacquetWhittaker
import Definitions.Def_LanglandsTunnell_StandardLocalConstantsAt
import Definitions.Def_LanglandsTunnell_TateLocalZeta
import Definitions.Def_LanglandsTunnell_CubicInduction_PrincipalSeries3
import Definitions.Def_LanglandsTunnell_CubicInduction_IotaTorus
import Definitions.Def_LanglandsTunnell_CubicInduction_GlobalZeta31
import Theorems.Thm_LanglandsTunnell_TateLocal_modulus_adicCompletion_eq_nnnorm
import Theorems.Thm_LanglandsTunnell_TateLocal_psiLocal_ne_one
import Theorems.Thm_LanglandsTunnell_CubicInduction_exists_forall_le_integrableOn_and_jacquetTruncated3_eq_of_cellSectionOf
import Theorems.Thm_LanglandsTunnell_CubicInduction_exists_forall_norm_setIntegral_annulus_setIntegral_compl_ball_jacquetWindow_le
import Theorems.Thm_LanglandsTunnell_CubicInduction_exists_forall_norm_dualZetaRemainder_outside_annulus_le
import Theorems.Thm_LanglandsTunnell_CubicInduction_localZeta_truncPsi_mul_coupled_eq_localZeta_of_forall_eq_integral_jacquetWindow
import Theorems.Thm_LanglandsTunnell_CubicInduction_tendsto_setIntegral_annulus_setIntegral_ball_jacquetWindow_sub_jacquetValue
import Theorems.Thm_LanglandsTunnell_CubicInduction_localZeta_primedDual_eq_pieces_add_setIntegral_annulus_of_forall_eq_zero
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Algebra.Polynomial.Eval.Defs
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

p2m_attr_erase "ext" "IsDedekindDomain.HeightOneSpectrum.adicCompletion.ext"
p2m_attr_erase "ext" "NumberField.InfinitePlace.Completion.ext"
namespace P2MW.S_LanglandsTunnell_CubicInduction_tendsto_localZeta_truncPsi_mul_coupled_of_forall_eq_integral_jacquetValue
p2m_attr_erase "instance" "instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions instCountableOfNumberField_definitions IsDedekindDomain.HeightOneSpectrum.Extension.instAlgebraSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnder IsDedekindDomain.HeightOneSpectrum.Extension.instAlgebraSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnder_1 IsDedekindDomain.HeightOneSpectrum.instMulActionHomClassAlgHomTensorProductAdicCompletionForallValEqUnder_definitions IsDedekindDomain.HeightOneSpectrum.Extension.instAlgebraAdicCompletionValEqUnder IsDedekindDomain.HeightOneSpectrum.adicCompletion.instFiniteForallValEqUnderOfFiniteDimensional_definitions IsDedekindDomain.HeightOneSpectrum.instIsBiscalarSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersTensorProductCoeAlgHomTensorAdicCompletionIntegersTo IsDedekindDomain.HeightOneSpectrum.Extension.instContinuousSMulAdicCompletionValEqUnder IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsModuleTopology IsDedekindDomain.HeightOneSpectrum.Extension.instFiniteSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnderOfFiniteDimensional IsDedekindDomain.HeightOneSpectrum.adicCompletion.instFiniteValEqUnderOfFiniteDimensional_definitions instIsBiscalarTensorProductCoeAlgHomBaseChange_of_algebraMap IsDedekindDomain.HeightOneSpectrum.instIsScalarTowerSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnder_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsModuleTopologyPi Submodule.instIsTopologicalModuleSubtypeMem Pi.instTopologicalModule IsTopologicalModule.toContinuousSMul IsTopologicalModule.toContinuousAdd instFunLike SemialgHomClass.toSemilinearMapClass instCoeTCSemialgHom SemialgHomClass.toRingHomClass SemialgHomClass.instSemialgHom"
p2m_attr_erase "simp" "SemialgHom.baseChange_of_algebraMap_tmul_left SemialgHom.baseChangeRightOfAlgebraMap_apply Pi.semialgHomPi_apply Pi.semialgHom_apply Module.Basis.rightBaseChange_apply LinearEquiv.coe_mulLeft LinearEquiv.coe_mulRight WithVal.semialgebraMap_toFun_ofVal Module.Basis.rightBaseChange_repr IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers.tensorCoe_tmul IsDedekindDomain.HeightOneSpectrum.tensorAdicCompletionIntegersTo_tmul SemialgHom.baseChangeRightOfAlgebraMap_coe IsDedekindDomain.HeightOneSpectrum.adicCompletion.integerBaseChangeLinearEquiv_tmul_apply SemialgHom.baseChange_of_algebraMap_tmul_right IsLocalization.map_moduleTensorEquiv_symm_tmul IsLocalization.leftModuleTensorEquiv_apply IsLocalization.moduleLid_symm_apply IsLocalization.leftModuleTensorEquiv_symm_apply IsLocalization.map_moduleTensorEquiv_tmul IsModuleTopology.continuousLinearEquiv_apply AlgEquiv.extendScalars_symm_apply IsModuleTopology.Module.Basis.equivFun_homeo_symm_apply IsModuleTopology.Module.Basis.equivFun_homeo_apply IsModuleTopology.continuousAlgEquivOfIsBiscalar_apply AlgEquiv.extendScalars_apply IsModuleTopology.continuousLinearEquiv_symm_apply SemialgHom.restrictScalars_toFun SemialgHom.mk.sizeOf_spec SemialgHom.mk.injEq SemialgHom.coe_coe coe_mk TensorProduct.RightActions.smul_def TensorProduct.RightActions.Module.TensorProduct.comm_symm_apply_tmul TensorProduct.RightActions.LinearMap.baseChange_id TensorProduct.RightActions.algebraMap_eval TensorProduct.RightActions.Module.TensorProduct.comm_apply_tmul TensorProduct.RightActions.Algebra.TensorProduct.comm_symm_apply_tmul TensorProduct.RightActions.Algebra.TensorProduct.comm_apply_tmul LanglandsTunnell.CubicInduction.translateRepStep_apply_coe LanglandsTunnell.CubicInduction.translateFn_apply"

set_option autoImplicit false

section Part2

set_option autoImplicit false

open IsDedekindDomain NumberField MeasureTheory
open scoped NNReal ENNReal Pointwise

namespace LanglandsTunnell
p2m_export "LanglandsTunnell" "TateLocal.localBorel TateLocal.borelSpace_localBorel CubicInduction.exists_forall_norm_setIntegral_annulus_setIntegral_compl_ball_jacquetWindow_le CubicInduction.exists_forall_norm_dualZetaRemainder_outside_annulus_le CubicInduction.localZeta_truncPsi_mul_coupled_eq_localZeta_of_forall_eq_integral_jacquetWindow CubicInduction.tendsto_setIntegral_annulus_setIntegral_ball_jacquetWindow_sub_jacquetValue CubicInduction.localZeta_primedDual_eq_pieces_add_setIntegral_annulus_of_forall_eq_zero"
namespace TateLocal
p2m_export "LanglandsTunnell.TateLocal" "addCharLevel localBorel borelSpace_localBorel integersPositiveCompacts coe_integersPositiveCompacts selfDualHaarAt modulus charExt charExt_zero mulMeasure localZeta modulus_adicCompletion_eq_nnnorm psiLocal_ne_one"
p2m_open "LanglandsTunnell.TateLocal LanglandsTunnell"

variable (K : Type) [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))

section Scaling

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

end LanglandsTunnell.TateLocal
end Part2

section Part1

set_option autoImplicit false

open NumberField NumberField.AdelicLevel IsDedekindDomain MeasureTheory
p2m_open "LanglandsTunnell.TateLocal P2MW.S_LanglandsTunnell_CubicInduction_tendsto_localZeta_truncPsi_mul_coupled_of_forall_eq_integral_jacquetValue.LanglandsTunnell.TateLocal"
open scoped NNReal ENNReal

namespace IsLaurentInQPow

variable {q : ℂ}

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
  exact LanglandsTunnell.TateLocal.isAddHaarMeasure_selfDualHaarAt ℚ v

private theorem sFinite_mulMeasure_selfDualHaarAt' : SFinite (mulMeasure (selfDualHaarAt ℚ v)) := by
  exact LanglandsTunnell.TateLocal.sFinite_mulMeasure_selfDualHaarAt ℚ v

attribute [local instance] sFinite_mulMeasure_selfDualHaarAt'

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

private theorem
    mulMeasure_unitShell : mulMeasure (selfDualHaarAt ℚ v) (unitShell v) = selfDualHaarAt ℚ v (unitShell v) := by
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

private theorem exists_mem_shell {x : v.adicCompletion ℚ} (hx : x ≠ 0) : ∃ j : ℤ, x ∈ shell v j := by
  have hv : Valued.v x ≠ 0 := (Valuation.ne_zero_iff _).mpr hx
  refine ⟨-WithZero.log (Valued.v x), ?_⟩
  show Valued.v x = WithZero.exp (- -WithZero.log (Valued.v x))
  rw [neg_neg, WithZero.exp_log hv]

private theorem coe_modulus_eq_of_mem_shell {j : ℤ} {x : v.adicCompletion ℚ} (hx : x ∈ shell v j) :
    (modulus x : ℝ) = (Ideal.absNorm v.asIdeal : ℝ) ^ (-j) := by
  rw [modulus_eq_of_mem_shell v hx, NNReal.coe_zpow, NNReal.coe_natCast]

end LaurentZetaSlot
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_tendsto_localZeta_truncPsi_mul_coupled_of_forall_eq_integral_jacquetValue.LaurentZetaSlot"
end Part1
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_tendsto_localZeta_truncPsi_mul_coupled_of_forall_eq_integral_jacquetValue.LaurentZetaSlot"

section Part3

set_option autoImplicit false

open Matrix IsDedekindDomain NumberField

namespace LanglandsTunnell
p2m_export "LanglandsTunnell" "TateLocal.localBorel TateLocal.borelSpace_localBorel CubicInduction.exists_forall_norm_setIntegral_annulus_setIntegral_compl_ball_jacquetWindow_le CubicInduction.exists_forall_norm_dualZetaRemainder_outside_annulus_le CubicInduction.localZeta_truncPsi_mul_coupled_eq_localZeta_of_forall_eq_integral_jacquetWindow CubicInduction.tendsto_setIntegral_annulus_setIntegral_ball_jacquetWindow_sub_jacquetValue CubicInduction.localZeta_primedDual_eq_pieces_add_setIntegral_annulus_of_forall_eq_zero"
namespace CubicInduction
p2m_export "LanglandsTunnell.CubicInduction" "lowerUnipotent21 longWeyl3 longWeyl3_coe weylPrime3 weylPrime3_coe transposeInv3_weylPrime3 transposeInv3_lowerUnipotent21 gl3AmbientRightTranslate gl3AmbientRightTranslate_apply transposeInv3 upperUnipotent3 upperUnipotent3_coe embedMat2 iotaGL coe_iotaGL LocalGL3 diagUnitGL2 coe_diagUnitGL2 unipotentBall3 mem_unipotentBall3_iff upperUnipotent3_mul_upperUnipotent3 jacquetHaar3 jacquetTruncated3 jacquetLevel jacquetValue jacquetTruncated3_eq_jacquetValue jacquetLevel_le bigCell3 mem_bigCell3_iff cellSectionOf cellSectionOf_apply_of_mem cellSectionOf_apply_of_notMem gl3Entry cornerEntry lowerMinor outerMinor gl3Det cellRatio cellValue antidiagonal3 antidiagonal3_coe eventually_valued_eq exists_forall_le_integrableOn_and_jacquetTruncated3_eq_of_cellSectionOf exists_forall_norm_setIntegral_annulus_setIntegral_compl_ball_jacquetWindow_le exists_forall_norm_dualZetaRemainder_outside_annulus_le localZeta_truncPsi_mul_coupled_eq_localZeta_of_forall_eq_integral_jacquetWindow tendsto_setIntegral_annulus_setIntegral_ball_jacquetWindow_sub_jacquetValue localZeta_primedDual_eq_pieces_add_setIntegral_annulus_of_forall_eq_zero"
p2m_open "LanglandsTunnell.CubicInduction LanglandsTunnell"

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
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_tendsto_localZeta_truncPsi_mul_coupled_of_forall_eq_integral_jacquetValue.LaurentZetaSlot"

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
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_tendsto_localZeta_truncPsi_mul_coupled_of_forall_eq_integral_jacquetValue.LaurentZetaSlot"

end LanglandsTunnell.CubicInduction
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_tendsto_localZeta_truncPsi_mul_coupled_of_forall_eq_integral_jacquetValue.LaurentZetaSlot"
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_tendsto_localZeta_truncPsi_mul_coupled_of_forall_eq_integral_jacquetValue.LaurentZetaSlot"
end Part3
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_tendsto_localZeta_truncPsi_mul_coupled_of_forall_eq_integral_jacquetValue.LaurentZetaSlot"

section Part4

set_option autoImplicit false

p2m_open "Matrix IsDedekindDomain NumberField LanglandsTunnell.TateLocal P2MW.S_LanglandsTunnell_CubicInduction_tendsto_localZeta_truncPsi_mul_coupled_of_forall_eq_integral_jacquetValue.LanglandsTunnell.TateLocal"

namespace LanglandsTunnell
p2m_export "LanglandsTunnell" "TateLocal.localBorel TateLocal.borelSpace_localBorel CubicInduction.exists_forall_norm_setIntegral_annulus_setIntegral_compl_ball_jacquetWindow_le CubicInduction.exists_forall_norm_dualZetaRemainder_outside_annulus_le CubicInduction.localZeta_truncPsi_mul_coupled_eq_localZeta_of_forall_eq_integral_jacquetWindow CubicInduction.tendsto_setIntegral_annulus_setIntegral_ball_jacquetWindow_sub_jacquetValue CubicInduction.localZeta_primedDual_eq_pieces_add_setIntegral_annulus_of_forall_eq_zero"
namespace CubicInduction
p2m_export "LanglandsTunnell.CubicInduction" "lowerUnipotent21 longWeyl3 longWeyl3_coe weylPrime3 weylPrime3_coe transposeInv3_weylPrime3 transposeInv3_lowerUnipotent21 gl3AmbientRightTranslate gl3AmbientRightTranslate_apply transposeInv3 upperUnipotent3 upperUnipotent3_coe embedMat2 iotaGL coe_iotaGL LocalGL3 diagUnitGL2 coe_diagUnitGL2 unipotentBall3 mem_unipotentBall3_iff upperUnipotent3_mul_upperUnipotent3 jacquetHaar3 jacquetTruncated3 jacquetLevel jacquetValue jacquetTruncated3_eq_jacquetValue jacquetLevel_le bigCell3 mem_bigCell3_iff cellSectionOf cellSectionOf_apply_of_mem cellSectionOf_apply_of_notMem gl3Entry cornerEntry lowerMinor outerMinor gl3Det cellRatio cellValue antidiagonal3 antidiagonal3_coe eventually_valued_eq exists_forall_le_integrableOn_and_jacquetTruncated3_eq_of_cellSectionOf exists_forall_norm_setIntegral_annulus_setIntegral_compl_ball_jacquetWindow_le exists_forall_norm_dualZetaRemainder_outside_annulus_le localZeta_truncPsi_mul_coupled_eq_localZeta_of_forall_eq_integral_jacquetWindow tendsto_setIntegral_annulus_setIntegral_ball_jacquetWindow_sub_jacquetValue localZeta_primedDual_eq_pieces_add_setIntegral_annulus_of_forall_eq_zero"
p2m_open "LanglandsTunnell.CubicInduction LanglandsTunnell"

variable (v : HeightOneSpectrum (𝓞 ℚ))

section DualPoint

private noncomputable def
    dualCellPoint (α β γ : v.adicCompletion ℚ) (a : (v.adicCompletion ℚ)ˣ) (x : v.adicCompletion ℚ) :
    LocalGL3 v :=
  antidiagonal3 v * upperUnipotent3 α β γ *
    (longWeyl3 * transposeInv3 (iotaGL (diagUnitGL2 a) * lowerUnipotent21 x * (weylPrime3 * transposeInv3 1)) *
      antidiagonal3 v)

end DualPoint
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_tendsto_localZeta_truncPsi_mul_coupled_of_forall_eq_integral_jacquetValue.LaurentZetaSlot"

end LanglandsTunnell.CubicInduction
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_tendsto_localZeta_truncPsi_mul_coupled_of_forall_eq_integral_jacquetValue.LaurentZetaSlot"
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_tendsto_localZeta_truncPsi_mul_coupled_of_forall_eq_integral_jacquetValue.LaurentZetaSlot"
end Part4
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_tendsto_localZeta_truncPsi_mul_coupled_of_forall_eq_integral_jacquetValue.LaurentZetaSlot"

section Part5

set_option autoImplicit false

open MeasureTheory
open IsDedekindDomain
open NumberField
p2m_open "LanglandsTunnell.TateLocal P2MW.S_LanglandsTunnell_CubicInduction_tendsto_localZeta_truncPsi_mul_coupled_of_forall_eq_integral_jacquetValue.LanglandsTunnell.TateLocal"
open NumberField.StandardAddChar
open scoped Topology

namespace LanglandsTunnell
p2m_export "LanglandsTunnell" "TateLocal.localBorel TateLocal.borelSpace_localBorel CubicInduction.exists_forall_norm_setIntegral_annulus_setIntegral_compl_ball_jacquetWindow_le CubicInduction.exists_forall_norm_dualZetaRemainder_outside_annulus_le CubicInduction.localZeta_truncPsi_mul_coupled_eq_localZeta_of_forall_eq_integral_jacquetWindow CubicInduction.tendsto_setIntegral_annulus_setIntegral_ball_jacquetWindow_sub_jacquetValue CubicInduction.localZeta_primedDual_eq_pieces_add_setIntegral_annulus_of_forall_eq_zero"
namespace CubicInduction
p2m_export "LanglandsTunnell.CubicInduction" "lowerUnipotent21 longWeyl3 longWeyl3_coe weylPrime3 weylPrime3_coe transposeInv3_weylPrime3 transposeInv3_lowerUnipotent21 gl3AmbientRightTranslate gl3AmbientRightTranslate_apply transposeInv3 upperUnipotent3 upperUnipotent3_coe embedMat2 iotaGL coe_iotaGL LocalGL3 diagUnitGL2 coe_diagUnitGL2 unipotentBall3 mem_unipotentBall3_iff upperUnipotent3_mul_upperUnipotent3 jacquetHaar3 jacquetTruncated3 jacquetLevel jacquetValue jacquetTruncated3_eq_jacquetValue jacquetLevel_le bigCell3 mem_bigCell3_iff cellSectionOf cellSectionOf_apply_of_mem cellSectionOf_apply_of_notMem gl3Entry cornerEntry lowerMinor outerMinor gl3Det cellRatio cellValue antidiagonal3 antidiagonal3_coe eventually_valued_eq exists_forall_le_integrableOn_and_jacquetTruncated3_eq_of_cellSectionOf exists_forall_norm_setIntegral_annulus_setIntegral_compl_ball_jacquetWindow_le exists_forall_norm_dualZetaRemainder_outside_annulus_le localZeta_truncPsi_mul_coupled_eq_localZeta_of_forall_eq_integral_jacquetWindow tendsto_setIntegral_annulus_setIntegral_ball_jacquetWindow_sub_jacquetValue localZeta_primedDual_eq_pieces_add_setIntegral_annulus_of_forall_eq_zero"
p2m_open "LanglandsTunnell.CubicInduction LanglandsTunnell"

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

private theorem
    valued_le_of_norm_le_zpow {x : v.adicCompletion ℚ} {n : ℤ} (hx : ‖x‖ ≤ (Ideal.absNorm v.asIdeal : ℝ) ^ n) :
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

private theorem modulus_real_eq_norm (x : v.adicCompletion ℚ) : (modulus x : ℝ) = ‖x‖ := by
  rw [modulus_adicCompletion_eq_nnnorm ℚ v x, coe_nnnorm]

private theorem one_lt_absNorm_real : (1 : ℝ) < (Ideal.absNorm v.asIdeal : ℝ) := by
  exact_mod_cast NumberField.HeightOneSpectrum.one_lt_absNorm (v := v)

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
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_tendsto_localZeta_truncPsi_mul_coupled_of_forall_eq_integral_jacquetValue.LaurentZetaSlot"

end LanglandsTunnell.CubicInduction
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_tendsto_localZeta_truncPsi_mul_coupled_of_forall_eq_integral_jacquetValue.LaurentZetaSlot"
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_tendsto_localZeta_truncPsi_mul_coupled_of_forall_eq_integral_jacquetValue.LaurentZetaSlot"
end Part5
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_tendsto_localZeta_truncPsi_mul_coupled_of_forall_eq_integral_jacquetValue.LaurentZetaSlot"

section Part6

set_option autoImplicit false

open MeasureTheory
open IsDedekindDomain
open NumberField
p2m_open "LanglandsTunnell.TateLocal P2MW.S_LanglandsTunnell_CubicInduction_tendsto_localZeta_truncPsi_mul_coupled_of_forall_eq_integral_jacquetValue.LanglandsTunnell.TateLocal"
open NumberField.StandardAddChar
open scoped Topology

namespace LanglandsTunnell
p2m_export "LanglandsTunnell" "TateLocal.localBorel TateLocal.borelSpace_localBorel CubicInduction.exists_forall_norm_setIntegral_annulus_setIntegral_compl_ball_jacquetWindow_le CubicInduction.exists_forall_norm_dualZetaRemainder_outside_annulus_le CubicInduction.localZeta_truncPsi_mul_coupled_eq_localZeta_of_forall_eq_integral_jacquetWindow CubicInduction.tendsto_setIntegral_annulus_setIntegral_ball_jacquetWindow_sub_jacquetValue CubicInduction.localZeta_primedDual_eq_pieces_add_setIntegral_annulus_of_forall_eq_zero"
namespace CubicInduction
p2m_export "LanglandsTunnell.CubicInduction" "lowerUnipotent21 longWeyl3 longWeyl3_coe weylPrime3 weylPrime3_coe transposeInv3_weylPrime3 transposeInv3_lowerUnipotent21 gl3AmbientRightTranslate gl3AmbientRightTranslate_apply transposeInv3 upperUnipotent3 upperUnipotent3_coe embedMat2 iotaGL coe_iotaGL LocalGL3 diagUnitGL2 coe_diagUnitGL2 unipotentBall3 mem_unipotentBall3_iff upperUnipotent3_mul_upperUnipotent3 jacquetHaar3 jacquetTruncated3 jacquetLevel jacquetValue jacquetTruncated3_eq_jacquetValue jacquetLevel_le bigCell3 mem_bigCell3_iff cellSectionOf cellSectionOf_apply_of_mem cellSectionOf_apply_of_notMem gl3Entry cornerEntry lowerMinor outerMinor gl3Det cellRatio cellValue antidiagonal3 antidiagonal3_coe eventually_valued_eq exists_forall_le_integrableOn_and_jacquetTruncated3_eq_of_cellSectionOf exists_forall_norm_setIntegral_annulus_setIntegral_compl_ball_jacquetWindow_le exists_forall_norm_dualZetaRemainder_outside_annulus_le localZeta_truncPsi_mul_coupled_eq_localZeta_of_forall_eq_integral_jacquetWindow tendsto_setIntegral_annulus_setIntegral_ball_jacquetWindow_sub_jacquetValue localZeta_primedDual_eq_pieces_add_setIntegral_annulus_of_forall_eq_zero"
p2m_open "LanglandsTunnell.CubicInduction LanglandsTunnell"

section DualTorusValues

variable (v : HeightOneSpectrum (𝓞 ℚ))
variable (ν : Fin 3 → ((v.adicCompletion ℚ)ˣ →* ℂˣ)) (Φ : (Fin 3 → v.adicCompletion ℚ) → ℂ)

private noncomputable def dualPoint (a : (v.adicCompletion ℚ)ˣ) (x : v.adicCompletion ℚ) : LocalGL3 v :=
  longWeyl3 * transposeInv3 (iotaGL (diagUnitGL2 a) * lowerUnipotent21 x * (weylPrime3 * transposeInv3 1)) *
    antidiagonal3 v

private noncomputable def dualTranslate (a : (v.adicCompletion ℚ)ˣ) (x : v.adicCompletion ℚ) : LocalGL3 v → ℂ :=
  gl3AmbientRightTranslate (R := ℂ) (dualPoint v a x) (cellSectionOf v ν Φ)

private theorem dualTranslate_apply (a : (v.adicCompletion ℚ)ˣ) (x : v.adicCompletion ℚ) (h : LocalGL3 v) :
    dualTranslate v ν Φ a x h = cellSectionOf v ν Φ (h * dualPoint v a x) :=
  rfl

open Classical in
private noncomputable def dualFn : v.adicCompletion ℚ → ℂ := fun t =>
  letI := localBorel ℚ v
  if h : t = 0 then 0 else
    (∫ x : v.adicCompletion ℚ, jacquetValue v (dualTranslate v ν Φ (Units.mk0 t h) x) ∂(selfDualHaarAt ℚ v)) *
      ((modulus t : ℝ) : ℂ)⁻¹

private theorem dualFn_coe_units (a : (v.adicCompletion ℚ)ˣ) :
    letI := localBorel ℚ v
    dualFn v ν Φ a =
      (∫ x : v.adicCompletion ℚ, jacquetValue v (dualTranslate v ν Φ a x) ∂(selfDualHaarAt ℚ v)) *
        ((modulus (a : v.adicCompletion ℚ) : ℝ) : ℂ)⁻¹ := by
  simp [dualFn, a.ne_zero]

end DualTorusValues
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_tendsto_localZeta_truncPsi_mul_coupled_of_forall_eq_integral_jacquetValue.LaurentZetaSlot"

end LanglandsTunnell.CubicInduction
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_tendsto_localZeta_truncPsi_mul_coupled_of_forall_eq_integral_jacquetValue.LaurentZetaSlot"
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_tendsto_localZeta_truncPsi_mul_coupled_of_forall_eq_integral_jacquetValue.LaurentZetaSlot"
end Part6
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_tendsto_localZeta_truncPsi_mul_coupled_of_forall_eq_integral_jacquetValue.LaurentZetaSlot"

section Part7
set_option autoImplicit false

open MeasureTheory
open IsDedekindDomain
open NumberField
p2m_open "LanglandsTunnell.TateLocal P2MW.S_LanglandsTunnell_CubicInduction_tendsto_localZeta_truncPsi_mul_coupled_of_forall_eq_integral_jacquetValue.LanglandsTunnell.TateLocal"
open NumberField.StandardAddChar

namespace LanglandsTunnell
p2m_export "LanglandsTunnell" "TateLocal.localBorel TateLocal.borelSpace_localBorel CubicInduction.exists_forall_norm_setIntegral_annulus_setIntegral_compl_ball_jacquetWindow_le CubicInduction.exists_forall_norm_dualZetaRemainder_outside_annulus_le CubicInduction.localZeta_truncPsi_mul_coupled_eq_localZeta_of_forall_eq_integral_jacquetWindow CubicInduction.tendsto_setIntegral_annulus_setIntegral_ball_jacquetWindow_sub_jacquetValue CubicInduction.localZeta_primedDual_eq_pieces_add_setIntegral_annulus_of_forall_eq_zero"
namespace CubicInduction
p2m_export "LanglandsTunnell.CubicInduction" "lowerUnipotent21 longWeyl3 longWeyl3_coe weylPrime3 weylPrime3_coe transposeInv3_weylPrime3 transposeInv3_lowerUnipotent21 gl3AmbientRightTranslate gl3AmbientRightTranslate_apply transposeInv3 upperUnipotent3 upperUnipotent3_coe embedMat2 iotaGL coe_iotaGL LocalGL3 diagUnitGL2 coe_diagUnitGL2 unipotentBall3 mem_unipotentBall3_iff upperUnipotent3_mul_upperUnipotent3 jacquetHaar3 jacquetTruncated3 jacquetLevel jacquetValue jacquetTruncated3_eq_jacquetValue jacquetLevel_le bigCell3 mem_bigCell3_iff cellSectionOf cellSectionOf_apply_of_mem cellSectionOf_apply_of_notMem gl3Entry cornerEntry lowerMinor outerMinor gl3Det cellRatio cellValue antidiagonal3 antidiagonal3_coe eventually_valued_eq exists_forall_le_integrableOn_and_jacquetTruncated3_eq_of_cellSectionOf exists_forall_norm_setIntegral_annulus_setIntegral_compl_ball_jacquetWindow_le exists_forall_norm_dualZetaRemainder_outside_annulus_le localZeta_truncPsi_mul_coupled_eq_localZeta_of_forall_eq_integral_jacquetWindow tendsto_setIntegral_annulus_setIntegral_ball_jacquetWindow_sub_jacquetValue localZeta_primedDual_eq_pieces_add_setIntegral_annulus_of_forall_eq_zero"
p2m_open "LanglandsTunnell.CubicInduction LanglandsTunnell"

section RightUnipotent

variable (v : HeightOneSpectrum (𝓞 ℚ))
variable (ν : Fin 3 → ((v.adicCompletion ℚ)ˣ →* ℂˣ)) (Φ : (Fin 3 → v.adicCompletion ℚ) → ℂ)

private theorem gl3Entry_mul_upperUnipotent3_zero (h : LocalGL3 v) (x y z : v.adicCompletion ℚ) (i : Fin 3) :
    gl3Entry v (h * upperUnipotent3 x y z) i 0 = gl3Entry v h i 0 := by
  simp [gl3Entry, Units.val_mul, Matrix.mul_apply, Fin.sum_univ_three]

private theorem gl3Entry_mul_upperUnipotent3_one (h : LocalGL3 v) (x y z : v.adicCompletion ℚ) (i : Fin 3) :
    gl3Entry v (h * upperUnipotent3 x y z) i 1 = gl3Entry v h i 0 * x + gl3Entry v h i 1 := by
  simp [gl3Entry, Units.val_mul, Matrix.mul_apply, Fin.sum_univ_three]

private theorem gl3Entry_mul_upperUnipotent3_two (h : LocalGL3 v) (x y z : v.adicCompletion ℚ) (i : Fin 3) :
    gl3Entry v (h * upperUnipotent3 x y z) i 2 = gl3Entry v h i 0 * z + gl3Entry v h i 1 * y + gl3Entry v h i 2 := by
  simp [gl3Entry, Units.val_mul, Matrix.mul_apply, Fin.sum_univ_three]

private theorem cornerEntry_mul_upperUnipotent3 (h : LocalGL3 v) (x y z : v.adicCompletion ℚ) :
    cornerEntry v (h * upperUnipotent3 x y z) = cornerEntry v h := by
  unfold cornerEntry
  exact gl3Entry_mul_upperUnipotent3_zero v h x y z 2

private theorem lowerMinor_mul_upperUnipotent3 (h : LocalGL3 v) (x y z : v.adicCompletion ℚ) :
    lowerMinor v (h * upperUnipotent3 x y z) = lowerMinor v h := by
  simp only [lowerMinor, gl3Entry_mul_upperUnipotent3_zero, gl3Entry_mul_upperUnipotent3_one]
  ring

private theorem outerMinor_mul_upperUnipotent3 (h : LocalGL3 v) (x y z : v.adicCompletion ℚ) :
    outerMinor v (h * upperUnipotent3 x y z) = outerMinor v h + y * lowerMinor v h := by
  simp only [outerMinor, lowerMinor, gl3Entry_mul_upperUnipotent3_zero, gl3Entry_mul_upperUnipotent3_two]
  ring

private theorem gl3Det_mul_upperUnipotent3 (h : LocalGL3 v) (x y z : v.adicCompletion ℚ) :
    gl3Det v (h * upperUnipotent3 x y z) = gl3Det v h := by
  have hdet : (!![(1 : v.adicCompletion ℚ), x, z; 0, 1, y; 0, 0, 1]).det = 1 := by
    simp [Matrix.det_fin_three]
  rw [gl3Det, gl3Det, Units.val_mul, Matrix.det_mul, upperUnipotent3_coe, hdet, mul_one]

private theorem mul_upperUnipotent3_mem_bigCell3_iff (h : LocalGL3 v) (x y z : v.adicCompletion ℚ) :
    h * upperUnipotent3 x y z ∈ bigCell3 v ↔ h ∈ bigCell3 v := by
  simp only [mem_bigCell3_iff, cornerEntry_mul_upperUnipotent3, lowerMinor_mul_upperUnipotent3]

private theorem cellValue_mul_upperUnipotent3 (h : LocalGL3 v) (x y z : v.adicCompletion ℚ) :
    cellValue v ν (h * upperUnipotent3 x y z) = cellValue v ν h := by
  simp only [cellValue, gl3Det_mul_upperUnipotent3, lowerMinor_mul_upperUnipotent3, cornerEntry_mul_upperUnipotent3]

private theorem cellRatio_apply_zero (g : LocalGL3 v) : cellRatio v g 0 = gl3Entry v g 2 1 / cornerEntry v g := rfl

private theorem cellRatio_apply_one (g : LocalGL3 v) : cellRatio v g 1 = gl3Entry v g 2 2 / cornerEntry v g := rfl

private theorem cellRatio_apply_two (g : LocalGL3 v) : cellRatio v g 2 = outerMinor v g / lowerMinor v g := rfl

private theorem cellRatio_mul_upperUnipotent3 {h : LocalGL3 v} (hc : cornerEntry v h ≠ 0) (hl : lowerMinor v h ≠ 0)
    (x y z : v.adicCompletion ℚ) :
    cellRatio v (h * upperUnipotent3 x y z) =
      ![cellRatio v h 0 + x, cellRatio v h 1 + (z + y * cellRatio v h 0), cellRatio v h 2 + y] := by
  have hc' : gl3Entry v h 2 0 ≠ 0 := hc
  ext i
  match i with
  | 0 =>
      change cellRatio v (h * upperUnipotent3 x y z) 0 = cellRatio v h 0 + x
      rw [cellRatio_apply_zero, cellRatio_apply_zero, cornerEntry_mul_upperUnipotent3,
        gl3Entry_mul_upperUnipotent3_one]
      unfold cornerEntry
      field_simp
      ring1
  | 1 =>
      change cellRatio v (h * upperUnipotent3 x y z) 1 = cellRatio v h 1 + (z + y * cellRatio v h 0)
      rw [cellRatio_apply_one, cellRatio_apply_one, cellRatio_apply_zero, cornerEntry_mul_upperUnipotent3,
        gl3Entry_mul_upperUnipotent3_two]
      unfold cornerEntry
      field_simp
      ring1
  | 2 =>
      change cellRatio v (h * upperUnipotent3 x y z) 2 = cellRatio v h 2 + y
      rw [cellRatio_apply_two, cellRatio_apply_two, outerMinor_mul_upperUnipotent3, lowerMinor_mul_upperUnipotent3]
      field_simp

private theorem
    exists_forall_cellSectionOf_mul_upperUnipotent3 (hΦl : IsLocallyConstant Φ) (hΦc : HasCompactSupport Φ) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ (h : LocalGL3 v) (x y z : v.adicCompletion ℚ), ‖x‖ ≤ ε → ‖y‖ ≤ ε → ‖z‖ ≤ ε →
      cellSectionOf v ν Φ (h * upperUnipotent3 x y z) = cellSectionOf v ν Φ h := by
  obtain ⟨r, hr, hrΦ⟩ := exists_invariance_radius v Φ hΦl hΦc
  obtain ⟨R, hR⟩ := exists_support_radius v Φ hΦc
  set R' : ℝ := max R 1 with hR'_def
  have hR'1 : (1 : ℝ) ≤ R' := le_max_right _ _
  have hR'0 : (0 : ℝ) < R' := zero_lt_one.trans_le hR'1
  set ε : ℝ := min 1 (r / R') with hε_def
  have hε0 : 0 < ε := lt_min zero_lt_one (div_pos hr hR'0)
  have hε1 : ε ≤ 1 := min_le_left _ _
  have hεr : ε * R' ≤ r := by
    calc ε * R' ≤ r / R' * R' := by gcongr; exact min_le_right _ _
      _ = r := div_mul_cancel₀ r hR'0.ne'
  have hεr' : ε ≤ r := by
    calc ε = ε * 1 := (mul_one ε).symm
      _ ≤ ε * R' := by gcongr
      _ ≤ r := hεr
  refine ⟨ε, hε0, fun h x y z hx hy hz => ?_⟩
  by_cases hg : h ∈ bigCell3 v
  · have hg' : h * upperUnipotent3 x y z ∈ bigCell3 v := (mul_upperUnipotent3_mem_bigCell3_iff v h x y z).mpr hg
    obtain ⟨hc, hl⟩ := (mem_bigCell3_iff v h).mp hg
    rw [cellSectionOf_apply_of_mem v ν Φ hg', cellSectionOf_apply_of_mem v ν Φ hg, cellValue_mul_upperUnipotent3]
    have hq := cellRatio_mul_upperUnipotent3 v hc hl x y z
    by_cases hzero : Φ (cellRatio v h) = 0 ∧ Φ (cellRatio v (h * upperUnipotent3 x y z)) = 0
    · rw [hzero.1, hzero.2]
    ·
      have h0 : ‖cellRatio v h 0‖ ≤ R' := by
        rcases not_and_or.mp hzero with h1 | h2
        · exact (hR _ h1 0).trans (le_max_left _ _)
        · have hb : ‖cellRatio v (h * upperUnipotent3 x y z) 0‖ ≤ R := hR _ h2 0
          have he : cellRatio v h 0 = cellRatio v (h * upperUnipotent3 x y z) 0 + -x := by
            rw [hq]
            simp
          rw [he]
          calc ‖cellRatio v (h * upperUnipotent3 x y z) 0 + -x‖
                ≤ max ‖cellRatio v (h * upperUnipotent3 x y z) 0‖ ‖-x‖ := IsUltrametricDist.norm_add_le_max _ _
            _ ≤ max R 1 := by
                rw [norm_neg]
                exact max_le_max hb (hx.trans hε1)
      congr 1
      apply hrΦ
      intro i
      rw [hq]
      fin_cases i
      · simpa using hx.trans hεr'
      · simp only [Fin.mk_one, Matrix.cons_val_one, Matrix.cons_val_zero, add_sub_cancel_left]
        calc ‖z + y * cellRatio v h 0‖ ≤ max ‖z‖ ‖y * cellRatio v h 0‖ := IsUltrametricDist.norm_add_le_max _ _
          _ ≤ max ε (ε * R') := by
              apply max_le_max hz
              rw [norm_mul]
              exact mul_le_mul hy h0 (norm_nonneg _) hε0.le
          _ ≤ ε * R' := max_le (le_mul_of_one_le_right hε0.le hR'1) le_rfl
          _ ≤ r := hεr
      · simpa using hy.trans hεr'
  · rw [cellSectionOf_apply_of_notMem v ν Φ
        (fun h' => hg ((mul_upperUnipotent3_mem_bigCell3_iff v h x y z).mp h')),
      cellSectionOf_apply_of_notMem v ν Φ hg]

private theorem preimage_add_unipotentBall3_of_mem {c : ℤ}
    {e : v.adicCompletion ℚ × v.adicCompletion ℚ × v.adicCompletion ℚ} (he : e ∈ unipotentBall3 v c) :
    (fun p : v.adicCompletion ℚ × v.adicCompletion ℚ × v.adicCompletion ℚ => p + e) ⁻¹' unipotentBall3 v c =
      unipotentBall3 v c := by
  simp only [mem_unipotentBall3_iff] at he
  obtain ⟨he1, he2, he3⟩ := he
  ext p
  simp only [Set.mem_preimage, mem_unipotentBall3_iff, Prod.fst_add, Prod.snd_add]
  constructor
  · rintro ⟨h1, h2, h3⟩
    refine ⟨?_, ?_, ?_⟩
    · rw [show p.1 = (p.1 + e.1) + -e.1 by ring]
      exact (Valuation.map_add _ _ _).trans (max_le h1 (by rwa [Valuation.map_neg]))
    · rw [show p.2.1 = (p.2.1 + e.2.1) + -e.2.1 by ring]
      exact (Valuation.map_add _ _ _).trans (max_le h2 (by rwa [Valuation.map_neg]))
    · rw [show p.2.2 = (p.2.2 + e.2.2) + -e.2.2 by ring]
      exact (Valuation.map_add _ _ _).trans (max_le h3 (by rwa [Valuation.map_neg]))
  · rintro ⟨h1, h2, h3⟩
    exact ⟨(Valuation.map_add _ _ _).trans (max_le h1 he1), (Valuation.map_add _ _ _).trans (max_le h2 he2),
      (Valuation.map_add _ _ _).trans (max_le h3 he3)⟩

private theorem setIntegral_unipotentBall3_add_of_mem {c : ℤ}
    {e : v.adicCompletion ℚ × v.adicCompletion ℚ × v.adicCompletion ℚ} (he : e ∈ unipotentBall3 v c)
    (F : v.adicCompletion ℚ × v.adicCompletion ℚ × v.adicCompletion ℚ → ℂ) :
    letI := localBorel ℚ v
    ∫ p in unipotentBall3 v c, F (p + e) ∂(jacquetHaar3 v) = ∫ p in unipotentBall3 v c, F p ∂(jacquetHaar3 v) := by
  letI := localBorel ℚ v
  haveI : BorelSpace (v.adicCompletion ℚ) := borelSpace_localBorel ℚ v
  haveI := isAddHaarMeasure_selfDualHaarAt ℚ v
  haveI := sFinite_selfDualHaarAt ℚ v
  have hmeas := measurableSet_unipotentBall3 v c
  have hpre := preimage_add_unipotentBall3_of_mem v he
  have key : (unipotentBall3 v c).indicator (fun p => F (p + e)) =
      fun p => (unipotentBall3 v c).indicator F (p + e) := by
    funext p
    by_cases hp : p ∈ unipotentBall3 v c
    · have hp' : p + e ∈ unipotentBall3 v c := by
        rw [← hpre] at hp
        exact hp
      rw [Set.indicator_of_mem hp, Set.indicator_of_mem hp']
    · have hp' : p + e ∉ unipotentBall3 v c := by
        rw [← hpre] at hp
        exact hp
      rw [Set.indicator_of_notMem hp, Set.indicator_of_notMem hp']
  unfold jacquetHaar3
  rw [← integral_indicator hmeas, ← integral_indicator hmeas, key, integral_add_right_eq_self]

private theorem exists_nat_valued_le_exp (x : v.adicCompletion ℚ) : ∃ N : ℕ, Valued.v x ≤ WithZero.exp (N : ℤ) := by
  obtain ⟨N, hN⟩ := pow_unbounded_of_one_lt ‖x‖ (one_lt_absNorm_real v)
  refine ⟨N, valued_le_of_norm_le_zpow v ?_⟩
  rw [zpow_natCast]
  exact hN.le

private theorem jacquetValue_rightTranslate_upperUnipotent3_mul (hν : ∀ i, IsLocallyConstant (ν i))
    (hΦl : IsLocallyConstant Φ) (hΦc : HasCompactSupport Φ) (g : LocalGL3 v) (e₁ e₃ : v.adicCompletion ℚ) :
    jacquetValue v (gl3AmbientRightTranslate (R := ℂ) (upperUnipotent3 e₁ 0 e₃ * g) (cellSectionOf v ν Φ)) =
      psiLocal ℚ v e₁ * jacquetValue v (gl3AmbientRightTranslate (R := ℂ) g (cellSectionOf v ν Φ)) := by
  letI := localBorel ℚ v
  set f₁ := gl3AmbientRightTranslate (R := ℂ) (upperUnipotent3 e₁ 0 e₃ * g) (cellSectionOf v ν Φ) with hf₁
  set f₀ := gl3AmbientRightTranslate (R := ℂ) g (cellSectionOf v ν Φ) with hf₀
  obtain ⟨c₁, h₁⟩ := exists_forall_le_integrableOn_and_jacquetTruncated3_eq_of_cellSectionOf v ν hν Φ ⟨hΦl, hΦc⟩
    (upperUnipotent3 e₁ 0 e₃ * g)
  obtain ⟨c₀, h₀⟩ := exists_forall_le_integrableOn_and_jacquetTruncated3_eq_of_cellSectionOf v ν hν Φ ⟨hΦl, hΦc⟩ g
  obtain ⟨N₁, hN₁⟩ := exists_nat_valued_le_exp v e₁
  obtain ⟨N₃, hN₃⟩ := exists_nat_valued_le_exp v e₃

  set c : ℤ := max (max (c₁ : ℤ) (c₀ : ℤ)) (max (N₁ : ℤ) (N₃ : ℤ)) with hc_def
  have hc₁ : (c₁ : ℤ) ≤ c := (le_max_left _ _).trans (le_max_left _ _)
  have hc₀ : (c₀ : ℤ) ≤ c := (le_max_right _ _).trans (le_max_left _ _)
  have hcN₁ : (N₁ : ℤ) ≤ c := (le_max_left _ _).trans (le_max_right _ _)
  have hcN₃ : (N₃ : ℤ) ≤ c := (le_max_right _ _).trans (le_max_right _ _)
  have hc0 : (0 : ℤ) ≤ c := (Int.natCast_nonneg N₁).trans hcN₁
  have hst₁ : ∃ c' : ℕ, ∀ c : ℤ, (c' : ℤ) ≤ c → jacquetTruncated3 v c f₁ = jacquetTruncated3 v c' f₁ :=
    ⟨c₁, fun c hc => (h₁ c hc).2⟩
  have hst₀ : ∃ c' : ℕ, ∀ c : ℤ, (c' : ℤ) ≤ c → jacquetTruncated3 v c f₀ = jacquetTruncated3 v c' f₀ :=
    ⟨c₀, fun c hc => (h₀ c hc).2⟩
  have hlev₁ : (jacquetLevel v f₁ : ℤ) ≤ c :=
    (Int.ofNat_le.mpr (jacquetLevel_le v f₁ fun c hc => (h₁ c hc).2)).trans hc₁
  have hlev₀ : (jacquetLevel v f₀ : ℤ) ≤ c :=
    (Int.ofNat_le.mpr (jacquetLevel_le v f₀ fun c hc => (h₀ c hc).2)).trans hc₀
  rw [← jacquetTruncated3_eq_jacquetValue v f₁ hst₁ hlev₁, ← jacquetTruncated3_eq_jacquetValue v f₀ hst₀ hlev₀]

  have he : ((e₁, (0 : v.adicCompletion ℚ), e₃) : v.adicCompletion ℚ × v.adicCompletion ℚ × v.adicCompletion ℚ) ∈
      unipotentBall3 v c := by
    simp only [mem_unipotentBall3_iff, Valuation.map_zero]
    refine ⟨hN₁.trans (WithZero.exp_le_exp.mpr hcN₁), zero_le', hN₃.trans (WithZero.exp_le_exp.mpr ?_)⟩
    omega

  set G : v.adicCompletion ℚ × v.adicCompletion ℚ × v.adicCompletion ℚ → ℂ :=
    fun p => psiLocal ℚ v (-(p.1 + p.2.1)) * f₀ (antidiagonal3 v * upperUnipotent3 p.1 p.2.1 p.2.2) with hG
  have hint : ∀ p : v.adicCompletion ℚ × v.adicCompletion ℚ × v.adicCompletion ℚ,
      psiLocal ℚ v (-(p.1 + p.2.1)) * f₁ (antidiagonal3 v * upperUnipotent3 p.1 p.2.1 p.2.2) =
        psiLocal ℚ v e₁ * G (p + (e₁, (0 : v.adicCompletion ℚ), e₃)) := by
    intro p
    simp only [hG, hf₁, hf₀, gl3AmbientRightTranslate_apply, Prod.fst_add, Prod.snd_add, add_zero]
    rw [show antidiagonal3 v * upperUnipotent3 p.1 p.2.1 p.2.2 * (upperUnipotent3 e₁ 0 e₃ * g) =
        antidiagonal3 v * upperUnipotent3 (p.1 + e₁) p.2.1 (p.2.2 + e₃) * g by
      rw [← mul_assoc, mul_assoc (antidiagonal3 v), upperUnipotent3_mul_upperUnipotent3, add_zero, mul_zero,
        add_zero]]
    rw [← mul_assoc, ← AddChar.map_add_eq_mul]
    congr 2
    ring
  unfold jacquetTruncated3
  simp_rw [hint]
  rw [integral_const_mul, setIntegral_unipotentBall3_add_of_mem v he]

end RightUnipotent
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_tendsto_localZeta_truncPsi_mul_coupled_of_forall_eq_integral_jacquetValue.LaurentZetaSlot"

section DualValueSupport

variable (v : HeightOneSpectrum (𝓞 ℚ))
variable (ν : Fin 3 → ((v.adicCompletion ℚ)ˣ →* ℂˣ)) (Φ : (Fin 3 → v.adicCompletion ℚ) → ℂ)

private theorem dualPoint_mul_upperUnipotent3 (a : (v.adicCompletion ℚ)ˣ) (x t : v.adicCompletion ℚ) :
    dualPoint v a x * upperUnipotent3 0 t 0 = upperUnipotent3 (t * x) 0 (t * a) * dualPoint v a x := by
  apply Units.ext
  rw [Units.val_mul, Units.val_mul, upperUnipotent3_coe, upperUnipotent3_coe,
    show ((dualPoint v a x : LocalGL3 v) : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) =
      !![0, 1, 0; 1, 0, 0; -(((a⁻¹ : (v.adicCompletion ℚ)ˣ) : v.adicCompletion ℚ) * x), 0,
        ((a⁻¹ : (v.adicCompletion ℚ)ˣ) : v.adicCompletion ℚ)] from coe_dualPoint_mul_antidiagonal3 v a x]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three]
  first | ring1 | (field_simp; ring1)

private theorem exists_forall_lt_norm_jacquetValue_dualTranslate_eq_zero (hν : ∀ i, IsLocallyConstant (ν i))
    (hΦl : IsLocallyConstant Φ) (hΦc : HasCompactSupport Φ) :
    ∃ X₀ : ℝ, ∀ (a : (v.adicCompletion ℚ)ˣ) (x : v.adicCompletion ℚ), X₀ < ‖x‖ →
      jacquetValue v (dualTranslate v ν Φ a x) = 0 := by
  obtain ⟨ε, hε, hU⟩ := exists_forall_cellSectionOf_mul_upperUnipotent3 v ν Φ hΦl hΦc
  obtain ⟨w₀, hw₀⟩ : ∃ w₀ : v.adicCompletion ℚ, psiLocal ℚ v w₀ ≠ 1 := by
    by_contra h
    push Not at h
    exact psiLocal_ne_one ℚ v (AddChar.ext _ _ h)
  refine ⟨‖w₀‖ / ε, fun a x hx => ?_⟩
  have hxpos : 0 < ‖x‖ := (div_nonneg (norm_nonneg _) hε.le).trans_lt hx
  have hx0 : x ≠ 0 := norm_pos_iff.mp hxpos
  set t : v.adicCompletion ℚ := w₀ / x with ht_def
  have ht : ‖t‖ ≤ ε := by
    rw [ht_def, norm_div, div_le_iff₀ hxpos]
    have := (div_lt_iff₀ hε).mp hx
    linarith [mul_comm ε ‖x‖]
  have htx : t * x = w₀ := div_mul_cancel₀ w₀ hx0

  have h1 : gl3AmbientRightTranslate (R := ℂ) (dualPoint v a x * upperUnipotent3 0 t 0) (cellSectionOf v ν Φ) =
      dualTranslate v ν Φ a x := by
    funext h
    rw [dualTranslate_apply, gl3AmbientRightTranslate_apply, ← mul_assoc]
    exact hU _ 0 t 0 (by simpa using hε.le) ht (by simpa using hε.le)
  have h2 := jacquetValue_rightTranslate_upperUnipotent3_mul v ν Φ hν hΦl hΦc (dualPoint v a x) (t * x) (t * a)
  rw [← dualPoint_mul_upperUnipotent3, h1, htx] at h2
  have h3 : jacquetValue v (gl3AmbientRightTranslate (R := ℂ) (dualPoint v a x) (cellSectionOf v ν Φ)) =
      jacquetValue v (dualTranslate v ν Φ a x) := rfl
  rw [h3] at h2

  have h4 : (1 - psiLocal ℚ v w₀) * jacquetValue v (dualTranslate v ν Φ a x) = 0 := by
    linear_combination h2
  rcases mul_eq_zero.mp h4 with h5 | h5
  · exact absurd (sub_eq_zero.mp h5).symm hw₀
  · exact h5

end DualValueSupport
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_tendsto_localZeta_truncPsi_mul_coupled_of_forall_eq_integral_jacquetValue.LaurentZetaSlot"

end LanglandsTunnell.CubicInduction
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_tendsto_localZeta_truncPsi_mul_coupled_of_forall_eq_integral_jacquetValue.LaurentZetaSlot"
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_tendsto_localZeta_truncPsi_mul_coupled_of_forall_eq_integral_jacquetValue.LaurentZetaSlot"

end Part7
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_tendsto_localZeta_truncPsi_mul_coupled_of_forall_eq_integral_jacquetValue.LaurentZetaSlot"

section Part14

set_option autoImplicit false

open IsDedekindDomain NumberField MeasureTheory
open scoped NNReal ENNReal

namespace LanglandsTunnell
p2m_export "LanglandsTunnell" "TateLocal.localBorel TateLocal.borelSpace_localBorel CubicInduction.exists_forall_norm_setIntegral_annulus_setIntegral_compl_ball_jacquetWindow_le CubicInduction.exists_forall_norm_dualZetaRemainder_outside_annulus_le CubicInduction.localZeta_truncPsi_mul_coupled_eq_localZeta_of_forall_eq_integral_jacquetWindow CubicInduction.tendsto_setIntegral_annulus_setIntegral_ball_jacquetWindow_sub_jacquetValue CubicInduction.localZeta_primedDual_eq_pieces_add_setIntegral_annulus_of_forall_eq_zero"
namespace TateLocal
p2m_export "LanglandsTunnell.TateLocal" "addCharLevel localBorel borelSpace_localBorel integersPositiveCompacts coe_integersPositiveCompacts selfDualHaarAt modulus charExt charExt_zero mulMeasure localZeta modulus_adicCompletion_eq_nnnorm psiLocal_ne_one"
p2m_open "LanglandsTunnell.TateLocal LanglandsTunnell"

variable (v : HeightOneSpectrum (𝓞 ℚ))

section MeasureForm

attribute [local instance] LanglandsTunnell.TateLocal.localBorel
attribute [local instance] LanglandsTunnell.TateLocal.borelSpace_localBorel

private theorem mulMeasure_singleton_zero (μ : Measure (v.adicCompletion ℚ)) :
    mulMeasure μ ({0} : Set (v.adicCompletion ℚ)) = 0 := by
  unfold mulMeasure
  rw [withDensity_apply _ (measurableSet_singleton 0), Measure.restrict_restrict (measurableSet_singleton 0),
    Set.inter_compl_self, Measure.restrict_empty, lintegral_zero_measure]

end MeasureForm
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_tendsto_localZeta_truncPsi_mul_coupled_of_forall_eq_integral_jacquetValue.LaurentZetaSlot"

end LanglandsTunnell.TateLocal
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_tendsto_localZeta_truncPsi_mul_coupled_of_forall_eq_integral_jacquetValue.LaurentZetaSlot"
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_tendsto_localZeta_truncPsi_mul_coupled_of_forall_eq_integral_jacquetValue.LaurentZetaSlot"
end Part14
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_tendsto_localZeta_truncPsi_mul_coupled_of_forall_eq_integral_jacquetValue.LaurentZetaSlot"

section Part15

set_option autoImplicit false

open MeasureTheory
open IsDedekindDomain
open NumberField
p2m_open "LanglandsTunnell.TateLocal P2MW.S_LanglandsTunnell_CubicInduction_tendsto_localZeta_truncPsi_mul_coupled_of_forall_eq_integral_jacquetValue.LanglandsTunnell.TateLocal"

attribute [local instance] LanglandsTunnell.TateLocal.localBorel

namespace LanglandsTunnell
p2m_export "LanglandsTunnell" "TateLocal.localBorel TateLocal.borelSpace_localBorel CubicInduction.exists_forall_norm_setIntegral_annulus_setIntegral_compl_ball_jacquetWindow_le CubicInduction.exists_forall_norm_dualZetaRemainder_outside_annulus_le CubicInduction.localZeta_truncPsi_mul_coupled_eq_localZeta_of_forall_eq_integral_jacquetWindow CubicInduction.tendsto_setIntegral_annulus_setIntegral_ball_jacquetWindow_sub_jacquetValue CubicInduction.localZeta_primedDual_eq_pieces_add_setIntegral_annulus_of_forall_eq_zero"
namespace CubicInduction
p2m_export "LanglandsTunnell.CubicInduction" "lowerUnipotent21 longWeyl3 longWeyl3_coe weylPrime3 weylPrime3_coe transposeInv3_weylPrime3 transposeInv3_lowerUnipotent21 gl3AmbientRightTranslate gl3AmbientRightTranslate_apply transposeInv3 upperUnipotent3 upperUnipotent3_coe embedMat2 iotaGL coe_iotaGL LocalGL3 diagUnitGL2 coe_diagUnitGL2 unipotentBall3 mem_unipotentBall3_iff upperUnipotent3_mul_upperUnipotent3 jacquetHaar3 jacquetTruncated3 jacquetLevel jacquetValue jacquetTruncated3_eq_jacquetValue jacquetLevel_le bigCell3 mem_bigCell3_iff cellSectionOf cellSectionOf_apply_of_mem cellSectionOf_apply_of_notMem gl3Entry cornerEntry lowerMinor outerMinor gl3Det cellRatio cellValue antidiagonal3 antidiagonal3_coe eventually_valued_eq exists_forall_le_integrableOn_and_jacquetTruncated3_eq_of_cellSectionOf exists_forall_norm_setIntegral_annulus_setIntegral_compl_ball_jacquetWindow_le exists_forall_norm_dualZetaRemainder_outside_annulus_le localZeta_truncPsi_mul_coupled_eq_localZeta_of_forall_eq_integral_jacquetWindow tendsto_setIntegral_annulus_setIntegral_ball_jacquetWindow_sub_jacquetValue localZeta_primedDual_eq_pieces_add_setIntegral_annulus_of_forall_eq_zero"
p2m_open "LanglandsTunnell.CubicInduction LanglandsTunnell"

variable (v : HeightOneSpectrum (𝓞 ℚ))

private noncomputable def truncChar (c : ℤ) (t : v.adicCompletion ℚ) : ℂ :=
  if Valued.v t ≤ WithZero.exp c then (NumberField.StandardAddChar.psiLocal ℚ v t : ℂ) else 0

private noncomputable def gaussIntegral (η : (v.adicCompletion ℚ)ˣ →* ℂˣ) (z : ℂ) (c : ℤ) : ℂ :=
  localZeta (selfDualHaarAt ℚ v) (fun t => truncChar v c (-t)) η z

private noncomputable def coupledIntegral (ν : Fin 3 → ((v.adicCompletion ℚ)ˣ →* ℂˣ))
    (Φ : (Fin 3 → v.adicCompletion ℚ) → ℂ) (χ : (v.adicCompletion ℚ)ˣ →* ℂˣ) (s : ℂ) (c : ℤ) : ℂ :=
  ∫ p : v.adicCompletion ℚ × v.adicCompletion ℚ × v.adicCompletion ℚ,
      Φ ![p.1, p.2.1, p.2.2] *
        (charExt (ν 2 * χ)⁻¹ p.1 * ((modulus p.1 : ℝ) : ℂ) ^ (1 - s)) *
        (charExt (ν 1 * χ) p.2.1 * ((modulus p.2.1 : ℝ) : ℂ) ^ s) *
        (charExt (ν 0 * (ν 1)⁻¹) (p.2.1 - p.1 * p.2.2) * ((modulus (p.2.1 - p.1 * p.2.2) : ℝ) : ℂ)⁻¹) *
        truncChar v c (p.2.2 / (p.2.1 - p.1 * p.2.2))
    ∂((mulMeasure (selfDualHaarAt ℚ v)).prod ((mulMeasure (selfDualHaarAt ℚ v)).prod (selfDualHaarAt ℚ v)))

end LanglandsTunnell.CubicInduction
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_tendsto_localZeta_truncPsi_mul_coupled_of_forall_eq_integral_jacquetValue.LaurentZetaSlot"
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_tendsto_localZeta_truncPsi_mul_coupled_of_forall_eq_integral_jacquetValue.LaurentZetaSlot"
end Part15
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_tendsto_localZeta_truncPsi_mul_coupled_of_forall_eq_integral_jacquetValue.LaurentZetaSlot"

section Part18
set_option autoImplicit false

open MeasureTheory
open IsDedekindDomain
open NumberField
p2m_open "LanglandsTunnell.TateLocal P2MW.S_LanglandsTunnell_CubicInduction_tendsto_localZeta_truncPsi_mul_coupled_of_forall_eq_integral_jacquetValue.LanglandsTunnell.TateLocal"

attribute [local instance] LanglandsTunnell.TateLocal.localBorel

namespace LanglandsTunnell
p2m_export "LanglandsTunnell" "TateLocal.localBorel TateLocal.borelSpace_localBorel CubicInduction.exists_forall_norm_setIntegral_annulus_setIntegral_compl_ball_jacquetWindow_le CubicInduction.exists_forall_norm_dualZetaRemainder_outside_annulus_le CubicInduction.localZeta_truncPsi_mul_coupled_eq_localZeta_of_forall_eq_integral_jacquetWindow CubicInduction.tendsto_setIntegral_annulus_setIntegral_ball_jacquetWindow_sub_jacquetValue CubicInduction.localZeta_primedDual_eq_pieces_add_setIntegral_annulus_of_forall_eq_zero"
namespace CubicInduction
p2m_export "LanglandsTunnell.CubicInduction" "lowerUnipotent21 longWeyl3 longWeyl3_coe weylPrime3 weylPrime3_coe transposeInv3_weylPrime3 transposeInv3_lowerUnipotent21 gl3AmbientRightTranslate gl3AmbientRightTranslate_apply transposeInv3 upperUnipotent3 upperUnipotent3_coe embedMat2 iotaGL coe_iotaGL LocalGL3 diagUnitGL2 coe_diagUnitGL2 unipotentBall3 mem_unipotentBall3_iff upperUnipotent3_mul_upperUnipotent3 jacquetHaar3 jacquetTruncated3 jacquetLevel jacquetValue jacquetTruncated3_eq_jacquetValue jacquetLevel_le bigCell3 mem_bigCell3_iff cellSectionOf cellSectionOf_apply_of_mem cellSectionOf_apply_of_notMem gl3Entry cornerEntry lowerMinor outerMinor gl3Det cellRatio cellValue antidiagonal3 antidiagonal3_coe eventually_valued_eq exists_forall_le_integrableOn_and_jacquetTruncated3_eq_of_cellSectionOf exists_forall_norm_setIntegral_annulus_setIntegral_compl_ball_jacquetWindow_le exists_forall_norm_dualZetaRemainder_outside_annulus_le localZeta_truncPsi_mul_coupled_eq_localZeta_of_forall_eq_integral_jacquetWindow tendsto_setIntegral_annulus_setIntegral_ball_jacquetWindow_sub_jacquetValue localZeta_primedDual_eq_pieces_add_setIntegral_annulus_of_forall_eq_zero"
p2m_open "LanglandsTunnell.CubicInduction LanglandsTunnell"

section DualLevelLegs

variable (v : HeightOneSpectrum (𝓞 ℚ))

private def annulus (N : ℕ) : Set (v.adicCompletion ℚ) :=
  {t | WithZero.exp (-(N : ℤ)) ≤ Valued.v t ∧ Valued.v t ≤ WithZero.exp (N : ℤ)}

private theorem isOpen_annulus (N : ℕ) : IsOpen (annulus v N) := by
  rw [isOpen_iff_eventually]
  intro t ht
  simp only [annulus, Set.mem_setOf_eq] at ht
  have ht0 : t ≠ 0 := by
    rintro rfl
    rw [map_zero] at ht
    exact (not_le.mpr WithZero.exp_pos) ht.1
  filter_upwards [eventually_valued_eq v ht0] with y hy
  simp only [annulus, Set.mem_setOf_eq, hy]
  exact ht

private theorem annulus_mono : Monotone (annulus v) := by
  intro N N' hNN' t ht
  simp only [annulus, Set.mem_setOf_eq] at ht ⊢
  refine ⟨le_trans ?_ ht.1, le_trans ht.2 ?_⟩
  · rw [WithZero.exp_le_exp]
    omega
  · rw [WithZero.exp_le_exp]
    omega

private theorem iUnion_annulus : (⋃ N : ℕ, annulus v N) = {(0 : v.adicCompletion ℚ)}ᶜ := by
  ext t
  simp only [Set.mem_iUnion, annulus, Set.mem_setOf_eq, Set.mem_compl_iff, Set.mem_singleton_iff]
  constructor
  · rintro ⟨N, hN, -⟩ rfl
    rw [map_zero] at hN
    exact (not_le.mpr WithZero.exp_pos) hN
  · intro ht
    have hv : Valued.v t ≠ (0 : WithZero (Multiplicative ℤ)) := (Valuation.ne_zero_iff _).mpr ht
    obtain ⟨k, hk⟩ : ∃ k : ℤ, Valued.v t = WithZero.exp k := ⟨_, (WithZero.exp_log hv).symm⟩
    refine ⟨k.natAbs, ?_, ?_⟩
    · rw [hk, WithZero.exp_le_exp]
      omega
    · rw [hk, WithZero.exp_le_exp]
      omega

private theorem mulMeasure_singleton_zero :
    mulMeasure (selfDualHaarAt ℚ v) {(0 : v.adicCompletion ℚ)} = 0 := by
  haveI : BorelSpace (v.adicCompletion ℚ) := borelSpace_localBorel ℚ v
  have hs : MeasurableSet {(0 : v.adicCompletion ℚ)} := isClosed_singleton.measurableSet
  rw [mulMeasure, withDensity_apply _ hs, Measure.restrict_restrict hs, Set.inter_compl_self,
    Measure.restrict_empty, lintegral_zero_measure]

private theorem tendsto_setIntegral_annulus_localZeta_dualFn (ν : Fin 3 → ((v.adicCompletion ℚ)ˣ →* ℂˣ))
    (Φ : (Fin 3 → v.adicCompletion ℚ) → ℂ) (χ : (v.adicCompletion ℚ)ˣ →* ℂˣ) (s : ℂ)
    (hint : Integrable (fun x => dualFn v ν Φ x * charExt χ⁻¹ x * ((modulus x : ℝ) : ℂ) ^ (1 - s))
      (mulMeasure (selfDualHaarAt ℚ v))) :
    Filter.Tendsto
      (fun N : ℕ => ∫ x in annulus v N, dualFn v ν Φ x * charExt χ⁻¹ x * ((modulus x : ℝ) : ℂ) ^ (1 - s)
        ∂(mulMeasure (selfDualHaarAt ℚ v)))
      Filter.atTop (nhds (localZeta (selfDualHaarAt ℚ v) (dualFn v ν Φ) χ⁻¹ (1 - s))) := by
  haveI : BorelSpace (v.adicCompletion ℚ) := borelSpace_localBorel ℚ v
  have h := tendsto_setIntegral_of_monotone₀
    (fun N => (isOpen_annulus v N).measurableSet.nullMeasurableSet (μ := mulMeasure (selfDualHaarAt ℚ v)))
    (annulus_mono v) hint.integrableOn
  rw [iUnion_annulus v, Measure.restrict_eq_self_of_ae_mem] at h
  · exact h
  · rw [ae_iff]
    simpa using mulMeasure_singleton_zero v

end DualLevelLegs
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_tendsto_localZeta_truncPsi_mul_coupled_of_forall_eq_integral_jacquetValue.LaurentZetaSlot"

end LanglandsTunnell.CubicInduction
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_tendsto_localZeta_truncPsi_mul_coupled_of_forall_eq_integral_jacquetValue.LaurentZetaSlot"
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_tendsto_localZeta_truncPsi_mul_coupled_of_forall_eq_integral_jacquetValue.LaurentZetaSlot"

end Part18
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_tendsto_localZeta_truncPsi_mul_coupled_of_forall_eq_integral_jacquetValue.LaurentZetaSlot"

section Part26

set_option autoImplicit false

open MeasureTheory
open IsDedekindDomain
open NumberField
p2m_open "LanglandsTunnell.TateLocal P2MW.S_LanglandsTunnell_CubicInduction_tendsto_localZeta_truncPsi_mul_coupled_of_forall_eq_integral_jacquetValue.LanglandsTunnell.TateLocal"
open NumberField.StandardAddChar
open scoped NNReal ENNReal

attribute [local instance] LanglandsTunnell.TateLocal.localBorel
attribute [local instance] LanglandsTunnell.TateLocal.borelSpace_localBorel

namespace LanglandsTunnell
p2m_export "LanglandsTunnell" "TateLocal.localBorel TateLocal.borelSpace_localBorel CubicInduction.exists_forall_norm_setIntegral_annulus_setIntegral_compl_ball_jacquetWindow_le CubicInduction.exists_forall_norm_dualZetaRemainder_outside_annulus_le CubicInduction.localZeta_truncPsi_mul_coupled_eq_localZeta_of_forall_eq_integral_jacquetWindow CubicInduction.tendsto_setIntegral_annulus_setIntegral_ball_jacquetWindow_sub_jacquetValue CubicInduction.localZeta_primedDual_eq_pieces_add_setIntegral_annulus_of_forall_eq_zero"
namespace CubicInduction
p2m_export "LanglandsTunnell.CubicInduction" "lowerUnipotent21 longWeyl3 longWeyl3_coe weylPrime3 weylPrime3_coe transposeInv3_weylPrime3 transposeInv3_lowerUnipotent21 gl3AmbientRightTranslate gl3AmbientRightTranslate_apply transposeInv3 upperUnipotent3 upperUnipotent3_coe embedMat2 iotaGL coe_iotaGL LocalGL3 diagUnitGL2 coe_diagUnitGL2 unipotentBall3 mem_unipotentBall3_iff upperUnipotent3_mul_upperUnipotent3 jacquetHaar3 jacquetTruncated3 jacquetLevel jacquetValue jacquetTruncated3_eq_jacquetValue jacquetLevel_le bigCell3 mem_bigCell3_iff cellSectionOf cellSectionOf_apply_of_mem cellSectionOf_apply_of_notMem gl3Entry cornerEntry lowerMinor outerMinor gl3Det cellRatio cellValue antidiagonal3 antidiagonal3_coe eventually_valued_eq exists_forall_le_integrableOn_and_jacquetTruncated3_eq_of_cellSectionOf exists_forall_norm_setIntegral_annulus_setIntegral_compl_ball_jacquetWindow_le exists_forall_norm_dualZetaRemainder_outside_annulus_le localZeta_truncPsi_mul_coupled_eq_localZeta_of_forall_eq_integral_jacquetWindow tendsto_setIntegral_annulus_setIntegral_ball_jacquetWindow_sub_jacquetValue localZeta_primedDual_eq_pieces_add_setIntegral_annulus_of_forall_eq_zero"
p2m_open "LanglandsTunnell.CubicInduction LanglandsTunnell"

variable (v : HeightOneSpectrum (𝓞 ℚ))

private noncomputable def rv (ρ : WithZero (Multiplicative ℤ)) : ℝ :=
  if ρ = 0 then 0 else (Ideal.absNorm v.asIdeal : ℝ) ^ (WithZero.log ρ)

private theorem rv_exp (n : ℤ) : rv v (WithZero.exp n) = (Ideal.absNorm v.asIdeal : ℝ) ^ n := by
  rw [rv, if_neg WithZero.exp_ne_zero, WithZero.log_exp]

private theorem rv_lt_rv_iff {ρ₁ ρ₂ : WithZero (Multiplicative ℤ)} (h₁ : ρ₁ ≠ 0) (h₂ : ρ₂ ≠ 0) :
    rv v ρ₁ < rv v ρ₂ ↔ ρ₁ < ρ₂ := by
  rw [rv, rv, if_neg h₁, if_neg h₂, zpow_lt_zpow_iff_right₀ (one_lt_absNorm_real v), WithZero.log_lt_log h₁ h₂]

private theorem rv_valued {x : v.adicCompletion ℚ} (hx : x ≠ 0) : rv v (Valued.v x) = (modulus x : ℝ) := by
  obtain ⟨j, hj⟩ := LaurentZetaSlot.exists_mem_shell v hx
  have hvx : Valued.v x = WithZero.exp (-j) := hj
  rw [hvx, rv_exp, LaurentZetaSlot.coe_modulus_eq_of_mem_shell v hj]

private theorem valued_ne_zero {x : v.adicCompletion ℚ} (hx : x ≠ 0) : Valued.v x ≠ 0 :=
  (Valuation.ne_zero_iff _).mpr hx

section Assembly

variable (ν : Fin 3 → ((v.adicCompletion ℚ)ˣ →* ℂˣ)) (Φ : (Fin 3 → v.adicCompletion ℚ) → ℂ)
variable (χ : (v.adicCompletion ℚ)ˣ →* ℂˣ) (s : ℂ)

end Assembly
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_tendsto_localZeta_truncPsi_mul_coupled_of_forall_eq_integral_jacquetValue.LaurentZetaSlot"

end LanglandsTunnell.CubicInduction
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_tendsto_localZeta_truncPsi_mul_coupled_of_forall_eq_integral_jacquetValue.LaurentZetaSlot"
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_tendsto_localZeta_truncPsi_mul_coupled_of_forall_eq_integral_jacquetValue.LaurentZetaSlot"
end Part26
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_tendsto_localZeta_truncPsi_mul_coupled_of_forall_eq_integral_jacquetValue.LaurentZetaSlot"

section Part34

set_option autoImplicit false

p2m_open "MeasureTheory IsDedekindDomain NumberField LanglandsTunnell.TateLocal P2MW.S_LanglandsTunnell_CubicInduction_tendsto_localZeta_truncPsi_mul_coupled_of_forall_eq_integral_jacquetValue.LanglandsTunnell.TateLocal NumberField.StandardAddChar"
open scoped ENNReal NNReal

attribute [local instance] LanglandsTunnell.TateLocal.localBorel

namespace LanglandsTunnell
p2m_export "LanglandsTunnell" "TateLocal.localBorel TateLocal.borelSpace_localBorel CubicInduction.exists_forall_norm_setIntegral_annulus_setIntegral_compl_ball_jacquetWindow_le CubicInduction.exists_forall_norm_dualZetaRemainder_outside_annulus_le CubicInduction.localZeta_truncPsi_mul_coupled_eq_localZeta_of_forall_eq_integral_jacquetWindow CubicInduction.tendsto_setIntegral_annulus_setIntegral_ball_jacquetWindow_sub_jacquetValue CubicInduction.localZeta_primedDual_eq_pieces_add_setIntegral_annulus_of_forall_eq_zero"
namespace CubicInduction
p2m_export "LanglandsTunnell.CubicInduction" "lowerUnipotent21 longWeyl3 longWeyl3_coe weylPrime3 weylPrime3_coe transposeInv3_weylPrime3 transposeInv3_lowerUnipotent21 gl3AmbientRightTranslate gl3AmbientRightTranslate_apply transposeInv3 upperUnipotent3 upperUnipotent3_coe embedMat2 iotaGL coe_iotaGL LocalGL3 diagUnitGL2 coe_diagUnitGL2 unipotentBall3 mem_unipotentBall3_iff upperUnipotent3_mul_upperUnipotent3 jacquetHaar3 jacquetTruncated3 jacquetLevel jacquetValue jacquetTruncated3_eq_jacquetValue jacquetLevel_le bigCell3 mem_bigCell3_iff cellSectionOf cellSectionOf_apply_of_mem cellSectionOf_apply_of_notMem gl3Entry cornerEntry lowerMinor outerMinor gl3Det cellRatio cellValue antidiagonal3 antidiagonal3_coe eventually_valued_eq exists_forall_le_integrableOn_and_jacquetTruncated3_eq_of_cellSectionOf exists_forall_norm_setIntegral_annulus_setIntegral_compl_ball_jacquetWindow_le exists_forall_norm_dualZetaRemainder_outside_annulus_le localZeta_truncPsi_mul_coupled_eq_localZeta_of_forall_eq_integral_jacquetWindow tendsto_setIntegral_annulus_setIntegral_ball_jacquetWindow_sub_jacquetValue localZeta_primedDual_eq_pieces_add_setIntegral_annulus_of_forall_eq_zero"
p2m_open "LanglandsTunnell.CubicInduction LanglandsTunnell"

section DualFiniteLevel

variable (v : HeightOneSpectrum (𝓞 ℚ))

private def primedBall3 (c : ℤ) : Set (v.adicCompletion ℚ × v.adicCompletion ℚ × v.adicCompletion ℚ) :=
  {p | Valued.v p.2.1 ≤ WithZero.exp c ∧ Valued.v p.2.2 ≤ WithZero.exp c * Valued.v p.2.1 ∧
    Valued.v (p.1 - p.2.2 / p.2.1) ≤ WithZero.exp c}

private noncomputable def jacquetPrimed3 (ν : Fin 3 → ((v.adicCompletion ℚ)ˣ →* ℂˣ))
    (Φ : (Fin 3 → v.adicCompletion ℚ) → ℂ) (c : ℤ) (a : (v.adicCompletion ℚ)ˣ) (x : v.adicCompletion ℚ) : ℂ :=
  ∫ p in primedBall3 v c,
    NumberField.StandardAddChar.psiLocal ℚ v (-(p.1 + p.2.1)) *
      cellSectionOf v ν Φ (dualCellPoint v p.1 p.2.1 p.2.2 a x) ∂(jacquetHaar3 v)

open Classical in
private noncomputable def dualFnPrimed (ν : Fin 3 → ((v.adicCompletion ℚ)ˣ →* ℂˣ))
    (Φ : (Fin 3 → v.adicCompletion ℚ) → ℂ) (c : ℤ) : v.adicCompletion ℚ → ℂ := fun t =>
  if h : t = 0 then 0 else
    (∫ x : v.adicCompletion ℚ, jacquetPrimed3 v ν Φ c (Units.mk0 t h) x ∂(selfDualHaarAt ℚ v)) *
      ((modulus t : ℝ) : ℂ)⁻¹

end DualFiniteLevel
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_tendsto_localZeta_truncPsi_mul_coupled_of_forall_eq_integral_jacquetValue.LaurentZetaSlot"

end LanglandsTunnell.CubicInduction
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_tendsto_localZeta_truncPsi_mul_coupled_of_forall_eq_integral_jacquetValue.LaurentZetaSlot"
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_tendsto_localZeta_truncPsi_mul_coupled_of_forall_eq_integral_jacquetValue.LaurentZetaSlot"
end Part34
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_tendsto_localZeta_truncPsi_mul_coupled_of_forall_eq_integral_jacquetValue.LaurentZetaSlot"

section Part35

set_option autoImplicit false

p2m_open "MeasureTheory IsDedekindDomain NumberField LanglandsTunnell.TateLocal P2MW.S_LanglandsTunnell_CubicInduction_tendsto_localZeta_truncPsi_mul_coupled_of_forall_eq_integral_jacquetValue.LanglandsTunnell.TateLocal NumberField.StandardAddChar"
open scoped ENNReal NNReal

attribute [local instance] LanglandsTunnell.TateLocal.localBorel

namespace LanglandsTunnell
p2m_export "LanglandsTunnell" "TateLocal.localBorel TateLocal.borelSpace_localBorel CubicInduction.exists_forall_norm_setIntegral_annulus_setIntegral_compl_ball_jacquetWindow_le CubicInduction.exists_forall_norm_dualZetaRemainder_outside_annulus_le CubicInduction.localZeta_truncPsi_mul_coupled_eq_localZeta_of_forall_eq_integral_jacquetWindow CubicInduction.tendsto_setIntegral_annulus_setIntegral_ball_jacquetWindow_sub_jacquetValue CubicInduction.localZeta_primedDual_eq_pieces_add_setIntegral_annulus_of_forall_eq_zero"
namespace CubicInduction
p2m_export "LanglandsTunnell.CubicInduction" "lowerUnipotent21 longWeyl3 longWeyl3_coe weylPrime3 weylPrime3_coe transposeInv3_weylPrime3 transposeInv3_lowerUnipotent21 gl3AmbientRightTranslate gl3AmbientRightTranslate_apply transposeInv3 upperUnipotent3 upperUnipotent3_coe embedMat2 iotaGL coe_iotaGL LocalGL3 diagUnitGL2 coe_diagUnitGL2 unipotentBall3 mem_unipotentBall3_iff upperUnipotent3_mul_upperUnipotent3 jacquetHaar3 jacquetTruncated3 jacquetLevel jacquetValue jacquetTruncated3_eq_jacquetValue jacquetLevel_le bigCell3 mem_bigCell3_iff cellSectionOf cellSectionOf_apply_of_mem cellSectionOf_apply_of_notMem gl3Entry cornerEntry lowerMinor outerMinor gl3Det cellRatio cellValue antidiagonal3 antidiagonal3_coe eventually_valued_eq exists_forall_le_integrableOn_and_jacquetTruncated3_eq_of_cellSectionOf exists_forall_norm_setIntegral_annulus_setIntegral_compl_ball_jacquetWindow_le exists_forall_norm_dualZetaRemainder_outside_annulus_le localZeta_truncPsi_mul_coupled_eq_localZeta_of_forall_eq_integral_jacquetWindow tendsto_setIntegral_annulus_setIntegral_ball_jacquetWindow_sub_jacquetValue localZeta_primedDual_eq_pieces_add_setIntegral_annulus_of_forall_eq_zero"
p2m_open "LanglandsTunnell.CubicInduction LanglandsTunnell"

section DualRemainder

variable (v : HeightOneSpectrum (𝓞 ℚ))

open Classical in
private noncomputable def primedKernel (ν : Fin 3 → ((v.adicCompletion ℚ)ˣ →* ℂˣ))
    (Φ : (Fin 3 → v.adicCompletion ℚ) → ℂ) (c : ℤ) (a x : v.adicCompletion ℚ) : ℂ :=
  if h : a = 0 then 0 else jacquetPrimed3 v ν Φ c (Units.mk0 a h) x

open Classical in
private noncomputable def valueKernel (ν : Fin 3 → ((v.adicCompletion ℚ)ˣ →* ℂˣ))
    (Φ : (Fin 3 → v.adicCompletion ℚ) → ℂ) (a x : v.adicCompletion ℚ) : ℂ :=
  if h : a = 0 then 0 else jacquetValue v (dualTranslate v ν Φ (Units.mk0 a h) x)

private noncomputable def dualWeight (χ : (v.adicCompletion ℚ)ˣ →* ℂˣ) (s : ℂ) (a : v.adicCompletion ℚ) : ℂ :=
  ((modulus a : ℝ) : ℂ)⁻¹ * charExt χ⁻¹ a * ((modulus a : ℝ) : ℂ) ^ (1 - s)

private def xBall (R : ℕ) : Set (v.adicCompletion ℚ) :=
  {x | Valued.v x ≤ WithZero.exp (R : ℤ)}

private noncomputable def pieceW (ν : Fin 3 → ((v.adicCompletion ℚ)ˣ →* ℂˣ))
    (Φ : (Fin 3 → v.adicCompletion ℚ) → ℂ) (χ : (v.adicCompletion ℚ)ˣ →* ℂˣ) (s : ℂ) (N R : ℕ) (c : ℤ) : ℂ :=
  ∫ a in annulus v N, dualWeight v χ s a *
    ∫ x in xBall v R, (primedKernel v ν Φ c a x - valueKernel v ν Φ a x) ∂(selfDualHaarAt ℚ v)
    ∂(mulMeasure (selfDualHaarAt ℚ v))

private noncomputable def pieceX (ν : Fin 3 → ((v.adicCompletion ℚ)ˣ →* ℂˣ))
    (Φ : (Fin 3 → v.adicCompletion ℚ) → ℂ) (χ : (v.adicCompletion ℚ)ˣ →* ℂˣ) (s : ℂ) (N R : ℕ) (c : ℤ) : ℂ :=
  ∫ a in annulus v N, dualWeight v χ s a *
    ∫ x in (xBall v R)ᶜ, primedKernel v ν Φ c a x ∂(selfDualHaarAt ℚ v) ∂(mulMeasure (selfDualHaarAt ℚ v))

private noncomputable def pieceY (ν : Fin 3 → ((v.adicCompletion ℚ)ˣ →* ℂˣ))
    (Φ : (Fin 3 → v.adicCompletion ℚ) → ℂ) (χ : (v.adicCompletion ℚ)ˣ →* ℂˣ) (s : ℂ) (N : ℕ) (c : ℤ) : ℂ :=
  ∫ a in (annulus v N)ᶜ, dualWeight v χ s a *
    ∫ x, primedKernel v ν Φ c a x ∂(selfDualHaarAt ℚ v) ∂(mulMeasure (selfDualHaarAt ℚ v))

end DualRemainder
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_tendsto_localZeta_truncPsi_mul_coupled_of_forall_eq_integral_jacquetValue.LaurentZetaSlot"

end LanglandsTunnell.CubicInduction
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_tendsto_localZeta_truncPsi_mul_coupled_of_forall_eq_integral_jacquetValue.LaurentZetaSlot"
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_tendsto_localZeta_truncPsi_mul_coupled_of_forall_eq_integral_jacquetValue.LaurentZetaSlot"
end Part35
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_tendsto_localZeta_truncPsi_mul_coupled_of_forall_eq_integral_jacquetValue.LaurentZetaSlot"

section PieceBridges

open MeasureTheory
open IsDedekindDomain
open NumberField
p2m_open "LanglandsTunnell.TateLocal P2MW.S_LanglandsTunnell_CubicInduction_tendsto_localZeta_truncPsi_mul_coupled_of_forall_eq_integral_jacquetValue.LanglandsTunnell.TateLocal"

attribute [local instance] LanglandsTunnell.TateLocal.localBorel
attribute [local instance] LanglandsTunnell.TateLocal.borelSpace_localBorel

namespace LanglandsTunnell
p2m_export "LanglandsTunnell" "TateLocal.localBorel TateLocal.borelSpace_localBorel CubicInduction.exists_forall_norm_setIntegral_annulus_setIntegral_compl_ball_jacquetWindow_le CubicInduction.exists_forall_norm_dualZetaRemainder_outside_annulus_le CubicInduction.localZeta_truncPsi_mul_coupled_eq_localZeta_of_forall_eq_integral_jacquetWindow CubicInduction.tendsto_setIntegral_annulus_setIntegral_ball_jacquetWindow_sub_jacquetValue CubicInduction.localZeta_primedDual_eq_pieces_add_setIntegral_annulus_of_forall_eq_zero"
namespace CubicInduction
p2m_export "LanglandsTunnell.CubicInduction" "lowerUnipotent21 longWeyl3 longWeyl3_coe weylPrime3 weylPrime3_coe transposeInv3_weylPrime3 transposeInv3_lowerUnipotent21 gl3AmbientRightTranslate gl3AmbientRightTranslate_apply transposeInv3 upperUnipotent3 upperUnipotent3_coe embedMat2 iotaGL coe_iotaGL LocalGL3 diagUnitGL2 coe_diagUnitGL2 unipotentBall3 mem_unipotentBall3_iff upperUnipotent3_mul_upperUnipotent3 jacquetHaar3 jacquetTruncated3 jacquetLevel jacquetValue jacquetTruncated3_eq_jacquetValue jacquetLevel_le bigCell3 mem_bigCell3_iff cellSectionOf cellSectionOf_apply_of_mem cellSectionOf_apply_of_notMem gl3Entry cornerEntry lowerMinor outerMinor gl3Det cellRatio cellValue antidiagonal3 antidiagonal3_coe eventually_valued_eq exists_forall_le_integrableOn_and_jacquetTruncated3_eq_of_cellSectionOf exists_forall_norm_setIntegral_annulus_setIntegral_compl_ball_jacquetWindow_le exists_forall_norm_dualZetaRemainder_outside_annulus_le localZeta_truncPsi_mul_coupled_eq_localZeta_of_forall_eq_integral_jacquetWindow tendsto_setIntegral_annulus_setIntegral_ball_jacquetWindow_sub_jacquetValue localZeta_primedDual_eq_pieces_add_setIntegral_annulus_of_forall_eq_zero"
p2m_open "LanglandsTunnell.CubicInduction LanglandsTunnell"

variable (v : HeightOneSpectrum (𝓞 ℚ))

private theorem primedKernel_coe_units (ν : Fin 3 → ((v.adicCompletion ℚ)ˣ →* ℂˣ))
    (Φ : (Fin 3 → v.adicCompletion ℚ) → ℂ) (c : ℤ)
    (a : (v.adicCompletion ℚ)ˣ) (x : v.adicCompletion ℚ) :
    primedKernel v ν Φ c a x = jacquetPrimed3 v ν Φ c a x := by
  simp only [primedKernel, dif_neg a.ne_zero, Units.mk0_val]

private theorem valueKernel_coe_units (ν : Fin 3 → ((v.adicCompletion ℚ)ˣ →* ℂˣ))
    (Φ : (Fin 3 → v.adicCompletion ℚ) → ℂ)
    (a : (v.adicCompletion ℚ)ˣ) (x : v.adicCompletion ℚ) :
    valueKernel v ν Φ a x = jacquetValue v (dualTranslate v ν Φ a x) := by
  simp only [valueKernel, dif_neg a.ne_zero, Units.mk0_val]

private theorem dualFnPrimed_coe_units (ν : Fin 3 → ((v.adicCompletion ℚ)ˣ →* ℂˣ))
    (Φ : (Fin 3 → v.adicCompletion ℚ) → ℂ) (c : ℤ)
    (a : (v.adicCompletion ℚ)ˣ) :
    dualFnPrimed v ν Φ c a =
      (∫ x : v.adicCompletion ℚ, primedKernel v ν Φ c a x ∂(selfDualHaarAt ℚ v)) *
        ((modulus (a : v.adicCompletion ℚ) : ℝ) : ℂ)⁻¹ := by
  simp only [dualFnPrimed, primedKernel, dif_neg a.ne_zero, Units.mk0_val]

private theorem tendsto_pieceW
    (ν : Fin 3 → ((v.adicCompletion ℚ)ˣ →* ℂˣ)) (hν : ∀ i, IsLocallyConstant (ν i))
    (Φ : (Fin 3 → v.adicCompletion ℚ) → ℂ) (hΦl : IsLocallyConstant Φ) (hΦc : HasCompactSupport Φ)
    (χ : (v.adicCompletion ℚ)ˣ →* ℂˣ) (hχ : IsLocallyConstant χ)
    (hu : ∀ i, ‖(((ν i * χ) (NumberField.AdelicLevel.uniformizerUnit ℚ v) : ℂˣ) : ℂ)‖ = 1)
    (s : ℂ) (_hs : 0 < s.re) (_hs' : s.re < 1) (N R : ℕ) :
    Filter.Tendsto (fun c : ℤ => pieceW v ν Φ χ s N R c) Filter.atTop (nhds 0) :=
  LanglandsTunnell.CubicInduction.tendsto_setIntegral_annulus_setIntegral_ball_jacquetWindow_sub_jacquetValue v ν hν Φ
    hΦl hΦc χ hχ hu s (primedKernel v ν Φ) (primedKernel_coe_units v ν Φ) (valueKernel v ν Φ)
    (valueKernel_coe_units v ν Φ) N R

private theorem exists_forall_norm_pieceX_le
    (ν : Fin 3 → ((v.adicCompletion ℚ)ˣ →* ℂˣ)) (hν : ∀ i, IsLocallyConstant (ν i))
    (Φ : (Fin 3 → v.adicCompletion ℚ) → ℂ) (hΦl : IsLocallyConstant Φ) (hΦc : HasCompactSupport Φ)
    (χ : (v.adicCompletion ℚ)ˣ →* ℂˣ) (hχ : IsLocallyConstant χ)
    (hu : ∀ i, ‖(((ν i * χ) (NumberField.AdelicLevel.uniformizerUnit ℚ v) : ℂˣ) : ℂ)‖ = 1)
    (s : ℂ) (hs : 0 < s.re) (hs' : s.re < 1) (N : ℕ) :
    ∃ ρ : ℕ → ℝ, Filter.Tendsto ρ Filter.atTop (nhds 0) ∧
      ∀ (R : ℕ) (c : ℤ), ‖pieceX v ν Φ χ s N R c‖ ≤ ρ R :=
  LanglandsTunnell.CubicInduction.exists_forall_norm_setIntegral_annulus_setIntegral_compl_ball_jacquetWindow_le v ν hν
    Φ hΦl hΦc χ hχ hu s hs hs' (primedKernel v ν Φ) (primedKernel_coe_units v ν Φ) N

private theorem exists_forall_norm_pieceY_le
    (ν : Fin 3 → ((v.adicCompletion ℚ)ˣ →* ℂˣ)) (hν : ∀ i, IsLocallyConstant (ν i))
    (Φ : (Fin 3 → v.adicCompletion ℚ) → ℂ) (hΦl : IsLocallyConstant Φ) (hΦc : HasCompactSupport Φ)
    (χ : (v.adicCompletion ℚ)ˣ →* ℂˣ) (hχ : IsLocallyConstant χ)
    (hu : ∀ i, ‖(((ν i * χ) (NumberField.AdelicLevel.uniformizerUnit ℚ v) : ℂˣ) : ℂ)‖ = 1)
    (s : ℂ) (hs : 0 < s.re) (hs' : s.re < 1) :
    ∃ ρ : ℕ → ℝ, Filter.Tendsto ρ Filter.atTop (nhds 0) ∧
      ∀ (N : ℕ) (c : ℤ), ‖pieceY v ν Φ χ s N c‖ ≤ ρ N :=
  LanglandsTunnell.CubicInduction.exists_forall_norm_dualZetaRemainder_outside_annulus_le v ν hν Φ hΦl hΦc χ hχ hu s hs
    hs' (primedKernel v ν Φ) (primedKernel_coe_units v ν Φ)

private theorem localZeta_dualFnPrimed_eq_pieceW_add_pieceX_add_pieceY_add_setIntegral_annulus
    (ν : Fin 3 → ((v.adicCompletion ℚ)ˣ →* ℂˣ)) (hν : ∀ i, IsLocallyConstant (ν i))
    (Φ : (Fin 3 → v.adicCompletion ℚ) → ℂ) (hΦl : IsLocallyConstant Φ) (hΦc : HasCompactSupport Φ)
    (χ : (v.adicCompletion ℚ)ˣ →* ℂˣ) (hχ : IsLocallyConstant χ)
    (hu : ∀ i, ‖(((ν i * χ) (NumberField.AdelicLevel.uniformizerUnit ℚ v) : ℂˣ) : ℂ)‖ = 1)
    (s : ℂ) (hs : 0 < s.re) (hs' : s.re < 1)
    (hint : Integrable (fun x => dualFn v ν Φ x * charExt χ⁻¹ x * ((modulus x : ℝ) : ℂ) ^ (1 - s))
      (mulMeasure (selfDualHaarAt ℚ v)))
    (N R : ℕ) (hR : ∀ (a : (v.adicCompletion ℚ)ˣ) (x : v.adicCompletion ℚ), WithZero.exp (R : ℤ) < Valued.v x →
      jacquetValue v (dualTranslate v ν Φ a x) = 0)
    (c : ℤ) :
    localZeta (selfDualHaarAt ℚ v) (dualFnPrimed v ν Φ c) χ⁻¹ (1 - s) =
      pieceW v ν Φ χ s N R c + pieceX v ν Φ χ s N R c + pieceY v ν Φ χ s N c +
        ∫ a in annulus v N, dualFn v ν Φ a * charExt χ⁻¹ a * ((modulus a : ℝ) : ℂ) ^ (1 - s)
          ∂(mulMeasure (selfDualHaarAt ℚ v)) :=
  LanglandsTunnell.CubicInduction.localZeta_primedDual_eq_pieces_add_setIntegral_annulus_of_forall_eq_zero v ν hν Φ hΦl
    hΦc χ hχ hu s hs hs' (dualFn v ν Φ) (dualFn_coe_units v ν Φ) hint (primedKernel v ν Φ)
    (primedKernel_coe_units v ν Φ) (valueKernel v ν Φ) (valueKernel_coe_units v ν Φ) (dualFnPrimed v ν Φ)
    (dualFnPrimed_coe_units v ν Φ) N R
    (fun a x hx => by simpa only [valueKernel, dif_neg a.ne_zero, Units.mk0_val] using hR a x hx) c

private theorem gaussIntegral_mul_gaussIntegral_mul_coupledIntegral_eq_localZeta_dualFnPrimed
    (ν : Fin 3 → ((v.adicCompletion ℚ)ˣ →* ℂˣ)) (hν : ∀ i, IsLocallyConstant (ν i))
    (Φ : (Fin 3 → v.adicCompletion ℚ) → ℂ) (hΦl : IsLocallyConstant Φ) (hΦc : HasCompactSupport Φ)
    (χ : (v.adicCompletion ℚ)ˣ →* ℂˣ) (hχ : IsLocallyConstant χ)
    (hu : ∀ i, ‖(((ν i * χ) (NumberField.AdelicLevel.uniformizerUnit ℚ v) : ℂˣ) : ℂ)‖ = 1)
    (s : ℂ) (hs : 0 < s.re) (hs' : s.re < 1) (c : ℤ) :
    gaussIntegral v (ν 0 * χ)⁻¹ (1 - s) c * gaussIntegral v (ν 1 * χ)⁻¹ (1 - s) c *
        coupledIntegral v ν Φ χ s c =
      localZeta (selfDualHaarAt ℚ v) (dualFnPrimed v ν Φ c) χ⁻¹ (1 - s) :=
  LanglandsTunnell.CubicInduction.localZeta_truncPsi_mul_coupled_eq_localZeta_of_forall_eq_integral_jacquetWindow v ν
    hν Φ hΦl hΦc χ hχ hu s hs hs' (primedKernel v ν Φ) (primedKernel_coe_units v ν Φ) (dualFnPrimed v ν Φ)
    (dualFnPrimed_coe_units v ν Φ) c

end LanglandsTunnell.CubicInduction
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_tendsto_localZeta_truncPsi_mul_coupled_of_forall_eq_integral_jacquetValue.LaurentZetaSlot"
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_tendsto_localZeta_truncPsi_mul_coupled_of_forall_eq_integral_jacquetValue.LaurentZetaSlot"

end PieceBridges
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_tendsto_localZeta_truncPsi_mul_coupled_of_forall_eq_integral_jacquetValue.LaurentZetaSlot"

section Part40
set_option autoImplicit false

open MeasureTheory
open IsDedekindDomain
open NumberField
p2m_open "LanglandsTunnell.TateLocal P2MW.S_LanglandsTunnell_CubicInduction_tendsto_localZeta_truncPsi_mul_coupled_of_forall_eq_integral_jacquetValue.LanglandsTunnell.TateLocal"

attribute [local instance] LanglandsTunnell.TateLocal.localBorel

namespace LanglandsTunnell
p2m_export "LanglandsTunnell" "TateLocal.localBorel TateLocal.borelSpace_localBorel CubicInduction.exists_forall_norm_setIntegral_annulus_setIntegral_compl_ball_jacquetWindow_le CubicInduction.exists_forall_norm_dualZetaRemainder_outside_annulus_le CubicInduction.localZeta_truncPsi_mul_coupled_eq_localZeta_of_forall_eq_integral_jacquetWindow CubicInduction.tendsto_setIntegral_annulus_setIntegral_ball_jacquetWindow_sub_jacquetValue CubicInduction.localZeta_primedDual_eq_pieces_add_setIntegral_annulus_of_forall_eq_zero"
namespace CubicInduction
p2m_export "LanglandsTunnell.CubicInduction" "lowerUnipotent21 longWeyl3 longWeyl3_coe weylPrime3 weylPrime3_coe transposeInv3_weylPrime3 transposeInv3_lowerUnipotent21 gl3AmbientRightTranslate gl3AmbientRightTranslate_apply transposeInv3 upperUnipotent3 upperUnipotent3_coe embedMat2 iotaGL coe_iotaGL LocalGL3 diagUnitGL2 coe_diagUnitGL2 unipotentBall3 mem_unipotentBall3_iff upperUnipotent3_mul_upperUnipotent3 jacquetHaar3 jacquetTruncated3 jacquetLevel jacquetValue jacquetTruncated3_eq_jacquetValue jacquetLevel_le bigCell3 mem_bigCell3_iff cellSectionOf cellSectionOf_apply_of_mem cellSectionOf_apply_of_notMem gl3Entry cornerEntry lowerMinor outerMinor gl3Det cellRatio cellValue antidiagonal3 antidiagonal3_coe eventually_valued_eq exists_forall_le_integrableOn_and_jacquetTruncated3_eq_of_cellSectionOf exists_forall_norm_setIntegral_annulus_setIntegral_compl_ball_jacquetWindow_le exists_forall_norm_dualZetaRemainder_outside_annulus_le localZeta_truncPsi_mul_coupled_eq_localZeta_of_forall_eq_integral_jacquetWindow tendsto_setIntegral_annulus_setIntegral_ball_jacquetWindow_sub_jacquetValue localZeta_primedDual_eq_pieces_add_setIntegral_annulus_of_forall_eq_zero"
p2m_open "LanglandsTunnell.CubicInduction LanglandsTunnell"

variable (v : HeightOneSpectrum (𝓞 ℚ))

private theorem exists_forall_exp_lt_valued_imp_jacquetValue_dualTranslate_eq_zero
    (ν : Fin 3 → ((v.adicCompletion ℚ)ˣ →* ℂˣ)) (hν : ∀ i, IsLocallyConstant (ν i))
    (Φ : (Fin 3 → v.adicCompletion ℚ) → ℂ) (hΦl : IsLocallyConstant Φ) (hΦc : HasCompactSupport Φ) :
    ∃ R₀ : ℕ, ∀ R : ℕ, R₀ ≤ R → ∀ (a : (v.adicCompletion ℚ)ˣ) (x : v.adicCompletion ℚ),
      WithZero.exp (R : ℤ) < Valued.v x → jacquetValue v (dualTranslate v ν Φ a x) = 0 := by
  obtain ⟨X₀, hX₀⟩ := exists_forall_lt_norm_jacquetValue_dualTranslate_eq_zero v ν Φ hν hΦl hΦc
  obtain ⟨R₀, hR₀⟩ := pow_unbounded_of_one_lt X₀ (one_lt_absNorm_real v)
  refine ⟨R₀, fun R hR a x hx => hX₀ a x ?_⟩
  have hx0 : x ≠ 0 := by
    rintro rfl
    rw [map_zero] at hx
    exact lt_irrefl _ (WithZero.exp_pos.trans hx)
  have h := (rv_lt_rv_iff v WithZero.exp_ne_zero (valued_ne_zero v hx0)).mpr hx
  rw [rv_exp, rv_valued v hx0, modulus_real_eq_norm, zpow_natCast] at h
  calc X₀ < (Ideal.absNorm v.asIdeal : ℝ) ^ R₀ := hR₀
    _ ≤ (Ideal.absNorm v.asIdeal : ℝ) ^ R := pow_le_pow_right₀ (one_lt_absNorm_real v).le hR
    _ < ‖x‖ := h

private theorem tendsto_gaussIntegral_mul_coupledIntegral_localZeta_dualFn_of_pieces
    (ν : Fin 3 → ((v.adicCompletion ℚ)ˣ →* ℂˣ)) (hν : ∀ i, IsLocallyConstant (ν i))
    (Φ : (Fin 3 → v.adicCompletion ℚ) → ℂ) (hΦl : IsLocallyConstant Φ) (hΦc : HasCompactSupport Φ)
    (χ : (v.adicCompletion ℚ)ˣ →* ℂˣ) (hχ : IsLocallyConstant χ)
    (hu : ∀ i, ‖(((ν i * χ) (NumberField.AdelicLevel.uniformizerUnit ℚ v) : ℂˣ) : ℂ)‖ = 1)
    (s : ℂ) (hs : 0 < s.re) (hs' : s.re < 1)
    (hint : Integrable (fun x => dualFn v ν Φ x * charExt χ⁻¹ x * ((modulus x : ℝ) : ℂ) ^ (1 - s))
      (mulMeasure (selfDualHaarAt ℚ v))) :
    Filter.Tendsto
      (fun c : ℤ => gaussIntegral v (ν 0 * χ)⁻¹ (1 - s) c * gaussIntegral v (ν 1 * χ)⁻¹ (1 - s) c *
        coupledIntegral v ν Φ χ s c)
      Filter.atTop (nhds (localZeta (selfDualHaarAt ℚ v) (dualFn v ν Φ) χ⁻¹ (1 - s))) := by
  obtain ⟨ρY, hρY, hY⟩ := exists_forall_norm_pieceY_le v ν hν Φ hΦl hΦc χ hχ hu s hs hs'
  have hZN := tendsto_setIntegral_annulus_localZeta_dualFn v ν Φ χ s hint
  obtain ⟨R₀, hR₀⟩ := exists_forall_exp_lt_valued_imp_jacquetValue_dualTranslate_eq_zero v ν hν Φ hΦl hΦc
  rw [Metric.tendsto_atTop]
  intro ε hε
  have hε4 : 0 < ε / 4 := by positivity

  obtain ⟨N₁, hN₁⟩ := Metric.tendsto_atTop.mp hρY (ε / 4) hε4
  obtain ⟨N₂, hN₂⟩ := Metric.tendsto_atTop.mp hZN (ε / 4) hε4
  set N : ℕ := max N₁ N₂ with hN_def
  have hYε : ∀ c : ℤ, ‖pieceY v ν Φ χ s N c‖ < ε / 4 := fun c => by
    have h := hN₁ N (le_max_left _ _)
    rw [Real.dist_eq, sub_zero] at h
    exact (hY N c).trans_lt (abs_lt.mp h).2
  have hZε : ‖(∫ a in annulus v N, dualFn v ν Φ a * charExt χ⁻¹ a * ((modulus a : ℝ) : ℂ) ^ (1 - s)
      ∂(mulMeasure (selfDualHaarAt ℚ v))) - localZeta (selfDualHaarAt ℚ v) (dualFn v ν Φ) χ⁻¹ (1 - s)‖ < ε / 4 := by
    rw [← dist_eq_norm]
    exact hN₂ N (le_max_right _ _)

  obtain ⟨ρX, hρX, hX⟩ := exists_forall_norm_pieceX_le v ν hν Φ hΦl hΦc χ hχ hu s hs hs' N
  obtain ⟨R₁, hR₁⟩ := Metric.tendsto_atTop.mp hρX (ε / 4) hε4
  set R : ℕ := max R₁ R₀ with hR_def
  have hXε : ∀ c : ℤ, ‖pieceX v ν Φ χ s N R c‖ < ε / 4 := fun c => by
    have h := hR₁ R (le_max_left _ _)
    rw [Real.dist_eq, sub_zero] at h
    exact (hX R c).trans_lt (abs_lt.mp h).2
  have hRv := hR₀ R (le_max_right _ _)

  obtain ⟨c₀, hc₀⟩ :=
    Metric.tendsto_atTop.mp (tendsto_pieceW v ν hν Φ hΦl hΦc χ hχ hu s hs hs' N R) (ε / 4) hε4
  refine ⟨c₀, fun c hc => ?_⟩
  have hWε : ‖pieceW v ν Φ χ s N R c‖ < ε / 4 := by
    have h := hc₀ c hc
    rwa [dist_zero_right] at h

  have hF1 := gaussIntegral_mul_gaussIntegral_mul_coupledIntegral_eq_localZeta_dualFnPrimed v ν hν Φ hΦl hΦc χ hχ hu
    s hs hs' c
  have hdec := localZeta_dualFnPrimed_eq_pieceW_add_pieceX_add_pieceY_add_setIntegral_annulus v ν hν Φ hΦl hΦc χ hχ
    hu s hs hs' hint N R hRv c
  rw [hF1, hdec, dist_eq_norm]
  set W : ℂ := pieceW v ν Φ χ s N R c with hW_def
  set X : ℂ := pieceX v ν Φ χ s N R c with hX_def
  set Y : ℂ := pieceY v ν Φ χ s N c with hY_def
  set ZN : ℂ := ∫ a in annulus v N, dualFn v ν Φ a * charExt χ⁻¹ a * ((modulus a : ℝ) : ℂ) ^ (1 - s)
    ∂(mulMeasure (selfDualHaarAt ℚ v)) with hZN_def
  set Z : ℂ := localZeta (selfDualHaarAt ℚ v) (dualFn v ν Φ) χ⁻¹ (1 - s) with hZ_def
  calc ‖W + X + Y + ZN - Z‖ = ‖W + X + Y + (ZN - Z)‖ := by rw [add_sub_assoc]
    _ ≤ ‖W + X + Y‖ + ‖ZN - Z‖ := norm_add_le _ _
    _ ≤ ‖W + X‖ + ‖Y‖ + ‖ZN - Z‖ := add_le_add (norm_add_le _ _) le_rfl
    _ ≤ ‖W‖ + ‖X‖ + ‖Y‖ + ‖ZN - Z‖ := add_le_add (add_le_add (norm_add_le _ _) le_rfl) le_rfl
    _ < ε / 4 + ε / 4 + ε / 4 + ε / 4 := add_lt_add (add_lt_add (add_lt_add hWε (hXε c)) (hYε c)) hZε
    _ = ε := by ring

end LanglandsTunnell.CubicInduction
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_tendsto_localZeta_truncPsi_mul_coupled_of_forall_eq_integral_jacquetValue.LaurentZetaSlot"
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_tendsto_localZeta_truncPsi_mul_coupled_of_forall_eq_integral_jacquetValue.LaurentZetaSlot"

end Part40
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_tendsto_localZeta_truncPsi_mul_coupled_of_forall_eq_integral_jacquetValue.LaurentZetaSlot"

attribute [local instance] LanglandsTunnell.TateLocal.localBorel in
open _root_.LanglandsTunnell.CubicInduction _root_.P2MW.S_LanglandsTunnell_CubicInduction_tendsto_localZeta_truncPsi_mul_coupled_of_forall_eq_integral_jacquetValue.LanglandsTunnell.CubicInduction in
open MeasureTheory IsDedekindDomain NumberField NumberField.StandardAddChar _root_.LanglandsTunnell.TateLocal _root_.P2MW.S_LanglandsTunnell_CubicInduction_tendsto_localZeta_truncPsi_mul_coupled_of_forall_eq_integral_jacquetValue.LanglandsTunnell.TateLocal in

theorem solution
    (v : HeightOneSpectrum (𝓞 ℚ))
    (ν : Fin 3 → ((v.adicCompletion ℚ)ˣ →* ℂˣ)) (hν : ∀ i, IsLocallyConstant (ν i))
    (Φ : (Fin 3 → v.adicCompletion ℚ) → ℂ) (hΦl : IsLocallyConstant Φ) (hΦc : HasCompactSupport Φ)
    (χ : (v.adicCompletion ℚ)ˣ →* ℂˣ) (hχ : IsLocallyConstant χ)
    (hu : ∀ i, ‖(((ν i * χ) (NumberField.AdelicLevel.uniformizerUnit ℚ v) : ℂˣ) : ℂ)‖ = 1)
    (s : ℂ) (hs : 0 < s.re) (hs' : s.re < 1)
    (F : v.adicCompletion ℚ → ℂ)
    (hF : ∀ a : (v.adicCompletion ℚ)ˣ,
      letI := localBorel ℚ v
      F a =
        (∫ x : v.adicCompletion ℚ,
            jacquetValue v (gl3AmbientRightTranslate (R := ℂ)
              (longWeyl3 * transposeInv3 (iotaGL (diagUnitGL2 a) * lowerUnipotent21 x *
                (weylPrime3 * transposeInv3 1)) * antidiagonal3 v) (cellSectionOf v ν Φ))
          ∂(selfDualHaarAt ℚ v)) *
          ((modulus (a : v.adicCompletion ℚ) : ℝ) : ℂ)⁻¹)
    (hint :
      letI := localBorel ℚ v
      Integrable (fun x => F x * charExt χ⁻¹ x * ((modulus x : ℝ) : ℂ) ^ (1 - s))
        (mulMeasure (selfDualHaarAt ℚ v))) :
    letI := localBorel ℚ v
    Filter.Tendsto
      (fun c : ℤ =>
        localZeta (selfDualHaarAt ℚ v)
            (fun t => if Valued.v (-t) ≤ WithZero.exp c then (psiLocal ℚ v (-t) : ℂ) else 0) (ν 0 * χ)⁻¹ (1 - s) *
          localZeta (selfDualHaarAt ℚ v)
            (fun t => if Valued.v (-t) ≤ WithZero.exp c then (psiLocal ℚ v (-t) : ℂ) else 0) (ν 1 * χ)⁻¹ (1 - s) *
          (∫ p : v.adicCompletion ℚ × v.adicCompletion ℚ × v.adicCompletion ℚ,
              Φ ![p.1, p.2.1, p.2.2] *
                (charExt (ν 2 * χ)⁻¹ p.1 * ((modulus p.1 : ℝ) : ℂ) ^ (1 - s)) *
                (charExt (ν 1 * χ) p.2.1 * ((modulus p.2.1 : ℝ) : ℂ) ^ s) *
                (charExt (ν 0 * (ν 1)⁻¹) (p.2.1 - p.1 * p.2.2) *
                  ((modulus (p.2.1 - p.1 * p.2.2) : ℝ) : ℂ)⁻¹) *
                (if Valued.v (p.2.2 / (p.2.1 - p.1 * p.2.2)) ≤ WithZero.exp c then
                  (psiLocal ℚ v (p.2.2 / (p.2.1 - p.1 * p.2.2)) : ℂ)
                else 0)
            ∂((mulMeasure (selfDualHaarAt ℚ v)).prod
              ((mulMeasure (selfDualHaarAt ℚ v)).prod (selfDualHaarAt ℚ v)))))
      Filter.atTop (nhds (localZeta (selfDualHaarAt ℚ v) F χ⁻¹ (1 - s))) := by
  have hfun : (fun x => F x * charExt χ⁻¹ x * ((modulus x : ℝ) : ℂ) ^ (1 - s)) =
      fun x => dualFn v ν Φ x * charExt χ⁻¹ x * ((modulus x : ℝ) : ℂ) ^ (1 - s) := by
    funext x
    by_cases hx : x = 0
    · subst hx
      simp only [charExt_zero, mul_zero, zero_mul]
    · have h1 := hF (Units.mk0 x hx)
      have h2 := dualFn_coe_units v ν Φ (Units.mk0 x hx)
      simp only [Units.val_mk0] at h1 h2
      rw [h1.trans h2.symm]
  have hz : localZeta (selfDualHaarAt ℚ v) F χ⁻¹ (1 - s) =
      localZeta (selfDualHaarAt ℚ v) (dualFn v ν Φ) χ⁻¹ (1 - s) := by
    unfold localZeta
    exact congrArg (fun g : v.adicCompletion ℚ → ℂ => ∫ x, g x ∂(mulMeasure (selfDualHaarAt ℚ v))) hfun
  have hint' : Integrable (fun x => dualFn v ν Φ x * charExt χ⁻¹ x * ((modulus x : ℝ) : ℂ) ^ (1 - s))
      (mulMeasure (selfDualHaarAt ℚ v)) := by
    have h0 : Integrable (fun x => F x * charExt χ⁻¹ x * ((modulus x : ℝ) : ℂ) ^ (1 - s))
        (mulMeasure (selfDualHaarAt ℚ v)) := hint
    rwa [hfun] at h0
  have h :=
    tendsto_gaussIntegral_mul_coupledIntegral_localZeta_dualFn_of_pieces v ν hν Φ hΦl hΦc χ hχ hu s hs hs' hint'
  rw [← hz] at h
  exact h

end S_LanglandsTunnell_CubicInduction_tendsto_localZeta_truncPsi_mul_coupled_of_forall_eq_integral_jacquetValue
end P2MW
export P2MW.S_LanglandsTunnell_CubicInduction_tendsto_localZeta_truncPsi_mul_coupled_of_forall_eq_integral_jacquetValue (solution)
