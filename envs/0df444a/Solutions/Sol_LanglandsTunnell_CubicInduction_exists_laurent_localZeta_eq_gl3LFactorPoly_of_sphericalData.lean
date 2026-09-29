-- Prove2me | solution 1 for LanglandsTunnell.CubicInduction.exists_laurent_localZeta_eq_gl3LFactorPoly_of_sphericalData
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.353894+00:00
-- url     : https://prove2.me/submissions/2e763a66-4174-501b-a094-a05223db2fa6

import Definitions.Def_JPSS_CubicLiftFactor
import Definitions.Def_LanglandsTunnell_CubicInduction_LocalZeta31
import Definitions.Def_LanglandsTunnell_CubicInduction_Structure
import Definitions.Def_LanglandsTunnell_StandardLocalConstantsAt
import Theorems.Thm_LanglandsTunnell_CubicInduction_eq_zero_of_coe_eq_diagonal_of_valued_lt_of_isGL3PsiWhittakerFn
import Theorems.Thm_LanglandsTunnell_CubicInduction_eq_zero_of_isCosetEigenfunction_of_isGL3PsiWhittakerFn_of_apply_one_eq_zero
import Theorems.Thm_LanglandsTunnell_CubicInduction_exists_eq_upperUnipotent3_mul_diagonal_mul_mem_localMaximalCompact3
import Theorems.Thm_LanglandsTunnell_CubicInduction_isGL3PsiWhittakerFn_dualWhittakerFn3
import Theorems.Thm_LanglandsTunnell_CubicInduction_sphericalTorusValue_eq_of_isCosetEigenfunction_of_isGL3PsiWhittakerFn
import Theorems.Thm_LanglandsTunnell_TateLocal_addCharLevel_psiLocal_rat
import Theorems.Thm_LanglandsTunnell_TateLocal_forall_eq_one_and_exists_ne_one_of_addCharLevel
import Theorems.Thm_LanglandsTunnell_TateLocal_localZeta_stdTestFunAt_eq_real_image_higherUnitsAt
import Theorems.Thm_LanglandsTunnell_TateLocal_localZeta_tateFourier_stdTestFunAt
import Theorems.Thm_LanglandsTunnell_TateLocal_measureReal_setOf_valued_le_exp
import Theorems.Thm_LanglandsTunnell_TateLocal_modulus_adicCompletion_eq_nnnorm
import Theorems.Thm_LanglandsTunnell_TateLocal_psiLocal_eq_one_of_mem_integers
import Theorems.Thm_LanglandsTunnell_TateLocal_psiLocal_ne_one
import Theorems.Thm_LanglandsTunnell_TateLocal_selfDualHaarAt_real_image_higherUnitsAt
import Theorems.Thm_LanglandsTunnell_TateLocal_selfDualHaarAt_real_integers_mul_real_setOf_valued_le_exp_addCharLevel
import Theorems.Thm_LanglandsTunnell_TateLocal_setIntegral_addChar_mul_charExt_mul_setIntegral_inv_mul_pow_eq
import Theorems.Thm_LanglandsTunnell_TateLocal_tateFourier_indicator_setOf_valued_sub_le
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

p2m_attr_erase "ext" "IsDedekindDomain.HeightOneSpectrum.adicCompletion.ext"
namespace P2MW.S_LanglandsTunnell_CubicInduction_exists_laurent_localZeta_eq_gl3LFactorPoly_of_sphericalData
p2m_attr_erase "instance" "instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions instCountableOfNumberField_definitions IsDedekindDomain.HeightOneSpectrum.Extension.instAlgebraSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnder IsDedekindDomain.HeightOneSpectrum.Extension.instAlgebraSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnder_1 IsDedekindDomain.HeightOneSpectrum.instMulActionHomClassAlgHomTensorProductAdicCompletionForallValEqUnder_definitions IsDedekindDomain.HeightOneSpectrum.Extension.instAlgebraAdicCompletionValEqUnder IsDedekindDomain.HeightOneSpectrum.adicCompletion.instFiniteForallValEqUnderOfFiniteDimensional_definitions IsDedekindDomain.HeightOneSpectrum.instIsBiscalarSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersTensorProductCoeAlgHomTensorAdicCompletionIntegersTo IsDedekindDomain.HeightOneSpectrum.Extension.instContinuousSMulAdicCompletionValEqUnder IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsModuleTopology IsDedekindDomain.HeightOneSpectrum.Extension.instFiniteSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnderOfFiniteDimensional IsDedekindDomain.HeightOneSpectrum.adicCompletion.instFiniteValEqUnderOfFiniteDimensional_definitions instIsBiscalarTensorProductCoeAlgHomBaseChange_of_algebraMap IsDedekindDomain.HeightOneSpectrum.instIsScalarTowerSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnder_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsModuleTopologyPi Submodule.instIsTopologicalModuleSubtypeMem Pi.instTopologicalModule IsTopologicalModule.toContinuousSMul IsTopologicalModule.toContinuousAdd instFunLike SemialgHomClass.toSemilinearMapClass instCoeTCSemialgHom SemialgHomClass.toRingHomClass SemialgHomClass.instSemialgHom"
p2m_attr_erase "simp" "SemialgHom.baseChange_of_algebraMap_tmul_left SemialgHom.baseChangeRightOfAlgebraMap_apply Pi.semialgHomPi_apply Pi.semialgHom_apply Module.Basis.rightBaseChange_apply LinearEquiv.coe_mulLeft LinearEquiv.coe_mulRight WithVal.semialgebraMap_toFun_ofVal Module.Basis.rightBaseChange_repr IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers.tensorCoe_tmul IsDedekindDomain.HeightOneSpectrum.tensorAdicCompletionIntegersTo_tmul SemialgHom.baseChangeRightOfAlgebraMap_coe IsDedekindDomain.HeightOneSpectrum.adicCompletion.integerBaseChangeLinearEquiv_tmul_apply SemialgHom.baseChange_of_algebraMap_tmul_right IsLocalization.map_moduleTensorEquiv_symm_tmul IsLocalization.leftModuleTensorEquiv_apply IsLocalization.moduleLid_symm_apply IsLocalization.leftModuleTensorEquiv_symm_apply IsLocalization.map_moduleTensorEquiv_tmul IsModuleTopology.continuousLinearEquiv_apply AlgEquiv.extendScalars_symm_apply IsModuleTopology.Module.Basis.equivFun_homeo_symm_apply IsModuleTopology.Module.Basis.equivFun_homeo_apply IsModuleTopology.continuousAlgEquivOfIsBiscalar_apply AlgEquiv.extendScalars_apply IsModuleTopology.continuousLinearEquiv_symm_apply SemialgHom.restrictScalars_toFun SemialgHom.mk.sizeOf_spec SemialgHom.mk.injEq SemialgHom.coe_coe coe_mk TensorProduct.RightActions.smul_def TensorProduct.RightActions.Module.TensorProduct.comm_symm_apply_tmul TensorProduct.RightActions.LinearMap.baseChange_id TensorProduct.RightActions.algebraMap_eval TensorProduct.RightActions.Module.TensorProduct.comm_apply_tmul TensorProduct.RightActions.Algebra.TensorProduct.comm_symm_apply_tmul TensorProduct.RightActions.Algebra.TensorProduct.comm_apply_tmul"

section

set_option autoImplicit false

open IsDedekindDomain NumberField NumberField.TateGlobal AutomorphicForm LanglandsTunnell.Converse LanglandsTunnell.RankinSelberg LanglandsTunnell.TateLocal MeasureTheory

p2m_open "LanglandsTunnell.CubicInduction P2MW.S_LanglandsTunnell_CubicInduction_exists_laurent_localZeta_eq_gl3LFactorPoly_of_sphericalData.LanglandsTunnell.CubicInduction Filter Topology Polynomial"

private theorem norm_le_pow_of_cubic_recursion (e₁ e₂ e₃ : ℂ) (h : ℕ → ℂ) (h0 : h 0 = 1) (h1 : h 1 = e₁)
    (h2 : h 2 = e₁ ^ 2 - e₂) (hrec : ∀ n, h (n + 3) = e₁ * h (n + 2) - e₂ * h (n + 1) + e₃ * h n) (n : ℕ) :
    ‖h n‖ ≤ (1 + ‖e₁‖ + ‖e₂‖ + ‖e₃‖) ^ n := by
  obtain ⟨R, hR⟩ : ∃ R : ℝ, R = 1 + ‖e₁‖ + ‖e₂‖ + ‖e₃‖ := ⟨_, rfl⟩
  rw [← hR]
  have hR1 : 1 ≤ R := by rw [hR]; linarith [norm_nonneg e₁, norm_nonneg e₂, norm_nonneg e₃]
  have hR0 : 0 ≤ R := zero_le_one.trans hR1
  have he₁ : ‖e₁‖ ≤ R := by rw [hR]; linarith [norm_nonneg e₂, norm_nonneg e₃]
  have he₁₂ : ‖e₁‖ + ‖e₂‖ ≤ R := by rw [hR]; linarith [norm_nonneg e₃]
  have hsum : ‖e₁‖ + ‖e₂‖ + ‖e₃‖ ≤ R := by rw [hR]; linarith
  suffices H : ∀ n, ‖h n‖ ≤ R ^ n ∧ ‖h (n + 1)‖ ≤ R ^ (n + 1) ∧ ‖h (n + 2)‖ ≤ R ^ (n + 2) from (H n).1
  intro n
  induction n with
  | zero =>
    refine ⟨le_of_eq (by rw [h0, norm_one, pow_zero]), ?_, ?_⟩
    · rw [h1, zero_add, pow_one]
      exact he₁
    · rw [h2, zero_add]
      calc ‖e₁ ^ 2 - e₂‖ ≤ ‖e₁ ^ 2‖ + ‖e₂‖ := norm_sub_le _ _
        _ = ‖e₁‖ * ‖e₁‖ + ‖e₂‖ := by rw [norm_pow, sq]
        _ ≤ R ^ 2 := by
            nlinarith [mul_le_mul_of_nonneg_right he₁ (norm_nonneg e₁), mul_le_mul_of_nonneg_right he₁₂ hR0,
              mul_le_mul_of_nonneg_right hR1 (norm_nonneg e₂), norm_nonneg e₁, norm_nonneg e₂]
  | succ k ih =>
    obtain ⟨ha, hb, hc⟩ := ih
    refine ⟨hb, hc, ?_⟩
    have hR2 : R ^ k ≤ R ^ (k + 2) := pow_le_pow_right₀ hR1 (by omega)
    have hR3 : R ^ (k + 1) ≤ R ^ (k + 2) := pow_le_pow_right₀ hR1 (by omega)
    have hk2 : 0 ≤ R ^ (k + 2) := pow_nonneg hR0 _
    rw [show k + 1 + 2 = k + 3 from rfl, hrec k]
    calc ‖e₁ * h (k + 2) - e₂ * h (k + 1) + e₃ * h k‖
        ≤ ‖e₁ * h (k + 2) - e₂ * h (k + 1)‖ + ‖e₃ * h k‖ := norm_add_le _ _
      _ ≤ ‖e₁ * h (k + 2)‖ + ‖e₂ * h (k + 1)‖ + ‖e₃ * h k‖ := add_le_add (norm_sub_le _ _) le_rfl
      _ = ‖e₁‖ * ‖h (k + 2)‖ + ‖e₂‖ * ‖h (k + 1)‖ + ‖e₃‖ * ‖h k‖ := by rw [norm_mul, norm_mul, norm_mul]
      _ ≤ ‖e₁‖ * R ^ (k + 2) + ‖e₂‖ * R ^ (k + 2) + ‖e₃‖ * R ^ (k + 2) :=
          add_le_add (add_le_add (mul_le_mul_of_nonneg_left hc (norm_nonneg _))
            (mul_le_mul_of_nonneg_left (hb.trans hR3) (norm_nonneg _)))
            (mul_le_mul_of_nonneg_left (ha.trans hR2) (norm_nonneg _))
      _ = (‖e₁‖ + ‖e₂‖ + ‖e₃‖) * R ^ (k + 2) := by ring
      _ ≤ R * R ^ (k + 2) := mul_le_mul_of_nonneg_right hsum hk2
      _ = R ^ (k + 3) := by ring

private theorem cubic_mul_sum_range_of_cubic_recursion (e₁ e₂ e₃ X : ℂ) (h : ℕ → ℂ) (h0 : h 0 = 1) (h1 : h 1 = e₁)
    (h2 : h 2 = e₁ ^ 2 - e₂) (hrec : ∀ n, h (n + 3) = e₁ * h (n + 2) - e₂ * h (n + 1) + e₃ * h n) (N : ℕ) :
    (1 - e₁ * X + e₂ * X ^ 2 - e₃ * X ^ 3) * ∑ n ∈ Finset.range N, h n * X ^ n =
      1 - (h N * X ^ N + (h (N + 1) * X ^ (N + 1) - e₁ * X * (h N * X ^ N)) +
        (h (N + 2) * X ^ (N + 2) - e₁ * X * (h (N + 1) * X ^ (N + 1)) + e₂ * X ^ 2 * (h N * X ^ N))) := by
  induction N with
  | zero =>
    simp only [Finset.range_zero, Finset.sum_empty, mul_zero, zero_add, h0, h1, h2]
    ring
  | succ N ih =>
    rw [Finset.sum_range_succ, mul_add, ih]
    simp only [show N + 1 + 1 = N + 2 from rfl, show N + 1 + 2 = N + 3 from rfl]
    rw [hrec N]
    ring

private theorem summable_mul_pow_of_cubic_recursion (e₁ e₂ e₃ X : ℂ) (h : ℕ → ℂ) (h0 : h 0 = 1) (h1 : h 1 = e₁)
    (h2 : h 2 = e₁ ^ 2 - e₂) (hrec : ∀ n, h (n + 3) = e₁ * h (n + 2) - e₂ * h (n + 1) + e₃ * h n)
    (hX : ‖X‖ * (1 + ‖e₁‖ + ‖e₂‖ + ‖e₃‖) < 1) :
    Summable (fun n : ℕ => h n * X ^ n) := by
  have hbound : ∀ n, ‖h n * X ^ n‖ ≤ (‖X‖ * (1 + ‖e₁‖ + ‖e₂‖ + ‖e₃‖)) ^ n := by
    intro n
    rw [mul_pow, mul_comm (‖X‖ ^ n), norm_mul, norm_pow]
    exact mul_le_mul_of_nonneg_right (norm_le_pow_of_cubic_recursion e₁ e₂ e₃ h h0 h1 h2 hrec n)
      (pow_nonneg (norm_nonneg X) n)
  exact Summable.of_norm_bounded (summable_geometric_of_lt_one (mul_nonneg (norm_nonneg X) (by positivity)) hX)
    hbound

private theorem cubic_mul_tsum_of_cubic_recursion (e₁ e₂ e₃ X : ℂ) (h : ℕ → ℂ) (h0 : h 0 = 1) (h1 : h 1 = e₁)
    (h2 : h 2 = e₁ ^ 2 - e₂) (hrec : ∀ n, h (n + 3) = e₁ * h (n + 2) - e₂ * h (n + 1) + e₃ * h n)
    (hX : ‖X‖ * (1 + ‖e₁‖ + ‖e₂‖ + ‖e₃‖) < 1) :
    (1 - e₁ * X + e₂ * X ^ 2 - e₃ * X ^ 3) * ∑' n : ℕ, h n * X ^ n = 1 := by
  obtain ⟨a, ha⟩ : ∃ a : ℕ → ℂ, a = fun n => h n * X ^ n := ⟨_, rfl⟩
  have hsumm : Summable a := by
    rw [ha]
    exact summable_mul_pow_of_cubic_recursion e₁ e₂ e₃ X h h0 h1 h2 hrec hX
  have hzero : Tendsto a atTop (𝓝 0) := hsumm.tendsto_atTop_zero
  have hzero1 : Tendsto (fun N => a (N + 1)) atTop (𝓝 0) := hzero.comp (tendsto_add_atTop_nat 1)
  have hzero2 : Tendsto (fun N => a (N + 2)) atTop (𝓝 0) := hzero.comp (tendsto_add_atTop_nat 2)
  have htail : Tendsto (fun N => a N + (a (N + 1) - e₁ * X * a N) + (a (N + 2) - e₁ * X * a (N + 1) +
      e₂ * X ^ 2 * a N)) atTop (𝓝 (0 + (0 - e₁ * X * 0) + (0 - e₁ * X * 0 + e₂ * X ^ 2 * 0))) :=
    (hzero.add (hzero1.sub (hzero.const_mul _))).add ((hzero2.sub (hzero1.const_mul _)).add (hzero.const_mul _))
  simp only [mul_zero, sub_zero, add_zero] at htail
  have hpartial : Tendsto (fun N => (1 - e₁ * X + e₂ * X ^ 2 - e₃ * X ^ 3) * ∑ n ∈ Finset.range N, a n) atTop
      (𝓝 ((1 - e₁ * X + e₂ * X ^ 2 - e₃ * X ^ 3) * ∑' n, a n)) :=
    hsumm.hasSum.tendsto_sum_nat.const_mul _
  have hpartial' : Tendsto (fun N => (1 - e₁ * X + e₂ * X ^ 2 - e₃ * X ^ 3) * ∑ n ∈ Finset.range N, a n) atTop
      (𝓝 (1 - 0)) := by
    refine (tendsto_const_nhds.sub htail).congr fun N => ?_
    rw [ha]
    exact (cubic_mul_sum_range_of_cubic_recursion e₁ e₂ e₃ X h h0 h1 h2 hrec N).symm
  have hprod : (1 - e₁ * X + e₂ * X ^ 2 - e₃ * X ^ 3) * ∑' n, a n = 1 := by
    rw [tendsto_nhds_unique hpartial hpartial', sub_zero]
  rw [ha] at hprod
  exact hprod

private theorem hasSum_mul_pow_of_cubic_recursion (e₁ e₂ e₃ X : ℂ) (h : ℕ → ℂ) (h0 : h 0 = 1) (h1 : h 1 = e₁)
    (h2 : h 2 = e₁ ^ 2 - e₂) (hrec : ∀ n, h (n + 3) = e₁ * h (n + 2) - e₂ * h (n + 1) + e₃ * h n)
    (hX : ‖X‖ * (1 + ‖e₁‖ + ‖e₂‖ + ‖e₃‖) < 1) :
    HasSum (fun n : ℕ => h n * X ^ n) (1 - e₁ * X + e₂ * X ^ 2 - e₃ * X ^ 3)⁻¹ := by
  have hfinal := (summable_mul_pow_of_cubic_recursion e₁ e₂ e₃ X h h0 h1 h2 hrec hX).hasSum
  rw [eq_inv_of_mul_eq_one_right (cubic_mul_tsum_of_cubic_recursion e₁ e₂ e₃ X h h0 h1 h2 hrec hX)] at hfinal
  exact hfinal

private theorem sphericalTorusValue_add_three (e₁ e₂ e₃ : ℂ) (n : ℕ) :
    sphericalTorusValue e₁ e₂ e₃ (n + 3) =
      e₁ * sphericalTorusValue e₁ e₂ e₃ (n + 2) - e₂ * sphericalTorusValue e₁ e₂ e₃ (n + 1) +
        e₃ * sphericalTorusValue e₁ e₂ e₃ n := by
  simp only [sphericalTorusValue]

private theorem eval_gl3LFactorPoly (e₁ e₂ e₃ X : ℂ) :
    (gl3LFactorPoly e₁ e₂ e₃).eval X = 1 - e₁ * X + e₂ * X ^ 2 - e₃ * X ^ 3 := by
  simp [gl3LFactorPoly]

private theorem eval_gl3LFactorPoly_twist (t e₁ e₂ e₃ X : ℂ) :
    (gl3LFactorPoly (t * e₁) (t ^ 2 * e₂) (t ^ 3 * e₃)).eval X = (gl3LFactorPoly e₁ e₂ e₃).eval (t * X) := by
  rw [eval_gl3LFactorPoly, eval_gl3LFactorPoly]
  ring

private theorem summable_sphericalTorusValue_mul_pow (e₁ e₂ e₃ X : ℂ) (hX : ‖X‖ * (1 + ‖e₁‖ + ‖e₂‖ + ‖e₃‖) < 1) :
    Summable (fun n : ℕ => sphericalTorusValue e₁ e₂ e₃ n * X ^ n) :=
  summable_mul_pow_of_cubic_recursion e₁ e₂ e₃ X (sphericalTorusValue e₁ e₂ e₃) rfl rfl rfl
    (sphericalTorusValue_add_three e₁ e₂ e₃) hX

private theorem eval_gl3LFactorPoly_mul_tsum_sphericalTorusValue (e₁ e₂ e₃ X : ℂ)
    (hX : ‖X‖ * (1 + ‖e₁‖ + ‖e₂‖ + ‖e₃‖) < 1) :
    (gl3LFactorPoly e₁ e₂ e₃).eval X * ∑' n : ℕ, sphericalTorusValue e₁ e₂ e₃ n * X ^ n = 1 := by
  rw [eval_gl3LFactorPoly]
  exact cubic_mul_tsum_of_cubic_recursion e₁ e₂ e₃ X (sphericalTorusValue e₁ e₂ e₃) rfl rfl rfl
    (sphericalTorusValue_add_three e₁ e₂ e₃) hX

private theorem eval_gl3LFactorPoly_ne_zero (e₁ e₂ e₃ X : ℂ) (hX : ‖X‖ * (1 + ‖e₁‖ + ‖e₂‖ + ‖e₃‖) < 1) :
    (gl3LFactorPoly e₁ e₂ e₃).eval X ≠ 0 :=
  left_ne_zero_of_mul_eq_one (eval_gl3LFactorPoly_mul_tsum_sphericalTorusValue e₁ e₂ e₃ X hX)

private theorem hasSum_sphericalTorusValue_mul_pow (e₁ e₂ e₃ X : ℂ) (hX : ‖X‖ * (1 + ‖e₁‖ + ‖e₂‖ + ‖e₃‖) < 1) :
    HasSum (fun n : ℕ => sphericalTorusValue e₁ e₂ e₃ n * X ^ n) ((gl3LFactorPoly e₁ e₂ e₃).eval X)⁻¹ := by
  rw [eval_gl3LFactorPoly]
  exact hasSum_mul_pow_of_cubic_recursion e₁ e₂ e₃ X (sphericalTorusValue e₁ e₂ e₃) rfl rfl rfl
    (sphericalTorusValue_add_three e₁ e₂ e₃) hX
end

section

set_option autoImplicit false

noncomputable section

section WindowIdentity

private def twoRow (h : ℕ → ℂ) : ℕ → ℕ → ℂ
  | a, 0 => h a
  | a, b + 1 => h a * h (b + 1) - h (a + 1) * h b

private theorem twoRow_zero (h : ℕ → ℂ) (a : ℕ) : twoRow h a 0 = h a := rfl

private theorem twoRow_succ (h : ℕ → ℂ) (a b : ℕ) : twoRow h a (b + 1) = h a * h (b + 1) - h (a + 1) * h b := rfl

private def cubicWindow (h : ℕ → ℂ) (f₁ f₂ Z : ℂ) (K c : ℕ) : ℂ :=
  twoRow h K c + (twoRow h (K + 1) c - f₁ * twoRow h K c) * Z +
    (twoRow h (K + 2) c - f₁ * twoRow h (K + 1) c + f₂ * twoRow h K c) * Z ^ 2

private def shiftBack (h : ℕ → ℂ) : ℕ → ℂ
  | 0 => 0
  | c + 1 => h c

private theorem twoRow_eq_shiftBack (h : ℕ → ℂ) (h0 : h 0 = 1) (a c : ℕ) :
    twoRow h a c = h a * h c - h (a + 1) * shiftBack h c := by
  cases c with
  | zero => simp [twoRow, shiftBack, h0]
  | succ c => simp [twoRow, shiftBack]

private def seqWindow (h : ℕ → ℂ) (f₁ f₂ Z : ℂ) (N : ℕ) : ℂ :=
  h N + (h (N + 1) - f₁ * h N) * Z + (h (N + 2) - f₁ * h (N + 1) + f₂ * h N) * Z ^ 2

private theorem cubicWindow_eq (h : ℕ → ℂ) (h0 : h 0 = 1) (f₁ f₂ Z : ℂ) (K c : ℕ) :
    cubicWindow h f₁ f₂ Z K c = seqWindow h f₁ f₂ Z K * h c - seqWindow h f₁ f₂ Z (K + 1) * shiftBack h c := by
  simp only [cubicWindow, seqWindow, twoRow_eq_shiftBack h h0]
  ring

private theorem seqWindow_eq (h : ℕ → ℂ) (f₁ f₂ f₃ Z : ℂ)
    (hrec : ∀ n, h (n + 3) = f₁ * h (n + 2) - f₂ * h (n + 1) + f₃ * h n) (N : ℕ) :
    seqWindow h f₁ f₂ Z N =
      Z * seqWindow h f₁ f₂ Z (N + 1) + (1 - f₁ * Z + f₂ * Z ^ 2 - f₃ * Z ^ 3) * h N := by
  simp only [seqWindow]
  linear_combination (-(Z ^ 3)) * hrec N

private theorem cubic_mul_sum_range_eq (h : ℕ → ℂ) (f₁ f₂ f₃ Z : ℂ) (h0 : h 0 = 1) (h1 : h 1 = f₁)
    (h2 : h 2 = f₁ ^ 2 - f₂) (hrec : ∀ n, h (n + 3) = f₁ * h (n + 2) - f₂ * h (n + 1) + f₃ * h n) (N : ℕ) :
    (1 - f₁ * Z + f₂ * Z ^ 2 - f₃ * Z ^ 3) * ∑ n ∈ Finset.range N, h n * Z ^ n =
      1 - Z ^ N * seqWindow h f₁ f₂ Z N := by
  rw [cubic_mul_sum_range_of_cubic_recursion f₁ f₂ f₃ Z h h0 h1 h2 hrec N]
  simp only [seqWindow]
  ring

private theorem sum_Ico_class_eq (h : ℕ → ℂ) (f₁ f₂ f₃ Z : ℂ) (h0 : h 0 = 1) (h1 : h 1 = f₁)
    (h2 : h 2 = f₁ ^ 2 - f₂) (hrec : ∀ n, h (n + 3) = f₁ * h (n + 2) - f₂ * h (n + 1) + f₃ * h n)
    (α β : ℂ) (K' lo hi : ℕ) (hlh : lo ≤ hi) :
    ∑ c ∈ Finset.Ico (lo + 1) (hi + 1),
        (α * Z ^ (c + 1) * cubicWindow h f₁ f₂ Z (K' + 1) c -
          β * twoRow h K' c * Z ^ c * (1 - f₁ * Z + f₂ * Z ^ 2 - f₃ * Z ^ 3)) =
      α * Z ^ 2 * seqWindow h f₁ f₂ Z (K' + 1 + 1) * (h hi * Z ^ hi - h lo * Z ^ lo) +
        (α * Z * h (K' + 1) - β * h K') *
          (Z ^ (lo + 1) * seqWindow h f₁ f₂ Z (lo + 1) - Z ^ (hi + 1) * seqWindow h f₁ f₂ Z (hi + 1)) +
        β * h (K' + 1) * Z * (Z ^ lo * seqWindow h f₁ f₂ Z lo - Z ^ hi * seqWindow h f₁ f₂ Z hi) := by
  have expand : ∀ c, α * Z ^ (c + 1) * cubicWindow h f₁ f₂ Z (K' + 1) c -
      β * twoRow h K' c * Z ^ c * (1 - f₁ * Z + f₂ * Z ^ 2 - f₃ * Z ^ 3) =
        (α * Z * seqWindow h f₁ f₂ Z (K' + 1) - β * (1 - f₁ * Z + f₂ * Z ^ 2 - f₃ * Z ^ 3) * h K') *
            (h c * Z ^ c) -
          (α * Z * seqWindow h f₁ f₂ Z (K' + 1 + 1) - β * (1 - f₁ * Z + f₂ * Z ^ 2 - f₃ * Z ^ 3) * h (K' + 1)) *
            (shiftBack h c * Z ^ c) := by
    intro c
    rw [cubicWindow_eq h h0, twoRow_eq_shiftBack h h0]
    ring
  rw [Finset.sum_congr rfl fun c _ => expand c, Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
  have hS : ∑ c ∈ Finset.Ico (lo + 1) (hi + 1), h c * Z ^ c =
      ∑ c ∈ Finset.range (hi + 1), h c * Z ^ c - ∑ c ∈ Finset.range (lo + 1), h c * Z ^ c :=
    Finset.sum_Ico_eq_sub _ (by omega)
  have hM : ∑ c ∈ Finset.Ico (lo + 1) (hi + 1), shiftBack h c * Z ^ c =
      Z * (∑ c ∈ Finset.range hi, h c * Z ^ c - ∑ c ∈ Finset.range lo, h c * Z ^ c) := by
    rw [← Finset.sum_Ico_eq_sub _ hlh, Finset.mul_sum, ← Finset.sum_Ico_add' (fun c => shiftBack h c * Z ^ c) lo hi 1]
    refine Finset.sum_congr rfl fun c _ => ?_
    simp only [shiftBack]
    ring
  have Ga := cubic_mul_sum_range_eq h f₁ f₂ f₃ Z h0 h1 h2 hrec lo
  have Gb := cubic_mul_sum_range_eq h f₁ f₂ f₃ Z h0 h1 h2 hrec hi
  have Ga1 := cubic_mul_sum_range_eq h f₁ f₂ f₃ Z h0 h1 h2 hrec (lo + 1)
  have Gb1 := cubic_mul_sum_range_eq h f₁ f₂ f₃ Z h0 h1 h2 hrec (hi + 1)
  rw [hS, hM, seqWindow_eq h f₁ f₂ f₃ Z hrec (K' + 1)]
  rw [Finset.sum_range_succ] at Ga1 Gb1 ⊢
  rw [Finset.sum_range_succ]
  linear_combination (α * Z * h (K' + 1) - β * h K') * Gb1 - (α * Z * h (K' + 1) - β * h K') * Ga1 +
    (β * h (K' + 1) * Z) * Gb - (β * h (K' + 1) * Z) * Ga

private theorem window_sum_identity (h : ℕ → ℂ) (f₁ f₂ f₃ : ℂ) (hf₃ : f₃ ≠ 0) (h0 : h 0 = 1) (h1 : h 1 = f₁)
    (h2 : h 2 = f₁ ^ 2 - f₂) (hrec : ∀ n, h (n + 3) = f₁ * h (n + 2) - f₂ * h (n + 1) + f₃ * h n)
    (q vol Z Y W₁ : ℂ) (hq : q ≠ 0) (hZ : Z ≠ 0) (hYZ : q * Z * Y = 1) (k d : ℕ) :
    vol⁻¹ * W₁ * (f₃⁻¹ / q) ^ (k + d) * (Z ^ (k + d + d + 1))⁻¹ *
        (vol * (vol * (1 - q⁻¹)) * Z ^ (k + d + 1) * cubicWindow h f₁ f₂ Z (k + d) (k + d) +
          ∑ c ∈ Finset.Ico (d - 1) (k + d),
            (if 1 ≤ d ∧ c = d - 1 then -(vol * q⁻¹) else vol * (1 - q⁻¹)) *
              (vol * (1 - q⁻¹) * Z ^ (c + 1) * cubicWindow h f₁ f₂ Z (k + d) c -
                vol * q⁻¹ * twoRow h (k + d - 1) c * Z ^ c * (1 - f₁ * Z + f₂ * Z ^ 2 - f₃ * Z ^ 3))) =
      W₁ * (vol * (1 - q⁻¹) * Y ^ (k + d) *
          (f₃⁻¹ ^ (k + d) * twoRow h (k + d) d +
            (f₃⁻¹ ^ (k + d + 1) * twoRow h (k + d + 1) (d + 1) - f₂ / f₃ * (f₃⁻¹ ^ (k + d) * twoRow h (k + d) d)) * Y +
            (f₃⁻¹ ^ (k + d + 2) * twoRow h (k + d + 2) (d + 2) -
                f₂ / f₃ * (f₃⁻¹ ^ (k + d + 1) * twoRow h (k + d + 1) (d + 1)) +
                f₁ / f₃ * (f₃⁻¹ ^ (k + d) * twoRow h (k + d) d)) * Y ^ 2) -
        if 1 ≤ d then
          vol * q⁻¹ * f₃⁻¹ ^ (k + d - 1) * twoRow h (k + d - 1) (d - 1) * Y ^ (k + d - 1) *
            (1 - f₂ / f₃ * Y + f₁ / f₃ * Y ^ 2 - f₃⁻¹ * Y ^ 3)
        else 0) := by
  have hY : Y = q⁻¹ * Z⁻¹ := by
    rw [← mul_inv]
    exact eq_inv_of_mul_eq_one_right hYZ
  subst hY
  rcases eq_or_ne vol 0 with hv | hv
  · subst hv
    simp
  have hcw := cubicWindow_eq h h0 f₁ f₂ Z
  have htr := twoRow_eq_shiftBack h h0
  rcases d with _ | _ | d''
  ·
    simp only [add_zero, Nat.zero_sub, zero_add, show ¬ (1 ≤ 0) from by omega, false_and, if_false]
    rcases k with _ | k'
    ·
      simp only [Finset.Ico_self, Finset.sum_empty, add_zero, pow_zero, zero_add, pow_one, one_mul]
      have r3 : h 3 = f₁ * h 2 - f₂ * h 1 + f₃ * h 0 := hrec 0
      simp only [cubicWindow, twoRow_zero, twoRow_succ, r3, h0, h1, h2]
      field_simp
      ring
    ·
      simp only [Nat.add_sub_cancel]
      rw [← Finset.mul_sum, Finset.sum_eq_sum_Ico_succ_bot (by omega : 0 < k' + 1),
        sum_Ico_class_eq h f₁ f₂ f₃ Z h0 h1 h2 hrec (vol * (1 - q⁻¹)) (vol * q⁻¹) k' 0 k' (Nat.zero_le _)]
      have r3 : h 3 = f₁ * h 2 - f₂ * h 1 + f₃ * h 0 := hrec 0
      simp only [hcw, htr, seqWindow, shiftBack, hrec (k' + 1), hrec k', r3, h0, h1, h2]
      simp only [div_pow, mul_pow, inv_pow]
      field_simp
      ring
  ·
    simp only [zero_add, Nat.sub_self, Nat.add_sub_cancel, le_refl, true_and, if_true]
    rw [Finset.sum_eq_sum_Ico_succ_bot (by omega : 0 < k + 1), if_pos rfl,
      Finset.sum_congr rfl fun c hc => by rw [if_neg (by rw [Finset.mem_Ico] at hc; omega)],
      ← Finset.mul_sum,
      sum_Ico_class_eq h f₁ f₂ f₃ Z h0 h1 h2 hrec (vol * (1 - q⁻¹)) (vol * q⁻¹) k 0 k (Nat.zero_le _)]
    have r3 : h 3 = f₁ * h 2 - f₂ * h 1 + f₃ * h 0 := hrec 0
    simp only [hcw, htr, seqWindow, shiftBack, hrec (k + 1), hrec k, r3, h0, h1, h2]
    simp only [div_pow, mul_pow, inv_pow]
    field_simp
    ring
  ·
    have e1 : k + (d'' + 1 + 1) = k + d'' + 1 + 1 := by omega
    simp only [e1, Nat.add_sub_cancel, show 1 ≤ d'' + 1 + 1 from by omega, true_and, if_true]
    rw [Finset.sum_eq_sum_Ico_succ_bot (by omega : d'' + 1 < k + d'' + 1 + 1), if_pos rfl,
      Finset.sum_congr rfl fun c hc => by rw [if_neg (by rw [Finset.mem_Ico] at hc; omega)],
      ← Finset.mul_sum,
      sum_Ico_class_eq h f₁ f₂ f₃ Z h0 h1 h2 hrec (vol * (1 - q⁻¹)) (vol * q⁻¹) (k + d'' + 1) (d'' + 1) (k + d'' + 1)
        (by omega)]
    simp only [hcw, htr, seqWindow, shiftBack, hrec (k + d'' + 1 + 1), hrec (k + d'' + 1), hrec (d'' + 1), hrec d'']
    simp only [div_pow, mul_pow, inv_pow]
    field_simp
    ring

end WindowIdentity

end
end

section

set_option autoImplicit false

open IsDedekindDomain NumberField NumberField.TateGlobal AutomorphicForm LanglandsTunnell.Converse LanglandsTunnell.RankinSelberg LanglandsTunnell.TateLocal MeasureTheory

p2m_open "IsDedekindDomain.HeightOneSpectrum~Extension LanglandsTunnell.CubicInduction P2MW.S_LanglandsTunnell_CubicInduction_exists_laurent_localZeta_eq_gl3LFactorPoly_of_sphericalData.LanglandsTunnell.CubicInduction NumberField.StandardAddChar"

private theorem valued_natCast_rat (v : HeightOneSpectrum (𝓞 ℚ)) (n : ℕ) :
    Valued.v ((n : ℕ) : v.adicCompletion ℚ) = v.intValuation (n : 𝓞 ℚ) := by
  rw [← map_natCast (algebraMap ℚ (v.adicCompletion ℚ)) n, ← map_natCast (algebraMap (𝓞 ℚ) ℚ) n]
  exact AdelicLevel.valued_algebraMap v (n : 𝓞 ℚ)

private theorem absNorm_span_intCast_rat (z : ℤ) : Ideal.absNorm (Ideal.span {(z : 𝓞 ℚ)}) = z.natAbs := by
  rw [Ideal.absNorm_span_singleton, ← eq_intCast (algebraMap ℤ (𝓞 ℚ)) z, Algebra.norm_algebraMap,
    RingOfIntegers.rank, Module.finrank_self, pow_one]

private theorem absNorm_span_natCast_rat (n : ℕ) : Ideal.absNorm (Ideal.span {(n : 𝓞 ℚ)}) = n := by
  simpa using absNorm_span_intCast_rat (n : ℤ)

private theorem intValuation_absNorm_rat (v : HeightOneSpectrum (𝓞 ℚ)) :
    v.intValuation (Ideal.absNorm v.asIdeal : 𝓞 ℚ) = WithZero.exp (-1 : ℤ) := by
  have hN : 1 < Ideal.absNorm v.asIdeal := NumberField.HeightOneSpectrum.one_lt_absNorm v
  have hmem : ((Ideal.absNorm v.asIdeal : ℕ) : 𝓞 ℚ) ∈ v.asIdeal := Ideal.absNorm_mem v.asIdeal
  have h1 : v.intValuation ((Ideal.absNorm v.asIdeal : ℕ) : 𝓞 ℚ) ≤ WithZero.exp (-((1 : ℕ) : ℤ)) := by
    rw [intValuation_le_pow_iff_mem, pow_one]
    exact hmem
  have h2 : ¬ v.intValuation ((Ideal.absNorm v.asIdeal : ℕ) : 𝓞 ℚ) ≤ WithZero.exp (-((2 : ℕ) : ℤ)) := by
    rw [intValuation_le_pow_iff_mem]
    intro hmem2
    have hle : Ideal.span {((Ideal.absNorm v.asIdeal : ℕ) : 𝓞 ℚ)} ≤ v.asIdeal ^ 2 :=
      (Ideal.span_singleton_le_iff_mem _).mpr hmem2
    have hdvd := Ideal.absNorm_dvd_absNorm_of_le hle
    rw [map_pow, absNorm_span_natCast_rat] at hdvd
    have hle' := Nat.le_of_dvd (by omega) hdvd
    nlinarith
  have hr : ((Ideal.absNorm v.asIdeal : ℕ) : 𝓞 ℚ) ≠ 0 := by
    exact_mod_cast (show Ideal.absNorm v.asIdeal ≠ 0 by omega)
  obtain ⟨c, hc⟩ : ∃ c : ℕ, v.intValuation ((Ideal.absNorm v.asIdeal : ℕ) : 𝓞 ℚ) = WithZero.exp (-(c : ℤ)) :=
    ⟨_, v.intValuation_if_neg hr⟩
  rw [hc, WithZero.exp_le_exp] at h1 h2
  rw [hc]
  congr 1
  omega

private theorem valued_varpi_eq (v : HeightOneSpectrum (𝓞 ℚ)) :
    Valued.v (varpi v) = WithZero.exp (-1 : ℤ) :=
  AdelicLevel.valued_uniformizerUnit ℚ v

private theorem valued_ratPrimeAt_eq_valued_varpi (v : HeightOneSpectrum (𝓞 ℚ)) :
    Valued.v (ratPrimeAt v) = Valued.v (varpi v) := by
  show Valued.v ((Ideal.absNorm v.asIdeal : ℕ) : v.adicCompletion ℚ) = Valued.v (varpi v)
  rw [valued_natCast_rat, intValuation_absNorm_rat, valued_varpi_eq]

private theorem coe_ratPrimeUnit (v : HeightOneSpectrum (𝓞 ℚ)) :
    ((ratPrimeUnit v : (v.adicCompletion ℚ)ˣ) : v.adicCompletion ℚ) = ratPrimeAt v := rfl

private theorem apply_ratPrimeUnit_eq_apply_uniformizerUnit (v : HeightOneSpectrum (𝓞 ℚ)) (χ : (v.adicCompletion ℚ)ˣ →* ℂˣ)
    (hχ : HasConductorExponentAt ℚ v χ 0) :
    χ (ratPrimeUnit v) = χ (AdelicLevel.uniformizerUnit ℚ v) := by
  have hne : Valued.v (varpi v) ≠ 0 := (Valuation.ne_zero_iff _).2 (varpi_ne_zero v)
  have hunit : Valued.v (((AdelicLevel.uniformizerUnit ℚ v)⁻¹ * ratPrimeUnit v : (v.adicCompletion ℚ)ˣ) :
      v.adicCompletion ℚ) = 1 := by
    rw [Units.val_mul, Units.val_inv_eq_inv_val, coe_ratPrimeUnit, Valuation.map_mul, Valuation.map_inv,
      valued_ratPrimeAt_eq_valued_varpi]
    exact inv_mul_cancel₀ hne
  have h := (hasConductorExponentAt_zero_iff ℚ v).1 hχ _ hunit
  rw [map_mul, map_inv] at h
  exact (inv_mul_eq_one.1 h).symm

private theorem coe_apply_ratPrimeUnit_eq (v : HeightOneSpectrum (𝓞 ℚ)) (χ : (v.adicCompletion ℚ)ˣ →* ℂˣ)
    (hχ : HasConductorExponentAt ℚ v χ 0) (t : ℂ) (ht : t = ((χ (AdelicLevel.uniformizerUnit ℚ v) : ℂˣ) : ℂ)) :
    ((χ (ratPrimeUnit v) : ℂˣ) : ℂ) = t := by
  rw [ht, apply_ratPrimeUnit_eq_apply_uniformizerUnit v χ hχ]

private theorem psiLocal_rat_apply_eq_one_of_valued_le_one (v : HeightOneSpectrum (𝓞 ℚ)) (x : v.adicCompletion ℚ)
    (hx : Valued.v x ≤ 1) : psiLocal ℚ v x = 1 :=
  psiLocal_eq_one_of_mem_integers ℚ v x hx

private theorem exists_valued_le_one_and_psiLocal_rat_varpi_inv_mul_ne_one (v : HeightOneSpectrum (𝓞 ℚ)) :
    ∃ x : v.adicCompletion ℚ, Valued.v x ≤ 1 ∧ psiLocal ℚ v ((varpi v)⁻¹ * x) ≠ 1 := by
  have hk : ∃ k : ℤ, ∀ x : v.adicCompletion ℚ, Valued.v x ≤ WithZero.exp k → psiLocal ℚ v x = 1 :=
    ⟨0, fun x hx => psiLocal_rat_apply_eq_one_of_valued_le_one v x (by rwa [WithZero.exp_zero] at hx)⟩
  obtain ⟨-, y, hy, hy1⟩ :=
    forall_eq_one_and_exists_ne_one_of_addCharLevel ℚ v (psiLocal ℚ v) hk (psiLocal_ne_one ℚ v)
  rw [addCharLevel_psiLocal_rat] at hy
  refine ⟨varpi v * y, ?_, ?_⟩
  · calc Valued.v (varpi v * y) = WithZero.exp (-1 : ℤ) * Valued.v y := by
          rw [Valuation.map_mul, valued_varpi_eq]
      _ ≤ WithZero.exp (-1 : ℤ) * WithZero.exp ((0 : ℤ) + 1) := mul_le_mul_right hy _
      _ = 1 := by rw [← WithZero.exp_add, zero_add, neg_add_cancel, WithZero.exp_zero]
  · rwa [inv_mul_cancel_left₀ (varpi_ne_zero v)]

private theorem exists_valued_le_exp_one_and_psiLocal_rat_ne_one (v : HeightOneSpectrum (𝓞 ℚ)) :
    ∃ x : v.adicCompletion ℚ, Valued.v x ≤ WithZero.exp (1 : ℤ) ∧ psiLocal ℚ v x ≠ 1 := by
  have hk : ∃ k : ℤ, ∀ x : v.adicCompletion ℚ, Valued.v x ≤ WithZero.exp k → psiLocal ℚ v x = 1 :=
    ⟨0, fun x hx => psiLocal_rat_apply_eq_one_of_valued_le_one v x (by rwa [WithZero.exp_zero] at hx)⟩
  obtain ⟨-, y, hy, hy1⟩ :=
    forall_eq_one_and_exists_ne_one_of_addCharLevel ℚ v (psiLocal ℚ v) hk (psiLocal_ne_one ℚ v)
  rw [addCharLevel_psiLocal_rat, zero_add] at hy
  exact ⟨y, hy, hy1⟩

private theorem exists_valued_le_exp_one_and_psiLocal_rat_inv_ne_one (v : HeightOneSpectrum (𝓞 ℚ)) :
    ∃ x : v.adicCompletion ℚ, Valued.v x ≤ WithZero.exp (1 : ℤ) ∧ (psiLocal ℚ v)⁻¹ x ≠ 1 := by
  obtain ⟨y, hy, hy1⟩ := exists_valued_le_exp_one_and_psiLocal_rat_ne_one v
  refine ⟨-y, by rwa [Valuation.map_neg], ?_⟩
  rwa [AddChar.inv_apply, neg_neg]

private theorem psiLocal_rat_facts (v : HeightOneSpectrum (𝓞 ℚ)) :
    (∀ x : v.adicCompletion ℚ, Valued.v x ≤ 1 → psiLocal ℚ v x = 1) ∧
      (∃ x : v.adicCompletion ℚ, Valued.v x ≤ 1 ∧ psiLocal ℚ v ((varpi v)⁻¹ * x) ≠ 1) ∧
      addCharLevel (psiLocal ℚ v) = 0 ∧ psiLocal ℚ v ≠ 1 :=
  ⟨psiLocal_rat_apply_eq_one_of_valued_le_one v, exists_valued_le_one_and_psiLocal_rat_varpi_inv_mul_ne_one v,
    addCharLevel_psiLocal_rat v, psiLocal_ne_one ℚ v⟩

private theorem addCharLevel_inv (v : HeightOneSpectrum (𝓞 ℚ)) (ψ : AddChar (v.adicCompletion ℚ) ℂ) :
    addCharLevel ψ⁻¹ = addCharLevel ψ := by
  rw [addCharLevel_def, addCharLevel_def]
  congr 1
  ext n
  simp only [Set.mem_setOf_eq, AddChar.inv_apply]
  constructor
  · intro h x hx
    have hx' := h (-x) (by rwa [Valuation.map_neg])
    rwa [neg_neg] at hx'
  · intro h x hx
    exact h (-x) (by rwa [Valuation.map_neg])

private theorem psiLocal_rat_inv_facts (v : HeightOneSpectrum (𝓞 ℚ)) :
    (∀ x : v.adicCompletion ℚ, Valued.v x ≤ 1 → (psiLocal ℚ v)⁻¹ x = 1) ∧
      (∃ x : v.adicCompletion ℚ, Valued.v x ≤ 1 ∧ (psiLocal ℚ v)⁻¹ ((varpi v)⁻¹ * x) ≠ 1) ∧
      addCharLevel (psiLocal ℚ v)⁻¹ = 0 ∧ (psiLocal ℚ v)⁻¹ ≠ 1 := by
  obtain ⟨x, hx, hx1⟩ := exists_valued_le_one_and_psiLocal_rat_varpi_inv_mul_ne_one v
  refine ⟨fun y hy => ?_, ⟨-x, ?_, ?_⟩, ?_, inv_ne_one.2 (psiLocal_ne_one ℚ v)⟩
  · rw [AddChar.inv_apply]
    exact psiLocal_rat_apply_eq_one_of_valued_le_one v (-y) (by rwa [Valuation.map_neg])
  · rwa [Valuation.map_neg]
  · rwa [AddChar.inv_apply, mul_neg, neg_neg]
  · rw [addCharLevel_inv, addCharLevel_psiLocal_rat]

private theorem apply_centralGen_pow_mul (v : HeightOneSpectrum (𝓞 ℚ)) (W : LocalGL3 v → ℂ) (e₃ : ℂ)
    (hZ : ∀ g : LocalGL3 v, W (centralGen v * g) = e₃ * W g) (m : ℕ) (g : LocalGL3 v) :
    W (centralGen v ^ m * g) = e₃ ^ m * W g := by
  induction m generalizing g with
  | zero => simp only [pow_zero, one_mul]
  | succ m ih => rw [pow_succ (centralGen v), mul_assoc, ih, hZ, pow_succ e₃, mul_assoc]

private theorem pow_mul_apply_centralGen_inv_pow_mul (v : HeightOneSpectrum (𝓞 ℚ)) (W : LocalGL3 v → ℂ) (e₃ : ℂ)
    (hZ : ∀ g : LocalGL3 v, W (centralGen v * g) = e₃ * W g) (m : ℕ) (g : LocalGL3 v) :
    e₃ ^ m * W ((centralGen v)⁻¹ ^ m * g) = W g := by
  rw [← apply_centralGen_pow_mul v W e₃ hZ m, ← mul_assoc, inv_pow, mul_inv_cancel, one_mul]

private theorem eq_zero_of_central_eq_zero (v : HeightOneSpectrum (𝓞 ℚ)) (W : LocalGL3 v → ℂ) (e₃ : ℂ)
    (hZ : ∀ g : LocalGL3 v, W (centralGen v * g) = e₃ * W g) (h3 : e₃ = 0) : W = 0 := by
  funext g
  show W g = 0
  rw [← mul_inv_cancel_left (centralGen v) g, hZ, h3, zero_mul]

private theorem eq_zero_of_apply_one_eq_zero (v : HeightOneSpectrum (𝓞 ℚ)) (ψv : AddChar (v.adicCompletion ℚ) ℂ)
    (W : LocalGL3 v → ℂ) (e₁ e₂ e₃ : ℂ)
    (hW : IsRightInvariant (localMaximalCompact3 (𝓞 ℚ) ℚ v) W ∧
      IsCosetEigenfunction (localMaximalCompact3 (𝓞 ℚ) ℚ v) (heckeGen1 v) W (cNormQ v * e₁) ∧
      IsCosetEigenfunction (localMaximalCompact3 (𝓞 ℚ) ℚ v) (heckeGen2 v) W (cNormQ v * e₂) ∧
      ∀ g : LocalGL3 v, W (centralGen v * g) = e₃ * W g)
    (hψ : IsGL3PsiWhittakerFn ψv W) (hlev : addCharLevel ψv = 0) (hne : ψv ≠ 1) (hW1 : W 1 = 0) : W = 0 :=
  eq_zero_of_isCosetEigenfunction_of_isGL3PsiWhittakerFn_of_apply_one_eq_zero v ψv e₁ e₂ e₃ W hW.1 hW.2.1
    hW.2.2.1 hW.2.2.2 hψ hlev hne hW1

private theorem eq_zero_of_apply_one_eq_zero_of_psiLocal (v : HeightOneSpectrum (𝓞 ℚ)) (W : LocalGL3 v → ℂ) (e₁ e₂ e₃ : ℂ)
    (hW : IsRightInvariant (localMaximalCompact3 (𝓞 ℚ) ℚ v) W ∧
      IsCosetEigenfunction (localMaximalCompact3 (𝓞 ℚ) ℚ v) (heckeGen1 v) W (cNormQ v * e₁) ∧
      IsCosetEigenfunction (localMaximalCompact3 (𝓞 ℚ) ℚ v) (heckeGen2 v) W (cNormQ v * e₂) ∧
      ∀ g : LocalGL3 v, W (centralGen v * g) = e₃ * W g)
    (hψ : IsGL3PsiWhittakerFn (psiLocal ℚ v) W) (hW1 : W 1 = 0) : W = 0 :=
  eq_zero_of_apply_one_eq_zero v (psiLocal ℚ v) W e₁ e₂ e₃ hW hψ (addCharLevel_psiLocal_rat v) (psiLocal_ne_one ℚ v)
    hW1

private noncomputable def twoRowCoeff (e₁ e₂ e₃ : ℂ) : ℕ → ℕ → ℂ
  | k₁, 0 => sphericalTorusValue e₁ e₂ e₃ k₁
  | k₁, k₂ + 1 =>
    sphericalTorusValue e₁ e₂ e₃ k₁ * sphericalTorusValue e₁ e₂ e₃ (k₂ + 1) -
      sphericalTorusValue e₁ e₂ e₃ (k₁ + 1) * sphericalTorusValue e₁ e₂ e₃ k₂

private theorem twoRowCoeff_zero (e₁ e₂ e₃ : ℂ) (k₁ : ℕ) : twoRowCoeff e₁ e₂ e₃ k₁ 0 = sphericalTorusValue e₁ e₂ e₃ k₁ :=
  rfl

private theorem twoRowCoeff_succ (e₁ e₂ e₃ : ℂ) (k₁ k₂ : ℕ) :
    twoRowCoeff e₁ e₂ e₃ k₁ (k₂ + 1) =
      sphericalTorusValue e₁ e₂ e₃ k₁ * sphericalTorusValue e₁ e₂ e₃ (k₂ + 1) -
        sphericalTorusValue e₁ e₂ e₃ (k₁ + 1) * sphericalTorusValue e₁ e₂ e₃ k₂ :=
  rfl

private theorem apply_twoRowPointLocal_eq (v : HeightOneSpectrum (𝓞 ℚ)) (ψv : AddChar (v.adicCompletion ℚ) ℂ)
    (W : LocalGL3 v → ℂ) (e₁ e₂ e₃ : ℂ)
    (hW : IsRightInvariant (localMaximalCompact3 (𝓞 ℚ) ℚ v) W ∧
      IsCosetEigenfunction (localMaximalCompact3 (𝓞 ℚ) ℚ v) (heckeGen1 v) W (cNormQ v * e₁) ∧
      IsCosetEigenfunction (localMaximalCompact3 (𝓞 ℚ) ℚ v) (heckeGen2 v) W (cNormQ v * e₂) ∧
      ∀ g : LocalGL3 v, W (centralGen v * g) = e₃ * W g)
    (hψ : IsGL3PsiWhittakerFn ψv W) (hψ0 : ∀ x : v.adicCompletion ℚ, Valued.v x ≤ 1 → ψv x = 1)
    (hψ1 : ∃ x : v.adicCompletion ℚ, Valued.v x ≤ 1 ∧ ψv ((varpi v)⁻¹ * x) ≠ 1) (k₁ k₂ : ℕ) (hk : k₂ ≤ k₁) :
    W (twoRowPointLocal v k₁ k₂) = W 1 * ((cNormQ v)⁻¹ ^ k₁ * twoRowCoeff e₁ e₂ e₃ k₁ k₂) := by
  obtain ⟨h1, h2⟩ :=
    sphericalTorusValue_eq_of_isCosetEigenfunction_of_isGL3PsiWhittakerFn v ψv W e₁ e₂ e₃ hW hψ hψ0 hψ1
  cases k₂ with
  | zero => rw [twoRowPointLocal_zero_right, h1 k₁, twoRowCoeff_zero]
  | succ k₂ =>
    rw [twoRowCoeff_succ]
    exact h2 k₁ k₂ hk

private theorem apply_twoRowPointLocal_eq_of_psiLocal (v : HeightOneSpectrum (𝓞 ℚ)) (W : LocalGL3 v → ℂ) (e₁ e₂ e₃ : ℂ)
    (hW : IsRightInvariant (localMaximalCompact3 (𝓞 ℚ) ℚ v) W ∧
      IsCosetEigenfunction (localMaximalCompact3 (𝓞 ℚ) ℚ v) (heckeGen1 v) W (cNormQ v * e₁) ∧
      IsCosetEigenfunction (localMaximalCompact3 (𝓞 ℚ) ℚ v) (heckeGen2 v) W (cNormQ v * e₂) ∧
      ∀ g : LocalGL3 v, W (centralGen v * g) = e₃ * W g)
    (hψ : IsGL3PsiWhittakerFn (psiLocal ℚ v) W) (k₁ k₂ : ℕ) (hk : k₂ ≤ k₁) :
    W (twoRowPointLocal v k₁ k₂) = W 1 * ((cNormQ v)⁻¹ ^ k₁ * twoRowCoeff e₁ e₂ e₃ k₁ k₂) :=
  apply_twoRowPointLocal_eq v (psiLocal ℚ v) W e₁ e₂ e₃ hW hψ (psiLocal_rat_apply_eq_one_of_valued_le_one v)
    (exists_valued_le_one_and_psiLocal_rat_varpi_inv_mul_ne_one v) k₁ k₂ hk

private theorem coe_twoRowPointLocal_eq_diagonal (v : HeightOneSpectrum (𝓞 ℚ)) (k₁ k₂ : ℕ) :
    ((twoRowPointLocal v k₁ k₂ : LocalGL3 v) : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) =
      Matrix.diagonal ![ratPrimeAt v ^ k₁, ratPrimeAt v ^ k₂, 1] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [twoRowPointLocal, embedMat2, Units.val_pow_eq_pow_val, coe_ratPrimeUnit]

private theorem valued_ratPrimeAt_pow_lt (v : HeightOneSpectrum (𝓞 ℚ)) {m n : ℕ} (h : m < n) :
    Valued.v (ratPrimeAt v ^ n) < Valued.v (ratPrimeAt v ^ m) := by
  have hlt : WithZero.exp (-1 : ℤ) < 1 := by
    rw [← WithZero.exp_zero, WithZero.exp_lt_exp]
    norm_num
  rw [Valuation.map_pow, Valuation.map_pow, valued_ratPrimeAt_eq_valued_varpi, valued_varpi_eq]
  exact pow_lt_pow_right_of_lt_one₀ WithZero.exp_pos hlt h

private theorem apply_twoRowPointLocal_eq_zero_of_lt (v : HeightOneSpectrum (𝓞 ℚ)) (ψv : AddChar (v.adicCompletion ℚ) ℂ)
    (W : LocalGL3 v → ℂ) (hU : IsRightInvariant (localMaximalCompact3 (𝓞 ℚ) ℚ v) W) (hψ : IsGL3PsiWhittakerFn ψv W)
    (hψ1 : ∃ x : v.adicCompletion ℚ, Valued.v x ≤ 1 ∧ ψv ((varpi v)⁻¹ * x) ≠ 1) (k₁ k₂ : ℕ) (hk : k₁ < k₂) :
    W (twoRowPointLocal v k₁ k₂) = 0 :=
  eq_zero_of_coe_eq_diagonal_of_valued_lt_of_isGL3PsiWhittakerFn v ψv W hU hψ hψ1 (twoRowPointLocal v k₁ k₂) _
    (coe_twoRowPointLocal_eq_diagonal v k₁ k₂) (Or.inl (valued_ratPrimeAt_pow_lt v hk))

private theorem coe_inv_of_coe_eq_diagonal {n : Type} [Fintype n] [DecidableEq n] {F : Type} [Field F] (g : GL n F)
    (w : n → F) (hg : (g : Matrix n n F) = Matrix.diagonal w) (hw : ∀ i, w i ≠ 0) :
    ((g⁻¹ : GL n F) : Matrix n n F) = Matrix.diagonal fun i => (w i)⁻¹ := by
  rw [Matrix.coe_units_inv, hg]
  refine Matrix.inv_eq_left_inv ?_
  rw [Matrix.diagonal_mul_diagonal]
  have h : (fun i => (w i)⁻¹ * w i) = fun _ => (1 : F) := funext fun i => inv_mul_cancel₀ (hw i)
  rw [h, Matrix.diagonal_one]

private theorem coe_inv_mul_of_coe_eq_diagonal {n : Type} [Fintype n] [DecidableEq n] {F : Type} [Field F]
    (g₁ g₂ : GL n F) (w₁ w₂ : n → F) (h₁ : (g₁ : Matrix n n F) = Matrix.diagonal w₁)
    (h₂ : (g₂ : Matrix n n F) = Matrix.diagonal w₂)
    (hw₁ : ∀ i, w₁ i ≠ 0) :
    ((g₁⁻¹ * g₂ : GL n F) : Matrix n n F) = Matrix.diagonal fun i => (w₁ i)⁻¹ * w₂ i := by
  rw [Units.val_mul, coe_inv_of_coe_eq_diagonal g₁ w₁ h₁ hw₁, h₂, Matrix.diagonal_mul_diagonal]

private theorem coe_pow_mul_of_coe_eq_diagonal {n : Type} [Fintype n] [DecidableEq n] {F : Type} [Field F]
    (c g : GL n F) (z : F) (w : n → F) (hc : (c : Matrix n n F) = Matrix.diagonal fun _ => z)
    (hg : (g : Matrix n n F) = Matrix.diagonal w) (m : ℕ) :
    ((c ^ m * g : GL n F) : Matrix n n F) = Matrix.diagonal fun i => z ^ m * w i := by
  simp only [Units.val_mul, Units.val_pow_eq_pow_val, hc, hg, Matrix.diagonal_pow, Matrix.diagonal_mul_diagonal,
    Pi.pow_apply]

private theorem coe_centralGen_eq_diagonal (v : HeightOneSpectrum (𝓞 ℚ)) :
    ((centralGen v : LocalGL3 v) : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) =
      Matrix.diagonal fun _ => varpi v := by
  rw [show ((centralGen v : LocalGL3 v) : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) =
      Matrix.diagonal ![varpi v, varpi v, varpi v] from rfl]
  congr 1
  funext i
  fin_cases i <;> rfl

private theorem mem_localMaximalCompact3_of_coe_eq_diagonal (v : HeightOneSpectrum (𝓞 ℚ)) (k : LocalGL3 v)
    (w : Fin 3 → v.adicCompletion ℚ) (hk : (k : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) = Matrix.diagonal w)
    (hw : ∀ i, Valued.v (w i) = 1) : k ∈ localMaximalCompact3 (𝓞 ℚ) ℚ v := by
  have hw0 : ∀ i, w i ≠ 0 := fun i h0 => by
    have h1 := hw i
    rw [h0, Valuation.map_zero] at h1
    exact zero_ne_one h1
  rw [mem_localMaximalCompact3_iff]
  refine ⟨fun i j => ?_, fun i j => ?_⟩
  · rw [hk]
    simp only [Matrix.diagonal_apply]
    split_ifs
    · exact (hw i).le
    · rw [Valuation.map_zero]
      exact zero_le'
  · rw [coe_inv_of_coe_eq_diagonal k w hk hw0]
    simp only [Matrix.diagonal_apply]
    split_ifs
    · refine le_of_eq ?_
      rw [Valuation.map_inv, hw i, inv_one]
    · rw [Valuation.map_zero]
      exact zero_le'

private theorem valued_varpi_pow_mul_ratPrimeAt_pow (v : HeightOneSpectrum (𝓞 ℚ)) (m k : ℕ) :
    Valued.v (varpi v ^ m * ratPrimeAt v ^ k) = WithZero.exp (-((m : ℤ) + k)) := by
  rw [Valuation.map_mul, Valuation.map_pow, Valuation.map_pow, valued_ratPrimeAt_eq_valued_varpi, valued_varpi_eq,
    ← pow_add, ← WithZero.exp_nsmul, nsmul_eq_mul]
  congr 1
  push_cast
  ring

private theorem apply_eq_zero_of_coe_eq_diagonal_of_not_dominant (v : HeightOneSpectrum (𝓞 ℚ))
    (ψv : AddChar (v.adicCompletion ℚ) ℂ) (W : LocalGL3 v → ℂ)
    (hU : IsRightInvariant (localMaximalCompact3 (𝓞 ℚ) ℚ v) W)
    (hψ : IsGL3PsiWhittakerFn ψv W) (hψ1 : ∃ x : v.adicCompletion ℚ, Valued.v x ≤ 1 ∧ ψv ((varpi v)⁻¹ * x) ≠ 1)
    (a : Fin 3 → (v.adicCompletion ℚ)ˣ) (lam : Fin 3 → ℤ)
    (hval : ∀ i, Valued.v (a i : v.adicCompletion ℚ) = WithZero.exp (-lam i)) (D : LocalGL3 v)
    (hD : (D : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) = Matrix.diagonal fun i => (a i : v.adicCompletion ℚ))
    (h : lam 0 < lam 1 ∨ lam 1 < lam 2) : W D = 0 := by
  refine eq_zero_of_coe_eq_diagonal_of_valued_lt_of_isGL3PsiWhittakerFn v ψv W hU hψ hψ1 D _ hD ?_
  refine h.imp (fun h01 => ?_) (fun h12 => ?_)
  · show Valued.v (a 1 : v.adicCompletion ℚ) < Valued.v (a 0 : v.adicCompletion ℚ)
    rw [hval 1, hval 0]
    exact WithZero.exp_lt_exp.2 (by omega)
  · show Valued.v (a 2 : v.adicCompletion ℚ) < Valued.v (a 1 : v.adicCompletion ℚ)
    rw [hval 2, hval 1]
    exact WithZero.exp_lt_exp.2 (by omega)

private theorem pow_mul_apply_eq_of_coe_eq_diagonal_of_dominant (v : HeightOneSpectrum (𝓞 ℚ))
    (ψv : AddChar (v.adicCompletion ℚ) ℂ) (W : LocalGL3 v → ℂ) (e₁ e₂ e₃ : ℂ)
    (hW : IsRightInvariant (localMaximalCompact3 (𝓞 ℚ) ℚ v) W ∧
      IsCosetEigenfunction (localMaximalCompact3 (𝓞 ℚ) ℚ v) (heckeGen1 v) W (cNormQ v * e₁) ∧
      IsCosetEigenfunction (localMaximalCompact3 (𝓞 ℚ) ℚ v) (heckeGen2 v) W (cNormQ v * e₂) ∧
      ∀ g : LocalGL3 v, W (centralGen v * g) = e₃ * W g)
    (hψ : IsGL3PsiWhittakerFn ψv W) (hψ0 : ∀ x : v.adicCompletion ℚ, Valued.v x ≤ 1 → ψv x = 1)
    (hψ1 : ∃ x : v.adicCompletion ℚ, Valued.v x ≤ 1 ∧ ψv ((varpi v)⁻¹ * x) ≠ 1)
    (a : Fin 3 → (v.adicCompletion ℚ)ˣ) (lam : Fin 3 → ℤ)
    (hval : ∀ i, Valued.v (a i : v.adicCompletion ℚ) = WithZero.exp (-lam i)) (D : LocalGL3 v)
    (hD : (D : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) = Matrix.diagonal fun i => (a i : v.adicCompletion ℚ))
    (h01 : lam 1 ≤ lam 0) (h12 : lam 2 ≤ lam 1) :
    e₃ ^ (-lam 2).toNat * W D =
      e₃ ^ (lam 2).toNat * (W 1 * ((cNormQ v)⁻¹ ^ (lam 0 - lam 2).toNat *
        twoRowCoeff e₁ e₂ e₃ (lam 0 - lam 2).toNat (lam 1 - lam 2).toNat)) := by
  obtain ⟨np, hnp⟩ : ∃ np : ℕ, np = (lam 2).toNat := ⟨_, rfl⟩
  obtain ⟨nn, hnn⟩ : ∃ nn : ℕ, nn = (-lam 2).toNat := ⟨_, rfl⟩
  obtain ⟨k₁, hk₁⟩ : ∃ k₁ : ℕ, k₁ = (lam 0 - lam 2).toNat := ⟨_, rfl⟩
  obtain ⟨k₂, hk₂⟩ : ∃ k₂ : ℕ, k₂ = (lam 1 - lam 2).toNat := ⟨_, rfl⟩
  rw [← hnp, ← hnn, ← hk₁, ← hk₂]
  have hn : (np : ℤ) - nn = lam 2 := by rw [hnp, hnn]; exact Int.toNat_sub_toNat_neg (lam 2)
  have hk₁' : (k₁ : ℤ) = lam 0 - lam 2 := by rw [hk₁]; exact Int.toNat_sub_of_le (h12.trans h01)
  have hk₂' : (k₂ : ℤ) = lam 1 - lam 2 := by rw [hk₂]; exact Int.toNat_sub_of_le h12
  have hk : k₂ ≤ k₁ := by rw [hk₁, hk₂]; exact Int.toNat_le_toNat (by omega)

  obtain ⟨kk, hkk_def⟩ : ∃ kk : Fin 3 → ℕ, kk = ![k₁, k₂, 0] := ⟨_, rfl⟩
  have hkk : ∀ i, (kk i : ℤ) = lam i - lam 2 := by
    intro i
    fin_cases i <;> simp [hkk_def, hk₁', hk₂']
  have htv : ![ratPrimeAt v ^ k₁, ratPrimeAt v ^ k₂, 1] = fun i => ratPrimeAt v ^ kk i := by
    funext i
    fin_cases i <;> simp [hkk_def]

  have hT : ((centralGen v ^ np * twoRowPointLocal v k₁ k₂ : LocalGL3 v) :
        Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) =
      Matrix.diagonal fun i => varpi v ^ np * ratPrimeAt v ^ kk i :=
    coe_pow_mul_of_coe_eq_diagonal (centralGen v) (twoRowPointLocal v k₁ k₂) (varpi v) (fun i => ratPrimeAt v ^ kk i)
      (coe_centralGen_eq_diagonal v) (by rw [coe_twoRowPointLocal_eq_diagonal, htv]) np
  have hDm : ((centralGen v ^ nn * D : LocalGL3 v) : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) =
      Matrix.diagonal fun i => varpi v ^ nn * (a i : v.adicCompletion ℚ) :=
    coe_pow_mul_of_coe_eq_diagonal (centralGen v) D (varpi v) (fun i => (a i : v.adicCompletion ℚ))
      (coe_centralGen_eq_diagonal v) hD nn
  have hTne : ∀ i, varpi v ^ np * ratPrimeAt v ^ kk i ≠ 0 := fun i =>
    mul_ne_zero (pow_ne_zero _ (varpi_ne_zero v)) (pow_ne_zero _ (ratPrimeAt_ne_zero v))
  have hY : ∀ i, Valued.v (varpi v ^ nn * (a i : v.adicCompletion ℚ)) = WithZero.exp ((nn : ℤ) * (-1) + -lam i) := by
    intro i
    rw [Valuation.map_mul, Valuation.map_pow, valued_varpi_eq, hval i, ← WithZero.exp_nsmul, ← WithZero.exp_add,
      nsmul_eq_mul]

  have hu : (centralGen v ^ np * twoRowPointLocal v k₁ k₂)⁻¹ * (centralGen v ^ nn * D) ∈
      localMaximalCompact3 (𝓞 ℚ) ℚ v := by
    refine mem_localMaximalCompact3_of_coe_eq_diagonal v _ _ (coe_inv_mul_of_coe_eq_diagonal _ _ _ _ hT hDm hTne)
      fun i => ?_
    rw [Valuation.map_mul, Valuation.map_inv, valued_varpi_pow_mul_ratPrimeAt_pow, hY i, ← WithZero.exp_neg,
      ← WithZero.exp_add]
    refine (congrArg WithZero.exp ?_).trans WithZero.exp_zero
    have hi := hkk i
    omega

  calc e₃ ^ nn * W D = W (centralGen v ^ nn * D) := (apply_centralGen_pow_mul v W e₃ hW.2.2.2 nn D).symm
    _ = W (centralGen v ^ np * twoRowPointLocal v k₁ k₂ *
          ((centralGen v ^ np * twoRowPointLocal v k₁ k₂)⁻¹ * (centralGen v ^ nn * D))) := by
        rw [mul_inv_cancel_left]
    _ = W (centralGen v ^ np * twoRowPointLocal v k₁ k₂) := hW.1 _ _ hu
    _ = e₃ ^ np * W (twoRowPointLocal v k₁ k₂) := apply_centralGen_pow_mul v W e₃ hW.2.2.2 np _
    _ = e₃ ^ np * (W 1 * ((cNormQ v)⁻¹ ^ k₁ * twoRowCoeff e₁ e₂ e₃ k₁ k₂)) := by
        rw [apply_twoRowPointLocal_eq v ψv W e₁ e₂ e₃ hW hψ hψ0 hψ1 k₁ k₂ hk]

private theorem apply_eq_zpow_mul_of_coe_eq_diagonal_of_dominant (v : HeightOneSpectrum (𝓞 ℚ))
    (ψv : AddChar (v.adicCompletion ℚ) ℂ) (W : LocalGL3 v → ℂ) (e₁ e₂ e₃ : ℂ)
    (hW : IsRightInvariant (localMaximalCompact3 (𝓞 ℚ) ℚ v) W ∧
      IsCosetEigenfunction (localMaximalCompact3 (𝓞 ℚ) ℚ v) (heckeGen1 v) W (cNormQ v * e₁) ∧
      IsCosetEigenfunction (localMaximalCompact3 (𝓞 ℚ) ℚ v) (heckeGen2 v) W (cNormQ v * e₂) ∧
      ∀ g : LocalGL3 v, W (centralGen v * g) = e₃ * W g)
    (hψ : IsGL3PsiWhittakerFn ψv W) (hψ0 : ∀ x : v.adicCompletion ℚ, Valued.v x ≤ 1 → ψv x = 1)
    (hψ1 : ∃ x : v.adicCompletion ℚ, Valued.v x ≤ 1 ∧ ψv ((varpi v)⁻¹ * x) ≠ 1) (he₃ : e₃ ≠ 0)
    (a : Fin 3 → (v.adicCompletion ℚ)ˣ) (lam : Fin 3 → ℤ)
    (hval : ∀ i, Valued.v (a i : v.adicCompletion ℚ) = WithZero.exp (-lam i)) (D : LocalGL3 v)
    (hD : (D : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) = Matrix.diagonal fun i => (a i : v.adicCompletion ℚ))
    (h01 : lam 1 ≤ lam 0) (h12 : lam 2 ≤ lam 1) :
    W D = e₃ ^ lam 2 * (W 1 * ((cNormQ v)⁻¹ ^ (lam 0 - lam 2).toNat *
      twoRowCoeff e₁ e₂ e₃ (lam 0 - lam 2).toNat (lam 1 - lam 2).toNat)) := by
  have hmul := pow_mul_apply_eq_of_coe_eq_diagonal_of_dominant v ψv W e₁ e₂ e₃ hW hψ hψ0 hψ1 a lam hval D hD h01 h12
  have hz : e₃ ^ lam 2 = e₃ ^ (lam 2).toNat * (e₃ ^ (-lam 2).toNat)⁻¹ := by
    conv_lhs => rw [← Int.toNat_sub_toNat_neg (lam 2)]
    rw [zpow_sub₀ he₃, zpow_natCast, zpow_natCast, div_eq_mul_inv]
  have hnn : e₃ ^ (-lam 2).toNat ≠ 0 := pow_ne_zero _ he₃
  calc W D = (e₃ ^ (-lam 2).toNat)⁻¹ * (e₃ ^ (-lam 2).toNat * W D) := (inv_mul_cancel_left₀ hnn _).symm
    _ = (e₃ ^ (-lam 2).toNat)⁻¹ * (e₃ ^ (lam 2).toNat * (W 1 * ((cNormQ v)⁻¹ ^ (lam 0 - lam 2).toNat *
          twoRowCoeff e₁ e₂ e₃ (lam 0 - lam 2).toNat (lam 1 - lam 2).toNat))) := by rw [hmul]
    _ = e₃ ^ lam 2 * (W 1 * ((cNormQ v)⁻¹ ^ (lam 0 - lam 2).toNat *
          twoRowCoeff e₁ e₂ e₃ (lam 0 - lam 2).toNat (lam 1 - lam 2).toNat)) := by rw [hz]; ring
end

section

set_option autoImplicit false

open IsDedekindDomain NumberField NumberField.TateGlobal AutomorphicForm LanglandsTunnell.Converse LanglandsTunnell.RankinSelberg LanglandsTunnell.TateLocal MeasureTheory

p2m_open "IsDedekindDomain.HeightOneSpectrum~Extension LanglandsTunnell.CubicInduction P2MW.S_LanglandsTunnell_CubicInduction_exists_laurent_localZeta_eq_gl3LFactorPoly_of_sphericalData.LanglandsTunnell.CubicInduction NumberField.StandardAddChar"

noncomputable section

section Radius

private theorem exists_forall_norm_mul_cpow_neg_mul_lt_one (c : ℂ) (B : ℝ) {q : ℝ} (hq : 1 < q) :
    ∃ σ : ℝ, ∀ w : ℂ, σ < w.re → ‖c * (q : ℂ) ^ (-w)‖ * B < 1 := by
  have hq0 : 0 < q := zero_lt_one.trans hq
  set A : ℝ := ‖c‖ * B with hA
  refine ⟨Real.logb q (|A| + 1), fun w hw => ?_⟩
  rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hq0, Complex.neg_re, mul_assoc, mul_comm (q ^ (-w.re)),
    ← mul_assoc, ← hA]
  have hpow : q ^ (-w.re) < (|A| + 1)⁻¹ := by
    rw [← Real.rpow_neg_one, ← Real.rpow_logb hq0 hq.ne' (by positivity : (0 : ℝ) < |A| + 1),
      ← Real.rpow_mul hq0.le, mul_neg_one]
    exact Real.rpow_lt_rpow_of_exponent_lt hq (by linarith)
  have hpos : 0 < q ^ (-w.re) := Real.rpow_pos_of_pos hq0 _
  have hA1 : 0 < |A| + 1 := by positivity
  calc A * q ^ (-w.re) ≤ |A| * q ^ (-w.re) := mul_le_mul_of_nonneg_right (le_abs_self A) hpos.le
    _ ≤ |A| * (|A| + 1)⁻¹ := mul_le_mul_of_nonneg_left hpow.le (abs_nonneg A)
    _ < 1 := by rw [mul_inv_lt_iff₀ hA1, one_mul]; linarith

private theorem one_lt_absNorm_real (v : HeightOneSpectrum (𝓞 ℚ)) : (1 : ℝ) < (Ideal.absNorm v.asIdeal : ℝ) := by
  have h0 : Ideal.absNorm v.asIdeal ≠ 0 := Ideal.absNorm_eq_zero_iff.not.mpr v.ne_bot
  have h1 : Ideal.absNorm v.asIdeal ≠ 1 := by
    rw [Ne, Ideal.absNorm_eq_one_iff]
    exact v.isPrime.ne_top
  exact_mod_cast (show 1 < Ideal.absNorm v.asIdeal by omega)

private theorem exists_forall_norm_mul_absNorm_cpow_neg_mul_lt_one (v : HeightOneSpectrum (𝓞 ℚ)) (c : ℂ) (B : ℝ) :
    ∃ σ : ℝ, ∀ w : ℂ, σ < w.re → ‖c * (Ideal.absNorm v.asIdeal : ℂ) ^ (-w)‖ * B < 1 := by
  obtain ⟨σ, hσ⟩ := exists_forall_norm_mul_cpow_neg_mul_lt_one c B (one_lt_absNorm_real v)
  refine ⟨σ, fun w hw => ?_⟩
  have h := hσ w hw
  rwa [Complex.ofReal_natCast] at h

end Radius

section ZeroFunction

variable (v : HeightOneSpectrum (𝓞 ℚ)) {W : LocalGL3 v → ℂ} (hW0 : ∀ g, W g = 0)
  (χ : (v.adicCompletion ℚ)ˣ →* ℂˣ)
include hW0

private theorem localZeta30_eq_zero_of_forall_eq_zero (s : ℂ) (g : LocalGL3 v) :
    letI := localBorel ℚ v
    localZeta30 v (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ v))) W χ s g = 0 := by
  simp only [localZeta30, hW0, zero_mul, integral_zero]

private theorem localZetaDual31_eq_zero_of_forall_eq_zero (w : ℂ) (g : LocalGL3 v) :
    letI := localBorel ℚ v
    localZetaDual31 v (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ v))) (selfDualHaarAt ℚ v) W χ w g =
      0 := by
  simp only [localZetaDual31, localZeta31, dualWhittakerFn3_apply, hW0, integral_zero, zero_mul]

private theorem isLocalZeta30ConvergentAbove_of_forall_eq_zero (g : LocalGL3 v) (σ : ℝ) :
    letI := localBorel ℚ v
    IsLocalZeta30ConvergentAbove v (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ v))) W χ g σ := by
  simp only [IsLocalZeta30ConvergentAbove, hW0, zero_mul]
  exact fun _ _ => integrable_zero _ _ _

private theorem isLocalZeta31ConvergentAbove_dual_of_forall_eq_zero (g : LocalGL3 v) (σ : ℝ) :
    letI := localBorel ℚ v
    IsLocalZeta31ConvergentAbove v (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ v)))
      (selfDualHaarAt ℚ v) (dualWhittakerFn3 W) χ⁻¹ (weylPrime3 * transposeInv3 g) σ := by
  simp only [IsLocalZeta31ConvergentAbove, dualWhittakerFn3_apply, hW0, zero_mul]
  exact fun _ _ => integrable_zero _ _ _

end ZeroFunction

end
end

section

set_option autoImplicit false

open IsDedekindDomain NumberField NumberField.TateGlobal AutomorphicForm LanglandsTunnell.Converse LanglandsTunnell.RankinSelberg

p2m_open "LanglandsTunnell.CubicInduction P2MW.S_LanglandsTunnell_CubicInduction_exists_laurent_localZeta_eq_gl3LFactorPoly_of_sphericalData.LanglandsTunnell.CubicInduction MeasureTheory NumberField.StandardAddChar"
open scoped WithZero

namespace LanglandsTunnell
p2m_export "LanglandsTunnell" "TateLocal.localBorel TateLocal.borelSpace_localBorel TateLocal.stdRootNumberAt TateLocal.higherUnitsAt TateLocal.mem_higherUnitsAt_iff TateLocal.HasConductorExponentAt TateLocal.modulus TateLocal.modulus_mul"
namespace CubicInduction
p2m_export "LanglandsTunnell.CubicInduction" "localZeta31 localZeta30 localZetaDual31 IsLocalZeta30ConvergentAbove IsLocalZeta31ConvergentAbove lowerUnipotent21 lowerUnipotent21_coe longWeyl3 longWeyl3_coe dualWhittakerFn3 dualWhittakerFn3_apply weylPrime3 weylPrime3_coe transposeInv3_weylPrime3 transposeInv3_lowerUnipotent21 IsGL3PsiWhittakerFn transposeInv3 upperUnipotent3 upperUnipotent3_coe upperUnipotent3_zero embedMat2 iotaGL coe_iotaGL localMaximalCompact3 mem_localMaximalCompact3_iff LocalGL3 varpi varpi_ne_zero heckeGen1 heckeGen2 centralGen cNormQ cosetSum IsCosetEigenfunction IsRightInvariant diagUnitGL2 coe_diagUnitGL2 diagHom diagHom_apply ratPrimeAt ratPrimeAt_ne_zero ratPrimeUnit sphericalTorusValue diagUnits2 coe_diagUnits2 twoRowPointLocal twoRowPointLocal_zero_right eq_zero_of_coe_eq_diagonal_of_valued_lt_of_isGL3PsiWhittakerFn eq_zero_of_isCosetEigenfunction_of_isGL3PsiWhittakerFn_of_apply_one_eq_zero exists_eq_upperUnipotent3_mul_diagonal_mul_mem_localMaximalCompact3 isGL3PsiWhittakerFn_dualWhittakerFn3 sphericalTorusValue_eq_of_isCosetEigenfunction_of_isGL3PsiWhittakerFn"
p2m_open "LanglandsTunnell.CubicInduction LanglandsTunnell"

section Cores

variable {K : Type*} [Field K] [Valued K ℤᵐ⁰]

private theorem exists_forall_valued_mul_entry_le (N : Matrix (Fin 3) (Fin 3) K) :
    ∃ R : ℤ, ∀ t : K, Valued.v t ≤ WithZero.exp R → ∀ i j, Valued.v (t * N i j) ≤ 1 := by
  obtain ⟨γ, hγ⟩ : ∃ γ : ℤᵐ⁰, ∀ i j, Valued.v (N i j) ≤ γ := by
    obtain ⟨γ, hγ⟩ := (Set.finite_range fun p : Fin 3 × Fin 3 => Valued.v (N p.1 p.2)).bddAbove
    exact ⟨γ, fun i j => hγ ⟨(i, j), rfl⟩⟩
  by_cases hγ0 : γ = 0
  · refine ⟨0, fun t _ i j => ?_⟩
    have h0 : Valued.v (N i j) = 0 := le_antisymm (hγ0 ▸ hγ i j) zero_le'
    rw [Valuation.map_mul, h0, mul_zero]
    exact zero_le'
  · refine ⟨-WithZero.log γ, fun t ht i j => ?_⟩
    rw [Valuation.map_mul]
    calc Valued.v t * Valued.v (N i j) ≤ WithZero.exp (-WithZero.log γ) * γ := mul_le_mul' ht (hγ i j)
      _ = WithZero.exp (-WithZero.log γ) * WithZero.exp (WithZero.log γ) := by rw [WithZero.exp_log hγ0]
      _ = 1 := by rw [← WithZero.exp_add, neg_add_cancel, WithZero.exp_zero]

private theorem valued_one_add_smul_entry_le (N : Matrix (Fin 3) (Fin 3) K) (t : K)
    (h : ∀ i j, Valued.v (t * N i j) ≤ 1) (i j : Fin 3) : Valued.v ((1 + t • N) i j) ≤ 1 := by
  rw [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
  refine (Valuation.map_add _ _ _).trans (max_le ?_ (h i j))
  by_cases hij : i = j
  · subst hij; simp
  · simp [Matrix.one_apply_ne hij]

private theorem norm_eq_one_of_pow_eq_one {z : ℂ} {n : ℕ} (hn : n ≠ 0) (h : z ^ n = 1) : ‖z‖ = 1 := by
  have h1 : ‖z‖ ^ n = 1 := by rw [← norm_pow, h, norm_one]
  exact (pow_eq_one_iff_of_nonneg (norm_nonneg z) hn).1 h1

private theorem isOpen_setOf_valued_sub_lt (α w : K) (hw : Valued.v w ≠ 0) :
    IsOpen {y : K | Valued.v (y - α) < Valued.v w} := by
  rw [isOpen_iff_mem_nhds]
  intro y hy
  rw [Valued.mem_nhds]
  have hw' : Valued.v.restrict w ≠ 0 := fun h0 => hw (Valued.v.restrict_eq_zero_iff.mp h0)
  refine ⟨Units.mk0 _ hw', fun y' hy' => ?_⟩
  have h1 : Valued.v (y' - y) < Valued.v w := Valued.v.restrict_lt_iff.mp hy'
  have h2 : y' - α = (y' - y) + (y - α) := by ring
  show Valued.v (y' - α) < Valued.v w
  rw [h2]
  exact (Valuation.map_add _ _ _).trans_lt (max_lt h1 hy)

private theorem exists_eq_mul_of_valued_sub_lt (α β : Kˣ) (r : ℤᵐ⁰) (hr : r ≤ 1)
    (h : Valued.v ((β : K) - α) < r * Valued.v (α : K)) :
    ∃ u : Kˣ, Valued.v (u : K) = 1 ∧ Valued.v ((u : K) - 1) < r ∧ β = α * u := by
  have hα : Valued.v (α : K) ≠ 0 := (Valuation.ne_zero_iff _).2 α.ne_zero
  have hlt : Valued.v ((β : K) - α) < Valued.v (α : K) :=
    h.trans_le (by simpa using mul_le_mul_left hr (Valued.v (α : K)))
  have hβ : Valued.v (β : K) = Valued.v (α : K) := by
    have := Valuation.map_add_eq_of_lt_left (Valued.v) (x := (α : K)) (y := (β : K) - α) hlt
    rwa [add_sub_cancel] at this
  refine ⟨α⁻¹ * β, ?_, ?_, by rw [mul_inv_cancel_left]⟩
  · rw [Units.val_mul, Valuation.map_mul, Units.val_inv_eq_inv_val, map_inv₀, hβ, inv_mul_cancel₀ hα]
  · have hrepr : ((α⁻¹ * β : Kˣ) : K) - 1 = ((α⁻¹ : Kˣ) : K) * ((β : K) - α) := by
      rw [mul_sub, Units.val_mul, Units.inv_mul]
    rw [hrepr, Valuation.map_mul, Units.val_inv_eq_inv_val, map_inv₀]
    calc (Valued.v (α : K))⁻¹ * Valued.v ((β : K) - α)
        < (Valued.v (α : K))⁻¹ * (r * Valued.v (α : K)) := by
          refine mul_lt_mul_of_pos_left h ?_
          exact inv_pos.2 (lt_of_le_of_ne zero_le' (Ne.symm hα))
      _ = r := by rw [mul_comm r, ← mul_assoc, inv_mul_cancel₀ hα, one_mul]

section Measurable

variable [MeasurableSpace K] [OpensMeasurableSpace K]

private theorem measurable_of_forall_exists_valued_sub_lt_imp (f : Kˣ → ℂ)
    (hf : ∀ α : Kˣ, ∃ w : K, Valued.v w ≠ 0 ∧ ∀ β : Kˣ, Valued.v ((β : K) - α) < Valued.v w → f β = f α) :
    Measurable f := by
  choose w hw hfw using hf
  intro S _
  have key : f ⁻¹' S = Units.val ⁻¹'
      (⋃ (α : Kˣ) (_ : α ∈ f ⁻¹' S), {y : K | Valued.v (y - (α : K)) < Valued.v (w α)}) := by
    ext β
    simp only [Set.mem_preimage, Set.mem_iUnion, Set.mem_setOf_eq, exists_prop]
    constructor
    · intro hβ
      refine ⟨β, hβ, ?_⟩
      rw [sub_self, Valuation.map_zero]
      exact lt_of_le_of_ne zero_le' (Ne.symm (hw β))
    · rintro ⟨α, hα, hβα⟩
      rw [hfw α β hβα]
      exact hα
  rw [key]
  exact (comap_measurable (Units.val : Kˣ → K))
    (isOpen_biUnion fun (α : Kˣ) _ => isOpen_setOf_valued_sub_lt (α : K) (w α) (hw α)).measurableSet

variable [SecondCountableTopology K]

private theorem measurable_prod_of_forall_exists_valued_sub_lt_imp (f : Kˣ × K → ℂ)
    (hf : ∀ (β : Kˣ) (x : K), ∃ w₁ w₂ : K, Valued.v w₁ ≠ 0 ∧ Valued.v w₂ ≠ 0 ∧
      ∀ (β' : Kˣ) (x' : K), Valued.v ((β' : K) - β) < Valued.v w₁ → Valued.v (x' - x) < Valued.v w₂ →
        f (β', x') = f (β, x)) :
    Measurable f := by
  choose w₁ w₂ hw₁ hw₂ hfw using hf
  intro S _
  have key : f ⁻¹' S = (fun q : Kˣ × K => ((q.1 : K), q.2)) ⁻¹' (⋃ (p : Kˣ × K) (_ : p ∈ f ⁻¹' S),
      {y : K | Valued.v (y - (p.1 : K)) < Valued.v (w₁ p.1 p.2)} ×ˢ
        {x : K | Valued.v (x - p.2) < Valued.v (w₂ p.1 p.2)}) := by
    ext q
    simp only [Set.mem_preimage, Set.mem_iUnion, Set.mem_prod, Set.mem_setOf_eq, exists_prop]
    constructor
    · intro hq
      refine ⟨q, hq, ?_, ?_⟩
      · rw [sub_self, Valuation.map_zero]
        exact lt_of_le_of_ne zero_le' (Ne.symm (hw₁ q.1 q.2))
      · rw [sub_self, Valuation.map_zero]
        exact lt_of_le_of_ne zero_le' (Ne.symm (hw₂ q.1 q.2))
    · rintro ⟨p, hp, h1, h2⟩
      rw [show q = (q.1, q.2) from rfl, hfw p.1 p.2 q.1 q.2 h1 h2]
      exact hp
  rw [key]
  refine (((comap_measurable (Units.val : Kˣ → K)).comp measurable_fst).prodMk measurable_snd) ?_
  refine (isOpen_biUnion fun (p : Kˣ × K) _ => ?_).measurableSet
  exact (isOpen_setOf_valued_sub_lt (p.1 : K) (w₁ p.1 p.2) (hw₁ p.1 p.2)).prod
    (isOpen_setOf_valued_sub_lt p.2 (w₂ p.1 p.2) (hw₂ p.1 p.2))

end Measurable

end Cores

variable (v : HeightOneSpectrum (𝓞 ℚ))

section ValuationPrivates

variable {v}

private theorem embedMat2_diagUnitGL2_eq (u : (v.adicCompletion ℚ)ˣ) :
    embedMat2 ((diagUnitGL2 u : GL (Fin 2) (v.adicCompletion ℚ)) : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)) =
      1 + ((u : v.adicCompletion ℚ) - 1) •
        (!![1, 0, 0; 0, 0, 0; 0, 0, 0] : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [embedMat2]

private theorem coe_lowerUnipotent21_eq (z : v.adicCompletion ℚ) :
    ((lowerUnipotent21 z : LocalGL3 v) : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) =
      1 + z • (!![0, 0, 0; 1, 0, 0; 0, 0, 0] : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp

private theorem diagUnitGL2_inv (u : (v.adicCompletion ℚ)ˣ) :
    (diagUnitGL2 u : GL (Fin 2) (v.adicCompletion ℚ))⁻¹ = diagUnitGL2 u⁻¹ :=
  Units.ext rfl

private theorem lowerUnipotent21_inv (z : v.adicCompletion ℚ) :
    (lowerUnipotent21 z : LocalGL3 v)⁻¹ = lowerUnipotent21 (-z) :=
  Units.ext rfl

private theorem coe_conj_eq {K : Type*} [Field K] (g₀ X : GL (Fin 3) K) (t : K) (E : Matrix (Fin 3) (Fin 3) K)
    (hX : (X : Matrix (Fin 3) (Fin 3) K) = 1 + t • E) :
    ((g₀⁻¹ * X * g₀ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
      1 + t • (((g₀⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) * E * (g₀ : Matrix (Fin 3) (Fin 3) K)) := by
  rw [Units.val_mul, Units.val_mul, hX, Matrix.mul_add, Matrix.mul_one, Matrix.add_mul, Units.inv_mul,
    Matrix.mul_smul, Matrix.smul_mul]

private theorem valued_inv_sub_one (u : (v.adicCompletion ℚ)ˣ) (hu : Valued.v (u : v.adicCompletion ℚ) = 1) :
    Valued.v (((u⁻¹ : (v.adicCompletion ℚ)ˣ) : v.adicCompletion ℚ) - 1) =
      Valued.v ((u : v.adicCompletion ℚ) - 1) := by
  have h : ((u⁻¹ : (v.adicCompletion ℚ)ˣ) : v.adicCompletion ℚ) - 1 =
      ((u⁻¹ : (v.adicCompletion ℚ)ˣ) : v.adicCompletion ℚ) * (1 - u) := by
    rw [mul_sub, mul_one, Units.inv_mul]
  rw [h, Valuation.map_mul, Units.val_inv_eq_inv_val, map_inv₀, hu, inv_one, one_mul, Valuation.map_sub_swap]

private theorem conj_mem (g₀ X : LocalGL3 v) (t t' : v.adicCompletion ℚ)
    (E : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ))
    (hX : (X : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) = 1 + t • E)
    (hX' : ((X⁻¹ : LocalGL3 v) : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) = 1 + t' • E)
    (ht : ∀ i j, Valued.v (t * (((g₀⁻¹ : LocalGL3 v) : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) * E *
      (g₀ : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ))) i j) ≤ 1)
    (ht' : ∀ i j, Valued.v (t' * (((g₀⁻¹ : LocalGL3 v) : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) * E *
      (g₀ : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ))) i j) ≤ 1) :
    g₀⁻¹ * X * g₀ ∈ localMaximalCompact3 (𝓞 ℚ) ℚ v := by
  rw [mem_localMaximalCompact3_iff]
  refine ⟨fun i j => ?_, fun i j => ?_⟩
  · rw [coe_conj_eq g₀ X t E hX]
    exact valued_one_add_smul_entry_le _ _ ht i j
  · have hinv : (g₀⁻¹ * X * g₀)⁻¹ = g₀⁻¹ * X⁻¹ * g₀ := by
      rw [mul_inv_rev, mul_inv_rev, inv_inv, mul_assoc]
    rw [hinv, coe_conj_eq g₀ X⁻¹ t' E hX']
    exact valued_one_add_smul_entry_le _ _ ht' i j

private theorem valued_varpi_pow (m : ℕ) : Valued.v (varpi v ^ m) = WithZero.exp (-(m : ℤ)) := by
  rw [Valuation.map_pow, AdelicLevel.valued_uniformizerUnit ℚ v, ← WithZero.exp_nsmul]
  congr 1
  simp

private theorem valued_varpi_zpow (n : ℤ) : Valued.v (varpi v ^ n) = WithZero.exp (-n) := by
  rw [map_zpow₀, AdelicLevel.valued_uniformizerUnit ℚ v, ← WithZero.exp_zsmul]
  congr 1
  simp

private scoped instance separableSpace_adicCompletion_rat : TopologicalSpace.SeparableSpace (v.adicCompletion ℚ) where
  exists_countable_dense :=
    ⟨_, Set.countable_range _, IsDedekindDomain.HeightOneSpectrum.denseRange_algebraMap (K := ℚ) (v := v)⟩

end ValuationPrivates

private theorem iotaGL_diagUnitGL2_mul_iotaGL_diagUnits2_mul_upperUnipotent3 (α : (v.adicCompletion ℚ)ˣ) (k : ℤ)
    (y : v.adicCompletion ℚ) :
    iotaGL (diagUnitGL2 α) * (iotaGL (diagUnits2 1 (ratPrimeUnit v ^ k)) * upperUnipotent3 y 0 0) =
      upperUnipotent3 (((α * (ratPrimeUnit v ^ k)⁻¹ : (v.adicCompletion ℚ)ˣ) : v.adicCompletion ℚ) * y) 0 0 *
        iotaGL (diagUnits2 α (ratPrimeUnit v ^ k)) := by
  have hp : ((ratPrimeUnit v ^ k : (v.adicCompletion ℚ)ˣ) : v.adicCompletion ℚ) ≠ 0 := Units.ne_zero _
  refine Units.ext ?_
  simp only [Units.val_mul, coe_iotaGL, upperUnipotent3_coe]
  ext i j : 1
  (fin_cases i <;> fin_cases j <;> simp [embedMat2, Matrix.mul_apply, Fin.sum_univ_three])
  field_simp

private theorem norm_psiLocal_rat_apply (x : v.adicCompletion ℚ) : ‖psiLocal ℚ v x‖ = 1 := by
  obtain ⟨N, hN⟩ : ∃ N : ℕ, Valued.v (ratPrimeAt v ^ N * x) ≤ 1 := by
    by_cases hx : Valued.v x = 0
    · exact ⟨0, by rw [pow_zero, one_mul, hx]; exact zero_le'⟩
    · refine ⟨(WithZero.log (Valued.v x)).toNat, ?_⟩
      rw [Valuation.map_mul, Valuation.map_pow, valued_ratPrimeAt_eq_valued_varpi,
        AdelicLevel.valued_uniformizerUnit ℚ v, ← WithZero.exp_log hx, ← WithZero.exp_nsmul, ← WithZero.exp_add,
        ← WithZero.exp_zero, WithZero.exp_le_exp]
      simp only [nsmul_eq_mul, mul_neg, mul_one, WithZero.log_exp]
      omega
  have hq : Ideal.absNorm v.asIdeal ^ N ≠ 0 := by
    have h := NumberField.HeightOneSpectrum.one_lt_absNorm v
    exact pow_ne_zero _ (by omega)
  have h1 : psiLocal ℚ v x ^ (Ideal.absNorm v.asIdeal ^ N) = 1 := by
    rw [← AddChar.map_nsmul_eq_pow, nsmul_eq_mul, Nat.cast_pow]
    exact psiLocal_rat_apply_eq_one_of_valued_le_one v _ hN
  exact norm_eq_one_of_pow_eq_one hq h1

private theorem norm_apply_iotaGL_diagUnitGL2_mul_of_isGL3PsiWhittakerFn (W : LocalGL3 v → ℂ)
    (hψ : IsGL3PsiWhittakerFn (psiLocal ℚ v) W) (α : (v.adicCompletion ℚ)ˣ) (k : ℤ) (y : v.adicCompletion ℚ) :
    ‖W (iotaGL (diagUnitGL2 α) * (iotaGL (diagUnits2 1 (ratPrimeUnit v ^ k)) * upperUnipotent3 y 0 0))‖ =
      ‖W (iotaGL (diagUnits2 α (ratPrimeUnit v ^ k)))‖ := by
  rw [iotaGL_diagUnitGL2_mul_iotaGL_diagUnits2_mul_upperUnipotent3, hψ, add_zero, norm_mul, norm_psiLocal_rat_apply,
    one_mul]

private theorem exists_forall_mem_higherUnitsAt_conj_iotaGL_diagUnitGL2_mem (g₀ : LocalGL3 v) :
    ∃ m : ℕ, ∀ u ∈ TateLocal.higherUnitsAt ℚ v m,
      g₀⁻¹ * iotaGL (diagUnitGL2 u) * g₀ ∈ localMaximalCompact3 (𝓞 ℚ) ℚ v := by
  obtain ⟨R, hR⟩ := exists_forall_valued_mul_entry_le
    (((g₀⁻¹ : LocalGL3 v) : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) * !![1, 0, 0; 0, 0, 0; 0, 0, 0] *
      (g₀ : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)))
  refine ⟨(-R).toNat + 1, fun u hu => ?_⟩
  rw [TateLocal.mem_higherUnitsAt_iff] at hu
  have hu1 : Valued.v ((u : v.adicCompletion ℚ) - 1) ≤ WithZero.exp R := by
    rcases hu.2 with h0 | h
    · exact absurd h0 (Nat.succ_ne_zero _)
    · exact h.trans (WithZero.exp_le_exp.2 (by push_cast; omega))
  have hu2 : Valued.v (((u⁻¹ : (v.adicCompletion ℚ)ˣ) : v.adicCompletion ℚ) - 1) ≤ WithZero.exp R := by
    rw [valued_inv_sub_one u hu.1]
    exact hu1
  refine conj_mem g₀ _ _ _ _ ?_ ?_ (hR _ hu1) (hR _ hu2)
  · rw [coe_iotaGL, embedMat2_diagUnitGL2_eq]
  · rw [← map_inv, diagUnitGL2_inv, coe_iotaGL, embedMat2_diagUnitGL2_eq]

private theorem exists_forall_valued_le_conj_lowerUnipotent21_mem (g₀ : LocalGL3 v) :
    ∃ R : ℤ, ∀ z : v.adicCompletion ℚ, Valued.v z ≤ WithZero.exp R →
      g₀⁻¹ * lowerUnipotent21 z * g₀ ∈ localMaximalCompact3 (𝓞 ℚ) ℚ v := by
  obtain ⟨R, hR⟩ := exists_forall_valued_mul_entry_le
    (((g₀⁻¹ : LocalGL3 v) : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) * !![0, 0, 0; 1, 0, 0; 0, 0, 0] *
      (g₀ : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)))
  refine ⟨R, fun z hz => ?_⟩
  have hz' : Valued.v (-z) ≤ WithZero.exp R := by rwa [Valuation.map_neg]
  refine conj_mem g₀ _ z (-z) _ (coe_lowerUnipotent21_eq z) ?_ (hR z hz) (hR (-z) hz')
  rw [lowerUnipotent21_inv, coe_lowerUnipotent21_eq]

private theorem measurable_of_forall_exists_forall_mem_higherUnitsAt_apply_mul_eq (f : (v.adicCompletion ℚ)ˣ → ℂ)
    (hf : ∀ α : (v.adicCompletion ℚ)ˣ, ∃ m : ℕ, ∀ u ∈ TateLocal.higherUnitsAt ℚ v m, f (α * u) = f α) :
    letI := TateLocal.localBorel ℚ v
    Measurable f := by
  letI := TateLocal.localBorel ℚ v
  haveI : BorelSpace (v.adicCompletion ℚ) := TateLocal.borelSpace_localBorel ℚ v
  refine measurable_of_forall_exists_valued_sub_lt_imp f fun α => ?_
  obtain ⟨m, hm⟩ := hf α
  refine ⟨(α : v.adicCompletion ℚ) * varpi v ^ m, ?_, fun β hβ => ?_⟩
  · exact (Valuation.ne_zero_iff _).2 (mul_ne_zero α.ne_zero (pow_ne_zero _ (varpi_ne_zero v)))
  · rw [Valuation.map_mul, valued_varpi_pow, mul_comm] at hβ
    obtain ⟨u, hu1, hu2, rfl⟩ := exists_eq_mul_of_valued_sub_lt α β (WithZero.exp (-(m : ℤ)))
      (by rw [← WithZero.exp_zero, WithZero.exp_le_exp]; omega) hβ
    exact hm u ((TateLocal.mem_higherUnitsAt_iff ℚ v).2 ⟨hu1, Or.inr hu2.le⟩)

private theorem measurable_of_forall_exists_forall_apply_mul_add_eq (f : (v.adicCompletion ℚ)ˣ × v.adicCompletion ℚ → ℂ)
    (hf : ∀ (β : (v.adicCompletion ℚ)ˣ) (x : v.adicCompletion ℚ), ∃ (m : ℕ) (R : ℤ),
      ∀ u ∈ TateLocal.higherUnitsAt ℚ v m, ∀ z : v.adicCompletion ℚ, Valued.v z ≤ WithZero.exp R →
        f (β * u, x + z) = f (β, x)) :
    letI := TateLocal.localBorel ℚ v
    Measurable f := by
  letI := TateLocal.localBorel ℚ v
  haveI : BorelSpace (v.adicCompletion ℚ) := TateLocal.borelSpace_localBorel ℚ v
  refine measurable_prod_of_forall_exists_valued_sub_lt_imp f fun β x => ?_
  obtain ⟨m, R, hmR⟩ := hf β x
  refine ⟨(β : v.adicCompletion ℚ) * varpi v ^ m, varpi v ^ (-R), ?_, ?_, fun β' x' hβ' hx' => ?_⟩
  · exact (Valuation.ne_zero_iff _).2 (mul_ne_zero β.ne_zero (pow_ne_zero _ (varpi_ne_zero v)))
  · exact (Valuation.ne_zero_iff _).2 (zpow_ne_zero _ (varpi_ne_zero v))
  · rw [Valuation.map_mul, valued_varpi_pow, mul_comm] at hβ'
    rw [valued_varpi_zpow, neg_neg] at hx'
    obtain ⟨u, hu1, hu2, rfl⟩ := exists_eq_mul_of_valued_sub_lt β β' (WithZero.exp (-(m : ℤ)))
      (by rw [← WithZero.exp_zero, WithZero.exp_le_exp]; omega) hβ'
    have key := hmR u ((TateLocal.mem_higherUnitsAt_iff ℚ v).2 ⟨hu1, Or.inr hu2.le⟩) (x' - x) hx'.le
    rwa [add_sub_cancel] at key

end LanglandsTunnell.CubicInduction
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_laurent_localZeta_eq_gl3LFactorPoly_of_sphericalData.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_exists_laurent_localZeta_eq_gl3LFactorPoly_of_sphericalData.LanglandsTunnell.CubicInduction"
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_laurent_localZeta_eq_gl3LFactorPoly_of_sphericalData.LanglandsTunnell"
end
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_laurent_localZeta_eq_gl3LFactorPoly_of_sphericalData.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_exists_laurent_localZeta_eq_gl3LFactorPoly_of_sphericalData.LanglandsTunnell.CubicInduction"

section

set_option autoImplicit false

open IsDedekindDomain NumberField NumberField.TateGlobal AutomorphicForm LanglandsTunnell.Converse LanglandsTunnell.RankinSelberg LanglandsTunnell.TateLocal MeasureTheory

p2m_open "IsDedekindDomain.HeightOneSpectrum~Extension LanglandsTunnell.CubicInduction P2MW.S_LanglandsTunnell_CubicInduction_exists_laurent_localZeta_eq_gl3LFactorPoly_of_sphericalData.LanglandsTunnell.CubicInduction NumberField.StandardAddChar"

section Involution

variable {A : Type*} [CommRing A]

private theorem coe_transposeInv3 (g : GL (Fin 3) A) :
    ((transposeInv3 g : GL (Fin 3) A) : Matrix (Fin 3) (Fin 3) A) =
      Matrix.transpose ((g⁻¹ : GL (Fin 3) A) : Matrix (Fin 3) (Fin 3) A) :=
  rfl

private theorem coe_transposeInv3_inv (g : GL (Fin 3) A) :
    (((transposeInv3 g)⁻¹ : GL (Fin 3) A) : Matrix (Fin 3) (Fin 3) A) =
      Matrix.transpose ((g : GL (Fin 3) A) : Matrix (Fin 3) (Fin 3) A) :=
  rfl

private theorem transposeInv3_mul (g h : GL (Fin 3) A) :
    transposeInv3 (g * h) = transposeInv3 g * transposeInv3 h := by
  refine Units.ext ?_
  rw [Units.val_mul, coe_transposeInv3, coe_transposeInv3, coe_transposeInv3, mul_inv_rev, Units.val_mul,
    Matrix.transpose_mul]

private theorem transposeInv3_transposeInv3 (g : GL (Fin 3) A) : transposeInv3 (transposeInv3 g) = g := by
  refine Units.ext ?_
  rw [coe_transposeInv3, coe_transposeInv3_inv, Matrix.transpose_transpose]

private theorem coe_longWeyl3_inv :
    (((longWeyl3 : GL (Fin 3) A)⁻¹ : GL (Fin 3) A) : Matrix (Fin 3) (Fin 3) A) = !![0, 0, 1; 0, 1, 0; 1, 0, 0] :=
  rfl

private theorem transposeInv3_longWeyl3 : transposeInv3 (longWeyl3 : GL (Fin 3) A) = longWeyl3 := by
  refine Units.ext ?_
  rw [coe_transposeInv3, coe_longWeyl3_inv, longWeyl3_coe]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.transpose_apply]

private theorem longWeyl3_mul_longWeyl3 : (longWeyl3 : GL (Fin 3) A) * longWeyl3 = 1 := by
  refine Units.ext ?_
  rw [Units.val_mul, Units.val_one]
  exact (longWeyl3 : GL (Fin 3) A).val_inv

private theorem contragredient3_aux_involutive (g : GL (Fin 3) A) :
    longWeyl3 * transposeInv3 (longWeyl3 * transposeInv3 g * longWeyl3) * longWeyl3 = g := by
  rw [transposeInv3_mul, transposeInv3_mul, transposeInv3_longWeyl3, transposeInv3_transposeInv3]
  calc longWeyl3 * (longWeyl3 * g * longWeyl3) * longWeyl3
      = (longWeyl3 * longWeyl3) * g * (longWeyl3 * longWeyl3) := by simp only [mul_assoc]
    _ = g := by rw [longWeyl3_mul_longWeyl3, one_mul, mul_one]

private theorem contragredient3_aux_mul (g h : GL (Fin 3) A) :
    longWeyl3 * transposeInv3 (g * h) * longWeyl3 =
      (longWeyl3 * transposeInv3 g * longWeyl3) * (longWeyl3 * transposeInv3 h * longWeyl3) := by
  rw [transposeInv3_mul]
  calc longWeyl3 * (transposeInv3 g * transposeInv3 h) * longWeyl3
      = longWeyl3 * transposeInv3 g * (longWeyl3 * longWeyl3) * transposeInv3 h * longWeyl3 := by
        rw [longWeyl3_mul_longWeyl3, mul_one]; simp only [mul_assoc]
    _ = (longWeyl3 * transposeInv3 g * longWeyl3) * (longWeyl3 * transposeInv3 h * longWeyl3) := by
        simp only [mul_assoc]

private noncomputable def contragredient3 : GL (Fin 3) A ≃* GL (Fin 3) A where
  toFun g := longWeyl3 * transposeInv3 g * longWeyl3
  invFun g := longWeyl3 * transposeInv3 g * longWeyl3
  left_inv g := contragredient3_aux_involutive g
  right_inv g := contragredient3_aux_involutive g
  map_mul' g h := contragredient3_aux_mul g h

private theorem contragredient3_apply (g : GL (Fin 3) A) :
    contragredient3 g = longWeyl3 * transposeInv3 g * longWeyl3 :=
  rfl

private theorem dualWhittakerFn3_eq_apply_contragredient3_mul {R : Type*} (W : GL (Fin 3) A → R) (g : GL (Fin 3) A) :
    dualWhittakerFn3 W g = W (contragredient3 g * longWeyl3) := by
  rw [dualWhittakerFn3_apply, contragredient3_apply, mul_assoc, longWeyl3_mul_longWeyl3, mul_one]

private theorem contragredient3_contragredient3 (g : GL (Fin 3) A) :
    contragredient3 (contragredient3 g) = g :=
  contragredient3_aux_involutive g

end Involution
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_laurent_localZeta_eq_gl3LFactorPoly_of_sphericalData.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_exists_laurent_localZeta_eq_gl3LFactorPoly_of_sphericalData.LanglandsTunnell.CubicInduction"

section CosetSystems

variable {G : Type*} [Group G]

private theorem isHeckeCosetSystem_mulEquiv (e : G ≃* G) {U : Subgroup G} (hU : ∀ x, e x ∈ U ↔ x ∈ U) {gen : G}
    {ι : Type*} {reps : ι → G} (h : HeckeIntegralSeam.IsHeckeCosetSystem U gen reps) :
    HeckeIntegralSeam.IsHeckeCosetSystem U (e gen) (e ∘ reps) := by
  refine ⟨fun i => ?_, fun x hx => ?_, fun i j hij => ?_⟩
  · obtain ⟨u, hu, u', hu', huu'⟩ := HeckePair.mem_doubleCoset_iff.1 (h.mem_doubleCoset i)
    refine HeckePair.mem_doubleCoset_iff.2 ⟨e u, (hU u).2 hu, e u', (hU u').2 hu', ?_⟩
    rw [Function.comp_apply, ← huu', map_mul, map_mul]
  · obtain ⟨u, hu, u', hu', huu'⟩ := HeckePair.mem_doubleCoset_iff.1 hx
    have hx' : e.symm x ∈ HeckePair.doubleCoset U gen := by
      refine HeckePair.mem_doubleCoset_iff.2 ⟨e.symm u, ?_, e.symm u', ?_, ?_⟩
      · rw [← hU, e.apply_symm_apply]; exact hu
      · rw [← hU, e.apply_symm_apply]; exact hu'
      · rw [← huu', map_mul, map_mul, e.symm_apply_apply]
    obtain ⟨i, hi⟩ := h.covers _ hx'
    refine ⟨i, ?_⟩
    rw [QuotientGroup.eq] at hi ⊢
    have h' := (hU _).2 hi
    simpa only [map_mul, map_inv, MulEquiv.apply_symm_apply, Function.comp_apply] using h'
  · have hij' : (QuotientGroup.mk (e (reps i)) : G ⧸ U) = QuotientGroup.mk (e (reps j)) := hij
    rw [QuotientGroup.eq, ← map_inv, ← map_mul, hU] at hij'
    exact h.mk_injective (QuotientGroup.eq.2 hij')

private theorem isHeckeCosetSystem_central_mul {U : Subgroup G} {gen : G} {ι : Type*} {reps : ι → G} (z : G)
    (hz : ∀ x : G, z * x = x * z) (h : HeckeIntegralSeam.IsHeckeCosetSystem U gen reps) :
    HeckeIntegralSeam.IsHeckeCosetSystem U (z * gen) (fun i => z * reps i) := by
  refine ⟨fun i => ?_, fun x hx => ?_, fun i j hij => ?_⟩
  · obtain ⟨u, hu, u', hu', huu'⟩ := HeckePair.mem_doubleCoset_iff.1 (h.mem_doubleCoset i)
    refine HeckePair.mem_doubleCoset_iff.2 ⟨u, hu, u', hu', ?_⟩
    rw [← huu']
    simp only [← mul_assoc]
    rw [← hz u]
  · obtain ⟨u, hu, u', hu', huu'⟩ := HeckePair.mem_doubleCoset_iff.1 hx
    have huz : u * (z * gen) = z * (u * gen) := by rw [← mul_assoc, ← hz u, mul_assoc]
    have hx' : z⁻¹ * x ∈ HeckePair.doubleCoset U gen := by
      refine HeckePair.mem_doubleCoset_iff.2 ⟨u, hu, u', hu', ?_⟩
      rw [← huu', huz, mul_assoc z, inv_mul_cancel_left]
    obtain ⟨i, hi⟩ := h.covers _ hx'
    refine ⟨i, ?_⟩
    rw [QuotientGroup.eq] at hi ⊢
    show x⁻¹ * (z * reps i) ∈ U
    rwa [mul_inv_rev, inv_inv, mul_assoc] at hi
  · have hij' : (QuotientGroup.mk (z * reps i) : G ⧸ U) = QuotientGroup.mk (z * reps j) := hij
    rw [QuotientGroup.eq, mul_inv_rev, mul_assoc, inv_mul_cancel_left] at hij'
    exact h.mk_injective (QuotientGroup.eq.2 hij')

end CosetSystems
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_laurent_localZeta_eq_gl3LFactorPoly_of_sphericalData.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_exists_laurent_localZeta_eq_gl3LFactorPoly_of_sphericalData.LanglandsTunnell.CubicInduction"

section SphericalDual

variable (v : HeightOneSpectrum (𝓞 ℚ))

private theorem valued_longWeyl3_entry (i j : Fin 3) :
    Valued.v ((!![0, 0, 1; 0, 1, 0; 1, 0, 0] : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) i j) ≤ 1 := by
  fin_cases i <;> fin_cases j <;> simp

private theorem longWeyl3_mem_localMaximalCompact3 : (longWeyl3 : LocalGL3 v) ∈ localMaximalCompact3 (𝓞 ℚ) ℚ v := by
  rw [mem_localMaximalCompact3_iff, longWeyl3_coe, coe_longWeyl3_inv]
  exact ⟨valued_longWeyl3_entry v, valued_longWeyl3_entry v⟩

private theorem transposeInv3_mem_of_mem {k : LocalGL3 v} (hk : k ∈ localMaximalCompact3 (𝓞 ℚ) ℚ v) :
    transposeInv3 k ∈ localMaximalCompact3 (𝓞 ℚ) ℚ v := by
  rw [mem_localMaximalCompact3_iff] at hk ⊢
  rw [coe_transposeInv3, coe_transposeInv3_inv]
  exact ⟨fun i j => by simpa only [Matrix.transpose_apply] using hk.2 j i,
    fun i j => by simpa only [Matrix.transpose_apply] using hk.1 j i⟩

private theorem contragredient3_mem_of_mem {k : LocalGL3 v} (hk : k ∈ localMaximalCompact3 (𝓞 ℚ) ℚ v) :
    contragredient3 k ∈ localMaximalCompact3 (𝓞 ℚ) ℚ v := by
  rw [contragredient3_apply]
  exact (localMaximalCompact3 (𝓞 ℚ) ℚ v).mul_mem
    ((localMaximalCompact3 (𝓞 ℚ) ℚ v).mul_mem (longWeyl3_mem_localMaximalCompact3 v) (transposeInv3_mem_of_mem v hk))
    (longWeyl3_mem_localMaximalCompact3 v)

private theorem contragredient3_mem_localMaximalCompact3_iff (k : LocalGL3 v) :
    contragredient3 k ∈ localMaximalCompact3 (𝓞 ℚ) ℚ v ↔ k ∈ localMaximalCompact3 (𝓞 ℚ) ℚ v := by
  refine ⟨fun h => ?_, contragredient3_mem_of_mem v⟩
  have := contragredient3_mem_of_mem v h
  rwa [contragredient3_contragredient3] at this

private theorem coe_heckeGen1_eq_diagonal :
    ((heckeGen1 v : LocalGL3 v) : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) = Matrix.diagonal ![varpi v, 1, 1] :=
  rfl

private theorem coe_heckeGen2_eq_diagonal :
    ((heckeGen2 v : LocalGL3 v) : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) =
      Matrix.diagonal ![varpi v, varpi v, 1] :=
  rfl

private theorem coe_centralGen_eq_diagonal' :
    ((centralGen v : LocalGL3 v) : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) =
      Matrix.diagonal ![varpi v, varpi v, varpi v] :=
  rfl

private theorem coe_inv_eq_diagonal (g : LocalGL3 v) (w : Fin 3 → v.adicCompletion ℚ)
    (hg : (g : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) = Matrix.diagonal w) (hw : ∀ i, w i ≠ 0) :
    ((g⁻¹ : LocalGL3 v) : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) = Matrix.diagonal fun i => (w i)⁻¹ := by
  rw [Matrix.coe_units_inv, hg]
  refine Matrix.inv_eq_left_inv ?_
  rw [Matrix.diagonal_mul_diagonal]
  have h : (fun i => (w i)⁻¹ * w i) = fun _ => (1 : v.adicCompletion ℚ) := funext fun i => inv_mul_cancel₀ (hw i)
  rw [h, Matrix.diagonal_one]

private theorem longWeyl3_mul_diagonal_mul_longWeyl3 (d : Fin 3 → v.adicCompletion ℚ) :
    (!![0, 0, 1; 0, 1, 0; 1, 0, 0] : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) * Matrix.diagonal d *
        !![0, 0, 1; 0, 1, 0; 1, 0, 0] =
      Matrix.diagonal ![d 2, d 1, d 0] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three, Matrix.vecMul_diagonal]

private theorem coe_contragredient3_eq_diagonal (g : LocalGL3 v) (w : Fin 3 → v.adicCompletion ℚ)
    (hg : (g : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) = Matrix.diagonal w) (hw : ∀ i, w i ≠ 0) :
    ((contragredient3 g : LocalGL3 v) : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) =
      Matrix.diagonal ![(w 2)⁻¹, (w 1)⁻¹, (w 0)⁻¹] := by
  rw [contragredient3_apply, Units.val_mul, Units.val_mul, coe_transposeInv3, coe_inv_eq_diagonal v g w hg hw,
    Matrix.diagonal_transpose, longWeyl3_coe, longWeyl3_mul_diagonal_mul_longWeyl3]

private theorem vec3_ne_zero_of (a b c : v.adicCompletion ℚ) (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0) :
    ∀ i, (![a, b, c] : Fin 3 → v.adicCompletion ℚ) i ≠ 0 := by
  intro i
  fin_cases i <;> assumption

private theorem contragredient3_heckeGen1 : contragredient3 (heckeGen1 v) = (centralGen v)⁻¹ * heckeGen2 v := by
  refine Units.ext ?_
  rw [coe_contragredient3_eq_diagonal v _ _ (coe_heckeGen1_eq_diagonal v)
    (vec3_ne_zero_of v _ _ _ (varpi_ne_zero v) one_ne_zero one_ne_zero), Units.val_mul,
    coe_inv_eq_diagonal v _ _ (coe_centralGen_eq_diagonal' v)
      (vec3_ne_zero_of v _ _ _ (varpi_ne_zero v) (varpi_ne_zero v) (varpi_ne_zero v)),
    coe_heckeGen2_eq_diagonal, Matrix.diagonal_mul_diagonal]
  congr 1
  funext i
  fin_cases i <;> simp [varpi_ne_zero v]

private theorem contragredient3_heckeGen2 : contragredient3 (heckeGen2 v) = (centralGen v)⁻¹ * heckeGen1 v := by
  refine Units.ext ?_
  rw [coe_contragredient3_eq_diagonal v _ _ (coe_heckeGen2_eq_diagonal v)
    (vec3_ne_zero_of v _ _ _ (varpi_ne_zero v) (varpi_ne_zero v) one_ne_zero), Units.val_mul,
    coe_inv_eq_diagonal v _ _ (coe_centralGen_eq_diagonal' v)
      (vec3_ne_zero_of v _ _ _ (varpi_ne_zero v) (varpi_ne_zero v) (varpi_ne_zero v)),
    coe_heckeGen1_eq_diagonal, Matrix.diagonal_mul_diagonal]
  congr 1
  funext i
  fin_cases i <;> simp [varpi_ne_zero v]

private theorem contragredient3_centralGen : contragredient3 (centralGen v) = (centralGen v)⁻¹ := by
  refine Units.ext ?_
  rw [coe_contragredient3_eq_diagonal v _ _ (coe_centralGen_eq_diagonal' v)
    (vec3_ne_zero_of v _ _ _ (varpi_ne_zero v) (varpi_ne_zero v) (varpi_ne_zero v)),
    coe_inv_eq_diagonal v _ _ (coe_centralGen_eq_diagonal' v)
      (vec3_ne_zero_of v _ _ _ (varpi_ne_zero v) (varpi_ne_zero v) (varpi_ne_zero v))]
  congr 1
  funext i
  fin_cases i <;> rfl

private theorem centralGen_mul_eq_mul_centralGen (x : LocalGL3 v) : centralGen v * x = x * centralGen v := by
  refine Units.ext ?_
  rw [Units.val_mul, Units.val_mul, coe_centralGen_eq_diagonal' v]
  have h : (![varpi v, varpi v, varpi v] : Fin 3 → v.adicCompletion ℚ) = fun _ => varpi v := by
    funext i; fin_cases i <;> rfl
  rw [h]
  ext i j
  simp [Matrix.diagonal_mul, Matrix.mul_diagonal, mul_comm]

variable {v}

private theorem dualWhittakerFn3_eq_comp_contragredient3 {W : LocalGL3 v → ℂ}
    (hW : IsRightInvariant (localMaximalCompact3 (𝓞 ℚ) ℚ v) W) :
    dualWhittakerFn3 W = fun g => W (contragredient3 g) := by
  funext g
  rw [dualWhittakerFn3_eq_apply_contragredient3_mul, hW _ _ (longWeyl3_mem_localMaximalCompact3 v)]

private theorem dualWhittakerFn3_apply_one {W : LocalGL3 v → ℂ}
    (hW : IsRightInvariant (localMaximalCompact3 (𝓞 ℚ) ℚ v) W) : dualWhittakerFn3 W 1 = W 1 := by
  rw [dualWhittakerFn3_eq_comp_contragredient3 hW]
  simp only [map_one]

private theorem cosetSum_dualWhittakerFn3 {W : LocalGL3 v → ℂ}
    (hW : IsRightInvariant (localMaximalCompact3 (𝓞 ℚ) ℚ v) W) {ι : Type} [Fintype ι] (reps : ι → LocalGL3 v)
    (g : LocalGL3 v) :
    cosetSum reps (dualWhittakerFn3 W) g = cosetSum (fun i => contragredient3 (reps i)) W (contragredient3 g) := by
  rw [dualWhittakerFn3_eq_comp_contragredient3 hW]
  simp only [cosetSum, map_mul]

private theorem cosetSum_contragredient3_eq {W : LocalGL3 v → ℂ} {e₃ lam : ℂ}
    (hc : ∀ g : LocalGL3 v, W (centralGen v * g) = e₃ * W g) (he₃ : e₃ ≠ 0) {gen gen' : LocalGL3 v}
    (hgen : contragredient3 gen = (centralGen v)⁻¹ * gen')
    (heig : IsCosetEigenfunction (localMaximalCompact3 (𝓞 ℚ) ℚ v) gen' W lam) {ι : Type} [Fintype ι]
    {reps : ι → LocalGL3 v} (hsys : HeckeIntegralSeam.IsHeckeCosetSystem (localMaximalCompact3 (𝓞 ℚ) ℚ v) gen reps)
    (x : LocalGL3 v) :
    cosetSum (fun i => contragredient3 (reps i)) W x = e₃⁻¹ * lam * W x := by
  have h₁ := isHeckeCosetSystem_mulEquiv contragredient3 (contragredient3_mem_localMaximalCompact3_iff v) hsys
  rw [hgen] at h₁
  have h₂ := isHeckeCosetSystem_central_mul (centralGen v) (centralGen_mul_eq_mul_centralGen v) h₁
  rw [mul_inv_cancel_left] at h₂
  have h₃ := heig ι _ h₂ x
  have h₄ : cosetSum (fun i => centralGen v * (contragredient3 ∘ reps) i) W x =
      e₃ * cosetSum (fun i => contragredient3 (reps i)) W x := by
    simp only [cosetSum, Function.comp_apply, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← mul_assoc, ← centralGen_mul_eq_mul_centralGen, mul_assoc, hc]
  rw [h₄] at h₃
  rw [mul_assoc, ← h₃, inv_mul_cancel_left₀ he₃]

private theorem isRightInvariant_and_isCosetEigenfunction_dualWhittakerFn3 (W : LocalGL3 v → ℂ) (e₁ e₂ e₃ : ℂ)
    (hW : IsRightInvariant (localMaximalCompact3 (𝓞 ℚ) ℚ v) W ∧
      IsCosetEigenfunction (localMaximalCompact3 (𝓞 ℚ) ℚ v) (heckeGen1 v) W (cNormQ v * e₁) ∧
      IsCosetEigenfunction (localMaximalCompact3 (𝓞 ℚ) ℚ v) (heckeGen2 v) W (cNormQ v * e₂) ∧
      ∀ g : LocalGL3 v, W (centralGen v * g) = e₃ * W g)
    (he₃ : e₃ ≠ 0) :
    IsRightInvariant (localMaximalCompact3 (𝓞 ℚ) ℚ v) (dualWhittakerFn3 W) ∧
      IsCosetEigenfunction (localMaximalCompact3 (𝓞 ℚ) ℚ v) (heckeGen1 v) (dualWhittakerFn3 W)
        (cNormQ v * (e₂ / e₃)) ∧
      IsCosetEigenfunction (localMaximalCompact3 (𝓞 ℚ) ℚ v) (heckeGen2 v) (dualWhittakerFn3 W)
        (cNormQ v * (e₁ / e₃)) ∧
      ∀ g : LocalGL3 v, dualWhittakerFn3 W (centralGen v * g) = e₃⁻¹ * dualWhittakerFn3 W g := by
  obtain ⟨hU, h1, h2, hc⟩ := hW
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro g u hu
    rw [dualWhittakerFn3_eq_comp_contragredient3 hU]
    simp only [map_mul]
    exact hU _ _ ((contragredient3_mem_localMaximalCompact3_iff v u).2 hu)
  · intro ι _ reps hsys g
    rw [cosetSum_dualWhittakerFn3 hU, dualWhittakerFn3_eq_comp_contragredient3 hU,
      cosetSum_contragredient3_eq hc he₃ (contragredient3_heckeGen1 v) h2 hsys]
    ring
  · intro ι _ reps hsys g
    rw [cosetSum_dualWhittakerFn3 hU, dualWhittakerFn3_eq_comp_contragredient3 hU,
      cosetSum_contragredient3_eq hc he₃ (contragredient3_heckeGen2 v) h1 hsys]
    ring
  · intro g
    rw [dualWhittakerFn3_eq_comp_contragredient3 hU]
    simp only [map_mul, contragredient3_centralGen]
    have h := hc ((centralGen v)⁻¹ * contragredient3 g)
    rw [mul_inv_cancel_left] at h
    rw [h, inv_mul_cancel_left₀ he₃]

private theorem coe_ratPrimeUnit_inv_pow (k : ℕ) :
    (((ratPrimeUnit v)⁻¹ ^ k : (v.adicCompletion ℚ)ˣ) : v.adicCompletion ℚ) = (ratPrimeAt v ^ k)⁻¹ := by
  rw [Units.val_pow_eq_pow_val, Units.val_inv_eq_inv_val, inv_pow]
  rfl

private theorem valued_ratPrimeAt_pow_inv (k : ℕ) :
    Valued.v ((ratPrimeAt v ^ k)⁻¹) = WithZero.exp (k : ℤ) := by
  rw [map_inv₀, Valuation.map_pow, valued_ratPrimeAt_eq_valued_varpi, AdelicLevel.valued_uniformizerUnit,
    ← WithZero.exp_nsmul, ← WithZero.exp_neg]
  congr 1
  simp

private theorem valued_coe_ratPrimeUnit_inv_pow (k : ℕ) :
    Valued.v ((((ratPrimeUnit v)⁻¹ ^ k : (v.adicCompletion ℚ)ˣ) : v.adicCompletion ℚ)) = WithZero.exp (k : ℤ) := by
  rw [coe_ratPrimeUnit_inv_pow, valued_ratPrimeAt_pow_inv]

private theorem cNormQ_ne_zero : cNormQ v ≠ 0 := by
  have h : Ideal.absNorm v.asIdeal ≠ 0 :=
    Ideal.absNorm_ne_zero_of_nonZeroDivisors ⟨v.asIdeal, mem_nonZeroDivisors_of_ne_zero v.ne_bot⟩
  unfold cNormQ
  exact_mod_cast h

private theorem twoRowCoeff_inv_triple (W : LocalGL3 v → ℂ) (e₁ e₂ e₃ : ℂ)
    (hW : IsRightInvariant (localMaximalCompact3 (𝓞 ℚ) ℚ v) W ∧
      IsCosetEigenfunction (localMaximalCompact3 (𝓞 ℚ) ℚ v) (heckeGen1 v) W (cNormQ v * e₁) ∧
      IsCosetEigenfunction (localMaximalCompact3 (𝓞 ℚ) ℚ v) (heckeGen2 v) W (cNormQ v * e₂) ∧
      ∀ g : LocalGL3 v, W (centralGen v * g) = e₃ * W g)
    (hψ : IsGL3PsiWhittakerFn (psiLocal ℚ v) W) (he₃ : e₃ ≠ 0) (hW1 : W 1 ≠ 0) (k₁ k₂ : ℕ) (hk : k₂ ≤ k₁) :
    twoRowCoeff (e₂ / e₃) (e₁ / e₃) e₃⁻¹ k₁ k₂ = e₃⁻¹ ^ k₁ * twoRowCoeff e₁ e₂ e₃ k₁ (k₁ - k₂) := by

  have hdual := isRightInvariant_and_isCosetEigenfunction_dualWhittakerFn3 W e₁ e₂ e₃ hW he₃
  have hψd : IsGL3PsiWhittakerFn (psiLocal ℚ v)⁻¹ (dualWhittakerFn3 W) :=
    isGL3PsiWhittakerFn_dualWhittakerFn3 (psiLocal ℚ v) W hψ
  have hA := apply_twoRowPointLocal_eq v (psiLocal ℚ v)⁻¹ (dualWhittakerFn3 W) (e₂ / e₃) (e₁ / e₃) e₃⁻¹ hdual hψd
    (psiLocal_rat_inv_facts v).1 (psiLocal_rat_inv_facts v).2.1 k₁ k₂ hk
  rw [dualWhittakerFn3_apply_one hW.1] at hA

  have hD := coe_contragredient3_eq_diagonal v (twoRowPointLocal v k₁ k₂) _
    (coe_twoRowPointLocal_eq_diagonal v k₁ k₂)
    (vec3_ne_zero_of v _ _ _ (pow_ne_zero _ (ratPrimeAt_ne_zero v)) (pow_ne_zero _ (ratPrimeAt_ne_zero v)) one_ne_zero)
  have hB := apply_eq_zpow_mul_of_coe_eq_diagonal_of_dominant v (psiLocal ℚ v) W e₁ e₂ e₃ hW hψ
    (psiLocal_rat_facts v).1 (psiLocal_rat_facts v).2.1 he₃ ![1, (ratPrimeUnit v)⁻¹ ^ k₂, (ratPrimeUnit v)⁻¹ ^ k₁]
    ![0, -(k₂ : ℤ), -(k₁ : ℤ)]
    (by
      intro i
      fin_cases i
      · show Valued.v (((1 : (v.adicCompletion ℚ)ˣ) : v.adicCompletion ℚ)) = WithZero.exp (-(0 : ℤ))
        simp
      · show Valued.v ((((ratPrimeUnit v)⁻¹ ^ k₂ : (v.adicCompletion ℚ)ˣ) : v.adicCompletion ℚ)) =
          WithZero.exp (-(-(k₂ : ℤ)))
        rw [neg_neg, valued_coe_ratPrimeUnit_inv_pow]
      · show Valued.v ((((ratPrimeUnit v)⁻¹ ^ k₁ : (v.adicCompletion ℚ)ˣ) : v.adicCompletion ℚ)) =
          WithZero.exp (-(-(k₁ : ℤ)))
        rw [neg_neg, valued_coe_ratPrimeUnit_inv_pow])
    (contragredient3 (twoRowPointLocal v k₁ k₂))
    (by
      rw [hD]
      congr 1
      funext i
      fin_cases i
      · show (1 : v.adicCompletion ℚ)⁻¹ = ((1 : (v.adicCompletion ℚ)ˣ) : v.adicCompletion ℚ)
        simp
      · show (ratPrimeAt v ^ k₂)⁻¹ = (((ratPrimeUnit v)⁻¹ ^ k₂ : (v.adicCompletion ℚ)ˣ) : v.adicCompletion ℚ)
        rw [coe_ratPrimeUnit_inv_pow]
      · show (ratPrimeAt v ^ k₁)⁻¹ = (((ratPrimeUnit v)⁻¹ ^ k₁ : (v.adicCompletion ℚ)ˣ) : v.adicCompletion ℚ)
        rw [coe_ratPrimeUnit_inv_pow])
    (by show -(k₂ : ℤ) ≤ 0; omega) (by show -(k₁ : ℤ) ≤ -(k₂ : ℤ); omega)
  have hB' : W (contragredient3 (twoRowPointLocal v k₁ k₂)) =
      e₃ ^ (-(k₁ : ℤ)) * (W 1 * ((cNormQ v)⁻¹ ^ ((0 : ℤ) - -(k₁ : ℤ)).toNat *
        twoRowCoeff e₁ e₂ e₃ ((0 : ℤ) - -(k₁ : ℤ)).toNat (-(k₂ : ℤ) - -(k₁ : ℤ)).toNat)) := hB
  have hn₁ : ((0 : ℤ) - -(k₁ : ℤ)).toNat = k₁ := by omega
  have hn₂ : (-(k₂ : ℤ) - -(k₁ : ℤ)).toNat = k₁ - k₂ := by omega
  rw [hn₁, hn₂, zpow_neg, zpow_natCast, ← inv_pow] at hB'

  have hAB : dualWhittakerFn3 W (twoRowPointLocal v k₁ k₂) = W (contragredient3 (twoRowPointLocal v k₁ k₂)) := by
    rw [dualWhittakerFn3_eq_comp_contragredient3 hW.1]
  rw [hAB, hB'] at hA
  have hWQ : W 1 * (cNormQ v)⁻¹ ^ k₁ ≠ 0 := mul_ne_zero hW1 (pow_ne_zero _ (inv_ne_zero cNormQ_ne_zero))
  apply mul_left_cancel₀ hWQ
  calc W 1 * (cNormQ v)⁻¹ ^ k₁ * twoRowCoeff (e₂ / e₃) (e₁ / e₃) e₃⁻¹ k₁ k₂
      = W 1 * ((cNormQ v)⁻¹ ^ k₁ * twoRowCoeff (e₂ / e₃) (e₁ / e₃) e₃⁻¹ k₁ k₂) := by ring
    _ = e₃⁻¹ ^ k₁ * (W 1 * ((cNormQ v)⁻¹ ^ k₁ * twoRowCoeff e₁ e₂ e₃ k₁ (k₁ - k₂))) := hA.symm
    _ = W 1 * (cNormQ v)⁻¹ ^ k₁ * (e₃⁻¹ ^ k₁ * twoRowCoeff e₁ e₂ e₃ k₁ (k₁ - k₂)) := by ring

end SphericalDual
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_laurent_localZeta_eq_gl3LFactorPoly_of_sphericalData.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_exists_laurent_localZeta_eq_gl3LFactorPoly_of_sphericalData.LanglandsTunnell.CubicInduction"
end
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_laurent_localZeta_eq_gl3LFactorPoly_of_sphericalData.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_exists_laurent_localZeta_eq_gl3LFactorPoly_of_sphericalData.LanglandsTunnell.CubicInduction"

section

set_option autoImplicit false

open IsDedekindDomain NumberField NumberField.AdelicLevel NumberField.StandardAddChar LanglandsTunnell.TateLocal MeasureTheory

open scoped Pointwise

noncomputable section

namespace LanglandsTunnell
p2m_export "LanglandsTunnell" "TateLocal.localBorel TateLocal.borelSpace_localBorel TateLocal.stdRootNumberAt TateLocal.higherUnitsAt TateLocal.mem_higherUnitsAt_iff TateLocal.HasConductorExponentAt TateLocal.modulus TateLocal.modulus_mul"
namespace CubicInduction
p2m_export "LanglandsTunnell.CubicInduction" "localZeta31 localZeta30 localZetaDual31 IsLocalZeta30ConvergentAbove IsLocalZeta31ConvergentAbove lowerUnipotent21 lowerUnipotent21_coe longWeyl3 longWeyl3_coe dualWhittakerFn3 dualWhittakerFn3_apply weylPrime3 weylPrime3_coe transposeInv3_weylPrime3 transposeInv3_lowerUnipotent21 IsGL3PsiWhittakerFn transposeInv3 upperUnipotent3 upperUnipotent3_coe upperUnipotent3_zero embedMat2 iotaGL coe_iotaGL localMaximalCompact3 mem_localMaximalCompact3_iff LocalGL3 varpi varpi_ne_zero heckeGen1 heckeGen2 centralGen cNormQ cosetSum IsCosetEigenfunction IsRightInvariant diagUnitGL2 coe_diagUnitGL2 diagHom diagHom_apply ratPrimeAt ratPrimeAt_ne_zero ratPrimeUnit sphericalTorusValue diagUnits2 coe_diagUnits2 twoRowPointLocal twoRowPointLocal_zero_right eq_zero_of_coe_eq_diagonal_of_valued_lt_of_isGL3PsiWhittakerFn eq_zero_of_isCosetEigenfunction_of_isGL3PsiWhittakerFn_of_apply_one_eq_zero exists_eq_upperUnipotent3_mul_diagonal_mul_mem_localMaximalCompact3 isGL3PsiWhittakerFn_dualWhittakerFn3 sphericalTorusValue_eq_of_isCosetEigenfunction_of_isGL3PsiWhittakerFn"
p2m_open "LanglandsTunnell.CubicInduction LanglandsTunnell"

section UnitShells

variable (v : HeightOneSpectrum (𝓞 ℚ))

private abbrev unitSet : Set (v.adicCompletion ℚ) := {u : v.adicCompletion ℚ | Valued.v u = 1}

private def unitShell (k : ℤ) : Set (v.adicCompletion ℚ)ˣ :=
  {α : (v.adicCompletion ℚ)ˣ | Valued.v (α : v.adicCompletion ℚ) = WithZero.exp (-k)}

private abbrev adicBall (m : ℤ) : Set (v.adicCompletion ℚ) := {x : v.adicCompletion ℚ | Valued.v x ≤ WithZero.exp m}

section Preliminaries

private theorem charExt_units_mul {F : Type*} [Field F] (χ : Fˣ →* ℂˣ) (u : Fˣ) (y : F) :
    charExt χ ((u : F) * y) = (χ u : ℂ) * charExt χ y := by
  by_cases hy : y = 0
  · simp [hy]
  · have hne : (u : F) * y ≠ 0 := mul_ne_zero u.ne_zero hy
    rw [charExt_of_ne_zero χ hne, charExt_of_ne_zero χ hy, ← Units.val_mul, ← map_mul]
    congr 2
    ext
    simp

private theorem preimage_mul_left_eq_smul {F : Type*} [Field F] (u : Fˣ) (s : Set F) :
    (fun x => (u : F) * x) ⁻¹' s = u⁻¹ • s := by
  ext x
  rw [Set.mem_preimage, Set.mem_smul_set_iff_inv_smul_mem, inv_inv, Units.smul_def, smul_eq_mul]

variable {F : Type*} [Field F] [TopologicalSpace F] [IsTopologicalRing F] [LocallyCompactSpace F]
  [MeasurableSpace F] [BorelSpace F]

private theorem map_mul_left_eq_smul (μ : Measure F) [μ.IsAddHaarMeasure] [μ.Regular] (u : Fˣ) :
    Measure.map (fun x => (u : F) * x) μ = ((modulus (u : F) : ENNReal)⁻¹) • μ := by
  ext s hs
  rw [Measure.map_apply (measurable_const_mul _) hs, preimage_mul_left_eq_smul, Measure.smul_apply, smul_eq_mul,
    ← distribHaarChar_mul μ u⁻¹ s, map_inv, modulus_coe_units, ENNReal.coe_inv distribHaarChar_pos.ne']

private theorem map_mul_left_of_modulus_eq_one (μ : Measure F) [μ.IsAddHaarMeasure] [μ.Regular] {u : Fˣ}
    (hu : modulus (u : F) = 1) : Measure.map (fun x => (u : F) * x) μ = μ := by
  rw [map_mul_left_eq_smul μ u, hu, ENNReal.coe_one, inv_one, one_smul]

private theorem integral_comp_mul_left_of_modulus_eq_one (μ : Measure F) [μ.IsAddHaarMeasure] [μ.Regular] {u : Fˣ}
    (hu : modulus (u : F) = 1) (Φ : F → ℂ) : ∫ y, Φ y ∂μ = ∫ y, Φ ((u : F) * y) ∂μ := by
  calc ∫ y, Φ y ∂μ = ∫ y, Φ y ∂(Measure.map (fun x => (u : F) * x) μ) := by
        rw [map_mul_left_of_modulus_eq_one μ hu]
    _ = ∫ y, Φ ((u : F) * y) ∂μ := by
        rw [← MeasurableEquiv.coe_mulLeft₀ u.ne_zero, integral_map_equiv]; rfl

private theorem setIntegral_comp_mul_left_of_modulus_eq_one (μ : Measure F) [μ.IsAddHaarMeasure] [μ.Regular]
    {u : Fˣ} (hu : modulus (u : F) = 1) (Φ : F → ℂ) {S : Set F} (hS : MeasurableSet S)
    (hstable : ∀ y, (u : F) * y ∈ S ↔ y ∈ S) : ∫ y in S, Φ y ∂μ = ∫ y in S, Φ ((u : F) * y) ∂μ := by
  have hpre : (fun y => (u : F) * y) ⁻¹' S = S := Set.ext fun y => hstable y
  rw [← integral_indicator hS, integral_comp_mul_left_of_modulus_eq_one μ hu (S.indicator Φ), ← integral_indicator hS]
  congr 1
  funext y
  by_cases hy : y ∈ S
  · rw [Set.indicator_of_mem ((hstable y).mpr hy), Set.indicator_of_mem hy]
  · rw [Set.indicator_of_notMem (fun h => hy ((hstable y).mp h)), Set.indicator_of_notMem hy]

private theorem setIntegral_mul_charExt_eq_zero (μ : Measure F) [μ.IsAddHaarMeasure] [μ.Regular] {S : Set F}
    (hSm : MeasurableSet S) (g : F → ℂ) (χ : Fˣ →* ℂˣ) {u₁ : Fˣ} (hu₁ : modulus (u₁ : F) = 1) (hχ : χ u₁ ≠ 1)
    (hS : ∀ y, (u₁ : F) * y ∈ S ↔ y ∈ S) (hg : ∀ y ∈ S, g ((u₁ : F) * y) = g y) :
    ∫ y in S, g y * charExt χ y ∂μ = 0 := by
  have hI : ∫ y in S, g y * charExt χ y ∂μ = (χ u₁ : ℂ) * ∫ y in S, g y * charExt χ y ∂μ := by
    calc ∫ y in S, g y * charExt χ y ∂μ = ∫ y in S, g ((u₁ : F) * y) * charExt χ ((u₁ : F) * y) ∂μ :=
          setIntegral_comp_mul_left_of_modulus_eq_one μ hu₁ _ hSm hS
      _ = ∫ y in S, (χ u₁ : ℂ) * (g y * charExt χ y) ∂μ := by
          refine setIntegral_congr_fun hSm fun y hy => ?_
          rw [hg y hy, charExt_units_mul]
          ring
      _ = (χ u₁ : ℂ) * ∫ y in S, g y * charExt χ y ∂μ := integral_const_mul _ _
  have h1 : (1 - (χ u₁ : ℂ)) * ∫ y in S, g y * charExt χ y ∂μ = 0 := by
    rw [sub_mul, one_mul, sub_eq_zero]
    exact hI
  have hne : (χ u₁ : ℂ) ≠ 1 := fun h => hχ (Units.val_eq_one.mp h)
  rcases mul_eq_zero.mp h1 with h | h
  · exact absurd (sub_eq_zero.mp h).symm hne
  · exact h

omit [LocallyCompactSpace F] in

private theorem setIntegral_addChar_mul_eq_zero (μ : Measure F) [μ.IsAddHaarMeasure] {S : Set F}
    (hSm : MeasurableSet S) (ψ : AddChar F ℂ) (c : F) (h : F → ℂ) {z : F} (hz : ψ (c * z) ≠ 1)
    (hS : ∀ y, y + z ∈ S ↔ y ∈ S) (hh : ∀ y ∈ S, h (y + z) = h y) : ∫ y in S, ψ (c * y) * h y ∂μ = 0 := by
  set Φ : F → ℂ := S.indicator fun y => ψ (c * y) * h y with hΦdef
  have hΦ : ∀ y, Φ (y + z) = ψ (c * z) * Φ y := by
    intro y
    by_cases hy : y ∈ S
    · rw [hΦdef, Set.indicator_of_mem ((hS y).mpr hy), Set.indicator_of_mem hy, hh y hy, mul_add,
        AddChar.map_add_eq_mul]
      ring
    · rw [hΦdef, Set.indicator_of_notMem (fun hm => hy ((hS y).mp hm)), Set.indicator_of_notMem hy, mul_zero]
  have hI : ∫ y, Φ y ∂μ = ψ (c * z) * ∫ y, Φ y ∂μ := by
    calc ∫ y, Φ y ∂μ = ∫ y, Φ (y + z) ∂μ := (integral_add_right_eq_self Φ z).symm
      _ = ∫ y, ψ (c * z) * Φ y ∂μ := by simp_rw [hΦ]
      _ = ψ (c * z) * ∫ y, Φ y ∂μ := integral_const_mul _ _
  have h1 : (1 - ψ (c * z)) * ∫ y, Φ y ∂μ = 0 := by
    rw [sub_mul, one_mul, sub_eq_zero]
    exact hI
  rcases mul_eq_zero.mp h1 with h0 | h0
  · exact absurd (sub_eq_zero.mp h0).symm hz
  · rwa [hΦdef, integral_indicator hSm] at h0

end Preliminaries
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_laurent_localZeta_eq_gl3LFactorPoly_of_sphericalData.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_exists_laurent_localZeta_eq_gl3LFactorPoly_of_sphericalData.LanglandsTunnell.CubicInduction"

section RationalPlace

private theorem _root_.LanglandsTunnell.CubicInduction.one_lt_absNorm : 1 < Ideal.absNorm v.asIdeal := by
  have h0 : Ideal.absNorm v.asIdeal ≠ 0 := Ideal.absNorm_eq_zero_iff.not.mpr v.ne_bot
  have h1 : Ideal.absNorm v.asIdeal ≠ 1 := by
    rw [Ne, Ideal.absNorm_eq_one_iff]
    exact v.isPrime.ne_top
  omega

p2m_export "LanglandsTunnell.CubicInduction" "one_lt_absNorm"
private theorem absNorm_pos : (0 : ℝ) < (Ideal.absNorm v.asIdeal : ℝ) := by
  exact_mod_cast Nat.zero_lt_one.trans (one_lt_absNorm v)

private theorem valued_uniformizerUnit_zpow (m : ℤ) :
    Valued.v ((uniformizerUnit ℚ v ^ m : (v.adicCompletion ℚ)ˣ) : v.adicCompletion ℚ) = WithZero.exp (-m) := by
  rw [Units.val_zpow_eq_zpow_val, map_zpow₀, valued_uniformizerUnit, ← WithZero.exp_zsmul]
  congr 1
  simp

private theorem norm_eq_zpow_of_valued {x : v.adicCompletion ℚ} {m : ℤ} (hx : Valued.v x = WithZero.exp m) :
    ‖x‖ = (Ideal.absNorm v.asIdeal : ℝ) ^ m := by
  rw [NumberField.FinitePlace.norm_def, hx,
    show (WithZero.exp m) = ((Multiplicative.ofAdd m : Multiplicative ℤ) : WithZero (Multiplicative ℤ)) from rfl,
    WithZeroMulInt.toNNReal_neg_apply _ WithZero.coe_ne_zero, WithZero.unzero_coe, toAdd_ofAdd, NNReal.coe_zpow,
    NNReal.coe_natCast]

private theorem modulus_eq_zpow_of_valued {x : v.adicCompletion ℚ} {m : ℤ} (hx : Valued.v x = WithZero.exp m) :
    modulus x = (Ideal.absNorm v.asIdeal : NNReal) ^ m := by
  rw [modulus_adicCompletion_eq_nnnorm ℚ v x, ← NNReal.coe_inj, coe_nnnorm, norm_eq_zpow_of_valued v hx,
    NNReal.coe_zpow, NNReal.coe_natCast]

private theorem modulus_eq_one_of_valued {u : v.adicCompletion ℚ} (hu : Valued.v u = 1) : modulus u = 1 := by
  rw [modulus_eq_zpow_of_valued v (m := 0) (by rw [hu, WithZero.exp_zero]), zpow_zero]

private theorem isClosed_adicBall (k : ℤ) : IsClosed (adicBall v k) := by
  have h := isClosed_setOf_valued_le v _ (Units.ne_zero (uniformizerUnit ℚ v ^ (-k)))
  rw [valued_uniformizerUnit_zpow, neg_neg] at h
  exact h

private theorem isOpen_adicBall (k : ℤ) : IsOpen (adicBall v k) := by
  have h := isOpen_setOf_valued_le v _ (Units.ne_zero (uniformizerUnit ℚ v ^ (-k)))
  rw [valued_uniformizerUnit_zpow, neg_neg] at h
  exact h

private theorem coe_integers_eq : (v.adicCompletionIntegers ℚ : Set (v.adicCompletion ℚ)) = adicBall v 0 := by
  ext x
  show _ ↔ Valued.v x ≤ WithZero.exp 0
  rw [WithZero.exp_zero]
  exact HeightOneSpectrum.mem_adicCompletionIntegers (𝓞 ℚ) ℚ v

private theorem isCompact_adicBall_zero : IsCompact (adicBall v 0) := by
  rw [← coe_integers_eq]
  exact isCompact_iff_compactSpace.mpr (show CompactSpace (v.adicCompletionIntegers ℚ) from inferInstance)

private theorem adicBall_subset {k m : ℤ} (hkm : k ≤ m) : adicBall v k ⊆ adicBall v m := fun x hx =>
  le_trans (show Valued.v x ≤ WithZero.exp k from hx) (WithZero.exp_le_exp.mpr hkm)

private theorem unitSet_eq_diff : unitSet v = adicBall v 0 \ adicBall v (-1) := by
  ext y
  simp only [unitSet, adicBall, Set.mem_setOf_eq, Set.mem_diff]
  constructor
  · intro hy
    refine ⟨by rw [hy, WithZero.exp_zero], fun h => ?_⟩
    rw [hy, ← WithZero.exp_zero, WithZero.exp_le_exp] at h
    omega
  · rintro ⟨h1, h2⟩
    have hne : Valued.v y ≠ 0 := fun h0 => h2 (by rw [h0]; exact zero_le')
    obtain ⟨m, hm⟩ : ∃ m : ℤ, Valued.v y = WithZero.exp m := ⟨_, (WithZero.exp_log hne).symm⟩
    rw [hm, WithZero.exp_le_exp] at h1 h2
    rw [hm, ← WithZero.exp_zero]
    congr 1
    omega

private theorem isClosed_unitSet : IsClosed (unitSet v) := by
  rw [unitSet_eq_diff]
  exact (isClosed_adicBall v 0).sdiff (isOpen_adicBall v (-1))

private theorem unitSet_subset_adicBall_zero : unitSet v ⊆ adicBall v 0 := by
  rw [unitSet_eq_diff]
  exact Set.diff_subset

private theorem isCompact_unitSet : IsCompact (unitSet v) :=
  (isCompact_adicBall_zero v).of_isClosed_subset (isClosed_unitSet v) (unitSet_subset_adicBall_zero v)

private theorem measurableSet_unitSet :
    letI := localBorel ℚ v
    MeasurableSet (unitSet v) := by
  letI := localBorel ℚ v
  haveI : BorelSpace (v.adicCompletion ℚ) := borelSpace_localBorel ℚ v
  exact (isClosed_unitSet v).measurableSet

private theorem measurableSet_adicBall (k : ℤ) :
    letI := localBorel ℚ v
    MeasurableSet (adicBall v k) := by
  letI := localBorel ℚ v
  haveI : BorelSpace (v.adicCompletion ℚ) := borelSpace_localBorel ℚ v
  exact (isClosed_adicBall v k).measurableSet

private theorem mul_mem_unitSet_iff {c : v.adicCompletion ℚ} (hc : Valued.v c = 1) (y : v.adicCompletion ℚ) :
    c * y ∈ unitSet v ↔ y ∈ unitSet v := by
  simp only [unitSet, Set.mem_setOf_eq, map_mul, hc, one_mul]

private theorem add_mem_unitSet_iff {z : v.adicCompletion ℚ} (hz : Valued.v z < 1) (y : v.adicCompletion ℚ) :
    y + z ∈ unitSet v ↔ y ∈ unitSet v := by
  simp only [unitSet, Set.mem_setOf_eq]
  constructor
  · intro h
    have hyz : Valued.v (y + z - z) = Valued.v (y + z) := Valuation.map_sub_eq_of_lt_left _ (by rw [h]; exact hz)
    rwa [add_sub_cancel_right, h] at hyz
  · intro h
    rw [Valuation.map_add_eq_of_lt_left _ (by rw [h]; exact hz)]
    exact h

private theorem regular_selfDualHaarAt :
    letI := localBorel ℚ v
    (selfDualHaarAt ℚ v).Regular := by
  letI := localBorel ℚ v
  haveI : BorelSpace (v.adicCompletion ℚ) := borelSpace_localBorel ℚ v
  show (((Ideal.absNorm v.asIdeal : NNReal) ^ (-(addCharLevel (psiLocal ℚ v) : ℝ) / 2) : NNReal) •
    Measure.addHaarMeasure (integersPositiveCompacts ℚ v)).Regular
  infer_instance

private theorem charExt_add_eq {χ : (v.adicCompletion ℚ)ˣ →* ℂˣ} {a : ℕ} (ha : 1 ≤ a)
    (hχ : ∀ u ∈ higherUnitsAt ℚ v a, χ u = 1) {y : v.adicCompletion ℚ} (hy : y ∈ unitSet v) {z : v.adicCompletion ℚ}
    (hz : Valued.v z ≤ WithZero.exp (-(a : ℤ))) : charExt χ (y + z) = charExt χ y := by
  have hy1 : Valued.v y = 1 := hy
  have hz1 : Valued.v z < 1 := lt_of_le_of_lt hz (by
    rw [← WithZero.exp_zero, WithZero.exp_lt_exp]
    omega)
  have hyz : y + z ∈ unitSet v := (add_mem_unitSet_iff v hz1 y).mpr hy
  have hyz1 : Valued.v (y + z) = 1 := hyz
  have hy0 : y ≠ 0 := (Valuation.ne_zero_iff _).mp (by rw [hy1]; exact one_ne_zero)
  have hyz0 : y + z ≠ 0 := (Valuation.ne_zero_iff _).mp (by rw [hyz1]; exact one_ne_zero)
  set u : (v.adicCompletion ℚ)ˣ := Units.mk0 (y + z) hyz0 * (Units.mk0 y hy0)⁻¹ with hu
  have huval : (u : v.adicCompletion ℚ) = (y + z) * y⁻¹ := by simp [hu]
  have humem : u ∈ higherUnitsAt ℚ v a := by
    refine (mem_higherUnitsAt_iff ℚ v).mpr ⟨?_, Or.inr ?_⟩
    · rw [huval, map_mul, map_inv₀, hyz1, hy1, inv_one, mul_one]
    · have hsub : (u : v.adicCompletion ℚ) - 1 = z * y⁻¹ := by
        rw [huval, add_mul, mul_inv_cancel₀ hy0, add_sub_cancel_left]
      rw [hsub, map_mul, map_inv₀, hy1, inv_one, mul_one]
      exact hz
  have hmk : Units.mk0 (y + z) hyz0 = u * Units.mk0 y hy0 := by rw [hu, inv_mul_cancel_right]
  rw [charExt_of_ne_zero χ hyz0, charExt_of_ne_zero χ hy0, hmk, map_mul, hχ u humem, one_mul]

end RationalPlace
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_laurent_localZeta_eq_gl3LFactorPoly_of_sphericalData.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_exists_laurent_localZeta_eq_gl3LFactorPoly_of_sphericalData.LanglandsTunnell.CubicInduction"

private theorem isAddHaarMeasure_selfDualHaarAt_rat :
    letI := localBorel ℚ v
    (selfDualHaarAt ℚ v).IsAddHaarMeasure := by
  letI := localBorel ℚ v
  haveI : BorelSpace (v.adicCompletion ℚ) := borelSpace_localBorel ℚ v
  set c : NNReal := (Ideal.absNorm v.asIdeal : NNReal) ^ (-(addCharLevel (psiLocal ℚ v) : ℝ) / 2) with hc
  have hc0 : c ≠ 0 := by
    rw [hc]
    exact (NNReal.rpow_pos (by exact_mod_cast Nat.zero_lt_one.trans (one_lt_absNorm v))).ne'
  have hdef : selfDualHaarAt ℚ v = (c : ENNReal) • Measure.addHaarMeasure (integersPositiveCompacts ℚ v) := rfl
  rw [hdef]
  exact Measure.IsAddHaarMeasure.smul _ (by exact_mod_cast hc0) ENNReal.coe_ne_top

private theorem real_adicBall (m : ℤ) :
    letI := localBorel ℚ v
    (selfDualHaarAt ℚ v).real (adicBall v m) =
      (Ideal.absNorm v.asIdeal : ℝ) ^ m *
        (selfDualHaarAt ℚ v).real (v.adicCompletionIntegers ℚ : Set (v.adicCompletion ℚ)) := by
  letI := localBorel ℚ v
  haveI : BorelSpace (v.adicCompletion ℚ) := borelSpace_localBorel ℚ v
  haveI : (selfDualHaarAt ℚ v).IsAddHaarMeasure := isAddHaarMeasure_selfDualHaarAt_rat v
  exact measureReal_setOf_valued_le_exp ℚ v (selfDualHaarAt ℚ v) m

section RationalPlaceMore

private theorem continuous_addChar_of_level {ψ : AddChar (v.adicCompletion ℚ) ℂ}
    (hψ0 : ∀ x : v.adicCompletion ℚ, Valued.v x ≤ 1 → ψ x = 1) : Continuous ψ := by
  refine continuous_iff_continuousAt.mpr fun x => ?_
  have hmem : (fun y => y - x) ⁻¹' adicBall v 0 ∈ nhds x := by
    refine ((isOpen_adicBall v 0).preimage (continuous_id.sub continuous_const)).mem_nhds ?_
    show Valued.v (x - x) ≤ WithZero.exp 0
    rw [sub_self, map_zero]
    exact zero_le'
  have hev : (fun _ => ψ x) =ᶠ[nhds x] (ψ : v.adicCompletion ℚ → ℂ) := by
    refine Filter.mem_of_superset hmem fun y hy => ?_
    show ψ x = ψ y
    have hy' : Valued.v (y - x) ≤ 1 := by
      have := (show Valued.v (y - x) ≤ WithZero.exp 0 from hy)
      rwa [WithZero.exp_zero] at this
    rw [show ψ y = ψ (x + (y - x)) by rw [add_sub_cancel], AddChar.map_add_eq_mul, hψ0 _ hy', mul_one]
  exact continuousAt_const.congr hev

private theorem real_integers_pos :
    letI := localBorel ℚ v
    0 < (selfDualHaarAt ℚ v).real (v.adicCompletionIntegers ℚ : Set (v.adicCompletion ℚ)) := by
  letI := localBorel ℚ v
  haveI : BorelSpace (v.adicCompletion ℚ) := borelSpace_localBorel ℚ v
  haveI : (selfDualHaarAt ℚ v).IsAddHaarMeasure := isAddHaarMeasure_selfDualHaarAt_rat v
  rw [coe_integers_eq]
  have h1 : 0 < selfDualHaarAt ℚ v (adicBall v 0) :=
    (isOpen_adicBall v 0).measure_pos (selfDualHaarAt ℚ v) ⟨0, by simp [adicBall]⟩
  exact ENNReal.toReal_pos h1.ne' (isCompact_adicBall_zero v).measure_lt_top.ne

private theorem not_hasConductorExponentAt_zero_of_one_le {χ : (v.adicCompletion ℚ)ˣ →* ℂˣ} {a : ℕ} (ha : 1 ≤ a)
    (hχ : HasConductorExponentAt ℚ v χ a) : ¬ HasConductorExponentAt ℚ v χ 0 := fun h0 => by
  have h := hasConductorExponentAt_unique ℚ v hχ h0
  omega

private theorem norm_inv_mul_natCast_cpow_lt_one (χ : (v.adicCompletion ℚ)ˣ →* ℂˣ)
    (hu : ‖((χ (uniformizerUnit ℚ v) : ℂˣ) : ℂ)‖ = 1) :
    ‖(χ⁻¹ (uniformizerUnit ℚ v) : ℂ) * (Ideal.absNorm v.asIdeal : ℂ) ^ (-(1 - (1 / 2 : ℂ)))‖ < 1 := by
  have hp : 0 < Ideal.absNorm v.asIdeal := Nat.zero_lt_one.trans (one_lt_absNorm v)
  rw [norm_mul, MonoidHom.inv_apply, Units.val_inv_eq_inv_val, norm_inv, hu, inv_one, one_mul,
    show (-(1 - (1 / 2 : ℂ))) = ((-(1 / 2 : ℝ) : ℝ) : ℂ) by norm_num, Complex.norm_natCast_cpow_of_pos hp,
    Complex.ofReal_re]
  exact Real.rpow_lt_one_of_one_lt_of_neg (by exact_mod_cast one_lt_absNorm v) (by norm_num)

end RationalPlaceMore
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_laurent_localZeta_eq_gl3LFactorPoly_of_sphericalData.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_exists_laurent_localZeta_eq_gl3LFactorPoly_of_sphericalData.LanglandsTunnell.CubicInduction"

section Shells

private theorem setOf_valued_eq_exp_eq_diff (e : ℤ) :
    {x : v.adicCompletion ℚ | Valued.v x = WithZero.exp e} = adicBall v e \ adicBall v (e - 1) := by
  ext y
  simp only [adicBall, Set.mem_setOf_eq, Set.mem_diff]
  constructor
  · intro hy
    refine ⟨hy.le, fun h => ?_⟩
    rw [hy, WithZero.exp_le_exp] at h
    omega
  · rintro ⟨h1, h2⟩
    have hne : Valued.v y ≠ 0 := fun h0 => h2 (by rw [h0]; exact zero_le')
    obtain ⟨m, hm⟩ : ∃ m : ℤ, Valued.v y = WithZero.exp m := ⟨_, (WithZero.exp_log hne).symm⟩
    rw [hm, WithZero.exp_le_exp] at h1 h2
    rw [hm]
    congr 1
    omega

private theorem measurableSet_setOf_valued_eq_exp (e : ℤ) :
    letI := localBorel ℚ v
    MeasurableSet {x : v.adicCompletion ℚ | Valued.v x = WithZero.exp e} := by
  letI := localBorel ℚ v
  haveI : BorelSpace (v.adicCompletion ℚ) := borelSpace_localBorel ℚ v
  rw [setOf_valued_eq_exp_eq_diff]
  exact (isClosed_adicBall v e).measurableSet.diff (isClosed_adicBall v (e - 1)).measurableSet

private theorem unitShell_eq_preimage (k : ℤ) :
    unitShell v k = Units.val ⁻¹' {x : v.adicCompletion ℚ | Valued.v x = WithZero.exp (-k)} := rfl

private theorem range_val : Set.range (Units.val : (v.adicCompletion ℚ)ˣ → v.adicCompletion ℚ) = {0}ᶜ := by
  ext x
  constructor
  · rintro ⟨u, rfl⟩
    exact u.ne_zero
  · intro hx
    exact ⟨Units.mk0 x hx, rfl⟩

private theorem measurableEmbedding_val :
    letI := localBorel ℚ v
    MeasurableEmbedding (Units.val : (v.adicCompletion ℚ)ˣ → v.adicCompletion ℚ) := by
  letI := localBorel ℚ v
  haveI : BorelSpace (v.adicCompletion ℚ) := borelSpace_localBorel ℚ v
  refine ⟨Units.val_injective, comap_measurable _, fun s hs => ?_⟩
  obtain ⟨t, ht, rfl⟩ := MeasurableSpace.measurableSet_comap.mp hs
  rw [Set.image_preimage_eq_inter_range, range_val]
  exact ht.inter (isClosed_singleton.measurableSet.compl)

private theorem image_val_unitShell (k : ℤ) :
    Units.val '' unitShell v k = {x : v.adicCompletion ℚ | Valued.v x = WithZero.exp (-k)} := by
  rw [unitShell_eq_preimage, Set.image_preimage_eq_inter_range, range_val]
  refine Set.inter_eq_left.mpr fun x hx => ?_
  have hx' : Valued.v x = WithZero.exp (-k) := hx
  exact (Valuation.ne_zero_iff _).mp (by rw [hx']; exact WithZero.exp_ne_zero)

private theorem image_val_unitShell_zero : Units.val '' unitShell v 0 = unitSet v := by
  rw [image_val_unitShell, neg_zero, WithZero.exp_zero]

open scoped Classical in

private noncomputable def extUnits (F : (v.adicCompletion ℚ)ˣ → ℂ) (x : v.adicCompletion ℚ) : ℂ :=
  if h : x = 0 then 0 else F (Units.mk0 x h)

private theorem extUnits_coe (F : (v.adicCompletion ℚ)ˣ → ℂ) (α : (v.adicCompletion ℚ)ˣ) :
    extUnits v F (α : v.adicCompletion ℚ) = F α := by
  rw [extUnits, dif_neg α.ne_zero, Units.mk0_val]

private theorem extUnits_comp_coe (F : (v.adicCompletion ℚ)ˣ → ℂ) :
    (fun α : (v.adicCompletion ℚ)ˣ => extUnits v F (α : v.adicCompletion ℚ)) = F :=
  funext (extUnits_coe v F)

private theorem extUnits_mul_left (F : (v.adicCompletion ℚ)ˣ → ℂ) (c : (v.adicCompletion ℚ)ˣ)
    (x : v.adicCompletion ℚ) :
    extUnits v (fun β => F (c * β)) x = extUnits v F ((c : v.adicCompletion ℚ) * x) := by
  by_cases hx : x = 0
  · simp [extUnits, hx]
  · have hcx : (c : v.adicCompletion ℚ) * x ≠ 0 := mul_ne_zero c.ne_zero hx
    rw [extUnits, extUnits, dif_neg hx, dif_neg hcx]
    congr 1
    ext
    simp

private theorem extUnits_mul_left_fun (F : (v.adicCompletion ℚ)ˣ → ℂ) (c : (v.adicCompletion ℚ)ˣ) :
    extUnits v (fun β => F (c * β)) = fun x => extUnits v F ((c : v.adicCompletion ℚ) * x) :=
  funext (extUnits_mul_left v F c)

private theorem map_val_restrict (S : Set (v.adicCompletion ℚ)ˣ) :
    letI := localBorel ℚ v
    Measure.map Units.val ((Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ v))).restrict S) =
      (mulMeasure (selfDualHaarAt ℚ v)).restrict (Units.val '' S) := by
  letI := localBorel ℚ v
  have hf := measurableEmbedding_val v
  conv_lhs => rw [← Units.val_injective.preimage_image S]
  rw [← hf.restrict_map, hf.map_comap, Measure.restrict_restrict' hf.measurableSet_range,
    Set.inter_eq_left.mpr (Set.image_subset_range _ _)]

private theorem setIntegral_units_eq (F : (v.adicCompletion ℚ)ˣ → ℂ) (S : Set (v.adicCompletion ℚ)ˣ) :
    letI := localBorel ℚ v
    ∫ α in S, F α ∂(Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ v))) =
      ∫ x in Units.val '' S, extUnits v F x ∂(mulMeasure (selfDualHaarAt ℚ v)) := by
  letI := localBorel ℚ v
  rw [← map_val_restrict, (measurableEmbedding_val v).integral_map, extUnits_comp_coe]

private theorem integrableOn_units_iff (F : (v.adicCompletion ℚ)ˣ → ℂ) (S : Set (v.adicCompletion ℚ)ˣ) :
    letI := localBorel ℚ v
    IntegrableOn F S (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ v))) ↔
      IntegrableOn (extUnits v F) (Units.val '' S) (mulMeasure (selfDualHaarAt ℚ v)) := by
  letI := localBorel ℚ v
  rw [IntegrableOn, IntegrableOn, ← map_val_restrict, (measurableEmbedding_val v).integrable_map_iff,
    show extUnits v F ∘ Units.val = F from funext (extUnits_coe v F)]

private theorem mulMeasure_restrict_unitSet :
    letI := localBorel ℚ v
    (mulMeasure (selfDualHaarAt ℚ v)).restrict (unitSet v) = (selfDualHaarAt ℚ v).restrict (unitSet v) := by
  letI := localBorel ℚ v
  have hU := measurableSet_unitSet v
  have hsub : unitSet v ∩ {0}ᶜ = unitSet v :=
    Set.inter_eq_left.mpr fun u hu =>
      (Valuation.ne_zero_iff _).mp (by rw [show Valued.v u = 1 from hu]; exact one_ne_zero)
  rw [mulMeasure, restrict_withDensity hU, Measure.restrict_restrict hU, hsub]
  have hone : (fun x : v.adicCompletion ℚ => ((modulus x : ENNReal))⁻¹)
      =ᵐ[(selfDualHaarAt ℚ v).restrict (unitSet v)] 1 := by
    refine ae_restrict_of_forall_mem hU fun u hu => ?_
    simp only [Pi.one_apply]
    rw [modulus_eq_one_of_valued v hu, ENNReal.coe_one, inv_one]
  rw [withDensity_congr_ae hone, withDensity_one]

private theorem measurable_density :
    letI := localBorel ℚ v
    Measurable fun x : v.adicCompletion ℚ => ((modulus x : ENNReal))⁻¹ := by
  letI := localBorel ℚ v
  haveI : BorelSpace (v.adicCompletion ℚ) := borelSpace_localBorel ℚ v
  have hmod : (modulus : v.adicCompletion ℚ → NNReal) = fun x => ‖x‖₊ :=
    funext fun x => modulus_adicCompletion_eq_nnnorm ℚ v x
  rw [hmod]
  exact measurable_nnnorm.coe_nnreal_ennreal.inv

private theorem map_mul_left_mulMeasure (c : (v.adicCompletion ℚ)ˣ) :
    letI := localBorel ℚ v
    Measure.map (fun x => (c : v.adicCompletion ℚ) * x) (mulMeasure (selfDualHaarAt ℚ v)) =
      mulMeasure (selfDualHaarAt ℚ v) := by
  letI := localBorel ℚ v
  haveI : BorelSpace (v.adicCompletion ℚ) := borelSpace_localBorel ℚ v
  haveI : (selfDualHaarAt ℚ v).IsAddHaarMeasure := isAddHaarMeasure_selfDualHaarAt_rat v
  haveI : (selfDualHaarAt ℚ v).Regular := regular_selfDualHaarAt v
  set ρ : v.adicCompletion ℚ → ENNReal := fun x => ((modulus x : ENNReal))⁻¹ with hρ
  have hρm : Measurable ρ := measurable_density v
  have hmc : Measurable fun x : v.adicCompletion ℚ => (c : v.adicCompletion ℚ) * x := measurable_const_mul _
  have h0c : MeasurableSet ({0}ᶜ : Set (v.adicCompletion ℚ)) := isClosed_singleton.measurableSet.compl
  have hpre : (fun x : v.adicCompletion ℚ => (c : v.adicCompletion ℚ) * x) ⁻¹' {0}ᶜ = {0}ᶜ := by
    ext x
    simp [c.ne_zero]
  have hmod0 : (modulus (c : v.adicCompletion ℚ) : ENNReal) ≠ 0 := by
    exact_mod_cast modulus_ne_zero c.ne_zero
  have hmodtop : (modulus (c : v.adicCompletion ℚ) : ENNReal) ≠ ⊤ := ENNReal.coe_ne_top

  have hmap : Measure.map (fun x => (c : v.adicCompletion ℚ) * x) ((selfDualHaarAt ℚ v).restrict {0}ᶜ) =
      ((modulus (c : v.adicCompletion ℚ) : ENNReal))⁻¹ • (selfDualHaarAt ℚ v).restrict {0}ᶜ := by
    rw [← hpre, ← Measure.restrict_map hmc h0c, map_mul_left_eq_smul (selfDualHaarAt ℚ v) c, Measure.restrict_smul,
      hpre]

  have hρc : ∀ x, ρ ((c : v.adicCompletion ℚ) * x) = ((modulus (c : v.adicCompletion ℚ) : ENNReal))⁻¹ * ρ x := by
    intro x
    simp only [hρ]
    rw [modulus_mul, ENNReal.coe_mul, ENNReal.mul_inv (Or.inl hmod0) (Or.inl hmodtop)]
  have hinv0 : ((modulus (c : v.adicCompletion ℚ) : ENNReal))⁻¹ ≠ 0 := ENNReal.inv_ne_zero.mpr hmodtop
  have hinvtop : ((modulus (c : v.adicCompletion ℚ) : ENNReal))⁻¹ ≠ ⊤ := ENNReal.inv_ne_top.mpr hmod0
  ext T hT
  rw [Measure.map_apply hmc hT, mulMeasure, withDensity_apply _ (hmc hT), withDensity_apply _ hT]

  have hsub : ((modulus (c : v.adicCompletion ℚ) : ENNReal))⁻¹ * ∫⁻ x in T, ρ x ∂((selfDualHaarAt ℚ v).restrict {0}ᶜ) =
      ∫⁻ x in (fun x => (c : v.adicCompletion ℚ) * x) ⁻¹' T, ρ ((c : v.adicCompletion ℚ) * x)
        ∂((selfDualHaarAt ℚ v).restrict {0}ᶜ) := by
    rw [← setLIntegral_map hT hρm hmc, hmap, Measure.restrict_smul, lintegral_smul_measure, smul_eq_mul]
  simp_rw [hρc] at hsub
  rw [lintegral_const_mul _ hρm] at hsub
  exact ((ENNReal.mul_right_inj hinv0 hinvtop).mp hsub).symm

private theorem setIntegral_mulMeasure_comp_mul_left (G : v.adicCompletion ℚ → ℂ) (c : (v.adicCompletion ℚ)ˣ)
    (T : Set (v.adicCompletion ℚ)) :
    letI := localBorel ℚ v
    ∫ x in T, G x ∂(mulMeasure (selfDualHaarAt ℚ v)) =
      ∫ y in (fun y => (c : v.adicCompletion ℚ) * y) ⁻¹' T, G ((c : v.adicCompletion ℚ) * y)
        ∂(mulMeasure (selfDualHaarAt ℚ v)) := by
  letI := localBorel ℚ v
  haveI : BorelSpace (v.adicCompletion ℚ) := borelSpace_localBorel ℚ v
  have he := measurableEmbedding_mulLeft₀ (G₀ := v.adicCompletion ℚ) c.ne_zero
  conv_lhs => rw [← map_mul_left_mulMeasure v c, he.restrict_map, he.integral_map]

private theorem integrableOn_mulMeasure_comp_mul_left_iff (G : v.adicCompletion ℚ → ℂ) (c : (v.adicCompletion ℚ)ˣ)
    (T : Set (v.adicCompletion ℚ)) :
    letI := localBorel ℚ v
    IntegrableOn G T (mulMeasure (selfDualHaarAt ℚ v)) ↔
      IntegrableOn (fun y => G ((c : v.adicCompletion ℚ) * y)) ((fun y => (c : v.adicCompletion ℚ) * y) ⁻¹' T)
        (mulMeasure (selfDualHaarAt ℚ v)) := by
  letI := localBorel ℚ v
  haveI : BorelSpace (v.adicCompletion ℚ) := borelSpace_localBorel ℚ v
  have he := measurableEmbedding_mulLeft₀ (G₀ := v.adicCompletion ℚ) c.ne_zero
  rw [IntegrableOn, IntegrableOn]
  conv_lhs => rw [← map_mul_left_mulMeasure v c, he.restrict_map, he.integrable_map_iff]
  rfl

private theorem preimage_mul_left_setOf_valued_eq {k : ℤ} {c : (v.adicCompletion ℚ)ˣ} (hc : c ∈ unitShell v k) :
    (fun y => (c : v.adicCompletion ℚ) * y) ⁻¹' {x : v.adicCompletion ℚ | Valued.v x = WithZero.exp (-k)} =
      unitSet v := by
  have hc' : Valued.v (c : v.adicCompletion ℚ) = WithZero.exp (-k) := hc
  ext y
  simp only [Set.mem_preimage, Set.mem_setOf_eq, unitSet, map_mul, hc']
  constructor
  · intro h
    have h' := h
    conv_rhs at h' => rw [← mul_one (WithZero.exp (-k))]
    exact mul_left_cancel₀ WithZero.exp_ne_zero h'
  · intro h
    rw [h, mul_one]

end Shells
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_laurent_localZeta_eq_gl3LFactorPoly_of_sphericalData.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_exists_laurent_localZeta_eq_gl3LFactorPoly_of_sphericalData.LanglandsTunnell.CubicInduction"

private theorem existsUnique_mem_unitShell (α : (v.adicCompletion ℚ)ˣ) : ∃! k : ℤ, α ∈ unitShell v k := by
  have hne : Valued.v (α : v.adicCompletion ℚ) ≠ 0 := (Valuation.ne_zero_iff _).mpr α.ne_zero
  refine ⟨-WithZero.log (Valued.v (α : v.adicCompletion ℚ)), ?_, fun k hk => ?_⟩
  · show Valued.v (α : v.adicCompletion ℚ) = WithZero.exp (-(-WithZero.log (Valued.v (α : v.adicCompletion ℚ))))
    rw [neg_neg, WithZero.exp_log hne]
  · have hk' : Valued.v (α : v.adicCompletion ℚ) = WithZero.exp (-k) := hk
    have h := hk'.symm.trans (WithZero.exp_log hne).symm
    have h1 := WithZero.exp_le_exp.mp h.le
    have h2 := WithZero.exp_le_exp.mp h.ge
    omega

private theorem measurableSet_unitShell (k : ℤ) :
    letI := localBorel ℚ v
    MeasurableSet (unitShell v k) := by
  letI := localBorel ℚ v
  rw [unitShell_eq_preimage]
  exact comap_measurable (Units.val : (v.adicCompletion ℚ)ˣ → v.adicCompletion ℚ)
    (measurableSet_setOf_valued_eq_exp v _)

private def unitShellIndex (α : (v.adicCompletion ℚ)ˣ) : ℤ := -WithZero.log (Valued.v (α : v.adicCompletion ℚ))

private theorem mem_unitShell_unitShellIndex (α : (v.adicCompletion ℚ)ˣ) : α ∈ unitShell v (unitShellIndex v α) := by
  have hne : Valued.v (α : v.adicCompletion ℚ) ≠ 0 := (Valuation.ne_zero_iff _).mpr α.ne_zero
  show Valued.v (α : v.adicCompletion ℚ) = WithZero.exp (-unitShellIndex v α)
  rw [unitShellIndex, neg_neg, WithZero.exp_log hne]

private theorem measurable_unitShellIndex :
    letI := localBorel ℚ v
    Measurable (unitShellIndex v) := by
  letI := localBorel ℚ v
  refine measurable_to_countable' fun k => ?_
  have hpre : unitShellIndex v ⁻¹' {k} = unitShell v k := by
    ext α
    simp only [Set.mem_preimage, Set.mem_singleton_iff]
    constructor
    · rintro rfl
      exact mem_unitShell_unitShellIndex v α
    · intro hα
      exact (existsUnique_mem_unitShell v α).unique (mem_unitShell_unitShellIndex v α) hα
  rw [hpre]
  exact measurableSet_unitShell v k

private theorem modulus_coe_eq_zpow_neg_unitShellIndex (α : (v.adicCompletion ℚ)ˣ) :
    modulus (α : v.adicCompletion ℚ) = (Ideal.absNorm v.asIdeal : NNReal) ^ (-unitShellIndex v α) := by
  exact modulus_eq_zpow_of_valued v (mem_unitShell_unitShellIndex v α)

private theorem measure_unitShell (k : ℤ) :
    letI := localBorel ℚ v
    Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ v)) (unitShell v k) = selfDualHaarAt ℚ v (unitSet v) := by
  letI := localBorel ℚ v
  haveI : BorelSpace (v.adicCompletion ℚ) := borelSpace_localBorel ℚ v
  have hc : uniformizerUnit ℚ v ^ k ∈ unitShell v k := valued_uniformizerUnit_zpow v k
  rw [(measurableEmbedding_val v).comap_apply, image_val_unitShell]
  conv_lhs => rw [← map_mul_left_mulMeasure v (uniformizerUnit ℚ v ^ k)]
  rw [Measure.map_apply (measurable_const_mul _) (measurableSet_setOf_valued_eq_exp v _),
    preimage_mul_left_setOf_valued_eq v hc, ← Measure.restrict_apply_self, mulMeasure_restrict_unitSet,
    Measure.restrict_apply_self]

private theorem measure_unitSet_ne_top :
    letI := localBorel ℚ v
    selfDualHaarAt ℚ v (unitSet v) ≠ ⊤ := by
  letI := localBorel ℚ v
  haveI : BorelSpace (v.adicCompletion ℚ) := borelSpace_localBorel ℚ v
  haveI : (selfDualHaarAt ℚ v).IsAddHaarMeasure := isAddHaarMeasure_selfDualHaarAt_rat v
  exact ((isCompact_unitSet v).measure_lt_top).ne

private theorem modulus_eq_of_mem_unitShell {k : ℤ} {α : (v.adicCompletion ℚ)ˣ} (hα : α ∈ unitShell v k) :
    modulus (α : v.adicCompletion ℚ) = (Ideal.absNorm v.asIdeal : NNReal) ^ (-k) := by
  exact modulus_eq_zpow_of_valued v hα

private theorem integral_eq_tsum_setIntegral_unitShell (F : (v.adicCompletion ℚ)ˣ → ℂ)
    (hF : letI := localBorel ℚ v; Integrable F (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ v)))) :
    letI := localBorel ℚ v
    ∫ α, F α ∂(Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ v))) =
      ∑' k : ℤ, ∫ α in unitShell v k, F α ∂(Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ v))) := by
  letI := localBorel ℚ v
  have hunion : (⋃ k : ℤ, unitShell v k) = Set.univ :=
    Set.eq_univ_of_forall fun α => Set.mem_iUnion.mpr ⟨_, mem_unitShell_unitShellIndex v α⟩
  have hdisj : Pairwise fun i j => Disjoint (unitShell v i) (unitShell v j) := fun i j hij =>
    Set.disjoint_left.mpr fun α hi hj => hij ((existsUnique_mem_unitShell v α).unique hi hj)
  have h := integral_iUnion (measurableSet_unitShell v) hdisj hF.integrableOn
  rwa [hunion, Measure.restrict_univ] at h

private theorem setIntegral_unitShell_eq_setIntegral_unitShell_zero (F : (v.adicCompletion ℚ)ˣ → ℂ) {k : ℤ}
    {c : (v.adicCompletion ℚ)ˣ} (hc : c ∈ unitShell v k) :
    letI := localBorel ℚ v
    ∫ α in unitShell v k, F α ∂(Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ v))) =
      ∫ β in unitShell v 0, F (c * β) ∂(Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ v))) := by
  letI := localBorel ℚ v
  rw [setIntegral_units_eq, setIntegral_units_eq, image_val_unitShell, image_val_unitShell_zero,
    setIntegral_mulMeasure_comp_mul_left v _ c, preimage_mul_left_setOf_valued_eq v hc, extUnits_mul_left_fun]

private theorem integrableOn_unitShell_iff (F : (v.adicCompletion ℚ)ˣ → ℂ) {k : ℤ} {c : (v.adicCompletion ℚ)ˣ}
    (hc : c ∈ unitShell v k) :
    letI := localBorel ℚ v
    IntegrableOn F (unitShell v k) (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ v))) ↔
      IntegrableOn (fun β => F (c * β)) (unitShell v 0)
        (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ v))) := by
  letI := localBorel ℚ v
  rw [integrableOn_units_iff, integrableOn_units_iff, image_val_unitShell, image_val_unitShell_zero,
    integrableOn_mulMeasure_comp_mul_left_iff v _ c, preimage_mul_left_setOf_valued_eq v hc, extUnits_mul_left_fun]

private theorem setIntegral_unitShell_zero_eq_setIntegral_unitSet (G : v.adicCompletion ℚ → ℂ) :
    letI := localBorel ℚ v
    ∫ α in unitShell v 0, G (α : v.adicCompletion ℚ) ∂(Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ v))) =
      ∫ u in unitSet v, G u ∂(selfDualHaarAt ℚ v) := by
  letI := localBorel ℚ v
  rw [setIntegral_units_eq, image_val_unitShell_zero, ← mulMeasure_restrict_unitSet]
  refine setIntegral_congr_fun (measurableSet_unitSet v) fun u hu => ?_
  have hu0 : u ≠ 0 := (Valuation.ne_zero_iff _).mp (by rw [show Valued.v u = 1 from hu]; exact one_ne_zero)
  simp only [extUnits, dif_neg hu0, Units.val_mk0]

private theorem integrableOn_unitShell_zero_iff (G : v.adicCompletion ℚ → ℂ) :
    letI := localBorel ℚ v
    IntegrableOn (fun α : (v.adicCompletion ℚ)ˣ => G (α : v.adicCompletion ℚ)) (unitShell v 0)
        (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ v))) ↔
      IntegrableOn G (unitSet v) (selfDualHaarAt ℚ v) := by
  letI := localBorel ℚ v
  rw [integrableOn_units_iff, image_val_unitShell_zero, IntegrableOn, IntegrableOn, ← mulMeasure_restrict_unitSet]
  have hU := measurableSet_unitSet v
  have heq : ∀ u ∈ unitSet v, extUnits v (fun α : (v.adicCompletion ℚ)ˣ => G (α : v.adicCompletion ℚ)) u = G u := by
    intro u hu
    have hu0 : u ≠ 0 := (Valuation.ne_zero_iff _).mp (by rw [show Valued.v u = 1 from hu]; exact one_ne_zero)
    simp only [extUnits, dif_neg hu0, Units.val_mk0]
  constructor
  · intro h
    exact (IntegrableOn.congr_fun h heq hU : IntegrableOn G (unitSet v) _)
  · intro h
    exact (IntegrableOn.congr_fun h (fun u hu => (heq u hu).symm) hU : IntegrableOn _ (unitSet v) _)

private theorem real_unitSet :
    letI := localBorel ℚ v
    (selfDualHaarAt ℚ v).real (unitSet v) =
      (1 - (Ideal.absNorm v.asIdeal : ℝ)⁻¹) *
        (selfDualHaarAt ℚ v).real (v.adicCompletionIntegers ℚ : Set (v.adicCompletion ℚ)) := by
  letI := localBorel ℚ v
  haveI : BorelSpace (v.adicCompletion ℚ) := borelSpace_localBorel ℚ v
  haveI : (selfDualHaarAt ℚ v).IsAddHaarMeasure := isAddHaarMeasure_selfDualHaarAt_rat v
  have hsub : adicBall v (-1) ⊆ adicBall v 0 := adicBall_subset v (by norm_num)
  have hfin : selfDualHaarAt ℚ v (adicBall v 0) ≠ ⊤ := (isCompact_adicBall_zero v).measure_lt_top.ne
  have hfin' : selfDualHaarAt ℚ v (adicBall v (-1)) ≠ ⊤ := ne_top_of_le_ne_top hfin (measure_mono hsub)
  have hdiff : (selfDualHaarAt ℚ v).real (adicBall v 0 \ adicBall v (-1)) =
      (selfDualHaarAt ℚ v).real (adicBall v 0) - (selfDualHaarAt ℚ v).real (adicBall v (-1)) := by
    simp only [Measure.real]
    rw [measure_diff hsub (measurableSet_adicBall v (-1)).nullMeasurableSet hfin',
      ENNReal.toReal_sub_of_le (measure_mono hsub) hfin]
  rw [unitSet_eq_diff, hdiff, real_adicBall, real_adicBall, zpow_zero, zpow_neg_one, one_mul, sub_mul, one_mul]

end UnitShells
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_laurent_localZeta_eq_gl3LFactorPoly_of_sphericalData.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_exists_laurent_localZeta_eq_gl3LFactorPoly_of_sphericalData.LanglandsTunnell.CubicInduction"

section AdditiveBalls

variable (v : HeightOneSpectrum (𝓞 ℚ))

variable {v}
variable {ψ : AddChar (v.adicCompletion ℚ) ℂ} (hψ0 : ∀ x : v.adicCompletion ℚ, Valued.v x ≤ 1 → ψ x = 1)
  (hψ1 : ∃ x : v.adicCompletion ℚ, Valued.v x ≤ WithZero.exp 1 ∧ ψ x ≠ 1)

include hψ0 hψ1 in

private theorem setIntegral_adicBall_addChar_eq_ite (m : ℤ) (c : v.adicCompletion ℚ) :
    letI := localBorel ℚ v
    ∫ x in adicBall v m, ψ (c * x) ∂(selfDualHaarAt ℚ v) =
      if Valued.v c ≤ WithZero.exp (-m) then (((selfDualHaarAt ℚ v).real (adicBall v m) : ℝ) : ℂ) else 0 := by
  letI := localBorel ℚ v
  haveI : BorelSpace (v.adicCompletion ℚ) := borelSpace_localBorel ℚ v
  haveI : (selfDualHaarAt ℚ v).IsAddHaarMeasure := isAddHaarMeasure_selfDualHaarAt_rat v
  have hψn : ∀ x : v.adicCompletion ℚ, Valued.v x ≤ WithZero.exp (0 : ℤ) → ψ x = 1 := fun x hx =>
    hψ0 x (by rwa [WithZero.exp_zero] at hx)
  have hψn' : ∃ x : v.adicCompletion ℚ, Valued.v x ≤ WithZero.exp ((0 : ℤ) + 1) ∧ ψ x ≠ 1 := by
    rwa [zero_add]
  have h := tateFourier_indicator_setOf_valued_sub_le ℚ v (selfDualHaarAt ℚ v) ψ 0 hψn hψn' 0 (-m) c
  simp only [sub_zero, zero_mul, AddChar.map_zero_eq_one, one_mul, neg_neg, zero_add] at h
  rw [tateFourier] at h
  rw [← integral_indicator (measurableSet_adicBall v m)]
  have hconv : ∀ x, (adicBall v m).indicator (fun x => ψ (c * x)) x =
      (adicBall v m).indicator (fun _ => (1 : ℂ)) x * ψ (x * c) := by
    intro x
    by_cases hx : x ∈ adicBall v m <;> simp [hx, mul_comm]
  simp_rw [hconv]
  simp only [adicBall]
  rw [h]
  by_cases hc : Valued.v c ≤ WithZero.exp (-m) <;>
    simp only [Set.indicator_apply, Set.mem_setOf_eq, hc, ite_true, ite_false, mul_one, mul_zero]

include hψ0 in

private theorem setIntegral_unitSet_addChar_eq_sub (c : v.adicCompletion ℚ) :
    letI := localBorel ℚ v
    ∫ u in unitSet v, ψ (c * u) ∂(selfDualHaarAt ℚ v) =
      (∫ x in adicBall v 0, ψ (c * x) ∂(selfDualHaarAt ℚ v)) -
        ∫ x in adicBall v (-1), ψ (c * x) ∂(selfDualHaarAt ℚ v) := by
  letI := localBorel ℚ v
  haveI : BorelSpace (v.adicCompletion ℚ) := borelSpace_localBorel ℚ v
  haveI : (selfDualHaarAt ℚ v).IsAddHaarMeasure := isAddHaarMeasure_selfDualHaarAt_rat v
  have hψc : Continuous ψ := continuous_addChar_of_level v hψ0
  have hint : IntegrableOn (fun x : v.adicCompletion ℚ => ψ (c * x)) (adicBall v 0) (selfDualHaarAt ℚ v) :=
    (hψc.comp (continuous_const.mul continuous_id)).continuousOn.integrableOn_compact (isCompact_adicBall_zero v)
  rw [unitSet_eq_diff, setIntegral_diff (measurableSet_adicBall v (-1)) hint (adicBall_subset v (by norm_num))]

include hψ0 in

private theorem setIntegral_ball_addChar_of_valued_le {m : ℤ} {c : v.adicCompletion ℚ} (hc : Valued.v c ≤ WithZero.exp (-m)) :
    letI := localBorel ℚ v
    ∫ x in adicBall v m, ψ (c * x) ∂(selfDualHaarAt ℚ v) = (selfDualHaarAt ℚ v).real (adicBall v m) := by
  letI := localBorel ℚ v
  have hS := measurableSet_adicBall v m
  have hone : ∀ x ∈ adicBall v m, ψ (c * x) = 1 := by
    intro x hx
    apply hψ0
    calc Valued.v (c * x) = Valued.v c * Valued.v x := map_mul _ _ _
      _ ≤ WithZero.exp (-m) * WithZero.exp m := mul_le_mul' hc hx
      _ = 1 := by rw [← WithZero.exp_add, neg_add_cancel, WithZero.exp_zero]
  rw [setIntegral_congr_fun hS hone, setIntegral_const, Complex.real_smul, mul_one]

include hψ1 in

private theorem setIntegral_ball_addChar_of_lt_valued {m : ℤ} {c : v.adicCompletion ℚ} (hc : WithZero.exp (-m) < Valued.v c) :
    letI := localBorel ℚ v
    ∫ x in adicBall v m, ψ (c * x) ∂(selfDualHaarAt ℚ v) = 0 := by
  letI := localBorel ℚ v
  haveI : BorelSpace (v.adicCompletion ℚ) := borelSpace_localBorel ℚ v
  haveI : (selfDualHaarAt ℚ v).IsAddHaarMeasure := isAddHaarMeasure_selfDualHaarAt_rat v
  obtain ⟨x₀, hx₀, hψx₀⟩ := hψ1
  have hc0 : c ≠ 0 := by
    rintro rfl
    rw [map_zero] at hc
    exact (not_lt_zero hc).elim
  obtain ⟨n, hn⟩ : ∃ n : ℤ, Valued.v c = WithZero.exp n :=
    ⟨_, (WithZero.exp_log ((Valuation.ne_zero_iff _).mpr hc0)).symm⟩
  rw [hn, WithZero.exp_lt_exp] at hc
  set z : v.adicCompletion ℚ := x₀ / c with hzdef
  have hcz : c * z = x₀ := by rw [hzdef, mul_div_cancel₀ x₀ hc0]
  have hz : Valued.v z ≤ WithZero.exp m := by
    rw [hzdef, map_div₀, hn, div_eq_mul_inv, ← WithZero.exp_neg]
    calc Valued.v x₀ * WithZero.exp (-n) ≤ WithZero.exp 1 * WithZero.exp (-n) := mul_le_mul' hx₀ le_rfl
      _ = WithZero.exp (1 + -n) := (WithZero.exp_add _ _).symm
      _ ≤ WithZero.exp m := WithZero.exp_le_exp.mpr (by omega)
  have hstable : ∀ y, y + z ∈ adicBall v m ↔ y ∈ adicBall v m := by
    intro y
    constructor
    · intro hy
      have hy' : Valued.v (y + z) ≤ WithZero.exp m := hy
      show Valued.v y ≤ WithZero.exp m
      rw [show y = (y + z) - z by ring]
      exact (Valuation.map_sub _ _ _).trans (max_le hy' hz)
    · intro hy
      exact Valuation.map_add_le _ hy hz
  have h := setIntegral_addChar_mul_eq_zero (selfDualHaarAt ℚ v) (measurableSet_adicBall v m) ψ c (fun _ => (1 : ℂ))
    (by rwa [hcz]) hstable (fun _ _ => rfl)
  simpa only [mul_one] using h

include hψ0 in

private theorem setIntegral_unitSet_addChar_of_valued_le_one {c : v.adicCompletion ℚ} (hc : Valued.v c ≤ 1) :
    letI := localBorel ℚ v
    ∫ u in unitSet v, ψ (c * u) ∂(selfDualHaarAt ℚ v) =
      (1 - (Ideal.absNorm v.asIdeal : ℝ)⁻¹) *
        (selfDualHaarAt ℚ v).real (v.adicCompletionIntegers ℚ : Set (v.adicCompletion ℚ)) := by
  letI := localBorel ℚ v
  have hS := measurableSet_unitSet v
  have hone : ∀ u ∈ unitSet v, ψ (c * u) = 1 := by
    intro u hu
    have hu1 : Valued.v u = 1 := hu
    apply hψ0
    rw [map_mul, hu1, mul_one]
    exact hc
  rw [setIntegral_congr_fun hS hone, setIntegral_const, Complex.real_smul, mul_one, real_unitSet]
  push_cast
  ring

include hψ0 hψ1 in

private theorem setIntegral_unitSet_addChar_of_valued_eq_exp_one {c : v.adicCompletion ℚ} (hc : Valued.v c = WithZero.exp 1) :
    letI := localBorel ℚ v
    ∫ u in unitSet v, ψ (c * u) ∂(selfDualHaarAt ℚ v) =
      -((Ideal.absNorm v.asIdeal : ℝ)⁻¹ *
        (selfDualHaarAt ℚ v).real (v.adicCompletionIntegers ℚ : Set (v.adicCompletion ℚ))) := by
  letI := localBorel ℚ v
  have h0 : ¬ Valued.v c ≤ WithZero.exp (-(0 : ℤ)) := by
    rw [hc, neg_zero, WithZero.exp_le_exp]
    omega
  have h1 : Valued.v c ≤ WithZero.exp (-(-1 : ℤ)) := by rw [hc, neg_neg]
  rw [setIntegral_unitSet_addChar_eq_sub hψ0 c, setIntegral_adicBall_addChar_eq_ite hψ0 hψ1,
    setIntegral_adicBall_addChar_eq_ite hψ0 hψ1, if_neg h0, if_pos h1, real_adicBall, zpow_neg_one, zero_sub]
  push_cast
  ring

include hψ0 hψ1 in

private theorem setIntegral_unitSet_addChar_of_exp_one_lt {c : v.adicCompletion ℚ} (hc : WithZero.exp 1 < Valued.v c) :
    letI := localBorel ℚ v
    ∫ u in unitSet v, ψ (c * u) ∂(selfDualHaarAt ℚ v) = 0 := by
  letI := localBorel ℚ v
  have h0 : ¬ Valued.v c ≤ WithZero.exp (-(0 : ℤ)) := by
    rw [neg_zero]
    exact not_le.mpr (lt_trans (WithZero.exp_lt_exp.mpr zero_lt_one) hc)
  have h1 : ¬ Valued.v c ≤ WithZero.exp (-(-1 : ℤ)) := by
    rw [neg_neg]
    exact not_le.mpr hc
  rw [setIntegral_unitSet_addChar_eq_sub hψ0 c, setIntegral_adicBall_addChar_eq_ite hψ0 hψ1,
    setIntegral_adicBall_addChar_eq_ite hψ0 hψ1, if_neg h0, if_neg h1, sub_zero]

end AdditiveBalls
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_laurent_localZeta_eq_gl3LFactorPoly_of_sphericalData.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_exists_laurent_localZeta_eq_gl3LFactorPoly_of_sphericalData.LanglandsTunnell.CubicInduction"

section GaussIntegrals

variable (v : HeightOneSpectrum (𝓞 ℚ))

private def gaussIntegral (ψ : AddChar (v.adicCompletion ℚ) ℂ) (χ : (v.adicCompletion ℚ)ˣ →* ℂˣ) (c : v.adicCompletion ℚ) :
    ℂ :=
  letI := localBorel ℚ v
  ∫ u in unitSet v, ψ (c * u) * charExt χ u ∂(selfDualHaarAt ℚ v)

private theorem forall_higherUnitsAt_max_eq_one {χ : (v.adicCompletion ℚ)ˣ →* ℂˣ} {a : ℕ}
    (hχ : ∀ u ∈ higherUnitsAt ℚ v a, χ u = 1) : ∀ u ∈ higherUnitsAt ℚ v (max a 1), χ u = 1 := by
  intro u hu
  obtain ⟨hval, hball⟩ := (mem_higherUnitsAt_iff ℚ v).mp hu
  refine hχ u ((mem_higherUnitsAt_iff ℚ v).mpr ⟨hval, ?_⟩)
  rcases hball with h0 | h
  · exact absurd h0 (by omega)
  · by_cases ha : a = 0
    · exact Or.inl ha
    · refine Or.inr (h.trans (WithZero.exp_le_exp.mpr ?_))
      omega

private theorem continuousOn_charExt_unitSet {χ : (v.adicCompletion ℚ)ˣ →* ℂˣ} {a : ℕ}
    (hχ : ∀ u ∈ higherUnitsAt ℚ v a, χ u = 1) : ContinuousOn (charExt χ) (unitSet v) := by
  have hχ' := forall_higherUnitsAt_max_eq_one v hχ
  have ha' : 1 ≤ max a 1 := le_max_right a 1
  intro y₀ hy₀
  have hmem : (fun y => y - y₀) ⁻¹' adicBall v (-((max a 1 : ℕ) : ℤ)) ∈ nhds y₀ := by
    refine ((isOpen_adicBall v _).preimage (continuous_id.sub continuous_const)).mem_nhds ?_
    show Valued.v (y₀ - y₀) ≤ WithZero.exp (-((max a 1 : ℕ) : ℤ))
    rw [sub_self, map_zero]
    exact zero_le'
  have hev : charExt χ =ᶠ[nhdsWithin y₀ (unitSet v)] fun _ => charExt χ y₀ := by
    refine Filter.mem_of_superset (mem_nhdsWithin_of_mem_nhds hmem) fun y hy => ?_
    show charExt χ y = charExt χ y₀
    have hy' : Valued.v (y - y₀) ≤ WithZero.exp (-((max a 1 : ℕ) : ℤ)) := hy
    rw [show y = y₀ + (y - y₀) by ring]
    exact charExt_add_eq v ha' hχ' hy₀ hy'
  exact (continuousWithinAt_const.congr_of_eventuallyEq hev rfl)

private theorem exists_forall_norm_charExt_le {χ : (v.adicCompletion ℚ)ˣ →* ℂˣ} {a : ℕ}
    (hχ : ∀ u ∈ higherUnitsAt ℚ v a, χ u = 1) :
    ∃ C : ℝ, ∀ u ∈ unitSet v, ‖charExt χ u‖ ≤ C := by
  exact (isCompact_unitSet v).exists_bound_of_continuousOn (continuousOn_charExt_unitSet v hχ)

private theorem gaussIntegral_eq_setIntegral_unitShell_zero (ψ : AddChar (v.adicCompletion ℚ) ℂ)
    (χ : (v.adicCompletion ℚ)ˣ →* ℂˣ) (c : v.adicCompletion ℚ) :
    letI := localBorel ℚ v
    gaussIntegral v ψ χ c =
      ∫ α in unitShell v 0, ψ (c * α) * (χ α : ℂ) ∂(Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ v))) := by
  letI := localBorel ℚ v
  simp only [gaussIntegral]
  rw [← setIntegral_unitShell_zero_eq_setIntegral_unitSet v (fun u => ψ (c * u) * charExt χ u)]
  simp only [charExt_coe_units]

private theorem gaussIntegral_of_hasConductorExponentAt_zero (ψ : AddChar (v.adicCompletion ℚ) ℂ)
    {χ : (v.adicCompletion ℚ)ˣ →* ℂˣ} (hχ : HasConductorExponentAt ℚ v χ 0) (c : v.adicCompletion ℚ) :
    letI := localBorel ℚ v
    gaussIntegral v ψ χ c = ∫ u in unitSet v, ψ (c * u) ∂(selfDualHaarAt ℚ v) := by
  letI := localBorel ℚ v
  simp only [gaussIntegral]
  refine setIntegral_congr_fun (measurableSet_unitSet v) fun u hu => ?_
  have hu1 : Valued.v u = 1 := hu
  have hu0 : u ≠ 0 := (Valuation.ne_zero_iff _).mp (by rw [hu1]; exact one_ne_zero)
  rw [charExt_of_ne_zero χ hu0, (hasConductorExponentAt_zero_iff ℚ v).mp hχ (Units.mk0 u hu0) (by simpa using hu1),
    Units.val_one, mul_one]

private theorem gaussIntegral_mul_coe_units (ψ : AddChar (v.adicCompletion ℚ) ℂ) (χ : (v.adicCompletion ℚ)ˣ →* ℂˣ)
    (c : v.adicCompletion ℚ) {w : (v.adicCompletion ℚ)ˣ} (hw : Valued.v (w : v.adicCompletion ℚ) = 1) :
    gaussIntegral v ψ χ (c * w) = (χ w : ℂ)⁻¹ * gaussIntegral v ψ χ c := by
  letI := localBorel ℚ v
  haveI : BorelSpace (v.adicCompletion ℚ) := borelSpace_localBorel ℚ v
  haveI : (selfDualHaarAt ℚ v).IsAddHaarMeasure := isAddHaarMeasure_selfDualHaarAt_rat v
  haveI : (selfDualHaarAt ℚ v).Regular := regular_selfDualHaarAt v
  have hw0 : (χ w : ℂ) ≠ 0 := Units.ne_zero _
  have hsub : gaussIntegral v ψ χ c = (χ w : ℂ) * gaussIntegral v ψ χ (c * w) := by
    simp only [gaussIntegral]
    rw [setIntegral_comp_mul_left_of_modulus_eq_one (selfDualHaarAt ℚ v) (modulus_eq_one_of_valued v hw)
        (fun u => ψ (c * u) * charExt χ u) (measurableSet_unitSet v) (mul_mem_unitSet_iff v hw), ← integral_const_mul]
    refine setIntegral_congr_fun (measurableSet_unitSet v) fun u _ => ?_
    rw [charExt_units_mul, mul_assoc c]
    ring
  rw [hsub, inv_mul_cancel_left₀ hw0]

variable {v}
variable {ψ : AddChar (v.adicCompletion ℚ) ℂ} (hψ0 : ∀ x : v.adicCompletion ℚ, Valued.v x ≤ 1 → ψ x = 1)
  (hψ1 : ∃ x : v.adicCompletion ℚ, Valued.v x ≤ WithZero.exp 1 ∧ ψ x ≠ 1)
  {χ : (v.adicCompletion ℚ)ˣ →* ℂˣ} {a : ℕ} (ha : 1 ≤ a) (hχ : HasConductorExponentAt ℚ v χ a)

include hψ0 ha hχ in

private theorem gaussIntegral_eq_zero_of_valued_lt {c : v.adicCompletion ℚ} (hc : Valued.v c < WithZero.exp (a : ℤ)) :
    gaussIntegral v ψ χ c = 0 := by
  letI := localBorel ℚ v
  haveI : BorelSpace (v.adicCompletion ℚ) := borelSpace_localBorel ℚ v
  haveI : (selfDualHaarAt ℚ v).IsAddHaarMeasure := isAddHaarMeasure_selfDualHaarAt_rat v
  haveI : (selfDualHaarAt ℚ v).Regular := regular_selfDualHaarAt v
  obtain ⟨u₁, hu₁mem, hu₁ne⟩ := hχ.2 (a - 1) (by omega)
  obtain ⟨hu₁val, hu₁ball⟩ := (mem_higherUnitsAt_iff ℚ v).mp hu₁mem

  have hsmall : Valued.v (c * ((u₁ : v.adicCompletion ℚ) - 1)) ≤ 1 := by
    rw [map_mul]
    by_cases hc0 : Valued.v c = 0
    · rw [hc0, zero_mul]
      exact zero_le'
    obtain ⟨m, hm⟩ : ∃ m : ℤ, Valued.v c = WithZero.exp m := ⟨_, (WithZero.exp_log hc0).symm⟩
    rw [hm, WithZero.exp_lt_exp] at hc
    have hball : Valued.v ((u₁ : v.adicCompletion ℚ) - 1) ≤ WithZero.exp (-((a - 1 : ℕ) : ℤ)) := by
      rcases hu₁ball with h0 | h
      ·
        rw [h0, Nat.cast_zero, neg_zero, WithZero.exp_zero]
        calc Valued.v ((u₁ : v.adicCompletion ℚ) - 1)
            ≤ max (Valued.v (u₁ : v.adicCompletion ℚ)) (Valued.v (1 : v.adicCompletion ℚ)) := Valuation.map_sub _ _ _
          _ = 1 := by rw [hu₁val, map_one, max_self]
      · exact h
    calc Valued.v c * Valued.v ((u₁ : v.adicCompletion ℚ) - 1)
        ≤ WithZero.exp m * WithZero.exp (-((a - 1 : ℕ) : ℤ)) := by rw [hm]; exact mul_le_mul' le_rfl hball
      _ ≤ 1 := by
        rw [← WithZero.exp_add, ← WithZero.exp_zero, WithZero.exp_le_exp]
        push_cast [Nat.cast_sub ha]
        omega
  simp only [gaussIntegral]
  refine setIntegral_mul_charExt_eq_zero (selfDualHaarAt ℚ v) (measurableSet_unitSet v) (fun y => ψ (c * y)) χ
    (modulus_eq_one_of_valued v hu₁val) hu₁ne (mul_mem_unitSet_iff v hu₁val) fun y hy => ?_
  have hy1 : Valued.v y = 1 := hy
  have hsplit : c * ((u₁ : v.adicCompletion ℚ) * y) = c * y + c * ((u₁ : v.adicCompletion ℚ) - 1) * y := by ring
  have hterm : Valued.v (c * ((u₁ : v.adicCompletion ℚ) - 1) * y) ≤ 1 := by
    rw [map_mul, hy1, mul_one]
    exact hsmall
  show ψ (c * ((u₁ : v.adicCompletion ℚ) * y)) = ψ (c * y)
  rw [hsplit, AddChar.map_add_eq_mul, hψ0 _ hterm, mul_one]

include hψ1 ha hχ in

private theorem gaussIntegral_eq_zero_of_exp_lt_valued {c : v.adicCompletion ℚ}
    (hc : WithZero.exp (a : ℤ) < Valued.v c) : gaussIntegral v ψ χ c = 0 := by
  letI := localBorel ℚ v
  haveI : BorelSpace (v.adicCompletion ℚ) := borelSpace_localBorel ℚ v
  haveI : (selfDualHaarAt ℚ v).IsAddHaarMeasure := isAddHaarMeasure_selfDualHaarAt_rat v
  obtain ⟨x, hx, hxne⟩ := hψ1
  have hc0 : c ≠ 0 := by
    rintro rfl
    rw [map_zero] at hc
    exact (not_lt_zero hc).elim
  have hcv : Valued.v c ≠ 0 := (Valuation.ne_zero_iff _).mpr hc0
  obtain ⟨n, hn⟩ : ∃ n : ℤ, Valued.v c = WithZero.exp n := ⟨_, (WithZero.exp_log hcv).symm⟩
  rw [hn, WithZero.exp_lt_exp] at hc
  set z : v.adicCompletion ℚ := x / c with hzdef
  have hcz : c * z = x := by rw [hzdef, mul_div_cancel₀ x hc0]
  have hz : Valued.v z ≤ WithZero.exp (-(a : ℤ)) := by
    rw [hzdef, map_div₀, hn, div_eq_mul_inv, ← WithZero.exp_neg]
    calc Valued.v x * WithZero.exp (-n) ≤ WithZero.exp 1 * WithZero.exp (-n) := mul_le_mul' hx le_rfl
      _ = WithZero.exp (1 + -n) := (WithZero.exp_add _ _).symm
      _ ≤ WithZero.exp (-(a : ℤ)) := WithZero.exp_le_exp.mpr (by omega)
  have hz1 : Valued.v z < 1 := lt_of_le_of_lt hz (by
    rw [← WithZero.exp_zero, WithZero.exp_lt_exp]
    omega)
  simp only [gaussIntegral]
  exact setIntegral_addChar_mul_eq_zero (selfDualHaarAt ℚ v) (measurableSet_unitSet v) ψ c (charExt χ) (by rwa [hcz])
    (add_mem_unitSet_iff v hz1) fun y hy => charExt_add_eq v ha hχ.1 hy hz

include hψ0 hψ1 ha hχ in

private theorem gaussIntegral_eq_zero_of_valued_ne {c : v.adicCompletion ℚ} (hc : Valued.v c ≠ WithZero.exp (a : ℤ)) :
    gaussIntegral v ψ χ c = 0 := by
  rcases lt_or_gt_of_ne hc with hlt | hgt
  · exact gaussIntegral_eq_zero_of_valued_lt hψ0 ha hχ hlt
  · exact gaussIntegral_eq_zero_of_exp_lt_valued hψ1 ha hχ hgt

include hψ0 hψ1 ha hχ in

private theorem gaussIntegral_mul_gaussIntegral_inv {c : v.adicCompletion ℚ} (hc : Valued.v c = WithZero.exp (a : ℤ)) :
    letI := localBorel ℚ v
    gaussIntegral v ψ χ c * gaussIntegral v ψ χ⁻¹ c * (Ideal.absNorm v.asIdeal : ℂ) ^ a =
      charExt χ (-1) *
        (((selfDualHaarAt ℚ v).real (v.adicCompletionIntegers ℚ : Set (v.adicCompletion ℚ)) : ℝ) : ℂ) ^ 2 := by
  letI := localBorel ℚ v
  haveI : BorelSpace (v.adicCompletion ℚ) := borelSpace_localBorel ℚ v
  haveI : (selfDualHaarAt ℚ v).IsAddHaarMeasure := isAddHaarMeasure_selfDualHaarAt_rat v
  have hψn : ∀ x : v.adicCompletion ℚ, Valued.v x ≤ WithZero.exp (0 : ℤ) → ψ x = 1 := fun x hx =>
    hψ0 x (by rwa [WithZero.exp_zero] at hx)
  have hψn' : ∃ x : v.adicCompletion ℚ, Valued.v x ≤ WithZero.exp ((0 : ℤ) + 1) ∧ ψ x ≠ 1 := by
    rwa [zero_add]
  have hc' : Valued.v c = WithZero.exp ((0 : ℤ) + a) := by rwa [zero_add]
  have h := setIntegral_addChar_mul_charExt_mul_setIntegral_inv_mul_pow_eq ℚ v (selfDualHaarAt ℚ v) ψ 0 hψn hψn' χ a ha
    hχ c hc'
  simpa only [gaussIntegral, unitSet] using h

include hψ0 hψ1 ha hχ in

private theorem gaussIntegral_ne_zero {c : v.adicCompletion ℚ} (hc : Valued.v c = WithZero.exp (a : ℤ)) :
    gaussIntegral v ψ χ c ≠ 0 := by
  intro h0
  have hprod := gaussIntegral_mul_gaussIntegral_inv hψ0 hψ1 ha hχ hc
  rw [h0, zero_mul, zero_mul] at hprod
  have hneg : charExt χ (-1 : v.adicCompletion ℚ) ≠ 0 := by
    rw [charExt_of_ne_zero χ (neg_ne_zero.mpr one_ne_zero)]
    exact Units.ne_zero _
  have hvol : (((selfDualHaarAt ℚ v).real (v.adicCompletionIntegers ℚ : Set (v.adicCompletion ℚ)) : ℝ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (real_integers_pos v).ne'
  exact mul_ne_zero hneg (pow_ne_zero 2 hvol) hprod.symm

end GaussIntegrals
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_laurent_localZeta_eq_gl3LFactorPoly_of_sphericalData.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_exists_laurent_localZeta_eq_gl3LFactorPoly_of_sphericalData.LanglandsTunnell.CubicInduction"

section RootNumber

variable (v : HeightOneSpectrum (𝓞 ℚ))

private theorem stdRootNumberAt_eq_gaussIntegral (χ : (v.adicCompletion ℚ)ˣ →* ℂˣ) {a : ℕ} (ha : 1 ≤ a)
    (hχ : HasConductorExponentAt ℚ v χ a) (hu : ‖((χ (uniformizerUnit ℚ v) : ℂˣ) : ℂ)‖ = 1)
    (hlev : addCharLevel (psiLocal ℚ v) = 0) :
    stdRootNumberAt ℚ v χ =
      ((χ (uniformizerUnit ℚ v) : ℂˣ) : ℂ) ^ a *
        ((((Ideal.absNorm v.asIdeal : ℝ) ^ (a : ℤ) : ℝ) : ℂ)) ^ (1 / 2 : ℂ) *
          gaussIntegral v (psiLocal ℚ v) χ⁻¹
            ((uniformizerUnit ℚ v ^ (-(a : ℤ)) : (v.adicCompletion ℚ)ˣ) : v.adicCompletion ℚ) := by
  letI := localBorel ℚ v
  have hnum := localZeta_tateFourier_stdTestFunAt ℚ v χ a ha hχ (1 / 2) (norm_inv_mul_natCast_cpow_lt_one v χ hu)
  have hden := localZeta_stdTestFunAt_eq_real_image_higherUnitsAt ℚ v χ a ha hχ (1 / 2)
  have hvol := selfDualHaarAt_real_image_higherUnitsAt ℚ v a ha
  have hV : (selfDualHaarAt ℚ v).real
      (((↑) : (v.adicCompletion ℚ)ˣ → v.adicCompletion ℚ) '' higherUnitsAt ℚ v a) ≠ 0 := by
    rw [hvol]
    exact (mul_pos (zpow_pos (absNorm_pos v) _) (Real.rpow_pos_of_pos (absNorm_pos v) _)).ne'
  have hVc : (((selfDualHaarAt ℚ v).real
      (((↑) : (v.adicCompletion ℚ)ˣ → v.adicCompletion ℚ) '' higherUnitsAt ℚ v a) : ℝ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr hV
  rw [stdRootNumberAt, stdEpsilonAt,
    localEpsilonAt_of_not_hasConductorExponentAt_zero ℚ v _ _ _ (not_hasConductorExponentAt_zero_of_one_le v ha hχ),
    localGammaAt, hnum, hden, mul_assoc, mul_assoc, mul_div_cancel_left₀ _ hVc]
  simp only [gaussIntegral, unitSet, hlev, zero_add, zpow_natCast]
  norm_num [mul_assoc]

end RootNumber
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_laurent_localZeta_eq_gl3LFactorPoly_of_sphericalData.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_exists_laurent_localZeta_eq_gl3LFactorPoly_of_sphericalData.LanglandsTunnell.CubicInduction"

section ProductIntegrals

variable (v : HeightOneSpectrum (𝓞 ℚ))

section ProductMeasure

private theorem sigmaFinite_unitsMeasure :
    letI := localBorel ℚ v
    SigmaFinite (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ v))) := by
  letI := localBorel ℚ v
  refine Measure.sigmaFinite_of_countable (S := Set.range (unitShell v)) (Set.countable_range _) ?_ ?_
  · rintro _ ⟨k, rfl⟩
    rw [measure_unitShell]
    exact lt_top_iff_ne_top.mpr (measure_unitSet_ne_top v)
  · rw [Set.sUnion_range]
    exact Set.eq_univ_of_forall fun α => Set.mem_iUnion.mpr ⟨_, mem_unitShell_unitShellIndex v α⟩

private theorem sigmaFinite_selfDualHaarAt :
    letI := localBorel ℚ v
    SigmaFinite (selfDualHaarAt ℚ v) := by
  letI := localBorel ℚ v
  haveI : BorelSpace (v.adicCompletion ℚ) := borelSpace_localBorel ℚ v
  haveI : (selfDualHaarAt ℚ v).IsAddHaarMeasure := isAddHaarMeasure_selfDualHaarAt_rat v
  infer_instance

end ProductMeasure
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_laurent_localZeta_eq_gl3LFactorPoly_of_sphericalData.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_exists_laurent_localZeta_eq_gl3LFactorPoly_of_sphericalData.LanglandsTunnell.CubicInduction"

private theorem integral_integral_eq_integral_prod (f : (v.adicCompletion ℚ)ˣ × v.adicCompletion ℚ → ℂ)
    (hf : letI := localBorel ℚ v
      Integrable f ((Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ v))).prod (selfDualHaarAt ℚ v))) :
    letI := localBorel ℚ v
    ∫ α, (∫ x, f (α, x) ∂(selfDualHaarAt ℚ v)) ∂(Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ v))) =
      ∫ p, f p ∂((Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ v))).prod (selfDualHaarAt ℚ v)) := by
  letI := localBorel ℚ v
  haveI := sigmaFinite_unitsMeasure v
  haveI := sigmaFinite_selfDualHaarAt v
  exact (integral_prod f hf).symm

private theorem integral_prod_eq_tsum_setIntegral_unitShell (f : (v.adicCompletion ℚ)ˣ × v.adicCompletion ℚ → ℂ)
    (hf : letI := localBorel ℚ v
      Integrable f ((Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ v))).prod (selfDualHaarAt ℚ v))) :
    letI := localBorel ℚ v
    ∫ p, f p ∂((Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ v))).prod (selfDualHaarAt ℚ v)) =
      ∑' k : ℤ, ∫ α in unitShell v k, (∫ x, f (α, x) ∂(selfDualHaarAt ℚ v))
        ∂(Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ v))) := by
  letI := localBorel ℚ v
  haveI := sigmaFinite_unitsMeasure v
  haveI := sigmaFinite_selfDualHaarAt v
  rw [integral_prod f hf]
  exact integral_eq_tsum_setIntegral_unitShell v _ hf.integral_prod_left

end ProductIntegrals
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_laurent_localZeta_eq_gl3LFactorPoly_of_sphericalData.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_exists_laurent_localZeta_eq_gl3LFactorPoly_of_sphericalData.LanglandsTunnell.CubicInduction"

end LanglandsTunnell.CubicInduction
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_laurent_localZeta_eq_gl3LFactorPoly_of_sphericalData.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_exists_laurent_localZeta_eq_gl3LFactorPoly_of_sphericalData.LanglandsTunnell.CubicInduction"
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_laurent_localZeta_eq_gl3LFactorPoly_of_sphericalData.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_exists_laurent_localZeta_eq_gl3LFactorPoly_of_sphericalData.LanglandsTunnell.CubicInduction"

end
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_laurent_localZeta_eq_gl3LFactorPoly_of_sphericalData.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_exists_laurent_localZeta_eq_gl3LFactorPoly_of_sphericalData.LanglandsTunnell.CubicInduction"
end
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_laurent_localZeta_eq_gl3LFactorPoly_of_sphericalData.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_exists_laurent_localZeta_eq_gl3LFactorPoly_of_sphericalData.LanglandsTunnell.CubicInduction"

section

set_option autoImplicit false

open IsDedekindDomain NumberField NumberField.AdelicLevel NumberField.StandardAddChar LanglandsTunnell.TateLocal MeasureTheory

noncomputable section

namespace LanglandsTunnell
p2m_export "LanglandsTunnell" "TateLocal.localBorel TateLocal.borelSpace_localBorel TateLocal.stdRootNumberAt TateLocal.higherUnitsAt TateLocal.mem_higherUnitsAt_iff TateLocal.HasConductorExponentAt TateLocal.modulus TateLocal.modulus_mul"
namespace CubicInduction
p2m_export "LanglandsTunnell.CubicInduction" "localZeta31 localZeta30 localZetaDual31 IsLocalZeta30ConvergentAbove IsLocalZeta31ConvergentAbove lowerUnipotent21 lowerUnipotent21_coe longWeyl3 longWeyl3_coe dualWhittakerFn3 dualWhittakerFn3_apply weylPrime3 weylPrime3_coe transposeInv3_weylPrime3 transposeInv3_lowerUnipotent21 IsGL3PsiWhittakerFn transposeInv3 upperUnipotent3 upperUnipotent3_coe upperUnipotent3_zero embedMat2 iotaGL coe_iotaGL localMaximalCompact3 mem_localMaximalCompact3_iff LocalGL3 varpi varpi_ne_zero heckeGen1 heckeGen2 centralGen cNormQ cosetSum IsCosetEigenfunction IsRightInvariant diagUnitGL2 coe_diagUnitGL2 diagHom diagHom_apply ratPrimeAt ratPrimeAt_ne_zero ratPrimeUnit sphericalTorusValue diagUnits2 coe_diagUnits2 twoRowPointLocal twoRowPointLocal_zero_right eq_zero_of_coe_eq_diagonal_of_valued_lt_of_isGL3PsiWhittakerFn eq_zero_of_isCosetEigenfunction_of_isGL3PsiWhittakerFn_of_apply_one_eq_zero exists_eq_upperUnipotent3_mul_diagonal_mul_mem_localMaximalCompact3 isGL3PsiWhittakerFn_dualWhittakerFn3 sphericalTorusValue_eq_of_isCosetEigenfunction_of_isGL3PsiWhittakerFn"
p2m_open "LanglandsTunnell.CubicInduction LanglandsTunnell"

section ScalingAndMeasurability

variable (v : HeightOneSpectrum (𝓞 ℚ))

private theorem map_mul_left_selfDualHaarAt (c : (v.adicCompletion ℚ)ˣ) :
    letI := localBorel ℚ v
    Measure.map (fun x => (c : v.adicCompletion ℚ) * x) (selfDualHaarAt ℚ v) =
      ((modulus (c : v.adicCompletion ℚ) : ENNReal))⁻¹ • selfDualHaarAt ℚ v := by
  letI := localBorel ℚ v
  haveI : BorelSpace (v.adicCompletion ℚ) := borelSpace_localBorel ℚ v
  haveI : (selfDualHaarAt ℚ v).IsAddHaarMeasure := isAddHaarMeasure_selfDualHaarAt_rat v
  haveI : (selfDualHaarAt ℚ v).Regular := regular_selfDualHaarAt v
  exact map_mul_left_eq_smul (selfDualHaarAt ℚ v) c

private theorem map_mul_left_unitsMeasure (c : (v.adicCompletion ℚ)ˣ) :
    letI := localBorel ℚ v
    Measure.map (fun α => c * α) (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ v))) =
      Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ v)) := by
  letI := localBorel ℚ v
  haveI : BorelSpace (v.adicCompletion ℚ) := borelSpace_localBorel ℚ v
  have hf := measurableEmbedding_val v
  have hm : Measurable fun α : (v.adicCompletion ℚ)ˣ => c * α :=
    measurable_comap_iff.mpr ((measurable_const_mul (c : v.adicCompletion ℚ)).comp (comap_measurable _))
  ext S hS
  rw [Measure.map_apply hm hS, hf.comap_apply, hf.comap_apply]
  have himg : Units.val '' ((fun α => c * α) ⁻¹' S) =
      (fun x => (c : v.adicCompletion ℚ) * x) ⁻¹' (Units.val '' S) := by
    ext x
    constructor
    · rintro ⟨α, hα, rfl⟩
      exact ⟨c * α, hα, rfl⟩
    · rintro ⟨β, hβ, hβx⟩
      refine ⟨c⁻¹ * β, ?_, ?_⟩
      · show c * (c⁻¹ * β) ∈ S
        rwa [mul_inv_cancel_left]
      · rw [Units.val_mul, hβx, ← mul_assoc, Units.inv_mul, one_mul]
  rw [himg, ← Measure.map_apply (measurable_const_mul _) (hf.measurableSet_image.mpr hS), map_mul_left_mulMeasure v c]

private theorem continuousOn_charExt_compl_zero {χ : (v.adicCompletion ℚ)ˣ →* ℂˣ} {a : ℕ}
    (hχ : ∀ u ∈ higherUnitsAt ℚ v a, χ u = 1) : ContinuousOn (charExt χ) ({0}ᶜ : Set (v.adicCompletion ℚ)) := by
  have hχ' := forall_higherUnitsAt_max_eq_one v hχ
  have ha' : 1 ≤ max a 1 := le_max_right a 1
  intro y hy
  have hy0 : y ≠ 0 := hy
  obtain ⟨n, hn⟩ : ∃ n : ℤ, Valued.v y = WithZero.exp n :=
    ⟨_, (WithZero.exp_log ((Valuation.ne_zero_iff _).mpr hy0)).symm⟩
  have hmem : (fun x => x - y) ⁻¹' adicBall v (n - (max a 1 : ℕ)) ∈ nhds y := by
    refine ((isOpen_adicBall v _).preimage (continuous_id.sub continuous_const)).mem_nhds ?_
    show Valued.v (y - y) ≤ WithZero.exp (n - (max a 1 : ℕ))
    rw [sub_self, map_zero]
    exact zero_le'
  have hev : charExt χ =ᶠ[nhdsWithin y {0}ᶜ] fun _ => charExt χ y := by
    refine Filter.mem_of_superset (mem_nhdsWithin_of_mem_nhds hmem) fun x hx => ?_
    show charExt χ x = charExt χ y
    have hx' : Valued.v (x - y) ≤ WithZero.exp (n - (max a 1 : ℕ)) := hx
    set w : v.adicCompletion ℚ := (x - y) / y with hw
    have hwv : Valued.v w ≤ WithZero.exp (-((max a 1 : ℕ) : ℤ)) := by
      rw [hw, map_div₀, hn, div_eq_mul_inv, ← WithZero.exp_neg]
      calc Valued.v (x - y) * WithZero.exp (-n)
          ≤ WithZero.exp (n - (max a 1 : ℕ)) * WithZero.exp (-n) := mul_le_mul' hx' le_rfl
        _ = WithZero.exp (n - (max a 1 : ℕ) + -n) := (WithZero.exp_add _ _).symm
        _ = WithZero.exp (-((max a 1 : ℕ) : ℤ)) := by congr 1; ring
    have hw1 : Valued.v w < 1 := lt_of_le_of_lt hwv (by
      rw [← WithZero.exp_zero, WithZero.exp_lt_exp]
      omega)
    have hu1 : Valued.v (1 + w) = 1 :=
      (add_mem_unitSet_iff v hw1 1).mpr (show Valued.v (1 : v.adicCompletion ℚ) = 1 from map_one _)
    have hu0 : (1 + w : v.adicCompletion ℚ) ≠ 0 := (Valuation.ne_zero_iff _).mp (by rw [hu1]; exact one_ne_zero)
    have humem : Units.mk0 (1 + w) hu0 ∈ higherUnitsAt ℚ v (max a 1) := by
      refine (mem_higherUnitsAt_iff ℚ v).mpr ⟨?_, Or.inr ?_⟩
      · rw [Units.val_mk0]
        exact hu1
      · rw [Units.val_mk0, add_sub_cancel_left]
        exact hwv
    have hxy : x = ((Units.mk0 (1 + w) hu0 : (v.adicCompletion ℚ)ˣ) : v.adicCompletion ℚ) * y := by
      rw [Units.val_mk0, hw, add_mul, one_mul, div_mul_cancel₀ _ hy0]
      ring
    rw [hxy, charExt_units_mul, hχ' _ humem, Units.val_one, one_mul]
  exact continuousWithinAt_const.congr_of_eventuallyEq hev rfl

private theorem measurable_charExt {χ : (v.adicCompletion ℚ)ˣ →* ℂˣ} {a : ℕ} (hχ : ∀ u ∈ higherUnitsAt ℚ v a, χ u = 1) :
    letI := localBorel ℚ v
    Measurable (charExt χ) := by
  letI := localBorel ℚ v
  haveI : BorelSpace (v.adicCompletion ℚ) := borelSpace_localBorel ℚ v
  exact measurable_of_continuousOn_compl_singleton 0 (continuousOn_charExt_compl_zero v hχ)

private theorem measurable_coe_units_apply {χ : (v.adicCompletion ℚ)ˣ →* ℂˣ} {a : ℕ}
    (hχ : ∀ u ∈ higherUnitsAt ℚ v a, χ u = 1) :
    letI := localBorel ℚ v
    Measurable fun α : (v.adicCompletion ℚ)ˣ => ((χ α : ℂˣ) : ℂ) := by
  letI := localBorel ℚ v
  have h : (fun α : (v.adicCompletion ℚ)ˣ => ((χ α : ℂˣ) : ℂ)) = charExt χ ∘ Units.val := by
    funext α
    simp only [Function.comp_apply, charExt_of_ne_zero χ α.ne_zero, Units.mk0_val]
  rw [h]
  exact (measurable_charExt v hχ).comp (comap_measurable _)

private theorem sigmaFinite_comap_val_mulMeasure :
    letI := localBorel ℚ v
    SigmaFinite (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ v))) := by
  letI := localBorel ℚ v
  exact sigmaFinite_unitsMeasure v

private theorem sigmaFinite_selfDualHaarAt_rat :
    letI := localBorel ℚ v
    SigmaFinite (selfDualHaarAt ℚ v) := by
  letI := localBorel ℚ v
  exact sigmaFinite_selfDualHaarAt v

end ScalingAndMeasurability
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_laurent_localZeta_eq_gl3LFactorPoly_of_sphericalData.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_exists_laurent_localZeta_eq_gl3LFactorPoly_of_sphericalData.LanglandsTunnell.CubicInduction"

end LanglandsTunnell.CubicInduction
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_laurent_localZeta_eq_gl3LFactorPoly_of_sphericalData.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_exists_laurent_localZeta_eq_gl3LFactorPoly_of_sphericalData.LanglandsTunnell.CubicInduction"
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_laurent_localZeta_eq_gl3LFactorPoly_of_sphericalData.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_exists_laurent_localZeta_eq_gl3LFactorPoly_of_sphericalData.LanglandsTunnell.CubicInduction"

end
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_laurent_localZeta_eq_gl3LFactorPoly_of_sphericalData.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_exists_laurent_localZeta_eq_gl3LFactorPoly_of_sphericalData.LanglandsTunnell.CubicInduction"
end
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_laurent_localZeta_eq_gl3LFactorPoly_of_sphericalData.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_exists_laurent_localZeta_eq_gl3LFactorPoly_of_sphericalData.LanglandsTunnell.CubicInduction"

section

set_option autoImplicit false

open IsDedekindDomain NumberField NumberField.AdelicLevel NumberField.StandardAddChar LanglandsTunnell.TateLocal MeasureTheory

noncomputable section

namespace LanglandsTunnell
p2m_export "LanglandsTunnell" "TateLocal.localBorel TateLocal.borelSpace_localBorel TateLocal.stdRootNumberAt TateLocal.higherUnitsAt TateLocal.mem_higherUnitsAt_iff TateLocal.HasConductorExponentAt TateLocal.modulus TateLocal.modulus_mul"
namespace CubicInduction
p2m_export "LanglandsTunnell.CubicInduction" "localZeta31 localZeta30 localZetaDual31 IsLocalZeta30ConvergentAbove IsLocalZeta31ConvergentAbove lowerUnipotent21 lowerUnipotent21_coe longWeyl3 longWeyl3_coe dualWhittakerFn3 dualWhittakerFn3_apply weylPrime3 weylPrime3_coe transposeInv3_weylPrime3 transposeInv3_lowerUnipotent21 IsGL3PsiWhittakerFn transposeInv3 upperUnipotent3 upperUnipotent3_coe upperUnipotent3_zero embedMat2 iotaGL coe_iotaGL localMaximalCompact3 mem_localMaximalCompact3_iff LocalGL3 varpi varpi_ne_zero heckeGen1 heckeGen2 centralGen cNormQ cosetSum IsCosetEigenfunction IsRightInvariant diagUnitGL2 coe_diagUnitGL2 diagHom diagHom_apply ratPrimeAt ratPrimeAt_ne_zero ratPrimeUnit sphericalTorusValue diagUnits2 coe_diagUnits2 twoRowPointLocal twoRowPointLocal_zero_right eq_zero_of_coe_eq_diagonal_of_valued_lt_of_isGL3PsiWhittakerFn eq_zero_of_isCosetEigenfunction_of_isGL3PsiWhittakerFn_of_apply_one_eq_zero exists_eq_upperUnipotent3_mul_diagonal_mul_mem_localMaximalCompact3 isGL3PsiWhittakerFn_dualWhittakerFn3 sphericalTorusValue_eq_of_isCosetEigenfunction_of_isGL3PsiWhittakerFn"
p2m_open "LanglandsTunnell.CubicInduction LanglandsTunnell"

section Balls

variable (v : HeightOneSpectrum (𝓞 ℚ))

private theorem adicBall_measurableSet (m : ℤ) :
    letI := localBorel ℚ v
    MeasurableSet (adicBall v m) :=
  measurableSet_adicBall v m

private theorem adicBall_eq_image (m : ℤ) :
    adicBall v m =
      (fun x => ((uniformizerUnit ℚ v ^ (-m) : (v.adicCompletion ℚ)ˣ) : v.adicCompletion ℚ) * x) '' adicBall v 0 := by
  have hc : Valued.v ((uniformizerUnit ℚ v ^ (-m) : (v.adicCompletion ℚ)ˣ) : v.adicCompletion ℚ) = WithZero.exp m := by
    rw [valued_uniformizerUnit_zpow, neg_neg]
  ext x
  constructor
  · intro hx
    refine ⟨((uniformizerUnit ℚ v ^ (-m) : (v.adicCompletion ℚ)ˣ) : v.adicCompletion ℚ)⁻¹ * x, ?_,
      mul_inv_cancel_left₀ (Units.ne_zero _) x⟩
    show Valued.v (((uniformizerUnit ℚ v ^ (-m) : (v.adicCompletion ℚ)ˣ) : v.adicCompletion ℚ)⁻¹ * x) ≤
      WithZero.exp 0
    rw [map_mul, map_inv₀, hc, ← WithZero.exp_neg]
    calc WithZero.exp (-m) * Valued.v x ≤ WithZero.exp (-m) * WithZero.exp m :=
          mul_le_mul' le_rfl (show Valued.v x ≤ WithZero.exp m from hx)
      _ = WithZero.exp 0 := by rw [← WithZero.exp_add, neg_add_cancel]
  · rintro ⟨y, hy, rfl⟩
    show Valued.v (((uniformizerUnit ℚ v ^ (-m) : (v.adicCompletion ℚ)ˣ) : v.adicCompletion ℚ) * y) ≤
      WithZero.exp m
    rw [map_mul, hc]
    calc WithZero.exp m * Valued.v y ≤ WithZero.exp m * WithZero.exp 0 :=
          mul_le_mul' le_rfl (show Valued.v y ≤ WithZero.exp 0 from hy)
      _ = WithZero.exp m := by rw [WithZero.exp_zero, mul_one]

private theorem adicBall_measure_ne_top (m : ℤ) :
    letI := localBorel ℚ v
    selfDualHaarAt ℚ v (adicBall v m) ≠ ⊤ := by
  letI := localBorel ℚ v
  haveI : BorelSpace (v.adicCompletion ℚ) := borelSpace_localBorel ℚ v
  haveI : (selfDualHaarAt ℚ v).IsAddHaarMeasure := isAddHaarMeasure_selfDualHaarAt_rat v
  rw [adicBall_eq_image v m]
  exact ((isCompact_adicBall_zero v).image (continuous_const_mul _)).measure_lt_top.ne

end Balls
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_laurent_localZeta_eq_gl3LFactorPoly_of_sphericalData.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_exists_laurent_localZeta_eq_gl3LFactorPoly_of_sphericalData.LanglandsTunnell.CubicInduction"

end LanglandsTunnell.CubicInduction
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_laurent_localZeta_eq_gl3LFactorPoly_of_sphericalData.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_exists_laurent_localZeta_eq_gl3LFactorPoly_of_sphericalData.LanglandsTunnell.CubicInduction"
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_laurent_localZeta_eq_gl3LFactorPoly_of_sphericalData.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_exists_laurent_localZeta_eq_gl3LFactorPoly_of_sphericalData.LanglandsTunnell.CubicInduction"

end
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_laurent_localZeta_eq_gl3LFactorPoly_of_sphericalData.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_exists_laurent_localZeta_eq_gl3LFactorPoly_of_sphericalData.LanglandsTunnell.CubicInduction"
end
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_laurent_localZeta_eq_gl3LFactorPoly_of_sphericalData.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_exists_laurent_localZeta_eq_gl3LFactorPoly_of_sphericalData.LanglandsTunnell.CubicInduction"

section

set_option autoImplicit false

open IsDedekindDomain NumberField NumberField.TateGlobal AutomorphicForm LanglandsTunnell.Converse LanglandsTunnell.RankinSelberg LanglandsTunnell.TateLocal MeasureTheory

p2m_open "IsDedekindDomain.HeightOneSpectrum~Extension LanglandsTunnell.CubicInduction P2MW.S_LanglandsTunnell_CubicInduction_exists_laurent_localZeta_eq_gl3LFactorPoly_of_sphericalData.LanglandsTunnell.CubicInduction NumberField.StandardAddChar"

section Group

variable {G : Type*} [Group G]

private theorem apply_zpow_mul_of_apply_mul (z : G) (W : G → ℂ) (lam : ℂ) (hlam : lam ≠ 0)
    (hz : ∀ h : G, W (z * h) = lam * W h) (n : ℤ) (h : G) : W (z ^ n * h) = lam ^ n * W h := by
  have hpow : ∀ (m : ℕ) (h : G), W (z ^ m * h) = lam ^ m * W h := by
    intro m
    induction m with
    | zero => intro h; simp
    | succ m ih =>
      intro h
      rw [pow_succ, mul_assoc, ih, hz, pow_succ]
      ring
  have hinv : ∀ (m : ℕ) (h : G), W (z⁻¹ ^ m * h) = lam⁻¹ ^ m * W h := by
    intro m h
    have h1 := hpow m (z⁻¹ ^ m * h)
    rw [inv_pow, mul_inv_cancel_left] at h1
    rw [inv_pow, inv_pow, h1, inv_mul_cancel_left₀ (pow_ne_zero m hlam)]
  rcases n with m | m
  · simpa using hpow m h
  · rw [zpow_negSucc, zpow_negSucc, ← inv_pow, hinv, inv_pow]

private theorem dualWhittakerFn3_mul_transposeInv3 {B : Type*} [CommRing B] (W : GL (Fin 3) B → ℂ) (k : GL (Fin 3) B)
    (hk : ∀ h : GL (Fin 3) B, W (h * k) = W h) (h : GL (Fin 3) B) :
    dualWhittakerFn3 W (h * transposeInv3 k) = dualWhittakerFn3 W h := by
  rw [dualWhittakerFn3_apply, dualWhittakerFn3_apply, transposeInv3_mul, transposeInv3_transposeInv3, ←
      mul_assoc, hk]

end Group
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_laurent_localZeta_eq_gl3LFactorPoly_of_sphericalData.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_exists_laurent_localZeta_eq_gl3LFactorPoly_of_sphericalData.LanglandsTunnell.CubicInduction"

section Diagonal

variable {n : Type} [Fintype n] [DecidableEq n] {F : Type} [Field F]

private theorem coe_mul_of_coe_eq_diagonal (g₁ g₂ : GL n F) (w₁ w₂ : n → F) (h₁ : (g₁ : Matrix n n F) = Matrix.diagonal
    w₁)
    (h₂ : (g₂ : Matrix n n F) = Matrix.diagonal w₂) :
    ((g₁ * g₂ : GL n F) : Matrix n n F) = Matrix.diagonal fun i => w₁ i * w₂ i := by
  rw [Units.val_mul, h₁, h₂, Matrix.diagonal_mul_diagonal]

private theorem coe_zpow_of_coe_eq_diagonal (c : GL n F) (z : F) (hz : z ≠ 0)
    (hc : (c : Matrix n n F) = Matrix.diagonal fun _ => z) (m : ℤ) :
    ((c ^ m : GL n F) : Matrix n n F) = Matrix.diagonal fun _ => z ^ m := by
  have hnat : ∀ k : ℕ, ((c ^ k : GL n F) : Matrix n n F) = Matrix.diagonal fun _ => z ^ k := by
    intro k
    rw [Units.val_pow_eq_pow_val, hc, Matrix.diagonal_pow]
    rfl
  rcases m with k | k
  · simp only [Int.ofNat_eq_natCast, zpow_natCast]
    exact hnat k
  · rw [zpow_negSucc, coe_inv_of_coe_eq_diagonal (c ^ (k + 1)) _ (hnat (k + 1)) fun _ => pow_ne_zero _ hz]
    simp [zpow_negSucc]

private theorem ne_zero_of_coe_eq_diagonal (t : GL n F) (d : n → F) (ht : (t : Matrix n n F) = Matrix.diagonal d) (i :
    n) :
    d i ≠ 0 := by
  have h := congrFun (congrFun (Units.mul_inv t) i) i
  rw [ht, Matrix.diagonal_mul, Matrix.one_apply_eq] at h
  exact left_ne_zero_of_mul_eq_one h

end Diagonal
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_laurent_localZeta_eq_gl3LFactorPoly_of_sphericalData.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_exists_laurent_localZeta_eq_gl3LFactorPoly_of_sphericalData.LanglandsTunnell.CubicInduction"

section Valuation

variable {K : Type} [Field K] [Valued K (WithZero (Multiplicative ℤ))]

private theorem exists_valued_inv_zpow_mul_eq_one (ϖ : K) (hϖ : Valued.v ϖ = WithZero.exp (-1 : ℤ)) {d : K} (hd : d ≠
    0) :
    ∃ m : ℤ, Valued.v ((ϖ ^ m)⁻¹ * d) = 1 := by
  have hvd : Valued.v d ≠ 0 := (Valuation.ne_zero_iff _).2 hd
  refine ⟨-WithZero.log (Valued.v d), ?_⟩
  rw [Valuation.map_mul, map_inv₀, map_zpow₀, hϖ, ← WithZero.exp_zsmul, smul_neg, smul_eq_mul, mul_one,
      neg_neg,
    WithZero.exp_log hvd, inv_mul_cancel₀ hvd]

private theorem exists_valued_inv_zpow_mul_zpow_mul_eq_one (ϖ p : K) (hϖ : Valued.v ϖ = WithZero.exp (-1 : ℤ))
    (hp : Valued.v p = Valued.v ϖ) (m : ℤ) {d : K} (hd : d ≠ 0) : ∃ k : ℤ, Valued.v ((ϖ ^ m * p ^ k)⁻¹ * d) = 1
        := by
  have hvd : Valued.v d ≠ 0 := (Valuation.ne_zero_iff _).2 hd
  refine ⟨-WithZero.log (Valued.v d) - m, ?_⟩
  rw [Valuation.map_mul, map_inv₀, Valuation.map_mul, map_zpow₀, map_zpow₀, hp, hϖ, ← WithZero.exp_zsmul,
    ← WithZero.exp_zsmul, ← WithZero.exp_add, smul_neg, smul_neg, smul_eq_mul, smul_eq_mul, mul_one, mul_one,
    show -m + -(-WithZero.log (Valued.v d) - m) = WithZero.log (Valued.v d) by ring, WithZero.exp_log hvd,
    inv_mul_cancel₀ hvd]

end Valuation
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_laurent_localZeta_eq_gl3LFactorPoly_of_sphericalData.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_exists_laurent_localZeta_eq_gl3LFactorPoly_of_sphericalData.LanglandsTunnell.CubicInduction"

section Conjugation

variable {A : Type*} [CommRing A]

private theorem iotaGL_diagUnitGL2_mul_iotaGL_diagUnitGL2 (a c : Aˣ) :
    (iotaGL (diagUnitGL2 a) : GL (Fin 3) A) * iotaGL (diagUnitGL2 c) = iotaGL (diagUnitGL2 (a * c)) := by
  rw [← diagHom_apply, ← diagHom_apply, ← diagHom_apply, ← map_mul iotaGL, ← map_mul diagHom]

private theorem transposeInv3_iotaGL_diagUnitGL2_eq_inv (c : Aˣ) :
    transposeInv3 (iotaGL (diagUnitGL2 c) : GL (Fin 3) A) = iotaGL (diagUnitGL2 c⁻¹) := by
  refine Units.ext ?_
  rw [coe_transposeInv3, ← map_inv iotaGL, ← diagHom_apply, ← map_inv diagHom, diagHom_apply, coe_iotaGL,
    coe_diagUnitGL2]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [embedMat2, Matrix.transpose_apply]

private theorem iotaGL_diagUnitGL2_mul_upperUnipotent3 (a : Aˣ) (y z : A) :
    (iotaGL (diagUnitGL2 a) : GL (Fin 3) A) * upperUnipotent3 0 y z =
      upperUnipotent3 0 y ((a : A) * z) * iotaGL (diagUnitGL2 a) := by
  refine Units.ext ?_
  rw [Units.val_mul, Units.val_mul, coe_iotaGL, coe_diagUnitGL2, upperUnipotent3_coe, upperUnipotent3_coe]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [embedMat2, Matrix.mul_apply, Fin.sum_univ_three]

private theorem weylPrime3_mul_iotaGL_diagUnitGL2 (c : Aˣ) :
    (weylPrime3 : GL (Fin 3) A) * iotaGL (diagUnitGL2 c) = iotaGL (diagUnitGL2 c) * weylPrime3 := by
  refine Units.ext ?_
  rw [Units.val_mul, Units.val_mul, coe_iotaGL, coe_diagUnitGL2, weylPrime3_coe]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [embedMat2, Matrix.mul_apply, Fin.sum_univ_three]

private theorem lowerUnipotent21_mul_iotaGL_diagUnitGL2 (x : A) (d : Aˣ) :
    (lowerUnipotent21 x : GL (Fin 3) A) * iotaGL (diagUnitGL2 d) =
      iotaGL (diagUnitGL2 d) * lowerUnipotent21 (x * d) := by
  refine Units.ext ?_
  rw [Units.val_mul, Units.val_mul, coe_iotaGL, coe_diagUnitGL2, lowerUnipotent21_coe, lowerUnipotent21_coe]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [embedMat2, Matrix.mul_apply, Fin.sum_univ_three, mul_comm]

private theorem weylPrime3_mul_transposeInv3_upperUnipotent3 (y z : A) :
    (weylPrime3 : GL (Fin 3) A) * transposeInv3 (upperUnipotent3 0 y z) =
      lowerUnipotent21 (-z) * upperUnipotent3 0 (-y) 0 * weylPrime3 := by
  have hinv : (((upperUnipotent3 0 y z : GL (Fin 3) A)⁻¹ : GL (Fin 3) A) : Matrix (Fin 3) (Fin 3) A) =
      !![1, 0, -z; 0, 1, -y; 0, 0, 1] := by
    rw [Matrix.coe_units_inv, upperUnipotent3_coe]
    refine Matrix.inv_eq_left_inv ?_
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three]
  refine Units.ext ?_
  rw [Units.val_mul, Units.val_mul, Units.val_mul, coe_transposeInv3, hinv, weylPrime3_coe,
      lowerUnipotent21_coe,
    upperUnipotent3_coe]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three, Matrix.transpose_apply]

private theorem lowerUnipotent21_mul_lowerUnipotent21 (x x' : A) :
    (lowerUnipotent21 x : GL (Fin 3) A) * lowerUnipotent21 x' = lowerUnipotent21 (x + x') := by
  refine Units.ext ?_
  rw [Units.val_mul, lowerUnipotent21_coe, lowerUnipotent21_coe, lowerUnipotent21_coe]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three, add_comm]

private theorem lowerUnipotent21_mul_upperUnipotent3 (x y : A) :
    (lowerUnipotent21 x : GL (Fin 3) A) * upperUnipotent3 0 y 0 = upperUnipotent3 0 y 0 * lowerUnipotent21 x :=
        by
  refine Units.ext ?_
  rw [Units.val_mul, Units.val_mul, lowerUnipotent21_coe, upperUnipotent3_coe]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three]

private theorem upperUnipotent3_mul_iotaGL_diagUnitGL2 (x y z : A) (c : Aˣ) :
    (upperUnipotent3 x y z : GL (Fin 3) A) * iotaGL (diagUnitGL2 c) =
      iotaGL (diagUnitGL2 c) * upperUnipotent3 (((c⁻¹ : Aˣ) : A) * x) y (((c⁻¹ : Aˣ) : A) * z) := by
  refine Units.ext ?_
  rw [Units.val_mul, Units.val_mul, coe_iotaGL, coe_diagUnitGL2, upperUnipotent3_coe, upperUnipotent3_coe]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [embedMat2, Matrix.mul_apply, Fin.sum_univ_three]

private theorem upperUnipotent3_eq_mul (x y z : A) :
    (upperUnipotent3 x y z : GL (Fin 3) A) = upperUnipotent3 0 y z * upperUnipotent3 x 0 0 := by
  refine Units.ext ?_
  rw [Units.val_mul, upperUnipotent3_coe, upperUnipotent3_coe, upperUnipotent3_coe]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three]

private theorem upperUnipotent3_mul_iotaGL_diagUnits2 (x : A) (t : Aˣ) :
    (upperUnipotent3 x 0 0 : GL (Fin 3) A) * iotaGL (diagUnits2 1 t) =
      iotaGL (diagUnits2 1 t) * upperUnipotent3 (x * t) 0 0 := by
  refine Units.ext ?_
  rw [Units.val_mul, Units.val_mul, coe_iotaGL, coe_diagUnits2, upperUnipotent3_coe, upperUnipotent3_coe]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [embedMat2, Matrix.mul_apply, Fin.sum_univ_three]

private theorem coe_iotaGL_diagUnitGL2_eq_diagonal (c : Aˣ) :
    ((iotaGL (diagUnitGL2 c) : GL (Fin 3) A) : Matrix (Fin 3) (Fin 3) A) = Matrix.diagonal ![(c : A), 1, 1] :=
        by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [embedMat2]

private theorem coe_iotaGL_diagUnits2_one_eq_diagonal (t : Aˣ) :
    ((iotaGL (diagUnits2 1 t) : GL (Fin 3) A) : Matrix (Fin 3) (Fin 3) A) = Matrix.diagonal ![1, (t : A), 1] :=
        by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [embedMat2]

end Conjugation
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_laurent_localZeta_eq_gl3LFactorPoly_of_sphericalData.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_exists_laurent_localZeta_eq_gl3LFactorPoly_of_sphericalData.LanglandsTunnell.CubicInduction"

section DualCentral

variable {F : Type} [Field F]

private theorem transposeInv3_zpow_of_coe_eq_diagonal (c : GL (Fin 3) F) (z : F) (hz : z ≠ 0)
    (hc : (c : Matrix (Fin 3) (Fin 3) F) = Matrix.diagonal fun _ => z) (m : ℤ) :
    transposeInv3 (c ^ m) = c ^ (-m) := by
  refine Units.ext ?_
  rw [coe_transposeInv3, coe_inv_of_coe_eq_diagonal (c ^ m) _ (coe_zpow_of_coe_eq_diagonal c z hz hc m)
    (fun _ => zpow_ne_zero m hz), Matrix.diagonal_transpose, coe_zpow_of_coe_eq_diagonal c z hz hc (-m)]
  simp only [zpow_neg]

private theorem dualWhittakerFn3_apply_mul_of_central (c : GL (Fin 3) F) (z : F) (hz : z ≠ 0)
    (hc : (c : Matrix (Fin 3) (Fin 3) F) = Matrix.diagonal fun _ => z) (hcen : ∀ h : GL (Fin 3) F, c * h = h *
        c)
    (W : GL (Fin 3) F → ℂ) (lam : ℂ) (hlam : lam ≠ 0) (hW : ∀ h, W (c * h) = lam * W h) (h : GL (Fin 3) F) :
    dualWhittakerFn3 W (c * h) = lam⁻¹ * dualWhittakerFn3 W h := by
  have hT : transposeInv3 c = c⁻¹ := by
    simpa using transposeInv3_zpow_of_coe_eq_diagonal c z hz hc 1
  have hlaw := apply_zpow_mul_of_apply_mul c W lam hlam hW (-1) (longWeyl3 * transposeInv3 h)
  rw [zpow_neg_one, zpow_neg_one] at hlaw
  have hcm : Commute c⁻¹ (longWeyl3 : GL (Fin 3) F) := (show Commute c longWeyl3 from hcen _).inv_left
  rw [dualWhittakerFn3_apply, dualWhittakerFn3_apply, transposeInv3_mul, hT, ← mul_assoc, ← hcm.eq, mul_assoc,
      hlaw]

private theorem weylPrime3_mul_transposeInv3_zpow_mul (c : GL (Fin 3) F) (z : F) (hz : z ≠ 0)
    (hc : (c : Matrix (Fin 3) (Fin 3) F) = Matrix.diagonal fun _ => z) (hcen : ∀ h : GL (Fin 3) F, c * h = h *
        c)
    (m : ℤ) (g : GL (Fin 3) F) :
    (weylPrime3 : GL (Fin 3) F) * transposeInv3 (c ^ m * g) = c ^ (-m) * (weylPrime3 * transposeInv3 g) := by
  have hcm : Commute (c ^ (-m)) (weylPrime3 : GL (Fin 3) F) := ((show Commute c weylPrime3 from hcen
      _).zpow_left (-m))
  rw [transposeInv3_mul, transposeInv3_zpow_of_coe_eq_diagonal c z hz hc, ← mul_assoc, ← hcm.eq, mul_assoc]

private theorem mul_zpow_mul_of_central (c : GL (Fin 3) F) (hcen : ∀ h : GL (Fin 3) F, c * h = h * c) (n : ℤ)
    (x h : GL (Fin 3) F) : x * (c ^ n * h) = c ^ n * (x * h) := by
  have hcm : Commute (c ^ n) x := ((show Commute c x from hcen _).zpow_left n)
  rw [← mul_assoc, ← hcm.eq, mul_assoc]

end DualCentral
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_laurent_localZeta_eq_gl3LFactorPoly_of_sphericalData.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_exists_laurent_localZeta_eq_gl3LFactorPoly_of_sphericalData.LanglandsTunnell.CubicInduction"

section Transport

open MeasureTheory

variable {α : Type*} [MeasurableSpace α] {β : Type*} [MeasurableSpace β]

private theorem integrable_const_mul_iff_of_ne_zero (μ : Measure α) (F : α → ℂ) {r : ℂ} (hr : r ≠ 0) :
    Integrable (fun a => r * F a) μ ↔ Integrable F μ := by
  refine ⟨fun h => ?_, fun h => h.const_mul r⟩
  have h' := h.const_mul r⁻¹
  simpa [inv_mul_cancel_left₀ hr] using h'

private theorem integral_comp_of_map_eq (μ : Measure α) (e : α ≃ᵐ α) (he : Measure.map e μ = μ) (G : α → ℂ) :
    ∫ a, G (e a) ∂μ = ∫ a, G a ∂μ :=
  (MeasurePreserving.integral_comp' (⟨e.measurable, he⟩ : MeasurePreserving e μ μ) G)

private theorem integrable_comp_iff_of_map_eq (μ : Measure α) (e : α ≃ᵐ α) (he : Measure.map e μ = μ) (G : α → ℂ) :
    Integrable (fun a => G (e a)) μ ↔ Integrable G μ :=
  (⟨e.measurable, he⟩ : MeasurePreserving e μ μ).integrable_comp_emb e.measurableEmbedding

private theorem integral_comp_of_map_eq_smul (ν : Measure β) (e : β ≃ᵐ β) {r : ENNReal} (he : Measure.map e ν = r • ν)
    (G : β → ℂ) : ∫ x, G (e x) ∂ν = (r.toReal : ℂ) * ∫ x, G x ∂ν := by
  rw [MeasurePreserving.integral_comp' (⟨e.measurable, he⟩ : MeasurePreserving e ν (r • ν)) G,
      integral_smul_measure]
  exact Complex.real_smul

private theorem integrable_comp_prod_iff (μ : Measure α) (ν : Measure β) [SigmaFinite μ] [SigmaFinite ν] (eα : α ≃ᵐ α)
    (hα : Measure.map eα μ = μ) (eβ : β ≃ᵐ β) {r : ENNReal} (hr0 : r ≠ 0) (hrt : r ≠ ⊤)
    (hβ : Measure.map eβ ν = r • ν) (G : α × β → ℂ) :
    Integrable (fun p : α × β => G (eα p.1, eβ p.2)) (μ.prod ν) ↔ Integrable G (μ.prod ν) := by
  have hP : MeasurePreserving (Prod.map eα eβ) (μ.prod ν) (μ.prod (r • ν)) :=
    (⟨eα.measurable, hα⟩ : MeasurePreserving eα μ μ).prod (⟨eβ.measurable, hβ⟩ : MeasurePreserving eβ ν (r •
        ν))
  have h : Integrable (G ∘ Prod.map eα eβ) (μ.prod ν) ↔ Integrable G (μ.prod (r • ν)) :=
    hP.integrable_comp_emb (eα.prodCongr eβ).measurableEmbedding
  rw [Measure.prod_smul_right, integrable_smul_measure hr0 hrt] at h
  exact h

private noncomputable def mulLeftEquiv₀ {K : Type*} [GroupWithZero K] [TopologicalSpace K] [ContinuousMul K]
    [MeasurableSpace K] [BorelSpace K] (a : K) (ha : a ≠ 0) : K ≃ᵐ K where
  toEquiv := Equiv.mulLeft₀ a ha
  measurable_toFun := by
    show Measurable fun x : K => a * x
    exact (continuous_const.mul continuous_id).measurable
  measurable_invFun := by
    show Measurable fun x : K => a⁻¹ * x
    exact (continuous_const.mul continuous_id).measurable

private theorem mulLeftEquiv₀_apply {K : Type*} [GroupWithZero K] [TopologicalSpace K] [ContinuousMul K]
    [MeasurableSpace K]
    [BorelSpace K] (a : K) (ha : a ≠ 0) (x : K) : mulLeftEquiv₀ a ha x = a * x := rfl

private def addLeftEquiv {K : Type*} [AddGroup K] [TopologicalSpace K] [ContinuousAdd K] [MeasurableSpace K]
    [BorelSpace K]
    (z : K) : K ≃ᵐ K where
  toEquiv := Equiv.addLeft z
  measurable_toFun := by
    show Measurable fun x : K => z + x
    exact (continuous_const.add continuous_id).measurable
  measurable_invFun := by
    show Measurable fun x : K => -z + x
    exact (continuous_const.add continuous_id).measurable

private theorem addLeftEquiv_apply {K : Type*} [AddGroup K] [TopologicalSpace K] [ContinuousAdd K] [MeasurableSpace K]
    [BorelSpace K] (z x : K) : addLeftEquiv z x = z + x := rfl

private theorem map_addLeftEquiv {K : Type*} [AddGroup K] [TopologicalSpace K] [ContinuousAdd K] [MeasurableSpace K]
    [BorelSpace K] (ν : Measure K) [ν.IsAddLeftInvariant] (z : K) : Measure.map (addLeftEquiv z) ν = ν := by
  show Measure.map (fun x : K => z + x) ν = ν
  exact Measure.IsAddLeftInvariant.map_add_left_eq_self z

private theorem measurable_units_mul_left {M : Type*} [Monoid M] [MeasurableSpace M] (c : Mˣ)
    (hc : Measurable fun x : M => (c : M) * x) : Measurable fun α : Mˣ => c * α := by
  refine measurable_iff_comap_le.2 ?_
  change MeasurableSpace.comap (fun α : Mˣ => c * α) (MeasurableSpace.comap Units.val ‹MeasurableSpace M›) ≤
    MeasurableSpace.comap Units.val ‹MeasurableSpace M›
  rw [MeasurableSpace.comap_comp, show (Units.val ∘ fun α : Mˣ => c * α) = (fun x : M => (c : M) * x) ∘
      Units.val from
    funext fun α => Units.val_mul c α, ← MeasurableSpace.comap_comp]
  exact MeasurableSpace.comap_mono hc.comap_le

private def unitsMulLeftEquiv {M : Type*} [Monoid M] [MeasurableSpace M] (c : Mˣ)
    (hc : ∀ d : Mˣ, Measurable fun x : M => (d : M) * x) : Mˣ ≃ᵐ Mˣ where
  toEquiv := Equiv.mulLeft c
  measurable_toFun := by
    show Measurable fun α : Mˣ => c * α
    exact measurable_units_mul_left c (hc c)
  measurable_invFun := by
    show Measurable fun α : Mˣ => c⁻¹ * α
    exact measurable_units_mul_left c⁻¹ (hc c⁻¹)

private theorem unitsMulLeftEquiv_apply {M : Type*} [Monoid M] [MeasurableSpace M] (c : Mˣ)
    (hc : ∀ d : Mˣ, Measurable fun x : M => (d : M) * x) (α : Mˣ) : unitsMulLeftEquiv c hc α = c * α := rfl

end Transport
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_laurent_localZeta_eq_gl3LFactorPoly_of_sphericalData.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_exists_laurent_localZeta_eq_gl3LFactorPoly_of_sphericalData.LanglandsTunnell.CubicInduction"

section Cpow

private theorem ofReal_cpow_one_sub_mul_cpow_sub_one {x : ℝ} (hx : 0 < x) (s : ℂ) :
    ((x : ℂ) ^ (1 - s)) * (x : ℂ) ^ (s - 1) = 1 := by
  rw [← Complex.cpow_add _ _ (Complex.ofReal_ne_zero.2 hx.ne'), show 1 - s + (s - 1) = 0 by ring,
      Complex.cpow_zero]

private theorem ofReal_mul_cpow_sub_one {x : ℝ} (hx : 0 < x) (w : ℂ) : (x : ℂ) * (x : ℂ) ^ (w - 1) = (x : ℂ) ^ w := by
  conv_rhs => rw [show w = 1 + (w - 1) by ring]
  rw [Complex.cpow_add _ _ (Complex.ofReal_ne_zero.2 hx.ne'), Complex.cpow_one]

private theorem ofReal_mul_cpow {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) (s : ℂ) :
    (((x * y : ℝ) : ℂ)) ^ s = (x : ℂ) ^ s * (y : ℂ) ^ s := by
  rw [Complex.ofReal_mul]
  exact Complex.mul_cpow_ofReal_nonneg hx hy s

private theorem factor_identity_direct (W' χa : ℂ) {χc : ℂ} (hχc : χc ≠ 0) {mc : ℝ} (hmc : 0 < mc) (ma : ℝ) (s : ℂ) :
    W' * χa * (ma : ℂ) ^ (s - 1) =
      χc⁻¹ * (mc : ℂ) ^ (1 - s) * (W' * (χc * χa) * ((mc : ℂ) ^ (s - 1) * (ma : ℂ) ^ (s - 1))) := by
  have h1 := ofReal_cpow_one_sub_mul_cpow_sub_one hmc s
  have h2 : χc⁻¹ * χc = 1 := inv_mul_cancel₀ hχc
  linear_combination (-(W' * χa * (ma : ℂ) ^ (s - 1) * (χc⁻¹ * χc))) * h1 + (-(W' * χa * (ma : ℂ) ^ (s - 1))) *
      h2

end Cpow
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_laurent_localZeta_eq_gl3LFactorPoly_of_sphericalData.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_exists_laurent_localZeta_eq_gl3LFactorPoly_of_sphericalData.LanglandsTunnell.CubicInduction"

section NormalForm

variable {F : Type} [Field F]

private theorem normal_form_reassembly (Z : GL (Fin 3) F) (hZ : ∀ h : GL (Fin 3) F, Z * h = h * Z) (m : ℤ) (c t : Fˣ)
    (x y z : F) (e k g : GL (Fin 3) F)
    (hg : g = upperUnipotent3 x y z * (Z ^ m * iotaGL (diagUnitGL2 c) * iotaGL (diagUnits2 1 t) * e) * k) :
    g = Z ^ m * iotaGL (diagUnitGL2 c) * upperUnipotent3 0 y (((c⁻¹ : Fˣ) : F) * z) *
        (iotaGL (diagUnits2 1 t) * upperUnipotent3 (((c⁻¹ : Fˣ) : F) * x * t) 0 0) * (e * k) := by
  have hc : Commute Z (upperUnipotent3 x y z) := hZ _
  have hcomm : upperUnipotent3 x y z * Z ^ m = Z ^ m * upperUnipotent3 x y z := (hc.zpow_left m).eq.symm
  rw [hg]
  simp only [mul_assoc]
  rw [← mul_assoc (upperUnipotent3 x y z), hcomm, mul_assoc, ← mul_assoc (upperUnipotent3 x y z),
    upperUnipotent3_mul_iotaGL_diagUnitGL2, mul_assoc, upperUnipotent3_eq_mul (((c⁻¹ : Fˣ) : F) * x),
    mul_assoc, ← mul_assoc (upperUnipotent3 _ 0 0), upperUnipotent3_mul_iotaGL_diagUnits2]
  simp only [mul_assoc]

end NormalForm
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_laurent_localZeta_eq_gl3LFactorPoly_of_sphericalData.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_exists_laurent_localZeta_eq_gl3LFactorPoly_of_sphericalData.LanglandsTunnell.CubicInduction"

private theorem centralGen_central (v : HeightOneSpectrum (𝓞 ℚ)) (h : LocalGL3 v) :
    centralGen v * h = h * centralGen v :=
  centralGen_mul_eq_mul_centralGen v h

private theorem apply_centralGen_zpow_mul_of_forall (v : HeightOneSpectrum (𝓞 ℚ)) (W : LocalGL3 v → ℂ) (e₃ : ℂ)
    (he₃ : e₃ ≠ 0) (hZ : ∀ g : LocalGL3 v, W (centralGen v * g) = e₃ * W g) (m : ℤ) (g : LocalGL3 v) :
    W (centralGen v ^ m * g) = e₃ ^ m * W g :=
  apply_zpow_mul_of_apply_mul (centralGen v) W e₃ he₃ hZ m g

private theorem dualWhittakerFn3_centralGen_zpow_mul (v : HeightOneSpectrum (𝓞 ℚ)) (W : LocalGL3 v → ℂ) (e₃ : ℂ)
    (he₃ : e₃ ≠ 0) (hZ : ∀ g : LocalGL3 v, W (centralGen v * g) = e₃ * W g) (m : ℤ) (h : LocalGL3 v) :
    dualWhittakerFn3 W (centralGen v ^ m * h) = e₃⁻¹ ^ m * dualWhittakerFn3 W h :=
  apply_zpow_mul_of_apply_mul (centralGen v) (dualWhittakerFn3 W) e₃⁻¹ (inv_ne_zero he₃)
    (dualWhittakerFn3_apply_mul_of_central (centralGen v) (varpi v) (varpi_ne_zero v) (coe_centralGen_eq_diagonal v)
      (centralGen_central v) W e₃ he₃ hZ) m h

private theorem localZeta30_eq_and_convergent_iff_of_forall (v : HeightOneSpectrum (𝓞 ℚ))
    {mT : MeasurableSpace (v.adicCompletion ℚ)ˣ} (μ : Measure (v.adicCompletion ℚ)ˣ) (W : LocalGL3 v → ℂ)
    (χ : (v.adicCompletion ℚ)ˣ →* ℂˣ) (g₁ g₂ : LocalGL3 v) (r : ℂ) (hr : r ≠ 0)
    (h : ∀ a : (v.adicCompletion ℚ)ˣ, W (iotaGL (diagUnitGL2 a) * g₁) = r * W (iotaGL (diagUnitGL2 a) * g₂)) :
    (∀ s : ℂ, localZeta30 v μ W χ s g₁ = r * localZeta30 v μ W χ s g₂) ∧
      ∀ σ : ℝ, IsLocalZeta30ConvergentAbove v μ W χ g₁ σ ↔ IsLocalZeta30ConvergentAbove v μ W χ g₂ σ := by
  have hfun : ∀ s : ℂ,
      (fun a : (v.adicCompletion ℚ)ˣ => W (iotaGL (diagUnitGL2 a) * g₁) * ((χ a : ℂˣ) : ℂ) *
        ((modulus (a : v.adicCompletion ℚ) : ℝ) : ℂ) ^ (s - 1)) =
      fun a : (v.adicCompletion ℚ)ˣ => r * (W (iotaGL (diagUnitGL2 a) * g₂) * ((χ a : ℂˣ) : ℂ) *
        ((modulus (a : v.adicCompletion ℚ) : ℝ) : ℂ) ^ (s - 1)) := by
    intro s
    funext a
    rw [h a]
    ring
  refine ⟨fun s => ?_, fun σ => ?_⟩
  · unfold localZeta30
    rw [hfun s, integral_const_mul]
  · unfold IsLocalZeta30ConvergentAbove
    refine forall_congr' fun s => imp_congr_right fun _ => ?_
    rw [hfun s]
    exact integrable_const_mul_iff_of_ne_zero μ _ hr

private theorem localZeta31_eq_and_convergent_iff_of_forall (v : HeightOneSpectrum (𝓞 ℚ))
    {mT : MeasurableSpace (v.adicCompletion ℚ)ˣ} {mK : MeasurableSpace (v.adicCompletion ℚ)}
    (μ : Measure (v.adicCompletion ℚ)ˣ) (ν : Measure (v.adicCompletion ℚ)) (W : LocalGL3 v → ℂ)
    (χ : (v.adicCompletion ℚ)ˣ →* ℂˣ) (g₁ g₂ : LocalGL3 v) (r : ℂ) (hr : r ≠ 0)
    (h : ∀ (a : (v.adicCompletion ℚ)ˣ) (x : v.adicCompletion ℚ),
      W (iotaGL (diagUnitGL2 a) * lowerUnipotent21 x * g₁) = r * W (iotaGL (diagUnitGL2 a) * lowerUnipotent21 x * g₂))
          :
    (∀ w : ℂ, localZeta31 v μ ν W χ w g₁ = r * localZeta31 v μ ν W χ w g₂) ∧
      ∀ σ : ℝ, IsLocalZeta31ConvergentAbove v μ ν W χ g₁ σ ↔ IsLocalZeta31ConvergentAbove v μ ν W χ g₂ σ := by
  have hin : ∀ a : (v.adicCompletion ℚ)ˣ,
      (∫ x, W (iotaGL (diagUnitGL2 a) * lowerUnipotent21 x * g₁) ∂ν) =
        r * ∫ x, W (iotaGL (diagUnitGL2 a) * lowerUnipotent21 x * g₂) ∂ν := by
    intro a
    simp_rw [h a]
    exact integral_const_mul r _
  have hfun : ∀ w : ℂ,
      (fun p : (v.adicCompletion ℚ)ˣ × v.adicCompletion ℚ =>
        W (iotaGL (diagUnitGL2 p.1) * lowerUnipotent21 p.2 * g₁) * ((χ p.1 : ℂˣ) : ℂ) *
          ((modulus (p.1 : v.adicCompletion ℚ) : ℝ) : ℂ) ^ (w - 1)) =
      fun p : (v.adicCompletion ℚ)ˣ × v.adicCompletion ℚ =>
        r * (W (iotaGL (diagUnitGL2 p.1) * lowerUnipotent21 p.2 * g₂) * ((χ p.1 : ℂˣ) : ℂ) *
          ((modulus (p.1 : v.adicCompletion ℚ) : ℝ) : ℂ) ^ (w - 1)) := by
    intro w
    funext p
    rw [h p.1 p.2]
    ring
  refine ⟨fun w => ?_, fun σ => ?_⟩
  · unfold localZeta31
    simp_rw [hin, mul_assoc]
    rw [integral_const_mul]
  · unfold IsLocalZeta31ConvergentAbove
    refine forall_congr' fun w => imp_congr_right fun _ => ?_
    rw [hfun w]
    exact integrable_const_mul_iff_of_ne_zero _ _ hr

private theorem measurable_units_coe_mul (v : HeightOneSpectrum (𝓞 ℚ)) (d : (v.adicCompletion ℚ)ˣ) :
    letI := localBorel ℚ v
    Measurable fun x : v.adicCompletion ℚ => (d : v.adicCompletion ℚ) * x := by
  letI := localBorel ℚ v
  haveI : BorelSpace (v.adicCompletion ℚ) := ⟨rfl⟩
  exact (continuous_const.mul continuous_id).measurable

private theorem integral_units_comp_mul_left (v : HeightOneSpectrum (𝓞 ℚ)) (c : (v.adicCompletion ℚ)ˣ)
    (G : (v.adicCompletion ℚ)ˣ → ℂ) :
    letI := localBorel ℚ v
    ∫ a, G (c * a) ∂(Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ v))) =
      ∫ a, G a ∂(Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ v))) := by
  letI := localBorel ℚ v
  exact integral_comp_of_map_eq _ (unitsMulLeftEquiv c (measurable_units_coe_mul v)) (map_mul_left_unitsMeasure v c) G

private theorem integrable_units_comp_mul_left_iff (v : HeightOneSpectrum (𝓞 ℚ)) (c : (v.adicCompletion ℚ)ˣ)
    (G : (v.adicCompletion ℚ)ˣ → ℂ) :
    letI := localBorel ℚ v
    Integrable (fun a => G (c * a)) (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ v))) ↔
      Integrable G (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ v))) := by
  letI := localBorel ℚ v
  exact integrable_comp_iff_of_map_eq _ (unitsMulLeftEquiv c (measurable_units_coe_mul v))
    (map_mul_left_unitsMeasure v c) G

private theorem modulus_coe_inv (v : HeightOneSpectrum (𝓞 ℚ)) (c : (v.adicCompletion ℚ)ˣ) :
    modulus ((c⁻¹ : (v.adicCompletion ℚ)ˣ) : v.adicCompletion ℚ) = (modulus (c : v.adicCompletion ℚ))⁻¹ := by
  refine eq_inv_of_mul_eq_one_right ?_
  rw [← modulus_mul, Units.mul_inv, modulus_one]

private theorem map_coe_inv_mul_selfDualHaarAt (v : HeightOneSpectrum (𝓞 ℚ)) (c : (v.adicCompletion ℚ)ˣ) :
    letI := localBorel ℚ v
    Measure.map (fun x => ((c⁻¹ : (v.adicCompletion ℚ)ˣ) : v.adicCompletion ℚ) * x) (selfDualHaarAt ℚ v) =
      ((modulus (c : v.adicCompletion ℚ) : ENNReal)) • selfDualHaarAt ℚ v := by
  letI := localBorel ℚ v
  rw [map_mul_left_selfDualHaarAt v c⁻¹, modulus_coe_inv, ENNReal.coe_inv (modulus_ne_zero c.ne_zero), inv_inv]

private theorem integral_selfDual_comp_coe_inv_mul (v : HeightOneSpectrum (𝓞 ℚ)) (c : (v.adicCompletion ℚ)ˣ)
    (G : v.adicCompletion ℚ → ℂ) :
    letI := localBorel ℚ v
    ∫ x, G (((c⁻¹ : (v.adicCompletion ℚ)ˣ) : v.adicCompletion ℚ) * x) ∂(selfDualHaarAt ℚ v) =
      ((modulus (c : v.adicCompletion ℚ) : ℝ) : ℂ) * ∫ x, G x ∂(selfDualHaarAt ℚ v) := by
  letI := localBorel ℚ v
  haveI : BorelSpace (v.adicCompletion ℚ) := ⟨rfl⟩
  have h := integral_comp_of_map_eq_smul (selfDualHaarAt ℚ v)
    (mulLeftEquiv₀ ((c⁻¹ : (v.adicCompletion ℚ)ˣ) : v.adicCompletion ℚ) c⁻¹.ne_zero)
    (map_coe_inv_mul_selfDualHaarAt v c) G
  rw [ENNReal.coe_toReal] at h
  exact h

private theorem integrable_prod_comp_inv_mul_iff (v : HeightOneSpectrum (𝓞 ℚ)) (c : (v.adicCompletion ℚ)ˣ)
    (G : (v.adicCompletion ℚ)ˣ × v.adicCompletion ℚ → ℂ) :
    letI := localBorel ℚ v
    Integrable (fun p : (v.adicCompletion ℚ)ˣ × v.adicCompletion ℚ =>
        G (c⁻¹ * p.1, ((c⁻¹ : (v.adicCompletion ℚ)ˣ) : v.adicCompletion ℚ) * p.2))
      ((Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ v))).prod (selfDualHaarAt ℚ v)) ↔
      Integrable G ((Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ v))).prod (selfDualHaarAt ℚ v)) := by
  letI := localBorel ℚ v
  haveI : BorelSpace (v.adicCompletion ℚ) := ⟨rfl⟩
  haveI := sigmaFinite_comap_val_mulMeasure v
  haveI := sigmaFinite_selfDualHaarAt_rat v
  exact integrable_comp_prod_iff _ _ (unitsMulLeftEquiv c⁻¹ (measurable_units_coe_mul v)) (map_mul_left_unitsMeasure v
      c⁻¹)
    (mulLeftEquiv₀ ((c⁻¹ : (v.adicCompletion ℚ)ˣ) : v.adicCompletion ℚ) c⁻¹.ne_zero)
    (ENNReal.coe_ne_zero.2 (modulus_ne_zero c.ne_zero)) ENNReal.coe_ne_top (map_coe_inv_mul_selfDualHaarAt v c) G

private theorem integral_selfDual_comp_add_left (v : HeightOneSpectrum (𝓞 ℚ)) (z : v.adicCompletion ℚ)
    (G : v.adicCompletion ℚ → ℂ) :
    letI := localBorel ℚ v
    ∫ x, G (z + x) ∂(selfDualHaarAt ℚ v) = ∫ x, G x ∂(selfDualHaarAt ℚ v) := by
  letI := localBorel ℚ v
  haveI : BorelSpace (v.adicCompletion ℚ) := ⟨rfl⟩
  haveI := isAddHaarMeasure_selfDualHaarAt_rat v
  exact integral_comp_of_map_eq _ (addLeftEquiv z) (map_addLeftEquiv _ z) G

private theorem integrable_prod_comp_add_left_iff (v : HeightOneSpectrum (𝓞 ℚ)) (z : v.adicCompletion ℚ)
    (G : (v.adicCompletion ℚ)ˣ × v.adicCompletion ℚ → ℂ) :
    letI := localBorel ℚ v
    Integrable (fun p : (v.adicCompletion ℚ)ˣ × v.adicCompletion ℚ => G (p.1, z + p.2))
      ((Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ v))).prod (selfDualHaarAt ℚ v)) ↔
      Integrable G ((Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ v))).prod (selfDualHaarAt ℚ v)) := by
  letI := localBorel ℚ v
  haveI : BorelSpace (v.adicCompletion ℚ) := ⟨rfl⟩
  haveI := isAddHaarMeasure_selfDualHaarAt_rat v
  haveI := sigmaFinite_comap_val_mulMeasure v
  haveI := sigmaFinite_selfDualHaarAt_rat v
  have h := integrable_comp_prod_iff _ _ (unitsMulLeftEquiv 1 (measurable_units_coe_mul v)) (map_mul_left_unitsMeasure
      v 1)
    (addLeftEquiv z) one_ne_zero ENNReal.one_ne_top (by rw [one_smul]; exact map_addLeftEquiv (selfDualHaarAt ℚ v) z) G
  simpa only [unitsMulLeftEquiv_apply, addLeftEquiv_apply, one_mul] using h

private theorem psiLocal_apply_ne_zero (v : HeightOneSpectrum (𝓞 ℚ)) (y : v.adicCompletion ℚ) : psiLocal ℚ v y ≠ 0 :=
    by
  have h1 : psiLocal ℚ v y * psiLocal ℚ v (-y) = 1 := by
    rw [← AddChar.map_add_eq_mul, add_neg_cancel, AddChar.map_zero_eq_one]
  exact left_ne_zero_of_mul_eq_one h1

section ZetaTransformation

variable (v : HeightOneSpectrum (𝓞 ℚ)) (W : LocalGL3 v → ℂ) (χ : (v.adicCompletion ℚ)ˣ →* ℂˣ)

private theorem localZeta30_centralGen_zpow_mul (e₃ : ℂ) (he₃ : e₃ ≠ 0)
    (hW₃ : ∀ g : LocalGL3 v, W (centralGen v * g) = e₃ * W g) (m : ℤ) (g : LocalGL3 v) :
    letI := localBorel ℚ v
    (∀ s : ℂ, localZeta30 v (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ v))) W χ s
        (centralGen v ^ m * g) =
      e₃ ^ m * localZeta30 v (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ v))) W χ s g) ∧
    ∀ σ : ℝ, IsLocalZeta30ConvergentAbove v (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ v))) W χ
        (centralGen v ^ m * g) σ ↔
      IsLocalZeta30ConvergentAbove v (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ v))) W χ g σ := by
  letI := localBorel ℚ v
  have h : ∀ a : (v.adicCompletion ℚ)ˣ, W (iotaGL (diagUnitGL2 a) * (centralGen v ^ m * g)) =
      e₃ ^ m * W (iotaGL (diagUnitGL2 a) * g) := fun a => by
    rw [mul_zpow_mul_of_central (centralGen v) (centralGen_central v),
      apply_centralGen_zpow_mul_of_forall v W e₃ he₃ hW₃]
  exact localZeta30_eq_and_convergent_iff_of_forall v _ W χ _ g _ (zpow_ne_zero m he₃) h

private theorem localZetaDual31_centralGen_zpow_mul (e₃ : ℂ) (he₃ : e₃ ≠ 0)
    (hW₃ : ∀ g : LocalGL3 v, W (centralGen v * g) = e₃ * W g) (m : ℤ) (g : LocalGL3 v) :
    letI := localBorel ℚ v
    (∀ w : ℂ, localZetaDual31 v (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ v))) (selfDualHaarAt ℚ v)
        W χ w (centralGen v ^ m * g) =
      e₃ ^ m * localZetaDual31 v (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ v))) (selfDualHaarAt ℚ v)
        W χ w g) ∧
    ∀ σ : ℝ, IsLocalZeta31ConvergentAbove v (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ v)))
        (selfDualHaarAt ℚ v) (dualWhittakerFn3 W) χ⁻¹ (weylPrime3 * transposeInv3 (centralGen v ^ m * g)) σ ↔
      IsLocalZeta31ConvergentAbove v (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ v)))
        (selfDualHaarAt ℚ v) (dualWhittakerFn3 W) χ⁻¹ (weylPrime3 * transposeInv3 g) σ := by
  letI := localBorel ℚ v
  have h : ∀ (a : (v.adicCompletion ℚ)ˣ) (x : v.adicCompletion ℚ),
      dualWhittakerFn3 W (iotaGL (diagUnitGL2 a) * lowerUnipotent21 x *
          (weylPrime3 * transposeInv3 (centralGen v ^ m * g))) =
        e₃ ^ m * dualWhittakerFn3 W (iotaGL (diagUnitGL2 a) * lowerUnipotent21 x * (weylPrime3 * transposeInv3 g)) :=
            by
    intro a x
    rw [weylPrime3_mul_transposeInv3_zpow_mul (centralGen v) (varpi v) (varpi_ne_zero v) (coe_centralGen_eq_diagonal v)
      (centralGen_central v), mul_zpow_mul_of_central (centralGen v) (centralGen_central v),
      dualWhittakerFn3_centralGen_zpow_mul v W e₃ he₃ hW₃, zpow_neg, inv_zpow, inv_inv]
  obtain ⟨hval, hconv⟩ := localZeta31_eq_and_convergent_iff_of_forall v _ _ (dualWhittakerFn3 W) χ⁻¹ _ _ _
    (zpow_ne_zero m he₃) h
  exact ⟨fun w => hval w, hconv⟩

private theorem localZeta30_iotaGL_diagUnitGL2_mul (c : (v.adicCompletion ℚ)ˣ) (g : LocalGL3 v) :
    letI := localBorel ℚ v
    (∀ s : ℂ, localZeta30 v (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ v))) W χ s
        (iotaGL (diagUnitGL2 c) * g) =
      ((χ c : ℂˣ) : ℂ)⁻¹ * ((LanglandsTunnell.TateLocal.modulus (c : v.adicCompletion ℚ) : ℝ) : ℂ) ^ (1 - s) *
        localZeta30 v (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ v))) W χ s g) ∧
    ∀ σ : ℝ, IsLocalZeta30ConvergentAbove v (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ v))) W χ
        (iotaGL (diagUnitGL2 c) * g) σ ↔
      IsLocalZeta30ConvergentAbove v (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ v))) W χ g σ := by
  letI := localBorel ℚ v
  have hmc : (0 : ℝ) < (modulus (c : v.adicCompletion ℚ) : ℝ) := NNReal.coe_pos.2 (modulus_pos c.ne_zero)
  have hpt : ∀ a : (v.adicCompletion ℚ)ˣ, iotaGL (diagUnitGL2 a) * (iotaGL (diagUnitGL2 c) * g) = iotaGL (diagUnitGL2
      (c * a)) * g :=
    fun a => by rw [← mul_assoc, iotaGL_diagUnitGL2_mul_iotaGL_diagUnitGL2, mul_comm a c]
  have hχ : ∀ a : (v.adicCompletion ℚ)ˣ, ((χ (c * a) : ℂˣ) : ℂ) = ((χ c : ℂˣ) : ℂ) * ((χ a : ℂˣ) : ℂ) := fun a => by
    rw [map_mul, Units.val_mul]
  have hm : ∀ (a : (v.adicCompletion ℚ)ˣ) (s : ℂ), ((modulus ((c * a : (v.adicCompletion ℚ)ˣ) : v.adicCompletion ℚ) :
      ℝ) : ℂ) ^ (s - 1) =
      ((modulus (c : v.adicCompletion ℚ) : ℝ) : ℂ) ^ (s - 1) * ((modulus (a : v.adicCompletion ℚ) : ℝ) : ℂ) ^ (s - 1)
          := fun a s => by
    rw [Units.val_mul, modulus_mul, NNReal.coe_mul, ofReal_mul_cpow (NNReal.coe_nonneg _) (NNReal.coe_nonneg _)]
  have hF : ∀ s : ℂ, ((χ c : ℂˣ) : ℂ)⁻¹ * ((modulus (c : v.adicCompletion ℚ) : ℝ) : ℂ) ^ (1 - s) ≠ 0 := fun s =>
    mul_ne_zero (inv_ne_zero (χ c).ne_zero) (left_ne_zero_of_mul_eq_one (ofReal_cpow_one_sub_mul_cpow_sub_one hmc s))
  have hfun : ∀ s : ℂ,
      (fun a : (v.adicCompletion ℚ)ˣ => W (iotaGL (diagUnitGL2 a) * (iotaGL (diagUnitGL2 c) * g)) * ((χ a : ℂˣ) : ℂ) *
        ((modulus (a : v.adicCompletion ℚ) : ℝ) : ℂ) ^ (s - 1)) =
      fun a : (v.adicCompletion ℚ)ˣ => ((χ c : ℂˣ) : ℂ)⁻¹ * ((modulus (c : v.adicCompletion ℚ) : ℝ) : ℂ) ^ (1 - s) *
        (W (iotaGL (diagUnitGL2 (c * a)) * g) * ((χ (c * a) : ℂˣ) : ℂ) *
          ((modulus ((c * a : (v.adicCompletion ℚ)ˣ) : v.adicCompletion ℚ) : ℝ) : ℂ) ^ (s - 1)) := by
    intro s
    funext a
    rw [hpt a, hχ a, hm a s]
    exact factor_identity_direct _ _ (χ c).ne_zero hmc _ s
  refine ⟨fun s => ?_, fun σ => ?_⟩
  · unfold localZeta30
    rw [hfun s, integral_const_mul]
    congr 1
    exact integral_units_comp_mul_left v c (fun b => W (iotaGL (diagUnitGL2 b) * g) * ((χ b : ℂˣ) : ℂ) * ((modulus (b :
        v.adicCompletion ℚ) : ℝ) : ℂ) ^ (s - 1))
  · unfold IsLocalZeta30ConvergentAbove
    refine forall_congr' fun s => imp_congr_right fun _ => ?_
    rw [hfun s, integrable_const_mul_iff_of_ne_zero _ _ (hF s)]
    exact integrable_units_comp_mul_left_iff v c (fun b => W (iotaGL (diagUnitGL2 b) * g) * ((χ b : ℂˣ) : ℂ) *
        ((modulus (b : v.adicCompletion ℚ) : ℝ) : ℂ) ^ (s - 1))

private theorem localZetaDual31_iotaGL_diagUnitGL2_mul (c : (v.adicCompletion ℚ)ˣ) (g : LocalGL3 v) :
    letI := localBorel ℚ v
    (∀ w : ℂ, localZetaDual31 v (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ v))) (selfDualHaarAt ℚ v)
        W χ w (iotaGL (diagUnitGL2 c) * g) =
      ((χ c : ℂˣ) : ℂ)⁻¹ * ((LanglandsTunnell.TateLocal.modulus (c : v.adicCompletion ℚ) : ℝ) : ℂ) ^ w *
        localZetaDual31 v (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ v))) (selfDualHaarAt ℚ v)
          W χ w g) ∧
    ∀ σ : ℝ, IsLocalZeta31ConvergentAbove v (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ v)))
        (selfDualHaarAt ℚ v) (dualWhittakerFn3 W) χ⁻¹
        (weylPrime3 * transposeInv3 (iotaGL (diagUnitGL2 c) * g)) σ ↔
      IsLocalZeta31ConvergentAbove v (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ v)))
        (selfDualHaarAt ℚ v) (dualWhittakerFn3 W) χ⁻¹ (weylPrime3 * transposeInv3 g) σ := by
  letI := localBorel ℚ v
  have hmc : (0 : ℝ) < (modulus (c : v.adicCompletion ℚ) : ℝ) := NNReal.coe_pos.2 (modulus_pos c.ne_zero)
  have hpt : ∀ (a : (v.adicCompletion ℚ)ˣ) (x : v.adicCompletion ℚ),
      iotaGL (diagUnitGL2 a) * lowerUnipotent21 x * (weylPrime3 * transposeInv3 (iotaGL (diagUnitGL2 c) * g)) =
        iotaGL (diagUnitGL2 (c⁻¹ * a)) * lowerUnipotent21 (((c⁻¹ : (v.adicCompletion ℚ)ˣ) : v.adicCompletion ℚ) * x) *
          (weylPrime3 * transposeInv3 g) := by
    intro a x
    rw [transposeInv3_mul, transposeInv3_iotaGL_diagUnitGL2_eq_inv, ← mul_assoc weylPrime3,
        weylPrime3_mul_iotaGL_diagUnitGL2,
      mul_assoc (iotaGL (diagUnitGL2 c⁻¹)), ← mul_assoc (iotaGL (diagUnitGL2 a) * lowerUnipotent21 x),
      mul_assoc (iotaGL (diagUnitGL2 a)), lowerUnipotent21_mul_iotaGL_diagUnitGL2, ← mul_assoc (iotaGL (diagUnitGL2
          a)),
      iotaGL_diagUnitGL2_mul_iotaGL_diagUnitGL2, mul_comm a c⁻¹, mul_comm x]
  have hχ : ∀ a : (v.adicCompletion ℚ)ˣ, ((χ⁻¹ a : ℂˣ) : ℂ) = ((χ⁻¹ c : ℂˣ) : ℂ) * ((χ⁻¹ (c⁻¹ * a) : ℂˣ) : ℂ) := fun a
      => by
    rw [← Units.val_mul, ← map_mul, mul_inv_cancel_left]
  have hm : ∀ (a : (v.adicCompletion ℚ)ˣ) (w : ℂ), ((modulus (a : v.adicCompletion ℚ) : ℝ) : ℂ) ^ (w - 1) =
      ((modulus (c : v.adicCompletion ℚ) : ℝ) : ℂ) ^ (w - 1) * ((modulus ((c⁻¹ * a : (v.adicCompletion ℚ)ˣ) :
          v.adicCompletion ℚ) : ℝ) : ℂ) ^ (w - 1) := fun a w => by
    rw [← ofReal_mul_cpow (NNReal.coe_nonneg _) (NNReal.coe_nonneg _), ← NNReal.coe_mul, ← modulus_mul, ←
        Units.val_mul,
      mul_inv_cancel_left]
  have hχi : ((χ⁻¹ c : ℂˣ) : ℂ) = ((χ c : ℂˣ) : ℂ)⁻¹ := by rw [MonoidHom.inv_apply, Units.val_inv_eq_inv_val]
  refine ⟨fun w => ?_, fun σ => ?_⟩
  · unfold localZetaDual31 localZeta31
    have hin : ∀ a : (v.adicCompletion ℚ)ˣ,
        (∫ x : v.adicCompletion ℚ, dualWhittakerFn3 W (iotaGL (diagUnitGL2 (c⁻¹ * a)) * lowerUnipotent21 (((c⁻¹ :
            (v.adicCompletion ℚ)ˣ) : v.adicCompletion ℚ) * x) *
            (weylPrime3 * transposeInv3 g)) ∂(selfDualHaarAt ℚ v)) =
          ((modulus (c : v.adicCompletion ℚ) : ℝ) : ℂ) * ∫ x : v.adicCompletion ℚ, dualWhittakerFn3 W (iotaGL
              (diagUnitGL2 (c⁻¹ * a)) * lowerUnipotent21 x * (weylPrime3 * transposeInv3 g)) ∂(selfDualHaarAt ℚ v) :=
              fun a =>
      integral_selfDual_comp_coe_inv_mul v c (fun x =>
        dualWhittakerFn3 W (iotaGL (diagUnitGL2 (c⁻¹ * a)) * lowerUnipotent21 x * (weylPrime3 * transposeInv3 g)))
    have hout : (∫ a : (v.adicCompletion ℚ)ˣ, (∫ x : v.adicCompletion ℚ, dualWhittakerFn3 W (iotaGL (diagUnitGL2 a) *
        lowerUnipotent21 x * (weylPrime3 * transposeInv3 g)) ∂(selfDualHaarAt ℚ v)) * ((χ⁻¹ a : ℂˣ) : ℂ) * ((modulus (a
        : v.adicCompletion ℚ) : ℝ) : ℂ) ^ (w - 1) ∂(Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ v)))) =
        ∫ a : (v.adicCompletion ℚ)ˣ, (∫ x : v.adicCompletion ℚ, dualWhittakerFn3 W (iotaGL (diagUnitGL2 (c⁻¹ * a)) *
            lowerUnipotent21 x * (weylPrime3 * transposeInv3 g)) ∂(selfDualHaarAt ℚ v)) * ((χ⁻¹ (c⁻¹ * a) : ℂˣ) : ℂ) *
          ((modulus ((c⁻¹ * a : (v.adicCompletion ℚ)ˣ) : v.adicCompletion ℚ) : ℝ) : ℂ) ^ (w - 1) ∂(Measure.comap
              Units.val (mulMeasure (selfDualHaarAt ℚ v))) :=
      (integral_units_comp_mul_left v c⁻¹ (fun b =>
        (∫ x : v.adicCompletion ℚ, dualWhittakerFn3 W (iotaGL (diagUnitGL2 b) * lowerUnipotent21 x * (weylPrime3 *
            transposeInv3 g)) ∂(selfDualHaarAt ℚ v)) * ((χ⁻¹ b : ℂˣ) : ℂ) * ((modulus (b : v.adicCompletion ℚ) : ℝ) :
            ℂ) ^ (w - 1))).symm
    simp_rw [hpt, hin]
    rw [hout, ← integral_const_mul]
    congr 1
    funext a
    rw [hχ a, hm a w, hχi, ← ofReal_mul_cpow_sub_one hmc w]
    ring
  · unfold IsLocalZeta31ConvergentAbove
    refine forall_congr' fun w => imp_congr_right fun _ => ?_
    have hfun : (fun p : (v.adicCompletion ℚ)ˣ × v.adicCompletion ℚ =>
        dualWhittakerFn3 W (iotaGL (diagUnitGL2 p.1) * lowerUnipotent21 p.2 *
            (weylPrime3 * transposeInv3 (iotaGL (diagUnitGL2 c) * g))) *
          ((χ⁻¹ p.1 : ℂˣ) : ℂ) * ((modulus (p.1 : v.adicCompletion ℚ) : ℝ) : ℂ) ^ (w - 1)) =
        fun p : (v.adicCompletion ℚ)ˣ × v.adicCompletion ℚ => ((χ⁻¹ c : ℂˣ) : ℂ) * ((modulus (c : v.adicCompletion ℚ) :
            ℝ) : ℂ) ^ (w - 1) *
          (dualWhittakerFn3 W (iotaGL (diagUnitGL2 (c⁻¹ * p.1)) * lowerUnipotent21 (((c⁻¹ : (v.adicCompletion ℚ)ˣ) :
              v.adicCompletion ℚ) * p.2) *
              (weylPrime3 * transposeInv3 g)) *
            ((χ⁻¹ (c⁻¹ * p.1) : ℂˣ) : ℂ) * ((modulus ((c⁻¹ * p.1 : (v.adicCompletion ℚ)ˣ) : v.adicCompletion ℚ) : ℝ) :
                ℂ) ^ (w - 1)) := by
      funext p
      rw [hpt, hχ, hm]
      ring
    rw [hfun, integrable_const_mul_iff_of_ne_zero _ _ (mul_ne_zero (χ⁻¹ c).ne_zero
      (right_ne_zero_of_mul_eq_one (ofReal_cpow_one_sub_mul_cpow_sub_one hmc w)))]
    exact integrable_prod_comp_inv_mul_iff v c (fun q : (v.adicCompletion ℚ)ˣ × v.adicCompletion ℚ =>
      dualWhittakerFn3 W (iotaGL (diagUnitGL2 q.1) * lowerUnipotent21 q.2 * (weylPrime3 * transposeInv3 g)) *
        ((χ⁻¹ q.1 : ℂˣ) : ℂ) * ((modulus (q.1 : v.adicCompletion ℚ) : ℝ) : ℂ) ^ (w - 1))

private theorem localZeta30_upperUnipotent3_mul (hψ : IsGL3PsiWhittakerFn (psiLocal ℚ v) W) (y z : v.adicCompletion ℚ)
    (g : LocalGL3 v) :
    letI := localBorel ℚ v
    (∀ s : ℂ, localZeta30 v (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ v))) W χ s
        (upperUnipotent3 0 y z * g) =
      psiLocal ℚ v y * localZeta30 v (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ v))) W χ s g) ∧
    ∀ σ : ℝ, IsLocalZeta30ConvergentAbove v (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ v))) W χ
        (upperUnipotent3 0 y z * g) σ ↔
      IsLocalZeta30ConvergentAbove v (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ v))) W χ g σ := by
  letI := localBorel ℚ v
  have h : ∀ a : (v.adicCompletion ℚ)ˣ, W (iotaGL (diagUnitGL2 a) * (upperUnipotent3 0 y z * g)) =
      psiLocal ℚ v y * W (iotaGL (diagUnitGL2 a) * g) := fun a => by
    rw [← mul_assoc, iotaGL_diagUnitGL2_mul_upperUnipotent3, mul_assoc, hψ 0 y _ _, zero_add]
  exact localZeta30_eq_and_convergent_iff_of_forall v _ W χ _ g _ (psiLocal_apply_ne_zero v y) h

private theorem localZetaDual31_upperUnipotent3_mul (hψ : IsGL3PsiWhittakerFn (psiLocal ℚ v) W) (y z : v.adicCompletion ℚ)
    (g : LocalGL3 v) :
    letI := localBorel ℚ v
    (∀ w : ℂ, localZetaDual31 v (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ v))) (selfDualHaarAt ℚ v)
        W χ w (upperUnipotent3 0 y z * g) =
      psiLocal ℚ v y *
        localZetaDual31 v (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ v))) (selfDualHaarAt ℚ v)
          W χ w g) ∧
    ∀ σ : ℝ, IsLocalZeta31ConvergentAbove v (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ v)))
        (selfDualHaarAt ℚ v) (dualWhittakerFn3 W) χ⁻¹
        (weylPrime3 * transposeInv3 (upperUnipotent3 0 y z * g)) σ ↔
      IsLocalZeta31ConvergentAbove v (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ v)))
        (selfDualHaarAt ℚ v) (dualWhittakerFn3 W) χ⁻¹ (weylPrime3 * transposeInv3 g) σ := by
  letI := localBorel ℚ v
  have hdual : IsGL3PsiWhittakerFn (psiLocal ℚ v)⁻¹ (dualWhittakerFn3 W) :=
    isGL3PsiWhittakerFn_dualWhittakerFn3 _ W hψ
  have hpt : ∀ (a : (v.adicCompletion ℚ)ˣ) (x : v.adicCompletion ℚ),
      dualWhittakerFn3 W (iotaGL (diagUnitGL2 a) * lowerUnipotent21 x *
          (weylPrime3 * transposeInv3 (upperUnipotent3 0 y z * g))) =
        psiLocal ℚ v y *
          dualWhittakerFn3 W (iotaGL (diagUnitGL2 a) * lowerUnipotent21 (-z + x) * (weylPrime3 * transposeInv3 g)) :=
              by
    intro a x
    rw [transposeInv3_mul, ← mul_assoc weylPrime3, weylPrime3_mul_transposeInv3_upperUnipotent3]
    simp only [mul_assoc]
    rw [← mul_assoc (lowerUnipotent21 x), lowerUnipotent21_mul_lowerUnipotent21, ← mul_assoc (lowerUnipotent21 (x +
        -z)),
      lowerUnipotent21_mul_upperUnipotent3, mul_assoc, ← mul_assoc (iotaGL (diagUnitGL2 a)),
      iotaGL_diagUnitGL2_mul_upperUnipotent3, mul_zero, mul_assoc, add_comm x, hdual 0 (-y) 0, AddChar.inv_apply,
          zero_add,
      neg_neg]
  refine ⟨fun w => ?_, fun σ => ?_⟩
  · unfold localZetaDual31 localZeta31
    have hin : ∀ a : (v.adicCompletion ℚ)ˣ,
        (∫ x : v.adicCompletion ℚ, dualWhittakerFn3 W (iotaGL (diagUnitGL2 a) * lowerUnipotent21 x *
            (weylPrime3 * transposeInv3 (upperUnipotent3 0 y z * g))) ∂(selfDualHaarAt ℚ v)) =
          psiLocal ℚ v y * ∫ x : v.adicCompletion ℚ, dualWhittakerFn3 W (iotaGL (diagUnitGL2 a) * lowerUnipotent21 x *
              (weylPrime3 * transposeInv3 g)) ∂(selfDualHaarAt ℚ v) := by
      intro a
      simp_rw [hpt a]
      rw [integral_const_mul]
      congr 1
      exact integral_selfDual_comp_add_left v (-z) (fun x =>
        dualWhittakerFn3 W (iotaGL (diagUnitGL2 a) * lowerUnipotent21 x * (weylPrime3 * transposeInv3 g)))
    simp_rw [hin, mul_assoc]
    rw [integral_const_mul]
  · unfold IsLocalZeta31ConvergentAbove
    refine forall_congr' fun w => imp_congr_right fun _ => ?_
    have hfun : (fun p : (v.adicCompletion ℚ)ˣ × v.adicCompletion ℚ =>
        dualWhittakerFn3 W (iotaGL (diagUnitGL2 p.1) * lowerUnipotent21 p.2 *
            (weylPrime3 * transposeInv3 (upperUnipotent3 0 y z * g))) *
          ((χ⁻¹ p.1 : ℂˣ) : ℂ) * ((modulus (p.1 : v.adicCompletion ℚ) : ℝ) : ℂ) ^ (w - 1)) =
        fun p : (v.adicCompletion ℚ)ˣ × v.adicCompletion ℚ => psiLocal ℚ v y *
          (dualWhittakerFn3 W (iotaGL (diagUnitGL2 p.1) * lowerUnipotent21 (-z + p.2) * (weylPrime3 * transposeInv3 g))
              *
            ((χ⁻¹ p.1 : ℂˣ) : ℂ) * ((modulus (p.1 : v.adicCompletion ℚ) : ℝ) : ℂ) ^ (w - 1)) := by
      funext p
      rw [hpt]
      ring
    rw [hfun, integrable_const_mul_iff_of_ne_zero _ _ (psiLocal_apply_ne_zero v y)]
    exact integrable_prod_comp_add_left_iff v (-z) (fun q : (v.adicCompletion ℚ)ˣ × v.adicCompletion ℚ =>
      dualWhittakerFn3 W (iotaGL (diagUnitGL2 q.1) * lowerUnipotent21 q.2 * (weylPrime3 * transposeInv3 g)) *
        ((χ⁻¹ q.1 : ℂˣ) : ℂ) * ((modulus (q.1 : v.adicCompletion ℚ) : ℝ) : ℂ) ^ (w - 1))

private theorem localZeta30_mul_of_mem_localMaximalCompact3 (hK : IsRightInvariant (localMaximalCompact3 (𝓞 ℚ) ℚ v) W)
    {k : LocalGL3 v} (hk : k ∈ localMaximalCompact3 (𝓞 ℚ) ℚ v) (g : LocalGL3 v) :
    letI := localBorel ℚ v
    (∀ s : ℂ, localZeta30 v (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ v))) W χ s (g * k) =
      localZeta30 v (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ v))) W χ s g) ∧
    ∀ σ : ℝ, IsLocalZeta30ConvergentAbove v (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ v))) W χ
        (g * k) σ ↔
      IsLocalZeta30ConvergentAbove v (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ v))) W χ g σ := by
  letI := localBorel ℚ v
  have h : ∀ a : (v.adicCompletion ℚ)ˣ, W (iotaGL (diagUnitGL2 a) * (g * k)) = 1 * W (iotaGL (diagUnitGL2 a) * g) :=
      fun a => by
    rw [← mul_assoc, hK _ k hk, one_mul]
  obtain ⟨hval, hconv⟩ := localZeta30_eq_and_convergent_iff_of_forall v _ W χ _ g _ one_ne_zero h
  exact ⟨fun s => by rw [hval s, one_mul], hconv⟩

private theorem localZetaDual31_mul_of_mem_localMaximalCompact3
    (hK : IsRightInvariant (localMaximalCompact3 (𝓞 ℚ) ℚ v) W) {k : LocalGL3 v}
    (hk : k ∈ localMaximalCompact3 (𝓞 ℚ) ℚ v) (g : LocalGL3 v) :
    letI := localBorel ℚ v
    (∀ w : ℂ, localZetaDual31 v (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ v))) (selfDualHaarAt ℚ v)
        W χ w (g * k) =
      localZetaDual31 v (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ v))) (selfDualHaarAt ℚ v)
        W χ w g) ∧
    ∀ σ : ℝ, IsLocalZeta31ConvergentAbove v (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ v)))
        (selfDualHaarAt ℚ v) (dualWhittakerFn3 W) χ⁻¹ (weylPrime3 * transposeInv3 (g * k)) σ ↔
      IsLocalZeta31ConvergentAbove v (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ v)))
        (selfDualHaarAt ℚ v) (dualWhittakerFn3 W) χ⁻¹ (weylPrime3 * transposeInv3 g) σ := by
  letI := localBorel ℚ v
  have hKd : ∀ h : LocalGL3 v, W (h * k) = W h := fun h => hK h k hk
  have h : ∀ (a : (v.adicCompletion ℚ)ˣ) (x : v.adicCompletion ℚ),
      dualWhittakerFn3 W (iotaGL (diagUnitGL2 a) * lowerUnipotent21 x * (weylPrime3 * transposeInv3 (g * k))) =
        1 * dualWhittakerFn3 W (iotaGL (diagUnitGL2 a) * lowerUnipotent21 x * (weylPrime3 * transposeInv3 g)) := by
    intro a x
    rw [transposeInv3_mul, ← mul_assoc weylPrime3, ← mul_assoc, dualWhittakerFn3_mul_transposeInv3 W k hKd, one_mul]
  obtain ⟨hval, hconv⟩ := localZeta31_eq_and_convergent_iff_of_forall v _ _ (dualWhittakerFn3 W) χ⁻¹ _ _ _ one_ne_zero
      h
  refine ⟨fun w => ?_, hconv⟩
  unfold localZetaDual31
  rw [hval w, one_mul]

private theorem exists_eq_centralGen_zpow_mul_iotaGL_mul_upperUnipotent3_mul_mul_of_mem (g : LocalGL3 v) :
    ∃ (m : ℤ) (c : (v.adicCompletion ℚ)ˣ) (y₂₃ y₁₃ : v.adicCompletion ℚ) (k : ℤ) (y : v.adicCompletion ℚ)
      (k₀ : LocalGL3 v), k₀ ∈ localMaximalCompact3 (𝓞 ℚ) ℚ v ∧
        g = centralGen v ^ m * iotaGL (diagUnitGL2 c) * upperUnipotent3 0 y₂₃ y₁₃ *
          (iotaGL (diagUnits2 1 (ratPrimeUnit v ^ k)) * upperUnipotent3 y 0 0) * k₀ := by
  obtain ⟨x, y, z, t, d, k, hk, ht, hg⟩ := exists_eq_upperUnipotent3_mul_diagonal_mul_mem_localMaximalCompact3 v g
  have hd : ∀ i, d i ≠ 0 := ne_zero_of_coe_eq_diagonal t d ht
  have hϖ : Valued.v (varpi v) = WithZero.exp (-1 : ℤ) := valued_varpi_eq v
  obtain ⟨m, hm⟩ := exists_valued_inv_zpow_mul_eq_one (varpi v) hϖ (hd 2)
  obtain ⟨n, hn⟩ := exists_valued_inv_zpow_mul_zpow_mul_eq_one (varpi v) (ratPrimeAt v) hϖ
    (valued_ratPrimeAt_eq_valued_varpi v) m (hd 1)
  have hϖm : varpi v ^ m ≠ 0 := zpow_ne_zero m (varpi_ne_zero v)
  obtain ⟨c, hc⟩ : ∃ c : (v.adicCompletion ℚ)ˣ, (c : v.adicCompletion ℚ) = d 0 * (varpi v ^ m)⁻¹ :=
    ⟨Units.mk0 _ (mul_ne_zero (hd 0) (inv_ne_zero hϖm)), rfl⟩
  have hP : (((centralGen v ^ m * iotaGL (diagUnitGL2 c) * iotaGL (diagUnits2 1 (ratPrimeUnit v ^ n))) : LocalGL3 v) :
      Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) =
      Matrix.diagonal ![varpi v ^ m * (c : v.adicCompletion ℚ), varpi v ^ m * ratPrimeAt v ^ n, varpi v ^ m] := by
    rw [coe_mul_of_coe_eq_diagonal _ _ _ _ (coe_mul_of_coe_eq_diagonal _ _ _ _
      (coe_zpow_of_coe_eq_diagonal _ _ (varpi_ne_zero v) (coe_centralGen_eq_diagonal v) m)
      (coe_iotaGL_diagUnitGL2_eq_diagonal c)) (coe_iotaGL_diagUnits2_one_eq_diagonal _)]
    congr 1
    funext i
    fin_cases i <;> simp [Units.val_zpow_eq_zpow_val, coe_ratPrimeUnit]
  have he : (((centralGen v ^ m * iotaGL (diagUnitGL2 c) * iotaGL (diagUnits2 1 (ratPrimeUnit v ^ n))))⁻¹ * t :
      LocalGL3 v) ∈ localMaximalCompact3 (𝓞 ℚ) ℚ v := by
    refine mem_localMaximalCompact3_of_coe_eq_diagonal v _ _ (coe_inv_mul_of_coe_eq_diagonal _ _ _ _ hP ht ?_) ?_
    · intro i
      fin_cases i
      · exact mul_ne_zero hϖm c.ne_zero
      · exact mul_ne_zero hϖm (zpow_ne_zero n (ratPrimeAt_ne_zero v))
      · exact hϖm
    · intro i
      fin_cases i
      · show Valued.v ((varpi v ^ m * (c : v.adicCompletion ℚ))⁻¹ * d 0) = 1
        rw [hc, mul_comm (d 0), mul_inv_cancel_left₀ hϖm, inv_mul_cancel₀ (hd 0), map_one]
      · exact hn
      · exact hm
  refine ⟨m, c, y, ((c⁻¹ : (v.adicCompletion ℚ)ˣ) : v.adicCompletion ℚ) * z, n, ((c⁻¹ : (v.adicCompletion ℚ)ˣ) :
      v.adicCompletion ℚ) * x * ((ratPrimeUnit v ^ n : (v.adicCompletion ℚ)ˣ) : v.adicCompletion ℚ),
    ((centralGen v ^ m * iotaGL (diagUnitGL2 c) * iotaGL (diagUnits2 1 (ratPrimeUnit v ^ n))))⁻¹ * t * k,
        Subgroup.mul_mem _ he hk, ?_⟩
  exact normal_form_reassembly (centralGen v) (centralGen_central v) m c (ratPrimeUnit v ^ n) x y z _ k g
    (by rw [mul_inv_cancel_left]; exact hg)

end ZetaTransformation
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_laurent_localZeta_eq_gl3LFactorPoly_of_sphericalData.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_exists_laurent_localZeta_eq_gl3LFactorPoly_of_sphericalData.LanglandsTunnell.CubicInduction"
end
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_laurent_localZeta_eq_gl3LFactorPoly_of_sphericalData.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_exists_laurent_localZeta_eq_gl3LFactorPoly_of_sphericalData.LanglandsTunnell.CubicInduction"

section

set_option autoImplicit false

open IsDedekindDomain NumberField NumberField.TateGlobal AutomorphicForm LanglandsTunnell.Converse LanglandsTunnell.RankinSelberg

p2m_open "LanglandsTunnell.CubicInduction P2MW.S_LanglandsTunnell_CubicInduction_exists_laurent_localZeta_eq_gl3LFactorPoly_of_sphericalData.LanglandsTunnell.CubicInduction MeasureTheory"
open scoped ENNReal

namespace LanglandsTunnell
p2m_export "LanglandsTunnell" "TateLocal.localBorel TateLocal.borelSpace_localBorel TateLocal.stdRootNumberAt TateLocal.higherUnitsAt TateLocal.mem_higherUnitsAt_iff TateLocal.HasConductorExponentAt TateLocal.modulus TateLocal.modulus_mul"
namespace CubicInduction
p2m_export "LanglandsTunnell.CubicInduction" "localZeta31 localZeta30 localZetaDual31 IsLocalZeta30ConvergentAbove IsLocalZeta31ConvergentAbove lowerUnipotent21 lowerUnipotent21_coe longWeyl3 longWeyl3_coe dualWhittakerFn3 dualWhittakerFn3_apply weylPrime3 weylPrime3_coe transposeInv3_weylPrime3 transposeInv3_lowerUnipotent21 IsGL3PsiWhittakerFn transposeInv3 upperUnipotent3 upperUnipotent3_coe upperUnipotent3_zero embedMat2 iotaGL coe_iotaGL localMaximalCompact3 mem_localMaximalCompact3_iff LocalGL3 varpi varpi_ne_zero heckeGen1 heckeGen2 centralGen cNormQ cosetSum IsCosetEigenfunction IsRightInvariant diagUnitGL2 coe_diagUnitGL2 diagHom diagHom_apply ratPrimeAt ratPrimeAt_ne_zero ratPrimeUnit sphericalTorusValue diagUnits2 coe_diagUnits2 twoRowPointLocal twoRowPointLocal_zero_right eq_zero_of_coe_eq_diagonal_of_valued_lt_of_isGL3PsiWhittakerFn eq_zero_of_isCosetEigenfunction_of_isGL3PsiWhittakerFn_of_apply_one_eq_zero exists_eq_upperUnipotent3_mul_diagonal_mul_mem_localMaximalCompact3 isGL3PsiWhittakerFn_dualWhittakerFn3 sphericalTorusValue_eq_of_isCosetEigenfunction_of_isGL3PsiWhittakerFn"
p2m_open "LanglandsTunnell.CubicInduction LanglandsTunnell"

private theorem norm_sphericalTorusValue_le_pow (e₁ e₂ e₃ : ℂ) (n : ℕ) :
    ‖sphericalTorusValue e₁ e₂ e₃ n‖ ≤ (1 + ‖e₁‖ + ‖e₂‖ + ‖e₃‖) ^ n := by
  exact norm_le_pow_of_cubic_recursion e₁ e₂ e₃ (sphericalTorusValue e₁ e₂ e₃) rfl rfl rfl
    (sphericalTorusValue_add_three e₁ e₂ e₃) n

private theorem norm_twoRowCoeff_le (e₁ e₂ e₃ : ℂ) (k₁ k₂ : ℕ) :
    ‖twoRowCoeff e₁ e₂ e₃ k₁ k₂‖ ≤ 2 * (1 + ‖e₁‖ + ‖e₂‖ + ‖e₃‖) ^ (k₁ + k₂ + 1) := by
  have hv := norm_sphericalTorusValue_le_pow e₁ e₂ e₃
  set B : ℝ := 1 + ‖e₁‖ + ‖e₂‖ + ‖e₃‖ with hB
  have hB1 : 1 ≤ B := by
    have := norm_nonneg e₁
    have := norm_nonneg e₂
    have := norm_nonneg e₃
    linarith
  have hB0 : 0 ≤ B := zero_le_one.trans hB1
  cases k₂ with
  | zero =>
    rw [twoRowCoeff_zero]
    calc ‖sphericalTorusValue e₁ e₂ e₃ k₁‖ ≤ B ^ k₁ := hv k₁
      _ ≤ B ^ (k₁ + 0 + 1) := pow_le_pow_right₀ hB1 (by omega)
      _ ≤ 2 * B ^ (k₁ + 0 + 1) := le_mul_of_one_le_left (by positivity) one_le_two
  | succ m =>
    rw [twoRowCoeff_succ]
    refine (norm_sub_le _ _).trans ?_
    rw [norm_mul, norm_mul]
    calc ‖sphericalTorusValue e₁ e₂ e₃ k₁‖ * ‖sphericalTorusValue e₁ e₂ e₃ (m + 1)‖ +
          ‖sphericalTorusValue e₁ e₂ e₃ (k₁ + 1)‖ * ‖sphericalTorusValue e₁ e₂ e₃ m‖
        ≤ B ^ k₁ * B ^ (m + 1) + B ^ (k₁ + 1) * B ^ m :=
          add_le_add (mul_le_mul (hv k₁) (hv (m + 1)) (norm_nonneg _) (by positivity))
            (mul_le_mul (hv (k₁ + 1)) (hv m) (norm_nonneg _) (by positivity))
      _ = 2 * B ^ (k₁ + m + 1) := by
          rw [← pow_add, ← pow_add, show k₁ + 1 + m = k₁ + (m + 1) by ring, show k₁ + m + 1 = k₁ + (m + 1) by ring]
          ring
      _ ≤ 2 * B ^ (k₁ + (m + 1) + 1) :=
          mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hB1 (by omega)) zero_le_two

private theorem mul_rpow_lt_one_of_logb_lt {q ρ σ : ℝ} (hq : 1 < q) (hρ : 0 < ρ) (h : Real.logb q ρ < σ - 1) :
    ρ * q ^ (1 - σ) < 1 := by
  have hq₀ : 0 < q := zero_lt_one.trans hq
  have h' : ρ < q ^ (σ - 1) := (Real.logb_lt_iff_lt_rpow hq hρ).1 h
  calc ρ * q ^ (1 - σ) < q ^ (σ - 1) * q ^ (1 - σ) :=
        mul_lt_mul_of_pos_right h' (Real.rpow_pos_of_pos hq₀ _)
    _ = 1 := by
        rw [← Real.rpow_add hq₀]
        simp

private theorem zpow_neg_rpow_eq_rpow_zpow {q : ℝ} (hq₀ : 0 < q) (n : ℤ) (σ : ℝ) :
    (q ^ (-n)) ^ (σ - 1) = (q ^ (1 - σ)) ^ n := by
  rw [← Real.rpow_intCast q (-n), ← Real.rpow_mul hq₀.le, ← Real.rpow_intCast (q ^ (1 - σ)) n,
    ← Real.rpow_mul hq₀.le]
  congr 1
  push_cast
  ring

private theorem lintegral_comp_ord_lt_top {α : Type*} {mα : MeasurableSpace α} (μ : Measure α) (ord : α → ℤ)
    (hord : Measurable ord) (M : ℝ≥0∞) (hM : M ≠ ∞) (hμ : ∀ n : ℤ, μ {a | ord a = n} ≤ M) (ψ : ℤ → ℝ≥0∞) (n₀ : ℤ)
    (hψ₀ : ∀ n, n < n₀ → ψ n = 0) (K t : ℝ) (ht₀ : 0 < t) (ht₁ : t < 1)
    (hψ : ∀ n, n₀ ≤ n → ψ n ≤ ENNReal.ofReal (K * t ^ n)) : ∫⁻ a, ψ (ord a) ∂μ < ∞ := by
  have hψm : Measurable ψ := measurable_of_countable ψ
  rw [← lintegral_map hψm hord, lintegral_countable' (μ := μ.map ord)]
  have hfib : ∀ n : ℤ, (μ.map ord) {n} ≤ M := fun n => by
    rw [Measure.map_apply hord (measurableSet_singleton n)]
    exact hμ n
  calc ∑' n : ℤ, ψ n * (μ.map ord) {n}
      ≤ ∑' n : ℤ, ψ n * M := ENNReal.tsum_le_tsum fun n => mul_le_mul_right (hfib n) _
    _ = (∑' n : ℤ, ψ n) * M := ENNReal.tsum_mul_right
    _ = (∑' j : ℕ, ψ (n₀ + j)) * M := by
        congr 1
        refine (Function.Injective.tsum_eq (g := fun j : ℕ => n₀ + (j : ℤ))
          (fun i j hij => by simpa using hij) ?_).symm
        · intro n hn
          refine ⟨(n - n₀).toNat, ?_⟩
          have hle : n₀ ≤ n := by
            by_contra h
            exact hn (hψ₀ n (lt_of_not_ge h))
          simp only
          omega
    _ ≤ (∑' j : ℕ, ENNReal.ofReal (K * t ^ n₀) * ENNReal.ofReal t ^ j) * M := by
        refine mul_le_mul_left (ENNReal.tsum_le_tsum fun j => ?_) _
        refine (hψ _ (by omega)).trans (le_of_eq ?_)
        rw [zpow_add₀ ht₀.ne', zpow_natCast, ← mul_assoc, ENNReal.ofReal_mul' (pow_nonneg ht₀.le j),
          ENNReal.ofReal_pow ht₀.le]
    _ = ENNReal.ofReal (K * t ^ n₀) * (1 - ENNReal.ofReal t)⁻¹ * M := by
        rw [ENNReal.tsum_mul_left, ENNReal.tsum_geometric]
    _ < ∞ := by
        have ht : ENNReal.ofReal t < 1 := ENNReal.ofReal_lt_one.2 ht₁
        refine ENNReal.mul_lt_top (ENNReal.mul_lt_top ENNReal.ofReal_lt_top ?_) hM.lt_top
        exact ENNReal.inv_lt_top.2 (tsub_pos_iff_lt.2 ht)

private theorem integrable_of_norm_le_zpow_ord {α : Type*} {mα : MeasurableSpace α} (μ : Measure α) (ord : α → ℤ)
    (hord : Measurable ord) (M : ℝ≥0∞) (hM : M ≠ ∞) (hμ : ∀ n : ℤ, μ {a | ord a = n} ≤ M) (F : α → ℂ)
    (hF : AEStronglyMeasurable F μ) (n₀ : ℤ) (hvan : ∀ a, ord a < n₀ → F a = 0) (C r : ℝ) (hr₀ : 0 < r)
    (hr₁ : r < 1) (hbd : ∀ a, n₀ ≤ ord a → ‖F a‖ ≤ C * r ^ ord a) : Integrable F μ := by
  classical
  refine ⟨hF, ?_⟩
  set ψ : ℤ → ℝ≥0∞ := fun n => if n₀ ≤ n then ENNReal.ofReal (C * r ^ n) else 0 with hψdef
  have hpt : ∀ a, ‖F a‖ₑ ≤ ψ (ord a) := fun a => by
    by_cases h : n₀ ≤ ord a
    · rw [← ofReal_norm, hψdef]
      simp only [h, if_true]
      exact ENNReal.ofReal_le_ofReal (hbd a h)
    · rw [hvan a (lt_of_not_ge h), enorm_zero]
      exact zero_le
  refine (lintegral_mono hpt).trans_lt
    (lintegral_comp_ord_lt_top μ ord hord M hM hμ ψ n₀ (fun n hn => ?_) C r hr₀ hr₁ fun n hn => ?_)
  · simp only [hψdef, not_le.2 hn, if_false]
  · simp only [hψdef, hn, if_true, le_refl]

private theorem integrable_prod_of_norm_le_zpow_ord {α β : Type*} {mα : MeasurableSpace α} {mβ : MeasurableSpace β}
    (μ : Measure α) (ν : Measure β) [SFinite ν] (ord : α → ℤ) (hord : Measurable ord) (M : ℝ≥0∞) (hM : M ≠ ∞)
    (hμ : ∀ n : ℤ, μ {a | ord a = n} ≤ M) (X : ℤ → Set β) (hX : ∀ n, MeasurableSet (X n)) (M' ρ : ℝ) (hM' : 0 ≤ M')
    (hρ : 0 < ρ) (hν : ∀ n : ℤ, ν (X n) ≤ ENNReal.ofReal (M' * ρ ^ n)) (G : α × β → ℂ)
    (hG : AEStronglyMeasurable G (μ.prod ν))
    (n₀ : ℤ) (hsupp : ∀ a b, G (a, b) ≠ 0 → n₀ ≤ ord a ∧ b ∈ X (ord a)) (C r : ℝ) (hr₀ : 0 < r) (hrρ : r * ρ < 1)
    (hbd : ∀ a b, n₀ ≤ ord a → ‖G (a, b)‖ ≤ C * r ^ ord a) : Integrable G (μ.prod ν) := by
  classical
  refine ⟨hG, ?_⟩
  set φ : ℤ → ℝ≥0∞ := fun n => if n₀ ≤ n then ENNReal.ofReal (C * r ^ n) else 0 with hφdef
  set T : Set (α × β) := ⋃ n : ℤ, ({a | ord a = n} ×ˢ X n) with hTdef
  have hT : MeasurableSet T :=
    MeasurableSet.iUnion fun n => (hord (measurableSet_singleton n)).prod (hX n)
  have hmemT : ∀ p : α × β, p ∈ T ↔ p.2 ∈ X (ord p.1) := fun p => by
    simp only [hTdef, Set.mem_iUnion, Set.mem_prod, Set.mem_setOf_eq]
    constructor
    · rintro ⟨n, hn, hp⟩
      rwa [hn]
    · intro hp
      exact ⟨ord p.1, rfl, hp⟩

  have hpt : ∀ p : α × β, ‖G p‖ₑ ≤ T.indicator (fun p => φ (ord p.1)) p := fun p => by
    by_cases hG0 : G p = 0
    · rw [hG0, enorm_zero]
      exact zero_le
    · obtain ⟨hn, hb⟩ := hsupp p.1 p.2 hG0
      rw [Set.indicator_of_mem ((hmemT p).2 hb), ← ofReal_norm]
      simp only [hφdef, hn, if_true]
      exact ENNReal.ofReal_le_ofReal (hbd p.1 p.2 hn)
  have hmeas : Measurable (T.indicator fun p : α × β => φ (ord p.1)) :=
    ((measurable_of_countable φ).comp (hord.comp measurable_fst)).indicator hT
  have hinner : ∀ a, ∫⁻ b, T.indicator (fun p : α × β => φ (ord p.1)) (a, b) ∂ν = φ (ord a) * ν (X (ord a)) := by
    intro a
    have : (fun b => T.indicator (fun p : α × β => φ (ord p.1)) (a, b)) =
        (X (ord a)).indicator fun _ => φ (ord a) := by
      funext b
      by_cases hb : b ∈ X (ord a)
      · rw [Set.indicator_of_mem ((hmemT (a, b)).2 hb), Set.indicator_of_mem hb]
      · rw [Set.indicator_of_notMem (fun h => hb ((hmemT (a, b)).1 h)), Set.indicator_of_notMem hb]
    rw [this, lintegral_indicator (hX _), setLIntegral_const]
  refine (lintegral_mono hpt).trans_lt ?_
  rw [lintegral_prod _ hmeas.aemeasurable]
  simp only [hinner]
  refine (lintegral_mono (fun a => ?_)).trans_lt (lintegral_comp_ord_lt_top μ ord hord M hM hμ
    (fun n => φ n * ENNReal.ofReal (M' * ρ ^ n)) n₀ (fun n hn => ?_) (M' * C) (r * ρ) (mul_pos hr₀ hρ) hrρ
    fun n hn => ?_)
  · exact mul_le_mul_right (hν _) _
  · simp only [hφdef, not_le.2 hn, if_false, zero_mul]
  · simp only [hφdef, hn, if_true]
    rw [mul_comm, ← ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ M' * ρ ^ n), mul_zpow]
    exact le_of_eq (congrArg ENNReal.ofReal (by ring))

section LocalZeta

variable (v : HeightOneSpectrum (𝓞 ℚ))

private theorem measurable_modulus_cpow_of_ord {mT : MeasurableSpace (v.adicCompletion ℚ)ˣ}
    (ord : (v.adicCompletion ℚ)ˣ → ℤ) (hord : Measurable ord) (q : ℝ)
    (hmod : ∀ a : (v.adicCompletion ℚ)ˣ, (TateLocal.modulus (a : v.adicCompletion ℚ) : ℝ) = q ^ (-ord a)) (s : ℂ) :
    Measurable fun a : (v.adicCompletion ℚ)ˣ =>
      ((TateLocal.modulus (a : v.adicCompletion ℚ) : ℝ) : ℂ) ^ (s - 1) := by
  have : (fun a : (v.adicCompletion ℚ)ˣ => ((TateLocal.modulus (a : v.adicCompletion ℚ) : ℝ) : ℂ) ^ (s - 1)) =
      (fun n : ℤ => ((q ^ (-n) : ℝ) : ℂ) ^ (s - 1)) ∘ ord := by
    funext a
    simp only [Function.comp, hmod a]
  rw [this]
  exact (measurable_of_countable _).comp hord

private theorem norm_modulus_cpow_of_ord (ord : (v.adicCompletion ℚ)ˣ → ℤ) (q : ℝ) (hq₀ : 0 < q)
    (hmod : ∀ a : (v.adicCompletion ℚ)ˣ, (TateLocal.modulus (a : v.adicCompletion ℚ) : ℝ) = q ^ (-ord a)) (s : ℂ)
    (a : (v.adicCompletion ℚ)ˣ) :
    ‖((TateLocal.modulus (a : v.adicCompletion ℚ) : ℝ) : ℂ) ^ (s - 1)‖ = (q ^ (1 - s.re)) ^ ord a := by
  have hpos : (0 : ℝ) < (TateLocal.modulus (a : v.adicCompletion ℚ) : ℝ) := by
    rw [hmod a]
    positivity
  rw [Complex.norm_cpow_eq_rpow_re_of_pos hpos, Complex.sub_re, Complex.one_re, hmod a,
    zpow_neg_rpow_eq_rpow_zpow hq₀]

private theorem isLocalZeta30ConvergentAbove_of_forall_norm_le {mT : MeasurableSpace (v.adicCompletion ℚ)ˣ}
    (μ : Measure (v.adicCompletion ℚ)ˣ) (ord : (v.adicCompletion ℚ)ˣ → ℤ) (hord : Measurable ord) (q : ℝ) (hq : 1 < q)
    (hmod : ∀ a : (v.adicCompletion ℚ)ˣ, (TateLocal.modulus (a : v.adicCompletion ℚ) : ℝ) = q ^ (-ord a))
    (M : ℝ≥0∞) (hM : M ≠ ∞) (hμ : ∀ n : ℤ, μ {a | ord a = n} ≤ M) (W : LocalGL3 v → ℂ)
    (χ : (v.adicCompletion ℚ)ˣ →* ℂˣ) (g : LocalGL3 v)
    (hmeas : AEStronglyMeasurable
      (fun a : (v.adicCompletion ℚ)ˣ => W (iotaGL (diagUnitGL2 a) * g) * ((χ a : ℂˣ) : ℂ)) μ)
    (n₀ : ℤ) (hvan : ∀ a : (v.adicCompletion ℚ)ˣ, ord a < n₀ → W (iotaGL (diagUnitGL2 a) * g) = 0) (C ρ : ℝ)
    (hρ : 0 < ρ)
    (hbd : ∀ a : (v.adicCompletion ℚ)ˣ, n₀ ≤ ord a →
      ‖W (iotaGL (diagUnitGL2 a) * g) * ((χ a : ℂˣ) : ℂ)‖ ≤ C * ρ ^ ord a) :
    IsLocalZeta30ConvergentAbove v μ W χ g (1 + Real.logb q ρ) := by
  intro s hs
  have hq₀ : 0 < q := zero_lt_one.trans hq
  have hr₀ : 0 < ρ * q ^ (1 - s.re) := mul_pos hρ (Real.rpow_pos_of_pos hq₀ _)
  have hr₁ : ρ * q ^ (1 - s.re) < 1 := mul_rpow_lt_one_of_logb_lt hq hρ (by linarith)
  refine integrable_of_norm_le_zpow_ord μ ord hord M hM hμ _ ?_ n₀ ?_ C _ hr₀ hr₁ ?_
  · exact hmeas.mul ((measurable_modulus_cpow_of_ord v ord hord q hmod s).aestronglyMeasurable)
  · intro a ha
    simp only [hvan a ha, zero_mul]
  · intro a ha
    rw [norm_mul, norm_modulus_cpow_of_ord v ord q hq₀ hmod s a, mul_zpow, ← mul_assoc]
    exact mul_le_mul_of_nonneg_right (hbd a ha) (zpow_nonneg (Real.rpow_pos_of_pos hq₀ _).le _)

private theorem isLocalZeta31ConvergentAbove_of_forall_norm_le {mT : MeasurableSpace (v.adicCompletion ℚ)ˣ}
    {mA : MeasurableSpace (v.adicCompletion ℚ)} (μ : Measure (v.adicCompletion ℚ)ˣ) (ν : Measure (v.adicCompletion ℚ))
    [SFinite ν] (ord : (v.adicCompletion ℚ)ˣ → ℤ) (hord : Measurable ord) (q : ℝ) (hq : 1 < q)
    (hmod : ∀ a : (v.adicCompletion ℚ)ˣ, (TateLocal.modulus (a : v.adicCompletion ℚ) : ℝ) = q ^ (-ord a))
    (M : ℝ≥0∞) (hM : M ≠ ∞) (hμ : ∀ n : ℤ, μ {a | ord a = n} ≤ M) (X : ℤ → Set (v.adicCompletion ℚ))
    (hX : ∀ n, MeasurableSet (X n)) (M' ρ' : ℝ) (hM' : 0 ≤ M') (hρ' : 0 < ρ')
    (hν : ∀ n : ℤ, ν (X n) ≤ ENNReal.ofReal (M' * ρ' ^ n))
    (W : LocalGL3 v → ℂ) (χ : (v.adicCompletion ℚ)ˣ →* ℂˣ) (g : LocalGL3 v)
    (hmeas : AEStronglyMeasurable
      (fun p : (v.adicCompletion ℚ)ˣ × v.adicCompletion ℚ =>
        W (iotaGL (diagUnitGL2 p.1) * lowerUnipotent21 p.2 * g) * ((χ p.1 : ℂˣ) : ℂ)) (μ.prod ν))
    (n₀ : ℤ)
    (hsupp : ∀ (a : (v.adicCompletion ℚ)ˣ) (x : v.adicCompletion ℚ),
      W (iotaGL (diagUnitGL2 a) * lowerUnipotent21 x * g) ≠ 0 → n₀ ≤ ord a ∧ x ∈ X (ord a))
    (C ρ : ℝ) (hρ : 0 < ρ)
    (hbd : ∀ (a : (v.adicCompletion ℚ)ˣ) (x : v.adicCompletion ℚ), n₀ ≤ ord a →
      ‖W (iotaGL (diagUnitGL2 a) * lowerUnipotent21 x * g) * ((χ a : ℂˣ) : ℂ)‖ ≤ C * ρ ^ ord a) :
    IsLocalZeta31ConvergentAbove v μ ν W χ g (1 + Real.logb q (ρ * ρ')) := by
  intro s hs
  have hq₀ : 0 < q := zero_lt_one.trans hq
  have hr₀ : 0 < ρ * q ^ (1 - s.re) := mul_pos hρ (Real.rpow_pos_of_pos hq₀ _)
  have hrρ : ρ * q ^ (1 - s.re) * ρ' < 1 := by
    have h := mul_rpow_lt_one_of_logb_lt hq (mul_pos hρ hρ') (by linarith : Real.logb q (ρ * ρ') < s.re - 1)
    calc ρ * q ^ (1 - s.re) * ρ' = ρ * ρ' * q ^ (1 - s.re) := by ring
      _ < 1 := h
  refine integrable_prod_of_norm_le_zpow_ord μ ν ord hord M hM hμ X hX M' ρ' hM' hρ' hν _ ?_ n₀ ?_ C _ hr₀ hrρ ?_
  · exact hmeas.mul
      (((measurable_modulus_cpow_of_ord v ord hord q hmod s).comp measurable_fst).aestronglyMeasurable)
  · intro a x hne
    refine hsupp a x fun h0 => hne ?_
    simp only [h0, zero_mul]
  · intro a x ha
    rw [norm_mul, norm_modulus_cpow_of_ord v ord q hq₀ hmod s a, mul_zpow, ← mul_assoc]
    exact mul_le_mul_of_nonneg_right (hbd a x ha) (zpow_nonneg (Real.rpow_pos_of_pos hq₀ _).le _)

end LocalZeta
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_laurent_localZeta_eq_gl3LFactorPoly_of_sphericalData.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_exists_laurent_localZeta_eq_gl3LFactorPoly_of_sphericalData.LanglandsTunnell.CubicInduction"

end LanglandsTunnell.CubicInduction
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_laurent_localZeta_eq_gl3LFactorPoly_of_sphericalData.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_exists_laurent_localZeta_eq_gl3LFactorPoly_of_sphericalData.LanglandsTunnell.CubicInduction"
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_laurent_localZeta_eq_gl3LFactorPoly_of_sphericalData.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_exists_laurent_localZeta_eq_gl3LFactorPoly_of_sphericalData.LanglandsTunnell.CubicInduction"
end
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_laurent_localZeta_eq_gl3LFactorPoly_of_sphericalData.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_exists_laurent_localZeta_eq_gl3LFactorPoly_of_sphericalData.LanglandsTunnell.CubicInduction"

section

set_option autoImplicit false

open IsDedekindDomain NumberField NumberField.TateGlobal AutomorphicForm LanglandsTunnell.Converse LanglandsTunnell.RankinSelberg LanglandsTunnell.TateLocal MeasureTheory

p2m_open "IsDedekindDomain.HeightOneSpectrum~Extension LanglandsTunnell.CubicInduction P2MW.S_LanglandsTunnell_CubicInduction_exists_laurent_localZeta_eq_gl3LFactorPoly_of_sphericalData.LanglandsTunnell.CubicInduction NumberField.StandardAddChar"

private theorem cubic_mul_tsum_eq_of_summable (e₁ e₂ e₃ : ℂ) (u : ℕ → ℂ)
    (hu : ∀ n : ℕ, u (n + 3) = e₁ * u (n + 2) - e₂ * u (n + 1) + e₃ * u n) (Y : ℂ)
    (hs : Summable fun n : ℕ => u n * Y ^ n) :
    (1 - e₁ * Y + e₂ * Y ^ 2 - e₃ * Y ^ 3) * ∑' n : ℕ, u n * Y ^ n =
      u 0 + (u 1 - e₁ * u 0) * Y + (u 2 - e₁ * u 1 + e₂ * u 0) * Y ^ 2 := by
  have H0 := hs.hasSum
  have H1 := (hasSum_nat_add_iff' 1).2 H0
  have H2 := (hasSum_nat_add_iff' 2).2 H0
  have H3 := (hasSum_nat_add_iff' 3).2 H0
  have hpt : ∀ n : ℕ, u (n + 3) * Y ^ (n + 3) =
      e₁ * Y * (u (n + 2) * Y ^ (n + 2)) - e₂ * Y ^ 2 * (u (n + 1) * Y ^ (n + 1)) + e₃ * Y ^ 3 * (u n * Y ^ n) := by
    intro n
    rw [hu n]
    ring
  rw [show (fun n : ℕ => u (n + 3) * Y ^ (n + 3)) = fun n : ℕ =>
      e₁ * Y * (u (n + 2) * Y ^ (n + 2)) - e₂ * Y ^ 2 * (u (n + 1) * Y ^ (n + 1)) + e₃ * Y ^ 3 * (u n * Y ^ n) from
    funext hpt] at H3
  have key := H3.unique (((H2.mul_left (e₁ * Y)).sub (H1.mul_left (e₂ * Y ^ 2))).add (H0.mul_left (e₃ * Y ^ 3)))
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, pow_zero, mul_one, pow_one] at key
  linear_combination key

private theorem summable_of_norm_le_mul_geometric (f : ℕ → ℂ) (C r : ℝ) (hr0 : 0 ≤ r) (hr1 : r < 1)
    (hf : ∀ k : ℕ, ‖f k‖ ≤ C * r ^ k) : Summable f :=
  Summable.of_norm_bounded ((summable_geometric_of_lt_one hr0 hr1).mul_left C) hf

private theorem summable_shift_mul_pow_of_norm_le (f : ℕ → ℂ) (C₀ B : ℝ) (hB : 0 ≤ B)
    (hf : ∀ k : ℕ, ‖f k‖ ≤ C₀ * B ^ k) (Y : ℂ) (hY : ‖Y‖ * B < 1) (K : ℕ) :
    Summable fun k : ℕ => f (K + k) * Y ^ k := by
  refine summable_of_norm_le_mul_geometric _ (C₀ * B ^ K) (‖Y‖ * B) (mul_nonneg (norm_nonneg Y) hB) hY fun k => ?_
  rw [norm_mul, norm_pow, mul_pow, mul_comm (‖Y‖ ^ k)]
  calc ‖f (K + k)‖ * ‖Y‖ ^ k ≤ C₀ * B ^ (K + k) * ‖Y‖ ^ k :=
        mul_le_mul_of_nonneg_right (hf (K + k)) (pow_nonneg (norm_nonneg Y) k)
    _ = C₀ * B ^ K * (B ^ k * ‖Y‖ ^ k) := by rw [pow_add]; ring

private theorem cubic_mul_tsum_shift_eq (e₁ e₂ e₃ : ℂ) (u : ℕ → ℂ)
    (hu : ∀ n : ℕ, u (n + 3) = e₁ * u (n + 2) - e₂ * u (n + 1) + e₃ * u n) (Y : ℂ) (K : ℕ)
    (hs : Summable fun k : ℕ => u (K + k) * Y ^ k) :
    (1 - e₁ * Y + e₂ * Y ^ 2 - e₃ * Y ^ 3) * ∑' k : ℕ, u (K + k) * Y ^ (K + k) =
      Y ^ K * (u K + (u (K + 1) - e₁ * u K) * Y + (u (K + 2) - e₁ * u (K + 1) + e₂ * u K) * Y ^ 2) := by
  have hu' : ∀ n : ℕ, u (K + (n + 3)) = e₁ * u (K + (n + 2)) - e₂ * u (K + (n + 1)) + e₃ * u (K + n) := by
    intro n
    simp only [← add_assoc]
    exact hu (K + n)
  have h := cubic_mul_tsum_eq_of_summable e₁ e₂ e₃ (fun n => u (K + n)) hu' Y hs
  simp only [add_zero] at h
  have hsplit : ∑' k : ℕ, u (K + k) * Y ^ (K + k) = Y ^ K * ∑' k : ℕ, u (K + k) * Y ^ k := by
    rw [← tsum_mul_left]
    refine tsum_congr fun k => ?_
    rw [pow_add]
    ring
  rw [hsplit]
  linear_combination Y ^ K * h

section GeneratingFunction

private theorem eval_gl3LFactorPoly_mul_tsum_of_cubic_recurrence (e₁ e₂ e₃ : ℂ) (u : ℕ → ℂ)
    (hu : ∀ n : ℕ, u (n + 3) = e₁ * u (n + 2) - e₂ * u (n + 1) + e₃ * u n) (Y : ℂ)
    (hs : Summable fun n : ℕ => u n * Y ^ n) :
    (gl3LFactorPoly e₁ e₂ e₃).eval Y * ∑' n : ℕ, u n * Y ^ n =
      u 0 + (u 1 - e₁ * u 0) * Y + (u 2 - e₁ * u 1 + e₂ * u 0) * Y ^ 2 := by
  rw [eval_gl3LFactorPoly]
  exact cubic_mul_tsum_eq_of_summable e₁ e₂ e₃ u hu Y hs

private theorem twoRowCoeff_add_three_left (e₁ e₂ e₃ : ℂ) (k c : ℕ) :
    twoRowCoeff e₁ e₂ e₃ (k + 3) c =
      e₁ * twoRowCoeff e₁ e₂ e₃ (k + 2) c - e₂ * twoRowCoeff e₁ e₂ e₃ (k + 1) c + e₃ * twoRowCoeff e₁ e₂ e₃ k c := by
  cases c with
  | zero =>
    simp only [twoRowCoeff_zero]
    exact sphericalTorusValue_add_three e₁ e₂ e₃ k
  | succ c =>
    have hA := sphericalTorusValue_add_three e₁ e₂ e₃ k
    have hB : sphericalTorusValue e₁ e₂ e₃ (k + 4) =
        e₁ * sphericalTorusValue e₁ e₂ e₃ (k + 3) - e₂ * sphericalTorusValue e₁ e₂ e₃ (k + 2) +
          e₃ * sphericalTorusValue e₁ e₂ e₃ (k + 1) := by
      have h' := sphericalTorusValue_add_three e₁ e₂ e₃ (k + 1)
      simp only [add_assoc, Nat.reduceAdd] at h'
      exact h'
    simp only [twoRowCoeff_succ, add_assoc, Nat.reduceAdd]
    linear_combination sphericalTorusValue e₁ e₂ e₃ (c + 1) * hA - sphericalTorusValue e₁ e₂ e₃ c * hB

private theorem summable_twoRowCoeff_shift (e₁ e₂ e₃ Y : ℂ) (hY : ‖Y‖ * (1 + ‖e₁‖ + ‖e₂‖ + ‖e₃‖) < 1) (K c : ℕ) :
    Summable fun k : ℕ => twoRowCoeff e₁ e₂ e₃ (K + k) c * Y ^ k := by
  refine summable_shift_mul_pow_of_norm_le (fun k => twoRowCoeff e₁ e₂ e₃ k c)
    (2 * (1 + ‖e₁‖ + ‖e₂‖ + ‖e₃‖) ^ (c + 1)) (1 + ‖e₁‖ + ‖e₂‖ + ‖e₃‖) (by positivity) (fun k => ?_) Y hY K
  refine (norm_twoRowCoeff_le e₁ e₂ e₃ k c).trans (le_of_eq ?_)
  rw [show k + c + 1 = c + 1 + k by omega, pow_add]
  ring

private theorem summable_twoRowCoeff_mul_pow (e₁ e₂ e₃ Y : ℂ) (hY : ‖Y‖ * (1 + ‖e₁‖ + ‖e₂‖ + ‖e₃‖) < 1) (K c : ℕ) :
    Summable fun k : ℕ => twoRowCoeff e₁ e₂ e₃ (K + k) c * Y ^ (K + k) := by
  refine ((summable_twoRowCoeff_shift e₁ e₂ e₃ Y hY K c).mul_left (Y ^ K)).congr fun k => ?_
  rw [pow_add]
  ring

private theorem eval_gl3LFactorPoly_mul_tsum_twoRowCoeff (e₁ e₂ e₃ Y : ℂ) (hY : ‖Y‖ * (1 + ‖e₁‖ + ‖e₂‖ + ‖e₃‖) < 1)
    (K c : ℕ) :
    (gl3LFactorPoly e₁ e₂ e₃).eval Y * ∑' k : ℕ, twoRowCoeff e₁ e₂ e₃ (K + k) c * Y ^ (K + k) =
      Y ^ K * (twoRowCoeff e₁ e₂ e₃ K c +
        (twoRowCoeff e₁ e₂ e₃ (K + 1) c - e₁ * twoRowCoeff e₁ e₂ e₃ K c) * Y +
        (twoRowCoeff e₁ e₂ e₃ (K + 2) c - e₁ * twoRowCoeff e₁ e₂ e₃ (K + 1) c + e₂ * twoRowCoeff e₁ e₂ e₃ K c) *
          Y ^ 2) := by
  rw [eval_gl3LFactorPoly]
  exact cubic_mul_tsum_shift_eq e₁ e₂ e₃ (fun k => twoRowCoeff e₁ e₂ e₃ k c)
    (fun n => twoRowCoeff_add_three_left e₁ e₂ e₃ n c) Y K (summable_twoRowCoeff_shift e₁ e₂ e₃ Y hY K c)

end GeneratingFunction
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_laurent_localZeta_eq_gl3LFactorPoly_of_sphericalData.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_exists_laurent_localZeta_eq_gl3LFactorPoly_of_sphericalData.LanglandsTunnell.CubicInduction"
end
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_laurent_localZeta_eq_gl3LFactorPoly_of_sphericalData.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_exists_laurent_localZeta_eq_gl3LFactorPoly_of_sphericalData.LanglandsTunnell.CubicInduction"

section

set_option autoImplicit false

open IsDedekindDomain NumberField NumberField.TateGlobal AutomorphicForm LanglandsTunnell.Converse LanglandsTunnell.RankinSelberg LanglandsTunnell.TateLocal MeasureTheory

p2m_open "IsDedekindDomain.HeightOneSpectrum~Extension LanglandsTunnell.CubicInduction P2MW.S_LanglandsTunnell_CubicInduction_exists_laurent_localZeta_eq_gl3LFactorPoly_of_sphericalData.LanglandsTunnell.CubicInduction NumberField.StandardAddChar"

noncomputable section

section UnipotentPrivates

variable {A : Type*} [CommRing A]

private theorem upperUnipotent3_mul_eq (x y z x' y' z' : A) :
    upperUnipotent3 x y z * upperUnipotent3 x' y' z' = upperUnipotent3 (x + x') (y + y') (z + z' + x * y') := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [upperUnipotent3, Units.val_mul, Matrix.mul_apply, Fin.sum_univ_three]
  all_goals ring

private theorem upperUnipotent3_inv (x y z : A) :
    (upperUnipotent3 x y z)⁻¹ = upperUnipotent3 (-x) (-y) (x * y - z) := by
  rw [inv_eq_iff_mul_eq_one, upperUnipotent3_mul_eq, show x + -x = 0 by ring, show y + -y = 0 by ring,
    show z + (x * y - z) + x * -y = 0 by ring, upperUnipotent3_zero]

end UnipotentPrivates
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_laurent_localZeta_eq_gl3LFactorPoly_of_sphericalData.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_exists_laurent_localZeta_eq_gl3LFactorPoly_of_sphericalData.LanglandsTunnell.CubicInduction"

section NormalisationPrivates

variable (v : HeightOneSpectrum (𝓞 ℚ))

private theorem upperUnipotent3_mem_localMaximalCompact3 (x : v.adicCompletion ℚ) (hx : Valued.v x ≤ 1) :
    upperUnipotent3 x 0 0 ∈ localMaximalCompact3 (𝓞 ℚ) ℚ v := by
  rw [mem_localMaximalCompact3_iff]
  refine ⟨fun i j => ?_, fun i j => ?_⟩
  · rw [upperUnipotent3_coe]
    fin_cases i <;> fin_cases j <;> simp [hx]
  · rw [upperUnipotent3_inv, upperUnipotent3_coe]
    fin_cases i <;> fin_cases j <;> simp [hx]

private theorem exists_nat_valued_eq_exp (y : v.adicCompletion ℚ) (hy : ¬ Valued.v y ≤ 1) :
    ∃ d : ℕ, Valued.v y = WithZero.exp (d : ℤ) := by
  have hy0 : Valued.v y ≠ 0 := fun h => hy (by rw [h]; exact zero_le')
  have hlog : 0 ≤ WithZero.log (Valued.v y) := by
    by_contra h
    push Not at h
    exact hy (by rw [← WithZero.exp_log hy0, ← WithZero.exp_zero, WithZero.exp_le_exp]; exact h.le)
  exact ⟨(WithZero.log (Valued.v y)).toNat, by rw [Int.toNat_of_nonneg hlog, WithZero.exp_log hy0]⟩

end NormalisationPrivates
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_laurent_localZeta_eq_gl3LFactorPoly_of_sphericalData.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_exists_laurent_localZeta_eq_gl3LFactorPoly_of_sphericalData.LanglandsTunnell.CubicInduction"

section Points

variable (v : HeightOneSpectrum (𝓞 ℚ))

private def torusUnipotentPoint (k : ℤ) (y : v.adicCompletion ℚ) : LocalGL3 v :=
  iotaGL (diagUnits2 1 (ratPrimeUnit v ^ k)) * upperUnipotent3 y 0 0

private theorem exists_torusUnipotentPoint_eq_mul_of_mem (k : ℤ) (y : v.adicCompletion ℚ) :
    ∃ (d : ℕ) (y' : v.adicCompletion ℚ) (k₀ : LocalGL3 v), Valued.v y' = WithZero.exp (d : ℤ) ∧
      k₀ ∈ localMaximalCompact3 (𝓞 ℚ) ℚ v ∧ torusUnipotentPoint v k y = torusUnipotentPoint v k y' * k₀ := by
  by_cases hy : Valued.v y ≤ 1
  · refine ⟨0, 1, upperUnipotent3 (y - 1) 0 0, by rw [map_one, Nat.cast_zero, WithZero.exp_zero],
      upperUnipotent3_mem_localMaximalCompact3 v _ ?_, ?_⟩
    · exact (Valuation.map_sub _ _ _).trans (max_le hy (by rw [map_one]))
    · rw [torusUnipotentPoint, torusUnipotentPoint, mul_assoc, upperUnipotent3_mul_eq, add_sub_cancel, add_zero,
        one_mul, add_zero]
  · obtain ⟨d, hd⟩ := exists_nat_valued_eq_exp v y hy
    exact ⟨d, y, 1, hd, (localMaximalCompact3 (𝓞 ℚ) ℚ v).one_mem, (mul_one _).symm⟩

end Points
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_laurent_localZeta_eq_gl3LFactorPoly_of_sphericalData.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_exists_laurent_localZeta_eq_gl3LFactorPoly_of_sphericalData.LanglandsTunnell.CubicInduction"

end
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_laurent_localZeta_eq_gl3LFactorPoly_of_sphericalData.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_exists_laurent_localZeta_eq_gl3LFactorPoly_of_sphericalData.LanglandsTunnell.CubicInduction"
end
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_laurent_localZeta_eq_gl3LFactorPoly_of_sphericalData.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_exists_laurent_localZeta_eq_gl3LFactorPoly_of_sphericalData.LanglandsTunnell.CubicInduction"

section

set_option autoImplicit false

open IsDedekindDomain NumberField NumberField.TateGlobal AutomorphicForm LanglandsTunnell.Converse LanglandsTunnell.RankinSelberg LanglandsTunnell.TateLocal MeasureTheory

p2m_open "IsDedekindDomain.HeightOneSpectrum~Extension LanglandsTunnell.CubicInduction P2MW.S_LanglandsTunnell_CubicInduction_exists_laurent_localZeta_eq_gl3LFactorPoly_of_sphericalData.LanglandsTunnell.CubicInduction NumberField.StandardAddChar"

noncomputable section

section SphericalValue

private def sphericalValue (W1 e₁ e₂ e₃ q : ℂ) (lam : Fin 3 → ℤ) : ℂ :=
  if lam 1 ≤ lam 0 ∧ lam 2 ≤ lam 1 then
    e₃ ^ lam 2 *
      (W1 * (q⁻¹ ^ (lam 0 - lam 2).toNat * twoRowCoeff e₁ e₂ e₃ (lam 0 - lam 2).toNat (lam 1 - lam 2).toNat))
  else 0

private theorem sphericalValue_of_not (W1 e₁ e₂ e₃ q : ℂ) (lam : Fin 3 → ℤ) (h : ¬ (lam 1 ≤ lam 0 ∧ lam 2 ≤ lam 1)) :
    sphericalValue W1 e₁ e₂ e₃ q lam = 0 :=
  if_neg h

private theorem sphericalValue_of_le (W1 e₁ e₂ e₃ q : ℂ) (lam : Fin 3 → ℤ) (h01 : lam 1 ≤ lam 0) (h12 : lam 2 ≤ lam 1) :
    sphericalValue W1 e₁ e₂ e₃ q lam =
      e₃ ^ lam 2 * (W1 * (q⁻¹ ^ (lam 0 - lam 2).toNat *
        twoRowCoeff e₁ e₂ e₃ (lam 0 - lam 2).toNat (lam 1 - lam 2).toNat)) :=
  if_pos ⟨h01, h12⟩

end SphericalValue
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_laurent_localZeta_eq_gl3LFactorPoly_of_sphericalData.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_exists_laurent_localZeta_eq_gl3LFactorPoly_of_sphericalData.LanglandsTunnell.CubicInduction"

section GenericEntries

variable {K : Type*}

private theorem forall_entries_of_literal (p : K → Prop) {a b c d e f g h i : K} (ha : p a) (hb : p b) (hc : p c)
    (hd : p d) (he : p e) (hf : p f) (hg : p g) (hh : p h) (hi : p i) :
    ∀ r s : Fin 3, p ((!![a, b, c; d, e, f; g, h, i] : Matrix (Fin 3) (Fin 3) K) r s) := by
  intro r s
  fin_cases r <;> fin_cases s <;> assumption

end GenericEntries
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_laurent_localZeta_eq_gl3LFactorPoly_of_sphericalData.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_exists_laurent_localZeta_eq_gl3LFactorPoly_of_sphericalData.LanglandsTunnell.CubicInduction"

section GenericMatrices

variable {K : Type*} [Field K]

private theorem kappaA_mul (y x : K) :
    (!![0, 1, 0; 1, y, 0; -x⁻¹, -(y * x⁻¹), 1] : Matrix (Fin 3) (Fin 3) K) * !![-y, 1, 0; 1, 0, 0; 0, x⁻¹, 1] = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three]
  ring

private theorem kappaA_mul' (y x : K) :
    (!![-y, 1, 0; 1, 0, 0; 0, x⁻¹, 1] : Matrix (Fin 3) (Fin 3) K) * !![0, 1, 0; 1, y, 0; -x⁻¹, -(y * x⁻¹), 1] = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three]
  ring

private theorem factorA (P b x y d₁ d₂ d₃ : K) (hx : x ≠ 0) (hb : b ≠ 0) (h₁ : d₁ = P) (h₂ : d₂ = x⁻¹)
    (h₃ : d₃ = -(x * b⁻¹)) :
    (!![0, P, 0; 0, 0, 1; b⁻¹, b⁻¹ * y, -(b⁻¹ * x)] : Matrix (Fin 3) (Fin 3) K) =
      !![1, 0, 0; 0, 1, -(b / x); 0, 0, 1] *
        (Matrix.diagonal ![d₁, d₂, d₃] * !![0, 1, 0; 1, y, 0; -x⁻¹, -(y * x⁻¹), 1]) := by
  subst h₁ h₂ h₃
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three] <;> field_simp <;> ring

private theorem kappaB_mul (y x : K) (hy : y ≠ 0) :
    (!![1, 0, 0; y⁻¹, 1, 0; -x⁻¹, -(y * x⁻¹), 1] : Matrix (Fin 3) (Fin 3) K) * !![1, 0, 0; -y⁻¹, 1, 0; 0, y * x⁻¹, 1] =
      1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three]
  field_simp
  ring

private theorem kappaB_mul' (y x : K) (hy : y ≠ 0) :
    (!![1, 0, 0; -y⁻¹, 1, 0; 0, y * x⁻¹, 1] : Matrix (Fin 3) (Fin 3) K) * !![1, 0, 0; y⁻¹, 1, 0; -x⁻¹, -(y * x⁻¹), 1] =
      1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three]
  field_simp
  ring

private theorem factorB (P b x y d₁ d₂ d₃ : K) (hx : x ≠ 0) (hy : y ≠ 0) (hb : b ≠ 0) (h₁ : d₁ = -(P * y⁻¹))
    (h₂ : d₂ = y * x⁻¹) (h₃ : d₃ = -(x * b⁻¹)) :
    (!![0, P, 0; 0, 0, 1; b⁻¹, b⁻¹ * y, -(b⁻¹ * x)] : Matrix (Fin 3) (Fin 3) K) =
      !![1, P * x / y, 0; 0, 1, -(b / x); 0, 0, 1] *
        (Matrix.diagonal ![d₁, d₂, d₃] * !![1, 0, 0; y⁻¹, 1, 0; -x⁻¹, -(y * x⁻¹), 1]) := by
  subst h₁ h₂ h₃
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three] <;> field_simp <;> ring

private theorem kappaC_mul (y x : K) :
    (!![1, 0, 0; 0, 0, 1; y⁻¹, 1, -(x * y⁻¹)] : Matrix (Fin 3) (Fin 3) K) * !![1, 0, 0; -y⁻¹, x * y⁻¹, 1; 0, 1, 0] =
      1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three]

private theorem kappaC_mul' (y x : K) :
    (!![1, 0, 0; -y⁻¹, x * y⁻¹, 1; 0, 1, 0] : Matrix (Fin 3) (Fin 3) K) * !![1, 0, 0; 0, 0, 1; y⁻¹, 1, -(x * y⁻¹)] =
      1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three]

private theorem factorC (P b x y d₁ d₂ d₃ : K) (hy : y ≠ 0) (hb : b ≠ 0) (h₁ : d₁ = -(P * y⁻¹)) (h₂ : d₂ = 1)
    (h₃ : d₃ = y * b⁻¹) :
    (!![0, P, 0; 0, 0, 1; b⁻¹, b⁻¹ * y, -(b⁻¹ * x)] : Matrix (Fin 3) (Fin 3) K) =
      !![1, P * x / y, P * b / y; 0, 1, 0; 0, 0, 1] *
        (Matrix.diagonal ![d₁, d₂, d₃] * !![1, 0, 0; 0, 0, 1; y⁻¹, 1, -(x * y⁻¹)]) := by
  subst h₁ h₂ h₃
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three] <;> field_simp <;> ring

end GenericMatrices
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_laurent_localZeta_eq_gl3LFactorPoly_of_sphericalData.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_exists_laurent_localZeta_eq_gl3LFactorPoly_of_sphericalData.LanglandsTunnell.CubicInduction"

section Helpers

variable {v : HeightOneSpectrum (𝓞 ℚ)}

private theorem valued_ratPrimeAt' (v : HeightOneSpectrum (𝓞 ℚ)) :
    Valued.v (ratPrimeAt v) = WithZero.exp (-1 : ℤ) := by
  rw [valued_ratPrimeAt_eq_valued_varpi]
  exact AdelicLevel.valued_uniformizerUnit ℚ v

private theorem valued_ratPrimeAt_zpow (k : ℤ) : Valued.v (ratPrimeAt v ^ k) = WithZero.exp (-k) := by
  rw [map_zpow₀, valued_ratPrimeAt' v, ← WithZero.exp_zsmul, smul_neg, smul_eq_mul, mul_one]

private theorem coe_ratPrimeUnit' (v : HeightOneSpectrum (𝓞 ℚ)) :
    ((ratPrimeUnit v : (v.adicCompletion ℚ)ˣ) : v.adicCompletion ℚ) = ratPrimeAt v :=
  rfl

private theorem coe_ratPrimeUnit_zpow (k : ℤ) :
    ((ratPrimeUnit v ^ k : (v.adicCompletion ℚ)ˣ) : v.adicCompletion ℚ) = ratPrimeAt v ^ k := by
  rw [Units.val_zpow_eq_zpow_val]
  rfl

private theorem valued_coe_ratPrimeUnit_zpow (k : ℤ) :
    Valued.v ((ratPrimeUnit v ^ k : (v.adicCompletion ℚ)ˣ) : v.adicCompletion ℚ) = WithZero.exp (-k) := by
  rw [coe_ratPrimeUnit_zpow, valued_ratPrimeAt_zpow]

private def diagGL (a : Fin 3 → (v.adicCompletion ℚ)ˣ) : LocalGL3 v where
  val := Matrix.diagonal fun i => (a i : v.adicCompletion ℚ)
  inv := Matrix.diagonal fun i => ((a i)⁻¹ : (v.adicCompletion ℚ)ˣ)
  val_inv := by
    rw [Matrix.diagonal_mul_diagonal]
    simp
  inv_val := by
    rw [Matrix.diagonal_mul_diagonal]
    simp

private theorem coe_diagGL (a : Fin 3 → (v.adicCompletion ℚ)ˣ) :
    ((diagGL a : LocalGL3 v) : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) =
      Matrix.diagonal fun i => (a i : v.adicCompletion ℚ) :=
  rfl

private def mkGL (m m' : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) (h : m * m' = 1) (h' : m' * m = 1) :
    LocalGL3 v :=
  ⟨m, m', h, h'⟩

private theorem coe_mkGL (m m' : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) (h : m * m' = 1) (h' : m' * m = 1) :
    ((mkGL m m' h h' : LocalGL3 v) : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) = m :=
  rfl

private theorem coe_mkGL_inv (m m' : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) (h : m * m' = 1) (h' : m' * m = 1) :
    (((mkGL m m' h h')⁻¹ : LocalGL3 v) : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) = m' :=
  rfl

private theorem transposeInv3_iotaGL_diagUnitGL2 (β : (v.adicCompletion ℚ)ˣ) :
    transposeInv3 (iotaGL (diagUnitGL2 β)) = iotaGL (diagUnitGL2 β⁻¹) := by
  refine Units.ext ?_
  rw [coe_transposeInv3, ← diagHom_apply, ← diagHom_apply, ← map_inv iotaGL, ← map_inv diagHom, coe_iotaGL,
    diagHom_apply, coe_diagUnitGL2]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [embedMat2, Matrix.transpose_apply]

private theorem coe_iotaGL_diagUnitGL2_inv_mul_upperUnipotent3 (β : (v.adicCompletion ℚ)ˣ) (x : v.adicCompletion ℚ) :
    ((iotaGL (diagUnitGL2 β⁻¹) * upperUnipotent3 (-x) 0 0 : LocalGL3 v) :
        Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) =
      !![((β : v.adicCompletion ℚ))⁻¹, -(((β : v.adicCompletion ℚ))⁻¹ * x), 0; 0, 1, 0; 0, 0, 1] := by
  rw [Units.val_mul, coe_iotaGL, coe_diagUnitGL2, upperUnipotent3_coe, Units.val_inv_eq_inv_val]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [embedMat2, Matrix.mul_apply, Fin.sum_univ_three]

private theorem coe_torusUnipotentPoint (k : ℤ) (y : v.adicCompletion ℚ) :
    ((torusUnipotentPoint v k y : LocalGL3 v) : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) =
      !![1, y, 0; 0, ratPrimeAt v ^ k, 0; 0, 0, 1] := by
  unfold torusUnipotentPoint
  rw [Units.val_mul, coe_iotaGL, upperUnipotent3_coe]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [embedMat2, diagUnits2, Matrix.mul_apply, Fin.sum_univ_three, coe_ratPrimeUnit']

private theorem coe_weylPrime3_mul_torusUnipotentPoint (k : ℤ) (y : v.adicCompletion ℚ) :
    ((weylPrime3 * torusUnipotentPoint v k y : LocalGL3 v) : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) =
      !![1, y, 0; 0, 0, 1; 0, ratPrimeAt v ^ k, 0] := by
  rw [Units.val_mul, weylPrime3_coe, coe_torusUnipotentPoint]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three]

private theorem coe_longWeyl3_mul_transposeInv3_dualPoint (k : ℤ) (y : v.adicCompletion ℚ) (β : (v.adicCompletion ℚ)ˣ)
    (x : v.adicCompletion ℚ) :
    ((longWeyl3 * transposeInv3 (iotaGL (diagUnitGL2 β) * lowerUnipotent21 x *
        (weylPrime3 * transposeInv3 (torusUnipotentPoint v k y))) : LocalGL3 v) :
          Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) =
      !![0, ratPrimeAt v ^ k, 0; 0, 0, 1;
        ((β : v.adicCompletion ℚ))⁻¹, ((β : v.adicCompletion ℚ))⁻¹ * y, -(((β : v.adicCompletion ℚ))⁻¹ * x)] := by
  rw [transposeInv3_mul, transposeInv3_mul, transposeInv3_mul, transposeInv3_transposeInv3, transposeInv3_weylPrime3,
    transposeInv3_lowerUnipotent21, transposeInv3_iotaGL_diagUnitGL2, Units.val_mul, Units.val_mul,
    coe_iotaGL_diagUnitGL2_inv_mul_upperUnipotent3, coe_weylPrime3_mul_torusUnipotentPoint, longWeyl3_coe]
  have hAB : (!![((β : v.adicCompletion ℚ))⁻¹, -(((β : v.adicCompletion ℚ))⁻¹ * x), 0; 0, 1, 0; 0, 0, 1] :
        Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) * !![1, y, 0; 0, 0, 1; 0, ratPrimeAt v ^ k, 0] =
      !![((β : v.adicCompletion ℚ))⁻¹, ((β : v.adicCompletion ℚ))⁻¹ * y, -(((β : v.adicCompletion ℚ))⁻¹ * x); 0, 0, 1;
        0, ratPrimeAt v ^ k, 0] := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three]
  rw [hAB]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three]

private theorem valued_zero_le_one' : Valued.v (0 : v.adicCompletion ℚ) ≤ 1 := by simp

private theorem valued_one_le_one' : Valued.v (1 : v.adicCompletion ℚ) ≤ 1 := by simp

private theorem valued_neg_le_one {z : v.adicCompletion ℚ} (h : Valued.v z ≤ 1) : Valued.v (-z) ≤ 1 := by
  rwa [Valuation.map_neg]

private theorem valued_mul_le_one {z w : v.adicCompletion ℚ} (hz : Valued.v z ≤ 1) (hw : Valued.v w ≤ 1) :
    Valued.v (z * w) ≤ 1 := by
  rw [map_mul]
  exact mul_le_one' hz hw

private theorem valued_inv_le_one_of_exp {z : v.adicCompletion ℚ} {e : ℤ} (hz : Valued.v z = WithZero.exp e)
    (he : 0 ≤ e) :
    Valued.v z⁻¹ ≤ 1 := by
  rw [map_inv₀, hz, ← WithZero.exp_neg, ← WithZero.exp_zero, WithZero.exp_le_exp]
  omega

private theorem valued_mul_inv_le_one_of_le {z w : v.adicCompletion ℚ} (hw : Valued.v w ≠ 0)
    (h : Valued.v z ≤ Valued.v w) :
    Valued.v (z * w⁻¹) ≤ 1 := by
  rw [map_mul, map_inv₀]
  calc Valued.v z * (Valued.v w)⁻¹ ≤ Valued.v w * (Valued.v w)⁻¹ := mul_le_mul' h le_rfl
    _ = 1 := mul_inv_cancel₀ hw

private theorem coe_diagGL_vec (u₁ u₂ u₃ : (v.adicCompletion ℚ)ˣ) :
    ((diagGL ![u₁, u₂, u₃] : LocalGL3 v) : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) =
      Matrix.diagonal ![(u₁ : v.adicCompletion ℚ), u₂, u₃] := by
  rw [coe_diagGL]
  congr 1
  funext i
  fin_cases i <;> rfl

private theorem kappa_of_le_of_eq_mem {y x : v.adicCompletion ℚ} (hy : Valued.v y ≤ 1) (hxi : Valued.v x⁻¹ ≤ 1)
    (hyx : Valued.v (y * x⁻¹) ≤ 1) :
    mkGL _ _ (kappaA_mul y x) (kappaA_mul' y x) ∈ localMaximalCompact3 (𝓞 ℚ) ℚ v := by
  rw [mem_localMaximalCompact3_iff, coe_mkGL, coe_mkGL_inv]
  exact ⟨forall_entries_of_literal (fun z => Valued.v z ≤ 1) valued_zero_le_one' valued_one_le_one' valued_zero_le_one'
      valued_one_le_one' hy valued_zero_le_one' (valued_neg_le_one hxi) (valued_neg_le_one hyx) valued_one_le_one',
    forall_entries_of_literal (fun z => Valued.v z ≤ 1) (valued_neg_le_one hy) valued_one_le_one' valued_zero_le_one'
      valued_one_le_one' valued_zero_le_one' valued_zero_le_one' valued_zero_le_one' hxi valued_one_le_one'⟩

private theorem dualPoint_eq_of_le_of_eq (k : ℤ) (y x : v.adicCompletion ℚ) (hx0 : x ≠ 0) (β : (v.adicCompletion ℚ)ˣ) :
    longWeyl3 * transposeInv3 (iotaGL (diagUnitGL2 β) * lowerUnipotent21 x *
        (weylPrime3 * transposeInv3 (torusUnipotentPoint v k y))) =
      upperUnipotent3 0 (-((β : v.adicCompletion ℚ) / x)) 0 *
        (diagGL ![ratPrimeUnit v ^ k, (Units.mk0 x hx0)⁻¹, -(Units.mk0 x hx0 * β⁻¹)] *
          mkGL _ _ (kappaA_mul y x) (kappaA_mul' y x)) := by
  refine Units.ext ?_
  rw [coe_longWeyl3_mul_transposeInv3_dualPoint, Units.val_mul, Units.val_mul, upperUnipotent3_coe, coe_diagGL_vec,
    coe_mkGL]
  exact factorA (ratPrimeAt v ^ k) (β : v.adicCompletion ℚ) x y _ _ _ hx0 β.ne_zero (coe_ratPrimeUnit_zpow k)
    (by rw [Units.val_inv_eq_inv_val, Units.val_mk0])
    (by rw [Units.val_neg, Units.val_mul, Units.val_mk0, Units.val_inv_eq_inv_val])

private theorem kappa_of_eq_of_le_mem {y x : v.adicCompletion ℚ} (hy0 : y ≠ 0) (hyi : Valued.v y⁻¹ ≤ 1)
    (hxi : Valued.v x⁻¹ ≤ 1) (hyx : Valued.v (y * x⁻¹) ≤ 1) :
    mkGL _ _ (kappaB_mul y x hy0) (kappaB_mul' y x hy0) ∈ localMaximalCompact3 (𝓞 ℚ) ℚ v := by
  rw [mem_localMaximalCompact3_iff, coe_mkGL, coe_mkGL_inv]
  exact ⟨forall_entries_of_literal (fun z => Valued.v z ≤ 1) valued_one_le_one' valued_zero_le_one' valued_zero_le_one'
      hyi valued_one_le_one' valued_zero_le_one' (valued_neg_le_one hxi) (valued_neg_le_one hyx) valued_one_le_one',
    forall_entries_of_literal (fun z => Valued.v z ≤ 1) valued_one_le_one' valued_zero_le_one' valued_zero_le_one'
      (valued_neg_le_one hyi) valued_one_le_one' valued_zero_le_one' valued_zero_le_one' hyx valued_one_le_one'⟩

private theorem dualPoint_eq_of_eq_of_le (k : ℤ) (y x : v.adicCompletion ℚ) (hy0 : y ≠ 0) (hx0 : x ≠ 0)
    (β : (v.adicCompletion ℚ)ˣ) :
    longWeyl3 * transposeInv3 (iotaGL (diagUnitGL2 β) * lowerUnipotent21 x *
        (weylPrime3 * transposeInv3 (torusUnipotentPoint v k y))) =
      upperUnipotent3 (ratPrimeAt v ^ k * x / y) (-((β : v.adicCompletion ℚ) / x)) 0 *
        (diagGL ![-(ratPrimeUnit v ^ k * (Units.mk0 y hy0)⁻¹), Units.mk0 y hy0 * (Units.mk0 x hx0)⁻¹,
            -(Units.mk0 x hx0 * β⁻¹)] *
          mkGL _ _ (kappaB_mul y x hy0) (kappaB_mul' y x hy0)) := by
  refine Units.ext ?_
  rw [coe_longWeyl3_mul_transposeInv3_dualPoint, Units.val_mul, Units.val_mul, upperUnipotent3_coe, coe_diagGL_vec,
    coe_mkGL]
  exact factorB (ratPrimeAt v ^ k) (β : v.adicCompletion ℚ) x y _ _ _ hx0 hy0 β.ne_zero
    (by rw [Units.val_neg, Units.val_mul, coe_ratPrimeUnit_zpow, Units.val_inv_eq_inv_val, Units.val_mk0])
    (by rw [Units.val_mul, Units.val_mk0, Units.val_inv_eq_inv_val, Units.val_mk0])
    (by rw [Units.val_neg, Units.val_mul, Units.val_mk0, Units.val_inv_eq_inv_val])

private theorem kappa_of_eq_of_lt_mem {y x : v.adicCompletion ℚ} (hyi : Valued.v y⁻¹ ≤ 1)
    (hxy : Valued.v (x * y⁻¹) ≤ 1) :
    mkGL _ _ (kappaC_mul y x) (kappaC_mul' y x) ∈ localMaximalCompact3 (𝓞 ℚ) ℚ v := by
  rw [mem_localMaximalCompact3_iff, coe_mkGL, coe_mkGL_inv]
  exact ⟨forall_entries_of_literal (fun z => Valued.v z ≤ 1) valued_one_le_one' valued_zero_le_one' valued_zero_le_one'
      valued_zero_le_one' valued_zero_le_one' valued_one_le_one' hyi valued_one_le_one' (valued_neg_le_one hxy),
    forall_entries_of_literal (fun z => Valued.v z ≤ 1) valued_one_le_one' valued_zero_le_one' valued_zero_le_one'
      (valued_neg_le_one hyi) hxy valued_one_le_one' valued_zero_le_one' valued_one_le_one' valued_zero_le_one'⟩

private theorem dualPoint_eq_of_eq_of_lt (k : ℤ) (y x : v.adicCompletion ℚ) (hy0 : y ≠ 0) (β : (v.adicCompletion ℚ)ˣ) :
    longWeyl3 * transposeInv3 (iotaGL (diagUnitGL2 β) * lowerUnipotent21 x *
        (weylPrime3 * transposeInv3 (torusUnipotentPoint v k y))) =
      upperUnipotent3 (ratPrimeAt v ^ k * x / y) 0 (ratPrimeAt v ^ k * (β : v.adicCompletion ℚ) / y) *
        (diagGL ![-(ratPrimeUnit v ^ k * (Units.mk0 y hy0)⁻¹), 1, Units.mk0 y hy0 * β⁻¹] *
          mkGL _ _ (kappaC_mul y x) (kappaC_mul' y x)) := by
  refine Units.ext ?_
  rw [coe_longWeyl3_mul_transposeInv3_dualPoint, Units.val_mul, Units.val_mul, upperUnipotent3_coe, coe_diagGL_vec,
    coe_mkGL]
  exact factorC (ratPrimeAt v ^ k) (β : v.adicCompletion ℚ) x y _ _ _ hy0 β.ne_zero
    (by rw [Units.val_neg, Units.val_mul, coe_ratPrimeUnit_zpow, Units.val_inv_eq_inv_val, Units.val_mk0])
    Units.val_one
    (by rw [Units.val_mul, Units.val_mk0, Units.val_inv_eq_inv_val])

end Helpers
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_laurent_localZeta_eq_gl3LFactorPoly_of_sphericalData.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_exists_laurent_localZeta_eq_gl3LFactorPoly_of_sphericalData.LanglandsTunnell.CubicInduction"

section Pointwise

variable {v : HeightOneSpectrum (𝓞 ℚ)} (W : LocalGL3 v → ℂ) (e₁ e₂ e₃ : ℂ)
  (hW : IsRightInvariant (localMaximalCompact3 (𝓞 ℚ) ℚ v) W ∧
    IsCosetEigenfunction (localMaximalCompact3 (𝓞 ℚ) ℚ v) (heckeGen1 v) W (cNormQ v * e₁) ∧
    IsCosetEigenfunction (localMaximalCompact3 (𝓞 ℚ) ℚ v) (heckeGen2 v) W (cNormQ v * e₂) ∧
    ∀ g : LocalGL3 v, W (centralGen v * g) = e₃ * W g)

include hW

private theorem apply_eq_zero_of_eq_zero (he₃ : e₃ = 0) (g : LocalGL3 v) : W g = 0 := by
  have h := hW.2.2.2 ((centralGen v)⁻¹ * g)
  rw [mul_inv_cancel_left, he₃, zero_mul] at h
  exact h

variable (hψ : IsGL3PsiWhittakerFn (psiLocal ℚ v) W) (he₃ : e₃ ≠ 0)

include hψ he₃

private theorem apply_eq_sphericalValue_of_coe_eq_diagonal (a : Fin 3 → (v.adicCompletion ℚ)ˣ) (lam : Fin 3 → ℤ)
    (hval : ∀ i, Valued.v (a i : v.adicCompletion ℚ) = WithZero.exp (-lam i)) (D : LocalGL3 v)
    (hD : (D : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) = Matrix.diagonal fun i => (a i : v.adicCompletion ℚ)) :
    W D = sphericalValue (W 1) e₁ e₂ e₃ (cNormQ v) lam := by
  by_cases h : lam 1 ≤ lam 0 ∧ lam 2 ≤ lam 1
  · rw [sphericalValue_of_le _ _ _ _ _ _ h.1 h.2]
    exact apply_eq_zpow_mul_of_coe_eq_diagonal_of_dominant v (psiLocal ℚ v) W e₁ e₂ e₃ hW hψ (psiLocal_rat_facts v).1
      (psiLocal_rat_facts v).2.1 he₃ a lam hval D hD h.1 h.2
  · rw [sphericalValue_of_not _ _ _ _ _ _ h]
    exact apply_eq_zero_of_coe_eq_diagonal_of_not_dominant v (psiLocal ℚ v) W hW.1 hψ (psiLocal_rat_facts v).2.1 a lam
      hval D hD (by omega)

private theorem apply_iotaGL_diagUnitGL2_mul_torusUnipotentPoint (k : ℤ) (y : v.adicCompletion ℚ) (n : ℤ)
    (α : (v.adicCompletion ℚ)ˣ) (hα : Valued.v (α : v.adicCompletion ℚ) = WithZero.exp (-n)) :
    W (iotaGL (diagUnitGL2 α) * torusUnipotentPoint v k y) =
      psiLocal ℚ v (((α * (ratPrimeUnit v ^ k)⁻¹ : (v.adicCompletion ℚ)ˣ) : v.adicCompletion ℚ) * y) *
        sphericalValue (W 1) e₁ e₂ e₃ (cNormQ v) ![n, k, 0] := by
  unfold torusUnipotentPoint
  rw [iotaGL_diagUnitGL2_mul_iotaGL_diagUnits2_mul_upperUnipotent3, hψ _ _ _ _, add_zero]
  congr 1
  refine apply_eq_sphericalValue_of_coe_eq_diagonal W e₁ e₂ e₃ hW hψ he₃ ![α, ratPrimeUnit v ^ k, 1] ![n, k, 0] ?_ _ ?_
  · intro i
    fin_cases i
    · show Valued.v (α : v.adicCompletion ℚ) = WithZero.exp (-n)
      exact hα
    · show Valued.v ((ratPrimeUnit v ^ k : (v.adicCompletion ℚ)ˣ) : v.adicCompletion ℚ) = WithZero.exp (-k)
      exact valued_coe_ratPrimeUnit_zpow k
    · show Valued.v ((1 : (v.adicCompletion ℚ)ˣ) : v.adicCompletion ℚ) = WithZero.exp (-(0 : ℤ))
      simp
  · rw [coe_iotaGL]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [embedMat2, diagUnits2, coe_ratPrimeUnit']

private theorem dualWhittakerFn3_apply_of_valued_le_of_valued_le (k : ℤ) (y : v.adicCompletion ℚ) (hy : Valued.v y ≤ 1)
    (n : ℤ) (β : (v.adicCompletion ℚ)ˣ) (hβ : Valued.v (β : v.adicCompletion ℚ) = WithZero.exp (-n))
    (x : v.adicCompletion ℚ) (hx : Valued.v x ≤ 1) :
    dualWhittakerFn3 W (iotaGL (diagUnitGL2 β) * lowerUnipotent21 x *
        (weylPrime3 * transposeInv3 (torusUnipotentPoint v k y))) =
      sphericalValue (W 1) e₁ e₂ e₃ (cNormQ v) ![k, 0, -n] := by
  have hκ : (!![0, 1, 0; 0, 0, 1; 1, y, -x] : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) *
      !![-y, x, 1; 1, 0, 0; 0, 1, 0] = 1 := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three]
  have hκ' : (!![-y, x, 1; 1, 0, 0; 0, 1, 0] : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) *
      !![0, 1, 0; 0, 0, 1; 1, y, -x] = 1 := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three]
  have hκK : mkGL _ _ hκ hκ' ∈ localMaximalCompact3 (𝓞 ℚ) ℚ v := by
    rw [mem_localMaximalCompact3_iff, coe_mkGL, coe_mkGL_inv]
    refine ⟨fun i j => ?_, fun i j => ?_⟩ <;> fin_cases i <;> fin_cases j <;> simp [hx, hy]
  have hfac : longWeyl3 * transposeInv3 (iotaGL (diagUnitGL2 β) * lowerUnipotent21 x *
      (weylPrime3 * transposeInv3 (torusUnipotentPoint v k y))) =
        diagGL ![ratPrimeUnit v ^ k, 1, β⁻¹] * mkGL _ _ hκ hκ' := by
    refine Units.ext ?_
    rw [coe_longWeyl3_mul_transposeInv3_dualPoint, Units.val_mul, coe_diagGL, coe_mkGL]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Matrix.diagonal_apply, coe_ratPrimeUnit']
  rw [dualWhittakerFn3_apply, hfac, hW.1 _ _ hκK]
  refine apply_eq_sphericalValue_of_coe_eq_diagonal W e₁ e₂ e₃ hW hψ he₃ _ _ ?_ _ (coe_diagGL _)
  intro i
  fin_cases i
  · show Valued.v ((ratPrimeUnit v ^ k : (v.adicCompletion ℚ)ˣ) : v.adicCompletion ℚ) = WithZero.exp (-k)
    exact valued_coe_ratPrimeUnit_zpow k
  · show Valued.v ((1 : (v.adicCompletion ℚ)ˣ) : v.adicCompletion ℚ) = WithZero.exp (-(0 : ℤ))
    simp
  · show Valued.v ((β⁻¹ : (v.adicCompletion ℚ)ˣ) : v.adicCompletion ℚ) = WithZero.exp (- -n)
    rw [Units.val_inv_eq_inv_val, map_inv₀, hβ, neg_neg, WithZero.exp_neg, inv_inv]

private theorem dualWhittakerFn3_apply_of_valued_le_of_valued_eq (k : ℤ) (y : v.adicCompletion ℚ) (hy : Valued.v y ≤ 1)
    (n : ℤ) (β : (v.adicCompletion ℚ)ˣ) (hβ : Valued.v (β : v.adicCompletion ℚ) = WithZero.exp (-n))
    (e : ℤ) (he : 1 ≤ e) (x : v.adicCompletion ℚ) (hx : Valued.v x = WithZero.exp e) :
    dualWhittakerFn3 W (iotaGL (diagUnitGL2 β) * lowerUnipotent21 x *
        (weylPrime3 * transposeInv3 (torusUnipotentPoint v k y))) =
      psiLocal ℚ v (-((β : v.adicCompletion ℚ) / x)) * sphericalValue (W 1) e₁ e₂ e₃ (cNormQ v) ![k, e, -(e + n)] := by
  have hx0 : x ≠ 0 := by
    rintro rfl
    simp at hx
    exact WithZero.exp_ne_zero hx.symm
  have hxi : Valued.v x⁻¹ ≤ 1 := valued_inv_le_one_of_exp hx (by omega)
  have hyx : Valued.v (y * x⁻¹) ≤ 1 := valued_mul_le_one hy hxi
  rw [dualWhittakerFn3_apply, dualPoint_eq_of_le_of_eq k y x hx0 β, hψ _ _ _ _, zero_add,
    hW.1 _ _ (kappa_of_le_of_eq_mem hy hxi hyx)]
  congr 1
  refine apply_eq_sphericalValue_of_coe_eq_diagonal W e₁ e₂ e₃ hW hψ he₃ _ _ ?_ _ (coe_diagGL _)
  intro i
  fin_cases i
  · show Valued.v ((ratPrimeUnit v ^ k : (v.adicCompletion ℚ)ˣ) : v.adicCompletion ℚ) = WithZero.exp (-k)
    exact valued_coe_ratPrimeUnit_zpow k
  · show Valued.v (((Units.mk0 x hx0)⁻¹ : (v.adicCompletion ℚ)ˣ) : v.adicCompletion ℚ) = WithZero.exp (-e)
    rw [Units.val_inv_eq_inv_val, Units.val_mk0, map_inv₀, hx, WithZero.exp_neg]
  · show Valued.v ((-(Units.mk0 x hx0 * β⁻¹) : (v.adicCompletion ℚ)ˣ) : v.adicCompletion ℚ) =
      WithZero.exp (- -(e + n))
    rw [Units.val_neg, Valuation.map_neg, Units.val_mul, Units.val_mk0, Units.val_inv_eq_inv_val, map_mul, map_inv₀,
      hx, hβ, neg_neg, WithZero.exp_add, WithZero.exp_neg, inv_inv]

private theorem dualWhittakerFn3_apply_of_valued_eq_of_le_valued (k : ℤ) (d : ℕ) (hd : 1 ≤ d) (y : v.adicCompletion ℚ)
    (hy : Valued.v y = WithZero.exp (d : ℤ)) (n : ℤ) (β : (v.adicCompletion ℚ)ˣ)
    (hβ : Valued.v (β : v.adicCompletion ℚ) = WithZero.exp (-n)) (e : ℤ) (hde : (d : ℤ) ≤ e) (x : v.adicCompletion ℚ)
    (hx : Valued.v x = WithZero.exp e) :
    dualWhittakerFn3 W (iotaGL (diagUnitGL2 β) * lowerUnipotent21 x *
        (weylPrime3 * transposeInv3 (torusUnipotentPoint v k y))) =
      psiLocal ℚ v (ratPrimeAt v ^ k * x / y - (β : v.adicCompletion ℚ) / x) *
        sphericalValue (W 1) e₁ e₂ e₃ (cNormQ v) ![k + d, e - d, -(e + n)] := by
  have hx0 : x ≠ 0 := by
    rintro rfl
    simp at hx
    exact WithZero.exp_ne_zero hx.symm
  have hy0 : y ≠ 0 := by
    rintro rfl
    simp at hy
    exact WithZero.exp_ne_zero hy.symm
  have hxi : Valued.v x⁻¹ ≤ 1 := valued_inv_le_one_of_exp hx (by omega)
  have hyi : Valued.v y⁻¹ ≤ 1 := valued_inv_le_one_of_exp hy (by omega)
  have hyx : Valued.v (y * x⁻¹) ≤ 1 := by
    refine valued_mul_inv_le_one_of_le (by rw [hx]; exact WithZero.exp_ne_zero) ?_
    rw [hx, hy, WithZero.exp_le_exp]
    exact hde
  rw [dualWhittakerFn3_apply, dualPoint_eq_of_eq_of_le k y x hy0 hx0 β, hψ _ _ _ _,
    hW.1 _ _ (kappa_of_eq_of_le_mem hy0 hyi hxi hyx), ← sub_eq_add_neg]
  congr 1
  refine apply_eq_sphericalValue_of_coe_eq_diagonal W e₁ e₂ e₃ hW hψ he₃ _ _ ?_ _ (coe_diagGL _)
  intro i
  fin_cases i
  · show Valued.v ((-(ratPrimeUnit v ^ k * (Units.mk0 y hy0)⁻¹) : (v.adicCompletion ℚ)ˣ) : v.adicCompletion ℚ) =
      WithZero.exp (-(k + d))
    rw [Units.val_neg, Valuation.map_neg, Units.val_mul, coe_ratPrimeUnit_zpow, Units.val_inv_eq_inv_val,
      Units.val_mk0,
      map_mul, map_inv₀, valued_ratPrimeAt_zpow, hy, ← WithZero.exp_neg, ← WithZero.exp_add, WithZero.exp_inj]
    ring
  · show Valued.v ((Units.mk0 y hy0 * (Units.mk0 x hx0)⁻¹ : (v.adicCompletion ℚ)ˣ) : v.adicCompletion ℚ) =
      WithZero.exp (-(e - d))
    rw [Units.val_mul, Units.val_inv_eq_inv_val, Units.val_mk0, Units.val_mk0, map_mul, map_inv₀, hx, hy,
      ← WithZero.exp_neg, ← WithZero.exp_add, WithZero.exp_inj]
    ring
  · show Valued.v ((-(Units.mk0 x hx0 * β⁻¹) : (v.adicCompletion ℚ)ˣ) : v.adicCompletion ℚ) =
      WithZero.exp (- -(e + n))
    rw [Units.val_neg, Valuation.map_neg, Units.val_mul, Units.val_mk0, Units.val_inv_eq_inv_val, map_mul, map_inv₀,
      hx, hβ, neg_neg, WithZero.exp_add, WithZero.exp_neg, inv_inv]

private theorem dualWhittakerFn3_apply_of_valued_eq_of_valued_lt (k : ℤ) (d : ℕ) (hd : 1 ≤ d) (y : v.adicCompletion ℚ)
    (hy : Valued.v y = WithZero.exp (d : ℤ)) (n : ℤ) (β : (v.adicCompletion ℚ)ˣ)
    (hβ : Valued.v (β : v.adicCompletion ℚ) = WithZero.exp (-n)) (x : v.adicCompletion ℚ)
    (hx : Valued.v x < WithZero.exp (d : ℤ)) :
    dualWhittakerFn3 W (iotaGL (diagUnitGL2 β) * lowerUnipotent21 x *
        (weylPrime3 * transposeInv3 (torusUnipotentPoint v k y))) =
      psiLocal ℚ v (ratPrimeAt v ^ k * x / y) * sphericalValue (W 1) e₁ e₂ e₃ (cNormQ v) ![k + d, 0, -(d + n)] := by
  have hy0 : y ≠ 0 := by
    rintro rfl
    simp at hy
    exact WithZero.exp_ne_zero hy.symm
  have hyi : Valued.v y⁻¹ ≤ 1 := valued_inv_le_one_of_exp hy (by omega)
  have hxy : Valued.v (x * y⁻¹) ≤ 1 :=
    valued_mul_inv_le_one_of_le (by rw [hy]; exact WithZero.exp_ne_zero) (by rw [hy]; exact hx.le)
  rw [dualWhittakerFn3_apply, dualPoint_eq_of_eq_of_lt k y x hy0 β, hψ _ _ _ _, add_zero,
    hW.1 _ _ (kappa_of_eq_of_lt_mem hyi hxy)]
  congr 1
  refine apply_eq_sphericalValue_of_coe_eq_diagonal W e₁ e₂ e₃ hW hψ he₃ _ _ ?_ _ (coe_diagGL _)
  intro i
  fin_cases i
  · show Valued.v ((-(ratPrimeUnit v ^ k * (Units.mk0 y hy0)⁻¹) : (v.adicCompletion ℚ)ˣ) : v.adicCompletion ℚ) =
      WithZero.exp (-(k + d))
    rw [Units.val_neg, Valuation.map_neg, Units.val_mul, coe_ratPrimeUnit_zpow, Units.val_inv_eq_inv_val,
      Units.val_mk0,
      map_mul, map_inv₀, valued_ratPrimeAt_zpow, hy, ← WithZero.exp_neg, ← WithZero.exp_add, WithZero.exp_inj]
    ring
  · show Valued.v ((1 : (v.adicCompletion ℚ)ˣ) : v.adicCompletion ℚ) = WithZero.exp (-(0 : ℤ))
    simp
  · show Valued.v ((Units.mk0 y hy0 * β⁻¹ : (v.adicCompletion ℚ)ˣ) : v.adicCompletion ℚ) =
      WithZero.exp (- -(d + n))
    rw [Units.val_mul, Units.val_mk0, Units.val_inv_eq_inv_val, map_mul, map_inv₀, hy, hβ, neg_neg, WithZero.exp_add,
      WithZero.exp_neg, inv_inv]

end Pointwise
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_laurent_localZeta_eq_gl3LFactorPoly_of_sphericalData.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_exists_laurent_localZeta_eq_gl3LFactorPoly_of_sphericalData.LanglandsTunnell.CubicInduction"

end
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_laurent_localZeta_eq_gl3LFactorPoly_of_sphericalData.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_exists_laurent_localZeta_eq_gl3LFactorPoly_of_sphericalData.LanglandsTunnell.CubicInduction"
end
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_laurent_localZeta_eq_gl3LFactorPoly_of_sphericalData.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_exists_laurent_localZeta_eq_gl3LFactorPoly_of_sphericalData.LanglandsTunnell.CubicInduction"

section

set_option autoImplicit false

open IsDedekindDomain NumberField NumberField.TateGlobal AutomorphicForm LanglandsTunnell.Converse LanglandsTunnell.RankinSelberg LanglandsTunnell.TateLocal MeasureTheory

p2m_open "IsDedekindDomain.HeightOneSpectrum~Extension LanglandsTunnell.CubicInduction P2MW.S_LanglandsTunnell_CubicInduction_exists_laurent_localZeta_eq_gl3LFactorPoly_of_sphericalData.LanglandsTunnell.CubicInduction NumberField.StandardAddChar"

noncomputable section

section UnramifiedAtoms

variable {v : HeightOneSpectrum (𝓞 ℚ)}

private theorem cNormQ_eq (v : HeightOneSpectrum (𝓞 ℚ)) : cNormQ v = (Ideal.absNorm v.asIdeal : ℂ) := rfl

private theorem absNorm_real_pos (v : HeightOneSpectrum (𝓞 ℚ)) : (0 : ℝ) < (Ideal.absNorm v.asIdeal : ℝ) := by
  have h := one_lt_absNorm v
  exact_mod_cast (show 0 < Ideal.absNorm v.asIdeal by omega)

private theorem coe_ratPrimeUnit_eq (v : HeightOneSpectrum (𝓞 ℚ)) :
    ((ratPrimeUnit v : (v.adicCompletion ℚ)ˣ) : v.adicCompletion ℚ) = ratPrimeAt v := rfl

private theorem valued_ratPrimeUnit_zpow (v : HeightOneSpectrum (𝓞 ℚ)) (m : ℤ) :
    Valued.v ((ratPrimeUnit v ^ m : (v.adicCompletion ℚ)ˣ) : v.adicCompletion ℚ) = WithZero.exp (-m) := by
  have h1 : Valued.v (ratPrimeAt v) = WithZero.exp (-1 : ℤ) := by
    rw [valued_ratPrimeAt_eq_valued_varpi]
    exact AdelicLevel.valued_uniformizerUnit ℚ v
  rw [Units.val_zpow_eq_zpow_val, coe_ratPrimeUnit_eq, map_zpow₀, h1, ← WithZero.exp_zsmul]
  congr 1
  simp

private theorem ratPrimeUnit_zpow_mem_unitShell (v : HeightOneSpectrum (𝓞 ℚ)) (n : ℤ) :
    ratPrimeUnit v ^ n ∈ unitShell v n :=
  show Valued.v ((ratPrimeUnit v ^ n : (v.adicCompletion ℚ)ˣ) : v.adicCompletion ℚ) = WithZero.exp (-n) from
    valued_ratPrimeUnit_zpow v n

private theorem psiLocal_level_zero_left (v : HeightOneSpectrum (𝓞 ℚ)) :
    ∀ x : v.adicCompletion ℚ, Valued.v x ≤ 1 → psiLocal ℚ v x = 1 :=
  psiLocal_rat_apply_eq_one_of_valued_le_one v

private theorem psiLocal_level_zero_right (v : HeightOneSpectrum (𝓞 ℚ)) :
    ∃ x : v.adicCompletion ℚ, Valued.v x ≤ WithZero.exp 1 ∧ psiLocal ℚ v x ≠ 1 := by
  obtain ⟨x, hx, hne⟩ := exists_valued_le_one_and_psiLocal_rat_varpi_inv_mul_ne_one v
  have hϖ : Valued.v (varpi v) = WithZero.exp (-1 : ℤ) := AdelicLevel.valued_uniformizerUnit ℚ v
  refine ⟨(varpi v)⁻¹ * x, ?_, hne⟩
  rw [map_mul, map_inv₀, hϖ, ← WithZero.exp_neg, neg_neg]
  exact mul_le_of_le_one_right' hx

private theorem valued_ratPrimeUnit_zpow_mul (v : HeightOneSpectrum (𝓞 ℚ)) (n k : ℤ) {d : ℕ}
    {y : v.adicCompletion ℚ} (hy : Valued.v y = WithZero.exp (d : ℤ)) :
    Valued.v (((ratPrimeUnit v ^ (n - k) : (v.adicCompletion ℚ)ˣ) : v.adicCompletion ℚ) * y) =
      WithZero.exp (k + d - n) := by
  rw [map_mul, valued_ratPrimeUnit_zpow, hy, ← WithZero.exp_add]
  congr 1
  ring

private theorem modulus_cpow_of_mem_unitShell (v : HeightOneSpectrum (𝓞 ℚ)) {n : ℤ} {α : (v.adicCompletion ℚ)ˣ}
    (hα : α ∈ unitShell v n) (s : ℂ) :
    ((LanglandsTunnell.TateLocal.modulus (α : v.adicCompletion ℚ) : ℝ) : ℂ) ^ (s - 1) =
      Complex.exp ((-n : ℂ) * Real.log (Ideal.absNorm v.asIdeal : ℝ) * (s - 1)) := by
  have hq := absNorm_real_pos v
  have hmod : (LanglandsTunnell.TateLocal.modulus (α : v.adicCompletion ℚ) : ℝ) =
      (Ideal.absNorm v.asIdeal : ℝ) ^ (-n) := by
    rw [modulus_eq_zpow_of_valued v (show Valued.v (α : v.adicCompletion ℚ) = WithZero.exp (-n) from hα),
      NNReal.coe_zpow, NNReal.coe_natCast]
  have hpos : (0 : ℝ) < (Ideal.absNorm v.asIdeal : ℝ) ^ (-n) := zpow_pos hq _
  rw [hmod, Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hpos.ne'), ← Complex.ofReal_log hpos.le,
    Real.log_zpow]
  congr 1
  push_cast
  ring

private theorem inv_pow_mul_exp_eq (v : HeightOneSpectrum (𝓞 ℚ)) (n : ℕ) (s : ℂ) :
    (Ideal.absNorm v.asIdeal : ℂ)⁻¹ ^ n *
        Complex.exp ((-((n : ℤ) : ℂ)) * Real.log (Ideal.absNorm v.asIdeal : ℝ) * (s - 1)) =
      ((Ideal.absNorm v.asIdeal : ℂ) ^ (-s)) ^ n := by
  have hq := absNorm_real_pos v
  have hne : ((Ideal.absNorm v.asIdeal : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hq.ne'
  have hq' : ((Ideal.absNorm v.asIdeal : ℝ) : ℂ) = Complex.exp (Real.log (Ideal.absNorm v.asIdeal : ℝ) : ℂ) := by
    rw [Complex.ofReal_log hq.le, Complex.exp_log hne]
  rw [← Complex.ofReal_natCast, Complex.cpow_def_of_ne_zero hne, ← Complex.ofReal_log hq.le, ← Complex.exp_nat_mul]
  conv_lhs => rw [hq', ← Complex.exp_neg, ← Complex.exp_nat_mul, ← Complex.exp_add]
  congr 1
  push_cast
  ring

open Function in
private theorem pairwise_disjoint_unitShell (v : HeightOneSpectrum (𝓞 ℚ)) : Pairwise (Disjoint on unitShell v) :=
  fun _ _ hij => Set.disjoint_left.mpr fun α hi hj => hij ((existsUnique_mem_unitShell v α).unique hi hj)

private theorem summable_setIntegral_unitShell (v : HeightOneSpectrum (𝓞 ℚ)) (F : (v.adicCompletion ℚ)ˣ → ℂ)
    (hF : letI := localBorel ℚ v; Integrable F (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ v)))) :
    letI := localBorel ℚ v
    Summable fun n : ℤ => ∫ α in unitShell v n, F α ∂(Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ v))) := by
  letI := localBorel ℚ v
  exact (hasSum_integral_iUnion (measurableSet_unitShell v) (pairwise_disjoint_unitShell v) hF.integrableOn).summable

private theorem gaussIntegral_unramified_of_le_one {χ : (v.adicCompletion ℚ)ˣ →* ℂˣ}
    (hχ0 : HasConductorExponentAt ℚ v χ 0) {c : v.adicCompletion ℚ} (hc : Valued.v c ≤ 1) :
    letI := localBorel ℚ v
    gaussIntegral v (psiLocal ℚ v) χ c =
      (((1 - (Ideal.absNorm v.asIdeal : ℝ)⁻¹) *
        (selfDualHaarAt ℚ v).real (v.adicCompletionIntegers ℚ : Set (v.adicCompletion ℚ)) : ℝ) : ℂ) := by
  letI := localBorel ℚ v
  rw [gaussIntegral_of_hasConductorExponentAt_zero v (psiLocal ℚ v) hχ0 c,
    setIntegral_unitSet_addChar_of_valued_le_one (psiLocal_level_zero_left v) hc]
  push_cast
  rfl

private theorem gaussIntegral_unramified_of_eq_exp_one {χ : (v.adicCompletion ℚ)ˣ →* ℂˣ}
    (hχ0 : HasConductorExponentAt ℚ v χ 0) {c : v.adicCompletion ℚ} (hc : Valued.v c = WithZero.exp 1) :
    letI := localBorel ℚ v
    gaussIntegral v (psiLocal ℚ v) χ c =
      ((-((Ideal.absNorm v.asIdeal : ℝ)⁻¹ *
        (selfDualHaarAt ℚ v).real (v.adicCompletionIntegers ℚ : Set (v.adicCompletion ℚ))) : ℝ) : ℂ) := by
  letI := localBorel ℚ v
  rw [gaussIntegral_of_hasConductorExponentAt_zero v (psiLocal ℚ v) hχ0 c,
    setIntegral_unitSet_addChar_of_valued_eq_exp_one (psiLocal_level_zero_left v) (psiLocal_level_zero_right v) hc]
  push_cast
  rfl

private theorem gaussIntegral_unramified_of_exp_one_lt {χ : (v.adicCompletion ℚ)ˣ →* ℂˣ}
    (hχ0 : HasConductorExponentAt ℚ v χ 0) {c : v.adicCompletion ℚ} (hc : WithZero.exp 1 < Valued.v c) :
    letI := localBorel ℚ v
    gaussIntegral v (psiLocal ℚ v) χ c = 0 := by
  letI := localBorel ℚ v
  rw [gaussIntegral_of_hasConductorExponentAt_zero v (psiLocal ℚ v) hχ0 c,
    setIntegral_unitSet_addChar_of_exp_one_lt (psiLocal_level_zero_left v) (psiLocal_level_zero_right v) hc]

private theorem gaussIntegral_ramified_of_ne {χ : (v.adicCompletion ℚ)ˣ →* ℂˣ} {a : ℕ} (ha : 1 ≤ a)
    (hχa : HasConductorExponentAt ℚ v χ a) {c : v.adicCompletion ℚ} (hc : Valued.v c ≠ WithZero.exp (a : ℤ)) :
    gaussIntegral v (psiLocal ℚ v) χ c = 0 :=
  gaussIntegral_eq_zero_of_valued_ne (psiLocal_level_zero_left v) (psiLocal_level_zero_right v) ha hχa hc

private theorem vec_zero (n k : ℤ) : (![n, k, 0] : Fin 3 → ℤ) 0 = n := rfl
private theorem vec_one (n k : ℤ) : (![n, k, 0] : Fin 3 → ℤ) 1 = k := rfl
private theorem vec_two (n k : ℤ) : (![n, k, 0] : Fin 3 → ℤ) 2 = 0 := rfl

private theorem sphericalValue_nat (W1 e₁ e₂ e₃ : ℂ) (v : HeightOneSpectrum (𝓞 ℚ)) {n k : ℕ} (hkn : k ≤ n) :
    sphericalValue W1 e₁ e₂ e₃ (cNormQ v) ![(n : ℤ), (k : ℤ), 0] =
      W1 * ((Ideal.absNorm v.asIdeal : ℂ)⁻¹ ^ n * twoRowCoeff e₁ e₂ e₃ n k) := by
  have h01 : ((k : ℤ)) ≤ (n : ℤ) := by exact_mod_cast hkn
  have h12 : (0 : ℤ) ≤ (k : ℤ) := by exact_mod_cast k.zero_le
  rw [sphericalValue_of_le W1 e₁ e₂ e₃ (cNormQ v) ![(n : ℤ), (k : ℤ), 0] h01 h12, vec_zero, vec_one, vec_two,
    zpow_zero, one_mul, sub_zero, sub_zero, Int.toNat_natCast, Int.toNat_natCast, cNormQ_eq]

private theorem sphericalValue_eq_zero (W1 e₁ e₂ e₃ : ℂ) (v : HeightOneSpectrum (𝓞 ℚ)) {n k : ℤ}
    (h : n < k ∨ k < 0) : sphericalValue W1 e₁ e₂ e₃ (cNormQ v) ![n, k, 0] = 0 :=
  sphericalValue_of_not W1 e₁ e₂ e₃ (cNormQ v) ![n, k, 0] fun hdom => by
    have h1 : k ≤ n := hdom.1
    have h2 : (0 : ℤ) ≤ k := hdom.2
    omega

private theorem tsum_int_eq (g : ℤ → ℂ) (hg : Summable g) (N : ℕ) (h0 : ∀ n : ℤ, n < (N : ℤ) - 1 → g n = 0) :
    ∑' n : ℤ, g n = g ((N : ℤ) - 1) + ∑' m : ℕ, g ((N + m : ℕ) : ℤ) := by
  have hinj : Function.Injective fun j : ℕ => (N : ℤ) - 1 + j := fun a b h => by
    have h' : (N : ℤ) - 1 + (a : ℤ) = (N : ℤ) - 1 + (b : ℤ) := h
    omega
  have hsupp : Function.support g ⊆ Set.range fun j : ℕ => (N : ℤ) - 1 + j := by
    intro n hn
    have hle : (N : ℤ) - 1 ≤ n := by
      by_contra hlt
      exact Function.mem_support.mp hn (h0 n (by omega))
    refine ⟨(n - ((N : ℤ) - 1)).toNat, ?_⟩
    show (N : ℤ) - 1 + (((n - ((N : ℤ) - 1)).toNat : ℕ) : ℤ) = n
    rw [Int.toNat_of_nonneg (by omega)]
    ring
  rw [← hinj.tsum_eq hsupp, tsum_eq_zero_add']
  · congr 1
    · congr 1
      simp
    · exact tsum_congr fun j => congrArg g (by push_cast; ring)
  · exact hg.comp_injective fun a b h => by
      have h' : (N : ℤ) - 1 + ((a + 1 : ℕ) : ℤ) = (N : ℤ) - 1 + ((b + 1 : ℕ) : ℤ) := h
      omega

end UnramifiedAtoms
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_laurent_localZeta_eq_gl3LFactorPoly_of_sphericalData.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_exists_laurent_localZeta_eq_gl3LFactorPoly_of_sphericalData.LanglandsTunnell.CubicInduction"

section Values

variable {v : HeightOneSpectrum (𝓞 ℚ)} (W : LocalGL3 v → ℂ) (e₁ e₂ e₃ : ℂ)
  (hW : IsRightInvariant (localMaximalCompact3 (𝓞 ℚ) ℚ v) W ∧
    IsCosetEigenfunction (localMaximalCompact3 (𝓞 ℚ) ℚ v) (heckeGen1 v) W (cNormQ v * e₁) ∧
    IsCosetEigenfunction (localMaximalCompact3 (𝓞 ℚ) ℚ v) (heckeGen2 v) W (cNormQ v * e₂) ∧
    ∀ g : LocalGL3 v, W (centralGen v * g) = e₃ * W g)
  (hψ : IsGL3PsiWhittakerFn (psiLocal ℚ v) W) (χ : (v.adicCompletion ℚ)ˣ →* ℂˣ)

include hW hψ

private theorem setIntegral_unitShell_integrand (he₃ : e₃ ≠ 0) (k : ℤ) (y : v.adicCompletion ℚ) (s : ℂ) (n : ℤ) :
    letI := localBorel ℚ v
    ∫ α in unitShell v n,
        W (iotaGL (diagUnitGL2 α) * torusUnipotentPoint v k y) * ((χ α : ℂˣ) : ℂ) *
          ((LanglandsTunnell.TateLocal.modulus (α : v.adicCompletion ℚ) : ℝ) : ℂ) ^ (s - 1)
        ∂(Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ v))) =
      sphericalValue (W 1) e₁ e₂ e₃ (cNormQ v) ![n, k, 0] *
          Complex.exp ((-n : ℂ) * Real.log (Ideal.absNorm v.asIdeal : ℝ) * (s - 1)) *
          ((χ (ratPrimeUnit v ^ n) : ℂˣ) : ℂ) *
        gaussIntegral v (psiLocal ℚ v) χ
          (((ratPrimeUnit v ^ (n - k) : (v.adicCompletion ℚ)ˣ) : v.adicCompletion ℚ) * y) := by
  letI := localBorel ℚ v
  have h1 : ∫ α in unitShell v n,
      W (iotaGL (diagUnitGL2 α) * torusUnipotentPoint v k y) * ((χ α : ℂˣ) : ℂ) *
        ((LanglandsTunnell.TateLocal.modulus (α : v.adicCompletion ℚ) : ℝ) : ℂ) ^ (s - 1)
      ∂(Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ v))) =
      ∫ α in unitShell v n,
        (sphericalValue (W 1) e₁ e₂ e₃ (cNormQ v) ![n, k, 0] *
            Complex.exp ((-n : ℂ) * Real.log (Ideal.absNorm v.asIdeal : ℝ) * (s - 1))) *
          (psiLocal ℚ v (((α * (ratPrimeUnit v ^ k)⁻¹ : (v.adicCompletion ℚ)ˣ) : v.adicCompletion ℚ) * y) *
            ((χ α : ℂˣ) : ℂ))
        ∂(Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ v))) := by
    refine setIntegral_congr_fun (measurableSet_unitShell v n) fun α hα => ?_
    rw [apply_iotaGL_diagUnitGL2_mul_torusUnipotentPoint W e₁ e₂ e₃ hW hψ he₃ k y n α
        (show Valued.v (α : v.adicCompletion ℚ) = WithZero.exp (-n) from hα),
      modulus_cpow_of_mem_unitShell v hα s]
    ring
  have h2 : ∫ α in unitShell v n,
      psiLocal ℚ v (((α * (ratPrimeUnit v ^ k)⁻¹ : (v.adicCompletion ℚ)ˣ) : v.adicCompletion ℚ) * y) *
        ((χ α : ℂˣ) : ℂ) ∂(Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ v))) =
      ((χ (ratPrimeUnit v ^ n) : ℂˣ) : ℂ) *
        gaussIntegral v (psiLocal ℚ v) χ
          (((ratPrimeUnit v ^ (n - k) : (v.adicCompletion ℚ)ˣ) : v.adicCompletion ℚ) * y) := by
    rw [setIntegral_unitShell_eq_setIntegral_unitShell_zero v _ (ratPrimeUnit_zpow_mem_unitShell v n),
      gaussIntegral_eq_setIntegral_unitShell_zero v (psiLocal ℚ v) χ, ← integral_const_mul]
    refine setIntegral_congr_fun (measurableSet_unitShell v 0) fun β _ => ?_
    rw [show (ratPrimeUnit v ^ n * β * (ratPrimeUnit v ^ k)⁻¹ : (v.adicCompletion ℚ)ˣ) =
          ratPrimeUnit v ^ (n - k) * β by rw [zpow_sub, mul_right_comm],
      map_mul χ, Units.val_mul, Units.val_mul,
      mul_right_comm ((ratPrimeUnit v ^ (n - k) : (v.adicCompletion ℚ)ˣ) : v.adicCompletion ℚ)
        (β : v.adicCompletion ℚ) y]
    ring
  rw [h1, integral_const_mul, h2]
  ring

private theorem setIntegral_unitShell_eq_zero (he₃ : e₃ ≠ 0) {n k : ℤ} (h : n < k ∨ k < 0) (y : v.adicCompletion ℚ)
    (s : ℂ) :
    letI := localBorel ℚ v
    ∫ α in unitShell v n,
        W (iotaGL (diagUnitGL2 α) * torusUnipotentPoint v k y) * ((χ α : ℂˣ) : ℂ) *
          ((LanglandsTunnell.TateLocal.modulus (α : v.adicCompletion ℚ) : ℝ) : ℂ) ^ (s - 1)
        ∂(Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ v))) = 0 := by
  letI := localBorel ℚ v
  rw [setIntegral_unitShell_integrand W e₁ e₂ e₃ hW hψ χ he₃ k y s n, sphericalValue_eq_zero (W 1) e₁ e₂ e₃ v h,
    zero_mul, zero_mul, zero_mul]

private theorem setIntegral_unitShell_natCast (he₃ : e₃ ≠ 0) {m k : ℕ} (hkm : k ≤ m) (y : v.adicCompletion ℚ)
    (s : ℂ) :
    letI := localBorel ℚ v
    ∫ α in unitShell v m,
        W (iotaGL (diagUnitGL2 α) * torusUnipotentPoint v k y) * ((χ α : ℂˣ) : ℂ) *
          ((LanglandsTunnell.TateLocal.modulus (α : v.adicCompletion ℚ) : ℝ) : ℂ) ^ (s - 1)
        ∂(Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ v))) =
      W 1 * twoRowCoeff e₁ e₂ e₃ m k *
          (((χ (ratPrimeUnit v) : ℂˣ) : ℂ) * (Ideal.absNorm v.asIdeal : ℂ) ^ (-s)) ^ m *
        gaussIntegral v (psiLocal ℚ v) χ
          (((ratPrimeUnit v ^ ((m : ℤ) - (k : ℤ)) : (v.adicCompletion ℚ)ˣ) : v.adicCompletion ℚ) * y) := by
  letI := localBorel ℚ v
  rw [setIntegral_unitShell_integrand W e₁ e₂ e₃ hW hψ χ he₃ k y s m, sphericalValue_nat (W 1) e₁ e₂ e₃ v hkm,
    zpow_natCast, map_pow, Units.val_pow_eq_pow_val, mul_pow, ← inv_pow_mul_exp_eq v m s]
  ring

private theorem localZeta30_torusUnipotentPoint_of_neg (k : ℤ) (hk : k < 0) (y : v.adicCompletion ℚ) (s : ℂ) :
    letI := localBorel ℚ v
    localZeta30 v (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ v))) W χ s (torusUnipotentPoint v k y) =
      0 := by
  letI := localBorel ℚ v
  by_cases he₃ : e₃ = 0
  · have hW0 := apply_eq_zero_of_eq_zero W e₁ e₂ e₃ hW he₃
    simp only [localZeta30, hW0, zero_mul, integral_zero]
  · have h : ∀ α : (v.adicCompletion ℚ)ˣ, W (iotaGL (diagUnitGL2 α) * torusUnipotentPoint v k y) = 0 := fun α => by
      rw [apply_iotaGL_diagUnitGL2_mul_torusUnipotentPoint W e₁ e₂ e₃ hW hψ he₃ k y (unitShellIndex v α) α
          (show Valued.v (α : v.adicCompletion ℚ) = WithZero.exp (-unitShellIndex v α) from
            mem_unitShell_unitShellIndex v α),
        sphericalValue_eq_zero (W 1) e₁ e₂ e₃ v (Or.inr hk), mul_zero]
    simp only [localZeta30, h, zero_mul, integral_zero]

private theorem localZeta30_torusUnipotentPoint_of_hasConductorExponentAt_zero (hχ0 : HasConductorExponentAt ℚ v χ 0)
    (t : ℂ) (ht : t = ((χ (NumberField.AdelicLevel.uniformizerUnit ℚ v) : ℂˣ) : ℂ)) (k d : ℕ)
    (y : v.adicCompletion ℚ) (hy : Valued.v y = WithZero.exp (d : ℤ)) (s : ℂ)
    (hint : letI := localBorel ℚ v
      Integrable (fun α : (v.adicCompletion ℚ)ˣ =>
        W (iotaGL (diagUnitGL2 α) * torusUnipotentPoint v k y) * ((χ α : ℂˣ) : ℂ) *
          ((LanglandsTunnell.TateLocal.modulus (α : v.adicCompletion ℚ) : ℝ) : ℂ) ^ (s - 1))
        (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ v)))) :
    letI := localBorel ℚ v
    localZeta30 v (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ v))) W χ s (torusUnipotentPoint v k y) =
      W 1 * (((selfDualHaarAt ℚ v).real (v.adicCompletionIntegers ℚ : Set (v.adicCompletion ℚ)) : ℂ) *
          (1 - (Ideal.absNorm v.asIdeal : ℂ)⁻¹) *
          ∑' m : ℕ, twoRowCoeff e₁ e₂ e₃ (k + d + m) k * (t * (Ideal.absNorm v.asIdeal : ℂ) ^ (-s)) ^ (k + d + m) -
        if 1 ≤ d then
          ((selfDualHaarAt ℚ v).real (v.adicCompletionIntegers ℚ : Set (v.adicCompletion ℚ)) : ℂ) *
            (Ideal.absNorm v.asIdeal : ℂ)⁻¹ * twoRowCoeff e₁ e₂ e₃ (k + d - 1) k *
            (t * (Ideal.absNorm v.asIdeal : ℂ) ^ (-s)) ^ (k + d - 1)
        else 0) := by
  letI := localBorel ℚ v
  by_cases he₃ : e₃ = 0
  · have hW0 := apply_eq_zero_of_eq_zero W e₁ e₂ e₃ hW he₃
    simp only [localZeta30, hW0, zero_mul, integral_zero]
  · have hχp : ((χ (ratPrimeUnit v) : ℂˣ) : ℂ) = t := coe_apply_ratPrimeUnit_eq v χ hχ0 t ht

    have hterm : ∀ m : ℕ,
        ∫ α in unitShell v ((k + d + m : ℕ) : ℤ),
            W (iotaGL (diagUnitGL2 α) * torusUnipotentPoint v k y) * ((χ α : ℂˣ) : ℂ) *
              ((LanglandsTunnell.TateLocal.modulus (α : v.adicCompletion ℚ) : ℝ) : ℂ) ^ (s - 1)
            ∂(Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ v))) =
          (W 1 * (((1 - (Ideal.absNorm v.asIdeal : ℝ)⁻¹) *
              (selfDualHaarAt ℚ v).real (v.adicCompletionIntegers ℚ : Set (v.adicCompletion ℚ)) : ℝ) : ℂ)) *
            (twoRowCoeff e₁ e₂ e₃ (k + d + m) k * (t * (Ideal.absNorm v.asIdeal : ℂ) ^ (-s)) ^ (k + d + m)) := by
      intro m
      rw [setIntegral_unitShell_natCast W e₁ e₂ e₃ hW hψ χ he₃ (by omega : k ≤ k + d + m) y s, hχp,
        gaussIntegral_unramified_of_le_one hχ0]
      · ring
      · rw [valued_ratPrimeUnit_zpow_mul v _ _ hy, ← WithZero.exp_zero, WithZero.exp_le_exp]
        omega

    have hpeel :
        ∫ α in unitShell v ((k + d : ℕ) - 1 : ℤ),
            W (iotaGL (diagUnitGL2 α) * torusUnipotentPoint v k y) * ((χ α : ℂˣ) : ℂ) *
              ((LanglandsTunnell.TateLocal.modulus (α : v.adicCompletion ℚ) : ℝ) : ℂ) ^ (s - 1)
            ∂(Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ v))) =
          if 1 ≤ d then
            W 1 * twoRowCoeff e₁ e₂ e₃ (k + d - 1) k * (t * (Ideal.absNorm v.asIdeal : ℂ) ^ (-s)) ^ (k + d - 1) *
              ((-((Ideal.absNorm v.asIdeal : ℝ)⁻¹ *
                (selfDualHaarAt ℚ v).real (v.adicCompletionIntegers ℚ : Set (v.adicCompletion ℚ))) : ℝ) : ℂ)
          else 0 := by
      by_cases hd : 1 ≤ d
      · rw [if_pos hd, show ((k + d : ℕ) - 1 : ℤ) = ((k + d - 1 : ℕ) : ℤ) by omega,
          setIntegral_unitShell_natCast W e₁ e₂ e₃ hW hψ χ he₃ (by omega : k ≤ k + d - 1) y s, hχp,
          gaussIntegral_unramified_of_eq_exp_one hχ0]
        rw [valued_ratPrimeUnit_zpow_mul v _ _ hy]
        congr 1
        omega
      · rw [if_neg hd]
        exact setIntegral_unitShell_eq_zero W e₁ e₂ e₃ hW hψ χ he₃ (Or.inl (by omega)) y s

    have hbelow : ∀ n : ℤ, n < ((k + d : ℕ) : ℤ) - 1 →
        ∫ α in unitShell v n,
            W (iotaGL (diagUnitGL2 α) * torusUnipotentPoint v k y) * ((χ α : ℂˣ) : ℂ) *
              ((LanglandsTunnell.TateLocal.modulus (α : v.adicCompletion ℚ) : ℝ) : ℂ) ^ (s - 1)
            ∂(Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ v))) = 0 := by
      intro n hn
      by_cases hnk : n < k
      · exact setIntegral_unitShell_eq_zero W e₁ e₂ e₃ hW hψ χ he₃ (Or.inl hnk) y s
      · obtain ⟨m, rfl⟩ : ∃ m : ℕ, n = (m : ℤ) := ⟨n.toNat, (Int.toNat_of_nonneg (by omega)).symm⟩
        rw [setIntegral_unitShell_natCast W e₁ e₂ e₃ hW hψ χ he₃ (by omega : k ≤ m) y s,
          gaussIntegral_unramified_of_exp_one_lt hχ0, mul_zero]
        rw [valued_ratPrimeUnit_zpow_mul v _ _ hy, WithZero.exp_lt_exp]
        omega
    rw [localZeta30, integral_eq_tsum_setIntegral_unitShell v _ hint,
      tsum_int_eq _ (summable_setIntegral_unitShell v _ hint) (k + d) hbelow]
    simp only [hterm, hpeel, tsum_mul_left]
    split_ifs <;> push_cast <;> ring

private theorem localZeta30_torusUnipotentPoint_of_hasConductorExponentAt (a : ℕ) (ha : 1 ≤ a)
    (hχa : HasConductorExponentAt ℚ v χ a) (k d : ℕ) (y : v.adicCompletion ℚ)
    (hy : Valued.v y = WithZero.exp (d : ℤ)) (s : ℂ)
    (hint : letI := localBorel ℚ v
      Integrable (fun α : (v.adicCompletion ℚ)ˣ =>
        W (iotaGL (diagUnitGL2 α) * torusUnipotentPoint v k y) * ((χ α : ℂˣ) : ℂ) *
          ((LanglandsTunnell.TateLocal.modulus (α : v.adicCompletion ℚ) : ℝ) : ℂ) ^ (s - 1))
        (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ v)))) :
    letI := localBorel ℚ v
    localZeta30 v (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ v))) W χ s (torusUnipotentPoint v k y) =
      if a ≤ d then
        W 1 * twoRowCoeff e₁ e₂ e₃ (k + d - a) k *
          (((χ (ratPrimeUnit v) : ℂˣ) : ℂ) * (Ideal.absNorm v.asIdeal : ℂ) ^ (-s)) ^ (k + d - a) *
          gaussIntegral v (psiLocal ℚ v) χ (ratPrimeAt v ^ (d - a) * y)
      else 0 := by
  letI := localBorel ℚ v
  by_cases he₃ : e₃ = 0
  · have hW0 := apply_eq_zero_of_eq_zero W e₁ e₂ e₃ hW he₃
    simp only [localZeta30, hW0, zero_mul, integral_zero, ite_self]
  · rw [localZeta30, integral_eq_tsum_setIntegral_unitShell v _ hint, tsum_eq_single ((k : ℤ) + d - a)]
    · by_cases had : a ≤ d
      · rw [if_pos had, show ((k : ℤ) + d - a) = ((k + d - a : ℕ) : ℤ) by omega,
          setIntegral_unitShell_natCast W e₁ e₂ e₃ hW hψ χ he₃ (by omega : k ≤ k + d - a) y s,
          show (((k + d - a : ℕ) : ℤ) - (k : ℤ)) = ((d - a : ℕ) : ℤ) by omega, zpow_natCast,
          Units.val_pow_eq_pow_val, coe_ratPrimeUnit_eq]
      · rw [if_neg had]
        exact setIntegral_unitShell_eq_zero W e₁ e₂ e₃ hW hψ χ he₃ (Or.inl (by omega)) y s
    · intro n hn
      by_cases hnk : n < k
      · exact setIntegral_unitShell_eq_zero W e₁ e₂ e₃ hW hψ χ he₃ (Or.inl hnk) y s
      · obtain ⟨m, rfl⟩ : ∃ m : ℕ, n = (m : ℤ) := ⟨n.toNat, (Int.toNat_of_nonneg (by omega)).symm⟩
        rw [setIntegral_unitShell_natCast W e₁ e₂ e₃ hW hψ χ he₃ (by omega : k ≤ m) y s,
          gaussIntegral_ramified_of_ne ha hχa, mul_zero]
        rw [valued_ratPrimeUnit_zpow_mul v _ _ hy]
        intro h
        have h' := WithZero.exp_inj.mp h
        omega

end Values
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_laurent_localZeta_eq_gl3LFactorPoly_of_sphericalData.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_exists_laurent_localZeta_eq_gl3LFactorPoly_of_sphericalData.LanglandsTunnell.CubicInduction"

end
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_laurent_localZeta_eq_gl3LFactorPoly_of_sphericalData.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_exists_laurent_localZeta_eq_gl3LFactorPoly_of_sphericalData.LanglandsTunnell.CubicInduction"
end
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_laurent_localZeta_eq_gl3LFactorPoly_of_sphericalData.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_exists_laurent_localZeta_eq_gl3LFactorPoly_of_sphericalData.LanglandsTunnell.CubicInduction"

section

set_option autoImplicit false

open IsDedekindDomain NumberField NumberField.TateGlobal AutomorphicForm LanglandsTunnell.Converse LanglandsTunnell.RankinSelberg LanglandsTunnell.TateLocal MeasureTheory

p2m_open "IsDedekindDomain.HeightOneSpectrum~Extension LanglandsTunnell.CubicInduction P2MW.S_LanglandsTunnell_CubicInduction_exists_laurent_localZeta_eq_gl3LFactorPoly_of_sphericalData.LanglandsTunnell.CubicInduction NumberField.StandardAddChar"

noncomputable section

namespace LanglandsTunnell
p2m_export "LanglandsTunnell" "TateLocal.localBorel TateLocal.borelSpace_localBorel TateLocal.stdRootNumberAt TateLocal.higherUnitsAt TateLocal.mem_higherUnitsAt_iff TateLocal.HasConductorExponentAt TateLocal.modulus TateLocal.modulus_mul"
namespace CubicInduction
p2m_export "LanglandsTunnell.CubicInduction" "localZeta31 localZeta30 localZetaDual31 IsLocalZeta30ConvergentAbove IsLocalZeta31ConvergentAbove lowerUnipotent21 lowerUnipotent21_coe longWeyl3 longWeyl3_coe dualWhittakerFn3 dualWhittakerFn3_apply weylPrime3 weylPrime3_coe transposeInv3_weylPrime3 transposeInv3_lowerUnipotent21 IsGL3PsiWhittakerFn transposeInv3 upperUnipotent3 upperUnipotent3_coe upperUnipotent3_zero embedMat2 iotaGL coe_iotaGL localMaximalCompact3 mem_localMaximalCompact3_iff LocalGL3 varpi varpi_ne_zero heckeGen1 heckeGen2 centralGen cNormQ cosetSum IsCosetEigenfunction IsRightInvariant diagUnitGL2 coe_diagUnitGL2 diagHom diagHom_apply ratPrimeAt ratPrimeAt_ne_zero ratPrimeUnit sphericalTorusValue diagUnits2 coe_diagUnits2 twoRowPointLocal twoRowPointLocal_zero_right eq_zero_of_coe_eq_diagonal_of_valued_lt_of_isGL3PsiWhittakerFn eq_zero_of_isCosetEigenfunction_of_isGL3PsiWhittakerFn_of_apply_one_eq_zero exists_eq_upperUnipotent3_mul_diagonal_mul_mem_localMaximalCompact3 isGL3PsiWhittakerFn_dualWhittakerFn3 sphericalTorusValue_eq_of_isCosetEigenfunction_of_isGL3PsiWhittakerFn"
p2m_open "LanglandsTunnell.CubicInduction LanglandsTunnell"

section AdicShells

variable (v : HeightOneSpectrum (𝓞 ℚ))

private def adicShell (e : ℤ) : Set (v.adicCompletion ℚ) := {x : v.adicCompletion ℚ | Valued.v x = WithZero.exp e}

private theorem exists_valued_eq_exp_of_ne_zero {x : v.adicCompletion ℚ} (hx : Valued.v x ≠ 0) :
    ∃ n : ℤ, Valued.v x = WithZero.exp n :=
  ⟨WithZero.log (Valued.v x), (WithZero.exp_log hx).symm⟩

private theorem valued_le_exp_iff (x : v.adicCompletion ℚ) (e : ℤ) :
    Valued.v x ≤ WithZero.exp e ↔ Valued.v x ≤ WithZero.exp (e - 1) ∨ Valued.v x = WithZero.exp e := by
  constructor
  · intro h
    by_cases hx : Valued.v x = 0
    · left
      rw [hx]
      exact zero_le'
    · obtain ⟨n, hn⟩ := exists_valued_eq_exp_of_ne_zero v hx
      rw [hn] at h ⊢
      rw [WithZero.exp_le_exp] at h
      rcases lt_or_eq_of_le h with h' | h'
      · left
        exact WithZero.exp_le_exp.2 (by omega)
      · right
        rw [h']
  · rintro (h | h)
    · exact h.trans (WithZero.exp_le_exp.2 (by omega))
    · exact h.le

private theorem not_valued_le_exp_sub_one {x : v.adicCompletion ℚ} {e : ℤ} (h : Valued.v x = WithZero.exp e) :
    ¬ Valued.v x ≤ WithZero.exp (e - 1) := by
  rw [h, WithZero.exp_le_exp]
  omega

private theorem adicShell_eq_adicBall_diff (e : ℤ) : adicShell v e = adicBall v e \ adicBall v (e - 1) := by
  ext x
  simp only [adicShell, adicBall, Set.mem_diff, Set.mem_setOf_eq]
  constructor
  · intro h
    exact ⟨h.le, not_valued_le_exp_sub_one v h⟩
  · rintro ⟨h1, h2⟩
    rcases (valued_le_exp_iff v x e).1 h1 with h | h
    · exact absurd h h2
    · exact h

private theorem univ_eq_adicBall_union_iUnion_adicShell (m : ℤ) :
    (Set.univ : Set (v.adicCompletion ℚ)) = adicBall v m ∪ ⋃ j : ℕ, adicShell v (m + 1 + j) := by
  ext x
  simp only [Set.mem_univ, true_iff, Set.mem_union, Set.mem_iUnion, adicBall, adicShell, Set.mem_setOf_eq]
  by_cases h : Valued.v x ≤ WithZero.exp m
  · exact Or.inl h
  · right
    have hx : Valued.v x ≠ 0 := fun h0 => h (by rw [h0]; exact zero_le')
    obtain ⟨n, hn⟩ := exists_valued_eq_exp_of_ne_zero v hx
    rw [hn, WithZero.exp_le_exp, not_le] at h
    refine ⟨(n - (m + 1)).toNat, ?_⟩
    rw [hn, WithZero.exp_inj]
    omega

open Function in
private theorem pairwise_disjoint_adicShell (m : ℤ) :
    Pairwise (Disjoint on fun j : ℕ => adicShell v (m + 1 + j)) := by
  intro i j hij
  rw [Function.onFun, Set.disjoint_left]
  intro x hx hx'
  simp only [adicShell, Set.mem_setOf_eq] at hx hx'
  rw [hx, WithZero.exp_inj] at hx'
  exact hij (by omega)

private theorem disjoint_adicBall_iUnion_adicShell (m : ℤ) :
    Disjoint (adicBall v m) (⋃ j : ℕ, adicShell v (m + 1 + j)) := by
  rw [Set.disjoint_iUnion_right]
  intro j
  rw [Set.disjoint_left]
  intro x hx hx'
  simp only [adicBall, adicShell, Set.mem_setOf_eq] at hx hx'
  rw [hx', WithZero.exp_le_exp] at hx
  omega

private theorem mul_mem_adicShell_iff {c : v.adicCompletion ℚ} {e : ℤ} (hc : Valued.v c = WithZero.exp e)
    (u : v.adicCompletion ℚ) : c * u ∈ adicShell v e ↔ u ∈ unitSet v := by
  simp only [adicShell, unitSet, Set.mem_setOf_eq, map_mul, hc]
  constructor
  · intro h
    exact mul_left_cancel₀ WithZero.exp_ne_zero (h.trans (mul_one _).symm)
  · intro h
    rw [h, mul_one]

private theorem valued_ratPrimeAt_zpow_eq_exp_neg (n : ℤ) : Valued.v (ratPrimeAt v ^ n) = WithZero.exp (-n) := by
  rw [map_zpow₀, valued_ratPrimeAt_eq_valued_varpi, valued_varpi_eq, ← WithZero.exp_zsmul, zsmul_eq_mul,
    mul_neg_one, Int.cast_id]

private theorem coe_ratPrimeUnit_zpow_eq_zpow (n : ℤ) :
    ((ratPrimeUnit v ^ n : (v.adicCompletion ℚ)ˣ) : v.adicCompletion ℚ) = ratPrimeAt v ^ n := by
  rw [Units.val_zpow_eq_zpow_val]
  rfl

private theorem mem_unitShell_ratPrimeUnit_zpow (n : ℤ) : ratPrimeUnit v ^ n ∈ unitShell v n := by
  show Valued.v ((ratPrimeUnit v ^ n : (v.adicCompletion ℚ)ˣ) : v.adicCompletion ℚ) = WithZero.exp (-n)
  rw [coe_ratPrimeUnit_zpow_eq_zpow, valued_ratPrimeAt_zpow_eq_exp_neg]

private theorem ne_zero_of_valued_eq_one {u : v.adicCompletion ℚ} (hu : Valued.v u = 1) : u ≠ 0 := fun h => by
  rw [h, map_zero] at hu
  exact zero_ne_one hu

private theorem setIntegral_eq_inv_mul_setIntegral_preimage {β : Type} [MeasurableSpace β] (ν : Measure β)
    (e : β ≃ᵐ β) {r : ENNReal} (hr0 : r ≠ 0) (hrt : r ≠ ⊤) (he : Measure.map e ν = r • ν) (G : β → ℂ) (S : Set β) :
    ∫ x in S, G x ∂ν = ((r.toReal⁻¹ : ℝ) : ℂ) * ∫ x in e ⁻¹' S, G (e x) ∂ν := by
  have h := setIntegral_map_equiv (μ := ν) e G S
  rw [he, Measure.restrict_smul, integral_smul_measure] at h
  have h3 : ∫ x in e ⁻¹' S, G (e x) ∂ν = (r.toReal : ℂ) * ∫ x in S, G x ∂ν := h.symm.trans Complex.real_smul
  rw [h3, ← mul_assoc, Complex.ofReal_inv,
    inv_mul_cancel₀ (Complex.ofReal_ne_zero.2 (ENNReal.toReal_ne_zero.2 ⟨hr0, hrt⟩)), one_mul]

private theorem setIntegral_one_eq_real {β : Type} [MeasurableSpace β] (ν : Measure β) (S : Set β) :
    ∫ _ in S, (1 : ℂ) ∂ν = ((ν.real S : ℝ) : ℂ) :=
  (setIntegral_const (1 : ℂ)).trans (Complex.real_smul.trans (mul_one _))

private theorem setIntegral_integral_eq_integral_setIntegral {α β : Type} [MeasurableSpace α] [MeasurableSpace β]
    (μ : Measure α) (ν : Measure β) [SigmaFinite μ] [SigmaFinite ν] (f : α × β → ℂ) (hf : Integrable f (μ.prod ν))
    (S : Set α) : ∫ a in S, (∫ b, f (a, b) ∂ν) ∂μ = ∫ b, (∫ a in S, f (a, b) ∂μ) ∂ν := by
  have hf' : Integrable (Function.uncurry fun a b => f (a, b)) ((μ.restrict S).prod ν) := by
    rw [Measure.restrict_prod_eq_prod_univ]
    exact hf.integrableOn
  exact integral_integral_swap hf'

private theorem setIntegral_adicShell_eq_mul_setIntegral_unitSet_aux (G : v.adicCompletion ℚ → ℂ) (e : ℤ) :
    letI := localBorel ℚ v
    ∫ x in adicShell v e, G x ∂(selfDualHaarAt ℚ v) =
      (((Ideal.absNorm v.asIdeal : ℝ) ^ e : ℝ) : ℂ) *
        ∫ u in unitSet v, G (ratPrimeAt v ^ (-e) * u) ∂(selfDualHaarAt ℚ v) := by
  letI := localBorel ℚ v
  haveI : BorelSpace (v.adicCompletion ℚ) := ⟨rfl⟩
  have hcoe := coe_ratPrimeUnit_zpow_eq_zpow v (-e)
  have hvc : Valued.v ((ratPrimeUnit v ^ (-e) : (v.adicCompletion ℚ)ˣ) : v.adicCompletion ℚ) = WithZero.exp e := by
    rw [hcoe, valued_ratPrimeAt_zpow_eq_exp_neg, neg_neg]
  have hmod : modulus ((ratPrimeUnit v ^ (-e) : (v.adicCompletion ℚ)ˣ) : v.adicCompletion ℚ) =
      (Ideal.absNorm v.asIdeal : NNReal) ^ e := by
    rw [modulus_eq_of_mem_unitShell v (mem_unitShell_ratPrimeUnit_zpow v (-e)), neg_neg]
  have hmap := map_mul_left_selfDualHaarAt v (ratPrimeUnit v ^ (-e))
  rw [hmod] at hmap
  have hq : (Ideal.absNorm v.asIdeal : NNReal) ^ e ≠ 0 :=
    zpow_ne_zero e (Nat.cast_ne_zero.2 (Nat.cast_pos.1 (absNorm_pos v)).ne')
  have hr0 : ((((Ideal.absNorm v.asIdeal : NNReal) ^ e : NNReal) : ENNReal))⁻¹ ≠ 0 :=
    ENNReal.inv_ne_zero.2 ENNReal.coe_ne_top
  have hrt : ((((Ideal.absNorm v.asIdeal : NNReal) ^ e : NNReal) : ENNReal))⁻¹ ≠ ⊤ :=
    ENNReal.inv_ne_top.2 (ENNReal.coe_ne_zero.2 hq)
  have hfac : (((((Ideal.absNorm v.asIdeal : NNReal) ^ e : NNReal) : ENNReal))⁻¹).toReal⁻¹ =
      (Ideal.absNorm v.asIdeal : ℝ) ^ e := by
    rw [ENNReal.toReal_inv, ENNReal.coe_toReal, inv_inv, NNReal.coe_zpow, NNReal.coe_natCast]
  have hpre : (mulLeftEquiv₀ _ (Units.ne_zero (ratPrimeUnit v ^ (-e)))) ⁻¹' adicShell v e = unitSet v := by
    ext u
    rw [Set.mem_preimage, mulLeftEquiv₀_apply]
    exact mul_mem_adicShell_iff v hvc u
  rw [setIntegral_eq_inv_mul_setIntegral_preimage (selfDualHaarAt ℚ v)
    (mulLeftEquiv₀ _ (Units.ne_zero (ratPrimeUnit v ^ (-e)))) hr0 hrt hmap G (adicShell v e), hfac, hpre]
  simp only [mulLeftEquiv₀_apply, hcoe]

private theorem adicShell_zero : adicShell v 0 = unitSet v := by
  ext x
  simp only [adicShell, unitSet, Set.mem_setOf_eq, WithZero.exp_zero]

private theorem measurableSet_adicShell (e : ℤ) :
    letI := localBorel ℚ v
    MeasurableSet (adicShell v e) := by
  letI := localBorel ℚ v
  rw [adicShell_eq_adicBall_diff]
  exact (adicBall_measurableSet v e).diff (adicBall_measurableSet v (e - 1))

private theorem adicBall_sub_one_union_adicShell (e : ℤ) : adicBall v (e - 1) ∪ adicShell v e = adicBall v e := by
  ext x
  simp only [adicBall, adicShell, Set.mem_union, Set.mem_setOf_eq]
  exact (valued_le_exp_iff v x e).symm

private theorem disjoint_adicBall_sub_one_adicShell (e : ℤ) : Disjoint (adicBall v (e - 1)) (adicShell v e) := by
  rw [Set.disjoint_left]
  intro x hx hx'
  exact not_valued_le_exp_sub_one v hx' hx

private theorem real_adicShell (e : ℤ) :
    letI := localBorel ℚ v
    (selfDualHaarAt ℚ v).real (adicShell v e) =
      (Ideal.absNorm v.asIdeal : ℝ) ^ e * (1 - (Ideal.absNorm v.asIdeal : ℝ)⁻¹) *
        (selfDualHaarAt ℚ v).real (v.adicCompletionIntegers ℚ : Set (v.adicCompletion ℚ)) := by
  letI := localBorel ℚ v
  have h := setIntegral_adicShell_eq_mul_setIntegral_unitSet_aux v (fun _ => (1 : ℂ)) e
  simp only [setIntegral_one_eq_real] at h
  rw [real_unitSet v] at h
  have h' : (selfDualHaarAt ℚ v).real (adicShell v e) =
      (Ideal.absNorm v.asIdeal : ℝ) ^ e * ((1 - (Ideal.absNorm v.asIdeal : ℝ)⁻¹) *
        (selfDualHaarAt ℚ v).real (v.adicCompletionIntegers ℚ : Set (v.adicCompletion ℚ))) := by
    exact_mod_cast h
  rw [h']
  ring

private theorem setIntegral_adicBall_eq_add (F : v.adicCompletion ℚ → ℂ) (e : ℤ)
    (hF : letI := localBorel ℚ v; IntegrableOn F (adicBall v e) (selfDualHaarAt ℚ v)) :
    letI := localBorel ℚ v
    ∫ x in adicBall v e, F x ∂(selfDualHaarAt ℚ v) =
      ∫ x in adicBall v (e - 1), F x ∂(selfDualHaarAt ℚ v) + ∫ x in adicShell v e, F x ∂(selfDualHaarAt ℚ v) := by
  letI := localBorel ℚ v
  rw [← adicBall_sub_one_union_adicShell v e] at hF ⊢
  exact setIntegral_union (disjoint_adicBall_sub_one_adicShell v e) (measurableSet_adicShell v e)
    (hF.mono_set Set.subset_union_left) (hF.mono_set Set.subset_union_right)

private theorem integral_eq_setIntegral_adicBall_add_tsum (F : v.adicCompletion ℚ → ℂ) (m : ℤ)
    (hF : letI := localBorel ℚ v; Integrable F (selfDualHaarAt ℚ v)) :
    letI := localBorel ℚ v
    ∫ x, F x ∂(selfDualHaarAt ℚ v) =
      ∫ x in adicBall v m, F x ∂(selfDualHaarAt ℚ v) +
        ∑' j : ℕ, ∫ x in adicShell v (m + 1 + j), F x ∂(selfDualHaarAt ℚ v) := by
  letI := localBorel ℚ v
  conv_lhs => rw [← setIntegral_univ, univ_eq_adicBall_union_iUnion_adicShell v m]
  rw [setIntegral_union (disjoint_adicBall_iUnion_adicShell v m)
    (MeasurableSet.iUnion fun j => measurableSet_adicShell v _) hF.integrableOn hF.integrableOn,
    integral_iUnion (fun j => measurableSet_adicShell v _) (pairwise_disjoint_adicShell v m) hF.integrableOn]

private theorem setIntegral_adicShell_eq_mul_setIntegral_unitSet (G : v.adicCompletion ℚ → ℂ) (e : ℤ) :
    letI := localBorel ℚ v
    ∫ x in adicShell v e, G x ∂(selfDualHaarAt ℚ v) =
      (((Ideal.absNorm v.asIdeal : ℝ) ^ e : ℝ) : ℂ) *
        ∫ u in unitSet v, G (ratPrimeAt v ^ (-e) * u) ∂(selfDualHaarAt ℚ v) := by
  exact setIntegral_adicShell_eq_mul_setIntegral_unitSet_aux v G e

private def addCharUnitSetValue (N : ℤ) : ℝ :=
  letI := localBorel ℚ v
  if 0 ≤ N then
    (1 - (Ideal.absNorm v.asIdeal : ℝ)⁻¹) *
      (selfDualHaarAt ℚ v).real (v.adicCompletionIntegers ℚ : Set (v.adicCompletion ℚ))
  else if N = -1 then
    -((Ideal.absNorm v.asIdeal : ℝ)⁻¹ *
      (selfDualHaarAt ℚ v).real (v.adicCompletionIntegers ℚ : Set (v.adicCompletion ℚ)))
  else 0

variable {v}
variable {ψ : AddChar (v.adicCompletion ℚ) ℂ} (hψ0 : ∀ x : v.adicCompletion ℚ, Valued.v x ≤ 1 → ψ x = 1)
  (hψ1 : ∃ x : v.adicCompletion ℚ, Valued.v x ≤ WithZero.exp 1 ∧ ψ x ≠ 1)

include hψ0 hψ1 in

private theorem setIntegral_unitSet_addChar_eq_addCharUnitSetValue {c : v.adicCompletion ℚ} {N : ℤ}
    (hc : Valued.v c = WithZero.exp (-N)) :
    letI := localBorel ℚ v
    ∫ u in unitSet v, ψ (c * u) ∂(selfDualHaarAt ℚ v) = addCharUnitSetValue v N := by
  letI := localBorel ℚ v
  unfold addCharUnitSetValue
  split_ifs with h0 h1
  · have hle : Valued.v c ≤ 1 := by
      rw [hc, ← WithZero.exp_zero]
      exact WithZero.exp_le_exp.2 (by omega)
    exact_mod_cast setIntegral_unitSet_addChar_of_valued_le_one hψ0 hle
  · have heq : Valued.v c = WithZero.exp 1 := by
      rw [hc, h1, neg_neg]
    exact_mod_cast setIntegral_unitSet_addChar_of_valued_eq_exp_one hψ0 hψ1 heq
  · have hlt : WithZero.exp 1 < Valued.v c := by
      rw [hc]
      exact WithZero.exp_lt_exp.2 (by omega)
    exact_mod_cast setIntegral_unitSet_addChar_of_exp_one_lt hψ0 hψ1 hlt

include hψ0 hψ1 in

private theorem setIntegral_adicShell_addChar_eq_mul_addCharUnitSetValue {c : v.adicCompletion ℚ} {e N : ℤ}
    (hc : Valued.v c = WithZero.exp (-(e + N))) :
    letI := localBorel ℚ v
    ∫ x in adicShell v e, ψ (c * x) ∂(selfDualHaarAt ℚ v) =
      (Ideal.absNorm v.asIdeal : ℝ) ^ e * addCharUnitSetValue v N := by
  letI := localBorel ℚ v
  have hc' : Valued.v (c * ratPrimeAt v ^ (-e)) = WithZero.exp (-N) := by
    rw [map_mul, hc, valued_ratPrimeAt_zpow_eq_exp_neg, neg_neg, ← WithZero.exp_add]
    congr 1
    ring
  rw [setIntegral_adicShell_eq_mul_setIntegral_unitSet v (fun x => ψ (c * x)) e]
  simp only [← mul_assoc]
  rw [setIntegral_unitSet_addChar_eq_addCharUnitSetValue hψ0 hψ1 hc']
  push_cast
  ring

end AdicShells
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_laurent_localZeta_eq_gl3LFactorPoly_of_sphericalData.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_exists_laurent_localZeta_eq_gl3LFactorPoly_of_sphericalData.LanglandsTunnell.CubicInduction"

section ShellIntegrals

variable (v : HeightOneSpectrum (𝓞 ℚ))

private theorem setIntegral_unitShell_addChar_mul_inv_mul_modulus_cpow (ψ : AddChar (v.adicCompletion ℚ) ℂ)
    (χ : (v.adicCompletion ℚ)ˣ →* ℂˣ) (z : v.adicCompletion ℚ) (n : ℤ) (w : ℂ) :
    letI := localBorel ℚ v
    ∫ β in unitShell v n, ψ (z * β) * ((χ⁻¹ β : ℂˣ) : ℂ) *
        ((LanglandsTunnell.TateLocal.modulus (β : v.adicCompletion ℚ) : ℝ) : ℂ) ^ (w - 1)
      ∂(Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ v))) =
      ((χ (ratPrimeUnit v ^ n) : ℂˣ) : ℂ)⁻¹ *
        ((((Ideal.absNorm v.asIdeal : NNReal) ^ (-n) : NNReal) : ℝ) : ℂ) ^ (w - 1) *
        gaussIntegral v ψ χ⁻¹ (z * ratPrimeAt v ^ n) := by
  letI := localBorel ℚ v
  have hχc : ((χ⁻¹ (ratPrimeUnit v ^ n) : ℂˣ) : ℂ) = ((χ (ratPrimeUnit v ^ n) : ℂˣ) : ℂ)⁻¹ := by
    rw [MonoidHom.inv_apply, Units.val_inv_eq_inv_val]
  have hcm : ∫ β in unitShell v 0, ((χ (ratPrimeUnit v ^ n) : ℂˣ) : ℂ)⁻¹ *
          ((((Ideal.absNorm v.asIdeal : NNReal) ^ (-n) : NNReal) : ℝ) : ℂ) ^ (w - 1) *
          (ψ (z * ratPrimeAt v ^ n * β) * ((χ⁻¹ β : ℂˣ) : ℂ))
        ∂(Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ v))) =
      ((χ (ratPrimeUnit v ^ n) : ℂˣ) : ℂ)⁻¹ *
        ((((Ideal.absNorm v.asIdeal : NNReal) ^ (-n) : NNReal) : ℝ) : ℂ) ^ (w - 1) *
        gaussIntegral v ψ χ⁻¹ (z * ratPrimeAt v ^ n) := by
    rw [gaussIntegral_eq_setIntegral_unitShell_zero v ψ χ⁻¹ (z * ratPrimeAt v ^ n)]
    exact integral_const_mul _ _
  rw [setIntegral_unitShell_eq_setIntegral_unitShell_zero v _ (mem_unitShell_ratPrimeUnit_zpow v n), ← hcm]
  refine setIntegral_congr_fun (measurableSet_unitShell v 0) fun β hβ => ?_
  have hmodβ : LanglandsTunnell.TateLocal.modulus (β : v.adicCompletion ℚ) = 1 := by
    rw [modulus_eq_of_mem_unitShell v hβ, neg_zero, zpow_zero]
  rw [Units.val_mul, LanglandsTunnell.TateLocal.modulus_mul,
    modulus_eq_of_mem_unitShell v (mem_unitShell_ratPrimeUnit_zpow v n), hmodβ, mul_one, map_mul χ⁻¹, Units.val_mul,
    coe_ratPrimeUnit_zpow_eq_zpow, ← mul_assoc z, hχc]
  ring

private theorem setIntegral_adicShell_addChar_mul_gaussIntegral (ψ : AddChar (v.adicCompletion ℚ) ℂ)
    (η : (v.adicCompletion ℚ)ˣ →* ℂˣ) (A c₀ : v.adicCompletion ℚ) (e : ℤ) :
    letI := localBorel ℚ v
    ∫ x in adicShell v e, ψ (A * x) * gaussIntegral v ψ η (c₀ * x⁻¹) ∂(selfDualHaarAt ℚ v) =
      (((Ideal.absNorm v.asIdeal : ℝ) ^ e : ℝ) : ℂ) * gaussIntegral v ψ η (c₀ * ratPrimeAt v ^ e) *
        gaussIntegral v ψ η (A * ratPrimeAt v ^ (-e)) := by
  letI := localBorel ℚ v
  have key : ∫ u in unitSet v, ψ (A * (ratPrimeAt v ^ (-e) * u)) *
        gaussIntegral v ψ η (c₀ * (ratPrimeAt v ^ (-e) * u)⁻¹) ∂(selfDualHaarAt ℚ v) =
      gaussIntegral v ψ η (A * ratPrimeAt v ^ (-e)) * gaussIntegral v ψ η (c₀ * ratPrimeAt v ^ e) := by
    have hmc : ∫ u in unitSet v, ψ (A * ratPrimeAt v ^ (-e) * u) * charExt η u *
          gaussIntegral v ψ η (c₀ * ratPrimeAt v ^ e) ∂(selfDualHaarAt ℚ v) =
        gaussIntegral v ψ η (A * ratPrimeAt v ^ (-e)) * gaussIntegral v ψ η (c₀ * ratPrimeAt v ^ e) :=
      integral_mul_const _ _
    rw [← hmc]
    refine setIntegral_congr_fun (measurableSet_unitSet v) fun u hu => ?_
    have hu' : Valued.v u = 1 := hu
    have hw : Valued.v (((Units.mk0 u (ne_zero_of_valued_eq_one v hu'))⁻¹ : (v.adicCompletion ℚ)ˣ) :
        v.adicCompletion ℚ) = 1 := by
      rw [Units.val_inv_eq_inv_val, Units.val_mk0, map_inv₀, hu', inv_one]
    have hinv : (ratPrimeAt v ^ (-e) * u)⁻¹ = ratPrimeAt v ^ e *
        (((Units.mk0 u (ne_zero_of_valued_eq_one v hu'))⁻¹ : (v.adicCompletion ℚ)ˣ) : v.adicCompletion ℚ) := by
      rw [mul_inv, zpow_neg, inv_inv, Units.val_inv_eq_inv_val, Units.val_mk0]
    rw [hinv, ← mul_assoc c₀, gaussIntegral_mul_coe_units v ψ η (c₀ * ratPrimeAt v ^ e) hw, map_inv η,
      Units.val_inv_eq_inv_val, inv_inv, ← charExt_coe_units η (Units.mk0 u (ne_zero_of_valued_eq_one v hu')),
      Units.val_mk0, ← mul_assoc A]
    ring
  rw [setIntegral_adicShell_eq_mul_setIntegral_unitSet v _ e, key]
  ring

private theorem setIntegral_unitShell_integral_eq_integral_setIntegral
    (f : (v.adicCompletion ℚ)ˣ × v.adicCompletion ℚ → ℂ)
    (hf : letI := localBorel ℚ v
      Integrable f ((Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ v))).prod (selfDualHaarAt ℚ v)))
    (n : ℤ) :
    letI := localBorel ℚ v
    ∫ β in unitShell v n, (∫ x, f (β, x) ∂(selfDualHaarAt ℚ v))
        ∂(Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ v))) =
      ∫ x, (∫ β in unitShell v n, f (β, x) ∂(Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ v))))
        ∂(selfDualHaarAt ℚ v) := by
  letI := localBorel ℚ v
  haveI := sigmaFinite_comap_val_mulMeasure v
  haveI := sigmaFinite_selfDualHaarAt_rat v
  exact setIntegral_integral_eq_integral_setIntegral _ _ f hf (unitShell v n)

private theorem hasConductorExponentAt_inv {χ : (v.adicCompletion ℚ)ˣ →* ℂˣ} {a : ℕ} (hχ : HasConductorExponentAt ℚ v χ a) :
    HasConductorExponentAt ℚ v χ⁻¹ a := by
  unfold HasConductorExponentAt at hχ ⊢
  obtain ⟨h1, h2⟩ := hχ
  refine ⟨fun u hu => ?_, fun m hm => ?_⟩
  · rw [MonoidHom.inv_apply, h1 u hu, inv_one]
  · obtain ⟨u, hu, hne⟩ := h2 m hm
    exact ⟨u, hu, fun h => hne (inv_eq_one.1 (by rw [MonoidHom.inv_apply] at h; exact h))⟩

end ShellIntegrals
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_laurent_localZeta_eq_gl3LFactorPoly_of_sphericalData.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_exists_laurent_localZeta_eq_gl3LFactorPoly_of_sphericalData.LanglandsTunnell.CubicInduction"

end LanglandsTunnell.CubicInduction
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_laurent_localZeta_eq_gl3LFactorPoly_of_sphericalData.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_exists_laurent_localZeta_eq_gl3LFactorPoly_of_sphericalData.LanglandsTunnell.CubicInduction"
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_laurent_localZeta_eq_gl3LFactorPoly_of_sphericalData.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_exists_laurent_localZeta_eq_gl3LFactorPoly_of_sphericalData.LanglandsTunnell.CubicInduction"

end
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_laurent_localZeta_eq_gl3LFactorPoly_of_sphericalData.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_exists_laurent_localZeta_eq_gl3LFactorPoly_of_sphericalData.LanglandsTunnell.CubicInduction"
end
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_laurent_localZeta_eq_gl3LFactorPoly_of_sphericalData.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_exists_laurent_localZeta_eq_gl3LFactorPoly_of_sphericalData.LanglandsTunnell.CubicInduction"

section

set_option autoImplicit false

open IsDedekindDomain NumberField NumberField.TateGlobal AutomorphicForm LanglandsTunnell.Converse LanglandsTunnell.RankinSelberg LanglandsTunnell.TateLocal MeasureTheory

p2m_open "IsDedekindDomain.HeightOneSpectrum~Extension LanglandsTunnell.CubicInduction P2MW.S_LanglandsTunnell_CubicInduction_exists_laurent_localZeta_eq_gl3LFactorPoly_of_sphericalData.LanglandsTunnell.CubicInduction NumberField.StandardAddChar"

noncomputable section

namespace LanglandsTunnell
p2m_export "LanglandsTunnell" "TateLocal.localBorel TateLocal.borelSpace_localBorel TateLocal.stdRootNumberAt TateLocal.higherUnitsAt TateLocal.mem_higherUnitsAt_iff TateLocal.HasConductorExponentAt TateLocal.modulus TateLocal.modulus_mul"
namespace CubicInduction
p2m_export "LanglandsTunnell.CubicInduction" "localZeta31 localZeta30 localZetaDual31 IsLocalZeta30ConvergentAbove IsLocalZeta31ConvergentAbove lowerUnipotent21 lowerUnipotent21_coe longWeyl3 longWeyl3_coe dualWhittakerFn3 dualWhittakerFn3_apply weylPrime3 weylPrime3_coe transposeInv3_weylPrime3 transposeInv3_lowerUnipotent21 IsGL3PsiWhittakerFn transposeInv3 upperUnipotent3 upperUnipotent3_coe upperUnipotent3_zero embedMat2 iotaGL coe_iotaGL localMaximalCompact3 mem_localMaximalCompact3_iff LocalGL3 varpi varpi_ne_zero heckeGen1 heckeGen2 centralGen cNormQ cosetSum IsCosetEigenfunction IsRightInvariant diagUnitGL2 coe_diagUnitGL2 diagHom diagHom_apply ratPrimeAt ratPrimeAt_ne_zero ratPrimeUnit sphericalTorusValue diagUnits2 coe_diagUnits2 twoRowPointLocal twoRowPointLocal_zero_right eq_zero_of_coe_eq_diagonal_of_valued_lt_of_isGL3PsiWhittakerFn eq_zero_of_isCosetEigenfunction_of_isGL3PsiWhittakerFn_of_apply_one_eq_zero exists_eq_upperUnipotent3_mul_diagonal_mul_mem_localMaximalCompact3 isGL3PsiWhittakerFn_dualWhittakerFn3 sphericalTorusValue_eq_of_isCosetEigenfunction_of_isGL3PsiWhittakerFn"
p2m_open "LanglandsTunnell.CubicInduction LanglandsTunnell"

section ShellDecomposition

variable (v : HeightOneSpectrum (𝓞 ℚ))

private theorem setIntegral_unitShell_integral_eq_setIntegral_adicBall_add_tsum
    (f : (v.adicCompletion ℚ)ˣ × v.adicCompletion ℚ → ℂ)
    (hf : letI := localBorel ℚ v
      Integrable f ((Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ v))).prod (selfDualHaarAt ℚ v)))
    (n m : ℤ) :
    letI := localBorel ℚ v
    ∫ β in unitShell v n, (∫ x, f (β, x) ∂(selfDualHaarAt ℚ v))
        ∂(Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ v))) =
      ∫ x in adicBall v m,
          (∫ β in unitShell v n, f (β, x) ∂(Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ v))))
          ∂(selfDualHaarAt ℚ v) +
        ∑' j : ℕ, ∫ x in adicShell v (m + 1 + j),
          (∫ β in unitShell v n, f (β, x) ∂(Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ v))))
            ∂(selfDualHaarAt ℚ v) := by
  letI := localBorel ℚ v
  haveI := sigmaFinite_comap_val_mulMeasure v
  haveI := sigmaFinite_selfDualHaarAt_rat v
  rw [setIntegral_unitShell_integral_eq_integral_setIntegral v f hf n]
  have hfn : Integrable f
      (((Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ v))).restrict (unitShell v n)).prod
        (selfDualHaarAt ℚ v)) := by
    rw [Measure.restrict_prod_eq_prod_univ]
    exact hf.integrableOn
  exact integral_eq_setIntegral_adicBall_add_tsum v _ m hfn.integral_prod_right

end ShellDecomposition
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_laurent_localZeta_eq_gl3LFactorPoly_of_sphericalData.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_exists_laurent_localZeta_eq_gl3LFactorPoly_of_sphericalData.LanglandsTunnell.CubicInduction"

end LanglandsTunnell.CubicInduction
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_laurent_localZeta_eq_gl3LFactorPoly_of_sphericalData.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_exists_laurent_localZeta_eq_gl3LFactorPoly_of_sphericalData.LanglandsTunnell.CubicInduction"
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_laurent_localZeta_eq_gl3LFactorPoly_of_sphericalData.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_exists_laurent_localZeta_eq_gl3LFactorPoly_of_sphericalData.LanglandsTunnell.CubicInduction"

section Values

variable {v : HeightOneSpectrum (𝓞 ℚ)} (W : LocalGL3 v → ℂ) (e₁ e₂ e₃ : ℂ)
  (hW : IsRightInvariant (localMaximalCompact3 (𝓞 ℚ) ℚ v) W ∧
    IsCosetEigenfunction (localMaximalCompact3 (𝓞 ℚ) ℚ v) (heckeGen1 v) W (cNormQ v * e₁) ∧
    IsCosetEigenfunction (localMaximalCompact3 (𝓞 ℚ) ℚ v) (heckeGen2 v) W (cNormQ v * e₂) ∧
    ∀ g : LocalGL3 v, W (centralGen v * g) = e₃ * W g)
  (hψ : IsGL3PsiWhittakerFn (psiLocal ℚ v) W) (χ : (v.adicCompletion ℚ)ˣ →* ℂˣ)

private def dualIntegrand (w : ℂ) (k : ℤ) (y : v.adicCompletion ℚ) (p : (v.adicCompletion ℚ)ˣ × v.adicCompletion ℚ) : ℂ :=
  dualWhittakerFn3 W (iotaGL (diagUnitGL2 p.1) * lowerUnipotent21 p.2 *
      (weylPrime3 * transposeInv3 (torusUnipotentPoint v k y))) *
    ((χ⁻¹ p.1 : ℂˣ) : ℂ) * ((LanglandsTunnell.TateLocal.modulus (p.1 : v.adicCompletion ℚ) : ℝ) : ℂ) ^ (w - 1)

private theorem dualIntegrand_apply (w : ℂ) (k : ℤ) (y : v.adicCompletion ℚ) (β : (v.adicCompletion ℚ)ˣ)
    (x : v.adicCompletion ℚ) :
    dualIntegrand W χ w k y (β, x) =
      dualWhittakerFn3 W (iotaGL (diagUnitGL2 β) * lowerUnipotent21 x *
          (weylPrime3 * transposeInv3 (torusUnipotentPoint v k y))) *
        ((χ⁻¹ β : ℂˣ) : ℂ) * ((LanglandsTunnell.TateLocal.modulus (β : v.adicCompletion ℚ) : ℝ) : ℂ) ^ (w - 1) :=
  rfl

private theorem localZetaDual31_torusUnipotentPoint_eq_integral_integral (w : ℂ) (k : ℤ) (y : v.adicCompletion ℚ) :
    letI := localBorel ℚ v
    localZetaDual31 v (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ v))) (selfDualHaarAt ℚ v) W χ w
        (torusUnipotentPoint v k y) =
      ∫ β, (∫ x, dualIntegrand W χ w k y (β, x) ∂(selfDualHaarAt ℚ v))
        ∂(Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ v))) := by
  letI := localBorel ℚ v
  simp only [localZetaDual31, localZeta31, dualIntegrand_apply, ← integral_mul_const]

private theorem localZetaDual31_torusUnipotentPoint_eq_tsum (w : ℂ) (k : ℤ) (y : v.adicCompletion ℚ)
    (hint : letI := localBorel ℚ v
      Integrable (dualIntegrand W χ w k y)
        ((Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ v))).prod (selfDualHaarAt ℚ v))) :
    letI := localBorel ℚ v
    localZetaDual31 v (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ v))) (selfDualHaarAt ℚ v) W χ w
        (torusUnipotentPoint v k y) =
      ∑' n : ℤ, ∫ β in unitShell v n, (∫ x, dualIntegrand W χ w k y (β, x) ∂(selfDualHaarAt ℚ v))
        ∂(Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ v))) := by
  letI := localBorel ℚ v
  haveI := sigmaFinite_selfDualHaarAt_rat v
  rw [localZetaDual31_torusUnipotentPoint_eq_integral_integral]
  exact integral_eq_tsum_setIntegral_unitShell v _ hint.integral_prod_left

private theorem weightVec_zero (a b c : ℤ) : (![a, b, c] : Fin 3 → ℤ) 0 = a := rfl

private theorem weightVec_one (a b c : ℤ) : (![a, b, c] : Fin 3 → ℤ) 1 = b := rfl

private theorem weightVec_two (a b c : ℤ) : (![a, b, c] : Fin 3 → ℤ) 2 = c := rfl

private theorem valued_neg_ratPrimeAt_zpow_mul_zpow (n e : ℤ) :
    Valued.v (-(ratPrimeAt v ^ n) * ratPrimeAt v ^ e) = WithZero.exp (-(n + e)) := by
  rw [Valuation.map_mul, Valuation.map_neg, valued_ratPrimeAt_zpow, valued_ratPrimeAt_zpow, ← WithZero.exp_add]
  congr 1
  ring

private theorem valued_ratPrimeAt_zpow_div_mul_zpow {d : ℕ} {y : v.adicCompletion ℚ}
    (hy : Valued.v y = WithZero.exp (d : ℤ)) (k e : ℤ) :
    Valued.v (ratPrimeAt v ^ k / y * ratPrimeAt v ^ (-e)) = WithZero.exp (e - k - d) := by
  rw [Valuation.map_mul, map_div₀, valued_ratPrimeAt_zpow, valued_ratPrimeAt_zpow, hy, ← WithZero.exp_sub,
    ← WithZero.exp_add]
  congr 1
  ring

private theorem gaussIntegral_inv_eq_zero_of_valued_ne {a : ℕ} (ha : 1 ≤ a) (hχa : HasConductorExponentAt ℚ v χ a)
    {c : v.adicCompletion ℚ} (hc : Valued.v c ≠ WithZero.exp (a : ℤ)) :
    gaussIntegral v (psiLocal ℚ v) χ⁻¹ c = 0 :=
  gaussIntegral_eq_zero_of_valued_ne (psiLocal_rat_apply_eq_one_of_valued_le_one v)
    (exists_valued_le_exp_one_and_psiLocal_rat_ne_one v) ha (hasConductorExponentAt_inv v hχa) hc

private theorem gaussIntegral_inv_mul_neg_one (c : v.adicCompletion ℚ) :
    gaussIntegral v (psiLocal ℚ v) χ⁻¹ (c * (((-1 : (v.adicCompletion ℚ)ˣ)) : v.adicCompletion ℚ)) =
      ((χ (-1) : ℂˣ) : ℂ) * gaussIntegral v (psiLocal ℚ v) χ⁻¹ c := by
  rw [gaussIntegral_mul_coe_units v (psiLocal ℚ v) χ⁻¹ c
      (show Valued.v (((-1 : (v.adicCompletion ℚ)ˣ)) : v.adicCompletion ℚ) = 1 by
        rw [Units.val_neg, Units.val_one, Valuation.map_neg, Valuation.map_one]),
    MonoidHom.inv_apply, Units.val_inv_eq_inv_val, inv_inv]

private theorem coe_apply_zpow_neg_natCast_inv (u : (v.adicCompletion ℚ)ˣ) (m : ℕ) :
    ((χ (u ^ (-(m : ℤ))) : ℂˣ) : ℂ)⁻¹ = ((χ u : ℂˣ) : ℂ) ^ m := by
  rw [map_zpow, zpow_neg, zpow_natCast, Units.val_inv_eq_inv_val, inv_inv, Units.val_pow_eq_pow_val]

private theorem absNorm_nnreal_zpow_cpow (z : ℤ) (s : ℂ) :
    ((((Ideal.absNorm v.asIdeal : NNReal) ^ z : NNReal) : ℝ) : ℂ) ^ s =
      (Ideal.absNorm v.asIdeal : ℂ) ^ ((z : ℂ) * s) := by
  have hq : 0 < Ideal.absNorm v.asIdeal := lt_trans zero_lt_one (NumberField.HeightOneSpectrum.one_lt_absNorm v)
  have hq' : (0 : ℝ) < Ideal.absNorm v.asIdeal := by exact_mod_cast hq
  have hr : (0 : ℝ) < (Ideal.absNorm v.asIdeal : ℝ) ^ z := zpow_pos hq' z
  rw [NNReal.coe_zpow, NNReal.coe_natCast, Complex.cpow_def_of_ne_zero (by exact_mod_cast hr.ne'),
    Complex.cpow_def_of_ne_zero (by exact_mod_cast hq'.ne'), ← Complex.ofReal_natCast,
    ← Complex.ofReal_log hr.le, Real.log_zpow, ← Complex.ofReal_log hq'.le]
  push_cast
  ring_nf

private theorem ratPrimeAt_zpow_div_mul_zpow_neg (y : v.adicCompletion ℚ) (k d a : ℕ) :
    ratPrimeAt v ^ (k : ℤ) / y * ratPrimeAt v ^ (-((d : ℤ) - 1 + 1 + ((k + a : ℕ) : ℤ))) =
      (ratPrimeAt v ^ (d + a) * y)⁻¹ := by
  rw [div_mul_eq_mul_div, ← zpow_add₀ (ratPrimeAt_ne_zero v),
    show (k : ℤ) + -((d : ℤ) - 1 + 1 + ((k + a : ℕ) : ℤ)) = -((d + a : ℕ) : ℤ) by push_cast; ring,
    zpow_neg, zpow_natCast, div_eq_mul_inv, ← mul_inv]

private theorem neg_ratPrimeAt_zpow_mul_zpow (k d a : ℕ) :
    -(ratPrimeAt v ^ (-((k + d + 2 * a : ℕ) : ℤ))) * ratPrimeAt v ^ ((d : ℤ) - 1 + 1 + ((k + a : ℕ) : ℤ)) =
      (ratPrimeAt v ^ a)⁻¹ * (((-1 : (v.adicCompletion ℚ)ˣ)) : v.adicCompletion ℚ) := by
  rw [neg_mul, ← zpow_add₀ (ratPrimeAt_ne_zero v),
    show -((k + d + 2 * a : ℕ) : ℤ) + ((d : ℤ) - 1 + 1 + ((k + a : ℕ) : ℤ)) = -(a : ℤ) by push_cast; ring,
    zpow_neg, zpow_natCast, Units.val_neg, Units.val_one, mul_neg_one]

private theorem absNorm_real_zpow_cast (k d a : ℕ) :
    ((((Ideal.absNorm v.asIdeal : ℝ)) ^ ((d : ℤ) - 1 + 1 + ((k + a : ℕ) : ℤ)) : ℝ) : ℂ) =
      (Ideal.absNorm v.asIdeal : ℂ) ^ (k + d + a) := by
  rw [show (d : ℤ) - 1 + 1 + ((k + a : ℕ) : ℤ) = ((k + d + a : ℕ) : ℤ) by push_cast; ring, zpow_natCast]
  push_cast
  ring

private theorem dualRamifiedTerm_eq (a : ℕ) (k d : ℕ) (y : v.adicCompletion ℚ) (w : ℂ) :
    sphericalValue (W 1) e₁ e₂ e₃ (cNormQ v)
          ![(k : ℤ) + d, (d : ℤ) - 1 + 1 + ((k + a : ℕ) : ℤ) - d,
            -((d : ℤ) - 1 + 1 + ((k + a : ℕ) : ℤ) + -((k + d + 2 * a : ℕ) : ℤ))] *
        ((((χ (ratPrimeUnit v ^ (-((k + d + 2 * a : ℕ) : ℤ)))) : ℂˣ) : ℂ)⁻¹ *
          ((((Ideal.absNorm v.asIdeal : NNReal) ^ (-(-((k + d + 2 * a : ℕ) : ℤ))) : NNReal) : ℝ) : ℂ) ^
            (w - 1)) *
        ((((Ideal.absNorm v.asIdeal : ℝ) ^ ((d : ℤ) - 1 + 1 + ((k + a : ℕ) : ℤ)) : ℝ) : ℂ) *
          gaussIntegral v (psiLocal ℚ v) χ⁻¹
            (-(ratPrimeAt v ^ (-((k + d + 2 * a : ℕ) : ℤ))) *
              ratPrimeAt v ^ ((d : ℤ) - 1 + 1 + ((k + a : ℕ) : ℤ))) *
          gaussIntegral v (psiLocal ℚ v) χ⁻¹
            (ratPrimeAt v ^ (k : ℤ) / y * ratPrimeAt v ^ (-((d : ℤ) - 1 + 1 + ((k + a : ℕ) : ℤ))))) =
      if a ≤ d then
        W 1 * e₃ ^ a * (Ideal.absNorm v.asIdeal : ℂ) ^ (2 * a) * twoRowCoeff e₁ e₂ e₃ (k + d - a) k *
          ((χ (ratPrimeUnit v) : ℂˣ) : ℂ) ^ (k + d + 2 * a) *
          (Ideal.absNorm v.asIdeal : ℂ) ^ (((k + d + 2 * a : ℕ) : ℂ) * (w - 1)) * ((χ (-1) : ℂˣ) : ℂ) *
          gaussIntegral v (psiLocal ℚ v) χ⁻¹ (ratPrimeAt v ^ a)⁻¹ *
          gaussIntegral v (psiLocal ℚ v) χ⁻¹ (ratPrimeAt v ^ (d + a) * y)⁻¹
      else 0 := by
  have hq : (Ideal.absNorm v.asIdeal : ℂ) ≠ 0 := by
    exact_mod_cast (lt_trans zero_lt_one (NumberField.HeightOneSpectrum.one_lt_absNorm v)).ne'
  by_cases had : a ≤ d
  · rw [if_pos had]
    have h01 : (![(k : ℤ) + d, (d : ℤ) - 1 + 1 + ((k + a : ℕ) : ℤ) - d,
        -((d : ℤ) - 1 + 1 + ((k + a : ℕ) : ℤ) + -((k + d + 2 * a : ℕ) : ℤ))] : Fin 3 → ℤ) 1 ≤
        (![(k : ℤ) + d, (d : ℤ) - 1 + 1 + ((k + a : ℕ) : ℤ) - d,
          -((d : ℤ) - 1 + 1 + ((k + a : ℕ) : ℤ) + -((k + d + 2 * a : ℕ) : ℤ))] : Fin 3 → ℤ) 0 := by
      show (d : ℤ) - 1 + 1 + ((k + a : ℕ) : ℤ) - d ≤ (k : ℤ) + d
      push_cast
      omega
    have h12 : (![(k : ℤ) + d, (d : ℤ) - 1 + 1 + ((k + a : ℕ) : ℤ) - d,
        -((d : ℤ) - 1 + 1 + ((k + a : ℕ) : ℤ) + -((k + d + 2 * a : ℕ) : ℤ))] : Fin 3 → ℤ) 2 ≤
        (![(k : ℤ) + d, (d : ℤ) - 1 + 1 + ((k + a : ℕ) : ℤ) - d,
          -((d : ℤ) - 1 + 1 + ((k + a : ℕ) : ℤ) + -((k + d + 2 * a : ℕ) : ℤ))] : Fin 3 → ℤ) 1 := by
      show -((d : ℤ) - 1 + 1 + ((k + a : ℕ) : ℤ) + -((k + d + 2 * a : ℕ) : ℤ)) ≤
        (d : ℤ) - 1 + 1 + ((k + a : ℕ) : ℤ) - d
      push_cast
      omega
    have hl2 : -((d : ℤ) - 1 + 1 + ((k + a : ℕ) : ℤ) + -((k + d + 2 * a : ℕ) : ℤ)) = (a : ℤ) := by
      push_cast
      ring
    have ht0 : ((k : ℤ) + d - (a : ℤ)).toNat = k + d - a := by omega
    have ht1 : ((d : ℤ) - 1 + 1 + ((k + a : ℕ) : ℤ) - d - (a : ℤ)).toNat = k := by omega
    rw [sphericalValue_of_le _ _ _ _ _ _ h01 h12, weightVec_zero, weightVec_one, weightVec_two, hl2, ht0, ht1,
      neg_ratPrimeAt_zpow_mul_zpow, gaussIntegral_inv_mul_neg_one, ratPrimeAt_zpow_div_mul_zpow_neg,
      absNorm_real_zpow_cast, coe_apply_zpow_neg_natCast_inv, absNorm_nnreal_zpow_cpow, neg_neg, Int.cast_natCast,
      zpow_natCast, show cNormQ v = (Ideal.absNorm v.asIdeal : ℂ) from rfl,
      show k + d + a = (k + d - a) + 2 * a by omega, pow_add (Ideal.absNorm v.asIdeal : ℂ) (k + d - a) (2 * a),
      inv_pow]
    have h : ((Ideal.absNorm v.asIdeal : ℂ) ^ (k + d - a))⁻¹ * (Ideal.absNorm v.asIdeal : ℂ) ^ (k + d - a) = 1 :=
      inv_mul_cancel₀ (pow_ne_zero _ hq)
    linear_combination (W 1 * e₃ ^ a * twoRowCoeff e₁ e₂ e₃ (k + d - a) k *
      ((χ (ratPrimeUnit v) : ℂˣ) : ℂ) ^ (k + d + 2 * a) *
      (Ideal.absNorm v.asIdeal : ℂ) ^ (((k + d + 2 * a : ℕ) : ℂ) * (w - 1)) * (Ideal.absNorm v.asIdeal : ℂ) ^ (2 * a) *
      ((χ (-1) : ℂˣ) : ℂ) * gaussIntegral v (psiLocal ℚ v) χ⁻¹ (ratPrimeAt v ^ a)⁻¹ *
      gaussIntegral v (psiLocal ℚ v) χ⁻¹ (ratPrimeAt v ^ (d + a) * y)⁻¹) * h
  · rw [if_neg had, sphericalValue_of_not _ _ _ _ _ _ (fun h => had ?_), zero_mul, zero_mul]
    have h1 : (d : ℤ) - 1 + 1 + ((k + a : ℕ) : ℤ) - d ≤ (k : ℤ) + d := h.1
    push_cast at h1
    omega

include hW hψ

private theorem setIntegral_adicBall_setIntegral_unitShell_dualIntegrand_of_valued_le (he₃ : e₃ ≠ 0) (w : ℂ) (k : ℤ)
    (y : v.adicCompletion ℚ) (hy : Valued.v y ≤ 1) (n : ℤ) :
    letI := localBorel ℚ v
    ∫ x in adicBall v 0, (∫ β in unitShell v n, dualIntegrand W χ w k y (β, x)
        ∂(Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ v)))) ∂(selfDualHaarAt ℚ v) =
      sphericalValue (W 1) e₁ e₂ e₃ (cNormQ v) ![k, 0, -n] *
        (((χ (ratPrimeUnit v ^ n) : ℂˣ) : ℂ)⁻¹ *
          ((((Ideal.absNorm v.asIdeal : NNReal) ^ (-n) : NNReal) : ℝ) : ℂ) ^ (w - 1) *
          gaussIntegral v (psiLocal ℚ v) χ⁻¹ 0) *
        ((selfDualHaarAt ℚ v).real (adicBall v 0) : ℂ) := by
  letI := localBorel ℚ v
  have hinner : ∀ x ∈ adicBall v 0, ∫ β in unitShell v n, dualIntegrand W χ w k y (β, x)
      ∂(Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ v))) =
      sphericalValue (W 1) e₁ e₂ e₃ (cNormQ v) ![k, 0, -n] *
        (((χ (ratPrimeUnit v ^ n) : ℂˣ) : ℂ)⁻¹ *
            ((((Ideal.absNorm v.asIdeal : NNReal) ^ (-n) : NNReal) : ℝ) : ℂ) ^ (w - 1) *
          gaussIntegral v (psiLocal ℚ v) χ⁻¹ 0) := by
    intro x hx
    have hx' : Valued.v x ≤ 1 := by
      have h0 : Valued.v x ≤ WithZero.exp 0 := hx
      rwa [WithZero.exp_zero] at h0
    have hcongr : Set.EqOn (fun β => dualIntegrand W χ w k y (β, x))
        (fun β => sphericalValue (W 1) e₁ e₂ e₃ (cNormQ v) ![k, 0, -n] *
          (psiLocal ℚ v (0 * (β : v.adicCompletion ℚ)) * ((χ⁻¹ β : ℂˣ) : ℂ) *
            ((LanglandsTunnell.TateLocal.modulus (β : v.adicCompletion ℚ) : ℝ) : ℂ) ^ (w - 1))) (unitShell v n) := by
      intro β hβ
      have hβ' : Valued.v (β : v.adicCompletion ℚ) = WithZero.exp (-n) := hβ
      dsimp only
      rw [dualIntegrand_apply, dualWhittakerFn3_apply_of_valued_le_of_valued_le W e₁ e₂ e₃ hW hψ he₃ k y hy n β hβ'
        x hx', zero_mul, AddChar.map_zero_eq_one, one_mul]
      ring
    rw [setIntegral_congr_fun (measurableSet_unitShell v n) hcongr, integral_const_mul,
      setIntegral_unitShell_addChar_mul_inv_mul_modulus_cpow v (psiLocal ℚ v) χ 0 n w, zero_mul]
  have hinner' : Set.EqOn
      (fun x => ∫ β in unitShell v n, dualIntegrand W χ w k y (β, x)
        ∂(Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ v))))
      (fun _ => sphericalValue (W 1) e₁ e₂ e₃ (cNormQ v) ![k, 0, -n] *
        (((χ (ratPrimeUnit v ^ n) : ℂˣ) : ℂ)⁻¹ *
            ((((Ideal.absNorm v.asIdeal : NNReal) ^ (-n) : NNReal) : ℝ) : ℂ) ^ (w - 1) *
          gaussIntegral v (psiLocal ℚ v) χ⁻¹ 0)) (adicBall v 0) := fun x hx => hinner x hx
  rw [setIntegral_congr_fun (adicBall_measurableSet v 0) hinner', setIntegral_const, Complex.real_smul]
  ring

private theorem setIntegral_adicShell_setIntegral_unitShell_dualIntegrand_of_valued_le (he₃ : e₃ ≠ 0) (w : ℂ) (k : ℤ)
    (y : v.adicCompletion ℚ) (hy : Valued.v y ≤ 1) (n : ℤ) (e : ℤ) (he : 1 ≤ e) :
    letI := localBorel ℚ v
    ∫ x in adicShell v e, (∫ β in unitShell v n, dualIntegrand W χ w k y (β, x)
        ∂(Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ v)))) ∂(selfDualHaarAt ℚ v) =
      sphericalValue (W 1) e₁ e₂ e₃ (cNormQ v) ![k, e, -(e + n)] *
        (((χ (ratPrimeUnit v ^ n) : ℂˣ) : ℂ)⁻¹ *
          ((((Ideal.absNorm v.asIdeal : NNReal) ^ (-n) : NNReal) : ℝ) : ℂ) ^ (w - 1)) *
        ((((Ideal.absNorm v.asIdeal : ℝ) ^ e : ℝ) : ℂ) *
          gaussIntegral v (psiLocal ℚ v) χ⁻¹ (-(ratPrimeAt v ^ n) * ratPrimeAt v ^ e) *
          gaussIntegral v (psiLocal ℚ v) χ⁻¹ 0) := by
  letI := localBorel ℚ v
  have hinner : ∀ x ∈ adicShell v e, ∫ β in unitShell v n, dualIntegrand W χ w k y (β, x)
      ∂(Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ v))) =
      sphericalValue (W 1) e₁ e₂ e₃ (cNormQ v) ![k, e, -(e + n)] *
          (((χ (ratPrimeUnit v ^ n) : ℂˣ) : ℂ)⁻¹ *
            ((((Ideal.absNorm v.asIdeal : NNReal) ^ (-n) : NNReal) : ℝ) : ℂ) ^ (w - 1)) *
        (psiLocal ℚ v (0 * x) * gaussIntegral v (psiLocal ℚ v) χ⁻¹ (-(ratPrimeAt v ^ n) * x⁻¹)) := by
    intro x hx
    have hx' : Valued.v x = WithZero.exp e := hx
    have hcongr : Set.EqOn (fun β => dualIntegrand W χ w k y (β, x))
        (fun β => sphericalValue (W 1) e₁ e₂ e₃ (cNormQ v) ![k, e, -(e + n)] *
          (psiLocal ℚ v (-x⁻¹ * (β : v.adicCompletion ℚ)) * ((χ⁻¹ β : ℂˣ) : ℂ) *
            ((LanglandsTunnell.TateLocal.modulus (β : v.adicCompletion ℚ) : ℝ) : ℂ) ^ (w - 1))) (unitShell v n) := by
      intro β hβ
      have hβ' : Valued.v (β : v.adicCompletion ℚ) = WithZero.exp (-n) := hβ
      show dualIntegrand W χ w k y (β, x) = _
      rw [dualIntegrand_apply, dualWhittakerFn3_apply_of_valued_le_of_valued_eq W e₁ e₂ e₃ hW hψ he₃ k y hy n β hβ'
        e he x hx', show -((β : v.adicCompletion ℚ) / x) = -x⁻¹ * (β : v.adicCompletion ℚ) from by ring]
      ring
    rw [setIntegral_congr_fun (measurableSet_unitShell v n) hcongr, integral_const_mul,
      setIntegral_unitShell_addChar_mul_inv_mul_modulus_cpow v (psiLocal ℚ v) χ (-x⁻¹) n w,
      show -x⁻¹ * ratPrimeAt v ^ n = -(ratPrimeAt v ^ n) * x⁻¹ from by ring, zero_mul, AddChar.map_zero_eq_one]
    ring
  have hinner' : Set.EqOn
      (fun x => ∫ β in unitShell v n, dualIntegrand W χ w k y (β, x)
        ∂(Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ v))))
      (fun x => sphericalValue (W 1) e₁ e₂ e₃ (cNormQ v) ![k, e, -(e + n)] *
          (((χ (ratPrimeUnit v ^ n) : ℂˣ) : ℂ)⁻¹ *
            ((((Ideal.absNorm v.asIdeal : NNReal) ^ (-n) : NNReal) : ℝ) : ℂ) ^ (w - 1)) *
        (psiLocal ℚ v (0 * x) * gaussIntegral v (psiLocal ℚ v) χ⁻¹ (-(ratPrimeAt v ^ n) * x⁻¹))) (adicShell v e) :=
    fun x hx => hinner x hx
  rw [setIntegral_congr_fun (measurableSet_adicShell v e) hinner', integral_const_mul,
    setIntegral_adicShell_addChar_mul_gaussIntegral v (psiLocal ℚ v) χ⁻¹ 0 (-(ratPrimeAt v ^ n)) e, zero_mul]

private theorem setIntegral_adicBall_setIntegral_unitShell_dualIntegrand_of_valued_eq (he₃ : e₃ ≠ 0) (w : ℂ) (k : ℤ)
    (d : ℕ) (hd : 1 ≤ d) (y : v.adicCompletion ℚ) (hy : Valued.v y = WithZero.exp (d : ℤ)) (n : ℤ) :
    letI := localBorel ℚ v
    ∫ x in adicBall v ((d : ℤ) - 1), (∫ β in unitShell v n, dualIntegrand W χ w k y (β, x)
        ∂(Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ v)))) ∂(selfDualHaarAt ℚ v) =
      sphericalValue (W 1) e₁ e₂ e₃ (cNormQ v) ![k + d, 0, -(d + n)] *
        (((χ (ratPrimeUnit v ^ n) : ℂˣ) : ℂ)⁻¹ *
          ((((Ideal.absNorm v.asIdeal : NNReal) ^ (-n) : NNReal) : ℝ) : ℂ) ^ (w - 1) *
          gaussIntegral v (psiLocal ℚ v) χ⁻¹ 0) *
        ∫ x in adicBall v ((d : ℤ) - 1), psiLocal ℚ v (ratPrimeAt v ^ k * x / y) ∂(selfDualHaarAt ℚ v) := by
  letI := localBorel ℚ v
  have hinner : ∀ x ∈ adicBall v ((d : ℤ) - 1), ∫ β in unitShell v n, dualIntegrand W χ w k y (β, x)
      ∂(Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ v))) =
      psiLocal ℚ v (ratPrimeAt v ^ k * x / y) * sphericalValue (W 1) e₁ e₂ e₃ (cNormQ v) ![k + d, 0, -(d + n)] *
        (((χ (ratPrimeUnit v ^ n) : ℂˣ) : ℂ)⁻¹ *
            ((((Ideal.absNorm v.asIdeal : NNReal) ^ (-n) : NNReal) : ℝ) : ℂ) ^ (w - 1) *
          gaussIntegral v (psiLocal ℚ v) χ⁻¹ 0) := by
    intro x hx
    have hxle : Valued.v x ≤ WithZero.exp ((d : ℤ) - 1) := hx
    have hx' : Valued.v x < WithZero.exp (d : ℤ) := lt_of_le_of_lt hxle (WithZero.exp_lt_exp.2 (by omega))
    have hcongr : Set.EqOn (fun β => dualIntegrand W χ w k y (β, x))
        (fun β => psiLocal ℚ v (ratPrimeAt v ^ k * x / y) *
            sphericalValue (W 1) e₁ e₂ e₃ (cNormQ v) ![k + d, 0, -(d + n)] *
          (psiLocal ℚ v (0 * (β : v.adicCompletion ℚ)) * ((χ⁻¹ β : ℂˣ) : ℂ) *
            ((LanglandsTunnell.TateLocal.modulus (β : v.adicCompletion ℚ) : ℝ) : ℂ) ^ (w - 1))) (unitShell v n) := by
      intro β hβ
      have hβ' : Valued.v (β : v.adicCompletion ℚ) = WithZero.exp (-n) := hβ
      dsimp only
      rw [dualIntegrand_apply, dualWhittakerFn3_apply_of_valued_eq_of_valued_lt W e₁ e₂ e₃ hW hψ he₃ k d hd y hy n β
        hβ' x hx', zero_mul, AddChar.map_zero_eq_one, one_mul]
      ring
    rw [setIntegral_congr_fun (measurableSet_unitShell v n) hcongr, integral_const_mul,
      setIntegral_unitShell_addChar_mul_inv_mul_modulus_cpow v (psiLocal ℚ v) χ 0 n w, zero_mul]
  have hinner' : Set.EqOn
      (fun x => ∫ β in unitShell v n, dualIntegrand W χ w k y (β, x)
        ∂(Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ v))))
      (fun x => psiLocal ℚ v (ratPrimeAt v ^ k * x / y) *
        (sphericalValue (W 1) e₁ e₂ e₃ (cNormQ v) ![k + d, 0, -(d + n)] *
          (((χ (ratPrimeUnit v ^ n) : ℂˣ) : ℂ)⁻¹ *
            ((((Ideal.absNorm v.asIdeal : NNReal) ^ (-n) : NNReal) : ℝ) : ℂ) ^ (w - 1) *
            gaussIntegral v (psiLocal ℚ v) χ⁻¹ 0))) (adicBall v ((d : ℤ) - 1)) := by
    intro x hx
    show (∫ β in unitShell v n, dualIntegrand W χ w k y (β, x)
        ∂(Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ v)))) = _
    rw [hinner x hx]
    ring
  rw [setIntegral_congr_fun (adicBall_measurableSet v ((d : ℤ) - 1)) hinner', integral_mul_const]
  ring

private theorem setIntegral_adicShell_setIntegral_unitShell_dualIntegrand_of_valued_eq (he₃ : e₃ ≠ 0) (w : ℂ) (k : ℤ)
    (d : ℕ) (hd : 1 ≤ d) (y : v.adicCompletion ℚ) (hy : Valued.v y = WithZero.exp (d : ℤ)) (n : ℤ) (e : ℤ)
    (hde : (d : ℤ) ≤ e) :
    letI := localBorel ℚ v
    ∫ x in adicShell v e, (∫ β in unitShell v n, dualIntegrand W χ w k y (β, x)
        ∂(Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ v)))) ∂(selfDualHaarAt ℚ v) =
      sphericalValue (W 1) e₁ e₂ e₃ (cNormQ v) ![k + d, e - d, -(e + n)] *
        (((χ (ratPrimeUnit v ^ n) : ℂˣ) : ℂ)⁻¹ *
          ((((Ideal.absNorm v.asIdeal : NNReal) ^ (-n) : NNReal) : ℝ) : ℂ) ^ (w - 1)) *
        ((((Ideal.absNorm v.asIdeal : ℝ) ^ e : ℝ) : ℂ) *
          gaussIntegral v (psiLocal ℚ v) χ⁻¹ (-(ratPrimeAt v ^ n) * ratPrimeAt v ^ e) *
          gaussIntegral v (psiLocal ℚ v) χ⁻¹ (ratPrimeAt v ^ k / y * ratPrimeAt v ^ (-e))) := by
  letI := localBorel ℚ v
  have hinner : ∀ x ∈ adicShell v e, ∫ β in unitShell v n, dualIntegrand W χ w k y (β, x)
      ∂(Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ v))) =
      sphericalValue (W 1) e₁ e₂ e₃ (cNormQ v) ![k + d, e - d, -(e + n)] *
          (((χ (ratPrimeUnit v ^ n) : ℂˣ) : ℂ)⁻¹ *
            ((((Ideal.absNorm v.asIdeal : NNReal) ^ (-n) : NNReal) : ℝ) : ℂ) ^ (w - 1)) *
        (psiLocal ℚ v (ratPrimeAt v ^ k / y * x) *
          gaussIntegral v (psiLocal ℚ v) χ⁻¹ (-(ratPrimeAt v ^ n) * x⁻¹)) := by
    intro x hx
    have hx' : Valued.v x = WithZero.exp e := hx
    have hcongr : Set.EqOn (fun β => dualIntegrand W χ w k y (β, x))
        (fun β => psiLocal ℚ v (ratPrimeAt v ^ k / y * x) *
            sphericalValue (W 1) e₁ e₂ e₃ (cNormQ v) ![k + d, e - d, -(e + n)] *
          (psiLocal ℚ v (-x⁻¹ * (β : v.adicCompletion ℚ)) * ((χ⁻¹ β : ℂˣ) : ℂ) *
            ((LanglandsTunnell.TateLocal.modulus (β : v.adicCompletion ℚ) : ℝ) : ℂ) ^ (w - 1))) (unitShell v n) := by
      intro β hβ
      have hβ' : Valued.v (β : v.adicCompletion ℚ) = WithZero.exp (-n) := hβ
      show dualIntegrand W χ w k y (β, x) = _
      rw [dualIntegrand_apply, dualWhittakerFn3_apply_of_valued_eq_of_le_valued W e₁ e₂ e₃ hW hψ he₃ k d hd y hy n β
        hβ' e hde x hx', show ratPrimeAt v ^ k * x / y - (β : v.adicCompletion ℚ) / x =
          ratPrimeAt v ^ k / y * x + -x⁻¹ * (β : v.adicCompletion ℚ) from by ring, AddChar.map_add_eq_mul]
      ring
    rw [setIntegral_congr_fun (measurableSet_unitShell v n) hcongr, integral_const_mul,
      setIntegral_unitShell_addChar_mul_inv_mul_modulus_cpow v (psiLocal ℚ v) χ (-x⁻¹) n w,
      show -x⁻¹ * ratPrimeAt v ^ n = -(ratPrimeAt v ^ n) * x⁻¹ from by ring]
    ring
  have hinner' : Set.EqOn
      (fun x => ∫ β in unitShell v n, dualIntegrand W χ w k y (β, x)
        ∂(Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ v))))
      (fun x => sphericalValue (W 1) e₁ e₂ e₃ (cNormQ v) ![k + d, e - d, -(e + n)] *
          (((χ (ratPrimeUnit v ^ n) : ℂˣ) : ℂ)⁻¹ *
            ((((Ideal.absNorm v.asIdeal : NNReal) ^ (-n) : NNReal) : ℝ) : ℂ) ^ (w - 1)) *
        (psiLocal ℚ v (ratPrimeAt v ^ k / y * x) *
          gaussIntegral v (psiLocal ℚ v) χ⁻¹ (-(ratPrimeAt v ^ n) * x⁻¹))) (adicShell v e) :=
    fun x hx => hinner x hx
  rw [setIntegral_congr_fun (measurableSet_adicShell v e) hinner', integral_const_mul,
    setIntegral_adicShell_addChar_mul_gaussIntegral v (psiLocal ℚ v) χ⁻¹ (ratPrimeAt v ^ k / y)
      (-(ratPrimeAt v ^ n)) e]

private theorem setIntegral_unitShell_integral_dualIntegrand_eq_zero_of_valued_le (he₃ : e₃ ≠ 0) {a : ℕ}
    (ha : 1 ≤ a) (hχa : HasConductorExponentAt ℚ v χ a) (k : ℤ) (y : v.adicCompletion ℚ) (hy : Valued.v y ≤ 1)
    (w : ℂ)
    (hint : letI := localBorel ℚ v
      Integrable (dualIntegrand W χ w k y)
        ((Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ v))).prod (selfDualHaarAt ℚ v))) (n : ℤ) :
    letI := localBorel ℚ v
    ∫ β in unitShell v n, (∫ x, dualIntegrand W χ w k y (β, x) ∂(selfDualHaarAt ℚ v))
        ∂(Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ v))) = 0 := by
  letI := localBorel ℚ v
  have hg0 : gaussIntegral v (psiLocal ℚ v) χ⁻¹ 0 = 0 :=
    gaussIntegral_inv_eq_zero_of_valued_ne χ ha hχa (by rw [Valuation.map_zero]; exact WithZero.exp_ne_zero.symm)
  have hsh := fun j : ℕ =>
    setIntegral_adicShell_setIntegral_unitShell_dualIntegrand_of_valued_le W e₁ e₂ e₃ hW hψ χ he₃ w k y hy n
      ((0 : ℤ) + 1 + j) (by omega)
  rw [setIntegral_unitShell_integral_eq_setIntegral_adicBall_add_tsum v _ hint n 0,
    setIntegral_adicBall_setIntegral_unitShell_dualIntegrand_of_valued_le W e₁ e₂ e₃ hW hψ χ he₃ w k y hy n, hg0]
  simp only [hsh, hg0, mul_zero, zero_mul, tsum_zero, add_zero]

private theorem setIntegral_unitShell_integral_dualIntegrand_of_valued_eq (he₃ : e₃ ≠ 0) {a : ℕ} (ha : 1 ≤ a)
    (hχa : HasConductorExponentAt ℚ v χ a) (k d : ℕ) (hd : 1 ≤ d) (y : v.adicCompletion ℚ)
    (hy : Valued.v y = WithZero.exp (d : ℤ)) (w : ℂ)
    (hint : letI := localBorel ℚ v
      Integrable (dualIntegrand W χ w k y)
        ((Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ v))).prod (selfDualHaarAt ℚ v))) (n : ℤ) :
    letI := localBorel ℚ v
    ∫ β in unitShell v n, (∫ x, dualIntegrand W χ w k y (β, x) ∂(selfDualHaarAt ℚ v))
        ∂(Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ v))) =
      if n = -((k + d + 2 * a : ℕ) : ℤ) then
        sphericalValue (W 1) e₁ e₂ e₃ (cNormQ v)
            ![(k : ℤ) + d, (d : ℤ) - 1 + 1 + ((k + a : ℕ) : ℤ) - d, -((d : ℤ) - 1 + 1 + ((k + a : ℕ) : ℤ) + n)] *
          ((((χ (ratPrimeUnit v ^ n)) : ℂˣ) : ℂ)⁻¹ *
            ((((Ideal.absNorm v.asIdeal : NNReal) ^ (-n) : NNReal) : ℝ) : ℂ) ^ (w - 1)) *
          ((((Ideal.absNorm v.asIdeal : ℝ) ^ ((d : ℤ) - 1 + 1 + ((k + a : ℕ) : ℤ)) : ℝ) : ℂ) *
            gaussIntegral v (psiLocal ℚ v) χ⁻¹
              (-(ratPrimeAt v ^ n) * ratPrimeAt v ^ ((d : ℤ) - 1 + 1 + ((k + a : ℕ) : ℤ))) *
            gaussIntegral v (psiLocal ℚ v) χ⁻¹
              (ratPrimeAt v ^ (k : ℤ) / y * ratPrimeAt v ^ (-((d : ℤ) - 1 + 1 + ((k + a : ℕ) : ℤ)))))
      else 0 := by
  letI := localBorel ℚ v
  have hg0 : gaussIntegral v (psiLocal ℚ v) χ⁻¹ 0 = 0 :=
    gaussIntegral_inv_eq_zero_of_valued_ne χ ha hχa (by rw [Valuation.map_zero]; exact WithZero.exp_ne_zero.symm)
  have hg2 : ∀ j : ℕ, j ≠ k + a →
      gaussIntegral v (psiLocal ℚ v) χ⁻¹ (ratPrimeAt v ^ (k : ℤ) / y * ratPrimeAt v ^ (-((d : ℤ) - 1 + 1 + j))) =
        0 := by
    intro j hj
    refine gaussIntegral_inv_eq_zero_of_valued_ne χ ha hχa ?_
    rw [valued_ratPrimeAt_zpow_div_mul_zpow hy, Ne, WithZero.exp_inj]
    omega
  have hg1 : n ≠ -((k + d + 2 * a : ℕ) : ℤ) → gaussIntegral v (psiLocal ℚ v) χ⁻¹
      (-(ratPrimeAt v ^ n) * ratPrimeAt v ^ ((d : ℤ) - 1 + 1 + ((k + a : ℕ) : ℤ))) = 0 := by
    intro hn
    refine gaussIntegral_inv_eq_zero_of_valued_ne χ ha hχa ?_
    rw [valued_neg_ratPrimeAt_zpow_mul_zpow, Ne, WithZero.exp_inj]
    push_cast
    omega
  have hsh := fun j : ℕ =>
    setIntegral_adicShell_setIntegral_unitShell_dualIntegrand_of_valued_eq W e₁ e₂ e₃ hW hψ χ he₃ w k d hd y hy n
      ((d : ℤ) - 1 + 1 + j) (by omega)
  rw [setIntegral_unitShell_integral_eq_setIntegral_adicBall_add_tsum v _ hint n ((d : ℤ) - 1),
    setIntegral_adicBall_setIntegral_unitShell_dualIntegrand_of_valued_eq W e₁ e₂ e₃ hW hψ χ he₃ w k d hd y hy n, hg0,
    tsum_eq_single (k + a) (fun j hj => by rw [hsh j, hg2 j hj]; simp only [mul_zero]), hsh (k + a)]
  simp only [mul_zero, zero_mul, zero_add]
  by_cases hn : n = -((k + d + 2 * a : ℕ) : ℤ)
  · rw [if_pos hn]
  · rw [if_neg hn, hg1 hn]
    simp only [mul_zero, zero_mul]

private theorem setIntegral_unitShell_integral_dualIntegrand_eq_zero_of_neg_of_valued_le (he₃ : e₃ ≠ 0) (k : ℤ)
    (hk : k < 0) (y : v.adicCompletion ℚ) (hy : Valued.v y ≤ 1) (w : ℂ)
    (hint : letI := localBorel ℚ v
      Integrable (dualIntegrand W χ w k y)
        ((Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ v))).prod (selfDualHaarAt ℚ v))) (n : ℤ) :
    letI := localBorel ℚ v
    ∫ β in unitShell v n, (∫ x, dualIntegrand W χ w k y (β, x) ∂(selfDualHaarAt ℚ v))
        ∂(Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ v))) = 0 := by
  letI := localBorel ℚ v
  have hV0 : sphericalValue (W 1) e₁ e₂ e₃ (cNormQ v) ![k, 0, -n] = 0 :=
    sphericalValue_of_not _ _ _ _ _ _ fun h => by
      have h1 : (0 : ℤ) ≤ k := h.1
      omega
  have hVe : ∀ e : ℤ, 1 ≤ e → sphericalValue (W 1) e₁ e₂ e₃ (cNormQ v) ![k, e, -(e + n)] = 0 := fun e he =>
    sphericalValue_of_not _ _ _ _ _ _ fun h => by
      have h1 : e ≤ k := h.1
      omega
  have hsh := fun j : ℕ =>
    setIntegral_adicShell_setIntegral_unitShell_dualIntegrand_of_valued_le W e₁ e₂ e₃ hW hψ χ he₃ w k y hy n
      ((0 : ℤ) + 1 + j) (by omega)
  have hsh0 : ∀ j : ℕ, ∫ x in adicShell v ((0 : ℤ) + 1 + j), (∫ β in unitShell v n, dualIntegrand W χ w k y (β, x)
      ∂(Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ v)))) ∂(selfDualHaarAt ℚ v) = 0 := by
    intro j
    rw [hsh j, hVe ((0 : ℤ) + 1 + j) (by omega)]
    simp only [zero_mul]
  rw [setIntegral_unitShell_integral_eq_setIntegral_adicBall_add_tsum v _ hint n 0,
    setIntegral_adicBall_setIntegral_unitShell_dualIntegrand_of_valued_le W e₁ e₂ e₃ hW hψ χ he₃ w k y hy n, hV0]
  simp only [hsh0, tsum_zero, zero_mul, add_zero]

private theorem setIntegral_unitShell_integral_dualIntegrand_eq_zero_of_neg_of_pos (he₃ : e₃ ≠ 0) {a : ℕ}
    (ha : 1 ≤ a) (hχa : HasConductorExponentAt ℚ v χ a) (k : ℤ) (hk : k < 0) (d : ℕ) (hd : 1 ≤ d)
    (y : v.adicCompletion ℚ) (hy : Valued.v y = WithZero.exp (d : ℤ)) (w : ℂ)
    (hint : letI := localBorel ℚ v
      Integrable (dualIntegrand W χ w k y)
        ((Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ v))).prod (selfDualHaarAt ℚ v))) (n : ℤ) :
    letI := localBorel ℚ v
    ∫ β in unitShell v n, (∫ x, dualIntegrand W χ w k y (β, x) ∂(selfDualHaarAt ℚ v))
        ∂(Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ v))) = 0 := by
  letI := localBorel ℚ v
  have hg0 : gaussIntegral v (psiLocal ℚ v) χ⁻¹ 0 = 0 :=
    gaussIntegral_inv_eq_zero_of_valued_ne χ ha hχa (by rw [Valuation.map_zero]; exact WithZero.exp_ne_zero.symm)
  have hterm : ∀ j : ℕ, ∫ x in adicShell v ((d : ℤ) - 1 + 1 + j), (∫ β in unitShell v n, dualIntegrand W χ w k y (β, x)
      ∂(Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ v)))) ∂(selfDualHaarAt ℚ v) = 0 := by
    intro j
    rw [setIntegral_adicShell_setIntegral_unitShell_dualIntegrand_of_valued_eq W e₁ e₂ e₃ hW hψ χ he₃ w k d hd y hy n
      ((d : ℤ) - 1 + 1 + j) (by omega)]
    by_cases hj : (j : ℤ) = k + a
    · by_cases hn : n = -((d : ℤ) - 1 + 1 + j + a)
      · rw [sphericalValue_of_not _ _ _ _ _ _ (fun h => ?_), zero_mul, zero_mul]
        have h2 : -((d : ℤ) - 1 + 1 + j + n) ≤ (d : ℤ) - 1 + 1 + j - d := h.2
        omega
      · rw [gaussIntegral_inv_eq_zero_of_valued_ne χ ha hχa
          (c := -(ratPrimeAt v ^ n) * ratPrimeAt v ^ ((d : ℤ) - 1 + 1 + j))
          (by rw [valued_neg_ratPrimeAt_zpow_mul_zpow, Ne, WithZero.exp_inj]; omega)]
        simp only [mul_zero, zero_mul]
    · rw [gaussIntegral_inv_eq_zero_of_valued_ne χ ha hχa
        (c := ratPrimeAt v ^ k / y * ratPrimeAt v ^ (-((d : ℤ) - 1 + 1 + j)))
        (by rw [valued_ratPrimeAt_zpow_div_mul_zpow hy, Ne, WithZero.exp_inj]; omega)]
      simp only [mul_zero]
  rw [setIntegral_unitShell_integral_eq_setIntegral_adicBall_add_tsum v _ hint n ((d : ℤ) - 1),
    setIntegral_adicBall_setIntegral_unitShell_dualIntegrand_of_valued_eq W e₁ e₂ e₃ hW hψ χ he₃ w k d hd y hy n, hg0]
  simp only [hterm, tsum_zero, mul_zero, zero_mul, add_zero]

private theorem setIntegral_unitShell_integral_dualIntegrand_eq_zero_of_neg_of_zero (he₃ : e₃ ≠ 0)
    (hχ0 : HasConductorExponentAt ℚ v χ 0) (k : ℤ) (hk : k < 0) (d : ℕ) (hd : 1 ≤ d) (y : v.adicCompletion ℚ)
    (hy : Valued.v y = WithZero.exp (d : ℤ)) (w : ℂ)
    (hint : letI := localBorel ℚ v
      Integrable (dualIntegrand W χ w k y)
        ((Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ v))).prod (selfDualHaarAt ℚ v))) (n : ℤ) :
    letI := localBorel ℚ v
    ∫ β in unitShell v n, (∫ x, dualIntegrand W χ w k y (β, x) ∂(selfDualHaarAt ℚ v))
        ∂(Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ v))) = 0 := by
  letI := localBorel ℚ v
  have hψ0 := psiLocal_rat_apply_eq_one_of_valued_le_one v
  have hψ1 := exists_valued_le_exp_one_and_psiLocal_rat_ne_one v
  have hχi : HasConductorExponentAt ℚ v χ⁻¹ 0 := hasConductorExponentAt_inv v hχ0
  have hp : ratPrimeAt v ≠ 0 := ratPrimeAt_ne_zero v
  have hG : ∀ c : v.adicCompletion ℚ,
      gaussIntegral v (psiLocal ℚ v) χ⁻¹ c = ∫ u in unitSet v, psiLocal ℚ v (c * u) ∂(selfDualHaarAt ℚ v) :=
    gaussIntegral_of_hasConductorExponentAt_zero v (psiLocal ℚ v) hχi
  have hg2 : ∀ j : ℕ, gaussIntegral v (psiLocal ℚ v) χ⁻¹
      (ratPrimeAt v ^ k / y * ratPrimeAt v ^ (-((d : ℤ) - 1 + 1 + j))) = addCharUnitSetValue v (k - j) := by
    intro j
    rw [hG, setIntegral_unitSet_addChar_eq_addCharUnitSetValue hψ0 hψ1
      (show Valued.v (ratPrimeAt v ^ k / y * ratPrimeAt v ^ (-((d : ℤ) - 1 + 1 + j))) = WithZero.exp (-(k - j)) by
        rw [valued_ratPrimeAt_zpow_div_mul_zpow hy]; congr 1; ring)]

  have hball : ∫ x in adicBall v ((d : ℤ) - 1), psiLocal ℚ v (ratPrimeAt v ^ k * x / y) ∂(selfDualHaarAt ℚ v) =
      ∫ x in adicBall v ((d : ℤ) - 1), psiLocal ℚ v (ratPrimeAt v ^ k / y * x) ∂(selfDualHaarAt ℚ v) :=
    setIntegral_congr_fun (adicBall_measurableSet v _) fun x _ => by ring_nf
  have hvc : Valued.v (ratPrimeAt v ^ k / y) = WithZero.exp (-k - d) := by
    rw [map_div₀, valued_ratPrimeAt_zpow, hy, ← WithZero.exp_sub]
  rw [setIntegral_unitShell_integral_eq_setIntegral_adicBall_add_tsum v _ hint n ((d : ℤ) - 1),
    setIntegral_adicBall_setIntegral_unitShell_dualIntegrand_of_valued_eq W e₁ e₂ e₃ hW hψ χ he₃ w k d hd y hy n,
    hball]
  rcases (show k = -1 ∨ k ≤ -2 by omega) with rfl | hk2
  ·
    have hterm : ∀ j : ℕ, j ≠ 0 → ∫ x in adicShell v ((d : ℤ) - 1 + 1 + j),
        (∫ β in unitShell v n, dualIntegrand W χ w (-1) y (β, x)
          ∂(Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ v)))) ∂(selfDualHaarAt ℚ v) = 0 := by
      intro j hj
      rw [setIntegral_adicShell_setIntegral_unitShell_dualIntegrand_of_valued_eq W e₁ e₂ e₃ hW hψ χ he₃ w (-1) d hd y
        hy n ((d : ℤ) - 1 + 1 + j) (by omega), hg2 j]
      have hU : addCharUnitSetValue v (-1 - j) = 0 := by
        simp only [addCharUnitSetValue]
        rw [if_neg (by omega), if_neg (by omega)]
      rw [hU]
      simp only [Complex.ofReal_zero, mul_zero]
    rw [tsum_eq_single 0 hterm,
      setIntegral_adicShell_setIntegral_unitShell_dualIntegrand_of_valued_eq W e₁ e₂ e₃ hW hψ χ he₃ w (-1) d hd y hy
        n ((d : ℤ) - 1 + 1 + (0 : ℕ)) (by omega), hg2 0,
      setIntegral_ball_addChar_of_valued_le hψ0 (show Valued.v (ratPrimeAt v ^ (-1 : ℤ) / y) ≤
        WithZero.exp (-((d : ℤ) - 1)) by rw [hvc]; exact le_of_eq (by congr 1; ring)),
      real_adicBall v]
    by_cases hdom : -((d : ℤ) + n) ≤ 0
    · have hU0 : gaussIntegral v (psiLocal ℚ v) χ⁻¹ 0 =
          (1 - (Ideal.absNorm v.asIdeal : ℝ)⁻¹) *
            (selfDualHaarAt ℚ v).real (v.adicCompletionIntegers ℚ : Set (v.adicCompletion ℚ)) := by
        rw [hG, setIntegral_unitSet_addChar_of_valued_le_one hψ0
          (show Valued.v (0 : v.adicCompletion ℚ) ≤ 1 by rw [Valuation.map_zero]; exact zero_le')]
      have hU1 : gaussIntegral v (psiLocal ℚ v) χ⁻¹
          (-(ratPrimeAt v ^ n) * ratPrimeAt v ^ ((d : ℤ) - 1 + 1 + (0 : ℕ))) =
          (1 - (Ideal.absNorm v.asIdeal : ℝ)⁻¹) *
            (selfDualHaarAt ℚ v).real (v.adicCompletionIntegers ℚ : Set (v.adicCompletion ℚ)) := by
        rw [hG, setIntegral_unitSet_addChar_of_valued_le_one hψ0 ?_]
        rw [valued_neg_ratPrimeAt_zpow_mul_zpow, ← WithZero.exp_zero, WithZero.exp_le_exp]
        push_cast
        omega
      have hUm : addCharUnitSetValue v (-1 - (0 : ℕ)) =
          -((Ideal.absNorm v.asIdeal : ℝ)⁻¹ *
            (selfDualHaarAt ℚ v).real (v.adicCompletionIntegers ℚ : Set (v.adicCompletion ℚ))) := by
        simp only [addCharUnitSetValue]
        rw [if_neg (by norm_num), if_pos (by norm_num)]
      have hwt : sphericalValue (W 1) e₁ e₂ e₃ (cNormQ v)
          ![(-1 : ℤ) + d, (d : ℤ) - 1 + 1 + (0 : ℕ) - d, -((d : ℤ) - 1 + 1 + (0 : ℕ) + n)] =
          sphericalValue (W 1) e₁ e₂ e₃ (cNormQ v) ![(-1 : ℤ) + d, 0, -(d + n)] := by
        congr 1
        ext i
        fin_cases i
        · rfl
        · show (d : ℤ) - 1 + 1 + (0 : ℕ) - d = 0
          push_cast
          ring
        · show -((d : ℤ) - 1 + 1 + (0 : ℕ) + n) = -((d : ℤ) + n)
          push_cast
          ring
      have hq : (Ideal.absNorm v.asIdeal : ℂ) ≠ 0 := by
        exact_mod_cast (lt_trans zero_lt_one (NumberField.HeightOneSpectrum.one_lt_absNorm v)).ne'
      obtain ⟨d', rfl⟩ : ∃ d' : ℕ, d = d' + 1 := ⟨d - 1, by omega⟩
      have hzd : ((d' + 1 : ℕ) : ℤ) - 1 = (d' : ℤ) := by push_cast; ring
      have hze : ((d' + 1 : ℕ) : ℤ) - 1 + 1 + (0 : ℕ) = ((d' + 1 : ℕ) : ℤ) := by push_cast; ring
      rw [hU0, hU1, hUm, hwt, hze, hzd, zpow_natCast, zpow_natCast]
      simp only [Complex.ofReal_mul, Complex.ofReal_neg, Complex.ofReal_inv, Complex.ofReal_pow,
        Complex.ofReal_natCast]
      have h : (Ideal.absNorm v.asIdeal : ℂ) * (Ideal.absNorm v.asIdeal : ℂ)⁻¹ = 1 := mul_inv_cancel₀ hq
      linear_combination (-(sphericalValue (W 1) e₁ e₂ e₃ (cNormQ v) ![(-1 : ℤ) + ((d' + 1 : ℕ) : ℤ), 0,
          -(((d' + 1 : ℕ) : ℤ) + n)] *
        (((χ (ratPrimeUnit v ^ n) : ℂˣ) : ℂ)⁻¹ *
          ((((Ideal.absNorm v.asIdeal : NNReal) ^ (-n) : NNReal) : ℝ) : ℂ) ^ (w - 1)) *
        ((1 - (Ideal.absNorm v.asIdeal : ℂ)⁻¹) *
          ((selfDualHaarAt ℚ v).real (v.adicCompletionIntegers ℚ : Set (v.adicCompletion ℚ)) : ℂ)) *
        ((Ideal.absNorm v.asIdeal : ℂ) ^ d' *
          ((selfDualHaarAt ℚ v).real (v.adicCompletionIntegers ℚ : Set (v.adicCompletion ℚ)) : ℂ)))) * h
    · have hV : sphericalValue (W 1) e₁ e₂ e₃ (cNormQ v) ![(-1 : ℤ) + d, 0, -(d + n)] = 0 :=
        sphericalValue_of_not _ _ _ _ _ _ fun h => by
          have h2 : -((d : ℤ) + n) ≤ 0 := h.2
          exact hdom h2
      have hV' : sphericalValue (W 1) e₁ e₂ e₃ (cNormQ v)
          ![(-1 : ℤ) + d, (d : ℤ) - 1 + 1 + (0 : ℕ) - d, -((d : ℤ) - 1 + 1 + (0 : ℕ) + n)] = 0 :=
        sphericalValue_of_not _ _ _ _ _ _ fun h => by
          have h2 : -((d : ℤ) - 1 + 1 + (0 : ℕ) + n) ≤ (d : ℤ) - 1 + 1 + (0 : ℕ) - d := h.2
          push_cast at h2
          omega
      rw [hV, hV']
      simp only [zero_mul, zero_add]
  ·
    have hterm : ∀ j : ℕ, ∫ x in adicShell v ((d : ℤ) - 1 + 1 + j),
        (∫ β in unitShell v n, dualIntegrand W χ w k y (β, x)
          ∂(Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ v)))) ∂(selfDualHaarAt ℚ v) = 0 := by
      intro j
      rw [setIntegral_adicShell_setIntegral_unitShell_dualIntegrand_of_valued_eq W e₁ e₂ e₃ hW hψ χ he₃ w k d hd y hy n
        ((d : ℤ) - 1 + 1 + j) (by omega), hg2 j]
      have hU : addCharUnitSetValue v (k - j) = 0 := by
        simp only [addCharUnitSetValue]
        rw [if_neg (by omega), if_neg (by omega)]
      rw [hU]
      simp only [Complex.ofReal_zero, mul_zero]
    rw [setIntegral_ball_addChar_of_lt_valued hψ1 (show WithZero.exp (-((d : ℤ) - 1)) < Valued.v (ratPrimeAt v ^ k / y)
      by rw [hvc, WithZero.exp_lt_exp]; omega)]
    simp only [hterm, tsum_zero, mul_zero, add_zero]

private theorem localZetaDual31_torusUnipotentPoint_of_neg (he₃ : e₃ ≠ 0) (a : ℕ) (hχa : HasConductorExponentAt ℚ v χ a)
    (k : ℤ) (hk : k < 0) (d : ℕ) (y : v.adicCompletion ℚ) (hy : Valued.v y = WithZero.exp (d : ℤ)) (w : ℂ)
    (hint : letI := localBorel ℚ v
      Integrable (fun p : (v.adicCompletion ℚ)ˣ × v.adicCompletion ℚ =>
        dualWhittakerFn3 W (iotaGL (diagUnitGL2 p.1) * lowerUnipotent21 p.2 *
            (weylPrime3 * transposeInv3 (torusUnipotentPoint v k y))) *
          ((χ⁻¹ p.1 : ℂˣ) : ℂ) *
          ((LanglandsTunnell.TateLocal.modulus (p.1 : v.adicCompletion ℚ) : ℝ) : ℂ) ^ (w - 1))
        ((Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ v))).prod (selfDualHaarAt ℚ v))) :
    letI := localBorel ℚ v
    localZetaDual31 v (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ v))) (selfDualHaarAt ℚ v) W χ w
      (torusUnipotentPoint v k y) = 0 := by
  letI := localBorel ℚ v
  have hf : Integrable (dualIntegrand W χ w k y)
      ((Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ v))).prod (selfDualHaarAt ℚ v)) := hint
  rw [localZetaDual31_torusUnipotentPoint_eq_tsum W χ w k y hf]
  rcases Nat.eq_zero_or_pos d with rfl | hd
  · have hy' : Valued.v y ≤ 1 := by rw [hy, Nat.cast_zero, WithZero.exp_zero]
    simp only [setIntegral_unitShell_integral_dualIntegrand_eq_zero_of_neg_of_valued_le W e₁ e₂ e₃ hW hψ χ he₃ k hk y
      hy' w hf, tsum_zero]
  · rcases Nat.eq_zero_or_pos a with rfl | ha
    · simp only [setIntegral_unitShell_integral_dualIntegrand_eq_zero_of_neg_of_zero W e₁ e₂ e₃ hW hψ χ he₃ hχa k hk d
        hd y hy w hf, tsum_zero]
    · simp only [setIntegral_unitShell_integral_dualIntegrand_eq_zero_of_neg_of_pos W e₁ e₂ e₃ hW hψ χ he₃ ha hχa k hk
        d hd y hy w hf, tsum_zero]

private theorem localZetaDual31_torusUnipotentPoint_of_hasConductorExponentAt (a : ℕ) (ha : 1 ≤ a)
    (hχa : HasConductorExponentAt ℚ v χ a) (k d : ℕ) (y : v.adicCompletion ℚ)
    (hy : Valued.v y = WithZero.exp (d : ℤ)) (w : ℂ)
    (hint : letI := localBorel ℚ v
      Integrable (fun p : (v.adicCompletion ℚ)ˣ × v.adicCompletion ℚ =>
        dualWhittakerFn3 W (iotaGL (diagUnitGL2 p.1) * lowerUnipotent21 p.2 *
            (weylPrime3 * transposeInv3 (torusUnipotentPoint v k y))) *
          ((χ⁻¹ p.1 : ℂˣ) : ℂ) *
          ((LanglandsTunnell.TateLocal.modulus (p.1 : v.adicCompletion ℚ) : ℝ) : ℂ) ^ (w - 1))
        ((Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ v))).prod (selfDualHaarAt ℚ v))) :
    letI := localBorel ℚ v
    localZetaDual31 v (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ v))) (selfDualHaarAt ℚ v) W χ w
        (torusUnipotentPoint v k y) =
      if a ≤ d then
        W 1 * e₃ ^ a * (Ideal.absNorm v.asIdeal : ℂ) ^ (2 * a) * twoRowCoeff e₁ e₂ e₃ (k + d - a) k *
          ((χ (ratPrimeUnit v) : ℂˣ) : ℂ) ^ (k + d + 2 * a) *
          (Ideal.absNorm v.asIdeal : ℂ) ^ (((k + d + 2 * a : ℕ) : ℂ) * (w - 1)) * ((χ (-1) : ℂˣ) : ℂ) *
          gaussIntegral v (psiLocal ℚ v) χ⁻¹ (ratPrimeAt v ^ a)⁻¹ *
          gaussIntegral v (psiLocal ℚ v) χ⁻¹ (ratPrimeAt v ^ (d + a) * y)⁻¹
      else 0 := by
  letI := localBorel ℚ v
  by_cases he₃ : e₃ = 0
  · have hW0 : ∀ g, W g = 0 := apply_eq_zero_of_eq_zero W e₁ e₂ e₃ hW he₃
    have hD : ∀ p, dualIntegrand W χ w k y p = 0 := fun p => by
      rw [show p = (p.1, p.2) from rfl, dualIntegrand_apply, dualWhittakerFn3_apply, hW0, zero_mul, zero_mul]
    rw [localZetaDual31_torusUnipotentPoint_eq_integral_integral]
    simp only [hD, integral_zero]
    split_ifs <;> simp [hW0 1]
  · have hf : Integrable (dualIntegrand W χ w k y)
        ((Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ v))).prod (selfDualHaarAt ℚ v)) := hint
    rw [localZetaDual31_torusUnipotentPoint_eq_tsum W χ w k y hf]
    rcases Nat.eq_zero_or_pos d with rfl | hd
    · have hy' : Valued.v y ≤ 1 := by rw [hy, Nat.cast_zero, WithZero.exp_zero]
      simp only [setIntegral_unitShell_integral_dualIntegrand_eq_zero_of_valued_le W e₁ e₂ e₃ hW hψ χ he₃ ha hχa _ y
        hy' w hf, tsum_zero]
      rw [if_neg (by omega)]
    · simp only [setIntegral_unitShell_integral_dualIntegrand_of_valued_eq W e₁ e₂ e₃ hW hψ χ he₃ ha hχa k d hd y hy w
        hf]
      rw [tsum_ite_eq]
      exact dualRamifiedTerm_eq W e₁ e₂ e₃ χ a k d y w

end Values
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_laurent_localZeta_eq_gl3LFactorPoly_of_sphericalData.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_exists_laurent_localZeta_eq_gl3LFactorPoly_of_sphericalData.LanglandsTunnell.CubicInduction"

end
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_laurent_localZeta_eq_gl3LFactorPoly_of_sphericalData.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_exists_laurent_localZeta_eq_gl3LFactorPoly_of_sphericalData.LanglandsTunnell.CubicInduction"
end
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_laurent_localZeta_eq_gl3LFactorPoly_of_sphericalData.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_exists_laurent_localZeta_eq_gl3LFactorPoly_of_sphericalData.LanglandsTunnell.CubicInduction"

section

set_option autoImplicit false

open IsDedekindDomain NumberField NumberField.TateGlobal AutomorphicForm LanglandsTunnell.Converse LanglandsTunnell.RankinSelberg LanglandsTunnell.TateLocal MeasureTheory

p2m_open "IsDedekindDomain.HeightOneSpectrum~Extension LanglandsTunnell.CubicInduction P2MW.S_LanglandsTunnell_CubicInduction_exists_laurent_localZeta_eq_gl3LFactorPoly_of_sphericalData.LanglandsTunnell.CubicInduction NumberField.StandardAddChar"

noncomputable section

namespace LanglandsTunnell
p2m_export "LanglandsTunnell" "TateLocal.localBorel TateLocal.borelSpace_localBorel TateLocal.stdRootNumberAt TateLocal.higherUnitsAt TateLocal.mem_higherUnitsAt_iff TateLocal.HasConductorExponentAt TateLocal.modulus TateLocal.modulus_mul"
namespace CubicInduction
p2m_export "LanglandsTunnell.CubicInduction" "localZeta31 localZeta30 localZetaDual31 IsLocalZeta30ConvergentAbove IsLocalZeta31ConvergentAbove lowerUnipotent21 lowerUnipotent21_coe longWeyl3 longWeyl3_coe dualWhittakerFn3 dualWhittakerFn3_apply weylPrime3 weylPrime3_coe transposeInv3_weylPrime3 transposeInv3_lowerUnipotent21 IsGL3PsiWhittakerFn transposeInv3 upperUnipotent3 upperUnipotent3_coe upperUnipotent3_zero embedMat2 iotaGL coe_iotaGL localMaximalCompact3 mem_localMaximalCompact3_iff LocalGL3 varpi varpi_ne_zero heckeGen1 heckeGen2 centralGen cNormQ cosetSum IsCosetEigenfunction IsRightInvariant diagUnitGL2 coe_diagUnitGL2 diagHom diagHom_apply ratPrimeAt ratPrimeAt_ne_zero ratPrimeUnit sphericalTorusValue diagUnits2 coe_diagUnits2 twoRowPointLocal twoRowPointLocal_zero_right eq_zero_of_coe_eq_diagonal_of_valued_lt_of_isGL3PsiWhittakerFn eq_zero_of_isCosetEigenfunction_of_isGL3PsiWhittakerFn_of_apply_one_eq_zero exists_eq_upperUnipotent3_mul_diagonal_mul_mem_localMaximalCompact3 isGL3PsiWhittakerFn_dualWhittakerFn3 sphericalTorusValue_eq_of_isCosetEigenfunction_of_isGL3PsiWhittakerFn"
p2m_open "LanglandsTunnell.CubicInduction LanglandsTunnell"

section DualSeries

variable (v : HeightOneSpectrum (𝓞 ℚ))

private theorem summable_setIntegral_setIntegral_unitShell (f : (v.adicCompletion ℚ)ˣ × v.adicCompletion ℚ → ℂ)
    (hf : letI := localBorel ℚ v
      Integrable f ((Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ v))).prod (selfDualHaarAt ℚ v)))
    (R : Set (v.adicCompletion ℚ)) :
    letI := localBorel ℚ v
    Summable fun n : ℤ => ∫ x in R,
      (∫ β in unitShell v n, f (β, x) ∂(Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ v))))
        ∂(selfDualHaarAt ℚ v) := by
  letI := localBorel ℚ v
  haveI := sigmaFinite_comap_val_mulMeasure v
  haveI := sigmaFinite_selfDualHaarAt_rat v

  have hR : Integrable f ((Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ v))).prod
      ((selfDualHaarAt ℚ v).restrict R)) := by
    have h := hf.integrableOn (s := Set.univ ×ˢ R)
    rwa [IntegrableOn, ← Measure.prod_restrict, Measure.restrict_univ] at h
  have hmarg := hR.integral_prod_left
  refine (hasSum_integral_iUnion (measurableSet_unitShell v) (pairwise_disjoint_unitShell v)
    hmarg.integrableOn).summable.congr fun n => ?_

  have hn : Integrable f (((Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ v))).restrict (unitShell v n)).prod
      ((selfDualHaarAt ℚ v).restrict R)) := by
    have h := hf.integrableOn (s := unitShell v n ×ˢ R)
    rwa [IntegrableOn, ← Measure.prod_restrict] at h
  exact (integral_prod f hn).symm.trans (integral_prod_symm f hn)

private theorem absNorm_cast_ne_zero_dualSeries : (Ideal.absNorm v.asIdeal : ℂ) ≠ 0 := by
  have h := one_lt_absNorm v
  exact_mod_cast (show Ideal.absNorm v.asIdeal ≠ 0 by omega)

private theorem ofReal_zpow_cpow (n : ℤ) (s : ℂ) :
    (((Ideal.absNorm v.asIdeal : ℝ) ^ n : ℝ) : ℂ) ^ s =
      Complex.exp (s * ((n : ℂ) * (Real.log (Ideal.absNorm v.asIdeal : ℝ) : ℂ))) := by
  have hpos : (0 : ℝ) < (Ideal.absNorm v.asIdeal : ℝ) ^ n := zpow_pos (absNorm_real_pos v) n
  rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hpos.ne'), ← Complex.ofReal_log hpos.le,
    Real.log_zpow]
  congr 1
  push_cast
  ring

private theorem absNorm_cpow_eq_exp (z : ℂ) :
    (Ideal.absNorm v.asIdeal : ℂ) ^ z = Complex.exp (z * (Real.log (Ideal.absNorm v.asIdeal : ℝ) : ℂ)) := by
  have hq := absNorm_real_pos v
  have hne : ((Ideal.absNorm v.asIdeal : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hq.ne'
  rw [← Complex.ofReal_natCast, Complex.cpow_def_of_ne_zero hne, ← Complex.ofReal_log hq.le]
  congr 1
  ring

private theorem absNorm_zpow_eq_exp (n : ℤ) :
    (Ideal.absNorm v.asIdeal : ℂ) ^ n = Complex.exp ((n : ℂ) * (Real.log (Ideal.absNorm v.asIdeal : ℝ) : ℂ)) := by
  have hq := absNorm_real_pos v
  have hne : ((Ideal.absNorm v.asIdeal : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hq.ne'
  have h : (Ideal.absNorm v.asIdeal : ℂ) = Complex.exp (Real.log (Ideal.absNorm v.asIdeal : ℝ) : ℂ) := by
    rw [← Complex.ofReal_natCast, Complex.ofReal_log hq.le, Complex.exp_log hne]
  rw [Complex.exp_int_mul, ← h]

private theorem inv_mul_cpow_eq_zpow_mul_zpow (χ : (v.adicCompletion ℚ)ˣ →* ℂˣ) (hχ0 : HasConductorExponentAt ℚ v χ 0)
    (t : ℂ) (ht : t = ((χ (NumberField.AdelicLevel.uniformizerUnit ℚ v) : ℂˣ) : ℂ)) (w : ℂ) (n : ℤ) :
    ((χ (ratPrimeUnit v ^ n) : ℂˣ) : ℂ)⁻¹ *
        ((((Ideal.absNorm v.asIdeal : NNReal) ^ (-n) : NNReal) : ℝ) : ℂ) ^ (w - 1) =
      (t⁻¹ * (Ideal.absNorm v.asIdeal : ℂ) ^ (-w)) ^ n * (Ideal.absNorm v.asIdeal : ℂ) ^ n := by
  have hχ : ((χ (ratPrimeUnit v ^ n) : ℂˣ) : ℂ) = t ^ n := by
    rw [map_zpow χ, Units.val_zpow_eq_zpow_val, coe_apply_ratPrimeUnit_eq v χ hχ0 t ht]
  rw [hχ, ← inv_zpow, mul_zpow, NNReal.coe_zpow, NNReal.coe_natCast, ofReal_zpow_cpow, absNorm_cpow_eq_exp,
    absNorm_zpow_eq_exp, ← Complex.exp_int_mul, mul_assoc, ← Complex.exp_add]
  congr 2
  push_cast
  ring

private theorem zpow_eq_pow_mul_zpow_neg {Z : ℂ} (hZ : Z ≠ 0) {a b : ℕ} {n : ℤ} (h : n = (a : ℤ) - b) :
    Z ^ n = Z ^ a * Z ^ (-(b : ℤ)) := by
  rw [h, sub_eq_add_neg, zpow_add₀ hZ, zpow_natCast]

private theorem zeta_variable_ne_zero (t : ℂ) (ht0 : t ≠ 0) (w : ℂ) :
    t⁻¹ * (Ideal.absNorm v.asIdeal : ℂ) ^ (-w) ≠ 0 :=
  mul_ne_zero (inv_ne_zero ht0) fun h => absNorm_cast_ne_zero_dualSeries v ((Complex.cpow_eq_zero_iff _ _).mp h).1

private theorem tsum_int_eq_add_tsum_nat (g : ℤ → ℂ) (hg : Summable g) (N : ℤ) (h0 : ∀ n : ℤ, n < N - 1 → g n = 0) :
    ∑' n : ℤ, g n = g (N - 1) + ∑' m : ℕ, g (N + m) := by
  have hinj : Function.Injective fun j : ℕ => N - 1 + (j : ℤ) := fun a b h => by
    have h' : N - 1 + (a : ℤ) = N - 1 + (b : ℤ) := h
    omega
  have hsupp : Function.support g ⊆ Set.range fun j : ℕ => N - 1 + (j : ℤ) := by
    intro n hn
    by_contra hcon
    refine hcon ⟨(n - (N - 1)).toNat, ?_⟩
    show N - 1 + (((n - (N - 1)).toNat : ℕ) : ℤ) = n
    by_cases hle : N - 1 ≤ n
    · rw [Int.toNat_of_nonneg (by omega)]
      ring
    · exact absurd (h0 n (by omega)) (Function.mem_support.mp hn)
  rw [← hinj.tsum_eq hsupp, tsum_eq_zero_add']
  · congr 1
    · simp only [Nat.cast_zero, add_zero]
    · exact tsum_congr fun j => congrArg g (by push_cast; ring)
  · exact (hg.comp_injective hinj).comp_injective fun a b h => Nat.succ_injective h

private theorem sphericalValue_eq_of_dominant (W1 e₁ e₂ e₃ : ℂ) {a b c : ℤ} {A B : ℕ} (hba : b ≤ a) (hcb : c ≤ b)
    (hA : a - c = (A : ℤ)) (hB : b - c = (B : ℤ)) :
    sphericalValue W1 e₁ e₂ e₃ (cNormQ v) ![a, b, c] =
      e₃ ^ c * (W1 * ((Ideal.absNorm v.asIdeal : ℂ)⁻¹ ^ A * twoRowCoeff e₁ e₂ e₃ A B)) := by
  have h0 : (![a, b, c] : Fin 3 → ℤ) 0 = a := rfl
  have h1 : (![a, b, c] : Fin 3 → ℤ) 1 = b := rfl
  have h2 : (![a, b, c] : Fin 3 → ℤ) 2 = c := rfl
  rw [sphericalValue_of_le W1 e₁ e₂ e₃ (cNormQ v) ![a, b, c] hba hcb]
  simp only [h0, h1, h2, hA, hB, Int.toNat_natCast, cNormQ_eq]

private theorem sphericalValue_eq_zero_of_not_dominant (W1 e₁ e₂ e₃ : ℂ) {a b c : ℤ} (h : a < b ∨ b < c) :
    sphericalValue W1 e₁ e₂ e₃ (cNormQ v) ![a, b, c] = 0 :=
  sphericalValue_of_not W1 e₁ e₂ e₃ (cNormQ v) ![a, b, c] fun hdom => by
    have h1 : b ≤ a := hdom.1
    have h2 : c ≤ b := hdom.2
    omega

private theorem tsum_eq_of_first_group (F : ℤ → ℂ) (hF : Summable F) (C Z : ℂ) (hZ : Z ≠ 0) (S : ℕ → ℂ) (K d : ℕ)
    (hpos : ∀ (n : ℤ) (m : ℕ), n + d = m → F n = C * (S m * Z ^ n)) (hneg : ∀ n : ℤ, n + d < 0 → F n = 0) :
    ∑' n : ℤ, F n = C * Z ^ (-((K + d + 1 : ℕ) : ℤ)) * ∑' m : ℕ, S m * Z ^ (K + m + 1) := by
  rw [tsum_int_eq_add_tsum_nat F hF (-(d : ℤ)) fun n hn => hneg n (by omega), hneg (-(d : ℤ) - 1) (by omega),
    zero_add]
  have h : ∀ m : ℕ, F (-(d : ℤ) + m) = (C * Z ^ (-((K + d + 1 : ℕ) : ℤ))) * (S m * Z ^ (K + m + 1)) := by
    intro m
    rw [hpos (-(d : ℤ) + m) m (by omega),
      zpow_eq_pow_mul_zpow_neg hZ (n := -(d : ℤ) + m) (a := K + m + 1) (b := K + d + 1) (by push_cast; ring)]
    ring
  simp_rw [h]
  exact tsum_mul_left

private theorem tsum_eq_of_bracket (F : ℤ → ℂ) (hF : Summable F) (C Z : ℂ) (hZ : Z ≠ 0) (S : ℕ → ℂ)
    (S₁ A B : ℂ) (K d c : ℕ) (e : ℤ) (he : e = (K : ℤ) + d - c)
    (hpos : ∀ (n : ℤ) (m : ℕ), n + e = m → F n = C * (A * (S m * Z ^ n)))
    (hneg : ∀ n : ℤ, n + e = -1 → F n = C * (B * (S₁ * Z ^ n))) (hzero : ∀ n : ℤ, n + e < -1 → F n = 0) :
    ∑' n : ℤ, F n =
      C * Z ^ (-((K + d + 1 : ℕ) : ℤ)) * (A * ∑' m : ℕ, S m * Z ^ (c + m + 1) + B * (S₁ * Z ^ c)) := by
  subst he
  rw [tsum_int_eq_add_tsum_nat F hF (-((K : ℤ) + d - c)) fun n hn => hzero n (by omega),
    hneg (-((K : ℤ) + d - c) - 1) (by omega),
    zpow_eq_pow_mul_zpow_neg hZ (n := -((K : ℤ) + d - c) - 1) (a := c) (b := K + d + 1) (by push_cast; ring)]
  have h : ∀ m : ℕ, F (-((K : ℤ) + d - c) + m) =
      (C * Z ^ (-((K + d + 1 : ℕ) : ℤ)) * A) * (S m * Z ^ (c + m + 1)) := by
    intro m
    rw [hpos (-((K : ℤ) + d - c) + m) m (by omega),
      zpow_eq_pow_mul_zpow_neg hZ (n := -((K : ℤ) + d - c) + m) (a := c + m + 1) (b := K + d + 1)
        (by push_cast; ring)]
    ring
  simp_rw [h, tsum_mul_left]
  ring

private theorem tsum_eq_tsum_add_sum_tsum (T Pb : ℤ → ℂ) (Ps : ℤ → ℕ → ℂ) (J : ℕ)
    (hT : ∀ n, T n = Pb n + ∑' j : ℕ, Ps n j) (hvan : ∀ n, ∀ j, J ≤ j → Ps n j = 0) (hb : Summable Pb)
    (hs : ∀ j, Summable fun n => Ps n j) :
    ∑' n : ℤ, T n = ∑' n : ℤ, Pb n + ∑ j ∈ Finset.range J, ∑' n : ℤ, Ps n j := by
  have hfin : ∀ n, ∑' j : ℕ, Ps n j = ∑ j ∈ Finset.range J, Ps n j := fun n =>
    tsum_eq_sum fun j hj => hvan n j (Nat.le_of_not_lt fun h => hj (Finset.mem_range.mpr h))
  simp_rw [hT, hfin]
  rw [hb.tsum_add (summable_sum fun j _ => hs j), Summable.tsum_finsetSum fun j _ => hs j]

private theorem coe_addCharUnitSetValue_of_nonneg {N : ℤ} (hN : 0 ≤ N) :
    letI := localBorel ℚ v
    ((addCharUnitSetValue v N : ℝ) : ℂ) = ((selfDualHaarAt ℚ v).real (v.adicCompletionIntegers ℚ :
        Set (v.adicCompletion ℚ)) : ℂ) * (1 - (Ideal.absNorm v.asIdeal : ℂ)⁻¹) := by
  simp only [addCharUnitSetValue, if_pos hN]
  push_cast
  ring

private theorem coe_addCharUnitSetValue_neg_one :
    letI := localBorel ℚ v
    ((addCharUnitSetValue v (-1) : ℝ) : ℂ) = -(((selfDualHaarAt ℚ v).real (v.adicCompletionIntegers ℚ :
        Set (v.adicCompletion ℚ)) : ℂ) * (Ideal.absNorm v.asIdeal : ℂ)⁻¹) := by
  have h1 : ¬ (0 : ℤ) ≤ -1 := by omega
  simp only [addCharUnitSetValue, if_neg h1]
  push_cast
  ring

private theorem coe_addCharUnitSetValue_of_lt {N : ℤ} (hN : N < -1) : ((addCharUnitSetValue v N : ℝ) : ℂ) = 0 := by
  have h1 : ¬ (0 : ℤ) ≤ N := by omega
  have h2 : N ≠ -1 := by omega
  simp only [addCharUnitSetValue, if_neg h1, if_neg h2, Complex.ofReal_zero]

private theorem gaussIntegral_inv_eq_coe_addCharUnitSetValue {χ : (v.adicCompletion ℚ)ˣ →* ℂˣ}
    (hχ0 : HasConductorExponentAt ℚ v χ 0) {c : v.adicCompletion ℚ} {N : ℤ} (hc : Valued.v c = WithZero.exp (-N)) :
    gaussIntegral v (psiLocal ℚ v) χ⁻¹ c = ((addCharUnitSetValue v N : ℝ) : ℂ) := by
  rw [gaussIntegral_of_hasConductorExponentAt_zero v (psiLocal ℚ v) (hasConductorExponentAt_inv v hχ0) c]
  exact setIntegral_unitSet_addChar_eq_addCharUnitSetValue (psiLocal_level_zero_left v) (psiLocal_level_zero_right v)
    hc

private theorem gaussIntegral_inv_zero_eq {χ : (v.adicCompletion ℚ)ˣ →* ℂˣ} (hχ0 : HasConductorExponentAt ℚ v χ 0) :
    letI := localBorel ℚ v
    gaussIntegral v (psiLocal ℚ v) χ⁻¹ 0 =
      ((selfDualHaarAt ℚ v).real (v.adicCompletionIntegers ℚ : Set (v.adicCompletion ℚ)) : ℂ) * (1 -
          (Ideal.absNorm v.asIdeal : ℂ)⁻¹) := by
  rw [gaussIntegral_of_hasConductorExponentAt_zero v (psiLocal ℚ v) (hasConductorExponentAt_inv v hχ0) 0,
    setIntegral_unitSet_addChar_of_valued_le_one (psiLocal_level_zero_left v) (by rw [map_zero]; exact zero_le')]
  push_cast
  ring

private theorem valued_neg_zpow_mul_zpow (n E N : ℤ) (h : n + E = N) :
    Valued.v (-(ratPrimeAt v ^ n) * ratPrimeAt v ^ E) = WithZero.exp (-N) := by
  subst h
  rw [map_mul, Valuation.map_neg, valued_ratPrimeAt_zpow, valued_ratPrimeAt_zpow, ← WithZero.exp_add]
  congr 1
  ring

private theorem valued_zpow_div_mul_zpow_neg (k d : ℕ) {y : v.adicCompletion ℚ}
    (hy : Valued.v y = WithZero.exp (d : ℤ)) (E N : ℤ) (h : N = (k : ℤ) + d - E) :
    Valued.v (ratPrimeAt v ^ (k : ℤ) / y * ratPrimeAt v ^ (-E)) = WithZero.exp (-N) := by
  subst h
  rw [map_mul, map_div₀, valued_ratPrimeAt_zpow, valued_ratPrimeAt_zpow, hy, div_eq_mul_inv, ← WithZero.exp_neg,
    ← WithZero.exp_add, ← WithZero.exp_add]
  congr 1
  ring

private theorem shell_algebra_of_pos {e₃ Q : ℂ} (he₃ : e₃ ≠ 0) (hQ : Q ≠ 0) (W1 S Zn VOLF ω : ℂ) (K m : ℕ) {E n : ℤ}
    (hn : n + E = m) :
    e₃ ^ (-(E + n)) * (W1 * (Q⁻¹ ^ (K + m) * (e₃ ^ (K + m) * S))) * (Zn * Q ^ n) * (Q ^ E * VOLF * ω) =
      W1 * e₃ ^ K * Q⁻¹ ^ K * ω * (VOLF * (S * Zn)) := by
  obtain rfl : n = (m : ℤ) - E := by omega
  have h1 : e₃ ^ (-(E + ((m : ℤ) - E))) = (e₃ ^ m)⁻¹ := by
    rw [show -(E + ((m : ℤ) - E)) = -(m : ℤ) by ring, zpow_neg, zpow_natCast]
  have h2 : Q ^ ((m : ℤ) - E) = Q ^ m * (Q ^ E)⁻¹ := by rw [zpow_sub₀ hQ, zpow_natCast, div_eq_mul_inv]
  have h3 : (Q ^ E)⁻¹ * Q ^ E = 1 := inv_mul_cancel₀ (zpow_ne_zero E hQ)
  have h4 : (e₃ ^ m)⁻¹ * e₃ ^ (K + m) = e₃ ^ K := by
    rw [pow_add, mul_comm (e₃ ^ K), ← mul_assoc, inv_mul_cancel₀ (pow_ne_zero m he₃), one_mul]
  have h5 : Q⁻¹ ^ (K + m) * Q ^ m = Q⁻¹ ^ K := by
    rw [pow_add, mul_assoc, ← mul_pow, inv_mul_cancel₀ hQ, one_pow, mul_one]
  rw [h1, h2]
  linear_combination (W1 * S * Zn * VOLF * ω * (Q⁻¹ ^ (K + m) * Q ^ m) * ((Q ^ E)⁻¹ * Q ^ E)) * h4 +
    (W1 * S * Zn * VOLF * ω * e₃ ^ K * ((Q ^ E)⁻¹ * Q ^ E)) * h5 + (W1 * S * Zn * VOLF * ω * e₃ ^ K * Q⁻¹ ^ K) * h3

private theorem shell_algebra_of_neg_one {Q : ℂ} (hQ : Q ≠ 0) (W1 e₃ S₁ Zn Bf ω : ℂ) {K K' : ℕ} (hK : K' + 1 = K)
    {E n : ℤ} (hn : n + E = -1) :
    e₃ ^ (-(E + n)) * (W1 * (Q⁻¹ ^ K' * (e₃ ^ K' * S₁))) * (Zn * Q ^ n) * (Q ^ E * Bf * ω) =
      W1 * e₃ ^ K * Q⁻¹ ^ K * ω * (Bf * (S₁ * Zn)) := by
  subst hK
  obtain rfl : n = -1 - E := by omega
  have h1 : e₃ ^ (-(E + (-1 - E))) = e₃ := by rw [show -(E + (-1 - E)) = (1 : ℤ) by ring, zpow_one]
  have h2 : Q ^ (-1 - E) = Q⁻¹ * (Q ^ E)⁻¹ := by
    rw [show (-1 - E : ℤ) = -1 + -E by ring, zpow_add₀ hQ, zpow_neg, zpow_one, zpow_neg]
  have h3 : (Q ^ E)⁻¹ * Q ^ E = 1 := inv_mul_cancel₀ (zpow_ne_zero E hQ)
  rw [h1, h2]
  linear_combination (W1 * S₁ * Zn * Bf * ω * e₃ ^ (K' + 1) * Q⁻¹ ^ (K' + 1)) * h3

private theorem first_algebra_of_pos {e₃ Q : ℂ} (he₃ : e₃ ≠ 0) (hQ : Q ≠ 0) (W1 S Zn VOL : ℂ) (K m d : ℕ) {n : ℤ}
    (hn : n + d = m) :
    e₃ ^ (-(d + n)) * (W1 * (Q⁻¹ ^ (K + m) * (e₃ ^ (K + m) * S))) * (Zn * Q ^ n * (VOL * (1 - Q⁻¹))) *
          (Q ^ ((d : ℤ) - 1) * VOL) +
        e₃ ^ (-(d + n)) * (W1 * (Q⁻¹ ^ (K + m) * (e₃ ^ (K + m) * S))) * (Zn * Q ^ n) *
          (Q ^ (d : ℤ) * (VOL * (1 - Q⁻¹)) * (VOL * (1 - Q⁻¹))) =
      W1 * e₃ ^ K * Q⁻¹ ^ K * (VOL * (VOL * (1 - Q⁻¹))) * (S * Zn) := by
  obtain rfl : n = (m : ℤ) - d := by omega
  have h1 : e₃ ^ (-((d : ℤ) + ((m : ℤ) - d))) = (e₃ ^ m)⁻¹ := by
    rw [show -((d : ℤ) + ((m : ℤ) - d)) = -(m : ℤ) by ring, zpow_neg, zpow_natCast]
  have h2 : Q ^ ((m : ℤ) - d) = Q ^ m * (Q ^ d)⁻¹ := by rw [zpow_sub₀ hQ, zpow_natCast, zpow_natCast, div_eq_mul_inv]
  have h2' : Q ^ ((d : ℤ) - 1) = Q ^ d * Q⁻¹ := by rw [zpow_sub₀ hQ, zpow_natCast, zpow_one, div_eq_mul_inv]
  have h3 : (Q ^ d)⁻¹ * Q ^ d = 1 := inv_mul_cancel₀ (pow_ne_zero d hQ)
  have h4 : (e₃ ^ m)⁻¹ * e₃ ^ (K + m) = e₃ ^ K := by
    rw [pow_add, mul_comm (e₃ ^ K), ← mul_assoc, inv_mul_cancel₀ (pow_ne_zero m he₃), one_mul]
  have h5 : Q⁻¹ ^ (K + m) * Q ^ m = Q⁻¹ ^ K := by
    rw [pow_add, mul_assoc, ← mul_pow, inv_mul_cancel₀ hQ, one_pow, mul_one]
  rw [h1, h2, h2', zpow_natCast]
  linear_combination
    (W1 * S * Zn * (VOL * (VOL * (1 - Q⁻¹))) * (Q⁻¹ ^ (K + m) * Q ^ m) * ((Q ^ d)⁻¹ * Q ^ d)) * h4 +
      (W1 * S * Zn * (VOL * (VOL * (1 - Q⁻¹))) * e₃ ^ K * ((Q ^ d)⁻¹ * Q ^ d)) * h5 +
      (W1 * S * Zn * (VOL * (VOL * (1 - Q⁻¹))) * e₃ ^ K * Q⁻¹ ^ K) * h3

private theorem first_algebra_of_zero {e₃ Q : ℂ} (he₃ : e₃ ≠ 0) (hQ : Q ≠ 0) (W1 S Zn VOL : ℂ) (K m : ℕ) {n : ℤ}
    (hn : n = m) :
    e₃ ^ (-n) * (W1 * (Q⁻¹ ^ (K + m) * (e₃ ^ (K + m) * S))) * (Zn * Q ^ n * (VOL * (1 - Q⁻¹))) * VOL =
      W1 * e₃ ^ K * Q⁻¹ ^ K * (VOL * (VOL * (1 - Q⁻¹))) * (S * Zn) := by
  subst hn
  have h1 : e₃ ^ (-(m : ℤ)) = (e₃ ^ m)⁻¹ := by rw [zpow_neg, zpow_natCast]
  have h4 : (e₃ ^ m)⁻¹ * e₃ ^ (K + m) = e₃ ^ K := by
    rw [pow_add, mul_comm (e₃ ^ K), ← mul_assoc, inv_mul_cancel₀ (pow_ne_zero m he₃), one_mul]
  have h5 : Q⁻¹ ^ (K + m) * Q ^ m = Q⁻¹ ^ K := by
    rw [pow_add, mul_assoc, ← mul_pow, inv_mul_cancel₀ hQ, one_pow, mul_one]
  rw [h1, zpow_natCast]
  linear_combination (W1 * S * Zn * (VOL * (VOL * (1 - Q⁻¹))) * (Q⁻¹ ^ (K + m) * Q ^ m)) * h4 +
    (W1 * S * Zn * (VOL * (VOL * (1 - Q⁻¹))) * e₃ ^ K) * h5

private theorem coe_real_adicBall_zero :
    letI := localBorel ℚ v
    (((selfDualHaarAt ℚ v).real (adicBall v 0) : ℝ) : ℂ) = ((selfDualHaarAt ℚ v).real (v.adicCompletionIntegers ℚ :
        Set (v.adicCompletion ℚ)) : ℂ) := by
  letI := localBorel ℚ v
  rw [real_adicBall v, zpow_zero, one_mul]

private theorem setIntegral_adicBall_psiLocal_eq (k d : ℕ) {y : v.adicCompletion ℚ}
    (hy : Valued.v y = WithZero.exp (d : ℤ)) :
    letI := localBorel ℚ v
    ∫ x in adicBall v ((d : ℤ) - 1), psiLocal ℚ v (ratPrimeAt v ^ (k : ℤ) * x / y) ∂(selfDualHaarAt ℚ v) =
      (Ideal.absNorm v.asIdeal : ℂ) ^ ((d : ℤ) - 1) * ((selfDualHaarAt ℚ v).real (v.adicCompletionIntegers ℚ :
          Set (v.adicCompletion ℚ)) : ℂ) := by
  letI := localBorel ℚ v
  have hc : Valued.v (ratPrimeAt v ^ (k : ℤ) / y) ≤ WithZero.exp (-((d : ℤ) - 1)) := by
    rw [map_div₀, valued_ratPrimeAt_zpow, hy, div_eq_mul_inv, ← WithZero.exp_neg, ← WithZero.exp_add]
    exact WithZero.exp_le_exp.mpr (by omega)
  simp_rw [mul_div_right_comm]
  rw [setIntegral_ball_addChar_of_valued_le (psiLocal_level_zero_left v) hc, real_adicBall v, Complex.ofReal_mul,
    Complex.ofReal_zpow, Complex.ofReal_natCast]

private theorem ite_eq_coe_addCharUnitSetValue (d c : ℕ) (hc : d - 1 ≤ c) :
    letI := localBorel ℚ v
    (if 1 ≤ d ∧ c = d - 1 then -(((selfDualHaarAt ℚ v).real (v.adicCompletionIntegers ℚ : Set (v.adicCompletion ℚ)) :
        ℂ) * (Ideal.absNorm v.asIdeal : ℂ)⁻¹) else ((selfDualHaarAt ℚ v).real (v.adicCompletionIntegers ℚ :
        Set (v.adicCompletion ℚ)) : ℂ) * (1 - (Ideal.absNorm v.asIdeal : ℂ)⁻¹)) =
      ((addCharUnitSetValue v ((c : ℤ) - d) : ℝ) : ℂ) := by
  by_cases h : 1 ≤ d ∧ c = d - 1
  · rw [if_pos h, show (c : ℤ) - d = -1 by omega, coe_addCharUnitSetValue_neg_one v]
  · rw [if_neg h, coe_addCharUnitSetValue_of_nonneg v (N := (c : ℤ) - d) (by omega)]

private theorem sum_Ico_eq_sum_range_sub (g : ℕ → ℂ) (lo K J : ℕ) (hJ : lo + J = K) :
    ∑ c ∈ Finset.Ico lo K, g c = ∑ j ∈ Finset.range J, g (K - 1 - j) := by
  subst hJ
  rw [Finset.sum_Ico_eq_sum_range, Nat.add_sub_cancel_left, ← Finset.sum_range_reflect]
  refine Finset.sum_congr rfl fun j hj => ?_
  rw [Finset.mem_range] at hj
  congr 1
  omega

private theorem tsum_eq_tsum_add_add_sum_tsum_succ (T Pb : ℤ → ℂ) (Ps : ℤ → ℕ → ℂ) (J : ℕ)
    (hT : ∀ n, T n = Pb n + ∑' j : ℕ, Ps n j) (hvan : ∀ n, ∀ j, J + 1 ≤ j → Ps n j = 0) (hb : Summable Pb)
    (hs : ∀ j, Summable fun n => Ps n j) :
    ∑' n : ℤ, T n = ∑' n : ℤ, (Pb n + Ps n 0) + ∑ j ∈ Finset.range J, ∑' n : ℤ, Ps n (j + 1) := by
  have hfin : ∀ n, ∑' j : ℕ, Ps n j = ∑ j ∈ Finset.range (J + 1), Ps n j := fun n =>
    tsum_eq_sum fun j hj => hvan n j (by simpa [Finset.mem_range, Nat.succ_le_iff] using hj)
  have hT' : ∀ n, T n = (Pb n + Ps n 0) + ∑ j ∈ Finset.range J, Ps n (j + 1) := fun n => by
    rw [hT n, hfin n, Finset.sum_range_succ']
    ring
  simp_rw [hT']
  rw [Summable.tsum_add (hb.add (hs 0)) (summable_sum fun j _ => hs (j + 1)),
    Summable.tsum_finsetSum fun j _ => hs (j + 1)]

end DualSeries
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_laurent_localZeta_eq_gl3LFactorPoly_of_sphericalData.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_exists_laurent_localZeta_eq_gl3LFactorPoly_of_sphericalData.LanglandsTunnell.CubicInduction"

end LanglandsTunnell.CubicInduction
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_laurent_localZeta_eq_gl3LFactorPoly_of_sphericalData.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_exists_laurent_localZeta_eq_gl3LFactorPoly_of_sphericalData.LanglandsTunnell.CubicInduction"
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_laurent_localZeta_eq_gl3LFactorPoly_of_sphericalData.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_exists_laurent_localZeta_eq_gl3LFactorPoly_of_sphericalData.LanglandsTunnell.CubicInduction"

section Values

variable {v : HeightOneSpectrum (𝓞 ℚ)} (W : LocalGL3 v → ℂ) (e₁ e₂ e₃ : ℂ)
  (hW : IsRightInvariant (localMaximalCompact3 (𝓞 ℚ) ℚ v) W ∧
    IsCosetEigenfunction (localMaximalCompact3 (𝓞 ℚ) ℚ v) (heckeGen1 v) W (cNormQ v * e₁) ∧
    IsCosetEigenfunction (localMaximalCompact3 (𝓞 ℚ) ℚ v) (heckeGen2 v) W (cNormQ v * e₂) ∧
    ∀ g : LocalGL3 v, W (centralGen v * g) = e₃ * W g)
  (hψ : IsGL3PsiWhittakerFn (psiLocal ℚ v) W) (χ : (v.adicCompletion ℚ)ˣ →* ℂˣ)
include hW hψ

private theorem twoRowCoeff_eq_pow_mul_inv_triple (he₃ : e₃ ≠ 0) (hW1 : W 1 ≠ 0) (A c : ℕ) (hcA : c ≤ A) :
    twoRowCoeff e₁ e₂ e₃ A (A - c) = e₃ ^ A * twoRowCoeff (e₂ / e₃) (e₁ / e₃) e₃⁻¹ A c := by
  rw [twoRowCoeff_inv_triple W e₁ e₂ e₃ hW hψ he₃ hW1 A c hcA, ← mul_assoc, ← mul_pow, mul_inv_cancel₀ he₃, one_pow,
    one_mul]

private theorem shellTerm_of_add_eq (he₃ : e₃ ≠ 0) (hW1 : W 1 ≠ 0) (hχ0 : HasConductorExponentAt ℚ v χ 0) (t : ℂ)
    (ht : t = ((χ (NumberField.AdelicLevel.uniformizerUnit ℚ v) : ℂˣ) : ℂ)) (k d : ℕ) {y : v.adicCompletion ℚ}
    (hy : Valued.v y = WithZero.exp (d : ℤ)) (w : ℂ) (c : ℕ) (hc : c < k + d) (E : ℤ) (hEc : E = ((k + d : ℕ) : ℤ) + d
        - c) (n : ℤ) (m : ℕ) (hn : n + E = m) :
    letI := localBorel ℚ v
    ∫ x in adicShell v E, (∫ β in unitShell v n, dualIntegrand W χ w k y (β, x)
        ∂(Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ v)))) ∂(selfDualHaarAt ℚ v) =
      W 1 * e₃ ^ (k + d) * (Ideal.absNorm v.asIdeal : ℂ)⁻¹ ^ (k + d) * ((addCharUnitSetValue v ((c : ℤ) - d) : ℝ) : ℂ)
          *
        (((selfDualHaarAt ℚ v).real (v.adicCompletionIntegers ℚ : Set (v.adicCompletion ℚ)) : ℂ) * (1 -
            (Ideal.absNorm v.asIdeal : ℂ)⁻¹) * (twoRowCoeff (e₂ / e₃) (e₁ / e₃) e₃⁻¹ (k + d + m) c * (t⁻¹ *
            (Ideal.absNorm v.asIdeal : ℂ) ^ (-w)) ^ n)) := by
  subst hEc
  letI := localBorel ℚ v
  have hQ : (Ideal.absNorm v.asIdeal : ℂ) ≠ 0 := absNorm_cast_ne_zero_dualSeries v
  have hβ := gaussIntegral_inv_eq_coe_addCharUnitSetValue v hχ0 (valued_neg_zpow_mul_zpow v n _ m hn)
  rw [coe_addCharUnitSetValue_of_nonneg v (N := m) (by omega)] at hβ
  have hdict := twoRowCoeff_eq_pow_mul_inv_triple W e₁ e₂ e₃ hW hψ he₃ hW1 (k + d + m) c (by omega)
  rcases Nat.eq_zero_or_pos d with hd0 | hd1
  · have hy1 : Valued.v y ≤ 1 := hy.le.trans_eq (by rw [hd0, Nat.cast_zero, WithZero.exp_zero])
    rw [setIntegral_adicShell_setIntegral_unitShell_dualIntegrand_of_valued_le W e₁ e₂ e₃ hW hψ χ he₃ w k y hy1 n _
        (by omega),
      sphericalValue_eq_of_dominant v (W 1) e₁ e₂ e₃ (A := k + d + m) (B := k + d + m -
          c) (by omega) (by omega) (by omega) (by omega), hdict, inv_mul_cpow_eq_zpow_mul_zpow v χ hχ0 t ht w n, hβ,
      gaussIntegral_inv_zero_eq v hχ0, coe_addCharUnitSetValue_of_nonneg v (N := (c : ℤ) - d) (by omega),
          Complex.ofReal_zpow, Complex.ofReal_natCast]
    exact shell_algebra_of_pos he₃ hQ _ _ _ _ _ (k + d) m hn
  · rw [setIntegral_adicShell_setIntegral_unitShell_dualIntegrand_of_valued_eq W e₁ e₂ e₃ hW hψ χ he₃ w k d hd1 y hy n
      _ (by omega),
      sphericalValue_eq_of_dominant v (W 1) e₁ e₂ e₃ (A := k + d + m) (B := k + d + m -
          c) (by omega) (by omega) (by omega) (by omega), hdict, inv_mul_cpow_eq_zpow_mul_zpow v χ hχ0 t ht w n, hβ,
      gaussIntegral_inv_eq_coe_addCharUnitSetValue v hχ0 (valued_zpow_div_mul_zpow_neg v k d hy _ ((c : ℤ) -
          d) (by omega)), Complex.ofReal_zpow, Complex.ofReal_natCast]
    exact shell_algebra_of_pos he₃ hQ _ _ _ _ _ (k + d) m hn

private theorem shellTerm_of_add_eq_neg_one (he₃ : e₃ ≠ 0) (hW1 : W 1 ≠ 0) (hχ0 : HasConductorExponentAt ℚ v χ 0) (t :
    ℂ)
    (ht : t = ((χ (NumberField.AdelicLevel.uniformizerUnit ℚ v) : ℂˣ) : ℂ)) (k d : ℕ) {y : v.adicCompletion ℚ}
    (hy : Valued.v y = WithZero.exp (d : ℤ)) (w : ℂ) (c : ℕ) (hc : c < k + d) (E : ℤ) (hEc : E = ((k + d : ℕ) : ℤ) + d
        - c) (n : ℤ) (hn : n + E = -1) :
    letI := localBorel ℚ v
    ∫ x in adicShell v E, (∫ β in unitShell v n, dualIntegrand W χ w k y (β, x)
        ∂(Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ v)))) ∂(selfDualHaarAt ℚ v) =
      W 1 * e₃ ^ (k + d) * (Ideal.absNorm v.asIdeal : ℂ)⁻¹ ^ (k + d) * ((addCharUnitSetValue v ((c : ℤ) - d) : ℝ) : ℂ)
          *
        (-(((selfDualHaarAt ℚ v).real (v.adicCompletionIntegers ℚ : Set (v.adicCompletion ℚ)) : ℂ) *
            (Ideal.absNorm v.asIdeal : ℂ)⁻¹) * (twoRowCoeff (e₂ / e₃) (e₁ / e₃) e₃⁻¹ (k + d - 1) c * (t⁻¹ *
            (Ideal.absNorm v.asIdeal : ℂ) ^ (-w)) ^ n)) := by
  subst hEc
  letI := localBorel ℚ v
  have hQ : (Ideal.absNorm v.asIdeal : ℂ) ≠ 0 := absNorm_cast_ne_zero_dualSeries v
  have hβ := gaussIntegral_inv_eq_coe_addCharUnitSetValue v hχ0 (valued_neg_zpow_mul_zpow v n _ (-1) hn)
  rw [coe_addCharUnitSetValue_neg_one v] at hβ
  have hdict := twoRowCoeff_eq_pow_mul_inv_triple W e₁ e₂ e₃ hW hψ he₃ hW1 (k + d - 1) c (by omega)
  have hK : k + d - 1 + 1 = k + d := by omega
  rcases Nat.eq_zero_or_pos d with hd0 | hd1
  · have hy1 : Valued.v y ≤ 1 := hy.le.trans_eq (by rw [hd0, Nat.cast_zero, WithZero.exp_zero])
    rw [setIntegral_adicShell_setIntegral_unitShell_dualIntegrand_of_valued_le W e₁ e₂ e₃ hW hψ χ he₃ w k y hy1 n _
        (by omega),
      sphericalValue_eq_of_dominant v (W 1) e₁ e₂ e₃ (A := k + d - 1) (B := k + d - 1 -
          c) (by omega) (by omega) (by omega) (by omega), hdict, inv_mul_cpow_eq_zpow_mul_zpow v χ hχ0 t ht w n, hβ,
      gaussIntegral_inv_zero_eq v hχ0, coe_addCharUnitSetValue_of_nonneg v (N := (c : ℤ) - d) (by omega),
          Complex.ofReal_zpow, Complex.ofReal_natCast]
    exact shell_algebra_of_neg_one hQ _ _ _ _ _ _ hK hn
  · rw [setIntegral_adicShell_setIntegral_unitShell_dualIntegrand_of_valued_eq W e₁ e₂ e₃ hW hψ χ he₃ w k d hd1 y hy n
      _ (by omega),
      sphericalValue_eq_of_dominant v (W 1) e₁ e₂ e₃ (A := k + d - 1) (B := k + d - 1 -
          c) (by omega) (by omega) (by omega) (by omega), hdict, inv_mul_cpow_eq_zpow_mul_zpow v χ hχ0 t ht w n, hβ,
      gaussIntegral_inv_eq_coe_addCharUnitSetValue v hχ0 (valued_zpow_div_mul_zpow_neg v k d hy _ ((c : ℤ) -
          d) (by omega)), Complex.ofReal_zpow, Complex.ofReal_natCast]
    exact shell_algebra_of_neg_one hQ _ _ _ _ _ _ hK hn

private theorem shellTerm_of_add_lt (he₃ : e₃ ≠ 0) (hχ0 : HasConductorExponentAt ℚ v χ 0) (k d : ℕ) {y :
    v.adicCompletion ℚ}
    (hy : Valued.v y = WithZero.exp (d : ℤ)) (w : ℂ) (c : ℕ) (hc : c < k + d) (E : ℤ) (hEc : E = ((k + d : ℕ) : ℤ) + d
        - c) (n : ℤ) (hn : n + E < -1) :
    letI := localBorel ℚ v
    ∫ x in adicShell v E, (∫ β in unitShell v n, dualIntegrand W χ w k y (β, x)
        ∂(Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ v)))) ∂(selfDualHaarAt ℚ v) = 0 := by
  subst hEc
  letI := localBorel ℚ v
  have hβ := gaussIntegral_inv_eq_coe_addCharUnitSetValue v hχ0 (valued_neg_zpow_mul_zpow v n (((k + d : ℕ) : ℤ) + d -
      c) _ rfl)
  rw [coe_addCharUnitSetValue_of_lt v hn] at hβ
  rcases Nat.eq_zero_or_pos d with hd0 | hd1
  · have hy1 : Valued.v y ≤ 1 := hy.le.trans_eq (by rw [hd0, Nat.cast_zero, WithZero.exp_zero])
    rw [setIntegral_adicShell_setIntegral_unitShell_dualIntegrand_of_valued_le W e₁ e₂ e₃ hW hψ χ he₃ w k y hy1 n _
        (by omega), hβ]
    simp only [mul_zero, zero_mul]
  · rw [setIntegral_adicShell_setIntegral_unitShell_dualIntegrand_of_valued_eq W e₁ e₂ e₃ hW hψ χ he₃ w k d hd1 y hy n
      _ (by omega), hβ]
    simp only [mul_zero, zero_mul]

private theorem tsum_shellTerm_eq (he₃ : e₃ ≠ 0) (hW1 : W 1 ≠ 0) (hχ0 : HasConductorExponentAt ℚ v χ 0) (t : ℂ)
    (ht : t = ((χ (NumberField.AdelicLevel.uniformizerUnit ℚ v) : ℂˣ) : ℂ)) (k d : ℕ) {y : v.adicCompletion ℚ}
    (hy : Valued.v y = WithZero.exp (d : ℤ)) (w : ℂ) (ht0 : t ≠ 0) (hint : letI := localBorel ℚ v
      Integrable (dualIntegrand W χ w k y) ((Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ v))).prod
          (selfDualHaarAt ℚ v))) (c : ℕ) (hc : c < k + d) (E : ℤ) (hEc : E = ((k + d : ℕ) : ℤ) + d - c) :
    letI := localBorel ℚ v
    ∑' n : ℤ, ∫ x in adicShell v E, (∫ β in unitShell v n, dualIntegrand W χ w k y (β, x)
        ∂(Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ v)))) ∂(selfDualHaarAt ℚ v) =
      W 1 * e₃ ^ (k + d) * (Ideal.absNorm v.asIdeal : ℂ)⁻¹ ^ (k + d) * ((addCharUnitSetValue v (((c : ℕ) : ℤ) - d) :
          ℝ) : ℂ) *
        (t⁻¹ * (Ideal.absNorm v.asIdeal : ℂ) ^ (-w)) ^ (-((k + d + d + 1 : ℕ) : ℤ)) *
        (((selfDualHaarAt ℚ v).real (v.adicCompletionIntegers ℚ : Set (v.adicCompletion ℚ)) : ℂ) * (1 -
            (Ideal.absNorm v.asIdeal : ℂ)⁻¹) * (∑' m : ℕ, twoRowCoeff (e₂ / e₃) (e₁ / e₃) e₃⁻¹ (k + d + m) c * (t⁻¹ *
            (Ideal.absNorm v.asIdeal : ℂ) ^ (-w)) ^ (c + m + 1)) +
          -(((selfDualHaarAt ℚ v).real (v.adicCompletionIntegers ℚ : Set (v.adicCompletion ℚ)) : ℂ) *
              (Ideal.absNorm v.asIdeal : ℂ)⁻¹) * (twoRowCoeff (e₂ / e₃) (e₁ / e₃) e₃⁻¹ (k + d - 1) c * (t⁻¹ *
              (Ideal.absNorm v.asIdeal : ℂ) ^ (-w)) ^ c)) := by
  letI := localBorel ℚ v
  exact tsum_eq_of_bracket _ (summable_setIntegral_setIntegral_unitShell v (dualIntegrand W χ w k y) hint (adicShell v
      E))
    (W 1 * e₃ ^ (k + d) * (Ideal.absNorm v.asIdeal : ℂ)⁻¹ ^ (k + d) * ((addCharUnitSetValue v ((c : ℤ) - d) : ℝ) :
        ℂ)) _ (zeta_variable_ne_zero v t ht0 w)
    (fun m => twoRowCoeff (e₂ / e₃) (e₁ / e₃) e₃⁻¹ (k + d + m) c) (twoRowCoeff (e₂ / e₃) (e₁ / e₃) e₃⁻¹ (k + d -
        1) c) _ _ (k + d) d c E hEc
    (fun n m hn => shellTerm_of_add_eq W e₁ e₂ e₃ hW hψ χ he₃ hW1 hχ0 t ht k d hy w c hc E hEc n m hn)
    (fun n hn => shellTerm_of_add_eq_neg_one W e₁ e₂ e₃ hW hψ χ he₃ hW1 hχ0 t ht k d hy w c hc E hEc n hn)
    (fun n hn => shellTerm_of_add_lt W e₁ e₂ e₃ hW hψ χ he₃ hχ0 k d hy w c hc E hEc n hn)

private theorem shellTerm_eq_zero_of_lt (he₃ : e₃ ≠ 0) (hχ0 : HasConductorExponentAt ℚ v χ 0) (k d : ℕ) {y :
    v.adicCompletion ℚ}
    (hy : Valued.v y = WithZero.exp (d : ℤ)) (w : ℂ) (E : ℤ) (hE : ((k + d : ℕ) : ℤ) + 1 ≤ E) (hE' : 1 ≤ d → ((k + d :
        ℕ) : ℤ) + 2 ≤ E)
    (n : ℤ) :
    letI := localBorel ℚ v
    ∫ x in adicShell v E, (∫ β in unitShell v n, dualIntegrand W χ w k y (β, x)
        ∂(Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ v)))) ∂(selfDualHaarAt ℚ v) = 0 := by
  letI := localBorel ℚ v
  rcases Nat.eq_zero_or_pos d with hd0 | hd1
  · have hy1 : Valued.v y ≤ 1 := hy.le.trans_eq (by rw [hd0, Nat.cast_zero, WithZero.exp_zero])
    rw [setIntegral_adicShell_setIntegral_unitShell_dualIntegrand_of_valued_le W e₁ e₂ e₃ hW hψ χ he₃ w k y hy1 n E
        (by omega),
      sphericalValue_eq_zero_of_not_dominant v (W 1) e₁ e₂ e₃ (Or.inl (by omega))]
    simp only [zero_mul]
  · have hx := gaussIntegral_inv_eq_coe_addCharUnitSetValue v hχ0 (valued_zpow_div_mul_zpow_neg v k d hy E _ rfl)
    rw [coe_addCharUnitSetValue_of_lt v (N := (k : ℤ) + d - E) (by have := hE' hd1; omega)] at hx
    rw [setIntegral_adicShell_setIntegral_unitShell_dualIntegrand_of_valued_eq W e₁ e₂ e₃ hW hψ χ he₃ w k d hd1 y hy n
        E (by omega), hx]
    simp only [mul_zero]

private theorem ballTerm_of_zero_of_add_eq (he₃ : e₃ ≠ 0) (hW1 : W 1 ≠ 0) (hχ0 : HasConductorExponentAt ℚ v χ 0) (t :
    ℂ)
    (ht : t = ((χ (NumberField.AdelicLevel.uniformizerUnit ℚ v) : ℂˣ) : ℂ)) (k d : ℕ) {y : v.adicCompletion ℚ}
    (hy : Valued.v y = WithZero.exp (d : ℤ)) (w : ℂ) (hd0 : d = 0) (n : ℤ) (m : ℕ) (hn : n + d = m) :
    letI := localBorel ℚ v
    ∫ x in adicBall v 0, (∫ β in unitShell v n, dualIntegrand W χ w k y (β, x)
        ∂(Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ v)))) ∂(selfDualHaarAt ℚ v) =
      W 1 * e₃ ^ (k + d) * (Ideal.absNorm v.asIdeal : ℂ)⁻¹ ^ (k + d) *
          (((selfDualHaarAt ℚ v).real (v.adicCompletionIntegers ℚ : Set (v.adicCompletion ℚ)) : ℂ) *
          (((selfDualHaarAt ℚ v).real (v.adicCompletionIntegers ℚ : Set (v.adicCompletion ℚ)) : ℂ) * (1 -
          (Ideal.absNorm v.asIdeal : ℂ)⁻¹))) *
        (twoRowCoeff (e₂ / e₃) (e₁ / e₃) e₃⁻¹ (k + d + m) (k + d) * (t⁻¹ * (Ideal.absNorm v.asIdeal : ℂ) ^ (-w))
            ^ n) := by
  letI := localBorel ℚ v
  have hQ : (Ideal.absNorm v.asIdeal : ℂ) ≠ 0 := absNorm_cast_ne_zero_dualSeries v
  have hy1 : Valued.v y ≤ 1 := hy.le.trans_eq (by rw [hd0, Nat.cast_zero, WithZero.exp_zero])
  have hdict := twoRowCoeff_eq_pow_mul_inv_triple W e₁ e₂ e₃ hW hψ he₃ hW1 (k + d + m) (k + d) (by omega)
  rw [setIntegral_adicBall_setIntegral_unitShell_dualIntegrand_of_valued_le W e₁ e₂ e₃ hW hψ χ he₃ w k y hy1 n,
    sphericalValue_eq_of_dominant v (W 1) e₁ e₂ e₃ (A := k + d + m) (B := k + d + m - (k +
        d)) (by omega) (by omega) (by omega) (by omega), hdict, inv_mul_cpow_eq_zpow_mul_zpow v χ hχ0 t ht w n,
    gaussIntegral_inv_zero_eq v hχ0, coe_real_adicBall_zero v]
  exact first_algebra_of_zero he₃ hQ _ _ _ _ (k + d) m (by omega)

private theorem ballTerm_of_zero_of_add_neg (he₃ : e₃ ≠ 0) (k d : ℕ) {y : v.adicCompletion ℚ} (hy : Valued.v y =
    WithZero.exp (d : ℤ)) (w : ℂ) (hd0 : d = 0) (n : ℤ) (hn : n + d < 0) :
    letI := localBorel ℚ v
    ∫ x in adicBall v 0, (∫ β in unitShell v n, dualIntegrand W χ w k y (β, x)
        ∂(Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ v)))) ∂(selfDualHaarAt ℚ v) = 0 := by
  letI := localBorel ℚ v
  have hy1 : Valued.v y ≤ 1 := hy.le.trans_eq (by rw [hd0, Nat.cast_zero, WithZero.exp_zero])
  rw [setIntegral_adicBall_setIntegral_unitShell_dualIntegrand_of_valued_le W e₁ e₂ e₃ hW hψ χ he₃ w k y hy1 n,
    sphericalValue_eq_zero_of_not_dominant v (W 1) e₁ e₂ e₃ (Or.inr (by omega))]
  simp only [zero_mul]

private theorem firstTerm_of_pos_of_add_eq (he₃ : e₃ ≠ 0) (hW1 : W 1 ≠ 0) (hχ0 : HasConductorExponentAt ℚ v χ 0) (t :
    ℂ)
    (ht : t = ((χ (NumberField.AdelicLevel.uniformizerUnit ℚ v) : ℂˣ) : ℂ)) (k d : ℕ) {y : v.adicCompletion ℚ}
    (hy : Valued.v y = WithZero.exp (d : ℤ)) (w : ℂ) (hd : 1 ≤ d) (n : ℤ) (m : ℕ) (hn : n + d = m) :
    letI := localBorel ℚ v
    ∫ x in adicBall v ((d : ℤ) - 1), (∫ β in unitShell v n, dualIntegrand W χ w k y (β, x)
        ∂(Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ v)))) ∂(selfDualHaarAt ℚ v) +
        ∫ x in adicShell v ((d : ℤ) - 1 + 1 + ((0 : ℕ) : ℤ)), (∫ β in unitShell v n, dualIntegrand W χ w k y (β, x)
        ∂(Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ v)))) ∂(selfDualHaarAt ℚ v) =
      W 1 * e₃ ^ (k + d) * (Ideal.absNorm v.asIdeal : ℂ)⁻¹ ^ (k + d) *
          (((selfDualHaarAt ℚ v).real (v.adicCompletionIntegers ℚ : Set (v.adicCompletion ℚ)) : ℂ) *
          (((selfDualHaarAt ℚ v).real (v.adicCompletionIntegers ℚ : Set (v.adicCompletion ℚ)) : ℂ) * (1 -
          (Ideal.absNorm v.asIdeal : ℂ)⁻¹))) *
        (twoRowCoeff (e₂ / e₃) (e₁ / e₃) e₃⁻¹ (k + d + m) (k + d) * (t⁻¹ * (Ideal.absNorm v.asIdeal : ℂ) ^ (-w))
            ^ n) := by
  rw [show ((d : ℤ) - 1 + 1 + ((0 : ℕ) : ℤ)) = (d : ℤ) by simp]
  letI := localBorel ℚ v
  have hQ : (Ideal.absNorm v.asIdeal : ℂ) ≠ 0 := absNorm_cast_ne_zero_dualSeries v
  have hdict := twoRowCoeff_eq_pow_mul_inv_triple W e₁ e₂ e₃ hW hψ he₃ hW1 (k + d + m) (k + d) (by omega)
  have hβ := gaussIntegral_inv_eq_coe_addCharUnitSetValue v hχ0 (valued_neg_zpow_mul_zpow v n d m hn)
  rw [coe_addCharUnitSetValue_of_nonneg v (N := m) (by omega)] at hβ
  have hx := gaussIntegral_inv_eq_coe_addCharUnitSetValue v hχ0 (valued_zpow_div_mul_zpow_neg v k d hy (d : ℤ) ((k :
      ℤ)) (by omega))
  rw [coe_addCharUnitSetValue_of_nonneg v (N := k) (by omega)] at hx
  rw [setIntegral_adicBall_setIntegral_unitShell_dualIntegrand_of_valued_eq W e₁ e₂ e₃ hW hψ χ he₃ w k d hd y hy n,
    setIntegral_adicShell_setIntegral_unitShell_dualIntegrand_of_valued_eq W e₁ e₂ e₃ hW hψ χ he₃ w k d hd y hy n d
        le_rfl,
    sphericalValue_eq_of_dominant v (W 1) e₁ e₂ e₃ (A := k + d + m) (B := k + d + m - (k +
        d)) (by omega) (by omega) (by omega) (by omega),
    sphericalValue_eq_of_dominant v (W 1) e₁ e₂ e₃ (A := k + d + m) (B := k + d + m - (k +
        d)) (by omega) (by omega) (by omega) (by omega), hdict, inv_mul_cpow_eq_zpow_mul_zpow v χ hχ0 t ht w n,
    gaussIntegral_inv_zero_eq v hχ0, setIntegral_adicBall_psiLocal_eq v k d hy, hβ, hx, Complex.ofReal_zpow,
        Complex.ofReal_natCast]
  exact first_algebra_of_pos he₃ hQ _ _ _ _ (k + d) m d hn

private theorem firstTerm_of_pos_of_add_neg (he₃ : e₃ ≠ 0) (k d : ℕ) {y : v.adicCompletion ℚ} (hy : Valued.v y =
    WithZero.exp (d : ℤ)) (w : ℂ) (hd : 1 ≤ d) (n : ℤ) (hn : n + d < 0) :
    letI := localBorel ℚ v
    ∫ x in adicBall v ((d : ℤ) - 1), (∫ β in unitShell v n, dualIntegrand W χ w k y (β, x)
        ∂(Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ v)))) ∂(selfDualHaarAt ℚ v) +
        ∫ x in adicShell v ((d : ℤ) - 1 + 1 + ((0 : ℕ) : ℤ)), (∫ β in unitShell v n, dualIntegrand W χ w k y (β, x)
        ∂(Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ v)))) ∂(selfDualHaarAt ℚ v) = 0 := by
  rw [show ((d : ℤ) - 1 + 1 + ((0 : ℕ) : ℤ)) = (d : ℤ) by simp]
  letI := localBorel ℚ v
  rw [setIntegral_adicBall_setIntegral_unitShell_dualIntegrand_of_valued_eq W e₁ e₂ e₃ hW hψ χ he₃ w k d hd y hy n,
    setIntegral_adicShell_setIntegral_unitShell_dualIntegrand_of_valued_eq W e₁ e₂ e₃ hW hψ χ he₃ w k d hd y hy n d
        le_rfl,
    sphericalValue_eq_zero_of_not_dominant v (W 1) e₁ e₂ e₃ (Or.inr (by omega)),
        sphericalValue_eq_zero_of_not_dominant v (W 1) e₁ e₂ e₃ (Or.inr (by omega))]
  simp only [zero_mul, add_zero]

private theorem closedForm_of_zero (he₃ : e₃ ≠ 0)
    (hχ0 : HasConductorExponentAt ℚ v χ 0) (t : ℂ)
    (ht : t = ((χ (NumberField.AdelicLevel.uniformizerUnit ℚ v) : ℂˣ) : ℂ))
    (ht0 : t ≠ 0) (k d : ℕ) (y : v.adicCompletion ℚ) (hy : Valued.v y = WithZero.exp (d : ℤ)) (w : ℂ)
    (hint : letI := localBorel ℚ v
      Integrable (fun p : (v.adicCompletion ℚ)ˣ × v.adicCompletion ℚ =>
        dualWhittakerFn3 W (iotaGL (diagUnitGL2 p.1) * lowerUnipotent21 p.2 *
            (weylPrime3 * transposeInv3 (torusUnipotentPoint v k y))) *
          ((χ⁻¹ p.1 : ℂˣ) : ℂ) *
          ((LanglandsTunnell.TateLocal.modulus (p.1 : v.adicCompletion ℚ) : ℝ) : ℂ) ^ (w - 1))
        ((Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ v))).prod (selfDualHaarAt ℚ v)))  (hW1 : W 1 ≠ 0) (hd0
            : d = 0) :
    letI := localBorel ℚ v
    localZetaDual31 v (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ v))) (selfDualHaarAt ℚ v) W χ w
        (torusUnipotentPoint v k y) =
      W 1 * (e₃ / (Ideal.absNorm v.asIdeal : ℂ)) ^ (k + d) *
        (t⁻¹ * (Ideal.absNorm v.asIdeal : ℂ) ^ (-w)) ^ (-((k + d + d + 1 : ℕ) : ℤ)) *
        (((selfDualHaarAt ℚ v).real (v.adicCompletionIntegers ℚ : Set (v.adicCompletion ℚ)) : ℂ) *
            (((selfDualHaarAt ℚ v).real (v.adicCompletionIntegers ℚ : Set (v.adicCompletion ℚ)) : ℂ) *
              (1 - (Ideal.absNorm v.asIdeal : ℂ)⁻¹)) *
            ∑' m : ℕ, twoRowCoeff (e₂ / e₃) (e₁ / e₃) e₃⁻¹ (k + d + m) (k + d) *
              (t⁻¹ * (Ideal.absNorm v.asIdeal : ℂ) ^ (-w)) ^ (k + d + m + 1) +
          ∑ c ∈ Finset.Ico (d - 1) (k + d),
            (if 1 ≤ d ∧ c = d - 1 then
                -(((selfDualHaarAt ℚ v).real (v.adicCompletionIntegers ℚ : Set (v.adicCompletion ℚ)) : ℂ) *
                  (Ideal.absNorm v.asIdeal : ℂ)⁻¹)
              else
                ((selfDualHaarAt ℚ v).real (v.adicCompletionIntegers ℚ : Set (v.adicCompletion ℚ)) : ℂ) *
                  (1 - (Ideal.absNorm v.asIdeal : ℂ)⁻¹)) *
              (((selfDualHaarAt ℚ v).real (v.adicCompletionIntegers ℚ : Set (v.adicCompletion ℚ)) : ℂ) *
                  (1 - (Ideal.absNorm v.asIdeal : ℂ)⁻¹) *
                  ∑' m : ℕ, twoRowCoeff (e₂ / e₃) (e₁ / e₃) e₃⁻¹ (k + d + m) c *
                    (t⁻¹ * (Ideal.absNorm v.asIdeal : ℂ) ^ (-w)) ^ (c + m + 1) -
                ((selfDualHaarAt ℚ v).real (v.adicCompletionIntegers ℚ : Set (v.adicCompletion ℚ)) : ℂ) *
                  (Ideal.absNorm v.asIdeal : ℂ)⁻¹ * twoRowCoeff (e₂ / e₃) (e₁ / e₃) e₃⁻¹ (k + d - 1) c *
                  (t⁻¹ * (Ideal.absNorm v.asIdeal : ℂ) ^ (-w)) ^ c)) := by
  letI := localBorel ℚ v
  have hsum : ∀ R : Set (v.adicCompletion ℚ), Summable fun n : ℤ => ∫ x in R, (∫ β in unitShell v n,
      dualIntegrand W χ w k y (β, x)
        ∂(Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ v)))) ∂(selfDualHaarAt ℚ v) :=
    fun R => summable_setIntegral_setIntegral_unitShell v (dualIntegrand W χ w k y) hint R
  have hbr : ∀ j ∈ Finset.range k,
      (∑' n : ℤ, ∫ x in adicShell v ((0 : ℤ) + 1 + (j : ℤ)), (∫ β in unitShell v n, dualIntegrand W χ w k y (β, x)
        ∂(Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ v)))) ∂(selfDualHaarAt ℚ v)) =
        W 1 * e₃ ^ (k + d) * (Ideal.absNorm v.asIdeal : ℂ)⁻¹ ^ (k + d) * ((addCharUnitSetValue v (((k + d - 1 - j : ℕ)
            : ℤ) - d) : ℝ) : ℂ) *
        (t⁻¹ * (Ideal.absNorm v.asIdeal : ℂ) ^ (-w)) ^ (-((k + d + d + 1 : ℕ) : ℤ)) *
        (((selfDualHaarAt ℚ v).real (v.adicCompletionIntegers ℚ : Set (v.adicCompletion ℚ)) : ℂ) * (1 -
            (Ideal.absNorm v.asIdeal : ℂ)⁻¹) * (∑' m : ℕ, twoRowCoeff (e₂ / e₃) (e₁ / e₃) e₃⁻¹ (k + d + m) (k + d - 1 -
            j) * (t⁻¹ * (Ideal.absNorm v.asIdeal : ℂ) ^ (-w)) ^ ((k + d - 1 - j) + m + 1)) +
          -(((selfDualHaarAt ℚ v).real (v.adicCompletionIntegers ℚ : Set (v.adicCompletion ℚ)) : ℂ) *
              (Ideal.absNorm v.asIdeal : ℂ)⁻¹) * (twoRowCoeff (e₂ / e₃) (e₁ / e₃) e₃⁻¹ (k + d - 1) (k + d - 1 - j) *
              (t⁻¹ * (Ideal.absNorm v.asIdeal : ℂ) ^ (-w)) ^ (k + d - 1 - j))) := by
    intro j hj
    rw [Finset.mem_range] at hj
    exact tsum_shellTerm_eq W e₁ e₂ e₃ hW hψ χ he₃ hW1 hχ0 t ht k d hy w ht0 hint (k + d - 1 -
        j) (by omega) _ (by omega)
  have hite : ∑ j ∈ Finset.range k,
        W 1 * e₃ ^ (k + d) * (Ideal.absNorm v.asIdeal : ℂ)⁻¹ ^ (k + d) * ((addCharUnitSetValue v (((k + d - 1 - j : ℕ)
            : ℤ) - d) : ℝ) : ℂ) *
        (t⁻¹ * (Ideal.absNorm v.asIdeal : ℂ) ^ (-w)) ^ (-((k + d + d + 1 : ℕ) : ℤ)) *
        (((selfDualHaarAt ℚ v).real (v.adicCompletionIntegers ℚ : Set (v.adicCompletion ℚ)) : ℂ) * (1 -
            (Ideal.absNorm v.asIdeal : ℂ)⁻¹) * (∑' m : ℕ, twoRowCoeff (e₂ / e₃) (e₁ / e₃) e₃⁻¹ (k + d + m) (k + d - 1 -
            j) * (t⁻¹ * (Ideal.absNorm v.asIdeal : ℂ) ^ (-w)) ^ ((k + d - 1 - j) + m + 1)) +
          -(((selfDualHaarAt ℚ v).real (v.adicCompletionIntegers ℚ : Set (v.adicCompletion ℚ)) : ℂ) *
              (Ideal.absNorm v.asIdeal : ℂ)⁻¹) * (twoRowCoeff (e₂ / e₃) (e₁ / e₃) e₃⁻¹ (k + d - 1) (k + d - 1 - j) *
              (t⁻¹ * (Ideal.absNorm v.asIdeal : ℂ) ^ (-w)) ^ (k + d - 1 - j))) =
      ∑ j ∈ Finset.range k, (W 1 * (e₃ / (Ideal.absNorm v.asIdeal : ℂ)) ^ (k + d) * (t⁻¹ * (Ideal.absNorm v.asIdeal :
          ℂ) ^ (-w)) ^ (-((k + d + d + 1 : ℕ) : ℤ))) * ((if 1 ≤ d ∧ k + d - 1 - j = d -
          1 then -(((selfDualHaarAt ℚ v).real (v.adicCompletionIntegers ℚ : Set (v.adicCompletion ℚ)) : ℂ) *
          (Ideal.absNorm v.asIdeal : ℂ)⁻¹) else ((selfDualHaarAt ℚ v).real (v.adicCompletionIntegers ℚ :
          Set (v.adicCompletion ℚ)) : ℂ) * (1 - (Ideal.absNorm v.asIdeal : ℂ)⁻¹)) *
          (((selfDualHaarAt ℚ v).real (v.adicCompletionIntegers ℚ : Set (v.adicCompletion ℚ)) : ℂ) * (1 -
          (Ideal.absNorm v.asIdeal : ℂ)⁻¹) * ∑' m : ℕ, twoRowCoeff (e₂ / e₃) (e₁ / e₃) e₃⁻¹ (k + d + m) (k + d - 1 -
          j) * (t⁻¹ * (Ideal.absNorm v.asIdeal : ℂ) ^ (-w)) ^ (k + d - 1 - j + m + 1) -
          ((selfDualHaarAt ℚ v).real (v.adicCompletionIntegers ℚ : Set (v.adicCompletion ℚ)) : ℂ) *
          (Ideal.absNorm v.asIdeal : ℂ)⁻¹ * twoRowCoeff (e₂ / e₃) (e₁ / e₃) e₃⁻¹ (k + d - 1) (k + d - 1 - j) * (t⁻¹ *
          (Ideal.absNorm v.asIdeal : ℂ) ^ (-w)) ^ (k + d - 1 - j))) := by
    refine Finset.sum_congr rfl fun j hj => ?_
    rw [Finset.mem_range] at hj
    rw [← ite_eq_coe_addCharUnitSetValue v d (k + d - 1 - j) (by omega)]
    ring
  rw [localZetaDual31_torusUnipotentPoint_eq_tsum W χ w k y hint,
    tsum_eq_tsum_add_sum_tsum _ (fun n => ∫ x in adicBall v 0, (∫ β in unitShell v n, dualIntegrand W χ w k y (β, x)
        ∂(Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ v)))) ∂(selfDualHaarAt ℚ v)) (fun n j => ∫ x in
            adicShell v ((0 : ℤ) + 1 + (j : ℤ)), (∫ β in unitShell v n, dualIntegrand W χ w k y (β, x)
        ∂(Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ v)))) ∂(selfDualHaarAt ℚ v)) k
      (fun n => setIntegral_unitShell_integral_eq_setIntegral_adicBall_add_tsum v (dualIntegrand W χ w k y) hint n 0)
      (fun n j hj => shellTerm_eq_zero_of_lt W e₁ e₂ e₃ hW hψ χ he₃ hχ0 k d hy w _ (by omega) (fun h => by omega) n)
          (hsum _) (fun j => hsum _),
    tsum_eq_of_first_group _ (hsum _) (W 1 * e₃ ^ (k + d) * (Ideal.absNorm v.asIdeal : ℂ)⁻¹ ^ (k + d) *
        (((selfDualHaarAt ℚ v).real (v.adicCompletionIntegers ℚ : Set (v.adicCompletion ℚ)) : ℂ) *
        (((selfDualHaarAt ℚ v).real (v.adicCompletionIntegers ℚ : Set (v.adicCompletion ℚ)) : ℂ) * (1 -
        (Ideal.absNorm v.asIdeal : ℂ)⁻¹)))) _ (zeta_variable_ne_zero v t ht0 w) (fun m => twoRowCoeff (e₂ / e₃) (e₁ /
        e₃) e₃⁻¹ (k + d + m) (k + d)) (k + d) d
      (fun n m hn => ballTerm_of_zero_of_add_eq W e₁ e₂ e₃ hW hψ χ he₃ hW1 hχ0 t ht k d hy w hd0 n m hn) (fun n hn =>
          ballTerm_of_zero_of_add_neg W e₁ e₂ e₃ hW hψ χ he₃ k d hy w hd0 n hn),
    Finset.sum_congr rfl hbr, hite, sum_Ico_eq_sum_range_sub _ (d - 1) (k + d) k (by omega), mul_add, Finset.mul_sum]
  ring

private theorem closedForm_of_pos (he₃ : e₃ ≠ 0)
    (hχ0 : HasConductorExponentAt ℚ v χ 0) (t : ℂ)
    (ht : t = ((χ (NumberField.AdelicLevel.uniformizerUnit ℚ v) : ℂˣ) : ℂ))
    (ht0 : t ≠ 0) (k d : ℕ) (y : v.adicCompletion ℚ) (hy : Valued.v y = WithZero.exp (d : ℤ)) (w : ℂ)
    (hint : letI := localBorel ℚ v
      Integrable (fun p : (v.adicCompletion ℚ)ˣ × v.adicCompletion ℚ =>
        dualWhittakerFn3 W (iotaGL (diagUnitGL2 p.1) * lowerUnipotent21 p.2 *
            (weylPrime3 * transposeInv3 (torusUnipotentPoint v k y))) *
          ((χ⁻¹ p.1 : ℂˣ) : ℂ) *
          ((LanglandsTunnell.TateLocal.modulus (p.1 : v.adicCompletion ℚ) : ℝ) : ℂ) ^ (w - 1))
        ((Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ v))).prod (selfDualHaarAt ℚ v)))  (hW1 : W 1 ≠ 0) (hd :
            1 ≤ d) :
    letI := localBorel ℚ v
    localZetaDual31 v (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ v))) (selfDualHaarAt ℚ v) W χ w
        (torusUnipotentPoint v k y) =
      W 1 * (e₃ / (Ideal.absNorm v.asIdeal : ℂ)) ^ (k + d) *
        (t⁻¹ * (Ideal.absNorm v.asIdeal : ℂ) ^ (-w)) ^ (-((k + d + d + 1 : ℕ) : ℤ)) *
        (((selfDualHaarAt ℚ v).real (v.adicCompletionIntegers ℚ : Set (v.adicCompletion ℚ)) : ℂ) *
            (((selfDualHaarAt ℚ v).real (v.adicCompletionIntegers ℚ : Set (v.adicCompletion ℚ)) : ℂ) *
              (1 - (Ideal.absNorm v.asIdeal : ℂ)⁻¹)) *
            ∑' m : ℕ, twoRowCoeff (e₂ / e₃) (e₁ / e₃) e₃⁻¹ (k + d + m) (k + d) *
              (t⁻¹ * (Ideal.absNorm v.asIdeal : ℂ) ^ (-w)) ^ (k + d + m + 1) +
          ∑ c ∈ Finset.Ico (d - 1) (k + d),
            (if 1 ≤ d ∧ c = d - 1 then
                -(((selfDualHaarAt ℚ v).real (v.adicCompletionIntegers ℚ : Set (v.adicCompletion ℚ)) : ℂ) *
                  (Ideal.absNorm v.asIdeal : ℂ)⁻¹)
              else
                ((selfDualHaarAt ℚ v).real (v.adicCompletionIntegers ℚ : Set (v.adicCompletion ℚ)) : ℂ) *
                  (1 - (Ideal.absNorm v.asIdeal : ℂ)⁻¹)) *
              (((selfDualHaarAt ℚ v).real (v.adicCompletionIntegers ℚ : Set (v.adicCompletion ℚ)) : ℂ) *
                  (1 - (Ideal.absNorm v.asIdeal : ℂ)⁻¹) *
                  ∑' m : ℕ, twoRowCoeff (e₂ / e₃) (e₁ / e₃) e₃⁻¹ (k + d + m) c *
                    (t⁻¹ * (Ideal.absNorm v.asIdeal : ℂ) ^ (-w)) ^ (c + m + 1) -
                ((selfDualHaarAt ℚ v).real (v.adicCompletionIntegers ℚ : Set (v.adicCompletion ℚ)) : ℂ) *
                  (Ideal.absNorm v.asIdeal : ℂ)⁻¹ * twoRowCoeff (e₂ / e₃) (e₁ / e₃) e₃⁻¹ (k + d - 1) c *
                  (t⁻¹ * (Ideal.absNorm v.asIdeal : ℂ) ^ (-w)) ^ c)) := by
  letI := localBorel ℚ v
  have hsum : ∀ R : Set (v.adicCompletion ℚ), Summable fun n : ℤ => ∫ x in R, (∫ β in unitShell v n,
      dualIntegrand W χ w k y (β, x)
        ∂(Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ v)))) ∂(selfDualHaarAt ℚ v) :=
    fun R => summable_setIntegral_setIntegral_unitShell v (dualIntegrand W χ w k y) hint R
  have hbr : ∀ j ∈ Finset.range (k + 1),
      (∑' n : ℤ, ∫ x in adicShell v ((d : ℤ) - 1 + 1 + ((j + 1 : ℕ) : ℤ)), (∫ β in unitShell v n,
          dualIntegrand W χ w k y (β, x)
        ∂(Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ v)))) ∂(selfDualHaarAt ℚ v)) =
        W 1 * e₃ ^ (k + d) * (Ideal.absNorm v.asIdeal : ℂ)⁻¹ ^ (k + d) * ((addCharUnitSetValue v (((k + d - 1 - j : ℕ)
            : ℤ) - d) : ℝ) : ℂ) *
        (t⁻¹ * (Ideal.absNorm v.asIdeal : ℂ) ^ (-w)) ^ (-((k + d + d + 1 : ℕ) : ℤ)) *
        (((selfDualHaarAt ℚ v).real (v.adicCompletionIntegers ℚ : Set (v.adicCompletion ℚ)) : ℂ) * (1 -
            (Ideal.absNorm v.asIdeal : ℂ)⁻¹) * (∑' m : ℕ, twoRowCoeff (e₂ / e₃) (e₁ / e₃) e₃⁻¹ (k + d + m) (k + d - 1 -
            j) * (t⁻¹ * (Ideal.absNorm v.asIdeal : ℂ) ^ (-w)) ^ ((k + d - 1 - j) + m + 1)) +
          -(((selfDualHaarAt ℚ v).real (v.adicCompletionIntegers ℚ : Set (v.adicCompletion ℚ)) : ℂ) *
              (Ideal.absNorm v.asIdeal : ℂ)⁻¹) * (twoRowCoeff (e₂ / e₃) (e₁ / e₃) e₃⁻¹ (k + d - 1) (k + d - 1 - j) *
              (t⁻¹ * (Ideal.absNorm v.asIdeal : ℂ) ^ (-w)) ^ (k + d - 1 - j))) := by
    intro j hj
    rw [Finset.mem_range] at hj
    exact tsum_shellTerm_eq W e₁ e₂ e₃ hW hψ χ he₃ hW1 hχ0 t ht k d hy w ht0 hint (k + d - 1 -
        j) (by omega) _ (by omega)
  have hite : ∑ j ∈ Finset.range (k + 1),
        W 1 * e₃ ^ (k + d) * (Ideal.absNorm v.asIdeal : ℂ)⁻¹ ^ (k + d) * ((addCharUnitSetValue v (((k + d - 1 - j : ℕ)
            : ℤ) - d) : ℝ) : ℂ) *
        (t⁻¹ * (Ideal.absNorm v.asIdeal : ℂ) ^ (-w)) ^ (-((k + d + d + 1 : ℕ) : ℤ)) *
        (((selfDualHaarAt ℚ v).real (v.adicCompletionIntegers ℚ : Set (v.adicCompletion ℚ)) : ℂ) * (1 -
            (Ideal.absNorm v.asIdeal : ℂ)⁻¹) * (∑' m : ℕ, twoRowCoeff (e₂ / e₃) (e₁ / e₃) e₃⁻¹ (k + d + m) (k + d - 1 -
            j) * (t⁻¹ * (Ideal.absNorm v.asIdeal : ℂ) ^ (-w)) ^ ((k + d - 1 - j) + m + 1)) +
          -(((selfDualHaarAt ℚ v).real (v.adicCompletionIntegers ℚ : Set (v.adicCompletion ℚ)) : ℂ) *
              (Ideal.absNorm v.asIdeal : ℂ)⁻¹) * (twoRowCoeff (e₂ / e₃) (e₁ / e₃) e₃⁻¹ (k + d - 1) (k + d - 1 - j) *
              (t⁻¹ * (Ideal.absNorm v.asIdeal : ℂ) ^ (-w)) ^ (k + d - 1 - j))) =
      ∑ j ∈ Finset.range (k + 1), (W 1 * (e₃ / (Ideal.absNorm v.asIdeal : ℂ)) ^ (k + d) * (t⁻¹ *
          (Ideal.absNorm v.asIdeal : ℂ) ^ (-w)) ^ (-((k + d + d + 1 : ℕ) : ℤ))) * ((if 1 ≤ d ∧ k + d - 1 - j = d -
          1 then -(((selfDualHaarAt ℚ v).real (v.adicCompletionIntegers ℚ : Set (v.adicCompletion ℚ)) : ℂ) *
          (Ideal.absNorm v.asIdeal : ℂ)⁻¹) else ((selfDualHaarAt ℚ v).real (v.adicCompletionIntegers ℚ :
          Set (v.adicCompletion ℚ)) : ℂ) * (1 - (Ideal.absNorm v.asIdeal : ℂ)⁻¹)) *
          (((selfDualHaarAt ℚ v).real (v.adicCompletionIntegers ℚ : Set (v.adicCompletion ℚ)) : ℂ) * (1 -
          (Ideal.absNorm v.asIdeal : ℂ)⁻¹) * ∑' m : ℕ, twoRowCoeff (e₂ / e₃) (e₁ / e₃) e₃⁻¹ (k + d + m) (k + d - 1 -
          j) * (t⁻¹ * (Ideal.absNorm v.asIdeal : ℂ) ^ (-w)) ^ (k + d - 1 - j + m + 1) -
          ((selfDualHaarAt ℚ v).real (v.adicCompletionIntegers ℚ : Set (v.adicCompletion ℚ)) : ℂ) *
          (Ideal.absNorm v.asIdeal : ℂ)⁻¹ * twoRowCoeff (e₂ / e₃) (e₁ / e₃) e₃⁻¹ (k + d - 1) (k + d - 1 - j) * (t⁻¹ *
          (Ideal.absNorm v.asIdeal : ℂ) ^ (-w)) ^ (k + d - 1 - j))) := by
    refine Finset.sum_congr rfl fun j hj => ?_
    rw [Finset.mem_range] at hj
    rw [← ite_eq_coe_addCharUnitSetValue v d (k + d - 1 - j) (by omega)]
    ring
  rw [localZetaDual31_torusUnipotentPoint_eq_tsum W χ w k y hint,
    tsum_eq_tsum_add_add_sum_tsum_succ _ (fun n => ∫ x in adicBall v ((d : ℤ) - 1), (∫ β in unitShell v n,
        dualIntegrand W χ w k y (β, x)
        ∂(Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ v)))) ∂(selfDualHaarAt ℚ v)) (fun n j => ∫ x in
            adicShell v ((d : ℤ) - 1 + 1 + (j : ℤ)), (∫ β in unitShell v n, dualIntegrand W χ w k y (β, x)
        ∂(Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ v)))) ∂(selfDualHaarAt ℚ v)) (k + 1)
      (fun n => setIntegral_unitShell_integral_eq_setIntegral_adicBall_add_tsum v (dualIntegrand W χ w k y) hint n ((d
          : ℤ) - 1))
      (fun n j hj => shellTerm_eq_zero_of_lt W e₁ e₂ e₃ hW hψ χ he₃ hχ0 k d hy w _ (by omega) (fun _ => by omega) n)
          (hsum _) (fun j => hsum _),
    tsum_eq_of_first_group _ ((hsum _).add (hsum _)) (W 1 * e₃ ^ (k + d) * (Ideal.absNorm v.asIdeal : ℂ)⁻¹ ^ (k + d) *
        (((selfDualHaarAt ℚ v).real (v.adicCompletionIntegers ℚ : Set (v.adicCompletion ℚ)) : ℂ) *
        (((selfDualHaarAt ℚ v).real (v.adicCompletionIntegers ℚ : Set (v.adicCompletion ℚ)) : ℂ) * (1 -
        (Ideal.absNorm v.asIdeal : ℂ)⁻¹)))) _ (zeta_variable_ne_zero v t ht0 w) (fun m => twoRowCoeff (e₂ / e₃) (e₁ /
        e₃) e₃⁻¹ (k + d + m) (k + d)) (k + d) d
      (fun n m hn => firstTerm_of_pos_of_add_eq W e₁ e₂ e₃ hW hψ χ he₃ hW1 hχ0 t ht k d hy w hd n m hn) (fun n hn =>
          firstTerm_of_pos_of_add_neg W e₁ e₂ e₃ hW hψ χ he₃ k d hy w hd n hn),
    Finset.sum_congr rfl hbr, hite, sum_Ico_eq_sum_range_sub _ (d - 1) (k + d) (k + 1) (by omega), mul_add,
        Finset.mul_sum]
  ring

private theorem localZetaDual31_torusUnipotentPoint_of_hasConductorExponentAt_zero (he₃ : e₃ ≠ 0)
    (hχ0 : HasConductorExponentAt ℚ v χ 0) (t : ℂ)
    (ht : t = ((χ (NumberField.AdelicLevel.uniformizerUnit ℚ v) : ℂˣ) : ℂ))
    (ht0 : t ≠ 0) (k d : ℕ) (y : v.adicCompletion ℚ) (hy : Valued.v y = WithZero.exp (d : ℤ)) (w : ℂ)
    (hint : letI := localBorel ℚ v
      Integrable (fun p : (v.adicCompletion ℚ)ˣ × v.adicCompletion ℚ =>
        dualWhittakerFn3 W (iotaGL (diagUnitGL2 p.1) * lowerUnipotent21 p.2 *
            (weylPrime3 * transposeInv3 (torusUnipotentPoint v k y))) *
          ((χ⁻¹ p.1 : ℂˣ) : ℂ) *
          ((LanglandsTunnell.TateLocal.modulus (p.1 : v.adicCompletion ℚ) : ℝ) : ℂ) ^ (w - 1))
        ((Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ v))).prod (selfDualHaarAt ℚ v))) :
    letI := localBorel ℚ v
    localZetaDual31 v (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ v))) (selfDualHaarAt ℚ v) W χ w
        (torusUnipotentPoint v k y) =
      W 1 * (e₃ / (Ideal.absNorm v.asIdeal : ℂ)) ^ (k + d) *
        (t⁻¹ * (Ideal.absNorm v.asIdeal : ℂ) ^ (-w)) ^ (-((k + d + d + 1 : ℕ) : ℤ)) *
        (((selfDualHaarAt ℚ v).real (v.adicCompletionIntegers ℚ : Set (v.adicCompletion ℚ)) : ℂ) *
            (((selfDualHaarAt ℚ v).real (v.adicCompletionIntegers ℚ : Set (v.adicCompletion ℚ)) : ℂ) *
              (1 - (Ideal.absNorm v.asIdeal : ℂ)⁻¹)) *
            ∑' m : ℕ, twoRowCoeff (e₂ / e₃) (e₁ / e₃) e₃⁻¹ (k + d + m) (k + d) *
              (t⁻¹ * (Ideal.absNorm v.asIdeal : ℂ) ^ (-w)) ^ (k + d + m + 1) +
          ∑ c ∈ Finset.Ico (d - 1) (k + d),
            (if 1 ≤ d ∧ c = d - 1 then
                -(((selfDualHaarAt ℚ v).real (v.adicCompletionIntegers ℚ : Set (v.adicCompletion ℚ)) : ℂ) *
                  (Ideal.absNorm v.asIdeal : ℂ)⁻¹)
              else
                ((selfDualHaarAt ℚ v).real (v.adicCompletionIntegers ℚ : Set (v.adicCompletion ℚ)) : ℂ) *
                  (1 - (Ideal.absNorm v.asIdeal : ℂ)⁻¹)) *
              (((selfDualHaarAt ℚ v).real (v.adicCompletionIntegers ℚ : Set (v.adicCompletion ℚ)) : ℂ) *
                  (1 - (Ideal.absNorm v.asIdeal : ℂ)⁻¹) *
                  ∑' m : ℕ, twoRowCoeff (e₂ / e₃) (e₁ / e₃) e₃⁻¹ (k + d + m) c *
                    (t⁻¹ * (Ideal.absNorm v.asIdeal : ℂ) ^ (-w)) ^ (c + m + 1) -
                ((selfDualHaarAt ℚ v).real (v.adicCompletionIntegers ℚ : Set (v.adicCompletion ℚ)) : ℂ) *
                  (Ideal.absNorm v.asIdeal : ℂ)⁻¹ * twoRowCoeff (e₂ / e₃) (e₁ / e₃) e₃⁻¹ (k + d - 1) c *
                  (t⁻¹ * (Ideal.absNorm v.asIdeal : ℂ) ^ (-w)) ^ c)) := by
  by_cases hW1 : W 1 = 0
  · have hW0 : ∀ g, W g = 0 := fun g =>
      congrFun (eq_zero_of_apply_one_eq_zero_of_psiLocal v W e₁ e₂ e₃ hW hψ hW1) g
    rw [localZetaDual31_eq_zero_of_forall_eq_zero (v := v) (χ := χ) (hW0 := hW0) w (torusUnipotentPoint v k y), hW1]
    simp only [zero_mul]
  · rcases Nat.eq_zero_or_pos d with hd0 | hd1
    · exact closedForm_of_zero W e₁ e₂ e₃ hW hψ χ he₃ hχ0 t ht ht0 k d y hy w hint hW1 hd0
    · exact closedForm_of_pos W e₁ e₂ e₃ hW hψ χ he₃ hχ0 t ht ht0 k d y hy w hint hW1 hd1

end Values
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_laurent_localZeta_eq_gl3LFactorPoly_of_sphericalData.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_exists_laurent_localZeta_eq_gl3LFactorPoly_of_sphericalData.LanglandsTunnell.CubicInduction"

end
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_laurent_localZeta_eq_gl3LFactorPoly_of_sphericalData.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_exists_laurent_localZeta_eq_gl3LFactorPoly_of_sphericalData.LanglandsTunnell.CubicInduction"
end
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_laurent_localZeta_eq_gl3LFactorPoly_of_sphericalData.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_exists_laurent_localZeta_eq_gl3LFactorPoly_of_sphericalData.LanglandsTunnell.CubicInduction"

section

set_option autoImplicit false

open IsDedekindDomain NumberField NumberField.TateGlobal AutomorphicForm LanglandsTunnell.Converse LanglandsTunnell.RankinSelberg LanglandsTunnell.TateLocal MeasureTheory

p2m_open "IsDedekindDomain.HeightOneSpectrum~Extension LanglandsTunnell.CubicInduction P2MW.S_LanglandsTunnell_CubicInduction_exists_laurent_localZeta_eq_gl3LFactorPoly_of_sphericalData.LanglandsTunnell.CubicInduction NumberField.StandardAddChar"

noncomputable section

section GrowthCores

private noncomputable def sphericalBase (B : ℝ) (e₃ q : ℂ) : ℝ :=
  max 1 (max B (max ‖e₃‖ (max ‖e₃‖⁻¹ ‖q⁻¹‖)))

private theorem one_le_sphericalBase (B : ℝ) (e₃ q : ℂ) : 1 ≤ sphericalBase B e₃ q := le_max_left _ _

private theorem norm_zpow_le_sphericalBase_pow (B : ℝ) (e₃ q : ℂ) (m : ℤ) (N : ℕ) (hm : m.natAbs ≤ N) :
    ‖e₃ ^ m‖ ≤ sphericalBase B e₃ q ^ N := by
  have h1 : 1 ≤ sphericalBase B e₃ q := one_le_sphericalBase B e₃ q
  have h3 : ‖e₃‖ ≤ sphericalBase B e₃ q :=
    (le_max_left _ _).trans ((le_max_right _ _).trans (le_max_right _ _))
  have h4 : ‖e₃‖⁻¹ ≤ sphericalBase B e₃ q :=
    (le_max_left _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans (le_max_right _ _)))
  rw [norm_zpow]
  rcases le_or_gt 0 m with hm0 | hm0
  · obtain ⟨a, rfl⟩ : ∃ a : ℕ, m = a := ⟨m.toNat, (Int.toNat_of_nonneg hm0).symm⟩
    rw [zpow_natCast]
    calc ‖e₃‖ ^ a ≤ sphericalBase B e₃ q ^ a := pow_le_pow_left₀ (norm_nonneg _) h3 a
      _ ≤ sphericalBase B e₃ q ^ N := pow_le_pow_right₀ h1 (by simpa using hm)
  · obtain ⟨a, ha⟩ : ∃ a : ℕ, m = -a := ⟨m.natAbs, by omega⟩
    rw [ha, zpow_neg, zpow_natCast, ← inv_pow]
    calc ‖e₃‖⁻¹ ^ a ≤ sphericalBase B e₃ q ^ a := pow_le_pow_left₀ (inv_nonneg.2 (norm_nonneg _)) h4 a
      _ ≤ sphericalBase B e₃ q ^ N := pow_le_pow_right₀ h1 (by subst ha; simpa using hm)

private theorem norm_ite_closed_form_le (W1 e₃ q : ℂ) (B : ℝ) (S : ℕ → ℕ → ℂ)
    (hS : ∀ a b, ‖S a b‖ ≤ 2 * B ^ (a + b + 1)) (dom : Prop) [Decidable dom] (lam : Fin 3 → ℤ) (N : ℕ)
    (hN : dom → (lam 0 - lam 2).toNat + (lam 1 - lam 2).toNat + 1 ≤ N ∧ (lam 2).natAbs ≤ N) :
    ‖(if dom then e₃ ^ lam 2 * (W1 * (q⁻¹ ^ (lam 0 - lam 2).toNat *
        S (lam 0 - lam 2).toNat (lam 1 - lam 2).toNat)) else 0)‖ ≤
      2 * ‖W1‖ * sphericalBase B e₃ q ^ (3 * N) := by
  have h1 : 1 ≤ sphericalBase B e₃ q := one_le_sphericalBase B e₃ q
  have h0 : 0 ≤ sphericalBase B e₃ q := zero_le_one.trans h1
  split_ifs with hdom
  · obtain ⟨hab, h2⟩ := hN hdom
    have hB : B ≤ sphericalBase B e₃ q := (le_max_left _ _).trans (le_max_right _ _)
    have hq : ‖q⁻¹‖ ≤ sphericalBase B e₃ q :=
      (le_max_right _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans (le_max_right _ _)))
    have hBnn : 0 ≤ B := by
      have := hS 0 0
      have h2' : (0 : ℝ) ≤ 2 * B ^ (0 + 0 + 1) := (norm_nonneg _).trans this
      simp only [zero_add, pow_one] at h2'
      linarith
    have hSle : ‖S (lam 0 - lam 2).toNat (lam 1 - lam 2).toNat‖ ≤ 2 * sphericalBase B e₃ q ^ N :=
      (hS _ _).trans (by
        have := (pow_le_pow_left₀ hBnn hB _).trans (pow_le_pow_right₀ h1 hab)
        linarith)
    have hqle : ‖q⁻¹ ^ (lam 0 - lam 2).toNat‖ ≤ sphericalBase B e₃ q ^ N := by
      rw [norm_pow]
      calc ‖q⁻¹‖ ^ (lam 0 - lam 2).toNat ≤ sphericalBase B e₃ q ^ (lam 0 - lam 2).toNat :=
            pow_le_pow_left₀ (norm_nonneg _) hq _
        _ ≤ sphericalBase B e₃ q ^ N := pow_le_pow_right₀ h1 (by omega)
    have hzle : ‖e₃ ^ lam 2‖ ≤ sphericalBase B e₃ q ^ N := norm_zpow_le_sphericalBase_pow B e₃ q _ N h2
    calc ‖e₃ ^ lam 2 * (W1 * (q⁻¹ ^ (lam 0 - lam 2).toNat * S (lam 0 - lam 2).toNat (lam 1 - lam 2).toNat))‖
        = ‖e₃ ^ lam 2‖ * (‖W1‖ * (‖q⁻¹ ^ (lam 0 - lam 2).toNat‖ *
            ‖S (lam 0 - lam 2).toNat (lam 1 - lam 2).toNat‖)) := by
          simp only [norm_mul]
      _ ≤ sphericalBase B e₃ q ^ N * (‖W1‖ * (sphericalBase B e₃ q ^ N * (2 * sphericalBase B e₃ q ^ N))) := by
          gcongr
      _ = 2 * ‖W1‖ * sphericalBase B e₃ q ^ (3 * N) := by ring
  · rw [norm_zero]
    positivity

private theorem exists_forall_mul_pow_mul_zpow_le (K₀ M t : ℝ) (hM : 1 ≤ M) (ht : 0 < t) (A s : ℕ)
    (n₀ : ℤ) :
    ∃ C ρ : ℝ, 0 < ρ ∧ ∀ n : ℤ, n₀ ≤ n → K₀ * M ^ (3 * (A + s * (n - n₀).toNat)) * t ^ n ≤ C * ρ ^ n := by
  have hM0 : 0 < M := zero_lt_one.trans_le hM
  have hMs : 0 < M ^ (3 * s) := pow_pos hM0 _
  refine ⟨K₀ * M ^ (3 * A) * (M ^ (3 * s)) ^ (-n₀), M ^ (3 * s) * t, mul_pos hMs ht, fun n hn => ?_⟩
  obtain ⟨j, hj⟩ : ∃ j : ℕ, n - n₀ = j := ⟨(n - n₀).toNat, (Int.toNat_of_nonneg (by omega)).symm⟩
  have key : M ^ (3 * (A + s * (n - n₀).toNat)) = M ^ (3 * A) * (M ^ (3 * s)) ^ (n - n₀) := by
    rw [hj, Int.toNat_natCast, zpow_natCast, ← pow_mul, ← pow_add]
    congr 1
    ring
  rw [key, mul_zpow, zpow_sub₀ hMs.ne', div_eq_mul_inv, ← zpow_neg]
  apply le_of_eq
  ring

private theorem exists_forall_of_oracle {U X : Type*} (shell : ℤ → U → Prop) (F : U → X → ℂ) (c : U → ℂ)
    (small : X → Prop) (Cχ t M W1n : ℝ) (ht : 0 < t) (hM : 1 ≤ M) (hW1n : 0 ≤ W1n)
    (hc : ∀ (n : ℤ) (β : U), shell n β → ‖c β‖ ≤ Cχ * t ^ n) (n₀ : ℤ) (A s : ℕ)
    (oracle : ∀ (n : ℤ) (β : U) (x : X), shell n β →
      ∃ (dom : Prop) (val : ℂ), (F β x ≠ 0 → dom) ∧ ‖F β x‖ ≤ ‖val‖ ∧
        (dom → n₀ ≤ n ∧ small x) ∧
        (n₀ ≤ n → ‖val‖ ≤ 2 * W1n * M ^ (3 * (A + s * (n - n₀).toNat)))) :
    ∃ C ρ : ℝ, 0 < ρ ∧
      (∀ (n : ℤ) (β : U) (x : X), shell n β → F β x ≠ 0 → n₀ ≤ n ∧ small x) ∧
      ∀ (n : ℤ) (β : U) (x : X), shell n β → n₀ ≤ n → ‖F β x * c β‖ ≤ C * ρ ^ n := by
  obtain ⟨C, ρ, hρ, hC⟩ :=
    exists_forall_mul_pow_mul_zpow_le (2 * W1n * Cχ) M t hM ht A s n₀
  refine ⟨C, ρ, hρ, fun n β x hβ hF => ?_, fun n β x hβ hn => ?_⟩
  · obtain ⟨dom, val, hdom, -, hsupp, -⟩ := oracle n β x hβ
    exact hsupp (hdom hF)
  · obtain ⟨dom, val, -, hle, -, hval⟩ := oracle n β x hβ
    rw [norm_mul]
    calc ‖F β x‖ * ‖c β‖ ≤ (2 * W1n * M ^ (3 * (A + s * (n - n₀).toNat))) * (Cχ * t ^ n) :=
          mul_le_mul (hle.trans (hval hn)) (hc n β hβ) (norm_nonneg _) (by positivity)
      _ = 2 * W1n * Cχ * M ^ (3 * (A + s * (n - n₀).toNat)) * t ^ n := by ring
      _ ≤ C * ρ ^ n := hC n hn

end GrowthCores
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_laurent_localZeta_eq_gl3LFactorPoly_of_sphericalData.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_exists_laurent_localZeta_eq_gl3LFactorPoly_of_sphericalData.LanglandsTunnell.CubicInduction"

section GrowthPrivates

variable {v : HeightOneSpectrum (𝓞 ℚ)}

private theorem iotaGL_diagUnitGL2_mul (α u : (v.adicCompletion ℚ)ˣ) :
    (iotaGL (diagUnitGL2 (α * u)) : LocalGL3 v) = iotaGL (diagUnitGL2 α) * iotaGL (diagUnitGL2 u) := by
  rw [← map_mul]
  congr 1
  refine Units.ext ?_
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

private theorem lowerUnipotent21_add (x z : v.adicCompletion ℚ) :
    (lowerUnipotent21 (x + z) : LocalGL3 v) = lowerUnipotent21 x * lowerUnipotent21 z := by
  refine Units.ext ?_
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three]

private theorem isRightInvariant_dualWhittakerFn3_of {W : LocalGL3 v → ℂ}
    (hU : IsRightInvariant (localMaximalCompact3 (𝓞 ℚ) ℚ v) W) :
    IsRightInvariant (localMaximalCompact3 (𝓞 ℚ) ℚ v) (dualWhittakerFn3 W) := by
  intro g u hu
  rw [dualWhittakerFn3_eq_comp_contragredient3 hU]
  simp only [map_mul]
  exact hU _ _ ((contragredient3_mem_localMaximalCompact3_iff v u).2 hu)

end GrowthPrivates
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_laurent_localZeta_eq_gl3LFactorPoly_of_sphericalData.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_exists_laurent_localZeta_eq_gl3LFactorPoly_of_sphericalData.LanglandsTunnell.CubicInduction"

section BoundPrivates

variable {v : HeightOneSpectrum (𝓞 ℚ)}

private theorem norm_sphericalValue_le (W1 e₁ e₂ e₃ : ℂ) (lam : Fin 3 → ℤ) (N : ℕ)
    (hN : lam 1 ≤ lam 0 ∧ lam 2 ≤ lam 1 →
      (lam 0 - lam 2).toNat + (lam 1 - lam 2).toNat + 1 ≤ N ∧ (lam 2).natAbs ≤ N) :
    ‖sphericalValue W1 e₁ e₂ e₃ (cNormQ v) lam‖ ≤
      2 * ‖W1‖ * sphericalBase (1 + ‖e₁‖ + ‖e₂‖ + ‖e₃‖) e₃ (cNormQ v) ^ (3 * N) := by
  unfold sphericalValue
  exact norm_ite_closed_form_le W1 e₃ (cNormQ v) _ (twoRowCoeff e₁ e₂ e₃) (norm_twoRowCoeff_le e₁ e₂ e₃) _ lam N hN

private theorem valued_ratPrimeUnit : Valued.v ((ratPrimeUnit v : (v.adicCompletion ℚ)ˣ) : v.adicCompletion ℚ) =
    WithZero.exp (-1 : ℤ) := by
  show Valued.v (ratPrimeAt v) = _
  rw [valued_ratPrimeAt_eq_valued_varpi, AdelicLevel.valued_uniformizerUnit ℚ v]

private theorem norm_coe_apply_le (χ : (v.adicCompletion ℚ)ˣ →* ℂˣ) (Cχ : ℝ)
    (hχ : ∀ u : (v.adicCompletion ℚ)ˣ, Valued.v (u : v.adicCompletion ℚ) = 1 → ‖((χ u : ℂˣ) : ℂ)‖ ≤ Cχ)
    (n : ℤ) (α : (v.adicCompletion ℚ)ˣ) (hα : Valued.v (α : v.adicCompletion ℚ) = WithZero.exp (-n)) :
    ‖((χ α : ℂˣ) : ℂ)‖ ≤ Cχ * ‖((χ (ratPrimeUnit v) : ℂˣ) : ℂ)‖ ^ n := by
  have hu : Valued.v ((((ratPrimeUnit v ^ n)⁻¹ * α : (v.adicCompletion ℚ)ˣ)) : v.adicCompletion ℚ) = 1 := by
    rw [Units.val_mul, Valuation.map_mul, Units.val_inv_eq_inv_val, map_inv₀, Units.val_zpow_eq_zpow_val,
      map_zpow₀, valued_ratPrimeUnit, hα]
    simp
  have hdec : α = ratPrimeUnit v ^ n * ((ratPrimeUnit v ^ n)⁻¹ * α) := (mul_inv_cancel_left _ _).symm
  calc ‖((χ α : ℂˣ) : ℂ)‖ = ‖((χ (ratPrimeUnit v ^ n * ((ratPrimeUnit v ^ n)⁻¹ * α)) : ℂˣ) : ℂ)‖ := by
        rw [← hdec]
    _ = ‖((χ (ratPrimeUnit v) : ℂˣ) : ℂ)‖ ^ n * ‖((χ ((ratPrimeUnit v ^ n)⁻¹ * α) : ℂˣ) : ℂ)‖ := by
        rw [map_mul, map_zpow, Units.val_mul, Units.val_zpow_eq_zpow_val, norm_mul, norm_zpow]
    _ ≤ ‖((χ (ratPrimeUnit v) : ℂˣ) : ℂ)‖ ^ n * Cχ := by
        gcongr
        exact hχ _ hu
    _ = Cχ * ‖((χ (ratPrimeUnit v) : ℂˣ) : ℂ)‖ ^ n := mul_comm _ _

private theorem forall_norm_inv_apply_le (χ : (v.adicCompletion ℚ)ˣ →* ℂˣ) (Cχ : ℝ)
    (hχ : ∀ u : (v.adicCompletion ℚ)ˣ, Valued.v (u : v.adicCompletion ℚ) = 1 → ‖((χ u : ℂˣ) : ℂ)‖ ≤ Cχ) :
    ∀ u : (v.adicCompletion ℚ)ˣ, Valued.v (u : v.adicCompletion ℚ) = 1 → ‖((χ⁻¹ u : ℂˣ) : ℂ)‖ ≤ Cχ := by
  intro u hu
  rw [MonoidHom.inv_apply, ← map_inv]
  exact hχ _ (by rw [Units.val_inv_eq_inv_val, map_inv₀, hu, inv_one])

private theorem exists_valued_eq_exp_of_not_le {x : v.adicCompletion ℚ} (hx : ¬ Valued.v x ≤ 1) :
    ∃ d : ℕ, 1 ≤ d ∧ Valued.v x = WithZero.exp (d : ℤ) := by
  have hx0 : Valued.v x ≠ 0 := fun h => hx (by rw [h]; exact zero_le')
  have hlog : 0 < WithZero.log (Valued.v x) := by
    by_contra h
    push Not at h
    apply hx
    rw [← WithZero.exp_log hx0, ← WithZero.exp_zero, WithZero.exp_le_exp]
    exact h
  refine ⟨(WithZero.log (Valued.v x)).toNat, by omega, ?_⟩
  rw [Int.toNat_of_nonneg hlog.le, WithZero.exp_log hx0]

private theorem exists_valued_eq_exp_of_not_le' {x : v.adicCompletion ℚ} (hx : ¬ Valued.v x ≤ 1) :
    ∃ e : ℤ, 1 ≤ e ∧ Valued.v x = WithZero.exp e := by
  obtain ⟨d, hd, hxd⟩ := exists_valued_eq_exp_of_not_le hx
  exact ⟨d, by omega, hxd⟩

end BoundPrivates
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_laurent_localZeta_eq_gl3LFactorPoly_of_sphericalData.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_exists_laurent_localZeta_eq_gl3LFactorPoly_of_sphericalData.LanglandsTunnell.CubicInduction"

section Growth

variable {v : HeightOneSpectrum (𝓞 ℚ)} (W : LocalGL3 v → ℂ) (e₁ e₂ e₃ : ℂ)
  (hW : IsRightInvariant (localMaximalCompact3 (𝓞 ℚ) ℚ v) W ∧
    IsCosetEigenfunction (localMaximalCompact3 (𝓞 ℚ) ℚ v) (heckeGen1 v) W (cNormQ v * e₁) ∧
    IsCosetEigenfunction (localMaximalCompact3 (𝓞 ℚ) ℚ v) (heckeGen2 v) W (cNormQ v * e₂) ∧
    ∀ g : LocalGL3 v, W (centralGen v * g) = e₃ * W g)
  (hψ : IsGL3PsiWhittakerFn (psiLocal ℚ v) W) (χ : (v.adicCompletion ℚ)ˣ →* ℂˣ) (Cχ : ℝ)
  (hχ : ∀ u : (v.adicCompletion ℚ)ˣ, Valued.v (u : v.adicCompletion ℚ) = 1 → ‖((χ u : ℂˣ) : ℂ)‖ ≤ Cχ)

include hW hψ hχ

private theorem aestronglyMeasurable_localZeta30_integrand_torusUnipotentPoint (a : ℕ) (hχa : HasConductorExponentAt ℚ v χ a)
    (k : ℤ) (y : v.adicCompletion ℚ) :
    letI := localBorel ℚ v
    AEStronglyMeasurable
      (fun α : (v.adicCompletion ℚ)ˣ => W (iotaGL (diagUnitGL2 α) * torusUnipotentPoint v k y) * ((χ α : ℂˣ) : ℂ))
      (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ v))) := by
  letI := localBorel ℚ v
  have _ := hψ
  have _ := hχ
  refine Measurable.aestronglyMeasurable (Measurable.mul ?_ (measurable_coe_units_apply v hχa.1))
  obtain ⟨m, hm⟩ := exists_forall_mem_higherUnitsAt_conj_iotaGL_diagUnitGL2_mem v (torusUnipotentPoint v k y)
  refine measurable_of_forall_exists_forall_mem_higherUnitsAt_apply_mul_eq v _ fun α => ⟨m, fun u hu => ?_⟩
  have h : iotaGL (diagUnitGL2 α) * iotaGL (diagUnitGL2 u) * torusUnipotentPoint v k y =
      iotaGL (diagUnitGL2 α) * torusUnipotentPoint v k y *
        ((torusUnipotentPoint v k y)⁻¹ * iotaGL (diagUnitGL2 u) * torusUnipotentPoint v k y) := by
    group
  rw [iotaGL_diagUnitGL2_mul, h, hW.1 _ _ (hm u hu)]

private theorem aestronglyMeasurable_dual_integrand_torusUnipotentPoint (a : ℕ) (hχa : HasConductorExponentAt ℚ v χ a) (k : ℤ)
    (y : v.adicCompletion ℚ) :
    letI := localBorel ℚ v
    AEStronglyMeasurable
      (fun p : (v.adicCompletion ℚ)ˣ × v.adicCompletion ℚ =>
        dualWhittakerFn3 W (iotaGL (diagUnitGL2 p.1) * lowerUnipotent21 p.2 *
            (weylPrime3 * transposeInv3 (torusUnipotentPoint v k y))) *
          ((χ⁻¹ p.1 : ℂˣ) : ℂ))
      ((Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ v))).prod (selfDualHaarAt ℚ v)) := by
  letI := localBorel ℚ v
  have _ := hψ
  have _ := hχ
  have hχinv : ∀ u ∈ higherUnitsAt ℚ v a, χ⁻¹ u = 1 := fun u hu => by
    rw [MonoidHom.inv_apply, hχa.1 u hu, inv_one]
  refine Measurable.aestronglyMeasurable
    (Measurable.mul ?_ ((measurable_coe_units_apply v hχinv).comp measurable_fst))
  have hW' := isRightInvariant_dualWhittakerFn3_of hW.1
  obtain ⟨R, hR⟩ :=
    exists_forall_valued_le_conj_lowerUnipotent21_mem v (weylPrime3 * transposeInv3 (torusUnipotentPoint v k y))
  refine measurable_of_forall_exists_forall_apply_mul_add_eq v _ fun β x => ?_
  obtain ⟨m, hm⟩ := exists_forall_mem_higherUnitsAt_conj_iotaGL_diagUnitGL2_mem v
    (lowerUnipotent21 x * (weylPrime3 * transposeInv3 (torusUnipotentPoint v k y)))
  refine ⟨m, R, fun u hu z hz => ?_⟩
  dsimp only
  rw [iotaGL_diagUnitGL2_mul, lowerUnipotent21_add]
  have h : iotaGL (diagUnitGL2 β) * iotaGL (diagUnitGL2 u) * (lowerUnipotent21 x * lowerUnipotent21 z) *
        (weylPrime3 * transposeInv3 (torusUnipotentPoint v k y)) =
      iotaGL (diagUnitGL2 β) * (lowerUnipotent21 x * (weylPrime3 * transposeInv3 (torusUnipotentPoint v k y))) *
          ((lowerUnipotent21 x * (weylPrime3 * transposeInv3 (torusUnipotentPoint v k y)))⁻¹ *
            iotaGL (diagUnitGL2 u) *
            (lowerUnipotent21 x * (weylPrime3 * transposeInv3 (torusUnipotentPoint v k y)))) *
        ((weylPrime3 * transposeInv3 (torusUnipotentPoint v k y))⁻¹ * lowerUnipotent21 z *
          (weylPrime3 * transposeInv3 (torusUnipotentPoint v k y))) := by
    group
  rw [h, hW' _ _ (hR z hz), hW' _ _ (hm u hu), mul_assoc]

private theorem exists_forall_norm_localZeta30_integrand_torusUnipotentPoint_le (k : ℤ) (y : v.adicCompletion ℚ) :
    ∃ C ρ : ℝ, 0 < ρ ∧
      (∀ (n : ℤ) (α : (v.adicCompletion ℚ)ˣ), Valued.v (α : v.adicCompletion ℚ) = WithZero.exp (-n) → n < 0 →
        W (iotaGL (diagUnitGL2 α) * torusUnipotentPoint v k y) = 0) ∧
      ∀ (n : ℤ) (α : (v.adicCompletion ℚ)ˣ), Valued.v (α : v.adicCompletion ℚ) = WithZero.exp (-n) → 0 ≤ n →
        ‖W (iotaGL (diagUnitGL2 α) * torusUnipotentPoint v k y) * ((χ α : ℂˣ) : ℂ)‖ ≤ C * ρ ^ n := by
  by_cases he₃ : e₃ = 0
  · refine ⟨0, 1, one_pos, fun n α _ _ => apply_eq_zero_of_eq_zero W e₁ e₂ e₃ hW he₃ _, fun n α _ _ => ?_⟩
    rw [apply_eq_zero_of_eq_zero W e₁ e₂ e₃ hW he₃, zero_mul, norm_zero, zero_mul]
  have ht : 0 < ‖((χ (ratPrimeUnit v) : ℂˣ) : ℂ)‖ := norm_pos_iff.2 (Units.ne_zero _)
  obtain ⟨C, ρ, hρ, hC⟩ := exists_forall_mul_pow_mul_zpow_le (2 * ‖W 1‖ * Cχ)
    (sphericalBase (1 + ‖e₁‖ + ‖e₂‖ + ‖e₃‖) e₃ (cNormQ v)) ‖((χ (ratPrimeUnit v) : ℂˣ) : ℂ)‖
    (one_le_sphericalBase _ _ _) ht (k.toNat + 1) 1 0
  refine ⟨C, ρ, hρ, fun n α hα hn => ?_, fun n α hα hn => ?_⟩
  · rw [apply_iotaGL_diagUnitGL2_mul_torusUnipotentPoint W e₁ e₂ e₃ hW hψ he₃ k y n α hα,
      sphericalValue_of_not, mul_zero]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons]
    omega
  · rw [apply_iotaGL_diagUnitGL2_mul_torusUnipotentPoint W e₁ e₂ e₃ hW hψ he₃ k y n α hα, norm_mul, norm_mul,
      norm_psiLocal_rat_apply, one_mul]
    have hV := norm_sphericalValue_le (v := v) (W 1) e₁ e₂ e₃ ![n, k, 0] (k.toNat + 1 + 1 * (n - 0).toNat) (by
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons]
      omega)
    have hM0 : 0 ≤ sphericalBase (1 + ‖e₁‖ + ‖e₂‖ + ‖e₃‖) e₃ (cNormQ v) :=
      zero_le_one.trans (one_le_sphericalBase _ _ _)
    set M : ℝ := sphericalBase (1 + ‖e₁‖ + ‖e₂‖ + ‖e₃‖) e₃ (cNormQ v) with hMdef
    set N : ℕ := k.toNat + 1 + 1 * (n - 0).toNat with hNdef
    calc ‖sphericalValue (W 1) e₁ e₂ e₃ (cNormQ v) ![n, k, 0]‖ * ‖((χ α : ℂˣ) : ℂ)‖
        ≤ (2 * ‖W 1‖ * M ^ (3 * N)) * (Cχ * ‖((χ (ratPrimeUnit v) : ℂˣ) : ℂ)‖ ^ n) :=
          mul_le_mul hV (norm_coe_apply_le χ Cχ hχ n α hα) (norm_nonneg _)
            (mul_nonneg (mul_nonneg zero_le_two (norm_nonneg _)) (pow_nonneg hM0 _))
      _ = 2 * ‖W 1‖ * Cχ * M ^ (3 * N) * ‖((χ (ratPrimeUnit v) : ℂˣ) : ℂ)‖ ^ n := by ring
      _ ≤ C * ρ ^ n := hC n hn

private theorem exists_forall_norm_dual_integrand_torusUnipotentPoint_le (he₃ : e₃ ≠ 0) (k : ℤ) (y : v.adicCompletion ℚ) :
    ∃ (n₀ R : ℤ) (C ρ : ℝ), 0 < ρ ∧
      (∀ (n : ℤ) (β : (v.adicCompletion ℚ)ˣ) (x : v.adicCompletion ℚ),
        Valued.v (β : v.adicCompletion ℚ) = WithZero.exp (-n) →
        dualWhittakerFn3 W (iotaGL (diagUnitGL2 β) * lowerUnipotent21 x *
            (weylPrime3 * transposeInv3 (torusUnipotentPoint v k y))) ≠ 0 →
          n₀ ≤ n ∧ Valued.v x ≤ WithZero.exp R) ∧
      ∀ (n : ℤ) (β : (v.adicCompletion ℚ)ˣ) (x : v.adicCompletion ℚ),
        Valued.v (β : v.adicCompletion ℚ) = WithZero.exp (-n) → n₀ ≤ n →
        ‖dualWhittakerFn3 W (iotaGL (diagUnitGL2 β) * lowerUnipotent21 x *
              (weylPrime3 * transposeInv3 (torusUnipotentPoint v k y))) *
            ((χ⁻¹ β : ℂˣ) : ℂ)‖ ≤ C * ρ ^ n := by
  have hχ' := forall_norm_inv_apply_le χ Cχ hχ
  have ht : 0 < ‖((χ⁻¹ (ratPrimeUnit v) : ℂˣ) : ℂ)‖ := norm_pos_iff.2 (Units.ne_zero _)
  have hc : ∀ (n : ℤ) (β : (v.adicCompletion ℚ)ˣ), Valued.v (β : v.adicCompletion ℚ) = WithZero.exp (-n) →
      ‖((χ⁻¹ β : ℂˣ) : ℂ)‖ ≤ Cχ * ‖((χ⁻¹ (ratPrimeUnit v) : ℂˣ) : ℂ)‖ ^ n :=
    fun n β hβ => norm_coe_apply_le χ⁻¹ Cχ hχ' n β hβ
  have hM := one_le_sphericalBase (1 + ‖e₁‖ + ‖e₂‖ + ‖e₃‖) e₃ (cNormQ v)

  by_cases hy : Valued.v y ≤ 1
  · refine ⟨-(2 * (k.toNat : ℤ)), k.toNat, exists_forall_of_oracle
      (fun n (β : (v.adicCompletion ℚ)ˣ) => Valued.v (β : v.adicCompletion ℚ) = WithZero.exp (-n))
      (fun β x => dualWhittakerFn3 W (iotaGL (diagUnitGL2 β) * lowerUnipotent21 x *
        (weylPrime3 * transposeInv3 (torusUnipotentPoint v k y))))
      (fun β => ((χ⁻¹ β : ℂˣ) : ℂ)) (fun x => Valued.v x ≤ WithZero.exp (k.toNat : ℤ)) Cχ _ _ ‖W 1‖ ht hM
      (norm_nonneg _) hc _ (k.toNat + 1) 2 fun n β x hβ => ?_⟩
    beta_reduce at hβ ⊢
    by_cases hx : Valued.v x ≤ 1
    ·
      refine ⟨(![k, 0, -n] : Fin 3 → ℤ) 1 ≤ ![k, 0, -n] 0 ∧ (![k, 0, -n] : Fin 3 → ℤ) 2 ≤ ![k, 0, -n] 1,
        sphericalValue (W 1) e₁ e₂ e₃ (cNormQ v) ![k, 0, -n], fun hne => ?_, ?_, fun hdom => ?_, fun hn => ?_⟩
      · by_contra hdom
        have hval := dualWhittakerFn3_apply_of_valued_le_of_valued_le W e₁ e₂ e₃ hW hψ he₃ k y hy n β hβ x hx
        rw [sphericalValue_of_not _ _ _ _ _ _ hdom] at hval
        exact hne hval
      · rw [dualWhittakerFn3_apply_of_valued_le_of_valued_le W e₁ e₂ e₃ hW hψ he₃ k y hy n β hβ x hx]
      · simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
          Matrix.tail_cons] at hdom
        refine ⟨by omega, hx.trans ?_⟩
        rw [← WithZero.exp_zero, WithZero.exp_le_exp]
        omega
      · refine norm_sphericalValue_le (v := v) (W 1) e₁ e₂ e₃ _ _ fun hdom => ?_
        simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
          Matrix.tail_cons] at hdom ⊢
        omega
    ·
      obtain ⟨e, he, hxe⟩ := exists_valued_eq_exp_of_not_le' hx
      refine ⟨(![k, e, -(e + n)] : Fin 3 → ℤ) 1 ≤ ![k, e, -(e + n)] 0 ∧
          (![k, e, -(e + n)] : Fin 3 → ℤ) 2 ≤ ![k, e, -(e + n)] 1,
        sphericalValue (W 1) e₁ e₂ e₃ (cNormQ v) ![k, e, -(e + n)], fun hne => ?_, ?_, fun hdom => ?_,
        fun hn => ?_⟩
      · by_contra hdom
        have hval := dualWhittakerFn3_apply_of_valued_le_of_valued_eq W e₁ e₂ e₃ hW hψ he₃ k y hy n β hβ e he x hxe
        rw [sphericalValue_of_not _ _ _ _ _ _ hdom, mul_zero] at hval
        exact hne hval
      · rw [dualWhittakerFn3_apply_of_valued_le_of_valued_eq W e₁ e₂ e₃ hW hψ he₃ k y hy n β hβ e he x hxe, norm_mul,
          norm_psiLocal_rat_apply, one_mul]
      · simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
          Matrix.tail_cons] at hdom
        refine ⟨by omega, ?_⟩
        rw [hxe, WithZero.exp_le_exp]
        omega
      · refine norm_sphericalValue_le (v := v) (W 1) e₁ e₂ e₃ _ _ fun hdom => ?_
        simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
          Matrix.tail_cons] at hdom ⊢
        omega
  · obtain ⟨d, hd, hyd⟩ := exists_valued_eq_exp_of_not_le hy
    refine ⟨-(2 * (k.toNat : ℤ) + 3 * d), ((k + 2 * d).toNat : ℤ) + d, exists_forall_of_oracle
      (fun n (β : (v.adicCompletion ℚ)ˣ) => Valued.v (β : v.adicCompletion ℚ) = WithZero.exp (-n))
      (fun β x => dualWhittakerFn3 W (iotaGL (diagUnitGL2 β) * lowerUnipotent21 x *
        (weylPrime3 * transposeInv3 (torusUnipotentPoint v k y))))
      (fun β => ((χ⁻¹ β : ℂˣ) : ℂ)) (fun x => Valued.v x ≤ WithZero.exp (((k + 2 * d).toNat : ℤ) + d)) Cχ _ _ ‖W 1‖
      ht hM (norm_nonneg _) hc _ (k.toNat + 2 * d + 1) 2 fun n β x hβ => ?_⟩
    beta_reduce at hβ ⊢
    by_cases hx : Valued.v x < WithZero.exp (d : ℤ)
    ·
      refine ⟨(![k + d, 0, -(d + n)] : Fin 3 → ℤ) 1 ≤ ![k + d, 0, -(d + n)] 0 ∧
          (![k + d, 0, -(d + n)] : Fin 3 → ℤ) 2 ≤ ![k + d, 0, -(d + n)] 1,
        sphericalValue (W 1) e₁ e₂ e₃ (cNormQ v) ![k + d, 0, -(d + n)], fun hne => ?_, ?_, fun hdom => ?_,
        fun hn => ?_⟩
      · by_contra hdom
        have hval := dualWhittakerFn3_apply_of_valued_eq_of_valued_lt W e₁ e₂ e₃ hW hψ he₃ k d hd y hyd n β hβ x hx
        rw [sphericalValue_of_not _ _ _ _ _ _ hdom, mul_zero] at hval
        exact hne hval
      · rw [dualWhittakerFn3_apply_of_valued_eq_of_valued_lt W e₁ e₂ e₃ hW hψ he₃ k d hd y hyd n β hβ x hx, norm_mul,
          norm_psiLocal_rat_apply, one_mul]
      · simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
          Matrix.tail_cons] at hdom
        refine ⟨by omega, hx.le.trans ?_⟩
        rw [WithZero.exp_le_exp]
        omega
      · refine norm_sphericalValue_le (v := v) (W 1) e₁ e₂ e₃ _ _ fun hdom => ?_
        simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
          Matrix.tail_cons] at hdom ⊢
        omega
    ·
      have hx0 : Valued.v x ≠ 0 := fun h => hx (by rw [h]; exact WithZero.exp_pos)
      obtain ⟨e, hde, hxe⟩ : ∃ e : ℤ, (d : ℤ) ≤ e ∧ Valued.v x = WithZero.exp e := by
        refine ⟨WithZero.log (Valued.v x), ?_, (WithZero.exp_log hx0).symm⟩
        rw [not_lt, ← WithZero.exp_log hx0, WithZero.exp_le_exp] at hx
        exact hx
      refine ⟨(![k + d, e - d, -(e + n)] : Fin 3 → ℤ) 1 ≤ ![k + d, e - d, -(e + n)] 0 ∧
          (![k + d, e - d, -(e + n)] : Fin 3 → ℤ) 2 ≤ ![k + d, e - d, -(e + n)] 1,
        sphericalValue (W 1) e₁ e₂ e₃ (cNormQ v) ![k + d, e - d, -(e + n)], fun hne => ?_, ?_, fun hdom => ?_,
        fun hn => ?_⟩
      · by_contra hdom
        have hval :=
          dualWhittakerFn3_apply_of_valued_eq_of_le_valued W e₁ e₂ e₃ hW hψ he₃ k d hd y hyd n β hβ e hde x hxe
        rw [sphericalValue_of_not _ _ _ _ _ _ hdom, mul_zero] at hval
        exact hne hval
      · rw [dualWhittakerFn3_apply_of_valued_eq_of_le_valued W e₁ e₂ e₃ hW hψ he₃ k d hd y hyd n β hβ e hde x hxe,
          norm_mul, norm_psiLocal_rat_apply, one_mul]
      · simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
          Matrix.tail_cons] at hdom
        refine ⟨by omega, ?_⟩
        rw [hxe, WithZero.exp_le_exp]
        omega
      · refine norm_sphericalValue_le (v := v) (W 1) e₁ e₂ e₃ _ _ fun hdom => ?_
        simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
          Matrix.tail_cons] at hdom ⊢
        omega

end Growth
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_laurent_localZeta_eq_gl3LFactorPoly_of_sphericalData.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_exists_laurent_localZeta_eq_gl3LFactorPoly_of_sphericalData.LanglandsTunnell.CubicInduction"

end
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_laurent_localZeta_eq_gl3LFactorPoly_of_sphericalData.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_exists_laurent_localZeta_eq_gl3LFactorPoly_of_sphericalData.LanglandsTunnell.CubicInduction"
end
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_laurent_localZeta_eq_gl3LFactorPoly_of_sphericalData.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_exists_laurent_localZeta_eq_gl3LFactorPoly_of_sphericalData.LanglandsTunnell.CubicInduction"

section

set_option autoImplicit false

open IsDedekindDomain NumberField NumberField.TateGlobal AutomorphicForm LanglandsTunnell.Converse LanglandsTunnell.RankinSelberg LanglandsTunnell.TateLocal MeasureTheory

p2m_open "IsDedekindDomain.HeightOneSpectrum~Extension LanglandsTunnell.CubicInduction P2MW.S_LanglandsTunnell_CubicInduction_exists_laurent_localZeta_eq_gl3LFactorPoly_of_sphericalData.LanglandsTunnell.CubicInduction NumberField.StandardAddChar"
open scoped NNReal

noncomputable section

section ShellIndexPrivates

variable (v : HeightOneSpectrum (𝓞 ℚ))

private theorem valued_coe_eq_exp_neg_unitShellIndex (α : (v.adicCompletion ℚ)ˣ) :
    Valued.v (α : v.adicCompletion ℚ) = WithZero.exp (-unitShellIndex v α) :=
  mem_unitShell_unitShellIndex v α

private theorem coe_modulus_coe_eq_zpow (α : (v.adicCompletion ℚ)ˣ) :
    ((modulus (α : v.adicCompletion ℚ) : ℝ≥0) : ℝ) = (Ideal.absNorm v.asIdeal : ℝ) ^ (-unitShellIndex v α) := by
  rw [modulus_coe_eq_zpow_neg_unitShellIndex v α, NNReal.coe_zpow, NNReal.coe_natCast]

private theorem setOf_unitShellIndex_eq (n : ℤ) :
    {α : (v.adicCompletion ℚ)ˣ | unitShellIndex v α = n} = unitShell v n := by
  ext α
  constructor
  · rintro (rfl : unitShellIndex v α = n)
    exact mem_unitShell_unitShellIndex v α
  · intro hα
    have hα' : Valued.v (α : v.adicCompletion ℚ) = WithZero.exp (-n) := hα
    show -WithZero.log (Valued.v (α : v.adicCompletion ℚ)) = n
    rw [hα', WithZero.log_exp, neg_neg]

private theorem measure_setOf_unitShellIndex_le (n : ℤ) :
    letI := localBorel ℚ v
    Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ v)) {α : (v.adicCompletion ℚ)ˣ | unitShellIndex v α = n} ≤
      selfDualHaarAt ℚ v (unitSet v) := by
  letI := localBorel ℚ v
  rw [setOf_unitShellIndex_eq v n]
  exact (measure_unitShell v n).le

private theorem one_lt_absNorm_asIdeal_real : (1 : ℝ) < (Ideal.absNorm v.asIdeal : ℝ) := by
  have h0 : Ideal.absNorm v.asIdeal ≠ 0 := Ideal.absNorm_eq_zero_iff.not.mpr v.ne_bot
  have h1 : Ideal.absNorm v.asIdeal ≠ 1 := by
    rw [Ne, Ideal.absNorm_eq_one_iff]
    exact v.isPrime.ne_top
  exact_mod_cast (show 1 < Ideal.absNorm v.asIdeal by omega)

private theorem exists_forall_norm_coe_apply_le {χ : (v.adicCompletion ℚ)ˣ →* ℂˣ} {a : ℕ}
    (hχa : HasConductorExponentAt ℚ v χ a) :
    ∃ Cχ : ℝ, ∀ u : (v.adicCompletion ℚ)ˣ, Valued.v (u : v.adicCompletion ℚ) = 1 → ‖((χ u : ℂˣ) : ℂ)‖ ≤ Cχ := by
  obtain ⟨Cχ, hCχ⟩ := exists_forall_norm_charExt_le v hχa.1
  exact ⟨Cχ, fun u hu => by simpa using hCχ (u : v.adicCompletion ℚ) hu⟩

end ShellIndexPrivates
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_laurent_localZeta_eq_gl3LFactorPoly_of_sphericalData.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_exists_laurent_localZeta_eq_gl3LFactorPoly_of_sphericalData.LanglandsTunnell.CubicInduction"

section Convergence

variable {v : HeightOneSpectrum (𝓞 ℚ)} (W : LocalGL3 v → ℂ) (e₁ e₂ e₃ : ℂ)
  (hW : IsRightInvariant (localMaximalCompact3 (𝓞 ℚ) ℚ v) W ∧
    IsCosetEigenfunction (localMaximalCompact3 (𝓞 ℚ) ℚ v) (heckeGen1 v) W (cNormQ v * e₁) ∧
    IsCosetEigenfunction (localMaximalCompact3 (𝓞 ℚ) ℚ v) (heckeGen2 v) W (cNormQ v * e₂) ∧
    ∀ g : LocalGL3 v, W (centralGen v * g) = e₃ * W g)
  (hψ : IsGL3PsiWhittakerFn (psiLocal ℚ v) W) (χ : (v.adicCompletion ℚ)ˣ →* ℂˣ) (a : ℕ)
  (hχa : HasConductorExponentAt ℚ v χ a)

include hW hψ hχa

private theorem exists_isLocalZeta30ConvergentAbove_torusUnipotentPoint (k : ℤ) (y : v.adicCompletion ℚ) :
    letI := localBorel ℚ v
    ∃ σ₀ : ℝ,
      IsLocalZeta30ConvergentAbove v (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ v)))
        W χ (torusUnipotentPoint v k y) σ₀ := by
  letI := localBorel ℚ v
  obtain ⟨Cχ, hχ⟩ := exists_forall_norm_coe_apply_le v hχa
  obtain ⟨C, ρ, hρ, hvan, hbd⟩ :=
    exists_forall_norm_localZeta30_integrand_torusUnipotentPoint_le W e₁ e₂ e₃ hW hψ χ Cχ hχ k y
  exact ⟨_, isLocalZeta30ConvergentAbove_of_forall_norm_le v _ (unitShellIndex v) (measurable_unitShellIndex v)
    (Ideal.absNorm v.asIdeal : ℝ) (one_lt_absNorm_asIdeal_real v) (coe_modulus_coe_eq_zpow v)
    (selfDualHaarAt ℚ v (unitSet v)) (measure_unitSet_ne_top v) (measure_setOf_unitShellIndex_le v) W χ _
    (aestronglyMeasurable_localZeta30_integrand_torusUnipotentPoint W e₁ e₂ e₃ hW hψ χ Cχ hχ a hχa k y) 0
    (fun α hα => hvan _ α (valued_coe_eq_exp_neg_unitShellIndex v α) hα) C ρ hρ
    (fun α hα => hbd _ α (valued_coe_eq_exp_neg_unitShellIndex v α) hα)⟩

private theorem exists_isLocalZeta31ConvergentAbove_dual_torusUnipotentPoint (he₃ : e₃ ≠ 0) (k : ℤ)
    (y : v.adicCompletion ℚ) :
    letI := localBorel ℚ v
    ∃ σ₁ : ℝ,
      IsLocalZeta31ConvergentAbove v (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ v)))
        (selfDualHaarAt ℚ v) (dualWhittakerFn3 W) χ⁻¹ (weylPrime3 * transposeInv3 (torusUnipotentPoint v k y)) σ₁ := by
  letI := localBorel ℚ v
  haveI : SigmaFinite (selfDualHaarAt ℚ v) := sigmaFinite_selfDualHaarAt_rat v
  obtain ⟨Cχ, hχ⟩ := exists_forall_norm_coe_apply_le v hχa
  obtain ⟨n₀, R, C, ρ, hρ, hsupp, hbd⟩ :=
    exists_forall_norm_dual_integrand_torusUnipotentPoint_le W e₁ e₂ e₃ hW hψ χ Cχ hχ he₃ k y
  refine ⟨_, isLocalZeta31ConvergentAbove_of_forall_norm_le v _ (selfDualHaarAt ℚ v) (unitShellIndex v)
    (measurable_unitShellIndex v) (Ideal.absNorm v.asIdeal : ℝ) (one_lt_absNorm_asIdeal_real v)
    (coe_modulus_coe_eq_zpow v) (selfDualHaarAt ℚ v (unitSet v)) (measure_unitSet_ne_top v)
    (measure_setOf_unitShellIndex_le v) (fun _ => adicBall v R) (fun _ => adicBall_measurableSet v R)
    ((selfDualHaarAt ℚ v).real (adicBall v R)) 1 measureReal_nonneg one_pos (fun n => ?_) (dualWhittakerFn3 W) χ⁻¹ _
    (aestronglyMeasurable_dual_integrand_torusUnipotentPoint W e₁ e₂ e₃ hW hψ χ Cχ hχ a hχa k y) n₀
    (fun β x hne => hsupp _ β x (valued_coe_eq_exp_neg_unitShellIndex v β) hne) C ρ hρ
    (fun β x hn => hbd _ β x (valued_coe_eq_exp_neg_unitShellIndex v β) hn)⟩
  rw [one_zpow, mul_one, measureReal_def, ENNReal.ofReal_toReal (adicBall_measure_ne_top v R)]

end Convergence
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_laurent_localZeta_eq_gl3LFactorPoly_of_sphericalData.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_exists_laurent_localZeta_eq_gl3LFactorPoly_of_sphericalData.LanglandsTunnell.CubicInduction"

end
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_laurent_localZeta_eq_gl3LFactorPoly_of_sphericalData.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_exists_laurent_localZeta_eq_gl3LFactorPoly_of_sphericalData.LanglandsTunnell.CubicInduction"
end
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_laurent_localZeta_eq_gl3LFactorPoly_of_sphericalData.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_exists_laurent_localZeta_eq_gl3LFactorPoly_of_sphericalData.LanglandsTunnell.CubicInduction"

section

set_option autoImplicit false

open IsDedekindDomain NumberField NumberField.TateGlobal AutomorphicForm LanglandsTunnell.Converse LanglandsTunnell.RankinSelberg LanglandsTunnell.TateLocal MeasureTheory

p2m_open "IsDedekindDomain.HeightOneSpectrum~Extension LanglandsTunnell.CubicInduction P2MW.S_LanglandsTunnell_CubicInduction_exists_laurent_localZeta_eq_gl3LFactorPoly_of_sphericalData.LanglandsTunnell.CubicInduction NumberField.StandardAddChar"

section LaurentClass

variable (q : ℂ)

private theorem exists_polynomial_eval_rpow_mul_of_monomial (c : ℂ) (n : ℕ) :
    ∃ (Q : Polynomial ℂ) (m : ℕ), ∀ s : ℂ, c * (q ^ (-s)) ^ n = Q.eval (q ^ (-s)) * q ^ ((m : ℂ) * s) :=
  ⟨Polynomial.C c * Polynomial.X ^ n, 0, fun s => by simp⟩

private theorem exists_polynomial_eval_rpow_mul_of_mul_zpow (hq : q ≠ 0) (P : ℂ → ℂ)
    (hP : ∃ (Q : Polynomial ℂ) (m : ℕ), ∀ s : ℂ, P s = Q.eval (q ^ (-s)) * q ^ ((m : ℂ) * s)) (c : ℂ) (n : ℤ) :
    ∃ (Q : Polynomial ℂ) (m : ℕ), ∀ s : ℂ, c * q ^ ((n : ℂ) * s) * P s = Q.eval (q ^ (-s)) * q ^ ((m : ℂ) * s) := by
  obtain ⟨Q, m, hQ⟩ := hP

  obtain ⟨t, u, htu⟩ : ∃ t u : ℕ, (n : ℂ) = -(t : ℂ) + (u : ℂ) :=
    ⟨(-n).toNat, n.toNat, by
      have h : (n : ℤ) = -(((-n).toNat : ℕ) : ℤ) + ((n.toNat : ℕ) : ℤ) := by omega
      exact_mod_cast h⟩
  refine ⟨Polynomial.C c * Polynomial.X ^ t * Q, m + u, fun s => ?_⟩
  have h1 : q ^ ((n : ℂ) * s) = (q ^ (-s)) ^ t * q ^ ((u : ℂ) * s) := by
    rw [htu, show (-(t : ℂ) + (u : ℂ)) * s = (t : ℂ) * (-s) + (u : ℂ) * s by ring, Complex.cpow_add _ _ hq,
      Complex.cpow_nat_mul]
  have h2 : q ^ (((m + u : ℕ) : ℂ) * s) = q ^ ((m : ℂ) * s) * q ^ ((u : ℂ) * s) := by
    rw [← Complex.cpow_add _ _ hq]
    push_cast
    ring_nf
  rw [hQ s, h1, h2]
  simp only [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  ring

end LaurentClass
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_laurent_localZeta_eq_gl3LFactorPoly_of_sphericalData.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_exists_laurent_localZeta_eq_gl3LFactorPoly_of_sphericalData.LanglandsTunnell.CubicInduction"

section Ramified

variable {v : HeightOneSpectrum (𝓞 ℚ)}

private theorem absNorm_complex_ne_zero (v : HeightOneSpectrum (𝓞 ℚ)) : (Ideal.absNorm v.asIdeal : ℂ) ≠ 0 := by
  have h : Ideal.absNorm v.asIdeal ≠ 0 :=
    Ideal.absNorm_ne_zero_of_nonZeroDivisors ⟨v.asIdeal, mem_nonZeroDivisors_of_ne_zero v.ne_bot⟩
  exact_mod_cast h

private theorem selfDualHaarAt_real_integers_eq_one (v : HeightOneSpectrum (𝓞 ℚ)) :
    letI := localBorel ℚ v
    (selfDualHaarAt ℚ v).real (v.adicCompletionIntegers ℚ : Set (v.adicCompletion ℚ)) = 1 := by
  letI := localBorel ℚ v
  have h := selfDualHaarAt_real_integers_mul_real_setOf_valued_le_exp_addCharLevel ℚ v
  have hlev : addCharLevel (psiLocal ℚ v) = 0 := (psiLocal_rat_facts v).2.2.1
  have hset : {x : v.adicCompletion ℚ | Valued.v x ≤ WithZero.exp (addCharLevel (psiLocal ℚ v))} =
      (v.adicCompletionIntegers ℚ : Set (v.adicCompletion ℚ)) := by
    ext x
    simp [hlev, mem_adicCompletionIntegers]
  rw [hset] at h
  have h0 : 0 ≤ (selfDualHaarAt ℚ v).real (v.adicCompletionIntegers ℚ : Set (v.adicCompletion ℚ)) :=
    measureReal_nonneg
  nlinarith [h, h0]

private noncomputable def primeUnit (v : HeightOneSpectrum (𝓞 ℚ)) : (v.adicCompletion ℚ)ˣ :=
  (AdelicLevel.uniformizerUnit ℚ v)⁻¹ * ratPrimeUnit v

private theorem valued_primeUnit (v : HeightOneSpectrum (𝓞 ℚ)) :
    Valued.v ((primeUnit v : (v.adicCompletion ℚ)ˣ) : v.adicCompletion ℚ) = 1 := by
  have hne : Valued.v (varpi v) ≠ 0 := (Valuation.ne_zero_iff _).2 (varpi_ne_zero v)
  unfold primeUnit
  rw [Units.val_mul, Units.val_inv_eq_inv_val, map_mul, map_inv₀]
  change (Valued.v (varpi v))⁻¹ * Valued.v (ratPrimeAt v) = 1
  rw [valued_ratPrimeAt_eq_valued_varpi]
  exact inv_mul_cancel₀ hne

private theorem ratPrimeUnit_eq_uniformizerUnit_mul (v : HeightOneSpectrum (𝓞 ℚ)) :
    ratPrimeUnit v = AdelicLevel.uniformizerUnit ℚ v * primeUnit v := by
  unfold primeUnit
  rw [mul_inv_cancel_left]

private theorem ratPrimeAt_pow_inv_eq (v : HeightOneSpectrum (𝓞 ℚ)) (a : ℕ) :
    (ratPrimeAt v ^ a)⁻¹ =
      ((AdelicLevel.uniformizerUnit ℚ v ^ (-(a : ℤ)) : (v.adicCompletion ℚ)ˣ) : v.adicCompletion ℚ) *
        (((primeUnit v ^ a)⁻¹ : (v.adicCompletion ℚ)ˣ) : v.adicCompletion ℚ) := by
  have hp : ratPrimeAt v = ((ratPrimeUnit v : (v.adicCompletion ℚ)ˣ) : v.adicCompletion ℚ) := rfl
  rw [hp, ratPrimeUnit_eq_uniformizerUnit_mul, Units.val_zpow_eq_zpow_val, zpow_neg, zpow_natCast, Units.val_mul,
    mul_pow, mul_inv, Units.val_inv_eq_inv_val, Units.val_pow_eq_pow_val]

private theorem stdRootNumberAt_eq_ratPrime_form (χ : (v.adicCompletion ℚ)ˣ →* ℂˣ) {a : ℕ} (ha : 1 ≤ a)
    (hχa : HasConductorExponentAt ℚ v χ a) (hu : ‖((χ (AdelicLevel.uniformizerUnit ℚ v) : ℂˣ) : ℂ)‖ = 1) :
    stdRootNumberAt ℚ v χ =
      ((((Ideal.absNorm v.asIdeal : ℝ) ^ (a : ℤ) : ℝ) : ℂ)) ^ (1 / 2 : ℂ) * ((χ (ratPrimeUnit v) : ℂˣ) : ℂ) ^ a *
        gaussIntegral v (psiLocal ℚ v) χ⁻¹ ((ratPrimeAt v ^ a)⁻¹) := by
  rw [stdRootNumberAt_eq_gaussIntegral v χ ha hχa hu (psiLocal_rat_facts v).2.2.1, ratPrimeAt_pow_inv_eq,
    gaussIntegral_mul_coe_units v _ _ _ (by rw [Units.val_inv_eq_inv_val, map_inv₀, Units.val_pow_eq_pow_val, map_pow,
      valued_primeUnit, one_pow, inv_one]),
    ratPrimeUnit_eq_uniformizerUnit_mul, map_mul]
  simp only [MonoidHom.inv_apply, map_inv, map_pow, Units.val_mul, Units.val_pow_eq_pow_val, Units.val_inv_eq_inv_val,
    inv_inv]
  have hc : ((χ (primeUnit v) : ℂˣ) : ℂ) ≠ 0 := Units.ne_zero _
  field_simp
  rw [mul_assoc _ (_ ^ a) ((1 / _) ^ a), ← mul_pow, mul_assoc ((χ (AdelicLevel.uniformizerUnit ℚ v) : ℂˣ) : ℂ),
    mul_one_div_cancel hc, mul_one]
  ring

private theorem ramified_clause_torusUnipotentPoint (W : LocalGL3 v → ℂ) (e₁ e₂ e₃ : ℂ)
    (hW : IsRightInvariant (localMaximalCompact3 (𝓞 ℚ) ℚ v) W ∧
      IsCosetEigenfunction (localMaximalCompact3 (𝓞 ℚ) ℚ v) (heckeGen1 v) W (cNormQ v * e₁) ∧
      IsCosetEigenfunction (localMaximalCompact3 (𝓞 ℚ) ℚ v) (heckeGen2 v) W (cNormQ v * e₂) ∧
      ∀ g : LocalGL3 v, W (centralGen v * g) = e₃ * W g)
    (hψ : IsGL3PsiWhittakerFn (psiLocal ℚ v) W) (χ : (v.adicCompletion ℚ)ˣ →* ℂˣ) (a : ℕ) (ha : 1 ≤ a)
    (hχa : HasConductorExponentAt ℚ v χ a)
    (hu : ‖((χ (NumberField.AdelicLevel.uniformizerUnit ℚ v) : ℂˣ) : ℂ)‖ = 1) (k : ℤ) (d : ℕ)
    (y : v.adicCompletion ℚ) (hy : Valued.v y = WithZero.exp (d : ℤ)) :
    letI := localBorel ℚ v
    ∃ (P : ℂ → ℂ) (σ₀ σ₁ : ℝ),
      (∃ (Q : Polynomial ℂ) (m : ℕ), ∀ s : ℂ,
        P s = Q.eval ((Ideal.absNorm v.asIdeal : ℂ) ^ (-s)) * (Ideal.absNorm v.asIdeal : ℂ) ^ ((m : ℂ) * s)) ∧
      IsLocalZeta30ConvergentAbove v (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ v)))
        W χ (torusUnipotentPoint v k y) σ₀ ∧
      (∀ s : ℂ, σ₀ < s.re →
        localZeta30 v (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ v))) W χ s (torusUnipotentPoint v k y) =
          P s) ∧
      IsLocalZeta31ConvergentAbove v (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ v)))
        (selfDualHaarAt ℚ v) (dualWhittakerFn3 W) χ⁻¹ (weylPrime3 * transposeInv3 (torusUnipotentPoint v k y)) σ₁ ∧
      ∀ s : ℂ, σ₁ < (1 - s).re →
        ((selfDualHaarAt ℚ v).real (v.adicCompletionIntegers ℚ : Set (v.adicCompletion ℚ)) : ℂ)⁻¹ *
            localZetaDual31 v (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ v)))
              (selfDualHaarAt ℚ v) W χ (1 - s) (torusUnipotentPoint v k y) =
          (e₃ ^ a * LanglandsTunnell.TateLocal.stdRootNumberAt ℚ v χ ^ 3 *
              (Ideal.absNorm v.asIdeal : ℂ) ^ (((3 * a : ℕ) : ℂ) * (1 / 2 - s))) * P s := by
  letI := localBorel ℚ v
  have hvol := selfDualHaarAt_real_integers_eq_one v
  by_cases he₃ : e₃ = 0
  ·
    have hW0 : ∀ g : LocalGL3 v, W g = 0 := apply_eq_zero_of_eq_zero W e₁ e₂ e₃ hW he₃
    refine ⟨fun _ => 0, 0, 0, ⟨0, 0, fun s => by simp⟩, ?_, ?_, ?_, ?_⟩
    · intro s _
      simp only [hW0, zero_mul]
      exact integrable_zero _ _ _
    · intro s _
      simp [localZeta30, hW0]
    · intro s _
      simp only [dualWhittakerFn3_apply, hW0, zero_mul]
      exact integrable_zero _ _ _
    · intro s _
      simp [localZetaDual31, localZeta31, dualWhittakerFn3_apply, hW0]

  obtain ⟨σ₀, hσ₀⟩ := exists_isLocalZeta30ConvergentAbove_torusUnipotentPoint W e₁ e₂ e₃ hW hψ χ a hχa k y
  obtain ⟨σ₁, hσ₁⟩ := exists_isLocalZeta31ConvergentAbove_dual_torusUnipotentPoint W e₁ e₂ e₃ hW hψ χ a hχa he₃ k y
  rcases lt_or_ge k 0 with hk | hk
  ·
    refine ⟨fun _ => 0, σ₀, σ₁, ⟨0, 0, fun s => by simp⟩, hσ₀, fun s _ => ?_, hσ₁, fun s hs => ?_⟩
    · exact localZeta30_torusUnipotentPoint_of_neg W e₁ e₂ e₃ hW hψ χ k hk y s
    · rw [localZetaDual31_torusUnipotentPoint_of_neg W e₁ e₂ e₃ hW hψ χ he₃ a hχa k hk d y hy (1 - s) (hσ₁ (1 - s) hs)]
      simp
  obtain ⟨k, rfl⟩ : ∃ k' : ℕ, k = (k' : ℤ) := ⟨k.toNat, by omega⟩

  refine ⟨fun s => if a ≤ d then
      W 1 * twoRowCoeff e₁ e₂ e₃ (k + d - a) k *
        (((χ (ratPrimeUnit v) : ℂˣ) : ℂ) * (Ideal.absNorm v.asIdeal : ℂ) ^ (-s)) ^ (k + d - a) *
        gaussIntegral v (psiLocal ℚ v) χ (ratPrimeAt v ^ (d - a) * y)
    else 0, σ₀, σ₁, ?_, hσ₀, fun s hs => ?_, hσ₁, fun s hs => ?_⟩
  ·
    by_cases had : a ≤ d
    · obtain ⟨Q, m, hQ⟩ := exists_polynomial_eval_rpow_mul_of_monomial (Ideal.absNorm v.asIdeal : ℂ)
        (W 1 * twoRowCoeff e₁ e₂ e₃ (k + d - a) k * ((χ (ratPrimeUnit v) : ℂˣ) : ℂ) ^ (k + d - a) *
          gaussIntegral v (psiLocal ℚ v) χ (ratPrimeAt v ^ (d - a) * y)) (k + d - a)
      refine ⟨Q, m, fun s => ?_⟩
      simp only [if_pos had]
      rw [← hQ s, mul_pow]
      ring
    · exact ⟨0, 0, fun s => by simp [had]⟩
  ·
    exact localZeta30_torusUnipotentPoint_of_hasConductorExponentAt W e₁ e₂ e₃ hW hψ χ a ha hχa k d y hy s (hσ₀ s hs)
  ·
    rw [localZetaDual31_torusUnipotentPoint_of_hasConductorExponentAt W e₁ e₂ e₃ hW hψ χ a ha hχa k d y hy (1 - s)
      (hσ₁ (1 - s) hs)]
    by_cases had : a ≤ d
    swap
    · simp [had]
    simp only [if_pos had]
    rw [hvol]

    set q : ℂ := (Ideal.absNorm v.asIdeal : ℂ) with hq
    have hq0 : q ≠ 0 := absNorm_complex_ne_zero v
    have hp0 : ratPrimeAt v ≠ 0 := ratPrimeAt_ne_zero v
    have hy0 : y ≠ 0 := by
      rintro rfl
      simp at hy
      exact WithZero.exp_ne_zero hy.symm

    have huy0 : ratPrimeAt v ^ d * y ≠ 0 := mul_ne_zero (pow_ne_zero _ hp0) hy0
    set uy : (v.adicCompletion ℚ)ˣ := Units.mk0 _ huy0 with huy
    have huy1 : Valued.v ((uy : (v.adicCompletion ℚ)ˣ) : v.adicCompletion ℚ) = 1 := by
      rw [huy, Units.val_mk0, map_mul, map_pow, valued_ratPrimeAt_eq_valued_varpi, AdelicLevel.valued_uniformizerUnit,
        hy, ← WithZero.exp_nsmul, ← WithZero.exp_add]
      simp
    have huy1' : Valued.v (((uy⁻¹ : (v.adicCompletion ℚ)ˣ)) : v.adicCompletion ℚ) = 1 := by
      rw [Units.val_inv_eq_inv_val, map_inv₀, huy1, inv_one]

    have hG_direct : gaussIntegral v (psiLocal ℚ v) χ (ratPrimeAt v ^ (d - a) * y) =
        ((χ uy : ℂˣ) : ℂ)⁻¹ * gaussIntegral v (psiLocal ℚ v) χ ((ratPrimeAt v ^ a)⁻¹) := by
      have harg : ratPrimeAt v ^ (d - a) * y =
          (ratPrimeAt v ^ a)⁻¹ * ((uy : (v.adicCompletion ℚ)ˣ) : v.adicCompletion ℚ) := by
        rw [huy, Units.val_mk0, pow_sub₀ _ hp0 had]
        ring
      rw [harg, gaussIntegral_mul_coe_units v _ _ _ huy1]
    have hG_dual : gaussIntegral v (psiLocal ℚ v) χ⁻¹ ((ratPrimeAt v ^ (d + a) * y)⁻¹) =
        ((χ uy : ℂˣ) : ℂ)⁻¹ * gaussIntegral v (psiLocal ℚ v) χ⁻¹ ((ratPrimeAt v ^ a)⁻¹) := by
      have harg : (ratPrimeAt v ^ (d + a) * y)⁻¹ =
          (ratPrimeAt v ^ a)⁻¹ * (((uy⁻¹ : (v.adicCompletion ℚ)ˣ)) : v.adicCompletion ℚ) := by
        rw [Units.val_inv_eq_inv_val, huy, Units.val_mk0, pow_add]
        field_simp
      rw [harg, gaussIntegral_mul_coe_units v _ _ _ huy1']
      simp only [MonoidHom.inv_apply, map_inv, inv_inv]

    have hprod : gaussIntegral v (psiLocal ℚ v) χ ((ratPrimeAt v ^ a)⁻¹) *
        gaussIntegral v (psiLocal ℚ v) χ⁻¹ ((ratPrimeAt v ^ a)⁻¹) * q ^ a = ((χ (-1) : ℂˣ) : ℂ) := by
      have h := gaussIntegral_mul_gaussIntegral_inv (psiLocal_rat_facts v).1
        (exists_valued_le_exp_one_and_psiLocal_rat_ne_one v) ha hχa (valued_ratPrimeAt_pow_inv a)
      rw [hvol] at h
      have hneg : charExt χ (-1 : v.adicCompletion ℚ) = ((χ (-1) : ℂˣ) : ℂ) := by
        rw [show (-1 : v.adicCompletion ℚ) = (((-1 : (v.adicCompletion ℚ)ˣ)) : v.adicCompletion ℚ) by simp,
          charExt_coe_units]
      rw [hneg] at h
      simpa using h

    have hε := stdRootNumberAt_eq_ratPrime_form χ ha hχa hu

    set r : ℂ := (((Ideal.absNorm v.asIdeal : ℝ) ^ (1 / 2 : ℝ) : ℝ) : ℂ) with hr
    have hq_nonneg : (0 : ℝ) ≤ (Ideal.absNorm v.asIdeal : ℝ) := Nat.cast_nonneg _
    have hr2 : r ^ 2 = q := by
      rw [hr, hq]
      have : ((Ideal.absNorm v.asIdeal : ℝ) ^ (1 / 2 : ℝ)) ^ 2 = (Ideal.absNorm v.asIdeal : ℝ) := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul hq_nonneg]
        norm_num
      exact_mod_cast this
    have hhalf : ((((Ideal.absNorm v.asIdeal : ℝ) ^ (a : ℤ) : ℝ) : ℂ)) ^ (1 / 2 : ℂ) = r ^ a := by
      have h1 : ((((Ideal.absNorm v.asIdeal : ℝ) ^ (a : ℤ) : ℝ) : ℂ)) ^ (1 / 2 : ℂ) =
          ((((Ideal.absNorm v.asIdeal : ℝ) ^ (a : ℤ)) ^ (1 / 2 : ℝ) : ℝ) : ℂ) := by
        rw [show (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) by norm_num, ← Complex.ofReal_cpow (zpow_nonneg hq_nonneg _)]
      rw [h1, hr, zpow_natCast, ← Real.rpow_natCast, ← Real.rpow_mul hq_nonneg, mul_comm (a : ℝ) (1 / 2),
        Real.rpow_mul hq_nonneg, Real.rpow_natCast, Complex.ofReal_pow]
    have hX1 : q ^ (((k + d + 2 * a : ℕ) : ℂ) * (1 - s - 1)) =
        (q ^ (-s)) ^ (3 * a) * (q ^ (-s)) ^ (k + d - a) := by
      rw [show (1 - s - 1 : ℂ) = -s by ring, Complex.cpow_nat_mul, ← pow_add]
      congr 1
      omega
    have hX2 : q ^ (((3 * a : ℕ) : ℂ) * (1 / 2 - s)) = r ^ (3 * a) * (q ^ (-s)) ^ (3 * a) := by
      rw [Complex.cpow_nat_mul, show (1 / 2 - s : ℂ) = (1 / 2 : ℂ) + -s by ring, Complex.cpow_add _ _ hq0, mul_pow]
      congr 2
      rw [hr, hq, ← Complex.ofReal_natCast, show (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) by norm_num,
        ← Complex.ofReal_cpow hq_nonneg]
    have hχp : ((χ (ratPrimeUnit v) : ℂˣ) : ℂ) ^ (k + d + 2 * a) =
        ((χ (ratPrimeUnit v) : ℂˣ) : ℂ) ^ (3 * a) * ((χ (ratPrimeUnit v) : ℂˣ) : ℂ) ^ (k + d - a) := by
      rw [← pow_add]
      congr 1
      omega
    rw [hG_direct, hG_dual, hε, hhalf, hX1, hX2, hχp, ← hprod, ← hr2, Complex.ofReal_one]
    ring

end Ramified
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_laurent_localZeta_eq_gl3LFactorPoly_of_sphericalData.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_exists_laurent_localZeta_eq_gl3LFactorPoly_of_sphericalData.LanglandsTunnell.CubicInduction"
end
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_laurent_localZeta_eq_gl3LFactorPoly_of_sphericalData.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_exists_laurent_localZeta_eq_gl3LFactorPoly_of_sphericalData.LanglandsTunnell.CubicInduction"

section

set_option autoImplicit false

open IsDedekindDomain NumberField NumberField.TateGlobal AutomorphicForm LanglandsTunnell.Converse LanglandsTunnell.RankinSelberg LanglandsTunnell.TateLocal MeasureTheory

p2m_open "IsDedekindDomain.HeightOneSpectrum~Extension LanglandsTunnell.CubicInduction P2MW.S_LanglandsTunnell_CubicInduction_exists_laurent_localZeta_eq_gl3LFactorPoly_of_sphericalData.LanglandsTunnell.CubicInduction NumberField.StandardAddChar"

section Unramified

variable {v : HeightOneSpectrum (𝓞 ℚ)}

private theorem twoRow_sphericalTorusValue (e₁ e₂ e₃ : ℂ) :
    twoRow (sphericalTorusValue e₁ e₂ e₃) = twoRowCoeff e₁ e₂ e₃ := by
  funext a b
  cases b <;> rfl

private theorem clause_of_forall_eq_zero (W : LocalGL3 v → ℂ) (e₁ e₂ e₃ : ℂ) (hW0 : ∀ g, W g = 0)
    (χ : (v.adicCompletion ℚ)ˣ →* ℂˣ) (t : ℂ) (k : ℤ) (y : v.adicCompletion ℚ) :
    letI := localBorel ℚ v
    ∃ (P : ℂ → ℂ) (σ₀ σ₁ : ℝ),
      (∃ (Q : Polynomial ℂ) (m : ℕ), ∀ s : ℂ,
        P s = Q.eval ((Ideal.absNorm v.asIdeal : ℂ) ^ (-s)) * (Ideal.absNorm v.asIdeal : ℂ) ^ ((m : ℂ) * s)) ∧
      IsLocalZeta30ConvergentAbove v (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ v)))
        W χ (torusUnipotentPoint v k y) σ₀ ∧
      (∀ s : ℂ, σ₀ < s.re →
        localZeta30 v (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ v))) W χ s (torusUnipotentPoint v k y) =
          ((gl3LFactorPoly (t * e₁) (t ^ 2 * e₂) (t ^ 3 * e₃)).eval
              ((Ideal.absNorm v.asIdeal : ℂ) ^ (-s)))⁻¹ * P s) ∧
      IsLocalZeta31ConvergentAbove v (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ v)))
        (selfDualHaarAt ℚ v) (dualWhittakerFn3 W) χ⁻¹ (weylPrime3 * transposeInv3 (torusUnipotentPoint v k y)) σ₁ ∧
      ∀ s : ℂ, σ₁ < (1 - s).re →
        ((selfDualHaarAt ℚ v).real (v.adicCompletionIntegers ℚ : Set (v.adicCompletion ℚ)) : ℂ)⁻¹ *
            localZetaDual31 v (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ v)))
              (selfDualHaarAt ℚ v) W χ (1 - s) (torusUnipotentPoint v k y) =
          ((gl3LFactorPoly (t⁻¹ * (e₂ / e₃)) (t⁻¹ ^ 2 * (e₁ / e₃)) (t⁻¹ ^ 3 * e₃⁻¹)).eval
              ((Ideal.absNorm v.asIdeal : ℂ) ^ (-(1 - s))))⁻¹ * P s := by
  letI := localBorel ℚ v
  refine ⟨fun _ => 0, 0, 0, ⟨0, 0, fun s => by simp⟩, isLocalZeta30ConvergentAbove_of_forall_eq_zero v hW0 χ _ 0,
    fun s _ => ?_, isLocalZeta31ConvergentAbove_dual_of_forall_eq_zero v hW0 χ _ 0, fun s _ => ?_⟩
  · rw [localZeta30_eq_zero_of_forall_eq_zero v hW0 χ s]
    simp
  · rw [localZetaDual31_eq_zero_of_forall_eq_zero v hW0 χ (1 - s)]
    simp

private theorem unramified_clause_torusUnipotentPoint (W : LocalGL3 v → ℂ) (e₁ e₂ e₃ : ℂ)
    (hW : IsRightInvariant (localMaximalCompact3 (𝓞 ℚ) ℚ v) W ∧
      IsCosetEigenfunction (localMaximalCompact3 (𝓞 ℚ) ℚ v) (heckeGen1 v) W (cNormQ v * e₁) ∧
      IsCosetEigenfunction (localMaximalCompact3 (𝓞 ℚ) ℚ v) (heckeGen2 v) W (cNormQ v * e₂) ∧
      ∀ g : LocalGL3 v, W (centralGen v * g) = e₃ * W g)
    (hψ : IsGL3PsiWhittakerFn (psiLocal ℚ v) W) (χ : (v.adicCompletion ℚ)ˣ →* ℂˣ)
    (hχ0 : HasConductorExponentAt ℚ v χ 0)
    (t : ℂ) (ht : t = ((χ (NumberField.AdelicLevel.uniformizerUnit ℚ v) : ℂˣ) : ℂ))
    (k : ℤ) (d : ℕ) (y : v.adicCompletion ℚ) (hy : Valued.v y = WithZero.exp (d : ℤ)) :
    letI := localBorel ℚ v
    ∃ (P : ℂ → ℂ) (σ₀ σ₁ : ℝ),
      (∃ (Q : Polynomial ℂ) (m : ℕ), ∀ s : ℂ,
        P s = Q.eval ((Ideal.absNorm v.asIdeal : ℂ) ^ (-s)) * (Ideal.absNorm v.asIdeal : ℂ) ^ ((m : ℂ) * s)) ∧
      IsLocalZeta30ConvergentAbove v (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ v)))
        W χ (torusUnipotentPoint v k y) σ₀ ∧
      (∀ s : ℂ, σ₀ < s.re →
        localZeta30 v (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ v))) W χ s (torusUnipotentPoint v k y) =
          ((gl3LFactorPoly (t * e₁) (t ^ 2 * e₂) (t ^ 3 * e₃)).eval
              ((Ideal.absNorm v.asIdeal : ℂ) ^ (-s)))⁻¹ * P s) ∧
      IsLocalZeta31ConvergentAbove v (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ v)))
        (selfDualHaarAt ℚ v) (dualWhittakerFn3 W) χ⁻¹ (weylPrime3 * transposeInv3 (torusUnipotentPoint v k y)) σ₁ ∧
      ∀ s : ℂ, σ₁ < (1 - s).re →
        ((selfDualHaarAt ℚ v).real (v.adicCompletionIntegers ℚ : Set (v.adicCompletion ℚ)) : ℂ)⁻¹ *
            localZetaDual31 v (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ v)))
              (selfDualHaarAt ℚ v) W χ (1 - s) (torusUnipotentPoint v k y) =
          ((gl3LFactorPoly (t⁻¹ * (e₂ / e₃)) (t⁻¹ ^ 2 * (e₁ / e₃)) (t⁻¹ ^ 3 * e₃⁻¹)).eval
              ((Ideal.absNorm v.asIdeal : ℂ) ^ (-(1 - s))))⁻¹ * P s := by
  letI := localBorel ℚ v

  by_cases he₃ : e₃ = 0
  · exact clause_of_forall_eq_zero W e₁ e₂ e₃ (apply_eq_zero_of_eq_zero W e₁ e₂ e₃ hW he₃) χ t k y
  by_cases hW1 : W 1 = 0
  · exact clause_of_forall_eq_zero W e₁ e₂ e₃
      (fun g => by simp only [eq_zero_of_apply_one_eq_zero_of_psiLocal v W e₁ e₂ e₃ hW hψ hW1, Pi.zero_apply]) χ t k y

  obtain ⟨σ₀, hσ₀⟩ := exists_isLocalZeta30ConvergentAbove_torusUnipotentPoint W e₁ e₂ e₃ hW hψ χ 0 hχ0 k y
  obtain ⟨σ₁, hσ₁⟩ := exists_isLocalZeta31ConvergentAbove_dual_torusUnipotentPoint W e₁ e₂ e₃ hW hψ χ 0 hχ0 he₃ k y
  rcases lt_or_ge k 0 with hk | hk
  ·
    refine ⟨fun _ => 0, σ₀, σ₁, ⟨0, 0, fun s => by simp⟩, hσ₀, fun s _ => ?_, hσ₁, fun s hs => ?_⟩
    · rw [localZeta30_torusUnipotentPoint_of_neg W e₁ e₂ e₃ hW hψ χ k hk y s]
      simp
    · rw [localZetaDual31_torusUnipotentPoint_of_neg W e₁ e₂ e₃ hW hψ χ he₃ 0 hχ0 k hk d y hy (1 - s) (hσ₁ (1 - s) hs)]
      simp
  obtain ⟨k, rfl⟩ : ∃ k' : ℕ, k = (k' : ℤ) := ⟨k.toNat, by omega⟩

  have ht0 : t ≠ 0 := by
    rw [ht]
    exact Units.ne_zero _
  have hq0 : (Ideal.absNorm v.asIdeal : ℂ) ≠ 0 := absNorm_complex_ne_zero v

  obtain ⟨ρ₀, hρ₀⟩ := exists_forall_norm_mul_absNorm_cpow_neg_mul_lt_one v t (1 + ‖e₁‖ + ‖e₂‖ + ‖e₃‖)
  obtain ⟨ρ₁, hρ₁⟩ :=
    exists_forall_norm_mul_absNorm_cpow_neg_mul_lt_one v t⁻¹ (1 + ‖e₂ / e₃‖ + ‖e₁ / e₃‖ + ‖e₃⁻¹‖)

  have hdict : ∀ n m : ℕ, m ≤ n →
      e₃ ^ n * twoRowCoeff (e₂ / e₃) (e₁ / e₃) e₃⁻¹ n m = twoRowCoeff e₁ e₂ e₃ n (n - m) := by
    intro n m hm
    rw [twoRowCoeff_inv_triple W e₁ e₂ e₃ hW hψ he₃ hW1 n m hm, ← mul_assoc, ← mul_pow, mul_inv_cancel₀ he₃, one_pow,
      one_mul]
  refine ⟨fun s => W 1 *
      (((selfDualHaarAt ℚ v).real (v.adicCompletionIntegers ℚ : Set (v.adicCompletion ℚ)) : ℂ) *
          (1 - (Ideal.absNorm v.asIdeal : ℂ)⁻¹) * (t * (Ideal.absNorm v.asIdeal : ℂ) ^ (-s)) ^ (k + d) *
          (twoRowCoeff e₁ e₂ e₃ (k + d) k +
            (twoRowCoeff e₁ e₂ e₃ (k + d + 1) k - e₁ * twoRowCoeff e₁ e₂ e₃ (k + d) k) *
              (t * (Ideal.absNorm v.asIdeal : ℂ) ^ (-s)) +
            (twoRowCoeff e₁ e₂ e₃ (k + d + 2) k - e₁ * twoRowCoeff e₁ e₂ e₃ (k + d + 1) k +
                e₂ * twoRowCoeff e₁ e₂ e₃ (k + d) k) *
              (t * (Ideal.absNorm v.asIdeal : ℂ) ^ (-s)) ^ 2) -
        if 1 ≤ d then
          ((selfDualHaarAt ℚ v).real (v.adicCompletionIntegers ℚ : Set (v.adicCompletion ℚ)) : ℂ) *
            (Ideal.absNorm v.asIdeal : ℂ)⁻¹ * twoRowCoeff e₁ e₂ e₃ (k + d - 1) k *
            (t * (Ideal.absNorm v.asIdeal : ℂ) ^ (-s)) ^ (k + d - 1) *
            (1 - e₁ * (t * (Ideal.absNorm v.asIdeal : ℂ) ^ (-s)) +
              e₂ * (t * (Ideal.absNorm v.asIdeal : ℂ) ^ (-s)) ^ 2 -
              e₃ * (t * (Ideal.absNorm v.asIdeal : ℂ) ^ (-s)) ^ 3)
        else 0),
    max σ₀ ρ₀, max σ₁ ρ₁, ?_, fun s hs => hσ₀ s ((le_max_left _ _).trans_lt hs), fun s hs => ?_,
    fun s hs => hσ₁ s ((le_max_left _ _).trans_lt hs), fun s hs => ?_⟩
  ·
    refine ⟨Polynomial.C (W 1) *
      (Polynomial.C (((selfDualHaarAt ℚ v).real (v.adicCompletionIntegers ℚ : Set (v.adicCompletion ℚ)) : ℂ) *
            (1 - (Ideal.absNorm v.asIdeal : ℂ)⁻¹)) * (Polynomial.C t * Polynomial.X) ^ (k + d) *
          (Polynomial.C (twoRowCoeff e₁ e₂ e₃ (k + d) k) +
            Polynomial.C (twoRowCoeff e₁ e₂ e₃ (k + d + 1) k - e₁ * twoRowCoeff e₁ e₂ e₃ (k + d) k) *
              (Polynomial.C t * Polynomial.X) +
            Polynomial.C (twoRowCoeff e₁ e₂ e₃ (k + d + 2) k - e₁ * twoRowCoeff e₁ e₂ e₃ (k + d + 1) k +
                e₂ * twoRowCoeff e₁ e₂ e₃ (k + d) k) *
              (Polynomial.C t * Polynomial.X) ^ 2) -
        if 1 ≤ d then
          Polynomial.C (((selfDualHaarAt ℚ v).real (v.adicCompletionIntegers ℚ : Set (v.adicCompletion ℚ)) : ℂ) *
              (Ideal.absNorm v.asIdeal : ℂ)⁻¹ * twoRowCoeff e₁ e₂ e₃ (k + d - 1) k) *
            (Polynomial.C t * Polynomial.X) ^ (k + d - 1) *
            (1 - Polynomial.C e₁ * (Polynomial.C t * Polynomial.X) +
              Polynomial.C e₂ * (Polynomial.C t * Polynomial.X) ^ 2 -
              Polynomial.C e₃ * (Polynomial.C t * Polynomial.X) ^ 3)
        else 0), 0, fun s => ?_⟩
    simp only [Nat.cast_zero, zero_mul, Complex.cpow_zero, mul_one]
    split_ifs <;>
      simp only [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X, Polynomial.eval_pow, Polynomial.eval_add,
        Polynomial.eval_sub, Polynomial.eval_one, sub_zero]
  ·
    have hY := hρ₀ s ((le_max_right _ _).trans_lt hs)
    have hL := eval_gl3LFactorPoly_ne_zero e₁ e₂ e₃ _ hY
    have hLF := eval_gl3LFactorPoly_mul_tsum_twoRowCoeff e₁ e₂ e₃ _ hY (k + d) k
    rw [localZeta30_torusUnipotentPoint_of_hasConductorExponentAt_zero W e₁ e₂ e₃ hW hψ χ hχ0 t ht k d y hy s
        (hσ₀ s ((le_max_left _ _).trans_lt hs)),
      eval_gl3LFactorPoly_twist, inv_mul_eq_div, eq_div_iff hL]
    rw [eval_gl3LFactorPoly] at hLF hL ⊢
    beta_reduce
    split_ifs <;>
      linear_combination
        (W 1 * (((selfDualHaarAt ℚ v).real (v.adicCompletionIntegers ℚ : Set (v.adicCompletion ℚ)) : ℂ) *
          (1 - (Ideal.absNorm v.asIdeal : ℂ)⁻¹))) * hLF
  ·
    have hZ := hρ₁ (1 - s) ((le_max_right _ _).trans_lt hs)
    have hL := eval_gl3LFactorPoly_ne_zero (e₂ / e₃) (e₁ / e₃) e₃⁻¹ _ hZ
    rw [localZetaDual31_torusUnipotentPoint_of_hasConductorExponentAt_zero W e₁ e₂ e₃ hW hψ χ he₃ hχ0 t ht ht0 k d y hy
        (1 - s) (hσ₁ (1 - s) ((le_max_left _ _).trans_lt hs)),
      eval_gl3LFactorPoly_twist, eq_inv_mul_iff_mul_eq₀ hL, zpow_neg, zpow_natCast]
    rw [eval_gl3LFactorPoly] at hL ⊢
    beta_reduce

    set q : ℂ := (Ideal.absNorm v.asIdeal : ℂ) with hq
    set vol : ℂ := ((selfDualHaarAt ℚ v).real (v.adicCompletionIntegers ℚ : Set (v.adicCompletion ℚ)) : ℂ) with hvol
    set Z : ℂ := t⁻¹ * q ^ (-(1 - s)) with hZdef
    set Y : ℂ := t * q ^ (-s) with hYdef
    set L : ℂ := 1 - e₂ / e₃ * Z + e₁ / e₃ * Z ^ 2 - e₃⁻¹ * Z ^ 3 with hLdef

    have hZY : q * Z * Y = 1 := by
      have h1 : q ^ (-(1 - s)) * q ^ (-s) = q⁻¹ := by
        rw [← Complex.cpow_add _ _ hq0, show -(1 - s) + -s = (-1 : ℂ) by ring, Complex.cpow_neg_one]
      calc q * Z * Y = q * (q ^ (-(1 - s)) * q ^ (-s)) * (t⁻¹ * t) := by rw [hZdef, hYdef]; ring
        _ = 1 := by rw [h1, inv_mul_cancel₀ ht0, mul_one, mul_inv_cancel₀ hq0]
    have hZ0 : Z ≠ 0 := right_ne_zero_of_mul (left_ne_zero_of_mul_eq_one hZY)

    have hclass : ∀ c : ℕ, L * ∑' m : ℕ, twoRowCoeff (e₂ / e₃) (e₁ / e₃) e₃⁻¹ (k + d + m) c * Z ^ (c + m + 1) =
        Z ^ (c + 1) * cubicWindow (sphericalTorusValue (e₂ / e₃) (e₁ / e₃) e₃⁻¹) (e₂ / e₃) (e₁ / e₃) Z (k + d) c := by
      intro c
      have hLF := eval_gl3LFactorPoly_mul_tsum_twoRowCoeff (e₂ / e₃) (e₁ / e₃) e₃⁻¹ Z hZ (k + d) c
      rw [eval_gl3LFactorPoly, ← hLdef] at hLF
      have hshift : (∑' m : ℕ, twoRowCoeff (e₂ / e₃) (e₁ / e₃) e₃⁻¹ (k + d + m) c * Z ^ (c + m + 1)) * Z ^ (k + d) =
          Z ^ (c + 1) * ∑' m : ℕ, twoRowCoeff (e₂ / e₃) (e₁ / e₃) e₃⁻¹ (k + d + m) c * Z ^ (k + d + m) := by
        rw [← tsum_mul_right, ← tsum_mul_left]
        congr 1
        funext m
        ring
      rw [cubicWindow, twoRow_sphericalTorusValue]
      apply mul_right_cancel₀ (pow_ne_zero (k + d) hZ0)
      linear_combination Z ^ (c + 1) * hLF + L * hshift

    have hsum : L *
        (vol * (vol * (1 - q⁻¹)) *
            ∑' m : ℕ, twoRowCoeff (e₂ / e₃) (e₁ / e₃) e₃⁻¹ (k + d + m) (k + d) * Z ^ (k + d + m + 1) +
          ∑ c ∈ Finset.Ico (d - 1) (k + d),
            (if 1 ≤ d ∧ c = d - 1 then -(vol * q⁻¹) else vol * (1 - q⁻¹)) *
              (vol * (1 - q⁻¹) * ∑' m : ℕ, twoRowCoeff (e₂ / e₃) (e₁ / e₃) e₃⁻¹ (k + d + m) c * Z ^ (c + m + 1) -
                vol * q⁻¹ * twoRowCoeff (e₂ / e₃) (e₁ / e₃) e₃⁻¹ (k + d - 1) c * Z ^ c)) =
        vol * (vol * (1 - q⁻¹)) * Z ^ (k + d + 1) *
            cubicWindow (sphericalTorusValue (e₂ / e₃) (e₁ / e₃) e₃⁻¹) (e₂ / e₃) (e₁ / e₃) Z (k + d) (k + d) +
          ∑ c ∈ Finset.Ico (d - 1) (k + d),
            (if 1 ≤ d ∧ c = d - 1 then -(vol * q⁻¹) else vol * (1 - q⁻¹)) *
              (vol * (1 - q⁻¹) * Z ^ (c + 1) *
                  cubicWindow (sphericalTorusValue (e₂ / e₃) (e₁ / e₃) e₃⁻¹) (e₂ / e₃) (e₁ / e₃) Z (k + d) c -
                vol * q⁻¹ * twoRowCoeff (e₂ / e₃) (e₁ / e₃) e₃⁻¹ (k + d - 1) c * Z ^ c * L) := by
      rw [mul_add, Finset.mul_sum]
      congr 1
      · linear_combination (vol * (vol * (1 - q⁻¹))) * hclass (k + d)
      · refine Finset.sum_congr rfl fun c _ => ?_
        linear_combination ((if 1 ≤ d ∧ c = d - 1 then -(vol * q⁻¹) else vol * (1 - q⁻¹)) * (vol * (1 - q⁻¹))) *
          hclass c

    have hb := window_sum_identity (sphericalTorusValue (e₂ / e₃) (e₁ / e₃) e₃⁻¹) (e₂ / e₃) (e₁ / e₃) e₃⁻¹
      (inv_ne_zero he₃) (by simp [sphericalTorusValue]) (by simp [sphericalTorusValue]) (by simp [sphericalTorusValue])
      (sphericalTorusValue_add_three _ _ _) q vol Z Y (W 1) hq0 hZ0 hZY k d
    have hf₁ : e₂ / e₃ / e₃⁻¹ = e₂ := by field_simp
    have hf₂ : e₁ / e₃ / e₃⁻¹ = e₁ := by field_simp
    rw [twoRow_sphericalTorusValue, ← hLdef, inv_inv, hf₁, hf₂, hdict (k + d) d (by omega),
      hdict (k + d + 1) (d + 1) (by omega), hdict (k + d + 2) (d + 2) (by omega)] at hb
    simp only [show k + d - d = k by omega, show k + d + 1 - (d + 1) = k by omega,
      show k + d + 2 - (d + 2) = k by omega] at hb
    split_ifs at hb ⊢ with hd1
    · have hpeel : vol * q⁻¹ * e₃ ^ (k + d - 1) * twoRowCoeff (e₂ / e₃) (e₁ / e₃) e₃⁻¹ (k + d - 1) (d - 1) =
          vol * q⁻¹ * twoRowCoeff e₁ e₂ e₃ (k + d - 1) k := by
        rw [mul_assoc (vol * q⁻¹), hdict (k + d - 1) (d - 1) (by omega), show k + d - 1 - (d - 1) = k by omega]
      rw [hpeel] at hb
      linear_combination (vol⁻¹ * W 1 * (e₃ / q) ^ (k + d) * (Z ^ (k + d + d + 1))⁻¹) * hsum + hb
    · linear_combination (vol⁻¹ * W 1 * (e₃ / q) ^ (k + d) * (Z ^ (k + d + d + 1))⁻¹) * hsum + hb

end Unramified
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_laurent_localZeta_eq_gl3LFactorPoly_of_sphericalData.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_exists_laurent_localZeta_eq_gl3LFactorPoly_of_sphericalData.LanglandsTunnell.CubicInduction"
end
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_laurent_localZeta_eq_gl3LFactorPoly_of_sphericalData.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_exists_laurent_localZeta_eq_gl3LFactorPoly_of_sphericalData.LanglandsTunnell.CubicInduction"

section

set_option autoImplicit false

open IsDedekindDomain NumberField NumberField.TateGlobal AutomorphicForm LanglandsTunnell.Converse LanglandsTunnell.RankinSelberg LanglandsTunnell.TateLocal MeasureTheory

p2m_open "IsDedekindDomain.HeightOneSpectrum~Extension LanglandsTunnell.CubicInduction P2MW.S_LanglandsTunnell_CubicInduction_exists_laurent_localZeta_eq_gl3LFactorPoly_of_sphericalData.LanglandsTunnell.CubicInduction NumberField.StandardAddChar"
open scoped NNReal

noncomputable section

section NormalFormPrivates

private theorem ofReal_zpow_cpow_one_sub {q : ℝ} (hq : 0 < q) (n : ℤ) (s : ℂ) :
    ((q ^ (-n) : ℝ) : ℂ) ^ (1 - s) = (q : ℂ) ^ (-n) * (q : ℂ) ^ ((n : ℂ) * s) := by
  have hq0 : (q : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hq.ne'
  rw [← Real.rpow_intCast, ← Complex.cpow_mul_ofReal_nonneg hq.le, ← Complex.cpow_intCast,
    ← Complex.cpow_add _ _ hq0]
  congr 1
  push_cast
  ring

variable (v : HeightOneSpectrum (𝓞 ℚ))

private theorem absNorm_ne_zero_complex : (Ideal.absNorm v.asIdeal : ℂ) ≠ 0 := by
  have h0 : Ideal.absNorm v.asIdeal ≠ 0 := Ideal.absNorm_eq_zero_iff.not.mpr v.ne_bot
  exact_mod_cast h0

private theorem coe_modulus_cpow_one_sub (c : (v.adicCompletion ℚ)ˣ) (s : ℂ) :
    ((modulus (c : v.adicCompletion ℚ) : ℝ) : ℂ) ^ (1 - s) =
      (Ideal.absNorm v.asIdeal : ℂ) ^ (-unitShellIndex v c) *
        (Ideal.absNorm v.asIdeal : ℂ) ^ ((unitShellIndex v c : ℂ) * s) := by
  have hq : (0 : ℝ) < (Ideal.absNorm v.asIdeal : ℝ) := by
    have h0 : Ideal.absNorm v.asIdeal ≠ 0 := Ideal.absNorm_eq_zero_iff.not.mpr v.ne_bot
    exact_mod_cast Nat.pos_of_ne_zero h0
  rw [modulus_coe_eq_zpow_neg_unitShellIndex v c, NNReal.coe_zpow, NNReal.coe_natCast,
    ofReal_zpow_cpow_one_sub hq, Complex.ofReal_natCast]

private theorem exists_eq_mul_torusUnipotentPoint_mul (g : LocalGL3 v) :
    ∃ (m : ℤ) (c : (v.adicCompletion ℚ)ˣ) (y₂₃ y₁₃ : v.adicCompletion ℚ) (k : ℤ) (d : ℕ) (y' : v.adicCompletion ℚ)
      (k' : LocalGL3 v), Valued.v y' = WithZero.exp (d : ℤ) ∧ k' ∈ localMaximalCompact3 (𝓞 ℚ) ℚ v ∧
        g = centralGen v ^ m * (iotaGL (diagUnitGL2 c) * (upperUnipotent3 0 y₂₃ y₁₃ *
          (torusUnipotentPoint v k y' * k'))) := by
  obtain ⟨m, c, y₂₃, y₁₃, k, y, k₀, hk₀, hg⟩ :=
    exists_eq_centralGen_zpow_mul_iotaGL_mul_upperUnipotent3_mul_mul_of_mem v g
  obtain ⟨d, y', k₁, hy', hk₁, hT⟩ := exists_torusUnipotentPoint_eq_mul_of_mem v k y
  refine ⟨m, c, y₂₃, y₁₃, k, d, y', k₁ * k₀, hy', mul_mem hk₁ hk₀, ?_⟩
  rw [hg, show iotaGL (diagUnits2 1 (ratPrimeUnit v ^ k)) * upperUnipotent3 y 0 0 = torusUnipotentPoint v k y
    from rfl, hT]
  simp only [mul_assoc]

end NormalFormPrivates
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_laurent_localZeta_eq_gl3LFactorPoly_of_sphericalData.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_exists_laurent_localZeta_eq_gl3LFactorPoly_of_sphericalData.LanglandsTunnell.CubicInduction"

private theorem localFunctionalEquation_of_sphericalData
    (v : HeightOneSpectrum (𝓞 ℚ)) (W : LocalGL3 v → ℂ) (e₁ e₂ e₃ : ℂ)
    (hW : IsRightInvariant (localMaximalCompact3 (𝓞 ℚ) ℚ v) W ∧
      IsCosetEigenfunction (localMaximalCompact3 (𝓞 ℚ) ℚ v) (heckeGen1 v) W (cNormQ v * e₁) ∧
      IsCosetEigenfunction (localMaximalCompact3 (𝓞 ℚ) ℚ v) (heckeGen2 v) W (cNormQ v * e₂) ∧
      ∀ g : LocalGL3 v, W (centralGen v * g) = e₃ * W g)
    (hψ : IsGL3PsiWhittakerFn (NumberField.StandardAddChar.psiLocal ℚ v) W)
    (χ : (v.adicCompletion ℚ)ˣ →* ℂˣ) (a : ℕ) (hχa : LanglandsTunnell.TateLocal.HasConductorExponentAt ℚ v χ a)
    (hu : ‖((χ (NumberField.AdelicLevel.uniformizerUnit ℚ v) : ℂˣ) : ℂ)‖ = 1)
    (t : ℂ) (ht : t = ((χ (NumberField.AdelicLevel.uniformizerUnit ℚ v) : ℂˣ) : ℂ)) (g : LocalGL3 v) :
    letI := localBorel ℚ v
    (a = 0 →
      ∃ (P : ℂ → ℂ) (σ₀ σ₁ : ℝ),
        (∃ (Q : Polynomial ℂ) (m : ℕ), ∀ s : ℂ,
          P s = Q.eval ((Ideal.absNorm v.asIdeal : ℂ) ^ (-s)) * (Ideal.absNorm v.asIdeal : ℂ) ^ ((m : ℂ) * s)) ∧
        IsLocalZeta30ConvergentAbove v (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ v)))
          W χ g σ₀ ∧
        (∀ s : ℂ, σ₀ < s.re →
          localZeta30 v (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ v))) W χ s g =
            ((gl3LFactorPoly (t * e₁) (t ^ 2 * e₂) (t ^ 3 * e₃)).eval
                ((Ideal.absNorm v.asIdeal : ℂ) ^ (-s)))⁻¹ * P s) ∧
        IsLocalZeta31ConvergentAbove v (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ v)))
          (selfDualHaarAt ℚ v) (dualWhittakerFn3 W) χ⁻¹ (weylPrime3 * transposeInv3 g) σ₁ ∧
        ∀ s : ℂ, σ₁ < (1 - s).re →
          ((selfDualHaarAt ℚ v).real (v.adicCompletionIntegers ℚ : Set (v.adicCompletion ℚ)) : ℂ)⁻¹ *
              localZetaDual31 v (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ v)))
                (selfDualHaarAt ℚ v) W χ (1 - s) g =
            ((gl3LFactorPoly (t⁻¹ * (e₂ / e₃)) (t⁻¹ ^ 2 * (e₁ / e₃)) (t⁻¹ ^ 3 * e₃⁻¹)).eval
                ((Ideal.absNorm v.asIdeal : ℂ) ^ (-(1 - s))))⁻¹ * P s) ∧
    (1 ≤ a →
      ∃ (P : ℂ → ℂ) (σ₀ σ₁ : ℝ),
        (∃ (Q : Polynomial ℂ) (m : ℕ), ∀ s : ℂ,
          P s = Q.eval ((Ideal.absNorm v.asIdeal : ℂ) ^ (-s)) * (Ideal.absNorm v.asIdeal : ℂ) ^ ((m : ℂ) * s)) ∧
        IsLocalZeta30ConvergentAbove v (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ v)))
          W χ g σ₀ ∧
        (∀ s : ℂ, σ₀ < s.re →
          localZeta30 v (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ v))) W χ s g =
            P s) ∧
        IsLocalZeta31ConvergentAbove v (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ v)))
          (selfDualHaarAt ℚ v) (dualWhittakerFn3 W) χ⁻¹ (weylPrime3 * transposeInv3 g) σ₁ ∧
        ∀ s : ℂ, σ₁ < (1 - s).re →
          ((selfDualHaarAt ℚ v).real (v.adicCompletionIntegers ℚ : Set (v.adicCompletion ℚ)) : ℂ)⁻¹ *
              localZetaDual31 v (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ v)))
                (selfDualHaarAt ℚ v) W χ (1 - s) g =
            (e₃ ^ a * LanglandsTunnell.TateLocal.stdRootNumberAt ℚ v χ ^ 3 *
                (Ideal.absNorm v.asIdeal : ℂ) ^ (((3 * a : ℕ) : ℂ) * (1 / 2 - s))) * P s) := by
  by_cases he₃ : e₃ = 0
  · have hW0 : W = fun _ => 0 := funext (apply_eq_zero_of_eq_zero W e₁ e₂ e₃ hW he₃)
    subst hW0
    refine ⟨fun _ => ⟨fun _ => 0, 0, 0, ⟨0, 0, fun s => by simp⟩, ?_, ?_, ?_, ?_⟩,
      fun _ => ⟨fun _ => 0, 0, 0, ⟨0, 0, fun s => by simp⟩, ?_, ?_, ?_, ?_⟩⟩
    · simp [IsLocalZeta30ConvergentAbove]
    · intro s _
      simp [localZeta30]
    · simp [IsLocalZeta31ConvergentAbove, dualWhittakerFn3]
    · intro s _
      simp [localZetaDual31, localZeta31, dualWhittakerFn3]
    · simp [IsLocalZeta30ConvergentAbove]
    · intro s _
      simp [localZeta30]
    · simp [IsLocalZeta31ConvergentAbove, dualWhittakerFn3]
    · intro s _
      simp [localZetaDual31, localZeta31, dualWhittakerFn3]
  obtain ⟨m, c, y₂₃, y₁₃, k, d, y', k', hy', hk', hg⟩ := exists_eq_mul_torusUnipotentPoint_mul v g
  subst hg
  have hq := absNorm_ne_zero_complex v

  have hZk := localZeta30_mul_of_mem_localMaximalCompact3 v W χ hW.1 hk' (torusUnipotentPoint v k y')
  have hDk := localZetaDual31_mul_of_mem_localMaximalCompact3 v W χ hW.1 hk' (torusUnipotentPoint v k y')
  have hZn := localZeta30_upperUnipotent3_mul v W χ hψ y₂₃ y₁₃ (torusUnipotentPoint v k y' * k')
  have hDn := localZetaDual31_upperUnipotent3_mul v W χ hψ y₂₃ y₁₃ (torusUnipotentPoint v k y' * k')
  have hZc := localZeta30_iotaGL_diagUnitGL2_mul v W χ c
    (upperUnipotent3 0 y₂₃ y₁₃ * (torusUnipotentPoint v k y' * k'))
  have hDc := localZetaDual31_iotaGL_diagUnitGL2_mul v W χ c
    (upperUnipotent3 0 y₂₃ y₁₃ * (torusUnipotentPoint v k y' * k'))
  have hZz := localZeta30_centralGen_zpow_mul v W χ e₃ he₃ hW.2.2.2 m
    (iotaGL (diagUnitGL2 c) * (upperUnipotent3 0 y₂₃ y₁₃ * (torusUnipotentPoint v k y' * k')))
  have hDz := localZetaDual31_centralGen_zpow_mul v W χ e₃ he₃ hW.2.2.2 m
    (iotaGL (diagUnitGL2 c) * (upperUnipotent3 0 y₂₃ y₁₃ * (torusUnipotentPoint v k y' * k')))
  refine ⟨fun ha0 => ?_, fun ha1 => ?_⟩
  · have hχ0 : HasConductorExponentAt ℚ v χ 0 := by rw [ha0] at hχa; exact hχa
    obtain ⟨P, σ₀, σ₁, hP, h0, hv0, h1, hv1⟩ :=
      unramified_clause_torusUnipotentPoint W e₁ e₂ e₃ hW hψ χ hχ0 t ht k d y' hy'
    refine ⟨fun s => e₃ ^ m * ((χ c : ℂˣ) : ℂ)⁻¹ * psiLocal ℚ v y₂₃ *
          (Ideal.absNorm v.asIdeal : ℂ) ^ (-unitShellIndex v c) *
        (Ideal.absNorm v.asIdeal : ℂ) ^ ((unitShellIndex v c : ℂ) * s) * P s, σ₀, σ₁,
      exists_polynomial_eval_rpow_mul_of_mul_zpow _ hq P hP _ _,
      (hZz.2 σ₀).2 ((hZc.2 σ₀).2 ((hZn.2 σ₀).2 ((hZk.2 σ₀).2 h0))),
      fun s hs => ?_, (hDz.2 σ₁).2 ((hDc.2 σ₁).2 ((hDn.2 σ₁).2 ((hDk.2 σ₁).2 h1))), fun s hs => ?_⟩
    · simp only [hZz.1 s, hZc.1 s, hZn.1 s, hZk.1 s, coe_modulus_cpow_one_sub]
      linear_combination
        (e₃ ^ m * ((χ c : ℂˣ) : ℂ)⁻¹ * psiLocal ℚ v y₂₃ * (Ideal.absNorm v.asIdeal : ℂ) ^ (-unitShellIndex v c) *
          (Ideal.absNorm v.asIdeal : ℂ) ^ ((unitShellIndex v c : ℂ) * s)) * hv0 s hs
    · simp only [hDz.1 (1 - s), hDc.1 (1 - s), hDn.1 (1 - s), hDk.1 (1 - s), coe_modulus_cpow_one_sub]
      linear_combination
        (e₃ ^ m * ((χ c : ℂˣ) : ℂ)⁻¹ * psiLocal ℚ v y₂₃ * (Ideal.absNorm v.asIdeal : ℂ) ^ (-unitShellIndex v c) *
          (Ideal.absNorm v.asIdeal : ℂ) ^ ((unitShellIndex v c : ℂ) * s)) * hv1 s hs
  · obtain ⟨P, σ₀, σ₁, hP, h0, hv0, h1, hv1⟩ :=
      ramified_clause_torusUnipotentPoint W e₁ e₂ e₃ hW hψ χ a ha1 hχa hu k d y' hy'
    refine ⟨fun s => e₃ ^ m * ((χ c : ℂˣ) : ℂ)⁻¹ * psiLocal ℚ v y₂₃ *
          (Ideal.absNorm v.asIdeal : ℂ) ^ (-unitShellIndex v c) *
        (Ideal.absNorm v.asIdeal : ℂ) ^ ((unitShellIndex v c : ℂ) * s) * P s, σ₀, σ₁,
      exists_polynomial_eval_rpow_mul_of_mul_zpow _ hq P hP _ _,
      (hZz.2 σ₀).2 ((hZc.2 σ₀).2 ((hZn.2 σ₀).2 ((hZk.2 σ₀).2 h0))),
      fun s hs => ?_, (hDz.2 σ₁).2 ((hDc.2 σ₁).2 ((hDn.2 σ₁).2 ((hDk.2 σ₁).2 h1))), fun s hs => ?_⟩
    · simp only [hZz.1 s, hZc.1 s, hZn.1 s, hZk.1 s, coe_modulus_cpow_one_sub]
      linear_combination
        (e₃ ^ m * ((χ c : ℂˣ) : ℂ)⁻¹ * psiLocal ℚ v y₂₃ * (Ideal.absNorm v.asIdeal : ℂ) ^ (-unitShellIndex v c) *
          (Ideal.absNorm v.asIdeal : ℂ) ^ ((unitShellIndex v c : ℂ) * s)) * hv0 s hs
    · simp only [hDz.1 (1 - s), hDc.1 (1 - s), hDn.1 (1 - s), hDk.1 (1 - s), coe_modulus_cpow_one_sub]
      linear_combination
        (e₃ ^ m * ((χ c : ℂˣ) : ℂ)⁻¹ * psiLocal ℚ v y₂₃ * (Ideal.absNorm v.asIdeal : ℂ) ^ (-unitShellIndex v c) *
          (Ideal.absNorm v.asIdeal : ℂ) ^ ((unitShellIndex v c : ℂ) * s)) * hv1 s hs

end
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_laurent_localZeta_eq_gl3LFactorPoly_of_sphericalData.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_exists_laurent_localZeta_eq_gl3LFactorPoly_of_sphericalData.LanglandsTunnell.CubicInduction"
end
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_laurent_localZeta_eq_gl3LFactorPoly_of_sphericalData.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_exists_laurent_localZeta_eq_gl3LFactorPoly_of_sphericalData.LanglandsTunnell.CubicInduction"

section

set_option autoImplicit false

open IsDedekindDomain NumberField NumberField.TateGlobal AutomorphicForm LanglandsTunnell.Converse LanglandsTunnell.RankinSelberg LanglandsTunnell.TateLocal MeasureTheory

p2m_open "LanglandsTunnell.CubicInduction P2MW.S_LanglandsTunnell_CubicInduction_exists_laurent_localZeta_eq_gl3LFactorPoly_of_sphericalData.LanglandsTunnell.CubicInduction"

theorem solution
    (v : HeightOneSpectrum (𝓞 ℚ)) (W : LocalGL3 v → ℂ) (e₁ e₂ e₃ : ℂ)
    (hW : IsRightInvariant (localMaximalCompact3 (𝓞 ℚ) ℚ v) W ∧
      IsCosetEigenfunction (localMaximalCompact3 (𝓞 ℚ) ℚ v) (heckeGen1 v) W (cNormQ v * e₁) ∧
      IsCosetEigenfunction (localMaximalCompact3 (𝓞 ℚ) ℚ v) (heckeGen2 v) W (cNormQ v * e₂) ∧
      ∀ g : LocalGL3 v, W (centralGen v * g) = e₃ * W g)
    (hψ : IsGL3PsiWhittakerFn (NumberField.StandardAddChar.psiLocal ℚ v) W)
    (χ : (v.adicCompletion ℚ)ˣ →* ℂˣ) (a : ℕ) (hχa : LanglandsTunnell.TateLocal.HasConductorExponentAt ℚ v χ a)
    (hu : ‖((χ (NumberField.AdelicLevel.uniformizerUnit ℚ v) : ℂˣ) : ℂ)‖ = 1)
    (t : ℂ) (ht : t = ((χ (NumberField.AdelicLevel.uniformizerUnit ℚ v) : ℂˣ) : ℂ)) (g : LocalGL3 v) :
    letI := localBorel ℚ v
    (a = 0 →
      ∃ (P : ℂ → ℂ) (σ₀ σ₁ : ℝ),
        (∃ (Q : Polynomial ℂ) (m : ℕ), ∀ s : ℂ,
          P s = Q.eval ((Ideal.absNorm v.asIdeal : ℂ) ^ (-s)) * (Ideal.absNorm v.asIdeal : ℂ) ^ ((m : ℂ) * s)) ∧
        IsLocalZeta30ConvergentAbove v (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ v)))
          W χ g σ₀ ∧
        (∀ s : ℂ, σ₀ < s.re →
          localZeta30 v (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ v))) W χ s g =
            ((gl3LFactorPoly (t * e₁) (t ^ 2 * e₂) (t ^ 3 * e₃)).eval
                ((Ideal.absNorm v.asIdeal : ℂ) ^ (-s)))⁻¹ * P s) ∧
        IsLocalZeta31ConvergentAbove v (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ v)))
          (selfDualHaarAt ℚ v) (dualWhittakerFn3 W) χ⁻¹ (weylPrime3 * transposeInv3 g) σ₁ ∧
        ∀ s : ℂ, σ₁ < (1 - s).re →
          ((selfDualHaarAt ℚ v).real (v.adicCompletionIntegers ℚ : Set (v.adicCompletion ℚ)) : ℂ)⁻¹ *
              localZetaDual31 v (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ v)))
                (selfDualHaarAt ℚ v) W χ (1 - s) g =
            ((gl3LFactorPoly (t⁻¹ * (e₂ / e₃)) (t⁻¹ ^ 2 * (e₁ / e₃)) (t⁻¹ ^ 3 * e₃⁻¹)).eval
                ((Ideal.absNorm v.asIdeal : ℂ) ^ (-(1 - s))))⁻¹ * P s) ∧
    (1 ≤ a →
      ∃ (P : ℂ → ℂ) (σ₀ σ₁ : ℝ),
        (∃ (Q : Polynomial ℂ) (m : ℕ), ∀ s : ℂ,
          P s = Q.eval ((Ideal.absNorm v.asIdeal : ℂ) ^ (-s)) * (Ideal.absNorm v.asIdeal : ℂ) ^ ((m : ℂ) * s)) ∧
        IsLocalZeta30ConvergentAbove v (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ v)))
          W χ g σ₀ ∧
        (∀ s : ℂ, σ₀ < s.re →
          localZeta30 v (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ v))) W χ s g =
            P s) ∧
        IsLocalZeta31ConvergentAbove v (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ v)))
          (selfDualHaarAt ℚ v) (dualWhittakerFn3 W) χ⁻¹ (weylPrime3 * transposeInv3 g) σ₁ ∧
        ∀ s : ℂ, σ₁ < (1 - s).re →
          ((selfDualHaarAt ℚ v).real (v.adicCompletionIntegers ℚ : Set (v.adicCompletion ℚ)) : ℂ)⁻¹ *
              localZetaDual31 v (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ v)))
                (selfDualHaarAt ℚ v) W χ (1 - s) g =
            (e₃ ^ a * LanglandsTunnell.TateLocal.stdRootNumberAt ℚ v χ ^ 3 *
                (Ideal.absNorm v.asIdeal : ℂ) ^ (((3 * a : ℕ) : ℂ) * (1 / 2 - s))) * P s) := by
  exact localFunctionalEquation_of_sphericalData v W e₁ e₂ e₃ hW hψ χ a hχa hu t ht g
end
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_laurent_localZeta_eq_gl3LFactorPoly_of_sphericalData.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_exists_laurent_localZeta_eq_gl3LFactorPoly_of_sphericalData.LanglandsTunnell.CubicInduction"

end S_LanglandsTunnell_CubicInduction_exists_laurent_localZeta_eq_gl3LFactorPoly_of_sphericalData
end P2MW
export P2MW.S_LanglandsTunnell_CubicInduction_exists_laurent_localZeta_eq_gl3LFactorPoly_of_sphericalData (solution)
