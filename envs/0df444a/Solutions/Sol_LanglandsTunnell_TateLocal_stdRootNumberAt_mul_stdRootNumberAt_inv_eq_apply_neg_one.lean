-- Prove2me | solution 1 for LanglandsTunnell.TateLocal.stdRootNumberAt_mul_stdRootNumberAt_inv_eq_apply_neg_one
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.670037+00:00
-- url     : https://prove2.me/submissions/acccdeab-7f01-5f8d-805f-ccd193ca69d1

import Definitions.Def_LanglandsTunnell_StandardLocalConstantsAt
import Theorems.Thm_LanglandsTunnell_TateLocal_localZeta_tateFourier_stdTestFunAt
import Theorems.Thm_LanglandsTunnell_TateLocal_localZeta_stdTestFunAt_eq_real_image_higherUnitsAt
import Theorems.Thm_LanglandsTunnell_TateLocal_selfDualHaarAt_real_image_higherUnitsAt
import Theorems.Thm_LanglandsTunnell_TateLocal_setIntegral_addChar_mul_charExt_mul_setIntegral_inv_mul_pow_eq
import Theorems.Thm_LanglandsTunnell_TateLocal_forall_eq_one_and_exists_ne_one_of_addCharLevel
import Theorems.Thm_LanglandsTunnell_TateLocal_psiLocal_eq_one_of_mem_integers
import Theorems.Thm_LanglandsTunnell_TateLocal_psiLocal_ne_one
import Theorems.Thm_LanglandsTunnell_TateLocal_selfDualHaarAt_real_integers_mul_real_setOf_valued_le_exp_addCharLevel
import Theorems.Thm_LanglandsTunnell_TateLocal_measureReal_setOf_valued_le_exp
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LanglandsTunnell_TateLocal_stdRootNumberAt_mul_stdRootNumberAt_inv_eq_apply_neg_one
p2m_attr_erase "instance" "instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions instCountableOfNumberField_definitions IsDedekindDomain.HeightOneSpectrum.Extension.instAlgebraSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnder IsDedekindDomain.HeightOneSpectrum.Extension.instAlgebraSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnder_1 IsDedekindDomain.HeightOneSpectrum.instMulActionHomClassAlgHomTensorProductAdicCompletionForallValEqUnder_definitions IsDedekindDomain.HeightOneSpectrum.Extension.instAlgebraAdicCompletionValEqUnder IsDedekindDomain.HeightOneSpectrum.adicCompletion.instFiniteForallValEqUnderOfFiniteDimensional_definitions IsDedekindDomain.HeightOneSpectrum.instIsBiscalarSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersTensorProductCoeAlgHomTensorAdicCompletionIntegersTo IsDedekindDomain.HeightOneSpectrum.Extension.instContinuousSMulAdicCompletionValEqUnder IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsModuleTopology IsDedekindDomain.HeightOneSpectrum.Extension.instFiniteSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnderOfFiniteDimensional IsDedekindDomain.HeightOneSpectrum.adicCompletion.instFiniteValEqUnderOfFiniteDimensional_definitions instIsBiscalarTensorProductCoeAlgHomBaseChange_of_algebraMap IsDedekindDomain.HeightOneSpectrum.instIsScalarTowerSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnder_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsModuleTopologyPi Submodule.instIsTopologicalModuleSubtypeMem Pi.instTopologicalModule IsTopologicalModule.toContinuousSMul IsTopologicalModule.toContinuousAdd instFunLike SemialgHomClass.toSemilinearMapClass instCoeTCSemialgHom SemialgHomClass.toRingHomClass SemialgHomClass.instSemialgHom"
p2m_attr_erase "simp" "SemialgHom.baseChange_of_algebraMap_tmul_left SemialgHom.baseChangeRightOfAlgebraMap_apply Pi.semialgHomPi_apply Pi.semialgHom_apply Module.Basis.rightBaseChange_apply LinearEquiv.coe_mulLeft LinearEquiv.coe_mulRight WithVal.semialgebraMap_toFun_ofVal Module.Basis.rightBaseChange_repr IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers.tensorCoe_tmul IsDedekindDomain.HeightOneSpectrum.tensorAdicCompletionIntegersTo_tmul SemialgHom.baseChangeRightOfAlgebraMap_coe IsDedekindDomain.HeightOneSpectrum.adicCompletion.integerBaseChangeLinearEquiv_tmul_apply SemialgHom.baseChange_of_algebraMap_tmul_right IsLocalization.map_moduleTensorEquiv_symm_tmul IsLocalization.leftModuleTensorEquiv_apply IsLocalization.moduleLid_symm_apply IsLocalization.leftModuleTensorEquiv_symm_apply IsLocalization.map_moduleTensorEquiv_tmul IsModuleTopology.continuousLinearEquiv_apply AlgEquiv.extendScalars_symm_apply IsModuleTopology.Module.Basis.equivFun_homeo_symm_apply IsModuleTopology.Module.Basis.equivFun_homeo_apply IsModuleTopology.continuousAlgEquivOfIsBiscalar_apply AlgEquiv.extendScalars_apply IsModuleTopology.continuousLinearEquiv_symm_apply SemialgHom.restrictScalars_toFun SemialgHom.mk.sizeOf_spec SemialgHom.mk.injEq SemialgHom.coe_coe coe_mk TensorProduct.RightActions.smul_def TensorProduct.RightActions.Module.TensorProduct.comm_symm_apply_tmul TensorProduct.RightActions.LinearMap.baseChange_id TensorProduct.RightActions.algebraMap_eval TensorProduct.RightActions.Module.TensorProduct.comm_apply_tmul TensorProduct.RightActions.Algebra.TensorProduct.comm_symm_apply_tmul TensorProduct.RightActions.Algebra.TensorProduct.comm_apply_tmul"

set_option autoImplicit false

open NumberField NumberField.StandardAddChar NumberField.AdelicLevel IsDedekindDomain
open LanglandsTunnell.TateLocal MeasureTheory

section Helpers

variable (K : Type) [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))

private theorem one_lt_absNorm_asIdeal : 1 < Ideal.absNorm v.asIdeal := by
  have h0 : Ideal.absNorm v.asIdeal ≠ 0 := by
    rw [Ne, Ideal.absNorm_eq_zero_iff]
    exact v.ne_bot
  have h1 : Ideal.absNorm v.asIdeal ≠ 1 := by
    rw [Ne, Ideal.absNorm_eq_one_iff]
    exact v.isPrime.ne_top
  omega

private theorem isAddHaarMeasure_selfDualHaarAt :
    letI := localBorel K v
    (selfDualHaarAt K v).IsAddHaarMeasure := by
  letI := localBorel K v
  haveI : BorelSpace (v.adicCompletion K) := ⟨rfl⟩
  have hN : (0 : NNReal) < (Ideal.absNorm v.asIdeal : NNReal) := by
    exact_mod_cast Nat.zero_lt_one.trans (one_lt_absNorm_asIdeal K v)
  unfold selfDualHaarAt
  exact Measure.IsAddHaarMeasure.nnreal_smul _ (NNReal.rpow_pos hN).ne'

private theorem not_hasConductorExponentAt_zero_of_one_le {χ : (v.adicCompletion K)ˣ →* ℂˣ} {a : ℕ} (ha : 1 ≤ a)
    (hχ : HasConductorExponentAt K v χ a) : ¬ HasConductorExponentAt K v χ 0 := fun h0 => by
  have := hasConductorExponentAt_unique K v hχ h0
  omega

private theorem hasConductorExponentAt_inv_aux {χ : (v.adicCompletion K)ˣ →* ℂˣ} {a : ℕ}
    (hχ : HasConductorExponentAt K v χ a) : HasConductorExponentAt K v χ⁻¹ a := by
  refine ⟨fun u hu => ?_, fun c hc => ?_⟩
  · rw [MonoidHom.inv_apply, hχ.1 u hu, inv_one]
  · obtain ⟨u, hu, hne⟩ := hχ.2 c hc
    exact ⟨u, hu, by rwa [MonoidHom.inv_apply, ne_eq, inv_eq_one]⟩

private noncomputable def shellGauss (ξ : (v.adicCompletion K)ˣ →* ℂˣ) (a : ℕ) : ℂ := by
  letI := localBorel K v
  exact ∫ u in {u : v.adicCompletion K | Valued.v u = 1},
    psiLocal K v
        (((uniformizerUnit K v ^ (-(addCharLevel (psiLocal K v) + a : ℤ)) : (v.adicCompletion K)ˣ) :
            v.adicCompletion K) * u)
      * charExt ξ u ∂(selfDualHaarAt K v)

private noncomputable def halfScale (a : ℕ) : ℂ :=
  ((((Ideal.absNorm v.asIdeal : ℝ) ^ (addCharLevel (psiLocal K v) + a : ℤ) : ℝ) : ℂ)) ^ (1 - (1 / 2 : ℂ))

private theorem halfScale_mul_self (a : ℕ) :
    halfScale K v a * halfScale K v a = (Ideal.absNorm v.asIdeal : ℂ) ^ (addCharLevel (psiLocal K v) + a : ℤ) := by
  have hN : (0 : ℝ) < (Ideal.absNorm v.asIdeal : ℝ) := by
    exact_mod_cast (Nat.zero_lt_one.trans (one_lt_absNorm_asIdeal K v))
  have hP : ((((Ideal.absNorm v.asIdeal : ℝ) ^ (addCharLevel (psiLocal K v) + a : ℤ) : ℝ) : ℂ)) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (zpow_ne_zero _ hN.ne')
  unfold halfScale
  rw [← Complex.cpow_add _ _ hP]
  norm_num

private theorem norm_inv_apply_uniformizerUnit_mul_cpow_lt_one {χ : (v.adicCompletion K)ˣ →* ℂˣ}
    (hu : ‖(χ (uniformizerUnit K v) : ℂ)‖ = 1) :
    ‖(χ⁻¹ (uniformizerUnit K v) : ℂ) * (Ideal.absNorm v.asIdeal : ℂ) ^ (-(1 - (1 / 2 : ℂ)))‖ < 1 := by
  have hNpos : 0 < Ideal.absNorm v.asIdeal := Nat.zero_lt_one.trans (one_lt_absNorm_asIdeal K v)
  have h1 : ‖(χ⁻¹ (uniformizerUnit K v) : ℂ)‖ = 1 := by
    rw [MonoidHom.inv_apply, Units.val_inv_eq_inv_val, norm_inv, hu, inv_one]
  rw [norm_mul, h1, one_mul, Complex.norm_natCast_cpow_of_pos hNpos]
  have hre : (-(1 - (1 / 2 : ℂ))).re = -(1 / 2 : ℝ) := by norm_num
  rw [hre]
  have hN1 : (1 : ℝ) < (Ideal.absNorm v.asIdeal : ℝ) := by exact_mod_cast one_lt_absNorm_asIdeal K v
  exact Real.rpow_lt_one_of_one_lt_of_neg hN1 (by norm_num)

private theorem stdRootNumberAt_eq_of_hasConductorExponentAt {χ : (v.adicCompletion K)ˣ →* ℂˣ} {a : ℕ} (ha : 1 ≤ a)
    (hχ : HasConductorExponentAt K v χ a) (hu : ‖(χ (uniformizerUnit K v) : ℂ)‖ = 1) :
    stdRootNumberAt K v χ
      = (χ (uniformizerUnit K v) : ℂ) ^ (addCharLevel (psiLocal K v) + a : ℤ) * halfScale K v a
          * shellGauss K v χ⁻¹ a := by
  letI := localBorel K v
  have hA := localZeta_stdTestFunAt_eq_real_image_higherUnitsAt K v χ a ha hχ (1 / 2)
  have hB := localZeta_tateFourier_stdTestFunAt K v χ a ha hχ (1 / 2)
    (norm_inv_apply_uniformizerUnit_mul_cpow_lt_one K v hu)
  have hvol := selfDualHaarAt_real_image_higherUnitsAt K v a ha
  try dsimp only at hA
  try dsimp only at hB
  try dsimp only at hvol
  have hvol0 : ((((selfDualHaarAt K v).real
      (((↑) : (v.adicCompletion K)ˣ → v.adicCompletion K) '' higherUnitsAt K v a) : ℝ)) : ℂ) ≠ 0 := by
    rw [hvol]
    have hN : (0 : ℝ) < (Ideal.absNorm v.asIdeal : ℝ) := by
      exact_mod_cast (Nat.zero_lt_one.trans (one_lt_absNorm_asIdeal K v))
    exact_mod_cast (mul_pos (zpow_pos hN _) (Real.rpow_pos_of_pos hN _)).ne'
  rw [stdRootNumberAt_def]
  unfold stdEpsilonAt
  rw [localEpsilonAt_of_not_hasConductorExponentAt_zero K v _ _ _
    (not_hasConductorExponentAt_zero_of_one_le K v ha hχ), localGammaAt]
  show _ / localZeta (selfDualHaarAt K v) (stdTestFunAt K v χ) χ (1 / 2) = _
  rw [hB, hA]
  unfold shellGauss halfScale
  field_simp

end Helpers

theorem solution
    (K : Type) [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))
    (χ : (v.adicCompletion K)ˣ →* ℂˣ) (a : ℕ) (ha : 1 ≤ a) (hχ : HasConductorExponentAt K v χ a)
    (hu : ‖((χ (uniformizerUnit K v) : ℂˣ) : ℂ)‖ = 1) :
    stdRootNumberAt K v χ * stdRootNumberAt K v χ⁻¹ = ((χ (-1 : (v.adicCompletion K)ˣ) : ℂˣ) : ℂ) := by
  letI := localBorel K v
  haveI : BorelSpace (v.adicCompletion K) := ⟨rfl⟩
  haveI : (selfDualHaarAt K v).IsAddHaarMeasure := isAddHaarMeasure_selfDualHaarAt K v
  have hu' : ‖(χ⁻¹ (uniformizerUnit K v) : ℂ)‖ = 1 := by
    rw [MonoidHom.inv_apply, Units.val_inv_eq_inv_val, norm_inv, hu, inv_one]
  have hχ' := hasConductorExponentAt_inv_aux K v hχ

  have hii : shellGauss K v χ⁻¹⁻¹ a = shellGauss K v χ a := by
    rw [show χ⁻¹⁻¹ = χ from inv_inv χ]
  rw [stdRootNumberAt_eq_of_hasConductorExponentAt K v ha hχ hu,
    stdRootNumberAt_eq_of_hasConductorExponentAt K v ha hχ' hu', hii]

  have hlev := forall_eq_one_and_exists_ne_one_of_addCharLevel K v (psiLocal K v)
    ⟨0, fun x hx => psiLocal_eq_one_of_mem_integers K v x (by
      rw [HeightOneSpectrum.mem_adicCompletionIntegers]; simpa using hx)⟩ (psiLocal_ne_one K v)

  have hc : Valued.v ((uniformizerUnit K v ^ (-(addCharLevel (psiLocal K v) + a : ℤ)) : (v.adicCompletion K)ˣ) :
      v.adicCompletion K) = WithZero.exp (addCharLevel (psiLocal K v) + a) := by
    rw [Units.val_zpow_eq_zpow_val, map_zpow₀, valued_uniformizerUnit K v, ← WithZero.exp_zsmul]
    congr 1
    simp
  have hG := setIntegral_addChar_mul_charExt_mul_setIntegral_inv_mul_pow_eq K v (selfDualHaarAt K v) (psiLocal K v)
    (addCharLevel (psiLocal K v)) hlev.1 hlev.2 χ a ha hχ _ hc

  have hnorm := selfDualHaarAt_real_integers_mul_real_setOf_valued_le_exp_addCharLevel K v
  rw [measureReal_setOf_valued_le_exp K v (selfDualHaarAt K v)] at hnorm

  have hm1 : charExt χ (-1 : v.adicCompletion K) = (χ (-1) : ℂ) := by
    rw [show (-1 : v.adicCompletion K) = ((-1 : (v.adicCompletion K)ˣ) : v.adicCompletion K) by simp,
      charExt_coe_units]
  rw [hm1] at hG

  have hG' : shellGauss K v χ a * shellGauss K v χ⁻¹ a * (Ideal.absNorm v.asIdeal : ℂ) ^ a
      = (χ (-1) : ℂ)
        * (((selfDualHaarAt K v).real (v.adicCompletionIntegers K : Set (v.adicCompletion K)) : ℝ) : ℂ) ^ 2 := hG
  have hN0 : (Ideal.absNorm v.asIdeal : ℂ) ≠ 0 := by
    exact_mod_cast (Nat.zero_lt_one.trans (one_lt_absNorm_asIdeal K v)).ne'
  have hsq : halfScale K v a * halfScale K v a
      = (Ideal.absNorm v.asIdeal : ℂ) ^ (addCharLevel (psiLocal K v) : ℤ) * (Ideal.absNorm v.asIdeal : ℂ) ^ a := by
    rw [halfScale_mul_self K v a, zpow_add₀ hN0, zpow_natCast]
  have hnormC : (Ideal.absNorm v.asIdeal : ℂ) ^ (addCharLevel (psiLocal K v) : ℤ)
      * (((selfDualHaarAt K v).real (v.adicCompletionIntegers K : Set (v.adicCompletion K)) : ℝ) : ℂ) ^ 2 = 1 := by
    have h' : ((Ideal.absNorm v.asIdeal : ℝ) ^ (addCharLevel (psiLocal K v) : ℤ)
        * (selfDualHaarAt K v).real (v.adicCompletionIntegers K : Set (v.adicCompletion K)) ^ 2 : ℝ) = 1 := by
      rw [← hnorm]
      ring
    have h'' : (((Ideal.absNorm v.asIdeal : ℝ) ^ (addCharLevel (psiLocal K v) : ℤ)
        * (selfDualHaarAt K v).real (v.adicCompletionIntegers K : Set (v.adicCompletion K)) ^ 2 : ℝ) : ℂ) = 1 := by
      rw [h', Complex.ofReal_one]
    rw [Complex.ofReal_mul, Complex.ofReal_zpow, Complex.ofReal_pow, Complex.ofReal_natCast] at h''
    exact h''
  have hϖ : (χ⁻¹ (uniformizerUnit K v) : ℂ) = (χ (uniformizerUnit K v) : ℂ)⁻¹ := by
    rw [MonoidHom.inv_apply, Units.val_inv_eq_inv_val]
  have hχϖ : (χ (uniformizerUnit K v) : ℂ) ≠ 0 := Units.ne_zero _
  rw [hϖ, inv_zpow]
  have hcancel : (χ (uniformizerUnit K v) : ℂ) ^ (addCharLevel (psiLocal K v) + a : ℤ)
      * ((χ (uniformizerUnit K v) : ℂ) ^ (addCharLevel (psiLocal K v) + a : ℤ))⁻¹ = 1 :=
    mul_inv_cancel₀ (zpow_ne_zero _ hχϖ)
  linear_combination
    (shellGauss K v χ⁻¹ a * shellGauss K v χ a * (halfScale K v a * halfScale K v a)) * hcancel
      + (shellGauss K v χ⁻¹ a * shellGauss K v χ a) * hsq
      + (Ideal.absNorm v.asIdeal : ℂ) ^ (addCharLevel (psiLocal K v) : ℤ) * hG'
      + (χ (-1) : ℂ) * hnormC

end S_LanglandsTunnell_TateLocal_stdRootNumberAt_mul_stdRootNumberAt_inv_eq_apply_neg_one
end P2MW
export P2MW.S_LanglandsTunnell_TateLocal_stdRootNumberAt_mul_stdRootNumberAt_inv_eq_apply_neg_one (solution)
