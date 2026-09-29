-- Prove2me | solution 1 for NumberField.TateGlobal.exists_zeroFree_norm_deriv_le_and_inv_le_eulerProduct_continuation_of_archLocalChar_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.93214+00:00
-- url     : https://prove2.me/submissions/814e6afa-cab8-5ac9-a518-62f53cf50834

import Mathlib
import Definitions.Def_NumberField_TateGlobalZeta
import Definitions.Def_NumberField_NormPowChar
import Definitions.Def_AutomorphicForm_HeckeEigenfunction
import Definitions.Def_AutomorphicForm_EtaFamily
import Definitions.Def_HeckeCharacter_FiniteOrder
import Theorems.Thm_Complex_norm_deriv_le_mul_norm_and_exp_neg_le_norm_of_forall_ne_zero_of_norm_le_exp
import Theorems.Thm_HeckeCharacter_exists_ne_bot_forall_admitsModulus_of_isUnramifiedCharAt_of_localChar_eq
import Theorems.Thm_NumberField_TateGlobal_exists_pos_forall_sub_one_mul_partialDedekindZeta_continuation_ne_zero_of_one_sub_div_log_le_re
import Theorems.Thm_NumberField_TateGlobal_exists_pos_forall_partialEulerProduct_continuation_ne_zero_of_one_sub_div_log_le_re_of_admitsModulus
import Theorems.Thm_NumberField_TateGlobal_exists_forall_norm_partialEulerProduct_continuation_le_rpow_of_re_mem_Icc_of_admitsModulus
import Theorems.Thm_NumberField_TateGlobal_exists_forall_norm_sub_one_mul_partialDedekindZeta_continuation_le_rpow_of_re_mem_Icc
import Theorems.Thm_EulerProduct_differentiableAt_and_ne_zero_and_hasSum_log_mul_div_neg_deriv_tprod_div
import Theorems.Thm_NumberField_TateGlobal_exists_eq_normPowChar_of_forall_mem_normOneIdeles
import Theorems.Thm_NumberField_TateGlobal_ite_isUnramifiedCharAt_normPowChar_apply_uniformizerIdele_eq_absNorm_cpow_neg
import Theorems.Thm_NumberField_TateGlobal_ideleNorm_eq_prod_norm_infinitePlace_pow_mult_of_snd_eq_one
import Theorems.Thm_NumberField_summable_heightOneSpectrum_absNorm_rpow_neg_of_one_lt
import Theorems.Thm_NumberField_exists_differentiable_eq_sub_one_mul_dedekindZeta_and_apply_neg_two_mul_add_one_eq_zero
import Theorems.Thm_NumberField_hasProd_inv_one_sub_absNorm_cpow_neg_dedekindZeta
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_NumberField_TateGlobal_exists_zeroFree_norm_deriv_le_and_inv_le_eulerProduct_continuation_of_archLocalChar_eq
p2m_attr_erase "instance" "instCountableOfNumberField_definitions instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions IsDedekindDomain.HeightOneSpectrum.Extension.instAlgebraSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnder IsDedekindDomain.HeightOneSpectrum.Extension.instAlgebraSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnder_1 IsDedekindDomain.HeightOneSpectrum.instMulActionHomClassAlgHomTensorProductAdicCompletionForallValEqUnder_definitions IsDedekindDomain.HeightOneSpectrum.Extension.instAlgebraAdicCompletionValEqUnder IsDedekindDomain.HeightOneSpectrum.adicCompletion.instFiniteForallValEqUnderOfFiniteDimensional_definitions IsDedekindDomain.HeightOneSpectrum.instIsBiscalarSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersTensorProductCoeAlgHomTensorAdicCompletionIntegersTo IsDedekindDomain.HeightOneSpectrum.Extension.instContinuousSMulAdicCompletionValEqUnder IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsModuleTopology IsDedekindDomain.HeightOneSpectrum.Extension.instFiniteSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnderOfFiniteDimensional IsDedekindDomain.HeightOneSpectrum.adicCompletion.instFiniteValEqUnderOfFiniteDimensional_definitions instIsBiscalarTensorProductCoeAlgHomBaseChange_of_algebraMap IsDedekindDomain.HeightOneSpectrum.instIsScalarTowerSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnder_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsModuleTopologyPi Submodule.instIsTopologicalModuleSubtypeMem Pi.instTopologicalModule IsTopologicalModule.toContinuousSMul IsTopologicalModule.toContinuousAdd instFunLike SemialgHomClass.toSemilinearMapClass instCoeTCSemialgHom SemialgHomClass.toRingHomClass SemialgHomClass.instSemialgHom Deep.NTSupply.instNormalRayClassSubgroup LanglandsTunnell.P2.Artin.ArtinPairCore.instNFN LanglandsTunnell.P2.Artin.ArtinFieldCore.instSTENΘ LanglandsTunnell.P2.Artin.ArtinFieldCore.instSTKLN LanglandsTunnell.P2.Artin.ArtinPairCore.instFE"
p2m_attr_erase "instance" "LanglandsTunnell.P2.Artin.ArtinPairCore.instAKE LanglandsTunnell.P2.Artin.ArtinFieldCore.instAKN LanglandsTunnell.P2.Artin.ArtinPairCore.instCN LanglandsTunnell.P2.Artin.ArtinFieldCore.instFΘ LanglandsTunnell.P2.Artin.ArtinFieldCore.instAEΘ LanglandsTunnell.P2.Artin.ArtinFieldCore.instNFΘ LanglandsTunnell.P2.Artin.ArtinPairCore.instAjE LanglandsTunnell.P2.Artin.ArtinFieldCore.instGEN LanglandsTunnell.P2.Artin.ArtinFieldCore.instCΘ LanglandsTunnell.P2.Artin.ArtinFieldCore.instFE LanglandsTunnell.P2.Artin.ArtinFieldCore.instNZq LanglandsTunnell.P2.Artin.ArtinPairCore.instAEN LanglandsTunnell.P2.Artin.ArtinPairCore.instSTKEN LanglandsTunnell.P2.Artin.ArtinPairCore.instSTKjE LanglandsTunnell.P2.Artin.ArtinFieldCore.instCN LanglandsTunnell.P2.Artin.ArtinFieldCore.instANΘ LanglandsTunnell.P2.Artin.ArtinPairCore.instSTKLN LanglandsTunnell.P2.Artin.ArtinPairCore.instGEN LanglandsTunnell.P2.Artin.ArtinPairCore.instAiE LanglandsTunnell.P2.Artin.instCommGroupIp LanglandsTunnell.P2.Artin.ArtinFieldCore.instNFE LanglandsTunnell.P2.Artin.ArtinFieldCore.instAEN LanglandsTunnell.P2.Artin.ArtinPairCore.instFN LanglandsTunnell.P2.Artin.ArtinPairCore.instALN LanglandsTunnell.P2.Artin.ArtinFieldCore.instFN LanglandsTunnell.P2.Artin.ArtinPairCore.instAKN LanglandsTunnell.P2.Artin.ArtinFieldCore.instSTKEN LanglandsTunnell.P2.Artin.ArtinFieldCore.instGEΘ LanglandsTunnell.P2.Artin.ArtinPairCore.instSTKiE LanglandsTunnell.P2.Artin.ArtinFieldCore.instNFN LanglandsTunnell.P2.Artin.ArtinFieldCore.instAKE LanglandsTunnell.P2.Artin.ArtinPairCore.instNFE LanglandsTunnell.P2.Artin.ArtinFieldCore.instALN LanglandsTunnell.P2.Artin.primeAbove_liesOver LanglandsTunnell.P2.Artin.isGaloisGroup_ringOfIntegers LanglandsTunnell.P2.Artin.primeAbove_isMaximal LanglandsTunnell.P2.Artin.primeAbove_finite"
p2m_attr_erase "simp" "NumberField.StandardAddChar.ratArchLine_apply NumberField.StandardAddChar.AdelicTraceData.mk.sizeOf_spec NumberField.StandardAddChar.AdelicTraceData.mk.injEq AutomorphicForm.whittakerCoefficient_zero NumberField.AdelicTrace.traceDiag_apply NumberField.AdelicTrace.diag_apply LanglandsTunnell.TateLocal.conductorExponentAt_one LanglandsTunnell.TateLocal.charExt_coe_units LanglandsTunnell.TateLocal.modulus_one LanglandsTunnell.TateLocal.modulus_zero LanglandsTunnell.TateLocal.modulus_coe_units LanglandsTunnell.TateLocal.charExt_zero LanglandsTunnell.signEpsilon_one LanglandsTunnell.RealArchParam.epsilonFactor_principal LanglandsTunnell.RealArchParam.epsilonFactor_discrete LanglandsTunnell.signEpsilon_zero LanglandsTunnell.signShift_zero LanglandsTunnell.RealArchParam.twist_zero LanglandsTunnell.RealArchParam.discrete.sizeOf_spec LanglandsTunnell.RealArchParam.principal.injEq LanglandsTunnell.ComplexArchParam.dual_dual LanglandsTunnell.ComplexArchParam.mk.sizeOf_spec LanglandsTunnell.RealArchParam.dual_dual LanglandsTunnell.RealArchParam.discrete.injEq LanglandsTunnell.ComplexArchParam.twist_zero LanglandsTunnell.RealArchParam.principal.sizeOf_spec LanglandsTunnell.signShift_one LanglandsTunnell.ComplexArchParam.mk.injEq LanglandsTunnell.LDatum.mk.sizeOf_spec LanglandsTunnell.LDatum.badFactor_zero LanglandsTunnell.LDatum.mk.injEq LanglandsTunnell.ArchPlace.complexTestFun_zero_apply LanglandsTunnell.ArchPlace.norm_anglePhase LanglandsTunnell.ArchPlace.realTestFun_zero_apply UnramifiedWhittaker.ProductMeasureData.mk.injEq UnramifiedWhittaker.ProductMeasureData.mk.sizeOf_spec AdelicDock.coe_finEmbed AdelicDock.splice_apply_self AdelicDock.coe_localEmbed NumberField.AdeleRing.val_finiteUnitsComponent"
p2m_attr_erase "simp" "IsDedekindDomain.FiniteAdeleRing.val_unitsComponent NumberField.AdeleRing.val_finitePartUnits NumberField.AdeleRing.val_infiniteUnitsComponent SemialgHom.baseChange_of_algebraMap_tmul_left SemialgHom.baseChangeRightOfAlgebraMap_apply Pi.semialgHomPi_apply Pi.semialgHom_apply Module.Basis.rightBaseChange_apply LinearEquiv.coe_mulLeft LinearEquiv.coe_mulRight WithVal.semialgebraMap_toFun_ofVal Module.Basis.rightBaseChange_repr IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers.tensorCoe_tmul IsDedekindDomain.HeightOneSpectrum.tensorAdicCompletionIntegersTo_tmul SemialgHom.baseChangeRightOfAlgebraMap_coe IsDedekindDomain.HeightOneSpectrum.adicCompletion.integerBaseChangeLinearEquiv_tmul_apply SemialgHom.baseChange_of_algebraMap_tmul_right IsLocalization.map_moduleTensorEquiv_symm_tmul IsLocalization.leftModuleTensorEquiv_apply IsLocalization.moduleLid_symm_apply IsLocalization.leftModuleTensorEquiv_symm_apply IsLocalization.map_moduleTensorEquiv_tmul IsModuleTopology.continuousLinearEquiv_apply AlgEquiv.extendScalars_symm_apply IsModuleTopology.Module.Basis.equivFun_homeo_symm_apply IsModuleTopology.Module.Basis.equivFun_homeo_apply IsModuleTopology.continuousAlgEquivOfIsBiscalar_apply AlgEquiv.extendScalars_apply IsModuleTopology.continuousLinearEquiv_symm_apply SemialgHom.restrictScalars_toFun SemialgHom.mk.sizeOf_spec SemialgHom.mk.injEq SemialgHom.coe_coe coe_mk TensorProduct.RightActions.smul_def TensorProduct.RightActions.Module.TensorProduct.comm_symm_apply_tmul TensorProduct.RightActions.LinearMap.baseChange_id TensorProduct.RightActions.algebraMap_eval TensorProduct.RightActions.Module.TensorProduct.comm_apply_tmul TensorProduct.RightActions.Algebra.TensorProduct.comm_symm_apply_tmul"
p2m_attr_erase "simp" "TensorProduct.RightActions.Algebra.TensorProduct.comm_apply_tmul M4aHerbrand.IdeleGaloisDescent.mk.sizeOf_spec M4aHerbrand.IdeleGaloisDescent.mk.injEq LanglandsTunnell.P2.Artin.ArtinPairCore.mk.sizeOf_spec LanglandsTunnell.P2.Artin.ArtinFieldCore.mk.sizeOf_spec LanglandsTunnell.P2.Artin.ArtinFieldCore.mk.injEq LanglandsTunnell.P2.Artin.ArtinPairCore.mk.injEq"

set_option autoImplicit false

noncomputable section

open NumberField IsDedekindDomain AutomorphicForm NumberField.TateGlobal NumberField.InfinitePlace
open Complex Filter Set
open scoped Topology

namespace R4ZFT

theorem two_le_absNorm {K : Type} [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K)) :
    2 ≤ Ideal.absNorm v.asIdeal := by
  have h0 : Ideal.absNorm v.asIdeal ≠ 0 := by
    rw [Ne, Ideal.absNorm_eq_zero_iff]; exact v.ne_bot
  have h1 : Ideal.absNorm v.asIdeal ≠ 1 := by
    rw [Ne, Ideal.absNorm_eq_one_iff]; exact v.isPrime.ne_top
  omega

theorem norm_coeff_le_one {K : Type} [Field K] [NumberField K] {χ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ}
    (hu : IsUnitaryChar (𝓞 K) K χ)
    (v : HeightOneSpectrum (𝓞 K)) [Decidable (IsUnramifiedCharAt χ v)] :
    ‖(if IsUnramifiedCharAt χ v then ((χ (uniformizerIdele K v) : ℂˣ) : ℂ) else 0)‖ ≤ 1 := by
  split_ifs
  · exact (hu _).le
  · simp

theorem re_ofReal_add_mul_I (σ t : ℝ) : ((σ : ℂ) + t * I).re = σ := by simp

theorem im_ofReal_add_mul_I (σ t : ℝ) : ((σ : ℂ) + t * I).im = t := by simp

theorem continuous_of_continuous_coe {K : Type} [Field K] [NumberField K]
    (χ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ) (h : Continuous fun z : (AdeleRing (𝓞 K) K)ˣ => ((χ z : ℂˣ) : ℂ)) :
    Continuous χ := by
  refine Units.continuous_iff.mpr ⟨h, ?_⟩
  have heq : (fun z : (AdeleRing (𝓞 K) K)ˣ => (((χ z)⁻¹ : ℂˣ) : ℂ)) =
      fun z : (AdeleRing (𝓞 K) K)ˣ => ((χ z⁻¹ : ℂˣ) : ℂ) := by
    funext z; rw [map_inv]
  rw [heq]
  exact h.comp continuous_inv

section eulerAbstract

theorem norm_tprod_inv_one_sub_eq_exp {ι : Type} (a : ι → ℂ) (ha : Summable fun i => ‖a i‖)
    (ha1 : ∀ i, ‖a i‖ < 1) :
    ‖∏' i, (1 - a i)⁻¹‖ = Real.exp (∑' i, (-log (1 - a i)).re) := by
  have hne : ∀ i, 1 - a i ≠ 0 := fun i h => by
    have : a i = 1 := (sub_eq_zero.mp h).symm
    have := ha1 i
    rw [‹a i = 1›, norm_one] at this
    exact lt_irrefl _ this
  have hsum : Summable fun i => -log (1 - a i) := ha.of_norm.clog_one_sub.neg
  have H := hsum.hasSum.cexp.tprod_eq
  have hcongr : (cexp ∘ fun i => -log (1 - a i)) = fun i => (1 - a i)⁻¹ := by
    funext i
    simp only [Function.comp_apply, exp_neg, exp_log (hne i)]
  rw [hcongr] at H
  rw [H, norm_exp, re_tsum hsum]

theorem norm_neg_log_one_sub_le {a : ℂ} (ha : ‖a‖ ≤ 1 / 2) : ‖-log (1 - a)‖ ≤ 2 * ‖a‖ := by
  rw [norm_neg, sub_eq_add_neg]
  have h := Complex.norm_log_one_add_half_le_self (z := -a) (by rwa [norm_neg])
  rw [norm_neg] at h
  linarith [norm_nonneg a]

theorem norm_natCast_cpow_neg (n : ℕ) (hn : 0 < n) (s : ℂ) :
    ‖(n : ℂ) ^ (-s)‖ = (n : ℝ) ^ (-s.re) := by
  rw [norm_natCast_cpow_of_pos hn]; simp

theorem rpow_neg_le_half {N : ℕ} (hN : 2 ≤ N) {σ : ℝ} (hσ : 1 ≤ σ) : ((N : ℕ) : ℝ) ^ (-σ) ≤ 1 / 2 := by
  have h2 : (2 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  rw [Real.rpow_neg (Nat.cast_nonneg _)]
  have h1 : (2 : ℝ) ≤ ((N : ℕ) : ℝ) ^ σ := by
    calc (2 : ℝ) = 2 ^ (1 : ℝ) := (Real.rpow_one 2).symm
      _ ≤ 2 ^ σ := Real.rpow_le_rpow_of_exponent_le (by norm_num) hσ
      _ ≤ ((N : ℕ) : ℝ) ^ σ := Real.rpow_le_rpow (by norm_num) h2 (by linarith)
  rw [one_div]
  exact inv_anti₀ (by norm_num) h1

theorem exp_neg_le_norm_tprod {ι : Type} (N : ι → ℕ) (hN : ∀ i, 2 ≤ N i) (c : ι → ℂ) (hc : ∀ i, ‖c i‖ ≤ 1)
    (s : ℂ) (hs : 1 ≤ s.re) (hsum : Summable fun i => ((N i : ℕ) : ℝ) ^ (-s.re)) :
    Real.exp (-(2 * ∑' i, ((N i : ℕ) : ℝ) ^ (-s.re))) ≤ ‖∏' i, (1 - c i * ((N i : ℕ) : ℂ) ^ (-s))⁻¹‖ := by
  have hN0 : ∀ i, 0 < N i := fun i => by have := hN i; omega
  set a : ι → ℂ := fun i => c i * ((N i : ℕ) : ℂ) ^ (-s) with ha_def
  have ha_le : ∀ i, ‖a i‖ ≤ ((N i : ℕ) : ℝ) ^ (-s.re) := fun i => by
    show ‖c i * ((N i : ℕ) : ℂ) ^ (-s)‖ ≤ _
    rw [norm_mul, norm_natCast_cpow_neg _ (hN0 i)]
    calc ‖c i‖ * ((N i : ℕ) : ℝ) ^ (-s.re) ≤ 1 * ((N i : ℕ) : ℝ) ^ (-s.re) :=
          mul_le_mul_of_nonneg_right (hc i) (Real.rpow_nonneg (Nat.cast_nonneg _) _)
      _ = _ := one_mul _
  have ha_half : ∀ i, ‖a i‖ ≤ 1 / 2 := fun i => (ha_le i).trans (rpow_neg_le_half (hN i) hs)
  have ha_lt : ∀ i, ‖a i‖ < 1 := fun i => (ha_half i).trans_lt (by norm_num)
  have ha_sum : Summable fun i => ‖a i‖ :=
    Summable.of_nonneg_of_le (fun i => norm_nonneg _) ha_le hsum
  rw [show (fun i => (1 - c i * ((N i : ℕ) : ℂ) ^ (-s))⁻¹) = fun i => (1 - a i)⁻¹ from rfl,
    norm_tprod_inv_one_sub_eq_exp a ha_sum ha_lt, Real.exp_le_exp]
  have hlog_le : ∀ i, ‖-log (1 - a i)‖ ≤ 2 * ((N i : ℕ) : ℝ) ^ (-s.re) := fun i =>
    (norm_neg_log_one_sub_le (ha_half i)).trans (by linarith [ha_le i])
  have hlog_sum : Summable fun i => ‖-log (1 - a i)‖ :=
    Summable.of_nonneg_of_le (fun i => norm_nonneg _) hlog_le (hsum.mul_left 2)
  have hre_sum : Summable fun i => (-log (1 - a i)).re :=
    (hlog_sum.of_norm).mapL Complex.reCLM
  have hneg : ∀ i, -(2 * ((N i : ℕ) : ℝ) ^ (-s.re)) ≤ (-log (1 - a i)).re := fun i => by
    have h1 := abs_re_le_norm (-log (1 - a i))
    have h2 := hlog_le i
    have := neg_le_of_abs_le h1
    linarith
  calc -(2 * ∑' i, ((N i : ℕ) : ℝ) ^ (-s.re)) = ∑' i, -(2 * ((N i : ℕ) : ℝ) ^ (-s.re)) := by
        rw [tsum_neg, tsum_mul_left]
    _ ≤ ∑' i, (-log (1 - a i)).re :=
        Summable.tsum_le_tsum hneg (hsum.mul_left 2).neg hre_sum

theorem tsum_rpow_neg_le_log_norm_tprod {ι : Type} (N : ι → ℕ) (hN : ∀ i, 2 ≤ N i)
    (σ : ℝ) (hσ : 1 ≤ σ) (hsum : Summable fun i => ((N i : ℕ) : ℝ) ^ (-σ)) :
    ∑' i, ((N i : ℕ) : ℝ) ^ (-σ) ≤ Real.log ‖∏' i, (1 - ((N i : ℕ) : ℂ) ^ (-(σ : ℂ)))⁻¹‖ := by
  have hN0 : ∀ i, 0 < N i := fun i => by have := hN i; omega
  set a : ι → ℂ := fun i => ((N i : ℕ) : ℂ) ^ (-(σ : ℂ)) with ha_def
  have ha_real : ∀ i, a i = ((((N i : ℕ) : ℝ) ^ (-σ) : ℝ) : ℂ) := fun i => by
    show ((N i : ℕ) : ℂ) ^ (-(σ : ℂ)) = _
    rw [Complex.ofReal_cpow (Nat.cast_nonneg _), ofReal_natCast, ofReal_neg]
  have ha_norm : ∀ i, ‖a i‖ = ((N i : ℕ) : ℝ) ^ (-σ) := fun i => by
    rw [ha_real i, norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg _) _)]
  have ha_half : ∀ i, ‖a i‖ ≤ 1 / 2 := fun i => by rw [ha_norm]; exact rpow_neg_le_half (hN i) hσ
  have ha_lt : ∀ i, ‖a i‖ < 1 := fun i => (ha_half i).trans_lt (by norm_num)
  have ha_sum : Summable fun i => ‖a i‖ := hsum.congr fun i => (ha_norm i).symm
  rw [show (fun i => (1 - ((N i : ℕ) : ℂ) ^ (-(σ : ℂ)))⁻¹) = fun i => (1 - a i)⁻¹ from rfl,
    norm_tprod_inv_one_sub_eq_exp a ha_sum ha_lt, Real.log_exp]
  have hterm : ∀ i, ((N i : ℕ) : ℝ) ^ (-σ) ≤ (-log (1 - a i)).re := fun i => by
    set x : ℝ := ((N i : ℕ) : ℝ) ^ (-σ) with hx
    have hx0 : 0 ≤ x := Real.rpow_nonneg (Nat.cast_nonneg _) _
    have hx1 : x ≤ 1 / 2 := rpow_neg_le_half (hN i) hσ
    have h1 : 1 - a i = (((1 - x : ℝ)) : ℂ) := by rw [ha_real i]; push_cast; rfl
    rw [h1, neg_re, log_ofReal_re]
    have h2 : Real.log (1 - x) ≤ (1 - x) - 1 := Real.log_le_sub_one_of_pos (by linarith)
    linarith
  have hlog_le : ∀ i, ‖-log (1 - a i)‖ ≤ 2 * ((N i : ℕ) : ℝ) ^ (-σ) := fun i =>
    (norm_neg_log_one_sub_le (ha_half i)).trans (by rw [ha_norm])
  have hlog_sum : Summable fun i => ‖-log (1 - a i)‖ :=
    Summable.of_nonneg_of_le (fun i => norm_nonneg _) hlog_le (hsum.mul_left 2)
  have hre_sum : Summable fun i => (-log (1 - a i)).re :=
    (hlog_sum.of_norm).mapL Complex.reCLM
  exact Summable.tsum_le_tsum hterm hsum hre_sum

end eulerAbstract

section zeta
variable {K : Type} [Field K] [NumberField K]

def nC (v : HeightOneSpectrum (𝓞 K)) : ℂ := ((Ideal.absNorm v.asIdeal : ℕ) : ℂ)

theorem nC_pos (v : HeightOneSpectrum (𝓞 K)) : 0 < Ideal.absNorm v.asIdeal :=
  lt_of_lt_of_le (by norm_num) (two_le_absNorm v)

theorem nC_ne_zero (v : HeightOneSpectrum (𝓞 K)) : nC v ≠ 0 := by
  unfold nC; exact_mod_cast (nC_pos v).ne'

theorem norm_nC_cpow_neg (v : HeightOneSpectrum (𝓞 K)) (s : ℂ) :
    ‖nC v ^ (-s)‖ = (Ideal.absNorm v.asIdeal : ℝ) ^ (-s.re) := by
  unfold nC
  rw [Complex.norm_natCast_cpow_of_pos (nC_pos v) (-s), Complex.neg_re]

theorem norm_nC_cpow_neg_le (v : HeightOneSpectrum (𝓞 K)) {s : ℂ} {σ₀ : ℝ} (hσ₀ : 0 ≤ σ₀)
    (hs : σ₀ ≤ s.re) : ‖nC v ^ (-s)‖ ≤ (2 : ℝ) ^ (-σ₀) := by
  rw [norm_nC_cpow_neg]
  have h2 : (2 : ℝ) ≤ (Ideal.absNorm v.asIdeal : ℝ) := by exact_mod_cast two_le_absNorm v
  calc (Ideal.absNorm v.asIdeal : ℝ) ^ (-s.re) ≤ (Ideal.absNorm v.asIdeal : ℝ) ^ (-σ₀) :=
        Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)
    _ ≤ (2 : ℝ) ^ (-σ₀) := by
        rw [Real.rpow_neg (by linarith), Real.rpow_neg (by norm_num)]
        exact inv_anti₀ (Real.rpow_pos_of_pos (by norm_num) _)
          (Real.rpow_le_rpow (by norm_num) h2 hσ₀)

theorem norm_nC_cpow_neg_lt_one {s : ℂ} (hs : 0 < s.re) (v : HeightOneSpectrum (𝓞 K)) :
    ‖nC v ^ (-s)‖ < 1 := by
  rw [norm_nC_cpow_neg]
  have h1 : (1 : ℝ) < (Ideal.absNorm v.asIdeal : ℝ) := by
    exact_mod_cast lt_of_lt_of_le one_lt_two (two_le_absNorm v)
  exact Real.rpow_lt_one_of_one_lt_of_neg h1 (by linarith)

theorem one_sub_mul_ne_zero {s : ℂ} (hs : 0 < s.re) (c : ℂ) (hc : ‖c‖ ≤ 1) (v : HeightOneSpectrum (𝓞 K)) :
    (1 : ℂ) - c * nC v ^ (-s) ≠ 0 := by
  intro h
  have hlt := norm_nC_cpow_neg_lt_one hs v
  rw [sub_eq_zero] at h
  have h1 : ‖c * nC v ^ (-s)‖ < 1 := by
    rw [norm_mul]
    calc ‖c‖ * ‖nC v ^ (-s)‖ ≤ 1 * ‖nC v ^ (-s)‖ := mul_le_mul_of_nonneg_right hc (norm_nonneg _)
      _ < 1 := by rw [one_mul]; exact hlt
  rw [← h, norm_one] at h1
  exact lt_irrefl _ h1

theorem one_sub_ne_zero {s : ℂ} (hs : 0 < s.re) (v : HeightOneSpectrum (𝓞 K)) :
    (1 : ℂ) - nC v ^ (-s) ≠ 0 := by
  have := one_sub_mul_ne_zero hs 1 (by rw [norm_one]) v
  rwa [one_mul] at this

def corr (T : Finset (HeightOneSpectrum (𝓞 K))) (c : HeightOneSpectrum (𝓞 K) → ℂ) (s : ℂ) : ℂ :=
  ∏ v ∈ T, (1 - c v * nC v ^ (-s))

theorem differentiable_corr (T : Finset (HeightOneSpectrum (𝓞 K))) (c : HeightOneSpectrum (𝓞 K) → ℂ) :
    Differentiable ℂ (corr T c) := by
  unfold corr
  refine Differentiable.fun_finsetProd fun v _ => ?_
  refine (differentiable_const _).sub ((differentiable_const _).mul ?_)
  exact Differentiable.const_cpow differentiable_neg (Or.inl (nC_ne_zero v))

theorem corr_ne_zero (T : Finset (HeightOneSpectrum (𝓞 K))) (c : HeightOneSpectrum (𝓞 K) → ℂ)
    (hc : ∀ v, ‖c v‖ ≤ 1) {s : ℂ} (hs : 0 < s.re) : corr T c s ≠ 0 :=
  Finset.prod_ne_zero_iff.mpr fun v _ => one_sub_mul_ne_zero hs (c v) (hc v) v

theorem norm_corr_le (T : Finset (HeightOneSpectrum (𝓞 K))) (c : HeightOneSpectrum (𝓞 K) → ℂ)
    (hc : ∀ v, ‖c v‖ ≤ 1) {s : ℂ} (hs : 0 < s.re) : ‖corr T c s‖ ≤ (2 : ℝ) ^ T.card := by
  unfold corr
  rw [norm_prod]
  calc ∏ v ∈ T, ‖1 - c v * nC v ^ (-s)‖ ≤ ∏ v ∈ T, (2 : ℝ) := by
        refine Finset.prod_le_prod (fun v _ => norm_nonneg _) fun v _ => ?_
        calc ‖1 - c v * nC v ^ (-s)‖ ≤ ‖(1 : ℂ)‖ + ‖c v * nC v ^ (-s)‖ := norm_sub_le _ _
          _ ≤ 1 + 1 := by
              rw [norm_one, norm_mul]
              have := (norm_nC_cpow_neg_lt_one hs v).le
              nlinarith [hc v, norm_nonneg (c v), norm_nonneg (nC v ^ (-s))]
          _ = 2 := by norm_num
    _ = (2 : ℝ) ^ T.card := Finset.prod_const 2

def kappa : ℝ := 1 - (2 : ℝ) ^ (-(1 / 2 : ℝ))

theorem kappa_pos : 0 < kappa := by
  unfold kappa
  have : (2 : ℝ) ^ (-(1 / 2 : ℝ)) < 1 := Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by norm_num)
  linarith

theorem kappa_le_one : kappa ≤ 1 := by
  unfold kappa
  have : 0 ≤ (2 : ℝ) ^ (-(1 / 2 : ℝ)) := Real.rpow_nonneg (by norm_num) _
  linarith

theorem pow_kappa_le_norm_corr (T : Finset (HeightOneSpectrum (𝓞 K))) (c : HeightOneSpectrum (𝓞 K) → ℂ)
    (hc : ∀ v, ‖c v‖ ≤ 1) {s : ℂ} (hs : 1 / 2 ≤ s.re) : kappa ^ T.card ≤ ‖corr T c s‖ := by
  unfold corr
  rw [norm_prod]
  calc kappa ^ T.card = ∏ _v ∈ T, kappa := (Finset.prod_const kappa).symm
    _ ≤ ∏ v ∈ T, ‖1 - c v * nC v ^ (-s)‖ := by
        refine Finset.prod_le_prod (fun v _ => kappa_pos.le) fun v _ => ?_
        have h1 : ‖c v * nC v ^ (-s)‖ ≤ (2 : ℝ) ^ (-(1 / 2 : ℝ)) := by
          rw [norm_mul]
          calc ‖c v‖ * ‖nC v ^ (-s)‖ ≤ 1 * ‖nC v ^ (-s)‖ :=
                mul_le_mul_of_nonneg_right (hc v) (norm_nonneg _)
            _ ≤ (2 : ℝ) ^ (-(1 / 2 : ℝ)) := by
                rw [one_mul]; exact norm_nC_cpow_neg_le v (by norm_num) hs
        have h2 : ‖(1 : ℂ)‖ - ‖c v * nC v ^ (-s)‖ ≤ ‖1 - c v * nC v ^ (-s)‖ := norm_sub_norm_le _ _
        rw [norm_one] at h2
        unfold kappa
        linarith

theorem summable_norm_coeff_mul {s : ℂ} (hs : 1 < s.re) (c : HeightOneSpectrum (𝓞 K) → ℂ)
    (hc : ∀ v, ‖c v‖ ≤ 1) : Summable fun v : HeightOneSpectrum (𝓞 K) => ‖c v * nC v ^ (-s)‖ := by
  have hn : Summable fun v : HeightOneSpectrum (𝓞 K) => ‖nC v ^ (-s)‖ := by
    refine (NumberField.summable_heightOneSpectrum_absNorm_rpow_neg_of_one_lt K hs).congr fun v => ?_
    rw [norm_nC_cpow_neg]
  refine Summable.of_nonneg_of_le (fun v => norm_nonneg _) (fun v => ?_) hn
  rw [norm_mul]
  calc ‖c v‖ * ‖nC v ^ (-s)‖ ≤ 1 * ‖nC v ^ (-s)‖ := mul_le_mul_of_nonneg_right (hc v) (norm_nonneg _)
    _ = _ := one_mul _

theorem hasProd_gated_subtype {s : ℂ} (hs : 1 < s.re) (c : HeightOneSpectrum (𝓞 K) → ℂ)
    (hc : ∀ v, ‖c v‖ ≤ 1) (p : HeightOneSpectrum (𝓞 K) → Prop) :
    HasProd (fun v : {v : HeightOneSpectrum (𝓞 K) // p v} => (1 - c v.1 * nC v.1 ^ (-s))⁻¹)
      (cexp (∑' v : {v : HeightOneSpectrum (𝓞 K) // p v}, -log (1 - c v.1 * nC v.1 ^ (-s)))) := by
  have hs0 : 0 < s.re := lt_trans zero_lt_one hs
  have hne : ∀ v : HeightOneSpectrum (𝓞 K), (1 : ℂ) - c v * nC v ^ (-s) ≠ 0 :=
    fun v => one_sub_mul_ne_zero hs0 (c v) (hc v) v
  have hsub : Summable fun v : {v : HeightOneSpectrum (𝓞 K) // p v} => c v.1 * nC v.1 ^ (-s) :=
    ((summable_norm_coeff_mul hs c hc).subtype {v | p v}).of_norm
  have hg : Summable fun v : {v : HeightOneSpectrum (𝓞 K) // p v} => -log (1 - c v.1 * nC v.1 ^ (-s)) :=
    hsub.clog_one_sub.neg
  have H := hg.hasSum.cexp
  have hcongr : (cexp ∘ fun v : {v : HeightOneSpectrum (𝓞 K) // p v} => -log (1 - c v.1 * nC v.1 ^ (-s))) =
      fun v => (1 - c v.1 * nC v.1 ^ (-s))⁻¹ := by
    funext v
    simp only [Function.comp_apply, exp_neg, exp_log (hne v.1)]
  rw [hcongr] at H
  exact H

theorem hasProd_gated {s : ℂ} (hs : 1 < s.re) (c : HeightOneSpectrum (𝓞 K) → ℂ)
    (hc : ∀ v, ‖c v‖ ≤ 1) :
    HasProd (fun v : HeightOneSpectrum (𝓞 K) => (1 - c v * nC v ^ (-s))⁻¹)
      (cexp (∑' v : HeightOneSpectrum (𝓞 K), -log (1 - c v * nC v ^ (-s)))) := by
  have hs0 : 0 < s.re := lt_trans zero_lt_one hs
  have hne : ∀ v : HeightOneSpectrum (𝓞 K), (1 : ℂ) - c v * nC v ^ (-s) ≠ 0 :=
    fun v => one_sub_mul_ne_zero hs0 (c v) (hc v) v
  have hsub : Summable fun v : HeightOneSpectrum (𝓞 K) => c v * nC v ^ (-s) :=
    (summable_norm_coeff_mul hs c hc).of_norm
  have hg : Summable fun v : HeightOneSpectrum (𝓞 K) => -log (1 - c v * nC v ^ (-s)) :=
    hsub.clog_one_sub.neg
  have H := hg.hasSum.cexp
  have hcongr : (cexp ∘ fun v : HeightOneSpectrum (𝓞 K) => -log (1 - c v * nC v ^ (-s))) =
      fun v => (1 - c v * nC v ^ (-s))⁻¹ := by
    funext v
    simp only [Function.comp_apply, exp_neg, exp_log (hne v)]
  rw [hcongr] at H
  exact H

theorem tprod_mul_corr_eq {s : ℂ} (hs : 1 < s.re) (c : HeightOneSpectrum (𝓞 K) → ℂ)
    (hc : ∀ v, ‖c v‖ ≤ 1) (T : Finset (HeightOneSpectrum (𝓞 K))) :
    (∏' v : HeightOneSpectrum (𝓞 K), (1 - c v * nC v ^ (-s))⁻¹) * corr T c s =
      ∏' v : {v : HeightOneSpectrum (𝓞 K) // v ∉ T}, (1 - c v.1 * nC v.1 ^ (-s))⁻¹ := by
  have hs0 : 0 < s.re := lt_trans zero_lt_one hs
  have hPS := hasProd_gated_subtype (K := K) hs c hc (fun v => v ∉ T)
  have hfull := hasProd_gated (K := K) hs c hc
  set f : HeightOneSpectrum (𝓞 K) → ℂ := fun v => (1 - c v * nC v ^ (-s))⁻¹ with hf
  set ES : ℂ := cexp (∑' v : {v : HeightOneSpectrum (𝓞 K) // v ∉ T}, -log (1 - c v.1 * nC v.1 ^ (-s)))
    with hES
  set EF : ℂ := cexp (∑' v : HeightOneSpectrum (𝓞 K), -log (1 - c v * nC v ^ (-s))) with hEF
  have hE' : HasProd (f ∘ (↑) : ((↑T : Set (HeightOneSpectrum (𝓞 K)))ᶜ : Set (HeightOneSpectrum (𝓞 K))) → ℂ)
      ES := hPS
  have hG : HasProd (f ∘ (↑) : (↑T : Set (HeightOneSpectrum (𝓞 K))) → ℂ) (∏ v ∈ T, f v) := Finset.hasProd T _
  have hall := hG.mul_isCompl isCompl_compl hE'
  have heq : (∏ v ∈ T, f v) * ES = EF := HasProd.unique hall hfull
  have hinv : (∏ v ∈ T, f v) = (corr T c s)⁻¹ := by
    unfold corr; rw [hf]; exact Finset.prod_inv_distrib _
  have hne : corr T c s ≠ 0 := corr_ne_zero T c hc hs0
  rw [hPS.tprod_eq, hfull.tprod_eq, ← heq, hinv]
  field_simp

theorem tprod_one_eq {s : ℂ} (hs : 1 < s.re) (T : Finset (HeightOneSpectrum (𝓞 K))) :
    ∏' v : {v : HeightOneSpectrum (𝓞 K) // v ∉ T}, (1 - nC v.1 ^ (-s))⁻¹ =
      dedekindZeta K s * corr T (fun _ => 1) s := by
  have h := tprod_mul_corr_eq (K := K) hs (fun _ => 1) (fun _ => by rw [norm_one]) T
  simp only [one_mul] at h
  rw [← h]
  congr 1
  exact (NumberField.hasProd_inv_one_sub_absNorm_cpow_neg_dedekindZeta K s hs).tprod_eq

theorem exists_Z (T : Finset (HeightOneSpectrum (𝓞 K))) :
    ∃ Z : ℂ → ℂ, Differentiable ℂ Z ∧ Z 1 ≠ 0 ∧
      ∀ s : ℂ, 1 < s.re → Z s = (s - 1) * ∏' v : {v : HeightOneSpectrum (𝓞 K) // v ∉ T},
        (1 - (((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) ^ (-s)))⁻¹ := by
  obtain ⟨R, hRd, hR1, hReq, -⟩ :=
    NumberField.exists_differentiable_eq_sub_one_mul_dedekindZeta_and_apply_neg_two_mul_add_one_eq_zero K
  refine ⟨fun s => R s * corr T (fun _ => 1) s, hRd.mul (differentiable_corr T _), ?_, fun s hs => ?_⟩
  · show R 1 * corr T (fun _ => 1) 1 ≠ 0
    exact mul_ne_zero hR1 (corr_ne_zero T _ (fun _ => by rw [norm_one]) (by simp))
  · show R s * corr T (fun _ => 1) s = (s - 1) * _
    have h := tprod_one_eq (K := K) hs T
    unfold nC at h
    rw [hReq s hs, h, mul_assoc]

end zeta

section zetaTools
variable {K : Type} [Field K] [NumberField K]

theorem summable_subtype_rpow (T : Finset (HeightOneSpectrum (𝓞 K))) {σ : ℝ} (hσ : 1 < σ) :
    Summable fun v : {v : HeightOneSpectrum (𝓞 K) // v ∉ T} =>
      ((Ideal.absNorm v.1.asIdeal : ℕ) : ℝ) ^ (-σ) :=
  (NumberField.summable_heightOneSpectrum_absNorm_rpow_neg_of_one_lt K hσ).subtype _

theorem differentiableAt_and_ne_zero (T : Finset (HeightOneSpectrum (𝓞 K)))
    (c : HeightOneSpectrum (𝓞 K) → ℂ) (hc : ∀ v, ‖c v‖ ≤ 1) (s : ℂ) (hs : 1 < s.re) :
    DifferentiableAt ℂ (fun z : ℂ => ∏' v : {v : HeightOneSpectrum (𝓞 K) // v ∉ T},
        (1 - c v.1 * (((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) ^ (-z)))⁻¹) s ∧
      (∏' v : {v : HeightOneSpectrum (𝓞 K) // v ∉ T},
        (1 - c v.1 * (((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) ^ (-s)))⁻¹) ≠ 0 := by
  have h := EulerProduct.differentiableAt_and_ne_zero_and_hasSum_log_mul_div_neg_deriv_tprod_div
    (fun v : {v : HeightOneSpectrum (𝓞 K) // v ∉ T} => Ideal.absNorm v.1.asIdeal)
    (fun v => two_le_absNorm v.1) (fun v => c v.1) (fun v => hc v.1)
    (fun σ hσ => summable_subtype_rpow T hσ) s hs
  exact ⟨h.1, h.2.1⟩

theorem tprod_ne_zero_one (T : Finset (HeightOneSpectrum (𝓞 K))) (s : ℂ) (hs : 1 < s.re) :
    (∏' v : {v : HeightOneSpectrum (𝓞 K) // v ∉ T},
        (1 - (((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) ^ (-s)))⁻¹) ≠ 0 := by
  have h := (differentiableAt_and_ne_zero T (fun _ => 1) (fun _ => by rw [norm_one]) s hs).2
  simp only [one_mul] at h
  exact h

theorem sq_le_norm_tprod (T : Finset (HeightOneSpectrum (𝓞 K)))
    (c : HeightOneSpectrum (𝓞 K) → ℂ) (hc : ∀ v, ‖c v‖ ≤ 1)
    (Z : ℂ → ℂ)
    (hZeq : ∀ s : ℂ, 1 < s.re → Z s = (s - 1) * ∏' v : {v : HeightOneSpectrum (𝓞 K) // v ∉ T},
        (1 - (((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) ^ (-s)))⁻¹)
    (C : ℝ) (hC1 : 1 ≤ C) (hZle : ∀ σ : ℝ, 1 < σ → σ ≤ 2 → ‖Z σ‖ ≤ C)
    (σ t : ℝ) (hσ : 1 < σ) (hσ2 : σ ≤ 2) :
    ((σ - 1) / C) ^ 2 ≤ ‖∏' v : {v : HeightOneSpectrum (𝓞 K) // v ∉ T},
        (1 - c v.1 * (((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) ^ (-((σ : ℂ) + t * I))))⁻¹‖ := by
  have hsumσ := summable_subtype_rpow (K := K) T hσ
  have hre : ((σ : ℂ) + t * I).re = σ := by simp
  have hlow := exp_neg_le_norm_tprod
    (fun v : {v : HeightOneSpectrum (𝓞 K) // v ∉ T} => Ideal.absNorm v.1.asIdeal)
    (fun v => two_le_absNorm v.1) (fun v => c v.1) (fun v => hc v.1) ((σ : ℂ) + t * I)
    (by rw [hre]; exact hσ.le) (by rw [hre]; exact hsumσ)
  rw [hre] at hlow
  refine le_trans ?_ hlow
  have hzeta := tsum_rpow_neg_le_log_norm_tprod
    (fun v : {v : HeightOneSpectrum (𝓞 K) // v ∉ T} => Ideal.absNorm v.1.asIdeal)
    (fun v => two_le_absNorm v.1) σ hσ.le hsumσ
  set E₀σ : ℂ := ∏' v : {v : HeightOneSpectrum (𝓞 K) // v ∉ T},
      (1 - (((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) ^ (-(σ : ℂ))))⁻¹ with hE₀σ
  have hσ1 : (σ : ℂ) - 1 ≠ 0 := by
    rw [sub_ne_zero]; intro h; have := congrArg Complex.re h; simp at this; linarith
  have hE₀eq : E₀σ = Z σ / ((σ : ℂ) - 1) := by
    rw [hZeq _ (by simpa using hσ), mul_div_cancel_left₀ _ hσ1]
  have hnormσ1 : ‖(σ : ℂ) - 1‖ = σ - 1 := by
    rw [← ofReal_one, ← ofReal_sub, norm_real, Real.norm_eq_abs, abs_of_pos (by linarith)]
  have hE₀norm : ‖E₀σ‖ ≤ C / (σ - 1) := by
    rw [hE₀eq, norm_div, hnormσ1]
    exact div_le_div_of_nonneg_right (hZle σ hσ hσ2) (by linarith)
  have hE₀pos : 0 < ‖E₀σ‖ := norm_pos_iff.mpr (tprod_ne_zero_one T (σ : ℂ) (by simpa using hσ))
  have hCσ : 0 < C / (σ - 1) := by positivity
  have hlog : Real.log ‖E₀σ‖ ≤ Real.log (C / (σ - 1)) := Real.log_le_log hE₀pos hE₀norm
  have hS : ∑' v : {v : HeightOneSpectrum (𝓞 K) // v ∉ T}, ((Ideal.absNorm v.1.asIdeal : ℕ) : ℝ) ^ (-σ)
      ≤ Real.log (C / (σ - 1)) := hzeta.trans hlog
  have hexp : ((σ - 1) / C) ^ 2 = Real.exp (-(2 * Real.log (C / (σ - 1)))) := by
    rw [show -(2 * Real.log (C / (σ - 1))) = (2 : ℕ) * (-Real.log (C / (σ - 1))) by push_cast; ring,
      Real.exp_nat_mul, Real.exp_neg, Real.exp_log hCσ, inv_div]
  rw [hexp, Real.exp_le_exp]
  linarith

end zetaTools

section three
open Metric

theorem three_bounds (F : ℂ → ℂ) (hF : Differentiable ℂ F) (t η U m σ : ℝ)
    (hη0 : 0 < η) (hη : η ≤ 1 / 8) (hU : 1 ≤ U) (hm0 : 0 < m) (hm1 : m ≤ 1)
    (hσ1 : 1 - η ≤ σ) (hσ2 : σ ≤ 2)
    (hzero : ∀ z : ℂ, 1 - 3 * η ≤ z.re → |z.im - t| ≤ 1 / 2 → F z ≠ 0)
    (hup : ∀ z : ℂ, 1 / 2 ≤ z.re → z.re ≤ 5 / 2 → |z.im - t| ≤ 1 / 2 → ‖F z‖ ≤ U)
    (hlo : ∀ σ' : ℝ, 1 + η ≤ σ' → σ' ≤ 2 → m ≤ ‖F ((σ' : ℂ) + t * I)‖) :
    F ((σ : ℂ) + t * I) ≠ 0 ∧
    ‖deriv F ((σ : ℂ) + t * I)‖ ≤ 12 / η * (Real.log U + Real.log (1 / m) + 1) * ‖F ((σ : ℂ) + t * I)‖ ∧
    Real.exp (-(5 * (Real.log U + Real.log (1 / m) + 1))) ≤ ‖F ((σ : ℂ) + t * I)‖ := by
  set M : ℝ := Real.log U + Real.log (1 / m) + 1 with hMdef
  have hlogU : 0 ≤ Real.log U := Real.log_nonneg hU
  have hlogm : 0 ≤ Real.log (1 / m) := Real.log_nonneg (by rw [le_div_iff₀ hm0]; linarith)
  have hM0 : 0 < M := by rw [hMdef]; linarith
  set σ₀ : ℝ := max σ (1 + η) with hσ₀def
  have hσ₀1 : 1 + η ≤ σ₀ := le_max_right _ _
  have hσ₀2 : σ₀ ≤ 2 := max_le hσ2 (by linarith)
  have hσσ₀ : σ ≤ σ₀ := le_max_left _ _
  have hσ₀σ : σ₀ ≤ σ + 2 * η := max_le (by linarith) (by linarith)
  set s₀ : ℂ := (σ₀ : ℂ) + t * I with hs₀def
  set R : ℝ := 4 * η with hRdef
  have hR0 : 0 < R := by positivity

  have hball : ∀ z ∈ ball s₀ R, |z.re - σ₀| < R ∧ |z.im - t| < R := by
    intro z hz
    rw [mem_ball, dist_eq_norm] at hz
    have hre := abs_re_le_norm (z - s₀)
    have him := abs_im_le_norm (z - s₀)
    simp only [hs₀def, sub_re, add_re, ofReal_re, mul_re, I_re, mul_zero, ofReal_im, I_im, mul_one,
      sub_self, add_zero, sub_im, add_im, mul_im, zero_add] at hre him
    exact ⟨hre.trans_lt hz, him.trans_lt hz⟩
  have hnz : ∀ z ∈ ball s₀ R, F z ≠ 0 := by
    intro z hz
    obtain ⟨hre, him⟩ := hball z hz
    have h1 := (abs_lt.mp hre).1
    exact hzero z (by rw [hRdef] at h1; linarith) (by rw [hRdef] at him; linarith)
  have hupM : ∀ z ∈ ball s₀ R, ‖F z‖ ≤ Real.exp M := by
    intro z hz
    obtain ⟨hre, him⟩ := hball z hz
    have h1 := abs_lt.mp hre
    rw [hRdef] at h1 him
    refine (hup z (by linarith) (by linarith) (by linarith)).trans ?_
    calc U = Real.exp (Real.log U) := (Real.exp_log (by linarith)).symm
      _ ≤ Real.exp M := Real.exp_le_exp.mpr (by rw [hMdef]; linarith)
  have hloM : Real.exp (-M) ≤ ‖F s₀‖ := by
    refine le_trans ?_ (hlo σ₀ hσ₀1 hσ₀2)
    have h1 : Real.exp (-M) ≤ Real.exp (Real.log m) := by
      refine Real.exp_le_exp.mpr ?_
      have : Real.log (1 / m) = -Real.log m := by rw [one_div, Real.log_inv]
      rw [hMdef, this]; linarith
    rwa [Real.exp_log hm0] at h1
  have H := Complex.norm_deriv_le_mul_norm_and_exp_neg_le_norm_of_forall_ne_zero_of_norm_le_exp
    F s₀ R M hR0 hM0 hF.differentiableOn hnz hupM hloM ((σ : ℂ) + t * I) (by
      rw [mem_closedBall, dist_eq_norm]
      have : ((σ : ℂ) + t * I) - s₀ = ((σ - σ₀ : ℝ) : ℂ) := by rw [hs₀def]; push_cast; ring
      rw [this, norm_real, Real.norm_eq_abs, abs_le]
      constructor <;> linarith)
  obtain ⟨hder, hlow⟩ := H
  refine ⟨fun h => ?_, ?_, hlow⟩
  · rw [h, norm_zero] at hlow
    linarith [Real.exp_pos (-(5 * M))]
  · refine hder.trans (le_of_eq ?_)
    rw [hRdef]
    field_simp
    ring

theorem M_le (T A U₀ M₀ c' a : ℝ) (e : ℕ) (hT : 2 ≤ T) (hA : 0 ≤ A) (hU₀ : 1 ≤ U₀) (hM₀ : 1 ≤ M₀)
    (hc' : 0 < c') (hc'1 : c' ≤ Real.log 2) (ha : 1 ≤ a) :
    Real.log (U₀ * (a * T) ^ A) + Real.log (1 / (1 / (M₀ * (Real.log T / c') ^ e))) + 1 ≤
      ((Real.log U₀ + A * Real.log a + Real.log M₀ + e * Real.log (1 / c') + 1) / Real.log 2 + (A + e)) *
        Real.log T := by
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlogT : Real.log 2 ≤ Real.log T := Real.log_le_log (by norm_num) hT
  have hlogT0 : 0 < Real.log T := hlog2.trans_le hlogT
  have hT0 : 0 < T := by linarith
  have ha0 : 0 < a := by linarith
  have hx : 1 ≤ Real.log T / c' := by rw [le_div_iff₀ hc']; linarith
  have hx0 : 0 < Real.log T / c' := by linarith
  have h1 : Real.log (U₀ * (a * T) ^ A) = Real.log U₀ + A * Real.log a + A * Real.log T := by
    rw [Real.log_mul (by linarith) (Real.rpow_pos_of_pos (by positivity) _).ne',
      Real.log_rpow (by positivity), Real.log_mul ha0.ne' hT0.ne']
    ring
  have h2 : Real.log (1 / (1 / (M₀ * (Real.log T / c') ^ e))) =
      Real.log M₀ + e * (Real.log (Real.log T) + Real.log (1 / c')) := by
    rw [one_div_one_div, Real.log_mul (by linarith) (pow_pos hx0 _).ne', Real.log_pow,
      Real.log_div hlogT0.ne' hc'.ne', one_div, Real.log_inv]
    ring
  have h3 : Real.log (Real.log T) ≤ Real.log T := by
    have := Real.log_le_sub_one_of_pos hlogT0
    linarith
  have hlogc : 0 ≤ Real.log (1 / c') := Real.log_nonneg (by
    rw [le_div_iff₀ hc']; linarith [Real.log_two_lt_d9])
  have hlogU₀ : 0 ≤ Real.log U₀ := Real.log_nonneg hU₀
  have hlogM₀ : 0 ≤ Real.log M₀ := Real.log_nonneg hM₀
  have hloga : 0 ≤ Real.log a := Real.log_nonneg ha
  set B : ℝ := Real.log U₀ + A * Real.log a + Real.log M₀ + e * Real.log (1 / c') + 1 with hB
  have hB0 : 0 ≤ B := by rw [hB]; positivity
  have hBle : B ≤ B / Real.log 2 * Real.log T := by
    rw [div_mul_eq_mul_div, le_div_iff₀ hlog2]
    exact mul_le_mul_of_nonneg_left hlogT hB0
  rw [h1, h2]
  have he0 : (0 : ℝ) ≤ e := Nat.cast_nonneg _
  have h4 : (e : ℝ) * (Real.log (Real.log T) + Real.log (1 / c')) ≤ e * (Real.log T + Real.log (1 / c')) :=
    mul_le_mul_of_nonneg_left (by linarith) he0
  nlinarith

theorem package (F : ℂ → ℂ) (s : ℂ) (T c' M D : ℝ) (hT : 2 ≤ T) (hc' : 0 < c') (hD : 0 < D)
    (hM0 : 0 < M) (hMD : M ≤ D * Real.log T)
    (hder : ‖deriv F s‖ ≤ 12 / (c' / Real.log T) * M * ‖F s‖)
    (hlow : Real.exp (-(5 * M)) ≤ ‖F s‖) :
    ‖deriv F s‖ ≤ max (12 * D / c') 1 * T ^ (⌈5 * D⌉₊ + 2) * ‖F s‖ ∧
      1 ≤ max (12 * D / c') 1 * T ^ (⌈5 * D⌉₊ + 2) * ‖F s‖ := by
  have hT1 : 1 ≤ T := by linarith
  have hT0 : 0 < T := by linarith
  have hlogT0 : 0 < Real.log T := Real.log_pos (by linarith)
  have hlogT : Real.log T ≤ T := by have := Real.log_le_sub_one_of_pos hT0; linarith
  set A : ℕ := ⌈5 * D⌉₊ + 2 with hAdef
  set C : ℝ := max (12 * D / c') 1 with hCdef
  have hC1 : 1 ≤ C := le_max_right _ _
  have hTA2 : T ^ 2 ≤ T ^ A := pow_le_pow_right₀ hT1 (by omega)
  have hTA1 : (1 : ℝ) ≤ T ^ A := one_le_pow₀ hT1

  have hexp : Real.exp (5 * M) ≤ T ^ A := by
    calc Real.exp (5 * M) ≤ Real.exp (5 * D * Real.log T) := Real.exp_le_exp.mpr (by nlinarith)
      _ = T ^ (5 * D) := by rw [Real.rpow_def_of_pos hT0, mul_comm]
      _ ≤ T ^ ((⌈5 * D⌉₊ : ℕ) : ℝ) := Real.rpow_le_rpow_of_exponent_le hT1 (Nat.le_ceil _)
      _ = T ^ (⌈5 * D⌉₊ : ℕ) := Real.rpow_natCast T _
      _ ≤ T ^ A := pow_le_pow_right₀ hT1 (by omega)
  constructor
  · refine hder.trans ?_
    refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
    have h1 : 12 / (c' / Real.log T) * M = 12 / c' * (M * Real.log T) := by
      field_simp
    rw [h1]
    calc 12 / c' * (M * Real.log T) ≤ 12 / c' * (D * Real.log T * Real.log T) := by
          refine mul_le_mul_of_nonneg_left ?_ (by positivity)
          exact mul_le_mul_of_nonneg_right hMD hlogT0.le
      _ ≤ 12 / c' * (D * T * T) := by
          refine mul_le_mul_of_nonneg_left ?_ (by positivity)
          have := mul_le_mul hlogT hlogT hlogT0.le hT0.le
          nlinarith
      _ = 12 * D / c' * T ^ 2 := by ring
      _ ≤ C * T ^ A := mul_le_mul (le_max_left _ _) hTA2 (by positivity) (by positivity)
  · have h1 : (1 : ℝ) ≤ Real.exp (5 * M) * ‖F s‖ := by
      have := mul_le_mul_of_nonneg_left hlow (Real.exp_pos (5 * M)).le
      rwa [← Real.exp_add, show 5 * M + -(5 * M) = 0 by ring, Real.exp_zero] at this
    calc (1 : ℝ) ≤ Real.exp (5 * M) * ‖F s‖ := h1
      _ ≤ C * T ^ A * ‖F s‖ := by
          refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
          calc Real.exp (5 * M) ≤ T ^ A := hexp
            _ = 1 * T ^ A := (one_mul _).symm
            _ ≤ C * T ^ A := mul_le_mul_of_nonneg_right hC1 (by positivity)

end three

section caseTwo
variable (K : Type) [Field K] [NumberField K]

omit [NumberField K] in

theorem tprod_subtype_empty (f : HeightOneSpectrum (𝓞 K) → ℂ) :
    ∏' v : {v : HeightOneSpectrum (𝓞 K) // v ∉ (∅ : Finset (HeightOneSpectrum (𝓞 K)))}, f v.1 = ∏' v, f v :=
  (Equiv.subtypeUnivEquiv (fun v : HeightOneSpectrum (𝓞 K) => Finset.notMem_empty v)).tprod_eq f

set_option maxHeartbeats 6400000 in
open scoped Classical in
theorem caseTwo :
    ∃ (c₂ C₂ : ℝ) (A₂ : ℕ), 0 < c₂ ∧ c₂ ≤ Real.log 2 / 8 ∧ 0 < C₂ ∧
      ∀ (τ₀ : ℝ) (Q : ℂ → ℂ), Differentiable ℂ Q →
        (∀ w : ℂ, 1 < w.re → Q w = (w - ((1 : ℂ) - ((τ₀ : ℝ) : ℂ) * Complex.I)) *
          ∏' v : HeightOneSpectrum (𝓞 K),
            (1 - (if IsUnramifiedCharAt (normPowChar K τ₀) v then
                ((normPowChar K τ₀ (uniformizerIdele K v) : ℂˣ) : ℂ) else 0) *
              (((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ^ (-w)))⁻¹) →
        ∀ (t σ : ℝ), 1 - c₂ / Real.log (2 + |t + τ₀|) ≤ σ → σ ≤ 2 →
          Q ((σ : ℂ) + (t : ℂ) * Complex.I) ≠ 0 ∧
          ‖deriv Q ((σ : ℂ) + (t : ℂ) * Complex.I)‖ ≤
            C₂ * (2 + |t + τ₀|) ^ A₂ * ‖Q ((σ : ℂ) + (t : ℂ) * Complex.I)‖ ∧
          1 ≤ C₂ * (2 + |t + τ₀|) ^ A₂ * ‖Q ((σ : ℂ) + (t : ℂ) * Complex.I)‖ := by
  obtain ⟨c₃, hc₃, hZF⟩ :=
    NumberField.TateGlobal.exists_pos_forall_sub_one_mul_partialDedekindZeta_continuation_ne_zero_of_one_sub_div_log_le_re
      K ∅
  obtain ⟨CZ, AZ, hCZ, hAZ, hZs⟩ :=
    NumberField.TateGlobal.exists_forall_norm_sub_one_mul_partialDedekindZeta_continuation_le_rpow_of_re_mem_Icc K ∅
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  set CZ' : ℝ := max (CZ * (2 : ℝ) ^ AZ) 1 with hCZ'def
  have hCZ'1 : 1 ≤ CZ' := le_max_right _ _
  set CZ₁ : ℝ := max CZ 1 with hCZ₁def
  have hCZ₁1 : 1 ≤ CZ₁ := le_max_right _ _
  set c₂ : ℝ := min (c₃ / 6) (Real.log 2 / 8) with hc₂def
  have hc₂0 : 0 < c₂ := lt_min (by linarith) (by positivity)
  have hc₂le : c₂ ≤ Real.log 2 / 8 := min_le_right _ _
  have hc₂le' : c₂ ≤ c₃ / 6 := min_le_left _ _
  have hc₂log : c₂ ≤ Real.log 2 := by linarith
  set M₀ : ℝ := CZ' ^ 2 with hM₀def
  have hM₀1 : 1 ≤ M₀ := by rw [hM₀def]; nlinarith
  set D : ℝ := (Real.log CZ₁ + AZ * Real.log 2 + Real.log M₀ + (3 : ℕ) * Real.log (1 / c₂) + 1) / Real.log 2
    + (AZ + (3 : ℕ)) with hDdef
  have hD0 : 0 < D := by
    have h1 : 0 ≤ (Real.log CZ₁ + AZ * Real.log 2 + Real.log M₀ + (3 : ℕ) * Real.log (1 / c₂) + 1) / Real.log 2 := by
      apply div_nonneg _ hlog2.le
      have : 0 ≤ Real.log (1 / c₂) := Real.log_nonneg (by rw [le_div_iff₀ hc₂0]; linarith [Real.log_two_lt_d9])
      have := Real.log_nonneg hCZ₁1
      have := Real.log_nonneg hM₀1
      positivity
    rw [hDdef]; positivity
  refine ⟨c₂, max (12 * D / c₂) 1, ⌈5 * D⌉₊ + 2, hc₂0, hc₂le, lt_of_lt_of_le one_pos (le_max_right _ _), ?_⟩
  intro τ₀ Q hQd hQeq t σ hσ1 hσ2

  set T : ℝ := 2 + |t + τ₀| with hTdef
  have hT2 : 2 ≤ T := by rw [hTdef]; linarith [abs_nonneg (t + τ₀)]
  have hT0 : 0 < T := by linarith
  have hlogT : Real.log 2 ≤ Real.log T := Real.log_le_log (by norm_num) hT2
  have hlogT0 : 0 < Real.log T := hlog2.trans_le hlogT
  set η : ℝ := c₂ / Real.log T with hηdef
  have hη0 : 0 < η := div_pos hc₂0 hlogT0
  have hη8 : η ≤ 1 / 8 := by
    rw [hηdef, div_le_iff₀ hlogT0]
    calc c₂ ≤ Real.log 2 / 8 := hc₂le
      _ ≤ 1 / 8 * Real.log T := by linarith

  set Z : ℂ → ℂ := fun u => Q (u - (τ₀ : ℂ) * I) with hZdef
  have hZd : Differentiable ℂ Z := hQd.comp (differentiable_id.sub_const _)
  have hZeq : ∀ u : ℂ, 1 < u.re → Z u = (u - 1) *
      ∏' v : {v : HeightOneSpectrum (𝓞 K) // v ∉ (∅ : Finset (HeightOneSpectrum (𝓞 K)))},
        (1 - (((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) ^ (-u)))⁻¹ := by
    intro u hu
    have hu' : 1 < (u - (τ₀ : ℂ) * I).re := by simpa using hu
    show Q (u - (τ₀ : ℂ) * I) = _
    rw [hQeq _ hu', tprod_subtype_empty K (fun v => (1 - (((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ^ (-u)))⁻¹)]
    congr 1
    · ring_nf
    · refine tprod_congr fun v => ?_
      rw [NumberField.TateGlobal.ite_isUnramifiedCharAt_normPowChar_apply_uniformizerIdele_eq_absNorm_cpow_neg,
        ← cpow_add _ _ (Nat.cast_ne_zero.mpr (by have := two_le_absNorm v; omega))]
      congr 2
      ring_nf

  have hZle : ∀ σ' : ℝ, 1 < σ' → σ' ≤ 2 → ‖Z σ'‖ ≤ CZ' := by
    intro σ' hσ' hσ'2
    have h := hZs Z hZd hZeq σ' (by rw [ofReal_re]; linarith) (by rw [ofReal_re]; linarith)
    rw [ofReal_im, abs_zero, add_zero] at h
    exact h.trans (le_max_left _ _)

  set U : ℝ := CZ₁ * (2 * T) ^ AZ with hUdef
  have hU1 : 1 ≤ U := by
    rw [hUdef]
    have : (1 : ℝ) ≤ (2 * T) ^ AZ := Real.one_le_rpow (by linarith) hAZ.le
    nlinarith
  set m : ℝ := 1 / (M₀ * (Real.log T / c₂) ^ (3 : ℕ)) with hmdef
  have hx1 : 1 ≤ Real.log T / c₂ := by rw [le_div_iff₀ hc₂0]; linarith
  have hx3 : 1 ≤ (Real.log T / c₂) ^ (3 : ℕ) := one_le_pow₀ hx1
  have hm0 : 0 < m := by rw [hmdef]; positivity
  have hm1 : m ≤ 1 := by
    rw [hmdef, div_le_one (by positivity)]
    nlinarith
  have hηx : Real.log T / c₂ = 1 / η := by rw [hηdef, one_div_div]
  have h3 := three_bounds Z hZd (t + τ₀) η U m σ hη0 hη8 hU1 hm0 hm1 (by rw [hηdef]; exact hσ1) hσ2 ?_ ?_ ?_
  rotate_left
  ·
    intro z hz1 hz2
    refine hZF Z hZd hZeq z ?_
    have him : |z.im| ≤ T := by
      have := abs_sub_abs_le_abs_sub z.im (t + τ₀)
      rw [hTdef]; linarith
    have h2 : 2 + |z.im| ≤ T ^ 2 := by nlinarith [abs_nonneg z.im]
    have hlogz0 : 0 < Real.log (2 + |z.im|) := Real.log_pos (by linarith [abs_nonneg z.im])
    have hlogz : Real.log (2 + |z.im|) ≤ 2 * Real.log T := by
      have := Real.log_le_log (by linarith [abs_nonneg z.im]) h2
      rwa [Real.log_pow, Nat.cast_ofNat] at this
    have h4 : 3 * η ≤ c₃ / Real.log (2 + |z.im|) := by
      rw [le_div_iff₀ hlogz0, hηdef]
      calc 3 * (c₂ / Real.log T) * Real.log (2 + |z.im|) ≤ 3 * (c₂ / Real.log T) * (2 * Real.log T) :=
            mul_le_mul_of_nonneg_left hlogz (by positivity)
        _ = 6 * c₂ := by field_simp; norm_num
        _ ≤ c₃ := by linarith
    linarith
  ·
    intro z hz1 hz2 hz3
    have h := hZs Z hZd hZeq z (by linarith) hz2
    refine h.trans ?_
    rw [hUdef]
    have him : 2 + |z.im| ≤ 2 * T := by
      have := abs_sub_abs_le_abs_sub z.im (t + τ₀)
      rw [hTdef]; linarith
    have h1 : (2 + |z.im|) ^ AZ ≤ (2 * T) ^ AZ := Real.rpow_le_rpow (by positivity) him hAZ.le
    exact mul_le_mul (le_max_left _ _) h1 (by positivity) (by positivity)
  ·
    intro σ' hσ'1 hσ'2
    have hσ' : 1 < σ' := by linarith
    have hpt : ((σ' : ℂ) + ((t + τ₀ : ℝ) : ℂ) * I).re = σ' := by simp
    rw [hZeq _ (by rw [hpt]; exact hσ'), norm_mul]
    have hsq := sq_le_norm_tprod ∅ (fun _ => (1 : ℂ)) (fun _ => by rw [norm_one]) Z hZeq CZ' hCZ'1 hZle
      σ' (t + τ₀) hσ' hσ'2
    simp only [one_mul] at hsq
    have h1 : σ' - 1 ≤ ‖((σ' : ℂ) + ((t + τ₀ : ℝ) : ℂ) * I) - 1‖ := by
      have := abs_re_le_norm (((σ' : ℂ) + ((t + τ₀ : ℝ) : ℂ) * I) - 1)
      simp only [sub_re, add_re, ofReal_re, mul_re, I_re, mul_zero, ofReal_im, I_im, mul_one, sub_self,
        add_zero, one_re] at this
      rw [abs_of_pos (by linarith)] at this
      exact this
    have h2 : η ≤ σ' - 1 := by linarith
    have h3 : (η / CZ') ^ 2 ≤ ((σ' - 1) / CZ') ^ 2 := by
      apply pow_le_pow_left₀ (by positivity)
      exact div_le_div_of_nonneg_right h2 (by linarith)
    calc m = η * (η / CZ') ^ 2 := by
          rw [hmdef, hM₀def, hηx]; field_simp
      _ ≤ ‖((σ' : ℂ) + ((t + τ₀ : ℝ) : ℂ) * I) - 1‖ * ((σ' - 1) / CZ') ^ 2 :=
          mul_le_mul (h2.trans h1) h3 (by positivity) (norm_nonneg _)
      _ ≤ _ := mul_le_mul_of_nonneg_left hsq (norm_nonneg _)

  obtain ⟨hne, hder, hlow⟩ := h3
  have harg : ((σ : ℂ) + ((t + τ₀ : ℝ) : ℂ) * I) - (τ₀ : ℂ) * I = (σ : ℂ) + (t : ℂ) * I := by
    push_cast; ring
  have hZval : Z ((σ : ℂ) + ((t + τ₀ : ℝ) : ℂ) * I) = Q ((σ : ℂ) + (t : ℂ) * I) := by
    show Q (((σ : ℂ) + ((t + τ₀ : ℝ) : ℂ) * I) - (τ₀ : ℂ) * I) = _; rw [harg]
  have hZder : deriv Z ((σ : ℂ) + ((t + τ₀ : ℝ) : ℂ) * I) = deriv Q ((σ : ℂ) + (t : ℂ) * I) := by
    show deriv (fun u => Q (u - (τ₀ : ℂ) * I)) _ = _
    rw [deriv_comp_sub_const, harg]
  rw [hZval] at hne hder hlow
  rw [hZder] at hder
  refine ⟨hne, ?_⟩

  have hM := M_le T AZ CZ₁ M₀ c₂ 2 3 hT2 hAZ.le hCZ₁1 hM₀1 hc₂0 hc₂log (by norm_num)
  have hMpos : 0 < Real.log U + Real.log (1 / m) + 1 := by
    have := Real.log_nonneg hU1
    have : 0 ≤ Real.log (1 / m) := Real.log_nonneg (by rw [le_div_iff₀ hm0]; linarith)
    linarith
  exact package Q _ T c₂ (Real.log U + Real.log (1 / m) + 1) D hT2 hc₂0 hD0 hMpos
    (by rw [hUdef, hmdef]; exact hM) (by rw [← hηdef]; exact hder) hlow

end caseTwo

section arch
variable {K : Type} [Field K] [NumberField K]

omit [NumberField K] in
theorem norm_eq_of_extensionEmbedding_eq (w : InfinitePlace K) (a : w.Completion) {r : ℝ} (hr : 0 < r)
    (ha : Completion.extensionEmbedding w a = (r : ℂ)) : ‖a‖ = r := by
  have h := (Completion.isometry_extensionEmbedding w).norm_map_of_map_zero (map_zero _) a
  rw [ha, norm_real, Real.norm_eq_abs, abs_of_pos hr] at h
  exact h.symm

theorem ideleNorm_archUnitHom (w : InfinitePlace K) (a : (w.Completion)ˣ) :
    ideleNorm K (archUnitHom w a) = ‖(a : w.Completion)‖ ^ w.mult := by
  classical
  rw [archUnitHom_apply,
    NumberField.TateGlobal.ideleNorm_eq_prod_norm_infinitePlace_pow_mult_of_snd_eq_one K _
      (AdelicVolume.archCentralUnit_snd w a), Finset.prod_eq_single w]
  · rw [AdelicVolume.archCentralUnit_fst_self]
  · intro w' _ hw'
    rw [AdelicVolume.archCentralUnit_fst_of_ne w a hw', norm_one, one_pow]
  · intro h; exact absurd (Finset.mem_univ w) h

theorem ofReal_exp_cpow (u : ℝ) (s : ℂ) : ((Real.exp u : ℝ) : ℂ) ^ s = cexp ((u : ℂ) * s) := by
  rw [cpow_def_of_ne_zero (ofReal_ne_zero.mpr (Real.exp_pos u).ne'), ← ofReal_log (Real.exp_pos u).le,
    Real.log_exp]

theorem archLocalChar_eq_cpow_of_pin (χ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ) (τ : InfinitePlace K → ℝ)
    (hτ : ∀ (v : InfinitePlace K) (x : (v.Completion)ˣ),
      0 < (InfinitePlace.Completion.extensionEmbedding v (x : v.Completion)).re →
      (InfinitePlace.Completion.extensionEmbedding v (x : v.Completion)).im = 0 →
      ((archLocalChar χ v x : ℂˣ) : ℂ) =
        (((ideleNorm K (archUnitHom v x)) : ℝ) : ℂ) ^ (((τ v : ℝ) : ℂ) * Complex.I))
    (w : InfinitePlace K) (a : (w.Completion)ˣ) (r : ℝ) (hr : 0 < r)
    (ha : Completion.extensionEmbedding w (a : w.Completion) = (r : ℂ)) :
    ((archLocalChar χ w a : ℂˣ) : ℂ) = (r : ℂ) ^ (Complex.I * (((w.mult : ℝ) * τ w : ℝ) : ℂ)) := by
  have h := hτ w a (by rw [ha, ofReal_re]; exact hr) (by rw [ha, ofReal_im])
  rw [h, ideleNorm_archUnitHom, norm_eq_of_extensionEmbedding_eq w a hr ha]
  have hr' : r = Real.exp (Real.log r) := (Real.exp_log hr).symm
  have hpow : r ^ w.mult = Real.exp ((w.mult : ℝ) * Real.log r) := by
    rw [Real.exp_nat_mul, ← hr']
  rw [hpow, ofReal_exp_cpow]
  conv_rhs => rw [hr', ofReal_exp_cpow]
  congr 1
  push_cast
  ring

omit [NumberField K] in
theorem mult_le_two (w : InfinitePlace K) : (w.mult : ℝ) ≤ 2 := by
  have : w.mult ≤ 2 := by
    unfold InfinitePlace.mult; split_ifs <;> norm_num
  exact_mod_cast this

theorem sum_mult_bounds (τ : InfinitePlace K → ℝ) (m : InfinitePlace K → ℤ) :
    ∑ v : InfinitePlace K, (|τ v| + |(m v : ℝ)|) ≤
        ∑ v : InfinitePlace K, (|(v.mult : ℝ) * τ v| + |(m v : ℝ)|) ∧
      ∑ v : InfinitePlace K, (|(v.mult : ℝ) * τ v| + |(m v : ℝ)|) ≤
        2 * ∑ v : InfinitePlace K, (|τ v| + |(m v : ℝ)|) := by
  constructor
  · refine Finset.sum_le_sum fun v _ => ?_
    have hmpos : (0 : ℝ) < v.mult := by exact_mod_cast (InfinitePlace.mult_pos (w := v))
    rw [abs_mul, abs_of_pos hmpos]
    have h1 : (1 : ℝ) ≤ v.mult := InfinitePlace.one_le_mult
    nlinarith [abs_nonneg (τ v)]
  · rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun v _ => ?_
    have hmpos : (0 : ℝ) < v.mult := by exact_mod_cast (InfinitePlace.mult_pos (w := v))
    rw [abs_mul, abs_of_pos hmpos]
    have h1 := mult_le_two v
    nlinarith [abs_nonneg (τ v), abs_nonneg (m v : ℝ)]

end arch

section caseOne
variable (K : Type) [Field K] [NumberField K]

set_option maxHeartbeats 12000000 in
open scoped Classical in
theorem caseOne (S : Finset (HeightOneSpectrum (𝓞 K))) (𝔣 : Ideal (𝓞 K)) :
    ∃ (c₁ C₁ : ℝ) (A₁ : ℕ), 0 < c₁ ∧ 0 < C₁ ∧
      ∀ (χ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ), IsIdeleClassChar (𝓞 K) K χ → Continuous χ →
        IsUnitaryChar (𝓞 K) K χ → (∃ x ∈ normOneIdeles K, χ x ≠ 1) →
        HeckeCharacter.AdmitsModulus K χ 𝔣 → (∀ v ∉ S, IsUnramifiedCharAt χ v) →
      ∀ (τ : InfinitePlace K → ℝ) (m : InfinitePlace K → ℤ),
        (∀ (v : InfinitePlace K) (x : (v.Completion)ˣ),
          0 < (InfinitePlace.Completion.extensionEmbedding v (x : v.Completion)).re →
          (InfinitePlace.Completion.extensionEmbedding v (x : v.Completion)).im = 0 →
          ((archLocalChar χ v x : ℂˣ) : ℂ) =
            (((ideleNorm K (archUnitHom v x)) : ℝ) : ℂ) ^ (((τ v : ℝ) : ℂ) * Complex.I)) →
        (∀ (v : InfinitePlace K) (x : (v.Completion)ˣ),
          ‖InfinitePlace.Completion.extensionEmbedding v (x : v.Completion)‖ = 1 →
          ((archLocalChar χ v x : ℂˣ) : ℂ) =
            (InfinitePlace.Completion.extensionEmbedding v (x : v.Completion)) ^ (m v)) →
      ∀ (L : ℂ → ℂ), Differentiable ℂ L →
        (∀ w : ℂ, 1 < w.re → L w = ∏' v : HeightOneSpectrum (𝓞 K),
            (1 - (if IsUnramifiedCharAt χ v then ((χ (uniformizerIdele K v) : ℂˣ) : ℂ) else 0) *
              (((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ^ (-w)))⁻¹) →
      ∀ (t σ : ℝ), 1 - c₁ / Real.log (2 + |t| + ∑ v : InfinitePlace K, (|τ v| + |(m v : ℝ)|)) ≤ σ → σ ≤ 2 →
        L ((σ : ℂ) + (t : ℂ) * Complex.I) ≠ 0 ∧
        ‖deriv L ((σ : ℂ) + (t : ℂ) * Complex.I)‖ ≤
          C₁ * (2 + |t| + ∑ v : InfinitePlace K, (|τ v| + |(m v : ℝ)|)) ^ A₁ *
            ‖L ((σ : ℂ) + (t : ℂ) * Complex.I)‖ ∧
        1 ≤ C₁ * (2 + |t| + ∑ v : InfinitePlace K, (|τ v| + |(m v : ℝ)|)) ^ A₁ *
            ‖L ((σ : ℂ) + (t : ℂ) * Complex.I)‖ := by
  obtain ⟨c, hc, hR⟩ :=
    NumberField.TateGlobal.exists_pos_forall_partialEulerProduct_continuation_ne_zero_of_one_sub_div_log_le_re_of_admitsModulus
      K S 𝔣
  obtain ⟨CS, AS, hCS, hAS, hS⟩ :=
    NumberField.TateGlobal.exists_forall_norm_partialEulerProduct_continuation_le_rpow_of_re_mem_Icc_of_admitsModulus
      K S 𝔣
  obtain ⟨CZ, AZ, hCZ, hAZ, hZs⟩ :=
    NumberField.TateGlobal.exists_forall_norm_sub_one_mul_partialDedekindZeta_continuation_le_rpow_of_re_mem_Icc K S
  obtain ⟨ZS, hZSd, -, hZSeq⟩ := exists_Z (K := K) S
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  set CZ' : ℝ := max (CZ * (2 : ℝ) ^ AZ) 1 with hCZ'def
  have hCZ'1 : 1 ≤ CZ' := le_max_right _ _
  have hZle : ∀ σ' : ℝ, 1 < σ' → σ' ≤ 2 → ‖ZS σ'‖ ≤ CZ' := by
    intro σ' hσ' hσ'2
    have h := hZs ZS hZSd hZSeq σ' (by rw [ofReal_re]; linarith) (by rw [ofReal_re]; linarith)
    rw [ofReal_im, abs_zero, add_zero] at h
    exact h.trans (le_max_left _ _)
  set c₁ : ℝ := min (c / 9) (Real.log 2 / 8) with hc₁def
  have hc₁0 : 0 < c₁ := lt_min (by linarith) (by positivity)
  have hc₁le : c₁ ≤ Real.log 2 / 8 := min_le_right _ _
  have hc₁le' : c₁ ≤ c / 9 := min_le_left _ _
  have hc₁log : c₁ ≤ Real.log 2 := by linarith
  have hκ := kappa_pos
  set U₀ : ℝ := max CS 1 * (kappa⁻¹) ^ S.card with hU₀def
  have hκinv : 1 ≤ kappa⁻¹ := one_le_inv_iff₀.mpr ⟨hκ, kappa_le_one⟩
  have hU₀1 : 1 ≤ U₀ := by
    rw [hU₀def]
    exact one_le_mul_of_one_le_of_one_le (le_max_right _ _) (one_le_pow₀ hκinv)
  set M₀ : ℝ := CZ' ^ 2 * (2 : ℝ) ^ S.card with hM₀def
  have hM₀1 : 1 ≤ M₀ := by
    rw [hM₀def]
    exact one_le_mul_of_one_le_of_one_le (by nlinarith) (one_le_pow₀ (by norm_num))
  set D : ℝ := (Real.log U₀ + AS * Real.log 3 + Real.log M₀ + (2 : ℕ) * Real.log (1 / c₁) + 1) / Real.log 2
    + (AS + (2 : ℕ)) with hDdef
  have hD0 : 0 < D := by
    have h1 : 0 ≤ (Real.log U₀ + AS * Real.log 3 + Real.log M₀ + (2 : ℕ) * Real.log (1 / c₁) + 1) / Real.log 2 := by
      apply div_nonneg _ hlog2.le
      have : 0 ≤ Real.log (1 / c₁) := Real.log_nonneg (by rw [le_div_iff₀ hc₁0]; linarith [Real.log_two_lt_d9])
      have := Real.log_nonneg hU₀1
      have := Real.log_nonneg hM₀1
      have : 0 ≤ Real.log 3 := Real.log_nonneg (by norm_num)
      positivity
    rw [hDdef]; positivity
  refine ⟨c₁, max (12 * D / c₁) 1, ⌈5 * D⌉₊ + 2, hc₁0, lt_of_lt_of_le one_pos (le_max_right _ _), ?_⟩
  intro χ hχ hχc hχu hχ1 hχ𝔣 hT τ m hτ hm L hLd hLP t σ hσ1 hσ2

  set Sm : ℝ := ∑ v : InfinitePlace K, (|τ v| + |(m v : ℝ)|) with hSmdef
  have hSm0 : 0 ≤ Sm := Finset.sum_nonneg fun v _ => by positivity
  set T : ℝ := 2 + |t| + Sm with hTdef
  have hT2 : 2 ≤ T := by rw [hTdef]; linarith [abs_nonneg t]
  have hT0 : 0 < T := by linarith
  have hlogT : Real.log 2 ≤ Real.log T := Real.log_le_log (by norm_num) hT2
  have hlogT0 : 0 < Real.log T := hlog2.trans_le hlogT
  set η : ℝ := c₁ / Real.log T with hηdef
  have hη0 : 0 < η := div_pos hc₁0 hlogT0
  have hη8 : η ≤ 1 / 8 := by
    rw [hηdef, div_le_iff₀ hlogT0]
    calc c₁ ≤ Real.log 2 / 8 := hc₁le
      _ ≤ 1 / 8 * Real.log T := by linarith

  set φ : InfinitePlace K → ℝ := fun w => (w.mult : ℝ) * τ w with hφdef
  have hφ : ∀ (w : InfinitePlace K) (a : (w.Completion)ˣ) (r : ℝ), 0 < r →
      Completion.extensionEmbedding w (a : w.Completion) = (r : ℂ) →
      ((archLocalChar χ w a : ℂˣ) : ℂ) = (r : ℂ) ^ (Complex.I * φ w) := fun w a r hr ha =>
    archLocalChar_eq_cpow_of_pin χ τ hτ w a r hr ha
  set Q : ℝ := ∑ w : InfinitePlace K, (|φ w| + |(m w : ℝ)|) with hQdef
  have hQb := sum_mult_bounds (K := K) τ m
  have hQ1 : Sm ≤ Q := hQb.1
  have hQ2 : Q ≤ 2 * Sm := hQb.2

  set cχ : HeightOneSpectrum (𝓞 K) → ℂ := fun v =>
    if IsUnramifiedCharAt χ v then ((χ (uniformizerIdele K v) : ℂˣ) : ℂ) else 0 with hcχdef
  have hcχ : ∀ v, ‖cχ v‖ ≤ 1 := fun v => norm_coeff_le_one hχu v
  set L' : ℂ → ℂ := fun w => L w * corr S cχ w with hL'def
  have hL'd : Differentiable ℂ L' := hLd.mul (differentiable_corr S cχ)
  have hL'eq : ∀ w : ℂ, 1 < w.re → L' w = ∏' v : {v : HeightOneSpectrum (𝓞 K) // v ∉ S},
      (1 - (if IsUnramifiedCharAt χ v.1 then ((χ (uniformizerIdele K v.1) : ℂˣ) : ℂ) else 0) *
        (((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) ^ (-w)))⁻¹ := by
    intro w hw
    show L w * corr S cχ w = _
    rw [hLP w hw]
    exact tprod_mul_corr_eq (K := K) hw cχ hcχ S
  have hcorr_ne : ∀ z : ℂ, 0 < z.re → corr S cχ z ≠ 0 := fun z hz => corr_ne_zero S cχ hcχ hz
  have hLeq' : ∀ z : ℂ, 0 < z.re → L z = L' z / corr S cχ z := by
    intro z hz
    show L z = L z * corr S cχ z / corr S cχ z
    rw [mul_div_cancel_right₀ _ (hcorr_ne z hz)]

  have hwin : ∀ z : ℂ, |z.im - t| ≤ 1 / 2 → 2 + |z.im| + Q ≤ 3 * T := by
    intro z hz
    have := abs_sub_abs_le_abs_sub z.im t
    rw [hTdef]; linarith [abs_nonneg t]

  set U : ℝ := U₀ * (3 * T) ^ AS with hUdef
  have hU1 : 1 ≤ U := by
    rw [hUdef]
    have : (1 : ℝ) ≤ (3 * T) ^ AS := Real.one_le_rpow (by linarith) hAS.le
    nlinarith
  set mlo : ℝ := 1 / (M₀ * (Real.log T / c₁) ^ (2 : ℕ)) with hmdef
  have hx1 : 1 ≤ Real.log T / c₁ := by rw [le_div_iff₀ hc₁0]; linarith
  have hx2 : 1 ≤ (Real.log T / c₁) ^ (2 : ℕ) := one_le_pow₀ hx1
  have hm0 : 0 < mlo := by rw [hmdef]; positivity
  have hm1 : mlo ≤ 1 := by
    rw [hmdef, div_le_one (by positivity)]
    nlinarith
  have hηx : Real.log T / c₁ = 1 / η := by rw [hηdef, one_div_div]
  have h3 := three_bounds L hLd t η U mlo σ hη0 hη8 hU1 hm0 hm1 (by rw [hηdef]; exact hσ1) hσ2 ?_ ?_ ?_
  rotate_left
  ·
    intro z hz1 hz2 hLz
    have h𝔮 := hwin z hz2
    have hz0 : 0 < z.re := by linarith
    have hlogz0 : 0 < Real.log (2 + |z.im| + Q) := Real.log_pos (by
      have : Sm ≤ Q := hQ1; linarith [abs_nonneg z.im])
    have hTT : 4 ≤ T * T := by nlinarith
    have hT3 : 3 * T ≤ T ^ 3 := by nlinarith
    have h33 : 2 + |z.im| + Q ≤ T ^ 3 := h𝔮.trans hT3
    have hlogz : Real.log (2 + |z.im| + Q) ≤ 3 * Real.log T := by
      have := Real.log_le_log (by linarith [abs_nonneg z.im]) h33
      rwa [Real.log_pow, Nat.cast_ofNat] at this
    have h4 : 3 * η ≤ c / Real.log (2 + |z.im| + Q) := by
      rw [le_div_iff₀ hlogz0, hηdef]
      calc 3 * (c₁ / Real.log T) * Real.log (2 + |z.im| + Q) ≤ 3 * (c₁ / Real.log T) * (3 * Real.log T) :=
            mul_le_mul_of_nonneg_left hlogz (by positivity)
        _ = 9 * c₁ := by field_simp; norm_num
        _ ≤ c := by linarith
    have hL'z : L' z = 0 := by show L z * corr S cχ z = 0; rw [hLz, zero_mul]
    exact hR χ hχ hχc hχu hχ1 hχ𝔣 hT φ m hφ hm L' hL'd hL'eq z (by linarith) hL'z
  ·
    intro z hz1 hz2 hz3
    have hz0 : 0 < z.re := by linarith
    have h := hS χ hχ hχc hχu hχ1 hχ𝔣 hT φ m hφ hm L' hL'd hL'eq z (by linarith) hz2
    have hcorr := pow_kappa_le_norm_corr S cχ hcχ (s := z) hz1
    have hκS : 0 < kappa ^ S.card := pow_pos hκ _
    rw [hLeq' z hz0, norm_div, div_le_iff₀ (hκS.trans_le hcorr)]
    refine h.trans ?_
    have h1 : (2 + |z.im| + Q) ^ AS ≤ (3 * T) ^ AS :=
      Real.rpow_le_rpow (by linarith [abs_nonneg z.im, hQ1]) (hwin z hz3) hAS.le
    calc CS * (2 + |z.im| + Q) ^ AS ≤ max CS 1 * (3 * T) ^ AS :=
          mul_le_mul (le_max_left _ _) h1 (by positivity) (by positivity)
      _ = U * ((kappa⁻¹) ^ S.card)⁻¹ := by
          rw [hUdef, hU₀def, inv_pow, inv_inv]; field_simp
      _ = U * kappa ^ S.card := by rw [inv_pow, inv_inv]
      _ ≤ U * ‖corr S cχ z‖ := mul_le_mul_of_nonneg_left hcorr (by linarith)
  ·
    intro σ' hσ'1 hσ'2
    have hσ' : 1 < σ' := by linarith
    have hpt : ((σ' : ℂ) + (t : ℂ) * I).re = σ' := by simp
    have hz0 : 0 < ((σ' : ℂ) + (t : ℂ) * I).re := by rw [hpt]; linarith
    rw [hLeq' _ hz0, norm_div]
    have hsq := sq_le_norm_tprod S cχ hcχ ZS hZSeq CZ' hCZ'1 hZle σ' t hσ' hσ'2
    rw [← hL'eq _ (by rw [hpt]; exact hσ')] at hsq
    have hcorr := norm_corr_le S cχ hcχ (s := (σ' : ℂ) + (t : ℂ) * I) hz0
    have hcorr0 : 0 < ‖corr S cχ ((σ' : ℂ) + (t : ℂ) * I)‖ := norm_pos_iff.mpr (hcorr_ne _ hz0)
    rw [le_div_iff₀ hcorr0]
    have h2 : η ≤ σ' - 1 := by linarith
    have h3 : (η / CZ') ^ 2 ≤ ((σ' - 1) / CZ') ^ 2 := by
      apply pow_le_pow_left₀ (by positivity)
      exact div_le_div_of_nonneg_right h2 (by linarith)
    calc mlo * ‖corr S cχ ((σ' : ℂ) + (t : ℂ) * I)‖ ≤ mlo * (2 : ℝ) ^ S.card :=
          mul_le_mul_of_nonneg_left hcorr hm0.le
      _ = (η / CZ') ^ 2 := by
          rw [hmdef, hM₀def, hηx]; field_simp
      _ ≤ ((σ' - 1) / CZ') ^ 2 := h3
      _ ≤ _ := hsq
  obtain ⟨hne, hder, hlow⟩ := h3
  refine ⟨hne, ?_⟩
  have hM := M_le T AS U₀ M₀ c₁ 3 2 hT2 hAS.le hU₀1 hM₀1 hc₁0 hc₁log (by norm_num)
  have hMpos : 0 < Real.log U + Real.log (1 / mlo) + 1 := by
    have := Real.log_nonneg hU1
    have : 0 ≤ Real.log (1 / mlo) := Real.log_nonneg (by rw [le_div_iff₀ hm0]; linarith)
    linarith
  exact package L _ T c₁ (Real.log U + Real.log (1 / mlo) + 1) D hT2 hc₁0 hD0 hMpos
    (by rw [hUdef, hmdef]; exact hM) (by rw [← hηdef]; exact hder) hlow

end caseOne

section assembly

theorem weaken {C₁ C T X Y : ℝ} {A₁ A : ℕ} (hC₁0 : 0 ≤ C₁) (hC : C₁ ≤ C) (hA : A₁ ≤ A) (hT : 1 ≤ T)
    (hX : 0 ≤ X) (h : Y ≤ C₁ * T ^ A₁ * X) : Y ≤ C * T ^ A * X := by
  refine h.trans (mul_le_mul_of_nonneg_right ?_ hX)
  have hC₁ : C₁ * T ^ A₁ ≤ C * T ^ A₁ := mul_le_mul_of_nonneg_right hC (by positivity)
  refine hC₁.trans ?_
  exact mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hT hA) (hC₁0.trans hC)

theorem region_weaken {c₀ c₁ T σ : ℝ} (hc : c₀ ≤ c₁) (hT : 2 ≤ T) (h : 1 - c₀ / Real.log T ≤ σ) :
    1 - c₁ / Real.log T ≤ σ := by
  have hlog : 0 < Real.log T := Real.log_pos (by linarith)
  have : c₀ / Real.log T ≤ c₁ / Real.log T := div_le_div_of_nonneg_right hc hlog.le
  linarith

end assembly

end R4ZFT

end

open NumberField IsDedekindDomain AutomorphicForm NumberField.TateGlobal in
open scoped Classical in
theorem solution
    (K : Type) [Field K] [NumberField K]
    (S : Finset (HeightOneSpectrum (𝓞 K)))
    (ρ : ∀ v : HeightOneSpectrum (𝓞 K), (v.adicCompletion K)ˣ →* ℂˣ) :
    ∃ (c₀ C : ℝ) (A : ℕ), 0 < c₀ ∧ 0 < C ∧
    ∀ (χ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ)
      (_hχc : Continuous fun z : (AdeleRing (𝓞 K) K)ˣ => ((χ z : ℂˣ) : ℂ))
      (_hχu : AutomorphicForm.IsUnitaryChar (𝓞 K) K χ) (_hχF : AutomorphicForm.IsIdeleClassChar (𝓞 K) K χ)
      (_hunr : ∀ v : HeightOneSpectrum (𝓞 K), v ∉ S → IsUnramifiedCharAt χ v)
      (_hram : ∀ v ∈ S, ∀ u : (v.adicCompletion K)ˣ, (u : v.adicCompletion K) ∈ v.adicCompletionIntegers K →
        ((u⁻¹ : (v.adicCompletion K)ˣ) : v.adicCompletion K) ∈ v.adicCompletionIntegers K → localChar χ v u = ρ v u),
    let P : ℂ → ℂ := fun w => ∏' v : HeightOneSpectrum (𝓞 K),
        (1 - (if IsUnramifiedCharAt χ v then ((χ (uniformizerIdele K v) : ℂˣ) : ℂ) else 0) *
          (((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ^ (-w)))⁻¹
    (∀ (τ : InfinitePlace K → ℝ) (m : InfinitePlace K → ℤ)
        (_hτ : ∀ (v : InfinitePlace K) (x : (v.Completion)ˣ),
          0 < (InfinitePlace.Completion.extensionEmbedding v (x : v.Completion)).re →
          (InfinitePlace.Completion.extensionEmbedding v (x : v.Completion)).im = 0 →
          ((archLocalChar χ v x : ℂˣ) : ℂ) =
            (((ideleNorm K (archUnitHom v x)) : ℝ) : ℂ) ^ (((τ v : ℝ) : ℂ) * Complex.I))
        (_hm : ∀ (v : InfinitePlace K) (x : (v.Completion)ˣ),
          ‖InfinitePlace.Completion.extensionEmbedding v (x : v.Completion)‖ = 1 →
          ((archLocalChar χ v x : ℂˣ) : ℂ) =
            (InfinitePlace.Completion.extensionEmbedding v (x : v.Completion)) ^ (m v))
        (_hχ1 : ∀ τ₀ : ℝ, χ ≠ normPowChar K τ₀)
        (L : ℂ → ℂ) (_hL : Differentiable ℂ L) (_hLP : ∀ w : ℂ, 1 < w.re → L w = P w)
        (t σ : ℝ),
        let T : ℝ := 2 + |t| + ∑ v : InfinitePlace K, (|τ v| + (|m v| : ℝ))
        1 - c₀ / Real.log T ≤ σ → σ ≤ 2 →
          L ((σ : ℂ) + (t : ℂ) * Complex.I) ≠ 0 ∧
          ‖deriv L ((σ : ℂ) + (t : ℂ) * Complex.I)‖ ≤ C * T ^ A * ‖L ((σ : ℂ) + (t : ℂ) * Complex.I)‖ ∧
          1 ≤ C * T ^ A * ‖L ((σ : ℂ) + (t : ℂ) * Complex.I)‖) ∧
    (∀ (τ₀ : ℝ) (_hχ0 : χ = normPowChar K τ₀)
        (Q : ℂ → ℂ) (_hQ : Differentiable ℂ Q)
        (_hQP : ∀ w : ℂ, 1 < w.re → Q w = (w - ((1 : ℂ) - ((τ₀ : ℝ) : ℂ) * Complex.I)) * P w)
        (t σ : ℝ),
        let T : ℝ := 2 + |t + τ₀|
        1 - c₀ / Real.log T ≤ σ → σ ≤ 2 →
          Q ((σ : ℂ) + (t : ℂ) * Complex.I) ≠ 0 ∧
          ‖deriv Q ((σ : ℂ) + (t : ℂ) * Complex.I)‖ ≤ C * T ^ A * ‖Q ((σ : ℂ) + (t : ℂ) * Complex.I)‖ ∧
          1 ≤ C * T ^ A * ‖Q ((σ : ℂ) + (t : ℂ) * Complex.I)‖) := by
  obtain ⟨𝔣, -, hAdm⟩ :=
    HeckeCharacter.exists_ne_bot_forall_admitsModulus_of_isUnramifiedCharAt_of_localChar_eq K S ρ
  obtain ⟨c₁, C₁, A₁, hc₁, hC₁, h1⟩ := R4ZFT.caseOne K S 𝔣
  obtain ⟨c₂, C₂, A₂, hc₂, -, hC₂, h2⟩ := R4ZFT.caseTwo K
  refine ⟨min c₁ c₂, max C₁ C₂, max A₁ A₂, lt_min hc₁ hc₂, lt_max_iff.mpr (Or.inl hC₁), ?_⟩
  intro χ hχc hχu hχF hunr hram P
  constructor
  · intro τ m hτ hm hχ1 L hL hLP t σ T hσ1 hσ2
    have hcont : Continuous χ := R4ZFT.continuous_of_continuous_coe χ hχc
    have h𝔸 : ∃ x ∈ normOneIdeles K, χ x ≠ 1 := by
      by_contra h
      push Not at h
      obtain ⟨θ, hθ⟩ :=
        NumberField.TateGlobal.exists_eq_normPowChar_of_forall_mem_normOneIdeles K χ hcont hχu h
      exact hχ1 θ hθ
    have hadm : HeckeCharacter.AdmitsModulus K χ 𝔣 := hAdm χ hχc hχu hunr hram
    have hSm : 0 ≤ ∑ v : InfinitePlace K, (|τ v| + (|m v| : ℝ)) := Finset.sum_nonneg fun v _ => by positivity
    have hT2 : 2 ≤ T := by show 2 ≤ 2 + |t| + _; linarith [abs_nonneg t]
    have hT1 : 1 ≤ T := by linarith
    have key := h1 χ hχF hcont hχu h𝔸 hadm hunr τ m hτ hm L hL hLP t σ
      (R4ZFT.region_weaken (min_le_left _ _) hT2 hσ1) hσ2
    obtain ⟨hne, hder, hlow⟩ := key
    exact ⟨hne, R4ZFT.weaken hC₁.le (le_max_left _ _) (le_max_left _ _) hT1 (norm_nonneg _) hder,
      R4ZFT.weaken hC₁.le (le_max_left _ _) (le_max_left _ _) hT1 (norm_nonneg _) hlow⟩
  · intro τ₀ hχ0 Q hQ hQP t σ T hσ1 hσ2
    subst hχ0
    have hT2 : 2 ≤ T := by show 2 ≤ 2 + |t + τ₀|; linarith [abs_nonneg (t + τ₀)]
    have hT1 : 1 ≤ T := by linarith
    have key := h2 τ₀ Q hQ hQP t σ (R4ZFT.region_weaken (min_le_right _ _) hT2 hσ1) hσ2
    obtain ⟨hne, hder, hlow⟩ := key
    exact ⟨hne, R4ZFT.weaken hC₂.le (le_max_right _ _) (le_max_right _ _) hT1 (norm_nonneg _) hder,
      R4ZFT.weaken hC₂.le (le_max_right _ _) (le_max_right _ _) hT1 (norm_nonneg _) hlow⟩

end S_NumberField_TateGlobal_exists_zeroFree_norm_deriv_le_and_inv_le_eulerProduct_continuation_of_archLocalChar_eq
end P2MW
export P2MW.S_NumberField_TateGlobal_exists_zeroFree_norm_deriv_le_and_inv_le_eulerProduct_continuation_of_archLocalChar_eq (solution)
