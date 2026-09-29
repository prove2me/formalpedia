-- Prove2me | solution 1 for NumberField.TateGlobal.exists_pos_forall_partialEulerProduct_continuation_ne_zero_of_one_sub_div_log_le_re_of_admitsModulus
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.93214+00:00
-- url     : https://prove2.me/submissions/a29adbac-ec08-51d0-877a-1201c35a12c4

import Mathlib
import Definitions.Def_NumberField_TateGlobalZeta
import Definitions.Def_NumberField_NormPowChar
import Definitions.Def_AutomorphicForm_HeckeEigenfunction
import Definitions.Def_HeckeCharacter_FiniteOrder
import Theorems.Thm_Complex_div_le_one_sub_of_apply_eq_zero_of_norm_le_exp_of_three_four_one_nonneg
import Theorems.Thm_EulerProduct_differentiableAt_and_ne_zero_and_hasSum_log_mul_div_neg_deriv_tprod_div
import Theorems.Thm_EulerProduct_three_mul_re_neg_deriv_tprod_div_add_four_mul_add_nonneg_of_norm_le_one
import Theorems.Thm_NumberField_TateGlobal_exists_forall_norm_partialEulerProduct_continuation_le_rpow_of_re_mem_Icc_of_admitsModulus
import Theorems.Thm_NumberField_TateGlobal_exists_forall_norm_sub_one_mul_partialDedekindZeta_continuation_le_rpow_of_re_mem_Icc
import Theorems.Thm_NumberField_TateGlobal_exists_pos_forall_partialEulerProduct_continuation_ne_zero_of_norm_sub_le_of_sq_eq_normPowChar_of_admitsModulus
import Theorems.Thm_NumberField_TateGlobal_exists_eq_normPowChar_of_forall_mem_normOneIdeles
import Theorems.Thm_NumberField_TateGlobal_ite_isUnramifiedCharAt_normPowChar_apply_uniformizerIdele_eq_absNorm_cpow_neg
import Theorems.Thm_NumberField_TateGlobal_exists_differentiable_eq_partialEulerProduct_of_exists_mem_normOneIdeles_ne_one
import Theorems.Thm_NumberField_TateGlobal_ideleNorm_eq_prod_norm_infinitePlace_pow_mult_of_snd_eq_one
import Theorems.Thm_NumberField_summable_heightOneSpectrum_absNorm_rpow_neg_of_one_lt
import Theorems.Thm_NumberField_exists_differentiable_eq_sub_one_mul_dedekindZeta_and_apply_neg_two_mul_add_one_eq_zero
import Theorems.Thm_NumberField_hasProd_inv_one_sub_absNorm_cpow_neg_dedekindZeta
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_NumberField_TateGlobal_exists_pos_forall_partialEulerProduct_continuation_ne_zero_of_one_sub_div_log_le_re_of_admitsModulus
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

namespace R4ZF

theorem two_le_absNorm {K : Type} [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K)) :
    2 ≤ Ideal.absNorm v.asIdeal := by
  have h0 : Ideal.absNorm v.asIdeal ≠ 0 := by
    rw [Ne, Ideal.absNorm_eq_zero_iff]; exact v.ne_bot
  have h1 : Ideal.absNorm v.asIdeal ≠ 1 := by
    rw [Ne, Ideal.absNorm_eq_one_iff]; exact v.isPrime.ne_top
  omega

section sq
variable {K : Type} [Field K] [NumberField K]

theorem sq_apply (χ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ) (x : (AdeleRing (𝓞 K) K)ˣ) :
    (χ ^ 2) x = χ x ^ 2 := MonoidHom.pow_apply χ 2 x

theorem coe_sq_apply (χ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ) (x : (AdeleRing (𝓞 K) K)ˣ) :
    (((χ ^ 2) x : ℂˣ) : ℂ) = ((χ x : ℂˣ) : ℂ) ^ 2 := by
  rw [sq_apply, Units.val_pow_eq_pow_val]

theorem isIdeleClassChar_sq {χ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ} (h : IsIdeleClassChar (𝓞 K) K χ) :
    IsIdeleClassChar (𝓞 K) K (χ ^ 2) := fun u => by rw [sq_apply, h u, one_pow]

theorem isUnitaryChar_sq {χ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ} (h : IsUnitaryChar (𝓞 K) K χ) :
    IsUnitaryChar (𝓞 K) K (χ ^ 2) := fun x => by rw [coe_sq_apply, norm_pow, h x, one_pow]

theorem continuous_sq {χ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ} (h : Continuous χ) :
    Continuous ((χ ^ 2 : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ) : (AdeleRing (𝓞 K) K)ˣ → ℂˣ) := by
  have : (⇑(χ ^ 2 : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ)) = fun x => χ x ^ 2 := funext (sq_apply χ)
  rw [this]; exact h.pow 2

theorem admitsModulus_sq {χ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ} {𝔣 : Ideal (𝓞 K)}
    (h : HeckeCharacter.AdmitsModulus K χ 𝔣) : HeckeCharacter.AdmitsModulus K (χ ^ 2) 𝔣 :=
  fun u hu₁ hu₂ => by rw [sq_apply, h u hu₁ hu₂, one_pow]

theorem localChar_sq_apply (χ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ) (v : HeightOneSpectrum (𝓞 K))
    (t : (v.adicCompletion K)ˣ) : localChar (χ ^ 2) v t = (localChar χ v t) ^ 2 := by
  rw [localChar_apply, localChar_apply, sq_apply]

theorem isUnramifiedCharAt_sq {χ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ} {v : HeightOneSpectrum (𝓞 K)}
    (h : IsUnramifiedCharAt χ v) : IsUnramifiedCharAt (χ ^ 2) v :=
  fun t ht ht' => by rw [localChar_sq_apply, h t ht ht', one_pow]

theorem archLocalChar_sq_apply (χ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ) (w : InfinitePlace K)
    (a : (w.Completion)ˣ) :
    ((archLocalChar (χ ^ 2) w a : ℂˣ) : ℂ) = ((archLocalChar χ w a : ℂˣ) : ℂ) ^ 2 := by
  rw [archLocalChar_apply, archLocalChar_apply, coe_sq_apply]

theorem norm_coeff_le_one {χ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ} (hu : IsUnitaryChar (𝓞 K) K χ)
    (v : HeightOneSpectrum (𝓞 K)) [Decidable (IsUnramifiedCharAt χ v)] :
    ‖(if IsUnramifiedCharAt χ v then ((χ (uniformizerIdele K v) : ℂˣ) : ℂ) else 0)‖ ≤ 1 := by
  split_ifs
  · exact (hu _).le
  · simp

end sq

section arch
variable {K : Type} [Field K] [NumberField K]

omit [NumberField K] in
theorem exists_unit_extensionEmbedding_eq (w : InfinitePlace K) {r : ℝ} (hr : 0 < r) :
    ∃ a : (w.Completion)ˣ, Completion.extensionEmbedding w (a : w.Completion) = (r : ℂ) := by
  have hr0 : (r : ℂ) ≠ 0 := ofReal_ne_zero.mpr hr.ne'
  by_cases hw : w.IsReal
  · obtain ⟨x, hx⟩ := Completion.surjective_extensionEmbeddingOfIsReal hw r
    have hx' : Completion.extensionEmbedding w x = (r : ℂ) := by
      rw [← Completion.extensionEmbeddingOfIsReal_apply hw x, hx]
    have hx0 : x ≠ 0 := by
      rintro rfl
      rw [map_zero] at hx'
      exact hr0 hx'.symm
    exact ⟨Units.mk0 x hx0, hx'⟩
  · have hc : w.IsComplex := not_isReal_iff_isComplex.mp hw
    obtain ⟨x, hx⟩ := Completion.surjective_extensionEmbedding_of_isComplex hc (r : ℂ)
    have hx0 : x ≠ 0 := by
      rintro rfl
      rw [map_zero] at hx
      exact hr0 hx.symm
    exact ⟨Units.mk0 x hx0, hx⟩

omit [NumberField K] in
theorem norm_eq_of_extensionEmbedding_eq (w : InfinitePlace K) (a : w.Completion) {r : ℝ} (hr : 0 < r)
    (ha : Completion.extensionEmbedding w a = (r : ℂ)) : ‖a‖ = r := by
  have h := (Completion.isometry_extensionEmbedding w).norm_map_of_map_zero (map_zero _) a
  rw [ha, norm_real, Real.norm_eq_abs, abs_of_pos hr] at h
  exact h.symm

theorem ideleNorm_archCentralUnit (w : InfinitePlace K) (a : (w.Completion)ˣ) :
    ideleNorm K (AdelicVolume.archCentralUnit K w a) = ‖(a : w.Completion)‖ ^ w.mult := by
  classical
  rw [NumberField.TateGlobal.ideleNorm_eq_prod_norm_infinitePlace_pow_mult_of_snd_eq_one K _
    (AdelicVolume.archCentralUnit_snd w a)]
  rw [Finset.prod_eq_single w]
  · rw [AdelicVolume.archCentralUnit_fst_self]
  · intro w' _ hw'
    rw [AdelicVolume.archCentralUnit_fst_of_ne w a hw', norm_one, one_pow]
  · intro h; exact absurd (Finset.mem_univ w) h

theorem archLocalChar_normPowChar_apply (θ : ℝ) (w : InfinitePlace K) (a : (w.Completion)ˣ) {r : ℝ}
    (hr : 0 < r) (ha : Completion.extensionEmbedding w (a : w.Completion) = (r : ℂ)) :
    ((archLocalChar (normPowChar K θ) w a : ℂˣ) : ℂ) = (r : ℂ) ^ ((w.mult : ℂ) * (I * θ)) := by
  rw [archLocalChar_apply, coe_normPowChar_apply]
  show (((ideleNorm K (AdelicVolume.archCentralUnit K w a)) : ℝ) : ℂ) ^ (I * θ) = _
  rw [ideleNorm_archCentralUnit, norm_eq_of_extensionEmbedding_eq w a hr ha, ofReal_pow]
  have hlog : (log (r : ℂ) * (w.mult : ℂ)).im = 0 := by
    rw [← ofReal_log hr.le, ← ofReal_natCast, ← ofReal_mul, ofReal_im]
  symm
  rw [cpow_mul (x := (r : ℂ)) (y := (w.mult : ℂ)) (I * θ) (by rw [hlog]; exact neg_lt_zero.mpr Real.pi_pos)
    (by rw [hlog]; exact Real.pi_pos.le), cpow_natCast]

theorem eq_zero_of_forall_exp_mul_I_eq_one {d : ℝ} (h : ∀ u : ℝ, cexp ((u : ℂ) * (I * d)) = 1) : d = 0 := by
  by_contra hd
  have := h (Real.pi / d)
  have hrew : ((Real.pi / d : ℝ) : ℂ) * (I * d) = Real.pi * I := by
    have hd' : (d : ℂ) ≠ 0 := ofReal_ne_zero.mpr hd
    push_cast
    field_simp
  rw [hrew, exp_pi_mul_I] at this
  norm_num at this

theorem ofReal_exp_cpow (u : ℝ) (s : ℂ) : ((Real.exp u : ℝ) : ℂ) ^ s = cexp ((u : ℂ) * s) := by
  rw [cpow_def_of_ne_zero (ofReal_ne_zero.mpr (Real.exp_pos u).ne'), ← ofReal_log (Real.exp_pos u).le,
    Real.log_exp]

theorem abs_theta_le (χ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ) (θ : ℝ) (hsq : χ ^ 2 = normPowChar K θ)
    (φ : InfinitePlace K → ℝ)
    (hφ : ∀ (w : InfinitePlace K) (a : (w.Completion)ˣ) (r : ℝ), 0 < r →
        Completion.extensionEmbedding w (a : w.Completion) = (r : ℂ) →
        ((archLocalChar χ w a : ℂˣ) : ℂ) = (r : ℂ) ^ (I * φ w))
    (w : InfinitePlace K) : |θ| ≤ 2 * |φ w| := by
  have key : ∀ u : ℝ, cexp ((u : ℂ) * (I * ((2 * φ w - w.mult * θ : ℝ) : ℂ))) = 1 := by
    intro u
    obtain ⟨a, ha⟩ := exists_unit_extensionEmbedding_eq w (Real.exp_pos u)
    have h1 := hφ w a _ (Real.exp_pos u) ha
    have h2 := archLocalChar_normPowChar_apply θ w a (Real.exp_pos u) ha
    have h3 : ((archLocalChar (χ ^ 2) w a : ℂˣ) : ℂ) = ((Real.exp u : ℝ) : ℂ) ^ ((2 : ℕ) * (I * φ w)) := by
      rw [archLocalChar_sq_apply, h1, cpow_nat_mul]
    rw [hsq, h2, ofReal_exp_cpow, ofReal_exp_cpow] at h3
    have h4 : cexp ((u : ℂ) * ((2 : ℕ) * (I * φ w))) * (cexp ((u : ℂ) * ((w.mult : ℂ) * (I * θ))))⁻¹ = 1 := by
      rw [h3, mul_inv_cancel₀ (exp_ne_zero _)]
    rw [← exp_neg, ← exp_add] at h4
    rw [← h4]
    congr 1
    push_cast
    ring
  have hd := eq_zero_of_forall_exp_mul_I_eq_one key
  have hm : (1 : ℝ) ≤ w.mult := by
    have := w.mult_pos
    exact_mod_cast this
  have hθ : θ = 2 * φ w / w.mult := by
    field_simp
    linarith
  rw [hθ, abs_div, abs_mul, abs_of_pos (by norm_num : (0:ℝ) < 2), abs_of_pos (by linarith : (0:ℝ) < w.mult)]
  rw [div_le_iff₀ (by linarith)]
  nlinarith [abs_nonneg (φ w)]

end arch

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

theorem norm_nC_cpow_neg (v : HeightOneSpectrum (𝓞 K)) (s : ℂ) :
    ‖nC v ^ (-s)‖ = (Ideal.absNorm v.asIdeal : ℝ) ^ (-s.re) := by
  unfold nC
  rw [Complex.norm_natCast_cpow_of_pos (nC_pos v) (-s), Complex.neg_re]

theorem norm_nC_cpow_neg_lt_one {s : ℂ} (hs : 0 < s.re) (v : HeightOneSpectrum (𝓞 K)) :
    ‖nC v ^ (-s)‖ < 1 := by
  rw [norm_nC_cpow_neg]
  have h1 : (1 : ℝ) < (Ideal.absNorm v.asIdeal : ℝ) := by
    exact_mod_cast lt_of_lt_of_le one_lt_two (two_le_absNorm v)
  exact Real.rpow_lt_one_of_one_lt_of_neg h1 (by linarith)

theorem one_sub_ne_zero {s : ℂ} (hs : 0 < s.re) (v : HeightOneSpectrum (𝓞 K)) :
    (1 : ℂ) - nC v ^ (-s) ≠ 0 := by
  intro h
  have hlt := norm_nC_cpow_neg_lt_one hs v
  rw [sub_eq_zero] at h
  rw [← h, norm_one] at hlt
  exact lt_irrefl _ hlt

def eulerFn (T : Finset (HeightOneSpectrum (𝓞 K))) (c : HeightOneSpectrum (𝓞 K) → ℂ) (s : ℂ) : ℂ :=
  ∏' v : {v : HeightOneSpectrum (𝓞 K) // v ∉ T},
    (1 - c v.1 * (((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) ^ (-s)))⁻¹

def corr (T : Finset (HeightOneSpectrum (𝓞 K))) (s : ℂ) : ℂ := ∏ v ∈ T, (1 - nC v ^ (-s))

theorem differentiable_corr (T : Finset (HeightOneSpectrum (𝓞 K))) : Differentiable ℂ (corr (K := K) T) := by
  unfold corr
  refine Differentiable.fun_finsetProd fun v _ => ?_
  refine (differentiable_const _).sub ?_
  refine Differentiable.const_cpow differentiable_neg (Or.inl ?_)
  unfold nC
  exact_mod_cast (nC_pos v).ne'

theorem corr_ne_zero (T : Finset (HeightOneSpectrum (𝓞 K))) {s : ℂ} (hs : 0 < s.re) : corr T s ≠ 0 :=
  Finset.prod_ne_zero_iff.mpr fun v _ => one_sub_ne_zero hs v

theorem hasProd_partial {s : ℂ} (hs : 1 < s.re) (T : Finset (HeightOneSpectrum (𝓞 K))) :
    HasProd (fun v : {v : HeightOneSpectrum (𝓞 K) // v ∉ T} => (1 - nC v.1 ^ (-s))⁻¹)
      (cexp (∑' v : {v : HeightOneSpectrum (𝓞 K) // v ∉ T}, -log (1 - nC v.1 ^ (-s)))) := by
  have hs0 : 0 < s.re := lt_trans zero_lt_one hs
  have hne : ∀ v : HeightOneSpectrum (𝓞 K), (1 : ℂ) - nC v ^ (-s) ≠ 0 := one_sub_ne_zero hs0
  have hn : Summable fun v : HeightOneSpectrum (𝓞 K) => ‖nC v ^ (-s)‖ := by
    refine (NumberField.summable_heightOneSpectrum_absNorm_rpow_neg_of_one_lt K hs).congr fun v => ?_
    rw [norm_nC_cpow_neg]
  have hsub : Summable fun v : {v : HeightOneSpectrum (𝓞 K) // v ∉ T} => nC v.1 ^ (-s) :=
    (hn.subtype {v | v ∉ T}).of_norm
  have hg : Summable fun v : {v : HeightOneSpectrum (𝓞 K) // v ∉ T} => -log (1 - nC v.1 ^ (-s)) :=
    hsub.clog_one_sub.neg
  have H := hg.hasSum.cexp
  have hcongr : (cexp ∘ fun v : {v : HeightOneSpectrum (𝓞 K) // v ∉ T} => -log (1 - nC v.1 ^ (-s))) =
      fun v => (1 - nC v.1 ^ (-s))⁻¹ := by
    funext v
    simp only [Function.comp_apply, exp_neg, exp_log (hne v.1)]
  rw [hcongr] at H
  exact H

theorem eulerFn_one_eq {s : ℂ} (hs : 1 < s.re) (T : Finset (HeightOneSpectrum (𝓞 K))) :
    eulerFn T (fun _ => 1) s = dedekindZeta K s * corr T s := by
  have hs0 : 0 < s.re := lt_trans zero_lt_one hs
  set E : ℂ := cexp (∑' v : {v : HeightOneSpectrum (𝓞 K) // v ∉ T}, -log (1 - nC v.1 ^ (-s))) with hE
  have hP := hasProd_partial (K := K) hs T
  have hEq : eulerFn T (fun _ => 1) s = E := by
    unfold eulerFn
    have := hP.tprod_eq
    simp only [one_mul]
    exact this
  have hE' : HasProd ((fun v : HeightOneSpectrum (𝓞 K) => (1 - nC v ^ (-s))⁻¹) ∘ (↑) :
      ((↑T : Set (HeightOneSpectrum (𝓞 K)))ᶜ : Set (HeightOneSpectrum (𝓞 K))) → ℂ) E := hP
  have hG : HasProd ((fun v : HeightOneSpectrum (𝓞 K) => (1 - nC v ^ (-s))⁻¹) ∘ (↑) :
      (↑T : Set (HeightOneSpectrum (𝓞 K))) → ℂ) (∏ v ∈ T, (1 - nC v ^ (-s))⁻¹) := Finset.hasProd T _
  have hall := hG.mul_isCompl isCompl_compl hE'
  have hζ : HasProd (fun v : HeightOneSpectrum (𝓞 K) => (1 - nC v ^ (-s))⁻¹) (dedekindZeta K s) :=
    NumberField.hasProd_inv_one_sub_absNorm_cpow_neg_dedekindZeta K s hs
  have heq : (∏ v ∈ T, (1 - nC v ^ (-s))⁻¹) * E = dedekindZeta K s := HasProd.unique hall hζ
  have hne : corr T s ≠ 0 := corr_ne_zero T hs0
  have hinv : (∏ v ∈ T, (1 - nC v ^ (-s))⁻¹) = (corr T s)⁻¹ := by
    unfold corr; exact Finset.prod_inv_distrib _
  rw [hinv] at heq
  rw [hEq]
  calc E = corr T s * ((corr T s)⁻¹ * E) := by rw [← mul_assoc, mul_inv_cancel₀ hne, one_mul]
    _ = corr T s * dedekindZeta K s := by rw [heq]
    _ = dedekindZeta K s * corr T s := mul_comm _ _

theorem exists_Z (T : Finset (HeightOneSpectrum (𝓞 K))) :
    ∃ Z : ℂ → ℂ, Differentiable ℂ Z ∧ Z 1 ≠ 0 ∧
      ∀ s : ℂ, 1 < s.re → Z s = (s - 1) * eulerFn T (fun _ => 1) s := by
  obtain ⟨R, hRd, hR1, hReq, -⟩ :=
    NumberField.exists_differentiable_eq_sub_one_mul_dedekindZeta_and_apply_neg_two_mul_add_one_eq_zero K
  refine ⟨fun s => R s * corr T s, hRd.mul (differentiable_corr T), ?_, fun s hs => ?_⟩
  · show R 1 * corr T 1 ≠ 0
    exact mul_ne_zero hR1 (corr_ne_zero T (by simp))
  · show R s * corr T s = (s - 1) * eulerFn T (fun _ => 1) s
    rw [hReq s hs, eulerFn_one_eq hs T, mul_assoc]

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

theorem differentiableAt_and_ne_zero_one (T : Finset (HeightOneSpectrum (𝓞 K))) (s : ℂ) (hs : 1 < s.re) :
    DifferentiableAt ℂ (fun z : ℂ => ∏' v : {v : HeightOneSpectrum (𝓞 K) // v ∉ T},
        (1 - (((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) ^ (-z)))⁻¹) s ∧
      (∏' v : {v : HeightOneSpectrum (𝓞 K) // v ∉ T},
        (1 - (((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) ^ (-s)))⁻¹) ≠ 0 := by
  have h := differentiableAt_and_ne_zero T (fun _ => 1) (fun _ => by rw [norm_one]) s hs
  simp only [one_mul] at h
  exact h

theorem exists_C₀ (T : Finset (HeightOneSpectrum (𝓞 K))) (Z : ℂ → ℂ) (hZd : Differentiable ℂ Z)
    (hZ1 : Z 1 ≠ 0)
    (hZeq : ∀ s : ℂ, 1 < s.re → Z s = (s - 1) * ∏' v : {v : HeightOneSpectrum (𝓞 K) // v ∉ T},
        (1 - (((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) ^ (-s)))⁻¹) :
    ∃ C₀ : ℝ, 0 ≤ C₀ ∧ ∀ σ : ℝ, 1 < σ → σ ≤ 2 →
      -(deriv (fun z : ℂ => ∏' v : {v : HeightOneSpectrum (𝓞 K) // v ∉ T},
            (1 - (((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) ^ (-z)))⁻¹) (σ : ℂ) /
          ∏' v : {v : HeightOneSpectrum (𝓞 K) // v ∉ T},
            (1 - (((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) ^ (-(σ : ℂ))))⁻¹).re ≤ 1 / (σ - 1) + C₀ := by
  set E₀ : ℂ → ℂ := fun z : ℂ => ∏' v : {v : HeightOneSpectrum (𝓞 K) // v ∉ T},
      (1 - (((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) ^ (-z)))⁻¹ with hE₀

  set S : Set ℂ := (fun σ : ℝ => (σ : ℂ)) '' Set.Icc (1 : ℝ) 2 with hS
  have hScomp : IsCompact S := (isCompact_Icc).image continuous_ofReal
  have hZne : ∀ z ∈ S, Z z ≠ 0 := by
    rintro z ⟨σ, hσ, rfl⟩
    rcases eq_or_lt_of_le hσ.1 with h | h
    · rw [← h]; simpa using hZ1
    · rw [hZeq _ (by simpa using h)]
      refine mul_ne_zero ?_ (differentiableAt_and_ne_zero_one T _ (by simpa using h)).2
      rw [sub_ne_zero]
      intro h1
      have := congrArg Complex.re h1
      simp at this
      linarith
  have hcontZ : Continuous Z := hZd.continuous
  have hcontZ' : Continuous (deriv Z) :=
    (analyticOnNhd_univ_iff_differentiable.mpr hZd).deriv.continuousOn.comp_continuous continuous_id
      (fun _ => Set.mem_univ _) |>.congr (fun _ => rfl)
  have hg : ContinuousOn (fun z => deriv Z z / Z z) S :=
    (hcontZ'.continuousOn.div hcontZ.continuousOn hZne)
  obtain ⟨C₀', hC₀'⟩ := hScomp.exists_bound_of_continuousOn hg
  refine ⟨max C₀' 0, le_max_right _ _, fun σ hσ hσ2 => ?_⟩
  have hσS : (σ : ℂ) ∈ S := ⟨σ, ⟨hσ.le, hσ2⟩, rfl⟩
  have hZσ : Z σ ≠ 0 := hZne _ hσS
  have hσ1 : (σ : ℂ) - 1 ≠ 0 := by
    rw [sub_ne_zero]; intro h; have := congrArg Complex.re h; simp at this; linarith

  have hVopen : IsOpen {s : ℂ | 1 < s.re} := isOpen_lt continuous_const continuous_re
  have hσV : (σ : ℂ) ∈ {s : ℂ | 1 < s.re} := by simpa using hσ
  have hev : E₀ =ᶠ[𝓝 (σ : ℂ)] fun s => Z s / (s - 1) := by
    refine Filter.eventuallyEq_of_mem (hVopen.mem_nhds hσV) fun z hz => ?_
    have hz1 : z - 1 ≠ 0 := by
      rw [sub_ne_zero]; intro h; rw [h] at hz; simp at hz
    show E₀ z = Z z / (z - 1)
    rw [hZeq z hz, hE₀]
    field_simp
  have hderivE₀ : deriv E₀ (σ : ℂ) = (deriv Z σ * ((σ : ℂ) - 1) - Z σ * 1) / ((σ : ℂ) - 1) ^ 2 := by
    rw [hev.deriv_eq]
    have hZ' : HasDerivAt Z (deriv Z σ) (σ : ℂ) := hZd.differentiableAt.hasDerivAt
    have hd : HasDerivAt (fun s : ℂ => s - 1) 1 (σ : ℂ) := (hasDerivAt_id _).sub_const 1
    exact (hZ'.div hd hσ1).deriv
  have hE₀σ : E₀ (σ : ℂ) = Z σ / ((σ : ℂ) - 1) := hev.eq_of_nhds
  have hratio : deriv E₀ (σ : ℂ) / E₀ (σ : ℂ) = deriv Z σ / Z σ - 1 / ((σ : ℂ) - 1) := by
    rw [hderivE₀, hE₀σ]
    field_simp
  show -(deriv E₀ (σ : ℂ) / E₀ (σ : ℂ)).re ≤ 1 / (σ - 1) + max C₀' 0
  rw [hratio, sub_re, neg_sub]
  have h1 : (1 / ((σ : ℂ) - 1)).re = 1 / (σ - 1) := by
    rw [← ofReal_one, ← ofReal_sub, ← ofReal_div, ofReal_re]
  rw [h1]
  have h2 : -(deriv Z σ / Z σ).re ≤ ‖deriv Z σ / Z σ‖ := by
    have := abs_re_le_norm (deriv Z σ / Z σ)
    have := neg_le_of_abs_le this
    linarith
  have h3 : ‖deriv Z σ / Z σ‖ ≤ max C₀' 0 := (hC₀' _ hσS).trans (le_max_left _ _)
  linarith

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
  have hE₀pos : 0 < ‖E₀σ‖ := by
    have h := (differentiableAt_and_ne_zero_one T (σ : ℂ) (by simpa using hσ)).2
    exact norm_pos_iff.mpr h
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

section threefourone
variable {K : Type} [Field K] [NumberField K]

open scoped Classical in
theorem three_four_one_L (T : Finset (HeightOneSpectrum (𝓞 K)))
    (χ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ) (hu : IsUnitaryChar (𝓞 K) K χ) (σ : ℝ) (hσ : 1 < σ) (t : ℝ)
    (F₁ F₂ : ℂ → ℂ)
    (h₁ : F₁ =ᶠ[𝓝 ((σ : ℂ) + t * I)] fun z : ℂ => ∏' v : {v : HeightOneSpectrum (𝓞 K) // v ∉ T},
        (1 - (if IsUnramifiedCharAt χ v.1 then ((χ (uniformizerIdele K v.1) : ℂˣ) : ℂ) else 0) *
          (((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) ^ (-z)))⁻¹)
    (h₂ : F₂ =ᶠ[𝓝 ((σ : ℂ) + 2 * t * I)] fun z : ℂ => ∏' v : {v : HeightOneSpectrum (𝓞 K) // v ∉ T},
        (1 - (if IsUnramifiedCharAt (χ ^ 2) v.1 then (((χ ^ 2) (uniformizerIdele K v.1) : ℂˣ) : ℂ) else 0) *
          (((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) ^ (-z)))⁻¹) :
    0 ≤ 3 * (-(deriv (fun z : ℂ => ∏' v : {v : HeightOneSpectrum (𝓞 K) // v ∉ T},
              (1 - (((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) ^ (-z)))⁻¹) (σ : ℂ) /
            ∏' v : {v : HeightOneSpectrum (𝓞 K) // v ∉ T},
              (1 - (((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) ^ (-(σ : ℂ))))⁻¹)).re
      + 4 * (-(deriv F₁ ((σ : ℂ) + t * I) / F₁ ((σ : ℂ) + t * I))).re
      + (-(deriv F₂ ((σ : ℂ) + 2 * t * I) / F₂ ((σ : ℂ) + 2 * t * I))).re := by
  have hsum : ∀ σ' : ℝ, 1 < σ' → Summable fun v : {v : HeightOneSpectrum (𝓞 K) // v ∉ T} =>
      ((Ideal.absNorm v.1.asIdeal : ℕ) : ℝ) ^ (-σ') := fun σ' hσ' =>
    (NumberField.summable_heightOneSpectrum_absNorm_rpow_neg_of_one_lt K hσ').subtype _
  have h := EulerProduct.three_mul_re_neg_deriv_tprod_div_add_four_mul_add_nonneg_of_norm_le_one
    (fun v : {v : HeightOneSpectrum (𝓞 K) // v ∉ T} => Ideal.absNorm v.1.asIdeal)
    (fun v => two_le_absNorm v.1)
    (fun v => if IsUnramifiedCharAt χ v.1 then ((χ (uniformizerIdele K v.1) : ℂˣ) : ℂ) else 0)
    (fun v => if IsUnramifiedCharAt (χ ^ 2) v.1 then (((χ ^ 2) (uniformizerIdele K v.1) : ℂˣ) : ℂ) else 0)
    (fun v => norm_coeff_le_one hu v.1) (fun v => norm_coeff_le_one (isUnitaryChar_sq hu) v.1)
    (fun v => ?_) hsum σ t hσ
  · rw [h₁.deriv_eq, h₁.eq_of_nhds, h₂.deriv_eq, h₂.eq_of_nhds]
    exact h
  · by_cases hv : IsUnramifiedCharAt χ v.1
    · right
      rw [if_pos hv, if_pos (isUnramifiedCharAt_sq hv), coe_sq_apply]
    · left
      rw [if_neg hv]

end threefourone

section main
variable (K : Type) [Field K] [NumberField K]

theorem re_ofReal_add_mul_I (σ t : ℝ) : ((σ : ℂ) + t * I).re = σ := by simp

theorem im_ofReal_add_mul_I (σ t : ℝ) : ((σ : ℂ) + t * I).im = t := by simp

theorem disc_bounds {σ u r : ℝ} {z : ℂ} (hz : z ∈ Metric.closedBall ((σ : ℂ) + u * I) r) :
    |z.re - σ| ≤ r ∧ |z.im - u| ≤ r := by
  rw [Metric.mem_closedBall, dist_eq_norm] at hz
  have hre := abs_re_le_norm (z - ((σ : ℂ) + u * I))
  have him := abs_im_le_norm (z - ((σ : ℂ) + u * I))
  simp only [sub_re, add_re, ofReal_re, mul_re, I_re, mul_zero, ofReal_im, I_im, mul_one, sub_self,
    add_zero, sub_im, add_im, mul_im, zero_add] at hre him
  exact ⟨hre.trans hz, him.trans hz⟩

set_option maxHeartbeats 24000000 in
open scoped Classical in
theorem main (T : Finset (HeightOneSpectrum (𝓞 K))) (𝔣 : Ideal (𝓞 K)) :
    ∃ c : ℝ, 0 < c ∧
      ∀ (χ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ), IsIdeleClassChar (𝓞 K) K χ → Continuous χ →
        IsUnitaryChar (𝓞 K) K χ → (∃ x ∈ normOneIdeles K, χ x ≠ 1) →
        HeckeCharacter.AdmitsModulus K χ 𝔣 → (∀ v ∉ T, IsUnramifiedCharAt χ v) →
      ∀ (φ : InfinitePlace K → ℝ) (k : InfinitePlace K → ℤ),
        (∀ (w : InfinitePlace K) (a : (w.Completion)ˣ) (r : ℝ), 0 < r →
            Completion.extensionEmbedding w (a : w.Completion) = (r : ℂ) →
            ((archLocalChar χ w a : ℂˣ) : ℂ) = (r : ℂ) ^ (Complex.I * φ w)) →
        (∀ (w : InfinitePlace K) (a : (w.Completion)ˣ),
            ‖Completion.extensionEmbedding w (a : w.Completion)‖ = 1 →
            ((archLocalChar χ w a : ℂˣ) : ℂ) = (Completion.extensionEmbedding w (a : w.Completion)) ^ (k w)) →
      ∀ (L : ℂ → ℂ), Differentiable ℂ L →
        (∀ s : ℂ, 1 < s.re → L s = ∏' v : {v : HeightOneSpectrum (𝓞 K) // v ∉ T},
            (1 - (if IsUnramifiedCharAt χ v.1 then ((χ (uniformizerIdele K v.1) : ℂˣ) : ℂ) else 0) *
              (((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) ^ (-s)))⁻¹) →
      ∀ s : ℂ, 1 - c / Real.log (2 + |s.im| + ∑ w : InfinitePlace K, (|φ w| + |(k w : ℝ)|)) ≤ s.re →
        L s ≠ 0 := by

  obtain ⟨CS, AS, hCS, hAS, hS⟩ :=
    NumberField.TateGlobal.exists_forall_norm_partialEulerProduct_continuation_le_rpow_of_re_mem_Icc_of_admitsModulus
      K T 𝔣
  obtain ⟨CZ, AZ, hCZ, hAZ, hZs⟩ :=
    NumberField.TateGlobal.exists_forall_norm_sub_one_mul_partialDedekindZeta_continuation_le_rpow_of_re_mem_Icc K T
  obtain ⟨δD, hδD0, hδDhalf, hD⟩ :=
    NumberField.TateGlobal.exists_pos_forall_partialEulerProduct_continuation_ne_zero_of_norm_sub_le_of_sq_eq_normPowChar_of_admitsModulus
      K T 𝔣
  obtain ⟨Z, hZd, hZ1, hZeq'⟩ := exists_Z (K := K) T
  have hZeq : ∀ s : ℂ, 1 < s.re → Z s = (s - 1) * ∏' v : {v : HeightOneSpectrum (𝓞 K) // v ∉ T},
      (1 - (((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) ^ (-s)))⁻¹ := by
    intro s hs; rw [hZeq' s hs]; simp only [eulerFn, one_mul]
  obtain ⟨C₀, hC₀0, hC₀⟩ := exists_C₀ T Z hZd hZ1 hZeq

  set CZ' : ℝ := max (CZ * (2 : ℝ) ^ AZ) 1 with hCZ'def
  have hCZ'1 : 1 ≤ CZ' := le_max_right _ _
  have hZle : ∀ σ : ℝ, 1 < σ → σ ≤ 2 → ‖Z σ‖ ≤ CZ' := by
    intro σ hσ hσ2
    have h := hZs Z hZd hZeq σ (by rw [ofReal_re]; linarith) (by rw [ofReal_re]; linarith)
    rw [ofReal_im, abs_zero, add_zero] at h
    exact h.trans (le_max_left _ _)

  set r : ℝ := min (1 / 2) (δD / 2) with hrdef
  have hr0 : 0 < r := lt_min (by norm_num) (by linarith)
  have hrhalf : r ≤ 1 / 2 := min_le_left _ _
  have hrδ : r ≤ δD / 2 := min_le_right _ _
  have hr1 : r ≤ 1 := by linarith

  set Abig : ℝ := max AS AZ with hAbigdef
  have hASle : AS ≤ Abig := le_max_left _ _
  have hAZle : AZ ≤ Abig := le_max_right _ _
  have hAbig0 : 0 < Abig := hAS.trans_le hASle
  set Cbig : ℝ := max (max (max (max (max CS (2 * CZ / δD)) (CZ' ^ 2)) (Real.exp C₀)) (Real.exp (1 / r))) 1
    with hCbigdef
  have hCbig1 : 1 ≤ Cbig := le_max_right _ _
  have hCbig0 : 0 < Cbig := one_pos.trans_le hCbig1
  have hCS_le : CS ≤ Cbig :=
    (le_max_left _ _).trans ((le_max_left _ _).trans ((le_max_left _ _).trans ((le_max_left _ _).trans (le_max_left _ _))))
  have h2CZ_le : 2 * CZ / δD ≤ Cbig :=
    (le_max_right _ _).trans ((le_max_left _ _).trans ((le_max_left _ _).trans ((le_max_left _ _).trans (le_max_left _ _))))
  have hCZ'2_le : CZ' ^ 2 ≤ Cbig :=
    (le_max_right _ _).trans ((le_max_left _ _).trans ((le_max_left _ _).trans (le_max_left _ _)))
  have hexpC₀ : Real.exp C₀ ≤ Cbig := (le_max_right _ _).trans ((le_max_left _ _).trans (le_max_left _ _))
  have hexpr : Real.exp (1 / r) ≤ Cbig := (le_max_right _ _).trans (le_max_left _ _)
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlogCbig : 0 ≤ Real.log Cbig := Real.log_nonneg hCbig1
  set D : ℝ := Real.log Cbig / Real.log 2 + Abig * (Real.log 3 / Real.log 2 + 1) with hDdef
  have hlog3 : 0 ≤ Real.log 3 := Real.log_nonneg (by norm_num)
  have hD0 : 0 < D := by
    have h1 : 0 ≤ Real.log Cbig / Real.log 2 := by positivity
    have h2 : 0 < Abig * (Real.log 3 / Real.log 2 + 1) := by positivity
    linarith
  refine ⟨min (r / (40000 * D)) (δD / 4), lt_min (by positivity) (by linarith), ?_⟩
  intro χ hχ hχc hχu hχ1 hχ𝔣 hT φ k hφ hk L hLd hLeq s hs hLs

  set β : ℝ := s.re with hβdef
  set γ : ℝ := s.im with hγdef
  set Q : ℝ := ∑ w : InfinitePlace K, (|φ w| + |(k w : ℝ)|) with hQdef
  have hQ0 : 0 ≤ Q := Finset.sum_nonneg fun w _ => by positivity
  set 𝔮 : ℝ := 2 + |γ| + Q with h𝔮def
  have h𝔮2 : 2 ≤ 𝔮 := by rw [h𝔮def]; linarith [abs_nonneg γ]
  have h𝔮0 : 0 < 𝔮 := by linarith
  have hlog𝔮2 : Real.log 2 ≤ Real.log 𝔮 := Real.log_le_log (by norm_num) h𝔮2
  have hlog𝔮0 : 0 < Real.log 𝔮 := hlog2.trans_le hlog𝔮2
  have hsβγ : s = (β : ℂ) + γ * I := (re_add_im s).symm
  have hcmin1 : min (r / (40000 * D)) (δD / 4) ≤ r / (40000 * D) := min_le_left _ _
  have hcmin2 : min (r / (40000 * D)) (δD / 4) ≤ δD / 4 := min_le_right _ _

  set cχ : HeightOneSpectrum (𝓞 K) → ℂ := fun v =>
    if IsUnramifiedCharAt χ v then ((χ (uniformizerIdele K v) : ℂˣ) : ℂ) else 0 with hcχdef
  have hcχ : ∀ v, ‖cχ v‖ ≤ 1 := fun v => norm_coeff_le_one hχu v
  have hLnz : ∀ z : ℂ, 1 < z.re → L z ≠ 0 := fun z hz => by
    rw [hLeq z hz]; exact (differentiableAt_and_ne_zero T cχ hcχ z hz).2
  have hβ1 : β ≤ 1 := by
    by_contra h
    push Not at h
    exact hLnz s h hLs

  set 𝓛 : ℝ := Real.log Cbig + Abig * Real.log (3 * 𝔮) with h𝓛def
  have h3𝔮 : 1 ≤ 3 * 𝔮 := by linarith
  have h3𝔮0 : 0 < 3 * 𝔮 := by linarith
  have hexp𝓛 : Real.exp 𝓛 = Cbig * (3 * 𝔮) ^ Abig := by
    rw [h𝓛def, Real.exp_add, Real.exp_log hCbig0, Real.rpow_def_of_pos h3𝔮0, mul_comm (Real.log _)]
  have hlog3𝔮 : 0 ≤ Real.log (3 * 𝔮) := Real.log_nonneg h3𝔮
  have h𝓛log : Real.log Cbig ≤ 𝓛 := by
    rw [h𝓛def]; nlinarith
  have h𝓛C₀ : C₀ ≤ 𝓛 := ((Real.le_log_iff_exp_le hCbig0).mpr hexpC₀).trans h𝓛log
  have hr𝓛 : 1 ≤ r * 𝓛 := by
    have h1 : 1 / r ≤ Real.log Cbig := (Real.le_log_iff_exp_le hCbig0).mpr hexpr
    have h2 : 1 ≤ r * Real.log Cbig := by
      rw [div_le_iff₀ hr0] at h1; linarith
    nlinarith
  have h𝓛0 : 0 < 𝓛 := by nlinarith
  have h𝓛D : 𝓛 ≤ D * Real.log 𝔮 := by
    rw [h𝓛def, hDdef, Real.log_mul (by norm_num) h𝔮0.ne']
    have h1 : Real.log Cbig ≤ Real.log Cbig / Real.log 2 * Real.log 𝔮 := by
      rw [div_mul_eq_mul_div, le_div_iff₀ hlog2]
      exact mul_le_mul_of_nonneg_left hlog𝔮2 hlogCbig
    have h2 : Real.log 3 ≤ Real.log 3 / Real.log 2 * Real.log 𝔮 := by
      rw [div_mul_eq_mul_div, le_div_iff₀ hlog2]
      exact mul_le_mul_of_nonneg_left hlog𝔮2 hlog3
    have h3 : Abig * (Real.log 3 + Real.log 𝔮) ≤ Abig * (Real.log 3 / Real.log 2 + 1) * Real.log 𝔮 := by
      rw [mul_assoc]
      refine mul_le_mul_of_nonneg_left ?_ hAbig0.le
      nlinarith
    nlinarith

  have hbnd : ∀ (C A x : ℝ), 0 ≤ C → C ≤ Cbig → 0 < A → A ≤ Abig → 1 ≤ x → x ≤ 3 * 𝔮 →
      C * x ^ A ≤ Real.exp 𝓛 := by
    intro C A x hC hCle hA hAle hx1 hxle
    rw [hexp𝓛]
    have h1 : x ^ A ≤ (3 * 𝔮) ^ A := Real.rpow_le_rpow (by linarith) hxle hA.le
    have h2 : (3 * 𝔮) ^ A ≤ (3 * 𝔮) ^ Abig := Real.rpow_le_rpow_of_exponent_le h3𝔮 hAle
    exact mul_le_mul hCle (h1.trans h2) (Real.rpow_nonneg (by linarith) _) hCbig0.le

  have hlo_conv : ∀ σ : ℝ, (σ - 1) ^ 2 * Real.exp (-𝓛) ≤ ((σ - 1) / CZ') ^ 2 := by
    intro σ
    have h1 : CZ' ^ 2 ≤ Real.exp 𝓛 := by
      refine hCZ'2_le.trans ?_
      rw [hexp𝓛]
      exact le_mul_of_one_le_right hCbig0.le (Real.one_le_rpow h3𝔮 hAbig0.le)
    rw [div_pow, Real.exp_neg, div_eq_mul_inv]
    exact mul_le_mul_of_nonneg_left (inv_anti₀ (by positivity) h1) (sq_nonneg _)

  have hdisc_re : ∀ {σ u : ℝ} {z : ℂ}, 1 < σ → σ ≤ 1 + r → z ∈ Metric.closedBall ((σ : ℂ) + u * I) r →
      -1 / 2 ≤ z.re ∧ z.re ≤ 5 / 2 ∧ |z.im - u| ≤ r := by
    intro σ u z hσ hσr hz
    obtain ⟨hre, him⟩ := disc_bounds hz
    have h := abs_le.mp hre
    exact ⟨by linarith, by linarith, him⟩

  have hLan : ∀ σ : ℝ, 1 < σ → σ ≤ 1 + r →
      AnalyticOnNhd ℂ L (Metric.closedBall ((σ : ℂ) + γ * I) r) := fun _ _ _ =>
    (analyticOnNhd_univ_iff_differentiable.mpr hLd).mono (Set.subset_univ _)
  have hLup : ∀ σ : ℝ, 1 < σ → σ ≤ 1 + r →
      ∀ z ∈ Metric.closedBall ((σ : ℂ) + γ * I) r, ‖L z‖ ≤ Real.exp 𝓛 := by
    intro σ hσ hσr z hz
    obtain ⟨hz1, hz2, him⟩ := hdisc_re hσ hσr hz
    have h := hS χ hχ hχc hχu hχ1 hχ𝔣 hT φ k hφ hk L hLd hLeq z hz1 hz2
    refine h.trans (hbnd CS AS _ hCS.le hCS_le hAS hASle (by linarith [abs_nonneg z.im]) ?_)
    have h1 : |z.im| ≤ |γ| + r := by
      have := abs_sub_abs_le_abs_sub z.im γ; linarith
    show 2 + |z.im| + Q ≤ 3 * 𝔮
    rw [h𝔮def]; linarith [abs_nonneg γ]
  have hLlo : ∀ σ : ℝ, 1 < σ → σ ≤ 1 + r →
      (σ - 1) ^ 2 * Real.exp (-𝓛) ≤ ‖L ((σ : ℂ) + γ * I)‖ := by
    intro σ hσ hσr
    refine (hlo_conv σ).trans ?_
    rw [hLeq _ (by rw [re_ofReal_add_mul_I]; exact hσ)]
    exact sq_le_norm_tprod T cχ hcχ Z hZeq CZ' hCZ'1 hZle σ γ hσ (by linarith)
  have hLev : ∀ σ : ℝ, 1 < σ →
      L =ᶠ[𝓝 ((σ : ℂ) + γ * I)] fun z : ℂ => ∏' v : {v : HeightOneSpectrum (𝓞 K) // v ∉ T},
        (1 - (if IsUnramifiedCharAt χ v.1 then ((χ (uniformizerIdele K v.1) : ℂˣ) : ℂ) else 0) *
          (((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) ^ (-z)))⁻¹ := by
    intro σ hσ
    have hVopen : IsOpen {z : ℂ | 1 < z.re} := isOpen_lt continuous_const continuous_re
    exact Filter.eventuallyEq_of_mem (hVopen.mem_nhds (by show 1 < ((σ : ℂ) + γ * I).re; simpa using hσ))
      fun z hz => hLeq z hz

  have finish : ∀ F₂ : ℂ → ℂ,
      (∀ z : ℂ, 1 < z.re → F₂ z ≠ 0) →
      (∀ σ : ℝ, 1 < σ → σ ≤ 1 + r → AnalyticOnNhd ℂ F₂ (Metric.closedBall ((σ : ℂ) + 2 * γ * I) r)) →
      (∀ σ : ℝ, 1 < σ → σ ≤ 1 + r →
        ∀ z ∈ Metric.closedBall ((σ : ℂ) + 2 * γ * I) r, ‖F₂ z‖ ≤ Real.exp 𝓛) →
      (∀ σ : ℝ, 1 < σ → σ ≤ 1 + r → (σ - 1) ^ 2 * Real.exp (-𝓛) ≤ ‖F₂ ((σ : ℂ) + 2 * γ * I)‖) →
      (∀ σ : ℝ, 1 < σ →
        F₂ =ᶠ[𝓝 ((σ : ℂ) + 2 * γ * I)] fun z : ℂ => ∏' v : {v : HeightOneSpectrum (𝓞 K) // v ∉ T},
          (1 - (if IsUnramifiedCharAt (χ ^ 2) v.1 then (((χ ^ 2) (uniformizerIdele K v.1) : ℂˣ) : ℂ) else 0) *
            (((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) ^ (-z)))⁻¹) → False := by
    intro F₂ h2nz h2an h2up h2lo h2ev
    have h341 : ∀ σ : ℝ, 1 < σ → σ ≤ 1 + r →
        0 ≤ 3 * (1 / (σ - 1) + C₀)
          + 4 * (-(deriv L ((σ : ℂ) + γ * I) / L ((σ : ℂ) + γ * I))).re
          + (-(deriv F₂ ((σ : ℂ) + 2 * γ * I) / F₂ ((σ : ℂ) + 2 * γ * I))).re := by
      intro σ hσ hσr
      have h := three_four_one_L T χ hχu σ hσ γ L F₂ (hLev σ hσ) (h2ev σ hσ)
      have h0 := hC₀ σ hσ (by linarith)
      rw [← neg_re] at h0
      linarith
    have hfin := Complex.div_le_one_sub_of_apply_eq_zero_of_norm_le_exp_of_three_four_one_nonneg
      L F₂ β γ r 𝓛 C₀ hr0 hr1 hr𝓛 hC₀0 h𝓛C₀ (by rw [← hsβγ]; exact hLs) hLnz h2nz hLan h2an hLup h2up
      hLlo h2lo h341

    set X : ℝ := D * Real.log 𝔮 with hXdef
    have hX0 : 0 < X := by positivity
    have h1 : r / (20000 * X) ≤ r / (20000 * 𝓛) :=
      div_le_div_of_nonneg_left hr0.le (by positivity) (by nlinarith)
    have h2 : 1 - β ≤ min (r / (40000 * D)) (δD / 4) / Real.log 𝔮 := by
      have := hs
      rw [sub_le_comm] at this
      exact this
    have h3 : min (r / (40000 * D)) (δD / 4) / Real.log 𝔮 ≤ r / (40000 * X) := by
      rw [hXdef]
      calc min (r / (40000 * D)) (δD / 4) / Real.log 𝔮 ≤ r / (40000 * D) / Real.log 𝔮 :=
            div_le_div_of_nonneg_right hcmin1 hlog𝔮0.le
        _ = r / (40000 * (D * Real.log 𝔮)) := by rw [div_div]; ring_nf
    have h4 : r / (20000 * X) ≤ r / (40000 * X) := by linarith
    rw [div_le_div_iff₀ (by positivity) (by positivity)] at h4
    nlinarith

  by_cases hsqtriv : ∃ x ∈ normOneIdeles K, (χ ^ 2) x ≠ 1
  ·
    obtain ⟨L₂, hL₂d, hL₂eq⟩ :=
      NumberField.TateGlobal.exists_differentiable_eq_partialEulerProduct_of_exists_mem_normOneIdeles_ne_one
        K (χ ^ 2) (isIdeleClassChar_sq hχ) (continuous_sq hχc) (isUnitaryChar_sq hχu) hsqtriv T
    set cχ2 : HeightOneSpectrum (𝓞 K) → ℂ := fun v =>
      if IsUnramifiedCharAt (χ ^ 2) v then (((χ ^ 2) (uniformizerIdele K v) : ℂˣ) : ℂ) else 0 with hcχ2def
    have hcχ2 : ∀ v, ‖cχ2 v‖ ≤ 1 := fun v => norm_coeff_le_one (isUnitaryChar_sq hχu) v
    have hSχ2 := hS (χ ^ 2) (isIdeleClassChar_sq hχ) (continuous_sq hχc) (isUnitaryChar_sq hχu) hsqtriv
      (admitsModulus_sq hχ𝔣) (fun v hv => isUnramifiedCharAt_sq (hT v hv)) (fun w => 2 * φ w) (fun w => 2 * k w)
      (fun w a r hr ha => by
        rw [archLocalChar_sq_apply, hφ w a r hr ha, ← cpow_nat_mul]
        congr 1; push_cast; ring)
      (fun w a ha => by
        rw [archLocalChar_sq_apply, hk w a ha, ← zpow_natCast, ← zpow_mul, mul_comm]
        push_cast; ring_nf)
      L₂ hL₂d hL₂eq
    have hQ2 : ∑ w : InfinitePlace K, (|2 * φ w| + |((2 * k w : ℤ) : ℝ)|) = 2 * Q := by
      rw [hQdef, Finset.mul_sum]
      refine Finset.sum_congr rfl fun w _ => ?_
      push_cast
      rw [abs_mul, abs_mul, abs_of_pos (by norm_num : (0:ℝ) < 2)]
      ring
    refine finish L₂ ?_ ?_ ?_ ?_ ?_
    · intro z hz
      rw [hL₂eq z hz]; exact (differentiableAt_and_ne_zero T cχ2 hcχ2 z hz).2
    · exact fun _ _ _ => (analyticOnNhd_univ_iff_differentiable.mpr hL₂d).mono (Set.subset_univ _)
    · intro σ hσ hσr z hz
      obtain ⟨hz1, hz2, him⟩ := hdisc_re (u := 2 * γ) hσ hσr (by push_cast at hz ⊢; exact hz)
      have h := hSχ2 z hz1 hz2
      rw [hQ2] at h
      refine h.trans (hbnd CS AS _ hCS.le hCS_le hAS hASle (by linarith [abs_nonneg z.im]) ?_)
      have h1 : |z.im| ≤ 2 * |γ| + r := by
        have := abs_sub_abs_le_abs_sub z.im (2 * γ)
        rw [abs_mul, abs_of_pos (by norm_num : (0:ℝ) < 2)] at this
        linarith
      rw [h𝔮def]; linarith [abs_nonneg γ]
    · intro σ hσ hσr
      refine (hlo_conv σ).trans ?_
      have hpt : ((σ : ℂ) + 2 * γ * I) = ((σ : ℂ) + ((2 * γ : ℝ) : ℂ) * I) := by push_cast; ring
      rw [hpt, hL₂eq _ (by rw [re_ofReal_add_mul_I]; exact hσ)]
      exact sq_le_norm_tprod T cχ2 hcχ2 Z hZeq CZ' hCZ'1 hZle σ (2 * γ) hσ (by linarith)
    · intro σ hσ
      have hVopen : IsOpen {z : ℂ | 1 < z.re} := isOpen_lt continuous_const continuous_re
      exact Filter.eventuallyEq_of_mem (hVopen.mem_nhds (by
        show 1 < ((σ : ℂ) + 2 * γ * I).re; simp; exact hσ)) fun z hz => hL₂eq z hz
  ·
    push Not at hsqtriv
    obtain ⟨θ, hθ⟩ := NumberField.TateGlobal.exists_eq_normPowChar_of_forall_mem_normOneIdeles K (χ ^ 2)
      (continuous_sq hχc) (isUnitaryChar_sq hχu) hsqtriv
    obtain ⟨w₀⟩ := (inferInstance : Nonempty (InfinitePlace K))
    have hθle : |θ| ≤ 2 * Q := by
      have h1 := abs_theta_le χ θ hθ φ hφ w₀
      have h2 : |φ w₀| ≤ Q := by
        have : |φ w₀| + |(k w₀ : ℝ)| ≤ Q :=
          Finset.single_le_sum (f := fun w => |φ w| + |(k w : ℝ)|) (fun w _ => by positivity)
            (Finset.mem_univ w₀)
        linarith [abs_nonneg (k w₀ : ℝ)]
      linarith
    by_cases hwin : |2 * γ + θ| < δD
    ·
      have hc4 : 1 - β ≤ δD / 2 := by
        have h1 : 1 - β ≤ min (r / (40000 * D)) (δD / 4) / Real.log 𝔮 := by
          have := hs; rw [sub_le_comm] at this; exact this
        have h2 : min (r / (40000 * D)) (δD / 4) / Real.log 𝔮 ≤ (δD / 4) / Real.log 2 :=
          div_le_div₀ (by linarith) hcmin2 hlog2 hlog𝔮2
        have h3 : (δD / 4) / Real.log 2 ≤ δD / 2 := by
          rw [div_le_iff₀ hlog2]
          have := Real.log_two_gt_d9
          nlinarith
        linarith
      have hdist : ‖s - (1 - θ / 2 * I)‖ ≤ δD := by
        rw [hsβγ]
        have hre : (((β : ℂ) + γ * I) - (1 - θ / 2 * I)) = (((β - 1 : ℝ) : ℂ) + ((γ + θ / 2 : ℝ) : ℂ) * I) := by
          push_cast; ring
        rw [hre]
        calc ‖(((β - 1 : ℝ) : ℂ) + ((γ + θ / 2 : ℝ) : ℂ) * I)‖
            ≤ ‖((β - 1 : ℝ) : ℂ)‖ + ‖((γ + θ / 2 : ℝ) : ℂ) * I‖ := norm_add_le _ _
          _ = |β - 1| + |γ + θ / 2| := by
              rw [norm_mul, norm_I, mul_one, norm_real, norm_real, Real.norm_eq_abs, Real.norm_eq_abs]
          _ ≤ δD / 2 + δD / 2 := by
              have h1 : |β - 1| ≤ δD / 2 := abs_le.mpr ⟨by linarith, by linarith⟩
              have h2 : |γ + θ / 2| ≤ δD / 2 := by
                have : |γ + θ / 2| = |2 * γ + θ| / 2 := by
                  rw [show γ + θ / 2 = (2 * γ + θ) / 2 by ring, abs_div, abs_of_pos (by norm_num : (0:ℝ) < 2)]
                rw [this]; linarith
              linarith
          _ = δD := by ring
      exact hD χ hχ hχc hχu hχ1 hχ𝔣 hT θ hθ L hLd.differentiableOn hLeq s hdist hLs
    ·
      push Not at hwin
      set G : ℂ → ℂ := fun z => Z (z + θ * I) / (z + θ * I - 1) with hGdef

      have hcoef : ∀ (z : ℂ) (v : {v : HeightOneSpectrum (𝓞 K) // v ∉ T}),
          (1 - (if IsUnramifiedCharAt (χ ^ 2) v.1 then (((χ ^ 2) (uniformizerIdele K v.1) : ℂˣ) : ℂ) else 0) *
            (((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) ^ (-z)))⁻¹ =
          (1 - (((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) ^ (-(z + θ * I))))⁻¹ := by
        intro z v
        rw [hθ, NumberField.TateGlobal.ite_isUnramifiedCharAt_normPowChar_apply_uniformizerIdele_eq_absNorm_cpow_neg,
          ← cpow_add _ _ (Nat.cast_ne_zero.mpr (by have := two_le_absNorm v.1; omega))]
        congr 2
        ring_nf
      have hGE₀ : ∀ z : ℂ, 1 < z.re →
          G z = ∏' v : {v : HeightOneSpectrum (𝓞 K) // v ∉ T},
            (1 - (((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) ^ (-(z + θ * I))))⁻¹ := by
        intro z hz
        have hz' : 1 < (z + θ * I).re := by simpa using hz
        have hne : z + θ * I - 1 ≠ 0 := by
          rw [sub_ne_zero]; intro h; rw [h] at hz'; simp at hz'
        show Z (z + θ * I) / (z + θ * I - 1) = _
        rw [hZeq _ hz', mul_div_cancel_left₀ _ hne]

      have hden : ∀ {σ : ℝ} {z : ℂ}, 1 < σ → σ ≤ 1 + r → z ∈ Metric.closedBall ((σ : ℂ) + 2 * γ * I) r →
          δD / 2 ≤ ‖z + θ * I - 1‖ ∧ |z.im + θ| ≤ 2 * |γ| + 2 * Q + 1 / 2 := by
        intro σ z hσ hσr hz
        obtain ⟨-, -, him⟩ := hdisc_re (u := 2 * γ) hσ hσr (by push_cast at hz ⊢; exact hz)
        have himabs := abs_le.mp him
        have h1 : |(z + θ * I - 1).im| ≤ ‖z + θ * I - 1‖ := abs_im_le_norm _
        have h2 : (z + θ * I - 1).im = z.im + θ := by simp
        rw [h2] at h1
        have h3 : δD / 2 ≤ |z.im + θ| := by
          have : |2 * γ + θ| ≤ |z.im + θ| + |z.im - 2 * γ| := by
            calc |2 * γ + θ| = |(z.im + θ) - (z.im - 2 * γ)| := by ring_nf
              _ ≤ |z.im + θ| + |z.im - 2 * γ| := abs_sub _ _
          linarith
        refine ⟨h3.trans h1, ?_⟩
        calc |z.im + θ| ≤ |z.im| + |θ| := abs_add_le _ _
          _ ≤ (2 * |γ| + r) + 2 * Q := by
              have := abs_sub_abs_le_abs_sub z.im (2 * γ)
              rw [abs_mul, abs_of_pos (by norm_num : (0:ℝ) < 2)] at this
              linarith
          _ ≤ 2 * |γ| + 2 * Q + 1 / 2 := by linarith
      refine finish G ?_ ?_ ?_ ?_ ?_
      · intro z hz
        rw [hGE₀ z hz]
        exact (differentiableAt_and_ne_zero_one T _ (by simpa using hz)).2
      · intro σ hσ hσr
        have hUopen : IsOpen {z : ℂ | z + θ * I - 1 ≠ 0} := isOpen_ne_fun (by fun_prop) continuous_const
        have hGan : AnalyticOnNhd ℂ G {z : ℂ | z + θ * I - 1 ≠ 0} := by
          refine DifferentiableOn.analyticOnNhd (fun z hz => ?_) hUopen
          refine DifferentiableAt.differentiableWithinAt ?_
          show DifferentiableAt ℂ (fun z => Z (z + θ * I) / (z + θ * I - 1)) z
          exact ((hZd.differentiableAt).comp z (differentiableAt_id.add_const _)).div
            ((differentiableAt_id.add_const _).sub_const _) hz
        refine hGan.mono fun z hz => ?_
        have h := (hden hσ hσr hz).1
        show z + θ * I - 1 ≠ 0
        intro h0; rw [h0, norm_zero] at h; linarith
      · intro σ hσ hσr z hz
        obtain ⟨hz1, hz2, -⟩ := hdisc_re (u := 2 * γ) hσ hσr (by push_cast at hz ⊢; exact hz)
        obtain ⟨hd, himθ⟩ := hden hσ hσr hz
        have hZb := hZs Z hZd hZeq (z + θ * I) (by simpa using hz1) (by simpa using hz2)
        have himeq : (z + θ * I).im = z.im + θ := by simp
        rw [himeq] at hZb
        have hnormG : ‖G z‖ = ‖Z (z + θ * I)‖ / ‖z + θ * I - 1‖ := by
          show ‖Z (z + θ * I) / (z + θ * I - 1)‖ = _; rw [norm_div]
        rw [hnormG, div_le_iff₀ (by linarith)]
        have h1 : CZ * (2 + |z.im + θ|) ^ AZ ≤ (2 * CZ / δD) * (2 + |z.im + θ|) ^ AZ * (δD / 2) := by
          have : (2 * CZ / δD) * (2 + |z.im + θ|) ^ AZ * (δD / 2) = CZ * (2 + |z.im + θ|) ^ AZ := by
            field_simp
          rw [this]
        have h2 : (2 * CZ / δD) * (2 + |z.im + θ|) ^ AZ ≤ Real.exp 𝓛 :=
          hbnd _ AZ _ (by positivity) h2CZ_le hAZ hAZle (by linarith [abs_nonneg (z.im + θ)])
            (by rw [h𝔮def]; linarith [abs_nonneg γ])
        calc ‖Z (z + θ * I)‖ ≤ CZ * (2 + |z.im + θ|) ^ AZ := hZb
          _ ≤ (2 * CZ / δD) * (2 + |z.im + θ|) ^ AZ * (δD / 2) := h1
          _ ≤ Real.exp 𝓛 * (δD / 2) := mul_le_mul_of_nonneg_right h2 (by linarith)
          _ = Real.exp 𝓛 * ‖z + θ * I - 1‖ - Real.exp 𝓛 * (‖z + θ * I - 1‖ - δD / 2) := by ring
          _ ≤ Real.exp 𝓛 * ‖z + θ * I - 1‖ := by
              have : 0 ≤ Real.exp 𝓛 * (‖z + θ * I - 1‖ - δD / 2) :=
                mul_nonneg (Real.exp_pos _).le (by linarith)
              linarith
      · intro σ hσ hσr
        refine (hlo_conv σ).trans ?_
        rw [hGE₀ _ (by rw [show ((σ : ℂ) + 2 * γ * I).re = σ by simp]; exact hσ)]
        have hpt : ((σ : ℂ) + 2 * γ * I + θ * I) = ((σ : ℂ) + ((2 * γ + θ : ℝ) : ℂ) * I) := by
          push_cast; ring
        rw [hpt]
        have h := sq_le_norm_tprod T (fun _ => (1 : ℂ)) (fun _ => by rw [norm_one]) Z hZeq CZ' hCZ'1 hZle σ
          (2 * γ + θ) hσ (by linarith)
        simp only [one_mul] at h
        exact h
      · intro σ hσ
        have hVopen : IsOpen {z : ℂ | 1 < z.re} := isOpen_lt continuous_const continuous_re
        refine Filter.eventuallyEq_of_mem (hVopen.mem_nhds (by
          show 1 < ((σ : ℂ) + 2 * γ * I).re; simp; exact hσ)) fun z hz => ?_
        rw [hGE₀ z hz, tprod_congr (hcoef z)]

end main

end R4ZF

end

open NumberField IsDedekindDomain AutomorphicForm NumberField.TateGlobal NumberField.InfinitePlace in
open scoped Classical in
theorem solution
    (K : Type) [Field K] [NumberField K]
    (T : Finset (HeightOneSpectrum (𝓞 K))) (𝔣 : Ideal (𝓞 K)) :
    ∃ c : ℝ, 0 < c ∧
      ∀ (χ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ), IsIdeleClassChar (𝓞 K) K χ → Continuous χ →
        IsUnitaryChar (𝓞 K) K χ → (∃ x ∈ normOneIdeles K, χ x ≠ 1) →
        HeckeCharacter.AdmitsModulus K χ 𝔣 → (∀ v ∉ T, IsUnramifiedCharAt χ v) →
      ∀ (φ : InfinitePlace K → ℝ) (k : InfinitePlace K → ℤ),
        (∀ (w : InfinitePlace K) (a : (w.Completion)ˣ) (r : ℝ), 0 < r →
            Completion.extensionEmbedding w (a : w.Completion) = (r : ℂ) →
            ((archLocalChar χ w a : ℂˣ) : ℂ) = (r : ℂ) ^ (Complex.I * φ w)) →
        (∀ (w : InfinitePlace K) (a : (w.Completion)ˣ),
            ‖Completion.extensionEmbedding w (a : w.Completion)‖ = 1 →
            ((archLocalChar χ w a : ℂˣ) : ℂ) = (Completion.extensionEmbedding w (a : w.Completion)) ^ (k w)) →
      ∀ (L : ℂ → ℂ), Differentiable ℂ L →
        (∀ s : ℂ, 1 < s.re → L s = ∏' v : {v : HeightOneSpectrum (𝓞 K) // v ∉ T},
            (1 - (if IsUnramifiedCharAt χ v.1 then ((χ (uniformizerIdele K v.1) : ℂˣ) : ℂ) else 0) *
              (((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) ^ (-s)))⁻¹) →
      ∀ s : ℂ, 1 - c / Real.log (2 + |s.im| + ∑ w : InfinitePlace K, (|φ w| + |(k w : ℝ)|)) ≤ s.re →
        L s ≠ 0 :=
  R4ZF.main K T 𝔣

end S_NumberField_TateGlobal_exists_pos_forall_partialEulerProduct_continuation_ne_zero_of_one_sub_div_log_le_re_of_admitsModulus
end P2MW
export P2MW.S_NumberField_TateGlobal_exists_pos_forall_partialEulerProduct_continuation_ne_zero_of_one_sub_div_log_le_re_of_admitsModulus (solution)
