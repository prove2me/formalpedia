-- Prove2me | solution 1 for NumberField.TateGlobal.exists_forall_norm_partialEulerProduct_continuation_le_rpow_of_re_mem_Icc_of_admitsModulus
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.93214+00:00
-- url     : https://prove2.me/submissions/58ab4831-53f5-550b-ba3f-c7ea2a11a714

import Mathlib
import Definitions.Def_NumberField_TateGlobalZeta
import Definitions.Def_AutomorphicForm_HeckeEigenfunction
import Definitions.Def_HeckeCharacter_FiniteOrder
import Theorems.Thm_EulerProduct_norm_tprod_inv_one_sub_mul_natCast_cpow_neg_le_exp
import Theorems.Thm_PhragmenLindelof_exists_norm_le_mul_one_add_abs_im_rpow_of_vertical_strip
import Theorems.Thm_NumberField_TateGlobal_exists_norm_partialEulerProduct_continuation_le_mul_exp_mul_im_sq
import Theorems.Thm_NumberField_TateGlobal_exists_forall_norm_partialEulerProduct_continuation_le_rpow_on_re_eq_neg_half_of_admitsModulus
import Theorems.Thm_NumberField_summable_heightOneSpectrum_absNorm_rpow_neg_of_one_lt
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_NumberField_TateGlobal_exists_forall_norm_partialEulerProduct_continuation_le_rpow_of_re_mem_Icc_of_admitsModulus
p2m_attr_erase "instance" "instCountableOfNumberField_definitions instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions IsDedekindDomain.HeightOneSpectrum.Extension.instAlgebraSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnder IsDedekindDomain.HeightOneSpectrum.Extension.instAlgebraSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnder_1 IsDedekindDomain.HeightOneSpectrum.instMulActionHomClassAlgHomTensorProductAdicCompletionForallValEqUnder_definitions IsDedekindDomain.HeightOneSpectrum.Extension.instAlgebraAdicCompletionValEqUnder IsDedekindDomain.HeightOneSpectrum.adicCompletion.instFiniteForallValEqUnderOfFiniteDimensional_definitions IsDedekindDomain.HeightOneSpectrum.instIsBiscalarSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersTensorProductCoeAlgHomTensorAdicCompletionIntegersTo IsDedekindDomain.HeightOneSpectrum.Extension.instContinuousSMulAdicCompletionValEqUnder IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsModuleTopology IsDedekindDomain.HeightOneSpectrum.Extension.instFiniteSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnderOfFiniteDimensional IsDedekindDomain.HeightOneSpectrum.adicCompletion.instFiniteValEqUnderOfFiniteDimensional_definitions instIsBiscalarTensorProductCoeAlgHomBaseChange_of_algebraMap IsDedekindDomain.HeightOneSpectrum.instIsScalarTowerSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnder_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsModuleTopologyPi Submodule.instIsTopologicalModuleSubtypeMem Pi.instTopologicalModule IsTopologicalModule.toContinuousSMul IsTopologicalModule.toContinuousAdd instFunLike SemialgHomClass.toSemilinearMapClass instCoeTCSemialgHom SemialgHomClass.toRingHomClass SemialgHomClass.instSemialgHom"
p2m_attr_erase "simp" "NumberField.StandardAddChar.ratArchLine_apply NumberField.StandardAddChar.AdelicTraceData.mk.sizeOf_spec NumberField.StandardAddChar.AdelicTraceData.mk.injEq AutomorphicForm.whittakerCoefficient_zero AutomorphicForm.unipotentGL2_zero AutomorphicForm.constantTerm_const AutomorphicForm.constantTerm_zero AutomorphicForm.unipotentGL2_coe NumberField.AdelicTrace.traceDiag_apply NumberField.AdelicTrace.diag_apply LanglandsTunnell.TateLocal.conductorExponentAt_one LanglandsTunnell.TateLocal.charExt_coe_units LanglandsTunnell.TateLocal.modulus_one LanglandsTunnell.TateLocal.modulus_zero LanglandsTunnell.TateLocal.modulus_coe_units LanglandsTunnell.TateLocal.charExt_zero LanglandsTunnell.signEpsilon_one LanglandsTunnell.RealArchParam.epsilonFactor_principal LanglandsTunnell.RealArchParam.epsilonFactor_discrete LanglandsTunnell.signEpsilon_zero LanglandsTunnell.signShift_zero LanglandsTunnell.RealArchParam.twist_zero LanglandsTunnell.RealArchParam.discrete.sizeOf_spec LanglandsTunnell.RealArchParam.principal.injEq LanglandsTunnell.ComplexArchParam.dual_dual LanglandsTunnell.ComplexArchParam.mk.sizeOf_spec LanglandsTunnell.RealArchParam.dual_dual LanglandsTunnell.RealArchParam.discrete.injEq LanglandsTunnell.ComplexArchParam.twist_zero LanglandsTunnell.RealArchParam.principal.sizeOf_spec LanglandsTunnell.signShift_one LanglandsTunnell.ComplexArchParam.mk.injEq LanglandsTunnell.LDatum.mk.sizeOf_spec LanglandsTunnell.LDatum.badFactor_zero LanglandsTunnell.LDatum.mk.injEq LanglandsTunnell.ArchPlace.complexTestFun_zero_apply LanglandsTunnell.ArchPlace.norm_anglePhase LanglandsTunnell.ArchPlace.realTestFun_zero_apply UnramifiedWhittaker.ProductMeasureData.mk.injEq UnramifiedWhittaker.ProductMeasureData.mk.sizeOf_spec"
p2m_attr_erase "simp" "AdelicDock.coe_finEmbed AdelicDock.splice_apply_self AdelicDock.coe_localEmbed NumberField.AdeleRing.val_finiteUnitsComponent IsDedekindDomain.FiniteAdeleRing.val_unitsComponent NumberField.AdeleRing.val_finitePartUnits NumberField.AdeleRing.val_infiniteUnitsComponent SemialgHom.baseChange_of_algebraMap_tmul_left SemialgHom.baseChangeRightOfAlgebraMap_apply Pi.semialgHomPi_apply Pi.semialgHom_apply Module.Basis.rightBaseChange_apply LinearEquiv.coe_mulLeft LinearEquiv.coe_mulRight WithVal.semialgebraMap_toFun_ofVal Module.Basis.rightBaseChange_repr IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers.tensorCoe_tmul IsDedekindDomain.HeightOneSpectrum.tensorAdicCompletionIntegersTo_tmul SemialgHom.baseChangeRightOfAlgebraMap_coe IsDedekindDomain.HeightOneSpectrum.adicCompletion.integerBaseChangeLinearEquiv_tmul_apply SemialgHom.baseChange_of_algebraMap_tmul_right IsLocalization.map_moduleTensorEquiv_symm_tmul IsLocalization.leftModuleTensorEquiv_apply IsLocalization.moduleLid_symm_apply IsLocalization.leftModuleTensorEquiv_symm_apply IsLocalization.map_moduleTensorEquiv_tmul IsModuleTopology.continuousLinearEquiv_apply AlgEquiv.extendScalars_symm_apply IsModuleTopology.Module.Basis.equivFun_homeo_symm_apply IsModuleTopology.Module.Basis.equivFun_homeo_apply IsModuleTopology.continuousAlgEquivOfIsBiscalar_apply AlgEquiv.extendScalars_apply IsModuleTopology.continuousLinearEquiv_symm_apply SemialgHom.restrictScalars_toFun SemialgHom.mk.sizeOf_spec SemialgHom.mk.injEq SemialgHom.coe_coe coe_mk TensorProduct.RightActions.smul_def TensorProduct.RightActions.Module.TensorProduct.comm_symm_apply_tmul"
p2m_attr_erase "simp" "TensorProduct.RightActions.LinearMap.baseChange_id TensorProduct.RightActions.algebraMap_eval TensorProduct.RightActions.Module.TensorProduct.comm_apply_tmul TensorProduct.RightActions.Algebra.TensorProduct.comm_symm_apply_tmul TensorProduct.RightActions.Algebra.TensorProduct.comm_apply_tmul M4aHerbrand.IdeleGaloisDescent.mk.sizeOf_spec M4aHerbrand.IdeleGaloisDescent.mk.injEq"

set_option autoImplicit false

noncomputable section

open NumberField IsDedekindDomain AutomorphicForm NumberField.TateGlobal NumberField.InfinitePlace
open Complex Filter Set
open scoped Topology

namespace R4LDCstrip

theorem sq_le_four_mul_exp_abs (t : ℝ) : t ^ 2 ≤ 4 * Real.exp |t| := by
  have h1 : |t| / 2 + 1 ≤ Real.exp (|t| / 2) := Real.add_one_le_exp _
  have h0 : 0 ≤ |t| / 2 + 1 := by positivity
  have h2 : (|t| / 2 + 1) ^ 2 ≤ Real.exp (|t| / 2) ^ 2 := pow_le_pow_left₀ h0 h1 2
  have h3 : Real.exp (|t| / 2) ^ 2 = Real.exp |t| := by
    rw [← Real.exp_nat_mul]; congr 1; ring
  have h4 : t ^ 2 = |t| ^ 2 := (sq_abs t).symm
  nlinarith [abs_nonneg t, h2, h3, h4]

theorem gaussian_le_doubleExp (B C : ℝ) :
    ∃ B' : ℝ, ∀ t : ℝ, max B 1 * Real.exp (max C 0 * t ^ 2) ≤ Real.exp (B' * Real.exp (1 * |t|)) := by
  refine ⟨Real.log (max B 1) + 4 * max C 0, fun t => ?_⟩
  have hB1 : 1 ≤ max B 1 := le_max_right _ _
  have hB0 : 0 < max B 1 := one_pos.trans_le hB1
  have hC0 : 0 ≤ max C 0 := le_max_right _ _
  have hlog : 0 ≤ Real.log (max B 1) := Real.log_nonneg hB1
  have he1 : 1 ≤ Real.exp (1 * |t|) := by rw [one_mul]; exact Real.one_le_exp (abs_nonneg t)
  have hrew : max B 1 * Real.exp (max C 0 * t ^ 2) =
      Real.exp (Real.log (max B 1) + max C 0 * t ^ 2) := by
    rw [Real.exp_add, Real.exp_log hB0]
  rw [hrew, Real.exp_le_exp]
  have h1 : Real.log (max B 1) ≤ Real.log (max B 1) * Real.exp (1 * |t|) :=
    le_mul_of_one_le_right hlog he1
  have h2 : max C 0 * t ^ 2 ≤ 4 * max C 0 * Real.exp (1 * |t|) := by
    rw [one_mul]
    have := sq_le_four_mul_exp_abs t
    nlinarith
  nlinarith

theorem two_le_absNorm {K : Type} [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K)) :
    2 ≤ Ideal.absNorm v.asIdeal := by
  have h0 : Ideal.absNorm v.asIdeal ≠ 0 := by
    rw [Ne, Ideal.absNorm_eq_zero_iff]; exact v.ne_bot
  have h1 : Ideal.absNorm v.asIdeal ≠ 1 := by
    rw [Ne, Ideal.absNorm_eq_one_iff]; exact v.isPrime.ne_top
  omega

section euler
variable {K : Type} [Field K] [NumberField K]

def eulerFn (T : Finset (HeightOneSpectrum (𝓞 K))) (c : HeightOneSpectrum (𝓞 K) → ℂ) (s : ℂ) : ℂ :=
  ∏' v : {v : HeightOneSpectrum (𝓞 K) // v ∉ T},
    (1 - c v.1 * (((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) ^ (-s)))⁻¹

def M₁ (T : Finset (HeightOneSpectrum (𝓞 K))) : ℝ :=
  Real.exp (2 * ∑' v : {v : HeightOneSpectrum (𝓞 K) // v ∉ T},
    ((Ideal.absNorm v.1.asIdeal : ℕ) : ℝ) ^ (-(3 / 2 : ℝ)))

theorem one_le_M₁ (T : Finset (HeightOneSpectrum (𝓞 K))) : 1 ≤ M₁ (K := K) T := by
  unfold M₁
  refine Real.one_le_exp (mul_nonneg (by norm_num) (tsum_nonneg fun v => ?_))
  exact Real.rpow_nonneg (Nat.cast_nonneg _) _

theorem summable_subtype_rpow (T : Finset (HeightOneSpectrum (𝓞 K))) {σ : ℝ} (hσ : 1 < σ) :
    Summable fun v : {v : HeightOneSpectrum (𝓞 K) // v ∉ T} =>
      ((Ideal.absNorm v.1.asIdeal : ℕ) : ℝ) ^ (-σ) :=
  (NumberField.summable_heightOneSpectrum_absNorm_rpow_neg_of_one_lt K hσ).subtype _

theorem norm_eulerFn_le (T : Finset (HeightOneSpectrum (𝓞 K))) (c : HeightOneSpectrum (𝓞 K) → ℂ)
    (hc : ∀ v, ‖c v‖ ≤ 1) (s : ℂ) (hs : 3 / 2 ≤ s.re) : ‖eulerFn T c s‖ ≤ M₁ (K := K) T := by
  have hs1 : 1 < s.re := by linarith
  have hsum := summable_subtype_rpow (K := K) T hs1
  have h := EulerProduct.norm_tprod_inv_one_sub_mul_natCast_cpow_neg_le_exp
    (fun v : {v : HeightOneSpectrum (𝓞 K) // v ∉ T} => Ideal.absNorm v.1.asIdeal)
    (fun v => two_le_absNorm v.1) (fun v => c v.1) (fun v => hc v.1) s hs1.le hsum
  refine h.trans ?_
  unfold M₁
  rw [Real.exp_le_exp]
  refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
  refine Summable.tsum_le_tsum (fun v => ?_) hsum (summable_subtype_rpow T (by norm_num))
  have h1 : (1 : ℝ) ≤ ((Ideal.absNorm v.1.asIdeal : ℕ) : ℝ) := by
    have := two_le_absNorm v.1
    exact_mod_cast (by omega : 1 ≤ Ideal.absNorm v.1.asIdeal)
  exact Real.rpow_le_rpow_of_exponent_le h1 (by linarith)

end euler

section main
variable {K : Type} [Field K] [NumberField K]

theorem norm_coeff_le_one {χ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ} (hu : IsUnitaryChar (𝓞 K) K χ)
    (v : HeightOneSpectrum (𝓞 K)) [Decidable (IsUnramifiedCharAt χ v)] :
    ‖(if IsUnramifiedCharAt χ v then ((χ (uniformizerIdele K v) : ℂˣ) : ℂ) else 0)‖ ≤ 1 := by
  split_ifs
  · exact (hu _).le
  · simp

theorem re_ofReal_add_mul_I (σ t : ℝ) : ((σ : ℂ) + t * I).re = σ := by simp

theorem im_ofReal_add_mul_I (σ t : ℝ) : ((σ : ℂ) + t * I).im = t := by simp

set_option maxHeartbeats 6400000 in
open scoped Classical in
theorem main (T : Finset (HeightOneSpectrum (𝓞 K))) (𝔣 : Ideal (𝓞 K)) :
    ∃ C A : ℝ, 0 < C ∧ 0 < A ∧
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
      ∀ s : ℂ, -1 / 2 ≤ s.re → s.re ≤ 5 / 2 →
        ‖L s‖ ≤ C * (2 + |s.im| + ∑ w : InfinitePlace K, (|φ w| + |(k w : ℝ)|)) ^ A := by

  obtain ⟨Cb, Ab, hCb, hAb, hleft⟩ :=
    NumberField.TateGlobal.exists_forall_norm_partialEulerProduct_continuation_le_rpow_on_re_eq_neg_half_of_admitsModulus
      K T 𝔣
  obtain ⟨C₃, hC₃, hPL⟩ :=
    PhragmenLindelof.exists_norm_le_mul_one_add_abs_im_rpow_of_vertical_strip (-1 / 2) (3 / 2) Ab
      (by norm_num) hAb.le

  set M1 : ℝ := M₁ (K := K) T with hM1def
  have hM1 : 1 ≤ M1 := one_le_M₁ T
  set C₀ : ℝ := max Cb M1 with hC₀
  have hC₀1 : 1 ≤ C₀ := hM1.trans (le_max_right _ _)
  have hC₀0 : 0 ≤ C₀ := zero_le_one.trans hC₀1
  have hCbC₀ : Cb ≤ C₀ := le_max_left _ _
  have hM1C₀ : M1 ≤ C₀ := le_max_right _ _
  set C₄ : ℝ := max C₃ 1 * C₀ with hC₄
  have hC₃C : C₃ ≤ max C₃ 1 := le_max_left _ _
  have hC₃1 : 1 ≤ max C₃ 1 := le_max_right _ _
  have hC₄1 : 1 ≤ C₄ := one_le_mul_of_one_le_of_one_le hC₃1 hC₀1
  have hC₄0 : 0 < C₄ := one_pos.trans_le hC₄1
  have hC₀C₄ : C₀ ≤ C₄ := le_mul_of_one_le_left hC₀0 hC₃1
  set Afin : ℝ := 2 * Ab with hAfin
  have hAfin0 : 0 < Afin := by positivity
  refine ⟨C₄, Afin, hC₄0, hAfin0, ?_⟩
  intro χ hχ hχc hχu hχ1 hχ𝔣 hT φ k hφ hk L hLd hLeq s hsa hsb

  set c : HeightOneSpectrum (𝓞 K) → ℂ := fun v =>
    if IsUnramifiedCharAt χ v then ((χ (uniformizerIdele K v) : ℂˣ) : ℂ) else 0 with hc
  have hc1 : ∀ v, ‖c v‖ ≤ 1 := fun v => norm_coeff_le_one hχu v
  have hLP : ∀ s : ℂ, 1 < s.re → L s = eulerFn T c s := fun s hs => hLeq s hs

  set Q : ℝ := ∑ w : InfinitePlace K, (|φ w| + |(k w : ℝ)|) with hQ
  have hQ0 : 0 ≤ Q := Finset.sum_nonneg fun w _ => by positivity

  set M : ℝ := C₀ * (2 + Q) ^ Ab with hM
  have h2Q1 : 1 ≤ (2 + Q) ^ Ab := Real.one_le_rpow (by linarith) hAb.le
  have hM0 : 0 ≤ M := by positivity
  have hkey : ∀ u : ℝ, (2 + |u| + Q) ≤ (2 + Q) * (1 + |u|) := fun u => by
    nlinarith [abs_nonneg u, hQ0]
  have hkeypow : ∀ u : ℝ, (2 + |u| + Q) ^ Ab ≤ (2 + Q) ^ Ab * (1 + |u|) ^ Ab := fun u => by
    rw [← Real.mul_rpow (by linarith) (by positivity)]
    exact Real.rpow_le_rpow (by positivity) (hkey u) hAb.le
  have hstrip : ∀ z : ℂ, -1 / 2 ≤ z.re → z.re ≤ 3 / 2 → ‖L z‖ ≤ C₃ * M * (1 + |z.im|) ^ Ab := by
    refine hPL L M hM0 hLd.diffContOnCl ?_ ?_ ?_
    ·
      obtain ⟨B, Cg, hBC⟩ :=
        NumberField.TateGlobal.exists_norm_partialEulerProduct_continuation_le_mul_exp_mul_im_sq
          K χ hχ hχc hχu hχ1 T L hLd hLeq (-1 / 2) (3 / 2)
      obtain ⟨B', hB'⟩ := gaussian_le_doubleExp B Cg
      refine ⟨1, ?_, B', fun z hza hzb => ?_⟩
      · have : Real.pi / (3 / 2 - -1 / 2) = Real.pi / 2 := by norm_num
        rw [this]
        linarith [Real.pi_gt_three]
      · refine le_trans ?_ (hB' z.im)
        refine (hBC z hza.le hzb.le).trans ?_
        have hB1 : B ≤ max B 1 := le_max_left _ _
        have he : Real.exp (Cg * z.im ^ 2) ≤ Real.exp (max Cg 0 * z.im ^ 2) :=
          Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right (le_max_left _ _) (sq_nonneg _))
        calc B * Real.exp (Cg * z.im ^ 2) ≤ max B 1 * Real.exp (Cg * z.im ^ 2) :=
              mul_le_mul_of_nonneg_right hB1 (Real.exp_pos _).le
          _ ≤ max B 1 * Real.exp (max Cg 0 * z.im ^ 2) :=
              mul_le_mul_of_nonneg_left he (zero_le_one.trans (le_max_right _ _))
    ·
      intro z hz
      have h := hleft χ hχ hχc hχu hχ1 hχ𝔣 hT φ k hφ hk L hLd hLeq z hz
      calc ‖L z‖ ≤ Cb * (2 + |z.im| + Q) ^ Ab := h
        _ ≤ C₀ * ((2 + Q) ^ Ab * (1 + |z.im|) ^ Ab) :=
            mul_le_mul hCbC₀ (hkeypow z.im) (by positivity) hC₀0
        _ = M * (1 + |z.im|) ^ Ab := by rw [hM]; ring
    ·
      intro z hz
      have hz1 : 1 < z.re := by rw [hz]; norm_num
      rw [hLP z hz1]
      have h := norm_eulerFn_le T c hc1 z (by rw [hz])
      have h1t : 1 ≤ (1 + |z.im|) ^ Ab := Real.one_le_rpow (by linarith [abs_nonneg z.im]) hAb.le
      calc ‖eulerFn T c z‖ ≤ M1 := h
        _ ≤ C₀ := hM1C₀
        _ = C₀ * 1 * 1 := by ring
        _ ≤ C₀ * (2 + Q) ^ Ab * (1 + |z.im|) ^ Ab := by gcongr
        _ = M * (1 + |z.im|) ^ Ab := by rw [hM]

  have hq1 : ∀ u : ℝ, 1 ≤ 2 + |u| + Q := fun u => by linarith [abs_nonneg u]
  have hbig : ∀ z : ℂ, -1 / 2 ≤ z.re → z.re ≤ 5 / 2 → ‖L z‖ ≤ C₄ * (2 + |z.im| + Q) ^ Afin := by
    intro z hza hzb
    have hq := hq1 z.im
    have hqpos : 0 < 2 + |z.im| + Q := by linarith
    have hpow2 : (2 + |z.im| + Q) ^ Afin = (2 + |z.im| + Q) ^ Ab * (2 + |z.im| + Q) ^ Ab := by
      rw [hAfin, two_mul, Real.rpow_add hqpos]
    rcases le_or_gt z.re (3 / 2) with hle | hgt
    · have h := hstrip z hza hle
      have hA1 : (2 + Q) ^ Ab ≤ (2 + |z.im| + Q) ^ Ab :=
        Real.rpow_le_rpow (by linarith) (by linarith [abs_nonneg z.im]) hAb.le
      have hA2 : (1 + |z.im|) ^ Ab ≤ (2 + |z.im| + Q) ^ Ab :=
        Real.rpow_le_rpow (by positivity) (by linarith) hAb.le
      calc ‖L z‖ ≤ C₃ * M * (1 + |z.im|) ^ Ab := h
        _ = C₃ * C₀ * ((2 + Q) ^ Ab * (1 + |z.im|) ^ Ab) := by rw [hM]; ring
        _ ≤ (max C₃ 1 * C₀) * ((2 + |z.im| + Q) ^ Ab * (2 + |z.im| + Q) ^ Ab) := by
            apply mul_le_mul (mul_le_mul_of_nonneg_right hC₃C hC₀0)
              (mul_le_mul hA1 hA2 (by positivity) (by positivity)) (by positivity) (by positivity)
        _ = C₄ * (2 + |z.im| + Q) ^ Afin := by rw [hC₄, hpow2]
    · have hz1 : 1 < z.re := by linarith
      rw [hLP z hz1]
      have h := norm_eulerFn_le T c hc1 z hgt.le
      have h1 : 1 ≤ (2 + |z.im| + Q) ^ Afin := Real.one_le_rpow hq hAfin0.le
      calc ‖eulerFn T c z‖ ≤ M1 := h
        _ ≤ C₄ := hM1C₀.trans hC₀C₄
        _ = C₄ * 1 := (mul_one _).symm
        _ ≤ C₄ * (2 + |z.im| + Q) ^ Afin := mul_le_mul_of_nonneg_left h1 hC₄0.le
  exact hbig s hsa hsb

end main

end R4LDCstrip

end

open NumberField IsDedekindDomain AutomorphicForm NumberField.TateGlobal NumberField.InfinitePlace in
open scoped Classical in
theorem solution
    (K : Type) [Field K] [NumberField K]
    (T : Finset (HeightOneSpectrum (𝓞 K))) (𝔣 : Ideal (𝓞 K)) :
    ∃ C A : ℝ, 0 < C ∧ 0 < A ∧
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
      ∀ s : ℂ, -1 / 2 ≤ s.re → s.re ≤ 5 / 2 →
        ‖L s‖ ≤ C * (2 + |s.im| + ∑ w : InfinitePlace K, (|φ w| + |(k w : ℝ)|)) ^ A :=
  R4LDCstrip.main T 𝔣

end S_NumberField_TateGlobal_exists_forall_norm_partialEulerProduct_continuation_le_rpow_of_re_mem_Icc_of_admitsModulus
end P2MW
export P2MW.S_NumberField_TateGlobal_exists_forall_norm_partialEulerProduct_continuation_le_rpow_of_re_mem_Icc_of_admitsModulus (solution)
