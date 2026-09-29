-- Prove2me | solution 1 for LanglandsTunnell.Converse.exists_formalBaseChange_generic_of_isArithGenuineCuspRealizable
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.353894+00:00
-- url     : https://prove2.me/submissions/83a7cbbf-7b43-5e6b-88f6-6bed1901a89b

import Definitions.Def_AutomorphicForm_ArithCuspRealization
import Definitions.Def_AutomorphicForm_ProductionPinsGeneral
import Definitions.Def_AutomorphicForm_FormalBaseChange
import Theorems.Thm_LanglandsTunnell_Converse_satakePow_sq_ne_of_sq_eq_real_mul_of_norm_sq_lt
import Theorems.Thm_LanglandsTunnell_Converse_exists_finset_sq_eq_real_mul_b_and_norm_sq_lt_of_isArithGenuineCuspRealizable
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LanglandsTunnell_Converse_exists_formalBaseChange_generic_of_isArithGenuineCuspRealizable
p2m_attr_erase "instance" "instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions instCountableOfNumberField_definitions RestrictedProduct.SecondCountableTopology_of_principal instCountableElemSetSetsCofinite_definitions"
p2m_attr_erase "simp" "AdelicDock.coe_finEmbed AdelicDock.splice_apply_self AdelicDock.coe_localEmbed M4aHerbrand.IdeleGaloisDescent.mk.sizeOf_spec M4aHerbrand.IdeleGaloisDescent.mk.injEq NumberField.StandardAddChar.ratArchLine_apply NumberField.StandardAddChar.AdelicTraceData.mk.sizeOf_spec NumberField.StandardAddChar.AdelicTraceData.mk.injEq AutomorphicForm.whittakerCoefficient_zero NumberField.AdelicTrace.traceDiag_apply NumberField.AdelicTrace.diag_apply LanglandsTunnell.TateLocal.conductorExponentAt_one LanglandsTunnell.TateLocal.charExt_coe_units LanglandsTunnell.TateLocal.modulus_one LanglandsTunnell.TateLocal.modulus_zero LanglandsTunnell.TateLocal.modulus_coe_units LanglandsTunnell.TateLocal.charExt_zero ContinuousAddEquiv.restrictedProductPi_apply RestrictedProduct.flatten_homeomorph_apply RestrictedProduct.flatten_homeomorph'_symm_apply ContinuousMulEquiv.restrictedProductPi_symm_apply RestrictedProduct.flatten_homeomorph'_apply RestrictedProduct.flatten_homeomorph_symm_apply ContinuousMulEquiv.restrictedProductPi_apply ContinuousAddEquiv.restrictedProductPi_symm_apply RingEquiv.restrictedProductCongr_symm_apply RingEquiv.restrictedProductCongrRight_apply MulEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductProd_symm_apply_coe Equiv.restrictedProductCongrRight_apply AddEquiv.restrictedProductCongr_apply Equiv.restrictedProductCongrLeft'_symm_apply_apply Equiv.restrictedProductCongr_apply_apply Equiv.restrictedProductCongrLeft_apply_apply RestrictedProduct.flatten_equiv'_apply AddEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductCongr_symm_apply Equiv.restrictedProductCongrRight_symm_apply RestrictedProduct.flatten_equiv'_symm_apply AddEquiv.restrictedProductCongrLeft'_apply"
p2m_attr_erase "simp" "Equiv.restrictedProductCongrLeft'_apply RestrictedProduct.flatten_apply RingEquiv.restrictedProductCongr_apply_apply RingEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductProd_apply RestrictedProduct.flatten_equiv_apply RestrictedProduct.flatten_equiv_symm_apply LinearEquiv.restrictedProductCongrLeft'_apply RestrictedProduct.not_mem_support RestrictedProduct.mem_structureSubring_iff RestrictedProduct.not_mem_mulSupport RestrictedProduct.support_neg RestrictedProduct.mem_indexSupport_iff RestrictedProduct.mulSupport_inv RestrictedProduct.mapAlongLinearMap_apply"

set_option autoImplicit false

namespace LanglandsTunnellBaseChangeAux

open IsDedekindDomain NumberField

variable (K : Type) [Field K] [NumberField K]
  [Algebra (RingOfIntegers ℚ) (RingOfIntegers K)] [Algebra.IsIntegral (RingOfIntegers ℚ) (RingOfIntegers K)]

omit [Algebra.IsIntegral (RingOfIntegers ℚ) (RingOfIntegers K)] in
private theorem moduleFinite : Module.Finite (RingOfIntegers ℚ) (RingOfIntegers K) := by
  haveI : IsScalarTower ℤ (RingOfIntegers ℚ) (RingOfIntegers K) :=
    IsScalarTower.of_algebraMap_eq' (Subsingleton.elim _ _)
  exact Module.Finite.of_restrictScalars_finite ℤ (RingOfIntegers ℚ) (RingOfIntegers K)

variable {K}

private theorem liesOver_under (𝔓 : HeightOneSpectrum (RingOfIntegers K)) :
    𝔓.asIdeal.LiesOver (𝔓.under (RingOfIntegers ℚ)).asIdeal :=
  Ideal.over_under 𝔓.asIdeal

private theorem _root_.LanglandsTunnellBaseChangeAux.inertiaDeg_pos (𝔓 : HeightOneSpectrum (RingOfIntegers K)) :
    0 < (𝔓.under (RingOfIntegers ℚ)).asIdeal.inertiaDeg' 𝔓.asIdeal := by
  haveI := moduleFinite K
  haveI := liesOver_under 𝔓
  exact Ideal.inertiaDeg'_pos _ _

p2m_export "LanglandsTunnellBaseChangeAux" "inertiaDeg_pos"
private theorem absNorm_eq_pow (𝔓 : HeightOneSpectrum (RingOfIntegers K)) :
    Ideal.absNorm 𝔓.asIdeal =
      Ideal.absNorm (𝔓.under (RingOfIntegers ℚ)).asIdeal ^
        (𝔓.under (RingOfIntegers ℚ)).asIdeal.inertiaDeg' 𝔓.asIdeal := by
  haveI := moduleFinite K
  haveI := liesOver_under 𝔓
  exact Ideal.absNorm_eq_pow_inertiaDeg_of_liesOver _ _ (𝔓.under (RingOfIntegers ℚ)).isPrime
    (𝔓.under (RingOfIntegers ℚ)).ne_bot

private theorem one_lt_absNorm (𝔭 : HeightOneSpectrum (RingOfIntegers ℚ)) : 1 < Ideal.absNorm 𝔭.asIdeal := by
  have h0 : Ideal.absNorm 𝔭.asIdeal ≠ 0 := Ideal.absNorm_eq_zero_iff.not.mpr 𝔭.ne_bot
  have h1 : Ideal.absNorm 𝔭.asIdeal ≠ 1 := Ideal.absNorm_eq_one_iff.not.mpr 𝔭.isPrime.ne_top
  omega

end LanglandsTunnellBaseChangeAux

open LanglandsTunnellBaseChangeAux in
theorem solution
    (K : Type) [Field K] [NumberField K]
    [Algebra (NumberField.RingOfIntegers ℚ) (NumberField.RingOfIntegers K)]
    [Algebra.IsIntegral (NumberField.RingOfIntegers ℚ) (NumberField.RingOfIntegers K)]
    (Φ : AutomorphicForm.HeckeEigensystem ℚ ℂ)
    (hΦ : AutomorphicForm.IsArithGenuineCuspRealizable ℚ
      (AutomorphicForm.productionPinsGeneral ℚ) Φ)
    (SQ₀ : Finset (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ℚ)))
    (hb : ∀ p : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ℚ), p ∉ SQ₀ → ‖Φ.b p‖ = 1)
    (ha : ∀ σ : ℝ, 1 < σ →
      Summable fun p : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ℚ) =>
        ‖Φ.a p‖ * (Ideal.absNorm p.asIdeal : ℝ) ^ (-σ)) :
    ∃ Tq : Finset (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ℚ)),
      ∀ 𝔓 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K),
        𝔓.under (NumberField.RingOfIntegers ℚ) ∉ Tq →
          (AutomorphicForm.formalBaseChange ℚ K Φ).a 𝔓 ^ 2 ≠
            (AutomorphicForm.formalBaseChange ℚ K Φ).b 𝔓 *
              (((Ideal.absNorm 𝔓.asIdeal : ℕ) : ℂ) + 2 + ((Ideal.absNorm 𝔓.asIdeal : ℕ) : ℂ)⁻¹) := by
  have _ := hb
  have _ := ha
  obtain ⟨S, hS⟩ :=
    LanglandsTunnell.Converse.exists_finset_sq_eq_real_mul_b_and_norm_sq_lt_of_isArithGenuineCuspRealizable Φ hΦ
  refine ⟨S, fun 𝔓 h𝔓 => ?_⟩
  obtain ⟨⟨t, ht0, hat⟩, hab⟩ := hS (𝔓.under (NumberField.RingOfIntegers ℚ)) h𝔓
  rw [AutomorphicForm.formalBaseChange_a, AutomorphicForm.formalBaseChange_b, absNorm_eq_pow 𝔓]
  exact LanglandsTunnell.Converse.satakePow_sq_ne_of_sq_eq_real_mul_of_norm_sq_lt _ _ _
    (one_lt_absNorm (𝔓.under (NumberField.RingOfIntegers ℚ))) t ht0 hat hab _ (inertiaDeg_pos 𝔓)

end S_LanglandsTunnell_Converse_exists_formalBaseChange_generic_of_isArithGenuineCuspRealizable
end P2MW
export P2MW.S_LanglandsTunnell_Converse_exists_formalBaseChange_generic_of_isArithGenuineCuspRealizable (solution)
