-- Prove2me | solution 1 for LanglandsTunnell.satake_norm_lt_sqrt_absNorm_of_norm_b_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.670037+00:00
-- url     : https://prove2.me/submissions/af0f94ad-2ca3-5774-9809-83f9c445c107

import Definitions.Def_AutomorphicForm_IsotypicCuspSpace
import Definitions.Def_AutomorphicForm_HeckeEigenfunction
import Theorems.Thm_LanglandsTunnell_satake_norm_lt_sqrt_absNorm_of_not_dvd_level_of_not_mem_exceptionalSet
import Theorems.Thm_AutomorphicForm_SmoothCuspRealizationAt_isIdeleClassChar_and_admitsModulus_level_and_continuous_of_genuine
import Theorems.Thm_NumberField_TateGlobal_exists_norm_apply_eq_ideleNorm_rpow
import Theorems.Thm_NumberField_TateGlobal_ideleNorm_uniformizerIdele
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LanglandsTunnell_satake_norm_lt_sqrt_absNorm_of_norm_b_eq_one
p2m_attr_erase "instance" "instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions instCountableOfNumberField_definitions RestrictedProduct.SecondCountableTopology_of_principal instCountableElemSetSetsCofinite_definitions"
p2m_attr_erase "simp" "AdelicDock.coe_finEmbed AdelicDock.splice_apply_self AdelicDock.coe_localEmbed NumberField.StandardAddChar.ratArchLine_apply NumberField.StandardAddChar.AdelicTraceData.mk.sizeOf_spec NumberField.StandardAddChar.AdelicTraceData.mk.injEq AutomorphicForm.whittakerCoefficient_zero NumberField.AdelicTrace.traceDiag_apply NumberField.AdelicTrace.diag_apply LanglandsTunnell.TateLocal.conductorExponentAt_one LanglandsTunnell.TateLocal.charExt_coe_units LanglandsTunnell.TateLocal.modulus_one LanglandsTunnell.TateLocal.modulus_zero LanglandsTunnell.TateLocal.modulus_coe_units LanglandsTunnell.TateLocal.charExt_zero ContinuousAddEquiv.restrictedProductPi_apply RestrictedProduct.flatten_homeomorph_apply RestrictedProduct.flatten_homeomorph'_symm_apply ContinuousMulEquiv.restrictedProductPi_symm_apply RestrictedProduct.flatten_homeomorph'_apply RestrictedProduct.flatten_homeomorph_symm_apply ContinuousMulEquiv.restrictedProductPi_apply ContinuousAddEquiv.restrictedProductPi_symm_apply RingEquiv.restrictedProductCongr_symm_apply RingEquiv.restrictedProductCongrRight_apply MulEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductProd_symm_apply_coe Equiv.restrictedProductCongrRight_apply AddEquiv.restrictedProductCongr_apply Equiv.restrictedProductCongrLeft'_symm_apply_apply Equiv.restrictedProductCongr_apply_apply Equiv.restrictedProductCongrLeft_apply_apply RestrictedProduct.flatten_equiv'_apply AddEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductCongr_symm_apply Equiv.restrictedProductCongrRight_symm_apply RestrictedProduct.flatten_equiv'_symm_apply AddEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductCongrLeft'_apply RestrictedProduct.flatten_apply"
p2m_attr_erase "simp" "RingEquiv.restrictedProductCongr_apply_apply RingEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductProd_apply RestrictedProduct.flatten_equiv_apply RestrictedProduct.flatten_equiv_symm_apply LinearEquiv.restrictedProductCongrLeft'_apply RestrictedProduct.not_mem_support RestrictedProduct.mem_structureSubring_iff RestrictedProduct.not_mem_mulSupport RestrictedProduct.support_neg RestrictedProduct.mem_indexSupport_iff RestrictedProduct.mulSupport_inv RestrictedProduct.mapAlongLinearMap_apply"

set_option autoImplicit false

open IsDedekindDomain NumberField
open NumberField.AdelicLevel NumberField.AdelicBox
open AutomorphicForm AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering

private theorem det_diagOne_eq (F : Type) [Field F] [NumberField F] (a : (AdeleRing (𝓞 F) F)ˣ) :
    Matrix.GeneralLinearGroup.det (diagOne a) = a := by
  ext
  show (Matrix.diagonal ![((a : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F), 1]).det
    = ((a : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F)
  rw [Matrix.det_diagonal, Fin.prod_univ_two]
  simp

private theorem det_heckeGen_eq_uniformizerIdele (F : Type) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) :
    Matrix.GeneralLinearGroup.det (heckeGen (𝓞 F) F v) = uniformizerIdele F v := by
  show Matrix.GeneralLinearGroup.det (diagOne (uniformizerIdele F v)) = uniformizerIdele F v
  exact det_diagOne_eq F _

private theorem continuous_centralScalar_adelic (F : Type) [Field F] [NumberField F] :
    Continuous (centralScalar (𝓞 F) F) := by
  refine Units.continuous_iff.mpr ⟨?_, ?_⟩
  · have h := (continuous_pi fun _ : Fin 2 => (Units.continuous_val (M := AdeleRing (𝓞 F) F))).matrix_diagonal
    convert h using 1
    all_goals try rfl
  · have h := (continuous_pi fun _ : Fin 2 => (Units.continuous_coe_inv (M := AdeleRing (𝓞 F) F))).matrix_diagonal
    convert h using 1
    all_goals try rfl

private theorem continuous_centralChar_comp_topEquiv (F : Type) [Field F] [NumberField F]
    (D : Set (AdelicGL2 (𝓞 F) F)) (gen : HeightOneSpectrum (𝓞 F) → AdelicGL2 (𝓞 F) F) (B : Set (AdeleRing (𝓞 F) F))
    (Ψ : HeckeEigensystem F ℂ)
    (R : SmoothCuspRealizationAt F
      (productionPinsOf F D (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) gen B) Ψ)
    (hR : Continuous R.toFun) :
    Continuous (R.centralChar.comp Subgroup.topEquiv.symm.toMonoidHom) := by
  obtain ⟨g₀, hg₀⟩ := R.exists_ne_zero
  have key : ∀ x : (AdeleRing (𝓞 F) F)ˣ,
      (((R.centralChar.comp Subgroup.topEquiv.symm.toMonoidHom) x : ℂˣ) : ℂ)
        = R.toFun (centralScalar (𝓞 F) F x * g₀) / R.toFun g₀ := fun x =>
    R.centralChar_apply_eq (Subgroup.topEquiv.symm x) hg₀
  have hval : Continuous fun x : (AdeleRing (𝓞 F) F)ˣ =>
      (((R.centralChar.comp Subgroup.topEquiv.symm.toMonoidHom) x : ℂˣ) : ℂ) := by
    simp only [key]
    exact (hR.comp ((continuous_centralScalar_adelic F).mul continuous_const)).div_const _
  refine Units.continuous_iff.mpr ⟨hval, ?_⟩
  have hinv : (fun x : (AdeleRing (𝓞 F) F)ˣ =>
        ((((R.centralChar.comp Subgroup.topEquiv.symm.toMonoidHom) x)⁻¹ : ℂˣ) : ℂ))
      = fun x => (((R.centralChar.comp Subgroup.topEquiv.symm.toMonoidHom) x⁻¹ : ℂˣ) : ℂ) := by
    funext x
    rw [map_inv]
  rw [hinv]
  exact hval.comp continuous_inv

private theorem norm_b_eq_of_not_mem_exceptionalSet (F : Type) [Field F] [NumberField F]
    (D : Set (AdelicGL2 (𝓞 F) F)) (B : Set (AdeleRing (𝓞 F) F)) (Φ : HeckeEigensystem F ℂ)
    (R : SmoothCuspRealizationAt F
      (productionPinsOf F D (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v) B)
      Φ.toRawCentral)
    (hR : Continuous R.toFun) :
    ∃ τ : ℝ, ∀ v : HeightOneSpectrum (𝓞 F), v ∉ R.exceptionalSet →
      ‖Φ.b v‖ = ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) * ((Ideal.absNorm v.asIdeal : ℕ) : ℝ)⁻¹ ^ τ := by
  have hclass := (SmoothCuspRealizationAt.isIdeleClassChar_and_admitsModulus_level_and_continuous_of_genuine
    F D (fun v => heckeGen (𝓞 F) F v) B Φ.toRawCentral R).1
  have hcont := continuous_centralChar_comp_topEquiv F D (fun v => heckeGen (𝓞 F) F v) B Φ.toRawCentral R hR
  obtain ⟨τ, hτ⟩ := NumberField.TateGlobal.exists_norm_apply_eq_ideleNorm_rpow F _ hclass hcont
  refine ⟨τ, fun v hv => ?_⟩
  have hN0 : Ideal.absNorm v.asIdeal ≠ 0 := Ideal.absNorm_eq_zero_iff.not.mpr v.ne_bot
  have hNne : ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hN0
  have hlink := R.centralChar_det_gen_eq_b hv (Subgroup.topEquiv.symm (uniformizerIdele F v))
    (det_heckeGen_eq_uniformizerIdele F v).symm
  have hraw : Φ.toRawCentral.b v = ((Ideal.absNorm v.asIdeal : ℕ) : ℂ)⁻¹ * Φ.b v := rfl
  have hτu := hτ (uniformizerIdele F v)
  rw [NumberField.TateGlobal.ideleNorm_uniformizerIdele F v] at hτu
  have hval : ‖((R.centralChar (Subgroup.topEquiv.symm (uniformizerIdele F v)) : ℂˣ) : ℂ)‖
      = ((Ideal.absNorm v.asIdeal : ℕ) : ℝ)⁻¹ * ‖Φ.b v‖ := by
    rw [hlink, hraw, norm_mul, norm_inv, RCLike.norm_natCast (K := ℂ)]
  have key : ((Ideal.absNorm v.asIdeal : ℕ) : ℝ)⁻¹ * ‖Φ.b v‖ = ((Ideal.absNorm v.asIdeal : ℕ) : ℝ)⁻¹ ^ τ :=
    hval.symm.trans hτu
  exact (inv_mul_eq_iff_eq_mul₀ hNne).mp key

private theorem exponent_eq_one_of_norm_b_eq_one {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F))
    {τ : ℝ} {x : ℂ} (hx : ‖x‖ = 1)
    (h : ‖x‖ = ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) * ((Ideal.absNorm v.asIdeal : ℕ) : ℝ)⁻¹ ^ τ) : τ = 1 := by
  have hN0 : Ideal.absNorm v.asIdeal ≠ 0 := Ideal.absNorm_eq_zero_iff.not.mpr v.ne_bot
  have hN1 : Ideal.absNorm v.asIdeal ≠ 1 := fun h1 => v.isPrime.ne_top (Ideal.absNorm_eq_one_iff.mp h1)
  have hNr : (1 : ℝ) < ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) := by
    exact_mod_cast (show 1 < Ideal.absNorm v.asIdeal by omega)
  have hNpos : (0 : ℝ) < ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) := zero_lt_one.trans hNr
  rw [hx, Real.inv_rpow hNpos.le] at h
  have hNτ : ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) = ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ^ τ :=
    (mul_inv_eq_one₀ (Real.rpow_pos_of_pos hNpos τ).ne').mp h.symm
  have hlog := congrArg Real.log hNτ
  rw [Real.log_rpow hNpos] at hlog
  have hlog' : (1 : ℝ) * Real.log ((Ideal.absNorm v.asIdeal : ℕ) : ℝ)
      = τ * Real.log ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) := by
    rw [one_mul]
    exact hlog
  exact (mul_right_cancel₀ (Real.log_ne_zero_of_pos_of_ne_one hNpos hNr.ne') hlog').symm

theorem solution
    (F : Type) [Field F] [NumberField F]
    (c u d₁ d₂ : ℝ) (T : Finset (AdelicGL2 (𝓞 F) F))
    (hc : 0 < c) (hd₁ : 0 < d₁) (hd : d₁ < d₂)
    (hcov : CoversModCentre F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂))
    (Φ : HeckeEigensystem F ℂ)
    (R : SmoothCuspRealizationAt F
      (productionPinsOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂)
        (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v) (adelicBox F))
      Φ.toRawCentral)
    (hR : Continuous R.toFun) :
    ∀ v : HeightOneSpectrum (𝓞 F), ¬ v.asIdeal ∣ Φ.level → v ∉ R.exceptionalSet → ‖Φ.b v‖ = 1 →
        Φ.a v ^ 2 ≠ Φ.b v * (((Ideal.absNorm v.asIdeal : ℕ) : ℂ) + 2 + ((Ideal.absNorm v.asIdeal : ℕ) : ℂ)⁻¹) ∧
        ∃ α β : ℂ, α + β = Φ.a v ∧ α * β = Φ.b v ∧
          ‖α‖ < Real.sqrt ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ∧
          ‖β‖ < Real.sqrt ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) := by
  intro v₀ hv₀ hv₀e hb₀
  obtain ⟨τ, hτ⟩ := norm_b_eq_of_not_mem_exceptionalSet F _ _ Φ R hR
  have hτ1 : τ = 1 := exponent_eq_one_of_norm_b_eq_one v₀ hb₀ (hτ v₀ hv₀e)
  have hb : ∀ v : HeightOneSpectrum (𝓞 F), ¬ v.asIdeal ∣ Φ.level → v ∉ R.exceptionalSet → ‖Φ.b v‖ = 1 := by
    intro v _ hve
    have hN0 : Ideal.absNorm v.asIdeal ≠ 0 := Ideal.absNorm_eq_zero_iff.not.mpr v.ne_bot
    have hNne : ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hN0
    rw [hτ v hve, hτ1, Real.rpow_one, mul_inv_cancel₀ hNne]
  exact LanglandsTunnell.satake_norm_lt_sqrt_absNorm_of_not_dvd_level_of_not_mem_exceptionalSet
    F c u d₁ d₂ T hc hd₁ hd hcov Φ R hR hb v₀ hv₀ hv₀e

end S_LanglandsTunnell_satake_norm_lt_sqrt_absNorm_of_norm_b_eq_one
end P2MW
export P2MW.S_LanglandsTunnell_satake_norm_lt_sqrt_absNorm_of_norm_b_eq_one (solution)
