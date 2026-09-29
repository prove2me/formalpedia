-- Prove2me | solution 1 for LanglandsTunnell.Converse.eq_zero_or_exists_agreesAwayFromFinite_eisensteinTableOf_of_unipotent_invariant
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.353894+00:00
-- url     : https://prove2.me/submissions/10c95434-ac6e-5d7d-9f6a-ce260e9764d1

import Definitions.Def_AutomorphicForm_ArithCuspRealization
import Definitions.Def_AutomorphicForm_BorelSubgroup
import Definitions.Def_LanglandsTunnell_ConverseData
import Theorems.Thm_LanglandsTunnell_Converse_eq_zero_or_exists_continuous_torus_recursion_of_unipotent_invariant
import Theorems.Thm_ContinuousMap_exists_continuous_monoidHom_forall_sum_eq_zero_of_compactSpace
import Theorems.Thm_NumberField_TateGlobal_compactSpace_normOneIdeleClass
import Theorems.Thm_NumberField_TateGlobal_continuous_ideleNorm
import Theorems.Thm_NumberField_TateGlobal_ideleNorm_uniformizerIdele
import Theorems.Thm_NumberField_AdeleRing_distribHaarChar_algebraMap
import Theorems.Thm_NumberField_AdeleRing_distribHaarChar_eq_prod_norm_pow_mult_of_snd_eq_one
import Definitions.Def_NumberField_TateGlobalZeta
import Definitions.Def_M4aHerbrand_IdeleClassVocab
import Definitions.Def_NumberField_AdelicVolume
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LanglandsTunnell_Converse_eq_zero_or_exists_agreesAwayFromFinite_eisensteinTableOf_of_unipotent_invariant
p2m_attr_erase "instance" "instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions instCountableOfNumberField_definitions"
p2m_attr_erase "simp" "LocalGL2.transposeGL_val LocalGL2.transposeGL_one LocalGL2.swapUnit_val AdelicDock.coe_finEmbed AdelicDock.splice_apply_self AdelicDock.coe_localEmbed LocalGL2.coe_localRepSome LocalGL2.coe_diagPi LocalGL2.coe_localRepInf LocalGL2.coe_localRepSome_inv LocalGL2.coe_unipotentInt LocalGL2.coe_weylInt LocalGL2.coe_diagPi_inv AutomorphicForm.classSq_apply AutomorphicForm.classRepEmbedding_one AutomorphicForm.finIdeleExponentAt_one AutomorphicForm.classRepFinIdele_one AutomorphicForm.productionPinsGeneralOf_D AutomorphicForm.productionPinsGeneral_D AutomorphicForm.productionPinsGeneralOf_μ AutomorphicForm.productionPinsGeneralOf_U AutomorphicForm.productionPinsCompact_ν AutomorphicForm.productionPinsCompact_U AutomorphicForm.productionPinsCompact_D AutomorphicForm.productionPinsCompact_nS AutomorphicForm.productionPinsCompact_gen AutomorphicForm.productionPinsCompact_Z AutomorphicForm.productionPinsCompact_mS AutomorphicForm.productionPinsCompact_μ AutomorphicForm.productionPins_nS AutomorphicForm.productionPins_mS AutomorphicForm.productionPins_ν AutomorphicForm.productionPins_Z AutomorphicForm.productionPins_U AutomorphicForm.productionPins_μ AutomorphicForm.productionPins_gen AutomorphicForm.productionPins_D AutomorphicForm.SiegelCoordinates.upperUnit_apply_zero_zero AutomorphicForm.SiegelCoordinates.upperUnit_apply_one_zero AutomorphicForm.SiegelCoordinates.upperUnit_apply_one_one"
p2m_attr_erase "simp" "AutomorphicForm.SiegelCoordinates.upperUnit_apply_zero_one MeasureTheory.L2.kernelIntegralLM_apply"

set_option autoImplicit false

open IsDedekindDomain NumberField NumberField.AdelicLevel AutomorphicForm AutomorphicForm.SmoothCusp
open NumberField.TateGlobal M4aHerbrand NumberField.AdelicVolume MeasureTheory
open scoped Pointwise

noncomputable section

namespace C4bWall

variable (K : Type) [Field K] [NumberField K]

private theorem cw_exists_place_comap_eq (p : ℕ) (hp : p.Prime) :
    ∃ v : HeightOneSpectrum (𝓞 K), v.asIdeal.comap (algebraMap ℤ (𝓞 K)) = Ideal.span {(p : ℤ)} := by
  have hp0 : (p : ℤ) ≠ 0 := by exact_mod_cast hp.ne_zero
  haveI : (Ideal.span {(p : ℤ)}).IsPrime := (Ideal.span_singleton_prime hp0).mpr (Nat.prime_iff_prime_int.mp hp)
  have hinj : Function.Injective (algebraMap ℤ (𝓞 K)) := by
    rw [algebraMap_int_eq]
    exact Int.cast_injective
  obtain ⟨Q, -, hQ, hQP⟩ := Ideal.exists_ideal_over_prime_of_isIntegral (Ideal.span {(p : ℤ)}) (⊥ : Ideal (𝓞 K))
    (by rw [Ideal.comap_bot_of_injective (f := algebraMap ℤ (𝓞 K)) hinj]; exact bot_le)
  refine ⟨⟨Q, hQ, ?_⟩, hQP⟩
  rintro rfl
  rw [Ideal.comap_bot_of_injective (f := algebraMap ℤ (𝓞 K)) hinj] at hQP
  exact hp0 (Ideal.span_singleton_eq_bot.mp hQP.symm)

private theorem cw_exists_place_notMem (S : Finset (HeightOneSpectrum (𝓞 K))) :
    ∃ v : HeightOneSpectrum (𝓞 K), v ∉ S := by
  classical
  choose f hf using fun p : Nat.Primes => cw_exists_place_comap_eq K p.1 p.2
  have hinj : Function.Injective f := by
    intro p q hpq
    have h : Ideal.span {(p.1 : ℤ)} = Ideal.span {(q.1 : ℤ)} := by rw [← hf p, ← hf q, hpq]
    have hmem : (p.1 : ℤ) ∈ Ideal.span {(q.1 : ℤ)} := by
      rw [← h]
      exact Ideal.mem_span_singleton_self _
    have hdvd : q.1 ∣ p.1 := Int.natCast_dvd_natCast.mp (Ideal.mem_span_singleton.mp hmem)
    exact Subtype.ext ((Nat.prime_dvd_prime_iff_eq q.2 p.2).mp hdvd).symm
  obtain ⟨v, -, hv⟩ := (Set.infinite_range_of_injective hinj).exists_notMem_finset S
  exact ⟨v, hv⟩

private def cw_normPow (s : ℂ) : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ :=
  MonoidHom.mk'
    (fun t => Units.mk0 (Complex.exp (s * (Real.log (ideleNorm K t) : ℂ))) (Complex.exp_ne_zero _))
    (by
      intro a b
      ext
      simp only [Units.val_mk0, Units.val_mul]
      rw [ideleNorm_mul, Real.log_mul (ideleNorm_pos a).ne' (ideleNorm_pos b).ne', Complex.ofReal_add,
        mul_add, Complex.exp_add])

private theorem cw_normPow_apply (s : ℂ) (t : (AdeleRing (𝓞 K) K)ˣ) :
    ((cw_normPow K s t : ℂˣ) : ℂ) = Complex.exp (s * (Real.log (ideleNorm K t) : ℂ)) := rfl

private theorem cw_continuous_normPow (s : ℂ) : Continuous (cw_normPow K s) := by
  have hlog : Continuous fun t : (AdeleRing (𝓞 K) K)ˣ => (Real.log (ideleNorm K t) : ℂ) :=
    Complex.continuous_ofReal.comp ((continuous_ideleNorm K).log fun t => (ideleNorm_pos t).ne')
  have hval : Continuous fun t : (AdeleRing (𝓞 K) K)ˣ => Complex.exp (s * (Real.log (ideleNorm K t) : ℂ)) :=
    Complex.continuous_exp.comp (continuous_const.mul hlog)
  refine Units.continuous_iff.mpr ⟨hval, ?_⟩
  have heq : (fun t : (AdeleRing (𝓞 K) K)ˣ => (((cw_normPow K s t)⁻¹ : ℂˣ) : ℂ))
      = fun t => (Complex.exp (s * (Real.log (ideleNorm K t) : ℂ)))⁻¹ := by
    funext t
    rw [Units.val_inv_eq_inv_val, cw_normPow_apply]
  rw [heq]
  exact hval.inv₀ fun t => Complex.exp_ne_zero _

private def cw_prin (γ : Kˣ) : (AdeleRing (𝓞 K) K)ˣ :=
  Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) γ

private theorem cw_ideleNorm_prin (γ : Kˣ) : ideleNorm K (cw_prin K γ) = 1 := by
  letI : MeasurableSpace (AdeleRing (𝓞 K) K) := borel _
  haveI : BorelSpace (AdeleRing (𝓞 K) K) := ⟨rfl⟩
  have h := NumberField.AdeleRing.distribHaarChar_algebraMap K γ
  rw [RingHom.toMonoidHom_eq_coe] at h
  unfold ideleNorm cw_prin
  rw [h]
  simp

private theorem cw_normPow_prin (s : ℂ) (γ : Kˣ) : cw_normPow K s (cw_prin K γ) = 1 := by
  ext
  rw [cw_normPow_apply, cw_ideleNorm_prin, Real.log_one, Complex.ofReal_zero, mul_zero, Complex.exp_zero,
    Units.val_one]

private theorem cw_one_lt_absNorm (v : HeightOneSpectrum (𝓞 K)) : (1 : ℝ) < (Ideal.absNorm v.asIdeal : ℕ) := by
  have h0 : Ideal.absNorm v.asIdeal ≠ 0 := by
    rw [Ne, Ideal.absNorm_eq_zero_iff]
    exact v.ne_bot
  have h1 : Ideal.absNorm v.asIdeal ≠ 1 := by
    rw [Ne, Ideal.absNorm_eq_one_iff]
    exact v.isPrime.ne_top
  have : 1 < Ideal.absNorm v.asIdeal := by omega
  exact_mod_cast this

private theorem cw_normPow_uniformizerIdele (s : ℂ) (v : HeightOneSpectrum (𝓞 K)) :
    ((cw_normPow K s (uniformizerIdele K v) : ℂˣ) : ℂ)
      = Complex.exp (-(s * (Real.log ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) : ℂ))) := by
  rw [cw_normPow_apply, ideleNorm_uniformizerIdele, Real.log_inv, Complex.ofReal_neg, mul_neg]

private theorem cw_cNorm_eq (v : HeightOneSpectrum (𝓞 K)) :
    HeckeEigensystem.cNorm v = (((Ideal.absNorm v.asIdeal : ℕ) : ℝ) : ℂ) := by
  rw [HeckeEigensystem.cNorm, Complex.ofReal_natCast]

private theorem cw_normPow_neg_one_uniformizerIdele (v : HeightOneSpectrum (𝓞 K)) :
    ((cw_normPow K (-1) (uniformizerIdele K v) : ℂˣ) : ℂ) = HeckeEigensystem.cNorm v := by
  rw [cw_normPow_uniformizerIdele, cw_cNorm_eq]
  have hq : (0 : ℝ) < (Ideal.absNorm v.asIdeal : ℕ) := lt_trans zero_lt_one (cw_one_lt_absNorm K v)
  rw [show -((-1 : ℂ) * (Real.log ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) : ℂ))
      = (Real.log ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) : ℂ) by ring]
  rw [← Complex.ofReal_exp, Real.exp_log hq]

private theorem cw_exists_normPow_uniformizerIdele_eq (v : HeightOneSpectrum (𝓞 K)) {ρ : ℂ} (hρ : ρ ≠ 0) :
    ∃ s : ℂ, ((cw_normPow K s (uniformizerIdele K v) : ℂˣ) : ℂ) = ρ := by
  have hL0 : (Real.log ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) : ℂ) ≠ 0 := by
    rw [Ne, Complex.ofReal_eq_zero]
    exact (Real.log_pos (cw_one_lt_absNorm K v)).ne'
  refine ⟨-(Complex.log ρ) / (Real.log ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) : ℂ), ?_⟩
  rw [cw_normPow_uniformizerIdele]
  rw [show -(-(Complex.log ρ) / (Real.log ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) : ℂ)
        * (Real.log ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) : ℂ)) = Complex.log ρ by
    field_simp]
  exact Complex.exp_log hρ

private def cw_nval (s : ℂ) (x : (AdeleRing (𝓞 K) K)ˣ) : ℂ := ((cw_normPow K s x : ℂˣ) : ℂ)

private def cw_wval (s : ℂ) (x : (AdeleRing (𝓞 K) K)ˣ) : ℂ := (((cw_normPow K s x)⁻¹ : ℂˣ) : ℂ)

private theorem cw_nval_mul (s : ℂ) (x y : (AdeleRing (𝓞 K) K)ˣ) :
    cw_nval K s (x * y) = cw_nval K s x * cw_nval K s y := by
  unfold cw_nval
  rw [map_mul, Units.val_mul]

private theorem cw_wval_mul (s : ℂ) (x y : (AdeleRing (𝓞 K) K)ˣ) :
    cw_wval K s (x * y) = cw_wval K s x * cw_wval K s y := by
  unfold cw_wval
  rw [map_mul, mul_inv, Units.val_mul]

private theorem cw_nval_one (s : ℂ) : cw_nval K s 1 = 1 := by
  unfold cw_nval
  rw [map_one, Units.val_one]

private theorem cw_nval_mul_wval (s : ℂ) (x : (AdeleRing (𝓞 K) K)ˣ) : cw_nval K s x * cw_wval K s x = 1 := by
  unfold cw_nval cw_wval
  exact Units.mul_inv _

private theorem cw_nval_ne_zero (s : ℂ) (x : (AdeleRing (𝓞 K) K)ˣ) : cw_nval K s x ≠ 0 := (cw_normPow K s x).ne_zero

private theorem cw_nval_neg_one_uniformizerIdele (v : HeightOneSpectrum (𝓞 K)) :
    cw_nval K (-1) (uniformizerIdele K v) = HeckeEigensystem.cNorm v :=
  cw_normPow_neg_one_uniformizerIdele K v

private theorem cw_nval_prin (s : ℂ) (γ : Kˣ) : cw_nval K s (cw_prin K γ) = 1 := by
  unfold cw_nval
  rw [cw_normPow_prin, Units.val_one]

private theorem cw_wval_prin (s : ℂ) (γ : Kˣ) : cw_wval K s (cw_prin K γ) = 1 := by
  unfold cw_wval
  rw [cw_normPow_prin, inv_one, Units.val_one]

private theorem cw_continuous_wval (s : ℂ) : Continuous (cw_wval K s) :=
  Units.continuous_coe_inv.comp (cw_continuous_normPow K s)

private structure cw_Torus (Pi : HeckeEigensystem K ℂ) (S₁ : Finset (HeightOneSpectrum (𝓞 K)))
    (ψ : (AdeleRing (𝓞 K) K)ˣ × (AdeleRing (𝓞 K) K)ˣ → ℂ) : Prop where
  cont : Continuous ψ
  inv : ∀ (γ₁ γ₂ : Kˣ) (t₁ t₂ : (AdeleRing (𝓞 K) K)ˣ), ψ (cw_prin K γ₁ * t₁, cw_prin K γ₂ * t₂) = ψ (t₁, t₂)
  recA : ∀ v : HeightOneSpectrum (𝓞 K), v ∉ S₁ → ∀ t₁ t₂ : (AdeleRing (𝓞 K) K)ˣ,
    HeckeEigensystem.cNorm v * ψ (uniformizerIdele K v * t₁, t₂) + ψ (t₁, uniformizerIdele K v * t₂)
      = Pi.a v * ψ (t₁, t₂)
  recB : ∀ v : HeightOneSpectrum (𝓞 K), v ∉ S₁ → ∀ t₁ t₂ : (AdeleRing (𝓞 K) K)ˣ,
    ψ (uniformizerIdele K v * t₁, uniformizerIdele K v * t₂)
      = (HeckeEigensystem.cNorm v)⁻¹ * Pi.b v * ψ (t₁, t₂)

variable {K}
variable {Pi : HeckeEigensystem K ℂ} {S₁ : Finset (HeightOneSpectrum (𝓞 K))}

private theorem cw_Torus.shift_sub {ψ : (AdeleRing (𝓞 K) K)ˣ × (AdeleRing (𝓞 K) K)ˣ → ℂ}
    (hψ : cw_Torus K Pi S₁ ψ) (ϖ : (AdeleRing (𝓞 K) K)ˣ) (ρ : ℂ) :
    cw_Torus K Pi S₁ (fun t => ψ (ϖ * t.1, t.2) - ρ * ψ t) where
  cont := by
    have h1 : Continuous fun t : (AdeleRing (𝓞 K) K)ˣ × (AdeleRing (𝓞 K) K)ˣ => ψ (ϖ * t.1, t.2) :=
      hψ.cont.comp ((continuous_const.mul continuous_fst).prodMk continuous_snd)
    exact h1.sub (continuous_const.mul hψ.cont)
  inv := by
    intro γ₁ γ₂ t₁ t₂
    dsimp only
    rw [mul_left_comm ϖ (cw_prin K γ₁) t₁, hψ.inv, hψ.inv]
  recA := by
    intro v hv t₁ t₂
    dsimp only
    have hA := hψ.recA v hv (ϖ * t₁) t₂
    have hA' := hψ.recA v hv t₁ t₂
    rw [mul_left_comm ϖ (uniformizerIdele K v) t₁]
    linear_combination hA - ρ * hA'
  recB := by
    intro v hv t₁ t₂
    dsimp only
    have hB := hψ.recB v hv (ϖ * t₁) t₂
    have hB' := hψ.recB v hv t₁ t₂
    rw [mul_left_comm ϖ (uniformizerIdele K v) t₁]
    linear_combination hB - ρ * hB'

private theorem cw_Torus.b_ne_zero {ψ : (AdeleRing (𝓞 K) K)ˣ × (AdeleRing (𝓞 K) K)ˣ → ℂ}
    (hψ : cw_Torus K Pi S₁ ψ) {t₀ : (AdeleRing (𝓞 K) K)ˣ × (AdeleRing (𝓞 K) K)ˣ} (h0 : ψ t₀ ≠ 0)
    {v : HeightOneSpectrum (𝓞 K)} (hv : v ∉ S₁) : Pi.b v ≠ 0 := by
  intro hb
  apply h0
  have key := hψ.recB v hv ((uniformizerIdele K v)⁻¹ * t₀.1) ((uniformizerIdele K v)⁻¹ * t₀.2)
  rw [hb, mul_zero, zero_mul, mul_inv_cancel_left, mul_inv_cancel_left] at key
  simpa using key

private theorem cw_Torus.exists_eigen {ψ : (AdeleRing (𝓞 K) K)ˣ × (AdeleRing (𝓞 K) K)ˣ → ℂ}
    (hψ : cw_Torus K Pi S₁ ψ) {t₀ : (AdeleRing (𝓞 K) K)ˣ × (AdeleRing (𝓞 K) K)ˣ} (h0 : ψ t₀ ≠ 0)
    {v₀ : HeightOneSpectrum (𝓞 K)} (hv₀ : v₀ ∉ S₁) :
    ∃ (ψ' : (AdeleRing (𝓞 K) K)ˣ × (AdeleRing (𝓞 K) K)ˣ → ℂ) (ρ σ : ℂ),
      cw_Torus K Pi S₁ ψ' ∧ (∃ t, ψ' t ≠ 0) ∧ ρ ≠ 0 ∧ σ ≠ 0 ∧
      (∀ t₁ t₂, ψ' (uniformizerIdele K v₀ * t₁, t₂) = ρ * ψ' (t₁, t₂)) ∧
      (∀ t₁ t₂, ψ' (t₁, uniformizerIdele K v₀ * t₂) = σ * ψ' (t₁, t₂)) := by

  have hq0 : HeckeEigensystem.cNorm v₀ ≠ 0 := HeckeEigensystem.cNorm_ne_zero v₀
  have hqi : HeckeEigensystem.cNorm v₀ * (HeckeEigensystem.cNorm v₀)⁻¹ = 1 := mul_inv_cancel₀ hq0
  have hb0 : Pi.b v₀ ≠ 0 := hψ.b_ne_zero h0 hv₀
  have hc0 : (HeckeEigensystem.cNorm v₀)⁻¹ * Pi.b v₀ ≠ 0 := mul_ne_zero (inv_ne_zero hq0) hb0

  have hsqE := IsAlgClosed.exists_pow_nat_eq
    (discrim (HeckeEigensystem.cNorm v₀) (-Pi.a v₀) ((HeckeEigensystem.cNorm v₀)⁻¹ * Pi.b v₀)) (by norm_num : 0 < 2)
  obtain ⟨sq, hsq⟩ := hsqE
  have hρE := exists_quadratic_eq_zero hq0 ⟨sq, by rw [← hsq]; ring⟩
  obtain ⟨ρ₁, hρ₁⟩ := hρE

  have hprod : ρ₁ * (Pi.a v₀ * (HeckeEigensystem.cNorm v₀)⁻¹ - ρ₁)
      = ((HeckeEigensystem.cNorm v₀)⁻¹ * Pi.b v₀) * (HeckeEigensystem.cNorm v₀)⁻¹ := by
    linear_combination (-(HeckeEigensystem.cNorm v₀)⁻¹) * hρ₁ + ρ₁ ^ 2 * hqi
  have hρ₁0 : ρ₁ ≠ 0 := by
    intro h
    rw [h, zero_mul] at hprod
    exact mul_ne_zero hc0 (inv_ne_zero hq0) hprod.symm
  have hρ₂0 : Pi.a v₀ * (HeckeEigensystem.cNorm v₀)⁻¹ - ρ₁ ≠ 0 := by
    intro h
    rw [h, mul_zero] at hprod
    exact mul_ne_zero hc0 (inv_ne_zero hq0) hprod.symm

  have hrec : ∀ t₁ t₂, HeckeEigensystem.cNorm v₀ * ψ (uniformizerIdele K v₀ * (uniformizerIdele K v₀ * t₁), t₂)
      - Pi.a v₀ * ψ (uniformizerIdele K v₀ * t₁, t₂)
      + (HeckeEigensystem.cNorm v₀)⁻¹ * Pi.b v₀ * ψ (t₁, t₂) = 0 := by
    intro t₁ t₂
    have hA := hψ.recA v₀ hv₀ (uniformizerIdele K v₀ * t₁) t₂
    have hB := hψ.recB v₀ hv₀ t₁ t₂
    linear_combination hA - hB

  have key2 : ∀ (φ : (AdeleRing (𝓞 K) K)ˣ × (AdeleRing (𝓞 K) K)ˣ → ℂ) (ρ : ℂ), cw_Torus K Pi S₁ φ → ρ ≠ 0 →
      (∀ t₁ t₂, φ (uniformizerIdele K v₀ * t₁, t₂) = ρ * φ (t₁, t₂)) →
      ∀ t₁ t₂, φ (t₁, uniformizerIdele K v₀ * t₂)
        = ((HeckeEigensystem.cNorm v₀)⁻¹ * Pi.b v₀ * ρ⁻¹) * φ (t₁, t₂) := by
    intro φ ρ hφ hρ heig t₁ t₂
    have hρi : ρ * ρ⁻¹ = 1 := mul_inv_cancel₀ hρ
    have hB := hφ.recB v₀ hv₀ t₁ t₂
    have h1 := heig t₁ (uniformizerIdele K v₀ * t₂)
    rw [h1] at hB

    linear_combination ρ⁻¹ * hB - φ (t₁, uniformizerIdele K v₀ * t₂) * hρi
  by_cases hzero : ∀ t, ψ (uniformizerIdele K v₀ * t.1, t.2) - (Pi.a v₀ * (HeckeEigensystem.cNorm v₀)⁻¹ - ρ₁) * ψ t = 0
  ·
    have heig : ∀ t₁ t₂, ψ (uniformizerIdele K v₀ * t₁, t₂)
        = (Pi.a v₀ * (HeckeEigensystem.cNorm v₀)⁻¹ - ρ₁) * ψ (t₁, t₂) := by
      intro t₁ t₂
      have := hzero (t₁, t₂)
      dsimp only at this
      linear_combination this
    exact ⟨ψ, _, _, hψ, ⟨t₀, h0⟩, hρ₂0, mul_ne_zero hc0 (inv_ne_zero hρ₂0), heig, key2 ψ _ hψ hρ₂0 heig⟩
  · push Not at hzero
    obtain ⟨t, ht⟩ := hzero
    have hT : cw_Torus K Pi S₁ (fun t => ψ (uniformizerIdele K v₀ * t.1, t.2)
        - (Pi.a v₀ * (HeckeEigensystem.cNorm v₀)⁻¹ - ρ₁) * ψ t) := hψ.shift_sub _ _
    have heig : ∀ t₁ t₂, (fun t => ψ (uniformizerIdele K v₀ * t.1, t.2)
          - (Pi.a v₀ * (HeckeEigensystem.cNorm v₀)⁻¹ - ρ₁) * ψ t) (uniformizerIdele K v₀ * t₁, t₂)
        = ρ₁ * (fun t => ψ (uniformizerIdele K v₀ * t.1, t.2)
          - (Pi.a v₀ * (HeckeEigensystem.cNorm v₀)⁻¹ - ρ₁) * ψ t) (t₁, t₂) := by
      intro t₁ t₂
      dsimp only
      have h := hrec t₁ t₂
      linear_combination (HeckeEigensystem.cNorm v₀)⁻¹ * h
        - ((HeckeEigensystem.cNorm v₀)⁻¹ * ψ (t₁, t₂)) * hρ₁
        - (ψ (uniformizerIdele K v₀ * (uniformizerIdele K v₀ * t₁), t₂) - ρ₁ ^ 2 * ψ (t₁, t₂)) * hqi
    exact ⟨_, ρ₁, _, hT, ⟨t, ht⟩, hρ₁0, mul_ne_zero hc0 (inv_ne_zero hρ₁0), heig, key2 _ ρ₁ hT hρ₁0 heig⟩

private def cw_twistA (ψ' : (AdeleRing (𝓞 K) K)ˣ × (AdeleRing (𝓞 K) K)ˣ → ℂ) (s₁ s₂ : ℂ) :
    (AdeleRing (𝓞 K) K)ˣ × (AdeleRing (𝓞 K) K)ˣ → ℂ :=
  fun t => ψ' t * (cw_wval K s₁ t.1 * cw_wval K s₂ t.2)

private theorem cw_twistA_apply (ψ' : (AdeleRing (𝓞 K) K)ˣ × (AdeleRing (𝓞 K) K)ˣ → ℂ) (s₁ s₂ : ℂ)
    (t₁ t₂ : (AdeleRing (𝓞 K) K)ˣ) :
    cw_twistA ψ' s₁ s₂ (t₁, t₂) = ψ' (t₁, t₂) * (cw_wval K s₁ t₁ * cw_wval K s₂ t₂) := rfl

private theorem cw_continuous_twistA {ψ' : (AdeleRing (𝓞 K) K)ˣ × (AdeleRing (𝓞 K) K)ˣ → ℂ} (h : Continuous ψ')
    (s₁ s₂ : ℂ) : Continuous (cw_twistA ψ' s₁ s₂) :=
  h.mul (((cw_continuous_wval K s₁).comp continuous_fst).mul ((cw_continuous_wval K s₂).comp continuous_snd))

section Descent

variable (K)

private def cw_Dsub (ϖ : (AdeleRing (𝓞 K) K)ˣ) : Subgroup (AdeleRing (𝓞 K) K)ˣ :=
  principalIdeles (𝓞 K) K ⊔ Subgroup.zpowers ϖ

private def cw_Hc (ϖ : (AdeleRing (𝓞 K) K)ˣ) : Subgroup ((AdeleRing (𝓞 K) K)ˣ × (AdeleRing (𝓞 K) K)ˣ) :=
  ((cw_Dsub K ϖ).prod (cw_Dsub K ϖ)).topologicalClosure

private abbrev cw_Qsq (ϖ : (AdeleRing (𝓞 K) K)ˣ) : Type :=
  ((AdeleRing (𝓞 K) K)ˣ × (AdeleRing (𝓞 K) K)ˣ) ⧸ cw_Hc K ϖ

private scoped instance cw_isClosed_Hc (ϖ : (AdeleRing (𝓞 K) K)ˣ) :
    IsClosed ((cw_Hc K ϖ : Subgroup ((AdeleRing (𝓞 K) K)ˣ × (AdeleRing (𝓞 K) K)ˣ)) :
      Set ((AdeleRing (𝓞 K) K)ˣ × (AdeleRing (𝓞 K) K)ˣ)) :=
  Subgroup.isClosed_topologicalClosure _

private scoped instance cw_t2Space_Qsq (ϖ : (AdeleRing (𝓞 K) K)ˣ) : T2Space (cw_Qsq K ϖ) := inferInstance

variable {K}

private theorem cw_prin_mem_Dsub (ϖ : (AdeleRing (𝓞 K) K)ˣ) (γ : Kˣ) : cw_prin K γ ∈ cw_Dsub K ϖ :=
  Subgroup.mem_sup_left ⟨γ, rfl⟩

private theorem cw_zpow_mem_Dsub (ϖ : (AdeleRing (𝓞 K) K)ˣ) (n : ℤ) : ϖ ^ n ∈ cw_Dsub K ϖ :=
  Subgroup.mem_sup_right (Subgroup.zpow_mem _ (Subgroup.mem_zpowers ϖ) n)

private theorem cw_prod_le_Hc (ϖ : (AdeleRing (𝓞 K) K)ˣ) : (cw_Dsub K ϖ).prod (cw_Dsub K ϖ) ≤ cw_Hc K ϖ :=
  Subgroup.le_topologicalClosure _

private theorem cw_invariant_Hc {A : (AdeleRing (𝓞 K) K)ˣ × (AdeleRing (𝓞 K) K)ˣ → ℂ} (hA : Continuous A)
    (ϖ : (AdeleRing (𝓞 K) K)ˣ)
    (hγ₁ : ∀ (γ : Kˣ) (t : (AdeleRing (𝓞 K) K)ˣ × (AdeleRing (𝓞 K) K)ˣ), A ((cw_prin K γ, 1) * t) = A t)
    (hγ₂ : ∀ (γ : Kˣ) (t : (AdeleRing (𝓞 K) K)ˣ × (AdeleRing (𝓞 K) K)ˣ), A ((1, cw_prin K γ) * t) = A t)
    (hϖ₁ : ∀ t : (AdeleRing (𝓞 K) K)ˣ × (AdeleRing (𝓞 K) K)ˣ, A ((ϖ, 1) * t) = A t)
    (hϖ₂ : ∀ t : (AdeleRing (𝓞 K) K)ˣ × (AdeleRing (𝓞 K) K)ˣ, A ((1, ϖ) * t) = A t) :
    ∀ d ∈ cw_Hc K ϖ, ∀ t, A (d * t) = A t := by

  let St : Subgroup ((AdeleRing (𝓞 K) K)ˣ × (AdeleRing (𝓞 K) K)ˣ) :=
    { carrier := {d | ∀ t, A (d * t) = A t}
      mul_mem' := by
        intro x y hx hy t
        rw [mul_assoc, hx, hy]
      one_mem' := by
        intro t
        rw [one_mul]
      inv_mem' := by
        intro x hx t
        have h := hx (x⁻¹ * t)
        rw [mul_inv_cancel_left] at h
        exact h.symm }
  have hclosed : IsClosed (St : Set ((AdeleRing (𝓞 K) K)ˣ × (AdeleRing (𝓞 K) K)ˣ)) := by
    have heq : (St : Set ((AdeleRing (𝓞 K) K)ˣ × (AdeleRing (𝓞 K) K)ˣ)) = ⋂ t, {d | A (d * t) = A t} := by
      ext d
      simp only [Set.mem_iInter, Set.mem_setOf_eq]
      rfl
    rw [heq]
    exact isClosed_iInter fun t => isClosed_eq (hA.comp (continuous_id.mul continuous_const)) continuous_const
  have h1 : cw_Dsub K ϖ ≤ St.comap (MonoidHom.inl _ _) := by
    refine sup_le ?_ ?_
    · rintro _ ⟨γ, rfl⟩
      exact fun t => hγ₁ γ t
    · rw [Subgroup.zpowers_le]
      exact fun t => hϖ₁ t
  have h2 : cw_Dsub K ϖ ≤ St.comap (MonoidHom.inr _ _) := by
    refine sup_le ?_ ?_
    · rintro _ ⟨γ, rfl⟩
      exact fun t => hγ₂ γ t
    · rw [Subgroup.zpowers_le]
      exact fun t => hϖ₂ t
  have hgen : (cw_Dsub K ϖ).prod (cw_Dsub K ϖ) ≤ St := by
    rintro ⟨d₁, d₂⟩ hd
    rw [Subgroup.mem_prod] at hd
    have hsplit : ((d₁, d₂) : (AdeleRing (𝓞 K) K)ˣ × (AdeleRing (𝓞 K) K)ˣ) = (d₁, 1) * (1, d₂) := by
      rw [Prod.mk_mul_mk, mul_one, one_mul]
    rw [hsplit]
    exact St.mul_mem (h1 hd.1) (h2 hd.2)
  have hle : cw_Hc K ϖ ≤ St := Subgroup.topologicalClosure_minimal _ hgen hclosed
  intro d hd
  exact hle hd

private def cw_descend (ϖ : (AdeleRing (𝓞 K) K)ˣ) (A : (AdeleRing (𝓞 K) K)ˣ × (AdeleRing (𝓞 K) K)ˣ → ℂ)
    (hinv : ∀ d ∈ cw_Hc K ϖ, ∀ t, A (d * t) = A t) : cw_Qsq K ϖ → ℂ :=
  fun x => Quotient.liftOn' x A (by
    intro a b hab
    have hab' : a⁻¹ * b ∈ cw_Hc K ϖ := QuotientGroup.leftRel_apply.mp hab
    have hmem : b * a⁻¹ ∈ cw_Hc K ϖ := by
      rw [mul_comm]
      exact hab'
    have h := hinv (b * a⁻¹) hmem a
    rw [inv_mul_cancel_right] at h
    exact h.symm)

private theorem cw_continuous_descend (ϖ : (AdeleRing (𝓞 K) K)ˣ)
    (A : (AdeleRing (𝓞 K) K)ˣ × (AdeleRing (𝓞 K) K)ˣ → ℂ) (hA : Continuous A)
    (hinv : ∀ d ∈ cw_Hc K ϖ, ∀ t, A (d * t) = A t) : Continuous (cw_descend ϖ A hinv) := by
  rw [(QuotientGroup.isQuotientMap_mk (cw_Hc K ϖ)).continuous_iff]
  exact hA

omit [NumberField K] in

private theorem cw_exists_norm_eq (w : InfinitePlace K) {r : ℝ} (hr : 0 ≤ r) : ∃ a : w.Completion, ‖a‖ = r := by
  rcases InfinitePlace.isReal_or_isComplex w with hw | hw
  · obtain ⟨a, ha⟩ := InfinitePlace.Completion.surjective_extensionEmbeddingOfIsReal hw r
    refine ⟨a, ?_⟩
    have h := (InfinitePlace.Completion.isometry_extensionEmbeddingOfIsReal hw).norm_map_of_map_zero
      (map_zero _) a
    rw [← h, ha, Real.norm_eq_abs, abs_of_nonneg hr]
  · obtain ⟨a, ha⟩ := InfinitePlace.Completion.surjective_extensionEmbedding_of_isComplex hw (r : ℂ)
    refine ⟨a, ?_⟩
    have h := (InfinitePlace.Completion.isometry_extensionEmbedding w).norm_map_of_map_zero (map_zero _) a
    rw [← h, ha, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hr]

private theorem cw_ideleNorm_archUnitHom (w : InfinitePlace K) (a : (w.Completion)ˣ) :
    ideleNorm K (archUnitHom w a) = ‖(a : w.Completion)‖ ^ w.mult := by
  classical
  rw [archUnitHom_apply]
  unfold ideleNorm
  rw [NumberField.AdeleRing.distribHaarChar_eq_prod_norm_pow_mult_of_snd_eq_one K (archCentralUnit K w a)
    (archCentralUnit_snd w a)]
  rw [← Finset.prod_erase_mul _ _ (Finset.mem_univ w), archCentralUnit_fst_self]
  rw [Finset.prod_eq_one fun v hv => ?_]
  · rw [one_mul]
  · rw [archCentralUnit_fst_of_ne w a (Finset.ne_of_mem_erase hv), norm_one, one_pow]

private theorem cw_continuous_archUnitHom (w : InfinitePlace K) :
    Continuous (archUnitHom (F := K) w) := by
  have hval : Continuous fun a : (w.Completion)ˣ =>
      ((archUnitHom (F := K) w a : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K) := by
    have hfst : Continuous fun a : (w.Completion)ˣ =>
        ((archUnitHom (F := K) w a : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).1 := by
      refine continuous_pi fun v => ?_
      by_cases hv : v = w
      · rw [hv]
        have heq : (fun a : (w.Completion)ˣ =>
            ((archUnitHom (F := K) w a : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).1 w)
            = fun a => ((a : (w.Completion)ˣ) : w.Completion) := by
          funext a
          rw [archUnitHom_apply, archCentralUnit_fst_self]
        rw [heq]
        exact Units.continuous_val
      · have heq : (fun a : (w.Completion)ˣ =>
            ((archUnitHom (F := K) w a : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).1 v) = fun _ => 1 := by
          funext a
          rw [archUnitHom_apply, archCentralUnit_fst_of_ne w a hv]
        rw [heq]
        exact continuous_const
    have hsnd : Continuous fun a : (w.Completion)ˣ =>
        ((archUnitHom (F := K) w a : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).2 := by
      have heq : (fun a : (w.Completion)ˣ =>
          ((archUnitHom (F := K) w a : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).2) = fun _ => 1 := by
        funext a
        rw [archUnitHom_apply, archCentralUnit_snd]
      rw [heq]
      exact continuous_const
    exact hfst.prodMk hsnd
  refine Units.continuous_iff.mpr ⟨hval, ?_⟩

  have heq : (fun a : (w.Completion)ˣ => (((archUnitHom (F := K) w a)⁻¹ : (AdeleRing (𝓞 K) K)ˣ) :
      AdeleRing (𝓞 K) K)) = (fun a : (w.Completion)ˣ =>
        ((archUnitHom (F := K) w a : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K)) ∘ fun a => a⁻¹ := by
    funext a
    simp only [Function.comp_apply, map_inv]
  rw [heq]
  exact hval.comp continuous_inv

private theorem cw_compactSpace_Qsq (v₀ : HeightOneSpectrum (𝓞 K)) :
    CompactSpace (cw_Qsq K (uniformizerIdele K v₀)) := by
  classical
  haveI := NumberField.TateGlobal.compactSpace_normOneIdeleClass K

  have hker : ∀ (j : (AdeleRing (𝓞 K) K)ˣ →* (AdeleRing (𝓞 K) K)ˣ × (AdeleRing (𝓞 K) K)ˣ),
      (∀ y, j y = (y, 1) ∨ j y = (1, y)) →
      (principalIdeles (𝓞 K) K).subgroupOf (normOneIdeles K)
        ≤ ((QuotientGroup.mk' (cw_Hc K (uniformizerIdele K v₀))).comp (j.comp (normOneIdeles K).subtype)).ker := by
    intro j hj y hy
    rw [MonoidHom.mem_ker, MonoidHom.comp_apply, MonoidHom.comp_apply, Subgroup.coe_subtype,
      QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
    refine cw_prod_le_Hc (uniformizerIdele K v₀) ?_
    rw [Subgroup.mem_subgroupOf] at hy
    obtain ⟨γ, hγ⟩ := hy
    have hγ' : cw_prin K γ = (y : (AdeleRing (𝓞 K) K)ˣ) := hγ
    rcases hj (y : (AdeleRing (𝓞 K) K)ˣ) with h | h <;> rw [h, Subgroup.mem_prod]
    · refine ⟨?_, Subgroup.one_mem _⟩
      show (y : (AdeleRing (𝓞 K) K)ˣ) ∈ cw_Dsub K (uniformizerIdele K v₀)
      rw [← hγ']
      exact cw_prin_mem_Dsub (uniformizerIdele K v₀) γ
    · refine ⟨Subgroup.one_mem _, ?_⟩
      show (y : (AdeleRing (𝓞 K) K)ˣ) ∈ cw_Dsub K (uniformizerIdele K v₀)
      rw [← hγ']
      exact cw_prin_mem_Dsub (uniformizerIdele K v₀) γ
  let f₁ : (normOneIdeles K) ⧸ (principalIdeles (𝓞 K) K).subgroupOf (normOneIdeles K)
      →* cw_Qsq K (uniformizerIdele K v₀) :=
    QuotientGroup.lift _ ((QuotientGroup.mk' (cw_Hc K (uniformizerIdele K v₀))).comp
      ((MonoidHom.inl _ _).comp (normOneIdeles K).subtype)) (hker (MonoidHom.inl _ _) fun y => Or.inl rfl)
  let f₂ : (normOneIdeles K) ⧸ (principalIdeles (𝓞 K) K).subgroupOf (normOneIdeles K)
      →* cw_Qsq K (uniformizerIdele K v₀) :=
    QuotientGroup.lift _ ((QuotientGroup.mk' (cw_Hc K (uniformizerIdele K v₀))).comp
      ((MonoidHom.inr _ _).comp (normOneIdeles K).subtype)) (hker (MonoidHom.inr _ _) fun y => Or.inr rfl)
  have hπc : Continuous (QuotientGroup.mk' (cw_Hc K (uniformizerIdele K v₀))) := QuotientGroup.continuous_mk
  have hf₁c : Continuous f₁ := by
    rw [(QuotientGroup.isQuotientMap_mk _).continuous_iff]
    exact hπc.comp ((continuous_id.prodMk continuous_const).comp continuous_subtype_val)
  have hf₂c : Continuous f₂ := by
    rw [(QuotientGroup.isQuotientMap_mk _).continuous_iff]
    exact hπc.comp ((continuous_const.prodMk continuous_id).comp continuous_subtype_val)
  have hK₁ : IsCompact (Set.range f₁) := isCompact_range hf₁c
  have hK₂ : IsCompact (Set.range f₂) := isCompact_range hf₂c

  obtain ⟨w⟩ := (inferInstance : Nonempty (InfinitePlace K))
  have hq1 : (1 : ℝ) < ((Ideal.absNorm v₀.asIdeal : ℕ) : ℝ) := cw_one_lt_absNorm K v₀
  have hq0 : (0 : ℝ) < ((Ideal.absNorm v₀.asIdeal : ℕ) : ℝ) := lt_trans zero_lt_one hq1
  have hAnnC : IsCompact {z : ℂ | 1 ≤ ‖z‖ ∧ ‖z‖ ≤ ((Ideal.absNorm v₀.asIdeal : ℕ) : ℝ)} := by
    have heq : {z : ℂ | 1 ≤ ‖z‖ ∧ ‖z‖ ≤ ((Ideal.absNorm v₀.asIdeal : ℕ) : ℝ)}
        = Metric.closedBall (0 : ℂ) ((Ideal.absNorm v₀.asIdeal : ℕ) : ℝ) ∩ {z | 1 ≤ ‖z‖} := by
      ext z
      simp only [Set.mem_setOf_eq, Set.mem_inter_iff, Metric.mem_closedBall, dist_zero_right]
      tauto
    rw [heq]
    exact (isCompact_closedBall _ _).inter_right (isClosed_le continuous_const continuous_norm)
  have he := InfinitePlace.Completion.isometry_extensionEmbedding w
  have hAnn : IsCompact {a : w.Completion | 1 ≤ ‖a‖ ∧ ‖a‖ ≤ ((Ideal.absNorm v₀.asIdeal : ℕ) : ℝ)} := by
    have hpre : {a : w.Completion | 1 ≤ ‖a‖ ∧ ‖a‖ ≤ ((Ideal.absNorm v₀.asIdeal : ℕ) : ℝ)}
        = (InfinitePlace.Completion.extensionEmbedding w) ⁻¹'
            {z : ℂ | 1 ≤ ‖z‖ ∧ ‖z‖ ≤ ((Ideal.absNorm v₀.asIdeal : ℕ) : ℝ)} := by
      ext a
      simp only [Set.mem_setOf_eq, Set.mem_preimage, he.norm_map_of_map_zero (map_zero _)]
    rw [hpre]
    exact he.isClosedEmbedding.isCompact_preimage hAnnC
  let AnnU : Set (w.Completion)ˣ :=
    {u | 1 ≤ ‖(u : w.Completion)‖ ∧ ‖(u : w.Completion)‖ ≤ ((Ideal.absNorm v₀.asIdeal : ℕ) : ℝ)}
  have hAnnU : IsCompact AnnU := by
    rw [Units.isEmbedding_val₀.isCompact_iff]
    have heq : (Units.val : (w.Completion)ˣ → w.Completion) '' AnnU
        = {a : w.Completion | 1 ≤ ‖a‖ ∧ ‖a‖ ≤ ((Ideal.absNorm v₀.asIdeal : ℕ) : ℝ)} := by
      ext a
      constructor
      · rintro ⟨u, hu, rfl⟩
        exact hu
      · intro ha
        have ha0 : a ≠ 0 := by
          rintro rfl
          have h1 : (1 : ℝ) ≤ ‖(0 : w.Completion)‖ := ha.1
          rw [norm_zero] at h1
          exact absurd h1 (by norm_num)
        exact ⟨Units.mk0 a ha0, ha, rfl⟩
    rw [heq]
    exact hAnn
  let arc₁ : Set (cw_Qsq K (uniformizerIdele K v₀)) := QuotientGroup.mk' (cw_Hc K (uniformizerIdele K v₀)) ''
    ((fun a => ((archUnitHom (F := K) w a, 1) : (AdeleRing (𝓞 K) K)ˣ × (AdeleRing (𝓞 K) K)ˣ)) '' AnnU)
  let arc₂ : Set (cw_Qsq K (uniformizerIdele K v₀)) := QuotientGroup.mk' (cw_Hc K (uniformizerIdele K v₀)) ''
    ((fun a => ((1, archUnitHom (F := K) w a) : (AdeleRing (𝓞 K) K)ˣ × (AdeleRing (𝓞 K) K)ˣ)) '' AnnU)
  have harc₁ : IsCompact arc₁ :=
    (hAnnU.image ((cw_continuous_archUnitHom w).prodMk continuous_const)).image hπc
  have harc₂ : IsCompact arc₂ :=
    (hAnnU.image (continuous_const.prodMk (cw_continuous_archUnitHom w))).image hπc

  have hwindow : ∀ x : (AdeleRing (𝓞 K) K)ˣ, ∃ (n : ℤ) (y : (AdeleRing (𝓞 K) K)ˣ) (a : (w.Completion)ˣ),
      y ∈ normOneIdeles K ∧ a ∈ AnnU ∧ x = uniformizerIdele K v₀ ^ n * (y * archUnitHom (F := K) w a) := by
    intro x
    have hx0 : 0 < ideleNorm K x := ideleNorm_pos x
    obtain ⟨m, hm⟩ := exists_mem_Ico_zpow hx0 hq1
    have hqm : (0 : ℝ) < ((Ideal.absNorm v₀.asIdeal : ℕ) : ℝ) ^ m := zpow_pos hq0 m

    have hr1 : 1 ≤ ideleNorm K x / ((Ideal.absNorm v₀.asIdeal : ℕ) : ℝ) ^ m := by
      rw [le_div_iff₀ hqm, one_mul]
      exact hm.1
    have hrq : ideleNorm K x / ((Ideal.absNorm v₀.asIdeal : ℕ) : ℝ) ^ m ≤ ((Ideal.absNorm v₀.asIdeal : ℕ) : ℝ) := by
      rw [div_le_iff₀ hqm]
      have h2 := hm.2
      rw [zpow_add_one₀ hq0.ne'] at h2
      linarith
    have hr0 : 0 ≤ ideleNorm K x / ((Ideal.absNorm v₀.asIdeal : ℕ) : ℝ) ^ m := le_trans zero_le_one hr1
    have hmult : (0 : ℝ) < w.mult := by exact_mod_cast (InfinitePlace.mult_pos (w := w))
    obtain ⟨b, hb⟩ := cw_exists_norm_eq w (Real.rpow_nonneg hr0 ((w.mult : ℝ)⁻¹))
    have hbpow : ‖b‖ ^ w.mult = ideleNorm K x / ((Ideal.absNorm v₀.asIdeal : ℕ) : ℝ) ^ m := by
      rw [hb, ← Real.rpow_natCast, ← Real.rpow_mul hr0, inv_mul_cancel₀ hmult.ne', Real.rpow_one]
    have hb1 : 1 ≤ ‖b‖ := by
      by_contra hlt
      push Not at hlt
      have : ‖b‖ ^ w.mult < 1 := pow_lt_one₀ (norm_nonneg _) hlt (InfinitePlace.mult_pos (w := w)).ne'
      linarith
    have hb0 : b ≠ 0 := by
      intro h
      rw [h, norm_zero] at hb1
      exact absurd hb1 (by norm_num)
    have hbq : ‖b‖ ≤ ((Ideal.absNorm v₀.asIdeal : ℕ) : ℝ) := by
      by_contra hlt
      push Not at hlt
      have h1 : ((Ideal.absNorm v₀.asIdeal : ℕ) : ℝ) ^ 1 ≤ ((Ideal.absNorm v₀.asIdeal : ℕ) : ℝ) ^ w.mult :=
        pow_le_pow_right₀ hq1.le (Nat.succ_le_of_lt (InfinitePlace.mult_pos (w := w)))
      have h2 : ((Ideal.absNorm v₀.asIdeal : ℕ) : ℝ) ^ w.mult < ‖b‖ ^ w.mult :=
        pow_lt_pow_left₀ hlt hq0.le (InfinitePlace.mult_pos (w := w)).ne'
      rw [pow_one] at h1
      linarith
    have ha_norm : ideleNorm K (archUnitHom (F := K) w (Units.mk0 b hb0))
        = ideleNorm K x / ((Ideal.absNorm v₀.asIdeal : ℕ) : ℝ) ^ m := by
      rw [cw_ideleNorm_archUnitHom, Units.val_mk0, hbpow]
    have hϖn : ideleNorm K (uniformizerIdele K v₀ ^ (-m)) = ((Ideal.absNorm v₀.asIdeal : ℕ) : ℝ) ^ m := by
      have h1 : ideleNorm K (uniformizerIdele K v₀ ^ (-m)) = (ideleNorm K (uniformizerIdele K v₀)) ^ (-m) := by
        unfold ideleNorm
        rw [map_zpow, NNReal.coe_zpow]
      rw [h1, ideleNorm_uniformizerIdele, inv_zpow', neg_neg]
    have hinv : ∀ z : (AdeleRing (𝓞 K) K)ˣ, ideleNorm K z⁻¹ = (ideleNorm K z)⁻¹ := by
      intro z
      unfold ideleNorm
      rw [map_inv, NNReal.coe_inv]
    refine ⟨-m, (uniformizerIdele K v₀ ^ (-m))⁻¹ * x * (archUnitHom (F := K) w (Units.mk0 b hb0))⁻¹,
      Units.mk0 b hb0, ?_, ⟨hb1, hbq⟩, ?_⟩
    · have hx0' : ideleNorm K x ≠ 0 := hx0.ne'
      have hqm' : ((Ideal.absNorm v₀.asIdeal : ℕ) : ℝ) ^ m ≠ 0 := hqm.ne'
      rw [mem_normOneIdeles_iff, ideleNorm_mul, ideleNorm_mul, hinv, hinv, hϖn, ha_norm]
      field_simp
    · group

  have hcover : (Set.univ : Set (cw_Qsq K (uniformizerIdele K v₀)))
      ⊆ (Set.range f₁ * Set.range f₂) * (arc₁ * arc₂) := by
    intro z _
    obtain ⟨⟨x₁, x₂⟩, rfl⟩ := QuotientGroup.mk_surjective z
    obtain ⟨n₁, y₁, a₁, hy₁, ha₁, hx₁⟩ := hwindow x₁
    obtain ⟨n₂, y₂, a₂, hy₂, ha₂, hx₂⟩ := hwindow x₂
    have hclass : (QuotientGroup.mk (x₁, x₂) : cw_Qsq K (uniformizerIdele K v₀))
        = QuotientGroup.mk ((y₁ * archUnitHom (F := K) w a₁, y₂ * archUnitHom (F := K) w a₂)) := by
      rw [QuotientGroup.eq]
      have hdiff : ((x₁, x₂) : (AdeleRing (𝓞 K) K)ˣ × (AdeleRing (𝓞 K) K)ˣ)⁻¹
          * (y₁ * archUnitHom (F := K) w a₁, y₂ * archUnitHom (F := K) w a₂)
          = ((uniformizerIdele K v₀ ^ n₁)⁻¹, (uniformizerIdele K v₀ ^ n₂)⁻¹) := by
        rw [hx₁, hx₂]
        refine Prod.ext ?_ ?_
        · show (uniformizerIdele K v₀ ^ n₁ * (y₁ * archUnitHom (F := K) w a₁))⁻¹
              * (y₁ * archUnitHom (F := K) w a₁) = (uniformizerIdele K v₀ ^ n₁)⁻¹
          rw [mul_inv, inv_mul_cancel_right]
        · show (uniformizerIdele K v₀ ^ n₂ * (y₂ * archUnitHom (F := K) w a₂))⁻¹
              * (y₂ * archUnitHom (F := K) w a₂) = (uniformizerIdele K v₀ ^ n₂)⁻¹
          rw [mul_inv, inv_mul_cancel_right]
      rw [hdiff]
      exact cw_prod_le_Hc _ (Subgroup.mem_prod.mpr
        ⟨Subgroup.inv_mem _ (cw_zpow_mem_Dsub _ n₁), Subgroup.inv_mem _ (cw_zpow_mem_Dsub _ n₂)⟩)
    have hsplit : ((y₁ * archUnitHom (F := K) w a₁, y₂ * archUnitHom (F := K) w a₂) :
        (AdeleRing (𝓞 K) K)ˣ × (AdeleRing (𝓞 K) K)ˣ)
        = ((y₁, 1) * (1, y₂)) * ((archUnitHom (F := K) w a₁, 1) * (1, archUnitHom (F := K) w a₂)) := by
      simp only [Prod.mk_mul_mk, one_mul, mul_one]
    rw [hclass, hsplit, ← QuotientGroup.mk'_apply (cw_Hc K (uniformizerIdele K v₀)), map_mul, map_mul, map_mul]
    refine Set.mul_mem_mul (Set.mul_mem_mul ⟨QuotientGroup.mk ⟨y₁, hy₁⟩, rfl⟩ ⟨QuotientGroup.mk ⟨y₂, hy₂⟩, rfl⟩)
      (Set.mul_mem_mul ⟨_, ⟨a₁, ha₁, rfl⟩, rfl⟩ ⟨_, ⟨a₂, ha₂, rfl⟩, rfl⟩)
  have hcompact : IsCompact ((Set.range f₁ * Set.range f₂) * (arc₁ * arc₂)) := (hK₁.mul hK₂).mul (harc₁.mul harc₂)
  exact isCompact_univ_iff.mp (hcompact.of_isClosed_subset isClosed_univ hcover)

end Descent

private def cw_rel3 {G : Type*} [MulOneClass G] (g₁ g₂ : G) (c₁ c₂ c₃ : ℂ) : G →₀ ℂ :=
  Finsupp.single g₁ c₁ + Finsupp.single g₂ c₂ + Finsupp.single 1 c₃

private def cw_rel2 {G : Type*} [MulOneClass G] (g₁ : G) (c₁ c₂ : ℂ) : G →₀ ℂ :=
  Finsupp.single g₁ c₁ + Finsupp.single 1 c₂

private theorem cw_rel3_sum {G : Type*} [MulOneClass G] (g₁ g₂ : G) (c₁ c₂ c₃ : ℂ) (F : G → ℂ) :
    ((cw_rel3 g₁ g₂ c₁ c₂ c₃).sum fun g c => c * F g) = c₁ * F g₁ + c₂ * F g₂ + c₃ * F 1 := by
  classical
  unfold cw_rel3
  rw [Finsupp.sum_add_index', Finsupp.sum_add_index', Finsupp.sum_single_index, Finsupp.sum_single_index,
    Finsupp.sum_single_index]
  all_goals first
    | exact zero_mul _
    | (intro a; exact zero_mul _)
    | (intro a b₁ b₂; exact add_mul _ _ _)

private theorem cw_rel2_sum {G : Type*} [MulOneClass G] (g₁ : G) (c₁ c₂ : ℂ) (F : G → ℂ) :
    ((cw_rel2 g₁ c₁ c₂).sum fun g c => c * F g) = c₁ * F g₁ + c₂ * F 1 := by
  classical
  unfold cw_rel2
  rw [Finsupp.sum_add_index', Finsupp.sum_single_index, Finsupp.sum_single_index]
  all_goals first
    | exact zero_mul _
    | (intro a; exact zero_mul _)
    | (intro a b₁ b₂; exact add_mul _ _ _)

private theorem cw_twistA_invariant {ψ' : (AdeleRing (𝓞 K) K)ˣ × (AdeleRing (𝓞 K) K)ˣ → ℂ}
    (hT : cw_Torus K Pi S₁ ψ') {ϖ₀ : (AdeleRing (𝓞 K) K)ˣ} {ρ σ s₁ s₂ : ℂ}
    (heig₁ : ∀ t₁ t₂, ψ' (ϖ₀ * t₁, t₂) = ρ * ψ' (t₁, t₂))
    (heig₂ : ∀ t₁ t₂, ψ' (t₁, ϖ₀ * t₂) = σ * ψ' (t₁, t₂))
    (hρW : ρ * cw_wval K s₁ ϖ₀ = 1) (hσW : σ * cw_wval K s₂ ϖ₀ = 1) :
    ∀ d ∈ cw_Hc K ϖ₀, ∀ t, cw_twistA ψ' s₁ s₂ (d * t) = cw_twistA ψ' s₁ s₂ t := by
  have hAγ₁ : ∀ (γ : Kˣ) (t : (AdeleRing (𝓞 K) K)ˣ × (AdeleRing (𝓞 K) K)ˣ),
      cw_twistA ψ' s₁ s₂ ((cw_prin K γ, 1) * t) = cw_twistA ψ' s₁ s₂ t := by
    rintro γ ⟨t₁, t₂⟩
    have h := hT.inv γ 1 t₁ t₂
    rw [show cw_prin K (1 : Kˣ) = 1 from map_one _, one_mul] at h
    rw [Prod.mk_mul_mk, one_mul, cw_twistA_apply, cw_twistA_apply, cw_wval_mul, cw_wval_prin, one_mul, h]
  have hAγ₂ : ∀ (γ : Kˣ) (t : (AdeleRing (𝓞 K) K)ˣ × (AdeleRing (𝓞 K) K)ˣ),
      cw_twistA ψ' s₁ s₂ ((1, cw_prin K γ) * t) = cw_twistA ψ' s₁ s₂ t := by
    rintro γ ⟨t₁, t₂⟩
    have h := hT.inv 1 γ t₁ t₂
    rw [show cw_prin K (1 : Kˣ) = 1 from map_one _, one_mul] at h
    rw [Prod.mk_mul_mk, one_mul, cw_twistA_apply, cw_twistA_apply, cw_wval_mul, cw_wval_prin, one_mul, h]
  have hAϖ₁ : ∀ t : (AdeleRing (𝓞 K) K)ˣ × (AdeleRing (𝓞 K) K)ˣ,
      cw_twistA ψ' s₁ s₂ ((ϖ₀, 1) * t) = cw_twistA ψ' s₁ s₂ t := by
    rintro ⟨t₁, t₂⟩
    rw [Prod.mk_mul_mk, one_mul, cw_twistA_apply, cw_twistA_apply, cw_wval_mul, heig₁]
    linear_combination (ψ' (t₁, t₂) * cw_wval K s₁ t₁ * cw_wval K s₂ t₂) * hρW
  have hAϖ₂ : ∀ t : (AdeleRing (𝓞 K) K)ˣ × (AdeleRing (𝓞 K) K)ˣ,
      cw_twistA ψ' s₁ s₂ ((1, ϖ₀) * t) = cw_twistA ψ' s₁ s₂ t := by
    rintro ⟨t₁, t₂⟩
    rw [Prod.mk_mul_mk, one_mul, cw_twistA_apply, cw_twistA_apply, cw_wval_mul, heig₂]
    linear_combination (ψ' (t₁, t₂) * cw_wval K s₁ t₁ * cw_wval K s₂ t₂) * hσW
  exact cw_invariant_Hc (cw_continuous_twistA hT.cont s₁ s₂) _ hAγ₁ hAγ₂ hAϖ₁ hAϖ₂

private theorem cw_twistA_recA {ψ' : (AdeleRing (𝓞 K) K)ˣ × (AdeleRing (𝓞 K) K)ˣ → ℂ}
    (hT : cw_Torus K Pi S₁ ψ') (s₁ s₂ : ℂ) {v : HeightOneSpectrum (𝓞 K)} (hv : v ∉ S₁)
    (t : (AdeleRing (𝓞 K) K)ˣ × (AdeleRing (𝓞 K) K)ˣ) :
    HeckeEigensystem.cNorm v * cw_nval K s₁ (uniformizerIdele K v)
        * cw_twistA ψ' s₁ s₂ ((uniformizerIdele K v, 1) * t)
      + cw_nval K s₂ (uniformizerIdele K v) * cw_twistA ψ' s₁ s₂ ((1, uniformizerIdele K v) * t)
      + (-Pi.a v) * cw_twistA ψ' s₁ s₂ t = 0 := by
  obtain ⟨t₁, t₂⟩ := t
  have h := hT.recA v hv t₁ t₂
  have e₁ := cw_nval_mul_wval K s₁ (uniformizerIdele K v)
  have e₂ := cw_nval_mul_wval K s₂ (uniformizerIdele K v)
  rw [Prod.mk_mul_mk, Prod.mk_mul_mk, one_mul, one_mul, cw_twistA_apply, cw_twistA_apply, cw_twistA_apply,
    cw_wval_mul, cw_wval_mul]
  linear_combination (cw_wval K s₁ t₁ * cw_wval K s₂ t₂) * h
    + (cw_wval K s₁ t₁ * cw_wval K s₂ t₂ * HeckeEigensystem.cNorm v * ψ' (uniformizerIdele K v * t₁, t₂)) * e₁
    + (cw_wval K s₁ t₁ * cw_wval K s₂ t₂ * ψ' (t₁, uniformizerIdele K v * t₂)) * e₂

private theorem cw_twistA_recB {ψ' : (AdeleRing (𝓞 K) K)ˣ × (AdeleRing (𝓞 K) K)ˣ → ℂ}
    (hT : cw_Torus K Pi S₁ ψ') (s₁ s₂ : ℂ) {v : HeightOneSpectrum (𝓞 K)} (hv : v ∉ S₁)
    (t : (AdeleRing (𝓞 K) K)ˣ × (AdeleRing (𝓞 K) K)ˣ) :
    cw_nval K s₁ (uniformizerIdele K v) * cw_nval K s₂ (uniformizerIdele K v)
        * cw_twistA ψ' s₁ s₂ ((uniformizerIdele K v, uniformizerIdele K v) * t)
      + (-((HeckeEigensystem.cNorm v)⁻¹ * Pi.b v)) * cw_twistA ψ' s₁ s₂ t = 0 := by
  obtain ⟨t₁, t₂⟩ := t
  have h := hT.recB v hv t₁ t₂
  have e₁ := cw_nval_mul_wval K s₁ (uniformizerIdele K v)
  have e₂ := cw_nval_mul_wval K s₂ (uniformizerIdele K v)
  rw [Prod.mk_mul_mk, cw_twistA_apply, cw_twistA_apply, cw_wval_mul, cw_wval_mul]
  linear_combination (cw_wval K s₁ t₁ * cw_wval K s₂ t₂ * cw_wval K s₁ (uniformizerIdele K v)
        * cw_wval K s₂ (uniformizerIdele K v) * cw_nval K s₁ (uniformizerIdele K v)
        * cw_nval K s₂ (uniformizerIdele K v)) * h
    + ((HeckeEigensystem.cNorm v)⁻¹ * Pi.b v * ψ' (t₁, t₂) * cw_wval K s₁ t₁ * cw_wval K s₂ t₂
        * cw_nval K s₂ (uniformizerIdele K v) * cw_wval K s₂ (uniformizerIdele K v)) * e₁
    + ((HeckeEigensystem.cNorm v)⁻¹ * Pi.b v * ψ' (t₁, t₂) * cw_wval K s₁ t₁ * cw_wval K s₂ t₂) * e₂

private theorem cw_main_chi {ψ : (AdeleRing (𝓞 K) K)ˣ × (AdeleRing (𝓞 K) K)ˣ → ℂ} (hψT : cw_Torus K Pi S₁ ψ)
    (hψ0 : ψ (1, 1) ≠ 0) {v₀ : HeightOneSpectrum (𝓞 K)} (hv₀ : v₀ ∉ S₁) :
    ∃ (s₁ s₂ : ℂ) (χ : cw_Qsq K (uniformizerIdele K v₀) →* ℂˣ), Continuous χ ∧
      ∀ v : HeightOneSpectrum (𝓞 K), v ≠ v₀ → v ∉ S₁ →
        HeckeEigensystem.cNorm v * cw_nval K s₁ (uniformizerIdele K v)
            * ((χ (QuotientGroup.mk (uniformizerIdele K v, 1)) : ℂˣ) : ℂ)
          + cw_nval K s₂ (uniformizerIdele K v) * ((χ (QuotientGroup.mk (1, uniformizerIdele K v)) : ℂˣ) : ℂ)
          + (-Pi.a v) = 0 ∧
        cw_nval K s₁ (uniformizerIdele K v) * cw_nval K s₂ (uniformizerIdele K v)
            * ((χ (QuotientGroup.mk (uniformizerIdele K v, uniformizerIdele K v)) : ℂˣ) : ℂ)
          + (-((HeckeEigensystem.cNorm v)⁻¹ * Pi.b v)) = 0 := by
  classical
  have hE := hψT.exists_eigen hψ0 hv₀
  obtain ⟨ψ', ρ, σ, hT, ⟨t₀, ht₀⟩, hρ, hσ, heig₁, heig₂⟩ := hE
  have hS₁ := cw_exists_normPow_uniformizerIdele_eq K v₀ hρ
  have hS₂ := cw_exists_normPow_uniformizerIdele_eq K v₀ hσ
  obtain ⟨s₁, hs₁⟩ := hS₁
  obtain ⟨s₂, hs₂⟩ := hS₂
  have hρW : ρ * cw_wval K s₁ (uniformizerIdele K v₀) = 1 := by
    rw [← hs₁]; exact cw_nval_mul_wval K s₁ _
  have hσW : σ * cw_wval K s₂ (uniformizerIdele K v₀) = 1 := by
    rw [← hs₂]; exact cw_nval_mul_wval K s₂ _
  have hAcont : Continuous (cw_twistA ψ' s₁ s₂) := cw_continuous_twistA hT.cont s₁ s₂
  obtain ⟨t₀₁, t₀₂⟩ := t₀
  have hA0 : cw_twistA ψ' s₁ s₂ (t₀₁, t₀₂) ≠ 0 := by
    rw [cw_twistA_apply]
    refine mul_ne_zero ht₀ (mul_ne_zero ?_ ?_)
    · exact ((cw_normPow K s₁ t₀₁)⁻¹).ne_zero
    · exact ((cw_normPow K s₂ t₀₂)⁻¹).ne_zero
  have hAinv : ∀ d ∈ cw_Hc K (uniformizerIdele K v₀), ∀ t, cw_twistA ψ' s₁ s₂ (d * t) = cw_twistA ψ' s₁ s₂ t :=
    cw_twistA_invariant hT heig₁ heig₂ hρW hσW

  haveI : CompactSpace (cw_Qsq K (uniformizerIdele K v₀)) := cw_compactSpace_Qsq v₀
  let f : C(cw_Qsq K (uniformizerIdele K v₀), ℂ) :=
    ⟨cw_descend _ (cw_twistA ψ' s₁ s₂) hAinv, cw_continuous_descend _ _ hAcont hAinv⟩
  have hfmk : ∀ t, f (QuotientGroup.mk t) = cw_twistA ψ' s₁ s₂ t := fun t => rfl
  have hf0 : f ≠ 0 := by
    intro h
    apply hA0
    rw [← hfmk (t₀₁, t₀₂), h]
    rfl

  let π : (AdeleRing (𝓞 K) K)ˣ × (AdeleRing (𝓞 K) K)ˣ →* cw_Qsq K (uniformizerIdele K v₀) :=
    QuotientGroup.mk' (cw_Hc K (uniformizerIdele K v₀))
  have hπmk : ∀ t, π t = QuotientGroup.mk t := fun t => rfl
  let good : Set (HeightOneSpectrum (𝓞 K)) := {v | v ≠ v₀ ∧ v ∉ S₁}
  let RA : HeightOneSpectrum (𝓞 K) → (cw_Qsq K (uniformizerIdele K v₀) →₀ ℂ) := fun v =>
    cw_rel3 (π (uniformizerIdele K v, 1)) (π (1, uniformizerIdele K v))
      (HeckeEigensystem.cNorm v * cw_nval K s₁ (uniformizerIdele K v)) (cw_nval K s₂ (uniformizerIdele K v)) (-Pi.a v)
  let RB : HeightOneSpectrum (𝓞 K) → (cw_Qsq K (uniformizerIdele K v₀) →₀ ℂ) := fun v =>
    cw_rel2 (π (uniformizerIdele K v, uniformizerIdele K v))
      (cw_nval K s₁ (uniformizerIdele K v) * cw_nval K s₂ (uniformizerIdele K v))
      (-((HeckeEigensystem.cNorm v)⁻¹ * Pi.b v))
  have hR : ∀ r ∈ RA '' good ∪ RB '' good, ∀ x : cw_Qsq K (uniformizerIdele K v₀),
      (r.sum fun g c => c * f (x * g)) = 0 := by
    intro r hr x
    obtain ⟨t, rfl⟩ := QuotientGroup.mk_surjective x
    rcases hr with ⟨v, hv, rfl⟩ | ⟨v, hv, rfl⟩
    · have hv' : v ∉ S₁ := hv.2
      dsimp only [RA]
      rw [cw_rel3_sum, mul_one, hπmk, hπmk, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, mul_comm t,
        mul_comm t, hfmk, hfmk, hfmk]
      exact cw_twistA_recA hT s₁ s₂ hv' t
    · have hv' : v ∉ S₁ := hv.2
      dsimp only [RB]
      rw [cw_rel2_sum, mul_one, hπmk, ← QuotientGroup.mk_mul, mul_comm t, hfmk, hfmk]
      exact cw_twistA_recB hT s₁ s₂ hv' t

  have hrowA := ContinuousMap.exists_continuous_monoidHom_forall_sum_eq_zero_of_compactSpace
    (cw_Qsq K (uniformizerIdele K v₀)) f hf0 (RA '' good ∪ RB '' good) hR
  obtain ⟨χ, hχc, hχR⟩ := hrowA
  refine ⟨s₁, s₂, χ, hχc, ?_⟩
  intro v hne hvS
  have hv : v ∈ good := ⟨hne, hvS⟩
  have hχA := hχR (RA v) (Or.inl ⟨v, hv, rfl⟩)
  have hχB := hχR (RB v) (Or.inr ⟨v, hv, rfl⟩)
  dsimp only [RA] at hχA
  dsimp only [RB] at hχB
  rw [cw_rel3_sum, map_one, Units.val_one, mul_one] at hχA
  rw [cw_rel2_sum, map_one, Units.val_one, mul_one] at hχB
  exact ⟨hχA, hχB⟩

private theorem cw_main {ψ : (AdeleRing (𝓞 K) K)ˣ × (AdeleRing (𝓞 K) K)ˣ → ℂ} (hψT : cw_Torus K Pi S₁ ψ)
    (hψ0 : ψ (1, 1) ≠ 0) {v₀ : HeightOneSpectrum (𝓞 K)} (hv₀ : v₀ ∉ S₁) :
    ∃ μ₁ μ₂ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ,
      IsIdeleClassChar (𝓞 K) K μ₁ ∧ IsIdeleClassChar (𝓞 K) K μ₂ ∧ Continuous μ₁ ∧ Continuous μ₂ ∧
      ∀ v : HeightOneSpectrum (𝓞 K), v ≠ v₀ → v ∉ S₁ →
        Pi.a v = ((μ₁ (uniformizerIdele K v) : ℂˣ) : ℂ) + ((μ₂ (uniformizerIdele K v) : ℂˣ) : ℂ) ∧
        Pi.b v = ((μ₁ (uniformizerIdele K v) : ℂˣ) : ℂ) * ((μ₂ (uniformizerIdele K v) : ℂˣ) : ℂ) := by
  have hχE := cw_main_chi hψT hψ0 hv₀
  obtain ⟨s₁, s₂, χ, hχc, hχ⟩ := hχE
  let π : (AdeleRing (𝓞 K) K)ˣ × (AdeleRing (𝓞 K) K)ˣ →* cw_Qsq K (uniformizerIdele K v₀) :=
    QuotientGroup.mk' (cw_Hc K (uniformizerIdele K v₀))
  let μt : (AdeleRing (𝓞 K) K)ˣ × (AdeleRing (𝓞 K) K)ˣ →* ℂˣ :=
    ((cw_normPow K s₁).comp (MonoidHom.fst _ _) * (cw_normPow K s₂).comp (MonoidHom.snd _ _)) * χ.comp π
  have hμtc : Continuous μt :=
    (((cw_continuous_normPow K s₁).comp continuous_fst).mul ((cw_continuous_normPow K s₂).comp continuous_snd)).mul
      (hχc.comp QuotientGroup.continuous_mk)
  have hμt_val : ∀ t₁ t₂ : (AdeleRing (𝓞 K) K)ˣ, ((μt (t₁, t₂) : ℂˣ) : ℂ)
      = cw_nval K s₁ t₁ * cw_nval K s₂ t₂ * ((χ (QuotientGroup.mk (t₁, t₂)) : ℂˣ) : ℂ) := by
    intro t₁ t₂
    show (((cw_normPow K s₁ t₁ * cw_normPow K s₂ t₂) * χ (π (t₁, t₂)) : ℂˣ) : ℂ) = _
    rw [Units.val_mul, Units.val_mul]
    rfl
  let μ₂ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ := μt.comp (MonoidHom.inr _ _)
  let μ₁ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ := cw_normPow K (-1) * μt.comp (MonoidHom.inl _ _)
  have hμ₂c : Continuous μ₂ := hμtc.comp (continuous_const.prodMk continuous_id)
  have hμ₁c : Continuous μ₁ := (cw_continuous_normPow K (-1)).mul (hμtc.comp (continuous_id.prodMk continuous_const))
  have hμ₁_val : ∀ x, ((μ₁ x : ℂˣ) : ℂ) = cw_nval K (-1) x * ((μt (x, 1) : ℂˣ) : ℂ) := by
    intro x
    show (((cw_normPow K (-1) x) * μt (x, 1) : ℂˣ) : ℂ) = _
    rw [Units.val_mul]
    rfl
  have hμ₂_val : ∀ x, ((μ₂ x : ℂˣ) : ℂ) = ((μt (1, x) : ℂˣ) : ℂ) := fun x => rfl

  have hmkγ₁ : ∀ γ : Kˣ, (QuotientGroup.mk (cw_prin K γ, 1) : cw_Qsq K (uniformizerIdele K v₀)) = 1 := fun γ => by
    rw [QuotientGroup.eq_one_iff]
    exact cw_prod_le_Hc _ (Subgroup.mem_prod.mpr ⟨cw_prin_mem_Dsub _ γ, Subgroup.one_mem _⟩)
  have hmkγ₂ : ∀ γ : Kˣ, (QuotientGroup.mk (1, cw_prin K γ) : cw_Qsq K (uniformizerIdele K v₀)) = 1 := fun γ => by
    rw [QuotientGroup.eq_one_iff]
    exact cw_prod_le_Hc _ (Subgroup.mem_prod.mpr ⟨Subgroup.one_mem _, cw_prin_mem_Dsub _ γ⟩)
  have hclass₁ : IsIdeleClassChar (𝓞 K) K μ₁ := by
    intro u
    change μ₁ (cw_prin K u) = 1
    apply Units.val_injective
    rw [hμ₁_val, hμt_val, hmkγ₁, map_one, Units.val_one, cw_nval_prin, cw_nval_prin, cw_nval_one]
    ring
  have hclass₂ : IsIdeleClassChar (𝓞 K) K μ₂ := by
    intro u
    change μ₂ (cw_prin K u) = 1
    apply Units.val_injective
    rw [hμ₂_val, hμt_val, hmkγ₂, map_one, Units.val_one, cw_nval_prin, cw_nval_one]
    ring
  refine ⟨μ₁, μ₂, hclass₁, hclass₂, hμ₁c, hμ₂c, ?_⟩
  intro v hne hvS
  obtain ⟨hχA, hχB⟩ := hχ v hne hvS
  have hq0 : HeckeEigensystem.cNorm v ≠ 0 := HeckeEigensystem.cNorm_ne_zero v
  have hqv : HeckeEigensystem.cNorm v * (HeckeEigensystem.cNorm v)⁻¹ = 1 := mul_inv_cancel₀ hq0
  have hm₁₂ : ((μt (uniformizerIdele K v, uniformizerIdele K v) : ℂˣ) : ℂ)
      = ((μt (uniformizerIdele K v, 1) : ℂˣ) : ℂ) * ((μt (1, uniformizerIdele K v) : ℂˣ) : ℂ) := by
    rw [← Units.val_mul, ← map_mul, Prod.mk_mul_mk, mul_one, one_mul]
  constructor
  · rw [hμ₁_val, hμ₂_val, hμt_val, hμt_val, cw_nval_one, cw_nval_one, cw_nval_neg_one_uniformizerIdele]
    linear_combination (-1 : ℂ) * hχA
  · rw [hμ₁_val, hμ₂_val, mul_assoc, ← hm₁₂, hμt_val, cw_nval_neg_one_uniformizerIdele]
    linear_combination (-HeckeEigensystem.cNorm v) * hχB - Pi.b v * hqv

end C4bWall
p2m_reactivate "P2MW.S_LanglandsTunnell_Converse_eq_zero_or_exists_agreesAwayFromFinite_eisensteinTableOf_of_unipotent_invariant.C4bWall"

theorem solution
    (K : Type) [Field K] [NumberField K] (Pi : HeckeEigensystem K ℂ)
    (S : Finset (HeightOneSpectrum (𝓞 K))) (N : Ideal (𝓞 K))
    (ϕ : AdelicGL2 (𝓞 K) K → ℂ) (hcont : Continuous ϕ)
    (hunip : ∀ (x : AdeleRing (𝓞 K) K) (g : AdelicGL2 (𝓞 K) K), ϕ (unipotentGL2 x * g) = ϕ g)
    (hborel : ∀ γ ∈ borelSubgroup K, ∀ g : AdelicGL2 (𝓞 K) K, ϕ (globalPoints (𝓞 K) K γ * g) = ϕ g)
    (hlevel : ∀ g : AdelicGL2 (𝓞 K) K, ∀ u ∈ levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K,
      ϕ (g * u) = ϕ g)
    (heigen : ∀ v : HeightOneSpectrum (𝓞 K), v ∉ S →
      IsHeckeCosetEigenfunctionAt K (levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K)
        (heckeGen (𝓞 K) K v) v ϕ (Pi.a v))
    (hcentralEigen : ∀ v : HeightOneSpectrum (𝓞 K), v ∉ S → ∀ g : AdelicGL2 (𝓞 K) K,
      ϕ (centralScalar (𝓞 K) K (Matrix.GeneralLinearGroup.det (heckeGen (𝓞 K) K v)) * g)
        = (HeckeEigensystem.cNorm v)⁻¹ * Pi.b v * ϕ g) :
    (∀ g : AdelicGL2 (𝓞 K) K, ϕ g = 0) ∨
      ∃ μ₁ μ₂ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ,
        IsIdeleClassChar (𝓞 K) K μ₁ ∧ IsIdeleClassChar (𝓞 K) K μ₂ ∧
        Continuous μ₁ ∧ Continuous μ₂ ∧
        HeckeEigensystem.AgreesAwayFromFinite Pi
          (LanglandsTunnell.Converse.eisensteinTableOf K Pi.level Pi.level_ne_bot μ₁ μ₂) := by
  classical
  have hrowC :=
    LanglandsTunnell.Converse.eq_zero_or_exists_continuous_torus_recursion_of_unipotent_invariant
      K Pi S N ϕ hcont hunip hborel hlevel heigen hcentralEigen
  rcases hrowC with h0 | hpacket
  · exact Or.inl h0
  · right
    obtain ⟨S₁, ψ, hψc, hψ1, hinv, hrecA, hrecB⟩ := hpacket
    have hT : C4bWall.cw_Torus K Pi S₁ ψ := ⟨hψc, hinv, hrecA, hrecB⟩
    have hplace := C4bWall.cw_exists_place_notMem K S₁
    obtain ⟨v₀, hv₀⟩ := hplace
    have hmain := C4bWall.cw_main hT hψ1 hv₀
    obtain ⟨μ₁, μ₂, h₁, h₂, c₁, c₂, hagree⟩ := hmain
    exact ⟨μ₁, μ₂, h₁, h₂, c₁, c₂, ⟨insert v₀ S₁, fun v hv =>
      hagree v (fun h => hv (by rw [h]; exact Finset.mem_insert_self v₀ S₁))
        (fun h => hv (Finset.mem_insert_of_mem h))⟩⟩

end
p2m_reactivate "P2MW.S_LanglandsTunnell_Converse_eq_zero_or_exists_agreesAwayFromFinite_eisensteinTableOf_of_unipotent_invariant.C4bWall"

#print axioms solution

end S_LanglandsTunnell_Converse_eq_zero_or_exists_agreesAwayFromFinite_eisensteinTableOf_of_unipotent_invariant
end P2MW
export P2MW.S_LanglandsTunnell_Converse_eq_zero_or_exists_agreesAwayFromFinite_eisensteinTableOf_of_unipotent_invariant (solution)
