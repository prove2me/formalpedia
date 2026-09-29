-- Prove2me | solution 1 for LanglandsTunnell.CubicInduction.exists_entire_eulerTwist_induced_of_not_exists_eq_pow_inertiaDeg
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.353894+00:00
-- url     : https://prove2.me/submissions/dbb881c2-6c14-59d6-8d38-81658f38581b

import Definitions.Def_LanglandsTunnell_CubicInduction_Structure
import Definitions.Def_LanglandsTunnell_CubicLambda
import Definitions.Def_M4aHerbrand_GenuineDescent
import Definitions.Def_M4aHerbrand_AdeleBaseChange
import Definitions.Def_NumberField_NormPowChar
import Definitions.Def_NumberField_AdelicHaar
import Theorems.Thm_NumberField_TateGlobal_exists_differentiable_eq_partialEulerProduct_of_exists_mem_normOneIdeles_ne_one
import Theorems.Thm_NumberField_TateGlobal_exists_eq_normPowChar_of_forall_mem_normOneIdeles
import Theorems.Thm_LanglandsTunnell_RankinSelberg_hasProd_inv_eval_inducedEulerPoly_of_hasProd
import Theorems.Thm_NumberField_multipliable_differentiableOn_tprod_ne_zero_eulerProduct_of_norm_le_one
import Theorems.Thm_M4aHerbrand_exists_idelicNorm_uniformizerIdele_eq_pow_inertiaDeg_mul_localUnit
import Theorems.Thm_M4aHerbrand_GenuineDescent_adelicNorm_genuineBaseChange_algebraMap
import Theorems.Thm_M4aHerbrand_GenuineDescent_continuous_adelicNorm_genuineBaseChange
import Theorems.Thm_NumberField_TateGlobal_exists_finset_forall_isUnramifiedCharAt_of_continuous
import Theorems.Thm_NumberField_TateGlobal_ite_isUnramifiedCharAt_normPowChar_apply_uniformizerIdele_eq_absNorm_cpow_neg
import Theorems.Thm_NumberField_AdeleRing_distribHaarChar_algebraMap
import Theorems.Thm_NumberField_TateGlobal_continuous_ideleNorm
import Theorems.Thm_LanglandsTunnell_RankinSelberg_eval_inducedEulerPoly_eq_of_finrank_le_three
import Theorems.Thm_LanglandsTunnell_CubicInduction_finite_setOf_isBadPlace_of_continuous
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LanglandsTunnell_CubicInduction_exists_entire_eulerTwist_induced_of_not_exists_eq_pow_inertiaDeg
p2m_attr_erase "instance" "instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instCountableOfNumberField_definitions instHenselianLocalRingOfCompactSpaceOfIsNoetherianRing NumberField.instHenselianLocalRingAdicCompletionIntegers instIsAdicCompleteMaximalIdealOfCompactSpace NumberField.instIsAdicCompleteMaximalIdealAdicCompletionIntegers"
p2m_attr_erase "simp" "LanglandsTunnell.ArchPlace.complexTestFun_zero_apply LanglandsTunnell.ArchPlace.norm_anglePhase LanglandsTunnell.ArchPlace.realTestFun_zero_apply NumberField.AdeleRing.val_finiteUnitsComponent IsDedekindDomain.FiniteAdeleRing.val_unitsComponent NumberField.AdeleRing.val_finitePartUnits NumberField.AdeleRing.val_infiniteUnitsComponent AutomorphicForm.SiegelCoordinates.upperUnit_apply_zero_zero AutomorphicForm.SiegelCoordinates.upperUnit_apply_one_zero AutomorphicForm.SiegelCoordinates.upperUnit_apply_one_one AutomorphicForm.SiegelCoordinates.upperUnit_apply_zero_one"
set_option Elab.async false

set_option autoImplicit false

open IsDedekindDomain NumberField NumberField.TateGlobal AutomorphicForm LanglandsTunnell.Converse LanglandsTunnell.RankinSelberg LanglandsTunnell.CubicLambda

section

open LanglandsTunnell.RankinSelberg

variable (F : Type) [Field F] [NumberField F]

private theorem asIdeal_mem_primesOver_of_mem_primeFibre (p : HeightOneSpectrum (𝓞 ℚ))
    {𝔓 : HeightOneSpectrum (𝓞 F)} (h : 𝔓 ∈ primeFibre ℚ F p) :
    𝔓.asIdeal ∈ p.asIdeal.primesOver (𝓞 F) := by
  rw [mem_primeFibre] at h
  refine ⟨𝔓.isPrime, ⟨?_⟩⟩
  rw [← h]
  rfl

private theorem image_asIdeal_primeFibre (p : HeightOneSpectrum (𝓞 ℚ)) :
    HeightOneSpectrum.asIdeal '' primeFibre ℚ F p = p.asIdeal.primesOver (𝓞 F) := by
  ext Q
  constructor
  · rintro ⟨𝔓, h𝔓, rfl⟩
    exact asIdeal_mem_primesOver_of_mem_primeFibre F p h𝔓
  · intro hQ
    haveI : Q.IsPrime := hQ.1
    haveI : Q.LiesOver p.asIdeal := hQ.2
    refine ⟨⟨Q, hQ.1, Ideal.ne_bot_of_mem_primesOver p.ne_bot hQ⟩, ?_, rfl⟩
    rw [mem_primeFibre]
    apply HeightOneSpectrum.ext
    exact (Ideal.over_def Q p.asIdeal).symm

private theorem primeFibre_finite (p : HeightOneSpectrum (𝓞 ℚ)) :
    (primeFibre ℚ F p).Finite := by
  have hfin : (p.asIdeal.primesOver (𝓞 F)).Finite := IsDedekindDomain.primesOver_finite p.asIdeal (𝓞 F)
  rw [← image_asIdeal_primeFibre F p] at hfin
  exact hfin.of_finite_image HeightOneSpectrum.asIdeal_injective.injOn

private theorem finsum_fibre_ramificationIdx_mul_inertiaDeg (p : HeightOneSpectrum (𝓞 ℚ)) :
    ∑ᶠ 𝔓 ∈ primeFibre ℚ F p, p.asIdeal.ramificationIdx' 𝔓.asIdeal * p.asIdeal.inertiaDeg' 𝔓.asIdeal =
      Module.finrank ℚ F := by
  calc ∑ᶠ 𝔓 ∈ primeFibre ℚ F p, p.asIdeal.ramificationIdx' 𝔓.asIdeal * p.asIdeal.inertiaDeg' 𝔓.asIdeal
      = ∑ᶠ Q ∈ HeightOneSpectrum.asIdeal '' primeFibre ℚ F p,
          p.asIdeal.ramificationIdx' Q * p.asIdeal.inertiaDeg' Q :=
        (finsum_mem_image (f := fun Q : Ideal (𝓞 F) => p.asIdeal.ramificationIdx' Q * p.asIdeal.inertiaDeg' Q)
          HeightOneSpectrum.asIdeal_injective.injOn).symm
    _ = ∑ᶠ Q ∈ p.asIdeal.primesOver (𝓞 F), p.asIdeal.ramificationIdx' Q * p.asIdeal.inertiaDeg' Q := by
        rw [image_asIdeal_primeFibre]
    _ = ∑ Q ∈ IsDedekindDomain.primesOverFinset p.asIdeal (𝓞 F),
          p.asIdeal.ramificationIdx' Q * p.asIdeal.inertiaDeg' Q := by
        rw [← IsDedekindDomain.coe_primesOverFinset p.ne_bot (𝓞 F), finsum_mem_coe_finset]
    _ = Module.finrank ℚ F := Ideal.sum_ramification_inertia (𝓞 F) ℚ F p.ne_bot

end

private theorem ringHom_ringOfIntegers_rat_ext {S : Type*} [Ring S] (f g : 𝓞 ℚ →+* S) : f = g := by
  have h : f.comp (Rat.ringOfIntegersEquiv.symm : ℤ →+* 𝓞 ℚ) = g.comp (Rat.ringOfIntegersEquiv.symm : ℤ →+* 𝓞 ℚ) :=
    Subsingleton.elim _ _
  ext x
  have hx : x = (Rat.ringOfIntegersEquiv.symm : ℤ →+* 𝓞 ℚ) (Rat.ringOfIntegersEquiv x) :=
    (Rat.ringOfIntegersEquiv.symm_apply_apply x).symm
  rw [hx]
  exact RingHom.congr_fun h _

private theorem algebra_ringOfIntegers_rat_eq (X : Type) [Field X] [NumberField X] (i : Algebra (𝓞 ℚ) (𝓞 X)) :
    i = NumberField.inst_ringOfIntegersAlgebra ℚ X :=
  Algebra.algebra_ext i (NumberField.inst_ringOfIntegersAlgebra ℚ X) fun r =>
    RingHom.congr_fun
      (ringHom_ringOfIntegers_rat_ext (@algebraMap (𝓞 ℚ) (𝓞 X) _ _ i)
        (@algebraMap (𝓞 ℚ) (𝓞 X) _ _ (NumberField.inst_ringOfIntegersAlgebra ℚ X))) r

namespace TwistedInducedContinuation

open Polynomial LanglandsTunnell.CubicInduction M4aHerbrand.GenuineDescent

private theorem ideleNorm_map_algebraMap (u : ℚˣ) :
    ideleNorm ℚ (Units.map (algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ)) u) = 1 := by
  letI : MeasurableSpace (AdeleRing (𝓞 ℚ) ℚ) := NumberField.AdelicHaar.adeleBorel (𝓞 ℚ) ℚ
  haveI : BorelSpace (AdeleRing (𝓞 ℚ) ℚ) := NumberField.AdelicHaar.borelSpace_adeleBorel (𝓞 ℚ) ℚ
  have h := NumberField.AdeleRing.distribHaarChar_algebraMap ℚ u
  simp only [RingHom.toMonoidHom_eq_coe] at h
  rw [ideleNorm, h]
  simp

private theorem continuous_normPowChar (t : ℝ) : Continuous (normPowChar ℚ t) := by
  have hval : Continuous fun x : (AdeleRing (𝓞 ℚ) ℚ)ˣ => ((ideleNorm ℚ x : ℝ) : ℂ) ^ (Complex.I * t) :=
    Continuous.cpow (Complex.continuous_ofReal.comp (continuous_ideleNorm ℚ)) continuous_const
      fun x => Complex.ofReal_mem_slitPlane.2 (ideleNorm_pos x)
  refine Units.continuous_iff.2 ⟨hval, ?_⟩
  simp only [Units.val_inv_eq_inv_val, coe_normPowChar_apply]
  exact hval.inv₀ fun x => ofReal_ideleNorm_cpow_ne_zero ℚ x _

private theorem isUnramifiedCharAt_normPowChar (F : Type) [Field F] [NumberField F] (t : ℝ)
    (v : HeightOneSpectrum (𝓞 F)) : IsUnramifiedCharAt (normPowChar F t) v := by
  by_contra h
  have e := ite_isUnramifiedCharAt_normPowChar_apply_uniformizerIdele_eq_absNorm_cpow_neg F t v
  rw [if_neg h] at e
  have hN : ((Ideal.absNorm v.asIdeal : ℕ) : ℂ) = 0 := ((Complex.cpow_eq_zero_iff _ _).mp e.symm).1
  exact v.ne_bot (Ideal.absNorm_eq_zero_iff.mp (by exact_mod_cast hN))

private theorem coe_normPowChar_uniformizerIdele (F : Type) [Field F] [NumberField F] (t : ℝ)
    (v : HeightOneSpectrum (𝓞 F)) :
    ((normPowChar F t (uniformizerIdele F v) : ℂˣ) : ℂ) =
      ((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ^ (-(Complex.I * t)) := by
  have e := ite_isUnramifiedCharAt_normPowChar_apply_uniformizerIdele_eq_absNorm_cpow_neg F t v
  rwa [if_pos (isUnramifiedCharAt_normPowChar F t v)] at e

private theorem isAdmissibleTwist_inv_mul_normPowChar (σ : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ)
    (hσ : IsAdmissibleTwist ℚ σ) (t : ℝ) : IsAdmissibleTwist ℚ (σ⁻¹ * normPowChar ℚ t) := by
  obtain ⟨hσ1, hσc, hσu⟩ := hσ
  refine ⟨fun u => ?_, ?_, fun x => ?_⟩
  · show (σ _)⁻¹ * normPowChar ℚ t _ = 1
    rw [hσ1 u, inv_one, one_mul]
    exact normPowChar_eq_one_of_ideleNorm_eq_one t (ideleNorm_map_algebraMap u)
  · show Continuous fun x => (σ x)⁻¹ * normPowChar ℚ t x
    exact hσc.inv.mul (continuous_normPowChar t)
  · show ‖(((σ x)⁻¹ * normPowChar ℚ t x : ℂˣ) : ℂ)‖ = 1
    rw [Units.val_mul, norm_mul, Units.val_inv_eq_inv_val, norm_inv, hσu x, inv_one, one_mul]
    exact norm_coe_normPowChar_apply t x

private theorem isUnramifiedCharAt_of_inv_mul_normPowChar (σ : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ) (t : ℝ)
    (p : HeightOneSpectrum (𝓞 ℚ)) (h : IsUnramifiedCharAt (σ⁻¹ * normPowChar ℚ t) p) :
    IsUnramifiedCharAt σ p := by
  intro u hu hu'
  have h1 := h u hu hu'
  have h2 := isUnramifiedCharAt_normPowChar ℚ t p u hu hu'
  simp only [localChar, MonoidHom.comp_apply] at h1 h2 ⊢
  change (σ _)⁻¹ * normPowChar ℚ t _ = 1 at h1
  rwa [h2, mul_one, inv_eq_one] at h1

section

variable (K : Type) [Field K] [NumberField K]

private theorem isIdeleClassChar_comp_idelicNorm (η : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ) (hη : IsIdeleClassChar (𝓞 ℚ) ℚ η) :
    IsIdeleClassChar (𝓞 K) K (η.comp (genuineBaseChange ℚ K).idelicNorm) := by
  intro u
  have hnorm :
      (genuineBaseChange ℚ K).idelicNorm (Units.map (algebraMap K (AdeleRing (𝓞 K) K)) u) =
        Units.map (algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ)) (Units.map (Algebra.norm ℚ (S := K)) u) := by
    apply Units.ext
    have h__af := (adelicNorm_genuineBaseChange_algebraMap ℚ K (u : K))
    simp at h__af ⊢
    exact h__af
  simpa [MonoidHom.comp_apply, hnorm] using hη (Units.map (Algebra.norm ℚ (S := K)) u)

private theorem continuous_comp_idelicNorm (η : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ) (hcη : Continuous η) :
    Continuous (η.comp (genuineBaseChange ℚ K).idelicNorm) := by
  refine hcη.comp ?_
  have hN : Continuous (genuineBaseChange ℚ K).adelicNorm := continuous_adelicNorm_genuineBaseChange ℚ K
  exact Units.continuous_iff.2 ⟨hN.comp Units.continuous_val, hN.comp Units.continuous_coe_inv⟩

private theorem isAdmissibleTwist_mul_comp_idelicNorm (μ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ) (hμ : IsAdmissibleTwist K μ)
    (σ : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ) (hσ : IsAdmissibleTwist ℚ σ) :
    IsAdmissibleTwist K (μ * σ.comp (genuineBaseChange ℚ K).idelicNorm) := by
  obtain ⟨hμ1, hμc, hμu⟩ := hμ
  obtain ⟨hσ1, hσc, hσu⟩ := hσ
  refine ⟨fun u => ?_, ?_, fun x => ?_⟩
  · show μ _ * (σ.comp (genuineBaseChange ℚ K).idelicNorm) _ = 1
    rw [hμ1 u, isIdeleClassChar_comp_idelicNorm K σ hσ1 u, one_mul]
  · show Continuous fun x => μ x * (σ.comp (genuineBaseChange ℚ K).idelicNorm) x
    exact hμc.mul (continuous_comp_idelicNorm K σ hσc)
  · show ‖((μ x * σ ((genuineBaseChange ℚ K).idelicNorm x) : ℂˣ) : ℂ)‖ = 1
    rw [Units.val_mul, norm_mul, hμu x, hσu _, one_mul]

private theorem coe_mul_comp_idelicNorm_uniformizerIdele (μ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ)
    (σ : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ) (𝔓 : HeightOneSpectrum (𝓞 K))
    (hσ𝔓 : IsUnramifiedCharAt σ (𝔓.under (𝓞 ℚ))) :
    (((μ * σ.comp (genuineBaseChange ℚ K).idelicNorm) (uniformizerIdele K 𝔓) : ℂˣ) : ℂ) =
      ((μ (uniformizerIdele K 𝔓) : ℂˣ) : ℂ) *
        ((σ (uniformizerIdele ℚ (𝔓.under (𝓞 ℚ))) : ℂˣ) : ℂ) ^ (𝔓.under (𝓞 ℚ)).asIdeal.inertiaDeg' 𝔓.asIdeal := by
  obtain ⟨t, ht, hN⟩ := M4aHerbrand.exists_idelicNorm_uniformizerIdele_eq_pow_inertiaDeg_mul_localUnit ℚ K 𝔓
  have ht_int : ((t : (𝔓.under (𝓞 ℚ)).adicCompletion ℚ)) ∈ (𝔓.under (𝓞 ℚ)).adicCompletionIntegers ℚ := by
    rw [HeightOneSpectrum.mem_adicCompletionIntegers, ht]
  have ht_inv_int : (((t⁻¹ : ((𝔓.under (𝓞 ℚ)).adicCompletion ℚ)ˣ)) : (𝔓.under (𝓞 ℚ)).adicCompletion ℚ)
      ∈ (𝔓.under (𝓞 ℚ)).adicCompletionIntegers ℚ := by
    rw [HeightOneSpectrum.mem_adicCompletionIntegers, Units.val_inv_eq_inv_val, map_inv₀, ht, inv_one]
  have hunit :
      σ (Units.map (NumberField.AdelicLevel.finIncl (𝓞 ℚ) ℚ)
        (NumberField.AdelicLevel.localUnit (𝓞 ℚ) ℚ (𝔓.under (𝓞 ℚ)) t)) = 1 :=
    hσ𝔓 t ht_int ht_inv_int
  show ((μ (uniformizerIdele K 𝔓) * σ ((genuineBaseChange ℚ K).idelicNorm (uniformizerIdele K 𝔓)) : ℂˣ) : ℂ) = _
  rw [hN, map_mul, map_pow, hunit, mul_one, Units.val_mul, Units.val_pow_eq_pow_val]

private noncomputable def cutCoeff (ν : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ) (T' : Finset (HeightOneSpectrum (𝓞 K)))
    (𝔓 : HeightOneSpectrum (𝓞 K)) : ℂ := by
  classical
  exact if 𝔓 ∈ T' then 0 else ((ν (uniformizerIdele K 𝔓) : ℂˣ) : ℂ)

private theorem cutCoeff_of_mem (ν : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ) {T' : Finset (HeightOneSpectrum (𝓞 K))}
    {𝔓 : HeightOneSpectrum (𝓞 K)} (h : 𝔓 ∈ T') : cutCoeff K ν T' 𝔓 = 0 := by
  rw [cutCoeff, if_pos h]

private theorem cutCoeff_of_notMem (ν : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ) {T' : Finset (HeightOneSpectrum (𝓞 K))}
    {𝔓 : HeightOneSpectrum (𝓞 K)} (h : 𝔓 ∉ T') : cutCoeff K ν T' 𝔓 = ((ν (uniformizerIdele K 𝔓) : ℂˣ) : ℂ) := by
  rw [cutCoeff, if_neg h]

private theorem norm_cutCoeff_le_one (ν : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ) (hνu : IsUnitaryChar (𝓞 K) K ν)
    (T' : Finset (HeightOneSpectrum (𝓞 K))) (𝔓 : HeightOneSpectrum (𝓞 K)) : ‖cutCoeff K ν T' 𝔓‖ ≤ 1 := by
  by_cases h : 𝔓 ∈ T'
  · rw [cutCoeff_of_mem K ν h, norm_zero]
    exact zero_le_one
  · rw [cutCoeff_of_notMem K ν h]
    exact (hνu _).le

private theorem inducedEulerPoly_eq_one (c : HeightOneSpectrum (𝓞 K) → ℂ) (p : HeightOneSpectrum (𝓞 ℚ))
    (h : ∀ 𝔓 ∈ primeFibre ℚ K p, c 𝔓 = 0) : inducedEulerPoly ℚ c p = 1 := by
  rw [inducedEulerPoly]
  refine finprod_mem_of_eqOn_one fun 𝔓 h𝔓 => ?_
  simp [inducedFactor, h 𝔓 h𝔓]

private theorem inducedEulerPoly_eq_comp (c d : HeightOneSpectrum (𝓞 K) → ℂ) (s : ℂ) (p : HeightOneSpectrum (𝓞 ℚ))
    (h : ∀ 𝔓 ∈ primeFibre ℚ K p, c 𝔓 = d 𝔓 * s ^ (𝔓.under (𝓞 ℚ)).asIdeal.inertiaDeg' 𝔓.asIdeal) :
    inducedEulerPoly ℚ c p = (inducedEulerPoly ℚ d p).comp (C s * X) := by
  simp only [inducedEulerPoly]
  rw [finprod_mem_eq_finite_toFinset_prod _ (primeFibre_finite K p),
    finprod_mem_eq_finite_toFinset_prod _ (primeFibre_finite K p), Polynomial.prod_comp]
  refine Finset.prod_congr rfl fun 𝔓 h𝔓 => ?_
  rw [Set.Finite.mem_toFinset] at h𝔓
  simp only [inducedFactor, h 𝔓 h𝔓, sub_comp, C_comp, mul_comp, pow_comp, X_comp, C_mul, C_pow, mul_pow]
  ring

private theorem exists_differentiable_hasProd (ν : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ) (hν : IsAdmissibleTwist K ν)
    (hν1 : ∃ x ∈ normOneIdeles K, ν x ≠ 1) (T' : Finset (HeightOneSpectrum (𝓞 K)))
    (hT' : ∀ 𝔓 ∉ T', IsUnramifiedCharAt ν 𝔓) :
    ∃ L : ℂ → ℂ, Differentiable ℂ L ∧ ∀ s : ℂ, 1 < s.re →
      HasProd (fun 𝔓 : HeightOneSpectrum (𝓞 K) =>
        (1 - cutCoeff K ν T' 𝔓 * ((Ideal.absNorm 𝔓.asIdeal : ℕ) : ℂ) ^ (-s))⁻¹) (L s) := by
  obtain ⟨hνi, hνc, hνu⟩ := hν
  obtain ⟨L, hL, hLs⟩ :=
    exists_differentiable_eq_partialEulerProduct_of_exists_mem_normOneIdeles_ne_one K ν hνi hνc hνu hν1 T'
  refine ⟨L, hL, fun s hs => ?_⟩
  have hmult := (NumberField.multipliable_differentiableOn_tprod_ne_zero_eulerProduct_of_norm_le_one K T'
    (fun 𝔓 => cutCoeff K ν T' 𝔓.1) fun 𝔓 => norm_cutCoeff_le_one K ν hνu T' 𝔓.1).1 s hs
  have h1 : HasProd (fun 𝔓 : {𝔓 : HeightOneSpectrum (𝓞 K) // 𝔓 ∉ T'} =>
      (1 - cutCoeff K ν T' 𝔓.1 * ((Ideal.absNorm 𝔓.1.asIdeal : ℕ) : ℂ) ^ (-s))⁻¹) (L s) := by
    have hprod : L s = ∏' 𝔓 : {𝔓 : HeightOneSpectrum (𝓞 K) // 𝔓 ∉ T'},
        (1 - cutCoeff K ν T' 𝔓.1 * ((Ideal.absNorm 𝔓.1.asIdeal : ℕ) : ℂ) ^ (-s))⁻¹ := by
      rw [hLs s hs]
      refine tprod_congr fun 𝔓 => ?_
      rw [if_pos (hT' 𝔓.1 𝔓.2), cutCoeff_of_notMem K ν 𝔓.2]
    rw [hprod]
    exact hmult.hasProd
  have h2 := (hasProd_subtype_iff_mulIndicator (s := {𝔓 : HeightOneSpectrum (𝓞 K) | 𝔓 ∉ T'})
    (f := fun 𝔓 : HeightOneSpectrum (𝓞 K) =>
      (1 - cutCoeff K ν T' 𝔓 * ((Ideal.absNorm 𝔓.asIdeal : ℕ) : ℂ) ^ (-s))⁻¹)).1 h1
  convert h2 using 1
  funext 𝔓
  by_cases h : 𝔓 ∈ T'
  · simp [h, cutCoeff_of_mem K ν h]
  · simp [h]

end

end TwistedInducedContinuation

open TwistedInducedContinuation LanglandsTunnell.CubicInduction M4aHerbrand.GenuineDescent Polynomial in
theorem solution
    (K : Type) [Field K] [NumberField K] [Algebra (𝓞 ℚ) (𝓞 K)] [Algebra.IsIntegral (𝓞 ℚ) (𝓞 K)]
    (hdeg : Module.finrank ℚ K = 3)
    (μ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ) (hμ : IsAdmissibleTwist K μ)
    (hns : ¬ (∃ η : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ, IsAdmissibleTwist ℚ η ∧
      ∀ 𝔓 : HeightOneSpectrum (𝓞 K), IsUnramifiedCharAt μ 𝔓 →
        IsUnramifiedCharAt η (𝔓.under (𝓞 ℚ)) →
        ((μ (uniformizerIdele K 𝔓) : ℂˣ) : ℂ) =
          ((η (uniformizerIdele ℚ (𝔓.under (𝓞 ℚ))) : ℂˣ) : ℂ) ^
            (𝔓.under (𝓞 ℚ)).asIdeal.inertiaDeg' 𝔓.asIdeal))
    (ω : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ)
    (hω : ∀ p : HeightOneSpectrum (𝓞 ℚ), ¬ IsBadPlace K μ p → eulerCoeff ℚ ω p = inducedE3 ℚ (inducedCoeff K μ) p)
    (S : Finset (HeightOneSpectrum (𝓞 ℚ))) :
    ∀ σ : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ, IsAdmissibleTwist ℚ σ →
      ∃ T : Finset (HeightOneSpectrum (𝓞 ℚ)), S ⊆ T ∧
        ∃ E : ℂ → ℂ, Differentiable ℂ E ∧
          ∀ s : ℂ, 1 < s.re →
            E s = ∏' p : {p : HeightOneSpectrum (𝓞 ℚ) // p ∉ T},
              (1 - inducedE1 ℚ (inducedCoeff K μ) p.1 *
                (eulerCoeff ℚ σ p.1 * (((Ideal.absNorm p.1.asIdeal : ℕ) : ℂ) ^ (-s)))
                + inducedE2 ℚ (inducedCoeff K μ) p.1 *
                (eulerCoeff ℚ σ p.1 * (((Ideal.absNorm p.1.asIdeal : ℕ) : ℂ) ^ (-s))) ^ 2
                - eulerCoeff ℚ ω p.1 *
                    (eulerCoeff ℚ σ p.1 * (((Ideal.absNorm p.1.asIdeal : ℕ) : ℂ) ^ (-s))) ^ 3)⁻¹ := by
  classical
  obtain rfl := algebra_ringOfIntegers_rat_eq K ‹Algebra (𝓞 ℚ) (𝓞 K)›
  obtain ⟨-, hμc, -⟩ := id hμ
  have hfinB := finite_setOf_isBadPlace_of_continuous K μ hμc
  have hB : ∀ p : HeightOneSpectrum (𝓞 ℚ), IsBadPlace K μ p → p ∈ hfinB.toFinset := fun p hp =>
    hfinB.mem_toFinset.2 hp
  intro σ hσ
  obtain ⟨-, hσc, -⟩ := id hσ

  have hν : IsAdmissibleTwist K (μ * σ.comp (genuineBaseChange ℚ K).idelicNorm) :=
    isAdmissibleTwist_mul_comp_idelicNorm K μ hμ σ hσ
  obtain ⟨-, hνc, hνu⟩ := id hν

  have hν1 : ∃ x ∈ normOneIdeles K, (μ * σ.comp (genuineBaseChange ℚ K).idelicNorm) x ≠ 1 := by
    by_contra hcon
    have hall : ∀ x ∈ normOneIdeles K, (μ * σ.comp (genuineBaseChange ℚ K).idelicNorm) x = 1 :=
      fun x hx => not_not.mp fun h => hcon ⟨x, hx, h⟩
    obtain ⟨t, ht⟩ := exists_eq_normPowChar_of_forall_mem_normOneIdeles K _ hνc hνu hall
    refine hns ⟨σ⁻¹ * normPowChar ℚ t, isAdmissibleTwist_inv_mul_normPowChar σ hσ t, fun 𝔓 _ hη𝔓 => ?_⟩
    have hσ𝔓 : IsUnramifiedCharAt σ (𝔓.under (𝓞 ℚ)) := isUnramifiedCharAt_of_inv_mul_normPowChar σ t _ hη𝔓
    have hA := coe_mul_comp_idelicNorm_uniformizerIdele K μ σ 𝔓 hσ𝔓
    rw [ht, coe_normPowChar_uniformizerIdele K t 𝔓] at hA
    haveI : 𝔓.asIdeal.LiesOver (𝔓.under (𝓞 ℚ)).asIdeal := ⟨rfl⟩
    have habs : ((Ideal.absNorm 𝔓.asIdeal : ℕ) : ℂ) =
        ((Ideal.absNorm (𝔓.under (𝓞 ℚ)).asIdeal : ℕ) : ℂ) ^ (𝔓.under (𝓞 ℚ)).asIdeal.inertiaDeg' 𝔓.asIdeal := by
      rw [Ideal.absNorm_eq_pow_inertiaDeg_of_liesOver 𝔓.asIdeal (𝔓.under (𝓞 ℚ)).asIdeal (𝔓.under (𝓞 ℚ)).isPrime
        (𝔓.under (𝓞 ℚ)).ne_bot, Nat.cast_pow]
    have hB' : ((((σ⁻¹ * normPowChar ℚ t) (uniformizerIdele ℚ (𝔓.under (𝓞 ℚ)))) : ℂˣ) : ℂ) ^
        (𝔓.under (𝓞 ℚ)).asIdeal.inertiaDeg' 𝔓.asIdeal =
        (((σ (uniformizerIdele ℚ (𝔓.under (𝓞 ℚ))) : ℂˣ) : ℂ) ^ (𝔓.under (𝓞 ℚ)).asIdeal.inertiaDeg' 𝔓.asIdeal)⁻¹ *
          ((Ideal.absNorm 𝔓.asIdeal : ℕ) : ℂ) ^ (-(Complex.I * t)) := by
      show ((((σ _)⁻¹ * normPowChar ℚ t _ : ℂˣ) : ℂ)) ^ _ = _
      rw [Units.val_mul, Units.val_inv_eq_inv_val, coe_normPowChar_uniformizerIdele ℚ t, mul_pow, inv_pow, habs,
        ← Complex.natCast_cpow_natCast_mul, Complex.cpow_nat_mul]
    rw [hB', hA, mul_comm (((μ (uniformizerIdele K 𝔓) : ℂˣ) : ℂ)),
      inv_mul_cancel_left₀ (pow_ne_zero _ (Units.ne_zero _))]

  obtain ⟨Sσ, hSσ⟩ := exists_finset_forall_isUnramifiedCharAt_of_continuous ℚ σ hσc
  obtain ⟨Sμ, hSμ⟩ := exists_finset_forall_isUnramifiedCharAt_of_continuous K μ hμc
  obtain ⟨Sν, hSν⟩ := exists_finset_forall_isUnramifiedCharAt_of_continuous K _ hνc
  set T : Finset (HeightOneSpectrum (𝓞 ℚ)) :=
    S ∪ hfinB.toFinset ∪ Sσ ∪ (Sμ ∪ Sν).image (fun 𝔓 => 𝔓.under (𝓞 ℚ)) with hT
  have hgood : ∀ p ∉ T, ¬ IsBadPlace K μ p ∧ IsUnramifiedCharAt σ p ∧
      ∀ 𝔓 : HeightOneSpectrum (𝓞 K), 𝔓.under (𝓞 ℚ) = p → IsUnramifiedCharAt μ 𝔓 ∧
        IsUnramifiedCharAt (μ * σ.comp (genuineBaseChange ℚ K).idelicNorm) 𝔓 := by
    intro p hp
    refine ⟨fun hbad => hp ?_, hSσ p fun hpσ => hp ?_, fun 𝔓 h𝔓 => ?_⟩
    · rw [hT]
      exact Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (hB p hbad)))
    · rw [hT]
      exact Finset.mem_union_left _ (Finset.mem_union_right _ hpσ)
    have h𝔓' : 𝔓 ∉ Sμ ∪ Sν := fun hmem => hp (by
      rw [hT]
      refine Finset.mem_union_right _ ?_
      rw [Finset.mem_image]
      exact ⟨𝔓, hmem, h𝔓⟩)
    rw [Finset.mem_union, not_or] at h𝔓'
    exact ⟨hSμ 𝔓 h𝔓'.1, hSν 𝔓 h𝔓'.2⟩
  refine ⟨T, ?_, ?_⟩
  · rw [hT]
    exact Finset.subset_union_left.trans (Finset.subset_union_left.trans Finset.subset_union_left)

  have hfin : {𝔓 : HeightOneSpectrum (𝓞 K) | 𝔓.under (𝓞 ℚ) ∈ T}.Finite :=
    HeightOneSpectrum.preimage_comap_finite (𝓞 ℚ) ℚ K (𝓞 K) (↑T) T.finite_toSet
  set T' : Finset (HeightOneSpectrum (𝓞 K)) := hfin.toFinset with hT'
  have hmemT' : ∀ 𝔓 : HeightOneSpectrum (𝓞 K), 𝔓 ∈ T' ↔ 𝔓.under (𝓞 ℚ) ∈ T := fun 𝔓 => by
    rw [hT', Set.Finite.mem_toFinset, Set.mem_setOf_eq]
  have hT'unr : ∀ 𝔓 ∉ T', IsUnramifiedCharAt (μ * σ.comp (genuineBaseChange ℚ K).idelicNorm) 𝔓 := fun 𝔓 h𝔓 =>
    ((hgood (𝔓.under (𝓞 ℚ)) fun h => h𝔓 ((hmemT' 𝔓).2 h)).2.2 𝔓 rfl).2

  obtain ⟨L, hL, hLs⟩ := exists_differentiable_hasProd K _ hν hν1 T' hT'unr
  refine ⟨L, hL, fun s hs => ?_⟩
  have hG := hasProd_inv_eval_inducedEulerPoly_of_hasProd ℚ K (cutCoeff K _ T') s (L s) (hLs s hs)
  have hG' : HasProd ({p : HeightOneSpectrum (𝓞 ℚ) | p ∉ T}.mulIndicator fun p : HeightOneSpectrum (𝓞 ℚ) =>
      ((inducedEulerPoly ℚ (cutCoeff K (μ * σ.comp (genuineBaseChange ℚ K).idelicNorm) T') p).eval
        (((Ideal.absNorm p.asIdeal : ℕ) : ℂ) ^ (-s)))⁻¹) (L s) := by
    convert hG using 1
    funext p
    by_cases hp : p ∈ T
    · have hone : inducedEulerPoly ℚ (cutCoeff K (μ * σ.comp (genuineBaseChange ℚ K).idelicNorm) T') p = 1 := by
        refine inducedEulerPoly_eq_one K _ p fun 𝔓 h𝔓 => cutCoeff_of_mem K _ ((hmemT' 𝔓).2 ?_)
        rw [mem_primeFibre] at h𝔓
        rw [h𝔓]
        exact hp
      simp [hp, hone]
    · simp [hp]
  have hsub := (hasProd_subtype_iff_mulIndicator (s := {p : HeightOneSpectrum (𝓞 ℚ) | p ∉ T})).2 hG'
  refine hsub.tprod_eq.symm.trans (tprod_congr fun p => ?_)
  obtain ⟨hpbad, hpσ, hpfib⟩ := hgood p.1 p.2
  have hcoef : ∀ 𝔓 ∈ primeFibre ℚ K p.1,
      cutCoeff K (μ * σ.comp (genuineBaseChange ℚ K).idelicNorm) T' 𝔓 =
        inducedCoeff K μ 𝔓 * (eulerCoeff ℚ σ p.1) ^ (𝔓.under (𝓞 ℚ)).asIdeal.inertiaDeg' 𝔓.asIdeal := by
    intro 𝔓 h𝔓
    rw [mem_primeFibre] at h𝔓
    obtain ⟨hμ𝔓, -⟩ := hpfib 𝔓 h𝔓
    have h𝔓T' : 𝔓 ∉ T' := fun h => p.2 (by
      have h' := (hmemT' 𝔓).1 h
      rwa [h𝔓] at h')
    have hσ𝔓 : IsUnramifiedCharAt σ (𝔓.under (𝓞 ℚ)) := by
      rw [h𝔓]
      exact hpσ
    rw [cutCoeff_of_notMem K _ h𝔓T', inducedCoeff, if_pos hμ𝔓, eulerCoeff, if_pos hpσ, ← h𝔓]
    exact coe_mul_comp_idelicNorm_uniformizerIdele K μ σ 𝔓 hσ𝔓
  show ((inducedEulerPoly ℚ _ p.1).eval _)⁻¹ = _
  rw [inducedEulerPoly_eq_comp K _ (inducedCoeff K μ) (eulerCoeff ℚ σ p.1) p.1 hcoef, eval_comp, eval_mul, eval_C,
    eval_X, eval_inducedEulerPoly_eq_of_finrank_le_three K hdeg.le, hω p.1 hpbad]

end S_LanglandsTunnell_CubicInduction_exists_entire_eulerTwist_induced_of_not_exists_eq_pow_inertiaDeg
end P2MW
export P2MW.S_LanglandsTunnell_CubicInduction_exists_entire_eulerTwist_induced_of_not_exists_eq_pow_inertiaDeg (solution)
