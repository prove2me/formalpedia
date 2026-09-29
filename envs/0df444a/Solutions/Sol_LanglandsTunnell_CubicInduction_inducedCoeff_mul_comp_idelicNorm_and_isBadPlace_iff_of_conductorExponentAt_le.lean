-- Prove2me | solution 1 for LanglandsTunnell.CubicInduction.inducedCoeff_mul_comp_idelicNorm_and_isBadPlace_iff_of_conductorExponentAt_le
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.353894+00:00
-- url     : https://prove2.me/submissions/c1e0a864-e996-509d-a326-6f58aeea0e18

import Definitions.Def_LanglandsTunnell_CubicInduction_AutomorphyDatum31
import Definitions.Def_LanglandsTunnell_CubicInduction_MirabolicMajorant
import Definitions.Def_LanglandsTunnell_CubicLambda
import Definitions.Def_M4aHerbrand_GenuineDescent
import Theorems.Thm_M4aHerbrand_exists_idelicNorm_uniformizerIdele_eq_pow_inertiaDeg_mul_localUnit
import Theorems.Thm_NumberField_TateGlobal_localChar_mul_comp_idelicNorm_genuineBaseChange
import Theorems.Thm_M4aHerbrand_valuation_norm_adicCompletion_eq_pow_inertiaDeg
import Theorems.Thm_M4aHerbrand_GenuineDescent_adelicNorm_genuineBaseChange_algebraMap
import Theorems.Thm_M4aHerbrand_GenuineDescent_continuous_adelicNorm_genuineBaseChange
import Theorems.Thm_LanglandsTunnell_TateLocal_hasConductorExponentAt_comp_norm_of_ramificationIdx_eq_one
import Theorems.Thm_NumberField_TateGlobal_continuous_localChar
import Theorems.Thm_LanglandsTunnell_TateLocal_exists_hasConductorExponentAt_of_continuous
import Theorems.Thm_LanglandsTunnell_TateLocal_hasConductorExponentAt_mul_of_hasConductorExponentAt_of_lt
import Theorems.Thm_LanglandsTunnell_TateLocal_addCharLevel_psiLocal_eq_count_differentIdeal
import Theorems.Thm_LanglandsTunnell_TateLocal_hasConductorExponentAt_comp_norm_of_finrank_eq_three
import Definitions.Def_DedekindDomain_Completion_BaseChange
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LanglandsTunnell_CubicInduction_inducedCoeff_mul_comp_idelicNorm_and_isBadPlace_iff_of_conductorExponentAt_le
p2m_attr_erase "instance" "instHenselianLocalRingOfCompactSpaceOfIsNoetherianRing NumberField.instHenselianLocalRingAdicCompletionIntegers instIsAdicCompleteMaximalIdealOfCompactSpace NumberField.instIsAdicCompleteMaximalIdealAdicCompletionIntegers instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instCountableOfNumberField_definitions"
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

private theorem isIdeleClassChar_comp_idelicNorm (K : Type) [Field K] [NumberField K]
    (η : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ) (hη : IsIdeleClassChar (𝓞 ℚ) ℚ η) :
    IsIdeleClassChar (𝓞 K) K (η.comp (M4aHerbrand.GenuineDescent.genuineBaseChange ℚ K).idelicNorm) := by
  intro u
  have hnorm :
      (M4aHerbrand.GenuineDescent.genuineBaseChange ℚ K).idelicNorm (Units.map (algebraMap K (AdeleRing (𝓞 K) K)) u) =
        Units.map (algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ)) (Units.map (Algebra.norm ℚ (S := K)) u) := by
    apply Units.ext
    have h__af := (M4aHerbrand.GenuineDescent.adelicNorm_genuineBaseChange_algebraMap ℚ K (u : K))
    simp at h__af ⊢
    exact h__af
  simpa [MonoidHom.comp_apply, hnorm] using hη (Units.map (Algebra.norm ℚ (S := K)) u)

private theorem continuous_comp_idelicNorm (K : Type) [Field K] [NumberField K]
    (η : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ) (hcη : Continuous η) :
    Continuous (η.comp (M4aHerbrand.GenuineDescent.genuineBaseChange ℚ K).idelicNorm) := by
  refine hcη.comp ?_
  have hN : Continuous (M4aHerbrand.GenuineDescent.genuineBaseChange ℚ K).adelicNorm :=
      M4aHerbrand.GenuineDescent.continuous_adelicNorm_genuineBaseChange ℚ K
  exact Units.continuous_iff.2 ⟨hN.comp Units.continuous_val, hN.comp Units.continuous_coe_inv⟩

private theorem isAdmissibleTwist_mul_comp_idelicNorm (K : Type) [Field K] [NumberField K]
    (μ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ) (hμ : IsAdmissibleTwist K μ)
    (σ : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ) (hσ : IsAdmissibleTwist ℚ σ) :
    IsAdmissibleTwist K (μ * σ.comp (M4aHerbrand.GenuineDescent.genuineBaseChange ℚ K).idelicNorm) := by
  obtain ⟨hμ1, hμc, hμu⟩ := hμ
  obtain ⟨hσ1, hσc, hσu⟩ := hσ
  refine ⟨fun u => ?_, ?_, fun x => ?_⟩
  · show μ _ * (σ.comp (M4aHerbrand.GenuineDescent.genuineBaseChange ℚ K).idelicNorm) _ = 1
    rw [hμ1 u, isIdeleClassChar_comp_idelicNorm K σ hσ1 u, one_mul]
  · show Continuous fun x => μ x * (σ.comp (M4aHerbrand.GenuineDescent.genuineBaseChange ℚ K).idelicNorm) x
    exact hμc.mul (continuous_comp_idelicNorm K σ hσc)
  · show ‖((μ x * σ ((M4aHerbrand.GenuineDescent.genuineBaseChange ℚ K).idelicNorm x) : ℂˣ) : ℂ)‖ = 1
    rw [Units.val_mul, norm_mul, hμu x, hσu _, one_mul]

namespace LanglandsTunnell p2m_export "LanglandsTunnell" "Converse.pinnedExp TateLocal.mem_higherUnitsAt_iff TateLocal.HasConductorExponentAt TateLocal.hasConductorExponentAt_zero_iff TateLocal.conductorExponentAt TateLocal.conductorExponentAt_eq_of_hasConductorExponentAt TateLocal.hasConductorExponentAt_comp_norm_of_ramificationIdx_eq_one TateLocal.exists_hasConductorExponentAt_of_continuous TateLocal.hasConductorExponentAt_mul_of_hasConductorExponentAt_of_lt TateLocal.addCharLevel_psiLocal_eq_count_differentIdeal TateLocal.hasConductorExponentAt_comp_norm_of_finrank_eq_three" namespace CubicInduction p2m_export "LanglandsTunnell.CubicInduction" "inducedCoeff IsRamifiedIn IsTwistRamifiedAbove IsBadPlace" end LanglandsTunnell.CubicInduction
p2m_open_scoped "LanglandsTunnell LanglandsTunnell.CubicInduction" in
private def LanglandsTunnell.CubicInduction.extensionOfMemPrimeFibre (K : Type) [Field K] [NumberField K]
    {v : HeightOneSpectrum (𝓞 ℚ)} {w : HeightOneSpectrum (𝓞 K)} (hw : w ∈ primeFibre ℚ K v) :
    v.Extension (𝓞 K) :=
  ⟨w, hw⟩

p2m_open_scoped "LanglandsTunnell LanglandsTunnell.CubicInduction" in
private theorem LanglandsTunnell.CubicInduction.val_extensionOfMemPrimeFibre (K : Type) [Field K] [NumberField K]
    {v : HeightOneSpectrum (𝓞 ℚ)} {w : HeightOneSpectrum (𝓞 K)} (hw : w ∈ primeFibre ℚ K v) :
    (extensionOfMemPrimeFibre K hw).1 = w :=
  rfl

p2m_open_scoped "LanglandsTunnell LanglandsTunnell.CubicInduction" in
private theorem LanglandsTunnell.CubicInduction.val_mem_primeFibre (K : Type) [Field K] [NumberField K]
    {v : HeightOneSpectrum (𝓞 ℚ)} (W : v.Extension (𝓞 K)) : W.1 ∈ primeFibre ℚ K v :=
  W.2

p2m_open_scoped "LanglandsTunnell LanglandsTunnell.CubicInduction" in
private theorem LanglandsTunnell.CubicInduction.isUnramifiedCharAt_mul_comp_idelicNorm_of_extension
    (K : Type) [Field K] [NumberField K] (μ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ) (χ : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ)
    (v : HeightOneSpectrum (𝓞 ℚ)) (W : v.Extension (𝓞 K)) (hμ : IsUnramifiedCharAt μ W.1)
    (hχ : IsUnramifiedCharAt χ v) :
    IsUnramifiedCharAt (μ * χ.comp (M4aHerbrand.GenuineDescent.genuineBaseChange ℚ K).idelicNorm) W.1 := by
  intro t ht ht'
  rw [NumberField.TateGlobal.localChar_mul_comp_idelicNorm_genuineBaseChange ℚ K μ χ v W, MonoidHom.mul_apply,
    MonoidHom.comp_apply, hμ t ht ht', one_mul]
  refine hχ _ ?_ ?_
  · rw [HeightOneSpectrum.mem_adicCompletionIntegers, Units.coe_map,
      M4aHerbrand.valuation_norm_adicCompletion_eq_pow_inertiaDeg ℚ K v W]
    exact pow_le_one₀ zero_le' ht
  · rw [← map_inv, HeightOneSpectrum.mem_adicCompletionIntegers, Units.coe_map,
      M4aHerbrand.valuation_norm_adicCompletion_eq_pow_inertiaDeg ℚ K v W]
    exact pow_le_one₀ zero_le' ht'

private theorem coe_mul_comp_idelicNorm_uniformizerIdele (K : Type) [Field K] [NumberField K]
    (μ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ)
    (σ : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ) (𝔓 : HeightOneSpectrum (𝓞 K))
    (hσ𝔓 : IsUnramifiedCharAt σ (𝔓.under (𝓞 ℚ))) :
    (((μ * σ.comp (M4aHerbrand.GenuineDescent.genuineBaseChange ℚ K).idelicNorm)
          (uniformizerIdele K 𝔓) : ℂˣ) : ℂ) =
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
  show ((μ (uniformizerIdele K 𝔓) *
      σ ((M4aHerbrand.GenuineDescent.genuineBaseChange ℚ K).idelicNorm (uniformizerIdele K 𝔓)) : ℂˣ) : ℂ) = _
  rw [hN, map_mul, map_pow, hunit, mul_one, Units.val_mul, Units.val_pow_eq_pow_val]

p2m_open_scoped "LanglandsTunnell LanglandsTunnell.CubicInduction" in
private theorem LanglandsTunnell.CubicInduction.inducedCoeff_mul_comp_idelicNorm_of_not_isBadPlace
    (K : Type) [Field K] [NumberField K] (μ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ) (χ : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ)
    (hoff : ∀ v : HeightOneSpectrum (𝓞 ℚ), ¬ IsBadPlace K μ v → IsUnramifiedCharAt χ v) :
    ∀ v : HeightOneSpectrum (𝓞 ℚ), ¬ IsBadPlace K μ v → ∀ w ∈ primeFibre ℚ K v,
      inducedCoeff K (μ * χ.comp (M4aHerbrand.GenuineDescent.genuineBaseChange ℚ K).idelicNorm) w =
        (χ (uniformizerIdele ℚ v) : ℂ) ^ (v.asIdeal.inertiaDeg' w.asIdeal) * inducedCoeff K μ w := by
  intro v hv w hw
  have hμw : IsUnramifiedCharAt μ w := by
    by_contra h
    have hram : IsTwistRamifiedAbove K μ v := by
      unfold IsTwistRamifiedAbove
      exact ⟨w, hw, h⟩
    exact hv (Or.inr hram)
  have hχv : IsUnramifiedCharAt χ v := hoff v hv
  have hw' : w.under (𝓞 ℚ) = v := hw
  have htw : IsUnramifiedCharAt (μ * χ.comp (M4aHerbrand.GenuineDescent.genuineBaseChange ℚ K).idelicNorm) w :=
    isUnramifiedCharAt_mul_comp_idelicNorm_of_extension K μ χ v (extensionOfMemPrimeFibre K hw) hμw hχv
  have hval := coe_mul_comp_idelicNorm_uniformizerIdele K μ χ w (by rw [hw']; exact hχv)
  unfold inducedCoeff
  rw [if_pos htw, if_pos hμw, hval, hw', mul_comm]

p2m_open_scoped "LanglandsTunnell LanglandsTunnell.CubicInduction" in

private theorem LanglandsTunnell.CubicInduction.hasConductorExponentAt_congr_units
    (K : Type) [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))
    (χ₁ χ₂ : (v.adicCompletion K)ˣ →* ℂˣ)
    (h : ∀ u : (v.adicCompletion K)ˣ, Valued.v (u : v.adicCompletion K) = 1 → χ₁ u = χ₂ u) (c : ℕ)
    (h₁ : LanglandsTunnell.TateLocal.HasConductorExponentAt K v χ₁ c) :
    LanglandsTunnell.TateLocal.HasConductorExponentAt K v χ₂ c := by
  refine ⟨fun u hu => ?_, fun m hm => ?_⟩
  · rw [← h u ((LanglandsTunnell.TateLocal.mem_higherUnitsAt_iff K v).mp hu).1]
    exact h₁.1 u hu
  · obtain ⟨u, hu, hne⟩ := h₁.2 m hm
    refine ⟨u, hu, fun h2 => hne ?_⟩
    rw [h u ((LanglandsTunnell.TateLocal.mem_higherUnitsAt_iff K v).mp hu).1]
    exact h2

p2m_open_scoped "LanglandsTunnell LanglandsTunnell.CubicInduction" in

private theorem LanglandsTunnell.CubicInduction.hasConductorExponentAt_inv
    (K : Type) [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))
    (χ : (v.adicCompletion K)ˣ →* ℂˣ) (c : ℕ) (h : LanglandsTunnell.TateLocal.HasConductorExponentAt K v χ c) :
    LanglandsTunnell.TateLocal.HasConductorExponentAt K v χ⁻¹ c := by
  refine ⟨fun u hu => ?_, fun m hm => ?_⟩
  · rw [MonoidHom.inv_apply, h.1 u hu, inv_one]
  · obtain ⟨u, hu, hne⟩ := h.2 m hm
    refine ⟨u, hu, fun h2 => hne ?_⟩
    rw [MonoidHom.inv_apply, inv_eq_one] at h2
    exact h2

p2m_open_scoped "LanglandsTunnell LanglandsTunnell.CubicInduction" in

private theorem LanglandsTunnell.CubicInduction.not_hasConductorExponentAt_zero_mul
    (K : Type) [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))
    (lam nu : (v.adicCompletion K)ˣ →* ℂˣ) (a : ℕ)
    (hnu : LanglandsTunnell.TateLocal.HasConductorExponentAt K v nu a)
    (hlt : LanglandsTunnell.TateLocal.conductorExponentAt K v lam < a) :
    ¬ LanglandsTunnell.TateLocal.HasConductorExponentAt K v (lam * nu) 0 := by
  intro h0
  have hagree : ∀ u : (v.adicCompletion K)ˣ, Valued.v (u : v.adicCompletion K) = 1 → nu⁻¹ u = lam u := by
    intro u hu
    have h1 : (lam * nu) u = 1 := (LanglandsTunnell.TateLocal.hasConductorExponentAt_zero_iff K v).mp h0 u hu
    rw [MonoidHom.mul_apply, mul_eq_one_iff_eq_inv] at h1
    rw [MonoidHom.inv_apply, h1]
  have hlam : LanglandsTunnell.TateLocal.HasConductorExponentAt K v lam a :=
    hasConductorExponentAt_congr_units K v nu⁻¹ lam hagree a (hasConductorExponentAt_inv K v nu a hnu)
  rw [LanglandsTunnell.TateLocal.conductorExponentAt_eq_of_hasConductorExponentAt K v hlam] at hlt
  exact lt_irrefl a hlt

p2m_open_scoped "LanglandsTunnell LanglandsTunnell.CubicInduction" in

private theorem LanglandsTunnell.CubicInduction.hasConductorExponentAt_zero_of_isUnramifiedCharAt
    (K : Type) [Field K] [NumberField K] (μ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ) (v : HeightOneSpectrum (𝓞 K))
    (h : IsUnramifiedCharAt μ v) :
    LanglandsTunnell.TateLocal.HasConductorExponentAt K v (localChar μ v) 0 := by
  rw [LanglandsTunnell.TateLocal.hasConductorExponentAt_zero_iff]
  intro u hu
  refine h u ?_ ?_
  · show Valued.v (u : v.adicCompletion K) ≤ 1
    exact hu.le
  · show Valued.v (((u⁻¹ : (v.adicCompletion K)ˣ)) : v.adicCompletion K) ≤ 1
    exact le_of_eq (by rw [Units.val_inv_eq_inv_val, map_inv₀, hu, inv_one])

p2m_open_scoped "LanglandsTunnell LanglandsTunnell.CubicInduction" in

private theorem LanglandsTunnell.CubicInduction.not_isUnramifiedCharAt_twist_of_hasConductorExponentAt
    (K : Type) [Field K] [NumberField K]
    (μ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ) (χ : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ)
    (v : HeightOneSpectrum (𝓞 ℚ)) (W : v.Extension (𝓞 K)) (a : ℕ)
    (ha : LanglandsTunnell.TateLocal.HasConductorExponentAt K W.1
      ((localChar χ v).comp (Units.map (Algebra.norm (v.adicCompletion ℚ)))) a)
    (hlt : LanglandsTunnell.TateLocal.conductorExponentAt K W.1 (localChar μ W.1) < a) :
    ¬ IsUnramifiedCharAt (μ * χ.comp (M4aHerbrand.GenuineDescent.genuineBaseChange ℚ K).idelicNorm) W.1 := by
  intro hunr
  have h0 := hasConductorExponentAt_zero_of_isUnramifiedCharAt K _ W.1 hunr
  rw [NumberField.TateGlobal.localChar_mul_comp_idelicNorm_genuineBaseChange ℚ K μ χ v W] at h0
  exact not_hasConductorExponentAt_zero_mul K W.1 (localChar μ W.1) _ a ha hlt h0

p2m_open_scoped "LanglandsTunnell LanglandsTunnell.CubicInduction" in

private theorem LanglandsTunnell.CubicInduction.not_isUnramifiedCharAt_twist_of_extension
    (K : Type) [Field K] [NumberField K]
    (μ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ) (χ : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ)
    (v : HeightOneSpectrum (𝓞 ℚ)) (W : v.Extension (𝓞 K)) (he : v.asIdeal.ramificationIdx' W.1.asIdeal = 1)
    (c : ℕ) (hcχ : LanglandsTunnell.TateLocal.HasConductorExponentAt ℚ v (localChar χ v) c)
    (hlt : LanglandsTunnell.TateLocal.conductorExponentAt K W.1 (localChar μ W.1) < c) :
    ¬ IsUnramifiedCharAt (μ * χ.comp (M4aHerbrand.GenuineDescent.genuineBaseChange ℚ K).idelicNorm) W.1 :=
  not_isUnramifiedCharAt_twist_of_hasConductorExponentAt K μ χ v W c
    (LanglandsTunnell.TateLocal.hasConductorExponentAt_comp_norm_of_ramificationIdx_eq_one ℚ K v W he
      (localChar χ v) c hcχ) hlt

p2m_open_scoped "LanglandsTunnell LanglandsTunnell.CubicInduction" in

private theorem LanglandsTunnell.CubicInduction.exists_hasConductorExponentAt_comp_norm_of_finrank_eq_three
    (K : Type) [Field K] [NumberField K] (hdeg : Module.finrank ℚ K = 3)
    (v : HeightOneSpectrum (𝓞 ℚ)) (w : v.Extension (𝓞 K)) (χ : (v.adicCompletion ℚ)ˣ →* ℂˣ) (c : ℕ)
    (h12 : 12 ≤ c) (hχ : LanglandsTunnell.TateLocal.HasConductorExponentAt ℚ v χ c) :
    ∃ a : ℕ, c ≤ a ∧
      LanglandsTunnell.TateLocal.HasConductorExponentAt K w.1
        (χ.comp (Units.map (Algebra.norm (v.adicCompletion ℚ)))) a ∧
        v.asIdeal.ramificationIdx' w.1.asIdeal * (c - 2) + 1 ≤ a :=
  LanglandsTunnell.TateLocal.hasConductorExponentAt_comp_norm_of_finrank_eq_three K hdeg v w χ c h12 hχ

p2m_open_scoped "LanglandsTunnell LanglandsTunnell.CubicInduction" in

private theorem LanglandsTunnell.CubicInduction.not_isUnramifiedCharAt_twist_of_finrank_eq_three
    (K : Type) [Field K] [NumberField K] (hdeg : Module.finrank ℚ K = 3)
    (μ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ) (χ : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ)
    (v : HeightOneSpectrum (𝓞 ℚ)) (W : v.Extension (𝓞 K)) (c : ℕ)
    (hcχ : LanglandsTunnell.TateLocal.HasConductorExponentAt ℚ v (localChar χ v) c)
    (hcμ : LanglandsTunnell.TateLocal.conductorExponentAt K W.1 (localChar μ W.1) + 12 ≤ c) :
    ¬ IsUnramifiedCharAt (μ * χ.comp (M4aHerbrand.GenuineDescent.genuineBaseChange ℚ K).idelicNorm) W.1 := by
  obtain ⟨a, hca, ha, -⟩ := exists_hasConductorExponentAt_comp_norm_of_finrank_eq_three K hdeg v W (localChar χ v) c
    (le_trans (Nat.le_add_left 12 _) hcμ) hcχ
  exact not_isUnramifiedCharAt_twist_of_hasConductorExponentAt K μ χ v W a ha (by omega)

p2m_open_scoped "LanglandsTunnell LanglandsTunnell.CubicInduction" in

private theorem LanglandsTunnell.CubicInduction.le_pinnedExp_twist_of_finrank_eq_three
    (K : Type) [Field K] [NumberField K] (hdeg : Module.finrank ℚ K = 3)
    (μ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ) (hμc : Continuous μ) (χ : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ)
    (v : HeightOneSpectrum (𝓞 ℚ)) (W : v.Extension (𝓞 K)) (c : ℕ)
    (hcχ : LanglandsTunnell.TateLocal.HasConductorExponentAt ℚ v (localChar χ v) c)
    (hcμ : LanglandsTunnell.TateLocal.conductorExponentAt K W.1 (localChar μ W.1) + 12 ≤ c) :
    (v.asIdeal.ramificationIdx' W.1.asIdeal : ℤ) * ((c : ℤ) - 2) + 1 ≤ LanglandsTunnell.Converse.pinnedExp K
        (μ * χ.comp (M4aHerbrand.GenuineDescent.genuineBaseChange ℚ K).idelicNorm) W.1 := by
  obtain ⟨a, hca, ha, had⟩ := exists_hasConductorExponentAt_comp_norm_of_finrank_eq_three K hdeg v W (localChar χ v)
    c (le_trans (Nat.le_add_left 12 _) hcμ) hcχ
  obtain ⟨b, hb⟩ := LanglandsTunnell.TateLocal.exists_hasConductorExponentAt_of_continuous K W.1 (localChar μ W.1)
    (NumberField.TateGlobal.continuous_localChar μ hμc W.1)
  rw [LanglandsTunnell.TateLocal.conductorExponentAt_eq_of_hasConductorExponentAt K W.1 hb] at hcμ
  have hexp : LanglandsTunnell.TateLocal.HasConductorExponentAt K W.1
      (localChar (μ * χ.comp (M4aHerbrand.GenuineDescent.genuineBaseChange ℚ K).idelicNorm) W.1) a := by
    have hprod := LanglandsTunnell.TateLocal.hasConductorExponentAt_mul_of_hasConductorExponentAt_of_lt K W.1 _ _ a b
      ha hb (by omega)
    rw [NumberField.TateGlobal.localChar_mul_comp_idelicNorm_genuineBaseChange ℚ K μ χ v W]
    exact hasConductorExponentAt_congr_units K W.1 _ _
      (fun u _ => by rw [MonoidHom.mul_apply, MonoidHom.mul_apply, mul_comm]) a hprod
  rw [LanglandsTunnell.Converse.pinnedExp,
    LanglandsTunnell.TateLocal.conductorExponentAt_eq_of_hasConductorExponentAt K W.1 hexp,
    LanglandsTunnell.TateLocal.addCharLevel_psiLocal_eq_count_differentIdeal K W.1]
  have h0 := FractionalIdeal.count_coe_nonneg K W.1 (differentIdeal ℤ (𝓞 K))
  have h2c : 2 ≤ c := le_trans (by norm_num) (le_trans (Nat.le_add_left 12 _) hcμ)
  zify [h2c] at had
  linarith

open _root_.LanglandsTunnell.CubicInduction _root_.P2MW.S_LanglandsTunnell_CubicInduction_inducedCoeff_mul_comp_idelicNorm_and_isBadPlace_iff_of_conductorExponentAt_le.LanglandsTunnell.CubicInduction in

theorem solution
    (K : Type) [Field K] [NumberField K] [Algebra (𝓞 ℚ) (𝓞 K)] [Algebra.IsIntegral (𝓞 ℚ) (𝓞 K)]
    (hdeg : Module.finrank ℚ K = 3)
    (μ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ) (hμ : IsAdmissibleTwist K μ)
    (χ : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ) (hχ : IsAdmissibleTwist ℚ χ)
    (hoff : ∀ v : HeightOneSpectrum (𝓞 ℚ), ¬ IsBadPlace K μ v → IsUnramifiedCharAt χ v)
    (c : HeightOneSpectrum (𝓞 ℚ) → ℕ)
    (hc : ∀ v : HeightOneSpectrum (𝓞 ℚ), IsBadPlace K μ v →
      LanglandsTunnell.TateLocal.HasConductorExponentAt ℚ v (localChar χ v) (c v) ∧
        ∀ w ∈ primeFibre ℚ K v,
          LanglandsTunnell.TateLocal.conductorExponentAt K w (localChar μ w) + 12 ≤ c v) :
    IsAdmissibleTwist K (μ * χ.comp (M4aHerbrand.GenuineDescent.genuineBaseChange ℚ K).idelicNorm) ∧
    (∀ v : HeightOneSpectrum (𝓞 ℚ), ¬ IsBadPlace K μ v → ∀ w ∈ primeFibre ℚ K v,
      inducedCoeff K (μ * χ.comp (M4aHerbrand.GenuineDescent.genuineBaseChange ℚ K).idelicNorm) w =
        (χ (uniformizerIdele ℚ v) : ℂ) ^ (v.asIdeal.inertiaDeg' w.asIdeal) *
          inducedCoeff K μ w) ∧
    (∀ v : HeightOneSpectrum (𝓞 ℚ),
      IsBadPlace K (μ * χ.comp (M4aHerbrand.GenuineDescent.genuineBaseChange ℚ K).idelicNorm) v ↔ IsBadPlace K μ v) ∧
    (∀ v : HeightOneSpectrum (𝓞 ℚ), IsBadPlace K μ v →
      (∀ w ∈ primeFibre ℚ K v, ¬ IsUnramifiedCharAt
        (μ * χ.comp (M4aHerbrand.GenuineDescent.genuineBaseChange ℚ K).idelicNorm) w)) ∧
    (∀ v : HeightOneSpectrum (𝓞 ℚ), IsBadPlace K μ v →
      3 * (c v : ℤ) ≤ 12 +
        ∑ᶠ w ∈ primeFibre ℚ K v, (v.asIdeal.inertiaDeg' w.asIdeal : ℤ) * LanglandsTunnell.Converse.pinnedExp K
          (μ * χ.comp (M4aHerbrand.GenuineDescent.genuineBaseChange ℚ K).idelicNorm) w) := by
  classical
  obtain rfl := algebra_ringOfIntegers_rat_eq K ‹Algebra (𝓞 ℚ) (𝓞 K)›
  obtain ⟨-, hμc, -⟩ := id hμ
  refine ⟨isAdmissibleTwist_mul_comp_idelicNorm K μ hμ χ hχ,
    inducedCoeff_mul_comp_idelicNorm_of_not_isBadPlace K μ χ hoff, fun v => ?_, fun v hbad w hw => ?_,
    fun v hbad => ?_⟩
  ·
    constructor
    · intro hbad'
      by_contra hgood
      rcases hbad' with hram | ⟨w, hw, hnot⟩
      · exact hgood (Or.inl hram)
      · have hμw : IsUnramifiedCharAt μ w := by
          by_contra hμw
          exact hgood (Or.inr ⟨w, hw, hμw⟩)
        exact hnot (isUnramifiedCharAt_mul_comp_idelicNorm_of_extension K μ χ v (extensionOfMemPrimeFibre K hw)
          hμw (hoff v hgood))
    · intro hbad
      rcases hbad with hram | ⟨w, hw, hnot⟩
      · exact Or.inl hram
      · by_cases hram : IsRamifiedIn K v
        · exact Or.inl hram
        · have he : v.asIdeal.ramificationIdx' w.asIdeal = 1 := by
            by_contra hne
            exact hram ⟨w, hw, hne⟩
          obtain ⟨hcχ, hcμ⟩ := hc v (Or.inr ⟨w, hw, hnot⟩)
          have hlt : LanglandsTunnell.TateLocal.conductorExponentAt K w (localChar μ w) < c v := by
            have h12 := hcμ w hw
            omega
          exact Or.inr ⟨w, hw, not_isUnramifiedCharAt_twist_of_extension K μ χ v (extensionOfMemPrimeFibre K hw)
            he (c v) hcχ hlt⟩
  ·
    obtain ⟨hcχ, hcμ⟩ := hc v hbad
    exact not_isUnramifiedCharAt_twist_of_finrank_eq_three K hdeg μ χ v (extensionOfMemPrimeFibre K hw) (c v) hcχ
      (hcμ w hw)
  ·
    obtain ⟨hcχ, hcμ⟩ := hc v hbad
    have hfin := primeFibre_finite K v
    have hkey : ∀ w ∈ primeFibre ℚ K v,
        ((v.asIdeal.ramificationIdx' w.asIdeal * v.asIdeal.inertiaDeg' w.asIdeal : ℕ) : ℤ) * ((c v : ℤ) - 2) ≤
          (v.asIdeal.inertiaDeg' w.asIdeal : ℤ) * LanglandsTunnell.Converse.pinnedExp K
            (μ * χ.comp (M4aHerbrand.GenuineDescent.genuineBaseChange ℚ K).idelicNorm) w := by
      intro w hw
      have h : (v.asIdeal.ramificationIdx' w.asIdeal : ℤ) * ((c v : ℤ) - 2) + 1 ≤ LanglandsTunnell.Converse.pinnedExp K
          (μ * χ.comp (M4aHerbrand.GenuineDescent.genuineBaseChange ℚ K).idelicNorm) w :=
        le_pinnedExp_twist_of_finrank_eq_three K hdeg μ hμc χ v (extensionOfMemPrimeFibre K hw) (c v) hcχ (hcμ w hw)
      have hf : (0 : ℤ) ≤ (v.asIdeal.inertiaDeg' w.asIdeal : ℤ) := Nat.cast_nonneg _
      have h1 := mul_le_mul_of_nonneg_left h hf
      push_cast
      linarith
    have hle := Finset.sum_le_sum fun w hw => hkey w (hfin.mem_toFinset.mp hw)
    have h3 : ∑ w ∈ hfin.toFinset, v.asIdeal.ramificationIdx' w.asIdeal * v.asIdeal.inertiaDeg' w.asIdeal = 3 := by
      rw [← finsum_mem_eq_finite_toFinset_sum _ hfin, finsum_fibre_ramificationIdx_mul_inertiaDeg K v, hdeg]
    rw [← Finset.sum_mul, ← Nat.cast_sum, h3] at hle
    rw [finsum_mem_eq_finite_toFinset_sum _ hfin]
    push_cast at hle
    linarith
#print axioms solution

end S_LanglandsTunnell_CubicInduction_inducedCoeff_mul_comp_idelicNorm_and_isBadPlace_iff_of_conductorExponentAt_le
end P2MW
export P2MW.S_LanglandsTunnell_CubicInduction_inducedCoeff_mul_comp_idelicNorm_and_isBadPlace_iff_of_conductorExponentAt_le (solution)
