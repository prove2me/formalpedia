-- Prove2me | solution 1 for LanglandsTunnell.CubicInduction.not_exists_eq_pow_inertiaDeg_mul_comp_idelicNorm_of_not_exists
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.670037+00:00
-- url     : https://prove2.me/submissions/58349478-4255-5572-bbad-3899dec77359

import Definitions.Def_LanglandsTunnell_CubicInduction_AutomorphyDatum31
import Definitions.Def_LanglandsTunnell_CubicInduction_MirabolicMajorant
import Definitions.Def_LanglandsTunnell_CubicLambda
import Definitions.Def_M4aHerbrand_GenuineDescent
import Definitions.Def_M4aHerbrand_AdeleBaseChange
import Definitions.Def_NumberField_TateGlobalZeta
import Definitions.Def_NumberField_AdelicLevel
import Definitions.Def_AutomorphicForm_HeckeEigenfunction
import Definitions.Def_LanglandsTunnell_ConverseData
import Definitions.Def_DedekindDomain_Completion_BaseChange
import Theorems.Thm_LanglandsTunnell_RankinSelberg_eq_comp_idelicNorm_of_forall_under_notMem_uniformizerIdele_eq_pow_inertiaDeg
import Theorems.Thm_NumberField_TateGlobal_exists_finset_forall_isUnramifiedCharAt_of_continuous
import Theorems.Thm_M4aHerbrand_exists_idelicNorm_uniformizerIdele_eq_pow_inertiaDeg_mul_localUnit
import Theorems.Thm_NumberField_TateGlobal_localChar_mul_comp_idelicNorm_genuineBaseChange
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LanglandsTunnell_CubicInduction_not_exists_eq_pow_inertiaDeg_mul_comp_idelicNorm_of_not_exists
p2m_attr_erase "instance" "instHenselianLocalRingOfCompactSpaceOfIsNoetherianRing NumberField.instHenselianLocalRingAdicCompletionIntegers instIsAdicCompleteMaximalIdealOfCompactSpace NumberField.instIsAdicCompleteMaximalIdealAdicCompletionIntegers instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instCountableOfNumberField_definitions"

set_option autoImplicit false

open IsDedekindDomain NumberField NumberField.TateGlobal AutomorphicForm LanglandsTunnell.Converse LanglandsTunnell.RankinSelberg LanglandsTunnell.CubicLambda

noncomputable section

namespace AdmissibleTwistClosure

open NumberField AutomorphicForm LanglandsTunnell.Converse

variable {K : Type} [Field K] [NumberField K]

private theorem isIdeleClassChar_mul_inv (η χ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ)
    (hη : IsIdeleClassChar (𝓞 K) K η) (hχ : IsIdeleClassChar (𝓞 K) K χ) :
    IsIdeleClassChar (𝓞 K) K (η * χ⁻¹) := by
  intro u
  rw [MonoidHom.mul_apply, MonoidHom.inv_apply, hη u, hχ u, inv_one, mul_one]

private theorem continuous_mul_inv (η χ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ)
    (hη : Continuous η) (hχ : Continuous χ) : Continuous (η * χ⁻¹) := by
  have h : ⇑(η * χ⁻¹) = fun x => η x * (χ x)⁻¹ := by
    funext x
    rw [MonoidHom.mul_apply, MonoidHom.inv_apply]
  rw [h]
  exact hη.mul hχ.inv

private theorem isUnitaryChar_mul_inv (η χ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ)
    (hη : IsUnitaryChar (𝓞 K) K η) (hχ : IsUnitaryChar (𝓞 K) K χ) :
    IsUnitaryChar (𝓞 K) K (η * χ⁻¹) := by
  intro x
  rw [MonoidHom.mul_apply, MonoidHom.inv_apply, Units.val_mul, Units.val_inv_eq_inv_val, norm_mul,
    norm_inv, hη x, hχ x, inv_one, mul_one]

private theorem isAdmissibleTwist_mul_inv (η χ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ)
    (hη : IsAdmissibleTwist K η) (hχ : IsAdmissibleTwist K χ) : IsAdmissibleTwist K (η * χ⁻¹) :=
  ⟨isIdeleClassChar_mul_inv η χ hη.1 hχ.1, continuous_mul_inv η χ hη.2.1 hχ.2.1,
    isUnitaryChar_mul_inv η χ hη.2.2 hχ.2.2⟩

end AdmissibleTwistClosure

end

section NormTwistUnramified

open IsDedekindDomain NumberField NumberField.TateGlobal M4aHerbrand.GenuineDescent

section

variable (K : Type) [Field K] [NumberField K]

private theorem norm_mem_adicCompletionIntegers (p : HeightOneSpectrum (𝓞 ℚ)) (w : p.Extension (𝓞 K))
    (x : w.1.adicCompletion K) (hx : x ∈ w.1.adicCompletionIntegers K) :
    Algebra.norm (p.adicCompletion ℚ) x ∈ p.adicCompletionIntegers ℚ := by
  haveI : Module.Finite (𝓞 ℚ) (𝓞 K) := Module.Finite.of_restrictScalars_finite ℤ (𝓞 ℚ) (𝓞 K)
  haveI : IsScalarTower (p.adicCompletionIntegers ℚ) (w.1.adicCompletionIntegers K) (w.1.adicCompletion K) :=
    IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  have hx' : IsIntegral (p.adicCompletionIntegers ℚ) x := by
    have h : IsIntegral (p.adicCompletionIntegers ℚ) (⟨x, hx⟩ : w.1.adicCompletionIntegers K) :=
      IsIntegral.of_finite (p.adicCompletionIntegers ℚ) _
    exact h.map (IsScalarTower.toAlgHom (p.adicCompletionIntegers ℚ) (w.1.adicCompletionIntegers K)
      (w.1.adicCompletion K))
  have hn : IsIntegral (p.adicCompletionIntegers ℚ) (Algebra.norm (p.adicCompletion ℚ) x) :=
    Algebra.isIntegral_norm (p.adicCompletion ℚ) hx'
  obtain ⟨y, hy⟩ := IsIntegrallyClosed.isIntegral_iff.mp hn
  rw [← hy]
  exact y.2

private theorem norm_unit_mem_and_inv_mem (p : HeightOneSpectrum (𝓞 ℚ)) (w : p.Extension (𝓞 K))
    (t : (w.1.adicCompletion K)ˣ) (ht : (t : w.1.adicCompletion K) ∈ w.1.adicCompletionIntegers K)
    (ht' : ((t⁻¹ : (w.1.adicCompletion K)ˣ) : w.1.adicCompletion K) ∈ w.1.adicCompletionIntegers K) :
    ((Units.map (Algebra.norm (p.adicCompletion ℚ)) t : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) ∈
        p.adicCompletionIntegers ℚ ∧
      (((Units.map (Algebra.norm (p.adicCompletion ℚ)) t)⁻¹ : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) ∈
        p.adicCompletionIntegers ℚ := by
  refine ⟨?_, ?_⟩
  · simpa only [Units.coe_map, MonoidHom.coe_coe] using norm_mem_adicCompletionIntegers K p w t ht
  · rw [← map_inv]
    simpa only [Units.coe_map, MonoidHom.coe_coe] using norm_mem_adicCompletionIntegers K p w _ ht'

end

private theorem isUnramifiedCharAt_comp_idelicNorm {K : Type} [Field K] [NumberField K]
    (χ : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ)
    (p : HeightOneSpectrum (𝓞 ℚ)) (hχp : IsUnramifiedCharAt χ p) (𝔓 : HeightOneSpectrum (𝓞 K))
    (h𝔓 : 𝔓.under (𝓞 ℚ) = p) :
    IsUnramifiedCharAt (χ.comp (genuineBaseChange ℚ K).idelicNorm) 𝔓 := by
  intro t ht ht'
  let w : p.Extension (𝓞 K) := ⟨𝔓, h𝔓⟩
  have key := DFunLike.congr_fun (localChar_mul_comp_idelicNorm_genuineBaseChange ℚ K 1 χ p w) t
  simp only [localChar_apply, MonoidHom.mul_apply, MonoidHom.one_apply, one_mul,
    MonoidHom.comp_apply] at key
  obtain ⟨h₁, h₂⟩ := norm_unit_mem_and_inv_mem K p w t ht ht'
  exact key.trans (hχp _ h₁ h₂)

end NormTwistUnramified

open IsDedekindDomain NumberField NumberField.TateGlobal AutomorphicForm LanglandsTunnell.Converse LanglandsTunnell.RankinSelberg LanglandsTunnell.CubicLambda

section ConverseLeg

variable (K : Type) [Field K] [NumberField K]

private theorem algebra_ringOfIntegers_rat_eq (inst : Algebra (𝓞 ℚ) (𝓞 K)) :
    inst = NumberField.inst_ringOfIntegersAlgebra ℚ K := by
  refine Algebra.algebra_ext _ _ fun r => ?_
  have h : (@algebraMap (𝓞 ℚ) (𝓞 K) _ _ inst).comp Rat.ringOfIntegersEquiv.symm.toRingHom =
      (@algebraMap (𝓞 ℚ) (𝓞 K) _ _ (NumberField.inst_ringOfIntegersAlgebra ℚ K)).comp
        Rat.ringOfIntegersEquiv.symm.toRingHom :=
    Subsingleton.elim _ _
  have h' := congrArg (fun f : ℤ →+* 𝓞 K => f (Rat.ringOfIntegersEquiv r)) h
  simp only [RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom,
    RingEquiv.symm_apply_apply] at h'
  exact h'

private theorem char_localUnit_eq_one (η₀ : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ) (p : HeightOneSpectrum (𝓞 ℚ))
    (hη₀ : IsUnramifiedCharAt η₀ p) (t : (p.adicCompletion ℚ)ˣ)
    (ht : Valued.v (t : p.adicCompletion ℚ) = 1) :
    η₀ (Units.map (NumberField.AdelicLevel.finIncl (𝓞 ℚ) ℚ) (NumberField.AdelicLevel.localUnit (𝓞 ℚ) ℚ p t)) =
      1 := by
  have h1 : (t : p.adicCompletion ℚ) ∈ p.adicCompletionIntegers ℚ := by
    rw [HeightOneSpectrum.mem_adicCompletionIntegers, ht]
  have h2 : ((t⁻¹ : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) ∈ p.adicCompletionIntegers ℚ := by
    rw [HeightOneSpectrum.mem_adicCompletionIntegers, Units.val_inv_eq_inv_val, map_inv₀, ht, inv_one]
  exact hη₀ t h1 h2

private theorem coe_apply_uniformizerIdele_eq_pow_inertiaDeg_of_eq_comp_idelicNorm
    [inst : Algebra (𝓞 ℚ) (𝓞 K)] [Algebra.IsIntegral (𝓞 ℚ) (𝓞 K)]
    (μ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ) (η₀ : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ)
    (h : μ = η₀.comp (M4aHerbrand.GenuineDescent.genuineBaseChange ℚ K).idelicNorm)
    (𝔓 : HeightOneSpectrum (𝓞 K)) (hη₀ : IsUnramifiedCharAt η₀ (𝔓.under (𝓞 ℚ))) :
    ((μ (uniformizerIdele K 𝔓) : ℂˣ) : ℂ) =
      ((η₀ (uniformizerIdele ℚ (𝔓.under (𝓞 ℚ))) : ℂˣ) : ℂ) ^ (𝔓.under (𝓞 ℚ)).asIdeal.inertiaDeg' 𝔓.asIdeal := by
  have e := algebra_ringOfIntegers_rat_eq K inst
  subst e
  obtain ⟨t, ht, hN⟩ :=
    M4aHerbrand.exists_idelicNorm_uniformizerIdele_eq_pow_inertiaDeg_mul_localUnit ℚ K 𝔓
  have hval : μ (uniformizerIdele K 𝔓) =
      η₀ (uniformizerIdele ℚ (𝔓.under (𝓞 ℚ))) ^ (𝔓.under (𝓞 ℚ)).asIdeal.inertiaDeg' 𝔓.asIdeal := by
    rw [h, MonoidHom.comp_apply, hN, map_mul, map_pow, char_localUnit_eq_one η₀ _ hη₀ t ht, mul_one]
  rw [hval, Units.val_pow_eq_pow_val]

private theorem exists_eq_pow_inertiaDeg_of_eq_comp_idelicNorm
    [Algebra (𝓞 ℚ) (𝓞 K)] [Algebra.IsIntegral (𝓞 ℚ) (𝓞 K)]
    (μ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ) (η₀ : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ) (hη₀ : IsAdmissibleTwist ℚ η₀)
    (h : μ = η₀.comp (M4aHerbrand.GenuineDescent.genuineBaseChange ℚ K).idelicNorm) :
    ∃ η : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ, IsAdmissibleTwist ℚ η ∧
      ∀ 𝔓 : HeightOneSpectrum (𝓞 K), IsUnramifiedCharAt μ 𝔓 →
        IsUnramifiedCharAt η (𝔓.under (𝓞 ℚ)) →
        ((μ (uniformizerIdele K 𝔓) : ℂˣ) : ℂ) =
          ((η (uniformizerIdele ℚ (𝔓.under (𝓞 ℚ))) : ℂˣ) : ℂ) ^
            (𝔓.under (𝓞 ℚ)).asIdeal.inertiaDeg' 𝔓.asIdeal :=
  ⟨η₀, hη₀, fun 𝔓 _ hp => coe_apply_uniformizerIdele_eq_pow_inertiaDeg_of_eq_comp_idelicNorm K μ η₀ h 𝔓 hp⟩

end ConverseLeg

private theorem isUnramifiedCharAt_mul {F : Type} [Field F] [NumberField F]
    (η χ : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ) (v : HeightOneSpectrum (𝓞 F))
    (hη : IsUnramifiedCharAt η v) (hχ : IsUnramifiedCharAt χ v) : IsUnramifiedCharAt (η * χ) v := by
  intro t ht ht'
  have e : localChar (η * χ) v t = localChar η v t * localChar χ v t := by
    simp only [localChar_apply, MonoidHom.mul_apply]
  rw [e, hη t ht ht', hχ t ht ht', mul_one]

private theorem eq_mul_inv_comp_idelicNorm_of_forall_uniformizerIdele
    (K : Type) [Field K] [NumberField K]
    [instA : Algebra (𝓞 ℚ) (𝓞 K)] [Algebra.IsIntegral (𝓞 ℚ) (𝓞 K)]
    (μ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ) (hμ : IsAdmissibleTwist K μ)
    (χ : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ) (hχ : IsAdmissibleTwist ℚ χ)
    (η : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ) (hη' : IsAdmissibleTwist ℚ (η * χ⁻¹))
    (hN : ∀ 𝔓 : HeightOneSpectrum (𝓞 K), IsUnramifiedCharAt χ (𝔓.under (𝓞 ℚ)) →
      IsUnramifiedCharAt (χ.comp (M4aHerbrand.GenuineDescent.genuineBaseChange ℚ K).idelicNorm) 𝔓)
    (hval : ∀ 𝔓 : HeightOneSpectrum (𝓞 K), IsUnramifiedCharAt χ (𝔓.under (𝓞 ℚ)) →
      (((χ.comp (M4aHerbrand.GenuineDescent.genuineBaseChange ℚ K).idelicNorm)
          (uniformizerIdele K 𝔓) : ℂˣ) : ℂ) =
        ((χ (uniformizerIdele ℚ (𝔓.under (𝓞 ℚ))) : ℂˣ) : ℂ) ^
          (𝔓.under (𝓞 ℚ)).asIdeal.inertiaDeg' 𝔓.asIdeal)
    (h : ∀ 𝔓 : HeightOneSpectrum (𝓞 K), IsUnramifiedCharAt
          (μ * χ.comp (M4aHerbrand.GenuineDescent.genuineBaseChange ℚ K).idelicNorm) 𝔓 →
        IsUnramifiedCharAt η (𝔓.under (𝓞 ℚ)) →
        (((μ * χ.comp (M4aHerbrand.GenuineDescent.genuineBaseChange ℚ K).idelicNorm)
            (uniformizerIdele K 𝔓) : ℂˣ) : ℂ) =
          ((η (uniformizerIdele ℚ (𝔓.under (𝓞 ℚ))) : ℂˣ) : ℂ) ^
            (𝔓.under (𝓞 ℚ)).asIdeal.inertiaDeg' 𝔓.asIdeal) :
    μ = (η * χ⁻¹).comp (M4aHerbrand.GenuineDescent.genuineBaseChange ℚ K).idelicNorm := by
  obtain rfl : instA = NumberField.inst_ringOfIntegersAlgebra ℚ K := algebra_ringOfIntegers_rat_eq K instA
  obtain ⟨T, hT⟩ :=
    NumberField.TateGlobal.exists_finset_forall_isUnramifiedCharAt_of_continuous ℚ χ hχ.2.1
  refine eq_comp_idelicNorm_of_forall_under_notMem_uniformizerIdele_eq_pow_inertiaDeg
    K μ hμ.1 hμ.2.1 (η * χ⁻¹) hη'.1 hη'.2.1 T ?_
  intro 𝔓 hpT hμ𝔓 hη'p
  have hχp : IsUnramifiedCharAt χ (𝔓.under (𝓞 ℚ)) := hT _ hpT
  have hηp : IsUnramifiedCharAt η (𝔓.under (𝓞 ℚ)) := by
    have hmul := isUnramifiedCharAt_mul (η * χ⁻¹) χ _ hη'p hχp
    have e : η * χ⁻¹ * χ = η := inv_mul_cancel_right η χ
    rw [e] at hmul
    exact hmul
  have hx := h 𝔓 (isUnramifiedCharAt_mul μ _ 𝔓 hμ𝔓 (hN 𝔓 hχp)) hηp
  rw [MonoidHom.mul_apply, Units.val_mul, hval 𝔓 hχp] at hx
  rw [MonoidHom.mul_apply, MonoidHom.inv_apply, Units.val_mul, Units.val_inv_eq_inv_val, mul_pow, inv_pow]
  exact (eq_mul_inv_iff_mul_eq₀ (pow_ne_zero _ (Units.ne_zero _))).2 hx

open LanglandsTunnell.CubicInduction in

theorem solution
    (K : Type) [Field K] [NumberField K] [Algebra (𝓞 ℚ) (𝓞 K)] [Algebra.IsIntegral (𝓞 ℚ) (𝓞 K)]
    (μ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ) (hμ : IsAdmissibleTwist K μ)
    (χ : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ) (hχ : IsAdmissibleTwist ℚ χ)
    (hns : ¬ (∃ η : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ, IsAdmissibleTwist ℚ η ∧
      ∀ 𝔓 : HeightOneSpectrum (𝓞 K), IsUnramifiedCharAt μ 𝔓 →
        IsUnramifiedCharAt η (𝔓.under (𝓞 ℚ)) →
        ((μ (uniformizerIdele K 𝔓) : ℂˣ) : ℂ) =
          ((η (uniformizerIdele ℚ (𝔓.under (𝓞 ℚ))) : ℂˣ) : ℂ) ^
            (𝔓.under (𝓞 ℚ)).asIdeal.inertiaDeg' 𝔓.asIdeal)) :
    ¬ (∃ η : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ, IsAdmissibleTwist ℚ η ∧
      ∀ 𝔓 : HeightOneSpectrum (𝓞 K), IsUnramifiedCharAt
          (μ * χ.comp (M4aHerbrand.GenuineDescent.genuineBaseChange ℚ K).idelicNorm) 𝔓 →
        IsUnramifiedCharAt η (𝔓.under (𝓞 ℚ)) →
        (((μ * χ.comp (M4aHerbrand.GenuineDescent.genuineBaseChange ℚ K).idelicNorm)
            (uniformizerIdele K 𝔓) : ℂˣ) : ℂ) =
          ((η (uniformizerIdele ℚ (𝔓.under (𝓞 ℚ))) : ℂˣ) : ℂ) ^
            (𝔓.under (𝓞 ℚ)).asIdeal.inertiaDeg' 𝔓.asIdeal) := by
  obtain rfl : ‹Algebra (𝓞 ℚ) (𝓞 K)› = NumberField.inst_ringOfIntegersAlgebra ℚ K :=
    algebra_ringOfIntegers_rat_eq K _
  intro hex
  obtain ⟨η, hη, hvals⟩ := hex
  have hη' := AdmissibleTwistClosure.isAdmissibleTwist_mul_inv η χ hη hχ
  have hA := eq_mul_inv_comp_idelicNorm_of_forall_uniformizerIdele K μ hμ χ hχ η hη'
    (fun 𝔓 hp => isUnramifiedCharAt_comp_idelicNorm χ _ hp 𝔓 rfl)
    (fun 𝔓 hp => coe_apply_uniformizerIdele_eq_pow_inertiaDeg_of_eq_comp_idelicNorm K
      (χ.comp (M4aHerbrand.GenuineDescent.genuineBaseChange ℚ K).idelicNorm) χ rfl 𝔓 hp) hvals
  exact hns (exists_eq_pow_inertiaDeg_of_eq_comp_idelicNorm K μ (η * χ⁻¹) hη' hA)

end S_LanglandsTunnell_CubicInduction_not_exists_eq_pow_inertiaDeg_mul_comp_idelicNorm_of_not_exists
end P2MW
export P2MW.S_LanglandsTunnell_CubicInduction_not_exists_eq_pow_inertiaDeg_mul_comp_idelicNorm_of_not_exists (solution)
