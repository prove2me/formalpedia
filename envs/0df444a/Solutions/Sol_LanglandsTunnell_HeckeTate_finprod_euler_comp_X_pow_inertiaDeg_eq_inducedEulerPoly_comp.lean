-- Prove2me | solution 1 for LanglandsTunnell.HeckeTate.finprod_euler_comp_X_pow_inertiaDeg_eq_inducedEulerPoly_comp
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.670037+00:00
-- url     : https://prove2.me/submissions/51f4fec0-fabf-5654-acd1-915ebd63e970

import Definitions.Def_LanglandsTunnell_HeckeTate
import Definitions.Def_M4aHerbrand_GenuineDescent
import Definitions.Def_LanglandsTunnell_RankinSelbergEuler
import Definitions.Def_LanglandsTunnell_CubicInduction_Structure
import Definitions.Def_LanglandsTunnell_CubicLambda
import Definitions.Def_DedekindDomain_Completion_BaseChange
import Theorems.Thm_NumberField_TateGlobal_localChar_mul_comp_idelicNorm_genuineBaseChange
import Theorems.Thm_M4aHerbrand_exists_idelicNorm_uniformizerIdele_eq_pow_inertiaDeg_mul_localUnit
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LanglandsTunnell_HeckeTate_finprod_euler_comp_X_pow_inertiaDeg_eq_inducedEulerPoly_comp
p2m_attr_erase "instance" "instHenselianLocalRingOfCompactSpaceOfIsNoetherianRing NumberField.instHenselianLocalRingAdicCompletionIntegers instIsAdicCompleteMaximalIdealOfCompactSpace NumberField.instIsAdicCompleteMaximalIdealAdicCompletionIntegers instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instCountableOfNumberField_definitions"

set_option autoImplicit false

open NumberField IsDedekindDomain AutomorphicForm NumberField.TateGlobal
open LanglandsTunnell.Converse LanglandsTunnell.HeckeTate LanglandsTunnell.RankinSelberg LanglandsTunnell.CubicLambda
open LanglandsTunnell.CubicInduction Polynomial

private theorem algebra_ringOfIntegers_rat_eq (K : Type) [Field K] [NumberField K]
    (inst : Algebra (𝓞 ℚ) (𝓞 K)) : inst = NumberField.inst_ringOfIntegersAlgebra ℚ K := by
  refine Algebra.algebra_ext _ _ fun r => ?_
  have huniq : ∀ f g : 𝓞 ℚ →+* 𝓞 K, f = g := fun f g => by
    have h1 : f.comp Rat.ringOfIntegersEquiv.symm.toRingHom = g.comp Rat.ringOfIntegersEquiv.symm.toRingHom :=
      Subsingleton.elim _ _
    have h2 := congrArg (fun φ : ℤ →+* 𝓞 K => φ.comp Rat.ringOfIntegersEquiv.toRingHom) h1
    simp only [RingHom.comp_assoc, RingEquiv.symm_toRingHom_comp_toRingHom, RingHom.comp_id] at h2
    exact h2
  exact RingHom.congr_fun
    (huniq (@algebraMap _ _ _ _ inst) (@algebraMap _ _ _ _ (NumberField.inst_ringOfIntegersAlgebra ℚ K))) r

private theorem char_localUnit_eq_one_of_isUnramifiedCharAt (χ : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ)
    (p : HeightOneSpectrum (𝓞 ℚ)) (hχ : IsUnramifiedCharAt χ p) (t : (p.adicCompletion ℚ)ˣ)
    (ht : Valued.v (t : p.adicCompletion ℚ) = 1) :
    χ (Units.map (NumberField.AdelicLevel.finIncl (𝓞 ℚ) ℚ) (NumberField.AdelicLevel.localUnit (𝓞 ℚ) ℚ p t)) = 1 := by
  have hinv : Valued.v ((t⁻¹ : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) = 1 := by
    have h := congrArg Valued.v (Units.mul_inv t)
    rwa [map_mul, ht, one_mul, map_one] at h
  have h1 : (t : p.adicCompletion ℚ) ∈ p.adicCompletionIntegers ℚ := by
    rw [HeightOneSpectrum.mem_adicCompletionIntegers]
    exact ht.le
  have h2 : ((t⁻¹ : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) ∈ p.adicCompletionIntegers ℚ := by
    rw [HeightOneSpectrum.mem_adicCompletionIntegers]
    exact hinv.le
  exact hχ t h1 h2

private theorem norm_mem_adicCompletionIntegers (K : Type) [Field K] [NumberField K]
    (p : HeightOneSpectrum (𝓞 ℚ)) (w : p.Extension (𝓞 K))
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

private theorem norm_unit_mem_and_inv_mem (K : Type) [Field K] [NumberField K]
    (p : HeightOneSpectrum (𝓞 ℚ)) (w : p.Extension (𝓞 K))
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

private theorem isUnramifiedCharAt_comp_idelicNorm {K : Type} [Field K] [NumberField K]
    (χ : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ)
    (p : HeightOneSpectrum (𝓞 ℚ)) (hχp : IsUnramifiedCharAt χ p) (𝔓 : HeightOneSpectrum (𝓞 K))
    (h𝔓 : 𝔓.under (𝓞 ℚ) = p) :
    IsUnramifiedCharAt (χ.comp (M4aHerbrand.GenuineDescent.genuineBaseChange ℚ K).idelicNorm) 𝔓 := by
  intro t ht ht'
  let w : p.Extension (𝓞 K) := ⟨𝔓, h𝔓⟩
  have key := DFunLike.congr_fun (localChar_mul_comp_idelicNorm_genuineBaseChange ℚ K 1 χ p w) t
  simp only [localChar_apply, MonoidHom.mul_apply, MonoidHom.one_apply, one_mul,
    MonoidHom.comp_apply] at key
  obtain ⟨h₁, h₂⟩ := norm_unit_mem_and_inv_mem K p w t ht ht'
  exact key.trans (hχp _ h₁ h₂)

private theorem isUnramifiedCharAt_mul_iff_of_isUnramifiedCharAt (K : Type) [Field K] [NumberField K]
    (μ ν : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ) (𝔓 : HeightOneSpectrum (𝓞 K)) (hν : IsUnramifiedCharAt ν 𝔓) :
    IsUnramifiedCharAt (μ * ν) 𝔓 ↔ IsUnramifiedCharAt μ 𝔓 := by
  have hmul : ∀ t : (𝔓.adicCompletion K)ˣ, localChar (μ * ν) 𝔓 t = localChar μ 𝔓 t * localChar ν 𝔓 t :=
    fun _ => rfl
  constructor
  · intro h t ht ht'
    have h1 := h t ht ht'
    rwa [hmul, hν t ht ht', mul_one] at h1
  · intro h t ht ht'
    rw [hmul, h t ht ht', hν t ht ht', mul_one]

private theorem mul_comp_idelicNorm_apply_uniformizerIdele (K : Type) [Field K] [NumberField K]
    (μ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ) (τ : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ) (𝔓 : HeightOneSpectrum (𝓞 K))
    (hτ : IsUnramifiedCharAt τ (𝔓.under (𝓞 ℚ))) :
    (μ * τ.comp (M4aHerbrand.GenuineDescent.genuineBaseChange ℚ K).idelicNorm) (uniformizerIdele K 𝔓) =
      μ (uniformizerIdele K 𝔓) *
        τ (uniformizerIdele ℚ (𝔓.under (𝓞 ℚ))) ^ ((𝔓.under (𝓞 ℚ)).asIdeal.inertiaDeg' 𝔓.asIdeal) := by
  obtain ⟨t, ht, hN⟩ := M4aHerbrand.exists_idelicNorm_uniformizerIdele_eq_pow_inertiaDeg_mul_localUnit ℚ K 𝔓
  rw [MonoidHom.mul_apply, MonoidHom.comp_apply, hN, map_mul, map_pow,
    char_localUnit_eq_one_of_isUnramifiedCharAt τ _ hτ t ht, mul_one]

private theorem euler_comp_X_pow_inertiaDeg_eq_inducedFactor_comp (K : Type) [Field K] [NumberField K]
    (μ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ) (τ : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ)
    (uR : ∀ w : InfinitePlace K, w.IsReal → ℂ) (aR : ∀ w : InfinitePlace K, w.IsReal → ZMod 2)
    (uC : ∀ w : InfinitePlace K, w.IsComplex → ℂ) (kC : ∀ w : InfinitePlace K, w.IsComplex → ℤ)
    (𝔓 : HeightOneSpectrum (𝓞 K)) (p : HeightOneSpectrum (𝓞 ℚ)) (h𝔓 : 𝔓.under (𝓞 ℚ) = p)
    (hτ : IsUnramifiedCharAt τ p) :
    ((heckeDatum K (μ * τ.comp (M4aHerbrand.GenuineDescent.genuineBaseChange ℚ K).idelicNorm)
        uR aR uC kC).euler 𝔓).comp (X ^ ((𝔓.under (𝓞 ℚ)).asIdeal.inertiaDeg' 𝔓.asIdeal))
      = (inducedFactor ℚ (inducedCoeff K μ) 𝔓).comp (C (eulerCoeff ℚ τ p) * X) := by
  subst h𝔓
  have hiff := isUnramifiedCharAt_mul_iff_of_isUnramifiedCharAt K μ _ 𝔓
    (isUnramifiedCharAt_comp_idelicNorm τ _ hτ 𝔓 rfl)
  simp only [heckeDatum, inducedFactor, inducedCoeff, eulerCoeff, if_pos hτ]
  by_cases hμ : IsUnramifiedCharAt μ 𝔓
  · rw [if_pos (hiff.2 hμ), if_pos hμ, mul_comp_idelicNorm_apply_uniformizerIdele K μ τ 𝔓 hτ]
    push_cast
    simp only [sub_comp, mul_comp, pow_comp, C_comp, X_comp, mul_pow, C_mul, C_pow, mul_assoc]
  · rw [if_neg (fun h => hμ (hiff.1 h)), if_neg hμ]
    simp only [C_comp, C_0, zero_mul, sub_zero]

private theorem comp_C_mul_X_injective (c : ℂ) (hc : c ≠ 0) :
    Function.Injective (fun q : ℂ[X] => q.comp (C c * X)) := by
  intro q₁ q₂ h
  have key : ∀ q : ℂ[X], (q.comp (C c * X)).comp (C c⁻¹ * X) = q := fun q => by
    rw [comp_assoc, C_mul_comp, X_comp, ← mul_assoc, ← C_mul, mul_inv_cancel₀ hc, C_1, one_mul, comp_X]
  have h' : q₁.comp (C c * X) = q₂.comp (C c * X) := h
  rw [← key q₁, ← key q₂, h']

private theorem finprod_mem_comp_C_mul_X {ι : Type} (s : Set ι) (g : ι → ℂ[X]) (c : ℂ) (hc : c ≠ 0) :
    (∏ᶠ i ∈ s, g i).comp (C c * X) = ∏ᶠ i ∈ s, (g i).comp (C c * X) := by
  have h := (compRingHom (C c * X)).toMonoidHom.map_finprod_of_injective
    (fun a b hab => comp_C_mul_X_injective c hc hab) (fun i => s.mulIndicator g i)
  rw [finprod_mem_def, finprod_mem_def]
  refine h.trans (finprod_congr fun i => ?_)
  exact map_mulIndicator (compRingHom (C c * X)).toMonoidHom s g i

open LanglandsTunnell LanglandsTunnell.HeckeTate in
theorem solution
    (K : Type) [Field K] [NumberField K] [Algebra (𝓞 ℚ) (𝓞 K)] [Algebra.IsIntegral (𝓞 ℚ) (𝓞 K)]
    (μ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ) (τ : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ)
    (uR : ∀ w : InfinitePlace K, w.IsReal → ℂ) (aR : ∀ w : InfinitePlace K, w.IsReal → ZMod 2)
    (uC : ∀ w : InfinitePlace K, w.IsComplex → ℂ) (kC : ∀ w : InfinitePlace K, w.IsComplex → ℤ)
    (p : HeightOneSpectrum (𝓞 ℚ)) (hτ : IsUnramifiedCharAt τ p) :
    (∏ᶠ 𝔓 ∈ primeFibre ℚ K p,
        ((heckeDatum K (μ * τ.comp (M4aHerbrand.GenuineDescent.genuineBaseChange ℚ K).idelicNorm)
            uR aR uC kC).euler 𝔓).comp (X ^ ((𝔓.under (𝓞 ℚ)).asIdeal.inertiaDeg' 𝔓.asIdeal)))
      = (inducedEulerPoly ℚ (inducedCoeff K μ) p).comp (C (eulerCoeff ℚ τ p) * X) := by
  obtain rfl := algebra_ringOfIntegers_rat_eq K ‹Algebra (𝓞 ℚ) (𝓞 K)›
  have hc : eulerCoeff ℚ τ p ≠ 0 := by
    simp only [eulerCoeff, if_pos hτ]
    exact Units.ne_zero _
  rw [inducedEulerPoly, finprod_mem_comp_C_mul_X _ _ _ hc]
  exact finprod_mem_congr rfl fun 𝔓 h𝔓 =>
    euler_comp_X_pow_inertiaDeg_eq_inducedFactor_comp K μ τ uR aR uC kC 𝔓 p h𝔓 hτ

end S_LanglandsTunnell_HeckeTate_finprod_euler_comp_X_pow_inertiaDeg_eq_inducedEulerPoly_comp
end P2MW
export P2MW.S_LanglandsTunnell_HeckeTate_finprod_euler_comp_X_pow_inertiaDeg_eq_inducedEulerPoly_comp (solution)
