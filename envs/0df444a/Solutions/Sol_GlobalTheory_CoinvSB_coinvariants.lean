-- Prove2me | solution 1 for GlobalTheory.CoinvSB.coinvariants
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T23:24:55.34601+00:00
-- url     : https://prove2.me/submissions/19bb0de3-cd97-4280-897f-5e27dad1bdb4

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_MatrixMeasurableSpace
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_PadicIsNonarchimedeanLocalField
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_AddCharConductorAndHaarIntegersExist
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_FourierTransformInversionLocalFieldPi
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_ExistsSchwartzBruhatConvolutionLocalFieldPower
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_LatticeFrames_ContrFactor
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_LatticeFrames_AllPositions
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_IntegralLastFactorSliceMemSchwartzBruhatStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_ExistsCutoffOfAddCharTranslationInvariantFunctioStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_SchwartzBruhatFunctionalZeroOfFibreIntegralZeroStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_SchwartzBruhatLinearFunctional
import Theorems.Thm_GlobalTheory_CoinvSB_isLocallyConstant_indicator_const
import Theorems.Thm_GlobalTheory_CoinvSB_kernel
import Theorems.Thm_GlobalTheory_SplitWeil_FourierPi_isCompact_box
import Theorems.Thm_GlobalTheory_SplitWeil_FourierPi_isOpen_box
import Theorems.Thm_GlobalTheory_SplitWeil_HasConductor_continuous
import Theorems.Thm_GlobalTheory_SplitWeil_secondCountable
import Theorems.Thm_GlobalTheory_SplitWeil_t2Space
import Theorems.Thm_GlobalTheory_StepData_IntM_mul
import Theorems.Thm_GlobalTheory_T_integral_last_factor_slice_mem_schwartzBruhat


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.SplitWeil.FourierPi
open scoped Topology
noncomputable section
open GlobalTheory GlobalTheory.CoinvSB
namespace GlobalTheory.CoinvSB
theorem _root_.solution : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (ψ : AddChar k Circle) (ν : Measure k), Continuous ψ → ψ ≠ 1 → ν.IsAddHaarMeasure → ∀ (I₀ I₁ I₂ : Type) [Fintype I₀] [Fintype I₁] [Fintype I₂] (M : Type) [AddCommGroup M] [Module ℂ M] (l : SB ((I₀ → k) × (I₁ → k) × (I₂ → k)) →ₗ[ℂ] M), (∀ (b : I₁ → k) (Φ Φ' : SB ((I₀ → k) × (I₁ → k) × (I₂ → k))), (∀ x, Φ'.1 x = (ψ (b ⬝ᵥ x.2.1) : ℂ) * Φ.1 x) → l Φ' = l Φ) → (∀ (a : I₂ → k) (Φ Φ' : SB ((I₀ → k) × (I₁ → k) × (I₂ → k))), (∀ x, Φ'.1 x = Φ.1 (x + (0, 0, a))) → l Φ' = l Φ) → ∃! l₀ : SB (I₀ → k) →ₗ[ℂ] M, ∀ Φ : SB ((I₀ → k) × (I₁ → k) × (I₂ → k)), ∃ Ψ : SB (I₀ → k), (∀ x, Ψ.1 x = ∫ a, Φ.1 (x, 0, a) ∂(Measure.pi fun _ => ν)) ∧ l Φ = l₀ Ψ := by
  intro k _ _ _ _ _ _ ψ ν hψc hψ1 hν I₀ I₁ I₂ _ _ _ M _ _ l h1 h2
  haveI := secondCountable k
  haveI := t2Space k
  set μ : Measure (I₂ → k) := Measure.pi fun _ => ν with hμ
  haveI : μ.IsAddHaarMeasure := by rw [hμ]; infer_instance
  set vol : ℝ := μ.real (box I₂ 1) with hvol
  have hvol0 : vol ≠ 0 := by
    refine (ENNReal.toReal_pos ?_ ?_).ne'
    · exact (isOpen_box 1).measure_ne_zero μ ⟨0, fun i _ => by simp [cball]⟩
    · exact (isCompact_box 1).measure_lt_top.ne
  have hlc : ∀ (n : Type) [Fintype n] (c : ℂ), IsLocallyConstant ((box n (1 : kˣ)).indicator fun _ => c) :=
    fun n _ c => isLocallyConstant_indicator_const (isOpen_box 1) (isCompact_box 1).isClosed c
  let σf : SB (I₀ → k) → (I₀ → k) × (I₁ → k) × (I₂ → k) → ℂ := fun Ψ x =>
    Ψ.1 x.1 * ((box I₁ (1 : kˣ)).indicator (fun _ => (1 : ℂ)) x.2.1 *
      (box I₂ (1 : kˣ)).indicator (fun _ => ((vol : ℂ))⁻¹) x.2.2)
  have hσ : ∀ Ψ, σf Ψ ∈ SB ((I₀ → k) × (I₁ → k) × (I₂ → k)) := by
    intro Ψ
    refine ⟨(Ψ.2.1.comp_continuous continuous_fst).mul
      (((hlc I₁ 1).comp_continuous (by fun_prop)).mul ((hlc I₂ _).comp_continuous (by fun_prop))), ?_⟩
    refine HasCompactSupport.intro (Ψ.2.2.prod ((isCompact_box (1 : kˣ)).prod (isCompact_box (1 : kˣ)))) ?_
    intro x hx
    simp only [σf]
    by_cases h0 : x.1 ∈ tsupport Ψ.1
    · by_cases h1' : x.2.1 ∈ box I₁ (1 : kˣ)
      · have h2' : x.2.2 ∉ box I₂ (1 : kˣ) := fun h => hx ⟨h0, h1', h⟩
        simp [Set.indicator_of_notMem h2']
      · simp [Set.indicator_of_notMem h1']
    · simp [image_eq_zero_of_notMem_tsupport h0]
  let σ : SB (I₀ → k) →ₗ[ℂ] SB ((I₀ → k) × (I₁ → k) × (I₂ → k)) :=
    { toFun := fun Ψ => ⟨σf Ψ, hσ Ψ⟩
      map_add' := fun Ψ Ψ' => by
        apply Subtype.ext; funext x; simp only [σf, Submodule.coe_add, Pi.add_apply]; ring
      map_smul' := fun c Ψ => by
        apply Subtype.ext; funext x; simp only [σf, Submodule.coe_smul, Pi.smul_apply, smul_eq_mul,
          RingHom.id_apply]; ring }
  have hσv : ∀ Ψ x, (σ Ψ).1 x = σf Ψ x := fun _ _ => rfl
  have hInt : ∀ (Φ : SB ((I₀ → k) × (I₁ → k) × (I₂ → k))) (x : I₀ → k),
      Integrable (fun a => Φ.1 (x, 0, a)) μ := by
    intro Φ x
    refine Continuous.integrable_of_hasCompactSupport (Φ.2.1.continuous.comp (by fun_prop)) ?_
    refine HasCompactSupport.intro (IsCompact.image Φ.2.2 (continuous_snd.comp continuous_snd)) fun a ha => ?_
    exact image_eq_zero_of_notMem_tsupport fun h => ha ⟨_, h, rfl⟩
  have hσi : ∀ Ψ x, ∫ a, (σ Ψ).1 (x, 0, a) ∂μ = Ψ.1 x := by
    intro Ψ x
    simp only [hσv, σf]
    have h0 : (0 : I₁ → k) ∈ box I₁ (1 : kˣ) := fun i _ => by simp [cball]
    simp only [Set.indicator_of_mem h0, one_mul]
    rw [integral_const_mul, integral_indicator_const _ (isOpen_box _).measurableSet]
    rw [← hvol, Complex.real_smul, mul_inv_cancel₀ (by exact_mod_cast hvol0), mul_one]
  refine ⟨l ∘ₗ σ, fun Φ => ⟨⟨_, GlobalTheory.T.integral_last_factor_slice_mem_schwartzBruhat k ν I₀ I₁ I₂ Φ⟩, fun x => rfl, ?_⟩, ?_⟩
  · set Ψ : SB (I₀ → k) := ⟨_, GlobalTheory.T.integral_last_factor_slice_mem_schwartzBruhat k ν I₀ I₁ I₂ Φ⟩
    have hk := kernel k ψ ν hψc hψ1 hν I₀ I₁ I₂ M l h1 h2 (Φ - σ Ψ) (fun x₀ => by
      simp only [Submodule.coe_sub, Pi.sub_apply]
      rw [integral_sub (hInt Φ x₀) (hInt (σ Ψ) x₀), hσi]
      exact sub_self _)
    rw [map_sub, sub_eq_zero] at hk
    simpa using hk
  · intro l₀ hl₀
    ext1 Ψ
    obtain ⟨Ψ', hΨ', hl⟩ := hl₀ (σ Ψ)
    have : Ψ' = Ψ := Subtype.ext (funext fun x => (hΨ' x).trans (hσi Ψ x))
    subst this
    simp [← hl]
end GlobalTheory.CoinvSB
