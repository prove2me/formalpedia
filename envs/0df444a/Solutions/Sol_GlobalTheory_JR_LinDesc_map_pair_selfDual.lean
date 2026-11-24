-- Prove2me | solution 1 for GlobalTheory.JR.LinDesc.map_pair_selfDual
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T18:01:20.672239+00:00
-- url     : https://prove2.me/submissions/96a268b9-ea77-4c55-8102-f704c6f8fb00

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_LeftMulTau
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_SelfDualIffLatticeVolumeAndPlancherelStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_JacquetRallisInvKRegularIffIsUnit
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_PartialFourierGlOrbitEqFourierEtaleKProd

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.JR Matrix MeasureTheory Filter Topology
noncomputable section
open GlobalTheory GlobalTheory.JR GlobalTheory.JR.LinDesc
namespace GlobalTheory.JR.LinDesc
theorem _root_.solution {F : Type} [NontriviallyNormedField F] [LocallyCompactSpace F] [MeasurableSpace F]
    [BorelSpace F] {r : ℕ} {V : Type} [AddCommGroup V] [Module F V] [TopologicalSpace V] [IsModuleTopology F V]
    [IsTopologicalAddGroup V] [ContinuousSMul F V] [MeasurableSpace V] [BorelSpace V]
    (ψ : AddChar F ℂ) (B : V → V → F) (hBs : ∀ x y, B x y = B y x)
    (e₁ e₂ : V ≃ₗ[F] (Fin r → F)) (hB : ∀ x y, e₁ x ⬝ᵥ e₂ y = B x y)
    (μV : Measure V) (hV : SelfDual μV (fun x y => ψ (B x y)))
    (ν : Measure (Fin r → F)) (hν : SelfDual ν (fun x y => ψ (x ⬝ᵥ y)))
    (h₀ : (Fin r → F) → ℂ) (ht₀ : IsTest h₀) (h₀0 : h₀ 0 = 1) :
    ∃ c₁ c₂ : ℂ, (∀ φ : (Fin r → F) → ℂ, ∫ x, φ (e₁ x) ∂μV = c₁ * ∫ y, φ y ∂ν) ∧
      (∀ φ : (Fin r → F) → ℂ, ∫ x, φ (e₂ x) ∂μV = c₂ * ∫ y, φ y ∂ν) ∧ c₁ * c₂ = 1 := by
  haveI : ProperSpace F := ProperSpace.of_locallyCompactSpace F
  haveI : SecondCountableTopology F := secondCountable_of_proper
  haveI := hV.1
  haveI := hν.1
  let E₁ : V ≃L[F] (Fin r → F) :=
    { e₁ with
      continuous_toFun := IsModuleTopology.continuous_of_linearMap e₁.toLinearMap
      continuous_invFun := IsModuleTopology.continuous_of_linearMap e₁.symm.toLinearMap }
  let E₂ : V ≃L[F] (Fin r → F) :=
    { e₂ with
      continuous_toFun := IsModuleTopology.continuous_of_linearMap e₂.toLinearMap
      continuous_invFun := IsModuleTopology.continuous_of_linearMap e₂.symm.toLinearMap }
  haveI : (Measure.map E₁ μV).IsAddHaarMeasure := E₁.isAddHaarMeasure_map μV
  haveI : (Measure.map E₂ μV).IsAddHaarMeasure := E₂.isAddHaarMeasure_map μV
  have hm₁ := Measure.isAddLeftInvariant_eq_smul (Measure.map E₁ μV) ν
  have hm₂ := Measure.isAddLeftInvariant_eq_smul (Measure.map E₂ μV) ν
  set c₁ := (Measure.map E₁ μV).addHaarScalarFactor ν
  set c₂ := (Measure.map E₂ μV).addHaarScalarFactor ν
  let M₁ := E₁.toHomeomorph.toMeasurableEquiv
  let M₂ := E₂.toHomeomorph.toMeasurableEquiv
  have hM₁ : ∀ x, M₁ x = e₁ x := fun _ => rfl
  have hM₂ : ∀ x, M₂ x = e₂ x := fun _ => rfl
  have hmap : ∀ (M : V ≃ᵐ (Fin r → F)) (c : ENNReal), Measure.map M μV = c • ν →
      ∀ φ : (Fin r → F) → ℂ, ∫ x, φ (M x) ∂μV = (c.toReal : ℂ) * ∫ y, φ y ∂ν := by
    intro M c hc φ
    rw [← integral_map_equiv M φ, hc, integral_smul_measure, Complex.real_smul]
  set FF := fourB ν (fun x y => ψ (x ⬝ᵥ y))
  set FV := fourB μV (fun x y => ψ (B x y))
  set f : V → ℂ := h₀ ∘ E₁
  have hf : IsTest f := ⟨ht₀.1.comp_continuous E₁.continuous, ht₀.2.comp_homeomorph E₁.toHomeomorph⟩
  have ha : ∀ c, FV f c = (c₁ : ℂ) * FF h₀ (e₂ c) := by
    intro c
    have := hmap M₁ c₁ hm₁ (fun y => h₀ y * ψ (y ⬝ᵥ e₂ c))
    simp only [hM₁, ENNReal.coe_toReal] at this
    simp only [FV, FF, fourB, f, Function.comp_apply]
    rw [← this]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    simp only [← hB]; rfl
  have hb : ∀ b, FV (FV f) b = (c₁ : ℂ) * (c₂ : ℂ) * FF (FF h₀) (e₁ b) := by
    intro b
    have := hmap M₂ c₂ hm₂ (fun y => FF h₀ y * ψ (y ⬝ᵥ e₁ b))
    simp only [hM₂, ENNReal.coe_toReal] at this
    show ∫ c, FV f c * ψ (B c b) ∂μV = _
    simp only [ha]
    have e : ∀ c, (c₁ : ℂ) * FF h₀ (e₂ c) * ψ (B c b) = (c₁ : ℂ) * (FF h₀ (e₂ c) * ψ (e₂ c ⬝ᵥ e₁ b)) := by
      intro c; rw [hBs, ← hB, dotProduct_comm, mul_assoc]
    simp only [e]
    rw [integral_const_mul, this, mul_assoc]
    rfl
  refine ⟨c₁, c₂, fun φ => ?_, fun φ => ?_, ?_⟩
  · have := hmap M₁ c₁ hm₁ φ; simpa only [hM₁, ENNReal.coe_toReal] using this
  · have := hmap M₂ c₂ hm₂ φ; simpa only [hM₂, ENNReal.coe_toReal] using this
  have h1 := hb 0
  have h3 : FV (FV f) 0 = f (-0) := hV.2 f hf 0
  have h4 : FF (FF h₀) 0 = h₀ (-0) := hν.2 h₀ ht₀ 0
  rw [h3, map_zero, h4] at h1
  simp only [neg_zero, f, Function.comp_apply, map_zero, h₀0, mul_one] at h1
  rw [← h1]
end GlobalTheory.JR.LinDesc
