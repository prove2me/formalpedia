-- Prove2me | solution 1 for MechanismDesign.Dynamic.dynamic_revelation_principle
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-07T09:54:28.557997+00:00
-- url     : https://prove2.me/submissions/805e30a5-e1f5-49c7-9f99-fc296ff976c2

import Mathlib
import Definitions.Def_MechanismDesign_Dynamic_Model



namespace MechanismDesign.Dynamic

theorem drp_core {τlo τhi θlo θhi : ℝ} (E : SeqEnv τlo τhi θlo θhi)
    (Γ : DynMechanism) (hΓ : Γ.Valid) (σ₁ : ℝ → Γ.A₁) (σ₂ : ℝ → ℝ → Γ.A₁ → Γ.A₂)
    (hσ : Γ.IsOptimalStrategy E σ₁ σ₂) :
    ∃ (m : DirectMechanism τlo τhi θlo θhi) (σ₁' : ℝ → Set.Icc τlo τhi)
      (σ₂' : ℝ → ℝ → Set.Icc τlo τhi → Set.Icc θlo θhi),
      m.toDyn.IsOptimalStrategy E σ₁' σ₂' ∧
      (∀ τ ∈ Set.Icc τlo τhi, (σ₁' τ : ℝ) = τ) ∧
      (∀ τ (hτ : τ ∈ Set.Icc τlo τhi), ∀ θ ∈ Set.Icc θlo θhi, (σ₂' τ θ ⟨τ, hτ⟩ : ℝ) = θ) ∧
      (∀ τ ∈ Set.Icc τlo τhi, ∀ θ ∈ Set.Icc θlo θhi,
        m.q τ θ = Γ.prob (σ₁ τ) (σ₂ τ θ (σ₁ τ)) ∧ m.t τ θ = Γ.pay (σ₁ τ) (σ₂ τ θ (σ₁ τ))) := by
  have h1 : τlo ≤ τhi := E.τlo_lt_τhi.le
  have h2 : θlo ≤ θhi := E.θlo_lt_θhi.le
  let m : DirectMechanism τlo τhi θlo θhi :=
    ⟨fun τ θ => Γ.prob (σ₁ τ) (σ₂ τ θ (σ₁ τ)), fun τ θ => Γ.pay (σ₁ τ) (σ₂ τ θ (σ₁ τ))⟩
  -- utility equality of optimal responses
  have heq : ∀ τ ∈ Set.Icc τlo τhi, ∀ τ' ∈ Set.Icc τlo τhi, ∀ θ ∈ Set.Icc θlo θhi, ∀ a : Γ.A₁,
      θ * Γ.prob a (σ₂ τ θ a) - Γ.pay a (σ₂ τ θ a) =
        θ * Γ.prob a (σ₂ τ' θ a) - Γ.pay a (σ₂ τ' θ a) := by
    intro τ hτ τ' hτ' θ hθ a
    have := hσ.1 τ hτ θ hθ a (σ₂ τ' θ a)
    have := hσ.1 τ' hτ' θ hθ a (σ₂ τ θ a)
    linarith
  refine ⟨m, fun τ => Set.projIcc τlo τhi h1 τ, fun _ θ _ => Set.projIcc θlo θhi h2 θ,
    ⟨?_, ?_⟩, ?_, ?_, ?_⟩
  · intro τ hτ θ hθ a₁' a₂'
    rcases a₁' with ⟨a₁, ha₁⟩
    rcases a₂' with ⟨a₂, ha₂⟩
    show θ * Γ.prob (σ₁ a₁) (σ₂ a₁ a₂ (σ₁ a₁)) - Γ.pay (σ₁ a₁) (σ₂ a₁ a₂ (σ₁ a₁)) ≤
      θ * Γ.prob (σ₁ a₁) (σ₂ a₁ (Set.projIcc θlo θhi h2 θ) (σ₁ a₁)) -
        Γ.pay (σ₁ a₁) (σ₂ a₁ (Set.projIcc θlo θhi h2 θ) (σ₁ a₁))
    rw [Set.projIcc_of_mem h2 hθ]
    exact hσ.1 a₁ ha₁ θ hθ (σ₁ a₁) _
  · intro τ hτ a₁'
    rcases a₁' with ⟨a₁, ha₁⟩
    show ∫ θ in θlo..θhi, (θ * Γ.prob (σ₁ a₁) (σ₂ a₁ (Set.projIcc θlo θhi h2 θ) (σ₁ a₁)) -
        Γ.pay (σ₁ a₁) (σ₂ a₁ (Set.projIcc θlo θhi h2 θ) (σ₁ a₁))) * E.f θ τ ≤
      ∫ θ in θlo..θhi, (θ * Γ.prob (σ₁ (Set.projIcc τlo τhi h1 τ))
          (σ₂ (Set.projIcc τlo τhi h1 τ) (Set.projIcc θlo θhi h2 θ) (σ₁ (Set.projIcc τlo τhi h1 τ))) -
        Γ.pay (σ₁ (Set.projIcc τlo τhi h1 τ))
          (σ₂ (Set.projIcc τlo τhi h1 τ) (Set.projIcc θlo θhi h2 θ)
            (σ₁ (Set.projIcc τlo τhi h1 τ)))) * E.f θ τ
    rw [Set.projIcc_of_mem h1 hτ]
    have hc1 : ∫ θ in θlo..θhi, (θ * Γ.prob (σ₁ a₁) (σ₂ a₁ (Set.projIcc θlo θhi h2 θ) (σ₁ a₁)) -
        Γ.pay (σ₁ a₁) (σ₂ a₁ (Set.projIcc θlo θhi h2 θ) (σ₁ a₁))) * E.f θ τ =
        ∫ θ in θlo..θhi, (θ * Γ.prob (σ₁ a₁) (σ₂ τ θ (σ₁ a₁)) -
        Γ.pay (σ₁ a₁) (σ₂ τ θ (σ₁ a₁))) * E.f θ τ := by
      apply intervalIntegral.integral_congr
      intro θ hθ
      rw [Set.uIcc_of_le h2] at hθ
      simp only
      rw [Set.projIcc_of_mem h2 hθ, heq a₁ ha₁ τ hτ θ hθ]
    have hc2 : ∫ θ in θlo..θhi, (θ * Γ.prob (σ₁ τ)
          (σ₂ τ (Set.projIcc θlo θhi h2 θ) (σ₁ τ)) -
        Γ.pay (σ₁ τ) (σ₂ τ (Set.projIcc θlo θhi h2 θ) (σ₁ τ))) * E.f θ τ =
        ∫ θ in θlo..θhi, (θ * Γ.prob (σ₁ τ) (σ₂ τ θ (σ₁ τ)) -
        Γ.pay (σ₁ τ) (σ₂ τ θ (σ₁ τ))) * E.f θ τ := by
      apply intervalIntegral.integral_congr
      intro θ hθ
      rw [Set.uIcc_of_le h2] at hθ
      simp only
      rw [Set.projIcc_of_mem h2 hθ]
    rw [hc1, hc2]
    exact hσ.2 τ hτ (σ₁ a₁)
  · intro τ hτ
    simp [Set.projIcc_of_mem h1 hτ]
  · intro τ hτ θ hθ
    simp [Set.projIcc_of_mem h2 hθ]
  · intro τ _ θ _
    exact ⟨rfl, rfl⟩

end MechanismDesign.Dynamic

open MechanismDesign.Dynamic


theorem solution {τlo τhi θlo θhi : ℝ} (E : SeqEnv τlo τhi θlo θhi)
    (Γ : DynMechanism) (hΓ : Γ.Valid) (σ₁ : ℝ → Γ.A₁) (σ₂ : ℝ → ℝ → Γ.A₁ → Γ.A₂)
    (hσ : Γ.IsOptimalStrategy E σ₁ σ₂) :
    ∃ (m : DirectMechanism τlo τhi θlo θhi) (σ₁' : ℝ → Set.Icc τlo τhi)
      (σ₂' : ℝ → ℝ → Set.Icc τlo τhi → Set.Icc θlo θhi),
      m.toDyn.IsOptimalStrategy E σ₁' σ₂' ∧
      (∀ τ ∈ Set.Icc τlo τhi, (σ₁' τ : ℝ) = τ) ∧
      (∀ τ (hτ : τ ∈ Set.Icc τlo τhi), ∀ θ ∈ Set.Icc θlo θhi, (σ₂' τ θ ⟨τ, hτ⟩ : ℝ) = θ) ∧
      (∀ τ ∈ Set.Icc τlo τhi, ∀ θ ∈ Set.Icc θlo θhi,
        m.q τ θ = Γ.prob (σ₁ τ) (σ₂ τ θ (σ₁ τ)) ∧ m.t τ θ = Γ.pay (σ₁ τ) (σ₂ τ θ (σ₁ τ))) := by
  exact drp_core E Γ hΓ σ₁ σ₂ hσ
