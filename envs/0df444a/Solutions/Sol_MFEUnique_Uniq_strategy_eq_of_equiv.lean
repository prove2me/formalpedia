-- Prove2me | solution 1 for MFEUnique.Uniq.strategy_eq_of_equiv
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-30T21:17:23.197714+00:00
-- url     : https://prove2.me/submissions/ead04a20-2a4a-481f-a042-4c4b6bc31e4d

import Mathlib
import Definitions.Def_MFEUnique_Uniq_Equilibrium

open MeasureTheory
open MFEUnique.Uniq

theorem solution {X : Type*} [MetricSpace X] [CompactSpace X] [MeasurableSpace X]
    [BorelSpace X]
    {q J : ℕ} {A : Set (EuclideanSpace ℝ (Fin q))} {E : Type*} [TopologicalSpace E]
    (G : Game X q J E A) (hG : G.Standing)
    (R : ProbabilityMeasure X → ProbabilityMeasure X → Prop) (hR : G.RelStanding R)
    (g : X → ProbabilityMeasure X → A) (hg : ∀ x s, g x s ∈ G.Gopt x s)
    (hsingle : ∀ x s a, a ∈ G.Gopt x s → a = g x s)
    (s₁ s₂ : ProbabilityMeasure X) (h₁₂ : R s₁ s₂) (h₂₁ : R s₂ s₁) :
    ∀ x : X, g x s₁ = g x s₂ := by
  obtain ⟨hpay, hw⟩ := hR s₁ s₂ h₂₁ h₁₂
  have hhist : ∀ (σ : Strategy X A) (x : X) (t : ℕ),
      G.hist σ x s₁ t = G.hist σ x s₂ t := by
    intro σ x t
    induction t with
    | zero => rfl
    | succ t ih =>
      funext j
      simp only [Game.hist, ih, hw]
  have hpayoff : ∀ (σ : Strategy X A) (x : X), G.payoff σ x s₁ = G.payoff σ x s₂ := by
    intro σ x
    simp only [Game.payoff, hhist, hpay]
  have hV : ∀ x, G.V x s₁ = G.V x s₂ := by
    intro x
    simp only [Game.V, hpayoff]
  have hB : ∀ x a, G.bellmanRHS x a s₁ = G.bellmanRHS x a s₂ := by
    intro x a
    simp only [Game.bellmanRHS, hpay, hw, hV]
  have hGopt : ∀ x, G.Gopt x s₁ = G.Gopt x s₂ := by
    intro x
    simp only [Game.Gopt, hB]
  intro x
  exact hsingle x s₂ (g x s₁) (hGopt x ▸ hg x s₁)
