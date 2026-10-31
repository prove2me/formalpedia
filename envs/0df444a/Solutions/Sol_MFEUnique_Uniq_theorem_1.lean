-- Prove2me | solution 1 for MFEUnique.Uniq.theorem_1
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-30T21:23:38.389799+00:00
-- url     : https://prove2.me/submissions/ae884237-2eb5-4e32-a1fe-efd1f995efeb

import Mathlib
import Definitions.Def_MFEUnique_Uniq_Equilibrium
import Theorems.Thm_MFEUnique_Uniq_sd_of_mfe_rel
import Theorems.Thm_MFEUnique_Uniq_strategy_eq_of_equiv

open MeasureTheory
open MFEUnique.Uniq

theorem solution {X : Type*} [MetricSpace X] [CompactSpace X] [PartialOrder X]
    [OrderClosedTopology X] [MeasurableSpace X] [BorelSpace X]
    {q J : ℕ} {A : Set (EuclideanSpace ℝ (Fin q))} {E : Type*} [TopologicalSpace E]
    (G : Game X q J E A) (hG : G.Standing)
    (R : ProbabilityMeasure X → ProbabilityMeasure X → Prop) (hR : G.RelStanding R)
    (hagree : AgreesSD R) (hcomplete : IsComplete R)
    (g : X → ProbabilityMeasure X → A) (hg : ∀ x s, g x s ∈ G.Gopt x s)
    (hsingle : ∀ x s a, a ∈ G.Gopt x s → a = g x s)
    (herg : G.IsXErgodic g) (hinc : G.IncreasingInX g) (hdec : G.DecreasingInS R g) :
    ∀ (g₁ g₂ : X → ProbabilityMeasure X → A) (s₁ s₂ : ProbabilityMeasure X),
      G.IsMFE g₁ s₁ → G.IsMFE g₂ s₂ → s₁ = s₂ := by
  have hfix : ∀ (g' : X → ProbabilityMeasure X → A) (s : ProbabilityMeasure X),
      G.IsMFE g' s → G.Mop g s (s : Measure X) = s := by
    intro g' s h
    have heq : ∀ x, g' x s = g x s := fun x => hsingle x s _ (h.1 x)
    have : G.Mop g' s = G.Mop g s := by
      funext θ; simp only [Game.Mop, heq]
    rw [← this]; exact h.2
  have key : ∀ (a b : ProbabilityMeasure X) (ga gb : X → ProbabilityMeasure X → A),
      G.IsMFE ga a → G.IsMFE gb b → R b a → a = b := by
    intro a b ga gb ha hb hba
    -- Step 1: `a ⪰SD b`, hence `a ⪰ b`, so `a ∼ b`.
    have hsd := sd_of_mfe_rel G hG R g hg hsingle herg hinc hdec ga gb a b ha hb hba
    have hab : R a b := hagree a b hsd
    -- Step 2: the strategies and the transitions agree at `a` and `b`.
    have heq := strategy_eq_of_equiv G hG R hR g hg hsingle a b hab hba
    have hw := (hR a b hba hab).2
    have hM : G.Mop g a = G.Mop g b := by
      funext θ; simp only [Game.Mop, heq, hw]
    -- Step 3: both are invariant for `M_a`, which has a unique invariant measure.
    obtain ⟨μ, -, huniq, -⟩ := herg a
    have h1 : a = μ := huniq a (hfix ga a ha)
    have h2 : b = μ := huniq b (by rw [hM]; exact hfix gb b hb)
    rw [h1, h2]
  intro g₁ g₂ s₁ s₂ h₁ h₂
  rcases hcomplete s₁ s₂ with h | h
  · exact (key s₂ s₁ g₂ g₁ h₂ h₁ h).symm
  · exact key s₁ s₂ g₁ g₂ h₁ h₂ h
