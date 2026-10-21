-- Prove2me | solution 1 for HarmonicGames.Projection.lemma_2_1
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-20T21:13:53.309786+00:00
-- url     : https://prove2.me/submissions/ae1e4bae-a5c2-4001-9a7c-4c2a521d68a7

import Mathlib
import Definitions.Def_HarmonicGames_Projection_EpsEquilibrium

set_option autoImplicit false
open HarmonicGames.Projection

theorem solution {ι : Type} [Fintype ι] [DecidableEq ι] {E : ι → Type}
    [∀ m, Fintype (E m)] [∀ m, DecidableEq (E m)] [∀ m, Nonempty (E m)]
    (u û : ι → (∀ m, E m) → ℝ) (ϵ₀ : ℝ) (h : ∀ m p, |u m p - û m p| ≤ ϵ₀) :
    (∀ (ϵ₁ : ℝ) (p : ∀ m, E m), IsEpsEquilibrium û ϵ₁ p →
        IsEpsEquilibrium u (2 * ϵ₀ + ϵ₁) p) ∧
      (∀ (ϵ₁ : ℝ) (p : ∀ m, E m), IsEpsEquilibrium u ϵ₁ p →
        IsEpsEquilibrium û (2 * ϵ₀ + ϵ₁) p) := by
  constructor
  · intro ϵ₁ p hp m q
    have h1 := abs_le.mp (h m (Function.update p m q))
    have h2 := abs_le.mp (h m p)
    have h3 := hp m q
    linarith [h1.1, h1.2, h2.1, h2.2]
  · intro ϵ₁ p hp m q
    have h1 := abs_le.mp (h m (Function.update p m q))
    have h2 := abs_le.mp (h m p)
    have h3 := hp m q
    linarith [h1.1, h1.2, h2.1, h2.2]
