-- Prove2me | solution 1 for ImpulseNMFG.Verification.eq_2_19_2_21
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-21T09:06:58.816567+00:00
-- url     : https://prove2.me/submissions/ca31a435-0b90-44d2-8e62-145d698365da

import Mathlib
import Definitions.Def_ImpulseNMFG_Verification_Game
import Definitions.Def_ImpulseNMFG_Verification_QVI
set_option autoImplicit false

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal
open ImpulseGames.Verification (State IsBrownianBasis)
open ImpulseNMFG.Verification

theorem solution {N d M : ℕ} [NeZero N] (G : Game N d M)
    (V : Fin N → State d → ℝ) (ξ : (i : Fin N) → State d → G.Imp i)
    (h210 : ∀ i, IsUniqueMinimizer G V ξ i)
    (hi : ∀ i, SolvesQVI G V ξ i) :
    (∀ i, ∀ y ∈ commonWait G V ξ i \ frontier (waitRegion G V ξ i),
      -G.f i y ≤ ImpulseGames.Verification.generator G.b G.σ (V i) y -
        G.ρ i * V i y) ∧
    (∀ i, ∀ y ∈ G.S, ∀ z ∈ G.Z i,
      V i y ≤ ownOp G V ξ i y ∧
      ownOp G V ξ i y ≤ V i (G.Γ i y z) + G.φ i y z) ∧
    (∀ i j, i ≠ j → ∀ y ∈ G.S,
      ownOp G V ξ j y - V j y = 0 →
      V i y = crossOp G V ξ i j y) := by
  refine ⟨?_, ?_, ?_⟩
  · intro i y hy
    have h := (hi i).2.2.2 y hy
    have h1 := (min_eq_iff.mp h)
    have : 0 ≤ ImpulseGames.Verification.generator G.b G.σ (V i) y - G.ρ i * V i y + G.f i y := by
      rcases h1 with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · linarith
      · linarith
    linarith
  · intro i y hy z hz
    refine ⟨?_, ?_⟩
    · have := (hi i).2.1 i y hy
      linarith
    · by_cases hzξ : z = ξ i y
      · subst hzξ; simp [ownOp]
      · exact le_of_lt ((h210 i y hy).2 z hz hzξ)
  · intro i j hij y hy h
    have := (hi i).2.2.1 j (Ne.symm hij) y hy h
    linarith
