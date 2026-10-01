-- Prove2me | solution 2 for MilnorDynamics.montel_three_omitted_values
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-30T18:03:12.66448+00:00
-- url     : https://prove2.me/submissions/0d2935a3-a481-4053-8632-6a8e4a90c75b
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_MilnorDynamics_NormalFamilies
import Theorems.Thm_MilnorDynamics_montel_normalized_omitting_zero_one_infty
import Theorems.Thm_MilnorDynamics_montel_reduce_to_normalized

open scoped OnePoint
open Filter Set
open MilnorDynamics

/-- Variant 3: no auxiliary declaration; the normalised core is named with an
explicit `have` binding and the normalisation child is applied through
`obtain`, then the transport implication closes the goal. -/
theorem solution (U : Set ℂ) (hU : IsOpen U) (hUc : IsConnected U)
    (a b c : OnePoint ℂ) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (𝓕 : Set (ℂ → OnePoint ℂ))
    (h𝓕 : ∀ f ∈ 𝓕, IsHolomorphicOn U f ∧
      ∀ z ∈ U, f z ≠ a ∧ f z ≠ b ∧ f z ≠ c) :
    IsNormalFamily U 𝓕 := by
  obtain ⟨𝓖, h𝓖, hnorm⟩ :=
    montel_reduce_to_normalized a b c hab hac hbc U 𝓕 h𝓕
  have hcore : IsNormalFamily U 𝓖 :=
    montel_normalized_omitting_zero_one_infty U hU hUc 𝓖 h𝓖
  exact hnorm hcore
