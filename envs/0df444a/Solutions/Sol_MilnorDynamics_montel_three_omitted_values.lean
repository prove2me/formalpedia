-- Prove2me | solution 1 for MilnorDynamics.montel_three_omitted_values
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-30T18:02:41.607586+00:00
-- url     : https://prove2.me/submissions/22bc8f6b-abf5-4d97-ad0f-7a72467581db
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_MilnorDynamics_NormalFamilies
import Theorems.Thm_MilnorDynamics_montel_normalized_omitting_zero_one_infty
import Theorems.Thm_MilnorDynamics_montel_reduce_to_normalized

open scoped OnePoint
open Filter Set
open MilnorDynamics

/-- Theorem 3.7 (Montel): holomorphic maps omitting three distinct values are normal.
Reduction to the two published children: Mobius normalisation of the three omitted
values, then Montel's theorem for maps omitting `0, 1, ∞`. -/
theorem solution (U : Set ℂ) (hU : IsOpen U) (hUc : IsConnected U)
    (a b c : OnePoint ℂ) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (𝓕 : Set (ℂ → OnePoint ℂ))
    (h𝓕 : ∀ f ∈ 𝓕, IsHolomorphicOn U f ∧
      ∀ z ∈ U, f z ≠ a ∧ f z ≠ b ∧ f z ≠ c) :
    IsNormalFamily U 𝓕 := by
  obtain ⟨𝓖, h𝓖, hred⟩ := montel_reduce_to_normalized a b c hab hac hbc U 𝓕 h𝓕
  exact hred (montel_normalized_omitting_zero_one_infty U hU hUc 𝓖 h𝓖)
