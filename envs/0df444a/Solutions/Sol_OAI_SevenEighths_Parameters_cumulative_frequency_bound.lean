-- Prove2me | solution 1 for OAI.SevenEighths.Parameters.cumulative_frequency_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T23:18:33.707197+00:00
-- url     : https://prove2.me/submissions/fc7b0223-f54b-4841-a5ae-ee9012c8535e

import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Algebra.Order.Archimedean.Basic
import Mathlib.Analysis.Complex.Norm
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp
import Definitions.Def_OAI_NumberTheory_DirichletL_Parameters

set_option autoImplicit false
open OAI
open OAI.SevenEighths OAI.SevenEighths.Parameters
namespace OAI.SevenEighths.Parameters
theorem _root_.solution {ι : Type*} (s : Finset ι)
    (frequency : ι → ℝ) {T : ℝ} (hT : 0 ≤ T)
    (hfreq : ∀ i ∈ s, |frequency i| ≤ T / (4 * s.card)) :
    |∑ i ∈ s, frequency i| ≤ T / 4 := by
  by_cases hs : s.card = 0
  · have he : s = ∅ := Finset.card_eq_zero.mp hs
    simp only [he, Finset.sum_empty, abs_zero]
    positivity
  · have hc : (s.card : ℝ) ≠ 0 := by exact_mod_cast hs
    calc
      |∑ i ∈ s, frequency i| ≤ ∑ i ∈ s, |frequency i| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _i ∈ s, T / (4 * s.card) := Finset.sum_le_sum hfreq
      _ = T / 4 := by simp only [Finset.sum_const, nsmul_eq_mul]; field_simp
end OAI.SevenEighths.Parameters
