-- Prove2me | solution 1 for OAI.PiExponent.DeterminantContradiction.FiniteTranslation.log_majorant_composition_reciprocal_sum_bound
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-18T18:23:39.281082+00:00
-- url     : https://prove2.me/submissions/2fb47e45-c82e-4ff1-aec9-950fa6ad06f3

import Definitions.Def_OAI_PiExponent_FiniteActualTranslation
import Definitions.Def_OAI_PiExponent_logMajorantCompositions

open scoped BigOperators
open OAI.PiExponent OAI.PiExponent.DeterminantContradiction
open OAI.PiExponent.DeterminantContradiction.FiniteTranslation

theorem solution (q k : ℕ) :
    ‖(∑ a ∈ logMajorantCompositions q k, ∏ i : Fin q, ((a i : ℂ)⁻¹))‖ ≤
      ((logMajorantCompositions q k).card : ℝ) := by
  classical
  let S := logMajorantCompositions q k
  have hpos (a : Fin q → ℕ) (ha : a ∈ S) (i : Fin q) : 0 < a i := by
    have hm : a ∈
        (((Finset.univ : Finset (Fin q → Fin (k + 1))).image
          (fun b i => (b i : ℕ))).filter
          (fun b => (∀ i, 0 < b i) ∧ ∑ i : Fin q, b i = k)) := by
      simpa [S, logMajorantCompositions] using ha
    exact (Finset.mem_filter.mp hm).2.1 i
  have hterm (a : Fin q → ℕ) (ha : a ∈ S) :
      ‖∏ i : Fin q, ((a i : ℂ)⁻¹)‖ ≤ 1 := by
    rw [norm_prod]
    apply Finset.prod_le_one
    · intro i hi
      exact norm_nonneg _
    · intro i hi
      rw [norm_inv, Complex.norm_natCast]
      have hp : (0 : ℝ) < (a i : ℝ) := Nat.cast_pos.mpr (hpos a ha i)
      have hle : (1 : ℝ) ≤ (a i : ℝ) := by
        exact_mod_cast (Nat.succ_le_of_lt (hpos a ha i))
      exact (inv_le_one₀ hp).2 hle
  calc
    ‖∑ a ∈ S, ∏ i : Fin q, ((a i : ℂ)⁻¹)‖ ≤
        ∑ a ∈ S, ‖∏ i : Fin q, ((a i : ℂ)⁻¹)‖ := norm_sum_le _ _
    _ ≤ ∑ _a ∈ S, (1 : ℝ) := by
      apply Finset.sum_le_sum
      intro a ha
      exact hterm a ha
    _ = (S.card : ℝ) := by simp [S]