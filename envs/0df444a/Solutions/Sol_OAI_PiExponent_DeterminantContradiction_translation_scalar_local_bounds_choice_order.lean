-- Prove2me | solution 1 for OAI.PiExponent.DeterminantContradiction.translation_scalar_local_bounds_choice_order
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-24T06:46:00.302786+00:00
-- url     : https://prove2.me/submissions/b7c69e16-2a00-49a2-9876-8c90cb3e21f2

import Definitions.Def_OAI_PiExponent_MinorTranslationData
import Mathlib

open OAI.PiExponent OAI.PiExponent.DeterminantContradiction OAI.PiExponent.MinorTranslationData
open scoped BigOperators

namespace S106RC

lemma row_bound {nu : ℝ} (d : FixedData nu) {H : ℝ} (r : Row d H) :
    (d.v0 : ℝ) * (r.2.1 0 : ℝ) < H := by
  have h := r.2.2
  simp only [strictWeightedSimplex, Finset.mem_filter] at h
  have hs := h.2
  rw [Fin.sum_univ_succ] at hs
  have hnn : 0 ≤ ∑ i : Fin d.m, InterpolationMatrix.rowWeights (d.v0 : ℝ) (d.base.theta : ℝ)
      (MatrixArithmetic.logWeights (finiteDenominators d)) i.succ * (r.2.1 i.succ : ℝ) := by
    refine Finset.sum_nonneg fun i _ => mul_nonneg ?_ (Nat.cast_nonneg _)
    simp only [InterpolationMatrix.rowWeights, Fin.cases_succ, MatrixArithmetic.logWeights]
    exact div_nonneg (Nat.cast_nonneg _) d.base.theta_pos.le
  simp only [InterpolationMatrix.rowWeights, Fin.cases_zero, Fin.cases_succ] at hs hnn
  linarith

end S106RC

theorem solution
    {nu : ℝ} (d : FixedData nu) {H : ℝ}
    (r : Row d H) (t : RowChoice d H r) :
    (t.2.2 : ℝ) ≤ H / (d.v0 : ℝ) := by
  have h := S106RC.row_bound d r
  have ht : (t.2.2 : ℕ) ≤ r.2.1 0 := Nat.lt_succ_iff.mp t.2.2.isLt
  rw [le_div_iff₀ d.v0_pos]
  have : ((t.2.2 : ℕ) : ℝ) ≤ (r.2.1 0 : ℝ) := by exact_mod_cast ht
  nlinarith [d.v0_pos]
