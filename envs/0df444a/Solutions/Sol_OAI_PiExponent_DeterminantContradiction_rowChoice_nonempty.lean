-- Prove2me | solution 1 for OAI.PiExponent.DeterminantContradiction.rowChoice_nonempty
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-24T06:45:33.361603+00:00
-- url     : https://prove2.me/submissions/f0bee505-87f3-4715-81a4-06300e5e2ca4

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
    {nu : ℝ} (d : FixedData nu) {H : ℝ} (r : Row d H) :
    Nonempty (RowChoice d H r) := by
  classical
  have hH : 0 ≤ H := by
    have := S106RC.row_bound d r
    have h2 : 0 ≤ (d.v0 : ℝ) * (r.2.1 0 : ℝ) := mul_nonneg d.v0_pos.le (Nat.cast_nonneg _)
    linarith
  have h0 : (0 : Fin d.m → ℕ) ∈ realWeightedSimplex (fixedWeights d) H := by
    simp only [realWeightedSimplex, Finset.mem_filter, Fintype.mem_piFinset, Finset.mem_range,
      Pi.zero_apply, Nat.cast_zero, mul_zero, Finset.sum_const_zero]
    exact ⟨fun _ => Nat.succ_pos _, hH⟩
  have hT : Finsupp.equivFunOnFinite.symm (0 : Fin d.m → ℕ) ∈ transverseIndices (fixedWeights d) H := by
    simp only [transverseIndices, Finset.mem_map, Equiv.coe_toEmbedding]
    exact ⟨0, h0, rfl⟩
  exact ⟨⟨⟨_, hT⟩, fun _ => ⟨0, Nat.succ_pos _⟩, ⟨0, Nat.succ_pos _⟩⟩⟩
