-- Prove2me | solution 1 for MatousekLP.Integrality.vertex_cover_lp_rounding
-- status  : ACCEPTED   (prove)
-- author  : @moona3k
-- created : 2026-10-05T03:55:31.469732+00:00
-- url     : https://prove2.me/submissions/53390b31-b6fd-4032-ba13-4e8475d16401

import Definitions.Def_MatousekLP_Integrality_VertexCoverLP
import Mathlib

open MatousekLP.Integrality

theorem solution {V : Type*} [Fintype V] (G : SimpleGraph V)
    (xstar : V → ℝ) (hx : IsVCRelaxOptimal G xstar)
    (SOPT : Finset V) (hcov : G.IsVertexCover (SOPT : Set V))
    (hmin : ∀ C : Finset V, G.IsVertexCover (C : Set V) → SOPT.card ≤ C.card) :
    G.IsVertexCover {v | 1 / 2 ≤ xstar v} ∧
      (Finset.univ.filter (fun v => 1 / 2 ≤ xstar v)).card ≤ 2 * SOPT.card := by
  classical
  obtain ⟨⟨hedge, hbox⟩, hopt⟩ := hx
  refine ⟨fun u v huv => ?_, ?_⟩
  · have := hedge u v huv
    by_contra h
    push_neg at h
    simp only [Set.mem_setOf_eq, not_le] at h
    linarith [h.1, h.2]
  · -- the indicator of SOPT is feasible for the relaxation
    set y : V → ℝ := fun v => if v ∈ SOPT then 1 else 0
    have hy : IsVCRelaxFeasible G y := by
      refine ⟨fun u v huv => ?_, fun v => ?_⟩
      · rcases hcov huv with h | h
        · have : y u = 1 := by simp [y, Finset.mem_coe.mp h]
          have : 0 ≤ y v := by simp only [y]; split_ifs <;> norm_num
          linarith
        · have : y v = 1 := by simp [y, Finset.mem_coe.mp h]
          have : 0 ≤ y u := by simp only [y]; split_ifs <;> norm_num
          linarith
      · simp only [y]; split_ifs <;> norm_num
    have hsum : ∑ v, xstar v ≤ SOPT.card := by
      have := hopt y hy
      simpa [y, Finset.sum_ite_mem, Finset.univ_inter] using this
    set H := Finset.univ.filter (fun v => 1 / 2 ≤ xstar v)
    have hH : (H.card : ℝ) ≤ 2 * ∑ v, xstar v := by
      calc (H.card : ℝ) = ∑ v ∈ H, (1 : ℝ) := by simp
        _ ≤ ∑ v ∈ H, 2 * xstar v := Finset.sum_le_sum fun v hv => by
            have := (Finset.mem_filter.mp hv).2; linarith
        _ ≤ ∑ v, 2 * xstar v := Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
            fun v _ _ => by linarith [(hbox v).1]
        _ = 2 * ∑ v, xstar v := by rw [Finset.mul_sum]
    have : (H.card : ℝ) ≤ 2 * SOPT.card := by linarith
    exact_mod_cast this
