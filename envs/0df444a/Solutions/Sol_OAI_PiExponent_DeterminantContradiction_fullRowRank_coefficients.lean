-- Prove2me | solution 1 for OAI.PiExponent.DeterminantContradiction.fullRowRank_coefficients
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-24T02:25:38.908984+00:00
-- url     : https://prove2.me/submissions/803471ed-4c11-44f6-adab-13860ff8094b

import Mathlib

theorem solution
    {α β : Type} [Fintype α] [Fintype β]
    (M : Matrix α β ℂ)
    (hrows : LinearIndependent ℂ (fun a : α => M a)) :
    ∀ y : α → ℂ, ∃ c : β → ℂ, ∀ a : α,
      ∑ b : β, c b * M a b = y a := by
  classical
  have hr : M.rank = Fintype.card α := LinearIndependent.rank_matrix (M := M) hrows
  have htop : LinearMap.range M.mulVecLin = ⊤ := by
    apply Submodule.eq_top_of_finrank_eq
    rw [Module.finrank_fintype_fun_eq_card]
    exact hr
  intro y
  obtain ⟨c, hc⟩ := LinearMap.range_eq_top.1 htop y
  refine ⟨c, fun a => ?_⟩
  have := congrFun hc a
  rw [Matrix.mulVecLin_apply, Matrix.mulVec, dotProduct] at this
  rw [← this]
  exact Finset.sum_congr rfl (fun b _ => mul_comm _ _)
