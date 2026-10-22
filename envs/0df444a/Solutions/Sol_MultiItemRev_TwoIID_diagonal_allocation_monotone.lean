-- Prove2me | solution 1 for MultiItemRev.TwoIID.diagonal_allocation_monotone
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T08:36:57.075215+00:00
-- url     : https://prove2.me/submissions/6f7a26ec-8173-4c16-a728-29c0b6423912

import Mathlib
import Definitions.Def_MultiItemRev_TwoIID_Model

set_option autoImplicit false
open MeasureTheory
open scoped NNReal ENNReal
open MultiItemRev.TwoIID

theorem solution
    (M : MultiItemRev.Decomp.Mechanism (Fin 2))
    (hFeas : MultiItemRev.Decomp.IsFeasible M)
    (hIC : MultiItemRev.Decomp.IsIC M)
    (hSym : IsSymmetric M) :
    Monotone (fun t => M.q (diag t) 0) ∧
      ∀ t, 0 ≤ M.q (diag t) 0 ∧ M.q (diag t) 0 ≤ 1 := by
  refine ⟨?_, fun t => hFeas _ _⟩
  have hq : ∀ s : ℝ≥0, M.q (diag s) 1 = M.q (diag s) 0 := by
    intro s
    have h := (hSym (diag s)).1
    have e : swap2 (diag s) = diag s := by
      funext i
      simp [swap2, diag]
    rw [e] at h
    exact h.symm
  intro t t' htt'
  show M.q (diag t) 0 ≤ M.q (diag t') 0
  rcases htt'.eq_or_lt with h | hlt
  · rw [h]
  · have hr : (t : ℝ) < t' := by exact_mod_cast hlt
    have h1 := hIC (diag t) (diag t')
    have h2 := hIC (diag t') (diag t)
    simp only [MultiItemRev.Decomp.buyerPayoff, Fin.sum_univ_two, hq] at h1 h2
    simp only [diag] at h1 h2
    by_contra hcon
    push_neg at hcon
    nlinarith
