-- Prove2me | solution 1 for LogicBenders.Generic.theorem_1
-- status  : ACCEPTED   (prove)
-- author  : @arexychen
-- created : 2026-10-13T02:02:37.82019+00:00
-- url     : https://prove2.me/submissions/7dc93ee4-2631-4e72-a90e-12f60fa3a928

import Definitions.Def_LogicBenders_Generic_Setting
import Mathlib
import Theorems.Thm_LogicBenders_Generic_subVal_upper_bound
import Theorems.Thm_LogicBenders_Generic_master_lower_bound
import Theorems.Thm_LogicBenders_Generic_beta_star_eq_zbar
import Theorems.Thm_LogicBenders_Generic_infeasible_of_master_infeasible
import Theorems.Thm_LogicBenders_Generic_unbounded_of_dual_infeasible

open LogicBenders.Generic

theorem solution {X Y : Type*} (S : Set (X × Y)) (f : X → Y → ℝ) (r : Run Y) (N : ℕ) :
    -- (i) termination with a finite optimal solution `(z̄, ȳ)` of the master problem
    (StopsAtWhile S f r N →
      (∀ k < N, ValidCut S f (r.cut k)) →
      r.zbar N ≠ ⊥ →
      -- attainment of the subproblem (7) at the terminal `ȳ` when its value is finite
      -- (asserted in the proof on p. 9: "some optimal solution x̄")
      (subVal S f (r.ybar N) ≠ ⊤ → subVal S f (r.ybar N) ≠ ⊥ →
        ∃ x : X, (x, r.ybar N) ∈ S ∧ (f x (r.ybar N) : EReal) = subVal S f (r.ybar N)) →
      ∃ xbar : X, (xbar, r.ybar N) ∈ S ∧ (f xbar (r.ybar N) : EReal) = r.zbar N ∧
        ∀ (x : X) (y : Y), (x, y) ∈ S → f xbar (r.ybar N) ≤ f x y) ∧
    -- (ii) termination with an infeasible master problem
    (StopsAtMaster S f r N →
      (∀ k ≤ N, ValidCut S f (r.cut k)) →
      S = ∅) ∧
    -- (iii) termination with an infeasible subproblem dual
    (StopsAtWhile S f r N →
      (∀ k < N, ValidCut S f (r.cut k)) →
      (¬ ∃ β : ℝ, IsDualFeasible S f (r.ybar N) (β : EReal)) →
      IsUnbounded S f) := by
  refine ⟨?_, ?_, ?_⟩
  · intro hs hvalid hn hatt
    cases N with
    | zero => exact (hn hs.1.1).elim
    | succ k =>
      have hm := (hs.1.2 k (Nat.lt_succ_self k)).2
      have hv : ∀ j ≤ k, ValidCut S f (r.cut j) := by
        intro j hj
        exact hvalid j (Nat.lt_succ_of_le hj)
      have heq := (beta_star_eq_zbar S f r.cut k hv (r.zbar (k+1))
        (r.ybar (k+1)) hm hs.2).2
      have hlo := master_lower_bound S f r.cut k hv (r.zbar (k+1))
        (r.ybar (k+1)) hm
      have hup := subVal_upper_bound S f (r.ybar (k+1))
      rw [heq] at hup
      have hopt : optVal S f = r.zbar (k+1) := le_antisymm hup hlo
      obtain ⟨xbar, hxb, hxf⟩ := hatt (by rw [heq]; exact ne_of_lt hm.2.1)
        (by rw [heq]; exact hn)
      refine ⟨xbar, hxb, hxf.trans heq, ?_⟩
      intro x y hxy
      apply EReal.coe_le_coe_iff.mp
      rw [hxf, heq, ← hopt]
      exact iInf_le_of_le (x,y) (iInf_le_of_le hxy le_rfl)
  · intro hs hvalid
    exact infeasible_of_master_infeasible S f r.cut N hvalid hs.2.2
  · intro _ _ hdual
    exact (unbounded_of_dual_infeasible S f (r.ybar N) hdual).2
