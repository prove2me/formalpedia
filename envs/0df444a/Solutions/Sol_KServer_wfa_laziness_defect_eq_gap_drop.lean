-- Prove2me | solution 1 for KServer.wfa_laziness_defect_eq_gap_drop
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-08-31T22:40:19.329905+00:00
-- url     : https://prove2.me/submissions/872b2d14-fe88-413c-a067-e83f171be837

import Mathlib
import Definitions.Def_KServer_workfunctionU
import Theorems.Thm_KServer_workFn_rec_ge
import Theorems.Thm_KServer_workFn_covered
import Definitions.Def_KServer_work_function
import Theorems.Thm_KServer_workFn_lipschitz
import Theorems.Thm_KServer_workFn_nil

open KServer

private theorem wf_eq {k : ℕ} {M : Type} [MetricSpace M] (C₀ : Config k M) (σ : List M)
    (X : Config k M) : workFunction C₀ σ X = workFn C₀ σ X := rfl

/-- The Work Function Algorithm's move is exactly what the update operator charges. -/
private theorem wfa_step_eq (k : ℕ) (hk : 1 ≤ k) (M : Type) [MetricSpace M] [Fintype M]
    (C₀ : Config k M) (l : List M) (Cprev : Config k M) (r : M) :
    workFn C₀ (l ++ [r]) Cprev
      = workFn C₀ (l ++ [r]) (wfaStep hk C₀ l Cprev r)
        + moveCost Cprev (wfaStep hk C₀ l Cprev r) := by
  refine le_antisymm ?_ ?_
  · have h := workFn_lipschitz k hk M C₀ (l ++ [r]) Cprev (wfaStep hk C₀ l Cprev r)
    have hc : moveCost (wfaStep hk C₀ l Cprev r) Cprev
        = moveCost Cprev (wfaStep hk C₀ l Cprev r) := by
      unfold moveCost
      exact Finset.sum_congr rfl fun i _ => dist_comm _ _
    linarith [h, hc.symm ▸ h]
  · obtain ⟨i, hi⟩ := workFn_rec_ge k hk M C₀ l r Cprev
    have hcov : ∃ j, (Function.update Cprev i r) j = r := ⟨i, Function.update_self _ _ _⟩
    have hc := workFn_covered k hk M C₀ l r (Function.update Cprev i r) hcov
    have hmin := wfaStep_min hk C₀ l Cprev r (Function.update Cprev i r) hcov
    have hmc : moveCost Cprev (Function.update Cprev i r) = dist r (Cprev i) := by
      unfold moveCost
      rw [Finset.sum_eq_single i]
      · rw [Function.update_self]; exact dist_comm _ _
      · intro j _ hj; rw [Function.update_of_ne hj, dist_self]
      · intro h; exact absurd (Finset.mem_univ i) h
    rw [wf_eq, wf_eq] at hmin
    rw [← hc] at hi
    linarith

/-- **The laziness defect of the Work Function Algorithm is the drop of the labelling gap.** -/
theorem solution (k : ℕ) (hk : 0 < k) (M : Type) [MetricSpace M] [Fintype M]
    (C₀ : Config k M) (σ : List M) (t : ℕ) (ht : t < σ.length) :
    moveCost ((WFA hk C₀).conf (σ.take t)) ((WFA hk C₀).conf (σ.take (t + 1)))
        - (workFnU C₀ (σ.take (t + 1)) ((WFA hk C₀).conf (σ.take t))
           - workFnU C₀ (σ.take (t + 1)) ((WFA hk C₀).conf (σ.take (t + 1))))
      = (workFunction C₀ (σ.take (t + 1)) ((WFA hk C₀).conf (σ.take t))
          - workFnU C₀ (σ.take (t + 1)) ((WFA hk C₀).conf (σ.take t)))
        - (workFunction C₀ (σ.take (t + 1)) ((WFA hk C₀).conf (σ.take (t + 1)))
          - workFnU C₀ (σ.take (t + 1)) ((WFA hk C₀).conf (σ.take (t + 1)))) := by
  classical
  have hsplit : σ.take (t + 1) = σ.take t ++ [σ[t]'ht] := by
    rw [List.take_succ, List.getElem?_eq_getElem ht]
    rfl
  have hSsucc : (WFA hk C₀).conf (σ.take (t + 1))
      = wfaStep hk C₀ (σ.take t) ((WFA hk C₀).conf (σ.take t)) (σ[t]'ht) := by
    show (wfaAux hk C₀ (σ.take (t + 1))).2
        = wfaStep hk C₀ (σ.take t) ((wfaAux hk C₀ (σ.take t)).2) (σ[t]'ht)
    rw [hsplit, wfaAux_append hk C₀ (σ.take t) (σ[t]'ht), wfaAux_fst]
  have hstep : workFn C₀ (σ.take (t + 1)) ((WFA hk C₀).conf (σ.take t))
      = workFn C₀ (σ.take (t + 1)) ((WFA hk C₀).conf (σ.take (t + 1)))
        + moveCost ((WFA hk C₀).conf (σ.take t)) ((WFA hk C₀).conf (σ.take (t + 1))) := by
    rw [hSsucc, hsplit]
    exact wfa_step_eq k hk M C₀ (σ.take t) ((WFA hk C₀).conf (σ.take t)) (σ[t]'ht)
  have he : workFunction C₀ (σ.take (t + 1)) ((WFA hk C₀).conf (σ.take t))
      = workFunction C₀ (σ.take (t + 1)) ((WFA hk C₀).conf (σ.take (t + 1)))
        + moveCost ((WFA hk C₀).conf (σ.take t)) ((WFA hk C₀).conf (σ.take (t + 1))) := hstep
  linarith
