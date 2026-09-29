-- Prove2me | solution 1 for KServer.wfa_trajectory_identity
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-08-31T21:37:20.791718+00:00
-- url     : https://prove2.me/submissions/4b5bfd16-1051-4d57-acaf-2ebac812cff3

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

/-- **The trajectory identity for the Work Function Algorithm.** -/
theorem solution (k : ℕ) (hk : 0 < k) (M : Type) [MetricSpace M] [Fintype M]
    (C₀ : Config k M) (σ : List M) :
    (WFA hk C₀).cost σ + workFunction C₀ σ ((WFA hk C₀).conf σ)
      = ∑ t ∈ Finset.range σ.length,
          (workFunction C₀ (σ.take (t + 1)) ((WFA hk C₀).conf (σ.take t))
            - workFunction C₀ (σ.take t) ((WFA hk C₀).conf (σ.take t))) := by
  classical
  set S : ℕ → Config k M := fun t => (WFA hk C₀).conf (σ.take t) with hSdef
  set f : ℕ → ℝ := fun t => workFn C₀ (σ.take t) (S t) with hfdef
  have hsplit : ∀ (t : ℕ) (ht : t < σ.length), σ.take (t + 1) = σ.take t ++ [σ[t]'ht] := by
    intro t ht
    rw [List.take_succ, List.getElem?_eq_getElem ht]
    rfl
  have hSsucc : ∀ (t : ℕ) (ht : t < σ.length),
      S (t + 1) = wfaStep hk C₀ (σ.take t) (S t) (σ[t]'ht) := by
    intro t ht
    show (wfaAux hk C₀ (σ.take (t + 1))).2
        = wfaStep hk C₀ (σ.take t) ((wfaAux hk C₀ (σ.take t)).2) (σ[t]'ht)
    rw [hsplit t ht, wfaAux_append hk C₀ (σ.take t) (σ[t]'ht), wfaAux_fst]
  have hstep : ∀ (t : ℕ) (ht : t < σ.length),
      workFn C₀ (σ.take (t + 1)) (S t)
        = workFn C₀ (σ.take (t + 1)) (S (t + 1)) + moveCost (S t) (S (t + 1)) := by
    intro t ht
    rw [hSsucc t ht]
    rw [hsplit t ht]
    exact wfa_step_eq k hk M C₀ (σ.take t) (S t) (σ[t]'ht)
  -- each step's movement equals (f t + growth t) - f (t+1)
  have hterm : ∀ t ∈ Finset.range σ.length,
      moveCost (S t) (S (t + 1))
        = (workFn C₀ (σ.take (t + 1)) (S t) - f t) + (f t - f (t + 1)) := by
    intro t htm
    have ht : t < σ.length := Finset.mem_range.mp htm
    have h1 := hstep t ht
    rw [hfdef]
    simp only
    linarith
  have hcost : (WFA hk C₀).cost σ
      = ∑ t ∈ Finset.range σ.length,
          ((workFn C₀ (σ.take (t + 1)) (S t) - f t) + (f t - f (t + 1))) := by
    refine Eq.trans ?_ (Finset.sum_congr rfl hterm)
    rfl
  have hsplit2 : (∑ t ∈ Finset.range σ.length,
        ((workFn C₀ (σ.take (t + 1)) (S t) - f t) + (f t - f (t + 1))))
      = (∑ t ∈ Finset.range σ.length, (workFn C₀ (σ.take (t + 1)) (S t) - f t))
        + ∑ t ∈ Finset.range σ.length, (f t - f (t + 1)) :=
    Finset.sum_add_distrib
  have htel : (∑ t ∈ Finset.range σ.length, (f t - f (t + 1))) = f 0 - f σ.length :=
    Finset.sum_range_sub' f σ.length
  have hf0 : f 0 = 0 := by
    show workFn C₀ (σ.take 0) ((WFA hk C₀).conf (σ.take 0)) = 0
    rw [List.take_zero]
    have hc : (WFA hk C₀).conf ([] : List M) = C₀ := rfl
    rw [hc, workFn_nil k hk M C₀ C₀]
    unfold moveCost
    simp
  have hfn : f σ.length = workFunction C₀ σ ((WFA hk C₀).conf σ) := by
    rw [hfdef]
    simp only [hSdef, List.take_length]
    rfl
  have hbody : ∀ t : ℕ, workFn C₀ (σ.take (t + 1)) (S t) - f t
      = workFunction C₀ (σ.take (t + 1)) ((WFA hk C₀).conf (σ.take t))
        - workFunction C₀ (σ.take t) ((WFA hk C₀).conf (σ.take t)) := fun _ => rfl
  rw [hcost, hsplit2, htel, hf0, hfn]
  simp only [hbody]
  ring
