-- Prove2me | solution 1 for KellyStochasticNetworks.erlang_deriv
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-25T19:59:49.083496+00:00
-- url     : https://prove2.me/submissions/45d0101e-3eaf-4ad4-8eb9-13194c60c9f6

import Mathlib
import Definitions.Def_KellyStochasticNetworks_Erlang

open KellyStochasticNetworks

theorem solution (ν : ℝ) (C : ℕ) (hν : 0 < ν) :
    HasDerivAt (fun v : ℝ => erlang v (C + 1))
      (-(1 - erlang ν (C + 1)) * (erlang ν (C + 1) - erlang ν C)) ν := by
  -- Derivative of a single term: `d/dv (v^(n+1)/(n+1)!) = v^n/n!`.
  have hterm : ∀ (n : ℕ) (v : ℝ),
      HasDerivAt (fun v : ℝ => v ^ (n + 1) / (Nat.factorial (n + 1) : ℝ))
        (v ^ n / (Nat.factorial n : ℝ)) v := by
    intro n v
    refine ((hasDerivAt_pow (n + 1) v).div_const (Nat.factorial (n + 1) : ℝ)).congr_deriv ?_
    rw [Nat.factorial_succ, Nat.add_sub_cancel]
    push_cast
    field_simp
  -- Derivative of the partial exponential sum: `d/dv S_{n+1}(v) = S_n(v)`,
  -- where `S_n(v) = ∑_{j ≤ n} v^j/j!`.
  have hsum : ∀ (n : ℕ) (v : ℝ),
      HasDerivAt (fun v : ℝ => ∑ j ∈ Finset.range (n + 2), v ^ j / (Nat.factorial j : ℝ))
        (∑ j ∈ Finset.range (n + 1), v ^ j / (Nat.factorial j : ℝ)) v := by
    intro n v
    induction n with
    | zero =>
      have e : (fun v : ℝ => ∑ j ∈ Finset.range (0 + 2), v ^ j / (Nat.factorial j : ℝ))
          = fun v => 1 + v ^ (0 + 1) / (Nat.factorial (0 + 1) : ℝ) := by
        funext w; simp [Finset.sum_range_succ]
      rw [e]
      exact ((hasDerivAt_const v (1 : ℝ)).add (hterm 0 v)).congr_deriv (by simp)
    | succ n ih =>
      have e : (fun v : ℝ => ∑ j ∈ Finset.range (n + 1 + 2), v ^ j / (Nat.factorial j : ℝ))
          = fun v => (∑ j ∈ Finset.range (n + 2), v ^ j / (Nat.factorial j : ℝ))
              + v ^ (n + 1 + 1) / (Nat.factorial (n + 1 + 1) : ℝ) := by
        funext w; rw [Finset.sum_range_succ]
      rw [e]
      exact (ih.add (hterm (n + 1) v)).congr_deriv (Finset.sum_range_succ _ (n + 1)).symm
  set D := ∑ j ∈ Finset.range (C + 2), ν ^ j / (Nat.factorial j : ℝ) with hD
  set D' := ∑ j ∈ Finset.range (C + 1), ν ^ j / (Nat.factorial j : ℝ) with hD'
  have hD'pos : 0 < D' := Finset.sum_pos (fun j _ => by positivity) ⟨0, by simp⟩
  have hDD' : D = D' + ν ^ (C + 1) / (Nat.factorial (C + 1) : ℝ) := by
    rw [hD, hD', Finset.sum_range_succ]
  have hDpos : 0 < D := by rw [hDD']; positivity
  have e : (fun v : ℝ => erlang v (C + 1)) = fun v =>
      v ^ (C + 1) / (Nat.factorial (C + 1) : ℝ) /
        ∑ j ∈ Finset.range (C + 2), v ^ j / (Nat.factorial j : ℝ) := by
    funext v; rfl
  rw [e]
  refine ((hterm C ν).div (hsum C ν) hDpos.ne').congr_deriv ?_
  simp only [erlang]
  rw [← hD, ← hD', hDD']
  field_simp
  ring
