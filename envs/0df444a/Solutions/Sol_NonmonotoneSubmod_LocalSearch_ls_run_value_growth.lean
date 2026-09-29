-- Prove2me | solution 1 for NonmonotoneSubmod.LocalSearch.ls_run_value_growth
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-28T23:08:20.688717+00:00
-- url     : https://prove2.me/submissions/927b16c2-dab4-4c16-b67d-43fc256dc8cb

import Mathlib
import Definitions.Def_NonmonotoneSubmod_LocalSearch_LSAlgorithm

namespace NonmonotoneSubmod.LocalSearch

theorem aux_lsrvg_step {X : Type} [Fintype X] [DecidableEq X] (ε : ℝ) (f : Finset X → ℝ)
    (S S' : Finset X) (h : lsStep ε f S S') : lsFactor X ε * f S < f S' := by
  rcases h with ⟨a, _, hlt, rfl⟩ | ⟨_, a, _, hlt, rfl⟩
  · exact hlt
  · exact hlt

theorem aux_lsrvg_pos {X : Type} [Fintype X] (ε : ℝ) (hε : 0 < ε) :
    0 ≤ lsFactor X ε := by
  unfold lsFactor
  have : 0 ≤ ε / (Fintype.card X : ℝ) ^ 2 := div_nonneg hε.le (sq_nonneg _)
  linarith

theorem aux_lsrvg_ind {X : Type} [Fintype X] [DecidableEq X] (ε : ℝ) (hε : 0 < ε)
    (f : Finset X → ℝ) (S : ℕ → Finset X) (k : ℕ) (hrun : IsLSRun ε f S k) (v : X)
    (hv : S 0 = {v}) : ∀ i, i ≤ k → lsFactor X ε ^ i * f {v} ≤ f (S i) := by
  intro i
  induction i with
  | zero => intro _; simp [hv]
  | succ i ih =>
    intro hi
    have h1 := ih (by omega)
    have h2 := aux_lsrvg_step ε f _ _ (hrun.2 i (by omega))
    have hc := aux_lsrvg_pos (X := X) ε hε
    calc lsFactor X ε ^ (i + 1) * f {v} = lsFactor X ε * (lsFactor X ε ^ i * f {v}) := by ring
      _ ≤ lsFactor X ε * f (S i) := mul_le_mul_of_nonneg_left h1 hc
      _ ≤ f (S (i + 1)) := h2.le

end NonmonotoneSubmod.LocalSearch

open NonmonotoneSubmod.LocalSearch

theorem solution {X : Type} [Fintype X] [DecidableEq X] (ε : ℝ) (hε : 0 < ε)
    (f : Finset X → ℝ) (S : ℕ → Finset X) (k : ℕ) (hrun : IsLSRun ε f S k) (v : X)
    (hv : S 0 = {v}) :
    (1 + ε / (Fintype.card X : ℝ) ^ 2) ^ k * f {v} ≤ f (S k) := by
  exact aux_lsrvg_ind ε hε f S k hrun v hv k le_rfl
