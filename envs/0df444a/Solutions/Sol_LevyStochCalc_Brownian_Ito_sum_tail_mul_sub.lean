-- Prove2me | solution 1 for LevyStochCalc.Brownian.Ito.sum_tail_mul_sub
-- status  : ACCEPTED   (prove)
-- author  : @yuzhou
-- created : 2026-11-21T07:07:16.796673+00:00
-- url     : https://prove2.me/submissions/54d571eb-f423-4773-ab05-e1def0a48233

import Definitions.Def_LevyStochCalc_Brownian_PRPGrid_F000

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# The predictable representation over a grid

Iterating the one-window statement over the cells of a grid: a square-integrable weight of mean
zero and orthogonal to every Itô integral is orthogonal to every character of the increments of a
Brownian motion along a grid.
-/

namespace LevyStochCalc.Brownian.Ito

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

universe u

variable {Ω : Type u} [MeasurableSpace Ω]

section Grid

variable {P : Measure Ω} [IsProbabilityMeasure P]
  {W : LevyStochCalc.Brownian.BrownianMotion P}
  {ℱ : Filtration ℝ ‹MeasurableSpace Ω›} {hℱ : IsBrownianFiltration W ℱ}

end Grid

section Abel



theorem _root_.solution (c : ℕ → ℝ) {Wv : ℕ → ℝ} (h0 : Wv 0 = 0) (n : ℕ) :
    ∑ k ∈ Finset.range n, (∑ j ∈ Finset.Ico (k + 1) (n + 1), c j) * (Wv (k + 1) - Wv k)
      = ∑ k ∈ Finset.Ico 1 (n + 1), c k * Wv k := by
  have telescope (j : ℕ) : ∑ k ∈ Finset.range j, (Wv (k + 1) - Wv k) = Wv j := by
    induction j with
    | zero => simp [h0]
    | succ j ih => rw [Finset.sum_range_succ, ih]; ring
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ]
    have hs (k : ℕ) (hk : k ∈ Finset.range n) :
        (∑ j ∈ Finset.Ico (k + 1) (n + 1 + 1), c j) =
        (∑ j ∈ Finset.Ico (k + 1) (n + 1), c j) + c (n + 1) :=
      Finset.sum_Ico_succ_top (by simpa using Nat.succ_le_succ (Finset.mem_range.mp hk).le) _
    have he : Finset.Ico (n + 1) (n + 1 + 1) = {n + 1} := by
      ext k
      simp [Finset.mem_Ico]
    rw [he, Finset.sum_singleton, Finset.sum_Ico_succ_top (by omega : 1 ≤ n + 1)]
    have hsum :
        ∑ k ∈ Finset.range n, (∑ j ∈ Finset.Ico (k + 1) (n + 1 + 1), c j) *
            (Wv (k + 1) - Wv k) =
        (∑ k ∈ Finset.range n, (∑ j ∈ Finset.Ico (k + 1) (n + 1), c j) *
            (Wv (k + 1) - Wv k)) + c (n + 1) * Wv n := by
      rw [← telescope n, Finset.mul_sum, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl (fun k hk => by rw [hs k hk, add_mul])
    rw [hsum, ih]
    ring
