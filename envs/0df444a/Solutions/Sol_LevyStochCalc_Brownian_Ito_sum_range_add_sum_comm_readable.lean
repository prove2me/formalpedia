-- Prove2me | solution 1 for LevyStochCalc.Brownian.Ito.sum_range_add_sum_comm_readable
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-26T14:18:22.878501+00:00
-- url     : https://prove2.me/submissions/1ba93cc5-3c53-4fa1-ad42-11324bc1dc56

import Definitions.Def_KLSModular_LevyStochCalc_Brownian_VectorItoFormulaDecomp

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
-- Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (upstream path LevyStochCalc/Brownian/VectorItoFormulaDecomp.lean; Apache-2.0; provenance in formalization/vendor/vendor-lock.json of the KLS repository)
open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
universe u
section Reindex
variable {n d : ℕ}
/-- Reordering a triple sum whose summand splits into a scalar and a sum over a second index. -/
theorem solution (m : ℕ) (A : Fin n → ℕ → ℝ) (Bc : Fin n → Fin d → ℕ → ℝ) :
    ∑ i ∈ Finset.range m, ∑ p : Fin n, (A p i + ∑ k : Fin d, Bc p k i)
      = (∑ p : Fin n, ∑ i ∈ Finset.range m, A p i)
        + ∑ p : Fin n, ∑ k : Fin d, ∑ i ∈ Finset.range m, Bc p k i := by
  calc ∑ i ∈ Finset.range m, ∑ p : Fin n, (A p i + ∑ k : Fin d, Bc p k i)
      = ∑ i ∈ Finset.range m,
          ((∑ p : Fin n, A p i) + ∑ p : Fin n, ∑ k : Fin d, Bc p k i) :=
        Finset.sum_congr rfl fun i _ => Finset.sum_add_distrib
    _ = (∑ i ∈ Finset.range m, ∑ p : Fin n, A p i)
          + ∑ i ∈ Finset.range m, ∑ p : Fin n, ∑ k : Fin d, Bc p k i :=
        Finset.sum_add_distrib
    _ = (∑ p : Fin n, ∑ i ∈ Finset.range m, A p i)
          + ∑ p : Fin n, ∑ i ∈ Finset.range m, ∑ k : Fin d, Bc p k i := by
        congr 1 <;> exact Finset.sum_comm
    _ = (∑ p : Fin n, ∑ i ∈ Finset.range m, A p i)
          + ∑ p : Fin n, ∑ k : Fin d, ∑ i ∈ Finset.range m, Bc p k i := by
        congr 1
        exact Finset.sum_congr rfl fun p _ => Finset.sum_comm
