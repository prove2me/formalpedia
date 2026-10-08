-- Prove2me | solution 1 for MatousekLP.SparseRecovery.bp_iff_bp_prime
-- status  : ACCEPTED   (prove)
-- author  : @moona3k
-- created : 2026-10-05T04:34:45.243724+00:00
-- url     : https://prove2.me/submissions/e2ecdf1b-eb6b-4883-80d0-e9748f47bc49

import Definitions.Def_MatousekLP_SparseRecovery_BasisPursuit
import Mathlib

open Matrix MatousekLP.SparseRecovery

theorem solution {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) :
    (∀ x u : Fin n → ℝ, IsBPPrimeOptimal A b x u → ∀ i, u i = |x i|) ∧
      (∀ x : Fin n → ℝ, IsBPOptimal A b x ↔ IsBPPrimeOptimal A b x (fun i => |x i|)) := by
  -- (x, |x|) is feasible whenever Ax = b, and any feasible (x, u) has u ≥ |x|
  have feas_abs : ∀ x, A *ᵥ x = b → IsBPPrimeFeasible A b x (fun i => |x i|) := by
    intro x hx
    refine ⟨hx, fun i => ?_, fun i => le_abs_self _, fun i => abs_nonneg _⟩
    simpa using neg_abs_le (x i)
  have abs_le_u : ∀ x u, IsBPPrimeFeasible A b x u → ∀ i, |x i| ≤ u i := by
    rintro x u ⟨-, h1, h2, -⟩ i
    exact abs_le.mpr ⟨by simpa using h1 i, h2 i⟩
  refine ⟨fun x u hopt i => ?_, fun x => ⟨fun hbp => ?_, fun hbp' => ?_⟩⟩
  · obtain ⟨hfeas, hmin⟩ := hopt
    have hle := hmin x (fun i => |x i|) (feas_abs x hfeas.1)
    have hge := abs_le_u x u hfeas
    -- ∑ (u - |x|) ≤ 0 with nonnegative terms
    have hsum : ∑ j, (u j - |x j|) = 0 := by
      apply le_antisymm
      · rw [Finset.sum_sub_distrib]; linarith
      · exact Finset.sum_nonneg fun j _ => sub_nonneg.mpr (hge j)
    have := (Finset.sum_eq_zero_iff_of_nonneg fun j _ => sub_nonneg.mpr (hge j)).mp hsum i
      (Finset.mem_univ i)
    linarith
  · obtain ⟨hx, hmin⟩ := hbp
    refine ⟨feas_abs x hx, fun x' u' hfeas' => ?_⟩
    calc ∑ i, |x i| = l1Norm x := rfl
      _ ≤ l1Norm x' := hmin x' hfeas'.1
      _ ≤ ∑ i, u' i := Finset.sum_le_sum fun i _ => abs_le_u x' u' hfeas' i
  · obtain ⟨hfeas, hmin⟩ := hbp'
    exact ⟨hfeas.1, fun x' hx' => hmin x' (fun i => |x' i|) (feas_abs x' hx')⟩
