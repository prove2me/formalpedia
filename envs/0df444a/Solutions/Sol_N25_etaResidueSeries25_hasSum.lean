-- Prove2me | solution 1 for N25.etaResidueSeries25_hasSum
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:35:52.167541+00:00
-- url     : https://prove2.me/submissions/da788ebd-c287-4b7b-804b-7bd3e01e1b66

import Mathlib
import Definitions.Def_N25_UnitSeries
import Theorems.Thm_N25_hasSum_stabilized_polynomial_product
import Theorems.Thm_N25_etaResidueSeries25_coeff

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency.types false

open Polynomial

open scoped BigOperators

namespace N25

/-- The frozen integer residue series sums to its residue-indexed Euler product in the unit disk. -/
theorem _root_.solution
    (g : ℕ) (hg : 0 < g) (hg25 : g < 25)
    (q : ℂ) (hq : ‖q‖ < 1) :
    HasSum (fun n : ℕ =>
      ((PowerSeries.coeff n (etaResidueSeries25 g) : ℤ) : ℂ) * q ^ n)
      (∏' k : ℕ,
        (if (k + 1) % 25 = g then 1 - q ^ (k + 1) else 1) *
        (if (k + 1) % 25 = 25 - g then 1 - q ^ (k + 1) else 1)) := by
  classical
  let P : ℕ → ℂ[X] := fun k =>
    (if (k + 1) % 25 = g then 1 - X else 1) *
    (if (k + 1) % 25 = 25 - g then 1 - X else 1)
  have hdistinct : g ≠ 25 - g := by omega
  have hP (k : ℕ) : (P k).coeff 0 = 1 := by
    dsimp only [P]
    split_ifs <;> simp
  have hone (k : ℕ) : ‖(1 : ℂ[X]).coeff k‖ ≤ ‖(1 - X : ℂ[X]).coeff k‖ := by
    by_cases hk : k = 0
    · subst k; simp
    · simp only [Polynomial.coeff_one, if_neg hk, norm_zero]
      exact norm_nonneg _
  have hdom (n k : ℕ) : ‖(P n).coeff k‖ ≤ ‖(1 - X : ℂ[X]).coeff k‖ := by
    dsimp only [P]
    split_ifs with ha hb hb
    · exact False.elim (hdistinct (ha.symm.trans hb))
    · simp
    · simp
    · simpa using hone k
  have hs := hasSum_stabilized_polynomial_product P (1 - X) hP (by simp) hdom q hq
  have hcoef (n : ℕ) :
      (∏ k ∈ Finset.range n, Polynomial.expand ℂ (k + 1) (P k)).coeff n =
        ((PowerSeries.coeff n (etaResidueSeries25 g) : ℤ) : ℂ) := by
    rw [etaResidueSeries25_coeff g hg hg25 n]
    have he :
        (∏ k ∈ Finset.range n, Polynomial.expand ℂ (k + 1) (P k)) =
        Polynomial.map (Int.castRingHom ℂ)
          (∏ k ∈ Finset.range n,
            ((if (k + 1) % 25 = g then (1 - X ^ (k + 1) : ℤ[X]) else 1) *
              (if (k + 1) % 25 = 25 - g then (1 - X ^ (k + 1) : ℤ[X]) else 1))) := by
      rw [Polynomial.map_prod]
      apply Finset.prod_congr rfl
      intro k hk
      dsimp only [P]
      split_ifs <;> simp [Polynomial.expand_X]
    rw [he, Polynomial.coeff_map]
    rfl
  have heval (k : ℕ) : (P k).eval (q ^ (k + 1)) =
      (if (k + 1) % 25 = g then 1 - q ^ (k + 1) else 1) *
      (if (k + 1) % 25 = 25 - g then 1 - q ^ (k + 1) else 1) := by
    dsimp only [P]
    split_ifs <;> simp
  simpa only [hcoef, heval] using hs

end N25
