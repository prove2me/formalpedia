-- Prove2me | solution 1 for NRLFormulary.cbinom_vandermonde
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-23T09:32:20.860982+00:00
-- url     : https://prove2.me/submissions/c16b6032-3e03-4ab6-8b60-cb8be947315c

import Mathlib
import Definitions.Def_NRLFormulary_cbinom

open NRLFormulary

namespace Ag3Aux_Vandermonde

theorem desc_smeval (w : ℂ) (k : ℕ) :
    (descPochhammer ℤ k).smeval w = ∏ j ∈ Finset.range k, (w - (j : ℂ)) := by
  induction k with
  | zero => simp [Polynomial.smeval_one]
  | succ k ih =>
    rw [descPochhammer_succ_right, Polynomial.smeval_mul, ih, Finset.prod_range_succ,
      Polynomial.smeval_sub, Polynomial.smeval_X, Polynomial.smeval_natCast]
    simp

theorem cbinom_eq_choose (w : ℂ) (k : ℕ) : cbinom w k = Ring.choose w k := by
  rw [Ring.choose_eq_smul, desc_smeval, cbinom, smul_eq_mul, div_eq_inv_mul]

end Ag3Aux_Vandermonde

open Ag3Aux_Vandermonde

theorem solution (x y : ℂ) (n : ℕ) :
    ∑ k ∈ Finset.range (n + 1), cbinom x k * cbinom y (n - k) = cbinom (x + y) n := by
  rw [cbinom_eq_choose, Ring.add_choose_eq _ (Commute.all x y),
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ (fun i j => Ring.choose x i * Ring.choose y j)]
  simp [cbinom_eq_choose]
