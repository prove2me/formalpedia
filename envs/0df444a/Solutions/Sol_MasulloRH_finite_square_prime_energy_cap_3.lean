-- Prove2me | solution 3 for MasulloRH.finite_square_prime_energy_cap
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T21:26:22.663811+00:00
-- url     : https://prove2.me/submissions/3f8fb5d2-c5d6-4145-9415-7e605313fa12
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Theorems.Thm_mathlib_riemannHypothesis
import Theorems.Thm_MasulloRH_riemannHypothesis_iff_square_sampled_prime_energy

set_option autoImplicit false

open Finset ArithmeticFunction MeasureTheory Set
open MasulloRH

theorem solution (N : ℕ) :
    let G (x : ℝ) := (∑ n ∈ range (⌊x⌋₊+1),vonMangoldt n*max (x/(n:ℝ)-1) 0) -
      x*(Real.log x-1-Real.eulerMascheroniConstant)
    (∑ n ∈ range N, let k := (n:ℝ)+4; (G (k^2))^2/(k^3*(1+Real.log k)^2)) ≤ 81 :=
  by
  obtain ⟨-, h2, -⟩ := MasulloRH.riemannHypothesis_iff_square_sampled_prime_energy
  exact h2.mp mathlib_riemannHypothesis N
