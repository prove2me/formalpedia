-- Prove2me | solution 1 for MasulloRH.finite_square_prime_energy_cap
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @marozols
-- created : 2026-11-21T03:51:02.651552+00:00
-- url     : https://prove2.me/submissions/25869ab5-c995-4648-84a9-c7c42fe1fc81
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_MasulloRH_RegularizedTrace
import Theorems.Thm_MasulloRH_verified_square_prime_energy_prefix
import Theorems.Thm_MasulloRH_prime_energy_growth_detects_zero_abscissa
import Theorems.Thm_MasulloRH_sparse_subpower_square_prime_energy
import Theorems.Thm_MasulloRH_riemannHypothesis_iff_square_sampled_prime_energy
import Mathlib
set_option autoImplicit false
open Finset ArithmeticFunction MeasureTheory Set
open MasulloRH
theorem solution (N : ℕ) :
    let G (x : ℝ) := (∑ n ∈ range (⌊x⌋₊+1),vonMangoldt n*max (x/(n:ℝ)-1) 0) -
      x*(Real.log x-1-Real.eulerMascheroniConstant)
    (∑ n ∈ range N, let k := (n:ℝ)+4; (G (k^2))^2/(k^3*(1+Real.log k)^2)) ≤ 81 := by
  dsimp only
  by_cases h : N≤10000000
  · exact (verified_square_prime_energy_prefix.2.1 N h).trans (by norm_num)
  · have hRH := prime_energy_growth_detects_zero_abscissa.2.2.mpr sparse_subpower_square_prime_energy
    exact riemannHypothesis_iff_square_sampled_prime_energy.2.1.mp hRH N
