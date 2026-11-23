-- Prove2me | solution 2 for MasulloRH.sparse_subpower_square_prime_energy
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T00:12:43.392668+00:00
-- url     : https://prove2.me/submissions/2f96bd4c-28b6-4b19-ac5f-b31f22259dc4
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_MasulloRH_RegularizedTrace
import Theorems.Thm_mathlib_riemannHypothesis
import Theorems.Thm_MasulloRH_prime_energy_growth_detects_zero_abscissa

set_option autoImplicit false

open Finset ArithmeticFunction MeasureTheory Set
namespace MasulloRH
end MasulloRH
open MasulloRH
theorem solution :
    let G (x : ℝ) := (∑ n ∈ range (⌊x⌋₊+1),vonMangoldt n*max (x/(n:ℝ)-1) 0) -
      x*(Real.log x-1-Real.eulerMascheroniConstant)
    let E (N : ℕ) := ∑ n ∈ range N, let k := (n:ℝ)+4; (G (k^2))^2/(k^3*(1+Real.log k)^2)
    ∃ J : ℕ,∀ j ≥ J, let D := (2:ℕ)^(2^j)
      E D ≤ (D:ℝ)^(1/((j:ℝ)+1)) :=
  by
  obtain ⟨-, -, h3⟩ := MasulloRH.prime_energy_growth_detects_zero_abscissa
  exact h3.mp mathlib_riemannHypothesis
