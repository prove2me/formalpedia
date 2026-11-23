-- Prove2me | solution 1 for MasulloRH.quadratic_mertens_prefix_bounds
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T00:12:35.035795+00:00
-- url     : https://prove2.me/submissions/26b0f165-166c-4441-b41a-1b0365ce5719
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Theorems.Thm_mathlib_riemannHypothesis
import Theorems.Thm_MasulloRH_mertens_energy_criterion_and_critical_divergence

set_option autoImplicit false

open Finset ArithmeticFunction
namespace MasulloRH
end MasulloRH
open MasulloRH
theorem solution :
    let M (n : ℕ) : ℝ := ∑ i ∈ Finset.Icc 1 n,(moebius i:ℝ)
    ∀ d : ℝ,0<d → ∃ C : ℝ,0≤C ∧ ∀ N : ℕ,
      (∑ n ∈ range N,(M (n+1))^2) ≤ C*((N:ℝ)+1)^(2+d) :=
  by
  obtain ⟨-, h2, -, -⟩ := MasulloRH.mertens_energy_criterion_and_critical_divergence
  exact h2.mp mathlib_riemannHypothesis
