-- Prove2me | solution 1 for OAI.PiExponent.DeterminantContradiction.analytic_remainder_candidate_tendsto_zero
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-23T17:59:48.619382+00:00
-- url     : https://prove2.me/submissions/8e74409f-da66-4822-ac41-7207e7f32c6c

import Definitions.Def_OAI_PiExponent_TruncatedPolynomialJets
import Theorems.Thm_OAI_PiExponent_DeterminantContradiction_actualRowCount_has_polynomial_bound
import Theorems.Thm_OAI_PiExponent_DeterminantContradiction_analytic_remainder_of_polynomial_bound

open OAI.PiExponent OAI.PiExponent.DeterminantContradiction
open Filter Topology

theorem solution {nu : Real} (d : FixedData nu) :
    Tendsto (fun H : Real =>
      (Real.log (actualRowCount d H : Real) + Real.log 2 / 4 -
        Real.log (1 - Real.exp (-Real.log 2 / 2)) +
        Real.log ((H + 1) ^ (2 * d.m) * (H / (d.v0 : Real) + 1))) / H)
      atTop (𝓝 0) := by
  exact analytic_remainder_of_polynomial_bound d
    (actualRowCount_has_polynomial_bound d)