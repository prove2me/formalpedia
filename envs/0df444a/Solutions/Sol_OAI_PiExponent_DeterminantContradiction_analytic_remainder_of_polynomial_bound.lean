-- Prove2me | solution 1 for OAI.PiExponent.DeterminantContradiction.analytic_remainder_of_polynomial_bound
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-23T18:05:33.711999+00:00
-- url     : https://prove2.me/submissions/07670cc3-bdaf-47b8-a994-b74c8d0ba1d8

import Definitions.Def_OAI_PiExponent_TruncatedPolynomialJets
import Theorems.Thm_OAI_PiExponent_DeterminantContradiction_log_nat_polynomial_bound_div_tends_zero
import Theorems.Thm_OAI_PiExponent_DeterminantContradiction_log_weighted_polynomial_factor_div_tends_zero
import Theorems.Thm_OAI_PiExponent_DeterminantContradiction_real_constant_div_tends_zero

open OAI.PiExponent OAI.PiExponent.DeterminantContradiction
open Filter Topology

theorem solution {nu : Real} (d : FixedData nu)
    (hbound : ∃ C : Real, 0 < C ∧ ∀ᶠ H : Real in atTop,
      0 < (actualRowCount d H : Real) ∧
        (actualRowCount d H : Real) ≤ C * (H + 1) ^ (d.m + 1)) :
    Tendsto (fun H : Real =>
      (Real.log (actualRowCount d H : Real) + Real.log 2 / 4 -
        Real.log (1 - Real.exp (-Real.log 2 / 2)) +
        Real.log ((H + 1) ^ (2 * d.m) * (H / (d.v0 : Real) + 1))) / H)
      atTop (𝓝 0) := by
  rcases hbound with ⟨C, hC, hrow⟩
  have hrowLog : Tendsto
      (fun H : Real => Real.log (actualRowCount d H : Real) / H)
      atTop (𝓝 0) :=
    OAI.PiExponent.DeterminantContradiction.log_nat_polynomial_bound_div_tends_zero
      (fun H => actualRowCount d H) C (d.m + 1) hC hrow
  have hfactorLog : Tendsto
      (fun H : Real =>
        Real.log ((H + 1) ^ (2 * d.m) * (H / (d.v0 : Real) + 1)) / H)
      atTop (𝓝 0) :=
    OAI.PiExponent.DeterminantContradiction.log_weighted_polynomial_factor_div_tends_zero
      d.m (d.v0 : Real) d.v0_pos
  have hconstant : Tendsto
      (fun H : Real =>
        (Real.log 2 / 4 - Real.log (1 - Real.exp (-Real.log 2 / 2))) / H)
      atTop (𝓝 0) :=
    OAI.PiExponent.DeterminantContradiction.real_constant_div_tends_zero _
  have hsum := hrowLog.add (hconstant.add hfactorLog)
  convert hsum using 1 <;> ext H <;> ring