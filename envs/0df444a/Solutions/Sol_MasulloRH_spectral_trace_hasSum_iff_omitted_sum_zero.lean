-- Prove2me | solution 1 for MasulloRH.spectral_trace_hasSum_iff_omitted_sum_zero
-- status  : ACCEPTED   (prove)
-- author  : @dga471
-- created : 2026-11-20T23:22:34.896727+00:00
-- url     : https://prove2.me/submissions/04c9daad-7371-4abd-ac1f-7b7d14913819

import Definitions.Def_MasulloRH_RationalTrace
import Definitions.Def_ConnesRZ_weil_defs
import Theorems.Thm_MasulloRH_trace_window_comparison
import Theorems.Thm_MasulloRH_archTerm_log_test_eq_neg_real_place

open MeasureTheory Set MasulloRH ConnesRZ

/-- Equivalence between the spectral `HasSum` assertion and the vanishing of
the omitted zero sum. Pure algebra from the two Proved inputs:
`trace_window_comparison` (identity + all summabilities) and
`archTerm_log_test_eq_neg_real_place`. -/
theorem solution (α : ℝ) (φ : ℝ → ℂ) (hφ : IsRationalTraceTest φ) :
    (HasSum (zetaTraceTerm φ α) ((mellin φ (1 / 2) + mellin φ (-1 / 2)) -
      ((∫ t in Ioi (1 : ℝ), realTraceIntegrand φ t) + ∑' i : Nat.Primes × ℕ, primePowerTraceTerm φ i))
    ↔
    (let omitted := {ρ : {z : ℂ // ConnesRZ.IsCriticalZero z} | α ≤ |ρ.val.re - 1/2|}
     (∑' r : omitted, (ConnesRZ.zeroMult r.val.val : ℂ) * mellin φ (r.val.val - 1/2)) = 0)) := by
  obtain ⟨hInt, hPrime, hWin, hOm, hId⟩ := MasulloRH.trace_window_comparison α φ hφ
  have hArch := MasulloRH.archTerm_log_test_eq_neg_real_place φ hφ
  constructor
  · -- Forward: HasSum gives the window tsum; comparison + arch identity force omitted = 0.
    intro h
    have hTsum : (∑' ρ, zetaTraceTerm φ α ρ)
        = (mellin φ (1 / 2) + mellin φ (-1 / 2)) -
          ((∫ t in Ioi (1 : ℝ), realTraceIntegrand φ t)
            + ∑' i : Nat.Primes × ℕ, primePowerTraceTerm φ i) :=
      hWin.hasSum_iff.mp h
    -- Goal (after the `let` is displayed): omitted tsum = 0.
    -- Arithmetic check: (hId) - (hTsum) + (hArch), as (LHS - RHS) combinations,
    -- equals (omitted - 0):  (P + W + O - (M + A)) - (W - (M - (R + P))) + (A - (-R)) = O.
    linear_combination hId - hTsum + hArch
  · -- Backward: omitted = 0 forces the window tsum to the trace value; promote to HasSum.
    intro hO
    apply hWin.hasSum_iff.mpr
    -- Arithmetic check: (hId) + (hArch) - (hO) has (LHS - RHS) combination
    -- (P + W + O - (M + A)) + (A - (-R)) - (O - 0) = P + W - M + R,
    -- and (window tsum - trace value) - that = 0 by ring.
    linear_combination hId + hArch - hO
