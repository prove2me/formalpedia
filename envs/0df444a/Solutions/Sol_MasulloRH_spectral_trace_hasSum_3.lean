-- Prove2me | solution 3 for MasulloRH.spectral_trace_hasSum
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @dga471
-- created : 2026-11-20T23:28:57.881047+00:00
-- url     : https://prove2.me/submissions/280c296d-4ad8-4667-be1d-b814e80d023d
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_MasulloRH_RationalTrace
import Definitions.Def_ConnesRZ_weil_defs
import Theorems.Thm_MasulloRH_trace_window_comparison
import Theorems.Thm_MasulloRH_archTerm_log_test_eq_neg_real_place
import Theorems.Thm_MasulloRH_narrow_window_omitted_zero_sum

open MeasureTheory Set MasulloRH

/-- SKETCH proof of `MasulloRH.spectral_trace_hasSum`
(id ab2befc9-2e68-45a1-9474-fcf930cb1338).

Strategy: the comparison identity (`trace_window_comparison`) writes
  prime + window + omitted = polar + archTerm,
and `archTerm_log_test_eq_neg_real_place` rewrites `archTerm = - realPlace`.
So it suffices to show the omitted sum is `0`, after which
`Summable.hasSum_iff` (summability = component 3 of the comparison) turns the
resulting `tsum` identity into the goal `HasSum`.

The omitted sum vanishes for two disjoint reasons:
* `α < 1/2`: this is exactly the open node `narrow_window_omitted_zero_sum`.
* `α ≥ 1/2`: the omitted subtype is EMPTY — a critical zero has
  `0 < re < 1`, hence `|re - 1/2| < 1/2 ≤ α`, contradicting the defining
  condition `α ≤ |re - 1/2|` — and a `tsum` over an empty type is `0`
  (`tsum_empty`). -/
theorem solution (α : ℝ) (hα : 0 < α) (φ : ℝ → ℂ) (hφ : IsRationalTraceTest φ) :
    HasSum (zetaTraceTerm φ α) ((mellin φ (1 / 2) + mellin φ (-1 / 2)) -
      ((∫ t in Ioi (1 : ℝ), realTraceIntegrand φ t) + ∑' i : Nat.Primes × ℕ, primePowerTraceTerm φ i)) := by
  obtain ⟨hInt, hPrime, hWin, hOm, hId⟩ := MasulloRH.trace_window_comparison α φ hφ
  have hArch := MasulloRH.archTerm_log_test_eq_neg_real_place φ hφ
  -- The omitted sum vanishes, by cases on the window width.
  have hOm0 : (let omitted := {ρ : {z : ℂ // ConnesRZ.IsCriticalZero z} | α ≤ |ρ.val.re - 1/2|}
      (∑' r : omitted, (ConnesRZ.zeroMult r.val.val : ℂ) * mellin φ (r.val.val - 1/2))) = 0 := by
    by_cases hsmall : α < 1 / 2
    · -- Narrow window: the (open) omitted-sum node applies verbatim.
      exact MasulloRH.narrow_window_omitted_zero_sum α hα hsmall φ hφ
    · -- Wide window: no critical zero can be omitted; the index type is empty.
      have hα2 : (1 : ℝ) / 2 ≤ α := le_of_not_gt hsmall
      have hEmpty : IsEmpty {ρ : {z : ℂ // ConnesRZ.IsCriticalZero z} | α ≤ |ρ.val.re - 1/2|} := by
        refine ⟨fun r => ?_⟩
        obtain ⟨-, h0, h1⟩ := r.val.property
        have hlt : |r.val.val.re - 1 / 2| < 1 / 2 := by
          rw [abs_lt]
          constructor <;> linarith
        exact absurd r.property (not_le.mpr (lt_of_lt_of_le hlt hα2))
      haveI := hEmpty
      exact tsum_empty
  -- Assemble: window tsum = trace value, then promote via `Summable.hasSum_iff`.
  apply hWin.hasSum_iff.mpr
  -- Arithmetic check: (hId) + (hArch) - (hOm0), as (LHS - RHS) combinations, is
  -- (P + W + O - (M + A)) + (A - (-R)) - (O - 0) = P + W - M + R, and
  -- (window tsum - trace value) minus that is 0 by ring.
  linear_combination hId + hArch - hOm0

