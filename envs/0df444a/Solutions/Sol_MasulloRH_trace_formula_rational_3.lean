-- Prove2me | solution 3 for MasulloRH.trace_formula_rational
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @marozols
-- created : 2026-11-20T22:29:19.357788+00:00
-- url     : https://prove2.me/submissions/659c04bf-bea7-4062-ae95-281e24ace0a5
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_MasulloRH_trace_window_comparison
import Theorems.Thm_MasulloRH_archTerm_log_test_eq_neg_real_place
import Theorems.Thm_riemann_hypothesis

set_option autoImplicit false

open MeasureTheory Set MasulloRH
open scoped Topology

/-- Under the Riemann hypothesis, no critical-strip zero lies on or outside the boundary
of a centered window of positive half-width `α`. -/
theorem solution (α : ℝ) (hα : 0 < α) (φ : ℝ → ℂ)
    (hφ : IsRationalTraceTest φ) :
    IntegrableOn (realTraceIntegrand φ) (Ioi 1) ∧
    Summable (primePowerTraceTerm φ) ∧
    Summable (zetaTraceTerm φ α) ∧
    (∫ t in Ioi (1 : ℝ), realTraceIntegrand φ t) +
      (∑' i : Nat.Primes × ℕ, primePowerTraceTerm φ i) =
      mellin φ (1 / 2) + mellin φ (-1 / 2) -
        ∑' ρ : ZetaZerosInTraceStrip α, zetaTraceTerm φ α ρ := by
  -- Unconditional window comparison (proved) and the archimedean bridge (proved).
  obtain ⟨hI, hP, hZ, -, hEq⟩ := trace_window_comparison α φ hφ
  have hArch := archTerm_log_test_eq_neg_real_place φ hφ
  -- RH: every critical-strip zero has real part `1/2`, so nothing is omitted.
  have hempty : IsEmpty
      {ρ : {z : ℂ // ConnesRZ.IsCriticalZero z} | α ≤ |ρ.val.re - 1/2|} := by
    refine ⟨fun r => ?_⟩
    obtain ⟨⟨z, hz0, hzpos, hzlt⟩, hzα⟩ := r
    have hre : z.re = 1 / 2 := by
      refine riemann_hypothesis z hz0 ?_ ?_
      · rintro ⟨n, rfl⟩
        have hn : (0 : ℝ) ≤ n := n.cast_nonneg
        have : ((-2 : ℂ) * ((n : ℂ) + 1)).re = -2 * ((n : ℝ) + 1) := by simp
        rw [this] at hzpos
        linarith
      · rintro rfl
        simp at hzlt
    have hzα' : α ≤ |z.re - 1 / 2| := hzα
    rw [hre, sub_self, abs_zero] at hzα'
    linarith
  have h0 : (∑' r : {ρ : {z : ℂ // ConnesRZ.IsCriticalZero z} | α ≤ |ρ.val.re - 1/2|},
      (ConnesRZ.zeroMult r.val.val : ℂ) * mellin φ (r.val.val - 1/2)) = 0 :=
    tsum_empty
  refine ⟨hI, hP, hZ, ?_⟩
  rw [h0, add_zero, hArch] at hEq
  linear_combination hEq
