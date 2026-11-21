-- Prove2me | solution 1 for MasulloAudit.trace_formula_rational_of_half_le
-- status  : ACCEPTED   (prove)
-- author  : @lll
-- created : 2026-11-21T00:25:58.396553+00:00
-- url     : https://prove2.me/submissions/d166483b-47dd-4180-b15c-7cd66d26aa94

import Theorems.Thm_MasulloRH_trace_formula_rational_full_strip

set_option autoImplicit false

open MeasureTheory Set MasulloRH
open scoped Topology

/-- For `α ≥ 1/2` the window contains the whole critical strip, so the window type is
equivalent to the full-strip type. -/
private def hw_equiv (α : ℝ) (hα : 1 / 2 ≤ α) :
    ZetaZerosInTraceStrip α ≃ ZetaZerosInTraceStrip (1 / 2) where
  toFun ρ := ⟨ρ.1, ρ.2.1, ρ.2.2.1, ρ.2.2.2.1,
    abs_sub_lt_iff.2 ⟨by linarith [ρ.2.2.2.1], by linarith [ρ.2.2.1]⟩⟩
  invFun ρ := ⟨ρ.1, ρ.2.1, ρ.2.2.1, ρ.2.2.2.1,
    lt_of_lt_of_le (abs_sub_lt_iff.2 ⟨by linarith [ρ.2.2.2.1], by linarith [ρ.2.2.1]⟩) hα⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem solution (α : ℝ) (hα : 1 / 2 ≤ α) :
    ∀ (φ : ℝ → ℂ), IsRationalTraceTest φ →
      IntegrableOn (realTraceIntegrand φ) (Ioi 1) ∧
      Summable (primePowerTraceTerm φ) ∧
      Summable (zetaTraceTerm φ α) ∧
      (∫ t in Ioi (1 : ℝ), realTraceIntegrand φ t) +
        (∑' i : Nat.Primes × ℕ, primePowerTraceTerm φ i) =
        mellin φ (1 / 2) + mellin φ (-1 / 2) -
          ∑' ρ : ZetaZerosInTraceStrip α, zetaTraceTerm φ α ρ := by
  intro φ hφ
  obtain ⟨hI, hP, hZ, hEq⟩ := trace_formula_rational_full_strip φ hφ
  have hcomp : zetaTraceTerm φ α = zetaTraceTerm φ (1 / 2) ∘ hw_equiv α hα := rfl
  refine ⟨hI, hP, ?_, ?_⟩
  · rw [hcomp]; exact (hw_equiv α hα).summable_iff.2 hZ
  · rw [hEq, hcomp]
    congr 1
    exact ((hw_equiv α hα).tsum_eq (zetaTraceTerm φ (1 / 2))).symm

#print axioms solution
