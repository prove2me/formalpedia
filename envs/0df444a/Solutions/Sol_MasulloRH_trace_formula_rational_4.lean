-- Prove2me | solution 4 for MasulloRH.trace_formula_rational
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @deleted
-- created : 2026-11-21T00:39:21.970931+00:00
-- url     : https://prove2.me/submissions/493bc6cd-ab57-4589-838f-95765f660e0f
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_MasulloRH_narrow_window_omitted_zero_sum
import Theorems.Thm_MasulloAudit_trace_formula_window_with_remainder
import Theorems.Thm_MasulloAudit_trace_formula_rational_of_half_le

set_option autoImplicit false

open MeasureTheory Set
open scoped Topology
open MasulloRH

theorem solution (α : ℝ) (hα : 0 < α) (φ : ℝ → ℂ)
    (hφ : IsRationalTraceTest φ) :
    IntegrableOn (realTraceIntegrand φ) (Ioi 1) ∧
    Summable (primePowerTraceTerm φ) ∧
    Summable (zetaTraceTerm φ α) ∧
    (∫ t in Ioi (1 : ℝ), realTraceIntegrand φ t) +
      (∑' i : Nat.Primes × ℕ, primePowerTraceTerm φ i) =
      mellin φ (1 / 2) + mellin φ (-1 / 2) -
        ∑' ρ : ZetaZerosInTraceStrip α, zetaTraceTerm φ α ρ := by
  rcases lt_or_ge α (1 / 2) with hsmall | hbig
  · -- Narrow window: unconditional formula with remainder, and the remainder vanishes.
    obtain ⟨hI, hP, hS, -, hEq⟩ := MasulloAudit.trace_formula_window_with_remainder α φ hφ
    let e : {ρ : {z : ℂ // ConnesRZ.IsCriticalZero z} | α ≤ |ρ.val.re - 1/2|} ≃
        {ρ : ZetaZerosInTraceStrip (1 / 2) | α ≤ |(ρ : ℂ).re - 1 / 2|} :=
      { toFun := fun r =>
          ⟨⟨r.1.1, r.1.2.1, r.1.2.2.1, r.1.2.2.2,
            by rw [abs_lt]; constructor <;> linarith [r.1.2.2.1, r.1.2.2.2]⟩, r.2⟩
        invFun := fun r => ⟨⟨r.1.1, r.1.2.1, r.1.2.2.1, r.1.2.2.2.1⟩, r.2⟩
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }
    have hrem : (∑' ρ : {ρ : ZetaZerosInTraceStrip (1 / 2) | α ≤ |(ρ : ℂ).re - 1 / 2|},
        zetaTraceTerm φ (1 / 2) ρ) = 0 := by
      rw [← e.tsum_eq]
      exact MasulloRH.narrow_window_omitted_zero_sum α hα hsmall φ hφ
    rw [hrem, sub_zero] at hEq
    exact ⟨hI, hP, hS, hEq⟩
  · -- Wide window α ≥ 1/2: the window contains the whole critical strip.
    exact MasulloAudit.trace_formula_rational_of_half_le α hbig φ hφ
