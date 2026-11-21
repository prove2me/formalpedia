-- Prove2me | solution 4 for MasulloRH.spectral_trace_hasSum
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @lll
-- created : 2026-11-21T00:37:04.757574+00:00
-- url     : https://prove2.me/submissions/d051a8e5-184e-416d-b794-8941f044d5e5
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_MasulloRH_omitted_spectral_mass_zero
import Theorems.Thm_MasulloAudit_trace_formula_window_with_remainder

open MeasureTheory Set
open MasulloRH

theorem solution (α : ℝ) (hα : 0 < α) (φ : ℝ → ℂ) (hφ : IsRationalTraceTest φ) :
    HasSum (zetaTraceTerm φ α) ((mellin φ (1 / 2) + mellin φ (-1 / 2)) -
      ((∫ t in Ioi (1 : ℝ), realTraceIntegrand φ t) + ∑' i : Nat.Primes × ℕ, primePowerTraceTerm φ i)) := by
  obtain ⟨-, -, hS, -, hEq⟩ := MasulloAudit.trace_formula_window_with_remainder α φ hφ
  -- The remainder of the unconditional window formula is the omitted zero sum, re-indexed.
  let e : {z : {w : ℂ // ConnesRZ.IsCriticalZero w} // ¬ |z.val.re - 1/2| < α} ≃
      {ρ : ZetaZerosInTraceStrip (1 / 2) | α ≤ |(ρ : ℂ).re - 1 / 2|} :=
    { toFun := fun r =>
        ⟨⟨r.1.1, r.1.2.1, r.1.2.2.1, r.1.2.2.2,
          by rw [abs_lt]; constructor <;> linarith [r.1.2.2.1, r.1.2.2.2]⟩, not_lt.1 r.2⟩
      invFun := fun r =>
        ⟨⟨r.1.1, r.1.2.1, r.1.2.2.1, r.1.2.2.2.1⟩, not_lt.2 r.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  have hrem : (∑' ρ : {ρ : ZetaZerosInTraceStrip (1 / 2) | α ≤ |(ρ : ℂ).re - 1 / 2|},
      zetaTraceTerm φ (1 / 2) ρ) = 0 := by
    rw [← e.tsum_eq]
    exact MasulloRH.omitted_spectral_mass_zero α hα φ hφ
  rw [hrem, sub_zero] at hEq
  have : (∑' ρ : ZetaZerosInTraceStrip α, zetaTraceTerm φ α ρ) =
      (mellin φ (1 / 2) + mellin φ (-1 / 2)) -
        ((∫ t in Ioi (1 : ℝ), realTraceIntegrand φ t) +
          ∑' i : Nat.Primes × ℕ, primePowerTraceTerm φ i) := by
    rw [hEq]; ring
  rw [← this]
  exact hS.hasSum
