-- Prove2me | solution 2 for MasulloRH.trace_formula_rational
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @nlehmann
-- created : 2026-11-20T22:25:59.568426+00:00
-- url     : https://prove2.me/submissions/9fce7f71-03b2-444b-af7f-b99e26884bdc
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_MasulloRH_trace_formula_rational_full_strip
import Theorems.Thm_MasulloRH_zero_free_right

set_option autoImplicit false

open MeasureTheory Set
open scoped Topology

/-- Under `zero_free_right` and the functional equation, every zeta zero in the open
critical strip lies on the critical line. -/
lemma MasulloRH_critical_zero_re_eq_half (ρ : ℂ) (hz : riemannZeta ρ = 0)
    (h0 : 0 < ρ.re) (h1 : ρ.re < 1) : ρ.re = 1 / 2 := by
  rcases lt_trichotomy ρ.re (1 / 2) with hlt | heq | hgt
  · exfalso
    have hs : ∀ n : ℕ, ρ ≠ -(n : ℂ) := by
      intro n hn
      have := congrArg Complex.re hn
      simp at this
      linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
    have hs1 : ρ ≠ 1 := by
      intro h; rw [h] at h1; simp at h1
    have hfe := riemannZeta_one_sub hs hs1
    rw [hz, mul_zero] at hfe
    have hre : (1 / 2 : ℝ) < (1 - ρ).re := by simp; linarith
    have hne : (1 - ρ) ≠ 1 := by
      intro h
      have := congrArg Complex.re h
      simp at this
      linarith
    exact MasulloRH.zero_free_right (1 - ρ) hre hne hfe
  · exact heq
  · exfalso
    have hne : ρ ≠ 1 := by
      intro h; rw [h] at h1; simp at h1
    exact MasulloRH.zero_free_right ρ hgt hne hz

/-- For every `α > 0`, the zeros in the `α`-strip are exactly the zeros in the full
critical strip, given `zero_free_right`. -/
noncomputable def MasulloRH_stripEquiv (α : ℝ) (hα : 0 < α) :
    MasulloRH.ZetaZerosInTraceStrip α ≃ MasulloRH.ZetaZerosInTraceStrip (1 / 2) where
  toFun ρ := ⟨ρ.1, ρ.2.1, ρ.2.2.1, ρ.2.2.2.1, by
    rw [MasulloRH_critical_zero_re_eq_half ρ.1 ρ.2.1 ρ.2.2.1 ρ.2.2.2.1]; norm_num⟩
  invFun ρ := ⟨ρ.1, ρ.2.1, ρ.2.2.1, ρ.2.2.2.1, by
    rw [MasulloRH_critical_zero_re_eq_half ρ.1 ρ.2.1 ρ.2.2.1 ρ.2.2.2.1]; simpa using hα⟩
  left_inv ρ := rfl
  right_inv ρ := rfl

theorem solution (α : ℝ) (hα : 0 < α) (φ : ℝ → ℂ)
    (hφ : MasulloRH.IsRationalTraceTest φ) :
    IntegrableOn (MasulloRH.realTraceIntegrand φ) (Ioi 1) ∧
    Summable (MasulloRH.primePowerTraceTerm φ) ∧
    Summable (MasulloRH.zetaTraceTerm φ α) ∧
    (∫ t in Ioi (1 : ℝ), MasulloRH.realTraceIntegrand φ t) +
      (∑' i : Nat.Primes × ℕ, MasulloRH.primePowerTraceTerm φ i) =
      mellin φ (1 / 2) + mellin φ (-1 / 2) -
        ∑' ρ : MasulloRH.ZetaZerosInTraceStrip α, MasulloRH.zetaTraceTerm φ α ρ := by
  obtain ⟨hint, hprime, hzero, hEq⟩ := MasulloRH.trace_formula_rational_full_strip φ hφ
  let e := MasulloRH_stripEquiv α hα
  have hterm : (MasulloRH.zetaTraceTerm φ (1 / 2)) ∘ e = MasulloRH.zetaTraceTerm φ α := rfl
  refine ⟨hint, hprime, ?_, ?_⟩
  · rw [← hterm]; exact e.summable_iff.mpr hzero
  · rw [hEq, ← hterm]
    exact congrArg _ (e.tsum_eq (MasulloRH.zetaTraceTerm φ (1 / 2))).symm
