-- Prove2me | solution 1 for MasulloRH.trace_formula_rational_record_windows
-- status  : ACCEPTED   (prove)
-- author  : @marozols
-- created : 2026-11-21T02:13:10.294027+00:00
-- url     : https://prove2.me/submissions/db4b3935-aed7-448a-b45b-0e726ba20acc

import Definitions.Def_MasulloRH_RegularizedTrace
import Theorems.Thm_TowardsGRH_LW56e2_b83dbbd_dirichlet_zero_free_bound
import Theorems.Thm_MasulloAudit_trace_formula_rational_fixed_window_iff
import Theorems.Thm_MasulloRH_regularized_trace_finite_height_error
import Mathlib

open MeasureTheory Set
open MasulloRH

private theorem zero_real_upper {s : ℂ} (hz : riemannZeta s = 0) (hs : s.re < 1) :
    s.re ≤ 0.8749570698 := by
  by_contra! h
  have hne : s ≠ 1 := fun he => by simpa [he] using hs
  have hfree := TowardsGRH_LW56e2_b83dbbd.dirichlet_zero_free_bound (1 : DirichletCharacter ℂ 1) h (fun he => hne he.2)
  simpa [hz] using hfree

private theorem center_bound (z : ZetaZerosInTraceStrip (1/2)) : |z.val.re-1/2| ≤ 0.3749570698 := by
  have hnot (j : ℕ) : z.val ≠ -j := by
    intro he; have h := congrArg Complex.re he; simp only [Complex.neg_re,Complex.natCast_re] at h
    linarith [z.prop.2.1,j.cast_nonneg (α:=ℝ)]
  have hnot1 : z.val ≠ 1 := by
    intro he; have h := congrArg Complex.re he; rw [Complex.one_re] at h; linarith [z.prop.2.2.1]
  have hzero : riemannZeta (1-z.val)=0 := by rw [riemannZeta_one_sub hnot hnot1,z.prop.1,mul_zero]
  have hlow := zero_real_upper hzero (by simp; linarith [z.prop.2.1])
  simp only [Complex.sub_re,Complex.one_re] at hlow
  have hu := zero_real_upper z.prop.1 z.prop.2.2.1
  exact abs_le.mpr ⟨by linarith,by linarith⟩

theorem solution (α : ℝ) (hα : 0.3749570698 < α) :
    (∀ (φ : ℝ → ℂ), IsRationalTraceTest φ →
      IntegrableOn (realTraceIntegrand φ) (Ioi 1) ∧
      Summable (primePowerTraceTerm φ) ∧
      Summable (zetaTraceTerm φ α) ∧
      (∫ t in Ioi (1 : ℝ), realTraceIntegrand φ t) +
        (∑' i : Nat.Primes × ℕ, primePowerTraceTerm φ i) =
        mellin φ (1 / 2) + mellin φ (-1 / 2) -
          ∑' ρ : ZetaZerosInTraceStrip α, zetaTraceTerm φ α ρ) ∧
      (∀ s : ℂ, (3/2:ℝ) < s.re → regularizedTraceRHS α s = zetaLogDeriv s) := by
  have hstrip (z : ZetaZerosInTraceStrip (1/2)) : |z.val.re - 1/2| < α := (center_bound z).trans_lt hα
  constructor
  · exact (MasulloAudit.trace_formula_rational_fixed_window_iff α (by linarith)).2 hstrip
  · intro s hs
    have h := regularized_trace_finite_height_error α 0 ‖s‖ s le_rfl hs
    have he : ‖zetaLogDeriv s - regularizedTraceRHS α s‖ ≤ 0 := by
      have ht (z : ZetaZerosInTraceStrip (1/2)) : ¬ α ≤ |z.val.re-1/2| := (hstrip z).not_ge
      simpa only [ht, false_and, ite_false, tsum_zero, sub_zero, mul_zero] using h
    exact (sub_eq_zero.mp (norm_le_zero_iff.mp he)).symm

