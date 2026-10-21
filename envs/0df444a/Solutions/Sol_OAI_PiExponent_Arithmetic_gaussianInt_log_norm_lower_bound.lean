-- Prove2me | solution 1 for OAI.PiExponent.Arithmetic.gaussianInt_log_norm_lower_bound
-- status  : ACCEPTED   (prove)
-- author  : @polylog
-- created : 2026-10-20T18:03:36.491898+00:00
-- url     : https://prove2.me/submissions/5fa195e8-bb68-4f36-978f-9872984621b6

import Definitions.Def_OAI_NumberTheory_PiExponent_Approximation_DeterminantContradiction_CoreData

open scoped BigOperators

/-- If multiplying a nonzero complex number by a positive integer gives a Gaussian integer,
the number's logarithmic norm is at least the negative logarithm of that integer. -/
theorem solution {D : ℕ} {z : ℂ} (hD : 0 < D) (hz : z ≠ 0) (g : GaussianInt)
    (hg : (D : ℂ) * z = (g : ℂ)) : -Real.log (D : ℝ) ≤ Real.log ‖z‖ := by
  have hDc : (D : ℂ) ≠ 0 := by exact_mod_cast hD.ne'
  -- A nonzero Gaussian integer has norm at least one.
  have hg0 : g ≠ 0 := by
    rintro rfl
    rw [GaussianInt.toComplex_zero, mul_eq_zero] at hg
    rcases hg with h | h
    · exact hDc h
    · exact hz h
  have hnorm1 : (1 : ℝ) ≤ ‖(g : ℂ)‖ := by
    have hpos : 0 < g.norm := GaussianInt.norm_pos.mpr hg0
    have h1 : (1 : ℝ) ≤ (g.norm : ℝ) := by exact_mod_cast hpos
    rw [GaussianInt.intCast_real_norm, Complex.normSq_eq_norm_sq] at h1
    nlinarith [norm_nonneg (g : ℂ)]
  -- Taking norms in `D * z = g` gives `D * ‖z‖ = ‖g‖`.
  have hnormeq : (D : ℝ) * ‖z‖ = ‖(g : ℂ)‖ := by
    have h := congrArg norm hg
    rw [norm_mul, Complex.norm_natCast] at h
    exact h
  have hzge : (1 : ℝ) / D ≤ ‖z‖ := by
    rw [div_le_iff₀ (by exact_mod_cast hD)]
    nlinarith [hnormeq, hnorm1]
  have hlog := Real.log_le_log (show (0 : ℝ) < (1 : ℝ) / D by positivity) hzge
  rw [Real.log_div (by norm_num) (by exact_mod_cast hD.ne')] at hlog
  simpa using hlog
