-- Prove2me | solution 1 for Kyprianou.Ch01.inverseGaussianGammaDifferenceRescaled
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-19T18:36:49.503093+00:00
-- url     : https://prove2.me/submissions/f66d36c4-63f0-4c03-9e6b-6a782d2bebe3

import Mathlib
import Definitions.Def_Kyprianou_Ch01_ExplicitLevyExamples
import Theorems.Thm_Kyprianou_Ch01_stableGammaStrictLeftDeficitDifference
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Complex ProbabilityTheory Kyprianou.Ch01
set_option autoImplicit false

theorem solution
    (b : ℝ) (hb : 0 < b) (theta : ℝ) :
    (((1 / Real.sqrt (2 * Real.pi) : ℝ)) : ℂ) * (∫ r in Set.Ioi (0 : ℝ),
        (Complex.exp (((-(b ^ 2 / 2) : ℝ) : ℂ) * (r : ℂ)) - Complex.exp ((((-(b ^ 2 / 2) : ℝ) : ℂ) +
            Complex.I * (theta : ℂ)) * (r : ℂ))) *
          ((r ^ (-(3 / 2 : ℝ)) : ℝ) : ℂ) ∂volume) =
    (((Real.Gamma (-(1 / 2 : ℝ)) / Real.sqrt (2 * Real.pi) : ℝ) : ℂ)) *
      (Complex.exp (((1 / 2 : ℝ) : ℂ) *
          Complex.log (((b ^ 2 / 2 : ℝ) : ℂ))) - Complex.exp (((1 / 2 : ℝ) : ℂ) *
          Complex.log ((((b ^ 2 / 2 : ℝ) : ℂ) -
            Complex.I * (theta : ℂ))))) := by
  let u : ℂ := ((-(b ^ 2 / 2) : ℝ) : ℂ)
  let v : ℂ := u + Complex.I * (theta : ℂ)
  have hu : u.re < 0 := by
    dsimp [u]
    nlinarith [sq_pos_of_pos hb]
  have hv : v.re < 0 := by
    simpa [v, Complex.add_re, Complex.mul_re] using hu
  have h :=
    Kyprianou.Ch01.stableGammaStrictLeftDeficitDifference
      (1 / 2 : ℝ) (by norm_num) (by norm_num) u v hu hv
  have hp (r : ℝ) :
      r ^ (-(1 / 2 : ℝ) - 1) = r ^ (-(3 / 2 : ℝ)) := by
    congr 1
    ring
  have hu' : -u = (((b ^ 2 / 2 : ℝ) : ℂ)) := by
    simp only [u, Complex.ofReal_neg, neg_neg]
  have hv' : -v = (((b ^ 2 / 2 : ℝ) : ℂ) -
      Complex.I * (theta : ℂ)) := by
    rw [show v = u + Complex.I * (theta : ℂ) from rfl, neg_add, hu']
    ring
  simp_rw [hp] at h
  change ((1 / Real.sqrt (2 * Real.pi) : ℝ) : ℂ) *
      (∫ r in Set.Ioi (0 : ℝ),
        (Complex.exp (u * (r : ℂ)) - Complex.exp (v * (r : ℂ))) *
        ((r ^ (-(3 / 2 : ℝ)) : ℝ) : ℂ) ∂volume) = _
  rw [h]
  rw [hu', hv']
  push_cast
  ring
