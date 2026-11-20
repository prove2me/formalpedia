-- Prove2me | solution 1 for Kyprianou.Ch01.stableAlphaOneCanonicalFromTripletPhase
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-19T16:06:17.451185+00:00
-- url     : https://prove2.me/submissions/b3a2d0bf-f074-4cb6-b9e6-f9da5c582571

import Mathlib.Probability.Distributions.Beta
import Definitions.Def_Kyprianou_Ch01_LevyTripletExponent
import Theorems.Thm_Kyprianou_Ch01_stableAlphaOneScaleSkewSignIdentity
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Complex Real Set Kyprianou.Ch01
set_option autoImplicit false

theorem solution
    (T : ProbabilityTheory.LevyKhintchineTriple)
    (cpos cneg : ℝ) (hsum : 0 < cpos + cneg)
    (hphase : ∃ k : ℝ, ∀ xi : ℝ,
      -Kyprianou.Ch01.levyTripleExponent T xi =
        (((Real.pi * (cpos + cneg) * |xi| / 2 : ℝ) : ℂ) +
          Complex.I * ((((cpos - cneg) * xi * Real.log |xi| : ℝ) : ℂ)) -
          Complex.I * ((((T.drift + (cpos - cneg) * k) * xi : ℝ) : ℂ)))) :
    ∃ c beta eta : ℝ,
      0 < c ∧ beta = (cpos - cneg) / (cpos + cneg) ∧
      ∀ xi : ℝ,
        let sgn : ℝ := if 0 < xi then 1 else if xi < 0 then -1 else 0
        (-Kyprianou.Ch01.levyTripleExponent T xi =
          ((c * |xi| : ℝ) : ℂ) *
            (1 + Complex.I *
              (((beta * (2 / Real.pi) * sgn * Real.log |xi| : ℝ) : ℂ))) +
          Complex.I * (((eta * xi : ℝ) : ℂ))) := by
  obtain ⟨k, hk⟩ := hphase
  let c : ℝ := Real.pi * (cpos + cneg) / 2
  let beta : ℝ := (cpos - cneg) / (cpos + cneg)
  let eta : ℝ := -T.drift - (cpos - cneg) * k
  refine ⟨c, beta, eta, ?_, rfl, ?_⟩
  · dsimp [c]
    positivity
  intro xi sgn
  have hsign :
      c * |xi| * beta * (2 / Real.pi) * sgn =
        (cpos - cneg) * xi := by
    simpa [c, beta, sgn] using
      Kyprianou.Ch01.stableAlphaOneScaleSkewSignIdentity
        cpos cneg xi hsum
  have hlog :
      c * |xi| * beta * (2 / Real.pi) * sgn * Real.log |xi| =
        (cpos - cneg) * xi * Real.log |xi| :=
    congrArg (fun u : ℝ => u * Real.log |xi|) hsign
  have hc : c * |xi| = Real.pi * (cpos + cneg) * |xi| / 2 := by
    dsimp [c]
    ring
  have heta :
      eta * xi = -((T.drift + (cpos - cneg) * k) * xi) := by
    dsimp [eta]
    ring
  rw [hk xi]
  calc
    (((Real.pi * (cpos + cneg) * |xi| / 2 : ℝ) : ℂ) +
        Complex.I * ((((cpos - cneg) * xi * Real.log |xi| : ℝ) : ℂ)) -
        Complex.I * ((((T.drift + (cpos - cneg) * k) * xi : ℝ) : ℂ))) =
      (((c * |xi| : ℝ) : ℂ) +
        Complex.I * (((c * |xi| * beta * (2 / Real.pi) * sgn *
          Real.log |xi| : ℝ) : ℂ)) +
        Complex.I * (((eta * xi : ℝ) : ℂ))) := by
          rw [hlog, heta, hc]
          push_cast
          ring
    _ = ((c * |xi| : ℝ) : ℂ) *
        (1 + Complex.I *
          (((beta * (2 / Real.pi) * sgn * Real.log |xi| : ℝ) : ℂ))) +
          Complex.I * (((eta * xi : ℝ) : ℂ)) := by
            push_cast
            ring
