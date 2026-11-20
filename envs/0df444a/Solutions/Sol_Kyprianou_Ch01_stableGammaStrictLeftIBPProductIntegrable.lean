-- Prove2me | solution 1 for Kyprianou.Ch01.stableGammaStrictLeftIBPProductIntegrable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-19T11:20:44.457817+00:00
-- url     : https://prove2.me/submissions/3642e4cf-ac9f-432a-b0e3-d0bf5a75ff7d

import Mathlib
import Theorems.Thm_Kyprianou_Ch01_stableGammaComplexDeficitIntegrable
import Theorems.Thm_Kyprianou_Ch01_stableGammaStrictLeftMellinIntegrable
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Complex Real Set Filter
set_option autoImplicit false

/-- Both exact stable gamma IBP integrands admit absolute Lebesgue integrals. -/
theorem solution
    (alpha : ℝ) (h0 : 0 < alpha) (h1 : alpha < 1)
    (w : ℂ) (hwre : w.re < 0) :
    IntegrableOn
      (fun r : ℝ => (Complex.exp (w * (r : ℂ)) - 1) *
        (((r ^ (-alpha - 1) : ℝ)) : ℂ))
      (Set.Ioi (0 : ℝ)) ∧
    IntegrableOn
      (fun r : ℝ => (w * Complex.exp (w * (r : ℂ))) *
        (((r ^ (-alpha) / (-alpha) : ℝ)) : ℂ))
      (Set.Ioi (0 : ℝ)) := by
  have hw : w ≠ 0 := by
    intro h
    simp [h] at hwre
  have hleft :=
    Kyprianou.Ch01.stableGammaComplexDeficitIntegrable
      alpha h0 h1 w hw hwre.le
  have hα : (alpha : ℂ) ≠ 0 := by
    exact_mod_cast (ne_of_gt h0)
  have hright :=
    Kyprianou.Ch01.stableGammaStrictLeftMellinIntegrable
      alpha h0 h1 w hwre
  have hs := hright.const_mul (-(w / (alpha : ℂ)))
  refine ⟨hleft, ?_⟩
  apply (integrableOn_congr_fun (fun r hr => ?_) measurableSet_Ioi).mpr hs
  push_cast
  field_simp [hα]
