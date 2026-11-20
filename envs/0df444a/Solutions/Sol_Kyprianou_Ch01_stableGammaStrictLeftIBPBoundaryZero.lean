-- Prove2me | solution 1 for Kyprianou.Ch01.stableGammaStrictLeftIBPBoundaryZero
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-19T11:24:58.718175+00:00
-- url     : https://prove2.me/submissions/eb5e4292-52ce-41da-a889-7f05b5c461c7

import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.SetSemiring
import Theorems.Thm_Kyprianou_Ch01_stableGammaStrictLeftIBPNearZero
import Theorems.Thm_Kyprianou_Ch01_stableGammaStrictLeftIBPAtInfinity
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Complex Real Set Filter
set_option autoImplicit false

theorem solution
    (alpha : ℝ) (h0 : 0 < alpha) (h1 : alpha < 1)
    (w : ℂ) (hwre : w.re < 0) :
    Tendsto
      (fun r : ℝ => (Complex.exp (w * (r : ℂ)) - 1) * (((r ^ (-alpha) / (-alpha) : ℝ)) : ℂ))
      (nhdsWithin (0 : ℝ) (Set.Ioi (0 : ℝ))) (nhds (0 : ℂ)) ∧
    Tendsto
      (fun r : ℝ => (Complex.exp (w * (r : ℂ)) - 1) * (((r ^ (-alpha) / (-alpha) : ℝ)) : ℂ))
      Filter.atTop (nhds (0 : ℂ)) := by
  exact ⟨Kyprianou.Ch01.stableGammaStrictLeftIBPNearZero
      alpha h0 h1 w hwre,
    Kyprianou.Ch01.stableGammaStrictLeftIBPAtInfinity
      alpha h0 h1 w hwre⟩
