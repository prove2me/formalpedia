-- Prove2me | solution 1 for Kyprianou.Ch01.stoppedRealExponentialContinuousTimeChangePublic
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-18T12:44:09.213228+00:00
-- url     : https://prove2.me/submissions/3f23598a-9bc3-4858-82d7-48fef8d432da

import Mathlib.Topology.ContinuousMap.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Data.NNReal.Defs
import Mathlib.Tactic.FunProp
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Filter
open scoped NNReal
set_option autoImplicit false

/-- Convergence of bounded stopping times implies convergence of stopped exponentials. -/
theorem solution
    (f : ℝ≥0 → ℝ) (hf : Continuous f)
    (theta q : ℝ)
    (t : ℕ → ℝ≥0) (tau : ℝ≥0)
    (ht : Tendsto t atTop (nhds tau)) :
    Tendsto
      (fun n : ℕ =>
        Real.exp (theta * f (t n) - q * ((t n) : ℝ)))
      atTop
      (nhds (Real.exp (theta * f tau - q * (tau : ℝ)))) := by
  have hG : Continuous (fun u : ℝ≥0 =>
      Real.exp (theta * f u - q * (u : ℝ))) := by
    fun_prop
  exact (hG.tendsto tau).comp ht
