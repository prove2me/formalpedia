-- Prove2me | solution 1 for OAI.PiExponent.FormalInterpolation.hasWeightedSupport_of_mem_span
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-19T11:31:27.508843+00:00
-- url     : https://prove2.me/submissions/ec17e63a-4a73-473d-9feb-fc2284d287e4

import Definitions.Def_OAI_PiExponent_WeightedSupport
import Mathlib.RingTheory.Ideal.Operations
import Theorems.Thm_OAI_PiExponent_FormalInterpolation_hasWeightedSupport_add
import Theorems.Thm_OAI_PiExponent_FormalInterpolation_hasWeightedSupport_mul
import Mathlib.RingTheory.MvPowerSeries.Basic

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open OAI.PiExponent OAI.PiExponent.DeterminantContradiction

theorem solution
    {m : ℕ} (v : Fin (m + 1) → ℝ)
    (R : ℝ)
    (f : MvPolynomial (Fin (m + 1)) ℂ →+*
      MvPowerSeries (Fin (m + 1)) ℂ)
    (x : Fin (m + 1) → MvPolynomial (Fin (m + 1)) ℂ)
    (hf0 : ∀ Q, FormalInterpolation.hasWeightedSupport v 0 (f Q))
    (hx : ∀ i, FormalInterpolation.hasWeightedSupport v R (f (x i)))
    (Q : MvPolynomial (Fin (m + 1)) ℂ)
    (hQ : Q ∈ Ideal.span (Set.range x)) :
    FormalInterpolation.hasWeightedSupport v R (f Q) := by
  classical
  refine Submodule.span_induction
    (R := MvPolynomial (Fin (m + 1)) ℂ)
    (s := Set.range x)
    (p := fun q _ => FormalInterpolation.hasWeightedSupport v R (f q))
    ?_ ?_ ?_ ?_ hQ
  · intro q hq
    rcases hq with ⟨i, rfl⟩
    exact hx i
  · intro b hb
    have hFalse : False := by simpa using hb
    exact hFalse.elim
  · intro a b ha hb hfa hfb
    simpa only [map_add] using
      (OAI.PiExponent.FormalInterpolation.hasWeightedSupport_add
        v R (f a) (f b) hfa hfb)
  · intro c q hq hqSupport
    simpa only [smul_eq_mul, map_mul, zero_add] using
      (OAI.PiExponent.FormalInterpolation.hasWeightedSupport_mul
        v 0 R (f c) (f q) (hf0 c) hqSupport)