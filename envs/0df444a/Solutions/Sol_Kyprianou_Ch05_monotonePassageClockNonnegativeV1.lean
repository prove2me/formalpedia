-- Prove2me | solution 1 for Kyprianou.Ch05.monotonePassageClockNonnegativeV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T21:49:58.994099+00:00
-- url     : https://prove2.me/submissions/a5b2a718-3bd4-44b7-91c1-3eac5aebbfd2

import Mathlib
import Theorems.Thm_Kyprianou_Ch01_monotoneStrictUpperClockInfEqRational
import Definitions.Def_Kyprianou_Ch05_KilledSubordinatorPotential
import Definitions.Def_Kyprianou_Ch05_FirstPassageObservables
import Definitions.Def_Kyprianou_Ch05_RenewalMeasure
import Definitions.Def_Kyprianou_Ch05_TailRatioClassL
open MeasureTheory Filter ProbabilityTheory
open scoped NNReal ENNReal
set_option autoImplicit false

open Set Topology Kyprianou.Ch05
open scoped Classical Topology
theorem solution
    (x : ℝ) (hx : 0 ≤ x) :
    ∃ T : (NNReal → ℝ) → ENNReal, Measurable T ∧
      ∀ f : NNReal → ℝ, Monotone f → f 0 = 0 →
        T f = sInf ((fun t : NNReal => (t : ENNReal)) '' {t : NNReal | 0 < t ∧ x < f t}) := by
  classical
  let T : (NNReal → ℝ) → ENNReal := fun f =>
    ⨅ r : ℚ, if x < f (Real.toNNReal (r : ℝ)) then
      (Real.toNNReal (r : ℝ) : ENNReal) else ⊤
  refine ⟨T,?_,?_⟩
  · exact Measurable.iInf fun r => Measurable.ite
      (measurableSet_lt measurable_const (measurable_pi_apply _))
      measurable_const measurable_const
  · intro f hm hz
    have h := Kyprianou.Ch01.monotoneStrictUpperClockInfEqRational
      (fun t => ENNReal.ofReal (f t)) (ENNReal.ofReal_mono.comp hm) (ENNReal.ofReal x)
    simp only [ENNReal.ofReal_lt_ofReal_iff_of_nonneg hx] at h
    have he : {z : ENNReal | ∃ u : NNReal, (u : ENNReal) = z ∧ x < f u} =
        (fun t : NNReal => (t : ENNReal)) '' {t : NNReal | 0 < t ∧ x < f t} := by
      ext z
      constructor
      · rintro ⟨u,rfl,hu⟩
        have hp : 0 < u := by
          by_contra! h0
          have : u = 0 := le_antisymm h0 bot_le
          rw [this,hz] at hu
          exact (not_lt_of_ge hx) hu
        exact ⟨u,⟨hp,hu⟩,rfl⟩
      · rintro ⟨u,hu,rfl⟩
        exact ⟨u,rfl,hu.2⟩
    change T f = _
    rw [← he]
    exact h.symm
