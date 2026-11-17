-- Prove2me | solution 1 for Kyprianou.Ch06.exponentialSurvivalFiniteAlmostSurely
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-16T08:41:26.215363+00:00
-- url     : https://prove2.me/submissions/b51a89e1-38d8-4ef8-98dc-f8e6261e0d6f

import Mathlib
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Topology
open scoped NNReal ENNReal
set_option autoImplicit false

theorem solution
    {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (T : Omega → WithTop NNReal) (rate : Real)
    (hRate : 0 < rate)
    (hSurv : ∀ t : NNReal,
      P {omega | (t : WithTop NNReal) < T omega} =
        ENNReal.ofReal (Real.exp (-(rate * (t : Real))))) :
    P {omega | T omega = ⊤} = 0 := by
  have hUpper : ∀ n : Nat,
      P {omega | T omega = ⊤} ≤
        ENNReal.ofReal (Real.exp (-((n : Real) * rate))) := by
    intro n
    have hSubset : {omega | T omega = ⊤} ⊆
        {omega | ((n : NNReal) : WithTop NNReal) < T omega} := by
      intro omega hTop
      change T omega = ⊤ at hTop
      simpa [hTop] using (WithTop.coe_lt_top (n : NNReal))
    calc
      P {omega | T omega = ⊤} ≤
          P {omega | ((n : NNReal) : WithTop NNReal) < T omega} :=
            measure_mono hSubset
      _ = ENNReal.ofReal (Real.exp (-((n : Real) * rate))) := by
        simpa [mul_comm] using hSurv (n : NNReal)
  have hToTop : Tendsto (fun n : Nat => (n : Real) * rate)
      atTop atTop := by
    exact (Filter.tendsto_mul_const_atTop_of_pos hRate).2
      tendsto_natCast_atTop_atTop
  have hToBot : Tendsto (fun n : Nat => -((n : Real) * rate))
      atTop atBot := Filter.tendsto_neg_atTop_atBot.comp hToTop
  have hExp : Tendsto (fun n : Nat =>
      Real.exp (-((n : Real) * rate))) atTop (nhds 0) :=
    Real.tendsto_exp_atBot.comp hToBot
  have hExpNN : Tendsto (fun n : Nat =>
      ENNReal.ofReal (Real.exp (-((n : Real) * rate))))
      atTop (nhds (0 : ENNReal)) := by
    simpa only [Function.comp_def, ENNReal.ofReal_zero] using
      (ENNReal.continuous_ofReal.tendsto (0 : Real)).comp hExp
  have hle : P {omega | T omega = ⊤} ≤ 0 :=
    ge_of_tendsto hExpNN (Filter.Eventually.of_forall hUpper)
  exact le_antisymm hle bot_le
