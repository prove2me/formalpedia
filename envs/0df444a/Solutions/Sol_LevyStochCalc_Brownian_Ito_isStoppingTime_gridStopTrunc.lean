-- Prove2me | solution 1 for LevyStochCalc.Brownian.Ito.isStoppingTime_gridStopTrunc
-- status  : ACCEPTED   (prove)
-- author  : @yuzhou
-- created : 2026-11-22T04:01:00.850853+00:00
-- url     : https://prove2.me/submissions/b030be15-c13e-4d89-813f-6149f144920c

import Definitions.Def_LevyStochCalc_Ito_GridStopTruncated_F000

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# The upward grid discretisation truncated at the horizon

The stopping time that stops at the first point of a uniform grid strictly beyond a stopping time
attains the horizon, so its values are not all grid points strictly below the horizon. Sending it
to `⊤` where it attains the horizon leaves a stopping time whose values are grid points strictly
below the horizon or `⊤`, and changes neither the horizon clipped at it nor an integrand cut off
at it on the closed window, hence neither the Itô integral at the horizon.

## Main statements

* `LevyStochCalc.Brownian.Ito.gridStopTrunc` — the upward grid discretisation of a stopping time,
  sent to `⊤` where it attains the horizon.
* `LevyStochCalc.Brownian.Ito.isStoppingTime_gridStopTrunc` — it is a stopping time.
* `LevyStochCalc.Brownian.Ito.gridStopTrunc_mono` — it is monotone in the stopping time.
* `LevyStochCalc.Brownian.Ito.measurableSpace_le_gridStopTrunc` — the σ-algebra of a stopping
  time is contained in that of its truncated grid discretisation.
* `LevyStochCalc.Brownian.Ito.gridStopTrunc_finiteRange` — its values are grid points strictly
  below the horizon, or `⊤`.
* `LevyStochCalc.Brownian.Ito.clipTime_gridStopTrunc` — the horizon clipped at it is the horizon
  clipped at the grid discretisation.
* `LevyStochCalc.Brownian.Ito.stopped_gridStopTrunc` — an integrand cut off at it agrees on the
  closed window with the integrand cut off at the grid discretisation.
* `LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian_congr_of_le_horizon` — the Itô integral
  at a horizon depends on the integrand only on the window up to that horizon.
* `LevyStochCalc.Brownian.Ito.itoFormula_between_gridStop_of_gridStopTrunc` — Itô's formula
  between the grid discretisations of two stopping times, from the identity between their
  truncations.
-/

namespace LevyStochCalc.Brownian.Ito

open MeasureTheory ProbabilityTheory LevyStochCalc.Brownian.Multidim
open scoped NNReal ENNReal Topology

universe u

section Truncate

variable {Ω : Type u}

end Truncate

section FiniteRange

variable {Ω : Type u}

end FiniteRange

section StoppingTime

variable {Ω : Type u} [MeasurableSpace Ω]



theorem _root_.solution {ℱ : Filtration ℝ ‹MeasurableSpace Ω›}
    {σ : Ω → WithTop ℝ} (hσ : MeasureTheory.IsStoppingTime ℱ σ) (T : ℝ) (m : ℕ) :
    MeasureTheory.IsStoppingTime ℱ (gridStopTrunc σ T m) := by
  have hgrid : MeasureTheory.IsStoppingTime ℱ (gridStop σ T m) := by
    first | exact isStoppingTime_gridStop hσ T m | exact?
  intro t
  by_cases ht : t < T
  · have he : {ω | gridStopTrunc σ T m ω ≤ (t : WithTop ℝ)} =
        {ω | gridStop σ T m ω ≤ (t : WithTop ℝ)} := by
      ext ω
      by_cases h : (T : WithTop ℝ) ≤ gridStop σ T m ω
      · rw [Set.mem_setOf_eq, Set.mem_setOf_eq, gridStopTrunc_of_le σ T m h]
        have hn : ¬ gridStop σ T m ω ≤ (t : WithTop ℝ) := by
          intro h'
          exact (not_le_of_gt ht) (by exact_mod_cast h.trans h')
        simp [hn]
      · simp [gridStopTrunc, h]
    rw [he]
    exact hgrid t
  · have hTt := le_of_not_gt ht
    have he : {ω | gridStopTrunc σ T m ω ≤ (t : WithTop ℝ)} =
        {ω | gridStop σ T m ω < (T : WithTop ℝ)} := by
      ext ω
      by_cases h : (T : WithTop ℝ) ≤ gridStop σ T m ω
      · simp [gridStopTrunc, h, not_lt_of_ge h]
      · have h' : gridStop σ T m ω < (T : WithTop ℝ) := lt_of_not_ge h
        have h'' : gridStop σ T m ω ≤ (t : WithTop ℝ) := h'.le.trans (by exact_mod_cast hTt)
        simp [gridStopTrunc, h, h', h'']
    rw [he]
    have hm : MeasurableSet[ℱ T] {ω | gridStop σ T m ω < (T : WithTop ℝ)} := by
      first | exact hgrid.measurableSet_lt T | exact?
    exact ℱ.mono hTt _ hm
