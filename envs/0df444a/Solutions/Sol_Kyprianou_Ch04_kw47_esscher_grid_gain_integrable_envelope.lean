-- Prove2me | solution 1 for Kyprianou.Ch04.kw47_esscher_grid_gain_integrable_envelope
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-25T20:58:08.439045+00:00
-- url     : https://prove2.me/submissions/9d45cacc-a1f4-4895-87b0-c4263d1a9a19

import Mathlib
import Theorems.Thm_Kyprianou_Ch04_kw47_universal_exp_runningSup_integrable
open MeasureTheory ProbabilityTheory AvramDividend.Classical
open scoped NNReal ENNReal
set_option autoImplicit false

/-- The mesh-independent uniform dominating envelope for exact
Kella-Whitt Esscher product-grid sums is integrable. -/
theorem solution
    {Ω : Type} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {F : Filtration NNReal mΩ}
    (L : SpectrallyNegativeLevy P F)
    (alpha : Real) (hAlpha : 0 ≤ alpha) (T : NNReal) :
    Integrable (fun w : Ω =>
      4 * Real.exp (alpha * runningSup L T w +
          |L.ψ alpha| * (T : Real)) *
        Real.exp (|L.ψ alpha| * (T : Real))) P := by
  have hU := Kyprianou.Ch04.kw47_universal_exp_runningSup_integrable
    L alpha hAlpha T
  have hC := hU.const_mul
    (4 * Real.exp (|L.ψ alpha| * (T : Real)) *
       Real.exp (|L.ψ alpha| * (T : Real)))
  convert hC using 1
  funext w
  rw [Real.exp_add]
  ring
