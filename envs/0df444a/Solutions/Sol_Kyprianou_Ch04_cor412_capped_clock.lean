-- Prove2me | solution 1 for Kyprianou.Ch04.cor412_capped_clock
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T08:16:23.833045+00:00
-- url     : https://prove2.me/submissions/320b36d6-e518-478e-bde5-380097969c34

import Mathlib
open MeasureTheory Set
open scoped NNReal ENNReal
set_option autoImplicit false

/-- A finite representative of the minimum of an extended stopping time and a deterministic cap is a stopping time. -/
theorem solution
    {Ω : Type} [mΩ : MeasurableSpace Ω]
    (F : Filtration NNReal mΩ)
    (τ : Ω → WithTop NNReal) (hτ : IsStoppingTime F τ)
    (n : NNReal) (T : Ω → NNReal)
    (hT : ∀ w, (T w : WithTop NNReal) = min (τ w) (n : WithTop NNReal)) :
    IsStoppingTime F (fun w => (T w : WithTop NNReal)) := by
  rw [funext hT]
  exact hτ.min_const n
