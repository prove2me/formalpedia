-- Prove2me | solution 1 for Kyprianou.Ch01.brownianCharFun_reflected
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-15T20:55:38.849617+00:00
-- url     : https://prove2.me/submissions/929e324b-099f-45a9-b649-fa6c2da5d2f4

import Mathlib
import Definitions.Def_Kyprianou_Ch01_ExplicitLevyExamples
import Definitions.Def_LeanLevy_Processes_LevyProcess
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true
open MeasureTheory ProbabilityTheory Kyprianou.Ch01
open scoped NNReal ENNReal
set_option autoImplicit false

/-- Reflection changes only the drift of Gaussian one-time characteristic laws. -/
theorem solution
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (X : ℝ≥0 → Ω → ℝ)
    (sigma gamma : ℝ)
    (hX : Kyprianou.Ch01.IsLinearBrownian P X sigma gamma) :
    ∀ (t : ℝ≥0) (xi : ℝ),
      charFun (P.map (fun ω => -X t ω)) xi =
        Complex.exp (((t : ℝ) : ℂ) *
          (Complex.I * (((-gamma) * xi : ℝ) : ℂ) -
            (((sigma ^ 2 * xi ^ 2 / 2 : ℝ)) : ℂ))) := by
  obtain ⟨hlevy, _, hchar⟩ := hX
  intro t xi
  have hxmeas : AEMeasurable (X t) P := by
    have hm := (hlevy.stationary_increments 0 t).aemeasurable_fst
    change AEMeasurable (fun ω => X (0 + t) ω - X 0 ω) P at hm
    simpa [hlevy.start_zero] using hm
  have href := charFun_map_mul_comp hxmeas (-1) xi
  have hmap : charFun (P.map (fun ω => -X t ω)) xi =
      charFun (P.map (X t)) (-xi) := by
    simpa only [neg_one_mul] using href
  rw [hmap, hchar t (-xi)]
  congr 1
  ring
