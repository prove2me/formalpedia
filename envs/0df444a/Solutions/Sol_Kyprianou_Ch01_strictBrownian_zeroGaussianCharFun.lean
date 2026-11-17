-- Prove2me | solution 1 for Kyprianou.Ch01.strictBrownian_zeroGaussianCharFun
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-16T21:24:19.91218+00:00
-- url     : https://prove2.me/submissions/14ce6b61-62f5-4dc2-9fdc-7465a8070e7b

import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess
open MeasureTheory ProbabilityTheory Complex
open scoped NNReal
set_option autoImplicit false


theorem Kyprianou.Ch01.strictBrownian_zeroGaussianCharFun
    {Ω : Type} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (X : ℝ≥0 → Ω → ℝ)
    (hB : IsBrownianReal X P) (t : ℝ≥0) (xi : ℝ) :
    charFun (P.map (fun ω => X t ω - X 0 ω)) xi =
      Complex.exp (-(((t : ℝ) : ℂ) * (xi : ℂ) ^ 2 / 2)) := by
  have h := hB.toIsPreBrownianReal.hasLaw_sub t 0
  have hm : P.map (fun ω => X t ω - X 0 ω) = gaussianReal 0 (nndist (t : ℝ) ((0 : ℝ≥0) : ℝ)) :=
    h.map_eq
  have hd : nndist (t : ℝ) ((0 : ℝ≥0) : ℝ) = t := by
    ext; simp
  rw [hm, hd, charFun_gaussianReal]
  congr 1
  push_cast
  ring

theorem solution
    {Ω : Type} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (X : ℝ≥0 → Ω → ℝ)
    (hB : IsBrownianReal X P) (t : ℝ≥0) (xi : ℝ) :
    charFun (P.map (fun ω => X t ω - X 0 ω)) xi =
      Complex.exp (-(((t : ℝ) : ℂ) * (xi : ℂ) ^ 2 / 2)) :=
  Kyprianou.Ch01.strictBrownian_zeroGaussianCharFun P X hB t xi

