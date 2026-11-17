-- Prove2me | solution 1 for Kyprianou.Ch01.charFun_scaledBrownianZeroStart
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-16T22:05:33.719847+00:00
-- url     : https://prove2.me/submissions/95f12484-de56-4b03-a065-64563e6329d8

import Mathlib
import Theorems.Thm_Kyprianou_Ch01_isPreBrownianReal_initial_zero_ae
import Theorems.Thm_Kyprianou_Ch01_brownianInitialValueNormalization
import Theorems.Thm_Kyprianou_Ch01_gaussianScaledMarginalCharFun
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Complex
open scoped NNReal
set_option autoImplicit false

theorem solution
    {Ω : Type} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (X : ℝ≥0 → Ω → ℝ)
    (hB : IsBrownianReal X P)
    (v : ℝ≥0) (t : ℝ≥0) (xi : ℝ) :
    charFun (P.map
      (fun ω => Real.sqrt (v : ℝ) * (X t ω - X 0 ω))) xi =
      Complex.exp (-(((v : ℝ) * (t : ℝ) : ℂ) * (xi : ℂ) ^ 2 / 2)) := by
  have hzero : ∀ᵐ ω ∂P, X 0 ω = 0 :=
    Kyprianou.Ch01.isPreBrownianReal_initial_zero_ae
      P X hB.toIsPreBrownianReal
  have hpre : IsPreBrownianReal
      (fun t ω => X t ω - X 0 ω) P :=
    Kyprianou.Ch01.brownianInitialValueNormalization
      P X hB.toIsPreBrownianReal hzero
  have hscale : HasLaw (fun x : ℝ => Real.sqrt (v : ℝ) * x)
      ((gaussianReal 0 t).map (fun x : ℝ => Real.sqrt (v : ℝ) * x))
      (gaussianReal 0 t) := by
    exact ⟨(measurable_const.mul measurable_id).aemeasurable, rfl⟩
  have hlaw := hscale.comp (hpre.hasLaw_eval t)
  change charFun (P.map
    ((fun x : ℝ => Real.sqrt (v : ℝ) * x) ∘
      (fun ω => X t ω - X 0 ω))) xi =
    Complex.exp (-(((v : ℝ) * (t : ℝ) : ℂ) * (xi : ℂ) ^ 2 / 2))
  rw [hlaw.map_eq]
  exact Kyprianou.Ch01.gaussianScaledMarginalCharFun v t xi
