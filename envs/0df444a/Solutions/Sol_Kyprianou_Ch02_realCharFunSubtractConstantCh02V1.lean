-- Prove2me | solution 1 for Kyprianou.Ch02.realCharFunSubtractConstantCh02V1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-23T22:27:04.020905+00:00
-- url     : https://prove2.me/submissions/ff41b10d-5b5a-4986-b780-ed3bf34eaf04

import Mathlib.MeasureTheory.Measure.CharacteristicFunction.Basic
open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal
set_option autoImplicit false

theorem solution
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    (F : Ω → ℝ) (hF : AEMeasurable F P) (c ξ : ℝ) :
    charFun (P.map (fun ω => F ω - c)) ξ =
      Complex.exp (((-c * ξ : ℝ) : ℂ) * Complex.I) *
        charFun (P.map F) ξ := by
  let g : ℝ → ℂ := fun x => Complex.exp (((ξ * x : ℝ) : ℂ) * Complex.I)
  have hg : Continuous g := by
    dsimp [g]
    fun_prop
  have hmap (Z : Ω → ℝ) (hZ : AEMeasurable Z P) :
      charFun (P.map Z) ξ = ∫ ω, g (Z ω) ∂P := by
    rw [charFun_apply_real]
    simpa only [g, Complex.ofReal_mul] using
      (integral_map hZ hg.aestronglyMeasurable)
  have hshift : AEMeasurable (fun ω => F ω - c) P :=
    hF.sub aemeasurable_const
  rw [hmap (fun ω => F ω - c) hshift, hmap F hF, ← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [] with ω
  dsimp [g]
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring
