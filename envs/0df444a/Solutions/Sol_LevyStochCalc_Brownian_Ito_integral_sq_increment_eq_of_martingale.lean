-- Prove2me | solution 1 for LevyStochCalc.Brownian.Ito.integral_sq_increment_eq_of_martingale
-- status  : ACCEPTED   (prove)
-- author  : @I am wealthy
-- created : 2026-11-22T05:03:01.195805+00:00
-- url     : https://prove2.me/submissions/de7e7719-bc10-40b4-994f-e4caa7b25135

import Mathlib.Probability.Martingale.Basic
import Mathlib.MeasureTheory.Function.ConditionalExpectation.PullOut
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Tactic.Ring

open MeasureTheory
open scoped NNReal ENNReal

universe u
variable {Ω : Type u} [MeasurableSpace Ω]

private theorem conditionalSquareIncrement
    {P : MeasureTheory.Measure Ω} [MeasureTheory.IsProbabilityMeasure P]
    {ℱ : MeasureTheory.Filtration ℝ ‹MeasurableSpace Ω›}
    {M : ℝ → Ω → ℝ}
    (hmart : MeasureTheory.Martingale M ℱ P)
    {s t : ℝ} (hMs : MeasureTheory.MemLp (M s) 2 P) (hMt : MeasureTheory.MemLp (M t) 2 P)
    (hst : s ≤ t) :
    P[(fun ω => (M t ω - M s ω) ^ 2) | ℱ s]
      =ᵐ[P] fun ω => (P[(fun ω => (M t ω) ^ 2) | ℱ s]) ω - (M s ω) ^ 2 := by
  let A := fun ω => (M t ω) ^ 2
  let B := M t * M s
  let C := fun ω => (M s ω) ^ 2
  have hA : Integrable A P := hMt.integrable_sq
  have hB : Integrable B P := hMt.integrable_mul hMs
  have hC : Integrable C P := hMs.integrable_sq
  have hsplit : (fun ω => (M t ω - M s ω) ^ 2) = A - B - B + C := by
    funext ω
    change (M t ω - M s ω) ^ 2 =
      (M t ω)^2 - M t ω * M s ω - M t ω * M s ω + (M s ω)^2
    ring
  have hfix : P[C | ℱ s] = C :=
    condExp_of_stronglyMeasurable (ℱ.le s) ((hmart.stronglyMeasurable s).pow 2) hC
  have hprod := condExp_mul_of_stronglyMeasurable_right
    (hmart.stronglyMeasurable s) hB (hmart.integrable t)
  rw [hsplit]
  filter_upwards [condExp_add ((hA.sub hB).sub hB) hC (ℱ s),
    condExp_sub (hA.sub hB) hB (ℱ s), condExp_sub hA hB (ℱ s),
    hprod, hmart.condExp_ae_eq hst] with ω hadd hsub₂ hsub₁ hp hm
  change (P[A - B - B + C | ℱ s]) ω = (P[A | ℱ s]) ω - (M s ω)^2
  simp only [Pi.add_apply, Pi.sub_apply, Pi.mul_apply] at hadd hsub₂ hsub₁ hp
  change (P[B | ℱ s]) ω = (P[M t | ℱ s]) ω * M s ω at hp
  rw [hadd, hsub₂, hsub₁, hp, hm, hfix]
  change _ - _ - _ + (M s ω)^2 = _
  ring

theorem solution
    {P : MeasureTheory.Measure Ω} [MeasureTheory.IsProbabilityMeasure P]
    {ℱ : MeasureTheory.Filtration ℝ ‹MeasurableSpace Ω›}
    {M : ℝ → Ω → ℝ}
    (hmart : MeasureTheory.Martingale M ℱ P)
    {s t : ℝ} (hMs : MeasureTheory.MemLp (M s) 2 P) (hMt : MeasureTheory.MemLp (M t) 2 P)
    (hst : s ≤ t) :
    ∫ ω, (M t ω - M s ω) ^ 2 ∂P
      = (∫ ω, (M t ω) ^ 2 ∂P) - ∫ ω, (M s ω) ^ 2 ∂P := by
  have hce := conditionalSquareIncrement hmart hMs hMt hst
  calc
    _ = ∫ ω, (P[(fun ω => (M t ω - M s ω)^2) | ℱ s]) ω ∂P :=
      (integral_condExp (ℱ.le s)).symm
    _ = ∫ ω, (P[(fun ω => (M t ω)^2) | ℱ s]) ω - (M s ω)^2 ∂P :=
      integral_congr_ae hce
    _ = _ := by rw [integral_sub integrable_condExp hMs.integrable_sq, integral_condExp (ℱ.le s)]

#print axioms solution
