-- Prove2me | solution 1 for Kyprianou.Ch01.frozenArrivalScalesByJumpMass
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @pageman
-- created : 2026-11-23T21:00:14.955851+00:00
-- url     : https://prove2.me/submissions/30cfaa36-bd72-4744-9fb1-80e7d14842e8
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_Kyprianou_Ch01_frozenArrivalIntegratesHeadRectangle

open MeasureTheory ProbabilityTheory Kyprianou.Ch01 Set
open scoped NNReal ENNReal
set_option autoImplicit false

theorem solution
    {Ω : Type*} [MeasurableSpace Ω]
    (Q : Measure Ω) [IsProbabilityMeasure Q]
    (rate : ℝ≥0) (hrate : 0 < rate)
    (offspring : PMF ℕ) (hNoZeroJumps : offspring 1 = 0)
    (arrival marks : ℕ → Ω → ℝ)
    (jumpLaw : Measure ℝ) [IsProbabilityMeasure jumpLaw]
    (hSupport : jumpLaw
      {x : ℝ | ∃ k : ℕ, x = (k : ℝ) - 1} = 1)
    (hHeadLaw : HasLaw (fun w => (arrival 0 w, marks 0 w))
      ((expMeasure rate).prod jumpLaw) Q)
    (hHeadTailIndependent : IndepFun
      (fun w => (arrival 0 w, marks 0 w))
      (fun w => ((fun n : ℕ => arrival (n + 1) w),
                 (fun n : ℕ => marks (n + 1) w))) Q)
    (y : ℕ) (hy : 0 < y) (t : ℝ≥0) (ht : 0 < t) (k j : ℕ) :
    (Q ({ω | marks 0 ω = (j : ℝ) - 1} ∩
        {ω |
          (compoundPoissonToBranching
            (integerCompoundPoisson
              ((y - 1) + j)
              (fun n w => arrival (n + 1) w)
              (fun n w => marks (n + 1) w))
            (Real.toNNReal ((t : ℝ) - arrival 0 ω / (y : ℝ)))
            ω).toNat = k ∧
          arrival 0 ω ≤ (y : ℝ) * (t : ℝ)})).toReal =
      (∫ a in Iic ((y : ℝ) * (t : ℝ)),
        (Q {ω |
            (compoundPoissonToBranching
              (integerCompoundPoisson
                ((y - 1) + j)
                (fun n w => arrival (n + 1) w)
                (fun n w => marks (n + 1) w))
              (Real.toNNReal ((t : ℝ) - a / (y : ℝ)))
              ω).toNat = k}).toReal
        ∂expMeasure (rate : ℝ)) *
        (jumpLaw {((j : ℝ) - 1)}).toReal := by
  let φ : ℝ → ℝ := fun a =>
    (Q {ω |
        (compoundPoissonToBranching
          (integerCompoundPoisson ((y - 1) + j)
            (fun n w => arrival (n + 1) w)
            (fun n w => marks (n + 1) w))
          (Real.toNNReal ((t : ℝ) - a / (y : ℝ))) ω).toNat = k}).toReal
  let s : Set ℝ := Iic ((y : ℝ) * (t : ℝ))
  let u : Set ℝ := {((j : ℝ) - 1)}
  rw [frozenArrivalIntegratesHeadRectangle Q rate hrate offspring hNoZeroJumps arrival marks
      jumpLaw hSupport hHeadLaw hHeadTailIndependent y hy t ht k j]
  have : IsProbabilityMeasure (expMeasure (rate : ℝ)) :=
    isProbabilityMeasure_expMeasure (NNReal.coe_pos.mpr hrate)
  have hunit :
      (∫ z in s ×ˢ u, φ z.1 ∂(expMeasure (rate : ℝ)).prod jumpLaw) =
        ∫ z in s ×ˢ u, φ z.1 * (1 : ℝ) ∂(expMeasure (rate : ℝ)).prod jumpLaw := by
    refine setIntegral_congr_fun (measurableSet_Iic.prod (measurableSet_singleton _)) ?_
    intro _ _
    ring
  rw [hunit, setIntegral_prod_mul φ (fun _ : ℝ => (1 : ℝ)) s u]
  have hmark : ∫ m in u, (1 : ℝ) ∂jumpLaw = (jumpLaw {((j : ℝ) - 1)}).toReal := by
    rw [setIntegral_const]
    change (jumpLaw {((j : ℝ) - 1)}).toReal * (1 : ℝ) = (jumpLaw {((j : ℝ) - 1)}).toReal
    ring
  rw [hmark]
