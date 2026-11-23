-- Prove2me | solution 1 for Kyprianou.Ch01.frozenPopulationScalesByJumpAtom
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @pageman
-- created : 2026-11-23T20:08:26.66385+00:00
-- url     : https://prove2.me/submissions/7aebbf1c-3674-45c1-8144-9f963b43f358
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_Kyprianou_Ch01_markProbabilityScalesFrozenArrival

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
    (Q {ω |
        marks 0 ω = (j : ℝ) - 1 ∧
        (compoundPoissonToBranching
          (integerCompoundPoisson
            ((y - 1) + j)
            (fun n w => arrival (n + 1) w)
            (fun n w => marks (n + 1) w))
          (Real.toNNReal ((t : ℝ) - arrival 0 ω / (y : ℝ)))
          ω).toNat = k ∧
        arrival 0 ω ≤ (y : ℝ) * (t : ℝ)}).toReal =
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
  have hinter :
      {ω |
        marks 0 ω = (j : ℝ) - 1 ∧
        (compoundPoissonToBranching
          (integerCompoundPoisson ((y - 1) + j)
            (fun n w => arrival (n + 1) w)
            (fun n w => marks (n + 1) w))
          (Real.toNNReal ((t : ℝ) - arrival 0 ω / (y : ℝ)))
          ω).toNat = k ∧
        arrival 0 ω ≤ (y : ℝ) * (t : ℝ)} =
      {ω | marks 0 ω = (j : ℝ) - 1} ∩
        {ω |
          (compoundPoissonToBranching
            (integerCompoundPoisson ((y - 1) + j)
              (fun n w => arrival (n + 1) w)
              (fun n w => marks (n + 1) w))
            (Real.toNNReal ((t : ℝ) - arrival 0 ω / (y : ℝ)))
            ω).toNat = k ∧
          arrival 0 ω ≤ (y : ℝ) * (t : ℝ)} := by
    ext ω
    simp
  rw [hinter]
  rw [markProbabilityScalesFrozenArrival Q rate hrate offspring hNoZeroJumps arrival marks
      jumpLaw hSupport hHeadLaw hHeadTailIndependent y hy t ht k j]
  have hp : MeasurableSet {x : ℝ × ℝ | x.2 = (j : ℝ) - 1} :=
    measurable_snd (measurableSet_singleton _)
  have hmarg :
      Q {ω | marks 0 ω = (j : ℝ) - 1} = jumpLaw {((j : ℝ) - 1)} := by
    rw [hHeadLaw.measure_eq hp]
    have hrect : {x : ℝ × ℝ | x.2 = (j : ℝ) - 1} = univ ×ˢ {((j : ℝ) - 1)} := by
      ext x
      simp
    have : IsProbabilityMeasure (expMeasure (rate : ℝ)) :=
      isProbabilityMeasure_expMeasure (NNReal.coe_pos.mpr hrate)
    rw [hrect, Measure.prod_prod, measure_univ, one_mul]
  rw [hmarg]
