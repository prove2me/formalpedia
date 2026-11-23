-- Prove2me | solution 1 for Kyprianou.Ch01.markProductIntegratesFrozenArrival
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @pageman
-- created : 2026-11-23T20:41:31.831264+00:00
-- url     : https://prove2.me/submissions/d0b7fb46-2fc0-4e8b-acb4-f2da6951135d
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_Kyprianou_Ch01_jumpAtomIntegratesFrozenArrival

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
      ∫ a in Iic ((y : ℝ) * (t : ℝ)),
        (Q {ω |
            (compoundPoissonToBranching
              (integerCompoundPoisson
                ((y - 1) + j)
                (fun n w => arrival (n + 1) w)
                (fun n w => marks (n + 1) w))
              (Real.toNNReal ((t : ℝ) - a / (y : ℝ)))
              ω).toNat = k} *
          Q {ω | marks 0 ω = (j : ℝ) - 1}).toReal
        ∂expMeasure (rate : ℝ) := by
  rw [jumpAtomIntegratesFrozenArrival Q rate hrate offspring hNoZeroJumps arrival marks
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
  refine setIntegral_congr_fun measurableSet_Iic ?_
  intro _ _
  dsimp
  rw [hmarg]
