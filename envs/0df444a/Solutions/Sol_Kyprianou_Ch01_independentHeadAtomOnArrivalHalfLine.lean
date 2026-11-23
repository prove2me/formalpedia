-- Prove2me | solution 1 for Kyprianou.Ch01.independentHeadAtomOnArrivalHalfLine
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @pageman
-- created : 2026-11-23T19:52:15.820066+00:00
-- url     : https://prove2.me/submissions/08edd717-da0a-4773-b28e-9e6f559c406d
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_Kyprianou_Ch01_independentHeadAtomIntegratesFrozenPopulation

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
    (K : PopulationLaws)
    (y : ℕ) (hy : 0 < y) (t : ℝ≥0) (ht : 0 < t) (k j : ℕ)
    (hPop : ∀ s : ℝ≥0,
      Q {ω | (compoundPoissonToBranching
          (integerCompoundPoisson ((y - 1) + j)
            (fun n w => arrival (n + 1) w)
            (fun n w => marks (n + 1) w)) s ω).toNat = k} =
        K ((y - 1) + j) s k) :
    (Q {ω |
        marks 0 ω = (j : ℝ) - 1 ∧
        (compoundPoissonToBranching
          (integerCompoundPoisson
            ((y - 1) + j)
            (fun n w => arrival (n + 1) w)
            (fun n w => marks (n + 1) w))
          (Real.toNNReal ((t : ℝ) - arrival 0 ω / (y : ℝ)))
          ω).toNat = k ∧
        ¬ ((y : ℝ) * (t : ℝ) < arrival 0 ω)}).toReal =
      ∫ z in Iic ((y : ℝ) * (t : ℝ)) ×ˢ {((j : ℝ) - 1)},
        (K ((y - 1) + j)
          (Real.toNNReal ((t : ℝ) - z.1 / (y : ℝ))) k).toReal
        ∂(expMeasure (rate : ℝ)).prod jumpLaw := by
  have hset :
      {ω |
        marks 0 ω = (j : ℝ) - 1 ∧
        (compoundPoissonToBranching
          (integerCompoundPoisson ((y - 1) + j)
            (fun n w => arrival (n + 1) w)
            (fun n w => marks (n + 1) w))
          (Real.toNNReal ((t : ℝ) - arrival 0 ω / (y : ℝ)))
          ω).toNat = k ∧
        ¬ ((y : ℝ) * (t : ℝ) < arrival 0 ω)} =
      {ω |
        marks 0 ω = (j : ℝ) - 1 ∧
        (compoundPoissonToBranching
          (integerCompoundPoisson ((y - 1) + j)
            (fun n w => arrival (n + 1) w)
            (fun n w => marks (n + 1) w))
          (Real.toNNReal ((t : ℝ) - arrival 0 ω / (y : ℝ)))
          ω).toNat = k ∧
        arrival 0 ω ≤ (y : ℝ) * (t : ℝ)} := by
    ext ω
    simp [not_lt]
  rw [hset]
  rw [independentHeadAtomIntegratesFrozenPopulation Q rate hrate offspring hNoZeroJumps arrival
      marks jumpLaw hSupport hHeadLaw hHeadTailIndependent y hy t ht k j]
  refine setIntegral_congr_fun (measurableSet_Iic.prod (measurableSet_singleton _)) ?_
  intro z _
  dsimp
  rw [hPop (Real.toNNReal ((t : ℝ) - z.1 / (y : ℝ)))]
