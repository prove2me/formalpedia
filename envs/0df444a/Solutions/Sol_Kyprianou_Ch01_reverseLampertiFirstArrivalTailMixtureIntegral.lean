-- Prove2me | solution 1 for Kyprianou.Ch01.reverseLampertiFirstArrivalTailMixtureIntegral
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @pageman
-- created : 2026-11-23T17:43:05.016804+00:00
-- url     : https://prove2.me/submissions/9d1e2a24-444a-467e-87e7-1f50ba4fb5be
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_Kyprianou_Ch01_reverseLampertiFirstArrivalPoissonClockMixture

open MeasureTheory ProbabilityTheory Kyprianou.Ch01 Set Filter intervalIntegral
open scoped NNReal ENNReal BigOperators Interval
set_option autoImplicit false

theorem solution
    {Ω : Type*} [MeasurableSpace Ω]
    (Q : Measure Ω) [IsProbabilityMeasure Q]
    (rate : ℝ≥0) (hrate : 0 < rate)
    (offspring : PMF ℕ) (hNoZeroJumps : offspring 1 = 0)
    (arrival marks : ℕ → Ω → ℝ)
    (jumpLaw : Measure ℝ) [IsProbabilityMeasure jumpLaw]
    (hdriver : IsCompoundPoissonDriver arrival marks rate jumpLaw Q)
    (hSupport : jumpLaw
      {x : ℝ | ∃ k : ℕ, x = (k : ℝ) - 1} = 1)
    (hJumpMass : ∀ k : ℕ,
      jumpLaw ({((k : ℝ) - 1)} : Set ℝ) = offspring k)
    (hNoExplosion : ∀ y : ℕ, ∀ᵐ ω ∂Q,
      ∀ t : ℝ≥0, ∃ s : ℝ≥0,
        (t : ℝ≥0∞) <
          reciprocalOccupation (integerCompoundPoisson y arrival marks) s ω)
    (K : PopulationLaws)
    (hRealisation : ∀ (y : ℕ) (t : ℝ≥0) (k : ℕ),
      K y t k =
        Q {ω | (compoundPoissonToBranching
          (integerCompoundPoisson y arrival marks) t ω).toNat = k})
    (y : ℕ) (hy : 0 < y) (t : ℝ≥0) (ht : 0 < t) (k : ℕ) :
    (Q { ω |
          (compoundPoissonToBranching
            (integerCompoundPoisson
              ((y - 1) +
                (Int.floor (marks 0 ω + 1)).toNat)
              (fun n w => arrival (n + 1) w)
              (fun n w => marks (n + 1) w))
            (Real.toNNReal
              ((t : ℝ) -
                ProbabilityTheory.arrival arrival 0 ω / (y : ℝ)))
            ω).toNat = k ∧
          ¬ ((y : ℝ) * (t : ℝ) <
          ProbabilityTheory.arrival arrival 0 ω) }).toReal =
        ∫ s in (0 : ℝ)..(t : ℝ),
          ((rate : ℝ) * (y : ℝ)) * Real.exp (-(((rate : ℝ) * (y : ℝ)) * s)) *
            ∑' j : ℕ, (offspring j).toReal *
              (K ((y - 1) + j) (Real.toNNReal ((t : ℝ) - s)) k).toReal := by
  have hClock :=
    reverseLampertiFirstArrivalPoissonClockMixture Q rate hrate offspring hNoZeroJumps
      arrival marks jumpLaw hdriver hSupport hJumpMass hNoExplosion K hRealisation
      y hy t ht k
  rw [hClock]
  let f : ℝ → ℝ := fun a =>
    (rate : ℝ) * Real.exp (-((rate : ℝ) * a)) *
      ∑' j : ℕ, (offspring j).toReal *
        (K ((y - 1) + j) (Real.toNNReal ((t : ℝ) - a / (y : ℝ))) k).toReal
  have hscale :
      (y : ℝ) * ∫ s in (0 : ℝ)..(t : ℝ), f ((y : ℝ) * s) =
        ∫ a in (0 : ℝ)..(y : ℝ) * (t : ℝ), f a := by
    simp [smul_eq_mul, mul_zero, smul_integral_comp_mul_left f (y : ℝ)]
  rw [← hscale]
  rw [← intervalIntegral.integral_const_mul (y : ℝ) (fun s => f ((y : ℝ) * s))]
  refine intervalIntegral.integral_congr fun s _ => ?_
  have hy0 : (y : ℝ) ≠ 0 := mod_cast hy.ne'
  dsimp only [f]
  have hdiv : ((y : ℝ) * s) / (y : ℝ) = s := by field_simp
  rw [hdiv]
  have hexp :
      Real.exp (-((rate : ℝ) * ((y : ℝ) * s))) =
        Real.exp (-((rate : ℝ) * (y : ℝ) * s)) := by
    congr 1
    ring
  rw [hexp]
  ring
