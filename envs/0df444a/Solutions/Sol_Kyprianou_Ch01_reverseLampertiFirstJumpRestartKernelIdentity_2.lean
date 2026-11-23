-- Prove2me | solution 2 for Kyprianou.Ch01.reverseLampertiFirstJumpRestartKernelIdentity
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @pageman
-- created : 2026-11-23T16:38:45.781543+00:00
-- url     : https://prove2.me/submissions/b7fcc317-cb1d-4191-8e68-addcb862c3ba
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_Kyprianou_Ch01_reverseLampertiFirstArrivalShiftedTailPathwise
import Theorems.Thm_Kyprianou_Ch01_reverseLampertiFirstArrivalTailMixtureIntegral

open MeasureTheory ProbabilityTheory Kyprianou.Ch01 Set Filter
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
    (Q {ω |
          (compoundPoissonToBranching
            (integerCompoundPoisson y arrival marks) t ω).toNat = k ∧
          ¬ ((y : ℝ) * (t : ℝ) < ProbabilityTheory.arrival arrival 0 ω)}).toReal =
        ∫ s in (0 : ℝ)..(t : ℝ),
          ((rate : ℝ) * (y : ℝ)) * Real.exp (-(((rate : ℝ) * (y : ℝ)) * s)) *
            ∑' j : ℕ, (offspring j).toReal *
              (K ((y - 1) + j) (Real.toNNReal ((t : ℝ) - s)) k).toReal := by
  let restarted : Ω → ℕ := fun ω =>
    (compoundPoissonToBranching
      (integerCompoundPoisson
        ((y - 1) + (Int.floor (marks 0 ω + 1)).toNat)
        (fun n w => arrival (n + 1) w)
        (fun n w => marks (n + 1) w))
      (Real.toNNReal
        ((t : ℝ) - ProbabilityTheory.arrival arrival 0 ω / (y : ℝ)))
      ω).toNat
  let here : Set Ω :=
    {ω |
      (compoundPoissonToBranching
        (integerCompoundPoisson y arrival marks) t ω).toNat = k ∧
      ¬ ((y : ℝ) * (t : ℝ) < ProbabilityTheory.arrival arrival 0 ω)}
  let there : Set Ω :=
    {ω |
      restarted ω = k ∧
      ¬ ((y : ℝ) * (t : ℝ) < ProbabilityTheory.arrival arrival 0 ω)}
  have hPath :=
    reverseLampertiFirstArrivalShiftedTailPathwise Q rate hrate offspring hNoZeroJumps
      arrival marks jumpLaw hdriver hSupport hJumpMass hNoExplosion K hRealisation
      y hy t ht k
  have hMix :=
    reverseLampertiFirstArrivalTailMixtureIntegral Q rate hrate offspring hNoZeroJumps
      arrival marks jumpLaw hdriver hSupport hJumpMass hNoExplosion K hRealisation
      y hy t ht k
  have hEq : here =ᵐ[Q] there := by
    filter_upwards [hPath] with ω hω
    dsimp only [here, there, restarted]
    apply propext
    constructor
    · rintro ⟨hk, hjump⟩
      exact ⟨(hω hjump).symm.trans hk, hjump⟩
    · rintro ⟨hk, hjump⟩
      exact ⟨(hω hjump).trans hk, hjump⟩
  have hMeasure : Q here = Q there := measure_congr hEq
  simp only [here, there, restarted] at hMeasure
  rw [hMeasure]
  exact hMix
