-- Prove2me | solution 1 for Kyprianou.Ch01.reverseLampertiPositiveTimeFirstJumpRenewal
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @pageman
-- created : 2026-11-23T13:34:16.481985+00:00
-- url     : https://prove2.me/submissions/92df7a4c-19a8-4363-a66d-b11dcdf6449c
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_Kyprianou_Ch01_BranchingClocks
import Definitions.Def_Kyprianou_Ch01_LampertiInverse
import Definitions.Def_Kyprianou_Ch01_BranchingGenerator
import Definitions.Def_LeanLevy_Processes_CompoundPoisson
import Theorems.Thm_Kyprianou_Ch01_reverseLampertiZeroBranchingTimeAbsorbed
import Theorems.Thm_Kyprianou_Ch01_reverseLampertiNoJumpStateRemainsInitial
import Theorems.Thm_Kyprianou_Ch01_reverseLampertiFirstJumpRestartIntegral
import Theorems.Thm_Kyprianou_Ch01_reverseLampertiFirstArrivalSurvival

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
          (integerCompoundPoisson y arrival marks) t ω).toNat = k}) :
    (∀ t : ℝ≥0, ∀ k : ℕ, K 0 t k = (PMF.pure 0) k) ∧
      ∀ y : ℕ, 0 < y → ∀ t : ℝ≥0, 0 < t → ∀ k : ℕ,
        IntervalIntegrable
          (fun s : ℝ =>
            ((rate : ℝ) * (y : ℝ)) * Real.exp (-(((rate : ℝ) * (y : ℝ)) * s)) *
              ∑' j : ℕ, (offspring j).toReal *
                (K ((y - 1) + j) (Real.toNNReal ((t : ℝ) - s)) k).toReal)
          volume 0 (t : ℝ) ∧
        (K y t k).toReal =
          (if k = y then Real.exp (-((rate : ℝ) * (y : ℝ) * (t : ℝ))) else 0) +
            ∫ s in (0 : ℝ)..(t : ℝ),
              ((rate : ℝ) * (y : ℝ)) * Real.exp (-(((rate : ℝ) * (y : ℝ)) * s)) *
                ∑' j : ℕ, (offspring j).toReal *
                  (K ((y - 1) + j) (Real.toNNReal ((t : ℝ) - s)) k).toReal := by
  refine ⟨reverseLampertiZeroBranchingTimeAbsorbed Q rate hrate offspring hNoZeroJumps
      arrival marks jumpLaw hdriver hSupport hJumpMass hNoExplosion K hRealisation, ?_⟩
  intro y hy t ht k
  obtain ⟨hInt, hPost⟩ :=
    reverseLampertiFirstJumpRestartIntegral Q rate hrate offspring hNoZeroJumps
      arrival marks jumpLaw hdriver hSupport hJumpMass hNoExplosion K hRealisation
      y hy t ht k
  have hPre :=
    reverseLampertiNoJumpStateRemainsInitial Q rate hrate offspring hNoZeroJumps
      arrival marks jumpLaw hdriver hSupport hJumpMass hNoExplosion K hRealisation
      y hy t ht k
  have hSurv :=
    reverseLampertiFirstArrivalSurvival Q rate hrate arrival marks jumpLaw hdriver y t
  let state : Set Ω :=
    {ω | (compoundPoissonToBranching (integerCompoundPoisson y arrival marks) t ω).toNat = k}
  let early : Set Ω :=
    {ω | (y : ℝ) * (t : ℝ) < ProbabilityTheory.arrival arrival 0 ω}
  have hmeas : MeasurableSet early := by
    have hclock : Measurable (fun ω => ProbabilityTheory.arrival arrival 0 ω) := by
      have hfun : (fun ω => ProbabilityTheory.arrival arrival 0 ω) = arrival 0 := by
        funext ω
        unfold ProbabilityTheory.arrival
        simp
      rw [hfun]
      exact hdriver.measurable_interarrival 0
    simpa [early] using measurableSet_lt measurable_const hclock
  have hsplit := measure_inter_add_sdiff (μ := Q) state (t := early) hmeas
  have hAdd :
      (Q state).toReal = (Q (state ∩ early)).toReal + (Q (state \ early)).toReal := by
    rw [← hsplit, ENNReal.toReal_add (measure_ne_top Q _) (measure_ne_top Q _)]
  have hInter : state ∩ early =
      {ω |
        (compoundPoissonToBranching (integerCompoundPoisson y arrival marks) t ω).toNat = k ∧
        (y : ℝ) * (t : ℝ) < ProbabilityTheory.arrival arrival 0 ω} := by
    ext ω
    simp [state, early]
  have hDiff : state \ early =
      {ω |
        (compoundPoissonToBranching (integerCompoundPoisson y arrival marks) t ω).toNat = k ∧
        ¬ ((y : ℝ) * (t : ℝ) < ProbabilityTheory.arrival arrival 0 ω)} := by
    ext ω
    simp [state, early]
  have hHold :
      (Q (state ∩ early)).toReal =
        if k = y then Real.exp (-((rate : ℝ) * (y : ℝ) * (t : ℝ))) else 0 := by
    rw [hInter, hPre]
    split_ifs with hk
    · rw [hSurv]
      exact congrArg Real.exp (by ring)
    · rfl
  refine ⟨hInt, ?_⟩
  rw [hRealisation y t k, hAdd, hDiff, hPost, hHold]
