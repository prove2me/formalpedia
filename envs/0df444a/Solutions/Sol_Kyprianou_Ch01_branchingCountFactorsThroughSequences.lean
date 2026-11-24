-- Prove2me | solution 1 for Kyprianou.Ch01.branchingCountFactorsThroughSequences
-- status  : ACCEPTED   (prove)
-- author  : @pageman
-- created : 2026-11-24T02:14:11.059883+00:00
-- url     : https://prove2.me/submissions/fbb2b7a2-7396-41fe-ab9f-3b568b3e6451

import Mathlib
import Definitions.Def_Kyprianou_Ch01_BranchingClocks
import Definitions.Def_Kyprianou_Ch01_LampertiInverse
import Definitions.Def_Kyprianou_Ch01_BranchingGenerator
import Definitions.Def_LeanLevy_Processes_CompoundPoisson

open MeasureTheory ProbabilityTheory Kyprianou.Ch01
open scoped NNReal ENNReal
set_option autoImplicit false

private theorem integerWalk_eq_frozenSequences
    {Ω : Type*} (arrival marks : ℕ → Ω → ℝ) (z : ℕ) (ω : Ω) (t : ℝ≥0) :
    integerCompoundPoisson z arrival marks t ω =
      integerCompoundPoisson z
        (fun n (_ : Unit) => arrival n ω)
        (fun n (_ : Unit) => marks n ω) t () := by
  simp [integerCompoundPoisson, ProbabilityTheory.compoundPoisson,
    ProbabilityTheory.arrival, ProbabilityTheory.piecewisePath, ProbabilityTheory.jumpCount]

private theorem compoundPoissonToBranching_of_path_eq
    {Ω : Type*} (X : ℝ≥0 → Ω → ℤ) (X' : ℝ≥0 → Unit → ℤ) (ω : Ω)
    (h : ∀ t, X t ω = X' t ()) (s : ℝ≥0) :
    compoundPoissonToBranching X s ω = compoundPoissonToBranching X' s () := by
  have hocc : ∀ u, reciprocalOccupation X u ω = reciprocalOccupation X' u () := by
    intro u
    simp [reciprocalOccupation, h]
  have hpass : firstNegativePassage X ω = firstNegativePassage X' () := by
    unfold firstNegativePassage
    have hex : (∃ t : ℝ≥0, 0 < t ∧ X t ω < 0) ↔ (∃ t : ℝ≥0, 0 < t ∧ X' t () < 0) := by
      constructor <;> rintro ⟨t, ht⟩ <;> exact ⟨t, by simpa [h] using ht⟩
    have hset : {t : ℝ≥0 | 0 < t ∧ X t ω < 0} = {t : ℝ≥0 | 0 < t ∧ X' t () < 0} := by
      ext t; simp [h]
    rw [hex, hset]
  have hinv : ∀ u, inverseReciprocalOccupation X u ω = inverseReciprocalOccupation X' u () := by
    intro u
    unfold inverseReciprocalOccupation
    have hex : (∃ s : ℝ≥0, (u : ℝ≥0∞) < reciprocalOccupation X s ω) ↔
        (∃ s : ℝ≥0, (u : ℝ≥0∞) < reciprocalOccupation X' s ()) := by
      constructor <;> rintro ⟨s, hs⟩ <;> exact ⟨s, by simpa [hocc] using hs⟩
    have hset : {s : ℝ≥0 | (u : ℝ≥0∞) < reciprocalOccupation X s ω} =
        {s : ℝ≥0 | (u : ℝ≥0∞) < reciprocalOccupation X' s ()} := by
      ext s; simp [hocc]
    rw [hex, hset]
  unfold compoundPoissonToBranching
  rw [hinv s, hpass]
  cases (min (inverseReciprocalOccupation X' s ()) (firstNegativePassage X' ()) :
      WithTop ℝ≥0) with
  | top => rfl
  | coe t =>
    change X t ω = X' t ()
    exact h t

theorem solution
    {Ω : Type*} [MeasurableSpace Ω]
    (Q : Measure Ω) [IsProbabilityMeasure Q]
    (rate : ℝ≥0)
    (arrival marks : ℕ → Ω → ℝ)
    (jumpLaw : Measure ℝ) [IsProbabilityMeasure jumpLaw]
    (hNoExplosion : ∀ y : ℕ, ∀ᵐ ω ∂Q,
      ∀ t : ℝ≥0, ∃ s : ℝ≥0,
        (t : ℝ≥0∞) <
          reciprocalOccupation (integerCompoundPoisson y arrival marks) s ω)
    (hTailDriver : IsCompoundPoissonDriver
      (fun n w => arrival (n + 1) w)
      (fun n w => marks (n + 1) w) rate jumpLaw Q)
    (ν : Measure ((ℕ → ℝ) × (ℕ → ℝ)))
    (hOrig : HasLaw (fun w => (fun n => arrival n w, fun n => marks n w)) ν Q)
    (hShift : HasLaw
      (fun w => (fun n => arrival (n + 1) w, fun n => marks (n + 1) w)) ν Q)
    (z : ℕ) (s : ℝ≥0) (m : ℕ) :
    (∀ ω,
        (compoundPoissonToBranching
          (integerCompoundPoisson z
            (fun n w => arrival (n + 1) w)
            (fun n w => marks (n + 1) w)) s ω).toNat =
          (compoundPoissonToBranching
            (integerCompoundPoisson z
              (fun n (_ : Unit) => arrival (n + 1) ω)
              (fun n (_ : Unit) => marks (n + 1) ω))
            s ()).toNat) ∧
      ∀ ω,
        (compoundPoissonToBranching
          (integerCompoundPoisson z arrival marks) s ω).toNat =
          (compoundPoissonToBranching
            (integerCompoundPoisson z
              (fun n (_ : Unit) => arrival n ω)
              (fun n (_ : Unit) => marks n ω))
            s ()).toNat := by
  refine ⟨?_, ?_⟩
  · intro ω
    refine congrArg Int.toNat ?_
    exact compoundPoissonToBranching_of_path_eq
        (integerCompoundPoisson z
          (fun n w => arrival (n + 1) w)
          (fun n w => marks (n + 1) w))
        (integerCompoundPoisson z
          (fun n (_ : Unit) => arrival (n + 1) ω)
          (fun n (_ : Unit) => marks (n + 1) ω))
        ω (fun t => integerWalk_eq_frozenSequences
          (fun n w => arrival (n + 1) w)
          (fun n w => marks (n + 1) w) z ω t) s
  · intro ω
    refine congrArg Int.toNat ?_
    exact compoundPoissonToBranching_of_path_eq
        (integerCompoundPoisson z arrival marks)
        (integerCompoundPoisson z
          (fun n (_ : Unit) => arrival n ω)
          (fun n (_ : Unit) => marks n ω))
        ω (fun t => integerWalk_eq_frozenSequences arrival marks z ω t) s
