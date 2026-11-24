-- Prove2me | solution 1 for Kyprianou.Ch01.sequenceBranchingCountMeasurable
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @pageman
-- created : 2026-11-24T02:42:24.695828+00:00
-- url     : https://prove2.me/submissions/06356199-935c-49db-90ef-81bb6adf9d74
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_Kyprianou_Ch01_BranchingClocks
import Definitions.Def_Kyprianou_Ch01_LampertiInverse
import Definitions.Def_Kyprianou_Ch01_BranchingGenerator
import Definitions.Def_LeanLevy_Processes_CompoundPoisson
import Theorems.Thm_Kyprianou_Ch01_sequenceDirectBranchingCountMeasurable

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
    (z : ℕ) (s : ℝ≥0) :
    Measurable
      (fun seq : (ℕ → ℝ) × (ℕ → ℝ) =>
        (compoundPoissonToBranching
          (integerCompoundPoisson z
            (fun n (_ : Unit) => seq.1 n)
            (fun n (_ : Unit) => seq.2 n))
          s ()).toNat) := by
  have hdirect := sequenceDirectBranchingCountMeasurable z s
  have hfun :
      (fun seq : (ℕ → ℝ) × (ℕ → ℝ) =>
          (compoundPoissonToBranching
            (integerCompoundPoisson z
              (fun n (_ : Unit) => seq.1 n)
              (fun n (_ : Unit) => seq.2 n))
            s ()).toNat) =
        (fun seq : (ℕ → ℝ) × (ℕ → ℝ) =>
          (compoundPoissonToBranching
            (integerCompoundPoisson z
              (fun n (σ : (ℕ → ℝ) × (ℕ → ℝ)) => σ.1 n)
              (fun n (σ : (ℕ → ℝ) × (ℕ → ℝ)) => σ.2 n))
            s seq).toNat) := by
    funext seq
    refine congrArg Int.toNat ?_
    exact (compoundPoissonToBranching_of_path_eq
      (integerCompoundPoisson z
        (fun n (σ : (ℕ → ℝ) × (ℕ → ℝ)) => σ.1 n)
        (fun n (σ : (ℕ → ℝ) × (ℕ → ℝ)) => σ.2 n))
      (integerCompoundPoisson z
        (fun n (_ : Unit) => seq.1 n)
        (fun n (_ : Unit) => seq.2 n))
      seq
      (fun t => integerWalk_eq_frozenSequences
        (fun n (σ : (ℕ → ℝ) × (ℕ → ℝ)) => σ.1 n)
        (fun n (σ : (ℕ → ℝ) × (ℕ → ℝ)) => σ.2 n) z seq t)
      s).symm
  exact hfun ▸ hdirect
