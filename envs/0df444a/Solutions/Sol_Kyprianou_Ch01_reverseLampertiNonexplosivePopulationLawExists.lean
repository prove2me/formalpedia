-- Prove2me | solution 1 for Kyprianou.Ch01.reverseLampertiNonexplosivePopulationLawExists
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-22T20:48:56.022177+00:00
-- url     : https://prove2.me/submissions/3a1c17ff-5568-47f1-90e3-00d7b3362133

import Mathlib
import Definitions.Def_Kyprianou_Ch01_BranchingClocks
import Definitions.Def_Kyprianou_Ch01_LampertiInverse
import Definitions.Def_Kyprianou_Ch01_BranchingGenerator
import Definitions.Def_LeanLevy_Processes_CompoundPoisson
import Theorems.Thm_Kyprianou_Ch01_aemeasurableNaturalRandomVariableHasPMF
import Theorems.Thm_Kyprianou_Ch01_reverseLampertiNonexplosiveStateAEAndInitialMass
open MeasureTheory ProbabilityTheory Kyprianou.Ch01 Set Filter
open scoped NNReal ENNReal
set_option autoImplicit false

/-- The a.e.-measurable reverse time-change yields exact PMF transition
laws, and its initial atom identities yield deterministic starting states. -/
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
          reciprocalOccupation
            (integerCompoundPoisson y arrival marks) s ω) :
    ∃ K : PopulationLaws,
      (∀ y : ℕ, K y 0 = PMF.pure y) ∧
      ∀ (y : ℕ) (t : ℝ≥0) (k : ℕ),
        K y t k =
          Q {ω | (compoundPoissonToBranching
            (integerCompoundPoisson y arrival marks) t ω).toNat = k} := by
  classical
  obtain ⟨hAE, hInitial⟩ :=
    Kyprianou.Ch01.reverseLampertiNonexplosiveStateAEAndInitialMass
      Q rate hrate offspring hNoZeroJumps
      arrival marks jumpLaw hdriver hSupport hJumpMass hNoExplosion
  let f : ℕ → ℝ≥0 → Ω → ℕ := fun y t ω =>
    (compoundPoissonToBranching
      (integerCompoundPoisson y arrival marks) t ω).toNat
  have hWitness : ∀ y t, ∃ p : PMF ℕ,
      ∀ k : ℕ, p k = Q {ω | f y t ω = k} := by
    intro y t
    exact Kyprianou.Ch01.aemeasurableNaturalRandomVariableHasPMF
      Q (f y t) (hAE y t)
  let K : PopulationLaws := fun y t => Classical.choose (hWitness y t)
  have hKlaw : ∀ y t k,
      K y t k =
        Q {ω | (compoundPoissonToBranching
          (integerCompoundPoisson y arrival marks) t ω).toNat = k} := by
    intro y t k
    simpa only [K, f] using (Classical.choose_spec (hWitness y t) k)
  refine ⟨K, ?_, hKlaw⟩
  intro y
  apply PMF.ext
  intro k
  exact (hKlaw y 0 k).trans (hInitial y k)
