-- Prove2me | solution 1 for Kyprianou.Ch01.reverseLampertiProductAncestorConvolutionPMF
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-23T11:09:04.07204+00:00
-- url     : https://prove2.me/submissions/1fdc83d7-8499-4067-9ebd-57dae06a9581

import Mathlib
import Definitions.Def_Kyprianou_Ch01_BranchingClocks
import Definitions.Def_Kyprianou_Ch01_LampertiInverse
import Definitions.Def_Kyprianou_Ch01_BranchingGenerator
import Definitions.Def_LeanLevy_Processes_CompoundPoisson
import Theorems.Thm_Kyprianou_Ch01_reverseLampertiNonexplosiveStateAEMeasurable
import Theorems.Thm_Kyprianou_Ch01_independentProductPMFSumLaw
open MeasureTheory ProbabilityTheory Kyprianou.Ch01 Set Filter
open scoped NNReal ENNReal
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
    (a b : ℕ) (t : ℝ≥0) (k : ℕ) :
    (Q.prod Q)
      {ζ : Ω × Ω |
        (compoundPoissonToBranching
          (integerCompoundPoisson a arrival marks) t ζ.1).toNat +
        (compoundPoissonToBranching
          (integerCompoundPoisson b arrival marks) t ζ.2).toNat = k} =
    ((K a t).bind (fun n => (K b t).map (fun m => n + m))) k := by
  let F : ℕ → ℝ≥0 → Ω → ℕ :=
    fun y t ω => (compoundPoissonToBranching
      (integerCompoundPoisson y arrival marks) t ω).toNat
  have hMeas := Kyprianou.Ch01.reverseLampertiNonexplosiveStateAEMeasurable
    Q rate hrate offspring hNoZeroJumps arrival marks
    jumpLaw hdriver hSupport hJumpMass hNoExplosion
  have hPa (n : ℕ) : Q {ω | F a t ω = n} = (K a t) n := by
    exact (hRealisation a t n).symm
  have hPb (n : ℕ) : Q {ω | F b t ω = n} = (K b t) n := by
    exact (hRealisation b t n).symm
  exact Kyprianou.Ch01.independentProductPMFSumLaw
    Q (F a t) (F b t) (hMeas a t) (hMeas b t)
    (K a t) (K b t) hPa hPb k

