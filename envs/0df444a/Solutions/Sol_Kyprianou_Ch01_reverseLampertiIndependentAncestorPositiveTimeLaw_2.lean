-- Prove2me | solution 2 for Kyprianou.Ch01.reverseLampertiIndependentAncestorPositiveTimeLaw
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @pageman
-- created : 2026-11-23T13:20:53.466025+00:00
-- url     : https://prove2.me/submissions/8ac55940-f3d9-4a66-9acd-1bfff793cd93
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_Kyprianou_Ch01_BranchingClocks
import Definitions.Def_Kyprianou_Ch01_LampertiInverse
import Definitions.Def_Kyprianou_Ch01_BranchingGenerator
import Definitions.Def_LeanLevy_Processes_CompoundPoisson
import Theorems.Thm_Kyprianou_Ch01_reverseLampertiPositiveTimeFirstJumpRenewal
import Theorems.Thm_Kyprianou_Ch01_branchingFirstJumpRenewalGivesAncestorConvolution
import Theorems.Thm_Kyprianou_Ch01_reverseLampertiProductAncestorConvolutionPMF

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
    (a b : ℕ) (t : ℝ≥0) (ht : 0 < t) (k : ℕ) :
    Q {ω |
        (compoundPoissonToBranching
          (integerCompoundPoisson (a + b) arrival marks) t ω).toNat = k} =
    (Q.prod Q)
      {ζ : Ω × Ω |
        (compoundPoissonToBranching
          (integerCompoundPoisson a arrival marks) t ζ.1).toNat +
        (compoundPoissonToBranching
          (integerCompoundPoisson b arrival marks) t ζ.2).toNat = k} := by
  obtain ⟨hZero, hRenew⟩ :=
    reverseLampertiPositiveTimeFirstJumpRenewal Q rate hrate offspring hNoZeroJumps
      arrival marks jumpLaw hdriver hSupport hJumpMass hNoExplosion K hRealisation
  have hrateR : 0 < (rate : ℝ) := NNReal.coe_pos.mpr hrate
  have hK :=
    branchingFirstJumpRenewalGivesAncestorConvolution (rate : ℝ) hrateR offspring K
      hZero hRenew a b t ht k
  rw [← hRealisation (a + b) t k,
    reverseLampertiProductAncestorConvolutionPMF Q rate hrate offspring hNoZeroJumps
      arrival marks jumpLaw hdriver hSupport hJumpMass hNoExplosion K hRealisation a b t k]
  exact hK
