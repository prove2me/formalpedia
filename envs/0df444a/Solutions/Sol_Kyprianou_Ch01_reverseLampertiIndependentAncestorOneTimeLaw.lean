-- Prove2me | solution 1 for Kyprianou.Ch01.reverseLampertiIndependentAncestorOneTimeLaw
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-23T12:36:47.790205+00:00
-- url     : https://prove2.me/submissions/c1415e57-8ad9-4ac8-ad2f-76770c907fc7
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_Kyprianou_Ch01_BranchingClocks
import Definitions.Def_Kyprianou_Ch01_LampertiInverse
import Definitions.Def_Kyprianou_Ch01_BranchingGenerator
import Definitions.Def_LeanLevy_Processes_CompoundPoisson
import Theorems.Thm_Kyprianou_Ch01_reverseLampertiNonexplosiveInitialAtoms
import Theorems.Thm_Kyprianou_Ch01_reverseLampertiProductAncestorConvolutionPMF
import Theorems.Thm_Kyprianou_Ch01_reverseLampertiIndependentAncestorPositiveTimeLaw
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
    Q {ω |
        (compoundPoissonToBranching
          (integerCompoundPoisson (a + b) arrival marks) t ω).toNat = k} =
    (Q.prod Q)
      {ζ : Ω × Ω |
        (compoundPoissonToBranching
          (integerCompoundPoisson a arrival marks) t ζ.1).toNat +
        (compoundPoissonToBranching
          (integerCompoundPoisson b arrival marks) t ζ.2).toNat = k} := by
  by_cases ht : t = 0
  · subst t
    have hAtom := Kyprianou.Ch01.reverseLampertiNonexplosiveInitialAtoms
      Q rate hrate offspring hNoZeroJumps arrival marks
      jumpLaw hdriver hSupport hJumpMass hNoExplosion
    have hConv := Kyprianou.Ch01.reverseLampertiProductAncestorConvolutionPMF
      Q rate hrate offspring hNoZeroJumps arrival marks
      jumpLaw hdriver hSupport hJumpMass hNoExplosion
      K hRealisation a b 0 k
    have hKzero (y : Nat) : K y 0 = PMF.pure y := by
      apply PMF.ext
      intro n
      rw [hRealisation y 0 n]
      exact hAtom y n
    rw [hAtom (a + b) k, hConv]
    classical
    simp [hKzero]
    rw [tsum_eq_single b (by
      intro j hj
      simp [hj])]
    simp
  · have hpos : 0 < t :=
      lt_of_le_of_ne (show 0 ≤ t from zero_le) (Ne.symm ht)
    exact Kyprianou.Ch01.reverseLampertiIndependentAncestorPositiveTimeLaw
      Q rate hrate offspring hNoZeroJumps arrival marks
      jumpLaw hdriver hSupport hJumpMass hNoExplosion
      K hRealisation a b t hpos k
