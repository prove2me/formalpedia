-- Prove2me | solution 2 for Kyprianou.Ch01.reverseLampertiNonexplosiveLaplaceProduct
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @pageman
-- created : 2026-11-23T13:04:13.367911+00:00
-- url     : https://prove2.me/submissions/2d97e3c0-0f3f-450a-a1aa-16f58d79f4b3
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_Kyprianou_Ch01_BranchingClocks
import Definitions.Def_Kyprianou_Ch01_LampertiInverse
import Definitions.Def_Kyprianou_Ch01_BranchingGenerator
import Definitions.Def_LeanLevy_Processes_CompoundPoisson
import Theorems.Thm_Kyprianou_Ch01_reverseLampertiNonexplosiveInitialAtoms
import Theorems.Thm_Kyprianou_Ch01_reverseLampertiIndependentAncestorPositiveTimeLaw
import Theorems.Thm_Kyprianou_Ch01_reverseLampertiProductAncestorConvolutionPMF
import Theorems.Thm_Kyprianou_Ch01_pmfLaplaceConvolution

open MeasureTheory ProbabilityTheory Kyprianou.Ch01 Set Filter
open scoped NNReal ENNReal BigOperators
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
    (a b : ℕ) (t : ℝ≥0) (phi : ℝ) (hphi : 0 < phi) :
    branchingLaplace K (a + b) t phi =
      branchingLaplace K a t phi * branchingLaplace K b t phi := by
  classical
  have hAtom (y k : ℕ) :
      Q {ω | (compoundPoissonToBranching
          (integerCompoundPoisson y arrival marks) 0 ω).toNat = k} =
        (PMF.pure y) k :=
    reverseLampertiNonexplosiveInitialAtoms Q rate hrate offspring hNoZeroJumps
      arrival marks jumpLaw hdriver hSupport hJumpMass hNoExplosion y k
  have hPure (y : ℕ) :
      branchingLaplace K y 0 phi = Real.exp (-phi * (y : ℝ)) := by
    unfold branchingLaplace
    have hpoint (n : ℕ) : K y 0 n = (PMF.pure y) n := by
      rw [hRealisation y 0 n, hAtom y n]
    simp_rw [hpoint]
    have hfun :
        (fun n : ℕ => ((PMF.pure y) n).toReal * Real.exp (-phi * (n : ℝ))) =
          fun n : ℕ => if n = y then Real.exp (-phi * (y : ℝ)) else 0 := by
      funext n
      by_cases hn : n = y
      · simp [hn, PMF.pure_apply]
      · simp [hn, PMF.pure_apply]
    rw [hfun, tsum_ite_eq]
  by_cases ht0 : t = 0
  · subst ht0
    rw [hPure (a + b), hPure a, hPure b]
    have hcast : ((a + b : ℕ) : ℝ) = (a : ℝ) + (b : ℝ) := Nat.cast_add a b
    rw [hcast, mul_add, ← Real.exp_add]
  · have ht : (0 : ℝ≥0) < t := (pos_iff_ne_zero).mpr ht0
    have hpmf (k : ℕ) :
        K (a + b) t k =
          ((K a t).bind (fun n => (K b t).map (fun m => n + m))) k := by
      rw [hRealisation (a + b) t k,
        reverseLampertiIndependentAncestorPositiveTimeLaw Q rate hrate offspring
          hNoZeroJumps arrival marks jumpLaw hdriver hSupport hJumpMass hNoExplosion
          K hRealisation a b t ht k,
        reverseLampertiProductAncestorConvolutionPMF Q rate hrate offspring
          hNoZeroJumps arrival marks jumpLaw hdriver hSupport hJumpMass hNoExplosion
          K hRealisation a b t k]
    unfold branchingLaplace
    simp_rw [hpmf]
    exact pmfLaplaceConvolution (K a t) (K b t) phi hphi
