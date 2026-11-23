-- Prove2me | solution 1 for Kyprianou.Ch01.reverseLampertiNonexplosiveLaplaceProduct
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-23T11:01:49.577379+00:00
-- url     : https://prove2.me/submissions/d3bea677-fa70-4f38-9fdc-4e58cfab5e16
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_Kyprianou_Ch01_BranchingClocks
import Definitions.Def_Kyprianou_Ch01_LampertiInverse
import Definitions.Def_Kyprianou_Ch01_BranchingGenerator
import Definitions.Def_LeanLevy_Processes_CompoundPoisson
import Theorems.Thm_Kyprianou_Ch01_reverseLampertiIndependentAncestorOneTimeLaw
import Theorems.Thm_Kyprianou_Ch01_reverseLampertiProductAncestorConvolutionPMF
import Theorems.Thm_Kyprianou_Ch01_pmfLaplaceConvolution
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
    (a b : ℕ) (t : ℝ≥0) (phi : ℝ) (hphi : 0 < phi) :
    branchingLaplace K (a + b) t phi =
      branchingLaplace K a t phi * branchingLaplace K b t phi := by
  have hconv (a b : ℕ) (t : ℝ≥0) :
      K (a + b) t =
        (K a t).bind (fun n => (K b t).map (fun m => n + m)) := by
    apply PMF.ext
    intro k
    calc
      K (a + b) t k =
          Q {ω | (compoundPoissonToBranching
            (integerCompoundPoisson (a + b) arrival marks) t ω).toNat = k} :=
        hRealisation (a + b) t k
      _ = (Q.prod Q)
        {ζ : Ω × Ω |
          (compoundPoissonToBranching
            (integerCompoundPoisson a arrival marks) t ζ.1).toNat +
          (compoundPoissonToBranching
            (integerCompoundPoisson b arrival marks) t ζ.2).toNat = k} :=
        Kyprianou.Ch01.reverseLampertiIndependentAncestorOneTimeLaw
          Q rate hrate offspring hNoZeroJumps
          arrival marks jumpLaw hdriver hSupport hJumpMass hNoExplosion
          K hRealisation a b t k
      _ = ((K a t).bind
        (fun n => (K b t).map (fun m => n + m))) k :=
        Kyprianou.Ch01.reverseLampertiProductAncestorConvolutionPMF
          Q rate hrate offspring hNoZeroJumps
          arrival marks jumpLaw hdriver hSupport hJumpMass hNoExplosion
          K hRealisation a b t k
  change
    (∑' n : ℕ, (K (a + b) t n).toReal *
      Real.exp (-phi * (n : ℝ))) =
    (∑' n : ℕ, (K a t n).toReal *
      Real.exp (-phi * (n : ℝ))) *
    (∑' n : ℕ, (K b t n).toReal *
      Real.exp (-phi * (n : ℝ)))
  rw [hconv a b t]
  exact Kyprianou.Ch01.pmfLaplaceConvolution (K a t) (K b t) phi hphi

