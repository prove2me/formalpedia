-- Prove2me | solution 1 for Kyprianou.Ch01.branchingOffDiagonalPointwiseSlope
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-18T11:28:21.550545+00:00
-- url     : https://prove2.me/submissions/e9597a2e-618c-4eca-9c9b-33b207eb794a

import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Topology.Algebra.InfiniteSum.Ring
import Mathlib.Probability.ProbabilityMassFunction.Monad
import Definitions.Def_Kyprianou_Ch01_BranchingGenerator
import Theorems.Thm_Kyprianou_Ch01_branchingOneAncestorOffDiagonalMass
import Theorems.Thm_Kyprianou_Ch01_branchingOneAncestorExitMassDerivative
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Kyprianou.Ch01 MeasureTheory Filter Set
open scoped NNReal ENNReal Topology BigOperators
set_option autoImplicit false

/-- Source transition generator yields each fixed off-diagonal quotient limit. -/
theorem solution
    (law : PopulationLaws) (rate : NNReal) (offspring : PMF ℕ)
    (hinit : law 1 0 = PMF.pure 1)
    (hRates : IsBranchingRateGenerator law rate offspring) :
    ∀ k : ℕ, Tendsto
      (fun t : ℝ =>
        (if k = 1 then (0 : ℝ)
         else ((law 1 (Real.toNNReal t)) k).toReal) / t)
      (nhdsWithin (0 : ℝ) (Set.Ioi 0))
      (𝓝 (if k = 1 then (0 : ℝ)
          else (rate : ℝ) * (offspring k).toReal)) := by
  have hset : Set.Ici (0 : ℝ) \ {0} = Set.Ioi 0 := by
    ext t
    simp only [Set.mem_diff, Set.mem_Ici, Set.mem_singleton_iff,
      Set.mem_Ioi]
    constructor
    · rintro ⟨hge, hne⟩
      exact lt_of_le_of_ne hge (fun heq => hne heq.symm)
    · intro ht
      exact ⟨ht.le, ne_of_gt ht⟩
  intro k
  by_cases hk : k = 1
  · subst k
    simpa using (tendsto_const_nhds : Tendsto
      (fun _ : ℝ => (0 : ℝ)) (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (𝓝 0))
  · have hzero : ((law 1 (0 : NNReal)) k).toReal = 0 := by
      rw [hinit, PMF.pure_apply_of_ne 1 k hk]
      simp
    have hderiv : HasDerivWithinAt
        (fun t : ℝ => ((law 1 (Real.toNNReal t)) k).toReal)
        ((rate : ℝ) * (offspring k).toReal) (Set.Ici 0) 0 := by
      simpa [IsBranchingRateGenerator, hk] using (hRates 1 k)
    have hs := hasDerivWithinAt_iff_tendsto_slope.mp hderiv
    rw [hset] at hs
    have hfun :
        (fun t : ℝ => ((law 1 (Real.toNNReal t)) k).toReal / t) =
          slope (fun t : ℝ =>
            ((law 1 (Real.toNNReal t)) k).toReal) 0 := by
      funext t
      rw [slope_def_field]
      simp [hzero]
    simp only [if_neg hk]
    rw [hfun]
    exact hs
