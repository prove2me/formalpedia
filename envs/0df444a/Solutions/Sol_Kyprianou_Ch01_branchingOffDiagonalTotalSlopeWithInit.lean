-- Prove2me | solution 1 for Kyprianou.Ch01.branchingOffDiagonalTotalSlopeWithInit
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-18T10:28:18.704936+00:00
-- url     : https://prove2.me/submissions/7779d332-c072-445f-8dfd-b789665be52a

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

/-- PMF conservation reduces the infinite exit-mass slope to the diagonal. -/
theorem solution
    (law : PopulationLaws) (rate : NNReal) (offspring : PMF ℕ)
    (hinit : law 1 0 = PMF.pure 1)
    (hRates : IsBranchingRateGenerator law rate offspring) :
    Tendsto (fun t : ℝ =>
      ∑' k : ℕ, (if k = 1 then (0 : ℝ)
         else ((law 1 (Real.toNNReal t)) k).toReal) / t)
      (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (𝓝 (rate : ℝ)) := by
  have hset : Set.Ici (0 : ℝ) \ {0} = Set.Ioi 0 := by
    ext t
    simp only [Set.mem_diff, Set.mem_Ici, Set.mem_singleton_iff,
      Set.mem_Ioi]
    constructor
    · rintro ⟨hge, hne⟩
      exact lt_of_le_of_ne hge (fun heq => hne heq.symm)
    · intro ht
      exact ⟨ht.le, ne_of_gt ht⟩
  have hdiag := Kyprianou.Ch01.branchingOneAncestorExitMassDerivative
    law rate offspring hRates
  have hs := hasDerivWithinAt_iff_tendsto_slope.mp hdiag
  rw [hset] at hs
  have hzero : (1 : ℝ) -
      ((law 1 (Real.toNNReal (0 : ℝ))) 1).toReal = 0 := by
    simp [hinit, PMF.pure_apply_self]
  have heq (t : ℝ) :
      (∑' k : ℕ, (if k = 1 then (0 : ℝ)
        else ((law 1 (Real.toNNReal t)) k).toReal) / t) =
      slope (fun s : ℝ =>
        1 - ((law 1 (Real.toNNReal s)) 1).toReal) 0 t := by
    rw [tsum_div_const,
      Kyprianou.Ch01.branchingOneAncestorOffDiagonalMass]
    simp [slope, hzero, hinit, PMF.pure_apply_self, div_eq_mul_inv, mul_comm]
  simpa only [heq] using hs
