-- Prove2me | solution 1 for OAI.SeymourSecondNeighborhood.Pruning.restrictFiber_mem_kernelD
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T13:10:04.939052+00:00
-- url     : https://prove2.me/submissions/b2347d83-ab7a-4359-8081-e279b53b4c41

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/SecondNeighborhood/KernelRestriction.lean:L82-L99
-- (upload_full_project.md Phase 4): solution for node OAI.SeymourSecondNeighborhood.Pruning.restrictFiber_mem_kernelD. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.MvPolynomial.Funext
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Combinatorics.Hall.Finite
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Max
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Finset.Sum
import Mathlib.Data.Finset.Union
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Sum
import Mathlib.Data.Matrix.Mul
import Mathlib.Data.Nat.Find
import Mathlib.Data.Real.Basic
import Mathlib.LinearAlgebra.Dimension.Finite
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Matrix.MvPolynomial
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.Tactic.Tauto
import Definitions.Def_SeymourSecondNeighborhood
import Definitions.Def_OAI_Combinatorics_SecondNeighborhood_Basic
import Definitions.Def_OAI_Combinatorics_SecondNeighborhood_ReductionCore
import Definitions.Def_OAI_Combinatorics_SecondNeighborhood_Reindex
import Definitions.Def_OAI_Combinatorics_SecondNeighborhood_MinimalCounterexample
import Definitions.Def_OAI_Combinatorics_SecondNeighborhood_Deletion
import Definitions.Def_OAI_Combinatorics_SecondNeighborhood_TransitiveBlowup
import Definitions.Def_OAI_Combinatorics_SecondNeighborhood_PruningDefinitions
import Definitions.Def_OAI_Combinatorics_SecondNeighborhood_Matching
import Definitions.Def_OAI_Combinatorics_SecondNeighborhood_AugmentedGraph
import Definitions.Def_OAI_Combinatorics_SecondNeighborhood_MatchingAugmented
import Definitions.Def_OAI_Combinatorics_SecondNeighborhood_GenericRankMatching
import Definitions.Def_OAI_Combinatorics_SecondNeighborhood_GenericRank
import Definitions.Def_OAI_Combinatorics_SecondNeighborhood_MatrixMaps
import Definitions.Def_OAI_Combinatorics_SecondNeighborhood_KernelRestriction

-- ---- from OAI.Combinatorics.SecondNeighborhood.KernelRestriction ----
namespace OAI

namespace SeymourSecondNeighborhood.Pruning

open Matrix
open scoped BigOperators

variable {X : Type*} [Fintype X] [DecidableEq X]

omit [Fintype X] [DecidableEq X] in
theorem fiberIndex_injective (P : Finset (X × X)) (p : X) :
    Function.Injective (fiberIndex P p) := by
  intro j k h
  apply Subtype.ext
  exact congrArg (fun q : ↥P => q.1.2) h

omit [Fintype X] [DecidableEq X] in
theorem mem_range_fiberIndex (P : Finset (X × X)) (p : X) (q : ↥P) :
    q ∈ Set.range (fiberIndex P p) ↔ q.1.1 = p := by
  constructor
  · rintro ⟨j, rfl⟩
    rfl
  · rcases q with ⟨⟨q₁, q₂⟩, hq⟩
    intro h
    change q₁ = p at h
    subst q₁
    exact ⟨⟨q₂, hq⟩, rfl⟩

theorem matrixB_mulVec_fiber (r : X → X → Prop) (R C : Finset (X × X))
    (b : X → X → ℝ) (u : ↥R → ℝ) (p s : X)
    (hps : (p, s) ∈ H r R C) :
    (matrixB r R C b *ᵥ u) ⟨(p, s), hps⟩ =
      ∑ j : PairFiber R p, b s j.1 * u (fiberIndex R p j) := by
  classical
  change (∑ q : ↥R, matrixB r R C b ⟨(p, s), hps⟩ q * u q) = _
  symm
  apply Fintype.sum_of_injective (fiberIndex R p) (fiberIndex_injective R p)
  · intro q hq
    have hfirst : p ≠ q.1.1 := by
      intro heq
      exact hq ((mem_range_fiberIndex R p q).mpr heq.symm)
    simp [matrixB, hfirst]
  · intro j
    simp [matrixB, fiberIndex]

theorem restrictFiber_mem_kernelD (r : X → X → Prop) (R C : Finset (X × X))
    (b : X → X → ℝ) (hb : SupportedCoefficients r b) (p i : X)
    (hpi : r p i) (u : ↥R → ℝ) (hu : matrixB r R C b *ᵥ u = 0) :
    matrixD R C b p i *ᵥ restrictFiber R p u = 0 := by
  classical
  funext s
  change (∑ j : PairFiber R p, b s.1 j.1 * u (fiberIndex R p j)) = 0
  by_cases hrow : ∃ j : PairFiber R p, r s.1 j.1
  · obtain ⟨j, hj⟩ := hrow
    have hps : (p, s.1) ∈ H r R C := by
      apply mem_H.mpr
      exact ⟨i, j.1, j.2, s.2, hpi, hj⟩
    rw [← matrixB_mulVec_fiber r R C b u p s.1 hps]
    exact congrFun hu ⟨(p, s.1), hps⟩
  · apply Finset.sum_eq_zero
    intro j _
    have hzero : b s.1 j.1 = 0 := hb s.1 j.1 (fun h => hrow ⟨j, h⟩)
    rw [hzero, zero_mul]

end SeymourSecondNeighborhood.Pruning

end OAI

-- ---- platform node ----
open OAI OAI.SeymourSecondNeighborhood OAI.SeymourSecondNeighborhood.Pruning
open Matrix
open scoped BigOperators


theorem solution : type_of% @_root_.OAI.SeymourSecondNeighborhood.Pruning.restrictFiber_mem_kernelD := @_root_.OAI.SeymourSecondNeighborhood.Pruning.restrictFiber_mem_kernelD
