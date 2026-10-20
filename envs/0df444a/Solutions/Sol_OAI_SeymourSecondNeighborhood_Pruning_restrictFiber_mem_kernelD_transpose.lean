-- Prove2me | solution 1 for OAI.SeymourSecondNeighborhood.Pruning.restrictFiber_mem_kernelD_transpose
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T13:10:57.347254+00:00
-- url     : https://prove2.me/submissions/2e5e9ff1-b089-4292-a70a-d45f8c2d401f

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/SecondNeighborhood/KernelRestriction.lean:L101-L119
-- (upload_full_project.md Phase 4): solution for node OAI.SeymourSecondNeighborhood.Pruning.restrictFiber_mem_kernelD_transpose. The node keeps its source
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

theorem matrixN_transpose_mulVec_fiber (r : X → X → Prop)
    (R C : Finset (X × X)) (b : X → X → ℝ) (v : ↥C → ℝ) (i j : X)
    (hij : (i, j) ∈ Z r R C) :
    ((matrixN r R C b)ᵀ *ᵥ v) ⟨(i, j), hij⟩ =
      ∑ s : PairFiber C i, b s.1 j * v (fiberIndex C i s) := by
  classical
  change (∑ q : ↥C, matrixN r R C b q ⟨(i, j), hij⟩ * v q) = _
  symm
  apply Fintype.sum_of_injective (fiberIndex C i) (fiberIndex_injective C i)
  · intro q hq
    have hfirst : q.1.1 ≠ i := by
      intro heq
      exact hq ((mem_range_fiberIndex C i q).mpr heq)
    simp [matrixN, hfirst]
  · intro s
    simp [matrixN, fiberIndex]

theorem restrictFiber_mem_kernelD_transpose (r : X → X → Prop)
    (R C : Finset (X × X)) (b : X → X → ℝ) (hb : SupportedCoefficients r b)
    (p i : X) (hpi : r p i) (v : ↥C → ℝ)
    (hv : (matrixN r R C b)ᵀ *ᵥ v = 0) :
    (matrixD R C b p i)ᵀ *ᵥ restrictFiber C i v = 0 := by
  classical
  funext j
  change (∑ s : PairFiber C i, b s.1 j.1 * v (fiberIndex C i s)) = 0
  by_cases hcol : ∃ s : PairFiber C i, r s.1 j.1
  · obtain ⟨s, hs⟩ := hcol
    have hij : (i, j.1) ∈ Z r R C := by
      apply mem_Z.mpr
      exact ⟨p, s.1, j.2, s.2, hpi, hs⟩
    rw [← matrixN_transpose_mulVec_fiber r R C b v i j.1 hij]
    exact congrFun hv ⟨(i, j.1), hij⟩
  · apply Finset.sum_eq_zero
    intro s _
    have hzero : b s.1 j.1 = 0 := hb s.1 j.1 (fun h => hcol ⟨s, h⟩)
    rw [hzero, zero_mul]

end SeymourSecondNeighborhood.Pruning

end OAI

-- ---- platform node ----
open OAI OAI.SeymourSecondNeighborhood OAI.SeymourSecondNeighborhood.Pruning
open Matrix
open scoped BigOperators


theorem solution : type_of% @_root_.OAI.SeymourSecondNeighborhood.Pruning.restrictFiber_mem_kernelD_transpose := @_root_.OAI.SeymourSecondNeighborhood.Pruning.restrictFiber_mem_kernelD_transpose
