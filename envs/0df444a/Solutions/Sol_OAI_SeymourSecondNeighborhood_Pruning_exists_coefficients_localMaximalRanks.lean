-- Prove2me | solution 1 for OAI.SeymourSecondNeighborhood.Pruning.exists_coefficients_localMaximalRanks
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T13:12:40.251474+00:00
-- url     : https://prove2.me/submissions/0536ca2e-2321-4647-a39c-5d5c7cd9426e

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/SecondNeighborhood/GenericRankCoefficients.lean:L48-L73
-- (upload_full_project.md Phase 4): solution for node OAI.SeymourSecondNeighborhood.Pruning.exists_coefficients_localMaximalRanks. The node keeps its source
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
import Definitions.Def_OAI_Combinatorics_SecondNeighborhood_MaxSupportKernel
import Definitions.Def_OAI_Combinatorics_SecondNeighborhood_KernelConflict
import Definitions.Def_OAI_Combinatorics_SecondNeighborhood_GenericRankCoefficients
import Theorems.Thm_OAI_SeymourSecondNeighborhood_exists_eval_maximal_support_rank

-- ---- from OAI.Combinatorics.SecondNeighborhood.GenericRankCoefficients ----
namespace OAI

namespace SeymourSecondNeighborhood.Pruning

variable {X τ : Type*} [Fintype X] [DecidableEq X] [Fintype τ]

omit [Fintype X] [DecidableEq X] in
theorem selectedA_supported (r : X → X → Prop) (v : CoefficientVariables X → ℝ) :
    SupportedCoefficients r (selectedA r v) := by
  classical
  intro x y h
  simp [selectedA, h]

omit [Fintype X] [DecidableEq X] in
theorem selectedB_supported (r : X → X → Prop) (v : CoefficientVariables X → ℝ) :
    SupportedCoefficients r (selectedB r v) := by
  classical
  intro x y h
  simp [selectedB, h]

omit [Fintype X] [DecidableEq X] in
theorem matrixD_eq_eval_supported (r : X → X → Prop) (R C : Finset (X × X))
    (v : CoefficientVariables X → ℝ) (p i : X) :
    matrixD R C (selectedB r v) p i = evalPolynomialMatrix v
      (supportedVariableMatrix (R := ℝ)
        (fun s : PairFiber C i => fun j : PairFiber R p => r s.1 j.1)
        (fun s j => Sum.inr (s.1, j.1))) := by
  classical
  ext s j
  by_cases h : r s.1 j.1 <;>
    simp [matrixD, selectedB, evalPolynomialMatrix, supportedVariableMatrix, h]

theorem exists_coefficients_localMaximalRanks
    (r : X → X → Prop) (R C : Finset (X × X))
    (extra : τ → MvPolynomial (CoefficientVariables X) ℝ)
    (hextra : ∀ t, extra t ≠ 0) :
    ∃ v : CoefficientVariables X → ℝ,
      (∀ t, MvPolynomial.eval v (extra t) ≠ 0) ∧
      SupportedCoefficients r (selectedA r v) ∧
      SupportedCoefficients r (selectedB r v) ∧
      LocalMaximalRanks r R C (selectedB r v) := by
  classical
  let support (q : X × X) (s : PairFiber C q.2) (j : PairFiber R q.1) := r s.1 j.1
  let label (q : X × X) (s : PairFiber C q.2) (j : PairFiber R q.1) :
      CoefficientVariables X := Sum.inr (s.1, j.1)
  have hlabel : ∀ q s j s' j', support q s j → support q s' j' →
      label q s j = label q s' j' → s = s' ∧ j = j' := by
    intro q s j s' j' _ _ h
    have hp : (s.1, j.1) = (s'.1, j'.1) := Sum.inr.inj h
    exact ⟨Subtype.ext (congrArg Prod.fst hp), Subtype.ext (congrArg Prod.snd hp)⟩
  obtain ⟨v, hv, hmax⟩ :=
    exists_eval_maximal_support_rank support label hlabel extra hextra
  refine ⟨v, hv, selectedA_supported r v, selectedB_supported r v, ?_⟩
  intro p i _ D hD
  rw [matrixD_eq_eval_supported]
  apply hmax (p, i) D
  intro s j h
  exact hD s j h

end SeymourSecondNeighborhood.Pruning

end OAI

-- ---- platform node ----
open OAI OAI.SeymourSecondNeighborhood OAI.SeymourSecondNeighborhood.Pruning


theorem solution : type_of% @_root_.OAI.SeymourSecondNeighborhood.Pruning.exists_coefficients_localMaximalRanks := @_root_.OAI.SeymourSecondNeighborhood.Pruning.exists_coefficients_localMaximalRanks
