-- Prove2me | solution 1 for OAI.SeymourSecondNeighborhood.Bipartite.exists_maximum_matching_with_maximum_blocks
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T13:02:13.267515+00:00
-- url     : https://prove2.me/submissions/a06eb378-2173-4bb0-91f7-962c95ab1bb9

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/SecondNeighborhood/MatchingAugmented.lean:L246-L264
-- (upload_full_project.md Phase 4): solution for node OAI.SeymourSecondNeighborhood.Bipartite.exists_maximum_matching_with_maximum_blocks. The node keeps its source
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
import Theorems.Thm_OAI_SeymourSecondNeighborhood_Bipartite_exists_maximum_matching_min_cost
import Theorems.Thm_OAI_SeymourSecondNeighborhood_Bipartite_isMaximumMatching_rightBlock_of_minimum_crossing

-- ---- from OAI.Combinatorics.SecondNeighborhood.MatchingAugmented ----
namespace OAI

namespace SeymourSecondNeighborhood.Bipartite

variable {L R : Type*} [Fintype L] [Fintype R]
    [DecidableEq L] [DecidableEq R]
    {E : L → R → Prop}

omit [Fintype L] [Fintype R] in
theorem IsMatching.swap {M : Finset (L × R)} (hM : IsMatching E M) :
    IsMatching (fun b a => E a b) (swapMatching M) := by
  refine ⟨?_, ?_, ?_⟩
  · intro e he
    exact hM.1 e.swap (mem_swapMatching.mp he)
  · intro e he f hf hef
    apply Prod.swap_injective
    exact hM.2.2 (mem_swapMatching.mp he) (mem_swapMatching.mp hf) hef
  · intro e he f hf hef
    apply Prod.swap_injective
    exact hM.2.1 (mem_swapMatching.mp he) (mem_swapMatching.mp hf) hef

omit [Fintype L] [Fintype R] in
theorem IsMaximumMatching.swap {M : Finset (L × R)}
    (hM : IsMaximumMatching E M) :
    IsMaximumMatching (fun b a => E a b) (swapMatching M) := by
  refine ⟨hM.1.swap, ?_⟩
  intro N hN
  have hcard := hM.2 (swapMatching N) hN.swap
  simpa using hcard

theorem isMaximumMatching_leftBlock_of_minimum_crossing
    (P : L → Prop) (Q : R → Prop) [DecidablePred P] [DecidablePred Q]
    (hblock : ∀ a b, E a b → Q b → P a)
    {M : Finset (L × R)} (hM : IsMaximumMatching E M)
    (hmin : ∀ N : Finset (L × R), IsMaximumMatching E N →
      (M.filter (fun e => P e.1 ∧ ¬Q e.2)).card ≤
        (N.filter (fun e => P e.1 ∧ ¬Q e.2)).card) :
    IsMaximumMatching (fun a b => E a b ∧ ¬P a)
      (M.filter (fun e => ¬P e.1)) := by
  classical
  have hblock' : ∀ b a, E a b → ¬P a → ¬Q b := by
    intro b a he hnP hQ
    exact hnP (hblock a b he hQ)
  have hmin' : ∀ N : Finset (R × L),
      IsMaximumMatching (fun b a => E a b) N →
      ((swapMatching M).filter (fun e => ¬Q e.1 ∧ ¬¬P e.2)).card ≤
        (N.filter (fun e => ¬Q e.1 ∧ ¬¬P e.2)).card := by
    intro N hN
    have h := hmin (swapMatching N) hN.swap
    simpa [and_comm] using h
  have hright := isMaximumMatching_rightBlock_of_minimum_crossing
    (fun b => ¬Q b) (fun a => ¬P a) hblock' hM.swap hmin'
  have hleft := hright.swap
  simpa only [filter_swapMatching, swapMatching_swapMatching,
    Prod.snd_swap] using hleft

theorem exists_maximum_matching_with_maximum_blocks
    (P : L → Prop) (Q : R → Prop) [DecidablePred P] [DecidablePred Q]
    (hblock : ∀ a b, E a b → Q b → P a) :
    ∃ M : Finset (L × R), IsMaximumMatching E M ∧
      IsMaximumMatching (fun a b => E a b ∧ Q b)
        (M.filter (fun e => Q e.2)) ∧
      IsMaximumMatching (fun a b => E a b ∧ ¬P a)
        (M.filter (fun e => ¬P e.1)) := by
  classical
  obtain ⟨M, hM, hmin⟩ := exists_maximum_matching_min_cost E
    (fun N => (N.filter (fun e => P e.1 ∧ ¬Q e.2)).card)
  have hmin' : ∀ N : Finset (L × R), IsMaximumMatching E N →
      (M.filter (fun e => P e.1 ∧ ¬Q e.2)).card ≤
        (N.filter (fun e => P e.1 ∧ ¬Q e.2)).card := by
    intro N hN
    exact hmin N hN.1 (Nat.le_antisymm (hM.2 N hN.1) (hN.2 M hM.1))
  exact ⟨M, hM,
    isMaximumMatching_rightBlock_of_minimum_crossing P Q hblock hM hmin',
    isMaximumMatching_leftBlock_of_minimum_crossing P Q hblock hM hmin'⟩

end SeymourSecondNeighborhood.Bipartite

end OAI

-- ---- platform node ----
open OAI OAI.SeymourSecondNeighborhood OAI.SeymourSecondNeighborhood.Bipartite


theorem solution : type_of% @_root_.OAI.SeymourSecondNeighborhood.Bipartite.exists_maximum_matching_with_maximum_blocks := @_root_.OAI.SeymourSecondNeighborhood.Bipartite.exists_maximum_matching_with_maximum_blocks
