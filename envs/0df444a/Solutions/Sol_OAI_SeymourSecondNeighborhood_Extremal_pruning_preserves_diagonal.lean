-- Prove2me | solution 1 for OAI.SeymourSecondNeighborhood.Extremal.pruning_preserves_diagonal
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T13:24:40.458596+00:00
-- url     : https://prove2.me/submissions/f340c2fa-4c59-4023-8d8f-45025d08efe3

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/SecondNeighborhood/ExtremalCompatibility.lean:L188-L202
-- (upload_full_project.md Phase 4): solution for node OAI.SeymourSecondNeighborhood.Extremal.pruning_preserves_diagonal. The node keeps its source
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
import Definitions.Def_OAI_Combinatorics_SecondNeighborhood_MatrixMapsPolynomial
import Definitions.Def_OAI_Combinatorics_SecondNeighborhood_GenericRankGlobalMinors
import Definitions.Def_OAI_Combinatorics_SecondNeighborhood_KernelBasisLifts
import Definitions.Def_OAI_Combinatorics_SecondNeighborhood_ExtremalImages
import Definitions.Def_OAI_Combinatorics_SecondNeighborhood_ExtremalCompatibility
import Theorems.Thm_OAI_SeymourSecondNeighborhood_Pruning_conflictFree_iff_disjoint

-- ---- from OAI.Combinatorics.SecondNeighborhood.ExtremalCompatibility ----
namespace OAI

namespace SeymourSecondNeighborhood.Extremal

open Pruning

variable {V : Type*} [Fintype V] [DecidableEq V]

noncomputable section

theorem diagonal_subset_leftCandidate {r : V → V → Prop}
    {P Q : Finset (V × V)} (hc : Compatible r P Q) (hP : diagonal ⊆ P) :
    diagonal ⊆ leftCandidate r Q := by
  intro z hz
  rcases z with ⟨v, w⟩
  have heq : v = w := mem_diagonal.mp hz
  subst w
  apply mem_leftCandidate.mpr
  intro hsecond
  obtain ⟨s, hvs, hsv⟩ := mem_rightImage.mp hsecond
  have hleft : (v, s) ∈ leftImage r P :=
    mem_leftImage.mpr ⟨s, hP (diagonal_mem s), hsv⟩
  exact Finset.disjoint_left.mp (conflictFree_iff_disjoint.mp hc) hleft hvs

theorem diagonal_subset_rightCandidate {r : V → V → Prop}
    {P Q : Finset (V × V)} (hc : Compatible r P Q) (hQ : diagonal ⊆ Q) :
    diagonal ⊆ rightCandidate r P := by
  intro z hz
  rcases z with ⟨v, w⟩
  have heq : v = w := mem_diagonal.mp hz
  subst w
  apply mem_rightCandidate.mpr
  intro hsecond
  obtain ⟨p, hpv, hpvArc⟩ := mem_leftImage.mp hsecond
  have hright : (p, v) ∈ rightImage r Q :=
    mem_rightImage.mpr ⟨p, hQ (diagonal_mem p), hpvArc⟩
  exact Finset.disjoint_left.mp (conflictFree_iff_disjoint.mp hc) hpv hright

theorem diagonal_left_conflictFree {r : V → V → Prop} {P : Finset (V × V)}
    (hP : diagonal ⊆ P) {a : V × V} (ha : a ∈ diagonal) :
    ∀ b ∈ rightCandidate r P, ¬ Conflict r a b := by
  rcases a with ⟨v, w⟩
  have heq : v = w := mem_diagonal.mp ha
  subst w
  intro b hb hc
  apply mem_rightCandidate.mp hb
  apply mem_leftImage.mpr
  refine ⟨v, ?_, hc.1⟩
  exact mem_leftImage.mpr ⟨b.2, hP (diagonal_mem b.2), hc.2⟩

theorem diagonal_right_conflictFree {r : V → V → Prop} {Q : Finset (V × V)}
    (hQ : diagonal ⊆ Q) {b : V × V} (hb : b ∈ diagonal) :
    ∀ a ∈ leftCandidate r Q, ¬ Conflict r a b := by
  rcases b with ⟨v, w⟩
  have heq : v = w := mem_diagonal.mp hb
  subst w
  intro a ha hc
  apply mem_leftCandidate.mp ha
  apply mem_rightImage.mpr
  refine ⟨v, ?_, hc.2⟩
  exact mem_rightImage.mpr ⟨a.1, hQ (diagonal_mem a.1), hc.1⟩

theorem pruning_preserves_diagonal {r : V → V → Prop}
    {P Q P' Q' : Finset (V × V)} (h : Admissible r P Q)
    (hp : PruningResult r (leftCandidate r Q) (rightCandidate r P) P' Q') :
    Admissible r P' Q' where
  compatible := hp.no_conflicts
  diagonal_left := by
    intro a ha
    exact hp.retain_left a
      (diagonal_subset_leftCandidate h.compatible h.diagonal_left ha)
      (diagonal_left_conflictFree h.diagonal_left ha)
  diagonal_right := by
    intro b hb
    exact hp.retain_right b
      (diagonal_subset_rightCandidate h.compatible h.diagonal_right hb)
      (diagonal_right_conflictFree h.diagonal_right hb)

end
end SeymourSecondNeighborhood.Extremal

end OAI

-- ---- platform node ----
open OAI OAI.SeymourSecondNeighborhood OAI.SeymourSecondNeighborhood.Extremal
open Pruning


theorem solution : type_of% @_root_.OAI.SeymourSecondNeighborhood.Extremal.pruning_preserves_diagonal := @_root_.OAI.SeymourSecondNeighborhood.Extremal.pruning_preserves_diagonal
