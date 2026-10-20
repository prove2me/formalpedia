-- Prove2me | solution 1 for OAI.SeymourSecondNeighborhood.Bipartite.minimum_cover_has_equal_matching
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T13:06:41.001894+00:00
-- url     : https://prove2.me/submissions/8ec0ce46-f848-4fd1-b01e-aa9a9a61cdb1

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/SecondNeighborhood/MatchingCover.lean:L75-L179
-- (upload_full_project.md Phase 4): solution for node OAI.SeymourSecondNeighborhood.Bipartite.minimum_cover_has_equal_matching. The node keeps its source
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
import Theorems.Thm_OAI_SeymourSecondNeighborhood_Bipartite_minimum_cover_left_hall

-- ---- from OAI.Combinatorics.SecondNeighborhood.MatchingCover ----
namespace OAI

namespace SeymourSecondNeighborhood.Bipartite

variable {L R : Type*} [Fintype L] [Fintype R] [DecidableEq L] [DecidableEq R]
variable {E : L → R → Prop}

private theorem minimum_cover_has_equal_matching {A : Finset L} {B : Finset R}
    (hC : IsVertexCover E A B)
    (hmin : ∀ A' B', IsVertexCover E A' B' →
      A.card + B.card ≤ A'.card + B'.card) :
    ∃ N : Finset (L × R), IsMatching E N ∧ N.card = A.card + B.card := by
  classical
  obtain ⟨f, hfinj, hf⟩ := minimum_cover_left_hall hC hmin
  have hCsym : IsVertexCover (fun r l => E l r) B A := by
    intro r l hlr
    exact (hC l r hlr).symm
  have hminsym : ∀ B' A', IsVertexCover (fun r l => E l r) B' A' →
      B.card + A.card ≤ B'.card + A'.card := by
    intro B' A' hC'
    have h := hmin A' B' (fun l r hlr => (hC' r l hlr).symm)
    omega
  obtain ⟨g, hginj, hg⟩ := minimum_cover_left_hall hCsym hminsym
  let P : Finset (L × R) := Finset.univ.image (fun a : A => ((a : L), f a))
  let Q : Finset (L × R) := Finset.univ.image (fun b : B => (g b, (b : R)))
  have hP : IsMatching E P := by
    refine ⟨?_, ?_, ?_⟩
    · intro e he
      obtain ⟨a, _, rfl⟩ := Finset.mem_image.mp he
      exact (hf a).1
    · intro e he e' he' heq
      obtain ⟨a, _, rfl⟩ := Finset.mem_image.mp he
      obtain ⟨a', _, rfl⟩ := Finset.mem_image.mp he'
      have haa : a = a' := Subtype.ext heq
      subst a'
      rfl
    · intro e he e' he' heq
      obtain ⟨a, _, rfl⟩ := Finset.mem_image.mp he
      obtain ⟨a', _, rfl⟩ := Finset.mem_image.mp he'
      have haa : a = a' := hfinj heq
      subst a'
      rfl
  have hQ : IsMatching E Q := by
    refine ⟨?_, ?_, ?_⟩
    · intro e he
      obtain ⟨b, _, rfl⟩ := Finset.mem_image.mp he
      exact (hg b).1
    · intro e he e' he' heq
      obtain ⟨b, _, rfl⟩ := Finset.mem_image.mp he
      obtain ⟨b', _, rfl⟩ := Finset.mem_image.mp he'
      have hbb : b = b' := hginj heq
      subst b'
      rfl
    · intro e he e' he' heq
      obtain ⟨b, _, rfl⟩ := Finset.mem_image.mp he
      obtain ⟨b', _, rfl⟩ := Finset.mem_image.mp he'
      have hbb : b = b' := Subtype.ext heq
      subst b'
      rfl
  have hcrossL : ∀ e ∈ P, ∀ e' ∈ Q, e.1 ≠ e'.1 := by
    intro e he e' he' heq
    obtain ⟨a, _, rfl⟩ := Finset.mem_image.mp he
    obtain ⟨b, _, rfl⟩ := Finset.mem_image.mp he'
    change (a : L) = g b at heq
    apply (hg b).2
    rw [← heq]
    exact a.property
  have hcrossR : ∀ e ∈ P, ∀ e' ∈ Q, e.2 ≠ e'.2 := by
    intro e he e' he' heq
    obtain ⟨a, _, rfl⟩ := Finset.mem_image.mp he
    obtain ⟨b, _, rfl⟩ := Finset.mem_image.mp he'
    change f a = (b : R) at heq
    apply (hf a).2
    rw [heq]
    exact b.property
  have hmatch : IsMatching E (P ∪ Q) := by
    refine ⟨?_, ?_, ?_⟩
    · intro e he
      rcases Finset.mem_union.mp he with he | he
      · exact hP.1 e he
      · exact hQ.1 e he
    · intro e he e' he' heq
      rcases Finset.mem_union.mp he with he | he <;>
        rcases Finset.mem_union.mp he' with he' | he'
      · exact hP.2.1 he he' heq
      · exact False.elim (hcrossL e he e' he' heq)
      · exact False.elim (hcrossL e' he' e he heq.symm)
      · exact hQ.2.1 he he' heq
    · intro e he e' he' heq
      rcases Finset.mem_union.mp he with he | he <;>
        rcases Finset.mem_union.mp he' with he' | he'
      · exact hP.2.2 he he' heq
      · exact False.elim (hcrossR e he e' he' heq)
      · exact False.elim (hcrossR e' he' e he heq.symm)
      · exact hQ.2.2 he he' heq
  have hdisjoint : Disjoint P Q :=
    Finset.disjoint_left.mpr (fun e he he' => hcrossL e he e he' rfl)
  have hPinj : Function.Injective (fun a : A => ((a : L), f a)) := by
    intro a a' h
    exact Subtype.ext (congrArg Prod.fst h)
  have hQinj : Function.Injective (fun b : B => (g b, (b : R))) := by
    intro b b' h
    exact Subtype.ext (congrArg Prod.snd h)
  have hPcard : P.card = A.card := by
    dsimp [P]
    rw [Finset.card_image_of_injective _ hPinj]
    simp
  have hQcard : Q.card = B.card := by
    dsimp [Q]
    rw [Finset.card_image_of_injective _ hQinj]
    simp
  exact ⟨P ∪ Q, hmatch, by rw [Finset.card_union_of_disjoint hdisjoint, hPcard, hQcard]⟩

end SeymourSecondNeighborhood.Bipartite

end OAI

-- ---- platform node ----
open OAI OAI.SeymourSecondNeighborhood OAI.SeymourSecondNeighborhood.Bipartite


theorem solution : type_of% @_root_.OAI.SeymourSecondNeighborhood.Bipartite.minimum_cover_has_equal_matching := @_root_.OAI.SeymourSecondNeighborhood.Bipartite.minimum_cover_has_equal_matching
