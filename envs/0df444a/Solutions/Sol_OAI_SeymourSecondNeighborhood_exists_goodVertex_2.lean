-- Prove2me | solution 2 for OAI.SeymourSecondNeighborhood.exists_goodVertex
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T13:27:24.30131+00:00
-- url     : https://prove2.me/submissions/299f30f8-79d0-4f38-98c4-f6f0bd3c487e

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/SecondNeighborhood/Main.lean:L11-L18
-- (upload_full_project.md Phase 4): solution for the platform mission target OAI.SeymourSecondNeighborhood.exists_goodVertex.
-- The source declaration is kept inside its namespace next to the proof-only helpers it needs;
-- `theorem solution` restates the platform stub (Theorems.Thm_OAI_SeymourSecondNeighborhood_exists_goodVertex) verbatim and is proved by it.
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
import Definitions.Def_OAI_Combinatorics_SecondNeighborhood_ExtremalCounting
import Theorems.Thm_OAI_SeymourSecondNeighborhood_Bipartite_exists_maximum_matching_with_maximum_blocks
import Theorems.Thm_OAI_SeymourSecondNeighborhood_Bipartite_exists_vertexCover_card_eq_of_isMaximumMatching
import Theorems.Thm_OAI_SeymourSecondNeighborhood_Extremal_exists_maximizing_pair
import Theorems.Thm_OAI_SeymourSecondNeighborhood_Extremal_pruning_preserves_diagonal
import Theorems.Thm_OAI_SeymourSecondNeighborhood_Pruning_alphaEdges_image
import Theorems.Thm_OAI_SeymourSecondNeighborhood_Pruning_alphaEdges_isMatching
import Theorems.Thm_OAI_SeymourSecondNeighborhood_Pruning_augmented_matching_card_le_corners
import Theorems.Thm_OAI_SeymourSecondNeighborhood_Pruning_betaEdges_image
import Theorems.Thm_OAI_SeymourSecondNeighborhood_Pruning_betaEdges_isMatching
import Theorems.Thm_OAI_SeymourSecondNeighborhood_Pruning_conflictFree_iff_disjoint
import Theorems.Thm_OAI_SeymourSecondNeighborhood_Pruning_exists_pruning_of_augmented_cover
import Theorems.Thm_OAI_SeymourSecondNeighborhood_blowup_isOriented
import Theorems.Thm_OAI_SeymourSecondNeighborhood_blowup_strictSubsetGrowth
import Theorems.Thm_OAI_SeymourSecondNeighborhood_exists_minimal_counterexample
import Theorems.Thm_OAI_SeymourSecondNeighborhood_subsetDeficit_of_minimal

-- ---- from OAI.Combinatorics.SecondNeighborhood.ReductionCore ----
namespace OAI

namespace SeymourSecondNeighborhood

variable {V : Type*} [Fintype V] [DecidableEq V]

theorem counterexample_iff_not_conjecture (r : V → V → Prop) :
    Counterexample r ↔ ¬ SecondNeighborhoodConjecture r := by
  classical
  simp only [Counterexample, SecondNeighborhoodConjecture, GoodVertex,
    not_exists, not_le]

end SeymourSecondNeighborhood

end OAI

-- ---- from OAI.Combinatorics.SecondNeighborhood.TransitiveBlowup ----
namespace OAI

namespace SeymourSecondNeighborhood

variable {V : Type*}

theorem blowup_positiveIndegree {r : V → V → Prop}
    (hi : PositiveIndegree r) (m : ℕ) : PositiveIndegree (blowup r m) := by
  intro p
  obtain ⟨v, hv⟩ := hi p.1
  exact ⟨(v, p.2), Or.inl hv⟩

variable [Fintype V] [DecidableEq V]

end SeymourSecondNeighborhood

end OAI

-- ---- from OAI.Combinatorics.SecondNeighborhood.Reduction ----
namespace OAI

namespace SeymourSecondNeighborhood

variable {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V]

theorem counterexample_reduction {r : V → V → Prop}
    (hr : IsOriented r) (hcounter : Counterexample r) :
    ∃ n : ℕ, 0 < n ∧
      ∃ g : (Fin n × Fin (n + 1)) → (Fin n × Fin (n + 1)) → Prop,
        IsOriented g ∧ PositiveIndegree g ∧ StrictSubsetGrowth g := by
  classical
  obtain ⟨n, hn, s, hs, hbad, hminimal, hboundary, hindegree⟩ :=
    exists_minimal_counterexample hr hcounter
  refine ⟨n, hn, blowup s (n + 1), blowup_isOriented hs (n + 1),
    blowup_positiveIndegree hindegree (n + 1), ?_⟩
  apply blowup_strictSubsetGrowth hs hindegree
    (subsetDeficit_of_minimal hs hbad hminimal hboundary)
  simpa only [Fintype.card_fin] using Nat.lt_succ_self n

end SeymourSecondNeighborhood

end OAI

-- ---- from OAI.Combinatorics.SecondNeighborhood.AugmentedGraph ----
namespace OAI

namespace SeymourSecondNeighborhood.Pruning

open Bipartite

variable {V : Type*} [Fintype V] [DecidableEq V]

variable {r : V → V → Prop} {R C : Finset (V × V)}

theorem alphaLift_injective :
    Function.Injective (alphaLift (r := r) (R := R) (C := C)) := by
  intro e f h
  exact Prod.ext (Sum.inr.inj (congrArg Prod.snd h))
    (Sum.inl.inj (congrArg Prod.fst h))

theorem betaLift_injective :
    Function.Injective (betaLift (r := r) (R := R) (C := C)) := by
  intro e f h
  exact Prod.ext (Sum.inr.inj (congrArg Prod.fst h))
    (Sum.inl.inj (congrArg Prod.snd h))

end SeymourSecondNeighborhood.Pruning

end OAI

-- ---- from OAI.Combinatorics.SecondNeighborhood.AugmentedMatching ----
namespace OAI

namespace SeymourSecondNeighborhood.Pruning

open Bipartite

variable {V : Type*} [Fintype V] [DecidableEq V]
    {r : V → V → Prop} {R C : Finset (V × V)}

private theorem alphaLift_image_isMatching
    {N : Finset (↥(Z r R C) × ↥R)}
    (hN : IsMatching (AlphaRelation r R C) N) :
    IsMatching (fun a b => AugmentedEdge r R C a b ∧ b.isRight)
      (N.image (alphaLift (r := r) (R := R) (C := C))) := by
  classical
  refine ⟨?_, ?_, ?_⟩
  · intro e he
    obtain ⟨f, hf, rfl⟩ := Finset.mem_image.mp he
    exact ⟨hN.1 f hf, by simp [alphaLift]⟩
  · intro e he f hf hef
    obtain ⟨e', he', rfl⟩ := Finset.mem_image.mp he
    obtain ⟨f', hf', rfl⟩ := Finset.mem_image.mp hf
    exact congrArg alphaLift (hN.2.2 he' hf' (Sum.inl.inj hef))
  · intro e he f hf hef
    obtain ⟨e', he', rfl⟩ := Finset.mem_image.mp he
    obtain ⟨f', hf', rfl⟩ := Finset.mem_image.mp hf
    exact congrArg alphaLift (hN.2.1 he' hf' (Sum.inr.inj hef))

private theorem betaLift_image_isMatching
    {N : Finset (↥(Z r R C) × ↥C)}
    (hN : IsMatching (BetaRelation r R C) N) :
    IsMatching (fun a b => AugmentedEdge r R C a b ∧ ¬a.isLeft)
      (N.image (betaLift (r := r) (R := R) (C := C))) := by
  classical
  refine ⟨?_, ?_, ?_⟩
  · intro e he
    obtain ⟨f, hf, rfl⟩ := Finset.mem_image.mp he
    exact ⟨hN.1 f hf, by simp [betaLift]⟩
  · intro e he f hf hef
    obtain ⟨e', he', rfl⟩ := Finset.mem_image.mp he
    obtain ⟨f', hf', rfl⟩ := Finset.mem_image.mp hf
    exact congrArg betaLift (hN.2.1 he' hf' (Sum.inr.inj hef))
  · intro e he f hf hef
    obtain ⟨e', he', rfl⟩ := Finset.mem_image.mp he
    obtain ⟨f', hf', rfl⟩ := Finset.mem_image.mp hf
    exact congrArg betaLift (hN.2.2 he' hf' (Sum.inl.inj hef))

theorem alphaEdges_isMaximumMatching
    {M : Finset (LeftVertex r R C × RightVertex r R C)}
    (hM : IsMatching (AugmentedEdge r R C) M)
    (hα : IsMaximumMatching
      (fun a b => AugmentedEdge r R C a b ∧ b.isRight)
      (M.filter (fun e => e.2.isRight))) :
    IsMaximumMatching (AlphaRelation r R C) (alphaEdges M) := by
  classical
  refine ⟨alphaEdges_isMatching hM, ?_⟩
  intro N hN
  have h := hα.2 (N.image alphaLift) (alphaLift_image_isMatching hN)
  rw [Finset.card_image_of_injective _ alphaLift_injective] at h
  have hcard : (M.filter (fun e => e.2.isRight)).card = (alphaEdges M).card := by
    rw [← alphaEdges_image hM, Finset.card_image_of_injective _ alphaLift_injective]
  simpa only [hcard] using h

theorem betaEdges_isMaximumMatching
    {M : Finset (LeftVertex r R C × RightVertex r R C)}
    (hM : IsMatching (AugmentedEdge r R C) M)
    (hβ : IsMaximumMatching
      (fun a b => AugmentedEdge r R C a b ∧ ¬a.isLeft)
      (M.filter (fun e => ¬e.1.isLeft))) :
    IsMaximumMatching (BetaRelation r R C) (betaEdges M) := by
  classical
  refine ⟨betaEdges_isMatching hM, ?_⟩
  intro N hN
  have h := hβ.2 (N.image betaLift) (betaLift_image_isMatching hN)
  rw [Finset.card_image_of_injective _ betaLift_injective] at h
  have hfilter : M.filter (fun e => ¬e.1.isLeft) =
      M.filter (fun e => e.1.isRight) := by
    ext ⟨a, b⟩
    cases a <;> simp
  have hcard : (M.filter (fun e => ¬e.1.isLeft)).card = (betaEdges M).card := by
    rw [hfilter, ← betaEdges_image hM,
      Finset.card_image_of_injective _ betaLift_injective]
  simpa only [hcard] using h

theorem exists_augmented_maximum_matching (r : V → V → Prop)
    (R C : Finset (V × V)) :
    ∃ M : Finset (LeftVertex r R C × RightVertex r R C),
      IsMaximumMatching (AugmentedEdge r R C) M ∧
      IsMaximumMatching (AlphaRelation r R C) (alphaEdges M) ∧
      IsMaximumMatching (BetaRelation r R C) (betaEdges M) := by
  classical
  have hblock : ∀ a b, AugmentedEdge r R C a b → b.isRight → a.isLeft := by
    intro a b hab hb
    cases a <;> cases b <;> simp_all [AugmentedEdge]
  obtain ⟨M, hM, hα, hβ⟩ := exists_maximum_matching_with_maximum_blocks
    (fun a : LeftVertex r R C => a.isLeft)
    (fun b : RightVertex r R C => b.isRight) hblock
  exact ⟨M, hM, alphaEdges_isMaximumMatching hM.1 hα,
    betaEdges_isMaximumMatching hM.1 hβ⟩

end SeymourSecondNeighborhood.Pruning

end OAI

-- ---- from OAI.Combinatorics.SecondNeighborhood.CoverPruning ----
namespace OAI

namespace SeymourSecondNeighborhood.Pruning

open Bipartite

variable {V : Type*} [Fintype V] [DecidableEq V]

theorem exists_pruning_of_augmented_matching_bound
    (r : V → V → Prop) (R C : Finset (V × V))
    (M : Finset (LeftVertex r R C × RightVertex r R C))
    (hM : IsMaximumMatching (AugmentedEdge r R C) M)
    (hbound : M.card ≤ (H r R C).card + (Z r R C).card) :
    ∃ R' C', PruningResult r R C R' C' := by
  classical
  obtain ⟨A, B, hcover, hcard, hA, hB⟩ :=
    exists_vertexCover_card_eq_of_isMaximumMatching hM
  exact exists_pruning_of_augmented_cover r R C A B hcover hA hB
    (hcard.trans_le hbound)

end SeymourSecondNeighborhood.Pruning

end OAI

-- ---- from OAI.Combinatorics.SecondNeighborhood.Pruning ----
namespace OAI

namespace SeymourSecondNeighborhood.Pruning

variable {X : Type*} [Fintype X] [DecidableEq X]

theorem pruning (r : X → X → Prop) : PruningStatement r := by
  intro R C
  obtain ⟨M, hM, hα, hβ⟩ := exists_augmented_maximum_matching r R C
  apply exists_pruning_of_augmented_matching_bound r R C M hM
  simpa only [Nat.add_comm] using
    augmented_matching_card_le_corners r R C M hM.1 hα hβ

end SeymourSecondNeighborhood.Pruning

end OAI

-- ---- from OAI.Combinatorics.SecondNeighborhood.ExtremalImages ----
namespace OAI

namespace SeymourSecondNeighborhood.Extremal

open Pruning
open scoped BigOperators

variable {V : Type*} [Fintype V] [DecidableEq V]

noncomputable section

theorem card_eq_sum_card_column (P : Finset (V × V)) :
    P.card = ∑ j : V, (column P j).card := by
  classical
  simpa only [← Finset.card_eq_sum_ones] using
    (Finset.sum_finset_product_right P Finset.univ (column P)
      (by intro z; simp) (f := fun _ => (1 : ℕ)))

theorem card_eq_sum_card_row (Q : Finset (V × V)) :
    Q.card = ∑ i : V, (row Q i).card := by
  classical
  simpa only [← Finset.card_eq_sum_ones] using
    (Finset.sum_finset_product Q Finset.univ (row Q)
      (by intro z; simp) (f := fun _ => (1 : ℕ)))

theorem strict_leftImage_growth [Nonempty V]
    (r : V → V → Prop) (P : Finset (V × V)) (hgrowth : StrictSubsetGrowth r)
    (hnonempty : ∀ j, (column P j).Nonempty)
    (hproper : ∀ j, column P j ≠ Finset.univ) :
    P.card + (leftImage r (leftImage r P)).card < 2 * (leftImage r P).card := by
  classical
  have hsum :
      (∑ j : V, ((column P j).card + (column (leftImage r (leftImage r P)) j).card)) <
        ∑ j : V, 2 * (column (leftImage r P) j).card := by
    apply Finset.sum_lt_sum_of_nonempty Finset.univ_nonempty
    intro j _
    simpa only [column_leftImage] using
      hgrowth (column P j) (hnonempty j) (hproper j)
  simpa only [Nat.two_mul, Finset.sum_add_distrib, ← card_eq_sum_card_column] using hsum

theorem strict_rightImage_growth [Nonempty V]
    (r : V → V → Prop) (Q : Finset (V × V)) (hgrowth : StrictSubsetGrowth r)
    (hnonempty : ∀ i, (row Q i).Nonempty)
    (hproper : ∀ i, row Q i ≠ Finset.univ) :
    Q.card + (rightImage r (rightImage r Q)).card < 2 * (rightImage r Q).card := by
  classical
  have hsum :
      (∑ i : V, ((row Q i).card + (row (rightImage r (rightImage r Q)) i).card)) <
        ∑ i : V, 2 * (row (rightImage r Q) i).card := by
    apply Finset.sum_lt_sum_of_nonempty Finset.univ_nonempty
    intro i _
    simpa only [row_rightImage] using
      hgrowth (row Q i) (hnonempty i) (hproper i)
  simpa only [Nat.two_mul, Finset.sum_add_distrib, ← card_eq_sum_card_row] using hsum

end
end SeymourSecondNeighborhood.Extremal

end OAI

-- ---- from OAI.Combinatorics.SecondNeighborhood.ExtremalCompatibility ----
namespace OAI

namespace SeymourSecondNeighborhood.Extremal

open Pruning

variable {V : Type*} [Fintype V] [DecidableEq V]

noncomputable section

theorem diagonal_compatible {r : V → V → Prop} (hr : IsOriented r) :
    Compatible r (diagonal : Finset (V × V)) diagonal := by
  intro a ha b hb hc
  have ha' := mem_diagonal.mp ha
  have hb' := mem_diagonal.mp hb
  have hreverse : r b.1 a.1 := by
    simpa only [← ha', ← hb'] using hc.2
  exact hr.asymmetric hc.1 hreverse

theorem diagonal_admissible {r : V → V → Prop} (hr : IsOriented r) :
    Admissible r (diagonal : Finset (V × V)) diagonal where
  compatible := diagonal_compatible hr
  diagonal_left := fun _ h => h
  diagonal_right := fun _ h => h

theorem column_nonempty_of_diagonal {P : Finset (V × V)}
    (hP : diagonal ⊆ P) (j : V) : (column P j).Nonempty := by
  refine ⟨j, mem_column.mpr ?_⟩
  exact hP (diagonal_mem j)

theorem row_nonempty_of_diagonal {Q : Finset (V × V)}
    (hQ : diagonal ⊆ Q) (i : V) : (row Q i).Nonempty := by
  refine ⟨i, mem_row.mpr ?_⟩
  exact hQ (diagonal_mem i)

theorem column_ne_univ_of_compatible {r : V → V → Prop} {P Q : Finset (V × V)}
    (hc : Compatible r P Q) (hQ : diagonal ⊆ Q)
    (hpos : PositiveIndegree r) (j : V) : column P j ≠ Finset.univ := by
  intro hfull
  obtain ⟨w, hwj⟩ := hpos j
  obtain ⟨p, hpw⟩ := hpos w
  have hp : (p, j) ∈ P := by
    apply mem_column.mp
    rw [hfull]
    exact Finset.mem_univ p
  exact hc (p, j) hp (w, w) (hQ (diagonal_mem w)) ⟨hpw, hwj⟩

theorem row_ne_univ_of_compatible {r : V → V → Prop} {P Q : Finset (V × V)}
    (hc : Compatible r P Q) (hP : diagonal ⊆ P)
    (hpos : PositiveIndegree r) (i : V) : row Q i ≠ Finset.univ := by
  intro hfull
  obtain ⟨w, hwi⟩ := hpos i
  obtain ⟨s, hsw⟩ := hpos w
  have hs : (i, s) ∈ Q := by
    apply mem_row.mp
    rw [hfull]
    exact Finset.mem_univ s
  exact hc (w, w) (hP (diagonal_mem w)) (i, s) hs ⟨hwi, hsw⟩

theorem Admissible.strict_leftImage_growth [Nonempty V]
    {r : V → V → Prop} {P Q : Finset (V × V)} (h : Admissible r P Q)
    (hpos : PositiveIndegree r) (hgrowth : StrictSubsetGrowth r) :
    P.card + (leftImage r (leftImage r P)).card < 2 * (leftImage r P).card :=
  Extremal.strict_leftImage_growth r P hgrowth
    (column_nonempty_of_diagonal h.diagonal_left)
    (column_ne_univ_of_compatible h.compatible h.diagonal_right hpos)

theorem Admissible.strict_rightImage_growth [Nonempty V]
    {r : V → V → Prop} {P Q : Finset (V × V)} (h : Admissible r P Q)
    (hpos : PositiveIndegree r) (hgrowth : StrictSubsetGrowth r) :
    Q.card + (rightImage r (rightImage r Q)).card < 2 * (rightImage r Q).card :=
  Extremal.strict_rightImage_growth r Q hgrowth
    (row_nonempty_of_diagonal h.diagonal_right)
    (row_ne_univ_of_compatible h.compatible h.diagonal_left hpos)

theorem H_candidates_subset_uncovered (r : V → V → Prop) (P Q : Finset (V × V)) :
    H r (leftCandidate r Q) (rightCandidate r P) ⊆ uncovered r P Q := by
  intro z hz
  obtain ⟨i, j, hleft, hright, hpi, hsj⟩ := mem_H.mp hz
  apply mem_uncovered.mpr
  intro hcovered
  rcases hcovered with hcovered | hcovered
  · apply mem_rightCandidate.mp hright
    exact mem_leftImage.mpr ⟨z.1, hcovered, hpi⟩
  · apply mem_leftCandidate.mp hleft
    exact mem_rightImage.mpr ⟨z.2, hcovered, hsj⟩

theorem H_candidates_card_le_uncovered (r : V → V → Prop) (P Q : Finset (V × V)) :
    (H r (leftCandidate r Q) (rightCandidate r P)).card ≤ (uncovered r P Q).card :=
  Finset.card_le_card (H_candidates_subset_uncovered r P Q)

end
end SeymourSecondNeighborhood.Extremal

end OAI

-- ---- from OAI.Combinatorics.SecondNeighborhood.ExtremalCounting ----
namespace OAI

namespace SeymourSecondNeighborhood.Extremal

open Pruning

variable {V : Type*} [Fintype V] [DecidableEq V]

noncomputable section

theorem uncoveredCount_add_images {r : V → V → Prop} {P Q : Finset (V × V)}
    (h : ConflictFree r P Q) :
    uncoveredCount r P Q + (leftImage r P).card + (rightImage r Q).card =
      (Finset.univ : Finset (V × V)).card := by
  classical
  have hc := Finset.card_sdiff_add_card_eq_card
    (Finset.subset_univ (leftImage r P ∪ rightImage r Q))
  rw [Finset.card_union_of_disjoint (conflictFree_iff_disjoint.mp h)] at hc
  simpa only [uncoveredCount, Nat.add_assoc] using hc

theorem uncoveredZ_card_le (r : V → V → Prop) (R C P Q : Finset (V × V)) :
    (uncoveredZ r R C P Q).card ≤ uncoveredCount r P Q := by
  classical
  apply Finset.card_le_card
  intro z hz
  obtain ⟨_, hn⟩ := mem_uncoveredZ.mp hz
  exact Finset.mem_sdiff.mpr ⟨Finset.mem_univ z, fun h =>
    hn (Finset.mem_union.mp h)⟩

theorem objective_lt_of_pruning {r : V → V → Prop}
    {P Q R C P' Q' : Finset (V × V)}
    (hpr : PruningResult r R C P' Q')
    (hH : (H r R C).card ≤ uncoveredCount r P Q)
    (hgain : P.card + Q.card + 2 * uncoveredCount r P Q < R.card + C.card) :
    objective r P Q < objective r P' Q' := by
  have hZ := uncoveredZ_card_le r R C P' Q'
  have hR := Finset.card_sdiff_add_card_eq_card hpr.subset_left
  have hC := Finset.card_sdiff_add_card_eq_card hpr.subset_right
  have hdel := hpr.deletion_bound
  unfold objective
  omega

end

end SeymourSecondNeighborhood.Extremal

end OAI

-- ---- from OAI.Combinatorics.SecondNeighborhood.ExtremalContradiction ----
namespace OAI

namespace SeymourSecondNeighborhood.Extremal

open Pruning

variable {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V]

theorem complement_gain {r : V → V → Prop} {P Q : Finset (V × V)}
    (h : Admissible r P Q) (hpos : PositiveIndegree r)
    (hgrowth : StrictSubsetGrowth r) :
    P.card + Q.card + 2 * uncoveredCount r P Q <
      (leftCandidate r Q).card + (rightCandidate r P).card := by
  classical
  have hleft := h.strict_leftImage_growth hpos hgrowth
  have hright := h.strict_rightImage_growth hpos hgrowth
  have huncovered := uncoveredCount_add_images h.compatible
  have hR : (leftCandidate r Q).card +
      (rightImage r (rightImage r Q)).card = (Finset.univ : Finset (V × V)).card :=
    Finset.card_sdiff_add_card_eq_card (Finset.subset_univ _)
  have hC : (rightCandidate r P).card +
      (leftImage r (leftImage r P)).card = (Finset.univ : Finset (V × V)).card :=
    Finset.card_sdiff_add_card_eq_card (Finset.subset_univ _)
  omega

theorem no_strictSubsetGrowth_of_pruning {r : V → V → Prop}
    (hr : IsOriented r) (hpos : PositiveIndegree r)
    (hprune : PruningStatement r) : ¬ StrictSubsetGrowth r := by
  classical
  intro hgrowth
  obtain ⟨P, Q, h, hmax⟩ := exists_maximizing_pair r (Admissible r)
    ⟨diagonal, diagonal, diagonal_admissible hr⟩
  obtain ⟨P', Q', hp⟩ := hprune (leftCandidate r Q) (rightCandidate r P)
  have hnext : Admissible r P' Q' := pruning_preserves_diagonal h hp
  have hH : (H r (leftCandidate r Q) (rightCandidate r P)).card ≤
      uncoveredCount r P Q := by
    exact H_candidates_card_le_uncovered r P Q
  have hbetter := objective_lt_of_pruning hp hH (complement_gain h hpos hgrowth)
  exact (not_lt_of_ge (hmax P' Q' hnext)) hbetter

end SeymourSecondNeighborhood.Extremal

end OAI

-- ---- from OAI.Combinatorics.SecondNeighborhood.Main ----
namespace OAI

namespace SeymourSecondNeighborhood

variable {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V]

theorem exists_goodVertex (r : V → V → Prop) (hr : IsOriented r) :
    ∃ v, GoodVertex r v := by
  classical
  by_contra h
  have hcounter : Counterexample r := (counterexample_iff_not_conjecture r).mpr h
  obtain ⟨n, hn, g, hg, hpos, hgrowth⟩ := counterexample_reduction hr hcounter
  let : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  exact Extremal.no_strictSubsetGrowth_of_pruning hg hpos (Pruning.pruning g) hgrowth

end SeymourSecondNeighborhood

end OAI

-- ---- mission target ----
open OAI OAI.SeymourSecondNeighborhood
variable {V : Type*}
variable [Fintype V] [DecidableEq V]
variable [Nonempty V]

namespace OAI
namespace SeymourSecondNeighborhood
theorem _root_.solution (r : V → V → Prop) (hr : IsOriented r) :
    ∃ v, GoodVertex r v := by
  first
    | exact OAI.SeymourSecondNeighborhood.exists_goodVertex r hr
    | exact OAI.SeymourSecondNeighborhood.exists_goodVertex
    | (apply OAI.SeymourSecondNeighborhood.exists_goodVertex <;> assumption)
    | (intros; apply OAI.SeymourSecondNeighborhood.exists_goodVertex <;> assumption)
end SeymourSecondNeighborhood
end OAI
