-- Prove2me | solution 1 for OAI.SeymourSecondNeighborhood.Pruning.exists_pruning_of_augmented_cover
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T13:23:43.820388+00:00
-- url     : https://prove2.me/submissions/19f60ea8-afd7-47db-9c71-0cb8d0856b7b

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/SecondNeighborhood/CoverPruning.lean:L13-L126
-- (upload_full_project.md Phase 4): solution for node OAI.SeymourSecondNeighborhood.Pruning.exists_pruning_of_augmented_cover. The node keeps its source
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

-- ---- from OAI.Combinatorics.SecondNeighborhood.PruningDefinitions ----
namespace OAI

namespace SeymourSecondNeighborhood.Pruning

variable {V : Type*}

variable [Fintype V] [DecidableEq V]

noncomputable section

theorem exists_leftCovers_iff {r : V → V → Prop} {R : Finset (V × V)}
    {z : V × V} : (∃ a ∈ R, LeftCovers r a z) ↔ z ∈ leftImage r R := by
  constructor
  · rintro ⟨⟨p, j⟩, ha, hj, hpi⟩
    apply mem_leftImage.mpr
    refine ⟨p, ?_, hpi⟩
    change j = z.2 at hj
    simpa only [hj] using ha
  · intro hz
    obtain ⟨p, hp, hpi⟩ := mem_leftImage.mp hz
    exact ⟨(p, z.2), hp, rfl, hpi⟩

theorem exists_rightCovers_iff {r : V → V → Prop} {C : Finset (V × V)}
    {z : V × V} : (∃ b ∈ C, RightCovers r b z) ↔ z ∈ rightImage r C := by
  constructor
  · rintro ⟨⟨i, s⟩, hb, hi, hsj⟩
    apply mem_rightImage.mpr
    refine ⟨s, ?_, hsj⟩
    change i = z.1 at hi
    simpa only [hi] using hb
  · intro hz
    obtain ⟨s, hs, hsj⟩ := mem_rightImage.mp hz
    exact ⟨(z.1, s), hs, rfl, hsj⟩

theorem conflictFree_left_not_covers_Z {r : V → V → Prop}
    {R C : Finset (V × V)} {a z : V × V}
    (ha : ∀ b ∈ C, ¬ Conflict r a b) (hz : z ∈ Z r R C) :
    ¬ LeftCovers r a z := by
  intro hc
  obtain ⟨p, s, _, hs, _, hsj⟩ := mem_Z.mp hz
  apply ha (z.1, s) hs
  refine ⟨hc.2, ?_⟩
  simpa only [hc.1] using hsj

theorem conflictFree_right_not_covers_Z {r : V → V → Prop}
    {R C : Finset (V × V)} {b z : V × V}
    (hb : ∀ a ∈ R, ¬ Conflict r a b) (hz : z ∈ Z r R C) :
    ¬ RightCovers r b z := by
  intro hc
  obtain ⟨p, s, hp, _, hpi, _⟩ := mem_Z.mp hz
  apply hb (p, z.2) hp
  refine ⟨?_, hc.2⟩
  simpa only [hc.1] using hpi

end
end SeymourSecondNeighborhood.Pruning

end OAI

-- ---- from OAI.Combinatorics.SecondNeighborhood.CoverPruning ----
namespace OAI

namespace SeymourSecondNeighborhood.Pruning

open Bipartite

variable {V : Type*} [Fintype V] [DecidableEq V]

private theorem exists_pruning_of_augmented_cover
    (r : V → V → Prop) (R C : Finset (V × V))
    (A : Finset (LeftVertex r R C)) (B : Finset (RightVertex r R C))
    (hcover : IsVertexCover (AugmentedEdge r R C) A B)
    (hA : ∀ a ∈ A, ∃ b, AugmentedEdge r R C a b)
    (hB : ∀ b ∈ B, ∃ a, AugmentedEdge r R C a b)
    (hbound : A.card + B.card ≤ (H r R C).card + (Z r R C).card) :
    ∃ R' C', PruningResult r R C R' C' := by
  classical
  let DR : Finset (V × V) := A.toLeft.image (fun a : R => (a : V × V))
  let DC : Finset (V × V) := B.toLeft.image (fun b : C => (b : V × V))
  let R' : Finset (V × V) := R \ DR
  let C' : Finset (V × V) := C \ DC
  have hDR : DR ⊆ R := by
    intro a ha
    obtain ⟨a', _, rfl⟩ := Finset.mem_image.mp ha
    exact a'.property
  have hDC : DC ⊆ C := by
    intro b hb
    obtain ⟨b', _, rfl⟩ := Finset.mem_image.mp hb
    exact b'.property
  have hR' : R' ⊆ R := Finset.sdiff_subset
  have hC' : C' ⊆ C := Finset.sdiff_subset
  have hsurvL (a : R) (ha : (a : V × V) ∈ R') : Sum.inl a ∉ A := by
    intro haA
    exact (Finset.mem_sdiff.mp ha).2
      (Finset.mem_image_of_mem _ (Finset.mem_toLeft.mpr haA))
  have hsurvR (b : C) (hb : (b : V × V) ∈ C') : Sum.inl b ∉ B := by
    intro hbB
    exact (Finset.mem_sdiff.mp hb).2
      (Finset.mem_image_of_mem _ (Finset.mem_toLeft.mpr hbB))
  have hconflictFree : ConflictFree r R' C' := by
    intro a ha b hb hab
    let a' : R := ⟨a, hR' ha⟩
    let b' : C := ⟨b, hC' hb⟩
    rcases hcover (Sum.inl a') (Sum.inl b') hab with haA | hbB
    · exact hsurvL a' ha haA
    · exact hsurvR b' hb hbB
  have hretainL : ∀ a ∈ R, (∀ b ∈ C, ¬ Conflict r a b) → a ∈ R' := by
    intro a ha hfree
    apply Finset.mem_sdiff.mpr
    refine ⟨ha, ?_⟩
    intro haDR
    obtain ⟨a', haA, hval⟩ := Finset.mem_image.mp haDR
    obtain ⟨b, hab⟩ := hA (Sum.inl a') (Finset.mem_toLeft.mp haA)
    cases b with
    | inl b =>
        change Conflict r (a' : V × V) (b : V × V) at hab
        apply hfree b b.property
        simpa only [hval] using hab
    | inr z =>
        change LeftCovers r (a' : V × V) (z : V × V) at hab
        apply conflictFree_left_not_covers_Z hfree z.property
        simpa only [hval] using hab
  have hretainR : ∀ b ∈ C, (∀ a ∈ R, ¬ Conflict r a b) → b ∈ C' := by
    intro b hb hfree
    apply Finset.mem_sdiff.mpr
    refine ⟨hb, ?_⟩
    intro hbDC
    obtain ⟨b', hbB, hval⟩ := Finset.mem_image.mp hbDC
    obtain ⟨a, hab⟩ := hB (Sum.inl b') (Finset.mem_toLeft.mp hbB)
    cases a with
    | inl a =>
        change Conflict r (a : V × V) (b' : V × V) at hab
        apply hfree a a.property
        simpa only [hval] using hab
    | inr z =>
        change RightCovers r (b' : V × V) (z : V × V) at hab
        apply conflictFree_right_not_covers_Z hfree z.property
        simpa only [hval] using hab
  let T : Finset (V × V) := (Z r R C).filter (Covered r R' C')
  have hcharged : T ⊆ (A.toRight ∪ B.toRight).image
      (fun z : Z r R C => (z : V × V)) := by
    intro z hz
    obtain ⟨hzZ, hzcovered⟩ := Finset.mem_filter.mp hz
    let z' : Z r R C := ⟨z, hzZ⟩
    apply Finset.mem_image.mpr
    refine ⟨z', ?_, rfl⟩
    rcases hzcovered with hzL | hzR
    · obtain ⟨a, ha, haz⟩ := exists_leftCovers_iff.mpr hzL
      let a' : R := ⟨a, hR' ha⟩
      have hzB : Sum.inr z' ∈ B :=
        (hcover (Sum.inl a') (Sum.inr z') haz).resolve_left (hsurvL a' ha)
      exact Finset.mem_union_right _ (Finset.mem_toRight.mpr hzB)
    · obtain ⟨b, hb, hbz⟩ := exists_rightCovers_iff.mpr hzR
      let b' : C := ⟨b, hC' hb⟩
      have hzA : Sum.inr z' ∈ A :=
        (hcover (Sum.inr z') (Sum.inl b') hbz).resolve_right (hsurvR b' hb)
      exact Finset.mem_union_left _ (Finset.mem_toRight.mpr hzA)
  have hTcard : T.card ≤ A.toRight.card + B.toRight.card := by
    calc
      T.card ≤ ((A.toRight ∪ B.toRight).image
          (fun z : Z r R C => (z : V × V))).card := Finset.card_le_card hcharged
      _ = (A.toRight ∪ B.toRight).card :=
        Finset.card_image_of_injective _ Subtype.val_injective
      _ ≤ A.toRight.card + B.toRight.card := Finset.card_union_le _ _
  have hpartition : T.card + (uncoveredZ r R C R' C').card = (Z r R C).card := by
    exact Finset.card_filter_add_card_filter_not
      (s := Z r R C) (Covered r R' C')
  have hdelL : (R \ R').card = A.toLeft.card := by
    change (R \ (R \ DR)).card = A.toLeft.card
    rw [Finset.sdiff_sdiff_eq_self hDR]
    exact Finset.card_image_of_injective _ Subtype.val_injective
  have hdelR : (C \ C').card = B.toLeft.card := by
    change (C \ (C \ DC)).card = B.toLeft.card
    rw [Finset.sdiff_sdiff_eq_self hDC]
    exact Finset.card_image_of_injective _ Subtype.val_injective
  have hAsplit : A.toLeft.card + A.toRight.card = A.card :=
    Finset.card_toLeft_add_card_toRight
  have hBsplit : B.toLeft.card + B.toRight.card = B.card :=
    Finset.card_toLeft_add_card_toRight
  refine ⟨R', C', hR', hC', hconflictFree, hretainL, hretainR, ?_⟩
  rw [hdelL, hdelR]
  omega

end SeymourSecondNeighborhood.Pruning

end OAI

-- ---- platform node ----
open OAI OAI.SeymourSecondNeighborhood OAI.SeymourSecondNeighborhood.Pruning
open Bipartite


theorem solution : type_of% @_root_.OAI.SeymourSecondNeighborhood.Pruning.exists_pruning_of_augmented_cover := @_root_.OAI.SeymourSecondNeighborhood.Pruning.exists_pruning_of_augmented_cover
