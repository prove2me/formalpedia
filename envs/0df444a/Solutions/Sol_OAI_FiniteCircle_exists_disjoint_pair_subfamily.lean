-- Prove2me | solution 1 for OAI.FiniteCircle.exists_disjoint_pair_subfamily
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T16:35:51.583724+00:00
-- url     : https://prove2.me/submissions/b15cd91a-aaa4-40aa-b4f5-58aa879171f2

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/FiniteCircle/BitCounting.lean:L11-L73
-- (upload_full_project.md Phase 4): solution for node OAI.FiniteCircle.exists_disjoint_pair_subfamily. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_FiniteCircle
import Definitions.Def_OAI_Combinatorics_FiniteCircle_Model
import Definitions.Def_OAI_Combinatorics_FiniteCircle_Edit
import Definitions.Def_OAI_Combinatorics_FiniteCircle_Matching
import Definitions.Def_OAI_Combinatorics_FiniteCircle_TaggedRows
import Definitions.Def_OAI_Combinatorics_FiniteCircle_PhaseCost
import Definitions.Def_OAI_Combinatorics_FiniteCircle_CircleWords
import Definitions.Def_OAI_Combinatorics_FiniteCircle_MaskSeparation
import Definitions.Def_OAI_Combinatorics_FiniteCircle_ExcludedSeparation
import Definitions.Def_OAI_Combinatorics_FiniteCircle_MaskDescent
import Definitions.Def_OAI_Combinatorics_FiniteCircle_ExcludedDescent
import Definitions.Def_OAI_Combinatorics_FiniteCircle_Primes
import Definitions.Def_OAI_Combinatorics_FiniteCircle_Fourier
import Definitions.Def_OAI_Combinatorics_FiniteCircle_DyadicShifts
import Definitions.Def_OAI_Combinatorics_FiniteCircle_MaskBranching
import Definitions.Def_OAI_Combinatorics_FiniteCircle_TreeBranching
import Definitions.Def_OAI_Combinatorics_FiniteCircle_Translations
import Definitions.Def_OAI_Combinatorics_FiniteCircle_Distortion
import Definitions.Def_OAI_Combinatorics_FiniteCircle_BlockMatching
import Definitions.Def_OAI_Combinatorics_FiniteCircle_OffsetRecovery

-- ---- from OAI.Combinatorics.FiniteCircle.BitCounting ----
namespace OAI

namespace FiniteCircle

open scoped BigOperators List
open scoped ComplexConjugate
open RCLike Module

theorem exists_disjoint_pair_subfamily {ι J : Type*} [DecidableEq ι] [DecidableEq J]
    (f g : ι → J) (hf : Function.Injective f) (hg : Function.Injective g)
    (I : Finset ι) (hne : ∀ i ∈ I, f i ≠ g i) :
    ∃ S ⊆ I, I.card ≤ 3*S.card ∧ ∀ i ∈ S, ∀ j ∈ S, f i ≠ g j := by
  induction I using Finset.strongInductionOn
  rename_i I ih
  by_cases he : I.Nonempty
  · obtain ⟨k, hk⟩ := he
    let N := I.filter (fun i => i = k ∨ f i = g k ∨ g i = f k)
    let T := I \ N
    have hkN : k ∈ N := Finset.mem_filter.mpr ⟨hk, Or.inl rfl⟩
    have hN : N ⊆ I := Finset.filter_subset _ _
    have hT : T ⊂ I := Finset.ssubset_iff_subset_ne.mpr ⟨Finset.sdiff_subset, by
      intro heq
      have hmem : k ∈ T := heq.symm ▸ hk
      exact (Finset.mem_sdiff.mp hmem).2 hkN⟩
    have hca : (I.filter (fun i => f i = g k)).card ≤ 1 := by
      apply Finset.card_le_one.mpr
      intro i hi j hj
      exact hf ((Finset.mem_filter.mp hi).2.trans (Finset.mem_filter.mp hj).2.symm)
    have hcb : (I.filter (fun i => g i = f k)).card ≤ 1 := by
      apply Finset.card_le_one.mpr
      intro i hi j hj
      exact hg ((Finset.mem_filter.mp hi).2.trans (Finset.mem_filter.mp hj).2.symm)
    have hsub : N ⊆ {k} ∪ I.filter (fun i => f i = g k) ∪ I.filter (fun i => g i = f k) := by
      intro i hi
      obtain ⟨hi, hn⟩ := Finset.mem_filter.mp hi
      rcases hn with rfl | ha | hb
      · simp
      · exact Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hi, ha⟩))
      · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hi, hb⟩)
    have hNc : N.card ≤ 3 := by
      have h1 := Finset.card_le_card hsub
      have h2 := Finset.card_union_le ({k} ∪ I.filter (fun i => f i = g k)) (I.filter (fun i => g i = f k))
      have h3 := Finset.card_union_le ({k} : Finset ι) (I.filter (fun i => f i = g k))
      simp only [Finset.card_singleton] at h3
      omega
    obtain ⟨S, hST, hc, hcross⟩ := ih T hT (fun i hi => hne i (Finset.sdiff_subset hi))
    have hkS : k ∉ S := fun hks => (Finset.mem_sdiff.mp (hST hks)).2 hkN
    refine ⟨insert k S, Finset.insert_subset_iff.mpr ⟨hk, hST.trans Finset.sdiff_subset⟩, ?_, ?_⟩
    · rw [Finset.card_insert_of_notMem hkS]
      have hIc : T.card = I.card - N.card := Finset.card_sdiff_of_subset hN
      have hNi := Finset.card_le_card hN
      omega
    · intro i hi j hj
      rcases Finset.mem_insert.mp hi with hi | hi
      · subst i
        rcases Finset.mem_insert.mp hj with hj | hj
        · subst j
          exact hne k hk
        · intro hh
          have hjI := (Finset.mem_sdiff.mp (hST hj)).1
          have hjN := (Finset.mem_sdiff.mp (hST hj)).2
          exact hjN (Finset.mem_filter.mpr ⟨hjI, Or.inr (Or.inr hh.symm)⟩)
      · rcases Finset.mem_insert.mp hj with hj | hj
        · subst j
          intro hh
          have hiI := (Finset.mem_sdiff.mp (hST hi)).1
          have hiN := (Finset.mem_sdiff.mp (hST hi)).2
          exact hiN (Finset.mem_filter.mpr ⟨hiI, Or.inr (Or.inl hh)⟩)
        · exact hcross i hi j hj
  · refine ⟨∅, Finset.empty_subset _, ?_, by simp⟩
    simp [Finset.not_nonempty_iff_eq_empty.mp he]

end FiniteCircle

end OAI

-- ---- platform node ----
open OAI OAI.FiniteCircle
open scoped BigOperators List
open scoped ComplexConjugate
open RCLike Module


theorem solution : type_of% @_root_.OAI.FiniteCircle.exists_disjoint_pair_subfamily := @_root_.OAI.FiniteCircle.exists_disjoint_pair_subfamily
