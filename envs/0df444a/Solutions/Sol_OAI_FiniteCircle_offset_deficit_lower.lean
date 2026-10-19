-- Prove2me | solution 1 for OAI.FiniteCircle.offset_deficit_lower
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T16:34:06.624926+00:00
-- url     : https://prove2.me/submissions/acff7431-cc60-4535-a319-9f87fde34e87

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/FiniteCircle/OffsetRecovery.lean:L377-L442
-- (upload_full_project.md Phase 4): solution for node OAI.FiniteCircle.offset_deficit_lower. The node keeps its source
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
import Theorems.Thm_OAI_FiniteCircle_WordMatching_block_after_card_le
import Theorems.Thm_OAI_FiniteCircle_WordMatching_block_before_card_le
import Theorems.Thm_OAI_FiniteCircle_WordMatching_offset_deficit_le
import Theorems.Thm_OAI_FiniteCircle_WordMatching_offset_interior_labels
import Theorems.Thm_OAI_FiniteCircle_WordMatching_sourceBlock_card_le
import Theorems.Thm_OAI_FiniteCircle_WordMatching_targetBlocks_card_le_three

-- ---- from OAI.Combinatorics.FiniteCircle.Matching ----
namespace OAI

namespace FiniteCircle

open scoped BigOperators List

namespace Slide
variable {α : Type*} {x y : List α}

end Slide

namespace SlidePath
variable {α : Type*} {x y z : List α} {n m : ℕ}

end SlidePath

namespace WordMatching
variable {α : Type*} {x y : List α} {q : ℕ}

theorem rightSpan_disjoint (A : WordMatching x y q) {S T : Finset (Fin q)}
    (h : ∀ i ∈ S, ∀ j ∈ T, i < j) : Disjoint (A.rightSpan S) (A.rightSpan T) := by
  apply Finset.disjoint_left.mpr
  intro z hz hw
  obtain ⟨_, i, hi, k, hk, hiz, hzk⟩ := Finset.mem_filter.mp hz
  obtain ⟨_, j, hj, l, hl, hjz, hzl⟩ := Finset.mem_filter.mp hw
  have hkj : A.right k < A.right j := A.right.strictMono (h k hk j hj)
  exact (not_lt_of_ge (hjz.trans hzk)) hkj

theorem sum_span_card_le {ι : Type*} [Fintype ι] [LinearOrder ι]
    (A : WordMatching x y q) (S : ι → Finset (Fin q))
    (h : ∀ i j, i < j → ∀ u ∈ S i, ∀ v ∈ S j, u < v) :
    ∑ i, (A.rightSpan (S i)).card ≤ y.length := by
  classical
  have hdis : (↑(Finset.univ : Finset ι) : Set ι).PairwiseDisjoint (fun i => A.rightSpan (S i)) := by
    intro i _ j _ hij
    rcases lt_or_gt_of_ne hij with hij | hij
    · exact A.rightSpan_disjoint (h i j hij)
    · exact (A.rightSpan_disjoint (h j i hij)).symm
  rw [← Finset.card_biUnion hdis]
  exact (Finset.card_le_card (Finset.subset_univ _)).trans_eq (Fintype.card_fin _)

end WordMatching

theorem exists_lcs_matching {α : Type*} (x y : List α) :
    Nonempty (WordMatching x y (lcs x y)) := by
  obtain ⟨z, hx, hy, hz⟩ := lcs_exists x y
  obtain ⟨f, hf⟩ := List.sublist_iff_exists_fin_orderEmbedding_get_eq.mp hx
  obtain ⟨g, hg⟩ := List.sublist_iff_exists_fin_orderEmbedding_get_eq.mp hy
  let e := (Fin.castOrderIso hz.symm).toOrderEmbedding
  exact ⟨⟨e.trans f, e.trans g, fun i => (hf (e i)).symm.trans (hg (e i))⟩⟩

namespace WordMatching
variable {α : Type*} {x y : List α} {q : ℕ}

theorem sum_sourceBlock_card (A : WordMatching x y q) {w L : ℕ} (hw : 0 < w)
    (hx : x.length = w*L) : ∑ i : Fin L, (A.sourceBlock w i).card = q := by
  let f : Fin q → Fin L := fun k => ⟨(A.left k).val / w, by
    apply (Nat.div_lt_iff_lt_mul hw).mpr
    simpa only [hx, Nat.mul_comm] using (A.left k).isLt⟩
  have hh (i : Fin L) : A.sourceBlock w i = Finset.univ.filter (fun k => f k = i) := by
    ext k
    simp only [mem_sourceBlock, Finset.mem_filter, Finset.mem_univ, true_and, Fin.ext_iff, f]
  simp_rw [hh]
  simpa using Finset.sum_card_fiberwise_eq_card_filter (Finset.univ : Finset (Fin q))
    (Finset.univ : Finset (Fin L)) f

theorem sourceBlock_order (A : WordMatching x y q) {w i j : ℕ} (hij : i < j)
    {k l : Fin q} (hk : k ∈ A.sourceBlock w i) (hl : l ∈ A.sourceBlock w j) : k < l := by
  by_contra h
  have hkl := A.left.monotone (not_lt.mp h)
  have hd := Nat.div_le_div_right (c := w) (show (A.left l).val ≤ (A.left k).val from hkl)
  rw [← (A.mem_sourceBlock w i k).mp hk, ← (A.mem_sourceBlock w j l).mp hl] at hij
  omega

theorem card_le_rightSpan (A : WordMatching x y q) (S : Finset (Fin q)) :
    S.card ≤ (A.rightSpan S).card := by
  have hmaps : Set.MapsTo A.right (↑S : Set (Fin q)) (↑(A.rightSpan S) : Set (Fin y.length)) := by
    intro k hk
    change A.right k ∈ A.rightSpan S
    simp only [rightSpan, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨k, hk, k, hk, le_rfl, le_rfl⟩
  exact Finset.card_le_card_of_injOn A.right hmaps A.right.injective.injOn

theorem sum_sourceLoss (A : WordMatching x y q) {w L : ℕ} (hw : 0 < w)
    (hx : x.length = w*L) : ∑ i : Fin L, A.sourceLoss w i = w*L-q := by
  have he : (∑ i : Fin L, A.sourceLoss w i) + q = w*L := by
    conv_lhs => rhs; rw [← A.sum_sourceBlock_card hw hx]
    rw [← Finset.sum_add_distrib]
    simp only [sourceLoss, Nat.sub_add_cancel (A.sourceBlock_card_le hw _),
      Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul, Nat.mul_comm]
  omega

theorem sum_spanLoss_le (A : WordMatching x y q) {w L : ℕ} (hw : 0 < w)
    (hx : x.length = w*L) (hy : y.length = w*L) : ∑ i : Fin L, A.spanLoss w i ≤ w*L-q := by
  have he : (∑ i : Fin L, A.spanLoss w i) + q =
      ∑ i : Fin L, (A.rightSpan (A.sourceBlock w i)).card := by
    conv_lhs => rhs; rw [← A.sum_sourceBlock_card hw hx]
    rw [← Finset.sum_add_distrib]
    simp only [spanLoss, Nat.sub_add_cancel (A.card_le_rightSpan _)]
  have hle := A.sum_span_card_le (fun i : Fin L => A.sourceBlock w i)
    (fun _ _ hij _ hk _ hl => A.sourceBlock_order hij hk hl)
  have hle' := hle.trans_eq hy
  omega

end WordMatching

namespace WordMatching
variable {α : Type*} {x y : List α} {q : ℕ}

end WordMatching

end FiniteCircle

end OAI

-- ---- from OAI.Combinatorics.FiniteCircle.AnchorRecovery ----
namespace OAI

namespace FiniteCircle

open scoped BigOperators List
open scoped ComplexConjugate
open RCLike Module

namespace WordMatching
variable {α : Type*} {x y : List α} {w q : ℕ} {c : α → Fin w → Bool}

end WordMatching

namespace WordMatching
variable {α : Type*} {x y : List α} {q : ℕ}

theorem mod_injectiveOn (A : WordMatching x y q) {w i : ℕ} :
    Set.InjOn (fun k : Fin q => (A.left k).val%w) (↑(A.sourceBlock w i) : Set (Fin q)) := by
  intro k hk l hl he
  change (A.left k).val%w = (A.left l).val%w at he
  apply A.left.injective
  apply Fin.ext
  have h1 := Nat.mod_add_div (A.left k).val w
  have h2 := Nat.mod_add_div (A.left l).val w
  rw [(A.mem_sourceBlock w i k).mp hk, he] at h1
  rw [(A.mem_sourceBlock w i l).mp hl] at h2
  omega

end WordMatching

namespace WordMatching
variable {α : Type*} {x y : List α} {w q : ℕ} {c : α → Fin w → Bool}

end WordMatching

end FiniteCircle

end OAI

-- ---- from OAI.Combinatorics.FiniteCircle.OffsetRecovery ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

namespace FiniteCircle

open scoped BigOperators List
open scoped ComplexConjugate
open RCLike Module

namespace WordMatching
variable {α : Type*} {x y : List α} {q : ℕ}

theorem common_offset_duplicate_loss (A : WordMatching x y q) {w i j t : ℕ} (hw : 0 < w)
    (hij : i < j) {k l : Fin q} (hk : k ∈ A.blockPair w i t) (hl : l ∈ A.blockPair w j t)
    (hmod : (A.left k).val%w = (A.left l).val%w) :
    (A.right k).val%w < A.sourceLoss w i + A.sourceLoss w j := by
  obtain ⟨hki, hkt⟩ := Finset.mem_inter.mp hk
  obtain ⟨hlj, hlt⟩ := Finset.mem_inter.mp hl
  let T := (A.sourceBlock w i).filter (fun v => k ≤ v)
  let U := (A.sourceBlock w j).filter (fun v => v ≤ l)
  have hdis : Disjoint T U := by
    apply Finset.disjoint_left.mpr
    intro v hv hu
    exact (lt_irrefl v) (A.sourceBlock_order hij (Finset.mem_filter.mp hv).1 (Finset.mem_filter.mp hu).1)
  have hmaps : Set.MapsTo A.right (↑(T ∪ U) : Set (Fin q))
      (↑(Finset.Icc (A.right k) (A.right l)) : Set (Fin y.length)) := by
    intro v hv
    change A.right v ∈ Finset.Icc (A.right k) (A.right l)
    rcases Finset.mem_union.mp hv with hv | hv
    · obtain ⟨hv, hkv⟩ := Finset.mem_filter.mp hv
      exact Finset.mem_Icc.mpr ⟨A.right.monotone hkv,
        A.right.monotone (A.sourceBlock_order hij hv hlj).le⟩
    · obtain ⟨hv, hvl⟩ := Finset.mem_filter.mp hv
      exact Finset.mem_Icc.mpr ⟨A.right.monotone (A.sourceBlock_order hij hki hv).le,
        A.right.monotone hvl⟩
  have hc := Finset.card_le_card_of_injOn A.right hmaps A.right.injective.injOn
  rw [Finset.card_union_of_disjoint hdis, Fin.card_Icc] at hc
  have hb := A.block_before_card_le hki
  have ha := A.block_after_card_le hw hlj
  have hTi : T.card + ((A.sourceBlock w i).filter (fun v => v < k)).card = (A.sourceBlock w i).card := by
    simpa only [not_le] using Finset.card_filter_add_card_filter_not (s := A.sourceBlock w i) (p := fun v => k ≤ v)
  have hUj : U.card + ((A.sourceBlock w j).filter (fun v => l < v)).card = (A.sourceBlock w j).card := by
    simpa only [not_le] using Finset.card_filter_add_card_filter_not (s := A.sourceBlock w j) (p := fun v => v ≤ l)
  have hXi : A.sourceLoss w i + (A.sourceBlock w i).card = w := Nat.sub_add_cancel (A.sourceBlock_card_le hw i)
  have hXj : A.sourceLoss w j + (A.sourceBlock w j).card = w := Nat.sub_add_cancel (A.sourceBlock_card_le hw j)
  have hrk := Nat.mod_add_div (A.right k).val w
  have hrl := Nat.mod_add_div (A.right l).val w
  have hkt' : (A.right k).val/w = t := (A.symm.mem_sourceBlock w t k).mp hkt
  have hlt' : (A.right l).val/w = t := (A.symm.mem_sourceBlock w t l).mp hlt
  rw [hkt'] at hrk
  rw [hlt'] at hrl
  have hklt := Nat.mod_lt (A.left k).val hw
  have hllt := Nat.mod_lt (A.left l).val hw
  have hrl_lt := Nat.mod_lt (A.right l).val hw
  have hkl : (A.right k).val ≤ (A.right l).val := A.right.monotone (A.sourceBlock_order hij hki hlj).le
  omega

theorem common_offset_duplicates_card (A : WordMatching x y q) {w i : ℕ}
    (hw : 0 < w) (hspan : (A.rightSpan (A.sourceBlock w i)).card ≤ 2*w) :
    ((A.sourceBlock w i).filter (fun k => ∃ l ∈ A.sourceBlock w (i+1),
      (A.left k).val%w = (A.left l).val%w ∧
      (A.right k).val/w = (A.right l).val/w)).card ≤
      3*(A.sourceLoss w i + A.sourceLoss w (i+1)) := by
  classical
  let S := (A.sourceBlock w i).filter (fun k => ∃ l ∈ A.sourceBlock w (i+1),
      (A.left k).val%w = (A.left l).val%w ∧
      (A.right k).val/w = (A.right l).val/w)
  let d := A.sourceLoss w i + A.sourceLoss w (i+1)
  let f : Fin q → ℕ × ℕ := fun k => ((A.right k).val/w,(A.right k).val%w)
  have hf : Function.Injective f := by
    intro k l h
    have h1 := congrArg Prod.fst h
    have h2 := congrArg Prod.snd h
    have hk := Nat.mod_add_div (A.right k).val w
    have hl := Nat.mod_add_div (A.right l).val w
    dsimp [f] at h1 h2
    rw [h1,h2] at hk
    exact A.right.injective (Fin.ext (by omega))
  have hmaps : S.image f ⊆ A.targetBlocks w (A.sourceBlock w i) ×ˢ Finset.range d := by
    intro v hv
    obtain ⟨k,hk,rfl⟩ := Finset.mem_image.mp hv
    obtain ⟨hki,l,hli,hmod,hdiv⟩ := Finset.mem_filter.mp hk
    apply Finset.mem_product.mpr
    refine ⟨Finset.mem_image.mpr ⟨k,hki,rfl⟩,Finset.mem_range.mpr ?_⟩
    have hkt : k ∈ A.blockPair w i ((A.right k).val/w) := Finset.mem_inter.mpr
      ⟨hki,(A.symm.mem_sourceBlock _ _ _).mpr rfl⟩
    have hlt : l ∈ A.blockPair w (i+1) ((A.right k).val/w) := Finset.mem_inter.mpr
      ⟨hli,(A.symm.mem_sourceBlock _ _ _).mpr hdiv.symm⟩
    exact A.common_offset_duplicate_loss hw (by omega) hkt hlt hmod
  have hh := Finset.card_le_card hmaps
  rw [Finset.card_image_of_injective S hf,Finset.card_product,Finset.card_range] at hh
  exact hh.trans (Nat.mul_le_mul_right d (A.targetBlocks_card_le_three hw hspan))

end WordMatching

namespace WordMatching
variable {α : Type*} {x y : List α} {q : ℕ}

theorem matchedAt_block (A : WordMatching x y q) {w i p : ℕ} {k : Fin q}
    (hp : p < w) (hk : (A.left k).val = i*w+p) :
    k ∈ A.sourceBlock w i ∧ (A.left k).val%w = p := by
  have hd : (A.left k).val/w = i :=
    Nat.div_eq_of_lt_le (by omega) (by rw [hk,Nat.add_mul,one_mul]; omega)
  refine ⟨(A.mem_sourceBlock w i k).mpr hd,?_⟩
  have hh := Nat.mod_add_div (A.left k).val w
  rw [hd,Nat.mul_comm w i] at hh
  omega

theorem unmatched_offsets_card_le (A : WordMatching x y q) {w i : ℕ}
    (hw : 0 < w) (I : Finset ℕ) (hI : I ⊆ Finset.range w) :
    (I.filter (fun p => ¬ A.matchedAt w i p)).card ≤ A.sourceLoss w i := by
  classical
  let T := (A.sourceBlock w i).image (fun k => (A.left k).val%w)
  have hT : T ⊆ Finset.range w := by
    intro p hp
    obtain ⟨k,_,rfl⟩ := Finset.mem_image.mp hp
    exact Finset.mem_range.mpr (Nat.mod_lt _ hw)
  have hTc : T.card = (A.sourceBlock w i).card :=
    Finset.card_image_of_injOn A.mod_injectiveOn
  have hs : I.filter (fun p => ¬ A.matchedAt w i p) ⊆ Finset.range w \ T := by
    intro p hp
    obtain ⟨hp,hn⟩ := Finset.mem_filter.mp hp
    refine Finset.mem_sdiff.mpr ⟨hI hp,?_⟩
    intro ht
    obtain ⟨k,hki,hkp⟩ := Finset.mem_image.mp ht
    apply hn
    refine ⟨k,?_⟩
    have hh := Nat.mod_add_div (A.left k).val w
    rw [(A.mem_sourceBlock w i k).mp hki,hkp,Nat.mul_comm w i] at hh
    omega
  have hh := Finset.card_le_card hs
  rwa [Finset.card_sdiff_of_subset hT,Finset.card_range,hTc] at hh

theorem duplicate_offsets_card_le (A : WordMatching x y q) {w i : ℕ}
    (hw : 0 < w) (I : Finset ℕ) (hI : I ⊆ Finset.range w)
    (hspan : (A.rightSpan (A.sourceBlock w i)).card ≤ 2*w) :
    (I.filter (A.duplicateAt w i)).card ≤ 3*(A.sourceLoss w i+A.sourceLoss w (i+1)) := by
  classical
  let T := (A.sourceBlock w i).filter (fun k => ∃ l ∈ A.sourceBlock w (i+1),
      (A.left k).val%w = (A.left l).val%w ∧
      (A.right k).val/w = (A.right l).val/w)
  have hs : I.filter (A.duplicateAt w i) ⊆ T.image (fun k => (A.left k).val%w) := by
    intro p hp
    obtain ⟨hp,k,l,hk,hl,hkl⟩ := Finset.mem_filter.mp hp
    have hpw := Finset.mem_range.mp (hI hp)
    obtain ⟨hki,hkp⟩ := A.matchedAt_block hpw hk
    obtain ⟨hli,hlp⟩ := A.matchedAt_block hpw hl
    exact Finset.mem_image.mpr ⟨k,Finset.mem_filter.mpr ⟨hki,l,hli,hkp.trans hlp.symm,hkl⟩,hkp⟩
  exact (Finset.card_le_card hs).trans ((Finset.card_image_le).trans
    (A.common_offset_duplicates_card hw hspan))

end WordMatching

theorem sum_card_filters_swap {α β : Type*} (S : Finset α) (T : Finset β)
    (R : α → β → Prop) [DecidableRel R] :
    ∑ a ∈ S, (T.filter (R a)).card = ∑ b ∈ T, (S.filter (fun a => R a b)).card := by
  simp only [Finset.card_eq_sum_ones,Finset.sum_filter]
  exact Finset.sum_comm

namespace WordMatching
variable {α : Type*} {x y : List α} {q : ℕ}

theorem sum_omitted_offsets_le (A : WordMatching x y q) {w L : ℕ}
    (hw : 0 < w) (I G : Finset ℕ) (hI : I ⊆ Finset.range w) (hG : G ⊆ Finset.range L) :
    (∑ p ∈ I, (L-(G.filter (fun i => A.matchedAt w i p)).card)) ≤
      I.card*(L-G.card) + ∑ i ∈ Finset.range L, A.sourceLoss w i := by
  classical
  have he (p : ℕ) : L-(G.filter (fun i => A.matchedAt w i p)).card =
      L-G.card + (G.filter (fun i => ¬ A.matchedAt w i p)).card := by
    have hh := Finset.card_filter_add_card_filter_not (s:=G) (p:=fun i => A.matchedAt w i p)
    have hg := Finset.card_le_card hG
    rw [Finset.card_range] at hg
    omega
  simp_rw [he]
  rw [Finset.sum_add_distrib]
  simp only [Finset.sum_const,smul_eq_mul]
  rw [sum_card_filters_swap]
  apply Nat.add_le_add_left
  exact (Finset.sum_le_sum (fun i _ => A.unmatched_offsets_card_le hw I hI)).trans
    (Finset.sum_le_sum_of_subset_of_nonneg hG (fun _ _ _ => Nat.zero_le _))

theorem sum_duplicate_offsets_le (A : WordMatching x y q) {w L : ℕ}
    (hw : 0 < w) (I G : Finset ℕ) (hI : I ⊆ Finset.range w) (hG : G ⊆ Finset.range L)
    (hspan : ∀ i ∈ G, (A.rightSpan (A.sourceBlock w i)).card ≤ 2*w) :
    (∑ p ∈ I, ((G.filter (fun i => i+1 < L)).filter (fun i => A.duplicateAt w i p)).card) ≤
      6 * ∑ i ∈ Finset.range L, A.sourceLoss w i := by
  classical
  let H := G.filter (fun i => i+1 < L)
  have hH : H ⊆ Finset.range L := (Finset.filter_subset _ _).trans hG
  have hsucc : H.image (fun i => i+1) ⊆ Finset.range L := by
    intro j hj
    obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hj
    exact Finset.mem_range.mpr (Finset.mem_filter.mp hi).2
  have h1 : (∑ i ∈ H, A.sourceLoss w i) ≤ ∑ i ∈ Finset.range L, A.sourceLoss w i :=
    Finset.sum_le_sum_of_subset_of_nonneg hH (fun _ _ _ => Nat.zero_le _)
  have h2 : (∑ i ∈ H, A.sourceLoss w (i+1)) ≤ ∑ i ∈ Finset.range L, A.sourceLoss w i := by
    rw [← Finset.sum_image (g:=fun i => i+1) (by intro i _ j _ h; dsimp only at h; omega)]
    exact Finset.sum_le_sum_of_subset_of_nonneg hsucc (fun _ _ _ => Nat.zero_le _)
  rw [sum_card_filters_swap]
  have hh : (∑ i ∈ H, (I.filter (fun p => A.duplicateAt w i p)).card) ≤
      ∑ i ∈ H, 3*(A.sourceLoss w i+A.sourceLoss w (i+1)) := by
    apply Finset.sum_le_sum
    intro i hi
    exact A.duplicate_offsets_card_le hw I hI (hspan i (Finset.mem_filter.mp hi).1)
  change (∑ i ∈ H, _) ≤ _
  refine hh.trans ?_
  rw [← Finset.mul_sum,Finset.sum_add_distrib]
  omega

end WordMatching

namespace WordMatching
variable {α : Type*} {x y : List α} {w q : ℕ} {c : α → Fin w → Bool}

theorem averaged_offset_recovery (A : WordMatching (encode c x) (encode c y) q)
    (hw : 0 < w) (I G : Finset ℕ) (hI : I ⊆ Finset.range w) (hG : G ⊆ Finset.range x.length)
    (hspan : ∀ i ∈ G, (A.rightSpan (A.sourceBlock w i)).card ≤ 2*w)
    (hlabels : ∀ p ∈ I, ∀ i ∈ G, ∀ k : Fin q, (A.left k).val=i*w+p →
      x[i]? = y[(A.right k).val/w]?) :
    I.card * deficit x y ≤ 2*I.card*(x.length-G.card) +
      8*(w*x.length-q) := by
  have hsum : (∑ i ∈ Finset.range x.length, A.sourceLoss w i) = w*x.length-q := by
    have hh := A.sum_sourceLoss hw (length_encode c x)
    simpa only [Fin.sum_univ_eq_sum_range] using hh
  have hh := Finset.sum_le_sum (fun p (hp : p ∈ I) => A.offset_deficit_le hw p G hG (hlabels p hp))
  rw [Finset.sum_add_distrib,← Finset.mul_sum] at hh
  simp only [Finset.sum_const,smul_eq_mul] at hh
  have h1 := A.sum_omitted_offsets_le hw I G hI hG
  have h2 := A.sum_duplicate_offsets_le hw I G hI hG hspan
  rw [hsum] at h1 h2
  rw [Nat.mul_assoc]
  omega

end WordMatching

namespace WordMatching
variable {α : Type*} {x y : List α} {w q : ℕ} {c : α → Fin w → Bool}

theorem offsetGood_subset (A : WordMatching (encode c x) (encode c y) q) (w : ℕ) (η : ℝ) :
    A.offsetGood w η ⊆ Finset.range x.length := Finset.filter_subset _ _

theorem offsetGood_span (A : WordMatching (encode c x) (encode c y) q)
    (hw : 0 < w) {η : ℝ} (hη : η ≤ 1) {i : ℕ} (hi : i ∈ A.offsetGood w η) :
    (A.rightSpan (A.sourceBlock w i)).card ≤ 2*w := by
  have hv := (Finset.mem_filter.mp hi).2.2
  have hv' : (A.spanLoss w i : ℝ) ≤ w := hv.trans (by nlinarith only [hη,(show (0 : ℝ) ≤ w from Nat.cast_nonneg w)])
  have hvn : A.spanLoss w i ≤ w := by exact_mod_cast hv'
  have h1 := A.card_le_rightSpan (A.sourceBlock w i)
  have h2 := A.sourceBlock_card_le hw i
  dsimp only [spanLoss] at hvn
  omega

theorem offsetGood_bad_cost (A : WordMatching (encode c x) (encode c y) q)
    (hw : 0 < w) (hlen : x.length=y.length) (η : ℝ) :
    η*w*(x.length-(A.offsetGood w η).card : ℕ) ≤ 2*(w*x.length-q : ℕ) := by
  classical
  let G := A.offsetGood w η
  let B := Finset.range x.length \ G
  have hG : G ⊆ Finset.range x.length := A.offsetGood_subset w η
  have hBc : B.card=x.length-G.card := by rw [Finset.card_sdiff_of_subset hG,Finset.card_range]
  have hbad (i : ℕ) (hi : i ∈ B) : η*w ≤ (A.sourceLoss w i : ℝ)+A.spanLoss w i := by
    obtain ⟨hi,hn⟩ := Finset.mem_sdiff.mp hi
    have hn' : ¬ ((A.sourceLoss w i : ℝ) ≤ η*w ∧ (A.spanLoss w i : ℝ) ≤ η*w) := by
      intro hh
      exact hn (Finset.mem_filter.mpr ⟨hi,hh⟩)
    have hU : (0 : ℝ) ≤ A.sourceLoss w i := Nat.cast_nonneg _
    have hV : (0 : ℝ) ≤ A.spanLoss w i := Nat.cast_nonneg _
    push Not at hn'
    by_cases hh : (A.sourceLoss w i : ℝ) ≤ η*w
    · have hv := hn' hh
      linarith
    · push Not at hh
      linarith
  have hsumU : (∑ i ∈ Finset.range x.length, (A.sourceLoss w i : ℝ)) = (w*x.length-q : ℕ) := by
    have hh := A.sum_sourceLoss hw (length_encode c x)
    rw [Fin.sum_univ_eq_sum_range] at hh
    exact_mod_cast hh
  have hsumV : (∑ i ∈ Finset.range x.length, (A.spanLoss w i : ℝ)) ≤ (w*x.length-q : ℕ) := by
    have hh := A.sum_spanLoss_le hw (length_encode c x) (by rw [length_encode,hlen])
    rw [Fin.sum_univ_eq_sum_range] at hh
    exact_mod_cast hh
  have hcost : η*w*(B.card : ℝ) ≤ ∑ i ∈ Finset.range x.length,
      ((A.sourceLoss w i : ℝ)+A.spanLoss w i) := calc
    _ = ∑ _i ∈ B, η*w := by simp [mul_comm]
    _ ≤ ∑ i ∈ B, ((A.sourceLoss w i : ℝ)+A.spanLoss w i) := Finset.sum_le_sum hbad
    _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg Finset.sdiff_subset
      (fun _ _ _ => add_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))
  rw [Finset.sum_add_distrib,hsumU,hBc] at hcost
  change η*w*(x.length-G.card : ℕ) ≤ _
  linarith only [hcost,hsumV]

end WordMatching

theorem offset_deficit_lower {α : Type*} {w : ℕ} (hw : 12 ≤ w) {δ η : ℝ}
    (hδ : δ ≤ 1) (hη0 : 0 ≤ η) (hη : η ≤ 1)
    (hfit : 2*η*w < δ*(w/8 : ℕ)) {c : α → Fin w → Bool} (hc : OffsetLocal δ c)
    (x y : List α) (hlen : x.length=y.length) :
    (η/(4+32*η))*w*deficit x y ≤ (deficit (encode c x) (encode c y) : ℝ) := by
  classical
  have hwp : 0 < w := by omega
  obtain ⟨A⟩ := exists_lcs_matching (encode c x) (encode c y)
  let G := A.offsetGood w η
  let I := Finset.Icc ((w+2)/3) (2*w/3)
  let E := deficit (encode c x) (encode c y)
  have hG : G ⊆ Finset.range x.length := A.offsetGood_subset w η
  have hI : I ⊆ Finset.range w := by
    intro p hp
    obtain ⟨h1,h2⟩ := Finset.mem_Icc.mp hp
    apply Finset.mem_range.mpr
    omega
  have hIp (p : ℕ) (hp : p ∈ I) : w/8 ≤ p ∧ p+w/8 ≤ w := by
    obtain ⟨h1,h2⟩ := Finset.mem_Icc.mp hp
    omega
  have hIc : w ≤ 4*I.card := by
    simp only [I,Nat.card_Icc]
    omega
  have hspan : ∀ i ∈ G, (A.rightSpan (A.sourceBlock w i)).card ≤ 2*w :=
    fun _ hi => A.offsetGood_span hwp hη hi
  have hlabels : ∀ p ∈ I, ∀ i ∈ G, ∀ k : Fin _, (A.left k).val=i*w+p →
      x[i]? = y[(A.right k).val/w]? := by
    intro p hp i hi k hk
    have hil := Finset.mem_range.mp (hG hi)
    have hjl : (A.right k).val/w < y.length := by
      apply (Nat.div_lt_iff_lt_mul hwp).mpr
      simpa only [length_encode,Nat.mul_comm] using (A.right k).isLt
    obtain ⟨hki,hkp⟩ := A.matchedAt_block (Finset.mem_range.mp (hI hp)) hk
    have hgood := (Finset.mem_filter.mp hi).2
    have hloss : (A.sourceLoss w i+A.spanLoss w i : ℕ) < δ*(w/8 : ℕ) := by
      push_cast
      linarith only [hgood.1,hgood.2,hfit]
    have hh := A.offset_interior_labels hwp hδ hc k ⟨i,hil⟩ ⟨(A.right k).val/w,hjl⟩
      ((A.mem_sourceBlock w i k).mp hki) rfl (by rw [hkp]; exact (hIp p hp).1)
      (by rw [hkp]; exact (hIp p hp).2) hloss
    simpa only [List.getElem?_eq_getElem hil,List.getElem?_eq_getElem hjl,
      List.get_eq_getElem,Option.some.injEq] using hh
  have hav := A.averaged_offset_recovery hwp I G hI hG hspan hlabels
  have he : w*x.length-lcs (encode c x) (encode c y) = E := by simp only [E,deficit,length_encode]
  rw [he] at hav
  have havr : (I.card : ℝ)*deficit x y ≤ 2*(I.card : ℝ)*(x.length-G.card : ℕ)+8*E := by exact_mod_cast hav
  have hbad := A.offsetGood_bad_cost hwp hlen η
  rw [he] at hbad
  have hbad' : η*w*(x.length-G.card : ℕ) ≤ 2*E := hbad
  have hicr : (w : ℝ) ≤ 4*I.card := by exact_mod_cast hIc
  have hip : (0 : ℝ) < I.card := by exact_mod_cast (show 0 < I.card by omega)
  have hmain : η*w*(deficit x y : ℝ) ≤ (4+32*η)*E := by
    apply (mul_le_mul_iff_right₀ hip).mp
    calc
      _ = η*w*((I.card : ℝ)*deficit x y) := by ring
      _ ≤ η*w*(2*(I.card : ℝ)*(x.length-G.card : ℕ)+8*E) :=
        mul_le_mul_of_nonneg_left havr (mul_nonneg hη0 (Nat.cast_nonneg w))
      _ = 2*(I.card : ℝ)*(η*w*(x.length-G.card : ℕ))+8*η*w*E := by ring
      _ ≤ 2*(I.card : ℝ)*(2*E)+8*η*(4*I.card)*E := add_le_add
        (mul_le_mul_of_nonneg_left hbad' (by positivity))
        (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hicr (by positivity)) (Nat.cast_nonneg E))
      _ = (I.card : ℝ)*((4+32*η)*E) := by ring
  have hden : 0 < 4+32*η := by linarith
  calc
    _ = (η*w*(deficit x y : ℝ))/(4+32*η) := by ring
    _ ≤ E := (div_le_iff₀ hden).mpr (by simpa only [mul_comm] using hmain)

end FiniteCircle

end OAI

-- ---- platform node ----
open OAI OAI.FiniteCircle
open scoped BigOperators List
open scoped ComplexConjugate
open RCLike Module


theorem solution : type_of% @_root_.OAI.FiniteCircle.offset_deficit_lower := @_root_.OAI.FiniteCircle.offset_deficit_lower
