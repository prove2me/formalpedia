-- Prove2me | solution 1 for OAI.FiniteCircle.anchor_deficit_lower
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T16:24:49.852765+00:00
-- url     : https://prove2.me/submissions/90033a80-65cb-49f7-80d8-0d1c6965983f

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/FiniteCircle/AnchorRecovery.lean:L254-L297
-- (upload_full_project.md Phase 4): solution for node OAI.FiniteCircle.anchor_deficit_lower. The node keeps its source
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
import Theorems.Thm_OAI_FiniteCircle_WordMatching_block_after_card_le
import Theorems.Thm_OAI_FiniteCircle_WordMatching_block_before_card_le
import Theorems.Thm_OAI_FiniteCircle_WordMatching_le_lcs
import Theorems.Thm_OAI_FiniteCircle_WordMatching_localIndices_span
import Theorems.Thm_OAI_FiniteCircle_WordMatching_sourceBlock_card_le
import Theorems.Thm_OAI_FiniteCircle_WordMatching_targetBlocks_card_le_three
import Theorems.Thm_OAI_FiniteCircle_get_encode_block

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

theorem rightSpan_matched_iff (A : WordMatching x y q) (S : Finset (Fin q))
    (hS : ∀ i ∈ S, ∀ k ∈ S, ∀ j, i ≤ j → j ≤ k → j ∈ S) (j : Fin q) :
    A.right j ∈ A.rightSpan S ↔ j ∈ S := by
  simp only [rightSpan, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨i, hi, k, hk, hij, hjk⟩
    exact hS i hi k hk j (A.right.le_iff_le.mp hij) (A.right.le_iff_le.mp hjk)
  · intro hj
    exact ⟨j, hj, j, hj, le_rfl, le_rfl⟩

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

theorem sourceBlock_convex (A : WordMatching x y q) (w i : ℕ) :
    ∀ k ∈ A.sourceBlock w i, ∀ l ∈ A.sourceBlock w i, ∀ j, k ≤ j → j ≤ l →
      j ∈ A.sourceBlock w i := by
  intro k hk l hl j hkj hjl
  rw [mem_sourceBlock] at *
  have h1 := Nat.div_le_div_right (c := w) (show (A.left k).val ≤ (A.left j).val from A.left.monotone hkj)
  have h2 := Nat.div_le_div_right (c := w) (show (A.left j).val ≤ (A.left l).val from A.left.monotone hjl)
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

theorem rightSpan_mono (A : WordMatching x y q) {S T : Finset (Fin q)} (h : S ⊆ T) :
    A.rightSpan S ⊆ A.rightSpan T := by
  intro j hj
  obtain ⟨_, i, hi, k, hk, hij, hjk⟩ := Finset.mem_filter.mp hj
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, i, h hi, k, h hk, hij, hjk⟩

theorem card_span_unmatched (A : WordMatching x y q) {S : Finset (Fin q)}
    (hS : ConvexIndices S) :
    (A.rightSpan S \ (Finset.univ.image A.right)).card = (A.rightSpan S).card - S.card := by
  have he : A.rightSpan S \ (Finset.univ.image A.right) = A.rightSpan S \ (S.image A.right) := by
    ext j
    simp only [Finset.mem_sdiff, Finset.mem_image, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨hj, hn⟩
      exact ⟨hj, fun ⟨k, _, hk⟩ => hn ⟨k, hk⟩⟩
    · rintro ⟨hj, hn⟩
      refine ⟨hj, ?_⟩
      rintro ⟨k, rfl⟩
      exact hn ⟨k, (A.rightSpan_matched_iff S hS k).mp hj, rfl⟩
  have hs : S.image A.right ⊆ A.rightSpan S := by
    intro j hj
    obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hj
    exact (A.rightSpan_matched_iff S hS k).mpr hk
  rw [he, Finset.card_sdiff_of_subset hs, Finset.card_image_of_injective S A.right.injective]

theorem span_holes_mono (A : WordMatching x y q) {S T : Finset (Fin q)}
    (hS : ConvexIndices S) (hT : ConvexIndices T) (h : S ⊆ T) :
    (A.rightSpan S).card - S.card ≤ (A.rightSpan T).card - T.card := by
  rw [← A.card_span_unmatched hS, ← A.card_span_unmatched hT]
  exact Finset.card_le_card (Finset.sdiff_subset_sdiff (A.rightSpan_mono h) le_rfl)

theorem leftSpan_sourceBlock_card_le (A : WordMatching x y q) {w : ℕ} (hw : 0 < w) (i : ℕ) :
    (A.symm.rightSpan (A.sourceBlock w i)).card ≤ w := by
  let f : Fin x.length → Fin w := fun j => ⟨j.val % w, Nat.mod_lt _ hw⟩
  have hquot (j : Fin x.length) (hj : j ∈ A.symm.rightSpan (A.sourceBlock w i)) : j.val/w = i := by
    obtain ⟨_, k, hk, l, hl, hkj, hjl⟩ := Finset.mem_filter.mp hj
    have hk := (A.mem_sourceBlock w i k).mp hk
    have hl := (A.mem_sourceBlock w i l).mp hl
    have h1 := Nat.div_le_div_right (c := w) (show (A.left k).val ≤ j.val from hkj)
    have h2 := Nat.div_le_div_right (c := w) (show j.val ≤ (A.left l).val from hjl)
    omega
  have hinj : Set.InjOn f (↑(A.symm.rightSpan (A.sourceBlock w i)) : Set (Fin x.length)) := by
    intro j hj k hk he
    have hj := hquot j hj
    have hk := hquot k hk
    have hf : j.val % w = k.val % w := congrArg Fin.val he
    have h1 := Nat.mod_add_div j.val w
    have h2 := Nat.mod_add_div k.val w
    rw [hj, hf] at h1
    rw [hk] at h2
    apply Fin.ext
    omega
  simpa using Finset.card_le_card_of_injOn f (fun _ _ => Finset.mem_univ _) hinj

theorem left_span_holes_le_sourceLoss (A : WordMatching x y q) {w : ℕ} (hw : 0 < w)
    {i : ℕ} {S : Finset (Fin q)} (hS : ConvexIndices S) (h : S ⊆ A.sourceBlock w i) :
    (A.symm.rightSpan S).card - S.card ≤ A.sourceLoss w i := by
  exact (A.symm.span_holes_mono hS (A.sourceBlock_convex w i) h).trans
    (Nat.sub_le_sub_right (A.leftSpan_sourceBlock_card_le hw i) _)

theorem right_span_holes_le_spanLoss (A : WordMatching x y q) {w i : ℕ}
    {S : Finset (Fin q)} (hS : ConvexIndices S) (h : S ⊆ A.sourceBlock w i) :
    (A.rightSpan S).card - S.card ≤ A.spanLoss w i :=
  A.span_holes_mono hS (A.sourceBlock_convex w i) h

end WordMatching

end FiniteCircle

end OAI

-- ---- from OAI.Combinatorics.FiniteCircle.BlockMatching ----
namespace OAI

namespace FiniteCircle

open scoped BigOperators List
open scoped ComplexConjugate
open RCLike Module

theorem get_encode {α : Type*} {w : ℕ} (hw : 0 < w) (c : α → Fin w → Bool)
    (x : List α) (k : Fin (encode c x).length) :
    (encode c x).get k = c (x.get ⟨k.val/w, by
      apply (Nat.div_lt_iff_lt_mul hw).mpr
      simpa only [length_encode, Nat.mul_comm] using k.isLt⟩)
      ⟨k.val%w, Nat.mod_lt _ hw⟩ := by
  have h := get_encode_block c x ⟨k.val/w, by
    apply (Nat.div_lt_iff_lt_mul hw).mpr
    simpa only [length_encode, Nat.mul_comm] using k.isLt⟩ ⟨k.val%w, Nat.mod_lt _ hw⟩
  convert h using 1
  congr 1
  apply Fin.ext
  simpa only [Nat.mul_comm] using (Nat.div_add_mod k.val w).symm

namespace WordMatching
variable {α : Type*} {x y : List α} {q : ℕ}

theorem mod_strictMono_on_block (A : WordMatching x y q) {w i : ℕ}
    {k l : Fin q} (hk : k ∈ A.sourceBlock w i) (hl : l ∈ A.sourceBlock w i)
    (hkl : k < l) : (A.left k).val % w < (A.left l).val % w := by
  have hm : (A.left k).val < (A.left l).val := A.left.strictMono hkl
  have h1 := Nat.mod_add_div (A.left k).val w
  have h2 := Nat.mod_add_div (A.left l).val w
  rw [(A.mem_sourceBlock w i k).mp hk] at h1
  rw [(A.mem_sourceBlock w i l).mp hl] at h2
  omega

theorem localIndices_sorted (A : WordMatching x y q) {w i : ℕ} (hw : 0 < w)
    {S : Finset (Fin q)} (hS : S ⊆ A.sourceBlock w i) :
    (A.localIndices hw S).Pairwise (fun i j => i.val < j.val) := by
  apply List.pairwise_ofFn.mpr
  intro k l hkl
  exact A.mod_strictMono_on_block (hS (S.orderEmbOfFin_mem rfl k))
    (hS (S.orderEmbOfFin_mem rfl l)) ((S.orderEmbOfFin rfl).strictMono hkl)

theorem blockPair_convex (A : WordMatching x y q) (w i j : ℕ) :
    ConvexIndices (A.blockPair w i j) := by
  intro k hk l hl v hkv hvl
  exact Finset.mem_inter.mpr
    ⟨A.sourceBlock_convex w i k (Finset.mem_inter.mp hk).1 l (Finset.mem_inter.mp hl).1 v hkv hvl,
     A.symm.sourceBlock_convex w j k (Finset.mem_inter.mp hk).2 l (Finset.mem_inter.mp hl).2 v hkv hvl⟩

theorem sum_blockPair_card (A : WordMatching x y q) (w i : ℕ) :
    ∑ j ∈ A.targetBlocks w (A.sourceBlock w i), (A.blockPair w i j).card =
      (A.sourceBlock w i).card := by
  have hpair (j : ℕ) : A.blockPair w i j = (A.sourceBlock w i).filter (fun k => (A.right k).val / w = j) := by
    ext k
    simp [blockPair, mem_sourceBlock, symm]
  simp_rw [hpair]
  rw [Finset.sum_card_fiberwise_eq_card_filter]
  congr 1
  apply Finset.filter_true_of_mem
  intro k hk
  exact Finset.mem_image_of_mem _ hk

theorem exists_large_blockPair (A : WordMatching x y q) {w i : ℕ} (hw : 0 < w)
    (hspan : (A.rightSpan (A.sourceBlock w i)).card ≤ 2*w)
    (hcard : 3*w < 4*(A.sourceBlock w i).card) :
    ∃ j ∈ A.targetBlocks w (A.sourceBlock w i), w ≤ 4*(A.blockPair w i j).card := by
  by_contra hh
  push Not at hh
  have hs := Finset.sum_le_sum (fun j hj => (hh j hj).le)
  rw [← Finset.mul_sum, A.sum_blockPair_card, Finset.sum_const, smul_eq_mul] at hs
  have ht := A.targetBlocks_card_le_three hw hspan
  have hmul := Nat.mul_le_mul_right w ht
  omega

end WordMatching

end FiniteCircle

end OAI

-- ---- from OAI.Combinatorics.FiniteCircle.AnchorRecovery ----
namespace OAI

namespace FiniteCircle

open scoped BigOperators List
open scoped ComplexConjugate
open RCLike Module

theorem zip_ofFn {α β : Type*} {n : ℕ} (f : Fin n → α) (g : Fin n → β) :
    (List.ofFn f).zip (List.ofFn g) = List.ofFn (fun i => (f i, g i)) := by
  apply List.ext_getElem
  · simp
  · intro i hi hj
    simp only [List.getElem_zip, List.getElem_ofFn]

namespace WordMatching
variable {α : Type*} {x y : List α} {w q : ℕ} {c : α → Fin w → Bool}

theorem localIndices_letters (hw : 0 < w) (A : WordMatching (encode c x) (encode c y) q)
    {i : Fin x.length} {j : Fin y.length} {S : Finset (Fin q)}
    (hS : S ⊆ A.blockPair w i j) :
    ∀ z ∈ (A.localIndices hw S).zip (A.symm.localIndices hw S),
      c (x.get i) z.1 = c (y.get j) z.2 := by
  intro z hz
  rw [localIndices, localIndices, zip_ofFn] at hz
  obtain ⟨k, rfl⟩ := List.mem_ofFn.mp hz
  let p := S.orderEmbOfFin rfl k
  have hp := hS (S.orderEmbOfFin_mem rfl k)
  obtain ⟨hl, hr⟩ := Finset.mem_inter.mp hp
  have hi := (A.mem_sourceBlock w i p).mp hl
  have hj := (A.symm.mem_sourceBlock w j p).mp hr
  have he := A.letters p
  rw [get_encode hw, get_encode hw] at he
  convert he using 1 <;> congr 2
  · apply Fin.ext
    exact hi.symm
  · apply Fin.ext
    exact hj.symm

theorem anchor_on_blockPair (hw : 0 < w) {ε : ℝ} (hlocal : AnchorLocal ε c)
    (A : WordMatching (encode c x) (encode c y) q)
    (i : Fin x.length) (j : Fin y.length)
    (hcard : w ≤ 4*(A.blockPair w i j).card)
    (hU : (A.sourceLoss w i : ℝ) ≤ ε*w)
    (hV : (A.spanLoss w i : ℝ) ≤ ε*w) :
    x.get i = y.get j ∧ ∃ k ∈ A.blockPair w i j, (A.left k).val%w = (A.right k).val%w := by
  let S := A.blockPair w i j
  have hS : S ⊆ A.sourceBlock w i := Finset.inter_subset_left
  have hT : S ⊆ A.symm.sourceBlock w j := Finset.inter_subset_right
  have hconv : ConvexIndices S := A.blockPair_convex w i j
  have hbound : (w : ℝ)/4 ≤ (A.localIndices hw S).length := by
    rw [localIndices_length]
    have hc : (w : ℝ) ≤ 4*(S.card : ℝ) := by exact_mod_cast hcard
    linarith
  have hleft : ((indexSpan (A.localIndices hw S) - (A.localIndices hw S).length : ℕ) : ℝ) ≤ ε*w := by
    rw [A.localIndices_span hw hS, localIndices_length]
    have hh : (((A.symm.rightSpan S).card - S.card : ℕ) : ℝ) ≤ A.sourceLoss w i := by
      exact_mod_cast A.left_span_holes_le_sourceLoss hw hconv hS
    exact hh.trans hU
  have hright : ((indexSpan (A.symm.localIndices hw S) - (A.symm.localIndices hw S).length : ℕ) : ℝ) ≤ ε*w := by
    rw [A.symm.localIndices_span hw hT, localIndices_length]
    have hh : (((A.rightSpan S).card - S.card : ℕ) : ℝ) ≤ A.spanLoss w i := by
      exact_mod_cast A.right_span_holes_le_spanLoss hconv hS
    exact hh.trans hV
  obtain ⟨hlabels, k, hk⟩ := hlocal (x.get i) (y.get j) _ _
    (A.localIndices_sorted hw hS) (A.symm.localIndices_sorted hw hT) (by simp)
    hbound hleft hright (A.localIndices_letters hw (by rfl))
  refine ⟨hlabels, ?_⟩
  rw [localIndices, localIndices, zip_ofFn] at hk
  obtain ⟨p, hp⟩ := List.mem_ofFn.mp hk
  refine ⟨S.orderEmbOfFin rfl p, S.orderEmbOfFin_mem rfl p, ?_⟩
  have hl := congrArg (fun z : Fin w × Fin w => z.1.val) hp
  have hr := congrArg (fun z : Fin w × Fin w => z.2.val) hp
  exact hl.trans hr.symm

theorem good_block_anchor (hw : 0 < w) {ε : ℝ} (hε : ε ≤ 1/10)
    (hlocal : AnchorLocal ε c) (A : WordMatching (encode c x) (encode c y) q)
    (i : Fin x.length) (hU : (A.sourceLoss w i : ℝ) ≤ ε*w)
    (hV : (A.spanLoss w i : ℝ) ≤ ε*w) :
    ∃ j : Fin y.length, x.get i = y.get j ∧
      ∃ k ∈ A.blockPair w i j, (A.left k).val%w = (A.right k).val%w := by
  have hc := A.sourceBlock_card_le hw i
  have hs := A.card_le_rightSpan (A.sourceBlock w i)
  have hcardU : A.sourceLoss w i + (A.sourceBlock w i).card = w := Nat.sub_add_cancel hc
  have hcardV : A.spanLoss w i + (A.sourceBlock w i).card = (A.rightSpan (A.sourceBlock w i)).card :=
    Nat.sub_add_cancel hs
  have hU' : (A.sourceLoss w i : ℝ) ≤ (w : ℝ)/10 := by nlinarith
  have hV' : (A.spanLoss w i : ℝ) ≤ (w : ℝ)/10 := by nlinarith
  have hsmall : (A.rightSpan (A.sourceBlock w i)).card ≤ 2*w := by
    apply Nat.cast_le (α := ℝ) |>.mp
    have h1 : (A.spanLoss w i : ℝ) + (A.sourceBlock w i).card = (A.rightSpan (A.sourceBlock w i)).card := by exact_mod_cast hcardV
    have h2 : ((A.sourceBlock w i).card : ℝ) ≤ w := by exact_mod_cast hc
    push_cast
    linarith
  have hlarge : 3*w < 4*(A.sourceBlock w i).card := by
    apply Nat.cast_lt (α := ℝ) |>.mp
    have h1 : (A.sourceLoss w i : ℝ) + (A.sourceBlock w i).card = w := by exact_mod_cast hcardU
    have hp : (0 : ℝ) < w := by exact_mod_cast hw
    push_cast
    linarith
  obtain ⟨j, hj, hcard⟩ := A.exists_large_blockPair hw hsmall hlarge
  have hjlt : j < y.length := by
    obtain ⟨k, _, rfl⟩ := Finset.mem_image.mp hj
    apply (Nat.div_lt_iff_lt_mul hw).mpr
    simpa only [length_encode, Nat.mul_comm] using (A.right k).isLt
  exact ⟨⟨j, hjlt⟩, A.anchor_on_blockPair hw hlocal i ⟨j, hjlt⟩ hcard hU hV⟩

end WordMatching

namespace WordMatching
variable {α : Type*} {x y : List α} {q : ℕ}

theorem two_anchors_source_loss (A : WordMatching x y q) {w i j t : ℕ} (hw : 0 < w)
    (hij : i < j) {k l : Fin q} (hk : k ∈ A.blockPair w i t) (hl : l ∈ A.blockPair w j t)
    (hkmod : (A.left k).val%w = (A.right k).val%w)
    (hlmod : (A.left l).val%w = (A.right l).val%w) :
    w ≤ A.sourceLoss w i + A.sourceLoss w j := by
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
  rw [hkt', ← hkmod] at hrk
  rw [hlt', ← hlmod] at hrl
  have hklt := Nat.mod_lt (A.left k).val hw
  have hllt := Nat.mod_lt (A.left l).val hw
  have hkl : (A.right k).val ≤ (A.right l).val := A.right.monotone (A.sourceBlock_order hij hki hlj).le
  omega

end WordMatching

namespace WordMatching
variable {α : Type*} {x y : List α} {w q : ℕ} {c : α → Fin w → Bool}

theorem anchors_strict_order (hw : 0 < w) {ε : ℝ} (hε : ε ≤ 1/10)
    (A : WordMatching (encode c x) (encode c y) q)
    {i j : Fin x.length} {s t : Fin y.length} (hij : i < j)
    {k l : Fin q} (hk : k ∈ A.blockPair w i s) (hl : l ∈ A.blockPair w j t)
    (hkmod : (A.left k).val%w = (A.right k).val%w)
    (hlmod : (A.left l).val%w = (A.right l).val%w)
    (hUi : (A.sourceLoss w i : ℝ) ≤ ε*w) (hUj : (A.sourceLoss w j : ℝ) ≤ ε*w) : s < t := by
  have hkl : k < l := A.sourceBlock_order hij (Finset.mem_inter.mp hk).1 (Finset.mem_inter.mp hl).1
  have hks : (A.right k).val/w = s.val := (A.symm.mem_sourceBlock w s k).mp (Finset.mem_inter.mp hk).2
  have hlt : (A.right l).val/w = t.val := (A.symm.mem_sourceBlock w t l).mp (Finset.mem_inter.mp hl).2
  have hquot := Nat.div_le_div_right (c := w) (show (A.right k).val ≤ (A.right l).val from (A.right.strictMono hkl).le)
  rw [hks, hlt] at hquot
  have hne : s ≠ t := by
    intro he
    have hl' : l ∈ A.blockPair w j s := by simpa only [he] using hl
    have hc := A.two_anchors_source_loss hw hij hk hl' hkmod hlmod
    have hc' : (w : ℝ) ≤ A.sourceLoss w i + A.sourceLoss w j := by exact_mod_cast hc
    have hp : (0 : ℝ) < w := by exact_mod_cast hw
    nlinarith
  exact lt_of_le_of_ne hquot hne

theorem good_blocks_le_lcs (hw : 0 < w) {ε : ℝ} (hε : ε ≤ 1/10)
    (hlocal : AnchorLocal ε c) (A : WordMatching (encode c x) (encode c y) q) :
    (Finset.univ.filter (fun i : Fin x.length =>
      (A.sourceLoss w i : ℝ) ≤ ε*w ∧ (A.spanLoss w i : ℝ) ≤ ε*w)).card ≤ lcs x y := by
  classical
  let G := Finset.univ.filter (fun i : Fin x.length =>
      (A.sourceLoss w i : ℝ) ≤ ε*w ∧ (A.spanLoss w i : ℝ) ≤ ε*w)
  let e := G.orderEmbOfFin rfl
  have hgood (k : Fin G.card) : (A.sourceLoss w (e k) : ℝ) ≤ ε*w ∧ (A.spanLoss w (e k) : ℝ) ≤ ε*w :=
    (Finset.mem_filter.mp (G.orderEmbOfFin_mem rfl k)).2
  have hex (k : Fin G.card) : ∃ j : Fin y.length, x.get (e k) = y.get j ∧
      ∃ p ∈ A.blockPair w (e k) j, (A.left p).val%w = (A.right p).val%w :=
    A.good_block_anchor hw hε hlocal (e k) (hgood k).1 (hgood k).2
  choose f hlabels p hp hmod using hex
  have hmono : StrictMono f := by
    intro k l hkl
    exact A.anchors_strict_order hw hε (e.strictMono hkl) (hp k) (hp l)
      (hmod k) (hmod l) (hgood k).1 (hgood l).1
  let B : WordMatching x y G.card :=
    { left := e
      right := OrderEmbedding.ofStrictMono f hmono
      letters := hlabels }
  exact B.le_lcs

end WordMatching

theorem anchor_deficit_lower {α : Type*} {w : ℕ} (hw : 0 < w) {ε : ℝ}
    (hε0 : 0 ≤ ε) (hε : ε ≤ 1/10) {c : α → Fin w → Bool} (hlocal : AnchorLocal ε c)
    (x y : List α) (hlen : x.length = y.length) :
    (ε/2) * w * deficit x y ≤ (deficit (encode c x) (encode c y) : ℝ) := by
  classical
  obtain ⟨A⟩ := exists_lcs_matching (encode c x) (encode c y)
  let U : Fin x.length → ℝ := fun i => A.sourceLoss w i
  let V : Fin x.length → ℝ := fun i => A.spanLoss w i
  let G := Finset.univ.filter (fun i : Fin x.length => U i ≤ ε*w ∧ V i ≤ ε*w)
  let B := Gᶜ
  have hG : G.card ≤ lcs x y := A.good_blocks_le_lcs hw hε hlocal
  have hB : deficit x y ≤ B.card := by
    have hc := Finset.card_compl G
    simp only [Fintype.card_fin] at hc
    dsimp only [B, deficit]
    omega
  have hbad (i : Fin x.length) (hi : i ∈ B) : ε*w ≤ U i + V i := by
    have hn : ¬(U i ≤ ε*w ∧ V i ≤ ε*w) := by
      simpa only [B, G, Finset.mem_compl, Finset.mem_filter, Finset.mem_univ, true_and] using hi
    have hu : 0 ≤ U i := Nat.cast_nonneg _
    have hv : 0 ≤ V i := Nat.cast_nonneg _
    push Not at hn
    by_cases hh : U i ≤ ε*w
    · have := hn hh
      linarith
    · push Not at hh
      linarith
  have hsumU : ∑ i, U i = (deficit (encode c x) (encode c y) : ℝ) := by
    have h := A.sum_sourceLoss hw (length_encode c x)
    simp only [U, deficit, length_encode]
    exact_mod_cast h
  have hsumV : ∑ i, V i ≤ (deficit (encode c x) (encode c y) : ℝ) := by
    have h := A.sum_spanLoss_le hw (length_encode c x) (by rw [length_encode, hlen])
    simp only [V, deficit, length_encode]
    exact_mod_cast h
  have hcost : ε*w*(B.card : ℝ) ≤ ∑ i, (U i + V i) := calc
    _ = ∑ _i ∈ B, ε*w := by simp [mul_comm]
    _ ≤ ∑ i ∈ B, (U i + V i) := Finset.sum_le_sum hbad
    _ ≤ ∑ i, (U i + V i) := Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
      (fun i _ _ => add_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))
  rw [Finset.sum_add_distrib, hsumU] at hcost
  have hmul := mul_le_mul_of_nonneg_left (show (deficit x y : ℝ) ≤ B.card by exact_mod_cast hB)
    (mul_nonneg hε0 (Nat.cast_nonneg w))
  nlinarith

end FiniteCircle

end OAI

-- ---- platform node ----
open OAI OAI.FiniteCircle
open scoped BigOperators List
open scoped ComplexConjugate
open RCLike Module


theorem solution : type_of% @_root_.OAI.FiniteCircle.anchor_deficit_lower := @_root_.OAI.FiniteCircle.anchor_deficit_lower
