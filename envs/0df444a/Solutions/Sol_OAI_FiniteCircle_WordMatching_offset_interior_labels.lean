-- Prove2me | solution 1 for OAI.FiniteCircle.WordMatching.offset_interior_labels
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T16:26:44.185288+00:00
-- url     : https://prove2.me/submissions/caf3d2ec-921e-4a2a-aae3-d7ec4be4c02b

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/FiniteCircle/WindowMatching.lean:L150-L254
-- (upload_full_project.md Phase 4): solution for node OAI.FiniteCircle.WordMatching.offset_interior_labels. The node keeps its source
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
import Theorems.Thm_OAI_FiniteCircle_WordMatching_le_lcs
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

end WordMatching

namespace WordMatching
variable {α : Type*} {x y : List α} {q : ℕ}

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

theorem right_span_holes_le_spanLoss (A : WordMatching x y q) {w i : ℕ}
    {S : Finset (Fin q)} (hS : ConvexIndices S) (h : S ⊆ A.sourceBlock w i) :
    (A.rightSpan S).card - S.card ≤ A.spanLoss w i :=
  A.span_holes_mono hS (A.sourceBlock_convex w i) h

end WordMatching

end FiniteCircle

end OAI

-- ---- from OAI.Combinatorics.FiniteCircle.WindowMatching ----
namespace OAI

namespace FiniteCircle

open scoped BigOperators List
open scoped ComplexConjugate
open RCLike Module

theorem matching_segments_card {α : Type*} {x y : List α} {q : ℕ}
    (A : WordMatching x y q) (a b n : ℕ) (ha : a+n ≤ x.length) (hb : b+n ≤ y.length) :
    (Finset.univ.filter (fun k : Fin q =>
      a ≤ (A.left k).val ∧ (A.left k).val < a+n ∧
      b ≤ (A.right k).val ∧ (A.right k).val < b+n)).card  ≤
      lcs (segment x a n) (segment y b n) := by
  classical
  let S := Finset.univ.filter (fun k : Fin q =>
    a ≤ (A.left k).val ∧ (A.left k).val < a+n ∧
    b ≤ (A.right k).val ∧ (A.right k).val < b+n)
  let e := S.orderEmbOfFin rfl
  have hmem (k : Fin S.card) : a ≤ (A.left (e k)).val ∧ (A.left (e k)).val < a+n ∧
      b ≤ (A.right (e k)).val ∧ (A.right (e k)).val < b+n :=
    (Finset.mem_filter.mp (S.orderEmbOfFin_mem rfl k)).2
  let f : Fin S.card → Fin (segment x a n).length := fun k =>
    ⟨(A.left (e k)).val-a, by rw [length_segment ha]; have := hmem k; omega⟩
  let g : Fin S.card → Fin (segment y b n).length := fun k =>
    ⟨(A.right (e k)).val-b, by rw [length_segment hb]; have := hmem k; omega⟩
  have hf : StrictMono f := by
    intro i j hij
    have hh := A.left.strictMono (e.strictMono hij)
    have hi := hmem i
    change (A.left (e i)).val-a  <  (A.left (e j)).val-a
    omega
  have hg : StrictMono g := by
    intro i j hij
    have hh := A.right.strictMono (e.strictMono hij)
    have hi := hmem i
    change (A.right (e i)).val-b  <  (A.right (e j)).val-b
    omega
  apply WordMatching.le_lcs (q:=S.card)
  refine ⟨OrderEmbedding.ofStrictMono f hf,OrderEmbedding.ofStrictMono g hg,?_⟩
  intro k
  have hka : a+((A.left (e k)).val-a)=(A.left (e k)).val := by have := hmem k; omega
  have hkb : b+((A.right (e k)).val-b)=(A.right (e k)).val := by have := hmem k; omega
  change (segment x a n).get (f k) = (segment y b n).get (g k)
  simpa only [f,g,List.get_eq_getElem, segment,
    List.getElem_take,List.getElem_drop,hka,hkb] using A.letters (e k)

theorem WordMatching.interval_card_loss {α : Type*} {x y : List α} {q w i a t : ℕ}
    (A : WordMatching x y q) (hw : 0 < w) (ha : i*w ≤ a) (ht : a+t ≤ (i+1)*w) :
    t  ≤  (Finset.univ.filter (fun k : Fin q =>  a ≤ (A.left k).val ∧ (A.left k).val < a+t)).card +
      A.sourceLoss w i := by
  classical
  let S := A.sourceBlock w i
  let B := Finset.Ico (i*w) ((i+1)*w)
  let T := S.image (fun k =>  (A.left k).val)
  let K := Finset.univ.filter (fun k : Fin q =>  a ≤ (A.left k).val ∧ (A.left k).val < a+t)
  let I := Finset.Ico a (a+t)
  have hinj : Function.Injective (fun k : Fin q =>  (A.left k).val) :=
    fun k l h =>  A.left.injective (Fin.ext h)
  have hT : T⊆B := by
    intro j hj
    obtain ⟨k,hk,rfl⟩ := Finset.mem_image.mp hj
    have hd := (A.mem_sourceBlock w i k).mp hk
    have hl := Nat.mod_lt (A.left k).val hw
    have he := Nat.mod_add_div (A.left k).val w
    rw [hd, Nat.mul_comm w i] at he
    apply Finset.mem_Ico.mpr
    constructor
    · omega
    · rw [Nat.add_mul, one_mul]; omega
  have hBcard : B.card=w := by simp [B,Nat.add_mul]
  have hTcard : T.card=S.card := Finset.card_image_of_injective S hinj
  have hI : I ⊆ B := by
    intro j hj
    obtain ⟨h1,h2⟩ := Finset.mem_Ico.mp hj
    exact Finset.mem_Ico.mpr ⟨ha.trans h1,h2.trans_le ht⟩
  have hsub : I ⊆ K.image (fun k =>  (A.left k).val) ∪ (B\T) := by
    intro j hj
    by_cases hjT : j∈T
    · obtain ⟨k,_,rfl⟩ := Finset.mem_image.mp hjT
      exact Finset.mem_union_left _ (Finset.mem_image.mpr
        ⟨k,Finset.mem_filter.mpr ⟨Finset.mem_univ _,Finset.mem_Ico.mp hj⟩,rfl⟩)
    · exact Finset.mem_union_right _ (Finset.mem_sdiff.mpr ⟨hI hj,hjT⟩)
  have hc := (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)
  rw [Finset.card_image_of_injective K hinj,Finset.card_sdiff_of_subset hT,hBcard,hTcard] at hc
  simpa only [I,Nat.card_Ico,Nat.add_sub_cancel_left,WordMatching.sourceLoss,S,K] using hc

namespace WordMatching
variable {α : Type*} {x y : List α} {q : ℕ}

theorem gap_right_le {w i : ℕ} (A : WordMatching x y q)
    {k l : Fin q} (hk : k∈A.sourceBlock w i) (hl : l∈A.sourceBlock w i) (hkl : k ≤ l) :
    (A.right l).val + (A.left k).val  ≤
      (A.right k).val + (A.left l).val + A.spanLoss w i := by
  let S := Finset.Icc k l
  have hS : S.Nonempty := ⟨k,Finset.mem_Icc.mpr ⟨le_rfl,hkl⟩⟩
  have hconv : ConvexIndices S := by
    intro a ha b hb c hac hcb
    exact Finset.mem_Icc.mpr ⟨(Finset.mem_Icc.mp ha).1.trans hac,hcb.trans (Finset.mem_Icc.mp hb).2⟩
  have hsub : S ⊆ A.sourceBlock w i := by
    intro j hj
    exact A.sourceBlock_convex w i k hk l hl j (Finset.mem_Icc.mp hj).1 (Finset.mem_Icc.mp hj).2
  have he : A.rightSpan S=Finset.Icc (A.right k) (A.right l) := by
    ext j
    simp only [rightSpan,Finset.mem_filter,Finset.mem_univ,true_and,S,Finset.mem_Icc]
    constructor
    · rintro ⟨a,ha,b,hb,haj,hjb⟩
      exact ⟨(A.right.monotone ha.1).trans haj,hjb.trans (A.right.monotone hb.2)⟩
    · intro hj
      exact ⟨k,⟨le_rfl,hkl⟩,l,⟨hkl,le_rfl⟩,hj.1,hj.2⟩
  have hv := A.right_span_holes_le_spanLoss hconv hsub
  rw [he,Fin.card_Icc,Fin.card_Icc] at hv
  have hleft := A.symm.card_le_rightSpan S
  have heleft : A.symm.rightSpan S=Finset.Icc (A.left k) (A.left l) := by
    ext j
    simp only [rightSpan, Finset.mem_filter, Finset.mem_univ, true_and, S, Finset.mem_Icc]
    change (∃ a, (k ≤ a ∧ a ≤ l) ∧ ∃ b, (k ≤ b ∧ b ≤ l) ∧ A.left a ≤ j ∧ j ≤ A.left b) ↔ _
    constructor
    · rintro ⟨a,ha,b,hb,haj,hjb⟩
      exact ⟨(A.left.monotone ha.1).trans haj,hjb.trans (A.left.monotone hb.2)⟩
    · intro hj
      exact ⟨k,⟨le_rfl,hkl⟩,l,⟨hkl,le_rfl⟩,hj.1,hj.2⟩
  rw [heleft,Fin.card_Icc,Fin.card_Icc] at hleft
  have h1 := A.left.monotone hkl
  have h2 := A.right.monotone hkl
  omega

end WordMatching

theorem segment_encode_block {α : Type*} {w : ℕ} (c : α → Fin w → Bool)
    (x : List α) (i : Fin x.length) (s n : ℕ) (hs : s+n ≤ w) :
    segment (encode c x) (i.val*w+s) n = interval c (x.get i) s n := by
  have ha : i.val*w+s+n ≤ (encode c x).length := by rw [length_encode]; nlinarith [i.isLt]
  apply List.ext_getElem
  · rw [length_segment ha]
    simp only [interval,List.length_take,List.length_drop,List.length_ofFn]
    omega
  · intro j hj hk
    have hjn : j < n := by simpa only [length_segment ha] using hj
    have hjw : s+j < w := by omega
    have hh := get_encode_block c x i ⟨s+j,hjw⟩
    simpa only [segment,interval,List.getElem_take,List.getElem_drop,List.getElem_ofFn,
      List.get_eq_getElem,Nat.add_assoc] using hh

namespace WordMatching
variable {α : Type*} {x y : List α} {w q : ℕ} {c : α → Fin w → Bool}

theorem offset_interior_labels (hw : 0 < w) {δ : ℝ} (hδ : δ ≤ 1)
    (hc : OffsetLocal δ c) (A : WordMatching (encode c x) (encode c y) q)
    (k : Fin q) (i : Fin x.length) (j : Fin y.length)
    (hi : (A.left k).val/w=i.val) (hj : (A.right k).val/w=j.val)
    (hp : w/8 ≤ (A.left k).val%w) (hp' : (A.left k).val%w+w/8 ≤ w)
    (hloss : (A.sourceLoss w i+A.spanLoss w i : ℕ)  <  δ*(w/8 : ℕ)) :
    x.get i=y.get j := by
  classical
  let u := w/8
  let p := (A.left k).val%w
  let r := (A.right k).val%w
  let U := A.sourceLoss w i
  let V := A.spanLoss w i
  have hloss' : ((U+V : ℕ) : ℝ) < δ*u := hloss
  have hUV : U+V < u := by
    have hnon : (0 : ℝ) ≤ u := by positivity
    have hh : (U+V : ℝ) < u := by push_cast at hloss'; nlinarith
    exact_mod_cast hh
  have hV : V < u := by omega
  have hup : u ≤ p := hp
  have hpu : p+u ≤ w := hp'
  have hpl : p < w := Nat.mod_lt _ hw
  have hrl : r < w := Nat.mod_lt _ hw
  have hleft : (A.left k).val=i.val*w+p := by
    have hh := Nat.mod_add_div (A.left k).val w
    rw [hi] at hh
    dsimp [p]
    nlinarith
  have hright : (A.right k).val=j.val*w+r := by
    have hh := Nat.mod_add_div (A.right k).val w
    rw [hj] at hh
    dsimp [r]
    nlinarith
  have hk : k∈A.sourceBlock w i := (A.mem_sourceBlock w i k).mpr hi
  have bound {a b t : ℕ} (hat : a+t ≤ w) (hbt : b+t ≤ w) :
      (Finset.univ.filter (fun z : Fin q =>
        i.val*w+a ≤ (A.left z).val ∧ (A.left z).val < i.val*w+a+t ∧
        j.val*w+b ≤ (A.right z).val ∧ (A.right z).val < j.val*w+b+t)).card  ≤
        lcs (interval c (x.get i) a t) (interval c (y.get j) b t) := by
    have hai : i.val*w+a+t ≤ (encode c x).length := by rw [length_encode]; nlinarith [i.isLt]
    have hbj : j.val*w+b+t ≤ (encode c y).length := by rw [length_encode]; nlinarith [j.isLt]
    simpa only [segment_encode_block c x i a t hat,segment_encode_block c y j b t hbt] using
      matching_segments_card A (i.val*w+a) (j.val*w+b) t hai hbj
  by_contra hne
  by_cases hf : r+u ≤ w
  · let a := i.val*w+p
    let b := j.val*w+r
    let t := u-V
    let K := Finset.univ.filter (fun z : Fin q =>  a ≤ (A.left z).val ∧ (A.left z).val < a+t)
    have ha : i.val*w ≤ a := by dsimp [a]; omega
    have hat : a+t ≤ (i.val+1)*w := by dsimp [a,t]; nlinarith [Nat.sub_le u V]
    have hcard : t ≤ K.card+U := A.interval_card_loss hw ha hat
    have hsub : K ⊆ Finset.univ.filter (fun z : Fin q =>
        i.val*w+p ≤ (A.left z).val ∧ (A.left z).val < i.val*w+p+u ∧
        j.val*w+r ≤ (A.right z).val ∧ (A.right z).val < j.val*w+r+u) := by
      intro z hz
      have hpos : a ≤ (A.left z).val ∧ (A.left z).val < a+t := (Finset.mem_filter.mp hz).2
      have hzi : (A.left z).val/w=i.val :=
        Nat.div_eq_of_lt_le (ha.trans hpos.1) (hpos.2.trans_le hat)
      have hkz : k ≤ z := A.left.le_iff_le.mp (by change (A.left k).val ≤ (A.left z).val; simpa only [hleft] using hpos.1)
      have hg := A.gap_right_le hk ((A.mem_sourceBlock w i z).mpr hzi) hkz
      have hmono := A.right.monotone hkz
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_univ _,?_,?_,?_,?_⟩ <;> dsimp [a,b,t] at * <;> omega
    have hb := (Finset.card_le_card hsub).trans (bound hpu hf)
    have hlocal := hc (x.get i) (y.get j) hne p r hpu hf
    have hs : (u : ℝ) ≤ (lcs (interval c (x.get i) p u) (interval c (y.get j) r u):ℝ)+U+V := by
      have hc' : u ≤ lcs (interval c (x.get i) p u) (interval c (y.get j) r u)+U+V := by dsimp [t] at hcard; omega
      exact_mod_cast hc'
    change _ ≤ (1-δ)*(u : ℝ) at hlocal
    push_cast at hloss'
    nlinarith only [hs,hlocal,hloss']
  · let a := i.val*w+(p+1-(u-V))
    let t := u-V
    have hrfit : u ≤ r+1 := by dsimp [u] at *; omega
    have hpfit : u ≤ p+1 := by omega
    have hps : p+1-u+u ≤ w := by omega
    have hrs : r+1-u+u ≤ w := by omega
    let K := Finset.univ.filter (fun z : Fin q =>  a ≤ (A.left z).val ∧ (A.left z).val < a+t)
    have ha : i.val*w ≤ a := by dsimp [a]; omega
    have hat : a+t ≤ (i.val+1)*w := by
      dsimp [a,t]
      rw [Nat.add_mul, one_mul]
      omega
    have hcard : t ≤ K.card+U := A.interval_card_loss hw ha hat
    have hsub : K ⊆ Finset.univ.filter (fun z : Fin q =>
        i.val*w+(p+1-u) ≤ (A.left z).val ∧ (A.left z).val < i.val*w+(p+1-u)+u ∧
        j.val*w+(r+1-u) ≤ (A.right z).val ∧ (A.right z).val < j.val*w+(r+1-u)+u) := by
      intro z hz
      have hpos : a ≤ (A.left z).val ∧ (A.left z).val < a+t := (Finset.mem_filter.mp hz).2
      have hzi : (A.left z).val/w=i.val :=
        Nat.div_eq_of_lt_le (ha.trans hpos.1) (hpos.2.trans_le hat)
      have hzk : z ≤ k := A.left.le_iff_le.mp (by change (A.left z).val ≤ (A.left k).val; dsimp [a,t] at hpos; omega)
      have hg := A.gap_right_le ((A.mem_sourceBlock w i z).mpr hzi) hk hzk
      have hmono := A.right.monotone hzk
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_univ _,?_,?_,?_,?_⟩ <;> dsimp [a,t] at * <;> omega
    have hb := (Finset.card_le_card hsub).trans (bound hps hrs)
    have hlocal := hc (x.get i) (y.get j) hne (p+1-u) (r+1-u) hps hrs
    have hs : (u : ℝ) ≤ (lcs (interval c (x.get i) (p+1-u) u) (interval c (y.get j) (r+1-u) u):ℝ)+U+V := by
      have hc' : u ≤ lcs (interval c (x.get i) (p+1-u) u) (interval c (y.get j) (r+1-u) u)+U+V := by dsimp [t] at hcard; omega
      exact_mod_cast hc'
    change _ ≤ (1-δ)*(u : ℝ) at hlocal
    push_cast at hloss'
    nlinarith only [hs,hlocal,hloss']

end WordMatching

end FiniteCircle

end OAI

-- ---- platform node ----
open OAI OAI.FiniteCircle OAI.FiniteCircle.WordMatching
open scoped BigOperators List
open scoped ComplexConjugate
open RCLike Module


theorem solution : type_of% @_root_.OAI.FiniteCircle.WordMatching.offset_interior_labels := @_root_.OAI.FiniteCircle.WordMatching.offset_interior_labels
