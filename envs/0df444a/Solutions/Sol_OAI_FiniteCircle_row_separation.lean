-- Prove2me | solution 1 for OAI.FiniteCircle.row_separation
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T14:35:43.142572+00:00
-- url     : https://prove2.me/submissions/2220f3c8-9524-490b-942e-533a2f6935e8

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/FiniteCircle/TaggedRows.lean:L256-L297
-- (upload_full_project.md Phase 4): solution for node OAI.FiniteCircle.row_separation. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_FiniteCircle
import Definitions.Def_OAI_Combinatorics_FiniteCircle_Model
import Definitions.Def_OAI_Combinatorics_FiniteCircle_Edit
import Definitions.Def_OAI_Combinatorics_FiniteCircle_Matching
import Definitions.Def_OAI_Combinatorics_FiniteCircle_TaggedRows
import Theorems.Thm_OAI_FiniteCircle_WordMatching_le_lcs
import Theorems.Thm_OAI_FiniteCircle_WordMatching_sourceBlock_card_le

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

theorem rightSpan_eq_Icc (A : WordMatching x y q) {S : Finset (Fin q)} (h : S.Nonempty) :
    A.rightSpan S = Finset.Icc (A.right (S.min' h)) (A.right (S.max' h)) := by
  ext j
  simp only [rightSpan, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_Icc]
  constructor
  · rintro ⟨i, hi, k, hk, hij, hjk⟩
    exact ⟨(A.right.monotone (S.min'_le _ hi)).trans hij,
      hjk.trans (A.right.monotone (S.le_max' _ hk))⟩
  · rintro ⟨hlo, hhi⟩
    exact ⟨_, S.min'_mem h, _, S.max'_mem h, hlo, hhi⟩

end WordMatching

end FiniteCircle

end OAI

-- ---- from OAI.Combinatorics.FiniteCircle.TaggedRows ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

namespace FiniteCircle

open scoped BigOperators List

namespace WordMatching
variable {β : Type*} {x y : List β} {q : ℕ}

theorem card_onSegments_le (A : WordMatching x y q) (S : Finset (Fin q))
    {s n t m : ℕ} (hs : s+n ≤ x.length) (ht : t+m ≤ y.length)
    (hleft : ∀ i ∈ S, s ≤ (A.left i).val ∧ (A.left i).val < s+n)
    (hright : ∀ i ∈ S, t ≤ (A.right i).val ∧ (A.right i).val < t+m) :
    S.card ≤ lcs (segment x s n) (segment y t m) :=
  (A.onSegments S hs ht hleft hright).le_lcs

end WordMatching

theorem position_decomposition (x t L : ℕ) :
    x = (x/(t*L))*(t*L) + ((x/L)%t)*L + x%L := by
  have h1 := Nat.mod_add_div (x/L) t
  have h2 := Nat.mod_add_div x L
  rw [Nat.div_div_eq_div_mul, Nat.mul_comm L t] at h1
  nlinarith

theorem split_positions_gap {t L i x₁ x₂ y₁ y₂ : ℕ} (ht : 2 ≤ t) (hL : 0 < L)
    (hx₁ : x₁/(t*L) = i) (hx₂ : x₂/(t*L) = i)
    (hy : y₁/(t*L) < y₂/(t*L)) (hx : x₁ ≤ x₂)
    (hxy : y₁ ≤ y₂)
    (htag₁ : (x₁/L)%t = (y₁/L)%t) (htag₂ : (x₂/L)%t = (y₂/L)%t) :
    (t-2)*L + (x₂+1-x₁) ≤ y₂+1-y₁ := by
  have ex₁ := position_decomposition x₁ t L
  have ex₂ := position_decomposition x₂ t L
  have ey₁ := position_decomposition y₁ t L
  have ey₂ := position_decomposition y₂ t L
  rw [hx₁, htag₁] at ex₁
  rw [hx₂, htag₂] at ex₂
  have hb := Nat.mul_le_mul_right (t*L) (show y₁/(t*L)+1 ≤ y₂/(t*L) by omega)
  have hrx₂ := Nat.mod_lt x₂ hL
  have hry₁ := Nat.mod_lt y₁ hL
  have hT : (t-2)*L+2*L = t*L := by
    rw [← Nat.add_mul]
    congr 1
    omega
  have hgap : (t-2)*L+x₂+y₁ ≤ y₂+x₁ := by nlinarith [Nat.zero_le (x₁%L), Nat.zero_le (y₂%L)]
  omega

namespace WordMatching
variable {β : Type*} {x y : List β} {q : ℕ}

theorem spanLoss_of_split (A : WordMatching x y q) {t L i : ℕ}
    (ht : 2 ≤ t) (hL : 0 < L) (tag : β → ℕ)
    (hx : ∀ k : Fin x.length, tag (x.get k) = (k.val/L)%t)
    (hy : ∀ k : Fin y.length, tag (y.get k) = (k.val/L)%t)
    (hsplit : ¬A.singleTargetRow (t*L) i) :
    (t-2)*L ≤ A.spanLoss (t*L) i := by
  classical
  let S := A.sourceBlock (t*L) i
  have hS : S.Nonempty := by
    by_contra he
    have he : S = ∅ := Finset.not_nonempty_iff_eq_empty.mp he
    apply hsplit
    exact ⟨0, fun k hk => False.elim (by change k ∈ S at hk; simp [he] at hk)⟩
  let a := S.min' hS
  let b := S.max' hS
  have ha : a ∈ S := S.min'_mem hS
  have hb : b ∈ S := S.max'_mem hS
  have hab : a ≤ b := S.min'_le b hb
  have hleft : (A.left a).val ≤ (A.left b).val := A.left.monotone hab
  have hright : (A.right a).val ≤ (A.right b).val := A.right.monotone hab
  have hrow : (A.right a).val/(t*L) < (A.right b).val/(t*L) := by
    by_contra hn
    have he : (A.right a).val/(t*L) = (A.right b).val/(t*L) := by
      have hh := Nat.div_le_div_right (c := t*L) hright
      omega
    apply hsplit
    refine ⟨(A.right a).val/(t*L), fun k hk => ?_⟩
    have hlo := Nat.div_le_div_right (c := t*L) (show (A.right a).val ≤ (A.right k).val from
      A.right.monotone (S.min'_le k hk))
    have hhi := Nat.div_le_div_right (c := t*L) (show (A.right k).val ≤ (A.right b).val from
      A.right.monotone (S.le_max' k hk))
    omega
  have htag (k : Fin q) : ((A.left k).val/L)%t = ((A.right k).val/L)%t := by
    rw [← hx, ← hy, A.letters]
  have hgap := split_positions_gap ht hL ((A.mem_sourceBlock (t*L) i a).mp ha)
    ((A.mem_sourceBlock (t*L) i b).mp hb) hrow hleft hright (htag a) (htag b)
  have hcard := A.symm.card_le_rightSpan S
  have hsx := A.symm.rightSpan_eq_Icc hS
  have hsy := A.rightSpan_eq_Icc hS
  rw [hsx, Fin.card_Icc] at hcard
  change (t-2)*L ≤ (A.rightSpan S).card - S.card
  rw [hsy, Fin.card_Icc]
  change S.card ≤ (A.left b).val+1-(A.left a).val at hcard
  change (t-2)*L ≤ (A.right b).val+1-(A.right a).val-S.card
  omega

theorem sourceLoss_of_single (A : WordMatching x y q) {W N i : ℕ}
    (hW : 0 < W) (hx : x.length = W*N) (hy : y.length = W*N) (hi : i < N)
    (hS : (A.sourceBlock W i).Nonempty) (hsingle : A.singleTargetRow W i) :
    ∃ j : Fin N, deficit (segment x (i*W) W) (segment y (j.val*W) W) ≤ A.sourceLoss W i := by
  obtain ⟨j, hj⟩ := hsingle
  obtain ⟨k, hk⟩ := hS
  have hjN : j < N := by
    have hkj := hj k hk
    have hkp := (A.right k).isLt
    simp only [hy] at hkp
    rw [← hkj]
    exact (Nat.div_lt_iff_lt_mul hW).mpr (by nlinarith)
  have hxi : i*W+W ≤ x.length := by rw [hx]; nlinarith
  have hyj : j*W+W ≤ y.length := by rw [hy]; nlinarith
  have hc := A.card_onSegments_le (A.sourceBlock W i) hxi hyj
    (fun k hk => by
      have hh := (A.mem_sourceBlock W i k).mp hk
      have h1 := Nat.mod_add_div (A.left k).val W
      have h2 := Nat.mod_lt (A.left k).val hW
      rw [hh] at h1
      constructor <;> nlinarith [Nat.zero_le ((A.left k).val%W)])
    (fun k hk => by
      have hh := hj k hk
      have h1 := Nat.mod_add_div (A.right k).val W
      have h2 := Nat.mod_lt (A.right k).val hW
      rw [hh] at h1
      constructor <;> nlinarith [Nat.zero_le ((A.right k).val%W)])
  refine ⟨⟨j, hjN⟩, ?_⟩
  simpa only [deficit, length_segment hxi, sourceLoss] using Nat.sub_le_sub_left hc W

end WordMatching

theorem row_separation {β : Type*} {x y : List β} {N t L : ℕ} (hL : 0 < L) (ht : 4 ≤ t)
    (hx : x.length = (t*L)*N) (hy : y.length = (t*L)*N)
    (tag : β → ℕ)
    (htagx : ∀ k : Fin x.length, tag (x.get k) = (k.val/L)%t)
    (htagy : ∀ k : Fin y.length, tag (y.get k) = (k.val/L)%t)
    (ρ : ℝ) (hρ : ρ ≤ 1/2)
    (hrows : ∀ i j : Fin N, ρ*(t*L) ≤
      (deficit (segment x (i.val*(t*L)) (t*L)) (segment y (j.val*(t*L)) (t*L)) : ℝ)) :
    ρ/2 * x.length ≤ (deficit x y : ℝ) := by
  classical
  have hW : 0 < t*L := by positivity
  obtain ⟨A⟩ := exists_lcs_matching x y
  have hper (i : Fin N) : ρ*(t*L) ≤ (A.sourceLoss (t*L) i : ℝ)+(A.spanLoss (t*L) i : ℝ) := by
    by_cases hS : (A.sourceBlock (t*L) i).Nonempty
    · by_cases hsingle : A.singleTargetRow (t*L) i
      · obtain ⟨j, hj⟩ := A.sourceLoss_of_single hW hx hy i.isLt hS hsingle
        have hh : (deficit (segment x (i.val*(t*L)) (t*L)) (segment y (j.val*(t*L)) (t*L)) : ℝ) ≤ A.sourceLoss (t*L) i := by exact_mod_cast hj
        exact (hrows i j).trans (hh.trans (le_add_of_nonneg_right (by positivity)))
      · have hh := A.spanLoss_of_split (by omega) hL tag htagx htagy hsingle
        have hh' : ((t-2 : ℕ) : ℝ)*L ≤ A.spanLoss (t*L) i := by exact_mod_cast hh
        have ht' : (4 : ℝ) ≤ t := by exact_mod_cast ht
        rw [Nat.cast_sub (by omega : 2 ≤ t), Nat.cast_ofNat] at hh'
        have hlt : (0 : ℝ) ≤ t*L := by positivity
        have hρ' := mul_le_mul_of_nonneg_right hρ hlt
        nlinarith [Nat.cast_nonneg (α := ℝ) (A.sourceLoss (t*L) i)]
    · have he : A.sourceBlock (t*L) i = ∅ := Finset.not_nonempty_iff_eq_empty.mp hS
      have hu : A.sourceLoss (t*L) i = t*L := by simp [WordMatching.sourceLoss, he]
      rw [hu, Nat.cast_mul]
      have hh := mul_le_mul_of_nonneg_right hρ (show (0 : ℝ) ≤ t*L by positivity)
      nlinarith [Nat.cast_nonneg (α := ℝ) (A.spanLoss (t*L) i)]
  have hsum := Finset.sum_le_sum (s := Finset.univ) (fun i _ => hper i)
  rw [Finset.sum_add_distrib] at hsum
  have hU := A.sum_sourceLoss hW hx
  have hV := A.sum_spanLoss_le hW hx hy
  have hUr : (∑ i : Fin N, (A.sourceLoss (t*L) i : ℝ)) = deficit x y := by
    exact_mod_cast (show (∑ i : Fin N, A.sourceLoss (t*L) i) = deficit x y by simpa only [deficit, hx] using hU)
  have hVr : (∑ i : Fin N, (A.spanLoss (t*L) i : ℝ)) ≤ deficit x y := by
    exact_mod_cast (show (∑ i : Fin N, A.spanLoss (t*L) i) ≤ deficit x y by simpa only [deficit, hx] using hV)
  rw [hUr] at hsum
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hsum
  rw [hx, Nat.cast_mul, Nat.cast_mul]
  nlinarith

end FiniteCircle

end OAI

-- ---- platform node ----
open OAI OAI.FiniteCircle
open scoped BigOperators List


theorem solution : type_of% @_root_.OAI.FiniteCircle.row_separation := @_root_.OAI.FiniteCircle.row_separation
