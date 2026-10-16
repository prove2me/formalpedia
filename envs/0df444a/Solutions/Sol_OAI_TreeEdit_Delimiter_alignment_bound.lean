-- Prove2me | solution 1 for OAI.TreeEdit.Delimiter.alignment_bound
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-16T03:23:04.002861+00:00
-- url     : https://prove2.me/submissions/35d623fe-bafc-46bf-8f64-4509089ad29e

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/TreeEdit/Delimiter.lean:L75-L132
-- (upload_full_project.md Phase 4): solution for node OAI.TreeEdit.Delimiter.alignment_bound. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_TreeEdit
import Definitions.Def_OAI_Combinatorics_TreeEdit_Model
import Definitions.Def_OAI_Combinatorics_TreeEdit_FiniteProbability
import Definitions.Def_OAI_Combinatorics_TreeEdit_EditMetric
import Definitions.Def_OAI_Combinatorics_TreeEdit_Alignments
import Definitions.Def_OAI_Combinatorics_TreeEdit_SegmentComparison
import Definitions.Def_OAI_Combinatorics_TreeEdit_CyclicWords
import Definitions.Def_OAI_Combinatorics_TreeEdit_TreeArithmetic
import Definitions.Def_OAI_Combinatorics_TreeEdit_CircleTree
import Definitions.Def_OAI_Combinatorics_TreeEdit_CircleSeparation
import Definitions.Def_OAI_Combinatorics_TreeEdit_RandomCircle
import Definitions.Def_OAI_Combinatorics_TreeEdit_FiniteFourier
import Definitions.Def_OAI_Combinatorics_TreeEdit_CircleFourier
import Definitions.Def_OAI_Combinatorics_TreeEdit_SampledSpectrum
import Definitions.Def_OAI_Combinatorics_TreeEdit_PrimeSupply
import Definitions.Def_OAI_Combinatorics_TreeEdit_CircleObstruction
import Definitions.Def_OAI_Combinatorics_TreeEdit_CircleParameters
import Definitions.Def_OAI_Combinatorics_TreeEdit_Delimiter
import Theorems.Thm_OAI_TreeEdit_Alignment_le_lcs
import Theorems.Thm_OAI_TreeEdit_card_block_fiber
import Theorems.Thm_OAI_TreeEdit_segment_encode_block
import Theorems.Thm_OAI_TreeEdit_span_card_le_lcs

-- ---- from OAI.Combinatorics.TreeEdit.Alignments ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
private theorem dite_eq_left.{u} {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t : c → α} {e : ¬c → α} : (dite c t e) = t hc := @dif_pos c h hc α t e

namespace OAI

namespace TreeEdit

universe u

variable {α : Type u} {x y z : List α}

namespace Alignment

variable {n : ℕ}

end Alignment

theorem mem_indexSpan {N L : ℕ} (f : Fin N ↪o Fin L) {s : Finset (Fin N)}
    {i : Fin N} (hi : i ∈ s) : f i ∈ indexSpan f s := by
  have hs : s.Nonempty := ⟨i, hi⟩
  simp only [indexSpan, dite_eq_left hs, Finset.mem_Icc]
  exact ⟨f.monotone (s.min'_le i hi), f.monotone (s.le_max' i hi)⟩

theorem card_le_indexSpan {N L : ℕ} (f : Fin N ↪o Fin L) (s : Finset (Fin N)) :
    s.card ≤ (indexSpan f s).card := by
  exact Finset.card_le_card_of_injOn f (fun _ hi => mem_indexSpan f hi) f.injective.injOn

theorem indexSpan_disjoint {N L K : ℕ} (f : Fin N ↪o Fin L)
    (key : Fin N → Fin K) (hk : Monotone key) {a b : Fin K} (hab : a ≠ b) :
    Disjoint (indexSpan f (Finset.univ.filter (fun i => key i = a)))
      (indexSpan f (Finset.univ.filter (fun i => key i = b))) := by
  classical
  let sa := Finset.univ.filter (fun i => key i = a)
  let sb := Finset.univ.filter (fun i => key i = b)
  change Disjoint (indexSpan f sa) (indexSpan f sb)
  by_cases ha : sa.Nonempty
  · by_cases hb : sb.Nonempty
    · have hamin : key (sa.min' ha) = a :=
        (Finset.mem_filter.mp (sa.min'_mem ha)).2
      have hamax : key (sa.max' ha) = a :=
        (Finset.mem_filter.mp (sa.max'_mem ha)).2
      have hbmin : key (sb.min' hb) = b :=
        (Finset.mem_filter.mp (sb.min'_mem hb)).2
      have hbmax : key (sb.max' hb) = b :=
        (Finset.mem_filter.mp (sb.max'_mem hb)).2
      refine Finset.disjoint_left.mpr ?_
      intro p hp hq
      simp only [indexSpan, dite_eq_left ha, dite_eq_left hb, Finset.mem_Icc] at hp hq
      rcases lt_or_gt_of_ne hab with hab | hba
      · have hh : sa.max' ha < sb.min' hb := by
          by_contra hn
          have := hk (le_of_not_gt hn)
          rw [hbmin, hamax] at this
          exact (not_le_of_gt hab) this
        exact (not_le_of_gt (f.strictMono hh)) (hq.1.trans hp.2)
      · have hh : sb.max' hb < sa.min' ha := by
          by_contra hn
          have := hk (le_of_not_gt hn)
          rw [hamin, hbmax] at this
          exact (not_le_of_gt hba) this
        exact (not_le_of_gt (f.strictMono hh)) (hp.1.trans hq.2)
    · simp [indexSpan, hb]
  · simp [indexSpan, ha]

theorem sum_span_card_le {N L K : ℕ} (f : Fin N ↪o Fin L)
    (key : Fin N → Fin K) (hk : Monotone key) :
    (∑ k : Fin K, (indexSpan f (Finset.univ.filter (fun i => key i = k))).card) ≤ L := by
  have hd : ((Finset.univ : Finset (Fin K)) : Set (Fin K)).PairwiseDisjoint
      (fun k => indexSpan f (Finset.univ.filter (fun i => key i = k))) := by
    intro a _ b _ hab
    exact indexSpan_disjoint f key hk hab
  rw [← Finset.card_biUnion hd]
  simpa using Finset.card_le_univ
    (Finset.univ.biUnion (fun k => indexSpan f (Finset.univ.filter (fun i => key i = k))))

theorem sum_span_gaps_le {N L K : ℕ} (f : Fin N ↪o Fin L)
    (key : Fin N → Fin K) (hk : Monotone key) :
    (∑ k : Fin K, ((indexSpan f (Finset.univ.filter (fun i => key i = k))).card -
      (Finset.univ.filter (fun i => key i = k)).card)) ≤ L - N := by
  rw [Finset.sum_tsub_distrib _ (fun _ _ => card_le_indexSpan f _)]
  have he : (∑ k : Fin K, (Finset.univ.filter (fun i => key i = k)).card) = N := by
    simpa using (Finset.card_eq_sum_card_fiberwise
      (s := Finset.univ) (t := Finset.univ) (f := key) (by simp)).symm
  rw [he]
  exact Nat.sub_le_sub_right (sum_span_card_le f key hk) N

end TreeEdit

end OAI

-- ---- from OAI.Combinatorics.TreeEdit.SegmentComparison ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

namespace TreeEdit

universe u

variable {α : Type u} {x y z : List α}

theorem length_segment {β : Type*} (x : List β) {start len : ℕ}
    (h : start + len ≤ x.length) : (segment x start len).length = len := by
  simp only [segment, List.length_take, List.length_drop]
  omega

theorem span_bounds {N L : ℕ} (f : Fin N ↪o Fin L) (s : Finset (Fin N))
    (hs : s.Nonempty) :
    (f (s.min' hs)).val + (indexSpan f s).card ≤ L := by
  rw [indexSpan, dite_eq_left hs, Fin.card_Icc]
  have hle := f.monotone (s.min'_le_max' hs)
  have hlt := (f (s.max' hs)).isLt
  omega

theorem span_length_formula {N L : ℕ} (f : Fin N ↪o Fin L) (s : Finset (Fin N))
    (hs : s.Nonempty) :
    (f (s.min' hs)).val + (indexSpan f s).card = (f (s.max' hs)).val + 1 := by
  rw [indexSpan, dite_eq_left hs, Fin.card_Icc]
  have hle := f.monotone (s.min'_le_max' hs)
  omega

theorem indexSpan_card_cast {N L L' : ℕ} (h : L = L')
    (f : Fin N ↪o Fin L) (s : Finset (Fin N)) :
    (indexSpan (f.comp (Fin.castOrderIso h).toOrderEmbedding) s).card =
      (indexSpan f s).card := by
  subst L'
  rfl

theorem span_in_block {M P N : ℕ} (hP : 0 < P)
    (f : Fin N ↪o Fin (M * P)) (s : Finset (Fin N)) (hs : s.Nonempty)
    (hb : blockIndex hP (f (s.min' hs)) = blockIndex hP (f (s.max' hs))) :
    (f (s.min' hs)).val % P + (indexSpan f s).card ≤ P := by
  have he := congrArg Fin.val hb
  change (f (s.min' hs)).val / P = (f (s.max' hs)).val / P at he
  have hl := span_length_formula f s hs
  have hmin := Nat.mod_add_div (f (s.min' hs)).val P
  have hmax := Nat.mod_add_div (f (s.max' hs)).val P
  have hmod := Nat.mod_lt (f (s.max' hs)).val hP
  rw [he] at hmin
  omega

end TreeEdit

end OAI

-- ---- from OAI.Combinatorics.TreeEdit.CycleCharging ----
namespace OAI

namespace TreeEdit

universe u

attribute [local instance] Classical.propDecidable

lemma blockIndex_monotone {M P N : ℕ} (hP : 0 < P)
    (f : Fin N ↪o Fin (M * P)) : Monotone (fun i => blockIndex hP (f i)) := by
  intro i j hij
  exact Nat.div_le_div_right (f.monotone hij)

lemma sum_block_losses {M P N : ℕ} (hP : 0 < P)
    (f : Fin N ↪o Fin (M * P)) :
    (∑ a : Fin M, (P - (Finset.univ.filter
      (fun i => blockIndex hP (f i) = a)).card)) = M * P - N := by
  rw [Finset.sum_tsub_distrib _ (fun a _ => card_block_fiber hP f a)]
  have he : (∑ a : Fin M, (Finset.univ.filter
      (fun i => blockIndex hP (f i) = a)).card) = N := by
    simpa using (Finset.card_eq_sum_card_fiberwise
      (s := Finset.univ) (t := Finset.univ)
      (f := fun i => blockIndex hP (f i)) (by simp)).symm
  simp [he]

end TreeEdit

end OAI

-- ---- from OAI.Combinatorics.TreeEdit.Delimiter ----
namespace OAI

namespace TreeEdit.Delimiter
open scoped BigOperators
open Classical

lemma eq_of_full_lcs {α : Type*} {x y : List α} (hl : x.length = y.length)
    (hc : x.length ≤ lcs x y) : x = y := by
  obtain ⟨z, hx, hy, hz⟩ := exists_lcs x y
  have hzx : z = x := hx.eq_of_length (by have := hx.length_le; omega)
  have hzy : z = y := hy.eq_of_length (by have := hx.length_le; omega)
  exact hzx.symm.trans hzy

lemma full_fiber {M B N : ℕ} (hB : 0 < B) (f : Fin N ↪o Fin (M*B))
    (a : Fin M) (hc : (Finset.univ.filter (fun i => blockIndex hB (f i) = a)).card = B) :
    ∃ (hs : (Finset.univ.filter (fun i => blockIndex hB (f i) = a)).Nonempty),
      (f ((Finset.univ.filter (fun i => blockIndex hB (f i) = a)).min' hs)).val = a.val*B ∧
      (indexSpan f (Finset.univ.filter (fun i => blockIndex hB (f i) = a))).card = B := by
  let S := Finset.univ.filter (fun i => blockIndex hB (f i) = a)
  have hs : S.Nonempty := Finset.card_pos.mp (by change S.card = B at hc; omega)
  have hl : blockIndex hB (f (S.min' hs)) = a := (Finset.mem_filter.mp (S.min'_mem hs)).2
  have hu : blockIndex hB (f (S.max' hs)) = a := (Finset.mem_filter.mp (S.max'_mem hs)).2
  have hw := span_in_block hB f S hs (hl.trans hu.symm)
  have hge := card_le_indexSpan f S
  have he : (indexSpan f S).card = B := by change S.card = B at hc; omega
  have hm : (f (S.min' hs)).val % B = 0 := by omega
  have hd := Nat.div_add_mod (f (S.min' hs)).val B
  have hq := congrArg Fin.val hl
  change (f (S.min' hs)).val / B = a.val at hq
  refine ⟨hs, ?_, he⟩
  rw [hq, hm, Nat.add_zero, Nat.mul_comm] at hd
  exact hd.symm

lemma good_fiber_matches {α : Type*} {M B N : ℕ} (hB : 0 < B)
    (c : α → Word Bool B) (hc : Synchronizing c) (x y : Word α M)
    (f g : Fin N ↪o Fin (M*B))
    (hfg : ∀ i, (encode c x.val).get (Fin.cast (by rw [length_encode, x.property]) (f i)) =
      (encode c y.val).get (Fin.cast (by rw [length_encode, y.property]) (g i)))
    (a : Fin M) (hfull : (Finset.univ.filter (fun i => blockIndex hB (f i) = a)).card = B)
    (hgap : (indexSpan g (Finset.univ.filter (fun i => blockIndex hB (f i) = a))).card = B) :
    ∃ (hs : (Finset.univ.filter (fun i => blockIndex hB (f i) = a)).Nonempty) (b : Fin M),
      (g ((Finset.univ.filter (fun i => blockIndex hB (f i) = a)).min' hs)).val = b.val*B ∧
      x.val.get (Fin.cast x.property.symm a) = y.val.get (Fin.cast y.property.symm b) := by
  let S := Finset.univ.filter (fun i => blockIndex hB (f i) = a)
  obtain ⟨hs, hstart, hspan⟩ := full_fiber hB f a hfull
  let f' := f.comp (Fin.castOrderIso (by rw [length_encode, x.property] : M*B = (encode c x.val).length)).toOrderEmbedding
  let g' := g.comp (Fin.castOrderIso (by rw [length_encode, y.property] : M*B = (encode c y.val).length)).toOrderEmbedding
  have hbase := span_card_le_lcs (encode c x.val) (encode c y.val) f' g' hfg S hs
  have hfc : (indexSpan f' S).card = B := (indexSpan_card_cast _ f S).trans hspan
  have hgc : (indexSpan g' S).card = B := (indexSpan_card_cast _ g S).trans hgap
  have hxs : segment (encode c x.val) (f' (S.min' hs)).val B = (c (x.val.get (Fin.cast x.property.symm a))).val := by
    change segment (encode c x.val) (f (S.min' hs)).val B = _
    rw [hstart]
    have hh := segment_encode_block c x.val a.val 0 B (by rw [x.property]; exact a.isLt) (by omega)
    simpa only [Nat.add_zero, segment, List.drop_zero, ← (c x.val[a.val]).property, List.take_length, List.get_eq_getElem, Fin.val_cast] using hh
  have hgy : (g' (S.min' hs)).val+B ≤ (encode c y.val).length := by
    simpa only [hgc] using span_bounds g' S hs
  have hfx : (f' (S.min' hs)).val+B ≤ (encode c x.val).length := by
    simpa only [hfc] using span_bounds f' S hs
  have heq : segment (encode c y.val) (g' (S.min' hs)).val B = (c (x.val.get (Fin.cast x.property.symm a))).val := by
    rw [hfc, hgc, hfull] at hbase
    have he := eq_of_full_lcs (x := segment (encode c x.val) (f' (S.min' hs)).val B) (y := segment (encode c y.val) (g' (S.min' hs)).val B) (by rw [length_segment _ hfx, length_segment _ hgy])
      (by simpa only [length_segment _ hfx] using hbase)
    exact he.symm.trans hxs
  obtain ⟨b, hb, hlabel⟩ := hc y.val (x.val.get (Fin.cast x.property.symm a)) _ hgy heq
  exact ⟨hs, Fin.cast y.property b, hb, hlabel.symm⟩

lemma alignment_bound {α : Type*} {M B N : ℕ} (hB : 0 < B)
    (c : α → Word Bool B) (hc : Synchronizing c) (x y : Word α M)
    (f g : Fin N ↪o Fin (M*B))
    (hfg : ∀ i, (encode c x.val).get (Fin.cast (by rw [length_encode, x.property]) (f i)) =
      (encode c y.val).get (Fin.cast (by rw [length_encode, y.property]) (g i))) :
    M ≤ lcs x.val y.val + 2*(M*B-N) := by
  let S (a : Fin M) := Finset.univ.filter (fun i => blockIndex hB (f i) = a)
  let G := Finset.univ.filter (fun a : Fin M => (S a).card = B ∧ (indexSpan g (S a)).card = B)
  have hgood (a : Fin M) (ha : a ∈ G) := good_fiber_matches hB c hc x y f g hfg a
    (Finset.mem_filter.mp ha).2.1 (Finset.mem_filter.mp ha).2.2
  let e := G.orderEmbOfFin rfl
  have hem (i : Fin G.card) : e i ∈ G := G.orderEmbOfFin_mem rfl i
  let minPos (i : Fin G.card) := (S (e i)).min' (hgood (e i) (hem i)).choose
  let b (i : Fin G.card) := (hgood (e i) (hem i)).choose_spec.choose
  have hb (i : Fin G.card) : (g (minPos i)).val = (b i).val*B := (hgood (e i) (hem i)).choose_spec.choose_spec.1
  have hl (i : Fin G.card) : x.val.get (Fin.cast x.property.symm (e i)) = y.val.get (Fin.cast y.property.symm (b i)) :=
    (hgood (e i) (hem i)).choose_spec.choose_spec.2
  have hsmin (i : Fin G.card) : blockIndex hB (f (minPos i)) = e i :=
    (Finset.mem_filter.mp ((S (e i)).min'_mem _)).2
  have hminmono : StrictMono minPos := by
    intro i j hij
    by_contra hn
    have h := blockIndex_monotone hB f (le_of_not_gt hn)
    dsimp only at h
    rw [hsmin, hsmin] at h
    exact not_le_of_gt (e.strictMono hij) h
  have hbmono : StrictMono b := by
    intro i j hij
    have hh := g.strictMono (hminmono hij)
    change (g (minPos i)).val < (g (minPos j)).val at hh
    rw [hb, hb] at hh
    exact (Nat.mul_lt_mul_right hB).mp hh
  have hglcs : G.card ≤ lcs x.val y.val := Alignment.le_lcs
    ⟨e.comp (Fin.castOrderIso x.property.symm).toOrderEmbedding,
      (OrderEmbedding.ofStrictMono b hbmono).comp (Fin.castOrderIso y.property.symm).toOrderEmbedding, hl⟩
  have hbad : ∀ a : Fin M, (if a ∈ G then 0 else 1) ≤
      (B-(S a).card) + ((indexSpan g (S a)).card - (S a).card) := by
    intro a
    have hc' := card_block_fiber hB f a
    have hs' := card_le_indexSpan g (S a)
    split_ifs with ha
    · omega
    · have hn : ¬ ((S a).card = B ∧ (indexSpan g (S a)).card = B) := by simpa only [G, Finset.mem_filter, Finset.mem_univ, true_and] using ha
      change (S a).card ≤ B at hc'
      omega
  have hsum := Finset.sum_le_sum (s := Finset.univ) (fun a _ => hbad a)
  have hloss := sum_block_losses hB f
  have hgap := sum_span_gaps_le g (fun i => blockIndex hB (f i)) (blockIndex_monotone hB f)
  have hcount : (∑ a : Fin M, if a ∈ G then 0 else 1) = M-G.card := by
    simpa only [ite_not, Finset.sum_boole, Finset.filter_not, Finset.filter_mem_eq_inter, Finset.univ_inter,
      Finset.card_sdiff_of_subset (Finset.subset_univ G), Finset.card_univ, Fintype.card_fin, Nat.cast_id] using
      (Finset.sum_boole (fun a : Fin M => a ∉ G) Finset.univ : (∑ a : Fin M, if a ∉ G then (1 : ℕ) else 0) = _)
  rw [hcount, Finset.sum_add_distrib] at hsum
  change (∑ a : Fin M, (B-(S a).card)) = M*B-N at hloss
  change (∑ a : Fin M, ((indexSpan g (S a)).card-(S a).card)) ≤ M*B-N at hgap
  rw [hloss] at hsum
  have hcard : G.card ≤ M := by simpa using Finset.card_le_univ G
  omega

end TreeEdit.Delimiter

namespace TreeEdit.Delimiter
open scoped BigOperators
open Classical

end TreeEdit.Delimiter

end OAI

-- ---- platform node ----
open OAI OAI.TreeEdit OAI.TreeEdit.Delimiter
open scoped BigOperators
open Classical


theorem solution : type_of% @_root_.OAI.TreeEdit.Delimiter.alignment_bound := @_root_.OAI.TreeEdit.Delimiter.alignment_bound
