-- Prove2me | solution 1 for OAI.TreeEdit.span_card_le_lcs
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-16T02:38:17.015142+00:00
-- url     : https://prove2.me/submissions/315acb4e-9e99-492f-8545-7dd1a4dc202a

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/TreeEdit/SegmentComparison.lean:L100-L154
-- (upload_full_project.md Phase 4): solution for node OAI.TreeEdit.span_card_le_lcs. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_TreeEdit
import Definitions.Def_OAI_Combinatorics_TreeEdit_Model
import Definitions.Def_OAI_Combinatorics_TreeEdit_FiniteProbability
import Definitions.Def_OAI_Combinatorics_TreeEdit_EditMetric
import Definitions.Def_OAI_Combinatorics_TreeEdit_Alignments
import Definitions.Def_OAI_Combinatorics_TreeEdit_SegmentComparison
import Theorems.Thm_OAI_TreeEdit_Alignment_le_lcs

-- ---- from OAI.Combinatorics.TreeEdit.SegmentComparison ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
private theorem dite_eq_left.{u} {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t : c → α} {e : ¬c → α} : (dite c t e) = t hc := @dif_pos c h hc α t e

namespace OAI

namespace TreeEdit

universe u

variable {α : Type u} {x y z : List α}

theorem length_segment {β : Type*} (x : List β) {start len : ℕ}
    (h : start + len ≤ x.length) : (segment x start len).length = len := by
  simp only [segment, List.length_take, List.length_drop]
  omega

theorem segment_get {β : Type*} (x : List β) (start len i : ℕ)
    (hi : i < (segment x start len).length) :
    (segment x start len)[i] = x[start + i]'(by
      simp only [segment, List.length_take, List.length_drop] at hi
      omega) := by
  simp only [segment, List.getElem_take, List.getElem_drop]

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

theorem span_card_le_lcs {β : Type*} {N : ℕ} (x y : List β)
    (f : Fin N ↪o Fin x.length) (g : Fin N ↪o Fin y.length)
    (hfg : ∀ i, x.get (f i) = y.get (g i))
    (s : Finset (Fin N)) (hs : s.Nonempty) :
    s.card ≤ lcs (segment x (f (s.min' hs)).val (indexSpan f s).card)
      (segment y (g (s.min' hs)).val (indexSpan g s).card) := by
  let e := s.orderEmbOfFin rfl
  let a := (f (s.min' hs)).val
  let b := (g (s.min' hs)).val
  let X := segment x a (indexSpan f s).card
  let Y := segment y b (indexSpan g s).card
  have hX : X.length = (indexSpan f s).card := length_segment _ (span_bounds f s hs)
  have hY : Y.length = (indexSpan g s).card := length_segment _ (span_bounds g s hs)
  have hlo (i : Fin s.card) : a ≤ (f (e i)).val :=
    f.monotone (s.min'_le _ (s.orderEmbOfFin_mem rfl i))
  have hro (i : Fin s.card) : b ≤ (g (e i)).val :=
    g.monotone (s.min'_le _ (s.orderEmbOfFin_mem rfl i))
  have hli (i : Fin s.card) : (f (e i)).val - a < X.length := by
    rw [hX]
    have hu := f.monotone (s.le_max' _ (s.orderEmbOfFin_mem rfl i))
    have hf := span_length_formula f s hs
    have hl := hlo i
    dsimp [a, e] at *
    omega
  have hri (i : Fin s.card) : (g (e i)).val - b < Y.length := by
    rw [hY]
    have hu := g.monotone (s.le_max' _ (s.orderEmbOfFin_mem rfl i))
    have hf := span_length_formula g s hs
    have hl := hro i
    dsimp [b, e] at *
    omega
  let fl : Fin s.card → Fin X.length := fun i => ⟨(f (e i)).val - a, hli i⟩
  let gr : Fin s.card → Fin Y.length := fun i => ⟨(g (e i)).val - b, hri i⟩
  have hfl : StrictMono fl := by
    intro i j hij
    have hi := hlo i
    have hj := hlo j
    have hh := f.strictMono (e.strictMono hij)
    change (f (e i)).val - a < (f (e j)).val - a
    omega
  have hgr : StrictMono gr := by
    intro i j hij
    have hi := hro i
    have hj := hro j
    have hh := g.strictMono (e.strictMono hij)
    change (g (e i)).val - b < (g (e j)).val - b
    omega
  apply Alignment.le_lcs (x := X) (y := Y)
    ⟨OrderEmbedding.ofStrictMono fl hfl, OrderEmbedding.ofStrictMono gr hgr, ?_⟩
  intro i
  change X.get (fl i) = Y.get (gr i)
  simp only [List.get_eq_getElem, X, Y, fl, gr]
  rw [segment_get, segment_get]
  simpa only [Nat.add_sub_of_le (hlo i), Nat.add_sub_of_le (hro i),
    List.get_eq_getElem] using hfg (e i)

end TreeEdit

end OAI

-- ---- platform node ----
open OAI OAI.TreeEdit


theorem solution : type_of% @_root_.OAI.TreeEdit.span_card_le_lcs := @_root_.OAI.TreeEdit.span_card_le_lcs
