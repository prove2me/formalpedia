-- Prove2me | solution 1 for OAI.FiniteCircle.StrongLocal.offsetLocal
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T16:42:25.605394+00:00
-- url     : https://prove2.me/submissions/8a8e23e3-b145-4224-a3be-f0ca87a79001

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/FiniteCircle/Codes.lean:L47-L121
-- (upload_full_project.md Phase 4): solution for node OAI.FiniteCircle.StrongLocal.offsetLocal. The node keeps its source
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
import Definitions.Def_OAI_Combinatorics_FiniteCircle_RandomCodes
import Definitions.Def_OAI_Combinatorics_FiniteCircle_Codes

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

end WordMatching

namespace WordMatching
variable {α : Type*} {x y : List α} {q : ℕ}

end WordMatching

end FiniteCircle

end OAI

-- ---- from OAI.Combinatorics.FiniteCircle.BlockMatching ----
namespace OAI

namespace FiniteCircle

open scoped BigOperators List
open scoped ComplexConjugate
open RCLike Module

theorem indexSpan_ofFn {w n : ℕ} (f : Fin n → Fin w) (hn : 0 < n) :
    indexSpan (List.ofFn f) = (f ⟨n-1, by omega⟩).val + 1 - (f ⟨0, hn⟩).val := by
  cases n with
  | zero => omega
  | succ n =>
    have he : List.ofFn f ≠ [] := by simp
    have hl := List.getLast_ofFn (f := f) he
    simp only [List.ofFn_succ, List.getLast_eq_getLastD] at hl
    simp only [List.ofFn_succ, indexSpan]
    rw [hl]
    rfl

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

theorem zip_ofFn {α β : Type*} {n : ℕ} (f : Fin n → α) (g : Fin n → β) :
    (List.ofFn f).zip (List.ofFn g) = List.ofFn (fun i => (f i, g i)) := by
  apply List.ext_getElem
  · simp
  · intro i hi hj
    simp only [List.getElem_zip, List.getElem_ofFn]

namespace WordMatching
variable {α : Type*} {x y : List α} {w q : ℕ} {c : α → Fin w → Bool}

end WordMatching

namespace WordMatching
variable {α : Type*} {x y : List α} {q : ℕ}

end WordMatching

namespace WordMatching
variable {α : Type*} {x y : List α} {w q : ℕ} {c : α → Fin w → Bool}

end WordMatching

end FiniteCircle

end OAI

-- ---- from OAI.Combinatorics.FiniteCircle.Codes ----
namespace OAI

namespace FiniteCircle

open scoped BigOperators List
open scoped ComplexConjugate
open RCLike Module
open Classical

theorem get_interval {α : Type*} {w : ℕ} (c : α → Fin w → Bool)
    (a : α) {s u : ℕ} (hs : s+u ≤ w) (i : Fin (interval c a s u).length) :
    (interval c a s u).get i = c a ⟨s+i.val, by
      have hi := i.isLt
      simp only [length_interval c a hs] at hi
      omega⟩ := by
  change (((List.ofFn (c a)).drop s).take u)[i.val] = _
  simp only [List.getElem_take, List.getElem_drop, List.getElem_ofFn]

theorem indexSpan_ofFn_le {w q s u : ℕ} (f : Fin q → Fin w)
    (hb : ∀ i, s ≤ (f i).val ∧ (f i).val < s+u) : indexSpan (List.ofFn f) ≤ u := by
  by_cases hq : 0 < q
  · rw [indexSpan_ofFn f hq]
    obtain ⟨hl, _⟩ := hb ⟨0, hq⟩
    obtain ⟨_, hh⟩ := hb ⟨q-1, by omega⟩
    omega
  · have he : q = 0 := by omega
    subst q
    simp [indexSpan]

theorem StrongLocal.offsetLocal {α : Type*} {w : ℕ} {c : α → Fin w → Bool}
    (hc : StrongLocal c) (hw : 0 < w) (hd : 8 ∣ w) : OffsetLocal (1/1048576) c := by
  intro a b hab s t hs ht
  let u := w/8
  let q := lcs (interval c a s u) (interval c b t u)
  have hsu : s+u ≤ w := hs
  have htu : t+u ≤ w := ht
  have hqu : q ≤ u := by simpa only [length_interval c a hsu] using lcs_le_length_left (interval c a s u) (interval c b t u)
  have huw : u*8 = w := Nat.div_mul_cancel hd
  by_contra hn
  have hn : (1-(1:ℝ)/1048576)*(u : ℝ) < q := lt_of_not_ge hn
  have hqpos : 0 < q := by
    have hu : (0 : ℝ) < u := by exact_mod_cast (by omega : 0 < u)
    have hqr : (0 : ℝ) < q := by nlinarith
    exact_mod_cast hqr
  obtain ⟨M⟩ := exists_lcs_matching (interval c a s u) (interval c b t u)
  let f : Fin q → Fin w := fun i => ⟨s+(M.left i).val, by
    have hh := (M.left i).isLt
    simp only [length_interval c a hsu] at hh
    omega⟩
  let g : Fin q → Fin w := fun i => ⟨t+(M.right i).val, by
    have hh := (M.right i).isLt
    simp only [length_interval c b htu] at hh
    omega⟩
  have hf : StrictMono f := by
    intro i j hij
    have hh := M.left.strictMono hij
    change s+(M.left i).val < s+(M.left j).val
    exact Nat.add_lt_add_left hh s
  have hg : StrictMono g := by
    intro i j hij
    have hh := M.right.strictMono hij
    change t+(M.right i).val < t+(M.right j).val
    exact Nat.add_lt_add_left hh t
  have his : (List.ofFn f).Pairwise (fun i j => i.val < j.val) := by
    apply List.pairwise_iff_get.mpr
    intro i j hij
    simpa only [List.get_ofFn, Fin.lt_def] using hf (show (Fin.cast List.length_ofFn i) < Fin.cast List.length_ofFn j from hij)
  have hjs : (List.ofFn g).Pairwise (fun i j => i.val < j.val) := by
    apply List.pairwise_iff_get.mpr
    intro i j hij
    simpa only [List.get_ofFn, Fin.lt_def] using hg (show (Fin.cast List.length_ofFn i) < Fin.cast List.length_ofFn j from hij)
  have hsize : w ≤ 16*(List.ofFn f).length := by
    rw [List.length_ofFn]
    have hur : (u : ℝ)*8 = w := by exact_mod_cast huw
    have hqr : (w : ℝ) ≤ 16*q := by nlinarith
    exact_mod_cast hqr
  have hdef : ((u-q : ℕ) : ℝ) ≤ (w : ℝ)/1048576 := by
    rw [Nat.cast_sub hqu]
    have hur : (u : ℝ)*8 = w := by exact_mod_cast huw
    nlinarith
  have hli : ((indexSpan (List.ofFn f) - (List.ofFn f).length : ℕ) : ℝ) ≤ (w : ℝ)/1048576 := by
    have hh : indexSpan (List.ofFn f) ≤ u := indexSpan_ofFn_le (s := s) (u := u) f (fun i => by
      dsimp only [f]
      have hi := (M.left i).isLt
      simp only [length_interval c a hsu] at hi
      omega)
    rw [List.length_ofFn]
    exact (Nat.cast_le.mpr (Nat.sub_le_sub_right hh q)).trans hdef
  have hlj : ((indexSpan (List.ofFn g) - (List.ofFn g).length : ℕ) : ℝ) ≤ (w : ℝ)/1048576 := by
    have hh : indexSpan (List.ofFn g) ≤ u := indexSpan_ofFn_le (s := t) (u := u) g (fun i => by
      dsimp only [g]
      have hi := (M.right i).isLt
      simp only [length_interval c b htu] at hi
      omega)
    rw [List.length_ofFn]
    exact (Nat.cast_le.mpr (Nat.sub_le_sub_right hh q)).trans hdef
  have hbits : ∀ ij ∈ (List.ofFn f).zip (List.ofFn g), c a ij.1 = c b ij.2 := by
    intro ij hij
    rw [zip_ofFn] at hij
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hij
    have hh := M.letters i
    rw [get_interval c a hsu, get_interval c b htu] at hh
    exact hh
  exact hab (hc a b (List.ofFn f) (List.ofFn g) his hjs (by simp) hsize hli hlj hbits).1

end FiniteCircle

end OAI

-- ---- platform node ----
open OAI OAI.FiniteCircle
open scoped BigOperators List
open scoped ComplexConjugate
open RCLike Module
open Classical


theorem solution : type_of% @_root_.OAI.FiniteCircle.StrongLocal.offsetLocal := @_root_.OAI.FiniteCircle.StrongLocal.offsetLocal
