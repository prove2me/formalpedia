-- Prove2me | solution 1 for OAI.FiniteCircle.WordMatching.localIndices_span
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T16:18:07.855744+00:00
-- url     : https://prove2.me/submissions/0421bcc6-277a-46af-9977-ffd73b0c8bab

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/FiniteCircle/BlockMatching.lean:L88-L105
-- (upload_full_project.md Phase 4): solution for node OAI.FiniteCircle.WordMatching.localIndices_span. The node keeps its source
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

namespace WordMatching
variable {α : Type*} {x y : List α} {q : ℕ}

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

theorem localIndices_span (A : WordMatching x y q) {w i : ℕ} (hw : 0 < w)
    {S : Finset (Fin q)} (hS : S ⊆ A.sourceBlock w i) :
    indexSpan (A.localIndices hw S) = (A.symm.rightSpan S).card := by
  by_cases h : S.Nonempty
  · have hc : 0 < S.card := Finset.card_pos.mpr h
    rw [localIndices, indexSpan_ofFn _ hc, A.symm.rightSpan_eq_Icc h, Fin.card_Icc]
    dsimp only
    rw [Finset.orderEmbOfFin_last rfl hc, Finset.orderEmbOfFin_zero rfl hc]
    simp only [symm]
    have h1 := Nat.mod_add_div (A.left (S.min' h)).val w
    have h2 := Nat.mod_add_div (A.left (S.max' h)).val w
    rw [(A.mem_sourceBlock w i _).mp (hS (S.min'_mem h))] at h1
    rw [(A.mem_sourceBlock w i _).mp (hS (S.max'_mem h))] at h2
    omega
  · have he : S = ∅ := Finset.not_nonempty_iff_eq_empty.mp h
    have hl : A.localIndices hw S = [] := List.length_eq_zero_iff.mp (by simp [he])
    rw [hl]
    simp [indexSpan, he, rightSpan]

end WordMatching

end FiniteCircle

end OAI

-- ---- platform node ----
open OAI OAI.FiniteCircle OAI.FiniteCircle.WordMatching
open scoped BigOperators List
open scoped ComplexConjugate
open RCLike Module


theorem solution : type_of% @_root_.OAI.FiniteCircle.WordMatching.localIndices_span := @_root_.OAI.FiniteCircle.WordMatching.localIndices_span
