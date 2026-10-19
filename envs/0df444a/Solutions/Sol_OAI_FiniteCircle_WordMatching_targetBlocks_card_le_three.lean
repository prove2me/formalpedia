-- Prove2me | solution 1 for OAI.FiniteCircle.WordMatching.targetBlocks_card_le_three
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T16:20:25.597706+00:00
-- url     : https://prove2.me/submissions/5c6e941e-182c-4f32-bca9-3d9b418f57fa

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/FiniteCircle/BlockMatching.lean:L120-L152
-- (upload_full_project.md Phase 4): solution for node OAI.FiniteCircle.WordMatching.targetBlocks_card_le_three. The node keeps its source
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

namespace WordMatching
variable {α : Type*} {x y : List α} {q : ℕ}

theorem targetBlocks_card_le_three (A : WordMatching x y q) {w : ℕ} (hw : 0 < w)
    {S : Finset (Fin q)} (hspan : (A.rightSpan S).card ≤ 2*w) :
    (A.targetBlocks w S).card ≤ 3 := by
  by_cases h : S.Nonempty
  · let lo := (A.right (S.min' h)).val
    let hi := (A.right (S.max' h)).val
    have hle : lo ≤ hi := A.right.monotone (S.min'_le _ (S.max'_mem h))
    have hspan' : hi + 1 - lo ≤ 2*w := by
      simpa only [A.rightSpan_eq_Icc h, Fin.card_Icc] using hspan
    have hdiv : hi/w ≤ lo/w+2 := by
      have hlo := Nat.mod_add_div lo w
      have hhi := Nat.mod_add_div hi w
      have hm := Nat.mod_lt lo hw
      by_contra hh
      have hh : lo/w+3 ≤ hi/w := by omega
      have hh' := Nat.mul_le_mul_left w hh
      have hs : hi+1 ≤ lo+2*w := by omega
      have hh2 : w*(lo/w)+3*w ≤ hi := calc
        _ = w*(lo/w+3) := by ring
        _ ≤ w*(hi/w) := hh'
        _ ≤ hi := Nat.mul_div_le hi w
      have hlo2 : lo < w*(lo/w)+w := by omega
      omega
    have hs : A.targetBlocks w S ⊆ Finset.Icc (lo/w) (lo/w+2) := by
      intro j hj
      obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hj
      have hklo : lo ≤ (A.right k).val := A.right.monotone (S.min'_le _ hk)
      have hkhi : (A.right k).val ≤ hi := A.right.monotone (S.le_max' _ hk)
      exact Finset.mem_Icc.mpr ⟨Nat.div_le_div_right hklo, (Nat.div_le_div_right hkhi).trans hdiv⟩
    have hc := Finset.card_le_card hs
    rw [Nat.card_Icc] at hc
    omega
  · simp [targetBlocks, Finset.not_nonempty_iff_eq_empty.mp h]

end WordMatching

end FiniteCircle

end OAI

-- ---- platform node ----
open OAI OAI.FiniteCircle OAI.FiniteCircle.WordMatching
open scoped BigOperators List
open scoped ComplexConjugate
open RCLike Module


theorem solution : type_of% @_root_.OAI.FiniteCircle.WordMatching.targetBlocks_card_le_three := @_root_.OAI.FiniteCircle.WordMatching.targetBlocks_card_le_three
