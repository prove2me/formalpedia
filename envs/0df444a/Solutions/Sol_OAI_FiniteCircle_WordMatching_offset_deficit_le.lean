-- Prove2me | solution 1 for OAI.FiniteCircle.WordMatching.offset_deficit_le
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T16:32:14.252668+00:00
-- url     : https://prove2.me/submissions/0c6d733d-3ee4-4632-8ce8-882f68308541

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/FiniteCircle/OffsetRecovery.lean:L245-L292
-- (upload_full_project.md Phase 4): solution for node OAI.FiniteCircle.WordMatching.offset_deficit_le. The node keeps its source
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
import Theorems.Thm_OAI_FiniteCircle_monotone_assignment_deficit

-- ---- from OAI.Combinatorics.FiniteCircle.OffsetRecovery ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
private theorem dite_eq_left.{u} {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t : c → α} {e : ¬c → α} : (dite c t e) = t hc := @dif_pos c h hc α t e

namespace OAI

namespace FiniteCircle

open scoped BigOperators List
open scoped ComplexConjugate
open RCLike Module

namespace WordMatching
variable {α : Type*} {x y : List α} {q : ℕ}

end WordMatching

namespace WordMatching
variable {α : Type*} {x y : List α} {q : ℕ}

theorem partnerAt_eq (A : WordMatching x y q) {w i p : ℕ} {k : Fin q}
    (hk : (A.left k).val = i*w+p) : A.partnerAt w i p = (A.right k).val/w := by
  have hh : A.matchedAt w i p := ⟨k,hk⟩
  rw [partnerAt,dite_eq_left hh]
  have he : Classical.choose hh = k := A.left.injective
    (Fin.ext ((Classical.choose_spec hh).trans hk.symm))
  rw [he]

end WordMatching

namespace WordMatching
variable {α : Type*} {x y : List α} {q : ℕ}

end WordMatching

namespace WordMatching
variable {α : Type*} {x y : List α} {w q : ℕ} {c : α → Fin w → Bool}

theorem offset_deficit_le (A : WordMatching (encode c x) (encode c y) q)
    (hw : 0 < w) (p : ℕ) (G : Finset ℕ) (hG : G ⊆ Finset.range x.length)
    (hlabels : ∀ i ∈ G, ∀ k : Fin q, (A.left k).val=i*w+p →
      x[i]? = y[(A.right k).val/w]?) :
    deficit x y ≤ 2*(x.length-(G.filter (fun i => A.matchedAt w i p)).card) +
      ((G.filter (fun i => i+1 < x.length)).filter (fun i => A.duplicateAt w i p)).card := by
  classical
  let S := G.filter (fun i => A.matchedAt w i p)
  let f := fun i => A.partnerAt w i p
  have hS : S ⊆ Finset.range x.length := (Finset.filter_subset _ _).trans hG
  have hf : ∀ i ∈ S, f i < y.length := by
    intro i hi
    obtain ⟨k,hk⟩ := (Finset.mem_filter.mp hi).2
    rw [show f i = (A.right k).val/w from A.partnerAt_eq hk]
    apply (Nat.div_lt_iff_lt_mul hw).mpr
    simpa only [length_encode,Nat.mul_comm] using (A.right k).isLt
  have hm : ∀ i ∈ S, ∀ j ∈ S, i ≤ j → f i ≤ f j := by
    intro i hi j hj hij
    obtain ⟨k,hk⟩ := (Finset.mem_filter.mp hi).2
    obtain ⟨l,hl⟩ := (Finset.mem_filter.mp hj).2
    rw [show f i = (A.right k).val/w from A.partnerAt_eq hk,
      show f j = (A.right l).val/w from A.partnerAt_eq hl]
    apply Nat.div_le_div_right
    apply A.right.monotone
    apply A.left.le_iff_le.mp
    change (A.left k).val ≤ (A.left l).val
    rw [hk,hl]
    exact Nat.add_le_add_right (Nat.mul_le_mul_right w hij) p
  have hl : ∀ i (hi : i ∈ S), x[i]'(Finset.mem_range.mp (hS hi)) = y[f i]'(hf i hi) := by
    intro i hi
    obtain ⟨k,hk⟩ := (Finset.mem_filter.mp hi).2
    have hh := hlabels i (Finset.mem_filter.mp hi).1 k hk
    rw [← A.partnerAt_eq hk] at hh
    change x[i]? = y[f i]? at hh
    simpa only [List.getElem?_eq_getElem (Finset.mem_range.mp (hS hi)),
      List.getElem?_eq_getElem (hf i hi),Option.some.injEq] using hh
  have hh := monotone_assignment_deficit S hS f hf hm hl
  have hs : S.filter (fun i => i+1 ∈ S ∧ f i=f (i+1)) ⊆
      (G.filter (fun i => i+1 < x.length)).filter (fun i => A.duplicateAt w i p) := by
    intro i hi
    obtain ⟨hi,hj,hfij⟩ := Finset.mem_filter.mp hi
    obtain ⟨k,hk⟩ := (Finset.mem_filter.mp hi).2
    obtain ⟨l,hl⟩ := (Finset.mem_filter.mp hj).2
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hi).1,
      Finset.mem_range.mp (hS hj)⟩, k,l,hk,hl,?_⟩
    simpa only [f,A.partnerAt_eq hk,A.partnerAt_eq hl] using hfij
  exact hh.trans (Nat.add_le_add_left (Finset.card_le_card hs) _)

end WordMatching

namespace WordMatching
variable {α : Type*} {x y : List α} {w q : ℕ} {c : α → Fin w → Bool}

end WordMatching

end FiniteCircle

end OAI

-- ---- platform node ----
open OAI OAI.FiniteCircle OAI.FiniteCircle.WordMatching
open scoped BigOperators List
open scoped ComplexConjugate
open RCLike Module


theorem solution : type_of% @_root_.OAI.FiniteCircle.WordMatching.offset_deficit_le := @_root_.OAI.FiniteCircle.WordMatching.offset_deficit_le
