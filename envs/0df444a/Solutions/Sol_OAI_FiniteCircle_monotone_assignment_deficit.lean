-- Prove2me | solution 1 for OAI.FiniteCircle.monotone_assignment_deficit
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T16:30:18.343019+00:00
-- url     : https://prove2.me/submissions/92220f52-5a3a-4055-a182-81e56412c592

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/FiniteCircle/WindowMatching.lean:L258-L328
-- (upload_full_project.md Phase 4): solution for node OAI.FiniteCircle.monotone_assignment_deficit. The node keeps its source
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

-- ---- from OAI.Combinatorics.FiniteCircle.WindowMatching ----
namespace OAI

namespace FiniteCircle

open scoped BigOperators List
open scoped ComplexConjugate
open RCLike Module

namespace WordMatching
variable {α : Type*} {x y : List α} {q : ℕ}

end WordMatching

namespace WordMatching
variable {α : Type*} {x y : List α} {w q : ℕ} {c : α → Fin w → Bool}

end WordMatching

theorem monotone_assignment_deficit {α : Type*} {x y : List α}
    (S : Finset ℕ) (hS : S ⊆ Finset.range x.length) (f : ℕ → ℕ)
    (hf : ∀ i ∈ S, f i < y.length)
    (hm : ∀ i ∈ S, ∀ j ∈ S, i ≤ j → f i ≤ f j)
    (hl : ∀ i (hi : i ∈ S), x[i]'(Finset.mem_range.mp (hS hi)) = y[f i]'(hf i hi)) :
    deficit x y ≤ 2 * (x.length - S.card) +
      (S.filter (fun i => i+1 ∈ S ∧ f i = f (i+1))).card := by
  classical
  let D := S.filter (fun i => ∃ j ∈ S, j < i ∧ f j = f i)
  let T := S \ D
  let B := Finset.range x.length \ S
  let J := S.filter (fun i => i+1 ∈ S ∧ f i = f (i+1))
  have hD : D ⊆ S := Finset.filter_subset _ _
  have hT : T ⊆ S := Finset.sdiff_subset
  have hdpos : ∀ i ∈ D, 0 < i := by
    intro i hi
    obtain ⟨j,_,hj,_⟩ := (Finset.mem_filter.mp hi).2
    omega
  have hpred : D.image (fun i => i-1) ⊆ B ∪ J := by
    intro v hv
    obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hv
    have hip := hdpos i hi
    have hil := Finset.mem_range.mp (hS (hD hi))
    by_cases hh : i-1 ∈ S
    · apply Finset.mem_union_right
      apply Finset.mem_filter.mpr
      refine ⟨hh,?_,?_⟩
      · simpa only [Nat.sub_add_cancel (by omega : 1 ≤ i)] using hD hi
      · obtain ⟨j,hj,hji,hfj⟩ := (Finset.mem_filter.mp hi).2
        have h1 := hm j hj (i-1) hh (by omega)
        have h2 := hm (i-1) hh i (hD hi) (by omega)
        simpa only [Nat.sub_add_cancel (by omega : 1 ≤ i)] using
          (show f (i-1) = f i by omega)
    · exact Finset.mem_union_left _ (Finset.mem_sdiff.mpr
        ⟨Finset.mem_range.mpr (by omega),hh⟩)
  have hdinj : Set.InjOn (fun i : ℕ => i-1) D := by
    intro i hi j hj hij
    have := hdpos i hi
    have := hdpos j hj
    dsimp only at hij
    omega
  have hdc : D.card ≤ B.card + J.card := by
    have hh := (Finset.card_le_card hpred).trans (Finset.card_union_le B J)
    rwa [Finset.card_image_of_injOn hdinj] at hh
  have htmat : T.card ≤ lcs x y := by
    let e := T.orderEmbOfFin rfl
    have he (k : Fin T.card) : e k ∈ T := T.orderEmbOfFin_mem rfl k
    let g : Fin T.card → Fin x.length := fun k =>
      ⟨e k,Finset.mem_range.mp (hS (hT (he k)))⟩
    let h : Fin T.card → Fin y.length := fun k => ⟨f (e k),hf _ (hT (he k))⟩
    have hg : StrictMono g := fun i j hij => e.strictMono hij
    have hh : StrictMono h := by
      intro i j hij
      have heij := e.strictMono hij
      have hm' := hm (e i) (hT (he i)) (e j) (hT (he j)) heij.le
      have hneq : f (e i) ≠ f (e j) := by
        intro heq
        have hn := (Finset.mem_sdiff.mp (he j)).2
        exact hn (Finset.mem_filter.mpr ⟨hT (he j),e i,hT (he i),heij,heq⟩)
      change f (e i) < f (e j)
      exact lt_of_le_of_ne hm' hneq
    let A : WordMatching x y T.card :=
      { left := OrderEmbedding.ofStrictMono g hg
        right := OrderEmbedding.ofStrictMono h hh
        letters := fun k => hl (e k) (hT (he k)) }
    exact A.le_lcs
  have htc : T.card = S.card - D.card := Finset.card_sdiff_of_subset hD
  have hbc : B.card = x.length - S.card := by rw [Finset.card_sdiff_of_subset hS,Finset.card_range]
  dsimp only [deficit]
  dsimp only [J] at hdc
  omega

end FiniteCircle

end OAI

-- ---- platform node ----
open OAI OAI.FiniteCircle
open scoped BigOperators List
open scoped ComplexConjugate
open RCLike Module


theorem solution : type_of% @_root_.OAI.FiniteCircle.monotone_assignment_deficit := @_root_.OAI.FiniteCircle.monotone_assignment_deficit
