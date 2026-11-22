-- Prove2me | solution 1 for LatinQuarter.Textbook.cyclic_criticalSet
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T17:27:59.503527+00:00
-- url     : https://prove2.me/submissions/d5daff31-7775-4e31-9676-71e4ba9c135f

module
public import Mathlib.SetTheory.Cardinal.Finite
public import Definitions.Def_LeanPool_LatinQuarter_Main
public import Definitions.Def_LeanPool_LatinQuarter_Parity
public import Definitions.Def_LeanPool_LatinQuarter_Textbook
public import Theorems.Thm_LatinQuarter_Textbook_cyclicSquare_eq
public import Theorems.Thm_LatinQuarter_Textbook_definingSet_card
public import Theorems.Thm_LatinQuarter_allTagsExponent_apply
public import Theorems.Thm_LatinQuarter_allTagsExponent_support
public import Theorems.Thm_LatinQuarter_chosenSquare_clue
public import Theorems.Thm_LatinQuarter_chosenSquare_free
public import Theorems.Thm_LatinQuarter_chosenSquare_one
public import Theorems.Thm_LatinQuarter_cornerSet_card
public import Theorems.Thm_LatinQuarter_cornerSet_isDefining
public import Theorems.Thm_LatinQuarter_mem_completions
public import Theorems.Thm_LatinQuarter_mem_cornerSet
public import Theorems.Thm_LatinQuarter_tag_sq
attribute [local simp] LatinQuarter.allTagsExponent_apply
attribute [local simp] LatinQuarter.allTagsExponent_support
attribute [local simp] LatinQuarter.chosenSquare_clue
attribute [local simp] LatinQuarter.chosenSquare_free
attribute [local simp] LatinQuarter.chosenSquare_one
attribute [local simp] LatinQuarter.mem_completions
attribute [local simp] LatinQuarter.mem_cornerSet
attribute [local simp] LatinQuarter.tag_sq



set_option autoImplicit true
@[expose] public section
public section
open LatinQuarter LatinQuarter.Textbook
namespace LatinQuarter.Textbook
theorem _root_.solution (n : ℕ) (hn : 0 < n) :
    ∃ T, CriticalSet (cyclicSquare n) T ∧ T.card = n * n / 4 := by
  let f : Fin n × Fin n → Fin n × Fin n × Fin n :=
    fun p => (p.1, p.2, cyclicSquare n p.1 p.2)
  have hf : Function.Injective f := by
    intro p q h
    simp only [f, Prod.mk.injEq] at h
    exact Prod.ext h.1 h.2.1
  let T := (cornerSet n).image f
  have hcard : T.card = n * n / 4 := by
    rw [Finset.card_image_of_injective _ hf, cornerSet_card n hn]
  have hdef := cornerSet_isDefining n hn
  have hlat : Latin (cyclicSquare n) := by
    rw [latin_iff, cyclicSquare_eq]
    exact hdef.1
  have hcomp : Completes T (cyclicSquare n) := by
    refine ⟨hlat, ?_⟩
    intro t ht
    obtain ⟨p, _, rfl⟩ := Finset.mem_image.mp ht
    rfl
  have hT : DefiningSet (cyclicSquare n) T := by
    refine ⟨hcomp, ?_⟩
    intro M hM
    rw [cyclicSquare_eq]
    apply hdef.2 M ((latin_iff M).mp hM.1)
    intro p hp
    have hMp : M p.1 p.2 = cyclicSquare n p.1 p.2 :=
      hM.2 (f p) (Finset.mem_image.mpr ⟨p, hp, rfl⟩)
    rw [hMp, cyclicSquare_eq]
  refine ⟨T, ⟨hT, ?_⟩, hcard⟩
  intro t ht
  have hLc : Completes (T.erase t) (cyclicSquare n) :=
    ⟨hlat, fun u hu => hcomp.2 u (Finset.mem_of_mem_erase hu)⟩
  by_contra hle
  rw [not_lt, numCompletions] at hle
  have hsub := (Finite.card_le_one_iff_subsingleton).mp hle
  have hdef' : DefiningSet (cyclicSquare n) (T.erase t) :=
    ⟨hLc, fun M hM => congrArg Subtype.val
      (Subsingleton.elim (⟨M, hM⟩ : {M // Completes (T.erase t) M}) ⟨_, hLc⟩)⟩
  have h1 := definingSet_card hdef'
  have h2 := Finset.card_erase_lt_of_mem ht
  rw [hcard] at h2
  exact (not_le.mpr h2) h1
end LatinQuarter.Textbook
