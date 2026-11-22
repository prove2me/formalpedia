-- Prove2me | solution 1 for Nock.Verb.vcostN_replace_cong
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:26:51.956908+00:00
-- url     : https://prove2.me/submissions/0f8c455d-290c-4495-9ddc-d95eb569d8a9

module
public import Definitions.Def_LeanPool_PureNock_PureComplete
public import Mathlib.Tactic.IntervalCases
public import Definitions.Def_LeanPool_PureNock_PureCompleteHint
public import Theorems.Thm_Nock_Verb_den_children_F
public import Theorems.Thm_Nock_Verb_vcostN_star_eq
public import Theorems.Thm_Nock_Verb_vcostN_slot_eq
public import Theorems.Thm_Nock_Verb_vcostN_equal_eq
public import Theorems.Thm_Nock_Verb_vcostN_minus_eq
public import Theorems.Thm_Nock_Verb_vcostN_edit_eq
public import Theorems.Thm_Nock_Verb_vcostN_null_eq
public import Theorems.Thm_Nock_Verb_vcostN_wut_eq
public import Theorems.Thm_Nock_Verb_den_F_swap_eq
public import Theorems.Thm_Nock_Verb_editOk_children
public import Theorems.Thm_Nock_Verb_editOk_replaceAux
public import Theorems.Thm_Nock_Verb_enum_index_range
public import Theorems.Thm_Nock_Verb_findAt_append
public import Theorems.Thm_Nock_Verb_findAt_some_mem
public import Theorems.Thm_Nock_Verb_replaceAux_counter
public import Theorems.Thm_Nock_Verb_replaceAux_notMem
public import Theorems.Thm_Nock_Verb_replaceAux_rel


set_option autoImplicit true
@[expose] public section
public section
open Nock
open Nock.Verb
open Noun
namespace Nock.Verb
theorem _root_.solution (F i : Nat) (sub r₀ : Verb) (hpend : sub.isPending = true)
    (hgraph : ∀ y, Den sub y ↔ Den r₀ y) (hr0 : editOk r₀ = true) :
    ∀ (v : Verb) (c : Nat) (xv xv' : Noun),
      editOk v = true →
      findAt i (enum v c).2 = some sub →
      den F v = some xv →
      den F (replaceAux i r₀ v c).2 = some xv' →
      vcostN F (replaceAux i r₀ v c).2 + vcostN F sub = vcostN F v + vcostN F r₀ := by
  intro v
  induction v with
  | leaf k => intro c xv xv' _ hfind; simp [enum, findAt] at hfind
  | node a l r ihl ihr =>
      intro c xv xv' hok hfind hdv hdv'
      obtain ⟨hokl, hokr⟩ := editOk_children hok
      by_cases hci : c = i
      · subst hci
        have hf : findAt c (enum (Verb.node a l r) c).2 = some (Verb.node a l r) := by
          simp [enum, findAt]
        have hsub : Verb.node a l r = sub := (Option.some.inj (hf.symm.trans hfind))
        have hrepl : (replaceAux c r₀ (Verb.node a l r) c).2 = r₀ := by simp [replaceAux]
        rw [hrepl, ← hsub]
        omega
      · have hine : ¬ (i = c) := fun h => hci h.symm
        have hcL : (replaceAux i r₀ l (c + 1)).1 = (enum l (c + 1)).1 := replaceAux_counter i r₀ l
          (c + 1)
        have hfind' : findAt i (enum l (c + 1)).2 = some sub ∧
              findAt i (enum r (enum l (c + 1)).1).2 = none
            ∨ findAt i (enum l (c + 1)).2 = none ∧
              findAt i (enum r (enum l (c + 1)).1).2 = some sub := by
          simp only [enum, findAt, if_neg hine] at hfind
          rw [findAt_append] at hfind
          cases hl : findAt i (enum l (c + 1)).2 with
          | some s => rw [hl] at hfind; exact Or.inl ⟨hfind, by
              cases hr : findAt i (enum r (enum l (c + 1)).1).2 with
              | none => rfl
              | some s2 =>
                  exfalso
                  have h1 := enum_index_range l (c + 1) (i, s) (findAt_some_mem hl)
                  have h2 := enum_index_range r (enum l (c + 1)).1 (i, s2) (findAt_some_mem hr)
                  omega⟩
          | none => rw [hl] at hfind; exact Or.inr ⟨rfl, hfind⟩
        obtain ⟨⟨xl, hxl⟩, ⟨xr, hxr⟩⟩ := den_children_F hok hdv
        have hok' : editOk (replaceAux i r₀ (Verb.node a l r) c).2 = true := by
          apply editOk_replaceAux i r₀ hr0 (Verb.node a l r) c hok
          intro s hs; have : s = sub := Option.some.inj (hs.symm.trans hfind); rw [this]; exact
            hpend
        simp only [replaceAux, if_neg hci] at hdv' hok' ⊢
        rw [hcL] at hdv' hok' ⊢
        obtain ⟨⟨xl', hxl'⟩, ⟨xr', hxr'⟩⟩ := den_children_F hok' hdv'
        rcases hfind' with ⟨hLsub, hRnone⟩ | ⟨hLnone, hRsub⟩
        · have hrIH := ihl (c + 1) xl xl' hokl hLsub hxl hxl'
          have hreq : (replaceAux i r₀ r (enum l (c + 1)).1).2 = r := replaceAux_notMem i r₀ r _
            hRnone
          rw [hreq] at hxr' ⊢
          have hrelL : Rel l (replaceAux i r₀ l (c + 1)).2 := by
            apply replaceAux_rel i r₀ l (c + 1)
            intro s hs
            have : s = sub := Option.some.inj (hs.symm.trans hLsub)
            rw [this]; exact ⟨hpend, hgraph⟩
          have hlEq : xl = xl' := den_F_swap_eq hokl hrelL hxl hxl'
          cases a <;>
            simp only [vcostN_star_eq, vcostN_null_eq, vcostN_wut_eq, vcostN_slot_eq,
              vcostN_equal_eq,
              vcostN_minus_eq, vcostN_edit_eq, hxl, hxl', hxr, hlEq] <;> omega
        · have hrIH := ihr (enum l (c + 1)).1 xr xr' hokr hRsub hxr hxr'
          have hleq : (replaceAux i r₀ l (c + 1)).2 = l := replaceAux_notMem i r₀ l _ hLnone
          rw [hleq] at hxl' ⊢
          have hrelR : Rel r (replaceAux i r₀ r (enum l (c + 1)).1).2 := by
            apply replaceAux_rel i r₀ r (enum l (c + 1)).1
            intro s hs
            have : s = sub := Option.some.inj (hs.symm.trans hRsub)
            rw [this]; exact ⟨hpend, hgraph⟩
          have hrEq : xr = xr' := den_F_swap_eq hokr hrelR hxr hxr'
          cases a <;>
            simp only [vcostN_star_eq, vcostN_null_eq, vcostN_wut_eq, vcostN_slot_eq,
              vcostN_equal_eq,
              vcostN_minus_eq, vcostN_edit_eq, hxr, hxr', hxl, hrEq] <;> omega
end Nock.Verb
