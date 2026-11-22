-- Prove2me | solution 1 for Nock.Verb.cost_stepN
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:28:33.883478+00:00
-- url     : https://prove2.me/submissions/e1c47259-5224-438f-a2af-651c03c2bfca

module
public import Definitions.Def_LeanPool_PureNock_PureComplete
public import Mathlib.Tactic.IntervalCases
public import Definitions.Def_LeanPool_PureNock_PureCompleteHint
public import Theorems.Thm_Nock_Verb_redexHint_eq_reduce_of_hintExpand_none
public import Theorems.Thm_Nock_Verb_vcostN_slot_eq
public import Theorems.Thm_Nock_Verb_vcostN_equal_eq
public import Theorems.Thm_Nock_Verb_vcostN_minus_eq
public import Theorems.Thm_Nock_Verb_vcostN_edit_eq
public import Theorems.Thm_Nock_Verb_vcostN_terminal
public import Theorems.Thm_Nock_Verb_cost_localN
public import Theorems.Thm_Nock_Verb_den_F_subnode
public import Theorems.Thm_Nock_Verb_vcostN_replace_cong
public import Theorems.Thm_Nock_Verb_children_terminal_of_getIndex
public import Theorems.Thm_Nock_Verb_denHint_local
public import Theorems.Thm_Nock_Verb_editOk_enum
public import Theorems.Thm_Nock_Verb_editOk_redexHint
public import Theorems.Thm_Nock_Verb_getIndex_eq_some_iff
public import Theorems.Thm_Nock_Verb_isTerminal_of_map_ofNoun
public import Theorems.Thm_Nock_Verb_mem_nodes_of_map
public import Theorems.Thm_Nock_Verb_nextHint_eq_some_iff
public import Theorems.Thm_Nock_Verb_ofNoun_terminal


set_option autoImplicit true
@[expose] public section
public section
open Nock
open Nock.Verb
open Noun
namespace Nock.Verb
theorem _root_.solution {F : Nat} {v v' : Verb} {x x' : Noun}
    (hwf : editOk v = true) (hv : den F v = some x) (hv' : den F v' = some x')
    (h : nextHint v = some v') : vcostN F v' < vcostN F v := by
  obtain ⟨i, sub, r₀, hmax, hmap, hdom, hred, hv'eq⟩ := nextHint_eq_some_iff.1 h
  have hgi : getIndex v = some i := getIndex_eq_some_iff.2 hmax
  have hoksub : editOk sub = true := editOk_enum v 0 hwf (i, sub) (mem_nodes_of_map hmap)
  have hokr0 : editOk r₀ = true := editOk_redexHint hred hoksub
  obtain ⟨w, hmapw, hpw⟩ := hmax.1
  have hpsub : Verb.isPending sub = true := (Option.some.inj (hmapw.symm.trans hmap)) ▸ hpw
  have hgraph : ∀ y, Den sub y ↔ Den r₀ y := fun y => denHint_local hdom hred
  obtain ⟨xs, hxs⟩ := den_F_subnode hwf hv hmap
  have hlocal : vcostN F r₀ < vcostN F sub := by
    cases sub with
    | leaf k => simp [isPending] at hpsub
    | node a L R =>
        obtain ⟨hL, hR⟩ := children_terminal_of_getIndex hgi hmap
        cases a with
        | null => simp [isPending, Action.isNull] at hpsub
        | wut => simp [redexHint, hintExpand, reduce] at hred
        | star => exact cost_localN hL hR hxs hred
        | slot =>
            have hEXn : hintExpand (Verb.node .slot L R) = none := by simp [hintExpand]
            rw [redexHint_eq_reduce_of_hintExpand_none hEXn] at hred
            have ht0 : isTerminal r₀ = true := by
              cases L with
              | leaf ax => rw [reduce] at hred; simp only [noun] at hred
                           exact isTerminal_of_map_ofNoun hred
              | node a2 l2 r2 => rw [reduce] at hred; simp only [noun] at hred; simp at hred
            rw [vcostN_terminal r₀ ht0]
            simp only [vcostN_slot_eq, vcostN_terminal L hL, vcostN_terminal R hR]; omega
        | equal =>
            have hEXn : hintExpand (Verb.node .equal L R) = none := by simp [hintExpand]
            rw [redexHint_eq_reduce_of_hintExpand_none hEXn] at hred
            have ht0 : isTerminal r₀ = true := by
              rw [reduce] at hred; obtain rfl := Option.some.inj hred; exact ofNoun_terminal _
            rw [vcostN_terminal r₀ ht0]
            simp only [vcostN_equal_eq, vcostN_terminal L hL, vcostN_terminal R hR]; omega
        | minus =>
            have hEXn : hintExpand (Verb.node .minus L R) = none := by simp [hintExpand]
            rw [redexHint_eq_reduce_of_hintExpand_none hEXn] at hred
            have ht0 : isTerminal r₀ = true := by
              cases L with
              | leaf ax =>
                  rw [reduce] at hred; simp only [noun] at hred
                  split at hred
                  · obtain rfl := Option.some.inj hred; exact ofNoun_terminal _
                  · exact isTerminal_of_map_ofNoun hred
                  · simp at hred
              | node a2 l2 r2 => rw [reduce] at hred; simp only [noun] at hred; simp at hred
            rw [vcostN_terminal r₀ ht0]
            simp only [vcostN_minus_eq, vcostN_terminal L hL, vcostN_terminal R hR]; omega
        | edit =>
            have hEXn : hintExpand (Verb.node .edit L R) = none := by simp [hintExpand]
            rw [redexHint_eq_reduce_of_hintExpand_none hEXn] at hred
            have ht0 : isTerminal r₀ = true := by
              cases L with
              | leaf ax =>
                  cases R with
                  | leaf k => simp [reduce, noun] at hred
                  | node rb nw od =>
                      simp only [reduce, noun] at hred
                      exact isTerminal_of_map_ofNoun hred
              | node a2 l2 r2 => simp [reduce, noun] at hred
            rw [vcostN_terminal r₀ ht0]
            simp only [vcostN_edit_eq, vcostN_terminal L hL, vcostN_terminal R hR]; omega
  have hv'2 : den F (replaceAt i v r₀) = some x' := hv'eq ▸ hv'
  have hcong : vcostN F (replaceAt i v r₀) + vcostN F sub = vcostN F v + vcostN F r₀ :=
    vcostN_replace_cong F i sub r₀ hpsub hgraph hokr0 v 0 x x' hwf hmap hv hv'2
  rw [hv'eq]
  omega
end Nock.Verb
