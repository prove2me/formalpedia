-- Prove2me | solution 1 for Nock.Verb.cost_stepP
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:26:40.826297+00:00
-- url     : https://prove2.me/submissions/f9990290-9253-4d32-9b00-98a1bde034fb

module
public import Definitions.Def_LeanPool_PureNock_PureAgreement
public import Mathlib.Tactic.IntervalCases
public import Definitions.Def_LeanPool_PureNock_PureComplete
public import Theorems.Thm_Nock_Verb_isTerminal_of_map_ofNoun
public import Theorems.Thm_Nock_Verb_vcost_slot_eq
public import Theorems.Thm_Nock_Verb_vcost_equal_eq
public import Theorems.Thm_Nock_Verb_vcost_minus_eq
public import Theorems.Thm_Nock_Verb_vcost_edit_eq
public import Theorems.Thm_Nock_Verb_cost_local
public import Theorems.Thm_Nock_Verb_denP_F_subnode
public import Theorems.Thm_Nock_Verb_vcost_replace_cong
public import Theorems.Thm_Nock_Verb_children_terminal_of_getIndex
public import Theorems.Thm_Nock_Verb_den_localP
public import Theorems.Thm_Nock_Verb_editOk_enum
public import Theorems.Thm_Nock_Verb_editOk_reduce
public import Theorems.Thm_Nock_Verb_getIndex_eq_some_iff
public import Theorems.Thm_Nock_Verb_mem_nodes_of_map
public import Theorems.Thm_Nock_Verb_next_eq_some_iff
public import Theorems.Thm_Nock_Verb_ofNoun_terminal
public import Theorems.Thm_Nock_Verb_vcost_terminal


set_option autoImplicit true
@[expose] public section
public section
open Nock
open Nock.Verb
open Noun
namespace Nock.Verb
theorem _root_.solution {F : Nat} {v v' : Verb} {x x' : Noun}
    (hwf : editOk v = true) (hv : denP F v = some x) (hv' : denP F v' = some x')
    (h : next v = some v') : vcost F v' < vcost F v := by
  obtain ⟨i, sub, r₀, hmax, hmap, hdom, hred, hv'eq⟩ := next_eq_some_iff.1 h
  have hgi : getIndex v = some i := getIndex_eq_some_iff.2 hmax
  have hoksub : editOk sub = true := editOk_enum v 0 hwf (i, sub) (mem_nodes_of_map hmap)
  have hokr0 : editOk r₀ = true := editOk_reduce hred hoksub
  obtain ⟨w, hmapw, hpw⟩ := hmax.1
  have hpsub : Verb.isPending sub = true := (Option.some.inj (hmapw.symm.trans hmap)) ▸ hpw
  have hgraph : ∀ y, DenP sub y ↔ DenP r₀ y := fun y => den_localP hdom hred
  -- denP-definedness of sub at F
  obtain ⟨xs, hxs⟩ := denP_F_subnode hwf hv hmap
  -- strict local decrease at the redex
  have hlocal : vcost F r₀ < vcost F sub := by
    cases sub with
    | leaf k => simp [isPending] at hpsub
    | node a L R =>
        obtain ⟨hL, hR⟩ := children_terminal_of_getIndex hgi hmap
        cases a with
        | null => simp [isPending, Action.isNull] at hpsub
        | wut => simp [reduce] at hred
        | star => exact cost_local hL hR hxs hred
        | slot =>
            have ht0 : isTerminal r₀ = true := by
              cases L with
              | leaf ax => rw [reduce] at hred; simp only [noun] at hred
                           exact isTerminal_of_map_ofNoun hred
              | node a2 l2 r2 => rw [reduce] at hred; simp only [noun] at hred; simp at hred
            rw [vcost_terminal r₀ ht0]
            simp only [vcost_slot_eq, vcost_terminal L hL, vcost_terminal R hR]; omega
        | equal =>
            have ht0 : isTerminal r₀ = true := by
              rw [reduce] at hred; obtain rfl := Option.some.inj hred; exact ofNoun_terminal _
            rw [vcost_terminal r₀ ht0]
            simp only [vcost_equal_eq, vcost_terminal L hL, vcost_terminal R hR]; omega
        | minus =>
            have ht0 : isTerminal r₀ = true := by
              cases L with
              | leaf ax =>
                  rw [reduce] at hred; simp only [noun] at hred
                  split at hred
                  · obtain rfl := Option.some.inj hred; exact ofNoun_terminal _
                  · exact isTerminal_of_map_ofNoun hred
                  · simp at hred
              | node a2 l2 r2 => rw [reduce] at hred; simp only [noun] at hred; simp at hred
            rw [vcost_terminal r₀ ht0]
            simp only [vcost_minus_eq, vcost_terminal L hL, vcost_terminal R hR]; omega
        | edit =>
            have ht0 : isTerminal r₀ = true := by
              cases L with
              | leaf ax =>
                  cases R with
                  | leaf k => simp [reduce, noun] at hred
                  | node rb nw od =>
                      simp only [reduce, noun] at hred
                      exact isTerminal_of_map_ofNoun hred
              | node a2 l2 r2 => simp [reduce, noun] at hred
            rw [vcost_terminal r₀ ht0]
            simp only [vcost_edit_eq, vcost_terminal L hL, vcost_terminal R hR]; omega
  -- congruence
  have hv'2 : denP F (replaceAt i v r₀) = some x' := hv'eq ▸ hv'
  have hcong : vcost F (replaceAt i v r₀) + vcost F sub = vcost F v + vcost F r₀ :=
    vcost_replace_cong F i sub r₀ hpsub hgraph hokr0 v 0 x x' hwf hmap hv hv'2
  rw [hv'eq]
  omega
end Nock.Verb
