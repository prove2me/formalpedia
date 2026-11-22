-- Prove2me | solution 1 for Nock.Verb.progressP
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:24:38.355849+00:00
-- url     : https://prove2.me/submissions/08d24b46-c219-4cb7-89a6-ab20d95d1dc7

module
public import Definitions.Def_LeanPool_PureNock_Agreement
public import Definitions.Def_LeanPool_PureNock_Trace
public import Definitions.Def_LeanPool_PureNock_PaperReference
public import Mathlib.Tactic.IntervalCases
public import Definitions.Def_LeanPool_PureNock_PureAgreement
public import Theorems.Thm_Nock_Verb_EvP_op2
public import Theorems.Thm_Nock_Verb_EvP_op5
public import Theorems.Thm_Nock_Verb_EvP_op6
public import Theorems.Thm_Nock_Verb_EvP_op7
public import Theorems.Thm_Nock_Verb_EvP_op8
public import Theorems.Thm_Nock_Verb_EvP_op9
public import Theorems.Thm_Nock_Verb_EvP_op10
public import Theorems.Thm_Nock_Verb_DenP_star
public import Theorems.Thm_Nock_Verb_DenP_slot
public import Theorems.Thm_Nock_Verb_DenP_minus
public import Theorems.Thm_Nock_Verb_DenP_edit_node
public import Theorems.Thm_Nock_Verb_DenP_edit_leaf
public import Theorems.Thm_Nock_Verb_DenP_wut
public import Theorems.Thm_Nock_Verb_DenP_terminal_iff
public import Theorems.Thm_Nock_Verb_DenP_subnode
public import Theorems.Thm_Nock_Verb_evalPaper_atom_none
public import Theorems.Thm_Nock_Verb_evalPaper_op_ge11
public import Theorems.Thm_Nock_Verb_inDomain_star_of
public import Theorems.Thm_Nock_Verb_children_terminal_of_getIndex
public import Theorems.Thm_Nock_Verb_getIndex_eq_some_iff
public import Theorems.Thm_Nock_Verb_getIndex_none_iff_terminal
public import Theorems.Thm_Nock_Verb_map_some_of_getIndex
public import Theorems.Thm_Nock_Verb_next_eq_some_iff

section
@[expose] public section
namespace Nock
namespace Verb
open Noun
private theorem paper_progress_for_evaluation {v : Verb} (L R : Verb) (hL
  : L.isTerminal = true)
  (hR : R.isTerminal = true) (y : Noun) (hsuby : (node Action.star L R).DenP y)
  (hstep :
    (node Action.star L R).inDomain = true → (node Action.star L R).reduce.isSome = true → ∃ v',
      v.next = some v') :
  ∃ v', v.next = some v' := by
  obtain ⟨a', b', hLa, hRb, hev⟩ := DenP_star.1 hsuby
  have haL : a' = L.noun := (DenP_terminal_iff hL).1 hLa
  have hbR : b' = R.noun := (DenP_terminal_iff hR).1 hRb
  subst haL; subst hbR
  cases R with
  | leaf k =>
      exfalso; obtain ⟨f, hf⟩ := hev
      simp [noun, evalPaper_atom_none] at hf
  | node rb fi n2 =>
      simp only [isTerminal, Bool.and_eq_true] at hR
      obtain ⟨⟨hrb, hfi_t⟩, hn2⟩ := hR
      simp only [noun] at hev
      cases fi with
      | node bi ic id =>
          exact hstep (inDomain_star_of hL hrb hfi_t hn2 rfl) (by simp [reduce, redex])
      | leaf op =>
          simp only [noun] at hev
          have hop : op < 11 := by
            rcases Nat.lt_or_ge op 11 with h | h
            · exact h
            · exfalso
              obtain ⟨f, hf⟩ := hev
              rw [evalPaper_op_ge11 f L.noun n2.noun op h] at hf
              exact absurd hf (by simp)
          interval_cases op
          · exact hstep (inDomain_star_of hL hrb rfl hn2 (by decide)) (by simp [reduce, redex])
          · exact hstep (inDomain_star_of hL hrb rfl hn2 (by decide)) (by simp [reduce, redex])
          · obtain ⟨hb, hc, _, _, hn2eq, _⟩ := EvP_op2.1 hev
            cases n2 with
            | leaf k => rw [noun] at hn2eq; exact absurd hn2eq (by simp)
            | node b2 c2 d2 =>
                exact hstep (inDomain_star_of hL hrb rfl hn2 (by decide)) (by simp [reduce, redex])
          · exact hstep (inDomain_star_of hL hrb rfl hn2 (by decide)) (by simp [reduce, redex])
          · exact hstep (inDomain_star_of hL hrb rfl hn2 (by decide)) (by simp [reduce, redex])
          · obtain ⟨hb, hc, _, _, hn2eq, _⟩ := EvP_op5.1 hev
            cases n2 with
            | leaf k => rw [noun] at hn2eq; exact absurd hn2eq (by simp)
            | node b2 c2 d2 =>
                exact hstep (inDomain_star_of hL hrb rfl hn2 (by decide)) (by simp [reduce, redex])
          · obtain ⟨b, c, d, cv, hn2eq, _⟩ := EvP_op6.1 hev
            cases n2 with
            | leaf k => rw [noun] at hn2eq; exact absurd hn2eq (by simp)
            | node b2 c2 d2 =>
                exact hstep (inDomain_star_of hL hrb rfl hn2 (by decide)) (by simp [reduce, redex])
          · obtain ⟨hb, hc, _, hn2eq, _⟩ := EvP_op7.1 hev
            cases n2 with
            | leaf k => rw [noun] at hn2eq; exact absurd hn2eq (by simp)
            | node b2 c2 d2 =>
                exact hstep (inDomain_star_of hL hrb rfl hn2 (by decide)) (by simp [reduce, redex])
          · obtain ⟨hb, hc, _, hn2eq, _⟩ := EvP_op8.1 hev
            cases n2 with
            | leaf k => rw [noun] at hn2eq; exact absurd hn2eq (by simp)
            | node b2 c2 d2 =>
                exact hstep (inDomain_star_of hL hrb rfl hn2 (by decide)) (by simp [reduce, redex])
          · obtain ⟨ax, c, _, _, hn2eq, _⟩ := EvP_op9.1 hev
            cases n2 with
            | leaf k => rw [noun] at hn2eq; exact absurd hn2eq (by simp)
            | node b2 c2 d2 =>
                exact hstep (inDomain_star_of hL hrb rfl hn2 (by decide)) (by simp [reduce, redex])
          · obtain ⟨ax, c, d, new, old, hn2eq, _⟩ := EvP_op10.1 hev
            cases n2 with
            | leaf k => rw [noun] at hn2eq; exact absurd hn2eq (by simp)
            | node b2 hd d2 =>
                rw [noun] at hn2eq
                have hhd : hd.noun = Noun.cell (Noun.atom ax) c := (Noun.cell.inj hn2eq).1
                cases hd with
                | leaf k => rw [noun] at hhd; exact absurd hhd (by simp)
                | node bhd axv cc =>
                    exact hstep (inDomain_star_of hL hrb rfl hn2 (by decide)) (by simp [reduce,
                      redex])
end Verb
end Nock
end
end

set_option autoImplicit true
@[expose] public section
public section
open Nock
open Nock.Verb
open Noun
namespace Nock.Verb
theorem _root_.solution {v : Verb} {x : Noun} (hwf : editOk v = true) (hd : DenP v x)
    (hnt : isTerminal v = false) : ∃ v', next v = some v' := by
  have hne : getIndex v ≠ none := by
    intro h; rw [getIndex_none_iff_terminal] at h; rw [h] at hnt; simp at hnt
  obtain ⟨i, hi⟩ := Option.ne_none_iff_exists'.mp hne
  obtain ⟨sub, hmap⟩ := map_some_of_getIndex hi
  have hmax : IsMaxPending dfsLt v i := getIndex_eq_some_iff.1 hi
  have hsubp : sub.isPending = true := by
    obtain ⟨w, hw, hwp⟩ := hmax.1
    rw [hmap] at hw
    have heq : sub = w := Option.some.inj hw
    rw [heq]; exact hwp
  cases sub with
  | leaf k => simp [isPending] at hsubp
  | node a L R =>
      obtain ⟨hL, hR⟩ := children_terminal_of_getIndex hi hmap
      obtain ⟨y, hsuby⟩ := DenP_subnode hwf hd hmap
      have hstep : inDomain (Verb.node a L R) = true →
          (reduce (Verb.node a L R)).isSome = true → ∃ v', next v = some v' := by
        intro hdom hred
        cases hrr : reduce (Verb.node a L R) with
        | none => rw [hrr] at hred; simp at hred
        | some rr =>
            exact ⟨replaceAt i v rr,
              next_eq_some_iff.2 ⟨i, Verb.node a L R, rr, hmax, hmap, hdom, hrr, rfl⟩⟩
      cases a with
      | null => simp [isPending, Action.isNull] at hsubp
      | wut => exact absurd hsuby DenP_wut
      | equal =>
          have hdom : inDomain (Verb.node .equal L R) = true := by
            simp [inDomain, inOpcodeDomain, opReady, Action.isOperator, hL, hR]
          exact hstep hdom (by simp [reduce])
      | slot =>
          obtain ⟨ax, b, hLax, hRb, hslot⟩ := DenP_slot.1 hsuby
          have hLn : L.noun = Noun.atom ax := ((DenP_terminal_iff hL).1 hLax).symm
          have hbR : b = R.noun := (DenP_terminal_iff hR).1 hRb
          subst hbR
          have hdom : inDomain (Verb.node .slot L R) = true := by
            simp [inDomain, inOpcodeDomain, opReady, Action.isOperator, hL, hR]
          exact hstep hdom (by simp [reduce, hLn, hslot])
      | minus =>
          obtain ⟨b, hRb, hcase⟩ := DenP_minus.1 hsuby
          have hbR : b = R.noun := (DenP_terminal_iff hR).1 hRb
          subst hbR
          have hdom : inDomain (Verb.node .minus L R) = true := by
            simp [inDomain, inOpcodeDomain, opReady, Action.isOperator, hL, hR]
          rcases hcase with ⟨hL3, _⟩ | ⟨hL4, hlus⟩
          · have hLn : L.noun = Noun.atom 3 := ((DenP_terminal_iff hL).1 hL3).symm
            exact hstep hdom (by simp [reduce, hLn])
          · have hLn : L.noun = Noun.atom 4 := ((DenP_terminal_iff hL).1 hL4).symm
            exact hstep hdom (by simp [reduce, hLn, hlus])
      | edit =>
          cases R with
          | leaf k => exact absurd hsuby DenP_edit_leaf
          | node rb nw od =>
              simp only [isTerminal, Bool.and_eq_true] at hR
              obtain ⟨⟨hrb, hnw⟩, hod⟩ := hR
              obtain ⟨ax, n, o, hLax, hnwn, hodo, hedit⟩ := DenP_edit_node.1 hsuby
              have hLn : L.noun = Noun.atom ax := ((DenP_terminal_iff hL).1 hLax).symm
              have hnwn' : n = nw.noun := (DenP_terminal_iff hnw).1 hnwn
              have hodo' : o = od.noun := (DenP_terminal_iff hod).1 hodo
              subst hnwn'; subst hodo'
              have hdom : inDomain (Verb.node .edit L (Verb.node rb nw od)) = true := by
                simp [inDomain, inOpcodeDomain, opReady, Action.isOperator, hL,
                      isTerminal, hrb, hnw, hod]
              exact hstep hdom (by simp [reduce, hLn, hedit])
      | star =>
          exact paper_progress_for_evaluation L R hL hR y hsuby hstep
end Nock.Verb
