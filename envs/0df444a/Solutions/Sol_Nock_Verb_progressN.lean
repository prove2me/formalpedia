-- Prove2me | solution 1 for Nock.Verb.progressN
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:27:02.403623+00:00
-- url     : https://prove2.me/submissions/36069325-e35e-4d7f-b9c8-0e9659fcbf57

module
public import Definitions.Def_LeanPool_PureNock_PureComplete
public import Mathlib.Tactic.IntervalCases
public import Definitions.Def_LeanPool_PureNock_PureCompleteHint
public import Theorems.Thm_Nock_Verb_evalN_atom_none
public import Theorems.Thm_Nock_Verb_evalN_op_ge12_none
public import Theorems.Thm_Nock_Verb_inDomainHint_of_inDomain
public import Theorems.Thm_Nock_Verb_Den_subnode
public import Theorems.Thm_Nock_Verb_Den_edit_leaf
public import Theorems.Thm_Nock_Verb_Den_edit_node
public import Theorems.Thm_Nock_Verb_Den_minus
public import Theorems.Thm_Nock_Verb_Den_slot
public import Theorems.Thm_Nock_Verb_Den_star
public import Theorems.Thm_Nock_Verb_Den_terminal_iff
public import Theorems.Thm_Nock_Verb_Den_wut
public import Theorems.Thm_Nock_Verb_EvN_op10
public import Theorems.Thm_Nock_Verb_EvN_op2
public import Theorems.Thm_Nock_Verb_EvN_op5
public import Theorems.Thm_Nock_Verb_EvN_op6
public import Theorems.Thm_Nock_Verb_EvN_op7
public import Theorems.Thm_Nock_Verb_EvN_op8
public import Theorems.Thm_Nock_Verb_EvN_op9
public import Theorems.Thm_Nock_Verb_children_terminal_of_getIndex
public import Theorems.Thm_Nock_Verb_getIndex_eq_some_iff
public import Theorems.Thm_Nock_Verb_getIndex_none_iff_terminal
public import Theorems.Thm_Nock_Verb_inDomain_star_of
public import Theorems.Thm_Nock_Verb_map_some_of_getIndex
public import Theorems.Thm_Nock_Verb_nextHint_eq_some_iff


set_option autoImplicit true
@[expose] public section
public section
open Nock
open Nock.Verb
open Noun
namespace Nock.Verb
theorem _root_.solution {v : Verb} {x : Noun} (hwf : editOk v = true) (hd : Den v x)
    (hnt : isTerminal v = false) : ∃ v', nextHint v = some v' := by
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
      obtain ⟨y, hsuby⟩ := Den_subnode hwf hd hmap
      have hstepN : inDomainHint (Verb.node a L R) = true →
          (redexHint (Verb.node a L R)).isSome = true → ∃ v', nextHint v = some v' := by
        intro hdom hred
        cases hrr : redexHint (Verb.node a L R) with
        | none => rw [hrr] at hred; simp at hred
        | some rr =>
            exact ⟨replaceAt i v rr,
              nextHint_eq_some_iff.2 ⟨i, Verb.node a L R, rr, hmax, hmap, hdom, hrr, rfl⟩⟩
      cases a with
      | null => simp [isPending, Action.isNull] at hsubp
      | wut => exact absurd hsuby Den_wut
      | equal =>
          have hdom : inDomain (Verb.node .equal L R) = true := by
            simp [inDomain, inOpcodeDomain, opReady, Action.isOperator, hL, hR]
          exact hstepN (inDomainHint_of_inDomain hdom) (by simp [redexHint, hintExpand, reduce])
      | slot =>
          obtain ⟨ax, b, hLax, hRb, hslot⟩ := Den_slot.1 hsuby
          have hLn : L.noun = Noun.atom ax := ((Den_terminal_iff hL).1 hLax).symm
          have hbR : b = R.noun := (Den_terminal_iff hR).1 hRb
          subst hbR
          have hdom : inDomain (Verb.node .slot L R) = true := by
            simp [inDomain, inOpcodeDomain, opReady, Action.isOperator, hL, hR]
          exact hstepN (inDomainHint_of_inDomain hdom)
            (by simp [redexHint, hintExpand, reduce, hLn, hslot])
      | minus =>
          obtain ⟨b, hRb, hcase⟩ := Den_minus.1 hsuby
          have hbR : b = R.noun := (Den_terminal_iff hR).1 hRb
          subst hbR
          have hdom : inDomain (Verb.node .minus L R) = true := by
            simp [inDomain, inOpcodeDomain, opReady, Action.isOperator, hL, hR]
          rcases hcase with ⟨hL3, _⟩ | ⟨hL4, hlus⟩
          · have hLn : L.noun = Noun.atom 3 := ((Den_terminal_iff hL).1 hL3).symm
            exact hstepN (inDomainHint_of_inDomain hdom)
              (by simp [redexHint, hintExpand, reduce, hLn])
          · have hLn : L.noun = Noun.atom 4 := ((Den_terminal_iff hL).1 hL4).symm
            exact hstepN (inDomainHint_of_inDomain hdom)
              (by simp [redexHint, hintExpand, reduce, hLn, hlus])
      | edit =>
          cases R with
          | leaf k => exact absurd hsuby Den_edit_leaf
          | node rb nw od =>
              simp only [isTerminal, Bool.and_eq_true] at hR
              obtain ⟨⟨hrb, hnw⟩, hod⟩ := hR
              obtain ⟨ax, n, o, hLax, hnwn, hodo, hedit⟩ := Den_edit_node.1 hsuby
              have hLn : L.noun = Noun.atom ax := ((Den_terminal_iff hL).1 hLax).symm
              have hnwn' : n = nw.noun := (Den_terminal_iff hnw).1 hnwn
              have hodo' : o = od.noun := (Den_terminal_iff hod).1 hodo
              subst hnwn'; subst hodo'
              have hdom : inDomain (Verb.node .edit L (Verb.node rb nw od)) = true := by
                simp [inDomain, inOpcodeDomain, opReady, Action.isOperator, hL,
                      isTerminal, hrb, hnw, hod]
              exact hstepN (inDomainHint_of_inDomain hdom)
                (by simp [redexHint, hintExpand, reduce, hLn, hedit])
      | star =>
          obtain ⟨a', b', hLa, hRb, hev⟩ := Den_star.1 hsuby
          have haL : a' = L.noun := (Den_terminal_iff hL).1 hLa
          have hbR : b' = R.noun := (Den_terminal_iff hR).1 hRb
          subst haL; subst hbR
          cases R with
          | leaf k =>
              exfalso; obtain ⟨f, hf⟩ := hev
              simp [noun, evalN_atom_none] at hf
          | node rb fi n2 =>
              simp only [isTerminal, Bool.and_eq_true] at hR
              obtain ⟨⟨hrb, hfi_t⟩, hn2⟩ := hR
              simp only [noun] at hev
              cases fi with
              | node bi ic id =>
                  exact hstepN (inDomainHint_of_inDomain (inDomain_star_of hL hrb hfi_t hn2 rfl))
                    (by simp [redexHint, hintExpand, reduce, redex])
              | leaf op =>
                  simp only [noun] at hev
                  have hop : op < 12 := by
                    rcases Nat.lt_or_ge op 12 with h | h
                    · exact h
                    · exfalso
                      obtain ⟨f, hf⟩ := hev
                      rw [evalN_op_ge12_none f L.noun n2.noun op h] at hf
                      exact absurd hf (by simp)
                  interval_cases op
                  · exact hstepN (inDomainHint_of_inDomain (inDomain_star_of hL hrb rfl hn2 (by
                    decide)))
                      (by simp [redexHint, hintExpand, reduce, redex])
                  · exact hstepN (inDomainHint_of_inDomain (inDomain_star_of hL hrb rfl hn2 (by
                    decide)))
                      (by simp [redexHint, hintExpand, reduce, redex])
                  · obtain ⟨hb, hc, _, _, hn2eq, _⟩ := EvN_op2.1 hev
                    cases n2 with
                    | leaf k => rw [noun] at hn2eq; exact absurd hn2eq (by simp)
                    | node b2 c2 d2 =>
                        exact hstepN (inDomainHint_of_inDomain (inDomain_star_of hL hrb rfl hn2 (by
                          decide)))
                          (by simp [redexHint, hintExpand, reduce, redex])
                  · exact hstepN (inDomainHint_of_inDomain (inDomain_star_of hL hrb rfl hn2 (by
                    decide)))
                      (by simp [redexHint, hintExpand, reduce, redex])
                  · exact hstepN (inDomainHint_of_inDomain (inDomain_star_of hL hrb rfl hn2 (by
                    decide)))
                      (by simp [redexHint, hintExpand, reduce, redex])
                  · obtain ⟨hb, hc, _, _, hn2eq, _⟩ := EvN_op5.1 hev
                    cases n2 with
                    | leaf k => rw [noun] at hn2eq; exact absurd hn2eq (by simp)
                    | node b2 c2 d2 =>
                        exact hstepN (inDomainHint_of_inDomain (inDomain_star_of hL hrb rfl hn2 (by
                          decide)))
                          (by simp [redexHint, hintExpand, reduce, redex])
                  · obtain ⟨b, c, d, cv, hn2eq, _⟩ := EvN_op6.1 hev
                    cases n2 with
                    | leaf k => rw [noun] at hn2eq; exact absurd hn2eq (by simp)
                    | node b2 c2 d2 =>
                        exact hstepN (inDomainHint_of_inDomain (inDomain_star_of hL hrb rfl hn2 (by
                          decide)))
                          (by simp [redexHint, hintExpand, reduce, redex])
                  · obtain ⟨hb, hc, _, hn2eq, _⟩ := EvN_op7.1 hev
                    cases n2 with
                    | leaf k => rw [noun] at hn2eq; exact absurd hn2eq (by simp)
                    | node b2 c2 d2 =>
                        exact hstepN (inDomainHint_of_inDomain (inDomain_star_of hL hrb rfl hn2 (by
                          decide)))
                          (by simp [redexHint, hintExpand, reduce, redex])
                  · obtain ⟨hb, hc, _, hn2eq, _⟩ := EvN_op8.1 hev
                    cases n2 with
                    | leaf k => rw [noun] at hn2eq; exact absurd hn2eq (by simp)
                    | node b2 c2 d2 =>
                        exact hstepN (inDomainHint_of_inDomain (inDomain_star_of hL hrb rfl hn2 (by
                          decide)))
                          (by simp [redexHint, hintExpand, reduce, redex])
                  · obtain ⟨ax, c, _, _, hn2eq, _⟩ := EvN_op9.1 hev
                    cases n2 with
                    | leaf k => rw [noun] at hn2eq; exact absurd hn2eq (by simp)
                    | node b2 c2 d2 =>
                        exact hstepN (inDomainHint_of_inDomain (inDomain_star_of hL hrb rfl hn2 (by
                          decide)))
                          (by simp [redexHint, hintExpand, reduce, redex])
                  · obtain ⟨ax, c, d, new, old, hn2eq, _⟩ := EvN_op10.1 hev
                    cases n2 with
                    | leaf k => rw [noun] at hn2eq; exact absurd hn2eq (by simp)
                    | node b2 hdd d2 =>
                        rw [noun] at hn2eq
                        have hhd : hdd.noun = Noun.cell (Noun.atom ax) c := (Noun.cell.inj hn2eq).1
                        cases hdd with
                        | leaf k => rw [noun] at hhd; exact absurd hhd (by simp)
                        | node bhd axv cc =>
                            exact hstepN (inDomainHint_of_inDomain (inDomain_star_of hL hrb rfl hn2
                              (by decide)))
                              (by simp [redexHint, hintExpand, reduce, redex])
                  · -- OP₁₁ hint redex
                    cases n2 with
                    | leaf k =>
                        exfalso; obtain ⟨f, hf⟩ := hev
                        simp only [noun] at hf
                        cases f with
                        | zero => simp [evalN] at hf
                        | succ ff => simp [evalN] at hf
                    | node rn2 h2 b2 =>
                        have hdomN : inDomainHint
                            (Verb.node .star L (Verb.node rb (Verb.leaf 11) (Verb.node rn2 h2 b2)))
                              = true := by
                          rw [inDomainHint]
                          have hhr : isHintRedex
                              (Verb.node .star L (Verb.node rb (Verb.leaf 11) (Verb.node rn2 h2
                                b2))) = true := by
                            simp [isHintRedex, hL, hrb, hn2]
                          rw [hhr]; simp
                        have hredN : (redexHint
                            (Verb.node .star L (Verb.node rb (Verb.leaf 11) (Verb.node rn2 h2
                              b2)))).isSome = true := by
                          cases h2 <;> simp [redexHint, hintExpand, hL, hrb, hn2]
                        exact hstepN hdomN hredN
end Nock.Verb
