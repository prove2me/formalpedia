-- Prove2me | solution 1 for Nock.Verb.run_completeP
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:27:29.42313+00:00
-- url     : https://prove2.me/submissions/2abd59c8-9dca-4027-a2dc-64ccecd9e6d3

module
public import Definitions.Def_LeanPool_PureNock_PureAgreement
public import Mathlib.Tactic.IntervalCases
public import Definitions.Def_LeanPool_PureNock_PureComplete
public import Theorems.Thm_Nock_Verb_denP_terminal_val
public import Theorems.Thm_Nock_Verb_vcost_mono
public import Theorems.Thm_Nock_Verb_cost_stepP
public import Theorems.Thm_Nock_Verb_denP_mono
public import Theorems.Thm_Nock_Verb_den_stepP
public import Theorems.Thm_Nock_Verb_editOk_next
public import Theorems.Thm_Nock_Verb_next_none_of_terminal
public import Theorems.Thm_Nock_Verb_progressP


set_option autoImplicit true
@[expose] public section
public section
open Nock
open Nock.Verb
open Noun
namespace Nock.Verb
theorem _root_.solution {v : Verb} {x : Noun} (hok : editOk v = true) (hv : DenP v x) :
    ∃ N, run N v = some x := by
  suffices aux : ∀ (bound F : Nat) (v : Verb) (x : Noun),
      editOk v = true → denP F v = some x → vcost F v < bound → ∃ N, run N v = some x by
    obtain ⟨F, hF⟩ := hv
    exact aux (vcost F v + 1) F v x hok hF (Nat.lt_succ_self _)
  intro bound
  induction bound with
  | zero => intro F v x _ _ hlt; omega
  | succ bound ih =>
      intro F v x hok hF hlt
      by_cases hterm : isTerminal v = true
      · refine ⟨1, ?_⟩
        have hx : x = v.noun := denP_terminal_val hterm hF
        subst hx
        simp only [run, next_none_of_terminal hterm, result, hterm, ite_true]
      · have hntf : isTerminal v = false := by
          cases hh : isTerminal v with
          | true => exact absurd hh hterm
          | false => rfl
        obtain ⟨v', hnext⟩ := progressP hok ⟨F, hF⟩ hntf
        obtain ⟨F', hF'⟩ := (den_stepP hok hnext).1 ⟨F, hF⟩
        have hokv' : editOk v' = true := editOk_next hnext hok
        have hGv : denP (max F F') v = some x := denP_mono (Nat.le_max_left _ _) hF
        have hGv' : denP (max F F') v' = some x := denP_mono (Nat.le_max_right _ _) hF'
        have hvcv : vcost (max F F') v = vcost F v := vcost_mono (Nat.le_max_left _ _) hok hF
        have hvcv' : vcost (max F F') v' = vcost F' v' := vcost_mono (Nat.le_max_right _ _) hokv'
          hF'
        have hdec : vcost (max F F') v' < vcost (max F F') v := cost_stepP hok hGv hGv' hnext
        have hlt' : vcost F' v' < bound := by
          rw [hvcv'] at hdec; rw [hvcv] at hdec; omega
        obtain ⟨N, hN⟩ := ih F' v' x hokv' hF' hlt'
        exact ⟨N + 1, by simp only [run, hnext]; exact hN⟩
end Nock.Verb
