-- Prove2me | solution 1 for Nock.Verb.run_completeN
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:29:09.840942+00:00
-- url     : https://prove2.me/submissions/26c3b9f4-cdc0-49f1-9dbd-2b5fa5edd0e4

module
public import Definitions.Def_LeanPool_PureNock_PureComplete
public import Mathlib.Tactic.IntervalCases
public import Definitions.Def_LeanPool_PureNock_PureCompleteHint
public import Theorems.Thm_Nock_Verb_nextHint_none_of_terminal
public import Theorems.Thm_Nock_Verb_den_terminal_val
public import Theorems.Thm_Nock_Verb_vcostN_mono
public import Theorems.Thm_Nock_Verb_cost_stepN
public import Theorems.Thm_Nock_Verb_progressN
public import Theorems.Thm_Nock_Verb_denHint_step
public import Theorems.Thm_Nock_Verb_den_mono
public import Theorems.Thm_Nock_Verb_editOk_nextHint


set_option autoImplicit true
@[expose] public section
public section
open Nock
open Nock.Verb
open Noun
namespace Nock.Verb
theorem _root_.solution {v : Verb} {x : Noun} (hok : editOk v = true) (hv : Den v x) :
    ∃ N, runHint N v = some x := by
  suffices aux : ∀ (bound F : Nat) (v : Verb) (x : Noun),
      editOk v = true → den F v = some x → vcostN F v < bound → ∃ N, runHint N v = some x by
    obtain ⟨F, hF⟩ := hv
    exact aux (vcostN F v + 1) F v x hok hF (Nat.lt_succ_self _)
  intro bound
  induction bound with
  | zero => intro F v x _ _ hlt; omega
  | succ bound ih =>
      intro F v x hok hF hlt
      by_cases hterm : isTerminal v = true
      · refine ⟨1, ?_⟩
        have hx : x = v.noun := den_terminal_val hterm hF
        subst hx
        simp only [runHint, nextHint_none_of_terminal hterm, result, hterm, ite_true]
      · have hntf : isTerminal v = false := by
          cases hh : isTerminal v with
          | true => exact absurd hh hterm
          | false => rfl
        obtain ⟨v', hnext⟩ := progressN hok ⟨F, hF⟩ hntf
        obtain ⟨F', hF'⟩ := (denHint_step hok hnext).1 ⟨F, hF⟩
        have hokv' : editOk v' = true := editOk_nextHint hnext hok
        have hGv : den (max F F') v = some x := den_mono (Nat.le_max_left _ _) hF
        have hGv' : den (max F F') v' = some x := den_mono (Nat.le_max_right _ _) hF'
        have hvcv : vcostN (max F F') v = vcostN F v := vcostN_mono (Nat.le_max_left _ _) hok hF
        have hvcv' : vcostN (max F F') v' = vcostN F' v' := vcostN_mono (Nat.le_max_right _ _) hokv'
          hF'
        have hdec : vcostN (max F F') v' < vcostN (max F F') v := cost_stepN hok hGv hGv' hnext
        have hlt' : vcostN F' v' < bound := by
          rw [hvcv'] at hdec; rw [hvcv] at hdec; omega
        obtain ⟨N, hN⟩ := ih F' v' x hokv' hF' hlt'
        exact ⟨N + 1, by simp only [runHint, hnext]; exact hN⟩
end Nock.Verb
