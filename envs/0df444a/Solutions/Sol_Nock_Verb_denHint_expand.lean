-- Prove2me | solution 1 for Nock.Verb.denHint_expand
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:22:51.561857+00:00
-- url     : https://prove2.me/submissions/26428821-be40-4d17-8bfa-729b751b353c

module
public import Definitions.Def_LeanPool_PureNock_Agreement
public import Definitions.Def_LeanPool_PureNock_Trace
public import Definitions.Def_LeanPool_PureNock_PaperReference
public import Mathlib.Tactic.IntervalCases
public import Definitions.Def_LeanPool_PureNock_PureAgreement
public import Theorems.Thm_Nock_Verb_Den_star_terminal
public import Theorems.Thm_Nock_Verb_EvN_op11_dyn
public import Theorems.Thm_Nock_Verb_EvN_op11_static
public import Theorems.Thm_Nock_Verb_EvN_macro_dyn

set_option autoImplicit true
@[expose] public section
public section
open Nock
open Nock.Verb
open Noun
namespace Nock.Verb
theorem _root_.solution {sub e x} (he : hintExpand sub = some e) : Den sub x ↔ Den e x := by
  unfold hintExpand at he
  split at he
  · rename_i n1 ra n2
    split at he
    · rename_i hguard
      simp only [Bool.and_eq_true] at hguard
      obtain ⟨⟨h1, hra⟩, hn2⟩ := hguard
      have hraN : ra = Action.null := by cases ra <;> simp_all only [Action.isNull, reduceCtorEq]
      subst hraN
      have hform : isTerminal (Verb.node .null (.leaf 11) n2) = true := by
        simp [isTerminal, Action.isNull, hn2]
      split at he
      · -- dynamic hint  n2 = [[tb clue] body]
        rename_i rn2 innerA tb clue body
        obtain rfl := Option.some.inj he
        simp only [isTerminal, Bool.and_eq_true] at hn2
        obtain ⟨⟨_, ⟨_, hclue⟩⟩, hbody⟩ := hn2
        have hE : isTerminal (Verb.node .null (.leaf 8)
            (.node .null clue (.node .null (.leaf 7)
              (.node .null (.node .null (.leaf 0) (.leaf 3)) body)))) = true := by
          simp [isTerminal, Action.isNull, hclue, hbody]
        rw [Den_star_terminal h1 hform, Den_star_terminal h1 hE]
        simp only [noun]
        rw [EvN_op11_dyn, EvN_macro_dyn]
      · -- static hint  n2 = [t body]  (t an atom)
        rename_i rn2 t body
        obtain rfl := Option.some.inj he
        simp only [isTerminal, Bool.and_eq_true] at hn2
        obtain ⟨_, hbody⟩ := hn2
        rw [Den_star_terminal h1 hform, Den_star_terminal h1 hbody]
        simp only [noun]
        rw [EvN_op11_static]
      · simp at he
    · simp at he
  · simp at he
end Nock.Verb
