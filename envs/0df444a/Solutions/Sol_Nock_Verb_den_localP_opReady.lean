-- Prove2me | solution 1 for Nock.Verb.den_localP_opReady
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:23:37.605069+00:00
-- url     : https://prove2.me/submissions/7d247d2c-c19d-413e-93f6-af98d98de005

module
public import Definitions.Def_LeanPool_PureNock_Agreement
public import Definitions.Def_LeanPool_PureNock_Trace
public import Definitions.Def_LeanPool_PureNock_PaperReference
public import Mathlib.Tactic.IntervalCases
public import Definitions.Def_LeanPool_PureNock_PureAgreement
public import Theorems.Thm_Nock_Verb_DenP_slot
public import Theorems.Thm_Nock_Verb_DenP_equal
public import Theorems.Thm_Nock_Verb_DenP_minus
public import Theorems.Thm_Nock_Verb_DenP_edit_node
public import Theorems.Thm_Nock_Verb_DenP_terminal_iff
public import Theorems.Thm_Nock_Verb_DenP_ofNoun_iff

set_option autoImplicit true
@[expose] public section
public section
open Nock
open Nock.Verb
open Noun
namespace Nock.Verb
theorem _root_.solution {sub r₀ x} (hor : opReady sub = true) (hr : reduce sub = some r₀) :
    (DenP sub x ↔ DenP r₀ x) := by
  cases sub with
  | leaf => simp [opReady] at hor
  | node a l r =>
    simp only [opReady, Bool.and_eq_true] at hor
    obtain ⟨⟨hao, htl⟩, htr⟩ := hor
    have hDl : ∀ v, DenP l v ↔ v = l.noun := fun v => DenP_terminal_iff htl
    have hDr : ∀ v, DenP r v ↔ v = r.noun := fun v => DenP_terminal_iff htr
    have atominj : ∀ {ax' ax : Nat}, DenP l (.atom ax') → l.noun = .atom ax → ax' = ax := by
      intro ax' ax hd he; have := (hDl _).1 hd; rw [he] at this; exact Noun.atom.inj this
    cases a with
    | null => simp [Action.isOperator] at hao
    | star => simp [Action.isOperator] at hao
    | wut => simp [reduce] at hr
    | equal =>
        rw [reduce] at hr; obtain rfl := Option.some.inj hr
        rw [DenP_equal, DenP_ofNoun_iff]
        constructor
        · rintro ⟨va, vb, hva, hvb, rfl⟩; rw [(hDl va).1 hva, (hDr vb).1 hvb]
        · rintro rfl; exact ⟨l.noun, r.noun, (hDl _).2 rfl, (hDr _).2 rfl, rfl⟩
    | slot =>
        rw [reduce] at hr
        rw [DenP_slot]
        split at hr
        · rename_i ax heq
          rw [Option.map_eq_some_iff] at hr
          obtain ⟨sr, hslot, rfl⟩ := hr
          rw [DenP_ofNoun_iff]
          constructor
          · rintro ⟨ax', b, hax', hb, hs⟩
            obtain rfl := atominj hax' heq
            rw [(hDr _).1 hb] at hs; rw [hs] at hslot; exact (Option.some.inj hslot)
          · rintro rfl
            exact ⟨ax, r.noun, (hDl _).2 heq.symm, (hDr _).2 rfl, hslot⟩
        · simp at hr
    | minus =>
        rw [reduce] at hr
        rw [DenP_minus]
        split at hr
        · rename_i heq
          obtain rfl := Option.some.inj hr
          rw [DenP_ofNoun_iff]
          constructor
          · rintro ⟨b, hb, hor2⟩
            rcases hor2 with ⟨_, hx⟩ | ⟨h4, _⟩
            · rw [(hDr _).1 hb] at hx; exact hx
            · exact absurd (atominj h4 heq) (by decide)
          · rintro rfl; exact ⟨r.noun, (hDr _).2 rfl, Or.inl ⟨(hDl _).2 heq.symm, rfl⟩⟩
        · rename_i heq
          rw [Option.map_eq_some_iff] at hr
          obtain ⟨sr, hlus, rfl⟩ := hr
          rw [DenP_ofNoun_iff]
          constructor
          · rintro ⟨b, hb, hor2⟩
            rcases hor2 with ⟨h3, _⟩ | ⟨_, hlus2⟩
            · exact absurd (atominj h3 heq) (by decide)
            · rw [(hDr _).1 hb] at hlus2; rw [hlus2] at hlus; exact (Option.some.inj hlus)
          · rintro rfl; exact ⟨r.noun, (hDr _).2 rfl, Or.inr ⟨(hDl _).2 heq.symm, hlus⟩⟩
        · simp at hr
    | edit =>
        cases hln : l.noun with
        | cell => simp [reduce, hln] at hr
        | atom ax =>
            cases hr2 : r with
            | leaf => simp [reduce, hln, hr2] at hr
            | node b nw od =>
                simp only [reduce, hln, hr2, Option.map_eq_some_iff] at hr
                obtain ⟨er, hedit, rfl⟩ := hr
                have htr2 : isTerminal (.node b nw od) = true := hr2 ▸ htr
                simp only [isTerminal, Bool.and_eq_true] at htr2
                obtain ⟨⟨_, htnw⟩, htod⟩ := htr2
                have hDnw : ∀ v, DenP nw v ↔ v = nw.noun := fun v => DenP_terminal_iff htnw
                have hDod : ∀ v, DenP od v ↔ v = od.noun := fun v => DenP_terminal_iff htod
                rw [DenP_edit_node, DenP_ofNoun_iff]
                constructor
                · rintro ⟨ax', n, o, hax', hn, ho, he⟩
                  obtain rfl := atominj hax' hln
                  rw [(hDnw _).1 hn, (hDod _).1 ho] at he
                  rw [he] at hedit; exact (Option.some.inj hedit)
                · rintro rfl
                  exact ⟨ax, nw.noun, od.noun, (hDl _).2 hln.symm, (hDnw _).2 rfl, (hDod _).2 rfl,
                    hedit⟩
end Nock.Verb
