-- Prove2me | solution 1 for Nock.Verb.runTrace_unique
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:33:36.980814+00:00
-- url     : https://prove2.me/submissions/65603e79-0670-4af9-9ad1-17638b4273e1

module
public import Definitions.Def_LeanPool_PureNock_Trace
public import Definitions.Def_LeanPool_PureNock_TraceCertificate

set_option autoImplicit true
@[expose] public section
public section
open Nock
open Nock.Verb
namespace Nock.Verb
theorem _root_.solution :
    ∀ (fuel₁ fuel₂ : Nat) (v : Verb) (T₁ T₂ : List Verb),
      runTrace fuel₁ v = some T₁ → runTrace fuel₂ v = some T₂ → T₁ = T₂ := by
  intro fuel₁
  induction fuel₁ with
  | zero => intro fuel₂ v T₁ T₂ h₁ _; simp [runTrace] at h₁
  | succ f₁ ih =>
      intro fuel₂ v T₁ T₂ h₁ h₂
      cases fuel₂ with
      | zero => simp [runTrace] at h₂
      | succ f₂ =>
          simp only [runTrace] at h₁ h₂
          cases hn : next v with
          | none =>
              rw [hn] at h₁ h₂
              simp only [Option.some.injEq] at h₁ h₂
              rw [← h₁, ← h₂]
          | some v' =>
              rw [hn] at h₁ h₂
              simp only [Option.map_eq_some_iff] at h₁ h₂
              obtain ⟨T₁', hT₁', rfl⟩ := h₁
              obtain ⟨T₂', hT₂', rfl⟩ := h₂
              rw [ih f₂ v' T₁' T₂' hT₁' hT₂']
end Nock.Verb
