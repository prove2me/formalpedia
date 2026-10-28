-- Prove2me | solution 1 for Intersectionality.Reductive.param_continuous
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-24T07:05:26.580986+00:00
-- url     : https://prove2.me/submissions/a73da62e-556e-45b7-b80a-5b2b76499081

import Mathlib
import Definitions.Def_Intersectionality_Reductive_Setting
import Theorems.Thm_Intersectionality_Generic_lemma_1_a

open Intersectionality.Reductive

theorem solution (X : Set ℝ) (hX : X.OrdConnected) (Q : Set (↥X → ↥X))
    (hQ : Intersectionality.Generic.IsPolicyFamily Q) :
    ∀ x0 x : ↥X, Continuous (fun θ : ↥X => param Q x0 θ x) := by
  intro x0 x
  have : Nonempty ↥X := ⟨x0⟩
  have hmem : ∀ y : ↥X, param Q x0 y ∈ Q ∧ param Q x0 y x0 = y := by
    intro y
    have h : ∃ q ∈ Q, q x0 = y := hQ.rich x0 y
    unfold param Intersectionality.Generic.transport
    rw [dif_pos h]
    exact Classical.choose_spec h
  obtain ⟨hsQ, hsx⟩ := hmem x
  have heq : (fun θ : ↥X => param Q x0 θ x) = param Q x0 x := by
    funext θ
    obtain ⟨hθQ, hθx⟩ := hmem θ
    have := congrFun (hQ.comm _ hθQ _ hsQ) x0
    simp only [Function.comp] at this
    calc param Q x0 θ x = param Q x0 θ (param Q x0 x x0) := by rw [hsx]
      _ = param Q x0 x (param Q x0 θ x0) := this
      _ = param Q x0 x θ := by rw [hθx]
  rw [heq]
  exact Intersectionality.Generic.lemma_1_a X hX Q hQ _ hsQ
