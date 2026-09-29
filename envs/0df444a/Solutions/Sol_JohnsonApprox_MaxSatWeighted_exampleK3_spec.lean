-- Prove2me | solution 1 for JohnsonApprox.MaxSatWeighted.exampleK3_spec
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-28T20:38:14.585989+00:00
-- url     : https://prove2.me/submissions/5f46d124-fa04-4d43-8c3b-ebb8c8fcb2d6

import Mathlib
import Definitions.Def_JohnsonApprox_Shared_Problem
import Definitions.Def_JohnsonApprox_MaxSatWeighted_B2
import Definitions.Def_JohnsonApprox_MaxSatWeighted_ExampleK3



namespace JohnsonApprox.MaxSatWeighted
open Finset Shared

def c1 : Clause := {lit 1, lit 2, lit 3}
def c2 : Clause := {nlit 1, lit 4, lit 5}
def c3 : Clause := {lit 1, nlit 2, lit 3}
def c4 : Clause := {nlit 1, lit 6, lit 7}
def c5 : Clause := {lit 1, lit 2, nlit 3}
def c6 : Clause := {nlit 1, lit 8, lit 9}
def c7 : Clause := {lit 1, nlit 2, nlit 3}
def c8 : Clause := {nlit 1, lit 10, lit 11}

lemma ex_eq : exampleK3 = {c1, c2, c3, c4, c5, c6, c7, c8} := rfl

lemma update_of_le (σ : State) (y : Literal) (h : σ.weight (σ.YF y) ≤ σ.weight (σ.YT y)) :
    σ.update y = ⟨σ.SUB ∪ σ.YT y, σ.LEFT \ σ.YT y, insert y σ.TRUE, insert y.var σ.decided,
      doubleOn σ.w (σ.YF y)⟩ := by
  unfold State.update; rw [if_pos h]

def w0 : Clause → ℚ := fun C => 1 / 2 ^ C.card
def σ0 : State := init exampleK3
def σ1 : State := ⟨{c1, c5}, {c2, c3, c4, c6, c7, c8}, {lit 2}, {2}, doubleOn w0 {c3, c7}⟩
def σ2 : State := ⟨{c1, c5, c3}, {c2, c4, c6, c7, c8}, {lit 3, lit 2}, {3, 2},
  doubleOn (doubleOn w0 {c3, c7}) {c7}⟩
def σ3 : State := ⟨{c1, c5, c3, c2, c4, c6, c8}, {c7}, {nlit 1, lit 3, lit 2}, {1, 3, 2},
  doubleOn (doubleOn (doubleOn w0 {c3, c7}) {c7}) {c7}⟩

lemma yt1 : σ0.YT (lit 2) = {c1, c5} := by decide
lemma yf1 : σ0.YF (lit 2) = {c3, c7} := by decide

lemma yt2 : σ1.YT (lit 3) = {c3} := by decide
lemma yf2 : σ1.YF (lit 3) = {c7} := by decide
lemma yt3 : σ2.YT (nlit 1) = {c2, c4, c6, c8} := by decide
lemma yf3 : σ2.YF (nlit 1) = {c7} := by decide

lemma cards : c1.card = 3 ∧ c2.card = 3 ∧ c3.card = 3 ∧ c4.card = 3 ∧ c5.card = 3 ∧
    c6.card = 3 ∧ c7.card = 3 ∧ c8.card = 3 := by decide

lemma step1 : StepWith σ0 (lit 2) σ1 := by
  have hle : σ0.weight (σ0.YF (lit 2)) ≤ σ0.weight (σ0.YT (lit 2)) := by
    rw [yf1, yt1]; unfold State.weight
    rw [sum_pair (by decide), sum_pair (by decide)]
    simp only [σ0, init, cards]; norm_num
  refine ⟨by unfold Halts State.inLIT σ0 init; decide, by unfold State.inLIT σ0 init; decide,
    by unfold σ0 init; decide, ?_⟩
  rw [update_of_le σ0 (lit 2) hle, yt1, yf1]
  simp only [σ1, State.mk.injEq]
  refine ⟨by decide, by decide, by decide, by decide, by first | rfl | trivial⟩

lemma step2 : StepWith σ1 (lit 3) σ2 := by
  have hle : σ1.weight (σ1.YF (lit 3)) ≤ σ1.weight (σ1.YT (lit 3)) := by
    rw [yf2, yt2]; unfold State.weight
    simp only [sum_singleton, σ1, doubleOn, w0, cards]
    rw [if_pos (by decide), if_pos (by decide)]
  refine ⟨by unfold Halts State.inLIT σ1; decide, by unfold State.inLIT σ1; decide,
    by unfold σ1; decide, ?_⟩
  rw [update_of_le σ1 (lit 3) hle, yt2, yf2]
  simp only [σ1, σ2, State.mk.injEq]
  refine ⟨by decide, by decide, by decide, by decide, by first | rfl | trivial⟩

lemma step3 : StepWith σ2 (nlit 1) σ3 := by
  have hle : σ2.weight (σ2.YF (nlit 1)) ≤ σ2.weight (σ2.YT (nlit 1)) := by
    rw [yf3, yt3]; unfold State.weight
    rw [sum_insert (by decide), sum_insert (by decide), sum_pair (by decide)]
    simp only [sum_singleton, σ2, doubleOn, w0, cards]
    rw [if_pos (by decide), if_pos (by decide), if_neg (by decide), if_neg (by decide),
      if_neg (by decide), if_neg (by decide), if_neg (by decide), if_neg (by decide),
      if_neg (by decide), if_neg (by decide)]
    norm_num
  refine ⟨by unfold Halts State.inLIT σ2; decide, by unfold State.inLIT σ2; decide,
    by unfold σ2; decide, ?_⟩
  rw [update_of_le σ2 (nlit 1) hle, yt3, yf3]
  simp only [σ2, σ3, State.mk.injEq]
  refine ⟨by decide, by decide, by decide, by decide, by first | rfl | trivial⟩

lemma opt_le_card (S : Finset Clause) : opt S ≤ S.card := by
  unfold opt
  apply Finset.sup'_le
  intro S' hS'
  unfold solutions at hS'
  simp only [Finset.mem_filter, Finset.mem_powerset] at hS'
  exact card_le_card hS'.1

lemma card_le_opt (S : Finset Clause) (hsat : Satisfiable S) : S.card ≤ opt S := by
  unfold opt
  exact Finset.le_sup' Finset.card (by
    unfold solutions; simp only [Finset.mem_filter, Finset.mem_powerset]
    exact ⟨subset_refl _, hsat⟩)

theorem exampleK3_core :
    Shared.InMS 3 exampleK3 ∧ Shared.opt exampleK3 = 8 ∧ ∃ X, Choosable exampleK3 X ∧ X.card = 7 := by
  have hcard : exampleK3.card = 8 := by decide
  refine ⟨?_, ?_, ?_⟩
  · intro C hC
    have : ∀ C ∈ exampleK3, 3 ≤ C.card := by decide
    exact this C hC
  · apply le_antisymm (hcard ▸ opt_le_card _)
    rw [← hcard]
    apply card_le_opt
    refine ⟨⟨{l | l.pos = true}, fun l hl hneg => ?_⟩, fun C hC => ?_⟩
    · simp only [Set.mem_setOf_eq, Literal.neg] at hl hneg
      rw [hl] at hneg; exact Bool.noConfusion hneg
    · have : ∀ C ∈ exampleK3, ∃ l ∈ C, l.pos = true := by decide
      obtain ⟨l, hl, hp⟩ := this C hC
      exact ⟨l, hl, hp⟩
  · refine ⟨σ3.SUB, ⟨σ3, ?_, ?_, rfl⟩, by decide⟩
    · exact ((Relation.ReflTransGen.refl.tail ⟨_, step1⟩).tail ⟨_, step2⟩).tail ⟨_, step3⟩
    · unfold Halts State.inLIT σ3; decide

end JohnsonApprox.MaxSatWeighted

open JohnsonApprox JohnsonApprox.MaxSatWeighted

theorem solution :
    Shared.InMS 3 exampleK3 ∧ Shared.opt exampleK3 = 8 ∧ ∃ X, Choosable exampleK3 X ∧ X.card = 7 := by
  exact exampleK3_core
