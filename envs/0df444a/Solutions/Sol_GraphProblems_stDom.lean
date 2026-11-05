-- Prove2me | solution 1 for GraphProblems.stDom
-- status  : ACCEPTED   (prove)
-- author  : @nonlocally
-- created : 2026-11-04T23:27:48.429323+00:00
-- url     : https://prove2.me/submissions/8bf3a2df-4a66-421a-8373-38153d3b47e0

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GraphProblems_Interfaces
import Definitions.Def_GraphProblems_Read
import Definitions.Def_GraphProblems_Sets
set_option autoImplicit false
section
section
open GraphProblems
open Groundwork Groundwork.Prog CountKSat Finset
open Sets

namespace StDomProof

/-- In a list of rows of length `n`, entry `i * n + j` is entry `j` of row `i`. -/
private theorem getD_flatMap {α β : Type} (f : α → List β) (n : ℕ) (d : β) {j : ℕ} (hj : j < n) :
    ∀ (L : List α) (_ : ∀ a ∈ L, (f a).length = n) (i : ℕ),
      (L.flatMap f).getD (i * n + j) d = (L[i]?.map fun a => (f a).getD j d).getD d
  | [], _, i => by simp
  | a :: L, hL, 0 => by
    have ha : (f a).length = n := hL a (by simp)
    rw [List.flatMap_cons, zero_mul, zero_add, List.getD_append _ _ _ _ (by omega)]
    simp
  | a :: L, hL, i + 1 => by
    have ha : (f a).length = n := hL a (by simp)
    rw [List.flatMap_cons, List.getD_append_right _ _ _ _ (by rw [ha]; nlinarith), ha,
      show (i + 1) * n + j - n = i * n + j by rw [add_mul, one_mul]; omega,
      getD_flatMap f n d hj L (fun b hb => hL b (by simp [hb])) i]
    simp

/-- The Boolean matrix entry records adjacency. -/
private theorem stAdj : StAdj := fun n G u v => by
  classical
  rw [adjB, matrix, getD_flatMap _ n false v.2 _ (by simp)]
  simp

variable {n : ℕ}

private theorem mem_trueSet {a : Fin n → Bool} {i : Fin n} : i ∈ trueSet a ↔ a i = true := by
  simp [trueSet]

/-- Satisfying assignments with `s` true variables biject with satisfying sets of cardinality `s`. -/
private theorem cntS_eq_ncard (s : ℕ) (ψ : Fml) (P : Finset (Fin n) → Prop)
    (h : ∀ a : Fin n → Bool, (∀ C ∈ ψ, ∃ l ∈ C, CountKSat.ext a l.1 = l.2) ↔ P (trueSet a)) :
    cntS n s ψ = {S : Finset (Fin n) | P S ∧ S.card = s}.ncard := by
  classical
  have h1 : {S : Finset (Fin n) | P S ∧ S.card = s} =
      ↑(univ.filter fun S : Finset (Fin n) => P S ∧ S.card = s) := by
    ext S
    simp
  rw [h1, Set.ncard_coe_finset, cntS]
  refine card_nbij' trueSet (fun S i => decide (i ∈ S)) ?_ ?_ ?_ ?_
  · intro a ha
    simp only [coe_filter, mem_univ, true_and, Set.mem_ofPred_eq] at ha ⊢
    exact ⟨(h a).1 ha.1, ha.2⟩
  · intro S hS
    have hS' : trueSet (fun i => decide (i ∈ S)) = S := by
      ext i
      simp [trueSet]
    simp only [coe_filter, mem_univ, true_and, Set.mem_ofPred_eq] at hS ⊢
    refine ⟨(h _).2 (by rw [hS']; exact hS.1), ?_⟩
    have := hS.2
    rw [← hS'] at this
    exact this
  · intro a _
    funext i
    simp [trueSet]
  · intro S _
    ext i
    simp [trueSet]

/-- An assignment satisfies the Dominating Set formula exactly when its true set dominates. -/
private theorem sat_domF (G : SimpleGraph (Fin n)) (a : Fin n → Bool) :
    (∀ C ∈ domF n (matrix G), ∃ l ∈ C, CountKSat.ext a l.1 = l.2) ↔ IsDominating G (trueSet a) := by
  constructor
  · intro H v
    obtain ⟨l, hl, hal⟩ := H
      (posC (v.val :: (List.range n).filter fun u => u != v.val && adjB n (matrix G) v.val u))
      (List.mem_map.2 ⟨_, List.mem_map.2 ⟨v.val, List.mem_range.2 v.2, rfl⟩, rfl⟩)
    obtain ⟨u, hu, rfl⟩ := List.mem_map.1 hl
    rcases List.mem_cons.1 hu with rfl | hu
    · left
      simpa [CountKSat.ext, v.2, mem_trueSet] using hal
    · right
      obtain ⟨hun, huv⟩ := List.mem_filter.1 hu
      rw [List.mem_range] at hun
      simp only [Bool.and_eq_true, bne_iff_ne] at huv
      refine ⟨⟨u, hun⟩, ?_, (stAdj n G v ⟨u, hun⟩).1 huv.2⟩
      simpa [CountKSat.ext, hun, mem_trueSet] using hal
  · intro H C hC
    obtain ⟨D, hD, rfl⟩ := List.mem_map.1 hC
    obtain ⟨v, hv, rfl⟩ := List.mem_map.1 hD
    rw [List.mem_range] at hv
    rcases H ⟨v, hv⟩ with h | ⟨u, hu, huv⟩
    · refine ⟨(v, true), List.mem_map.2 ⟨v, by simp, rfl⟩, ?_⟩
      simpa [CountKSat.ext, hv, mem_trueSet] using h
    · refine ⟨(u.val, true), List.mem_map.2
        ⟨u.val, List.mem_cons_of_mem _ (List.mem_filter.2 ⟨List.mem_range.2 u.2, ?_⟩), rfl⟩, ?_⟩
      · simp only [Bool.and_eq_true, bne_iff_ne]
        exact ⟨fun e => huv.ne (Fin.ext e.symm), (stAdj n G ⟨v, hv⟩ u).2 huv⟩
      · simpa [CountKSat.ext, u.2, mem_trueSet] using hu

end StDomProof

theorem solution : StDom := fun _ G s =>
  StDomProof.cntS_eq_ncard s _ (fun S => IsDominating G S) (StDomProof.sat_domF G)
