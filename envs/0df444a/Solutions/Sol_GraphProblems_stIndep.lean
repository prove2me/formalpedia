-- Prove2me | solution 1 for GraphProblems.stIndep
-- status  : ACCEPTED   (prove)
-- author  : @nonlocally
-- created : 2026-11-04T23:04:14.076304+00:00
-- url     : https://prove2.me/submissions/a6266012-87dd-48cd-80f6-d3964af1bd08

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

namespace GraphProblems
namespace Sets

private theorem mem_trueSet_aux {n : ℕ} {a : Fin n → Bool} {i : Fin n} :
    i ∈ trueSet a ↔ a i = true := by
  simp [trueSet]

private theorem cntS_eq_ncard_aux {n : ℕ} (s : ℕ) (ψ : Fml) (P : Finset (Fin n) → Prop)
    (h : ∀ a : Fin n → Bool,
      (∀ C ∈ ψ, ∃ l ∈ C, CountKSat.ext a l.1 = l.2) ↔ P (trueSet a)) :
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
    have hc := hS.2
    rw [← hS'] at hc
    exact hc
  · intro a _
    funext i
    simp [trueSet]
  · intro S _
    ext i
    simp [trueSet]

private theorem mem_pairs_aux {n : ℕ} {p : ℕ × ℕ} :
    p ∈ pairs n ↔ p.1 < n ∧ p.2 < n := by
  obtain ⟨u, v⟩ := p
  simp [pairs]

private theorem sat_pairs_iff_aux {n : ℕ} (q : ℕ × ℕ → Bool) (b : Bool)
    (a : Fin n → Bool) :
    (∀ C ∈ ((pairs n).filter q).map fun p => [(p.1, b), (p.2, b)],
        ∃ l ∈ C, CountKSat.ext a l.1 = l.2) ↔
      ∀ u v : Fin n, q (u.val, v.val) = true → a u = b ∨ a v = b := by
  simp only [List.forall_mem_map, List.mem_filter, mem_pairs_aux, List.mem_cons,
    List.not_mem_nil, or_false, exists_eq_or_imp, exists_eq_left]
  constructor
  · intro H u v hq
    simpa [CountKSat.ext, u.2, v.2] using H (u.val, v.val) ⟨⟨u.2, v.2⟩, hq⟩
  · rintro H ⟨u, v⟩ ⟨⟨hu, hv⟩, hq⟩
    simpa [CountKSat.ext, hu, hv] using H ⟨u, hu⟩ ⟨v, hv⟩ hq

end Sets

private theorem getD_flatMap_aux {α β : Type} (f : α → List β) (n : ℕ) (d : β)
    {j : ℕ} (hj : j < n) :
    ∀ (L : List α) (_ : ∀ a ∈ L, (f a).length = n) (i : ℕ),
      (L.flatMap f).getD (i * n + j) d =
        (L[i]?.map fun a => (f a).getD j d).getD d
  | [], _, i => by simp
  | a :: L, hL, 0 => by
    have ha : (f a).length = n := hL a (by simp)
    rw [List.flatMap_cons, zero_mul, zero_add,
      List.getD_append _ _ _ _ (by omega)]
    simp
  | a :: L, hL, i + 1 => by
    have ha : (f a).length = n := hL a (by simp)
    rw [List.flatMap_cons, List.getD_append_right _ _ _ _ (by rw [ha]; nlinarith), ha,
      show (i + 1) * n + j - n = i * n + j by rw [add_mul, one_mul]; omega,
      getD_flatMap_aux f n d hj L (fun b hb => hL b (by simp [hb])) i]
    simp

private theorem stAdj_aux : StAdj := fun n G u v => by
  classical
  rw [adjB, matrix, getD_flatMap_aux _ n false v.2 _ (by simp)]
  simp

namespace Sets

private theorem sat_indepF_aux {n : ℕ} (G : SimpleGraph (Fin n)) (a : Fin n → Bool) :
    (∀ C ∈ indepF n (matrix G), ∃ l ∈ C, CountKSat.ext a l.1 = l.2) ↔
      G.IsIndepSet (trueSet a : Set (Fin n)) := by
  rw [indepF, sat_pairs_iff_aux]
  constructor
  · intro H u hu v hv _ huv
    have ha := H u v ((stAdj_aux n G u v).2 huv)
    rw [mem_coe, mem_trueSet_aux] at hu hv
    simp [hu, hv] at ha
  · intro H u v huv
    have huv' := (stAdj_aux n G u v).1 huv
    by_contra hc
    simp only [not_or, Bool.not_eq_false] at hc
    exact H (mem_coe.2 (mem_trueSet_aux.2 hc.1))
      (mem_coe.2 (mem_trueSet_aux.2 hc.2)) huv'.ne huv'

end Sets
end GraphProblems

theorem solution : StIndep := fun n G s => by
  rw [GraphProblems.Sets.cntS_eq_ncard_aux s _
    (fun S => G.IsIndepSet (S : Set (Fin n))) (GraphProblems.Sets.sat_indepF_aux G),
    numIndepSets]
  congr 1
  ext S
  exact (G.isNIndepSet_iff s S).symm
