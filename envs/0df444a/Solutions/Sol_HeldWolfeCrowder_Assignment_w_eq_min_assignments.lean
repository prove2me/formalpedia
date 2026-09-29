-- Prove2me | solution 1 for HeldWolfeCrowder.Assignment.w_eq_min_assignments
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-09-28T06:10:29.167754+00:00
-- url     : https://prove2.me/submissions/fc6026d2-55bc-488b-968a-aa0a72573a69

import Mathlib
import Definitions.Def_HeldWolfeCrowder_Assignment_Setting

open HeldWolfeCrowder.Assignment

theorem solution {n : ℕ} (a : Matrix (Fin n) (Fin n) ℝ) (π : Fin n → ℝ) :
    w a π = Finset.univ.inf' ⟨id, Finset.mem_univ _⟩
      (fun A : Fin n → Fin n => assignCost a A + ∑ i, π i * assignVec A i) := by
  classical
  -- the objective of an assignment `A`, rewritten
  have hobj : ∀ A : Fin n → Fin n,
      assignCost a A + ∑ i, π i * assignVec A i
        = (∑ i, π i) + ∑ r, (a (A r) r - π (A r)) := by
    intro A
    have hcount : ∀ i : Fin n, π i * ((Finset.univ.filter fun r => A r = i).card : ℝ)
        = ∑ r ∈ Finset.univ.filter (fun r => A r = i), π (A r) := by
      intro i
      have h1 : ∑ r ∈ Finset.univ.filter (fun r => A r = i), π (A r)
          = ∑ _r ∈ Finset.univ.filter (fun r => A r = i), π i :=
        Finset.sum_congr rfl fun r hr => by rw [(Finset.mem_filter.mp hr).2]
      rw [h1, Finset.sum_const, nsmul_eq_mul]
      ring
    have hpi : ∑ i, π i * ((Finset.univ.filter fun r => A r = i).card : ℝ) = ∑ r, π (A r) := by
      rw [Finset.sum_congr rfl fun i (_ : i ∈ Finset.univ) => hcount i]
      exact Finset.sum_fiberwise Finset.univ A (fun r => π (A r))
    have hvec : ∑ i, π i * assignVec A i
        = (∑ i, π i) - ∑ i, π i * ((Finset.univ.filter fun r => A r = i).card : ℝ) := by
      rw [← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [assignVec]
      ring
    have hrhs : ∑ r, (a (A r) r - π (A r)) = (∑ r, a (A r) r) - ∑ r, π (A r) :=
      Finset.sum_sub_distrib _ _
    rw [hvec, hpi, assignCost, hrhs]
    ring
  rw [w]
  refine le_antisymm ?_ ?_
  · refine Finset.le_inf' _ _ ?_
    intro A _
    rw [hobj A]
    refine add_le_add (le_refl _) (Finset.sum_le_sum fun r _ => ?_)
    exact Finset.inf'_le _ (Finset.mem_univ (A r))
  · have hch : ∀ r : Fin n, ∃ b : Fin n,
        Finset.univ.inf' (⟨r, Finset.mem_univ r⟩ : (Finset.univ : Finset (Fin n)).Nonempty)
          (fun s => a s r - π s) = a b r - π b := by
      intro r
      obtain ⟨b, _, hb⟩ := Finset.exists_mem_eq_inf'
        (⟨r, Finset.mem_univ r⟩ : (Finset.univ : Finset (Fin n)).Nonempty)
        (fun s => a s r - π s)
      exact ⟨b, hb⟩
    choose A hA using hch
    refine le_trans (Finset.inf'_le _ (Finset.mem_univ A)) ?_
    rw [hobj A]
    refine add_le_add (le_refl _) (Finset.sum_le_sum fun r _ => ?_)
    exact le_of_eq (hA r).symm
