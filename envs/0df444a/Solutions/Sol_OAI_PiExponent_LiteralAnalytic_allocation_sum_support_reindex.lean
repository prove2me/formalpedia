-- Prove2me | solution 1 for OAI.PiExponent.LiteralAnalytic.allocation_sum_support_reindex
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-24T07:08:46.38623+00:00
-- url     : https://prove2.me/submissions/1f29d4be-bdb3-447b-8e1d-8fae43f875ea

import Mathlib.Tactic
import Definitions.Def_allocationSum
import Definitions.Def_allocationWeight

open scoped BigOperators

theorem solution
    {σ : Type*} [Fintype σ] [DecidableEq σ]
    (e : σ → ℕ) (k : ℕ) :
    (∑ n : {n : σ → Fin (k + 1) // ∀ i, e i = 0 → n i = 0},
      OAI.PiExponent.LiteralAnalytic.allocationWeight e k n.1) =
      OAI.PiExponent.LiteralAnalytic.allocationSum
        (fun i : {j : σ // e j ≠ 0} => e i.1) k := by
  classical
  let E : {n : σ → Fin (k + 1) // ∀ i, e i = 0 → n i = 0} ≃ ({j : σ // e j ≠ 0} → Fin (k + 1)) :=
    { toFun := fun n i => n.1 i.1
      invFun := fun n' => ⟨fun i => if h : e i = 0 then 0 else n' ⟨i, h⟩, fun i hi => by simp [hi]⟩
      left_inv := fun n => by
        apply Subtype.ext; funext i
        by_cases h : e i = 0
        · simp [h, n.2 i h]
        · simp [h]
      right_inv := fun n' => by
        funext i
        simp [i.2] }
  rw [OAI.PiExponent.LiteralAnalytic.allocationSum]
  refine Fintype.sum_equiv E _ _ fun n => ?_
  simp only [OAI.PiExponent.LiteralAnalytic.allocationWeight, E, Equiv.coe_fn_mk]
  have hsum : ∑ i, ((n.1 i : ℕ)) = ∑ i : {j : σ // e j ≠ 0}, ((n.1 i.1 : ℕ)) := by
    rw [← Fintype.sum_subtype_add_sum_subtype (fun j => e j ≠ 0) (fun i => ((n.1 i : ℕ)))]
    have : ∑ i : {j : σ // ¬ e j ≠ 0}, ((n.1 i.1 : ℕ)) = 0 :=
      Finset.sum_eq_zero fun i _ => by
        have := n.2 i.1 (not_not.mp i.2); simp [this]
    rw [this, add_zero]
  have hprod : (∏ i, (if e i = 0 then (if (n.1 i : ℕ) = 0 then 1 else 0)
       else Nat.choose ((n.1 i : ℕ) + e i - 1) (n.1 i : ℕ))) =
      ∏ i : {j : σ // e j ≠ 0}, (if e i.1 = 0 then (if (n.1 i.1 : ℕ) = 0 then 1 else 0)
       else Nat.choose ((n.1 i.1 : ℕ) + e i.1 - 1) (n.1 i.1 : ℕ)) := by
    rw [← Fintype.prod_subtype_mul_prod_subtype (fun j => e j ≠ 0)]
    have : ∏ i : {j : σ // ¬ e j ≠ 0}, (if e i.1 = 0 then (if (n.1 i.1 : ℕ) = 0 then 1 else 0)
       else Nat.choose ((n.1 i.1 : ℕ) + e i.1 - 1) (n.1 i.1 : ℕ)) = 1 :=
      Finset.prod_eq_one fun i _ => by
        have h0 := not_not.mp i.2
        have := n.2 i.1 h0; simp [h0, this]
    rw [this, mul_one]
  rw [hsum, hprod]
