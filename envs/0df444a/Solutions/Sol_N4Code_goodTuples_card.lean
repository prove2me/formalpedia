-- Prove2me | solution 1 for N4Code.goodTuples_card
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:01:06.236598+00:00
-- url     : https://prove2.me/submissions/01c382e0-9f7d-4857-9577-10769e44f265

import Definitions.Def_N4Code_Definitions
import Mathlib.Data.Finset.Defs
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.FinCases
import Definitions.Def_N4Code_Basic
import Theorems.Thm_N4Code_fiber_card_eq_count

set_option autoImplicit true
open scoped BigOperators
set_option maxHeartbeats 4000000
set_option maxRecDepth 1000000
open N4Code
namespace N4Code
theorem _root_.solution {n : ℕ} (C : Code n) (k : ℕ → ℕ) :
    (GoodTuples C k).card = ∏ i ∈ Finset.Icc 0 15, Nat.choose (count C i) (k i) := by
  let B := {g : Fin 16 → Finset (Fin n) // g ∈ GoodTuples C k}
  have hB : Fintype.card B = (GoodTuples C k).card := by
    change (Finset.univ : Finset B).card = (GoodTuples C k).card
    rw [show (Finset.univ : Finset B) = (GoodTuples C k).attach by
      ext g
      exact iff_of_true (by simp) (Finset.mem_attach (GoodTuples C k) g)]
    exact Finset.card_attach
  have hsub : ∀ a : Fin 16,
      Fintype.card {S : Finset (Fin n) // S ∈ (fiber C a.val).powersetCard (k a.val)} =
        Nat.choose (count C a.val) (k a.val) := by
    intro a
    change (Finset.univ : Finset {S : Finset (Fin n) // S ∈ (fiber C a.val).powersetCard (k a.val)}).card =
      Nat.choose (count C a.val) (k a.val)
    rw [show (Finset.univ : Finset {S : Finset (Fin n) // S ∈ (fiber C a.val).powersetCard (k a.val)}) =
        ((fiber C a.val).powersetCard (k a.val)).attach by
      ext S
      exact iff_of_true (by simp)
        (Finset.mem_attach ((fiber C a.val).powersetCard (k a.val)) S)]
    rw [Finset.card_attach, Finset.card_powersetCard, fiber_card_eq_count]
  have hEq : B ≃ ((a : Fin 16) →
      {S : Finset (Fin n) // S ∈ (fiber C a.val).powersetCard (k a.val)}) :=
    { toFun := fun g a => ⟨g.1 a, (Finset.mem_filter.mp g.2).2 a⟩
      invFun := fun t => ⟨fun a => (t a).1,
        Finset.mem_filter.mpr ⟨Finset.mem_univ _, fun a => (t a).2⟩⟩
      left_inv := fun g => by
        apply Subtype.ext
        ext a
        rfl
      right_inv := fun t => by
        funext a
        apply Subtype.ext
        rfl }
  rw [← hB]
  rw [Fintype.card_congr hEq, Fintype.card_pi]
  calc
    (∏ a ∈ (Finset.univ : Finset (Fin 16)),
        Fintype.card {S : Finset (Fin n) // S ∈ (fiber C a.val).powersetCard (k a.val)}) =
        ∏ a ∈ (Finset.univ : Finset (Fin 16)), Nat.choose (count C a.val) (k a.val) := by
      apply Finset.prod_congr rfl
      intro a _
      exact hsub a
    _ = ∏ i ∈ Finset.Icc 0 15, Nat.choose (count C i) (k i) := by
      exact Finset.prod_bij
        (fun (a : Fin 16) _ => (a.val : ℕ))
        (by intro a _; exact Finset.mem_Icc.mpr ⟨Nat.zero_le a.val, Nat.le_of_lt_succ a.isLt⟩)
        (by intro a _ b _ h; apply Fin.ext; exact h)
        (by
          intro b hb
          refine ⟨⟨b, ?_⟩, ?_, ?_⟩
          · exact Nat.lt_succ_of_le (Finset.mem_Icc.mp hb).2
          · simp
          · rfl)
        (by intro a _; rfl)
end N4Code
