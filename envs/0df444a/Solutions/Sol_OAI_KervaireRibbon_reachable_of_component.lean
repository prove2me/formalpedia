-- Prove2me | solution 1 for OAI.KervaireRibbon.reachable_of_component
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-18T18:17:08.920377+00:00
-- url     : https://prove2.me/submissions/05cd4d07-7dda-47bc-9851-ba8720413357

import Mathlib
import Definitions.Def_Kervaire
import Definitions.Def_OAI_GroupTheory_Kervaire_Reductions
import Definitions.Def_OAI_GroupTheory_Kervaire_PermutationCycles
import Definitions.Def_OAI_GroupTheory_Kervaire_Components
import Definitions.Def_OAI_GroupTheory_Kervaire_Suppression
import Definitions.Def_OAI_GroupTheory_Kervaire_ComponentFibers

open OAI OAI.KervaireRibbon
open Equiv Equiv.Perm
open scoped Classical
variable {D : Type*} [Fintype D] [DecidableEq D]
omit [DecidableEq D] in
theorem solution (σ θ : Perm D) {x y : D} (h : components σ θ x y) :
    Relation.ReflTransGen (fun d f ↦ f = σ d ∨ f = θ d) x y := by
  let step : D → D → Prop := fun d f ↦ f = σ d ∨ f = θ d
  have hpow : ∀ (π : Perm D), (∀ d, step d (π d)) → ∀ (n : ℕ) d, Relation.ReflTransGen step d ((π ^ n) d) := by
    intro π hπ n
    induction n with
    | zero => intro d; rw [pow_zero]; exact Relation.ReflTransGen.refl
    | succ n ih =>
      intro d
      rw [pow_succ', Perm.mul_apply]
      exact (ih d).tail (hπ _)
  have hback : ∀ (π : Perm D), (∀ d, step d (π d)) → ∀ d, Relation.ReflTransGen step (π d) d := by
    intro π hπ d
    have hpos : 0 < orderOf π := orderOf_pos π
    have := hpow π hπ (orderOf π - 1) (π d)
    have he : (π ^ (orderOf π - 1)) (π d) = d := by
      rw [← Perm.mul_apply, ← pow_succ, Nat.sub_add_cancel hpos, pow_orderOf_eq_one]; rfl
    rwa [he] at this
  have hσ : ∀ d, step d (σ d) := fun d => Or.inl rfl
  have hθ : ∀ d, step d (θ d) := fun d => Or.inr rfl
  have hsymm : ∀ a b, Relation.ReflTransGen step a b → Relation.ReflTransGen step b a := by
    intro a b hab
    induction hab with
    | refl => exact Relation.ReflTransGen.refl
    | tail _ hbc ih =>
      rcases hbc with rfl | rfl
      · exact (hback σ hσ _).trans ih
      · exact (hback θ hθ _).trans ih
  let R : Setoid D := ⟨Relation.ReflTransGen step,
    ⟨fun _ => Relation.ReflTransGen.refl, fun h => hsymm _ _ h, fun h1 h2 => h1.trans h2⟩⟩
  have h1 : SameCycle.setoid σ ≤ R := cycle_le_of_step σ R (fun d => hback σ hσ d)
  have h2 : SameCycle.setoid θ ≤ R := cycle_le_of_step θ R (fun d => hback θ hθ d)
  exact (sup_le h1 h2 : components σ θ ≤ R) h
