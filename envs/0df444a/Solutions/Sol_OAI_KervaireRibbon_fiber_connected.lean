-- Prove2me | solution 1 for OAI.KervaireRibbon.fiber_connected
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-18T19:07:54.031973+00:00
-- url     : https://prove2.me/submissions/e6b5abf7-440f-46b8-bb33-35aa8040f756

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
theorem kr_reach (σ θ : Perm D) {x y : D} (h : components σ θ x y) :
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

theorem solution (σ θ : Equiv.Perm D) (c : Quotient (components σ θ)) :
    components (fiberPerm σ (components σ θ) le_sup_left c)
      (fiberPerm θ (components σ θ) le_sup_right c) = ⊤ := by
  have hσr : SameCycle.setoid σ ≤ (components σ θ) := le_sup_left
  have hθr : SameCycle.setoid θ ≤ (components σ θ) := le_sup_right
  have hclass : ∀ d e : D, Relation.ReflTransGen (fun d f ↦ f = σ d ∨ f = θ d) d e →
      Quotient.mk (components σ θ) e = Quotient.mk (components σ θ) d := by
    intro d e h
    induction h with
    | refl => rfl
    | tail _ hstep ih =>
      rw [← ih]
      apply Quotient.sound
      rcases hstep with rfl | rfl
      · exact (components σ θ).symm' (hσr SameCycle.rfl.apply_right)
      · exact (components σ θ).symm' (hθr SameCycle.rfl.apply_right)
  refine le_antisymm le_top ?_
  rintro ⟨d, hd⟩ ⟨e, he⟩ -
  have hde : (components σ θ) d e := Quotient.exact (hd.trans he.symm)
  have hpath := kr_reach σ θ hde
  suffices key : ∀ e', Relation.ReflTransGen (fun d f ↦ f = σ d ∨ f = θ d) d e' →
      ∀ he' : Quotient.mk (components σ θ) e' = c,
      components (fiberPerm σ (components σ θ) hσr c) (fiberPerm θ (components σ θ) hθr c) ⟨d, hd⟩ ⟨e', he'⟩ from key e hpath he
  intro e' hp
  induction hp with
  | refl => intro _; exact Setoid.refl' _ _
  | @tail b e'' hb hstep ih =>
    intro he''
    have hb' : Quotient.mk (components σ θ) b = c := (hclass d b hb).trans hd
    refine (components _ _).trans' (ih hb') ?_
    rcases hstep with rfl | rfl
    · have : (⟨σ b, he''⟩ : Fiber (components σ θ) c) = fiberPerm σ (components σ θ) hσr c ⟨b, hb'⟩ := rfl
      rw [this]
      exact (le_sup_left : SameCycle.setoid _ ≤ components _ _) SameCycle.rfl.apply_right
    · have : (⟨θ b, he''⟩ : Fiber (components σ θ) c) = fiberPerm θ (components σ θ) hθr c ⟨b, hb'⟩ := rfl
      rw [this]
      exact (le_sup_right : SameCycle.setoid _ ≤ components _ _) SameCycle.rfl.apply_right
