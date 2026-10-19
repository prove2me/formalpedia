-- Prove2me | solution 2 for OAI.KervaireRibbon.fiber_connected
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T19:27:35.64968+00:00
-- url     : https://prove2.me/submissions/de9037e7-833a-4103-b124-a37c84f26484

-- Generated from openai/math@1581d4c lean/OAI/GroupTheory/Kervaire/ComponentFibers.lean:L56-L94
-- (upload_full_project.md Phase 4): solution for node OAI.KervaireRibbon.fiber_connected. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_Kervaire
import Definitions.Def_OAI_GroupTheory_Kervaire_Reductions
import Definitions.Def_OAI_GroupTheory_Kervaire_PermutationCycles
import Definitions.Def_OAI_GroupTheory_Kervaire_Components
import Definitions.Def_OAI_GroupTheory_Kervaire_Suppression
import Definitions.Def_OAI_GroupTheory_Kervaire_ComponentFibers

-- ---- from OAI.GroupTheory.Kervaire.ComponentFibers ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
private theorem dite_eq_left.{u} {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t : c → α} {e : ¬c → α} : (dite c t e) = t hc := @dif_pos c h hc α t e
private theorem dite_eq_right.{u} {c : Prop} {h : Decidable c} (hc : ¬c) {α : Sort u} {t : c → α} {e : ¬c → α} : (dite c t e) = e hc := @dif_neg c h hc α t e

namespace OAI

noncomputable section

namespace KervaireRibbon

section
open Equiv Equiv.Perm
open scoped Classical
variable {D : Type*} [Fintype D] [DecidableEq D]

lemma fiber_connected (σ θ : Equiv.Perm D) (c : Quotient (components σ θ)) :
    components (fiberPerm σ (components σ θ) le_sup_left c)
      (fiberPerm θ (components σ θ) le_sup_right c) = ⊤ := by
  let r := components σ θ
  let σ' := fiberPerm σ r le_sup_left c
  let θ' := fiberPerm θ r le_sup_right c
  let r' := components σ' θ'
  let f : D → Option (Quotient r') := fun d ↦ if h : Quotient.mk r d = c then some (Quotient.mk r' ⟨d,h⟩) else none
  have step (τ : Equiv.Perm D) (ht : SameCycle.setoid τ ≤ r)
      (ht' : SameCycle.setoid (fiberPerm τ r ht c) ≤ r') (d : D) : f (τ d) = f d := by
    have he : Quotient.mk r (τ d) = Quotient.mk r d := Quotient.sound (ht SameCycle.rfl.apply_left)
    by_cases hd : Quotient.mk r d = c
    · have htd : Quotient.mk r (τ d) = c := he.trans hd
      simp only [f,dite_eq_left htd,dite_eq_left hd]
      apply congrArg some
      apply Quotient.sound
      exact ht' (SameCycle.rfl.apply_left (x := (⟨d,hd⟩ : Fiber r c)))
    · have htd : Quotient.mk r (τ d) ≠ c := fun h ↦ hd (he.symm.trans h)
      simp only [f,dite_eq_right htd,dite_eq_right hd]
  have hrker : r ≤ Setoid.ker f := sup_le
    (cycle_le_of_step σ _ (step σ le_sup_left le_sup_left))
    (cycle_le_of_step θ _ (step θ le_sup_right le_sup_right))
  apply top_unique
  intro d e _
  have hde : r d.val e.val := Quotient.exact (d.property.trans e.property.symm)
  have hh := hrker hde
  have hd : f d.val = some (Quotient.mk r' d) := by
    dsimp [f]
    split
    · rfl
    · exact False.elim (‹¬ _› d.property)
  have he : f e.val = some (Quotient.mk r' e) := by
    dsimp [f]
    split
    · rfl
    · exact False.elim (‹¬ _› e.property)
  change f d.val = f e.val at hh
  rw [hd,he] at hh
  exact Quotient.exact (Option.some.inj hh)

end

section
open Equiv Equiv.Perm
open scoped Classical
variable {D : Type*} [Fintype D] [DecidableEq D]

end

open Equiv Equiv.Perm
open scoped Classical
variable {D : Type*} [Fintype D] [DecidableEq D]

end KervaireRibbon

end

end OAI

-- ---- platform node ----
open OAI OAI.KervaireRibbon
open Equiv Equiv.Perm
open scoped Classical


theorem solution : type_of% @_root_.OAI.KervaireRibbon.fiber_connected := @_root_.OAI.KervaireRibbon.fiber_connected
