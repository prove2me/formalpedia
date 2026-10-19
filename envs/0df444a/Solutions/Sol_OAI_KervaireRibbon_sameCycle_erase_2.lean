-- Prove2me | solution 2 for OAI.KervaireRibbon.sameCycle_erase
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T19:19:13.133214+00:00
-- url     : https://prove2.me/submissions/e3bcf178-15ab-46eb-b7e6-5dd4cc96de59

-- Generated from openai/math@1581d4c lean/OAI/GroupTheory/Kervaire/Suppression.lean:L41-L63
-- (upload_full_project.md Phase 4): solution for node OAI.KervaireRibbon.sameCycle_erase. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_Kervaire
import Definitions.Def_OAI_GroupTheory_Kervaire_Reductions
import Definitions.Def_OAI_GroupTheory_Kervaire_PermutationCycles
import Definitions.Def_OAI_GroupTheory_Kervaire_Components
import Definitions.Def_OAI_GroupTheory_Kervaire_Suppression

-- ---- from OAI.GroupTheory.Kervaire.Suppression ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
private theorem ite_eq_left.{u} {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t e : α} : (ite c t e) = t := @if_pos c h hc α t e
private theorem ite_eq_right.{u} {c : Prop} {h : Decidable c} (hc : ¬c) {α : Sort u} {t e : α} : (ite c t e) = e := @if_neg c h hc α t e

namespace OAI

noncomputable section

namespace KervaireRibbon

section
open Equiv Equiv.Perm
open scoped Classical
variable {D : Type*} [Fintype D] [DecidableEq D]

lemma cycles_erase_le (σ : Equiv.Perm D) (x : D) :
    SameCycle.setoid (erase σ x) ≤ SameCycle.setoid σ := by
  have h := cycles_swap_le σ (SameCycle.setoid σ) le_rfl x (σ x)
  rw [joinPair_eq _ SameCycle.rfl.apply_right] at h
  exact h

lemma sameCycle_erase (σ : Equiv.Perm D) {x d e : D} (hx : σ x ≠ x)
    (hd : d ≠ x) (he : e ≠ x) :
    (erase σ x).SameCycle d e ↔ σ.SameCycle d e := by
  refine ⟨fun h ↦ cycles_erase_le σ x h,?_⟩
  intro h
  let τ := erase σ x
  let f : D → Cycles τ := fun a ↦ Quotient.mk _ (if a = x then σ x else a)
  have hf (a : D) : f (σ a) = f a := by
    by_cases ha : a = x
    · subst a
      simp [f,hx]
    by_cases hs : σ a = x
    · have ht : τ a = σ x := by simp only [τ,erase_apply σ x a ha,ite_eq_left hs]
      change Quotient.mk _ (if σ a = x then σ x else σ a) = Quotient.mk _ (if a = x then σ x else a)
      rw [ite_eq_left hs,ite_eq_right ha,← ht]
      exact Quotient.sound SameCycle.rfl.apply_left
    · have ht : τ a = σ a := by simp only [τ,erase_apply σ x a ha,ite_eq_right hs]
      change Quotient.mk _ (if σ a = x then σ x else σ a) = Quotient.mk _ (if a = x then σ x else a)
      rw [ite_eq_right hs,ite_eq_right ha,← ht]
      exact Quotient.sound SameCycle.rfl.apply_left
  have hh := sameCycle_map_eq σ f hf h
  apply Quotient.exact (s := SameCycle.setoid τ)
  simpa only [f,ite_eq_right hd,ite_eq_right he] using hh

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


theorem solution : type_of% @_root_.OAI.KervaireRibbon.sameCycle_erase := @_root_.OAI.KervaireRibbon.sameCycle_erase
