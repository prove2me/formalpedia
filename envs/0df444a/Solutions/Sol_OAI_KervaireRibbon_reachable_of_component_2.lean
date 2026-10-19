-- Prove2me | solution 2 for OAI.KervaireRibbon.reachable_of_component
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T19:31:20.839163+00:00
-- url     : https://prove2.me/submissions/961f6add-9c6c-41c3-be75-f73b6ab82900

-- Generated from openai/math@1581d4c lean/OAI/GroupTheory/Kervaire/ComponentFibers.lean:L227-L244
-- (upload_full_project.md Phase 4): solution for node OAI.KervaireRibbon.reachable_of_component. The node keeps its source
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
namespace OAI

noncomputable section

namespace KervaireRibbon

section
open Equiv Equiv.Perm
open scoped Classical
variable {D : Type*} [Fintype D] [DecidableEq D]

end

section
open Equiv Equiv.Perm
open scoped Classical
variable {D : Type*} [Fintype D] [DecidableEq D]

end

open Equiv Equiv.Perm
open scoped Classical
variable {D : Type*} [Fintype D] [DecidableEq D]

omit [DecidableEq D] in
lemma reachable_of_cycle {r : D → D → Prop} (σ : Perm D)
    (hs : ∀ d, r d (σ d)) {x y : D} (hxy : σ.SameCycle x y) : Relation.ReflTransGen r x y := by
  obtain ⟨n,rfl⟩ := hxy.exists_nat_pow_eq
  clear hxy
  induction n with
  | zero => exact .refl
  | succ n ih =>
    rw [pow_succ',mul_apply]
    exact ih.tail (hs _)

omit [DecidableEq D] in
lemma reachable_of_component (σ θ : Perm D) {x y : D} (h : components σ θ x y) :
    Relation.ReflTransGen (fun d f ↦ f = σ d ∨ f = θ d) x y := by
  change (SameCycle.setoid σ ⊔ SameCycle.setoid θ) x y at h
  rw [Setoid.sup_eq_eqvGen] at h
  have hh : Relation.ReflTransGen (fun d f ↦ f = σ d ∨ f = θ d) x y ∧
      Relation.ReflTransGen (fun d f ↦ f = σ d ∨ f = θ d) y x := by
    induction h with
    | rel x y h =>
      rcases h with h | h
      · exact ⟨reachable_of_cycle σ (fun _ ↦ Or.inl rfl) h,
          reachable_of_cycle σ (fun _ ↦ Or.inl rfl) h.symm⟩
      · exact ⟨reachable_of_cycle θ (fun _ ↦ Or.inr rfl) h,
          reachable_of_cycle θ (fun _ ↦ Or.inr rfl) h.symm⟩
    | refl x => exact ⟨.refl,.refl⟩
    | symm x y h ih => exact ih.symm
    | trans x y z h₁ h₂ ih₁ ih₂ => exact ⟨ih₁.1.trans ih₂.1,ih₂.2.trans ih₁.2⟩
  exact hh.1
end KervaireRibbon

end

end OAI

-- ---- platform node ----
open OAI OAI.KervaireRibbon
open Equiv Equiv.Perm
open scoped Classical


theorem solution : type_of% @_root_.OAI.KervaireRibbon.reachable_of_component := @_root_.OAI.KervaireRibbon.reachable_of_component
