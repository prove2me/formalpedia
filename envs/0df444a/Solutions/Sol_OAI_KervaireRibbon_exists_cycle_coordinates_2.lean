-- Prove2me | solution 2 for OAI.KervaireRibbon.exists_cycle_coordinates
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T19:17:45.311163+00:00
-- url     : https://prove2.me/submissions/d93448fb-2cbd-4588-9b33-cd8e1c822eac

-- Generated from openai/math@1581d4c lean/OAI/GroupTheory/Kervaire/PermutationCycles.lean:L82-L101
-- (upload_full_project.md Phase 4): solution for node OAI.KervaireRibbon.exists_cycle_coordinates. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_Kervaire
import Definitions.Def_OAI_GroupTheory_Kervaire_Reductions
import Definitions.Def_OAI_GroupTheory_Kervaire_PermutationCycles

-- ---- from OAI.GroupTheory.Kervaire.PermutationCycles ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
private theorem ite_eq_right.{u} {c : Prop} {h : Decidable c} (hc : ¬c) {α : Sort u} {t e : α} : (ite c t e) = e := @if_neg c h hc α t e

namespace OAI

noncomputable section

namespace KervaireRibbon

section
open Equiv Equiv.Perm
open scoped Classical
variable {D : Type*} [Fintype D] [DecidableEq D]

lemma cycleList_ne_nil (σ : Equiv.Perm D) (x : D) : cycleList σ x ≠ [] := by
  by_cases hx : σ x = x
  · simp [cycleList,hx]
  · simp [cycleList,hx,Equiv.Perm.toList_eq_nil_iff,Equiv.Perm.mem_support]
lemma cycleList_next (σ : Equiv.Perm D) (x y : D) (hy : y ∈ cycleList σ x) :
    (cycleList σ x).next y hy = σ y := by
  by_cases hx : σ x = x
  · have he : y = x := by simpa [cycleList,hx] using hy
    subst y
    simp [cycleList,hx,List.next]
  · simp only [cycleList,ite_eq_right hx] at hy ⊢
    exact σ.next_toList_eq_apply x y hy

lemma cycleEquiv_rotate (σ : Equiv.Perm D) (z : Cycles σ)
    (i : Fin (cycleList σ z.out).length) :
    σ (cycleEquiv σ ⟨z,i⟩) = cycleEquiv σ ⟨z,finRotate _ i⟩ := by
  have hn : 0 < (cycleList σ z.out).length := List.length_pos_iff.mpr (cycleList_ne_nil σ _)
  have hx := cycleList_next σ z.out ((cycleList σ z.out)[i.val]) (List.getElem_mem i.isLt)
  rw [List.next_getElem _ (cycleList_nodup σ z.out)] at hx
  change σ ((cycleList σ z.out)[i.val]) = (cycleList σ z.out)[(finRotate _ i).val]
  rw [← hx]
  congr 1
  let _ : NeZero (cycleList σ z.out).length := ⟨hn.ne'⟩
  simp [finRotate_apply,Fin.val_add,Nat.add_mod]

/-- Every finite permutation has a literal decomposition into nonempty cyclic
lists, including its fixed points. -/
lemma exists_cycle_coordinates (σ : Equiv.Perm D) :
    ∃ (n : Cycles σ → ℕ) (e : (Σ z, Fin (n z+1)) ≃ D),
      ∀ z i, σ (e ⟨z,i⟩) = e ⟨z,finRotate (n z+1) i⟩ := by
  let n : Cycles σ → ℕ := fun z ↦ (cycleList σ z.out).length - 1
  have hn (z : Cycles σ) : n z + 1 = (cycleList σ z.out).length := by
    have hh := List.length_pos_iff.mpr (cycleList_ne_nil σ z.out)
    dsimp [n]
    omega
  let E := Equiv.sigmaCongrRight (fun z ↦ finCongr (hn z))
  refine ⟨n,E.trans (cycleEquiv σ),?_⟩
  intro z i
  change σ (cycleEquiv σ ⟨z,finCongr (hn z) i⟩) =
    cycleEquiv σ ⟨z,finCongr (hn z) (finRotate _ i)⟩
  rw [cycleEquiv_rotate]
  apply congrArg (cycleEquiv σ)
  apply congrArg (fun j : Fin (cycleList σ z.out).length ↦ (⟨z,j⟩ : Σ z : Cycles σ, Fin (cycleList σ z.out).length))
  apply Fin.ext
  simp [finRotate_apply,Fin.val_add,hn]

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


theorem solution : type_of% @_root_.OAI.KervaireRibbon.exists_cycle_coordinates := @_root_.OAI.KervaireRibbon.exists_cycle_coordinates
