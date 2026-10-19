-- Prove2me | solution 1 for OAI.Saxl.high_positions_rigidity
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T00:09:03.194091+00:00
-- url     : https://prove2.me/submissions/8e54dfc5-d668-47ac-af02-0ea6d14f47fd

import Mathlib
import Definitions.Def_Saxl
import Definitions.Def_OAI_RepresentationTheory_Saxl_Basic
import Definitions.Def_OAI_RepresentationTheory_Saxl_Polytabloid
import Definitions.Def_OAI_RepresentationTheory_Saxl_SpechtSubmodule
import Definitions.Def_OAI_RepresentationTheory_Saxl_SpechtDuality
import Definitions.Def_OAI_RepresentationTheory_Saxl_TableauTransport
import Definitions.Def_OAI_RepresentationTheory_Saxl_StaircaseTensor
import Definitions.Def_OAI_RepresentationTheory_Saxl_HighProjection

open OAI OAI.Saxl
open scoped TensorProduct
theorem h42_finset_eq {X : Type*} [DecidableEq X]
    (A B : Finset X) (w : X → ℤ)
    (hp : ∀ x ∈ B, 0 < w x) (hn : ∀ x ∉ B, w x < 0)
    (he : ∑ x ∈ A, w x = ∑ x ∈ B, w x) : A = B := by
  have h1 := Finset.sum_sdiff (s₁ := A ∩ B) (s₂ := A) (f := w) Finset.inter_subset_left
  have h2 := Finset.sum_sdiff (s₁ := A ∩ B) (s₂ := B) (f := w) Finset.inter_subset_right
  have e1 : A \ (A ∩ B) = A \ B := by ext x; simp
  have e2 : B \ (A ∩ B) = B \ A := by ext x; simp [and_comm]
  rw [e1] at h1; rw [e2] at h2
  have hAB : ∑ x ∈ A \ B, w x = ∑ x ∈ B \ A, w x := by omega
  have hle : ∑ x ∈ A \ B, w x ≤ 0 := Finset.sum_nonpos (fun x hx => by
    have := hn x (Finset.mem_sdiff.1 hx).2; omega)
  have hge : 0 ≤ ∑ x ∈ B \ A, w x := Finset.sum_nonneg (fun x hx => by
    have := hp x (Finset.mem_sdiff.1 hx).1; omega)
  have d1 : A \ B = ∅ := by
    by_contra hne
    obtain ⟨y, hy⟩ := Finset.nonempty_iff_ne_empty.2 hne
    have : ∑ x ∈ A \ B, w x < 0 := Finset.sum_neg (fun x hx => hn x (Finset.mem_sdiff.1 hx).2) ⟨y, hy⟩
    omega
  have d2 : B \ A = ∅ := by
    by_contra hne
    obtain ⟨y, hy⟩ := Finset.nonempty_iff_ne_empty.2 hne
    have : 0 < ∑ x ∈ B \ A, w x := Finset.sum_pos (fun x hx => hp x (Finset.mem_sdiff.1 hx).1) ⟨y, hy⟩
    omega
  rw [Finset.sdiff_eq_empty_iff_subset] at d1 d2
  exact Finset.Subset.antisymm d1 d2

theorem h42_shiftA (h s : ℕ) (f : ℕ → ℤ) :
    ∑ y ∈ (staircase (h+s)).cells, (if s ≤ y.2 then f y.1 else 0) =
      ∑ y ∈ (staircase (h+s)).cells, (if y.1 + y.2 < h then f y.1 else 0) := by
  rw [← Finset.sum_filter, ← Finset.sum_filter]
  apply Finset.sum_nbij' (fun y => (y.1, y.2 - s)) (fun y => (y.1, y.2 + s))
  · rintro ⟨a, b⟩ hy
    dsimp only; simp only [Finset.mem_filter, YoungDiagram.mem_cells, mem_staircase] at hy ⊢; omega
  · rintro ⟨a, b⟩ hy
    dsimp only; simp only [Finset.mem_filter, YoungDiagram.mem_cells, mem_staircase] at hy ⊢; omega
  · rintro ⟨a, b⟩ hy
    simp only [Finset.mem_filter, YoungDiagram.mem_cells, mem_staircase] at hy
    refine Prod.ext ?_ ?_ <;> dsimp only <;> omega
  · rintro ⟨a, b⟩ hy
    simp only [Finset.mem_filter, YoungDiagram.mem_cells, mem_staircase] at hy
    refine Prod.ext ?_ ?_ <;> dsimp only <;> omega
  · intro y _; rfl

theorem h42_shiftB (h s : ℕ) (f : ℕ → ℤ) :
    ∑ y ∈ (staircase (h+s)).cells, (if s ≤ y.1 then f y.2 else 0) =
      ∑ y ∈ (staircase (h+s)).cells, (if y.1 + y.2 < h then f y.2 else 0) := by
  rw [← Finset.sum_filter, ← Finset.sum_filter]
  apply Finset.sum_nbij' (fun y => (y.1 - s, y.2)) (fun y => (y.1 + s, y.2))
  · rintro ⟨a, b⟩ hy
    dsimp only; simp only [Finset.mem_filter, YoungDiagram.mem_cells, mem_staircase] at hy ⊢; omega
  · rintro ⟨a, b⟩ hy
    dsimp only; simp only [Finset.mem_filter, YoungDiagram.mem_cells, mem_staircase] at hy ⊢; omega
  · rintro ⟨a, b⟩ hy
    simp only [Finset.mem_filter, YoungDiagram.mem_cells, mem_staircase] at hy
    refine Prod.ext ?_ ?_ <;> dsimp only <;> omega
  · rintro ⟨a, b⟩ hy
    simp only [Finset.mem_filter, YoungDiagram.mem_cells, mem_staircase] at hy
    refine Prod.ext ?_ ?_ <;> dsimp only <;> omega
  · intro y _; rfl

theorem solution (h s : ℕ)
    (g k : Equiv.Perm (staircase (h+s)).cells)
    (hg : ∀ x, (g x).val.1 = x.val.1)
    (hk : ∀ x, (k x).val.2 = x.val.2)
    (hc : ∀ x, s ≤ (g x).val.2 ↔ s ≤ (k x).val.1) :
    ∀ x, s ≤ (g x).val.2 ↔ x.val.1 + x.val.2 < h := by
  classical
  let C := (staircase (h+s)).cells
  let α : ℕ → ℤ := fun r => 2 * (h : ℤ) - 1 - 2 * r
  let β : ℕ → ℤ := fun c => -2 * (c : ℤ)
  let w : C → ℤ := fun x => α x.val.1 + β x.val.2
  let H : Finset C := Finset.univ.filter (fun x => s ≤ (g x).val.2)
  let T : Finset C := Finset.univ.filter (fun x => x.val.1 + x.val.2 < h)
  have hA : ∑ x : C, (if s ≤ x.val.2 then α x.val.1 else 0) =
      ∑ x : C, (if x.val.1 + x.val.2 < h then α x.val.1 else 0) := by
    rw [Finset.sum_coe_sort C (fun y => if s ≤ y.2 then α y.1 else 0),
      Finset.sum_coe_sort C (fun y => if y.1 + y.2 < h then α y.1 else 0)]
    exact h42_shiftA h s α
  have hB : ∑ x : C, (if s ≤ x.val.1 then β x.val.2 else 0) =
      ∑ x : C, (if x.val.1 + x.val.2 < h then β x.val.2 else 0) := by
    rw [Finset.sum_coe_sort C (fun y => if s ≤ y.1 then β y.2 else 0),
      Finset.sum_coe_sort C (fun y => if y.1 + y.2 < h then β y.2 else 0)]
    exact h42_shiftB h s β
  have hgA : ∑ x : C, (if s ≤ (g x).val.2 then α x.val.1 else 0) =
      ∑ x : C, (if s ≤ x.val.2 then α x.val.1 else 0) := by
    rw [← Equiv.sum_comp g (fun x : C => if s ≤ x.val.2 then α x.val.1 else 0)]
    apply Finset.sum_congr rfl; intro x _; simp only [hg]
  have hkB : ∑ x : C, (if s ≤ (g x).val.2 then β x.val.2 else 0) =
      ∑ x : C, (if s ≤ x.val.1 then β x.val.2 else 0) := by
    rw [← Equiv.sum_comp k (fun x : C => if s ≤ x.val.1 then β x.val.2 else 0)]
    apply Finset.sum_congr rfl; intro x _; simp only [hk, hc]
  have hsplit : ∀ (p : C → Prop) [DecidablePred p], ∑ x ∈ Finset.univ.filter p, w x =
      ∑ x : C, (if p x then α x.val.1 else 0) + ∑ x : C, (if p x then β x.val.2 else 0) := by
    intro p _
    rw [Finset.sum_filter, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl; intro x _
    split_ifs <;> simp [w]
  have heq : H = T := by
    apply h42_finset_eq H T w
    · intro x hx
      simp only [T, Finset.mem_filter, Finset.mem_univ, true_and] at hx
      simp only [w, α, β]; omega
    · intro x hx
      simp only [T, Finset.mem_filter, Finset.mem_univ, true_and] at hx
      simp only [w, α, β]; omega
    · rw [hsplit, hsplit, hgA, hkB, hA, hB]
  intro x
  have := congrArg (fun S : Finset C => x ∈ S) heq
  simpa [H, T] using this

