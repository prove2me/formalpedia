-- Prove2me | solution 1 for Matrix.exists_eq_smul_one_of_commute_of_map_span_eq_top
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.007888+00:00
-- url     : https://prove2.me/submissions/93880e2a-d56f-565c-9f69-006782c22587

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_Matrix_exists_eq_smul_one_of_commute_of_map_span_eq_top

open IsLocalRing

theorem w2aux_mem_smul_top
    {n : Type*} [Fintype n] [DecidableEq n] {A : Type*} [CommRing A]
    {I : Ideal A} {M : Matrix n n A} (hM : ∀ i j, M i j ∈ I) :
    M ∈ (I • ⊤ : Submodule A (Matrix n n A)) := by
  rw [Matrix.matrix_eq_sum_single M]
  refine Submodule.sum_mem _ fun i _ => Submodule.sum_mem _ fun j _ => ?_
  rw [show Matrix.single i j (M i j) = M i j • Matrix.single i j (1 : A) by
    rw [Matrix.smul_single, smul_eq_mul, mul_one]]
  exact Submodule.smul_mem_smul (hM i j) Submodule.mem_top

theorem w2aux_exists_map_eq
    {n : Type*} {A : Type*} [CommRing A] {k : Type*} [Field k]
    (π : A →+* k) (hπ : Function.Surjective π)
    {S : Set (Matrix n n A)}
    (hS : Submodule.span k ((fun X : Matrix n n A => X.map π) '' S) = ⊤)
    (X : Matrix n n k) : ∃ Y ∈ Submodule.span A S, Y.map π = X := by
  have hX : X ∈ Submodule.span k ((fun X : Matrix n n A => X.map π) '' S) :=
    hS ▸ Submodule.mem_top
  induction hX using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨Y, hY, rfl⟩ := hx
    exact ⟨Y, Submodule.subset_span hY, rfl⟩
  | zero => exact ⟨0, Submodule.zero_mem _, by simp [Matrix.map_zero]⟩
  | add x y _ _ hx hy =>
    obtain ⟨Y, hY, rfl⟩ := hx
    obtain ⟨Z, hZ, rfl⟩ := hy
    exact ⟨Y + Z, Submodule.add_mem _ hY hZ, by simp [Matrix.map_add]⟩
  | smul c x _ hx =>
    obtain ⟨Y, hY, rfl⟩ := hx
    obtain ⟨c', rfl⟩ := hπ c
    refine ⟨c' • Y, Submodule.smul_mem _ _ hY, ?_⟩
    ext i j
    simp [Matrix.map_apply]

theorem w2aux_span_lift
    {n : Type*} [Fintype n] [DecidableEq n] {A : Type*} [CommRing A] [IsLocalRing A]
    {k : Type*} [Field k] (π : A →+* k) (hπ : Function.Surjective π) {S : Set (Matrix n n A)}
    (hS : Submodule.span k ((fun X : Matrix n n A => X.map π) '' S) = ⊤) :
    Submodule.span A S = ⊤ := by
  rw [eq_top_iff]
  refine Submodule.le_of_le_smul_of_le_jacobson_bot (I := maximalIdeal A) Module.Finite.fg_top
    (by rw [IsLocalRing.jacobson_eq_maximalIdeal ⊥ bot_ne_top]) ?_
  intro Z _
  obtain ⟨Y, hY, hYZ⟩ := w2aux_exists_map_eq π hπ hS (Z.map π)
  have hZY : Z - Y ∈ (maximalIdeal A • ⊤ : Submodule A (Matrix n n A)) := by
    refine w2aux_mem_smul_top fun i j => ?_
    have hker : ∀ a : A, π a = 0 → a ∈ maximalIdeal A := fun a ha => by
      rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
      intro h
      exact not_isUnit_zero (ha ▸ h.map π)
    refine hker _ ?_
    have := congrArg (fun W => W i j) hYZ
    simp only [Matrix.map_apply] at this
    simp [this]
  have : Z = Y + (Z - Y) := by abel
  rw [this]
  exact Submodule.add_mem _ (Submodule.mem_sup_left hY) (Submodule.mem_sup_right hZY)

theorem w2aux_center
    {n : Type*} [Fintype n] [DecidableEq n] {A : Type*} [CommRing A]
    {S : Set (Matrix n n A)} (hS : Submodule.span A S = ⊤)
    (M : Matrix n n A) (hM : ∀ X ∈ S, X * M = M * X) :
    ∃ a : A, M = a • 1 := by
  have hcomm : ∀ X : Matrix n n A, X * M = M * X := by
    have hle : Submodule.span A S ≤
        { carrier := {X | X * M = M * X}
          add_mem' := fun {X} {Y} hX hY => by
            simp only [Set.mem_setOf_eq] at hX hY ⊢
            rw [add_mul, mul_add, hX, hY]
          zero_mem' := by simp
          smul_mem' := fun a X hX => by
            simp only [Set.mem_setOf_eq] at hX ⊢
            rw [smul_mul_assoc, mul_smul_comm, hX] } :=
      Submodule.span_le.mpr hM
    intro X
    exact hle (hS ▸ Submodule.mem_top)
  have hMc : M ∈ Set.center (Matrix n n A) := Semigroup.mem_center_iff.mpr hcomm
  rw [Matrix.center_eq_range] at hMc
  obtain ⟨a, ha⟩ := hMc
  refine ⟨a, ?_⟩
  rw [← ha, Matrix.scalar_apply, Matrix.smul_one_eq_diagonal]

theorem solution
    {n : Type*} [Fintype n] [DecidableEq n] {A : Type*} [CommRing A] [IsLocalRing A]
    {k : Type*} [Field k] (π : A →+* k) (hπ : Function.Surjective π)
    {S : Set (Matrix n n A)}
    (hS : Submodule.span k ((fun X : Matrix n n A => X.map π) '' S) = ⊤)
    (M : Matrix n n A) (hM : ∀ X ∈ S, X * M = M * X) : ∃ a : A, M = a • 1 :=
  w2aux_center
    (w2aux_span_lift π hπ hS) M hM

end S_Matrix_exists_eq_smul_one_of_commute_of_map_span_eq_top
end P2MW
export P2MW.S_Matrix_exists_eq_smul_one_of_commute_of_map_span_eq_top (solution)
