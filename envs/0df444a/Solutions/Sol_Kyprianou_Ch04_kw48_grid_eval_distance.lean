-- Prove2me | solution 1 for Kyprianou.Ch04.kw48_grid_eval_distance
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-25T23:38:09.369885+00:00
-- url     : https://prove2.me/submissions/8f68a4dc-296c-4f9a-baa0-64d10051cb6f

import Mathlib
import Theorems.Thm_Kyprianou_Ch04_kw47_grid_cell_exists_unique
open Set
set_option autoImplicit false

/-- A step approximation on an ordered grid evaluates its function
at an endpoint on the chosen side within the mesh distance. -/
theorem solution
    (f : Real → Complex) (u : Nat → Real) (N : Nat)
    (hu : Monotone u) (delta : Real)
    (hMesh : ∀ i, i < N → u (i+1)-u i ≤ delta)
    (right : Bool) (x : Real) (hx : x ∈ Ioc (u 0) (u N)) :
    ∃ y, y ∈ (if right then Ici x else Iic x) ∧
      dist y x ≤ delta ∧
      (∑ i ∈ Finset.range N, (Ioc (u i) (u (i+1))).indicator
        (fun _ : Real => f (if right then u (i+1) else u i)) x) = f y := by
  classical
  obtain ⟨i,hi,hxi,huniq⟩ :=
    Kyprianou.Ch04.kw47_grid_cell_exists_unique u hu N x hx
  refine ⟨if right then u (i+1) else u i,?_,?_,?_⟩
  · cases right <;> simp [hxi.1.le,hxi.2]
  · have hm := hMesh i (Finset.mem_range.mp hi)
    cases right
    · simp only [Bool.false_eq_true,if_false,Real.dist_eq]
      rw [abs_of_nonpos (sub_nonpos.mpr hxi.1.le)]
      linarith [hxi.2]
    · simp only [if_true,Real.dist_eq]
      rw [abs_of_nonneg (sub_nonneg.mpr hxi.2)]
      linarith [hxi.1]
  · rw [Finset.sum_eq_single_of_mem i hi]
    · exact Set.indicator_of_mem hxi _
    · intro j hj hne
      have hn : x ∉ Ioc (u j) (u (j+1)) :=
        fun h => hne (huniq j hj h)
      simp [Set.indicator, hn]
