-- Prove2me | solution 1 for MaxLatticeFree.Geometry.unbounded_maxLambdaFree_linSpace_eq_recCone
-- status  : ACCEPTED   (prove)
-- author  : @xwh
-- created : 2026-10-23T09:07:14.351591+00:00
-- url     : https://prove2.me/submissions/e52b85d4-cf00-4e68-892d-1c229a97f74a

import Mathlib
import Definitions.Def_MaxLatticeFree_Geometry_IsLatticeOf
import Definitions.Def_MaxLatticeFree_Geometry_intW
import Definitions.Def_MaxLatticeFree_Geometry_IsLambdaFree
import Definitions.Def_MaxLatticeFree_Geometry_recCone
import Definitions.Def_MaxLatticeFree_Geometry_affDim
import Theorems.Thm_MaxLatticeFree_Geometry_lambdaFree_add_span_recCone

open scoped Pointwise
open MaxLatticeFree.Geometry

theorem solution {n : ℕ} (Λ : AddSubgroup (EuclideanSpace ℝ (Fin n)))
    (V : Submodule ℝ (EuclideanSpace ℝ (Fin n))) (hΛ : IsLatticeOf Λ V)
    (S : Set (EuclideanSpace ℝ (Fin n))) (hS : IsMaxLambdaFree Λ V S)
    (hdim : affDim S = (Module.finrank ℝ V : ℤ)) (hunbdd : ¬ Bornology.IsBounded S) :
    linSpace S = recCone S := by
  let K := Submodule.span ℝ (recCone S)
  have hfree : IsLambdaFree Λ V (S + (K : Set (EuclideanSpace ℝ (Fin n)))) :=
    lambdaFree_add_span_recCone Λ V hΛ S hS.1
  have heq : S + (K : Set (EuclideanSpace ℝ (Fin n))) = S := by
    apply hS.2 _ hfree
    intro x hx
    exact ⟨x, hx, 0, K.zero_mem, by simp⟩
  apply Set.Subset.antisymm
  · intro r hr
    exact hr.1
  · intro r hr
    refine ⟨hr, ?_⟩
    intro x hx t ht
    rw [← heq]
    exact ⟨x, hx, t • (-r), K.smul_mem t (K.neg_mem (Submodule.subset_span hr)), rfl⟩
