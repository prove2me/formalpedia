-- Prove2me | solution 1 for HopfOrder.antipode_mem_sup
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.85352+00:00
-- url     : https://prove2.me/submissions/299e66a6-7550-5826-b9e6-e7b8d7ff9f5f

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_HopfOrder_antipode_mem_sup

set_option autoImplicit false
set_option maxHeartbeats 800000

universe u v w

open scoped TensorProduct

theorem solution
    {R : Type u} [CommRing R] {K : Type v} [Field K] [Algebra R K]
    {A : Type w} [CommRing A] [HopfAlgebra K A] [Algebra R A] [IsScalarTower R K A] {S S' : Subalgebra R A}
    (hS : ∀ x ∈ S, HopfAlgebra.antipode K x ∈ S) (hS' : ∀ x ∈ S', HopfAlgebra.antipode K x ∈ S') :
    ∀ x ∈ S ⊔ S', HopfAlgebra.antipode K x ∈ S ⊔ S' := by
  let T : Subalgebra R A :=
    { carrier := {x | HopfAlgebra.antipode K x ∈ S ⊔ S'}
      mul_mem' := by
        intro a b ha hb
        show HopfAlgebra.antipode K (a * b) ∈ S ⊔ S'
        rw [HopfAlgebra.antipode_mul]
        exact Subalgebra.mul_mem _ hb ha
      one_mem' := by
        show HopfAlgebra.antipode K (1 : A) ∈ S ⊔ S'
        rw [HopfAlgebra.antipode_one]
        exact Subalgebra.one_mem _
      add_mem' := by
        intro a b ha hb
        show HopfAlgebra.antipode K (a + b) ∈ S ⊔ S'
        rw [map_add]
        exact Subalgebra.add_mem _ ha hb
      zero_mem' := by
        show HopfAlgebra.antipode K (0 : A) ∈ S ⊔ S'
        rw [map_zero]
        exact Subalgebra.zero_mem _
      algebraMap_mem' := by
        intro r
        show HopfAlgebra.antipode K (algebraMap R A r) ∈ S ⊔ S'
        have h1 : algebraMap R A r = algebraMap R K r • (1 : A) := by
          rw [IsScalarTower.algebraMap_apply R K A, Algebra.algebraMap_eq_smul_one]
        rw [h1, map_smul, HopfAlgebra.antipode_one, ← h1]
        exact Subalgebra.algebraMap_mem _ r }
  have key : S ⊔ S' ≤ T := sup_le (fun y hy => (le_sup_left : S ≤ S ⊔ S') (hS y hy))
    (fun y hy => (le_sup_right : S' ≤ S ⊔ S') (hS' y hy))
  intro x hx
  exact key hx

end S_HopfOrder_antipode_mem_sup
end P2MW
export P2MW.S_HopfOrder_antipode_mem_sup (solution)
