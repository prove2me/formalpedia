-- Prove2me | solution 1 for HopfOrder.map_eq_of_forall_le
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.85352+00:00
-- url     : https://prove2.me/submissions/90719d02-f92d-5063-bfc4-908e9d335fe1

import Mathlib
import Definitions.Def_HopfAlgebra_HopfOrderData
import Definitions.Def_HopfAlgebra_FVectStructure
import Theorems.Thm_HopfOrder_isHopfOrder_map
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_HopfOrder_map_eq_of_forall_le

set_option autoImplicit false

open scoped TensorProduct

theorem solution
    {R : Type*} [CommRing R] [IsDomain R] [IsPrincipalIdealRing R]
    {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K]
    {A : Type*} [CommRing A] [HopfAlgebra K A] [Algebra R A] [IsScalarTower R K A]
    (S : Subalgebra R A)
    (hfin : Module.Finite R ↥S) (hspan : Submodule.span K (S : Set A) = ⊤)
    (hcomul : ∀ x ∈ S, Coalgebra.comul (R := K) x ∈
        (Algebra.TensorProduct.productMap
          (((Algebra.TensorProduct.includeLeft : A →ₐ[K] A ⊗[K] A).restrictScalars R).comp S.val)
          (((Algebra.TensorProduct.includeRight : A →ₐ[K] A ⊗[K] A).restrictScalars R).comp S.val)).range)
    (hanti : ∀ x ∈ S, HopfAlgebra.antipode K (A := A) x ∈ S)
    (hcounit : ∀ x ∈ S, Coalgebra.counit (R := K) (A := A) x ∈ (algebraMap R K).range)
    (hmax : ∀ T : Subalgebra R A, (Module.Finite R ↥T ∧ Submodule.span K (T : Set A) = ⊤ ∧
        (∀ x ∈ T, Coalgebra.comul (R := K) x ∈
          (Algebra.TensorProduct.productMap
            (((Algebra.TensorProduct.includeLeft : A →ₐ[K] A ⊗[K] A).restrictScalars R).comp T.val)
            (((Algebra.TensorProduct.includeRight : A →ₐ[K] A ⊗[K] A).restrictScalars R).comp T.val)).range) ∧
        (∀ x ∈ T, HopfAlgebra.antipode K (A := A) x ∈ T) ∧
        (∀ x ∈ T, Coalgebra.counit (R := K) (A := A) x ∈ (algebraMap R K).range)) → T ≤ S)
    (σ : A ≃ₐc[K] A) :
    S.map (((σ : A →ₐc[K] A) : A →ₐ[K] A).restrictScalars R) = S := by
  have himg : ∀ τ : A ≃ₐc[K] A, (Module.Finite R ↥(S.map (((τ : A →ₐc[K] A) : A →ₐ[K] A).restrictScalars R)) ∧ Submodule.span K ((S.map (((τ : A →ₐc[K] A) : A →ₐ[K] A).restrictScalars R)) : Set A) = ⊤ ∧
        (∀ x ∈ (S.map (((τ : A →ₐc[K] A) : A →ₐ[K] A).restrictScalars R)), Coalgebra.comul (R := K) x ∈
          (Algebra.TensorProduct.productMap
            (((Algebra.TensorProduct.includeLeft : A →ₐ[K] A ⊗[K] A).restrictScalars R).comp (S.map (((τ : A →ₐc[K] A) : A →ₐ[K] A).restrictScalars R)).val)
            (((Algebra.TensorProduct.includeRight : A →ₐ[K] A ⊗[K] A).restrictScalars R).comp (S.map (((τ : A →ₐc[K] A) : A →ₐ[K] A).restrictScalars R)).val)).range) ∧
        (∀ x ∈ (S.map (((τ : A →ₐc[K] A) : A →ₐ[K] A).restrictScalars R)), HopfAlgebra.antipode K (A := A) x ∈ (S.map (((τ : A →ₐc[K] A) : A →ₐ[K] A).restrictScalars R))) ∧
        (∀ x ∈ (S.map (((τ : A →ₐc[K] A) : A →ₐ[K] A).restrictScalars R)), Coalgebra.counit (R := K) (A := A) x ∈ (algebraMap R K).range)) := by
    intro τ
    have hsurj : Function.Surjective (τ : A →ₐc[K] A) := fun y => ⟨τ.symm y, by simp⟩
    exact HopfOrder.isHopfOrder_map S hfin hspan hcomul hanti hcounit (τ : A →ₐc[K] A) hsurj

  have hmapmap : ∀ (τ τ' : A ≃ₐc[K] A) (x : A), x ∈ S → (∀ y, τ (τ' y) = y) →
      x ∈ (S.map (((τ' : A →ₐc[K] A) : A →ₐ[K] A).restrictScalars R)).map
        (((τ : A →ₐc[K] A) : A →ₐ[K] A).restrictScalars R) := by
    intro τ τ' x hx hinv
    refine Subalgebra.mem_map.mpr ⟨τ' x, Subalgebra.mem_map.mpr ⟨x, hx, rfl⟩, ?_⟩
    simpa using hinv x
  apply le_antisymm
  · exact hmax _ (himg σ)
  ·
    intro x hx
    have h1 := hmapmap σ σ.symm x hx (fun y => by simp)
    exact Subalgebra.map_mono (hmax _ (himg σ.symm)) h1

end S_HopfOrder_map_eq_of_forall_le
end P2MW
export P2MW.S_HopfOrder_map_eq_of_forall_le (solution)
