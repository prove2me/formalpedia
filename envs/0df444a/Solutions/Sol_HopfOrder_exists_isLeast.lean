-- Prove2me | solution 1 for HopfOrder.exists_isLeast
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.85352+00:00
-- url     : https://prove2.me/submissions/c0cd6efa-e2d3-5602-ab49-3626e4f6d610

import Mathlib
import Definitions.Def_HopfAlgebra_CartierDual
import Theorems.Thm_HopfOrder_exists_isGreatest
import Theorems.Thm_HopfOrder_exists_dual_hopfOrder
import Theorems.Thm_HopfOrder_exists_predual_hopfOrder
import Theorems.Thm_HopfOrder_mem_of_forall_mem_dual_apply_mem_range
import Theorems.Thm_HopfAlgebra_algebra_etale_of_module_finite_of_charZero
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_HopfOrder_exists_isLeast

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1600000

open scoped TensorProduct

theorem solution
    {R : Type*} [CommRing R] [IsDomain R] [IsPrincipalIdealRing R]
    {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K] [CharZero K]
    {A : Type*} [CommRing A] [HopfAlgebra K A] [Algebra R A] [IsScalarTower R K A]
    [Module.Finite K A] [Coalgebra.IsCocomm K A]
    (S : Subalgebra R A)
    (hfin : Module.Finite R ↥S) (hspan : Submodule.span K (S : Set A) = ⊤)
    (hcomul : ∀ x ∈ S, Coalgebra.comul (R := K) x ∈
        (Algebra.TensorProduct.productMap
          (((Algebra.TensorProduct.includeLeft : A →ₐ[K] A ⊗[K] A).restrictScalars R).comp S.val)
          (((Algebra.TensorProduct.includeRight : A →ₐ[K] A ⊗[K] A).restrictScalars R).comp S.val)).range)
    (hanti : ∀ x ∈ S, HopfAlgebra.antipode K (A := A) x ∈ S)
    (hcounit : ∀ x ∈ S, Coalgebra.counit (R := K) (A := A) x ∈ (algebraMap R K).range) :
    ∃ Smin : Subalgebra R A, (Module.Finite R ↥Smin ∧ Submodule.span K (Smin : Set A) = ⊤ ∧
        (∀ x ∈ Smin, Coalgebra.comul (R := K) x ∈
          (Algebra.TensorProduct.productMap
            (((Algebra.TensorProduct.includeLeft : A →ₐ[K] A ⊗[K] A).restrictScalars R).comp Smin.val)
            (((Algebra.TensorProduct.includeRight : A →ₐ[K] A ⊗[K] A).restrictScalars R).comp Smin.val)).range) ∧
        (∀ x ∈ Smin, HopfAlgebra.antipode K (A := A) x ∈ Smin) ∧
        (∀ x ∈ Smin, Coalgebra.counit (R := K) (A := A) x ∈ (algebraMap R K).range)) ∧
      ∀ T : Subalgebra R A, (Module.Finite R ↥T ∧ Submodule.span K (T : Set A) = ⊤ ∧
        (∀ x ∈ T, Coalgebra.comul (R := K) x ∈
          (Algebra.TensorProduct.productMap
            (((Algebra.TensorProduct.includeLeft : A →ₐ[K] A ⊗[K] A).restrictScalars R).comp T.val)
            (((Algebra.TensorProduct.includeRight : A →ₐ[K] A ⊗[K] A).restrictScalars R).comp T.val)).range) ∧
        (∀ x ∈ T, HopfAlgebra.antipode K (A := A) x ∈ T) ∧
        (∀ x ∈ T, Coalgebra.counit (R := K) (A := A) x ∈ (algebraMap R K).range)) → Smin ≤ T := by
  classical

  letI algRD : Algebra R (CartierDual K A) := Algebra.compHom (CartierDual K A) (algebraMap R K)
  haveI : IsScalarTower R K (CartierDual K A) := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  haveI : Algebra.Etale K (CartierDual K A) := HopfAlgebra.algebra_etale_of_module_finite_of_charZero K (CartierDual K A)

  obtain ⟨S', -, hS'fin, hS'span, hS'comul, hS'anti, hS'counit⟩ :=
    HopfOrder.exists_dual_hopfOrder S hfin hspan hcomul hanti hcounit

  obtain ⟨Tmax, ⟨hTfin, hTspan, hTcomul, hTanti, hTcounit⟩, hTmax⟩ :=
    HopfOrder.exists_isGreatest (K := K) (A := CartierDual K A) S' hS'fin hS'span hS'comul hS'anti hS'counit

  obtain ⟨Smin, hSmin, h1, h2, h3, h4, h5⟩ :=
    HopfOrder.exists_predual_hopfOrder (K := K) (A := A) Tmax hTfin hTspan hTcomul hTanti hTcounit
  refine ⟨Smin, ⟨h1, h2, h3, h4, h5⟩, ?_⟩

  rintro T ⟨hTf, hTs, hTc, hTa, hTu⟩
  obtain ⟨Td, hTdmem, hTdfin, hTdspan, hTdcomul, hTdanti, hTdcounit⟩ :=
    HopfOrder.exists_dual_hopfOrder T hTf hTs hTc hTa hTu
  have hle : Td ≤ Tmax := hTmax Td ⟨hTdfin, hTdspan, hTdcomul, hTdanti, hTdcounit⟩
  intro a ha
  apply HopfOrder.mem_of_forall_mem_dual_apply_mem_range T hTf hTs Td hTdmem
  intro φ hφ
  exact (hSmin a).mp ha φ (hle hφ)

end S_HopfOrder_exists_isLeast
end P2MW
export P2MW.S_HopfOrder_exists_isLeast (solution)
