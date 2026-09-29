-- Prove2me | solution 1 for HopfOrder.exists_isGreatest
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.85352+00:00
-- url     : https://prove2.me/submissions/3e6e9d2c-6db9-507a-97aa-23b2cd4dad5d

import Mathlib
import Theorems.Thm_HopfOrder_comul_mem_range_sup
import Theorems.Thm_HopfOrder_antipode_mem_sup
import Theorems.Thm_HopfOrder_counit_mem_range_sup
import Theorems.Thm_HopfOrder_finite_sup_and_span_sup_eq_top
import Theorems.Thm_HopfOrder_le_integralClosure_of_finite
import Theorems.Thm_HopfOrder_exists_greatest_of_sup_closed_of_le_noetherian
import Theorems.Thm_HopfOrder_integralClosure_finite_of_etale
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_HopfOrder_exists_isGreatest

set_option autoImplicit false

open scoped TensorProduct

theorem solution
    {R : Type*} [CommRing R] [IsDomain R] [IsIntegrallyClosed R] [IsNoetherianRing R]
    {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K]
    {A : Type*} [CommRing A] [HopfAlgebra K A] [Algebra R A] [IsScalarTower R K A] [Algebra.Etale K A]
    (S : Subalgebra R A)
    (hfin : Module.Finite R ↥S) (hspan : Submodule.span K (S : Set A) = ⊤)
    (hcomul : ∀ x ∈ S, Coalgebra.comul (R := K) x ∈
        (Algebra.TensorProduct.productMap
          (((Algebra.TensorProduct.includeLeft : A →ₐ[K] A ⊗[K] A).restrictScalars R).comp S.val)
          (((Algebra.TensorProduct.includeRight : A →ₐ[K] A ⊗[K] A).restrictScalars R).comp S.val)).range)
    (hanti : ∀ x ∈ S, HopfAlgebra.antipode K (A := A) x ∈ S)
    (hcounit : ∀ x ∈ S, Coalgebra.counit (R := K) (A := A) x ∈ (algebraMap R K).range) :
    ∃ Smax : Subalgebra R A, (Module.Finite R ↥Smax ∧ Submodule.span K (Smax : Set A) = ⊤ ∧
        (∀ x ∈ Smax, Coalgebra.comul (R := K) x ∈
          (Algebra.TensorProduct.productMap
            (((Algebra.TensorProduct.includeLeft : A →ₐ[K] A ⊗[K] A).restrictScalars R).comp Smax.val)
            (((Algebra.TensorProduct.includeRight : A →ₐ[K] A ⊗[K] A).restrictScalars R).comp Smax.val)).range) ∧
        (∀ x ∈ Smax, HopfAlgebra.antipode K (A := A) x ∈ Smax) ∧
        (∀ x ∈ Smax, Coalgebra.counit (R := K) (A := A) x ∈ (algebraMap R K).range)) ∧
      ∀ T : Subalgebra R A, (Module.Finite R ↥T ∧ Submodule.span K (T : Set A) = ⊤ ∧
        (∀ x ∈ T, Coalgebra.comul (R := K) x ∈
          (Algebra.TensorProduct.productMap
            (((Algebra.TensorProduct.includeLeft : A →ₐ[K] A ⊗[K] A).restrictScalars R).comp T.val)
            (((Algebra.TensorProduct.includeRight : A →ₐ[K] A ⊗[K] A).restrictScalars R).comp T.val)).range) ∧
        (∀ x ∈ T, HopfAlgebra.antipode K (A := A) x ∈ T) ∧
        (∀ x ∈ T, Coalgebra.counit (R := K) (A := A) x ∈ (algebraMap R K).range)) → T ≤ Smax := by
  haveI : Module.Finite R ↥(integralClosure R A) := HopfOrder.integralClosure_finite_of_etale (K := K)
  obtain ⟨Smax, hPmax, hmax⟩ := HopfOrder.exists_greatest_of_sup_closed_of_le_noetherian
    (fun T : Subalgebra R A => Module.Finite R ↥T ∧ Submodule.span K (T : Set A) = ⊤ ∧
        (∀ x ∈ T, Coalgebra.comul (R := K) x ∈
          (Algebra.TensorProduct.productMap
            (((Algebra.TensorProduct.includeLeft : A →ₐ[K] A ⊗[K] A).restrictScalars R).comp T.val)
            (((Algebra.TensorProduct.includeRight : A →ₐ[K] A ⊗[K] A).restrictScalars R).comp T.val)).range) ∧
        (∀ x ∈ T, HopfAlgebra.antipode K (A := A) x ∈ T) ∧
        (∀ x ∈ T, Coalgebra.counit (R := K) (A := A) x ∈ (algebraMap R K).range))
    (fun T T' hT hT' => by
      obtain ⟨hf, hs, hc, ha, hu⟩ := hT
      obtain ⟨hf', hs', hc', ha', hu'⟩ := hT'
      haveI : Module.Finite R ↥T := hf
      haveI : Module.Finite R ↥T' := hf'
      obtain ⟨h1, h2⟩ := HopfOrder.finite_sup_and_span_sup_eq_top (K := K) (S := T) (S' := T') hs
      exact ⟨h1, h2, HopfOrder.comul_mem_range_sup hc hc', HopfOrder.antipode_mem_sup ha ha',
        HopfOrder.counit_mem_range_sup hu hu'⟩)
    (integralClosure R A)
    (fun T hT => by
      haveI : Module.Finite R ↥T := hT.1
      exact HopfOrder.le_integralClosure_of_finite T)
    ⟨S, hfin, hspan, hcomul, hanti, hcounit⟩
  exact ⟨Smax, hPmax, hmax⟩

end S_HopfOrder_exists_isGreatest
end P2MW
export P2MW.S_HopfOrder_exists_isGreatest (solution)
