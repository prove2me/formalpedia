-- Prove2me | solution 1 for HopfAlgebra.comul_antipode
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.85352+00:00
-- url     : https://prove2.me/submissions/c2102578-d1db-57b0-86ee-4259dc7484c2

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_HopfAlgebra_comul_antipode

set_option autoImplicit false
set_option maxHeartbeats 3200000

p2m_open "Coalgebra HopfAlgebra P2MW.S_HopfAlgebra_comul_antipode.HopfAlgebra WithConv"
p2m_open_scoped "TensorProduct Coalgebra.TensorProduct"

universe u v

namespace HopfAlgebra
p2m_export "HopfAlgebra" "sum_mul_antipode_eq_algebraMap_counit sum_antipode_mul_eq_algebraMap_counit"
p2m_open "HopfAlgebra"

noncomputable section

variable {R : Type u} [CommSemiring R]
variable {A : Type v} [Semiring A] [HopfAlgebra R A]

theorem toConv_includeLeft_comp_antipode_mul_toConv_includeLeft :
    toConv ((Algebra.TensorProduct.includeLeft : A →ₐ[R] A ⊗[R] A).toLinearMap ∘ₗ antipode R)
        * toConv (Algebra.TensorProduct.includeLeft : A →ₐ[R] A ⊗[R] A).toLinearMap
      = (1 : WithConv (A →ₗ[R] A ⊗[R] A)) := by
  refine WithConv.ext (LinearMap.ext fun a => ?_)
  simp only [LinearMap.convMul_def, LinearMap.convOne_def, WithConv.ofConv_toConv,
    LinearMap.comp_apply, Algebra.linearMap_apply]
  rw [← (ℛ R a).eq]
  simp only [map_sum, TensorProduct.map_tmul, LinearMap.mul'_apply, LinearMap.comp_apply,
    AlgHom.toLinearMap_apply, Algebra.TensorProduct.includeLeft_apply,
    Algebra.TensorProduct.tmul_mul_tmul, mul_one]
  rw [Algebra.TensorProduct.algebraMap_apply, ← sum_antipode_mul_eq_algebraMap_counit (ℛ R a)]
  exact (TensorProduct.sum_tmul _ _ _).symm

theorem toConv_includeRight_comp_antipode_mul_toConv_includeRight :
    toConv ((Algebra.TensorProduct.includeRight : A →ₐ[R] A ⊗[R] A).toLinearMap ∘ₗ antipode R)
        * toConv (Algebra.TensorProduct.includeRight : A →ₐ[R] A ⊗[R] A).toLinearMap
      = (1 : WithConv (A →ₗ[R] A ⊗[R] A)) := by
  refine WithConv.ext (LinearMap.ext fun a => ?_)
  simp only [LinearMap.convMul_def, LinearMap.convOne_def, WithConv.ofConv_toConv,
    LinearMap.comp_apply, Algebra.linearMap_apply]
  rw [← (ℛ R a).eq]
  simp only [map_sum, TensorProduct.map_tmul, LinearMap.mul'_apply, LinearMap.comp_apply,
    AlgHom.toLinearMap_apply, Algebra.TensorProduct.includeRight_apply,
    Algebra.TensorProduct.tmul_mul_tmul, one_mul]
  rw [Algebra.TensorProduct.algebraMap_apply', ← sum_antipode_mul_eq_algebraMap_counit (ℛ R a)]
  exact (TensorProduct.tmul_sum _ _ _).symm

theorem toConv_includeLeft_mul_toConv_includeRight :
    toConv (Algebra.TensorProduct.includeLeft : A →ₐ[R] A ⊗[R] A).toLinearMap
        * toConv (Algebra.TensorProduct.includeRight : A →ₐ[R] A ⊗[R] A).toLinearMap
      = toConv (comul : A →ₗ[R] A ⊗[R] A) := by
  refine WithConv.ext (LinearMap.ext fun a => ?_)
  simp only [LinearMap.convMul_def, WithConv.ofConv_toConv, LinearMap.comp_apply]
  rw [← (ℛ R a).eq]
  simp only [map_sum, TensorProduct.map_tmul, LinearMap.mul'_apply, AlgHom.toLinearMap_apply,
    Algebra.TensorProduct.includeLeft_apply, Algebra.TensorProduct.includeRight_apply,
    Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]

theorem toConv_includeRight_comp_antipode_mul_toConv_includeLeft_comp_antipode :
    toConv ((Algebra.TensorProduct.includeRight : A →ₐ[R] A ⊗[R] A).toLinearMap ∘ₗ antipode R)
        * toConv
            ((Algebra.TensorProduct.includeLeft : A →ₐ[R] A ⊗[R] A).toLinearMap ∘ₗ antipode R)
      = toConv ((TensorProduct.comm R A A).toLinearMap
          ∘ₗ TensorProduct.map (antipode R) (antipode R) ∘ₗ comul) := by
  refine WithConv.ext (LinearMap.ext fun a => ?_)
  simp only [LinearMap.convMul_def, WithConv.ofConv_toConv, LinearMap.comp_apply]
  rw [← (ℛ R a).eq]
  simp only [map_sum, TensorProduct.map_tmul, LinearMap.mul'_apply, LinearMap.comp_apply,
    AlgHom.toLinearMap_apply, Algebra.TensorProduct.includeLeft_apply,
    Algebra.TensorProduct.includeRight_apply, Algebra.TensorProduct.tmul_mul_tmul, mul_one,
    one_mul, LinearEquiv.coe_toLinearMap, TensorProduct.comm_tmul]

theorem toConv_comm_map_antipode_comul_mul_toConv_comul :
    toConv ((TensorProduct.comm R A A).toLinearMap
          ∘ₗ TensorProduct.map (antipode R) (antipode R) ∘ₗ comul)
        * toConv (comul : A →ₗ[R] A ⊗[R] A)
      = (1 : WithConv (A →ₗ[R] A ⊗[R] A)) := by
  rw [← toConv_includeRight_comp_antipode_mul_toConv_includeLeft_comp_antipode,
    ← toConv_includeLeft_mul_toConv_includeRight, mul_assoc,
    ← mul_assoc (toConv
      ((Algebra.TensorProduct.includeLeft : A →ₐ[R] A ⊗[R] A).toLinearMap ∘ₗ antipode R)),
    toConv_includeLeft_comp_antipode_mul_toConv_includeLeft, one_mul]
  exact toConv_includeRight_comp_antipode_mul_toConv_includeRight

theorem toConv_comul_mul_toConv_comul_comp_antipode :
    toConv (comul : A →ₗ[R] A ⊗[R] A)
        * toConv (comul ∘ₗ antipode R : A →ₗ[R] A ⊗[R] A)
      = (1 : WithConv (A →ₗ[R] A ⊗[R] A)) := by
  refine WithConv.ext (LinearMap.ext fun a => ?_)
  simp only [LinearMap.convMul_def, LinearMap.convOne_def, WithConv.ofConv_toConv,
    LinearMap.comp_apply, Algebra.linearMap_apply]
  rw [← (ℛ R a).eq]
  simp only [map_sum, TensorProduct.map_tmul, LinearMap.mul'_apply, LinearMap.comp_apply,
    ← Bialgebra.comul_mul]
  rw [show ∑ i ∈ (ℛ R a).index,
        comul (R := R) ((ℛ R a).left i * antipode R ((ℛ R a).right i))
      = comul (R := R) (∑ i ∈ (ℛ R a).index, (ℛ R a).left i * antipode R ((ℛ R a).right i)) from
      (map_sum _ _ _).symm,
    sum_mul_antipode_eq_algebraMap_counit (ℛ R a), Bialgebra.comul_algebraMap]

theorem comul_comp_antipode :
    comul ∘ₗ antipode R
      = (TensorProduct.comm R A A).toLinearMap
          ∘ₗ TensorProduct.map (antipode R) (antipode R) ∘ₗ comul :=
  (WithConv.toConv_injective
    (left_inv_eq_right_inv
      (toConv_comm_map_antipode_comul_mul_toConv_comul (R := R) (A := A))
      (toConv_comul_mul_toConv_comul_comp_antipode (R := R) (A := A)))).symm

end
end HopfAlgebra

open scoped _root_.TensorProduct _root_.Coalgebra.TensorProduct in
theorem solution {R : Type*} [CommSemiring R]
    {A : Type*} [Semiring A] [HopfAlgebra R A] (a : A) :
    Coalgebra.comul (HopfAlgebra.antipode R a)
      = TensorProduct.comm R A A
          (TensorProduct.map (HopfAlgebra.antipode R) (HopfAlgebra.antipode R)
            (Coalgebra.comul a)) := by
  have h := LinearMap.congr_fun (HopfAlgebra.comul_comp_antipode (R := R) (A := A)) a
  simpa only [LinearMap.comp_apply, LinearEquiv.coe_toLinearMap] using h

end S_HopfAlgebra_comul_antipode
end P2MW
export P2MW.S_HopfAlgebra_comul_antipode (solution)
