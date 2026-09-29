-- Prove2me | solution 1 for HopfAlgebra.antipode_antipode
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.85352+00:00
-- url     : https://prove2.me/submissions/86b9e643-a07e-5136-abd6-974721366f4e

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_HopfAlgebra_antipode_antipode

p2m_open "Coalgebra HopfAlgebra P2MW.S_HopfAlgebra_antipode_antipode.HopfAlgebra"
p2m_open_scoped "TensorProduct Coalgebra.TensorProduct"

namespace HopfAlgebra
p2m_export "HopfAlgebra" "antipode_one antipode_mul sum_antipode_mul_eq_algebraMap_counit"
p2m_open "HopfAlgebra"

section GeneralHopf
variable {R : Type*} [CommSemiring R] {A : Type*} [Semiring A] [HopfAlgebra R A]

private theorem antipode_algebraMap' (r : R) :
    antipode R (algebraMap R A r) = algebraMap R A r := by
  rw [Algebra.algebraMap_eq_smul_one, map_smul, antipode_one]

private theorem toConv_antipode_mul_toConv_id' :
    WithConv.toConv (antipode R (A := A)) * WithConv.toConv (LinearMap.id : A →ₗ[R] A)
      = (1 : WithConv (A →ₗ[R] A)) := by
  refine WithConv.ext (LinearMap.ext fun a => ?_)
  simp only [LinearMap.convMul_def, LinearMap.convOne_def, WithConv.ofConv_toConv,
    LinearMap.comp_apply, Algebra.linearMap_apply]
  rw [← (ℛ R a).eq]
  simp only [map_sum, TensorProduct.map_tmul, LinearMap.mul'_apply, LinearMap.id_coe, id_eq]
  exact sum_antipode_mul_eq_algebraMap_counit (ℛ R a)

end GeneralHopf

section CommutativeHopf
variable {R : Type*} [CommSemiring R] {A : Type*} [CommSemiring A] [HopfAlgebra R A]

private theorem sum_antipode_antipode_mul_antipode' {a : A} {ι𝓡 : Type*} (𝓡 : Coalgebra.Repr R a ι𝓡) :
    ∑ i ∈ 𝓡.index, antipode R (antipode R (𝓡.left i)) * antipode R (𝓡.right i)
      = algebraMap R A (counit (R := R) a) := by
  calc ∑ i ∈ 𝓡.index, antipode R (antipode R (𝓡.left i)) * antipode R (𝓡.right i)
      = ∑ i ∈ 𝓡.index, antipode R (antipode R (𝓡.left i) * 𝓡.right i) := by
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [antipode_mul (antipode R (𝓡.left i)) (𝓡.right i)]
        exact mul_comm _ _
    _ = antipode R (∑ i ∈ 𝓡.index, antipode R (𝓡.left i) * 𝓡.right i) := by
        rw [map_sum]
    _ = antipode R (algebraMap R A (counit (R := R) a)) := by
        rw [sum_antipode_mul_eq_algebraMap_counit 𝓡]
    _ = algebraMap R A (counit (R := R) a) := antipode_algebraMap' _

private theorem toConv_antipode_comp_antipode_mul_toConv_antipode' :
    WithConv.toConv (antipode R ∘ₗ antipode R : A →ₗ[R] A)
        * WithConv.toConv (antipode R (A := A))
      = (1 : WithConv (A →ₗ[R] A)) := by
  refine WithConv.ext (LinearMap.ext fun a => ?_)
  simp only [LinearMap.convMul_def, LinearMap.convOne_def, WithConv.ofConv_toConv,
    LinearMap.comp_apply, Algebra.linearMap_apply]
  rw [← (ℛ R a).eq]
  simp only [map_sum, TensorProduct.map_tmul, LinearMap.mul'_apply, LinearMap.comp_apply]
  exact sum_antipode_antipode_mul_antipode' (ℛ R a)

private theorem antipode_comp_antipode' :
    (antipode R ∘ₗ antipode R : A →ₗ[R] A) = LinearMap.id :=
  WithConv.toConv_injective
    (left_inv_eq_right_inv toConv_antipode_comp_antipode_mul_toConv_antipode'
      toConv_antipode_mul_toConv_id')

end CommutativeHopf
end HopfAlgebra

theorem solution {R : Type*} [CommSemiring R]
    {A : Type*} [CommSemiring A] [HopfAlgebra R A] (a : A) :
    HopfAlgebra.antipode R (HopfAlgebra.antipode R a) = a := by
  simpa only [LinearMap.comp_apply, LinearMap.id_apply] using
    LinearMap.congr_fun (HopfAlgebra.antipode_comp_antipode' (R := R) (A := A)) a

end S_HopfAlgebra_antipode_antipode
end P2MW
export P2MW.S_HopfAlgebra_antipode_antipode (solution)
