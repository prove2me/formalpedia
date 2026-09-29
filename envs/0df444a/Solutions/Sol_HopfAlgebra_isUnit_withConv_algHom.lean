-- Prove2me | solution 1 for HopfAlgebra.isUnit_withConv_algHom
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.85352+00:00
-- url     : https://prove2.me/submissions/ac1f239e-e6c3-5416-8e52-3bf369031a6d

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_HopfAlgebra_isUnit_withConv_algHom

p2m_open "Coalgebra HopfAlgebra P2MW.S_HopfAlgebra_isUnit_withConv_algHom.HopfAlgebra"
p2m_open_scoped "TensorProduct Coalgebra.TensorProduct"

namespace HopfAlgebra
p2m_export "HopfAlgebra" "sum_mul_antipode_eq_algebraMap_counit antipode_one antipode_mul sum_antipode_mul_eq_algebraMap_counit"
p2m_open "HopfAlgebra"

section
variable {R : Type*} [CommSemiring R] {A : Type*} [CommSemiring A] [HopfAlgebra R A]

private noncomputable def antipodeAlgHom' : A →ₐ[R] A where
  toFun := antipode R
  map_one' := antipode_one
  map_mul' a b := by rw [antipode_mul]; exact mul_comm _ _
  map_zero' := map_zero _
  map_add' := map_add _
  commutes' r := by rw [Algebra.algebraMap_eq_smul_one, map_smul, antipode_one]

@[scoped simp] private lemma antipodeAlgHom'_apply (a : A) :
    antipodeAlgHom' (R := R) a = antipode R a := rfl

variable {L : Type*} [CommSemiring L] [Algebra R L]

private theorem convMul_comp_antipode_right (φ : A →ₐ[R] L) :
    WithConv.toConv φ * WithConv.toConv (φ.comp antipodeAlgHom') = 1 := by
  refine WithConv.ext (AlgHom.ext fun a => ?_)
  simp only [AlgHom.convMul_def, AlgHom.convOne_def, WithConv.ofConv_toConv,
    AlgHom.coe_comp, Function.comp_apply,
    Bialgebra.comulAlgHom_apply, Bialgebra.counitAlgHom_apply, Algebra.ofId_apply]
  rw [← (ℛ R a).eq]
  simp only [map_sum, Algebra.TensorProduct.map_tmul, Algebra.TensorProduct.lmul'_apply_tmul,
    antipodeAlgHom'_apply]
  calc ∑ i ∈ (ℛ R a).index, φ ((ℛ R a).left i) * φ (antipode R ((ℛ R a).right i))
      = φ (∑ i ∈ (ℛ R a).index, (ℛ R a).left i * antipode R ((ℛ R a).right i)) := by
        rw [map_sum]; exact Finset.sum_congr rfl fun i _ => (φ.map_mul _ _).symm
    _ = φ (algebraMap R A (counit (R := R) a)) := by
        rw [sum_mul_antipode_eq_algebraMap_counit (ℛ R a)]
    _ = algebraMap R L (counit (R := R) a) := φ.commutes _

private theorem convMul_comp_antipode_left (φ : A →ₐ[R] L) :
    WithConv.toConv (φ.comp antipodeAlgHom') * WithConv.toConv φ = 1 := by
  refine WithConv.ext (AlgHom.ext fun a => ?_)
  simp only [AlgHom.convMul_def, AlgHom.convOne_def, WithConv.ofConv_toConv,
    AlgHom.coe_comp, Function.comp_apply,
    Bialgebra.comulAlgHom_apply, Bialgebra.counitAlgHom_apply, Algebra.ofId_apply]
  rw [← (ℛ R a).eq]
  simp only [map_sum, Algebra.TensorProduct.map_tmul, Algebra.TensorProduct.lmul'_apply_tmul,
    antipodeAlgHom'_apply]
  calc ∑ i ∈ (ℛ R a).index, φ (antipode R ((ℛ R a).left i)) * φ ((ℛ R a).right i)
      = φ (∑ i ∈ (ℛ R a).index, antipode R ((ℛ R a).left i) * (ℛ R a).right i) := by
        rw [map_sum]; exact Finset.sum_congr rfl fun i _ => (φ.map_mul _ _).symm
    _ = φ (algebraMap R A (counit (R := R) a)) := by
        rw [sum_antipode_mul_eq_algebraMap_counit (ℛ R a)]
    _ = algebraMap R L (counit (R := R) a) := φ.commutes _

end
end HopfAlgebra
p2m_reactivate "P2MW.S_HopfAlgebra_isUnit_withConv_algHom.HopfAlgebra"

theorem solution
    {R : Type*} [CommSemiring R] {A : Type*} [CommSemiring A] [HopfAlgebra R A]
    {L : Type*} [CommSemiring L] [Algebra R L]
    (φ : WithConv (A →ₐ[R] L)) : IsUnit φ := by
  refine ⟨⟨φ, WithConv.toConv ((WithConv.ofConv φ).comp HopfAlgebra.antipodeAlgHom'), ?_, ?_⟩, rfl⟩
  · have h := HopfAlgebra.convMul_comp_antipode_right (R := R) (WithConv.ofConv φ)
    rwa [WithConv.toConv_ofConv] at h
  · have h := HopfAlgebra.convMul_comp_antipode_left (R := R) (WithConv.ofConv φ)
    rwa [WithConv.toConv_ofConv] at h

end S_HopfAlgebra_isUnit_withConv_algHom
end P2MW
export P2MW.S_HopfAlgebra_isUnit_withConv_algHom (solution)
