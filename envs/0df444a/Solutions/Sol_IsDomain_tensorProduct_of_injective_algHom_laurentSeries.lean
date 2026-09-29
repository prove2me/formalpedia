-- Prove2me | solution 1 for IsDomain.tensorProduct_of_injective_algHom_laurentSeries
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.85352+00:00
-- url     : https://prove2.me/submissions/efd9d0a6-6e41-535f-bda0-c98a7c8f2867

import Mathlib
import Theorems.Thm_IntermediateField_isDomain_tensorProduct_of_le_laurentSeries
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_IsDomain_tensorProduct_of_injective_algHom_laurentSeries
p2m_attr_erase "simp" "ModularCurve.coeffEmb_coeff ModularCurve.coeffMap_coeff ModularCurve.coeffMap_id ModularCurve.coeffMap_single"

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 3200000

open scoped TensorProduct

theorem solution
    (A : Type*) [CommRing A] [IsDomain A]
    (K : Type*) [Field K] [Algebra A K] [IsFractionRing A K]
    (D : Type*) [CommRing D] [Nontrivial D] [Algebra A D]
    (φ : D →ₐ[A] LaurentSeries K) (hφ : Function.Injective φ)
    (L : Type*) [Field L] [Algebra K L] [Algebra A L] [IsScalarTower A K L] :
    IsDomain (L ⊗[A] D) := by
  classical

  let E : IntermediateField K (LaurentSeries K) := ⊤
  letI algAE : Algebra A ↥E := ((algebraMap K ↥E).comp (algebraMap A K)).toAlgebra
  haveI hAKE : IsScalarTower A K ↥E := IsScalarTower.of_algebraMap_eq (fun _ => rfl)

  haveI : Module.Flat A K := IsLocalization.flat K (nonZeroDivisors A)
  haveI : Module.Flat A L := Module.Flat.trans A K L

  have hEL : IsDomain (↥E ⊗[K] L) :=
    IntermediateField.isDomain_tensorProduct_of_le_laurentSeries K L E
  let e1 : L ⊗[K] ↥E ≃ₐ[K] ↥E ⊗[K] L := Algebra.TensorProduct.comm K L ↥E
  let e2 : L ⊗[K] ↥E ≃ₐ[K] L ⊗[A] ↥E := IsLocalization.algebraTensorEquiv (nonZeroDivisors A) K L ↥E
  haveI hLE : IsDomain (L ⊗[A] ↥E) :=
    haveI := hEL
    haveI : IsDomain (L ⊗[K] ↥E) := Function.Injective.isDomain e1.toRingHom e1.injective
    Function.Injective.isDomain e2.symm.toRingHom e2.symm.injective

  let τ : LaurentSeries K ≃ₐ[K] ↥E := IntermediateField.topEquiv.symm
  have hτA : ∀ a : A, τ (algebraMap A (LaurentSeries K) a) = algebraMap A ↥E a := by
    intro a
    have h1 : algebraMap A (LaurentSeries K) a = algebraMap K (LaurentSeries K) (algebraMap A K a) := by
      rw [HahnSeries.algebraMap_apply', HahnSeries.algebraMap_apply', PowerSeries.algebraMap_apply,
        PowerSeries.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply]
    rw [h1, AlgEquiv.commutes]
    rfl
  let φE : D →ₐ[A] ↥E :=
    { toRingHom := τ.toRingEquiv.toRingHom.comp φ.toRingHom
      commutes' := fun a => by
        change τ (φ (algebraMap A D a)) = algebraMap A (↥E) a
        rw [AlgHom.commutes]
        exact hτA a }
  have hφE : Function.Injective φE := fun x y hxy => hφ (τ.injective (by simpa [φE] using hxy))

  let g : L ⊗[A] D →ₐ[A] L ⊗[A] ↥E := Algebra.TensorProduct.map (AlgHom.id A L) φE
  have hg : Function.Injective g := by
    have h := Module.Flat.lTensor_preserves_injective_linearMap (M := L) φE.toLinearMap hφE
    have hfun : (g : L ⊗[A] D → L ⊗[A] ↥E) = LinearMap.lTensor L φE.toLinearMap := by
      funext x
      induction x using TensorProduct.induction_on with
      | zero => simp [g]
      | tmul a d => simp [g]
      | add x y hx hy => simp only [map_add, hx, hy]
    rw [hfun]; exact h
  exact Function.Injective.isDomain g.toRingHom hg

end S_IsDomain_tensorProduct_of_injective_algHom_laurentSeries
end P2MW
export P2MW.S_IsDomain_tensorProduct_of_injective_algHom_laurentSeries (solution)
