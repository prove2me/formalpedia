-- Prove2me | solution 1 for HopfAlgebra.toConv_comp_hopfKer_val_mul_and_eq_iff_existsUnique
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.85352+00:00
-- url     : https://prove2.me/submissions/56aa9cbd-8042-545d-b82b-dfc05fddfe8f

import Mathlib
import Definitions.Def_HopfAlgebra_HopfKerHopf
import Theorems.Thm_HopfAlgebra_algHom_comp_hopfKer_val_eq_iff
import Theorems.Thm_HopfAlgebra_isHopfGalois_of_surjective
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_HopfAlgebra_toConv_comp_hopfKer_val_mul_and_eq_iff_existsUnique
set_option autoImplicit false

open scoped TensorProduct

namespace HopfAlgebra
p2m_export "HopfAlgebra" "coaction coaction_apply hopfKer algHom_comp_hopfKer_val_eq_iff isHopfGalois_of_surjective"
p2m_open "HopfAlgebra"
namespace HopfKerPoints

open WithConv

variable {R : Type*} [CommRing R] {A : Type*} [CommRing A] [HopfAlgebra R A]
  {B : Type*} [CommRing B] [HopfAlgebra R B] (π : A →ₐc[R] B)
  {L : Type*} [CommRing L] [Algebra R L]

theorem lift_comp_map_id (ψ : A →ₐ[R] L) (χ : B →ₐ[R] L) :
    (Algebra.TensorProduct.lift ψ χ (fun _ _ => Commute.all _ _)).comp
        (Algebra.TensorProduct.map (AlgHom.id R A) (π : A →ₐ[R] B))
      = Algebra.TensorProduct.lift ψ (χ.comp (π : A →ₐ[R] B)) (fun _ _ => Commute.all _ _) := by
  ext a
  · simp
  · simp

theorem lift_comp_coaction (ψ : A →ₐ[R] L) (χ : B →ₐ[R] L) :
    (Algebra.TensorProduct.lift ψ χ (fun _ _ => Commute.all _ _)).comp (coaction π)
      = (toConv ψ * toConv (χ.comp (π : A →ₐ[R] B))).ofConv := by
  apply AlgHom.ext
  intro a
  rw [AlgHom.convMul_apply, AlgHom.comp_apply, coaction_apply]
  change ((Algebra.TensorProduct.lift ψ χ (fun _ _ => Commute.all _ _)).comp
      (Algebra.TensorProduct.map (AlgHom.id R A) (π : A →ₐ[R] B))) (Coalgebra.comul (R := R) a) = _
  rw [lift_comp_map_id]

variable [Coalgebra.IsCocomm R A] [Module.Flat R A] [Module.Flat R B] [Module.Flat R ↥(hopfKer π)]

theorem coe_hopfKerVal :
    ((hopfKerVal π : ↥(hopfKer π) →ₐc[R] A) : ↥(hopfKer π) →ₐ[R] A) = (hopfKer π).val :=
  AlgHom.ext fun _ => rfl

theorem res_one :
    toConv ((ofConv (1 : WithConv (A →ₐ[R] L))).comp (hopfKer π).val)
      = (1 : WithConv (↥(hopfKer π) →ₐ[R] L)) := by
  apply WithConv.ext
  apply AlgHom.ext
  intro c
  change (1 : WithConv (A →ₐ[R] L)) (c : A) = (1 : WithConv (↥(hopfKer π) →ₐ[R] L)) c
  rw [AlgHom.convOne_apply, AlgHom.convOne_apply, counit_coe]

theorem res_mul (ν ν' : WithConv (A →ₐ[R] L)) :
    toConv ((ofConv (ν * ν')).comp (hopfKer π).val)
      = toConv ((ofConv ν).comp (hopfKer π).val) * toConv ((ofConv ν').comp (hopfKer π).val) := by
  have h := AlgHom.convMul_comp_bialgHom_distrib ν ν' (hopfKerVal π)
  rw [coe_hopfKerVal] at h
  rw [h]

end HopfKerPoints
end HopfAlgebra

open _root_.HopfAlgebra _root_.P2MW.S_HopfAlgebra_toConv_comp_hopfKer_val_mul_and_eq_iff_existsUnique.HopfAlgebra WithConv in
theorem solution
    {R : Type*} [CommRing R] {A : Type*} [CommRing A] [HopfAlgebra R A] [Coalgebra.IsCocomm R A]
    {B : Type*} [CommRing B] [HopfAlgebra R B] [Module.Finite R B] [Module.Free R B]
    (π : A →ₐc[R] B) (hπ : Function.Surjective π)
    [Module.Flat R A] [Module.Flat R ↥(HopfAlgebra.hopfKer π)]
    (L : Type*) [CommRing L] [Algebra R L] :
    WithConv.toConv ((WithConv.ofConv (1 : WithConv (A →ₐ[R] L))).comp (HopfAlgebra.hopfKer π).val)
        = (1 : WithConv (↥(HopfAlgebra.hopfKer π) →ₐ[R] L)) ∧
    (∀ ν ν' : WithConv (A →ₐ[R] L),
        WithConv.toConv ((WithConv.ofConv (ν * ν')).comp (HopfAlgebra.hopfKer π).val)
          = WithConv.toConv ((WithConv.ofConv ν).comp (HopfAlgebra.hopfKer π).val)
            * WithConv.toConv ((WithConv.ofConv ν').comp (HopfAlgebra.hopfKer π).val)) ∧
    (∀ ν ν' : WithConv (A →ₐ[R] L),
        (WithConv.ofConv ν).comp (HopfAlgebra.hopfKer π).val
            = (WithConv.ofConv ν').comp (HopfAlgebra.hopfKer π).val
          ↔ ∃! χ : B →ₐ[R] L, ν' = ν * WithConv.toConv (χ.comp (π : A →ₐ[R] B))) := by
  refine ⟨HopfKerPoints.res_one π, HopfKerPoints.res_mul π, fun ν ν' => ?_⟩
  rw [algHom_comp_hopfKer_val_eq_iff π (isHopfGalois_of_surjective π hπ) (ofConv ν) (ofConv ν')]
  refine existsUnique_congr fun χ => ?_
  rw [HopfKerPoints.lift_comp_coaction]
  constructor
  · intro h
    apply WithConv.ext
    rw [← h]
  · intro h
    rw [h]

end S_HopfAlgebra_toConv_comp_hopfKer_val_mul_and_eq_iff_existsUnique
end P2MW
export P2MW.S_HopfAlgebra_toConv_comp_hopfKer_val_mul_and_eq_iff_existsUnique (solution)
