-- Prove2me | solution 1 for HopfAlgebra.exists_fVectStructure_baseChange_eq_of_pow_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.85352+00:00
-- url     : https://prove2.me/submissions/aeab6af8-20b0-5c8a-96ca-474dd5556b30

import Definitions.Def_HopfAlgebra_FVectStructure
import Theorems.Thm_HopfAlgebra_existsUnique_bialgHom_baseChange_eq_of_pow_eq_one
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_HopfAlgebra_exists_fVectStructure_baseChange_eq_of_pow_eq_one
p2m_attr_erase "instance" "HopfAlgebra.HopfKerHopf.instHopfAlgebra HopfAlgebra.HopfKerHopf.instCoalgebra HopfAlgebra.HopfKerHopf.instIsCocomm HopfAlgebra.HopfKerHopf.instBialgebra CartierDual.instAlgebraBaseChangeDual CartierDual.instRingBaseChangeDual CartierDual.instModuleRestrictBaseChange CartierDual.instIsScalarTowerRestrictBaseChange MonoidAlgebra.instModuleFiniteOfCartier CartierDual.instCoalgebra CartierDual.instModuleFinite CartierDual.instBialgebra CartierDual.instFunLike CartierDual.instRing CartierDual.instLinearMapClass CartierDual.instCommRing CartierDual.instIsCocomm MonoidAlgebra.instModuleFreeOfCartier CartierDual.instModuleFree CartierDual.instHopfAlgebra CartierDual.instAlgebra instIsScalarTowerTensorProduct_definitions"
p2m_attr_erase "simp" "HopfOrder.doubleCmp_tmul HopfOrder.tensorSqHom_tmul HopfOrder.baseChangeHom_tmul HopfAlgebra.canAlgHom_tmul HopfAlgebra.canMap_tmul HopfAlgebra.HopfKerHopf.ι₂_comulK HopfAlgebra.HopfKerHopf.ι₃_tmul HopfAlgebra.HopfKerHopf.counitK_apply HopfAlgebra.HopfKerHopf.coe_antipodeK HopfAlgebra.HopfKerHopf.ι₂_tmul HopfAlgebra.HopfKerHopf.coe_antipode HopfAlgebra.HopfKerHopf.hopfKerVal_apply HopfAlgebra.HopfKerHopf.valL_apply HopfAlgebra.HopfKerHopf.ι₂_comul HopfAlgebra.mem_vanishingIdealOfPoints_iff HopfAlgebra.liftPoint_mk HopfAlgebra.mem_ptSet_iff CartierDual.dualBaseChangeLin_tmul CartierDual.dualBaseChange_tmul CartierDual.toDual_ofDual CartierDual.algebraMap_apply CartierDual.antipode_apply CartierDual.one_apply CartierDual.toDual_apply CartierDual.ofDual_toDual CartierDual.ofDual_apply CartierDual.counit_apply mem_flatClosure_iff"

open scoped TensorProduct

universe u v w

set_option autoImplicit false

namespace FVExtE72

open scoped TensorProduct
open HopfAlgebra

section BC

variable {R : Type u} [CommRing R] (K : Type u) [Field K] [Algebra R K]
  {B : Type v} [CommRing B] [HopfAlgebra R B]

private theorem _root_.FVExtE72.baseChange_id : (AlgHom.id R B).toLinearMap.baseChange K =
    (AlgHom.id K (K ⊗[R] B)).toLinearMap := by
  rw [AlgHom.toLinearMap_id, LinearMap.baseChange_id, AlgHom.toLinearMap_id]

p2m_export "FVExtE72" "baseChange_id"

private theorem _root_.FVExtE72.baseChange_comp (f g : B →ₐ[R] B) (fK gK : K ⊗[R] B →ₐ[K] K ⊗[R] B)
    (hf : f.toLinearMap.baseChange K = fK.toLinearMap) (hg : g.toLinearMap.baseChange K = gK.toLinearMap) :
    (f.comp g).toLinearMap.baseChange K = (fK.comp gK).toLinearMap := by
  rw [AlgHom.comp_toLinearMap, LinearMap.baseChange_comp, hf, hg, AlgHom.comp_toLinearMap]

p2m_export "FVExtE72" "baseChange_comp"

theorem baseChange_one :
    ((1 : WithConv (B →ₐ[R] B)).ofConv).toLinearMap.baseChange K =
      ((1 : WithConv (K ⊗[R] B →ₐ[K] K ⊗[R] B)).ofConv).toLinearMap := by
  apply TensorProduct.AlgebraTensorModule.ext
  intro a b
  rw [LinearMap.baseChange_tmul]
  change a ⊗ₜ[R] ((1 : WithConv (B →ₐ[R] B)) b) = (1 : WithConv (K ⊗[R] B →ₐ[K] K ⊗[R] B)) (a ⊗ₜ[R] b)
  rw [AlgHom.convOne_apply, AlgHom.convOne_apply, TensorProduct.counit_tmul, CommSemiring.counit_apply,
    Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_eq_smul_one, TensorProduct.tmul_smul,
    TensorProduct.smul_tmul']
  congr 1

theorem baseChange_convMul (f g : B →ₐ[R] B) (fK gK : K ⊗[R] B →ₐ[K] K ⊗[R] B)
    (hf : f.toLinearMap.baseChange K = fK.toLinearMap) (hg : g.toLinearMap.baseChange K = gK.toLinearMap) :
    ((WithConv.toConv f * WithConv.toConv g).ofConv).toLinearMap.baseChange K =
      ((WithConv.toConv fK * WithConv.toConv gK).ofConv).toLinearMap := by
  apply TensorProduct.AlgebraTensorModule.ext
  intro a b
  have hfK : ∀ (c : K) (x : B), fK (c ⊗ₜ[R] x) = c ⊗ₜ[R] f x := fun c x => by
    have := congrArg (fun L : K ⊗[R] B →ₗ[K] K ⊗[R] B => L (c ⊗ₜ[R] x)) hf
    simpa [LinearMap.baseChange_tmul] using this.symm
  have hgK : ∀ (c : K) (x : B), gK (c ⊗ₜ[R] x) = c ⊗ₜ[R] g x := fun c x => by
    have := congrArg (fun L : K ⊗[R] B →ₗ[K] K ⊗[R] B => L (c ⊗ₜ[R] x)) hg
    simpa [LinearMap.baseChange_tmul] using this.symm
  rw [LinearMap.baseChange_tmul]
  change a ⊗ₜ[R] ((WithConv.toConv f * WithConv.toConv g) b) = (WithConv.toConv fK * WithConv.toConv gK) (a ⊗ₜ[R] b)

  classical
  obtain ⟨ι, s, x, y, hrep⟩ : ∃ (ι : Type v) (s : Finset ι) (x y : ι → B),
      Coalgebra.comul (R := R) b = ∑ i ∈ s, x i ⊗ₜ[R] y i :=
    ⟨_, (Coalgebra.Repr.arbitrary R b).index, _, _, (Coalgebra.Repr.arbitrary R b).eq.symm⟩
  rw [AlgHom.convMul_apply, AlgHom.convMul_apply]
  simp only []
  rw [TensorProduct.comul_tmul, CommSemiring.comul_apply, hrep]
  simp only [map_sum, TensorProduct.tmul_sum, TensorProduct.AlgebraTensorModule.tensorTensorTensorComm_tmul]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Algebra.TensorProduct.lift_tmul, Algebra.TensorProduct.lift_tmul, hfK, hgK,
    Algebra.TensorProduct.tmul_mul_tmul, one_mul]

end BC

section Main

variable {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  (K : Type u) [Field K] [Algebra R K] [IsFractionRing R K]
  (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2) (hunif : Irreducible (p : R))
  {B : Type v} [CommRing B] [HopfAlgebra R B] [Module.Finite R B] [Module.Flat R B]
  [Coalgebra.IsCocomm R B]
  (n : ℕ) (hB : ∀ (T : Type v) [CommRing T] [Algebra R T] (f : WithConv (B →ₐ[R] T)), f ^ p ^ n = 1)
  {F : Type w} [Field F] (fvK : FVectStructure F K (K ⊗[R] B))

include hp2 hunif hB in
theorem main : ∃ fv : FVectStructure F R B,
    ∀ a : F, (fv.act a : B →ₐ[R] B).toLinearMap.baseChange K
      = (fvK.act a : K ⊗[R] B →ₐ[K] K ⊗[R] B).toLinearMap := by
  have EU := fun (ψ : (K ⊗[R] B) →ₐc[K] (K ⊗[R] B)) =>
    HopfAlgebra.existsUnique_bialgHom_baseChange_eq_of_pow_eq_one K p hp2 hunif n hB hB ψ

  choose φ hφ hφu using fun a : F => EU (fvK.act a)

  have huniq : ∀ (a : F) (ψ : B →ₐc[R] B),
      (ψ : B →ₐ[R] B).toLinearMap.baseChange K = (fvK.act a : K ⊗[R] B →ₐ[K] K ⊗[R] B).toLinearMap →
      ψ = φ a := fun a ψ h => hφu a ψ h
  refine ⟨{ act := φ, act_one := ?_, act_mul := ?_, act_zero := ?_, act_add := ?_ }, hφ⟩
  ·
    symm
    apply huniq
    rw [fvK.act_one]
    exact baseChange_id K
  · intro a b
    symm
    apply huniq
    rw [fvK.act_mul]
    exact baseChange_comp K (φ a : B →ₐ[R] B) (φ b : B →ₐ[R] B) _ _ (hφ a) (hφ b)
  ·
    have h1 : ((1 : WithConv (B →ₐc[R] B)).ofConv : B →ₐc[R] B) = φ 0 := by
      apply huniq
      have hK : (fvK.act 0 : K ⊗[R] B →ₐ[K] K ⊗[R] B) =
          (1 : WithConv (K ⊗[R] B →ₐ[K] K ⊗[R] B)).ofConv :=
        WithConv.toConv_injective (by rw [fvK.act_zero, WithConv.toConv_ofConv])
      have hB1 : ((1 : WithConv (B →ₐc[R] B)).ofConv : B →ₐ[R] B) = (1 : WithConv (B →ₐ[R] B)).ofConv :=
        WithConv.toConv_injective (by rw [BialgHom.toAlgHom_convOne, WithConv.toConv_ofConv])
      rw [hK, hB1]
      exact baseChange_one K
    rw [← h1, BialgHom.toAlgHom_convOne]
  · intro a b
    have hsum : (WithConv.toConv (φ a) * WithConv.toConv (φ b)).ofConv = φ (a + b) := by
      apply huniq
      have h2 : ((WithConv.toConv (φ a) * WithConv.toConv (φ b)).ofConv : B →ₐ[R] B) =
          (WithConv.toConv (φ a : B →ₐ[R] B) * WithConv.toConv (φ b : B →ₐ[R] B)).ofConv :=
        WithConv.toConv_injective (by rw [BialgHom.toAlgHom_convMul, WithConv.toConv_ofConv])
      have h3 : (fvK.act (a + b) : K ⊗[R] B →ₐ[K] K ⊗[R] B) =
          (WithConv.toConv (fvK.act a : K ⊗[R] B →ₐ[K] K ⊗[R] B) *
            WithConv.toConv (fvK.act b : K ⊗[R] B →ₐ[K] K ⊗[R] B)).ofConv :=
        WithConv.toConv_injective (by rw [fvK.act_add, WithConv.toConv_ofConv])
      rw [h2, h3]
      exact baseChange_convMul K _ _ _ _ (hφ a) (hφ b)
    rw [← hsum, BialgHom.toAlgHom_convMul, WithConv.ofConv_toConv, WithConv.ofConv_toConv]

end Main

end FVExtE72

open scoped TensorProduct in
theorem solution
    {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    (K : Type u) [Field K] [Algebra R K] [IsFractionRing R K]
    (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2) (hunif : Irreducible (p : R))
    {B : Type v} [CommRing B] [HopfAlgebra R B] [Module.Finite R B] [Module.Flat R B]
    [Coalgebra.IsCocomm R B]
    (n : ℕ) (hB : ∀ (T : Type v) [CommRing T] [Algebra R T] (f : WithConv (B →ₐ[R] T)), f ^ p ^ n = 1)
    {F : Type w} [Field F] (fvK : HopfAlgebra.FVectStructure F K (K ⊗[R] B)) :
    ∃ fv : HopfAlgebra.FVectStructure F R B,
      ∀ a : F, (fv.act a : B →ₐ[R] B).toLinearMap.baseChange K
        = (fvK.act a : K ⊗[R] B →ₐ[K] K ⊗[R] B).toLinearMap :=
  FVExtE72.main K p hp2 hunif n hB fvK

end S_HopfAlgebra_exists_fVectStructure_baseChange_eq_of_pow_eq_one
end P2MW
export P2MW.S_HopfAlgebra_exists_fVectStructure_baseChange_eq_of_pow_eq_one (solution)
