-- Prove2me | solution 1 for HopfAlgebra.surjective_of_surjective_baseChange_of_pow_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.85352+00:00
-- url     : https://prove2.me/submissions/dc0b3f7c-7cf1-52f6-8d7b-8173c007a144

import Mathlib
import Theorems.Thm_HopfAlgebra_surjective_of_injective_of_surjective_baseChange_of_pow_eq_one
import Theorems.Thm_HopfAlgebra_exists_hopfAlgebra_surjective_injective_comp_eq
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_HopfAlgebra_surjective_of_surjective_baseChange_of_pow_eq_one
p2m_attr_erase "instance" "HopfAlgebra.HopfKerHopf.instHopfAlgebra HopfAlgebra.HopfKerHopf.instCoalgebra HopfAlgebra.HopfKerHopf.instIsCocomm HopfAlgebra.HopfKerHopf.instBialgebra CartierDual.instAlgebraBaseChangeDual CartierDual.instRingBaseChangeDual CartierDual.instModuleRestrictBaseChange CartierDual.instIsScalarTowerRestrictBaseChange MonoidAlgebra.instModuleFiniteOfCartier CartierDual.instCoalgebra CartierDual.instModuleFinite CartierDual.instBialgebra CartierDual.instFunLike CartierDual.instRing CartierDual.instLinearMapClass CartierDual.instCommRing CartierDual.instIsCocomm MonoidAlgebra.instModuleFreeOfCartier CartierDual.instModuleFree CartierDual.instHopfAlgebra CartierDual.instAlgebra instIsScalarTowerTensorProduct_definitions"
p2m_attr_erase "simp" "HopfAlgebra.canAlgHom_tmul HopfAlgebra.canMap_tmul HopfAlgebra.HopfKerHopf.ι₂_comulK HopfAlgebra.HopfKerHopf.ι₃_tmul HopfAlgebra.HopfKerHopf.counitK_apply HopfAlgebra.HopfKerHopf.coe_antipodeK HopfAlgebra.HopfKerHopf.ι₂_tmul HopfAlgebra.HopfKerHopf.coe_antipode HopfAlgebra.HopfKerHopf.hopfKerVal_apply HopfAlgebra.HopfKerHopf.valL_apply HopfAlgebra.HopfKerHopf.ι₂_comul HopfAlgebra.FVectStructure.addChar_apply HopfAlgebra.FVectStructure.mk.sizeOf_spec HopfAlgebra.FVectStructure.mk.injEq HopfAlgebra.FVectStructure.unitsAct_apply HopfAlgebra.mem_vanishingIdealOfPoints_iff HopfAlgebra.liftPoint_mk HopfAlgebra.mem_ptSet_iff CartierDual.dualBaseChangeLin_tmul CartierDual.dualBaseChange_tmul CartierDual.toDual_ofDual CartierDual.algebraMap_apply CartierDual.antipode_apply CartierDual.one_apply CartierDual.toDual_apply CartierDual.ofDual_toDual CartierDual.ofDual_apply CartierDual.counit_apply mem_flatClosure_iff HopfOrder.doubleCmp_tmul HopfOrder.tensorSqHom_tmul HopfOrder.baseChangeHom_tmul"

set_option autoImplicit false

universe u v

namespace HopfAlgebra
p2m_export "HopfAlgebra" "surjective_of_injective_of_surjective_baseChange_of_pow_eq_one exists_hopfAlgebra_surjective_injective_comp_eq"
namespace C1Glue
p2m_open "HopfAlgebra"

open scoped TensorProduct

variable {R : Type u} [CommRing R]

theorem isCocomm_of_surjective
    {H : Type v} [CommRing H] [HopfAlgebra R H] [Coalgebra.IsCocomm R H]
    {Q : Type v} [CommRing Q] [HopfAlgebra R Q]
    (π : H →ₐc[R] Q) (hπ : Function.Surjective π) : Coalgebra.IsCocomm R Q := by
  refine ⟨LinearMap.ext fun y => ?_⟩
  obtain ⟨x, rfl⟩ := hπ y
  have hco := congrArg (fun f : H →ₗ[R] Q ⊗[R] Q => f x) (CoalgHomClass.map_comp_comul π)
  simp only [LinearMap.comp_apply] at hco

  change TensorProduct.comm R Q Q (Coalgebra.comul (π x)) = Coalgebra.comul (π x)
  have hx : Coalgebra.comul ((π : H →ₗc[R] Q) x) = TensorProduct.map (π : H →ₗc[R] Q).toLinearMap
      (π : H →ₗc[R] Q).toLinearMap (Coalgebra.comul x) := hco.symm
  have hnat : ∀ t : H ⊗[R] H, TensorProduct.comm R Q Q (TensorProduct.map (π : H →ₗc[R] Q).toLinearMap
      (π : H →ₗc[R] Q).toLinearMap t) = TensorProduct.map (π : H →ₗc[R] Q).toLinearMap
      (π : H →ₗc[R] Q).toLinearMap (TensorProduct.comm R H H t) := by
    intro t
    induction t using TensorProduct.induction_on with
    | zero => simp
    | tmul a b => simp
    | add a b ha hb => simp only [map_add, ha, hb]
  change TensorProduct.comm R Q Q (Coalgebra.comul ((π : H →ₗc[R] Q) x)) = Coalgebra.comul ((π : H →ₗc[R] Q) x)
  rw [hx, hnat, Coalgebra.comm_comul]

theorem ofConv_pow_comp
    {H : Type v} [CommRing H] [HopfAlgebra R H]
    {Q : Type v} [CommRing Q] [HopfAlgebra R Q]
    (π : H →ₐc[R] Q) {T : Type v} [CommRing T] [Algebra R T]
    (f : WithConv (Q →ₐ[R] T)) (k : ℕ) :
    (f ^ k).ofConv.comp (π : H →ₐ[R] Q) =
      ((WithConv.toConv (f.ofConv.comp (π : H →ₐ[R] Q))) ^ k).ofConv := by
  induction k with
  | zero =>
      rw [pow_zero, pow_zero, AlgHom.convOne_def, AlgHom.convOne_def]
      change ((Algebra.ofId R T).comp (Bialgebra.counitAlgHom R Q)).comp (π : H →ₐ[R] Q) =
        (Algebra.ofId R T).comp (Bialgebra.counitAlgHom R H)
      rw [AlgHom.comp_assoc]
      congr 1
      apply AlgHom.toLinearMap_injective
      exact CoalgHomClass.counit_comp π
  | succ k ih =>
      rw [pow_succ, pow_succ, AlgHom.convMul_def, AlgHom.convMul_def]
      change ((Algebra.TensorProduct.lmul' R).comp
          ((Algebra.TensorProduct.map (f ^ k).ofConv f.ofConv).comp (Bialgebra.comulAlgHom R Q))).comp
            (π : H →ₐ[R] Q) =
        (Algebra.TensorProduct.lmul' R).comp
          ((Algebra.TensorProduct.map ((WithConv.toConv (f.ofConv.comp (π : H →ₐ[R] Q))) ^ k).ofConv
            (f.ofConv.comp (π : H →ₐ[R] Q))).comp (Bialgebra.comulAlgHom R H))
      rw [← ih, AlgHom.comp_assoc, AlgHom.comp_assoc, Algebra.TensorProduct.map_comp, AlgHom.comp_assoc]
      have hm := BialgHomClass.map_comp_comulAlgHom π
      exact congrArg (fun g : H →ₐ[R] Q ⊗[R] Q =>
        (Algebra.TensorProduct.lmul' R).comp ((Algebra.TensorProduct.map (f ^ k).ofConv f.ofConv).comp g))
        hm.symm

theorem pow_eq_one_of_surjective
    {H : Type v} [CommRing H] [HopfAlgebra R H]
    {Q : Type v} [CommRing Q] [HopfAlgebra R Q]
    (π : H →ₐc[R] Q) (hπ : Function.Surjective π) (m : ℕ)
    (hH : ∀ (T : Type v) [CommRing T] [Algebra R T] (f : WithConv (H →ₐ[R] T)), f ^ m = 1)
    (T : Type v) [CommRing T] [Algebra R T] (f : WithConv (Q →ₐ[R] T)) : f ^ m = 1 := by
  have h1 := ofConv_pow_comp π f m
  rw [hH T] at h1
  have h0 := ofConv_pow_comp π f 0
  rw [pow_zero, pow_zero] at h0
  rw [← h0] at h1

  have hc : (f ^ m).ofConv = (1 : WithConv (Q →ₐ[R] T)).ofConv := by
    apply AlgHom.ext
    intro y
    obtain ⟨x, rfl⟩ := hπ y
    exact congrArg (fun g : H →ₐ[R] T => g x) h1
  exact WithConv.ext hc

end HopfAlgebra.C1Glue

open HopfAlgebra.C1Glue in
theorem solution
    {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    (K : Type u) [Field K] [Algebra R K] [IsFractionRing R K]
    (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2) (hunif : Irreducible (p : R))
    {H : Type v} [CommRing H] [HopfAlgebra R H] [Module.Finite R H] [Module.Flat R H]
    [Coalgebra.IsCocomm R H]
    {H' : Type v} [CommRing H'] [HopfAlgebra R H'] [Module.Finite R H'] [Module.Flat R H']
    [Coalgebra.IsCocomm R H']
    (n : ℕ)
    (hH : ∀ (T : Type v) [CommRing T] [Algebra R T] (f : WithConv (H →ₐ[R] T)), f ^ p ^ n = 1)
    (hH' : ∀ (T : Type v) [CommRing T] [Algebra R T] (f : WithConv (H' →ₐ[R] T)), f ^ p ^ n = 1)
    (φ : H →ₐc[R] H') (hφK : Function.Surjective ((φ : H →ₐ[R] H').toLinearMap.baseChange K)) :
    Function.Surjective φ := by
  obtain ⟨Q, _, _, _, _, π, ι, hπ, hι, hcomp⟩ :=
    HopfAlgebra.exists_hopfAlgebra_surjective_injective_comp_eq φ
  haveI : Coalgebra.IsCocomm R Q := isCocomm_of_surjective π hπ
  have hQ : ∀ (T : Type v) [CommRing T] [Algebra R T] (f : WithConv (Q →ₐ[R] T)), f ^ p ^ n = 1 :=
    fun T _ _ f => pow_eq_one_of_surjective π hπ (p ^ n) hH T f
  have hφ : ∀ x, φ x = ι (π x) := fun x => by rw [← hcomp]; rfl
  have hιK : Function.Surjective ((ι : Q →ₐ[R] H').toLinearMap.baseChange K) := by
    have hfac : ∀ t, ((φ : H →ₐ[R] H').toLinearMap.baseChange K) t =
        ((ι : Q →ₐ[R] H').toLinearMap.baseChange K) (((π : H →ₐ[R] Q).toLinearMap.baseChange K) t) := by
      intro t
      induction t using TensorProduct.induction_on with
      | zero => simp
      | tmul k x => simp [LinearMap.baseChange_tmul, hφ]
      | add a b ha hb => simp only [map_add, ha, hb]
    intro z
    obtain ⟨t, rfl⟩ := hφK z
    exact ⟨_, (hfac t).symm⟩
  have hιs : Function.Surjective ι :=
    HopfAlgebra.surjective_of_injective_of_surjective_baseChange_of_pow_eq_one K p hp2 hunif n hQ hH' ι hι hιK
  intro y
  obtain ⟨q, rfl⟩ := hιs y
  obtain ⟨x, rfl⟩ := hπ q
  exact ⟨x, hφ x⟩

end S_HopfAlgebra_surjective_of_surjective_baseChange_of_pow_eq_one
end P2MW
export P2MW.S_HopfAlgebra_surjective_of_surjective_baseChange_of_pow_eq_one (solution)
