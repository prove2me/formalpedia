-- Prove2me | solution 1 for HopfAlgebra.bialgHom_addMonoidAlgebra_eq_of_mapAlgHom_residueField_comp_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.85352+00:00
-- url     : https://prove2.me/submissions/2fb00a11-350c-5d59-b10f-b8aaeaeea7b6

import Mathlib
import Definitions.Def_HopfAlgebra_CartierDual
import Definitions.Def_HopfAlgebra_CartierDualInstances
import Theorems.Thm_AlgHom_eq_of_forall_sub_mem_of_le_jacobson_of_formallyUnramified
import Theorems.Thm_CartierDual_algebraEtale_addMonoidAlgebra
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_HopfAlgebra_bialgHom_addMonoidAlgebra_eq_of_mapAlgHom_residueField_comp_eq

set_option autoImplicit false

universe u v w

open IsLocalRing
open scoped TensorProduct

namespace RigidMult2

section CartierPullback

variable {R : Type u} [CommRing R]
variable {H : Type v} [CommRing H] [Bialgebra R H]
variable {H' : Type w} [CommRing H'] [Bialgebra R H']

noncomputable def dualMap (φ : H' →ₐc[R] H) : CartierDual R H →ₐ[R] CartierDual R H' where
  toFun ψ := CartierDual.ofDual R H'
    { toFun := fun a => ψ (φ a)
      map_add' := fun x y => by simp
      map_smul' := fun r x => by simp }
  map_one' := by
    ext a
    simp [CartierDual.one_apply]
  map_mul' ψ χ := by
    ext a
    simp only [CartierDual.ofDual_apply, LinearMap.coe_mk, AddHom.coe_mk]
    rw [CartierDual.mul_apply, CartierDual.mul_apply, ← CoalgHomClass.map_comp_comul_apply]
    induction (Coalgebra.comul (R := R) a) using TensorProduct.induction_on with
    | zero => simp
    | tmul x y => simp [TensorProduct.dualDistrib_apply]
    | add x y hx hy => simp only [map_add, hx, hy]
  map_zero' := by ext; rfl
  map_add' ψ χ := by ext; rfl
  commutes' r := by
    ext a
    simp [CartierDual.algebraMap_apply]

@[scoped simp] theorem dualMap_apply (φ : H' →ₐc[R] H) (ψ : CartierDual R H) (a : H') :
    dualMap φ ψ a = ψ (φ a) := rfl

end CartierPullback

theorem dual_mem_map_of_forall_apply_mem
    {R : Type u} [CommRing R] (I : Ideal R)
    {H' : Type w} [CommRing H'] [Bialgebra R H'] [Coalgebra.IsCocomm R H']
    [Module.Finite R H'] [Module.Free R H']
    (δ : CartierDual R H') (hδ : ∀ a, δ a ∈ I) :
    δ ∈ I.map (algebraMap R (CartierDual R H')) := by
  classical
  let b := Module.Free.chooseBasis R H'
  have hsum : (∑ i, δ (b i) • CartierDual.ofDual R H' (b.coord i)) = δ := by
    apply (CartierDual.toDual R H').injective
    rw [map_sum]
    simp_rw [map_smul, CartierDual.toDual_ofDual]
    exact b.sum_dual_apply_smul_coord (CartierDual.toDual R H' δ)
  rw [← hsum]
  refine Ideal.sum_mem _ fun i _ => ?_
  rw [Algebra.smul_def]
  exact Ideal.mul_mem_right _ _ (Ideal.mem_map_of_mem _ (hδ (b i)))

theorem map_maximalIdeal_le_jacobson
    {R : Type*} [CommRing R] [IsLocalRing R] {B : Type*} [CommRing B] [Algebra R B] [Module.Finite R B] :
    (IsLocalRing.maximalIdeal R).map (algebraMap R B) ≤ Ideal.jacobson ⊥ := by
  rw [Ideal.jacobson]
  refine le_sInf fun J hJ => ?_
  haveI : J.IsMaximal := hJ.2
  rw [Ideal.map_le_iff_le_comap]
  have hmax : (J.comap (algebraMap R B)).IsMaximal := Ideal.isMaximal_comap_of_isIntegral_of_isMaximal J
  rw [IsLocalRing.eq_maximalIdeal hmax]

theorem bialgHom_eq
    {R : Type u} [CommRing R] [IsLocalRing R]
    (H : Type v) [CommRing H] [Bialgebra R H] [Coalgebra.IsCocomm R H]
    [Module.Finite R H] [Module.Free R H]
    [Algebra.Etale R (CartierDual R H)]
    (H' : Type w) [CommRing H'] [Bialgebra R H'] [Coalgebra.IsCocomm R H']
    [Module.Finite R H'] [Module.Free R H']
    (φ φ' : H' →ₐc[R] H)
    (hφ : ∀ a : H', φ a - φ' a ∈ (IsLocalRing.maximalIdeal R).map (algebraMap R H)) :
    φ = φ' := by
  classical
  set 𝔪 := IsLocalRing.maximalIdeal R
  have hcong : ∀ ψ : CartierDual R H,
      dualMap φ ψ - dualMap φ' ψ ∈ 𝔪.map (algebraMap R (CartierDual R H')) := by
    intro ψ
    apply dual_mem_map_of_forall_apply_mem
    intro a
    have key : (dualMap φ ψ - dualMap φ' ψ) a = ψ (φ a - φ' a) := by
      rw [show (dualMap φ ψ - dualMap φ' ψ) a = dualMap φ ψ a - dualMap φ' ψ a from rfl]
      rw [dualMap_apply, dualMap_apply, map_sub]
    rw [key]
    have hx : φ a - φ' a ∈ (𝔪 • ⊤ : Submodule R H) := by
      rw [Ideal.smul_top_eq_map]; exact hφ a
    refine Submodule.smul_induction_on hx (fun r hr n _ => ?_) (fun x y hx hy => ?_)
    · rw [map_smul, smul_eq_mul]; exact 𝔪.mul_mem_right _ hr
    · rw [map_add]; exact 𝔪.add_mem hx hy
  haveI : Algebra.EssFiniteType R (CartierDual R H) := inferInstance
  have heq : dualMap φ = dualMap φ' :=
    AlgHom.eq_of_forall_sub_mem_of_le_jacobson_of_formallyUnramified _ map_maximalIdeal_le_jacobson _ _ hcong
  apply BialgHom.coe_algHom_injective
  apply AlgHom.ext
  intro a
  rw [← sub_eq_zero, ← Module.forall_dual_apply_eq_zero_iff R]
  intro ψ
  have := congrArg (fun F => F (CartierDual.ofDual R H ψ) a) heq
  simp only [dualMap_apply, CartierDual.ofDual_apply] at this
  rw [map_sub, sub_eq_zero]
  exact this

theorem mem_map_of_forall_apply_mem {S : Type u} [CommRing S] (I : Ideal S) {M : Type v} [AddCommMonoid M]
    (x : AddMonoidAlgebra S M) (hx : ∀ j : M, x.coeff j ∈ I) :
    x ∈ I.map (algebraMap S (AddMonoidAlgebra S M)) := by
  classical
  rw [← AddMonoidAlgebra.sum_coeff_single x, Finsupp.sum]
  refine Ideal.sum_mem _ fun j _ => ?_
  have : (AddMonoidAlgebra.single j (x.coeff j) : AddMonoidAlgebra S M) =
      algebraMap S (AddMonoidAlgebra S M) (x.coeff j) * AddMonoidAlgebra.single j 1 := by
    rw [AddMonoidAlgebra.coe_algebraMap, Function.comp_apply, AddMonoidAlgebra.single_mul_single, zero_add, mul_one]
    rfl
  rw [this]
  exact Ideal.mul_mem_right _ _ (Ideal.mem_map_of_mem _ (hx j))

end RigidMult2
p2m_reactivate "P2MW.S_HopfAlgebra_bialgHom_addMonoidAlgebra_eq_of_mapAlgHom_residueField_comp_eq.RigidMult2"

open RigidMult2 in

theorem solution
    {R : Type u} [CommRing R] [IsLocalRing R]
    {H : Type u} [CommRing H] [HopfAlgebra R H] [Module.Finite R H] [Module.Flat R H] [Coalgebra.IsCocomm R H]
    (M : Type v) [AddCommGroup M] [Finite M]
    (ψ ψ' : H →ₐc[R] AddMonoidAlgebra R M)
    (h : (AddMonoidAlgebra.mapAlgHom M (Algebra.ofId R (ResidueField R))).comp (ψ : H →ₐ[R] AddMonoidAlgebra R M) =
      (AddMonoidAlgebra.mapAlgHom M (Algebra.ofId R (ResidueField R))).comp (ψ' : H →ₐ[R] AddMonoidAlgebra R M)) :
    ψ = ψ' := by
  classical
  haveI : Module.Free R H := Module.free_of_flat_of_isLocalRing
  haveI : Algebra.Etale R (CartierDual R (AddMonoidAlgebra R M)) := CartierDual.algebraEtale_addMonoidAlgebra R M
  refine bialgHom_eq (AddMonoidAlgebra R M) H ψ ψ' fun a => ?_
  apply mem_map_of_forall_apply_mem
  intro j
  have hd : AddMonoidAlgebra.mapAlgHom M (Algebra.ofId R (ResidueField R))
      ((ψ : H →ₐ[R] AddMonoidAlgebra R M) a - (ψ' : H →ₐ[R] AddMonoidAlgebra R M) a) = 0 := by
    rw [map_sub, sub_eq_zero]
    exact congrArg (fun F : H →ₐ[R] AddMonoidAlgebra (ResidueField R) M => F a) h
  have hdj := congrArg (fun y : AddMonoidAlgebra (ResidueField R) M => y.coeff j) hd
  simp only [AddMonoidAlgebra.coeff_mapAlgHom, AddMonoidAlgebra.coeff_zero] at hdj
  rw [← IsLocalRing.residue_eq_zero_iff]
  exact hdj

#print axioms solution

end S_HopfAlgebra_bialgHom_addMonoidAlgebra_eq_of_mapAlgHom_residueField_comp_eq
end P2MW
export P2MW.S_HopfAlgebra_bialgHom_addMonoidAlgebra_eq_of_mapAlgHom_residueField_comp_eq (solution)
