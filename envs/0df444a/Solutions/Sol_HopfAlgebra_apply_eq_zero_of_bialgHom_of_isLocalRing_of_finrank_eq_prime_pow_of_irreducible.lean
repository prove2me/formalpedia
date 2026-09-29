-- Prove2me | solution 1 for HopfAlgebra.apply_eq_zero_of_bialgHom_of_isLocalRing_of_finrank_eq_prime_pow_of_irreducible
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.85352+00:00
-- url     : https://prove2.me/submissions/e64b2476-e156-56aa-81af-0b1e62004a9b

import Mathlib
import Theorems.Thm_HopfAlgebra_existsUnique_bialgHom_forall_apply_comp_eq_of_finrank_eq_prime_pow_of_irreducible
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_HopfAlgebra_apply_eq_zero_of_bialgHom_of_isLocalRing_of_finrank_eq_prime_pow_of_irreducible
p2m_attr_erase "instance" "GaloisRepAdic.instAddCommGroup GaloisRepAdic.instFree GaloisRepAdic.instFinite GaloisRepAdic.instModule ResidualGaloisRep.instModule ResidualGaloisRep.instModuleFinite ResidualGaloisRep.instAddCommGroup WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv WeierstrassCurve.Affine.Point.instFinite HopfAlgebra.HopfKerHopf.instHopfAlgebra HopfAlgebra.HopfKerHopf.instCoalgebra HopfAlgebra.HopfKerHopf.instIsCocomm HopfAlgebra.HopfKerHopf.instBialgebra CartierDual.instAlgebraBaseChangeDual CartierDual.instRingBaseChangeDual CartierDual.instModuleRestrictBaseChange CartierDual.instIsScalarTowerRestrictBaseChange MonoidAlgebra.instModuleFiniteOfCartier CartierDual.instCoalgebra CartierDual.instModuleFinite CartierDual.instBialgebra CartierDual.instFunLike CartierDual.instRing CartierDual.instLinearMapClass CartierDual.instCommRing CartierDual.instIsCocomm MonoidAlgebra.instModuleFreeOfCartier CartierDual.instModuleFree CartierDual.instHopfAlgebra CartierDual.instAlgebra instIsScalarTowerTensorProduct_definitions"
p2m_attr_erase "simp" "GaloisRepAdic.mk.injEq GaloisRepAdic.mk.sizeOf_spec GaloisRepAdic.Equiv.mk.sizeOf_spec GaloisRepAdic.Equiv.mk.injEq ResidualGaloisRep.mk.sizeOf_spec ResidualGaloisRep.mk.injEq WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply FreyPackage.mk.sizeOf_spec FreyPackage.mk.injEq ResidualGaloisRep.Equiv.mk.sizeOf_spec ResidualGaloisRep.Equiv.mk.injEq HopfOrder.doubleCmp_tmul HopfOrder.tensorSqHom_tmul HopfOrder.baseChangeHom_tmul HopfAlgebra.canAlgHom_tmul HopfAlgebra.canMap_tmul HopfAlgebra.HopfKerHopf.ι₂_comulK HopfAlgebra.HopfKerHopf.ι₃_tmul HopfAlgebra.HopfKerHopf.counitK_apply HopfAlgebra.HopfKerHopf.coe_antipodeK HopfAlgebra.HopfKerHopf.ι₂_tmul HopfAlgebra.HopfKerHopf.coe_antipode HopfAlgebra.HopfKerHopf.hopfKerVal_apply HopfAlgebra.HopfKerHopf.valL_apply HopfAlgebra.HopfKerHopf.ι₂_comul HopfAlgebra.FVectStructure.addChar_apply HopfAlgebra.FVectStructure.mk.sizeOf_spec HopfAlgebra.FVectStructure.mk.injEq HopfAlgebra.FVectStructure.unitsAct_apply HopfAlgebra.mem_vanishingIdealOfPoints_iff HopfAlgebra.liftPoint_mk HopfAlgebra.mem_ptSet_iff CartierDual.dualBaseChangeLin_tmul CartierDual.dualBaseChange_tmul CartierDual.toDual_ofDual CartierDual.algebraMap_apply CartierDual.antipode_apply CartierDual.one_apply CartierDual.toDual_apply CartierDual.ofDual_toDual"
p2m_attr_erase "simp" "CartierDual.ofDual_apply CartierDual.counit_apply mem_flatClosure_iff"

set_option autoImplicit false
set_option linter.unusedSectionVars false
open scoped TensorProduct

def nuq_C (R U : Type) : Type := U → R

section nuq_ring
variable (R U : Type) [CommRing R] [AddCommGroup U]

scoped instance nuq_C.instCommRing : CommRing (nuq_C R U) := inferInstanceAs (CommRing (U → R))
p2m_reactivate "P2MW.S_HopfAlgebra_apply_eq_zero_of_bialgHom_of_isLocalRing_of_finrank_eq_prime_pow_of_irreducible.nuq_C"
scoped instance nuq_C.instAlgebra : Algebra R (nuq_C R U) := inferInstanceAs (Algebra R (U → R))

p2m_reactivate "P2MW.S_HopfAlgebra_apply_eq_zero_of_bialgHom_of_isLocalRing_of_finrank_eq_prime_pow_of_irreducible.nuq_C"
variable {R U}

lemma nuq_mul_apply (f g : nuq_C R U) (v : U) : (f * g) v = f v * g v := rfl
lemma nuq_one_apply (v : U) : (1 : nuq_C R U) v = 1 := rfl
lemma nuq_zero_apply (v : U) : (0 : nuq_C R U) v = 0 := rfl
lemma nuq_algebraMap_apply (r : R) (v : U) : (algebraMap R (nuq_C R U) r) v = r := rfl

@[scoped ext] lemma nuq_ext {f g : nuq_C R U} (h : ∀ v, f v = g v) : f = g := funext h

variable [DecidableEq U]

def nuq_δ (u : U) : nuq_C R U := (Pi.single u (1 : R) : U → R)

lemma nuq_δ_apply (u v : U) : (nuq_δ u : nuq_C R U) v = if v = u then 1 else 0 :=
  Pi.single_apply u (1 : R) v

lemma nuq_δ_mul_δ (u v : U) : (nuq_δ u * nuq_δ v : nuq_C R U) = if u = v then nuq_δ u else 0 := by
  ext w
  simp only [nuq_mul_apply, nuq_δ_apply]
  split_ifs <;> simp_all [nuq_δ_apply, nuq_zero_apply]

lemma nuq_δ_mul_δ_self (u : U) : (nuq_δ u * nuq_δ u : nuq_C R U) = nuq_δ u := by
  rw [nuq_δ_mul_δ, if_pos rfl]

variable [Fintype U]

lemma nuq_one_eq : (1 : nuq_C R U) = ∑ w : U, nuq_δ w := by
  ext v
  change (1 : R) = (∑ w : U, (Pi.single w (1 : R) : U → R)) v
  simp [Finset.sum_apply, Pi.single_apply]

noncomputable def nuq_basis : Module.Basis U R (nuq_C R U) := Pi.basisFun R U

lemma nuq_basis_apply (u : U) : (nuq_basis u : nuq_C R U) = nuq_δ u := Pi.basisFun_apply R U u

scoped instance nuq_C.instFinite : Module.Finite R (nuq_C R U) := Module.Finite.of_basis nuq_basis
p2m_reactivate "P2MW.S_HopfAlgebra_apply_eq_zero_of_bialgHom_of_isLocalRing_of_finrank_eq_prime_pow_of_irreducible.nuq_C"
scoped instance nuq_C.instFree : Module.Free R (nuq_C R U) := Module.Free.of_basis nuq_basis

p2m_reactivate "P2MW.S_HopfAlgebra_apply_eq_zero_of_bialgHom_of_isLocalRing_of_finrank_eq_prime_pow_of_irreducible.nuq_C"
lemma nuq_finrank [Nontrivial R] : Module.finrank R (nuq_C R U) = Fintype.card U := by
  rw [Module.finrank_eq_card_basis nuq_basis]

noncomputable def nuq_comul : nuq_C R U →ₗ[R] nuq_C R U ⊗[R] nuq_C R U :=
  nuq_basis.constr R fun w => ∑ u : U, (nuq_δ u : nuq_C R U) ⊗ₜ[R] (nuq_δ (w - u) : nuq_C R U)

lemma nuq_comul_δ (w : U) :
    nuq_comul (nuq_δ w : nuq_C R U) = ∑ u : U, (nuq_δ u : nuq_C R U) ⊗ₜ[R] (nuq_δ (w - u)) := by
  rw [← nuq_basis_apply]; exact Module.Basis.constr_basis _ _ _ _

def nuq_counit : nuq_C R U →ₗ[R] R where
  toFun f := f 0
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

lemma nuq_counit_apply (f : nuq_C R U) : nuq_counit f = f 0 := rfl

lemma nuq_counit_δ (w : U) : nuq_counit (nuq_δ w : nuq_C R U) = if w = 0 then 1 else 0 := by
  rw [nuq_counit_apply, nuq_δ_apply]; simp only [@eq_comm U 0 w]

noncomputable def nuq_antipode : nuq_C R U →ₗ[R] nuq_C R U :=
  nuq_basis.constr R fun w => (nuq_δ (-w) : nuq_C R U)

lemma nuq_antipode_δ (w : U) : nuq_antipode (nuq_δ w : nuq_C R U) = nuq_δ (-w) := by
  rw [← nuq_basis_apply]; exact Module.Basis.constr_basis _ _ _ _

noncomputable scoped instance nuq_C.instCoalgebraStruct : CoalgebraStruct R (nuq_C R U) where
  comul := nuq_comul
  counit := nuq_counit

p2m_reactivate "P2MW.S_HopfAlgebra_apply_eq_zero_of_bialgHom_of_isLocalRing_of_finrank_eq_prime_pow_of_irreducible.nuq_C"
lemma nuq_comul_eq : (CoalgebraStruct.comul : nuq_C R U →ₗ[R] _) = nuq_comul := rfl
lemma nuq_counit_eq : (CoalgebraStruct.counit : nuq_C R U →ₗ[R] R) = nuq_counit := rfl

noncomputable scoped instance nuq_C.instCoalgebra : Coalgebra R (nuq_C R U) where
  coassoc := by
    apply nuq_basis.ext; intro w
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, nuq_basis_apply, nuq_comul_eq,
      nuq_comul_δ, map_sum, LinearMap.rTensor_tmul, LinearMap.lTensor_tmul,
      TensorProduct.sum_tmul, TensorProduct.tmul_sum, TensorProduct.assoc_tmul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun a _ => ?_
    refine Fintype.sum_equiv (Equiv.subRight a) _ _ fun u => ?_
    simp only [Equiv.subRight_apply]
    congr 3
    abel
  rTensor_counit_comp_comul := by
    apply nuq_basis.ext; intro w
    simp only [LinearMap.comp_apply, nuq_basis_apply, nuq_comul_eq, nuq_counit_eq,
      nuq_comul_δ, map_sum, LinearMap.rTensor_tmul, nuq_counit_δ, TensorProduct.ite_tmul,
      Finset.sum_ite_eq', Finset.mem_univ, if_true, sub_zero,
      TensorProduct.mk_apply]
  lTensor_counit_comp_comul := by
    apply nuq_basis.ext; intro w
    simp only [LinearMap.comp_apply, nuq_basis_apply, nuq_comul_eq, nuq_counit_eq,
      nuq_comul_δ, map_sum, LinearMap.lTensor_tmul, nuq_counit_δ, TensorProduct.tmul_ite,
      sub_eq_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true,
      LinearMap.flip_apply, TensorProduct.mk_apply]

p2m_reactivate "P2MW.S_HopfAlgebra_apply_eq_zero_of_bialgHom_of_isLocalRing_of_finrank_eq_prime_pow_of_irreducible.nuq_C"
lemma nuq_comul_one : nuq_comul (1 : nuq_C R U) = 1 := by
  rw [nuq_one_eq, map_sum]
  simp only [nuq_comul_δ]
  rw [Finset.sum_comm]
  simp_rw [← TensorProduct.tmul_sum]
  have h : ∀ u : U, (∑ w : U, (nuq_δ (w - u) : nuq_C R U)) = ∑ w : U, nuq_δ w := fun u =>
    Fintype.sum_equiv (Equiv.subRight u) _ _ fun w => rfl
  simp_rw [h, ← TensorProduct.sum_tmul, ← nuq_one_eq, Algebra.TensorProduct.one_def]

lemma nuq_comul_δ_mul_δ (i j : U) :
    nuq_comul (nuq_δ i * nuq_δ j : nuq_C R U) = nuq_comul (nuq_δ i) * nuq_comul (nuq_δ j) := by
  rw [nuq_δ_mul_δ, nuq_comul_δ, nuq_comul_δ, Finset.sum_mul_sum]
  simp_rw [Algebra.TensorProduct.tmul_mul_tmul, nuq_δ_mul_δ, TensorProduct.ite_tmul,
    Finset.sum_ite_eq, Finset.mem_univ, if_true, sub_left_inj]
  by_cases h : i = j
  · subst h; simp [nuq_comul_δ]
  · simp [h]

lemma nuq_mul_compr₂_comul :
    (LinearMap.mul R (nuq_C R U)).compr₂ nuq_comul =
      (LinearMap.mul R (nuq_C R U ⊗[R] nuq_C R U)).compl₁₂ nuq_comul nuq_comul := by
  apply nuq_basis.ext; intro i; apply nuq_basis.ext; intro j
  simp only [LinearMap.compr₂_apply, LinearMap.compl₁₂_apply, LinearMap.mul_apply',
    nuq_basis_apply, nuq_comul_δ_mul_δ]

noncomputable scoped instance nuq_C.instBialgebra : Bialgebra R (nuq_C R U) where
  counit_one := rfl
  mul_compr₂_counit := by ext f g; rfl
  comul_one := nuq_comul_one
  mul_compr₂_comul := nuq_mul_compr₂_comul

p2m_reactivate "P2MW.S_HopfAlgebra_apply_eq_zero_of_bialgHom_of_isLocalRing_of_finrank_eq_prime_pow_of_irreducible.nuq_C"
noncomputable scoped instance nuq_C.instHopfAlgebra : HopfAlgebra R (nuq_C R U) where
  antipode := nuq_antipode
  mul_antipode_rTensor_comul := by
    apply nuq_basis.ext; intro w
    simp only [LinearMap.comp_apply, nuq_basis_apply, nuq_comul_eq, nuq_counit_eq,
      nuq_comul_δ, map_sum, LinearMap.rTensor_tmul, nuq_antipode_δ, LinearMap.mul'_apply,
      nuq_δ_mul_δ, Algebra.linearMap_apply, nuq_counit_δ]
    have key : ∀ u : U, (-u = w - u) ↔ w = 0 := fun u => by
      rw [eq_sub_iff_add_eq, neg_add_cancel]; exact eq_comm
    simp_rw [key]
    by_cases hw : w = 0
    · subst hw
      simp only [if_true, map_one, nuq_one_eq]
      exact Fintype.sum_equiv (Equiv.neg U) _ _ fun u => rfl
    · simp [hw]
  mul_antipode_lTensor_comul := by
    apply nuq_basis.ext; intro w
    simp only [LinearMap.comp_apply, nuq_basis_apply, nuq_comul_eq, nuq_counit_eq,
      nuq_comul_δ, map_sum, LinearMap.lTensor_tmul, nuq_antipode_δ, LinearMap.mul'_apply,
      nuq_δ_mul_δ, Algebra.linearMap_apply, nuq_counit_δ, neg_sub]
    have key : ∀ u : U, (u = u - w) ↔ w = 0 := fun u => by
      constructor
      · intro h; have h2 : u + w = u := eq_sub_iff_add_eq.mp h; simpa using h2
      · rintro rfl; simp
    simp_rw [key]
    by_cases hw : w = 0
    · subst hw
      simp only [if_true, map_one, nuq_one_eq]
    · simp [hw]

p2m_reactivate "P2MW.S_HopfAlgebra_apply_eq_zero_of_bialgHom_of_isLocalRing_of_finrank_eq_prime_pow_of_irreducible.nuq_C"
scoped instance nuq_C.instIsCocomm : Coalgebra.IsCocomm R (nuq_C R U) where
  comm_comp_comul := by
    apply nuq_basis.ext; intro w
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, nuq_basis_apply, nuq_comul_eq,
      nuq_comul_δ, map_sum, TensorProduct.comm_tmul]
    exact Fintype.sum_equiv (Equiv.subLeft w) _ _ fun u => by simp [sub_sub_cancel]

p2m_reactivate "P2MW.S_HopfAlgebra_apply_eq_zero_of_bialgHom_of_isLocalRing_of_finrank_eq_prime_pow_of_irreducible.nuq_C"
end nuq_ring
p2m_reactivate "P2MW.S_HopfAlgebra_apply_eq_zero_of_bialgHom_of_isLocalRing_of_finrank_eq_prime_pow_of_irreducible.nuq_C"

section nuq_points
variable {R U : Type} [CommRing R] [AddCommGroup U] [DecidableEq U] [Fintype U]
variable (L : Type) [Field L] [Algebra R L]

def nuq_ev (a : U) : nuq_C R U →ₐ[R] L :=
  (Algebra.ofId R L).comp (Pi.evalAlgHom R (fun _ : U => R) a)

lemma nuq_ev_apply (a : U) (f : nuq_C R U) : nuq_ev L a f = algebraMap R L (f a) := rfl

lemma nuq_ev_δ (a u : U) : nuq_ev L a (nuq_δ u : nuq_C R U) = if u = a then 1 else 0 := by
  rw [nuq_ev_apply, nuq_δ_apply]; simp only [@eq_comm U a u]; split_ifs <;> simp

variable {L}

lemma nuq_χ_δ_mul_δ (χ : nuq_C R U →ₐ[R] L) (u v : U) :
    χ (nuq_δ u) * χ (nuq_δ v) = if u = v then χ (nuq_δ u) else 0 := by
  rw [← map_mul, nuq_δ_mul_δ]
  split_ifs <;> simp

lemma nuq_χ_sum_δ (χ : nuq_C R U →ₐ[R] L) : ∑ u : U, χ (nuq_δ u) = 1 := by
  rw [← map_sum, ← nuq_one_eq, map_one]

lemma nuq_exists_unique_pt (χ : nuq_C R U →ₐ[R] L) : ∃! a : U, χ (nuq_δ a) = 1 := by
  obtain ⟨a, ha⟩ : ∃ a : U, χ (nuq_δ a) ≠ 0 := by
    by_contra h
    push Not at h
    have := nuq_χ_sum_δ χ
    simp [h] at this
  have ha1 : χ (nuq_δ a) = 1 := by
    have h2 := nuq_χ_δ_mul_δ χ a a
    rw [if_pos rfl] at h2
    exact mul_left_cancel₀ ha (h2.trans (mul_one _).symm)
  refine ⟨a, ha1, fun b hb => ?_⟩
  by_contra hne
  have h3 := nuq_χ_δ_mul_δ χ b a
  rw [hb, ha1, if_neg hne, mul_one] at h3
  exact one_ne_zero h3

noncomputable def nuq_pt (χ : nuq_C R U →ₐ[R] L) : U := (nuq_exists_unique_pt χ).exists.choose

lemma nuq_pt_spec (χ : nuq_C R U →ₐ[R] L) : χ (nuq_δ (nuq_pt χ)) = 1 :=
  (nuq_exists_unique_pt χ).exists.choose_spec

lemma nuq_pt_eq {χ : nuq_C R U →ₐ[R] L} {a : U} (h : χ (nuq_δ a) = 1) : nuq_pt χ = a :=
  (nuq_exists_unique_pt χ).unique (nuq_pt_spec χ) h

lemma nuq_χ_δ_eq_zero (χ : nuq_C R U →ₐ[R] L) {u : U} (hu : u ≠ nuq_pt χ) : χ (nuq_δ u) = 0 := by
  have h := nuq_χ_δ_mul_δ χ u (nuq_pt χ)
  rwa [nuq_pt_spec, mul_one, if_neg hu] at h

lemma nuq_pt_ev (a : U) : nuq_pt (nuq_ev L a : nuq_C R U →ₐ[R] L) = a :=
  nuq_pt_eq (by rw [nuq_ev_δ, if_pos rfl])

lemma nuq_ev_pt (χ : nuq_C R U →ₐ[R] L) : nuq_ev L (nuq_pt χ) = χ := by
  apply AlgHom.toLinearMap_injective
  apply nuq_basis.ext
  intro u
  simp only [AlgHom.toLinearMap_apply, nuq_basis_apply, nuq_ev_δ]
  split_ifs with h
  · rw [h, nuq_pt_spec]
  · rw [nuq_χ_δ_eq_zero χ h]

variable (L)

noncomputable def nuq_e₂ : WithConv (nuq_C R U →ₐ[R] L) ≃ U where
  toFun χ := nuq_pt χ.ofConv
  invFun a := WithConv.toConv (nuq_ev L a)
  left_inv χ := by simp only [nuq_ev_pt]
  right_inv a := nuq_pt_ev a

lemma nuq_e₂_apply (χ : WithConv (nuq_C R U →ₐ[R] L)) : nuq_e₂ L χ = nuq_pt χ.ofConv := rfl

lemma nuq_e₂_add (f g : WithConv (nuq_C R U →ₐ[R] L)) :
    nuq_e₂ L (f * g) = nuq_e₂ L f + nuq_e₂ L g := by
  simp only [nuq_e₂_apply]
  apply nuq_pt_eq
  change (f * g) (nuq_δ (nuq_pt f.ofConv + nuq_pt g.ofConv)) = 1
  rw [AlgHom.convMul_apply, nuq_comul_eq, nuq_comul_δ, map_sum]
  simp only [Algebra.TensorProduct.lift_tmul]
  rw [Finset.sum_eq_single (nuq_pt f.ofConv)]
  · rw [nuq_pt_spec, one_mul, add_sub_cancel_left, nuq_pt_spec]
  · intro u _ hu; rw [nuq_χ_δ_eq_zero _ hu, zero_mul]
  · intro h; exact absurd (Finset.mem_univ _) h

lemma nuq_e₂_act {G : Type} [Group G] [MulSemiringAction G L]
    (σ : G) (f g : WithConv (nuq_C R U →ₐ[R] L)) (h : ∀ x : nuq_C R U, g x = σ • (f x)) :
    nuq_e₂ L g = nuq_e₂ L f := by
  simp only [nuq_e₂_apply]
  apply nuq_pt_eq
  change g (nuq_δ (nuq_pt f.ofConv)) = 1
  rw [h]
  change σ • (f.ofConv (nuq_δ (nuq_pt f.ofConv))) = 1
  rw [nuq_pt_spec, smul_one]

lemma nuq_idem_eq_zero_or_one {S : Type} [CommRing S] [IsLocalRing S] {x : S}
    (h : IsIdempotentElem x) : x = 0 ∨ x = 1 := by
  rcases IsLocalRing.isUnit_or_isUnit_one_sub_self x with hu | hu
  · right
    exact hu.mul_left_cancel (h.eq.trans (mul_one x).symm)
  · left
    have : (1 - x) * x = (1 - x) * 0 := by rw [sub_mul, one_mul, h.eq, sub_self, mul_zero]
    exact hu.mul_left_cancel this

lemma nuq_pt_comp_eq_of_isLocalRing {H₀ : Type} [CommRing H₀] [Algebra R H₀] [IsLocalRing H₀]
    (θ : nuq_C R U →ₐ[R] H₀) (f₁ f₂ : H₀ →ₐ[R] L) :
    nuq_pt (f₁.comp θ) = nuq_pt (f₂.comp θ) := by
  have h1 : f₁ (θ (nuq_δ (nuq_pt (f₁.comp θ)))) = 1 := nuq_pt_spec (f₁.comp θ)
  have hidem : IsIdempotentElem (θ (nuq_δ (nuq_pt (f₁.comp θ)))) := by
    unfold IsIdempotentElem; rw [← map_mul, nuq_δ_mul_δ_self]
  rcases nuq_idem_eq_zero_or_one hidem with h0 | h0
  · rw [h0, map_zero] at h1; exact absurd h1 zero_ne_one
  · symm; apply nuq_pt_eq; rw [AlgHom.comp_apply, h0, map_one]

end nuq_points
p2m_reactivate "P2MW.S_HopfAlgebra_apply_eq_zero_of_bialgHom_of_isLocalRing_of_finrank_eq_prime_pow_of_irreducible.nuq_C"

@[reducible] def nuq_trivAction (G M : Type) [Monoid G] [AddCommGroup M] : DistribMulAction G M where
  smul := fun _ m => m
  one_smul := fun _ => rfl
  mul_smul := fun _ _ _ => rfl
  smul_zero := fun _ => rfl
  smul_add := fun _ _ _ => rfl

theorem solution
    (R : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [CharZero R]
    (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2) (hunif : Irreducible (p : R))
    (K : Type) [Field K] [Algebra R K] [IsFractionRing R K]
    (L : Type) [Field L] [Algebra K L] [Algebra R L] [IsScalarTower R K L] [IsAlgClosed L]
    [Algebra.IsAlgebraic K L]
    {M : Type} [AddCommGroup M] [DistribMulAction (L ≃ₐ[K] L) M]
    (H : Type) [CommRing H] [HopfAlgebra R H] [Module.Finite R H] [Module.Free R H]
    [Coalgebra.IsCocomm R H] (hrank : ∃ a : ℕ, Module.finrank R H = p ^ a)
    (e : WithConv (H →ₐ[R] L) ≃ M)
    (he_add : ∀ f g, e (f * g) = e f + e g)
    (he_act : ∀ (σ : L ≃ₐ[K] L) (f g : WithConv (H →ₐ[R] L)), (∀ x : H, g x = σ (f x)) → e g = σ • (e f))
    (H₀ : Type) [CommRing H₀] [Bialgebra R H₀] (hloc : IsLocalRing H₀) (π : H →ₐc[R] H₀)
    {U : Type} [AddCommGroup U] (hU : ∃ b : ℕ, Nat.card U = p ^ b)
    (φ : M →+ U) (hφ : ∀ (σ : L ≃ₐ[K] L) (m : M), φ (σ • m) = φ m)
    (f₀ : H₀ →ₐ[R] L) :
    φ (e (WithConv.toConv (f₀.comp (π : H →ₐ[R] H₀)))) = 0 := by
  classical
  obtain ⟨b, hb⟩ := hU
  haveI : Finite U := Nat.finite_of_card_ne_zero
    (by rw [hb]; exact pow_ne_zero _ (Fact.out : p.Prime).ne_zero)
  letI : Fintype U := Fintype.ofFinite U
  letI : DistribMulAction (L ≃ₐ[K] L) U := nuq_trivAction (L ≃ₐ[K] L) U
  haveI : IsLocalRing H₀ := hloc
  have hrank₂ : ∃ a : ℕ, Module.finrank R (nuq_C R U) = p ^ a :=
    ⟨b, by rw [nuq_finrank, ← Nat.card_eq_fintype_card, hb]⟩
  have hφ' : ∀ (σ : L ≃ₐ[K] L) (m : M), φ (σ • m) = σ • φ m := fun σ m => hφ σ m
  have he₂_act : ∀ (σ : L ≃ₐ[K] L) (f g : WithConv (nuq_C R U →ₐ[R] L)),
      (∀ x : nuq_C R U, g x = σ (f x)) → nuq_e₂ L g = σ • (nuq_e₂ L f) :=
    fun σ f g h => nuq_e₂_act L σ f g h
  obtain ⟨g, hg, -⟩ :=
    HopfAlgebra.existsUnique_bialgHom_forall_apply_comp_eq_of_finrank_eq_prime_pow_of_irreducible
      R p hp2 hunif K L H hrank e he_add he_act (nuq_C R U) hrank₂ (nuq_e₂ L) (nuq_e₂_add L)
      he₂_act φ hφ'
  rw [← hg (WithConv.toConv (f₀.comp (π : H →ₐ[R] H₀)))]
  change nuq_pt ((f₀.comp (π : H →ₐ[R] H₀)).comp (g : nuq_C R U →ₐ[R] H)) = 0
  rw [AlgHom.comp_assoc, nuq_pt_comp_eq_of_isLocalRing (L := L)
    (θ := (π : H →ₐ[R] H₀).comp (g : nuq_C R U →ₐ[R] H)) (f₁ := f₀)
    (f₂ := (Algebra.ofId R L).comp (Bialgebra.counitAlgHom R H₀))]
  apply nuq_pt_eq
  simp only [AlgHom.comp_apply, Bialgebra.counitAlgHom_apply, BialgHom.coe_toAlgHom,
    CoalgHomClass.counit_comp_apply, nuq_counit_eq, nuq_counit_δ, if_true, map_one]

end S_HopfAlgebra_apply_eq_zero_of_bialgHom_of_isLocalRing_of_finrank_eq_prime_pow_of_irreducible
end P2MW
export P2MW.S_HopfAlgebra_apply_eq_zero_of_bialgHom_of_isLocalRing_of_finrank_eq_prime_pow_of_irreducible (solution)
