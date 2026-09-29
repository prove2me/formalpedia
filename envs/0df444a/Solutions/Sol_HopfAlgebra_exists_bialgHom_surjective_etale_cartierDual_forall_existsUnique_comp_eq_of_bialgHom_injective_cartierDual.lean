-- Prove2me | solution 1 for HopfAlgebra.exists_bialgHom_surjective_etale_cartierDual_forall_existsUnique_comp_eq_of_bialgHom_injective_cartierDual
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.85352+00:00
-- url     : https://prove2.me/submissions/4452e031-413d-50e8-b586-69fd689fdef2

import Mathlib
import Definitions.Def_HopfAlgebra_CartierDual
import Definitions.Def_HopfAlgebra_CartierDualMap
import Definitions.Def_HopfAlgebra_CartierDualInstances
import Theorems.Thm_CartierDual_exists_bialgEquiv_bidual
import Theorems.Thm_CartierDual_exists_bialgEquiv_baseChange_forall_pairing_symm_tmul
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_HopfAlgebra_exists_bialgHom_surjective_etale_cartierDual_forall_existsUnique_comp_eq_of_bialgHom_injective_cartierDual
p2m_attr_erase "instance" "CartierDual.instAlgebraBaseChangeDual CartierDual.instRingBaseChangeDual CartierDual.instModuleRestrictBaseChange CartierDual.instIsScalarTowerRestrictBaseChange instIsScalarTowerTensorProduct_definitions"
p2m_attr_erase "simp" "HopfAlgebra.mem_vanishingIdealOfPoints_iff HopfAlgebra.liftPoint_mk HopfAlgebra.mem_ptSet_iff CartierDual.dualBaseChangeLin_tmul CartierDual.dualBaseChange_tmul mem_flatClosure_iff"

set_option autoImplicit false

open scoped TensorProduct

universe u v

namespace HopfTransfer

variable {R : Type*} [CommRing R]
variable {Q : Type*} [CommRing Q] [Algebra R Q]
variable {D : Type*} [CommRing D] [HopfAlgebra R D]
variable (e : Q ≃ₐ[R] D)

private noncomputable def _root_.HopfTransfer.comulAlgHom : Q →ₐ[R] Q ⊗[R] Q :=
  (Algebra.TensorProduct.map (e.symm : D →ₐ[R] Q) (e.symm : D →ₐ[R] Q)).comp
    ((Bialgebra.comulAlgHom R D).comp (e : Q →ₐ[R] D))

p2m_export "HopfTransfer" "comulAlgHom"

private noncomputable def _root_.HopfTransfer.counitAlgHom : Q →ₐ[R] R := (Bialgebra.counitAlgHom R D).comp (e : Q →ₐ[R] D)

p2m_export "HopfTransfer" "counitAlgHom"
theorem counitAlgHom_apply (q : Q) : counitAlgHom e q = Coalgebra.counit (R := R) (e q) := rfl

theorem comulAlgHom_apply' (q : Q) :
    comulAlgHom e q = Algebra.TensorProduct.map (e.symm : D →ₐ[R] Q) (e.symm : D →ₐ[R] Q)
      (Coalgebra.comul (R := R) (e q)) := rfl

theorem comulAlgHom_eq_sum (q : Q) {ιrepr : Type*} (repr : Coalgebra.Repr R (e q) ιrepr) :
    comulAlgHom e q = ∑ i ∈ repr.index, e.symm (repr.left i) ⊗ₜ[R] e.symm (repr.right i) := by
  rw [comulAlgHom_apply', ← repr.eq, map_sum]
  simp only [Algebra.TensorProduct.map_tmul, AlgEquiv.coe_algHom]

theorem comulAlgHom_symm_eq_sum (x : D) {ιrepr : Type*} (repr : Coalgebra.Repr R x ιrepr) :
    comulAlgHom e (e.symm x) = ∑ i ∈ repr.index, e.symm (repr.left i) ⊗ₜ[R] e.symm (repr.right i) := by
  rw [comulAlgHom_apply', e.apply_symm_apply, ← repr.eq, map_sum]
  simp only [Algebra.TensorProduct.map_tmul, AlgEquiv.coe_algHom]

theorem h_rTensor :
    (Algebra.TensorProduct.map (counitAlgHom e) (.id R Q)).comp (comulAlgHom e) =
      (Algebra.TensorProduct.lid R Q).symm := by
  apply AlgHom.ext
  intro q
  let repr := Coalgebra.Repr.arbitrary R (e q)
  have key := congrArg (TensorProduct.map (LinearMap.id : R →ₗ[R] R) e.symm.toLinearEquiv.toLinearMap)
    (Coalgebra.sum_counit_tmul_eq repr)
  simp only [map_sum, TensorProduct.map_tmul, LinearMap.id_apply, LinearEquiv.coe_coe,
    AlgEquiv.toLinearEquiv_apply, e.symm_apply_apply] at key
  rw [AlgHom.comp_apply, comulAlgHom_eq_sum e q repr, map_sum]
  simp only [Algebra.TensorProduct.map_tmul, AlgHom.coe_id, id_eq, counitAlgHom_apply, e.apply_symm_apply]
  rw [key]
  rfl

theorem h_lTensor :
    (Algebra.TensorProduct.map (.id R Q) (counitAlgHom e)).comp (comulAlgHom e) =
      (Algebra.TensorProduct.rid R R Q).symm := by
  apply AlgHom.ext
  intro q
  let repr := Coalgebra.Repr.arbitrary R (e q)
  have key := congrArg (TensorProduct.map e.symm.toLinearEquiv.toLinearMap (LinearMap.id : R →ₗ[R] R))
    (Coalgebra.sum_tmul_counit_eq repr)
  simp only [map_sum, TensorProduct.map_tmul, LinearMap.id_apply, LinearEquiv.coe_coe,
    AlgEquiv.toLinearEquiv_apply, e.symm_apply_apply] at key
  rw [AlgHom.comp_apply, comulAlgHom_eq_sum e q repr, map_sum]
  simp only [Algebra.TensorProduct.map_tmul, AlgHom.coe_id, id_eq, counitAlgHom_apply, e.apply_symm_apply]
  rw [key]
  rfl

theorem h_coassoc :
    (Algebra.TensorProduct.assoc R R R Q Q Q).toAlgHom.comp
        ((Algebra.TensorProduct.map (comulAlgHom e) (.id R Q)).comp (comulAlgHom e)) =
      (Algebra.TensorProduct.map (.id R Q) (comulAlgHom e)).comp (comulAlgHom e) := by
  apply AlgHom.ext
  intro q
  let repr := Coalgebra.Repr.arbitrary R (e q)
  let a₁ := fun i => Coalgebra.Repr.arbitrary R (repr.left i)
  let a₂ := fun i => Coalgebra.Repr.arbitrary R (repr.right i)
  have key := congrArg (TensorProduct.map e.symm.toLinearEquiv.toLinearMap
    (TensorProduct.map e.symm.toLinearEquiv.toLinearMap e.symm.toLinearEquiv.toLinearMap))
    (Coalgebra.sum_tmul_tmul_eq repr a₁ a₂)
  simp only [map_sum, TensorProduct.map_tmul, LinearEquiv.coe_coe, AlgEquiv.toLinearEquiv_apply] at key
  rw [AlgHom.comp_apply, AlgHom.comp_apply, AlgHom.comp_apply, comulAlgHom_eq_sum e q repr, map_sum, map_sum,
    map_sum]
  simp only [Algebra.TensorProduct.map_tmul, AlgHom.coe_id, id_eq, comulAlgHom_symm_eq_sum e _ (a₁ _),
    comulAlgHom_symm_eq_sum e _ (a₂ _), TensorProduct.sum_tmul, TensorProduct.tmul_sum, map_sum]
  exact key

@[reducible] noncomputable def bialgebra : Bialgebra R Q :=
  Bialgebra.ofAlgHom (comulAlgHom e) (counitAlgHom e) (h_coassoc e) (h_rTensor e) (h_lTensor e)

private noncomputable def _root_.HopfTransfer.antipode : Q →ₗ[R] Q :=
  e.symm.toLinearEquiv.toLinearMap ∘ₗ HopfAlgebraStruct.antipode R ∘ₗ e.toLinearEquiv.toLinearMap

p2m_export "HopfTransfer" "antipode"
theorem antipode_apply (q : Q) : antipode e q = e.symm (HopfAlgebraStruct.antipode R (e q)) := rfl

@[reducible] noncomputable def hopfAlgebra : HopfAlgebra R Q :=
  letI := bialgebra e
  { antipode := antipode e
    mul_antipode_rTensor_comul := by
      apply LinearMap.ext
      intro q
      let repr := Coalgebra.Repr.arbitrary R (e q)
      change LinearMap.mul' R Q ((antipode e).rTensor Q (comulAlgHom e q)) =
        algebraMap R Q (Coalgebra.counit (R := R) (e q))
      rw [comulAlgHom_eq_sum e q repr, map_sum, map_sum]
      simp only [LinearMap.rTensor_tmul, LinearMap.mul'_apply, antipode_apply, e.apply_symm_apply, ← map_mul,
        ← map_sum, HopfAlgebra.sum_antipode_mul_eq_algebraMap_counit, AlgEquiv.commutes]
    mul_antipode_lTensor_comul := by
      apply LinearMap.ext
      intro q
      let repr := Coalgebra.Repr.arbitrary R (e q)
      change LinearMap.mul' R Q ((antipode e).lTensor Q (comulAlgHom e q)) =
        algebraMap R Q (Coalgebra.counit (R := R) (e q))
      rw [comulAlgHom_eq_sum e q repr, map_sum, map_sum]
      simp only [LinearMap.lTensor_tmul, LinearMap.mul'_apply, antipode_apply, e.apply_symm_apply, ← map_mul,
        ← map_sum, HopfAlgebra.sum_mul_antipode_eq_algebraMap_counit, AlgEquiv.commutes] }

noncomputable def bialgEquiv : letI := bialgebra e; Q ≃ₐc[R] D :=
  letI := bialgebra e
  BialgEquiv.ofAlgEquiv e rfl
    (by
      apply AlgHom.ext
      intro q
      let repr := Coalgebra.Repr.arbitrary R (e q)
      change Algebra.TensorProduct.map (e : Q →ₐ[R] D) (e : Q →ₐ[R] D) (comulAlgHom e q) =
        Coalgebra.comul (R := R) (e q)
      rw [comulAlgHom_eq_sum e q repr, map_sum]
      simp only [Algebra.TensorProduct.map_tmul, AlgEquiv.coe_algHom, e.apply_symm_apply, repr.eq])

theorem bialgEquiv_apply (q : Q) : (letI := bialgebra e; bialgEquiv e q) = e q := rfl

end HopfTransfer

namespace HopfTransfer

variable {R : Type*} [CommRing R] {Q : Type*} [CommRing Q] [Algebra R Q] {D : Type*} [CommRing D] [HopfAlgebra R D]

theorem isCocomm (e : Q ≃ₐ[R] D) [Coalgebra.IsCocomm R D] : letI := bialgebra e; Coalgebra.IsCocomm R Q := by
  letI := bialgebra e
  refine ⟨?_⟩
  apply LinearMap.ext
  intro q
  let repr := Coalgebra.Repr.arbitrary R (e q)
  change (TensorProduct.comm R Q Q) (comulAlgHom e q) = comulAlgHom e q
  have key := congrArg (TensorProduct.map e.symm.toLinearEquiv.toLinearMap e.symm.toLinearEquiv.toLinearMap)
    (Coalgebra.comm_comul R (e q))
  rw [← repr.eq, map_sum, map_sum, map_sum] at key
  simp only [TensorProduct.comm_tmul, TensorProduct.map_tmul, LinearEquiv.coe_coe, AlgEquiv.toLinearEquiv_apply] at key
  rw [comulAlgHom_eq_sum e q repr, map_sum]
  simp only [TensorProduct.comm_tmul]
  exact key

end HopfTransfer

namespace DualiseAux

theorem exists_retraction {R : Type*} [CommRing R] {E L : Type*} [AddCommGroup E] [Module R E] [AddCommGroup L]
    [Module R L] (ι : E →ₗ[R] L) (hι : Function.Injective ι) (hfree : Module.Free R (L ⧸ LinearMap.range ι)) :
    ∃ r : L →ₗ[R] E, r ∘ₗ ι = LinearMap.id := by
  haveI := hfree
  obtain ⟨s, hs⟩ := Module.projective_lifting_property (LinearMap.range ι).mkQ (LinearMap.id) (Submodule.mkQ_surjective _)

  have hmem : ∀ x : L, x - s ((LinearMap.range ι).mkQ x) ∈ LinearMap.range ι := by
    intro x
    rw [← Submodule.Quotient.mk_eq_zero, ← Submodule.mkQ_apply, map_sub, ← LinearMap.comp_apply, hs,
      LinearMap.id_apply, sub_self]
  let eι := LinearEquiv.ofInjective ι hι
  refine ⟨eι.symm.toLinearMap ∘ₗ LinearMap.codRestrict (LinearMap.range ι) (LinearMap.id - s ∘ₗ (LinearMap.range ι).mkQ)
    (fun x => hmem x), ?_⟩
  apply LinearMap.ext
  intro y
  apply eι.injective
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply, LinearMap.id_apply]
  apply Subtype.ext
  simp only [LinearMap.codRestrict_apply, LinearMap.sub_apply, LinearMap.id_apply, LinearMap.comp_apply,
    Submodule.mkQ_apply, LinearEquiv.ofInjective_apply, eι]
  rw [(Submodule.Quotient.mk_eq_zero _).2 (LinearMap.mem_range_self ι y), map_zero, sub_zero]

theorem map_surjective_of_free_quotient {R : Type u} [CommRing R]
    {E : Type*} [CommRing E] [Bialgebra R E] [Module.Finite R E] [Module.Free R E]
    {L : Type*} [CommRing L] [Bialgebra R L] [Module.Finite R L] [Module.Free R L]
    (ι : E →ₐc[R] L) (hι : Function.Injective ι)
    (hsplit : Module.Free R (L ⧸ (LinearMap.range (ι : E →ₐ[R] L).toLinearMap : Submodule R L))) :
    Function.Surjective (CartierDual.map ι) := by
  obtain ⟨r, hr⟩ := exists_retraction (ι : E →ₐ[R] L).toLinearMap hι hsplit
  intro ψ
  refine ⟨CartierDual.ofDual R L ((CartierDual.toDual R E ψ) ∘ₗ r), ?_⟩
  apply CartierDual.ext
  intro x
  rw [CartierDual.map_apply]
  change (CartierDual.toDual R E ψ) (r (ι x)) = ψ x
  have := LinearMap.congr_fun hr x
  simp only [LinearMap.comp_apply, AlgHom.toLinearMap_apply, LinearMap.id_apply] at this
  change (CartierDual.toDual R E ψ) (r ((ι : E →ₐ[R] L) x)) = ψ x
  rw [this]
  rfl

end DualiseAux

set_option maxHeartbeats 6400000 in
set_option synthInstance.maxHeartbeats 1600000 in

theorem solution
    (R : Type u) [CommRing R]
    (H : Type v) [CommRing H] [HopfAlgebra R H] [Coalgebra.IsCocomm R H]
    [Module.Finite R H] [Module.Free R H]

    (E : Type (max u v)) [CommRing E] [HopfAlgebra R E] [Coalgebra.IsCocomm R E]
    [Module.Free R E] [Module.Finite R E] (ι : E →ₐc[R] CartierDual R H)
    (hι : Function.Injective ι)
    (hE : Algebra.Etale R E)
    (huniv : ∀ (E' : Type (max u v)) [CommRing E'] [HopfAlgebra R E'] [Coalgebra.IsCocomm R E']
        [Module.Free R E'] [Module.Finite R E'] [Algebra.Etale R E']
        (f : E' →ₐc[R] CartierDual R H), ∃! g : E' →ₐc[R] E, ι.comp g = f)
    (hsplit : Module.Free R (CartierDual R H ⧸
      (LinearMap.range (ι : E →ₐ[R] CartierDual R H).toLinearMap : Submodule R (CartierDual R H))))
    (hbc : ∀ (R' : Type u) [CommRing R'] [HenselianLocalRing R'] [Algebra R R'],
        IsLocalHom (algebraMap R R') →
        Algebra.Etale R' (R' ⊗[R] E) ∧
        ∀ (E' : Type (max u v)) [CommRing E'] [HopfAlgebra R' E'] [Coalgebra.IsCocomm R' E']
          [Module.Free R' E'] [Module.Finite R' E'] [Algebra.Etale R' E']
          (f : E' →ₐc[R'] R' ⊗[R] CartierDual R H),
            ∃! g : E' →ₐc[R'] R' ⊗[R] E,
              (Bialgebra.TensorProduct.map (BialgHom.id R' R') ι).comp g = f) :
    ∃ (M : Type v) (_ : CommRing M) (_ : HopfAlgebra R M) (_ : Coalgebra.IsCocomm R M)
      (_ : Module.Free R M) (_ : Module.Finite R M) (π : H →ₐc[R] M),
      Function.Surjective π ∧

      Algebra.Etale R (CartierDual R M) ∧

      (∀ (M' : Type v) [CommRing M'] [HopfAlgebra R M'] [Coalgebra.IsCocomm R M']
          [Module.Free R M'] [Module.Finite R M'] [Algebra.Etale R (CartierDual R M')]
          (f : H →ₐc[R] M'), ∃! g : M →ₐc[R] M', g.comp π = f) ∧

      (∀ φ : H →ₐc[R] H, ∃! ψ : M →ₐc[R] M, ψ.comp π = π.comp φ) ∧

      (∀ (R' : Type u) [CommRing R'] [HenselianLocalRing R'] [Algebra R R'],
          IsLocalHom (algebraMap R R') →
          Algebra.Etale R' (CartierDual R' (R' ⊗[R] M)) ∧
          ∀ (N : Type v) [CommRing N] [HopfAlgebra R' N] [Coalgebra.IsCocomm R' N]
            [Module.Free R' N] [Module.Finite R' N] [Algebra.Etale R' (CartierDual R' N)]
            (f : R' ⊗[R] H →ₐc[R'] N),
              ∃! g : R' ⊗[R] M →ₐc[R'] N,
                g.comp (Bialgebra.TensorProduct.map (BialgHom.id R' R') π) = f) := by
  classical

  obtain ⟨θ, hθ⟩ := CartierDual.exists_bialgEquiv_bidual R H

  let π₀ : H →ₐc[R] CartierDual R E := (CartierDual.map ι).comp θ.toBialgHom
  have hπ₀ : Function.Surjective π₀ := by
    change Function.Surjective ((CartierDual.map ι) ∘ θ)
    exact (DualiseAux.map_surjective_of_free_quotient ι hι hsplit).comp θ.surjective

  let eM : (H ⧸ RingHom.ker (π₀ : H →ₐ[R] CartierDual R E)) ≃ₐ[R] CartierDual R E :=
    Ideal.quotientKerAlgEquivOfSurjective (f := (π₀ : H →ₐ[R] CartierDual R E)) hπ₀
  letI : HopfAlgebra R (H ⧸ RingHom.ker (π₀ : H →ₐ[R] CartierDual R E)) := HopfTransfer.hopfAlgebra eM
  haveI : Coalgebra.IsCocomm R (H ⧸ RingHom.ker (π₀ : H →ₐ[R] CartierDual R E)) := HopfTransfer.isCocomm eM
  let eB : (H ⧸ RingHom.ker (π₀ : H →ₐ[R] CartierDual R E)) ≃ₐc[R] CartierDual R E := HopfTransfer.bialgEquiv eM
  haveI : Module.Free R (H ⧸ RingHom.ker (π₀ : H →ₐ[R] CartierDual R E)) := Module.Free.of_equiv eB.toLinearEquiv.symm
  haveI : Module.Finite R (H ⧸ RingHom.ker (π₀ : H →ₐ[R] CartierDual R E)) := Module.Finite.equiv eB.toLinearEquiv.symm
  let π : H →ₐc[R] (H ⧸ RingHom.ker (π₀ : H →ₐ[R] CartierDual R E)) := eB.symm.toBialgHom.comp π₀
  have hπ : Function.Surjective π := by
    change Function.Surjective (eB.symm ∘ π₀)
    exact eB.symm.surjective.comp hπ₀

  obtain ⟨θE, hθE⟩ := CartierDual.exists_bialgEquiv_bidual R E
  haveI := hE
  have hMet : Algebra.Etale R (CartierDual R (H ⧸ RingHom.ker (π₀ : H →ₐ[R] CartierDual R E))) :=
    Algebra.Etale.of_equiv (θE.trans (CartierDual.congr eB)).toAlgEquiv

  set Mq : Type v := H ⧸ RingHom.ker (π₀ : H →ₐ[R] CartierDual R E) with hMq
  have heBπ : ∀ h : H, eB (π h) = π₀ h := fun h => eB.apply_symm_apply (π₀ h)
  have hπ₀θ : ∀ (h : H) (a : E), π₀ h a = ι a h := fun h a => by
    change (CartierDual.map ι (θ h)) a = ι a h
    rw [CartierDual.map_apply, hθ]

  haveI : Algebra.Etale R (CartierDual R Mq) := hMet
  have hUniv : ∀ (M' : Type v) [CommRing M'] [HopfAlgebra R M'] [Coalgebra.IsCocomm R M']
      [Module.Free R M'] [Module.Finite R M'] [Algebra.Etale R (CartierDual R M')]
      (f : H →ₐc[R] M'), ∃! g : Mq →ₐc[R] M', g.comp π = f := by
    intro M' _ _ _ _ _ _ f
    obtain ⟨θ', hθ'⟩ := CartierDual.exists_bialgEquiv_bidual R M'
    obtain ⟨g', hg', -⟩ := huniv (CartierDual R M') (CartierDual.map f)
    let g : Mq →ₐc[R] M' := (θ'.symm.toBialgHom.comp (CartierDual.map g')).comp eB.toBialgHom
    have hcomp : g.comp π = f := by
      apply BialgHom.ext
      intro h
      change θ'.symm (CartierDual.map g' (eB (π h))) = f h
      rw [heBπ]
      suffices hx : CartierDual.map g' (π₀ h) = θ' (f h) by rw [hx, BialgEquiv.symm_apply_apply]
      apply CartierDual.ext
      intro ψ
      rw [CartierDual.map_apply, hθ', hπ₀θ, ← BialgHom.comp_apply, hg', CartierDual.map_apply]
    refine ⟨g, hcomp, fun g₁ hg₁ => BialgHom.ext fun m => ?_⟩
    obtain ⟨h, rfl⟩ := hπ m
    exact (DFunLike.congr_fun hg₁ h).trans (DFunLike.congr_fun hcomp h).symm

  let eMdual : CartierDual R Mq ≃ₐ[R] E := (θE.trans (CartierDual.congr eB)).toAlgEquiv.symm
  refine ⟨Mq, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, π, hπ, hMet, hUniv,
    fun φ => hUniv Mq (π.comp φ), ?_⟩

  intro R' _ _ _ hloc
  obtain ⟨hEt', huniv'⟩ := hbc R' hloc
  haveI := hEt'

  obtain ⟨eM', -⟩ := CartierDual.exists_bialgEquiv_baseChange_forall_pairing_symm_tmul R R' Mq
  obtain ⟨eE', heE'⟩ := CartierDual.exists_bialgEquiv_baseChange_forall_pairing_symm_tmul R R' E
  obtain ⟨eH', heH'⟩ := CartierDual.exists_bialgEquiv_baseChange_forall_pairing_symm_tmul R R' H
  refine ⟨?_, ?_⟩
  ·
    exact Algebra.Etale.of_equiv
      ((eM'.toAlgEquiv.trans (Algebra.TensorProduct.congr AlgEquiv.refl eMdual)).symm)
  ·
    intro N _ _ _ _ _ _ f
    obtain ⟨θN, hθN⟩ := CartierDual.exists_bialgEquiv_bidual R' N

    obtain ⟨g', hg', -⟩ := huniv' (CartierDual R' N) (eH'.toBialgHom.comp (CartierDual.map f))

    have key : ∀ (r : R') (h : H) (ψ : CartierDual R' N),
        (CartierDual.map g' (eE'.symm (r ⊗ₜ[R] π₀ h))) ψ = ψ (f (r ⊗ₜ[R] h)) := by
      intro r h ψ
      rw [CartierDual.map_apply]

      let evh : CartierDual R H →ₗ[R] R := (CartierDual.pairing R H).flip h
      let Λl : R' ⊗[R] CartierDual R H →ₗ[R'] R' :=
        r • ((TensorProduct.AlgebraTensorModule.rid R R' R').toLinearMap ∘ₗ evh.baseChange R')
      have hΛ : ∀ (t : R') (φ : CartierDual R H), Λl (t ⊗ₜ[R] φ) = r * t * algebraMap R R' (φ h) := by
        intro t φ
        simp only [Λl, evh, LinearMap.smul_apply, LinearMap.comp_apply, LinearMap.baseChange_tmul,
          LinearEquiv.coe_coe, TensorProduct.AlgebraTensorModule.rid_tmul, LinearMap.flip_apply,
          CartierDual.pairing_apply, Algebra.smul_def, Algebra.algebraMap_self, RingHom.id_apply]
        ring

      have h1 : CartierDual.toDual R' (R' ⊗[R] E) (eE'.symm (r ⊗ₜ[R] π₀ h)) =
          Λl ∘ₗ (Bialgebra.TensorProduct.map (BialgHom.id R' R') ι).toLinearMap := by
        apply TensorProduct.AlgebraTensorModule.ext
        intro t a
        change CartierDual.pairing R' (R' ⊗[R] E) (eE'.symm (r ⊗ₜ[R] π₀ h)) (t ⊗ₜ[R] a) = Λl (t ⊗ₜ[R] ι a)
        rw [heE', CartierDual.pairing_apply, hπ₀θ, hΛ]
      have h1' : (eE'.symm (r ⊗ₜ[R] π₀ h)) (g' ψ) = Λl ((Bialgebra.TensorProduct.map (BialgHom.id R' R') ι) (g' ψ)) :=
        LinearMap.congr_fun h1 (g' ψ)
      have hg'ψ : (Bialgebra.TensorProduct.map (BialgHom.id R' R') ι) (g' ψ) = eH' (CartierDual.map f ψ) :=
        DFunLike.congr_fun hg' ψ
      rw [h1', hg'ψ]

      let Rl : R' ⊗[R] CartierDual R H →ₗ[R'] R' :=
        { toFun := fun y => (eH'.symm y) (r ⊗ₜ[R] h)
          map_add' := fun y y' => by rw [map_add]; rfl
          map_smul' := fun c y => by rw [map_smul]; rfl }
      have h2 : Λl = Rl := by
        apply TensorProduct.AlgebraTensorModule.ext
        intro t φ
        rw [hΛ]
        change r * t * algebraMap R R' (φ h) = CartierDual.pairing R' (R' ⊗[R] H) (eH'.symm (t ⊗ₜ[R] φ)) (r ⊗ₜ[R] h)
        rw [heH', CartierDual.pairing_apply, mul_comm t r]
      rw [h2]
      change (eH'.symm (eH' (CartierDual.map f ψ))) (r ⊗ₜ[R] h) = ψ (f (r ⊗ₜ[R] h))
      rw [BialgEquiv.symm_apply_apply, CartierDual.map_apply]
    have hg_tmul : ∀ (r : R') (h : H),
        (((θN.symm.toBialgHom.comp (CartierDual.map g')).comp eE'.symm.toBialgHom).comp
        (Bialgebra.TensorProduct.map (BialgHom.id R' R') eB.toBialgHom)) (r ⊗ₜ[R] π h) = f (r ⊗ₜ[R] h) := by
      intro r h
      have e2 : (Bialgebra.TensorProduct.map (BialgHom.id R' R') eB.toBialgHom) (r ⊗ₜ[R] π h) = r ⊗ₜ[R] π₀ h := by
        rw [Bialgebra.TensorProduct.map_tmul, BialgHom.id_apply]
        exact congrArg (fun z => r ⊗ₜ[R] z) (heBπ h)
      rw [BialgHom.comp_apply, BialgHom.comp_apply, BialgHom.comp_apply]
      refine (congrArg (fun z => θN.symm (CartierDual.map g' (eE'.symm z))) e2).trans ?_
      change θN.symm (CartierDual.map g' (eE'.symm (r ⊗ₜ[R] π₀ h))) = f (r ⊗ₜ[R] h)
      suffices hx : CartierDual.map g' (eE'.symm (r ⊗ₜ[R] π₀ h)) = θN (f (r ⊗ₜ[R] h)) by
        rw [hx, BialgEquiv.symm_apply_apply]
      apply CartierDual.ext
      intro ψ
      rw [hθN]
      exact key r h ψ
    have hcomp : (((θN.symm.toBialgHom.comp (CartierDual.map g')).comp eE'.symm.toBialgHom).comp
        (Bialgebra.TensorProduct.map (BialgHom.id R' R') eB.toBialgHom)).comp
        (Bialgebra.TensorProduct.map (BialgHom.id R' R') π) = f := by
      apply BialgHom.ext
      intro x
      induction x using TensorProduct.induction_on with
      | zero => simp only [map_zero]
      | add x y hx hy => simp only [map_add, hx, hy]
      | tmul r h =>
        rw [BialgHom.comp_apply, Bialgebra.TensorProduct.map_tmul]
        exact hg_tmul r h
    refine ⟨(((θN.symm.toBialgHom.comp (CartierDual.map g')).comp eE'.symm.toBialgHom).comp
        (Bialgebra.TensorProduct.map (BialgHom.id R' R') eB.toBialgHom)), hcomp, fun g₁ hg₁ => BialgHom.ext fun x => ?_⟩
    have hsurj : Function.Surjective (Bialgebra.TensorProduct.map (BialgHom.id R' R') π) := by
      intro z
      induction z using TensorProduct.induction_on with
      | zero => exact ⟨0, map_zero _⟩
      | tmul r m =>
        obtain ⟨h, rfl⟩ := hπ m
        exact ⟨r ⊗ₜ[R] h, Bialgebra.TensorProduct.map_tmul _ _ r h⟩
      | add x y hx hy =>
        obtain ⟨x', rfl⟩ := hx
        obtain ⟨y', rfl⟩ := hy
        exact ⟨x' + y', map_add _ x' y'⟩
    obtain ⟨y, rfl⟩ := hsurj x
    exact (DFunLike.congr_fun hg₁ y).trans (DFunLike.congr_fun hcomp y).symm

end S_HopfAlgebra_exists_bialgHom_surjective_etale_cartierDual_forall_existsUnique_comp_eq_of_bialgHom_injective_cartierDual
end P2MW
export P2MW.S_HopfAlgebra_exists_bialgHom_surjective_etale_cartierDual_forall_existsUnique_comp_eq_of_bialgHom_injective_cartierDual (solution)
