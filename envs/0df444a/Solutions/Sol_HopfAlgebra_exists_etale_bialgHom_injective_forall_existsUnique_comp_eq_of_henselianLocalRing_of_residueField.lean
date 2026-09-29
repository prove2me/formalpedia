-- Prove2me | solution 1 for HopfAlgebra.exists_etale_bialgHom_injective_forall_existsUnique_comp_eq_of_henselianLocalRing_of_residueField
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.85352+00:00
-- url     : https://prove2.me/submissions/01d30f2f-d715-5561-a2e7-b27400931670

import Mathlib
import Theorems.Thm_HopfAlgebra_exists_etale_nonempty_bialgEquiv_baseChange_residueField_of_henselianLocalRing
import Theorems.Thm_Algebra_Etale_existsUnique_bialgHom_baseChange_residueField_eq_of_moduleFinite_of_henselianLocalRing
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_HopfAlgebra_exists_etale_bialgHom_injective_forall_existsUnique_comp_eq_of_henselianLocalRing_of_residueField

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 80000
set_option Elab.async false

open scoped TensorProduct
p2m_open "IsLocalRing Coalgebra TensorProduct Coalgebra.TensorProduct"

universe u v w

namespace HopfAlgebra
p2m_export "HopfAlgebra" "sum_mul_antipode_eq_algebraMap_counit ofAlgHom sum_antipode_mul_eq_algebraMap_counit mul_antipode_rTensor_comul mul_antipode_lTensor_comul exists_etale_nonempty_bialgEquiv_baseChange_residueField_of_henselianLocalRing"
namespace EtQuotLift
p2m_open "HopfAlgebra"
section Transport
variable {R : Type*} [CommRing R] {A B : Type*} [CommRing A] [CommRing B] [Bialgebra R A] [Algebra R B]

noncomputable def tComul (e : A ≃ₐ[R] B) : B →ₐ[R] B ⊗[R] B :=
  (Algebra.TensorProduct.map (e : A →ₐ[R] B) (e : A →ₐ[R] B)).comp
    ((Bialgebra.comulAlgHom R A).comp (e.symm : B →ₐ[R] A))

noncomputable def tCounit (e : A ≃ₐ[R] B) : B →ₐ[R] R :=
  (Bialgebra.counitAlgHom R A).comp (e.symm : B →ₐ[R] A)

lemma tComul_apply (e : A ≃ₐ[R] B) (a : A) {ιr : Type*} (r : Repr R a ιr) :
    tComul e (e a) = ∑ i ∈ r.index, e (r.left i) ⊗ₜ[R] e (r.right i) := by
  simp [tComul, ← r.eq, map_sum]

@[scoped simp] lemma tCounit_apply (e : A ≃ₐ[R] B) (a : A) : tCounit e (e a) = counit (R := R) a := by
  simp [tCounit]

lemma t_coassoc (e : A ≃ₐ[R] B) :
    (Algebra.TensorProduct.assoc R R R B B B).toAlgHom.comp
      ((Algebra.TensorProduct.map (tComul e) (.id R B)).comp (tComul e))
      = (Algebra.TensorProduct.map (.id R B) (tComul e)).comp (tComul e) := by
  refine AlgHom.ext fun b => ?_
  obtain ⟨a, rfl⟩ := e.surjective b
  have key := sum_map_tmul_tmul_eq (R := R) (e : A →ₗ[R] B) (e : A →ₗ[R] B) (e : A →ₗ[R] B) a
    (repr := ℛ R a) (a₁ := fun i => ℛ R ((ℛ R a).left i)) (a₂ := fun i => ℛ R ((ℛ R a).right i))
  simp only [AlgHom.comp_apply] at *
  rw [tComul_apply e a (ℛ R a)]
  simp only [map_sum, Algebra.TensorProduct.map_tmul, AlgHom.coe_id, id_eq]
  simp_rw [tComul_apply e _ (ℛ R _)]
  simp only [TensorProduct.sum_tmul, TensorProduct.tmul_sum, map_sum]
  try simp only [map_sum, AlgHom.coe_coe, Algebra.TensorProduct.assoc_tmul]
  try simp only [AlgEquiv.toLinearMap_apply] at key
  exact key.symm

lemma t_rTensor (e : A ≃ₐ[R] B) :
    (Algebra.TensorProduct.map (tCounit e) (.id R B)).comp (tComul e)
      = (Algebra.TensorProduct.lid R B).symm := by
  refine AlgHom.ext fun b => ?_
  obtain ⟨a, rfl⟩ := e.surjective b
  simp only [AlgHom.comp_apply]
  rw [tComul_apply e a (ℛ R a)]
  simp [map_sum, sum_counit_tmul_map_eq]

lemma t_lTensor (e : A ≃ₐ[R] B) :
    (Algebra.TensorProduct.map (.id R B) (tCounit e)).comp (tComul e)
      = (Algebra.TensorProduct.rid R R B).symm := by
  refine AlgHom.ext fun b => ?_
  obtain ⟨a, rfl⟩ := e.surjective b
  simp only [AlgHom.comp_apply]
  rw [tComul_apply e a (ℛ R a)]
  simp [map_sum, sum_map_tmul_counit_eq]

@[reducible] noncomputable def transportBialgebra (e : A ≃ₐ[R] B) : Bialgebra R B :=
  Bialgebra.ofAlgHom (tComul e) (tCounit e) (t_coassoc e) (t_rTensor e) (t_lTensor e)

lemma t_comul_def (e : A ≃ₐ[R] B) :
    @CoalgebraStruct.comul R B _ _ _ (transportBialgebra e).toCoalgebra.toCoalgebraStruct
      = (tComul e).toLinearMap := rfl

lemma t_counit_def (e : A ≃ₐ[R] B) :
    @CoalgebraStruct.counit R B _ _ _ (transportBialgebra e).toCoalgebra.toCoalgebraStruct
      = (tCounit e).toLinearMap := rfl

noncomputable def transportEquiv (e : A ≃ₐ[R] B) :
    @BialgEquiv R _ A B _ _ _ _ _ (transportBialgebra e).toCoalgebra.toCoalgebraStruct :=
  letI := transportBialgebra e
  BialgEquiv.ofAlgEquiv e
    (by
      refine AlgHom.ext fun a => ?_
      show tCounit e (e a) = counit (R := R) a
      simp)
    (by
      refine AlgHom.ext fun a => ?_
      show Algebra.TensorProduct.map (e : A →ₐ[R] B) (e : A →ₐ[R] B) (comul (R := R) a) = tComul e (e a)
      simp [tComul])

lemma transportEquiv_apply (e : A ≃ₐ[R] B) (a : A) : transportEquiv e a = e a := rfl

lemma transport_isCocomm (e : A ≃ₐ[R] B) [Coalgebra.IsCocomm R A] :
    @Coalgebra.IsCocomm R B _ _ _ (transportBialgebra e).toCoalgebra := by
  letI := transportBialgebra e
  refine ⟨LinearMap.ext fun b => ?_⟩
  obtain ⟨a, rfl⟩ := e.surjective b
  show TensorProduct.comm R B B (tComul e (e a)) = tComul e (e a)
  have h : tComul e (e a) =
      Algebra.TensorProduct.map (e : A →ₐ[R] B) (e : A →ₐ[R] B) (comul (R := R) a) := by
    simp [tComul]
  rw [h]
  conv_lhs => rw [← Coalgebra.comm_comul R a]

  induction comul (R := R) a using TensorProduct.induction_on with
  | zero => simp
  | tmul x y => simp
  | add x y hx hy => simp only [map_add, hx, hy]

end Transport

section TransportHopf
variable {R : Type*} [CommRing R] {A B : Type*} [CommRing A] [CommRing B] [HopfAlgebra R A] [Algebra R B]

noncomputable def tAntipode (e : A ≃ₐ[R] B) : B →ₗ[R] B :=
  (e.toLinearEquiv : A →ₗ[R] B) ∘ₗ antipode R (A := A) ∘ₗ (e.symm.toLinearEquiv : B →ₗ[R] A)

@[scoped simp] lemma tAntipode_apply (e : A ≃ₐ[R] B) (a : A) : tAntipode e (e a) = e (antipode R a) := by
  simp [tAntipode]

@[reducible] noncomputable def transportHopf (e : A ≃ₐ[R] B) : HopfAlgebra R B where
  __ := transportBialgebra e
  antipode := tAntipode e
  mul_antipode_rTensor_comul := by
    refine LinearMap.ext fun b => ?_
    obtain ⟨a, rfl⟩ := e.surjective b
    show LinearMap.mul' R B (((tAntipode e).rTensor B) (tComul e (e a))) = algebraMap R B (tCounit e (e a))
    rw [tComul_apply e a (ℛ R a)]
    simp only [map_sum, LinearMap.rTensor_tmul, tAntipode_apply, LinearMap.mul'_apply, tCounit_apply,
      ← map_mul]
    rw [← map_sum, sum_antipode_mul_eq_algebraMap_counit, AlgEquiv.commutes]
  mul_antipode_lTensor_comul := by
    refine LinearMap.ext fun b => ?_
    obtain ⟨a, rfl⟩ := e.surjective b
    show LinearMap.mul' R B (((tAntipode e).lTensor B) (tComul e (e a))) = algebraMap R B (tCounit e (e a))
    rw [tComul_apply e a (ℛ R a)]
    simp only [map_sum, LinearMap.lTensor_tmul, tAntipode_apply, LinearMap.mul'_apply, tCounit_apply,
      ← map_mul]
    rw [← map_sum, sum_mul_antipode_eq_algebraMap_counit, AlgEquiv.commutes]

end TransportHopf

section TransportHom
variable {R : Type*} [CommRing R] {A B : Type*} [CommRing A] [CommRing B] [Bialgebra R A] [Algebra R B]

noncomputable def transportHom (e : A ≃ₐ[R] B) {C : Type*} [Semiring C] [Bialgebra R C] (g : A →ₐc[R] C) :
    @BialgHom R B C _ _ _ _ _ (transportBialgebra e).toCoalgebra.toCoalgebraStruct _ :=
  letI := transportBialgebra e
  g.comp ((transportEquiv e).symm : B →ₐc[R] A)

lemma transportHom_apply (e : A ≃ₐ[R] B) {C : Type*} [Semiring C] [Bialgebra R C] (g : A →ₐc[R] C)
    (a : A) : transportHom e g (e a) = g a := by
  letI := transportBialgebra e
  show g ((transportEquiv e).symm (transportEquiv e a)) = g a
  rw [BialgEquiv.symm_apply_apply]

end TransportHom

theorem injective_and_free_quotient_of_lTensor_residueField_injective
    {R : Type u} [CommRing R] [IsLocalRing R] {M : Type w} {N : Type v}
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    [Module.Finite R M] [Module.Finite R N] [Module.Free R N]
    (f : M →ₗ[R] N) (hf : Function.Injective (f.lTensor (ResidueField R))) :
    Function.Injective f ∧ Module.Free R (N ⧸ LinearMap.range f) := by
  refine ⟨?_, Module.free_of_lTensor_residueField_injective f (LinearMap.range f).mkQ
      (Submodule.mkQ_surjective _) f.exact_map_mkQ_range hf⟩
  obtain ⟨g, hg⟩ := (IsLocalRing.split_injective_iff_lTensor_residueField_injective f).mpr hf
  exact Function.LeftInverse.injective (g := g) fun x => congr($hg x)

section MapId
variable {R : Type*} [CommRing R] (S : Type*) [CommRing S] [Algebra R S]

theorem coe_map_id_eq_lTensor {A B : Type*} [CommRing A] [CommRing B] [Bialgebra R A] [Bialgebra R B]
    (f : A →ₐc[R] B) :
    ⇑(Bialgebra.TensorProduct.map (BialgHom.id S S) f) = ⇑((f : A →ₗ[R] B).lTensor S) := by
  funext x
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul s a => simp [Bialgebra.TensorProduct.map_tmul]
  | add x y hx hy => simp only [map_add, hx, hy]

theorem map_id_comp {A B C : Type*} [CommRing A] [CommRing B] [CommRing C]
    [Bialgebra R A] [Bialgebra R B] [Bialgebra R C] (φ : B →ₐc[R] C) (ψ : A →ₐc[R] B) :
    Bialgebra.TensorProduct.map (BialgHom.id S S) (φ.comp ψ)
      = (Bialgebra.TensorProduct.map (BialgHom.id S S) φ).comp
          (Bialgebra.TensorProduct.map (BialgHom.id S S) ψ) := by
  refine DFunLike.ext _ _ fun x => ?_
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul s a => simp [Bialgebra.TensorProduct.map_tmul]
  | add x y hx hy => simp only [map_add, hx, hy]

theorem map_id_injective {A B : Type*} [CommRing A] [CommRing B] [Bialgebra R A] [Bialgebra R B]
    (φ : A →ₐc[R] B) (hφ : Function.Injective φ) [Module.Flat R S] :
    Function.Injective (Bialgebra.TensorProduct.map (BialgHom.id S S) φ) := by
  rw [coe_map_id_eq_lTensor]
  exact Module.Flat.lTensor_preserves_injective_linearMap _ hφ

end MapId

section Theta
variable (R : Type*) [CommRing R] (S : Type*) [CommRing S] [Algebra R S]
  (T : Type*) [CommRing T] [Algebra R T] [Algebra S T] [IsScalarTower R S T]
  (X : Type*) [CommRing X] [Bialgebra R X]

set_option synthInstance.maxHeartbeats 1600000 in

lemma comul_one_tmul_one_tmul (x : X) {ιr : Type*} (r : Repr R x ιr) :
    comul (R := T) ((1 : T) ⊗ₜ[S] ((1 : S) ⊗ₜ[R] x))
      = ∑ i ∈ r.index, ((1 : T) ⊗ₜ[S] ((1 : S) ⊗ₜ[R] r.left i)) ⊗ₜ[T] ((1 : T) ⊗ₜ[S] ((1 : S) ⊗ₜ[R] r.right i)) := by
  rw [TensorProduct.comul_tmul, TensorProduct.comul_tmul, CommSemiring.comul_apply, CommSemiring.comul_apply, ← r.eq]
  simp only [tmul_sum, map_sum, AlgebraTensorModule.tensorTensorTensorComm_tmul]

lemma counit_one_tmul_one_tmul (x : X) :
    counit (R := T) ((1 : T) ⊗ₜ[S] ((1 : S) ⊗ₜ[R] x)) = algebraMap R T (counit (R := R) x) := by
  rw [TensorProduct.counit_tmul, TensorProduct.counit_tmul, CommSemiring.counit_apply, CommSemiring.counit_apply]
  simp [Algebra.algebraMap_eq_smul_one, smul_assoc]

variable (S₁ S₂ : Type*) [CommRing S₁] [CommRing S₂] [Algebra R S₁] [Algebra R S₂]
  [Algebra S₁ T] [Algebra S₂ T] [IsScalarTower R S₁ T] [IsScalarTower R S₂ T]

noncomputable def thetaAlg : T ⊗[S₁] (S₁ ⊗[R] X) ≃ₐ[T] T ⊗[S₂] (S₂ ⊗[R] X) :=
  (Algebra.TensorProduct.cancelBaseChange R S₁ T T X).trans
    (Algebra.TensorProduct.cancelBaseChange R S₂ T T X).symm

@[scoped simp] lemma thetaAlg_tmul (t : T) (s : S₁) (x : X) :
    thetaAlg R T X S₁ S₂ (t ⊗ₜ (s ⊗ₜ x)) = (s • t) ⊗ₜ ((1 : S₂) ⊗ₜ x) := by
  simp [thetaAlg]

noncomputable def theta : T ⊗[S₁] (S₁ ⊗[R] X) ≃ₐc[T] T ⊗[S₂] (S₂ ⊗[R] X) :=
  BialgEquiv.ofAlgEquiv (thetaAlg R T X S₁ S₂)
    (by
      refine Algebra.TensorProduct.ext (Subsingleton.elim _ _) ?_
      refine Algebra.TensorProduct.ext (Subsingleton.elim _ _) ?_
      refine AlgHom.ext fun x => ?_
      simp only [AlgHom.comp_apply, AlgHom.coe_restrictScalars', Algebra.TensorProduct.includeRight_apply,
        AlgEquiv.coe_algHom, thetaAlg_tmul, one_smul, Bialgebra.counitAlgHom_apply]
      rw [counit_one_tmul_one_tmul, counit_one_tmul_one_tmul])
    (by
      refine Algebra.TensorProduct.ext (Subsingleton.elim _ _) ?_
      refine Algebra.TensorProduct.ext (Subsingleton.elim _ _) ?_
      refine AlgHom.ext fun x => ?_
      simp only [AlgHom.comp_apply, AlgHom.coe_restrictScalars', Algebra.TensorProduct.includeRight_apply,
        AlgEquiv.coe_algHom, thetaAlg_tmul, one_smul, Bialgebra.comulAlgHom_apply]
      rw [comul_one_tmul_one_tmul R S₁ T X x (ℛ R x), comul_one_tmul_one_tmul R S₂ T X x (ℛ R x)]
      simp only [map_sum, Algebra.TensorProduct.map_tmul, AlgEquiv.coe_algHom, thetaAlg_tmul, one_smul])

@[scoped simp] lemma theta_tmul (t : T) (s : S₁) (x : X) :
    theta R T X S₁ S₂ (t ⊗ₜ (s ⊗ₜ x)) = (s • t) ⊗ₜ ((1 : S₂) ⊗ₜ x) :=
  thetaAlg_tmul R T X S₁ S₂ t s x

end Theta

end HopfAlgebra.EtQuotLift
p2m_reactivate "P2MW.S_HopfAlgebra_exists_etale_bialgHom_injective_forall_existsUnique_comp_eq_of_henselianLocalRing_of_residueField.HopfAlgebra P2MW.S_HopfAlgebra_exists_etale_bialgHom_injective_forall_existsUnique_comp_eq_of_henselianLocalRing_of_residueField.HopfAlgebra.EtQuotLift"
p2m_reactivate "P2MW.S_HopfAlgebra_exists_etale_bialgHom_injective_forall_existsUnique_comp_eq_of_henselianLocalRing_of_residueField.HopfAlgebra"

set_option maxHeartbeats 16000000 in
set_option synthInstance.maxHeartbeats 400000 in
open HopfAlgebra.EtQuotLift in
theorem solution
    (R : Type u) [CommRing R] [HenselianLocalRing R]
    (H : Type v) [CommRing H] [HopfAlgebra R H] [Coalgebra.IsCocomm R H]
    [Module.Finite R H] [Module.Flat R H]

    (E₀ : Type (max u v)) [CommRing E₀] [HopfAlgebra (IsLocalRing.ResidueField R) E₀]
    [Coalgebra.IsCocomm (IsLocalRing.ResidueField R) E₀] [Module.Finite (IsLocalRing.ResidueField R) E₀]
    (ι₀ : E₀ →ₐc[IsLocalRing.ResidueField R] IsLocalRing.ResidueField R ⊗[R] H)
    (hι₀ : Function.Injective ι₀)
    (hE₀ : Algebra.Etale (IsLocalRing.ResidueField R) E₀)
    (huniv₀ : ∀ (E' : Type (max u v)) [CommRing E'] [HopfAlgebra (IsLocalRing.ResidueField R) E']
        [Coalgebra.IsCocomm (IsLocalRing.ResidueField R) E'] [Module.Finite (IsLocalRing.ResidueField R) E']
        [Algebra.Etale (IsLocalRing.ResidueField R) E']
        (f : E' →ₐc[IsLocalRing.ResidueField R] IsLocalRing.ResidueField R ⊗[R] H),
        ∃! g : E' →ₐc[IsLocalRing.ResidueField R] E₀, ι₀.comp g = f)
    (hbc₀ : ∀ (K : Type u) [Field K] [Algebra (IsLocalRing.ResidueField R) K]
        (E' : Type (max u v)) [CommRing E'] [HopfAlgebra K E'] [Coalgebra.IsCocomm K E']
        [Module.Finite K E'] [Algebra.Etale K E']
        (f : E' →ₐc[K] K ⊗[IsLocalRing.ResidueField R] (IsLocalRing.ResidueField R ⊗[R] H)),
        ∃! g : E' →ₐc[K] K ⊗[IsLocalRing.ResidueField R] E₀,
          (Bialgebra.TensorProduct.map (BialgHom.id K K) ι₀).comp g = f) :
    ∃ (E : Type v) (_ : CommRing E) (_ : HopfAlgebra R E) (_ : Coalgebra.IsCocomm R E)
      (_ : Module.Free R E) (_ : Module.Finite R E) (ι : E →ₐc[R] H),
      Function.Injective ι ∧

      Algebra.Etale R E ∧

      (∀ (E' : Type v) [CommRing E'] [HopfAlgebra R E'] [Coalgebra.IsCocomm R E']
          [Module.Free R E'] [Module.Finite R E'] [Algebra.Etale R E']
          (f : E' →ₐc[R] H), ∃! g : E' →ₐc[R] E, ι.comp g = f) ∧

      (∀ φ : H →ₐc[R] H, ∃! ψ : E →ₐc[R] E, ι.comp ψ = φ.comp ι) ∧

      Module.Free R (H ⧸ LinearMap.range (ι : E →ₐ[R] H).toLinearMap) ∧

      (∀ (R' : Type u) [CommRing R'] [HenselianLocalRing R'] [Algebra R R'],
          IsLocalHom (algebraMap R R') →
          Algebra.Etale R' (R' ⊗[R] E) ∧
          ∀ (E' : Type v) [CommRing E'] [HopfAlgebra R' E'] [Coalgebra.IsCocomm R' E']
            [Module.Free R' E'] [Module.Finite R' E'] [Algebra.Etale R' E']
            (f : E' →ₐc[R'] R' ⊗[R] H),
              ∃! g : E' →ₐc[R'] R' ⊗[R] E,
                (Bialgebra.TensorProduct.map (BialgHom.id R' R') ι).comp g = f) := by

  haveI := hE₀
  obtain ⟨E₁, _, _, _, _, _, hEt₁, ⟨e⟩⟩ :=
    HopfAlgebra.exists_etale_nonempty_bialgEquiv_baseChange_residueField_of_henselianLocalRing R E₀
  haveI := hEt₁

  obtain ⟨ι₁, hι₁, -⟩ :=
    Algebra.Etale.existsUnique_bialgHom_baseChange_residueField_eq_of_moduleFinite_of_henselianLocalRing
      R E₁ H (ι₀.comp (e : ResidueField R ⊗[R] E₁ →ₐc[ResidueField R] E₀))

  have hfib : Function.Injective ((ι₁ : E₁ →ₗ[R] H).lTensor (ResidueField R)) := by
    rw [← coe_map_id_eq_lTensor (ResidueField R) ι₁, hι₁]
    exact hι₀.comp e.injective
  haveI : Module.Free R H := Module.free_of_flat_of_isLocalRing
  obtain ⟨hinj₁, hfree₁⟩ :=
    injective_and_free_quotient_of_lTensor_residueField_injective (ι₁ : E₁ →ₗ[R] H) hfib

  let S : Subalgebra R H := (ι₁ : E₁ →ₐ[R] H).range
  let eS : E₁ ≃ₐ[R] S := AlgEquiv.ofInjective (ι₁ : E₁ →ₐ[R] H) hinj₁
  letI hHS : HopfAlgebra R S := transportHopf eS
  haveI : Coalgebra.IsCocomm R S := transport_isCocomm eS
  haveI : Module.Free R S := Module.Free.of_equiv eS.toLinearEquiv
  haveI : Module.Finite R S := Module.Finite.equiv eS.toLinearEquiv
  have hEtS : Algebra.Etale R S := Algebra.Etale.of_equiv eS
  let eB : E₁ ≃ₐc[R] S := transportEquiv eS
  have heB : ∀ x, eB x = eS x := fun x => rfl

  let ι : S →ₐc[R] H := transportHom eS ι₁
  have hι_eB : ∀ x : E₁, ι (eB x) = ι₁ x := fun x => transportHom_apply eS ι₁ x
  have hιval : ∀ s : S, ι s = (s : H) := by
    intro s
    obtain ⟨x, rfl⟩ := eS.surjective s
    rw [← heB, hι_eB]
    exact (AlgEquiv.ofInjective_apply (ι₁ : E₁ →ₐ[R] H) hinj₁ x).symm
  have hιinj : Function.Injective ι := by
    intro s t h
    rw [hιval, hιval] at h
    exact Subtype.ext h
  have hι_comp_eB : ι.comp (eB : E₁ →ₐc[R] S) = ι₁ := BialgHom.coe_fn_injective (funext hι_eB)

  have huniv : ∀ (E' : Type v) [CommRing E'] [HopfAlgebra R E'] [Coalgebra.IsCocomm R E']
      [Module.Free R E'] [Module.Finite R E'] [Algebra.Etale R E']
      (f : E' →ₐc[R] H), ∃! g : E' →ₐc[R] S, ι.comp g = f := by
    intro E' _ _ _ _ _ _ f

    let fbar := Bialgebra.TensorProduct.map (BialgHom.id (ResidueField R) (ResidueField R)) f
    obtain ⟨gbar, hgbar, hgbaru⟩ := huniv₀ (ResidueField R ⊗[R] E') fbar

    obtain ⟨g₁, hg₁, hg₁u⟩ :=
      Algebra.Etale.existsUnique_bialgHom_baseChange_residueField_eq_of_moduleFinite_of_henselianLocalRing
        R E' E₁ ((e.symm : E₀ →ₐc[ResidueField R] ResidueField R ⊗[R] E₁).comp gbar)

    obtain ⟨f', -, hf'u⟩ :=
      Algebra.Etale.existsUnique_bialgHom_baseChange_residueField_eq_of_moduleFinite_of_henselianLocalRing
        R E' H fbar
    have hred : Bialgebra.TensorProduct.map (BialgHom.id (ResidueField R) (ResidueField R)) (ι₁.comp g₁)
        = fbar := by
      rw [map_id_comp, hι₁, hg₁]
      refine DFunLike.ext _ _ fun x => ?_
      simp only [BialgHom.coe_comp, Function.comp_apply, BialgEquiv.coe_toBialgHom,
        BialgEquiv.apply_symm_apply]
      exact congr($hgbar x)
    have hι₁g₁ : ι₁.comp g₁ = f := (hf'u _ hred).trans (hf'u _ rfl).symm
    refine ⟨(eB : E₁ →ₐc[R] S).comp g₁, ?_, ?_⟩
    · show ι.comp ((eB : E₁ →ₐc[R] S).comp g₁) = f
      rw [← BialgHom.comp_assoc, hι_comp_eB, hι₁g₁]
    · intro g' (hg' : ι.comp g' = f)

      let g₁' : E' →ₐc[R] E₁ := (eB.symm : S →ₐc[R] E₁).comp g'
      have h1 : ι₁.comp g₁' = f := by
        rw [← hι_comp_eB, BialgHom.comp_assoc, ← BialgHom.comp_assoc (eB : E₁ →ₐc[R] S),
          BialgEquiv.comp_symm, BialgHom.id_comp, hg']
      have h2 : ι₀.comp ((e : ResidueField R ⊗[R] E₁ →ₐc[ResidueField R] E₀).comp
          (Bialgebra.TensorProduct.map (BialgHom.id (ResidueField R) (ResidueField R)) g₁')) = fbar := by
        rw [← BialgHom.comp_assoc, ← hι₁, ← map_id_comp, h1]
      have h3 := hgbaru _ h2
      have h4 : Bialgebra.TensorProduct.map (BialgHom.id (ResidueField R) (ResidueField R)) g₁'
          = (e.symm : E₀ →ₐc[ResidueField R] ResidueField R ⊗[R] E₁).comp gbar := by
        rw [← h3, ← BialgHom.comp_assoc, BialgEquiv.symm_comp, BialgHom.id_comp]
      have h5 : g₁' = g₁ := hg₁u _ h4
      calc g' = (eB : E₁ →ₐc[R] S).comp g₁' := by
              rw [← BialgHom.comp_assoc, BialgEquiv.comp_symm, BialgHom.id_comp]
        _ = (eB : E₁ →ₐc[R] S).comp g₁ := by rw [h5]

  have hsplit : Module.Free R (H ⧸ LinearMap.range (ι : S →ₐ[R] H).toLinearMap) := by
    have hr : LinearMap.range (ι : S →ₐ[R] H).toLinearMap = LinearMap.range (ι₁ : E₁ →ₗ[R] H) := by
      apply le_antisymm
      · rintro _ ⟨s, rfl⟩
        obtain ⟨x, rfl⟩ := eB.surjective s
        exact ⟨x, (hι_eB x).symm⟩
      · rintro _ ⟨x, rfl⟩
        exact ⟨eB x, hι_eB x⟩
    rw [hr]
    exact hfree₁

  have hbc : ∀ (R' : Type u) [CommRing R'] [HenselianLocalRing R'] [Algebra R R'],
      IsLocalHom (algebraMap R R') →
      Algebra.Etale R' (R' ⊗[R] S) ∧
      ∀ (E' : Type v) [CommRing E'] [HopfAlgebra R' E'] [Coalgebra.IsCocomm R' E']
        [Module.Free R' E'] [Module.Finite R' E'] [Algebra.Etale R' E']
        (f : E' →ₐc[R'] R' ⊗[R] H),
          ∃! g : E' →ₐc[R'] R' ⊗[R] S,
            (Bialgebra.TensorProduct.map (BialgHom.id R' R') ι).comp g = f := by
    intro R' _ _ _ hloc
    haveI := hEtS
    haveI := hloc
    refine ⟨inferInstance, ?_⟩
    intro E' _ _ _ _ _ _ f

    have hιR'inj : Function.Injective (Bialgebra.TensorProduct.map (BialgHom.id R' R') ι) := by
      obtain ⟨rι, hrι⟩ : ∃ rι : H →ₗ[R] S, rι ∘ₗ (ι : S →ₐ[R] H).toLinearMap = LinearMap.id := by
        have hex := ((ι : S →ₐ[R] H).toLinearMap).exact_map_mkQ_range
        have hιinj' : Function.Injective (ι : S →ₐ[R] H).toLinearMap := hιinj
        haveI := hsplit
        have htf := (hex.split_tfae hιinj' (Submodule.mkQ_surjective _)).out 0 1
        exact htf.mp (Module.projective_lifting_property _ _ (Submodule.mkQ_surjective _))
      rw [coe_map_id_eq_lTensor]
      refine Function.HasLeftInverse.injective ⟨(rι.lTensor R'), fun x => ?_⟩
      rw [← LinearMap.comp_apply, ← LinearMap.lTensor_comp]
      have : ((ι : S →ₐc[R] H) : S →ₗ[R] H) = (ι : S →ₐ[R] H).toLinearMap := rfl
      rw [this, hrι, LinearMap.lTensor_id, LinearMap.id_apply]
    refine existsUnique_of_exists_of_unique ?_ ?_
    swap
    · intro g₁ g₂ h₁ h₂
      refine BialgHom.coe_fn_injective (funext fun x => hιR'inj ?_)
      exact (congr($h₁ x)).trans (congr($h₂ x)).symm

    let K := ResidueField R'
    let θH := theta R K H R' (ResidueField R)
    let θS := theta R K S R' (ResidueField R)
    let fK := Bialgebra.TensorProduct.map (BialgHom.id K K) f
    obtain ⟨gbar, hgbar, -⟩ := hbc₀ K (K ⊗[R'] E') ((θH : _ →ₐc[K] _).comp fK)
    let c1 : K ⊗[ResidueField R] E₀ →ₐc[K] K ⊗[ResidueField R] (ResidueField R ⊗[R] E₁) :=
      Bialgebra.TensorProduct.map (BialgHom.id K K) (e.symm : E₀ →ₐc[ResidueField R] ResidueField R ⊗[R] E₁)
    let c2 : K ⊗[ResidueField R] (ResidueField R ⊗[R] E₁) →ₐc[K] K ⊗[ResidueField R] (ResidueField R ⊗[R] S) :=
      Bialgebra.TensorProduct.map (BialgHom.id K K)
        (Bialgebra.TensorProduct.map (BialgHom.id (ResidueField R) (ResidueField R)) (eB : E₁ →ₐc[R] S))
    let gbar' : K ⊗[R'] E' →ₐc[K] K ⊗[R'] (R' ⊗[R] S) :=
      (θS.symm : _ →ₐc[K] _).comp (c2.comp (c1.comp gbar))
    obtain ⟨g, hg, -⟩ :=
      Algebra.Etale.existsUnique_bialgHom_baseChange_residueField_eq_of_moduleFinite_of_henselianLocalRing
        R' E' (R' ⊗[R] S) gbar'
    refine ⟨g, ?_⟩
    obtain ⟨f'', -, hu⟩ :=
      Algebra.Etale.existsUnique_bialgHom_baseChange_residueField_eq_of_moduleFinite_of_henselianLocalRing
        R' E' (R' ⊗[R] H) fK

    have θnat : (θH : _ →ₐc[K] _).comp (Bialgebra.TensorProduct.map (BialgHom.id K K)
          (Bialgebra.TensorProduct.map (BialgHom.id R' R') ι))
        = (Bialgebra.TensorProduct.map (BialgHom.id K K)
            (Bialgebra.TensorProduct.map (BialgHom.id (ResidueField R) (ResidueField R)) ι)).comp
          (θS : _ →ₐc[K] _) := by
      refine DFunLike.ext _ _ fun z => ?_
      induction z using TensorProduct.induction_on with
      | zero => simp
      | add z₁ z₂ h₁ h₂ => simp only [map_add, h₁, h₂]
      | tmul t y =>
        induction y using TensorProduct.induction_on with
        | zero => simp
        | add y₁ y₂ h₁ h₂ => simp only [tmul_add, map_add, h₁, h₂]
        | tmul s x =>
          simp only [BialgHom.coe_comp, Function.comp_apply, BialgEquiv.coe_toBialgHom,
            Bialgebra.TensorProduct.map_tmul, BialgHom.id_apply]
          simp only [θH, θS, theta_tmul, Bialgebra.TensorProduct.map_tmul, BialgHom.id_apply]

    have hkι : (Bialgebra.TensorProduct.map (BialgHom.id (ResidueField R) (ResidueField R)) ι).comp
          (Bialgebra.TensorProduct.map (BialgHom.id (ResidueField R) (ResidueField R)) (eB : E₁ →ₐc[R] S))
        = ι₀.comp (e : ResidueField R ⊗[R] E₁ →ₐc[ResidueField R] E₀) := by
      rw [← map_id_comp, hι_comp_eB, hι₁]

    have hcc : ∀ w : K ⊗[ResidueField R] E₀,
        (Bialgebra.TensorProduct.map (BialgHom.id K K)
          (Bialgebra.TensorProduct.map (BialgHom.id (ResidueField R) (ResidueField R)) ι)) (c2 (c1 w))
        = (Bialgebra.TensorProduct.map (BialgHom.id K K) ι₀) w := by
      intro w
      induction w using TensorProduct.induction_on with
      | zero => simp
      | add w₁ w₂ h₁ h₂ => simp only [map_add, h₁, h₂]
      | tmul κ x =>
        simp only [c1, c2, Bialgebra.TensorProduct.map_tmul, BialgHom.id_apply]
        congr 1
        have := congr($hkι (e.symm x))
        simpa only [BialgHom.coe_comp, Function.comp_apply, BialgEquiv.coe_toBialgHom,
          BialgEquiv.apply_symm_apply] using this
    have key : Bialgebra.TensorProduct.map (BialgHom.id K K)
        ((Bialgebra.TensorProduct.map (BialgHom.id R' R') ι).comp g) = fK := by
      rw [map_id_comp, hg]
      refine DFunLike.ext _ _ fun z => ?_
      have hinjθ : ∀ a b, θH a = θH b → a = b := fun a b h => θH.injective h
      apply hinjθ
      have h1 := congr($θnat (gbar' z))
      have h2 := congr($hgbar z)
      simp only [BialgHom.coe_comp, Function.comp_apply, BialgEquiv.coe_toBialgHom] at h1 h2 ⊢
      rw [h1]
      simp only [gbar', BialgHom.coe_comp, Function.comp_apply, BialgEquiv.coe_toBialgHom,
        BialgEquiv.apply_symm_apply]
      rw [hcc, h2]
    exact (hu _ key).trans (hu _ rfl).symm
  refine ⟨S, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, ι, hιinj, hEtS, huniv,
    fun φ => huniv S (φ.comp ι), hsplit, hbc⟩

end S_HopfAlgebra_exists_etale_bialgHom_injective_forall_existsUnique_comp_eq_of_henselianLocalRing_of_residueField
end P2MW
export P2MW.S_HopfAlgebra_exists_etale_bialgHom_injective_forall_existsUnique_comp_eq_of_henselianLocalRing_of_residueField (solution)
