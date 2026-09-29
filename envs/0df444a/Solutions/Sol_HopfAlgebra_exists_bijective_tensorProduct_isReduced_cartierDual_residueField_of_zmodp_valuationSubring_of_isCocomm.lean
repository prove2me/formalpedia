-- Prove2me | solution 1 for HopfAlgebra.exists_bijective_tensorProduct_isReduced_cartierDual_residueField_of_zmodp_valuationSubring_of_isCocomm
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.85352+00:00
-- url     : https://prove2.me/submissions/06db8e88-e5dc-59cd-8227-dc966e08cf40

import Mathlib
import Definitions.Def_HopfAlgebra_CartierDual
import Definitions.Def_HopfAlgebra_CartierDualMap
import Definitions.Def_HopfAlgebra_CartierDualInstances
import Theorems.Thm_CartierDual_exists_bialgEquiv_baseChange_forall_pairing_symm_tmul
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_HopfAlgebra_exists_bijective_tensorProduct_isReduced_cartierDual_residueField_of_zmodp_valuationSubring_of_isCocomm
p2m_attr_erase "instance" "CartierDual.instAlgebraBaseChangeDual CartierDual.instRingBaseChangeDual CartierDual.instModuleRestrictBaseChange CartierDual.instIsScalarTowerRestrictBaseChange instIsScalarTowerTensorProduct_definitions"
p2m_attr_erase "simp" "HopfAlgebra.mem_vanishingIdealOfPoints_iff HopfAlgebra.liftPoint_mk HopfAlgebra.mem_ptSet_iff CartierDual.dualBaseChangeLin_tmul CartierDual.dualBaseChange_tmul mem_flatClosure_iff"

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 80000
set_option Elab.async false

open scoped TensorProduct

noncomputable section

namespace HopfAlgebra
p2m_export "HopfAlgebra" "mk"
namespace OrdBC
p2m_open "HopfAlgebra"

section Cancel

variable (R S T : Type*) [CommRing R] [CommRing S] [CommRing T] [Algebra R S] [Algebra R T] [Algebra S T]
  [IsScalarTower R S T] (B : Type*) [CommRing B] [Bialgebra R B]

def cancelAlg : T ⊗[S] (S ⊗[R] B) ≃ₐ[T] T ⊗[R] B := Algebra.TensorProduct.cancelBaseChange R S T T B

theorem cancelAlg_tmul (t : T) (s : S) (b : B) : cancelAlg R S T B (t ⊗ₜ[S] (s ⊗ₜ[R] b)) = (s • t) ⊗ₜ[R] b :=
  Algebra.TensorProduct.cancelBaseChange_tmul R S T T B t s b

theorem cancelAlg_coe_tmul (t : T) (s : S) (b : B) :
    (cancelAlg R S T B : T ⊗[S] (S ⊗[R] B) →ₐ[T] T ⊗[R] B) (t ⊗ₜ[S] (s ⊗ₜ[R] b)) = (s • t) ⊗ₜ[R] b :=
  cancelAlg_tmul R S T B t s b

theorem tmul_tmul_eq_smul (t : T) (s : S) (b : B) :
    t ⊗ₜ[S] (s ⊗ₜ[R] b) = (s • t) • ((1 : T) ⊗ₜ[S] ((1 : S) ⊗ₜ[R] b)) := by
  rw [eq_comm, TensorProduct.smul_tmul', smul_eq_mul, mul_one, TensorProduct.smul_tmul, TensorProduct.smul_tmul',
    smul_eq_mul, mul_one]

theorem linearMap_ext_cancel {C : Type*} [AddCommMonoid C] [Module T C]
    {f g : T ⊗[S] (S ⊗[R] B) →ₗ[T] C}
    (h : ∀ b : B, f ((1 : T) ⊗ₜ[S] ((1 : S) ⊗ₜ[R] b)) = g ((1 : T) ⊗ₜ[S] ((1 : S) ⊗ₜ[R] b))) : f = g := by
  refine LinearMap.ext fun x => ?_
  induction x using TensorProduct.induction_on with
  | zero => rw [map_zero, map_zero]
  | tmul t y =>
    induction y using TensorProduct.induction_on with
    | zero => rw [TensorProduct.tmul_zero, map_zero, map_zero]
    | tmul s b => rw [tmul_tmul_eq_smul, map_smul, map_smul, h]
    | add x y hx hy => rw [TensorProduct.tmul_add, map_add, map_add, hx, hy]
  | add x y hx hy => rw [map_add, map_add, hx, hy]

theorem algHom_ext_cancel {C : Type*} [Semiring C] [Algebra T C]
    {f g : T ⊗[S] (S ⊗[R] B) →ₐ[T] C}
    (h : ∀ b : B, f ((1 : T) ⊗ₜ[S] ((1 : S) ⊗ₜ[R] b)) = g ((1 : T) ⊗ₜ[S] ((1 : S) ⊗ₜ[R] b))) : f = g :=
  AlgHom.toLinearMap_injective (linearMap_ext_cancel R S T B h)

def cancel : T ⊗[S] (S ⊗[R] B) ≃ₐc[T] T ⊗[R] B :=
  BialgEquiv.ofAlgEquiv (cancelAlg R S T B)
    (by
      refine algHom_ext_cancel R S T B fun b => ?_
      rw [AlgHom.comp_apply, Bialgebra.counitAlgHom_apply, Bialgebra.counitAlgHom_apply,
        cancelAlg_coe_tmul, one_smul, TensorProduct.counit_tmul, TensorProduct.counit_tmul, TensorProduct.counit_tmul,
        CommSemiring.counit_apply, CommSemiring.counit_apply, smul_assoc, one_smul])
    (by
      refine algHom_ext_cancel R S T B fun b => ?_
      rw [AlgHom.comp_apply, AlgHom.comp_apply, Bialgebra.comulAlgHom_apply, Bialgebra.comulAlgHom_apply,
        cancelAlg_coe_tmul, one_smul, TensorProduct.comul_tmul, CommSemiring.comul_apply,
        TensorProduct.comul_tmul, CommSemiring.comul_apply, TensorProduct.comul_tmul, CommSemiring.comul_apply]
      induction Coalgebra.comul (R := R) b using TensorProduct.induction_on with
      | zero =>
        rw [TensorProduct.tmul_zero, TensorProduct.tmul_zero, LinearEquiv.map_zero, LinearEquiv.map_zero,
          TensorProduct.tmul_zero, LinearEquiv.map_zero, map_zero]
      | tmul b₁ b₂ =>
        rw [TensorProduct.AlgebraTensorModule.tensorTensorTensorComm_tmul,
          TensorProduct.AlgebraTensorModule.tensorTensorTensorComm_tmul,
          TensorProduct.AlgebraTensorModule.tensorTensorTensorComm_tmul, Algebra.TensorProduct.map_tmul,
          cancelAlg_coe_tmul, cancelAlg_coe_tmul, one_smul]
      | add x y hx hy =>
        rw [TensorProduct.tmul_add, TensorProduct.tmul_add, LinearEquiv.map_add, LinearEquiv.map_add,
          TensorProduct.tmul_add, LinearEquiv.map_add, map_add, hx, hy])

theorem cancel_apply (x : T ⊗[S] (S ⊗[R] B)) : cancel R S T B x = cancelAlg R S T B x := rfl

theorem cancel_tmul (t : T) (s : S) (b : B) : cancel R S T B (t ⊗ₜ[S] (s ⊗ₜ[R] b)) = (s • t) ⊗ₜ[R] b :=
  cancelAlg_tmul R S T B t s b

end Cancel

section Distrib

variable (R k : Type*) [CommRing R] [CommRing k] [Algebra R k]
  (M E : Type*) [CommRing M] [CommRing E] [Bialgebra R M] [Bialgebra R E]

def distribLin : (k ⊗[R] M) ⊗[k] (k ⊗[R] E) ≃ₗ[k] k ⊗[R] (M ⊗[R] E) :=
  (TensorProduct.AlgebraTensorModule.tensorTensorTensorComm R R k k k M k E).trans
    (TensorProduct.AlgebraTensorModule.congr (TensorProduct.lid k k) (LinearEquiv.refl R (M ⊗[R] E)))

theorem distribLin_tmul (a c : k) (m : M) (e : E) :
    distribLin R k M E ((a ⊗ₜ[R] m) ⊗ₜ[k] (c ⊗ₜ[R] e)) = (a * c) ⊗ₜ[R] (m ⊗ₜ[R] e) := by
  simp [distribLin]

def inclM : M →ₐc[R] M ⊗[R] E :=
  (Bialgebra.TensorProduct.map (BialgHom.id R M) (Bialgebra.unitBialgHom R E)).comp
    (Bialgebra.TensorProduct.rid R R M).symm.toBialgHom

def inclE : E →ₐc[R] M ⊗[R] E :=
  (Bialgebra.TensorProduct.map (Bialgebra.unitBialgHom R M) (BialgHom.id R E)).comp
    (Bialgebra.TensorProduct.lid R E).symm.toBialgHom

theorem inclM_apply (m : M) : inclM R M E m = m ⊗ₜ[R] (1 : E) := by
  change Bialgebra.TensorProduct.map (BialgHom.id R M) (Bialgebra.unitBialgHom R E)
    ((Bialgebra.TensorProduct.rid R R M).symm m) = _
  rw [Bialgebra.TensorProduct.rid_symm_apply, Bialgebra.TensorProduct.map_tmul, map_one]
  rfl

theorem inclE_apply (e : E) : inclE R M E e = (1 : M) ⊗ₜ[R] e := by
  change Bialgebra.TensorProduct.map (Bialgebra.unitBialgHom R M) (BialgHom.id R E)
    ((Bialgebra.TensorProduct.lid R E).symm e) = _
  rw [Bialgebra.TensorProduct.lid_symm_apply, Bialgebra.TensorProduct.map_tmul, map_one]
  rfl

def distribHom : (k ⊗[R] M) ⊗[k] (k ⊗[R] E) →ₐc[k] k ⊗[R] (M ⊗[R] E) :=
  (Bialgebra.mulBialgHom k (k ⊗[R] (M ⊗[R] E))).comp
    (Bialgebra.TensorProduct.map
      (Bialgebra.TensorProduct.map (BialgHom.id k k) (inclM R M E))
      (Bialgebra.TensorProduct.map (BialgHom.id k k) (inclE R M E)))

theorem distribHom_tmul (a c : k) (m : M) (e : E) :
    distribHom R k M E ((a ⊗ₜ[R] m) ⊗ₜ[k] (c ⊗ₜ[R] e)) = (a * c) ⊗ₜ[R] (m ⊗ₜ[R] e) := by
  change Bialgebra.mulBialgHom k (k ⊗[R] (M ⊗[R] E))
    (Bialgebra.TensorProduct.map
      (Bialgebra.TensorProduct.map (BialgHom.id k k) (inclM R M E))
      (Bialgebra.TensorProduct.map (BialgHom.id k k) (inclE R M E)) ((a ⊗ₜ[R] m) ⊗ₜ[k] (c ⊗ₜ[R] e))) = _
  rw [Bialgebra.TensorProduct.map_tmul, Bialgebra.TensorProduct.map_tmul, Bialgebra.TensorProduct.map_tmul,
    inclM_apply, inclE_apply, Bialgebra.coe_mulBialgHom, LinearMap.mul'_apply]
  change (a ⊗ₜ[R] (m ⊗ₜ[R] (1 : E))) * (c ⊗ₜ[R] ((1 : M) ⊗ₜ[R] e)) = _
  rw [Algebra.TensorProduct.tmul_mul_tmul, Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]

set_option synthInstance.maxHeartbeats 1600000 in
set_option maxHeartbeats 3200000 in
theorem distribHom_eq_distribLin (x : (k ⊗[R] M) ⊗[k] (k ⊗[R] E)) :
    distribHom R k M E x = distribLin R k M E x := by
  induction x using TensorProduct.induction_on with
  | zero => rw [map_zero, LinearEquiv.map_zero]
  | add x y hx hy => rw [map_add, LinearEquiv.map_add, hx, hy]
  | tmul x y =>
    induction x using TensorProduct.induction_on with
    | zero => rw [TensorProduct.zero_tmul, map_zero, LinearEquiv.map_zero]
    | add x₁ x₂ h₁ h₂ => rw [TensorProduct.add_tmul, map_add, LinearEquiv.map_add, h₁, h₂]
    | tmul a m =>
      induction y using TensorProduct.induction_on with
      | zero => rw [TensorProduct.tmul_zero, map_zero, LinearEquiv.map_zero]
      | add y₁ y₂ h₁ h₂ => rw [TensorProduct.tmul_add, map_add, LinearEquiv.map_add, h₁, h₂]
      | tmul c e => rw [distribHom_tmul, distribLin_tmul]

theorem distribHom_bijective : Function.Bijective (distribHom R k M E) := by
  have h : ⇑(distribHom R k M E) = ⇑(distribLin R k M E) := funext (distribHom_eq_distribLin R k M E)
  rw [h]
  exact (distribLin R k M E).bijective

set_option maxHeartbeats 3200000 in

def distrib : (k ⊗[R] M) ⊗[k] (k ⊗[R] E) ≃ₐc[k] k ⊗[R] (M ⊗[R] E) :=
  BialgEquiv.ofBijective (R := k) (A := (k ⊗[R] M) ⊗[k] (k ⊗[R] E)) (B := k ⊗[R] (M ⊗[R] E))
    (distribHom R k M E) (distribHom_bijective R k M E)

theorem distrib_tmul (a c : k) (m : M) (e : E) :
    distrib R k M E ((a ⊗ₜ[R] m) ⊗ₜ[k] (c ⊗ₜ[R] e)) = (a * c) ⊗ₜ[R] (m ⊗ₜ[R] e) :=
  distribHom_tmul R k M E a c m e

end Distrib

section Reduced

attribute [local instance] IsArtinianRing.fieldOfSubtypeIsMaximal in

theorem etale_of_isReduced_of_perfectField (K A : Type*) [Field K] [PerfectField K] [CommRing A] [Algebra K A]
    [Module.Finite K A] [IsReduced A] : Algebra.Etale K A := by
  haveI : IsArtinianRing A := isArtinian_of_tower K (inferInstance : IsArtinian K A)
  rw [Algebra.Etale.iff_exists_algEquiv_prod]
  refine ⟨MaximalSpectrum A, inferInstance, fun I => A ⧸ I.asIdeal, inferInstance, inferInstance,
    (IsArtinianRing.equivPi A).restrictScalars K, fun I => ⟨inferInstance, ?_⟩⟩
  haveI : Module.Finite K (A ⧸ I.asIdeal) := inferInstance
  haveI : Algebra.IsAlgebraic K (A ⧸ I.asIdeal) := Algebra.IsAlgebraic.of_finite K _
  infer_instance

theorem isReduced_baseChange_of_isReduced_zmodp (p : ℕ) [Fact p.Prime]
    (k : Type*) [Field k] [Algebra (ZMod p) k]
    (E : Type*) [CommRing E] [Algebra (ZMod p) E] [Module.Finite (ZMod p) E] [IsReduced E] :
    IsReduced (k ⊗[ZMod p] E) := by
  haveI : Algebra.Etale (ZMod p) E := etale_of_isReduced_of_perfectField (ZMod p) E
  haveI : Algebra.Etale k (k ⊗[ZMod p] E) := Algebra.Etale.baseChange (ZMod p) E k
  haveI : Algebra.EssFiniteType k (k ⊗[ZMod p] E) := inferInstance
  exact Algebra.FormallyUnramified.isReduced_of_field k (k ⊗[ZMod p] E)

theorem isReduced_cartierDual_baseChange_zmodp (p : ℕ) [Fact p.Prime]
    (k : Type*) [Field k] [Algebra (ZMod p) k]
    (M : Type*) [CommRing M] [Bialgebra (ZMod p) M] [Coalgebra.IsCocomm (ZMod p) M]
    [Module.Finite (ZMod p) M] [Module.Free (ZMod p) M]
    (hM : IsReduced (CartierDual (ZMod p) M)) :
    IsReduced (CartierDual k (k ⊗[ZMod p] M)) := by
  haveI := hM
  have h1 : IsReduced (k ⊗[ZMod p] CartierDual (ZMod p) M) :=
    isReduced_baseChange_of_isReduced_zmodp p k (CartierDual (ZMod p) M)
  obtain ⟨e, -⟩ := CartierDual.exists_bialgEquiv_baseChange_forall_pairing_symm_tmul (ZMod p) k M
  exact @isReduced_of_injective _ _ _ _ _ _ _ e e.injective h1

end Reduced

section Factor

theorem finite_right_of_finite_tensorProduct (K : Type*) [Field K]
    (M E : Type*) [AddCommGroup M] [Module K M] [AddCommGroup E] [Module K E]
    [Nontrivial M] [Module.Finite K (M ⊗[K] E)] : Module.Finite K E := by
  obtain ⟨x, hx⟩ := exists_ne (0 : M)
  let ι : E →ₗ[K] M ⊗[K] E := TensorProduct.mk K M E x
  have hι : Function.Injective ι := by
    obtain ⟨f, hf⟩ := Module.Projective.exists_dual_eq_one K hx
    refine Function.LeftInverse.injective (g := fun z => TensorProduct.lid K E (LinearMap.rTensor E f z)) ?_
    intro e
    show TensorProduct.lid K E (LinearMap.rTensor E f (x ⊗ₜ[K] e)) = e
    rw [LinearMap.rTensor_tmul, TensorProduct.lid_tmul, hf, one_smul]
  exact Module.Finite.of_injective ι hι

theorem isCocomm_of_surjective {R C D : Type*} [CommSemiring R] [AddCommMonoid C] [Module R C] [Coalgebra R C]
    [AddCommMonoid D] [Module R D] [Coalgebra R D] [Coalgebra.IsCocomm R C]
    (f : C →ₗc[R] D) (hf : Function.Surjective f) : Coalgebra.IsCocomm R D := by
  refine ⟨LinearMap.ext fun d => ?_⟩
  obtain ⟨c, rfl⟩ := hf d
  rw [LinearMap.comp_apply, ← CoalgHomClass.map_comp_comul_apply f c]
  have hc := LinearMap.congr_fun (Coalgebra.IsCocomm.comm_comp_comul (R := R) (A := C)) c
  rw [LinearMap.comp_apply] at hc
  conv_rhs => rw [← hc]
  induction Coalgebra.comul (R := R) c using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | tmul x y => rfl
  | add x y hx hy => simp only [map_add, hx, hy]

def projLeft (K : Type*) [CommRing K] (M E : Type*) [CommRing M] [CommRing E] [Bialgebra K M] [Bialgebra K E] :
    M ⊗[K] E →ₐc[K] M :=
  let π₁ : M ⊗[K] E →ₐc[K] M ⊗[K] K := Bialgebra.TensorProduct.map (BialgHom.id K M) (Bialgebra.counitBialgHom K E)
  let π₂ : M ⊗[K] K →ₐc[K] M := (Bialgebra.TensorProduct.rid K K M : M ⊗[K] K ≃ₐc[K] M)
  π₂.comp π₁

theorem projLeft_tmul (K : Type*) [CommRing K] (M E : Type*) [CommRing M] [CommRing E] [Bialgebra K M] [Bialgebra K E]
    (m : M) (e : E) : projLeft K M E (m ⊗ₜ[K] e) = Coalgebra.counit (R := K) e • m := by
  show Bialgebra.TensorProduct.rid K K M (Bialgebra.TensorProduct.map (BialgHom.id K M) (Bialgebra.counitBialgHom K E)
    (m ⊗ₜ[K] e)) = _
  rw [Bialgebra.TensorProduct.map_tmul]
  exact Algebra.TensorProduct.rid_tmul K (Bialgebra.counitBialgHom K E e) m

theorem isCocomm_left_of_surjective (K : Type*) [Field K]
    (B M E : Type*) [CommRing B] [CommRing M] [CommRing E] [Bialgebra K B] [Bialgebra K M] [Bialgebra K E]
    [Coalgebra.IsCocomm K B] (Θ : B →ₐc[K] M ⊗[K] E) (hΘ : Function.Surjective Θ) :
    Coalgebra.IsCocomm K M := by
  refine isCocomm_of_surjective (((projLeft K M E).comp Θ : B →ₐc[K] M) : B →ₗc[K] M) ?_
  intro m
  obtain ⟨b, hb⟩ := hΘ (m ⊗ₜ[K] (1 : E))
  refine ⟨b, ?_⟩
  show projLeft K M E (Θ b) = m
  rw [hb, projLeft_tmul, Bialgebra.counit_one, one_smul]

end Factor

section Assembly

theorem nontrivial_of_bialgebra (K : Type*) [Field K] (B : Type*) [CommRing B] [Bialgebra K B] : Nontrivial B :=
  ⟨⟨0, 1, fun h => zero_ne_one (α := K) (by
    have := congrArg (Coalgebra.counit (R := K) (A := B)) h
    rwa [map_zero, Bialgebra.counit_one] at this)⟩⟩

theorem bijective_map_id {R k : Type*} [CommRing R] [CommRing k] [Algebra R k]
    {X Y : Type*} [CommRing X] [CommRing Y] [Bialgebra R X] [Bialgebra R Y]
    (Θ : X →ₐc[R] Y) (hΘ : Function.Bijective Θ) :
    Function.Bijective (Bialgebra.TensorProduct.map (BialgHom.id k k) Θ) := by
  let eΘ : k ⊗[R] X ≃ₗ[k] k ⊗[R] Y :=
    LinearEquiv.baseChange R k X Y (LinearEquiv.ofBijective (Θ : X →ₗ[R] Y) hΘ)
  have h : ∀ x, Bialgebra.TensorProduct.map (BialgHom.id k k) Θ x = eΘ x := by
    intro x
    induction x using TensorProduct.induction_on with
    | zero => rw [map_zero, map_zero]
    | tmul a x =>
      rw [Bialgebra.TensorProduct.map_tmul]
      show a ⊗ₜ[R] Θ x = LinearEquiv.baseChange R k X Y (LinearEquiv.ofBijective (Θ : X →ₗ[R] Y) hΘ) (a ⊗ₜ[R] x)
      rw [LinearEquiv.baseChange_tmul]
      rfl
    | add x y hx hy => rw [map_add, map_add, hx, hy]
  have hfun : (⇑(Bialgebra.TensorProduct.map (BialgHom.id k k) Θ) : k ⊗[R] X → k ⊗[R] Y) = ⇑eΘ := funext h
  rw [hfun]
  exact eΘ.bijective

end Assembly

end HopfAlgebra.OrdBC

open HopfAlgebra.OrdBC in

theorem solution
    (p : ℕ) [Fact p.Prime]
    {O : Type} [CommRing O] [Algebra O (AlgebraicClosure ℚ)] [Algebra O (ZMod p)]
    (P : ValuationSubring (AlgebraicClosure ℚ))
    (hOP : ∀ x : O, algebraMap O (AlgebraicClosure ℚ) x ∈ P)
    (hres : ∀ x : O, algebraMap O (ZMod p) x = 0 ↔
      P.valuation (algebraMap O (AlgebraicClosure ℚ) x) < 1)
    (A : Type) [CommRing A] [HopfAlgebra O A] [Coalgebra.IsCocomm O A] [Module.Finite O A] [Module.Free O A]
    (hord : ∃ (M : Type) (_ : CommRing M) (_ : HopfAlgebra (ZMod p) M) (_ : Module.Finite (ZMod p) M)
        (_ : Module.Free (ZMod p) M) (E : Type) (_ : CommRing E) (_ : HopfAlgebra (ZMod p) E)
        (Θ : ZMod p ⊗[O] A →ₐc[ZMod p] M ⊗[ZMod p] E),
        Function.Bijective Θ ∧ IsReduced E ∧ IsReduced (CartierDual (ZMod p) M)) :
    letI : Algebra O P := ((algebraMap O (AlgebraicClosure ℚ)).codRestrict P.toSubring hOP).toAlgebra
    ∃ (M₀ : Type) (_ : CommRing M₀) (_ : HopfAlgebra (IsLocalRing.ResidueField P) M₀)
        (_ : Module.Finite (IsLocalRing.ResidueField P) M₀) (_ : Module.Free (IsLocalRing.ResidueField P) M₀)
        (E₀ : Type) (_ : CommRing E₀) (_ : HopfAlgebra (IsLocalRing.ResidueField P) E₀)
        (Θ : IsLocalRing.ResidueField P ⊗[P] (P ⊗[O] A) →ₐc[IsLocalRing.ResidueField P]
          M₀ ⊗[IsLocalRing.ResidueField P] E₀),
        Function.Bijective Θ ∧ IsReduced E₀ ∧ IsReduced (CartierDual (IsLocalRing.ResidueField P) M₀) := by
  classical
  letI instOP : Algebra O P := ((algebraMap O (AlgebraicClosure ℚ)).codRestrict P.toSubring hOP).toAlgebra

  letI instOk : Algebra O (IsLocalRing.ResidueField P) :=
    ((algebraMap P (IsLocalRing.ResidueField P)).comp (algebraMap O P)).toAlgebra
  letI : Module O (IsLocalRing.ResidueField P) := Algebra.toModule
  haveI : IsScalarTower O P (IsLocalRing.ResidueField P) := IsScalarTower.of_algebraMap_eq fun _ => rfl

  have hpm : ((p : ℕ) : P) ∈ IsLocalRing.maximalIdeal P := by
    rw [ValuationSubring.valuation_lt_one_iff]
    have h := (hres (p : O)).mp (by rw [map_natCast, ZMod.natCast_self])
    rwa [map_natCast] at h
  have hp0 : ((p : ℕ) : IsLocalRing.ResidueField P) = 0 := by
    rw [← map_natCast (algebraMap P (IsLocalRing.ResidueField P)), IsLocalRing.ResidueField.algebraMap_eq,
      IsLocalRing.residue_eq_zero_iff]
    exact hpm
  haveI : CharP (IsLocalRing.ResidueField P) p := (CharP.charP_iff_prime_eq_zero Fact.out).mpr hp0
  letI instZk : Algebra (ZMod p) (IsLocalRing.ResidueField P) := ZMod.algebra _ p

  haveI : IsScalarTower O (ZMod p) (IsLocalRing.ResidueField P) := by
    refine IsScalarTower.of_algebraMap_eq fun x => ?_

    set c := algebraMap O (ZMod p) x with hc
    have hcn : ((c.val : ℕ) : ZMod p) = c := ZMod.natCast_zmod_val c
    have hx : algebraMap O (ZMod p) (x - (c.val : O)) = 0 := by rw [map_sub, map_natCast, hcn, hc, sub_self]
    have hxm : (algebraMap O P (x - (c.val : O))) ∈ IsLocalRing.maximalIdeal P := by
      rw [ValuationSubring.valuation_lt_one_iff]
      exact (hres _).mp hx
    have h1 : algebraMap O (IsLocalRing.ResidueField P) x = ((c.val : ℕ) : IsLocalRing.ResidueField P) := by
      have : algebraMap P (IsLocalRing.ResidueField P) (algebraMap O P (x - (c.val : O))) = 0 := by
        rw [IsLocalRing.ResidueField.algebraMap_eq, IsLocalRing.residue_eq_zero_iff]; exact hxm
      rw [map_sub, map_sub, map_natCast, map_natCast, sub_eq_zero] at this
      exact this
    rw [h1]
    exact (map_natCast (algebraMap (ZMod p) (IsLocalRing.ResidueField P)) c.val).symm.trans (congrArg _ hcn)

  obtain ⟨M, _iM1, _iM2, _iM3, _iM4, E, _iE1, _iE2, Θ, hΘ, hEred, hMred⟩ := hord
  haveI : Coalgebra.IsCocomm (ZMod p) M := isCocomm_left_of_surjective (ZMod p) (ZMod p ⊗[O] A) M E Θ hΘ.2
  haveI : Nontrivial M := nontrivial_of_bialgebra (ZMod p) M
  haveI : Module.Finite (ZMod p) (M ⊗[ZMod p] E) :=
    Module.Finite.of_surjective ((Θ : ZMod p ⊗[O] A →ₐ[ZMod p] M ⊗[ZMod p] E).toLinearMap) hΘ.2
  haveI : Module.Finite (ZMod p) E := finite_right_of_finite_tensorProduct (ZMod p) M E
  haveI : IsReduced E := hEred

  let k := IsLocalRing.ResidueField P
  let Θ₁ : k ⊗[P] (P ⊗[O] A) →ₐc[k] k ⊗[O] A := cancel O P k A
  let Θ₂ : k ⊗[O] A →ₐc[k] k ⊗[ZMod p] (ZMod p ⊗[O] A) := (cancel O (ZMod p) k A).symm
  let Θ₃ : k ⊗[ZMod p] (ZMod p ⊗[O] A) →ₐc[k] k ⊗[ZMod p] (M ⊗[ZMod p] E) :=
    Bialgebra.TensorProduct.map (BialgHom.id k k) Θ
  let Θ₄ : k ⊗[ZMod p] (M ⊗[ZMod p] E) →ₐc[k] (k ⊗[ZMod p] M) ⊗[k] (k ⊗[ZMod p] E) := (distrib (ZMod p) k M E).symm
  let Θ₀ : k ⊗[P] (P ⊗[O] A) →ₐc[k] (k ⊗[ZMod p] M) ⊗[k] (k ⊗[ZMod p] E) := Θ₄.comp (Θ₃.comp (Θ₂.comp Θ₁))
  have hbij : Function.Bijective Θ₀ :=
    (distrib (ZMod p) k M E).symm.bijective.comp ((bijective_map_id Θ hΘ).comp
      ((cancel O (ZMod p) k A).symm.bijective.comp (cancel O P k A).bijective))
  exact ⟨k ⊗[ZMod p] M, inferInstance, inferInstance, inferInstance, inferInstance,
    k ⊗[ZMod p] E, inferInstance, inferInstance, Θ₀, hbij,
    isReduced_baseChange_of_isReduced_zmodp p k E, isReduced_cartierDual_baseChange_zmodp p k M hMred⟩

end
end S_HopfAlgebra_exists_bijective_tensorProduct_isReduced_cartierDual_residueField_of_zmodp_valuationSubring_of_isCocomm
end P2MW
export P2MW.S_HopfAlgebra_exists_bijective_tensorProduct_isReduced_cartierDual_residueField_of_zmodp_valuationSubring_of_isCocomm (solution)
