-- Prove2me | solution 1 for HopfAlgebra.exists_eq_comp_of_forall_sub_counit_mem_maximalIdeal_of_bijective_tensorProduct_isReduced_valuationSubring
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.85352+00:00
-- url     : https://prove2.me/submissions/6d486fe1-16b9-504e-a532-c85d8d7e7421

import Mathlib
import Definitions.Def_HopfAlgebra_CartierDual
import Definitions.Def_HopfAlgebra_CartierDualMap
import Definitions.Def_HopfAlgebra_CartierDualInstances
import Theorems.Thm_AlgHom_exists_residue_comp_eq_of_moduleFinite_of_flat_of_isAlgClosed_fractionRing
import Theorems.Thm_Algebra_natCard_algHom_eq_finrank_residueField_tensorProduct_of_flat_of_isReduced
import Theorems.Thm_HopfAlgebra_isReduced_of_finiteType_of_charZero
import Theorems.Thm_AlgHom_natCard_eq_finrank_of_isReduced_of_isAlgClosed
import Theorems.Thm_HopfAlgebra_isUnit_withConv_algHom
import Theorems.Thm_HopfAlgebra_natCard_algHom_dvd_natCard_algHom_of_surjective
import Theorems.Thm_ValuationSubring_isAlgClosed_residueField
import Theorems.Thm_HopfAlgebra_isLocalRing_of_isReduced_cartierDual_of_finrank_eq_prime_pow
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_HopfAlgebra_exists_eq_comp_of_forall_sub_counit_mem_maximalIdeal_of_bijective_tensorProduct_isReduced_valuationSubring

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 80000
set_option Elab.async false

open scoped TensorProduct

universe u v w

namespace MonoidHom
p2m_export "MonoidHom" "codRestrict comp id_apply comp_apply mem_ker ext mk ker id"
p2m_open "MonoidHom"

theorem natCard_eq_natCard_fiber_one_mul_of_surjective_of_forall_isUnit
    {X Y : Type*} [CommMonoid X] [Monoid Y] [Finite X] (φ : X → Y)
    (hmul : ∀ a b : X, φ (a * b) = φ a * φ b) (hone : φ 1 = 1) (hφ : Function.Surjective φ)
    (hu : ∀ x : X, ∃ y : X, y * x = 1) :
    Nat.card X = Nat.card {x : X // φ x = 1} * Nat.card Y := by
  classical
  haveI : Finite Y := Finite.of_surjective φ hφ

  choose s hs using hφ
  choose inv hinv using hu

  have e : ∀ y : Y, {x : X // φ x = y} ≃ {x : X // φ x = 1} := fun y =>
    { toFun := fun x => ⟨inv (s y) * x.1, by
        have h1 : φ (inv (s y)) * φ (s y) = 1 := by rw [← hmul, hinv, hone]
        rw [hs] at h1
        rw [hmul, x.2, h1]⟩
      invFun := fun x => ⟨s y * x.1, by rw [hmul, x.2, mul_one, hs]⟩
      left_inv := fun x => by
        ext
        simp only
        rw [← mul_assoc, mul_comm (s y), hinv, one_mul]
      right_inv := fun x => by
        ext
        simp only
        rw [← mul_assoc, hinv, one_mul] }
  haveI := Fintype.ofFinite X
  haveI := Fintype.ofFinite Y
  rw [Nat.card_congr (Equiv.sigmaFiberEquiv φ).symm, Nat.card_sigma,
    Finset.sum_congr rfl (fun y _ => Nat.card_congr (e y)), Finset.sum_const, Finset.card_univ, smul_eq_mul,
    mul_comm, ← Nat.card_eq_fintype_card]

end MonoidHom

namespace Bialgebra
p2m_export "Bialgebra" "TensorProduct.rid_tmul counitBialgHom_apply counitAlgHom TensorProduct.lid_tmul TensorProduct.rid TensorProduct.map counit_one TensorProduct.lid mk TensorProduct.map_tmul counitBialgHom"
namespace PointReduction
p2m_open "Bialgebra"

section BaseChangeCoalgebra

variable (𝓞 S L : Type*) [CommRing 𝓞] [CommRing S] [Algebra 𝓞 S] [CommRing L] [Bialgebra 𝓞 L]

noncomputable def baseChangeTensorHom : L ⊗[𝓞] L →ₐ[𝓞] (S ⊗[𝓞] L) ⊗[S] (S ⊗[𝓞] L) :=
  Algebra.TensorProduct.lift
    ((Algebra.TensorProduct.includeLeft :
        S ⊗[𝓞] L →ₐ[𝓞] (S ⊗[𝓞] L) ⊗[S] (S ⊗[𝓞] L)).comp
      (Algebra.TensorProduct.includeRight : L →ₐ[𝓞] S ⊗[𝓞] L))
    (((Algebra.TensorProduct.includeRight :
        S ⊗[𝓞] L →ₐ[S] (S ⊗[𝓞] L) ⊗[S] (S ⊗[𝓞] L)).restrictScalars 𝓞).comp
      (Algebra.TensorProduct.includeRight : L →ₐ[𝓞] S ⊗[𝓞] L))
    (fun _ _ => @Commute.all ((S ⊗[𝓞] L) ⊗[S] (S ⊗[𝓞] L)) _ _ _)

@[scoped simp] theorem baseChangeTensorHom_tmul (l₁ l₂ : L) :
    baseChangeTensorHom 𝓞 S L (l₁ ⊗ₜ[𝓞] l₂) = ((1 : S) ⊗ₜ[𝓞] l₁) ⊗ₜ[S] ((1 : S) ⊗ₜ[𝓞] l₂) := by
  rw [baseChangeTensorHom, Algebra.TensorProduct.lift_tmul]
  simp only [AlgHom.comp_apply, AlgHom.restrictScalars_apply, Algebra.TensorProduct.includeRight_apply,
    Algebra.TensorProduct.includeLeft_apply, Algebra.TensorProduct.tmul_mul_tmul, one_mul, mul_one]

variable {𝓞 S L}

theorem comul_one_tmul (l : L) :
    Coalgebra.comul (R := S) ((1 : S) ⊗ₜ[𝓞] l) =
      baseChangeTensorHom 𝓞 S L (Coalgebra.comul (R := 𝓞) l) := by
  rw [TensorProduct.comul_tmul, CommSemiring.comul_apply]
  induction Coalgebra.comul (R := 𝓞) l using TensorProduct.induction_on with
  | zero => rw [TensorProduct.tmul_zero, LinearEquiv.map_zero, map_zero]
  | tmul l₁ l₂ =>
    rw [baseChangeTensorHom_tmul, TensorProduct.AlgebraTensorModule.tensorTensorTensorComm_tmul]
  | add x y hx hy => rw [TensorProduct.tmul_add, LinearEquiv.map_add, map_add, hx, hy]

theorem counit_one_tmul (l : L) :
    Coalgebra.counit (R := S) ((1 : S) ⊗ₜ[𝓞] l) = algebraMap 𝓞 S (Coalgebra.counit (R := 𝓞) l) := by
  rw [TensorProduct.counit_tmul, CommSemiring.counit_apply, Algebra.algebraMap_eq_smul_one]

end BaseChangeCoalgebra

section Red

variable (R : Type*) [CommRing R] [IsLocalRing R] (A : Type*) [CommRing A] [Bialgebra R A]

local notation "k" => IsLocalRing.ResidueField R

noncomputable def redPt (f : A →ₐ[R] R) : k ⊗[R] A →ₐ[k] k :=
  Algebra.TensorProduct.lift (Algebra.ofId k k) ((Algebra.ofId R k).comp f) (fun _ _ => Commute.all _ _)

variable {R A}

theorem redPt_tmul (f : A →ₐ[R] R) (c : k) (a : A) :
    redPt R A f (c ⊗ₜ[R] a) = c * IsLocalRing.residue R (f a) := by
  rw [redPt, Algebra.TensorProduct.lift_tmul]
  rfl

theorem algHom_ext_one_tmul {C : Type*} [CommRing C] [Algebra R C] [Algebra k C] [IsScalarTower R k C]
    {F G : k ⊗[R] A →ₐ[k] C}
    (h : ∀ a, F ((1 : k) ⊗ₜ[R] a) = G ((1 : k) ⊗ₜ[R] a)) : F = G := by
  refine Algebra.TensorProduct.ext' fun c a => ?_
  have : (c ⊗ₜ[R] a : k ⊗[R] A) = c • ((1 : k) ⊗ₜ[R] a) := by
    rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
  rw [this, map_smul, map_smul, h]

theorem redPt_convMul (f g : A →ₐ[R] R) :
    redPt R A (WithConv.toConv f * WithConv.toConv g).ofConv =
      (WithConv.toConv (redPt R A f) * WithConv.toConv (redPt R A g)).ofConv := by
  refine algHom_ext_one_tmul fun a => ?_
  rw [redPt_tmul, one_mul, AlgHom.convMul_apply, AlgHom.convMul_apply, comul_one_tmul]

  induction Coalgebra.comul (R := R) a using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | tmul a₁ a₂ =>
    rw [baseChangeTensorHom_tmul, Algebra.TensorProduct.lift_tmul, Algebra.TensorProduct.lift_tmul]
    show IsLocalRing.residue R (f a₁ * g a₂) = _
    rw [redPt_tmul, redPt_tmul, one_mul, one_mul, map_mul]
  | add x y hx hy => simp only [map_add, hx, hy]

theorem redPt_convOne :
    redPt R A (1 : WithConv (A →ₐ[R] R)).ofConv = (1 : WithConv (k ⊗[R] A →ₐ[k] k)).ofConv := by
  refine algHom_ext_one_tmul fun a => ?_
  rw [redPt_tmul, one_mul, AlgHom.convOne_apply, AlgHom.convOne_apply, counit_one_tmul, Algebra.algebraMap_self,
    RingHom.id_apply]
  rfl

variable (R A)

noncomputable def redHom : WithConv (A →ₐ[R] R) →* WithConv (k ⊗[R] A →ₐ[k] k) where
  toFun f := WithConv.toConv (redPt R A f.ofConv)
  map_one' := congrArg WithConv.toConv (redPt_convOne (R := R) (A := A))
  map_mul' f g := congrArg WithConv.toConv (redPt_convMul f.ofConv g.ofConv)

variable {R A}

theorem redHom_apply (f : WithConv (A →ₐ[R] R)) : (redHom R A f).ofConv = redPt R A f.ofConv := rfl

theorem redHom_eq_one_iff (f : WithConv (A →ₐ[R] R)) :
    redHom R A f = 1 ↔ ∀ a : A, f.ofConv a - Coalgebra.counit (R := R) a ∈ IsLocalRing.maximalIdeal R := by
  constructor
  · intro h a
    have h1 := congrArg (fun F : WithConv (k ⊗[R] A →ₐ[k] k) => F.ofConv ((1 : k) ⊗ₜ[R] a)) h
    simp only [redHom_apply, redPt_tmul, one_mul, AlgHom.convOne_apply, counit_one_tmul,
      Algebra.algebraMap_self, RingHom.id_apply] at h1
    rw [← IsLocalRing.residue_eq_zero_iff, map_sub, sub_eq_zero]
    exact h1
  · intro h
    apply WithConv.ofConv_injective
    refine algHom_ext_one_tmul fun a => ?_
    rw [redHom_apply, redPt_tmul, one_mul, AlgHom.convOne_apply, counit_one_tmul, Algebra.algebraMap_self,
      RingHom.id_apply]
    have := h a
    rw [← IsLocalRing.residue_eq_zero_iff, map_sub, sub_eq_zero] at this
    exact this

theorem redHom_surjective [IsDomain R] [IsIntegrallyClosed R]
    (K : Type*) [Field K] [Algebra R K] [IsFractionRing R K] [IsAlgClosed K]
    [Module.Finite R A] [Module.Flat R A] :
    Function.Surjective (redHom R A) := by
  intro F
  let ψ : A →ₐ[R] k := (F.ofConv.restrictScalars R).comp Algebra.TensorProduct.includeRight
  obtain ⟨φ, hφ⟩ :=
    AlgHom.exists_residue_comp_eq_of_moduleFinite_of_flat_of_isAlgClosed_fractionRing R K A ψ
  refine ⟨WithConv.toConv φ, ?_⟩
  apply WithConv.ofConv_injective
  refine algHom_ext_one_tmul fun a => ?_
  rw [redHom_apply, WithConv.ofConv_toConv, redPt_tmul, one_mul, hφ]
  rfl

end Red

end Bialgebra.PointReduction
p2m_reactivate "P2MW.S_HopfAlgebra_exists_eq_comp_of_forall_sub_counit_mem_maximalIdeal_of_bijective_tensorProduct_isReduced_valuationSubring.Bialgebra P2MW.S_HopfAlgebra_exists_eq_comp_of_forall_sub_counit_mem_maximalIdeal_of_bijective_tensorProduct_isReduced_valuationSubring.Bialgebra.PointReduction"
p2m_reactivate "P2MW.S_HopfAlgebra_exists_eq_comp_of_forall_sub_counit_mem_maximalIdeal_of_bijective_tensorProduct_isReduced_valuationSubring.Bialgebra"

namespace Algebra p2m_export "Algebra" "ofId_apply algebraMap_eq_smul_one IsAlgebraic.of_finite TensorProduct.rid botEquivOfInjective ofId isIntegral_iff commutes TensorProduct.includeRight TensorProduct.tmul_mul_tmul TensorProduct.lift_tmul mk TensorProduct.rid_tmul TensorProduct.includeLeft_apply algebraMap TensorProduct.lid FormallyUnramified TensorProduct.lift TensorProduct.map_tmul Etale.iff_exists_algEquiv_prod TensorProduct.liftEquiv IsIntegral.isIntegral algebraMap_self TensorProduct.ext' Etale TensorProduct.includeRight_apply TensorProduct.includeLeft id mem_bot restrictScalars TensorProduct.map FormallyUnramified.isReduced_of_field TensorProduct.lid_tmul natCard_algHom_eq_finrank_residueField_tensorProduct_of_flat_of_isReduced" end Algebra
p2m_open_scoped "Algebra" in

theorem Algebra.natCard_algHom_self_eq_natCard_algHom_of_isIntegrallyClosed_of_isIntegral
    (R : Type*) [CommRing R] [IsDomain R] [IsIntegrallyClosed R]
    (K : Type*) [Field K] [Algebra R K] [IsFractionRing R K]
    (B : Type*) [CommRing B] [Algebra R B] [Algebra.IsIntegral R B] :
    Nat.card (B →ₐ[R] R) = Nat.card (B →ₐ[R] K) := by
  classical
  have hinj : Function.Injective (algebraMap R K) := IsFractionRing.injective R K

  have hmem : ∀ (φ : B →ₐ[R] K) (b : B), φ b ∈ (⊥ : Subalgebra R K) := fun φ b => by
    obtain ⟨y, hy⟩ := (IsIntegrallyClosed.isIntegral_iff (R := R) (K := K)).1
      ((Algebra.IsIntegral.isIntegral (R := R) b).map φ)
    exact Algebra.mem_bot.2 ⟨y, hy⟩
  set e := Algebra.botEquivOfInjective hinj with he
  have hval : ∀ x : (⊥ : Subalgebra R K), algebraMap R K (e x) = x.val := fun x =>
    congrArg Subtype.val (e.symm_apply_apply x)
  exact Nat.card_congr
    { toFun := fun ψ => (Algebra.ofId R K).comp ψ
      invFun := fun φ => (e : (⊥ : Subalgebra R K) →ₐ[R] R).comp (φ.codRestrict ⊥ (hmem φ))
      left_inv := fun ψ => by
        apply AlgHom.ext; intro b
        apply hinj
        rw [AlgHom.comp_apply]
        exact hval _
      right_inv := fun φ => by
        apply AlgHom.ext; intro b
        rw [AlgHom.comp_apply, AlgHom.comp_apply, Algebra.ofId_apply]
        exact hval _ }

namespace Algebra p2m_export "Algebra" "ofId_apply algebraMap_eq_smul_one IsAlgebraic.of_finite TensorProduct.rid botEquivOfInjective ofId isIntegral_iff commutes TensorProduct.includeRight TensorProduct.tmul_mul_tmul TensorProduct.lift_tmul mk TensorProduct.rid_tmul TensorProduct.includeLeft_apply algebraMap TensorProduct.lid FormallyUnramified TensorProduct.lift TensorProduct.map_tmul Etale.iff_exists_algEquiv_prod TensorProduct.liftEquiv IsIntegral.isIntegral algebraMap_self TensorProduct.ext' Etale TensorProduct.includeRight_apply TensorProduct.includeLeft id mem_bot restrictScalars TensorProduct.map FormallyUnramified.isReduced_of_field TensorProduct.lid_tmul natCard_algHom_eq_finrank_residueField_tensorProduct_of_flat_of_isReduced" namespace TensorProduct p2m_export "Algebra.TensorProduct" "includeRight tmul_mul_tmul lift_tmul rid_tmul includeLeft_apply lift map_tmul rTensor liftEquiv ext' includeRight_apply tensorTensorTensorComm_tmul includeLeft map ext lid_tmul" end Algebra.TensorProduct
p2m_open_scoped "Algebra Algebra.TensorProduct" in

theorem Algebra.TensorProduct.natCard_algHom_eq_mul
    (R : Type*) [CommRing R] (A B C : Type*) [CommRing A] [CommRing B] [CommRing C]
    [Algebra R A] [Algebra R B] [Algebra R C] :
    Nat.card (A ⊗[R] B →ₐ[R] C) = Nat.card (A →ₐ[R] C) * Nat.card (B →ₐ[R] C) := by
  rw [← Nat.card_prod]
  refine Nat.card_congr ((Algebra.TensorProduct.liftEquiv).symm.trans ?_)
  exact
    { toFun := fun fg => fg.1
      invFun := fun fg => ⟨fg, fun _ _ => Commute.all _ _⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }

namespace Algebra
p2m_export "Algebra" "ofId_apply algebraMap_eq_smul_one IsAlgebraic.of_finite TensorProduct.rid botEquivOfInjective ofId isIntegral_iff commutes TensorProduct.includeRight TensorProduct.tmul_mul_tmul TensorProduct.lift_tmul mk TensorProduct.rid_tmul TensorProduct.includeLeft_apply algebraMap TensorProduct.lid FormallyUnramified TensorProduct.lift TensorProduct.map_tmul Etale.iff_exists_algEquiv_prod TensorProduct.liftEquiv IsIntegral.isIntegral algebraMap_self TensorProduct.ext' Etale TensorProduct.includeRight_apply TensorProduct.includeLeft id mem_bot restrictScalars TensorProduct.map FormallyUnramified.isReduced_of_field TensorProduct.lid_tmul natCard_algHom_eq_finrank_residueField_tensorProduct_of_flat_of_isReduced"
p2m_open "Algebra"

attribute [local instance] IsArtinianRing.fieldOfSubtypeIsMaximal in

theorem etale_of_isReduced_of_perfectField (K A : Type u) [Field K] [PerfectField K] [CommRing A] [Algebra K A]
    [Module.Finite K A] [IsReduced A] : Algebra.Etale K A := by
  haveI : IsArtinianRing A := isArtinian_of_tower K (inferInstance : IsArtinian K A)
  rw [Algebra.Etale.iff_exists_algEquiv_prod]
  refine ⟨MaximalSpectrum A, inferInstance, fun I => A ⧸ I.asIdeal, inferInstance, inferInstance,
    (IsArtinianRing.equivPi A).restrictScalars K, fun I => ⟨inferInstance, ?_⟩⟩
  haveI : Module.Finite K (A ⧸ I.asIdeal) := inferInstance
  haveI : Algebra.IsAlgebraic K (A ⧸ I.asIdeal) := Algebra.IsAlgebraic.of_finite K _
  infer_instance

end Algebra
p2m_reactivate "P2MW.S_HopfAlgebra_exists_eq_comp_of_forall_sub_counit_mem_maximalIdeal_of_bijective_tensorProduct_isReduced_valuationSubring.Bialgebra P2MW.S_HopfAlgebra_exists_eq_comp_of_forall_sub_counit_mem_maximalIdeal_of_bijective_tensorProduct_isReduced_valuationSubring.Bialgebra.PointReduction"

namespace HopfAlgebra
p2m_export "HopfAlgebra" "mk isReduced_of_finiteType_of_charZero isUnit_withConv_algHom natCard_algHom_dvd_natCard_algHom_of_surjective isLocalRing_of_isReduced_cartierDual_of_finrank_eq_prime_pow"
namespace FormalCount
p2m_open "HopfAlgebra"

theorem finrank_le_finrank_baseChange_of_universal
    {P : Type} [CommRing P] (k : Type) [Field k] [Algebra P k]
    (A M : Type) [CommRing A] [HopfAlgebra P A] [CommRing M] [HopfAlgebra P M] (π : A →ₐc[P] M)
    (huniv : ∀ (N : Type) [CommRing N] [HopfAlgebra k N] [Coalgebra.IsCocomm k N]
        [Module.Free k N] [Module.Finite k N] [Algebra.Etale k (CartierDual k N)]
        (f : k ⊗[P] A →ₐc[k] N),
          ∃! g : k ⊗[P] M →ₐc[k] N, g.comp (Bialgebra.TensorProduct.map (BialgHom.id k k) π) = f)
    (M₀ : Type) [CommRing M₀] [HopfAlgebra k M₀] [Coalgebra.IsCocomm k M₀] [Module.Finite k M₀]
    [Algebra.Etale k (CartierDual k M₀)]
    (f : k ⊗[P] A →ₐc[k] M₀) (hf : Function.Surjective f) [Module.Finite k (k ⊗[P] M)] :
    Module.finrank k M₀ ≤ Module.finrank k (k ⊗[P] M) := by
  haveI : Module.Free k M₀ := Module.Free.of_divisionRing k M₀
  obtain ⟨g, hg, -⟩ := huniv M₀ f
  have hgs : Function.Surjective g := by
    intro y
    obtain ⟨x, rfl⟩ := hf y
    exact ⟨Bialgebra.TensorProduct.map (BialgHom.id k k) π x, by rw [← hg]; rfl⟩
  exact LinearMap.finrank_le_finrank_of_surjective (f := (g : k ⊗[P] M →ₐ[k] M₀).toLinearMap) hgs

end HopfAlgebra.FormalCount
p2m_reactivate "P2MW.S_HopfAlgebra_exists_eq_comp_of_forall_sub_counit_mem_maximalIdeal_of_bijective_tensorProduct_isReduced_valuationSubring.Bialgebra P2MW.S_HopfAlgebra_exists_eq_comp_of_forall_sub_counit_mem_maximalIdeal_of_bijective_tensorProduct_isReduced_valuationSubring.Bialgebra.PointReduction"
p2m_reactivate "P2MW.S_HopfAlgebra_exists_eq_comp_of_forall_sub_counit_mem_maximalIdeal_of_bijective_tensorProduct_isReduced_valuationSubring.Bialgebra P2MW.S_HopfAlgebra_exists_eq_comp_of_forall_sub_counit_mem_maximalIdeal_of_bijective_tensorProduct_isReduced_valuationSubring.Bialgebra.PointReduction"

namespace HopfAlgebra
p2m_export "HopfAlgebra" "mk isReduced_of_finiteType_of_charZero isUnit_withConv_algHom natCard_algHom_dvd_natCard_algHom_of_surjective isLocalRing_of_isReduced_cartierDual_of_finrank_eq_prime_pow"
namespace FormalCount
p2m_open "HopfAlgebra"

theorem natCard_algHom_eq_one_of_isLocalRing (k B : Type*) [Field k] [CommRing B] [Algebra k B] [IsLocalRing B]
    (φ₀ : B →ₐ[k] k) : Nat.card (B →ₐ[k] k) = 1 := by
  haveI : Subsingleton (B →ₐ[k] k) := ⟨fun φ ψ => by
    apply AlgHom.ext; intro b
    have hker : ∀ χ : B →ₐ[k] k, RingHom.ker χ = IsLocalRing.maximalIdeal B := fun χ =>
      IsLocalRing.eq_maximalIdeal (RingHom.ker_isMaximal_of_surjective χ fun c => ⟨algebraMap k B c, χ.commutes c⟩)
    have hb : b - algebraMap k B (φ b) ∈ RingHom.ker ψ := by
      rw [hker ψ, ← hker φ, RingHom.mem_ker, map_sub, AlgHom.commutes, Algebra.algebraMap_self, RingHom.id_apply,
        sub_self]
    rw [RingHom.mem_ker, map_sub, AlgHom.commutes, Algebra.algebraMap_self, RingHom.id_apply, sub_eq_zero] at hb
    exact hb.symm⟩
  haveI : Unique (B →ₐ[k] k) := uniqueOfSubsingleton φ₀
  exact Nat.card_unique

theorem finite_right_of_finite_tensorProduct (k : Type*) [Field k] (M₀ E₀ : Type*)
    [AddCommGroup M₀] [Module k M₀] [AddCommGroup E₀] [Module k E₀] [Nontrivial M₀]
    [Module.Finite k (M₀ ⊗[k] E₀)] : Module.Finite k E₀ := by
  obtain ⟨x, hx⟩ := exists_ne (0 : M₀)

  let ι : E₀ →ₗ[k] M₀ ⊗[k] E₀ := TensorProduct.mk k M₀ E₀ x
  have hι : Function.Injective ι := by
    obtain ⟨f, hf⟩ := Module.Projective.exists_dual_eq_one k hx
    refine Function.LeftInverse.injective (g := fun z => TensorProduct.lid k E₀ (LinearMap.rTensor E₀ f z)) ?_
    intro e
    show TensorProduct.lid k E₀ (LinearMap.rTensor E₀ f (x ⊗ₜ[k] e)) = e
    rw [LinearMap.rTensor_tmul, TensorProduct.lid_tmul, hf, one_smul]
  exact Module.Finite.of_injective ι hι

end HopfAlgebra.FormalCount
p2m_reactivate "P2MW.S_HopfAlgebra_exists_eq_comp_of_forall_sub_counit_mem_maximalIdeal_of_bijective_tensorProduct_isReduced_valuationSubring.Bialgebra P2MW.S_HopfAlgebra_exists_eq_comp_of_forall_sub_counit_mem_maximalIdeal_of_bijective_tensorProduct_isReduced_valuationSubring.Bialgebra.PointReduction"
p2m_reactivate "P2MW.S_HopfAlgebra_exists_eq_comp_of_forall_sub_counit_mem_maximalIdeal_of_bijective_tensorProduct_isReduced_valuationSubring.Bialgebra P2MW.S_HopfAlgebra_exists_eq_comp_of_forall_sub_counit_mem_maximalIdeal_of_bijective_tensorProduct_isReduced_valuationSubring.Bialgebra.PointReduction"

namespace HopfAlgebra
p2m_export "HopfAlgebra" "mk isReduced_of_finiteType_of_charZero isUnit_withConv_algHom natCard_algHom_dvd_natCard_algHom_of_surjective isLocalRing_of_isReduced_cartierDual_of_finrank_eq_prime_pow"
namespace FormalCount
p2m_open "HopfAlgebra"

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

end HopfAlgebra.FormalCount
p2m_reactivate "P2MW.S_HopfAlgebra_exists_eq_comp_of_forall_sub_counit_mem_maximalIdeal_of_bijective_tensorProduct_isReduced_valuationSubring.Bialgebra P2MW.S_HopfAlgebra_exists_eq_comp_of_forall_sub_counit_mem_maximalIdeal_of_bijective_tensorProduct_isReduced_valuationSubring.Bialgebra.PointReduction"
p2m_reactivate "P2MW.S_HopfAlgebra_exists_eq_comp_of_forall_sub_counit_mem_maximalIdeal_of_bijective_tensorProduct_isReduced_valuationSubring.Bialgebra P2MW.S_HopfAlgebra_exists_eq_comp_of_forall_sub_counit_mem_maximalIdeal_of_bijective_tensorProduct_isReduced_valuationSubring.Bialgebra.PointReduction"

open HopfAlgebra.FormalCount Bialgebra.PointReduction in
theorem solution
    (p : ℕ) [Fact p.Prime]
    (P : ValuationSubring (AlgebraicClosure ℚ)) [HenselianLocalRing P]
    (hp : (p : P) ∈ IsLocalRing.maximalIdeal P)
    (A : Type) [CommRing A] [HopfAlgebra P A] [Coalgebra.IsCocomm P A]
    [Module.Finite P A] [Module.Free P A]
    (hA : ∃ n : ℕ, Module.finrank P A = p ^ n)

    (M : Type) [CommRing M] [HopfAlgebra P M] [Coalgebra.IsCocomm P M] [Module.Free P M] [Module.Finite P M]
    (π : A →ₐc[P] M) (hπ : Function.Surjective π) (hMet : Algebra.Etale P (CartierDual P M))
    (hμbc : (∀ (R' : Type) [CommRing R'] [HenselianLocalRing R'] [Algebra P R'],
          IsLocalHom (algebraMap P R') →
          Algebra.Etale R' (CartierDual R' (R' ⊗[P] M)) ∧
          ∀ (N : Type) [CommRing N] [HopfAlgebra R' N] [Coalgebra.IsCocomm R' N]
            [Module.Free R' N] [Module.Finite R' N] [Algebra.Etale R' (CartierDual R' N)]
            (f : R' ⊗[P] A →ₐc[R'] N),
              ∃! g : R' ⊗[P] M →ₐc[R'] N,
                g.comp (Bialgebra.TensorProduct.map (BialgHom.id R' R') π) = f))

    (hord : ∃ (M₀ : Type) (_ : CommRing M₀) (_ : HopfAlgebra (IsLocalRing.ResidueField P) M₀)
        (_ : Module.Finite (IsLocalRing.ResidueField P) M₀) (_ : Module.Free (IsLocalRing.ResidueField P) M₀)
        (E₀ : Type) (_ : CommRing E₀) (_ : HopfAlgebra (IsLocalRing.ResidueField P) E₀)
        (Θ : IsLocalRing.ResidueField P ⊗[P] A →ₐc[IsLocalRing.ResidueField P]
          M₀ ⊗[IsLocalRing.ResidueField P] E₀),
        Function.Bijective Θ ∧ IsReduced E₀ ∧ IsReduced (CartierDual (IsLocalRing.ResidueField P) M₀))
    (f : A →ₐ[P] P) (hf : ∀ a : A, f a - Coalgebra.counit (R := P) a ∈ IsLocalRing.maximalIdeal P) :
    ∃ g : M →ₐ[P] P, f = g.comp (π : A →ₐ[P] M) := by
  classical

  haveI hkac : IsAlgClosed (IsLocalRing.ResidueField P) := ValuationSubring.isAlgClosed_residueField P
  haveI : CharP (IsLocalRing.ResidueField P) p :=
    (CharP.charP_iff_prime_eq_zero Fact.out).2 (by
      rw [← map_natCast (algebraMap P (IsLocalRing.ResidueField P)) p]
      exact (IsLocalRing.residue_eq_zero_iff _).2 hp)
  obtain ⟨M₀, _, _, _, _, E₀, _, _, Θ, hΘ, hE₀red, hM₀red⟩ := hord
  let Θa : IsLocalRing.ResidueField P ⊗[P] A →ₐ[IsLocalRing.ResidueField P] M₀ ⊗[IsLocalRing.ResidueField P] E₀ := Θ
  have hΘa : Function.Bijective Θa := hΘ

  let f₀ : IsLocalRing.ResidueField P ⊗[P] A →ₐc[IsLocalRing.ResidueField P] M₀ :=
    ((Bialgebra.TensorProduct.rid (IsLocalRing.ResidueField P) (IsLocalRing.ResidueField P) M₀ :
        M₀ ⊗[IsLocalRing.ResidueField P] IsLocalRing.ResidueField P ≃ₐc[IsLocalRing.ResidueField P] M₀) :
        M₀ ⊗[IsLocalRing.ResidueField P] IsLocalRing.ResidueField P →ₐc[IsLocalRing.ResidueField P] M₀).comp
      ((Bialgebra.TensorProduct.map (BialgHom.id (IsLocalRing.ResidueField P) M₀)
        (Bialgebra.counitBialgHom (IsLocalRing.ResidueField P) E₀)).comp Θ)
  have hf₀ : Function.Surjective f₀ := by
    intro y
    obtain ⟨x, hx⟩ := hΘ.2 (y ⊗ₜ[IsLocalRing.ResidueField P] (1 : E₀))
    refine ⟨x, ?_⟩
    show (Bialgebra.TensorProduct.rid (IsLocalRing.ResidueField P) (IsLocalRing.ResidueField P) M₀)
      (Bialgebra.TensorProduct.map (BialgHom.id (IsLocalRing.ResidueField P) M₀) (Bialgebra.counitBialgHom (IsLocalRing.ResidueField P) E₀) (Θ x)) = y
    rw [hx, Bialgebra.TensorProduct.map_tmul, Bialgebra.counitBialgHom_apply, Bialgebra.counit_one,
      Bialgebra.TensorProduct.rid_tmul, one_smul]
    rfl

  haveI : Coalgebra.IsCocomm (IsLocalRing.ResidueField P) M₀ :=
    isCocomm_of_surjective (f₀ : IsLocalRing.ResidueField P ⊗[P] A →ₗc[IsLocalRing.ResidueField P] M₀) hf₀
  obtain ⟨n, hn⟩ := hA
  have hp' : p.Prime := Fact.out

  haveI : IsReduced (AlgebraicClosure ℚ ⊗[P] A) :=
    HopfAlgebra.isReduced_of_finiteType_of_charZero (AlgebraicClosure ℚ) (AlgebraicClosure ℚ ⊗[P] A)
  haveI : IsReduced (AlgebraicClosure ℚ ⊗[P] M) :=
    HopfAlgebra.isReduced_of_finiteType_of_charZero (AlgebraicClosure ℚ) (AlgebraicClosure ℚ ⊗[P] M)
  have hXK : Nat.card (A →ₐ[P] AlgebraicClosure ℚ) = Module.finrank P A := by
    rw [Algebra.natCard_algHom_eq_finrank_residueField_tensorProduct_of_flat_of_isReduced
      (AlgebraicClosure ℚ) A, Module.finrank_baseChange]
  have hYK : Nat.card (M →ₐ[P] AlgebraicClosure ℚ) = Module.finrank P M := by
    rw [Algebra.natCard_algHom_eq_finrank_residueField_tensorProduct_of_flat_of_isReduced
      (AlgebraicClosure ℚ) M, Module.finrank_baseChange]
  have hX : Nat.card (A →ₐ[P] P) = p ^ n := by
    rw [Algebra.natCard_algHom_self_eq_natCard_algHom_of_isIntegrallyClosed_of_isIntegral P (AlgebraicClosure ℚ) A,
      hXK, hn]
  have hY : Nat.card (M →ₐ[P] P) = Module.finrank P M := by
    rw [Algebra.natCard_algHom_self_eq_natCard_algHom_of_isIntegrallyClosed_of_isIntegral P (AlgebraicClosure ℚ) M,
      hYK]

  obtain ⟨j, -, hj⟩ : ∃ j ≤ n, Module.finrank P M = p ^ j := by
    haveI : Finite (A →ₐ[P] AlgebraicClosure ℚ) := Nat.finite_of_card_ne_zero (by
      rw [hXK, hn]; exact pow_ne_zero _ hp'.ne_zero)
    have hdvd := HopfAlgebra.natCard_algHom_dvd_natCard_algHom_of_surjective P (AlgebraicClosure ℚ) A M π hπ
    rw [hXK, hYK, hn] at hdvd
    exact (Nat.dvd_prime_pow hp').1 hdvd

  haveI : Nontrivial M₀ := (Bialgebra.counitAlgHom (IsLocalRing.ResidueField P) M₀).toRingHom.domain_nontrivial
  haveI : Module.Finite (IsLocalRing.ResidueField P) (M₀ ⊗[IsLocalRing.ResidueField P] E₀) :=
    Module.Finite.of_surjective Θa.toLinearMap hΘa.2
  haveI : Module.Finite (IsLocalRing.ResidueField P) E₀ :=
    finite_right_of_finite_tensorProduct (IsLocalRing.ResidueField P) M₀ E₀
  haveI := hE₀red

  have hdim : Module.finrank (IsLocalRing.ResidueField P) M₀ * Module.finrank (IsLocalRing.ResidueField P) E₀ = p ^ n := by
    rw [← Module.finrank_tensorProduct, ← LinearEquiv.finrank_eq (LinearEquiv.ofBijective Θa.toLinearMap hΘa),
      Module.finrank_baseChange, hn]
  obtain ⟨m, -, hm⟩ : ∃ m ≤ n, Module.finrank (IsLocalRing.ResidueField P) M₀ = p ^ m :=
    (Nat.dvd_prime_pow hp').1 (Dvd.intro _ hdim)
  haveI : IsLocalRing M₀ :=
    HopfAlgebra.isLocalRing_of_isReduced_cartierDual_of_finrank_eq_prime_pow (IsLocalRing.ResidueField P) p M₀
      hM₀red m hm
  have hXk : Nat.card (IsLocalRing.ResidueField P ⊗[P] A →ₐ[IsLocalRing.ResidueField P] IsLocalRing.ResidueField P) =
      Module.finrank (IsLocalRing.ResidueField P) E₀ := by
    rw [Nat.card_congr (AlgEquiv.arrowCongr (AlgEquiv.ofBijective Θa hΘa) AlgEquiv.refl),
      Algebra.TensorProduct.natCard_algHom_eq_mul,
      natCard_algHom_eq_one_of_isLocalRing _ _ (Bialgebra.counitAlgHom (IsLocalRing.ResidueField P) M₀), one_mul,
      AlgHom.natCard_eq_finrank_of_isReduced_of_isAlgClosed]

  have hred_surj := redHom_surjective (R := P) (A := A) (AlgebraicClosure ℚ)
  haveI : Finite (WithConv (A →ₐ[P] P)) := by
    refine Nat.finite_of_card_ne_zero ?_
    rw [Nat.card_congr (WithConv.equiv (A →ₐ[P] P)), hX]; exact pow_ne_zero _ hp'.ne_zero
  have hcount := MonoidHom.natCard_eq_natCard_fiber_one_mul_of_surjective_of_forall_isUnit (fun x => redHom P A x)
    (map_mul (redHom P A)) (map_one (redHom P A)) hred_surj
    (fun x => by
      obtain ⟨u, hu⟩ := HopfAlgebra.isUnit_withConv_algHom (R := P) (A := A) (L := P) x
      exact ⟨↑u⁻¹, by rw [← hu, Units.inv_mul]⟩)
  rw [Nat.card_congr (WithConv.equiv (A →ₐ[P] P)), hX,
    Nat.card_congr (WithConv.equiv (IsLocalRing.ResidueField P ⊗[P] A →ₐ[IsLocalRing.ResidueField P] IsLocalRing.ResidueField P)),
    hXk] at hcount

  have hE₀pos : 0 < Module.finrank (IsLocalRing.ResidueField P) E₀ := by
    rcases Nat.eq_zero_or_pos (Module.finrank (IsLocalRing.ResidueField P) E₀) with h0 | h0
    · rw [h0, mul_zero] at hdim; exact absurd hdim.symm (pow_ne_zero _ hp'.ne_zero)
    · exact h0
  have hF : Nat.card {x : WithConv (A →ₐ[P] P) // redHom P A x = 1} = Module.finrank (IsLocalRing.ResidueField P) M₀ :=
    Nat.eq_of_mul_eq_mul_right hE₀pos (hcount.symm.trans hdim.symm)

  obtain ⟨hMket, huniv⟩ := hμbc (IsLocalRing.ResidueField P)
    ⟨fun a ha => by
      by_contra h
      exact (isUnit_iff_ne_zero.1 ha)
        ((IsLocalRing.residue_eq_zero_iff a).2 ((IsLocalRing.mem_maximalIdeal a).2 h))⟩
  haveI : IsReduced (CartierDual (IsLocalRing.ResidueField P) (IsLocalRing.ResidueField P ⊗[P] M)) := by
    haveI := hMket
    exact Algebra.FormallyUnramified.isReduced_of_field (IsLocalRing.ResidueField P) _
  haveI : IsLocalRing (IsLocalRing.ResidueField P ⊗[P] M) :=
    HopfAlgebra.isLocalRing_of_isReduced_cartierDual_of_finrank_eq_prime_pow (IsLocalRing.ResidueField P) p
      (IsLocalRing.ResidueField P ⊗[P] M) inferInstance j (by rw [Module.finrank_baseChange, hj])

  have hMformal : ∀ g : WithConv (M →ₐ[P] P), redHom P M g = 1 := fun g => by
    have h1 := natCard_algHom_eq_one_of_isLocalRing (IsLocalRing.ResidueField P) (IsLocalRing.ResidueField P ⊗[P] M)
      (Bialgebra.counitAlgHom _ _)
    haveI := (Nat.card_eq_one_iff_unique.1 h1).1
    exact WithConv.ofConv_injective (Subsingleton.elim _ _)

  let Φ : (M →ₐ[P] P) → {x : WithConv (A →ₐ[P] P) // redHom P A x = 1} := fun g =>
    ⟨WithConv.toConv (g.comp (π : A →ₐ[P] M)), by
      rw [redHom_eq_one_iff]
      intro a
      have := (redHom_eq_one_iff (R := P) (A := M) (WithConv.toConv g)).1 (hMformal _) (π a)
      rw [WithConv.ofConv_toConv] at this ⊢
      rw [AlgHom.comp_apply]
      convert this using 2
      all_goals first | rfl | exact (CoalgHomClass.counit_comp_apply π a).symm⟩
  have hΦinj : Function.Injective Φ := fun g g' h => by
    have h' := congrArg (fun x => (x.1).ofConv) h
    simp only [Φ] at h'
    exact AlgHom.ext fun m => by obtain ⟨a, rfl⟩ := hπ m; exact AlgHom.congr_fun h' a

  haveI : Algebra.Etale (IsLocalRing.ResidueField P) (CartierDual (IsLocalRing.ResidueField P) M₀) := by
    haveI := hM₀red
    exact Algebra.etale_of_isReduced_of_perfectField (IsLocalRing.ResidueField P) _
  have hle : Nat.card {x : WithConv (A →ₐ[P] P) // redHom P A x = 1} ≤ Nat.card (M →ₐ[P] P) := by
    rw [hF, hY]
    exact (finrank_le_finrank_baseChange_of_universal (IsLocalRing.ResidueField P) A M π huniv M₀ f₀ hf₀).trans_eq
      Module.finrank_baseChange

  haveI : Finite {x : WithConv (A →ₐ[P] P) // redHom P A x = 1} := inferInstance
  have hΦbij := hΦinj.bijective_of_nat_card_le hle
  obtain ⟨g, hg⟩ := hΦbij.2 ⟨WithConv.toConv f, (redHom_eq_one_iff (WithConv.toConv f)).2 hf⟩
  exact ⟨g, by have := congrArg (fun x => x.1.ofConv) hg; simpa [Φ] using this.symm⟩

end S_HopfAlgebra_exists_eq_comp_of_forall_sub_counit_mem_maximalIdeal_of_bijective_tensorProduct_isReduced_valuationSubring
end P2MW
export P2MW.S_HopfAlgebra_exists_eq_comp_of_forall_sub_counit_mem_maximalIdeal_of_bijective_tensorProduct_isReduced_valuationSubring (solution)
