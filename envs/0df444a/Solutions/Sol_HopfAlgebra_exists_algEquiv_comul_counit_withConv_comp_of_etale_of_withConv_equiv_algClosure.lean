-- Prove2me | solution 1 for HopfAlgebra.exists_algEquiv_comul_counit_withConv_comp_of_etale_of_withConv_equiv_algClosure
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.85352+00:00
-- url     : https://prove2.me/submissions/0b0ec21d-97a1-53b5-9e75-08301e64c57f

import Mathlib
import Mathlib.RingTheory.Etale.Field
import Mathlib.RingTheory.Bialgebra.Convolution
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_HopfAlgebra_exists_algEquiv_comul_counit_withConv_comp_of_etale_of_withConv_equiv_algClosure

set_option autoImplicit false

open scoped TensorProduct

namespace EtalePointsDescent

section Separation

universe u

variable {K : Type*} [Field K] {Ω : Type*} [Field Ω] [Algebra K Ω] [IsAlgClosed Ω]

theorem eq_of_forall_algHom_apply_eq {A : Type u} [CommRing A] [Algebra K A] [Algebra.Etale K A]
    {a b : A} (h : ∀ χ : A →ₐ[K] Ω, χ a = χ b) : a = b := by
  obtain ⟨I, _, Ai, _, _, e, hAi⟩ := (Algebra.Etale.iff_exists_algEquiv_prod K A).mp inferInstance
  apply e.injective
  funext i
  haveI : Module.Finite K (Ai i) := (hAi i).1
  haveI : Algebra.IsAlgebraic K (Ai i) := Algebra.IsAlgebraic.of_finite K (Ai i)
  let ψ : Ai i →ₐ[K] Ω := IsAlgClosed.lift
  let χ : A →ₐ[K] Ω := ψ.comp ((Pi.evalAlgHom K Ai i).comp e.toAlgHom)
  have hχ := h χ
  exact ψ.toRingHom.injective hχ

end Separation

section Points

variable {K : Type*} [Field K] {Ω : Type*} [Field Ω] [Algebra K Ω]
variable {A : Type*} [CommRing A] [Algebra K A]

variable (K Ω A) in
theorem finite_algHom [Module.Finite K A] : Finite (A →ₐ[K] Ω) :=
  (linearIndependent_toLinearMap K A Ω).finite

theorem card_algHom_le_finrank [Module.Finite K A] [Fintype (A →ₐ[K] Ω)] :
    Fintype.card (A →ₐ[K] Ω) ≤ Module.finrank K A := by
  have h := (linearIndependent_toLinearMap K A Ω).fintype_card_le_finrank
  rwa [Module.finrank_linearMap_self] at h

variable (K Ω) in

def evFun (a : A) : (A →ₐ[K] Ω) → Ω := fun x => x a

@[scoped simp] theorem evFun_apply (a : A) (x : A →ₐ[K] Ω) : evFun K Ω a x = x a := rfl

variable [IsAlgClosed Ω]

theorem linearIndependent_evFun [Algebra.Etale K A] {ι : Type*} (b : Module.Basis ι K A) :
    LinearIndependent Ω (fun i => evFun K Ω (b i)) := by
  classical
  rw [linearIndependent_iff']
  intro s c hc i hi
  set z : Ω ⊗[K] A := ∑ j ∈ s, c j ⊗ₜ[K] b j with hz_def
  have hz : z = 0 := by
    apply eq_of_forall_algHom_apply_eq (K := Ω) (Ω := Ω)
    intro χ
    rw [map_zero]
    let x : A →ₐ[K] Ω := (χ.restrictScalars K).comp Algebra.TensorProduct.includeRight
    have hx := congrFun hc x
    simp only [Finset.sum_apply, Pi.smul_apply, evFun_apply, smul_eq_mul, Pi.zero_apply] at hx
    have hχ : ∀ j, χ (c j ⊗ₜ[K] b j) = c j * x (b j) := by
      intro j
      have h1 : c j ⊗ₜ[K] b j = c j • ((1 : Ω) ⊗ₜ[K] b j) := by
        rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
      rw [h1, map_smul, smul_eq_mul]
      rfl
    rw [hz_def, map_sum]
    simp_rw [hχ]
    exact hx
  let bΩ := Algebra.TensorProduct.basis Ω b
  have hz' : z = ∑ j ∈ s, c j • bΩ j := by
    rw [hz_def]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Algebra.TensorProduct.basis_apply, TensorProduct.smul_tmul', smul_eq_mul, mul_one]
  have hli := (linearIndependent_iff'.mp bΩ.linearIndependent) s c (by rw [← hz', hz])
  exact hli i hi

noncomputable def evBasis [Algebra.Etale K A] [Module.Finite K A] [Fintype (A →ₐ[K] Ω)]
    {ι : Type*} [Fintype ι] (b : Module.Basis ι K A) :
    Module.Basis ι Ω ((A →ₐ[K] Ω) → Ω) :=
  basisOfLinearIndependentOfCardEqFinrank' _ (linearIndependent_evFun b) (by
    apply le_antisymm
    · exact (linearIndependent_evFun (Ω := Ω) b).fintype_card_le_finrank
    · rw [Module.finrank_fintype_fun_eq_card, ← Module.finrank_eq_card_basis b]
      exact card_algHom_le_finrank)

@[scoped simp] theorem evBasis_apply [Algebra.Etale K A] [Module.Finite K A] [Fintype (A →ₐ[K] Ω)]
    {ι : Type*} [Fintype ι] (b : Module.Basis ι K A) (i : ι) :
    evBasis (Ω := Ω) b i = evFun K Ω (b i) := by
  simp [evBasis]

end Points

section Descent

variable {K : Type*} [Field K] {Ω : Type*} [Field Ω] [Algebra K Ω] [IsAlgClosed Ω] [IsGalois K Ω]
variable {A : Type*} [CommRing A] [Algebra K A] [Algebra.Etale K A]

theorem exists_forall_apply_eq (F : (A →ₐ[K] Ω) → Ω)
    (hF : ∀ (σ : Ω ≃ₐ[K] Ω) (x : A →ₐ[K] Ω), F (σ.toAlgHom.comp x) = σ (F x)) :
    ∃ a : A, ∀ x : A →ₐ[K] Ω, x a = F x := by
  classical
  haveI : Module.Finite K A := Algebra.FormallyUnramified.finite_of_free K A
  haveI : Finite (A →ₐ[K] Ω) := finite_algHom K Ω A
  letI : Fintype (A →ₐ[K] Ω) := Fintype.ofFinite _
  let b := Module.finBasis K A
  let bF := evBasis (Ω := Ω) b
  set c : Fin (Module.finrank K A) → Ω := fun i => bF.repr F i with hc_def
  have hFsum : F = ∑ i, c i • evFun K Ω (b i) := by
    conv_lhs => rw [← bF.sum_repr F]
    simp [bF, c]
  have hF' : ∀ y : A →ₐ[K] Ω, F y = ∑ i, c i * y (b i) := by
    intro y
    have := congrFun hFsum y
    simpa [Finset.sum_apply] using this

  have hc : ∀ (σ : Ω ≃ₐ[K] Ω) (i), σ (c i) = c i := by
    intro σ
    have key : ∀ y : A →ₐ[K] Ω, F y = ∑ i, σ (c i) * y (b i) := by
      intro y
      let x : A →ₐ[K] Ω := σ.symm.toAlgHom.comp y
      have hx : σ.toAlgHom.comp x = y := by
        ext a
        simp [x]
      calc F y = F (σ.toAlgHom.comp x) := by rw [hx]
        _ = σ (F x) := hF σ x
        _ = σ (∑ i, c i * x (b i)) := by rw [hF' x]
        _ = ∑ i, σ (c i) * y (b i) := by simp [map_sum, map_mul, x]
    have hsum : (∑ i, σ (c i) • bF i) = F := by
      funext y
      rw [key y]
      simp [Finset.sum_apply, bF]
    have hrepr := bF.repr_sum_self (fun i => σ (c i))
    rw [hsum] at hrepr
    intro i
    have := congrFun hrepr i

    rw [← this]

  have hcK : ∀ i, ∃ d : K, algebraMap K Ω d = c i := fun i =>
    (InfiniteGalois.mem_range_algebraMap_iff_fixed (c i)).mpr (fun σ => hc σ i)
  choose d hd using hcK
  refine ⟨∑ i, d i • b i, fun x => ?_⟩
  rw [hF' x, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_smul, Algebra.smul_def, hd]

end Descent

section Iso

variable {K : Type*} [Field K] {Ω : Type*} [Field Ω] [Algebra K Ω] [IsAlgClosed Ω] [IsGalois K Ω]
variable {A : Type*} [CommRing A] [Algebra K A] [Algebra.Etale K A]
variable {B : Type*} [CommRing B] [Algebra K B] [Algebra.Etale K B]

omit [Algebra.Etale K B] in

theorem exists_algHom_forall_comp_eq (β : (A →ₐ[K] Ω) → (B →ₐ[K] Ω))
    (hβ : ∀ (σ : Ω ≃ₐ[K] Ω) (x : A →ₐ[K] Ω), β (σ.toAlgHom.comp x) = σ.toAlgHom.comp (β x)) :
    ∃ φ : B →ₐ[K] A, ∀ x : A →ₐ[K] Ω, x.comp φ = β x := by
  let evA : A →ₐ[K] ((A →ₐ[K] Ω) → Ω) := Pi.algHom K (fun _ => Ω) (fun x => x)
  have hinj : Function.Injective evA := fun a a' h =>
    eq_of_forall_algHom_apply_eq (K := K) (Ω := Ω) (fun χ => congrFun h χ)
  let Φ : B →ₐ[K] ((A →ₐ[K] Ω) → Ω) := Pi.algHom K (fun _ => Ω) (fun x => β x)
  have hΦ : ∀ b, Φ b ∈ evA.range := by
    intro b
    obtain ⟨a, ha⟩ := exists_forall_apply_eq (K := K) (Ω := Ω) (A := A) (fun x => β x b)
      (fun σ x => by show β (σ.toAlgHom.comp x) b = σ (β x b); rw [hβ]; rfl)
    exact ⟨a, funext fun x => ha x⟩
  let e := AlgEquiv.ofInjective evA hinj
  refine ⟨e.symm.toAlgHom.comp (Φ.codRestrict evA.range hΦ), fun x => ?_⟩
  ext b
  have h1 : evA (e.symm ⟨Φ b, hΦ b⟩) = Φ b := by
    have := AlgEquiv.ofInjective_apply evA hinj (e.symm ⟨Φ b, hΦ b⟩)
    rw [AlgEquiv.apply_symm_apply] at this
    exact this.symm
  exact congrFun h1 x

theorem exists_algEquiv_forall_comp_eq (β : (A →ₐ[K] Ω) ≃ (B →ₐ[K] Ω))
    (hβ : ∀ (σ : Ω ≃ₐ[K] Ω) (x : A →ₐ[K] Ω), β (σ.toAlgHom.comp x) = σ.toAlgHom.comp (β x)) :
    ∃ φ : B ≃ₐ[K] A, ∀ x : A →ₐ[K] Ω, x.comp φ.toAlgHom = β x := by
  have hβ' : ∀ (σ : Ω ≃ₐ[K] Ω) (y : B →ₐ[K] Ω),
      β.symm (σ.toAlgHom.comp y) = σ.toAlgHom.comp (β.symm y) := by
    intro σ y
    apply β.injective
    rw [β.apply_symm_apply, hβ, β.apply_symm_apply]
  obtain ⟨φ, hφ⟩ := exists_algHom_forall_comp_eq (K := K) (Ω := Ω) β hβ
  obtain ⟨ψ, hψ⟩ := exists_algHom_forall_comp_eq (K := K) (Ω := Ω) β.symm hβ'
  have h1 : φ.comp ψ = AlgHom.id K A := by
    ext a
    apply eq_of_forall_algHom_apply_eq (K := K) (Ω := Ω)
    intro x
    have := congrArg (fun g : B →ₐ[K] Ω => g.comp ψ) (hφ x)
    rw [hψ (β x), Equiv.symm_apply_apply] at this
    exact DFunLike.congr_fun this a
  have h2 : ψ.comp φ = AlgHom.id K B := by
    ext b
    apply eq_of_forall_algHom_apply_eq (K := K) (Ω := Ω)
    intro y
    have := congrArg (fun g : A →ₐ[K] Ω => g.comp φ) (hψ y)
    rw [hφ (β.symm y), Equiv.apply_symm_apply] at this
    exact DFunLike.congr_fun this b
  exact ⟨AlgEquiv.ofAlgHom φ ψ h1 h2, hφ⟩

end Iso

section Additive

variable {K : Type*} [CommRing K] {Ω : Type*} [CommRing Ω] [Algebra K Ω]
variable {A : Type*} [CommRing A] [HopfAlgebra K A] {M : Type*} [AddCommGroup M]

theorem equiv_one (e : WithConv (A →ₐ[K] Ω) ≃ M) (he : ∀ f g, e (f * g) = e f + e g) :
    e 1 = 0 := by
  have h : e 1 + e 1 = e 1 + 0 := by rw [← he, one_mul, add_zero]
  exact add_left_cancel h

theorem equiv_symm_zero (e : WithConv (A →ₐ[K] Ω) ≃ M) (he : ∀ f g, e (f * g) = e f + e g) :
    e.symm 0 = 1 :=
  e.injective (by rw [e.apply_symm_apply, equiv_one e he])

theorem equiv_symm_add (e : WithConv (A →ₐ[K] Ω) ≃ M) (he : ∀ f g, e (f * g) = e f + e g)
    (m n : M) : e.symm (m + n) = e.symm m * e.symm n :=
  e.injective (by rw [e.apply_symm_apply, he, e.apply_symm_apply, e.apply_symm_apply])

end Additive

section Conv

variable {K : Type*} [CommRing K] {Ω : Type*} [CommRing Ω] [Algebra K Ω]
variable {A : Type*} [CommRing A] [HopfAlgebra K A]
variable {B : Type*} [CommRing B] [HopfAlgebra K B]

theorem lift_map_eq (x y : A →ₐ[K] Ω) (φ : B ≃ₐ[K] A) (t : B ⊗[K] B) :
    Algebra.TensorProduct.lift x y (fun _ _ => .all _ _)
        (TensorProduct.map φ.toLinearMap φ.toLinearMap t) =
      Algebra.TensorProduct.lift (x.comp φ.toAlgHom) (y.comp φ.toAlgHom) (fun _ _ => .all _ _) t := by
  induction t using TensorProduct.induction_on with
  | zero => simp
  | tmul a b =>
    rw [TensorProduct.map_tmul, Algebra.TensorProduct.lift_tmul, Algebra.TensorProduct.lift_tmul]
    rfl
  | add s t hs ht => rw [map_add, map_add, hs, ht, map_add]

theorem algHom_tensor_eq_lift (χ : A ⊗[K] A →ₐ[K] Ω) :
    χ = Algebra.TensorProduct.lift (χ.comp Algebra.TensorProduct.includeLeft)
      ((χ.restrictScalars K).comp Algebra.TensorProduct.includeRight) (fun _ _ => .all _ _) := by
  apply Algebra.TensorProduct.ext'
  intro a b
  rw [Algebra.TensorProduct.lift_tmul]
  simp only [AlgHom.coe_comp, Function.comp_apply, AlgHom.coe_restrictScalars',
    Algebra.TensorProduct.includeLeft_apply, Algebra.TensorProduct.includeRight_apply]
  rw [← map_mul, Algebra.TensorProduct.tmul_mul_tmul, one_mul, mul_one]

end Conv

section Main

variable (K : Type*) [Field K] (Ω : Type*) [Field Ω] [Algebra K Ω]
    [IsAlgClosed Ω] [Algebra.IsAlgebraic K Ω] [IsGalois K Ω]
    {M : Type*} [AddCommGroup M] [DistribMulAction (Ω ≃ₐ[K] Ω) M]
    (A : Type*) [CommRing A] [HopfAlgebra K A] [Algebra.Etale K A]
    (eA : WithConv (A →ₐ[K] Ω) ≃ M)
    (heA_add : ∀ f g, eA (f * g) = eA f + eA g)
    (heA_act : ∀ (σ : Ω ≃ₐ[K] Ω) (f g : WithConv (A →ₐ[K] Ω)),
      (∀ a : A, g a = σ (f a)) → eA g = σ • (eA f))
    (B : Type*) [CommRing B] [HopfAlgebra K B] [Algebra.Etale K B]
    (eB : WithConv (B →ₐ[K] Ω) ≃ M)
    (heB_add : ∀ f g, eB (f * g) = eB f + eB g)
    (heB_act : ∀ (σ : Ω ≃ₐ[K] Ω) (f g : WithConv (B →ₐ[K] Ω)),
      (∀ b : B, g b = σ (f b)) → eB g = σ • (eB f))

omit [IsAlgClosed Ω] [Algebra.IsAlgebraic K Ω] [IsGalois K Ω] [Algebra.Etale K A]
  [Algebra.Etale K B] in
include heA_act heB_act in
theorem beta_equivariant (σ : Ω ≃ₐ[K] Ω) (x : A →ₐ[K] Ω) :
    (eB.symm (eA (WithConv.toConv (σ.toAlgHom.comp x)))).ofConv =
      σ.toAlgHom.comp (eB.symm (eA (WithConv.toConv x))).ofConv := by
  have hA : eA (WithConv.toConv (σ.toAlgHom.comp x)) = σ • eA (WithConv.toConv x) :=
    heA_act σ (WithConv.toConv x) (WithConv.toConv (σ.toAlgHom.comp x)) (fun _ => rfl)
  set y : WithConv (B →ₐ[K] Ω) := eB.symm (eA (WithConv.toConv x)) with hy
  have hB : eB (WithConv.toConv (σ.toAlgHom.comp y.ofConv)) = σ • eB y :=
    heB_act σ y (WithConv.toConv (σ.toAlgHom.comp y.ofConv)) (fun _ => rfl)
  have hy' : eB y = eA (WithConv.toConv x) := by rw [hy, Equiv.apply_symm_apply]
  have : eB.symm (eA (WithConv.toConv (σ.toAlgHom.comp x))) =
      WithConv.toConv (σ.toAlgHom.comp y.ofConv) := by
    apply eB.injective
    rw [Equiv.apply_symm_apply, hA, hB, hy']
  rw [this]

omit [Algebra.IsAlgebraic K Ω] in
include heA_add heA_act heB_add heB_act in
theorem main :
    ∃ φ : B ≃ₐ[K] A,
      (∀ x, Coalgebra.comul (R := K) (φ x) =
        (TensorProduct.map φ.toLinearMap φ.toLinearMap) (Coalgebra.comul (R := K) x)) ∧
      (∀ x, Coalgebra.counit (R := K) (φ x) = Coalgebra.counit (R := K) x) ∧
      ∀ f : WithConv (A →ₐ[K] Ω),
        eB (WithConv.toConv ((WithConv.ofConv f).comp φ.toAlgHom)) = eA f := by

  let β : (A →ₐ[K] Ω) ≃ (B →ₐ[K] Ω) :=
    { toFun := fun x => (eB.symm (eA (WithConv.toConv x))).ofConv
      invFun := fun y => (eA.symm (eB (WithConv.toConv y))).ofConv
      left_inv := fun x => by simp
      right_inv := fun y => by simp }
  have hβ : ∀ (σ : Ω ≃ₐ[K] Ω) (x : A →ₐ[K] Ω),
      β (σ.toAlgHom.comp x) = σ.toAlgHom.comp (β x) := fun σ x =>
    beta_equivariant K Ω A eA heA_act B eB heB_act σ x
  obtain ⟨φ, hφ⟩ := exists_algEquiv_forall_comp_eq (K := K) (Ω := Ω) β hβ

  have hpt : ∀ z : A →ₐ[K] Ω,
      WithConv.toConv (z.comp φ.toAlgHom) = eB.symm (eA (WithConv.toConv z)) := by
    intro z
    rw [hφ z]
    rfl
  haveI : Algebra.Etale K (A ⊗[K] A) := Algebra.Etale.comp K A (A ⊗[K] A)
  refine ⟨φ, ?_, ?_, ?_⟩
  ·
    intro b
    apply eq_of_forall_algHom_apply_eq (K := K) (Ω := Ω)
    intro χ
    rw [algHom_tensor_eq_lift χ]
    set x := χ.comp (Algebra.TensorProduct.includeLeft (R := K) (S := K) (A := A) (B := A))
    set y := (χ.restrictScalars K).comp
      (Algebra.TensorProduct.includeRight (R := K) (A := A) (B := A))
    rw [lift_map_eq, ← AlgHom.convMul_apply, ← AlgHom.convMul_apply]
    have hmul : WithConv.toConv (x.comp φ.toAlgHom) * WithConv.toConv (y.comp φ.toAlgHom) =
        WithConv.toConv ((WithConv.toConv x * WithConv.toConv y).ofConv.comp φ.toAlgHom) := by
      rw [hpt, hpt, hpt, heA_add, equiv_symm_add eB heB_add]
    rw [hmul]
    rfl
  ·
    intro b
    apply (algebraMap K Ω).injective
    have h1 : WithConv.toConv ((1 : WithConv (A →ₐ[K] Ω)).ofConv.comp φ.toAlgHom) = 1 := by
      rw [hpt, equiv_one eA heA_add, equiv_symm_zero eB heB_add]
    have h2 := congrArg (fun g : WithConv (B →ₐ[K] Ω) => g b) h1
    change ((1 : WithConv (A →ₐ[K] Ω)) (φ b) : Ω) = (1 : WithConv (B →ₐ[K] Ω)) b at h2
    rwa [AlgHom.convOne_apply, AlgHom.convOne_apply] at h2
  ·
    intro f
    rw [hpt, Equiv.apply_symm_apply]

end Main

end EtalePointsDescent
p2m_reactivate "P2MW.S_HopfAlgebra_exists_algEquiv_comul_counit_withConv_comp_of_etale_of_withConv_equiv_algClosure.EtalePointsDescent"

theorem solution
    (K : Type*) [Field K] (Ω : Type*) [Field Ω] [Algebra K Ω]
    [IsAlgClosed Ω] [Algebra.IsAlgebraic K Ω] [IsGalois K Ω]
    {M : Type*} [AddCommGroup M] [DistribMulAction (Ω ≃ₐ[K] Ω) M]
    (A : Type*) [CommRing A] [HopfAlgebra K A] [Algebra.Etale K A]
    (eA : WithConv (A →ₐ[K] Ω) ≃ M)
    (heA_add : ∀ f g, eA (f * g) = eA f + eA g)
    (heA_act : ∀ (σ : Ω ≃ₐ[K] Ω) (f g : WithConv (A →ₐ[K] Ω)),
      (∀ a : A, g a = σ (f a)) → eA g = σ • (eA f))
    (B : Type*) [CommRing B] [HopfAlgebra K B] [Algebra.Etale K B]
    (eB : WithConv (B →ₐ[K] Ω) ≃ M)
    (heB_add : ∀ f g, eB (f * g) = eB f + eB g)
    (heB_act : ∀ (σ : Ω ≃ₐ[K] Ω) (f g : WithConv (B →ₐ[K] Ω)),
      (∀ b : B, g b = σ (f b)) → eB g = σ • (eB f)) :
    ∃ φ : B ≃ₐ[K] A,
      (∀ x, Coalgebra.comul (R := K) (φ x) =
        (TensorProduct.map φ.toLinearMap φ.toLinearMap) (Coalgebra.comul (R := K) x)) ∧
      (∀ x, Coalgebra.counit (R := K) (φ x) = Coalgebra.counit (R := K) x) ∧
      ∀ f : WithConv (A →ₐ[K] Ω),
        eB (WithConv.toConv ((WithConv.ofConv f).comp φ.toAlgHom)) = eA f :=
  EtalePointsDescent.main K Ω A eA heA_add heA_act B eB heB_add heB_act

end S_HopfAlgebra_exists_algEquiv_comul_counit_withConv_comp_of_etale_of_withConv_equiv_algClosure
end P2MW
export P2MW.S_HopfAlgebra_exists_algEquiv_comul_counit_withConv_comp_of_etale_of_withConv_equiv_algClosure (solution)
