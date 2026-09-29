-- Prove2me | solution 1 for Module.ker_baseChange_field_of_subsingleton_H1_of_projective
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.620212+00:00
-- url     : https://prove2.me/submissions/79a05324-5b51-52a8-9a0e-92f3a2735945

import Mathlib
import Theorems.Thm_Module_free_coker_and_ker_baseChange_of_ker_le_range_residueField
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_Module_ker_baseChange_field_of_subsingleton_H1_of_projective

set_option autoImplicit false

universe u v

open TensorProduct

namespace BC0Pt

section Transfer

variable {S : Type*} [CommRing S]
  {A B C A' B' C' : Type*} [AddCommGroup A] [Module S A] [AddCommGroup B] [Module S B] [AddCommGroup C] [Module S C]
  [AddCommGroup A'] [Module S A'] [AddCommGroup B'] [Module S B'] [AddCommGroup C'] [Module S C']

theorem exact_of_equiv (f : A →ₗ[S] B) (g : B →ₗ[S] C) (f' : A' →ₗ[S] B') (g' : B' →ₗ[S] C')
    (eA : A ≃ₗ[S] A') (eB : B ≃ₗ[S] B') (eC : C ≃ₗ[S] C')
    (hf : ∀ a, eB (f a) = f' (eA a)) (hg : ∀ b, eC (g b) = g' (eB b)) (h : Function.Exact f g) :
    Function.Exact f' g' := by
  intro b'
  obtain ⟨b, rfl⟩ := eB.surjective b'
  rw [← hg]
  constructor
  · intro hb
    have hb0 : g b = 0 := by
      apply eC.injective; rw [hb, map_zero]
    obtain ⟨a, rfl⟩ := (h b).mp hb0
    exact ⟨eA a, (hf a).symm⟩
  · rintro ⟨a', ha'⟩
    obtain ⟨a, rfl⟩ := eA.surjective a'
    rw [← hf] at ha'
    have : f a = b := eB.injective ha'
    rw [← this, (h (f a)).mpr ⟨a, rfl⟩, map_zero]

theorem injective_of_equiv (f : A →ₗ[S] B) (f' : A' →ₗ[S] B') (eA : A ≃ₗ[S] A') (eB : B ≃ₗ[S] B')
    (hf : ∀ a, eB (f a) = f' (eA a)) (h : Function.Injective f) : Function.Injective f' := by
  intro x y hxy
  obtain ⟨a, rfl⟩ := eA.surjective x
  obtain ⟨b, rfl⟩ := eA.surjective y
  rw [← hf, ← hf] at hxy
  rw [h (eB.injective hxy)]

theorem ker_eq_range_and_injective_of_equiv (f : A →ₗ[S] B) (g : B →ₗ[S] C) (f' : A' →ₗ[S] B') (g' : B' →ₗ[S] C')
    (eA : A ≃ₗ[S] A') (eB : B ≃ₗ[S] B') (eC : C ≃ₗ[S] C')
    (hf : ∀ a, eB (f a) = f' (eA a)) (hg : ∀ b, eC (g b) = g' (eB b))
    (h : LinearMap.range f = LinearMap.ker g ∧ Function.Injective f) :
    LinearMap.range f' = LinearMap.ker g' ∧ Function.Injective f' := by
  refine ⟨?_, injective_of_equiv f f' eA eB hf h.2⟩
  have hex : Function.Exact f g := LinearMap.exact_iff.mpr h.1.symm
  exact (LinearMap.exact_iff.mp (exact_of_equiv f g f' g' eA eB eC hf hg hex)).symm

end Transfer

section Cancel

variable (R : Type*) [CommRing R] (A : Type*) [CommRing A] [Algebra R A] (B : Type*) [CommRing B] [Algebra R B]
  [Algebra A B] [IsScalarTower R A B]
  {M N : Type*} [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N] (f : M →ₗ[R] N)

noncomputable abbrev can (M : Type*) [AddCommGroup M] [Module R M] : B ⊗[A] (A ⊗[R] M) ≃ₗ[B] B ⊗[R] M :=
  TensorProduct.AlgebraTensorModule.cancelBaseChange R A B B M

theorem can_nat (z : B ⊗[A] (A ⊗[R] M)) :
    can R A B N ((f.baseChange A).baseChange B z) = f.baseChange B (can R A B M z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => rw [map_add, map_add, hx, hy, map_add, map_add]
  | tmul b w =>
    induction w using TensorProduct.induction_on with
    | zero => simp
    | add x y hx hy => rw [TensorProduct.tmul_add, map_add, map_add, hx, hy, map_add, map_add]
    | tmul a m =>
      rw [LinearMap.baseChange_tmul, LinearMap.baseChange_tmul,
        TensorProduct.AlgebraTensorModule.cancelBaseChange_tmul,
        TensorProduct.AlgebraTensorModule.cancelBaseChange_tmul, LinearMap.baseChange_tmul]

end Cancel

theorem main
    (R : Type u) [CommRing R]
    {C0 C1 C2 : Type v} [AddCommGroup C0] [Module R C0] [AddCommGroup C1] [Module R C1]
    [AddCommGroup C2] [Module R C2]
    [Module.Finite R C1] [Module.Projective R C1] [Module.Finite R C2] [Module.Projective R C2]
    (d0 : C0 →ₗ[R] C1) (d1 : C1 →ₗ[R] C2) (hdd : d1 ∘ₗ d0 = 0)
    (K : Type u) [Field K] [Algebra R K]
    (hH1 : LinearMap.ker (d1.baseChange K) ≤ LinearMap.range (d0.baseChange K)) :
    LinearMap.range ((LinearMap.ker d0).subtype.baseChange K) = LinearMap.ker (d0.baseChange K) ∧
      Function.Injective ((LinearMap.ker d0).subtype.baseChange K) := by
  classical

  let 𝔭 : Ideal R := RingHom.ker (algebraMap R K)
  haveI h𝔭 : 𝔭.IsPrime := RingHom.ker_isPrime _
  let Rp : Type u := Localization.AtPrime 𝔭

  have hunit : ∀ y : 𝔭.primeCompl, IsUnit (algebraMap R K y) := by
    intro y
    refine isUnit_iff_ne_zero.mpr fun h => y.2 ?_
    show (y : R) ∈ RingHom.ker (algebraMap R K)
    rwa [RingHom.mem_ker]
  letI algRpK : Algebra Rp K := (IsLocalization.lift (M := 𝔭.primeCompl) (S := Rp) hunit).toAlgebra
  have hφ : ∀ r : R, algebraMap Rp K (algebraMap R Rp r) = algebraMap R K r := fun r =>
    IsLocalization.lift_eq (M := 𝔭.primeCompl) (S := Rp) hunit r
  haveI : IsScalarTower R Rp K := IsScalarTower.of_algebraMap_eq fun r => (hφ r).symm

  haveI : IsLocalHom (algebraMap Rp K) := by
    constructor
    intro a ha
    obtain ⟨⟨r, s⟩, rfl⟩ := IsLocalization.mk'_surjective 𝔭.primeCompl a
    dsimp only at ha ⊢
    by_cases hr : r ∈ 𝔭
    · exfalso
      apply ha.ne_zero
      show IsLocalization.lift (M := 𝔭.primeCompl) (S := Rp) hunit (IsLocalization.mk' Rp r s) = 0
      rw [IsLocalization.lift_mk']
      have : algebraMap R K r = 0 := by rwa [← RingHom.mem_ker]
      rw [this, zero_mul]
    · rw [IsLocalization.mk'_eq_mul_mk'_one]
      refine (IsLocalization.map_units Rp (⟨r, show r ∈ 𝔭.primeCompl from hr⟩ : 𝔭.primeCompl)).mul ?_
      exact IsUnit.of_mul_eq_one (algebraMap R Rp s) (by rw [IsLocalization.mk'_spec, map_one])

  let κ : Type u := IsLocalRing.ResidueField Rp
  letI algκK : Algebra κ K := (IsLocalRing.ResidueField.lift (algebraMap Rp K)).toAlgebra
  haveI : IsScalarTower Rp κ K := IsScalarTower.of_algebraMap_eq fun a =>
    (IsLocalRing.ResidueField.lift_residue_apply (algebraMap Rp K) a).symm
  haveI : Module.FaithfullyFlat κ K := inferInstance

  set e0 : Rp ⊗[R] C0 →ₗ[Rp] Rp ⊗[R] C1 := d0.baseChange Rp with he0
  set e1 : Rp ⊗[R] C1 →ₗ[Rp] Rp ⊗[R] C2 := d1.baseChange Rp with he1
  have hee : e1 ∘ₗ e0 = 0 := by
    rw [he0, he1, ← LinearMap.baseChange_comp, hdd]
    ext; simp
  haveI : Module.Free Rp (Rp ⊗[R] C1) := Module.free_of_flat_of_isLocalRing
  haveI : Module.Free Rp (Rp ⊗[R] C2) := Module.free_of_flat_of_isLocalRing

  have hdd' : ∀ {A : Type u} [CommRing A] [Algebra R A], d1.baseChange A ∘ₗ d0.baseChange A = 0 := by
    intro A _ _
    rw [← LinearMap.baseChange_comp, hdd]
    ext; simp
  have hexK : Function.Exact (d0.baseChange K) (d1.baseChange K) := by
    refine LinearMap.exact_iff.mpr (le_antisymm hH1 ?_)
    rintro _ ⟨w, rfl⟩
    rw [LinearMap.mem_ker, ← LinearMap.comp_apply, hdd', LinearMap.zero_apply]

  have hnat : ∀ {M N : Type v} [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N] (f : M →ₗ[R] N)
      (z : K ⊗[κ] (κ ⊗[Rp] (Rp ⊗[R] M))),
      (can Rp κ K (Rp ⊗[R] N) ≪≫ₗ can R Rp K N) ((((f.baseChange Rp).baseChange κ).baseChange K) z)
        = f.baseChange K ((can Rp κ K (Rp ⊗[R] M) ≪≫ₗ can R Rp K M) z) := by
    intro M N _ _ _ _ f z
    simp only [LinearEquiv.trans_apply]
    rw [can_nat Rp κ K (f.baseChange Rp) z, can_nat R Rp K f]
  have hexK' : Function.Exact ((e0.baseChange κ).baseChange K) ((e1.baseChange κ).baseChange K) := by
    refine exact_of_equiv (d0.baseChange K) (d1.baseChange K) _ _
      (can Rp κ K (Rp ⊗[R] C0) ≪≫ₗ can R Rp K C0).symm (can Rp κ K (Rp ⊗[R] C1) ≪≫ₗ can R Rp K C1).symm
      (can Rp κ K (Rp ⊗[R] C2) ≪≫ₗ can R Rp K C2).symm ?_ ?_ hexK
    · intro a
      apply (can Rp κ K (Rp ⊗[R] C1) ≪≫ₗ can R Rp K C1).injective
      rw [LinearEquiv.apply_symm_apply, he0, hnat d0, LinearEquiv.apply_symm_apply]
    · intro b
      apply (can Rp κ K (Rp ⊗[R] C2) ≪≫ₗ can R Rp K C2).injective
      rw [LinearEquiv.apply_symm_apply, he1, hnat d1, LinearEquiv.apply_symm_apply]
  have hexκ : Function.Exact (e0.baseChange κ) (e1.baseChange κ) := by
    apply Module.FaithfullyFlat.lTensor_reflects_exact κ K
    simpa only [LinearMap.baseChange_eq_ltensor] using hexK'
  have hκ : LinearMap.ker (e1.baseChange κ) ≤ LinearMap.range (e0.baseChange κ) :=
    (LinearMap.exact_iff.mp hexκ).le

  obtain ⟨-, hbc⟩ := Module.free_coker_and_ker_baseChange_of_ker_le_range_residueField Rp e0 e1 hee hκ
  have hK := hbc K

  have hinj : Function.Injective ((LinearMap.ker d0).subtype.baseChange Rp) := by
    have := Module.Flat.lTensor_preserves_injective_linearMap (M := Rp) (LinearMap.ker d0).subtype
      (Submodule.injective_subtype _)
    simpa only [LinearMap.baseChange_eq_ltensor] using this
  have hrange : LinearMap.range ((LinearMap.ker d0).subtype.baseChange Rp) = LinearMap.ker e0 := by
    have hex : Function.Exact ((LinearMap.ker d0).subtype.baseChange Rp) (d0.baseChange Rp) := by
      have := Module.Flat.lTensor_exact Rp (LinearMap.exact_subtype_ker_map d0)
      simpa only [LinearMap.baseChange_eq_ltensor] using this
    rw [he0]
    exact (LinearMap.exact_iff.mp hex).symm
  let G : (Rp ⊗[R] LinearMap.ker d0) ≃ₗ[Rp] LinearMap.ker e0 :=
    (LinearEquiv.ofInjective _ hinj) ≪≫ₗ (LinearEquiv.ofEq _ _ hrange)
  have hG : ∀ w, ((LinearMap.ker e0).subtype (G w) : Rp ⊗[R] C0) = (LinearMap.ker d0).subtype.baseChange Rp w :=
    fun w => rfl
  let GK : K ⊗[Rp] (Rp ⊗[R] LinearMap.ker d0) ≃ₗ[K] K ⊗[Rp] LinearMap.ker e0 := LinearEquiv.baseChange Rp K _ _ G
  have hGK : ∀ w, (LinearMap.ker e0).subtype.baseChange K (GK w)
      = ((LinearMap.ker d0).subtype.baseChange Rp).baseChange K w := by
    intro w
    induction w using TensorProduct.induction_on with
    | zero => simp
    | add x y hx hy => rw [map_add, map_add, hx, hy, map_add]
    | tmul k v =>
      show (LinearMap.ker e0).subtype.baseChange K (k ⊗ₜ G v) = _
      rw [LinearMap.baseChange_tmul, LinearMap.baseChange_tmul, hG]

  refine ker_eq_range_and_injective_of_equiv ((LinearMap.ker e0).subtype.baseChange K) (e0.baseChange K)
    ((LinearMap.ker d0).subtype.baseChange K) (d0.baseChange K)
    (GK.symm ≪≫ₗ can R Rp K (LinearMap.ker d0)) (can R Rp K C0) (can R Rp K C1) ?_ ?_ hK
  · intro a
    obtain ⟨w, rfl⟩ := GK.surjective a
    rw [LinearEquiv.trans_apply, GK.symm_apply_apply, hGK, can_nat R Rp K ((LinearMap.ker d0).subtype) w]
  · intro b
    rw [he0, can_nat R Rp K d0 b]

end BC0Pt

theorem solution
    (R : Type u) [CommRing R]
    {C0 C1 C2 : Type v} [AddCommGroup C0] [Module R C0] [AddCommGroup C1] [Module R C1]
    [AddCommGroup C2] [Module R C2]
    [Module.Finite R C1] [Module.Projective R C1] [Module.Finite R C2] [Module.Projective R C2]
    (d0 : C0 →ₗ[R] C1) (d1 : C1 →ₗ[R] C2) (hdd : d1 ∘ₗ d0 = 0)
    (K : Type u) [Field K] [Algebra R K]
    (hH1 : LinearMap.ker (d1.baseChange K) ≤ LinearMap.range (d0.baseChange K)) :
    LinearMap.range ((LinearMap.ker d0).subtype.baseChange K) = LinearMap.ker (d0.baseChange K) ∧
      Function.Injective ((LinearMap.ker d0).subtype.baseChange K) :=
  BC0Pt.main R d0 d1 hdd K hH1

end S_Module_ker_baseChange_field_of_subsingleton_H1_of_projective
end P2MW
export P2MW.S_Module_ker_baseChange_field_of_subsingleton_H1_of_projective (solution)
