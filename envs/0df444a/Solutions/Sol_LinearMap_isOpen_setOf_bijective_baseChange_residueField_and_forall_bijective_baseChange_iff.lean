-- Prove2me | solution 1 for LinearMap.isOpen_setOf_bijective_baseChange_residueField_and_forall_bijective_baseChange_iff
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.670037+00:00
-- url     : https://prove2.me/submissions/71fba550-ef89-5a79-acaf-49c4f31ec48a

import Mathlib
import Theorems.Thm_LinearMap_isOpen_setOf_surjective_baseChange_residueField
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LinearMap_isOpen_setOf_bijective_baseChange_residueField_and_forall_bijective_baseChange_iff

set_option autoImplicit false

universe u v

open scoped TensorProduct

noncomputable section

namespace LS1Body

open TensorProduct

theorem surjective_baseChange_iff_subsingleton {A : Type*} [CommRing A] {P Q : Type*} [AddCommGroup P] [Module A P]
    [AddCommGroup Q] [Module A Q] (d : P →ₗ[A] Q) (K : Type*) [CommRing K] [Algebra A K] :
    Function.Surjective (d.baseChange K) ↔ Subsingleton (K ⊗[A] (Q ⧸ LinearMap.range d)) := by
  rw [(TensorProduct.tensorQuotientEquiv K (LinearMap.range d)).toEquiv.subsingleton_congr,
    Submodule.Quotient.subsingleton_iff, LinearMap.baseChange_eq_ltensor, ← LinearMap.range_eq_top]
  have : (TensorProduct.map LinearMap.id (LinearMap.range d).subtype).range = (LinearMap.lTensor K d).range :=
    (LinearMap.lTensor_range K).symm
  rw [this]

theorem bijective_iff_surjective_and_finrank_eq {k : Type*} [Field k] {V W : Type*} [AddCommGroup V] [Module k V]
    [AddCommGroup W] [Module k W] [Module.Finite k V] [Module.Finite k W] (h : V →ₗ[k] W) :
    Function.Bijective h ↔ Function.Surjective h ∧ Module.finrank k V = Module.finrank k W := by
  constructor
  · intro hb; exact ⟨hb.2, (LinearEquiv.ofBijective h hb).finrank_eq⟩
  · rintro ⟨hs, hr⟩; exact ⟨(LinearMap.injective_iff_surjective_of_finrank_eq_finrank hr).mpr hs, hs⟩

theorem surjective_baseChange_field_iff {k : Type*} [Field k] (K : Type*) [Field K] [Algebra k K]
    {V W : Type*} [AddCommGroup V] [Module k V] [AddCommGroup W] [Module k W] [Module.Finite k W] (h : V →ₗ[k] W) :
    Function.Surjective (h.baseChange K) ↔ Function.Surjective h := by
  rw [surjective_baseChange_iff_subsingleton, ← Module.finrank_eq_zero_iff_of_free K, Module.finrank_baseChange,
    Module.finrank_eq_zero_iff_of_free k, Submodule.Quotient.subsingleton_iff, LinearMap.range_eq_top]

theorem bijective_baseChange_field_iff {k : Type*} [Field k] (K : Type*) [Field K] [Algebra k K]
    {V W : Type*} [AddCommGroup V] [Module k V] [AddCommGroup W] [Module k W] [Module.Finite k V] [Module.Finite k W]
    (h : V →ₗ[k] W) :
    Function.Bijective (h.baseChange K) ↔ Function.Bijective h := by
  rw [bijective_iff_surjective_and_finrank_eq, bijective_iff_surjective_and_finrank_eq, surjective_baseChange_field_iff,
    Module.finrank_baseChange, Module.finrank_baseChange]

theorem baseChange_baseChange_comp {A : Type*} [CommRing A] (S T : Type*) [CommRing S] [CommRing T] [Algebra A S]
    [Algebra A T] [Algebra S T] [IsScalarTower A S T] {V W : Type*} [AddCommGroup V] [Module A V] [AddCommGroup W]
    [Module A W] (g : V →ₗ[A] W) :
    (AlgebraTensorModule.cancelBaseChange A S T T W).toLinearMap ∘ₗ ((g.baseChange S).baseChange T) =
      (g.baseChange T) ∘ₗ (AlgebraTensorModule.cancelBaseChange A S T T V).toLinearMap := by
  refine LinearMap.ext fun z => ?_
  induction z using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => rw [map_add, map_add, hx, hy]
  | tmul t x =>
    induction x using TensorProduct.induction_on with
    | zero => simp
    | add x y hx hy => rw [TensorProduct.tmul_add, map_add, map_add, hx, hy]
    | tmul s v =>
      simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearMap.baseChange_tmul,
        AlgebraTensorModule.cancelBaseChange_tmul, LinearMap.baseChange_tmul]

theorem bijective_baseChange_baseChange_iff {A : Type*} [CommRing A] (S T : Type*) [CommRing S] [CommRing T]
    [Algebra A S] [Algebra A T] [Algebra S T] [IsScalarTower A S T] {V W : Type*} [AddCommGroup V] [Module A V]
    [AddCommGroup W] [Module A W] (g : V →ₗ[A] W) :
    Function.Bijective ((g.baseChange S).baseChange T) ↔ Function.Bijective (g.baseChange T) := by
  have h := congrArg (fun f : T ⊗[S] (S ⊗[A] V) →ₗ[T] T ⊗[A] W => (f : T ⊗[S] (S ⊗[A] V) → T ⊗[A] W))
    (baseChange_baseChange_comp S T g)
  simp only [LinearMap.coe_comp, LinearEquiv.coe_coe] at h
  rw [← (AlgebraTensorModule.cancelBaseChange A S T T W).toEquiv.comp_bijective, LinearEquiv.coe_toEquiv, h,
    ← LinearEquiv.coe_toEquiv, Equiv.bijective_comp]

theorem surjective_baseChange_baseChange_iff {A : Type*} [CommRing A] (S T : Type*) [CommRing S] [CommRing T]
    [Algebra A S] [Algebra A T] [Algebra S T] [IsScalarTower A S T] {V W : Type*} [AddCommGroup V] [Module A V]
    [AddCommGroup W] [Module A W] (g : V →ₗ[A] W) :
    Function.Surjective ((g.baseChange S).baseChange T) ↔ Function.Surjective (g.baseChange T) := by
  have h := congrArg (fun f : T ⊗[S] (S ⊗[A] V) →ₗ[T] T ⊗[A] W => (f : T ⊗[S] (S ⊗[A] V) → T ⊗[A] W))
    (baseChange_baseChange_comp S T g)
  simp only [LinearMap.coe_comp, LinearEquiv.coe_coe] at h
  rw [← (AlgebraTensorModule.cancelBaseChange A S T T W).toEquiv.comp_surjective, LinearEquiv.coe_toEquiv, h,
    ← LinearEquiv.coe_toEquiv, Equiv.surjective_comp]

theorem injective_of_surjective_of_rankAtStalk_eq {B : Type*} [CommRing B] {F N : Type*} [AddCommGroup F] [Module B F]
    [AddCommGroup N] [Module B N] [Module.Finite B F] [Module.Flat B F] [Module.Finite B N] [Module.Projective B N]
    (g : F →ₗ[B] N) (hs : Function.Surjective g) (hrk : Module.rankAtStalk (R := B) F = Module.rankAtStalk N) :
    Function.Injective g := by
  obtain ⟨s, hs'⟩ := LinearMap.exists_rightInverse_of_surjective g (LinearMap.range_eq_top.mpr hs)
  obtain ⟨e, he₁, he₂⟩ := (LinearMap.exact_subtype_ker_map g).splitSurjectiveEquiv (Submodule.injective_subtype _) ⟨s, hs'⟩
  have hret : ∀ x : LinearMap.ker g, (e ((LinearMap.ker g).subtype x)).1 = x := fun x => by
    have hx : (LinearMap.ker g).subtype x = e.symm (LinearMap.inl B _ _ x) := by rw [he₁]; rfl
    rw [hx, LinearEquiv.apply_symm_apply]; rfl
  haveI : Module.Finite B (LinearMap.ker g) :=
    Module.Finite.of_surjective ((LinearMap.fst B _ _).comp e.toLinearMap) fun x => ⟨(LinearMap.ker g).subtype x, hret x⟩
  haveI : Module.Flat B (LinearMap.ker g) :=
    Module.Flat.of_retract (LinearMap.ker g).subtype ((LinearMap.fst B _ _).comp e.toLinearMap) (LinearMap.ext fun x => hret x)
  have hrk' := Module.rankAtStalk_eq_of_equiv e
  rw [Module.rankAtStalk_prod, hrk] at hrk'
  have hz : Module.rankAtStalk (R := B) (LinearMap.ker g) = 0 := by
    funext q
    have h1 := congrFun hrk' q
    simp only [Pi.add_apply] at h1
    simp only [Pi.zero_apply]; omega
  have hK : Subsingleton (LinearMap.ker g) := Module.rankAtStalk_eq_zero_iff_subsingleton.mp hz
  intro x y hxy
  have hmem : x - y ∈ LinearMap.ker g := by rw [LinearMap.mem_ker, map_sub, hxy, sub_self]
  exact sub_eq_zero.mp (congrArg Subtype.val (hK.elim ⟨x - y, hmem⟩ ⟨0, (LinearMap.ker g).zero_mem⟩))

section Main

variable {A : Type u} [CommRing A] {M : Type v} [AddCommGroup M] [Module A M] [Module.Finite A M] [Module.Projective A M]
  {m : ℕ} (u : (Fin m → A) →ₗ[A] M)

theorem bijective_fibre_iff (p : PrimeSpectrum A) :
    Function.Bijective (u.baseChange p.asIdeal.ResidueField) ↔
      Function.Surjective (u.baseChange p.asIdeal.ResidueField) ∧ Module.rankAtStalk M p = m := by
  haveI : Nontrivial A := p.nontrivial
  rw [bijective_iff_surjective_and_finrank_eq, Module.rankAtStalk_eq p,
    (TensorProduct.piScalarRight A p.asIdeal.ResidueField p.asIdeal.ResidueField (Fin m)).finrank_eq, Module.finrank_fin_fun]
  exact and_congr_right fun _ => eq_comm

theorem isOpen_setOf_bijective :
    IsOpen {𝔭 : PrimeSpectrum A | Function.Bijective (u.baseChange 𝔭.asIdeal.ResidueField)} := by
  haveI : Module.FinitePresentation A M := Module.finitePresentation_of_projective A M
  have hU : {𝔭 : PrimeSpectrum A | Function.Bijective (u.baseChange 𝔭.asIdeal.ResidueField)} =
      {𝔭 : PrimeSpectrum A | Function.Surjective (u.baseChange 𝔭.asIdeal.ResidueField)} ∩
        {𝔭 : PrimeSpectrum A | Module.rankAtStalk M 𝔭 = m} := by
    ext 𝔭; exact bijective_fibre_iff u 𝔭
  rw [hU]
  exact (LinearMap.isOpen_setOf_surjective_baseChange_residueField u).inter
    (Module.isLocallyConstant_rankAtStalk.isOpen_fiber m)

omit [Module.Projective A M] in

theorem fibre_comap_iff (B : Type u) [CommRing B] [Algebra A B] (q : PrimeSpectrum B) :
    (Function.Bijective (u.baseChange q.asIdeal.ResidueField) ↔
        Function.Bijective (u.baseChange (PrimeSpectrum.comap (algebraMap A B) q).asIdeal.ResidueField)) ∧
      (Function.Surjective (u.baseChange q.asIdeal.ResidueField) ↔
        Function.Surjective (u.baseChange (PrimeSpectrum.comap (algebraMap A B) q).asIdeal.ResidueField)) := by
  let φ : (PrimeSpectrum.comap (algebraMap A B) q).asIdeal.ResidueField →ₐ[A] q.asIdeal.ResidueField :=
    Ideal.ResidueField.mapₐ _ _ (Algebra.ofId A B) rfl
  letI : Algebra (PrimeSpectrum.comap (algebraMap A B) q).asIdeal.ResidueField q.asIdeal.ResidueField := φ.toRingHom.toAlgebra
  haveI : IsScalarTower A (PrimeSpectrum.comap (algebraMap A B) q).asIdeal.ResidueField q.asIdeal.ResidueField :=
    IsScalarTower.of_algebraMap_eq fun a => (φ.commutes a).symm
  constructor
  · rw [← bijective_baseChange_baseChange_iff (PrimeSpectrum.comap (algebraMap A B) q).asIdeal.ResidueField q.asIdeal.ResidueField u,
      bijective_baseChange_field_iff]
  · rw [← surjective_baseChange_baseChange_iff (PrimeSpectrum.comap (algebraMap A B) q).asIdeal.ResidueField q.asIdeal.ResidueField u,
      surjective_baseChange_field_iff]

end Main

end LS1Body

open LS1Body in

theorem solution
    {A : Type u} [CommRing A] {M : Type v} [AddCommGroup M] [Module A M] [Module.Finite A M] [Module.Projective A M]
    {m : ℕ} (u : (Fin m → A) →ₗ[A] M) :
    IsOpen {𝔭 : PrimeSpectrum A | Function.Bijective (u.baseChange 𝔭.asIdeal.ResidueField)} ∧
    ∀ (B : Type u) [CommRing B] [Algebra A B],
      Function.Bijective (u.baseChange B) ↔
        Set.range (PrimeSpectrum.comap (algebraMap A B)) ⊆
          {𝔭 : PrimeSpectrum A | Function.Bijective (u.baseChange 𝔭.asIdeal.ResidueField)} := by
  refine ⟨isOpen_setOf_bijective u, fun B _ _ => ⟨fun hB => ?_, fun h => ?_⟩⟩
  ·
    rintro _ ⟨q, rfl⟩
    show Function.Bijective (u.baseChange (PrimeSpectrum.comap (algebraMap A B) q).asIdeal.ResidueField)
    rw [← (fibre_comap_iff u B q).1, ← bijective_baseChange_baseChange_iff B q.asIdeal.ResidueField u]
    have e1 : ((LinearEquiv.ofBijective (u.baseChange B) hB : _ ≃ₗ[B] _) : _ →ₗ[B] _) = u.baseChange B :=
      LinearMap.ext fun _ => rfl
    have := ((LinearEquiv.ofBijective (u.baseChange B) hB).baseChange B q.asIdeal.ResidueField _ _).bijective
    rwa [← LinearEquiv.coe_coe, LinearEquiv.coe_baseChange, e1] at this
  ·
    have hq : ∀ q : PrimeSpectrum B,
        Function.Bijective (u.baseChange (PrimeSpectrum.comap (algebraMap A B) q).asIdeal.ResidueField) := fun q => h ⟨q, rfl⟩

    have hsurj : Function.Surjective (u.baseChange B) := by
      rw [surjective_baseChange_iff_subsingleton, ← Module.support_eq_empty_iff (R := B), Set.eq_empty_iff_forall_notMem]
      intro q hmem
      rw [Module.mem_support_iff_nontrivial_residueField_tensorProduct,
        (TensorProduct.AlgebraTensorModule.cancelBaseChange A B q.asIdeal.ResidueField q.asIdeal.ResidueField
          (M ⧸ LinearMap.range u)).nontrivial_congr, ← not_subsingleton_iff_nontrivial] at hmem
      exact hmem ((surjective_baseChange_iff_subsingleton u _).mp ((fibre_comap_iff u B q).2.mpr (hq q).2))
    refine ⟨?_, hsurj⟩

    have hrkN : ∀ q : PrimeSpectrum B, Module.rankAtStalk (B ⊗[A] M) q = m := fun q => by
      rw [Module.rankAtStalk_baseChange]; exact ((bijective_fibre_iff u _).mp (hq q)).2
    have hrkF : ∀ q : PrimeSpectrum B, Module.rankAtStalk (B ⊗[A] (Fin m → A)) q = m := fun q => by
      haveI : Nontrivial A := (PrimeSpectrum.comap (algebraMap A B) q).nontrivial
      rw [Module.rankAtStalk_baseChange, Module.rankAtStalk_eq_finrank_of_free, Module.finrank_fin_fun]; rfl
    exact injective_of_surjective_of_rankAtStalk_eq (u.baseChange B) hsurj (funext fun q => (hrkF q).trans (hrkN q).symm)

end
end S_LinearMap_isOpen_setOf_bijective_baseChange_residueField_and_forall_bijective_baseChange_iff
end P2MW
export P2MW.S_LinearMap_isOpen_setOf_bijective_baseChange_residueField_and_forall_bijective_baseChange_iff (solution)
