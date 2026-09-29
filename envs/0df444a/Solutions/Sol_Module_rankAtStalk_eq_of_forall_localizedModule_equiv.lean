-- Prove2me | solution 1 for Module.rankAtStalk_eq_of_forall_localizedModule_equiv
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.620212+00:00
-- url     : https://prove2.me/submissions/fb22afa3-c193-5a79-9078-22438066fc27

import Mathlib.RingTheory.Spectrum.Prime.FreeLocus
import Mathlib.RingTheory.Spectrum.Prime.Noetherian
import Mathlib.RingTheory.IsTensorProduct
import Mathlib.RingTheory.Localization.BaseChange
import Mathlib.LinearAlgebra.TensorProduct.Pi
import Mathlib.RingTheory.Artinian.Module
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_Module_rankAtStalk_eq_of_forall_localizedModule_equiv

set_option autoImplicit false

open TensorProduct

universe u

namespace RankAtStalkLocallyIso

section UnitsBaseChange

variable {A : Type*} [CommRing A] (S : Submonoid A) (T : Type*) [CommRing T] [Algebra A T]
  (X : Type*) [AddCommGroup X] [Module A X]

theorem isLocalizedModule_id_of_forall_isUnit (hT : ∀ s : S, IsUnit (algebraMap A T s)) :
    IsLocalizedModule S (LinearMap.id : T ⊗[A] X →ₗ[A] T ⊗[A] X) where
  map_units s := by
    rw [Module.End.isUnit_iff]
    have : ⇑(algebraMap A (Module.End A (T ⊗[A] X)) s) = fun y => algebraMap A T s • y := by
      funext y
      simp [Module.algebraMap_end_apply]
    rw [this]
    exact (hT s).smul_bijective
  surj y := ⟨(y, 1), one_smul _ _⟩
  exists_of_eq h := ⟨1, by simpa using h⟩

noncomputable def tensorLocalizedModuleEquiv (hT : ∀ s : S, IsUnit (algebraMap A T s)) :
    T ⊗[A] X ≃ₗ[T] T ⊗[A] LocalizedModule S X :=
  LinearEquiv.ofBijective ((LocalizedModule.mkLinearMap S X).baseChange T) (by
    haveI := isLocalizedModule_id_of_forall_isUnit S T X hT

    let g : T ⊗[A] X →ₗ[A] T ⊗[A] LocalizedModule S X :=
      (TensorProduct.comm A (LocalizedModule S X) T).toLinearMap ∘ₗ
        (AlgebraTensorModule.rTensor A T (LocalizedModule.mkLinearMap S X)) ∘ₗ
        (TensorProduct.comm A T X).toLinearMap
    haveI : IsLocalizedModule S g := inferInstance
    have hg' : (LocalizedModule.mkLinearMap S X).lTensor T = g :=
      TensorProduct.ext' fun t x => by simp [g]

    have hg : ⇑((LocalizedModule.mkLinearMap S X).baseChange T) =
        ⇑(IsLocalizedModule.linearEquiv S LinearMap.id g) := by
      funext y
      rw [LinearMap.baseChange_eq_ltensor, hg']
      exact (IsLocalizedModule.linearEquiv_apply S LinearMap.id g y).symm
    rw [hg]
    exact LinearEquiv.bijective _)

end UnitsBaseChange

section Artinian

variable (k : Type*) [Field k] (B : Type*) [CommRing B] [Algebra k B] [IsArtinianRing B]
  (V : Type*) [AddCommGroup V] [Module B V] [Module k V] [IsScalarTower k B V] [Module.Finite k V]

theorem finrank_eq_sum_finrank_localization [Fintype (PrimeSpectrum B)] :
    Module.finrank k V =
      ∑ q : PrimeSpectrum B, Module.finrank k (Localization.AtPrime q.asIdeal ⊗[B] V) := by
  classical

  let e : V ≃ₗ[B] ((q : PrimeSpectrum B) → Localization.AtPrime q.asIdeal ⊗[B] V) :=
    (TensorProduct.lid B V).symm ≪≫ₗ
      LinearEquiv.rTensor V (PrimeSpectrum.toPiLocalizationEquiv B).toLinearEquiv ≪≫ₗ
      TensorProduct.piLeft B V (fun q : PrimeSpectrum B => Localization.AtPrime q.asIdeal)

  haveI : ∀ q : PrimeSpectrum B, Module.Finite k (Localization.AtPrime q.asIdeal ⊗[B] V) :=
    fun q => Module.Finite.of_surjective
      ((TensorProduct.mk B (Localization.AtPrime q.asIdeal) V 1).restrictScalars k)
      (TensorProduct.mk_surjective B V _
        (IsArtinianRing.localization_surjective q.asIdeal.primeCompl _))
  rw [(e.restrictScalars k).finrank_eq, Module.finrank_pi_fintype k]

theorem finrank_eq_of_forall_localization_equiv (W : Type*) [AddCommGroup W] [Module B W]
    [Module k W] [IsScalarTower k B W] [Module.Finite k W]
    (H : ∀ q : PrimeSpectrum B, Nonempty
      (Localization.AtPrime q.asIdeal ⊗[B] V ≃ₗ[k] Localization.AtPrime q.asIdeal ⊗[B] W)) :
    Module.finrank k V = Module.finrank k W := by
  classical
  haveI := Fintype.ofFinite (PrimeSpectrum B)
  rw [finrank_eq_sum_finrank_localization k B V, finrank_eq_sum_finrank_localization k B W]
  exact Finset.sum_congr rfl fun q _ => (H q).some.finrank_eq

end Artinian

end RankAtStalkLocallyIso

open RankAtStalkLocallyIso in
theorem solution
    {R A : Type u} [CommRing R] [CommRing A] [Algebra R A] [Module.Finite R A]
    (M N : Type u) [AddCommGroup M] [Module R M] [Module A M] [IsScalarTower R A M]
    [Module.Finite R M] [Module.Flat R M]
    [AddCommGroup N] [Module R N] [Module A N] [IsScalarTower R A N]
    [Module.Finite R N] [Module.Flat R N] (s : Set A) (hs : Ideal.span s = ⊤)
    (H : ∀ h ∈ s, Nonempty
      (LocalizedModule (Submonoid.powers h) M ≃ₗ[A] LocalizedModule (Submonoid.powers h) N)) :
    Module.rankAtStalk (R := R) M = Module.rankAtStalk N := by
  classical
  funext p
  rw [Module.rankAtStalk_eq, Module.rankAtStalk_eq]

  let k := p.asIdeal.ResidueField
  let B := k ⊗[R] A
  letI : Algebra A B := Algebra.TensorProduct.rightAlgebra
  haveI : IsArtinianRing B := IsArtinianRing.of_finite k B

  let eM : B ⊗[A] M ≃ₗ[k] k ⊗[R] M := Algebra.IsPushout.cancelBaseChange R k A B M
  let eN : B ⊗[A] N ≃ₗ[k] k ⊗[R] N := Algebra.IsPushout.cancelBaseChange R k A B N
  haveI : Module.Finite k (B ⊗[A] M) := Module.Finite.equiv eM.symm
  haveI : Module.Finite k (B ⊗[A] N) := Module.Finite.equiv eN.symm
  change Module.finrank k (k ⊗[R] M) = Module.finrank k (k ⊗[R] N)
  rw [← eM.finrank_eq, ← eN.finrank_eq]
  refine finrank_eq_of_forall_localization_equiv k B (B ⊗[A] M) (B ⊗[A] N) fun q => ?_

  obtain ⟨h, hhs, hq⟩ : ∃ h ∈ s, algebraMap A B h ∉ q.asIdeal := by
    by_contra! hcon
    have hle : Ideal.span s ≤ q.asIdeal.comap (algebraMap A B) :=
      Ideal.span_le.mpr fun x hx => Ideal.mem_comap.mpr (hcon x hx)
    rw [hs, top_le_iff] at hle
    exact Ideal.comap_ne_top _ q.isPrime.ne_top hle
  obtain ⟨φ⟩ := H h hhs

  let T := Localization.AtPrime q.asIdeal
  have hT : ∀ x : Submonoid.powers h, IsUnit (algebraMap A T x) := by
    intro x
    obtain ⟨n, hn⟩ := (Submonoid.mem_powers_iff _ _).mp x.2
    rw [← hn, map_pow]
    refine IsUnit.pow n ?_
    rw [IsScalarTower.algebraMap_apply A B T]
    exact IsLocalization.map_units T (⟨algebraMap A B h, hq⟩ : q.asIdeal.primeCompl)

  let e₁ : T ⊗[B] (B ⊗[A] M) ≃ₗ[T] T ⊗[A] M := AlgebraTensorModule.cancelBaseChange A B T T M
  let e₂ : T ⊗[A] M ≃ₗ[T] T ⊗[A] LocalizedModule (.powers h) M :=
    tensorLocalizedModuleEquiv (.powers h) T M hT
  let e₃ : T ⊗[A] LocalizedModule (.powers h) M ≃ₗ[T] T ⊗[A] LocalizedModule (.powers h) N :=
    LinearEquiv.baseChange A T _ _ φ
  let e₄ : T ⊗[A] N ≃ₗ[T] T ⊗[A] LocalizedModule (.powers h) N :=
    tensorLocalizedModuleEquiv (.powers h) T N hT
  let e₅ : T ⊗[B] (B ⊗[A] N) ≃ₗ[T] T ⊗[A] N := AlgebraTensorModule.cancelBaseChange A B T T N
  exact ⟨(e₁ ≪≫ₗ e₂ ≪≫ₗ e₃ ≪≫ₗ e₄.symm ≪≫ₗ e₅.symm).restrictScalars k⟩

end S_Module_rankAtStalk_eq_of_forall_localizedModule_equiv
end P2MW
export P2MW.S_Module_rankAtStalk_eq_of_forall_localizedModule_equiv (solution)
