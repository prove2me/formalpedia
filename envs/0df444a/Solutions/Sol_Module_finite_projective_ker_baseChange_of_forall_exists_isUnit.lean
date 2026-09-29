-- Prove2me | solution 1 for Module.finite_projective_ker_baseChange_of_forall_exists_isUnit
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.620212+00:00
-- url     : https://prove2.me/submissions/b34e991b-afeb-5269-b09e-75d4d33ed6c0

import Mathlib
import Definitions.Def_AlgebraicGeometry_TwoChartCech
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_Module_finite_projective_ker_baseChange_of_forall_exists_isUnit

set_option autoImplicit false
set_option maxHeartbeats 6400000
set_option synthInstance.maxHeartbeats 1600000

universe u

open TensorProduct

theorem solution
    {R : Type u} [CommRing R] (A : Type u) [CommRing A] [Algebra R A]
    {C0 C1 F : Type u} [AddCommGroup C0] [Module R C0] [AddCommGroup C1] [Module R C1]
    [AddCommGroup F] [Module R F]
    (δ : C0 →ₗ[R] C1) (Θ : F →ₗ[R] C0) (r : ℕ)
    (hloc : ∀ 𝔮 : PrimeSpectrum A, ∃ g : R, algebraMap R A g ∉ 𝔮.asIdeal ∧
      ∀ (A' : Type u) [CommRing A'] [Algebra R A'], IsUnit (algebraMap R A' g) →
        Module.Finite A' (LinearMap.ker (δ.baseChange A')) ∧
        Module.Projective A' (LinearMap.ker (δ.baseChange A')) ∧
        (∀ 𝔮' : PrimeSpectrum A', Module.rankAtStalk (LinearMap.ker (δ.baseChange A')) 𝔮' = r) ∧
        LinearMap.ker (δ.baseChange A') ≤ LinearMap.range (Θ.baseChange A')) :
    Module.Finite A (LinearMap.ker (δ.baseChange A)) ∧
    Module.Projective A (LinearMap.ker (δ.baseChange A)) ∧
    (∀ 𝔮 : PrimeSpectrum A, Module.rankAtStalk (LinearMap.ker (δ.baseChange A)) 𝔮 = r) ∧
    LinearMap.ker (δ.baseChange A) ≤ LinearMap.range (Θ.baseChange A) := by
  classical

  choose g hg hgood using hloc

  set t : Set A := Set.range (fun 𝔮 : PrimeSpectrum A => algebraMap R A (g 𝔮)) with ht_def
  have ht : Ideal.span t = ⊤ := by
    by_contra hne
    obtain ⟨m, hm, hle⟩ := Ideal.exists_le_maximal _ hne
    exact hg ⟨m, hm.isPrime⟩ (hle (Ideal.subset_span ⟨⟨m, hm.isPrime⟩, rfl⟩))

  let L : t → Type u := fun a => Localization.Away (a : A)

  let e0 : ∀ a : t, (L a) ⊗[A] (A ⊗[R] C0) ≃ₗ[A] (L a) ⊗[R] C0 :=
    fun a => (TensorProduct.AlgebraTensorModule.cancelBaseChange R A (L a) (L a) C0).restrictScalars A
  let e1 : ∀ a : t, (L a) ⊗[A] (A ⊗[R] C1) ≃ₗ[A] (L a) ⊗[R] C1 :=
    fun a => (TensorProduct.AlgebraTensorModule.cancelBaseChange R A (L a) (L a) C1).restrictScalars A
  let f0 : ∀ a : t, A ⊗[R] C0 →ₗ[A] (L a) ⊗[R] C0 := fun a => (e0 a).toLinearMap ∘ₗ TensorProduct.mk A (L a) (A ⊗[R] C0) 1
  let f1 : ∀ a : t, A ⊗[R] C1 →ₗ[A] (L a) ⊗[R] C1 := fun a => (e1 a).toLinearMap ∘ₗ TensorProduct.mk A (L a) (A ⊗[R] C1) 1
  haveI hl0 : ∀ a : t, IsLocalizedModule (Submonoid.powers (a : A)) (f0 a) :=
    fun a => IsLocalizedModule.of_linearEquiv _ _ _
  haveI hl1 : ∀ a : t, IsLocalizedModule (Submonoid.powers (a : A)) (f1 a) :=
    fun a => IsLocalizedModule.of_linearEquiv _ _ _
  have hf0 : ∀ (a : t) (x : A) (c : C0), f0 a (x ⊗ₜ c) = algebraMap A (L a) x ⊗ₜ c := by
    intro a x c
    simp [f0, e0, TensorProduct.AlgebraTensorModule.cancelBaseChange_tmul, Algebra.smul_def]
  have hf1 : ∀ (a : t) (x : A) (c : C1), f1 a (x ⊗ₜ c) = algebraMap A (L a) x ⊗ₜ c := by
    intro a x c
    simp [f1, e1, TensorProduct.AlgebraTensorModule.cancelBaseChange_tmul, Algebra.smul_def]

  have hmap : ∀ a : t, IsLocalizedModule.map (Submonoid.powers (a : A)) (f0 a) (f1 a) (δ.baseChange A) =
      (δ.baseChange (L a)).restrictScalars A := by
    intro a
    apply IsLocalizedModule.linearMap_ext (Submonoid.powers (a : A)) (f0 a) (f1 a)
    rw [IsLocalizedModule.map_comp]
    apply TensorProduct.AlgebraTensorModule.curry_injective
    ext x c
    simp [hf0, hf1, LinearMap.baseChange_tmul]

  let eF : ∀ a : t, (L a) ⊗[A] (A ⊗[R] F) ≃ₗ[A] (L a) ⊗[R] F :=
    fun a => (TensorProduct.AlgebraTensorModule.cancelBaseChange R A (L a) (L a) F).restrictScalars A
  let fF : ∀ a : t, A ⊗[R] F →ₗ[A] (L a) ⊗[R] F := fun a => (eF a).toLinearMap ∘ₗ TensorProduct.mk A (L a) (A ⊗[R] F) 1
  haveI hlF : ∀ a : t, IsLocalizedModule (Submonoid.powers (a : A)) (fF a) :=
    fun a => IsLocalizedModule.of_linearEquiv _ _ _
  have hfF : ∀ (a : t) (x : A) (c : F), fF a (x ⊗ₜ c) = algebraMap A (L a) x ⊗ₜ c := by
    intro a x c
    simp [fF, eF, TensorProduct.AlgebraTensorModule.cancelBaseChange_tmul, Algebra.smul_def]
  have hmapΘ : ∀ a : t, IsLocalizedModule.map (Submonoid.powers (a : A)) (fF a) (f0 a) (Θ.baseChange A) =
      (Θ.baseChange (L a)).restrictScalars A := by
    intro a
    apply IsLocalizedModule.linearMap_ext (Submonoid.powers (a : A)) (fF a) (f0 a)
    rw [IsLocalizedModule.map_comp]
    apply TensorProduct.AlgebraTensorModule.curry_injective
    ext x c
    simp [hf0, hfF, LinearMap.baseChange_tmul]

  let Kl : ∀ a : t, Submodule A ((L a) ⊗[R] C0) := fun a => (LinearMap.ker (δ.baseChange (L a))).restrictScalars A
  have hkerEq : ∀ a : t, LinearMap.ker (IsLocalizedModule.map (Submonoid.powers (a : A)) (f0 a) (f1 a) (δ.baseChange A)) = Kl a := by
    intro a; rw [hmap a, LinearMap.ker_restrictScalars]
  let φ : ∀ a : t, ↥(LinearMap.ker (δ.baseChange A)) →ₗ[A] ↥(Kl a) := fun a =>
    (LinearEquiv.ofEq _ _ (hkerEq a)).toLinearMap ∘ₗ
      LinearMap.toKerIsLocalized (Submonoid.powers (a : A)) (f0 a) (f1 a) (δ.baseChange A)
  haveI hlφ : ∀ a : t, IsLocalizedModule (Submonoid.powers (a : A)) (φ a) := by
    intro a
    haveI := LinearMap.toKerLocalized_isLocalizedModule (L a) (Submonoid.powers (a : A)) (f0 a) (f1 a) (δ.baseChange A)
    exact IsLocalizedModule.of_linearEquiv _ _ _

  have hgood' : ∀ a : t,
      Module.Finite (L a) ↥(LinearMap.ker (δ.baseChange (L a))) ∧
      Module.Projective (L a) ↥(LinearMap.ker (δ.baseChange (L a))) ∧
      (∀ 𝔮' : PrimeSpectrum (L a), Module.rankAtStalk ↥(LinearMap.ker (δ.baseChange (L a))) 𝔮' = r) ∧
      LinearMap.ker (δ.baseChange (L a)) ≤ LinearMap.range (Θ.baseChange (L a)) := by
    intro a
    obtain ⟨𝔮, h𝔮⟩ := a.2
    have h𝔮' : algebraMap R A (g 𝔮) = (a : A) := h𝔮
    refine hgood 𝔮 (L a) ?_
    rw [IsScalarTower.algebraMap_apply R A (L a), h𝔮']
    exact IsLocalization.Away.algebraMap_isUnit (a : A)

  let ι : ∀ a : t, ↥(Kl a) ≃ₗ[L a] ↥(LinearMap.ker (δ.baseChange (L a))) := fun a =>
    Submodule.restrictScalarsEquiv A (L a) _ (LinearMap.ker (δ.baseChange (L a)))
  haveI hfinl : ∀ a : t, Module.Finite (L a) ↥(Kl a) := fun a => by
    haveI := (hgood' a).1
    exact Module.Finite.equiv (ι a).symm
  haveI hprojl : ∀ a : t, Module.Projective (L a) ↥(Kl a) := fun a => by
    haveI := (hgood' a).2.1
    exact Module.Projective.of_equiv (ι a).symm

  haveI hfp : Module.FinitePresentation A ↥(LinearMap.ker (δ.baseChange A)) := by
    refine Module.FinitePresentation.of_localizationSpan' (M := ↥(LinearMap.ker (δ.baseChange A))) t ht (Mₚ := fun a => ↥(Kl a)) (Rₚ := L) (fun a => φ a) ?_
    intro a
    exact Module.finitePresentation_of_projective (L a) ↥(Kl a)
  have hfin : Module.Finite A ↥(LinearMap.ker (δ.baseChange A)) := inferInstance

  have hflat : Module.Flat A ↥(LinearMap.ker (δ.baseChange A)) := by
    refine Module.flat_of_isLocalized_span (R := A) A ↥(LinearMap.ker (δ.baseChange A)) t ht (fun a => ↥(Kl a)) (fun a => φ a) (fun a => ?_)
    haveI : Module.Flat (L a) ↥(Kl a) := Module.Flat.of_projective
    haveI : Module.Flat A (L a) := IsLocalization.flat (L a) (Submonoid.powers (a : A))
    exact Module.Flat.trans A (L a) ↥(Kl a)
  have hproj : Module.Projective A ↥(LinearMap.ker (δ.baseChange A)) := by
    exact Module.Flat.projective_of_finitePresentation (R := A) (M := ↥(LinearMap.ker (δ.baseChange A)))

  have hrank : ∀ 𝔮 : PrimeSpectrum A, Module.rankAtStalk ↥(LinearMap.ker (δ.baseChange A)) 𝔮 = r := by
    intro 𝔮
    let a : t := ⟨algebraMap R A (g 𝔮), ⟨𝔮, rfl⟩⟩
    have ha : (a : A) ∉ 𝔮.asIdeal := hg 𝔮
    have hdisj : Disjoint (↑(Submonoid.powers (a : A)) : Set A) ↑𝔮.asIdeal :=
      (Ideal.disjoint_powers_iff_notMem_of_isPrime (I := 𝔮.asIdeal) (a : A)).mpr ha
    let 𝔮' : PrimeSpectrum (L a) := ⟨Ideal.map (algebraMap A (L a)) 𝔮.asIdeal,
      IsLocalization.isPrime_of_isPrime_disjoint (Submonoid.powers (a : A)) (L a) 𝔮.asIdeal 𝔮.isPrime hdisj⟩
    have hcomap : 𝔮'.comap (algebraMap A (L a)) = 𝔮 :=
      PrimeSpectrum.ext (IsLocalization.under_map_of_isPrime_disjoint (Submonoid.powers (a : A)) (L a) 𝔮.isPrime hdisj)
    have hbc : IsBaseChange (L a) (φ a) := IsLocalizedModule.isBaseChange (Submonoid.powers (a : A)) (L a) (φ a)
    have ebc : (L a) ⊗[A] ↥(LinearMap.ker (δ.baseChange A)) ≃ₗ[L a] ↥(Kl a) := hbc.equiv
    rw [← hcomap, ← Module.rankAtStalk_baseChange,
      Module.rankAtStalk_eq_of_equiv (R := L a) (M := (L a) ⊗[A] ↥(LinearMap.ker (δ.baseChange A))) (N := ↥(Kl a)) ebc,
      Module.rankAtStalk_eq_of_equiv (R := L a) (M := ↥(Kl a)) (N := ↥(LinearMap.ker (δ.baseChange (L a)))) (ι a)]
    exact (hgood' a).2.2.1 𝔮'

  have hle : LinearMap.ker (δ.baseChange A) ≤ LinearMap.range (Θ.baseChange A) := by
    refine Submodule.le_of_isLocalized_span t ht (fun a => (L a) ⊗[R] C0) f0 (fun a => ?_)
    rw [← LinearMap.ker_localizedMap_eq_localized₀_ker (Submonoid.powers (a : A)) (f0 a) (f1 a) (δ.baseChange A),
      ← LinearMap.range_localizedMap_eq_localized₀_range (Submonoid.powers (a : A)) (fF a) (f0 a) (Θ.baseChange A),
      hmap a, hmapΘ a]
    intro x hx
    rw [LinearMap.mem_ker, LinearMap.restrictScalars_apply] at hx
    obtain ⟨y, hy⟩ := (hgood' a).2.2.2 (LinearMap.mem_ker.mpr hx)
    exact ⟨y, hy⟩
  exact ⟨hfin, hproj, hrank, hle⟩

end S_Module_finite_projective_ker_baseChange_of_forall_exists_isUnit
end P2MW
export P2MW.S_Module_finite_projective_ker_baseChange_of_forall_exists_isUnit (solution)
