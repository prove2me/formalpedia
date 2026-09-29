-- Prove2me | solution 1 for Module.finitePresentation_of_rankAtStalk_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.620212+00:00
-- url     : https://prove2.me/submissions/77baf893-63dd-5992-8407-f0eaa96b450b

import Mathlib.RingTheory.Spectrum.Prime.FreeLocus
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_Module_finitePresentation_of_rankAtStalk_eq

set_option autoImplicit false

universe u v

open Module

namespace FPRank

section localizedTop

variable {R : Type*} [CommRing R] (S : Submonoid R) (A : Type*) [CommRing A] [Algebra R A]
  [IsLocalization S A] {M : Type*} [AddCommGroup M] [Module R M] {Mₛ : Type*}
  [AddCommGroup Mₛ] [Module R Mₛ] [Module A Mₛ] [IsScalarTower R A Mₛ] (f : M →ₗ[R] Mₛ)
  [IsLocalizedModule S f]

theorem localized'_eq_top_iff (N : Submodule R M) :
    N.localized' A S f = ⊤ ↔ ∀ x : M, ∃ t : S, (t : R) • x ∈ N := by
  constructor
  · intro H x
    have hx : f x ∈ N.localized' A S f := H ▸ Submodule.mem_top
    obtain ⟨m, hm, t, ht⟩ := (Submodule.mem_localized' A S f N (f x)).mp hx
    rw [IsLocalizedModule.mk'_eq_iff, Submonoid.smul_def, ← map_smul] at ht
    obtain ⟨u, hu⟩ := IsLocalizedModule.exists_of_eq (S := S) (f := f) ht
    refine ⟨u * t, ?_⟩
    rw [Submonoid.coe_mul, mul_smul, ← Submonoid.smul_def, ← hu]
    exact N.smul_mem _ hm
  · intro H
    refine eq_top_iff.mpr fun y _ ↦ ?_
    obtain ⟨⟨x, t⟩, hxt⟩ := IsLocalizedModule.surj S f y
    obtain ⟨t', ht'⟩ := H x
    refine (Submodule.mem_localized' A S f N y).mpr ⟨(t' : R) • x, ht', t' * t, ?_⟩
    rw [IsLocalizedModule.mk'_eq_iff, map_smul, ← hxt, Submonoid.smul_def, Submonoid.smul_def,
      Submonoid.coe_mul, mul_smul]

theorem localized'_eq_top_iff_subsingleton (N : Submodule R M) :
    N.localized' A S f = ⊤ ↔ Subsingleton (LocalizedModule S (M ⧸ N)) := by
  rw [localized'_eq_top_iff, LocalizedModule.subsingleton_iff]
  constructor
  · intro H c
    induction c using Submodule.Quotient.induction_on with
    | H x =>
      obtain ⟨t, ht⟩ := H x
      exact ⟨t, t.2, by
        rw [← Submodule.Quotient.mk_smul, (Submodule.Quotient.mk_eq_zero N).mpr ht]⟩
  · intro H x
    obtain ⟨t, ht, htx⟩ := H (Submodule.Quotient.mk x)
    exact ⟨⟨t, ht⟩,
      (Submodule.Quotient.mk_eq_zero N).mp (by rw [Submodule.Quotient.mk_smul, htx])⟩

end localizedTop

section surjection

variable {A : Type*} [CommRing A] {P : Type*} [AddCommGroup P] [Module A P]
  [Module.Finite A P] [Module.Flat A P] {n : ℕ}

theorem injective_of_surjective_of_rankAtStalk_eq
    (h : ∀ p : PrimeSpectrum A, rankAtStalk P p = n)
    (ψ : (Fin n → A) →ₗ[A] P) (hψ : Function.Surjective ψ) : Function.Injective ψ := by
  rcases subsingleton_or_nontrivial A with hA | hA
  · haveI : Subsingleton (Fin n → A) := inferInstance
    exact Function.injective_of_subsingleton ψ
  apply injective_of_localized_maximal
  intro J hJ
  haveI : Module.Free (Localization.AtPrime J)
      (LocalizedModule J.primeCompl (Fin n → A)) :=
    free_of_flat_of_isLocalRing
  haveI : Module.Free (Localization.AtPrime J) (LocalizedModule J.primeCompl P) :=
    free_of_flat_of_isLocalRing
  have h1 : finrank (Localization.AtPrime J) (LocalizedModule J.primeCompl (Fin n → A)) = n := by
    have := congrFun (rankAtStalk_eq_finrank_of_free (R := A) (M := Fin n → A)) ⟨J, hJ.isPrime⟩
    simpa [rankAtStalk, finrank_fin_fun] using this
  have h2 : finrank (Localization.AtPrime J) (LocalizedModule J.primeCompl P) = n :=
    h ⟨J, hJ.isPrime⟩
  let e : LocalizedModule J.primeCompl P ≃ₗ[Localization.AtPrime J]
      LocalizedModule J.primeCompl (Fin n → A) :=
    LinearEquiv.ofFinrankEq _ _ (h2.trans h1.symm)
  have hsurj : Function.Surjective (LocalizedModule.map J.primeCompl ψ) :=
    LocalizedModule.map_surjective J.primeCompl ψ hψ
  have hinj := OrzechProperty.injective_of_surjective_endomorphism
    (e.toLinearMap ∘ₗ LocalizedModule.map J.primeCompl ψ) (e.surjective.comp hsurj)
  exact fun x y hxy ↦ hinj (by simp [hxy])

theorem finitePresentation_of_surjective_of_rankAtStalk_eq
    (h : ∀ p : PrimeSpectrum A, rankAtStalk P p = n)
    (ψ : (Fin n → A) →ₗ[A] P) (hψ : Function.Surjective ψ) : Module.FinitePresentation A P := by
  haveI : Module.FinitePresentation A (Fin n → A) :=
    Module.finitePresentation_of_projective _ _
  exact Module.FinitePresentation.of_equiv
    (LinearEquiv.ofBijective ψ ⟨injective_of_surjective_of_rankAtStalk_eq h ψ hψ, hψ⟩)

end surjection

section localToGlobal

variable {R : Type u} [CommRing R] {M : Type v} [AddCommGroup M] [Module R M] [Module.Finite R M]

theorem finitePresentation_of_localizationSpan (s : Set R) (hs : Ideal.span s = ⊤)
    (H : ∀ r : s, Module.FinitePresentation (Localization.Away (r : R))
      (LocalizedModule (Submonoid.powers (r : R)) M)) :
    Module.FinitePresentation R M := by
  obtain ⟨k, π, hπ⟩ := Module.Finite.exists_fin' R M
  rw [← Module.FinitePresentation.fg_ker_iff π hπ, ← Module.Finite.iff_fg]
  refine Module.Finite.of_localizationSpan' s hs
    (Rₚ := fun r : s ↦ Localization.Away (r : R))
    (Mₚ := fun r : s ↦ (LinearMap.ker π).localized' (Localization.Away (r : R))
      (Submonoid.powers (r : R))
      (LocalizedModule.mkLinearMap (Submonoid.powers (r : R)) (Fin k → R)))
    (fun r ↦ (LinearMap.ker π).toLocalized' _ _ _) (fun r ↦ ?_)
  refine Module.Finite.iff_fg.mpr ?_
  rw [LinearMap.localized'_ker_eq_ker_localizedMap (Localization.Away (r : R))
    (Submonoid.powers (r : R)) (LocalizedModule.mkLinearMap (Submonoid.powers (r : R)) (Fin k → R))
    (LocalizedModule.mkLinearMap (Submonoid.powers (r : R)) M) π]
  haveI := H r
  exact Module.FinitePresentation.fg_ker _
    (IsLocalizedModule.map_surjective (Submonoid.powers (r : R)) _ _ π hπ)

end localToGlobal

section mainProof

variable {R : Type u} [CommRing R] {M : Type v} [AddCommGroup M] [Module R M]
  [Module.Finite R M] [Module.Flat R M] {n : ℕ}

theorem exists_finitePresentation_away (h : ∀ p : PrimeSpectrum R, rankAtStalk M p = n)
    (p : PrimeSpectrum R) :
    ∃ r : R, r ∉ p.asIdeal ∧ Module.FinitePresentation (Localization.Away r)
      (LocalizedModule (Submonoid.powers r) M) := by
  classical
  let S := p.asIdeal.primeCompl
  let Rₚ := Localization.AtPrime p.asIdeal
  let f : M →ₗ[R] LocalizedModule S M := LocalizedModule.mkLinearMap S M
  haveI : Module.Free Rₚ (LocalizedModule S M) := free_of_flat_of_isLocalRing
  let b : Basis (Fin n) Rₚ (LocalizedModule S M) := Module.finBasisOfFinrankEq Rₚ _ (h p)

  choose ms hms using fun i ↦ IsLocalizedModule.surj S f (b i)
  let N : Submodule R M := Submodule.span R (Set.range fun i ↦ (ms i).1)

  have hNp : N.localized' Rₚ S f = ⊤ := by
    rw [Submodule.localized'_span, eq_top_iff, ← b.span_eq, Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    have hu : IsUnit (algebraMap R Rₚ ((ms i).2 : R)) := IsLocalization.map_units Rₚ (ms i).2
    have key : (↑(hu.unit⁻¹) : Rₚ) • f (ms i).1 = b i := by
      rw [← hms i, Submonoid.smul_def, ← algebraMap_smul Rₚ ((ms i).2 : R) (b i), smul_smul,
        IsUnit.val_inv_mul, one_smul]
    rw [SetLike.mem_coe, ← key]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, ⟨i, rfl⟩, rfl⟩)

  have hsub : Subsingleton (LocalizedModule S (M ⧸ N)) :=
    (localized'_eq_top_iff_subsingleton S Rₚ f N).mp hNp
  obtain ⟨r, hr, hrN⟩ := LocalizedModule.exists_subsingleton_away (M := M ⧸ N) p.asIdeal
  refine ⟨r, hr, ?_⟩
  let A := Localization.Away r
  let fA : M →ₗ[R] LocalizedModule (Submonoid.powers r) M :=
    LocalizedModule.mkLinearMap (Submonoid.powers r) M
  have hNA : N.localized' A (Submonoid.powers r) fA = ⊤ :=
    (localized'_eq_top_iff_subsingleton (Submonoid.powers r) A fA N).mpr hrN

  let ψ : (Fin n → A) →ₗ[A] LocalizedModule (Submonoid.powers r) M :=
    Fintype.linearCombination A fun i ↦ fA (ms i).1
  have hψ : Function.Surjective ψ := by
    rw [← LinearMap.range_eq_top, Fintype.range_linearCombination, ← top_le_iff, ← hNA,
      Submodule.localized'_span, ← Set.range_comp]
    rfl

  have hrank :
      ∀ q : PrimeSpectrum A, rankAtStalk (LocalizedModule (Submonoid.powers r) M) q = n := by
    intro q
    rw [rankAtStalk_eq_of_equiv (LocalizedModule.equivTensorProduct (Submonoid.powers r) M),
      rankAtStalk_baseChange]
    exact h _
  exact finitePresentation_of_surjective_of_rankAtStalk_eq hrank ψ hψ

end mainProof

section main

variable {R : Type u} [CommRing R] {M : Type v} [AddCommGroup M] [Module R M]
  [Module.Finite R M] [Module.Flat R M] {n : ℕ}

theorem finitePresentation_of_rankAtStalk_eq (h : ∀ p : PrimeSpectrum R, rankAtStalk M p = n) :
    Module.FinitePresentation R M := by
  choose r hr hfp using exists_finitePresentation_away (M := M) h
  refine finitePresentation_of_localizationSpan (Set.range r) ?_ ?_
  · by_contra hne
    obtain ⟨m, hm, hle⟩ := Ideal.exists_le_maximal _ hne
    exact hr ⟨m, hm.isPrime⟩ (hle (Ideal.subset_span ⟨_, rfl⟩))
  · rintro ⟨_, p, rfl⟩
    exact hfp p

end main

end FPRank

theorem solution {R : Type u} [CommRing R]
    (M : Type v) [AddCommGroup M] [Module R M] [Module.Finite R M] [Module.Flat R M] (n : ℕ)
    (h : ∀ p : PrimeSpectrum R, Module.rankAtStalk M p = n) : Module.FinitePresentation R M :=
  FPRank.finitePresentation_of_rankAtStalk_eq h

end S_Module_finitePresentation_of_rankAtStalk_eq
end P2MW
export P2MW.S_Module_finitePresentation_of_rankAtStalk_eq (solution)
