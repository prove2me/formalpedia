-- Prove2me | solution 1 for IsDedekindDomain.HeightOneSpectrum.exists_tameCharacter_inertia_maxUnramified_of_pole
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-11-15T06:32:46.85468+00:00
-- url     : https://prove2.me/submissions/3a57f750-3dd7-4eb1-92a4-eaa28f6e448b

import Mathlib
import Definitions.Def_RPLib_S4_TameInertia

set_option autoImplicit false

namespace TameInertiaSol

open RamanujanPetersson

theorem unram_iff (A K : Type) [CommRing A] [Field K] [Algebra A K]
    (L : IntermediateField K (AlgebraicClosure K)) :
    IsUnramifiedSub A K L ↔ ∀ P : Ideal (integralClosure A L), P.IsPrime → ∀ σ : L ≃ₐ[K] L,
      (∀ b : integralClosure A L, ∃ c ∈ P, (c : L) = σ b - b) → σ = 1 := by
  refine forall_congr' fun P => forall_congr' fun _ => ?_
  rw [Subgroup.eq_bot_iff_forall]
  refine forall_congr' fun σ => imp_congr_left ?_
  rw [AddSubgroup.mem_inertia]
  refine forall_congr' fun b => ⟨fun h => ⟨_, h, rfl⟩, fun ⟨c, hc, he⟩ => ?_⟩
  have : c = σ • b - b := Subtype.ext he
  rwa [← this]

end TameInertiaSol

open RamanujanPetersson CurveCoh TameInertia in
theorem solution
    (A K : Type) [CommRing A] [IsDomain A] [Field K] [Algebra A K] [IsFractionRing A K]
    (R0 : Type) [CommRing R0] [IsDedekindDomain R0] [Algebra R0 K] [IsFractionRing R0 K]
    [Ring.HasFiniteQuotients R0] (p : ℕ) [Fact p.Prime] [CharP K p]
    (KU : IntermediateField K (AlgebraicClosure K))
    (hKU : KU = ⨆ L : {L : IntermediateField K (AlgebraicClosure K) //
        FiniteDimensional K L ∧ IsGalois K L ∧
        ∀ P : Ideal (integralClosure A L), P.IsPrime → ∀ σ : L ≃ₐ[K] L,
          (∀ b : integralClosure A L, ∃ c ∈ P, (c : L) = σ b - b) → σ = 1}, L.1)
    (Q : Ideal (integralClosure R0 KU)) [Q.IsPrime] (hQ : Q ≠ ⊥)
    (I : Subgroup (KU ≃ₐ[K] KU))
    (hI : ∀ σ : KU ≃ₐ[K] KU, σ ∈ I ↔ ∀ b : integralClosure R0 KU, ∃ c ∈ Q, (c : KU) = σ b - b)
    (N : ℕ) [NeZero N] (hNA : IsUnit (N : A)) (hNR : IsUnit (N : R0))
    (ζ : KU) (hζ : IsPrimitiveRoot ζ N) (hζI : ∀ σ ∈ I, σ ζ = ζ)
    (x : IsDedekindDomain.HeightOneSpectrum R0)
    (hx : x.asIdeal = Q.comap (algebraMap R0 (integralClosure R0 KU)))
    (a : A) (ha : 1 < x.valuation K (algebraMap A K a)) :
    ∃ θ : I → ZMod N, ∃ σ₀ : I,
      IsLocallyConstant θ ∧ (∀ σ τ : I, θ (σ * τ) = θ σ + θ τ) ∧ θ σ₀ = 1 ∧
      (∀ φ : KU ≃ₐ[K] KU, (∀ b : integralClosure R0 KU, (∃ c ∈ Q, (c : KU) = φ b) ↔ b ∈ Q) →
        ∀ w : ZMod N, φ ζ = ζ ^ w.val →
        ∀ σ τ : I, (τ : KU ≃ₐ[K] KU) = φ⁻¹ * σ * φ → θ σ = w * θ τ) ∧
      ∀ (M : Type) [AddCommGroup M], (∀ m : M, N • m = 0) →
        (∀ χ : I → M, IsLocallyConstant χ → (∀ σ τ : I, χ (σ * τ) = χ σ + χ τ) →
          ∀ σ : I, χ σ = (θ σ).val • χ σ₀) ∧
        ∀ m : M, IsLocallyConstant (fun σ : I => (θ σ).val • m) ∧
          (∀ σ τ : I, (θ (σ * τ)).val • m = (θ σ).val • m + (θ τ).val • m) ∧
          (θ σ₀).val • m = m := by
  have hset : unramSet A K = {L : IntermediateField K (AlgebraicClosure K) |
      FiniteDimensional K L ∧ IsGalois K L ∧
        ∀ P : Ideal (integralClosure A L), P.IsPrime → ∀ σ : L ≃ₐ[K] L,
          (∀ b : integralClosure A L, ∃ c ∈ P, (c : L) = σ b - b) → σ = 1} := by
    ext L
    exact and_congr Iff.rfl (and_congr Iff.rfl (TameInertiaSol.unram_iff A K L))
  have hKU' : KU = maxUnram A K := by
    rw [hKU, maxUnram, hset]
    rfl
  subst hKU'
  have hI' : I = Q.inertia (Pi1 A K) := by
    ext σ
    rw [hI, AddSubgroup.mem_inertia]
    refine forall_congr' fun b => ⟨fun ⟨c, hc, he⟩ => ?_, fun h => ⟨_, h, rfl⟩⟩
    have : c = σ • b - b := Subtype.ext he
    rwa [← this]
  subst hI'
  obtain ⟨θ, σ₀, hc, hm, h1, htw, hcoef⟩ :=
    TameInertia.tame_inertia (p := p) ⟨‹Q.IsPrime›, hQ⟩ hNA hNR hζ hζI x hx ha
  refine ⟨θ, σ₀, hc, hm, h1, fun φ hφ w hw σ τ hτ => ?_, hcoef⟩
  have hφ' : ∀ b : proChart A K R0, φ • b ∈ Q ↔ b ∈ Q := fun b => by
    rw [← hφ b]
    refine ⟨fun h => ⟨_, h, rfl⟩, fun ⟨c, hc, he⟩ => ?_⟩
    have : c = φ • b := Subtype.ext he
    rwa [← this]
  obtain rfl : τ = ⟨φ⁻¹ * σ.1 * φ, inertia_conj hφ' σ.2⟩ := Subtype.ext hτ
  exact htw φ hφ' w hw σ.1 σ.2
