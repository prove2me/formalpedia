-- Prove2me | solution 1 for Leopoldt.continuous_semilocalGaloisAut
-- status  : ACCEPTED   (prove)
-- author  : @xuanji
-- created : 2026-09-27T02:50:51.431462+00:00
-- url     : https://prove2.me/submissions/ebeced01-e3f0-4add-8e00-974ee4e1a790

import Definitions.Def_LeopoldtGaloisAction

open NumberField IsDedekindDomain Leopoldt Leopoldt.GaloisAction

namespace GALProofs

section Local

variable {K : Type*} [Field K] [NumberField K]

theorem continuous_localUnitsEquiv (σ : K ≃ₐ[ℚ] K) {v w : HeightOneSpectrum (𝓞 K)}
    (h : ∀ x : K, w.valuation K (σ x) = v.valuation K x) :
    Continuous (localUnitsEquiv σ h) := by
  have hc : Continuous (localIntegersEquiv σ h) :=
    continuous_induced_rng.2 ((continuous_localRingEquiv σ h).comp continuous_subtype_val)
  show Continuous (Units.map (localIntegersEquiv σ h).toMonoidHom)
  rw [Units.continuous_iff]
  exact ⟨hc.comp Units.continuous_val, hc.comp (Units.continuous_val.comp continuous_inv)⟩

theorem localRingEquiv_comp (σ τ : K ≃ₐ[ℚ] K) {u v w : HeightOneSpectrum (𝓞 K)}
    (hτ : ∀ x : K, v.valuation K (τ x) = u.valuation K x)
    (hσ : ∀ x : K, w.valuation K (σ x) = v.valuation K x)
    (hστ : ∀ x : K, w.valuation K ((σ * τ) x) = u.valuation K x)
    (y : u.adicCompletion K) :
    localRingEquiv σ hσ (localRingEquiv τ hτ y) = localRingEquiv (σ * τ) hστ y := by
  have := (HeightOneSpectrum.denseRange_algebraMap K u).equalizer
    ((continuous_localRingEquiv σ hσ).comp (continuous_localRingEquiv τ hτ))
    (continuous_localRingEquiv (σ * τ) hστ) (funext fun k => ?_)
  · exact congrFun this y
  show localRingEquiv σ hσ (localRingEquiv τ hτ (k : u.adicCompletion K))
    = localRingEquiv (σ * τ) hστ (k : u.adicCompletion K)
  rw [localRingEquiv_coe, localRingEquiv_coe, localRingEquiv_coe]
  rfl

theorem localRingEquiv_one {v : HeightOneSpectrum (𝓞 K)}
    (h : ∀ x : K, v.valuation K ((1 : K ≃ₐ[ℚ] K) x) = v.valuation K x)
    (y : v.adicCompletion K) : localRingEquiv 1 h y = y := by
  have := (HeightOneSpectrum.denseRange_algebraMap K v).equalizer
    (continuous_localRingEquiv 1 h) continuous_id (funext fun k => ?_)
  · exact congrFun this y
  show localRingEquiv 1 h (k : v.adicCompletion K) = (k : v.adicCompletion K)
  rw [localRingEquiv_coe]
  rfl

end Local

section Global

set_option linter.unusedSectionVars false

variable (p : ℕ) [Fact p.Prime] (K : Type*) [Field K] [NumberField K]

theorem transport (ρ : K ≃ₐ[ℚ] K) (w : PrimesOver p K) (x : SemilocalUnits p K)
    (v₁ v₂ : PrimesOver p K) (e : v₁ = v₂)
    (h₁ : ∀ k : K, w.1.valuation K (ρ k) = v₁.1.valuation K k)
    (h₂ : ∀ k : K, w.1.valuation K (ρ k) = v₂.1.valuation K k) :
    localUnitsEquiv ρ h₁ (x v₁) = localUnitsEquiv ρ h₂ (x v₂) := by
  subst e; rfl

theorem continuous_semilocalGaloisAut (σ : K ≃ₐ[ℚ] K) :
    Continuous (semilocalGaloisAut p K σ) :=
  continuous_pi fun _ => (continuous_localUnitsEquiv σ _).comp (continuous_apply _)

theorem semilocalGaloisAut_diagonalUnits (σ : K ≃ₐ[ℚ] K) (ε : (𝓞 K)ˣ) :
    semilocalGaloisAut p K σ (diagonalUnits p K ε)
      = diagonalUnits p K (Units.map (RingOfIntegers.mapRingHom (σ : K →+* K)).toMonoidHom ε) := by
  funext w
  apply Units.ext
  apply Subtype.ext
  show localRingEquiv σ _ (((ε : 𝓞 K) : K) : _) = (((RingOfIntegers.mapRingHom (σ : K →+* K)
    (ε : 𝓞 K) : 𝓞 K) : K) : w.1.adicCompletion K)
  rw [localRingEquiv_coe]
  rfl

theorem semilocalGaloisAut_mul (σ τ : K ≃ₐ[ℚ] K) :
    semilocalGaloisAut p K (σ * τ) = (semilocalGaloisAut p K τ).trans (semilocalGaloisAut p K σ) := by
  refine MulEquiv.ext fun x => funext fun w => ?_
  have e : (primesOverPerm p K τ).symm ((primesOverPerm p K σ).symm w)
      = (primesOverPerm p K (σ * τ)).symm w := by
    apply Subtype.ext
    apply HeightOneSpectrum.ext
    ext a
    rfl
  have h' : ∀ k : K, w.1.valuation K ((σ * τ) k)
      = ((primesOverPerm p K τ).symm ((primesOverPerm p K σ).symm w)).1.valuation K k := by
    intro k
    rw [AlgEquiv.mul_apply, valuation_primesOverPerm_symm p K σ,
      valuation_primesOverPerm_symm p K τ]
  show _ = semilocalGaloisAut p K σ (semilocalGaloisAut p K τ x) w
  rw [semilocalGaloisAut_apply, semilocalGaloisAut_apply]
  have hcomp : localUnitsEquiv σ (valuation_primesOverPerm_symm p K σ w)
      (semilocalGaloisAut p K τ x ((primesOverPerm p K σ).symm w))
      = localUnitsEquiv (σ * τ) h'
          (x ((primesOverPerm p K τ).symm ((primesOverPerm p K σ).symm w))) := by
    rw [semilocalGaloisAut_apply]
    apply Units.ext
    apply Subtype.ext
    exact localRingEquiv_comp σ τ _ _ _ _
  rw [hcomp]
  exact (transport p K (σ * τ) w x _ _ e h' _).symm

theorem semilocalGaloisAut_one : semilocalGaloisAut p K 1 = MulEquiv.refl _ := by
  refine MulEquiv.ext fun x => funext fun w => ?_
  have e : (primesOverPerm p K 1).symm w = w := by
    apply Subtype.ext
    apply HeightOneSpectrum.ext
    ext a
    rfl
  have h' : ∀ k : K, w.1.valuation K ((1 : K ≃ₐ[ℚ] K) k) = w.1.valuation K k := fun _ => rfl
  rw [semilocalGaloisAut_apply, transport p K 1 w x _ _ e _ h']
  show _ = x w
  apply Units.ext
  apply Subtype.ext
  exact localRingEquiv_one h' _

theorem exists_monoidHom_mulAut :
    ∃ φ : (K ≃ₐ[ℚ] K) →* MulAut (SemilocalUnits p K),
      ∀ σ, φ σ = semilocalGaloisAut p K σ :=
  ⟨{ toFun := semilocalGaloisAut p K
     map_one' := semilocalGaloisAut_one p K
     map_mul' := fun σ τ => semilocalGaloisAut_mul p K σ τ }, fun _ => rfl⟩

theorem semilocalGaloisAut_mem_unitClosure (σ : K ≃ₐ[ℚ] K) {x : SemilocalUnits p K}
    (hx : x ∈ unitClosure p K) : semilocalGaloisAut p K σ x ∈ unitClosure p K := by
  simp only [unitClosure, Subgroup.mem_iInf] at hx ⊢
  intro n
  obtain ⟨a, ha, b, hb, hab⟩ := Subgroup.mem_sup.1 (hx n)
  obtain ⟨ε, hε⟩ := ha
  obtain ⟨u, hu⟩ := hb
  refine Subgroup.mem_sup.2
    ⟨diagonalUnits p K (Units.map (RingOfIntegers.mapRingHom (σ : K →+* K)).toMonoidHom ε),
      ⟨_, rfl⟩, powMonoidHom (p ^ (n + 1)) (semilocalGaloisAut p K σ u), ⟨_, rfl⟩, ?_⟩
  rw [← semilocalGaloisAut_diagonalUnits p K σ ε]
  show semilocalGaloisAut p K σ (diagonalUnits p K ε) * (semilocalGaloisAut p K σ u) ^ (p ^ (n + 1)) = _
  rw [← map_pow, ← map_mul, ← hab, ← hε, ← hu]
  rfl

end Global

end GALProofs

open NumberField in
theorem solution (p : ℕ) [Fact p.Prime] (K : Type*) [Field K] [NumberField K] (σ : K ≃ₐ[ℚ] K) :
    Continuous (Leopoldt.semilocalGaloisAut p K σ) :=
  GALProofs.continuous_semilocalGaloisAut p K σ
