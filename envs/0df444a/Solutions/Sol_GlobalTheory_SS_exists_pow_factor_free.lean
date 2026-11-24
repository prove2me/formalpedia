-- Prove2me | solution 1 for GlobalTheory.SS.exists_pow_factor_free
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T20:23:19.891973+00:00
-- url     : https://prove2.me/submissions/90a357f3-78db-482b-adcf-17ac753e8298

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_OfDerivationFnOn
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_PlOrdSomeOfAssociated
import Definitions.Def_Development_AbelianVarietyTheory_Statements_SemistableTorsion_SemistableFin
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_DefectBounded

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.SS
open GlobalTheory GlobalTheory.SS
namespace GlobalTheory.SS
theorem _root_.solution {B S M M' : Type} [CommRing B] [CommRing S] [Algebra B S] (b : B)
    [IsLocalization (Submonoid.powers b) S] [AddCommGroup M] [Module B M] [Module.FinitePresentation B M]
    [AddCommGroup M'] [Module B M'] [Module S M'] [IsScalarTower B S M'] [Module.Projective S M']
    (f : M →ₗ[B] M') [IsLocalizedModule (Submonoid.powers b) f] :
    ∃ (c n : ℕ) (s : M →ₗ[B] (Fin n → B)) (t : (Fin n → B) →ₗ[B] M), t ∘ₗ s = b ^ c • LinearMap.id := by
  classical
  have : Module.FinitePresentation S M' := _root_.FinitePresentation.of_isBaseChange f
    ((isLocalizedModule_iff_isBaseChange (Submonoid.powers b) S f).mp inferInstance)
  obtain ⟨n, p, hp⟩ := Module.Finite.exists_fin' S M'
  obtain ⟨σ, hσ⟩ := Module.projective_lifting_property p LinearMap.id hp
  let eS := Finsupp.linearEquivFunOnFinite S S (Fin n)
  let eB := Finsupp.linearEquivFunOnFinite B B (Fin n)
  let ℓ : (Fin n →₀ B) →ₗ[B] (Fin n →₀ S) := Finsupp.mapRange.linearMap (Algebra.linearMap B S)
  let p' : (Fin n →₀ S) →ₗ[S] M' := p ∘ₗ eS.toLinearMap
  let σ' : M' →ₗ[S] (Fin n →₀ S) := eS.symm.toLinearMap ∘ₗ σ
  have hpσ : ∀ x, p' (σ' x) = x := fun x => by
    simpa [p', σ'] using LinearMap.congr_fun hσ x
  obtain ⟨h, s₁, hh⟩ := Module.FinitePresentation.exists_lift_of_isLocalizedModule
    (Submonoid.powers b) ℓ ((σ'.restrictScalars B) ∘ₗ f)
  obtain ⟨t, s₂, ht⟩ := Module.FinitePresentation.exists_lift_of_isLocalizedModule
    (Submonoid.powers b) f ((p'.restrictScalars B) ∘ₗ ℓ)
  have key : f ∘ₗ (t ∘ₗ h) = f ∘ₗ ((s₂ * s₁) • LinearMap.id) := by
    refine LinearMap.ext fun m => ?_
    have e1 : f (t (h m)) = (s₂ : B) • p' (ℓ (h m)) := by
      simpa [Submonoid.smul_def] using LinearMap.congr_fun ht (h m)
    have e2 : ℓ (h m) = (s₁ : B) • σ' (f m) := by
      simpa [Submonoid.smul_def] using LinearMap.congr_fun hh m
    have e3 : p' ((s₁ : B) • σ' (f m)) = (s₁ : B) • f m := by
      have := (p'.restrictScalars B).map_smul (s₁ : B) (σ' (f m))
      rw [LinearMap.coe_restrictScalars] at this
      rw [this, hpσ]
    rw [LinearMap.comp_apply, LinearMap.comp_apply, e1, e2, e3, LinearMap.comp_apply,
      LinearMap.smul_apply, LinearMap.id_apply, Submonoid.smul_def, map_smul, Submonoid.coe_mul,
      mul_smul]
  obtain ⟨s₃, hs₃⟩ :=
    Module.Finite.exists_smul_of_comp_eq_of_isLocalizedModule (Submonoid.powers b) f _ _ key
  obtain ⟨k₁, hk₁⟩ := s₁.2
  obtain ⟨k₂, hk₂⟩ := s₂.2
  obtain ⟨k₃, hk₃⟩ := s₃.2
  dsimp only at hk₁ hk₂ hk₃
  refine ⟨k₃ + (k₂ + k₁), n, eB.toLinearMap ∘ₗ h, ((s₃ : B) • t) ∘ₗ eB.symm.toLinearMap, ?_⟩
  refine LinearMap.ext fun m => ?_
  have hm := LinearMap.congr_fun hs₃ m
  rw [LinearMap.smul_apply, LinearMap.smul_apply, LinearMap.comp_apply, LinearMap.smul_apply,
    LinearMap.id_apply, Submonoid.smul_def, Submonoid.smul_def, Submonoid.smul_def,
    Submonoid.coe_mul] at hm
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply]
  rw [LinearMap.smul_apply, LinearMap.smul_apply, LinearMap.id_apply, hm,
    ← hk₁, ← hk₂, ← hk₃, pow_add, pow_add, mul_smul, mul_smul, mul_smul]
end GlobalTheory.SS
