-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.PTIso.Norm.isNormalised_transfer
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T12:55:10.770168+00:00
-- url     : https://prove2.me/submissions/6c780b0f-5aa0-44ea-9a8f-f123b2aa81bd

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_TemperedRepresentationTheory_GelfandSpectralNormalisation_NormalisedInvariants_PTConclAt
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_NineTermExactIff
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_RingEquivTransportsResidue

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain Representation Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.Published GlobalTheory.Published.PoitouTate PositivityTheory.PoitouTateConclusion GlobalTheory.CompanionTheory.PTIso
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.PTIso GlobalTheory.CompanionTheory.PTIso.Norm
namespace GlobalTheory.CompanionTheory.PTIso.Norm
theorem _root_.solution : ∀ (F Ω F' Ω' : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] [Field F'] [NumberField F'] [Field Ω'] [Algebra F' Ω'] [IsAlgClosure F' Ω'] (e : F ≃+* F') (E : Ω ≃+* Ω'), (∀ x : F, E (algebraMap F Ω x) = algebraMap F' Ω' (e x)) → ∀ (Φ : G F Ω ≃ₜ* G F' Ω'), (∀ (σ : G F Ω) (x : Ω), Φ σ (E x) = E (σ x)) → ∀ (eO : 𝓞 F ≃+* 𝓞 F') (eV : HeightOneSpectrum (𝓞 F) ≃ HeightOneSpectrum (𝓞 F')), (∀ x : 𝓞 F, ((eO x : 𝓞 F') : F') = e (x : F)) → (∀ (v : HeightOneSpectrum (𝓞 F)) (x : 𝓞 F), x ∈ v.asIdeal ↔ eO x ∈ (eV v).asIdeal) → (∀ (v : HeightOneSpectrum (𝓞 F)) (x : 𝓞 F), x ∈ v.asIdeal ^ 2 ↔ eO x ∈ (eV v).asIdeal ^ 2) → (∀ v : HeightOneSpectrum (𝓞 F), normV (eV v) = normV v) → ∀ (l : ℕ) [Fact l.Prime] (r : ℕ), (∀ σ : G F Ω, cycMod F' Ω' l r (Φ σ) = cycMod F Ω l r σ) → ∀ (A : ValuationSubring Ω) (A' : ValuationSubring Ω'), (∀ x, E x ∈ A' ↔ x ∈ A) → (∀ σ : G F Ω, (σ ∈ Dec (F := F) A ↔ Φ σ ∈ Dec (F := F') A') ∧ (σ ∈ Inertia (F := F) A ↔ Φ σ ∈ Inertia (F := F') A') ∧ ∀ q : ℕ, IsFrob (F := F) A q σ ↔ IsFrob (F := F') A' q (Φ σ)) → ∀ (ζ : Ω) (v : HeightOneSpectrum (𝓞 F)) (iA : H2 (muLoc F l r A) →ₗ[ZMod (l ^ r)] ZMod (l ^ r)) (iA' : H2 (muLoc F' l r A') →ₗ[ZMod (l ^ r)] ZMod (l ^ r)), (∀ (z : Z2 (muLoc F l r A)) (z' : Z2 (muLoc F' l r A')), (∀ (g h : Dec (F := F) A) (g' h' : Dec (F := F') A'), (g' : G F' Ω') = Φ g → (h' : G F' Ω') = Φ h → z'.1 (g', h') = z.1 (g, h)) → iA' (Submodule.Quotient.mk z') = iA (Submodule.Quotient.mk z)) → IsNormalised ζ A v iA → IsNormalised (E ζ) A' (eV v) iA' := by
  intro F Ω F' Ω' _ _ _ _ _ _ _ _ _ _ e E hE Φ hΦ eO eV heO hI hI2 hN l _ r hc A A' hA hD ζ v iA iA'
    hrel hn ϖ' y' κ' χ' z' h1 h2 h3 h4 h5 h6 h7 h8
  let eD : Dec (F := F) A ≃ₜ* Dec (F := F') A' :=
    subgroupIso Φ (Dec (F := F) A) (Dec (F := F') A') (fun a => (hD a).1)
  have hcoe : ∀ g : Dec (F := F) A, ((eD g : Dec (F := F') A') : G F' Ω') = Φ g := fun _ => rfl
  let zz : Z2 (muLoc F l r A) :=
    compatiblePairCocycles2 (muLoc F' l r A') (muLoc F l r A) (eD : Dec (F := F) A →* Dec (F := F') A')
      eD.continuous LinearMap.id continuous_id
      (fun g m => by
        show ((cycMod F' Ω' l r (Φ g) : (ZMod (l ^ r))ˣ) : ZMod (l ^ r)) * m =
          ((cycMod F Ω l r g : (ZMod (l ^ r))ˣ) : ZMod (l ^ r)) * m
        rw [hc]) z'
  have hEy : E (E.symm y') = y' := E.apply_symm_apply y'
  have hϖ : eO (eO.symm ϖ') = ϖ' := eO.apply_symm_apply ϖ'
  have key : iA (Submodule.Quotient.mk zz) = 1 := by
    refine hn (eO.symm ϖ') (E.symm y') (fun g => κ' (eD g)) (fun g => χ' (eD g)) zz
      ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
    · rw [hI, hϖ]; exact h1
    · rw [hI2, hϖ]; exact h2
    · apply E.injective
      rw [map_pow, hEy, h3, hE, ← heO, hϖ]
    · intro g
      apply E.injective
      have h := h4 (eD g)
      rw [← hΦ, hEy, ← hcoe, h, map_mul, map_pow, hEy]
    · intro g h
      show χ' (eD (g * h)) = χ' (eD g) + χ' (eD h)
      rw [map_mul, h5]
    · intro g hg
      exact h6 (eD g) ((hD (g : G F Ω)).2.1.1 hg)
    · intro g hg
      refine h7 (eD g) ?_
      rw [hN]
      exact ((hD (g : G F Ω)).2.2 _).1 hg
    · intro g h
      exact h8 (eD g) (eD h)
  rw [hrel zz z' ?_]
  · exact key
  · intro g h g' h' hg hh
    have e1 : g' = eD g := Subtype.ext hg
    have e2 : h' = eD h := Subtype.ext hh
    subst e1 e2
    rfl
end GlobalTheory.CompanionTheory.PTIso.Norm
