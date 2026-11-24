-- Prove2me | solution 1 for GlobalTheory.T.ring_equiv_transports_residue
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T21:22:19.860581+00:00
-- url     : https://prove2.me/submissions/a6edba9d-adc7-4c69-a8c0-3203bbac4c28

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_RingEquivTransportsResidue
import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_TemperedRepresentationTheory_GelfandSpectralNormalisation_NormalisedInvariants_PTConclAt
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_NineTermExactIff
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_RingEquivTransportsResidueStatement
import Theorems.Thm_GlobalTheory_CompanionTheory_PTIso_Norm_isNormalised_transfer


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain Representation Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.Published GlobalTheory.Published.PoitouTate PositivityTheory.PoitouTateConclusion GlobalTheory.CompanionTheory.PTIso
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (F Ω F' Ω' : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] [Field F'] [NumberField F'] [Field Ω'] [Algebra F' Ω'] [IsAlgClosure F' Ω'] (e : F ≃+* F') (E : Ω ≃+* Ω'), (∀ x : F, E (algebraMap F Ω x) = algebraMap F' Ω' (e x)) → ∀ (Φ : G F Ω ≃ₜ* G F' Ω'), (∀ (σ : G F Ω) (x : Ω), Φ σ (E x) = E (σ x)) → ∀ (eO : 𝓞 F ≃+* 𝓞 F') (eV : HeightOneSpectrum (𝓞 F) ≃ HeightOneSpectrum (𝓞 F')), (∀ x : 𝓞 F, ((eO x : 𝓞 F') : F') = e (x : F)) → (∀ (v : HeightOneSpectrum (𝓞 F)) (x : 𝓞 F), x ∈ v.asIdeal ↔ eO x ∈ (eV v).asIdeal) → (∀ (v : HeightOneSpectrum (𝓞 F)) (x : 𝓞 F), x ∈ v.asIdeal ^ 2 ↔ eO x ∈ (eV v).asIdeal ^ 2) → (∀ v : HeightOneSpectrum (𝓞 F), normV (eV v) = normV v) → ∀ (l : ℕ) [Fact l.Prime] (r : ℕ), (∀ σ : G F Ω, cycMod F' Ω' l r (Φ σ) = cycMod F Ω l r σ) → ∀ (A : ValuationSubring Ω) (A' : ValuationSubring Ω'), (∀ x, E x ∈ A' ↔ x ∈ A) → (∀ σ : G F Ω, (σ ∈ Dec (F := F) A ↔ Φ σ ∈ Dec (F := F') A') ∧ (σ ∈ Inertia (F := F) A ↔ Φ σ ∈ Inertia (F := F') A') ∧ ∀ q : ℕ, IsFrob (F := F) A q σ ↔ IsFrob (F := F') A' q (Φ σ)) → ∀ (ζ : Ω) (v : HeightOneSpectrum (𝓞 F)) (iA : H2 (muLoc F l r A) →ₗ[ZMod (l ^ r)] ZMod (l ^ r)) (iA' : H2 (muLoc F' l r A') →ₗ[ZMod (l ^ r)] ZMod (l ^ r)), (∀ (z : Z2 (muLoc F l r A)) (z' : Z2 (muLoc F' l r A')), (∀ (g h : Dec (F := F) A) (g' h' : Dec (F := F') A'), (g' : G F' Ω') = Φ g → (h' : G F' Ω') = Φ h → z'.1 (g', h') = z.1 (g, h)) → iA' (Submodule.Quotient.mk z') = iA (Submodule.Quotient.mk z)) → IsNormalised ζ A v iA → IsNormalised (E ζ) A' (eV v) iA' := by
  first | exact @GlobalTheory.CompanionTheory.PTIso.Norm.isNormalised_transfer | exact GlobalTheory.CompanionTheory.PTIso.Norm.isNormalised_transfer | (intros; apply GlobalTheory.CompanionTheory.PTIso.Norm.isNormalised_transfer <;> assumption)
end _root_.GlobalTheory.T
