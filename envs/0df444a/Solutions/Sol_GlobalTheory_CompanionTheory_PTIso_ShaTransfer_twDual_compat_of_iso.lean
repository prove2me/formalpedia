-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.PTIso.ShaTransfer.twDual_compat_of_iso
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T12:55:18.384688+00:00
-- url     : https://prove2.me/submissions/ad32c76f-7b9b-4f85-9fde-17eea54e21ec

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_TemperedRepresentationTheory_GelfandSpectralNormalisation_NormalisedInvariants_PTConclAt
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_NineTermExactIff
import Definitions.Def_ReciprocityTheory_NeutralLocalFields_LocalFieldComparison_TransportA
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_TateShafarevichTransport

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain Representation Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.Published GlobalTheory.Published.PoitouTate
  PositivityTheory.PoitouTateConclusion GlobalTheory.CompanionTheory.PTIso ReciprocityTheory.Neutral.Bridge
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.PTIso GlobalTheory.CompanionTheory.PTIso.ShaTransfer
namespace GlobalTheory.CompanionTheory.PTIso.ShaTransfer
theorem _root_.solution {R Γ Γ' M : Type} [CommRing R] [Group Γ] [TopologicalSpace Γ]
    [Group Γ'] [TopologicalSpace Γ'] [AddCommGroup M] [Module R M]
    (χ : Γ →* Rˣ) (χ' : Γ' →* Rˣ) (ρ : Representation R Γ M) (ρ' : Representation R Γ' M)
    (eG : Γ ≃ₜ* Γ') (hχ : ∀ g, χ' (eG g) = χ g) (hρ : ∀ g m, ρ' (eG g) m = ρ g m) :
    ∀ g ψ, twDual χ' ρ' (eG g) ψ = twDual χ ρ g ψ := by
  intro g ψ
  ext m
  rw [twDual_apply, twDual_apply, hχ, ← map_inv, hρ]
end GlobalTheory.CompanionTheory.PTIso.ShaTransfer
