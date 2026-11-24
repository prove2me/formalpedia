-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.PTIso.NineTransfer.exact_transfer
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T12:54:14.026035+00:00
-- url     : https://prove2.me/submissions/48c98be9-1954-46cc-85e1-d09fa7ea2a69

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_TemperedRepresentationTheory_GelfandSpectralNormalisation_NormalisedInvariants_PTConclAt
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_NineTermExactIff
import Definitions.Def_ReciprocityTheory_NeutralLocalFields_LocalFieldComparison_TransportA
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_PoitouTateSequenceTransport

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain Representation Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.Published GlobalTheory.Published.PoitouTate PositivityTheory.PoitouTateConclusion GlobalTheory.CompanionTheory.PTIso ReciprocityTheory.Neutral.Bridge
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.PTIso GlobalTheory.CompanionTheory.PTIso.NineTransfer
variable {R : Type*} [CommRing R]
namespace GlobalTheory.CompanionTheory.PTIso.NineTransfer
theorem _root_.solution {A A' B B' C C' : Type*}
    [AddCommGroup A] [Module R A] [AddCommGroup A'] [Module R A']
    [AddCommGroup B] [Module R B] [AddCommGroup B'] [Module R B']
    [AddCommGroup C] [Module R C] [AddCommGroup C'] [Module R C']
    (a : A' ≃ₗ[R] A) (b : B' ≃ₗ[R] B) (c : C' ≃ₗ[R] C)
    {f' : A' →ₗ[R] B'} {g' : B' →ₗ[R] C'} {f : A →ₗ[R] B} {g : B →ₗ[R] C}
    (h1 : ∀ x, f (a x) = b (f' x)) (h2 : ∀ y, g (b y) = c (g' y))
    (h : Function.Exact f' g') : Function.Exact f g := by
  intro y
  obtain ⟨y', rfl⟩ := b.surjective y
  rw [h2, LinearEquiv.map_eq_zero_iff, h y']
  constructor
  · rintro ⟨x', rfl⟩
    exact ⟨a x', h1 x'⟩
  · rintro ⟨x, hx⟩
    obtain ⟨x', rfl⟩ := a.surjective x
    exact ⟨x', b.injective (by rw [← h1, hx])⟩
end GlobalTheory.CompanionTheory.PTIso.NineTransfer
