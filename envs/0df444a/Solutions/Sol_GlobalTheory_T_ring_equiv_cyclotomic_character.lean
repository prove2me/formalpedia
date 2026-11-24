-- Prove2me | solution 1 for GlobalTheory.T.ring_equiv_cyclotomic_character
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T21:22:16.130139+00:00
-- url     : https://prove2.me/submissions/e7aad6b2-73a2-4a35-bf22-1cbd7b069f61

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_RingEquivCyclotomicCharacter
import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_TemperedRepresentationTheory_GelfandSpectralNormalisation_NormalisedInvariants_PTConclAt
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_NineTermExactIff
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_RingEquivCyclotomicCharacterStatement
import Theorems.Thm_GlobalTheory_CompanionTheory_PTIso_cycMod_intrinsic


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
theorem _root_.solution : ∀ (F Ω F' Ω' : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] [Field F'] [NumberField F'] [Field Ω'] [Algebra F' Ω'] [IsAlgClosure F' Ω'] (e : F ≃+* F') (E : Ω ≃+* Ω'), (∀ x : F, E (algebraMap F Ω x) = algebraMap F' Ω' (e x)) → ∀ (Φ : G F Ω ≃ₜ* G F' Ω'), (∀ (σ : G F Ω) (x : Ω), Φ σ (E x) = E (σ x)) → ∀ (l : ℕ) [Fact l.Prime] (r : ℕ) (σ : G F Ω), cycMod F' Ω' l r (Φ σ) = cycMod F Ω l r σ := by
  first | exact @GlobalTheory.CompanionTheory.PTIso.cycMod_intrinsic | exact GlobalTheory.CompanionTheory.PTIso.cycMod_intrinsic | (intros; apply GlobalTheory.CompanionTheory.PTIso.cycMod_intrinsic <;> assumption)
end _root_.GlobalTheory.T
