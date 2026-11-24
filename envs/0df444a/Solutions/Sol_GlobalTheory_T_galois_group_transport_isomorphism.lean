-- Prove2me | solution 1 for GlobalTheory.T.galois_group_transport_isomorphism
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T21:10:55.391161+00:00
-- url     : https://prove2.me/submissions/9db0f3d4-674c-4120-99c8-451c007af5cc

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_GaloisGroupTransportIsomorphism
import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_TemperedRepresentationTheory_GelfandSpectralNormalisation_NormalisedInvariants_PTConclAt
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_NineTermExactIff
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_GaloisGroupTransportIsomorphismStatement
import Theorems.Thm_GlobalTheory_CompanionTheory_PTIso_exists_galContinuousMulEquiv


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
theorem _root_.solution : ∀ (F Ω F' Ω' : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] [Field F'] [NumberField F'] [Field Ω'] [Algebra F' Ω'] [IsAlgClosure F' Ω'] (e : F ≃+* F') (E : Ω ≃+* Ω'), (∀ x : F, E (algebraMap F Ω x) = algebraMap F' Ω' (e x)) → ∃ Φ : G F Ω ≃ₜ* G F' Ω', ∀ (σ : G F Ω) (x : Ω), Φ σ (E x) = E (σ x) := by
  first | exact @GlobalTheory.CompanionTheory.PTIso.exists_galContinuousMulEquiv | exact GlobalTheory.CompanionTheory.PTIso.exists_galContinuousMulEquiv | (intros; apply GlobalTheory.CompanionTheory.PTIso.exists_galContinuousMulEquiv <;> assumption)
end _root_.GlobalTheory.T
