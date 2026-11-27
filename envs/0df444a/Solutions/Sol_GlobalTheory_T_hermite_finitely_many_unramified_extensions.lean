-- Prove2me | solution 1 for GlobalTheory.T.hermite_finitely_many_unramified_extensions
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-27T04:33:46.264067+00:00
-- url     : https://prove2.me/submissions/ac444676-9da3-4fde-bc8c-31efe80fffec

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_HermiteFinitelyManyUnramifiedExtensions
import Definitions.Def_ReciprocityTheory_Hypotheses_GalCoh
import Definitions.Def_GroundTheory_ProfiniteCohomology_RestrictedRamification_IsUnramifiedOutsideIffLeMaxUnramifiedOutside
import Definitions.Def_GroundTheory_ProfiniteCohomology_ContinuousCochains
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_HermiteFinitelyManyUnramifiedExtensionsStatement
import Theorems.Thm_GlobalTheory_CompanionTheory_HermiteMinkowski_finite_unramified_bounded_degree


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain CategoryTheory GroundTheory.ProfCoh ReciprocityTheory.Gal Formalism.ConjugateSelfDual
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (S : Finset (HeightOneSpectrum (𝓞 F))) (N : ℕ), {E : IntermediateField F Ω | FiniteDimensional F E ∧ IsUnramifiedOutside (S : Set (HeightOneSpectrum (𝓞 F))) E ∧ Module.finrank F E ≤ N}.Finite := by
  first | exact @GlobalTheory.CompanionTheory.HermiteMinkowski.finite_unramified_bounded_degree | exact GlobalTheory.CompanionTheory.HermiteMinkowski.finite_unramified_bounded_degree | (intros; apply GlobalTheory.CompanionTheory.HermiteMinkowski.finite_unramified_bounded_degree <;> assumption)
end _root_.GlobalTheory.T
