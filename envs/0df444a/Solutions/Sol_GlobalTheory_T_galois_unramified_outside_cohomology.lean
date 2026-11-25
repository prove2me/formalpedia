-- Prove2me | solution 1 for GlobalTheory.T.galois_unramified_outside_cohomology
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T18:21:02.706926+00:00
-- url     : https://prove2.me/submissions/ab465568-8892-46d1-967c-eae81ea3e1cc

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_GaloisUnramifiedOutsideCohomology
import Definitions.Def_ReciprocityTheory_Hypotheses_GalCoh
import Definitions.Def_GroundTheory_ProfiniteCohomology_RestrictedRamification_IsUnramifiedOutsideIffLeMaxUnramifiedOutside
import Definitions.Def_GroundTheory_ProfiniteCohomology_ContinuousCochains
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_GaloisUnramifiedOutsideCohomologyStatement
import Theorems.Thm_GlobalTheory_CompanionTheory_Glob_InertiaLift_fixingSubgroup_le_NS


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
theorem _root_.solution : ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (S : Set (HeightOneSpectrum (𝓞 F))), (maxUnramifiedOutside F Ω S).fixingSubgroup ≤ NS Ω S := by
  first | exact @GlobalTheory.CompanionTheory.Glob.InertiaLift.fixingSubgroup_le_NS | exact GlobalTheory.CompanionTheory.Glob.InertiaLift.fixingSubgroup_le_NS | (intros; apply GlobalTheory.CompanionTheory.Glob.InertiaLift.fixingSubgroup_le_NS <;> assumption)
end _root_.GlobalTheory.T
