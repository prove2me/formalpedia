-- Prove2me | solution 1 for GlobalTheory.T.normal_subgroup_le_unramified_fixing
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T18:26:52.359346+00:00
-- url     : https://prove2.me/submissions/4e17e10c-6db1-4b26-8499-14e53071c329

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_NormalSubgroupLeUnramifiedFixing
import Definitions.Def_ReciprocityTheory_Hypotheses_GalCoh
import Definitions.Def_GroundTheory_ProfiniteCohomology_RestrictedRamification_IsUnramifiedOutsideIffLeMaxUnramifiedOutside
import Definitions.Def_GroundTheory_ProfiniteCohomology_ContinuousCochains
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_NormalSubgroupLeUnramifiedFixingStatement
import Theorems.Thm_GlobalTheory_CompanionTheory_GlobalFiniteness_NS_le_fixingSubgroup


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
theorem _root_.solution : ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (S : Set (HeightOneSpectrum (𝓞 F))), NS Ω S ≤ (maxUnramifiedOutside F Ω S).fixingSubgroup := by
  first | exact @GlobalTheory.CompanionTheory.GlobalFiniteness.NS_le_fixingSubgroup | exact GlobalTheory.CompanionTheory.GlobalFiniteness.NS_le_fixingSubgroup | (intros; apply GlobalTheory.CompanionTheory.GlobalFiniteness.NS_le_fixingSubgroup <;> assumption)
end _root_.GlobalTheory.T
