-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.GlobalFiniteness.mem_cutPrime_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T02:34:07.745025+00:00
-- url     : https://prove2.me/submissions/46aa10ca-a3f0-4962-a394-f00f4f19d2f8

import Mathlib
import Definitions.Def_ReciprocityTheory_Hypotheses_GalCoh
import Definitions.Def_GroundTheory_ProfiniteCohomology_RestrictedRamification_IsUnramifiedOutsideIffLeMaxUnramifiedOutside
import Definitions.Def_GroundTheory_ProfiniteCohomology_ContinuousCochains
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_NormalSubgroupLeUnramifiedFixing

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain CategoryTheory GroundTheory.ProfCoh ReciprocityTheory.Gal Formalism.ConjugateSelfDual
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.GlobalFiniteness
variable {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω]
namespace GlobalTheory.CompanionTheory.GlobalFiniteness
theorem _root_.solution (A : ValuationSubring Ω) (M : IntermediateField F Ω) (z : 𝓞 M) :
    z ∈ cutPrime A M ↔ A.valuation ((z : M) : Ω) < 1 := by
  rw [cutPrime, Ideal.mem_comap, ValuationSubring.valuation_lt_one_iff]
  rfl
end GlobalTheory.CompanionTheory.GlobalFiniteness
