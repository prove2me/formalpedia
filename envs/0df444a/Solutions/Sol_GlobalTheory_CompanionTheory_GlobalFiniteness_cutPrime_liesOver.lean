-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.GlobalFiniteness.cutPrime_liesOver
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T03:02:15.934544+00:00
-- url     : https://prove2.me/submissions/a3c63855-b34e-4345-9cba-401ffbb17f52

import Mathlib
import Definitions.Def_ReciprocityTheory_Hypotheses_GalCoh
import Definitions.Def_GroundTheory_ProfiniteCohomology_RestrictedRamification_IsUnramifiedOutsideIffLeMaxUnramifiedOutside
import Definitions.Def_GroundTheory_ProfiniteCohomology_ContinuousCochains
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_NormalSubgroupLeUnramifiedFixing
import Theorems.Thm_GlobalTheory_CompanionTheory_GlobalFiniteness_mem_cutPrime_iff

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
theorem _root_.solution {A : ValuationSubring Ω} {v : HeightOneSpectrum (𝓞 F)}
    (hA : IsPlaceOver A v) (M : IntermediateField F Ω) : (cutPrime A M).LiesOver v.asIdeal := by
  constructor
  ext x
  rw [Ideal.under_def, Ideal.mem_comap, mem_cutPrime_iff, ← hA x]
  rfl
end GlobalTheory.CompanionTheory.GlobalFiniteness
