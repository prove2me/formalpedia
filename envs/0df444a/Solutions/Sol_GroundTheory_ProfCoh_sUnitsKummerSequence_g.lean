-- Prove2me | solution 1 for GroundTheory.ProfCoh.sUnitsKummerSequence_g
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-27T04:49:57.643966+00:00
-- url     : https://prove2.me/submissions/e100ec7e-29c5-4d98-92c3-b69cf7d43000

import Mathlib
import Definitions.Def_GroundTheory_ProfiniteCohomology_GaloisModules_Discrete
import Definitions.Def_GroundTheory_ProfiniteCohomology_GaloisCohomology_UnitsInflationCochainsFHomApply
import Definitions.Def_GroundTheory_ProfiniteCohomology_RestrictedRamification_MaxUnramifiedOutside
import Definitions.Def_GroundTheory_ProfiniteCohomology_RestrictedRamification_SUnitsDefs

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.ProfCoh
open NumberField IsDedekindDomain CategoryTheory
universe u
variable {F : Type u} [Field F] [NumberField F] (S : Set (HeightOneSpectrum (𝓞 F)))
variable (E : Type u) [Field E] [Algebra F E]
variable {S E}
variable (S E)
variable (n : ℕ) [NeZero n]
namespace GroundTheory.ProfCoh
theorem _root_.solution : (sUnitsKummerSequence S E n).g = n • 𝟙 (galSUnits S E) :=
  rfl
end GroundTheory.ProfCoh
