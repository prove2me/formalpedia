-- Prove2me | solution 1 for GroundTheory.ProfCoh.mem_sUnitsOf
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T00:24:46.97351+00:00
-- url     : https://prove2.me/submissions/89177997-a5c2-48df-b872-0b59e6928f0e

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
namespace GroundTheory.ProfCoh
theorem _root_.solution {x : Eˣ} :
    x ∈ sUnitsOf S E ↔
      IsIntegral (S.integer F) (x : E) ∧ IsIntegral (S.integer F) ((x⁻¹ : Eˣ) : E) :=
  Iff.rfl
end GroundTheory.ProfCoh
