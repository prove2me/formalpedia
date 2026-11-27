-- Prove2me | solution 1 for GroundTheory.ProfCoh.finite_setOf_ramified
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-27T04:49:29.328538+00:00
-- url     : https://prove2.me/submissions/a8db52ed-0312-4e3a-b7df-84b9c573195a

import Mathlib
import Definitions.Def_GroundTheory_ProfiniteCohomology_GlobalClassFormation_IdeleCohomology_Ramified
import Theorems.Thm_GroundTheory_ProfCoh_ramified_dvd_differentIdeal

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
open IsDedekindDomain NumberField
variable {K : Type*} [Field K] [NumberField K] {L : Type*} [Field L] [NumberField L] [Algebra K L]
variable (K L)
namespace GroundTheory.ProfCoh
theorem _root_.solution :
    {w : HeightOneSpectrum (𝓞 L) | w.asIdeal.ramificationIdx (𝓞 K) ≠ 1}.Finite :=
  (Ideal.finite_factors (differentIdeal_ne_bot (A := 𝓞 K) (B := 𝓞 L))).subset
    fun _ hw => ramified_dvd_differentIdeal hw
end GroundTheory.ProfCoh
