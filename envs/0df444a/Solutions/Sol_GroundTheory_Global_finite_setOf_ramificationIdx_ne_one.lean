-- Prove2me | solution 1 for GroundTheory.Global.finite_setOf_ramificationIdx_ne_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T03:58:32.215561+00:00
-- url     : https://prove2.me/submissions/995c55f6-37f5-40a2-96d2-43e206ef0bf7

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_DegreeOnePrimes
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_PrimeZetaPole
import Definitions.Def_GroundTheory_GlobalFields_KummerTheory_Splitting
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_DegreeOneDensity
import Theorems.Thm_GroundTheory_Global_dvd_differentIdeal_of_ramificationIdx_ne_one

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Global
open NumberField IsDedekindDomain Filter Topology Set Ideal
noncomputable section
variable {K : Type*} [Field K] [NumberField K] {L : Type*} [Field L] [NumberField L]
  [Algebra K L]
variable (K L)
namespace GroundTheory.Global
theorem _root_.solution :
    {w : HeightOneSpectrum (𝓞 L) | w.asIdeal.ramificationIdx (𝓞 K) ≠ 1}.Finite :=
  (Ideal.finite_factors (differentIdeal_ne_bot (A := 𝓞 K) (B := 𝓞 L))).subset
    fun _ hw => dvd_differentIdeal_of_ramificationIdx_ne_one hw
end GroundTheory.Global
