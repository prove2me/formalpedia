-- Prove2me | solution 1 for GroundTheory.Global.HeckeCharacter.coeff_asIdeal_of_dvd
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T08:15:25.733137+00:00
-- url     : https://prove2.me/submissions/96cb17b9-b2f9-4a9b-a93b-a3d841fc181d

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_HeckeChar
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_SummableAbsNormRpowInv
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_HeckeLFunction
import Theorems.Thm_GroundTheory_Global_isCoprime_asIdeal_iff

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
open Topology Filter NumberField IsDedekindDomain WithZero FractionalIdeal Function Ideal
open scoped NumberField.AdeleRing nonZeroDivisors
open GroundTheory GroundTheory.Global
noncomputable section
open GroundTheory.Global.HeckeCharacter
variable {K : Type*} [Field K] [NumberField K] (χ : HeckeCharacter K)
namespace GroundTheory.Global.HeckeCharacter
theorem _root_.solution {v : HeightOneSpectrum (𝓞 K)} (hv : v.asIdeal ∣ χ.conductor) :
    χ.coeff v.asIdeal = 0 :=
  χ.coeff_of_not fun h ↦ ((isCoprime_asIdeal_iff v _).1 h.2) hv
end GroundTheory.Global.HeckeCharacter
