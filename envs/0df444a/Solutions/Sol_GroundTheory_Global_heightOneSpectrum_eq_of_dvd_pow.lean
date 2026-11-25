-- Prove2me | solution 1 for GroundTheory.Global.heightOneSpectrum_eq_of_dvd_pow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T08:19:48.49014+00:00
-- url     : https://prove2.me/submissions/307c9432-8eff-48c3-b064-b40ec09dd715

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_HeckeChar
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_SummableAbsNormRpowInv
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_HeckeLFunction
import Theorems.Thm_GroundTheory_Global_heightOneSpectrum_eq_of_dvd

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
variable {R : Type*} [CommRing R] [IsDedekindDomain R]
namespace GroundTheory.Global
theorem _root_.solution {v w : HeightOneSpectrum R} {k : ℕ}
    (h : w.asIdeal ∣ v.asIdeal ^ k) : w = v :=
  heightOneSpectrum_eq_of_dvd ((HeightOneSpectrum.prime w).dvd_of_dvd_pow h)
end GroundTheory.Global
