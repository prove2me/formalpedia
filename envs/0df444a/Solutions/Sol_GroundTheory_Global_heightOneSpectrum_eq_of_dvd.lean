-- Prove2me | solution 1 for GroundTheory.Global.heightOneSpectrum_eq_of_dvd
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T08:07:49.821237+00:00
-- url     : https://prove2.me/submissions/c1dbf987-4195-44b8-864c-8feae44c5bee

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_HeckeChar
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_SummableAbsNormRpowInv
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_HeckeLFunction

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
theorem _root_.solution {v w : HeightOneSpectrum R} (h : w.asIdeal ∣ v.asIdeal) :
    w = v :=
  HeightOneSpectrum.ext (associated_iff_eq.1
    ((HeightOneSpectrum.prime w).associated_of_dvd (HeightOneSpectrum.prime v) h))
end GroundTheory.Global
