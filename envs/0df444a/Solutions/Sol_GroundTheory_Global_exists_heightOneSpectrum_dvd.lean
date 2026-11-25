-- Prove2me | solution 1 for GroundTheory.Global.exists_heightOneSpectrum_dvd
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T08:21:07.392139+00:00
-- url     : https://prove2.me/submissions/82ebde0b-21f4-4f10-aa78-f3144b4d721c

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
theorem _root_.solution {I : Ideal R} (h0 : I ≠ ⊥) (h1 : I ≠ ⊤) :
    ∃ v : HeightOneSpectrum R, v.asIdeal ∣ I := by
  obtain ⟨M, hM, hIM⟩ := Ideal.exists_le_maximal I h1
  have hM0 : M ≠ ⊥ := fun h ↦ h0 (le_bot_iff.1 (h ▸ hIM))
  exact ⟨⟨M, hM.isPrime, hM0⟩, Ideal.dvd_iff_le.2 hIM⟩
end GroundTheory.Global
