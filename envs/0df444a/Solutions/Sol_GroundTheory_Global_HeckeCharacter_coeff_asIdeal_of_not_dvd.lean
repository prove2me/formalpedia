-- Prove2me | solution 1 for GroundTheory.Global.HeckeCharacter.coeff_asIdeal_of_not_dvd
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T08:15:30.098669+00:00
-- url     : https://prove2.me/submissions/172d3a63-53ee-4667-8042-356cc2c92b07

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
theorem _root_.solution {v : HeightOneSpectrum (𝓞 K)} (hv : ¬ v.asIdeal ∣ χ.conductor) :
    χ.coeff v.asIdeal =
      χ.idealCharacter ⟨primeIdealUnit v, primeIdealUnit_mem_idealsPrimeTo hv⟩ := by
  rw [coeff, dif_pos ⟨v.ne_bot, (isCoprime_asIdeal_iff v _).2 hv⟩]
  rfl
end GroundTheory.Global.HeckeCharacter
