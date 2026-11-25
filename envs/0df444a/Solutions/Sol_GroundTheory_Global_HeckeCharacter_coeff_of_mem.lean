-- Prove2me | solution 1 for GroundTheory.Global.HeckeCharacter.coeff_of_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T08:07:28.218845+00:00
-- url     : https://prove2.me/submissions/68d5ecc5-b2f6-410f-b416-744d7bdedc4e

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
open GroundTheory.Global.HeckeCharacter
variable {K : Type*} [Field K] [NumberField K] (χ : HeckeCharacter K)
namespace GroundTheory.Global.HeckeCharacter
theorem _root_.solution {I : Ideal (𝓞 K)} (h : I ≠ ⊥ ∧ IsCoprime I χ.conductor) :
    χ.coeff I = χ.idealCharacter ⟨idealUnit I h.1, idealUnit_mem_idealsPrimeTo h.1 h.2⟩ :=
  dif_pos h
end GroundTheory.Global.HeckeCharacter
