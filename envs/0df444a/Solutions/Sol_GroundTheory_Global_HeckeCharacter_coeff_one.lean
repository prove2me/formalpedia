-- Prove2me | solution 1 for GroundTheory.Global.HeckeCharacter.coeff_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T08:38:35.36+00:00
-- url     : https://prove2.me/submissions/cfb64a2a-dcb9-44a1-abfe-039320f86a86

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_HeckeChar
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_SummableAbsNormRpowInv
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_HeckeLFunction
import Theorems.Thm_GroundTheory_Global_HeckeCharacter_conductor_one

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
theorem _root_.solution {I : Ideal (𝓞 K)} (hI : I ≠ ⊥) : (1 : HeckeCharacter K).coeff I = 1 := by
  have h : I ≠ ⊥ ∧ IsCoprime I (1 : HeckeCharacter K).conductor :=
    ⟨hI, by rw [conductor_one, ← Ideal.one_eq_top]; exact isCoprime_one_right⟩
  rw [coeff, dif_pos h]
  exact congrArg ((↑) : Circle → ℂ) rfl |>.trans Circle.coe_one
end GroundTheory.Global.HeckeCharacter
