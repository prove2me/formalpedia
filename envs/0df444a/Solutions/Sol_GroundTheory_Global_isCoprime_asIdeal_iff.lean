-- Prove2me | solution 1 for GroundTheory.Global.isCoprime_asIdeal_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T08:03:18.010613+00:00
-- url     : https://prove2.me/submissions/30dfb227-7f61-485a-9f92-9a4a24637d6f

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
variable {K : Type*} [Field K] [NumberField K]
namespace GroundTheory.Global
theorem _root_.solution (v : HeightOneSpectrum (𝓞 K)) (𝔪 : Ideal (𝓞 K)) :
    IsCoprime v.asIdeal 𝔪 ↔ ¬ v.asIdeal ∣ 𝔪 := by
  constructor
  · intro h hv
    exact not_dvd_of_isCoprime h hv (dvd_refl _)
  · intro h
    rw [Ideal.isCoprime_iff_sup_eq]
    exact v.isMaximal.out.2 _ (left_lt_sup.2 fun hle ↦ h (Ideal.dvd_iff_le.2 hle))
end GroundTheory.Global
