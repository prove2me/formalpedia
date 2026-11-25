-- Prove2me | solution 1 for GroundTheory.Global.summable_absNorm_rpow_inv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T09:32:18.503865+00:00
-- url     : https://prove2.me/submissions/27c4dd5c-1963-4416-8933-bb0f9319f66d

import Theorems.Thm_P2M_UpperTheory_Reformulated_B_Qp7_summable_absNorm_rpow_inv__1131da3fa2ce
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
theorem _root_.solution {σ : ℝ} (hσ : 1 < σ) :
    Summable fun I : Ideal (𝓞 K) ↦ ((absNorm I : ℝ) ^ σ)⁻¹ :=
  _root_.P2M_UpperTheory_Reformulated_B_Qp7_summable_absNorm_rpow_inv__1131da3fa2ce hσ
end GroundTheory.Global
