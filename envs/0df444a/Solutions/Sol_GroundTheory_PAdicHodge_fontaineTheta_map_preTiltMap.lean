-- Prove2me | solution 1 for GroundTheory.PAdicHodge.fontaineTheta_map_preTiltMap
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T00:51:37.339218+00:00
-- url     : https://prove2.me/submissions/aa028f01-ec95-46df-8d7d-005260b4b457

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_PerfectoidField
import Definitions.Def_GroundTheory_PAdicHodge_TiltValuation
import Definitions.Def_GroundTheory_PAdicHodge_TiltField
import Definitions.Def_GroundTheory_PAdicHodge_KerTheta
import Definitions.Def_GroundTheory_PAdicHodge_KerFontaineThetaCompFrobeniusEquivSymmPow
import Definitions.Def_GroundTheory_PAdicHodge_TiltMap
import Theorems.Thm_GroundTheory_PAdicHodge_ringHom_ext_wittVector_preTilt

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.PAdicHodge
variable {K L : Type*} [NontriviallyNormedField K] [IsUltrametricDist K]
  [NontriviallyNormedField L] [IsUltrametricDist L]
variable {p : ℕ} [Fact p.Prime] [IsPerfectoidField K p] [IsPerfectoidField L p]
variable (φ : K →+* L) (hφ : ∀ x, ‖φ x‖ = ‖x‖)
local notation "𝒪K♭" => PreTilt (normInteger K) p
local notation "𝒪L♭" => PreTilt (normInteger L) p
local notation "K♭" => Tilt K NormedField.valuation (normInteger K) normInteger_integers p
local notation "L♭" => Tilt L NormedField.valuation (normInteger L) normInteger_integers p
namespace GroundTheory.PAdicHodge
theorem _root_.solution (w : WittVector p 𝒪K♭) :
    WittVector.fontaineTheta (normInteger L) p (WittVector.map (preTiltMap p φ hφ) w) =
      integerMap φ hφ (WittVector.fontaineTheta (normInteger K) p w) := by
  have := ringHom_ext_wittVector_preTilt
    (f := (WittVector.fontaineTheta (normInteger L) p).comp (WittVector.map (preTiltMap p φ hφ)))
    (g := (integerMap φ hφ).comp (WittVector.fontaineTheta (normInteger K) p)) fun a => by
      rw [RingHom.comp_apply, RingHom.comp_apply, WittVector.map_teichmuller,
        WittVector.fontaineTheta_teichmuller, WittVector.fontaineTheta_teichmuller, untilt_preTiltMap]
  exact congrArg (fun F => F w) this
end GroundTheory.PAdicHodge
