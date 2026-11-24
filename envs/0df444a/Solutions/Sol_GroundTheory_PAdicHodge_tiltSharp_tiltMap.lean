-- Prove2me | solution 1 for GroundTheory.PAdicHodge.tiltSharp_tiltMap
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T09:41:10.584208+00:00
-- url     : https://prove2.me/submissions/d5ce3fa3-b447-4630-adf0-ca2293faaf76

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_PerfectoidField
import Definitions.Def_GroundTheory_PAdicHodge_TiltValuation
import Definitions.Def_GroundTheory_PAdicHodge_TiltField
import Definitions.Def_GroundTheory_PAdicHodge_KerTheta
import Definitions.Def_GroundTheory_PAdicHodge_KerFontaineThetaCompFrobeniusEquivSymmPow
import Definitions.Def_GroundTheory_PAdicHodge_TiltMap
import Theorems.Thm_GroundTheory_PAdicHodge_tiltMap_algebraMap
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GroundTheory.PAdicHodge.tiltMap_algebraMap

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
theorem _root_.solution (x : K♭) : tiltSharp L p (tiltMap p φ hφ x) = φ (tiltSharp K p x) := by
  obtain ⟨a, b, hb, h⟩ := exists_mul_algebraMap_eq x
  have hb' : preTiltMap p φ hφ b ≠ 0 :=
    (map_ne_zero_iff _ (preTiltMap_injective φ hφ)).2 hb
  have h' : tiltMap p φ hφ x * algebraMap 𝒪L♭ L♭ (preTiltMap p φ hφ b) =
      algebraMap 𝒪L♭ L♭ (preTiltMap p φ hφ a) := by
    rw [← tiltMap_algebraMap, ← tiltMap_algebraMap, ← map_mul, h]
  rw [tiltSharp_eq hb' h', tiltSharp_eq hb h, map_div₀, coe_untilt_preTiltMap,
    coe_untilt_preTiltMap]
end GroundTheory.PAdicHodge
