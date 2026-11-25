-- Prove2me | solution 1 for GroundTheory.PAdicHodge.WittTilt.gn_unit
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T14:02:24.586464+00:00
-- url     : https://prove2.me/submissions/a3006cdf-71f5-41e1-95a8-597e3baf7fcb

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_BCrisNewtonLift
import Definitions.Def_GroundTheory_PAdicHodge_FactorizationFactorialLe
import Definitions.Def_GroundTheory_PAdicHodge_KerTheta
import Definitions.Def_GroundTheory_PAdicHodge_BCrisNewtonNorm
import Theorems.Thm_GroundTheory_PAdicHodge_WittTilt_gn_nonneg
import Theorems.Thm_GroundTheory_PAdicHodge_WittTilt_gn_mul
import Theorems.Thm_GroundTheory_PAdicHodge_WittTilt_gn_one
import Theorems.Thm_GroundTheory_PAdicHodge_WittTilt_gn_algebraMap_le_one

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
open GroundTheory.PAdicHodge.WittTilt
open _root_.WittVector Laurent
variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K]
variable {p : ℕ} [hp : Fact p.Prime] [IsPerfectoidField K p]
local notation "𝒪" => normInteger K
local notation "𝒪♭" => PreTilt (normInteger K) p
local notation "K♭" => Tilt K NormedField.valuation (normInteger K) normInteger_integers p
local notation "𝔸" => Localization.Away (p : AInf K p)
local notation "θ" => fontaineTheta (normInteger K) p
variable {ρ : ℝ}
namespace GroundTheory.PAdicHodge.WittTilt
theorem _root_.solution (hρ0 : 0 < ρ) (hρ1 : ρ < 1) {x : AInf K p} (hx : IsUnit x) :
    gn K p ρ (algebraMap (AInf K p) 𝔸 x) = 1 := by
  obtain ⟨u, rfl⟩ := hx
  have h1 := gn_algebraMap_le_one (K := K) hρ0 hρ1.le (u : AInf K p)
  have h2 := gn_algebraMap_le_one (K := K) hρ0 hρ1.le (↑u⁻¹ : AInf K p)
  have h3 : gn K p ρ (algebraMap (AInf K p) 𝔸 u) * gn K p ρ (algebraMap (AInf K p) 𝔸 ↑u⁻¹) = 1 := by
    rw [← gn_mul hρ0 hρ1, ← map_mul, Units.mul_inv, map_one, gn_one hρ0 hρ1]
  nlinarith [gn_nonneg (K := K) hρ0 (algebraMap (AInf K p) 𝔸 u),
    gn_nonneg (K := K) hρ0 (algebraMap (AInf K p) 𝔸 ↑u⁻¹)]
end GroundTheory.PAdicHodge.WittTilt
