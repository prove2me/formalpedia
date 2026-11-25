-- Prove2me | solution 1 for GroundTheory.PAdicHodge.IsPerfectoidField.isAdicComplete_maximalIdeal_bDeRhamPlus
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T10:18:26.8378+00:00
-- url     : https://prove2.me/submissions/68a829e4-b949-4099-8dd8-abe27078701e

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_KerTheta
import Definitions.Def_GroundTheory_PAdicHodge_ThetaPlus
import Theorems.Thm_GroundTheory_PAdicHodge_maximalIdeal_bDeRhamPlus_eq_span
import Theorems.Thm_GroundTheory_PAdicHodge_IsPerfectoidField_maximalIdeal_bDeRhamPlus_eq_span

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
open Ideal WittVector IsLocalRing
open GroundTheory.PAdicHodge.IsPerfectoidField
variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K]
variable (p : ℕ) [Fact p.Prime] [IsPerfectoidField K p]
local notation "𝒪" => normInteger K
local notation "𝕎𝒪♭" => WittVector p (PreTilt (normInteger K) p)
local notation "θ" => fontaineTheta (normInteger K) p
local notation "𝔹" => BDeRhamPlus (normInteger K) p
variable {p}
variable [CharZero K]
namespace GroundTheory.PAdicHodge.IsPerfectoidField
theorem _root_.solution : IsAdicComplete (maximalIdeal 𝔹) 𝔹 := by
  rw [maximalIdeal_bDeRhamPlus_eq_span (ker_fontaineTheta_eq_span_kerThetaGenerator K p)]
  exact isAdicComplete_bDeRhamPlus (ker_fontaineTheta_eq_span_kerThetaGenerator K p)
end GroundTheory.PAdicHodge.IsPerfectoidField
