-- Prove2me | solution 1 for GroundTheory.PAdicHodge.IsPerfectoidField.ker_evalB
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T10:40:40.12728+00:00
-- url     : https://prove2.me/submissions/09ee2774-2114-497a-8215-86320418b7aa

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_ThetaPlus
import Definitions.Def_GroundTheory_PAdicHodge_AInfGalois
import Definitions.Def_GroundTheory_PAdicHodge_BdRGalois
import Theorems.Thm_GroundTheory_PAdicHodge_IsPerfectoidField_map_ker_fontaineThetaInvertP

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
open Ideal WittVector IsLocalRing
open GroundTheory GroundTheory.PAdicHodge
open GroundTheory.PAdicHodge.IsPerfectoidField
variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K]
variable {p : ℕ} [Fact p.Prime] [IsPerfectoidField K p] [CharZero K]
local notation "𝒪" => normInteger K
local notation "𝕎𝒪♭" => WittVector p (PreTilt (normInteger K) p)
local notation "𝔸" => Localization.Away (p : WittVector p (PreTilt (normInteger K) p))
local notation "𝔹" => BDeRhamPlus (normInteger K) p
local notation "J" => RingHom.ker (fontaineThetaInvertP (normInteger K) p)
namespace GroundTheory.PAdicHodge.IsPerfectoidField
theorem _root_.solution (n : ℕ) : RingHom.ker (evalB K p n) = maximalIdeal 𝔹 ^ n := by
  have h := ker_adicCompletion_evalₐ (fg_ker_fontaineThetaInvertP
    (ker_fontaineTheta_eq_span_kerThetaGenerator K p)) n
  rw [Ideal.map_pow] at h
  rw [← map_ker_fontaineThetaInvertP K p]
  exact h
end GroundTheory.PAdicHodge.IsPerfectoidField
