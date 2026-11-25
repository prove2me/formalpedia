-- Prove2me | solution 1 for GroundTheory.PAdicHodge.IsPerfectoidField.map_ker_fontaineThetaInvertP
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T10:25:04.756601+00:00
-- url     : https://prove2.me/submissions/39495f0d-c50d-4a7c-9873-17d295911232

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_ThetaPlus
import Definitions.Def_GroundTheory_PAdicHodge_AInfGalois
import Definitions.Def_GroundTheory_PAdicHodge_BdRGalois
import Theorems.Thm_GroundTheory_PAdicHodge_IsPerfectoidField_maximalIdeal_bDeRhamPlus_eq_span
import Theorems.Thm_GroundTheory_PAdicHodge_maximalIdeal_bDeRhamPlus_eq_span


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
variable (K p)
namespace GroundTheory.PAdicHodge.IsPerfectoidField
theorem _root_.solution :
    Ideal.map (toBDeRhamPlus 𝒪 p) J = maximalIdeal 𝔹 := by
  rw [ker_fontaineThetaInvertP (ker_fontaineTheta_eq_span_kerThetaGenerator K p), Ideal.map_span,
    Set.image_singleton, maximalIdeal_bDeRhamPlus_eq_span (ker_fontaineTheta_eq_span_kerThetaGenerator K p)]
  rfl
end GroundTheory.PAdicHodge.IsPerfectoidField
