-- Prove2me | solution 1 for GroundTheory.PAdicHodge.IsPerfectoidField.iSup_fil
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T11:27:53.186278+00:00
-- url     : https://prove2.me/submissions/12d36519-9534-421c-aea1-dc6cee615cf1

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_BdRGalois
import Definitions.Def_GroundTheory_PAdicHodge_BdRField
import Theorems.Thm_GroundTheory_PAdicHodge_IsPerfectoidField_isLocalization_away_bDeRham
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
open Ideal WittVector IsLocalRing
noncomputable section
open GroundTheory GroundTheory.PAdicHodge
open GroundTheory.PAdicHodge.IsPerfectoidField
variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K]
variable {p : ℕ} [Fact p.Prime] [IsPerfectoidField K p] [CharZero K]
local notation "𝒪" => normInteger K
local notation "𝔸" => Localization.Away (p : WittVector p (PreTilt (normInteger K) p))
local notation "𝔹" => BDeRhamPlus (normInteger K) p
local notation "𝔹dR" => BDeRham (normInteger K) p
local notation "J" => RingHom.ker (fontaineThetaInvertP (normInteger K) p)
variable (K p)
namespace GroundTheory.PAdicHodge.IsPerfectoidField
theorem _root_.solution : ⨆ i, fil K p i = ⊤ := by
  have hϖ := maximalIdeal_eq_span_varpi K p
  have hne := algebraMap_ne_zero_of_maximalIdeal_eq_span (K := K) hϖ
  haveI := isLocalization_away_bDeRham hϖ
  refine eq_top_iff.2 fun x _ => ?_
  obtain ⟨⟨a, ⟨_, m, rfl⟩⟩, ha⟩ := IsLocalization.surj (Submonoid.powers (varpi K p)) x
  simp only [map_pow] at ha
  refine Submodule.mem_iSup_of_mem (-(m : ℤ)) ((mem_fil_iff hϖ).2 ⟨a, ?_⟩)
  rw [← ha, zpow_neg, zpow_natCast, mul_comm x, ← mul_assoc, inv_mul_cancel₀ (pow_ne_zero _ hne),
    one_mul]
end GroundTheory.PAdicHodge.IsPerfectoidField
