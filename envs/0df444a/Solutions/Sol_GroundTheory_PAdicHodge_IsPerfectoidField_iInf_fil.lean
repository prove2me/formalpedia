-- Prove2me | solution 1 for GroundTheory.PAdicHodge.IsPerfectoidField.iInf_fil
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T11:18:20.778473+00:00
-- url     : https://prove2.me/submissions/2fdfa93c-bc8f-43bb-8255-f4ee47f54e56

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_BdRGalois
import Definitions.Def_GroundTheory_PAdicHodge_BdRField
import Theorems.Thm_GroundTheory_PAdicHodge_IsPerfectoidField_isLocalization_away_bDeRham
import Theorems.Thm_GroundTheory_PAdicHodge_IsPerfectoidField_eq_zero_of_forall_mem_maximalIdeal_pow
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
theorem _root_.solution : ⨅ i, fil K p i = ⊥ := by
  have hϖ := maximalIdeal_eq_span_varpi K p
  have hne := algebraMap_ne_zero_of_maximalIdeal_eq_span (K := K) hϖ
  haveI := isLocalization_away_bDeRham hϖ
  refine eq_bot_iff.2 fun x hx => ?_
  rw [Submodule.mem_iInf] at hx
  obtain ⟨⟨a, ⟨_, m, rfl⟩⟩, ha⟩ := IsLocalization.surj (Submonoid.powers (varpi K p)) x
  simp only [map_pow] at ha
  have ha0 : a = 0 := by
    refine eq_zero_of_forall_mem_maximalIdeal_pow fun n => ?_
    obtain ⟨b, hb⟩ := (mem_fil_iff hϖ).1 (hx ((n : ℤ) - m))
    have h2 : algebraMap 𝔹 𝔹dR a = algebraMap 𝔹 𝔹dR (varpi K p ^ n * b) := by
      rw [← ha, hb, map_mul, map_pow, mul_right_comm,
        ← zpow_natCast (algebraMap 𝔹 𝔹dR (varpi K p)) m, ← zpow_add₀ hne, sub_add_cancel,
        zpow_natCast]
    rw [algebraMap_bDeRham_injective h2, hϖ, span_singleton_pow]
    exact mul_mem_right _ _ (mem_span_singleton_self _)
  rw [ha0, map_zero] at ha
  rw [Submodule.mem_bot]
  exact (mul_eq_zero.1 ha).resolve_right (pow_ne_zero _ hne)
end GroundTheory.PAdicHodge.IsPerfectoidField
