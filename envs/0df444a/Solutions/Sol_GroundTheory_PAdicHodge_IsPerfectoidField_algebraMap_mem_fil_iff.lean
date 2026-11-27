-- Prove2me | solution 1 for GroundTheory.PAdicHodge.IsPerfectoidField.algebraMap_mem_fil_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-27T04:48:13.625793+00:00
-- url     : https://prove2.me/submissions/e93f18cb-af82-494c-889c-6eaf65f71088

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_BdRGalois
import Definitions.Def_GroundTheory_PAdicHodge_BdRField
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
namespace GroundTheory.PAdicHodge.IsPerfectoidField
theorem _root_.solution (b : 𝔹) (n : ℕ) :
    algebraMap 𝔹 𝔹dR b ∈ fil K p n ↔ b ∈ maximalIdeal 𝔹 ^ n := by
  rw [mem_fil_iff (maximalIdeal_eq_span_varpi K p), maximalIdeal_eq_span_varpi K p,
    span_singleton_pow, mem_span_singleton]
  simp only [zpow_natCast, ← map_pow, ← map_mul]
  constructor
  · rintro ⟨c, hc⟩
    exact ⟨c, algebraMap_bDeRham_injective hc⟩
  · rintro ⟨c, hc⟩
    exact ⟨c, by rw [hc]⟩
end GroundTheory.PAdicHodge.IsPerfectoidField
