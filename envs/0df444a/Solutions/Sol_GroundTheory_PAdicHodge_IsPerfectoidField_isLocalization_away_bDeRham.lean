-- Prove2me | solution 1 for GroundTheory.PAdicHodge.IsPerfectoidField.isLocalization_away_bDeRham
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T11:06:38.204617+00:00
-- url     : https://prove2.me/submissions/609123dd-73f4-4519-92ef-e89d3b0e6c76

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
theorem _root_.solution {π : 𝔹} (hπ : maximalIdeal 𝔹 = span {π}) :
    IsLocalization.Away π 𝔹dR := by
  have hirr : Irreducible π := IsDiscreteValuationRing.irreducible_iff_uniformizer π |>.2 hπ
  rw [IsLocalization.Away, isLocalization_iff]
  refine ⟨?_, fun z => ?_, fun {x y} h => ⟨1, by rw [algebraMap_bDeRham_injective h]⟩⟩
  · rintro ⟨_, n, rfl⟩
    have h := (isUnit_algebraMap_bDeRham (K := K) (ne_zero_of_maximalIdeal_eq_span hπ)).pow n
    rw [← map_pow] at h
    exact h
  · obtain ⟨⟨x, y⟩, hxy⟩ := IsLocalization.surj (nonZeroDivisors 𝔹) z
    obtain ⟨n, u, hu⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible
      (nonZeroDivisors.coe_ne_zero y) hirr
    refine ⟨⟨x * ↑u⁻¹, ⟨π ^ n, n, rfl⟩⟩, ?_⟩
    simp only at hxy ⊢
    have hu' : (y : 𝔹) * ↑u⁻¹ = π ^ n := by rw [hu, mul_comm (↑u : 𝔹), mul_assoc, Units.mul_inv, mul_one]
    rw [← hu', map_mul, ← mul_assoc, hxy, map_mul]
end GroundTheory.PAdicHodge.IsPerfectoidField
