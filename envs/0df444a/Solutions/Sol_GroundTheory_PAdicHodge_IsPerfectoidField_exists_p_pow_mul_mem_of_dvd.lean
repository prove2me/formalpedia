-- Prove2me | solution 1 for GroundTheory.PAdicHodge.IsPerfectoidField.exists_p_pow_mul_mem_of_dvd
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T10:02:12.873351+00:00
-- url     : https://prove2.me/submissions/67802ebd-4174-4ffa-9b8f-638b244eb139

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_ThetaPlus
import Definitions.Def_GroundTheory_PAdicHodge_BdRLattice

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
variable {p : ℕ} [Fact p.Prime] [IsPerfectoidField K p] [CharZero K]
local notation "𝒪" => normInteger K
local notation "𝕎𝒪♭" => WittVector p (PreTilt (normInteger K) p)
local notation "θ" => fontaineTheta (normInteger K) p
local notation "𝔹" => BDeRhamPlus (normInteger K) p
local notation "𝔸" => Localization.Away (p : WittVector p (PreTilt (normInteger K) p))
variable {ξ : WittVector p (PreTilt (normInteger K) p)}
namespace GroundTheory.PAdicHodge.IsPerfectoidField
theorem _root_.solution {z : 𝕎𝒪♭} {k : ℕ}
    (h : algebraMap 𝕎𝒪♭ 𝔸 (ξ ^ k) ∣ algebraMap 𝕎𝒪♭ 𝔸 z) :
    ∃ s : ℕ, (p : 𝕎𝒪♭) ^ s * z ∈ span {ξ ^ k} := by
  obtain ⟨c, hc⟩ := h
  obtain ⟨⟨c', m⟩, hcm⟩ := IsLocalization.mk'_surjective (Submonoid.powers (p : 𝕎𝒪♭)) c
  obtain ⟨s, hs⟩ := Submonoid.mem_powers_iff _ _ |>.1 m.2
  have h2 : algebraMap 𝕎𝒪♭ 𝔸 (z * (m : 𝕎𝒪♭)) = algebraMap 𝕎𝒪♭ 𝔸 (ξ ^ k * c') := by
    rw [map_mul, hc, ← hcm, mul_assoc, IsLocalization.mk'_spec, map_mul]
  obtain ⟨r, hr⟩ := IsLocalization.exists_of_eq (M := Submonoid.powers (p : 𝕎𝒪♭)) h2
  obtain ⟨r', hr'⟩ := Submonoid.mem_powers_iff _ _ |>.1 r.2
  refine ⟨r' + s, mem_span_singleton.2 ⟨(p : 𝕎𝒪♭) ^ r' * c', ?_⟩⟩
  rw [← hs, ← hr'] at hr
  rw [pow_add]
  linear_combination hr
end GroundTheory.PAdicHodge.IsPerfectoidField
