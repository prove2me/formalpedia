-- Prove2me | solution 1 for GroundTheory.PAdicHodge.IsPerfectoidField.mem_maximalIdeal_pow_of_forall_sub_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T10:25:17.441489+00:00
-- url     : https://prove2.me/submissions/ce514bbb-a833-423d-aaed-77186d5134ca

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_ThetaPlus
import Definitions.Def_GroundTheory_PAdicHodge_BdRLattice
import Theorems.Thm_GroundTheory_PAdicHodge_IsPerfectoidField_mem_span_xi_pow_of_p_pow_mul_mem
import Theorems.Thm_GroundTheory_PAdicHodge_IsPerfectoidField_mem_span_xi_pow_of_forall_mem_sup
import Theorems.Thm_GroundTheory_PAdicHodge_IsPerfectoidField_exists_p_pow_mul_mem_of_dvd
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
theorem _root_.solution {y : 𝔹} {k : ℕ}
    (h : ∀ M : ℕ, ∃ a : 𝕎𝒪♭, y - (p : 𝔹) ^ M * wittToBDeRhamPlus 𝒪 p a ∈ maximalIdeal 𝔹 ^ k) :
    y ∈ maximalIdeal 𝔹 ^ k := by
  set ξ₀ := kerThetaGenerator K p
  have hξ := ker_fontaineTheta_eq_span_kerThetaGenerator K p
  have hm : maximalIdeal 𝔹 ^ k = span {wittToBDeRhamPlus 𝒪 p (ξ₀ ^ k)} := by
    rw [maximalIdeal_bDeRhamPlus_eq_span hξ, span_singleton_pow, map_pow]
  obtain ⟨a₀, ha₀⟩ := h 0
  rw [pow_zero, one_mul] at ha₀
  suffices hs : a₀ ∈ span {ξ₀ ^ k} by
    have h1 : wittToBDeRhamPlus 𝒪 p a₀ ∈ maximalIdeal 𝔹 ^ k := by
      rw [hm]
      obtain ⟨d, rfl⟩ := mem_span_singleton.1 hs
      rw [map_mul]
      exact mul_mem_right _ _ (mem_span_singleton_self _)
    have := add_mem ha₀ h1
    rwa [sub_add_cancel] at this
  refine mem_span_xi_pow_of_forall_mem_sup hξ fun M => ?_
  obtain ⟨a, ha⟩ := h M
  have h2 : wittToBDeRhamPlus 𝒪 p (a₀ - (p : 𝕎𝒪♭) ^ M * a) ∈ maximalIdeal 𝔹 ^ k := by
    have := sub_mem ha ha₀
    rw [map_sub, map_mul, map_pow, map_natCast]
    convert this using 1
    ring
  rw [hm] at h2
  have h3 : toBDeRhamPlus 𝒪 p (algebraMap 𝕎𝒪♭ 𝔸 (a₀ - (p : 𝕎𝒪♭) ^ M * a)) ∈
      span {wittToBDeRhamPlus 𝒪 p ξ₀ ^ k} := by
    rw [← map_pow]; exact h2
  rw [toBDeRhamPlus_mem_span_pow_iff hξ, ← map_pow] at h3
  obtain ⟨s, hs⟩ := exists_p_pow_mul_mem_of_dvd h3
  have h4 := mem_span_xi_pow_of_p_pow_mul_mem hξ hs
  refine Submodule.mem_sup.2 ⟨(p : 𝕎𝒪♭) ^ M * a, mem_span_singleton.2 ⟨a, rfl⟩, _, h4, ?_⟩
  ring
end GroundTheory.PAdicHodge.IsPerfectoidField
