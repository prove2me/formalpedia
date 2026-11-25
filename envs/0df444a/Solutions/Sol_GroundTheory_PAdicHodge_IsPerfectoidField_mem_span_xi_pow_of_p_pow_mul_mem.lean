-- Prove2me | solution 1 for GroundTheory.PAdicHodge.IsPerfectoidField.mem_span_xi_pow_of_p_pow_mul_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T10:14:49.145545+00:00
-- url     : https://prove2.me/submissions/56dced06-ce5e-4f85-ba3d-eeffed0cfbf0

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_ThetaPlus
import Definitions.Def_GroundTheory_PAdicHodge_BdRLattice
import Theorems.Thm_GroundTheory_PAdicHodge_IsPerfectoidField_natCast_p_ne_zero

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
theorem _root_.solution (hξ : RingHom.ker θ = span {ξ}) {x : 𝕎𝒪♭} {s k : ℕ}
    (h : (p : 𝕎𝒪♭) ^ s * x ∈ span {ξ ^ k}) : x ∈ span {ξ ^ k} := by
  have hnz := mem_nonZeroDivisors_of_ker_eq_span hξ
  induction k generalizing x with
  | zero => simp
  | succ k ih =>
    have hx1 : (p : 𝕎𝒪♭) ^ s * x ∈ RingHom.ker θ := by
      rw [hξ]
      exact (Ideal.span_singleton_le_span_singleton.2 (dvd_pow_self ξ (Nat.succ_ne_zero k))) h
    have hx2 : x ∈ RingHom.ker θ := by
      rw [RingHom.mem_ker, map_mul, map_pow, map_natCast] at hx1
      rw [RingHom.mem_ker]
      exact (mul_eq_zero.1 hx1).resolve_left (pow_ne_zero _ natCast_p_ne_zero)
    rw [hξ, mem_span_singleton] at hx2
    obtain ⟨x', rfl⟩ := hx2
    obtain ⟨c, hc⟩ := mem_span_singleton.1 h
    have h3 : (p : 𝕎𝒪♭) ^ s * x' = ξ ^ k * c := by
      have h4 : ξ * ((p : 𝕎𝒪♭) ^ s * x' - ξ ^ k * c) = 0 := by
        rw [pow_succ] at hc
        linear_combination hc
      exact sub_eq_zero.1 ((mem_nonZeroDivisors_iff.1 hnz).1 _ h4)
    have h5 := ih (mem_span_singleton.2 ⟨c, h3⟩)
    obtain ⟨d, hd⟩ := mem_span_singleton.1 h5
    exact mem_span_singleton.2 ⟨d, by rw [hd, pow_succ]; ring⟩
end GroundTheory.PAdicHodge.IsPerfectoidField
