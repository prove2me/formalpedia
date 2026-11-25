-- Prove2me | solution 1 for GroundTheory.PAdicHodge.IsPerfectoidField.mem_span_xi_pow_of_forall_mem_sup
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T10:19:04.929604+00:00
-- url     : https://prove2.me/submissions/985bc0c6-f973-460e-ad32-b0fe9d2976d5

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_ThetaPlus
import Definitions.Def_GroundTheory_PAdicHodge_BdRLattice
import Theorems.Thm_GroundTheory_PAdicHodge_IsPerfectoidField_eq_zero_of_forall_mem_span_p_pow
import Theorems.Thm_GroundTheory_PAdicHodge_IsPerfectoidField_mem_span_xi_pow_of_p_pow_mul_mem

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
theorem _root_.solution (hξ : RingHom.ker θ = span {ξ}) {x : 𝕎𝒪♭} {k : ℕ}
    (h : ∀ M : ℕ, x ∈ span {(p : 𝕎𝒪♭) ^ M} ⊔ span {ξ ^ k}) : x ∈ span {ξ ^ k} := by
  have hnz := mem_nonZeroDivisors_of_ker_eq_span hξ
  induction k generalizing x with
  | zero => simp
  | succ k ih =>
    have hθ : θ x = 0 := by
      refine eq_zero_of_forall_mem_span_p_pow (p := p) fun M => ?_
      obtain ⟨a, ha, b, hb, hab⟩ := Submodule.mem_sup.1 (h M)
      obtain ⟨a', rfl⟩ := mem_span_singleton.1 ha
      obtain ⟨b', rfl⟩ := mem_span_singleton.1 hb
      have hξ0 : θ ξ = 0 := by
        rw [← RingHom.mem_ker, hξ]; exact mem_span_singleton_self ξ
      rw [← hab, map_add, map_mul, map_mul, map_pow, map_pow, map_natCast, hξ0,
        zero_pow (Nat.succ_ne_zero k), zero_mul, add_zero]
      exact mem_span_singleton.2 ⟨_, rfl⟩
    have hx2 : x ∈ span {ξ} := by rw [← hξ]; exact hθ
    obtain ⟨x', rfl⟩ := mem_span_singleton.1 hx2
    have h' : ∀ M : ℕ, x' ∈ span {(p : 𝕎𝒪♭) ^ M} ⊔ span {ξ ^ k} := by
      intro M
      obtain ⟨a, ha, b, hb, hab⟩ := Submodule.mem_sup.1 (h M)
      obtain ⟨a', rfl⟩ := mem_span_singleton.1 ha
      obtain ⟨b', rfl⟩ := mem_span_singleton.1 hb
      have ha1 : (p : 𝕎𝒪♭) ^ M * a' ∈ span {ξ ^ 1} := by
        rw [pow_one, mem_span_singleton]
        exact ⟨x' - ξ ^ k * b', by rw [← sub_eq_iff_eq_add.2 hab.symm, pow_succ]; ring⟩
      obtain ⟨a'', ha''⟩ := mem_span_singleton.1 (mem_span_xi_pow_of_p_pow_mul_mem hξ ha1)
      have h4 : ξ * (x' - (p : 𝕎𝒪♭) ^ M * a'' - ξ ^ k * b') = 0 := by
        rw [pow_one] at ha''
        rw [ha'', pow_succ] at hab
        linear_combination -hab
      have h5 := sub_eq_zero.1 ((mem_nonZeroDivisors_iff.1 hnz).1 _ h4)
      refine Submodule.mem_sup.2 ⟨_, mem_span_singleton.2 ⟨a'', rfl⟩, _,
        mem_span_singleton.2 ⟨b', rfl⟩, ?_⟩
      rw [← h5]; ring
    obtain ⟨d, hd⟩ := mem_span_singleton.1 (ih h')
    exact mem_span_singleton.2 ⟨d, by rw [hd, pow_succ]; ring⟩
end GroundTheory.PAdicHodge.IsPerfectoidField
