-- Prove2me | solution 1 for GroundTheory.PAdicHodge.IsPerfectoidField.exists_ker_fontaineTheta_eq_span_p_sub_teichmuller
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-27T03:07:39.32094+00:00
-- url     : https://prove2.me/submissions/f2a3d3e0-1c32-46b2-aed8-a2a7a757be9c

import Mathlib
import Theorems.Thm_GroundTheory_PAdicHodge_IsPerfectoidField_ker_fontaineTheta_eq_span_p_sub_teichmuller_ofCompatible
import Theorems.Thm_GroundTheory_PAdicHodge_IsPerfectoidField_untilt_ofCompatible
import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_PerfectoidField
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_LeSpanSingletonOfForallMemEq
import Definitions.Def_GroundTheory_PAdicHodge_KerTheta
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
open WittVector
open GroundTheory.PAdicHodge.IsPerfectoidField
variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K]
variable {p : ℕ} [Fact p.Prime] [IsPerfectoidField K p]
local notation "𝒪" => normInteger K
local notation "𝒪♭" => PreTilt (normInteger K) p
local notation "𝕎𝒪♭" => WittVector p (PreTilt (normInteger K) p)
local notation "θ" => fontaineTheta (normInteger K) p
variable (K p)
theorem solution [IsAlgClosed K] :
    ∃ pflat : 𝒪♭, PreTilt.untilt pflat = p ∧
      RingHom.ker θ = Ideal.span {(p : 𝕎𝒪♭) - teichmuller p pflat} := by
  have hpp : p.Prime := Fact.out
  have root : ∀ a : 𝒪, ∃ b : 𝒪, b ^ p = a := by
    intro a
    obtain ⟨z, hz⟩ := IsAlgClosed.exists_pow_nat_eq (a : K) hpp.pos
    have hz1 : ‖z‖ ≤ 1 := by
      have : ‖z‖ ^ p ≤ 1 := by rw [← norm_pow, hz]; exact mem_normInteger.1 a.2
      exact (pow_le_one_iff_of_nonneg (norm_nonneg _) hpp.ne_zero).1 this
    exact ⟨⟨z, mem_normInteger.2 hz1⟩, Subtype.ext (by simp [hz])⟩
  choose r hr using root
  let y : ℕ → 𝒪 := fun n => Nat.rec (p : 𝒪) (fun _ b => r b) n
  have hy : ∀ n, y (n + 1) ^ p = y n := fun n => hr (y n)
  refine ⟨ofCompatible p y hy, ?_,
    IsPerfectoidField.ker_fontaineTheta_eq_span_p_sub_teichmuller_ofCompatible y hy rfl⟩
  rw [IsPerfectoidField.untilt_ofCompatible]
  rfl
