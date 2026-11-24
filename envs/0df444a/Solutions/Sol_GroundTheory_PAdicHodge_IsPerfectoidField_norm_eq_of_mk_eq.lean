-- Prove2me | solution 1 for GroundTheory.PAdicHodge.IsPerfectoidField.norm_eq_of_mk_eq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T09:05:43.030364+00:00
-- url     : https://prove2.me/submissions/fb3e1f57-7f93-42f3-aab2-26d58ae02bd8

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_PerfectoidField
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_LeSpanSingletonOfForallMemEq
import Definitions.Def_GroundTheory_PAdicHodge_KerTheta
import Theorems.Thm_GroundTheory_PAdicHodge_IsPerfectoidField_norm_le_of_mem_span_p

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
variable (p : ℕ) [Fact p.Prime] [IsPerfectoidField K p]
local notation "𝒪" => normInteger K
local notation "𝒪♭" => PreTilt (normInteger K) p
variable {p}
omit [Fact p.Prime] [IsPerfectoidField K p]
variable (p)
namespace GroundTheory.PAdicHodge.IsPerfectoidField
theorem _root_.solution {b c : 𝒪}
    (h : Ideal.Quotient.mk (Ideal.span {(p : 𝒪)}) b = Ideal.Quotient.mk _ c)
    (hc : ‖(p : K)‖ < ‖(c : K)‖) : ‖(b : K)‖ = ‖(c : K)‖ := by
  have hbc : ‖(b : K) - c‖ ≤ ‖(p : K)‖ := by
    have := norm_le_of_mem_span_p (Ideal.Quotient.eq.1 h)
    rwa [AddSubgroupClass.coe_sub] at this
  have h1 : ‖(b : K)‖ ≤ max ‖(b : K) - c‖ ‖(c : K)‖ := by
    simpa using IsUltrametricDist.norm_add_le_max ((b : K) - c) (c : K)
  have h2 : ‖(c : K)‖ ≤ max ‖(c : K) - b‖ ‖(b : K)‖ := by
    simpa using IsUltrametricDist.norm_add_le_max ((c : K) - b) (b : K)
  rw [norm_sub_rev] at h2
  rcases le_max_iff.1 h1 with h3 | h3 <;> rcases le_max_iff.1 h2 with h4 | h4 <;> linarith
end GroundTheory.PAdicHodge.IsPerfectoidField
