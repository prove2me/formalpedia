-- Prove2me | solution 1 for GroundTheory.PAdicHodge.IsPerfectoidField.exists_untilt_eq_p_mul_unit
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T00:25:39.933392+00:00
-- url     : https://prove2.me/submissions/6975cdc2-9cea-4943-a2c2-7598e6011b8b

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_PerfectoidField
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_LeSpanSingletonOfForallMemEq
import Definitions.Def_GroundTheory_PAdicHodge_KerTheta
import Theorems.Thm_GroundTheory_PAdicHodge_IsPerfectoidField_isUnit_iff_norm_eq_one
import Theorems.Thm_GroundTheory_PAdicHodge_IsPerfectoidField_untilt_zero
import Theorems.Thm_GroundTheory_PAdicHodge_IsPerfectoidField_exists_norm_untilt_eq

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
namespace GroundTheory.PAdicHodge.IsPerfectoidField
theorem _root_.solution :
    ∃ ϖ : 𝒪♭, ∃ u : 𝒪, IsUnit u ∧ PreTilt.untilt ϖ = p * u := by
  by_cases hpO : (p : 𝒪) = 0
  · exact ⟨0, 1, isUnit_one, by rw [untilt_zero, hpO, zero_mul]⟩
  have hpK : (p : K) ≠ 0 := fun h => hpO (Subtype.ext (by simpa using h))
  have hp1 : ‖(p : K)‖ < 1 := IsPerfectoidField.norm_natCast_lt_one (K := K) (p := p)
  have hpos : 0 < ‖(p : K)‖ := norm_pos_iff.2 hpK
  obtain ⟨x, hx1, hx2⟩ := IsPerfectoidField.exists_norm_mem_Ioo (K := K) (p := p) _ hp1
  have hxpos : 0 < ‖x‖ := hpos.trans hx1
  have hx0 : x ≠ 0 := norm_pos_iff.1 hxpos
  have hy : ‖(p : K) / x‖ ≤ 1 := by
    rw [norm_div]; exact div_le_one_of_le₀ hx1.le hxpos.le
  obtain ⟨a₁, ha₁⟩ := exists_norm_untilt_eq (K := K) p (b := ⟨x, mem_normInteger.2 hx2.le⟩) hx1
  obtain ⟨a₂, ha₂⟩ := exists_norm_untilt_eq (K := K) p (b := ⟨(p : K) / x, mem_normInteger.2 hy⟩)
    (by
      show ‖(p : K)‖ < ‖(p : K) / x‖
      rw [norm_div, lt_div_iff₀ hxpos]
      exact mul_lt_of_lt_one_right hpos hx2)
  have hϖ : ‖((PreTilt.untilt (a₁ * a₂) : 𝒪) : K)‖ = ‖(p : K)‖ := by
    rw [map_mul, Subring.coe_mul, norm_mul, ha₁, ha₂]
    show ‖x‖ * ‖(p : K) / x‖ = ‖(p : K)‖
    rw [norm_div, mul_div_cancel₀ _ hxpos.ne']
  have hu : ‖((PreTilt.untilt (a₁ * a₂) : 𝒪) : K) / p‖ = 1 := by
    rw [norm_div, hϖ, div_self hpos.ne']
  refine ⟨a₁ * a₂, ⟨_, mem_normInteger.2 hu.le⟩, isUnit_iff_norm_eq_one.2 hu, ?_⟩
  ext
  simp only [Subring.coe_mul]
  rw [show ((p : 𝒪) : K) = (p : K) by simp, mul_div_cancel₀ _ hpK]
end GroundTheory.PAdicHodge.IsPerfectoidField
