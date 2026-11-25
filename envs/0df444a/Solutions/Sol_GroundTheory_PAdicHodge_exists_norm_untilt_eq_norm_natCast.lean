-- Prove2me | solution 1 for GroundTheory.PAdicHodge.exists_norm_untilt_eq_norm_natCast
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T00:18:12.366542+00:00
-- url     : https://prove2.me/submissions/27b092ff-95da-4ba9-b399-4773b16e4289

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_PerfectoidField
import Definitions.Def_GroundTheory_PAdicHodge_TiltValuation
import Theorems.Thm_GroundTheory_PAdicHodge_exists_norm_untilt_eq

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
open Filter Topology NNReal
variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K]
variable {p : ℕ} [Fact p.Prime] [IsPerfectoidField K p]
namespace GroundTheory.PAdicHodge
theorem _root_.solution :
    ∃ x : PreTilt (normInteger K) p, ‖((x.untilt : normInteger K) : K)‖ = ‖(p : K)‖ := by
  by_cases hp : (p : K) = 0
  · exact ⟨0, by simp [hp]⟩
  have hp0 : 0 < ‖(p : K)‖ := norm_pos_iff.2 hp
  obtain ⟨ϖ, hϖ, hϖ1⟩ := IsPerfectoidField.exists_norm_mem_Ioo (K := K) (p := p) _
    (IsPerfectoidField.norm_natCast_lt_one (K := K) (p := p))
  have hϖ0 : 0 < ‖ϖ‖ := hp0.trans hϖ
  have hb : ‖(p : K) / ϖ‖ = ‖(p : K)‖ / ‖ϖ‖ := norm_div _ _
  obtain ⟨x, hx⟩ := exists_norm_untilt_eq (p := p) ⟨ϖ, mem_normInteger.2 hϖ1.le⟩ hϖ
  obtain ⟨y, hy⟩ := exists_norm_untilt_eq (p := p)
    ⟨(p : K) / ϖ, mem_normInteger.2 (by rw [hb]; exact div_le_one_of_le₀ hϖ.le hϖ0.le)⟩
    (by
      change ‖(p : K)‖ < ‖(p : K) / ϖ‖
      rw [hb, lt_div_iff₀ hϖ0]
      exact mul_lt_of_lt_one_right hp0 hϖ1)
  refine ⟨x * y, ?_⟩
  rw [untilt_mul, Subring.coe_mul, norm_mul, hx, hy]
  change ‖ϖ‖ * ‖(p : K) / ϖ‖ = _
  rw [hb, mul_div_cancel₀ _ hϖ0.ne']
end GroundTheory.PAdicHodge
