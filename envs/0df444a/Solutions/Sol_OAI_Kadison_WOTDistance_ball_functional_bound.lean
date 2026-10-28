-- Prove2me | solution 1 for OAI.Kadison.WOTDistance.ball_functional_bound
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T10:07:11.223402+00:00
-- url     : https://prove2.me/submissions/4f5db855-239f-49dd-8016-de629877103b

import Mathlib
import Definitions.Def_OAIQ039C018

section
-- module Solutions.OAIQ039_CM.Commutator_ArvesonDistance
attribute [-instance] _root_.OAI.Kadison.UnitaryDualAction.action
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

open scoped BigOperators InnerProductSpace Pointwise

open ContinuousLinearMapWOT

namespace Kadison.WOTDistance

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

lemma ball_functional_bound_oai (φ : (H →WOT[ℂ] H) →L[ℂ] ℂ)
    {c u : ℝ} (hc : 0 < c) (hu : 0≤u)
    (hφ : ∀ T∈normBall (H:=H) c, (φ T).re≤u) :
    c*‖φ.comp ContinuousLinearMap.WOTofCLM‖≤u := by
  let ψ : StrongDual ℂ (H →L[ℂ] H) := φ.comp ContinuousLinearMap.WOTofCLM
  let ψr : StrongDual ℝ (H →L[ℂ] H) := (StrongDual.extendRCLikeₗᵢ (𝕜:=ℂ)).symm ψ
  have hn : ‖ψr‖=‖ψ‖ := LinearIsometryEquiv.norm_map _ _
  have hnorm : ‖ψr‖≤u/c := by
    apply ContinuousLinearMap.opNorm_le_of_unit_norm (div_nonneg hu hc.le)
    intro T hT
    have hp := hφ (ofCLM (c • T)) (by
      change ‖c • T‖ ≤ c
      simp [norm_smul,hT,abs_of_pos hc])
    have hm := hφ (ofCLM ((-c) • T)) (by
      change ‖(-c) • T‖ ≤ c
      simp [norm_smul,hT,abs_of_pos hc])
    have hp' : c*ψr T≤u := by
      change ψr (c • T)≤u at hp
      simpa only [map_smul,smul_eq_mul] using hp
    have hm' : -(c*ψr T)≤u := by
      change ψr ((-c) • T)≤u at hm
      simpa only [map_smul,smul_eq_mul,neg_mul] using hm
    rw [Real.norm_eq_abs,abs_le]
    constructor
    · apply (le_of_mul_le_mul_left ?_ hc)
      rw [mul_neg, mul_div_cancel₀ _ hc.ne']
      linarith
    · exact (le_div_iff₀ hc).mpr (by simpa [mul_comm] using hp')
  rw [hn] at hnorm
  simpa only [mul_comm] using (le_div_iff₀ hc).mp hnorm

end Kadison.WOTDistance

end

end
end

end OAI
end

theorem solution.{u_1} : type_of% @OAI.Kadison.WOTDistance.ball_functional_bound_oai.{u_1} := @OAI.Kadison.WOTDistance.ball_functional_bound_oai.{u_1}
