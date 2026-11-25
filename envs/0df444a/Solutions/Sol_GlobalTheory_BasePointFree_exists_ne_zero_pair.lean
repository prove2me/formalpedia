-- Prove2me | solution 1 for GlobalTheory.BasePointFree.exists_ne_zero_pair
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T02:04:47.439057+00:00
-- url     : https://prove2.me/submissions/53502363-4253-4fd2-b38d-cfb900654f23

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_TorusAtData
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FundamentalDomainPointBound
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_ModerateCoefficientPositivity
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_ExistsNeZeroPair

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.I2
open GlobalTheory GlobalTheory.BasePointFree
namespace GlobalTheory.BasePointFree
theorem _root_.solution (g : ℂ → ℂ) (hg : Differentiable ℂ g) (h1 : g 1 ≠ 0) (m : ℂ)
    (hm : m ≠ 0) : ∃ t : ℂ, g t ≠ 0 ∧ g (-(m * t)) ≠ 0 := by
  by_contra hne
  push Not at hne
  have hg' : Differentiable ℂ (fun t : ℂ => g (-(m * t))) := hg.comp (by fun_prop)
  have A : AnalyticOnNhd ℂ g Set.univ := fun z _ => hg.analyticAt z
  have B : AnalyticOnNhd ℂ (fun t : ℂ => g (-(m * t))) Set.univ := fun z _ => hg'.analyticAt z
  have := AnalyticOnNhd.eq_zero_or_eq_zero_of_mul_eq_zero A B (fun z _ => by
    by_cases h : g z = 0
    · simp [h]
    · simp [hne z h]) isPreconnected_univ
  rcases this with h | h
  · exact h1 (h 1 (Set.mem_univ _))
  · have := h (-m⁻¹) (Set.mem_univ _)
    apply h1
    simpa [hm] using this
end GlobalTheory.BasePointFree
