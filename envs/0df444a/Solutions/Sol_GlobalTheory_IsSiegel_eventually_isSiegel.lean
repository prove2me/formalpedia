-- Prove2me | solution 1 for GlobalTheory.IsSiegel.eventually_isSiegel
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T17:56:16.750589+00:00
-- url     : https://prove2.me/submissions/2d80e7a1-7a95-41c2-a567-5abfbff04eba

import Mathlib
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_PeriodLattice
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_ExistsEventuallyNormRiemannThetaTermLe
import Theorems.Thm_GlobalTheory_IsSiegel_exists_eventually_mul_dotProduct_le

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex Matrix Filter Topology MeasureTheory
open scoped Real
noncomputable section
open GlobalTheory
variable {ι κ : Type*}
variable [Fintype ι] [Fintype κ]
namespace GlobalTheory
namespace IsSiegel
theorem _root_.solution {Ω : Matrix ι ι ℂ} (h : IsSiegel Ω) :
    ∀ᶠ Ω' in 𝓝 Ω, Matrix.IsSymm Ω' → IsSiegel Ω' := by
  obtain ⟨c, hc, hY⟩ := h.exists_eventually_mul_dotProduct_le
  filter_upwards [hY] with Ω' hΩ' hs
  refine IsSiegel.of_dotProduct_pos hs fun x hx => lt_of_lt_of_le (mul_pos hc ?_) (hΩ' x)
  obtain ⟨i, hi⟩ := Function.ne_iff.mp hx
  exact Finset.sum_pos' (fun j _ => mul_self_nonneg _) ⟨i, Finset.mem_univ _, mul_self_pos.mpr hi⟩
end IsSiegel
end GlobalTheory
