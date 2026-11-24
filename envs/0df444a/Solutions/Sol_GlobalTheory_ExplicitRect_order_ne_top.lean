-- Prove2me | solution 1 for GlobalTheory.ExplicitRect.order_ne_top
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T14:49:14.355459+00:00
-- url     : https://prove2.me/submissions/233b2f53-b979-42d9-8c38-1eeba472e0ad

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_BdIntEqZeroOfPrimitive
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_CompletedLFunctionNeZeroOfReNonpos
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_AnalyticAtDslope
import Theorems.Thm_GlobalTheory_ExplicitRect_analyticOff

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex DirichletCharacter ArithmeticFunction MeasureTheory Filter Topology
open GlobalTheory GlobalTheory.ExplicitRect
namespace GlobalTheory.ExplicitRect
theorem _root_.solution {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) {ρ : ℂ} (hρ : ρ ≠ 1) :
    analyticOrderAt (LFunction χ) ρ ≠ ⊤ := by
  have hU : IsPreconnected ({1}ᶜ : Set ℂ) :=
    (isConnected_compl_singleton_of_one_lt_rank (by rw [Complex.rank_real_complex]; norm_num) 1).isPreconnected
  have h2 : analyticOrderAt (LFunction χ) 2 ≠ ⊤ := by
    intro htop
    have hne : LFunction χ 2 ≠ 0 :=
      DirichletCharacter.LFunction_ne_zero_of_one_le_re χ (.inr (by norm_num)) (by norm_num)
    exact hne (analyticOrderAt_eq_top.mp htop).self_of_nhds
  exact (analyticOff χ).analyticOrderAt_ne_top_of_isPreconnected hU
    (by norm_num : (2 : ℂ) ∈ ({1}ᶜ : Set ℂ)) hρ h2
end GlobalTheory.ExplicitRect
