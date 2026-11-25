-- Prove2me | solution 1 for GlobalTheory.eventually_eq_zero_of_slices
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T00:35:57.896166+00:00
-- url     : https://prove2.me/submissions/05df8913-9108-4caf-82d2-b411c96e4338

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_TopLePreimageOfValAtNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_TangentBijectionOfValues
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_IsLocalHomeomorphAddMonoidHomOfEventuallyEq
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsOpenPartialHomeomorphAnalytic
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsAnalyticParamInverse

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory
open Metric Set Filter Asymptotics
open scoped Topology
variable {B V : Type*} [NormedAddCommGroup B] [NormedSpace ℂ B] [FiniteDimensional ℂ B]
  [NormedAddCommGroup V] [NormedSpace ℂ V] [FiniteDimensional ℂ V]
omit [FiniteDimensional ℂ B] [FiniteDimensional ℂ V]
namespace GlobalTheory
theorem _root_.solution {W : Type*} [NormedAddCommGroup W] [NormedSpace ℂ W]
    [CompleteSpace V] {F : B × W → V} {b₀ : B} (hF : AnalyticAt ℂ F (b₀, 0))
    (h : ∀ᶠ b in 𝓝 b₀, ∀ᶠ w in 𝓝 (0 : W), F (b, w) = 0) :
    ∀ᶠ q in 𝓝 ((b₀, 0) : B × W), F q = 0 := by
  obtain ⟨s, hs, hsa⟩ := Metric.eventually_nhds_iff_ball.mp hF.eventually_analyticAt
  rw [← ball_prod_same] at hsa
  filter_upwards [prod_mem_nhds (Filter.inter_mem h (ball_mem_nhds b₀ hs)) (ball_mem_nhds 0 hs)]
    with ⟨b, w⟩ ⟨⟨hb, hbs⟩, hw⟩
  have ha : AnalyticOnNhd ℂ (fun w => F (b, w)) (ball 0 s) := fun x hx =>
    AnalyticAt.comp (f := fun x : W => (b, x)) (hsa (b, x) ⟨hbs, hx⟩)
      (analyticAt_const.prod analyticAt_id)
  exact ha.eqOn_zero_of_preconnected_of_eventuallyEq_zero (convex_ball 0 s).isPreconnected
    (mem_ball_self hs) hb hw
end GlobalTheory
