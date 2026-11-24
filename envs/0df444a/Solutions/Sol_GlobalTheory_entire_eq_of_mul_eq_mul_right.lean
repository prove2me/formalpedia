-- Prove2me | solution 1 for GlobalTheory.entire_eq_of_mul_eq_mul_right
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T22:37:12.475561+00:00
-- url     : https://prove2.me/submissions/3ba32fc6-70cf-45d2-988c-8f6197e4d206

import Mathlib
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_ThetaQuasiPeriodStatement
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_Transl
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_Change
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_DifferentiableOnOfTendstoLocallyUniformlyOn
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_EntireApplyEqOfPeriodicOfSpanReal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_MemPeriodLatticeOfThetaTranslateEqUnitMul
import Theorems.Thm_GlobalTheory_SCV_eqOn_of_eqOn_open


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory.PTheta Complex Matrix Filter Topology
open scoped BigOperators Real
open GlobalTheory
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]
namespace GlobalTheory
theorem _root_.solution {f₁ f₂ θ : E → ℂ} (h₁ : Differentiable ℂ f₁)
    (h₂ : Differentiable ℂ f₂) (hθ : Continuous θ) (hθ0 : θ ≠ 0)
    (h : ∀ z, f₁ z * θ z = f₂ z * θ z) : f₁ = f₂ := by
  obtain ⟨z₀, hz₀⟩ : ∃ z₀, θ z₀ ≠ 0 := by
    by_contra hc
    apply hθ0
    funext z
    by_contra hz
    exact hc ⟨z, hz⟩
  have hW : IsOpen {z | θ z ≠ 0} := isOpen_ne_fun hθ continuous_const
  have hEq : Set.EqOn f₁ f₂ {z | θ z ≠ 0} := fun z hz => mul_right_cancel₀ hz (h z)
  have hall := GlobalTheory.SCV.eqOn_of_eqOn_open isOpen_univ isPreconnected_univ h₁.differentiableOn
    h₂.differentiableOn hW ⟨z₀, hz₀⟩ (Set.subset_univ _) hEq
  funext z
  exact hall (Set.mem_univ z)
end GlobalTheory
