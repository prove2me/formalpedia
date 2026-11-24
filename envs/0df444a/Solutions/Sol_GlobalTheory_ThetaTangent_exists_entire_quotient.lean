-- Prove2me | solution 1 for GlobalTheory.ThetaTangent.exists_entire_quotient
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T21:33:04.561824+00:00
-- url     : https://prove2.me/submissions/3c907cee-0d46-4d74-81f7-1732ad39bfeb

import Mathlib
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_ThetaQuasiPeriodStatement
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_Transl
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_Change
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_DifferentiableOnOfTendstoLocallyUniformlyOn
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_LevelThreeSeparatesTangentVectors

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
open GlobalTheory GlobalTheory.ThetaTangent
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
namespace GlobalTheory.ThetaTangent
theorem _root_.solution {θ D : E → ℂ} (hU : Dense {x | θ x ≠ 0})
    (h : ∀ a, ∃ φ : E → ℂ, ∀ᶠ x in 𝓝 a, DifferentiableAt ℂ φ x ∧ D x = φ x * θ x) :
    ∃ ψ : E → ℂ, Differentiable ℂ ψ ∧ ∀ x, D x = ψ x * θ x := by
  choose φ hφ using h
  refine ⟨fun a => φ a a, fun a => ?_, fun x => (hφ x).self_of_nhds.2⟩
  have key : (fun x => φ x x) =ᶠ[𝓝 a] φ a := by
    filter_upwards [(hφ a).eventually_nhds] with x hx
    have hfr : ∃ᶠ y in 𝓝 x, y ∈ {x | θ x ≠ 0} := mem_closure_iff_frequently.mp (hU x)
    have hfr2 : ∃ᶠ y in 𝓝 x, φ x y = φ a y := by
      refine (hfr.and_eventually (hx.and (hφ x))).mono ?_
      rintro y ⟨hy, ⟨-, h1⟩, -, h2⟩
      exact mul_right_cancel₀ hy (h2.symm.trans h1)
    exact tendsto_nhds_unique_of_frequently_eq (hφ x).self_of_nhds.1.continuousAt
      hx.self_of_nhds.1.continuousAt hfr2
  exact (hφ a).self_of_nhds.1.congr_of_eventuallyEq key
end GlobalTheory.ThetaTangent
