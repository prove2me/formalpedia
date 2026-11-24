-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.SmoothParam.hasFDerivAt_weight
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T14:19:24.173207+00:00
-- url     : https://prove2.me/submissions/f61d435f-7b4d-4913-807d-16c6d81b7177

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ContDiffIntegralDensity
import Theorems.Thm_GlobalTheory_CompanionTheory_SmoothParam_hasFDerivAt_partial
import Theorems.Thm_GlobalTheory_CompanionTheory_SmoothParam_contDiff_pderiv
import Theorems.Thm_GlobalTheory_CompanionTheory_SmoothParam_integrable_weight

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Filter Topology
open scoped ContDiff
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SmoothParam
variable {Ω P Y F : Type} [MeasurableSpace Ω] [NormedAddCommGroup P] [NormedSpace ℝ P]
  [FiniteDimensional ℝ P] [NormedAddCommGroup Y] [NormedSpace ℝ Y] [FiniteDimensional ℝ Y]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
namespace GlobalTheory.CompanionTheory.SmoothParam
theorem _root_.solution {ν : Measure Ω} {u : Ω → ℝ} {ψ : Ω → Y} {K : Set Y}
    (hu : Integrable u ν) (hψ : AEStronglyMeasurable ψ ν) (hK : IsCompact K)
    (hψK : ∀ᵐ x ∂ν, ψ x ∈ K) [CompleteSpace F] {H : P × Y → F} (hH : ContDiff ℝ ∞ H) (p₀ : P) :
    HasFDerivAt (fun p => ∫ x, u x • H (p, ψ x) ∂ν)
      (∫ x, u x • pderiv H (p₀, ψ x) ∂ν) p₀ := by
  have hd : Differentiable ℝ H := hH.differentiable (by simp)
  have hc' : Continuous (pderiv H) := (contDiff_pderiv hH).continuous
  obtain ⟨C, hC⟩ := ((isCompact_closedBall p₀ 1).prod hK).exists_bound_of_continuousOn
    (f := pderiv H) hc'.continuousOn
  refine hasFDerivAt_integral_of_dominated_of_fderiv_le
    (F := fun p x => u x • H (p, ψ x)) (F' := fun p x => u x • pderiv H (p, ψ x))
    (bound := fun x => ‖u x‖ * C) (s := Metric.closedBall p₀ 1)
    (Metric.closedBall_mem_nhds p₀ one_pos) ?_ ?_ ?_ ?_ ?_ ?_
  · exact Eventually.of_forall fun p =>
      (integrable_weight hu hψ hK hψK hH.continuous p).aestronglyMeasurable
  · exact integrable_weight hu hψ hK hψK hH.continuous p₀
  · exact (integrable_weight hu hψ hK hψK hc' p₀).aestronglyMeasurable
  · filter_upwards [hψK] with x hx p hp
    rw [norm_smul]
    exact mul_le_mul_of_nonneg_left (hC _ ⟨hp, hx⟩) (norm_nonneg _)
  · exact hu.norm.mul_const C
  · refine Eventually.of_forall fun x p _ => ?_
    have h1 : HasFDerivAt (fun q => H (q, ψ x)) (pderiv H (p, ψ x)) p :=
      ((hasFDerivAt_partial hd p (ψ x)).differentiableAt).hasFDerivAt
    exact h1.const_smul (u x)
end GlobalTheory.CompanionTheory.SmoothParam
