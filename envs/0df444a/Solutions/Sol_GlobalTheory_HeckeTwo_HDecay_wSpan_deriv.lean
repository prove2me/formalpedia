-- Prove2me | solution 1 for GlobalTheory.HeckeTwo.HDecay.wSpan_deriv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T18:21:06.669416+00:00
-- url     : https://prove2.me/submissions/1e078ee4-d3a8-4fd0-a687-8468676ad6f4

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_KFacDifferentiable
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HeckePhiFourierTransformRapidDecay
import Theorems.Thm_GlobalTheory_HeckeTwo_HDecay_hasDerivAt_wF

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField Complex MeasureTheory
open scoped ContDiff FourierTransform
open GlobalTheory GlobalTheory.HeckeTwo GlobalTheory.HeckeTwo.HDecay
variable (σ : ℂ) (y : ℝ)
variable {σ y}
namespace GlobalTheory.HeckeTwo.HDecay
theorem _root_.solution (hy : y ≠ 0) {F : ℝ → ℂ} (hF : F ∈ wSpan σ y) :
    Differentiable ℝ F ∧ deriv F ∈ wSpan σ y := by
  induction hF using Submodule.span_induction with
  | mem F hF =>
    obtain ⟨⟨a, b⟩, rfl⟩ := hF
    refine ⟨fun t => (hasDerivAt_wF σ hy a b t).differentiableAt, ?_⟩
    have e : deriv (wF σ y a b) =
        (-((a : ℂ) + 2 + σ)) • wF σ y (a + 1) b - ((b : ℂ) + σ) • wF σ y a (b + 1) := by
      funext t
      rw [(hasDerivAt_wF σ hy a b t).deriv]
      simp
    rw [e]
    exact Submodule.sub_mem _ (Submodule.smul_mem _ _ (Submodule.subset_span ⟨(a + 1, b), rfl⟩))
      (Submodule.smul_mem _ _ (Submodule.subset_span ⟨(a, b + 1), rfl⟩))
  | zero =>
    refine ⟨differentiable_const 0, ?_⟩
    have e : deriv (0 : ℝ → ℂ) = 0 := by
      funext t
      exact deriv_const t 0
    rw [e]
    exact zero_mem _
  | add F G _ _ hF hG =>
    refine ⟨hF.1.add hG.1, ?_⟩
    have e : deriv (F + G) = deriv F + deriv G := by
      funext t
      exact deriv_add (hF.1 t) (hG.1 t)
    rw [e]
    exact add_mem hF.2 hG.2
  | smul c F _ hF =>
    refine ⟨hF.1.const_smul c, ?_⟩
    have e : deriv (c • F) = c • deriv F := by
      funext t
      exact deriv_const_smul c (hF.1 t)
    rw [e]
    exact Submodule.smul_mem _ c hF.2
end GlobalTheory.HeckeTwo.HDecay
