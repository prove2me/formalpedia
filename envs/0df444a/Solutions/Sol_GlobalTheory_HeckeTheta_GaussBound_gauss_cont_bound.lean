-- Prove2me | solution 1 for GlobalTheory.HeckeTheta.GaussBound.gauss_cont_bound
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T17:55:55.114363+00:00
-- url     : https://prove2.me/submissions/7559760e-06f5-44d9-8f2a-41ffad693934

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_EmbAApply
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IntegrableWeightedHeckeThetaKernelHalfSpace
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_GaussianHarmonicProductKernelContinuousBounded
import Theorems.Thm_GlobalTheory_HeckeTheta_Decay_continuous_hmon
import Theorems.Thm_GlobalTheory_HeckeTheta_Decay_norm_gauss_le


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField MeasureTheory
open scoped RealInnerProductSpace FourierTransform
noncomputable section
open GlobalTheory GlobalTheory.HeckeTheta GlobalTheory.HeckeTheta.GaussBound
open GlobalTheory.HeckeTheta
namespace GlobalTheory.HeckeTheta.GaussBound
theorem _root_.solution : ∀ (I : Type) [Fintype I] (n : I → ℤ), Continuous (fun w : EuclideanSpace ℂ I => GlobalTheory.HeckeTheta.gauss n (WithLp.ofLp w)) ∧ ∃ C : ℝ, ∀ w : EuclideanSpace ℂ I, ‖GlobalTheory.HeckeTheta.gauss n (WithLp.ofLp w)‖ ≤ C * Real.exp (-Real.pi * ‖w‖ ^ 2) := by
  intro I _ n
  refine ⟨?_, ⟨Decay.gC n, fun w => ?_⟩⟩
  · unfold gauss
    refine continuous_finset_prod _ fun i _ => ?_
    have hc : Continuous fun w : EuclideanSpace ℂ I => (WithLp.ofLp w) i :=
      (continuous_apply i).comp (PiLp.continuous_ofLp 2 _)
    exact ((Decay.continuous_hmon _).comp hc).mul (by fun_prop)
  · have h := Decay.norm_gauss_le n (WithLp.ofLp w)
    have e : ‖w‖ ^ 2 = ∑ i, ‖(WithLp.ofLp w) i‖ ^ 2 := EuclideanSpace.norm_sq_eq w
    rw [e]; exact h
end GlobalTheory.HeckeTheta.GaussBound
