-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.Kloc.Fresnel.hasTemperateGrowth_expI
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T12:40:52.995801+00:00
-- url     : https://prove2.me/submissions/fae6253d-d85a-4ec3-a5c9-2830d245344f

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_FourierTransformMatrixSpaceInvolution

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Complex
open scoped FourierTransform RealInnerProductSpace SchwartzMap Matrix
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.Kloc GlobalTheory.CompanionTheory.Kloc.Fresnel
namespace GlobalTheory.CompanionTheory.Kloc.Fresnel
theorem _root_.solution : Function.HasTemperateGrowth (fun t : ℝ => cexp (I * t)) := by
  have hd : ∀ n : ℕ, iteratedDeriv n (fun y : ℝ => cexp (I * y)) =
      fun y : ℝ => I ^ n * cexp (I * y) := by
    intro n
    induction n with
    | zero => funext y; simp
    | succ n ih =>
      rw [iteratedDeriv_succ, ih]
      funext y
      have h1 : HasDerivAt (fun y : ℝ => (y : ℂ)) 1 y := by
        simpa using (hasDerivAt_id y).ofReal_comp
      have h : HasDerivAt (fun y : ℝ => I ^ n * cexp (I * y)) (I ^ n * (cexp (I * y) * (I * 1))) y :=
        ((h1.const_mul I).cexp).const_mul (I ^ n)
      rw [h.deriv]; ring
  have hc : ContDiff ℝ (⊤ : ℕ∞) (fun y : ℝ => cexp (I * y)) :=
    (contDiff_const.mul Complex.ofRealCLM.contDiff).cexp
  refine ⟨hc, fun n => ⟨0, 1, fun x => ?_⟩⟩
  rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv, hd, norm_mul, norm_pow, Complex.norm_I, one_pow,
    one_mul, mul_comm I, Complex.norm_exp_ofReal_mul_I]
  simp
end GlobalTheory.CompanionTheory.Kloc.Fresnel
