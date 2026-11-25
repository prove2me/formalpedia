-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.WeilSiegel.NoFrame.integrable_of_mul_unimodular
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T17:41:26.433027+00:00
-- url     : https://prove2.me/submissions/0bbd8405-85d6-4537-8e14-07a2212e5040

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_IntegrableOfMulUnimodular

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped Matrix
open MeasureTheory
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.WeilSiegel GlobalTheory.CompanionTheory.WeilSiegel.NoFrame
namespace GlobalTheory.CompanionTheory.WeilSiegel.NoFrame
theorem _root_.solution {α : Type} [MeasurableSpace α] (μ : Measure α) (a b : α → ℂ)
    (hi : Integrable (fun x => a x * b x) μ) (hb : AEStronglyMeasurable b μ) (hb1 : ∀ x, ‖b x‖ = 1) :
    Integrable a μ := by
  have hfun : a = fun x => (a x * b x) * star (b x) := by
    funext x
    rw [mul_assoc, Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq, hb1]
    simp
  have hmeas : AEStronglyMeasurable a μ := by
    rw [hfun]
    exact hi.1.mul hb.star
  refine hi.mono hmeas (Filter.Eventually.of_forall fun x => ?_)
  rw [norm_mul, hb1, mul_one]
end GlobalTheory.CompanionTheory.WeilSiegel.NoFrame
