-- Prove2me | solution 1 for Kyprianou.Ch04.exercise41SmoothScalarChainV9
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T12:34:04.968242+00:00
-- url     : https://prove2.me/submissions/40663489-da86-4e37-a2f8-0e325b0a87ff

import Mathlib
import Theorems.Thm_Kyprianou_Ch04_exercise42FixedLipschitzChainRuleV1
import Definitions.Def_Kyprianou_Ch02_LargeJumpProcess
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_Kyprianou_Ch04_PathJumpAndItoIntegral
open MeasureTheory ProbabilityTheory Set Filter Topology AvramDividend.Classical Kyprianou.Ch04
open scoped NNReal ENNReal BigOperators Classical Topology
set_option autoImplicit false
theorem solution
    {Ω : Type}
    (X Xleft : NNReal → Ω → ℝ) (w : Ω) (c : ℝ)
    (hd : 0 < c) (hzero : X 0 w = 0)
    (hCadlag : IsCadlag (fun t : NNReal => X t w))
    (hLeft : ∀ t : NNReal, 0 < t →
      Tendsto (fun s => X s w) (nhdsWithin t (Iio t)) (nhds (Xleft t w)))
    (hNeg : ∀ t : NNReal, 0 < t → X t w ≤ Xleft t w)
    (hRep : ∀ t : NNReal,
      Summable (fun s : Ioc (0 : NNReal) t => |X s w - Xleft s w|) ∧
      X t w = X 0 w + c * (t : ℝ) +
        ∑' s : Ioc (0 : NNReal) t, (X s w - Xleft s w))
    (g : ℝ → ℝ) (hg : ContDiff ℝ 1 g) (t : NNReal) :
    g (X t w) = g (X 0 w) +
      c * (∫ s in Icc (0 : ℝ) (t : ℝ), deriv g (X s.toNNReal w) ∂volume) +
      ∑' s : Ioc (0 : NNReal) t, (g (X s w) - g (Xleft s w)) := by
  letI : MeasurableSpace Ω := ⊤
  let f : ℝ × ℝ → ℝ := fun z => g z.2
  have hf : ContDiff ℝ 1 f := hg.comp contDiff_snd
  have hD (x : ℝ) : fderiv ℝ f (1, x) (0, 1) = deriv g x := by
    have h := ((hg.differentiable (by norm_num) x).hasDerivAt.hasFDerivAt).comp
      (1, x) (ContinuousLinearMap.snd ℝ ℝ ℝ).hasFDerivAt
    change (fderiv ℝ (g ∘ ⇑(ContinuousLinearMap.snd ℝ ℝ ℝ)) (1, x)) (0, 1) = _
    rw [h.fderiv]
    simp
  have H := exercise42FixedLipschitzChainRuleV1 X Xleft w c hd hzero hCadlag
    hLeft hNeg hRep (fun _ => (1 : ℝ)) 0 (LipschitzWith.const 1)
    (by norm_num) (fun _ _ => by norm_num) f hf.contDiffOn t
  simp only [hD, deriv_const, mul_zero, integral_zero, add_zero] at H
  exact H
