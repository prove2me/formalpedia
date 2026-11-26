-- Prove2me | solution 1 for Kyprianou.Ch04.exercise41SmoothApproxDataV9
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T12:42:16.572355+00:00
-- url     : https://prove2.me/submissions/1ba98a68-5038-4150-a2e0-97b7cc37e373

import Mathlib
import Theorems.Thm_Kyprianou_Ch04_exercise41SmoothFunctionApproxV10
import Theorems.Thm_Kyprianou_Ch04_exercise41ApproxEnvelopeV10
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
    (fLeft fRight : ℝ → ℝ)
    (hC1Left : ContDiff ℝ 1 fLeft) (hC1Right : ContDiff ℝ 1 fRight)
    (t : NNReal) :
    let G := fun x : ℝ => if x < 0 then fLeft x - fLeft 0
        else if 0 < x then fRight x - fRight 0 else 0
    let D0 := fun s : ℝ => if X s.toNNReal w < 0 then deriv fLeft (X s.toNNReal w)
        else if 0 < X s.toNNReal w then deriv fRight (X s.toNNReal w) else 0
    let μ := (volume : Measure ℝ).restrict (Icc 0 (t : ℝ))
    ∃ (g : ℕ → ℝ → ℝ) (K : ℝ → ℝ) (B : Ioc (0 : NNReal) t → ℝ),
      (∀ n, ContDiff ℝ 1 (g n)) ∧
      (∀ x : ℝ, Tendsto (fun n => g n x) atTop (𝓝 (G x))) ∧
      (∀ n, AEStronglyMeasurable (fun s => deriv (g n) (X s.toNNReal w)) μ) ∧
      Integrable K μ ∧
      (∀ n, ∀ᵐ s ∂μ, ‖deriv (g n) (X s.toNNReal w)‖ ≤ K s) ∧
      (∀ᵐ s ∂μ, Tendsto (fun n => deriv (g n) (X s.toNNReal w)) atTop (𝓝 (D0 s))) ∧
      Summable B ∧
      (∀ᶠ n in atTop, ∀ k : Ioc (0 : NNReal) t,
        ‖g n (X k w) - g n (Xleft k w)‖ ≤ B k) ∧
      Summable (fun k : Ioc (0 : NNReal) t => ‖G (X k w) - G (Xleft k w)‖) := by
  obtain ⟨g,hg,hlim,hD,hBound⟩ := exercise41SmoothFunctionApproxV10
    fLeft fRight hC1Left hC1Right
  obtain ⟨K,B,hm,hK,hDb,hDl,hB,hJb,hs⟩ :=
    exercise41ApproxEnvelopeV10 X Xleft w hCadlag hLeft (fun s => (hRep s).1)
      g _ _ hg hlim hD hBound t
  exact ⟨g,K,B,hg,hlim,hm,hK,hDb,hDl,hB,hJb,hs⟩
