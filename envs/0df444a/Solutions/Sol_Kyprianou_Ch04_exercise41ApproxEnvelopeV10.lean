-- Prove2me | solution 1 for Kyprianou.Ch04.exercise41ApproxEnvelopeV10
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T12:44:51.275702+00:00
-- url     : https://prove2.me/submissions/d6056f6b-fcde-471b-8e3b-1a63d22e9d90

import Mathlib
import Theorems.Thm_Kyprianou_Ch04_exercise41PathCompactV10
import Theorems.Thm_Kyprianou_Ch04_exercise41BoundedJumpEnvelopeV10
import Theorems.Thm_Kyprianou_Ch04_exercise41DriftEnvelopeV10
import Definitions.Def_Kyprianou_Ch02_LargeJumpProcess
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_Kyprianou_Ch04_PathJumpAndItoIntegral
open MeasureTheory ProbabilityTheory Set Filter Topology AvramDividend.Classical Kyprianou.Ch04
open scoped NNReal ENNReal BigOperators Classical Topology
set_option autoImplicit false
theorem solution
    {Ω : Type}
    (X Xleft : NNReal → Ω → ℝ) (w : Ω)
    (hCadlag : IsCadlag (fun t : NNReal => X t w))
    (hLeft : ∀ t : NNReal, 0 < t →
      Tendsto (fun s => X s w) (nhdsWithin t (Iio t)) (nhds (Xleft t w)))
    (hSum : ∀ t : NNReal,
      Summable (fun s : Ioc (0 : NNReal) t => |X s w - Xleft s w|))
    (g : ℕ → ℝ → ℝ) (G D : ℝ → ℝ)
    (hg : ∀ n, ContDiff ℝ 1 (g n))
    (hlim : ∀ x, Tendsto (fun n => g n x) atTop (𝓝 (G x)))
    (hD : ∀ x, Tendsto (fun n => deriv (g n) x) atTop (𝓝 (D x)))
    (hBound : ∀ R : ℝ, 0 < R → ∃ K : ℝ, 0 ≤ K ∧
      ∀ n x, |x| ≤ R → ‖deriv (g n) x‖ ≤ K)
    (t : NNReal) :
    let μ := (volume : Measure ℝ).restrict (Icc 0 (t : ℝ))
    ∃ (K : ℝ → ℝ) (B : Ioc (0 : NNReal) t → ℝ),
      (∀ n, AEStronglyMeasurable (fun s => deriv (g n) (X s.toNNReal w)) μ) ∧
      Integrable K μ ∧
      (∀ n, ∀ᵐ s ∂μ, ‖deriv (g n) (X s.toNNReal w)‖ ≤ K s) ∧
      (∀ᵐ s ∂μ, Tendsto (fun n => deriv (g n) (X s.toNNReal w)) atTop
        (𝓝 (D (X s.toNNReal w)))) ∧
      Summable B ∧
      (∀ᶠ n in atTop, ∀ k : Ioc (0 : NNReal) t,
        ‖g n (X k w) - g n (Xleft k w)‖ ≤ B k) ∧
      Summable (fun k : Ioc (0 : NNReal) t => ‖G (X k w) - G (Xleft k w)‖) := by
  obtain ⟨hm,R,hR,hX,hL⟩ := exercise41PathCompactV10 X Xleft w hCadlag hLeft t
  obtain ⟨K,hK,hb⟩ := hBound R hR
  have ht (s : ℝ) (hs : s ∈ Icc (0 : ℝ) (t : ℝ)) : |X s.toNNReal w| ≤ R := by
    apply hX
    exact_mod_cast (Real.coe_toNNReal s hs.1).trans_le hs.2
  obtain ⟨hm',hi,hDb,hDl⟩ := exercise41DriftEnvelopeV10
    (fun s => X s.toNNReal w) hm (t : ℝ) R K ht g D hg hD hb
  obtain ⟨B,hB,hJb,hs⟩ := exercise41BoundedJumpEnvelopeV10
    (fun s : Ioc (0 : NNReal) t => X s w)
    (fun s : Ioc (0 : NNReal) t => Xleft s w) R K
    (fun s => hX s s.2.2) (fun s => hL s s.2.1 s.2.2)
    g G hg hlim hb (hSum t)
  exact ⟨fun _ => K,B,hm',hi,hDb,hDl,hB,hJb,hs⟩
