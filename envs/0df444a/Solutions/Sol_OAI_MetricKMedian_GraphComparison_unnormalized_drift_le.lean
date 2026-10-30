-- Prove2me | solution 1 for OAI.MetricKMedian.GraphComparison.unnormalized_drift_le
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-29T09:51:41.551199+00:00
-- url     : https://prove2.me/submissions/1ec2ef9c-7d80-40fa-b0f5-706d5dc5412f

import Mathlib
import Definitions.Def_OAIQ035K021
import Theorems.Thm_OAI_MetricKMedian_GraphComparison_unnormalized_drift_le_s35

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace MetricKMedian.GraphComparison

open FiniteComparison Analytic

theorem _root_.solution {I : Type*} [Fintype I]
    {μ d N s : I → ℝ} {q K : I → I → ℝ} {x y pHat ζ : ℝ}
    (hx0 : 0 ≤ x) (hx : x ≤ 1) (hy0 : 0 < y) (hy : y ≤ 1)
    (hμ0 : ∀ i, 0 ≤ μ i) (hμ : ∑ i, μ i=y)
    (hd0 : ∀ i, 0 ≤ d i) (hV : 0 < ∑ i, μ i*d i) (hN : ∀ i, 0 ≤ N i)
    (hs0 : ∀ i, 0 ≤ s i) (hs : ∀ i, s i ≤ 1)
    (hq0 : ∀ i t, 0 ≤ q i t) (hq : ∀ i t, q i t ≤ 1)
    (hp0 : 0 ≤ pHat) (hp : pHat ≤ 1/2) (hζ0 : 0 ≤ ζ) (hζ : ζ < 1/4)
    (he : |pHat-P x| ≤ ζ)
    (hcomp : ∀ i t, q i t < 1 → N i*(1-pHat*q i t) ≤ d i+d t)
    (hK : ∀ i t, K i t ≤
      (s i*(1-∑ u, μ u*q i u)+s t*(1-∑ u, μ u*q t u))/2) :
    unnormalizedDrift μ d N s q K x y pHat ≤ 12*ζ*(∑ i, μ i*d i) := by
  first
  | exact _root_.OAI.MetricKMedian.GraphComparison.unnormalized_drift_le_s35
  | (apply _root_.OAI.MetricKMedian.GraphComparison.unnormalized_drift_le_s35 <;> assumption)
  | (intros; apply _root_.OAI.MetricKMedian.GraphComparison.unnormalized_drift_le_s35 <;> assumption)

end MetricKMedian.GraphComparison
end
end

end OAI
end

