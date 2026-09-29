-- Prove2me | solution 1 for NonsmoothNewton.AugLagrangian.tangency_4_7
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-28T23:29:39.844976+00:00
-- url     : https://prove2.me/submissions/a08d345c-71a0-47a3-acfb-21f97d8fda19

import Mathlib
import Definitions.Def_NonsmoothNewton_Shared_clarkeJac
import Definitions.Def_NonsmoothNewton_AugLagrangian_SemismoothAt
import Definitions.Def_NonsmoothNewton_AugLagrangian_augLagrangian
open Filter Topology

namespace NonsmoothNewton.AugLagrangian

end NonsmoothNewton.AugLagrangian

open NonsmoothNewton.AugLagrangian

theorem solution {n : ℕ} (r : ℝ) (hr : 0 < r) (g : EuclideanSpace ℝ (Fin n) → ℝ)
    (hg : ContDiff ℝ 2 g) (xbar : EuclideanSpace ℝ (Fin n)) (sbar : ℝ)
    (h43 : sbar + r * g xbar = 0)
    (h : EuclideanSpace ℝ (Fin n)) (α : ℝ)
    (hj : ℕ → EuclideanSpace ℝ (Fin n)) (αj tj : ℕ → ℝ)
    (hhj : Tendsto hj atTop (𝓝 h)) (hαj : Tendsto αj atTop (𝓝 α))
    (htj : Tendsto tj atTop (𝓝[>] 0))
    (h46 : ∀ j, sbar + tj j * αj j + r * g (xbar + tj j • hj j) = 0) :
    α + r * fderiv ℝ g xbar h = 0 := by
  have hdiff : DifferentiableAt ℝ g xbar :=
    (hg.differentiable (by norm_num)) xbar
  have hfd : HasFDerivWithinAt g (fderiv ℝ g xbar) Set.univ xbar :=
    hdiff.hasFDerivAt.hasFDerivWithinAt
  have ht0 : Tendsto tj atTop (𝓝 0) := tendsto_nhdsWithin_iff.1 htj |>.1
  have htpos : ∀ᶠ j in atTop, 0 < tj j := tendsto_nhdsWithin_iff.1 htj |>.2
  have hd0 : Tendsto (fun j => tj j • hj j) atTop (𝓝 0) := by
    simpa using ht0.smul hhj
  have hcd : Tendsto (fun j => (tj j)⁻¹ • (tj j • hj j)) atTop (𝓝 h) := by
    refine hhj.congr' ?_
    filter_upwards [htpos] with j hj0
    rw [smul_smul, inv_mul_cancel₀ hj0.ne', one_smul]
  have hlim := hfd.lim hd0 (Eventually.of_forall fun _ => Set.mem_univ _) hcd
  have hlim2 : Tendsto (fun j => -r * ((tj j)⁻¹ • (g (xbar + tj j • hj j) - g xbar))) atTop
      (𝓝 (-r * fderiv ℝ g xbar h)) := hlim.const_mul _
  have heq : αj =ᶠ[atTop] fun j => -r * ((tj j)⁻¹ • (g (xbar + tj j • hj j) - g xbar)) := by
    filter_upwards [htpos] with j hj0
    have e := h46 j
    rw [smul_eq_mul]
    field_simp
    linarith
  have := tendsto_nhds_unique (hαj.congr' heq) hlim2
  rw [this]
  ring
