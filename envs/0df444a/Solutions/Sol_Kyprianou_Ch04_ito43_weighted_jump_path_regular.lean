-- Prove2me | solution 1 for Kyprianou.Ch04.ito43_weighted_jump_path_regular
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T22:22:18.217937+00:00
-- url     : https://prove2.me/submissions/ddaa76ff-2823-4447-8f66-d3d66db8c9a1

import Mathlib
import Definitions.Def_Kyprianou_Ch02_LargeJumpProcess
import Definitions.Def_Kyprianou_Ch02_CompensatedSmallJumpBand
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_LeanLevy_Levy_LevyKhintchine
import Definitions.Def_Kyprianou_Ch01_LevyTripletExponent
import Definitions.Def_Kyprianou_Ch04_PathJumpAndItoIntegral
import Definitions.Def_Kyprianou_Ch04_StochasticIntegralUCPV2
import Theorems.Thm_Kyprianou_Ch04_ito43_general_kernel_jump_series
import Theorems.Thm_Kyprianou_Ch04_ito43_path_weight_compact_bound
import Theorems.Thm_Kyprianou_Ch02_locallyAbsSummableCumulativeJumpSeriesRightContinuousV1
import Theorems.Thm_Kyprianou_Ch04_exercise41CadlagPhysicalJumpsCountableV17
import Theorems.Thm_Kyprianou_Ch04_ito43_path_jump_kernel_energy_bound
open MeasureTheory Filter ProbabilityTheory
open scoped NNReal ENNReal
set_option autoImplicit false
open Kyprianou.Ch04
open scoped Topology

open Set
theorem solution {Ω : Type} [MeasurableSpace Ω] (X L : NNReal → Ω → ℝ) (w : Ω)
    (hc : IsCadlag (fun s => X s w))
    (hl : ∀ s : NNReal, 0 < s → Tendsto (fun t => X t w) (nhdsWithin s (Iio s)) (nhds (L s w)))
    (g : ℝ × ℝ → ℝ) (hg : ContinuousOn g (Ici (0:ℝ) ×ˢ (univ : Set ℝ))) (T : NNReal)
    (hs : ∀ H : NNReal, Summable (fun s : Ioc (0:NNReal) H => (X s w-L s w)^2)) :
    let J : NNReal → ℝ := fun t =>
      ∫ z in Icc (0:ℝ) (t:ℝ) ×ˢ (univ : Set ℝ),
        g (z.1,L z.1.toNNReal w)*z.2^2/2 ∂(pathJumpMeasure X L w)
    (∀ t, ContinuousWithinAt J (Ici t) t) ∧ ∃ M : ℝ, ∀ t ≤ T, |J t| ≤ M := by
  intro J
  let K : NNReal → ℝ → ℝ → ℝ := fun s x z => g ((s:ℝ),x)*z^2/2
  let W : NNReal → ℝ := fun s => K s (L s w) (X s w-L s w)
  have h0 (s : NNReal) (x : ℝ) : K s x 0 = 0 := by simp [K]
  have heq (t : NNReal) : J t = ∑' s : Ioc (0:NNReal) t, W s := by
    rw [← ito43_general_kernel_jump_series X L w hc hl K h0 t]
    apply setIntegral_congr_fun (measurableSet_Icc.prod MeasurableSet.univ)
    intro z hz
    dsimp [J,K]
    rw [max_eq_left hz.1.1]
  have hsum (H : NNReal) : Summable (fun s : Ioc (0:NNReal) H => |W s|) := by
    obtain ⟨M,hM,_,hL⟩ := ito43_path_weight_compact_bound X L w hc hl g hg H
    apply Summable.of_nonneg_of_le (fun _ => abs_nonneg _) _ ((hs H).mul_left (M/2))
    intro s
    dsimp [W,K]
    rw [abs_div,abs_mul,abs_of_nonneg (sq_nonneg (X s w-L s w)),abs_of_nonneg (by norm_num : (0:ℝ) ≤ 2)]
    have h := mul_le_mul_of_nonneg_right (hL s s.2.1 s.2.2) (sq_nonneg (X s w-L s w))
    linarith
  constructor
  · intro t
    have hfun : J = (fun u => ∑' s : Ioc (0:NNReal) u, W s) := funext heq
    change ContinuousWithinAt J (Ici t) t
    rw [hfun]
    exact Kyprianou.Ch02.locallyAbsSummableCumulativeJumpSeriesRightContinuousV1 W hsum t
  · obtain ⟨M,hM,_,hL⟩ := ito43_path_weight_compact_bound X L w hc hl g hg T
    have hJ := exercise41CadlagPhysicalJumpsCountableV17 (fun s => X s w)
      (fun s => L s w) (fun s => (hc s).1) hl
    refine ⟨(M/2)*(∑' s : Ioc (0:NNReal) T, (X s w-L s w)^2),fun t ht => ?_⟩
    exact (ito43_path_jump_kernel_energy_bound X L w hJ T t ht (M/2) (by positivity) (hs T)
      (fun z => g (z.1,L z.1.toNNReal w)*z.2^2/2) (by
        intro s hs' hst
        simp only [Real.toNNReal_coe]
        rw [abs_div,abs_mul,abs_of_nonneg (sq_nonneg (X s w-L s w)),abs_of_nonneg (by norm_num : (0:ℝ) ≤ 2)]
        have h := mul_le_mul_of_nonneg_right (hL s hs' (hst.trans ht)) (sq_nonneg (X s w-L s w))
        linarith)).2
