-- Prove2me | solution 1 for Kyprianou.Ch04.ito43_qv_time_path_step_error
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T23:40:16.43375+00:00
-- url     : https://prove2.me/submissions/16bd39ed-3413-43d6-9909-f507570d0705

import Mathlib
import Definitions.Def_LeanLevy_Processes_Cadlag
import Theorems.Thm_Kyprianou_Ch04_ito43_qv_time_step_error
import Theorems.Thm_Kyprianou_Ch04_ito43_weighted_time_integrable
open MeasureTheory Filter ProbabilityTheory Set
open scoped NNReal ENNReal Topology
set_option autoImplicit false
/-- Transport the nonnegative time-coordinate approximation. -/
theorem solution
    {Ω : Type} [MeasurableSpace Ω] (X L : NNReal → Ω → ℝ) (w : Ω)
    (hc : IsCadlag (fun s => X s w))
    (hl : ∀ s : NNReal, 0 < s →
      Tendsto (fun r => X r w) (nhdsWithin s (Iio s)) (nhds (L s w)))
    (g : ℝ × ℝ → ℝ) (hg : ContinuousOn g (Ici (0:ℝ) ×ˢ (univ : Set ℝ)))
    (T t : NNReal) (ht : t ≤ T) (δ : ℝ) (hδ : 0 ≤ δ)
    (m : ℕ) (b : ℕ → NNReal) (c : ℕ → ℝ)
    (hW : ∀ s ≤ T, |g ((s:ℝ),X s w) -
      ∑ i ∈ Finset.range m, c i * (if b i ≤ s then (1:ℝ) else 0)| ≤ δ) :
    |(∫ s in Icc (0:ℝ) (t:ℝ), g (s,X s.toNNReal w) ∂volume) -
      ∑ i ∈ Finset.range m, c i *
        ((∫ s in Icc (0:ℝ) (t:ℝ), (1:ℝ) ∂volume) -
          ∫ s in Icc (0:ℝ) ((min t (b i):NNReal):ℝ), (1:ℝ) ∂volume)| ≤
      δ * (T:ℝ) := by
  have h := Kyprianou.Ch04.ito43_qv_time_step_error
    (fun s => g (s,X s.toNNReal w)) t
    (Kyprianou.Ch04.ito43_weighted_time_integrable X L w hc hl g hg t)
    δ m b c (by
      intro s hs
      have hst : s.toNNReal ≤ t := by simpa using Real.toNNReal_mono hs.2
      have hco := Real.coe_toNNReal s hs.1
      have hiff (i : ℕ) : b i ≤ s.toNNReal ↔ (b i:ℝ) ≤ s := by
        change (b i:ℝ) ≤ (s.toNNReal:ℝ) ↔ _
        rw [hco]
      simpa only [hco,hiff] using hW s.toNNReal (hst.trans ht))
  exact h.trans (mul_le_mul_of_nonneg_left (show (t:ℝ) ≤ (T:ℝ) from ht) hδ)
