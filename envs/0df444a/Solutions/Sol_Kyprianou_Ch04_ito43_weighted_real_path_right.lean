-- Prove2me | solution 1 for Kyprianou.Ch04.ito43_weighted_real_path_right
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T23:20:25.291967+00:00
-- url     : https://prove2.me/submissions/6f3237a0-8130-4aba-8dd7-537c1cf36682

import Mathlib
import Definitions.Def_LeanLevy_Processes_Cadlag
open Set Filter
open scoped Topology ENNReal NNReal
set_option autoImplicit false
/-- Compose the right-sided path limit with the continuous weight, using nonnegative real time. -/
theorem solution
    {Ω : Type} [MeasurableSpace Ω] (X : NNReal → Ω → ℝ) (w : Ω)
    (g : ℝ × ℝ → ℝ) (hg : ContinuousOn g (Ici (0:ℝ) ×ˢ (univ : Set ℝ)))
    (hc : ProbabilityTheory.IsCadlag (fun s => X s w))
    (t : ℝ) (ht : 0 ≤ t) :
    ContinuousWithinAt (fun r : ℝ => g (r, X r.toNNReal w)) (Ici t) t := by
  have hm : Tendsto Real.toNNReal (nhdsWithin t (Ici t))
      (nhdsWithin t.toNNReal (Ici t.toNNReal)) := by
    refine tendsto_nhdsWithin_iff.mpr ⟨?_,?_⟩
    · exact continuous_real_toNNReal.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with r hr
      change max t 0 ≤ max r 0
      exact max_le_max hr le_rfl
  have hx := (hc t.toNNReal).1.tendsto.comp hm
  have hid : Tendsto (fun r : ℝ => r) (nhdsWithin t (Ici t)) (nhds t) :=
    continuousAt_id.tendsto.mono_left nhdsWithin_le_nhds
  have hpair : Tendsto (fun r : ℝ => (r,X r.toNNReal w)) (nhdsWithin t (Ici t))
      (nhdsWithin (t,X t.toNNReal w) (Ici (0:ℝ) ×ˢ (univ : Set ℝ))) := by
    refine tendsto_nhdsWithin_iff.mpr ⟨hid.prodMk_nhds hx,?_⟩
    filter_upwards [self_mem_nhdsWithin] with r hr
    exact ⟨ht.trans hr,mem_univ _⟩
  exact (hg (t,X t.toNNReal w) ⟨ht,mem_univ _⟩).tendsto.comp hpair
