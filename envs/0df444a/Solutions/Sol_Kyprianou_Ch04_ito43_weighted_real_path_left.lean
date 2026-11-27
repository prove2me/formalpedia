-- Prove2me | solution 1 for Kyprianou.Ch04.ito43_weighted_real_path_left
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T23:20:25.649086+00:00
-- url     : https://prove2.me/submissions/d7efae8c-f0fa-4089-8b3d-edab0f4a3921

import Mathlib
import Definitions.Def_LeanLevy_Processes_Cadlag
open Set Filter
open scoped Topology ENNReal NNReal
set_option autoImplicit false
/-- Compose the left-sided path limit with the continuous weight, using positive time. -/
theorem solution
    {Ω : Type} [MeasurableSpace Ω] (X : NNReal → Ω → ℝ) (w : Ω)
    (g : ℝ × ℝ → ℝ) (hg : ContinuousOn g (Ici (0:ℝ) ×ˢ (univ : Set ℝ)))
    (L : NNReal → Ω → ℝ)
    (hl : ∀ s : NNReal, 0 < s →
      Tendsto (fun r => X r w) (nhdsWithin s (Iio s)) (nhds (L s w)))
    (t : ℝ) (ht : 0 < t) :
    Tendsto (fun r : ℝ => g (r,X r.toNNReal w)) (nhdsWithin t (Iio t))
      (nhds (g (t,L t.toNNReal w))) := by
  have ht' : 0 < t.toNNReal := by
    change (0:ℝ) < max t 0
    exact ht.trans_le (le_max_left _ _)
  have hm : Tendsto Real.toNNReal (nhdsWithin t (Iio t))
      (nhdsWithin t.toNNReal (Iio t.toNNReal)) := by
    refine tendsto_nhdsWithin_iff.mpr ⟨?_,?_⟩
    · exact continuous_real_toNNReal.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with r hr
      change max r 0 < max t 0
      rw [max_eq_left ht.le]
      exact max_lt hr ht
  have hx := (hl t.toNNReal ht').comp hm
  have hid : Tendsto (fun r : ℝ => r) (nhdsWithin t (Iio t)) (nhds t) :=
    continuousAt_id.tendsto.mono_left nhdsWithin_le_nhds
  have hpair : Tendsto (fun r : ℝ => (r,X r.toNNReal w)) (nhdsWithin t (Iio t))
      (nhdsWithin (t,L t.toNNReal w) (Ici (0:ℝ) ×ˢ (univ : Set ℝ))) := by
    refine tendsto_nhdsWithin_iff.mpr ⟨hid.prodMk_nhds hx,?_⟩
    have hpos : ∀ᶠ r in nhdsWithin t (Iio t), 0 < r :=
      nhdsWithin_le_nhds (Ioi_mem_nhds ht)
    filter_upwards [hpos] with r hr
    exact ⟨hr.le,mem_univ _⟩
  exact (hg (t,L t.toNNReal w) ⟨ht.le,mem_univ _⟩).tendsto.comp hpair
