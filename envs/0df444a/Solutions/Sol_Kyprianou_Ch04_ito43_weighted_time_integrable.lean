-- Prove2me | solution 1 for Kyprianou.Ch04.ito43_weighted_time_integrable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T23:26:45.535121+00:00
-- url     : https://prove2.me/submissions/e292ce3d-d2dd-4171-9c9f-158d7a1553f9

import Mathlib
import Definitions.Def_LeanLevy_Processes_Cadlag
import Theorems.Thm_Kyprianou_Ch04_exercise41PathCompactV10
import Theorems.Thm_Kyprianou_Ch04_ito43_path_weight_compact_bound
open MeasureTheory Filter Set
open scoped NNReal ENNReal Topology
set_option autoImplicit false
/-- Reuse the compact-path bound and measurable cadlag version from the accepted time regularity proof. -/
theorem solution
    {Ω : Type} [MeasurableSpace Ω] (X L : NNReal → Ω → ℝ) (w : Ω)
    (hc : ProbabilityTheory.IsCadlag (fun s => X s w))
    (hl : ∀ s : NNReal, 0 < s →
      Tendsto (fun r => X r w) (nhdsWithin s (Iio s)) (nhds (L s w)))
    (g : ℝ × ℝ → ℝ) (hg : ContinuousOn g (Ici (0:ℝ) ×ˢ (univ : Set ℝ)))
    (t : NNReal) :
    IntegrableOn (fun s : ℝ => g (s,X s.toNNReal w)) (Icc (0:ℝ) (t:ℝ)) volume := by
  let H : ℝ → ℝ := fun s => g (s,X s.toNNReal w)
  have hG : Continuous (fun z : ℝ × ℝ => g (max 0 z.1,z.2)) :=
    hg.comp_continuous ((continuous_const.max continuous_fst).prodMk continuous_snd)
      (fun z => ⟨show 0 ≤ max 0 z.1 from le_max_left _ _,mem_univ _⟩)
  let H0 : ℝ → ℝ := fun s => g (max 0 s,X s.toNNReal w)
  have hXm := (Kyprianou.Ch04.exercise41PathCompactV10 X L w hc hl t).1
  have hHm : Measurable H0 := hG.measurable.comp (measurable_id.prodMk hXm)
  obtain ⟨M,hM,hX,_⟩ := Kyprianou.Ch04.ito43_path_weight_compact_bound X L w hc hl g hg t
  have hb : IntegrableOn (fun _ : ℝ => M) (Icc 0 (t:ℝ)) volume :=
    integrableOn_const (by rw [Real.volume_Icc]; exact ENNReal.ofReal_ne_top)
  have hbound : ∀ᵐ s ∂volume.restrict (Icc 0 (t:ℝ)), ‖H0 s‖ ≤ M := by
    filter_upwards [ae_restrict_mem (μ := volume)
      (measurableSet_Icc : MeasurableSet (Icc (0:ℝ) (t:ℝ)))] with s hs
    have hh : s.toNNReal ≤ t := by simpa using Real.toNNReal_mono hs.2
    simpa [H0,Real.norm_eq_abs,max_eq_right hs.1,Real.coe_toNNReal _ hs.1]
      using hX s.toNNReal hh
  apply (hb.mono' hHm.aestronglyMeasurable hbound).congr
  filter_upwards [ae_restrict_mem (μ := volume)
    (measurableSet_Icc : MeasurableSet (Icc (0:ℝ) (t:ℝ)))] with s hs
  simp [H0,max_eq_right hs.1]
