-- Prove2me | solution 1 for Kyprianou.Ch04.ito43_weighted_time_path_regular
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T22:21:28.375081+00:00
-- url     : https://prove2.me/submissions/60754c00-a179-4a85-ba8d-07c8da96a960

import Mathlib
import Definitions.Def_Kyprianou_Ch02_LargeJumpProcess
import Definitions.Def_Kyprianou_Ch02_CompensatedSmallJumpBand
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_LeanLevy_Levy_LevyKhintchine
import Definitions.Def_Kyprianou_Ch01_LevyTripletExponent
import Definitions.Def_Kyprianou_Ch04_PathJumpAndItoIntegral
import Definitions.Def_Kyprianou_Ch04_StochasticIntegralUCPV2
import Theorems.Thm_Kyprianou_Ch04_exercise41PathCompactV10
import Theorems.Thm_Kyprianou_Ch04_ito43_path_weight_compact_bound
open MeasureTheory Filter ProbabilityTheory
open scoped NNReal ENNReal
set_option autoImplicit false
open Kyprianou.Ch04
open scoped Topology

open Set
theorem solution {Ω : Type} [MeasurableSpace Ω] (X L : NNReal → Ω → ℝ) (w : Ω)
    (hc : IsCadlag (fun s => X s w))
    (hl : ∀ s : NNReal, 0 < s → Tendsto (fun t => X t w) (nhdsWithin s (Iio s)) (nhds (L s w)))
    (g : ℝ × ℝ → ℝ) (hg : ContinuousOn g (Ici (0:ℝ) ×ˢ (univ : Set ℝ))) (T : NNReal) :
    let J : NNReal → ℝ := fun t =>
      ∫ s in Icc (0:ℝ) (t:ℝ), g (s,X s.toNNReal w) ∂volume
    Continuous J ∧ ∃ M : ℝ, ∀ t ≤ T, |J t| ≤ M := by
  intro J
  let H : ℝ → ℝ := fun s => g (s,X s.toNNReal w)
  have hG : Continuous (fun z : ℝ × ℝ => g (max 0 z.1,z.2)) :=
    hg.comp_continuous ((continuous_const.max continuous_fst).prodMk continuous_snd)
      (fun z => ⟨show 0 ≤ max 0 z.1 from le_max_left _ _,mem_univ _⟩)
  let H0 : ℝ → ℝ := fun s => g (max 0 s,X s.toNNReal w)
  have hXm := (exercise41PathCompactV10 X L w hc hl T).1
  have hHm : Measurable H0 := hG.measurable.comp (measurable_id.prodMk hXm)
  have heq (s : ℝ) (hs : 0 ≤ s) : H s = H0 s := by simp [H,H0,max_eq_right hs]
  have hi (b : ℝ) : IntegrableOn H (Icc 0 b) volume := by
    obtain ⟨M,hM,hX,hL⟩ := ito43_path_weight_compact_bound X L w hc hl g hg b.toNNReal
    have hb : IntegrableOn (fun _ : ℝ => M) (Icc 0 b) volume := integrableOn_const (by rw [Real.volume_Icc]; exact ENNReal.ofReal_ne_top)
    have hbound : ∀ᵐ s ∂volume.restrict (Icc 0 b), ‖H0 s‖ ≤ M := by
      filter_upwards [ae_restrict_mem (μ := volume) (measurableSet_Icc : MeasurableSet (Icc (0:ℝ) b))] with s hs
      have hh : s.toNNReal ≤ b.toNNReal := Real.toNNReal_mono hs.2
      have h := hX s.toNNReal hh
      simpa [H0,Real.norm_eq_abs,max_eq_right hs.1,Real.coe_toNNReal _ hs.1] using h
    have hi0 := hb.mono' hHm.aestronglyMeasurable hbound
    apply hi0.congr
    filter_upwards [ae_restrict_mem (μ := volume) (measurableSet_Icc : MeasurableSet (Icc (0:ℝ) b))] with s hs
    exact (heq s hs.1).symm
  have hJ : Continuous J := by
    rw [continuous_iff_continuousAt]
    intro t
    let b : NNReal := t+1
    have hc := intervalIntegral.continuousOn_primitive_Icc (hi (b:ℝ))
    have hb : t < b := lt_add_of_pos_right t (by norm_num)
    have hcont : ContinuousOn J (Icc 0 b) := by
      exact hc.comp continuous_subtype_val.continuousOn (fun x hx => by
        exact ⟨x.coe_nonneg,by exact_mod_cast hx.2⟩)
    exact hcont.continuousAt (by
      have h : Iio b ∈ nhds t := Iio_mem_nhds hb
      apply Filter.mem_of_superset h
      intro x hx
      exact ⟨zero_le,hx.le⟩)
  obtain ⟨M,hM⟩ := (isCompact_Icc : IsCompact (Icc (0:NNReal) T)).bddAbove_image hJ.abs.continuousOn
  exact ⟨hJ,M,fun t ht => hM ⟨t,⟨zero_le,ht⟩,rfl⟩⟩
