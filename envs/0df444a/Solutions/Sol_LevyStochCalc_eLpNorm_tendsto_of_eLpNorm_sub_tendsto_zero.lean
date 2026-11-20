-- Prove2me | solution 1 for LevyStochCalc.eLpNorm_tendsto_of_eLpNorm_sub_tendsto_zero
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-19T06:16:22.007178+00:00
-- url     : https://prove2.me/submissions/b5b9d6cd-2c97-4ad9-b36e-9d21738e5b1a

import Definitions.Def_LevyStochCalc_Basic_F000

open MeasureTheory
open scoped NNReal ENNReal

namespace LevyStochCalc

theorem _root_.solution
    {α E : Type*} [MeasurableSpace α] [NormedAddCommGroup E]
    {p : ℝ≥0∞} (hp : 1 ≤ p) {μ : Measure α}
    {f : α → E} {fn : ℕ → α → E}
    (hf : MeasureTheory.AEStronglyMeasurable f μ)
    (hfn : ∀ n, MeasureTheory.AEStronglyMeasurable (fn n) μ)
    (h_tendsto : Filter.Tendsto
      (fun n => MeasureTheory.eLpNorm (fn n - f) p μ) Filter.atTop (nhds 0)) :
    Filter.Tendsto
      (fun n => MeasureTheory.eLpNorm (fn n) p μ) Filter.atTop
      (nhds (MeasureTheory.eLpNorm f p μ)) := by
  have up : ∀ n, eLpNorm (fn n) p μ ≤ eLpNorm (fn n - f) p μ + eLpNorm f p μ := by
    intro n
    have := eLpNorm_add_le ((hfn n).sub hf) hf hp
    simpa using this
  have lo : ∀ n, eLpNorm f p μ ≤ eLpNorm (fn n - f) p μ + eLpNorm (fn n) p μ := by
    intro n
    have := eLpNorm_add_le (hf.sub (hfn n)) (hfn n) hp
    have e : f - fn n = -(fn n - f) := (neg_sub _ _).symm
    rw [e, eLpNorm_neg] at this
    simpa using this
  rw [tendsto_order]
  refine ⟨fun a ha => ?_, fun b hb => ?_⟩
  · obtain ⟨r, hr0, hr⟩ := ENNReal.lt_iff_exists_add_pos_lt.1 ha
    have hev : ∀ᶠ n in Filter.atTop, eLpNorm (fn n - f) p μ < r :=
      (tendsto_order.1 h_tendsto).2 _ (by exact_mod_cast hr0)
    filter_upwards [hev] with n hn
    have h1 : a + r < r + eLpNorm (fn n) p μ :=
      lt_of_lt_of_le hr ((lo n).trans (add_le_add hn.le le_rfl))
    rw [add_comm] at h1
    exact (ENNReal.add_lt_add_iff_left ENNReal.coe_ne_top).1 h1
  · have ht : Filter.Tendsto (fun n => eLpNorm (fn n - f) p μ + eLpNorm f p μ) Filter.atTop
        (nhds (0 + eLpNorm f p μ)) := h_tendsto.add tendsto_const_nhds
    rw [zero_add] at ht
    filter_upwards [(tendsto_order.1 ht).2 _ hb] with n hn
    exact lt_of_le_of_lt (up n) hn

end LevyStochCalc
