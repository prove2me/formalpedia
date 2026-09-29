-- Prove2me | solution 1 for MeasureTheory.tendsto_lintegral_nhds_zero_of_le_of_limsup_lintegral_le
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.007888+00:00
-- url     : https://prove2.me/submissions/1dea83bf-a6c9-56b7-9bd2-c0260f135253

import Mathlib.MeasureTheory.Integral.Lebesgue.Add
import Mathlib.Topology.Instances.ENNReal.Lemmas
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_MeasureTheory_tendsto_lintegral_nhds_zero_of_le_of_limsup_lintegral_le

set_option autoImplicit false

open MeasureTheory Filter
open scoped ENNReal Topology

theorem solution
    {α ι : Type*} [MeasurableSpace α] {μ : Measure α} {l : Filter ι} [l.IsCountablyGenerated]
    (F G : ι → α → ℝ≥0∞) (g : α → ℝ≥0∞)
    (hF : ∀ i, AEMeasurable (F i) μ) (hG : ∀ i, AEMeasurable (G i) μ)
    (hFG : ∀ i, ∀ᵐ x ∂μ, F i x ≤ G i x)
    (hF0 : ∀ᵐ x ∂μ, Tendsto (fun i => F i x) l (𝓝 0))
    (hGg : ∀ᵐ x ∂μ, Tendsto (fun i => G i x) l (𝓝 (g x)))
    (hg : ∫⁻ x, g x ∂μ ≠ ∞)
    (hlim : limsup (fun i => ∫⁻ x, G i x ∂μ) l ≤ ∫⁻ x, g x ∂μ) :
    Tendsto (fun i => ∫⁻ x, F i x ∂μ) l (𝓝 0) := by
  rcases l.eq_or_neBot with rfl | hl
  · exact tendsto_bot

  have hHmeas : ∀ i, AEMeasurable (fun x => G i x - F i x) μ := fun i => (hG i).sub (hF i)
  have hHlim : ∀ᵐ x ∂μ, liminf (fun i => G i x - F i x) l = g x := by
    filter_upwards [hF0, hGg] with x hx0 hxg
    have h := ENNReal.Tendsto.sub hxg hx0 (Or.inr ENNReal.zero_ne_top)
    rw [tsub_zero] at h
    exact h.liminf_eq

  have hFatou : ∫⁻ x, g x ∂μ ≤ liminf (fun i => ∫⁻ x, G i x - F i x ∂μ) l :=
    calc ∫⁻ x, g x ∂μ = ∫⁻ x, liminf (fun i => G i x - F i x) l ∂μ :=
          lintegral_congr_ae (hHlim.mono fun x hx => hx.symm)
      _ ≤ liminf (fun i => ∫⁻ x, G i x - F i x ∂μ) l := lintegral_liminf_le' hHmeas

  have hsum : ∀ i, ∫⁻ x, F i x ∂μ + ∫⁻ x, G i x - F i x ∂μ = ∫⁻ x, G i x ∂μ := by
    intro i
    rw [← lintegral_add_left' (hF i)]
    exact lintegral_congr_ae ((hFG i).mono fun x hx => add_tsub_cancel_of_le hx)

  refine ENNReal.tendsto_nhds_zero.2 fun ε hε => ?_
  have hε2 : ε / 2 ≠ 0 := (ENNReal.half_pos hε.ne').ne'
  have h1 : ∀ᶠ i in l, ∫⁻ x, G i x ∂μ < ∫⁻ x, g x ∂μ + ε / 2 :=
    eventually_lt_of_limsup_lt (hlim.trans_lt (ENNReal.lt_add_right hg hε2))
  have h2 : ∀ᶠ i in l, ∫⁻ x, g x ∂μ - ε / 2 ≤ ∫⁻ x, G i x - F i x ∂μ := by
    rcases eq_or_ne (∫⁻ x, g x ∂μ) 0 with h0 | h0
    · exact Eventually.of_forall fun i => by rw [h0, zero_tsub]; exact zero_le
    · exact (eventually_lt_of_lt_liminf ((ENNReal.sub_lt_self hg h0 hε2).trans_le hFatou)).mono
        fun i hi => hi.le
  filter_upwards [h1, h2] with i hi1 hi2
  have hfin : ∫⁻ x, g x ∂μ - ε / 2 ≠ ∞ := ENNReal.sub_ne_top hg
  have h3 : ∫⁻ x, F i x ∂μ + (∫⁻ x, g x ∂μ - ε / 2) ≤ ∫⁻ x, g x ∂μ + ε / 2 :=
    calc ∫⁻ x, F i x ∂μ + (∫⁻ x, g x ∂μ - ε / 2)
          ≤ ∫⁻ x, F i x ∂μ + ∫⁻ x, G i x - F i x ∂μ := by gcongr
      _ = ∫⁻ x, G i x ∂μ := hsum i
      _ ≤ ∫⁻ x, g x ∂μ + ε / 2 := hi1.le
  calc ∫⁻ x, F i x ∂μ ≤ (∫⁻ x, g x ∂μ + ε / 2) - (∫⁻ x, g x ∂μ - ε / 2) :=
        ENNReal.le_sub_of_add_le_right hfin h3
    _ ≤ ε := by
        refine tsub_le_iff_right.2 ?_
        calc ∫⁻ x, g x ∂μ + ε / 2 ≤ (∫⁻ x, g x ∂μ - ε / 2 + ε / 2) + ε / 2 := by
              gcongr; exact le_tsub_add
          _ = ε + (∫⁻ x, g x ∂μ - ε / 2) := by rw [add_assoc, ENNReal.add_halves, add_comm]

end S_MeasureTheory_tendsto_lintegral_nhds_zero_of_le_of_limsup_lintegral_le
end P2MW
export P2MW.S_MeasureTheory_tendsto_lintegral_nhds_zero_of_le_of_limsup_lintegral_le (solution)
