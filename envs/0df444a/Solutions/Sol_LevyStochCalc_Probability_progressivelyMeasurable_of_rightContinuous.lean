-- Prove2me | solution 1 for LevyStochCalc.Probability.progressivelyMeasurable_of_rightContinuous
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-19T06:44:30.399435+00:00
-- url     : https://prove2.me/submissions/d4a5c648-7b66-4d3d-983a-9a9f606901cd

import Definitions.Def_LevyStochCalc_Probability_ProgressiveCadlag_F000

open MeasureTheory Filter Topology

namespace LevyStochCalc.Probability

universe u

variable {Ω : Type u} [MeasurableSpace Ω]

theorem _root_.solution
    {ℱ : MeasureTheory.Filtration ℝ ‹MeasurableSpace Ω›} {X : ℝ → Ω → ℝ}
    (hadapt : ∀ t : ℝ, Measurable[ℱ t] (X t))
    (hright : ∀ (ω : Ω) (t : ℝ), Tendsto (fun s => X s ω) (𝓝[>] t) (𝓝 (X t ω))) :
    ProgressivelyMeasurable ℱ (fun ω s => X s ω) := by
  intro i
  let _ : MeasurableSpace Ω := ℱ i
  have hF : ∀ n : ℕ, Measurable (fun p : Ω × ℤ => X (min ((p.2 : ℝ) / 2 ^ n) i) p.1) := by
    intro n
    refine measurable_from_prod_countable_left fun k => ?_
    exact (hadapt (min ((k : ℝ) / 2 ^ n) i)).mono (ℱ.mono (min_le_right _ _)) le_rfl
  have hc : ∀ n : ℕ, Measurable (fun s : ℝ => ⌈(2 : ℝ) ^ n * s⌉) :=
    fun n => Int.measurable_ceil.comp (measurable_const.mul measurable_id)
  let fn : ℕ → Ω × ℝ → ℝ := fun n p =>
    (Set.Iic i).indicator (fun s => X (dyadicCeil n i s) p.1) p.2
  have hfn : ∀ n, Measurable (fn n) := by
    intro n
    have h1 : Measurable (fun p : Ω × ℝ => X (dyadicCeil n i p.2) p.1) :=
      (hF n).comp (measurable_fst.prodMk ((hc n).comp measurable_snd))
    have h2 : Measurable (fun p : Ω × ℝ => (Set.Iic i).indicator (fun _ => (1 : ℝ)) p.2) :=
      (measurable_const.indicator measurableSet_Iic).comp measurable_snd
    have e : fn n = fun p => (Set.Iic i).indicator (fun _ => (1 : ℝ)) p.2
        * X (dyadicCeil n i p.2) p.1 := by
      funext p
      simp only [fn, Set.indicator]
      split_ifs <;> simp
    rw [e]
    exact h2.mul h1
  have hlim : Tendsto fn atTop (𝓝 fun p : Ω × ℝ =>
      (Set.Iic i).indicator ((fun ω s => X s ω) p.1) p.2) := by
    rw [tendsto_pi_nhds]
    rintro ⟨ω, s⟩
    by_cases hs : s ≤ i
    · simp only [fn, Set.indicator_of_mem (Set.mem_Iic.2 hs)]
      have hge := tendsto_nhdsGE_of_nhdsGT (hright ω s)
      refine hge.comp ?_
      exact tendsto_nhdsWithin_iff.2 ⟨tendsto_dyadicCeil hs,
        Eventually.of_forall fun n => le_dyadicCeil n hs⟩
    · have hn : s ∉ Set.Iic i := hs
      simp only [fn, Set.indicator_of_notMem hn]
      exact tendsto_const_nhds
  exact (measurable_of_tendsto_metrizable hfn hlim).stronglyMeasurable

end LevyStochCalc.Probability
