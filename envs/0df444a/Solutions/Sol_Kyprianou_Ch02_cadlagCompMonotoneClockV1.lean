-- Prove2me | solution 1 for Kyprianou.Ch02.cadlagCompMonotoneClockV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-23T23:48:30.059371+00:00
-- url     : https://prove2.me/submissions/f484908f-91a9-497a-9b4e-42b8e6325f01

import Theorems.Thm_Kyprianou_Ch02_monotoneClockLeLeftLimitV1
import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_Kyprianou_Ch01_LevyTripletExponent
open MeasureTheory ProbabilityTheory Complex Filter Set Topology
open scoped NNReal ENNReal Topology
set_option autoImplicit false

theorem solution
    (f : ℝ≥0 → ℝ) (g : ℝ≥0 → ℝ≥0)
    (hf : ProbabilityTheory.IsCadlag f)
    (hg : ProbabilityTheory.IsCadlag (fun t => (g t : ℝ)))
    (hm : Monotone g) :
    ProbabilityTheory.IsCadlag (fun t => f (g t)) := by
  intro t
  constructor
  · have hg' : Tendsto g (nhdsWithin t (Set.Ici t)) (nhds (g t)) :=
      NNReal.tendsto_coe.1 (hg t).1
    have hmem : ∀ᶠ s in nhdsWithin t (Set.Ici t), g s ∈ Set.Ici (g t) :=
      eventually_nhdsWithin_of_forall (fun s hs => hm hs)
    exact (hf (g t)).1.tendsto.comp (tendsto_nhdsWithin_iff.2 ⟨hg', hmem⟩)
  · obtain ⟨l, hl⟩ := (hg t).2
    let u := l.toNNReal
    have hu : Tendsto g (nhdsWithin t (Set.Iio t)) (nhds u) := by
      have h := tendsto_real_toNNReal hl
      simpa [u, Function.comp_def] using h
    by_cases hflat : ∃ s : ℝ≥0, s < t ∧ g s = u
    · obtain ⟨s, hs, hsu⟩ := hflat
      have he : ∀ᶠ r in nhdsWithin t (Set.Iio t), g r = u := by
        filter_upwards [(nhdsWithin_le_nhds (Ioi_mem_nhds hs)), self_mem_nhdsWithin]
          with r hsr hrt
        have hle := Kyprianou.Ch02.monotoneClockLeLeftLimitV1 g hm t u hu r hrt
        exact le_antisymm hle (hsu ▸ hm hsr.le)
      exact ⟨f u, tendsto_nhds_of_eventually_eq (he.mono fun r hr => congrArg f hr)⟩
    · obtain ⟨v, hv⟩ := (hf u).2
      have hmem : ∀ᶠ r in nhdsWithin t (Set.Iio t), g r ∈ Set.Iio u := by
        apply eventually_nhdsWithin_of_forall
        intro r hr
        have hle := Kyprianou.Ch02.monotoneClockLeLeftLimitV1 g hm t u hu r hr
        exact lt_of_le_of_ne hle (fun he => hflat ⟨r, hr, he⟩)
      exact ⟨v, hv.comp (tendsto_nhdsWithin_iff.2 ⟨hu, hmem⟩)⟩
