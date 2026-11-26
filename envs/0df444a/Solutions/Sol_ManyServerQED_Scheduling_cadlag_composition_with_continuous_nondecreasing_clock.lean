-- Prove2me | solution 1 for ManyServerQED.Scheduling.cadlag_composition_with_continuous_nondecreasing_clock
-- status  : ACCEPTED   (prove)
-- author  : @Jie Luo
-- created : 2026-11-26T03:37:17.672976+00:00
-- url     : https://prove2.me/submissions/50b527a2-60c3-491d-8f4a-6c5028ec8c91

import Definitions.Def_BellWilliams2001_ThresholdPolicy_Paths

open Filter Topology Set MeasureTheory
open BellWilliams2001.ThresholdPolicy

theorem solution (f c : ℝ → ℝ) (hf : IsCadlag f)
    (hc : ContinuousOn c (Ici (0:ℝ))) (hm : MonotoneOn c (Ici (0:ℝ)))
    (hn : ∀ t, 0 ≤ t → 0 ≤ c t) :
    IsCadlag (f ∘ c) := by
  constructor
  · intro t ht
    exact (hf.1 (c t) (hn t ht)).comp ((hc t ht).mono (Ici_subset_Ici.2 ht))
      (fun s hs => hm ht (ht.trans hs) hs)
  · intro t ht
    by_cases h : ∃ s ∈ Ico (0:ℝ) t, c s = c t
    · obtain ⟨s,hs,he⟩ := h
      refine ⟨f (c t),tendsto_nhds_of_eventually_eq ?_⟩
      have hEvent : Ioi s ∈ 𝓝[<] t := mem_nhdsWithin_of_mem_nhds (Ioi_mem_nhds hs.2)
      filter_upwards [hEvent,self_mem_nhdsWithin] with u hu hut
      change f (c u) = f (c t)
      have hu0 := hs.1.trans hu.le
      have h1 := hm hs.1 hu0 hu.le
      have h2 := hm hu0 ht.le hut.le
      exact congrArg f (le_antisymm h2 (he ▸ h1))
    · have hh (s : ℝ) (hs : s ∈ Ico (0:ℝ) t) : c s < c t :=
        lt_of_le_of_ne (hm hs.1 ht.le hs.2.le) (fun he => h ⟨s,hs,he⟩)
      have hct : 0 < c t := (hn 0 le_rfl).trans_lt (hh 0 ⟨le_rfl,ht⟩)
      obtain ⟨l,hl⟩ := hf.2 (c t) hct
      refine ⟨l,hl.comp ?_⟩
      have hτ : Ioi (0:ℝ) ∈ 𝓝[<] t :=
        mem_nhdsWithin_of_mem_nhds (Ioi_mem_nhds ht)
      apply tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within
      · apply (hc t ht.le).mono_left
        apply le_inf nhdsWithin_le_nhds
        rw [le_principal_iff]
        exact mem_of_superset hτ Ioi_subset_Ici_self
      · filter_upwards [hτ,self_mem_nhdsWithin] with u hu hut
        exact hh u ⟨hu.le,hut⟩
