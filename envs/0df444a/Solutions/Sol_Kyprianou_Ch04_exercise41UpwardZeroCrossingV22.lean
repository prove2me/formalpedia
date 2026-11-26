-- Prove2me | solution 1 for Kyprianou.Ch04.exercise41UpwardZeroCrossingV22
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T15:37:01.092376+00:00
-- url     : https://prove2.me/submissions/049cf64b-4681-4ce5-a001-48202d06f3eb

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory ProbabilityTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators Classical Topology
set_option autoImplicit false
theorem solution
    (x : NNReal → ℝ)
    (hR : ∀ s, ContinuousWithinAt x (Ici s) s)
    (hL : ∀ s, 0 < s → ∃ l, Tendsto x (nhdsWithin s (Iio s)) (nhds l))
    (hNeg : ∀ s l, 0 < s → Tendsto x (nhdsWithin s (Iio s)) (nhds l) → x s ≤ l)
    (a b : NNReal) (hab : a ≤ b) (ha : x a < 0) (hb : 0 ≤ x b) :
    ∃ c ∈ Icc a b, x c = 0 := by
  let S : Set NNReal := {u | u ∈ Icc a b ∧ 0 ≤ x u}
  have hS : S.Nonempty := ⟨b,⟨hab,le_rfl⟩,hb⟩
  have hB : BddBelow S := ⟨a,fun u hu => hu.1.1⟩
  let c := sInf S
  have hac : a ≤ c := le_csInf hS (fun u hu => hu.1.1)
  have hcb : c ≤ b := csInf_le hB ⟨⟨hab,le_rfl⟩,hb⟩
  have hC : c ∈ closure S := csInf_mem_closure hS hB
  letI : NeBot (nhdsWithin c S) := mem_closure_iff_nhdsWithin_neBot.mp hC
  have hr : Tendsto x (nhdsWithin c S) (nhds (x c)) :=
    (hR c).mono_left (nhdsWithin_mono _ (fun u hu => csInf_le hB hu))
  have hc : 0 ≤ x c := ge_of_tendsto hr (Filter.mem_of_superset (self_mem_nhdsWithin : S ∈ nhdsWithin c S) (fun u hu => hu.2))
  have hlt : a < c := lt_of_le_of_ne hac (fun he => (not_le_of_gt ha) (he.symm ▸ hc))
  have hp : 0 < c := lt_of_le_of_lt bot_le hlt
  obtain ⟨l,hl⟩ := hL c hp
  letI : NeBot (nhdsWithin c (Iio c)) := nhdsLT_neBot_of_exists_lt ⟨a,hlt⟩
  have hpre : ∀ᶠ u in nhdsWithin c (Iio c), x u ≤ 0 := by
    filter_upwards [self_mem_nhdsWithin (s := Iio c) (a := c),
      mem_nhdsWithin_of_mem_nhds (Ioi_mem_nhds hlt)] with u hu hAu
    by_contra hn
    exact (not_le_of_gt hu) (csInf_le hB ⟨⟨hAu.le,hu.le.trans hcb⟩,le_of_not_ge hn⟩)
  exact ⟨c,⟨hac,hcb⟩,le_antisymm ((hNeg c l hp hl).trans (le_of_tendsto hl hpre)) hc⟩
