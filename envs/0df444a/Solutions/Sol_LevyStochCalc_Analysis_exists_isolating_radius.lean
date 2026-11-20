-- Prove2me | solution 1 for LevyStochCalc.Analysis.exists_isolating_radius
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-19T07:46:34.118173+00:00
-- url     : https://prove2.me/submissions/d67484e9-7cea-47c4-ad4e-411787a3f9dd

import Definitions.Def_LevyStochCalc_Analysis_CadlagJumps_F000

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# The jumps of a càdlàg function

A function on the line that is right-continuous and has left limits everywhere jumps only at
isolated points of each level of the jump size, so its jump set is countable and therefore
Lebesgue-null: such a function agrees with its left limits almost everywhere.
-/

open Filter Set MeasureTheory
open scoped Topology

namespace LevyStochCalc.Analysis

theorem AuxIso.near {f : ℝ → ℝ} (hleft : ∀ t : ℝ, ∃ L : ℝ, Tendsto f (𝓝[<] t) (𝓝 L))
    {a s c r : ℝ} (has : a < s) (hb : ∀ u ∈ Ioo a s, |f u - c| < r) :
    |Function.leftLim f s - c| ≤ r := by
  obtain ⟨L, hL⟩ := hleft s
  rw [leftLim_eq_of_tendsto hL]
  have hev : ∀ᶠ u in 𝓝[<] s, |f u - c| ≤ r := by
    filter_upwards [Ioo_mem_nhdsLT has] with u hu using (hb u hu).le
  exact le_of_tendsto (((continuous_abs.comp (continuous_id.sub continuous_const)).tendsto L).comp hL) hev

theorem _root_.LevyStochCalc.Analysis.exists_isolating_radius' {f : ℝ → ℝ}
    (hright : ∀ t : ℝ, Tendsto f (𝓝[>] t) (𝓝 (f t)))
    (hleft : ∀ t : ℝ, ∃ L : ℝ, Tendsto f (𝓝[<] t) (𝓝 L)) {ε : ℝ} (hε : 0 < ε) (t : ℝ) :
    ∃ δ > 0, ∀ s ∈ Set.Ioo (t - δ) (t + δ), s ≠ t → |f s - Function.leftLim f s| < ε := by
  obtain ⟨L, hL⟩ := hleft t
  have h2 : 0 < ε / 2 := by linarith
  have hR := Metric.tendsto_nhds.1 (hright t) (ε / 2) h2
  have hLt := Metric.tendsto_nhds.1 hL (ε / 2) h2
  obtain ⟨u, hu, hus⟩ := mem_nhdsGT_iff_exists_Ioo_subset.1 hR
  obtain ⟨l, hl, hls⟩ := mem_nhdsLT_iff_exists_Ioo_subset.1 hLt
  refine ⟨min (u - t) (t - l), lt_min (by linarith [hu.out]) (by linarith [hl.out]), ?_⟩
  intro s hs hst
  obtain ⟨hs1, hs2⟩ := hs
  have hm1 := min_le_left (u - t) (t - l)
  have hm2 := min_le_right (u - t) (t - l)
  have hu' : t < u := hu
  have hl' : l < t := hl
  rcases lt_or_gt_of_ne hst with h | h
  · -- s < t
    have hsl : l < s := by linarith
    have hfs : |f s - L| < ε / 2 := by
      have := hls ⟨hsl, h⟩; simpa [Real.dist_eq] using this
    have hll : |Function.leftLim f s - L| ≤ ε / 2 := AuxIso.near hleft hsl fun v hv => by
      have := hls ⟨hv.1, hv.2.trans h⟩; simpa [Real.dist_eq] using this
    calc |f s - Function.leftLim f s| = |(f s - L) - (Function.leftLim f s - L)| := by ring_nf
      _ ≤ |f s - L| + |Function.leftLim f s - L| := abs_sub _ _
      _ < ε := by linarith
  · -- s > t
    have hsu : s < u := by linarith
    have hfs : |f s - f t| < ε / 2 := by
      have := hus ⟨h, hsu⟩; simpa [Real.dist_eq] using this
    have hll : |Function.leftLim f s - f t| ≤ ε / 2 := AuxIso.near hleft h fun v hv => by
      have := hus ⟨hv.1, hv.2.trans hsu⟩; simpa [Real.dist_eq] using this
    calc |f s - Function.leftLim f s| = |(f s - f t) - (Function.leftLim f s - f t)| := by ring_nf
      _ ≤ |f s - f t| + |Function.leftLim f s - f t| := abs_sub _ _
      _ < ε := by linarith

theorem _root_.solution {f : ℝ → ℝ}
    (hright : ∀ t : ℝ, Tendsto f (𝓝[>] t) (𝓝 (f t)))
    (hleft : ∀ t : ℝ, ∃ L : ℝ, Tendsto f (𝓝[<] t) (𝓝 L)) {ε : ℝ} (hε : 0 < ε) (t : ℝ) :
    ∃ δ > 0, ∀ s ∈ Set.Ioo (t - δ) (t + δ), s ≠ t → |f s - Function.leftLim f s| < ε :=
  LevyStochCalc.Analysis.exists_isolating_radius' hright hleft hε t

end LevyStochCalc.Analysis
