-- Prove2me | solution 1 for Maldacena2003.squeezed_limit_consistency_relation
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-17T07:13:16.17667+00:00
-- url     : https://prove2.me/submissions/0a984574-cedd-451b-af87-49c2a5052ca4

import Mathlib
import Definitions.Def_Maldacena2003_InflationDefs
open Filter Topology Maldacena2003

theorem solution (ρd φd φdd k : ℝ)
    (hρ : 0 < ρd) (hφ : φd ≠ 0) (hk : 0 < k) :
    Tendsto
      (fun p : ℝ × ℝ => zetaBispectrum ρd φd φdd k p.1 p.2
        / (zetaPowerSpectrum ρd φd k * zetaPowerSpectrum ρd φd p.2))
      (𝓝[{p : ℝ × ℝ | IsMomentumTriangle k p.1 p.2}] (k, 0))
      (𝓝 (-scalarTilt ρd φd φdd)) := by
  have hk0 : k ≠ 0 := hk.ne'
  set g : ℝ × ℝ → ℝ := fun p => amplitudeA ρd φd φdd k p.1 p.2 / (2 * p.1 ^ 3) with hg
  have hc : ContinuousAt g (k, 0) := by
    simp only [hg, amplitudeA, shapeBracket]
    apply ContinuousAt.div _ (by fun_prop) (by simp [hk0])
    apply ContinuousAt.add (by fun_prop)
    apply ContinuousAt.mul (by fun_prop)
    apply ContinuousAt.add (by fun_prop)
    apply ContinuousAt.div (by fun_prop) (by fun_prop)
    simp; linarith
  have hv : g (k, 0) = -scalarTilt ρd φd φdd := by
    simp only [hg, amplitudeA, shapeBracket, scalarTilt]
    field_simp
    ring
  have h1 := hc.tendsto.mono_left (nhdsWithin_le_nhds (s := {p : ℝ × ℝ | IsMomentumTriangle k p.1 p.2}))
  rw [hv] at h1
  apply h1.congr'
  filter_upwards [self_mem_nhdsWithin] with p hp
  obtain ⟨h1, h2, h3, -, -, -⟩ := hp
  simp only [hg, zetaBispectrum, zetaPowerSpectrum]
  field_simp
