-- Prove2me | solution 1 for Maldacena2003.zetaGammaGamma_squeezed_limit
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-17T07:04:38.145932+00:00
-- url     : https://prove2.me/submissions/ae8d6456-5e5b-45cd-bf9d-71bacc2e3e42

import Mathlib
import Definitions.Def_Maldacena2003_InflationDefs
open Filter Topology Maldacena2003

theorem solution (ρd φd k E : ℝ) (hρ : 0 < ρd) (hφ : φd ≠ 0)
    (hk : 0 < k) :
    Tendsto
      (fun p : ℝ × ℝ => zetaGammaGammaBispectrum ρd p.1 k p.2 E
        / (zetaPowerSpectrum ρd φd p.1 * tensorPowerSpectrum ρd k))
      (𝓝[{p : ℝ × ℝ | IsMomentumTriangle p.1 k p.2}] (0, k))
      (𝓝 (-(E / 2) * tensorTilt ρd φd)) := by
  set g : ℝ × ℝ → ℝ := fun p => (-(1 / 4) * p.1 ^ 3 + (1 / 2) * p.1 * (k ^ 2 + p.2 ^ 2)
        + 4 * k ^ 2 * p.2 ^ 2 / (p.1 + k + p.2)) * E * φd ^ 2 / (4 * p.2 ^ 3 * ρd ^ 2) with hg
  have hc : ContinuousAt g (0, k) := by
    simp only [hg]
    apply ContinuousAt.div _ (by fun_prop) (by simp [hk.ne', hρ.ne'])
    apply ContinuousAt.mul (ContinuousAt.mul _ continuousAt_const) continuousAt_const
    apply ContinuousAt.add (by fun_prop)
    apply ContinuousAt.div (by fun_prop) (by fun_prop)
    simp; linarith
  have hv : g (0, k) = -(E / 2) * tensorTilt ρd φd := by
    simp only [hg, tensorTilt]
    have : k ≠ 0 := hk.ne'
    field_simp
    ring
  have h1 := (hc.tendsto.mono_left (nhdsWithin_le_nhds (s := {p : ℝ × ℝ | IsMomentumTriangle p.1 k p.2})))
  rw [hv] at h1
  apply h1.congr'
  filter_upwards [self_mem_nhdsWithin] with p hp
  obtain ⟨h1, h2, h3, -, -, -⟩ := hp
  simp only [hg, zetaGammaGammaBispectrum, zetaPowerSpectrum, tensorPowerSpectrum]
  field_simp
  ring
