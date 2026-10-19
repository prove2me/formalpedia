-- Prove2me | solution 1 for Maldacena2003.fNL_eq_tilts
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-17T07:02:51.252614+00:00
-- url     : https://prove2.me/submissions/fe32ed05-5607-44d1-97ed-86d822c9fe04

import Mathlib
import Definitions.Def_Maldacena2003_InflationDefs
open Filter Topology Maldacena2003

theorem solution (ρd φd φdd k₁ k₂ k₃ : ℝ) (hρ : 0 < ρd) (hφ : φd ≠ 0)
    (hk : IsMomentumTriangle k₁ k₂ k₃) :
    (5 / 3) * (amplitudeA ρd φd φdd k₁ k₂ k₃ / (4 * (k₁ ^ 3 + k₂ ^ 3 + k₃ ^ 3)))
        = (5 / 12) * (2 * (φdd / (φd * ρd)) + φd ^ 2 / ρd ^ 2 * (2 + shapeF k₁ k₂ k₃)) ∧
      (5 / 12) * (2 * (φdd / (φd * ρd)) + φd ^ 2 / ρd ^ 2 * (2 + shapeF k₁ k₂ k₃))
        = -(5 / 12) * (scalarTilt ρd φd φdd + shapeF k₁ k₂ k₃ * tensorTilt ρd φd) := by
  obtain ⟨h1, h2, h3, -, -, -⟩ := hk
  have hS : 0 < k₁ ^ 3 + k₂ ^ 3 + k₃ ^ 3 := by positivity
  constructor
  · simp only [amplitudeA, shapeF]
    field_simp
    ring
  · simp only [scalarTilt, tensorTilt]
    field_simp
    ring
