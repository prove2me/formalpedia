-- Prove2me | solution 1 for MongeKantorovichYao.weak_duality
-- status  : ACCEPTED   (prove)
-- author  : @BrunoDCDO
-- created : 2026-09-30T22:12:35.164713+00:00
-- url     : https://prove2.me/submissions/f8da6e6f-8e4c-4aa0-8e4d-d21e0bd8544b

import Definitions.Def_MongeKantorovichYao_Defs

open MeasureTheory MongeKantorovichYao

theorem solution {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (μ : Measure X) (ν : Measure Y) (c : X × Y → ℝ)
    (π : Measure (X × Y)) (hπ : π ∈ transferencePlans μ ν)
    (ψ : X → ℝ) (φ : Y → ℝ) (hψ : Integrable ψ μ) (hφ : Integrable φ ν)
    (hc : Integrable c π) (hfeas : ∀ x y, ψ x + φ y ≤ c (x, y)) :
    ∫ x, ψ x ∂μ + ∫ y, φ y ∂ν ≤ ∫ p, c p ∂π := by
  have hfst : π.map Prod.fst = μ := hπ.2.1
  have hsnd : π.map Prod.snd = ν := hπ.2.2
  rw [← hfst] at hψ ⊢
  rw [← hsnd] at hφ ⊢
  have hψπ : Integrable (fun p : X × Y => ψ p.1) π := hψ.comp_measurable measurable_fst
  have hφπ : Integrable (fun p : X × Y => φ p.2) π := hφ.comp_measurable measurable_snd
  rw [integral_map measurable_fst.aemeasurable hψ.aestronglyMeasurable,
    integral_map measurable_snd.aemeasurable hφ.aestronglyMeasurable,
    ← integral_add hψπ hφπ]
  exact integral_mono (hψπ.add hφπ) hc (fun p => hfeas p.1 p.2)
