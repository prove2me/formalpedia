-- Prove2me | solution 1 for MongeKantorovichYao.integral_fst_eq_of_mem_transferencePlans
-- status  : ACCEPTED   (prove)
-- author  : @BrunoDCDO
-- created : 2026-09-30T22:12:24.211985+00:00
-- url     : https://prove2.me/submissions/fb700f0a-cba3-40fb-ad36-60f31e3ba9ea

import Definitions.Def_MongeKantorovichYao_Defs

open MeasureTheory MongeKantorovichYao

theorem solution {X Y : Type*}
    [MeasurableSpace X] [MeasurableSpace Y]
    (μ : Measure X) (ν : Measure Y) (π : Measure (X × Y)) (hπ : π ∈ transferencePlans μ ν)
    (f : X → ℝ) (hf : Integrable f μ) :
    ∫ x, f x ∂μ = ∫ p, f p.1 ∂π := by
  have hfst : π.map Prod.fst = μ := hπ.2.1
  rw [← hfst] at hf ⊢
  exact integral_map measurable_fst.aemeasurable hf.aestronglyMeasurable
