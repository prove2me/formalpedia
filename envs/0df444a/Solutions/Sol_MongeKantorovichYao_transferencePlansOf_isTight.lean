-- Prove2me | solution 1 for MongeKantorovichYao.transferencePlansOf_isTight
-- status  : ACCEPTED   (prove)
-- author  : @BrunoDCDO
-- created : 2026-09-30T22:12:44.828917+00:00
-- url     : https://prove2.me/submissions/34bc6bf6-e0a9-4b0e-96aa-b3bae20a7e99

import Definitions.Def_MongeKantorovichYao_Defs

open MeasureTheory MongeKantorovichYao

theorem solution {X Y : Type*}
    [TopologicalSpace X] [PolishSpace X] [MeasurableSpace X] [BorelSpace X]
    [TopologicalSpace Y] [PolishSpace Y] [MeasurableSpace Y] [BorelSpace Y]
    (M : Set (Measure X)) (N : Set (Measure Y))
    (hMprob : ∀ μ ∈ M, IsProbabilityMeasure μ) (hNprob : ∀ ν ∈ N, IsProbabilityMeasure ν)
    (hM : IsTightMeasureSet M) (hN : IsTightMeasureSet N) :
    IsTightMeasureSet (transferencePlansOf M N) := by
  apply IsTightMeasureSet.prodMk
  · apply hM.subset
    rintro _ ⟨π, hπ, rfl⟩
    exact hπ.2.1
  · apply hN.subset
    rintro _ ⟨π, hπ, rfl⟩
    exact hπ.2.2
