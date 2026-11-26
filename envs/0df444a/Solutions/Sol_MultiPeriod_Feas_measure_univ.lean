-- Prove2me | solution 1 for MultiPeriod.Feas.measure_univ
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T08:09:50.478798+00:00
-- url     : https://prove2.me/submissions/437e7afd-4786-4f32-9d5a-2cf549f2ede0

import Definitions.Def_BicausalOT_Defs
import Definitions.Def_BicausalOT_UpperBound
import Mathlib.MeasureTheory.Integral.Lebesgue.Add
import Definitions.Def_BicausalOT_MultiPeriod

set_option autoImplicit false
open MeasureTheory Set ENNReal
noncomputable section
open MultiPeriod
variable (X Y : ℕ → Type*)
variable {X Y}
variable [∀ n, MeasurableSpace (X n)] [∀ n, MeasurableSpace (Y n)]
variable (κμ : (t : ℕ) → XHist X t → Measure (X (t + 1)))
variable (κν : (t : ℕ) → YHist Y t → Measure (Y (t + 1)))
variable (c : (t : ℕ) → PairHist X Y t → ℝ≥0∞)
variable {κμ κν}
variable (κμ κν)
namespace MultiPeriod
namespace Feas
theorem _root_.solution
    (hκμ : ∀ t x, IsProbabilityMeasure (κμ t x))
    {t : ℕ} {h : PairHist X Y t}
    {γm : Measure (X (t + 1) × Y (t + 1))} (hγ : γm ∈ Feas κμ κν t h) :
    γm Set.univ = 1 := by
  have h1 : (γm.map Prod.fst) Set.univ = 1 := by
    rw [hγ.1]
    exact (hκμ t (projX t h)).measure_univ
  rwa [Measure.map_apply measurable_fst MeasurableSet.univ,
    Set.preimage_univ] at h1
end Feas
end MultiPeriod
