-- Prove2me | solution 1 for MultiPeriod.Feas.nonempty
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T08:14:59.421539+00:00
-- url     : https://prove2.me/submissions/7289fac8-0aeb-41b4-93a8-35d492a9adf2

import Definitions.Def_BicausalOT_MultiPeriod
import Definitions.Def_BicausalOT_ValueRepresentation
import Mathlib.MeasureTheory.Measure.Prod
import Definitions.Def_BicausalOT_FeasNonempty
import Theorems.Thm_MeasureTheory_Measure_map_fst_prod_of_isProbabilityMeasure
import Theorems.Thm_MeasureTheory_Measure_map_snd_prod_of_isProbabilityMeasure

set_option autoImplicit false
open MeasureTheory Set ENNReal
noncomputable section
open MultiPeriod
variable {X Y : ℕ → Type*}
variable [∀ n, MeasurableSpace (X n)] [∀ n, MeasurableSpace (Y n)]
variable (κμ : (t : ℕ) → XHist X t → Measure (X (t + 1)))
variable (κν : (t : ℕ) → YHist Y t → Measure (Y (t + 1)))
namespace MultiPeriod
namespace Feas
theorem _root_.solution
    (hκμ : ∀ t x, IsProbabilityMeasure (κμ t x))
    (hκν : ∀ t y, IsProbabilityMeasure (κν t y))
    (t : ℕ) (h : PairHist X Y t) :
    (Feas κμ κν t h).Nonempty := by
  haveI := hκμ t (projX t h)
  haveI := hκν t (projY t h)
  exact ⟨(κμ t (projX t h)).prod (κν t (projY t h)),
    Measure.map_fst_prod_of_isProbabilityMeasure _ _,
    Measure.map_snd_prod_of_isProbabilityMeasure _ _⟩
end Feas
end MultiPeriod
