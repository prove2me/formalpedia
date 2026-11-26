-- Prove2me | solution 1 for MultiPeriod.VGo_le_pointwise
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T08:14:10.462701+00:00
-- url     : https://prove2.me/submissions/02426644-a4a2-4561-9100-77e751079101

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
theorem _root_.solution {t k : ℕ} {h : PairHist X Y t}
    {γm : Measure (X (t + 1) × Y (t + 1))} (hγ : γm ∈ Feas κμ κν t h) :
    VGo c κμ κν (k + 1) t h
      ≤ c t h + ∫⁻ z, VGo c κμ κν k (t + 1) (h, z) ∂γm := by
  show c t h + _ ≤ _
  gcongr
  exact iInf₂_le γm hγ
end MultiPeriod
