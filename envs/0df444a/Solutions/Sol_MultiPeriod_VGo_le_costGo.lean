-- Prove2me | solution 1 for MultiPeriod.VGo_le_costGo
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T08:14:46.520845+00:00
-- url     : https://prove2.me/submissions/b0bd7a75-afa7-4da3-9b00-00b89796dfd2

import Definitions.Def_BicausalOT_Defs
import Definitions.Def_BicausalOT_UpperBound
import Mathlib.MeasureTheory.Integral.Lebesgue.Add
import Definitions.Def_BicausalOT_MultiPeriod
import Theorems.Thm_MultiPeriod_VGo_le_pointwise

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
theorem _root_.solution (γ : Strat X Y)
    (hfeas : ∀ t h, γ t h ∈ Feas κμ κν t h) :
    ∀ (k t : ℕ) (h : PairHist X Y t),
      VGo c κμ κν k t h ≤ costGo c γ k t h
  | 0, _, _ => le_of_eq rfl
  | k + 1, t, h => by
    refine le_trans (VGo_le_pointwise κμ κν c (hfeas t h)) ?_
    show c t h + _ ≤ c t h + _
    gcongr with z
    exact solution γ hfeas k (t + 1) (h, z)
end MultiPeriod
