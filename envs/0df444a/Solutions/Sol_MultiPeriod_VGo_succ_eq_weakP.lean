-- Prove2me | solution 1 for MultiPeriod.VGo_succ_eq_weakP
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T08:15:09.160627+00:00
-- url     : https://prove2.me/submissions/d9d78429-eb9c-4fac-bc3c-517d91809734

import Definitions.Def_BicausalOT_MultiPeriodTopology
import Definitions.Def_BicausalOT_FeasNonempty
import Definitions.Def_BicausalOT_DescriptiveSetTheory_LsaAlgebra
import Definitions.Def_BicausalOT_DescriptiveSetTheory_KernelIntegral
import Definitions.Def_BicausalOT_DescriptiveSetTheory_ProbabilityMeasurePolish
import Definitions.Def_BicausalOT_SemianalyticValue
import Theorems.Thm_MultiPeriod_iInf_feas_eq_iInf_feasGraph

set_option autoImplicit false
open MeasureTheory Set ENNReal
noncomputable section
open MultiPeriod
variable {X Y : ℕ → Type*}
  [∀ n, TopologicalSpace (X n)] [∀ n, PolishSpace (X n)]
  [∀ n, MeasurableSpace (X n)] [∀ n, BorelSpace (X n)]
  [∀ n, TopologicalSpace (Y n)] [∀ n, PolishSpace (Y n)]
  [∀ n, MeasurableSpace (Y n)] [∀ n, BorelSpace (Y n)]
variable (κμ : (t : ℕ) → XHist X t → Measure (X (t + 1)))
variable (κν : (t : ℕ) → YHist Y t → Measure (Y (t + 1)))
variable (c : (t : ℕ) → PairHist X Y t → ℝ≥0∞)
omit [∀ n, TopologicalSpace (X n)] [∀ n, PolishSpace (X n)]
  [∀ n, BorelSpace (X n)] [∀ n, TopologicalSpace (Y n)]
  [∀ n, PolishSpace (Y n)] [∀ n, BorelSpace (Y n)]
namespace MultiPeriod
theorem _root_.solution
    (hκμ_prob : ∀ t x, IsProbabilityMeasure (κμ t x)) (k t : ℕ)
    (h : PairHist X Y t) :
    VGo c κμ κν (k + 1) t h
      = c t h + ⨅ (γ : WeakP (X (t + 1) × Y (t + 1)))
          (_ : (h, γ) ∈ FeasGraph κμ κν t),
          ∫⁻ z, VGo c κμ κν k (t + 1) (h, z) ∂γ.toMeasure := by
  show c t h + _ = c t h + _
  congr 1
  exact iInf_feas_eq_iInf_feasGraph κμ κν hκμ_prob t h _
end MultiPeriod
