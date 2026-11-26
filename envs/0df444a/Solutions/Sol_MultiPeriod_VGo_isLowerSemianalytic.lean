-- Prove2me | solution 1 for MultiPeriod.VGo_isLowerSemianalytic
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T08:16:13.44635+00:00
-- url     : https://prove2.me/submissions/4dbb3afc-03e5-4321-81c4-9c3bdf772307

import Definitions.Def_BicausalOT_MultiPeriodTopology
import Definitions.Def_BicausalOT_FeasNonempty
import Definitions.Def_BicausalOT_DescriptiveSetTheory_LsaAlgebra
import Definitions.Def_BicausalOT_DescriptiveSetTheory_KernelIntegral
import Definitions.Def_BicausalOT_DescriptiveSetTheory_ProbabilityMeasurePolish
import Definitions.Def_BicausalOT_SemianalyticValue
import Theorems.Thm_MultiPeriod_measurableSet_feasGraph
import Theorems.Thm_MultiPeriod_lintegral_weakP_lowerSemianalytic
import Theorems.Thm_MultiPeriod_VGo_succ_eq_weakP
import Theorems.Thm_IsLowerSemianalytic_add
import Theorems.Thm_IsLowerSemianalytic_iInf_fiber


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
namespace MultiPeriod
theorem _root_.solution
    (hκμ_meas : ∀ t, Measurable (κμ t))
    (hκν_meas : ∀ t, Measurable (κν t))
    (hκμ_prob : ∀ t x, IsProbabilityMeasure (κμ t x))
    (hκν_prob : ∀ t y, IsProbabilityMeasure (κν t y))
    (hc : ∀ t, IsLowerSemianalytic (c t)) :
    ∀ k t : ℕ, IsLowerSemianalytic (VGo c κμ κν k t) := by
  intro k
  induction k with
  | zero => exact fun t => hc t
  | succ k ih =>
    intro t
    -- the integrand on the product with the measure space
    have hintegrand : IsLowerSemianalytic
        (fun p : PairHist X Y t × WeakP (X (t + 1) × Y (t + 1)) =>
          ∫⁻ z, VGo c κμ κν k (t + 1) (p.1, z) ∂p.2.toMeasure) :=
      lintegral_weakP_lowerSemianalytic t (ih (t + 1))
    -- fiber infimum over the Borel (hence analytic) feasibility graph
    have hfiber : IsLowerSemianalytic
        (fun h : PairHist X Y t =>
          ⨅ (γ : WeakP (X (t + 1) × Y (t + 1)))
            (_ : (h, γ) ∈ FeasGraph κμ κν t),
            ∫⁻ z, VGo c κμ κν k (t + 1) (h, z) ∂γ.toMeasure) :=
      IsLowerSemianalytic.iInf_fiber
        ((measurableSet_feasGraph κμ κν hκμ_meas hκν_meas
          hκμ_prob hκν_prob t).analyticSet)
        hintegrand
    -- reassemble VGo (k+1)
    have heq : VGo c κμ κν (k + 1) t
        = fun h => c t h + ⨅ (γ : WeakP (X (t + 1) × Y (t + 1)))
            (_ : (h, γ) ∈ FeasGraph κμ κν t),
            ∫⁻ z, VGo c κμ κν k (t + 1) (h, z) ∂γ.toMeasure :=
      funext fun h => VGo_succ_eq_weakP κμ κν c hκμ_prob k t h
    rw [heq]
    exact (hc t).add hfiber
end MultiPeriod
