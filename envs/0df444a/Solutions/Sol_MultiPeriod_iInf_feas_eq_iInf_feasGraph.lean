-- Prove2me | solution 1 for MultiPeriod.iInf_feas_eq_iInf_feasGraph
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T08:12:23.734328+00:00
-- url     : https://prove2.me/submissions/78ed37c6-a3f3-46a0-bfc7-998711b2e831

import Definitions.Def_BicausalOT_MultiPeriodTopology
import Definitions.Def_BicausalOT_FeasNonempty
import Definitions.Def_BicausalOT_DescriptiveSetTheory_LsaAlgebra
import Definitions.Def_BicausalOT_DescriptiveSetTheory_KernelIntegral
import Definitions.Def_BicausalOT_DescriptiveSetTheory_ProbabilityMeasurePolish
import Definitions.Def_BicausalOT_SemianalyticValue
import Theorems.Thm_MultiPeriod_Feas_measure_univ
import Theorems.Thm_P2M_CouplingSet__measure_univ_db95189062ba


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
    (hκμ_prob : ∀ t x, IsProbabilityMeasure (κμ t x))
    (t : ℕ) (h : PairHist X Y t) (f : X (t + 1) × Y (t + 1) → ℝ≥0∞) :
    (⨅ (γm : Measure (X (t + 1) × Y (t + 1))) (_ : γm ∈ Feas κμ κν t h),
        ∫⁻ z, f z ∂γm)
      = ⨅ (γ : WeakP (X (t + 1) × Y (t + 1)))
          (_ : (h, γ) ∈ FeasGraph κμ κν t),
          ∫⁻ z, f z ∂γ.toMeasure := by
  apply le_antisymm
  · exact le_iInf₂ fun γ hγ => iInf₂_le γ.toMeasure hγ
  · refine le_iInf₂ fun γm hγm => ?_
    haveI hpm : IsProbabilityMeasure γm :=
      ⟨Feas.measure_univ κμ κν hκμ_prob hγm⟩
    exact iInf₂_le
      (show WeakP (X (t + 1) × Y (t + 1)) from
        (⟨γm, hpm⟩ : ProbabilityMeasure (X (t + 1) × Y (t + 1)))) hγm
end MultiPeriod
