-- Prove2me | solution 1 for MultiPeriod.argminSet_nonempty
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T08:32:02.509162+00:00
-- url     : https://prove2.me/submissions/d6398dd4-167d-4a40-9953-43f05cf7c048

import Definitions.Def_BicausalOT_MeasurableStrategy
import Definitions.Def_BicausalOT_DescriptiveSetTheory_CouplingsUHC
import Definitions.Def_BicausalOT_DescriptiveSetTheory_LscIntegral
import Definitions.Def_BicausalOT_DescriptiveSetTheory_MeasurableSelection
import Definitions.Def_BicausalOT_LscBellman
import Theorems.Thm_MultiPeriod_isCompact_feasGraph_fiber
import Theorems.Thm_P2M_MultiPeriod_feasGraph_fiber_nonempty__29fdcaa9c5cf

set_option autoImplicit false
open MeasureTheory Set Filter Topology
open scoped ENNReal
noncomputable section
open MultiPeriod
variable {X Y : ℕ → Type*}
  [∀ n, TopologicalSpace (X n)] [∀ n, PolishSpace (X n)]
  [∀ n, MeasurableSpace (X n)] [∀ n, BorelSpace (X n)]
  [∀ n, TopologicalSpace (Y n)] [∀ n, PolishSpace (Y n)]
  [∀ n, MeasurableSpace (Y n)] [∀ n, BorelSpace (Y n)]
variable (κμP : (t : ℕ) → XHist X t → ProbabilityMeasure (X (t + 1)))
variable (κνP : (t : ℕ) → YHist Y t → ProbabilityMeasure (Y (t + 1)))
variable (c : (t : ℕ) → PairHist X Y t → ℝ≥0∞)
namespace MultiPeriod
theorem _root_.solution (t : ℕ)
    {F : PairHist X Y t × WeakP (X (t + 1) × Y (t + 1)) → ℝ≥0∞}
    (hF : LowerSemicontinuous F) (h : PairHist X Y t) :
    (argminSet κμP κνP t F h).Nonempty := by
  obtain ⟨γ₀, hγ₀⟩ := feasGraph_fiber_nonempty' κμP κνP t h
  obtain ⟨γ, hγmem, hγmin⟩ := LowerSemicontinuousOn.exists_isMinOn
    ⟨γ₀, hγ₀⟩ (isCompact_feasGraph_fiber κμP κνP t h)
    ((hF.comp (Continuous.prodMk continuous_const continuous_id)
      ).lowerSemicontinuousOn _)
  refine ⟨γ, hγmem, ?_⟩
  exact le_iInf₂ fun γ' hγ' => isMinOn_iff.mp hγmin γ' hγ'.1
end MultiPeriod
