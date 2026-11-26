-- Prove2me | solution 1 for MultiPeriod.lintegral_weakP_lowerSemianalytic
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T08:13:36.063985+00:00
-- url     : https://prove2.me/submissions/c3ff4423-624b-406f-9174-677c78553f89

import Definitions.Def_BicausalOT_MultiPeriodTopology
import Definitions.Def_BicausalOT_FeasNonempty
import Definitions.Def_BicausalOT_DescriptiveSetTheory_LsaAlgebra
import Definitions.Def_BicausalOT_DescriptiveSetTheory_KernelIntegral
import Definitions.Def_BicausalOT_DescriptiveSetTheory_ProbabilityMeasurePolish
import Definitions.Def_BicausalOT_SemianalyticValue
import Theorems.Thm_WeakP_measurable_toMeasure
import Theorems.Thm_IsLowerSemianalytic_comp_continuous
import Theorems.Thm_lintegral_lowerSemianalytic


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
theorem _root_.solution (t : ℕ)
    {f : PairHist X Y (t + 1) → ℝ≥0∞} (hf : IsLowerSemianalytic f) :
    IsLowerSemianalytic
      (fun p : PairHist X Y t × WeakP (X (t + 1) × Y (t + 1)) =>
        ∫⁻ z, f (p.1, z) ∂p.2.toMeasure) := by
  have hf' : IsLowerSemianalytic
      (fun q : (PairHist X Y t × WeakP (X (t + 1) × Y (t + 1)))
          × (X (t + 1) × Y (t + 1)) => f (q.1.1, q.2)) := by
    have hcomp : (fun q : (PairHist X Y t × WeakP (X (t + 1) × Y (t + 1)))
          × (X (t + 1) × Y (t + 1)) => f (q.1.1, q.2))
        = f ∘ (fun q => (q.1.1, q.2)) := rfl
    rw [hcomp]
    exact hf.comp_continuous
      ((continuous_fst.comp continuous_fst).prodMk continuous_snd)
  exact lintegral_lowerSemianalytic hf'
    (WeakP.measurable_toMeasure.comp measurable_snd)
    (fun p => inferInstance)
end MultiPeriod
