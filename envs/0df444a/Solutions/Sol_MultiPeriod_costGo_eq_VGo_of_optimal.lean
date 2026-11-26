-- Prove2me | solution 1 for MultiPeriod.costGo_eq_VGo_of_optimal
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T08:31:51.552243+00:00
-- url     : https://prove2.me/submissions/1f267a16-1797-4346-ab57-4352333e5b20

import Definitions.Def_BicausalOT_MeasurableStrategy
import Definitions.Def_BicausalOT_DescriptiveSetTheory_CouplingsUHC
import Definitions.Def_BicausalOT_DescriptiveSetTheory_LscIntegral
import Definitions.Def_BicausalOT_DescriptiveSetTheory_MeasurableSelection
import Definitions.Def_BicausalOT_LscBellman
import Theorems.Thm_MultiPeriod_VGo_le_costGo
import Theorems.Thm_MultiPeriod_costGo_le_VGo_add


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
omit [∀ n, TopologicalSpace (X n)] [∀ n, PolishSpace (X n)]
  [∀ n, BorelSpace (X n)] [∀ n, TopologicalSpace (Y n)]
  [∀ n, PolishSpace (Y n)] [∀ n, BorelSpace (Y n)]
namespace MultiPeriod
theorem _root_.solution
    {κμ : (t : ℕ) → XHist X t → Measure (X (t + 1))}
    {κν : (t : ℕ) → YHist Y t → Measure (Y (t + 1))} (T : ℕ)
    (hκμ_prob : ∀ t x, IsProbabilityMeasure (κμ t x))
    (γ : Strat X Y) (hmem : ∀ t h, γ t h ∈ Feas κμ κν t h)
    (hopt : ∀ t (h : PairHist X Y t),
      ∫⁻ z, VGo c κμ κν (T - t - 1) (t + 1) (h, z) ∂(γ t h)
        ≤ ⨅ (γm : Measure (X (t + 1) × Y (t + 1)))
            (_ : γm ∈ Feas κμ κν t h),
            ∫⁻ z, VGo c κμ κν (T - t - 1) (t + 1) (h, z) ∂γm) :
    ∀ (k t : ℕ), t + k = T → ∀ h : PairHist X Y t,
      costGo c γ k t h = VGo c κμ κν k t h := by
  intro k t htk h
  refine le_antisymm ?_ (VGo_le_costGo κμ κν c γ hmem k t h)
  have hle := costGo_le_VGo_add κμ κν c T hκμ_prob γ hmem (ε := 0)
    (fun t h => by simpa using hopt t h) k t htk h
  simpa using hle
end MultiPeriod
