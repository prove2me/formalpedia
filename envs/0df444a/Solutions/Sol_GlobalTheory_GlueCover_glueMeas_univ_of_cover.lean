-- Prove2me | solution 1 for GlobalTheory.GlueCover.glueMeas_univ_of_cover
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T18:01:20.512882+00:00
-- url     : https://prove2.me/submissions/626f750f-07c6-4499-ae37-30f760d12eb5

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_ChartMeasApplyOfSubset
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ChartDensityChangeFormula
import Theorems.Thm_GlobalTheory_GlueCover_map_glueMeas

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open MeasureTheory Set Topology
open ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Y
open scoped ENNReal
open GlobalTheory GlobalTheory.GlueCover
open GlobalTheory.ChartGlue
variable {n : ℕ}
namespace GlobalTheory.GlueCover
theorem _root_.solution : ∀ (n : ℕ), n ≠ 0 → ∀ (A B ι κ : Type) [TopologicalSpace A]
    [TopologicalSpace B] [T2Space A] [T2Space B] [SecondCountableTopology A]
    [SecondCountableTopology B] [MeasurableSpace A] [BorelSpace A] [MeasurableSpace B]
    [BorelSpace B] (e : ι → OpenPartialHomeomorph A (ReciprocityTheory.L2DbarEstimates.V n)) (ρ : ι → A → ℝ≥0∞)
    (e' : κ → OpenPartialHomeomorph B (ReciprocityTheory.L2DbarEstimates.V n)) (ρ' : κ → B → ℝ≥0∞),
    (∀ i j, DifferentiableOn ℂ (e j ∘ (e i).symm) (ReciprocityTheory.L2DbarEstimates.Y.ovl e i j)) →
    (∀ i j y, y ∈ (e i).source → y ∈ (e j).source →
      ρ i y = ENNReal.ofReal (‖GlobalTheory.ChartGlue.transDet (e i) (e j) y‖ ^ 2) * ρ j y) →
    (∀ i j, DifferentiableOn ℂ (e' j ∘ (e' i).symm) (ReciprocityTheory.L2DbarEstimates.Y.ovl e' i j)) →
    (∀ i j y, y ∈ (e' i).source → y ∈ (e' j).source →
      ρ' i y = ENNReal.ofReal (‖GlobalTheory.ChartGlue.transDet (e' i) (e' j) y‖ ^ 2) * ρ' j y) →
    ∀ (m : B → A), Continuous m → ∀ T : Set A, T.Finite → (m ⁻¹' T).Finite → ∀ d : ℕ, d ≠ 0 →
    (∀ x ∉ T, (m ⁻¹' {x}).encard = d) →
    (∀ z, m z ∉ T → ∃ i j, z ∈ (e' j).source ∧ m z ∈ (e i).source ∧ ∀ w ∈ (e' j).source,
      m w ∈ (e i).source → e' j w = e i (m w) ∧ ρ' j w = ρ i (m w)) →
    GlobalTheory.ChartGlue.glueMeas e' ρ' Set.univ = d * GlobalTheory.ChartGlue.glueMeas e ρ Set.univ := by
  intro n hn A B ι κ _ _ _ _ _ _ _ _ _ _ e ρ e' ρ' hd hρ hd' hρ' m hm T hT hT' d _ hfib hch
  have h := map_glueMeas hn hd hρ hd' hρ' hm hT hT' hfib hch
  have h' := congrArg (fun μ : Measure A => μ Set.univ) h
  simpa [Measure.map_apply hm.measurable MeasurableSet.univ] using h'
end GlobalTheory.GlueCover
