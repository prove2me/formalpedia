-- Prove2me | solution 1 for GlobalTheory.T.glueMeas_univ_eq_mul_of_fibre_encard_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T18:18:37.4819+00:00
-- url     : https://prove2.me/submissions/8fc53506-0012-49ca-bb81-672132dfd5f3

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ChartDensityChangeFormula
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_ChartMeasApplyOfSubset
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ChartDensityChangeFormulaStatement
import Theorems.Thm_GlobalTheory_GlueCover_glueMeas_univ_of_cover


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Topology
open scoped ENNReal
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (n : ℕ), n ≠ 0 → ∀ (A B ι κ : Type) [TopologicalSpace A] [TopologicalSpace B] [T2Space A] [T2Space B] [SecondCountableTopology A] [SecondCountableTopology B] [MeasurableSpace A] [BorelSpace A] [MeasurableSpace B] [BorelSpace B] (e : ι → OpenPartialHomeomorph A (ReciprocityTheory.L2DbarEstimates.V n)) (ρ : ι → A → ℝ≥0∞) (e' : κ → OpenPartialHomeomorph B (ReciprocityTheory.L2DbarEstimates.V n)) (ρ' : κ → B → ℝ≥0∞), (∀ i j, DifferentiableOn ℂ (e j ∘ (e i).symm) (ReciprocityTheory.L2DbarEstimates.Y.ovl e i j)) → (∀ i j y, y ∈ (e i).source → y ∈ (e j).source → ρ i y = ENNReal.ofReal (‖GlobalTheory.ChartGlue.transDet (e i) (e j) y‖ ^ 2) * ρ j y) → (∀ i j, DifferentiableOn ℂ (e' j ∘ (e' i).symm) (ReciprocityTheory.L2DbarEstimates.Y.ovl e' i j)) → (∀ i j y, y ∈ (e' i).source → y ∈ (e' j).source → ρ' i y = ENNReal.ofReal (‖GlobalTheory.ChartGlue.transDet (e' i) (e' j) y‖ ^ 2) * ρ' j y) → ∀ (m : B → A), Continuous m → ∀ T : Set A, T.Finite → (m ⁻¹' T).Finite → ∀ d : ℕ, d ≠ 0 → (∀ x ∉ T, (m ⁻¹' {x}).encard = d) → (∀ z, m z ∉ T → ∃ i j, z ∈ (e' j).source ∧ m z ∈ (e i).source ∧ ∀ w ∈ (e' j).source, m w ∈ (e i).source → e' j w = e i (m w) ∧ ρ' j w = ρ i (m w)) → GlobalTheory.ChartGlue.glueMeas e' ρ' Set.univ = d * GlobalTheory.ChartGlue.glueMeas e ρ Set.univ := by
  first | exact @GlobalTheory.GlueCover.glueMeas_univ_of_cover | exact GlobalTheory.GlueCover.glueMeas_univ_of_cover | (intros; apply GlobalTheory.GlueCover.glueMeas_univ_of_cover <;> assumption)
end _root_.GlobalTheory.T
