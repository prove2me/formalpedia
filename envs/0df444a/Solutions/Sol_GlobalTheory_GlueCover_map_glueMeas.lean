-- Prove2me | solution 1 for GlobalTheory.GlueCover.map_glueMeas
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T17:45:35.272609+00:00
-- url     : https://prove2.me/submissions/24990b71-40e1-4da3-ba13-f407a2d7fa54

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_ChartMeasApplyOfSubset
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ChartDensityChangeFormula
import Theorems.Thm_GlobalTheory_GlueCover_glueMeas_finite
import Theorems.Thm_GlobalTheory_GlueCover_exists_evenly_covered

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
variable {A B ι κ : Type} [TopologicalSpace A] [TopologicalSpace B] [T2Space A] [T2Space B]
  [SecondCountableTopology A] [SecondCountableTopology B] [MeasurableSpace A] [BorelSpace A]
  [MeasurableSpace B] [BorelSpace B]
  {e : ι → OpenPartialHomeomorph A (V n)} {ρ : ι → A → ℝ≥0∞}
  {e' : κ → OpenPartialHomeomorph B (V n)} {ρ' : κ → B → ℝ≥0∞} {m : B → A}
namespace GlobalTheory.GlueCover
theorem _root_.solution (hn : n ≠ 0)
    (hd : ∀ i j, DifferentiableOn ℂ (e j ∘ (e i).symm) (ovl e i j))
    (hρ : ∀ i j y, y ∈ (e i).source → y ∈ (e j).source →
      ρ i y = ENNReal.ofReal (‖transDet (e i) (e j) y‖ ^ 2) * ρ j y)
    (hd' : ∀ i j, DifferentiableOn ℂ (e' j ∘ (e' i).symm) (ovl e' i j))
    (hρ' : ∀ i j y, y ∈ (e' i).source → y ∈ (e' j).source →
      ρ' i y = ENNReal.ofReal (‖transDet (e' i) (e' j) y‖ ^ 2) * ρ' j y)
    (hm : Continuous m) {T : Set A} (hT : T.Finite) (hT' : (m ⁻¹' T).Finite) {d : ℕ}
    (hfib : ∀ x ∉ T, (m ⁻¹' {x}).encard = d)
    (hch : ∀ z, m z ∉ T → ∃ i j, z ∈ (e' j).source ∧ m z ∈ (e i).source ∧ ∀ w ∈ (e' j).source,
      m w ∈ (e i).source → e' j w = e i (m w) ∧ ρ' j w = ρ i (m w)) :
    Measure.map m (glueMeas e' ρ') = (d : ℝ≥0∞) • glueMeas e ρ := by
  have hW : ∀ x : {x // x ∉ T}, ∃ W : Set A, IsOpen W ∧ x.1 ∈ W ∧
      ∀ Q : Set A, MeasurableSet Q → Q ⊆ W →
        glueMeas e' ρ' (m ⁻¹' Q) = d * glueMeas e ρ Q := fun x =>
    exists_evenly_covered hd hρ hd' hρ' hm hT hfib hch x.2
  choose W hWo hxW hWQ using hW
  obtain ⟨C, hC, hCW⟩ := TopologicalSpace.isOpen_iUnion_countable W hWo
  haveI : Countable C := hC.to_subtype
  refine Measure.ext_of_iUnion_eq_univ
    (s := fun o : Option C => o.elim T fun c => W c.1) ?_ fun o => ?_
  · refine eq_univ_of_forall fun x => ?_
    by_cases hx : x ∈ T
    · exact mem_iUnion.2 ⟨none, hx⟩
    · have hmem : x ∈ ⋃ i ∈ C, W i := by
        rw [hCW]
        exact mem_iUnion.2 ⟨⟨x, hx⟩, hxW _⟩
      obtain ⟨c, hc, hxc⟩ := mem_iUnion₂.1 hmem
      exact mem_iUnion.2 ⟨some ⟨c, hc⟩, hxc⟩
  · cases o with
    | none =>
      show (Measure.map m (glueMeas e' ρ')).restrict T = ((d : ℝ≥0∞) • glueMeas e ρ).restrict T
      rw [Measure.restrict_eq_zero.2, Measure.restrict_eq_zero.2]
      · simp [glueMeas_finite hn e ρ hT]
      · rw [Measure.map_apply hm.measurable hT.measurableSet]
        exact glueMeas_finite hn e' ρ' hT'
    | some c =>
      show (Measure.map m (glueMeas e' ρ')).restrict (W c.1) =
        ((d : ℝ≥0∞) • glueMeas e ρ).restrict (W c.1)
      ext Q hQ
      have hQW := hQ.inter (hWo c.1).measurableSet
      rw [Measure.restrict_apply hQ, Measure.restrict_apply hQ,
        Measure.map_apply hm.measurable hQW, hWQ c.1 _ hQW inter_subset_right]
      simp
end GlobalTheory.GlueCover
