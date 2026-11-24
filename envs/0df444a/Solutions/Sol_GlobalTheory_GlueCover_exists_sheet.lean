-- Prove2me | solution 1 for GlobalTheory.GlueCover.exists_sheet
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T16:34:48.695579+00:00
-- url     : https://prove2.me/submissions/76ec76c6-b22d-4da7-99a8-f70a425939be

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_ChartMeasApplyOfSubset
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ChartDensityChangeFormula

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
set_option autoImplicit false
open MeasureTheory Set Topology
open scoped ENNReal
variable {n : ℕ}
variable {A B ι κ : Type} [TopologicalSpace A] [TopologicalSpace B] [T2Space A] [T2Space B]
  [SecondCountableTopology A] [SecondCountableTopology B] [MeasurableSpace A] [BorelSpace A]
  [MeasurableSpace B] [BorelSpace B]
  {e : ι → OpenPartialHomeomorph A (_root_.ReciprocityTheory.L2DbarEstimates.V n)} {ρ : ι → A → ℝ≥0∞}
  {e' : κ → OpenPartialHomeomorph B (_root_.ReciprocityTheory.L2DbarEstimates.V n)} {ρ' : κ → B → ℝ≥0∞} {m : B → A}
omit [T2Space A] [T2Space B]
namespace GlobalTheory.GlueCover
namespace _root_.GlobalTheory.GlueCover
theorem _root_.solution
    (hd : ∀ i j, DifferentiableOn ℂ (e j ∘ (e i).symm) (_root_.ReciprocityTheory.L2DbarEstimates.Y.ovl e i j))
    (hρ : ∀ i j y, y ∈ (e i).source → y ∈ (e j).source →
      ρ i y = ENNReal.ofReal (‖_root_.GlobalTheory.ChartGlue.transDet (e i) (e j) y‖ ^ 2) * ρ j y)
    (hd' : ∀ i j, DifferentiableOn ℂ (e' j ∘ (e' i).symm) (_root_.ReciprocityTheory.L2DbarEstimates.Y.ovl e' i j))
    (hρ' : ∀ i j y, y ∈ (e' i).source → y ∈ (e' j).source →
      ρ' i y = ENNReal.ofReal (‖_root_.GlobalTheory.ChartGlue.transDet (e' i) (e' j) y‖ ^ 2) * ρ' j y)
    (hm : Continuous m) {z : B}
    (hch : ∃ i j, z ∈ (e' j).source ∧ m z ∈ (e i).source ∧ ∀ w ∈ (e' j).source,
      m w ∈ (e i).source → e' j w = e i (m w) ∧ ρ' j w = ρ i (m w))
    {U : Set B} (hUo : IsOpen U) (hzU : z ∈ U) :
    ∃ M : Set B, M ⊆ U ∧ IsOpen M ∧ z ∈ M ∧ IsOpen (m '' M) ∧
      ∀ Q : Set A, MeasurableSet Q → Q ⊆ m '' M →
        _root_.GlobalTheory.ChartGlue.glueMeas e' ρ' (M ∩ m ⁻¹' Q) = _root_.GlobalTheory.ChartGlue.glueMeas e ρ Q := by
  obtain ⟨i, j, hzj, hzi, hcompat⟩ := hch
  have hMo : IsOpen (U ∩ (e' j).source ∩ m ⁻¹' (e i).source) :=
    (hUo.inter (e' j).open_source).inter ((e i).open_source.preimage hm)
  refine ⟨U ∩ (e' j).source ∩ m ⁻¹' (e i).source, fun w hw => hw.1.1, hMo,
    ⟨⟨hzU, hzj⟩, hzi⟩, ?_, ?_⟩
  · have hm_eq : ∀ w ∈ U ∩ (e' j).source ∩ m ⁻¹' (e i).source,
        (e i).symm (e' j w) = m w := by
      intro w hw
      rw [(hcompat w hw.1.2 hw.2).1, (e i).left_inv hw.2]
    have himage : m '' (U ∩ (e' j).source ∩ m ⁻¹' (e i).source) =
        (e i).symm '' (e' j '' (U ∩ (e' j).source ∩ m ⁻¹' (e i).source)) := by
      rw [Set.image_image]
      exact (Set.image_congr hm_eq).symm
    rw [himage]
    have hS : IsOpen (e' j '' (U ∩ (e' j).source ∩ m ⁻¹' (e i).source)) :=
      (e' j).isOpen_image_of_subset_source hMo (fun w hw => hw.1.2)
    refine (e i).symm.isOpen_image_of_subset_source hS ?_
    rintro _ ⟨w, hw, rfl⟩
    rw [OpenPartialHomeomorph.symm_source, (hcompat w hw.1.2 hw.2).1]
    exact (e i).map_source hw.2
  · intro Q hQ hQM
    have hQi : Q ⊆ (e i).source := by
      intro q hq
      obtain ⟨w, hw, rfl⟩ := hQM hq
      exact hw.2
    have hPm : MeasurableSet (U ∩ (e' j).source ∩ m ⁻¹' (e i).source ∩ m ⁻¹' Q) :=
      hMo.measurableSet.inter (hm.measurable hQ)
    have hPj : U ∩ (e' j).source ∩ m ⁻¹' (e i).source ∩ m ⁻¹' Q ⊆ (e' j).source :=
      fun w hw => hw.1.1.2
    rw [_root_.GlobalTheory.ChartGlue.glueMeas_apply e' ρ' hd' hρ' j hPm hPj,
      _root_.GlobalTheory.ChartGlue.glueMeas_apply e ρ hd hρ i hQ hQi,
      _root_.GlobalTheory.ChartGlue.chartMeas_apply_of_subset _ _ hPm hPj,
      _root_.GlobalTheory.ChartGlue.chartMeas_apply_of_subset _ _ hQ hQi]
    have himg : e' j '' (U ∩ (e' j).source ∩ m ⁻¹' (e i).source ∩ m ⁻¹' Q) = e i '' Q := by
      ext v
      constructor
      · rintro ⟨w, hw, rfl⟩
        exact ⟨m w, hw.2, ((hcompat w hw.1.1.2 hw.1.2).1).symm⟩
      · rintro ⟨q, hq, rfl⟩
        obtain ⟨w, hw, rfl⟩ := hQM hq
        exact ⟨w, ⟨hw, hq⟩, (hcompat w hw.1.2 hw.2).1⟩
    rw [himg]
    refine setLIntegral_congr_fun (_root_.GlobalTheory.ChartGlue.measurableSet_image _ hQ hQi) ?_
    rintro v ⟨q, hq, rfl⟩
    obtain ⟨w, hw, rfl⟩ := hQM hq
    beta_reduce
    rw [(e i).left_inv hw.2, ← (hcompat w hw.1.2 hw.2).1, (e' j).left_inv hw.1.2]
    exact (hcompat w hw.1.2 hw.2).2
end _root_.GlobalTheory.GlueCover
end GlobalTheory.GlueCover
