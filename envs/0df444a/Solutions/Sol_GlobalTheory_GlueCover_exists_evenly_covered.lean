-- Prove2me | solution 1 for GlobalTheory.GlueCover.exists_evenly_covered
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T17:09:34.005411+00:00
-- url     : https://prove2.me/submissions/8e2cfe7b-926b-499b-b26c-c8753175d287

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_ChartMeasApplyOfSubset
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ChartDensityChangeFormula
import Theorems.Thm_GlobalTheory_GlueCover_exists_sheet

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
theorem _root_.solution
    (hd : ∀ i j, DifferentiableOn ℂ (e j ∘ (e i).symm) (ovl e i j))
    (hρ : ∀ i j y, y ∈ (e i).source → y ∈ (e j).source →
      ρ i y = ENNReal.ofReal (‖transDet (e i) (e j) y‖ ^ 2) * ρ j y)
    (hd' : ∀ i j, DifferentiableOn ℂ (e' j ∘ (e' i).symm) (ovl e' i j))
    (hρ' : ∀ i j y, y ∈ (e' i).source → y ∈ (e' j).source →
      ρ' i y = ENNReal.ofReal (‖transDet (e' i) (e' j) y‖ ^ 2) * ρ' j y)
    (hm : Continuous m) {T : Set A} (hT : T.Finite) {d : ℕ}
    (hfib : ∀ x ∉ T, (m ⁻¹' {x}).encard = d)
    (hch : ∀ z, m z ∉ T → ∃ i j, z ∈ (e' j).source ∧ m z ∈ (e i).source ∧ ∀ w ∈ (e' j).source,
      m w ∈ (e i).source → e' j w = e i (m w) ∧ ρ' j w = ρ i (m w))
    {x : A} (hx : x ∉ T) :
    ∃ W : Set A, IsOpen W ∧ x ∈ W ∧ ∀ Q : Set A, MeasurableSet Q → Q ⊆ W →
      glueMeas e' ρ' (m ⁻¹' Q) = d * glueMeas e ρ Q := by
  classical
  have hfin : ∀ y ∉ T, (m ⁻¹' {y}).Finite := fun y hy => finite_of_encard_eq_coe (hfib y hy)
  have hcard : ∀ y (hy : y ∉ T), (hfin y hy).toFinset.card = d := fun y hy => by
    have h := hfib y hy
    rw [← (hfin y hy).coe_toFinset, encard_coe_eq_coe_finsetCard] at h
    exact_mod_cast h
  obtain ⟨U, hU, hUd⟩ := (hfin x hx).t2_separation
  have hFc := hcard x hx
  have hFm : ∀ z, z ∈ (hfin x hx).toFinset ↔ m z = x := fun z => by simp
  generalize (hfin x hx).toFinset = F at hFc hFm
  have hzF : ∀ z ∈ F, m z = x := fun z hz => (hFm z).1 hz
  have hzT : ∀ z ∈ F, m z ∉ T := fun z hz => by rwa [hzF z hz]
  have hsheet : ∀ z, z ∈ F → ∃ M : Set B, M ⊆ U z ∧ IsOpen M ∧ z ∈ M ∧ IsOpen (m '' M) ∧
      ∀ Q : Set A, MeasurableSet Q → Q ⊆ m '' M →
        glueMeas e' ρ' (M ∩ m ⁻¹' Q) = glueMeas e ρ Q := fun z hz =>
    exists_sheet hd hρ hd' hρ' hm (hch z (hzT z hz)) (hU z).2 (hU z).1
  choose! M hMU hMo hzM hMi hMQ using hsheet
  refine ⟨(⋂ z ∈ F, m '' M z) ∩ Tᶜ, (isOpen_biInter_finset hMi).inter hT.isClosed.isOpen_compl,
    ⟨mem_iInter₂.2 fun z hz => ⟨z, hzM z hz, hzF z hz⟩, hx⟩, fun Q hQ hQW => ?_⟩
  have hdisj : ∀ z₁ ∈ F, ∀ z₂ ∈ F, z₁ ≠ z₂ → Disjoint (M z₁) (M z₂) := fun z₁ h₁ z₂ h₂ hne =>
    Disjoint.mono (hMU z₁ h₁) (hMU z₂ h₂) (hUd (hzF z₁ h₁) (hzF z₂ h₂) hne)
  have key : m ⁻¹' Q = ⋃ z ∈ F, (M z ∩ m ⁻¹' Q) := by
    ext w
    constructor
    · intro hw
      have hWx := hQW hw
      have hpre : ∀ z ∈ F, ∃ z', z' ∈ M z ∧ m z' = m w := fun z hz => by
        obtain ⟨z', h₁, h₂⟩ := mem_iInter₂.1 hWx.1 z hz
        exact ⟨z', h₁, h₂⟩
      haveI : Nonempty B := ⟨w⟩
      choose! f hfM hfm using hpre
      have hinj : InjOn f F := fun z₁ h₁ z₂ h₂ h12 => by
        by_contra hne
        exact disjoint_left.1 (hdisj z₁ h₁ z₂ h₂ hne) (hfM z₁ h₁) (h12 ▸ hfM z₂ h₂)
      have hsub : F.image f ⊆ (hfin (m w) hWx.2).toFinset := fun v hv => by
        obtain ⟨z, hz, rfl⟩ := Finset.mem_image.1 hv
        simpa using hfm z hz
      have heq := Finset.eq_of_subset_of_card_le hsub (by
        rw [Finset.card_image_of_injOn hinj, hcard _ hWx.2, hFc])
      have hwm : w ∈ F.image f := by
        rw [heq]
        simp
      obtain ⟨z, hz, hzw⟩ := Finset.mem_image.1 hwm
      exact mem_iUnion₂.2 ⟨z, hz, hzw ▸ hfM z hz, hw⟩
    · intro hw
      obtain ⟨z, _, _, h⟩ := mem_iUnion₂.1 hw
      exact h
  rw [key, measure_biUnion_finset
    (fun z₁ h₁ z₂ h₂ hne => Disjoint.mono inter_subset_left inter_subset_left
      (hdisj z₁ h₁ z₂ h₂ hne))
    (fun z hz => (hMo z hz).measurableSet.inter (hm.measurable hQ)),
    Finset.sum_congr rfl fun z hz => hMQ z hz Q hQ
      fun y hy => mem_iInter₂.1 (hQW hy).1 z hz,
    Finset.sum_const, nsmul_eq_mul, hFc]
end GlobalTheory.GlueCover
