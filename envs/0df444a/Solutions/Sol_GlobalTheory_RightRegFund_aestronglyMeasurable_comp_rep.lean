-- Prove2me | solution 1 for GlobalTheory.RightRegFund.aestronglyMeasurable_comp_rep
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T20:06:03.338555+00:00
-- url     : https://prove2.me/submissions/04420e9e-c6fd-4ee1-92ed-63a0d19b5e62

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_AestronglyMeasurableCompRep
import Theorems.Thm_GlobalTheory_RightRegFund_rep_eq
import Theorems.Thm_GlobalTheory_RightRegFund_ae_good

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Filter Set
open scoped ENNReal symmDiff Topology Pointwise
open GlobalTheory GlobalTheory.RightRegFund
variable {G : Type} [Group G]
variable {Γ : Subgroup G} {D : Set G} {r : G → G}
variable [TopologicalSpace G] [IsTopologicalGroup G] [MeasurableSpace G] [BorelSpace G]
  {μ : Measure G} [μ.IsMulLeftInvariant] [Countable Γ]
namespace GlobalTheory.RightRegFund
theorem _root_.solution (hD : IsFundamentalDomain Γ D μ) (hDm : MeasurableSet D)
    (hr : ∀ y, ∃ γ : Γ, r y = (γ : G) * y ∧ r y ∈ D) {f : G → ℂ} (hf : StronglyMeasurable f) :
    AEStronglyMeasurable (fun y => f (r y)) μ := by
  have hU : (⋃ γ : Γ, (fun y => (γ : G) * y) ⁻¹' D) = univ := by
    refine eq_univ_of_forall fun y => ?_
    obtain ⟨γ, h1, h2⟩ := hr y
    exact mem_iUnion.2 ⟨γ, by simpa [← h1] using h2⟩
  rw [← Measure.restrict_univ (μ := μ), ← hU, aestronglyMeasurable_iUnion_iff]
  intro γ
  have hm : Measurable fun y => (γ : G) * y := measurable_const_mul _
  refine ((hf.comp_measurable hm).aestronglyMeasurable).congr ?_
  refine (ae_restrict_iff' (hm hDm)).2 ((ae_good hD).mono fun y hy h => ?_)
  simp only [Function.comp]
  rw [rep_eq hr hy h]
end GlobalTheory.RightRegFund
