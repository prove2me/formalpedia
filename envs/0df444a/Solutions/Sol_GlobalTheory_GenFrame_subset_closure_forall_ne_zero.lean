-- Prove2me | solution 1 for GlobalTheory.GenFrame.subset_closure_forall_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T17:44:51.861346+00:00
-- url     : https://prove2.me/submissions/d3be03c2-52d9-490d-8369-cdd923b9a300

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_BasePsiLeviLowerBound
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_NormOrderStatement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_PTNonempty
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_GGConn
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FourierCoefficientDomain
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_JetGauges_ReadingRatioAddition
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_DifferentiableOnOfTendstoLocallyUniformlyOn
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_DomSubsetClosureIsGenFrame
import Theorems.Thm_GlobalTheory_SCV_eqOn_of_eqOn_open


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.T0 ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates GlobalTheory.IndefiniteRowSideFullHecke.GenericFrameParameters
open Cardinal Topology
open GlobalTheory GlobalTheory.GenFrame
namespace GlobalTheory.GenFrame
theorem _root_.solution {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [FiniteDimensional ℂ E] {U : Set E} (hU : IsOpen U) (hc : IsPreconnected U)
    {J : Type*} [Countable J] (f : J → E → ℂ) (hf : ∀ j, DifferentiableOn ℂ (f j) U)
    (hne : ∀ j, ∃ x ∈ U, f j x ≠ 0) : U ⊆ closure {x | x ∈ U ∧ ∀ j, f j x ≠ 0} := by
  have : CompleteSpace E := FiniteDimensional.complete ℂ E
  set W : J → Set E := fun j => (U ∩ f j ⁻¹' {0}ᶜ) ∪ (closure U)ᶜ with hW
  have hWo : ∀ j, IsOpen (W j) := fun j =>
    ((hf j).continuousOn.isOpen_inter_preimage hU isOpen_compl_singleton).union
      isClosed_closure.isOpen_compl
  have hWd : ∀ j, Dense (W j) := by
    intro j
    rw [dense_iff_inter_open]
    intro O hO hOne
    by_contra hemp
    rw [Set.not_nonempty_iff_eq_empty] at hemp
    have hnot : ∀ y ∈ O, y ∉ W j := fun y hy hyW => by
      have : y ∈ O ∩ W j := ⟨hy, hyW⟩
      rw [hemp] at this
      exact this
    obtain ⟨y, hy⟩ := hOne
    have hyc : y ∈ closure U := by
      by_contra h
      exact hnot y hy (Or.inr h)
    obtain ⟨z, hzO, hzU⟩ := mem_closure_iff.mp hyc O hO hy
    have hz := GlobalTheory.SCV.eqOn_of_eqOn_open (g := fun _ => (0 : ℂ)) hU hc (hf j)
      (differentiableOn_const 0) (hO.inter hU) ⟨z, hzO, hzU⟩ Set.inter_subset_right
      (fun w hw => by
        by_contra h
        exact hnot w hw.1 (Or.inl ⟨hw.2, h⟩))
    obtain ⟨x, hx, hx0⟩ := hne j
    exact hx0 (hz hx)
  have hD := dense_iInter_of_isOpen hWo hWd
  refine (hD.open_subset_closure_inter hU).trans (closure_mono ?_)
  rintro x ⟨hxU, hx⟩
  refine ⟨hxU, fun j => ?_⟩
  rcases Set.mem_iInter.mp hx j with h | h
  · exact h.2
  · exact absurd (subset_closure hxU) h
end GlobalTheory.GenFrame
