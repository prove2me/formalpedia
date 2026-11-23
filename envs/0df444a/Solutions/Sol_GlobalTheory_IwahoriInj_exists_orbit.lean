-- Prove2me | solution 1 for GlobalTheory.IwahoriInj.exists_orbit
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:35:14.844015+00:00
-- url     : https://prove2.me/submissions/99c4ffed-dfa1-4da6-adfd-93cc3e1d77e7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_IsSubquotientDetRepParInd
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_T2SpaceGeneralLinearGroup
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_TwistedKernelFixed
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IsLocallyConstantOrbit
import Theorems.Thm_GlobalTheory_IwahoriInj_mem_fixed
import Theorems.Thm_GlobalTheory_IwahoriInj_isLocallyConstant_orbit

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL ValuativeRel MeasureTheory
open GlobalTheory GlobalTheory.IwahoriInj
variable {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V] {π : Representation ℂ G V}
variable [TopologicalSpace G] [IsTopologicalGroup G]
namespace GlobalTheory.IwahoriInj
theorem _root_.solution (hπ : IsSmooth π) {H : Subgroup G} (hH : IsCompact (H : Set G)) (v : V) :
    ∃ S : Finset V, (∀ u, u ∈ S ↔ ∃ h ∈ H, π h v = u) ∧ ∑ u ∈ S, u ∈ fixed π H := by
  haveI : CompactSpace H := isCompact_iff_compactSpace.1 hH
  have hf := ((isLocallyConstant_orbit hπ v).comp_continuous (f := fun h : H => (h : G))
    continuous_subtype_val).range_finite
  have hS : ∀ u, u ∈ hf.toFinset ↔ ∃ h ∈ H, π h v = u := fun u => by simp
  refine ⟨hf.toFinset, hS, mem_fixed.2 fun g hg => ?_⟩
  rw [map_sum]
  have key : ∀ g ∈ H, ∀ u ∈ hf.toFinset, π g u ∈ hf.toFinset := fun g hg u hu => by
    obtain ⟨h, hh, rfl⟩ := (hS u).1 hu
    exact (hS _).2 ⟨g * h, mul_mem hg hh, by simp⟩
  refine Finset.sum_nbij' (fun u => π g u) (fun u => π g⁻¹ u) (key g hg) (key _ (inv_mem hg))
    (fun u _ => ?_) (fun u _ => ?_) fun _ _ => rfl
  · rw [← Module.End.mul_apply, ← map_mul]; simp
  · rw [← Module.End.mul_apply, ← map_mul]; simp
end GlobalTheory.IwahoriInj
