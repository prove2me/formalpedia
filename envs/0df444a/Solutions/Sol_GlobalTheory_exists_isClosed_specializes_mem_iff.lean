-- Prove2me | solution 1 for GlobalTheory.exists_isClosed_specializes_mem_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T22:42:41.224015+00:00
-- url     : https://prove2.me/submissions/0a41dfb6-454c-4892-85d3-2bd28aa29d8e

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_IntToRatA
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_FiniteResidueFieldOfIsClosedOfLocallyOfFiniteTyp

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory
variable {T : Type*} [TopologicalSpace T] [JacobsonSpace T]
namespace GlobalTheory
theorem _root_.solution (ξ : T) {ι : Type*} [Finite ι] (U : ι → Set T)
    (hU : ∀ i, IsOpen (U i)) {W : Set T} (hW : IsOpen W) (hξ : ξ ∈ W) :
    ∃ x : T, IsClosed ({x} : Set T) ∧ ξ ⤳ x ∧ x ∈ W ∧ ∀ i, x ∈ U i ↔ ξ ∈ U i := by
  have hO : IsOpen (W ∩ ⋂ i : {i // ξ ∈ U i}, U i.1) :=
    hW.inter (isOpen_iInter_of_finite fun i => hU i.1)
  obtain ⟨x, ⟨hxc, hxW, hxU⟩, hx⟩ := nonempty_inter_closedPoints
    (Z := closure {ξ} ∩ (W ∩ ⋂ i : {i // ξ ∈ U i}, U i.1))
    ⟨ξ, subset_closure rfl, hξ, Set.mem_iInter.mpr fun i => i.2⟩
    (isClosed_closure.isLocallyClosed.inter hO.isLocallyClosed)
  have hs : ξ ⤳ x := specializes_iff_mem_closure.mpr hxc
  exact ⟨x, hx, hs, hxW, fun i =>
    ⟨fun h => hs.mem_open (hU i) h, fun h => Set.mem_iInter.mp hxU ⟨i, h⟩⟩⟩
end GlobalTheory
