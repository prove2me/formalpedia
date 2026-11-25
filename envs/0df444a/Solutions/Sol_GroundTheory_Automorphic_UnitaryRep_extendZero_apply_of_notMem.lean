-- Prove2me | solution 1 for GroundTheory.Automorphic.UnitaryRep.extendZero_apply_of_notMem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T00:43:33.497802+00:00
-- url     : https://prove2.me/submissions/7e29cfd2-beec-44b9-9f0b-8bad222c1966

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_DiscreteSpectrumAbstract
import Definitions.Def_GroundTheory_AutomorphicForms_MultiplicityOne_OpenSubgroupRep

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Set Filter Topology Function
open GroundTheory GroundTheory.Automorphic
noncomputable section
open GroundTheory.Automorphic.UnitaryRep
variable {G : Type*} [Group G] [TopologicalSpace G]
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
set_option linter.unusedSectionVars false
variable [IsTopologicalGroup G] [T2Space G]
open Classical
namespace GroundTheory.Automorphic.UnitaryRep
theorem _root_.solution {L : Subgroup G} (hL : IsOpen (L : Set G))
    (f : CompactlySupportedContinuousMap L ℂ) {g : G} (hg : g ∉ L) : extendZero hL f g = 0 := by
  show (if h : g ∈ L then f ⟨g, h⟩ else 0) = 0
  rw [dif_neg hg]
end GroundTheory.Automorphic.UnitaryRep
