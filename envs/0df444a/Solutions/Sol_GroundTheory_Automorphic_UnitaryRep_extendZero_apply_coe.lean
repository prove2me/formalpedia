-- Prove2me | solution 1 for GroundTheory.Automorphic.UnitaryRep.extendZero_apply_coe
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T00:45:22.594071+00:00
-- url     : https://prove2.me/submissions/cdcda3d9-8930-4356-8292-5f533dfbb5e3

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
    (f : CompactlySupportedContinuousMap L ℂ) (x : L) : extendZero hL f x = f x := by
  show (if h : (x : G) ∈ L then f ⟨x, h⟩ else 0) = f x
  rw [dif_pos x.2]
end GroundTheory.Automorphic.UnitaryRep
