-- Prove2me | solution 1 for GroundTheory.Automorphic.UnitaryRep.isCompactOperator_compHom_subtype
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-27T04:44:16.167306+00:00
-- url     : https://prove2.me/submissions/be3f78af-f38f-4f5d-9dfa-356737466fb9

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_DiscreteSpectrumAbstract
import Definitions.Def_GroundTheory_AutomorphicForms_MultiplicityOne_OpenSubgroupRep
import Theorems.Thm_GroundTheory_Automorphic_UnitaryRep_integrated_compHom_subtype

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
variable [MeasurableSpace G] [BorelSpace G]
namespace GroundTheory.Automorphic.UnitaryRep
theorem _root_.solution (π : UnitaryRep G H) (μ : Measure G)
    [IsFiniteMeasureOnCompacts μ] {L : Subgroup G} (hL : IsOpen (L : Set G))
    (hcpt : ∀ F : CompactlySupportedContinuousMap G ℂ,
      IsCompactOperator (π.integrated μ (ccToL1 μ F)))
    (f : CompactlySupportedContinuousMap L ℂ) :
    haveI := isFiniteMeasureOnCompacts_comap μ hL
    IsCompactOperator ((π.compHom L.subtype continuous_subtype_val).integrated
      (μ.comap ((↑) : L → G)) (ccToL1 (μ.comap ((↑) : L → G)) f)) := by
  have := isFiniteMeasureOnCompacts_comap μ hL
  rw [integrated_compHom_subtype π μ hL f]
  exact hcpt _
end GroundTheory.Automorphic.UnitaryRep
