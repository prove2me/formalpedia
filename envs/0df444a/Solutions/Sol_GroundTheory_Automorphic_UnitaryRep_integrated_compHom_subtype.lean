-- Prove2me | solution 1 for GroundTheory.Automorphic.UnitaryRep.integrated_compHom_subtype
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T00:54:21.762854+00:00
-- url     : https://prove2.me/submissions/ef7ef5de-1cd2-403c-a0fe-9f5e9f571612

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_DiscreteSpectrumAbstract
import Definitions.Def_GroundTheory_AutomorphicForms_MultiplicityOne_OpenSubgroupRep
import Theorems.Thm_GroundTheory_Automorphic_UnitaryRep_extendZero_apply_coe
import Theorems.Thm_GroundTheory_Automorphic_UnitaryRep_extendZero_apply_of_notMem
import Theorems.Thm_GroundTheory_Automorphic_UnitaryRep_IsEquivalent_trans
import Theorems.Thm_GroundTheory_Automorphic_UnitaryRep_integrated_ccToL1_apply


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
theorem _root_.solution (π : UnitaryRep G H) (μ : Measure G) [IsFiniteMeasureOnCompacts μ]
    {L : Subgroup G} (hL : IsOpen (L : Set G)) (f : CompactlySupportedContinuousMap L ℂ) :
    haveI := isFiniteMeasureOnCompacts_comap μ hL
    (π.compHom L.subtype continuous_subtype_val).integrated (μ.comap ((↑) : L → G))
        (ccToL1 (μ.comap ((↑) : L → G)) f) =
      π.integrated μ (ccToL1 μ (extendZero hL f)) := by
  have := isFiniteMeasureOnCompacts_comap μ hL
  refine ContinuousLinearMap.ext fun v => ?_
  rw [integrated_ccToL1_apply, integrated_ccToL1_apply]
  have h1 : ∫ x : L, f x • (π.compHom L.subtype continuous_subtype_val) x v
      ∂(μ.comap ((↑) : L → G)) =
      ∫ x : L, (fun g : G => extendZero hL f g • π g v) (x : G) ∂(μ.comap ((↑) : L → G)) := by
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    show f x • _ = extendZero hL f x • _
    rw [extendZero_apply_coe]
    rfl
  rw [h1]
  refine (integral_subtype_comap (μ := μ) (s := (L : Set G)) hL.measurableSet
    (fun g => extendZero hL f g • π g v)).trans ?_
  refine setIntegral_eq_integral_of_forall_compl_eq_zero fun g hg => ?_
  rw [extendZero_apply_of_notMem hL f hg, zero_smul]
end GroundTheory.Automorphic.UnitaryRep
