-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.SW.ThW.GaussFlat.swapCurry_measurePreserving
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T13:33:45.251028+00:00
-- url     : https://prove2.me/submissions/f8b18bb4-18d3-4db5-b6f0-676bac5a85d1

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_SumRhoEqTrace
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_ArchimedeanGaussianFourier
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_GaussianFourierTransformFormula

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain MeasureTheory Matrix Topology GlobalTheory.CompanionTheory.SW.Core GlobalTheory.CompanionTheory.SW.ThW
open scoped ENNReal NNReal MatrixGroups Kronecker
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.ThW GlobalTheory.CompanionTheory.SW.ThW.GaussFlat
namespace GlobalTheory.CompanionTheory.SW.ThW.GaussFlat
theorem _root_.solution (α β : Type) [Fintype α] [Fintype β] :
    MeasurePreserving (swapCurry α β) volume volume := by
  have h : (volume : Measure (α × β → ℝ)) =
      (volume : Measure (β → α → ℝ)).map (swapCurry α β).symm := by
    refine Measure.pi_eq fun s hs => ?_
    rw [Measure.map_apply (MeasurableEquiv.measurable _) (MeasurableSet.univ_pi hs)]
    have e : (swapCurry α β).symm ⁻¹' Set.univ.pi s =
        Set.univ.pi (fun b => Set.univ.pi (fun a => s (a, b))) := by
      ext f
      simp only [Set.mem_preimage, Set.mem_univ_pi]
      exact ⟨fun H b a => H (a, b), fun H p => H p.2 p.1⟩
    rw [e, volume_pi, Measure.pi_pi]
    simp_rw [volume_pi, Measure.pi_pi]
    rw [Fintype.prod_prod_type_right]
  refine ⟨(swapCurry α β).measurable, ?_⟩
  rw [h, Measure.map_map (MeasurableEquiv.measurable _) (MeasurableEquiv.measurable _)]
  simp
end GlobalTheory.CompanionTheory.SW.ThW.GaussFlat
