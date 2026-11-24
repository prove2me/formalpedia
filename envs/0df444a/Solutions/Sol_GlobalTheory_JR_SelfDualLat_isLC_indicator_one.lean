-- Prove2me | solution 1 for GlobalTheory.JR.SelfDualLat.isLC_indicator_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T18:09:35.905941+00:00
-- url     : https://prove2.me/submissions/3edcbca5-8631-4a25-9255-1023c0f20077

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_IsTestRep
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_SelfDualMeasureExistsUniqueFourierInversionStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_UnramifiedStandardAddCharConductorPropertiesStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_SelfDualIffLatticeVolumeAndPlancherel

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.JR Matrix MeasureTheory Filter Topology
open GlobalTheory GlobalTheory.JR GlobalTheory.JR.SelfDualLat
namespace GlobalTheory.JR.SelfDualLat
theorem _root_.solution {X : Type} [TopologicalSpace X] (s : Set X) (h : IsClopen s) :
    IsLocallyConstant (s.indicator (fun _ => (1 : ℂ))) := by
  classical
  intro B
  rw [Set.indicator_preimage, Set.ite]
  refine (IsOpen.inter ?_ h.isOpen).union ?_
  · rw [Set.preimage_const]; split_ifs <;> simp
  · rw [Set.diff_eq]
    refine IsOpen.inter ?_ h.isClosed.isOpen_compl
    change IsOpen ((fun _ : X => (0:ℂ)) ⁻¹' B)
    rw [Set.preimage_const]; split_ifs <;> simp
end GlobalTheory.JR.SelfDualLat
