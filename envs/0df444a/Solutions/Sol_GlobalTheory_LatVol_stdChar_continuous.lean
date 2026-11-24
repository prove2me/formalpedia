-- Prove2me | solution 1 for GlobalTheory.LatVol.stdChar_continuous
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T18:38:47.806991+00:00
-- url     : https://prove2.me/submissions/17510fac-5b6c-44a3-b7d0-5bf92b7e7d32

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_IsTestRep
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_EtaleHermitianPairStructureFactsStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_SelfDualIffLatticeVolumeAndPlancherelStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_UnramifiedValuationParitySignCharacterKernelNormStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_FiniteNormedAlgebraEqModuleTopology
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_NonemptyMeasAndReps
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_VolumeScaledIntegersMulVolumeDualEqOne

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.JR Matrix MeasureTheory Filter Topology
open GlobalTheory GlobalTheory.LatVol
namespace GlobalTheory.LatVol
theorem _root_.solution {F : Type} [NontriviallyNormedField F] (ψ : AddChar F ℂ) (hψ : IsStdChar ψ) :
    Continuous ψ := by
  refine continuous_iff_continuousAt.2 fun x => ?_
  have h : ∀ᶠ y in 𝓝 x, ψ y = ψ x := by
    filter_upwards [Metric.ball_mem_nhds x one_pos] with y hy
    have h1 : ψ (y - x) = 1 := hψ.1 _ (by rw [Metric.mem_ball, dist_eq_norm] at hy; exact hy.le)
    calc ψ y = ψ (x + (y - x)) := by rw [add_sub_cancel]
      _ = ψ x * ψ (y - x) := AddChar.map_add_eq_mul ψ _ _
      _ = ψ x := by rw [h1, mul_one]
  exact (continuousAt_const).congr (h.mono fun y hy => hy.symm)
end GlobalTheory.LatVol
