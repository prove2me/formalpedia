-- Prove2me | solution 1 for GlobalTheory.PlancherelZero.continuous_char
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T19:27:09.549827+00:00
-- url     : https://prove2.me/submissions/2524d5ab-25a2-4126-99f1-88d5c02875e6

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_IsTestRep
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_EtaleHermitianPairStructureFactsStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_SelfDualIffLatticeVolumeAndPlancherelStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_SelfDualMeasureExistsUniqueFourierInversionStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_EqZeroOfTruncatedFourierTendstoZeroEtale

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.JR Matrix MeasureTheory Filter Topology
noncomputable section
open GlobalTheory GlobalTheory.PlancherelZero
variable {F E : Type} [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E]
namespace GlobalTheory.PlancherelZero
theorem _root_.solution (ψ : AddChar F ℂ) (hψ : IsStdChar ψ) : Continuous ψ := by
  rw [continuous_iff_continuousAt]
  intro x
  refine (continuousAt_const (y := ψ x)).congr ?_
  filter_upwards [Metric.closedBall_mem_nhds x one_pos] with z hz
  have h1 : ψ (z - x) = 1 := hψ.1 _ (by simpa [dist_eq_norm] using hz)
  calc ψ x = ψ x * ψ (z - x) := by rw [h1, mul_one]
    _ = ψ z := by rw [← AddChar.map_add_eq_mul]; congr 1; abel
end GlobalTheory.PlancherelZero
