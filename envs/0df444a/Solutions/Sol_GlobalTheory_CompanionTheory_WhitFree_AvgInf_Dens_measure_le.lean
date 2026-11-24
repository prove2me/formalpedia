-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.WhitFree.AvgInf.Dens.measure_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T15:27:00.445853+00:00
-- url     : https://prove2.me/submissions/e0fa482d-d383-48cc-9144-70ca11b6fbb8

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_SecondCountableHermC
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_DensityOfFourierPairingIntegrable
import Theorems.Thm_GlobalTheory_CompanionTheory_WhitFree_AvgInf_Dens_compact_le

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Real Complex SchwartzMap FourierTransform
open scoped ENNReal NNReal RealInnerProductSpace Topology ContDiff Manifold
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.WhitFree GlobalTheory.CompanionTheory.WhitFree.AvgInf GlobalTheory.CompanionTheory.WhitFree.AvgInf.Dens
variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]
namespace GlobalTheory.CompanionTheory.WhitFree.AvgInf.Dens
theorem _root_.solution (m : Measure V) [IsFiniteMeasure m] (hi : Integrable (chf m)) {Y : Set V}
    (hY : MeasurableSet Y) : m Y ≤ ENNReal.ofReal (∫ ξ, ‖chf m ξ‖) * volume Y := by
  have hC : ENNReal.ofReal (∫ ξ, ‖chf m ξ‖) ≠ ⊤ := ENNReal.ofReal_ne_top
  haveI : (ENNReal.ofReal (∫ ξ, ‖chf m ξ‖) • (volume : Measure V)).OuterRegular :=
    Measure.OuterRegular.smul _ hC
  rw [hY.measure_eq_iSup_isCompact]
  refine iSup_le fun K => iSup_le fun hKY => iSup_le fun hK => ?_
  have : ENNReal.ofReal (∫ ξ, ‖chf m ξ‖) * volume Y = (ENNReal.ofReal (∫ ξ, ‖chf m ξ‖) • (volume : Measure V)) Y := by
    simp
  rw [this, Y.measure_eq_iInf_isOpen]
  refine le_iInf fun U => le_iInf fun hYU => le_iInf fun hU => ?_
  simpa using compact_le m hi hK hU (hKY.trans hYU)
end GlobalTheory.CompanionTheory.WhitFree.AvgInf.Dens
