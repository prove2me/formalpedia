-- Prove2me | solution 1 for GlobalTheory.JR.LinDesc.Swap.continuous_eta_det
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T18:36:30.138174+00:00
-- url     : https://prove2.me/submissions/90d0a4e2-cf3c-4fc0-aa2f-d95b7944ba9a

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_LeftMulTau
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_JacquetRallisInvKRegularIffIsUnit
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_LinearDescentPartialFourierEqFourierDescent
import Theorems.Thm_GlobalTheory_JR_LinDesc_Swap_eta_eventually

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
open GlobalTheory GlobalTheory.JR GlobalTheory.JR.LinDesc GlobalTheory.JR.LinDesc.Swap
namespace GlobalTheory.JR.LinDesc.Swap
theorem _root_.solution {F : Type} [NontriviallyNormedField F] [IsUltrametricDist F] (r : ℕ) :
    Continuous (fun g : GL (Fin r) F => eta ((g : Matrix (Fin r) (Fin r) F).det)) := by
  rw [continuous_iff_continuousAt]
  intro g
  have hd : ((g : Matrix (Fin r) (Fin r) F).det) ≠ 0 := (Matrix.isUnits_det_units g).ne_zero
  have hc : Continuous (fun g : GL (Fin r) F => (g : Matrix (Fin r) (Fin r) F).det) :=
    Units.continuous_val.matrix_det
  exact ContinuousAt.comp (f := fun g : GL (Fin r) F => (g : Matrix (Fin r) (Fin r) F).det)
    (continuousAt_const.congr (eta_eventually hd)) hc.continuousAt
end GlobalTheory.JR.LinDesc.Swap
