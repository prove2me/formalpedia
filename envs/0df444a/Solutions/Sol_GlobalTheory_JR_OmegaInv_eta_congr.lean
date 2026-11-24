-- Prove2me | solution 1 for GlobalTheory.JR.OmegaInv.eta_congr
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T18:11:21.120216+00:00
-- url     : https://prove2.me/submissions/7f7bec5e-02ca-4bf2-9f25-64a06f478b3d

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_NormMulApplyLeOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_JacquetRallisTransferFactorKrylovDet
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_JacquetRallisTransferFactorGlBorderedConjugation

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
open GlobalTheory GlobalTheory.JR GlobalTheory.JR.OmegaInv
namespace GlobalTheory.JR.OmegaInv
theorem _root_.solution {F : Type} [NormedField F] {x y : F} (h : ‖x‖ = ‖y‖) : eta x = eta y := by
  have hiff : (∃ z : F, ‖x‖ = ‖z‖ ^ 2) ↔ (∃ z : F, ‖y‖ = ‖z‖ ^ 2) := by rw [h]
  unfold eta
  split_ifs <;> tauto
end GlobalTheory.JR.OmegaInv
