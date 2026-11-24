-- Prove2me | solution 1 for GlobalTheory.JR.transfer_factor_lemma
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T19:24:29.546977+00:00
-- url     : https://prove2.me/submissions/6db5e3c3-740d-4c4d-b11f-7402918b3d50

import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_FourierMatch
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_JacquetRallisTransferFactorKrylovDet
import Theorems.Thm_GlobalTheory_JR_TransferFactor_lastDet_eq
import Theorems.Thm_GlobalTheory_JR_TransferFactor_Cm_act

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.JR Matrix MeasureTheory Filter Topology
namespace GlobalTheory.JR
theorem _root_.solution : ∀ (k : Type) [CommRing k] (r : ℕ), (∀ Y : Gl r k, lastDet Y = (-1) ^ r * (Cm Y).det) ∧ ∀ (g : GL (Fin r) k) (Y : Gl r k), Cm (act g Y) = Cm Y * ((g⁻¹ : GL (Fin r) k) : Matrix (Fin r) (Fin r) k) :=
  fun _ _ _ => ⟨GlobalTheory.JR.TransferFactor.lastDet_eq, GlobalTheory.JR.TransferFactor.Cm_act⟩
end GlobalTheory.JR
