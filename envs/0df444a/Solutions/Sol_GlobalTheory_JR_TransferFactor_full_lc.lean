-- Prove2me | solution 1 for GlobalTheory.JR.TransferFactor.full_lc
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T18:12:32.34485+00:00
-- url     : https://prove2.me/submissions/995aa5d6-cb8a-498f-adbe-6d67c1faf0d2

import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_FourierMatch
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_JacquetRallisTransferFactorKrylovDet

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.JR Matrix MeasureTheory Filter Topology
open GlobalTheory GlobalTheory.JR GlobalTheory.JR.TransferFactor
variable {k : Type} [CommRing k] {r : ℕ}
namespace GlobalTheory.JR.TransferFactor
theorem _root_.solution (Y : Gl r k) (b : Fin r) : full Y (Fin.last r) (Fin.castSucc b) = Y.2.2.1 b := by
  simp [full, finSumFinEquiv_symm_apply_castSucc, finSumFinEquiv_symm_last]
end GlobalTheory.JR.TransferFactor
