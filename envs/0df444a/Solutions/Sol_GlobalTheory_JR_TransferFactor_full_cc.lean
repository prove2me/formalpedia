-- Prove2me | solution 1 for GlobalTheory.JR.TransferFactor.full_cc
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T18:12:30.590056+00:00
-- url     : https://prove2.me/submissions/67a21c7b-1748-4fe4-b6eb-5e2ef1510a32

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
theorem _root_.solution (Y : Gl r k) (a b : Fin r) : full Y (Fin.castSucc a) (Fin.castSucc b) = Y.1 a b := by
  simp [full, finSumFinEquiv_symm_apply_castSucc]
end GlobalTheory.JR.TransferFactor
