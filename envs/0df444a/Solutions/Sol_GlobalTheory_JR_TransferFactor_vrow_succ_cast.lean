-- Prove2me | solution 1 for GlobalTheory.JR.TransferFactor.vrow_succ_cast
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T18:32:33.57303+00:00
-- url     : https://prove2.me/submissions/8574bc13-fc53-4eee-af3f-4ea7befe211f

import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_FourierMatch
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_JacquetRallisTransferFactorKrylovDet
import Theorems.Thm_GlobalTheory_JR_TransferFactor_full_cc
import Theorems.Thm_GlobalTheory_JR_TransferFactor_full_lc

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
theorem _root_.solution (Y : Gl r k) (i : ℕ) (j : Fin r) :
    vrow Y (i + 1) (Fin.castSucc j) =
      ((fun l => vrow Y i (Fin.castSucc l)) ᵥ* Y.1) j + vrow Y i (Fin.last r) * Y.2.2.1 j := by
  simp only [vrow, pow_succ, ← Matrix.vecMul_vecMul]
  rw [Matrix.vecMul, dotProduct, Fin.sum_univ_castSucc]
  simp only [full_cc, full_lc]
  rfl
end GlobalTheory.JR.TransferFactor
