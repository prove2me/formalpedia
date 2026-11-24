-- Prove2me | solution 1 for GlobalTheory.JR.NormalFormL.companion_pow_ev
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T18:28:27.341731+00:00
-- url     : https://prove2.me/submissions/5d94195c-5635-4a86-a56b-a5dcb4bcd869

import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_FourierMatch
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_JacquetRallisBorderedMatrixNormalFormInvariants
import Theorems.Thm_GlobalTheory_JR_NormalFormL_companion_mulVec_ev

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.JR Matrix MeasureTheory Filter Topology
open GlobalTheory GlobalTheory.JR GlobalTheory.JR.NormalFormL
variable {k : Type} [Field k] {r : ℕ}
namespace GlobalTheory.JR.NormalFormL
theorem _root_.solution (p : Fin r → k) (i : ℕ) (hi : i < r) :
    companion p ^ i *ᵥ ev r k 0 = ev r k i := by
  induction i with
  | zero => simp
  | succ i ih => rw [pow_succ', ← mulVec_mulVec, ih (by omega), companion_mulVec_ev p i hi]
end GlobalTheory.JR.NormalFormL
