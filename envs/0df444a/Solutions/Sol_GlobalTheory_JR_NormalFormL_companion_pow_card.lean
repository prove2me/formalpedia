-- Prove2me | solution 1 for GlobalTheory.JR.NormalFormL.companion_pow_card
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T18:45:07.574632+00:00
-- url     : https://prove2.me/submissions/af70d038-5cc6-4f60-854c-eaeb0546ee4a

import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_FourierMatch
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_JacquetRallisBorderedMatrixNormalFormInvariants
import Theorems.Thm_GlobalTheory_JR_NormalFormL_companion_mulVec_last
import Theorems.Thm_GlobalTheory_JR_NormalFormL_companion_pow_ev

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
theorem _root_.solution (p : Fin r → k) (hr : 0 < r) :
    companion p ^ r *ᵥ ev r k 0 = - p := by
  obtain ⟨m, rfl⟩ : ∃ m, r = m + 1 := ⟨r - 1, by omega⟩
  rw [pow_succ', ← mulVec_mulVec, companion_pow_ev p m (by omega), companion_mulVec_last p m rfl]
end GlobalTheory.JR.NormalFormL
