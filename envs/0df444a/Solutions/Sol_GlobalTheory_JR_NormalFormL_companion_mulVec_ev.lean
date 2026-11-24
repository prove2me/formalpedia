-- Prove2me | solution 1 for GlobalTheory.JR.NormalFormL.companion_mulVec_ev
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T18:08:42.41117+00:00
-- url     : https://prove2.me/submissions/7f59f1fd-5ff8-485d-aed0-8d5cb8f458e2

import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_FourierMatch
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_JacquetRallisBorderedMatrixNormalFormInvariants
import Theorems.Thm_GlobalTheory_JR_NormalFormL_ev_eq_single

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
theorem _root_.solution (p : Fin r → k) (i : ℕ) (hi : i + 1 < r) :
    companion p *ᵥ ev r k i = ev r k (i + 1) := by
  rw [ev_eq_single i (by omega)]
  funext j
  simp only [mulVec_single, companion, of_apply, mul_one, ev]
  have : ¬ (i + 1 = r) := by omega
  simp [this]
end GlobalTheory.JR.NormalFormL
