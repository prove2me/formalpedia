-- Prove2me | solution 1 for GlobalTheory.DegreeBound.good_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T14:12:51.34955+00:00
-- url     : https://prove2.me/submissions/7004d92b-8572-4f35-8753-047b079341cc

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_TotalDegreeLeOfIntegralAtInfinity
import Theorems.Thm_GlobalTheory_DegreeBound_good_mono

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial
open GlobalTheory GlobalTheory.DegreeBound
variable {K : Type} [Field K] {D : ℕ}
namespace GlobalTheory.DegreeBound
theorem _root_.solution {y : Fin D → K} {j : Fin D} {N N' : ℕ} {b : K} (h : Good y j N b) (hN : N ≤ N') :
    Good y j N' b := by
  obtain ⟨M, rfl⟩ := Nat.exists_eq_add_of_le hN
  exact good_mono h M
end GlobalTheory.DegreeBound
