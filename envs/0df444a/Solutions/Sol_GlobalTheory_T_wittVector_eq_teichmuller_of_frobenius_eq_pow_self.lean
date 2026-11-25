-- Prove2me | solution 1 for GlobalTheory.T.wittVector_eq_teichmuller_of_frobenius_eq_pow_self
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T23:58:35.893246+00:00
-- url     : https://prove2.me/submissions/48a7bc5c-431d-4a35-b3b9-6b65e4be03cf

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_WittVectorEqTeichmullerOfFrobeniusEqPowSelf
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_WittVectorEqTeichmullerOfFrobeniusEqPowSelfStatement
import Theorems.Thm_GlobalTheory_wittVector_eq_teichmuller_of_frobenius_eq_pow


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped NNReal
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (l : ℕ) [Fact l.Prime] (O : Type) [CommRing O] [CharP O l] [PerfectRing O l] (y : WittVector l O), WittVector.frobenius y = y ^ l → y = WittVector.teichmuller l (y.coeff 0) := by
  first | exact @GlobalTheory.wittVector_eq_teichmuller_of_frobenius_eq_pow | exact GlobalTheory.wittVector_eq_teichmuller_of_frobenius_eq_pow | (intros; apply GlobalTheory.wittVector_eq_teichmuller_of_frobenius_eq_pow <;> assumption)
end _root_.GlobalTheory.T
