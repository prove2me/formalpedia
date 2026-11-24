-- Prove2me | solution 1 for GlobalTheory.Capelli.casimir_colOp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T22:33:58.304061+00:00
-- url     : https://prove2.me/submissions/98a48a02-3497-4467-8528-a79412e2ee8a

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_CommuteRowOpRightMixedOp
import Theorems.Thm_GlobalTheory_Capelli_polar_apply
import Theorems.Thm_GlobalTheory_Capelli_colOp_apply
import Theorems.Thm_GlobalTheory_Capelli_rowOp_apply
import Theorems.Thm_GlobalTheory_capelli_casimir
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.Capelli.polar_apply

set_option autoImplicit false
open MvPolynomial
open GlobalTheory
open Capelli
open GlobalTheory.Capelli
variable {K σ : Type*} [CommRing K] {p q n : ℕ}
namespace GlobalTheory.Capelli
theorem _root_.solution (z : Fin p × Fin n → σ) (hz : Function.Injective z)
    (P : MvPolynomial σ K) :
    ∑ k, ∑ l, colOp K z k l (colOp K z l k P) =
      ∑ a, ∑ b, rowOp K z a b (rowOp K z b a P) +
        ((n : K) - (p : K)) • ∑ a, rowOp K z a a P := by
  classical
  simp only [colOp_apply, rowOp_apply]
  rw [capelli_casimir z hz P, Fintype.sum_prod_type]
end GlobalTheory.Capelli
