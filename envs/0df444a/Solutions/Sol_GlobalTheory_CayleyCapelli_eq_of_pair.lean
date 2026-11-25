-- Prove2me | solution 1 for GlobalTheory.CayleyCapelli.eq_of_pair
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T00:49:08.609801+00:00
-- url     : https://prove2.me/submissions/7a646ff2-b560-42dc-9a65-22128e76cf7a

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_BiadditiveInSingleVariables
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_WtAddSingle
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_ProdIccMulFactorial
import Theorems.Thm_GlobalTheory_CayleyCapelli_wt_eq
import Theorems.Thm_GlobalTheory_CayleyCapelli_mfact_ne_zero
import Theorems.Thm_GlobalTheory_DetPowPairing_pair_monomial


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.L2.FormalSeriesBounds
noncomputable section
open GlobalTheory GlobalTheory.CayleyCapelli
open MvPolynomial Formalism.IncomingBounds ReciprocityTheory.PGsh GlobalTheory.DetPowPairing
variable {σ : Type} {C : Type} [Field C]
namespace GlobalTheory.CayleyCapelli
theorem _root_.solution [CharZero C] {P Q : MvPolynomial σ C}
    (h : ∀ B : σ →₀ ℕ, pair (monomial B (1 : C)) P = pair (monomial B (1 : C)) Q) : P = Q := by
  ext B
  have hB := h B
  rw [pair_monomial, pair_monomial, one_mul, wt_eq] at hB
  exact mul_left_cancel₀ (mfact_ne_zero B) hB
end GlobalTheory.CayleyCapelli
