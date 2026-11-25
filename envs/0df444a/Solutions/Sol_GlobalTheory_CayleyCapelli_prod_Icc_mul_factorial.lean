-- Prove2me | solution 1 for GlobalTheory.CayleyCapelli.prod_Icc_mul_factorial
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T00:47:58.403746+00:00
-- url     : https://prove2.me/submissions/872c0e03-a9b6-4b16-8457-6c7ffa966433

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_BiadditiveInSingleVariables
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_WtAddSingle
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_ProdIccMulFactorial

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
theorem _root_.solution (x c : ℕ) :
    (∏ t ∈ Finset.Icc 1 x, (t + c)) * c.factorial = (x + c).factorial := by
  induction x with
  | zero => simp
  | succ x ih =>
    rw [Finset.prod_Icc_succ_top (by omega), mul_right_comm, ih, show x + 1 + c = (x + c) + 1 by omega,
      Nat.factorial_succ, mul_comm]
end GlobalTheory.CayleyCapelli
