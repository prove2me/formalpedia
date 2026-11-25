-- Prove2me | solution 1 for GlobalTheory.CayleyCapelli.pair_pow_self
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T17:16:45.073881+00:00
-- url     : https://prove2.me/submissions/1fb18261-0569-4878-bf74-523a50c3635f

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_BiadditiveInSingleVariables
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_WtAddSingle
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_ProdIccMulFactorial
import Theorems.Thm_GlobalTheory_CayleyCapelli_wt_eq
import Theorems.Thm_GlobalTheory_CayleyCapelli_pair_detL_pow
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
theorem _root_.solution (n x : ℕ) :
    pair (detL C n ^ x) (detL C n ^ x) =
      ((∏ t ∈ Finset.Icc 1 x, ∏ c ∈ Finset.range n, (t + c) : ℕ) : C) := by
  induction x with
  | zero =>
    rw [pow_zero, ← MvPolynomial.C_1, MvPolynomial.C_apply, pair_monomial, wt_eq]
    simp [mfact]
  | succ x ih =>
    have h := pair_detL_pow n x (detL C n ^ x)
    rw [← pow_succ] at h
    rw [h, ih, Finset.prod_Icc_succ_top (by omega), Nat.cast_mul, mul_comm]
end GlobalTheory.CayleyCapelli
