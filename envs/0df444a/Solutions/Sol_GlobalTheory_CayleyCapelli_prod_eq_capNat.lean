-- Prove2me | solution 1 for GlobalTheory.CayleyCapelli.prod_eq_capNat
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T00:58:36.230912+00:00
-- url     : https://prove2.me/submissions/65038ae2-ee7f-46e2-bbfd-9a44b1d70c13

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_BiadditiveInSingleVariables
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_WtAddSingle
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_ProdIccMulFactorial
import Theorems.Thm_GlobalTheory_CayleyCapelli_prod_Icc_mul_factorial

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
    (∏ t ∈ Finset.Icc 1 x, ∏ c ∈ Finset.range n, (t + c)) = capNat n x := by
  rw [capNat, Finset.prod_comm]
  refine Finset.prod_congr rfl fun a _ => ?_
  exact (Nat.div_eq_of_eq_mul_left (Nat.factorial_pos a) (prod_Icc_mul_factorial x a).symm).symm
end GlobalTheory.CayleyCapelli
