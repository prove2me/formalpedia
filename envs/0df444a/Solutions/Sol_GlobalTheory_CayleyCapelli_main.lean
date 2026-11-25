-- Prove2me | solution 1 for GlobalTheory.CayleyCapelli.main
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T17:31:25.656556+00:00
-- url     : https://prove2.me/submissions/9e435cf7-210f-4d9b-87b8-40a5f297db87

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_BiadditiveInSingleVariables
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_WtAddSingle
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_ProdIccMulFactorial
import Theorems.Thm_GlobalTheory_CayleyCapelli_jetAt0_coe
import Theorems.Thm_GlobalTheory_CayleyCapelli_cayleyId
import Theorems.Thm_GlobalTheory_CayleyCapelli_pair_pow_self
import Theorems.Thm_GlobalTheory_CayleyCapelli_prod_eq_capNat

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
theorem _root_.solution : F1 ∧ CapacityFactorialProduct := by
  refine ⟨cayleyId, ?_⟩
  intro K _ _ n x
  refine ⟨by rw [jetAt0_coe, pair_pow_self], prod_eq_capNat n x,
    fun c => Nat.factorial_dvd_factorial (by omega), ?_⟩
  rw [← prod_eq_capNat]
  refine Finset.prod_ne_zero_iff.2 fun t ht => Finset.prod_ne_zero_iff.2 fun c _ => ?_
  rw [Finset.mem_Icc] at ht
  omega
end GlobalTheory.CayleyCapelli
