-- Prove2me | solution 1 for GlobalTheory.CayleyCapelli.pair_diffOp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T00:49:10.142776+00:00
-- url     : https://prove2.me/submissions/85432c9d-7efd-486f-986d-871d15c0ce2f

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
theorem _root_.solution [CharZero C] (B : σ →₀ ℕ) (P Q : MvPolynomial σ C) :
    pair (monomial B (1 : C)) (diffOp P Q) = pair (monomial B (1 : C) * P) Q := by
  classical
  have hinner : ∀ m : σ →₀ ℕ, coeff B (∑ a ∈ Q.support, if m ≤ a then
      monomial (a - m) (coeff m P * coeff a Q * ((mfact a : C) / (mfact (a - m) : C))) else 0) =
      coeff m P * coeff (B + m) Q * ((mfact (B + m) : C) / (mfact B : C)) := by
    intro m
    rw [coeff_sum, Finset.sum_eq_single (B + m)]
    · rw [if_pos (le_add_self), coeff_monomial, add_tsub_cancel_right, if_pos rfl]
    · intro a _ ha
      split_ifs with hma
      · rw [coeff_monomial, if_neg]
        intro hB
        exact ha (by rw [← hB, tsub_add_cancel_of_le hma])
      · exact coeff_zero B
    · intro hQ
      rw [notMem_support_iff] at hQ
      rw [hQ, if_pos (le_add_self), coeff_monomial, add_tsub_cancel_right, if_pos rfl, mul_zero, zero_mul]
  have hP : monomial B (1 : C) * P = ∑ m ∈ P.support, monomial (B + m) (coeff m P) := by
    conv_lhs => rw [P.as_sum]
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [monomial_mul, one_mul]
  rw [pair_monomial, diffOp, coeff_sum, hP, map_sum, LinearMap.sum_apply, wt_eq, one_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [hinner, pair_monomial, wt_eq]
  have := mfact_ne_zero (C := C) B
  field_simp
end GlobalTheory.CayleyCapelli
