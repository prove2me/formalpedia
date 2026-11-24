-- Prove2me | solution 1 for GlobalTheory.Cyc.norm_primitiveRoot_sub_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T14:29:02.73849+00:00
-- url     : https://prove2.me/submissions/8f745f46-9abf-4a48-8a8e-7f7e99f722fe

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_LevelLetterCocycles_DataNLoc
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_HTBasis
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_NormPrimitiveRootPrimePowSubOnePadicComplex
import Theorems.Thm_GlobalTheory_Cyc_norm_natCast_prime_padicComplex
import Theorems.Thm_GlobalTheory_Cyc_norm_sub_one_le_of_isPrimitiveRoot

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.Cyc
open GlobalTheory GlobalTheory.Cyc
namespace GlobalTheory.Cyc
namespace _root_.GlobalTheory.Cyc
theorem _root_.solution (l : ℕ) [hl : Fact l.Prime] (j : ℕ)
    (hj : 1 ≤ j) (ζ : PadicComplex l) (hζ : IsPrimitiveRoot ζ (l ^ j)) :
    ‖ζ - 1‖ = (l : ℝ) ^ (-(1 : ℝ) / ((l : ℝ) ^ (j - 1) * ((l : ℝ) - 1))) := by
  have hpos : 0 < l ^ j := pow_pos hl.out.pos j
  have hall : ∀ μ ∈ primitiveRoots (l ^ j) (PadicComplex l), ‖1 - μ‖ = ‖ζ - 1‖ := by
    intro μ hμ
    rw [mem_primitiveRoots hpos] at hμ
    rw [norm_sub_rev]
    exact le_antisymm
      (_root_.GlobalTheory.Cyc.norm_sub_one_le_of_isPrimitiveRoot hpos.ne' hζ hμ.pow_eq_one)
      (_root_.GlobalTheory.Cyc.norm_sub_one_le_of_isPrimitiveRoot hpos.ne' hμ hζ.pow_eq_one)
  have heval :=
    congrArg (Polynomial.eval 1) (Polynomial.cyclotomic_eq_prod_X_sub_primitiveRoots hζ)
  obtain ⟨k, rfl⟩ : ∃ k, j = k + 1 := ⟨j - 1, by omega⟩
  rw [Polynomial.eval_one_cyclotomic_prime_pow, Polynomial.eval_prod] at heval
  simp only [Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C] at heval
  have hprod := congrArg norm heval
  rw [_root_.GlobalTheory.Cyc.norm_natCast_prime_padicComplex, norm_prod, Finset.prod_congr rfl hall, Finset.prod_const,
    hζ.card_primitiveRoots, Nat.totient_prime_pow hl.out (Nat.succ_pos k)] at hprod
  simp only [Nat.succ_sub_one, Nat.add_sub_cancel] at hprod ⊢
  have hN : l ^ k * (l - 1) ≠ 0 :=
    Nat.mul_ne_zero (pow_ne_zero _ hl.out.ne_zero) (Nat.sub_ne_zero_of_lt hl.out.one_lt)
  have hcast : ((l ^ k * (l - 1) : ℕ) : ℝ) = (l : ℝ) ^ k * ((l : ℝ) - 1) := by
    push_cast [Nat.cast_sub hl.out.one_le]
    ring
  rw [← Real.pow_rpow_inv_natCast (norm_nonneg (ζ - 1)) hN, ← hprod, hcast,
    Real.inv_rpow (Nat.cast_nonneg l), ← Real.rpow_neg (Nat.cast_nonneg l), neg_div, one_div]
end _root_.GlobalTheory.Cyc
end GlobalTheory.Cyc
