-- Prove2me | solution 1 for GlobalTheory.UnitCase.diag_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T01:08:36.403194+00:00
-- url     : https://prove2.me/submissions/f800e237-8391-4739-895e-32b35aa21417

import Mathlib
import Definitions.Def_Formalism_DropLevelBounds_Statement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_WtAddSingle
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_LeWeightOfCoeffPow
import Theorems.Thm_GlobalTheory_UnitCase_mfact_eq
import Theorems.Thm_GlobalTheory_UnitCase_mfact_smul
import Theorems.Thm_GlobalTheory_UnitCase_coeff_pow_zmod
import Theorems.Thm_GlobalTheory_UnitCase_coeff_exp_mainTerm
import Theorems.Thm_GlobalTheory_UnitCase_neg_pow_mul_inv

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.UnitaryBoundIntegral Formalism.IncomingBounds ReciprocityTheory.PGsh
open scoped BigOperators
noncomputable section
open GlobalTheory GlobalTheory.UnitCase
variable {C : Type} [Field C] {σ κ : Type}
namespace GlobalTheory.UnitCase
theorem _root_.solution [CharZero C] [Fintype κ] {l : ℕ} (hl : l.Prime) (O : Subring C)
    (q : MvPolynomial κ ℤ) (B : κ →₀ ℕ) :
    (∑ A ∈ (q ^ l).support, ((MvPolynomial.coeff A (q ^ l) : ℤ) : C) *
        (MvPolynomial.coeff B q : ℤ) * ((mfact A : C) * mfact B) *
        MvPowerSeries.coeff (Finsupp.sumElim A B) (mvExp (mainTerm l (-(l : C)⁻¹)))) -
      ((MvPolynomial.coeff B q : ℤ) : C) * mfact B * (MvPolynomial.coeff B q : ℤ) ∈ mult O l := by
  classical
  simp only [coeff_exp_mainTerm]
  rw [Finset.sum_eq_single (l • B), if_pos rfl]
  · obtain ⟨w, hw, hw'⟩ := mfact_smul hl B
    have h0 := coeff_pow_zmod hl q (l • B)
    rw [MvPolynomial.coeff_expand_smul _ hl.ne_zero, MvPolynomial.coeff_map, eq_intCast] at h0
    have h1 : ((MvPolynomial.coeff (l • B) (q ^ l) * w - MvPolynomial.coeff B q * mfact B : ℤ) :
        ZMod l) = 0 := by
      push_cast
      rw [h0, hw', sub_self]
    rw [ZMod.intCast_zmod_eq_zero_iff_dvd] at h1
    obtain ⟨z, hz⟩ := h1
    have hz' : ((MvPolynomial.coeff (l • B) (q ^ l) : ℤ) : C) * w -
        ((MvPolynomial.coeff B q : ℤ) : C) * mfact B = l * z := by
      exact_mod_cast congrArg (Int.cast : ℤ → C) hz
    have hw2 : (mfact (l • B) : C) = (-(l : C)) ^ (∑ j, B j) * w := by
      exact_mod_cast congrArg (Int.cast : ℤ → C) hw
    have h3 := neg_pow_mul_inv (C := C) hl (∑ j, B j)
    have h4 : (mfact B : C) * (mfact B : C)⁻¹ = 1 := by
      refine mul_inv_cancel₀ (Nat.cast_ne_zero.2 ?_)
      rw [mfact_eq]
      exact Finset.prod_ne_zero_iff.2 fun j _ => Nat.factorial_ne_zero _
    refine ⟨(z : C) * (MvPolynomial.coeff B q : ℤ),
      O.mul_mem (intCast_mem O _) (intCast_mem O _), ?_⟩
    change (l : C) * _ = _
    rw [hw2]
    generalize ((MvPolynomial.coeff (l • B) (q ^ l) : ℤ) : C) = a at *
    generalize ((MvPolynomial.coeff B q : ℤ) : C) = b at *
    generalize (-(l : C)) ^ (∑ j, B j) = c at *
    generalize (-(l : C)⁻¹) ^ (∑ j, B j) = d at *
    linear_combination (-b) * hz' - (a * b * w) * h3 - (a * b * w * c * d) * h4
  · intro A _ hA
    rw [if_neg hA, mul_zero]
  · intro h
    rw [MvPolynomial.notMem_support_iff.1 h]
    simp
end GlobalTheory.UnitCase
