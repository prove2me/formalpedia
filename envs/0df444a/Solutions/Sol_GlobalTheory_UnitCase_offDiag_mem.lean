-- Prove2me | solution 1 for GlobalTheory.UnitCase.offDiag_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T01:29:37.02197+00:00
-- url     : https://prove2.me/submissions/abd9043c-6564-4f9d-83aa-b99e0629be74

import Mathlib
import Definitions.Def_Formalism_DropLevelBounds_Statement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_WtAddSingle
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_LeWeightOfCoeffPow
import Theorems.Thm_GlobalTheory_UnitCase_not_dvd_mfact
import Theorems.Thm_GlobalTheory_UnitCase_coeff_exp_mainTerm
import Theorems.Thm_GlobalTheory_UnitCase_exists_sumElim
import Theorems.Thm_GlobalTheory_UnitCase_coeff_mul_mfact
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
    (hO : ∀ n : ℕ, ¬ l ∣ n → (n : C)⁻¹ ∈ O) (q : MvPolynomial κ ℤ) (t : ℤ) (A B : κ →₀ ℕ)
    (hB : ∀ j, B j < l) (hAB : ∑ j, A j = l * ∑ j, B j) (G : MvPowerSeries (κ ⊕ κ) C)
    (hG0 : MvPowerSeries.coeff 0 G = 1)
    (hG : ∀ m ≤ Finsupp.sumElim A B, MvPowerSeries.coeff m G ∈ O) :
    ((MvPolynomial.coeff A (q ^ l) : ℤ) : C) * t * ((mfact A : C) * mfact B) *
        MvPowerSeries.coeff (Finsupp.sumElim A B) (mvExp (mainTerm l (-(l : C)⁻¹)) * G) -
      ((MvPolynomial.coeff A (q ^ l) : ℤ) : C) * t * ((mfact A : C) * mfact B) *
        MvPowerSeries.coeff (Finsupp.sumElim A B) (mvExp (mainTerm l (-(l : C)⁻¹))) ∈
      mult O l := by
  classical
  have hmem : (Finsupp.sumElim A B, (0 : κ ⊕ κ →₀ ℕ)) ∈
      Finset.HasAntidiagonal.antidiagonal (Finsupp.sumElim A B) := by
    rw [Finset.HasAntidiagonal.mem_antidiagonal, add_zero]
  rw [MvPowerSeries.coeff_mul, ← Finset.add_sum_erase _ _ hmem, hG0, mul_one, mul_add,
    add_sub_cancel_left, Finset.mul_sum]
  refine sum_mem ?_
  rintro ⟨p, r⟩ hpr
  rw [Finset.mem_erase, Finset.HasAntidiagonal.mem_antidiagonal] at hpr
  obtain ⟨hne, hsum⟩ := hpr
  obtain ⟨A₁, β, rfl⟩ := exists_sumElim p
  simp only at hsum ⊢
  rw [coeff_exp_mainTerm]
  split_ifs with h
  swap
  · simp
  subst h
  have h1 : ∀ j, l * β j ≤ A j := fun j => by
    have := DFunLike.congr_fun hsum (Sum.inl j)
    simp at this
    omega
  have h2 : ∀ j, β j ≤ B j := fun j => by
    have := DFunLike.congr_fun hsum (Sum.inr j)
    simp at this
    omega
  have h3 : A ≠ l • β := by
    rintro rfl
    have h4 : ∑ j, β j = ∑ j, B j := by
      apply Nat.eq_of_mul_eq_mul_left hl.pos
      rw [← hAB, Finset.mul_sum]
      simp
    have h5 : β = B := Finsupp.ext fun j =>
      (Finset.sum_eq_sum_iff_of_le fun i _ => h2 i).1 h4 j (Finset.mem_univ j)
    subst h5
    exact hne (by rw [left_eq_add.1 hsum.symm])
  obtain ⟨z, hz⟩ := coeff_mul_mfact hl q A β h1 h3
  have hz' : ((MvPolynomial.coeff A (q ^ l) : ℤ) : C) * (mfact A : C) =
      (-(l : C)) ^ (∑ j, β j) * (l * z) := by exact_mod_cast congrArg (Int.cast : ℤ → C) hz
  refine ⟨(z : C) * t * mfact B * (mfact β : C)⁻¹ * MvPowerSeries.coeff r G, ?_, ?_⟩
  · exact O.mul_mem (O.mul_mem (O.mul_mem (O.mul_mem (intCast_mem O z) (intCast_mem O t))
      (natCast_mem O _)) (hO _ (not_dvd_mfact hl β fun j => (h2 j).trans_lt (hB j))))
      (hG r (hsum ▸ le_add_self))
  · have := neg_pow_mul_inv (C := C) hl (∑ j, β j)
    change (l : C) * _ = _
    linear_combination
      (-(t * mfact B * (mfact β : C)⁻¹ * MvPowerSeries.coeff r G * (-(l : C)⁻¹) ^ (∑ j, β j))) * hz'
        - ((l : C) * z * t * mfact B * (mfact β : C)⁻¹ * MvPowerSeries.coeff r G) * this
end GlobalTheory.UnitCase
