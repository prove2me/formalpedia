-- Prove2me | solution 1 for GlobalTheory.PolyNorm.monic_ev
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T19:27:11.913044+00:00
-- url     : https://prove2.me/submissions/a1541233-e528-4fee-b760-b45bc962fff4

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_EqOfNormResultantEqStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_EqProdOfMul

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial
open GlobalTheory GlobalTheory.PolyNorm
namespace GlobalTheory.PolyNorm
theorem _root_.solution {m : ℕ} {Φ : MvPolynomial (Fin 2) ℚ} (h : Φ.IsHomogeneous m)
    (h1 : ev Φ (1 : ℚ[X]) = 1) :
    (ev Φ (C X - X : ℚ[X][X])).Monic ∧ (ev Φ (C X - X : ℚ[X][X])).natDegree = m := by
  have hd : ∀ d ∈ Φ.support, d 0 + d 1 = m := fun d hd => by
    have := h.degree_eq_sum_deg_support hd
    rw [this, ← Fin.sum_univ_two (fun i => d i)]
    exact (Finset.sum_subset (Finset.subset_univ _) (by simp)).symm
  have e : ev Φ (C X - X : ℚ[X][X]) =
      ∑ d ∈ Φ.support, monomial (d 0) (Φ.coeff d * (-1) ^ d 1) := by
    unfold ev
    rw [MvPolynomial.aeval_def, MvPolynomial.eval₂_eq']
    refine Finset.sum_congr rfl fun d _ => ?_
    simp [← C_mul_X_pow_eq_monomial, coeff_X, coeff_C]
    ring
  have hle : (ev Φ (C X - X : ℚ[X][X])).natDegree ≤ m := by
    rw [e]
    refine natDegree_sum_le_of_forall_le _ _ fun d hd' => (natDegree_monomial_le _).trans ?_
    have := hd d hd'; omega
  have hc : (ev Φ (C X - X : ℚ[X][X])).coeff m = 1 := by
    rw [e, ← h1, finset_sum_coeff]
    unfold ev
    rw [MvPolynomial.aeval_def, MvPolynomial.eval₂_eq']
    refine Finset.sum_congr rfl fun d hd' => ?_
    have := hd d hd'
    by_cases h0 : d 1 = 0
    · have : d 0 = m := by omega
      simp [coeff_monomial, h0, this]
    · have : d 0 ≠ m := by omega
      simp [coeff_monomial, h0, this, coeff_one]
  exact ⟨monic_of_natDegree_le_of_coeff_eq_one m hle hc,
    natDegree_eq_of_le_of_coeff_ne_zero hle (by simp [hc])⟩
end GlobalTheory.PolyNorm
