-- Prove2me | solution 1 for GlobalTheory.ProductDegreeCoefficient.natDegree_le_and_coeff_prod_pow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T19:41:24.759429+00:00
-- url     : https://prove2.me/submissions/9476e735-0ac3-49ed-b0ec-e17a3335293e

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_NatDegreeLeAndCoeffProdPow

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
universe u_1 u_2
open GlobalTheory GlobalTheory.ProductDegreeCoefficient
open Polynomial
namespace GlobalTheory.ProductDegreeCoefficient
theorem _root_.solution {B : Type u_1} [CommRing B] {T : Type u_2}
    (s : Finset T) (p : T → Polynomial B) (e : T → ℕ)
    (h : ∀ t : T, (p t).natDegree ≤ 1) :
    (∏ t ∈ s, p t ^ e t).natDegree ≤ ∑ t ∈ s, e t ∧
      (∏ t ∈ s, p t ^ e t).coeff (∑ t ∈ s, e t) = ∏ t ∈ s, (p t).coeff 1 ^ e t := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    obtain ⟨ih1, ih2⟩ := ih
    rw [Finset.prod_insert ha, Finset.sum_insert ha, Finset.prod_insert ha]
    have h1 : (p a ^ e a).natDegree ≤ e a := by
      have := Polynomial.natDegree_pow_le_of_le (e a) (h a)
      simpa using this
    have h2 : (p a ^ e a).coeff (e a) = (p a).coeff 1 ^ e a := by
      have := Polynomial.coeff_pow_of_natDegree_le (m := e a) (h a)
      simpa using this
    refine ⟨Polynomial.natDegree_mul_le_of_le h1 ih1, ?_⟩
    rw [Polynomial.coeff_mul_add_eq_of_natDegree_le h1 ih1, h2, ih2]
end GlobalTheory.ProductDegreeCoefficient
