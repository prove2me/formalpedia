-- Prove2me | solution 1 for GlobalTheory.coeff_aeval_C_mul_X
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T22:31:51.950228+00:00
-- url     : https://prove2.me/submissions/7fdba395-15d0-45f7-9163-5574fd875a06

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_RangeAlgebraMapEqIInfDiscreteValuationSubring
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsCompleteDiscreteValuationRingOfMemClosureC

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped BigOperators
open IsLocalRing
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution {K A J : Type*} [CommRing K] [CommRing A] [Algebra K A] (w : J → A)
    (G : MvPolynomial J K) (d : ℕ) :
    (MvPolynomial.aeval (fun j => Polynomial.C (w j) * Polynomial.X) G).coeff d =
      MvPolynomial.aeval w (MvPolynomial.homogeneousComponent d G) := by
  induction G using MvPolynomial.induction_on' with
  | monomial u a =>
    have h : MvPolynomial.aeval (fun j => Polynomial.C (w j) * Polynomial.X)
        (MvPolynomial.monomial u a) =
        Polynomial.C (MvPolynomial.aeval w (MvPolynomial.monomial u a)) *
          Polynomial.X ^ u.degree := by
      simp only [MvPolynomial.aeval_monomial, Finsupp.prod, mul_pow, Finset.prod_mul_distrib,
        Finset.prod_pow_eq_pow_sum, map_mul, map_prod, map_pow, Polynomial.algebraMap_apply,
        mul_assoc]
      rfl
    rw [h, Polynomial.coeff_C_mul_X_pow, MvPolynomial.homogeneousComponent_of_mem
      (MvPolynomial.isHomogeneous_monomial a (rfl : u.degree = u.degree))]
    split_ifs <;> simp
  | add p q hp hq => simp only [map_add, Polynomial.coeff_add, hp, hq]
end GlobalTheory
