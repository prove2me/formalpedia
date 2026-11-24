-- Prove2me | solution 1 for GlobalTheory.BorelAlg.coeff_scale
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T12:02:18.267597+00:00
-- url     : https://prove2.me/submissions/b0522bf2-b1b4-4d02-ab4c-974a19952745

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_SectionOfLineBundleOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_IrreducibleDetOfIsRelPrime
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_ExistsIsHomogeneousOfEquivariant

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial
open GlobalTheory GlobalTheory.BorelAlg
namespace GlobalTheory.BorelAlg
theorem _root_.solution {σ L : Type*} [CommRing L] (Q : MvPolynomial σ L) (n : ℕ) :
    (eval₂Hom ((Polynomial.C : MvPolynomial σ L →+* _).comp C)
      (fun i => Polynomial.X * Polynomial.C (X i)) Q).coeff n = homogeneousComponent n Q := by
  classical
  induction Q using MvPolynomial.induction_on' with
  | monomial u r =>
    have : eval₂Hom ((Polynomial.C : MvPolynomial σ L →+* _).comp C)
        (fun i => Polynomial.X * Polynomial.C (X i)) (monomial u r) =
        Polynomial.C (monomial u r) * Polynomial.X ^ u.degree := by
      rw [eval₂Hom_monomial, monomial_eq, Finsupp.prod, Finsupp.prod, Finsupp.degree_apply]
      simp only [mul_pow, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum, map_mul, map_prod,
        map_pow, RingHom.comp_apply]
      ring
    rw [this, Polynomial.coeff_C_mul_X_pow,
      homogeneousComponent_of_mem (isHomogeneous_monomial r rfl)]
  | add p q hp hq => simp only [map_add, Polynomial.coeff_add, hp, hq]
end GlobalTheory.BorelAlg
