-- Prove2me | solution 1 for MvPolynomial.IsWeightedHomogeneous.eq_monomial_of_unique_weight_tenProofs
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:02.589874+00:00
-- url     : https://prove2.me/submissions/9c85b0f0-dcd0-4af6-ae92-aca04d48970a

import Mathlib
import Definitions.Def_Permanent

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 100000
open MvPolynomial MvPolynomial.IsWeightedHomogeneous
namespace MvPolynomial.IsWeightedHomogeneous
theorem _root_.solution
    {σ R M : Type*} [CommSemiring R] [AddCommMonoid M]
    {w : σ → M} {p : MvPolynomial σ R} {m : M} {d : σ →₀ ℕ}
    (hp : MvPolynomial.IsWeightedHomogeneous w p m)
    (hunique : ∀ b : σ →₀ ℕ, Finsupp.weight w b = m → b = d) :
    p = MvPolynomial.monomial d (MvPolynomial.coeff d p) := by
  classical
  apply MvPolynomial.ext
  intro b
  by_cases h : b = d
  · subst b
    simp
  · have hz : MvPolynomial.coeff b p = 0 := by
      by_contra hb
      exact h (hunique b (hp hb))
    rw [MvPolynomial.coeff_monomial, if_neg (Ne.symm h), hz]
end MvPolynomial.IsWeightedHomogeneous
