-- Prove2me | solution 1 for GlobalTheory.mem_smul_of_isHomogeneous_of_coeff_mem
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T13:17:04.159831+00:00
-- url     : https://prove2.me/submissions/70397d59-d55f-4bea-908c-4a5dd84d642a

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsRingKrullDimQuotientMvPolynomialEqNat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsFormsAlgebraicIndependentSmulSubSumMem

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory
open MvPolynomial
attribute [local instance] MvPolynomial.gradedAlgebra
variable {σ ι R : Type*} [CommRing R]
namespace GlobalTheory
theorem _root_.solution {J : Ideal R} {Q : Submodule R (MvPolynomial σ R)}
    {n : ℕ} (hQ : ∀ m : σ →₀ ℕ, m.degree = n → monomial m (1 : R) ∈ Q) {p : MvPolynomial σ R}
    (hp : p.IsHomogeneous n) (hJ : ∀ m, p.coeff m ∈ J) : p ∈ J • Q := by
  rw [p.as_sum]
  refine Submodule.sum_mem _ fun m hm => ?_
  have h1 : monomial m (coeff m p) = coeff m p • monomial m (1 : R) := by
    rw [smul_monomial, smul_eq_mul, mul_one]
  rw [h1]
  refine Submodule.smul_mem_smul (hJ m) (hQ m ?_)
  by_contra hne
  exact (mem_support_iff.mp hm) (hp.coeff_eq_zero hne)
end GlobalTheory
