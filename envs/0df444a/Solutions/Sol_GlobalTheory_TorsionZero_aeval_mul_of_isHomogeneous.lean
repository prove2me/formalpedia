-- Prove2me | solution 1 for GlobalTheory.TorsionZero.aeval_mul_of_isHomogeneous
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:48:33.440708+00:00
-- url     : https://prove2.me/submissions/371b3472-9fb9-409b-ab34-e7bad8bba719

import Mathlib
import Definitions.Def_ReciprocityTheory_CommutativeAlgebra_PolynomialHeights_HeightAddRingKrullDimQuotientMvPolynomialField
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaFamilyOrigin_NonemptyGradedAlgebraSubGrading

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.TorsionZero
open MvPolynomial
variable {K σ : Type} [Field K]
namespace GlobalTheory.TorsionZero
theorem _root_.solution {S : Type} [CommRing S] [Algebra K S] (a : σ → S) (w : S)
    {G : MvPolynomial σ K} {n : ℕ} (hG : G.IsHomogeneous n) :
    aeval (fun j => a j * w) G = aeval a G * w ^ n := by
  conv_lhs => rw [G.as_sum]
  conv_rhs => rw [G.as_sum]
  rw [map_sum, map_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun m hm => ?_
  have hmn : m.degree = n := by
    by_contra hne
    exact (mem_support_iff.mp hm) (hG.coeff_eq_zero hne)
  rw [aeval_monomial, aeval_monomial, ← hmn]
  simp only [Finsupp.prod, mul_pow, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum,
    mul_assoc, Finsupp.degree_apply]
end GlobalTheory.TorsionZero
