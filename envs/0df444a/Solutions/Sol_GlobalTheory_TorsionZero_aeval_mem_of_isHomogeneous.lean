-- Prove2me | solution 1 for GlobalTheory.TorsionZero.aeval_mem_of_isHomogeneous
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:55:53.873675+00:00
-- url     : https://prove2.me/submissions/02df80cb-2e6d-4c26-8e09-90706e5ce589

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
theorem _root_.solution {R : Type} [CommRing R] [Algebra K R] (𝒜 : ℕ → Submodule K R)
    [SetLike.GradedMonoid 𝒜] {N : ℕ} {x : σ → R} (hx : ∀ j, x j ∈ 𝒜 N)
    {G : MvPolynomial σ K} {n : ℕ} (hG : G.IsHomogeneous n) : aeval x G ∈ 𝒜 (N * n) := by
  rw [G.as_sum, map_sum]
  refine Submodule.sum_mem _ fun m hm => ?_
  have hmn : m.degree = n := by
    by_contra hne
    exact (mem_support_iff.mp hm) (hG.coeff_eq_zero hne)
  rw [aeval_monomial, ← Algebra.smul_def]
  refine Submodule.smul_mem _ _ ?_
  have h := SetLike.prod_pow_mem_graded 𝒜 (F := m.support) (fun _ => N) x m (fun j _ => hx j)
  rw [← hmn, Finsupp.degree_apply, Finset.mul_sum]
  simpa [Finsupp.prod, mul_comm] using h
end GlobalTheory.TorsionZero
