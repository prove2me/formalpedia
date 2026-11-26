-- Prove2me | solution 1 for IsKPolynomialSpectralSet.mono_const
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T15:06:04.323017+00:00
-- url     : https://prove2.me/submissions/ff94e5ab-62e1-4c4c-840b-b3fa491fd11c

import Definitions.Def_Operator_Crouzeix_ApproximationSupNorm
import Definitions.Def_Operator_Crouzeix_BoundaryMaximum
import Definitions.Def_Operator_Crouzeix_SpectralSetMonotone
import Theorems.Thm_polynomialSupNorm_nonneg


set_option autoImplicit false
open Set
open scoped InnerProductSpace Polynomial
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
namespace IsKPolynomialSpectralSet
theorem _root_.solution
    {A : E →L[ℂ] E} {K L : ℝ} {X : Set ℂ}
    (h : IsKPolynomialSpectralSet A K X) (hKL : K ≤ L) :
    IsKPolynomialSpectralSet A L X := by
  refine ⟨h.1, fun p => (h.2 p).trans ?_⟩
  exact mul_le_mul_of_nonneg_right hKL (polynomialSupNorm_nonneg p X)
end IsKPolynomialSpectralSet
