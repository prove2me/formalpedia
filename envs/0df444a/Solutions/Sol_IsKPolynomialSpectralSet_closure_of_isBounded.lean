-- Prove2me | solution 1 for IsKPolynomialSpectralSet.closure_of_isBounded
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T15:06:54.969752+00:00
-- url     : https://prove2.me/submissions/8f5cddca-65db-486d-a34c-82b220b63439

import Definitions.Def_Operator_Crouzeix_ApproximationSupNorm
import Definitions.Def_Operator_Crouzeix_BoundaryMaximum
import Definitions.Def_Operator_Crouzeix_SpectralSetMonotone
import Theorems.Thm_polynomialSupNorm_closure_of_isBounded


set_option autoImplicit false
open Set
open scoped InnerProductSpace Polynomial
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
namespace IsKPolynomialSpectralSet
theorem _root_.solution
    {A : E →L[ℂ] E} {K : ℝ} {X : Set ℂ}
    (h : IsKPolynomialSpectralSet A K X)
    (hX : Bornology.IsBounded X) :
    IsKPolynomialSpectralSet A K (closure X) := by
  constructor
  · exact h.1.trans subset_closure
  · intro p
    rw [polynomialSupNorm_closure_of_isBounded p hX]
    exact h.2 p
end IsKPolynomialSpectralSet
