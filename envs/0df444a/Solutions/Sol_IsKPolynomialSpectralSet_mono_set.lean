-- Prove2me | solution 1 for IsKPolynomialSpectralSet.mono_set
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:26:00.440934+00:00
-- url     : https://prove2.me/submissions/9f43043b-0d81-498f-8d80-34978fab0891

import Definitions.Def_Operator_Crouzeix_ApproximationSupNorm
import Definitions.Def_Operator_Crouzeix_BoundaryMaximum
import Definitions.Def_Operator_Crouzeix_SpectralSetMonotone
import Theorems.Thm_polynomialSupNorm_mono_of_isCompact


set_option autoImplicit false
open Set
open scoped InnerProductSpace Polynomial
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
namespace IsKPolynomialSpectralSet
theorem _root_.solution
    {A : E →L[ℂ] E} {K : ℝ} {X Y : Set ℂ}
    (h : IsKPolynomialSpectralSet A K X) (hK : 0 ≤ K)
    (hXY : X ⊆ Y) (hY : IsCompact Y) :
    IsKPolynomialSpectralSet A K Y := by
  constructor
  · exact h.1.trans hXY
  · intro p
    exact (h.2 p).trans (mul_le_mul_of_nonneg_left
      (polynomialSupNorm_mono_of_isCompact p hXY hY) hK)
end IsKPolynomialSpectralSet
