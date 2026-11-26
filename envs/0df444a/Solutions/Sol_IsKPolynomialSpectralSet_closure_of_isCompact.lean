-- Prove2me | solution 1 for IsKPolynomialSpectralSet.closure_of_isCompact
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T15:37:33.816039+00:00
-- url     : https://prove2.me/submissions/ddf2ca7e-161f-4548-8a26-43d69cd82de0

import Definitions.Def_Operator_Crouzeix_ApproximationSupNorm
import Definitions.Def_Operator_Crouzeix_BoundaryMaximum
import Definitions.Def_Operator_Crouzeix_SpectralSetMonotone
import Theorems.Thm_IsKPolynomialSpectralSet_closure_of_isBounded

set_option autoImplicit false
open Set
open scoped InnerProductSpace Polynomial
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
namespace IsKPolynomialSpectralSet
theorem _root_.solution
    {A : E →L[ℂ] E} {K : ℝ} {X : Set ℂ}
    (h : IsKPolynomialSpectralSet A K X) (hX : IsCompact X) :
    IsKPolynomialSpectralSet A K (closure X) :=
  h.closure_of_isBounded hX.isBounded
end IsKPolynomialSpectralSet
