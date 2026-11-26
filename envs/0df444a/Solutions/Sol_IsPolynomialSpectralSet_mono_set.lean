-- Prove2me | solution 1 for IsPolynomialSpectralSet.mono_set
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T14:22:06.06107+00:00
-- url     : https://prove2.me/submissions/3132ae15-2636-4b91-affa-efa0ca9de849

import Definitions.Def_Operator_Crouzeix_ApproximationSupNorm
import Definitions.Def_Operator_Crouzeix_BoundaryMaximum
import Definitions.Def_Operator_Crouzeix_SpectralSetMonotone
import Theorems.Thm_IsKPolynomialSpectralSet_mono_set

set_option autoImplicit false
open Set
open scoped InnerProductSpace Polynomial
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
namespace IsPolynomialSpectralSet
theorem _root_.solution
    {A : E →L[ℂ] E} {X Y : Set ℂ}
    (h : IsPolynomialSpectralSet A X)
    (hXY : X ⊆ Y) (hY : IsCompact Y) :
    IsPolynomialSpectralSet A Y :=
  IsKPolynomialSpectralSet.mono_set h zero_le_one hXY hY
end IsPolynomialSpectralSet
