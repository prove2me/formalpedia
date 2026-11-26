-- Prove2me | solution 1 for IsPolynomialSpectralSet.affine
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T15:27:42.511432+00:00
-- url     : https://prove2.me/submissions/6020eefa-9707-4b32-bfa3-47e1a444832d

import Definitions.Def_Operator_Crouzeix_AffinePolynomial
import Definitions.Def_Operator_Crouzeix_AffineSpectralSet
import Theorems.Thm_IsKPolynomialSpectralSet_affine

set_option autoImplicit false
open Set
open scoped InnerProductSpace Pointwise Polynomial
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
namespace IsPolynomialSpectralSet
theorem _root_.solution
    {A : E →L[ℂ] E} {X : Set ℂ}
    (h : IsPolynomialSpectralSet A X)
    {a : ℂ} (ha : a ≠ 0) (b : ℂ) :
    IsPolynomialSpectralSet (a • A + b • 1)
      ((fun z => a * z + b) '' X) :=
  IsKPolynomialSpectralSet.affine h ha b
end IsPolynomialSpectralSet
