-- Prove2me | solution 1 for IsKPolynomialSpectralSet.mono
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T15:37:33.167059+00:00
-- url     : https://prove2.me/submissions/2c4cb5a4-32dd-430e-969e-1ea1e9da8498

import Definitions.Def_Operator_Crouzeix_ApproximationSupNorm
import Definitions.Def_Operator_Crouzeix_BoundaryMaximum
import Definitions.Def_Operator_Crouzeix_SpectralSetMonotone
import Theorems.Thm_IsKPolynomialSpectralSet_mono_const
import Theorems.Thm_IsKPolynomialSpectralSet_mono_set

set_option autoImplicit false
open Set
open scoped InnerProductSpace Polynomial
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
namespace IsKPolynomialSpectralSet
theorem _root_.solution
    {A : E →L[ℂ] E} {K L : ℝ} {X Y : Set ℂ}
    (h : IsKPolynomialSpectralSet A K X) (hK : 0 ≤ K)
    (hKL : K ≤ L) (hXY : X ⊆ Y) (hY : IsCompact Y) :
    IsKPolynomialSpectralSet A L Y :=
  (h.mono_set hK hXY hY).mono_const hKL
end IsKPolynomialSpectralSet
