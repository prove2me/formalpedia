-- Prove2me | solution 1 for IsKPolynomialSpectralSet.affine
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T14:39:22.470363+00:00
-- url     : https://prove2.me/submissions/57a69114-794b-4cbd-bd2c-7a4b98ca4920

import Definitions.Def_Operator_Crouzeix_AffinePolynomial
import Definitions.Def_Operator_Crouzeix_AffineSpectralSet
import Theorems.Thm_spectrum_smul_add_smul_one
import Theorems.Thm_Polynomial_aeval_affineComposition
import Theorems.Thm_polynomialSupNorm_affineComposition_image
attribute [local simp] Polynomial.aeval_affineComposition



set_option autoImplicit false
open Set
open scoped InnerProductSpace Pointwise Polynomial
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
namespace IsKPolynomialSpectralSet
theorem _root_.solution
    {A : E →L[ℂ] E} {K : ℝ} {X : Set ℂ}
    (h : IsKPolynomialSpectralSet A K X)
    {a : ℂ} (ha : a ≠ 0) (b : ℂ) :
    IsKPolynomialSpectralSet (a • A + b • 1) K
      ((fun z => a * z + b) '' X) := by
  constructor
  · rw [spectrum_smul_add_smul_one A ha b]
    exact Set.image_mono h.1
  · intro p
    let q : ℂ[X] := p.affineComposition a b
    have heval : Polynomial.aeval A q =
        Polynomial.aeval (a • A + b • 1) p := by
      exact Polynomial.aeval_affineComposition p a b A
    calc
      ‖Polynomial.aeval (a • A + b • 1) p‖ =
          ‖Polynomial.aeval A q‖ := congrArg norm heval.symm
      _ ≤ K * polynomialSupNorm q X := h.2 q
      _ = K * polynomialSupNorm p ((fun z => a * z + b) '' X) := by
        rw [polynomialSupNorm_affineComposition_image]
end IsKPolynomialSpectralSet
