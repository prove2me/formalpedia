-- Prove2me | solution 1 for GlobalTheory.isLocalization_rat_tensor
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T23:04:58.491425+00:00
-- url     : https://prove2.me/submissions/7e515926-3c8d-4519-95eb-a8a8adefac3b

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_LocalMaximumPrincipleWeightFiniteMvPolynomialStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_LocalMaxPrincipleWeightedFiniteTypeInt

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped TensorProduct
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution (B : Type) [CommRing B] :
    letI := Algebra.TensorProduct.rightAlgebra (R := ℤ) (A := ℚ) (B := B)
    IsLocalization (Algebra.algebraMapSubmonoid B (nonZeroDivisors ℤ)) (ℚ ⊗[ℤ] B) :=
  IsLocalization.tensorRight ℚ (nonZeroDivisors ℤ)
end GlobalTheory
