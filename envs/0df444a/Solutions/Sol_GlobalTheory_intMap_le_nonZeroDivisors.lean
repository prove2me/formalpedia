-- Prove2me | solution 1 for GlobalTheory.intMap_le_nonZeroDivisors
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T23:00:07.038719+00:00
-- url     : https://prove2.me/submissions/be3207b7-d0ab-4f71-8330-b3eeab852630

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
theorem _root_.solution (B : Type) [CommRing B] [IsDomain B] [CharZero B] :
    Algebra.algebraMapSubmonoid B (nonZeroDivisors ℤ) ≤ nonZeroDivisors B := by
  rintro _ ⟨n, hn, rfl⟩
  have h : n ≠ 0 := nonZeroDivisors.ne_zero hn
  exact mem_nonZeroDivisors_of_ne_zero (by simpa using h)
end GlobalTheory
