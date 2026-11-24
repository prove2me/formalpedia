-- Prove2me | solution 1 for GlobalTheory.ratExtPoint_tmul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T23:30:41.584081+00:00
-- url     : https://prove2.me/submissions/5994607a-0024-4b6e-8130-9683c4dce9fc

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
theorem _root_.solution {B : Type} [CommRing B] (x : B →+* ℂ) (q : ℚ) (b : B) :
    ratExtPoint x (q ⊗ₜ[ℤ] b) = (q : ℂ) * x b := by
  simp [ratExtPoint]
end GlobalTheory
