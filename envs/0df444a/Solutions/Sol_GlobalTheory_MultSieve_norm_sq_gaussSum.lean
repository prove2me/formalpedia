-- Prove2me | solution 1 for GlobalTheory.MultSieve.norm_sq_gaussSum
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T18:59:28.043823+00:00
-- url     : https://prove2.me/submissions/2060be4c-7f51-4a4f-9176-c93713685765

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_SumIntervalIntegralLeOfSpaced
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_GaussSumMulGaussSumInvOfIsPrimitive
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_MultiplicativeLargeSieve
import Theorems.Thm_GlobalTheory_GaussInt_gaussSum_mul_gaussSum_inv_of_isPrimitive


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex DirichletCharacter ArithmeticFunction MeasureTheory
open GlobalTheory GlobalTheory.MultSieve
namespace GlobalTheory.MultSieve
theorem _root_.solution {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q} (hχ : χ.IsPrimitive) :
    ‖gaussSum χ (ZMod.stdAddChar (N := q))‖ ^ 2 = q := by
  have h := GlobalTheory.GaussInt.gaussSum_mul_gaussSum_inv_of_isPrimitive hχ (ZMod.isPrimitive_stdAddChar q)
  rw [← star_gaussSum_eq] at h
  apply Complex.ofReal_injective
  rw [Complex.ofReal_pow, ← Complex.mul_conj']
  simpa using h
end GlobalTheory.MultSieve
