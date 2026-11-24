-- Prove2me | solution 1 for GlobalTheory.HermFrame.incl_mul_orthProj_add
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T17:27:52.622525+00:00
-- url     : https://prove2.me/submissions/e956afc0-9794-4a41-a1e7-1e9cc6878a20

import Mathlib
import Definitions.Def_ReciprocityTheory_AnalyticForms_MaIntEmpty
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_EventuallyDifferentiableAtOfContDiffAtTwo
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_LeTwoMulOfForallScale
import Theorems.Thm_GlobalTheory_HermFrame_opNorm_zero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.HermFrame.opNorm_zero

set_option autoImplicit false
open Matrix Complex ComplexConjugate
open scoped ComplexOrder MatrixOrder
noncomputable section
open GlobalTheory GlobalTheory.HermFrame
variable {m n l : Type*} [Fintype m] [Fintype n] [Fintype l]
variable [DecidableEq m] [DecidableEq l]
variable {H : Matrix (m ⊕ l) (m ⊕ l) ℂ}
namespace GlobalTheory.HermFrame
theorem _root_.solution (H : Matrix (m ⊕ l) (m ⊕ l) ℂ) :
    incl m l * orthProj H + orthLift H * quotMap m l = 1 := by
  rw [quotMap, orthLift, incl, orthProj, fromRows_mul_fromCols, fromRows_mul_fromCols,
    fromBlocks_add, ← fromBlocks_one]
  simp
end GlobalTheory.HermFrame
