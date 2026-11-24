-- Prove2me | solution 1 for GlobalTheory.HilbFam.TwistMem.vecMul_scalar
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T17:30:35.221064+00:00
-- url     : https://prove2.me/submissions/0ac54571-ab70-4c47-999f-88ddb02acd32

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_HasLevelStd
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_HasQIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_MemHilbertLatticeTwistIffLift
import Theorems.Thm_GlobalTheory_CMVal_coe_latticeSub
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.CMVal.coe_latticeSub



set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open NumberField UpperHalfPlane GlobalTheory.HilbFam GlobalTheory.QFam
open scoped Classical MatrixGroups nonZeroDivisors
open GlobalTheory GlobalTheory.HilbFam GlobalTheory.HilbFam.TwistMem
variable {F : Type} [Field F] [NumberField F]
namespace GlobalTheory.HilbFam.TwistMem
theorem _root_.solution (N : ℕ) (w : Fin 2 → F) :
    Matrix.vecMul w ((((N : ℤ) • (1 : Matrix (Fin 2) (Fin 2) ℤ))).map (Int.cast : ℤ → F)) = (N : F) • w := by
  ext j
  fin_cases j <;> simp [Matrix.vecMul, dotProduct, Fin.sum_univ_two, Matrix.one_apply, Matrix.natCast_apply, mul_comm]
end GlobalTheory.HilbFam.TwistMem
