-- Prove2me | solution 1 for GlobalTheory.NormEq.mul_ofAdd_one_le_of_lt_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T19:14:44.732105+00:00
-- url     : https://prove2.me/submissions/a87169b7-41ba-445a-94e4-b814c560d0fc

import Mathlib
import Definitions.Def_Formalism_SatakeDualWeyl_StatementF
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_AevalRootEqZeroIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsUnitOneAddPiOMul
import Definitions.Def_GroundTheory_LocalFields_FilteredSurj
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsMulInvolEqOfFixed
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsReducedAdjoinRootOfSeparable
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_NormApproximationFirstLevel

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial Matrix Formalism.UG
open GlobalTheory GlobalTheory.NormEq
variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))]
namespace GlobalTheory.NormEq
theorem _root_.solution {a : WithZero (Multiplicative ℤ)} (ha : a < 1) :
    a * ((Multiplicative.ofAdd (1 : ℤ) : Multiplicative ℤ) : WithZero (Multiplicative ℤ)) ≤ 1 := by
  induction a using WithZero.recZeroCoe with
  | zero => simp
  | coe m =>
    rw [← WithZero.coe_one, WithZero.coe_lt_coe] at ha
    rw [← WithZero.coe_mul, ← WithZero.coe_one, WithZero.coe_le_coe]
    rw [← ofAdd_toAdd m, ← ofAdd_add, ← ofAdd_zero, Multiplicative.ofAdd_le]
    rw [← ofAdd_toAdd m, ← ofAdd_zero, Multiplicative.ofAdd_lt] at ha
    omega
end GlobalTheory.NormEq
