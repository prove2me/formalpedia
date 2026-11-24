-- Prove2me | solution 1 for GlobalTheory.T.det_restrictScalars_twoSidedMatrixMul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T21:51:30.512311+00:00
-- url     : https://prove2.me/submissions/df8f6206-3653-4c37-82a3-65c9c1677eb0

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_DetRestrictScalarsTwoSidedMatrixMul
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_UnipVal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_PadicIsNonarchimedeanLocalField
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_DetRestrictScalarsTwoSidedMatrixMulStatement
import Theorems.Thm_GlobalTheory_KSp_det_restrictScalars_twoSidedMul


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Matrix GlobalTheory.KSp GlobalTheory.SplitUnitary
open GlobalTheory.WeilM (UG IsQuad IsHerm ResEtaPow)
open GlobalTheory.SplitWeil (SB nabs)
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (F : Type) [Field F] (E : Type) [Field E] [Algebra F E] [FiniteDimensional F E] (α : Type) [Fintype α] [DecidableEq α] (ν : Type) [Fintype ν] [DecidableEq ν] (u : Matrix α α E) (a : Matrix ν ν E) (T : Matrix α ν E →ₗ[F] Matrix α ν E), (∀ x, T x = u * x * a) → LinearMap.det T = Algebra.norm F u.det ^ Fintype.card ν * Algebra.norm F a.det ^ Fintype.card α := by
  first | exact @GlobalTheory.KSp.det_restrictScalars_twoSidedMul | exact GlobalTheory.KSp.det_restrictScalars_twoSidedMul | (intros; apply GlobalTheory.KSp.det_restrictScalars_twoSidedMul <;> assumption)
end _root_.GlobalTheory.T
