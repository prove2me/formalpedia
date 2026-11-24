-- Prove2me | solution 1 for GlobalTheory.T.exists_hermitian_splitUnitary_lowerBlock_invertible
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T22:15:32.47355+00:00
-- url     : https://prove2.me/submissions/ac4977f9-dcf3-4e62-a7fa-cc0ab5f7f087

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsHermitianSplitUnitaryLowerBlockInvertible
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_UnipVal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_PadicIsNonarchimedeanLocalField
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsHermitianSplitUnitaryLowerBlockInvertibleStatement
import Theorems.Thm_GlobalTheory_KSp_exists_herm_transverse


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
theorem _root_.solution : ∀ (F : Type) [Field F] [CharZero F] (E : Type) [Field E] [Algebra F E] (c : E →ₐ[F] E) (δ : E) (hE : IsQuad c δ) (ν : Type) [Fintype ν] [DecidableEq ν] (g : UG c (stdJ ν E)), ∃ t : Matrix ν ν E, (t.map c)ᵀ = t ∧ ((mat c g).toBlocks₂₁ + (mat c g).toBlocks₂₂ * t).det ≠ 0 := by
  first | exact @GlobalTheory.KSp.exists_herm_transverse | exact GlobalTheory.KSp.exists_herm_transverse | (intros; apply GlobalTheory.KSp.exists_herm_transverse <;> assumption)
end _root_.GlobalTheory.T
