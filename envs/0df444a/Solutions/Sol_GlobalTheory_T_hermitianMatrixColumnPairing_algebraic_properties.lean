-- Prove2me | solution 1 for GlobalTheory.T.hermitianMatrixColumnPairing_algebraic_properties
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T21:51:49.819685+00:00
-- url     : https://prove2.me/submissions/e6f51741-925a-4b8e-9ba8-1816b7c9fc46

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HermitianMatrixColumnPairingAlgebraicProperties
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_UnipVal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_PadicIsNonarchimedeanLocalField
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HermitianMatrixColumnPairingAlgebraicPropertiesStatement
import Theorems.Thm_GlobalTheory_KSp_pr_alg


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
theorem _root_.solution : ∀ (F : Type) [Field F] [CharZero F] (E : Type) [Field E] [Algebra F E] (c : E →ₐ[F] E) (δ : E) (hE : IsQuad c δ) (α : Type) [Fintype α] [DecidableEq α] (ν : Type) [Fintype ν] [DecidableEq ν] (Q : Matrix α α E) (_ : IsHerm c Q), ∃ β : Matrix α ν E →ₗ[F] Matrix α ν E →ₗ[F] F, (∀ x y, β x y = pr c Q x y) ∧ (∀ x y, β x y = β y x) ∧ (∀ y, (∀ x, β x y = 0) → y = 0) ∧ (∀ (x y : Matrix α ν E) (a : Matrix ν ν E), β (x * a) y = β x (y * (a.map c)ᵀ)) ∧ ∀ x y, β x y = 2⁻¹ * Algebra.trace F E (Matrix.trace (Qᵀ * (x * (y.map c)ᵀ))) := by
  first | exact @GlobalTheory.KSp.pr_alg | exact GlobalTheory.KSp.pr_alg | (intros; apply GlobalTheory.KSp.pr_alg <;> assumption)
end _root_.GlobalTheory.T
