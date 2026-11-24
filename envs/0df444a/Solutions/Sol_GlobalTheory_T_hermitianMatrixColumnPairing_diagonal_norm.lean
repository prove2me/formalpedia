-- Prove2me | solution 1 for GlobalTheory.T.hermitianMatrixColumnPairing_diagonal_norm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T21:56:01.440424+00:00
-- url     : https://prove2.me/submissions/10f0f49d-368e-44e2-9cdf-c5d3d5755650

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HermitianMatrixColumnPairingDiagonalNorm
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_UnipVal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_PadicIsNonarchimedeanLocalField
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HermitianMatrixColumnPairingDiagonalNormStatement
import Theorems.Thm_GlobalTheory_KSp_pr_diag_norm


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
theorem _root_.solution : ∀ (F : Type) [Field F] [CharZero F] (E : Type) [Field E] [Algebra F E] (c : E →ₐ[F] E) (δ : E) (hE : IsQuad c δ) (α : Type) [Fintype α] [DecidableEq α] (ν : Type) [Fintype ν] [DecidableEq ν] (Q : Matrix α α E) (_ : IsHerm c Q) (u : Matrix α α E) (D' : α → F) (a : Matrix ν ν E) (D : ν → F), Q = u * diagonal (fun i => algebraMap F E (D' i)) * (u.map c)ᵀ → ∀ x : Matrix α ν E, 2⁻¹ * pr c Q x (x * (a * diagonal (fun j => algebraMap F E (D j)) * (a.map c)ᵀ)) = ∑ i, ∑ j, (2⁻¹ * D' i * D j) * Algebra.norm F ((uᵀ * x * a) i j) := by
  first | exact @GlobalTheory.KSp.pr_diag_norm | exact GlobalTheory.KSp.pr_diag_norm | (intros; apply GlobalTheory.KSp.pr_diag_norm <;> assumption)
end _root_.GlobalTheory.T
