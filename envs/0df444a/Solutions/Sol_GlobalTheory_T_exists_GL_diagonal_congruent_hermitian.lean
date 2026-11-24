-- Prove2me | solution 1 for GlobalTheory.T.exists_GL_diagonal_congruent_hermitian
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T21:39:13.44261+00:00
-- url     : https://prove2.me/submissions/edca48ce-a6b3-4018-8608-d715f8125ee0

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsGLDiagonalCongruentHermitian
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_UnipVal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_PadicIsNonarchimedeanLocalField
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsGLDiagonalCongruentHermitianStatement
import Theorems.Thm_GlobalTheory_KSp_exists_gl_diagonal_hermitian


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
theorem _root_.solution : ∀ (F : Type) [Field F] [CharZero F] (E : Type) [Field E] [Algebra F E] (c : E →ₐ[F] E) (δ : E) (hE : IsQuad c δ) (ν : Type) [Fintype ν] [DecidableEq ν] (b : Matrix ν ν E), (b.map c)ᵀ = b → b.det ≠ 0 → ∃ (a : GL ν E) (D : ν → Fˣ), b = (a : Matrix ν ν E) * diagonal (fun j => algebraMap F E (D j)) * ((a : Matrix ν ν E).map c)ᵀ := by
  first | exact @GlobalTheory.KSp.exists_gl_diagonal_hermitian | exact GlobalTheory.KSp.exists_gl_diagonal_hermitian | (intros; apply GlobalTheory.KSp.exists_gl_diagonal_hermitian <;> assumption)
end _root_.GlobalTheory.T
