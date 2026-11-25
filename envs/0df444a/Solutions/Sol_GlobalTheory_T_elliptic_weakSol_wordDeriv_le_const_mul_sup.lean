-- Prove2me | solution 1 for GlobalTheory.T.elliptic_weakSol_wordDeriv_le_const_mul_sup
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T17:50:06.897845+00:00
-- url     : https://prove2.me/submissions/e0248d40-d45d-4fe6-9313-bdf5ee804f6e

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_EllipticWeakSolWordDerivLeConstMulSup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_ZeroMemSolSet
import Definitions.Def_Formalism_UnipotentAdelicQuotients_EllRegCheck
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_EllipticWeakSolWordDerivLeConstMulSupStatement
import Theorems.Thm_GlobalTheory_HCA_dw_le_sup


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ZetaZeros.D.EllReg GlobalTheory.HCA MeasureTheory
open scoped ContDiff BoundedContinuousFunction
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (d : ℕ) (ι : Type) [Fintype ι] (P : Sys d ι) (U : Set (E d)), IsOpen U → (∀ i n w, ContDiffOn ℝ ∞ (P.a i n w) U) → (∀ x ∈ U, ∀ ξ : E d, ξ ≠ 0 → ∃ i, P.symb i x ξ ≠ 0) → ∀ (w : List (Fin d)), ∀ x₀ ∈ U, ∃ C : ℝ, 0 ≤ C ∧ ∀ u : E d → ℂ, ContinuousOn u U → WeakSol P U u → ∀ M : ℝ, (∀ x ∈ U, ‖u x‖ ≤ M) → ‖dw w u x₀‖ ≤ C * M := by
  first | exact @GlobalTheory.HCA.dw_le_sup | exact GlobalTheory.HCA.dw_le_sup | (intros; apply GlobalTheory.HCA.dw_le_sup <;> assumption)
end _root_.GlobalTheory.T
