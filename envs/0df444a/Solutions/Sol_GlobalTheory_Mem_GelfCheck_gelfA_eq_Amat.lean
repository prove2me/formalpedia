-- Prove2me | solution 1 for GlobalTheory.Mem.GelfCheck.gelfA_eq_Amat
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T18:55:43.371839+00:00
-- url     : https://prove2.me/submissions/893cf731-c0cb-4173-a491-92a0f2d60308

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_GelfA
import Definitions.Def_Formalism_RealPlaceAnalysis_StatementB
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_TracePowApply
import Theorems.Thm_Formalism_GradedWeylDivisibility_rowDivL_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.GradedWeylDivisibility.rowDivL_apply



set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.Mem GlobalTheory.Mem.GelfCheck
open MvPolynomial GlobalTheory.Mem.Gelf
open MvPolynomial
namespace GlobalTheory.Mem.GelfCheck
namespace _root_.GlobalTheory.Mem.GelfCheck
theorem _root_.solution {N : ℕ} (μ : Fin N → ℂ) :
    _root_.GlobalTheory.Mem.Gelf.gelfA μ = _root_.Formalism.REAL.Amat (_root_.Formalism.REAL.lsh μ) := by
  ext a b
  simp only [_root_.GlobalTheory.Mem.Gelf.gelfA, _root_.Formalism.REAL.Amat, _root_.Formalism.REAL.lsh, Matrix.of_apply]
  split_ifs with hab
  · subst hab
    have ha := a.isLt
    have h1 : 1 ≤ N := by omega
    have h2 : a.val ≤ N - 1 := by omega
    rw [Nat.cast_sub h2, Nat.cast_sub h1, Nat.cast_one]
  · rfl
  · rfl
end _root_.GlobalTheory.Mem.GelfCheck
end GlobalTheory.Mem.GelfCheck
