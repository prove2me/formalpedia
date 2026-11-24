-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.InertCount.isInt_smul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T17:03:40.431836+00:00
-- url     : https://prove2.me/submissions/37b6122f-2b98-448a-8459-46a427f1794f

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_HasLenOfLatLen
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_TwistedProofs_CountOfHeisenbergIndex

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.InertZeta Formalism.UG Matrix
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.InertCount
variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] {ϖ : L} {σ : L →+* L} {q N : ℕ}
namespace GlobalTheory.CompanionTheory.InertCount
theorem _root_.solution {ϖ : L} (hϖ : ϖ ∈ intL L) (e : ℕ) {C : Matrix (Fin N) (Fin N) L} (hC : IsInt C) :
    IsInt (ϖ ^ e • C) := by
  intro i j
  rw [Matrix.smul_apply, smul_eq_mul]
  exact mul_mem (pow_mem hϖ e) (hC i j)
end GlobalTheory.CompanionTheory.InertCount
