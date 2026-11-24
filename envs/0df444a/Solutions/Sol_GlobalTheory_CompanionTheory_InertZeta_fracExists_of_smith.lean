-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.InertZeta.fracExists_of_smith
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T19:12:03.94383+00:00
-- url     : https://prove2.me/submissions/b93d87ab-0a1d-487b-bf27-0628c4002bae

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_HasLenOfLatLen
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_TwistedProofs_FractionExistsOfSmith
import Theorems.Thm_GlobalTheory_CompanionTheory_InertZeta_hasLen_diagonal
import Theorems.Thm_GlobalTheory_InertZeta_HasLen_len_eq
import Theorems.Thm_GlobalTheory_InertZeta_HasLen_mul_mul


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.InertZeta
open GlobalTheory.InertZeta
variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] {n : ℕ}
namespace GlobalTheory.CompanionTheory.InertZeta
theorem _root_.solution : Smith → FracExists := by
  intro hS L _ _ ϖ n hϖ g hg
  obtain ⟨d, a, a', b, b', ha, ha', hb, hb', ea, eb, rfl⟩ := hS L ϖ n hϖ g hg
  have h := (hasLen_diagonal hϖ d).mul_mul ha ha' hb hb' ea eb
  rw [h.len_eq]
  exact h
end GlobalTheory.CompanionTheory.InertZeta
