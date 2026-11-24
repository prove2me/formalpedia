-- Prove2me | solution 1 for GlobalTheory.InertZeta.fracExists_of_smith
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T18:46:48.425829+00:00
-- url     : https://prove2.me/submissions/1a7f1788-4b2c-4829-acb4-8067d0339865

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_HasLenOfLatLen
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_MatrixLengthExistsOfElementaryDivisors
import Theorems.Thm_GlobalTheory_InertZeta_hasLen_diagonal_zpow
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
open GlobalTheory.InertZeta
noncomputable section
open Matrix Formalism.UG
open GlobalTheory GlobalTheory.InertZeta
namespace GlobalTheory.InertZeta
theorem _root_.solution : Smith → FracExists := by
  intro hS L _ _ ϖ n hϖ g hg
  obtain ⟨d, a, a', b, b', ha, ha', hb, hb', ea, eb, rfl⟩ := hS L ϖ n hϖ g hg
  have h := (hasLen_diagonal_zpow hϖ d).mul_mul ha ha' hb hb' ea eb
  rw [h.len_eq]
  exact h
end GlobalTheory.InertZeta
