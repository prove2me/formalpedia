-- Prove2me | solution 1 for GlobalTheory.T.gl_hom_nnreal_trivial_of_scalar_trivial
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T23:07:34.418322+00:00
-- url     : https://prove2.me/submissions/06e8b9d2-6a6a-412c-8d1b-0bf9b851b065

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SatakeParameters_GlHomNnrealTrivialOfScalarTrivial
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SatakeParameters_GlHomNnrealTrivialOfScalarTrivialStatement
import Theorems.Thm_GlobalTheory_gl_hom_nnreal_trivial_of_scalar


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (k : Type) [Field k], (∃ x : k, x ≠ 0 ∧ x ≠ 1) → ∀ (N : ℕ) (φ : GL (Fin N) k →* NNReal), (∀ z : kˣ, φ (Matrix.GeneralLinearGroup.scalar (Fin N) z) = 1) → ∀ g, φ g = 1 := by
  first | exact @GlobalTheory.gl_hom_nnreal_trivial_of_scalar | exact GlobalTheory.gl_hom_nnreal_trivial_of_scalar | (intros; apply GlobalTheory.gl_hom_nnreal_trivial_of_scalar <;> assumption)
end _root_.GlobalTheory.T
