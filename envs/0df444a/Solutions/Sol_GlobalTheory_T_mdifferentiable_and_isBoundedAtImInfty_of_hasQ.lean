-- Prove2me | solution 1 for GlobalTheory.T.mdifferentiable_and_isBoundedAtImInfty_of_hasQ
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T18:25:24.638553+00:00
-- url     : https://prove2.me/submissions/7317b396-2cc5-48bb-be24-b242f0977b76

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HasQMdifferentiableAndIsBoundedAtImInfty
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_HasQIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HasQMdifferentiableAndIsBoundedAtImInftyStatement
import Theorems.Thm_GlobalTheory_QFam_hasQ_mdifferentiable_and_isBoundedAtImInfty


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (N : ℕ) (f : ℍ → ℂ) (a : ℕ → ℂ), 0 < N → HasQ N f a → MDifferentiable 𝓘(ℂ) 𝓘(ℂ) f ∧ UpperHalfPlane.IsBoundedAtImInfty f := by
  first | exact @GlobalTheory.QFam.hasQ_mdifferentiable_and_isBoundedAtImInfty | exact GlobalTheory.QFam.hasQ_mdifferentiable_and_isBoundedAtImInfty | (intros; apply GlobalTheory.QFam.hasQ_mdifferentiable_and_isBoundedAtImInfty <;> assumption)
end _root_.GlobalTheory.T
