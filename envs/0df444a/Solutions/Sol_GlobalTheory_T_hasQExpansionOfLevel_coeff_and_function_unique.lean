-- Prove2me | solution 1 for GlobalTheory.T.hasQExpansionOfLevel_coeff_and_function_unique
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T18:22:09.228668+00:00
-- url     : https://prove2.me/submissions/d92003c5-bd41-4c31-9c0f-cc2692c1d10b

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HasQExpansionOfLevelCoeffAndFunctionUnique
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_HasQIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HasQExpansionOfLevelCoeffAndFunctionUniqueStatement
import Theorems.Thm_GlobalTheory_QFam_hasQ_unique_both


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
theorem _root_.solution : (∀ (N : ℕ) (f : ℍ → ℂ) (a b : ℕ → ℂ), 0 < N → HasQ N f a → HasQ N f b → a = b) ∧ (∀ (N : ℕ) (f g : ℍ → ℂ) (a : ℕ → ℂ), HasQ N f a → HasQ N g a → f = g) := by
  first | exact @GlobalTheory.QFam.hasQ_unique_both | exact GlobalTheory.QFam.hasQ_unique_both | (intros; apply GlobalTheory.QFam.hasQ_unique_both <;> assumption)
end _root_.GlobalTheory.T
