-- Prove2me | solution 1 for GlobalTheory.T.isSLTwoPermutedModularFamily_iff_values
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T18:22:14.156695+00:00
-- url     : https://prove2.me/submissions/86aca18c-4384-4da7-9ee1-3d6e8c030752

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsSLTwoPermutedModularFamilyIffValues
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_HasQIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsSLTwoPermutedModularFamilyIffValuesStatement
import Theorems.Thm_GlobalTheory_QFam_isFam_iff_values


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
theorem _root_.solution : ∀ (ι : Type) (act : ι → SL(2, ℤ) → ι) (w : ℤ) (f : ι → ℍ → ℂ), IsFam act w f ↔ ∀ (i : ι) (γ : SL(2, ℤ)) (τ : ℍ), f i (γ • τ) = (((γ 1 0 : ℤ) : ℂ) * τ + ((γ 1 1 : ℤ) : ℂ)) ^ w * f (act i γ) τ := by
  first | exact @GlobalTheory.QFam.isFam_iff_values | exact GlobalTheory.QFam.isFam_iff_values | (intros; apply GlobalTheory.QFam.isFam_iff_values <;> assumption)
end _root_.GlobalTheory.T
