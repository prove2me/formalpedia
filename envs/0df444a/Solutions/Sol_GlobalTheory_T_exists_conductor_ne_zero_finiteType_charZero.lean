-- Prove2me | solution 1 for GlobalTheory.T.exists_conductor_ne_zero_finiteType_charZero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T18:14:59.455687+00:00
-- url     : https://prove2.me/submissions/7c893631-e81f-4960-abeb-5c4915ace6f6

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsConductorNeZeroFiniteTypeCharZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_FiniteIntegralClosureOfEssFiniteTypeField
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsConductorNeZeroFiniteTypeCharZeroStatement
import Theorems.Thm_GlobalTheory_exists_ne_zero_mul_mem_of_isIntegral_of_fraction


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
theorem _root_.solution : ∀ (K R B : Type) [Field K] [CharZero K] [CommRing R] [IsDomain R] [Algebra K R] [Algebra.FiniteType K R] [CommRing B] [IsDomain B] [Algebra R B], Function.Injective (algebraMap R B) → ∃ c : R, c ≠ 0 ∧ ∀ x : B, IsIntegral R x → (∃ r s : R, r ≠ 0 ∧ algebraMap R B r * x = algebraMap R B s) → ∃ s : R, algebraMap R B c * x = algebraMap R B s := by
  first | exact @GlobalTheory.exists_ne_zero_mul_mem_of_isIntegral_of_fraction | exact GlobalTheory.exists_ne_zero_mul_mem_of_isIntegral_of_fraction | (intros; apply GlobalTheory.exists_ne_zero_mul_mem_of_isIntegral_of_fraction <;> assumption)
end _root_.GlobalTheory.T
