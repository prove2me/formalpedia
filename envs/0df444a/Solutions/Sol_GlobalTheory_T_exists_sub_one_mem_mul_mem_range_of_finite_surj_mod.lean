-- Prove2me | solution 1 for GlobalTheory.T.exists_sub_one_mem_mul_mem_range_of_finite_surj_mod
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T18:19:25.810704+00:00
-- url     : https://prove2.me/submissions/c517ea8a-8017-46e4-9624-4edb37ce09ec

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_FiniteSurjModIdealExistsCongrOneMulMemRange
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_BaseIdealIdeal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsCompletedStrictHens
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_FiniteSurjModIdealExistsCongrOneMulMemRangeStatement
import Theorems.Thm_GlobalTheory_finite_surj_mod_ideal_exists_congr_one_mul_mem_range


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.AbLaw GlobalTheory.FormalAlg
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (B C : Type) [CommRing B] [CommRing C] (f : B →+* C), f.Finite → ∀ J : Ideal B, Function.Surjective ((Ideal.Quotient.mk (J.map f)).comp f) → ∃ r : B, r - 1 ∈ J ∧ ∀ c : C, ∃ b : B, f r * c = f b := by
  first | exact @GlobalTheory.finite_surj_mod_ideal_exists_congr_one_mul_mem_range | exact GlobalTheory.finite_surj_mod_ideal_exists_congr_one_mul_mem_range | (intros; apply GlobalTheory.finite_surj_mod_ideal_exists_congr_one_mul_mem_range <;> assumption)
end _root_.GlobalTheory.T
