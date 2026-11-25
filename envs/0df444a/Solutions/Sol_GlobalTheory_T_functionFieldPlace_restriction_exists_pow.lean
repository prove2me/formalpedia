-- Prove2me | solution 1 for GlobalTheory.T.functionFieldPlace_restriction_exists_pow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T05:08:10.766353+00:00
-- url     : https://prove2.me/submissions/596ed670-9138-4e64-86be-bb7f15c217da

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_FunctionFieldPlaceRestrictionExistsPow
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_IsAdmissibleIntegralBasisChangeOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_FunctionFieldPlaceRestrictionExistsPowStatement
import Theorems.Thm_GlobalTheory_Nef_place_res_exists_pow


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped IntermediateField Polynomial RatFunc
open GlobalTheory.Nef
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (k F E : Type) [Field k] [Field F] [Field E] [Algebra k F] [Algebra k E] [Algebra F E] [IsScalarTower k F E] [FiniteDimensional F E], (∃ ρ : Place k E → Place k F, IsRes ρ) ∧ ∀ ρ : Place k E → Place k F, IsRes ρ → ∀ p, ∃ e : ℕ, 0 < e ∧ (∀ x : F, p.1 (algebraMap F E x) = (ρ p).1 x ^ e) ∧ ∀ x : F, ord p (algebraMap F E x) = e * ord (ρ p) x := by
  first | exact @GlobalTheory.Nef.place_res_exists_pow | exact GlobalTheory.Nef.place_res_exists_pow | (intros; apply GlobalTheory.Nef.place_res_exists_pow <;> assumption)
end _root_.GlobalTheory.T
