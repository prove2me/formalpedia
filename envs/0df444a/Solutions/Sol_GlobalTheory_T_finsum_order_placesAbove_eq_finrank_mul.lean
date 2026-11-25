-- Prove2me | solution 1 for GlobalTheory.T.finsum_order_placesAbove_eq_finrank_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T18:23:35.961335+00:00
-- url     : https://prove2.me/submissions/dc107249-7508-4b75-82fd-b3a1500288e4

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_FinsumOrderPlacesAboveEqFinrankMul
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_IsAdmissibleIntegralBasisChangeOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_FinsumOrderPlacesAboveEqFinrankMulStatement
import Theorems.Thm_GlobalTheory_Nef_finsum_ord_pull_eq_finrank_mul


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
theorem _root_.solution : ∀ (k F E : Type) [Field k] [IsAlgClosed k] [CharZero k] [Field F] [Field E] [Algebra k F] [Algebra k E] [Algebra F E] [IsScalarTower k F E] [FiniteDimensional F E], IsFF k F →
  ∀ ρ : Place k E → Place k F, IsRes ρ → (∀ s : Set (Place k F), s.Finite → (ρ ⁻¹' s).Finite) ∧ ∀ φ : Place k F → F, {v | ord v (φ v) ≠ 0}.Finite → ∑ᶠ p : Place k E, ord p (algebraMap F E (φ (ρ p))) = Module.finrank F E * ∑ᶠ v, ord v (φ v) := by
  first | exact @GlobalTheory.Nef.finsum_ord_pull_eq_finrank_mul | exact GlobalTheory.Nef.finsum_ord_pull_eq_finrank_mul | (intros; apply GlobalTheory.Nef.finsum_ord_pull_eq_finrank_mul <;> assumption)
end _root_.GlobalTheory.T
