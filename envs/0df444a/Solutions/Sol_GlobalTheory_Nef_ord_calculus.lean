-- Prove2me | solution 1 for GlobalTheory.Nef.ord_calculus
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T01:29:28.636106+00:00
-- url     : https://prove2.me/submissions/2c7fe3ab-3390-47b3-8fd3-ac0b3137d8bc

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_IsAdmissibleIntegralBasisChangeOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_FunctionFieldPlaceOrderCalculus
import Theorems.Thm_GlobalTheory_Nef_OrdCalc_ord_mul
import Theorems.Thm_GlobalTheory_Nef_OrdCalc_ord_zpow
import Theorems.Thm_GlobalTheory_Nef_OrdCalc_le_one_iff
import Theorems.Thm_GlobalTheory_Nef_OrdCalc_le_iff
import Theorems.Thm_GlobalTheory_Nef_OrdCalc_eq_one_iff
import Theorems.Thm_GlobalTheory_Nef_OrdCalc_exists_unif
import Theorems.Thm_GlobalTheory_Nef_OrdCalc_nrm_max
import Theorems.Thm_GlobalTheory_Nef_OrdCalc_nrm_smul
import Theorems.Thm_GlobalTheory_Nef_OrdCalc_unimod_mul_inv
import Theorems.Thm_GlobalTheory_Nef_OrdCalc_nrm_unimod

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
set_option autoImplicit false
open GlobalTheory.Nef.OrdCalc
namespace GlobalTheory.Nef
theorem _root_.solution : ∀ (k F : Type) [Field k] [Field F] [Algebra k F], ∀ v : Place k F, (∀ x y : F, x ≠ 0 → y ≠ 0 → ord v (x * y) = ord v x + ord v y) ∧ (∀ x : F, x ≠ 0 → ∀ m : ℤ, ord v (x ^ m) = m * ord v x) ∧ (∀ x : F, x ≠ 0 → (v.1 x ≤ 1 ↔ 0 ≤ ord v x)) ∧ (∀ x : F, x ≠ 0 → (v.1 x = 1 ↔ ord v x = 0)) ∧ (∀ x y : F, x ≠ 0 → y ≠ 0 → (v.1 x ≤ v.1 y ↔ ord v y ≤ ord v x)) ∧ (∃ π : F, π ≠ 0 ∧ ord v π = 1) ∧ (∀ (n : ℕ) (x : Fin n → F), x ≠ 0 → ∃ i, x i ≠ 0 ∧ nrm v x = v.1 (x i) ∧ ordVec v x = ord v (x i) ∧ ∀ j, v.1 (x j) ≤ v.1 (x i)) ∧ (∀ (n : ℕ) (x : Fin n → F) (c : F), nrm v (c • x) = v.1 c * nrm v x) ∧ (∀ (n : ℕ) (u : Matrix (Fin n) (Fin n) F) (x : Fin n → F), Unimod v u → nrm v (u.mulVec x) = nrm v x) ∧ (∀ (n : ℕ) (u u' : Matrix (Fin n) (Fin n) F), Unimod v u → Unimod v u' → Unimod v (u * u') ∧ Unimod v u⁻¹) := by
  intro k F _ _ _ v
  exact ⟨fun x y hx hy => ord_mul v x y hx hy, fun x _ m => ord_zpow v x m,
    fun x hx => le_one_iff v x hx, fun x hx => eq_one_iff v x hx, fun x y hx hy => le_iff v x y hx hy,
    exists_unif v, fun n x hx => nrm_max v n x hx, fun n x c => nrm_smul v n x c,
    fun n u x hu => nrm_unimod v n u x hu, fun n u u' hu hu' => unimod_mul_inv v n u u' hu hu'⟩
end GlobalTheory.Nef
