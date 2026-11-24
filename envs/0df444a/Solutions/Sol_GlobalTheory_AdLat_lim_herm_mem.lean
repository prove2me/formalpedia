-- Prove2me | solution 1 for GlobalTheory.AdLat.lim_herm_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T15:06:23.081128+00:00
-- url     : https://prove2.me/submissions/56d513fa-6706-4e0d-aa53-2cfad2d55116

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ExistenceOfLattices_Hat1
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_AdelicCompletionFractionalIdealProperties
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_AdelicCompletionRationalPointsAndApproximation
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_AdelicCompletionRationalPointsAndApproximationStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_AdelicCompletionLatticeSeparatedCompleteStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_AdelicCompletionFractionalIdealDivisibleEqZero
import Theorems.Thm_GlobalTheory_AdLat_lim_hat_induction
import Theorems.Thm_GlobalTheory_AdLat_lim_herm_fv
import Theorems.Thm_GlobalTheory_AdLat_adele_mul_integral
import Theorems.Thm_GlobalTheory_AdLat_tmul_mem_adelicCompletion_of_integral
import Theorems.Thm_GlobalTheory_Idele_adelicMulEquiv_mk
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.Idele.adelicMulEquiv_mk



set_option autoImplicit false
open NumberField IsDedekindDomain GlobalTheory.AdLat
open scoped TensorProduct Matrix nonZeroDivisors
open GlobalTheory GlobalTheory.AdLat
variable (F : Type) {E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] {n : ℕ}
namespace GlobalTheory.AdLat
theorem _root_.solution (c : E ≃ₐ[F] E) (G : Matrix (Fin n) (Fin n) E) {Λ : Set (Fin n → E)} {J : Set E}
    (h : ∀ x ∈ Λ, ∀ y ∈ Λ, (∑ a, ∑ b, x a * G a b * c (y b)) ∈ J) {x y : Fin n → RA F E}
    (hx : x ∈ hat F Λ) (hy : y ∈ hat F Λ) : hermBil F c G x y ∈ hat1 F J := by
  refine lim_hat_induction F (fun x => hermBil F c G x y ∈ hat1 F J) ?_ ?_ ?_ ?_ hx
  · simp
  · intro x y hx hy; rw [map_add, LinearMap.add_apply]; exact add_mem hx hy
  · intro x hx; rw [map_neg, LinearMap.neg_apply]; exact neg_mem hx
  intro a ha x hx
  refine lim_hat_induction F (fun y => hermBil F c G (a • fv F x) y ∈ hat1 F J) ?_ ?_ ?_ ?_ hy
  · simp
  · intro x y hx hy; rw [map_add]; exact add_mem hx hy
  · intro x hx; rw [map_neg]; exact neg_mem hx
  intro b hb y hy
  rw [map_smul, map_smul, LinearMap.smul_apply, smul_smul, lim_herm_fv, TensorProduct.smul_tmul',
    smul_eq_mul, mul_one]
  exact tmul_mem_adelicCompletion_of_integral F (fun v => adele_mul_integral F (hb v) (ha v)) (h x hx y hy)
end GlobalTheory.AdLat
