-- Prove2me | solution 1 for GlobalTheory.Nef.PlaceResiduePowerBound.exists_one_lt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T01:03:57.975922+00:00
-- url     : https://prove2.me/submissions/6377e8d5-d32d-4135-9742-e54eb0644642

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_IsAdmissibleIntegralBasisChangeOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_FunctionFieldPlaceRestrictionExistsPow
import Theorems.Thm_GroundTheory_FunctionField_Place_ordHom_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GroundTheory.FunctionField.Place.ordHom_apply



set_option autoImplicit false
open scoped IntermediateField Polynomial RatFunc
open GlobalTheory.Nef
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.Nef GlobalTheory.Nef.PlaceResiduePowerBound
open WithZero
variable {F : Type} [Field F]
namespace GlobalTheory.Nef.PlaceResiduePowerBound
theorem _root_.solution {E : Type} [Field E] [Algebra F E] [FiniteDimensional F E]
    (p : Valuation E ℤᵐ⁰) (hp : Function.Surjective p) : ∃ a : F, 1 < p (algebraMap F E a) := by
  by_contra hcon
  push_neg at hcon
  obtain ⟨y, hy⟩ := hp (exp (1 : ℤ))
  have hy1 : 1 < p y := by rw [hy, ← exp_zero, exp_lt_exp]; norm_num
  obtain ⟨f, hfm, hfy⟩ := Algebra.IsIntegral.isIntegral (R := F) y
  rw [hfm.as_sum] at hfy
  simp only [Polynomial.eval₂_add, Polynomial.eval₂_X_pow, Polynomial.eval₂_finset_sum,
    Polynomial.eval₂_mul, Polynomial.eval₂_C] at hfy
  have hlt : p (∑ i ∈ Finset.range f.natDegree, algebraMap F E (f.coeff i) * y ^ i) <
      p y ^ f.natDegree := by
    apply p.map_sum_lt (pow_ne_zero _ (ne_of_gt (lt_trans zero_lt_one hy1)))
    intro i hi
    rw [map_mul, map_pow]
    calc p (algebraMap F E (f.coeff i)) * p y ^ i ≤ 1 * p y ^ i := mul_le_mul_of_nonneg_right (hcon _) zero_le'
      _ = p y ^ i := one_mul _
      _ < p y ^ f.natDegree := pow_lt_pow_right₀ hy1 (Finset.mem_range.1 hi)
  have hs : ∑ i ∈ Finset.range f.natDegree, algebraMap F E (f.coeff i) * y ^ i =
      -(y ^ f.natDegree) := by linear_combination hfy
  rw [hs, Valuation.map_neg, map_pow] at hlt
  exact lt_irrefl _ hlt
end GlobalTheory.Nef.PlaceResiduePowerBound
