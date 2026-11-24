-- Prove2me | solution 1 for GlobalTheory.MultSieve.sum_norm_sq_char
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T18:59:28.67393+00:00
-- url     : https://prove2.me/submissions/6e6d8cf1-9e6e-4cb7-b080-c7d6d5d60bc0

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_SumIntervalIntegralLeOfSpaced
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_GaussSumMulGaussSumInvOfIsPrimitive
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_MultiplicativeLargeSieve
import Theorems.Thm_Formalism_DivisionValues_LocalCovolumeBasis_key


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex DirichletCharacter ArithmeticFunction MeasureTheory
open GlobalTheory GlobalTheory.MultSieve
namespace GlobalTheory.MultSieve
theorem _root_.solution {q : ℕ} [NeZero q] (F : ZMod q → ℂ) :
    ∑ χ : DirichletCharacter ℂ q, ‖∑ b : ZMod q, χ⁻¹ b * F b‖ ^ 2
      = q.totient * ∑ b : ZMod q, if IsUnit b then ‖F b‖ ^ 2 else 0 := by
  classical
  apply Complex.ofReal_injective
  have key : ∀ χ : DirichletCharacter ℂ q, ((‖∑ b : ZMod q, χ⁻¹ b * F b‖ ^ 2 : ℝ) : ℂ)
      = ∑ b : ZMod q, ∑ c : ZMod q, (χ⁻¹ b * χ c) * (F b * (starRingEnd ℂ) (F c)) := by
    intro χ
    rw [Complex.ofReal_pow, ← Complex.mul_conj', map_sum, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun c _ => ?_
    have : (starRingEnd ℂ) (χ⁻¹ c) = χ c := by
      have := MulChar.star_apply' χ⁻¹ c
      rwa [inv_inv] at this
    rw [map_mul, this]; ring
  rw [Complex.ofReal_sum]
  simp_rw [key]
  rw [Finset.sum_comm, Complex.ofReal_mul, Complex.ofReal_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [Finset.sum_comm]
  simp_rw [← Finset.sum_mul]
  by_cases hb : IsUnit b
  · have h1 : ∀ c : ZMod q, ∑ χ : DirichletCharacter ℂ q, χ⁻¹ b * χ c
        = if b = c then (q.totient : ℂ) else 0 := by
      intro c
      rw [← DirichletCharacter.sum_char_inv_mul_char_eq ℂ hb c]
      refine Finset.sum_congr rfl fun χ _ => ?_
      obtain ⟨u, rfl⟩ := hb
      rw [MulChar.inv_apply, Ring.inverse_unit, ZMod.inv_coe_unit]
    simp [h1, hb, Complex.mul_conj']
  · simp [hb, MulChar.map_nonunit _ hb]
end GlobalTheory.MultSieve
