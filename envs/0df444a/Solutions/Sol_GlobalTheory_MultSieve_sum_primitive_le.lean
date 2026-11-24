-- Prove2me | solution 1 for GlobalTheory.MultSieve.sum_primitive_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T19:22:26.557152+00:00
-- url     : https://prove2.me/submissions/c195044b-9f9f-4f34-bdb3-56dd5eb9d9eb

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_SumIntervalIntegralLeOfSpaced
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_GaussSumMulGaussSumInvOfIsPrimitive
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_MultiplicativeLargeSieve
import Theorems.Thm_GlobalTheory_MultSieve_norm_sq_gaussSum
import Theorems.Thm_GlobalTheory_MultSieve_sum_norm_sq_char

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
theorem _root_.solution {q : ℕ} [NeZero q] (s : Finset ℕ) (a : ℕ → ℂ) :
    ∑ᶠ χ ∈ {χ : DirichletCharacter ℂ q | χ.IsPrimitive}, ‖∑ n ∈ s, a n * χ (n : ZMod q)‖ ^ 2
      ≤ ∑ b ∈ (Finset.range q).filter (fun b => Nat.Coprime b q),
        ‖∑ n ∈ s, a n * Complex.exp (2 * Real.pi * I * n * (((b : ℝ) / q : ℝ) : ℂ))‖ ^ 2 := by
  classical
  set F : ZMod q → ℂ := fun b => ∑ n ∈ s, a n * ZMod.stdAddChar ((n : ZMod q) * b) with hF
  have hq : (0 : ℝ) < q := by exact_mod_cast NeZero.pos q
  have h1 : ∀ χ : DirichletCharacter ℂ q, χ.IsPrimitive →
      q * ‖∑ n ∈ s, a n * χ (n : ZMod q)‖ ^ 2 = ‖∑ b : ZMod q, χ⁻¹ b * F b‖ ^ 2 := by
    intro χ hχ
    have hχ' : (χ⁻¹).IsPrimitive := by
      rw [DirichletCharacter.isPrimitive_def, DirichletCharacter.conductor_inv]; exact hχ
    rw [← norm_sq_gaussSum hχ', ← mul_pow, ← norm_mul]
    congr 2
    simp only [hF, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun n _ => ?_
    have h := gaussSum_mulShift_of_isPrimitive (ZMod.stdAddChar (N := q)) hχ' (n : ZMod q)
    rw [inv_inv] at h
    rw [mul_left_comm, mul_comm (gaussSum _ _), ← h, gaussSum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [AddChar.mulShift_apply]; ring
  have h2 : ∑ b : ZMod q, (if IsUnit b then ‖F b‖ ^ 2 else 0)
      = ∑ b ∈ (Finset.range q).filter (fun b => Nat.Coprime b q),
        ‖∑ n ∈ s, a n * Complex.exp (2 * Real.pi * I * n * (((b : ℝ) / q : ℝ) : ℂ))‖ ^ 2 := by
    rw [Finset.sum_filter]
    symm
    refine Finset.sum_nbij' (fun b => (b : ZMod q)) (fun b => b.val) (by simp)
      (fun b _ => by simpa using ZMod.val_lt b)
      (fun b hb => ZMod.val_cast_of_lt (by simpa using hb)) (by simp) ?_
    intro b _
    refine if_congr (ZMod.isUnit_iff_coprime b q).symm ?_ rfl
    congr 2
    refine Finset.sum_congr rfl fun n _ => ?_
    have := ZMod.stdAddChar_coe (N := q) ((n * b : ℕ) : ℤ)
    push_cast at this
    rw [this]
    congr 2
    push_cast; ring
  rw [← h2]
  have h3 : {χ : DirichletCharacter ℂ q | χ.IsPrimitive}
      = ↑(Finset.univ.filter fun χ : DirichletCharacter ℂ q => χ.IsPrimitive) := by simp
  rw [h3, finsum_mem_coe_finset]
  refine le_of_mul_le_mul_left ?_ hq
  rw [Finset.mul_sum, Finset.sum_congr rfl fun χ hχ => h1 χ (Finset.mem_filter.1 hχ).2]
  refine (Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
    fun _ _ _ => by positivity).trans ?_
  rw [sum_norm_sq_char]
  refine mul_le_mul_of_nonneg_right (by exact_mod_cast Nat.totient_le q)
    (Finset.sum_nonneg fun b _ => by split_ifs <;> positivity)
end GlobalTheory.MultSieve
