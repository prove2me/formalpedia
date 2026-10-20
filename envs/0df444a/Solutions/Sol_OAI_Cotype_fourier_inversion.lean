-- Prove2me | solution 1 for OAI.Cotype.fourier_inversion
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T20:22:27.223589+00:00
-- url     : https://prove2.me/submissions/b13af648-13e7-4bdb-9452-fa675ff4757b

import Mathlib
import Definitions.Def_Cotype
import Definitions.Def_OAI_Analysis_Cotype_ComplexDualLift
import Definitions.Def_OAI_Analysis_Cotype_Cube

open OAI OAI.Cotype
open scoped BigOperators
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
omit [DecidableEq ι] in
theorem h50f_char_symm (p ε : ι → Bool) : character p ε = character ε p := by
  unfold character
  refine Finset.prod_congr rfl fun i _ => ?_
  cases p i <;> cases ε i <;> rfl

theorem h50f_dual (η ε : ι → Bool) :
    ∑ p : ι → Bool, character p η * character p ε =
      if η = ε then (Fintype.card (ι → Bool) : ℝ) else 0 := by
  simp only [h50f_char_symm _ η, h50f_char_symm _ ε]
  exact character_orthogonality η ε

theorem h50f_inversion (f : (ι → Bool) → ℝ) (ε : ι → Bool) :
    (∑ p, fourier f p * character p ε) = f ε := by
  have hc : (Fintype.card (ι → Bool) : ℝ) ≠ 0 := by
    exact_mod_cast (Fintype.card_ne_zero (α := ι → Bool))
  simp only [Cotype.fourier, average, smul_eq_mul, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  have : ∀ η, ∑ p : ι → Bool, (Fintype.card (ι → Bool) : ℝ)⁻¹ * (f η * character p η) * character p ε
      = (Fintype.card (ι → Bool) : ℝ)⁻¹ * f η * ∑ p : ι → Bool, character p η * character p ε := by
    intro η; rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun p _ => ?_; ring
  simp only [this, h50f_dual, mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  field_simp

theorem h50f_parseval (f : (ι → Bool) → ℝ) :
    (∑ p, fourier f p ^ 2) = average (fun ε => f ε ^ 2) := by
  have hc : (Fintype.card (ι → Bool) : ℝ) ≠ 0 := by
    exact_mod_cast (Fintype.card_ne_zero (α := ι → Bool))
  have h1 : ∀ p, fourier f p ^ 2 = ∑ η, ∑ ε, ((Fintype.card (ι → Bool) : ℝ)⁻¹) ^ 2 * (f η * f ε) *
      (character p η * character p ε) := by
    intro p
    rw [sq]
    simp only [Cotype.fourier, average, smul_eq_mul, Finset.mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun η _ => Finset.sum_congr rfl fun ε _ => ?_
    ring
  simp only [h1]
  rw [Finset.sum_comm]
  rw [Finset.sum_congr rfl (fun η _ => Finset.sum_comm)]
  simp only [← Finset.mul_sum, h50f_dual, mul_ite, mul_zero]
  simp only [Finset.sum_ite_eq, Finset.mem_univ, if_true]
  simp only [average, smul_eq_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun η _ => ?_
  field_simp

theorem solution (f : (ι → Bool) → ℝ) (ε : ι → Bool) :
    (∑ p, fourier f p * character p ε) = f ε := by
  exact h50f_inversion f ε

