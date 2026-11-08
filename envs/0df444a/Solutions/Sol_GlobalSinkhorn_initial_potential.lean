-- Prove2me | solution 1 for GlobalSinkhorn.initial_potential
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-07T20:40:35.785445+00:00
-- url     : https://prove2.me/submissions/4396a938-6f2c-49f7-83b3-ac9a24a18091

import Mathlib
import Definitions.Def_GlobalSinkhorn_potential

open Matrix

open GlobalSinkhorn in
theorem solution {n : ℕ} (hn : 2 ≤ n) (x y : Fin n → ℝ) (T : ℝ)
    (hx : ∀ i, 0 < x i) (hy : ∀ j, 0 < y j)
    (hprod : ∀ i j, T⁻¹ ≤ x i * y j ∧ x i * y j ≤ T) :
    (∀ j k, (y j)⁻¹ / (y k)⁻¹ ≤ T ^ 2) ∧
      potential (fun j => (y j)⁻¹) ≤ T ^ 4 - 1 := by
  obtain ⟨i0⟩ : Nonempty (Fin n) := ⟨⟨0, by omega⟩⟩
  have hx0 := hx i0
  have hT : 0 < T := lt_of_lt_of_le (mul_pos hx0 (hy i0)) (hprod i0 i0).2
  have key : ∀ j k, y k / y j ≤ T ^ 2 := by
    intro j k
    obtain ⟨h1, -⟩ := hprod i0 j
    obtain ⟨-, h2⟩ := hprod i0 k
    have hyj := hy j
    rw [div_le_iff₀ hyj]
    have h3 : x i0 * y k ≤ x i0 * (T ^ 2 * y j) := by
      calc x i0 * y k ≤ T := h2
        _ = T ^ 2 * T⁻¹ := by rw [pow_two, mul_assoc, mul_inv_cancel₀ hT.ne', mul_one]
        _ ≤ T ^ 2 * (x i0 * y j) := by gcongr
        _ = x i0 * (T ^ 2 * y j) := by ring
    exact le_of_mul_le_mul_left h3 hx0
  refine ⟨fun j k => by rw [inv_div_inv]; exact key j k, ?_⟩
  unfold potential avg
  simp only [inv_inv]
  have hn' : (0 : ℝ) < n := Nat.cast_pos.mpr (by omega)
  rw [div_mul_div_comm, Finset.sum_mul_sum, sub_le_sub_iff_right, div_le_iff₀ (by positivity)]
  calc ∑ i, ∑ j, (y i)⁻¹ ^ 2 * y j ^ 2 ≤ ∑ i : Fin n, ∑ j : Fin n, T ^ 4 := by
        apply Finset.sum_le_sum; intro i _
        apply Finset.sum_le_sum; intro j _
        have h0 : 0 ≤ y j / y i := div_nonneg (hy j).le (hy i).le
        calc (y i)⁻¹ ^ 2 * y j ^ 2 = (y j / y i) ^ 2 := by ring
          _ ≤ (T ^ 2) ^ 2 := pow_le_pow_left₀ h0 (key i j) 2
          _ = T ^ 4 := by ring
    _ = T ^ 4 * (n * n) := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]; ring
