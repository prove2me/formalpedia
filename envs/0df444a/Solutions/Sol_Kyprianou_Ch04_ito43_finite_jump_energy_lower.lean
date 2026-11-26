-- Prove2me | solution 1 for Kyprianou.Ch04.ito43_finite_jump_energy_lower
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T17:20:46.468435+00:00
-- url     : https://prove2.me/submissions/0611449d-9499-46c4-a34e-5bcc65e94e4f

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_p2_h_cadlag_finite_actual_jump_cell_test_sum_tendsto
import Theorems.Thm_AvramDividend_Classical_avram_p2_a_zero_rate_original_uniform_selected_cells_eventually_injective
open Filter Set
open scoped NNReal Topology
set_option autoImplicit false

/-- Every finite jump energy below the horizon is an eventual lower bound up to any strict slack. -/
theorem solution (Y L : NNReal → ℝ) (T : NNReal) (hT : 0 < T)
    (hR : ∀ t, ContinuousWithinAt Y (Ici t) t)
    (hL : ∀ t, 0 < t → Tendsto Y (nhdsWithin t (Iio t)) (nhds (L t)))
    (S : Finset NNReal) (hS : ∀ t ∈ S, 0 < t ∧ t ≤ T)
    (C : ℝ) (hC : C < ∑ t ∈ S, (Y t-L t)^2) :
    ∀ᶠ n : ℕ in atTop, C ≤ ∑ k ∈ Finset.range (n+1),
      (Y (T*((k+1 : ℕ) : NNReal)/((n+1 : ℕ) : NNReal)) -
       Y (T*(k : NNReal)/((n+1 : ℕ) : NNReal)))^2 := by
  classical
  have heq (t : NNReal) (ht : t ∈ S) : Function.leftLim Y t = L t := by
    have : (nhdsWithin t (Iio t)).NeBot := nhdsLT_neBot_of_exists_lt ⟨0,(hS t ht).1⟩
    exact leftLim_eq_of_tendsto (hL t (hS t ht).1)
  obtain ⟨idx,hidx,hlim⟩ :=
    AvramDividend.Classical.avram_p2_h_cadlag_finite_actual_jump_cell_test_sum_tendsto
      Y S T hT (fun z : ℝ => z^2) (by fun_prop) hS
      (fun t ht => by rw [heq t ht]; exact hL t (hS t ht).1)
      (fun t _ => hR t)
  have hinj :=
    AvramDividend.Classical.avram_p2_a_zero_rate_original_uniform_selected_cells_eventually_injective
      T S idx (fun t ht n => (hidx t ht n).2)
  have hlimit : Tendsto (fun n : ℕ => ∑ t ∈ S,
      (Y (((idx t n+1 : ℕ) : NNReal)*(T/((n : NNReal)+1))) -
       Y ((idx t n : NNReal)*(T/((n : NNReal)+1))))^2) atTop
      (nhds (∑ t ∈ S, (Y t-L t)^2)) := by
    convert hlim using 2
    apply Finset.sum_congr rfl
    intro t ht
    rw [heq t ht]
  filter_upwards [hinj,hlimit.eventually (lt_mem_nhds hC)] with n hi hn
  let A : ℕ → ℝ := fun k =>
    (Y (T*((k+1 : ℕ) : NNReal)/((n+1 : ℕ) : NNReal)) -
     Y (T*(k : NNReal)/((n+1 : ℕ) : NNReal)))^2
  have hsub : S.image (fun t => idx t n) ⊆ Finset.range (n+1) := by
    intro k hk
    obtain ⟨t,ht,rfl⟩ := Finset.mem_image.mp hk
    exact Finset.mem_range.mpr (Nat.lt_succ_of_le (hidx t ht n).1)
  have hsum : ∑ t ∈ S, A (idx t n) ≤ ∑ k ∈ Finset.range (n+1), A k := by
    rw [← Finset.sum_image hi]
    exact Finset.sum_le_sum_of_subset_of_nonneg hsub (fun k _ _ => sq_nonneg _)
  have he : (∑ t ∈ S, A (idx t n)) = ∑ t ∈ S,
      (Y (((idx t n+1 : ℕ) : NNReal)*(T/((n : NNReal)+1))) -
       Y ((idx t n : NNReal)*(T/((n : NNReal)+1))))^2 := by
    apply Finset.sum_congr rfl
    intro t ht
    dsimp [A]
    push_cast
    rw [mul_comm T ((idx t n : NNReal)+1),mul_div_assoc,
      mul_comm T (idx t n : NNReal),mul_div_assoc]
  rw [he] at hsum
  exact (le_of_lt hn).trans hsum
