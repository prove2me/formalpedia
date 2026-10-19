-- Prove2me | solution 1 for OAI.PiExponent.DeterminantContradiction.FiniteTranslation.index_card_le_pow
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-18T22:37:38.299444+00:00
-- url     : https://prove2.me/submissions/fb30c72a-d376-4cb3-a574-eb759e08bf32

import Mathlib
import Definitions.Def_OAI_PiExponent_FiniteActualTranslation

open scoped BigOperators
open OAI.PiExponent OAI.PiExponent.DeterminantContradiction
open OAI.PiExponent.DeterminantContradiction.FiniteTranslation
theorem h41_index_coord_le {nu : ℝ} (d : FixedData nu) {H : ℝ} (hH : 0 < H)
    (a : Index d H) (i : Fin d.m) : ((a.1 i : ℕ) : ℝ) ≤ H := by
  have ha := a.2
  simp only [realWeightedSimplex, Finset.mem_filter, Fintype.mem_piFinset,
    Finset.mem_range] at ha
  have h1 := Nat.lt_succ_iff.mp (ha.1 i)
  have hw : MatrixArithmetic.logWeights (finiteDenominators d) i =
      ((⌈Real.log (finiteDenominators d i)⌉₊ : ℕ) : ℝ) := rfl
  rcases Nat.eq_zero_or_pos (⌈Real.log (finiteDenominators d i)⌉₊) with h0 | hpos
  · rw [hw, h0] at h1
    simp at h1
    rw [h1]; simp; exact hH.le
  · have hw1 : (1 : ℝ) ≤ MatrixArithmetic.logWeights (finiteDenominators d) i := by
      rw [hw]; exact_mod_cast hpos
    calc ((a.1 i : ℕ) : ℝ) ≤ (⌊H / MatrixArithmetic.logWeights (finiteDenominators d) i⌋₊ : ℝ) := by
          exact_mod_cast h1
      _ ≤ H / MatrixArithmetic.logWeights (finiteDenominators d) i :=
          Nat.floor_le (div_nonneg hH.le (by linarith))
      _ ≤ H := div_le_self hH.le hw1

theorem h41_row0_le {nu : ℝ} (d : FixedData nu) {H : ℝ} (hH : 0 < H)
    (r : Row d H) : ((r.2.1 0 : ℕ) : ℝ) ≤ H / (d.v0 : ℝ) := by
  have hr := r.2.2
  simp only [strictWeightedSimplex, realWeightedSimplex, Finset.mem_filter, Fintype.mem_piFinset,
    Finset.mem_range] at hr
  have h1 := Nat.lt_succ_iff.mp (hr.1.1 0)
  have hv : InterpolationMatrix.rowWeights (d.v0 : ℝ) (d.base.theta : ℝ)
      (MatrixArithmetic.logWeights (finiteDenominators d)) 0 = d.v0 := rfl
  rw [hv] at h1
  calc ((r.2.1 0 : ℕ) : ℝ) ≤ (⌊H / (d.v0 : ℝ)⌋₊ : ℝ) := by exact_mod_cast h1
    _ ≤ H / (d.v0 : ℝ) := Nat.floor_le (div_nonneg hH.le d.v0_pos.le)

theorem h41_index_card {nu : ℝ} (d : FixedData nu) {H : ℝ} (hH : 0 < H) :
    (Fintype.card (Index d H) : ℝ) ≤ (H + 1) ^ d.m := by
  classical
  rw [Fintype.card_coe]
  have hsub : realWeightedSimplex (MatrixArithmetic.logWeights (finiteDenominators d)) H ⊆
      Fintype.piFinset (fun _ : Fin d.m => Finset.range (⌊H⌋₊ + 1)) := by
    intro a ha
    rw [Fintype.mem_piFinset]
    intro i
    rw [Finset.mem_range, Nat.lt_succ_iff]
    have := h41_index_coord_le d hH ⟨a, ha⟩ i
    exact Nat.le_floor this
  have h2 := Finset.card_le_card hsub
  rw [Fintype.card_piFinset] at h2
  simp only [Finset.card_range, Finset.prod_const, Finset.card_univ, Fintype.card_fin] at h2
  calc ((realWeightedSimplex (MatrixArithmetic.logWeights (finiteDenominators d)) H).card : ℝ)
      ≤ ((⌊H⌋₊ + 1) ^ d.m : ℕ) := by exact_mod_cast h2
    _ ≤ (H + 1) ^ d.m := by
        push_cast
        gcongr
        exact Nat.floor_le hH.le

theorem h41_fiber_card {nu : ℝ} (d : FixedData nu) {H : ℝ} (hH : 0 < H)
    (r : Row d H) (a : Index d H) :
    (Fintype.card
      ((∀ i : Fin d.m, Fin (a.1 i - r.2.1 i.succ + 1)) ×
        Fin (r.2.1 0 + 1)) : ℝ) ≤
      (H + 1) ^ d.m * (H / (d.v0 : ℝ) + 1) := by
  rw [Fintype.card_prod, Fintype.card_pi]
  simp only [Fintype.card_fin]
  push_cast
  have hv : 0 < (d.v0 : ℝ) := d.v0_pos
  apply mul_le_mul _ _ (by positivity) (by positivity)
  · calc _ ≤ ∏ _i : Fin d.m, (H + 1) := by
          apply Finset.prod_le_prod
          · intro i _; positivity
          · intro i _
            have h1 := h41_index_coord_le d hH a i
            have : ((a.1 i - r.2.1 i.succ : ℕ) : ℝ) ≤ (a.1 i : ℝ) := by
              exact_mod_cast Nat.sub_le _ _
            linarith
      _ = (H + 1) ^ d.m := by simp
  · linarith [h41_row0_le d hH r]

theorem h41_choice_card {nu : ℝ} (d : FixedData nu) {H : ℝ} (hH : 0 < H)
    (r : Row d H) :
    (Fintype.card (Choice d H r) : ℝ) ≤
      (Fintype.card (Index d H) : ℝ) *
        ((H + 1) ^ d.m * (H / (d.v0 : ℝ) + 1)) := by
  rw [Fintype.card_sigma]
  push_cast
  calc _ ≤ ∑ _a : Index d H, ((H + 1) ^ d.m * (H / (d.v0 : ℝ) + 1)) := by
        apply Finset.sum_le_sum
        intro a _
        exact_mod_cast h41_fiber_card d hH r a
    _ = _ := by simp

theorem solution
    {nu : ℝ} (d : FixedData nu) {H : ℝ} (hH : 0 < H) :
    (Fintype.card (Index d H) : ℝ) ≤ (H + 1) ^ d.m := by
  exact h41_index_card d hH

