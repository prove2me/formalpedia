-- Prove2me | solution 1 for NestedLogitNBR.optimal_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-07T21:06:43.473229+00:00
-- url     : https://prove2.me/submissions/354b3eb0-2170-4ea3-ad38-86ccad3dbc83

import Mathlib
import Definitions.Def_NestedLogitNBR_IsOptimalNBR

open NestedLogitNBR in
theorem solution {m n : ℕ} (v0 : ℝ) (r v : Fin m → Fin n → ℝ) (γ : Fin m → ℝ)
    (hv0 : 0 ≤ v0) (hv : ∀ i j, 0 ≤ v i j) (hr : ∀ i j, 0 ≤ r i j)
    (hord : ∀ i, Antitone (r i)) (hγ : ∀ i, 0 ≤ γ i)
    (x : ℝ) (y : Fin m → ℝ) (hopt : IsOptimalNBR v0 r v γ x y) :
    0 ≤ x ∧ ∀ i, 0 ≤ y i := by
  obtain ⟨⟨hsum, hcon⟩, hmin⟩ := hopt
  have hW : ∀ i S, 0 ≤ prefWeight v i S := fun i S =>
    Finset.sum_nonneg (fun j _ => hv i j)
  have hA : ∀ i S, 0 ≤ nestAttraction v γ i S := by
    intro i S
    unfold nestAttraction
    split_ifs
    · exact le_refl 0
    · exact Real.rpow_nonneg (hW i S) _
  have hR : ∀ i S, 0 ≤ nestRevenue r v i S := fun i S =>
    div_nonneg (Finset.sum_nonneg (fun j _ => mul_nonneg (hr i j) (hv i j))) (hW i S)
  have hy : ∀ i, 0 ≤ y i := by
    intro i
    have h := hcon i 0 (Nat.zero_le _)
    have h0 : nestAttraction v γ i (nbr 0) = 0 := by
      simp [nestAttraction, prefWeight, nbr]
    rw [h0, zero_mul] at h
    exact h
  refine ⟨?_, hy⟩
  by_contra hx
  push_neg at hx
  have hS0 : 0 ≤ ∑ i, y i := Finset.sum_nonneg (fun i _ => hy i)
  have hv00 : v0 = 0 := by
    refine le_antisymm ?_ hv0
    by_contra h
    push_neg at h
    nlinarith [mul_neg_of_pos_of_neg h hx]
  rw [hv00, zero_mul] at hsum
  have hyz : ∀ i, y i = 0 := fun i =>
    (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => hy i)).mp (le_antisymm hsum hS0) i
      (Finset.mem_univ i)
  have hfeas : FeasibleNBR v0 r v γ (x - 1) y := by
    refine ⟨by rw [hv00, zero_mul]; exact hsum, fun i j hj => ?_⟩
    have h1 := hcon i j hj
    rw [hyz i] at h1 ⊢
    have hA0 : nestAttraction v γ i (nbr j) = 0 := by
      by_contra hne
      have hpos : 0 < nestAttraction v γ i (nbr j) := lt_of_le_of_ne (hA i _) (Ne.symm hne)
      have := mul_pos hpos (by linarith [hR i (nbr j)] :
        0 < nestRevenue r v i (nbr j) - x)
      linarith
    rw [hA0, zero_mul]
  have := hmin (x - 1) y hfeas
  linarith
