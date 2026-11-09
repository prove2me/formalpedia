-- Prove2me | solution 1 for NestedLogitAssort.DeltaGrid.constraint_zero_weight
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-08T12:06:37.879169+00:00
-- url     : https://prove2.me/submissions/49abbc24-5fcb-42c6-859f-542eb0bd7607

import Mathlib
import Definitions.Def_NestedLogitAssort_DeltaGrid_T

open NestedLogitAssort.DeltaGrid in
theorem solution {M : Type*} {n : ℕ} (I : Instance M n) (i : M)
    (hw0 : 0 ≤ I.w0 i) (hv : ∀ j, 0 ≤ I.v i j) (γbar : ℝ) (hγbar0 : 0 ≤ γbar)
    (δ : ℝ) (hδ : 1 < δ) (x : ℝ) (hx : 0 ≤ x) (yi : ℝ) (hy : T I i ∅ x ≤ yi)
    (S : Finset (Fin n)) (hS : S = ∅ ∨ V I i S = 0) :
    T I i S (δ ^ (2 * γbar + 1) * x) ≤ δ ^ (γbar + 1) * yi := by
  have hVS : V I i S = I.w0 i ∧ R I i S = 0 := by
    rcases hS with rfl | h0
    · refine ⟨by simp [V], ?_⟩
      simp [R]
    · have hsum : 0 ≤ ∑ j ∈ S, I.v i j := Finset.sum_nonneg (fun j _ => hv j)
      have hw : I.w0 i = 0 := by unfold V at h0; linarith
      refine ⟨by rw [h0, hw], ?_⟩
      unfold R; rw [h0, div_zero]
  have hV0 : V I i ∅ = I.w0 i := by simp [V]
  have hR0 : R I i ∅ = 0 := by simp [R]
  unfold T at hy ⊢
  rw [hV0, hR0] at hy
  rw [hVS.1, hVS.2]
  have ha : 0 ≤ I.w0 i ^ I.γ i := Real.rpow_nonneg hw0 _
  have hP : 0 < δ ^ (γbar + 1) := Real.rpow_pos_of_pos (by linarith) _
  have hPQ : δ ^ (γbar + 1) ≤ δ ^ (2 * γbar + 1) :=
    Real.rpow_le_rpow_of_exponent_le hδ.le (by linarith)
  have h1 := mul_le_mul_of_nonneg_left hy hP.le
  have h2 := mul_le_mul_of_nonneg_left hPQ (mul_nonneg ha hx)
  nlinarith
