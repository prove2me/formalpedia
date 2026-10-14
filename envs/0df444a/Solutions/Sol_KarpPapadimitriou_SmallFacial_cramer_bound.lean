-- Prove2me | solution 1 for KarpPapadimitriou.SmallFacial.cramer_bound
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-12T21:34:28.705992+00:00
-- url     : https://prove2.me/submissions/80ae380f-d7b4-4efe-af2b-a3403bdfa20b

import Mathlib
import Definitions.Def_KarpPapadimitriou_SmallFacial_COP



namespace KarpPapadimitriou.SmallFacial

theorem cb_minor_bound (m x : ℕ) (W : Matrix (Fin m) (Fin (m+1)) ℤ)
    (hWb : ∀ i j, (W i j).natAbs ≤ 2 * x) (j : Fin (m+1)) :
    (Matrix.det (W.submatrix id j.succAbove)).natAbs ≤ (m+1)^m * (2*x)^m := by
  have h := Matrix.det_le (A := W.submatrix id j.succAbove) (abv := AbsoluteValue.abs)
    (x := ((2*x : ℕ) : ℤ)) (by
      intro i k
      have := hWb i (j.succAbove k)
      simp only [AbsoluteValue.abs_apply, Matrix.submatrix_apply, id]
      rw [Int.abs_eq_natAbs]; exact_mod_cast this)
  simp only [AbsoluteValue.abs_apply, Fintype.card_fin, nsmul_eq_mul] at h
  rw [Int.abs_eq_natAbs] at h
  have h2 : (Matrix.det (W.submatrix id j.succAbove)).natAbs ≤ m.factorial * (2*x)^m := by
    zify; push_cast at h ⊢; exact h
  calc _ ≤ _ := h2
    _ ≤ (m+1)^m * (2*x)^m := by
      apply Nat.mul_le_mul_right
      calc m.factorial ≤ m^m := Nat.factorial_le_pow m
        _ ≤ (m+1)^m := Nat.pow_le_pow_left (Nat.le_succ m) m

theorem cb_core (m x : ℕ) (hx : 1 ≤ x) (W : Matrix (Fin m) (Fin (m+1)) ℤ) (v₀ : Fin (m+1) → ℤ)
    (hW : LinearIndependent ℚ (fun i : Fin m => fun j : Fin (m+1) => (W i j : ℚ)))
    (hWb : ∀ i j, (W i j).natAbs ≤ 2 * x)
    (hv : ∀ j, (v₀ j).natAbs ≤ x) :
    ∃ f : Fin (m+1) → ℤ,
      f ≠ 0 ∧
      (∀ i, (∑ j, W i j * f j) = 0) ∧
      (∀ j, (f j).natAbs ≤ (2 * (m+1) * x) ^ (m+1)) ∧
      (∑ j, f j * v₀ j).natAbs ≤ (2 * (m+1) * x) ^ (m+1) := by
  set f : Fin (m+1) → ℤ := fun j => (-1)^(j:ℕ) * Matrix.det (W.submatrix id j.succAbove) with hf
  refine ⟨f, ?_, ?_, ?_, ?_⟩
  · -- nonzero
    have hspan : Submodule.span ℚ (Set.range (fun i : Fin m => fun j : Fin (m+1) => (W i j : ℚ))) ≠ ⊤ := by
      intro htop
      have := finrank_span_eq_card hW
      rw [htop, finrank_top] at this
      simp at this
    obtain ⟨u, hu⟩ : ∃ u : Fin (m+1) → ℚ, u ∉ Submodule.span ℚ (Set.range (fun i : Fin m => fun j : Fin (m+1) => (W i j : ℚ))) := by
      by_contra h
      push_neg at h
      exact hspan (eq_top_iff.mpr fun y _ => h y)
    have hli : LinearIndependent ℚ (Fin.cons u (fun i : Fin m => fun j : Fin (m+1) => (W i j : ℚ)) : Fin (m+1) → Fin (m+1) → ℚ) :=
      (linearIndependent_fin_cons).2 ⟨hW, hu⟩
    set B : Matrix (Fin (m+1)) (Fin (m+1)) ℚ := Matrix.of (Fin.cons u (fun i : Fin m => fun j : Fin (m+1) => (W i j : ℚ)) : Fin (m+1) → Fin (m+1) → ℚ) with hB
    have hBu : IsUnit B := by
      rw [← Matrix.linearIndependent_rows_iff_isUnit]
      exact hli
    have hdet : B.det ≠ 0 := by
      have := (Matrix.isUnit_iff_isUnit_det B).1 hBu
      exact this.ne_zero
    rw [Matrix.det_succ_row_zero] at hdet
    obtain ⟨j, -, hj⟩ := Finset.exists_ne_zero_of_sum_ne_zero hdet
    intro hf0
    have hfj : f j = 0 := by rw [hf0]; rfl
    have hd0 : Matrix.det (W.submatrix id j.succAbove) = 0 := by
      simp only [hf] at hfj
      rcases mul_eq_zero.1 hfj with h | h
      · simp at h
      · exact h
    apply hj
    have : B.submatrix Fin.succ j.succAbove = (W.submatrix id j.succAbove).map (Int.cast : ℤ → ℚ) := by
      ext a b; simp [hB]
    have hc : ((W.submatrix id j.succAbove).map (Int.cast : ℤ → ℚ)).det = ((Matrix.det (W.submatrix id j.succAbove) : ℤ) : ℚ) := by
      simpa using (RingHom.map_det (Int.castRingHom ℚ) (W.submatrix id j.succAbove)).symm
    rw [this, hc, hd0]; simp
  · intro i
    set A : Matrix (Fin (m+1)) (Fin (m+1)) ℤ := Matrix.vecCons (W i) W with hA
    have h0 : A.det = 0 := Matrix.det_zero_of_row_eq (i := 0) (j := i.succ) (Fin.succ_ne_zero i).symm (by rw [hA]; rfl)
    rw [Matrix.det_succ_row_zero] at h0
    rw [← h0]
    apply Finset.sum_congr rfl
    intro j _
    have : A.submatrix Fin.succ j.succAbove = W.submatrix id j.succAbove := by
      ext a b; rw [hA]; rfl
    rw [this]
    have h00 : A 0 j = W i j := by rw [hA]; rfl
    rw [h00]
    simp only [hf]; ring
  · intro j
    have h1 := cb_minor_bound m x W hWb j
    have : (f j).natAbs = (Matrix.det (W.submatrix id j.succAbove)).natAbs := by
      simp [hf, Int.natAbs_mul, Int.natAbs_pow]
    rw [this]
    refine h1.trans ?_
    calc (m+1)^m * (2*x)^m = (2*(m+1)*x)^m := by rw [← mul_pow]; ring_nf
      _ ≤ (2*(m+1)*x)^(m+1) := Nat.pow_le_pow_right (by positivity) (Nat.le_succ m)
  · have hb : ∀ j, (f j * v₀ j).natAbs ≤ (2*(m+1)*x)^m * x := by
      intro j
      have h1 := cb_minor_bound m x W hWb j
      have : (f j).natAbs = (Matrix.det (W.submatrix id j.succAbove)).natAbs := by
        simp [hf, Int.natAbs_mul, Int.natAbs_pow]
      rw [Int.natAbs_mul, this]
      apply Nat.mul_le_mul _ (hv j)
      calc _ ≤ (m+1)^m * (2*x)^m := h1
        _ = (2*(m+1)*x)^m := by rw [← mul_pow]; ring_nf
    have hs : (∑ j, f j * v₀ j).natAbs ≤ ∑ j, (f j * v₀ j).natAbs := Int.natAbs_sum_le _ _
    refine hs.trans ?_
    calc ∑ j, (f j * v₀ j).natAbs ≤ ∑ _j : Fin (m+1), (2*(m+1)*x)^m * x := Finset.sum_le_sum fun j _ => hb j
      _ = (m+1) * ((2*(m+1)*x)^m * x) := by simp
      _ ≤ (2*(m+1)*x)^(m+1) := by
        rw [pow_succ]
        have : (m+1) * ((2*(m+1)*x)^m * x) = (2*(m+1)*x)^m * ((m+1)*x) := by ring
        rw [this]
        apply Nat.mul_le_mul_left
        nlinarith

theorem cb_main (n x : ℕ) (hn : 1 ≤ n) (hx : 1 ≤ x)
    (W : Matrix (Fin (n - 1)) (Fin n) ℤ) (v₀ : Fin n → ℤ)
    (hW : LinearIndependent ℚ (fun i : Fin (n - 1) => fun j : Fin n => (W i j : ℚ)))
    (hWb : ∀ i j, (W i j).natAbs ≤ 2 * x)
    (hv : ∀ j, (v₀ j).natAbs ≤ x) :
    ∃ f : Fin n → ℤ,
      f ≠ 0 ∧
      (∀ i, (∑ j, W i j * f j) = 0) ∧
      (∀ j, (f j).natAbs ≤ (2 * n * x) ^ n) ∧
      (∑ j, f j * v₀ j).natAbs ≤ (2 * n * x) ^ n := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  exact cb_core m x hx W v₀ hW hWb hv

end KarpPapadimitriou.SmallFacial

open KarpPapadimitriou.SmallFacial


theorem solution (n x : ℕ) (hn : 1 ≤ n) (hx : 1 ≤ x)
    (W : Matrix (Fin (n - 1)) (Fin n) ℤ) (v₀ : Fin n → ℤ)
    (hW : LinearIndependent ℚ (fun i : Fin (n - 1) => fun j : Fin n => (W i j : ℚ)))
    (hWb : ∀ i j, (W i j).natAbs ≤ 2 * x)
    (hv : ∀ j, (v₀ j).natAbs ≤ x) :
    ∃ f : Fin n → ℤ,
      f ≠ 0 ∧
      (∀ i, (∑ j, W i j * f j) = 0) ∧
      (∀ j, (f j).natAbs ≤ (2 * n * x) ^ n) ∧
      (∑ j, f j * v₀ j).natAbs ≤ (2 * n * x) ^ n := by
  exact cb_main n x hn hx W v₀ hW hWb hv
