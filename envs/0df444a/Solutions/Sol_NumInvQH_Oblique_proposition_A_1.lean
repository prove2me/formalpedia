-- Prove2me | solution 1 for NumInvQH.Oblique.proposition_A_1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-26T15:45:46.383797+00:00
-- url     : https://prove2.me/submissions/33e6fd78-cabb-42d0-8fca-a5f23facf829

import Mathlib
import Definitions.Def_LocalDistanceNetwork_GLS
import Definitions.Def_NumInvQH_Oblique_Basic

open Matrix

namespace Aux_NIQH_A1

open LocalDistanceNetwork

variable {m n : ℕ}

lemma lA {M : Matrix (Fin m) (Fin n) ℝ} {P : Matrix (Fin n) (Fin m) ℝ}
    (h : IsMoorePenroseInverse M P) : P * Pᵀ * Mᵀ = P := by
  obtain ⟨_, h2, h3, _⟩ := h
  calc P * Pᵀ * Mᵀ = P * (M * P)ᵀ := by rw [transpose_mul, Matrix.mul_assoc]
    _ = P * (M * P) := by rw [h3]
    _ = P := by rw [← Matrix.mul_assoc, h2]

lemma lB {M : Matrix (Fin m) (Fin n) ℝ} {P : Matrix (Fin n) (Fin m) ℝ}
    (h : IsMoorePenroseInverse M P) : Mᵀ * Pᵀ * P = P := by
  obtain ⟨_, h2, _, h4⟩ := h
  calc Mᵀ * Pᵀ * P = (P * M)ᵀ * P := by rw [transpose_mul]
    _ = P * M * P := by rw [h4]
    _ = P := h2

lemma lC {M : Matrix (Fin m) (Fin n) ℝ} {P : Matrix (Fin n) (Fin m) ℝ}
    (h : IsMoorePenroseInverse M P) : Mᵀ * M * P = Mᵀ := by
  obtain ⟨h1, _, h3, _⟩ := h
  calc Mᵀ * M * P = Mᵀ * (M * P)ᵀ := by rw [h3, Matrix.mul_assoc]
    _ = (M * P * M)ᵀ := by rw [transpose_mul (M * P) M]
    _ = Mᵀ := by rw [h1]

lemma lD {M : Matrix (Fin m) (Fin n) ℝ} {P : Matrix (Fin n) (Fin m) ℝ}
    (h : IsMoorePenroseInverse M P) : P * M * Mᵀ = Mᵀ := by
  obtain ⟨h1, _, _, h4⟩ := h
  calc P * M * Mᵀ = (P * M)ᵀ * Mᵀ := by rw [h4]
    _ = (M * (P * M))ᵀ := by rw [transpose_mul M (P * M)]
    _ = Mᵀ := by rw [← Matrix.mul_assoc, h1]

lemma uniq {M : Matrix (Fin m) (Fin n) ℝ} {P Q : Matrix (Fin n) (Fin m) ℝ}
    (hP : IsMoorePenroseInverse M P) (hQ : IsMoorePenroseInverse M Q) : P = Q := by
  have e1 : P = P * M * Q := by
    calc P = P * Pᵀ * Mᵀ := (lA hP).symm
      _ = P * Pᵀ * (Mᵀ * M * Q) := by rw [lC hQ]
      _ = (P * Pᵀ * Mᵀ) * M * Q := by simp only [Matrix.mul_assoc]
      _ = P * M * Q := by rw [lA hP]
  have e2 : Q = P * M * Q := by
    calc Q = Mᵀ * Qᵀ * Q := (lB hQ).symm
      _ = (P * M * Mᵀ) * Qᵀ * Q := by rw [lD hP]
      _ = P * M * (Mᵀ * Qᵀ * Q) := by simp only [Matrix.mul_assoc]
      _ = P * M * Q := by rw [lB hQ]
  exact e1.trans e2.symm

lemma tr {M : Matrix (Fin m) (Fin n) ℝ} {P : Matrix (Fin n) (Fin m) ℝ}
    (h : IsMoorePenroseInverse M P) : IsMoorePenroseInverse Mᵀ Pᵀ := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [Matrix.mul_assoc, ← transpose_mul, ← transpose_mul, h1]
  · rw [Matrix.mul_assoc, ← transpose_mul, ← transpose_mul, h2]
  · rw [← transpose_mul, transpose_transpose, h4]
  · rw [← transpose_mul, transpose_transpose, h3]

lemma range_mul_le {k : ℕ} (B : Matrix (Fin m) (Fin n) ℝ) (C : Matrix (Fin n) (Fin k) ℝ) :
    LinearMap.range (Matrix.toLin' (B * C)) ≤ LinearMap.range (Matrix.toLin' B) := by
  rw [Matrix.toLin'_mul]
  exact LinearMap.range_comp_le_range _ _

end Aux_NIQH_A1

open NumInvQH.Oblique Aux_NIQH_A1 in
theorem solution :
    (∀ {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (X : Matrix (Fin n) (Fin m) ℝ)
        (Y : Matrix (Fin m) (Fin n) ℝ),
        LocalDistanceNetwork.IsMoorePenroseInverse A X →
        LocalDistanceNetwork.IsMoorePenroseInverse Aᵀ Y → Y = Xᵀ) ∧
    (∀ {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (X : Matrix (Fin n) (Fin m) ℝ),
        LocalDistanceNetwork.IsMoorePenroseInverse A X →
        LinearMap.range (Matrix.toLin' X) = LinearMap.range (Matrix.toLin' Aᵀ)) ∧
    (∀ {n p : ℕ} (U : Matrix (Fin n) (Fin n) ℝ) (V : Matrix (Fin p) (Fin n) ℝ)
        (X : Matrix (Fin n) (Fin p) ℝ),
        U * U = U → Uᵀ = U →
        LocalDistanceNetwork.IsMoorePenroseInverse (V * U) X → U * X = X) ∧
    (∀ {n p : ℕ} (V : Matrix (Fin n) (Fin n) ℝ) (U : Matrix (Fin n) (Fin p) ℝ)
        (X : Matrix (Fin p) (Fin n) ℝ),
        V * V = V → Vᵀ = V →
        LocalDistanceNetwork.IsMoorePenroseInverse (V * U) X → X * V = X) ∧
    (∀ {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (X : Matrix (Fin n) (Fin m) ℝ)
        (Y : Matrix (Fin m) (Fin m) ℝ) (Z : Matrix (Fin n) (Fin n) ℝ),
        LocalDistanceNetwork.IsMoorePenroseInverse A X →
        LocalDistanceNetwork.IsMoorePenroseInverse (A * Aᵀ) Y →
        LocalDistanceNetwork.IsMoorePenroseInverse (Aᵀ * A) Z →
        X = Aᵀ * Y ∧ X = Z * Aᵀ) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro m n A X Y hX hY
    exact uniq hY (tr hX)
  · intro m n A X hX
    apply le_antisymm
    · rw [← lB hX, Matrix.mul_assoc]
      exact range_mul_le _ _
    · rw [← lD hX, Matrix.mul_assoc]
      exact range_mul_le _ _
  · intro n p U V X hUU hUt hX
    have hb := lB hX
    rw [transpose_mul, hUt] at hb
    calc U * X = U * (U * Vᵀ * Xᵀ * X) := by rw [hb]
      _ = (U * U) * Vᵀ * Xᵀ * X := by simp only [Matrix.mul_assoc]
      _ = X := by rw [hUU, hb]
  · intro n p V U X hVV hVt hX
    have ha := lA hX
    rw [transpose_mul, hVt] at ha
    calc X * V = (X * Xᵀ * (Uᵀ * V)) * V := by rw [ha]
      _ = X * Xᵀ * Uᵀ * (V * V) := by simp only [Matrix.mul_assoc]
      _ = X := by rw [hVV, Matrix.mul_assoc (X * Xᵀ)]; exact ha
  · intro m n A X Y Z hX hY hZ
    have hBt : (A * Aᵀ)ᵀ = A * Aᵀ := by rw [transpose_mul, transpose_transpose]
    have hCt : (Aᵀ * A)ᵀ = Aᵀ * A := by rw [transpose_mul, transpose_transpose]
    have hYs : Yᵀ = Y := by
      have := tr hY
      rw [hBt] at this
      exact uniq this hY
    have hZs : Zᵀ = Z := by
      have := tr hZ
      rw [hCt] at this
      exact uniq this hZ
    obtain ⟨hY1, hY2, hY3, hY4⟩ := hY
    obtain ⟨hZ1, hZ2, hZ3, hZ4⟩ := hZ
    constructor
    · -- A Aᵀ Y A = A
      set E := A * Aᵀ * Y * A - A with hE
      have hEt : Eᵀ = Aᵀ * Y * (A * Aᵀ) - Aᵀ := by
        rw [hE]
        simp only [transpose_sub, transpose_mul, transpose_transpose, hYs, Matrix.mul_assoc]
      have t1 : (A * Aᵀ * Y * A) * (Aᵀ * Y * (A * Aᵀ)) = A * Aᵀ := by
        calc _ = (A * Aᵀ * Y * (A * Aᵀ)) * Y * (A * Aᵀ) := by simp only [Matrix.mul_assoc]
          _ = A * Aᵀ := by rw [hY1, hY1]
      have t2 : (A * Aᵀ * Y * A) * Aᵀ = A * Aᵀ := by
        calc _ = A * Aᵀ * Y * (A * Aᵀ) := by simp only [Matrix.mul_assoc]
          _ = _ := hY1
      have t3 : A * (Aᵀ * Y * (A * Aᵀ)) = A * Aᵀ := by
        calc _ = A * Aᵀ * Y * (A * Aᵀ) := by simp only [Matrix.mul_assoc]
          _ = _ := hY1
      have hEE : E * Eᵀ = 0 := by
        rw [hEt, hE, Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_sub, t1, t2, t3]
        simp
      have hE0 : E = 0 := by
        have h := (conjTranspose_mul_self_eq_zero (A := Eᵀ)).mp (by
          rw [conjTranspose_eq_transpose_of_trivial, transpose_transpose]; exact hEE)
        rw [← transpose_transpose E, h, transpose_zero]
      have hA1 : A * (Aᵀ * Y) * A = A := by
        have h0 : A * Aᵀ * Y * A - A = 0 := by rw [← hE]; exact hE0
        have := sub_eq_zero.mp h0
        calc A * (Aᵀ * Y) * A = A * Aᵀ * Y * A := by simp only [Matrix.mul_assoc]
          _ = A := this
      have hMP : LocalDistanceNetwork.IsMoorePenroseInverse A (Aᵀ * Y) := by
        refine ⟨hA1, ?_, ?_, ?_⟩
        · calc Aᵀ * Y * A * (Aᵀ * Y) = Aᵀ * (Y * (A * Aᵀ) * Y) := by simp only [Matrix.mul_assoc]
            _ = Aᵀ * Y := by rw [hY2]
        · rw [← Matrix.mul_assoc, hY3]
        · rw [transpose_mul, transpose_mul, transpose_transpose, hYs, Matrix.mul_assoc]
      exact uniq hX hMP
    · -- A Z Aᵀ A = A
      set F := A * Z * Aᵀ * A - A with hF
      have hFt : Fᵀ = Aᵀ * A * Z * Aᵀ - Aᵀ := by
        rw [hF]
        simp only [transpose_sub, transpose_mul, transpose_transpose, hZs, Matrix.mul_assoc]
      have t1 : (Aᵀ * A * Z * Aᵀ) * (A * Z * Aᵀ * A) = Aᵀ * A := by
        calc _ = (Aᵀ * A * Z * (Aᵀ * A)) * Z * (Aᵀ * A) := by simp only [Matrix.mul_assoc]
          _ = Aᵀ * A := by rw [hZ1, hZ1]
      have t2 : (Aᵀ * A * Z * Aᵀ) * A = Aᵀ * A := by
        calc _ = Aᵀ * A * Z * (Aᵀ * A) := by simp only [Matrix.mul_assoc]
          _ = _ := hZ1
      have t3 : Aᵀ * (A * Z * Aᵀ * A) = Aᵀ * A := by
        calc _ = Aᵀ * A * Z * (Aᵀ * A) := by simp only [Matrix.mul_assoc]
          _ = _ := hZ1
      have hFF : Fᵀ * F = 0 := by
        rw [hFt, hF, Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_sub, t1, t2, t3]
        simp
      have hF0 : F = 0 := by
        apply (conjTranspose_mul_self_eq_zero (A := F)).mp
        rw [conjTranspose_eq_transpose_of_trivial]; exact hFF
      have hA1 : A * (Z * Aᵀ) * A = A := by
        have h0 : A * Z * Aᵀ * A - A = 0 := by rw [← hF]; exact hF0
        have := sub_eq_zero.mp h0
        calc A * (Z * Aᵀ) * A = A * Z * Aᵀ * A := by simp only [Matrix.mul_assoc]
          _ = A := this
      have hMP : LocalDistanceNetwork.IsMoorePenroseInverse A (Z * Aᵀ) := by
        refine ⟨hA1, ?_, ?_, ?_⟩
        · calc Z * Aᵀ * A * (Z * Aᵀ) = (Z * (Aᵀ * A) * Z) * Aᵀ := by simp only [Matrix.mul_assoc]
            _ = Z * Aᵀ := by rw [hZ2]
        · rw [transpose_mul, transpose_mul, transpose_transpose, hZs, Matrix.mul_assoc]
        · rw [Matrix.mul_assoc, hZ4]
      exact uniq hX hMP
