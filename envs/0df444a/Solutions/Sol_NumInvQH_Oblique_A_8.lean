-- Prove2me | solution 1 for NumInvQH.Oblique.A_8
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-26T15:48:57.141249+00:00
-- url     : https://prove2.me/submissions/57abb018-9f19-4f81-9eca-7d8e2f418e39

import Mathlib
import Definitions.Def_LocalDistanceNetwork_GLS
import Definitions.Def_NumInvQH_Oblique_Basic

open Matrix

namespace Aux_NIQH_A8

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

lemma gram_right {A : Matrix (Fin m) (Fin n) ℝ} {X : Matrix (Fin n) (Fin m) ℝ}
    {Z : Matrix (Fin n) (Fin n) ℝ} (hX : IsMoorePenroseInverse A X)
    (hZ : IsMoorePenroseInverse (Aᵀ * A) Z) : X = Z * Aᵀ := by
  have hCt : (Aᵀ * A)ᵀ = Aᵀ * A := by rw [transpose_mul, transpose_transpose]
  have hZs : Zᵀ = Z := by
    have := tr hZ
    rw [hCt] at this
    exact uniq this hZ
  obtain ⟨hZ1, hZ2, hZ3, hZ4⟩ := hZ
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
  have hMP : IsMoorePenroseInverse A (Z * Aᵀ) := by
    refine ⟨hA1, ?_, ?_, ?_⟩
    · calc Z * Aᵀ * A * (Z * Aᵀ) = (Z * (Aᵀ * A) * Z) * Aᵀ := by simp only [Matrix.mul_assoc]
        _ = Z * Aᵀ := by rw [hZ2]
    · rw [transpose_mul, transpose_mul, transpose_transpose, hZs, Matrix.mul_assoc]
    · rw [Matrix.mul_assoc, hZ4]
  exact uniq hX hMP

end Aux_NIQH_A8

open NumInvQH.Oblique Aux_NIQH_A8 in
theorem solution {k n : ℕ}
    (A : Matrix (Fin k) (Fin n) ℝ) (C : Matrix (Fin n) (Fin n) ℝ) (hC : C.PosSemidef)
    (R : Matrix (Fin n) (Fin n) ℝ) (hR : R.PosSemidef) (hRC : R * R = C)
    (Ap : Matrix (Fin n) (Fin k) ℝ)
    (hAp : LocalDistanceNetwork.IsMoorePenroseInverse A Ap)
    (J : Matrix (Fin n) (Fin n) ℝ)
    (hJ : LocalDistanceNetwork.IsMoorePenroseInverse ((1 - Ap * A) * C * (1 - Ap * A)) J)
    (K : Matrix (Fin n) (Fin n) ℝ)
    (hK : LocalDistanceNetwork.IsMoorePenroseInverse (R * (1 - Ap * A)) K) :
    let M := 1 - Ap * A
    J * C = M * J * M * C ∧
      J * C = M * K * R ∧
      J * C = K * R ∧
      J * C * J = J := by
  intro M
  have hCt : Cᵀ = C := by
    have := hC.1; rw [IsHermitian, conjTranspose_eq_transpose_of_trivial] at this; exact this
  have hRt : Rᵀ = R := by
    have := hR.1; rw [IsHermitian, conjTranspose_eq_transpose_of_trivial] at this; exact this
  have hPP : Ap * A * (Ap * A) = Ap * A := by rw [← Matrix.mul_assoc, hAp.2.1]
  have hMt : Mᵀ = M := by
    simp only [M, transpose_sub, transpose_one, hAp.2.2.2]
  have hMM : M * M = M := by
    simp only [M, Matrix.sub_mul, Matrix.mul_sub, Matrix.one_mul, Matrix.mul_one, hPP]
    abel
  have hD : (M * C * M)ᵀ = M * C * M := by
    rw [transpose_mul, transpose_mul, hMt, hCt, Matrix.mul_assoc]
  have hJ' : LocalDistanceNetwork.IsMoorePenroseInverse (M * C * M) J := hJ
  have hJM : J * M = J := by
    have h := lA hJ'
    rw [hD] at h
    calc J * M = (J * Jᵀ * (M * C * M)) * M := by rw [h]
      _ = J * Jᵀ * (M * C * (M * M)) := by simp only [Matrix.mul_assoc]
      _ = J := by rw [hMM, h]
  have hMJ : M * J = J := by
    have h := lB hJ'
    rw [hD] at h
    calc M * J = M * ((M * C * M) * Jᵀ * J) := by rw [h]
      _ = ((M * M) * C * M) * Jᵀ * J := by simp only [Matrix.mul_assoc]
      _ = J := by rw [hMM, h]
  have hMJM : M * J * M = J := by rw [hMJ, hJM]
  -- K = J * M * R
  have hK' : LocalDistanceNetwork.IsMoorePenroseInverse (R * M) K := hK
  have hgram : (R * M)ᵀ * (R * M) = M * C * M := by
    rw [transpose_mul, hRt, hMt, ← hRC]; simp only [Matrix.mul_assoc]
  have hJg : LocalDistanceNetwork.IsMoorePenroseInverse ((R * M)ᵀ * (R * M)) J := by rw [hgram]; exact hJ'
  have hKeq : K = J * (R * M)ᵀ := gram_right hK' hJg
  rw [transpose_mul, hRt, hMt] at hKeq
  have hKR : K * R = J * C := by
    rw [hKeq, ← hRC]
    calc J * (M * R) * R = (J * M) * (R * R) := by simp only [Matrix.mul_assoc]
      _ = J * (R * R) := by rw [hJM]
  refine ⟨?_, ?_, hKR.symm, ?_⟩
  · rw [hMJM]
  · rw [Matrix.mul_assoc M K R, hKR, ← Matrix.mul_assoc, hMJ]
  · obtain ⟨_, h2, _, _⟩ := hJ'
    calc J * C * J = (J * M) * C * (M * J) := by rw [hJM, hMJ]
      _ = J * (M * C * M) * J := by simp only [Matrix.mul_assoc]
      _ = J := h2
