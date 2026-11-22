-- Prove2me | solution 1 for Matrix.charpolyRev_of_transpose_mul_mul_eq_smul
-- status  : ACCEPTED   (prove)
-- author  : @emmgaml
-- created : 2026-11-21T23:46:22.902458+00:00
-- url     : https://prove2.me/submissions/b43ea0d0-1dd3-4add-a835-3527c121a88c

import Mathlib

namespace WCAux

open Matrix

/-- A determinant identity behind Poincaré duality: if `Φᵀ G Ψ = μ G` with `G` invertible,
then `det Φ · det (1 - x Ψ) = det (Φ - x μ)`. -/
theorem det_mul_det_one_sub_smul {R : Type*} [CommRing R] {m n : Type*} [Fintype m]
    [DecidableEq m] [Fintype n] [DecidableEq n] (Φ : Matrix m m R) (Ψ : Matrix n n R)
    (G : Matrix m n R) (H : Matrix n m R) (hGH : G * H = 1) (hHG : H * G = 1) (μ x : R)
    (h : Φ.transpose * G * Ψ = μ • G) :
    Φ.det * (1 - x • Ψ).det = (Φ - (x * μ) • (1 : Matrix m m R)).det := by
  have e1 : (1 : Matrix n n R) - x • Ψ = 1 - H * (x • (G * Ψ)) := by
    rw [Matrix.mul_smul, ← Matrix.mul_assoc, hHG, Matrix.one_mul]
  have e2 : Φ.transpose * (1 - (x • (G * Ψ)) * H) =
      (Φ - (x * μ) • (1 : Matrix m m R)).transpose := by
    rw [Matrix.mul_sub, Matrix.mul_one, Matrix.smul_mul, Matrix.mul_smul, ← Matrix.mul_assoc,
      ← Matrix.mul_assoc, h, Matrix.smul_mul, hGH, smul_smul, Matrix.transpose_sub,
      Matrix.transpose_smul, Matrix.transpose_one]
  rw [e1, Matrix.det_one_sub_mul_comm, ← Matrix.det_transpose Φ, ← Matrix.det_mul, e2,
    Matrix.det_transpose]

/-- **Characteristic polynomials of endomorphisms adjoint under a perfect pairing**
(Hartshorne, *Algebraic Geometry*, Appendix C, Lemma 4.3, in matrix form).
If `Φᵀ G Ψ = λ G` with `G` invertible and `λ ≠ 0`, then `Φ` is invertible and
`det Φ · det (1 - T Ψ) = (-1)^r · χ_Φ(λ T)`, where `χ_Φ(T) = det (T - Φ)` and `r` is the size
of `Φ`. -/
theorem charpolyRev_of_pairing {K : Type*} [Field K] {m n : Type*} [Fintype m] [DecidableEq m]
    [Fintype n] [DecidableEq n] (Φ : Matrix m m K) (Ψ : Matrix n n K) (G : Matrix m n K)
    (H : Matrix n m K) (hGH : G * H = 1) (hHG : H * G = 1) (lam : K) (hlam : lam ≠ 0)
    (h : Φ.transpose * G * Ψ = lam • G) :
    Φ.det ≠ 0 ∧ Φ.det * Ψ.det = lam ^ Fintype.card m ∧
    Polynomial.C Φ.det * Ψ.charpolyRev =
      (-1) ^ Fintype.card m * Φ.charpoly.comp (Polynomial.C lam * Polynomial.X) := by
  have hdd : Φ.det * Ψ.det = lam ^ Fintype.card m := by
    have h1 : Φ.transpose * (G * Ψ * H) = lam • (1 : Matrix m m K) := by
      rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, h, Matrix.smul_mul, hGH]
    have h2 := congrArg Matrix.det h1
    rw [Matrix.det_mul, Matrix.det_transpose, Matrix.det_conj_of_mul_eq_one hGH hHG,
      Matrix.det_smul, Matrix.det_one, mul_one] at h2
    exact h2
  refine ⟨?_, hdd, ?_⟩
  · intro h0
    rw [h0, zero_mul] at hdd
    exact pow_ne_zero _ hlam hdd.symm
  · have hGH' : G.map (Polynomial.C : K →+* Polynomial K) *
        H.map (Polynomial.C : K →+* Polynomial K) = 1 := by
      rw [← Matrix.map_mul, hGH]
      exact Matrix.map_one _ (map_zero _) (map_one _)
    have hHG' : H.map (Polynomial.C : K →+* Polynomial K) *
        G.map (Polynomial.C : K →+* Polynomial K) = 1 := by
      rw [← Matrix.map_mul, hHG]
      exact Matrix.map_one _ (map_zero _) (map_one _)
    have h' : (Φ.map (Polynomial.C : K →+* Polynomial K)).transpose *
        G.map (Polynomial.C : K →+* Polynomial K) * Ψ.map (Polynomial.C : K →+* Polynomial K) =
        Polynomial.C lam • G.map (Polynomial.C : K →+* Polynomial K) := by
      rw [← Matrix.transpose_map, ← Matrix.map_mul, ← Matrix.map_mul, h]
      ext i j : 1
      simp
    have key := det_mul_det_one_sub_smul _ _ _ _ hGH' hHG' (Polynomial.C lam) Polynomial.X h'
    have hdet : (Φ.map (Polynomial.C : K →+* Polynomial K)).det = Polynomial.C Φ.det :=
      (RingHom.map_det _ _).symm
    have hcomp : Φ.charpoly.comp (Polynomial.C lam * Polynomial.X) =
        ((Polynomial.C lam * Polynomial.X) • (1 : Matrix m m (Polynomial K)) -
          Φ.map (Polynomial.C : K →+* Polynomial K)).det := by
      rw [← Polynomial.coe_compRingHom_apply, Matrix.charpoly, RingHom.map_det]
      congr 1
      ext i j : 1
      by_cases hij : i = j
      · subst hij
        simp [Matrix.charmatrix_apply]
      · simp [Matrix.charmatrix_apply, hij, Matrix.one_apply]
    rw [hdet] at key
    rw [Matrix.charpolyRev, key, hcomp, ← Matrix.det_neg]
    congr 1
    rw [mul_comm Polynomial.X (Polynomial.C lam), neg_sub]

end WCAux

theorem solution {K : Type*} [Field K] {m n : Type*}
    [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]
    (Φ : Matrix m m K) (Ψ : Matrix n n K) (G : Matrix m n K) (H : Matrix n m K)
    (hGH : G * H = 1) (hHG : H * G = 1) (lam : K) (hlam : lam ≠ 0)
    (h : Φ.transpose * G * Ψ = lam • G) :
    Φ.det ≠ 0 ∧ Φ.det * Ψ.det = lam ^ Fintype.card m ∧
    Polynomial.C Φ.det * Ψ.charpolyRev =
      (-1) ^ Fintype.card m * Φ.charpoly.comp (Polynomial.C lam * Polynomial.X) :=
  WCAux.charpolyRev_of_pairing Φ Ψ G H hGH hHG lam hlam h
