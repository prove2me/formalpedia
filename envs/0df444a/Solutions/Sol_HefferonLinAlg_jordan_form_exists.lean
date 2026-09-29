-- Prove2me | solution 1 for HefferonLinAlg.jordan_form_exists
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-08-07T15:08:21.660363+00:00
-- url     : https://prove2.me/submissions/44d5d463-2d23-47f4-925f-099af167ce5d

import Definitions.Def_HefferonLinAlg_jordan
import Theorems.Thm_HefferonLinAlg_jordan_string_basis
import Theorems.Thm_HefferonLinAlg_change_of_basis_gives_similar_matrices

open Matrix
open HefferonLinAlg

private theorem toMatrix_reindex_basis {K : Type*} [Field K] {n : ℕ}
    {J : Type*} [Fintype J] [DecidableEq J] {V : Type*} [AddCommGroup V] [Module K V]
    (b : Module.Basis J K V) (e : Fin n ≃ J) (g : V →ₗ[K] V) :
    LinearMap.toMatrix (b.reindex e.symm) (b.reindex e.symm) g
      = Matrix.reindex e.symm e.symm (LinearMap.toMatrix b b g) := by
  ext i j
  simp [LinearMap.toMatrix_apply, Module.Basis.reindex_apply,
    Matrix.reindex_apply, Matrix.submatrix_apply]

private theorem jsigma_eq_iff {k : ℕ} {sz : Fin k → ℕ} (i j : Fin k)
    (x : Fin (sz i)) (y : Fin (sz j)) :
    ((⟨i, x⟩ : Σ i : Fin k, Fin (sz i)) = ⟨j, y⟩) ↔ (i = j ∧ (x : ℕ) = (y : ℕ)) := by
  rw [Sigma.mk.injEq]
  constructor
  · rintro ⟨rfl, h⟩
    exact ⟨rfl, congrArg Fin.val (eq_of_heq h)⟩
  · rintro ⟨rfl, h⟩
    exact ⟨rfl, heq_of_eq (Fin.ext h)⟩

theorem solution {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) : HasJordanForm A := by
  classical
  obtain ⟨k, sz, lam, b, hpos, hstr⟩ :=
    HefferonLinAlg.jordan_string_basis (Matrix.toLinAlgEquiv' A)
  refine ⟨k, sz, lam, hpos, ?_⟩
  have hcard : Fintype.card (jordanIndex sz) = n := by
    have h := Module.finrank_eq_card_basis b
    rw [Module.finrank_pi, Fintype.card_fin] at h
    exact h.symm
  refine ⟨(Fintype.equivFinOfCardEq hcard).symm, ?_⟩
  set e : Fin n ≃ jordanIndex sz := (Fintype.equivFinOfCardEq hcard).symm with he
  obtain ⟨P, hP, hPeq⟩ := HefferonLinAlg.change_of_basis_gives_similar_matrices
      (Pi.basisFun ℂ (Fin n)) (b.reindex e.symm) (Matrix.toLinAlgEquiv' A)
  refine ⟨P, hP, ?_⟩
  have hBA : LinearMap.toMatrix (Pi.basisFun ℂ (Fin n)) (Pi.basisFun ℂ (Fin n))
      (Matrix.toLinAlgEquiv' A) = A := by
    rw [LinearMap.toMatrix_eq_toMatrix']
    exact LinearMap.toMatrix'_toLin' A
  rw [hBA] at hPeq
  rw [← hPeq, toMatrix_reindex_basis]
  congr 1
  ext p q
  obtain ⟨i, x⟩ := p
  obtain ⟨j, y⟩ := q
  rw [LinearMap.toMatrix_apply, hstr]
  by_cases hij : i = j
  · subst hij
    rw [jordanMatrix_apply_same, jordanBlock_apply]
    by_cases hy : (y : ℕ) + 1 < sz i
    · rw [dif_pos hy]
      simp only [map_add, Finsupp.add_apply, map_smul, Finsupp.smul_apply,
        Module.Basis.repr_self, Finsupp.single_apply, smul_eq_mul, jsigma_eq_iff,
        Fin.ext_iff, true_and, and_true, eq_self_iff_true]
      split_ifs with h1 h2 h3 <;> first
        | (exfalso; omega)
        | simp
        | ring
    · rw [dif_neg hy, add_zero]
      have hx : ¬ ((x : ℕ) = (y : ℕ) + 1) := by
        have := x.2
        omega
      simp only [map_add, Finsupp.add_apply, map_smul, Finsupp.smul_apply,
        Module.Basis.repr_self, Finsupp.single_apply, smul_eq_mul, jsigma_eq_iff,
        Fin.ext_iff, true_and, Finsupp.coe_zero, Pi.zero_apply, add_zero]
      split_ifs with h1 h2 <;> first
        | (exfalso; omega)
        | simp
        | ring
  · rw [jordanMatrix_apply_ne _ _ _ _ hij]
    by_cases hy : (y : ℕ) + 1 < sz j
    · rw [dif_pos hy]
      simp only [map_add, Finsupp.add_apply, map_smul, Finsupp.smul_apply,
        Module.Basis.repr_self, Finsupp.single_apply, smul_eq_mul, jsigma_eq_iff]
      rw [if_neg (by tauto), if_neg (by tauto)]
      ring
    · rw [dif_neg hy, add_zero]
      simp only [map_add, Finsupp.add_apply, map_smul, Finsupp.smul_apply,
        Module.Basis.repr_self, Finsupp.single_apply, smul_eq_mul, jsigma_eq_iff,
        Finsupp.coe_zero, Pi.zero_apply, add_zero]
      rw [if_neg (by tauto)]
      ring
