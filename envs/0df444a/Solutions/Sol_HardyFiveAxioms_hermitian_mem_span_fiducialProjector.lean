-- Prove2me | solution 1 for HardyFiveAxioms.hermitian_mem_span_fiducialProjector
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-03T12:58:08.541826+00:00
-- url     : https://prove2.me/submissions/966bd59f-d939-431e-a3e7-fca29fb9ef43

import Mathlib
import Definitions.Def_hardy2001_projectors

set_option autoImplicit false

namespace HardyC50

open HardyFiveAxioms

lemma cc : ((1 / Real.sqrt 2 : ℝ) : ℂ) * ((1 / Real.sqrt 2 : ℝ) : ℂ) = (1 / 2 : ℂ) := by
  rw [← Complex.ofReal_mul]
  have h : (1 / Real.sqrt 2) * (1 / Real.sqrt 2) = (1 / 2 : ℝ) := by
    rw [div_mul_div_comm, one_mul, Real.mul_self_sqrt (by norm_num)]
  rw [h]; push_cast; ring

lemma star_c : star ((1 / Real.sqrt 2 : ℝ) : ℂ) = ((1 / Real.sqrt 2 : ℝ) : ℂ) :=
  Complex.conj_ofReal _

lemma star_ket {N : ℕ} (n : Fin N) : star (ket n) = ket n := by
  ext i
  simp only [ket, Pi.star_apply, Pi.single_apply]
  split_ifs <;> simp

lemma E_def {N : ℕ} (m n : Fin N) :
    Matrix.vecMulVec (ket m) (ket n) = Matrix.single m n (1 : ℂ) :=
  (Matrix.single_eq_single_vecMulVec_single m n).symm

lemma rsmul {N : ℕ} (r : ℝ) (M : Matrix (Fin N) (Fin N) ℂ) : r • M = (r : ℂ) • M := by
  ext i j
  simp [Complex.real_smul]

lemma proj_ket {N : ℕ} (m : Fin N) : proj (ket m) = Matrix.single m m (1 : ℂ) := by
  rw [proj, star_ket, E_def]

lemma proj_ketX {N : ℕ} (m n : Fin N) :
    proj (ketX m n) = (1 / 2 : ℂ) • (Matrix.single m m 1 + Matrix.single m n 1
      + Matrix.single n m 1 + Matrix.single n n 1) := by
  rw [proj, ketX, star_smul, star_c, star_add, star_ket, star_ket, Matrix.smul_vecMulVec,
    Matrix.vecMulVec_smul, smul_smul, cc]
  simp only [Matrix.add_vecMulVec, Matrix.vecMulVec_add, E_def]
  abel

lemma proj_ketY {N : ℕ} (m n : Fin N) :
    proj (ketY m n) = (1 / 2 : ℂ) • (Matrix.single m m 1 + Matrix.single n n 1
      - Complex.I • Matrix.single m n 1 + Complex.I • Matrix.single n m 1) := by
  have hs : star (Complex.I • ket (N := N) n) = (-Complex.I) • ket n := by
    rw [star_smul, star_ket, Complex.star_def, Complex.conj_I]
  rw [proj, ketY, star_smul, star_c, star_add, star_ket, hs,
    Matrix.smul_vecMulVec, Matrix.vecMulVec_smul, smul_smul, cc]
  simp only [Matrix.add_vecMulVec, Matrix.vecMulVec_add, Matrix.smul_vecMulVec,
    Matrix.vecMulVec_smul, E_def]
  match_scalars <;>
    first
    | ring1
    | linear_combination (-1 / 2 : ℂ) * Complex.I_sq
    | linear_combination (1 / 2 : ℂ) * Complex.I_sq

lemma single_eq_smul {N : ℕ} (i j : Fin N) (w : ℂ) :
    Matrix.single i j w = w • Matrix.single i j (1 : ℂ) := by
  rw [Matrix.smul_single, smul_eq_mul, mul_one]

lemma key_lt {N : ℕ} (m n : Fin N) (hlt : m < n) (z : ℂ) :
    Matrix.single m n z + Matrix.single n m ((starRingEnd ℂ) z) ∈
      Submodule.span ℝ (Set.range (fiducialProjector (N := N))) := by
  obtain ⟨a, b, rfl⟩ : ∃ a b : ℝ, z = (a : ℂ) + (b : ℂ) * Complex.I :=
    ⟨z.re, z.im, (Complex.re_add_im z).symm⟩
  set S := Submodule.span ℝ (Set.range (fiducialProjector (N := N)))
  have hX : fiducialProjector (Sum.inr (⟨(m, n), hlt⟩, false)) ∈ S :=
    Submodule.subset_span ⟨_, rfl⟩
  have hY : fiducialProjector (Sum.inr (⟨(m, n), hlt⟩, true)) ∈ S :=
    Submodule.subset_span ⟨_, rfl⟩
  have hDm : fiducialProjector (N := N) (Sum.inl m) ∈ S := Submodule.subset_span ⟨_, rfl⟩
  have hDn : fiducialProjector (N := N) (Sum.inl n) ∈ S := Submodule.subset_span ⟨_, rfl⟩
  have heq : Matrix.single m n ((a : ℂ) + (b : ℂ) * Complex.I)
      + Matrix.single n m ((starRingEnd ℂ) ((a : ℂ) + (b : ℂ) * Complex.I)) =
      (2 * a) • fiducialProjector (Sum.inr (⟨(m, n), hlt⟩, false))
      + (b - a) • fiducialProjector (N := N) (Sum.inl m)
      + (b - a) • fiducialProjector (N := N) (Sum.inl n)
      - (2 * b) • fiducialProjector (Sum.inr (⟨(m, n), hlt⟩, true)) := by
    simp only [fiducialProjector, proj_ket, proj_ketX, proj_ketY, rsmul]
    rw [single_eq_smul m n, single_eq_smul n m]
    simp only [map_add, map_mul, Complex.conj_ofReal, Complex.conj_I]
    push_cast
    module
  rw [heq]
  exact S.sub_mem (S.add_mem (S.add_mem (S.smul_mem _ hX) (S.smul_mem _ hDm))
    (S.smul_mem _ hDn)) (S.smul_mem _ hY)

lemma key {N : ℕ} (m n : Fin N) (z : ℂ) :
    Matrix.single m n z + Matrix.single n m ((starRingEnd ℂ) z) ∈
      Submodule.span ℝ (Set.range (fiducialProjector (N := N))) := by
  rcases lt_trichotomy m n with h | h | h
  · exact key_lt m n h z
  · subst h
    have hD : fiducialProjector (N := N) (Sum.inl m) ∈
        Submodule.span ℝ (Set.range (fiducialProjector (N := N))) :=
      Submodule.subset_span ⟨_, rfl⟩
    have heq : Matrix.single m m z + Matrix.single m m ((starRingEnd ℂ) z) =
        (2 * z.re) • fiducialProjector (N := N) (Sum.inl m) := by
      simp only [fiducialProjector, proj_ket, rsmul]
      rw [← Matrix.single_add, single_eq_smul m m (z + _), Complex.add_conj]
    rw [heq]
    exact Submodule.smul_mem _ _ hD
  · have := key_lt n m h ((starRingEnd ℂ) z)
    rw [Complex.conj_conj, add_comm] at this
    exact this

end HardyC50

open HardyFiveAxioms in
theorem solution (N : ℕ) (A : Matrix (Fin N) (Fin N) ℂ)
    (hA : A.IsHermitian) :
    A ∈ Submodule.span ℝ (Set.range (fiducialProjector (N := N))) := by
  have hsum : (2 : ℝ) • A = ∑ i : Fin N, ∑ j : Fin N,
      (Matrix.single i j (A i j) + Matrix.single j i ((starRingEnd ℂ) (A i j))) := by
    simp only [Finset.sum_add_distrib]
    have h1 : ∑ i : Fin N, ∑ j : Fin N, Matrix.single j i ((starRingEnd ℂ) (A i j)) = A := by
      have : ∀ i j : Fin N, (starRingEnd ℂ) (A i j) = A j i := fun i j => hA.apply j i
      simp only [this]
      rw [Finset.sum_comm]
      exact (Matrix.matrix_eq_sum_single A).symm
    rw [h1, ← Matrix.matrix_eq_sum_single A, two_smul]
  have hA' : A = (1 / 2 : ℝ) • ((2 : ℝ) • A) := by
    rw [smul_smul]; norm_num
  rw [hA', hsum]
  refine Submodule.smul_mem _ _ (Submodule.sum_mem _ fun i _ => Submodule.sum_mem _ fun j _ => ?_)
  exact HardyC50.key i j (A i j)
