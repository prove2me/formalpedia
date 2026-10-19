-- Prove2me | solution 1 for Hadamard_Conjecture_paley_sylvester_case
-- status  : ACCEPTED   (prove)
-- author  : @ronr
-- created : 2026-09-05T22:15:14.80715+00:00
-- url     : https://prove2.me/submissions/285a3599-d8bb-4b7b-9c6b-d7c4dd114124

import Mathlib
import Theorems.Thm_Paley_construction_I
import Theorems.Thm_Hadamard_matrix_kronecker_product

open Matrix

/-- Transport a `±1`-entried orthogonal matrix across an index equivalence. -/
private lemma transport_hadamard {ι ι' : Type} [Fintype ι] [DecidableEq ι] [Fintype ι']
    [DecidableEq ι'] (e : ι' ≃ ι) (M : Matrix ι ι ℝ) (c : ℝ)
    (hpm : ∀ i j, M i j = 1 ∨ M i j = -1)
    (horth : M * Mᵀ = c • (1 : Matrix ι ι ℝ)) :
    (∀ i j, (M.submatrix e e) i j = 1 ∨ (M.submatrix e e) i j = -1) ∧
      (M.submatrix e e) * (M.submatrix e e)ᵀ = c • (1 : Matrix ι' ι' ℝ) := by
  refine ⟨fun i j => hpm (e i) (e j), ?_⟩
  apply Matrix.ext
  intro i j
  have hlhs : ((M.submatrix e e) * (M.submatrix e e)ᵀ) i j = (M * Mᵀ) (e i) (e j) := by
    simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.submatrix_apply]
    exact Equiv.sum_comp e (fun l => M (e i) l * M (e j) l)
  rw [hlhs, horth]
  simp only [Matrix.smul_apply, Matrix.one_apply, smul_eq_mul]
  by_cases h : i = j
  · subst h; simp
  · have hne : e i ≠ e j := fun heq => h (e.injective heq)
    simp [h, hne]

/-- Sylvester's 1867 doubling construction: a `±1`-entried orthogonal matrix of every
order `2 ^ t`, with `M * Mᵀ = 2 ^ t • 1`. -/
private lemma sylvester_exists : ∀ t : ℕ, ∃ M : Matrix (Fin (2 ^ t)) (Fin (2 ^ t)) ℝ,
    (∀ i j, M i j = 1 ∨ M i j = -1) ∧
      M * Mᵀ = ((2 ^ t : ℕ) : ℝ) • (1 : Matrix (Fin (2 ^ t)) (Fin (2 ^ t)) ℝ) := by
  intro t
  induction t with
  | zero =>
    have hpm1 : ∀ i j : Fin 1, (1 : Matrix (Fin 1) (Fin 1) ℝ) i j = 1 ∨
        (1 : Matrix (Fin 1) (Fin 1) ℝ) i j = -1 := by
      intro i j
      left
      have hij : i = j := Subsingleton.elim i j
      rw [hij, Matrix.one_apply_eq]
    have horth1 : (1 : Matrix (Fin 1) (Fin 1) ℝ) * (1 : Matrix (Fin 1) (Fin 1) ℝ)ᵀ =
        ((1 : ℕ) : ℝ) • (1 : Matrix (Fin 1) (Fin 1) ℝ) := by simp
    obtain ⟨hpm', horth'⟩ :=
      transport_hadamard (finCongr (pow_zero 2)) (1 : Matrix (Fin 1) (Fin 1) ℝ)
        ((1 : ℕ) : ℝ) hpm1 horth1
    have hcast0 : ((1 : ℕ) : ℝ) = ((2 ^ 0 : ℕ) : ℝ) := by norm_num
    refine ⟨_, hpm', ?_⟩
    rw [← hcast0]
    exact horth'
  | succ t ih =>
    obtain ⟨M, hpm, horth⟩ := ih
    set H2 : Matrix (Fin 2) (Fin 2) ℝ := !![1, 1; 1, -1] with hH2def
    have hH2pm : ∀ i j : Fin 2, H2 i j = 1 ∨ H2 i j = -1 := by
      intro i j
      fin_cases i <;> fin_cases j <;> simp [hH2def]
    have hH2orth : H2 * H2ᵀ = (2 : ℝ) • (1 : Matrix (Fin 2) (Fin 2) ℝ) := by
      apply Matrix.ext
      intro i j
      fin_cases i <;> fin_cases j <;>
        simp [hH2def, Matrix.mul_apply, Fin.sum_univ_two, Matrix.transpose_apply,
              Matrix.smul_apply, Matrix.one_apply] <;> norm_num
    have hsmul_kron : ∀ (c c' : ℝ) (A : Matrix (Fin (2 ^ t)) (Fin (2 ^ t)) ℝ)
        (B : Matrix (Fin 2) (Fin 2) ℝ),
        Matrix.kroneckerMap (· * ·) (c • A) (c' • B) =
          (c * c') • Matrix.kroneckerMap (· * ·) A B := by
      intro c c' A B
      apply Matrix.ext
      intro i j
      simp only [Matrix.kroneckerMap_apply, Matrix.smul_apply, smul_eq_mul]
      ring
    set K : Matrix (Fin (2 ^ t) × Fin 2) (Fin (2 ^ t) × Fin 2) ℝ :=
      Matrix.kroneckerMap (· * ·) M H2 with hKdef
    have hKpm : ∀ i j, K i j = 1 ∨ K i j = -1 := by
      intro i j
      rw [hKdef, Matrix.kroneckerMap_apply]
      rcases hpm i.1 j.1 with ha | ha <;> rcases hH2pm i.2 j.2 with hb | hb <;>
        rw [ha, hb] <;> norm_num
    have hKorth : K * Kᵀ = (((2 ^ t : ℕ) : ℝ) * 2) •
        (1 : Matrix (Fin (2 ^ t) × Fin 2) (Fin (2 ^ t) × Fin 2) ℝ) := by
      rw [hKdef, ← Matrix.kroneckerMap_transpose, ← Matrix.mul_kronecker_mul, horth, hH2orth,
          hsmul_kron, Matrix.one_kronecker_one]
    let e : Fin (2 ^ t) × Fin 2 ≃ Fin (2 ^ (t + 1)) :=
      finProdFinEquiv.trans (finCongr (pow_succ 2 t).symm)
    obtain ⟨hfinal_pm, hfinal_orth⟩ := transport_hadamard e.symm K (((2 ^ t : ℕ) : ℝ) * 2) hKpm hKorth
    refine ⟨K.submatrix e.symm e.symm, hfinal_pm, ?_⟩
    have hcast : (((2 ^ t : ℕ) : ℝ) * 2) = ((2 ^ (t + 1) : ℕ) : ℝ) := by
      push_cast [pow_succ]; ring
    rwa [hcast] at hfinal_orth

/-- The determinant of an `N × N` `±1`-orthogonal matrix (`M * Mᵀ = N • 1`) attains
Hadamard's bound. -/
private lemma hadamard_det_of_orthogonal (k : ℕ) (M : Matrix (Fin (4 * k)) (Fin (4 * k)) ℝ)
    (horth : M * Mᵀ = ((4 * k : ℕ) : ℝ) • (1 : Matrix (Fin (4 * k)) (Fin (4 * k)) ℝ)) :
    |M.det| = ((4 * k : ℕ) : ℝ) ^ (((4 * k : ℕ) : ℝ) / 2) := by
  have hexp : (((4 * k : ℕ) : ℝ) / 2) = ((2 * k : ℕ) : ℝ) := by push_cast; ring
  rw [hexp, Real.rpow_natCast]
  have h1 : M.det * Mᵀ.det = (M * Mᵀ).det := (Matrix.det_mul M Mᵀ).symm
  rw [Matrix.det_transpose, horth, Matrix.det_smul, Matrix.det_one, mul_one,
      Fintype.card_fin] at h1
  have hsq : (M.det) ^ 2 = ((4 * k : ℕ) : ℝ) ^ (4 * k) := by rw [sq]; exact h1
  have hb : ((4 * k : ℕ) : ℝ) ^ (4 * k) = (((4 * k : ℕ) : ℝ) ^ (2 * k)) ^ 2 := by
    rw [← pow_mul]; congr 1; omega
  rw [hb] at hsq
  have hnonneg : (0 : ℝ) ≤ ((4 * k : ℕ) : ℝ) ^ (2 * k) := by positivity
  have hzero : (M.det - ((4 * k : ℕ) : ℝ) ^ (2 * k)) * (M.det + ((4 * k : ℕ) : ℝ) ^ (2 * k)) = 0 := by
    nlinarith [hsq]
  rcases mul_eq_zero.mp hzero with h | h
  · have heq : M.det = ((4 * k : ℕ) : ℝ) ^ (2 * k) := by linarith
    rw [heq, abs_of_nonneg hnonneg]
  · have heq : M.det = -(((4 * k : ℕ) : ℝ) ^ (2 * k)) := by linarith
    rw [heq, abs_of_nonpos (by linarith), neg_neg]

theorem solution (k : ℕ)
    (hk : ∃ q t : ℕ, Nat.Prime q ∧ q % 4 = 3 ∧ 4 * k = (q + 1) * 2 ^ t) :
    ∃ M : Matrix (Fin (4 * k)) (Fin (4 * k)) ℝ,
      (∀ i j, M i j ∈ ({1, -1} : Finset ℝ)) ∧
      |M.det| = ((4 * k : ℕ) : ℝ) ^ (((4 * k : ℕ) : ℝ) / 2) := by
  obtain ⟨q, t, hqprime, hqmod, hdim⟩ := hk
  haveI : Fact (Nat.Prime q) := ⟨hqprime⟩
  have hcardZ : Fintype.card (ZMod q) = q := ZMod.card q
  have hcharZ : ringChar (ZMod q) ≠ 2 := by
    have : ringChar (ZMod q) = q := ZMod.ringChar_zmod_n q
    rw [this]
    have hq2 : q ≠ 2 := by omega
    exact hq2
  have hmodZ : Fintype.card (ZMod q) % 4 = 3 := by rw [hcardZ]; exact hqmod
  obtain ⟨P, hPpm, hPorth⟩ := Paley_construction_I (F := ZMod q) hcharZ hmodZ
  set eP : Fin (q + 1) ≃ Fin (Fintype.card (ZMod q) + 1) := finCongr (by rw [hcardZ])
  obtain ⟨hPpm', hPorth'⟩ := transport_hadamard eP P ((Fintype.card (ZMod q) + 1 : ℕ) : ℝ) hPpm hPorth
  have hcastP : ((Fintype.card (ZMod q) + 1 : ℕ) : ℝ) = ((q + 1 : ℕ) : ℝ) := by rw [hcardZ]
  rw [hcastP] at hPorth'
  obtain ⟨S, hSpm, hSorth⟩ := sylvester_exists t
  obtain ⟨M0, hM0pm, hM0orth⟩ :=
    Hadamard_matrix_kronecker_product (P.submatrix eP eP) S hPpm' hPorth' hSpm hSorth
  set eK : Fin (4 * k) ≃ Fin ((q + 1) * 2 ^ t) := finCongr hdim
  obtain ⟨hMpm, hMorth⟩ := transport_hadamard eK M0 (((q + 1) * 2 ^ t : ℕ) : ℝ) hM0pm hM0orth
  have hcastK : (((q + 1) * 2 ^ t : ℕ) : ℝ) = ((4 * k : ℕ) : ℝ) := by rw [hdim]
  rw [hcastK] at hMorth
  refine ⟨M0.submatrix eK eK, ?_, ?_⟩
  · intro i j
    simp only [Matrix.submatrix_apply]
    rcases hM0pm (eK i) (eK j) with h | h <;> simp [h]
  · exact hadamard_det_of_orthogonal k (M0.submatrix eK eK) hMorth
