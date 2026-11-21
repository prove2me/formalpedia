-- Prove2me | solution 1 for NisetNoGo.GECC.gecc_channel
-- status  : ACCEPTED   (prove)
-- author  : @utkuokur
-- created : 2026-11-20T22:48:25.172024+00:00
-- url     : https://prove2.me/submissions/3a2eae78-94e4-4638-b0d1-ab2094218bb6

import Mathlib
import Definitions.Def_NisetNoGo_GECC_Setup

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

open QAlgorithms.Papers.Independent.Frontier30.P13
open QAlgorithms.Papers.Independent.Dependency50.P10 (complexify)
open scoped ComplexOrder
open Matrix

namespace NisetNoGo.GECC.Code

/-! ### Complexification is compatible with the matrix operations -/

theorem c_mul {a b c : Type*} [Fintype b] (A : Matrix a b ℝ) (B : Matrix b c ℝ) :
    complexify (A * B) = complexify A * complexify B := by
  ext i j
  simp [complexify, Matrix.mul_apply]

theorem c_add {a b : Type*} (A B : Matrix a b ℝ) :
    complexify (A + B) = complexify A + complexify B := by
  ext i j
  simp [complexify]

theorem c_sub {a b : Type*} (A B : Matrix a b ℝ) :
    complexify (A - B) = complexify A - complexify B := by
  ext i j
  simp [complexify]

theorem c_conjTranspose {a b : Type*} (A : Matrix a b ℝ) :
    (complexify A)ᴴ = complexify Aᵀ := by
  ext i j
  simp [complexify, Matrix.conjTranspose_apply]

/-! ### Sums over the coordinates -/

theorem sum_q1 {β : Type*} [AddCommMonoid β] (f : ModeQuadrature (Fin 1) → β) :
    ∑ q, f q = f (0, false) + f (0, true) := by
  rw [Fintype.sum_prod_type]
  simp [add_comm]

theorem sum_qn {n : ℕ} {β : Type*} [AddCommMonoid β] (f : ModeQuadrature (Fin n) → β) :
    ∑ i, f i = ∑ k : Fin n, (f (k, false) + f (k, true)) := by
  rw [Fintype.sum_prod_type]
  simp [add_comm]

/-! ### Block-diagonal matrices: one single-mode block per mode -/

/-- The block-diagonal matrix with the single-mode block `F k` on mode `k`. -/
def bd {R : Type*} [Zero R] (n : ℕ)
    (F : Fin n → Matrix (ModeQuadrature (Fin 1)) (ModeQuadrature (Fin 1)) R) :
    Matrix (ModeQuadrature (Fin n)) (ModeQuadrature (Fin n)) R :=
  fun i j => if i.1 = j.1 then F i.1 (0, i.2) (0, j.2) else 0

theorem bd_mul {n : ℕ} (F G : Fin n → Matrix (ModeQuadrature (Fin 1)) (ModeQuadrature (Fin 1)) ℝ) :
    bd n F * bd n G = bd n (fun k => F k * G k) := by
  ext ⟨k, a⟩ ⟨l, b⟩
  simp only [Matrix.mul_apply, bd, sum_qn, sum_q1]
  by_cases h : k = l
  · subst h
    rw [Finset.sum_eq_single k]
    · simp
    · intro m _ hm
      simp [Ne.symm hm]
    · simp
  · simp only [h, if_false]
    apply Finset.sum_eq_zero
    intro m _
    by_cases hkm : k = m
    · subst hkm
      simp [h]
    · simp [hkm]

theorem bd_sub {n : ℕ} (F G : Fin n → Matrix (ModeQuadrature (Fin 1)) (ModeQuadrature (Fin 1)) ℝ) :
    bd n F - bd n G = bd n (fun k => F k - G k) := by
  ext i j
  simp only [bd, Matrix.sub_apply]
  split_ifs <;> simp

theorem bd_csub {n : ℕ} (F G : Fin n → Matrix (ModeQuadrature (Fin 1)) (ModeQuadrature (Fin 1)) ℂ) :
    bd n F - bd n G = bd n (fun k => F k - G k) := by
  ext i j
  simp only [bd, Matrix.sub_apply]
  split_ifs <;> simp

theorem bd_csmul {n : ℕ} (z : ℂ)
    (F : Fin n → Matrix (ModeQuadrature (Fin 1)) (ModeQuadrature (Fin 1)) ℂ) :
    z • bd n F = bd n (fun k => z • F k) := by
  ext i j
  simp only [bd, Matrix.smul_apply]
  split_ifs <;> simp

theorem bd_transpose {n : ℕ} (F : Fin n → Matrix (ModeQuadrature (Fin 1)) (ModeQuadrature (Fin 1)) ℝ) :
    (bd n F)ᵀ = bd n (fun k => (F k)ᵀ) := by
  ext i j
  simp only [bd, Matrix.transpose_apply]
  by_cases h : i.1 = j.1
  · simp [h]
  · simp [h, Ne.symm h]

theorem c_bd {n : ℕ} (F : Fin n → Matrix (ModeQuadrature (Fin 1)) (ModeQuadrature (Fin 1)) ℝ) :
    complexify (bd n F) = bd n (fun k => complexify (F k)) := by
  ext i j
  simp only [bd, complexify]
  split_ifs <;> simp

/-- A block-diagonal matrix with positive semidefinite blocks is positive semidefinite. -/
theorem bd_psd {n : ℕ} (F : Fin n → Matrix (ModeQuadrature (Fin 1)) (ModeQuadrature (Fin 1)) ℂ)
    (hF : ∀ k, (F k).PosSemidef) : (bd n F).PosSemidef := by
  refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg ?_ ?_
  · ext ⟨k, a⟩ ⟨l, b⟩
    simp only [Matrix.conjTranspose_apply, bd]
    by_cases h : k = l
    · subst h
      have := congrFun (congrFun (hF k).1 (0, a)) (0, b)
      simpa [Matrix.conjTranspose_apply] using this
    · simp [h, Ne.symm h]
  · intro x
    have e : star x ⬝ᵥ (bd n F *ᵥ x) =
        ∑ k, star (fun q : ModeQuadrature (Fin 1) => x (k, q.2)) ⬝ᵥ
          (F k *ᵥ fun q : ModeQuadrature (Fin 1) => x (k, q.2)) := by
      simp only [dotProduct, Matrix.mulVec, sum_qn, sum_q1, bd, Pi.star_apply]
      apply Finset.sum_congr rfl
      intro k _
      simp [ite_mul, Finset.sum_add_distrib, Finset.sum_ite_eq]
    rw [e]
    exact Finset.sum_nonneg (fun k _ => (hF k).dotProduct_mulVec_nonneg _)

/-! ### The matrices of the code as block-diagonal matrices -/

theorem channelPower_eq {n : ℕ} (M : Matrix (ModeQuadrature (Fin 1)) (ModeQuadrature (Fin 1)) ℝ) :
    channelPower n M = bd n (fun _ => M) := by
  ext i j
  by_cases h : i.1 = j.1 <;> simp [channelPower, bd, h]

theorem phaseJ_eq (n : ℕ) : phaseJ (Fin n) = bd n (fun _ => phaseJ (Fin 1)) := by
  ext i j
  by_cases h : i.1 = j.1 <;> simp [phaseJ, bd, h]

theorem vac_eq (n : ℕ) [NeZero n] :
    ancillaVacuum n = bd n (fun k => if k = 0 then 0 else 1) := by
  ext ⟨k, a⟩ ⟨l, b⟩
  by_cases h : k = l
  · subst h
    by_cases hk : k = 0 <;> by_cases hab : a = b <;>
      simp [ancillaVacuum, bd, Matrix.diagonal_apply, Matrix.one_apply, hk, hab]
  · simp [ancillaVacuum, bd, Matrix.diagonal_apply, h]

/-- The selection matrix of the signal mode. -/
def sel (n : ℕ) [NeZero n] : Matrix (ModeQuadrature (Fin 1)) (ModeQuadrature (Fin n)) ℝ :=
  fun q i => if i = inputMode n q then 1 else 0

theorem sub_eq (n : ℕ) [NeZero n]
    (A : Matrix (ModeQuadrature (Fin n)) (ModeQuadrature (Fin n)) ℝ) :
    A.submatrix (inputMode n) (inputMode n) = sel n * A * (sel n)ᵀ := by
  ext q q'
  simp [Matrix.mul_apply, sel, Matrix.transpose_apply]

theorem phaseJ_sub (n : ℕ) [NeZero n] :
    (phaseJ (Fin n)).submatrix (inputMode n) (inputMode n) = phaseJ (Fin 1) := by
  ext ⟨k, a⟩ ⟨l, b⟩
  cases a <;> cases b <;> simp [phaseJ, inputMode, Subsingleton.elim k l]

theorem emb_eq (n : ℕ) [NeZero n] :
    (sel n)ᵀ * phaseJ (Fin 1) * sel n = bd n (fun k => if k = 0 then phaseJ (Fin 1) else 0) := by
  ext ⟨k, a⟩ ⟨l, b⟩
  simp only [Matrix.mul_apply, sum_q1, sel, Matrix.transpose_apply, inputMode, bd, Prod.mk.injEq]
  by_cases hk : k = 0 <;> by_cases hl : l = 0 <;> cases a <;> cases b <;>
    simp [hk, hl, phaseJ, eq_comm]

/-- The vacuum satisfies the uncertainty relation. -/
theorem vacuum_psd :
    (complexify (1 : Matrix (ModeQuadrature (Fin 1)) (ModeQuadrature (Fin 1)) ℝ) -
      Complex.I • complexify (phaseJ (Fin 1))).PosSemidef := by
  refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg ?_ ?_
  · ext ⟨k, a⟩ ⟨l, b⟩
    have hk : k = 0 := Subsingleton.elim _ _
    have hl : l = 0 := Subsingleton.elim _ _
    subst hk hl
    cases a <;> cases b <;>
      simp [Matrix.conjTranspose_apply, complexify, phaseJ, Matrix.one_apply]
  · intro x
    have e : star x ⬝ᵥ ((complexify (1 : Matrix (ModeQuadrature (Fin 1))
        (ModeQuadrature (Fin 1)) ℝ) - Complex.I • complexify (phaseJ (Fin 1))) *ᵥ x) =
        ((Complex.normSq (x (0, false) + Complex.I * x (0, true)) : ℝ) : ℂ) := by
      simp only [dotProduct, Matrix.mulVec, sum_q1, Pi.star_apply]
      simp [complexify, phaseJ, Matrix.one_apply]
      apply Complex.ext <;> simp [Complex.normSq_apply] <;> ring
    rw [e]
    exact_mod_cast Complex.normSq_nonneg _

end NisetNoGo.GECC.Code

open NisetNoGo.GECC NisetNoGo.GECC.Code in
theorem solution (n : ℕ) [NeZero n]
    (M N : Matrix (ModeQuadrature (Fin 1)) (ModeQuadrature (Fin 1)) ℝ)
    (SE SD : Matrix (ModeQuadrature (Fin n)) (ModeQuadrature (Fin n)) ℝ)
    (hT : IsCPChannel M N) (hE : IsSymplecticMat SE)
    (hD : IsSymplecticMat SD) :
    IsCPChannel (geccM n M SE SD) (geccN n M N SE SD) := by
  obtain ⟨hsym, hpsd⟩ := hT
  -- abbreviations
  set Jn := phaseJ (Fin n) with hJn
  set J1 := phaseJ (Fin 1) with hJ1
  set Mn := channelPower n M with hMn
  set Nn := channelPower n N with hNn
  set V := ancillaVacuum n with hV
  set P := sel n with hP
  set K := SD * Mn * SE with hK
  have hE' : SE * (Jn * SEᵀ) = Jn := by
    rw [← Matrix.mul_assoc]
    exact hE
  have hD' : SD * (Jn * SDᵀ) = Jn := by
    rw [← Matrix.mul_assoc]
    exact hD
  have hMM : geccM n M SE SD = P * K * Pᵀ := sub_eq n _
  have hNN : geccN n M N SE SD = P * (K * V * Kᵀ + SD * Nn * SDᵀ) * Pᵀ := sub_eq n _
  have hJP : J1 = P * Jn * Pᵀ := by
    rw [← sub_eq n Jn]
    exact (phaseJ_sub n).symm
  have hVt : Vᵀ = V := by
    rw [hV, vac_eq, bd_transpose]
    congr 1
    funext k
    by_cases hk : k = 0 <;> simp [hk]
  have hNt : Nnᵀ = Nn := by
    rw [hNn, channelPower_eq, bd_transpose]
    congr 1
    funext k
    exact hsym
  refine ⟨?_, ?_⟩
  · -- the noise matrix is symmetric
    rw [hNN]
    simp only [Matrix.transpose_mul, Matrix.transpose_add, Matrix.transpose_transpose, hVt, hNt,
      Matrix.mul_assoc]
  · -- the two positive semidefinite pieces
    have hDpsd : (complexify Nn - Complex.I • complexify (Jn - Mn * Jn * Mnᵀ)).PosSemidef := by
      have e : complexify Nn - Complex.I • complexify (Jn - Mn * Jn * Mnᵀ) =
          bd n (fun _ => complexify N - Complex.I • complexify (J1 - M * J1 * Mᵀ)) := by
        rw [hNn, hMn, hJn, channelPower_eq, channelPower_eq, phaseJ_eq, bd_transpose, bd_mul, bd_mul,
          bd_sub, c_bd, c_bd, bd_csmul, bd_csub]
      rw [e]
      exact bd_psd _ (fun _ => hpsd)
    have hWpsd : (complexify V - Complex.I • complexify (Jn - Pᵀ * J1 * P)).PosSemidef := by
      have e : complexify V - Complex.I • complexify (Jn - Pᵀ * J1 * P) =
          bd n (fun k => complexify (if k = 0 then 0 else 1) -
            Complex.I • complexify (J1 - (if k = 0 then J1 else 0))) := by
        rw [hV, hJn, hP, hJ1, vac_eq, phaseJ_eq, emb_eq, bd_sub, c_bd, c_bd, bd_csmul, bd_csub]
      rw [e]
      apply bd_psd
      intro k
      by_cases hk : k = 0
      · have z : complexify (if k = 0 then (0 : Matrix (ModeQuadrature (Fin 1))
            (ModeQuadrature (Fin 1)) ℝ) else 1) -
            Complex.I • complexify (J1 - (if k = 0 then J1 else 0)) = 0 := by
          ext i j
          simp [hk, complexify]
        rw [z]
        exact Matrix.PosSemidef.zero
      · have z : complexify (if k = 0 then (0 : Matrix (ModeQuadrature (Fin 1))
            (ModeQuadrature (Fin 1)) ℝ) else 1) -
            Complex.I • complexify (J1 - (if k = 0 then J1 else 0)) =
            complexify (1 : Matrix (ModeQuadrature (Fin 1)) (ModeQuadrature (Fin 1)) ℝ) -
              Complex.I • complexify (phaseJ (Fin 1)) := by
          simp [hk, hJ1]
        rw [z]
        exact vacuum_psd
    -- the real identity behind the decomposition
    have hKJ : K * Jn * Kᵀ = SD * Mn * Jn * Mnᵀ * SDᵀ := by
      have h1 : K * Jn * Kᵀ = SD * Mn * (SE * Jn * SEᵀ) * Mnᵀ * SDᵀ := by
        rw [hK]
        simp only [Matrix.transpose_mul, Matrix.mul_assoc]
      rw [h1, show SE * Jn * SEᵀ = Jn from hE]
    have r1 : P * SD * (Jn - Mn * Jn * Mnᵀ) * SDᵀ * Pᵀ =
        P * (SD * Jn * SDᵀ) * Pᵀ - P * (SD * Mn * Jn * Mnᵀ * SDᵀ) * Pᵀ := by
      simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_assoc]
    have r2 : P * K * (Jn - Pᵀ * J1 * P) * Kᵀ * Pᵀ =
        P * (K * Jn * Kᵀ) * Pᵀ - (P * K * Pᵀ) * J1 * (P * K * Pᵀ)ᵀ := by
      simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_assoc, Matrix.transpose_mul,
        Matrix.transpose_transpose]
    have hreal : J1 - geccM n M SE SD * J1 * (geccM n M SE SD)ᵀ =
        P * SD * (Jn - Mn * Jn * Mnᵀ) * SDᵀ * Pᵀ + P * K * (Jn - Pᵀ * J1 * P) * Kᵀ * Pᵀ := by
      rw [r1, r2, hD, hKJ, hMM, ← hJP]
      abel
    have key : complexify (geccN n M N SE SD) -
        Complex.I • complexify (J1 - geccM n M SE SD * J1 * (geccM n M SE SD)ᵀ) =
        (complexify P * complexify SD) *
            (complexify Nn - Complex.I • complexify (Jn - Mn * Jn * Mnᵀ)) *
            (complexify P * complexify SD)ᴴ +
          (complexify P * complexify K) *
            (complexify V - Complex.I • complexify (Jn - Pᵀ * J1 * P)) *
            (complexify P * complexify K)ᴴ := by
      rw [hreal, hNN]
      simp only [c_mul, c_add, c_sub, Matrix.conjTranspose_mul, c_conjTranspose, Matrix.mul_add,
        Matrix.add_mul, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_assoc, Matrix.mul_smul,
        Matrix.smul_mul, smul_add, smul_sub]
      abel
    show (complexify (geccN n M N SE SD) -
        Complex.I • complexify (J1 - geccM n M SE SD * J1 * (geccM n M SE SD)ᵀ)).PosSemidef
    rw [key]
    exact (hDpsd.mul_mul_conjTranspose_same _).add (hWpsd.mul_mul_conjTranspose_same _)
