-- Prove2me | solution 1 for MatrixLewis.lemma_3_8
-- status  : ACCEPTED   (prove)
-- author  : @CGTMoyano
-- created : 2026-11-24T19:27:31.478432+00:00
-- url     : https://prove2.me/submissions/c545e643-3250-4729-841f-5d235d18a956

import Mathlib
import Definitions.Def_MatrixLewis_Assumption31
import Definitions.Def_MatrixLewis_Fpr
import Definitions.Def_MatrixLewis_Fdu
import Definitions.Def_MatrixLewis_gapDelta
import Theorems.Thm_MatrixLewis_fact_3_6

open MatrixLewis Matrix

namespace Lemma38Aux

section Spectral

variable {k : Type*} [Fintype k] [DecidableEq k]

theorem herm_iff {X : Matrix k k ℝ} : X.IsHermitian ↔ Xᵀ = X := by
  unfold Matrix.IsHermitian
  rw [conjTranspose_eq_transpose_of_trivial]

theorem cfc_rep {A : Matrix k k ℝ} (hA : A.IsHermitian) (f : ℝ → ℝ) :
    cfc f A = (hA.eigenvectorUnitary : Matrix k k ℝ) *
      diagonal (fun i => f (hA.eigenvalues i)) * (hA.eigenvectorUnitary : Matrix k k ℝ)ᵀ := by
  rw [hA.cfc_eq, Matrix.IsHermitian.cfc, Unitary.conjStarAlgAut_apply]
  simp [Matrix.star_eq_conjTranspose, Function.comp_def]

theorem self_rep {A : Matrix k k ℝ} (hA : A.IsHermitian) :
    A = (hA.eigenvectorUnitary : Matrix k k ℝ) *
      diagonal (fun i => hA.eigenvalues i) * (hA.eigenvectorUnitary : Matrix k k ℝ)ᵀ := by
  rw [← cfc_rep hA (fun t => t)]
  exact (cfc_id' ℝ A hA.isSelfAdjoint).symm

theorem orth {A : Matrix k k ℝ} (hA : A.IsHermitian) :
    (hA.eigenvectorUnitary : Matrix k k ℝ)ᵀ * (hA.eigenvectorUnitary : Matrix k k ℝ) = 1 ∧
      (hA.eigenvectorUnitary : Matrix k k ℝ) * (hA.eigenvectorUnitary : Matrix k k ℝ)ᵀ = 1 := by
  have h1 := Unitary.coe_star_mul_self hA.eigenvectorUnitary
  have h2 := Unitary.coe_mul_star_self hA.eigenvectorUnitary
  simp only [Unitary.coe_star, Matrix.star_eq_conjTranspose,
    Matrix.conjTranspose_eq_transpose_of_trivial] at h1 h2
  exact ⟨h1, h2⟩

theorem trace_conj (U X : Matrix k k ℝ) (hU : Uᵀ * U = 1) : trace (U * X * Uᵀ) = trace X := by
  rw [Matrix.trace_mul_comm, ← Matrix.mul_assoc, hU, Matrix.one_mul]

theorem trace_conj_diag (U : Matrix k k ℝ) (hU : Uᵀ * U = 1) (f : k → ℝ) :
    trace (U * diagonal f * Uᵀ) = ∑ i, f i := by
  rw [trace_conj U _ hU, Matrix.trace_diagonal]

theorem conj_diag_mul (U : Matrix k k ℝ) (hU : Uᵀ * U = 1) (d e : k → ℝ) :
    (U * diagonal d * Uᵀ) * (U * diagonal e * Uᵀ) = U * diagonal (fun i => d i * e i) * Uᵀ := by
  calc (U * diagonal d * Uᵀ) * (U * diagonal e * Uᵀ)
      = U * (diagonal d * (Uᵀ * U) * diagonal e) * Uᵀ := by simp only [Matrix.mul_assoc]
    _ = U * diagonal (fun i => d i * e i) * Uᵀ := by
      rw [hU, Matrix.mul_one, diagonal_mul_diagonal]

theorem conj_herm (U : Matrix k k ℝ) (d : k → ℝ) : (U * diagonal d * Uᵀ).IsHermitian := by
  rw [herm_iff, transpose_mul, transpose_mul, transpose_transpose, diagonal_transpose,
    Matrix.mul_assoc]

theorem conj_posDef (U : Matrix k k ℝ) (hU' : U * Uᵀ = 1) (d : k → ℝ) (hd : ∀ i, 0 < d i) :
    (U * diagonal d * Uᵀ).PosDef := by
  have hD : (diagonal d).PosDef := PosDef.diagonal hd
  have hinj : Function.Injective (Uᵀ).mulVec := by
    intro x y hxy
    have := congrArg (fun v => U *ᵥ v) hxy
    simpa [mulVec_mulVec, hU'] using this
  have := hD.conjTranspose_mul_mul_same hinj
  simpa [conjTranspose_eq_transpose_of_trivial] using this

theorem mpow_herm {X : Matrix k k ℝ} (hX : X.IsHermitian) (r : ℝ) : (mpow r X).IsHermitian := by
  unfold mpow
  rw [cfc_rep hX]
  exact conj_herm _ _

theorem mpow_posDef {X : Matrix k k ℝ} (hX : X.PosDef) (r : ℝ) : (mpow r X).PosDef := by
  unfold mpow
  rw [cfc_rep hX.1]
  exact conj_posDef _ (orth hX.1).2 _ (fun i => Real.rpow_pos_of_pos (hX.eigenvalues_pos i) r)

theorem mpow_half_mul {X : Matrix k k ℝ} (hX : X.PosSemidef) :
    mpow (1 / 2) X * mpow (1 / 2) X = X := by
  unfold mpow
  rw [cfc_rep hX.1, conj_diag_mul _ (orth hX.1).1]
  conv_rhs => rw [self_rep hX.1]
  have e : (fun i => hX.1.eigenvalues i ^ (1 / 2 : ℝ) * hX.1.eigenvalues i ^ (1 / 2 : ℝ)) =
      fun i => hX.1.eigenvalues i := by
    funext i
    rw [← Real.rpow_add' (hX.eigenvalues_nonneg i) (by norm_num)]
    norm_num
  rw [e]

theorem rpow_sub_one_mul {x p : ℝ} (hx : 0 ≤ x) (hp : 0 < p) : x ^ (p - 1) * x = x ^ p := by
  rcases hx.eq_or_lt with h | h
  · rw [← h, mul_zero, Real.zero_rpow hp.ne']
  · rw [Real.rpow_sub_one h.ne']
    field_simp

theorem isUnit_of_posDef {X : Matrix k k ℝ} (hX : X.PosDef) : IsUnit X.det :=
  (hX.det_pos).ne'.isUnit

theorem posDef_conj_herm {X H : Matrix k k ℝ} (hX : X.IsHermitian) (hXu : IsUnit X.det)
    (hH : H.PosDef) : (X * H * X).PosDef := by
  have hinj : Function.Injective X.mulVec :=
    Matrix.mulVec_injective_iff_isUnit.mpr ((Matrix.isUnit_iff_isUnit_det X).mpr hXu)
  have := hH.conjTranspose_mul_mul_same hinj
  rwa [hX.eq] at this

/-- For a positive definite matrix, the sum of `ϱ` over its eigenvalues. -/
theorem sum_rho {X : Matrix k k ℝ} (hX : X.PosDef) :
    ∑ i, rho (hX.1.eigenvalues i) = X.trace - Real.log X.det - Fintype.card k := by
  have htr : X.trace = ∑ i, hX.1.eigenvalues i := by
    simpa using hX.1.trace_eq_sum_eigenvalues
  have hdet : X.det = ∏ i, hX.1.eigenvalues i := by
    simpa using hX.1.det_eq_prod_eigenvalues
  rw [htr, hdet, Real.log_prod (fun i _ => (hX.eigenvalues_pos i).ne')]
  unfold rho
  rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ]
  simp

theorem rho_nonneg {t : ℝ} (ht : 0 < t) : 0 ≤ rho t := by
  unfold rho
  linarith [Real.log_le_sub_one_of_pos ht]

theorem rho_eq_zero {t : ℝ} (ht : 0 < t) : rho t = 0 ↔ t = 1 := by
  constructor
  · intro h
    by_contra hne
    have := Real.log_lt_sub_one_of_pos ht hne
    unfold rho at h
    linarith
  · intro h
    unfold rho
    rw [h, Real.log_one]
    ring

theorem eq_one_iff {X : Matrix k k ℝ} (hX : X.IsHermitian) :
    X = 1 ↔ ∀ i, hX.eigenvalues i = 1 := by
  obtain ⟨hU, hU'⟩ := orth hX
  set U := (hX.eigenvectorUnitary : Matrix k k ℝ) with hUdef
  have hrep : X = U * diagonal (fun i => hX.eigenvalues i) * Uᵀ := self_rep hX
  constructor
  · intro h1 i
    have e : Uᵀ * (U * diagonal (fun i => hX.eigenvalues i) * Uᵀ) * U =
        diagonal (fun i => hX.eigenvalues i) := by
      simp only [Matrix.mul_assoc]
      rw [hU, Matrix.mul_one, ← Matrix.mul_assoc, hU, Matrix.one_mul]
    have hD : diagonal (fun i => hX.eigenvalues i) = Uᵀ * X * U := by
      calc diagonal (fun i => hX.eigenvalues i)
          = Uᵀ * (U * diagonal (fun i => hX.eigenvalues i) * Uᵀ) * U := e.symm
        _ = Uᵀ * X * U := by rw [← hrep]
    have h2 : Uᵀ * X * U = 1 := by rw [h1, Matrix.mul_one, hU]
    rw [h2] at hD
    have := congrFun (congrFun hD i) i
    simpa using this
  · intro h
    rw [hrep]
    have : (fun i => hX.eigenvalues i) = fun _ => (1 : ℝ) := funext h
    rw [this, Matrix.diagonal_one, Matrix.mul_one, hU']

end Spectral

/-- Adjointness of `H_S` and `H*_S` in the trace pairing (eq. (5)). -/
theorem trace_adj {n m : ℕ} (B : Fin m → Matrix (Fin n) (Fin n) ℝ) (hB : ∀ i, (B i)ᵀ = B i)
    (Z : Matrix (Fin n) (Fin n) ℝ) (hZ : Zᵀ = Z) (M : Matrix (Fin m) (Fin m) ℝ) :
    trace ((∑ i, ∑ j, M i j • sym (B i * B j)) * Z) =
      trace (M * Matrix.of fun i j => (B i * Z * B j).trace) := by
  have key : ∀ i j, trace (sym (B i * B j) * Z) = trace (B j * Z * B i) := by
    intro i j
    have h1 : trace (B i * B j * Z) = trace (B j * Z * B i) := by
      rw [Matrix.mul_assoc, Matrix.trace_mul_comm]
    have h2 : trace (B j * Z * B i) = trace (B i * Z * B j) := by
      rw [← Matrix.trace_transpose (B j * Z * B i)]
      simp only [transpose_mul, hB, hZ, Matrix.mul_assoc]
    have h3 : trace (B j * B i * Z) = trace (B i * Z * B j) := by
      rw [Matrix.mul_assoc, Matrix.trace_mul_comm]
    unfold sym
    rw [Matrix.smul_mul, Matrix.trace_smul, Matrix.add_mul, Matrix.trace_add, transpose_mul,
      hB, hB, h1, h3, ← h2, smul_eq_mul]
    ring
  rw [Finset.sum_mul, Matrix.trace_sum]
  simp only [Finset.sum_mul, Matrix.trace_sum, Matrix.smul_mul, Matrix.trace_smul, smul_eq_mul,
    key]
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.of_apply]


theorem dot_sym {n : ℕ} (X : Matrix (Fin n) (Fin n) ℝ) (hX : Xᵀ = X) (u w : Fin n → ℝ) :
    u ⬝ᵥ (X *ᵥ w) = (X *ᵥ u) ⬝ᵥ w := by
  rw [dotProduct_mulVec]
  congr 1
  rw [← vecMul_transpose, hX]

/-- `vᵀ H*_S(M) v = ∑ₜ ∑ᵢⱼ Mᵢⱼ (Bᵢv)ₜ (Bⱼv)ₜ`. -/
theorem quad_adj {n m : ℕ} (B : Fin m → Matrix (Fin n) (Fin n) ℝ) (hB : ∀ i, (B i)ᵀ = B i)
    (M : Matrix (Fin m) (Fin m) ℝ) (v : Fin n → ℝ) :
    v ⬝ᵥ ((∑ i, ∑ j, M i j • sym (B i * B j)) *ᵥ v) =
      ∑ t, ∑ i, ∑ j, M i j * ((B i *ᵥ v) t * (B j *ᵥ v) t) := by
  have key : ∀ i j, v ⬝ᵥ (sym (B i * B j) *ᵥ v) = (B i *ᵥ v) ⬝ᵥ (B j *ᵥ v) := by
    intro i j
    have e1 : v ⬝ᵥ ((B i * B j) *ᵥ v) = (B i *ᵥ v) ⬝ᵥ (B j *ᵥ v) := by
      rw [← mulVec_mulVec, dot_sym _ (hB i)]
    have e2 : v ⬝ᵥ ((B i * B j)ᵀ *ᵥ v) = (B i *ᵥ v) ⬝ᵥ (B j *ᵥ v) := by
      rw [transpose_mul, hB, hB, ← mulVec_mulVec, dot_sym _ (hB j), dotProduct_comm]
    unfold sym
    rw [smul_mulVec, add_mulVec, dotProduct_smul, dotProduct_add, e1, e2, smul_eq_mul]
    ring
  simp only [sum_mulVec, dotProduct_sum, smul_mulVec, dotProduct_smul, key, smul_eq_mul]
  simp only [dotProduct, Finset.mul_sum]
  refine (Finset.sum_congr rfl (fun i _ => Finset.sum_comm)).trans Finset.sum_comm

theorem sym_transpose {n : ℕ} (X : Matrix (Fin n) (Fin n) ℝ) : (sym X)ᵀ = sym X := by
  unfold sym
  rw [transpose_smul, transpose_add, transpose_transpose, add_comm]

theorem adj_posDef {n m : ℕ} (B : Fin m → Matrix (Fin n) (Fin n) ℝ) (hB : ∀ i, (B i)ᵀ = B i)
    (M : Matrix (Fin m) (Fin m) ℝ) (hM : M.PosDef)
    (hker : ∀ v, (∀ i, B i *ᵥ v = 0) → v = 0) :
    (∑ i, ∑ j, M i j • sym (B i * B j)).PosDef := by
  refine PosDef.of_dotProduct_mulVec_pos ?_ ?_
  · rw [herm_iff]
    simp only [transpose_sum, transpose_smul, sym_transpose]
  · intro v hv
    rw [star_trivial, quad_adj B hB M v]
    have hterm : ∀ t, ∑ i, ∑ j, M i j * ((B i *ᵥ v) t * (B j *ᵥ v) t) =
        (fun i => (B i *ᵥ v) t) ⬝ᵥ (M *ᵥ fun i => (B i *ᵥ v) t) := by
      intro t
      simp only [dotProduct, mulVec, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      ring
    simp only [hterm]
    obtain ⟨i, hi⟩ : ∃ i, B i *ᵥ v ≠ 0 := by
      by_contra h
      push_neg at h
      exact hv (hker v h)
    obtain ⟨t, ht⟩ := Function.ne_iff.mp hi
    apply Finset.sum_pos'
    · intro t _
      have := hM.posSemidef.dotProduct_mulVec_nonneg (fun i => (B i *ᵥ v) t)
      simpa using this
    · refine ⟨t, Finset.mem_univ _, ?_⟩
      have hy : (fun i => (B i *ᵥ v) t) ≠ 0 := by
        intro h0
        exact ht (congrFun h0 i)
      have := hM.dotProduct_mulVec_pos hy
      simpa using this

theorem mat_eq_zero_of_mulVec {n : ℕ} (C : Matrix (Fin n) (Fin n) ℝ)
    (h : ∀ w, C *ᵥ w = 0) : C = 0 := by
  ext i j
  have := congrFun (h (Pi.single j 1)) i
  simpa [mulVec, dotProduct, Pi.single_apply] using this

theorem gram_posDef {n m : ℕ} (B : Fin m → Matrix (Fin n) (Fin n) ℝ) (hB : ∀ i, (B i)ᵀ = B i)
    (hlin : LinearIndependent ℝ B) (Z : Matrix (Fin n) (Fin n) ℝ) (hZ : Z.PosDef) :
    (Matrix.of fun i j => (B i * Z * B j).trace).PosDef := by
  have hZT : Zᵀ = Z := herm_iff.mp hZ.1
  refine PosDef.of_dotProduct_mulVec_pos ?_ ?_
  · rw [herm_iff]
    ext i j
    simp only [transpose_apply, of_apply]
    rw [← Matrix.trace_transpose]
    simp only [transpose_mul, hB, hZT, Matrix.mul_assoc]
  · intro x hx
    rw [star_trivial]
    have hsym : ∀ i j, (B i * Z * B j).trace = (B j * Z * B i).trace := by
      intro i j
      rw [← Matrix.trace_transpose]
      simp only [transpose_mul, hB, hZT, Matrix.mul_assoc]
    set C := ∑ i, x i • B i with hCdef
    have hq : x ⬝ᵥ ((Matrix.of fun i j => (B i * Z * B j).trace) *ᵥ x) = trace (C * Z * C) := by
      simp only [hCdef, dotProduct, mulVec, of_apply, Finset.sum_mul, Finset.mul_sum,
        Matrix.smul_mul, Matrix.mul_smul, Matrix.trace_sum, Matrix.trace_smul, smul_eq_mul]
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      rw [hsym i j]
      ring
    rw [hq]
    have hC : C ≠ 0 := by
      intro h0
      apply hx
      funext i
      exact Fintype.linearIndependent_iff.mp hlin x h0 i
    have hCT : Cᵀ = C := by
      simp only [hCdef, transpose_sum, transpose_smul, hB]
    have hpsd : (Cᴴ * Z * C).PosSemidef := hZ.posSemidef.conjTranspose_mul_mul_same C
    rw [conjTranspose_eq_transpose_of_trivial, hCT] at hpsd
    rcases hpsd.trace_nonneg.lt_or_eq with hlt | heq
    · exact hlt
    · exfalso
      have h0 : C * Z * C = 0 := (hpsd.trace_eq_zero_iff).mp heq.symm
      obtain ⟨w, hw⟩ : ∃ w, C *ᵥ w ≠ 0 := by
        by_contra h
        push_neg at h
        exact hC (mat_eq_zero_of_mulVec C h)
      have hpos := hZ.dotProduct_mulVec_pos hw
      have : star (C *ᵥ w) ⬝ᵥ (Z *ᵥ (C *ᵥ w)) = w ⬝ᵥ ((C * Z * C) *ᵥ w) := by
        rw [star_trivial, ← mulVec_mulVec, ← mulVec_mulVec, dot_sym C hCT]
      rw [this, h0, zero_mulVec, dotProduct_zero] at hpos
      exact lt_irrefl _ hpos

end Lemma38Aux

open Lemma38Aux in
theorem solution {n m : ℕ} (q : ℝ) (A : Fin m → Matrix (Fin n) (Fin n) ℝ)
    (hA : ∀ i, (A i).IsHermitian) (h31 : Assumption31 A) (hq : 2 < q)
    (S Z : Matrix (Fin n) (Fin n) ℝ) (M : Matrix (Fin m) (Fin m) ℝ)
    (hS : S.PosDef) (hZ : Z.PosSemidef) (hHZ : (gram A S Z).PosDef) (hM : M.PosDef) :
    let G := gramAdj A S M
    let Ψ := mpow (1 / 2 : ℝ) M * gram A S Z * mpow (1 / 2 : ℝ) M
    let Z₀ := primalOf q A S M
    (∀ hΨ : Ψ.IsHermitian,
      (∀ i, 0 < hΨ.eigenvalues i) ∧
      Fpr q A S Z + Fdu q A S M =
        ((1 / pExp q) * (mpow (pExp q) Z).trace + (1 / pDual q) * (mpow (pDual q) G).trace
          - (G * Z).trace) + ∑ i, rho (hΨ.eigenvalues i)) ∧
    0 ≤ Fpr q A S Z + Fdu q A S M ∧
    (Fpr q A S Z + Fdu q A S M = 0 ↔ (gramAdj A S M = mpow (pExp q - 1) Z ∧ M⁻¹ = gram A S Z)) ∧
    ((1 / pExp q) * (mpow (pExp q) Z₀).trace + (1 / pDual q) * (mpow (pDual q) G).trace
        - (G * Z₀).trace = 0 ∧
      (mpow (pDual q) G).trace = (gapMatrix q A S M).trace ∧
      Fpr q A S Z₀ + Fdu q A S M = gapDelta q A S M) := by
  intro G Ψ Z₀
  -- exponents
  have hq2 : 0 < q - 2 := by linarith
  have hp1 : 1 < pExp q := by
    unfold pExp
    rw [lt_div_iff₀ hq2]
    linarith
  have hp0 : 0 < pExp q := by linarith
  have hd0 : 0 < pDual q := by unfold pDual; linarith
  have hd1 : 0 < pDual q - 1 := by unfold pDual; linarith
  have hpp : pExp q / (pExp q - 1) = pDual q := by
    unfold pExp pDual
    field_simp
    ring
  have hsum : 1 / pExp q + 1 / pDual q = 1 := by
    unfold pExp pDual
    field_simp
    ring
  have hprod : (pDual q - 1) * pExp q = pDual q := by
    unfold pExp pDual
    field_simp

  -- the scaled matrices
  set R := mpow (-(1 / 2 : ℝ)) S with hRdef
  have hRpd : R.PosDef := mpow_posDef hS _
  have hRT : Rᵀ = R := herm_iff.mp hRpd.1
  have hRu : IsUnit R.det := isUnit_of_posDef hRpd
  have hBdef : ∀ i, scaled A S i = R * A i * R := fun i => rfl
  have hBT : ∀ i, (scaled A S i)ᵀ = scaled A S i := by
    intro i
    rw [hBdef, transpose_mul, transpose_mul, hRT, herm_iff.mp (hA i), Matrix.mul_assoc]
  have hlin : LinearIndependent ℝ (scaled A S) := by
    rw [Fintype.linearIndependent_iff]
    intro g hg
    have hsumA : R * (∑ i, g i • A i) * R = 0 := by
      rw [← hg]
      simp only [Finset.mul_sum, Finset.sum_mul, Matrix.mul_smul, Matrix.smul_mul, hBdef]
    have : ∑ i, g i • A i = 0 := by
      have h1 : R⁻¹ * (R * (∑ i, g i • A i) * R) * R⁻¹ = ∑ i, g i • A i := by
        simp only [← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hRu, Matrix.one_mul]
        rw [Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hRu, Matrix.mul_one]
      rw [← h1, hsumA, Matrix.mul_zero, Matrix.zero_mul]
    exact Fintype.linearIndependent_iff.mp h31.1 g this
  have hker : ∀ v, (∀ i, scaled A S i *ᵥ v = 0) → v = 0 := by
    intro v hv
    have hRinj : Function.Injective R.mulVec :=
      Matrix.mulVec_injective_iff_isUnit.mpr ((Matrix.isUnit_iff_isUnit_det R).mpr hRu)
    have h1 : ∀ i, A i *ᵥ (R *ᵥ v) = 0 := by
      intro i
      apply hRinj
      rw [mulVec_zero]
      have := hv i
      rw [hBdef, ← mulVec_mulVec, ← mulVec_mulVec] at this
      exact this
    have h2 := h31.2 (R *ᵥ v) h1
    apply hRinj
    rw [h2, mulVec_zero]
  -- the dual matrix
  have hGdef : G = ∑ i, ∑ j, M i j • sym (scaled A S i * scaled A S j) := rfl
  have hGpd : G.PosDef := by rw [hGdef]; exact adj_posDef _ hBT M hM hker
  have hGT : Gᵀ = G := herm_iff.mp hGpd.1
  have hadj : ∀ Z' : Matrix (Fin n) (Fin n) ℝ, Z'ᵀ = Z' → (G * Z').trace = (M * gram A S Z').trace := by
    intro Z' hZ'
    rw [hGdef]
    exact trace_adj _ hBT Z' hZ' M
  -- the square root of M
  set R2 := mpow (1 / 2 : ℝ) M with hR2def
  have hR2sq : R2 * R2 = M := mpow_half_mul hM.posSemidef
  have hR2h : R2.IsHermitian := mpow_herm hM.1 _
  have hR2u : IsUnit R2.det := isUnit_of_posDef (mpow_posDef hM _)
  have hMdet : 0 < M.det := hM.det_pos
  have htrΨ : ∀ Z' : Matrix (Fin n) (Fin n) ℝ, Z'ᵀ = Z' →
      (R2 * gram A S Z' * R2).trace = (G * Z').trace := by
    intro Z' hZ'
    rw [hadj Z' hZ', Matrix.trace_mul_comm, ← Matrix.mul_assoc, hR2sq]
  have ident : ∀ Z' : Matrix (Fin n) (Fin n) ℝ, Z'ᵀ = Z' → (gram A S Z').PosDef →
      (R2 * gram A S Z' * R2).PosDef ∧
      Fpr q A S Z' + Fdu q A S M =
        ((1 / pExp q) * (mpow (pExp q) Z').trace + (1 / pDual q) * (mpow (pDual q) G).trace
          - (G * Z').trace) +
        ((R2 * gram A S Z' * R2).trace - Real.log (R2 * gram A S Z' * R2).det - m) := by
    intro Z' hZ' hH'
    have hPD := posDef_conj_herm hR2h hR2u hH'
    refine ⟨hPD, ?_⟩
    have hdet : (R2 * gram A S Z' * R2).det = M.det * (gram A S Z').det := by
      rw [det_mul, det_mul, ← hR2sq, det_mul]
      ring
    have hlog : Real.log (R2 * gram A S Z' * R2).det =
        Real.log M.det + Real.log (gram A S Z').det := by
      rw [hdet, Real.log_mul hMdet.ne' hH'.det_pos.ne']
    rw [hlog, htrΨ Z' hZ']
    unfold Fpr Fdu
    ring
  have hZT : Zᵀ = Z := herm_iff.mp hZ.1
  obtain ⟨hΨpd, hid⟩ := ident Z hZT hHZ
  have hΨdef : Ψ = R2 * gram A S Z * R2 := rfl
  -- Young's inequality from Fact 3.6
  have hY := MatrixLewis.fact_3_6 (pExp q) hp1 G Z hGpd.posSemidef hZ
  dsimp only at hY
  rw [hpp] at hY
  obtain ⟨hY0, hYeq⟩ := hY
  have hrho := sum_rho hΨpd
  simp only [Fintype.card_fin] at hrho
  have hrho0 : ∀ i, 0 ≤ rho (hΨpd.1.eigenvalues i) := fun i => rho_nonneg (hΨpd.eigenvalues_pos i)
  have hsumrho0 : 0 ≤ ∑ i, rho (hΨpd.1.eigenvalues i) :=
    Finset.sum_nonneg (fun i _ => hrho0 i)
  have hFeq : Fpr q A S Z + Fdu q A S M =
      ((1 / pExp q) * (mpow (pExp q) Z).trace + (1 / pDual q) * (mpow (pDual q) G).trace
          - (G * Z).trace) + ∑ i, rho (hΨpd.1.eigenvalues i) := by
    rw [hid, hrho]
  -- Ψ = 1 ↔ M⁻¹ = H
  have hΨone : R2 * gram A S Z * R2 = 1 ↔ M⁻¹ = gram A S Z := by
    constructor
    · intro h1
      calc M⁻¹ = R2⁻¹ * R2⁻¹ := by rw [← hR2sq, Matrix.mul_inv_rev]
        _ = R2⁻¹ * (R2 * gram A S Z * R2) * R2⁻¹ := by rw [h1, Matrix.mul_one]
        _ = gram A S Z := by
          simp only [← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hR2u, Matrix.one_mul]
          rw [Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hR2u, Matrix.mul_one]
    · intro h1
      rw [← h1, ← hR2sq, Matrix.mul_inv_rev]
      simp only [← Matrix.mul_assoc]
      rw [Matrix.mul_nonsing_inv _ hR2u, Matrix.one_mul, Matrix.nonsing_inv_mul _ hR2u]
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro hΨ
    exact ⟨fun i => hΨpd.eigenvalues_pos i, hFeq⟩
  · rw [hFeq]
    linarith
  · constructor
    · intro h0
      rw [hFeq] at h0
      have hYz : (1 / pExp q) * (mpow (pExp q) Z).trace + (1 / pDual q) * (mpow (pDual q) G).trace
          - (G * Z).trace = 0 := by linarith
      have hRz : ∑ i, rho (hΨpd.1.eigenvalues i) = 0 := by linarith
      refine ⟨hYeq.mp hYz, hΨone.mp ?_⟩
      apply (eq_one_iff hΨpd.1).mpr
      intro i
      have := (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => hrho0 i)).mp hRz i (Finset.mem_univ _)
      exact (rho_eq_zero (hΨpd.eigenvalues_pos i)).mp this
    · rintro ⟨hG1, hM1⟩
      rw [hFeq, hYeq.mpr hG1, zero_add]
      apply Finset.sum_eq_zero
      intro i _
      have h1 := (eq_one_iff hΨpd.1).mp (hΨone.mpr hM1) i
      exact (rho_eq_zero (hΨpd.eigenvalues_pos i)).mpr h1
  · -- the primal point determined by M
    set UG := (hGpd.1.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℝ) with hUG
    set lG := hGpd.1.eigenvalues with hlG
    obtain ⟨hUGo, hUGo'⟩ : UGᵀ * UG = 1 ∧ UG * UGᵀ = 1 := orth hGpd.1
    have hl0 : ∀ i, 0 ≤ lG i := fun i => (hGpd.eigenvalues_pos i).le
    have hZ0def : Z₀ = mpow (pDual q - 1) G := rfl
    have hZ0rep : Z₀ = UG * diagonal (fun i => lG i ^ (pDual q - 1)) * UGᵀ := by
      rw [hZ0def]; unfold mpow; exact cfc_rep hGpd.1 _
    have hZ0pd : Z₀.PosDef := by rw [hZ0def]; exact mpow_posDef hGpd _
    have hZ0T : Z₀ᵀ = Z₀ := herm_iff.mp hZ0pd.1
    have hH0 : (gram A S Z₀).PosDef := gram_posDef _ hBT hlin Z₀ hZ0pd
    set T := ∑ i, lG i ^ pDual q with hT
    have hTG : (mpow (pDual q) G).trace = T := by
      unfold mpow
      rw [cfc_rep hGpd.1, trace_conj_diag _ hUGo]
    have hTZ : (mpow (pExp q) Z₀).trace = T := by
      have hc : mpow (pExp q) Z₀ =
          cfc ((fun t : ℝ => t ^ pExp q) ∘ (fun t : ℝ => t ^ (pDual q - 1))) G := by
        rw [hZ0def]
        unfold mpow
        rw [cfc_comp (fun t : ℝ => t ^ pExp q) (fun t : ℝ => t ^ (pDual q - 1)) G
          hGpd.1.isSelfAdjoint (Real.continuous_rpow_const hp0.le).continuousOn
          (Real.continuous_rpow_const hd1.le).continuousOn]
      rw [hc, cfc_rep hGpd.1, trace_conj_diag _ hUGo]
      apply Finset.sum_congr rfl
      intro i _
      simp only [Function.comp_apply]
      rw [← Real.rpow_mul (hl0 i), hprod]
    have hTGZ : (G * Z₀).trace = T := by
      have hGrep : G = UG * diagonal (fun i => lG i) * UGᵀ := self_rep hGpd.1
      rw [hZ0rep]
      conv_lhs => rw [hGrep]
      rw [conj_diag_mul _ hUGo, trace_conj_diag _ hUGo]
      apply Finset.sum_congr rfl
      intro i _
      rw [mul_comm]
      exact rpow_sub_one_mul (hl0 i) hd0
    have hgap : gapMatrix q A S M = R2 * gram A S Z₀ * R2 := rfl
    have hY0 : (1 / pExp q) * (mpow (pExp q) Z₀).trace + (1 / pDual q) * (mpow (pDual q) G).trace
        - (G * Z₀).trace = 0 := by
      rw [hTZ, hTG, hTGZ]
      linear_combination T * hsum
    refine ⟨hY0, ?_, ?_⟩
    · rw [hTG, hgap, htrΨ Z₀ hZ0T, hTGZ]
    · obtain ⟨_, hid0⟩ := ident Z₀ hZ0T hH0
      rw [hid0, hY0, zero_add]
      unfold gapDelta
      rw [hgap]
