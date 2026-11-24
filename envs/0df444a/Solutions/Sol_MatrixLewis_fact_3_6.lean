-- Prove2me | solution 1 for MatrixLewis.fact_3_6
-- status  : ACCEPTED   (prove)
-- author  : @CGTMoyano
-- created : 2026-11-24T18:58:19.20181+00:00
-- url     : https://prove2.me/submissions/651f11d8-82d6-407c-b96f-b30387462ca6

import Mathlib
import Definitions.Def_MatrixLewis_mpow

open MatrixLewis Matrix

namespace MatrixYoungAux

/-- Equality case of the scalar Young inequality. -/
theorem young_eq {p x y : ℝ} (hp : 1 < p) (hx : 0 ≤ x) (hy : 0 ≤ y)
    (h : x * y = x ^ p / p + y ^ (p / (p - 1)) / (p / (p - 1))) : y = x ^ (p - 1) := by
  set q := p / (p - 1) with hq
  have hp0 : 0 < p := by linarith
  have hp1 : 0 < p - 1 := by linarith
  have hq0 : 0 < q := div_pos hp0 hp1
  have hw : ∀ i ∈ (Finset.univ : Finset (Fin 2)), 0 < (![1 / p, 1 / q] : Fin 2 → ℝ) i := by
    intro i _
    fin_cases i
    · simp [hp0]
    · simp [hq0]
  have hw' : ∑ i, (![1 / p, 1 / q] : Fin 2 → ℝ) i = 1 := by
    rw [Fin.sum_univ_two]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
    rw [hq]
    field_simp
    ring
  have hz : ∀ i ∈ (Finset.univ : Finset (Fin 2)), 0 ≤ (![x ^ p, y ^ q] : Fin 2 → ℝ) i := by
    intro i _
    fin_cases i
    · simp [Real.rpow_nonneg hx]
    · simp [Real.rpow_nonneg hy]
  have e1 : (x ^ p) ^ (1 / p) = x := by rw [one_div]; exact Real.rpow_rpow_inv hx hp0.ne'
  have e2 : (y ^ q) ^ (1 / q) = y := by rw [one_div]; exact Real.rpow_rpow_inv hy hq0.ne'
  have heq : ∏ i, (![x ^ p, y ^ q] : Fin 2 → ℝ) i ^ (![1 / p, 1 / q] : Fin 2 → ℝ) i =
      ∑ i, (![1 / p, 1 / q] : Fin 2 → ℝ) i * (![x ^ p, y ^ q] : Fin 2 → ℝ) i := by
    rw [Fin.prod_univ_two, Fin.sum_univ_two]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
    rw [e1, e2, h]
    ring
  have key := (Real.geom_mean_eq_arith_mean_weighted_iff_of_pos Finset.univ _ _ hw hw' hz).mp heq
  have hxy : x ^ p = y ^ q := by
    have := key 0 (Finset.mem_univ _) 1 (Finset.mem_univ _)
    simpa using this
  calc y = (y ^ q) ^ q⁻¹ := (Real.rpow_rpow_inv hy hq0.ne').symm
    _ = (x ^ p) ^ q⁻¹ := by rw [hxy]
    _ = x ^ (p * q⁻¹) := (Real.rpow_mul hx _ _).symm
    _ = x ^ (p - 1) := by
      congr 1
      rw [hq]
      field_simp

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The functional calculus of a real symmetric matrix in its eigenbasis. -/
theorem cfc_rep {A : Matrix n n ℝ} (hA : A.IsHermitian) (f : ℝ → ℝ) :
    cfc f A = (hA.eigenvectorUnitary : Matrix n n ℝ) *
      diagonal (fun i => f (hA.eigenvalues i)) * (hA.eigenvectorUnitary : Matrix n n ℝ)ᵀ := by
  rw [hA.cfc_eq, Matrix.IsHermitian.cfc, Unitary.conjStarAlgAut_apply]
  simp [Matrix.star_eq_conjTranspose, Function.comp_def]

theorem self_rep {A : Matrix n n ℝ} (hA : A.IsHermitian) :
    A = (hA.eigenvectorUnitary : Matrix n n ℝ) *
      diagonal (fun i => hA.eigenvalues i) * (hA.eigenvectorUnitary : Matrix n n ℝ)ᵀ := by
  rw [← cfc_rep hA (fun t => t)]
  exact (cfc_id' ℝ A hA.isSelfAdjoint).symm

theorem orth {A : Matrix n n ℝ} (hA : A.IsHermitian) :
    (hA.eigenvectorUnitary : Matrix n n ℝ)ᵀ * (hA.eigenvectorUnitary : Matrix n n ℝ) = 1 ∧
      (hA.eigenvectorUnitary : Matrix n n ℝ) * (hA.eigenvectorUnitary : Matrix n n ℝ)ᵀ = 1 := by
  have h1 := Unitary.coe_star_mul_self hA.eigenvectorUnitary
  have h2 := Unitary.coe_mul_star_self hA.eigenvectorUnitary
  simp only [Unitary.coe_star, Matrix.star_eq_conjTranspose,
    Matrix.conjTranspose_eq_transpose_of_trivial] at h1 h2
  exact ⟨h1, h2⟩

theorem trace_conj (U M : Matrix n n ℝ) (hU : Uᵀ * U = 1) : trace (U * M * Uᵀ) = trace M := by
  rw [Matrix.trace_mul_comm, ← Matrix.mul_assoc, hU, Matrix.one_mul]

theorem trace_conj_diag (U : Matrix n n ℝ) (hU : Uᵀ * U = 1) (f : n → ℝ) :
    trace (U * diagonal f * Uᵀ) = ∑ i, f i := by
  rw [trace_conj U _ hU, Matrix.trace_diagonal]

/-- Trace of a product of two matrices given in orthonormal eigenbases. -/
theorem trace_prod (U V : Matrix n n ℝ) (hV : Vᵀ * V = 1) (hV' : V * Vᵀ = 1)
    (lam mu : n → ℝ) :
    trace ((V * diagonal mu * Vᵀ) * (U * diagonal lam * Uᵀ)) =
      ∑ j, ∑ i, mu j * lam i * (Vᵀ * U) j i ^ 2 := by
  have hP : (V * diagonal mu * Vᵀ) * (U * diagonal lam * Uᵀ) =
      V * (diagonal mu * (Vᵀ * U) * diagonal lam * (Vᵀ * U)ᵀ) * Vᵀ := by
    simp only [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.mul_assoc, hV',
      Matrix.mul_one]
  rw [hP, trace_conj V _ hV]
  generalize Vᵀ * U = W
  have hM : ∀ j i, (diagonal mu * W * diagonal lam) j i = mu j * W j i * lam i := by
    intro j i
    rw [Matrix.mul_diagonal, Matrix.diagonal_mul]
  simp only [Matrix.trace, Matrix.diag]
  apply Finset.sum_congr rfl
  intro j _
  rw [Matrix.mul_apply]
  apply Finset.sum_congr rfl
  intro i _
  rw [hM, Matrix.transpose_apply]
  ring

theorem row_sum (U V : Matrix n n ℝ) (hU' : U * Uᵀ = 1) (hV : Vᵀ * V = 1) (j : n) :
    ∑ i, (Vᵀ * U) j i ^ 2 = 1 := by
  have h : (Vᵀ * U) * (Vᵀ * U)ᵀ = 1 := by
    simp only [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.mul_assoc]
    rw [← Matrix.mul_assoc U, hU', Matrix.one_mul, hV]
  have := congrFun (congrFun h j) j
  rw [Matrix.mul_apply, Matrix.one_apply_eq] at this
  rw [← this]
  apply Finset.sum_congr rfl
  intro i _
  rw [Matrix.transpose_apply]
  ring

theorem col_sum (U V : Matrix n n ℝ) (hU : Uᵀ * U = 1) (hV' : V * Vᵀ = 1) (i : n) :
    ∑ j, (Vᵀ * U) j i ^ 2 = 1 := by
  have h : (Vᵀ * U)ᵀ * (Vᵀ * U) = 1 := by
    simp only [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.mul_assoc]
    rw [← Matrix.mul_assoc V, hV', Matrix.one_mul, hU]
  have := congrFun (congrFun h i) i
  rw [Matrix.mul_apply, Matrix.one_apply_eq] at this
  rw [← this]
  apply Finset.sum_congr rfl
  intro j _
  rw [Matrix.transpose_apply]
  ring

theorem rpow_sub_one_mul {x p : ℝ} (hx : 0 ≤ x) (hp : 0 < p) : x ^ (p - 1) * x = x ^ p := by
  rcases hx.eq_or_lt with h | h
  · rw [← h, mul_zero, Real.zero_rpow hp.ne']
  · rw [Real.rpow_sub_one h.ne']
    field_simp

end MatrixYoungAux

open MatrixYoungAux in
theorem solution {n : ℕ} (p : ℝ) (hp : 1 < p) (A Z : Matrix (Fin n) (Fin n) ℝ)
    (hA : A.PosSemidef) (hZ : Z.PosSemidef) :
    let p' := p / (p - 1)
    0 ≤ (1 / p) * (mpow p Z).trace + (1 / p') * (mpow p' A).trace - (A * Z).trace ∧
      ((1 / p) * (mpow p Z).trace + (1 / p') * (mpow p' A).trace - (A * Z).trace = 0 ↔
        A = mpow (p - 1) Z) := by
  intro p'
  have hp0 : 0 < p := by linarith
  have hp1 : 0 < p - 1 := by linarith
  have hq0 : 0 < p' := div_pos hp0 hp1
  have hconj : p.HolderConjugate p' := Real.HolderConjugate.conjExponent hp
  set U := (hZ.1.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℝ) with hUdef
  set V := (hA.1.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℝ) with hVdef
  set lam := hZ.1.eigenvalues with hlam
  set mu := hA.1.eigenvalues with hmu
  have hlam0 : ∀ i, 0 ≤ lam i := hZ.eigenvalues_nonneg
  have hmu0 : ∀ j, 0 ≤ mu j := hA.eigenvalues_nonneg
  obtain ⟨hU, hU'⟩ : Uᵀ * U = 1 ∧ U * Uᵀ = 1 := orth hZ.1
  obtain ⟨hV, hV'⟩ : Vᵀ * V = 1 ∧ V * Vᵀ = 1 := orth hA.1
  have hZrep : Z = U * diagonal lam * Uᵀ := self_rep hZ.1
  have hArep : A = V * diagonal mu * Vᵀ := self_rep hA.1
  have htrZ : (mpow p Z).trace = ∑ i, lam i ^ p := by
    unfold mpow
    rw [cfc_rep hZ.1, trace_conj_diag _ hU]
  have htrA : (mpow p' A).trace = ∑ j, mu j ^ p' := by
    unfold mpow
    rw [cfc_rep hA.1, trace_conj_diag _ hV]
  set W := Vᵀ * U with hW
  have htrAZ : (A * Z).trace = ∑ j, ∑ i, mu j * lam i * W j i ^ 2 := by
    conv_lhs => rw [hArep, hZrep]
    exact trace_prod U V hV hV' lam mu
  -- the deficit as a doubly stochastic average of scalar Young deficits
  set Dl : Fin n → Fin n → ℝ := fun j i => lam i ^ p / p + mu j ^ p' / p' - lam i * mu j with hDl
  have hD0 : ∀ j i, 0 ≤ Dl j i := by
    intro j i
    have := Real.young_inequality_of_nonneg (hlam0 i) (hmu0 j) hconj
    simp only [hDl]
    linarith
  have hexpr : (1 / p) * (mpow p Z).trace + (1 / p') * (mpow p' A).trace - (A * Z).trace =
      ∑ j, ∑ i, W j i ^ 2 * Dl j i := by
    rw [htrZ, htrA, htrAZ]
    have h1 : (1 / p) * ∑ i, lam i ^ p = ∑ j, ∑ i, W j i ^ 2 * (lam i ^ p / p) := by
      rw [Finset.sum_comm, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      rw [← Finset.sum_mul, col_sum U V hU hV' i]
      ring
    have h2 : (1 / p') * ∑ j, mu j ^ p' = ∑ j, ∑ i, W j i ^ 2 * (mu j ^ p' / p') := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      rw [← Finset.sum_mul, row_sum U V hU' hV j]
      ring
    rw [h1, h2, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro j _
    rw [← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i _
    simp only [hDl]
    ring
  have hterm0 : ∀ j i, 0 ≤ W j i ^ 2 * Dl j i := fun j i => mul_nonneg (sq_nonneg _) (hD0 j i)
  refine ⟨?_, ?_⟩
  · rw [hexpr]
    exact Finset.sum_nonneg (fun j _ => Finset.sum_nonneg (fun i _ => hterm0 j i))
  constructor
  · intro h0
    rw [hexpr] at h0
    have hzero : ∀ j i, W j i ^ 2 * Dl j i = 0 := by
      intro j i
      have hj := (Finset.sum_eq_zero_iff_of_nonneg
        (fun j _ => Finset.sum_nonneg (fun i _ => hterm0 j i))).mp h0 j (Finset.mem_univ _)
      exact (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => hterm0 j i)).mp hj i
        (Finset.mem_univ _)
    have hmatch : ∀ j i, W j i ≠ 0 → mu j = lam i ^ (p - 1) := by
      intro j i hWji
      have hD : Dl j i = 0 := by
        rcases mul_eq_zero.mp (hzero j i) with h | h
        · exact absurd ((pow_eq_zero_iff two_ne_zero).mp h) hWji
        · exact h
      simp only [hDl] at hD
      exact young_eq hp (hlam0 i) (hmu0 j)
        (by change lam i * mu j = lam i ^ p / p + mu j ^ p' / p'; linarith)
    have hcomm : diagonal mu * W = W * diagonal (fun i => lam i ^ (p - 1)) := by
      ext j i
      rw [Matrix.diagonal_mul, Matrix.mul_diagonal]
      by_cases hWji : W j i = 0
      · rw [hWji]; ring
      · rw [hmatch j i hWji]; ring
    have hpow : mpow (p - 1) Z = U * diagonal (fun i => lam i ^ (p - 1)) * Uᵀ := by
      unfold mpow
      exact cfc_rep hZ.1 _
    rw [hpow]
    calc A = V * diagonal mu * Vᵀ := hArep
      _ = V * (diagonal mu * W) * Uᵀ := by
        simp only [hW, Matrix.mul_assoc, hU', Matrix.mul_one]
      _ = V * (W * diagonal (fun i => lam i ^ (p - 1))) * Uᵀ := by rw [hcomm]
      _ = U * diagonal (fun i => lam i ^ (p - 1)) * Uᵀ := by
        simp only [hW, ← Matrix.mul_assoc, hV', Matrix.one_mul]
  · intro hAZ
    have hpow : mpow (p - 1) Z = U * diagonal (fun i => lam i ^ (p - 1)) * Uᵀ := by
      unfold mpow
      exact cfc_rep hZ.1 _
    have htrA' : (mpow p' A).trace = ∑ i, lam i ^ p := by
      have hc : mpow p' A = cfc ((fun t : ℝ => t ^ p') ∘ (fun t : ℝ => t ^ (p - 1))) Z := by
        unfold mpow
        rw [hAZ]
        unfold mpow
        rw [cfc_comp (fun t : ℝ => t ^ p') (fun t : ℝ => t ^ (p - 1)) Z hZ.1.isSelfAdjoint
          (Real.continuous_rpow_const hq0.le).continuousOn
          (Real.continuous_rpow_const hp1.le).continuousOn]
      rw [hc, cfc_rep hZ.1, trace_conj_diag _ hU]
      apply Finset.sum_congr rfl
      intro i _
      simp only [Function.comp_apply]
      rw [← Real.rpow_mul (hlam0 i)]
      congr 1
      simp only [p']
      field_simp
    have htrAZ' : (A * Z).trace = ∑ i, lam i ^ p := by
      rw [hAZ, hpow]
      conv_lhs => rw [hZrep]
      have : U * diagonal (fun i => lam i ^ (p - 1)) * Uᵀ * (U * diagonal lam * Uᵀ) =
          U * diagonal (fun i => lam i ^ (p - 1) * lam i) * Uᵀ := by
        rw [← Matrix.diagonal_mul_diagonal]
        simp only [Matrix.mul_assoc]
        rw [← Matrix.mul_assoc Uᵀ U, hU, Matrix.one_mul]
      rw [this, trace_conj_diag _ hU]
      apply Finset.sum_congr rfl
      intro i _
      exact rpow_sub_one_mul (hlam0 i) hp0
    rw [htrZ, htrA', htrAZ']
    have : 1 / p' = (p - 1) / p := by simp only [p']; field_simp
    rw [this]
    field_simp
    ring
