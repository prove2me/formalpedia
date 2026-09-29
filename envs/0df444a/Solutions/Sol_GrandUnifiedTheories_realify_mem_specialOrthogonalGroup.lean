-- Prove2me | solution 1 for GrandUnifiedTheories.realify_mem_specialOrthogonalGroup
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-24T07:13:39.442187+00:00
-- url     : https://prove2.me/submissions/30854fa6-58c2-4c95-8534-c40289b671c4

import Mathlib
import Definitions.Def_GUT_standard_model_group
import Definitions.Def_GUT_realification

open GrandUnifiedTheories
open Matrix

/-- Realification of a complex square matrix indexed by any finite type. -/
noncomputable def W7b_GrandUnifiedTheories_rN {n : Type} (A : Matrix n n ℂ) :
    Matrix (n × Fin 2) (n × Fin 2) ℝ :=
  Matrix.of (fun p q => realEntry (A p.1 q.1) p.2 q.2)

theorem W7b_GrandUnifiedTheories_rN_mul {n : Type} [Fintype n] (A B : Matrix n n ℂ) :
    W7b_GrandUnifiedTheories_rN (A * B) =
      W7b_GrandUnifiedTheories_rN A * W7b_GrandUnifiedTheories_rN B := by
  have hsum : ∀ (s t : Fin 2) (f : n → ℂ),
      realEntry (∑ k, f k) s t = ∑ k, realEntry (f k) s t := by
    intro s t f
    fin_cases s <;> fin_cases t <;> simp [realEntry, Complex.re_sum, Complex.im_sum]
  have hmul : ∀ (s t : Fin 2) (z w : ℂ),
      realEntry (z * w) s t = ∑ u, realEntry z s u * realEntry w u t := by
    intro s t z w
    fin_cases s <;> fin_cases t <;> simp [realEntry, Fin.sum_univ_two] <;> ring
  ext x y
  simp only [W7b_GrandUnifiedTheories_rN, Matrix.of_apply, Matrix.mul_apply, hsum, hmul]
  rw [Fintype.sum_prod_type]

theorem W7b_GrandUnifiedTheories_rN_one {n : Type} [DecidableEq n] :
    W7b_GrandUnifiedTheories_rN (1 : Matrix n n ℂ) = 1 := by
  ext ⟨i, s⟩ ⟨j, t⟩
  by_cases hij : i = j
  · subst hij
    fin_cases s <;> fin_cases t <;> simp [W7b_GrandUnifiedTheories_rN, realEntry, Matrix.one_apply]
  · simp [W7b_GrandUnifiedTheories_rN, realEntry, Matrix.one_apply, hij]

theorem W7b_GrandUnifiedTheories_rN_conjTranspose {n : Type} (A : Matrix n n ℂ) :
    W7b_GrandUnifiedTheories_rN Aᴴ = (W7b_GrandUnifiedTheories_rN A)ᵀ := by
  ext ⟨i, s⟩ ⟨j, t⟩
  simp only [W7b_GrandUnifiedTheories_rN, Matrix.of_apply, Matrix.transpose_apply,
    Matrix.conjTranspose_apply]
  fin_cases s <;> fin_cases t <;> simp [realEntry]

/-- The ℝ-basis `(e_j, i e_j)` of `ℂⁿ`. -/
noncomputable def W7b_GrandUnifiedTheories_B (n : Type) [Fintype n] [DecidableEq n] :
    Module.Basis (n × Fin 2) ℝ (n → ℂ) :=
  Complex.basisOneI.smulTower' (Pi.basisFun ℂ n)

theorem W7b_GrandUnifiedTheories_toMatrix {n : Type} [Fintype n] [DecidableEq n]
    (A : Matrix n n ℂ) :
    LinearMap.toMatrix (W7b_GrandUnifiedTheories_B n) (W7b_GrandUnifiedTheories_B n)
        ((Matrix.toLin' A).restrictScalars ℝ) = W7b_GrandUnifiedTheories_rN A := by
  ext ⟨i, s⟩ ⟨j, t⟩
  rw [LinearMap.toMatrix_apply, W7b_GrandUnifiedTheories_B, Module.Basis.smulTower'_repr,
    Module.Basis.smulTower'_apply]
  simp only [LinearMap.restrictScalars_apply, Matrix.toLin'_apply, Pi.basisFun_apply,
    Pi.basisFun_repr, Complex.coe_basisOneI, Complex.coe_basisOneI_repr,
    W7b_GrandUnifiedTheories_rN, Matrix.of_apply]
  have : A.mulVec ((![(1 : ℂ), Complex.I] t) • Pi.single j (1 : ℂ)) i =
      A i j * ![(1 : ℂ), Complex.I] t := by
    simp [Matrix.mulVec, dotProduct, Pi.single_apply, mul_comm]
  rw [this]
  fin_cases s <;> fin_cases t <;> simp [realEntry]

theorem W7b_GrandUnifiedTheories_det_rN {n : Type} [Fintype n] [DecidableEq n]
    (A : Matrix n n ℂ) :
    (W7b_GrandUnifiedTheories_rN A).det = Complex.normSq A.det := by
  rw [← W7b_GrandUnifiedTheories_toMatrix, LinearMap.det_toMatrix, LinearMap.det_restrictScalars,
    LinearMap.det_toLin', Algebra.norm_complex_apply]

theorem W7b_GrandUnifiedTheories_rN_mem {n : Type} [Fintype n] [DecidableEq n]
    (A : Matrix n n ℂ) (hA : A ∈ Matrix.unitaryGroup n ℂ) :
    W7b_GrandUnifiedTheories_rN A ∈ Matrix.specialOrthogonalGroup (n × Fin 2) ℝ := by
  rw [Matrix.mem_specialOrthogonalGroup_iff]
  refine ⟨?_, ?_⟩
  · rw [Matrix.mem_orthogonalGroup_iff]
    have hU := hA
    rw [Matrix.mem_unitaryGroup_iff] at hU
    have : W7b_GrandUnifiedTheories_rN (A * star A) = 1 := by
      rw [hU, W7b_GrandUnifiedTheories_rN_one]
    rw [W7b_GrandUnifiedTheories_rN_mul, Matrix.star_eq_conjTranspose,
      W7b_GrandUnifiedTheories_rN_conjTranspose] at this
    exact this
  · rw [W7b_GrandUnifiedTheories_det_rN]
    have hd := Matrix.det_of_mem_unitary hA
    have hn : ‖A.det‖ = 1 := CStarRing.norm_of_mem_unitary hd
    rw [Complex.normSq_eq_norm_sq, hn, one_pow]

/-- The reindexing `Idx10 ≃ Idx5 × Fin 2`. -/
def W7b_GrandUnifiedTheories_e : Idx10 ≃ Idx5 × Fin 2 :=
  { toFun := idx10ToC
    invFun := fun p => match p with
      | (Sum.inl i, s) => Sum.inl (i, s)
      | (Sum.inr j, s) => Sum.inr (j, s)
    left_inv := by rintro (⟨i, s⟩ | ⟨j, s⟩) <;> rfl
    right_inv := by rintro (⟨i | j, s⟩) <;> rfl }

theorem W7b_GrandUnifiedTheories_realify_eq (A : Matrix Idx5 Idx5 ℂ) :
    realify A = (W7b_GrandUnifiedTheories_rN A).submatrix W7b_GrandUnifiedTheories_e
      W7b_GrandUnifiedTheories_e := by
  ext x y; rfl

theorem solution (A : Matrix Idx5 Idx5 ℂ)
    (hA : A ∈ Matrix.specialUnitaryGroup Idx5 ℂ) :
    realify A ∈ Matrix.specialOrthogonalGroup Idx10 ℝ := by
  have hU : A ∈ Matrix.unitaryGroup Idx5 ℂ := (Matrix.mem_specialUnitaryGroup_iff.mp hA).1
  have hM := W7b_GrandUnifiedTheories_rN_mem A hU
  rw [Matrix.mem_specialOrthogonalGroup_iff, Matrix.mem_orthogonalGroup_iff] at hM ⊢
  rw [W7b_GrandUnifiedTheories_realify_eq]
  refine ⟨?_, ?_⟩
  · rw [Matrix.transpose_submatrix, Matrix.submatrix_mul_equiv, hM.1, Matrix.submatrix_one_equiv]
  · rw [Matrix.det_submatrix_equiv_self, hM.2]

theorem W7b_GrandUnifiedTheories_star (a : Circle) : star (a : ℂ) = (a : ℂ)⁻¹ := by
  rw [← Circle.coe_inv, Circle.coe_inv_eq_conj]; rfl

theorem W7b_GrandUnifiedTheories_conj (a : Circle) : (starRingEnd ℂ) (a : ℂ) = (a : ℂ)⁻¹ := by
  rw [← Circle.coe_inv_eq_conj, Circle.coe_inv]

theorem W7b_GrandUnifiedTheories_smul_mem {n : Type} [Fintype n] [DecidableEq n]
    (b : Circle) {P : Matrix n n ℂ} (hP : P ∈ Matrix.unitaryGroup n ℂ) :
    (b : ℂ) • P ∈ Matrix.unitaryGroup n ℂ := by
  rw [Matrix.mem_unitaryGroup_iff] at hP ⊢
  rw [star_smul, Matrix.smul_mul, Matrix.mul_smul, smul_smul, hP, W7b_GrandUnifiedTheories_star,
    mul_inv_cancel₀ (Circle.coe_ne_zero b), one_smul]

theorem W7b_GrandUnifiedTheories_fromBlocks_mem {m n : Type} [Fintype m] [DecidableEq m]
    [Fintype n] [DecidableEq n] {P : Matrix m m ℂ} {Q : Matrix n n ℂ}
    (hP : P ∈ Matrix.unitaryGroup m ℂ) (hQ : Q ∈ Matrix.unitaryGroup n ℂ) :
    Matrix.fromBlocks P 0 0 Q ∈ Matrix.unitaryGroup (m ⊕ n) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose] at hP hQ ⊢
  rw [Matrix.fromBlocks_conjTranspose, Matrix.fromBlocks_multiply]
  simp [hP, hQ]

theorem W7b_GrandUnifiedTheories_phi_mem_specialUnitaryGroup (x : GSM) :
    phiMatrix x ∈ Matrix.specialUnitaryGroup Idx5 ℂ := by
  obtain ⟨a, g, h⟩ := x
  have ha := Circle.coe_ne_zero a
  have hg := Matrix.mem_specialUnitaryGroup_iff.mp g.2
  have hh := Matrix.mem_specialUnitaryGroup_iff.mp h.2
  refine Matrix.mem_specialUnitaryGroup_iff.mpr ⟨?_, ?_⟩
  · have e1 : ((a : ℂ) ^ 3) = ((a ^ 3 : Circle) : ℂ) := by simp
    have e2 : (((a⁻¹ : Circle) : ℂ) ^ 2) = ((a⁻¹ ^ 2 : Circle) : ℂ) := by simp
    simp only [phiMatrix]
    rw [e1, e2]
    exact W7b_GrandUnifiedTheories_fromBlocks_mem (W7b_GrandUnifiedTheories_smul_mem _ hg.1)
      (W7b_GrandUnifiedTheories_smul_mem _ hh.1)
  · simp only [phiMatrix]
    rw [Matrix.det_fromBlocks_zero₂₁, Matrix.det_smul, Matrix.det_smul, hg.2, hh.2]
    simp only [Fintype.card_fin, Circle.coe_inv, mul_one]
    calc ((a : ℂ) ^ 3) ^ 2 * (((a : ℂ)⁻¹) ^ 2) ^ 3 = ((a : ℂ) * (a : ℂ)⁻¹) ^ 6 := by ring
      _ = 1 := by rw [mul_inv_cancel₀ ha, one_pow]


theorem W7b_GrandUnifiedTheories_phi_range_eq (A : Matrix Idx5 Idx5 ℂ) :
    (∃ x : GSM, phiMatrix x = A) ↔
      (A ∈ Matrix.specialUnitaryGroup Idx5 ℂ ∧
        ∀ i j, A (Sum.inl i) (Sum.inr j) = 0 ∧ A (Sum.inr j) (Sum.inl i) = 0) := by
  constructor
  · rintro ⟨x, rfl⟩
    exact ⟨W7b_GrandUnifiedTheories_phi_mem_specialUnitaryGroup x,
      fun i j => ⟨by simp [phiMatrix], by simp [phiMatrix]⟩⟩
  · rintro ⟨hA, hblk⟩
    obtain ⟨hU, hdet⟩ := Matrix.mem_specialUnitaryGroup_iff.mp hA
    have hAeq : A = Matrix.fromBlocks A.toBlocks₁₁ 0 0 A.toBlocks₂₂ := by
      ext i j
      rcases i with i | i <;> rcases j with j | j
      · rfl
      · simp [(hblk i j).1]
      · simp [(hblk j i).2]
      · rfl
    generalize A.toBlocks₁₁ = P at hAeq
    generalize A.toBlocks₂₂ = Q at hAeq
    subst hAeq
    have hPU : P ∈ Matrix.unitaryGroup (Fin 2) ℂ ∧ Q ∈ Matrix.unitaryGroup (Fin 3) ℂ := by
      rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose,
        Matrix.fromBlocks_conjTranspose, Matrix.fromBlocks_multiply] at hU
      simp only [Matrix.conjTranspose_zero, Matrix.mul_zero, Matrix.zero_mul, add_zero,
        zero_add] at hU
      rw [← Matrix.fromBlocks_one, Matrix.fromBlocks_inj] at hU
      simp only [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose]
      exact ⟨hU.1, hU.2.2.2⟩
    have hdet' : P.det * Q.det = 1 := by rwa [Matrix.det_fromBlocks_zero₂₁] at hdet
    have hnorm : ‖P.det‖ = 1 := CStarRing.norm_of_mem_unitary (Matrix.det_of_mem_unitary hPU.1)
    set w : Circle := Circle.exp (Complex.arg P.det / 6) with hwdef
    have hw : (w : ℂ) ^ 6 = P.det := by
      rw [hwdef, Circle.coe_exp, ← Complex.exp_nat_mul]
      have h := Complex.norm_mul_exp_arg_mul_I P.det
      rw [hnorm, Complex.ofReal_one, one_mul] at h
      calc Complex.exp (((6 : ℕ) : ℂ) * (((Complex.arg P.det / 6 : ℝ)) * Complex.I))
          = Complex.exp (Complex.arg P.det * Complex.I) := by congr 1; push_cast; ring
        _ = P.det := h
    have hw0 := Circle.coe_ne_zero w
    have hgmem : ((w⁻¹ ^ 3 : Circle) : ℂ) • P ∈ Matrix.specialUnitaryGroup (Fin 2) ℂ := by
      refine Matrix.mem_specialUnitaryGroup_iff.mpr
        ⟨W7b_GrandUnifiedTheories_smul_mem _ hPU.1, ?_⟩
      rw [Matrix.det_smul, Fintype.card_fin, Circle.coe_pow, Circle.coe_inv, ← hw]
      calc (((w : ℂ)⁻¹) ^ 3) ^ 2 * (w : ℂ) ^ 6 = ((w : ℂ)⁻¹ * w) ^ 6 := by ring
        _ = 1 := by rw [inv_mul_cancel₀ hw0, one_pow]
    have hhmem : ((w ^ 2 : Circle) : ℂ) • Q ∈ Matrix.specialUnitaryGroup (Fin 3) ℂ := by
      refine Matrix.mem_specialUnitaryGroup_iff.mpr
        ⟨W7b_GrandUnifiedTheories_smul_mem _ hPU.2, ?_⟩
      rw [Matrix.det_smul, Fintype.card_fin, Circle.coe_pow]
      calc ((w : ℂ) ^ 2) ^ 3 * Q.det = (w : ℂ) ^ 6 * Q.det := by ring
        _ = 1 := by rw [hw, hdet']
    refine ⟨(w, ⟨_, hgmem⟩, ⟨_, hhmem⟩), ?_⟩
    simp only [phiMatrix]
    congr 1
    · rw [smul_smul, Circle.coe_pow, Circle.coe_inv, ← mul_pow, mul_inv_cancel₀ hw0, one_pow,
        one_smul]
    · rw [smul_smul, Circle.coe_pow, Circle.coe_inv, ← mul_pow, inv_mul_cancel₀ hw0, one_pow,
        one_smul]


theorem W7b_GrandUnifiedTheories_gsm_eq_su5_inter_so4_so6 (M : Matrix Idx10 Idx10 ℝ) :
    ((∃ A : Matrix Idx5 Idx5 ℂ, A ∈ Matrix.specialUnitaryGroup Idx5 ℂ ∧ realify A = M) ∧
        (∃ P Q, P ∈ Matrix.specialOrthogonalGroup (Fin 2 × Fin 2) ℝ ∧
          Q ∈ Matrix.specialOrthogonalGroup (Fin 3 × Fin 2) ℝ ∧
          M = Matrix.fromBlocks P 0 0 Q)) ↔
      ∃ x : GSM, realify (phiMatrix x) = M := by
  constructor
  · rintro ⟨⟨A, hA, rfl⟩, ⟨P, Q, -, -, hPQ⟩⟩
    have hblk : ∀ i j, A (Sum.inl i) (Sum.inr j) = 0 ∧ A (Sum.inr j) (Sum.inl i) = 0 := by
      intro i j
      have h1 := congrFun (congrFun hPQ (Sum.inl (i, 0))) (Sum.inr (j, 0))
      have h2 := congrFun (congrFun hPQ (Sum.inl (i, 1))) (Sum.inr (j, 0))
      have h3 := congrFun (congrFun hPQ (Sum.inr (j, 0))) (Sum.inl (i, 0))
      have h4 := congrFun (congrFun hPQ (Sum.inr (j, 1))) (Sum.inl (i, 0))
      simp [realify, idx10ToC, realEntry] at h1 h2 h3 h4
      exact ⟨Complex.ext h1 h2, Complex.ext h3 h4⟩
    obtain ⟨x, hx⟩ := (W7b_GrandUnifiedTheories_phi_range_eq A).mpr ⟨hA, hblk⟩
    exact ⟨x, by rw [hx]⟩
  · rintro ⟨x, rfl⟩
    refine ⟨⟨phiMatrix x, W7b_GrandUnifiedTheories_phi_mem_specialUnitaryGroup x, rfl⟩, ?_⟩
    obtain ⟨a, g, h⟩ := x
    have hg := Matrix.mem_specialUnitaryGroup_iff.mp g.2
    have hh := Matrix.mem_specialUnitaryGroup_iff.mp h.2
    have e1 : ((a : ℂ) ^ 3) = ((a ^ 3 : Circle) : ℂ) := by simp
    have e2 : (((a⁻¹ : Circle) : ℂ) ^ 2) = ((a⁻¹ ^ 2 : Circle) : ℂ) := by simp
    refine ⟨W7b_GrandUnifiedTheories_rN (((a : ℂ) ^ 3) • (g : Matrix (Fin 2) (Fin 2) ℂ)),
      W7b_GrandUnifiedTheories_rN ((((a⁻¹ : Circle) : ℂ) ^ 2) • (h : Matrix (Fin 3) (Fin 3) ℂ)),
      ?_, ?_, ?_⟩
    · apply W7b_GrandUnifiedTheories_rN_mem
      rw [e1]; exact W7b_GrandUnifiedTheories_smul_mem _ hg.1
    · apply W7b_GrandUnifiedTheories_rN_mem
      rw [e2]; exact W7b_GrandUnifiedTheories_smul_mem _ hh.1
    · ext x y
      rcases x with ⟨i, s⟩ | ⟨i, s⟩ <;> rcases y with ⟨j, t⟩ | ⟨j, t⟩ <;>
        simp [realify, idx10ToC, phiMatrix, W7b_GrandUnifiedTheories_rN, realEntry]
