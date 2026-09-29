-- Prove2me | solution 1 for HighDimStat.MatrixRank.prop10_7_operator_norm_curvature_bound
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-29T08:07:25.511244+00:00
-- url     : https://prove2.me/submissions/358a288a-ba4d-4383-b9e3-a13e7a3648a8

import Mathlib
import Definitions.Def_HighDimStat_MatrixRank_Core

namespace HighDimStat.MatrixRank
open Matrix

theorem aux_p107_spec {d1 d2 : ℕ} (A : Matrix (Fin d1) (Fin d2) ℝ) :
    ∃ U : Matrix (Fin d2) (Fin d2) ℝ, ∃ μ : Fin d2 → ℝ,
      Uᵀ * U = 1 ∧ U * Uᵀ = 1 ∧ Aᵀ * A = U * diagonal μ * Uᵀ ∧ (∀ j, 0 ≤ μ j) ∧
      nuclearNorm A = ∑ j, Real.sqrt (μ j) ∧ A.rank = Fintype.card {j // μ j ≠ 0} := by
  set hP := Matrix.posSemidef_conjTranspose_mul_self A with hPdef
  set H := hP.1 with hH
  refine ⟨(H.eigenvectorUnitary : Matrix (Fin d2) (Fin d2) ℝ), H.eigenvalues, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have := Unitary.coe_star_mul_self H.eigenvectorUnitary
    rwa [Matrix.star_eq_conjTranspose, conjTranspose_eq_transpose_of_trivial (H.eigenvectorUnitary : Matrix (Fin d2) (Fin d2) ℝ)] at this
  · have := Unitary.coe_mul_star_self H.eigenvectorUnitary
    rwa [Unitary.coe_star, Matrix.star_eq_conjTranspose, conjTranspose_eq_transpose_of_trivial (H.eigenvectorUnitary : Matrix (Fin d2) (Fin d2) ℝ)] at this
  · have := H.spectral_theorem
    rw [Unitary.conjStarAlgAut_apply, Matrix.star_eq_conjTranspose] at this
    rw [show Aᵀ = Aᴴ from (conjTranspose_eq_transpose_of_trivial A).symm]
    refine this.trans ?_
    rw [conjTranspose_eq_transpose_of_trivial (H.eigenvectorUnitary : Matrix (Fin d2) (Fin d2) ℝ)]
    congr 2
  · intro j; exact hP.eigenvalues_nonneg j
  · unfold nuclearNorm singularValues
    simp only [Matrix.IsHermitian.eigenvalues]
    exact (Equiv.sum_comp ((finCongr (Fintype.card_fin d2)).symm) (fun k => Real.sqrt (H.eigenvalues₀ k))).trans
      (Equiv.sum_comp ((Fintype.equivOfCardEq (Fintype.card_fin _)).symm) (fun k => Real.sqrt (H.eigenvalues₀ k))).symm
  · rw [← H.rank_eq_card_non_zero_eigs, Matrix.rank_conjTranspose_mul_self]


noncomputable def aux_p107_nm {m : ℕ} (x : Fin m → ℝ) : ℝ := Real.sqrt (∑ i, x i ^ 2)

theorem aux_p107_nm_nonneg {m : ℕ} (x : Fin m → ℝ) : 0 ≤ aux_p107_nm x := Real.sqrt_nonneg _

theorem aux_p107_nm_sq {m : ℕ} (x : Fin m → ℝ) : aux_p107_nm x ^ 2 = x ⬝ᵥ x := by
  unfold aux_p107_nm
  rw [Real.sq_sqrt (Finset.sum_nonneg fun i _ => sq_nonneg _)]
  simp [dotProduct, sq]

theorem aux_p107_cs {m : ℕ} (x y : Fin m → ℝ) : x ⬝ᵥ y ≤ aux_p107_nm x * aux_p107_nm y :=
  Real.sum_mul_le_sqrt_mul_sqrt _ _ _

theorem aux_p107_nm_le_of_sq {m k : ℕ} (x : Fin m → ℝ) (y : Fin k → ℝ) (c : ℝ) (hc : 0 ≤ c)
    (h : x ⬝ᵥ x ≤ c ^ 2 * (y ⬝ᵥ y)) : aux_p107_nm x ≤ c * aux_p107_nm y := by
  have h1 := aux_p107_nm_nonneg x
  have h2 := mul_nonneg hc (aux_p107_nm_nonneg y)
  rw [← pow_le_pow_iff_left₀ h1 h2 two_ne_zero, mul_pow, aux_p107_nm_sq, aux_p107_nm_sq]
  exact h

theorem aux_p107_nm_add {m : ℕ} (x y : Fin m → ℝ) :
    aux_p107_nm (x + y) ≤ aux_p107_nm x + aux_p107_nm y := by
  have h1 := aux_p107_nm_nonneg (x + y)
  have h2 := add_nonneg (aux_p107_nm_nonneg x) (aux_p107_nm_nonneg y)
  rw [← pow_le_pow_iff_left₀ h1 h2 two_ne_zero, add_sq, aux_p107_nm_sq, aux_p107_nm_sq,
    aux_p107_nm_sq]
  have := aux_p107_cs x y
  have e : (x + y) ⬝ᵥ (x + y) = x ⬝ᵥ x + 2 * (x ⬝ᵥ y) + y ⬝ᵥ y := by
    rw [add_dotProduct, dotProduct_add, dotProduct_add, dotProduct_comm y x]; ring
  rw [e]; nlinarith

theorem aux_p107_nm_neg {m : ℕ} (x : Fin m → ℝ) : aux_p107_nm (-x) = aux_p107_nm x := by
  simp [aux_p107_nm]

theorem aux_p107_nm_smul {m : ℕ} (c : ℝ) (x : Fin m → ℝ) :
    aux_p107_nm (c • x) = |c| * aux_p107_nm x := by
  unfold aux_p107_nm
  rw [← Real.sqrt_sq_eq_abs, ← Real.sqrt_mul (sq_nonneg _)]
  congr 1
  simp [mul_pow, Finset.mul_sum]

theorem aux_p107_nm_eq_zero {m : ℕ} (x : Fin m → ℝ) (h : aux_p107_nm x = 0) : x = 0 := by
  have h2 : x ⬝ᵥ x = 0 := by rw [← aux_p107_nm_sq, h]; ring
  exact dotProduct_self_eq_zero.mp h2

/-! operator norm -/

theorem aux_p107_op_nonneg {d1 d2 : ℕ} (A : Matrix (Fin d1) (Fin d2) ℝ) : 0 ≤ opNorm A :=
  Real.iSup_nonneg fun _ => Real.sqrt_nonneg _

theorem aux_p107_op_bdd {d1 d2 : ℕ} (A : Matrix (Fin d1) (Fin d2) ℝ) :
    BddAbove (Set.range fun v : {v : Fin d2 → ℝ // ∑ j, (v j) ^ 2 = 1} =>
      Real.sqrt (∑ i, (A.mulVec v.1 i) ^ 2)) := by
  refine ⟨Real.sqrt (∑ i, ∑ j, A i j ^ 2), ?_⟩
  rintro _ ⟨v, rfl⟩
  apply Real.sqrt_le_sqrt
  apply Finset.sum_le_sum
  intro i _
  have := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun j => A i j) v.1
  rw [v.2, mul_one] at this
  simpa [mulVec, dotProduct] using this

theorem aux_p107_op_le {d1 d2 : ℕ} (A : Matrix (Fin d1) (Fin d2) ℝ) (v : Fin d2 → ℝ) :
    aux_p107_nm (A *ᵥ v) ≤ opNorm A * aux_p107_nm v := by
  by_cases hv : aux_p107_nm v = 0
  · rw [aux_p107_nm_eq_zero v hv, mulVec_zero]
    simp [aux_p107_nm]
  · have hpos : 0 < aux_p107_nm v := lt_of_le_of_ne (aux_p107_nm_nonneg v) (Ne.symm hv)
    set c := aux_p107_nm v with hc
    have hw : ∑ j, ((c⁻¹ • v) j) ^ 2 = 1 := by
      have h1 : aux_p107_nm (c⁻¹ • v) = 1 := by
        rw [aux_p107_nm_smul, abs_of_pos (inv_pos.mpr hpos), inv_mul_cancel₀ hv]
      have h2 := aux_p107_nm_sq (c⁻¹ • v)
      rw [h1] at h2
      simpa [dotProduct, sq] using h2.symm
    have hle : aux_p107_nm (A *ᵥ (c⁻¹ • v)) ≤ opNorm A :=
      le_ciSup (f := fun v : {v : Fin d2 → ℝ // ∑ j, (v j) ^ 2 = 1} =>
        Real.sqrt (∑ i, (A.mulVec v.1 i) ^ 2)) (aux_p107_op_bdd A) ⟨c⁻¹ • v, hw⟩
    rw [mulVec_smul, aux_p107_nm_smul, abs_of_pos (inv_pos.mpr hpos)] at hle
    rw [inv_mul_le_iff₀ hpos] at hle
    linarith [mul_comm c (opNorm A)]

theorem aux_p107_op_le_of {d1 d2 : ℕ} (A : Matrix (Fin d1) (Fin d2) ℝ) {c : ℝ} (hc : 0 ≤ c)
    (h : ∀ v, aux_p107_nm (A *ᵥ v) ≤ c * aux_p107_nm v) : opNorm A ≤ c := by
  refine Real.iSup_le (fun v => ?_) hc
  have := h v.1
  have h1 : aux_p107_nm v.1 = 1 := by simp [aux_p107_nm, v.2]
  rw [h1, mul_one] at this
  exact this

theorem aux_p107_op_sub {d1 d2 : ℕ} (A B : Matrix (Fin d1) (Fin d2) ℝ) :
    opNorm (A - B) ≤ opNorm A + opNorm B := by
  refine aux_p107_op_le_of _ (add_nonneg (aux_p107_op_nonneg A) (aux_p107_op_nonneg B)) ?_
  intro v
  rw [sub_mulVec, sub_eq_add_neg]
  refine (aux_p107_nm_add _ _).trans ?_
  rw [aux_p107_nm_neg, add_mul]
  exact add_le_add (aux_p107_op_le A v) (aux_p107_op_le B v)

/-! trace inner product -/

theorem aux_p107_ti_eq {d1 d2 : ℕ} (A B : Matrix (Fin d1) (Fin d2) ℝ) :
    traceInner A B = trace (Aᵀ * B) := by
  simp only [traceInner, trace, diag, mul_apply, transpose_apply]
  exact Finset.sum_comm

theorem aux_p107_ti_comm {d1 d2 : ℕ} (A B : Matrix (Fin d1) (Fin d2) ℝ) :
    traceInner A B = traceInner B A := by
  simp only [traceInner, mul_comm]

theorem aux_p107_ti_add_left {d1 d2 : ℕ} (A B C : Matrix (Fin d1) (Fin d2) ℝ) :
    traceInner (A + B) C = traceInner A C + traceInner B C := by
  simp only [traceInner, Matrix.add_apply, add_mul, Finset.sum_add_distrib]

theorem aux_p107_ti_add_right {d1 d2 : ℕ} (A B C : Matrix (Fin d1) (Fin d2) ℝ) :
    traceInner A (B + C) = traceInner A B + traceInner A C := by
  simp only [traceInner, Matrix.add_apply, mul_add, Finset.sum_add_distrib]

theorem aux_p107_ti_sub_right {d1 d2 : ℕ} (A B C : Matrix (Fin d1) (Fin d2) ℝ) :
    traceInner A (B - C) = traceInner A B - traceInner A C := by
  simp only [traceInner, Matrix.sub_apply, mul_sub, Finset.sum_sub_distrib]

theorem aux_p107_ti_smul_left {d1 d2 : ℕ} (c : ℝ) (A B : Matrix (Fin d1) (Fin d2) ℝ) :
    traceInner (c • A) B = c * traceInner A B := by
  simp only [traceInner, Matrix.smul_apply, smul_eq_mul, Finset.mul_sum, mul_assoc]

theorem aux_p107_ti_smul_right {d1 d2 : ℕ} (c : ℝ) (A B : Matrix (Fin d1) (Fin d2) ℝ) :
    traceInner A (c • B) = c * traceInner A B := by
  simp only [traceInner, Matrix.smul_apply, smul_eq_mul, Finset.mul_sum]
  congr 1; ext i; congr 1; ext j; ring

theorem aux_p107_ti_neg_left {d1 d2 : ℕ} (A B : Matrix (Fin d1) (Fin d2) ℝ) :
    traceInner (-A) B = - traceInner A B := by
  simp only [traceInner, Matrix.neg_apply, neg_mul, Finset.sum_neg_distrib]

theorem aux_p107_ti_zero_right {d1 d2 : ℕ} (A : Matrix (Fin d1) (Fin d2) ℝ) :
    traceInner A 0 = 0 := by
  simp [traceInner]

theorem aux_p107_ti_mul_left {d1 d2 : ℕ} (A B : Matrix (Fin d1) (Fin d2) ℝ)
    (P : Matrix (Fin d1) (Fin d1) ℝ) : traceInner A (P * B) = traceInner (Pᵀ * A) B := by
  rw [aux_p107_ti_eq, aux_p107_ti_eq, transpose_mul, transpose_transpose, Matrix.mul_assoc]

theorem aux_p107_ti_mul_right {d1 d2 : ℕ} (A B : Matrix (Fin d1) (Fin d2) ℝ)
    (Q : Matrix (Fin d2) (Fin d2) ℝ) : traceInner A (B * Q) = traceInner (A * Qᵀ) B := by
  rw [aux_p107_ti_eq, aux_p107_ti_eq, transpose_mul, transpose_transpose, ← Matrix.mul_assoc,
    trace_mul_comm, ← Matrix.mul_assoc]

theorem aux_p107_ti_vecMulVec {d1 d2 : ℕ} (G : Matrix (Fin d1) (Fin d2) ℝ) (u : Fin d1 → ℝ)
    (x : Fin d2 → ℝ) : traceInner G (vecMulVec u x) = u ⬝ᵥ (G *ᵥ x) := by
  simp only [traceInner, vecMulVec_apply, dotProduct, mulVec, Finset.mul_sum]
  congr 1; ext i; congr 1; ext j; ring


/-! projections -/

theorem aux_p107_quad {m k : ℕ} (A : Matrix (Fin m) (Fin k) ℝ) (x : Fin k → ℝ) :
    (A *ᵥ x) ⬝ᵥ (A *ᵥ x) = x ⬝ᵥ ((Aᵀ * A) *ᵥ x) := by
  rw [dotProduct_mulVec, ← mulVec_transpose, mulVec_mulVec, dotProduct_comm]

theorem aux_p107_proj {m : ℕ} (R : Matrix (Fin m) (Fin m) ℝ) (hs : Rᵀ = R) (hi : R * R = R)
    (x : Fin m → ℝ) : aux_p107_nm (R *ᵥ x) ≤ aux_p107_nm x := by
  have h1 : (R *ᵥ x) ⬝ᵥ (R *ᵥ x) = x ⬝ᵥ (R *ᵥ x) := by rw [aux_p107_quad, hs, hi]
  have h2 : 0 ≤ (x - R *ᵥ x) ⬝ᵥ (x - R *ᵥ x) := by rw [← aux_p107_nm_sq]; positivity
  rw [sub_dotProduct, dotProduct_sub, dotProduct_sub, dotProduct_comm (R *ᵥ x) x] at h2
  have h3 : (R *ᵥ x) ⬝ᵥ (R *ᵥ x) ≤ 1 ^ 2 * (x ⬝ᵥ x) := by rw [one_pow, one_mul]; linarith
  simpa using aux_p107_nm_le_of_sq _ _ 1 zero_le_one h3

theorem aux_p107_pi {m k : ℕ} (Z : Matrix (Fin m) (Fin k) ℝ) (hZ : Z * Zᵀ * Z = Z)
    (x : Fin k → ℝ) : aux_p107_nm (Z *ᵥ x) ≤ aux_p107_nm x := by
  have hs : (Zᵀ * Z)ᵀ = Zᵀ * Z := by rw [transpose_mul, transpose_transpose]
  have hi : Zᵀ * Z * (Zᵀ * Z) = Zᵀ * Z := by
    rw [show Zᵀ * Z * (Zᵀ * Z) = Zᵀ * (Z * Zᵀ * Z) by simp only [Matrix.mul_assoc], hZ]
  have h := aux_p107_proj _ hs hi x
  have e : aux_p107_nm (Z *ᵥ x) ^ 2 = aux_p107_nm ((Zᵀ * Z) *ᵥ x) ^ 2 := by
    rw [aux_p107_nm_sq, aux_p107_nm_sq, aux_p107_quad Z, aux_p107_quad (Zᵀ * Z), hs, hi]
  have e2 : aux_p107_nm (Z *ᵥ x) = aux_p107_nm ((Zᵀ * Z) *ᵥ x) := by
    rw [← Real.sqrt_sq (aux_p107_nm_nonneg (Z *ᵥ x)), e, Real.sqrt_sq (aux_p107_nm_nonneg _)]
  rw [e2]; exact h

theorem aux_p107_pi_op {d1 d2 : ℕ} (Z : Matrix (Fin d1) (Fin d2) ℝ) (hZ : Z * Zᵀ * Z = Z) :
    opNorm Z ≤ 1 :=
  aux_p107_op_le_of Z zero_le_one (fun v => by rw [one_mul]; exact aux_p107_pi Z hZ v)

/-! spectral columns and Hölder -/

theorem aux_p107_col {d1 d2 : ℕ} (A : Matrix (Fin d1) (Fin d2) ℝ) (U : Matrix (Fin d2) (Fin d2) ℝ)
    (μ : Fin d2 → ℝ) (hUU : Uᵀ * U = 1) (hspec : Aᵀ * A = U * diagonal μ * Uᵀ)
    (j : Fin d2) :
    aux_p107_nm (U *ᵥ Pi.single j 1) = 1 ∧
      aux_p107_nm (A *ᵥ (U *ᵥ Pi.single j 1)) = Real.sqrt (μ j) := by
  have hUe : Uᵀ *ᵥ (U *ᵥ Pi.single j 1) = Pi.single j 1 := by
    rw [mulVec_mulVec, hUU, one_mulVec]
  have hu : (U *ᵥ Pi.single j 1) ⬝ᵥ (U *ᵥ Pi.single j 1) = 1 := by
    rw [aux_p107_quad, hUU, one_mulVec, single_dotProduct, one_mul, Pi.single_eq_same]
  constructor
  · rw [← Real.sqrt_sq (aux_p107_nm_nonneg _), aux_p107_nm_sq, hu, Real.sqrt_one]
  · have h := aux_p107_quad A (U *ᵥ Pi.single j 1)
    rw [hspec, ← mulVec_mulVec, ← mulVec_mulVec, hUe, diagonal_mulVec_single, mul_one] at h
    have e : Pi.single j (μ j) = μ j • (Pi.single j (1:ℝ) : Fin d2 → ℝ) := by
      rw [← Pi.single_smul, smul_eq_mul, mul_one]
    rw [e, mulVec_smul, dotProduct_smul, hu, smul_eq_mul, mul_one] at h
    rw [← Real.sqrt_sq (aux_p107_nm_nonneg _), aux_p107_nm_sq, h]

theorem aux_p107_holder {d1 d2 : ℕ} (G A : Matrix (Fin d1) (Fin d2) ℝ) :
    traceInner G A ≤ opNorm G * nuclearNorm A := by
  obtain ⟨U, μ, hUU, hUU', hspec, hμ, hN, -⟩ := aux_p107_spec A
  have e1 : traceInner G A = ∑ j, (G *ᵥ (U *ᵥ Pi.single j 1)) ⬝ᵥ (A *ᵥ (U *ᵥ Pi.single j 1)) := by
    have : traceInner G A = trace ((G * U)ᵀ * (A * U)) := by
      rw [aux_p107_ti_eq, transpose_mul,
        show Uᵀ * Gᵀ * (A * U) = Uᵀ * (Gᵀ * A * U) by simp only [Matrix.mul_assoc],
        trace_mul_comm Uᵀ, Matrix.mul_assoc, hUU', Matrix.mul_one]
    rw [this, trace]
    congr 1; ext j
    rw [mulVec_mulVec, mulVec_mulVec, mulVec_single_one, mulVec_single_one]
    simp [diag, mul_apply, dotProduct, mul_comm]
  rw [e1, hN, Finset.mul_sum]
  refine Finset.sum_le_sum fun j _ => ?_
  obtain ⟨h1, h2⟩ := aux_p107_col A U μ hUU hspec j
  refine (aux_p107_cs _ _).trans ?_
  rw [h2]
  have := aux_p107_op_le G (U *ᵥ Pi.single j 1)
  rw [h1, mul_one] at this
  exact mul_le_mul_of_nonneg_right this (Real.sqrt_nonneg _)


/-! polar part -/

theorem aux_p107_diag_id (t : ℝ) :
    t⁻¹ * (t⁻¹ * t ^ 2 * t⁻¹) = t⁻¹ ∧ t⁻¹ * t⁻¹ * t⁻¹ * t ^ 2 = t⁻¹ ∧
      (1 - t⁻¹ * t ^ 2 * t⁻¹) * t ^ 2 = 0 ∧ t ^ 2 * t⁻¹ = t := by
  by_cases h : t = 0
  · simp [h]
  · refine ⟨?_, ?_, ?_, ?_⟩ <;> field_simp <;> ring

theorem aux_p107_polar {d1 d2 : ℕ} (A : Matrix (Fin d1) (Fin d2) ℝ) :
    ∃ Z : Matrix (Fin d1) (Fin d2) ℝ, traceInner A Z = nuclearNorm A ∧ Z * Zᵀ * Z = Z ∧
      (∃ X : Matrix (Fin d2) (Fin d2) ℝ, Z = A * X) ∧
      (∀ Y : Matrix (Fin d2) (Fin d2) ℝ, A * Y = 0 → Z * Y = 0) ∧ A * (Zᵀ * Z) = A := by
  obtain ⟨U, μ, hUU, hUU', hspec, hμ, hN, -⟩ := aux_p107_spec A
  set s : Fin d2 → ℝ := fun j => (Real.sqrt (μ j))⁻¹ with hs
  have hid : ∀ j, s j * (s j * μ j * s j) = s j ∧ s j * s j * s j * μ j = s j ∧
      (1 - s j * μ j * s j) * μ j = 0 ∧ μ j * s j = Real.sqrt (μ j) := fun j => by
    have := aux_p107_diag_id (Real.sqrt (μ j)); rwa [Real.sq_sqrt (hμ j)] at this
  have hL : ∀ {k : ℕ} (M : Matrix (Fin d2) (Fin k) ℝ), Uᵀ * (U * M) = M := fun M => by
    rw [← Matrix.mul_assoc, hUU, Matrix.one_mul]
  set X := U * diagonal s * Uᵀ with hX
  have hXt : Xᵀ = X := by simp [hX, transpose_mul, Matrix.mul_assoc]
  have hD : diagonal (fun j => s j * μ j * s j) = diagonal s * diagonal μ * diagonal s := by
    rw [diagonal_mul_diagonal, diagonal_mul_diagonal]
  have hZZ : (A * X)ᵀ * (A * X) = U * diagonal (fun j => s j * μ j * s j) * Uᵀ := by
    rw [transpose_mul, hXt, show X * Aᵀ * (A * X) = X * (Aᵀ * A) * X by
      simp only [Matrix.mul_assoc], hspec, hX, hD]
    simp only [Matrix.mul_assoc, hL]
  refine ⟨A * X, ?_, ?_, ⟨X, rfl⟩, ?_, ?_⟩
  · rw [aux_p107_ti_eq, ← Matrix.mul_assoc, hspec, hX, hN,
      show U * diagonal μ * Uᵀ * (U * diagonal s * Uᵀ) = U * (diagonal μ * diagonal s * Uᵀ) by
        simp only [Matrix.mul_assoc, hL],
      trace_mul_comm, Matrix.mul_assoc, hUU, Matrix.mul_one, diagonal_mul_diagonal,
      trace_diagonal]
    exact Finset.sum_congr rfl fun j _ => (hid j).2.2.2
  · have hDE : diagonal s * diagonal (fun j => s j * μ j * s j) = diagonal s := by
      rw [diagonal_mul_diagonal]; congr 1; funext j; exact (hid j).1
    rw [Matrix.mul_assoc (A * X), hZZ, hX]
    simp only [Matrix.mul_assoc, hL]
    rw [← Matrix.mul_assoc (diagonal s), hDE]
  · intro Y hY
    have h1 : diagonal μ * (Uᵀ * Y) = 0 := by
      have h0 : Aᵀ * A * Y = 0 := by rw [Matrix.mul_assoc, hY, Matrix.mul_zero]
      rw [hspec] at h0
      have h2 := congrArg (fun M => Uᵀ * M) h0
      simp only [Matrix.mul_assoc, hL, Matrix.mul_zero] at h2
      exact h2
    have hD3 : diagonal s = diagonal (fun j => s j * s j * s j) * diagonal μ := by
      rw [diagonal_mul_diagonal]; congr 1; funext j; exact (hid j).2.1.symm
    rw [hX]
    simp only [Matrix.mul_assoc]
    rw [hD3, Matrix.mul_assoc, h1]
    simp
  · rw [hZZ]
    have hE'D : diagonal (fun j => 1 - s j * μ j * s j) * diagonal μ = 0 := by
      rw [diagonal_mul_diagonal, ← diagonal_zero]; congr 1; funext j; exact (hid j).2.2.1
    have hV : (A * U * diagonal (fun j => 1 - s j * μ j * s j))ᵀ *
        (A * U * diagonal (fun j => 1 - s j * μ j * s j)) = 0 := by
      calc (A * U * diagonal (fun j => 1 - s j * μ j * s j))ᵀ *
            (A * U * diagonal (fun j => 1 - s j * μ j * s j))
          = diagonal (fun j => 1 - s j * μ j * s j) * (Uᵀ * ((Aᵀ * A) *
              (U * diagonal (fun j => 1 - s j * μ j * s j)))) := by
            rw [transpose_mul, transpose_mul, diagonal_transpose]; simp only [Matrix.mul_assoc]
        _ = diagonal (fun j => 1 - s j * μ j * s j) * diagonal μ *
              diagonal (fun j => 1 - s j * μ j * s j) := by
            rw [hspec]; simp only [Matrix.mul_assoc, hL]
        _ = 0 := by rw [hE'D, Matrix.zero_mul]
    have hV0 : A * U * diagonal (fun j => 1 - s j * μ j * s j) = 0 := by
      rw [← conjTranspose_eq_transpose_of_trivial] at hV
      exact conjTranspose_mul_self_eq_zero.mp hV
    have hEE : diagonal (fun j => s j * μ j * s j) + diagonal (fun j => 1 - s j * μ j * s j) =
        (1 : Matrix (Fin d2) (Fin d2) ℝ) := by
      rw [diagonal_add, ← diagonal_one]; congr 1; funext j; ring
    have h1 : A * (U * diagonal (fun j => s j * μ j * s j) * Uᵀ) +
        A * U * diagonal (fun j => 1 - s j * μ j * s j) * Uᵀ = A := by
      rw [show A * U * diagonal (fun j => 1 - s j * μ j * s j) * Uᵀ =
          A * (U * diagonal (fun j => 1 - s j * μ j * s j) * Uᵀ) by simp only [Matrix.mul_assoc],
        ← Matrix.mul_add, ← Matrix.add_mul, ← Matrix.mul_add, hEE, Matrix.mul_one, hUU',
        Matrix.mul_one]
    rw [hV0, Matrix.zero_mul, add_zero] at h1
    exact h1

/-! nuclear norm facts -/

theorem aux_p107_nuc_nonneg {d1 d2 : ℕ} (A : Matrix (Fin d1) (Fin d2) ℝ) : 0 ≤ nuclearNorm A :=
  Finset.sum_nonneg fun _ _ => Real.sqrt_nonneg _

theorem aux_p107_pi_ti {d1 d2 : ℕ} (Z A : Matrix (Fin d1) (Fin d2) ℝ) (hZ : Z * Zᵀ * Z = Z) :
    traceInner Z A ≤ nuclearNorm A := by
  have h1 := aux_p107_holder Z A
  have h2 := aux_p107_pi_op Z hZ
  have h3 := aux_p107_nuc_nonneg A
  nlinarith

theorem aux_p107_neg_pi {d1 d2 : ℕ} (Z : Matrix (Fin d1) (Fin d2) ℝ) (hZ : Z * Zᵀ * Z = Z) :
    (-Z) * (-Z)ᵀ * (-Z) = -Z := by
  simp [transpose_neg, hZ]

theorem aux_p107_nuc_add {d1 d2 : ℕ} (A B : Matrix (Fin d1) (Fin d2) ℝ) :
    nuclearNorm (A + B) ≤ nuclearNorm A + nuclearNorm B := by
  obtain ⟨Z, h1, h2, -⟩ := aux_p107_polar (A + B)
  rw [← h1, aux_p107_ti_add_left, aux_p107_ti_comm A, aux_p107_ti_comm B]
  exact add_le_add (aux_p107_pi_ti Z A h2) (aux_p107_pi_ti Z B h2)

theorem aux_p107_nuc_smul {d1 d2 : ℕ} (t : ℝ) (ht : 0 ≤ t) (A : Matrix (Fin d1) (Fin d2) ℝ) :
    nuclearNorm (t • A) ≤ t * nuclearNorm A := by
  obtain ⟨Z, h1, h2, -⟩ := aux_p107_polar (t • A)
  rw [← h1, aux_p107_ti_smul_left, aux_p107_ti_comm]
  exact mul_le_mul_of_nonneg_left (aux_p107_pi_ti Z A h2) ht

theorem aux_p107_nuc_rank1 {d1 d2 : ℕ} (u : Fin d1 → ℝ) (x : Fin d2 → ℝ) :
    nuclearNorm (vecMulVec u x) ≤ aux_p107_nm u * aux_p107_nm x := by
  obtain ⟨Z, h1, h2, -⟩ := aux_p107_polar (vecMulVec u x)
  rw [← h1, aux_p107_ti_comm, aux_p107_ti_vecMulVec]
  exact (aux_p107_cs _ _).trans
    (mul_le_mul_of_nonneg_left (aux_p107_pi Z h2 x) (aux_p107_nm_nonneg u))

theorem aux_p107_nuc_rank {d1 d2 : ℕ} (M : Matrix (Fin d1) (Fin d2) ℝ) :
    nuclearNorm M ≤ M.rank * opNorm M := by
  obtain ⟨U, μ, hUU, hUU', hspec, hμ, hN, hrk⟩ := aux_p107_spec M
  have hle : ∀ j, Real.sqrt (μ j) ≤ opNorm M := fun j => by
    obtain ⟨h1, h2⟩ := aux_p107_col M U μ hUU hspec j
    rw [← h2]
    have := aux_p107_op_le M (U *ᵥ Pi.single j 1)
    rwa [h1, mul_one] at this
  rw [hN, hrk, Fintype.card_subtype, ← Finset.sum_filter_of_ne (p := fun j => μ j ≠ 0)]
  · refine (Finset.sum_le_card_nsmul _ _ _ (fun j _ => hle j)).trans ?_
    rw [nsmul_eq_mul]
  · intro j _ h hμ0; apply h; rw [hμ0, Real.sqrt_zero]


theorem aux_p107_ti_zero_left {d1 d2 : ℕ} (A : Matrix (Fin d1) (Fin d2) ℝ) :
    traceInner 0 A = 0 := by
  simp [traceInner]

/-! decomposability / cone condition -/

theorem aux_p107_cone {d1 d2 : ℕ} (Θ Δ : Matrix (Fin d1) (Fin d2) ℝ)
    (h : nuclearNorm (Θ + Δ) ≤ nuclearNorm Θ + nuclearNorm Δ / 2) :
    nuclearNorm Δ ≤ 8 * (Θ.rank : ℝ) * opNorm Δ := by
  obtain ⟨Z1, h1N, h1pi, ⟨X1, hX1⟩, -, h1Q⟩ := aux_p107_polar Θ
  set P := Z1 * Z1ᵀ with hP
  set Q := Z1ᵀ * Z1 with hQ
  have hPt : Pᵀ = P := by rw [hP, transpose_mul, transpose_transpose]
  have hQt : Qᵀ = Q := by rw [hQ, transpose_mul, transpose_transpose]
  have hPZ : P * Z1 = Z1 := h1pi
  have hZQ : Z1 * Q = Z1 := by rw [hQ, ← Matrix.mul_assoc]; exact h1pi
  have hPP : P * P = P := by rw [hP, ← Matrix.mul_assoc, h1pi]
  have hQQ : Q * Q = Q := by
    rw [hQ, show Z1ᵀ * Z1 * (Z1ᵀ * Z1) = Z1ᵀ * (Z1 * Z1ᵀ * Z1) by simp only [Matrix.mul_assoc], h1pi]
  have hΘQ : Θ * Q = Θ := h1Q
  set Δ2 := (1 - P) * Δ * (1 - Q) with hΔ2
  have hP1P : P * (1 - P) = 0 := by rw [Matrix.mul_sub, Matrix.mul_one, hPP, sub_self]
  have h1QQ : (1 - Q) * Q = 0 := by rw [Matrix.sub_mul, Matrix.one_mul, hQQ, sub_self]
  have hPΔ2 : P * Δ2 = 0 := by
    rw [hΔ2, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hP1P, Matrix.zero_mul, Matrix.zero_mul]
  have hΔ2Q : Δ2 * Q = 0 := by
    rw [hΔ2, Matrix.mul_assoc, h1QQ, Matrix.mul_zero]
  obtain ⟨Z2, h2N, h2pi, ⟨X2, hX2⟩, h2Y, -⟩ := aux_p107_polar Δ2
  have hPZ2 : P * Z2 = 0 := by rw [hX2, ← Matrix.mul_assoc, hPΔ2, Matrix.zero_mul]
  have hZ2Q : Z2 * Q = 0 := h2Y Q hΔ2Q
  have hZ1tZ2 : Z1ᵀ * Z2 = 0 := by
    calc Z1ᵀ * Z2 = (P * Z1)ᵀ * Z2 := by rw [hPZ]
      _ = Z1ᵀ * (P * Z2) := by rw [transpose_mul, hPt, Matrix.mul_assoc]
      _ = 0 := by rw [hPZ2, Matrix.mul_zero]
  have hZ1Z2t : Z1 * Z2ᵀ = 0 := by
    calc Z1 * Z2ᵀ = Z1 * Q * Z2ᵀ := by rw [hZQ]
      _ = Z1 * (Z2 * Qᵀ)ᵀ := by rw [transpose_mul, transpose_transpose, Matrix.mul_assoc]
      _ = 0 := by rw [hQt, hZ2Q, transpose_zero, Matrix.mul_zero]
  have hZ2Z1t : Z2 * Z1ᵀ = 0 := by
    rw [← transpose_transpose (Z2 * Z1ᵀ), transpose_mul, transpose_transpose, hZ1Z2t,
      transpose_zero]
  have hZ2tZ1 : Z2ᵀ * Z1 = 0 := by
    rw [← transpose_transpose (Z2ᵀ * Z1), transpose_mul, transpose_transpose, hZ1tZ2,
      transpose_zero]
  have hZpi : (Z1 + Z2) * (Z1 + Z2)ᵀ * (Z1 + Z2) = Z1 + Z2 := by
    have e1 : (Z1 + Z2) * (Z1 + Z2)ᵀ = Z1 * Z1ᵀ + Z2 * Z2ᵀ := by
      rw [transpose_add, Matrix.add_mul, Matrix.mul_add, Matrix.mul_add, hZ1Z2t, hZ2Z1t, add_zero,
        zero_add]
    rw [e1, Matrix.add_mul, Matrix.mul_add, Matrix.mul_add, Matrix.mul_assoc Z1 Z1ᵀ Z2, hZ1tZ2,
      Matrix.mul_assoc Z2 Z2ᵀ Z1, hZ2tZ1, Matrix.mul_zero, Matrix.mul_zero, add_zero, zero_add,
      h1pi, h2pi]
  have hZ2' : Z2 = Z2 * (1 - Q) := by rw [Matrix.mul_sub, Matrix.mul_one, hZ2Q, sub_zero]
  have h1Qt : (1 - Q)ᵀ = 1 - Q := by rw [transpose_sub, transpose_one, hQt]
  have hΘ1Q : Θ * (1 - Q) = 0 := by rw [Matrix.mul_sub, Matrix.mul_one, hΘQ, sub_self]
  have hZ11Q : Z1 * (1 - Q) = 0 := by rw [Matrix.mul_sub, Matrix.mul_one, hZQ, sub_self]
  have hE : Δ - Δ2 = P * Δ + (1 - P) * Δ * Q := by
    rw [hΔ2]; simp only [Matrix.sub_mul, Matrix.mul_sub, Matrix.one_mul, Matrix.mul_one]; abel
  have hbound : nuclearNorm Θ + nuclearNorm Δ2 - nuclearNorm (Δ - Δ2) ≤ nuclearNorm (Θ + Δ) := by
    have hZ := aux_p107_pi_ti (Z1 + Z2) (Θ + Δ) hZpi
    have t1 : traceInner Z1 Θ = nuclearNorm Θ := by rw [aux_p107_ti_comm]; exact h1N
    have t2 : traceInner Z2 Θ = 0 := by
      rw [aux_p107_ti_comm, hZ2', aux_p107_ti_mul_right, h1Qt, hΘ1Q, aux_p107_ti_zero_left]
    have t3 : traceInner Z1 Δ2 = 0 := by
      rw [hΔ2, aux_p107_ti_mul_right, h1Qt, hZ11Q, aux_p107_ti_zero_left]
    have t4 : traceInner Z2 Δ2 = nuclearNorm Δ2 := by rw [aux_p107_ti_comm]; exact h2N
    have t5 : traceInner Z2 (Δ - Δ2) = 0 := by
      rw [hE, aux_p107_ti_add_right, aux_p107_ti_mul_left, hPt, hPZ2, aux_p107_ti_zero_left,
        aux_p107_ti_mul_right, hQt, hZ2Q, aux_p107_ti_zero_left, add_zero]
    have t6 : -nuclearNorm (Δ - Δ2) ≤ traceInner Z1 (Δ - Δ2) := by
      have := aux_p107_pi_ti (-Z1) (Δ - Δ2) (aux_p107_neg_pi Z1 h1pi)
      rw [aux_p107_ti_neg_left] at this; linarith
    have e : traceInner (Z1 + Z2) (Θ + Δ) = traceInner Z1 Θ + traceInner Z2 Θ +
        traceInner Z1 Δ2 + traceInner Z2 Δ2 + traceInner Z1 (Δ - Δ2) +
        traceInner Z2 (Δ - Δ2) := by
      have : Θ + Δ = Θ + Δ2 + (Δ - Δ2) := by abel
      rw [this]
      simp only [aux_p107_ti_add_left, aux_p107_ti_add_right]
      ring
    linarith
  have hsplit : nuclearNorm Δ ≤ nuclearNorm Δ2 + nuclearNorm (Δ - Δ2) := by
    have := aux_p107_nuc_add Δ2 (Δ - Δ2); rwa [add_sub_cancel] at this
  have hZ1r : Z1.rank ≤ Θ.rank := by rw [hX1]; exact rank_mul_le_left Θ X1
  have hr1 : ((P * Δ).rank : ℝ) ≤ Θ.rank := by
    exact_mod_cast ((rank_mul_le_left (Z1 * Z1ᵀ) Δ).trans (rank_mul_le_left Z1 Z1ᵀ)).trans hZ1r
  have hr2 : (((1 - P) * Δ * Q).rank : ℝ) ≤ Θ.rank := by
    have : (1 - P) * Δ * Q = ((1 - P) * Δ * Z1ᵀ) * Z1 := by rw [hQ, Matrix.mul_assoc _ Z1ᵀ Z1]
    rw [this]
    exact_mod_cast (rank_mul_le_right _ Z1).trans hZ1r
  have h1Pt : (1 - P)ᵀ = 1 - P := by rw [transpose_sub, transpose_one, hPt]
  have h1PP : (1 - P) * (1 - P) = 1 - P := by
    simp only [Matrix.sub_mul, Matrix.mul_sub, Matrix.one_mul, Matrix.mul_one, hPP]; abel
  have hop0 := aux_p107_op_nonneg Δ
  have ho1 : opNorm (P * Δ) ≤ opNorm Δ := by
    refine aux_p107_op_le_of _ hop0 (fun v => ?_)
    rw [← mulVec_mulVec]
    exact (aux_p107_proj P hPt hPP _).trans (aux_p107_op_le Δ v)
  have ho2 : opNorm ((1 - P) * Δ * Q) ≤ opNorm Δ := by
    refine aux_p107_op_le_of _ hop0 (fun v => ?_)
    rw [← mulVec_mulVec, ← mulVec_mulVec]
    refine (aux_p107_proj _ h1Pt h1PP _).trans ((aux_p107_op_le Δ _).trans ?_)
    exact mul_le_mul_of_nonneg_left (aux_p107_proj Q hQt hQQ v) hop0
  have hrk0 : (0 : ℝ) ≤ Θ.rank := Nat.cast_nonneg _
  have n1 := aux_p107_nuc_rank (P * Δ)
  have n2 := aux_p107_nuc_rank ((1 - P) * Δ * Q)
  have m1 : ((P * Δ).rank : ℝ) * opNorm (P * Δ) ≤ Θ.rank * opNorm Δ :=
    mul_le_mul hr1 ho1 (aux_p107_op_nonneg _) hrk0
  have m2 : (((1 - P) * Δ * Q).rank : ℝ) * opNorm ((1 - P) * Δ * Q) ≤ Θ.rank * opNorm Δ :=
    mul_le_mul hr2 ho2 (aux_p107_op_nonneg _) hrk0
  have hNE : nuclearNorm (Δ - Δ2) ≤ 2 * Θ.rank * opNorm Δ := by
    rw [hE]
    refine (aux_p107_nuc_add _ _).trans ?_
    linarith
  linarith


theorem aux_p107_ti_adj {d1 d2 n : ℕ} (Xs : Fin n → Matrix (Fin d1) (Fin d2) ℝ) (u : Fin n → ℝ)
    (a : ℝ) (D : Matrix (Fin d1) (Fin d2) ℝ) :
    traceInner (a • observationOpAdjoint Xs u) D = a * ∑ i, u i * observationOp Xs D i := by
  rw [aux_p107_ti_smul_left]
  congr 1
  unfold observationOpAdjoint observationOp
  calc traceInner (∑ i, u i • Xs i) D
      = ∑ a, ∑ b, ∑ i, u i * (Xs i a b * D a b) := by
        simp only [traceInner, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul, Finset.sum_mul,
          mul_assoc]
    _ = ∑ a, ∑ i, ∑ b, u i * (Xs i a b * D a b) := Finset.sum_congr rfl fun a _ => Finset.sum_comm
    _ = ∑ i, ∑ a, ∑ b, u i * (Xs i a b * D a b) := Finset.sum_comm
    _ = ∑ i, u i * traceInner (Xs i) D := by
        simp only [traceInner, Finset.mul_sum]

end HighDimStat.MatrixRank

open HighDimStat.MatrixRank

theorem solution {d1 d2 n : ℕ}
    (Xs : Fin n → Matrix (Fin d1) (Fin d2) ℝ) (w : Fin n → ℝ)
    (Θstar Θhat : Matrix (Fin d1) (Fin d2) ℝ) (κ τn lamN : ℝ)
    (hκ : 0 < κ) (hτn : 0 ≤ τn) (hlam : 0 < lamN)
    (hcurv : DualCurvatureNuclear Xs κ τn)
    (hrank : (Θstar.rank : ℝ) < κ / (64 * τn))
    (hsol : IsNuclearNormLSSolution Xs (fun i => traceInner (Xs i) Θstar + w i) lamN Θhat)
    (hG : opNorm ((1 / (n : ℝ)) • observationOpAdjoint Xs w) ≤ lamN / 2) :
    opNorm (Θhat - Θstar) ≤ 3 * Real.sqrt 2 * lamN / κ := by
  obtain ⟨Δ, hΔ⟩ : ∃ Δ, Δ = Θhat - Θstar := ⟨_, rfl⟩
  rw [← hΔ]
  have hΘhat : Θhat = Θstar + Δ := by rw [hΔ]; abel
  have hτpos : 0 < τn := by
    rcases hτn.lt_or_eq with h | h
    · exact h
    · exfalso
      rw [← h, mul_zero, div_zero] at hrank
      exact absurd hrank (not_lt.mpr (Nat.cast_nonneg _))
  obtain ⟨c, hc⟩ : ∃ c : ℝ, c = 1 / (2 * (n : ℝ)) := ⟨_, rfl⟩
  have hc0 : 0 ≤ c := by rw [hc]; positivity
  have h2c : 2 * c = 1 / (n : ℝ) := by
    rw [hc]
    rcases eq_or_ne (n : ℝ) 0 with h | h
    · simp [h]
    · field_simp
  obtain ⟨r, hr⟩ : ∃ r : Fin n → ℝ,
      r = fun i => (traceInner (Xs i) Θstar + w i) - observationOp Xs Θhat i := ⟨_, rfl⟩
  have hsol' : ∀ Θ : Matrix (Fin d1) (Fin d2) ℝ,
      c * (∑ i, (r i) ^ 2) + lamN * nuclearNorm Θhat ≤
      c * (∑ i, ((traceInner (Xs i) Θstar + w i) - observationOp Xs Θ i) ^ 2) +
        lamN * nuclearNorm Θ := by
    intro Θ; have := hsol Θ; rw [hr, hc]; exact this
  obtain ⟨G, hGdef⟩ : ∃ G, G = (1 / (n : ℝ)) • observationOpAdjoint Xs r := ⟨_, rfl⟩
  -- first-order optimality
  have hG1 : ∀ D, traceInner G D ≤ lamN * nuclearNorm D := by
    intro D
    rw [hGdef, aux_p107_ti_adj]
    have hT0 : 0 ≤ ∑ i, (observationOp Xs D i) ^ 2 := Finset.sum_nonneg fun i _ => sq_nonneg _
    have key : ∀ t : ℝ, 0 < t → 1 / (n : ℝ) * ∑ i, r i * observationOp Xs D i ≤
        lamN * nuclearNorm D + t * (c * ∑ i, (observationOp Xs D i) ^ 2) := by
      intro t ht
      have h1 := hsol' (Θhat + t • D)
      have e : ∀ i, (traceInner (Xs i) Θstar + w i) - observationOp Xs (Θhat + t • D) i =
          r i - t * observationOp Xs D i := by
        intro i
        simp only [hr, observationOp, aux_p107_ti_add_right, aux_p107_ti_smul_right]; ring
      simp only [e] at h1
      have hexp : ∑ i, (r i - t * observationOp Xs D i) ^ 2 = ∑ i, (r i) ^ 2 -
          2 * t * ∑ i, r i * observationOp Xs D i + t ^ 2 * ∑ i, (observationOp Xs D i) ^ 2 := by
        have : ∀ i, (r i - t * observationOp Xs D i) ^ 2 = (r i) ^ 2 -
            2 * t * (r i * observationOp Xs D i) + t ^ 2 * (observationOp Xs D i) ^ 2 :=
          fun i => by ring
        simp only [this, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum]
      rw [hexp] at h1
      have hN1 := aux_p107_nuc_add Θhat (t • D)
      have hN2 := aux_p107_nuc_smul t ht.le D
      have h3 : t * (2 * c * ∑ i, r i * observationOp Xs D i) ≤
          t * (lamN * nuclearNorm D + t * (c * ∑ i, (observationOp Xs D i) ^ 2)) := by
        nlinarith
      rw [← h2c]
      exact le_of_mul_le_mul_left h3 ht
    apply le_of_forall_pos_le_add
    intro ε hε
    set T := c * ∑ i, (observationOp Xs D i) ^ 2 with hT
    have hT0' : 0 ≤ T := mul_nonneg hc0 hT0
    have h1 := key (ε / (T + 1)) (by positivity)
    have h2 : ε / (T + 1) * T ≤ ε := by
      rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]; nlinarith
    linarith
  have hG2 : opNorm G ≤ lamN := by
    apply aux_p107_op_le_of G hlam.le
    intro x
    have h1 : aux_p107_nm (Matrix.mulVec G x) ^ 2 ≤ lamN * (aux_p107_nm (Matrix.mulVec G x) * aux_p107_nm x) := by
      rw [aux_p107_nm_sq]
      have := hG1 (Matrix.vecMulVec (Matrix.mulVec G x) x)
      rw [aux_p107_ti_vecMulVec] at this
      exact this.trans (mul_le_mul_of_nonneg_left (aux_p107_nuc_rank1 _ x) hlam.le)
    by_cases hu : aux_p107_nm (Matrix.mulVec G x) = 0
    · rw [hu]; exact mul_nonneg hlam.le (aux_p107_nm_nonneg x)
    · have hpos : 0 < aux_p107_nm (Matrix.mulVec G x) := lt_of_le_of_ne (aux_p107_nm_nonneg _) (Ne.symm hu)
      have h2 : aux_p107_nm (Matrix.mulVec G x) * aux_p107_nm (Matrix.mulVec G x) ≤
          aux_p107_nm (Matrix.mulVec G x) * (lamN * aux_p107_nm x) := by nlinarith
      exact le_of_mul_le_mul_left h2 hpos
  have hXX : (1 / (n : ℝ)) • observationOpAdjoint Xs (observationOp Xs Δ) =
      (1 / (n : ℝ)) • observationOpAdjoint Xs w - G := by
    rw [hGdef, ← smul_sub]
    congr 1
    unfold observationOpAdjoint
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← sub_smul]
    congr 1
    simp only [hr, observationOp, hΔ, aux_p107_ti_sub_right]; ring
  have hop : opNorm ((1 / (n : ℝ)) • observationOpAdjoint Xs (observationOp Xs Δ)) ≤
      3 / 2 * lamN := by
    rw [hXX]; refine (aux_p107_op_sub _ _).trans ?_; linarith
  -- basic inequality
  have hbasic : nuclearNorm (Θstar + Δ) ≤ nuclearNorm Θstar + nuclearNorm Δ / 2 := by
    have h1 := hsol' Θstar
    have e1 : ∀ i, r i = w i - observationOp Xs Δ i := by
      intro i; simp only [hr, observationOp, hΔ, aux_p107_ti_sub_right]; ring
    have e2 : ∀ i, (traceInner (Xs i) Θstar + w i) - observationOp Xs Θstar i = w i := by
      intro i; simp only [observationOp]; ring
    simp only [e1, e2] at h1
    have hexp : ∑ i, (w i - observationOp Xs Δ i) ^ 2 = ∑ i, (w i) ^ 2 -
        2 * ∑ i, w i * observationOp Xs Δ i + ∑ i, (observationOp Xs Δ i) ^ 2 := by
      have : ∀ i, (w i - observationOp Xs Δ i) ^ 2 = (w i) ^ 2 -
          2 * (w i * observationOp Xs Δ i) + (observationOp Xs Δ i) ^ 2 := fun i => by ring
      simp only [this, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum]
    rw [hexp] at h1
    have hT0 : 0 ≤ ∑ i, (observationOp Xs Δ i) ^ 2 := Finset.sum_nonneg fun i _ => sq_nonneg _
    have hti := aux_p107_holder ((1 / (n : ℝ)) • observationOpAdjoint Xs w) Δ
    rw [aux_p107_ti_adj] at hti
    have hNΔ := aux_p107_nuc_nonneg Δ
    have h3 : opNorm ((1 / (n : ℝ)) • observationOpAdjoint Xs w) * nuclearNorm Δ ≤
        lamN / 2 * nuclearNorm Δ := mul_le_mul_of_nonneg_right hG hNΔ
    have hS : 2 * c * ∑ i, w i * observationOp Xs Δ i =
        1 / (n : ℝ) * ∑ i, w i * observationOp Xs Δ i := by rw [h2c]
    have h4 : lamN * nuclearNorm Θhat ≤ lamN * (nuclearNorm Θstar + nuclearNorm Δ / 2) := by
      nlinarith
    rw [← hΘhat]
    exact le_of_mul_le_mul_left h4 hlam
  have hcone := aux_p107_cone Θstar Δ hbasic
  have hc' := hcurv Δ
  have hr64 : 64 * τn * (Θstar.rank : ℝ) < κ := by
    rw [lt_div_iff₀ (by positivity)] at hrank; linarith
  have hop0 := aux_p107_op_nonneg Δ
  have h8 : τn * nuclearNorm Δ ≤ κ / 8 * opNorm Δ := by
    calc τn * nuclearNorm Δ ≤ τn * (8 * (Θstar.rank : ℝ) * opNorm Δ) :=
          mul_le_mul_of_nonneg_left hcone hτn
      _ = (8 * τn * (Θstar.rank : ℝ)) * opNorm Δ := by ring
      _ ≤ κ / 8 * opNorm Δ := mul_le_mul_of_nonneg_right (by linarith) hop0
  have hmain : 7 / 8 * κ * opNorm Δ ≤ 3 / 2 * lamN := by linarith
  have hsqrt : 1 ≤ Real.sqrt 2 := by
    rw [show (1 : ℝ) = Real.sqrt 1 from Real.sqrt_one.symm]
    exact Real.sqrt_le_sqrt (by norm_num)
  have h3 : 3 * lamN ≤ 3 * Real.sqrt 2 * lamN := by nlinarith
  rw [le_div_iff₀ hκ]
  nlinarith
