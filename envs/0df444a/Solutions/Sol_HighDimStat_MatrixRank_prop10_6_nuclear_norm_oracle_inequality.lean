-- Prove2me | solution 1 for HighDimStat.MatrixRank.prop10_6_nuclear_norm_oracle_inequality
-- status  : ACCEPTED   (disprove)
-- author  : @raresbuhai
-- created : 2026-10-03T06:19:38.547987+00:00
-- url     : https://prove2.me/submissions/cdb73707-62c0-4dfd-a9cf-701f48678b4b

import Mathlib
import Definitions.Def_HighDimStat_MatrixRank_Core


-- Source module: NuclearExistingGeometry
-- Matrix geometry adapted from mrfancypants, Prove2Me accepted submission
-- 358a288a-ba4d-4383-b9e3-a13e7a3648a8; the complete helper proofs are retained.

namespace HighDimStat.MatrixRank
open Matrix

theorem nuclearBase_spec {d1 d2 : ℕ} (A : Matrix (Fin d1) (Fin d2) ℝ) :
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


noncomputable def nuclearBase_nm {m : ℕ} (x : Fin m → ℝ) : ℝ := Real.sqrt (∑ i, x i ^ 2)

theorem nuclearBase_nm_nonneg {m : ℕ} (x : Fin m → ℝ) : 0 ≤ nuclearBase_nm x := Real.sqrt_nonneg _

theorem nuclearBase_nm_sq {m : ℕ} (x : Fin m → ℝ) : nuclearBase_nm x ^ 2 = x ⬝ᵥ x := by
  unfold nuclearBase_nm
  rw [Real.sq_sqrt (Finset.sum_nonneg fun i _ => sq_nonneg _)]
  simp [dotProduct, sq]

theorem nuclearBase_cs {m : ℕ} (x y : Fin m → ℝ) : x ⬝ᵥ y ≤ nuclearBase_nm x * nuclearBase_nm y :=
  Real.sum_mul_le_sqrt_mul_sqrt _ _ _

theorem nuclearBase_nm_le_of_sq {m k : ℕ} (x : Fin m → ℝ) (y : Fin k → ℝ) (c : ℝ) (hc : 0 ≤ c)
    (h : x ⬝ᵥ x ≤ c ^ 2 * (y ⬝ᵥ y)) : nuclearBase_nm x ≤ c * nuclearBase_nm y := by
  have h1 := nuclearBase_nm_nonneg x
  have h2 := mul_nonneg hc (nuclearBase_nm_nonneg y)
  rw [← pow_le_pow_iff_left₀ h1 h2 two_ne_zero, mul_pow, nuclearBase_nm_sq, nuclearBase_nm_sq]
  exact h

theorem nuclearBase_nm_add {m : ℕ} (x y : Fin m → ℝ) :
    nuclearBase_nm (x + y) ≤ nuclearBase_nm x + nuclearBase_nm y := by
  have h1 := nuclearBase_nm_nonneg (x + y)
  have h2 := add_nonneg (nuclearBase_nm_nonneg x) (nuclearBase_nm_nonneg y)
  rw [← pow_le_pow_iff_left₀ h1 h2 two_ne_zero, add_sq, nuclearBase_nm_sq, nuclearBase_nm_sq,
    nuclearBase_nm_sq]
  have := nuclearBase_cs x y
  have e : (x + y) ⬝ᵥ (x + y) = x ⬝ᵥ x + 2 * (x ⬝ᵥ y) + y ⬝ᵥ y := by
    rw [add_dotProduct, dotProduct_add, dotProduct_add, dotProduct_comm y x]; ring
  rw [e]; nlinarith

theorem nuclearBase_nm_neg {m : ℕ} (x : Fin m → ℝ) : nuclearBase_nm (-x) = nuclearBase_nm x := by
  simp [nuclearBase_nm]

theorem nuclearBase_nm_smul {m : ℕ} (c : ℝ) (x : Fin m → ℝ) :
    nuclearBase_nm (c • x) = |c| * nuclearBase_nm x := by
  unfold nuclearBase_nm
  rw [← Real.sqrt_sq_eq_abs, ← Real.sqrt_mul (sq_nonneg _)]
  congr 1
  simp [mul_pow, Finset.mul_sum]

theorem nuclearBase_nm_eq_zero {m : ℕ} (x : Fin m → ℝ) (h : nuclearBase_nm x = 0) : x = 0 := by
  have h2 : x ⬝ᵥ x = 0 := by rw [← nuclearBase_nm_sq, h]; ring
  exact dotProduct_self_eq_zero.mp h2

/-! operator norm -/

theorem nuclearBase_op_nonneg {d1 d2 : ℕ} (A : Matrix (Fin d1) (Fin d2) ℝ) : 0 ≤ opNorm A :=
  Real.iSup_nonneg fun _ => Real.sqrt_nonneg _

theorem nuclearBase_op_bdd {d1 d2 : ℕ} (A : Matrix (Fin d1) (Fin d2) ℝ) :
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

theorem nuclearBase_op_le {d1 d2 : ℕ} (A : Matrix (Fin d1) (Fin d2) ℝ) (v : Fin d2 → ℝ) :
    nuclearBase_nm (A *ᵥ v) ≤ opNorm A * nuclearBase_nm v := by
  by_cases hv : nuclearBase_nm v = 0
  · rw [nuclearBase_nm_eq_zero v hv, mulVec_zero]
    simp [nuclearBase_nm]
  · have hpos : 0 < nuclearBase_nm v := lt_of_le_of_ne (nuclearBase_nm_nonneg v) (Ne.symm hv)
    set c := nuclearBase_nm v with hc
    have hw : ∑ j, ((c⁻¹ • v) j) ^ 2 = 1 := by
      have h1 : nuclearBase_nm (c⁻¹ • v) = 1 := by
        rw [nuclearBase_nm_smul, abs_of_pos (inv_pos.mpr hpos), inv_mul_cancel₀ hv]
      have h2 := nuclearBase_nm_sq (c⁻¹ • v)
      rw [h1] at h2
      simpa [dotProduct, sq] using h2.symm
    have hle : nuclearBase_nm (A *ᵥ (c⁻¹ • v)) ≤ opNorm A :=
      le_ciSup (f := fun v : {v : Fin d2 → ℝ // ∑ j, (v j) ^ 2 = 1} =>
        Real.sqrt (∑ i, (A.mulVec v.1 i) ^ 2)) (nuclearBase_op_bdd A) ⟨c⁻¹ • v, hw⟩
    rw [mulVec_smul, nuclearBase_nm_smul, abs_of_pos (inv_pos.mpr hpos)] at hle
    rw [inv_mul_le_iff₀ hpos] at hle
    linarith [mul_comm c (opNorm A)]

theorem nuclearBase_op_le_of {d1 d2 : ℕ} (A : Matrix (Fin d1) (Fin d2) ℝ) {c : ℝ} (hc : 0 ≤ c)
    (h : ∀ v, nuclearBase_nm (A *ᵥ v) ≤ c * nuclearBase_nm v) : opNorm A ≤ c := by
  refine Real.iSup_le (fun v => ?_) hc
  have := h v.1
  have h1 : nuclearBase_nm v.1 = 1 := by simp [nuclearBase_nm, v.2]
  rw [h1, mul_one] at this
  exact this

theorem nuclearBase_op_sub {d1 d2 : ℕ} (A B : Matrix (Fin d1) (Fin d2) ℝ) :
    opNorm (A - B) ≤ opNorm A + opNorm B := by
  refine nuclearBase_op_le_of _ (add_nonneg (nuclearBase_op_nonneg A) (nuclearBase_op_nonneg B)) ?_
  intro v
  rw [sub_mulVec, sub_eq_add_neg]
  refine (nuclearBase_nm_add _ _).trans ?_
  rw [nuclearBase_nm_neg, add_mul]
  exact add_le_add (nuclearBase_op_le A v) (nuclearBase_op_le B v)

/-! trace inner product -/

theorem nuclearBase_ti_eq {d1 d2 : ℕ} (A B : Matrix (Fin d1) (Fin d2) ℝ) :
    traceInner A B = trace (Aᵀ * B) := by
  simp only [traceInner, trace, diag, mul_apply, transpose_apply]
  exact Finset.sum_comm

theorem nuclearBase_ti_comm {d1 d2 : ℕ} (A B : Matrix (Fin d1) (Fin d2) ℝ) :
    traceInner A B = traceInner B A := by
  simp only [traceInner, mul_comm]

theorem nuclearBase_ti_add_left {d1 d2 : ℕ} (A B C : Matrix (Fin d1) (Fin d2) ℝ) :
    traceInner (A + B) C = traceInner A C + traceInner B C := by
  simp only [traceInner, Matrix.add_apply, add_mul, Finset.sum_add_distrib]

theorem nuclearBase_ti_add_right {d1 d2 : ℕ} (A B C : Matrix (Fin d1) (Fin d2) ℝ) :
    traceInner A (B + C) = traceInner A B + traceInner A C := by
  simp only [traceInner, Matrix.add_apply, mul_add, Finset.sum_add_distrib]

theorem nuclearBase_ti_sub_right {d1 d2 : ℕ} (A B C : Matrix (Fin d1) (Fin d2) ℝ) :
    traceInner A (B - C) = traceInner A B - traceInner A C := by
  simp only [traceInner, Matrix.sub_apply, mul_sub, Finset.sum_sub_distrib]

theorem nuclearBase_ti_smul_left {d1 d2 : ℕ} (c : ℝ) (A B : Matrix (Fin d1) (Fin d2) ℝ) :
    traceInner (c • A) B = c * traceInner A B := by
  simp only [traceInner, Matrix.smul_apply, smul_eq_mul, Finset.mul_sum, mul_assoc]

theorem nuclearBase_ti_smul_right {d1 d2 : ℕ} (c : ℝ) (A B : Matrix (Fin d1) (Fin d2) ℝ) :
    traceInner A (c • B) = c * traceInner A B := by
  simp only [traceInner, Matrix.smul_apply, smul_eq_mul, Finset.mul_sum]
  congr 1; ext i; congr 1; ext j; ring

theorem nuclearBase_ti_neg_left {d1 d2 : ℕ} (A B : Matrix (Fin d1) (Fin d2) ℝ) :
    traceInner (-A) B = - traceInner A B := by
  simp only [traceInner, Matrix.neg_apply, neg_mul, Finset.sum_neg_distrib]

theorem nuclearBase_ti_zero_right {d1 d2 : ℕ} (A : Matrix (Fin d1) (Fin d2) ℝ) :
    traceInner A 0 = 0 := by
  simp [traceInner]

theorem nuclearBase_ti_mul_left {d1 d2 : ℕ} (A B : Matrix (Fin d1) (Fin d2) ℝ)
    (P : Matrix (Fin d1) (Fin d1) ℝ) : traceInner A (P * B) = traceInner (Pᵀ * A) B := by
  rw [nuclearBase_ti_eq, nuclearBase_ti_eq, transpose_mul, transpose_transpose, Matrix.mul_assoc]

theorem nuclearBase_ti_mul_right {d1 d2 : ℕ} (A B : Matrix (Fin d1) (Fin d2) ℝ)
    (Q : Matrix (Fin d2) (Fin d2) ℝ) : traceInner A (B * Q) = traceInner (A * Qᵀ) B := by
  rw [nuclearBase_ti_eq, nuclearBase_ti_eq, transpose_mul, transpose_transpose, ← Matrix.mul_assoc,
    trace_mul_comm, ← Matrix.mul_assoc]

theorem nuclearBase_ti_vecMulVec {d1 d2 : ℕ} (G : Matrix (Fin d1) (Fin d2) ℝ) (u : Fin d1 → ℝ)
    (x : Fin d2 → ℝ) : traceInner G (vecMulVec u x) = u ⬝ᵥ (G *ᵥ x) := by
  simp only [traceInner, vecMulVec_apply, dotProduct, mulVec, Finset.mul_sum]
  congr 1; ext i; congr 1; ext j; ring


/-! projections -/

theorem nuclearBase_quad {m k : ℕ} (A : Matrix (Fin m) (Fin k) ℝ) (x : Fin k → ℝ) :
    (A *ᵥ x) ⬝ᵥ (A *ᵥ x) = x ⬝ᵥ ((Aᵀ * A) *ᵥ x) := by
  rw [dotProduct_mulVec, ← mulVec_transpose, mulVec_mulVec, dotProduct_comm]

theorem nuclearBase_proj {m : ℕ} (R : Matrix (Fin m) (Fin m) ℝ) (hs : Rᵀ = R) (hi : R * R = R)
    (x : Fin m → ℝ) : nuclearBase_nm (R *ᵥ x) ≤ nuclearBase_nm x := by
  have h1 : (R *ᵥ x) ⬝ᵥ (R *ᵥ x) = x ⬝ᵥ (R *ᵥ x) := by rw [nuclearBase_quad, hs, hi]
  have h2 : 0 ≤ (x - R *ᵥ x) ⬝ᵥ (x - R *ᵥ x) := by rw [← nuclearBase_nm_sq]; positivity
  rw [sub_dotProduct, dotProduct_sub, dotProduct_sub, dotProduct_comm (R *ᵥ x) x] at h2
  have h3 : (R *ᵥ x) ⬝ᵥ (R *ᵥ x) ≤ 1 ^ 2 * (x ⬝ᵥ x) := by rw [one_pow, one_mul]; linarith
  simpa using nuclearBase_nm_le_of_sq _ _ 1 zero_le_one h3

theorem nuclearBase_pi {m k : ℕ} (Z : Matrix (Fin m) (Fin k) ℝ) (hZ : Z * Zᵀ * Z = Z)
    (x : Fin k → ℝ) : nuclearBase_nm (Z *ᵥ x) ≤ nuclearBase_nm x := by
  have hs : (Zᵀ * Z)ᵀ = Zᵀ * Z := by rw [transpose_mul, transpose_transpose]
  have hi : Zᵀ * Z * (Zᵀ * Z) = Zᵀ * Z := by
    rw [show Zᵀ * Z * (Zᵀ * Z) = Zᵀ * (Z * Zᵀ * Z) by simp only [Matrix.mul_assoc], hZ]
  have h := nuclearBase_proj _ hs hi x
  have e : nuclearBase_nm (Z *ᵥ x) ^ 2 = nuclearBase_nm ((Zᵀ * Z) *ᵥ x) ^ 2 := by
    rw [nuclearBase_nm_sq, nuclearBase_nm_sq, nuclearBase_quad Z, nuclearBase_quad (Zᵀ * Z), hs, hi]
  have e2 : nuclearBase_nm (Z *ᵥ x) = nuclearBase_nm ((Zᵀ * Z) *ᵥ x) := by
    rw [← Real.sqrt_sq (nuclearBase_nm_nonneg (Z *ᵥ x)), e, Real.sqrt_sq (nuclearBase_nm_nonneg _)]
  rw [e2]; exact h

theorem nuclearBase_pi_op {d1 d2 : ℕ} (Z : Matrix (Fin d1) (Fin d2) ℝ) (hZ : Z * Zᵀ * Z = Z) :
    opNorm Z ≤ 1 :=
  nuclearBase_op_le_of Z zero_le_one (fun v => by rw [one_mul]; exact nuclearBase_pi Z hZ v)

/-! spectral columns and Hölder -/

theorem nuclearBase_col {d1 d2 : ℕ} (A : Matrix (Fin d1) (Fin d2) ℝ) (U : Matrix (Fin d2) (Fin d2) ℝ)
    (μ : Fin d2 → ℝ) (hUU : Uᵀ * U = 1) (hspec : Aᵀ * A = U * diagonal μ * Uᵀ)
    (j : Fin d2) :
    nuclearBase_nm (U *ᵥ Pi.single j 1) = 1 ∧
      nuclearBase_nm (A *ᵥ (U *ᵥ Pi.single j 1)) = Real.sqrt (μ j) := by
  have hUe : Uᵀ *ᵥ (U *ᵥ Pi.single j 1) = Pi.single j 1 := by
    rw [mulVec_mulVec, hUU, one_mulVec]
  have hu : (U *ᵥ Pi.single j 1) ⬝ᵥ (U *ᵥ Pi.single j 1) = 1 := by
    rw [nuclearBase_quad, hUU, one_mulVec, single_dotProduct, one_mul, Pi.single_eq_same]
  constructor
  · rw [← Real.sqrt_sq (nuclearBase_nm_nonneg _), nuclearBase_nm_sq, hu, Real.sqrt_one]
  · have h := nuclearBase_quad A (U *ᵥ Pi.single j 1)
    rw [hspec, ← mulVec_mulVec, ← mulVec_mulVec, hUe, diagonal_mulVec_single, mul_one] at h
    have e : Pi.single j (μ j) = μ j • (Pi.single j (1:ℝ) : Fin d2 → ℝ) := by
      rw [← Pi.single_smul, smul_eq_mul, mul_one]
    rw [e, mulVec_smul, dotProduct_smul, hu, smul_eq_mul, mul_one] at h
    rw [← Real.sqrt_sq (nuclearBase_nm_nonneg _), nuclearBase_nm_sq, h]

theorem nuclearBase_holder {d1 d2 : ℕ} (G A : Matrix (Fin d1) (Fin d2) ℝ) :
    traceInner G A ≤ opNorm G * nuclearNorm A := by
  obtain ⟨U, μ, hUU, hUU', hspec, hμ, hN, -⟩ := nuclearBase_spec A
  have e1 : traceInner G A = ∑ j, (G *ᵥ (U *ᵥ Pi.single j 1)) ⬝ᵥ (A *ᵥ (U *ᵥ Pi.single j 1)) := by
    have : traceInner G A = trace ((G * U)ᵀ * (A * U)) := by
      rw [nuclearBase_ti_eq, transpose_mul,
        show Uᵀ * Gᵀ * (A * U) = Uᵀ * (Gᵀ * A * U) by simp only [Matrix.mul_assoc],
        trace_mul_comm Uᵀ, Matrix.mul_assoc, hUU', Matrix.mul_one]
    rw [this, trace]
    congr 1; ext j
    rw [mulVec_mulVec, mulVec_mulVec, mulVec_single_one, mulVec_single_one]
    simp [diag, mul_apply, dotProduct, mul_comm]
  rw [e1, hN, Finset.mul_sum]
  refine Finset.sum_le_sum fun j _ => ?_
  obtain ⟨h1, h2⟩ := nuclearBase_col A U μ hUU hspec j
  refine (nuclearBase_cs _ _).trans ?_
  rw [h2]
  have := nuclearBase_op_le G (U *ᵥ Pi.single j 1)
  rw [h1, mul_one] at this
  exact mul_le_mul_of_nonneg_right this (Real.sqrt_nonneg _)


/-! polar part -/

theorem nuclearBase_diag_id (t : ℝ) :
    t⁻¹ * (t⁻¹ * t ^ 2 * t⁻¹) = t⁻¹ ∧ t⁻¹ * t⁻¹ * t⁻¹ * t ^ 2 = t⁻¹ ∧
      (1 - t⁻¹ * t ^ 2 * t⁻¹) * t ^ 2 = 0 ∧ t ^ 2 * t⁻¹ = t := by
  by_cases h : t = 0
  · simp [h]
  · refine ⟨?_, ?_, ?_, ?_⟩ <;> field_simp <;> ring

theorem nuclearBase_polar {d1 d2 : ℕ} (A : Matrix (Fin d1) (Fin d2) ℝ) :
    ∃ Z : Matrix (Fin d1) (Fin d2) ℝ, traceInner A Z = nuclearNorm A ∧ Z * Zᵀ * Z = Z ∧
      (∃ X : Matrix (Fin d2) (Fin d2) ℝ, Z = A * X) ∧
      (∀ Y : Matrix (Fin d2) (Fin d2) ℝ, A * Y = 0 → Z * Y = 0) ∧ A * (Zᵀ * Z) = A := by
  obtain ⟨U, μ, hUU, hUU', hspec, hμ, hN, -⟩ := nuclearBase_spec A
  set s : Fin d2 → ℝ := fun j => (Real.sqrt (μ j))⁻¹ with hs
  have hid : ∀ j, s j * (s j * μ j * s j) = s j ∧ s j * s j * s j * μ j = s j ∧
      (1 - s j * μ j * s j) * μ j = 0 ∧ μ j * s j = Real.sqrt (μ j) := fun j => by
    have := nuclearBase_diag_id (Real.sqrt (μ j)); rwa [Real.sq_sqrt (hμ j)] at this
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
  · rw [nuclearBase_ti_eq, ← Matrix.mul_assoc, hspec, hX, hN,
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

theorem nuclearBase_nuc_nonneg {d1 d2 : ℕ} (A : Matrix (Fin d1) (Fin d2) ℝ) : 0 ≤ nuclearNorm A :=
  Finset.sum_nonneg fun _ _ => Real.sqrt_nonneg _

theorem nuclearBase_pi_ti {d1 d2 : ℕ} (Z A : Matrix (Fin d1) (Fin d2) ℝ) (hZ : Z * Zᵀ * Z = Z) :
    traceInner Z A ≤ nuclearNorm A := by
  have h1 := nuclearBase_holder Z A
  have h2 := nuclearBase_pi_op Z hZ
  have h3 := nuclearBase_nuc_nonneg A
  nlinarith

theorem nuclearBase_neg_pi {d1 d2 : ℕ} (Z : Matrix (Fin d1) (Fin d2) ℝ) (hZ : Z * Zᵀ * Z = Z) :
    (-Z) * (-Z)ᵀ * (-Z) = -Z := by
  simp [transpose_neg, hZ]

theorem nuclearBase_nuc_add {d1 d2 : ℕ} (A B : Matrix (Fin d1) (Fin d2) ℝ) :
    nuclearNorm (A + B) ≤ nuclearNorm A + nuclearNorm B := by
  obtain ⟨Z, h1, h2, -⟩ := nuclearBase_polar (A + B)
  rw [← h1, nuclearBase_ti_add_left, nuclearBase_ti_comm A, nuclearBase_ti_comm B]
  exact add_le_add (nuclearBase_pi_ti Z A h2) (nuclearBase_pi_ti Z B h2)

theorem nuclearBase_nuc_smul {d1 d2 : ℕ} (t : ℝ) (ht : 0 ≤ t) (A : Matrix (Fin d1) (Fin d2) ℝ) :
    nuclearNorm (t • A) ≤ t * nuclearNorm A := by
  obtain ⟨Z, h1, h2, -⟩ := nuclearBase_polar (t • A)
  rw [← h1, nuclearBase_ti_smul_left, nuclearBase_ti_comm]
  exact mul_le_mul_of_nonneg_left (nuclearBase_pi_ti Z A h2) ht

theorem nuclearBase_nuc_rank1 {d1 d2 : ℕ} (u : Fin d1 → ℝ) (x : Fin d2 → ℝ) :
    nuclearNorm (vecMulVec u x) ≤ nuclearBase_nm u * nuclearBase_nm x := by
  obtain ⟨Z, h1, h2, -⟩ := nuclearBase_polar (vecMulVec u x)
  rw [← h1, nuclearBase_ti_comm, nuclearBase_ti_vecMulVec]
  exact (nuclearBase_cs _ _).trans
    (mul_le_mul_of_nonneg_left (nuclearBase_pi Z h2 x) (nuclearBase_nm_nonneg u))

theorem nuclearBase_nuc_rank {d1 d2 : ℕ} (M : Matrix (Fin d1) (Fin d2) ℝ) :
    nuclearNorm M ≤ M.rank * opNorm M := by
  obtain ⟨U, μ, hUU, hUU', hspec, hμ, hN, hrk⟩ := nuclearBase_spec M
  have hle : ∀ j, Real.sqrt (μ j) ≤ opNorm M := fun j => by
    obtain ⟨h1, h2⟩ := nuclearBase_col M U μ hUU hspec j
    rw [← h2]
    have := nuclearBase_op_le M (U *ᵥ Pi.single j 1)
    rwa [h1, mul_one] at this
  rw [hN, hrk, Fintype.card_subtype, ← Finset.sum_filter_of_ne (p := fun j => μ j ≠ 0)]
  · refine (Finset.sum_le_card_nsmul _ _ _ (fun j _ => hle j)).trans ?_
    rw [nsmul_eq_mul]
  · intro j _ h hμ0; apply h; rw [hμ0, Real.sqrt_zero]


theorem nuclearBase_ti_zero_left {d1 d2 : ℕ} (A : Matrix (Fin d1) (Fin d2) ℝ) :
    traceInner 0 A = 0 := by
  simp [traceInner]

/-! decomposability / cone condition -/

theorem nuclearBase_cone {d1 d2 : ℕ} (Θ Δ : Matrix (Fin d1) (Fin d2) ℝ)
    (h : nuclearNorm (Θ + Δ) ≤ nuclearNorm Θ + nuclearNorm Δ / 2) :
    nuclearNorm Δ ≤ 8 * (Θ.rank : ℝ) * opNorm Δ := by
  obtain ⟨Z1, h1N, h1pi, ⟨X1, hX1⟩, -, h1Q⟩ := nuclearBase_polar Θ
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
  obtain ⟨Z2, h2N, h2pi, ⟨X2, hX2⟩, h2Y, -⟩ := nuclearBase_polar Δ2
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
    have hZ := nuclearBase_pi_ti (Z1 + Z2) (Θ + Δ) hZpi
    have t1 : traceInner Z1 Θ = nuclearNorm Θ := by rw [nuclearBase_ti_comm]; exact h1N
    have t2 : traceInner Z2 Θ = 0 := by
      rw [nuclearBase_ti_comm, hZ2', nuclearBase_ti_mul_right, h1Qt, hΘ1Q, nuclearBase_ti_zero_left]
    have t3 : traceInner Z1 Δ2 = 0 := by
      rw [hΔ2, nuclearBase_ti_mul_right, h1Qt, hZ11Q, nuclearBase_ti_zero_left]
    have t4 : traceInner Z2 Δ2 = nuclearNorm Δ2 := by rw [nuclearBase_ti_comm]; exact h2N
    have t5 : traceInner Z2 (Δ - Δ2) = 0 := by
      rw [hE, nuclearBase_ti_add_right, nuclearBase_ti_mul_left, hPt, hPZ2, nuclearBase_ti_zero_left,
        nuclearBase_ti_mul_right, hQt, hZ2Q, nuclearBase_ti_zero_left, add_zero]
    have t6 : -nuclearNorm (Δ - Δ2) ≤ traceInner Z1 (Δ - Δ2) := by
      have := nuclearBase_pi_ti (-Z1) (Δ - Δ2) (nuclearBase_neg_pi Z1 h1pi)
      rw [nuclearBase_ti_neg_left] at this; linarith
    have e : traceInner (Z1 + Z2) (Θ + Δ) = traceInner Z1 Θ + traceInner Z2 Θ +
        traceInner Z1 Δ2 + traceInner Z2 Δ2 + traceInner Z1 (Δ - Δ2) +
        traceInner Z2 (Δ - Δ2) := by
      have : Θ + Δ = Θ + Δ2 + (Δ - Δ2) := by abel
      rw [this]
      simp only [nuclearBase_ti_add_left, nuclearBase_ti_add_right]
      ring
    linarith
  have hsplit : nuclearNorm Δ ≤ nuclearNorm Δ2 + nuclearNorm (Δ - Δ2) := by
    have := nuclearBase_nuc_add Δ2 (Δ - Δ2); rwa [add_sub_cancel] at this
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
  have hop0 := nuclearBase_op_nonneg Δ
  have ho1 : opNorm (P * Δ) ≤ opNorm Δ := by
    refine nuclearBase_op_le_of _ hop0 (fun v => ?_)
    rw [← mulVec_mulVec]
    exact (nuclearBase_proj P hPt hPP _).trans (nuclearBase_op_le Δ v)
  have ho2 : opNorm ((1 - P) * Δ * Q) ≤ opNorm Δ := by
    refine nuclearBase_op_le_of _ hop0 (fun v => ?_)
    rw [← mulVec_mulVec, ← mulVec_mulVec]
    refine (nuclearBase_proj _ h1Pt h1PP _).trans ((nuclearBase_op_le Δ _).trans ?_)
    exact mul_le_mul_of_nonneg_left (nuclearBase_proj Q hQt hQQ v) hop0
  have hrk0 : (0 : ℝ) ≤ Θ.rank := Nat.cast_nonneg _
  have n1 := nuclearBase_nuc_rank (P * Δ)
  have n2 := nuclearBase_nuc_rank ((1 - P) * Δ * Q)
  have m1 : ((P * Δ).rank : ℝ) * opNorm (P * Δ) ≤ Θ.rank * opNorm Δ :=
    mul_le_mul hr1 ho1 (nuclearBase_op_nonneg _) hrk0
  have m2 : (((1 - P) * Δ * Q).rank : ℝ) * opNorm ((1 - P) * Δ * Q) ≤ Θ.rank * opNorm Δ :=
    mul_le_mul hr2 ho2 (nuclearBase_op_nonneg _) hrk0
  have hNE : nuclearNorm (Δ - Δ2) ≤ 2 * Θ.rank * opNorm Δ := by
    rw [hE]
    refine (nuclearBase_nuc_add _ _).trans ?_
    linarith
  linarith


theorem nuclearBase_ti_adj {d1 d2 n : ℕ} (Xs : Fin n → Matrix (Fin d1) (Fin d2) ℝ) (u : Fin n → ℝ)
    (a : ℝ) (D : Matrix (Fin d1) (Fin d2) ℝ) :
    traceInner (a • observationOpAdjoint Xs u) D = a * ∑ i, u i * observationOp Xs D i := by
  rw [nuclearBase_ti_smul_left]
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


-- Source module: NuclearFrobenius

namespace HighDimStat.MatrixRank
open Matrix

theorem nuclearF_sq {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) :
    frobeniusNorm A ^ 2 = traceInner A A := by
  unfold frobeniusNorm
  have hn : 0 ≤ ∑ i, ∑ j, (A i j) ^ 2 :=
    Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => sq_nonneg (A i j)
  rw [Real.sq_sqrt hn]
  simp [traceInner, sq]

theorem nuclearF_nonneg {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) :
    0 ≤ frobeniusNorm A := Real.sqrt_nonneg _

theorem nuclearF_cs {m n : ℕ} (A B : Matrix (Fin m) (Fin n) ℝ) :
    traceInner A B ≤ frobeniusNorm A * frobeniusNorm B := by
  simpa [traceInner, frobeniusNorm, Fintype.sum_prod_type] using
    (Real.sum_mul_le_sqrt_mul_sqrt Finset.univ
      (fun ij : Fin m × Fin n => A ij.1 ij.2)
      (fun ij : Fin m × Fin n => B ij.1 ij.2))

theorem nuclearF_cs_sq {m n : ℕ} (A B : Matrix (Fin m) (Fin n) ℝ) :
    traceInner A B ^ 2 ≤ traceInner A A * traceInner B B := by
  simpa [traceInner, Fintype.sum_prod_type, sq] using
    (Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
      (fun ij : Fin m × Fin n => A ij.1 ij.2)
      (fun ij : Fin m × Fin n => B ij.1 ij.2))

theorem nuclearF_self_nonneg {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) :
    0 ≤ traceInner A A := by rw [← nuclearF_sq]; positivity

theorem nuclearF_ti_sub_left {m n : ℕ} (A B C : Matrix (Fin m) (Fin n) ℝ) :
    traceInner (A-B) C = traceInner A C - traceInner B C := by
  simp [traceInner, Matrix.sub_apply, sub_mul, Finset.sum_sub_distrib]

theorem nuclearF_ti_diag {n : ℕ} (a b : Fin n → ℝ) :
    traceInner (diagonal a) (diagonal b) = ∑ i, a i * b i := by
  simp [traceInner, Matrix.diagonal_apply]

theorem nuclearF_nuc_sum {m n : ℕ} {ι : Type*} [Fintype ι]
    (A : ι → Matrix (Fin m) (Fin n) ℝ) : nuclearNorm (∑ i, A i) ≤ ∑ i, nuclearNorm (A i) := by
  classical
  have hzero : nuclearNorm (0 : Matrix (Fin m) (Fin n) ℝ) = 0 := by
    have h := nuclearBase_nuc_rank (0 : Matrix (Fin m) (Fin n) ℝ)
    simp only [Matrix.rank_zero, Nat.cast_zero, zero_mul] at h
    exact le_antisymm h (nuclearBase_nuc_nonneg _)
  exact Finset.le_sum_of_subadditive nuclearNorm hzero.le
    (fun A B => nuclearBase_nuc_add A B) _ _

theorem nuclearF_nuc_diag {n : ℕ} (a : Fin n → ℝ) :
    nuclearNorm (diagonal a) = ∑ i, |a i| := by
  classical
  have he : diagonal a = ∑ i, vecMulVec (Pi.single i (a i)) (Pi.single i 1) := by
    ext i j
    simp [Matrix.diagonal_apply, Matrix.vecMulVec_apply, Matrix.sum_apply,
      Pi.single_apply, mul_ite, ite_mul]
    split_ifs with h
    · subst j; rfl
    · rfl
  have hupper : nuclearNorm (diagonal a) ≤ ∑ i, |a i| := by
    rw [he]
    refine (nuclearF_nuc_sum _).trans (Finset.sum_le_sum fun i _ => ?_)
    refine (nuclearBase_nuc_rank1 _ _).trans_eq ?_
    simp [nuclearBase_nm, Pi.single_apply, Real.sqrt_sq_eq_abs]
  let s : Fin n → ℝ := fun i => if 0 ≤ a i then 1 else -1
  have hpi : diagonal s * (diagonal s)ᵀ * diagonal s = diagonal s := by
    simp only [Matrix.diagonal_transpose, Matrix.diagonal_mul_diagonal]
    congr 1; ext i; dsimp [s]; split_ifs <;> norm_num
  have hlo := nuclearBase_pi_ti (diagonal s) (diagonal a) hpi
  rw [nuclearF_ti_diag] at hlo
  have hprod : ∀ i, s i * a i = |a i| := by
    intro i; dsimp [s]; split_ifs with h
    · simp [abs_of_nonneg h]
    · simp [abs_of_neg (lt_of_not_ge h)]
  simp only [hprod] at hlo
  exact le_antisymm hupper hlo

end HighDimStat.MatrixRank

-- Source module: NuclearCounterexampleData

namespace HighDimStat.MatrixRank.NuclearCounterexample
open Matrix
noncomputable section

def blocks (a b c : ℝ) (i : Fin 101) : ℝ :=
  if i.val = 0 then a else if i.val ≤ 50 then b else c

theorem sum_blocks (a b c : ℝ) : ∑ i, blocks a b c i = a+50*b+50*c := by
  rw [Fin.sum_univ_succ]
  have h1 : ∀ i : Fin 50, blocks a b c ((Fin.castAdd 50 i : Fin 100).succ)=b := by
    intro i; dsimp [blocks]; split_ifs <;> first | rfl | omega
  have h2 : ∀ i : Fin 50, blocks a b c ((Fin.natAdd 50 i : Fin 100).succ)=c := by
    intro i; dsimp [blocks]; split_ifs <;> first | rfl | omega
  rw [Fin.sum_univ_add (fun i : Fin (50+50) => blocks a b c i.succ)]
  simp only [h1,h2,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
  norm_num [blocks]
  ring

theorem blocks_mul (a b c x y z : ℝ) :
    (fun i => blocks a b c i * blocks x y z i) = blocks (a*x) (b*y) (c*z) := by
  funext i; dsimp [blocks]; split_ifs <;> rfl

theorem blocks_sub (a b c x y z : ℝ) :
    (fun i => blocks a b c i - blocks x y z i) = blocks (a-x) (b-y) (c-z) := by
  funext i; dsimp [blocks]; split_ifs <;> rfl

def Theta : Matrix (Fin 101) (Fin 101) ℝ := diagonal (blocks 2 (2/25) 0)
def Hat : Matrix (Fin 101) (Fin 101) ℝ := diagonal (blocks 1 0 (7/25))
def D : Matrix (Fin 101) (Fin 101) ℝ := diagonal (blocks (-1) (-2/25) (7/25))
def S : Matrix (Fin 101) (Fin 101) ℝ := diagonal (blocks (-1) (-1) 1)
def Z : Matrix (Fin 101) (Fin 101) ℝ := diagonal (blocks (-3/200) (-3/200) (-1/200))
def G : Matrix (Fin 101) (Fin 101) ℝ := (1/200 : ℝ) • S

theorem D_eq : D = Hat-Theta := by
  unfold D Hat Theta
  rw [diagonal_sub, blocks_sub]
  norm_num

theorem Z_eq : Z = G-(1/100 : ℝ) • (1 : Matrix (Fin 101) (Fin 101) ℝ) := by
  ext i j
  simp only [Z,G,S,Matrix.sub_apply,Matrix.smul_apply,smul_eq_mul,Matrix.diagonal_apply,
    Matrix.one_apply]
  by_cases h : i=j
  · subst j; dsimp [blocks]; split_ifs <;> norm_num
  · simp [h]

theorem D_sq : traceInner D D = 131/25 := by
  rw [D,nuclearF_ti_diag,blocks_mul,sum_blocks]; norm_num

theorem DS : traceInner D S = 19 := by
  rw [D,S,nuclearF_ti_diag,blocks_mul,sum_blocks]; norm_num

theorem DZ : traceInner D Z = 1/200 := by
  rw [D,Z,nuclearF_ti_diag,blocks_mul,sum_blocks]; norm_num

theorem SS : traceInner S S = 101 := by
  rw [S,nuclearF_ti_diag,blocks_mul,sum_blocks]; norm_num

theorem S_pi : S*Sᵀ*S=S := by
  simp only [S,Matrix.diagonal_transpose,Matrix.diagonal_mul_diagonal]
  congr 1; funext i; dsimp [blocks]; split_ifs <;> norm_num

theorem I_pi : (1 : Matrix (Fin 101) (Fin 101) ℝ)*1ᵀ*1=1 := by simp

theorem Theta_nuc : nuclearNorm Theta=6 := by
  rw [Theta,nuclearF_nuc_diag]
  have : (fun i => |blocks 2 (2/25) 0 i|)=blocks 2 (2/25) 0 := by
    funext i; dsimp [blocks]; split_ifs <;> norm_num
  rw [this,sum_blocks]; norm_num

theorem Hat_nuc : nuclearNorm Hat=15 := by
  rw [Hat,nuclearF_nuc_diag]
  have : (fun i => |blocks 1 0 (7/25) i|)=blocks 1 0 (7/25) := by
    funext i; dsimp [blocks]; split_ifs <;> norm_num
  rw [this,sum_blocks]; norm_num

theorem I_Hat : traceInner (1 : Matrix (Fin 101) (Fin 101) ℝ) Hat = nuclearNorm Hat := by
  rw [Hat_nuc]
  have hid : (1 : Matrix (Fin 101) (Fin 101) ℝ)=diagonal (blocks 1 1 1) := by
    ext i j; simp [Matrix.diagonal_apply,Matrix.one_apply,blocks]
  rw [hid,Hat,nuclearF_ti_diag,blocks_mul,sum_blocks]; norm_num

def U : Matrix (Fin 101) (Fin 101) ℝ := (2 : ℝ) • Z + (19/32 : ℝ) • S

theorem U_sq : traceInner U U = 23603501/640000 := by
  have he : U = diagonal (blocks (-499/800) (-499/800) (467/800)) := by
    ext i j
    by_cases h : i=j
    · subst j
      simp only [U,Z,S,Matrix.add_apply,Matrix.smul_apply,smul_eq_mul,
        Matrix.diagonal_apply_eq]
      dsimp [blocks]; split_ifs <;> norm_num
    · simp [U,Z,S,Matrix.diagonal_apply,h]
  rw [he,nuclearF_ti_diag,blocks_mul,sum_blocks]; norm_num

end
end HighDimStat.MatrixRank.NuclearCounterexample

-- Source module: NuclearCounterexampleGeometry

namespace HighDimStat.MatrixRank.NuclearCounterexample
open Matrix
noncomputable section

abbrev Mat := Matrix (Fin 101) (Fin 101) ℝ

def P (A : Mat) : Mat := A - (traceInner D A / (131/25)) • D

def H (A : Mat) : Mat := (200 * traceInner Z A) • Z + (200 : ℝ) • P A

def energy (A : Mat) : ℝ := 200 * traceInner Z A ^ 2 + 200 * traceInner (P A) (P A)

theorem P_orth (A : Mat) : traceInner D (P A)=0 := by
  rw [P,nuclearBase_ti_sub_right,nuclearBase_ti_smul_right,D_sq]; ring

theorem P_selfadj (A B : Mat) : traceInner (P A) B = traceInner A (P B) := by
  rw [P,P,nuclearF_ti_sub_left,nuclearBase_ti_sub_right,
    nuclearBase_ti_smul_left,nuclearBase_ti_smul_right]
  rw [nuclearBase_ti_comm A D]; ring

theorem P_idem (A : Mat) : P (P A)=P A := by rw [P,P_orth]; simp

theorem P_D : P D=0 := by rw [P,D_sq]; norm_num

theorem P_smul (a : ℝ) (A : Mat) : P (a • A) = a • P A := by
  unfold P
  rw [nuclearBase_ti_smul_right]
  simp only [smul_sub,smul_smul]
  congr 1; congr 1; ring

theorem P_add (A B : Mat) : P (A+B)=P A+P B := by
  unfold P
  rw [nuclearBase_ti_add_right,add_div,add_smul]
  abel

theorem H_D : H D=Z := by
  rw [H,P_D,nuclearBase_ti_comm Z D,DZ]; norm_num

theorem inner_H (A B : Mat) : traceInner (H A) B =
    200*traceInner Z A*traceInner Z B + 200*traceInner (P A) (P B) := by
  rw [H,nuclearBase_ti_add_left,nuclearBase_ti_smul_left,nuclearBase_ti_smul_left]
  have he : traceInner (P A) B=traceInner (P A) (P B) := by
    rw [P_selfadj,P_selfadj,P_idem]
  rw [he]

theorem energy_eq (A : Mat) : energy A=traceInner (H A) A := by
  rw [inner_H]; unfold energy; ring

theorem energy_nonneg (A : Mat) : 0 ≤ energy A := by
  unfold energy; positivity [nuclearF_self_nonneg (P A)]

theorem energy_rsc (A : Mat) :
    frobeniusNorm A ^ 2 - nuclearNorm A ^ 2 / 64 ≤ energy A := by
  let a : ℝ := traceInner D A / (131/25)
  let V : Mat := P A
  have hDV : traceInner D V=0 := P_orth A
  have he : A=a • D+V := by dsimp [a,V,P]; abel
  have hAA : traceInner A A=a^2*(131/25)+traceInner V V := by
    conv_lhs => rw [he]
    rw [nuclearBase_ti_add_left,nuclearBase_ti_add_right,nuclearBase_ti_add_right,
      nuclearBase_ti_smul_left,nuclearBase_ti_smul_left,nuclearBase_ti_smul_right,
      nuclearBase_ti_smul_right,D_sq,hDV,nuclearBase_ti_comm V D,hDV]
    ring
  have hZA : traceInner Z A=a/200+traceInner Z V := by
    rw [he,nuclearBase_ti_add_right,nuclearBase_ti_smul_right,nuclearBase_ti_comm Z D,DZ]; ring
  have hSA : traceInner S A=19*a+traceInner S V := by
    rw [he,nuclearBase_ti_add_right,nuclearBase_ti_smul_right,nuclearBase_ti_comm S D,DS]; ring
  have hUV : traceInner U V=2*traceInner Z V+19/32*traceInner S V := by
    rw [U,nuclearBase_ti_add_left,nuclearBase_ti_smul_left,nuclearBase_ti_smul_left]
  have hcs := nuclearF_cs_sq U V
  rw [U_sq] at hcs
  have hv := nuclearF_self_nonneg V
  have hbound : traceInner A A-traceInner S A^2/64 ≤ energy A := by
    rw [hAA,hSA,energy,hZA]
    change a^2*(131/25)+traceInner V V-(19*a+traceInner S V)^2/64 ≤
      200*(a/200+traceInner Z V)^2+200*traceInner V V
    have hy := sq_nonneg (a/2+traceInner U V)
    rw [hUV] at hy hcs
    nlinarith [hy,sq_nonneg (traceInner Z V),
      sq_nonneg (traceInner S V),sq_nonneg a]
  have hs := nuclearBase_pi_ti S A S_pi
  have hns := nuclearBase_pi_ti (-S) A (nuclearBase_neg_pi S S_pi)
  rw [nuclearBase_ti_neg_left] at hns
  have hn := nuclearBase_nuc_nonneg A
  have hsq : traceInner S A^2 ≤ nuclearNorm A^2 := by nlinarith
  rw [nuclearF_sq]
  linarith

def beta : ℝ := traceInner D G / (1/200)
def Vnoise : Mat := (1/200 : ℝ) • (G-beta • Z)
def alpha : ℝ := beta-traceInner Z Vnoise / (1/200)
def W : Mat := alpha • D + Vnoise

theorem Vnoise_orth : traceInner D Vnoise=0 := by
  rw [Vnoise,nuclearBase_ti_smul_right,nuclearBase_ti_sub_right,nuclearBase_ti_smul_right,DZ]
  unfold beta; ring

theorem P_W : P W=Vnoise := by
  rw [W,P_add,P_smul,P_D]
  have h : P Vnoise=Vnoise := by rw [P,Vnoise_orth]; simp
  rw [h]; simp

theorem H_W : H W=G := by
  rw [H,P_W,W,nuclearBase_ti_add_right,nuclearBase_ti_smul_right,
    nuclearBase_ti_comm Z D,DZ]
  unfold alpha Vnoise
  module

theorem G_op : opNorm G ≤ (1/100 : ℝ)/2 := by
  apply nuclearBase_op_le_of G (by norm_num)
  intro v
  rw [G,Matrix.smul_mulVec,nuclearBase_nm_smul]
  norm_num
  exact nuclearBase_pi S S_pi v

end
end HighDimStat.MatrixRank.NuclearCounterexample

-- Source module: NuclearCounterexampleTail

namespace HighDimStat.MatrixRank.NuclearCounterexample
open Matrix
noncomputable section

theorem Theta_gram : Thetaᵀ*Theta=diagonal (blocks 4 (4/625) 0) := by
  rw [Theta,Matrix.diagonal_transpose,Matrix.diagonal_mul_diagonal,blocks_mul]
  norm_num

theorem first_singular : 2 ≤ singularValues Theta (0 : Fin 101) := by
  let hP := Matrix.posSemidef_conjTranspose_mul_self Theta
  let hT := hP.1
  have hmem : (4 : ℝ) ∈ spectrum ℝ (Thetaᴴ*Theta) := by
    rw [Matrix.conjTranspose_eq_transpose_of_trivial,Theta_gram,spectrum_diagonal]
    exact ⟨0,by norm_num [blocks]⟩
  rw [hT.spectrum_real_eq_range_eigenvalues] at hmem
  obtain ⟨j,hj⟩ := hmem
  have heig : 4 ≤ hT.eigenvalues₀ ((finCongr (Fintype.card_fin 101)).symm (0 : Fin 101)) := by
    have hz : ((finCongr (Fintype.card_fin 101)).symm (0 : Fin 101) :
      Fin (Fintype.card (Fin 101)))=0 := by simp [finCongr]
    rw [hz]
    have hanti : hT.eigenvalues j ≤ hT.eigenvalues₀ 0 := by
      unfold Matrix.IsHermitian.eigenvalues
      exact hT.eigenvalues₀_antitone (Fin.zero_le _)
    change hT.eigenvalues j = 4 at hj
    rw [hj] at hanti
    exact hanti
  change 2 ≤ Real.sqrt (hT.eigenvalues₀ _)
  have := Real.sqrt_le_sqrt heig
  norm_num at this
  exact this

theorem tail_eq : tailSingularSum Theta 1 = nuclearNorm Theta-singularValues Theta (0 : Fin 101) := by
  have he : (Finset.univ : Finset (Fin 101)).filter (fun j => 1 ≤ j.val)=Finset.univ.erase 0 := by
    ext j; simp only [Finset.mem_filter,Finset.mem_univ,true_and,Finset.mem_erase,and_true]
    constructor
    · intro h hz; subst j; norm_num at h
    · intro h; by_contra hn; apply h; apply Fin.ext; omega
  unfold tailSingularSum
  rw [he,Finset.sum_erase_eq_sub (by simp)]
  rfl

theorem tail_bounds : 0 ≤ tailSingularSum Theta 1 ∧ tailSingularSum Theta 1 ≤ 4 := by
  constructor
  · unfold tailSingularSum
    exact Finset.sum_nonneg fun j _ => Real.sqrt_nonneg _
  · rw [tail_eq,Theta_nuc]
    linarith [first_singular]

end
end HighDimStat.MatrixRank.NuclearCounterexample

-- Source module: NuclearCounterexampleObservations

namespace HighDimStat.MatrixRank.NuclearCounterexample
open Matrix
noncomputable section
set_option maxRecDepth 4000
set_option maxHeartbeats 1000000

abbrev Ix := Unit ⊕ (Fin 101 × Fin 101)
def N : ℕ := 10202
def idxEquiv : Ix ≃ Fin N := (Fintype.equivFin Ix).trans
  (finCongr (by norm_num [Ix,N]))

def basis (ij : Fin 101 × Fin 101) : Mat :=
  vecMulVec (Pi.single ij.1 1) (Pi.single ij.2 1)

theorem basis_ti (ij : Fin 101 × Fin 101) (A : Mat) : traceInner (basis ij) A=A ij.1 ij.2 := by
  simp [basis,traceInner,Matrix.vecMulVec_apply,Pi.single_apply,ite_mul,mul_ite]

theorem ti_ext (A B : Mat) (h : ∀ C : Mat, traceInner A C=traceInner B C) : A=B := by
  ext i j
  have he := h (basis (i,j))
  rw [nuclearBase_ti_comm A,nuclearBase_ti_comm B,basis_ti,basis_ti] at he
  exact he

def scale : ℝ := Real.sqrt (200*(N : ℝ))
def raw : Ix → Mat := Sum.elim (fun _ => scale • Z) (fun ij => scale • P (basis ij))
def Xs (i : Fin N) : Mat := raw (idxEquiv.symm i)

theorem N_val : N=10202 := by norm_num [N,Ix]
theorem N_pos : 0 < (N : ℝ) := by rw [N_val]; norm_num

theorem scale_sq : scale^2=200*(N : ℝ) := by
  exact Real.sq_sqrt (by positivity [N_pos])

theorem raw_gram (A B : Mat) :
    ∑ j : Ix, traceInner (raw j) A * traceInner (raw j) B =
      scale^2*(traceInner Z A*traceInner Z B+traceInner (P A) (P B)) := by
  have hproj : ∀ ij, traceInner (P (basis ij)) A = P A ij.1 ij.2 := by
    intro ij; rw [P_selfadj,basis_ti]
  have hprojB : ∀ ij, traceInner (P (basis ij)) B = P B ij.1 ij.2 := by
    intro ij; rw [P_selfadj,basis_ti]
  simp only [raw,Fintype.sum_sum_type,Sum.elim_inl,Sum.elim_inr,
    nuclearBase_ti_smul_left,Fintype.sum_unique,hproj,hprojB]
  have he : ∑ ij : Fin 101 × Fin 101,
      scale*P A ij.1 ij.2*(scale*P B ij.1 ij.2)=scale^2*traceInner (P A) (P B) := by
    simp only [traceInner,Fintype.sum_prod_type,Finset.mul_sum]
    congr 1; funext i; congr 1; funext j; ring
  rw [he]; ring

theorem gram (A B : Mat) :
    traceInner ((1/(N : ℝ)) • observationOpAdjoint Xs (observationOp Xs A)) B =
      traceInner (H A) B := by
  rw [nuclearBase_ti_adj]
  unfold observationOp
  have he : (∑ i : Fin N, traceInner (Xs i) A*traceInner (Xs i) B)=
      ∑ j : Ix, traceInner (raw j) A*traceInner (raw j) B :=
    by
      simpa only [Xs] using (Equiv.sum_comp idxEquiv.symm
        (fun j : Ix => traceInner (raw j) A*traceInner (raw j) B))
  rw [he,raw_gram,scale_sq,inner_H]
  have hn := ne_of_gt N_pos
  field_simp [hn]

theorem gram_matrix (A : Mat) :
    (1/(N : ℝ)) • observationOpAdjoint Xs (observationOp Xs A)=H A := by
  exact ti_ext _ _ (gram A)

theorem prediction_energy (A : Mat) :
    (∑ i, observationOp Xs A i^2)/(N : ℝ)=energy A := by
  have he := gram A A
  rw [nuclearBase_ti_adj,← energy_eq] at he
  simpa only [sq,div_eq_mul_inv,one_div,mul_comm,mul_one] using he

def noise : Fin N → ℝ := observationOp Xs W

theorem noise_adj : (1/(N : ℝ)) • observationOpAdjoint Xs noise=G := by
  rw [noise,gram_matrix,H_W]

theorem rsc : RSCNuclear Xs 1 ((N : ℝ)/(128*202)) := by
  intro A
  have he := prediction_energy A
  have hb := energy_rsc A
  have hn := ne_of_gt N_pos
  have e1 : (∑ i, observationOp Xs A i^2)/(2*(N : ℝ))=energy A/2 := by
    rw [← he]; field_simp [hn]
  have e2 : (N : ℝ)/(128*202)*((101 : ℝ)+101)/(N : ℝ)=1/128 := by
    field_simp; norm_num
  change _ ≥ _
  rw [e1]
  norm_num only [Nat.cast_ofNat] at *
  rw [e2]
  norm_num
  linarith

theorem noise_good : opNorm ((1/(N : ℝ)) • observationOpAdjoint Xs noise) ≤ (1/100 : ℝ)/2 := by
  rw [noise_adj]; exact G_op

end
end HighDimStat.MatrixRank.NuclearCounterexample

-- Source module: NuclearCounterexampleEnd

namespace HighDimStat.MatrixRank.NuclearCounterexample
open Matrix
noncomputable section
set_option maxRecDepth 4000
set_option maxHeartbeats 1000000

theorem optimal : IsNuclearNormLSSolution Xs
    (fun i => traceInner (Xs i) Theta+noise i) (1/100) Hat := by
  intro T
  let E : Mat := T-Hat
  let residual : Fin N → ℝ := fun i => traceInner (Xs i) Theta+noise i-observationOp Xs Hat i
  have hres : ∀ i, residual i=noise i-observationOp Xs D i := by
    intro i
    dsimp [residual,observationOp]
    rw [D_eq,nuclearBase_ti_sub_right]; ring
  have hcand : ∀ i, traceInner (Xs i) Theta+noise i-observationOp Xs T i=
      residual i-observationOp Xs E i := by
    intro i
    dsimp [residual,E,observationOp]
    rw [nuclearBase_ti_sub_right]; ring
  have hinner : 1/(N : ℝ)*∑ i, residual i*observationOp Xs E i=
      1/100*traceInner (1 : Mat) E := by
    have hnoise := nuclearBase_ti_adj Xs noise (1/(N : ℝ)) E
    rw [noise_adj] at hnoise
    have hd := gram D E
    rw [H_D,nuclearBase_ti_adj] at hd
    have he : G-Z=(1/100 : ℝ) • (1 : Mat) := by rw [Z_eq]; abel
    have hdiff := nuclearF_ti_sub_left G Z E
    rw [he,nuclearBase_ti_smul_left] at hdiff
    simp only [hres,sub_mul,Finset.sum_sub_distrib] 
    nlinarith
  have hsupport := nuclearBase_pi_ti (1 : Mat) T I_pi
  have hE : traceInner (1 : Mat) E=traceInner (1 : Mat) T-nuclearNorm Hat := by
    dsimp only [E]
    rw [nuclearBase_ti_sub_right,I_Hat]
  rw [hE] at hinner
  have hexp : ∑ i, (residual i-observationOp Xs E i)^2=
      ∑ i, residual i^2-2*∑ i, residual i*observationOp Xs E i+
        ∑ i, observationOp Xs E i^2 := by
    have hpoint : ∀ i, (residual i-observationOp Xs E i)^2=
        residual i^2-2*(residual i*observationOp Xs E i)+observationOp Xs E i^2 :=
      fun i => by ring
    simp only [hpoint,Finset.sum_add_distrib,Finset.sum_sub_distrib,← Finset.mul_sum]
  have h2c : 2*(1/(2*(N : ℝ)))=1/(N : ℝ) := by field_simp
  rw [← h2c] at hinner
  have hS : 0 ≤ ∑ i : Fin N, (observationOp Xs E i)^2 :=
    Finset.sum_nonneg (s := Finset.univ)
      (f := fun i : Fin N => (observationOp Xs E i)^2)
      (fun i _ => sq_nonneg (observationOp Xs E i))
  have hc : (0 : ℝ) ≤ 1/(2*(N : ℝ)) :=
    div_nonneg zero_le_one (mul_nonneg (by norm_num) N_pos.le)
  have hnonneg := mul_nonneg hc hS
  change (1/(2*(N : ℝ)))*(∑ i, residual i^2)+1/100*nuclearNorm Hat ≤ _
  simp only [hcand]
  rw [hexp]
  nlinarith

theorem conclusion_fails : ¬ (frobeniusNorm (Hat-Theta))^2 ≤
    9/2*((1/100 : ℝ)^2/1^2)*(1 : ℕ)+
      1/1*(2*(1/100 : ℝ)*tailSingularSum Theta 1+
        32*((N : ℝ)/(128*202))*((101 : ℝ)+101)/(N : ℝ)*(tailSingularSum Theta 1)^2) := by
  rw [← D_eq,nuclearF_sq,D_sq]
  have he : 32*((N : ℝ)/(128*202))*((101 : ℝ)+101)/(N : ℝ)=1/4 := by
    have hn := ne_of_gt N_pos
    field_simp; norm_num
  rw [he]
  norm_num
  obtain ⟨ht0,ht4⟩ := tail_bounds
  have ht2 : tailSingularSum Theta 1^2 ≤ 16 := by nlinarith
  nlinarith

end
end HighDimStat.MatrixRank.NuclearCounterexample

open HighDimStat.MatrixRank
open HighDimStat.MatrixRank.NuclearCounterexample

theorem solution : ¬ (∀ {d1 d2 n : ℕ}
    (Xs : Fin n → Matrix (Fin d1) (Fin d2) ℝ) (w : Fin n → ℝ)
    (Θstar Θhat : Matrix (Fin d1) (Fin d2) ℝ) (κ c0 lamN : ℝ) (r : ℕ),
    0 < κ → 0 ≤ c0 → 0 < lamN → RSCNuclear Xs κ c0 →
    opNorm ((1/(n : ℝ)) • observationOpAdjoint Xs w) ≤ lamN/2 →
    IsNuclearNormLSSolution Xs (fun i => traceInner (Xs i) Θstar+w i) lamN Θhat →
    1 ≤ r → r ≤ min d1 d2 →
    (r : ℝ) ≤ κ*n/(128*c0*((d1 : ℝ)+d2)) →
    (frobeniusNorm (Θhat-Θstar))^2 ≤
      9/2*(lamN^2/κ^2)*r+1/κ*(2*lamN*tailSingularSum Θstar r+
        32*c0*((d1 : ℝ)+d2)/n*(tailSingularSum Θstar r)^2)) := by
  intro hall
  have hc0 : (0 : ℝ) ≤ (N : ℝ)/(128*202) := by positivity
  have hr : (1 : ℝ) ≤ 1*(N : ℝ)/(128*((N : ℝ)/(128*202))*((101 : ℝ)+101)) := by
    have hn := ne_of_gt N_pos
    field_simp; norm_num
  exact conclusion_fails (hall Xs noise Theta Hat 1 ((N : ℝ)/(128*202)) (1/100) 1
    (by norm_num) hc0 (by norm_num) rsc noise_good optimal (by norm_num) (by norm_num)
    (by simpa only [Nat.cast_ofNat,Nat.cast_one] using hr))


#print axioms solution
