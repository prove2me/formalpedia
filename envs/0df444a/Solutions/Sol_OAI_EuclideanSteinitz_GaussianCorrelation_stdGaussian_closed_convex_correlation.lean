-- Prove2me | solution 1 for OAI.EuclideanSteinitz.GaussianCorrelation.stdGaussian_closed_convex_correlation
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-18T19:20:30.156649+00:00
-- url     : https://prove2.me/submissions/5fb141e4-65ac-45f3-b0b1-c1fc50a087b1

import Mathlib
import Definitions.Def_OAIQWESB000

section
-- module Solutions.OAIQW_EuclideanSteinitzBergstrom.Compat
/-! Compatibility with the newer Lean core OpenAI's code was written against: lemmas it uses by
names this environment (Lean 4.33.1, Mathlib 0df444a) does not have yet. Each is the
corresponding `if_pos` / `if_neg` / `dif_pos` / `dif_neg`. -/
section OAICompat434
theorem ite_eq_left {α : Sort _} {p : Prop} {_ : Decidable p} {a b : α} (h : p) :
    (if p then a else b) = a := if_pos h
theorem ite_eq_right {α : Sort _} {p : Prop} {_ : Decidable p} {a b : α} (h : ¬p) :
    (if p then a else b) = b := if_neg h
end OAICompat434
end

section
-- module Solutions.OAIQW_EuclideanSteinitzBergstrom.Gain
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Contraction and gain potentials for positive semidefinite matrices. -/

namespace EuclideanSteinitz.Gain
open Matrix
open scoped MatrixOrder Matrix.Norms.L2Operator
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma inverseSqrt_psd (M : Matrix ι ι ℝ) : (inverseSqrt M).PosSemidef :=
  (CFC.sqrt_nonneg M).posSemidef.inv

lemma inverseSqrt_transpose (M : Matrix ι ι ℝ) : (inverseSqrt M).transpose = inverseSqrt M := by
  simpa only [conjTranspose_eq_transpose_of_trivial] using (inverseSqrt_psd M).1.eq

lemma inverseSqrt_mul_sqrt {M : Matrix ι ι ℝ} (hM : M.PosDef) :
    inverseSqrt M * CFC.sqrt M = 1 := by
  have h := (CFC.isUnit_sqrt_iff M hM.posSemidef.nonneg).mpr hM.isUnit
  let _ := h.invertible
  exact Matrix.inv_mul_of_invertible _

lemma sqrt_mul_inverseSqrt {M : Matrix ι ι ℝ} (hM : M.PosDef) :
    CFC.sqrt M * inverseSqrt M = 1 := by
  have h := (CFC.isUnit_sqrt_iff M hM.posSemidef.nonneg).mpr hM.isUnit
  let _ := h.invertible
  exact Matrix.mul_inv_of_invertible _

lemma inverseSqrt_sandwich {M : Matrix ι ι ℝ} (hM : M.PosDef) :
    inverseSqrt M * M * inverseSqrt M = 1 := by
  calc
    _ = inverseSqrt M * (CFC.sqrt M * CFC.sqrt M) * inverseSqrt M := by
      rw [CFC.sqrt_mul_sqrt_self M hM.posSemidef.nonneg]
    _ = 1 := by rw [← Matrix.mul_assoc, inverseSqrt_mul_sqrt hM, Matrix.one_mul,
      sqrt_mul_inverseSqrt hM]

lemma inverseSqrt_unit {M : Matrix ι ι ℝ} (hM : M.PosDef) : IsUnit (inverseSqrt M) := by
  rw [inverseSqrt, nonsing_inv_eq_ringInverse, isUnit_ringInverse]
  exact (CFC.isUnit_sqrt_iff M hM.posSemidef.nonneg).mpr hM.isUnit

omit [DecidableEq ι] in
lemma congruence_mono {A B : Matrix ι ι ℝ} (hAB : A ≤ B) (L : Matrix ι ι ℝ) :
    L * A * L.transpose ≤ L * B * L.transpose := by
  apply Matrix.le_iff.mpr
  simpa only [Matrix.mul_sub, Matrix.sub_mul, conjTranspose_eq_transpose_of_trivial]
    using (Matrix.le_iff.mp hAB).mul_mul_conjTranspose_same L

end EuclideanSteinitz.Gain

end OAI
end

section
-- module Solutions.OAIQW_EuclideanSteinitzBergstrom.Correlation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Gaussian correlation and symmetric convex events. -/

section

namespace EuclideanSteinitz.GaussianCorrelation
open Matrix Gain
open scoped MatrixOrder Matrix.Norms.L2Operator
variable {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]

omit [Fintype κ] [DecidableEq κ] in
lemma one_le_det {A : Matrix ι ι ℝ} (hA : A.IsHermitian) (h : 1 ≤ A) :
    1 ≤ A.det := by
  rw [hA.det_eq_prod_eigenvalues]
  have hs : ∀ x ∈ spectrum ℝ A, 1 ≤ x :=
    (algebraMap_le_iff_le_spectrum (R := ℝ) hA.isSelfAdjoint).mp (by simpa using h)
  simpa using Finset.one_le_prod (fun i (_ : i ∈ (Finset.univ : Finset ι)) =>
    hs _ (hA.spectrum_real_eq_range_eigenvalues.symm ▸ Set.mem_range_self i))

omit [Fintype κ] [DecidableEq κ] in
lemma det_mono {A B : Matrix ι ι ℝ} (hA : A.PosDef) (hB : B.PosDef) (h : A ≤ B) :
    A.det ≤ B.det := by
  let S := inverseSqrt A
  have hS : S.PosSemidef := inverseSqrt_psd A
  have hSA : S * A * S = 1 := inverseSqrt_sandwich hA
  have hSB : (S * B * S).PosDef := by
    simpa only [Matrix.star_eq_conjTranspose, conjTranspose_eq_transpose_of_trivial,
      inverseSqrt_transpose] using
      (inverseSqrt_unit hA).posDef_star_right_conjugate_iff.mpr hB
  have hAB' : 1 ≤ S * B * S := by
    have hm := congruence_mono h S
    simpa only [S, inverseSqrt_transpose, inverseSqrt_sandwich hA] using hm
  have hd := one_le_det hSB.1 hAB'
  have hdet : S.det * A.det * S.det = 1 := by simpa only [det_mul, det_one] using congrArg det hSA
  rw [det_mul, det_mul] at hd
  nlinarith [hA.det_pos, hS.det_nonneg, sq_nonneg S.det]

lemma blockCov_schur {A : Matrix ι ι ℝ} (hA : A.PosDef)
    (B : Matrix ι κ ℝ) (D : Matrix κ κ ℝ) (t : ℝ) :
    (blockCov A B D t).det = A.det * (D - t ^ 2 • (B.transpose * A⁻¹ * B)).det := by
  let _ := hA.isUnit.invertible
  rw [blockCov, det_fromBlocks₁₁, invOf_eq_nonsing_inv]
  congr 2
  simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul, pow_two]

omit [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ] in
lemma blockCov_diag_posDef {A : Matrix ι ι ℝ} {B : Matrix ι κ ℝ}
    {D : Matrix κ κ ℝ} (h : (blockCov A B D 1).PosDef) : A.PosDef ∧ D.PosDef := by
  constructor
  · exact h.submatrix Sum.inl_injective
  · exact h.submatrix Sum.inr_injective

lemma schur_posDef {A : Matrix ι ι ℝ} {B : Matrix ι κ ℝ} {D : Matrix κ κ ℝ}
    (h : (blockCov A B D 1).PosDef) : (D - B.transpose * A⁻¹ * B).PosDef := by
  have hA := (blockCov_diag_posDef h).1
  let _ := hA.isUnit.invertible
  have he : blockCov A B D 1 = fromBlocks A B Bᴴ D := by
    simp only [blockCov, one_smul, conjTranspose_eq_transpose_of_trivial]
  have hs : (D - B.transpose * A⁻¹ * B).PosSemidef := by
    simpa only [conjTranspose_eq_transpose_of_trivial] using
      (hA.fromBlocks₁₁ B D).mp (he ▸ h.posSemidef)
  apply hs.posDef_iff_det_ne_zero.mpr
  intro hz
  have hd := blockCov_schur hA B D 1
  simp only [one_pow, one_smul, hz, mul_zero] at hd
  exact h.det_pos.ne' hd

lemma blockCov_posDef {A : Matrix ι ι ℝ} {B : Matrix ι κ ℝ} {D : Matrix κ κ ℝ}
    (h : (blockCov A B D 1).PosDef) {t : ℝ} (ht : t ∈ Set.Icc 0 1) :
    (blockCov A B D t).PosDef := by
  have hA := (blockCov_diag_posDef h).1
  let _ := hA.isUnit.invertible
  have hK : (B.transpose * A⁻¹ * B).PosSemidef := by
    simpa only [conjTranspose_eq_transpose_of_trivial] using
      hA.posSemidef.inv.conjTranspose_mul_mul_same B
  have he : D - t ^ 2 • (B.transpose * A⁻¹ * B) =
      (D - B.transpose * A⁻¹ * B) + (1 - t ^ 2) • (B.transpose * A⁻¹ * B) := by
    module
  have hs : (D - t ^ 2 • (B.transpose * A⁻¹ * B)).PosDef := by
    rw [he]
    exact (schur_posDef h).add_posSemidef (hK.smul (by nlinarith [ht.1, ht.2]))
  have he' : blockCov A B D t = fromBlocks A (t • B) (t • B)ᴴ D := by
    simp only [blockCov, conjTranspose_eq_transpose_of_trivial, transpose_smul]
  have hp : (blockCov A B D t).PosSemidef := by
    rw [he', hA.fromBlocks₁₁]
    simpa only [conjTranspose_eq_transpose_of_trivial, transpose_smul,
      Matrix.smul_mul, Matrix.mul_smul, smul_smul, ← pow_two] using hs.posSemidef
  apply hp.posDef_iff_det_ne_zero.mpr
  rw [blockCov_schur hA]
  exact mul_ne_zero hA.det_pos.ne' hs.det_pos.ne'

lemma blockCov_det_antitone {A : Matrix ι ι ℝ} {B : Matrix ι κ ℝ} {D : Matrix κ κ ℝ}
    (h : (blockCov A B D 1).PosDef) :
    AntitoneOn (fun t => (blockCov A B D t).det) (Set.Icc 0 1) := by
  intro s hs t ht hst
  have hA := (blockCov_diag_posDef h).1
  have hK : (B.transpose * A⁻¹ * B).PosSemidef := by
    simpa only [conjTranspose_eq_transpose_of_trivial] using
      hA.posSemidef.inv.conjTranspose_mul_mul_same B
  have hpos (r : ℝ) (hr : r ∈ Set.Icc 0 1) :
      (D - r ^ 2 • (B.transpose * A⁻¹ * B)).PosDef := by
    have he : D - r ^ 2 • (B.transpose * A⁻¹ * B) =
        (D - B.transpose * A⁻¹ * B) + (1 - r ^ 2) • (B.transpose * A⁻¹ * B) := by module
    rw [he]
    exact (schur_posDef h).add_posSemidef (hK.smul (by nlinarith [hr.1, hr.2]))
  dsimp only
  rw [blockCov_schur hA, blockCov_schur hA]
  apply mul_le_mul_of_nonneg_left _ hA.det_pos.le
  apply det_mono (hpos t ht) (hpos s hs)
  apply sub_le_sub_left
  exact smul_le_smul_of_nonneg_right (by nlinarith [hs.1, ht.1]) hK.nonneg

omit [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ] in
lemma interpolate_one (p : ι → Bool) (R : Matrix ι ι ℝ) : interpolate p R 1 = R := by
  ext i j
  simp [interpolate]

omit [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ] in
lemma interpolate_blocks (p : ι → Bool) {R : Matrix ι ι ℝ} (hR : R.IsHermitian) (t : ℝ) :
    let e := Equiv.sumCompl (fun i => p i = true)
    (interpolate p R t).submatrix e e =
      blockCov (R.submatrix (Subtype.val : {i // p i = true} → ι) Subtype.val)
        (R.submatrix (Subtype.val : {i // p i = true} → ι)
          (Subtype.val : {i // ¬ p i = true} → ι))
        (R.submatrix (Subtype.val : {i // ¬ p i = true} → ι) Subtype.val) t := by
  dsimp only
  ext (i | i) (j | j) <;> dsimp [interpolate, blockCov, fromBlocks, Equiv.sumCompl]
  · simp only [i.prop, j.prop, ↓reduceIte]
  · simp only [i.prop, Bool.eq_false_iff.mpr j.prop, Bool.true_eq_false, ↓reduceIte]
  · simp only [Bool.eq_false_iff.mpr i.prop, j.prop, Bool.false_eq_true, ↓reduceIte]
    rw [show R (↑i) (↑j) = R (↑j) (↑i) from (hR.apply _ _).symm]
  · simp only [Bool.eq_false_iff.mpr i.prop, Bool.eq_false_iff.mpr j.prop, ↓reduceIte]

omit [Fintype κ] [DecidableEq κ] in
lemma interpolate_posDef (p : ι → Bool) {R : Matrix ι ι ℝ} (hR : R.PosDef)
    {t : ℝ} (ht : t ∈ Set.Icc 0 1) : (interpolate p R t).PosDef := by
  let e := Equiv.sumCompl (fun i => p i = true)
  have h : ((interpolate p R 1).submatrix e e).PosDef := by
    rw [interpolate_one]
    exact hR.submatrix e.injective
  rw [interpolate_blocks p hR.1 1] at h
  have ht' := blockCov_posDef h ht
  rw [← interpolate_blocks p hR.1 t] at ht'
  have hp := ht'.submatrix e.symm.injective
  have he : ((interpolate p R t).submatrix e e).submatrix e.symm e.symm =
      interpolate p R t := by ext i j; simp [submatrix]
  exact he ▸ hp

omit [Fintype κ] [DecidableEq κ] in
lemma interpolate_det_antitone (p : ι → Bool) {R : Matrix ι ι ℝ} (hR : R.PosDef) :
    AntitoneOn (fun t => (interpolate p R t).det) (Set.Icc 0 1) := by
  let e := Equiv.sumCompl (fun i => p i = true)
  have he (t : ℝ) : (interpolate p R t).det = ((interpolate p R t).submatrix e e).det :=
    (det_submatrix_equiv_self e _).symm
  have h : ((interpolate p R 1).submatrix e e).PosDef := by
    rw [interpolate_one]
    exact hR.submatrix e.injective
  rw [interpolate_blocks p hR.1 1] at h
  simp only [he]
  dsimp only [e]
  simpa only [interpolate_blocks p hR.1] using blockCov_det_antitone h

omit [Fintype κ] [DecidableEq κ] in
lemma interpolate_det_differentiable (p : ι → Bool) (R : Matrix ι ι ℝ) :
    Differentiable ℝ (fun t => (interpolate p R t).det) := by
  have he (i j : ι) : Differentiable ℝ (fun t => interpolate p R t i j) := by
    dsimp [interpolate]
    split_ifs <;> fun_prop
  simp only [Matrix.det_apply']
  apply Differentiable.fun_sum
  intro σ _
  apply Differentiable.const_mul
  exact Differentiable.fun_finsetProd (fun i _ => he _ _)

omit [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ] in
lemma interpolate_submatrix {η : Type*} (p : ι → Bool) (R : Matrix ι ι ℝ)
    (f : η → ι) (t : ℝ) :
    (interpolate p R t).submatrix f f = interpolate (p ∘ f) (R.submatrix f f) t := rfl

omit [Fintype ι] [Fintype κ] [DecidableEq κ] in
lemma principal_minor_deriv_nonpos (p : ι → Bool) {R : Matrix ι ι ℝ} (hR : R.PosDef)
    (S : Finset ι) {t : ℝ} (ht : t ∈ Set.Ioo 0 1) :
    deriv (fun u => ((interpolate p R u).submatrix (Subtype.val : S → ι) Subtype.val).det) t ≤ 0 := by
  simp only [interpolate_submatrix]
  have hm := interpolate_det_antitone (p ∘ (Subtype.val : S → ι))
    (hR.submatrix Subtype.val_injective)
  have hd := hm.derivWithin_nonpos (x := t)
  rwa [derivWithin_of_mem_nhds (Icc_mem_nhds ht.1 ht.2)] at hd

omit [Fintype κ] [DecidableEq κ] in
lemma det_diagonal_mul_add_one (R : Matrix ι ι ℝ) (z : ι → ℝ) :
    (diagonal z * R + 1).det = ∑ S : Finset ι,
      (∏ i ∈ S, z i) * (R.submatrix (Subtype.val : S → ι) Subtype.val).det := by
  change detRowAlternating ((fun i j => (diagonal z * R) i j) +
    (fun i j => (1 : Matrix ι ι ℝ) i j)) = _
  rw [detRowAlternating.map_add_univ]
  apply Finset.sum_congr rfl
  intro S _
  have he : S.piecewise (diagonal z * R) (1 : Matrix ι ι ℝ) =
      fun i => (if i ∈ S then z i else 1) • S.piecewise R (1 : Matrix ι ι ℝ) i := by
    ext i j
    simp only [Finset.piecewise, Pi.smul_apply, smul_eq_mul]
    split_ifs <;> simp_all
  rw [he, detRowAlternating.map_smul_univ]
  simp only [Finset.prod_ite_mem, Finset.univ_inter]
  change _ * (Matrix.of (S.piecewise R.row (1 : Matrix ι ι ℝ).row)).det = _
  rw [det_piecewise_one_eq_submatrix_det]

omit [Fintype κ] [DecidableEq κ] in
lemma det_interpolate_derivative (p : ι → Bool) (R : Matrix ι ι ℝ) (z : ι → ℝ) (t : ℝ) :
    HasDerivAt (fun u => (diagonal z * interpolate p R u + 1).det)
      (∑ S : Finset ι, (∏ i ∈ S, z i) *
        deriv (fun u => ((interpolate p R u).submatrix
          (Subtype.val : S → ι) Subtype.val).det) t) t := by
  simp only [det_diagonal_mul_add_one]
  apply HasDerivAt.fun_sum
  intro S _
  apply HasDerivAt.const_mul
  have hd := (interpolate_det_differentiable (p ∘ (Subtype.val : S → ι))
    (R.submatrix Subtype.val Subtype.val) t).hasDerivAt
  simpa only [interpolate_submatrix] using hd

end EuclideanSteinitz.GaussianCorrelation

namespace EuclideanSteinitz.GaussianCorrelation
open Matrix MeasureTheory ProbabilityTheory
open scoped NNReal MatrixOrder Matrix.Norms.L2Operator

lemma integral_exp_square_gaussian {t : ℝ} (ht : 0 ≤ t) :
    (∫ x : ℝ, Real.exp (-t * x ^ 2 / 2) ∂gaussianReal 0 1) =
      (Real.sqrt (1 + t))⁻¹ := by
  rw [integral_gaussianReal_eq_integral_smul (by norm_num : (1 : ℝ≥0) ≠ 0)]
  have he (x : ℝ) : gaussianPDFReal 0 1 x * Real.exp (-t * x ^ 2 / 2) =
      (Real.sqrt (2 * Real.pi))⁻¹ * Real.exp (-((1 + t) / 2) * x ^ 2) := by
    simp only [gaussianPDFReal, NNReal.coe_one, mul_one, sub_zero]
    rw [mul_assoc, ← Real.exp_add]
    congr 2
    ring
  simp only [smul_eq_mul, he, integral_const_mul, integral_gaussian]
  rw [show Real.pi / ((1 + t) / 2) = (2 * Real.pi) / (1 + t) by rw [div_div_eq_mul_div]; ring]
  rw [Real.sqrt_div (by positivity : 0 ≤ 2 * Real.pi)]
  have hp : Real.sqrt (2 * Real.pi) ≠ 0 := by positivity
  field_simp

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
open scoped RealInnerProductSpace

lemma eigenvector_toEuclideanCLM {A : Matrix ι ι ℝ} (hA : A.IsHermitian) (i : ι) :
    toEuclideanCLM (𝕜 := ℝ) A (hA.eigenvectorBasis i) =
      hA.eigenvalues i • hA.eigenvectorBasis i := by
  apply WithLp.ofLp_injective
  exact hA.mulVec_eigenvectorBasis i

lemma quadratic_eigenbasis {A : Matrix ι ι ℝ} (hA : A.IsHermitian) (x : ι → ℝ) :
    ⟪∑ i, x i • hA.eigenvectorBasis i,
      toEuclideanCLM (𝕜 := ℝ) A (∑ i, x i • hA.eigenvectorBasis i)⟫ =
      ∑ i, hA.eigenvalues i * x i ^ 2 := by
  simp only [map_sum, map_smul, eigenvector_toEuclideanCLM, smul_smul,
    sum_inner, inner_sum, real_inner_smul_left, real_inner_smul_right,
    hA.eigenvectorBasis.inner_eq_ite]
  simp [mul_ite, ite_mul, pow_two, mul_comm, mul_left_comm, mul_assoc]

lemma det_one_add_eigenvalues {A : Matrix ι ι ℝ} (hA : A.IsHermitian) :
    (1 + A).det = ∏ i, (1 + hA.eigenvalues i) := by
  have he : 1 + A = (Unitary.conjStarAlgAut ℝ _ hA.eigenvectorUnitary)
      (diagonal (fun i => 1 + hA.eigenvalues i)) := by
    rw [show diagonal (fun i => 1 + hA.eigenvalues i) =
      1 + diagonal (RCLike.ofReal ∘ hA.eigenvalues) by
      simp only [Function.comp_def, RCLike.ofReal_real_eq_id, id_eq,
        ← diagonal_one, ← diagonal_add]]
    rw [map_add, map_one, ← hA.spectral_theorem]
  rw [he]
  simp only [Matrix.det_map', det_diagonal]

lemma quadratic_laplace_stdGaussian {A : Matrix ι ι ℝ} (hA : A.PosSemidef) :
    (∫ x : EuclideanSpace ℝ ι, Real.exp (-⟪x, toEuclideanCLM (𝕜 := ℝ) A x⟫ / 2)
      ∂stdGaussian (EuclideanSpace ℝ ι)) = (Real.sqrt (1 + A).det)⁻¹ := by
  have he (x : ι → ℝ) :
      Real.exp (-⟪∑ i, x i • hA.1.eigenvectorBasis i,
        toEuclideanCLM (𝕜 := ℝ) A (∑ i, x i • hA.1.eigenvectorBasis i)⟫ / 2) =
      ∏ i, Real.exp (-hA.1.eigenvalues i * x i ^ 2 / 2) := by
    rw [quadratic_eigenbasis, ← Real.exp_sum]
    congr 1
    simp only [Finset.sum_div, neg_mul, Finset.sum_neg_distrib, neg_div]
  rw [stdGaussian_eq_map_pi_orthonormalBasis hA.1.eigenvectorBasis,
    integral_map (Measurable.aemeasurable (by fun_prop)) (by fun_prop)]
  simp only [he]
  rw [integral_fintype_prod_eq_prod
    (f := fun i (x : ℝ) => Real.exp (-hA.1.eigenvalues i * x ^ 2 / 2))]
  simp_rw [integral_exp_square_gaussian (hA.eigenvalues_nonneg _)]
  rw [det_one_add_eigenvalues hA.1, Real.sqrt_prod]
  · simp
  · intro i _
    linarith [hA.eigenvalues_nonneg i]

end EuclideanSteinitz.GaussianCorrelation

namespace EuclideanSteinitz.GaussianCorrelation
open Matrix MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace MatrixOrder Matrix.Norms.L2Operator
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma quadratic_diagonal (z : ι → ℝ) (x : EuclideanSpace ℝ ι) :
    ⟪x, toEuclideanCLM (𝕜 := ℝ) (diagonal z) x⟫ = ∑ i, z i * x i ^ 2 := by
  rw [inner_toEuclideanCLM]
  simp only [dotProduct, mulVec_diagonal, pow_two]
  congr 1
  ext i
  ring

lemma quadratic_sandwich (S D : Matrix ι ι ℝ) (hS : S.IsHermitian)
    (x : EuclideanSpace ℝ ι) :
    ⟪toEuclideanCLM (𝕜 := ℝ) S x,
      toEuclideanCLM (𝕜 := ℝ) D (toEuclideanCLM (𝕜 := ℝ) S x)⟫ =
      ⟪x, toEuclideanCLM (𝕜 := ℝ) (S * D * S) x⟫ := by
  have hs : IsSelfAdjoint (toEuclideanCLM (𝕜 := ℝ) S) := hS.isSelfAdjoint.map _
  rw [← ContinuousLinearMap.adjoint_inner_right, hs.adjoint_eq]
  simp only [map_mul, mul_apply_eq_comp]

lemma sqrt_sandwich_psd {R : Matrix ι ι ℝ} (z : ι → ℝ) (hz : ∀ i, 0 ≤ z i) :
    (CFC.sqrt R * diagonal z * CFC.sqrt R).PosSemidef := by
  have hD : (diagonal z).PosSemidef := posSemidef_diagonal_iff.mpr hz
  have hS : (CFC.sqrt R).IsHermitian := (CFC.sqrt_nonneg R).isSelfAdjoint
  simpa only [hS.eq] using hD.conjTranspose_mul_mul_same (CFC.sqrt R)

lemma det_one_add_sqrt_sandwich {R : Matrix ι ι ℝ} (hR : R.PosSemidef) (z : ι → ℝ) :
    (1 + CFC.sqrt R * diagonal z * CFC.sqrt R).det = (diagonal z * R + 1).det := by
  rw [Matrix.mul_assoc, det_one_add_mul_comm (CFC.sqrt R) (diagonal z * CFC.sqrt R),
    Matrix.mul_assoc, CFC.sqrt_mul_sqrt_self R hR.nonneg, add_comm]

lemma det_diagonal_mul_add_one_pos {R : Matrix ι ι ℝ} (hR : R.PosSemidef)
    {z : ι → ℝ} (hz : ∀ i, 0 ≤ z i) : 0 < (diagonal z * R + 1).det := by
  rw [← det_one_add_sqrt_sandwich hR z]
  exact ((show (1 : Matrix ι ι ℝ).PosDef from Matrix.PosDef.one).add_posSemidef (sqrt_sandwich_psd z hz)).det_pos

lemma quadratic_laplace_multivariateGaussian {R : Matrix ι ι ℝ} (hR : R.PosSemidef)
    {z : ι → ℝ} (hz : ∀ i, 0 ≤ z i) :
    (∫ x : EuclideanSpace ℝ ι, Real.exp (-(∑ i, z i * x i ^ 2) / 2)
      ∂multivariateGaussian 0 R) = (Real.sqrt (diagonal z * R + 1).det)⁻¹ := by
  rw [multivariateGaussian,
    integral_map (Measurable.aemeasurable (by fun_prop)) (by fun_prop)]
  simp only [zero_add, ← quadratic_diagonal,
    quadratic_sandwich _ _ (CFC.sqrt_nonneg R).isSelfAdjoint]
  rw [quadratic_laplace_stdGaussian (sqrt_sandwich_psd z hz),
    det_one_add_sqrt_sandwich hR z]

end EuclideanSteinitz.GaussianCorrelation

namespace EuclideanSteinitz.GaussianCorrelation
open Matrix MeasureTheory ProbabilityTheory
open scoped NNReal RealInnerProductSpace MatrixOrder Matrix.Norms.L2Operator
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in
lemma laplaceKernel_nonneg (z x : ι → ℝ) : 0 ≤ laplaceKernel z x :=
  (Real.exp_pos _).le

omit [DecidableEq ι] in
lemma laplaceKernel_le_one {z x : ι → ℝ} (hz : ∀ i, 0 ≤ z i) (hx : ∀ i, 0 ≤ x i) :
    laplaceKernel z x ≤ 1 := by
  apply Real.exp_le_one_iff.mpr
  exact neg_nonpos.mpr (Finset.sum_nonneg (fun i _ => mul_nonneg (hz i) (hx i)))

omit [DecidableEq ι] in
lemma laplaceKernel_add (z x y : ι → ℝ) :
    laplaceKernel z (x + y) = laplaceKernel z x * laplaceKernel z y := by
  simp only [laplaceKernel, Pi.add_apply, mul_add, Finset.sum_add_distrib,
    neg_add, Real.exp_add]

omit [DecidableEq ι] in
lemma continuous_laplaceKernel (z : ι → ℝ) : Continuous (laplaceKernel z) := by
  unfold laplaceKernel
  fun_prop

omit [DecidableEq ι] in
lemma measurableSet_nonnegative : MeasurableSet {x : ι → ℝ | ∀ i, 0 ≤ x i} := by
  simp only [Set.ofPred_forall]
  exact MeasurableSet.iInter (fun i => measurableSet_le measurable_const (measurable_pi_apply i))

lemma squareLaw_nonneg (R : Matrix ι ι ℝ) :
    ∀ᵐ x ∂squareLaw R, ∀ i, 0 ≤ x i := by
  rw [squareLaw, ae_map_iff (by fun_prop) measurableSet_nonnegative]
  filter_upwards [] with x i
  positivity

omit [DecidableEq ι] in
lemma integrable_laplaceKernel {μ : Measure (ι → ℝ)} [IsFiniteMeasure μ]
    (hμ : ∀ᵐ x ∂μ, ∀ i, 0 ≤ x i) {z : ι → ℝ} (hz : ∀ i, 0 ≤ z i) :
    Integrable (laplaceKernel z) μ := by
  apply Integrable.mono' (integrable_const (1 : ℝ)) (continuous_laplaceKernel _).aestronglyMeasurable
  filter_upwards [hμ] with x hx
  rw [Real.norm_eq_abs, abs_of_nonneg (laplaceKernel_nonneg _ _)]
  exact laplaceKernel_le_one hz hx

lemma laplace_squareLaw {R : Matrix ι ι ℝ} (hR : R.PosSemidef)
    {z : ι → ℝ} (hz : ∀ i, 0 ≤ z i) :
    (∫ x, laplaceKernel z x ∂squareLaw R) =
      (Real.sqrt (diagonal z * R + 1).det)⁻¹ := by
  rw [squareLaw, integral_map (Measurable.aemeasurable (by fun_prop))
    (continuous_laplaceKernel _).aestronglyMeasurable]
  simp only [laplaceKernel, ← mul_div_assoc, ← Finset.sum_div]
  simpa only [neg_div] using quadratic_laplace_multivariateGaussian hR hz

omit [DecidableEq ι] in
lemma sumLaw_nonneg {μ ν : Measure (ι → ℝ)} [SFinite μ] [SFinite ν]
    (hμ : ∀ᵐ x ∂μ, ∀ i, 0 ≤ x i) (hν : ∀ᵐ x ∂ν, ∀ i, 0 ≤ x i) :
    ∀ᵐ x ∂sumLaw μ ν, ∀ i, 0 ≤ x i := by
  rw [sumLaw, ae_map_iff (by fun_prop) measurableSet_nonnegative]
  apply (Measure.ae_prod_iff_ae_ae (measurableSet_nonnegative.preimage (by fun_prop))).mpr
  filter_upwards [hμ] with x hx
  filter_upwards [hν] with y hy
  exact fun i => add_nonneg (hx i) (hy i)

omit [DecidableEq ι] in
lemma laplace_sumLaw {μ ν : Measure (ι → ℝ)} [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (z : ι → ℝ) :
    (∫ x, laplaceKernel z x ∂sumLaw μ ν) =
      (∫ x, laplaceKernel z x ∂μ) * (∫ x, laplaceKernel z x ∂ν) := by
  rw [sumLaw, integral_map (Measurable.aemeasurable (by fun_prop))
    (continuous_laplaceKernel _).aestronglyMeasurable]
  simp only [laplaceKernel_add]
  exact integral_prod_mul _ _

lemma tripleSquareLaw_nonneg (R : Matrix ι ι ℝ) :
    ∀ᵐ x ∂tripleSquareLaw R, ∀ i, 0 ≤ x i :=
  sumLaw_nonneg (squareLaw_nonneg R)
    (sumLaw_nonneg (squareLaw_nonneg R) (squareLaw_nonneg R))

lemma laplace_tripleSquareLaw {R : Matrix ι ι ℝ} (hR : R.PosSemidef)
    {z : ι → ℝ} (hz : ∀ i, 0 ≤ z i) :
    (∫ x, laplaceKernel z x ∂tripleSquareLaw R) =
      ((Real.sqrt (diagonal z * R + 1).det)⁻¹) ^ 3 := by
  rw [tripleSquareLaw, laplace_sumLaw, laplace_sumLaw,
    laplace_squareLaw hR hz]
  ring

end EuclideanSteinitz.GaussianCorrelation

namespace EuclideanSteinitz.GaussianCorrelation
open Matrix MeasureTheory ProbabilityTheory Polynomial
open scoped NNReal RealInnerProductSpace MatrixOrder Matrix.Norms.L2Operator
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma polynomial_euler_eval (p : ℝ[X]) (y : ℝ) :
    y * p.derivative.eval y =
      ∑ k : Fin (p.natDegree + 1), p.coeff k * (k : ℝ) * y ^ (k : ℕ) := by
  have he := congrArg (fun q : ℝ[X] => y * q.derivative.eval y) p.as_sum_range
  rw [he]
  simp only [Polynomial.derivative_sum, Polynomial.eval_finsetSum, Finset.mul_sum]
  have hm (k : ℕ) : y * ((monomial k) (p.coeff k)).derivative.eval y =
      p.coeff k * (k : ℝ) * y ^ k := by
    cases k with
    | zero => simp
    | succ k => simp [pow_succ]; ring
  simp only [hm, Finset.sum_range]

lemma polynomial_eval_exp (p : ℝ[X]) (x : ℝ) :
    p.eval (Real.exp (-x)) = ∑ k : Fin (p.natDegree + 1),
      p.coeff k * Real.exp (-(k : ℝ) * x) := by
  rw [Polynomial.eval_eq_sum_range]
  simp only [← Real.exp_nat_mul, Finset.sum_range, mul_neg, neg_mul]

lemma polynomial_euler_exp (p : ℝ[X]) (x : ℝ) :
    Real.exp (-x) * p.derivative.eval (Real.exp (-x)) =
      ∑ k : Fin (p.natDegree + 1), p.coeff k * (k : ℝ) * Real.exp (-(k : ℝ) * x) := by
  rw [polynomial_euler_eval]
  simp only [← Real.exp_nat_mul, mul_neg, neg_mul]

lemma mixedPolynomial_expansion (p : ι → ℝ[X]) (S : Finset ι) (x : ι → ℝ) :
    mixedPolynomial p S x = ∑ k : PolynomialIndex p,
      polynomialWeight p k * mixedMultiplier k S * laplaceKernel (exponentVector k) x := by
  have hf (i : ι) :
      (if i ∈ S then Real.exp (-x i) * (p i).derivative.eval (Real.exp (-x i))
        else (p i).eval (Real.exp (-x i))) =
      ∑ k : Fin ((p i).natDegree + 1), (p i).coeff k *
        (if i ∈ S then (k : ℝ) else 1) * Real.exp (-(k : ℝ) * x i) := by
    split_ifs with hi
    · exact polynomial_euler_exp _ _
    · simpa only [mul_one] using polynomial_eval_exp (p i) (x i)
  rw [mixedPolynomial]
  simp_rw [hf]
  rw [Fintype.prod_sum]
  apply Finset.sum_congr rfl
  intro k _
  simp only [Finset.prod_mul_distrib, Finset.prod_ite_mem, Finset.univ_inter,
    polynomialWeight, mixedMultiplier, laplaceKernel, exponentVector,
    ← Real.exp_sum, Finset.sum_neg_distrib, neg_mul]

lemma mixedPolynomial_nonneg (p : ι → ℝ[X]) (S : Finset ι)
    (hp : ∀ i y, y ∈ Set.Icc (0 : ℝ) 1 → 0 ≤ (p i).eval y)
    (hdp : ∀ i y, y ∈ Set.Icc (0 : ℝ) 1 → 0 ≤ (p i).derivative.eval y)
    {x : ι → ℝ} (hx : ∀ i, 0 ≤ x i) : 0 ≤ mixedPolynomial p S x := by
  apply Finset.prod_nonneg
  intro i _
  have hy : Real.exp (-x i) ∈ Set.Icc (0 : ℝ) 1 :=
    ⟨(Real.exp_pos _).le, Real.exp_le_one_iff.mpr (neg_nonpos.mpr (hx i))⟩
  split_ifs
  · exact mul_nonneg (Real.exp_pos _).le (hdp i _ hy)
  · exact hp i _ hy

lemma integrable_mixedPolynomial {μ : Measure (ι → ℝ)} [IsFiniteMeasure μ]
    (hμ : ∀ᵐ x ∂μ, ∀ i, 0 ≤ x i) (p : ι → ℝ[X]) (S : Finset ι) :
    Integrable (mixedPolynomial p S) μ := by
  simp_rw [show mixedPolynomial p S = fun x => ∑ k : PolynomialIndex p,
      polynomialWeight p k * mixedMultiplier k S * laplaceKernel (exponentVector k) x
    from funext (mixedPolynomial_expansion p S)]
  apply integrable_finsetSum
  intro k _
  exact (integrable_laplaceKernel hμ (fun i => by simp [exponentVector])).const_mul _

lemma integral_mixedPolynomial {μ : Measure (ι → ℝ)} [IsFiniteMeasure μ]
    (hμ : ∀ᵐ x ∂μ, ∀ i, 0 ≤ x i) (p : ι → ℝ[X]) (S : Finset ι) :
    (∫ x, mixedPolynomial p S x ∂μ) = ∑ k : PolynomialIndex p,
      polynomialWeight p k * mixedMultiplier k S *
        ∫ x, laplaceKernel (exponentVector k) x ∂μ := by
  simp_rw [mixedPolynomial_expansion]
  rw [integral_finsetSum]
  · simp only [integral_const_mul]
  · intro k _
    exact (integrable_laplaceKernel hμ (fun i => by simp [exponentVector])).const_mul _

end EuclideanSteinitz.GaussianCorrelation

namespace EuclideanSteinitz.GaussianCorrelation
open Matrix MeasureTheory ProbabilityTheory Polynomial
open scoped NNReal RealInnerProductSpace MatrixOrder Matrix.Norms.L2Operator
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [Fintype ι] in
lemma royenCoefficient_nonneg (p : ι → Bool) {R : Matrix ι ι ℝ} (hR : R.PosDef)
    (S : Finset ι) {t : ℝ} (ht : t ∈ Set.Ioo 0 1) : 0 ≤ royenCoefficient p R S t :=
  div_nonneg (neg_nonneg.mpr (principal_minor_deriv_nonpos p hR S ht)) (by norm_num)

lemma laplace_interpolate_derivative (p : ι → Bool) {R : Matrix ι ι ℝ}
    (hR : R.PosDef) {z : ι → ℝ} (hz : ∀ i, 0 ≤ z i) {t : ℝ}
    (ht : t ∈ Set.Icc 0 1) :
    HasDerivAt (fun u => (Real.sqrt (diagonal z * interpolate p R u + 1).det)⁻¹)
      (∑ S : Finset ι, royenCoefficient p R S t * (∏ i ∈ S, z i) *
        ((Real.sqrt (diagonal z * interpolate p R t + 1).det)⁻¹)^3) t := by
  have hpos := det_diagonal_mul_add_one_pos (interpolate_posDef p hR ht).posSemidef hz
  have hspos := Real.sqrt_pos.mpr hpos
  have hd := ((det_interpolate_derivative p R z t).sqrt hpos.ne').inv hspos.ne'
  apply hd.congr_deriv
  symm
  rw [← Finset.sum_mul]
  have he : (∑ S : Finset ι, royenCoefficient p R S t * ∏ i ∈ S, z i) =
      -(∑ S : Finset ι, (∏ i ∈ S, z i) * deriv (fun u =>
        ((interpolate p R u).submatrix (Subtype.val : S → ι) Subtype.val).det) t) / 2 := by
    simp only [royenCoefficient]
    rw [← Finset.sum_neg_distrib, Finset.sum_div]
    apply Finset.sum_congr rfl
    intro S _
    ring
  rw [he]
  field_simp

lemma polynomialExpectation_eq_integral (p : ι → ℝ[X]) {R : Matrix ι ι ℝ}
    (hR : R.PosSemidef) : polynomialExpectation p R =
      ∫ x, mixedPolynomial p ∅ x ∂squareLaw R := by
  rw [integral_mixedPolynomial (squareLaw_nonneg R)]
  unfold polynomialExpectation
  apply Finset.sum_congr rfl
  intro k _
  simp only [mixedMultiplier, Finset.prod_empty, mul_one]
  rw [laplace_squareLaw hR (z := exponentVector k) (fun i => Nat.cast_nonneg (k i).val)]

lemma polynomialExpectation_derivative (b : ι → Bool) {R : Matrix ι ι ℝ}
    (hR : R.PosDef) (p : ι → ℝ[X]) {t : ℝ} (ht : t ∈ Set.Icc 0 1) :
    HasDerivAt (fun u => polynomialExpectation p (interpolate b R u))
      (∑ S : Finset ι, royenCoefficient b R S t *
        ∫ x, mixedPolynomial p S x ∂tripleSquareLaw (interpolate b R t)) t := by
  have hd := HasDerivAt.fun_sum (u := Finset.univ) (fun (k : PolynomialIndex p) _ =>
    (laplace_interpolate_derivative b hR (z := exponentVector k)
      (fun i => by simp [exponentVector]) ht).const_mul (polynomialWeight p k))
  apply hd.congr_deriv
  have he (S : Finset ι) :
      (∫ x, mixedPolynomial p S x ∂tripleSquareLaw (interpolate b R t)) =
        ∑ k : PolynomialIndex p, polynomialWeight p k * mixedMultiplier k S *
          ((Real.sqrt (diagonal (exponentVector k) * interpolate b R t + 1).det)⁻¹)^3 := by
    rw [integral_mixedPolynomial (tripleSquareLaw_nonneg _)]
    apply Finset.sum_congr rfl
    intro k _
    rw [laplace_tripleSquareLaw (interpolate_posDef b hR ht).posSemidef
      (z := exponentVector k) (fun i => Nat.cast_nonneg (k i).val)]
  simp_rw [he, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro S _
  apply Finset.sum_congr rfl
  intro k _
  simp only [mixedMultiplier, exponentVector]
  ring

lemma polynomialExpectation_monotone (b : ι → Bool) {R : Matrix ι ι ℝ}
    (hR : R.PosDef) (p : ι → ℝ[X])
    (hp : ∀ i y, y ∈ Set.Icc (0 : ℝ) 1 → 0 ≤ (p i).eval y)
    (hdp : ∀ i y, y ∈ Set.Icc (0 : ℝ) 1 → 0 ≤ (p i).derivative.eval y) :
    MonotoneOn (fun t => polynomialExpectation p (interpolate b R t)) (Set.Icc 0 1) := by
  have hd := fun t ht => polynomialExpectation_derivative b hR p (t := t) ht
  apply monotoneOn_of_deriv_nonneg (convex_Icc _ _)
  · intro t ht
    exact (hd t ht).continuousAt.continuousWithinAt
  · intro t ht
    exact (hd t (interior_subset ht)).differentiableAt.differentiableWithinAt
  · intro t ht
    have ht' : t ∈ Set.Ioo 0 1 := by simpa only [interior_Icc] using ht
    rw [(hd t ⟨ht'.1.le, ht'.2.le⟩).deriv]
    apply Finset.sum_nonneg
    intro S _
    apply mul_nonneg (royenCoefficient_nonneg b hR S ht')
    apply integral_nonneg_of_ae
    filter_upwards [tripleSquareLaw_nonneg (interpolate b R t)] with x hx
    exact mixedPolynomial_nonneg p S hp hdp hx

lemma polynomial_correlation_interpolate (b : ι → Bool) {R : Matrix ι ι ℝ}
    (hR : R.PosDef) (p : ι → ℝ[X])
    (hp : ∀ i y, y ∈ Set.Icc (0 : ℝ) 1 → 0 ≤ (p i).eval y)
    (hdp : ∀ i y, y ∈ Set.Icc (0 : ℝ) 1 → 0 ≤ (p i).derivative.eval y) :
    (∫ x, mixedPolynomial p ∅ x ∂squareLaw (interpolate b R 0)) ≤
      ∫ x, mixedPolynomial p ∅ x ∂squareLaw R := by
  have hm := polynomialExpectation_monotone b hR p hp hdp
  have he := hm (a := 0) (b := 1) (by norm_num) (by norm_num) (by norm_num)
  dsimp only at he
  rw [interpolate_one, polynomialExpectation_eq_integral p hR.posSemidef,
    polynomialExpectation_eq_integral p
      (interpolate_posDef b hR (by norm_num : (0 : ℝ) ∈ Set.Icc 0 1)).posSemidef] at he
  exact he

end EuclideanSteinitz.GaussianCorrelation

namespace EuclideanSteinitz.GaussianCorrelation
open Polynomial _root_.Filter
open scoped unitInterval Topology

lemma bernsteinP_derivative (n : ℕ) (a : ℕ → ℝ) :
    (bernsteinP (n + 1) a).derivative =
      C (n + 1 : ℝ) * ∑ k ∈ Finset.range (n + 1),
        C (a (k + 1) - a k) * bernsteinPolynomial ℝ n k := by
  have hend : bernsteinPolynomial ℝ n (n + 1) = 0 := by
    simp [bernsteinPolynomial]
  have ht : (∑ k ∈ Finset.range (n + 1), C (a (k + 1)) * bernsteinPolynomial ℝ n (k + 1)) =
      (∑ k ∈ Finset.range (n + 1), C (a k) * bernsteinPolynomial ℝ n k) -
        C (a 0) * bernsteinPolynomial ℝ n 0 := by
    have he := Finset.sum_range_succ' (fun k => C (a k) * bernsteinPolynomial ℝ n k) (n+1)
    rw [Finset.sum_range_succ, hend, mul_zero, add_zero] at he
    exact eq_sub_iff_add_eq.mpr he.symm
  rw [bernsteinP, Finset.sum_range_succ']
  simp only [Polynomial.derivative_sum,
    Polynomial.derivative_C_mul, bernsteinPolynomial.derivative_succ_aux,
    bernsteinPolynomial.derivative_zero, Nat.add_sub_cancel,
    map_add, map_natCast, map_one, Nat.cast_add, Nat.cast_one]
  simp only [mul_sub, Finset.sum_sub_distrib, map_sub]
  simp only [show ∀ k, C (a (k + 1)) * ((n + 1) * bernsteinPolynomial ℝ n k) =
    (n + 1) * (C (a (k + 1)) * bernsteinPolynomial ℝ n k) from fun k => by ring,
    show ∀ k, C (a (k + 1)) * ((n + 1) * bernsteinPolynomial ℝ n (k + 1)) =
    (n + 1) * (C (a (k + 1)) * bernsteinPolynomial ℝ n (k + 1)) from fun k => by ring,
    ← Finset.mul_sum, ht]
  simp only [sub_mul, Finset.sum_sub_distrib]
  ring

lemma bernsteinP_eval (n : ℕ) (f : C(ℝ, ℝ)) (x : I) :
    (bernsteinP n (fun k => f ((k : ℝ) / n))).eval (x : ℝ) =
      bernsteinApproximation n (f.comp ⟨Subtype.val, continuous_subtype_val⟩) x := by
  simp only [bernsteinP, Polynomial.eval_finsetSum, Polynomial.eval_mul,
    Polynomial.eval_C, bernsteinApproximation.apply, smul_eq_mul, ContinuousMap.comp_apply,
    ContinuousMap.coe_mk, bernstein.z, Finset.sum_range]
  apply Finset.sum_congr rfl
  intro k _
  rw [mul_comm]
  rfl

lemma bernsteinP_eval_nonneg (n : ℕ) (f : C(ℝ, ℝ))
    (hf : ∀ x ∈ Set.Icc (0 : ℝ) 1, 0 ≤ f x) {x : ℝ} (hx : x ∈ Set.Icc (0 : ℝ) 1) :
    0 ≤ (bernsteinP n (fun k => f ((k : ℝ) / n))).eval x := by
  have he := bernsteinP_eval n f ⟨x, hx⟩
  rw [he, bernsteinApproximation.apply]
  apply Finset.sum_nonneg
  intro k _
  exact mul_nonneg bernstein_nonneg (hf _ (bernstein.z k).prop)

lemma bernsteinP_eval_le_one (n : ℕ) (f : C(ℝ, ℝ))
    (hf : ∀ x ∈ Set.Icc (0 : ℝ) 1, f x ≤ 1) {x : ℝ} (hx : x ∈ Set.Icc (0 : ℝ) 1) :
    (bernsteinP n (fun k => f ((k : ℝ) / n))).eval x ≤ 1 := by
  have he := bernsteinP_eval n f ⟨x, hx⟩
  rw [he, bernsteinApproximation.apply, ← bernstein.probability n ⟨x, hx⟩]
  apply Finset.sum_le_sum
  intro k _
  exact mul_le_of_le_one_right bernstein_nonneg (hf _ (bernstein.z k).prop)

lemma bernsteinP_derivative_nonneg (n : ℕ) (f : C(ℝ, ℝ))
    (hf : MonotoneOn f (Set.Icc (0 : ℝ) 1))
    {x : ℝ} (hx : x ∈ Set.Icc (0 : ℝ) 1) :
    0 ≤ (bernsteinP n (fun k => f ((k : ℝ) / n))).derivative.eval x := by
  cases n with
  | zero => simp [bernsteinP, bernsteinPolynomial]
  | succ n =>
    rw [bernsteinP_derivative]
    simp only [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_finsetSum]
    apply mul_nonneg (by positivity)
    apply Finset.sum_nonneg
    intro k hk
    have hk' : k < n + 1 := Finset.mem_range.mp hk
    have hn : (0 : ℝ) < n + 1 := by positivity
    have hk0 : (0 : ℝ) ≤ k / (n + 1) := div_nonneg (Nat.cast_nonneg _) hn.le
    have hk1 : (k : ℝ) / (n + 1) ≤ 1 := (div_le_one hn).mpr (by exact_mod_cast hk'.le)
    have hks0 : (0 : ℝ) ≤ (k + 1) / (n + 1) := by positivity
    have hks1 : (k + 1 : ℝ) / (n + 1) ≤ 1 :=
      (div_le_one hn).mpr (by exact_mod_cast hk')
    have hmono := hf ⟨hk0, hk1⟩ ⟨hks0, hks1⟩ (by gcongr; linarith)
    apply mul_nonneg
    · simpa only [Nat.cast_add, Nat.cast_one] using sub_nonneg.mpr hmono
    · exact @bernstein_nonneg n k ⟨x, hx⟩

lemma bernsteinP_tendsto (f : C(ℝ, ℝ)) {x : ℝ} (hx : x ∈ Set.Icc (0 : ℝ) 1) :
    Tendsto (fun n => (bernsteinP n (fun k => f ((k : ℝ) / n))).eval x)
      atTop (𝓝 (f x)) := by
  simp_rw [bernsteinP_eval _ _ ⟨x, hx⟩]
  exact (continuous_eval_const ⟨x, hx⟩).continuousAt.tendsto.comp
    (bernsteinApproximation_uniform (f.comp ⟨Subtype.val, continuous_subtype_val⟩))

end EuclideanSteinitz.GaussianCorrelation

namespace EuclideanSteinitz.GaussianCorrelation
open Matrix MeasureTheory ProbabilityTheory Polynomial _root_.Filter
open scoped NNReal RealInnerProductSpace MatrixOrder Matrix.Norms.L2Operator Topology
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma interpolate_zero_posSemidef (b : ι → Bool) {R : Matrix ι ι ℝ}
    (hR : R.PosSemidef) : (interpolate b R 0).PosSemidef := by
  let A : Matrix ι ι ℝ := diagonal (fun i => if b i = true then 1 else 0)
  let B : Matrix ι ι ℝ := diagonal (fun i => if b i = true then 0 else 1)
  have he : interpolate b R 0 = A * R * Aᴴ + B * R * Bᴴ := by
    ext i j
    simp only [interpolate, zero_mul, A, B, diagonal_conjTranspose,
      star_trivial, diagonal_mul, mul_diagonal, Matrix.add_apply]
    cases b i <;> cases b j <;> simp
  rw [he]
  exact (hR.mul_mul_conjTranspose_same A).add (hR.mul_mul_conjTranspose_same B)

omit [Fintype ι] [DecidableEq ι] in
lemma interpolate_continuous (b : ι → Bool) (t : ℝ) :
    Continuous (fun R : Matrix ι ι ℝ => interpolate b R t) := by
  apply continuous_pi
  intro i
  apply continuous_pi
  intro j
  dsimp only [interpolate]
  split_ifs <;> fun_prop

lemma polynomialExpectation_continuousAt (p : ι → ℝ[X]) {R : Matrix ι ι ℝ}
    (hR : R.PosSemidef) : ContinuousAt (polynomialExpectation p) R := by
  unfold polynomialExpectation
  apply tendsto_finsetSum
  intro k _
  apply ContinuousAt.const_mul
  apply ContinuousAt.inv₀
  · exact (Continuous.sqrt (by fun_prop)).continuousAt
  · exact (Real.sqrt_pos.mpr (det_diagonal_mul_add_one_pos hR
      (fun i => Nat.cast_nonneg (k i).val))).ne'

lemma polynomial_correlation_psd (b : ι → Bool) {R : Matrix ι ι ℝ}
    (hR : R.PosSemidef) (p : ι → ℝ[X])
    (hp : ∀ i y, y ∈ Set.Icc (0 : ℝ) 1 → 0 ≤ (p i).eval y)
    (hdp : ∀ i y, y ∈ Set.Icc (0 : ℝ) 1 → 0 ≤ (p i).derivative.eval y) :
    (∫ x, mixedPolynomial p ∅ x ∂squareLaw (interpolate b R 0)) ≤
      ∫ x, mixedPolynomial p ∅ x ∂squareLaw R := by
  let Rn (n : ℕ) := R + (1 / ((n : ℝ) + 1)) • (1 : Matrix ι ι ℝ)
  have hn (n : ℕ) : (Rn n).PosDef :=
    Matrix.PosDef.posSemidef_add hR (Matrix.PosDef.one.smul (by positivity))
  have ht : Tendsto Rn atTop (𝓝 R) := by
    simpa only [zero_smul, add_zero] using
      (tendsto_const_nhds (x := R)).add
        ((tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).smul
          (tendsto_const_nhds (x := (1 : Matrix ι ι ℝ))))
  rw [← polynomialExpectation_eq_integral p hR,
    ← polynomialExpectation_eq_integral p (interpolate_zero_posSemidef b hR)]
  exact le_of_tendsto_of_tendsto'
    ((polynomialExpectation_continuousAt p (interpolate_zero_posSemidef b hR)).tendsto.comp
      ((interpolate_continuous b 0).continuousAt.tendsto.comp ht))
    ((polynomialExpectation_continuousAt p hR).tendsto.comp ht)
    (fun n => by
      have he := polynomial_correlation_interpolate b (hn n) p hp hdp
      simpa only [← polynomialExpectation_eq_integral p (hn n).posSemidef,
        ← polynomialExpectation_eq_integral p
          (interpolate_zero_posSemidef b (hn n).posSemidef)] using! he)

lemma bernstein_integral_tendsto {μ : Measure (ι → ℝ)} [IsFiniteMeasure μ]
    (hμ : ∀ᵐ x ∂μ, ∀ i, 0 ≤ x i) (f : ι → C(ℝ, ℝ))
    (hf : ∀ i y, y ∈ Set.Icc (0 : ℝ) 1 → f i y ∈ Set.Icc (0 : ℝ) 1) :
    Tendsto (fun n : ℕ => ∫ x, mixedPolynomial
      (fun i => bernsteinP n (fun k => f i ((k : ℝ) / n))) ∅ x ∂μ)
      atTop (𝓝 (∫ x, continuousProduct f x ∂μ)) := by
  apply tendsto_integral_of_dominated_convergence (fun _ => (1 : ℝ))
  · intro n
    exact (integrable_mixedPolynomial hμ _ ∅).aestronglyMeasurable
  · exact integrable_const _
  · intro n
    filter_upwards [hμ] with x hx
    have hy (i : ι) : Real.exp (-x i) ∈ Set.Icc (0 : ℝ) 1 :=
      ⟨(Real.exp_pos _).le, Real.exp_le_one_iff.mpr (neg_nonpos.mpr (hx i))⟩
    have hnon (i : ι) := bernsteinP_eval_nonneg n (f i) (fun y hy => (hf i y hy).1) (hy i)
    have hone (i : ι) := bernsteinP_eval_le_one n (f i) (fun y hy => (hf i y hy).2) (hy i)
    simp only [mixedPolynomial, Finset.notMem_empty, ↓reduceIte, Real.norm_eq_abs]
    rw [abs_of_nonneg (Finset.prod_nonneg (fun i _ => hnon i))]
    exact Finset.prod_le_one (fun i _ => hnon i) (fun i _ => hone i)
  · filter_upwards [hμ] with x hx
    simp only [mixedPolynomial, Finset.notMem_empty, ↓reduceIte, continuousProduct]
    apply tendsto_finsetProd
    intro i _
    exact bernsteinP_tendsto (f i)
      ⟨(Real.exp_pos _).le, Real.exp_le_one_iff.mpr (neg_nonpos.mpr (hx i))⟩

lemma continuous_correlation_interpolate (b : ι → Bool) {R : Matrix ι ι ℝ}
    (hR : R.PosSemidef) (f : ι → C(ℝ, ℝ))
    (hf : ∀ i y, y ∈ Set.Icc (0 : ℝ) 1 → f i y ∈ Set.Icc (0 : ℝ) 1)
    (hm : ∀ i, MonotoneOn (f i) (Set.Icc (0 : ℝ) 1)) :
    (∫ x, continuousProduct f x ∂squareLaw (interpolate b R 0)) ≤
      ∫ x, continuousProduct f x ∂squareLaw R := by
  apply le_of_tendsto_of_tendsto'
    (bernstein_integral_tendsto (squareLaw_nonneg _) f hf)
    (bernstein_integral_tendsto (squareLaw_nonneg _) f hf)
  intro n
  apply polynomial_correlation_psd b hR
  · intro i y hy
    exact bernsteinP_eval_nonneg n (f i) (fun y hy => (hf i y hy).1) hy
  · intro i y hy
    exact bernsteinP_derivative_nonneg n (f i) (hm i) hy

end EuclideanSteinitz.GaussianCorrelation

namespace EuclideanSteinitz.GaussianCorrelation
open Matrix MeasureTheory ProbabilityTheory _root_.Filter
open scoped NNReal RealInnerProductSpace MatrixOrder Matrix.Norms.L2Operator Topology
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma upperCutoff_bounds (n : ℕ) (a y : ℝ) :
    upperCutoff n a y ∈ Set.Icc (0 : ℝ) 1 := by
  exact ⟨le_min zero_le_one (le_max_left _ _), min_le_left _ _⟩

lemma upperCutoff_monotone (n : ℕ) (a : ℝ) : Monotone (upperCutoff n a) := by
  intro x y hxy
  dsimp only [upperCutoff, ContinuousMap.coe_mk]
  gcongr

lemma upperCutoff_tendsto (a y : ℝ) :
    Tendsto (fun n => upperCutoff n a y) atTop (𝓝 (if a ≤ y then (1 : ℝ) else 0)) := by
  by_cases h : a ≤ y
  · have he (n : ℕ) : upperCutoff n a y = 1 := by
      apply min_eq_left
      exact (by nlinarith [show (0 : ℝ) ≤ n by positivity] : (1:ℝ) ≤
        1 + ((n : ℝ)+1) * (y-a)) |>.trans (le_max_right _ _)
    simp only [he, ite_eq_left h]
    exact tendsto_const_nhds
  · have ha : 0 < a - y := sub_pos.mpr (lt_of_not_ge h)
    obtain ⟨N, hN⟩ := exists_nat_gt (1 / (a - y))
    have he : ∀ᶠ n : ℕ in atTop, upperCutoff n a y = 0 := by
      filter_upwards [eventually_ge_atTop N] with n hn
      have hnn : (N : ℝ) ≤ n := by exact_mod_cast hn
      have hb : 1 ≤ ((n : ℝ) + 1) * (a-y) := by
        have := (div_lt_iff₀ ha).mp hN
        nlinarith
      simp only [upperCutoff, ContinuousMap.coe_mk]
      rw [max_eq_left (by nlinarith), min_eq_right zero_le_one]
    simp only [ite_eq_right h]
    exact tendsto_const_nhds.congr' (Filter.EventuallyEq.symm he)

omit [DecidableEq ι] in
lemma measurableSet_exponentialBox (a : ι → ℝ) : MeasurableSet (exponentialBox a) := by
  unfold exponentialBox
  simp only [Set.ofPred_forall]
  exact MeasurableSet.iInter (fun i => measurableSet_le measurable_const (by fun_prop))

omit [DecidableEq ι] in
lemma cutoffProduct_tendsto (a x : ι → ℝ) :
    Tendsto (fun n => continuousProduct (fun i => upperCutoff n (a i)) x) atTop
      (𝓝 ((exponentialBox a).indicator (fun _ => (1 : ℝ)) x)) := by
  have ht := tendsto_finsetProd Finset.univ
    (fun i _ => upperCutoff_tendsto (a i) (Real.exp (- x i)))
  convert ht using 1
  congr 1
  by_cases h : x ∈ exponentialBox a
  · rw [Set.indicator_of_mem h]
    have hi (i : ι) : a i ≤ Real.exp (-x i) := h i
    simp [hi]
  · rw [Set.indicator_of_notMem h]
    have hi : ∃ i, ¬ a i ≤ Real.exp (-x i) := by simpa [exponentialBox] using h
    obtain ⟨i, hi⟩ := hi
    symm
    exact congrArg nhds (Finset.prod_eq_zero (f := fun j => if a j ≤ Real.exp (-x j) then (1 : ℝ) else 0)
      (Finset.mem_univ i) (ite_eq_right hi))

omit [DecidableEq ι] in
lemma cutoff_integral_tendsto {μ : Measure (ι → ℝ)} [IsFiniteMeasure μ] (a : ι → ℝ) :
    Tendsto (fun n => ∫ x, continuousProduct (fun i => upperCutoff n (a i)) x ∂μ)
      atTop (𝓝 (μ.real (exponentialBox a))) := by
  rw [← integral_indicator_one (measurableSet_exponentialBox a)]
  apply tendsto_integral_of_dominated_convergence (fun _ => (1 : ℝ))
  · intro n
    exact Continuous.aestronglyMeasurable (by unfold continuousProduct; fun_prop)
  · exact integrable_const _
  · intro n
    filter_upwards [] with x
    have hn (i : ι) := (upperCutoff_bounds n (a i) (Real.exp (-x i))).1
    have ho (i : ι) := (upperCutoff_bounds n (a i) (Real.exp (-x i))).2
    rw [continuousProduct, Real.norm_eq_abs, abs_of_nonneg (Finset.prod_nonneg (fun i _ => hn i))]
    exact Finset.prod_le_one (fun i _ => hn i) (fun i _ => ho i)
  · exact Filter.Eventually.of_forall (cutoffProduct_tendsto a)

lemma rectangle_correlation_interpolate (b : ι → Bool) {R : Matrix ι ι ℝ}
    (hR : R.PosSemidef) (a : ι → ℝ) :
    (squareLaw (interpolate b R 0)).real (exponentialBox a) ≤
      (squareLaw R).real (exponentialBox a) := by
  apply le_of_tendsto_of_tendsto' (cutoff_integral_tendsto a) (cutoff_integral_tendsto a)
  intro n
  exact continuous_correlation_interpolate b hR (fun i => upperCutoff n (a i))
    (fun i y _ => upperCutoff_bounds n (a i) y)
    (fun i => (upperCutoff_monotone n (a i)).monotoneOn _)

end EuclideanSteinitz.GaussianCorrelation

namespace EuclideanSteinitz.GaussianCorrelation
open Matrix MeasureTheory ProbabilityTheory _root_.Filter
open scoped NNReal RealInnerProductSpace MatrixOrder Matrix.Norms.L2Operator Topology
variable {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]

lemma map_coordinate_multivariateGaussian (f : κ → ι) {R : Matrix ι ι ℝ}
    (hR : R.PosSemidef) :
    (multivariateGaussian 0 R).map (coordinateCLM f) =
      multivariateGaussian 0 (R.submatrix f f) := by
  apply IsGaussian.ext
  · simp only [id_eq, integral_id_multivariateGaussian]
    rw [ContinuousLinearMap.integral_id_map IsGaussian.integrable_id,
      integral_id_multivariateGaussian, map_zero]
  rw [← ContinuousLinearMap.toBilinForm_inj]
  refine LinearMap.BilinForm.ext_basis (EuclideanSpace.basisFun κ ℝ).toBasis fun i j => ?_
  rw [ContinuousLinearMap.toBilinForm_apply, ContinuousLinearMap.toBilinForm_apply,
    covarianceBilin_apply_eq_cov, covariance_map]
  · have he (i : κ) : (fun u => ⟪(EuclideanSpace.basisFun κ ℝ).toBasis i, u⟫) ∘
        coordinateCLM f = fun u => u (f i) := by
      ext u
      simp [PiLp.inner_apply]
    simp_rw [he, covariance_eval_multivariateGaussian hR,
      covarianceBilin_multivariateGaussian (hR.submatrix _)]
    simp
  any_goals exact Measurable.aestronglyMeasurable (by fun_prop)
  · fun_prop
  · exact IsGaussian.memLp_two_id

omit [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ] in
lemma block_submatrix_eq (b : ι → Bool) (v : Bool) (R : Matrix ι ι ℝ) :
    (interpolate b R 0).submatrix (fun i : {i // b i = v} => i.val)
      (fun i : {i // b i = v} => i.val) =
        R.submatrix (fun i : {i // b i = v} => i.val) (fun i : {i // b i = v} => i.val) := by
  ext i j
  simp [Matrix.submatrix, interpolate, i.prop, j.prop]

omit [Fintype κ] [DecidableEq κ] in
lemma gaussian_blocks_independent (b : ι → Bool) {R : Matrix ι ι ℝ} (hR : R.PosSemidef) :
    IndepFun (coordinatePi (fun i : {i // b i = true} => i.val))
      (coordinatePi (fun i : {i // b i = false} => i.val))
        (multivariateGaussian 0 (interpolate b R 0)) := by
  apply HasGaussianLaw.indepFun_of_covariance_eval
  · exact IsGaussian.hasGaussianLaw_id.map
      ((coordinatePi (fun i : {i // b i = true} => i.val)).prod
        (coordinatePi (fun i : {i // b i = false} => i.val)))
  · intro i j
    change cov[fun x => x i.val, fun x => x j.val;
      multivariateGaussian 0 (interpolate b R 0)] = 0
    rw [covariance_eval_multivariateGaussian (interpolate_zero_posSemidef b hR)]
    simp [interpolate, i.prop, j.prop]

omit [DecidableEq ι] [Fintype κ] [DecidableEq κ] in
lemma measurableSet_quadraticBox (t : ι → ℝ) : MeasurableSet (quadraticBox t) := by
  unfold quadraticBox
  simp only [Set.ofPred_forall]
  exact MeasurableSet.iInter (fun i => measurableSet_le (by fun_prop) measurable_const)

omit [Fintype κ] [DecidableEq κ] in
lemma squareLaw_exponentialBox (R : Matrix ι ι ℝ) (t : ι → ℝ) :
    (squareLaw R).real (exponentialBox (fun i => Real.exp (-t i))) =
      (multivariateGaussian 0 R).real (quadraticBox t) := by
  unfold Measure.real squareLaw
  rw [Measure.map_apply (by fun_prop) (measurableSet_exponentialBox _)]
  congr 2
  ext x
  simp [exponentialBox, quadraticBox, Real.exp_le_exp]

omit [Fintype κ] [DecidableEq κ] in
lemma quadratic_correlation_interpolate (b : ι → Bool) {R : Matrix ι ι ℝ}
    (hR : R.PosSemidef) (t : ι → ℝ) :
    (multivariateGaussian 0 (interpolate b R 0)).real (quadraticBox t) ≤
      (multivariateGaussian 0 R).real (quadraticBox t) := by
  simpa only [squareLaw_exponentialBox] using
    rectangle_correlation_interpolate b hR (fun i => Real.exp (-t i))

omit [Fintype κ] [DecidableEq κ] in
lemma block_marginal_eq (b : ι → Bool) (v : Bool) {R : Matrix ι ι ℝ}
    (hR : R.PosSemidef) (S : Set (EuclideanSpace ℝ {i // b i = v})) (hS : MeasurableSet S) :
    (multivariateGaussian 0 (interpolate b R 0)) ((coordinateCLM Subtype.val) ⁻¹' S) =
      (multivariateGaussian 0 R) ((coordinateCLM Subtype.val) ⁻¹' S) := by
  rw [← Measure.map_apply (coordinateCLM Subtype.val).measurable hS,
    ← Measure.map_apply (coordinateCLM Subtype.val).measurable hS,
    map_coordinate_multivariateGaussian _ (interpolate_zero_posSemidef b hR),
    map_coordinate_multivariateGaussian _ hR, block_submatrix_eq]

omit [Fintype κ] [DecidableEq κ] in
lemma gaussian_quadraticBox_correlation (b : ι → Bool) {R : Matrix ι ι ℝ}
    (hR : R.PosSemidef) (t : ι → ℝ) :
    (multivariateGaussian 0 R).real {x | ∀ i, b i = true → x i ^ 2 / 2 ≤ t i} *
      (multivariateGaussian 0 R).real {x | ∀ i, b i = false → x i ^ 2 / 2 ≤ t i} ≤
        (multivariateGaussian 0 R).real (quadraticBox t) := by
  let S : Set ({i // b i = true} → ℝ) := {x | ∀ i, x i ^ 2 / 2 ≤ t i.val}
  let T : Set ({i // b i = false} → ℝ) := {x | ∀ i, x i ^ 2 / 2 ≤ t i.val}
  have hS : MeasurableSet S := by
    dsimp only [S]
    simp only [Set.ofPred_forall]
    exact MeasurableSet.iInter (fun i => measurableSet_le (by fun_prop) measurable_const)
  have hT : MeasurableSet T := by
    dsimp only [T]
    simp only [Set.ofPred_forall]
    exact MeasurableSet.iInter (fun i => measurableSet_le (by fun_prop) measurable_const)
  have he := (gaussian_blocks_independent b hR).measure_inter_preimage_eq_mul S T hS hT
  have hi : (coordinatePi (fun i : {i // b i = true} => i.val)) ⁻¹' S ∩
      (coordinatePi (fun i : {i // b i = false} => i.val)) ⁻¹' T = quadraticBox t := by
    ext x
    simp only [Set.mem_inter_iff, Set.mem_preimage, S, T, Set.mem_ofPred_eq,
      coordinatePi, ContinuousLinearMap.pi_apply,
      quadraticBox, Subtype.forall]
    constructor
    · rintro ⟨ht, hf⟩ i
      cases hi : b i
      · exact hf i hi
      · exact ht i hi
    · exact fun h => ⟨fun i _ => h i, fun i _ => h i⟩
  have hs (v : Bool) :
      (coordinateCLM (fun i : {i // b i = v} => i.val)) ⁻¹'
        quadraticBox (fun i => t i.val) =
      {x : EuclideanSpace ℝ ι | ∀ i, b i = v → x i ^ 2 / 2 ≤ t i} := by
    ext x
    simp [quadraticBox, Subtype.forall]
  have hm (v : Bool) := block_marginal_eq b v hR _
    (measurableSet_quadraticBox (fun i : {i // b i = v} => t i.val))
  simp_rw [hs] at hm
  have hps : (coordinatePi (fun i : {i // b i = true} => i.val)) ⁻¹' S =
      {x : EuclideanSpace ℝ ι | ∀ i, b i = true → x i ^ 2 / 2 ≤ t i} := by
    ext x
    simp [S, coordinatePi, Subtype.forall]
  have hpt : (coordinatePi (fun i : {i // b i = false} => i.val)) ⁻¹' T =
      {x : EuclideanSpace ℝ ι | ∀ i, b i = false → x i ^ 2 / 2 ≤ t i} := by
    ext x
    simp [T, coordinatePi, Subtype.forall]
  rw [hi, hps, hpt, hm true, hm false] at he
  have her := congrArg ENNReal.toReal he
  rw [ENNReal.toReal_mul] at her
  change (multivariateGaussian 0 R).real _ * (multivariateGaussian 0 R).real _ ≤ _
  unfold Measure.real
  rw [← her]
  exact quadratic_correlation_interpolate b hR t

end EuclideanSteinitz.GaussianCorrelation

namespace EuclideanSteinitz.GaussianCorrelation
open Matrix MeasureTheory ProbabilityTheory _root_.Filter
open scoped NNReal RealInnerProductSpace MatrixOrder Matrix.Norms.L2Operator Topology
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

lemma map_innerCoordinates_stdGaussian (u : ι → E) :
    (stdGaussian E).map (innerCoordinates u) = multivariateGaussian 0 (gram ℝ u) := by
  apply IsGaussian.ext
  · simp only [id_eq, integral_id_multivariateGaussian]
    rw [ContinuousLinearMap.integral_id_map IsGaussian.integrable_id,
      integral_id_stdGaussian, map_zero]
  rw [← ContinuousLinearMap.toBilinForm_inj]
  refine LinearMap.BilinForm.ext_basis (EuclideanSpace.basisFun ι ℝ).toBasis fun i j => ?_
  rw [ContinuousLinearMap.toBilinForm_apply, ContinuousLinearMap.toBilinForm_apply,
    covarianceBilin_apply_eq_cov, covariance_map]
  · have he (i : ι) : (fun y => ⟪(EuclideanSpace.basisFun ι ℝ).toBasis i, y⟫) ∘
        innerCoordinates u = fun x => ⟪u i, x⟫ := by
      ext x
      simp [PiLp.inner_apply]
    simp_rw [he]
    rw [← covarianceBilin_apply_eq_cov IsGaussian.memLp_two_id,
      covarianceBilin_stdGaussian,
      covarianceBilin_multivariateGaussian (posSemidef_gram ℝ u)]
    simp
    rfl
  any_goals exact Measurable.aestronglyMeasurable (by fun_prop)
  · fun_prop
  · exact IsGaussian.memLp_two_id

lemma stdGaussian_finite_slabs_correlation (b : ι → Bool) (u : ι → E) (r : ι → ℝ)
    (hr : ∀ i, 0 ≤ r i) :
    (stdGaussian E).real {x | ∀ i, b i = true → |⟪u i, x⟫| ≤ r i} *
      (stdGaussian E).real {x | ∀ i, b i = false → |⟪u i, x⟫| ≤ r i} ≤
        (stdGaussian E).real {x | ∀ i, |⟪u i, x⟫| ≤ r i} := by
  have he := gaussian_quadraticBox_correlation b (posSemidef_gram ℝ u) (fun i => r i ^ 2 / 2)
  rw [← map_innerCoordinates_stdGaussian u] at he
  have hmeas (v : Bool) : MeasurableSet
      {x : EuclideanSpace ℝ ι | ∀ i, b i = v → x i ^ 2 / 2 ≤ r i ^ 2 / 2} := by
    simp only [Set.ofPred_forall]
    exact MeasurableSet.iInter (fun i => MeasurableSet.iInter (fun _ =>
      measurableSet_le (by fun_prop) measurable_const))
  unfold Measure.real at he ⊢
  rw [Measure.map_apply (innerCoordinates u).measurable (hmeas true),
    Measure.map_apply (innerCoordinates u).measurable (hmeas false),
    Measure.map_apply (innerCoordinates u).measurable (measurableSet_quadraticBox _)] at he
  have hsq (i : ι) (x : E) : ⟪u i, x⟫ ^ 2 / 2 ≤ r i ^ 2 / 2 ↔ |⟪u i, x⟫| ≤ r i := by
    rw [div_le_div_iff_of_pos_right (by norm_num : (0:ℝ)<2)]
    exact (sq_le_sq₀ (abs_nonneg _) (hr i)).symm.trans (by rw [sq_abs]) |>.symm
  simpa only [Set.preimage_ofPred_eq, innerCoordinates_apply, quadraticBox, hsq] using he

end EuclideanSteinitz.GaussianCorrelation

namespace EuclideanSteinitz.GaussianCorrelation
open Matrix MeasureTheory ProbabilityTheory _root_.Filter InnerProductSpace
open scoped NNReal RealInnerProductSpace MatrixOrder Matrix.Norms.L2Operator Topology
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

omit [MeasurableSpace E] [BorelSpace E] in
lemma closed_symmetric_convex_countable_slabs {K : Set E} (hK : IsClosed K)
    (hc : Convex ℝ K) (hs : ∀ x ∈ K, -x ∈ K) (h0 : (0:E) ∈ K) :
    ∃ (u : ℕ → E) (r : ℕ → ℝ), (∀ n, 0 ≤ r n) ∧
      K = ⋂ n, {x | |⟪u n, x⟫| ≤ r n} := by
  let I := {p : StrongDual ℝ E × ℝ // ∀ x ∈ K, |p.1 x| ≤ p.2}
  let : Nonempty I := ⟨⟨(0, 0), by intro x _; simp⟩⟩
  let U (p : I) : Set E := {x | |p.val.1 x| ≤ p.val.2}ᶜ
  have ho (p : I) : IsOpen (U p) := (isClosed_le (p.val.1.continuous.abs) continuous_const).isOpen_compl
  have hcover : Kᶜ ⊆ ⋃ p, U p := by
    intro x hx
    obtain ⟨f, r, hf, hr⟩ := geometric_hahn_banach_closed_point hc hK hx
    have hb : ∀ y ∈ K, |f y| ≤ r := by
      intro y hy
      apply abs_le.mpr
      have hneg := hf (-y) (hs y hy)
      simp only [map_neg] at hneg
      exact ⟨by linarith, (hf y hy).le⟩
    refine Set.mem_iUnion.mpr ⟨⟨(f, r), hb⟩, ?_⟩
    change ¬ |f x| ≤ r
    exact not_le.mpr (lt_of_lt_of_le hr (le_abs_self _))
  obtain ⟨g, hg⟩ := (HereditarilyLindelofSpace.isLindelof Kᶜ).indexed_countable_subcover U ho hcover
  refine ⟨fun n => (toDual ℝ E).symm (g n).val.1, fun n => (g n).val.2, ?_, ?_⟩
  · intro n
    simpa using (g n).prop 0 h0
  · ext x
    simp only [Set.mem_iInter, Set.mem_ofPred_eq, toDual_symm_apply]
    constructor
    · exact fun hx n => (g n).prop x hx
    · intro hx
      by_contra hn
      obtain ⟨n, hn⟩ := Set.mem_iUnion.mp (hg hn)
      exact hn (hx n)

omit [FiniteDimensional ℝ E] in
lemma measurableSet_partialSlabs (u : ℕ → E) (r : ℕ → ℝ) (n : ℕ) :
    MeasurableSet (partialSlabs u r n) := by
  unfold partialSlabs
  simp only [Set.ofPred_forall]
  exact MeasurableSet.iInter (fun i => MeasurableSet.iInter (fun _ =>
    measurableSet_le (by fun_prop) measurable_const))

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
lemma partialSlabs_antitone (u : ℕ → E) (r : ℕ → ℝ) : Antitone (partialSlabs u r) := by
  intro n m hnm x hx i hi
  exact hx i (hi.trans_le hnm)

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
lemma partialSlabs_iInter (u : ℕ → E) (r : ℕ → ℝ) :
    (⋂ n, partialSlabs u r n) = ⋂ n, {x | |⟪u n, x⟫| ≤ r n} := by
  ext x
  simp only [Set.mem_iInter, partialSlabs, Set.mem_ofPred_eq]
  constructor
  · exact fun h i => h (i+1) i (Nat.lt_succ_self i)
  · exact fun h _ i _ => h i

lemma stdGaussian_partialSlabs_correlation (u v : ℕ → E) (r s : ℕ → ℝ)
    (hr : ∀ n, 0 ≤ r n) (hs : ∀ n, 0 ≤ s n) (n : ℕ) :
    (stdGaussian E).real (partialSlabs u r n) * (stdGaussian E).real (partialSlabs v s n) ≤
      (stdGaussian E).real (partialSlabs u r n ∩ partialSlabs v s n) := by
  let b : Fin n ⊕ Fin n → Bool := Sum.elim (fun _ => true) (fun _ => false)
  let w : Fin n ⊕ Fin n → E := Sum.elim (fun i => u i.val) (fun i => v i.val)
  let t : Fin n ⊕ Fin n → ℝ := Sum.elim (fun i => r i.val) (fun i => s i.val)
  have ht : ∀ i, 0 ≤ t i := by intro i; cases i with
    | inl i => exact hr i.val
    | inr i => exact hs i.val
  have he := stdGaussian_finite_slabs_correlation b w t ht
  have hleft : {x : E | ∀ i, b i = true → |⟪w i, x⟫| ≤ t i} = partialSlabs u r n := by
    ext x
    simp [b, w, t, partialSlabs, Sum.forall, Fin.forall_iff]
  have hright : {x : E | ∀ i, b i = false → |⟪w i, x⟫| ≤ t i} = partialSlabs v s n := by
    ext x
    simp [b, w, t, partialSlabs, Sum.forall, Fin.forall_iff]
  have hboth : {x : E | ∀ i, |⟪w i, x⟫| ≤ t i} =
      partialSlabs u r n ∩ partialSlabs v s n := by
    ext x
    simp [w, t, partialSlabs, Sum.forall, Fin.forall_iff]
  simpa only [hleft, hright, hboth] using he

omit [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [BorelSpace E] in
lemma tendsto_real_measure_decreasing {μ : Measure E} [IsFiniteMeasure μ] {S : ℕ → Set E}
    (hS : ∀ n, MeasurableSet (S n)) (hm : Antitone S) :
    Tendsto (fun n => μ.real (S n)) atTop (𝓝 (μ.real (⋂ n, S n))) := by
  exact (ENNReal.tendsto_toReal (measure_ne_top _ _)).comp
    (tendsto_measure_iInter_atTop (fun n => (hS n).nullMeasurableSet) hm
      ⟨0, measure_ne_top _ _⟩)

lemma stdGaussian_closed_convex_correlation_oai {K L : Set E}
    (hK : IsClosed K) (hL : IsClosed L) (hcK : Convex ℝ K) (hcL : Convex ℝ L)
    (hsK : ∀ x ∈ K, -x ∈ K) (hsL : ∀ x ∈ L, -x ∈ L) :
    (stdGaussian E).real K * (stdGaussian E).real L ≤ (stdGaussian E).real (K ∩ L) := by
  by_cases hKe : K.Nonempty
  swap
  · rw [Set.not_nonempty_iff_eq_empty.mp hKe]
    simp
  by_cases hLe : L.Nonempty
  swap
  · rw [Set.not_nonempty_iff_eq_empty.mp hLe]
    simp
  have hz (S : Set E) (hSc : Convex ℝ S) (hSs : ∀ x ∈ S, -x ∈ S) (hSe : S.Nonempty) :
      (0:E) ∈ S := by
    obtain ⟨x, hx⟩ := hSe
    simpa using hSc hx (hSs x hx) (a := (1/2:ℝ)) (b := (1/2:ℝ))
      (by norm_num) (by norm_num) (by norm_num)
  obtain ⟨u, r, hr, hKr⟩ := closed_symmetric_convex_countable_slabs hK hcK hsK (hz K hcK hsK hKe)
  obtain ⟨v, s, hs, hLs⟩ := closed_symmetric_convex_countable_slabs hL hcL hsL (hz L hcL hsL hLe)
  have hKt := tendsto_real_measure_decreasing (μ := stdGaussian E)
    (measurableSet_partialSlabs u r) (partialSlabs_antitone u r)
  have hLt := tendsto_real_measure_decreasing (μ := stdGaussian E)
    (measurableSet_partialSlabs v s) (partialSlabs_antitone v s)
  have hIt := tendsto_real_measure_decreasing (μ := stdGaussian E)
    (fun n => (measurableSet_partialSlabs u r n).inter (measurableSet_partialSlabs v s n))
    (fun _ _ h => Set.inter_subset_inter (partialSlabs_antitone u r h) (partialSlabs_antitone v s h))
  have he := le_of_tendsto_of_tendsto' (hKt.mul hLt) hIt
    (stdGaussian_partialSlabs_correlation u v r s hr hs)
  simpa only [Set.iInter_inter_distrib, partialSlabs_iInter, ← hKr, ← hLs] using he

end EuclideanSteinitz.GaussianCorrelation

end

end OAI
end

theorem solution.{u_1} : type_of% @OAI.EuclideanSteinitz.GaussianCorrelation.stdGaussian_closed_convex_correlation_oai.{u_1} := @OAI.EuclideanSteinitz.GaussianCorrelation.stdGaussian_closed_convex_correlation_oai.{u_1}
