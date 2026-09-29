-- Prove2me | solution 1 for LanglandsTunnell.CubicInduction.WhittakerBlock.setLIntegral_zerothShell_eq_mul_lintegral_torus
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.353894+00:00
-- url     : https://prove2.me/submissions/b96a22c2-eabb-5e77-853d-5810b753ecd4

import Definitions.Def_LanglandsTunnell_CubicInduction_WhittakerBlock
import Definitions.Def_NumberField_IdeleProductMeasure
import Definitions.Def_AutomorphicForm_SmoothingKernel
import Theorems.Thm_NumberField_AdelicHaar_exists_map_adelicGLHaar_eq_smul_prod
import Definitions.Def_Mathlib_Topology_Algebra_RestrictedProduct_TopologicalSpace
import Definitions.Def_NumberField_HeightOneSpectrum
import Theorems.Thm_LanglandsTunnell_CubicInduction_exists_eq_upperUnipotent3_mul_diagonal_mul_mem_localMaximalCompact3
import Theorems.Thm_WhittakerBlock_isHaarMeasure_unipotentHaar3
import Theorems.Thm_HaarQuotient_lintegral_eq_lintegral_lintegral_mul_out
import Theorems.Thm_HaarQuotient_lintegral_density_mul_eq_one
import Theorems.Thm_WhittakerBlock_isMulRightInvariant_unipotentHaar3
import Theorems.Thm_NumberField_TateGlobal_ideleNorm_eq_one_of_fst_eq_one_of_finitePartUnits_mem_unitIdeles
import Theorems.Thm_NumberField_AdeleRing_secondCountableTopology
import Theorems.Thm_NumberField_Idele_exists_lintegral_prod_norm_sPartMeasure_empty_eq_mul_prod_lintegral
import Theorems.Thm_NumberField_TateGlobal_continuous_ideleNorm
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

p2m_attr_erase "ext" "IsDedekindDomain.HeightOneSpectrum.adicCompletion.ext"
p2m_attr_erase "ext" "NumberField.InfinitePlace.Completion.ext"
namespace P2MW.S_LanglandsTunnell_CubicInduction_WhittakerBlock_setLIntegral_zerothShell_eq_mul_lintegral_torus
p2m_attr_erase "instance" "instCountableOfNumberField_definitions instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions"
p2m_attr_erase "simp" "AutomorphicForm.SiegelCoordinates.upperUnit_apply_zero_zero AutomorphicForm.SiegelCoordinates.upperUnit_apply_one_zero AutomorphicForm.SiegelCoordinates.upperUnit_apply_one_one AutomorphicForm.SiegelCoordinates.upperUnit_apply_zero_one"

set_option autoImplicit false
set_option Elab.async false

open IsDedekindDomain NumberField AutomorphicForm MeasureTheory
open scoped ENNReal

namespace LanglandsTunnell
namespace CubicInduction
p2m_export "LanglandsTunnell.CubicInduction" "orth3 AdelicGL upperUnipotent3 upperUnipotent3_coe upperUnipotent3_zero valued_mul_apply_le3 localMaximalCompact3 mem_localMaximalCompact3_iff componentAtN archComponentN componentAt3 archComponent3 exists_eq_upperUnipotent3_mul_diagonal_mul_mem_localMaximalCompact3"
namespace WhittakerBlock
p2m_open "LanglandsTunnell.CubicInduction LanglandsTunnell"

private def orthogonalSubgroup3 : Subgroup (GL (Fin 3) ℝ) where
  carrier := {k | (k : Matrix (Fin 3) (Fin 3) ℝ).transpose * k = 1}
  one_mem' := by simp
  mul_mem' := by
    intro a b ha hb
    simp only [Set.mem_setOf_eq, Units.val_mul, Matrix.transpose_mul] at ha hb ⊢
    rw [Matrix.mul_assoc, ← Matrix.mul_assoc (a : Matrix (Fin 3) (Fin 3) ℝ).transpose, ha, Matrix.one_mul, hb]
  inv_mem' := by
    intro a ha
    simp only [Set.mem_setOf_eq] at ha ⊢
    have hinv : ((a⁻¹ : GL (Fin 3) ℝ) : Matrix (Fin 3) (Fin 3) ℝ) = (a : Matrix (Fin 3) (Fin 3) ℝ).transpose :=
      Units.inv_eq_of_mul_eq_one_left ha
    rw [hinv, Matrix.transpose_transpose, ← hinv, Units.mul_inv]

private def orthogonalMatrixSet3 : Set (Matrix (Fin 3) (Fin 3) ℝ) :=
  {A | A.transpose * A = 1}

private theorem isClosed_orthogonalMatrixSet3 : IsClosed orthogonalMatrixSet3 :=
  isClosed_singleton.preimage
    ((continuous_id : Continuous fun A : Matrix (Fin 3) (Fin 3) ℝ => A).matrix_transpose.matrix_mul continuous_id)

private theorem abs_apply_le_one_of_mem_orthogonalMatrixSet3 {A : Matrix (Fin 3) (Fin 3) ℝ}
    (hA : A ∈ orthogonalMatrixSet3) (i j : Fin 3) : |A i j| ≤ 1 := by
  have hcol : ∑ k, A k j * A k j = 1 := by
    have h := congrFun (congrFun hA j) j
    simpa [Matrix.mul_apply] using h
  rw [abs_le_one_iff_mul_self_le_one, ← hcol]
  exact Finset.single_le_sum (fun k _ => mul_self_nonneg (A k j)) (Finset.mem_univ i)

private theorem isCompact_orthogonalMatrixSet3 : IsCompact orthogonalMatrixSet3 := by
  have hcube : IsCompact (Set.pi Set.univ fun _ : Fin 3 => Set.pi Set.univ fun _ : Fin 3 => Set.Icc (-1 : ℝ) 1) :=
    isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => isCompact_Icc
  refine hcube.of_isClosed_subset isClosed_orthogonalMatrixSet3 fun A hA => ?_
  exact Set.mem_univ_pi.2 fun i => Set.mem_univ_pi.2 fun j =>
    abs_le.1 (abs_apply_le_one_of_mem_orthogonalMatrixSet3 hA i j)

private def orthogonalMatrixToUnits3 (A : orthogonalMatrixSet3) : GL (Fin 3) ℝ :=
  ⟨A.1, A.1.transpose, mul_eq_one_comm.mp A.2, A.2⟩

private theorem continuous_orthogonalMatrixToUnits3 : Continuous orthogonalMatrixToUnits3 :=
  Units.continuous_iff.2 ⟨continuous_subtype_val, continuous_subtype_val.matrix_transpose⟩

private theorem range_orthogonalMatrixToUnits3 :
    Set.range orthogonalMatrixToUnits3 = (orthogonalSubgroup3 : Set (GL (Fin 3) ℝ)) := by
  ext k
  constructor
  · rintro ⟨A, rfl⟩
    exact A.2
  · intro hk
    exact ⟨⟨(k : Matrix (Fin 3) (Fin 3) ℝ), hk⟩, Units.ext rfl⟩

private theorem isClosed_orthogonalSubgroup3 : IsClosed (orthogonalSubgroup3 : Set (GL (Fin 3) ℝ)) :=
  isClosed_singleton.preimage
    ((Units.continuous_val (M := Matrix (Fin 3) (Fin 3) ℝ)).matrix_transpose.matrix_mul Units.continuous_val)

private theorem _root_.LanglandsTunnell.CubicInduction.WhittakerBlock.isCompact_orthogonalSubgroup3 : IsCompact (orthogonalSubgroup3 : Set (GL (Fin 3) ℝ)) := by
  rw [← range_orthogonalMatrixToUnits3]
  haveI : CompactSpace orthogonalMatrixSet3 := isCompact_iff_compactSpace.1 isCompact_orthogonalMatrixSet3
  exact isCompact_range continuous_orthogonalMatrixToUnits3

p2m_export "LanglandsTunnell.CubicInduction.WhittakerBlock" "isCompact_orthogonalSubgroup3"

private theorem continuous_iwasawaMap3 :
    Continuous fun q : ((ℝ × ℝ × ℝ) × (Fin 3 → ℝ)) × orthogonalSubgroup3 =>
      upperUnipotent3 q.1.1.1 q.1.1.2.1 q.1.1.2.2 *
        Units.map (Matrix.diagonalRingHom (Fin 3) ℝ).toMonoidHom
          (MulEquiv.piUnits.symm fun i => Units.mk0 (Real.exp (q.1.2 i)) (Real.exp_pos _).ne') *
        (q.2 : GL (Fin 3) ℝ) := by
  refine (Continuous.mul ?_ ?_).mul (continuous_subtype_val.comp continuous_snd)
  · refine Units.continuous_iff.2 ⟨?_, ?_⟩
    · show Continuous fun q : ((ℝ × ℝ × ℝ) × (Fin 3 → ℝ)) × orthogonalSubgroup3 =>
        (!![1, q.1.1.1, q.1.1.2.2; 0, 1, q.1.1.2.1; 0, 0, 1] : Matrix (Fin 3) (Fin 3) ℝ)
      refine continuous_matrix fun i j => ?_
      fin_cases i <;> fin_cases j <;> simp <;> fun_prop
    · show Continuous fun q : ((ℝ × ℝ × ℝ) × (Fin 3 → ℝ)) × orthogonalSubgroup3 =>
        (!![1, -q.1.1.1, q.1.1.1 * q.1.1.2.1 - q.1.1.2.2; 0, 1, -q.1.1.2.1; 0, 0, 1] : Matrix (Fin 3) (Fin 3) ℝ)
      refine continuous_matrix fun i j => ?_
      fin_cases i <;> fin_cases j <;> simp <;> fun_prop
  · refine Units.continuous_iff.2 ⟨?_, ?_⟩
    · show Continuous fun q : ((ℝ × ℝ × ℝ) × (Fin 3 → ℝ)) × orthogonalSubgroup3 =>
        Matrix.diagonal fun i => Real.exp (q.1.2 i)
      exact Continuous.matrix_diagonal (by fun_prop)
    · show Continuous fun q : ((ℝ × ℝ × ℝ) × (Fin 3 → ℝ)) × orthogonalSubgroup3 =>
        Matrix.diagonal fun i => (Real.exp (q.1.2 i))⁻¹
      refine Continuous.matrix_diagonal (continuous_pi fun i => ?_)
      exact (Real.continuous_exp.comp ((continuous_apply i).comp (continuous_snd.comp continuous_fst))).inv₀
        fun q => (Real.exp_pos _).ne'

private theorem eq_one_of_upper_of_pos_diag_of_transpose_mul_self {b : GL (Fin 3) ℝ}
    (hup : ∀ i j : Fin 3, j < i → (b : Matrix (Fin 3) (Fin 3) ℝ) i j = 0)
    (hpos : ∀ i : Fin 3, 0 < (b : Matrix (Fin 3) (Fin 3) ℝ) i i)
    (horth : (b : Matrix (Fin 3) (Fin 3) ℝ).transpose * b = 1) : b = 1 := by
  set B : Matrix (Fin 3) (Fin 3) ℝ := (b : Matrix (Fin 3) (Fin 3) ℝ) with hB
  have h10 : B 1 0 = 0 := hup 1 0 (by decide)
  have h20 : B 2 0 = 0 := hup 2 0 (by decide)
  have h21 : B 2 1 = 0 := hup 2 1 (by decide)
  have hp0 : 0 < B 0 0 := hpos 0
  have hp1 : 0 < B 1 1 := hpos 1
  have hp2 : 0 < B 2 2 := hpos 2
  have e : ∀ i j : Fin 3, ∑ k, B k i * B k j = (1 : Matrix (Fin 3) (Fin 3) ℝ) i j := fun i j => by
    have := congrFun (congrFun horth i) j
    simpa [Matrix.mul_apply] using this
  have e00 := e 0 0
  have e01 := e 0 1
  have e02 := e 0 2
  have e11 := e 1 1
  have e12 := e 1 2
  have e22 := e 2 2
  simp only [Fin.sum_univ_three, Matrix.one_apply_eq, Matrix.one_apply_ne (show (0 : Fin 3) ≠ 1 by decide),
    Matrix.one_apply_ne (show (0 : Fin 3) ≠ 2 by decide), Matrix.one_apply_ne (show (1 : Fin 3) ≠ 2 by decide),
    h10, h20, h21, mul_zero, zero_mul, add_zero] at e00 e01 e02 e11 e12 e22
  have h00 : B 0 0 = 1 := by nlinarith
  have h01 : B 0 1 = 0 := by
    rw [h00, one_mul] at e01
    exact e01
  have h02 : B 0 2 = 0 := by
    rw [h00, one_mul] at e02
    exact e02
  have h11 : B 1 1 = 1 := by
    rw [h01, mul_zero, zero_add] at e11
    nlinarith
  have h12 : B 1 2 = 0 := by
    rw [h01, zero_mul, zero_add, h11, one_mul] at e12
    exact e12
  have h22 : B 2 2 = 1 := by
    rw [h02, mul_zero, h12, mul_zero, zero_add, zero_add] at e22
    nlinarith
  apply Units.ext
  change B = 1
  ext i j
  fin_cases i <;> fin_cases j <;> simp [h00, h01, h02, h10, h11, h12, h20, h21, h22]

private theorem val_expDiagonal3 (s : Fin 3 → ℝ) :
    ((Units.map (Matrix.diagonalRingHom (Fin 3) ℝ).toMonoidHom
        (MulEquiv.piUnits.symm fun i => Units.mk0 (Real.exp (s i)) (Real.exp_pos _).ne') : GL (Fin 3) ℝ) :
          Matrix (Fin 3) (Fin 3) ℝ) =
      Matrix.diagonal fun i => Real.exp (s i) :=
  rfl

private theorem inv_expDiagonal3 (s : Fin 3 → ℝ) :
    (Units.map (Matrix.diagonalRingHom (Fin 3) ℝ).toMonoidHom
        (MulEquiv.piUnits.symm fun i => Units.mk0 (Real.exp (s i)) (Real.exp_pos _).ne'))⁻¹ =
      Units.map (Matrix.diagonalRingHom (Fin 3) ℝ).toMonoidHom
        (MulEquiv.piUnits.symm fun i => Units.mk0 (Real.exp ((fun i => -s i) i)) (Real.exp_pos _).ne') := by
  refine inv_eq_of_mul_eq_one_right (Units.ext ?_)
  rw [Units.val_mul, val_expDiagonal3, val_expDiagonal3, Matrix.diagonal_mul_diagonal, Units.val_one,
    ← Matrix.diagonal_one]
  congr 1
  funext i
  simp only [← Real.exp_add, add_neg_cancel, Real.exp_zero]

private theorem inv_upperUnipotent3 (x y z : ℝ) :
    (upperUnipotent3 x y z)⁻¹ = upperUnipotent3 (-x) (-y) (x * y - z) :=
  Units.ext rfl

private theorem eq_diagonal_mul_upperUnipotent3_of_upper {R : Matrix (Fin 3) (Fin 3) ℝ}
    (hup : ∀ i j : Fin 3, j < i → R i j = 0) (hpos : ∀ i : Fin 3, 0 < R i i) :
    R = Matrix.diagonal (fun i => R i i) *
      ((upperUnipotent3 (R 0 1 / R 0 0) (R 1 2 / R 1 1) (R 0 2 / R 0 0) : GL (Fin 3) ℝ) :
        Matrix (Fin 3) (Fin 3) ℝ) := by
  have h10 := hup 1 0 (by decide)
  have h20 := hup 2 0 (by decide)
  have h21 := hup 2 1 (by decide)
  have h0 := (hpos 0).ne'
  have h1 := (hpos 1).ne'
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.diagonal_mul, upperUnipotent3_coe, h10, h20, h21] <;> field_simp

private theorem exists_orthogonal_mul_upper_pos_diag (h : Matrix (Fin 3) (Fin 3) ℝ) (hdet : h.det ≠ 0) :
    ∃ Q R : Matrix (Fin 3) (Fin 3) ℝ, Q.transpose * Q = 1 ∧ (∀ i j : Fin 3, j < i → R i j = 0) ∧
      (∀ i : Fin 3, 0 < R i i) ∧ h = Q * R := by

  set f : Fin 3 → EuclideanSpace ℝ (Fin 3) := fun j => WithLp.toLp 2 fun i => h i j with hf
  set b := InnerProductSpace.gramSchmidtOrthonormalBasis (finrank_euclideanSpace (𝕜 := ℝ) (ι := Fin 3)) f with hb
  set Q₀ : Matrix (Fin 3) (Fin 3) ℝ := fun i j => (b j).ofLp i with hQ₀
  set R₀ : Matrix (Fin 3) (Fin 3) ℝ := fun i j => inner ℝ (b i) (f j) with hR₀
  have hQ₀orth : Q₀.transpose * Q₀ = 1 := by
    ext i j
    have hij := orthonormal_iff_ite.1 b.orthonormal i j
    change (b j).ofLp ⬝ᵥ (b i).ofLp = if i = j then (1 : ℝ) else 0 at hij
    rw [Matrix.mul_apply, Matrix.one_apply, ← hij]
    simp only [Matrix.transpose_apply, hQ₀, dotProduct, mul_comm]
  have hR₀up : ∀ i j : Fin 3, j < i → R₀ i j = 0 := fun i j hij =>
    InnerProductSpace.gramSchmidtOrthonormalBasis_inv_triangular _ f hij
  have hfac : h = Q₀ * R₀ := by
    ext i j
    have hsum := congrArg (fun v : EuclideanSpace ℝ (Fin 3) => v.ofLp i) (b.sum_repr' (f j))
    simp only [WithLp.ofLp_sum, WithLp.ofLp_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at hsum
    rw [Matrix.mul_apply]
    change (f j).ofLp i = _
    rw [← hsum]
    simp only [hQ₀, hR₀, mul_comm]
  have hR₀diag : ∀ i : Fin 3, R₀ i i ≠ 0 := by
    have hdetR : R₀.det = ∏ i, R₀ i i := Matrix.det_of_upperTriangular fun i j hij => hR₀up i j hij
    have : R₀.det ≠ 0 := fun h0 => hdet (by rw [hfac, Matrix.det_mul, h0, mul_zero])
    rw [hdetR, Finset.prod_ne_zero_iff] at this
    exact fun i => this i (Finset.mem_univ i)

  set σ : Fin 3 → ℝ := fun i => if 0 < R₀ i i then 1 else -1 with hσ
  have hσσ : ∀ i, σ i * σ i = 1 := by
    intro i
    simp only [hσ]
    split_ifs <;> norm_num
  have hS : Matrix.diagonal σ * Matrix.diagonal σ = 1 := by
    rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    exact congrArg Matrix.diagonal (funext hσσ)
  refine ⟨Q₀ * Matrix.diagonal σ, Matrix.diagonal σ * R₀, ?_, ?_, ?_, ?_⟩
  · rw [Matrix.transpose_mul, Matrix.diagonal_transpose, Matrix.mul_assoc, ← Matrix.mul_assoc Q₀.transpose,
      hQ₀orth, Matrix.one_mul, hS]
  · intro i j hij
    rw [Matrix.diagonal_mul, hR₀up i j hij, mul_zero]
  · intro i
    rw [Matrix.diagonal_mul]
    simp only [hσ]
    split_ifs with hi
    · simpa using hi
    · have := lt_of_le_of_ne (not_lt.1 hi) (hR₀diag i)
      linarith
  · rw [Matrix.mul_assoc, ← Matrix.mul_assoc (Matrix.diagonal σ), hS, Matrix.one_mul, hfac]

private theorem exists_iwasawa3 (g : GL (Fin 3) ℝ) :
    ∃ (x y z : ℝ) (s : Fin 3 → ℝ) (k : orthogonalSubgroup3),
      g = upperUnipotent3 x y z *
        Units.map (Matrix.diagonalRingHom (Fin 3) ℝ).toMonoidHom
          (MulEquiv.piUnits.symm fun i => Units.mk0 (Real.exp (s i)) (Real.exp_pos _).ne') *
        (k : GL (Fin 3) ℝ) := by

  have hdet : ((g⁻¹ : GL (Fin 3) ℝ) : Matrix (Fin 3) (Fin 3) ℝ).det ≠ 0 :=
    ((Matrix.isUnit_iff_isUnit_det _).1 (g⁻¹).isUnit).ne_zero
  obtain ⟨Q, R, hQ, hup, hpos, hfac⟩ := exists_orthogonal_mul_upper_pos_diag _ hdet

  set Qu : GL (Fin 3) ℝ := ⟨Q, Q.transpose, mul_eq_one_comm.1 hQ, hQ⟩ with hQu
  have hk : Qu⁻¹ ∈ orthogonalSubgroup3 := by
    change (Q.transpose).transpose * Q.transpose = 1
    rw [Matrix.transpose_transpose]
    exact mul_eq_one_comm.1 hQ
  set t : Fin 3 → ℝ := fun i => Real.log (R i i) with ht
  have hRd : R = Matrix.diagonal (fun i => Real.exp (t i)) *
      ((upperUnipotent3 (R 0 1 / R 0 0) (R 1 2 / R 1 1) (R 0 2 / R 0 0) : GL (Fin 3) ℝ) :
        Matrix (Fin 3) (Fin 3) ℝ) := by
    conv_lhs => rw [eq_diagonal_mul_upperUnipotent3_of_upper hup hpos]
    congr 2
    funext i
    exact (Real.exp_log (hpos i)).symm

  have hginv : g⁻¹ = Qu *
      Units.map (Matrix.diagonalRingHom (Fin 3) ℝ).toMonoidHom
        (MulEquiv.piUnits.symm fun i => Units.mk0 (Real.exp (t i)) (Real.exp_pos _).ne') *
      upperUnipotent3 (R 0 1 / R 0 0) (R 1 2 / R 1 1) (R 0 2 / R 0 0) := by
    apply Units.ext
    rw [Units.val_mul, Units.val_mul, val_expDiagonal3, hfac]
    conv_lhs => rw [hRd]
    rw [← Matrix.mul_assoc]
  refine ⟨-(R 0 1 / R 0 0), -(R 1 2 / R 1 1), R 0 1 / R 0 0 * (R 1 2 / R 1 1) - R 0 2 / R 0 0, fun i => -t i,
    ⟨Qu⁻¹, hk⟩, ?_⟩
  rw [← inv_upperUnipotent3, ← inv_expDiagonal3, ← inv_inv g, hginv, mul_inv_rev, mul_inv_rev, ← mul_assoc]

private noncomputable def iwasawaDensity3 (q : (ℝ × ℝ × ℝ) × (Fin 3 → ℝ)) : ℝ≥0∞ :=
  ENNReal.ofReal (Real.exp (-2 * q.2 0 + 2 * q.2 2))

private theorem measurable_iwasawaDensity3 : Measurable iwasawaDensity3 := by
  unfold iwasawaDensity3
  fun_prop

private theorem iwasawaDensity3_add_left (p : ℝ × ℝ × ℝ) (s' s : Fin 3 → ℝ) :
    iwasawaDensity3 (p, s) =
      ENNReal.ofReal (Real.exp (2 * s' 0 - 2 * s' 2)) * iwasawaDensity3 (p, s' + s) := by
  unfold iwasawaDensity3
  rw [← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add]
  congr 2
  simp only [Pi.add_apply]
  ring

private theorem iwasawa_measurePreserving_shear (a b c d e : ℝ) :
    MeasurePreserving (fun p : ℝ × ℝ × ℝ => (p.1 + a, p.2.1 + b, p.2.2 + (c + d * p.1 + e * p.2.1)))
      (volume : Measure (ℝ × ℝ × ℝ)) volume := by
  have hinner : ∀ x : ℝ, MeasurePreserving (fun r : ℝ × ℝ => (r.1 + b, r.2 + (c + d * x + e * r.1)))
      (volume : Measure (ℝ × ℝ)) volume := by
    intro x
    rw [Measure.volume_eq_prod]
    exact (measurePreserving_add_right volume b).skew_product (g := fun (y : ℝ) (z : ℝ) => z + (c + d * x + e * y))
      (by show Measurable fun r : ℝ × ℝ => r.2 + (c + d * x + e * r.1); fun_prop)
      (Filter.Eventually.of_forall fun y => (measurePreserving_add_right volume (c + d * x + e * y)).map_eq)
  rw [Measure.volume_eq_prod]
  exact (measurePreserving_add_right volume a).skew_product
    (g := fun (x : ℝ) (r : ℝ × ℝ) => (r.1 + b, r.2 + (c + d * x + e * r.1)))
    (by show Measurable fun p : ℝ × ℝ × ℝ => (p.2.1 + b, p.2.2 + (c + d * p.1 + e * p.2.1)); fun_prop)
    (Filter.Eventually.of_forall fun x => (hinner x).map_eq)

private theorem iwasawa_map_scale_volume {c₁ c₂ c₃ : ℝ} (h₁ : c₁ ≠ 0) (h₂ : c₂ ≠ 0) (h₃ : c₃ ≠ 0) :
    Measure.map (fun p : ℝ × ℝ × ℝ => (c₁ * p.1, c₂ * p.2.1, c₃ * p.2.2)) (volume : Measure (ℝ × ℝ × ℝ)) =
      ENNReal.ofReal |(c₁ * c₂ * c₃)⁻¹| • volume := by
  have hmap : (fun p : ℝ × ℝ × ℝ => (c₁ * p.1, c₂ * p.2.1, c₃ * p.2.2)) =
      Prod.map (c₁ * ·) (Prod.map (c₂ * ·) (c₃ * ·)) := rfl
  rw [hmap, Measure.volume_eq_prod, Measure.volume_eq_prod ℝ ℝ, ← Measure.map_prod_map _ _ (by fun_prop) (by fun_prop),
    ← Measure.map_prod_map _ _ (by fun_prop) (by fun_prop), Real.map_volume_mul_left h₁, Real.map_volume_mul_left h₂,
    Real.map_volume_mul_left h₃]
  simp only [Measure.prod_smul_left, Measure.prod_smul_right, smul_smul]
  congr 1
  rw [show (c₁ * c₂ * c₃)⁻¹ = c₁⁻¹ * c₂⁻¹ * c₃⁻¹ by rw [mul_inv, mul_inv], abs_mul, abs_mul,
    ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (by positivity)]
  ring

private theorem iwasawa_map_withDensity_eq_smul {T : (ℝ × ℝ × ℝ) × (Fin 3 → ℝ) → (ℝ × ℝ × ℝ) × (Fin 3 → ℝ)}
    (hT : Measurable T)
    {α β : ℝ≥0∞} (hvol : Measure.map T (volume : Measure ((ℝ × ℝ × ℝ) × (Fin 3 → ℝ))) = α • volume)
    (hρ : ∀ q, iwasawaDensity3 q = β * iwasawaDensity3 (T q)) :
    Measure.map T (volume.withDensity iwasawaDensity3) = (β * α) • volume.withDensity iwasawaDensity3 := by
  ext s hs
  rw [Measure.map_apply hT hs, Measure.smul_apply, smul_eq_mul, withDensity_apply _ (hT hs), withDensity_apply _ hs,
    ← lintegral_indicator (hT hs), ← lintegral_indicator hs]
  have hpt : ∀ q, (T ⁻¹' s).indicator iwasawaDensity3 q = β * s.indicator iwasawaDensity3 (T q) := by
    intro q
    by_cases hq : T q ∈ s
    · rw [Set.indicator_of_mem (show q ∈ T ⁻¹' s from hq), Set.indicator_of_mem hq, hρ q]
    · rw [Set.indicator_of_notMem (show q ∉ T ⁻¹' s from hq), Set.indicator_of_notMem hq, mul_zero]
  simp_rw [hpt]
  rw [lintegral_const_mul β (show Measurable fun q => s.indicator iwasawaDensity3 (T q) from
      (measurable_iwasawaDensity3.indicator hs).comp hT),
    ← lintegral_map (measurable_iwasawaDensity3.indicator hs) hT, hvol, lintegral_smul_measure, smul_eq_mul, mul_assoc]

private theorem iwasawa_map_shear_withDensity (a b c d e : ℝ) :
    Measure.map (fun q : (ℝ × ℝ × ℝ) × (Fin 3 → ℝ) =>
        ((q.1.1 + a, q.1.2.1 + b, q.1.2.2 + (c + d * q.1.1 + e * q.1.2.1)), q.2))
      (volume.withDensity iwasawaDensity3) = volume.withDensity iwasawaDensity3 := by
  have hT : (fun q : (ℝ × ℝ × ℝ) × (Fin 3 → ℝ) =>
      ((q.1.1 + a, q.1.2.1 + b, q.1.2.2 + (c + d * q.1.1 + e * q.1.2.1)), q.2)) =
      Prod.map (fun p : ℝ × ℝ × ℝ => (p.1 + a, p.2.1 + b, p.2.2 + (c + d * p.1 + e * p.2.1))) id := rfl
  rw [hT]
  have hpres : MeasurePreserving
      (Prod.map (fun p : ℝ × ℝ × ℝ => (p.1 + a, p.2.1 + b, p.2.2 + (c + d * p.1 + e * p.2.1))) id)
      (volume : Measure ((ℝ × ℝ × ℝ) × (Fin 3 → ℝ))) volume := by
    rw [Measure.volume_eq_prod]
    exact (iwasawa_measurePreserving_shear a b c d e).prod (MeasurePreserving.id _)
  rw [iwasawa_map_withDensity_eq_smul hpres.measurable (by rw [hpres.map_eq, one_smul]) (fun q => (one_mul _).symm),
    one_mul, one_smul]

private theorem iwasawa_map_scale_add_withDensity {c₁ c₂ c₃ : ℝ} (h₁ : c₁ ≠ 0) (h₂ : c₂ ≠ 0) (h₃ : c₃ ≠ 0)
    (s' : Fin 3 → ℝ) :
    Measure.map (fun q : (ℝ × ℝ × ℝ) × (Fin 3 → ℝ) => ((c₁ * q.1.1, c₂ * q.1.2.1, c₃ * q.1.2.2), s' + q.2))
        (volume.withDensity iwasawaDensity3) =
      ENNReal.ofReal (Real.exp (2 * s' 0 - 2 * s' 2) / |c₁ * c₂ * c₃|) • volume.withDensity iwasawaDensity3 := by
  have hT : (fun q : (ℝ × ℝ × ℝ) × (Fin 3 → ℝ) => ((c₁ * q.1.1, c₂ * q.1.2.1, c₃ * q.1.2.2), s' + q.2)) =
      Prod.map (fun p : ℝ × ℝ × ℝ => (c₁ * p.1, c₂ * p.2.1, c₃ * p.2.2)) (fun s => s' + s) := rfl
  rw [hT]
  have hvol : Measure.map (Prod.map (fun p : ℝ × ℝ × ℝ => (c₁ * p.1, c₂ * p.2.1, c₃ * p.2.2)) (fun s => s' + s))
      (volume : Measure ((ℝ × ℝ × ℝ) × (Fin 3 → ℝ))) = ENNReal.ofReal |(c₁ * c₂ * c₃)⁻¹| • volume := by
    rw [Measure.volume_eq_prod, ← Measure.map_prod_map _ _ (by fun_prop) (by fun_prop),
      iwasawa_map_scale_volume h₁ h₂ h₃, (measurePreserving_add_left volume s').map_eq, Measure.prod_smul_left]
  rw [iwasawa_map_withDensity_eq_smul (by fun_prop) hvol
      (fun q => iwasawaDensity3_add_left (c₁ * q.1.1, c₂ * q.1.2.1, c₃ * q.1.2.2) s' q.2),
    ← ENNReal.ofReal_mul (Real.exp_pos _).le, abs_inv, div_eq_mul_inv]

private theorem map_iwasawaShift_volume_withDensity (x₀ y₀ z₀ : ℝ) (t : Fin 3 → ℝ) :
    Measure.map (fun q : (ℝ × ℝ × ℝ) × (Fin 3 → ℝ) =>
        ((x₀ + Real.exp (t 0 - t 1) * q.1.1,
          (y₀ + Real.exp (t 1 - t 2) * q.1.2.1,
            z₀ + Real.exp (t 0 - t 2) * q.1.2.2 + x₀ * (Real.exp (t 1 - t 2) * q.1.2.1))), t + q.2))
      ((volume : Measure ((ℝ × ℝ × ℝ) × (Fin 3 → ℝ))).withDensity
        (fun q => ENNReal.ofReal (Real.exp (-2 * q.2 0 + 2 * q.2 2)))) =
    (volume : Measure ((ℝ × ℝ × ℝ) × (Fin 3 → ℝ))).withDensity
      (fun q => ENNReal.ofReal (Real.exp (-2 * q.2 0 + 2 * q.2 2))) := by
  show Measure.map _ (volume.withDensity iwasawaDensity3) = volume.withDensity iwasawaDensity3
  have hexp : ∀ u : ℝ, Real.exp u ≠ 0 := fun u => (Real.exp_pos u).ne'
  have hL : (fun q : (ℝ × ℝ × ℝ) × (Fin 3 → ℝ) =>
        ((x₀ + Real.exp (t 0 - t 1) * q.1.1,
          (y₀ + Real.exp (t 1 - t 2) * q.1.2.1,
            z₀ + Real.exp (t 0 - t 2) * q.1.2.2 + x₀ * (Real.exp (t 1 - t 2) * q.1.2.1))), t + q.2)) =
      (fun q : (ℝ × ℝ × ℝ) × (Fin 3 → ℝ) =>
          ((q.1.1 + x₀, q.1.2.1 + y₀, q.1.2.2 + (z₀ + 0 * q.1.1 + x₀ * q.1.2.1)), q.2)) ∘
        (fun q : (ℝ × ℝ × ℝ) × (Fin 3 → ℝ) =>
          ((Real.exp (t 0 - t 1) * q.1.1, Real.exp (t 1 - t 2) * q.1.2.1, Real.exp (t 0 - t 2) * q.1.2.2),
            t + q.2)) := by
    funext q
    simp only [Function.comp_apply]
    refine Prod.ext (Prod.ext ?_ (Prod.ext ?_ ?_)) rfl
    · dsimp only
      ring
    · dsimp only
      ring
    · dsimp only
      ring
  have hc : ENNReal.ofReal (Real.exp (2 * t 0 - 2 * t 2) /
      |Real.exp (t 0 - t 1) * Real.exp (t 1 - t 2) * Real.exp (t 0 - t 2)|) = 1 := by
    rw [abs_of_pos (by positivity), ← Real.exp_add, ← Real.exp_add,
      show t 0 - t 1 + (t 1 - t 2) + (t 0 - t 2) = 2 * t 0 - 2 * t 2 by ring, div_self (hexp _), ENNReal.ofReal_one]
  rw [hL, ← Measure.map_map (by fun_prop) (by fun_prop),
    iwasawa_map_scale_add_withDensity (hexp _) (hexp _) (hexp _) t, Measure.map_smul, iwasawa_map_shear_withDensity,
    hc, one_smul]

private theorem isFiniteMeasureOnCompacts_withDensity_iwasawaDensity3 :
    IsFiniteMeasureOnCompacts ((volume : Measure ((ℝ × ℝ × ℝ) × (Fin 3 → ℝ))).withDensity iwasawaDensity3) := by
  refine ⟨fun K hK => ?_⟩
  obtain ⟨M, hM⟩ := hK.exists_bound_of_continuousOn
    (f := fun q : (ℝ × ℝ × ℝ) × (Fin 3 → ℝ) => Real.exp (-2 * q.2 0 + 2 * q.2 2)) (by fun_prop)
  rw [withDensity_apply _ hK.measurableSet]
  calc ∫⁻ q in K, iwasawaDensity3 q ∂volume ≤ ∫⁻ _ in K, ENNReal.ofReal M ∂volume :=
        setLIntegral_mono' hK.measurableSet fun q hq =>
          ENNReal.ofReal_le_ofReal ((Real.le_norm_self _).trans (hM q hq))
    _ = ENNReal.ofReal M * volume K := setLIntegral_const K _
    _ < ∞ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top hK.measure_lt_top

private theorem iwasawa_eq_of_isMulLeftInvariant_of_measure_univ_eq {K : Type*} [Group K] [TopologicalSpace K]
    [IsTopologicalGroup K] [CompactSpace K] [MeasurableSpace K] [BorelSpace K] (ν' ν : Measure K)
    [ν.IsHaarMeasure] [ν'.IsMulLeftInvariant] [IsFiniteMeasureOnCompacts ν'] (h : ν' Set.univ = ν Set.univ) :
    ν' = ν := by
  have hν' := Measure.isMulInvariant_eq_smul_of_compactSpace ν' ν
  have hu : ν Set.univ = (Measure.haarScalarFactor ν' ν : ℝ≥0∞) * ν Set.univ := by
    conv_lhs => rw [← h, hν']
    rw [Measure.smul_apply, ENNReal.smul_def, smul_eq_mul]
  have h0 : ν Set.univ ≠ 0 := (isOpen_univ.measure_pos ν Set.univ_nonempty).ne'
  have htop : ν Set.univ ≠ ∞ := (isCompact_univ.measure_lt_top).ne
  have hc : (Measure.haarScalarFactor ν' ν : ℝ≥0∞) = 1 := by
    rw [mul_comm] at hu
    exact (ENNReal.mul_eq_left h0 htop).1 hu.symm
  rw [ENNReal.coe_eq_one.1 hc] at hν'
  rw [hν']
  exact Measure.ext fun s _ => by rw [Measure.smul_apply]; exact one_smul NNReal (ν s)

private theorem map_mul_right_eq_self_of_compactSpace {K : Type*} [Group K] [TopologicalSpace K]
    [IsTopologicalGroup K] [CompactSpace K] [MeasurableSpace K] [BorelSpace K] (ν : Measure K)
    [ν.IsHaarMeasure] (k : K) : Measure.map (fun x => x * k) ν = ν :=
  iwasawa_eq_of_isMulLeftInvariant_of_measure_univ_eq _ ν (by
    rw [Measure.map_apply (measurable_mul_const k) MeasurableSet.univ, Set.preimage_univ])

private theorem iwasawa_isMulRightInvariant_of_compactSpace {K : Type*} [Group K] [TopologicalSpace K]
    [IsTopologicalGroup K] [CompactSpace K] [MeasurableSpace K] [BorelSpace K] (ν : Measure K)
    [ν.IsHaarMeasure] : ν.IsMulRightInvariant :=
  ⟨map_mul_right_eq_self_of_compactSpace ν⟩

private theorem iwasawa_inv_eq_self_of_compactSpace {K : Type*} [Group K] [TopologicalSpace K]
    [IsTopologicalGroup K] [CompactSpace K] [MeasurableSpace K] [BorelSpace K] (ν : Measure K)
    [ν.IsHaarMeasure] : ν.inv = ν := by
  haveI := iwasawa_isMulRightInvariant_of_compactSpace ν
  haveI : IsFiniteMeasure ν.inv := ⟨by rw [Measure.inv_apply, Set.inv_univ]; exact isCompact_univ.measure_lt_top⟩
  exact iwasawa_eq_of_isMulLeftInvariant_of_measure_univ_eq ν.inv ν (by rw [Measure.inv_apply, Set.inv_univ])

private theorem map_inv_eq_self_of_compactSpace {K : Type*} [Group K] [TopologicalSpace K]
    [IsTopologicalGroup K] [CompactSpace K] [MeasurableSpace K] [BorelSpace K] (ν : Measure K)
    [ν.IsHaarMeasure] : Measure.map (fun k => k⁻¹) ν = ν :=
  iwasawa_inv_eq_self_of_compactSpace ν

private theorem expDiag3_coe (t : Fin 3 → ℝ) :
    ((Units.map (Matrix.diagonalRingHom (Fin 3) ℝ).toMonoidHom
          (MulEquiv.piUnits.symm fun i => Units.mk0 (Real.exp (t i)) (Real.exp_pos _).ne') : GL (Fin 3) ℝ) :
        Matrix (Fin 3) (Fin 3) ℝ) =
      !![Real.exp (t 0), 0, 0; 0, Real.exp (t 1), 0; 0, 0, Real.exp (t 2)] := by
  show Matrix.diagonal (fun i => Real.exp (t i)) = _
  ext i j
  fin_cases i <;> fin_cases j <;> simp

private theorem upperUnipotent3_mul_upperUnipotent3 (x y z x' y' z' : ℝ) :
    upperUnipotent3 x y z * upperUnipotent3 x' y' z' = upperUnipotent3 (x + x') (y + y') (z + z' + x * y') := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [upperUnipotent3, Units.val_mul, Matrix.mul_apply, Fin.sum_univ_three]
  all_goals ring

private theorem expDiag3_mul_upperUnipotent3 (t : Fin 3 → ℝ) (x y z : ℝ) :
    Units.map (Matrix.diagonalRingHom (Fin 3) ℝ).toMonoidHom
        (MulEquiv.piUnits.symm fun i => Units.mk0 (Real.exp (t i)) (Real.exp_pos _).ne') * upperUnipotent3 x y z =
      upperUnipotent3 (Real.exp (t 0 - t 1) * x) (Real.exp (t 1 - t 2) * y) (Real.exp (t 0 - t 2) * z) *
        Units.map (Matrix.diagonalRingHom (Fin 3) ℝ).toMonoidHom
          (MulEquiv.piUnits.symm fun i => Units.mk0 (Real.exp (t i)) (Real.exp_pos _).ne') := by
  apply Units.ext
  rw [Units.val_mul, Units.val_mul, expDiag3_coe, upperUnipotent3_coe, upperUnipotent3_coe, Matrix.mul_fin_three,
    Matrix.mul_fin_three]
  have h0 := Real.exp_ne_zero (t 0)
  have h1 := Real.exp_ne_zero (t 1)
  have h2 := Real.exp_ne_zero (t 2)
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Real.exp_sub] <;> field_simp

private theorem expDiag3_mul_expDiag3 (t s : Fin 3 → ℝ) :
    Units.map (Matrix.diagonalRingHom (Fin 3) ℝ).toMonoidHom
          (MulEquiv.piUnits.symm fun i => Units.mk0 (Real.exp (t i)) (Real.exp_pos _).ne') *
        Units.map (Matrix.diagonalRingHom (Fin 3) ℝ).toMonoidHom
          (MulEquiv.piUnits.symm fun i => Units.mk0 (Real.exp (s i)) (Real.exp_pos _).ne') =
      Units.map (Matrix.diagonalRingHom (Fin 3) ℝ).toMonoidHom
        (MulEquiv.piUnits.symm fun i => Units.mk0 (Real.exp ((t + s) i)) (Real.exp_pos _).ne') := by
  apply Units.ext
  rw [Units.val_mul, expDiag3_coe, expDiag3_coe, expDiag3_coe, Matrix.mul_fin_three]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Real.exp_add]

private def posUpper3 : Subgroup (GL (Fin 3) ℝ) where
  carrier := {b | (∀ i j : Fin 3, j < i → (b : Matrix (Fin 3) (Fin 3) ℝ) i j = 0) ∧
    ∀ i : Fin 3, 0 < (b : Matrix (Fin 3) (Fin 3) ℝ) i i}
  one_mem' := by
    refine ⟨fun i j h => ?_, fun i => ?_⟩
    · rw [Units.val_one]
      exact Matrix.one_apply_ne' h.ne
    · rw [Units.val_one, Matrix.one_apply_eq]
      exact one_pos
  mul_mem' := by
    rintro a b ⟨ha, ha'⟩ ⟨hb, hb'⟩
    refine ⟨fun i j h => ?_, fun i => ?_⟩
    · rw [Units.val_mul, Matrix.mul_apply]
      refine Finset.sum_eq_zero fun k _ => ?_
      rcases lt_or_ge k i with hk | hk
      · rw [ha i k hk, zero_mul]
      · rw [hb k j (lt_of_lt_of_le h hk), mul_zero]
    · rw [Units.val_mul, Matrix.mul_apply, Finset.sum_eq_single i]
      · exact mul_pos (ha' i) (hb' i)
      · intro k _ hk
        rcases lt_or_gt_of_ne hk with hk | hk
        · rw [ha i k hk, zero_mul]
        · rw [hb k i hk, mul_zero]
      · exact fun h => (h (Finset.mem_univ i)).elim
  inv_mem' := by
    rintro a ⟨ha, ha'⟩
    haveI : Invertible (a : Matrix (Fin 3) (Fin 3) ℝ) := a.invertible
    have hBT : (a : Matrix (Fin 3) (Fin 3) ℝ).BlockTriangular id := fun i j h => ha i j h
    have hBTi : ((a⁻¹ : GL (Fin 3) ℝ) : Matrix (Fin 3) (Fin 3) ℝ).BlockTriangular id := by
      rw [Matrix.coe_units_inv]
      exact Matrix.blockTriangular_inv_of_blockTriangular hBT
    refine ⟨fun i j h => hBTi h, fun i => ?_⟩
    have h1 : (a : Matrix (Fin 3) (Fin 3) ℝ) i i * ((a⁻¹ : GL (Fin 3) ℝ) : Matrix (Fin 3) (Fin 3) ℝ) i i = 1 := by
      have h := congrArg (fun m : Matrix (Fin 3) (Fin 3) ℝ => m i i) (Units.mul_inv a)
      simp only [Matrix.mul_apply, Matrix.one_apply_eq] at h
      rw [Finset.sum_eq_single i] at h
      · exact h
      · intro k _ hk
        rcases lt_or_gt_of_ne hk with hk | hk
        · rw [ha i k hk, zero_mul]
        · rw [hBTi hk, mul_zero]
      · exact fun h => (h (Finset.mem_univ i)).elim
    have hinv : ((a⁻¹ : GL (Fin 3) ℝ) : Matrix (Fin 3) (Fin 3) ℝ) i i = ((a : Matrix (Fin 3) (Fin 3) ℝ) i i)⁻¹ :=
      eq_inv_of_mul_eq_one_right h1
    rw [hinv]
    exact inv_pos.2 (ha' i)

private theorem mem_posUpper3_iff {b : GL (Fin 3) ℝ} :
    b ∈ posUpper3 ↔ (∀ i j : Fin 3, j < i → (b : Matrix (Fin 3) (Fin 3) ℝ) i j = 0) ∧
      ∀ i : Fin 3, 0 < (b : Matrix (Fin 3) (Fin 3) ℝ) i i :=
  Iff.rfl

private theorem isClosed_posUpper3 : IsClosed ((posUpper3 : Subgroup (GL (Fin 3) ℝ)) : Set (GL (Fin 3) ℝ)) := by
  have hval : Continuous fun b : GL (Fin 3) ℝ => (b : Matrix (Fin 3) (Fin 3) ℝ) := Units.continuous_val
  have hset : ((posUpper3 : Subgroup (GL (Fin 3) ℝ)) : Set (GL (Fin 3) ℝ)) =
      (⋂ i : Fin 3, ⋂ j : Fin 3, {b : GL (Fin 3) ℝ | j < i → (b : Matrix (Fin 3) (Fin 3) ℝ) i j = 0}) ∩
        ⋂ i : Fin 3, {b : GL (Fin 3) ℝ | 0 ≤ (b : Matrix (Fin 3) (Fin 3) ℝ) i i} := by
    ext b
    simp only [SetLike.mem_coe, mem_posUpper3_iff, Set.mem_inter_iff, Set.mem_iInter, Set.mem_setOf_eq]
    constructor
    · rintro ⟨h, h'⟩
      exact ⟨h, fun i => (h' i).le⟩
    · rintro ⟨h, h'⟩
      refine ⟨h, fun i => (h' i).lt_of_ne' ?_⟩
      have hdet : (b : Matrix (Fin 3) (Fin 3) ℝ).det ≠ 0 := (Matrix.isUnits_det_units b).ne_zero
      rw [Matrix.det_of_upperTriangular (fun i j hij => h i j hij)] at hdet
      exact (Finset.prod_ne_zero_iff.1 hdet) i (Finset.mem_univ i)
  rw [hset]
  refine IsClosed.inter (isClosed_iInter fun i => isClosed_iInter fun j => ?_) (isClosed_iInter fun i => ?_)
  · by_cases hij : j < i
    · simp only [hij, forall_true_left]
      exact isClosed_eq (hval.matrix_elem i j) continuous_const
    · simp only [hij, IsEmpty.forall_iff, Set.setOf_true, isClosed_univ]
  · exact isClosed_le continuous_const (hval.matrix_elem i i)

private theorem val_expDiag3 (s : Fin 3 → ℝ) :
    ((Units.map (Matrix.diagonalRingHom (Fin 3) ℝ).toMonoidHom
          (MulEquiv.piUnits.symm fun i => Units.mk0 (Real.exp (s i)) (Real.exp_pos _).ne') : GL (Fin 3) ℝ) :
        Matrix (Fin 3) (Fin 3) ℝ) = Matrix.diagonal fun i => Real.exp (s i) :=
  rfl

private noncomputable def iwasawaB (q : (ℝ × ℝ × ℝ) × (Fin 3 → ℝ)) : GL (Fin 3) ℝ :=
  upperUnipotent3 q.1.1 q.1.2.1 q.1.2.2 *
    Units.map (Matrix.diagonalRingHom (Fin 3) ℝ).toMonoidHom
      (MulEquiv.piUnits.symm fun i => Units.mk0 (Real.exp (q.2 i)) (Real.exp_pos _).ne')

private theorem val_iwasawaB (q : (ℝ × ℝ × ℝ) × (Fin 3 → ℝ)) :
    (iwasawaB q : Matrix (Fin 3) (Fin 3) ℝ) =
      !![Real.exp (q.2 0), q.1.1 * Real.exp (q.2 1), q.1.2.2 * Real.exp (q.2 2);
        0, Real.exp (q.2 1), q.1.2.1 * Real.exp (q.2 2);
        0, 0, Real.exp (q.2 2)] := by
  rw [iwasawaB, Units.val_mul, val_expDiag3, upperUnipotent3_coe]
  ext i j
  rw [Matrix.mul_diagonal]
  fin_cases i <;> fin_cases j <;> simp

private theorem iwasawaB_mem (q : (ℝ × ℝ × ℝ) × (Fin 3 → ℝ)) : iwasawaB q ∈ posUpper3 := by
  refine ⟨fun i j h => ?_, fun i => ?_⟩
  · rw [val_iwasawaB]
    fin_cases i <;> fin_cases j <;> simp at h ⊢
  · rw [val_iwasawaB]
    fin_cases i <;> simp [Real.exp_pos]

private noncomputable def iwasawaLog (b : posUpper3) : (ℝ × ℝ × ℝ) × (Fin 3 → ℝ) :=
  ((((b : GL (Fin 3) ℝ) : Matrix (Fin 3) (Fin 3) ℝ) 0 1 / ((b : GL (Fin 3) ℝ) : Matrix (Fin 3) (Fin 3) ℝ) 1 1,
      (((b : GL (Fin 3) ℝ) : Matrix (Fin 3) (Fin 3) ℝ) 1 2 / ((b : GL (Fin 3) ℝ) : Matrix (Fin 3) (Fin 3) ℝ) 2 2,
        ((b : GL (Fin 3) ℝ) : Matrix (Fin 3) (Fin 3) ℝ) 0 2 / ((b : GL (Fin 3) ℝ) : Matrix (Fin 3) (Fin 3) ℝ) 2 2)),
    fun i => Real.log (((b : GL (Fin 3) ℝ) : Matrix (Fin 3) (Fin 3) ℝ) i i))

private theorem iwasawaLog_iwasawaB (q : (ℝ × ℝ × ℝ) × (Fin 3 → ℝ)) : iwasawaLog ⟨iwasawaB q, iwasawaB_mem q⟩ = q := by
  obtain ⟨⟨x, y, z⟩, s⟩ := q
  have h0 : ∀ r : ℝ, Real.exp r ≠ 0 := fun r => (Real.exp_pos r).ne'
  simp only [iwasawaLog, val_iwasawaB]
  refine Prod.ext (Prod.ext ?_ (Prod.ext ?_ ?_)) (funext fun i => ?_)
  · simp [mul_div_cancel_right₀ _ (h0 _)]
  · simp [mul_div_cancel_right₀ _ (h0 _)]
  · simp [mul_div_cancel_right₀ _ (h0 _)]
  · fin_cases i <;> simp [Real.log_exp]

private theorem iwasawaB_iwasawaLog (b : posUpper3) : iwasawaB (iwasawaLog b) = b := by
  obtain ⟨hz, hp⟩ := mem_posUpper3_iff.1 b.2
  apply Units.ext
  rw [val_iwasawaB]
  ext i j
  simp only [iwasawaLog]
  fin_cases i <;> fin_cases j
  · simp [Real.exp_log (hp 0)]
  · simp [Real.exp_log (hp 1), div_mul_cancel₀ _ (hp 1).ne']
  · simp [Real.exp_log (hp 2), div_mul_cancel₀ _ (hp 2).ne']
  · simp [hz 1 0 (by decide)]
  · simp [Real.exp_log (hp 1)]
  · simp [Real.exp_log (hp 2), div_mul_cancel₀ _ (hp 2).ne']
  · simp [hz 2 0 (by decide)]
  · simp [hz 2 1 (by decide)]
  · simp [Real.exp_log (hp 2)]

private theorem continuous_iwasawaLog : Continuous iwasawaLog := by
  have hval : Continuous fun b : posUpper3 => ((b : GL (Fin 3) ℝ) : Matrix (Fin 3) (Fin 3) ℝ) :=
    Units.continuous_val.comp continuous_subtype_val
  have hne : ∀ (b : posUpper3) (i : Fin 3), ((b : GL (Fin 3) ℝ) : Matrix (Fin 3) (Fin 3) ℝ) i i ≠ 0 :=
    fun b i => ((mem_posUpper3_iff.1 b.2).2 i).ne'
  unfold iwasawaLog
  refine ((((hval.matrix_elem 0 1).div (hval.matrix_elem 1 1) fun b => hne b 1).prodMk
    (((hval.matrix_elem 1 2).div (hval.matrix_elem 2 2) fun b => hne b 2).prodMk
      ((hval.matrix_elem 0 2).div (hval.matrix_elem 2 2) fun b => hne b 2))).prodMk
    (continuous_pi fun i => (hval.matrix_elem i i).log fun b => hne b i))

private noncomputable def iwasawaBHomeomorph (hc : Continuous iwasawaB) :
    ((ℝ × ℝ × ℝ) × (Fin 3 → ℝ)) ≃ₜ posUpper3 where
  toFun q := ⟨iwasawaB q, iwasawaB_mem q⟩
  invFun := iwasawaLog
  left_inv := iwasawaLog_iwasawaB
  right_inv b := Subtype.ext (iwasawaB_iwasawaLog b)
  continuous_toFun := hc.subtype_mk _
  continuous_invFun := continuous_iwasawaLog

private theorem map_mul_right_eq_self_of_isCompact_subgroup [MeasurableSpace (GL (Fin 3) ℝ)]
    [BorelSpace (GL (Fin 3) ℝ)] {K : Subgroup (GL (Fin 3) ℝ)} (hK : IsCompact (K : Set (GL (Fin 3) ℝ)))
    (μ : Measure (GL (Fin 3) ℝ)) [μ.IsHaarMeasure]
    {k : GL (Fin 3) ℝ} (hk : k ∈ K) : Measure.map (fun g => g * k) μ = μ := by
  haveI : SecondCountableTopology (Matrix (Fin 3) (Fin 3) ℝ) :=
    inferInstanceAs (SecondCountableTopology (Fin 3 → Fin 3 → ℝ))
  haveI : SecondCountableTopology (Matrix (Fin 3) (Fin 3) ℝ)ᵐᵒᵖ :=
    MulOpposite.opHomeomorph.symm.secondCountableTopology
  haveI : SecondCountableTopology (GL (Fin 3) ℝ) := Units.isInducing_embedProduct.secondCountableTopology
  haveI : LocallyCompactSpace (Matrix (Fin 3) (Fin 3) ℝ) := inferInstanceAs (LocallyCompactSpace (Fin 3 → Fin 3 → ℝ))
  haveI : LocallyCompactSpace (Matrix (Fin 3) (Fin 3) ℝ)ᵐᵒᵖ := MulOpposite.instLocallyCompactSpace
  haveI : LocallyCompactSpace (Matrix (Fin 3) (Fin 3) ℝ × (Matrix (Fin 3) (Fin 3) ℝ)ᵐᵒᵖ) :=
    Prod.locallyCompactSpace _ _
  haveI : LocallyCompactSpace (GL (Fin 3) ℝ) := Units.isClosedEmbedding_embedProduct.locallyCompactSpace
  obtain ⟨U, hUc, hU1⟩ := exists_compact_mem_nhds (1 : GL (Fin 3) ℝ)
  set E : Set (GL (Fin 3) ℝ) :=
    (fun p : GL (Fin 3) ℝ × GL (Fin 3) ℝ => p.1 * p.2) '' (U ×ˢ (K : Set (GL (Fin 3) ℝ))) with hE
  have hEc : IsCompact E := (hUc.prod hK).image continuous_mul
  have hUE : U ⊆ E := fun u hu => ⟨(u, 1), ⟨hu, K.one_mem⟩, mul_one u⟩
  have hpre : (fun g => g * k) ⁻¹' E = E := by
    ext g
    simp only [hE, Set.mem_preimage, Set.mem_image, Set.mem_prod, Prod.exists]
    constructor
    · rintro ⟨u, k', ⟨hu, hk'⟩, h⟩
      exact ⟨u, k' * k⁻¹, ⟨hu, K.mul_mem hk' (K.inv_mem hk)⟩, by rw [← mul_assoc, h, mul_inv_cancel_right]⟩
    · rintro ⟨u, k', ⟨hu, hk'⟩, h⟩
      exact ⟨u, k' * k, ⟨hu, K.mul_mem hk' hk⟩, by rw [← mul_assoc, h]⟩
  have hc := Measure.isMulLeftInvariant_eq_smul (Measure.map (fun g => g * k) μ) μ
  have hE0 : μ E ≠ 0 := (Measure.measure_pos_of_mem_nhds μ (Filter.mem_of_superset hU1 hUE)).ne'
  have hET : μ E ≠ ⊤ := hEc.measure_lt_top.ne
  have hval : Measure.map (fun g => g * k) μ E = μ E := by
    rw [Measure.map_apply (measurable_mul_const k) hEc.measurableSet, hpre]
  have h1 : Measure.haarScalarFactor (Measure.map (fun g => g * k) μ) μ = 1 := by
    have h := congrArg (fun m : Measure (GL (Fin 3) ℝ) => m E) hc
    simp only [Measure.coe_nnreal_smul_apply, hval] at h
    rw [← ENNReal.coe_eq_one]
    exact ((ENNReal.mul_left_inj hE0 hET).1 (by rw [one_mul]; exact h.symm))
  rw [hc, h1]
  exact Measure.ext fun s _ => by rw [Measure.coe_nnreal_smul_apply, ENNReal.coe_one, one_mul]

private noncomputable def iwasawaProdHomeomorph (hK : IsCompact (orthogonalSubgroup3 : Set (GL (Fin 3) ℝ)))
    (hsurj : Function.Surjective
      fun p : posUpper3 × orthogonalSubgroup3 => (p.1 : GL (Fin 3) ℝ) * ((p.2 : GL (Fin 3) ℝ))⁻¹)
    (hinj : Function.Injective
      fun p : posUpper3 × orthogonalSubgroup3 => (p.1 : GL (Fin 3) ℝ) * ((p.2 : GL (Fin 3) ℝ))⁻¹) :
    posUpper3 × orthogonalSubgroup3 ≃ₜ GL (Fin 3) ℝ :=
  haveI : LocallyCompactSpace (Matrix (Fin 3) (Fin 3) ℝ) := inferInstanceAs (LocallyCompactSpace (Fin 3 → Fin 3 → ℝ))
  haveI : LocallyCompactSpace (Matrix (Fin 3) (Fin 3) ℝ)ᵐᵒᵖ := MulOpposite.instLocallyCompactSpace
  haveI : LocallyCompactSpace (Matrix (Fin 3) (Fin 3) ℝ × (Matrix (Fin 3) (Fin 3) ℝ)ᵐᵒᵖ) :=
    Prod.locallyCompactSpace _ _
  haveI : LocallyCompactSpace (GL (Fin 3) ℝ) := Units.isClosedEmbedding_embedProduct.locallyCompactSpace
  haveI : CompactSpace orthogonalSubgroup3 := isCompact_iff_compactSpace.mp hK
  have hcont : Continuous fun p : posUpper3 × orthogonalSubgroup3 => (p.1 : GL (Fin 3) ℝ) * ((p.2 : GL (Fin 3) ℝ))⁻¹ :=
    (continuous_subtype_val.comp continuous_fst).mul (continuous_subtype_val.comp continuous_snd).inv
  have hproper :
      IsProperMap fun p : posUpper3 × orthogonalSubgroup3 => (p.1 : GL (Fin 3) ℝ) * ((p.2 : GL (Fin 3) ℝ))⁻¹ := by
    refine isProperMap_iff_isCompact_preimage.2 ⟨hcont, fun C hC => ?_⟩
    have hbig : IsCompact ((Subtype.val ⁻¹'
        ((fun p : GL (Fin 3) ℝ × GL (Fin 3) ℝ => p.1 * p.2) ''
          (C ×ˢ (orthogonalSubgroup3 : Set (GL (Fin 3) ℝ)))) : Set posUpper3) ×ˢ
          (Set.univ : Set orthogonalSubgroup3)) :=
      (isClosed_posUpper3.isClosedEmbedding_subtypeVal.isCompact_preimage
        ((hC.prod hK).image continuous_mul)).prod isCompact_univ
    refine hbig.of_isClosed_subset (hC.isClosed.preimage hcont) fun p hp => ⟨?_, Set.mem_univ _⟩
    exact ⟨((p.1 : GL (Fin 3) ℝ) * ((p.2 : GL (Fin 3) ℝ))⁻¹, (p.2 : GL (Fin 3) ℝ)), ⟨hp, p.2.2⟩,
      inv_mul_cancel_right _ _⟩
  (Topology.IsClosedEmbedding.of_continuous_injective_isClosedMap hcont hinj
    hproper.isClosedMap).toIsEmbedding.toHomeomorphOfSurjective hsurj

private theorem isFiniteMeasureOnCompacts_volume_withDensity_exp :
    IsFiniteMeasureOnCompacts ((volume : Measure ((ℝ × ℝ × ℝ) × (Fin 3 → ℝ))).withDensity
      fun q => ENNReal.ofReal (Real.exp (-2 * q.2 0 + 2 * q.2 2))) := by
  refine ⟨fun C hC => ?_⟩
  rw [withDensity_apply _ hC.measurableSet]
  have hcont : Continuous fun q : (ℝ × ℝ × ℝ) × (Fin 3 → ℝ) => (Real.exp (-2 * q.2 0 + 2 * q.2 2)).toNNReal :=
    continuous_real_toNNReal.comp (Real.continuous_exp.comp
      ((continuous_const.mul ((continuous_apply 0).comp continuous_snd)).add
        (continuous_const.mul ((continuous_apply 2).comp continuous_snd))))
  exact setLIntegral_lt_top_of_isCompact hC.measure_lt_top.ne hC hcont

private theorem isOpenPosMeasure_volume_withDensity_exp :
    ((volume : Measure ((ℝ × ℝ × ℝ) × (Fin 3 → ℝ))).withDensity
      fun q => ENNReal.ofReal (Real.exp (-2 * q.2 0 + 2 * q.2 2))).IsOpenPosMeasure := by
  refine ⟨fun U hU hne => ?_⟩
  have hm : Measurable fun q : (ℝ × ℝ × ℝ) × (Fin 3 → ℝ) => ENNReal.ofReal (Real.exp (-2 * q.2 0 + 2 * q.2 2)) :=
    ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp
      ((measurable_const.mul ((measurable_pi_apply 0).comp measurable_snd)).add
        (measurable_const.mul ((measurable_pi_apply 2).comp measurable_snd))))
  rw [Ne, withDensity_apply_eq_zero' hm.aemeasurable]
  have huniv : {q : (ℝ × ℝ × ℝ) × (Fin 3 → ℝ) | ENNReal.ofReal (Real.exp (-2 * q.2 0 + 2 * q.2 2)) ≠ 0} = Set.univ :=
    Set.eq_univ_of_forall fun q => (ENNReal.ofReal_pos.2 (Real.exp_pos _)).ne'
  rw [huniv, Set.univ_inter]
  exact (hU.measure_pos volume hne).ne'

private theorem iwasawaProdHomeomorph_apply (hK : IsCompact (orthogonalSubgroup3 : Set (GL (Fin 3) ℝ)))
    (hsurj : Function.Surjective
      fun p : posUpper3 × orthogonalSubgroup3 => (p.1 : GL (Fin 3) ℝ) * ((p.2 : GL (Fin 3) ℝ))⁻¹)
    (hinj : Function.Injective
      fun p : posUpper3 × orthogonalSubgroup3 => (p.1 : GL (Fin 3) ℝ) * ((p.2 : GL (Fin 3) ℝ))⁻¹)
    (p : posUpper3 × orthogonalSubgroup3) :
    iwasawaProdHomeomorph hK hsurj hinj p = (p.1 : GL (Fin 3) ℝ) * ((p.2 : GL (Fin 3) ℝ))⁻¹ :=
  rfl

private theorem continuous_iwasawaB : Continuous iwasawaB :=
  (continuous_iwasawaMap3.comp (continuous_id.prodMk
    (continuous_const : Continuous fun _ : (ℝ × ℝ × ℝ) × (Fin 3 → ℝ) => (1 : orthogonalSubgroup3)))).congr
      fun q => mul_one (iwasawaB q)

private theorem iwasawaB_mul (x₀ y₀ z₀ : ℝ) (t : Fin 3 → ℝ) (q : (ℝ × ℝ × ℝ) × (Fin 3 → ℝ)) :
    iwasawaB ((x₀, y₀, z₀), t) * iwasawaB q =
      iwasawaB ((x₀ + Real.exp (t 0 - t 1) * q.1.1,
        (y₀ + Real.exp (t 1 - t 2) * q.1.2.1,
          z₀ + Real.exp (t 0 - t 2) * q.1.2.2 + x₀ * (Real.exp (t 1 - t 2) * q.1.2.1))), t + q.2) := by
  simp only [iwasawaB]
  rw [show ∀ a b c d : GL (Fin 3) ℝ, a * b * (c * d) = a * (b * c) * d from fun a b c d => by simp only [mul_assoc],
    expDiag3_mul_upperUnipotent3,
    show ∀ a b c d : GL (Fin 3) ℝ, a * (b * c) * d = a * b * (c * d) from fun a b c d => by simp only [mul_assoc],
    upperUnipotent3_mul_upperUnipotent3, expDiag3_mul_expDiag3]

private theorem isHaarMeasure_map_iwasawaBHomeomorph [MeasurableSpace (GL (Fin 3) ℝ)] [BorelSpace (GL (Fin 3) ℝ)]
    (hc : Continuous iwasawaB) :
    (Measure.map (iwasawaBHomeomorph hc) ((volume : Measure ((ℝ × ℝ × ℝ) × (Fin 3 → ℝ))).withDensity
      fun q => ENNReal.ofReal (Real.exp (-2 * q.2 0 + 2 * q.2 2)))).IsHaarMeasure := by
  have hφm : Measurable (iwasawaBHomeomorph hc) := (iwasawaBHomeomorph hc).measurable
  refine
    { toIsFiniteMeasureOnCompacts := ⟨fun C hC => ?_⟩
      toIsMulLeftInvariant := ⟨fun b => ?_⟩
      toIsOpenPosMeasure := ⟨fun U hU hne => ?_⟩ }
  · rw [Measure.map_apply hφm hC.measurableSet]
    haveI := isFiniteMeasureOnCompacts_volume_withDensity_exp
    exact ((iwasawaBHomeomorph hc).isCompact_preimage.2 hC).measure_lt_top
  · obtain ⟨⟨⟨x₀, y₀, z₀⟩, t⟩, rfl⟩ := (iwasawaBHomeomorph hc).surjective b
    have hLc : Continuous fun q : (ℝ × ℝ × ℝ) × (Fin 3 → ℝ) =>
        ((x₀ + Real.exp (t 0 - t 1) * q.1.1,
          (y₀ + Real.exp (t 1 - t 2) * q.1.2.1,
            z₀ + Real.exp (t 0 - t 2) * q.1.2.2 + x₀ * (Real.exp (t 1 - t 2) * q.1.2.1))), t + q.2) :=
      ((continuous_const.add (continuous_const.mul (continuous_fst.comp continuous_fst))).prodMk
        ((continuous_const.add
          (continuous_const.mul ((continuous_fst.comp continuous_snd).comp continuous_fst))).prodMk
          ((continuous_const.add
            (continuous_const.mul ((continuous_snd.comp continuous_snd).comp continuous_fst))).add
            (continuous_const.mul
              (continuous_const.mul ((continuous_fst.comp continuous_snd).comp continuous_fst)))))).prodMk
        (continuous_const.add continuous_snd)
    have hcomp : (fun x => iwasawaBHomeomorph hc ((x₀, y₀, z₀), t) * x) ∘ (iwasawaBHomeomorph hc) =
        (iwasawaBHomeomorph hc) ∘ fun q : (ℝ × ℝ × ℝ) × (Fin 3 → ℝ) =>
          ((x₀ + Real.exp (t 0 - t 1) * q.1.1,
            (y₀ + Real.exp (t 1 - t 2) * q.1.2.1,
              z₀ + Real.exp (t 0 - t 2) * q.1.2.2 + x₀ * (Real.exp (t 1 - t 2) * q.1.2.1))), t + q.2) :=
      funext fun q => Subtype.ext (iwasawaB_mul x₀ y₀ z₀ t q)
    rw [Measure.map_map (measurable_const_mul _) hφm, hcomp, ← Measure.map_map hφm hLc.measurable,
      map_iwasawaShift_volume_withDensity]
  · rw [Measure.map_apply hφm hU.measurableSet]
    haveI := isOpenPosMeasure_volume_withDensity_exp
    exact ((hU.preimage (iwasawaBHomeomorph hc).continuous).measure_pos _
      (hne.preimage (iwasawaBHomeomorph hc).surjective)).ne'

private theorem exists_isHaarMeasure_GL_three_real_eq_smul_map_iwasawa
    [MeasurableSpace (GL (Fin 3) ℝ)] [BorelSpace (GL (Fin 3) ℝ)]
    (μ : Measure (GL (Fin 3) ℝ)) [μ.IsHaarMeasure]
    (ν : Measure orthogonalSubgroup3) [ν.IsHaarMeasure] :
    ∃ c : ℝ≥0∞, c ≠ 0 ∧ c ≠ ⊤ ∧
      μ = c • Measure.map
        (fun q : ((ℝ × ℝ × ℝ) × (Fin 3 → ℝ)) × orthogonalSubgroup3 =>
          upperUnipotent3 q.1.1.1 q.1.1.2.1 q.1.1.2.2 *
            Units.map (Matrix.diagonalRingHom (Fin 3) ℝ).toMonoidHom
              (MulEquiv.piUnits.symm fun i => Units.mk0 (Real.exp (q.1.2 i)) (Real.exp_pos _).ne') *
            (q.2 : GL (Fin 3) ℝ))
        (((volume : Measure ((ℝ × ℝ × ℝ) × (Fin 3 → ℝ))).withDensity
            (fun q => ENNReal.ofReal (Real.exp (-2 * q.2 0 + 2 * q.2 2)))).prod ν) := by

  haveI : SecondCountableTopology (Matrix (Fin 3) (Fin 3) ℝ) :=
    inferInstanceAs (SecondCountableTopology (Fin 3 → Fin 3 → ℝ))
  haveI : SecondCountableTopology (Matrix (Fin 3) (Fin 3) ℝ)ᵐᵒᵖ :=
    MulOpposite.opHomeomorph.symm.secondCountableTopology
  haveI : SecondCountableTopology (GL (Fin 3) ℝ) := Units.isInducing_embedProduct.secondCountableTopology
  haveI : LocallyCompactSpace (Matrix (Fin 3) (Fin 3) ℝ) :=
    inferInstanceAs (LocallyCompactSpace (Fin 3 → Fin 3 → ℝ))
  haveI : LocallyCompactSpace (Matrix (Fin 3) (Fin 3) ℝ)ᵐᵒᵖ := MulOpposite.instLocallyCompactSpace
  haveI : LocallyCompactSpace (Matrix (Fin 3) (Fin 3) ℝ × (Matrix (Fin 3) (Fin 3) ℝ)ᵐᵒᵖ) :=
    Prod.locallyCompactSpace _ _
  haveI : LocallyCompactSpace (GL (Fin 3) ℝ) := Units.isClosedEmbedding_embedProduct.locallyCompactSpace

  haveI : CompactSpace orthogonalSubgroup3 := isCompact_iff_compactSpace.mp isCompact_orthogonalSubgroup3
  haveI : IsFiniteMeasure ν := CompactSpace.isFiniteMeasure
  haveI : LocallyCompactSpace posUpper3 := isClosed_posUpper3.isClosedEmbedding_subtypeVal.locallyCompactSpace
  haveI : SecondCountableTopology posUpper3 := TopologicalSpace.Subtype.secondCountableTopology _
  haveI : SecondCountableTopology orthogonalSubgroup3 := TopologicalSpace.Subtype.secondCountableTopology _
  haveI : BorelSpace posUpper3 := Subtype.borelSpace _
  haveI : BorelSpace orthogonalSubgroup3 := Subtype.borelSpace _
  haveI : BorelSpace (posUpper3 × orthogonalSubgroup3) := Prod.borelSpace
  haveI : MeasurableMul posUpper3 := ContinuousMul.measurableMul
  haveI : MeasurableMul orthogonalSubgroup3 := ContinuousMul.measurableMul
  haveI : MeasurableMul (posUpper3 × orthogonalSubgroup3) := ContinuousMul.measurableMul
  haveI : MeasurableInv orthogonalSubgroup3 := ContinuousInv.measurableInv

  set ρ : Measure ((ℝ × ℝ × ℝ) × (Fin 3 → ℝ)) :=
    (volume : Measure ((ℝ × ℝ × ℝ) × (Fin 3 → ℝ))).withDensity
      fun q => ENNReal.ofReal (Real.exp (-2 * q.2 0 + 2 * q.2 2)) with hρ
  set φ : ((ℝ × ℝ × ℝ) × (Fin 3 → ℝ)) ≃ₜ posUpper3 := iwasawaBHomeomorph continuous_iwasawaB with hφ
  have hφm : Measurable φ := φ.measurable
  haveI : (Measure.map φ ρ).IsHaarMeasure := isHaarMeasure_map_iwasawaBHomeomorph continuous_iwasawaB

  have hsurj : Function.Surjective
      fun p : posUpper3 × orthogonalSubgroup3 => (p.1 : GL (Fin 3) ℝ) * ((p.2 : GL (Fin 3) ℝ))⁻¹ := by
    intro g
    obtain ⟨x, y, z, s, k, hg⟩ := exists_iwasawa3 g
    refine ⟨(⟨iwasawaB ((x, y, z), s), iwasawaB_mem _⟩, k⁻¹), ?_⟩
    show iwasawaB ((x, y, z), s) * (((k⁻¹ : orthogonalSubgroup3) : GL (Fin 3) ℝ))⁻¹ = g
    rw [hg, Subgroup.coe_inv, inv_inv]
    rfl
  have hinj : Function.Injective
      fun p : posUpper3 × orthogonalSubgroup3 => (p.1 : GL (Fin 3) ℝ) * ((p.2 : GL (Fin 3) ℝ))⁻¹ := by
    rintro ⟨b, k⟩ ⟨b', k'⟩ h
    change (b : GL (Fin 3) ℝ) * ((k : GL (Fin 3) ℝ))⁻¹ =
      (b' : GL (Fin 3) ℝ) * ((k' : GL (Fin 3) ℝ))⁻¹ at h
    have hbk : ((b'⁻¹ * b : posUpper3) : GL (Fin 3) ℝ) =
        ((k'⁻¹ * k : orthogonalSubgroup3) : GL (Fin 3) ℝ) := by
      have hb : (b : GL (Fin 3) ℝ) = b' * ((k' : GL (Fin 3) ℝ))⁻¹ * k := by rw [← h, inv_mul_cancel_right]
      rw [Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_mul, Subgroup.coe_inv, hb]
      group
    have hu : (b'⁻¹ * b : posUpper3) = 1 := by
      obtain ⟨hz, hp⟩ := mem_posUpper3_iff.1 (b'⁻¹ * b).2
      have horth : ((b'⁻¹ * b : posUpper3) : GL (Fin 3) ℝ) ∈ orthogonalSubgroup3 := hbk ▸ (k'⁻¹ * k).2
      exact Subtype.ext (eq_one_of_upper_of_pos_diag_of_transpose_mul_self hz hp horth)
    have hk : (k'⁻¹ * k : orthogonalSubgroup3) = 1 := by
      apply Subtype.ext
      rw [← hbk, hu]
      rfl
    rw [inv_mul_eq_one] at hu hk
    rw [hu, hk]
  set Ψ : posUpper3 × orthogonalSubgroup3 ≃ₜ GL (Fin 3) ℝ :=
    iwasawaProdHomeomorph isCompact_orthogonalSubgroup3 hsurj hinj with hΨ
  have hΨapply : ∀ p : posUpper3 × orthogonalSubgroup3,
      Ψ p = (p.1 : GL (Fin 3) ℝ) * ((p.2 : GL (Fin 3) ℝ))⁻¹ :=
    iwasawaProdHomeomorph_apply isCompact_orthogonalSubgroup3 hsurj hinj
  set Ψm : posUpper3 × orthogonalSubgroup3 ≃ᵐ GL (Fin 3) ℝ := Ψ.toMeasurableEquiv with hΨm
  have hΨmapply : ∀ p : posUpper3 × orthogonalSubgroup3,
      Ψm p = (p.1 : GL (Fin 3) ℝ) * ((p.2 : GL (Fin 3) ℝ))⁻¹ := by
    intro p
    rw [hΨm, Homeomorph.toMeasurableEquiv_coe, hΨapply]

  set μ' : Measure (posUpper3 × orthogonalSubgroup3) := Measure.map Ψm.symm μ with hμ'
  haveI : μ'.IsMulLeftInvariant := by
    refine ⟨fun h => ?_⟩
    obtain ⟨b₀, k₀⟩ := h
    have hT :
        Measure.map (fun g : GL (Fin 3) ℝ => (b₀ : GL (Fin 3) ℝ) * g * ((k₀ : GL (Fin 3) ℝ))⁻¹) μ = μ := by
      rw [show (fun g : GL (Fin 3) ℝ => (b₀ : GL (Fin 3) ℝ) * g * ((k₀ : GL (Fin 3) ℝ))⁻¹) =
          (fun g : GL (Fin 3) ℝ => (b₀ : GL (Fin 3) ℝ) * g) ∘
            fun g : GL (Fin 3) ℝ => g * ((k₀ : GL (Fin 3) ℝ))⁻¹ from
            funext fun g => mul_assoc _ _ _,
        ← Measure.map_map (measurable_const_mul _) (measurable_mul_const _),
        map_mul_right_eq_self_of_isCompact_subgroup isCompact_orthogonalSubgroup3 μ
          (orthogonalSubgroup3.inv_mem k₀.2),
        map_mul_left_eq_self]
    have hkey : ∀ p : posUpper3 × orthogonalSubgroup3,
        Ψm ((b₀, k₀) * p) = (b₀ : GL (Fin 3) ℝ) * Ψm p * ((k₀ : GL (Fin 3) ℝ))⁻¹ := by
      intro p
      rw [hΨmapply, hΨmapply, Prod.fst_mul, Prod.snd_mul, Subgroup.coe_mul, Subgroup.coe_mul, mul_inv_rev]
      simp only [mul_assoc]
    have hcomm : (fun p : posUpper3 × orthogonalSubgroup3 => (b₀, k₀) * p) ∘ Ψm.symm =
        Ψm.symm ∘ fun g : GL (Fin 3) ℝ => (b₀ : GL (Fin 3) ℝ) * g * ((k₀ : GL (Fin 3) ℝ))⁻¹ := by
      funext g
      apply Ψm.injective
      simp only [Function.comp_apply]
      rw [hkey, MeasurableEquiv.apply_symm_apply, MeasurableEquiv.apply_symm_apply]
    rw [hμ', Measure.map_map (measurable_const_mul _) Ψm.symm.measurable, hcomm,
      ← Measure.map_map Ψm.symm.measurable ((measurable_const_mul _).mul_const _), hT]
  haveI : IsFiniteMeasureOnCompacts μ' := by
    refine ⟨fun C hC => ?_⟩
    rw [hμ', Measure.map_apply Ψm.symm.measurable hC.measurableSet, hΨm, Homeomorph.toMeasurableEquiv_symm_coe]
    exact (Ψ.symm.isCompact_preimage.2 hC).measure_lt_top

  have huniq := Measure.isMulLeftInvariant_eq_smul μ' ((Measure.map φ ρ).prod ν)
  set c := Measure.haarScalarFactor μ' ((Measure.map φ ρ).prod ν) with hc
  have hμ : μ = Measure.map Ψm μ' := by rw [hμ', MeasurableEquiv.map_map_symm]

  have hfun :
      (Ψm : posUpper3 × orthogonalSubgroup3 → GL (Fin 3) ℝ) ∘ Prod.map φ (fun k : orthogonalSubgroup3 => k⁻¹) =
      fun q : ((ℝ × ℝ × ℝ) × (Fin 3 → ℝ)) × orthogonalSubgroup3 =>
        upperUnipotent3 q.1.1.1 q.1.1.2.1 q.1.1.2.2 *
          Units.map (Matrix.diagonalRingHom (Fin 3) ℝ).toMonoidHom
            (MulEquiv.piUnits.symm fun i => Units.mk0 (Real.exp (q.1.2 i)) (Real.exp_pos _).ne') *
          (q.2 : GL (Fin 3) ℝ) := by
    funext q
    rw [Function.comp_apply, hΨmapply, Prod.map_fst, Prod.map_snd, Subgroup.coe_inv, inv_inv, hφ]
    rfl
  have hid : Measure.map Ψm ((Measure.map φ ρ).prod ν) = Measure.map
      (fun q : ((ℝ × ℝ × ℝ) × (Fin 3 → ℝ)) × orthogonalSubgroup3 =>
        upperUnipotent3 q.1.1.1 q.1.1.2.1 q.1.1.2.2 *
          Units.map (Matrix.diagonalRingHom (Fin 3) ℝ).toMonoidHom
            (MulEquiv.piUnits.symm fun i => Units.mk0 (Real.exp (q.1.2 i)) (Real.exp_pos _).ne') *
          (q.2 : GL (Fin 3) ℝ)) (ρ.prod ν) := by
    conv_lhs => rw [← map_inv_eq_self_of_compactSpace ν]
    rw [Measure.map_prod_map _ _ hφm measurable_inv, Measure.map_map Ψm.measurable (hφm.prodMap measurable_inv),
      hfun]
  have hcpos : c ≠ 0 := by
    intro h0
    apply (isOpen_univ.measure_pos μ Set.univ_nonempty).ne'
    rw [hμ, huniq, h0, Measure.map_apply Ψm.measurable MeasurableSet.univ, Measure.coe_nnreal_smul_apply,
      ENNReal.coe_zero, zero_mul]
  refine ⟨c, ENNReal.coe_ne_zero.2 hcpos, ENNReal.coe_ne_top, ?_⟩
  rw [hμ, huniq, Measure.map_smul, hid]
  exact Measure.ext fun s _ => by rw [Measure.coe_nnreal_smul_apply, Measure.smul_apply, smul_eq_mul]

section

private abbrev IwasawaThree.secondCountable_finiteAdeleRing : SecondCountableTopology (FiniteAdeleRing (𝓞 ℚ) ℚ) :=
  RestrictedProduct.secondCountableTopology fun v : HeightOneSpectrum (𝓞 ℚ) =>
    Valued.isOpen_valuationSubring (v.adicCompletion ℚ)
attribute [local instance] IwasawaThree.secondCountable_finiteAdeleRing

private abbrev IwasawaThree.secondCountable_completion (v : InfinitePlace ℚ) :
    SecondCountableTopology v.Completion := by
  obtain rfl : v = Rat.infinitePlace := Subsingleton.elim _ _
  exact (InfinitePlace.Completion.isometryEquivRealOfIsReal
    Rat.isReal_infinitePlace).toHomeomorph.secondCountableTopology
attribute [local instance] IwasawaThree.secondCountable_completion

private abbrev IwasawaThree.secondCountable_infiniteAdeleRing : SecondCountableTopology (InfiniteAdeleRing ℚ) :=
  inferInstanceAs (SecondCountableTopology ((v : InfinitePlace ℚ) → v.Completion))
attribute [local instance] IwasawaThree.secondCountable_infiniteAdeleRing

private abbrev IwasawaThree.secondCountable_adeleRing : SecondCountableTopology (AdeleRing (𝓞 ℚ) ℚ) :=
  inferInstanceAs (SecondCountableTopology (InfiniteAdeleRing ℚ × FiniteAdeleRing (𝓞 ℚ) ℚ))
attribute [local instance] IwasawaThree.secondCountable_adeleRing

private abbrev IwasawaThree.secondCountable_adeleRing_mop : SecondCountableTopology (AdeleRing (𝓞 ℚ) ℚ)ᵐᵒᵖ :=
  MulOpposite.opHomeomorph.symm.secondCountableTopology
attribute [local instance] IwasawaThree.secondCountable_adeleRing_mop

private abbrev IwasawaThree.secondCountable_ideles : SecondCountableTopology (AdeleRing (𝓞 ℚ) ℚ)ˣ :=
  Units.isEmbedding_embedProduct.isInducing.secondCountableTopology
attribute [local instance] IwasawaThree.secondCountable_ideles

private abbrev IwasawaThree.secondCountable_matrix_adeleRing :
    SecondCountableTopology (Matrix (Fin 3) (Fin 3) (AdeleRing (𝓞 ℚ) ℚ)) :=
  inferInstanceAs (SecondCountableTopology (Fin 3 → Fin 3 → AdeleRing (𝓞 ℚ) ℚ))
attribute [local instance] IwasawaThree.secondCountable_matrix_adeleRing

private abbrev IwasawaThree.secondCountable_matrix_adeleRing_mop :
    SecondCountableTopology (Matrix (Fin 3) (Fin 3) (AdeleRing (𝓞 ℚ) ℚ))ᵐᵒᵖ :=
  MulOpposite.opHomeomorph.symm.secondCountableTopology
attribute [local instance] IwasawaThree.secondCountable_matrix_adeleRing_mop

private abbrev IwasawaThree.secondCountable_adelicGL : SecondCountableTopology (AdelicGL 3 (𝓞 ℚ) ℚ) :=
  Units.isEmbedding_embedProduct.isInducing.secondCountableTopology
attribute [local instance] IwasawaThree.secondCountable_adelicGL

private abbrev IwasawaThree.secondCountable_matrix_infiniteAdeleRing :
    SecondCountableTopology (Matrix (Fin 3) (Fin 3) (InfiniteAdeleRing ℚ)) :=
  inferInstanceAs (SecondCountableTopology (Fin 3 → Fin 3 → InfiniteAdeleRing ℚ))
attribute [local instance] IwasawaThree.secondCountable_matrix_infiniteAdeleRing

private abbrev IwasawaThree.secondCountable_matrix_infiniteAdeleRing_mop :
    SecondCountableTopology (Matrix (Fin 3) (Fin 3) (InfiniteAdeleRing ℚ))ᵐᵒᵖ :=
  MulOpposite.opHomeomorph.symm.secondCountableTopology
attribute [local instance] IwasawaThree.secondCountable_matrix_infiniteAdeleRing_mop

private abbrev IwasawaThree.secondCountable_gl_infiniteAdeleRing :
    SecondCountableTopology (GL (Fin 3) (InfiniteAdeleRing ℚ)) :=
  Units.isEmbedding_embedProduct.isInducing.secondCountableTopology
attribute [local instance] IwasawaThree.secondCountable_gl_infiniteAdeleRing

private abbrev IwasawaThree.secondCountable_matrix_finiteAdeleRing :
    SecondCountableTopology (Matrix (Fin 3) (Fin 3) (FiniteAdeleRing (𝓞 ℚ) ℚ)) :=
  inferInstanceAs (SecondCountableTopology (Fin 3 → Fin 3 → FiniteAdeleRing (𝓞 ℚ) ℚ))
attribute [local instance] IwasawaThree.secondCountable_matrix_finiteAdeleRing

private abbrev IwasawaThree.secondCountable_matrix_finiteAdeleRing_mop :
    SecondCountableTopology (Matrix (Fin 3) (Fin 3) (FiniteAdeleRing (𝓞 ℚ) ℚ))ᵐᵒᵖ :=
  MulOpposite.opHomeomorph.symm.secondCountableTopology
attribute [local instance] IwasawaThree.secondCountable_matrix_finiteAdeleRing_mop

private abbrev IwasawaThree.secondCountable_gl_finiteAdeleRing :
    SecondCountableTopology (GL (Fin 3) (FiniteAdeleRing (𝓞 ℚ) ℚ)) :=
  Units.isEmbedding_embedProduct.isInducing.secondCountableTopology
attribute [local instance] IwasawaThree.secondCountable_gl_finiteAdeleRing

private abbrev IwasawaThree.secondCountable_finiteAdeleRing_mop :
    SecondCountableTopology (FiniteAdeleRing (𝓞 ℚ) ℚ)ᵐᵒᵖ :=
  MulOpposite.opHomeomorph.symm.secondCountableTopology
attribute [local instance] IwasawaThree.secondCountable_finiteAdeleRing_mop

private abbrev IwasawaThree.secondCountable_finiteIdeles : SecondCountableTopology (FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ :=
  Units.isEmbedding_embedProduct.isInducing.secondCountableTopology
attribute [local instance] IwasawaThree.secondCountable_finiteIdeles

private abbrev IwasawaThree.secondCountable_infiniteAdeleRing_mop :
    SecondCountableTopology (InfiniteAdeleRing ℚ)ᵐᵒᵖ :=
  MulOpposite.opHomeomorph.symm.secondCountableTopology
attribute [local instance] IwasawaThree.secondCountable_infiniteAdeleRing_mop

private abbrev IwasawaThree.secondCountable_infiniteAdeleRing_units :
    SecondCountableTopology (InfiniteAdeleRing ℚ)ˣ :=
  Units.isEmbedding_embedProduct.isInducing.secondCountableTopology
attribute [local instance] IwasawaThree.secondCountable_infiniteAdeleRing_units

private abbrev IwasawaThree.locallyCompact_finiteIdeles : LocallyCompactSpace (FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ :=
  Units.isClosedEmbedding_embedProduct.locallyCompactSpace
attribute [local instance] IwasawaThree.locallyCompact_finiteIdeles

private abbrev IwasawaThree.sigmaCompact_finiteIdeles : SigmaCompactSpace (FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ := inferInstance
attribute [local instance] IwasawaThree.sigmaCompact_finiteIdeles

private abbrev IwasawaThree.locallyCompact_matrix_finiteAdeleRing :
    LocallyCompactSpace (Matrix (Fin 3) (Fin 3) (FiniteAdeleRing (𝓞 ℚ) ℚ)) :=
  inferInstanceAs (LocallyCompactSpace (Fin 3 → Fin 3 → FiniteAdeleRing (𝓞 ℚ) ℚ))
attribute [local instance] IwasawaThree.locallyCompact_matrix_finiteAdeleRing

private abbrev IwasawaThree.locallyCompact_matrix_infiniteAdeleRing :
    LocallyCompactSpace (Matrix (Fin 3) (Fin 3) (InfiniteAdeleRing ℚ)) :=
  inferInstanceAs (LocallyCompactSpace (Fin 3 → Fin 3 → InfiniteAdeleRing ℚ))
attribute [local instance] IwasawaThree.locallyCompact_matrix_infiniteAdeleRing

private abbrev IwasawaThree.locallyCompact_gl_finiteAdeleRing :
    LocallyCompactSpace (GL (Fin 3) (FiniteAdeleRing (𝓞 ℚ) ℚ)) :=
  Units.isClosedEmbedding_embedProduct.locallyCompactSpace
attribute [local instance] IwasawaThree.locallyCompact_gl_finiteAdeleRing

private abbrev IwasawaThree.locallyCompact_gl_infiniteAdeleRing :
    LocallyCompactSpace (GL (Fin 3) (InfiniteAdeleRing ℚ)) :=
  Units.isClosedEmbedding_embedProduct.locallyCompactSpace
attribute [local instance] IwasawaThree.locallyCompact_gl_infiniteAdeleRing

private abbrev IwasawaThree.secondCountable_subgroup (K : Subgroup (AdelicGL 3 (𝓞 ℚ) ℚ)) :
    SecondCountableTopology K :=
  Topology.IsInducing.subtypeVal.secondCountableTopology
attribute [local instance] IwasawaThree.secondCountable_subgroup

private abbrev IwasawaThree.secondCountable_subgroup_finiteAdeleRing
    (K : Subgroup (GL (Fin 3) (FiniteAdeleRing (𝓞 ℚ) ℚ))) :
    SecondCountableTopology K :=
  Topology.IsInducing.subtypeVal.secondCountableTopology
attribute [local instance] IwasawaThree.secondCountable_subgroup_finiteAdeleRing

private abbrev IwasawaThree.secondCountable_subgroup_infiniteAdeleRing
    (K : Subgroup (GL (Fin 3) (InfiniteAdeleRing ℚ))) :
    SecondCountableTopology K :=
  Topology.IsInducing.subtypeVal.secondCountableTopology
attribute [local instance] IwasawaThree.secondCountable_subgroup_infiniteAdeleRing

private abbrev IwasawaThree.sigmaCompact_ideles : SigmaCompactSpace (AdeleRing (𝓞 ℚ) ℚ)ˣ := inferInstance
attribute [local instance] IwasawaThree.sigmaCompact_ideles

private abbrev IwasawaThree.sigmaFinite_idelicHaar : SigmaFinite (Idele.idelicHaar ℚ) := by
  letI : MeasurableSpace (AdeleRing (𝓞 ℚ) ℚ)ˣ := Idele.ideleBorel ℚ
  haveI := Idele.isHaarMeasure_idelicHaar ℚ
  exact inferInstance
attribute [local instance] IwasawaThree.sigmaFinite_idelicHaar

private theorem IwasawaThree.sigmaFinite_pi_idelicHaar :
    letI : MeasurableSpace (AdeleRing (𝓞 ℚ) ℚ)ˣ := Idele.ideleBorel ℚ
    SigmaFinite (Measure.pi fun _ : Fin 3 => Idele.idelicHaar ℚ) := by
  letI : MeasurableSpace (AdeleRing (𝓞 ℚ) ℚ)ˣ := Idele.ideleBorel ℚ
  exact inferInstance

private theorem IwasawaThree.exists_ennreal_smul_eq_of_isHaarMeasure {G : Type*} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [LocallyCompactSpace G] [SecondCountableTopology G] [MeasurableSpace G]
    [BorelSpace G] (μ ν : Measure G) [μ.IsHaarMeasure] [ν.IsHaarMeasure] :
    ∃ c : ENNReal, c ≠ 0 ∧ c ≠ ⊤ ∧ μ = c • ν := by
  refine ⟨(Measure.haarScalarFactor μ ν : ENNReal), ?_, ENNReal.coe_ne_top, ?_⟩
  · exact_mod_cast (Measure.haarScalarFactor_pos_of_isHaarMeasure μ ν).ne'
  · rw [← ENNReal.smul_def]
    exact Measure.isMulLeftInvariant_eq_smul μ ν

private theorem IwasawaThree.exists_ennreal_smul_eq_of_isAddHaarMeasure {G : Type*} [AddGroup G] [TopologicalSpace G]
    [IsTopologicalAddGroup G] [LocallyCompactSpace G] [SecondCountableTopology G] [MeasurableSpace G]
    [BorelSpace G] (μ ν : Measure G) [μ.IsAddHaarMeasure] [ν.IsAddHaarMeasure] :
    ∃ c : ENNReal, c ≠ 0 ∧ c ≠ ⊤ ∧ μ = c • ν := by
  refine ⟨(Measure.addHaarScalarFactor μ ν : ENNReal), ?_, ENNReal.coe_ne_top, ?_⟩
  · exact_mod_cast (Measure.addHaarScalarFactor_pos_of_isAddHaarMeasure μ ν).ne'
  · rw [← ENNReal.smul_def]
    exact Measure.isAddLeftInvariant_eq_smul μ ν

private theorem IwasawaThree.continuous_glMap_adeleArch :
    Continuous fun x : AdelicGL 3 (𝓞 ℚ) ℚ =>
      Matrix.GeneralLinearGroup.map (AdelicLevel.adeleArch (𝓞 ℚ) ℚ) x := by
  refine Units.continuous_iff.2 ⟨?_, ?_⟩
  · exact Units.continuous_val.matrix_map (AdelicLevel.continuous_adeleArch (𝓞 ℚ) ℚ)
  · exact Units.continuous_coe_inv.matrix_map (AdelicLevel.continuous_adeleArch (𝓞 ℚ) ℚ)

private theorem IwasawaThree.continuous_glMap_adeleFin :
    Continuous fun x : AdelicGL 3 (𝓞 ℚ) ℚ =>
      Matrix.GeneralLinearGroup.map (AdelicLevel.adeleFin (𝓞 ℚ) ℚ) x := by
  refine Units.continuous_iff.2 ⟨?_, ?_⟩
  · exact Units.continuous_val.matrix_map (AdelicLevel.continuous_adeleFin (𝓞 ℚ) ℚ)
  · exact Units.continuous_coe_inv.matrix_map (AdelicLevel.continuous_adeleFin (𝓞 ℚ) ℚ)

private theorem IwasawaThree.measurable_glSplit :
    letI : MeasurableSpace (AdelicGL 3 (𝓞 ℚ) ℚ) := AdelicHaar.glBorel (Fin 3) (𝓞 ℚ) ℚ
    letI : MeasurableSpace (GL (Fin 3) (InfiniteAdeleRing ℚ)) := borel _
    letI : MeasurableSpace (GL (Fin 3) (FiniteAdeleRing (𝓞 ℚ) ℚ)) := borel _
    Measurable fun x : AdelicGL 3 (𝓞 ℚ) ℚ =>
      (Matrix.GeneralLinearGroup.map (AdelicLevel.adeleArch (𝓞 ℚ) ℚ) x,
        Matrix.GeneralLinearGroup.map (AdelicLevel.adeleFin (𝓞 ℚ) ℚ) x) := by
  letI : MeasurableSpace (AdelicGL 3 (𝓞 ℚ) ℚ) := AdelicHaar.glBorel (Fin 3) (𝓞 ℚ) ℚ
  haveI : BorelSpace (AdelicGL 3 (𝓞 ℚ) ℚ) := AdelicHaar.borelSpace_glBorel (Fin 3) (𝓞 ℚ) ℚ
  letI : MeasurableSpace (GL (Fin 3) (InfiniteAdeleRing ℚ)) := borel _
  haveI : BorelSpace (GL (Fin 3) (InfiniteAdeleRing ℚ)) := ⟨rfl⟩
  letI : MeasurableSpace (GL (Fin 3) (FiniteAdeleRing (𝓞 ℚ) ℚ)) := borel _
  haveI : BorelSpace (GL (Fin 3) (FiniteAdeleRing (𝓞 ℚ) ℚ)) := ⟨rfl⟩
  exact continuous_glMap_adeleArch.measurable.prodMk continuous_glMap_adeleFin.measurable

private noncomputable abbrev IwasawaThree.diagGL {R : Type*} [CommRing R] (t : Fin 3 → Rˣ) : GL (Fin 3) R :=
  Units.map (Matrix.diagonalRingHom (Fin 3) R).toMonoidHom (MulEquiv.piUnits.symm t)

private noncomputable def IwasawaThree.matrixSplit :
    Matrix (Fin 3) (Fin 3) (AdeleRing (𝓞 ℚ) ℚ) ≃*
      Matrix (Fin 3) (Fin 3) (InfiniteAdeleRing ℚ) × Matrix (Fin 3) (Fin 3) (FiniteAdeleRing (𝓞 ℚ) ℚ) where
  toFun M := (M.map (AdelicLevel.adeleArch (𝓞 ℚ) ℚ), M.map (AdelicLevel.adeleFin (𝓞 ℚ) ℚ))
  invFun P := Matrix.of fun i j => (P.1 i j, P.2 i j)
  left_inv _ := Matrix.ext fun _ _ => rfl
  right_inv _ := Prod.ext (Matrix.ext fun _ _ => rfl) (Matrix.ext fun _ _ => rfl)
  map_mul' _ _ := Prod.ext Matrix.map_mul Matrix.map_mul

private theorem IwasawaThree.continuous_matrixSplit_symm : Continuous IwasawaThree.matrixSplit.symm :=
  continuous_matrix fun i j => (continuous_fst.matrix_elem i j).prodMk (continuous_snd.matrix_elem i j)

private noncomputable def IwasawaThree.glSplit :
    AdelicGL 3 (𝓞 ℚ) ℚ ≃* GL (Fin 3) (InfiniteAdeleRing ℚ) × GL (Fin 3) (FiniteAdeleRing (𝓞 ℚ) ℚ) :=
  (Units.mapEquiv IwasawaThree.matrixSplit).trans MulEquiv.prodUnits

private theorem IwasawaThree.glSplit_apply (x : AdelicGL 3 (𝓞 ℚ) ℚ) :
    IwasawaThree.glSplit x =
      (Matrix.GeneralLinearGroup.map (AdelicLevel.adeleArch (𝓞 ℚ) ℚ) x,
        Matrix.GeneralLinearGroup.map (AdelicLevel.adeleFin (𝓞 ℚ) ℚ) x) :=
  Prod.ext (Units.ext rfl) (Units.ext rfl)

private theorem IwasawaThree.continuous_glSplit : Continuous IwasawaThree.glSplit := by
  have h : (IwasawaThree.glSplit : AdelicGL 3 (𝓞 ℚ) ℚ → _) = fun x =>
      (Matrix.GeneralLinearGroup.map (AdelicLevel.adeleArch (𝓞 ℚ) ℚ) x,
        Matrix.GeneralLinearGroup.map (AdelicLevel.adeleFin (𝓞 ℚ) ℚ) x) :=
    funext IwasawaThree.glSplit_apply
  rw [h]
  exact IwasawaThree.continuous_glMap_adeleArch.prodMk IwasawaThree.continuous_glMap_adeleFin

private theorem IwasawaThree.continuous_glSplit_symm : Continuous IwasawaThree.glSplit.symm := by
  have h₁ : Continuous (Units.map IwasawaThree.matrixSplit.symm.toMonoidHom) :=
    IwasawaThree.continuous_matrixSplit_symm.units_map _
  have h₂ : Continuous (MulEquiv.prodUnits (M := Matrix (Fin 3) (Fin 3) (InfiniteAdeleRing ℚ))
      (N := Matrix (Fin 3) (Fin 3) (FiniteAdeleRing (𝓞 ℚ) ℚ))).symm :=
    (Homeomorph.prodUnits (α := Matrix (Fin 3) (Fin 3) (InfiniteAdeleRing ℚ))
      (β := Matrix (Fin 3) (Fin 3) (FiniteAdeleRing (𝓞 ℚ) ℚ))).symm.continuous
  exact h₁.comp h₂

private theorem IwasawaThree.measurable_glSplit_symm :
    letI : MeasurableSpace (AdelicGL 3 (𝓞 ℚ) ℚ) := AdelicHaar.glBorel (Fin 3) (𝓞 ℚ) ℚ
    letI : MeasurableSpace (GL (Fin 3) (InfiniteAdeleRing ℚ)) := borel _
    letI : MeasurableSpace (GL (Fin 3) (FiniteAdeleRing (𝓞 ℚ) ℚ)) := borel _
    Measurable IwasawaThree.glSplit.symm := by
  letI : MeasurableSpace (AdelicGL 3 (𝓞 ℚ) ℚ) := AdelicHaar.glBorel (Fin 3) (𝓞 ℚ) ℚ
  haveI : BorelSpace (AdelicGL 3 (𝓞 ℚ) ℚ) := AdelicHaar.borelSpace_glBorel (Fin 3) (𝓞 ℚ) ℚ
  letI : MeasurableSpace (GL (Fin 3) (InfiniteAdeleRing ℚ)) := borel _
  haveI : BorelSpace (GL (Fin 3) (InfiniteAdeleRing ℚ)) := ⟨rfl⟩
  letI : MeasurableSpace (GL (Fin 3) (FiniteAdeleRing (𝓞 ℚ) ℚ)) := borel _
  haveI : BorelSpace (GL (Fin 3) (FiniteAdeleRing (𝓞 ℚ) ℚ)) := ⟨rfl⟩
  exact IwasawaThree.continuous_glSplit_symm.measurable

private noncomputable def IwasawaThree.ideleSplit :
    (AdeleRing (𝓞 ℚ) ℚ)ˣ ≃ₜ* (InfiniteAdeleRing ℚ)ˣ × (FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ where
  toMulEquiv := MulEquiv.prodUnits
  continuous_toFun :=
    (Homeomorph.prodUnits (α := InfiniteAdeleRing ℚ) (β := FiniteAdeleRing (𝓞 ℚ) ℚ)).continuous
  continuous_invFun :=
    (Homeomorph.prodUnits (α := InfiniteAdeleRing ℚ) (β := FiniteAdeleRing (𝓞 ℚ) ℚ)).symm.continuous

private theorem IwasawaThree.regular_adelicAddHaar :
    @Measure.Regular (AdeleRing (𝓞 ℚ) ℚ) (AdelicHaar.adeleBorel (𝓞 ℚ) ℚ) _
      (AdelicHaar.adelicAddHaar (𝓞 ℚ) ℚ) := by
  letI := AdelicHaar.adeleBorel (𝓞 ℚ) ℚ
  haveI := AdelicHaar.borelSpace_adeleBorel (𝓞 ℚ) ℚ
  unfold AdelicHaar.adelicAddHaar
  infer_instance

private theorem IwasawaThree.exists_countable_iUnion_image_mul_eq_univ {G : Type*} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [SecondCountableTopology G] (K : Subgroup G) (hKo : IsOpen (K : Set G)) :
    ∃ D : Set G, D.Countable ∧ ⋃ d ∈ D, (fun x => d * x) '' (K : Set G) = Set.univ := by
  obtain ⟨D, hDc, hDd⟩ := TopologicalSpace.exists_countable_dense G
  refine ⟨D, hDc, Set.eq_univ_of_forall fun g => ?_⟩
  obtain ⟨d, hdD, hd⟩ := hDd.exists_mem_open (isOpenMap_mul_left g _ hKo) ⟨g, ⟨1, K.one_mem, mul_one g⟩⟩
  obtain ⟨k, hk, rfl⟩ := hd
  exact Set.mem_iUnion₂.2 ⟨g * k, hdD, ⟨k⁻¹, K.inv_mem hk, mul_inv_cancel_right g k⟩⟩

private theorem IwasawaThree.image_mul_eq_image_mul_of_inv_mul_mem {G : Type*} [Group G] (K : Subgroup G) {d b : G}
    (h : b⁻¹ * d ∈ K) : (fun x => d * x) '' (K : Set G) = (fun x => b * x) '' (K : Set G) := by
  ext y
  constructor
  · rintro ⟨k, hk, rfl⟩
    exact ⟨b⁻¹ * d * k, K.mul_mem h hk, by simp [mul_assoc]⟩
  · rintro ⟨k, hk, rfl⟩
    refine ⟨d⁻¹ * b * k, K.mul_mem ?_ hk, by simp [mul_assoc]⟩
    simpa using K.inv_mem h

private theorem IwasawaThree.inter_image_mul_eq {G : Type*} [Group G] (K : Subgroup G) (b : G) (A : Set G) :
    A ∩ (fun x => b * x) '' (K : Set G) = (fun x => b * x) '' ((fun x => b⁻¹ * x) '' A ∩ (K : Set G)) := by
  ext y
  constructor
  · rintro ⟨hyA, k, hk, rfl⟩
    exact ⟨k, ⟨⟨b * k, hyA, inv_mul_cancel_left b k⟩, hk⟩, rfl⟩
  · rintro ⟨k, ⟨⟨a, haA, hak⟩, hk⟩, rfl⟩
    refine ⟨?_, k, hk, rfl⟩
    rw [← hak]
    show b * (b⁻¹ * a) ∈ A
    rw [mul_inv_cancel_left]
    exact haA

private theorem IwasawaThree.eq_smul_of_isOpen_of_forall_subset {G : Type*} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]
    (B K : Subgroup G) (hKo : IsOpen (K : Set G)) (hBK : ∀ g : G, ∃ b ∈ B, b⁻¹ * g ∈ K) (μ ν : Measure G)
    (c : ℝ≥0∞) (hμ : ∀ b ∈ B, ∀ A : Set G, MeasurableSet A → μ ((fun x => b * x) '' A) = μ A)
    (hν : ∀ b ∈ B, ∀ A : Set G, MeasurableSet A → ν ((fun x => b * x) '' A) = ν A)
    (hK : ∀ A : Set G, A ⊆ (K : Set G) → MeasurableSet A → ν A = c * μ A) : ν = c • μ := by
  obtain ⟨D, hDc, hDcov⟩ := IwasawaThree.exists_countable_iUnion_image_mul_eq_univ K hKo
  haveI : Countable D := hDc.to_subtype
  have hcov : ⋃ d : D, (fun x => (d : G) * x) '' (K : Set G) = Set.univ := by
    rw [← hDcov, Set.biUnion_eq_iUnion]
  refine (Measure.ext_iff_of_iUnion_eq_univ hcov).2 fun d => ?_
  obtain ⟨b, hbB, hbd⟩ := hBK d
  rw [IwasawaThree.image_mul_eq_image_mul_of_inv_mul_mem K hbd]
  ext A hA
  have hA' : MeasurableSet ((fun x => b⁻¹ * x) '' A ∩ (K : Set G)) := by
    refine MeasurableSet.inter ?_ hKo.measurableSet
    have h := (MeasurableEquiv.mulLeft b⁻¹).measurableSet_image.2 hA
    rwa [MeasurableEquiv.coe_mulLeft] at h
  rw [Measure.restrict_apply hA, Measure.restrict_apply hA, Measure.smul_apply, smul_eq_mul,
    IwasawaThree.inter_image_mul_eq K b A, hν b hbB _ hA', hK _ Set.inter_subset_right hA', hμ b hbB _ hA']

private theorem IwasawaThree.measure_image_mul_eq_of_map_eq {G : Type*} [Group G] [MeasurableSpace G]
    [MeasurableMul G] (μ : Measure G) (b : G) (h : Measure.map (fun x => b * x) μ = μ) (A : Set G)
    (hA : MeasurableSet A) : μ ((fun x => b * x) '' A) = μ A := by
  have himg : (fun x => b * x) '' A = (fun x => b⁻¹ * x) ⁻¹' A := by
    ext y
    constructor
    · rintro ⟨a, ha, rfl⟩
      show b⁻¹ * (b * a) ∈ A
      rwa [inv_mul_cancel_left]
    · intro hy
      exact ⟨b⁻¹ * y, hy, mul_inv_cancel_left b y⟩
  have hinv : Measure.map (fun x => b⁻¹ * x) μ = μ := by
    have hcomp : ((fun x => b⁻¹ * x) ∘ fun x => b * x) = id := by
      funext x
      exact inv_mul_cancel_left b x
    calc Measure.map (fun x => b⁻¹ * x) μ
        = Measure.map (fun x => b⁻¹ * x) (Measure.map (fun x => b * x) μ) := by rw [h]
      _ = Measure.map ((fun x => b⁻¹ * x) ∘ fun x => b * x) μ :=
          Measure.map_map (measurable_const_mul b⁻¹) (measurable_const_mul b)
      _ = μ := by rw [hcomp, Measure.map_id]
  rw [himg, ← Measure.map_apply (measurable_const_mul b⁻¹) hA, hinv]

private noncomputable def IwasawaThree.intGL3f : Subgroup (GL (Fin 3) (FiniteAdeleRing (𝓞 ℚ) ℚ)) :=
  ⨅ v : HeightOneSpectrum (𝓞 ℚ),
    (localMaximalCompact3 (𝓞 ℚ) ℚ v).comap
      (Matrix.GeneralLinearGroup.map (AdelicLevel.finAdeleEval (𝓞 ℚ) ℚ v))

private theorem IwasawaThree.mem_intGL3f_iff (k : GL (Fin 3) (FiniteAdeleRing (𝓞 ℚ) ℚ)) :
    k ∈ IwasawaThree.intGL3f ↔ ∀ v : HeightOneSpectrum (𝓞 ℚ),
      Matrix.GeneralLinearGroup.map (AdelicLevel.finAdeleEval (𝓞 ℚ) ℚ v) k ∈
        localMaximalCompact3 (𝓞 ℚ) ℚ v := by
  simp only [IwasawaThree.intGL3f, Subgroup.mem_iInf, Subgroup.mem_comap]

private def IwasawaThree.upperTriangular3 (A : Type*) [CommRing A] : Subgroup (GL (Fin 3) A) where
  carrier := {g | (g : Matrix (Fin 3) (Fin 3) A).BlockTriangular id ∧
    ((g⁻¹ : GL (Fin 3) A) : Matrix (Fin 3) (Fin 3) A).BlockTriangular id}
  one_mem' := by
    refine ⟨?_, ?_⟩
    · rw [Units.val_one]
      exact Matrix.blockTriangular_one
    · rw [inv_one, Units.val_one]
      exact Matrix.blockTriangular_one
  mul_mem' := by
    rintro a b ⟨ha, ha'⟩ ⟨hb, hb'⟩
    refine ⟨?_, ?_⟩
    · rw [Units.val_mul]
      exact ha.mul hb
    · rw [mul_inv_rev, Units.val_mul]
      exact hb'.mul ha'
  inv_mem' := by
    rintro a ⟨ha, ha'⟩
    exact ⟨ha', by rwa [inv_inv]⟩

private noncomputable def IwasawaThree.iwMapF
    (q : ((FiniteAdeleRing (𝓞 ℚ) ℚ × FiniteAdeleRing (𝓞 ℚ) ℚ × FiniteAdeleRing (𝓞 ℚ) ℚ) ×
      (Fin 3 → (FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ)) × IwasawaThree.intGL3f) :
    GL (Fin 3) (FiniteAdeleRing (𝓞 ℚ) ℚ) :=
  upperUnipotent3 q.1.1.1 q.1.1.2.1 q.1.1.2.2 *
    Units.map (Matrix.diagonalRingHom (Fin 3) (FiniteAdeleRing (𝓞 ℚ) ℚ)).toMonoidHom (MulEquiv.piUnits.symm q.1.2) *
    (q.2 : GL (Fin 3) (FiniteAdeleRing (𝓞 ℚ) ℚ))

private noncomputable def IwasawaThree.densF (t : Fin 3 → (FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) : ENNReal :=
  ENNReal.ofReal (((distribHaarChar (FiniteAdeleRing (𝓞 ℚ) ℚ) (t 0) : NNReal) : ℝ)⁻¹ ^ 2 *
    ((distribHaarChar (FiniteAdeleRing (𝓞 ℚ) ℚ) (t 2) : NNReal) : ℝ) ^ 2)

private noncomputable def IwasawaThree.nuF [MeasurableSpace (FiniteAdeleRing (𝓞 ℚ) ℚ)]
    [MeasurableSpace (FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ] [MeasurableSpace (GL (Fin 3) (FiniteAdeleRing (𝓞 ℚ) ℚ))]
    (lam : Measure (FiniteAdeleRing (𝓞 ℚ) ℚ)) (tau : Measure (FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ)
    (kap : Measure IwasawaThree.intGL3f) : Measure (GL (Fin 3) (FiniteAdeleRing (𝓞 ℚ) ℚ)) :=
  Measure.map IwasawaThree.iwMapF
    (((lam.prod (lam.prod lam)).prod
      ((Measure.pi fun _ : Fin 3 => tau).withDensity IwasawaThree.densF)).prod kap)

private theorem IwasawaThree.mem_integralFiniteAdeles_iff (x : FiniteAdeleRing (𝓞 ℚ) ℚ) :
    x ∈ NumberField.AdelicBox.integralFiniteAdeles (𝓞 ℚ) ℚ ↔
      ∀ v : HeightOneSpectrum (𝓞 ℚ), Valued.v (AdelicLevel.finAdeleEval (𝓞 ℚ) ℚ v x) ≤ 1 :=
  Iff.rfl

private noncomputable def IwasawaThree.intSubF : Submonoid (FiniteAdeleRing (𝓞 ℚ) ℚ) where
  carrier := NumberField.AdelicBox.integralFiniteAdeles (𝓞 ℚ) ℚ
  one_mem' := by
    rw [IwasawaThree.mem_integralFiniteAdeles_iff]
    intro v
    rw [map_one, Valuation.map_one]
  mul_mem' := by
    intro a b ha hb
    rw [IwasawaThree.mem_integralFiniteAdeles_iff] at ha hb ⊢
    intro v
    rw [map_mul, Valuation.map_mul]
    exact mul_le_one' (ha v) (hb v)

private theorem IwasawaThree.coe_intSubF :
    (IwasawaThree.intSubF : Set (FiniteAdeleRing (𝓞 ℚ) ℚ)) = NumberField.AdelicBox.integralFiniteAdeles (𝓞 ℚ) ℚ :=
  rfl

private noncomputable def IwasawaThree.intMat3f : Submonoid (Matrix (Fin 3) (Fin 3) (FiniteAdeleRing (𝓞 ℚ) ℚ)) where
  carrier := {M | ∀ i j, M i j ∈ NumberField.AdelicBox.integralFiniteAdeles (𝓞 ℚ) ℚ}
  one_mem' := by
    intro i j
    rw [IwasawaThree.mem_integralFiniteAdeles_iff]
    intro v
    rw [Matrix.one_apply]
    split_ifs
    · rw [map_one, Valuation.map_one]
    · rw [map_zero, Valuation.map_zero]
      exact zero_le'
  mul_mem' := by
    intro a b ha hb i j
    rw [Set.mem_setOf_eq] at ha hb
    rw [IwasawaThree.mem_integralFiniteAdeles_iff]
    intro v
    have h : AdelicLevel.finAdeleEval (𝓞 ℚ) ℚ v ((a * b) i j) =
        ((AdelicLevel.finAdeleEval (𝓞 ℚ) ℚ v).mapMatrix a * (AdelicLevel.finAdeleEval (𝓞 ℚ) ℚ v).mapMatrix b)
          i j := by
      rw [← map_mul]
      rfl
    rw [h]
    exact valued_mul_apply_le3 (𝓞 ℚ) ℚ v (fun l => (ha i l) v) (fun l => (hb l j) v)

private theorem IwasawaThree.mem_intMat3f_iff (M : Matrix (Fin 3) (Fin 3) (FiniteAdeleRing (𝓞 ℚ) ℚ)) :
    M ∈ IwasawaThree.intMat3f ↔ ∀ i j, M i j ∈ NumberField.AdelicBox.integralFiniteAdeles (𝓞 ℚ) ℚ :=
  Iff.rfl

private theorem IwasawaThree.coe_intMat3f_eq_pi :
    (IwasawaThree.intMat3f : Set (Matrix (Fin 3) (Fin 3) (FiniteAdeleRing (𝓞 ℚ) ℚ))) =
      Set.pi Set.univ fun _ => Set.pi Set.univ fun _ => NumberField.AdelicBox.integralFiniteAdeles (𝓞 ℚ) ℚ := by
  ext M
  exact ⟨fun h i _ j _ => h i j, fun h i j => h i (Set.mem_univ i) j (Set.mem_univ j)⟩

private theorem IwasawaThree.isCompact_intMat3f :
    IsCompact (IwasawaThree.intMat3f : Set (Matrix (Fin 3) (Fin 3) (FiniteAdeleRing (𝓞 ℚ) ℚ))) := by
  rw [IwasawaThree.coe_intMat3f_eq_pi]
  exact isCompact_univ_pi fun _ =>
    isCompact_univ_pi fun _ => NumberField.AdelicBox.isCompact_integralFiniteAdeles ℚ

private theorem IwasawaThree.isOpen_intMat3f :
    IsOpen (IwasawaThree.intMat3f : Set (Matrix (Fin 3) (Fin 3) (FiniteAdeleRing (𝓞 ℚ) ℚ))) := by
  rw [IwasawaThree.coe_intMat3f_eq_pi]
  exact isOpen_set_pi Set.finite_univ fun _ _ =>
    isOpen_set_pi Set.finite_univ fun _ _ => NumberField.AdelicBox.isOpen_integralFiniteAdeles ℚ

private theorem IwasawaThree.coe_intGL3f_eq_units :
    (IwasawaThree.intGL3f : Set (GL (Fin 3) (FiniteAdeleRing (𝓞 ℚ) ℚ))) = IwasawaThree.intMat3f.units := by
  ext k
  rw [SetLike.mem_coe, IwasawaThree.mem_intGL3f_iff, SetLike.mem_coe, Submonoid.mem_units_iff,
    IwasawaThree.mem_intMat3f_iff, IwasawaThree.mem_intMat3f_iff]
  constructor
  · intro h
    exact ⟨fun i j v => (h v).1 i j, fun i j v => (h v).2 i j⟩
  · rintro ⟨h₁, h₂⟩ v
    exact ⟨fun i j => (h₁ i j) v, fun i j => (h₂ i j) v⟩

private theorem IwasawaThree.isOpen_units_of_isOpen {M : Type*} [Monoid M] [TopologicalSpace M] [ContinuousMul M]
    {S : Submonoid M} (hS : IsOpen (S : Set M)) : IsOpen (S.units : Set Mˣ) := by
  have h : (S.units : Set Mˣ) = Units.embedProduct M ⁻¹' ((S : Set M) ×ˢ (MulOpposite.unop ⁻¹' (S : Set M))) := by
    ext u
    rw [SetLike.mem_coe, Submonoid.mem_units_iff, Set.mem_preimage, Set.mem_prod, Set.mem_preimage]
    rfl
  rw [h]
  exact (hS.prod (MulOpposite.continuous_unop.isOpen_preimage _ hS)).preimage Units.continuous_embedProduct

private theorem IwasawaThree.isCompact_intGL3f :
    IsCompact (IwasawaThree.intGL3f : Set (GL (Fin 3) (FiniteAdeleRing (𝓞 ℚ) ℚ))) := by
  rw [IwasawaThree.coe_intGL3f_eq_units]
  exact Submonoid.units_isCompact IwasawaThree.isCompact_intMat3f

private theorem IwasawaThree.isOpen_intGL3f
    : IsOpen (IwasawaThree.intGL3f : Set (GL (Fin 3) (FiniteAdeleRing (𝓞 ℚ) ℚ))) := by
  rw [IwasawaThree.coe_intGL3f_eq_units]
  exact IwasawaThree.isOpen_units_of_isOpen IwasawaThree.isOpen_intMat3f

private theorem IwasawaThree.compactSpace_intGL3f : CompactSpace IwasawaThree.intGL3f :=
  isCompact_iff_compactSpace.1 IwasawaThree.isCompact_intGL3f

private noncomputable def IwasawaThree.intUnitsF : Subgroup (FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ :=
  IwasawaThree.intSubF.units

private theorem IwasawaThree.mem_intUnitsF_iff (u : (FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) :
    u ∈ IwasawaThree.intUnitsF ↔ (u : FiniteAdeleRing (𝓞 ℚ) ℚ) ∈ NumberField.AdelicBox.integralFiniteAdeles (𝓞 ℚ) ℚ ∧
      ((u⁻¹ : (FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) : FiniteAdeleRing (𝓞 ℚ) ℚ) ∈
        NumberField.AdelicBox.integralFiniteAdeles (𝓞 ℚ) ℚ :=
  Iff.rfl

private theorem IwasawaThree.isCompact_intUnitsF :
    IsCompact (IwasawaThree.intUnitsF : Set (FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) :=
  Submonoid.units_isCompact (S := IwasawaThree.intSubF) (NumberField.AdelicBox.isCompact_integralFiniteAdeles ℚ)

private theorem IwasawaThree.isOpen_intUnitsF : IsOpen (IwasawaThree.intUnitsF : Set (FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) :=
  IwasawaThree.isOpen_units_of_isOpen (S := IwasawaThree.intSubF) (NumberField.AdelicBox.isOpen_integralFiniteAdeles ℚ)

private noncomputable abbrev IwasawaThree.locF (v : HeightOneSpectrum (𝓞 ℚ)) :
    GL (Fin 3) (FiniteAdeleRing (𝓞 ℚ) ℚ) →* GL (Fin 3) (v.adicCompletion ℚ) :=
  Matrix.GeneralLinearGroup.map (AdelicLevel.finAdeleEval (𝓞 ℚ) ℚ v)

private theorem IwasawaThree.locF_apply (v : HeightOneSpectrum (𝓞 ℚ)) (g : GL (Fin 3) (FiniteAdeleRing (𝓞 ℚ) ℚ))
    (i j : Fin 3) :
    ((IwasawaThree.locF v g : GL (Fin 3) (v.adicCompletion ℚ)) : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ))
      i j = ((g : Matrix (Fin 3) (Fin 3) (FiniteAdeleRing (𝓞 ℚ) ℚ)) i j) v :=
  rfl

private theorem IwasawaThree.locF_inv_apply (v : HeightOneSpectrum (𝓞 ℚ)) (g : GL (Fin 3) (FiniteAdeleRing (𝓞 ℚ) ℚ))
    (i j : Fin 3) :
    (((IwasawaThree.locF v g)⁻¹ : GL (Fin 3) (v.adicCompletion ℚ)) :
        Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) i j =
      (((g⁻¹ : GL (Fin 3) (FiniteAdeleRing (𝓞 ℚ) ℚ)) : Matrix (Fin 3) (Fin 3) (FiniteAdeleRing (𝓞 ℚ) ℚ)) i j) v := by
  rw [← map_inv]
  rfl

private theorem IwasawaThree.eventually_locF_mem (g : GL (Fin 3) (FiniteAdeleRing (𝓞 ℚ) ℚ)) :
    ∀ᶠ v in Filter.cofinite, IwasawaThree.locF v g ∈ localMaximalCompact3 (𝓞 ℚ) ℚ v := by
  have h₁ : ∀ p : Fin 3 × Fin 3, ∀ᶠ v : HeightOneSpectrum (𝓞 ℚ) in Filter.cofinite,
      ((g : Matrix (Fin 3) (Fin 3) (FiniteAdeleRing (𝓞 ℚ) ℚ)) p.1 p.2) v ∈ v.adicCompletionIntegers ℚ :=
    fun p => RestrictedProduct.eventually _ _ ((g : Matrix (Fin 3) (Fin 3) (FiniteAdeleRing (𝓞 ℚ) ℚ)) p.1 p.2)
  have h₂ : ∀ p : Fin 3 × Fin 3, ∀ᶠ v : HeightOneSpectrum (𝓞 ℚ) in Filter.cofinite,
      (((g⁻¹ : GL (Fin 3) (FiniteAdeleRing (𝓞 ℚ) ℚ)) : Matrix (Fin 3) (Fin 3) (FiniteAdeleRing (𝓞 ℚ) ℚ)) p.1 p.2) v ∈
        v.adicCompletionIntegers ℚ :=
    fun p => RestrictedProduct.eventually _ _
      ((((g⁻¹ : GL (Fin 3) (FiniteAdeleRing (𝓞 ℚ) ℚ)) : Matrix (Fin 3) (Fin 3) (FiniteAdeleRing (𝓞 ℚ) ℚ)) p.1 p.2))
  filter_upwards [Filter.eventually_all.2 h₁, Filter.eventually_all.2 h₂] with v hv hv'
  refine ⟨fun i j => ?_, fun i j => ?_⟩
  · rw [IwasawaThree.locF_apply]
    exact hv (i, j)
  · rw [IwasawaThree.locF_inv_apply]
    exact hv' (i, j)

private noncomputable def IwasawaThree.borelPartF
    (g : GL (Fin 3) (FiniteAdeleRing (𝓞 ℚ) ℚ)) (v : HeightOneSpectrum (𝓞 ℚ)) :
    GL (Fin 3) (v.adicCompletion ℚ) := by
  classical
  exact if IwasawaThree.locF v g ∈ localMaximalCompact3 (𝓞 ℚ) ℚ v then 1
    else
      let E := exists_eq_upperUnipotent3_mul_diagonal_mul_mem_localMaximalCompact3 v (IwasawaThree.locF v g)
      upperUnipotent3 E.choose E.choose_spec.choose E.choose_spec.choose_spec.choose *
        E.choose_spec.choose_spec.choose_spec.choose

private theorem IwasawaThree.borelPartF_of_mem {g : GL (Fin 3) (FiniteAdeleRing (𝓞 ℚ) ℚ)} {v : HeightOneSpectrum (𝓞 ℚ)}
    (h : IwasawaThree.locF v g ∈ localMaximalCompact3 (𝓞 ℚ) ℚ v) : IwasawaThree.borelPartF g v = 1 := by
  classical
  rw [IwasawaThree.borelPartF, if_pos h]

private theorem IwasawaThree.borelPartF_spec (g : GL (Fin 3) (FiniteAdeleRing (𝓞 ℚ) ℚ)) (v : HeightOneSpectrum (𝓞 ℚ)) :
    ((IwasawaThree.borelPartF g v : GL (Fin 3) (v.adicCompletion ℚ)) :
        Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)).BlockTriangular id ∧
      (((IwasawaThree.borelPartF g v)⁻¹ : GL (Fin 3) (v.adicCompletion ℚ)) :
        Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)).BlockTriangular id ∧
      (IwasawaThree.borelPartF g v)⁻¹ * IwasawaThree.locF v g ∈ localMaximalCompact3 (𝓞 ℚ) ℚ v := by
  have htri : ∀ b : GL (Fin 3) (v.adicCompletion ℚ),
      (b : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)).BlockTriangular id →
        ((b⁻¹ : GL (Fin 3) (v.adicCompletion ℚ)) : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)).BlockTriangular id :=
    fun b hb => by
      rw [Matrix.coe_units_inv]
      letI := b.invertible
      exact Matrix.blockTriangular_inv_of_blockTriangular hb
  by_cases h : IwasawaThree.locF v g ∈ localMaximalCompact3 (𝓞 ℚ) ℚ v
  · rw [IwasawaThree.borelPartF_of_mem h, inv_one, one_mul, Units.val_one]
    exact ⟨Matrix.blockTriangular_one, Matrix.blockTriangular_one, h⟩
  · set E := exists_eq_upperUnipotent3_mul_diagonal_mul_mem_localMaximalCompact3 v (IwasawaThree.locF v g) with hE
    have hb : IwasawaThree.borelPartF g v =
        upperUnipotent3 E.choose E.choose_spec.choose E.choose_spec.choose_spec.choose *
          E.choose_spec.choose_spec.choose_spec.choose := by
      classical
      rw [IwasawaThree.borelPartF, if_neg h]
    obtain ⟨k, hk, htd, hg⟩ := E.choose_spec.choose_spec.choose_spec.choose_spec.choose_spec
    have hut : ∀ x y z : v.adicCompletion ℚ,
        ((upperUnipotent3 x y z : GL (Fin 3) (v.adicCompletion ℚ)) :
          Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)).BlockTriangular id := by
      intro x y z i j hij
      change !![(1 : v.adicCompletion ℚ), x, z; 0, 1, y; 0, 0, 1] i j = 0
      fin_cases i <;> fin_cases j <;> simp at hij ⊢
    have h1 : ((IwasawaThree.borelPartF g v : GL (Fin 3) (v.adicCompletion ℚ)) :
        Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)).BlockTriangular id := by
      rw [hb, Units.val_mul, htd]
      exact (hut _ _ _).mul (Matrix.blockTriangular_diagonal _)
    refine ⟨h1, htri _ h1, ?_⟩
    have key : ∀ b m k' : GL (Fin 3) (v.adicCompletion ℚ), m = b * k' → b⁻¹ * m = k' :=
      fun b m k' hm => by rw [hm, inv_mul_cancel_left]
    rw [hb, key _ _ _ hg]
    exact hk

private theorem IwasawaThree.eventually_borelPartF_eq_one (g : GL (Fin 3) (FiniteAdeleRing (𝓞 ℚ) ℚ)) :
    ∀ᶠ v in Filter.cofinite, IwasawaThree.borelPartF g v = 1 :=
  (IwasawaThree.eventually_locF_mem g).mono fun _ hv => IwasawaThree.borelPartF_of_mem hv

private theorem IwasawaThree.eventually_borelPartF_apply_mem (g : GL (Fin 3) (FiniteAdeleRing (𝓞 ℚ) ℚ)) (i j : Fin 3) :
    ∀ᶠ v in Filter.cofinite, ((IwasawaThree.borelPartF g v : GL (Fin 3) (v.adicCompletion ℚ)) :
        Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) i j ∈ v.adicCompletionIntegers ℚ := by
  filter_upwards [IwasawaThree.eventually_borelPartF_eq_one g] with v hv
  rw [hv, Units.val_one, Matrix.one_apply]
  split_ifs
  · exact one_mem _
  · exact zero_mem _

private theorem IwasawaThree.eventually_borelPartF_inv_apply_mem
    (g : GL (Fin 3) (FiniteAdeleRing (𝓞 ℚ) ℚ)) (i j : Fin 3) :
    ∀ᶠ v in Filter.cofinite, (((IwasawaThree.borelPartF g v)⁻¹ : GL (Fin 3) (v.adicCompletion ℚ)) :
        Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) i j ∈ v.adicCompletionIntegers ℚ := by
  filter_upwards [IwasawaThree.eventually_borelPartF_eq_one g] with v hv
  rw [hv, inv_one, Units.val_one, Matrix.one_apply]
  split_ifs
  · exact one_mem _
  · exact zero_mem _

private noncomputable def IwasawaThree.borelMatF (g : GL (Fin 3) (FiniteAdeleRing (𝓞 ℚ) ℚ)) :
    Matrix (Fin 3) (Fin 3) (FiniteAdeleRing (𝓞 ℚ) ℚ) :=
  fun i j => RestrictedProduct.mk
    (fun v => ((IwasawaThree.borelPartF g v : GL (Fin 3) (v.adicCompletion ℚ)) :
      Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) i j)
    (IwasawaThree.eventually_borelPartF_apply_mem g i j)

private noncomputable def IwasawaThree.borelMatInvF (g : GL (Fin 3) (FiniteAdeleRing (𝓞 ℚ) ℚ)) :
    Matrix (Fin 3) (Fin 3) (FiniteAdeleRing (𝓞 ℚ) ℚ) :=
  fun i j => RestrictedProduct.mk
    (fun v => (((IwasawaThree.borelPartF g v)⁻¹ : GL (Fin 3) (v.adicCompletion ℚ)) :
      Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) i j)
    (IwasawaThree.eventually_borelPartF_inv_apply_mem g i j)

private theorem IwasawaThree.mapMatrix_borelMatF
    (g : GL (Fin 3) (FiniteAdeleRing (𝓞 ℚ) ℚ)) (v : HeightOneSpectrum (𝓞 ℚ)) :
    (AdelicLevel.finAdeleEval (𝓞 ℚ) ℚ v).mapMatrix (IwasawaThree.borelMatF g) =
      ((IwasawaThree.borelPartF g v : GL (Fin 3) (v.adicCompletion ℚ)) :
        Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) :=
  rfl

private theorem IwasawaThree.mapMatrix_borelMatInvF (g : GL (Fin 3) (FiniteAdeleRing (𝓞 ℚ) ℚ))
    (v : HeightOneSpectrum (𝓞 ℚ)) :
    (AdelicLevel.finAdeleEval (𝓞 ℚ) ℚ v).mapMatrix (IwasawaThree.borelMatInvF g) =
      (((IwasawaThree.borelPartF g v)⁻¹ : GL (Fin 3) (v.adicCompletion ℚ)) :
        Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) :=
  rfl

private theorem IwasawaThree.matrix_ext_finAdeleEval {a b : Matrix (Fin 3) (Fin 3) (FiniteAdeleRing (𝓞 ℚ) ℚ)}
    (h : ∀ v : HeightOneSpectrum (𝓞 ℚ),
      (AdelicLevel.finAdeleEval (𝓞 ℚ) ℚ v).mapMatrix a = (AdelicLevel.finAdeleEval (𝓞 ℚ) ℚ v).mapMatrix b) :
    a = b := by
  refine Matrix.ext fun i j => FiniteAdeleRing.ext (R := 𝓞 ℚ) ℚ fun v => ?_
  exact congrArg (fun M : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ) => M i j) (h v)

private noncomputable def IwasawaThree.borelGLF (g : GL (Fin 3) (FiniteAdeleRing (𝓞 ℚ) ℚ)) :
    GL (Fin 3) (FiniteAdeleRing (𝓞 ℚ) ℚ) where
  val := IwasawaThree.borelMatF g
  inv := IwasawaThree.borelMatInvF g
  val_inv := IwasawaThree.matrix_ext_finAdeleEval fun v => by
    rw [map_mul, map_one, IwasawaThree.mapMatrix_borelMatF, IwasawaThree.mapMatrix_borelMatInvF,
      ← Units.val_mul, mul_inv_cancel, Units.val_one]
  inv_val := IwasawaThree.matrix_ext_finAdeleEval fun v => by
    rw [map_mul, map_one, IwasawaThree.mapMatrix_borelMatF, IwasawaThree.mapMatrix_borelMatInvF,
      ← Units.val_mul, inv_mul_cancel, Units.val_one]

private theorem IwasawaThree.locF_borelGLF (g : GL (Fin 3) (FiniteAdeleRing (𝓞 ℚ) ℚ)) (v : HeightOneSpectrum (𝓞 ℚ)) :
    IwasawaThree.locF v (IwasawaThree.borelGLF g) = IwasawaThree.borelPartF g v :=
  Units.ext (IwasawaThree.mapMatrix_borelMatF g v)

private theorem IwasawaThree.borelGLF_mem (g : GL (Fin 3) (FiniteAdeleRing (𝓞 ℚ) ℚ)) :
    IwasawaThree.borelGLF g ∈ IwasawaThree.upperTriangular3 (FiniteAdeleRing (𝓞 ℚ) ℚ) := by
  constructor
  · intro i j hij
    refine FiniteAdeleRing.ext (R := 𝓞 ℚ) ℚ fun v => ?_
    change ((IwasawaThree.borelPartF g v : GL (Fin 3) (v.adicCompletion ℚ)) :
      Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) i j = (0 : FiniteAdeleRing (𝓞 ℚ) ℚ) v
    rw [(IwasawaThree.borelPartF_spec g v).1 hij]
    rfl
  · intro i j hij
    refine FiniteAdeleRing.ext (R := 𝓞 ℚ) ℚ fun v => ?_
    change (((IwasawaThree.borelPartF g v)⁻¹ : GL (Fin 3) (v.adicCompletion ℚ)) :
      Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) i j = (0 : FiniteAdeleRing (𝓞 ℚ) ℚ) v
    rw [(IwasawaThree.borelPartF_spec g v).2.1 hij]
    rfl

private theorem IwasawaThree.exists_mem_upperTriangular3_inv_mul_mem_intGL3f
    (g : GL (Fin 3) (FiniteAdeleRing (𝓞 ℚ) ℚ)) :
    ∃ b ∈ IwasawaThree.upperTriangular3 (FiniteAdeleRing (𝓞 ℚ) ℚ), b⁻¹ * g ∈ IwasawaThree.intGL3f := by
  refine ⟨IwasawaThree.borelGLF g, IwasawaThree.borelGLF_mem g, ?_⟩
  rw [IwasawaThree.mem_intGL3f_iff]
  intro v
  show IwasawaThree.locF v ((IwasawaThree.borelGLF g)⁻¹ * g) ∈ localMaximalCompact3 (𝓞 ℚ) ℚ v
  rw [map_mul, map_inv, IwasawaThree.locF_borelGLF]
  exact (IwasawaThree.borelPartF_spec g v).2.2

namespace IwasawaThree

private theorem _root_.LanglandsTunnell.CubicInduction.WhittakerBlock.IwasawaThree.continuous_upperUnipotent3
    {A : Type*} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A] :
    Continuous fun p : A × A × A => upperUnipotent3 p.1 p.2.1 p.2.2 := by
  refine Units.continuous_iff.2 ⟨?_, ?_⟩
  · refine continuous_matrix fun i j => ?_
    change Continuous fun p : A × A × A =>
      (!![(1 : A), p.1, p.2.2; 0, 1, p.2.1; 0, 0, 1] : Matrix (Fin 3) (Fin 3) A) i j
    fin_cases i <;> fin_cases j <;> simp <;> fun_prop
  · refine continuous_matrix fun i j => ?_
    change Continuous fun p : A × A × A =>
      (!![(1 : A), -p.1, p.1 * p.2.1 - p.2.2; 0, 1, -p.2.1; 0, 0, 1] : Matrix (Fin 3) (Fin 3) A) i j
    fin_cases i <;> fin_cases j <;> simp <;> fun_prop

end IwasawaThree
p2m_export "LanglandsTunnell.CubicInduction.WhittakerBlock" "IwasawaThree.continuous_upperUnipotent3"

private theorem IwasawaThree.continuous_diagUnits {A : Type*} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A] :
    Continuous fun t : Fin 3 → Aˣ =>
      Units.map (Matrix.diagonalRingHom (Fin 3) A).toMonoidHom (MulEquiv.piUnits.symm t) := by
  refine Units.continuous_iff.2 ⟨?_, ?_⟩
  · show Continuous fun t : Fin 3 → Aˣ => Matrix.diagonal fun i => ((t i : Aˣ) : A)
    exact (continuous_pi fun i => Units.continuous_val.comp (continuous_apply i)).matrix_diagonal
  · show Continuous fun t : Fin 3 → Aˣ => Matrix.diagonal fun i => (((t i)⁻¹ : Aˣ) : A)
    exact (continuous_pi fun i => Units.continuous_coe_inv.comp (continuous_apply i)).matrix_diagonal

namespace IwasawaThree
private theorem _root_.LanglandsTunnell.CubicInduction.WhittakerBlock.IwasawaThree.continuous_iwMapF : Continuous IwasawaThree.iwMapF := by
  have h₁ := IwasawaThree.continuous_upperUnipotent3 (A := FiniteAdeleRing (𝓞 ℚ) ℚ)
  have h₂ := IwasawaThree.continuous_diagUnits (A := FiniteAdeleRing (𝓞 ℚ) ℚ)
  unfold IwasawaThree.iwMapF
  exact ((h₁.comp (continuous_fst.comp continuous_fst)).mul (h₂.comp (continuous_snd.comp continuous_fst))).mul
    (continuous_subtype_val.comp continuous_snd)

end IwasawaThree
p2m_export "LanglandsTunnell.CubicInduction.WhittakerBlock" "IwasawaThree.continuous_iwMapF"
namespace IwasawaThree
private theorem _root_.LanglandsTunnell.CubicInduction.WhittakerBlock.IwasawaThree.measurable_iwMapF [MeasurableSpace (FiniteAdeleRing (𝓞 ℚ) ℚ)]
    [BorelSpace (FiniteAdeleRing (𝓞 ℚ) ℚ)] [MeasurableSpace (FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ]
    [BorelSpace (FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ] [MeasurableSpace (GL (Fin 3) (FiniteAdeleRing (𝓞 ℚ) ℚ))]
    [BorelSpace (GL (Fin 3) (FiniteAdeleRing (𝓞 ℚ) ℚ))] : Measurable IwasawaThree.iwMapF :=
  IwasawaThree.continuous_iwMapF.measurable

end IwasawaThree
p2m_export "LanglandsTunnell.CubicInduction.WhittakerBlock" "IwasawaThree.measurable_iwMapF"

private theorem IwasawaThree.smul_integralFiniteAdeles_eq
    {u : (FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ} (hu : u ∈ IwasawaThree.intUnitsF) :
    (fun x : FiniteAdeleRing (𝓞 ℚ) ℚ => u • x) '' NumberField.AdelicBox.integralFiniteAdeles (𝓞 ℚ) ℚ =
      NumberField.AdelicBox.integralFiniteAdeles (𝓞 ℚ) ℚ := by
  obtain ⟨hu₁, hu₂⟩ := (Submonoid.mem_units_iff _ _).1 hu
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    show (u : FiniteAdeleRing (𝓞 ℚ) ℚ) * y ∈ IwasawaThree.intSubF
    exact IwasawaThree.intSubF.mul_mem hu₁ hy
  · intro hx
    refine ⟨u⁻¹ • x, ?_, smul_inv_smul u x⟩
    show ((u⁻¹ : (FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) : FiniteAdeleRing (𝓞 ℚ) ℚ) * x ∈ IwasawaThree.intSubF
    exact IwasawaThree.intSubF.mul_mem hu₂ hx

private noncomputable def IwasawaThree.intPositiveCompactsF
    : TopologicalSpace.PositiveCompacts (FiniteAdeleRing (𝓞 ℚ) ℚ) where
  carrier := NumberField.AdelicBox.integralFiniteAdeles (𝓞 ℚ) ℚ
  isCompact' := NumberField.AdelicBox.isCompact_integralFiniteAdeles ℚ
  interior_nonempty' := by
    rw [(NumberField.AdelicBox.isOpen_integralFiniteAdeles ℚ).interior_eq]
    exact ⟨0, fun v => zero_mem _⟩

private theorem IwasawaThree.distribHaarChar_eq_one_of_mem_intUnitsF {u : (FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ}
    (hu : u ∈ IwasawaThree.intUnitsF) : distribHaarChar (FiniteAdeleRing (𝓞 ℚ) ℚ) u = 1 := by
  letI : MeasurableSpace (FiniteAdeleRing (𝓞 ℚ) ℚ) := borel _
  haveI : BorelSpace (FiniteAdeleRing (𝓞 ℚ) ℚ) := ⟨rfl⟩
  have hμ : Measure.addHaarMeasure IwasawaThree.intPositiveCompactsF
      (NumberField.AdelicBox.integralFiniteAdeles (𝓞 ℚ) ℚ) = 1 :=
    Measure.addHaarMeasure_self
  have h : ((distribHaarChar (FiniteAdeleRing (𝓞 ℚ) ℚ) u : NNReal) : ENNReal) *
      Measure.addHaarMeasure IwasawaThree.intPositiveCompactsF (NumberField.AdelicBox.integralFiniteAdeles (𝓞 ℚ) ℚ) =
        Measure.addHaarMeasure IwasawaThree.intPositiveCompactsF
          ((fun x : FiniteAdeleRing (𝓞 ℚ) ℚ => u • x) '' NumberField.AdelicBox.integralFiniteAdeles (𝓞 ℚ) ℚ) :=
    distribHaarChar_mul _ u _
  rw [IwasawaThree.smul_integralFiniteAdeles_eq hu, hμ, mul_one] at h
  exact ENNReal.coe_eq_one.1 h

private theorem IwasawaThree.continuous_distribHaarChar_finiteAdele :
    Continuous fun u : (FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ => distribHaarChar (FiniteAdeleRing (𝓞 ℚ) ℚ) u := by
  refine IsLocallyConstant.continuous ((IsLocallyConstant.iff_exists_open _).2 fun u => ?_)
  refine ⟨(fun w => u * w) '' (IwasawaThree.intUnitsF : Set (FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ),
    isOpenMap_mul_left u _ IwasawaThree.isOpen_intUnitsF, ⟨1, one_mem _, mul_one u⟩, ?_⟩
  rintro _ ⟨w, hw, rfl⟩
  rw [map_mul, IwasawaThree.distribHaarChar_eq_one_of_mem_intUnitsF hw, mul_one]

private theorem IwasawaThree.continuous_densF : Continuous IwasawaThree.densF := by
  have hc : ∀ i : Fin 3, Continuous fun t : Fin 3 → (FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ =>
      ((distribHaarChar (FiniteAdeleRing (𝓞 ℚ) ℚ) (t i) : NNReal) : ℝ) := fun i =>
    NNReal.continuous_coe.comp (IwasawaThree.continuous_distribHaarChar_finiteAdele.comp (continuous_apply i))
  have h0 : ∀ t : Fin 3 → (FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ,
      ((distribHaarChar (FiniteAdeleRing (𝓞 ℚ) ℚ) (t 0) : NNReal) : ℝ) ≠ 0 := fun t =>
    (NNReal.coe_pos.2 distribHaarChar_pos).ne'
  unfold IwasawaThree.densF
  exact ENNReal.continuous_ofReal.comp ((((hc 0).inv₀ h0).pow 2).mul ((hc 2).pow 2))

private theorem IwasawaThree.measurable_densF [MeasurableSpace (FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ]
    [BorelSpace (FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ] : Measurable IwasawaThree.densF :=
  IwasawaThree.continuous_densF.measurable

private noncomputable abbrev IwasawaThree.Unipotent.addHaarA :
    @Measure (AdeleRing (𝓞 ℚ) ℚ) (NumberField.AdelicHaar.adeleBorel (𝓞 ℚ) ℚ) :=
  NumberField.AdelicHaar.adelicAddHaar (𝓞 ℚ) ℚ

private noncomputable def IwasawaThree.Unipotent.unip (x y z : AdeleRing (𝓞 ℚ) ℚ) :
    WhittakerBlock.unipotentSubgroup3 :=
  ⟨upperUnipotent3 x y z, (WhittakerBlock.mem_unipotentSubgroup3_iff _).2 ⟨x, y, z, rfl⟩⟩

private theorem IwasawaThree.Unipotent.unip_mul (x y z x' y' z' : AdeleRing (𝓞 ℚ) ℚ) :
    unip x y z * unip x' y' z' = unip (x + x') (y + y') (z + z' + x * y') := by
  apply Subtype.ext
  show upperUnipotent3 x y z * upperUnipotent3 x' y' z' = upperUnipotent3 _ _ _
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [upperUnipotent3, Units.val_mul, Matrix.mul_apply, Fin.sum_univ_three]
  all_goals ring

private theorem IwasawaThree.Unipotent.surjective_unip :
    Function.Surjective (fun p : AdeleRing (𝓞 ℚ) ℚ × AdeleRing (𝓞 ℚ) ℚ × AdeleRing (𝓞 ℚ) ℚ =>
      unip p.1 p.2.1 p.2.2) := by
  rintro ⟨g, hg⟩
  obtain ⟨x, y, z, rfl⟩ := (WhittakerBlock.mem_unipotentSubgroup3_iff g).1 hg
  exact ⟨(x, y, z), rfl⟩

private theorem IwasawaThree.Unipotent.coe_diagGL (t : Fin 3 → (AdeleRing (𝓞 ℚ) ℚ)ˣ) :
    ((IwasawaThree.diagGL t : AdelicGL 3 (𝓞 ℚ) ℚ) : Matrix (Fin 3) (Fin 3) (AdeleRing (𝓞 ℚ) ℚ)) =
      Matrix.diagonal fun i => (t i : AdeleRing (𝓞 ℚ) ℚ) := rfl

private theorem IwasawaThree.Unipotent.coe_diagGL_inv (t : Fin 3 → (AdeleRing (𝓞 ℚ) ℚ)ˣ) :
    (((IwasawaThree.diagGL t : AdelicGL 3 (𝓞 ℚ) ℚ)⁻¹ : AdelicGL 3 (𝓞 ℚ) ℚ) :
        Matrix (Fin 3) (Fin 3) (AdeleRing (𝓞 ℚ) ℚ)) =
      Matrix.diagonal fun i => (((t i)⁻¹ : (AdeleRing (𝓞 ℚ) ℚ)ˣ) : AdeleRing (𝓞 ℚ) ℚ) := by
  rw [← map_inv]
  rfl

private theorem IwasawaThree.Unipotent.diagGL_mul_unip_mul_inv (t : Fin 3 → (AdeleRing (𝓞 ℚ) ℚ)ˣ)
    (x y z : AdeleRing (𝓞 ℚ) ℚ) :
    IwasawaThree.diagGL t * (unip x y z : AdelicGL 3 (𝓞 ℚ) ℚ) * (IwasawaThree.diagGL t)⁻¹ =
      unip (((t 0 * (t 1)⁻¹ : (AdeleRing (𝓞 ℚ) ℚ)ˣ) : AdeleRing (𝓞 ℚ) ℚ) * x)
        (((t 1 * (t 2)⁻¹ : (AdeleRing (𝓞 ℚ) ℚ)ˣ) : AdeleRing (𝓞 ℚ) ℚ) * y)
        (((t 0 * (t 2)⁻¹ : (AdeleRing (𝓞 ℚ) ℚ)ˣ) : AdeleRing (𝓞 ℚ) ℚ) * z) := by
  apply Units.ext
  rw [Units.val_mul, Units.val_mul, coe_diagGL, coe_diagGL_inv]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [unip, upperUnipotent3, Matrix.mul_apply, Matrix.diagonal, Units.val_mul] <;>
    ring

private theorem IwasawaThree.Unipotent.diagGL_mul_mem (t : Fin 3 → (AdeleRing (𝓞 ℚ) ℚ)ˣ)
    (n : WhittakerBlock.unipotentSubgroup3) :
    IwasawaThree.diagGL t * (n : AdelicGL 3 (𝓞 ℚ) ℚ) * (IwasawaThree.diagGL t)⁻¹ ∈
      WhittakerBlock.unipotentSubgroup3 := by
  obtain ⟨⟨x, y, z⟩, rfl⟩ := surjective_unip n
  rw [diagGL_mul_unip_mul_inv]
  exact (unip _ _ _).2

private noncomputable def IwasawaThree.Unipotent.conj (t : Fin 3 → (AdeleRing (𝓞 ℚ) ℚ)ˣ)
    (n : WhittakerBlock.unipotentSubgroup3) : WhittakerBlock.unipotentSubgroup3 :=
  ⟨IwasawaThree.diagGL t * (n : AdelicGL 3 (𝓞 ℚ) ℚ) * (IwasawaThree.diagGL t)⁻¹, diagGL_mul_mem t n⟩

private theorem IwasawaThree.Unipotent.conj_unip (t : Fin 3 → (AdeleRing (𝓞 ℚ) ℚ)ˣ) (x y z : AdeleRing (𝓞 ℚ) ℚ) :
    conj t (unip x y z) =
      unip (((t 0 * (t 1)⁻¹ : (AdeleRing (𝓞 ℚ) ℚ)ˣ) : AdeleRing (𝓞 ℚ) ℚ) * x)
        (((t 1 * (t 2)⁻¹ : (AdeleRing (𝓞 ℚ) ℚ)ˣ) : AdeleRing (𝓞 ℚ) ℚ) * y)
        (((t 0 * (t 2)⁻¹ : (AdeleRing (𝓞 ℚ) ℚ)ˣ) : AdeleRing (𝓞 ℚ) ℚ) * z) :=
  Subtype.ext (diagGL_mul_unip_mul_inv t x y z)

private theorem IwasawaThree.Unipotent.continuous_unip :
    Continuous (fun p : AdeleRing (𝓞 ℚ) ℚ × AdeleRing (𝓞 ℚ) ℚ × AdeleRing (𝓞 ℚ) ℚ => unip p.1 p.2.1 p.2.2) := by
  refine Continuous.subtype_mk ?_ _
  refine Units.continuous_iff.2 ⟨?_, ?_⟩
  · refine continuous_pi fun i => continuous_pi fun j => ?_
    fin_cases i <;> fin_cases j <;> simp [upperUnipotent3] <;> fun_prop
  · have h : ∀ x y z : AdeleRing (𝓞 ℚ) ℚ,
        (((upperUnipotent3 x y z)⁻¹ : GL (Fin 3) (AdeleRing (𝓞 ℚ) ℚ)) :
            Matrix (Fin 3) (Fin 3) (AdeleRing (𝓞 ℚ) ℚ)) =
          !![1, -x, x * y - z; 0, 1, -y; 0, 0, 1] := by
      intro x y z
      have hmul : upperUnipotent3 x y z * upperUnipotent3 (-x) (-y) (x * y - z) = 1 := by
        ext i j
        fin_cases i <;> fin_cases j <;> simp [upperUnipotent3, Units.val_mul, Matrix.mul_apply, Fin.sum_univ_three]
        ring
      rw [inv_eq_of_mul_eq_one_right hmul]
      rfl
    have h' : (fun p : AdeleRing (𝓞 ℚ) ℚ × AdeleRing (𝓞 ℚ) ℚ × AdeleRing (𝓞 ℚ) ℚ =>
        (((upperUnipotent3 p.1 p.2.1 p.2.2)⁻¹ : GL (Fin 3) (AdeleRing (𝓞 ℚ) ℚ)) :
          Matrix (Fin 3) (Fin 3) (AdeleRing (𝓞 ℚ) ℚ))) =
        fun p => !![1, -p.1, p.1 * p.2.1 - p.2.2; 0, 1, -p.2.1; 0, 0, 1] :=
      funext fun p => h p.1 p.2.1 p.2.2
    rw [h']
    refine continuous_pi fun i => continuous_pi fun j => ?_
    fin_cases i <;> fin_cases j <;> simp <;> fun_prop

private theorem IwasawaThree.Unipotent.measurable_unip :
    letI : MeasurableSpace (AdeleRing (𝓞 ℚ) ℚ) := NumberField.AdelicHaar.adeleBorel (𝓞 ℚ) ℚ
    letI : MeasurableSpace (AdelicGL 3 (𝓞 ℚ) ℚ) := NumberField.AdelicHaar.glBorel (Fin 3) (𝓞 ℚ) ℚ
    Measurable (fun p : AdeleRing (𝓞 ℚ) ℚ × AdeleRing (𝓞 ℚ) ℚ × AdeleRing (𝓞 ℚ) ℚ => unip p.1 p.2.1 p.2.2) := by
  letI : MeasurableSpace (AdeleRing (𝓞 ℚ) ℚ) := NumberField.AdelicHaar.adeleBorel (𝓞 ℚ) ℚ
  letI : MeasurableSpace (AdelicGL 3 (𝓞 ℚ) ℚ) := NumberField.AdelicHaar.glBorel (Fin 3) (𝓞 ℚ) ℚ
  haveI := NumberField.AdelicHaar.borelSpace_adeleBorel (𝓞 ℚ) ℚ
  haveI := NumberField.AdelicHaar.borelSpace_glBorel (Fin 3) (𝓞 ℚ) ℚ
  exact continuous_unip.measurable

private theorem IwasawaThree.Unipotent.measurable_conj (t : Fin 3 → (AdeleRing (𝓞 ℚ) ℚ)ˣ) :
    letI : MeasurableSpace (AdelicGL 3 (𝓞 ℚ) ℚ) := NumberField.AdelicHaar.glBorel (Fin 3) (𝓞 ℚ) ℚ
    Measurable (conj t) := by
  letI : MeasurableSpace (AdelicGL 3 (𝓞 ℚ) ℚ) := NumberField.AdelicHaar.glBorel (Fin 3) (𝓞 ℚ) ℚ
  haveI := NumberField.AdelicHaar.borelSpace_glBorel (Fin 3) (𝓞 ℚ) ℚ
  exact ((continuous_const.mul continuous_subtype_val).mul continuous_const).measurable.subtype_mk

private theorem IwasawaThree.Unipotent.unipotentHaar3_eq :
    letI : MeasurableSpace (AdeleRing (𝓞 ℚ) ℚ) := NumberField.AdelicHaar.adeleBorel (𝓞 ℚ) ℚ
    letI : MeasurableSpace (AdelicGL 3 (𝓞 ℚ) ℚ) := NumberField.AdelicHaar.glBorel (Fin 3) (𝓞 ℚ) ℚ
    WhittakerBlock.unipotentHaar3 =
      Measure.map (fun p : AdeleRing (𝓞 ℚ) ℚ × AdeleRing (𝓞 ℚ) ℚ × AdeleRing (𝓞 ℚ) ℚ => unip p.1 p.2.1 p.2.2)
        (addHaarA.prod (addHaarA.prod addHaarA)) := rfl

private theorem IwasawaThree.Unipotent.measurable_unip_section (x : AdeleRing (𝓞 ℚ) ℚ) :
    letI : MeasurableSpace (AdeleRing (𝓞 ℚ) ℚ) := NumberField.AdelicHaar.adeleBorel (𝓞 ℚ) ℚ
    letI : MeasurableSpace (AdelicGL 3 (𝓞 ℚ) ℚ) := NumberField.AdelicHaar.glBorel (Fin 3) (𝓞 ℚ) ℚ
    Measurable (fun q : AdeleRing (𝓞 ℚ) ℚ × AdeleRing (𝓞 ℚ) ℚ => unip x q.1 q.2) :=
  letI : MeasurableSpace (AdeleRing (𝓞 ℚ) ℚ) := NumberField.AdelicHaar.adeleBorel (𝓞 ℚ) ℚ
  letI : MeasurableSpace (AdelicGL 3 (𝓞 ℚ) ℚ) := NumberField.AdelicHaar.glBorel (Fin 3) (𝓞 ℚ) ℚ
  measurable_unip.comp (measurable_prodMk_left (x := x))

private theorem IwasawaThree.Unipotent.lintegral_unipotentHaar3_eq_lintegral_prod
    (f : WhittakerBlock.unipotentSubgroup3 → ℝ≥0∞) :
    letI : MeasurableSpace (AdeleRing (𝓞 ℚ) ℚ) := NumberField.AdelicHaar.adeleBorel (𝓞 ℚ) ℚ
    letI : MeasurableSpace (AdelicGL 3 (𝓞 ℚ) ℚ) := NumberField.AdelicHaar.glBorel (Fin 3) (𝓞 ℚ) ℚ
    Measurable f →
      ∫⁻ n, f n ∂WhittakerBlock.unipotentHaar3 =
        ∫⁻ p : AdeleRing (𝓞 ℚ) ℚ × AdeleRing (𝓞 ℚ) ℚ × AdeleRing (𝓞 ℚ) ℚ, f (unip p.1 p.2.1 p.2.2)
          ∂(addHaarA.prod (addHaarA.prod addHaarA)) := by
  intro hf
  letI : MeasurableSpace (AdeleRing (𝓞 ℚ) ℚ) := NumberField.AdelicHaar.adeleBorel (𝓞 ℚ) ℚ
  letI : MeasurableSpace (AdelicGL 3 (𝓞 ℚ) ℚ) := NumberField.AdelicHaar.glBorel (Fin 3) (𝓞 ℚ) ℚ
  rw [unipotentHaar3_eq]
  exact lintegral_map hf measurable_unip

private theorem IwasawaThree.Unipotent.lintegral_unipotentHaar3 (f : WhittakerBlock.unipotentSubgroup3 → ℝ≥0∞) :
    letI : MeasurableSpace (AdeleRing (𝓞 ℚ) ℚ) := NumberField.AdelicHaar.adeleBorel (𝓞 ℚ) ℚ
    letI : MeasurableSpace (AdelicGL 3 (𝓞 ℚ) ℚ) := NumberField.AdelicHaar.glBorel (Fin 3) (𝓞 ℚ) ℚ
    Measurable f →
      ∫⁻ n, f n ∂WhittakerBlock.unipotentHaar3 = ∫⁻ x, ∫⁻ y, ∫⁻ z, f (unip x y z) ∂addHaarA ∂addHaarA ∂addHaarA := by
  intro hf
  letI : MeasurableSpace (AdeleRing (𝓞 ℚ) ℚ) := NumberField.AdelicHaar.adeleBorel (𝓞 ℚ) ℚ
  letI : MeasurableSpace (AdelicGL 3 (𝓞 ℚ) ℚ) := NumberField.AdelicHaar.glBorel (Fin 3) (𝓞 ℚ) ℚ
  haveI := NumberField.AdelicHaar.isAddHaarMeasure_adelicAddHaar (𝓞 ℚ) ℚ
  haveI : SigmaFinite addHaarA := sigmaFinite_of_locallyFinite
  have h₁ : ∫⁻ p : AdeleRing (𝓞 ℚ) ℚ × AdeleRing (𝓞 ℚ) ℚ × AdeleRing (𝓞 ℚ) ℚ, f (unip p.1 p.2.1 p.2.2)
        ∂(addHaarA.prod (addHaarA.prod addHaarA)) =
      ∫⁻ x, ∫⁻ q : AdeleRing (𝓞 ℚ) ℚ × AdeleRing (𝓞 ℚ) ℚ, f (unip x q.1 q.2) ∂(addHaarA.prod addHaarA) ∂addHaarA :=
    lintegral_prod (fun p : AdeleRing (𝓞 ℚ) ℚ × AdeleRing (𝓞 ℚ) ℚ × AdeleRing (𝓞 ℚ) ℚ => f (unip p.1 p.2.1 p.2.2))
      (hf.comp measurable_unip).aemeasurable
  have h₂ : ∀ x : AdeleRing (𝓞 ℚ) ℚ,
      ∫⁻ q : AdeleRing (𝓞 ℚ) ℚ × AdeleRing (𝓞 ℚ) ℚ, f (unip x q.1 q.2) ∂(addHaarA.prod addHaarA) =
        ∫⁻ y, ∫⁻ z, f (unip x y z) ∂addHaarA ∂addHaarA :=
    fun x => lintegral_prod (fun q : AdeleRing (𝓞 ℚ) ℚ × AdeleRing (𝓞 ℚ) ℚ => f (unip x q.1 q.2))
      (hf.comp (measurable_unip_section x)).aemeasurable
  rw [lintegral_unipotentHaar3_eq_lintegral_prod f hf, h₁]
  exact lintegral_congr h₂

private noncomputable def IwasawaThree.Unipotent.mulEquiv (a : (AdeleRing (𝓞 ℚ) ℚ)ˣ) :
    letI : MeasurableSpace (AdeleRing (𝓞 ℚ) ℚ) := NumberField.AdelicHaar.adeleBorel (𝓞 ℚ) ℚ
    AdeleRing (𝓞 ℚ) ℚ ≃ᵐ AdeleRing (𝓞 ℚ) ℚ :=
  letI : MeasurableSpace (AdeleRing (𝓞 ℚ) ℚ) := NumberField.AdelicHaar.adeleBorel (𝓞 ℚ) ℚ
  haveI := NumberField.AdelicHaar.borelSpace_adeleBorel (𝓞 ℚ) ℚ
  { toEquiv := MulAction.toPerm a
    measurable_toFun := (continuous_const.mul continuous_id).measurable
    measurable_invFun := (continuous_const.mul continuous_id).measurable }

private theorem IwasawaThree.Unipotent.map_mulEquiv (a : (AdeleRing (𝓞 ℚ) ℚ)ˣ) :
    letI : MeasurableSpace (AdeleRing (𝓞 ℚ) ℚ) := NumberField.AdelicHaar.adeleBorel (𝓞 ℚ) ℚ
    Measure.map (mulEquiv a) addHaarA =
      (((distribHaarChar (AdeleRing (𝓞 ℚ) ℚ) a)⁻¹ : NNReal) : ENNReal) • addHaarA := by
  letI : MeasurableSpace (AdeleRing (𝓞 ℚ) ℚ) := NumberField.AdelicHaar.adeleBorel (𝓞 ℚ) ℚ
  haveI := NumberField.AdelicHaar.borelSpace_adeleBorel (𝓞 ℚ) ℚ
  haveI := NumberField.AdelicHaar.isAddHaarMeasure_adelicAddHaar (𝓞 ℚ) ℚ
  haveI := IwasawaThree.regular_adelicAddHaar
  ext s -
  rw [MeasurableEquiv.map_apply, Measure.smul_apply, smul_eq_mul, ← map_inv, distribHaarChar_mul]
  congr 1
  exact Set.preimage_smul a s

private theorem IwasawaThree.Unipotent.lintegral_unit_mul (a : (AdeleRing (𝓞 ℚ) ℚ)ˣ) (g : AdeleRing (𝓞 ℚ) ℚ → ℝ≥0∞) :
    letI : MeasurableSpace (AdeleRing (𝓞 ℚ) ℚ) := NumberField.AdelicHaar.adeleBorel (𝓞 ℚ) ℚ
    ∫⁻ x, g ((a : AdeleRing (𝓞 ℚ) ℚ) * x) ∂addHaarA =
      (((distribHaarChar (AdeleRing (𝓞 ℚ) ℚ) a)⁻¹ : NNReal) : ℝ≥0∞) * ∫⁻ x, g x ∂addHaarA := by
  letI : MeasurableSpace (AdeleRing (𝓞 ℚ) ℚ) := NumberField.AdelicHaar.adeleBorel (𝓞 ℚ) ℚ
  have h := lintegral_map_equiv (μ := addHaarA) g (mulEquiv a)
  rw [map_mulEquiv, lintegral_smul_measure] at h
  exact h.symm

private theorem IwasawaThree.Unipotent.ofReal_density_eq (t : Fin 3 → (AdeleRing (𝓞 ℚ) ℚ)ˣ) :
    ENNReal.ofReal ((NumberField.TateGlobal.ideleNorm ℚ (t 0))⁻¹ ^ 2 * NumberField.TateGlobal.ideleNorm ℚ (t 2) ^ 2) =
      (((distribHaarChar (AdeleRing (𝓞 ℚ) ℚ) (t 0 * (t 1)⁻¹))⁻¹ : NNReal) : ℝ≥0∞) *
        ((((distribHaarChar (AdeleRing (𝓞 ℚ) ℚ) (t 1 * (t 2)⁻¹))⁻¹ : NNReal) : ℝ≥0∞) *
          (((distribHaarChar (AdeleRing (𝓞 ℚ) ℚ) (t 0 * (t 2)⁻¹))⁻¹ : NNReal) : ℝ≥0∞)) := by
  have h0 : ((distribHaarChar (AdeleRing (𝓞 ℚ) ℚ) (t 0) : NNReal) : ℝ) ≠ 0 :=
    (NNReal.coe_pos.2 distribHaarChar_pos).ne'
  have h1 : ((distribHaarChar (AdeleRing (𝓞 ℚ) ℚ) (t 1) : NNReal) : ℝ) ≠ 0 :=
    (NNReal.coe_pos.2 distribHaarChar_pos).ne'
  have h2 : ((distribHaarChar (AdeleRing (𝓞 ℚ) ℚ) (t 2) : NNReal) : ℝ) ≠ 0 :=
    (NNReal.coe_pos.2 distribHaarChar_pos).ne'
  rw [← ENNReal.coe_mul, ← ENNReal.coe_mul, NumberField.TateGlobal.ideleNorm, NumberField.TateGlobal.ideleNorm,
    ← NNReal.coe_inv, ← NNReal.coe_pow, ← NNReal.coe_pow, ← NNReal.coe_mul, ENNReal.ofReal_coe_nnreal]
  congr 1
  rw [← NNReal.coe_inj]
  simp only [map_mul, map_inv, NNReal.coe_mul, NNReal.coe_inv, NNReal.coe_pow]
  field_simp

private theorem IwasawaThree.Unipotent.lintegral_conj (t : Fin 3 → (AdeleRing (𝓞 ℚ) ℚ)ˣ)
    (f : WhittakerBlock.unipotentSubgroup3 → ℝ≥0∞) :
    letI : MeasurableSpace (AdelicGL 3 (𝓞 ℚ) ℚ) := NumberField.AdelicHaar.glBorel (Fin 3) (𝓞 ℚ) ℚ
    Measurable f →
      ∫⁻ n, f (conj t n) ∂WhittakerBlock.unipotentHaar3 =
        ENNReal.ofReal ((NumberField.TateGlobal.ideleNorm ℚ (t 0))⁻¹ ^ 2 *
            NumberField.TateGlobal.ideleNorm ℚ (t 2) ^ 2) *
          ∫⁻ n, f n ∂WhittakerBlock.unipotentHaar3 := by
  intro hf
  letI : MeasurableSpace (AdelicGL 3 (𝓞 ℚ) ℚ) := NumberField.AdelicHaar.glBorel (Fin 3) (𝓞 ℚ) ℚ
  rw [lintegral_unipotentHaar3 (fun n => f (conj t n)) (hf.comp (measurable_conj t)), lintegral_unipotentHaar3 f hf]
  simp only [conj_unip]
  have hz : ∀ x y : AdeleRing (𝓞 ℚ) ℚ,
      ∫⁻ z, f (unip x y (((t 0 * (t 2)⁻¹ : (AdeleRing (𝓞 ℚ) ℚ)ˣ) : AdeleRing (𝓞 ℚ) ℚ) * z)) ∂addHaarA =
        (((distribHaarChar (AdeleRing (𝓞 ℚ) ℚ) (t 0 * (t 2)⁻¹))⁻¹ : NNReal) : ℝ≥0∞) *
          ∫⁻ z, f (unip x y z) ∂addHaarA :=
    fun x y => lintegral_unit_mul _ fun w => f (unip x y w)
  have hy : ∀ x : AdeleRing (𝓞 ℚ) ℚ,
      ∫⁻ y, ∫⁻ z, f (unip x (((t 1 * (t 2)⁻¹ : (AdeleRing (𝓞 ℚ) ℚ)ˣ) : AdeleRing (𝓞 ℚ) ℚ) * y) z) ∂addHaarA
          ∂addHaarA =
        (((distribHaarChar (AdeleRing (𝓞 ℚ) ℚ) (t 1 * (t 2)⁻¹))⁻¹ : NNReal) : ℝ≥0∞) *
          ∫⁻ y, ∫⁻ z, f (unip x y z) ∂addHaarA ∂addHaarA :=
    fun x => lintegral_unit_mul _ fun w => ∫⁻ z, f (unip x w z) ∂addHaarA
  have hx :
      ∫⁻ x, ∫⁻ y, ∫⁻ z, f (unip (((t 0 * (t 1)⁻¹ : (AdeleRing (𝓞 ℚ) ℚ)ˣ) : AdeleRing (𝓞 ℚ) ℚ) * x) y z)
          ∂addHaarA ∂addHaarA ∂addHaarA =
        (((distribHaarChar (AdeleRing (𝓞 ℚ) ℚ) (t 0 * (t 1)⁻¹))⁻¹ : NNReal) : ℝ≥0∞) *
          ∫⁻ x, ∫⁻ y, ∫⁻ z, f (unip x y z) ∂addHaarA ∂addHaarA ∂addHaarA :=
    lintegral_unit_mul _ fun w => ∫⁻ y, ∫⁻ z, f (unip w y z) ∂addHaarA ∂addHaarA
  simp only [hz, lintegral_const_mul' _ _ ENNReal.coe_ne_top, hy]
  rw [hx, ofReal_density_eq]
  ring

private noncomputable def IwasawaThree.Torus.posExp (s : ℝ) : ℝˣ := Units.mk0 (Real.exp s) (Real.exp_pos s).ne'

private noncomputable def IwasawaThree.Torus.negExp (s : ℝ) : ℝˣ := -IwasawaThree.Torus.posExp s

private noncomputable def IwasawaThree.Torus.logAbs (t : ℝˣ) : ℝ := Real.log |(t : ℝ)|

private theorem IwasawaThree.Torus.val_posExp (s : ℝ) : ((IwasawaThree.Torus.posExp s : ℝˣ) : ℝ) = Real.exp s := rfl

private theorem IwasawaThree.Torus.continuous_posExp : Continuous IwasawaThree.Torus.posExp := by
  refine Units.continuous_iff.2 ⟨Real.continuous_exp, ?_⟩
  show Continuous fun s : ℝ => (Real.exp s)⁻¹
  exact Real.continuous_exp.inv₀ fun s => (Real.exp_pos s).ne'

private theorem IwasawaThree.Torus.continuous_negExp : Continuous IwasawaThree.Torus.negExp := by
  refine Units.continuous_iff.2 ⟨?_, ?_⟩
  · show Continuous fun s : ℝ => -Real.exp s
    exact Real.continuous_exp.neg
  · show Continuous fun s : ℝ => -(Real.exp s)⁻¹
    exact (Real.continuous_exp.inv₀ fun s => (Real.exp_pos s).ne').neg

private theorem IwasawaThree.Torus.continuous_logAbs : Continuous IwasawaThree.Torus.logAbs := by
  show Continuous fun t : ℝˣ => Real.log |(t : ℝ)|
  exact (continuous_abs.comp Units.continuous_val).log fun t => abs_ne_zero.2 t.ne_zero

private theorem IwasawaThree.Torus.logAbs_mul (u t : ℝˣ) :
    IwasawaThree.Torus.logAbs (u * t) = IwasawaThree.Torus.logAbs u + IwasawaThree.Torus.logAbs t := by
  unfold IwasawaThree.Torus.logAbs
  rw [Units.val_mul, abs_mul, Real.log_mul (abs_ne_zero.2 u.ne_zero) (abs_ne_zero.2 t.ne_zero)]

private theorem IwasawaThree.Torus.logAbs_posExp (s : ℝ) :
    IwasawaThree.Torus.logAbs (IwasawaThree.Torus.posExp s) = s := by
  unfold IwasawaThree.Torus.logAbs
  rw [IwasawaThree.Torus.val_posExp, abs_of_pos (Real.exp_pos s), Real.log_exp]

private theorem IwasawaThree.Torus.eq_posExp_or_eq_negExp (t : ℝˣ) :
    t = IwasawaThree.Torus.posExp (IwasawaThree.Torus.logAbs t) ∨
      t = IwasawaThree.Torus.negExp (IwasawaThree.Torus.logAbs t) := by
  have habs : Real.exp (IwasawaThree.Torus.logAbs t) = |(t : ℝ)| :=
    Real.exp_log (abs_pos.2 t.ne_zero)
  rcases lt_or_gt_of_ne t.ne_zero with hneg | hpos
  · right
    apply Units.ext
    show (t : ℝ) = -Real.exp (IwasawaThree.Torus.logAbs t)
    rw [habs, abs_of_neg hneg, neg_neg]
  · left
    apply Units.ext
    show (t : ℝ) = Real.exp (IwasawaThree.Torus.logAbs t)
    rw [habs, abs_of_pos hpos]

private theorem IwasawaThree.Torus.preimage_logAbs_subset (K : Set ℝ) :
    IwasawaThree.Torus.logAbs ⁻¹' K ⊆
      IwasawaThree.Torus.posExp '' K ∪ IwasawaThree.Torus.negExp '' K := by
  intro t ht
  rcases IwasawaThree.Torus.eq_posExp_or_eq_negExp t with h | h
  · exact Or.inl ⟨_, ht, h.symm⟩
  · exact Or.inr ⟨_, ht, h.symm⟩

private theorem IwasawaThree.Torus.isAddHaarMeasure_map_logAbs [MeasurableSpace ℝˣ] [BorelSpace ℝˣ]
    (tau : Measure ℝˣ) [tau.IsHaarMeasure] :
    (Measure.map IwasawaThree.Torus.logAbs tau).IsAddHaarMeasure :=
  { toIsAddLeftInvariant := ⟨fun r => by
      rw [Measure.map_map (measurable_const_add r) IwasawaThree.Torus.continuous_logAbs.measurable]
      have h : (fun x : ℝ => r + x) ∘ IwasawaThree.Torus.logAbs =
          IwasawaThree.Torus.logAbs ∘ fun t : ℝˣ => IwasawaThree.Torus.posExp r * t := by
        funext t
        simp only [Function.comp, IwasawaThree.Torus.logAbs_mul, IwasawaThree.Torus.logAbs_posExp]
      have hm : Measurable fun t : ℝˣ => IwasawaThree.Torus.posExp r * t :=
        (continuous_const.mul continuous_id).measurable
      rw [h, ← Measure.map_map IwasawaThree.Torus.continuous_logAbs.measurable hm,
        map_mul_left_eq_self tau (IwasawaThree.Torus.posExp r)]⟩
    lt_top_of_isCompact := fun K hK => by
      rw [Measure.map_apply IwasawaThree.Torus.continuous_logAbs.measurable hK.measurableSet]
      refine lt_of_le_of_lt (measure_mono (IwasawaThree.Torus.preimage_logAbs_subset K)) ?_
      exact ((hK.image IwasawaThree.Torus.continuous_posExp).union
        (hK.image IwasawaThree.Torus.continuous_negExp)).measure_lt_top
    toIsOpenPosMeasure := ⟨fun U hU hne => by
      rw [Measure.map_apply IwasawaThree.Torus.continuous_logAbs.measurable hU.measurableSet]
      obtain ⟨r, hr⟩ := hne
      refine ((hU.preimage IwasawaThree.Torus.continuous_logAbs).measure_pos tau ⟨IwasawaThree.Torus.posExp r, ?_⟩).ne'
      show IwasawaThree.Torus.logAbs (IwasawaThree.Torus.posExp r) ∈ U
      rwa [IwasawaThree.Torus.logAbs_posExp]⟩ }

private theorem IwasawaThree.Torus.exists_map_logAbs_eq_smul [MeasurableSpace ℝˣ] [BorelSpace ℝˣ]
    (tau : Measure ℝˣ) [tau.IsHaarMeasure] :
    ∃ b : ℝ≥0∞, b ≠ 0 ∧ b ≠ ⊤ ∧ Measure.map IwasawaThree.Torus.logAbs tau = b • (volume : Measure ℝ) := by
  haveI := IwasawaThree.Torus.isAddHaarMeasure_map_logAbs tau
  exact IwasawaThree.exists_ennreal_smul_eq_of_isAddHaarMeasure _ volume

private theorem IwasawaThree.Torus.pi_map_logAbs_eq_smul [MeasurableSpace ℝˣ] [BorelSpace ℝˣ]
    (tau : Measure ℝˣ) [tau.IsHaarMeasure] (b : ℝ≥0∞)
    (hb : Measure.map IwasawaThree.Torus.logAbs tau = b • (volume : Measure ℝ)) :
    Measure.pi (fun _ : Fin 3 => Measure.map IwasawaThree.Torus.logAbs tau) =
      b ^ 3 • (volume : Measure (Fin 3 → ℝ)) := by
  haveI := IwasawaThree.Torus.isAddHaarMeasure_map_logAbs tau
  refine Measure.pi_eq fun s hs => ?_
  rw [Measure.smul_apply, volume_pi, Measure.pi_pi, smul_eq_mul]
  simp only [hb, Measure.smul_apply, smul_eq_mul, Finset.prod_mul_distrib, Finset.prod_const,
    Finset.card_univ, Fintype.card_fin]

private theorem IwasawaThree.Torus.exists_lintegral_pi_eq_mul_lintegral_posExp [MeasurableSpace ℝˣ] [BorelSpace ℝˣ]
    (tau : Measure ℝˣ) [tau.IsHaarMeasure] :
    ∃ b : ℝ≥0∞, b ≠ 0 ∧ b ≠ ⊤ ∧ ∀ G : (Fin 3 → ℝˣ) → ℝ≥0∞, Measurable G →
      (∀ t : Fin 3 → ℝˣ,
        G (fun i => IwasawaThree.Torus.posExp (IwasawaThree.Torus.logAbs (t i))) = G t) →
      ∫⁻ t, G t ∂(Measure.pi fun _ : Fin 3 => tau) =
        b * ∫⁻ s : Fin 3 → ℝ, G fun i => IwasawaThree.Torus.posExp (s i) := by
  obtain ⟨b, hb0, hbt, hb⟩ := IwasawaThree.Torus.exists_map_logAbs_eq_smul tau
  haveI := IwasawaThree.Torus.isAddHaarMeasure_map_logAbs tau
  refine ⟨b ^ 3, pow_ne_zero 3 hb0, ENNReal.pow_ne_top hbt, fun G hG hinv => ?_⟩
  have hpres := measurePreserving_pi (fun _ : Fin 3 => tau)
    (fun _ : Fin 3 => Measure.map IwasawaThree.Torus.logAbs tau)
    (f := fun _ : Fin 3 => IwasawaThree.Torus.logAbs)
    (fun _ => ⟨IwasawaThree.Torus.continuous_logAbs.measurable, rfl⟩)
  have hH : Measurable fun s : Fin 3 → ℝ => G fun i => IwasawaThree.Torus.posExp (s i) :=
    hG.comp (measurable_pi_lambda _ fun i =>
      IwasawaThree.Torus.continuous_posExp.measurable.comp (measurable_pi_apply i))
  calc ∫⁻ t, G t ∂(Measure.pi fun _ : Fin 3 => tau)
      = ∫⁻ t, G (fun i => IwasawaThree.Torus.posExp (IwasawaThree.Torus.logAbs (t i)))
          ∂(Measure.pi fun _ : Fin 3 => tau) := lintegral_congr fun t => (hinv t).symm
    _ = ∫⁻ s : Fin 3 → ℝ, G (fun i => IwasawaThree.Torus.posExp (s i))
          ∂(Measure.pi fun _ : Fin 3 => Measure.map IwasawaThree.Torus.logAbs tau) :=
        hpres.lintegral_comp hH
    _ = b ^ 3 * ∫⁻ s : Fin 3 → ℝ, G fun i => IwasawaThree.Torus.posExp (s i) := by
        rw [IwasawaThree.Torus.pi_map_logAbs_eq_smul tau b hb, lintegral_smul_measure, smul_eq_mul]

private theorem IwasawaThree.Torus.density_posExp (s : Fin 3 → ℝ) :
    ENNReal.ofReal (|((IwasawaThree.Torus.posExp (s 0) : ℝˣ) : ℝ)|⁻¹ ^ 2 *
        |((IwasawaThree.Torus.posExp (s 2) : ℝˣ) : ℝ)| ^ 2) =
      ENNReal.ofReal (Real.exp (-2 * s 0 + 2 * s 2)) := by
  congr 1
  rw [IwasawaThree.Torus.val_posExp, IwasawaThree.Torus.val_posExp, abs_of_pos (Real.exp_pos _),
    abs_of_pos (Real.exp_pos _),
    show -2 * s 0 + 2 * s 2 = -s 0 + -s 0 + (s 2 + s 2) by ring, Real.exp_add, Real.exp_add,
    Real.exp_add, Real.exp_neg]
  ring

private theorem IwasawaThree.val_diagGL {R : Type*} [CommRing R] (t : Fin 3 → Rˣ) :
    ((IwasawaThree.diagGL t : GL (Fin 3) R) : Matrix (Fin 3) (Fin 3) R) = Matrix.diagonal fun i => (t i : R) := rfl

private theorem IwasawaThree.val_diagGL_inv {R : Type*} [CommRing R] (t : Fin 3 → Rˣ) :
    (((IwasawaThree.diagGL t)⁻¹ : GL (Fin 3) R) : Matrix (Fin 3) (Fin 3) R) =
      Matrix.diagonal fun i => (((t i)⁻¹ : Rˣ) : R) := rfl

private theorem IwasawaThree.diagGL_mul {R : Type*} [CommRing R] (u v : Fin 3 → Rˣ) :
    IwasawaThree.diagGL (u * v) = IwasawaThree.diagGL u * IwasawaThree.diagGL v := by
  unfold IwasawaThree.diagGL
  rw [map_mul, map_mul]

private abbrev IwasawaThree.Real.secondCountable_matrix : SecondCountableTopology (Matrix (Fin 3) (Fin 3) ℝ) :=
  inferInstanceAs (SecondCountableTopology (Fin 3 → Fin 3 → ℝ))
attribute [local instance] IwasawaThree.Real.secondCountable_matrix

private abbrev IwasawaThree.Real.secondCountable_matrix_mop :
    SecondCountableTopology (Matrix (Fin 3) (Fin 3) ℝ)ᵐᵒᵖ :=
  MulOpposite.opHomeomorph.symm.secondCountableTopology
attribute [local instance] IwasawaThree.Real.secondCountable_matrix_mop

private abbrev IwasawaThree.Real.secondCountable_gl : SecondCountableTopology (GL (Fin 3) ℝ) :=
  Units.isEmbedding_embedProduct.isInducing.secondCountableTopology
attribute [local instance] IwasawaThree.Real.secondCountable_gl

private theorem IwasawaThree.Real.abs_apply_le_one_of_transpose_mul_self {k : Matrix (Fin 3) (Fin 3) ℝ}
    (hk : k.transpose * k = 1) (i j : Fin 3) : |k i j| ≤ 1 := by
  have hjj : ∑ l, k l j * k l j = 1 := by
    have h := congrFun (congrFun hk j) j
    simpa [Matrix.mul_apply, Matrix.transpose_apply] using h
  have hle : k i j ^ 2 ≤ ∑ l, k l j * k l j := by
    rw [sq]
    exact Finset.single_le_sum (f := fun l => k l j * k l j) (fun l _ => mul_self_nonneg (k l j))
      (Finset.mem_univ i)
  exact (sq_le_one_iff_abs_le_one _).1 (hjj ▸ hle)

private theorem IwasawaThree.Real.val_inv_eq_transpose_of_mem {k : GL (Fin 3) ℝ}
    (hk : k ∈ LanglandsTunnell.CubicInduction.WhittakerBlock.orthogonalSubgroup3) :
    ((k⁻¹ : GL (Fin 3) ℝ) : Matrix (Fin 3) (Fin 3) ℝ) = (k : Matrix (Fin 3) (Fin 3) ℝ).transpose := by
  have hk' : (k : Matrix (Fin 3) (Fin 3) ℝ).transpose * (k : Matrix (Fin 3) (Fin 3) ℝ) = 1 := hk
  exact Units.inv_eq_of_mul_eq_one_left hk'

private def IwasawaThree.Real.unitBox : Set (Matrix (Fin 3) (Fin 3) ℝ) :=
  Set.pi Set.univ fun _ => Set.pi Set.univ fun _ => Set.Icc (-1 : ℝ) 1

private theorem IwasawaThree.Real.isCompact_unitBox : IsCompact IwasawaThree.Real.unitBox :=
  isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => isCompact_Icc

private theorem IwasawaThree.Real.mem_unitBox_of_forall {M : Matrix (Fin 3) (Fin 3) ℝ} (h : ∀ i j, |M i j| ≤ 1) :
    M ∈ IwasawaThree.Real.unitBox := by
  intro i _ j _
  exact Set.mem_Icc.2 (abs_le.1 (h i j))

private theorem IwasawaThree.Real.isCompact_orthogonalSubgroup3 :
    IsCompact (LanglandsTunnell.CubicInduction.WhittakerBlock.orthogonalSubgroup3 : Set (GL (Fin 3) ℝ)) := by
  haveI : T2Space (Matrix (Fin 3) (Fin 3) ℝ) := inferInstanceAs (T2Space (Fin 3 → Fin 3 → ℝ))
  have hpre : IsCompact (Units.embedProduct (Matrix (Fin 3) (Fin 3) ℝ) ⁻¹'
      (IwasawaThree.Real.unitBox ×ˢ (MulOpposite.op '' IwasawaThree.Real.unitBox))) :=
    Units.isClosedEmbedding_embedProduct.isCompact_preimage
      (IwasawaThree.Real.isCompact_unitBox.prod
        (IwasawaThree.Real.isCompact_unitBox.image MulOpposite.continuous_op))
  have hclosed :
      IsClosed (LanglandsTunnell.CubicInduction.WhittakerBlock.orthogonalSubgroup3 : Set (GL (Fin 3) ℝ)) := by
    have hcont : Continuous fun k : GL (Fin 3) ℝ =>
        (k : Matrix (Fin 3) (Fin 3) ℝ).transpose * (k : Matrix (Fin 3) (Fin 3) ℝ) :=
      Units.continuous_val.matrix_transpose.matrix_mul Units.continuous_val
    exact isClosed_singleton.preimage hcont
  refine hpre.of_isClosed_subset hclosed fun k hk => ?_
  have hk' : (k : Matrix (Fin 3) (Fin 3) ℝ).transpose * (k : Matrix (Fin 3) (Fin 3) ℝ) = 1 := hk
  refine Set.mem_prod.2 ⟨IwasawaThree.Real.mem_unitBox_of_forall fun i j => ?_, ?_⟩
  · exact IwasawaThree.Real.abs_apply_le_one_of_transpose_mul_self hk' i j
  · refine ⟨((k⁻¹ : GL (Fin 3) ℝ) : Matrix (Fin 3) (Fin 3) ℝ), ?_, rfl⟩
    rw [IwasawaThree.Real.val_inv_eq_transpose_of_mem hk]
    exact IwasawaThree.Real.mem_unitBox_of_forall fun i j =>
      IwasawaThree.Real.abs_apply_le_one_of_transpose_mul_self hk' j i

private abbrev IwasawaThree.Real.compactSpace_orthogonalSubgroup3 :
    CompactSpace LanglandsTunnell.CubicInduction.WhittakerBlock.orthogonalSubgroup3 :=
  isCompact_iff_compactSpace.1 IwasawaThree.Real.isCompact_orthogonalSubgroup3
attribute [local instance] IwasawaThree.Real.compactSpace_orthogonalSubgroup3

private noncomputable def IwasawaThree.Real.signUnit (t : ℝˣ) : ℝˣ :=
  (IwasawaThree.Torus.posExp (IwasawaThree.Torus.logAbs t))⁻¹ * t

private theorem IwasawaThree.Real.posExp_logAbs_mul_signUnit (t : ℝˣ) :
    IwasawaThree.Torus.posExp (IwasawaThree.Torus.logAbs t) * IwasawaThree.Real.signUnit t = t :=
  mul_inv_cancel_left _ _

private theorem IwasawaThree.Real.val_signUnit_mul_self (t : ℝˣ) :
    ((IwasawaThree.Real.signUnit t : ℝˣ) : ℝ) * ((IwasawaThree.Real.signUnit t : ℝˣ) : ℝ) = 1 := by
  have habs : Real.exp (IwasawaThree.Torus.logAbs t) = |(t : ℝ)| := Real.exp_log (abs_pos.2 t.ne_zero)
  unfold IwasawaThree.Real.signUnit
  rw [Units.val_mul, Units.val_inv_eq_inv_val, IwasawaThree.Torus.val_posExp, habs, ← sq, mul_pow, inv_pow,
    sq_abs, inv_mul_cancel₀ (pow_ne_zero 2 t.ne_zero)]

private theorem IwasawaThree.Real.diagGL_eq_abs_mul_sign (t : Fin 3 → ℝˣ) :
    IwasawaThree.diagGL t =
      IwasawaThree.diagGL (fun i => IwasawaThree.Torus.posExp (IwasawaThree.Torus.logAbs (t i))) *
        IwasawaThree.diagGL (fun i => IwasawaThree.Real.signUnit (t i)) := by
  rw [← IwasawaThree.diagGL_mul]
  congr 1
  funext i
  exact (IwasawaThree.Real.posExp_logAbs_mul_signUnit (t i)).symm

private theorem IwasawaThree.Real.diagGL_signUnit_mem (t : Fin 3 → ℝˣ) :
    IwasawaThree.diagGL (fun i => IwasawaThree.Real.signUnit (t i)) ∈
      LanglandsTunnell.CubicInduction.WhittakerBlock.orthogonalSubgroup3 := by
  show (Matrix.transpose _) * _ = (1 : Matrix (Fin 3) (Fin 3) ℝ)
  rw [IwasawaThree.val_diagGL, Matrix.diagonal_transpose, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
  congr 1
  funext i
  exact IwasawaThree.Real.val_signUnit_mul_self (t i)

private theorem IwasawaThree.Real.lintegral_diagGL_eq_lintegral_diagGL_abs
    [MeasurableSpace (GL (Fin 3) ℝ)] [BorelSpace (GL (Fin 3) ℝ)]
    (nu : Measure LanglandsTunnell.CubicInduction.WhittakerBlock.orthogonalSubgroup3) [nu.IsMulLeftInvariant]
    (φ : GL (Fin 3) ℝ → ℝ≥0∞) (g : GL (Fin 3) ℝ) (t : Fin 3 → ℝˣ) :
    ∫⁻ k : LanglandsTunnell.CubicInduction.WhittakerBlock.orthogonalSubgroup3,
        φ (g * IwasawaThree.diagGL t * k) ∂nu =
      ∫⁻ k : LanglandsTunnell.CubicInduction.WhittakerBlock.orthogonalSubgroup3,
        φ (g * IwasawaThree.diagGL (fun i => IwasawaThree.Torus.posExp (IwasawaThree.Torus.logAbs (t i))) * k)
          ∂nu := by
  set σ : LanglandsTunnell.CubicInduction.WhittakerBlock.orthogonalSubgroup3 :=
    ⟨_, IwasawaThree.Real.diagGL_signUnit_mem t⟩ with hσ
  calc ∫⁻ k : LanglandsTunnell.CubicInduction.WhittakerBlock.orthogonalSubgroup3,
          φ (g * IwasawaThree.diagGL t * k) ∂nu
      = ∫⁻ k : LanglandsTunnell.CubicInduction.WhittakerBlock.orthogonalSubgroup3,
          (fun k : LanglandsTunnell.CubicInduction.WhittakerBlock.orthogonalSubgroup3 =>
            φ (g * IwasawaThree.diagGL
              (fun i => IwasawaThree.Torus.posExp (IwasawaThree.Torus.logAbs (t i))) * k)) (σ * k) ∂nu := by
        refine lintegral_congr fun k => ?_
        simp only [IwasawaThree.Real.diagGL_eq_abs_mul_sign t, hσ, Subgroup.coe_mul, mul_assoc]
    _ = _ := lintegral_mul_left_eq_self
      (fun k : LanglandsTunnell.CubicInduction.WhittakerBlock.orthogonalSubgroup3 =>
        φ (g * IwasawaThree.diagGL (fun i => IwasawaThree.Torus.posExp (IwasawaThree.Torus.logAbs (t i))) * k)) σ

private abbrev IwasawaThree.Real.secondCountable_units : SecondCountableTopology ℝˣ :=
  Units.isEmbedding_embedProduct.isInducing.secondCountableTopology
attribute [local instance] IwasawaThree.Real.secondCountable_units

private theorem IwasawaThree.Real.continuous_diagGL :
    Continuous (IwasawaThree.diagGL : (Fin 3 → ℝˣ) → GL (Fin 3) ℝ) := by
  refine Units.continuous_iff.2 ⟨?_, ?_⟩
  · show Continuous fun t : Fin 3 → ℝˣ => Matrix.diagonal fun i => ((t i : ℝˣ) : ℝ)
    refine continuous_matrix fun i j => ?_
    simp only [Matrix.diagonal_apply]
    split_ifs
    · exact Units.continuous_val.comp (continuous_apply i)
    · exact continuous_const
  · show Continuous fun t : Fin 3 → ℝˣ => Matrix.diagonal fun i => (((t i)⁻¹ : ℝˣ) : ℝ)
    refine continuous_matrix fun i j => ?_
    simp only [Matrix.diagonal_apply]
    split_ifs
    · exact Units.continuous_coe_inv.comp (continuous_apply i)
    · exact continuous_const

namespace IwasawaThree.Real
private theorem _root_.LanglandsTunnell.CubicInduction.WhittakerBlock.IwasawaThree.Real.continuous_upperUnipotent3 :
    Continuous fun x : ℝ × ℝ × ℝ => (upperUnipotent3 x.1 x.2.1 x.2.2 : GL (Fin 3) ℝ) := by
  refine Units.continuous_iff.2 ⟨?_, ?_⟩
  · refine continuous_matrix fun i j => ?_
    fin_cases i <;> fin_cases j <;> simp [upperUnipotent3] <;> fun_prop
  · refine continuous_matrix fun i j => ?_
    fin_cases i <;> fin_cases j <;> simp [upperUnipotent3] <;> fun_prop

end IwasawaThree.Real
p2m_export "LanglandsTunnell.CubicInduction.WhittakerBlock" "IwasawaThree.Real.continuous_upperUnipotent3"

private theorem IwasawaThree.Real.continuous_iwasawaMap :
    Continuous fun q : ((ℝ × ℝ × ℝ) × (Fin 3 → ℝ)) × orthogonalSubgroup3 =>
      upperUnipotent3 q.1.1.1 q.1.1.2.1 q.1.1.2.2 *
        Units.map (Matrix.diagonalRingHom (Fin 3) ℝ).toMonoidHom
          (MulEquiv.piUnits.symm fun i => Units.mk0 (Real.exp (q.1.2 i)) (Real.exp_pos _).ne') *
        (q.2 : GL (Fin 3) ℝ) := by
  show Continuous fun q : ((ℝ × ℝ × ℝ) × (Fin 3 → ℝ)) × orthogonalSubgroup3 =>
    upperUnipotent3 q.1.1.1 q.1.1.2.1 q.1.1.2.2 *
      IwasawaThree.diagGL (fun i => IwasawaThree.Torus.posExp (q.1.2 i)) * (q.2 : GL (Fin 3) ℝ)
  have h₁ : Continuous fun q : ((ℝ × ℝ × ℝ) × (Fin 3 → ℝ)) × orthogonalSubgroup3 =>
      (upperUnipotent3 q.1.1.1 q.1.1.2.1 q.1.1.2.2 : GL (Fin 3) ℝ) :=
    IwasawaThree.Real.continuous_upperUnipotent3.comp (continuous_fst.comp continuous_fst)
  have h₂ : Continuous fun q : ((ℝ × ℝ × ℝ) × (Fin 3 → ℝ)) × orthogonalSubgroup3 =>
      IwasawaThree.diagGL (fun i => IwasawaThree.Torus.posExp (q.1.2 i)) :=
    IwasawaThree.Real.continuous_diagGL.comp (continuous_pi fun i =>
      IwasawaThree.Torus.continuous_posExp.comp ((continuous_apply i).comp (continuous_snd.comp continuous_fst)))
  exact (h₁.mul h₂).mul (continuous_subtype_val.comp continuous_snd)

namespace IwasawaThree.Real

private noncomputable def _root_.LanglandsTunnell.CubicInduction.WhittakerBlock.IwasawaThree.Real.dens (t : Fin 3 → ℝˣ) : ℝ≥0∞ :=
  ENNReal.ofReal (|(t 0 : ℝ)|⁻¹ ^ 2 * |(t 2 : ℝ)| ^ 2)

end IwasawaThree.Real
p2m_export "LanglandsTunnell.CubicInduction.WhittakerBlock" "IwasawaThree.Real.dens"
private theorem IwasawaThree.Real.dens_ne_top (t : Fin 3 → ℝˣ) : IwasawaThree.Real.dens t ≠ ⊤ := ENNReal.ofReal_ne_top

private theorem IwasawaThree.Real.continuous_dens : Continuous IwasawaThree.Real.dens := by
  unfold IwasawaThree.Real.dens
  refine ENNReal.continuous_ofReal.comp (Continuous.mul (Continuous.pow ?_ 2) (Continuous.pow ?_ 2))
  · have h0 : Continuous fun t : Fin 3 → ℝˣ => |((t 0 : ℝˣ) : ℝ)| :=
      continuous_abs.comp (Units.continuous_val.comp (continuous_apply 0))
    exact h0.inv₀ fun t => abs_ne_zero.2 (t 0).ne_zero
  · exact continuous_abs.comp (Units.continuous_val.comp (continuous_apply 2))

private theorem IwasawaThree.Real.dens_abs (t : Fin 3 → ℝˣ) :
    IwasawaThree.Real.dens (fun i => IwasawaThree.Torus.posExp (IwasawaThree.Torus.logAbs (t i))) =
      IwasawaThree.Real.dens t := by
  unfold IwasawaThree.Real.dens
  simp only [IwasawaThree.Torus.val_posExp, IwasawaThree.Torus.logAbs, Real.exp_log (abs_pos.2 (t 0).ne_zero),
    Real.exp_log (abs_pos.2 (t 2).ne_zero), abs_abs]

private theorem IwasawaThree.Real.dens_posExp (s : Fin 3 → ℝ) :
    IwasawaThree.Real.dens (fun i => IwasawaThree.Torus.posExp (s i)) =
      ENNReal.ofReal (Real.exp (-2 * s 0 + 2 * s 2)) :=
  IwasawaThree.Torus.density_posExp s

private theorem IwasawaThree.exists_lintegral_real_eq_mul_lintegral_iwasawa
    [MeasurableSpace (GL (Fin 3) ℝ)] [BorelSpace (GL (Fin 3) ℝ)]
    (μ : Measure (GL (Fin 3) ℝ)) [μ.IsHaarMeasure]
    (ν : Measure orthogonalSubgroup3) [ν.IsHaarMeasure]
    (lam : Measure ℝ) [lam.IsAddHaarMeasure]
    [MeasurableSpace ℝˣ] [BorelSpace ℝˣ] (tau : Measure ℝˣ) [tau.IsHaarMeasure] :
    ∃ c : ℝ≥0∞, c ≠ 0 ∧ c ≠ ⊤ ∧ ∀ φ : GL (Fin 3) ℝ → ℝ≥0∞, Measurable φ →
      ∫⁻ g, φ g ∂μ =
        c * ∫⁻ x : ℝ × ℝ × ℝ, ∫⁻ t : Fin 3 → ℝˣ, ∫⁻ k : orthogonalSubgroup3,
          φ (upperUnipotent3 x.1 x.2.1 x.2.2 * IwasawaThree.diagGL t * (k : GL (Fin 3) ℝ)) *
            ENNReal.ofReal (|(t 0 : ℝ)|⁻¹ ^ 2 * |(t 2 : ℝ)| ^ 2)
          ∂ν ∂(Measure.pi fun _ : Fin 3 => tau) ∂(lam.prod (lam.prod lam)) := by
  obtain ⟨c, hc0, hct, hμ⟩ := exists_isHaarMeasure_GL_three_real_eq_smul_map_iwasawa μ ν
  obtain ⟨a, ha0, hat, hlam⟩ := IwasawaThree.exists_ennreal_smul_eq_of_isAddHaarMeasure lam volume
  obtain ⟨b, hb0, hbt, htorus⟩ := IwasawaThree.Torus.exists_lintegral_pi_eq_mul_lintegral_posExp tau
  have hab0 : a ^ 3 * b ≠ 0 := mul_ne_zero (pow_ne_zero 3 ha0) hb0
  have habt : a ^ 3 * b ≠ ⊤ := ENNReal.mul_ne_top (ENNReal.pow_ne_top hat) hbt
  refine ⟨c / (a ^ 3 * b), (ENNReal.div_pos hc0 habt).ne', ENNReal.div_ne_top hct hab0, fun φ hφ => ?_⟩

  have hlam2 : lam.prod lam = a ^ 2 • (volume : Measure (ℝ × ℝ)) := by
    refine Measure.prod_eq fun s t hs ht => ?_
    rw [Measure.smul_apply, Measure.volume_eq_prod, Measure.prod_prod, hlam, Measure.smul_apply,
      Measure.smul_apply, smul_eq_mul, smul_eq_mul, smul_eq_mul]
    ring
  have hlam3 : lam.prod (lam.prod lam) = a ^ 3 • (volume : Measure (ℝ × ℝ × ℝ)) := by
    refine Measure.prod_eq fun s t hs ht => ?_
    rw [Measure.smul_apply, Measure.volume_eq_prod, Measure.prod_prod, hlam2, hlam, Measure.smul_apply,
      Measure.smul_apply, smul_eq_mul, smul_eq_mul, smul_eq_mul]
    ring

  set w : (ℝ × ℝ × ℝ) × (Fin 3 → ℝ) → ℝ≥0∞ := fun p => ENNReal.ofReal (Real.exp (-2 * p.2 0 + 2 * p.2 2)) with hw_def
  have hw : Measurable w :=
    (ENNReal.continuous_ofReal.comp (Real.continuous_exp.comp (by fun_prop))).measurable
  set Ψ : ((ℝ × ℝ × ℝ) × (Fin 3 → ℝ)) × orthogonalSubgroup3 → GL (Fin 3) ℝ := fun q =>
    upperUnipotent3 q.1.1.1 q.1.1.2.1 q.1.1.2.2 *
      Units.map (Matrix.diagonalRingHom (Fin 3) ℝ).toMonoidHom
        (MulEquiv.piUnits.symm fun i => Units.mk0 (Real.exp (q.1.2 i)) (Real.exp_pos _).ne') *
      (q.2 : GL (Fin 3) ℝ) with hΨ_def
  have hΨ : Measurable Ψ := IwasawaThree.Real.continuous_iwasawaMap.measurable
  have hφΨ : Measurable fun q => φ (Ψ q) := hφ.comp hΨ
  set g : (ℝ × ℝ × ℝ) × (Fin 3 → ℝ) → ℝ≥0∞ := fun p => ∫⁻ k : orthogonalSubgroup3, φ (Ψ (p, k)) ∂ν with hg_def
  have hg : Measurable g := hφΨ.lintegral_prod_right'

  have hleft : ∫⁻ x, φ x ∂μ =
      c * ∫⁻ x : ℝ × ℝ × ℝ, ∫⁻ s : Fin 3 → ℝ, w (x, s) * g (x, s) := by
    have hwg : Measurable fun p : (ℝ × ℝ × ℝ) × (Fin 3 → ℝ) => w p * g p := hw.mul hg
    rw [hμ, lintegral_smul_measure, smul_eq_mul, lintegral_map hφ hΨ, lintegral_prod _ hφΨ.aemeasurable, ← hg_def,
      lintegral_withDensity_eq_lintegral_mul volume hw hg, Measure.volume_eq_prod]
    exact congrArg (c * ·) (lintegral_prod _ hwg.aemeasurable)

  have hinner : ∀ x : ℝ × ℝ × ℝ,
      ∫⁻ t : Fin 3 → ℝˣ, ∫⁻ k : orthogonalSubgroup3,
          φ (upperUnipotent3 x.1 x.2.1 x.2.2 * IwasawaThree.diagGL t * (k : GL (Fin 3) ℝ)) *
            ENNReal.ofReal (|(t 0 : ℝ)|⁻¹ ^ 2 * |(t 2 : ℝ)| ^ 2) ∂ν ∂(Measure.pi fun _ : Fin 3 => tau) =
        b * ∫⁻ s : Fin 3 → ℝ, w (x, s) * g (x, s) := by
    intro x
    set G : (Fin 3 → ℝˣ) → ℝ≥0∞ := fun t => ∫⁻ k : orthogonalSubgroup3,
      φ (upperUnipotent3 x.1 x.2.1 x.2.2 * IwasawaThree.diagGL t * (k : GL (Fin 3) ℝ)) *
        IwasawaThree.Real.dens t ∂ν with hG_def
    have hGmeas : Measurable G := by
      refine Measurable.lintegral_prod_right' (f := fun tk : (Fin 3 → ℝˣ) × orthogonalSubgroup3 =>
        φ (upperUnipotent3 x.1 x.2.1 x.2.2 * IwasawaThree.diagGL tk.1 * (tk.2 : GL (Fin 3) ℝ)) *
          IwasawaThree.Real.dens tk.1) ?_
      refine Measurable.mul (hφ.comp ?_) (IwasawaThree.Real.continuous_dens.comp continuous_fst).measurable
      exact ((continuous_const.mul (IwasawaThree.Real.continuous_diagGL.comp continuous_fst)).mul
        (continuous_subtype_val.comp continuous_snd)).measurable
    have hGinv : ∀ t : Fin 3 → ℝˣ,
        G (fun i => IwasawaThree.Torus.posExp (IwasawaThree.Torus.logAbs (t i))) = G t := by
      intro t
      simp only [hG_def]
      rw [lintegral_mul_const' _ _ (IwasawaThree.Real.dens_ne_top _),
        lintegral_mul_const' _ _ (IwasawaThree.Real.dens_ne_top _), IwasawaThree.Real.dens_abs,
        IwasawaThree.Real.lintegral_diagGL_eq_lintegral_diagGL_abs ν φ _ t]
    have hG : ∀ s : Fin 3 → ℝ, G (fun i => IwasawaThree.Torus.posExp (s i)) = w (x, s) * g (x, s) := by
      intro s
      simp only [hG_def, hw_def, hg_def, hΨ_def]
      rw [lintegral_mul_const' _ _ (IwasawaThree.Real.dens_ne_top _), IwasawaThree.Real.dens_posExp, mul_comm]
      rfl
    calc _ = ∫⁻ t, G t ∂(Measure.pi fun _ : Fin 3 => tau) := rfl
      _ = b * ∫⁻ s : Fin 3 → ℝ, G fun i => IwasawaThree.Torus.posExp (s i) := htorus G hGmeas hGinv
      _ = b * ∫⁻ s : Fin 3 → ℝ, w (x, s) * g (x, s) := by simp only [hG]
  rw [hleft, hlam3, lintegral_smul_measure]
  simp only [hinner]
  rw [lintegral_const_mul' b _ hbt, smul_eq_mul,
    show c / (a ^ 3 * b) * (a ^ 3 * (b * ∫⁻ x : ℝ × ℝ × ℝ, ∫⁻ s : Fin 3 → ℝ, w (x, s) * g (x, s))) =
      c / (a ^ 3 * b) * (a ^ 3 * b) * ∫⁻ x : ℝ × ℝ × ℝ, ∫⁻ s : Fin 3 → ℝ, w (x, s) * g (x, s) by ring,
    ENNReal.div_mul_cancel hab0 habt]

private def IwasawaThree.orthSubgroupInf : Subgroup (GL (Fin 3) (InfiniteAdeleRing ℚ)) where
  carrier := orth3
  one_mem' := by
    show ((1 : GL (Fin 3) (InfiniteAdeleRing ℚ)) : Matrix (Fin 3) (Fin 3) (InfiniteAdeleRing ℚ)).transpose * _ = 1
    simp
  mul_mem' := by
    intro a b ha hb
    have ha' : (a : Matrix (Fin 3) (Fin 3) (InfiniteAdeleRing ℚ)).transpose * a = 1 := ha
    have hb' : (b : Matrix (Fin 3) (Fin 3) (InfiniteAdeleRing ℚ)).transpose * b = 1 := hb
    show ((a * b : GL (Fin 3) (InfiniteAdeleRing ℚ)) : Matrix (Fin 3) (Fin 3) (InfiniteAdeleRing ℚ)).transpose *
      (a * b : GL (Fin 3) (InfiniteAdeleRing ℚ)) = 1
    rw [Units.val_mul, Matrix.transpose_mul, Matrix.mul_assoc,
      ← Matrix.mul_assoc (a : Matrix (Fin 3) (Fin 3) (InfiniteAdeleRing ℚ)).transpose, ha', Matrix.one_mul, hb']
  inv_mem' := by
    intro a ha
    have ha' : (a : Matrix (Fin 3) (Fin 3) (InfiniteAdeleRing ℚ)).transpose * a = 1 := ha
    have hinv : ((a⁻¹ : GL (Fin 3) (InfiniteAdeleRing ℚ)) : Matrix (Fin 3) (Fin 3) (InfiniteAdeleRing ℚ)) =
        (a : Matrix (Fin 3) (Fin 3) (InfiniteAdeleRing ℚ)).transpose :=
      Units.inv_eq_of_mul_eq_one_left ha'
    show ((a⁻¹ : GL (Fin 3) (InfiniteAdeleRing ℚ)) : Matrix (Fin 3) (Fin 3) (InfiniteAdeleRing ℚ)).transpose *
      (a⁻¹ : GL (Fin 3) (InfiniteAdeleRing ℚ)) = 1
    rw [hinv, Matrix.transpose_transpose, ← hinv, Units.mul_inv]

private theorem IwasawaThree.mem_orthSubgroupInf_iff (k : GL (Fin 3) (InfiniteAdeleRing ℚ)) :
    k ∈ IwasawaThree.orthSubgroupInf ↔ k ∈ orth3 :=
  Iff.rfl

private theorem IwasawaThree.Arch.realCoord_ofReal (r : ℝ) :
    AutomorphicForm.StandardKernel.realCoord (AutomorphicForm.StandardKernel.ofReal r) = r :=
  (InfinitePlace.Completion.ringEquivRealOfIsReal Rat.isReal_infinitePlace).apply_symm_apply r

private noncomputable def IwasawaThree.Arch.archEquiv : InfiniteAdeleRing ℚ ≃+* ℝ :=
  RingEquiv.ofBijective AutomorphicForm.StandardKernel.realCoord
    ⟨Function.LeftInverse.injective AutomorphicForm.StandardKernel.ofReal_realCoord,
      Function.RightInverse.surjective IwasawaThree.Arch.realCoord_ofReal⟩

private theorem IwasawaThree.Arch.archEquiv_apply (x : InfiniteAdeleRing ℚ) :
    IwasawaThree.Arch.archEquiv x = AutomorphicForm.StandardKernel.realCoord x := rfl

private theorem IwasawaThree.Arch.archEquiv_symm_apply (r : ℝ) :
    IwasawaThree.Arch.archEquiv.symm r = AutomorphicForm.StandardKernel.ofReal r := by
  apply IwasawaThree.Arch.archEquiv.injective
  rw [RingEquiv.apply_symm_apply, IwasawaThree.Arch.archEquiv_apply, IwasawaThree.Arch.realCoord_ofReal]

private theorem IwasawaThree.Arch.continuous_archEquiv : Continuous IwasawaThree.Arch.archEquiv :=
  (InfinitePlace.Completion.isometryEquivRealOfIsReal Rat.isReal_infinitePlace).continuous.comp
    (continuous_apply Rat.infinitePlace)

private theorem IwasawaThree.Arch.continuous_archEquiv_symm : Continuous IwasawaThree.Arch.archEquiv.symm := by
  have h : ⇑IwasawaThree.Arch.archEquiv.symm = AutomorphicForm.StandardKernel.ofReal :=
    funext IwasawaThree.Arch.archEquiv_symm_apply
  rw [h]
  exact AutomorphicForm.StandardKernel.continuous_ofReal

private abbrev IwasawaThree.Arch.locallyCompact_units : LocallyCompactSpace (InfiniteAdeleRing ℚ)ˣ :=
  Units.isClosedEmbedding_embedProduct.locallyCompactSpace
attribute [local instance] IwasawaThree.Arch.locallyCompact_units

private abbrev IwasawaThree.Arch.locallyCompact_realUnits : LocallyCompactSpace ℝˣ :=
  Units.isClosedEmbedding_embedProduct.locallyCompactSpace
attribute [local instance] IwasawaThree.Arch.locallyCompact_realUnits

private noncomputable def IwasawaThree.Arch.glEquivReal : GL (Fin 3) (InfiniteAdeleRing ℚ) ≃* GL (Fin 3) ℝ :=
  Units.mapEquiv (IwasawaThree.Arch.archEquiv.mapMatrix (m := Fin 3)).toMulEquiv

private theorem IwasawaThree.Arch.val_glEquivReal (g : GL (Fin 3) (InfiniteAdeleRing ℚ)) :
    ((IwasawaThree.Arch.glEquivReal g : GL (Fin 3) ℝ) : Matrix (Fin 3) (Fin 3) ℝ) =
      (g : Matrix (Fin 3) (Fin 3) (InfiniteAdeleRing ℚ)).map IwasawaThree.Arch.archEquiv := rfl

private theorem IwasawaThree.Arch.val_glEquivReal_symm (h : GL (Fin 3) ℝ) :
    ((IwasawaThree.Arch.glEquivReal.symm h : GL (Fin 3) (InfiniteAdeleRing ℚ)) :
        Matrix (Fin 3) (Fin 3) (InfiniteAdeleRing ℚ)) =
      (h : Matrix (Fin 3) (Fin 3) ℝ).map IwasawaThree.Arch.archEquiv.symm := rfl

private theorem IwasawaThree.Arch.continuous_glEquivReal : Continuous IwasawaThree.Arch.glEquivReal := by
  refine Units.continuous_iff.2 ⟨?_, ?_⟩
  · show Continuous fun g : GL (Fin 3) (InfiniteAdeleRing ℚ) =>
      (g : Matrix (Fin 3) (Fin 3) (InfiniteAdeleRing ℚ)).map IwasawaThree.Arch.archEquiv
    exact Units.continuous_val.matrix_map IwasawaThree.Arch.continuous_archEquiv
  · show Continuous fun g : GL (Fin 3) (InfiniteAdeleRing ℚ) =>
      ((g⁻¹ : GL (Fin 3) (InfiniteAdeleRing ℚ)) : Matrix (Fin 3) (Fin 3) (InfiniteAdeleRing ℚ)).map
        IwasawaThree.Arch.archEquiv
    exact Units.continuous_coe_inv.matrix_map IwasawaThree.Arch.continuous_archEquiv

private theorem IwasawaThree.Arch.continuous_glEquivReal_symm : Continuous IwasawaThree.Arch.glEquivReal.symm := by
  refine Units.continuous_iff.2 ⟨?_, ?_⟩
  · show Continuous fun h : GL (Fin 3) ℝ => (h : Matrix (Fin 3) (Fin 3) ℝ).map IwasawaThree.Arch.archEquiv.symm
    exact Units.continuous_val.matrix_map IwasawaThree.Arch.continuous_archEquiv_symm
  · show Continuous fun h : GL (Fin 3) ℝ =>
      ((h⁻¹ : GL (Fin 3) ℝ) : Matrix (Fin 3) (Fin 3) ℝ).map IwasawaThree.Arch.archEquiv.symm
    exact Units.continuous_coe_inv.matrix_map IwasawaThree.Arch.continuous_archEquiv_symm

private noncomputable def IwasawaThree.Arch.unitsEquiv : (InfiniteAdeleRing ℚ)ˣ ≃* ℝˣ :=
  Units.mapEquiv IwasawaThree.Arch.archEquiv.toMulEquiv

private theorem IwasawaThree.Arch.val_unitsEquiv (u : (InfiniteAdeleRing ℚ)ˣ) :
    ((IwasawaThree.Arch.unitsEquiv u : ℝˣ) : ℝ) = IwasawaThree.Arch.archEquiv (u : InfiniteAdeleRing ℚ) := rfl

private theorem IwasawaThree.Arch.val_unitsEquiv_inv (u : (InfiniteAdeleRing ℚ)ˣ) :
    (((IwasawaThree.Arch.unitsEquiv u)⁻¹ : ℝˣ) : ℝ) =
      IwasawaThree.Arch.archEquiv ((u⁻¹ : (InfiniteAdeleRing ℚ)ˣ) : InfiniteAdeleRing ℚ) := rfl

private theorem IwasawaThree.Arch.continuous_unitsEquiv : Continuous IwasawaThree.Arch.unitsEquiv := by
  refine Units.continuous_iff.2 ⟨?_, ?_⟩
  · show Continuous fun u : (InfiniteAdeleRing ℚ)ˣ => IwasawaThree.Arch.archEquiv (u : InfiniteAdeleRing ℚ)
    exact IwasawaThree.Arch.continuous_archEquiv.comp Units.continuous_val
  · show Continuous fun u : (InfiniteAdeleRing ℚ)ˣ =>
      IwasawaThree.Arch.archEquiv ((u⁻¹ : (InfiniteAdeleRing ℚ)ˣ) : InfiniteAdeleRing ℚ)
    exact IwasawaThree.Arch.continuous_archEquiv.comp Units.continuous_coe_inv

private theorem IwasawaThree.Arch.continuous_unitsEquiv_symm : Continuous IwasawaThree.Arch.unitsEquiv.symm := by
  refine Units.continuous_iff.2 ⟨?_, ?_⟩
  · show Continuous fun r : ℝˣ => IwasawaThree.Arch.archEquiv.symm (r : ℝ)
    exact IwasawaThree.Arch.continuous_archEquiv_symm.comp Units.continuous_val
  · show Continuous fun r : ℝˣ => IwasawaThree.Arch.archEquiv.symm ((r⁻¹ : ℝˣ) : ℝ)
    exact IwasawaThree.Arch.continuous_archEquiv_symm.comp Units.continuous_coe_inv

private theorem IwasawaThree.Arch.glEquivReal_upperUnipotent3 (x y z : InfiniteAdeleRing ℚ) :
    IwasawaThree.Arch.glEquivReal (upperUnipotent3 x y z) =
      upperUnipotent3 (IwasawaThree.Arch.archEquiv x) (IwasawaThree.Arch.archEquiv y)
        (IwasawaThree.Arch.archEquiv z) := by
  apply Units.ext
  rw [IwasawaThree.Arch.val_glEquivReal, upperUnipotent3_coe, upperUnipotent3_coe]
  ext i j
  fin_cases i <;> fin_cases j <;> simp

private theorem IwasawaThree.Arch.glEquivReal_diagGL (t : Fin 3 → (InfiniteAdeleRing ℚ)ˣ) :
    IwasawaThree.Arch.glEquivReal (IwasawaThree.diagGL t) =
      IwasawaThree.diagGL fun i => IwasawaThree.Arch.unitsEquiv (t i) := by
  apply Units.ext
  rw [IwasawaThree.Arch.val_glEquivReal, IwasawaThree.val_diagGL, IwasawaThree.val_diagGL,
    Matrix.diagonal_map (map_zero IwasawaThree.Arch.archEquiv)]
  rfl

private theorem IwasawaThree.Arch.glEquivReal_mem_iff (k : GL (Fin 3) (InfiniteAdeleRing ℚ)) :
    IwasawaThree.Arch.glEquivReal k ∈ orthogonalSubgroup3 ↔ k ∈ IwasawaThree.orthSubgroupInf := by
  show ((IwasawaThree.Arch.glEquivReal k : GL (Fin 3) ℝ) : Matrix (Fin 3) (Fin 3) ℝ).transpose *
      (IwasawaThree.Arch.glEquivReal k : GL (Fin 3) ℝ) = 1 ↔
    (k : Matrix (Fin 3) (Fin 3) (InfiniteAdeleRing ℚ)).transpose * k = 1
  rw [IwasawaThree.Arch.val_glEquivReal, ← Matrix.transpose_map, ← Matrix.map_mul]
  constructor
  · intro h
    apply (IwasawaThree.Arch.archEquiv.mapMatrix (m := Fin 3)).injective
    rw [map_one]
    exact h
  · intro h
    rw [h]
    exact Matrix.map_one _ (map_zero _) (map_one _)

private noncomputable def IwasawaThree.Arch.orthEquiv : IwasawaThree.orthSubgroupInf ≃* orthogonalSubgroup3 :=
  (IwasawaThree.Arch.glEquivReal.subgroupMap IwasawaThree.orthSubgroupInf).trans
    (MulEquiv.subgroupCongr (by
      ext h
      show h ∈ Subgroup.map IwasawaThree.Arch.glEquivReal.toMonoidHom IwasawaThree.orthSubgroupInf ↔ _
      rw [Subgroup.mem_map_equiv, ← IwasawaThree.Arch.glEquivReal_mem_iff, MulEquiv.apply_symm_apply]))

private theorem IwasawaThree.Arch.coe_orthEquiv (k : IwasawaThree.orthSubgroupInf) :
    ((IwasawaThree.Arch.orthEquiv k : orthogonalSubgroup3) : GL (Fin 3) ℝ) =
      IwasawaThree.Arch.glEquivReal (k : GL (Fin 3) (InfiniteAdeleRing ℚ)) := rfl

private theorem IwasawaThree.Arch.coe_orthEquiv_symm (k : orthogonalSubgroup3) :
    ((IwasawaThree.Arch.orthEquiv.symm k : IwasawaThree.orthSubgroupInf) : GL (Fin 3) (InfiniteAdeleRing ℚ)) =
      IwasawaThree.Arch.glEquivReal.symm (k : GL (Fin 3) ℝ) := rfl

private theorem IwasawaThree.Arch.continuous_orthEquiv : Continuous IwasawaThree.Arch.orthEquiv := by
  refine continuous_induced_rng.2 ?_
  have h : (Subtype.val ∘ ⇑IwasawaThree.Arch.orthEquiv) = ⇑IwasawaThree.Arch.glEquivReal ∘ Subtype.val :=
    funext IwasawaThree.Arch.coe_orthEquiv
  rw [h]
  exact IwasawaThree.Arch.continuous_glEquivReal.comp continuous_subtype_val

private theorem IwasawaThree.Arch.continuous_orthEquiv_symm : Continuous IwasawaThree.Arch.orthEquiv.symm := by
  refine continuous_induced_rng.2 ?_
  have h : (Subtype.val ∘ ⇑IwasawaThree.Arch.orthEquiv.symm) =
      ⇑IwasawaThree.Arch.glEquivReal.symm ∘ Subtype.val :=
    funext IwasawaThree.Arch.coe_orthEquiv_symm
  rw [h]
  exact IwasawaThree.Arch.continuous_glEquivReal_symm.comp continuous_subtype_val

private theorem IwasawaThree.Arch.distribHaarChar_real (r : ℝˣ) : distribHaarChar ℝ r = ‖(r : ℝ)‖₊ := by
  refine distribHaarChar_eq_of_measure_smul_eq_mul (μ := (volume : Measure ℝ)) (s := Set.Icc (0 : ℝ) 1)
    (by simp) (by simp) ?_
  rw [← Set.preimage_smul_inv]
  simp only [Units.smul_def, smul_eq_mul]
  rw [Real.volume_preimage_mul_left (Units.ne_zero _), Units.val_inv_eq_inv_val, inv_inv, ← enorm_eq_nnnorm,
    Real.enorm_eq_ofReal_abs]

private theorem IwasawaThree.Arch.distribHaarChar_infiniteAdele_eq_real (u : (InfiniteAdeleRing ℚ)ˣ) :
    distribHaarChar (InfiniteAdeleRing ℚ) u = distribHaarChar ℝ (IwasawaThree.Arch.unitsEquiv u) := by
  letI : MeasurableSpace (InfiniteAdeleRing ℚ) := borel _
  haveI : BorelSpace (InfiniteAdeleRing ℚ) := ⟨rfl⟩
  have hsymm : Measurable IwasawaThree.Arch.archEquiv.symm := IwasawaThree.Arch.continuous_archEquiv_symm.measurable
  set μ : Measure (InfiniteAdeleRing ℚ) := Measure.map IwasawaThree.Arch.archEquiv.symm volume with hμ
  haveI : μ.IsAddHaarMeasure :=
    IwasawaThree.Arch.archEquiv.symm.toAddEquiv.isAddHaarMeasure_map volume
      IwasawaThree.Arch.continuous_archEquiv_symm IwasawaThree.Arch.continuous_archEquiv
  haveI : μ.Regular := by
    have h := Measure.Regular.map (μ := (volume : Measure ℝ))
      (Homeomorph.mk IwasawaThree.Arch.archEquiv.toEquiv IwasawaThree.Arch.continuous_archEquiv
        IwasawaThree.Arch.continuous_archEquiv_symm).symm
    exact h
  set s : Set (InfiniteAdeleRing ℚ) := IwasawaThree.Arch.archEquiv ⁻¹' Set.Icc (0 : ℝ) 1 with hs_def
  have hs_meas : MeasurableSet s := measurableSet_Icc.preimage IwasawaThree.Arch.continuous_archEquiv.measurable
  have hpre : IwasawaThree.Arch.archEquiv.symm ⁻¹' s = Set.Icc (0 : ℝ) 1 := by
    ext r
    simp [hs_def]
  have hμs : μ s = 1 := by
    rw [hμ, Measure.map_apply hsymm hs_meas, hpre, Real.volume_Icc]
    simp
  have hm : Measurable fun x : InfiniteAdeleRing ℚ => ((u⁻¹ : (InfiniteAdeleRing ℚ)ˣ) : InfiniteAdeleRing ℚ) * x :=
    (continuous_const.mul continuous_id).measurable
  have hpre_mul : IwasawaThree.Arch.archEquiv.symm ⁻¹'
        ((fun x : InfiniteAdeleRing ℚ => ((u⁻¹ : (InfiniteAdeleRing ℚ)ˣ) : InfiniteAdeleRing ℚ) * x) ⁻¹' s) =
      (fun r : ℝ => (((IwasawaThree.Arch.unitsEquiv u)⁻¹ : ℝˣ) : ℝ) * r) ⁻¹' Set.Icc (0 : ℝ) 1 := by
    ext r
    show IwasawaThree.Arch.archEquiv (((u⁻¹ : (InfiniteAdeleRing ℚ)ˣ) : InfiniteAdeleRing ℚ) *
        IwasawaThree.Arch.archEquiv.symm r) ∈ Set.Icc (0 : ℝ) 1 ↔
      (((IwasawaThree.Arch.unitsEquiv u)⁻¹ : ℝˣ) : ℝ) * r ∈ Set.Icc (0 : ℝ) 1
    rw [map_mul, RingEquiv.apply_symm_apply, IwasawaThree.Arch.val_unitsEquiv_inv]
  refine distribHaarChar_eq_of_measure_smul_eq_mul (μ := μ) (s := s) (by rw [hμs]; exact one_ne_zero)
    (by rw [hμs]; exact ENNReal.one_ne_top) ?_
  rw [← Set.preimage_smul_inv]
  simp only [Units.smul_def, smul_eq_mul]
  rw [hμ, Measure.map_apply hsymm (hs_meas.preimage hm), Measure.map_apply hsymm hs_meas, hpre_mul, hpre,
    Real.volume_preimage_mul_left (Units.ne_zero _), IwasawaThree.Arch.distribHaarChar_real,
    Units.val_inv_eq_inv_val, inv_inv, ← enorm_eq_nnnorm, Real.enorm_eq_ofReal_abs]

private theorem IwasawaThree.distribHaarChar_infiniteAdele_eq (u : (InfiniteAdeleRing ℚ)ˣ) :
    distribHaarChar (InfiniteAdeleRing ℚ) u =
      ‖AutomorphicForm.StandardKernel.realCoord (u : InfiniteAdeleRing ℚ)‖₊ := by
  rw [IwasawaThree.Arch.distribHaarChar_infiniteAdele_eq_real, IwasawaThree.Arch.distribHaarChar_real]
  rfl

private theorem IwasawaThree.coe_distribHaarChar_infiniteAdele (u : (InfiniteAdeleRing ℚ)ˣ) :
    ((distribHaarChar (InfiniteAdeleRing ℚ) u : NNReal) : ℝ) =
      |AutomorphicForm.StandardKernel.realCoord (u : InfiniteAdeleRing ℚ)| := by
  rw [IwasawaThree.distribHaarChar_infiniteAdele_eq, coe_nnnorm, Real.norm_eq_abs]

private noncomputable def IwasawaThree.iwMapA
    (q : ((InfiniteAdeleRing ℚ × InfiniteAdeleRing ℚ × InfiniteAdeleRing ℚ) × (Fin 3 → (InfiniteAdeleRing ℚ)ˣ)) ×
      IwasawaThree.orthSubgroupInf) : GL (Fin 3) (InfiniteAdeleRing ℚ) :=
  upperUnipotent3 q.1.1.1 q.1.1.2.1 q.1.1.2.2 *
    Units.map (Matrix.diagonalRingHom (Fin 3) (InfiniteAdeleRing ℚ)).toMonoidHom (MulEquiv.piUnits.symm q.1.2) *
    (q.2 : GL (Fin 3) (InfiniteAdeleRing ℚ))

private noncomputable def IwasawaThree.densA (t : Fin 3 → (InfiniteAdeleRing ℚ)ˣ) : ENNReal :=
  ENNReal.ofReal (((distribHaarChar (InfiniteAdeleRing ℚ) (t 0) : NNReal) : ℝ)⁻¹ ^ 2 *
    ((distribHaarChar (InfiniteAdeleRing ℚ) (t 2) : NNReal) : ℝ) ^ 2)

private noncomputable def IwasawaThree.nuA
    [MeasurableSpace (InfiniteAdeleRing ℚ)] [MeasurableSpace (InfiniteAdeleRing ℚ)ˣ]
    [MeasurableSpace (GL (Fin 3) (InfiniteAdeleRing ℚ))]
    (lam : Measure (InfiniteAdeleRing ℚ)) (tau : Measure (InfiniteAdeleRing ℚ)ˣ)
    (nu : Measure IwasawaThree.orthSubgroupInf) : Measure (GL (Fin 3) (InfiniteAdeleRing ℚ)) :=
  Measure.map IwasawaThree.iwMapA
    (((lam.prod (lam.prod lam)).prod ((Measure.pi fun _ : Fin 3 => tau).withDensity IwasawaThree.densA)).prod nu)

private noncomputable def IwasawaThree.iwMap (K : Subgroup (AdelicGL 3 (𝓞 ℚ) ℚ))
    (q : ((AdeleRing (𝓞 ℚ) ℚ × AdeleRing (𝓞 ℚ) ℚ × AdeleRing (𝓞 ℚ) ℚ) × (Fin 3 → (AdeleRing (𝓞 ℚ) ℚ)ˣ)) × K) :
    AdelicGL 3 (𝓞 ℚ) ℚ :=
  upperUnipotent3 q.1.1.1 q.1.1.2.1 q.1.1.2.2 *
    Units.map (Matrix.diagonalRingHom (Fin 3) (AdeleRing (𝓞 ℚ) ℚ)).toMonoidHom (MulEquiv.piUnits.symm q.1.2) *
    (q.2 : AdelicGL 3 (𝓞 ℚ) ℚ)

namespace IwasawaThree

private noncomputable def _root_.LanglandsTunnell.CubicInduction.WhittakerBlock.IwasawaThree.dens (t : Fin 3 → (AdeleRing (𝓞 ℚ) ℚ)ˣ) : ENNReal :=
  ENNReal.ofReal ((NumberField.TateGlobal.ideleNorm ℚ (t 0))⁻¹ ^ 2 * NumberField.TateGlobal.ideleNorm ℚ (t 2) ^ 2)

end IwasawaThree
p2m_export "LanglandsTunnell.CubicInduction.WhittakerBlock" "IwasawaThree.dens"

private def IwasawaThree.regroupN
    (p : (InfiniteAdeleRing ℚ × InfiniteAdeleRing ℚ × InfiniteAdeleRing ℚ) ×
      (FiniteAdeleRing (𝓞 ℚ) ℚ × FiniteAdeleRing (𝓞 ℚ) ℚ × FiniteAdeleRing (𝓞 ℚ) ℚ)) :
    AdeleRing (𝓞 ℚ) ℚ × AdeleRing (𝓞 ℚ) ℚ × AdeleRing (𝓞 ℚ) ℚ :=
  ((p.1.1, p.2.1), (p.1.2.1, p.2.2.1), (p.1.2.2, p.2.2.2))

private noncomputable def IwasawaThree.regroupT
    (p : (Fin 3 → (InfiniteAdeleRing ℚ)ˣ) × (Fin 3 → (FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ)) :
    Fin 3 → (AdeleRing (𝓞 ℚ) ℚ)ˣ :=
  fun i => IwasawaThree.ideleSplit.symm (p.1 i, p.2 i)

private theorem IwasawaThree.glSplit_symm_mem (K : Subgroup (AdelicGL 3 (𝓞 ℚ) ℚ))
    (hK : ∀ k : AdelicGL 3 (𝓞 ℚ) ℚ, k ∈ K ↔ archComponent3 (𝓞 ℚ) ℚ k ∈ orth3 ∧
      ∀ p : HeightOneSpectrum (𝓞 ℚ), componentAt3 (𝓞 ℚ) ℚ p k ∈ localMaximalCompact3 (𝓞 ℚ) ℚ p)
    (a : IwasawaThree.orthSubgroupInf) (b : IwasawaThree.intGL3f) :
    IwasawaThree.glSplit.symm ((a : GL (Fin 3) (InfiniteAdeleRing ℚ)), (b : GL (Fin 3) (FiniteAdeleRing (𝓞 ℚ) ℚ))) ∈
      K := by
  have h := IwasawaThree.glSplit_apply
    (IwasawaThree.glSplit.symm ((a : GL (Fin 3) (InfiniteAdeleRing ℚ)), (b : GL (Fin 3) (FiniteAdeleRing (𝓞 ℚ) ℚ))))
  rw [MulEquiv.apply_symm_apply, Prod.mk.injEq] at h
  refine (hK _).2 ⟨?_, fun p => ?_⟩
  · show Matrix.GeneralLinearGroup.map (AdelicLevel.adeleArch (𝓞 ℚ) ℚ) _ ∈ orth3
    rw [← h.1]
    exact a.2
  · show Matrix.GeneralLinearGroup.map ((AdelicLevel.finAdeleEval (𝓞 ℚ) ℚ p).comp (AdelicLevel.adeleFin (𝓞 ℚ) ℚ)) _ ∈
      localMaximalCompact3 (𝓞 ℚ) ℚ p
    rw [Matrix.GeneralLinearGroup.map_comp, MonoidHom.comp_apply, ← h.2]
    exact (IwasawaThree.mem_intGL3f_iff _).1 b.2 p

private noncomputable def IwasawaThree.regroupK (K : Subgroup (AdelicGL 3 (𝓞 ℚ) ℚ))
    (hK : ∀ k : AdelicGL 3 (𝓞 ℚ) ℚ, k ∈ K ↔ archComponent3 (𝓞 ℚ) ℚ k ∈ orth3 ∧
      ∀ p : HeightOneSpectrum (𝓞 ℚ), componentAt3 (𝓞 ℚ) ℚ p k ∈ localMaximalCompact3 (𝓞 ℚ) ℚ p)
    (p : IwasawaThree.orthSubgroupInf × IwasawaThree.intGL3f) : K :=
  ⟨IwasawaThree.glSplit.symm ((p.1 : GL (Fin 3) (InfiniteAdeleRing ℚ)), (p.2 : GL (Fin 3) (FiniteAdeleRing (𝓞 ℚ) ℚ))),
    IwasawaThree.glSplit_symm_mem K hK p.1 p.2⟩

private theorem IwasawaThree.coe_regroupK (K : Subgroup (AdelicGL 3 (𝓞 ℚ) ℚ))
    (hK : ∀ k : AdelicGL 3 (𝓞 ℚ) ℚ, k ∈ K ↔ archComponent3 (𝓞 ℚ) ℚ k ∈ orth3 ∧
      ∀ p : HeightOneSpectrum (𝓞 ℚ), componentAt3 (𝓞 ℚ) ℚ p k ∈ localMaximalCompact3 (𝓞 ℚ) ℚ p)
    (p : IwasawaThree.orthSubgroupInf × IwasawaThree.intGL3f) :
    ((IwasawaThree.regroupK K hK p : K) : AdelicGL 3 (𝓞 ℚ) ℚ) =
      IwasawaThree.glSplit.symm
        ((p.1 : GL (Fin 3) (InfiniteAdeleRing ℚ)), (p.2 : GL (Fin 3) (FiniteAdeleRing (𝓞 ℚ) ℚ))) :=
  rfl

private theorem IwasawaThree.Arch.glMap_upperUnipotent3
    {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S) (x y z : R) :
    Matrix.GeneralLinearGroup.map f (upperUnipotent3 x y z) = upperUnipotent3 (f x) (f y) (f z) := by
  apply Units.ext
  show ((upperUnipotent3 x y z : GL (Fin 3) R) : Matrix (Fin 3) (Fin 3) R).map f = _
  rw [upperUnipotent3_coe, upperUnipotent3_coe]
  ext i j
  fin_cases i <;> fin_cases j <;> simp

private theorem IwasawaThree.Arch.glMap_diagGL {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S) (t : Fin 3 → Rˣ) :
    Matrix.GeneralLinearGroup.map f (IwasawaThree.diagGL t) =
      IwasawaThree.diagGL fun i => Units.map f.toMonoidHom (t i) := by
  apply Units.ext
  show ((IwasawaThree.diagGL t : GL (Fin 3) R) : Matrix (Fin 3) (Fin 3) R).map f = _
  rw [IwasawaThree.val_diagGL, IwasawaThree.val_diagGL, Matrix.diagonal_map (map_zero f)]
  rfl

private theorem IwasawaThree.Arch.unitsMap_adeleArch_regroupT (ta : Fin 3 → (InfiniteAdeleRing ℚ)ˣ)
    (tf : Fin 3 → (FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) (i : Fin 3) :
    Units.map (AdelicLevel.adeleArch (𝓞 ℚ) ℚ).toMonoidHom (IwasawaThree.regroupT (ta, tf) i) = ta i := by
  have h := congrArg Prod.fst (IwasawaThree.ideleSplit.apply_symm_apply (ta i, tf i))
  exact (Units.ext rfl).trans h

private theorem IwasawaThree.Arch.unitsMap_adeleFin_regroupT (ta : Fin 3 → (InfiniteAdeleRing ℚ)ˣ)
    (tf : Fin 3 → (FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) (i : Fin 3) :
    Units.map (AdelicLevel.adeleFin (𝓞 ℚ) ℚ).toMonoidHom (IwasawaThree.regroupT (ta, tf) i) = tf i := by
  have h := congrArg Prod.snd (IwasawaThree.ideleSplit.apply_symm_apply (ta i, tf i))
  exact (Units.ext rfl).trans h

private theorem IwasawaThree.glSplit_symm_iwMap (K : Subgroup (AdelicGL 3 (𝓞 ℚ) ℚ))
    (hK : ∀ k : AdelicGL 3 (𝓞 ℚ) ℚ, k ∈ K ↔ archComponent3 (𝓞 ℚ) ℚ k ∈ orth3 ∧
      ∀ p : HeightOneSpectrum (𝓞 ℚ), componentAt3 (𝓞 ℚ) ℚ p k ∈ localMaximalCompact3 (𝓞 ℚ) ℚ p)
    (qa : ((InfiniteAdeleRing ℚ × InfiniteAdeleRing ℚ × InfiniteAdeleRing ℚ) × (Fin 3 → (InfiniteAdeleRing ℚ)ˣ)) ×
      IwasawaThree.orthSubgroupInf)
    (qf : ((FiniteAdeleRing (𝓞 ℚ) ℚ × FiniteAdeleRing (𝓞 ℚ) ℚ × FiniteAdeleRing (𝓞 ℚ) ℚ) ×
      (Fin 3 → (FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ)) × IwasawaThree.intGL3f) :
    IwasawaThree.glSplit.symm (IwasawaThree.iwMapA qa, IwasawaThree.iwMapF qf) =
      IwasawaThree.iwMap K ((IwasawaThree.regroupN (qa.1.1, qf.1.1), IwasawaThree.regroupT (qa.1.2, qf.1.2)),
        IwasawaThree.regroupK K hK (qa.2, qf.2)) := by
  rw [MulEquiv.symm_apply_eq]
  simp only [IwasawaThree.iwMap]
  rw [map_mul, map_mul, IwasawaThree.coe_regroupK, MulEquiv.apply_symm_apply, IwasawaThree.glSplit_apply,
    IwasawaThree.glSplit_apply]
  have hN₁ : Matrix.GeneralLinearGroup.map (AdelicLevel.adeleArch (𝓞 ℚ) ℚ)
      (upperUnipotent3 (IwasawaThree.regroupN (qa.1.1, qf.1.1)).1 (IwasawaThree.regroupN (qa.1.1, qf.1.1)).2.1
        (IwasawaThree.regroupN (qa.1.1, qf.1.1)).2.2) = upperUnipotent3 qa.1.1.1 qa.1.1.2.1 qa.1.1.2.2 :=
    IwasawaThree.Arch.glMap_upperUnipotent3 _ _ _ _
  have hN₂ : Matrix.GeneralLinearGroup.map (AdelicLevel.adeleFin (𝓞 ℚ) ℚ)
      (upperUnipotent3 (IwasawaThree.regroupN (qa.1.1, qf.1.1)).1 (IwasawaThree.regroupN (qa.1.1, qf.1.1)).2.1
        (IwasawaThree.regroupN (qa.1.1, qf.1.1)).2.2) = upperUnipotent3 qf.1.1.1 qf.1.1.2.1 qf.1.1.2.2 :=
    IwasawaThree.Arch.glMap_upperUnipotent3 _ _ _ _
  have hT₁ : Matrix.GeneralLinearGroup.map (AdelicLevel.adeleArch (𝓞 ℚ) ℚ)
      (Units.map (Matrix.diagonalRingHom (Fin 3) (AdeleRing (𝓞 ℚ) ℚ)).toMonoidHom
        (MulEquiv.piUnits.symm (IwasawaThree.regroupT (qa.1.2, qf.1.2)))) = IwasawaThree.diagGL qa.1.2 := by
    show Matrix.GeneralLinearGroup.map (AdelicLevel.adeleArch (𝓞 ℚ) ℚ)
      (IwasawaThree.diagGL (IwasawaThree.regroupT (qa.1.2, qf.1.2))) = _
    rw [IwasawaThree.Arch.glMap_diagGL]
    congr 1
  have hT₂ : Matrix.GeneralLinearGroup.map (AdelicLevel.adeleFin (𝓞 ℚ) ℚ)
      (Units.map (Matrix.diagonalRingHom (Fin 3) (AdeleRing (𝓞 ℚ) ℚ)).toMonoidHom
        (MulEquiv.piUnits.symm (IwasawaThree.regroupT (qa.1.2, qf.1.2)))) = IwasawaThree.diagGL qf.1.2 := by
    show Matrix.GeneralLinearGroup.map (AdelicLevel.adeleFin (𝓞 ℚ) ℚ)
      (IwasawaThree.diagGL (IwasawaThree.regroupT (qa.1.2, qf.1.2))) = _
    rw [IwasawaThree.Arch.glMap_diagGL]
    congr 1
  rw [Prod.mk_mul_mk, Prod.mk_mul_mk, hN₁, hN₂, hT₁, hT₂]
  rfl

private theorem IwasawaThree.exists_lintegral_infiniteAdele_eq_mul_lintegral_iwasawa
    [MeasurableSpace (GL (Fin 3) (InfiniteAdeleRing ℚ))] [BorelSpace (GL (Fin 3) (InfiniteAdeleRing ℚ))]
    (μa : Measure (GL (Fin 3) (InfiniteAdeleRing ℚ))) [μa.IsHaarMeasure]
    (nu : Measure IwasawaThree.orthSubgroupInf) [nu.IsHaarMeasure]
    [MeasurableSpace (InfiniteAdeleRing ℚ)] [BorelSpace (InfiniteAdeleRing ℚ)]
    (lam : Measure (InfiniteAdeleRing ℚ)) [lam.IsAddHaarMeasure]
    [MeasurableSpace (InfiniteAdeleRing ℚ)ˣ] [BorelSpace (InfiniteAdeleRing ℚ)ˣ]
    (tau : Measure (InfiniteAdeleRing ℚ)ˣ) [tau.IsHaarMeasure] :
    ∃ c : ℝ≥0∞, c ≠ 0 ∧ c ≠ ⊤ ∧ ∀ φ : GL (Fin 3) (InfiniteAdeleRing ℚ) → ℝ≥0∞, Measurable φ →
      ∫⁻ g, φ g ∂μa =
        c * ∫⁻ x : InfiniteAdeleRing ℚ × InfiniteAdeleRing ℚ × InfiniteAdeleRing ℚ,
          ∫⁻ t : Fin 3 → (InfiniteAdeleRing ℚ)ˣ, ∫⁻ k : IwasawaThree.orthSubgroupInf,
            φ (upperUnipotent3 x.1 x.2.1 x.2.2 * IwasawaThree.diagGL t * (k : GL (Fin 3) (InfiniteAdeleRing ℚ))) *
              ENNReal.ofReal (((distribHaarChar (InfiniteAdeleRing ℚ) (t 0) : NNReal) : ℝ)⁻¹ ^ 2 *
                ((distribHaarChar (InfiniteAdeleRing ℚ) (t 2) : NNReal) : ℝ) ^ 2)
          ∂nu ∂(Measure.pi fun _ : Fin 3 => tau) ∂(lam.prod (lam.prod lam)) := by

  letI : MeasurableSpace (GL (Fin 3) ℝ) := borel _
  haveI : BorelSpace (GL (Fin 3) ℝ) := ⟨rfl⟩
  letI : MeasurableSpace ℝˣ := borel _
  haveI : BorelSpace ℝˣ := ⟨rfl⟩
  haveI : BorelSpace IwasawaThree.orthSubgroupInf :=
    inferInstanceAs (BorelSpace (IwasawaThree.orthSubgroupInf : Set (GL (Fin 3) (InfiniteAdeleRing ℚ))))
  haveI : BorelSpace orthogonalSubgroup3 := inferInstanceAs (BorelSpace (orthogonalSubgroup3 : Set (GL (Fin 3) ℝ)))

  let eG : GL (Fin 3) (InfiniteAdeleRing ℚ) ≃ᵐ GL (Fin 3) ℝ :=
    (Homeomorph.mk IwasawaThree.Arch.glEquivReal.toEquiv IwasawaThree.Arch.continuous_glEquivReal
      IwasawaThree.Arch.continuous_glEquivReal_symm).toMeasurableEquiv
  let eK : IwasawaThree.orthSubgroupInf ≃ᵐ orthogonalSubgroup3 :=
    (Homeomorph.mk IwasawaThree.Arch.orthEquiv.toEquiv IwasawaThree.Arch.continuous_orthEquiv
      IwasawaThree.Arch.continuous_orthEquiv_symm).toMeasurableEquiv
  let eA : InfiniteAdeleRing ℚ ≃ᵐ ℝ :=
    (Homeomorph.mk IwasawaThree.Arch.archEquiv.toEquiv IwasawaThree.Arch.continuous_archEquiv
      IwasawaThree.Arch.continuous_archEquiv_symm).toMeasurableEquiv
  let eU : (InfiniteAdeleRing ℚ)ˣ ≃ᵐ ℝˣ :=
    (Homeomorph.mk IwasawaThree.Arch.unitsEquiv.toEquiv IwasawaThree.Arch.continuous_unitsEquiv
      IwasawaThree.Arch.continuous_unitsEquiv_symm).toMeasurableEquiv
  have heG : (eG : GL (Fin 3) (InfiniteAdeleRing ℚ) → GL (Fin 3) ℝ) = IwasawaThree.Arch.glEquivReal := rfl
  have heK : (eK : IwasawaThree.orthSubgroupInf → orthogonalSubgroup3) = IwasawaThree.Arch.orthEquiv := rfl
  have heA : (eA : InfiniteAdeleRing ℚ → ℝ) = IwasawaThree.Arch.archEquiv := rfl
  have heU : (eU : (InfiniteAdeleRing ℚ)ˣ → ℝˣ) = IwasawaThree.Arch.unitsEquiv := rfl

  haveI hμ' : (Measure.map eG μa).IsHaarMeasure := by
    rw [heG]
    exact IwasawaThree.Arch.glEquivReal.isHaarMeasure_map μa IwasawaThree.Arch.continuous_glEquivReal
      IwasawaThree.Arch.continuous_glEquivReal_symm
  haveI hν' : (Measure.map eK nu).IsHaarMeasure := by
    rw [heK]
    exact IwasawaThree.Arch.orthEquiv.isHaarMeasure_map nu IwasawaThree.Arch.continuous_orthEquiv
      IwasawaThree.Arch.continuous_orthEquiv_symm
  haveI hlam' : (Measure.map eA lam).IsAddHaarMeasure := by
    rw [heA]
    exact IwasawaThree.Arch.archEquiv.toAddEquiv.isAddHaarMeasure_map lam IwasawaThree.Arch.continuous_archEquiv
      IwasawaThree.Arch.continuous_archEquiv_symm
  haveI htau' : (Measure.map eU tau).IsHaarMeasure := by
    rw [heU]
    exact IwasawaThree.Arch.unitsEquiv.isHaarMeasure_map tau IwasawaThree.Arch.continuous_unitsEquiv
      IwasawaThree.Arch.continuous_unitsEquiv_symm
  obtain ⟨c, hc0, hct, hc⟩ := IwasawaThree.exists_lintegral_real_eq_mul_lintegral_iwasawa (Measure.map eG μa)
    (Measure.map eK nu) (Measure.map eA lam) (Measure.map eU tau)
  refine ⟨c, hc0, hct, fun φ hφ => ?_⟩

  set ψ : GL (Fin 3) ℝ → ℝ≥0∞ := fun h => φ (IwasawaThree.Arch.glEquivReal.symm h) with hψ_def
  have hψ : Measurable ψ := hφ.comp IwasawaThree.Arch.continuous_glEquivReal_symm.measurable
  have hleft : ∫⁻ g, φ g ∂μa = ∫⁻ h, ψ h ∂(Measure.map eG μa) := by
    rw [lintegral_map_equiv ψ eG]
    refine lintegral_congr fun g => ?_
    simp only [hψ_def, heG, MulEquiv.symm_apply_apply]

  have hprod : (Measure.map eA lam).prod ((Measure.map eA lam).prod (Measure.map eA lam)) =
      Measure.map (eA.prodCongr (eA.prodCongr eA)) (lam.prod (lam.prod lam)) := by
    rw [Measure.map_prod_map _ _ eA.measurable eA.measurable, Measure.map_prod_map _ _ eA.measurable
      (eA.measurable.prodMap eA.measurable)]
    rfl
  have hpi : (Measure.pi fun _ : Fin 3 => Measure.map eU tau) =
      Measure.map (MeasurableEquiv.piCongrRight fun _ : Fin 3 => eU) (Measure.pi fun _ : Fin 3 => tau) :=
    (measurePreserving_pi (fun _ : Fin 3 => tau) (fun _ : Fin 3 => Measure.map eU tau)
      (fun _ => ⟨eU.measurable, rfl⟩)).map_eq.symm

  have hpoint : ∀ (x : InfiniteAdeleRing ℚ × InfiniteAdeleRing ℚ × InfiniteAdeleRing ℚ)
      (t : Fin 3 → (InfiniteAdeleRing ℚ)ˣ) (k : IwasawaThree.orthSubgroupInf),
      IwasawaThree.Arch.glEquivReal.symm
          (upperUnipotent3 (IwasawaThree.Arch.archEquiv x.1) (IwasawaThree.Arch.archEquiv x.2.1)
              (IwasawaThree.Arch.archEquiv x.2.2) *
            IwasawaThree.diagGL (fun i => IwasawaThree.Arch.unitsEquiv (t i)) *
            ((IwasawaThree.Arch.orthEquiv k : orthogonalSubgroup3) : GL (Fin 3) ℝ)) =
        upperUnipotent3 x.1 x.2.1 x.2.2 * IwasawaThree.diagGL t * (k : GL (Fin 3) (InfiniteAdeleRing ℚ)) := by
    intro x t k
    rw [← IwasawaThree.Arch.glEquivReal_upperUnipotent3, ← IwasawaThree.Arch.glEquivReal_diagGL,
      IwasawaThree.Arch.coe_orthEquiv, ← map_mul, ← map_mul, MulEquiv.symm_apply_apply]
  rw [hleft, hc ψ hψ, hprod, lintegral_map_equiv, hpi]
  congr 1
  refine lintegral_congr fun x => ?_
  rw [lintegral_map_equiv]
  refine lintegral_congr fun t => ?_
  rw [lintegral_map_equiv]
  refine lintegral_congr fun k => ?_
  simp only [hψ_def, IwasawaThree.coe_distribHaarChar_infiniteAdele]
  rw [← hpoint x t k]
  rfl

private abbrev IwasawaThree.Arch.compactSpace_orthSubgroupInf : CompactSpace IwasawaThree.orthSubgroupInf :=
  (Homeomorph.mk IwasawaThree.Arch.orthEquiv.symm.toEquiv IwasawaThree.Arch.continuous_orthEquiv_symm
    IwasawaThree.Arch.continuous_orthEquiv).compactSpace
attribute [local instance] IwasawaThree.Arch.compactSpace_orthSubgroupInf

private theorem IwasawaThree.Arch.continuous_iwMapA : Continuous IwasawaThree.iwMapA := by
  have h₁ := IwasawaThree.continuous_upperUnipotent3 (A := InfiniteAdeleRing ℚ)
  have h₂ := IwasawaThree.continuous_diagUnits (A := InfiniteAdeleRing ℚ)
  unfold IwasawaThree.iwMapA
  exact ((h₁.comp (continuous_fst.comp continuous_fst)).mul (h₂.comp (continuous_snd.comp continuous_fst))).mul
    (continuous_subtype_val.comp continuous_snd)

private theorem IwasawaThree.Arch.measurable_iwMapA
    [MeasurableSpace (InfiniteAdeleRing ℚ)] [BorelSpace (InfiniteAdeleRing ℚ)]
    [MeasurableSpace (InfiniteAdeleRing ℚ)ˣ] [BorelSpace (InfiniteAdeleRing ℚ)ˣ]
    [MeasurableSpace (GL (Fin 3) (InfiniteAdeleRing ℚ))] [BorelSpace (GL (Fin 3) (InfiniteAdeleRing ℚ))] :
    Measurable IwasawaThree.iwMapA :=
  IwasawaThree.Arch.continuous_iwMapA.measurable

private theorem IwasawaThree.Arch.continuous_coe_distribHaarChar (i : Fin 3) :
    Continuous fun t : Fin 3 → (InfiniteAdeleRing ℚ)ˣ =>
      ((distribHaarChar (InfiniteAdeleRing ℚ) (t i) : NNReal) : ℝ) := by
  have h : (fun t : Fin 3 → (InfiniteAdeleRing ℚ)ˣ => ((distribHaarChar (InfiniteAdeleRing ℚ) (t i) : NNReal) : ℝ)) =
      fun t => |IwasawaThree.Arch.archEquiv ((t i : (InfiniteAdeleRing ℚ)ˣ) : InfiniteAdeleRing ℚ)| :=
    funext fun t => IwasawaThree.coe_distribHaarChar_infiniteAdele (t i)
  rw [h]
  exact continuous_abs.comp
    (IwasawaThree.Arch.continuous_archEquiv.comp (Units.continuous_val.comp (continuous_apply i)))

private theorem IwasawaThree.Arch.continuous_densA : Continuous IwasawaThree.densA := by
  have h0 : ∀ t : Fin 3 → (InfiniteAdeleRing ℚ)ˣ, ((distribHaarChar (InfiniteAdeleRing ℚ) (t 0) : NNReal) : ℝ) ≠ 0 :=
    fun t => (NNReal.coe_pos.2 distribHaarChar_pos).ne'
  unfold IwasawaThree.densA
  exact ENNReal.continuous_ofReal.comp
    ((((IwasawaThree.Arch.continuous_coe_distribHaarChar 0).inv₀ h0).pow 2).mul
      ((IwasawaThree.Arch.continuous_coe_distribHaarChar 2).pow 2))

private theorem IwasawaThree.Arch.measurable_densA [MeasurableSpace (InfiniteAdeleRing ℚ)ˣ]
    [BorelSpace (InfiniteAdeleRing ℚ)ˣ] :
    Measurable IwasawaThree.densA :=
  IwasawaThree.Arch.continuous_densA.measurable

private theorem IwasawaThree.Arch.densA_ne_top (t : Fin 3 → (InfiniteAdeleRing ℚ)ˣ) : IwasawaThree.densA t ≠ ⊤ :=
  ENNReal.ofReal_ne_top

private theorem IwasawaThree.Arch.lintegral_nuA
    [MeasurableSpace (GL (Fin 3) (InfiniteAdeleRing ℚ))] [BorelSpace (GL (Fin 3) (InfiniteAdeleRing ℚ))]
    (nu : Measure IwasawaThree.orthSubgroupInf) [nu.IsHaarMeasure]
    [MeasurableSpace (InfiniteAdeleRing ℚ)] [BorelSpace (InfiniteAdeleRing ℚ)]
    (lam : Measure (InfiniteAdeleRing ℚ)) [lam.IsAddHaarMeasure]
    [MeasurableSpace (InfiniteAdeleRing ℚ)ˣ] [BorelSpace (InfiniteAdeleRing ℚ)ˣ]
    (tau : Measure (InfiniteAdeleRing ℚ)ˣ) [tau.IsHaarMeasure]
    (φ : GL (Fin 3) (InfiniteAdeleRing ℚ) → ℝ≥0∞) (hφ : Measurable φ) :
    ∫⁻ g, φ g ∂IwasawaThree.nuA lam tau nu =
      ∫⁻ x : InfiniteAdeleRing ℚ × InfiniteAdeleRing ℚ × InfiniteAdeleRing ℚ,
        ∫⁻ t : Fin 3 → (InfiniteAdeleRing ℚ)ˣ, ∫⁻ k : IwasawaThree.orthSubgroupInf,
          φ (upperUnipotent3 x.1 x.2.1 x.2.2 * IwasawaThree.diagGL t * (k : GL (Fin 3) (InfiniteAdeleRing ℚ))) *
            ENNReal.ofReal (((distribHaarChar (InfiniteAdeleRing ℚ) (t 0) : NNReal) : ℝ)⁻¹ ^ 2 *
              ((distribHaarChar (InfiniteAdeleRing ℚ) (t 2) : NNReal) : ℝ) ^ 2)
        ∂nu ∂(Measure.pi fun _ : Fin 3 => tau) ∂(lam.prod (lam.prod lam)) := by
  have hφA : Measurable fun q => φ (IwasawaThree.iwMapA q) := hφ.comp IwasawaThree.Arch.measurable_iwMapA
  have hinner : Measurable fun p : (InfiniteAdeleRing ℚ × InfiniteAdeleRing ℚ × InfiniteAdeleRing ℚ) ×
      (Fin 3 → (InfiniteAdeleRing ℚ)ˣ) => ∫⁻ k : IwasawaThree.orthSubgroupInf, φ (IwasawaThree.iwMapA (p, k)) ∂nu :=
    hφA.lintegral_prod_right'
  unfold IwasawaThree.nuA
  rw [lintegral_map hφ IwasawaThree.Arch.measurable_iwMapA, lintegral_prod _ hφA.aemeasurable,
    lintegral_prod _ hinner.aemeasurable]
  refine lintegral_congr fun x => ?_
  have hx : Measurable fun t : Fin 3 → (InfiniteAdeleRing ℚ)ˣ =>
      ∫⁻ k : IwasawaThree.orthSubgroupInf, φ (IwasawaThree.iwMapA ((x, t), k)) ∂nu :=
    hinner.comp (measurable_const.prodMk measurable_id)
  rw [lintegral_withDensity_eq_lintegral_mul _ IwasawaThree.Arch.measurable_densA hx]
  refine lintegral_congr fun t => ?_
  show IwasawaThree.densA t * ∫⁻ k : IwasawaThree.orthSubgroupInf, φ (IwasawaThree.iwMapA ((x, t), k)) ∂nu = _
  rw [mul_comm, ← lintegral_mul_const' _ _ (IwasawaThree.Arch.densA_ne_top t)]
  rfl

private theorem IwasawaThree.exists_nuA_eq_smul
    [MeasurableSpace (GL (Fin 3) (InfiniteAdeleRing ℚ))] [BorelSpace (GL (Fin 3) (InfiniteAdeleRing ℚ))]
    (μa : Measure (GL (Fin 3) (InfiniteAdeleRing ℚ))) [μa.IsHaarMeasure]
    (nu : Measure IwasawaThree.orthSubgroupInf) [nu.IsHaarMeasure]
    [MeasurableSpace (InfiniteAdeleRing ℚ)] [BorelSpace (InfiniteAdeleRing ℚ)]
    (lam : Measure (InfiniteAdeleRing ℚ)) [lam.IsAddHaarMeasure]
    [MeasurableSpace (InfiniteAdeleRing ℚ)ˣ] [BorelSpace (InfiniteAdeleRing ℚ)ˣ]
    (tau : Measure (InfiniteAdeleRing ℚ)ˣ) [tau.IsHaarMeasure] :
    ∃ c : ℝ≥0∞, c ≠ 0 ∧ c ≠ ⊤ ∧ IwasawaThree.nuA lam tau nu = c • μa := by
  obtain ⟨c, hc0, hct, hc⟩ := IwasawaThree.exists_lintegral_infiniteAdele_eq_mul_lintegral_iwasawa μa nu lam tau
  refine ⟨c⁻¹, ENNReal.inv_ne_zero.2 hct, ENNReal.inv_ne_top.2 hc0, ?_⟩
  refine Measure.ext_of_lintegral _ fun φ hφ => ?_
  rw [IwasawaThree.Arch.lintegral_nuA nu lam tau φ hφ, lintegral_smul_measure, hc φ hφ, smul_eq_mul, ← mul_assoc,
    ENNReal.inv_mul_cancel hc0 hct, one_mul]

private theorem IwasawaThree.map_prodProdProdComm {α β γ δ : Type*} [MeasurableSpace α] [MeasurableSpace β]
    [MeasurableSpace γ] [MeasurableSpace δ] (μ : Measure α) (ν : Measure β) (ρ : Measure γ) (σ : Measure δ)
    [SFinite μ] [SFinite ν] [SFinite ρ] [SFinite σ] :
    Measure.map (fun p : (α × β) × (γ × δ) => ((p.1.1, p.2.1), (p.1.2, p.2.2))) ((μ.prod ν).prod (ρ.prod σ)) =
      (μ.prod ρ).prod (ν.prod σ) := by
  have h₁ := MeasureTheory.measurePreserving_prodAssoc μ ν (ρ.prod σ)
  have h₂ : MeasurePreserving (Prod.map id (MeasurableEquiv.prodAssoc : (β × γ) × δ ≃ᵐ β × γ × δ).symm)
      (μ.prod (ν.prod (ρ.prod σ))) (μ.prod ((ν.prod ρ).prod σ)) :=
    (MeasurePreserving.id μ).prod (MeasureTheory.measurePreserving_prodAssoc ν ρ σ).symm
  have h₃ : MeasurePreserving (Prod.map id (Prod.map Prod.swap id) : α × (β × γ) × δ → α × (γ × β) × δ)
      (μ.prod ((ν.prod ρ).prod σ)) (μ.prod ((ρ.prod ν).prod σ)) :=
    (MeasurePreserving.id μ).prod ((Measure.measurePreserving_swap (μ := ν) (ν := ρ)).prod
      (MeasurePreserving.id σ))
  have h₄ : MeasurePreserving (Prod.map id (MeasurableEquiv.prodAssoc : (γ × β) × δ ≃ᵐ γ × β × δ))
      (μ.prod ((ρ.prod ν).prod σ)) (μ.prod (ρ.prod (ν.prod σ))) :=
    (MeasurePreserving.id μ).prod (MeasureTheory.measurePreserving_prodAssoc ρ ν σ)
  have h₅ := (MeasureTheory.measurePreserving_prodAssoc μ ρ (ν.prod σ)).symm
  have h := h₅.comp (h₄.comp (h₃.comp (h₂.comp h₁)))
  exact h.map_eq

private noncomputable def IwasawaThree.regroupKEquiv (K : Subgroup (AdelicGL 3 (𝓞 ℚ) ℚ))
    (hK : ∀ k : AdelicGL 3 (𝓞 ℚ) ℚ, k ∈ K ↔ archComponent3 (𝓞 ℚ) ℚ k ∈ orth3 ∧
      ∀ p : HeightOneSpectrum (𝓞 ℚ), componentAt3 (𝓞 ℚ) ℚ p k ∈ localMaximalCompact3 (𝓞 ℚ) ℚ p) :
    IwasawaThree.orthSubgroupInf × IwasawaThree.intGL3f ≃ₜ* K where
  toFun := IwasawaThree.regroupK K hK
  invFun k :=
    (⟨(IwasawaThree.glSplit (k : AdelicGL 3 (𝓞 ℚ) ℚ)).1, by
        have h := ((hK _).1 k.2).1
        rw [IwasawaThree.mem_orthSubgroupInf_iff, IwasawaThree.glSplit_apply]
        exact h⟩,
      ⟨(IwasawaThree.glSplit (k : AdelicGL 3 (𝓞 ℚ) ℚ)).2, by
        have h := ((hK _).1 k.2).2
        rw [IwasawaThree.mem_intGL3f_iff, IwasawaThree.glSplit_apply]
        intro p
        show Matrix.GeneralLinearGroup.map (AdelicLevel.finAdeleEval (𝓞 ℚ) ℚ p)
          (Matrix.GeneralLinearGroup.map (AdelicLevel.adeleFin (𝓞 ℚ) ℚ) (k : AdelicGL 3 (𝓞 ℚ) ℚ)) ∈ _
        rw [← Matrix.GeneralLinearGroup.map_comp_apply]
        exact h p⟩)
  left_inv p := by
    refine Prod.ext (Subtype.ext ?_) (Subtype.ext ?_)
    · show (IwasawaThree.glSplit (IwasawaThree.glSplit.symm _)).1 = _
      rw [MulEquiv.apply_symm_apply]
    · show (IwasawaThree.glSplit (IwasawaThree.glSplit.symm _)).2 = _
      rw [MulEquiv.apply_symm_apply]
  right_inv k := by
    refine Subtype.ext ?_
    show IwasawaThree.glSplit.symm ((IwasawaThree.glSplit (k : AdelicGL 3 (𝓞 ℚ) ℚ)).1,
      (IwasawaThree.glSplit (k : AdelicGL 3 (𝓞 ℚ) ℚ)).2) = (k : AdelicGL 3 (𝓞 ℚ) ℚ)
    rw [Prod.mk.eta, MulEquiv.symm_apply_apply]
  map_mul' p q := by
    refine Subtype.ext ?_
    show IwasawaThree.glSplit.symm (((p * q).1 : GL (Fin 3) (InfiniteAdeleRing ℚ)),
        ((p * q).2 : GL (Fin 3) (FiniteAdeleRing (𝓞 ℚ) ℚ))) =
      IwasawaThree.glSplit.symm
          ((p.1 : GL (Fin 3) (InfiniteAdeleRing ℚ)), (p.2 : GL (Fin 3) (FiniteAdeleRing (𝓞 ℚ) ℚ))) *
        IwasawaThree.glSplit.symm
          ((q.1 : GL (Fin 3) (InfiniteAdeleRing ℚ)), (q.2 : GL (Fin 3) (FiniteAdeleRing (𝓞 ℚ) ℚ)))
    rw [← map_mul]
    rfl
  continuous_toFun :=
    (IwasawaThree.continuous_glSplit_symm.comp
      ((continuous_subtype_val.comp continuous_fst).prodMk (continuous_subtype_val.comp continuous_snd))).subtype_mk _
  continuous_invFun :=
    ((continuous_fst.comp (IwasawaThree.continuous_glSplit.comp continuous_subtype_val)).subtype_mk _).prodMk
      ((continuous_snd.comp (IwasawaThree.continuous_glSplit.comp continuous_subtype_val)).subtype_mk _)

private theorem IwasawaThree.coe_regroupKEquiv (K : Subgroup (AdelicGL 3 (𝓞 ℚ) ℚ))
    (hK : ∀ k : AdelicGL 3 (𝓞 ℚ) ℚ, k ∈ K ↔ archComponent3 (𝓞 ℚ) ℚ k ∈ orth3 ∧
      ∀ p : HeightOneSpectrum (𝓞 ℚ), componentAt3 (𝓞 ℚ) ℚ p k ∈ localMaximalCompact3 (𝓞 ℚ) ℚ p) :
    (IwasawaThree.regroupKEquiv K hK : IwasawaThree.orthSubgroupInf × IwasawaThree.intGL3f → K) =
      IwasawaThree.regroupK K hK :=
  rfl

private theorem IwasawaThree.exists_map_regroupK_eq_smul (K : Subgroup (AdelicGL 3 (𝓞 ℚ) ℚ))
    (hK : ∀ k : AdelicGL 3 (𝓞 ℚ) ℚ, k ∈ K ↔ archComponent3 (𝓞 ℚ) ℚ k ∈ orth3 ∧
      ∀ p : HeightOneSpectrum (𝓞 ℚ), componentAt3 (𝓞 ℚ) ℚ p k ∈ localMaximalCompact3 (𝓞 ℚ) ℚ p)
    [MeasurableSpace (GL (Fin 3) (InfiniteAdeleRing ℚ))] [BorelSpace (GL (Fin 3) (InfiniteAdeleRing ℚ))]
    [MeasurableSpace (GL (Fin 3) (FiniteAdeleRing (𝓞 ℚ) ℚ))] [BorelSpace (GL (Fin 3) (FiniteAdeleRing (𝓞 ℚ) ℚ))]
    (nu : Measure IwasawaThree.orthSubgroupInf) [nu.IsHaarMeasure]
    (kap : Measure IwasawaThree.intGL3f) [kap.IsHaarMeasure] :
    letI : MeasurableSpace (AdelicGL 3 (𝓞 ℚ) ℚ) := NumberField.AdelicHaar.glBorel (Fin 3) (𝓞 ℚ) ℚ
    ∀ (κ : Measure K) [κ.IsHaarMeasure], ∃ c : ENNReal, c ≠ 0 ∧ c ≠ ⊤ ∧
      Measure.map (IwasawaThree.regroupK K hK) (nu.prod kap) = c • κ := by
  intro κ _
  letI : MeasurableSpace (AdelicGL 3 (𝓞 ℚ) ℚ) := NumberField.AdelicHaar.glBorel (Fin 3) (𝓞 ℚ) ℚ
  haveI : BorelSpace (AdelicGL 3 (𝓞 ℚ) ℚ) := NumberField.AdelicHaar.borelSpace_glBorel (Fin 3) (𝓞 ℚ) ℚ
  haveI : BorelSpace K := inferInstanceAs (BorelSpace (K : Set (AdelicGL 3 (𝓞 ℚ) ℚ)))
  haveI : BorelSpace IwasawaThree.orthSubgroupInf :=
    inferInstanceAs (BorelSpace (IwasawaThree.orthSubgroupInf : Set (GL (Fin 3) (InfiniteAdeleRing ℚ))))
  haveI : BorelSpace IwasawaThree.intGL3f :=
    inferInstanceAs (BorelSpace (IwasawaThree.intGL3f : Set (GL (Fin 3) (FiniteAdeleRing (𝓞 ℚ) ℚ))))
  haveI : CompactSpace IwasawaThree.orthSubgroupInf := IwasawaThree.Arch.compactSpace_orthSubgroupInf
  haveI : CompactSpace IwasawaThree.intGL3f := IwasawaThree.compactSpace_intGL3f
  haveI : IsFiniteMeasure nu := ⟨(isCompact_univ (X := IwasawaThree.orthSubgroupInf)).measure_lt_top⟩
  haveI : IsFiniteMeasure kap := ⟨(isCompact_univ (X := IwasawaThree.intGL3f)).measure_lt_top⟩
  haveI : CompactSpace K := (IwasawaThree.regroupKEquiv K hK).toHomeomorph.compactSpace
  have hKc : IsClosed (K : Set (AdelicGL 3 (𝓞 ℚ) ℚ)) :=
    (isCompact_iff_compactSpace.2 ‹CompactSpace K›).isClosed
  haveI : LocallyCompactSpace K := hKc.isClosedEmbedding_subtypeVal.locallyCompactSpace
  obtain ⟨c, hc₀, hc₁, h⟩ :=
    IwasawaThree.exists_ennreal_smul_eq_of_isHaarMeasure
      (Measure.map (IwasawaThree.regroupKEquiv K hK) (nu.prod kap)) κ
  exact ⟨c, hc₀, hc₁, h⟩

private abbrev IwasawaThree.Unipotent.Af : Type := FiniteAdeleRing (𝓞 ℚ) ℚ

private theorem IwasawaThree.Unipotent.upperUnipotent3_mul' {A : Type*} [CommRing A] (x y z x' y' z' : A) :
    upperUnipotent3 x y z * upperUnipotent3 x' y' z' = upperUnipotent3 (x + x') (y + y') (z + z' + x * y') := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [upperUnipotent3, Units.val_mul, Matrix.mul_apply, Fin.sum_univ_three]
  all_goals ring

private theorem IwasawaThree.Unipotent.coe_diagGL' {A : Type*} [CommRing A] (t : Fin 3 → Aˣ) :
    ((IwasawaThree.diagGL t : GL (Fin 3) A) : Matrix (Fin 3) (Fin 3) A) = Matrix.diagonal fun i => (t i : A) := rfl

private theorem IwasawaThree.Unipotent.coe_diagGL_inv' {A : Type*} [CommRing A] (t : Fin 3 → Aˣ) :
    (((IwasawaThree.diagGL t)⁻¹ : GL (Fin 3) A) : Matrix (Fin 3) (Fin 3) A) =
      Matrix.diagonal fun i => (((t i)⁻¹ : Aˣ) : A) := by
  rw [← map_inv]
  rfl

private theorem IwasawaThree.Unipotent.diagGL_mul' {A : Type*} [CommRing A] (s t : Fin 3 → Aˣ) :
    (IwasawaThree.diagGL s : GL (Fin 3) A) * IwasawaThree.diagGL t = IwasawaThree.diagGL (s * t) := by
  simp only [IwasawaThree.diagGL, map_mul]

private def IwasawaThree.Unipotent.rescale {A : Type*} [CommRing A] (s : Fin 3 → Aˣ) (p : A × A × A) : A × A × A :=
  (((s 0 * (s 1)⁻¹ : Aˣ) : A) * p.1, ((s 1 * (s 2)⁻¹ : Aˣ) : A) * p.2.1, ((s 0 * (s 2)⁻¹ : Aˣ) : A) * p.2.2)

private theorem IwasawaThree.Unipotent.diagGL_mul_upperUnipotent3' {A : Type*} [CommRing A] (s : Fin 3 → Aˣ)
    (p : A × A × A) :
    (IwasawaThree.diagGL s : GL (Fin 3) A) * upperUnipotent3 p.1 p.2.1 p.2.2 =
      upperUnipotent3 (rescale s p).1 (rescale s p).2.1 (rescale s p).2.2 * IwasawaThree.diagGL s := by
  apply Units.ext
  rw [Units.val_mul, Units.val_mul, coe_diagGL']
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [upperUnipotent3, rescale, Matrix.mul_apply, Matrix.diagonal, Units.val_mul] <;>
    ring_nf <;> simp only [Units.inv_mul_cancel_right]

private def IwasawaThree.Unipotent.shift {A : Type*} [CommRing A] (a b c : A) (p : A × A × A) : A × A × A :=
  (a + p.1, b + p.2.1, c + p.2.2 + a * p.2.1)

private theorem IwasawaThree.Unipotent.upperUnipotent3_mul_eq_shift {A : Type*} [CommRing A] (a b c : A)
    (p : A × A × A) :
    upperUnipotent3 a b c * upperUnipotent3 p.1 p.2.1 p.2.2 =
      upperUnipotent3 (shift a b c p).1 (shift a b c p).2.1 (shift a b c p).2.2 := by
  rw [upperUnipotent3_mul']
  rfl

private theorem IwasawaThree.Unipotent.exists_eq_upperUnipotent3_mul_diagGL (b : GL (Fin 3) Af)
    (hb : b ∈ IwasawaThree.upperTriangular3 Af) :
    ∃ (x y z : Af) (s : Fin 3 → Afˣ), b = upperUnipotent3 x y z * IwasawaThree.diagGL s := by
  obtain ⟨hU, hU'⟩ := hb
  set B : Matrix (Fin 3) (Fin 3) Af := (b : Matrix (Fin 3) (Fin 3) Af) with hB
  set B' : Matrix (Fin 3) (Fin 3) Af := ((b⁻¹ : GL (Fin 3) Af) : Matrix (Fin 3) (Fin 3) Af) with hB'
  have hBB' : B * B' = 1 := by rw [hB, hB', ← Units.val_mul, mul_inv_cancel, Units.val_one]
  have h10 : B 1 0 = 0 := hU (by decide)
  have h20 : B 2 0 = 0 := hU (by decide)
  have h21 : B 2 1 = 0 := hU (by decide)
  have h10' : B' 1 0 = 0 := hU' (by decide)
  have h20' : B' 2 0 = 0 := hU' (by decide)
  have h21' : B' 2 1 = 0 := hU' (by decide)
  have hd : ∀ i : Fin 3, B i i * B' i i = 1 := by
    intro i
    have h := congrFun (congrFun hBB' i) i
    fin_cases i <;> simpa [Matrix.mul_apply, Fin.sum_univ_three, h10, h20, h21, h10', h20', h21'] using h
  have e01 : B 0 1 * B' 1 1 * B 1 1 = B 0 1 := by rw [mul_assoc, mul_comm (B' 1 1), hd 1, mul_one]
  have e02 : B 0 2 * B' 2 2 * B 2 2 = B 0 2 := by rw [mul_assoc, mul_comm (B' 2 2), hd 2, mul_one]
  have e12 : B 1 2 * B' 2 2 * B 2 2 = B 1 2 := by rw [mul_assoc, mul_comm (B' 2 2), hd 2, mul_one]
  let s : Fin 3 → Afˣ := fun i => ⟨B i i, B' i i, hd i, by rw [mul_comm]; exact hd i⟩
  refine ⟨B 0 1 * B' 1 1, B 1 2 * B' 2 2, B 0 2 * B' 2 2, s, ?_⟩
  apply Units.ext
  rw [Units.val_mul, coe_diagGL']
  refine Matrix.ext fun i j => ?_
  fin_cases i <;> fin_cases j <;>
    simp [upperUnipotent3, Matrix.mul_apply, Matrix.diagonal, s, h10, h20, h21, e01, e02, e12, ← hB]

private theorem IwasawaThree.Unipotent.continuous_upperUnipotent3' {A : Type*} [CommRing A] [TopologicalSpace A]
    [IsTopologicalRing A] : Continuous (fun p : A × A × A => upperUnipotent3 p.1 p.2.1 p.2.2) := by
  refine Units.continuous_iff.2 ⟨?_, ?_⟩
  · refine continuous_pi fun i => continuous_pi fun j => ?_
    fin_cases i <;> fin_cases j <;> simp [upperUnipotent3] <;> fun_prop
  · have h : ∀ p : A × A × A,
        (((upperUnipotent3 p.1 p.2.1 p.2.2)⁻¹ : GL (Fin 3) A) : Matrix (Fin 3) (Fin 3) A) =
          !![1, -p.1, p.1 * p.2.1 - p.2.2; 0, 1, -p.2.1; 0, 0, 1] := by
      intro p
      have hmul : upperUnipotent3 p.1 p.2.1 p.2.2 * upperUnipotent3 (-p.1) (-p.2.1) (p.1 * p.2.1 - p.2.2) = 1 := by
        rw [upperUnipotent3_mul']
        simp only [add_neg_cancel]
        rw [show p.2.2 + (p.1 * p.2.1 - p.2.2) + p.1 * -p.2.1 = 0 by ring, upperUnipotent3_zero]
      rw [inv_eq_of_mul_eq_one_right hmul]
      rfl
    rw [funext h]
    refine continuous_pi fun i => continuous_pi fun j => ?_
    fin_cases i <;> fin_cases j <;> simp <;> fun_prop

private theorem IwasawaThree.Unipotent.continuous_diagGL' {A : Type*} [CommRing A] [TopologicalSpace A]
    [IsTopologicalRing A] : Continuous (fun t : Fin 3 → Aˣ => (IwasawaThree.diagGL t : GL (Fin 3) A)) := by
  refine Units.continuous_iff.2 ⟨?_, ?_⟩
  · refine continuous_pi fun i => continuous_pi fun j => ?_
    simp only [Function.comp_def, coe_diagGL', Matrix.diagonal_apply]
    split_ifs
    · exact Units.continuous_val.comp (continuous_apply i)
    · exact continuous_const
  · refine continuous_pi fun i => continuous_pi fun j => ?_
    simp only [coe_diagGL_inv', Matrix.diagonal_apply]
    split_ifs
    · exact Units.continuous_coe_inv.comp (continuous_apply i)
    · exact continuous_const

namespace IwasawaThree.Unipotent
private theorem _root_.LanglandsTunnell.CubicInduction.WhittakerBlock.IwasawaThree.Unipotent.continuous_iwMapF : Continuous IwasawaThree.iwMapF := by
  unfold IwasawaThree.iwMapF
  exact ((continuous_upperUnipotent3'.comp (continuous_fst.comp continuous_fst)).mul
    (continuous_diagGL'.comp (continuous_snd.comp continuous_fst))).mul (continuous_subtype_val.comp continuous_snd)

end IwasawaThree.Unipotent
p2m_export "LanglandsTunnell.CubicInduction.WhittakerBlock" "IwasawaThree.Unipotent.continuous_iwMapF"

private theorem IwasawaThree.Unipotent.upperUnipotent3_mul_iwMapF (a b c : Af) (q : (Af × Af × Af) × (Fin 3 → Afˣ))
    (k : IwasawaThree.intGL3f) :
    upperUnipotent3 a b c * IwasawaThree.iwMapF (q, k) = IwasawaThree.iwMapF ((shift a b c q.1, q.2), k) := by
  show upperUnipotent3 a b c *
      (upperUnipotent3 q.1.1 q.1.2.1 q.1.2.2 * IwasawaThree.diagGL q.2 * (k : GL (Fin 3) Af)) =
    upperUnipotent3 (shift a b c q.1).1 (shift a b c q.1).2.1 (shift a b c q.1).2.2 * IwasawaThree.diagGL q.2 *
      (k : GL (Fin 3) Af)
  rw [← mul_assoc, ← mul_assoc, upperUnipotent3_mul_eq_shift]

private theorem IwasawaThree.Unipotent.diagGL_mul_iwMapF (s : Fin 3 → Afˣ) (q : (Af × Af × Af) × (Fin 3 → Afˣ))
    (k : IwasawaThree.intGL3f) :
    (IwasawaThree.diagGL s : GL (Fin 3) Af) * IwasawaThree.iwMapF (q, k) =
      IwasawaThree.iwMapF ((rescale s q.1, s * q.2), k) := by
  show IwasawaThree.diagGL s *
      (upperUnipotent3 q.1.1 q.1.2.1 q.1.2.2 * IwasawaThree.diagGL q.2 * (k : GL (Fin 3) Af)) =
    upperUnipotent3 (rescale s q.1).1 (rescale s q.1).2.1 (rescale s q.1).2.2 * IwasawaThree.diagGL (s * q.2) *
      (k : GL (Fin 3) Af)
  rw [← mul_assoc, ← mul_assoc, diagGL_mul_upperUnipotent3', mul_assoc _ (IwasawaThree.diagGL s), diagGL_mul']

private theorem IwasawaThree.Unipotent.densF_mul (s t : Fin 3 → Afˣ) :
    IwasawaThree.densF (s * t) = IwasawaThree.densF s * IwasawaThree.densF t := by
  unfold IwasawaThree.densF
  rw [← ENNReal.ofReal_mul (by positivity)]
  congr 1
  simp only [Pi.mul_apply, map_mul, NNReal.coe_mul]
  ring

private theorem IwasawaThree.Unipotent.densF_pos (s : Fin 3 → Afˣ) : 0 < IwasawaThree.densF s := by
  unfold IwasawaThree.densF
  have h0 : (0 : ℝ) < (distribHaarChar Af (s 0) : NNReal) := NNReal.coe_pos.2 distribHaarChar_pos
  have h2 : (0 : ℝ) < (distribHaarChar Af (s 2) : NNReal) := NNReal.coe_pos.2 distribHaarChar_pos
  exact ENNReal.ofReal_pos.2 (by positivity)

private theorem IwasawaThree.Unipotent.densF_ne_top (s : Fin 3 → Afˣ) : IwasawaThree.densF s ≠ ⊤ :=
  ENNReal.ofReal_ne_top

private theorem IwasawaThree.Unipotent.densF_inv_mul (s t : Fin 3 → Afˣ) :
    IwasawaThree.densF (s⁻¹ * t) = (IwasawaThree.densF s)⁻¹ * IwasawaThree.densF t := by
  have h := densF_mul s (s⁻¹ * t)
  rw [mul_inv_cancel_left] at h
  rw [h, ← mul_assoc, ENNReal.inv_mul_cancel (densF_pos s).ne' (densF_ne_top s), one_mul]

private theorem IwasawaThree.Unipotent.densF_eq_coe (s : Fin 3 → Afˣ) :
    IwasawaThree.densF s =
      (((distribHaarChar Af (s 0 * (s 1)⁻¹))⁻¹ : NNReal) : ENNReal) *
        ((((distribHaarChar Af (s 1 * (s 2)⁻¹))⁻¹ : NNReal) : ENNReal) *
          (((distribHaarChar Af (s 0 * (s 2)⁻¹))⁻¹ : NNReal) : ENNReal)) := by
  have h0 : ((distribHaarChar Af (s 0) : NNReal) : ℝ) ≠ 0 := (NNReal.coe_pos.2 distribHaarChar_pos).ne'
  have h1 : ((distribHaarChar Af (s 1) : NNReal) : ℝ) ≠ 0 := (NNReal.coe_pos.2 distribHaarChar_pos).ne'
  have h2 : ((distribHaarChar Af (s 2) : NNReal) : ℝ) ≠ 0 := (NNReal.coe_pos.2 distribHaarChar_pos).ne'
  unfold IwasawaThree.densF
  rw [← ENNReal.coe_mul, ← ENNReal.coe_mul, ← NNReal.coe_inv, ← NNReal.coe_pow, ← NNReal.coe_pow,
    ← NNReal.coe_mul, ENNReal.ofReal_coe_nnreal]
  congr 1
  rw [← NNReal.coe_inj]
  simp only [map_mul, map_inv, NNReal.coe_mul, NNReal.coe_inv, NNReal.coe_pow]
  field_simp

private theorem IwasawaThree.Unipotent.regular_of_isAddHaarMeasure [MeasurableSpace Af] [BorelSpace Af]
    (lam : Measure Af) [lam.IsAddHaarMeasure] : lam.Regular := by
  obtain ⟨c, -, hc, hlam⟩ := IwasawaThree.exists_ennreal_smul_eq_of_isAddHaarMeasure lam Measure.addHaar
  rw [hlam]
  exact Measure.Regular.smul hc

private theorem IwasawaThree.Unipotent.map_unit_mul_eq_smul [MeasurableSpace Af] [BorelSpace Af] (lam : Measure Af)
    [lam.IsAddHaarMeasure] (a : Afˣ) :
    Measure.map (fun x => (a : Af) * x) lam = (((distribHaarChar Af a)⁻¹ : NNReal) : ENNReal) • lam := by
  haveI := regular_of_isAddHaarMeasure lam
  have hma : Measurable fun x : Af => (a : Af) * x := (continuous_const.mul continuous_id).measurable
  ext S hS
  rw [Measure.map_apply hma hS, Measure.smul_apply, smul_eq_mul, ← map_inv, distribHaarChar_mul]
  congr 1
  exact Set.preimage_smul a S

private theorem IwasawaThree.Unipotent.map_rescale_eq_smul [MeasurableSpace Af] [BorelSpace Af] (lam : Measure Af)
    [lam.IsAddHaarMeasure] (s : Fin 3 → Afˣ) :
    Measure.map (rescale s) (lam.prod (lam.prod lam)) = IwasawaThree.densF s • lam.prod (lam.prod lam) := by
  have hm : ∀ u : Afˣ, Measurable fun x : Af => (u : Af) * x := fun u =>
    (continuous_const.mul continuous_id).measurable
  have hfun : rescale s = Prod.map (fun x : Af => ((s 0 * (s 1)⁻¹ : Afˣ) : Af) * x)
      (Prod.map (fun x : Af => ((s 1 * (s 2)⁻¹ : Afˣ) : Af) * x) fun x : Af => ((s 0 * (s 2)⁻¹ : Afˣ) : Af) * x) := rfl
  rw [hfun, ← Measure.map_prod_map _ _ (hm _) ((hm _).prodMap (hm _)), ← Measure.map_prod_map _ _ (hm _) (hm _),
    map_unit_mul_eq_smul, map_unit_mul_eq_smul, map_unit_mul_eq_smul]
  simp only [Measure.prod_smul_left, Measure.prod_smul_right, smul_smul, densF_eq_coe]
  congr 1
  ring

private theorem IwasawaThree.Unipotent.measurable_rescale [MeasurableSpace Af] [BorelSpace Af] (s : Fin 3 → Afˣ) :
    Measurable (rescale s) := by
  unfold rescale
  fun_prop

private theorem IwasawaThree.Unipotent.map_mul_left_withDensity [MeasurableSpace Afˣ] [BorelSpace Afˣ]
    (tau : Measure Afˣ) [tau.IsHaarMeasure] (s : Fin 3 → Afˣ) :
    Measure.map (fun t => s * t) ((Measure.pi fun _ : Fin 3 => tau).withDensity IwasawaThree.densF) =
      (IwasawaThree.densF s)⁻¹ • (Measure.pi fun _ : Fin 3 => tau).withDensity IwasawaThree.densF := by
  have hms : Measurable fun t : Fin 3 → Afˣ => s * t := (continuous_const.mul continuous_id).measurable
  have hemb : MeasurableEmbedding fun t : Fin 3 → Afˣ => s * t := (MeasurableEquiv.mulLeft s).measurableEmbedding
  ext S hS
  rw [Measure.map_apply hms hS, Measure.smul_apply, smul_eq_mul, MeasureTheory.withDensity_apply _ (hS.preimage hms),
    MeasureTheory.withDensity_apply _ hS]
  calc ∫⁻ t in (fun t : Fin 3 → Afˣ => s * t) ⁻¹' S, IwasawaThree.densF t ∂(Measure.pi fun _ : Fin 3 => tau)
      = ∫⁻ t in (fun t : Fin 3 → Afˣ => s * t) ⁻¹' S, (IwasawaThree.densF s)⁻¹ * IwasawaThree.densF (s * t)
          ∂(Measure.pi fun _ : Fin 3 => tau) := by
        refine setLIntegral_congr_fun (hS.preimage hms) fun t _ => ?_
        rw [← densF_inv_mul, inv_mul_cancel_left]
    _ = ∫⁻ t in S, (IwasawaThree.densF s)⁻¹ * IwasawaThree.densF t ∂(Measure.pi fun _ : Fin 3 => tau) :=
        (measurePreserving_mul_left (Measure.pi fun _ : Fin 3 => tau) s).setLIntegral_comp_preimage_emb hemb
          (fun u => (IwasawaThree.densF s)⁻¹ * IwasawaThree.densF u) S
    _ = (IwasawaThree.densF s)⁻¹ * ∫⁻ t in S, IwasawaThree.densF t ∂(Measure.pi fun _ : Fin 3 => tau) :=
        lintegral_const_mul' _ _ (ENNReal.inv_ne_top.2 (densF_pos s).ne')

private theorem IwasawaThree.Unipotent.measurePreserving_shift [MeasurableSpace Af] [BorelSpace Af] (lam : Measure Af)
    [lam.IsAddHaarMeasure] (a b c : Af) :
    MeasurePreserving (shift a b c) (lam.prod (lam.prod lam)) (lam.prod (lam.prod lam)) := by
  have hin : MeasurePreserving (fun q : Af × Af => (b + q.1, c + q.2 + a * q.1)) (lam.prod lam) (lam.prod lam) := by
    refine (measurePreserving_add_left lam b).skew_product (g := fun y z => c + z + a * y) (by fun_prop) ?_
    refine Filter.Eventually.of_forall fun y => ?_
    show Measure.map (fun z : Af => c + z + a * y) lam = lam
    rw [show (fun z : Af => c + z + a * y) = fun z => (c + a * y) + z from funext fun z => by ring]
    exact (measurePreserving_add_left lam (c + a * y)).map_eq
  exact (measurePreserving_add_left lam a).prod hin

namespace IwasawaThree.Unipotent
private theorem _root_.LanglandsTunnell.CubicInduction.WhittakerBlock.IwasawaThree.Unipotent.measurable_iwMapF [MeasurableSpace Af] [BorelSpace Af] [MeasurableSpace Afˣ]
    [BorelSpace Afˣ] [MeasurableSpace (GL (Fin 3) Af)] [BorelSpace (GL (Fin 3) Af)] : Measurable IwasawaThree.iwMapF :=
  continuous_iwMapF.measurable

end IwasawaThree.Unipotent
p2m_export "LanglandsTunnell.CubicInduction.WhittakerBlock" "IwasawaThree.Unipotent.measurable_iwMapF"

private theorem IwasawaThree.Unipotent.map_upperUnipotent3_mul_nuF [MeasurableSpace Af] [BorelSpace Af]
    [MeasurableSpace Afˣ] [BorelSpace Afˣ] [MeasurableSpace (GL (Fin 3) Af)] [BorelSpace (GL (Fin 3) Af)]
    (lam : Measure Af) [lam.IsAddHaarMeasure] (tau : Measure Afˣ) [tau.IsHaarMeasure]
    (kap : Measure IwasawaThree.intGL3f) [SFinite kap] (a b c : Af) :
    Measure.map (fun g => upperUnipotent3 a b c * g) (IwasawaThree.nuF lam tau kap) =
      IwasawaThree.nuF lam tau kap := by
  have hsh := measurePreserving_shift lam a b c
  have hml : Measurable fun g : GL (Fin 3) Af => upperUnipotent3 a b c * g :=
    (continuous_const.mul continuous_id).measurable
  have hcomp : (fun g : GL (Fin 3) Af => upperUnipotent3 a b c * g) ∘ IwasawaThree.iwMapF =
      IwasawaThree.iwMapF ∘ Prod.map (Prod.map (shift a b c) id) id :=
    funext fun qk => upperUnipotent3_mul_iwMapF a b c qk.1 qk.2
  unfold IwasawaThree.nuF
  rw [Measure.map_map hml measurable_iwMapF, hcomp,
    ← Measure.map_map measurable_iwMapF ((hsh.measurable.prodMap measurable_id).prodMap measurable_id),
    ← Measure.map_prod_map _ _ (hsh.measurable.prodMap measurable_id) measurable_id, Measure.map_id,
    ← Measure.map_prod_map _ _ hsh.measurable measurable_id, hsh.map_eq, Measure.map_id]

private theorem IwasawaThree.Unipotent.map_diagGL_mul_nuF [MeasurableSpace Af] [BorelSpace Af] [MeasurableSpace Afˣ]
    [BorelSpace Afˣ] [MeasurableSpace (GL (Fin 3) Af)] [BorelSpace (GL (Fin 3) Af)]
    (lam : Measure Af) [lam.IsAddHaarMeasure] (tau : Measure Afˣ) [tau.IsHaarMeasure]
    (kap : Measure IwasawaThree.intGL3f) [SFinite kap] (s : Fin 3 → Afˣ) :
    Measure.map (fun g => (IwasawaThree.diagGL s : GL (Fin 3) Af) * g) (IwasawaThree.nuF lam tau kap) =
      IwasawaThree.nuF lam tau kap := by
  have hml : Measurable fun g : GL (Fin 3) Af => (IwasawaThree.diagGL s : GL (Fin 3) Af) * g :=
    (continuous_const.mul continuous_id).measurable
  have hmt : Measurable fun t : Fin 3 → Afˣ => s * t := (continuous_const.mul continuous_id).measurable
  have hcomp : (fun g : GL (Fin 3) Af => (IwasawaThree.diagGL s : GL (Fin 3) Af) * g) ∘ IwasawaThree.iwMapF =
      IwasawaThree.iwMapF ∘ Prod.map (Prod.map (rescale s) fun t => s * t) id :=
    funext fun qk => diagGL_mul_iwMapF s qk.1 qk.2
  unfold IwasawaThree.nuF
  rw [Measure.map_map hml measurable_iwMapF, hcomp,
    ← Measure.map_map measurable_iwMapF (((measurable_rescale s).prodMap hmt).prodMap measurable_id),
    ← Measure.map_prod_map _ _ ((measurable_rescale s).prodMap hmt) measurable_id, Measure.map_id,
    ← Measure.map_prod_map _ _ (measurable_rescale s) hmt, map_rescale_eq_smul, map_mul_left_withDensity,
    Measure.prod_smul_left, Measure.prod_smul_right, smul_smul,
    ENNReal.mul_inv_cancel (densF_pos s).ne' (densF_ne_top s), one_smul]

private theorem IwasawaThree.map_mul_left_nuF [MeasurableSpace (FiniteAdeleRing (𝓞 ℚ) ℚ)]
    [BorelSpace (FiniteAdeleRing (𝓞 ℚ) ℚ)] [MeasurableSpace (FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ]
    [BorelSpace (FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ] [MeasurableSpace (GL (Fin 3) (FiniteAdeleRing (𝓞 ℚ) ℚ))]
    [BorelSpace (GL (Fin 3) (FiniteAdeleRing (𝓞 ℚ) ℚ))]
    (lam : Measure (FiniteAdeleRing (𝓞 ℚ) ℚ)) [lam.IsAddHaarMeasure]
    (tau : Measure (FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) [tau.IsHaarMeasure]
    (kap : Measure IwasawaThree.intGL3f) [SFinite kap]
    (b : GL (Fin 3) (FiniteAdeleRing (𝓞 ℚ) ℚ)) (hb : b ∈ IwasawaThree.upperTriangular3 (FiniteAdeleRing (𝓞 ℚ) ℚ)) :
    Measure.map (fun g => b * g) (IwasawaThree.nuF lam tau kap) = IwasawaThree.nuF lam tau kap := by
  obtain ⟨x, y, z, s, rfl⟩ := IwasawaThree.Unipotent.exists_eq_upperUnipotent3_mul_diagGL b hb
  have h₁ : Measurable fun g : GL (Fin 3) (FiniteAdeleRing (𝓞 ℚ) ℚ) => upperUnipotent3 x y z * g :=
    (continuous_const.mul continuous_id).measurable
  have h₂ : Measurable fun g : GL (Fin 3) (FiniteAdeleRing (𝓞 ℚ) ℚ) => (IwasawaThree.diagGL s : GL (Fin 3) _) * g :=
    (continuous_const.mul continuous_id).measurable
  rw [show (fun g => upperUnipotent3 x y z * IwasawaThree.diagGL s * g) =
      (fun g => upperUnipotent3 x y z * g) ∘ fun g => (IwasawaThree.diagGL s : GL (Fin 3) _) * g from
      funext fun g => mul_assoc _ _ _,
    ← Measure.map_map h₁ h₂,
    IwasawaThree.Unipotent.map_diagGL_mul_nuF, IwasawaThree.Unipotent.map_upperUnipotent3_mul_nuF]

private abbrev IwasawaThree.Unipotent.Ainf : Type := InfiniteAdeleRing ℚ

private abbrev IwasawaThree.Unipotent.Ad : Type := AdeleRing (𝓞 ℚ) ℚ

private theorem IwasawaThree.Unipotent.smul_prod_eq (t : Adˣ) (S : Set Ainf) (T : Set Af) :
    (fun p : Ad => t • p) '' (S ×ˢ T : Set Ad) =
      (((fun x : Ainf => (IwasawaThree.ideleSplit t).1 • x) '' S) ×ˢ
        ((fun y : Af => (IwasawaThree.ideleSplit t).2 • y) '' T) : Set (Ainf × Af)) := by
  ext p
  constructor
  · rintro ⟨q, ⟨hq₁, hq₂⟩, rfl⟩
    exact ⟨⟨q.1, hq₁, rfl⟩, ⟨q.2, hq₂, rfl⟩⟩
  · rintro ⟨⟨a, ha, ha'⟩, ⟨b, hb, hb'⟩⟩
    exact ⟨(a, b), ⟨ha, hb⟩, Prod.ext ha' hb'⟩

private theorem IwasawaThree.Unipotent.distribHaarChar_adele_eq_mul_of_haar [MeasurableSpace Ainf] [BorelSpace Ainf]
    [MeasurableSpace Af] [BorelSpace Af] (μ₁ : Measure Ainf) [μ₁.IsAddHaarMeasure] (μ₂ : Measure Af)
    [μ₂.IsAddHaarMeasure] (t : Adˣ) :
    distribHaarChar Ad t =
      distribHaarChar Ainf (IwasawaThree.ideleSplit t).1 * distribHaarChar Af (IwasawaThree.ideleSplit t).2 := by
  letI : MeasurableSpace Ad := inferInstanceAs (MeasurableSpace (Ainf × Af))
  haveI : BorelSpace Ad := inferInstanceAs (BorelSpace (Ainf × Af))

  let P : Measure Ad := μ₁.prod μ₂
  haveI : P.IsAddHaarMeasure := inferInstanceAs (μ₁.prod μ₂).IsAddHaarMeasure
  haveI : μ₁.Regular := by
    obtain ⟨c, -, hc, h⟩ := IwasawaThree.exists_ennreal_smul_eq_of_isAddHaarMeasure μ₁ Measure.addHaar
    rw [h]
    exact Measure.Regular.smul hc
  haveI : μ₂.Regular := by
    obtain ⟨c, -, hc, h⟩ := IwasawaThree.exists_ennreal_smul_eq_of_isAddHaarMeasure μ₂ Measure.addHaar
    rw [h]
    exact Measure.Regular.smul hc
  haveI : P.Regular := by
    obtain ⟨c, -, hc, h⟩ := IwasawaThree.exists_ennreal_smul_eq_of_isAddHaarMeasure P Measure.addHaar
    rw [h]
    exact Measure.Regular.smul hc
  obtain ⟨S, hSc, hS⟩ := exists_compact_mem_nhds (0 : Ainf)
  obtain ⟨T, hTc, hT⟩ := exists_compact_mem_nhds (0 : Af)
  refine distribHaarChar_eq_of_measure_smul_eq_mul (μ := P) (s := (S ×ˢ T : Set Ad)) ?_ ?_ ?_
  · show μ₁.prod μ₂ (S ×ˢ T) ≠ 0
    rw [Measure.prod_prod]
    exact mul_ne_zero (Measure.measure_pos_of_mem_nhds (μ := μ₁) hS).ne'
      (Measure.measure_pos_of_mem_nhds (μ := μ₂) hT).ne'
  · show μ₁.prod μ₂ (S ×ˢ T) ≠ ⊤
    rw [Measure.prod_prod]
    exact ENNReal.mul_ne_top hSc.measure_lt_top.ne hTc.measure_lt_top.ne
  · show (μ₁.prod μ₂ : Measure Ad) ((fun p : Ad => t • p) '' (S ×ˢ T : Set Ad)) =
      ↑(distribHaarChar Ainf (IwasawaThree.ideleSplit t).1 * distribHaarChar Af (IwasawaThree.ideleSplit t).2) *
        (μ₁.prod μ₂ : Measure Ad) (S ×ˢ T : Set Ad)

    have himg : (μ₁.prod μ₂ : Measure Ad) ((fun p : Ad => t • p) '' (S ×ˢ T : Set Ad)) =
        μ₁.prod μ₂ (((fun x : Ainf => (IwasawaThree.ideleSplit t).1 • x) '' S) ×ˢ
          ((fun y : Af => (IwasawaThree.ideleSplit t).2 • y) '' T)) :=
      congrArg _ (smul_prod_eq t S T)
    refine himg.trans ?_
    show μ₁.prod μ₂ (((fun x : Ainf => (IwasawaThree.ideleSplit t).1 • x) '' S) ×ˢ
        ((fun y : Af => (IwasawaThree.ideleSplit t).2 • y) '' T)) =
      ↑(distribHaarChar Ainf (IwasawaThree.ideleSplit t).1 * distribHaarChar Af (IwasawaThree.ideleSplit t).2) *
        μ₁.prod μ₂ (S ×ˢ T)
    have h₁ : μ₁ ((fun x : Ainf => (IwasawaThree.ideleSplit t).1 • x) '' S) =
        ↑(distribHaarChar Ainf (IwasawaThree.ideleSplit t).1) * μ₁ S :=
      (distribHaarChar_mul μ₁ (IwasawaThree.ideleSplit t).1 S).symm
    have h₂ : μ₂ ((fun y : Af => (IwasawaThree.ideleSplit t).2 • y) '' T) =
        ↑(distribHaarChar Af (IwasawaThree.ideleSplit t).2) * μ₂ T :=
      (distribHaarChar_mul μ₂ (IwasawaThree.ideleSplit t).2 T).symm
    rw [Measure.prod_prod, Measure.prod_prod, h₁, h₂, ENNReal.coe_mul]
    ring

private theorem IwasawaThree.distribHaarChar_adele_eq_mul (t : (AdeleRing (𝓞 ℚ) ℚ)ˣ) :
    distribHaarChar (AdeleRing (𝓞 ℚ) ℚ) t =
      distribHaarChar (InfiniteAdeleRing ℚ) (IwasawaThree.ideleSplit t).1 *
        distribHaarChar (FiniteAdeleRing (𝓞 ℚ) ℚ) (IwasawaThree.ideleSplit t).2 := by
  letI : MeasurableSpace (InfiniteAdeleRing ℚ) := borel _
  haveI : BorelSpace (InfiniteAdeleRing ℚ) := ⟨rfl⟩
  letI : MeasurableSpace (FiniteAdeleRing (𝓞 ℚ) ℚ) := borel _
  haveI : BorelSpace (FiniteAdeleRing (𝓞 ℚ) ℚ) := ⟨rfl⟩
  exact IwasawaThree.Unipotent.distribHaarChar_adele_eq_mul_of_haar Measure.addHaar Measure.addHaar t

private noncomputable def IwasawaThree.Unipotent.regroupNEquiv :
    (InfiniteAdeleRing ℚ × InfiniteAdeleRing ℚ × InfiniteAdeleRing ℚ) ×
      (FiniteAdeleRing (𝓞 ℚ) ℚ × FiniteAdeleRing (𝓞 ℚ) ℚ × FiniteAdeleRing (𝓞 ℚ) ℚ) ≃+
        (AdeleRing (𝓞 ℚ) ℚ × AdeleRing (𝓞 ℚ) ℚ × AdeleRing (𝓞 ℚ) ℚ) where
  toFun := IwasawaThree.regroupN
  invFun x := ((x.1.1, x.2.1.1, x.2.2.1), (x.1.2, x.2.1.2, x.2.2.2))
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl

private theorem IwasawaThree.Unipotent.continuous_regroupN : Continuous IwasawaThree.regroupN := by
  unfold IwasawaThree.regroupN
  exact (continuous_fst.fst.prodMk continuous_snd.fst).prodMk
    ((continuous_fst.snd.fst.prodMk continuous_snd.snd.fst).prodMk
      (continuous_fst.snd.snd.prodMk continuous_snd.snd.snd))

private theorem IwasawaThree.Unipotent.continuous_regroupNEquiv_symm : Continuous regroupNEquiv.symm := by
  show Continuous fun x : AdeleRing (𝓞 ℚ) ℚ × AdeleRing (𝓞 ℚ) ℚ × AdeleRing (𝓞 ℚ) ℚ =>
    ((x.1.1, x.2.1.1, x.2.2.1), (x.1.2, x.2.1.2, x.2.2.2))
  exact (continuous_fst.fst.prodMk (continuous_snd.fst.fst.prodMk continuous_snd.snd.fst)).prodMk
    (continuous_fst.snd.prodMk (continuous_snd.fst.snd.prodMk continuous_snd.snd.snd))

private theorem IwasawaThree.measurable_regroupN [MeasurableSpace (InfiniteAdeleRing ℚ)]
    [BorelSpace (InfiniteAdeleRing ℚ)] [MeasurableSpace (FiniteAdeleRing (𝓞 ℚ) ℚ)]
    [BorelSpace (FiniteAdeleRing (𝓞 ℚ) ℚ)] :
    letI := NumberField.AdelicHaar.adeleBorel (𝓞 ℚ) ℚ
    Measurable IwasawaThree.regroupN := by
  letI := NumberField.AdelicHaar.adeleBorel (𝓞 ℚ) ℚ
  haveI := NumberField.AdelicHaar.borelSpace_adeleBorel (𝓞 ℚ) ℚ
  exact IwasawaThree.Unipotent.continuous_regroupN.measurable

private theorem IwasawaThree.exists_map_regroupN_eq_smul [MeasurableSpace (InfiniteAdeleRing ℚ)]
    [BorelSpace (InfiniteAdeleRing ℚ)] [MeasurableSpace (FiniteAdeleRing (𝓞 ℚ) ℚ)]
    [BorelSpace (FiniteAdeleRing (𝓞 ℚ) ℚ)]
    (lamA : Measure (InfiniteAdeleRing ℚ)) [lamA.IsAddHaarMeasure] (lamF : Measure (FiniteAdeleRing (𝓞 ℚ) ℚ))
    [lamF.IsAddHaarMeasure] :
    letI := NumberField.AdelicHaar.adeleBorel (𝓞 ℚ) ℚ
    ∃ c : ENNReal, c ≠ 0 ∧ c ≠ ⊤ ∧
      Measure.map IwasawaThree.regroupN ((lamA.prod (lamA.prod lamA)).prod (lamF.prod (lamF.prod lamF))) =
        c • (NumberField.AdelicHaar.adelicAddHaar (𝓞 ℚ) ℚ).prod
          ((NumberField.AdelicHaar.adelicAddHaar (𝓞 ℚ) ℚ).prod (NumberField.AdelicHaar.adelicAddHaar (𝓞 ℚ) ℚ)) := by
  letI := NumberField.AdelicHaar.adeleBorel (𝓞 ℚ) ℚ
  haveI := NumberField.AdelicHaar.borelSpace_adeleBorel (𝓞 ℚ) ℚ
  haveI := NumberField.AdelicHaar.isAddHaarMeasure_adelicAddHaar (𝓞 ℚ) ℚ

  haveI : SigmaCompactSpace (InfiniteAdeleRing ℚ) := sigmaCompactSpace_of_locallyCompact_secondCountable
  haveI : SigmaCompactSpace (FiniteAdeleRing (𝓞 ℚ) ℚ) := sigmaCompactSpace_of_locallyCompact_secondCountable
  haveI : SigmaCompactSpace (AdeleRing (𝓞 ℚ) ℚ) := sigmaCompactSpace_of_locallyCompact_secondCountable
  haveI : SigmaFinite lamA := Measure.IsAddHaarMeasure.sigmaFinite lamA
  haveI : SigmaFinite lamF := Measure.IsAddHaarMeasure.sigmaFinite lamF
  haveI : SigmaFinite (NumberField.AdelicHaar.adelicAddHaar (𝓞 ℚ) ℚ) := Measure.IsAddHaarMeasure.sigmaFinite _
  haveI : (lamA.prod lamA).IsAddHaarMeasure := inferInstance
  haveI : (lamA.prod (lamA.prod lamA)).IsAddHaarMeasure := inferInstance
  haveI : (lamF.prod lamF).IsAddHaarMeasure := inferInstance
  haveI : (lamF.prod (lamF.prod lamF)).IsAddHaarMeasure := inferInstance
  haveI : ((lamA.prod (lamA.prod lamA)).prod (lamF.prod (lamF.prod lamF))).IsAddHaarMeasure := inferInstance
  haveI : ((NumberField.AdelicHaar.adelicAddHaar (𝓞 ℚ) ℚ).prod
      (NumberField.AdelicHaar.adelicAddHaar (𝓞 ℚ) ℚ)).IsAddHaarMeasure :=
    inferInstance
  haveI : ((NumberField.AdelicHaar.adelicAddHaar (𝓞 ℚ) ℚ).prod
      ((NumberField.AdelicHaar.adelicAddHaar (𝓞 ℚ) ℚ).prod
        (NumberField.AdelicHaar.adelicAddHaar (𝓞 ℚ) ℚ))).IsAddHaarMeasure :=
    inferInstance
  haveI : (Measure.map IwasawaThree.regroupN
      ((lamA.prod (lamA.prod lamA)).prod (lamF.prod (lamF.prod lamF)))).IsAddHaarMeasure :=
    AddEquiv.isAddHaarMeasure_map (μ := (lamA.prod (lamA.prod lamA)).prod (lamF.prod (lamF.prod lamF)))
      IwasawaThree.Unipotent.regroupNEquiv IwasawaThree.Unipotent.continuous_regroupN
      IwasawaThree.Unipotent.continuous_regroupNEquiv_symm
  exact IwasawaThree.exists_ennreal_smul_eq_of_isAddHaarMeasure _ _

private noncomputable def IwasawaThree.Unipotent.regroupTEquiv :
    (Fin 3 → (InfiniteAdeleRing ℚ)ˣ) × (Fin 3 → (FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) ≃* (Fin 3 → (AdeleRing (𝓞 ℚ) ℚ)ˣ) where
  toFun := IwasawaThree.regroupT
  invFun t := (fun i => (IwasawaThree.ideleSplit (t i)).1, fun i => (IwasawaThree.ideleSplit (t i)).2)
  left_inv p := by
    ext i <;> simp [IwasawaThree.regroupT, ContinuousMulEquiv.apply_symm_apply]
  right_inv t := by
    funext i
    simp [IwasawaThree.regroupT, ContinuousMulEquiv.symm_apply_apply]
  map_mul' p q := by
    funext i
    show IwasawaThree.ideleSplit.symm (p.1 i * q.1 i, p.2 i * q.2 i) =
      IwasawaThree.ideleSplit.symm (p.1 i, p.2 i) * IwasawaThree.ideleSplit.symm (q.1 i, q.2 i)
    rw [← Prod.mk_mul_mk, map_mul]

namespace IwasawaThree.Unipotent
private theorem _root_.LanglandsTunnell.CubicInduction.WhittakerBlock.IwasawaThree.Unipotent.continuous_regroupT : Continuous IwasawaThree.regroupT := by
  unfold IwasawaThree.regroupT
  exact continuous_pi fun i => IwasawaThree.ideleSplit.symm.continuous.comp
    (((continuous_apply i).comp continuous_fst).prodMk ((continuous_apply i).comp continuous_snd))

end IwasawaThree.Unipotent
p2m_export "LanglandsTunnell.CubicInduction.WhittakerBlock" "IwasawaThree.Unipotent.continuous_regroupT"
private theorem IwasawaThree.Unipotent.continuous_regroupTEquiv_symm : Continuous regroupTEquiv.symm := by
  show Continuous fun t : Fin 3 → (AdeleRing (𝓞 ℚ) ℚ)ˣ =>
    ((fun i => (IwasawaThree.ideleSplit (t i)).1, fun i => (IwasawaThree.ideleSplit (t i)).2) :
      (Fin 3 → (InfiniteAdeleRing ℚ)ˣ) × (Fin 3 → (FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ))
  exact (continuous_pi fun i =>
      continuous_fst.comp (IwasawaThree.ideleSplit.continuous.comp (continuous_apply i))).prodMk
    (continuous_pi fun i => continuous_snd.comp (IwasawaThree.ideleSplit.continuous.comp (continuous_apply i)))

private theorem IwasawaThree.measurable_regroupT [MeasurableSpace (InfiniteAdeleRing ℚ)ˣ]
    [BorelSpace (InfiniteAdeleRing ℚ)ˣ] [MeasurableSpace (FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ]
    [BorelSpace (FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ] :
    letI := NumberField.Idele.ideleBorel ℚ
    Measurable IwasawaThree.regroupT := by
  letI := NumberField.Idele.ideleBorel ℚ
  haveI := NumberField.Idele.borelSpace_ideleBorel ℚ
  exact IwasawaThree.Unipotent.continuous_regroupT.measurable

private theorem IwasawaThree.exists_map_regroupT_eq_smul [MeasurableSpace (InfiniteAdeleRing ℚ)ˣ]
    [BorelSpace (InfiniteAdeleRing ℚ)ˣ] [MeasurableSpace (FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ]
    [BorelSpace (FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ] (tauA : Measure (InfiniteAdeleRing ℚ)ˣ) [tauA.IsHaarMeasure]
    (tauF : Measure (FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) [tauF.IsHaarMeasure] :
    letI := NumberField.Idele.ideleBorel ℚ
    ∃ c : ENNReal, c ≠ 0 ∧ c ≠ ⊤ ∧
      Measure.map IwasawaThree.regroupT ((Measure.pi fun _ : Fin 3 => tauA).prod (Measure.pi fun _ : Fin 3 => tauF)) =
        c • Measure.pi fun _ : Fin 3 => NumberField.Idele.idelicHaar ℚ := by
  letI := NumberField.Idele.ideleBorel ℚ
  haveI := NumberField.Idele.borelSpace_ideleBorel ℚ
  haveI := NumberField.Idele.isHaarMeasure_idelicHaar ℚ

  haveI : SigmaCompactSpace (InfiniteAdeleRing ℚ)ˣ := sigmaCompactSpace_of_locallyCompact_secondCountable
  haveI : SigmaFinite tauA := Measure.IsHaarMeasure.sigmaFinite tauA
  haveI : SigmaFinite tauF := Measure.IsHaarMeasure.sigmaFinite tauF
  haveI : (Measure.pi fun _ : Fin 3 => tauA).IsHaarMeasure := inferInstance
  haveI : (Measure.pi fun _ : Fin 3 => tauF).IsHaarMeasure := inferInstance
  haveI : ((Measure.pi fun _ : Fin 3 => tauA).prod (Measure.pi fun _ : Fin 3 => tauF)).IsHaarMeasure := inferInstance
  haveI : (Measure.pi fun _ : Fin 3 => NumberField.Idele.idelicHaar ℚ).IsHaarMeasure := inferInstance
  haveI : (Measure.map IwasawaThree.regroupT
      ((Measure.pi fun _ : Fin 3 => tauA).prod (Measure.pi fun _ : Fin 3 => tauF))).IsHaarMeasure :=
    MulEquiv.isHaarMeasure_map (μ := (Measure.pi fun _ : Fin 3 => tauA).prod (Measure.pi fun _ : Fin 3 => tauF))
      IwasawaThree.Unipotent.regroupTEquiv IwasawaThree.Unipotent.continuous_regroupT
      IwasawaThree.Unipotent.continuous_regroupTEquiv_symm
  exact IwasawaThree.exists_ennreal_smul_eq_of_isHaarMeasure _ _

private theorem IwasawaThree.densA_mul_densF (a : Fin 3 → (InfiniteAdeleRing ℚ)ˣ)
    (b : Fin 3 → (FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) :
    IwasawaThree.densA a * IwasawaThree.densF b = IwasawaThree.dens (IwasawaThree.regroupT (a, b)) := by
  unfold IwasawaThree.densA IwasawaThree.densF IwasawaThree.dens IwasawaThree.regroupT
  simp only [NumberField.TateGlobal.ideleNorm, IwasawaThree.distribHaarChar_adele_eq_mul,
    ContinuousMulEquiv.apply_symm_apply, NNReal.coe_mul]
  rw [← ENNReal.ofReal_mul]
  · congr 1
    ring
  · positivity

namespace IwasawaThree.Arch
private theorem _root_.LanglandsTunnell.CubicInduction.WhittakerBlock.IwasawaThree.Arch.continuous_regroupT : Continuous IwasawaThree.regroupT := by
  unfold IwasawaThree.regroupT
  refine continuous_pi fun i => ?_
  exact IwasawaThree.ideleSplit.toHomeomorph.symm.continuous.comp
    (((continuous_apply i).comp continuous_fst).prodMk ((continuous_apply i).comp continuous_snd))

end IwasawaThree.Arch
p2m_export "LanglandsTunnell.CubicInduction.WhittakerBlock" "IwasawaThree.Arch.continuous_regroupT"
private theorem IwasawaThree.Arch.continuous_distribHaarChar_infiniteAdele :
    Continuous fun u : (InfiniteAdeleRing ℚ)ˣ => distribHaarChar (InfiniteAdeleRing ℚ) u := by
  have h : (fun u : (InfiniteAdeleRing ℚ)ˣ => distribHaarChar (InfiniteAdeleRing ℚ) u) =
      fun u => ‖IwasawaThree.Arch.archEquiv ((u : (InfiniteAdeleRing ℚ)ˣ) : InfiniteAdeleRing ℚ)‖₊ :=
    funext fun u => IwasawaThree.distribHaarChar_infiniteAdele_eq u
  rw [h]
  exact continuous_nnnorm.comp (IwasawaThree.Arch.continuous_archEquiv.comp Units.continuous_val)

private theorem IwasawaThree.continuous_distribHaarChar_adele :
    Continuous fun t : (AdeleRing (𝓞 ℚ) ℚ)ˣ => distribHaarChar (AdeleRing (𝓞 ℚ) ℚ) t := by
  have h : (fun t : (AdeleRing (𝓞 ℚ) ℚ)ˣ => distribHaarChar (AdeleRing (𝓞 ℚ) ℚ) t) = fun t =>
      distribHaarChar (InfiniteAdeleRing ℚ) (IwasawaThree.ideleSplit t).1 *
        distribHaarChar (FiniteAdeleRing (𝓞 ℚ) ℚ) (IwasawaThree.ideleSplit t).2 :=
    funext IwasawaThree.distribHaarChar_adele_eq_mul
  rw [h]
  have hs : Continuous IwasawaThree.ideleSplit := IwasawaThree.ideleSplit.toHomeomorph.continuous
  exact (IwasawaThree.Arch.continuous_distribHaarChar_infiniteAdele.comp (continuous_fst.comp hs)).mul
    (IwasawaThree.continuous_distribHaarChar_finiteAdele.comp (continuous_snd.comp hs))

namespace IwasawaThree
private theorem _root_.LanglandsTunnell.CubicInduction.WhittakerBlock.IwasawaThree.continuous_ideleNorm : Continuous (NumberField.TateGlobal.ideleNorm ℚ) :=
  NNReal.continuous_coe.comp IwasawaThree.continuous_distribHaarChar_adele

end IwasawaThree
p2m_export "LanglandsTunnell.CubicInduction.WhittakerBlock" "IwasawaThree.continuous_ideleNorm"
private theorem IwasawaThree.measurable_dens :
    letI := NumberField.Idele.ideleBorel ℚ
    Measurable IwasawaThree.dens := by
  letI := NumberField.Idele.ideleBorel ℚ
  haveI := NumberField.Idele.borelSpace_ideleBorel ℚ
  have hn : Measurable (NumberField.TateGlobal.ideleNorm ℚ) := IwasawaThree.continuous_ideleNorm.measurable
  unfold IwasawaThree.dens
  exact ENNReal.measurable_ofReal.comp
    (((hn.comp (measurable_pi_apply 0)).inv.pow_const 2).mul ((hn.comp (measurable_pi_apply 2)).pow_const 2))

private theorem IwasawaThree.Arch.map_withDensity_comp {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (P : Measure α) {e : α → β} (he : Measurable e) {h : β → ℝ≥0∞} (hh : Measurable h) :
    Measure.map e (P.withDensity (h ∘ e)) = (Measure.map e P).withDensity h := by
  ext s hs
  rw [Measure.map_apply he hs, withDensity_apply _ (hs.preimage he), withDensity_apply _ hs,
    setLIntegral_map hs hh he]
  rfl

private theorem IwasawaThree.exists_map_regroupT_withDensity_eq_smul [MeasurableSpace (InfiniteAdeleRing ℚ)ˣ]
    [BorelSpace (InfiniteAdeleRing ℚ)ˣ] [MeasurableSpace (FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ]
    [BorelSpace (FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ] (tauA : Measure (InfiniteAdeleRing ℚ)ˣ) [tauA.IsHaarMeasure]
    (tauF : Measure (FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) [tauF.IsHaarMeasure] :
    letI := NumberField.Idele.ideleBorel ℚ
    ∃ c : ℝ≥0∞, c ≠ 0 ∧ c ≠ ⊤ ∧
      Measure.map IwasawaThree.regroupT
          (((Measure.pi fun _ : Fin 3 => tauA).withDensity IwasawaThree.densA).prod
            ((Measure.pi fun _ : Fin 3 => tauF).withDensity IwasawaThree.densF)) =
        c • (Measure.pi fun _ : Fin 3 => NumberField.Idele.idelicHaar ℚ).withDensity IwasawaThree.dens := by
  letI := NumberField.Idele.ideleBorel ℚ
  haveI := NumberField.Idele.borelSpace_ideleBorel ℚ
  obtain ⟨c, hc0, hct, hc⟩ := IwasawaThree.exists_map_regroupT_eq_smul tauA tauF
  refine ⟨c, hc0, hct, ?_⟩
  have hT : Measurable IwasawaThree.regroupT := IwasawaThree.Arch.continuous_regroupT.measurable
  have hdens : Measurable IwasawaThree.dens := IwasawaThree.measurable_dens
  have hfun : ((fun z : (Fin 3 → (InfiniteAdeleRing ℚ)ˣ) × (Fin 3 → (FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) =>
        IwasawaThree.densF z.2) * fun z => IwasawaThree.densA z.1) =
      IwasawaThree.dens ∘ IwasawaThree.regroupT := by
    funext z
    rw [Pi.mul_apply, mul_comm, Function.comp_apply]
    exact IwasawaThree.densA_mul_densF z.1 z.2
  have hF2 : Measurable fun z : (Fin 3 → (InfiniteAdeleRing ℚ)ˣ) × (Fin 3 → (FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) =>
      IwasawaThree.densF z.2 :=
    IwasawaThree.measurable_densF.comp measurable_snd
  have hA1 : Measurable fun z : (Fin 3 → (InfiniteAdeleRing ℚ)ˣ) × (Fin 3 → (FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) =>
      IwasawaThree.densA z.1 :=
    IwasawaThree.Arch.measurable_densA.comp measurable_fst
  rw [prod_withDensity_left IwasawaThree.Arch.measurable_densA, prod_withDensity_right IwasawaThree.measurable_densF,
    ← withDensity_mul _ hF2 hA1, hfun, IwasawaThree.Arch.map_withDensity_comp _ hT hdens, hc,
    withDensity_smul_measure]

private theorem IwasawaThree.Unipotent.continuous_iwMap (K : Subgroup (AdelicGL 3 (𝓞 ℚ) ℚ)) :
    Continuous (IwasawaThree.iwMap K) := by
  unfold IwasawaThree.iwMap
  exact (((IwasawaThree.continuous_upperUnipotent3 (A := AdeleRing (𝓞 ℚ) ℚ)).comp
      (continuous_fst.comp continuous_fst)).mul
    ((IwasawaThree.continuous_diagUnits (A := AdeleRing (𝓞 ℚ) ℚ)).comp (continuous_snd.comp continuous_fst))).mul
    (continuous_subtype_val.comp continuous_snd)

private theorem IwasawaThree.measurable_iwMap (K : Subgroup (AdelicGL 3 (𝓞 ℚ) ℚ)) :
    letI : MeasurableSpace (AdelicGL 3 (𝓞 ℚ) ℚ) := NumberField.AdelicHaar.glBorel (Fin 3) (𝓞 ℚ) ℚ
    letI : MeasurableSpace (AdeleRing (𝓞 ℚ) ℚ)ˣ := NumberField.Idele.ideleBorel ℚ
    letI : MeasurableSpace (AdeleRing (𝓞 ℚ) ℚ) := NumberField.AdelicHaar.adeleBorel (𝓞 ℚ) ℚ
    Measurable (IwasawaThree.iwMap K) := by
  letI : MeasurableSpace (AdelicGL 3 (𝓞 ℚ) ℚ) := NumberField.AdelicHaar.glBorel (Fin 3) (𝓞 ℚ) ℚ
  letI : MeasurableSpace (AdeleRing (𝓞 ℚ) ℚ)ˣ := NumberField.Idele.ideleBorel ℚ
  letI : MeasurableSpace (AdeleRing (𝓞 ℚ) ℚ) := NumberField.AdelicHaar.adeleBorel (𝓞 ℚ) ℚ
  haveI := NumberField.AdelicHaar.borelSpace_glBorel (Fin 3) (𝓞 ℚ) ℚ
  haveI := NumberField.Idele.borelSpace_ideleBorel ℚ
  haveI := NumberField.AdelicHaar.borelSpace_adeleBorel (𝓞 ℚ) ℚ
  haveI : BorelSpace K := inferInstanceAs (BorelSpace (K : Set (AdelicGL 3 (𝓞 ℚ) ℚ)))
  exact (IwasawaThree.Unipotent.continuous_iwMap K).measurable

private theorem IwasawaThree.lintegral_iwMap_eq (K : Subgroup (AdelicGL 3 (𝓞 ℚ) ℚ)) :
    letI : MeasurableSpace (AdelicGL 3 (𝓞 ℚ) ℚ) := NumberField.AdelicHaar.glBorel (Fin 3) (𝓞 ℚ) ℚ
    letI : MeasurableSpace (AdeleRing (𝓞 ℚ) ℚ)ˣ := NumberField.Idele.ideleBorel ℚ
    letI : MeasurableSpace (AdeleRing (𝓞 ℚ) ℚ) := NumberField.AdelicHaar.adeleBorel (𝓞 ℚ) ℚ
    ∀ (κ : Measure K) [SFinite κ] (φ : AdelicGL 3 (𝓞 ℚ) ℚ → ENNReal), Measurable φ →
      ∫⁻ q, φ (IwasawaThree.iwMap K q)
          ∂((((NumberField.AdelicHaar.adelicAddHaar (𝓞 ℚ) ℚ).prod
            ((NumberField.AdelicHaar.adelicAddHaar (𝓞 ℚ) ℚ).prod (NumberField.AdelicHaar.adelicAddHaar (𝓞 ℚ) ℚ))).prod
            ((Measure.pi fun _ : Fin 3 => NumberField.Idele.idelicHaar ℚ).withDensity IwasawaThree.dens)).prod κ) =
        ∫⁻ n : WhittakerBlock.unipotentSubgroup3, ∫⁻ t : Fin 3 → (AdeleRing (𝓞 ℚ) ℚ)ˣ, ∫⁻ k : K,
          φ ((n : AdelicGL 3 (𝓞 ℚ) ℚ) *
              Units.map (Matrix.diagonalRingHom (Fin 3) (AdeleRing (𝓞 ℚ) ℚ)).toMonoidHom
                (MulEquiv.piUnits.symm t) * k) *
            ENNReal.ofReal ((NumberField.TateGlobal.ideleNorm ℚ (t 0))⁻¹ ^ 2 *
              NumberField.TateGlobal.ideleNorm ℚ (t 2) ^ 2)
          ∂κ ∂(Measure.pi fun _ : Fin 3 => NumberField.Idele.idelicHaar ℚ) ∂WhittakerBlock.unipotentHaar3 := by
  letI : MeasurableSpace (AdelicGL 3 (𝓞 ℚ) ℚ) := NumberField.AdelicHaar.glBorel (Fin 3) (𝓞 ℚ) ℚ
  letI : MeasurableSpace (AdeleRing (𝓞 ℚ) ℚ)ˣ := NumberField.Idele.ideleBorel ℚ
  letI : MeasurableSpace (AdeleRing (𝓞 ℚ) ℚ) := NumberField.AdelicHaar.adeleBorel (𝓞 ℚ) ℚ
  haveI := NumberField.AdelicHaar.borelSpace_glBorel (Fin 3) (𝓞 ℚ) ℚ
  haveI := NumberField.Idele.borelSpace_ideleBorel ℚ
  haveI := NumberField.AdelicHaar.borelSpace_adeleBorel (𝓞 ℚ) ℚ
  haveI := NumberField.AdelicHaar.isAddHaarMeasure_adelicAddHaar (𝓞 ℚ) ℚ
  haveI := NumberField.Idele.isHaarMeasure_idelicHaar ℚ
  haveI : BorelSpace K := inferInstanceAs (BorelSpace (K : Set (AdelicGL 3 (𝓞 ℚ) ℚ)))
  haveI : BorelSpace WhittakerBlock.unipotentSubgroup3 :=
    inferInstanceAs (BorelSpace (WhittakerBlock.unipotentSubgroup3 : Set (AdelicGL 3 (𝓞 ℚ) ℚ)))
  intro κ _ φ hφ

  have hf : Measurable fun z : ((AdeleRing (𝓞 ℚ) ℚ × AdeleRing (𝓞 ℚ) ℚ × AdeleRing (𝓞 ℚ) ℚ) ×
      (Fin 3 → (AdeleRing (𝓞 ℚ) ℚ)ˣ)) × K => φ (IwasawaThree.iwMap K z) :=
    hφ.comp (IwasawaThree.measurable_iwMap K)
  rw [lintegral_prod _ hf.aemeasurable, lintegral_prod _ (Measurable.lintegral_prod_right' (ν := κ) hf).aemeasurable]

  have hG : Measurable fun w : (WhittakerBlock.unipotentSubgroup3 × (Fin 3 → (AdeleRing (𝓞 ℚ) ℚ)ˣ)) × K =>
      φ ((w.1.1 : AdelicGL 3 (𝓞 ℚ) ℚ) *
          Units.map (Matrix.diagonalRingHom (Fin 3) (AdeleRing (𝓞 ℚ) ℚ)).toMonoidHom (MulEquiv.piUnits.symm w.1.2) *
          (w.2 : AdelicGL 3 (𝓞 ℚ) ℚ)) *
        IwasawaThree.dens w.1.2 :=
    (hφ.comp (((continuous_subtype_val.comp (continuous_fst.comp continuous_fst)).mul
      ((IwasawaThree.continuous_diagUnits (A := AdeleRing (𝓞 ℚ) ℚ)).comp (continuous_snd.comp continuous_fst))).mul
        (continuous_subtype_val.comp continuous_snd)).measurable).mul
      (IwasawaThree.measurable_dens.comp (measurable_snd.comp measurable_fst))
  have hF : Measurable (fun n : WhittakerBlock.unipotentSubgroup3 =>
        ∫⁻ t : Fin 3 → (AdeleRing (𝓞 ℚ) ℚ)ˣ, ∫⁻ k : K,
          φ ((n : AdelicGL 3 (𝓞 ℚ) ℚ) *
              Units.map (Matrix.diagonalRingHom (Fin 3) (AdeleRing (𝓞 ℚ) ℚ)).toMonoidHom
                (MulEquiv.piUnits.symm t) * k) *
            ENNReal.ofReal ((NumberField.TateGlobal.ideleNorm ℚ (t 0))⁻¹ ^ 2 *
              NumberField.TateGlobal.ideleNorm ℚ (t 2) ^ 2)
          ∂κ ∂(Measure.pi fun _ : Fin 3 => NumberField.Idele.idelicHaar ℚ)) :=
    Measurable.lintegral_prod_right' (Measurable.lintegral_prod_right' (ν := κ) hG)
  rw [IwasawaThree.Unipotent.unipotentHaar3_eq, lintegral_map hF IwasawaThree.Unipotent.measurable_unip]
  refine lintegral_congr fun x => ?_
  have hx : Measurable fun t : Fin 3 → (AdeleRing (𝓞 ℚ) ℚ)ˣ => ∫⁻ k : K, φ (IwasawaThree.iwMap K ((x, t), k)) ∂κ :=
    Measurable.lintegral_prod_right' (ν := κ)
      (hf.comp ((measurable_const.prodMk measurable_fst).prodMk measurable_snd))
  rw [lintegral_withDensity_eq_lintegral_mul _ IwasawaThree.measurable_dens hx]
  refine lintegral_congr fun t => ?_
  show IwasawaThree.dens t * ∫⁻ k : K, φ (IwasawaThree.iwMap K ((x, t), k)) ∂κ = _
  have hk : Measurable fun k : K => φ (IwasawaThree.iwMap K ((x, t), k)) :=
    hf.comp (measurable_const.prodMk measurable_id)
  rw [mul_comm, ← lintegral_mul_const _ hk]
  rfl

private abbrev IwasawaThree.Unipotent.Zf : Set Af := NumberField.AdelicBox.integralFiniteAdeles (𝓞 ℚ) ℚ

private theorem IwasawaThree.Unipotent.Zf_eq :
    Zf = NumberField.AdelicLevel.integralFiniteAdeles (𝓞 ℚ) ℚ := rfl

private theorem IwasawaThree.Unipotent.integralFiniteAdeles_eq :
    NumberField.AdelicBox.integralFiniteAdeles (𝓞 ℚ) ℚ = NumberField.AdelicLevel.integralFiniteAdeles (𝓞 ℚ) ℚ := rfl

private theorem IwasawaThree.Unipotent.neg_mem_Zf {x : Af}
    (hx : x ∈ NumberField.AdelicLevel.integralFiniteAdeles (𝓞 ℚ) ℚ) :
    -x ∈ NumberField.AdelicLevel.integralFiniteAdeles (𝓞 ℚ) ℚ := by
  have h := NumberField.AdelicLevel.sub_mem_integralFiniteAdeles NumberField.AdelicLevel.zero_mem_integralFiniteAdeles hx
  rwa [zero_sub] at h

private theorem IwasawaThree.Unipotent.upperUnipotent3_inv' {A : Type*} [CommRing A] (x y z : A) :
    (upperUnipotent3 x y z)⁻¹ = upperUnipotent3 (-x) (-y) (x * y - z) := by
  refine inv_eq_of_mul_eq_one_right ?_
  rw [upperUnipotent3_mul']
  simp only [add_neg_cancel]
  rw [show z + (x * y - z) + x * -y = 0 by ring, upperUnipotent3_zero]

private noncomputable def IwasawaThree.Unipotent.bPart (q : (Af × Af × Af) × (Fin 3 → Afˣ)) : GL (Fin 3) Af :=
  upperUnipotent3 q.1.1 q.1.2.1 q.1.2.2 * IwasawaThree.diagGL q.2

private theorem IwasawaThree.Unipotent.iwMapF_eq (q : (Af × Af × Af) × (Fin 3 → Afˣ)) (k : IwasawaThree.intGL3f) :
    IwasawaThree.iwMapF (q, k) = bPart q * (k : GL (Fin 3) Af) := rfl

private theorem IwasawaThree.Unipotent.coe_bPart (q : (Af × Af × Af) × (Fin 3 → Afˣ)) :
    ((bPart q : GL (Fin 3) Af) : Matrix (Fin 3) (Fin 3) Af) =
      !![(q.2 0 : Af), q.1.1 * q.2 1, q.1.2.2 * q.2 2; 0, q.2 1, q.1.2.1 * q.2 2; 0, 0, q.2 2] := by
  rw [bPart, Units.val_mul, coe_diagGL']
  ext i j
  fin_cases i <;> fin_cases j <;> simp [upperUnipotent3, Matrix.mul_apply, Matrix.diagonal]

private theorem IwasawaThree.Unipotent.coe_bPart_inv (q : (Af × Af × Af) × (Fin 3 → Afˣ)) :
    (((bPart q)⁻¹ : GL (Fin 3) Af) : Matrix (Fin 3) (Fin 3) Af) =
      !![(((q.2 0)⁻¹ : Afˣ) : Af), (((q.2 0)⁻¹ : Afˣ) : Af) * -q.1.1,
          (((q.2 0)⁻¹ : Afˣ) : Af) * (q.1.1 * q.1.2.1 - q.1.2.2);
        0, (((q.2 1)⁻¹ : Afˣ) : Af), (((q.2 1)⁻¹ : Afˣ) : Af) * -q.1.2.1;
        0, 0, (((q.2 2)⁻¹ : Afˣ) : Af)] := by
  rw [bPart, mul_inv_rev, Units.val_mul, coe_diagGL_inv', upperUnipotent3_inv']
  ext i j
  fin_cases i <;> fin_cases j <;> simp [upperUnipotent3, Matrix.mul_apply, Matrix.diagonal]

private def IwasawaThree.Unipotent.box : Set ((Af × Af × Af) × (Fin 3 → Afˣ)) :=
  (Zf ×ˢ Zf ×ˢ Zf) ×ˢ Set.pi Set.univ fun _ : Fin 3 => (IwasawaThree.intUnitsF : Set Afˣ)

private theorem IwasawaThree.Unipotent.mem_box_iff (q : (Af × Af × Af) × (Fin 3 → Afˣ)) :
    q ∈ box ↔ (q.1.1 ∈ Zf ∧ q.1.2.1 ∈ Zf ∧ q.1.2.2 ∈ Zf) ∧ ∀ i, q.2 i ∈ IwasawaThree.intUnitsF := by
  simp only [box, Set.mem_prod, Set.mem_univ_pi, SetLike.mem_coe]

private theorem IwasawaThree.Unipotent.bPart_mem_iff (q : (Af × Af × Af) × (Fin 3 → Afˣ)) :
    bPart q ∈ IwasawaThree.intGL3f ↔ q ∈ box := by
  rw [← SetLike.mem_coe, IwasawaThree.coe_intGL3f_eq_units, SetLike.mem_coe, Submonoid.mem_units_iff,
    IwasawaThree.mem_intMat3f_iff, IwasawaThree.mem_intMat3f_iff, coe_bPart, coe_bPart_inv, mem_box_iff]
  rw [integralFiniteAdeles_eq, Zf_eq]
  constructor
  · rintro ⟨h, h'⟩
    have ht0 : (q.2 0 : Af) ∈ NumberField.AdelicLevel.integralFiniteAdeles (𝓞 ℚ) ℚ := by simpa using h 0 0
    have ht1 : (q.2 1 : Af) ∈ NumberField.AdelicLevel.integralFiniteAdeles (𝓞 ℚ) ℚ := by simpa using h 1 1
    have ht2 : (q.2 2 : Af) ∈ NumberField.AdelicLevel.integralFiniteAdeles (𝓞 ℚ) ℚ := by simpa using h 2 2
    have ht0' : (((q.2 0)⁻¹ : Afˣ) : Af) ∈ NumberField.AdelicLevel.integralFiniteAdeles (𝓞 ℚ) ℚ := by simpa using h' 0 0
    have ht1' : (((q.2 1)⁻¹ : Afˣ) : Af) ∈ NumberField.AdelicLevel.integralFiniteAdeles (𝓞 ℚ) ℚ := by simpa using h' 1 1
    have ht2' : (((q.2 2)⁻¹ : Afˣ) : Af) ∈ NumberField.AdelicLevel.integralFiniteAdeles (𝓞 ℚ) ℚ := by simpa using h' 2 2
    have hx1 : q.1.1 * q.2 1 ∈ NumberField.AdelicLevel.integralFiniteAdeles (𝓞 ℚ) ℚ := by simpa using h 0 1
    have hz2 : q.1.2.2 * q.2 2 ∈ NumberField.AdelicLevel.integralFiniteAdeles (𝓞 ℚ) ℚ := by simpa using h 0 2
    have hy2 : q.1.2.1 * q.2 2 ∈ NumberField.AdelicLevel.integralFiniteAdeles (𝓞 ℚ) ℚ := by simpa using h 1 2
    refine ⟨⟨?_, ?_, ?_⟩, fun i => ?_⟩
    · simpa using NumberField.AdelicLevel.mul_mem_integralFiniteAdeles hx1 ht1'
    · simpa using NumberField.AdelicLevel.mul_mem_integralFiniteAdeles hy2 ht2'
    · simpa using NumberField.AdelicLevel.mul_mem_integralFiniteAdeles hz2 ht2'
    · rw [IwasawaThree.mem_intUnitsF_iff, integralFiniteAdeles_eq]
      fin_cases i
      · exact ⟨ht0, ht0'⟩
      · exact ⟨ht1, ht1'⟩
      · exact ⟨ht2, ht2'⟩
  · rintro ⟨⟨hx, hy, hz⟩, ht⟩
    have hu : ∀ i, (q.2 i : Af) ∈ NumberField.AdelicLevel.integralFiniteAdeles (𝓞 ℚ) ℚ ∧
        (((q.2 i)⁻¹ : Afˣ) : Af) ∈ NumberField.AdelicLevel.integralFiniteAdeles (𝓞 ℚ) ℚ := fun i => by
      have hi := (IwasawaThree.mem_intUnitsF_iff _).1 (ht i)
      rwa [integralFiniteAdeles_eq] at hi

    refine ⟨fun i j => ?_, fun i j => ?_⟩ <;> fin_cases i <;> fin_cases j
    · simpa using (hu 0).1
    · simpa using NumberField.AdelicLevel.mul_mem_integralFiniteAdeles hx (hu 1).1
    · simpa using NumberField.AdelicLevel.mul_mem_integralFiniteAdeles hz (hu 2).1
    · simpa using NumberField.AdelicLevel.zero_mem_integralFiniteAdeles
    · simpa using (hu 1).1
    · simpa using NumberField.AdelicLevel.mul_mem_integralFiniteAdeles hy (hu 2).1
    · simpa using NumberField.AdelicLevel.zero_mem_integralFiniteAdeles
    · simpa using NumberField.AdelicLevel.zero_mem_integralFiniteAdeles
    · simpa using (hu 2).1
    · simpa using (hu 0).2
    · simpa using NumberField.AdelicLevel.mul_mem_integralFiniteAdeles (hu 0).2 (neg_mem_Zf hx)
    · simpa using NumberField.AdelicLevel.mul_mem_integralFiniteAdeles (hu 0).2
        (NumberField.AdelicLevel.sub_mem_integralFiniteAdeles
          (NumberField.AdelicLevel.mul_mem_integralFiniteAdeles hx hy) hz)
    · simpa using NumberField.AdelicLevel.zero_mem_integralFiniteAdeles
    · simpa using (hu 1).2
    · simpa using NumberField.AdelicLevel.mul_mem_integralFiniteAdeles (hu 1).2 (neg_mem_Zf hy)
    · simpa using NumberField.AdelicLevel.zero_mem_integralFiniteAdeles
    · simpa using NumberField.AdelicLevel.zero_mem_integralFiniteAdeles
    · simpa using (hu 2).2

private theorem IwasawaThree.Unipotent.measurableSet_box [MeasurableSpace Af] [BorelSpace Af] [MeasurableSpace Afˣ]
    [BorelSpace Afˣ] : MeasurableSet box := by
  have hZ : MeasurableSet Zf := (NumberField.AdelicBox.isOpen_integralFiniteAdeles ℚ).measurableSet
  exact (hZ.prod (hZ.prod hZ)).prod (MeasurableSet.univ_pi fun _ => IwasawaThree.isOpen_intUnitsF.measurableSet)

private theorem IwasawaThree.Unipotent.densF_eq_one_of_forall_mem {t : Fin 3 → Afˣ}
    (ht : ∀ i, t i ∈ IwasawaThree.intUnitsF) : IwasawaThree.densF t = 1 := by
  simp [IwasawaThree.densF, IwasawaThree.distribHaarChar_eq_one_of_mem_intUnitsF (ht 0),
    IwasawaThree.distribHaarChar_eq_one_of_mem_intUnitsF (ht 2)]

private theorem IwasawaThree.Unipotent.measure_box [MeasurableSpace Af] [BorelSpace Af] [MeasurableSpace Afˣ]
    [BorelSpace Afˣ] (lam : Measure Af) [lam.IsAddHaarMeasure] (tau : Measure Afˣ) [tau.IsHaarMeasure] :
    (lam.prod (lam.prod lam)).prod ((Measure.pi fun _ : Fin 3 => tau).withDensity IwasawaThree.densF) box =
      lam Zf * (lam Zf * lam Zf) * tau (IwasawaThree.intUnitsF : Set Afˣ) ^ 3 := by
  have hU : MeasurableSet (Set.pi Set.univ fun _ : Fin 3 => (IwasawaThree.intUnitsF : Set Afˣ)) :=
    MeasurableSet.univ_pi fun _ => IwasawaThree.isOpen_intUnitsF.measurableSet
  rw [box, Measure.prod_prod, Measure.prod_prod, Measure.prod_prod, MeasureTheory.withDensity_apply _ hU,
    setLIntegral_congr_fun hU (g := fun _ => 1) fun t ht => densF_eq_one_of_forall_mem fun i => by
      simpa using (Set.mem_univ_pi.1 ht) i,
    setLIntegral_one, Measure.pi_pi]
  simp

private theorem IwasawaThree.Unipotent.measure_section [MeasurableSpace (GL (Fin 3) Af)] [BorelSpace (GL (Fin 3) Af)]
    (kap : Measure IwasawaThree.intGL3f) [kap.IsHaarMeasure] {A : Set (GL (Fin 3) Af)}
    (hAK : A ⊆ (IwasawaThree.intGL3f : Set (GL (Fin 3) Af))) (q : (Af × Af × Af) × (Fin 3 → Afˣ)) :
    kap (Prod.mk q ⁻¹' (IwasawaThree.iwMapF ⁻¹' A)) =
      box.indicator (fun _ => kap ((Subtype.val : IwasawaThree.intGL3f → GL (Fin 3) Af) ⁻¹' A)) q := by
  haveI : BorelSpace IwasawaThree.intGL3f :=
    inferInstanceAs (BorelSpace (IwasawaThree.intGL3f : Set (GL (Fin 3) Af)))
  classical
  rw [Set.indicator_apply]
  split_ifs with hq
  · have hb : bPart q ∈ IwasawaThree.intGL3f := (bPart_mem_iff q).2 hq
    have hset : Prod.mk q ⁻¹' (IwasawaThree.iwMapF ⁻¹' A) =
        (fun k : IwasawaThree.intGL3f => (⟨bPart q, hb⟩ : IwasawaThree.intGL3f) * k) ⁻¹'
          ((Subtype.val : IwasawaThree.intGL3f → GL (Fin 3) Af) ⁻¹' A) := by
      ext k
      simp [iwMapF_eq]
    rw [hset, measure_preimage_mul]
  · have hset : Prod.mk q ⁻¹' (IwasawaThree.iwMapF ⁻¹' A) = ∅ := by
      ext k
      simp only [Set.mem_preimage, iwMapF_eq, Set.mem_empty_iff_false, iff_false]
      intro hk
      have hmem : bPart q * (k : GL (Fin 3) Af) ∈ IwasawaThree.intGL3f := hAK hk
      exact hq ((bPart_mem_iff q).1 (by simpa using mul_mem hmem (inv_mem k.2)))
    rw [hset, measure_empty]

private theorem IwasawaThree.Unipotent.nuF_apply_of_subset [MeasurableSpace Af] [BorelSpace Af] [MeasurableSpace Afˣ]
    [BorelSpace Afˣ] [MeasurableSpace (GL (Fin 3) Af)] [BorelSpace (GL (Fin 3) Af)]
    (lam : Measure Af) [lam.IsAddHaarMeasure] (tau : Measure Afˣ) [tau.IsHaarMeasure]
    (kap : Measure IwasawaThree.intGL3f) [kap.IsHaarMeasure] {A : Set (GL (Fin 3) Af)}
    (hAK : A ⊆ (IwasawaThree.intGL3f : Set (GL (Fin 3) Af))) (hA : MeasurableSet A) :
    IwasawaThree.nuF lam tau kap A =
      kap ((Subtype.val : IwasawaThree.intGL3f → GL (Fin 3) Af) ⁻¹' A) *
        (lam Zf * (lam Zf * lam Zf) * tau (IwasawaThree.intUnitsF : Set Afˣ) ^ 3) := by
  haveI : CompactSpace IwasawaThree.intGL3f := IwasawaThree.compactSpace_intGL3f
  rw [IwasawaThree.nuF, Measure.map_apply IwasawaThree.measurable_iwMapF hA,
    Measure.prod_apply (IwasawaThree.measurable_iwMapF hA), lintegral_congr (measure_section kap hAK),
    lintegral_indicator_const measurableSet_box, measure_box]

private theorem IwasawaThree.Unipotent.isHaarMeasure_comap [MeasurableSpace (GL (Fin 3) Af)]
    [BorelSpace (GL (Fin 3) Af)] (muf : Measure (GL (Fin 3) Af)) [muf.IsHaarMeasure] :
    (muf.comap (Subtype.val : IwasawaThree.intGL3f → GL (Fin 3) Af)).IsHaarMeasure := by
  haveI : BorelSpace IwasawaThree.intGL3f :=
    inferInstanceAs (BorelSpace (IwasawaThree.intGL3f : Set (GL (Fin 3) Af)))
  exact Measure.IsHaarMeasure.comap muf (f := IwasawaThree.intGL3f.subtype) (mH := inferInstance)
    (IwasawaThree.isOpen_intGL3f.isOpenEmbedding_subtypeVal)

private theorem IwasawaThree.Unipotent.comap_apply_of_subset [MeasurableSpace (GL (Fin 3) Af)]
    [BorelSpace (GL (Fin 3) Af)] (muf : Measure (GL (Fin 3) Af)) {A : Set (GL (Fin 3) Af)}
    (hAK : A ⊆ (IwasawaThree.intGL3f : Set (GL (Fin 3) Af))) :
    muf.comap (Subtype.val : IwasawaThree.intGL3f → GL (Fin 3) Af)
        ((Subtype.val : IwasawaThree.intGL3f → GL (Fin 3) Af) ⁻¹' A) = muf A := by
  refine (comap_subtype_coe_apply IwasawaThree.isOpen_intGL3f.measurableSet muf _).trans ?_
  congr 1
  ext g
  constructor
  · rintro ⟨k, hk, rfl⟩
    exact hk
  · intro hg
    exact ⟨⟨g, hAK hg⟩, hg, rfl⟩

private theorem IwasawaThree.exists_forall_nuF_eq_mul [MeasurableSpace (FiniteAdeleRing (𝓞 ℚ) ℚ)]
    [BorelSpace (FiniteAdeleRing (𝓞 ℚ) ℚ)] [MeasurableSpace (FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ]
    [BorelSpace (FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ] [MeasurableSpace (GL (Fin 3) (FiniteAdeleRing (𝓞 ℚ) ℚ))]
    [BorelSpace (GL (Fin 3) (FiniteAdeleRing (𝓞 ℚ) ℚ))]
    (muf : Measure (GL (Fin 3) (FiniteAdeleRing (𝓞 ℚ) ℚ))) [muf.IsHaarMeasure]
    (lam : Measure (FiniteAdeleRing (𝓞 ℚ) ℚ)) [lam.IsAddHaarMeasure]
    (tau : Measure (FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) [tau.IsHaarMeasure]
    (kap : Measure IwasawaThree.intGL3f) [kap.IsHaarMeasure] :
    ∃ c : ENNReal, c ≠ 0 ∧ c ≠ ⊤ ∧ ∀ A : Set (GL (Fin 3) (FiniteAdeleRing (𝓞 ℚ) ℚ)),
      A ⊆ (IwasawaThree.intGL3f : Set (GL (Fin 3) (FiniteAdeleRing (𝓞 ℚ) ℚ))) → MeasurableSet A →
        IwasawaThree.nuF lam tau kap A = c * muf A := by

  haveI : BorelSpace IwasawaThree.intGL3f :=
    inferInstanceAs (BorelSpace (IwasawaThree.intGL3f : Set (GL (Fin 3) (FiniteAdeleRing (𝓞 ℚ) ℚ))))
  haveI : LocallyCompactSpace IwasawaThree.intGL3f := IwasawaThree.isOpen_intGL3f.locallyCompactSpace
  haveI := IwasawaThree.Unipotent.isHaarMeasure_comap muf
  obtain ⟨c', hc'0, hc'top, hc'⟩ := IwasawaThree.exists_ennreal_smul_eq_of_isHaarMeasure
    (muf.comap (Subtype.val : IwasawaThree.intGL3f → GL (Fin 3) (FiniteAdeleRing (𝓞 ℚ) ℚ))) kap

  set m : ENNReal := lam IwasawaThree.Unipotent.Zf * (lam IwasawaThree.Unipotent.Zf * lam IwasawaThree.Unipotent.Zf) *
    tau (IwasawaThree.intUnitsF : Set (FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) ^ 3 with hm
  have hZ0 : lam IwasawaThree.Unipotent.Zf ≠ 0 :=
    ((NumberField.AdelicBox.isOpen_integralFiniteAdeles ℚ).measure_pos lam
      ⟨0, NumberField.AdelicLevel.zero_mem_integralFiniteAdeles⟩).ne'
  have hZtop : lam IwasawaThree.Unipotent.Zf ≠ ⊤ :=
    (NumberField.AdelicBox.isCompact_integralFiniteAdeles ℚ).measure_lt_top.ne
  have hU0 : tau (IwasawaThree.intUnitsF : Set (FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) ≠ 0 :=
    (IwasawaThree.isOpen_intUnitsF.measure_pos tau ⟨1, IwasawaThree.intUnitsF.one_mem⟩).ne'
  have hUtop : tau (IwasawaThree.intUnitsF : Set (FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) ≠ ⊤ :=
    IwasawaThree.isCompact_intUnitsF.measure_lt_top.ne
  have hm0 : m ≠ 0 := mul_ne_zero (mul_ne_zero hZ0 (mul_ne_zero hZ0 hZ0)) (pow_ne_zero 3 hU0)
  have hmtop : m ≠ ⊤ :=
    ENNReal.mul_ne_top (ENNReal.mul_ne_top hZtop (ENNReal.mul_ne_top hZtop hZtop)) (ENNReal.pow_ne_top hUtop)
  refine ⟨m * c'⁻¹, mul_ne_zero hm0 (ENNReal.inv_ne_zero.2 hc'top),
    ENNReal.mul_ne_top hmtop (ENNReal.inv_ne_top.2 hc'0), fun A hAK hA => ?_⟩
  have hmuf : muf A = c' * kap (Subtype.val ⁻¹' A) := by
    rw [← IwasawaThree.Unipotent.comap_apply_of_subset muf hAK, hc', Measure.smul_apply, smul_eq_mul]
  have hkap : kap (Subtype.val ⁻¹' A) = c'⁻¹ * muf A := by
    rw [hmuf, ← mul_assoc, ENNReal.inv_mul_cancel hc'0 hc'top, one_mul]
  rw [IwasawaThree.Unipotent.nuF_apply_of_subset lam tau kap hAK hA, hkap, ← hm]
  ring

private theorem IwasawaThree.exists_nuF_eq_smul
    [MeasurableSpace (FiniteAdeleRing (𝓞 ℚ) ℚ)] [BorelSpace (FiniteAdeleRing (𝓞 ℚ) ℚ)]
    [MeasurableSpace (FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ] [BorelSpace (FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ]
    [MeasurableSpace (GL (Fin 3) (FiniteAdeleRing (𝓞 ℚ) ℚ))] [BorelSpace (GL (Fin 3) (FiniteAdeleRing (𝓞 ℚ) ℚ))]
    (muf : Measure (GL (Fin 3) (FiniteAdeleRing (𝓞 ℚ) ℚ))) [muf.IsHaarMeasure]
    (kap : Measure IwasawaThree.intGL3f) [kap.IsHaarMeasure]
    (lam : Measure (FiniteAdeleRing (𝓞 ℚ) ℚ)) [lam.IsAddHaarMeasure]
    (tau : Measure (FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) [tau.IsHaarMeasure] :
    ∃ c : ENNReal, c ≠ 0 ∧ c ≠ ⊤ ∧ IwasawaThree.nuF lam tau kap = c • muf := by
  haveI : CompactSpace IwasawaThree.intGL3f := IwasawaThree.compactSpace_intGL3f
  haveI : IsFiniteMeasure kap := ⟨(isCompact_univ (X := IwasawaThree.intGL3f)).measure_lt_top⟩
  obtain ⟨c₄, hc₀, hc₁, hK⟩ := IwasawaThree.exists_forall_nuF_eq_mul muf lam tau kap
  have hν : IwasawaThree.nuF lam tau kap = c₄ • muf :=
    IwasawaThree.eq_smul_of_isOpen_of_forall_subset (IwasawaThree.upperTriangular3 (FiniteAdeleRing (𝓞 ℚ) ℚ))
      IwasawaThree.intGL3f IwasawaThree.isOpen_intGL3f IwasawaThree.exists_mem_upperTriangular3_inv_mul_mem_intGL3f
      muf (IwasawaThree.nuF lam tau kap) c₄
      (fun b _ A hA => IwasawaThree.measure_image_mul_eq_of_map_eq muf b (map_mul_left_eq_self muf b) A hA)
      (fun b hb A hA => IwasawaThree.measure_image_mul_eq_of_map_eq (IwasawaThree.nuF lam tau kap) b
        (IwasawaThree.map_mul_left_nuF lam tau kap b hb) A hA)
      hK
  exact ⟨c₄, hc₀, hc₁, hν⟩

private theorem IwasawaThree.exists_lintegral_finiteAdele_eq_mul_lintegral_iwasawa
    [MeasurableSpace (FiniteAdeleRing (𝓞 ℚ) ℚ)] [BorelSpace (FiniteAdeleRing (𝓞 ℚ) ℚ)]
    [MeasurableSpace (FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ] [BorelSpace (FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ]
    [MeasurableSpace (GL (Fin 3) (FiniteAdeleRing (𝓞 ℚ) ℚ))] [BorelSpace (GL (Fin 3) (FiniteAdeleRing (𝓞 ℚ) ℚ))]
    (muf : Measure (GL (Fin 3) (FiniteAdeleRing (𝓞 ℚ) ℚ))) [muf.IsHaarMeasure]
    (kap : Measure IwasawaThree.intGL3f) [kap.IsHaarMeasure]
    (lam : Measure (FiniteAdeleRing (𝓞 ℚ) ℚ)) [lam.IsAddHaarMeasure]
    (tau : Measure (FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) [tau.IsHaarMeasure] :
    ∃ c : ENNReal, c ≠ 0 ∧ c ≠ ⊤ ∧ ∀ φ : GL (Fin 3) (FiniteAdeleRing (𝓞 ℚ) ℚ) → ENNReal, Measurable φ →
      ∫⁻ g, φ g ∂muf =
        c * ∫⁻ x : FiniteAdeleRing (𝓞 ℚ) ℚ × FiniteAdeleRing (𝓞 ℚ) ℚ × FiniteAdeleRing (𝓞 ℚ) ℚ,
          ∫⁻ t : Fin 3 → (FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ, ∫⁻ k : IwasawaThree.intGL3f,
            φ (upperUnipotent3 x.1 x.2.1 x.2.2 *
                Units.map (Matrix.diagonalRingHom (Fin 3) (FiniteAdeleRing (𝓞 ℚ) ℚ)).toMonoidHom
                  (MulEquiv.piUnits.symm t) * (k : GL (Fin 3) (FiniteAdeleRing (𝓞 ℚ) ℚ))) *
              IwasawaThree.densF t
          ∂kap ∂(Measure.pi fun _ : Fin 3 => tau) ∂(lam.prod (lam.prod lam)) := by
  haveI : CompactSpace IwasawaThree.intGL3f := IwasawaThree.compactSpace_intGL3f
  haveI : IsFiniteMeasure kap := ⟨(isCompact_univ (X := IwasawaThree.intGL3f)).measure_lt_top⟩
  obtain ⟨c₄, hc₀, hc₁, hν⟩ := IwasawaThree.exists_nuF_eq_smul muf kap lam tau
  refine ⟨c₄⁻¹, ENNReal.inv_ne_zero.2 hc₁, ENNReal.inv_ne_top.2 hc₀, fun φ hφ => ?_⟩
  have hiw : Measurable IwasawaThree.iwMapF := IwasawaThree.measurable_iwMapF
  have hF : Measurable fun q => φ (IwasawaThree.iwMapF q) := hφ.comp hiw
  have hG : ∀ x : FiniteAdeleRing (𝓞 ℚ) ℚ × FiniteAdeleRing (𝓞 ℚ) ℚ × FiniteAdeleRing (𝓞 ℚ) ℚ,
      Measurable fun q : (Fin 3 → (FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) × IwasawaThree.intGL3f =>
        φ (IwasawaThree.iwMapF ((x, q.1), q.2)) :=
    fun x => hF.comp ((measurable_const.prodMk measurable_fst).prodMk measurable_snd)
  have h₁ : ∫⁻ g, φ g ∂muf = c₄⁻¹ * ∫⁻ g, φ g ∂(IwasawaThree.nuF lam tau kap) := by
    rw [hν, lintegral_smul_measure, smul_eq_mul, ← mul_assoc, ENNReal.inv_mul_cancel hc₀ hc₁, one_mul]
  rw [h₁]
  congr 1
  rw [IwasawaThree.nuF, lintegral_map hφ hiw, lintegral_prod _ hF.aemeasurable,
    lintegral_prod _ hF.lintegral_prod_right'.aemeasurable]
  refine lintegral_congr fun x => ?_
  rw [lintegral_withDensity_eq_lintegral_mul _ IwasawaThree.measurable_densF (hG x).lintegral_prod_right']
  refine lintegral_congr fun t => ?_
  have hk : Measurable fun k : IwasawaThree.intGL3f => φ (IwasawaThree.iwMapF ((x, t), k)) :=
    hF.comp (measurable_const.prodMk measurable_id)
  show IwasawaThree.densF t * ∫⁻ k, φ (IwasawaThree.iwMapF ((x, t), k)) ∂kap = _
  rw [mul_comm, ← lintegral_mul_const _ hk]
  rfl

private abbrev IwasawaThree.ArchData : Type :=
  ((InfiniteAdeleRing ℚ × InfiniteAdeleRing ℚ × InfiniteAdeleRing ℚ) × (Fin 3 → (InfiniteAdeleRing ℚ)ˣ)) ×
    IwasawaThree.orthSubgroupInf

private abbrev IwasawaThree.FinData : Type :=
  ((FiniteAdeleRing (𝓞 ℚ) ℚ × FiniteAdeleRing (𝓞 ℚ) ℚ × FiniteAdeleRing (𝓞 ℚ) ℚ) ×
      (Fin 3 → (FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ)) × IwasawaThree.intGL3f

private theorem IwasawaThree.measurable_regroupK
    (K : Subgroup (AdelicGL 3 (𝓞 ℚ) ℚ))
    (hK : ∀ k : AdelicGL 3 (𝓞 ℚ) ℚ, k ∈ K ↔ archComponent3 (𝓞 ℚ) ℚ k ∈ orth3 ∧
      ∀ p : HeightOneSpectrum (𝓞 ℚ), componentAt3 (𝓞 ℚ) ℚ p k ∈ localMaximalCompact3 (𝓞 ℚ) ℚ p)
    [MeasurableSpace (GL (Fin 3) (InfiniteAdeleRing ℚ))] [BorelSpace (GL (Fin 3) (InfiniteAdeleRing ℚ))]
    [MeasurableSpace (GL (Fin 3) (FiniteAdeleRing (𝓞 ℚ) ℚ))] [BorelSpace (GL (Fin 3) (FiniteAdeleRing (𝓞 ℚ) ℚ))] :
    letI : MeasurableSpace (AdelicGL 3 (𝓞 ℚ) ℚ) := NumberField.AdelicHaar.glBorel (Fin 3) (𝓞 ℚ) ℚ
    Measurable (IwasawaThree.regroupK K hK) := by
  letI : MeasurableSpace (AdelicGL 3 (𝓞 ℚ) ℚ) := NumberField.AdelicHaar.glBorel (Fin 3) (𝓞 ℚ) ℚ
  haveI : BorelSpace (AdelicGL 3 (𝓞 ℚ) ℚ) := NumberField.AdelicHaar.borelSpace_glBorel (Fin 3) (𝓞 ℚ) ℚ
  haveI : BorelSpace K := inferInstanceAs (BorelSpace (K : Set (AdelicGL 3 (𝓞 ℚ) ℚ)))
  haveI : BorelSpace IwasawaThree.orthSubgroupInf :=
    inferInstanceAs (BorelSpace (IwasawaThree.orthSubgroupInf : Set (GL (Fin 3) (InfiniteAdeleRing ℚ))))
  haveI : BorelSpace IwasawaThree.intGL3f :=
    inferInstanceAs (BorelSpace (IwasawaThree.intGL3f : Set (GL (Fin 3) (FiniteAdeleRing (𝓞 ℚ) ℚ))))
  exact (IwasawaThree.regroupKEquiv K hK).continuous_toFun.measurable

private noncomputable def IwasawaThree.regroup3
    (K : Subgroup (AdelicGL 3 (𝓞 ℚ) ℚ))
    (hK : ∀ k : AdelicGL 3 (𝓞 ℚ) ℚ, k ∈ K ↔ archComponent3 (𝓞 ℚ) ℚ k ∈ orth3 ∧
      ∀ p : HeightOneSpectrum (𝓞 ℚ), componentAt3 (𝓞 ℚ) ℚ p k ∈ localMaximalCompact3 (𝓞 ℚ) ℚ p)
    (p : IwasawaThree.ArchData × IwasawaThree.FinData) :
    ((AdeleRing (𝓞 ℚ) ℚ × AdeleRing (𝓞 ℚ) ℚ × AdeleRing (𝓞 ℚ) ℚ) × (Fin 3 → (AdeleRing (𝓞 ℚ) ℚ)ˣ)) × K :=
  ((IwasawaThree.regroupN (p.1.1.1, p.2.1.1), IwasawaThree.regroupT (p.1.1.2, p.2.1.2)),
    IwasawaThree.regroupK K hK (p.1.2, p.2.2))

private theorem IwasawaThree.measurable_regroup3
    (K : Subgroup (AdelicGL 3 (𝓞 ℚ) ℚ))
    (hK : ∀ k : AdelicGL 3 (𝓞 ℚ) ℚ, k ∈ K ↔ archComponent3 (𝓞 ℚ) ℚ k ∈ orth3 ∧
      ∀ p : HeightOneSpectrum (𝓞 ℚ), componentAt3 (𝓞 ℚ) ℚ p k ∈ localMaximalCompact3 (𝓞 ℚ) ℚ p)
    [MeasurableSpace (InfiniteAdeleRing ℚ)] [BorelSpace (InfiniteAdeleRing ℚ)]
    [MeasurableSpace (FiniteAdeleRing (𝓞 ℚ) ℚ)] [BorelSpace (FiniteAdeleRing (𝓞 ℚ) ℚ)]
    [MeasurableSpace (InfiniteAdeleRing ℚ)ˣ] [BorelSpace (InfiniteAdeleRing ℚ)ˣ]
    [MeasurableSpace (FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ] [BorelSpace (FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ]
    [MeasurableSpace (GL (Fin 3) (InfiniteAdeleRing ℚ))] [BorelSpace (GL (Fin 3) (InfiniteAdeleRing ℚ))]
    [MeasurableSpace (GL (Fin 3) (FiniteAdeleRing (𝓞 ℚ) ℚ))] [BorelSpace (GL (Fin 3) (FiniteAdeleRing (𝓞 ℚ) ℚ))] :
    letI : MeasurableSpace (AdelicGL 3 (𝓞 ℚ) ℚ) := NumberField.AdelicHaar.glBorel (Fin 3) (𝓞 ℚ) ℚ
    letI : MeasurableSpace (AdeleRing (𝓞 ℚ) ℚ)ˣ := NumberField.Idele.ideleBorel ℚ
    letI : MeasurableSpace (AdeleRing (𝓞 ℚ) ℚ) := NumberField.AdelicHaar.adeleBorel (𝓞 ℚ) ℚ
    Measurable (IwasawaThree.regroup3 K hK) := by
  letI : MeasurableSpace (AdelicGL 3 (𝓞 ℚ) ℚ) := NumberField.AdelicHaar.glBorel (Fin 3) (𝓞 ℚ) ℚ
  letI : MeasurableSpace (AdeleRing (𝓞 ℚ) ℚ)ˣ := NumberField.Idele.ideleBorel ℚ
  letI : MeasurableSpace (AdeleRing (𝓞 ℚ) ℚ) := NumberField.AdelicHaar.adeleBorel (𝓞 ℚ) ℚ
  exact ((IwasawaThree.measurable_regroupN.comp
      ((measurable_fst.comp (measurable_fst.comp measurable_fst)).prodMk
        (measurable_fst.comp (measurable_fst.comp measurable_snd)))).prodMk
    (IwasawaThree.measurable_regroupT.comp
      ((measurable_snd.comp (measurable_fst.comp measurable_fst)).prodMk
        (measurable_snd.comp (measurable_fst.comp measurable_snd))))).prodMk
    ((IwasawaThree.measurable_regroupK K hK).comp
      ((measurable_snd.comp measurable_fst).prodMk (measurable_snd.comp measurable_snd)))

private theorem IwasawaThree.exists_map_regroup3_eq_smul
    (K : Subgroup (AdelicGL 3 (𝓞 ℚ) ℚ))
    (hK : ∀ k : AdelicGL 3 (𝓞 ℚ) ℚ, k ∈ K ↔ archComponent3 (𝓞 ℚ) ℚ k ∈ orth3 ∧
      ∀ p : HeightOneSpectrum (𝓞 ℚ), componentAt3 (𝓞 ℚ) ℚ p k ∈ localMaximalCompact3 (𝓞 ℚ) ℚ p)
    [MeasurableSpace (InfiniteAdeleRing ℚ)] [BorelSpace (InfiniteAdeleRing ℚ)]
    [MeasurableSpace (FiniteAdeleRing (𝓞 ℚ) ℚ)] [BorelSpace (FiniteAdeleRing (𝓞 ℚ) ℚ)]
    [MeasurableSpace (InfiniteAdeleRing ℚ)ˣ] [BorelSpace (InfiniteAdeleRing ℚ)ˣ]
    [MeasurableSpace (FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ] [BorelSpace (FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ]
    [MeasurableSpace (GL (Fin 3) (InfiniteAdeleRing ℚ))] [BorelSpace (GL (Fin 3) (InfiniteAdeleRing ℚ))]
    [MeasurableSpace (GL (Fin 3) (FiniteAdeleRing (𝓞 ℚ) ℚ))] [BorelSpace (GL (Fin 3) (FiniteAdeleRing (𝓞 ℚ) ℚ))]
    (lamA : Measure (InfiniteAdeleRing ℚ)) [lamA.IsAddHaarMeasure]
    (lamF : Measure (FiniteAdeleRing (𝓞 ℚ) ℚ)) [lamF.IsAddHaarMeasure]
    (tauA : Measure (InfiniteAdeleRing ℚ)ˣ) [tauA.IsHaarMeasure]
    (tauF : Measure (FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) [tauF.IsHaarMeasure]
    (nu : Measure IwasawaThree.orthSubgroupInf) [nu.IsHaarMeasure]
    (kap : Measure IwasawaThree.intGL3f) [kap.IsHaarMeasure] :
    letI : MeasurableSpace (AdelicGL 3 (𝓞 ℚ) ℚ) := NumberField.AdelicHaar.glBorel (Fin 3) (𝓞 ℚ) ℚ
    letI : MeasurableSpace (AdeleRing (𝓞 ℚ) ℚ)ˣ := NumberField.Idele.ideleBorel ℚ
    letI : MeasurableSpace (AdeleRing (𝓞 ℚ) ℚ) := NumberField.AdelicHaar.adeleBorel (𝓞 ℚ) ℚ
    ∀ (κ : Measure K) [κ.IsHaarMeasure], ∃ c : ENNReal, c ≠ 0 ∧ c ≠ ⊤ ∧
      Measure.map (IwasawaThree.regroup3 K hK)
        ((((lamA.prod (lamA.prod lamA)).prod ((Measure.pi fun _ : Fin 3 => tauA).withDensity IwasawaThree.densA)).prod
            nu).prod
          (((lamF.prod (lamF.prod lamF)).prod ((Measure.pi fun _ : Fin 3 => tauF).withDensity IwasawaThree.densF)).prod
            kap)) =
        c • ((((NumberField.AdelicHaar.adelicAddHaar (𝓞 ℚ) ℚ).prod
              ((NumberField.AdelicHaar.adelicAddHaar (𝓞 ℚ) ℚ).prod
                (NumberField.AdelicHaar.adelicAddHaar (𝓞 ℚ) ℚ))).prod
            ((Measure.pi fun _ : Fin 3 => NumberField.Idele.idelicHaar ℚ).withDensity IwasawaThree.dens)).prod κ) := by
  intro κ _
  letI : MeasurableSpace (AdelicGL 3 (𝓞 ℚ) ℚ) := NumberField.AdelicHaar.glBorel (Fin 3) (𝓞 ℚ) ℚ
  letI : MeasurableSpace (AdeleRing (𝓞 ℚ) ℚ)ˣ := NumberField.Idele.ideleBorel ℚ
  letI : MeasurableSpace (AdeleRing (𝓞 ℚ) ℚ) := NumberField.AdelicHaar.adeleBorel (𝓞 ℚ) ℚ
  haveI : BorelSpace (AdelicGL 3 (𝓞 ℚ) ℚ) := NumberField.AdelicHaar.borelSpace_glBorel (Fin 3) (𝓞 ℚ) ℚ
  haveI : BorelSpace (AdeleRing (𝓞 ℚ) ℚ)ˣ := NumberField.Idele.borelSpace_ideleBorel ℚ
  haveI : BorelSpace (AdeleRing (𝓞 ℚ) ℚ) := NumberField.AdelicHaar.borelSpace_adeleBorel (𝓞 ℚ) ℚ
  haveI : BorelSpace K := inferInstanceAs (BorelSpace (K : Set (AdelicGL 3 (𝓞 ℚ) ℚ)))
  haveI : BorelSpace IwasawaThree.orthSubgroupInf :=
    inferInstanceAs (BorelSpace (IwasawaThree.orthSubgroupInf : Set (GL (Fin 3) (InfiniteAdeleRing ℚ))))
  haveI : BorelSpace IwasawaThree.intGL3f :=
    inferInstanceAs (BorelSpace (IwasawaThree.intGL3f : Set (GL (Fin 3) (FiniteAdeleRing (𝓞 ℚ) ℚ))))
  haveI : CompactSpace IwasawaThree.intGL3f := IwasawaThree.compactSpace_intGL3f
  haveI := NumberField.AdelicHaar.isAddHaarMeasure_adelicAddHaar (𝓞 ℚ) ℚ
  haveI := NumberField.Idele.isHaarMeasure_idelicHaar ℚ
  haveI := NumberField.AdelicHaar.isHaarMeasure_adelicGLHaar (Fin 3) (𝓞 ℚ) ℚ
  haveI : CompactSpace IwasawaThree.orthSubgroupInf := IwasawaThree.Arch.compactSpace_orthSubgroupInf
  haveI : SigmaCompactSpace (InfiniteAdeleRing ℚ) := sigmaCompactSpace_of_locallyCompact_secondCountable
  haveI : SigmaCompactSpace (InfiniteAdeleRing ℚ)ˣ := sigmaCompactSpace_of_locallyCompact_secondCountable
  haveI : SigmaCompactSpace (FiniteAdeleRing (𝓞 ℚ) ℚ) := sigmaCompactSpace_of_locallyCompact_secondCountable
  haveI : SigmaCompactSpace (FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ := sigmaCompactSpace_of_locallyCompact_secondCountable
  haveI : SigmaFinite lamA := Measure.IsAddHaarMeasure.sigmaFinite lamA
  haveI : SigmaFinite lamF := Measure.IsAddHaarMeasure.sigmaFinite lamF
  haveI : SigmaFinite tauA := Measure.IsHaarMeasure.sigmaFinite tauA
  haveI : SigmaFinite tauF := Measure.IsHaarMeasure.sigmaFinite tauF
  haveI : IsFiniteMeasure nu := ⟨(isCompact_univ (X := IwasawaThree.orthSubgroupInf)).measure_lt_top⟩
  haveI : IsFiniteMeasure kap := ⟨(isCompact_univ (X := IwasawaThree.intGL3f)).measure_lt_top⟩
  haveI : SFinite (lamA.prod (lamA.prod lamA)) := inferInstance
  haveI : SFinite (lamF.prod (lamF.prod lamF)) := inferInstance
  haveI : SigmaFinite (Measure.pi fun _ : Fin 3 => tauA) := inferInstance
  haveI : SigmaFinite (Measure.pi fun _ : Fin 3 => tauF) := inferInstance
  haveI : SFinite ((Measure.pi fun _ : Fin 3 => tauA).withDensity IwasawaThree.densA) := inferInstance
  haveI : SFinite ((Measure.pi fun _ : Fin 3 => tauF).withDensity IwasawaThree.densF) := inferInstance
  haveI : SFinite ((lamA.prod (lamA.prod lamA)).prod
      ((Measure.pi fun _ : Fin 3 => tauA).withDensity IwasawaThree.densA)) := inferInstance
  haveI : SFinite ((lamF.prod (lamF.prod lamF)).prod
      ((Measure.pi fun _ : Fin 3 => tauF).withDensity IwasawaThree.densF)) := inferInstance
  haveI : SFinite (nu.prod kap) := inferInstance
  haveI : SFinite ((lamA.prod (lamA.prod lamA)).prod (lamF.prod (lamF.prod lamF))) := inferInstance
  haveI : SFinite (((Measure.pi fun _ : Fin 3 => tauA).withDensity IwasawaThree.densA).prod
      ((Measure.pi fun _ : Fin 3 => tauF).withDensity IwasawaThree.densF)) := inferInstance
  haveI : CompactSpace K := (IwasawaThree.regroupKEquiv K hK).toHomeomorph.compactSpace
  haveI : IsFiniteMeasure κ := ⟨(isCompact_univ (X := K)).measure_lt_top⟩
  obtain ⟨cN, hN₀, hN₁, hN⟩ := IwasawaThree.exists_map_regroupN_eq_smul lamA lamF
  obtain ⟨cT, hT₀, hT₁, hT⟩ := IwasawaThree.exists_map_regroupT_withDensity_eq_smul tauA tauF
  obtain ⟨cK, hK₀, hK₁, hKK⟩ := IwasawaThree.exists_map_regroupK_eq_smul K hK nu kap κ
  refine ⟨cK * cN * cT, mul_ne_zero (mul_ne_zero hK₀ hN₀) hT₀, ENNReal.mul_ne_top (ENNReal.mul_ne_top hK₁ hN₁) hT₁,
    ?_⟩
  have hshuffle :
      Measure.map (fun p : IwasawaThree.ArchData × IwasawaThree.FinData =>
          (((p.1.1.1, p.2.1.1), (p.1.1.2, p.2.1.2)), (p.1.2, p.2.2)))
        ((((lamA.prod (lamA.prod lamA)).prod ((Measure.pi fun _ : Fin 3 => tauA).withDensity IwasawaThree.densA)).prod
            nu).prod
          (((lamF.prod (lamF.prod lamF)).prod ((Measure.pi fun _ : Fin 3 => tauF).withDensity IwasawaThree.densF)).prod
            kap)) =
        (((lamA.prod (lamA.prod lamA)).prod (lamF.prod (lamF.prod lamF))).prod
            (((Measure.pi fun _ : Fin 3 => tauA).withDensity IwasawaThree.densA).prod
              ((Measure.pi fun _ : Fin 3 => tauF).withDensity IwasawaThree.densF))).prod
          (nu.prod kap) := by
    have h₁ := IwasawaThree.map_prodProdProdComm
      ((lamA.prod (lamA.prod lamA)).prod ((Measure.pi fun _ : Fin 3 => tauA).withDensity IwasawaThree.densA)) nu
      ((lamF.prod (lamF.prod lamF)).prod ((Measure.pi fun _ : Fin 3 => tauF).withDensity IwasawaThree.densF)) kap
    have h₂ := IwasawaThree.map_prodProdProdComm (lamA.prod (lamA.prod lamA))
      ((Measure.pi fun _ : Fin 3 => tauA).withDensity IwasawaThree.densA) (lamF.prod (lamF.prod lamF))
      ((Measure.pi fun _ : Fin 3 => tauF).withDensity IwasawaThree.densF)
    have hs₁ : Measurable fun p : IwasawaThree.ArchData × IwasawaThree.FinData => ((p.1.1, p.2.1), (p.1.2, p.2.2)) :=
      ((measurable_fst.comp measurable_fst).prodMk (measurable_fst.comp measurable_snd)).prodMk
        ((measurable_snd.comp measurable_fst).prodMk (measurable_snd.comp measurable_snd))
    have hs₂ : Measurable fun r :
        ((InfiniteAdeleRing ℚ × InfiniteAdeleRing ℚ × InfiniteAdeleRing ℚ) × (Fin 3 → (InfiniteAdeleRing ℚ)ˣ)) ×
          ((FiniteAdeleRing (𝓞 ℚ) ℚ × FiniteAdeleRing (𝓞 ℚ) ℚ × FiniteAdeleRing (𝓞 ℚ) ℚ) ×
            (Fin 3 → (FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ)) => ((r.1.1, r.2.1), (r.1.2, r.2.2)) :=
      ((measurable_fst.comp measurable_fst).prodMk (measurable_fst.comp measurable_snd)).prodMk
        ((measurable_snd.comp measurable_fst).prodMk (measurable_snd.comp measurable_snd))
    rw [← Measure.map_id (μ := nu.prod kap), ← h₂, Measure.map_prod_map _ _ hs₂ measurable_id, ← h₁,
      Measure.map_map (hs₂.prodMap measurable_id) hs₁]
    rfl
  have hdecomp : IwasawaThree.regroup3 K hK =
      (Prod.map (Prod.map IwasawaThree.regroupN IwasawaThree.regroupT) (IwasawaThree.regroupK K hK)) ∘
        fun p : IwasawaThree.ArchData × IwasawaThree.FinData =>
          (((p.1.1.1, p.2.1.1), (p.1.1.2, p.2.1.2)), (p.1.2, p.2.2)) :=
    rfl
  have hmeas : Measurable fun p : IwasawaThree.ArchData × IwasawaThree.FinData =>
      (((p.1.1.1, p.2.1.1), (p.1.1.2, p.2.1.2)), (p.1.2, p.2.2)) :=
    (((measurable_fst.comp (measurable_fst.comp measurable_fst)).prodMk
        (measurable_fst.comp (measurable_fst.comp measurable_snd))).prodMk
      ((measurable_snd.comp (measurable_fst.comp measurable_fst)).prodMk
        (measurable_snd.comp (measurable_fst.comp measurable_snd)))).prodMk
      ((measurable_snd.comp measurable_fst).prodMk (measurable_snd.comp measurable_snd))
  rw [hdecomp, ← Measure.map_map ((IwasawaThree.measurable_regroupN.prodMap IwasawaThree.measurable_regroupT).prodMap
    (IwasawaThree.measurable_regroupK K hK)) hmeas, hshuffle,
    ← Measure.map_prod_map _ _ (IwasawaThree.measurable_regroupN.prodMap IwasawaThree.measurable_regroupT)
      (IwasawaThree.measurable_regroupK K hK),
    ← Measure.map_prod_map _ _ IwasawaThree.measurable_regroupN IwasawaThree.measurable_regroupT, hN, hT, hKK,
    Measure.prod_smul_left, Measure.prod_smul_right, Measure.prod_smul_left, Measure.prod_smul_right,
    Measure.prod_smul_left, smul_smul, smul_smul]

private theorem IwasawaThree.exists_lintegral_adelicGLHaar_eq_mul_of_measures
    (K : Subgroup (AdelicGL 3 (𝓞 ℚ) ℚ))
    (hK : ∀ k : AdelicGL 3 (𝓞 ℚ) ℚ, k ∈ K ↔ archComponent3 (𝓞 ℚ) ℚ k ∈ orth3 ∧
      ∀ p : HeightOneSpectrum (𝓞 ℚ), componentAt3 (𝓞 ℚ) ℚ p k ∈ localMaximalCompact3 (𝓞 ℚ) ℚ p)
    [MeasurableSpace (InfiniteAdeleRing ℚ)] [BorelSpace (InfiniteAdeleRing ℚ)]
    [MeasurableSpace (FiniteAdeleRing (𝓞 ℚ) ℚ)] [BorelSpace (FiniteAdeleRing (𝓞 ℚ) ℚ)]
    [MeasurableSpace (InfiniteAdeleRing ℚ)ˣ] [BorelSpace (InfiniteAdeleRing ℚ)ˣ]
    [MeasurableSpace (FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ] [BorelSpace (FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ]
    [MeasurableSpace (GL (Fin 3) (InfiniteAdeleRing ℚ))] [BorelSpace (GL (Fin 3) (InfiniteAdeleRing ℚ))]
    [MeasurableSpace (GL (Fin 3) (FiniteAdeleRing (𝓞 ℚ) ℚ))] [BorelSpace (GL (Fin 3) (FiniteAdeleRing (𝓞 ℚ) ℚ))]
    (μa : Measure (GL (Fin 3) (InfiniteAdeleRing ℚ))) [μa.IsHaarMeasure] [μa.Regular]
    (μf : Measure (GL (Fin 3) (FiniteAdeleRing (𝓞 ℚ) ℚ))) [μf.IsHaarMeasure] [μf.Regular]
    (nu : Measure IwasawaThree.orthSubgroupInf) [nu.IsHaarMeasure]
    (kap : Measure IwasawaThree.intGL3f) [kap.IsHaarMeasure]
    (lamA : Measure (InfiniteAdeleRing ℚ)) [lamA.IsAddHaarMeasure]
    (lamF : Measure (FiniteAdeleRing (𝓞 ℚ) ℚ)) [lamF.IsAddHaarMeasure]
    (tauA : Measure (InfiniteAdeleRing ℚ)ˣ) [tauA.IsHaarMeasure]
    (tauF : Measure (FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) [tauF.IsHaarMeasure] :
    letI : MeasurableSpace (AdelicGL 3 (𝓞 ℚ) ℚ) := NumberField.AdelicHaar.glBorel (Fin 3) (𝓞 ℚ) ℚ
    letI : MeasurableSpace (AdeleRing (𝓞 ℚ) ℚ)ˣ := NumberField.Idele.ideleBorel ℚ
    ∀ (κ : Measure K) [κ.IsHaarMeasure],
      ∃ c : ENNReal, c ≠ 0 ∧ c ≠ ⊤ ∧ ∀ φ : AdelicGL 3 (𝓞 ℚ) ℚ → ENNReal, Measurable φ →
        ∫⁻ g, φ g ∂NumberField.AdelicHaar.adelicGLHaar (Fin 3) (𝓞 ℚ) ℚ =
          c * ∫⁻ n : WhittakerBlock.unipotentSubgroup3, ∫⁻ t : Fin 3 → (AdeleRing (𝓞 ℚ) ℚ)ˣ, ∫⁻ k : K,
            φ ((n : AdelicGL 3 (𝓞 ℚ) ℚ) *
                Units.map (Matrix.diagonalRingHom (Fin 3) (AdeleRing (𝓞 ℚ) ℚ)).toMonoidHom
                  (MulEquiv.piUnits.symm t) * k) *
              ENNReal.ofReal ((NumberField.TateGlobal.ideleNorm ℚ (t 0))⁻¹ ^ 2 *
                NumberField.TateGlobal.ideleNorm ℚ (t 2) ^ 2)
            ∂κ ∂(Measure.pi fun _ : Fin 3 => NumberField.Idele.idelicHaar ℚ) ∂WhittakerBlock.unipotentHaar3 := by
  intro κ _
  letI : MeasurableSpace (AdelicGL 3 (𝓞 ℚ) ℚ) := NumberField.AdelicHaar.glBorel (Fin 3) (𝓞 ℚ) ℚ
  letI : MeasurableSpace (AdeleRing (𝓞 ℚ) ℚ)ˣ := NumberField.Idele.ideleBorel ℚ
  letI : MeasurableSpace (AdeleRing (𝓞 ℚ) ℚ) := NumberField.AdelicHaar.adeleBorel (𝓞 ℚ) ℚ
  haveI : BorelSpace (AdelicGL 3 (𝓞 ℚ) ℚ) := NumberField.AdelicHaar.borelSpace_glBorel (Fin 3) (𝓞 ℚ) ℚ
  haveI : BorelSpace (AdeleRing (𝓞 ℚ) ℚ)ˣ := NumberField.Idele.borelSpace_ideleBorel ℚ
  haveI : BorelSpace (AdeleRing (𝓞 ℚ) ℚ) := NumberField.AdelicHaar.borelSpace_adeleBorel (𝓞 ℚ) ℚ
  haveI : BorelSpace K := inferInstanceAs (BorelSpace (K : Set (AdelicGL 3 (𝓞 ℚ) ℚ)))
  haveI : BorelSpace IwasawaThree.orthSubgroupInf :=
    inferInstanceAs (BorelSpace (IwasawaThree.orthSubgroupInf : Set (GL (Fin 3) (InfiniteAdeleRing ℚ))))
  haveI : BorelSpace IwasawaThree.intGL3f :=
    inferInstanceAs (BorelSpace (IwasawaThree.intGL3f : Set (GL (Fin 3) (FiniteAdeleRing (𝓞 ℚ) ℚ))))
  haveI : CompactSpace IwasawaThree.intGL3f := IwasawaThree.compactSpace_intGL3f
  haveI := NumberField.AdelicHaar.isAddHaarMeasure_adelicAddHaar (𝓞 ℚ) ℚ
  haveI := NumberField.Idele.isHaarMeasure_idelicHaar ℚ
  haveI := NumberField.AdelicHaar.isHaarMeasure_adelicGLHaar (Fin 3) (𝓞 ℚ) ℚ
  haveI : CompactSpace IwasawaThree.orthSubgroupInf := IwasawaThree.Arch.compactSpace_orthSubgroupInf
  haveI : SigmaCompactSpace (InfiniteAdeleRing ℚ) := sigmaCompactSpace_of_locallyCompact_secondCountable
  haveI : SigmaCompactSpace (InfiniteAdeleRing ℚ)ˣ := sigmaCompactSpace_of_locallyCompact_secondCountable
  haveI : SigmaCompactSpace (FiniteAdeleRing (𝓞 ℚ) ℚ) := sigmaCompactSpace_of_locallyCompact_secondCountable
  haveI : SigmaCompactSpace (FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ := sigmaCompactSpace_of_locallyCompact_secondCountable
  haveI : SigmaFinite lamA := Measure.IsAddHaarMeasure.sigmaFinite lamA
  haveI : SigmaFinite lamF := Measure.IsAddHaarMeasure.sigmaFinite lamF
  haveI : SigmaFinite tauA := Measure.IsHaarMeasure.sigmaFinite tauA
  haveI : SigmaFinite tauF := Measure.IsHaarMeasure.sigmaFinite tauF
  haveI : IsFiniteMeasure nu := ⟨(isCompact_univ (X := IwasawaThree.orthSubgroupInf)).measure_lt_top⟩
  haveI : IsFiniteMeasure kap := ⟨(isCompact_univ (X := IwasawaThree.intGL3f)).measure_lt_top⟩
  haveI : SFinite (lamA.prod (lamA.prod lamA)) := inferInstance
  haveI : SFinite (lamF.prod (lamF.prod lamF)) := inferInstance
  haveI : SigmaFinite (Measure.pi fun _ : Fin 3 => tauA) := inferInstance
  haveI : SigmaFinite (Measure.pi fun _ : Fin 3 => tauF) := inferInstance
  haveI : SFinite ((Measure.pi fun _ : Fin 3 => tauA).withDensity IwasawaThree.densA) := inferInstance
  haveI : SFinite ((Measure.pi fun _ : Fin 3 => tauF).withDensity IwasawaThree.densF) := inferInstance
  haveI : SFinite ((lamA.prod (lamA.prod lamA)).prod
      ((Measure.pi fun _ : Fin 3 => tauA).withDensity IwasawaThree.densA)) := inferInstance
  haveI : SFinite ((lamF.prod (lamF.prod lamF)).prod
      ((Measure.pi fun _ : Fin 3 => tauF).withDensity IwasawaThree.densF)) := inferInstance
  haveI : SFinite (nu.prod kap) := inferInstance
  haveI : SFinite ((lamA.prod (lamA.prod lamA)).prod (lamF.prod (lamF.prod lamF))) := inferInstance
  haveI : SFinite (((Measure.pi fun _ : Fin 3 => tauA).withDensity IwasawaThree.densA).prod
      ((Measure.pi fun _ : Fin 3 => tauF).withDensity IwasawaThree.densF)) := inferInstance
  haveI : CompactSpace K := (IwasawaThree.regroupKEquiv K hK).toHomeomorph.compactSpace
  haveI : IsFiniteMeasure κ := ⟨(isCompact_univ (X := K)).measure_lt_top⟩
  obtain ⟨c₁, hc₁, hsplit⟩ := NumberField.AdelicHaar.exists_map_adelicGLHaar_eq_smul_prod (Fin 3) ℚ μa μf
  obtain ⟨ca, ca₀, ca₁, hA⟩ := IwasawaThree.exists_nuA_eq_smul μa nu lamA tauA
  obtain ⟨cf, cf₀, cf₁, hF⟩ := IwasawaThree.exists_nuF_eq_smul μf kap lamF tauF
  obtain ⟨c₃, c₃₀, c₃₁, h₃⟩ := IwasawaThree.exists_map_regroup3_eq_smul K hK lamA lamF tauA tauF nu kap κ
  refine ⟨(c₁ : ENNReal) * (ca * cf)⁻¹ * c₃, ?_, ?_, fun φ hφ => ?_⟩
  · exact mul_ne_zero (mul_ne_zero (ENNReal.coe_ne_zero.2 hc₁.ne')
      (ENNReal.inv_ne_zero.2 (ENNReal.mul_ne_top ca₁ cf₁))) c₃₀
  · exact ENNReal.mul_ne_top (ENNReal.mul_ne_top ENNReal.coe_ne_top (ENNReal.inv_ne_top.2 (mul_ne_zero ca₀ cf₀))) c₃₁
  have hsymm : Measurable (IwasawaThree.glSplit.symm :
      GL (Fin 3) (InfiniteAdeleRing ℚ) × GL (Fin 3) (FiniteAdeleRing (𝓞 ℚ) ℚ) → AdelicGL 3 (𝓞 ℚ) ℚ) :=
    IwasawaThree.continuous_glSplit_symm.measurable
  have hpair : Measurable fun x : AdelicGL 3 (𝓞 ℚ) ℚ =>
      (Matrix.GeneralLinearGroup.map (AdelicLevel.adeleArch (𝓞 ℚ) ℚ) x,
        Matrix.GeneralLinearGroup.map (AdelicLevel.adeleFin (𝓞 ℚ) ℚ) x) :=
    IwasawaThree.continuous_glMap_adeleArch.measurable.prodMk IwasawaThree.continuous_glMap_adeleFin.measurable
  have hψ : Measurable fun p : GL (Fin 3) (InfiniteAdeleRing ℚ) × GL (Fin 3) (FiniteAdeleRing (𝓞 ℚ) ℚ) =>
      φ (IwasawaThree.glSplit.symm p) :=
    hφ.comp hsymm
  have hΦ : Measurable fun q => φ (IwasawaThree.iwMap K q) := hφ.comp (IwasawaThree.measurable_iwMap K)
  have h₁ : ∫⁻ g, φ g ∂NumberField.AdelicHaar.adelicGLHaar (Fin 3) (𝓞 ℚ) ℚ =
      ∫⁻ p, φ (IwasawaThree.glSplit.symm p)
        ∂(Measure.map
          (fun x : AdelicGL 3 (𝓞 ℚ) ℚ =>
            (Matrix.GeneralLinearGroup.map (AdelicLevel.adeleArch (𝓞 ℚ) ℚ) x,
              Matrix.GeneralLinearGroup.map (AdelicLevel.adeleFin (𝓞 ℚ) ℚ) x))
          (NumberField.AdelicHaar.adelicGLHaar (Fin 3) (𝓞 ℚ) ℚ)) := by
    rw [lintegral_map hψ hpair]
    refine lintegral_congr fun x => ?_
    rw [← IwasawaThree.glSplit_apply, MulEquiv.symm_apply_apply]
  have hprod : (IwasawaThree.nuA lamA tauA nu).prod (IwasawaThree.nuF lamF tauF kap) = (ca * cf) • μa.prod μf := by
    rw [hA, hF, Measure.prod_smul_left, Measure.prod_smul_right, smul_smul]
  have hmap : (IwasawaThree.nuA lamA tauA nu).prod (IwasawaThree.nuF lamF tauF kap) =
      Measure.map (Prod.map IwasawaThree.iwMapA IwasawaThree.iwMapF)
        (((((lamA.prod (lamA.prod lamA)).prod
              ((Measure.pi fun _ : Fin 3 => tauA).withDensity IwasawaThree.densA)).prod nu).prod
          (((lamF.prod (lamF.prod lamF)).prod
              ((Measure.pi fun _ : Fin 3 => tauF).withDensity IwasawaThree.densF)).prod kap))) := by
    rw [IwasawaThree.nuA, IwasawaThree.nuF,
      Measure.map_prod_map _ _ IwasawaThree.Arch.measurable_iwMapA IwasawaThree.measurable_iwMapF]
  have h₂ : ∫⁻ p, φ (IwasawaThree.glSplit.symm p) ∂(μa.prod μf) =
      (ca * cf)⁻¹ * ∫⁻ q, φ (IwasawaThree.iwMap K q)
        ∂(Measure.map (IwasawaThree.regroup3 K hK)
          (((((lamA.prod (lamA.prod lamA)).prod
                ((Measure.pi fun _ : Fin 3 => tauA).withDensity IwasawaThree.densA)).prod nu).prod
            (((lamF.prod (lamF.prod lamF)).prod
                ((Measure.pi fun _ : Fin 3 => tauF).withDensity IwasawaThree.densF)).prod kap)))) := by
    have hs : μa.prod μf = (ca * cf)⁻¹ • (IwasawaThree.nuA lamA tauA nu).prod (IwasawaThree.nuF lamF tauF kap) := by
      rw [hprod, smul_smul, ENNReal.inv_mul_cancel (mul_ne_zero ca₀ cf₀) (ENNReal.mul_ne_top ca₁ cf₁), one_smul]
    rw [hs, lintegral_smul_measure, smul_eq_mul, hmap,
      lintegral_map hψ (IwasawaThree.Arch.measurable_iwMapA.prodMap IwasawaThree.measurable_iwMapF),
      lintegral_map hΦ (IwasawaThree.measurable_regroup3 K hK)]
    congr 1
    refine lintegral_congr fun q => ?_
    exact congrArg φ (IwasawaThree.glSplit_symm_iwMap K hK q.1 q.2)
  rw [h₁, hsplit, lintegral_smul_measure, ENNReal.smul_def, smul_eq_mul, h₂, h₃, lintegral_smul_measure, smul_eq_mul,
    IwasawaThree.lintegral_iwMap_eq K κ φ hφ]
  ring

private theorem exists_lintegral_adelicGLHaar_eq_mul_lintegral_iwasawa3
    (K : Subgroup (AdelicGL 3 (𝓞 ℚ) ℚ))
    (hK : ∀ k : AdelicGL 3 (𝓞 ℚ) ℚ, k ∈ K ↔ archComponent3 (𝓞 ℚ) ℚ k ∈ orth3 ∧
      ∀ p : HeightOneSpectrum (𝓞 ℚ), componentAt3 (𝓞 ℚ) ℚ p k ∈ localMaximalCompact3 (𝓞 ℚ) ℚ p) :
    letI : MeasurableSpace (AdelicGL 3 (𝓞 ℚ) ℚ) := NumberField.AdelicHaar.glBorel (Fin 3) (𝓞 ℚ) ℚ
    letI : MeasurableSpace (AdeleRing (𝓞 ℚ) ℚ)ˣ := NumberField.Idele.ideleBorel ℚ
    ∀ (κ : Measure K) [κ.IsHaarMeasure],
      ∃ c : ℝ≥0∞, c ≠ 0 ∧ c ≠ ⊤ ∧ ∀ φ : AdelicGL 3 (𝓞 ℚ) ℚ → ℝ≥0∞, Measurable φ →
        ∫⁻ g, φ g ∂NumberField.AdelicHaar.adelicGLHaar (Fin 3) (𝓞 ℚ) ℚ =
          c * ∫⁻ n : WhittakerBlock.unipotentSubgroup3, ∫⁻ t : Fin 3 → (AdeleRing (𝓞 ℚ) ℚ)ˣ, ∫⁻ k : K,
            φ ((n : AdelicGL 3 (𝓞 ℚ) ℚ) *
                Units.map (Matrix.diagonalRingHom (Fin 3) (AdeleRing (𝓞 ℚ) ℚ)).toMonoidHom
                  (MulEquiv.piUnits.symm t) * k) *
              ENNReal.ofReal ((NumberField.TateGlobal.ideleNorm ℚ (t 0))⁻¹ ^ 2 *
                NumberField.TateGlobal.ideleNorm ℚ (t 2) ^ 2)
            ∂κ ∂(Measure.pi fun _ : Fin 3 => NumberField.Idele.idelicHaar ℚ) ∂WhittakerBlock.unipotentHaar3 := by
  intro κ _
  letI : MeasurableSpace (AdelicGL 3 (𝓞 ℚ) ℚ) := NumberField.AdelicHaar.glBorel (Fin 3) (𝓞 ℚ) ℚ
  letI : MeasurableSpace (AdeleRing (𝓞 ℚ) ℚ)ˣ := NumberField.Idele.ideleBorel ℚ
  letI : MeasurableSpace (GL (Fin 3) (InfiniteAdeleRing ℚ)) := borel _
  haveI : BorelSpace (GL (Fin 3) (InfiniteAdeleRing ℚ)) := ⟨rfl⟩
  letI : MeasurableSpace (GL (Fin 3) (FiniteAdeleRing (𝓞 ℚ) ℚ)) := borel _
  haveI : BorelSpace (GL (Fin 3) (FiniteAdeleRing (𝓞 ℚ) ℚ)) := ⟨rfl⟩
  letI : MeasurableSpace (InfiniteAdeleRing ℚ) := borel _
  haveI : BorelSpace (InfiniteAdeleRing ℚ) := ⟨rfl⟩
  letI : MeasurableSpace (FiniteAdeleRing (𝓞 ℚ) ℚ) := borel _
  haveI : BorelSpace (FiniteAdeleRing (𝓞 ℚ) ℚ) := ⟨rfl⟩
  letI : MeasurableSpace (InfiniteAdeleRing ℚ)ˣ := borel _
  haveI : BorelSpace (InfiniteAdeleRing ℚ)ˣ := ⟨rfl⟩
  letI : MeasurableSpace (FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ := borel _
  haveI : BorelSpace (FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ := ⟨rfl⟩
  haveI : BorelSpace IwasawaThree.orthSubgroupInf :=
    inferInstanceAs (BorelSpace (IwasawaThree.orthSubgroupInf : Set (GL (Fin 3) (InfiniteAdeleRing ℚ))))
  haveI : BorelSpace IwasawaThree.intGL3f :=
    inferInstanceAs (BorelSpace (IwasawaThree.intGL3f : Set (GL (Fin 3) (FiniteAdeleRing (𝓞 ℚ) ℚ))))
  haveI : CompactSpace IwasawaThree.intGL3f := IwasawaThree.compactSpace_intGL3f
  exact IwasawaThree.exists_lintegral_adelicGLHaar_eq_mul_of_measures K hK
    (Measure.haarMeasure (Classical.arbitrary _)) (Measure.haarMeasure (Classical.arbitrary _))
    (Measure.haarMeasure (Classical.arbitrary _)) (Measure.haarMeasure (Classical.arbitrary _))
    (Measure.addHaarMeasure (Classical.arbitrary _)) (Measure.addHaarMeasure (Classical.arbitrary _))
    (Measure.haarMeasure (Classical.arbitrary _)) (Measure.haarMeasure (Classical.arbitrary _)) κ

end

section ShellReduction

private def zerothShellSet : Set (AdelicGL 3 (𝓞 ℚ) ℚ) :=
  (Quotient.mk'' :
      AdelicGL 3 (𝓞 ℚ) ℚ → MulAction.orbitRel.Quotient WhittakerBlock.unipotentSubgroup3 (AdelicGL 3 (𝓞 ℚ) ℚ)) ⁻¹'
    WhittakerBlock.zerothShell ∅

private noncomputable def shellLift (F : AdelicGL 3 (𝓞 ℚ) ℚ → ℝ≥0∞) (g : AdelicGL 3 (𝓞 ℚ) ℚ) : ℝ≥0∞ :=
  letI : MeasurableSpace (AdelicGL 3 (𝓞 ℚ) ℚ) := NumberField.AdelicHaar.glBorel (Fin 3) (𝓞 ℚ) ℚ
  zerothShellSet.indicator F g * HaarQuotient.density WhittakerBlock.unipotentSubgroup3 WhittakerBlock.unipotentHaar3 g

variable (K : Subgroup (AdelicGL 3 (𝓞 ℚ) ℚ))

private noncomputable abbrev primeHom (p : HeightOneSpectrum (𝓞 ℚ)) : AdeleRing (𝓞 ℚ) ℚ →+* p.adicCompletion ℚ :=
  (AdelicLevel.finAdeleEval (𝓞 ℚ) ℚ p).comp (AdelicLevel.adeleFin (𝓞 ℚ) ℚ)

private theorem _root_.LanglandsTunnell.CubicInduction.WhittakerBlock.upperUnipotent3_mul' {B : Type*} [CommRing B] (x y z x' y' z' : B) :
    upperUnipotent3 x y z * upperUnipotent3 x' y' z' = upperUnipotent3 (x + x') (y + y') (z + z' + x * y') := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [upperUnipotent3, Units.val_mul, Matrix.mul_apply, Fin.sum_univ_three]
  all_goals ring

p2m_export "LanglandsTunnell.CubicInduction.WhittakerBlock" "upperUnipotent3_mul'"

private theorem _root_.LanglandsTunnell.CubicInduction.WhittakerBlock.upperUnipotent3_inv' {B : Type*} [CommRing B] (x y z : B) :
    (upperUnipotent3 x y z)⁻¹ = upperUnipotent3 (-x) (-y) (x * y - z) := by
  rw [inv_eq_iff_mul_eq_one, upperUnipotent3_mul', show x + -x = 0 by ring, show y + -y = 0 by ring,
    show z + (x * y - z) + x * -y = 0 by ring, upperUnipotent3_zero]

p2m_export "LanglandsTunnell.CubicInduction.WhittakerBlock" "upperUnipotent3_inv'"

private theorem componentAt3_upperUnipotent3 (p : HeightOneSpectrum (𝓞 ℚ)) (x y z : AdeleRing (𝓞 ℚ) ℚ) :
    componentAt3 (𝓞 ℚ) ℚ p (upperUnipotent3 x y z) =
      upperUnipotent3 (primeHom p x) (primeHom p y) (primeHom p z) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [componentAtN, Matrix.GeneralLinearGroup.map_apply, upperUnipotent3]

private theorem coe_componentAt3_diag (p : HeightOneSpectrum (𝓞 ℚ)) (t : Fin 3 → (AdeleRing (𝓞 ℚ) ℚ)ˣ) :
    (componentAt3 (𝓞 ℚ) ℚ p (Units.map (Matrix.diagonalRingHom (Fin 3) (AdeleRing (𝓞 ℚ) ℚ)).toMonoidHom
          (MulEquiv.piUnits.symm t)) :
        Matrix (Fin 3) (Fin 3) (p.adicCompletion ℚ)) =
      Matrix.diagonal fun i => primeHom p (t i) := by
  ext i j
  simp only [componentAtN, Matrix.GeneralLinearGroup.map_apply]
  change primeHom p ((Matrix.diagonal fun i => ((t i : (AdeleRing (𝓞 ℚ) ℚ)ˣ) : AdeleRing (𝓞 ℚ) ℚ)) i j) = _
  rw [Matrix.diagonal_apply, Matrix.diagonal_apply]
  split_ifs <;> simp

private theorem diag_inv (t : Fin 3 → (AdeleRing (𝓞 ℚ) ℚ)ˣ) :
    (Units.map (Matrix.diagonalRingHom (Fin 3) (AdeleRing (𝓞 ℚ) ℚ)).toMonoidHom
          (MulEquiv.piUnits.symm t))⁻¹ =
      Units.map (Matrix.diagonalRingHom (Fin 3) (AdeleRing (𝓞 ℚ) ℚ)).toMonoidHom (MulEquiv.piUnits.symm t⁻¹) := by
  simp only [map_inv]

private theorem componentAt3_diag_mem_localMaximalCompact3 (p : HeightOneSpectrum (𝓞 ℚ))
    {t : Fin 3 → (AdeleRing (𝓞 ℚ) ℚ)ˣ}
    (ht : t ∈ Set.pi Set.univ fun _ : Fin 3 =>
      (NumberField.AdeleRing.unitIdelesOutside (𝓞 ℚ) ℚ (↑(∅ : Finset (HeightOneSpectrum (𝓞 ℚ)))) :
        Set (AdeleRing (𝓞 ℚ) ℚ)ˣ)) :
    componentAt3 (𝓞 ℚ) ℚ p (Units.map (Matrix.diagonalRingHom (Fin 3) (AdeleRing (𝓞 ℚ) ℚ)).toMonoidHom
          (MulEquiv.piUnits.symm t)) ∈ localMaximalCompact3 (𝓞 ℚ) ℚ p := by
  have hu : ∀ i, Valued.v (primeHom p (t i)) ≤ 1 ∧ Valued.v (primeHom p ((t i)⁻¹ : (AdeleRing (𝓞 ℚ) ℚ)ˣ)) ≤ 1 := by
    intro i
    have h := ht i (Set.mem_univ i)
    rw [SetLike.mem_coe, NumberField.AdeleRing.mem_unitIdelesOutside_iff,
      FiniteAdeleRing.mem_unitIdelesOutside_iff] at h
    obtain ⟨h1, h2⟩ := h p (by simp)
    rw [HeightOneSpectrum.mem_adicCompletionIntegers] at h1 h2
    exact ⟨h1, h2⟩
  rw [mem_localMaximalCompact3_iff]
  refine ⟨fun i j => ?_, fun i j => ?_⟩
  · rw [coe_componentAt3_diag, Matrix.diagonal_apply]
    split_ifs
    · exact (hu i).1
    · simp
  · rw [← map_inv, diag_inv, coe_componentAt3_diag, Matrix.diagonal_apply]
    split_ifs
    · simpa using (hu i).2
    · simp

private theorem exists_out_eq_unipotent_mul (g : AdelicGL 3 (𝓞 ℚ) ℚ) :
    ∃ x y z : AdeleRing (𝓞 ℚ) ℚ,
      (Quotient.mk'' g : MulAction.orbitRel.Quotient WhittakerBlock.unipotentSubgroup3 (AdelicGL 3 (𝓞 ℚ) ℚ)).out =
        upperUnipotent3 x y z * g := by
  have h : (Quotient.mk'' g : MulAction.orbitRel.Quotient WhittakerBlock.unipotentSubgroup3 (AdelicGL 3 (𝓞 ℚ) ℚ)).out ∈
      MulAction.orbit WhittakerBlock.unipotentSubgroup3 g :=
    MulAction.orbitRel_apply.1 (Quotient.mk_out g)
  obtain ⟨n, hn⟩ := MulAction.mem_orbit_iff.1 h
  obtain ⟨x, y, z, hxyz⟩ := (WhittakerBlock.mem_unipotentSubgroup3_iff n).1 n.2
  exact ⟨x, y, z, by rw [← hn, Subgroup.smul_def, smul_eq_mul, hxyz]⟩

private theorem primeHom_coe_inv (p : HeightOneSpectrum (𝓞 ℚ)) (x : (AdeleRing (𝓞 ℚ) ℚ)ˣ) :
    primeHom p ((x⁻¹ : (AdeleRing (𝓞 ℚ) ℚ)ˣ) : AdeleRing (𝓞 ℚ) ℚ) = (primeHom p (x : AdeleRing (𝓞 ℚ) ℚ))⁻¹ :=
  eq_inv_of_mul_eq_one_left (by rw [← map_mul, Units.inv_mul, map_one])

private theorem diag_mul_mem_zerothShellSet_iff
    (hK : ∀ k : AdelicGL 3 (𝓞 ℚ) ℚ, k ∈ K ↔ archComponent3 (𝓞 ℚ) ℚ k ∈ orth3 ∧
      ∀ p : HeightOneSpectrum (𝓞 ℚ), componentAt3 (𝓞 ℚ) ℚ p k ∈ localMaximalCompact3 (𝓞 ℚ) ℚ p)
    (t : Fin 3 → (AdeleRing (𝓞 ℚ) ℚ)ˣ) (k : AdelicGL 3 (𝓞 ℚ) ℚ) (hk : k ∈ K) :
    Units.map (Matrix.diagonalRingHom (Fin 3) (AdeleRing (𝓞 ℚ) ℚ)).toMonoidHom
                (MulEquiv.piUnits.symm t) * k ∈
        zerothShellSet ↔
      t ∈ Set.pi Set.univ fun _ : Fin 3 =>
          (NumberField.AdeleRing.unitIdelesOutside (𝓞 ℚ) ℚ (↑(∅ : Finset (HeightOneSpectrum (𝓞 ℚ)))) :
            Set (AdeleRing (𝓞 ℚ) ℚ)ˣ) := by
  obtain ⟨x, y, z, hout⟩ :=
    exists_out_eq_unipotent_mul (Units.map (Matrix.diagonalRingHom (Fin 3) (AdeleRing (𝓞 ℚ) ℚ)).toMonoidHom
          (MulEquiv.piUnits.symm t) * k)
  have hkp : ∀ p : HeightOneSpectrum (𝓞 ℚ), componentAt3 (𝓞 ℚ) ℚ p k ∈ localMaximalCompact3 (𝓞 ℚ) ℚ p :=
    fun p => ((hK k).1 hk).2 p
  simp only [zerothShellSet, Set.mem_preimage, WhittakerBlock.zerothShell, Set.mem_setOf_eq, hout, map_mul,
    componentAt3_upperUnipotent3]
  constructor
  · intro h
    rw [Set.mem_univ_pi]
    intro i
    rw [SetLike.mem_coe, NumberField.AdeleRing.mem_unitIdelesOutside_iff, FiniteAdeleRing.mem_unitIdelesOutside_iff]
    intro p _
    obtain ⟨x', y', z', κ, hκ, hp⟩ := h p (by simp)

    have hM : upperUnipotent3 (-x' + primeHom p x) (-y' + primeHom p y)
          (x' * y' - z' + primeHom p z + -x' * primeHom p y) *
        componentAt3 (𝓞 ℚ) ℚ p (Units.map (Matrix.diagonalRingHom (Fin 3) (AdeleRing (𝓞 ℚ) ℚ)).toMonoidHom
          (MulEquiv.piUnits.symm t)) ∈ localMaximalCompact3 (𝓞 ℚ) ℚ p := by
      have hM' : upperUnipotent3 (-x' + primeHom p x) (-y' + primeHom p y)
            (x' * y' - z' + primeHom p z + -x' * primeHom p y) *
          componentAt3 (𝓞 ℚ) ℚ p (Units.map (Matrix.diagonalRingHom (Fin 3) (AdeleRing (𝓞 ℚ) ℚ)).toMonoidHom
          (MulEquiv.piUnits.symm t)) =
            κ * (componentAt3 (𝓞 ℚ) ℚ p k)⁻¹ := by
        rw [← upperUnipotent3_mul', ← upperUnipotent3_inv', mul_assoc, eq_mul_inv_iff_mul_eq, mul_assoc, mul_assoc,
          hp, inv_mul_cancel_left]
      rw [hM']
      exact mul_mem hκ (inv_mem (hkp p))
    rw [mem_localMaximalCompact3_iff] at hM
    obtain ⟨h1, h2⟩ := hM
    refine ⟨?_, ?_⟩
    · have := h1 i i
      rw [Units.val_mul, coe_componentAt3_diag, Matrix.mul_diagonal] at this
      rw [HeightOneSpectrum.mem_adicCompletionIntegers]
      fin_cases i <;> first | exact this | simpa using this |
        simpa [NumberField.AdelicLevel.finAdeleEval_apply, NumberField.AdelicLevel.adeleFin_apply] using this
    · have := h2 i i
      rw [_root_.mul_inv_rev, upperUnipotent3_inv', ← map_inv, diag_inv, Units.val_mul, coe_componentAt3_diag,
        Matrix.diagonal_mul] at this
      rw [HeightOneSpectrum.mem_adicCompletionIntegers]
      change Valued.v (primeHom p (((t i)⁻¹ : (AdeleRing (𝓞 ℚ) ℚ)ˣ) : AdeleRing (𝓞 ℚ) ℚ)) ≤ 1
      rw [primeHom_coe_inv, map_inv₀]
      fin_cases i <;> first | exact this | simpa using this |
        simpa [NumberField.AdelicLevel.finAdeleEval_apply, NumberField.AdelicLevel.adeleFin_apply] using this
  · intro ht p _
    exact ⟨primeHom p x, primeHom p y, primeHom p z, _,
      mul_mem (componentAt3_diag_mem_localMaximalCompact3 p ht) (hkp p), rfl⟩

private theorem secondCountableTopology_adeleRing : SecondCountableTopology (AdeleRing (𝓞 ℚ) ℚ) :=
  NumberField.AdeleRing.secondCountableTopology ℚ

private theorem secondCountableTopology_adelicGL : SecondCountableTopology (AdelicGL 3 (𝓞 ℚ) ℚ) := by
  haveI := secondCountableTopology_adeleRing
  haveI : SecondCountableTopology (Matrix (Fin 3) (Fin 3) (AdeleRing (𝓞 ℚ) ℚ)) :=
    inferInstanceAs (SecondCountableTopology (Fin 3 → Fin 3 → AdeleRing (𝓞 ℚ) ℚ))
  haveI : SecondCountableTopology (Matrix (Fin 3) (Fin 3) (AdeleRing (𝓞 ℚ) ℚ))ᵐᵒᵖ :=
    (MulOpposite.opHomeomorph (M := Matrix (Fin 3) (Fin 3) (AdeleRing (𝓞 ℚ) ℚ))).symm.secondCountableTopology
  exact Units.isInducing_embedProduct.secondCountableTopology

private theorem sigmaFinite_unipotentHaar3 :
    letI : MeasurableSpace (AdelicGL 3 (𝓞 ℚ) ℚ) := NumberField.AdelicHaar.glBorel (Fin 3) (𝓞 ℚ) ℚ
    SigmaFinite WhittakerBlock.unipotentHaar3 := by
  letI : MeasurableSpace (AdelicGL 3 (𝓞 ℚ) ℚ) := NumberField.AdelicHaar.glBorel (Fin 3) (𝓞 ℚ) ℚ
  haveI := secondCountableTopology_adelicGL
  haveI : LocallyCompactSpace WhittakerBlock.unipotentSubgroup3 :=
    WhittakerBlock.isClosed_unipotentSubgroup3.locallyCompactSpace
  haveI : SecondCountableTopology WhittakerBlock.unipotentSubgroup3 :=
    inferInstanceAs (SecondCountableTopology (WhittakerBlock.unipotentSubgroup3 : Set (AdelicGL 3 (𝓞 ℚ) ℚ)))
  haveI : WhittakerBlock.unipotentHaar3.IsHaarMeasure := WhittakerBlock.isHaarMeasure_unipotentHaar3
  exact sigmaFinite_of_locallyFinite

private theorem measurable_density {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] (H : Subgroup G) (μH : Measure H)
    [SFinite μH] : Measurable (HaarQuotient.density H μH) := by
  have hw : Measurable (HaarQuotient.weight H μH) := by
    unfold HaarQuotient.weight
    split_ifs with h
    · simp_rw [ENNReal.tsum_eq_iSup_sum]
      exact .iSup fun s => s.measurable_fun_sum fun n _ =>
        measurable_const.mul (measurable_const.indicator isOpen_interior.measurableSet)
    · exact measurable_const
  have hmul : Measurable fun p : G × H => HaarQuotient.weight H μH ((p.2 : G) * p.1) :=
    hw.comp ((continuous_subtype_val.comp continuous_snd).mul continuous_fst).measurable
  unfold HaarQuotient.density
  exact hw.div hmul.lintegral_prod_right'

private noncomputable def shellDensity : AdelicGL 3 (𝓞 ℚ) ℚ → ℝ≥0∞ :=
  letI : MeasurableSpace (AdelicGL 3 (𝓞 ℚ) ℚ) := NumberField.AdelicHaar.glBorel (Fin 3) (𝓞 ℚ) ℚ
  HaarQuotient.density WhittakerBlock.unipotentSubgroup3 WhittakerBlock.unipotentHaar3

private theorem measurable_shellDensity :
    letI : MeasurableSpace (AdelicGL 3 (𝓞 ℚ) ℚ) := NumberField.AdelicHaar.glBorel (Fin 3) (𝓞 ℚ) ℚ
    Measurable shellDensity := by
  letI : MeasurableSpace (AdelicGL 3 (𝓞 ℚ) ℚ) := NumberField.AdelicHaar.glBorel (Fin 3) (𝓞 ℚ) ℚ
  haveI : BorelSpace (AdelicGL 3 (𝓞 ℚ) ℚ) := NumberField.AdelicHaar.borelSpace_glBorel (Fin 3) (𝓞 ℚ) ℚ
  haveI := secondCountableTopology_adelicGL
  haveI : SigmaFinite WhittakerBlock.unipotentHaar3 := sigmaFinite_unipotentHaar3
  exact measurable_density _ _

private theorem lintegral_shellDensity_mul (g : AdelicGL 3 (𝓞 ℚ) ℚ) :
    ∫⁻ n : WhittakerBlock.unipotentSubgroup3, shellDensity ((n : AdelicGL 3 (𝓞 ℚ) ℚ) * g)
      ∂WhittakerBlock.unipotentHaar3 = 1 := by
  letI : MeasurableSpace (AdelicGL 3 (𝓞 ℚ) ℚ) := NumberField.AdelicHaar.glBorel (Fin 3) (𝓞 ℚ) ℚ
  haveI : BorelSpace (AdelicGL 3 (𝓞 ℚ) ℚ) := NumberField.AdelicHaar.borelSpace_glBorel (Fin 3) (𝓞 ℚ) ℚ
  haveI := secondCountableTopology_adelicGL
  haveI : WhittakerBlock.unipotentHaar3.IsHaarMeasure := WhittakerBlock.isHaarMeasure_unipotentHaar3
  haveI : WhittakerBlock.unipotentHaar3.IsMulRightInvariant := WhittakerBlock.isMulRightInvariant_unipotentHaar3
  exact HaarQuotient.lintegral_density_mul_eq_one _ WhittakerBlock.isClosed_unipotentSubgroup3 _ g

private theorem mk''_unipotent_mul (n : WhittakerBlock.unipotentSubgroup3) (g : AdelicGL 3 (𝓞 ℚ) ℚ) :
    (Quotient.mk'' ((n : AdelicGL 3 (𝓞 ℚ) ℚ) * g) :
        MulAction.orbitRel.Quotient WhittakerBlock.unipotentSubgroup3 (AdelicGL 3 (𝓞 ℚ) ℚ)) = Quotient.mk'' g :=
  Quotient.sound (MulAction.mem_orbit g n)

private theorem unipotent_mul_mem_zerothShellSet_iff (n : WhittakerBlock.unipotentSubgroup3) (g : AdelicGL 3 (𝓞 ℚ) ℚ) :
    (n : AdelicGL 3 (𝓞 ℚ) ℚ) * g ∈ zerothShellSet ↔ g ∈ zerothShellSet := by
  unfold zerothShellSet
  rw [Set.mem_preimage, Set.mem_preimage, mk''_unipotent_mul]

private theorem indicator_unipotent_mul (F : AdelicGL 3 (𝓞 ℚ) ℚ → ℝ≥0∞)
    (hFN : ∀ n ∈ WhittakerBlock.unipotentSubgroup3, ∀ g : AdelicGL 3 (𝓞 ℚ) ℚ, F (n * g) = F g)
    (n : WhittakerBlock.unipotentSubgroup3) (g : AdelicGL 3 (𝓞 ℚ) ℚ) :
    zerothShellSet.indicator F ((n : AdelicGL 3 (𝓞 ℚ) ℚ) * g) = zerothShellSet.indicator F g := by
  by_cases hg : g ∈ zerothShellSet
  · rw [Set.indicator_of_mem ((unipotent_mul_mem_zerothShellSet_iff n g).2 hg), Set.indicator_of_mem hg, hFN n n.2 g]
  · rw [Set.indicator_of_notMem (fun h => hg ((unipotent_mul_mem_zerothShellSet_iff n g).1 h)),
      Set.indicator_of_notMem hg]

private theorem shellLift_unipotent_mul (F : AdelicGL 3 (𝓞 ℚ) ℚ → ℝ≥0∞)
    (hFN : ∀ n ∈ WhittakerBlock.unipotentSubgroup3, ∀ g : AdelicGL 3 (𝓞 ℚ) ℚ, F (n * g) = F g)
    (n : WhittakerBlock.unipotentSubgroup3) (g : AdelicGL 3 (𝓞 ℚ) ℚ) :
    shellLift F ((n : AdelicGL 3 (𝓞 ℚ) ℚ) * g) =
      zerothShellSet.indicator F g * shellDensity ((n : AdelicGL 3 (𝓞 ℚ) ℚ) * g) := by
  show zerothShellSet.indicator F ((n : AdelicGL 3 (𝓞 ℚ) ℚ) * g) * shellDensity ((n : AdelicGL 3 (𝓞 ℚ) ℚ) * g) = _
  rw [indicator_unipotent_mul F hFN n g]

private theorem isClopen_localMaximalCompact3 (p : HeightOneSpectrum (𝓞 ℚ)) :
    IsClopen (localMaximalCompact3 (𝓞 ℚ) ℚ p : Set (GL (Fin 3) (p.adicCompletion ℚ))) := by
  have hint : IsClopen (p.adicCompletionIntegers ℚ : Set (p.adicCompletion ℚ)) :=
    Valued.isClopen_valuationSubring (p.adicCompletion ℚ)
  have hval : Continuous fun k : GL (Fin 3) (p.adicCompletion ℚ) =>
      (k : Matrix (Fin 3) (Fin 3) (p.adicCompletion ℚ)) := Units.continuous_val
  have hinv : Continuous fun k : GL (Fin 3) (p.adicCompletion ℚ) =>
      ((k⁻¹ : GL (Fin 3) (p.adicCompletion ℚ)) : Matrix (Fin 3) (Fin 3) (p.adicCompletion ℚ)) :=
    Units.continuous_coe_inv
  have hrepr : (localMaximalCompact3 (𝓞 ℚ) ℚ p : Set (GL (Fin 3) (p.adicCompletion ℚ))) =
      (⋂ i : Fin 3, ⋂ j : Fin 3, (fun k : GL (Fin 3) (p.adicCompletion ℚ) =>
          (k : Matrix (Fin 3) (Fin 3) (p.adicCompletion ℚ)) i j) ⁻¹'
            (p.adicCompletionIntegers ℚ : Set (p.adicCompletion ℚ))) ∩
        (⋂ i : Fin 3, ⋂ j : Fin 3, (fun k : GL (Fin 3) (p.adicCompletion ℚ) =>
          ((k⁻¹ : GL (Fin 3) (p.adicCompletion ℚ)) : Matrix (Fin 3) (Fin 3) (p.adicCompletion ℚ)) i j) ⁻¹'
            (p.adicCompletionIntegers ℚ : Set (p.adicCompletion ℚ))) := by
    ext k
    simp [mem_localMaximalCompact3_iff, HeightOneSpectrum.mem_adicCompletionIntegers]
  rw [hrepr]
  exact (isClopen_iInter_of_finite fun i => isClopen_iInter_of_finite fun j =>
      hint.preimage (hval.matrix_elem i j)).inter
    (isClopen_iInter_of_finite fun i => isClopen_iInter_of_finite fun j => hint.preimage (hinv.matrix_elem i j))

private theorem continuous_componentAt3 (p : HeightOneSpectrum (𝓞 ℚ)) : Continuous (componentAt3 (𝓞 ℚ) ℚ p) := by
  have hφ : Continuous ((AdelicLevel.finAdeleEval (R := 𝓞 ℚ) (K := ℚ) p).comp (AdelicLevel.adeleFin (𝓞 ℚ) ℚ)) :=
    (AdelicLevel.continuous_finAdeleEval (R := 𝓞 ℚ) (K := ℚ) p).comp (AdelicLevel.continuous_adeleFin (𝓞 ℚ) ℚ)
  have hmat : Continuous ⇑((RingHom.mapMatrix (m := Fin 3) ((AdelicLevel.finAdeleEval (R := 𝓞 ℚ) (K := ℚ) p).comp
      (AdelicLevel.adeleFin (𝓞 ℚ) ℚ))).toMonoidHom) := by
    show Continuous fun A : Matrix (Fin 3) (Fin 3) (AdeleRing (𝓞 ℚ) ℚ) =>
      A.map ((AdelicLevel.finAdeleEval (R := 𝓞 ℚ) (K := ℚ) p).comp (AdelicLevel.adeleFin (𝓞 ℚ) ℚ))
    exact continuous_id.matrix_map hφ
  exact Units.continuous_map hmat

private theorem continuous_archComponent3 : Continuous (archComponent3 (𝓞 ℚ) ℚ) := by
  have hmat : Continuous ⇑((RingHom.mapMatrix (m := Fin 3) (AdelicLevel.adeleArch (𝓞 ℚ) ℚ)).toMonoidHom) := by
    show Continuous fun A : Matrix (Fin 3) (Fin 3) (AdeleRing (𝓞 ℚ) ℚ) => A.map (AdelicLevel.adeleArch (𝓞 ℚ) ℚ)
    exact continuous_id.matrix_map (AdelicLevel.continuous_adeleArch (𝓞 ℚ) ℚ)
  exact Units.continuous_map hmat

private def orth3Subgroup : Subgroup (GL (Fin 3) (InfiniteAdeleRing ℚ)) where
  carrier := orth3
  one_mem' := by simp [orth3]
  mul_mem' := by
    intro a b ha hb
    simp only [orth3, Set.mem_setOf_eq, Units.val_mul, Matrix.transpose_mul] at ha hb ⊢
    rw [Matrix.mul_assoc, ← Matrix.mul_assoc (a : Matrix (Fin 3) (Fin 3) (InfiniteAdeleRing ℚ)).transpose, ha,
      Matrix.one_mul, hb]
  inv_mem' := by
    intro a ha
    simp only [orth3, Set.mem_setOf_eq] at ha ⊢
    have hinv : ((a⁻¹ : GL (Fin 3) (InfiniteAdeleRing ℚ)) : Matrix (Fin 3) (Fin 3) (InfiniteAdeleRing ℚ)) =
        (a : Matrix (Fin 3) (Fin 3) (InfiniteAdeleRing ℚ)).transpose := Units.inv_eq_of_mul_eq_one_left ha
    rw [hinv, Matrix.transpose_transpose, ← hinv, Units.mul_inv]

private theorem isClosed_orth3 : IsClosed (orth3 : Set (GL (Fin 3) (InfiniteAdeleRing ℚ))) := by
  unfold orth3
  exact isClosed_eq (Units.continuous_val.matrix_transpose.matrix_mul Units.continuous_val) continuous_const

private theorem isClosed_of_mem_iff (K : Subgroup (AdelicGL 3 (𝓞 ℚ) ℚ))
    (hK : ∀ k : AdelicGL 3 (𝓞 ℚ) ℚ, k ∈ K ↔ archComponent3 (𝓞 ℚ) ℚ k ∈ orth3 ∧
      ∀ p : HeightOneSpectrum (𝓞 ℚ), componentAt3 (𝓞 ℚ) ℚ p k ∈ localMaximalCompact3 (𝓞 ℚ) ℚ p) :
    IsClosed (K : Set (AdelicGL 3 (𝓞 ℚ) ℚ)) := by
  have h1 : IsClosed ((archComponent3 (𝓞 ℚ) ℚ) ⁻¹' (orth3 : Set (GL (Fin 3) (InfiniteAdeleRing ℚ)))) :=
    isClosed_orth3.preimage continuous_archComponent3
  have h2 : ∀ q : HeightOneSpectrum (𝓞 ℚ), IsClosed ((componentAt3 (𝓞 ℚ) ℚ q) ⁻¹'
      (localMaximalCompact3 (𝓞 ℚ) ℚ q : Set (GL (Fin 3) (q.adicCompletion ℚ)))) :=
    fun q => (isClopen_localMaximalCompact3 q).isClosed.preimage (continuous_componentAt3 q)
  have hrepr : (K : Set (AdelicGL 3 (𝓞 ℚ) ℚ)) =
      (archComponent3 (𝓞 ℚ) ℚ) ⁻¹' (orth3 : Set (GL (Fin 3) (InfiniteAdeleRing ℚ))) ∩
        ⋂ q : HeightOneSpectrum (𝓞 ℚ), (componentAt3 (𝓞 ℚ) ℚ q) ⁻¹'
          (localMaximalCompact3 (𝓞 ℚ) ℚ q : Set (GL (Fin 3) (q.adicCompletion ℚ))) := by
    ext k
    simp only [SetLike.mem_coe, hK, Set.mem_inter_iff, Set.mem_preimage, Set.mem_iInter]
  rw [hrepr]
  exact h1.inter (isClosed_iInter h2)

private theorem sigmaFinite_haar_of_mem_iff (K : Subgroup (AdelicGL 3 (𝓞 ℚ) ℚ))
    (hK : ∀ k : AdelicGL 3 (𝓞 ℚ) ℚ, k ∈ K ↔ archComponent3 (𝓞 ℚ) ℚ k ∈ orth3 ∧
      ∀ p : HeightOneSpectrum (𝓞 ℚ), componentAt3 (𝓞 ℚ) ℚ p k ∈ localMaximalCompact3 (𝓞 ℚ) ℚ p) :
    letI : MeasurableSpace (AdelicGL 3 (𝓞 ℚ) ℚ) := NumberField.AdelicHaar.glBorel (Fin 3) (𝓞 ℚ) ℚ
    ∀ (κ : Measure K) [κ.IsHaarMeasure], SigmaFinite κ := by
  intro κ _
  letI : MeasurableSpace (AdelicGL 3 (𝓞 ℚ) ℚ) := NumberField.AdelicHaar.glBorel (Fin 3) (𝓞 ℚ) ℚ
  haveI := secondCountableTopology_adelicGL
  haveI : LocallyCompactSpace K := (isClosed_of_mem_iff K hK).locallyCompactSpace
  haveI : SecondCountableTopology K := inferInstanceAs (SecondCountableTopology (K : Set (AdelicGL 3 (𝓞 ℚ) ℚ)))
  exact sigmaFinite_of_locallyFinite

private theorem continuous_diagIdele :
    Continuous fun t : Fin 3 → (AdeleRing (𝓞 ℚ) ℚ)ˣ =>
      (Units.map (Matrix.diagonalRingHom (Fin 3) (AdeleRing (𝓞 ℚ) ℚ)).toMonoidHom (MulEquiv.piUnits.symm t) :
        AdelicGL 3 (𝓞 ℚ) ℚ) := by
  refine Units.continuous_iff.2 ⟨?_, ?_⟩
  · exact Continuous.matrix_diagonal (continuous_pi fun i => Units.continuous_val.comp (continuous_apply i))
  · exact Continuous.matrix_diagonal (continuous_pi fun i =>
      Units.continuous_val.comp (continuous_inv.comp (continuous_apply i)))

private theorem secondCountableTopology_idele : SecondCountableTopology (AdeleRing (𝓞 ℚ) ℚ)ˣ := by
  haveI := secondCountableTopology_adeleRing
  haveI : SecondCountableTopology (AdeleRing (𝓞 ℚ) ℚ)ᵐᵒᵖ :=
    (MulOpposite.opHomeomorph (M := AdeleRing (𝓞 ℚ) ℚ)).symm.secondCountableTopology
  exact Units.isInducing_embedProduct.secondCountableTopology

private theorem _root_.LanglandsTunnell.CubicInduction.WhittakerBlock.sigmaFinite_idelicHaar :
    letI : MeasurableSpace (AdeleRing (𝓞 ℚ) ℚ)ˣ := NumberField.Idele.ideleBorel ℚ
    SigmaFinite (NumberField.Idele.idelicHaar ℚ) := by
  letI : MeasurableSpace (AdeleRing (𝓞 ℚ) ℚ)ˣ := NumberField.Idele.ideleBorel ℚ
  haveI := secondCountableTopology_idele
  haveI : (NumberField.Idele.idelicHaar ℚ).IsHaarMeasure := NumberField.Idele.isHaarMeasure_idelicHaar ℚ
  exact sigmaFinite_of_locallyFinite

p2m_export "LanglandsTunnell.CubicInduction.WhittakerBlock" "sigmaFinite_idelicHaar"

private theorem measurable_normWeight :
    letI : MeasurableSpace (AdeleRing (𝓞 ℚ) ℚ)ˣ := NumberField.Idele.ideleBorel ℚ
    Measurable fun t : Fin 3 → (AdeleRing (𝓞 ℚ) ℚ)ˣ =>
      ENNReal.ofReal ((NumberField.TateGlobal.ideleNorm ℚ (t 0))⁻¹ ^ 2 *
        NumberField.TateGlobal.ideleNorm ℚ (t 2) ^ 2) := by
  letI : MeasurableSpace (AdeleRing (𝓞 ℚ) ℚ)ˣ := NumberField.Idele.ideleBorel ℚ
  haveI : BorelSpace (AdeleRing (𝓞 ℚ) ℚ)ˣ := NumberField.Idele.borelSpace_ideleBorel ℚ
  have hN : ∀ i : Fin 3, Measurable fun t : Fin 3 → (AdeleRing (𝓞 ℚ) ℚ)ˣ => NumberField.TateGlobal.ideleNorm ℚ (t i) :=
    fun i => (NumberField.TateGlobal.continuous_ideleNorm ℚ).measurable.comp (measurable_pi_apply i)
  exact (((hN 0).inv.pow_const 2).mul ((hN 2).pow_const 2)).ennreal_ofReal

private def localShellSet (p : HeightOneSpectrum (𝓞 ℚ)) : Set (GL (Fin 3) (p.adicCompletion ℚ)) :=
  ⋃ (x : p.adicCompletion ℚ) (y : p.adicCompletion ℚ) (z : p.adicCompletion ℚ),
    (fun h : GL (Fin 3) (p.adicCompletion ℚ) => upperUnipotent3 x y z * h) ⁻¹'
      (localMaximalCompact3 (𝓞 ℚ) ℚ p : Set (GL (Fin 3) (p.adicCompletion ℚ)))

private theorem mem_localShellSet_iff (p : HeightOneSpectrum (𝓞 ℚ)) (h : GL (Fin 3) (p.adicCompletion ℚ)) :
    h ∈ localShellSet p ↔
      ∃ x y z : p.adicCompletion ℚ, upperUnipotent3 x y z * h ∈ localMaximalCompact3 (𝓞 ℚ) ℚ p := by
  simp only [localShellSet, Set.mem_iUnion, Set.mem_preimage, SetLike.mem_coe]

private theorem isOpen_localShellSet (p : HeightOneSpectrum (𝓞 ℚ)) : IsOpen (localShellSet p) :=
  isOpen_iUnion fun x => isOpen_iUnion fun y => isOpen_iUnion fun z =>
    (isClopen_localMaximalCompact3 p).isOpen.preimage (continuous_const_mul (upperUnipotent3 x y z))

private theorem exists_eq_unipotent_mul_iff_mem_localShellSet (p : HeightOneSpectrum (𝓞 ℚ))
    (a b c : p.adicCompletion ℚ)
    (h : GL (Fin 3) (p.adicCompletion ℚ)) :
    (∃ (x y z : p.adicCompletion ℚ) (k : GL (Fin 3) (p.adicCompletion ℚ)), k ∈ localMaximalCompact3 (𝓞 ℚ) ℚ p ∧
        upperUnipotent3 a b c * h = upperUnipotent3 x y z * k) ↔ h ∈ localShellSet p := by
  rw [mem_localShellSet_iff]
  constructor
  · rintro ⟨x, y, z, k, hk, hx⟩
    refine ⟨-x + a, -y + b, x * y - z + c + -x * b, ?_⟩
    rw [← upperUnipotent3_mul', mul_assoc, ← upperUnipotent3_inv', hx, inv_mul_cancel_left]
    exact hk
  · rintro ⟨x, y, z, hxk⟩
    refine ⟨a + -x, b + -y, c + (x * y - z) + a * -y, upperUnipotent3 x y z * h, hxk, ?_⟩
    rw [← upperUnipotent3_mul', ← upperUnipotent3_inv', mul_assoc, inv_mul_cancel_left]

private theorem zerothShellSet_eq_iInter :
    zerothShellSet = ⋂ p : HeightOneSpectrum (𝓞 ℚ), componentAt3 (𝓞 ℚ) ℚ p ⁻¹' localShellSet p := by
  ext g
  obtain ⟨a, b, c, hout⟩ := exists_out_eq_unipotent_mul g
  have hcomp : ∀ p : HeightOneSpectrum (𝓞 ℚ),
      componentAt3 (𝓞 ℚ) ℚ p
          (Quotient.mk'' g :
            MulAction.orbitRel.Quotient WhittakerBlock.unipotentSubgroup3 (AdelicGL 3 (𝓞 ℚ) ℚ)).out =
        upperUnipotent3 (primeHom p a) (primeHom p b) (primeHom p c) * componentAt3 (𝓞 ℚ) ℚ p g :=
    fun p => by rw [hout, map_mul, componentAt3_upperUnipotent3]
  simp only [zerothShellSet, Set.mem_preimage, WhittakerBlock.zerothShell, Set.mem_setOf_eq, Set.mem_iInter,
    Finset.notMem_empty, not_false_eq_true, true_implies]
  exact forall_congr' fun p => by rw [hcomp p]; exact exists_eq_unipotent_mul_iff_mem_localShellSet p _ _ _ _

private theorem measurableSet_zerothShellSet :
    letI : MeasurableSpace (AdelicGL 3 (𝓞 ℚ) ℚ) := NumberField.AdelicHaar.glBorel (Fin 3) (𝓞 ℚ) ℚ
    MeasurableSet zerothShellSet := by
  letI : MeasurableSpace (AdelicGL 3 (𝓞 ℚ) ℚ) := NumberField.AdelicHaar.glBorel (Fin 3) (𝓞 ℚ) ℚ
  haveI : BorelSpace (AdelicGL 3 (𝓞 ℚ) ℚ) := NumberField.AdelicHaar.borelSpace_glBorel (Fin 3) (𝓞 ℚ) ℚ
  rw [zerothShellSet_eq_iInter]
  exact MeasurableSet.iInter fun p => ((isOpen_localShellSet p).preimage (continuous_componentAt3 p)).measurableSet

private noncomputable def diagMul (t : Fin 3 → (AdeleRing (𝓞 ℚ) ℚ)ˣ) (k : K) : AdelicGL 3 (𝓞 ℚ) ℚ :=
  Units.map (Matrix.diagonalRingHom (Fin 3) (AdeleRing (𝓞 ℚ) ℚ)).toMonoidHom
      (MulEquiv.piUnits.symm t) * k

private theorem continuous_diagMul : Continuous fun q : (Fin 3 → (AdeleRing (𝓞 ℚ) ℚ)ˣ) × K => diagMul K q.1 q.2 :=
  (continuous_diagIdele.comp continuous_fst).mul (continuous_subtype_val.comp continuous_snd)

private theorem continuous_diagMul_right (t : Fin 3 → (AdeleRing (𝓞 ℚ) ℚ)ˣ) : Continuous fun k : K => diagMul K t k :=
  continuous_const.mul continuous_subtype_val

private noncomputable def shellTorusIntegrand (F : AdelicGL 3 (𝓞 ℚ) ℚ → ℝ≥0∞) (t : Fin 3 → (AdeleRing (𝓞 ℚ) ℚ)ˣ)
    (k : K) : ℝ≥0∞ :=
  zerothShellSet.indicator F (diagMul K t k) *
    ENNReal.ofReal ((NumberField.TateGlobal.ideleNorm ℚ (t 0))⁻¹ ^ 2 * NumberField.TateGlobal.ideleNorm ℚ (t 2) ^ 2)

private theorem measurable_shellTorusIntegrand (F : AdelicGL 3 (𝓞 ℚ) ℚ → ℝ≥0∞) :
    letI : MeasurableSpace (AdelicGL 3 (𝓞 ℚ) ℚ) := NumberField.AdelicHaar.glBorel (Fin 3) (𝓞 ℚ) ℚ
    letI : MeasurableSpace (AdeleRing (𝓞 ℚ) ℚ)ˣ := NumberField.Idele.ideleBorel ℚ
    Measurable F → Measurable fun q : (Fin 3 → (AdeleRing (𝓞 ℚ) ℚ)ˣ) × K => shellTorusIntegrand K F q.1 q.2 := by
  intro hF
  letI : MeasurableSpace (AdelicGL 3 (𝓞 ℚ) ℚ) := NumberField.AdelicHaar.glBorel (Fin 3) (𝓞 ℚ) ℚ
  letI : MeasurableSpace (AdeleRing (𝓞 ℚ) ℚ)ˣ := NumberField.Idele.ideleBorel ℚ
  haveI : BorelSpace (AdelicGL 3 (𝓞 ℚ) ℚ) := NumberField.AdelicHaar.borelSpace_glBorel (Fin 3) (𝓞 ℚ) ℚ
  haveI : BorelSpace (AdeleRing (𝓞 ℚ) ℚ)ˣ := NumberField.Idele.borelSpace_ideleBorel ℚ
  haveI := secondCountableTopology_idele
  unfold shellTorusIntegrand
  exact ((hF.indicator measurableSet_zerothShellSet).comp (continuous_diagMul K).measurable).mul
    (measurable_normWeight.comp measurable_fst)

private theorem measurable_shellTorusIntegrand_right (F : AdelicGL 3 (𝓞 ℚ) ℚ → ℝ≥0∞)
    (t : Fin 3 → (AdeleRing (𝓞 ℚ) ℚ)ˣ) :
    letI : MeasurableSpace (AdelicGL 3 (𝓞 ℚ) ℚ) := NumberField.AdelicHaar.glBorel (Fin 3) (𝓞 ℚ) ℚ
    Measurable F → Measurable (shellTorusIntegrand K F t) := by
  intro hF
  letI : MeasurableSpace (AdelicGL 3 (𝓞 ℚ) ℚ) := NumberField.AdelicHaar.glBorel (Fin 3) (𝓞 ℚ) ℚ
  haveI : BorelSpace (AdelicGL 3 (𝓞 ℚ) ℚ) := NumberField.AdelicHaar.borelSpace_glBorel (Fin 3) (𝓞 ℚ) ℚ
  unfold shellTorusIntegrand
  exact ((hF.indicator measurableSet_zerothShellSet).comp (continuous_diagMul_right K t).measurable).mul_const _

private theorem measurable_shellLift (F : AdelicGL 3 (𝓞 ℚ) ℚ → ℝ≥0∞) :
    letI : MeasurableSpace (AdelicGL 3 (𝓞 ℚ) ℚ) := NumberField.AdelicHaar.glBorel (Fin 3) (𝓞 ℚ) ℚ
    Measurable F → Measurable (shellLift F) := by
  intro hF
  letI : MeasurableSpace (AdelicGL 3 (𝓞 ℚ) ℚ) := NumberField.AdelicHaar.glBorel (Fin 3) (𝓞 ℚ) ℚ
  unfold shellLift
  exact (hF.indicator measurableSet_zerothShellSet).mul measurable_shellDensity

private theorem out_mem_zerothShellSet_iff
    (q : MulAction.orbitRel.Quotient WhittakerBlock.unipotentSubgroup3 (AdelicGL 3 (𝓞 ℚ) ℚ)) :
    q.out ∈ zerothShellSet ↔ q ∈ WhittakerBlock.zerothShell ∅ := by
  show Quotient.mk'' q.out ∈ WhittakerBlock.zerothShell ∅ ↔ q ∈ WhittakerBlock.zerothShell ∅
  rw [Quotient.out_eq']

private theorem measurableSet_zerothShell :
    letI : MeasurableSpace (AdelicGL 3 (𝓞 ℚ) ℚ) := NumberField.AdelicHaar.glBorel (Fin 3) (𝓞 ℚ) ℚ
    MeasurableSet (WhittakerBlock.zerothShell ∅) := by
  letI : MeasurableSpace (AdelicGL 3 (𝓞 ℚ) ℚ) := NumberField.AdelicHaar.glBorel (Fin 3) (𝓞 ℚ) ℚ
  exact measurableSet_quotient.2 measurableSet_zerothShellSet

private theorem setLIntegral_zerothShell_eq_lintegral_shellLift (F : AdelicGL 3 (𝓞 ℚ) ℚ → ℝ≥0∞) :
    letI : MeasurableSpace (AdelicGL 3 (𝓞 ℚ) ℚ) := NumberField.AdelicHaar.glBorel (Fin 3) (𝓞 ℚ) ℚ
    Measurable F → (∀ n ∈ WhittakerBlock.unipotentSubgroup3, ∀ g : AdelicGL 3 (𝓞 ℚ) ℚ, F (n * g) = F g) →
      ∫⁻ q in WhittakerBlock.zerothShell ∅, F q.out ∂WhittakerBlock.quotientMeasure =
        ∫⁻ g, shellLift F g ∂NumberField.AdelicHaar.adelicGLHaar (Fin 3) (𝓞 ℚ) ℚ := by
  intro hF hinv
  letI : MeasurableSpace (AdelicGL 3 (𝓞 ℚ) ℚ) := NumberField.AdelicHaar.glBorel (Fin 3) (𝓞 ℚ) ℚ
  haveI : BorelSpace (AdelicGL 3 (𝓞 ℚ) ℚ) := NumberField.AdelicHaar.borelSpace_glBorel (Fin 3) (𝓞 ℚ) ℚ
  haveI := secondCountableTopology_adelicGL
  haveI : (NumberField.AdelicHaar.adelicGLHaar (Fin 3) (𝓞 ℚ) ℚ).IsHaarMeasure :=
    NumberField.AdelicHaar.isHaarMeasure_adelicGLHaar (Fin 3) (𝓞 ℚ) ℚ
  haveI : SigmaFinite (NumberField.AdelicHaar.adelicGLHaar (Fin 3) (𝓞 ℚ) ℚ) := sigmaFinite_of_locallyFinite
  haveI : WhittakerBlock.unipotentHaar3.IsHaarMeasure := WhittakerBlock.isHaarMeasure_unipotentHaar3
  haveI : WhittakerBlock.unipotentHaar3.IsMulRightInvariant := WhittakerBlock.isMulRightInvariant_unipotentHaar3
  have hmd : Measurable shellDensity := measurable_shellDensity
  have hS : MeasurableSet (WhittakerBlock.zerothShell ∅) := measurableSet_zerothShell
  have hA := HaarQuotient.lintegral_eq_lintegral_lintegral_mul_out
    (NumberField.AdelicHaar.adelicGLHaar (Fin 3) (𝓞 ℚ) ℚ)
    WhittakerBlock.unipotentSubgroup3 WhittakerBlock.isClosed_unipotentSubgroup3 WhittakerBlock.unipotentHaar3
    (shellLift F) (measurable_shellLift F hF)
  rw [hA, ← lintegral_indicator hS]
  unfold WhittakerBlock.quotientMeasure
  refine lintegral_congr fun q => ?_

  have hd : Measurable fun n : WhittakerBlock.unipotentSubgroup3 => shellDensity ((n : AdelicGL 3 (𝓞 ℚ) ℚ) * q.out) :=
    hmd.comp (continuous_subtype_val.mul continuous_const).measurable
  simp_rw [shellLift_unipotent_mul F hinv]
  rw [lintegral_const_mul _ hd, lintegral_shellDensity_mul, mul_one]
  by_cases hmem : q ∈ WhittakerBlock.zerothShell ∅ <;> simp [Set.indicator, hmem, out_mem_zerothShellSet_iff]

private theorem lintegral_lintegral_lintegral_eq_of_lintegral_eq_one {X Y Z : Type*}
    [MeasurableSpace X] [MeasurableSpace Y] [MeasurableSpace Z]
    (μX : Measure X) (μY : Measure Y) (μZ : Measure Z) [SigmaFinite μX] [SigmaFinite μY] [SigmaFinite μZ]
    (L : X → Y → Z → ℝ≥0∞) (φ : Y → Z → ℝ≥0∞) (ρ : X → Y → Z → ℝ≥0∞)
    (hL : ∀ x y z, L x y z = φ y z * ρ x y z) (hφ : Measurable fun p : Y × Z => φ p.1 p.2)
    (hρ : Measurable fun p : (X × Y) × Z => ρ p.1.1 p.1.2 p.2) (hρ1 : ∀ y z, ∫⁻ x, ρ x y z ∂μX = 1) :
    ∫⁻ x, ∫⁻ y, ∫⁻ z, L x y z ∂μZ ∂μY ∂μX = ∫⁻ y, ∫⁻ z, φ y z ∂μZ ∂μY := by
  simp_rw [hL]
  have hj : Measurable fun p : (X × Y) × Z => φ p.1.2 p.2 * ρ p.1.1 p.1.2 p.2 :=
    (hφ.comp ((measurable_snd.comp measurable_fst).prodMk measurable_snd)).mul hρ
  have h1 : AEMeasurable (Function.uncurry fun (x : X) (y : Y) => ∫⁻ z, φ y z * ρ x y z ∂μZ) (μX.prod μY) :=
    (hj.lintegral_prod_right' : Measurable fun q : X × Y => ∫⁻ z, φ q.2 z * ρ q.1 q.2 z ∂μZ).aemeasurable
  rw [lintegral_lintegral_swap h1]
  refine lintegral_congr fun y => ?_
  have h2 : AEMeasurable (Function.uncurry fun (x : X) (z : Z) => φ y z * ρ x y z) (μX.prod μZ) :=
    ((hφ.comp (measurable_prodMk_left.comp measurable_snd)).mul
      (hρ.comp ((measurable_fst.prodMk measurable_const).prodMk measurable_snd)) :
      Measurable fun r : X × Z => φ y r.2 * ρ r.1 y r.2).aemeasurable
  rw [lintegral_lintegral_swap h2]
  refine lintegral_congr fun z => ?_
  have hd : Measurable fun x : X => ρ x y z :=
    hρ.comp ((measurable_id'.prodMk measurable_const).prodMk measurable_const)
  rw [lintegral_const_mul _ hd, hρ1, mul_one]

private theorem lintegral_iwasawa3_shellLift (F : AdelicGL 3 (𝓞 ℚ) ℚ → ℝ≥0∞)
    (hK : ∀ k : AdelicGL 3 (𝓞 ℚ) ℚ, k ∈ K ↔ archComponent3 (𝓞 ℚ) ℚ k ∈ orth3 ∧
      ∀ p : HeightOneSpectrum (𝓞 ℚ), componentAt3 (𝓞 ℚ) ℚ p k ∈ localMaximalCompact3 (𝓞 ℚ) ℚ p) :
    letI : MeasurableSpace (AdelicGL 3 (𝓞 ℚ) ℚ) := NumberField.AdelicHaar.glBorel (Fin 3) (𝓞 ℚ) ℚ
    letI : MeasurableSpace (AdeleRing (𝓞 ℚ) ℚ)ˣ := NumberField.Idele.ideleBorel ℚ
    ∀ (κ : Measure K) [κ.IsHaarMeasure], Measurable F →
      (∀ n ∈ WhittakerBlock.unipotentSubgroup3, ∀ g : AdelicGL 3 (𝓞 ℚ) ℚ, F (n * g) = F g) →
      ∫⁻ n : WhittakerBlock.unipotentSubgroup3, ∫⁻ t : Fin 3 → (AdeleRing (𝓞 ℚ) ℚ)ˣ, ∫⁻ k : K,
          shellLift F ((n : AdelicGL 3 (𝓞 ℚ) ℚ) *
              Units.map (Matrix.diagonalRingHom (Fin 3) (AdeleRing (𝓞 ℚ) ℚ)).toMonoidHom
                (MulEquiv.piUnits.symm t) * k) *
            ENNReal.ofReal ((NumberField.TateGlobal.ideleNorm ℚ (t 0))⁻¹ ^ 2 *
                NumberField.TateGlobal.ideleNorm ℚ (t 2) ^ 2)
          ∂κ ∂(Measure.pi fun _ : Fin 3 => NumberField.Idele.idelicHaar ℚ) ∂WhittakerBlock.unipotentHaar3 =
        ∫⁻ t : Fin 3 → (AdeleRing (𝓞 ℚ) ℚ)ˣ, ∫⁻ k : K,
          zerothShellSet.indicator F
              (Units.map (Matrix.diagonalRingHom (Fin 3) (AdeleRing (𝓞 ℚ) ℚ)).toMonoidHom
                (MulEquiv.piUnits.symm t) * k) *
            ENNReal.ofReal ((NumberField.TateGlobal.ideleNorm ℚ (t 0))⁻¹ ^ 2 *
                NumberField.TateGlobal.ideleNorm ℚ (t 2) ^ 2)
          ∂κ ∂(Measure.pi fun _ : Fin 3 => NumberField.Idele.idelicHaar ℚ) := by
  intro κ _ hF hFN
  letI : MeasurableSpace (AdelicGL 3 (𝓞 ℚ) ℚ) := NumberField.AdelicHaar.glBorel (Fin 3) (𝓞 ℚ) ℚ
  letI : MeasurableSpace (AdeleRing (𝓞 ℚ) ℚ)ˣ := NumberField.Idele.ideleBorel ℚ
  haveI : BorelSpace (AdelicGL 3 (𝓞 ℚ) ℚ) := NumberField.AdelicHaar.borelSpace_glBorel (Fin 3) (𝓞 ℚ) ℚ
  haveI : BorelSpace (AdeleRing (𝓞 ℚ) ℚ)ˣ := NumberField.Idele.borelSpace_ideleBorel ℚ
  haveI := secondCountableTopology_adelicGL
  haveI := secondCountableTopology_idele
  haveI : SigmaFinite WhittakerBlock.unipotentHaar3 := sigmaFinite_unipotentHaar3
  haveI : SigmaFinite κ := sigmaFinite_haar_of_mem_iff K hK κ
  haveI : ∀ _ : Fin 3, SigmaFinite (NumberField.Idele.idelicHaar ℚ) := fun _ => sigmaFinite_idelicHaar

  have hdiag : Continuous fun t : Fin 3 → (AdeleRing (𝓞 ℚ) ℚ)ˣ =>
      (Units.map (Matrix.diagonalRingHom (Fin 3) (AdeleRing (𝓞 ℚ) ℚ)).toMonoidHom
          (MulEquiv.piUnits.symm t) : AdelicGL 3 (𝓞 ℚ) ℚ) := by
    refine Units.continuous_iff.2 ⟨?_, ?_⟩
    · exact Continuous.matrix_diagonal (continuous_pi fun i => Units.continuous_val.comp (continuous_apply i))
    · exact Continuous.matrix_diagonal (continuous_pi fun i =>
        Units.continuous_val.comp (continuous_inv.comp (continuous_apply i)))
  have hN : ∀ i : Fin 3, Measurable fun t : Fin 3 → (AdeleRing (𝓞 ℚ) ℚ)ˣ => NumberField.TateGlobal.ideleNorm ℚ (t i) :=
    fun i => (NumberField.TateGlobal.continuous_ideleNorm ℚ).measurable.comp (measurable_pi_apply i)
  refine lintegral_lintegral_lintegral_eq_of_lintegral_eq_one WhittakerBlock.unipotentHaar3
    (Measure.pi fun _ : Fin 3 => NumberField.Idele.idelicHaar ℚ) κ
    (fun (n : WhittakerBlock.unipotentSubgroup3) (t : Fin 3 → (AdeleRing (𝓞 ℚ) ℚ)ˣ) (k : K) =>
      shellLift F ((n : AdelicGL 3 (𝓞 ℚ) ℚ) *
          Units.map (Matrix.diagonalRingHom (Fin 3) (AdeleRing (𝓞 ℚ) ℚ)).toMonoidHom
          (MulEquiv.piUnits.symm t) * k) *
        ENNReal.ofReal ((NumberField.TateGlobal.ideleNorm ℚ (t 0))⁻¹ ^ 2 *
          NumberField.TateGlobal.ideleNorm ℚ (t 2) ^ 2))
    (fun (t : Fin 3 → (AdeleRing (𝓞 ℚ) ℚ)ˣ) (k : K) =>
      zerothShellSet.indicator F (Units.map (Matrix.diagonalRingHom (Fin 3) (AdeleRing (𝓞 ℚ) ℚ)).toMonoidHom
          (MulEquiv.piUnits.symm t) * k) *
        ENNReal.ofReal ((NumberField.TateGlobal.ideleNorm ℚ (t 0))⁻¹ ^ 2 *
          NumberField.TateGlobal.ideleNorm ℚ (t 2) ^ 2))
    (fun (n : WhittakerBlock.unipotentSubgroup3) (t : Fin 3 → (AdeleRing (𝓞 ℚ) ℚ)ˣ) (k : K) =>
      shellDensity ((n : AdelicGL 3 (𝓞 ℚ) ℚ) *
        (Units.map (Matrix.diagonalRingHom (Fin 3) (AdeleRing (𝓞 ℚ) ℚ)).toMonoidHom
          (MulEquiv.piUnits.symm t) * k)))
    (fun n t k => ?_) ?_ ?_ ?_
  ·
    exact (congrArg (fun g : AdelicGL 3 (𝓞 ℚ) ℚ => shellLift F g * _) (mul_assoc _ _ _)).trans
      ((congrArg (· * _) (shellLift_unipotent_mul F hFN n _)).trans (mul_right_comm _ _ _))
  · exact ((hF.indicator measurableSet_zerothShellSet).comp
        ((hdiag.comp continuous_fst).mul (continuous_subtype_val.comp continuous_snd)).measurable).mul
      ((((hN 0).inv.pow_const 2).mul ((hN 2).pow_const 2)).ennreal_ofReal.comp measurable_fst)
  ·

    haveI : MeasurableMul₂ (AdelicGL 3 (𝓞 ℚ) ℚ) := ContinuousMul.measurableMul₂
    have h₁ : Measurable fun r : (WhittakerBlock.unipotentSubgroup3 × (Fin 3 → (AdeleRing (𝓞 ℚ) ℚ)ˣ)) × K =>
        (r.1.1 : AdelicGL 3 (𝓞 ℚ) ℚ) :=
      measurable_subtype_coe.comp (measurable_fst.comp measurable_fst)
    have h₂ : Measurable fun r : (WhittakerBlock.unipotentSubgroup3 × (Fin 3 → (AdeleRing (𝓞 ℚ) ℚ)ˣ)) × K =>
        (Units.map (Matrix.diagonalRingHom (Fin 3) (AdeleRing (𝓞 ℚ) ℚ)).toMonoidHom (MulEquiv.piUnits.symm r.1.2) :
          AdelicGL 3 (𝓞 ℚ) ℚ) :=
      hdiag.measurable.comp (measurable_snd.comp measurable_fst)
    have h₃ : Measurable fun r : (WhittakerBlock.unipotentSubgroup3 × (Fin 3 → (AdeleRing (𝓞 ℚ) ℚ)ˣ)) × K =>
        (r.2 : AdelicGL 3 (𝓞 ℚ) ℚ) :=
      measurable_subtype_coe.comp measurable_snd
    exact measurable_shellDensity.comp (h₁.mul (h₂.mul h₃))
  · exact fun t k => lintegral_shellDensity_mul _

private theorem fst_mul' (x y : AdeleRing (𝓞 ℚ) ℚ) : (x * y).1 = x.1 * y.1 := rfl

private theorem fst_one' : (1 : AdeleRing (𝓞 ℚ) ℚ).1 = 1 := rfl

private theorem snd_partAt_empty (x : (AdeleRing (𝓞 ℚ) ℚ)ˣ) :
    ((NumberField.Idele.partAt ℚ ∅ x : (AdeleRing (𝓞 ℚ) ℚ)ˣ) : AdeleRing (𝓞 ℚ) ℚ).2 = 1 :=
  IsDedekindDomain.FiniteAdeleRing.ext ℚ fun v => by
    rw [NumberField.Idele.partAt_snd_of_not_mem ℚ ∅ x (Finset.notMem_empty v)]
    rfl

private theorem partAt_empty_mem_unitIdelesOutside (x : (AdeleRing (𝓞 ℚ) ℚ)ˣ) :
    NumberField.Idele.partAt ℚ ∅ x ∈
      NumberField.AdeleRing.unitIdelesOutside (𝓞 ℚ) ℚ (↑(∅ : Finset (HeightOneSpectrum (𝓞 ℚ)))) := by
  rw [NumberField.AdeleRing.mem_unitIdelesOutside_iff]
  have h : Units.map (RingHom.snd (InfiniteAdeleRing ℚ) (FiniteAdeleRing (𝓞 ℚ) ℚ)).toMonoidHom
      (NumberField.Idele.partAt ℚ ∅ x) = 1 :=
    Units.ext (snd_partAt_empty x)
  rw [h]
  exact one_mem _

private theorem one_mem_orth3 : (1 : GL (Fin 3) (InfiniteAdeleRing ℚ)) ∈ orth3 := by
  simp [orth3]

private theorem archComponent3_diag_eq_one {u : Fin 3 → (AdeleRing (𝓞 ℚ) ℚ)ˣ}
    (hu : ∀ i, ((u i : (AdeleRing (𝓞 ℚ) ℚ)ˣ) : AdeleRing (𝓞 ℚ) ℚ).1 = 1) :
    archComponent3 (𝓞 ℚ) ℚ
      (Units.map (Matrix.diagonalRingHom (Fin 3) (AdeleRing (𝓞 ℚ) ℚ)).toMonoidHom (MulEquiv.piUnits.symm u)) = 1 := by
  ext i j
  simp only [archComponentN, Matrix.GeneralLinearGroup.map_apply]
  change AdelicLevel.adeleArch (𝓞 ℚ) ℚ
      ((Matrix.diagonal fun i => ((u i : (AdeleRing (𝓞 ℚ) ℚ)ˣ) : AdeleRing (𝓞 ℚ) ℚ)) i j) =
    (1 : Matrix (Fin 3) (Fin 3) (InfiniteAdeleRing ℚ)) i j
  rw [Matrix.diagonal_apply, Matrix.one_apply]
  split_ifs
  · exact hu i
  · exact map_zero _

private theorem lintegral_diag_mul_eq_lintegral_diag_partAt_mul (F : AdelicGL 3 (𝓞 ℚ) ℚ → ℝ≥0∞)
    (hK : ∀ k : AdelicGL 3 (𝓞 ℚ) ℚ, k ∈ K ↔ archComponent3 (𝓞 ℚ) ℚ k ∈ orth3 ∧
      ∀ p : HeightOneSpectrum (𝓞 ℚ), componentAt3 (𝓞 ℚ) ℚ p k ∈ localMaximalCompact3 (𝓞 ℚ) ℚ p) :
    letI : MeasurableSpace (AdelicGL 3 (𝓞 ℚ) ℚ) := NumberField.AdelicHaar.glBorel (Fin 3) (𝓞 ℚ) ℚ
    ∀ (κ : Measure K) [κ.IsHaarMeasure] (t : Fin 3 → (AdeleRing (𝓞 ℚ) ℚ)ˣ),
      t ∈ (Set.pi Set.univ fun _ : Fin 3 =>
          (NumberField.AdeleRing.unitIdelesOutside (𝓞 ℚ) ℚ (↑(∅ : Finset (HeightOneSpectrum (𝓞 ℚ)))) :
            Set (AdeleRing (𝓞 ℚ) ℚ)ˣ)) →
      ∫⁻ k : K, F (Units.map (Matrix.diagonalRingHom (Fin 3) (AdeleRing (𝓞 ℚ) ℚ)).toMonoidHom
                (MulEquiv.piUnits.symm t) * k) *
            ENNReal.ofReal ((NumberField.TateGlobal.ideleNorm ℚ (t 0))⁻¹ ^ 2 *
                NumberField.TateGlobal.ideleNorm ℚ (t 2) ^ 2) ∂κ =
        ∫⁻ k : K, F (Units.map (Matrix.diagonalRingHom (Fin 3) (AdeleRing (𝓞 ℚ) ℚ)).toMonoidHom
                (MulEquiv.piUnits.symm fun i => NumberField.Idele.partAt ℚ ∅ (t i)) * k) *
            ENNReal.ofReal
              ((NumberField.TateGlobal.ideleNorm ℚ (NumberField.Idele.partAt ℚ ∅ (t 0)))⁻¹ ^ 2 *
                NumberField.TateGlobal.ideleNorm ℚ (NumberField.Idele.partAt ℚ ∅ (t 2)) ^ 2) ∂κ := by
  intro κ _hκ t ht
  letI : MeasurableSpace (AdelicGL 3 (𝓞 ℚ) ℚ) := NumberField.AdelicHaar.glBorel (Fin 3) (𝓞 ℚ) ℚ
  haveI : BorelSpace (AdelicGL 3 (𝓞 ℚ) ℚ) := NumberField.AdelicHaar.borelSpace_glBorel (Fin 3) (𝓞 ℚ) ℚ

  obtain ⟨u, hu⟩ : ∃ u : Fin 3 → (AdeleRing (𝓞 ℚ) ℚ)ˣ,
      u = fun i => (NumberField.Idele.partAt ℚ ∅ (t i))⁻¹ * t i :=
    ⟨_, rfl⟩
  have hu_mem : u ∈ Set.pi Set.univ fun _ : Fin 3 =>
      (NumberField.AdeleRing.unitIdelesOutside (𝓞 ℚ) ℚ (↑(∅ : Finset (HeightOneSpectrum (𝓞 ℚ)))) :
        Set (AdeleRing (𝓞 ℚ) ℚ)ˣ) := by
    rw [Set.mem_univ_pi]
    intro i
    rw [hu, SetLike.mem_coe]
    exact mul_mem (inv_mem (partAt_empty_mem_unitIdelesOutside (t i))) (SetLike.mem_coe.1 (ht i (Set.mem_univ i)))
  have hu_arch : ∀ i, ((u i : (AdeleRing (𝓞 ℚ) ℚ)ˣ) : AdeleRing (𝓞 ℚ) ℚ).1 = 1 := by
    intro i
    rw [hu]
    show ((((NumberField.Idele.partAt ℚ ∅ (t i))⁻¹ * t i : (AdeleRing (𝓞 ℚ) ℚ)ˣ)) : AdeleRing (𝓞 ℚ) ℚ).1 = 1
    rw [Units.val_mul, fst_mul', ← NumberField.Idele.partAt_fst ℚ ∅ (t i), ← fst_mul', ← Units.val_mul,
      inv_mul_cancel, Units.val_one, fst_one']

  have hN : ∀ i, NumberField.TateGlobal.ideleNorm ℚ (t i) =
      NumberField.TateGlobal.ideleNorm ℚ (NumberField.Idele.partAt ℚ ∅ (t i)) := by
    intro i
    have hone : NumberField.TateGlobal.ideleNorm ℚ (u i) = 1 := by
      refine NumberField.TateGlobal.ideleNorm_eq_one_of_fst_eq_one_of_finitePartUnits_mem_unitIdeles ℚ (u i)
        (hu_arch i) ?_
      have h := (NumberField.AdeleRing.mem_unitIdelesOutside_iff _ _).1
        (SetLike.mem_coe.1 (Set.mem_univ_pi.1 hu_mem i))
      rw [Finset.coe_empty, FiniteAdeleRing.unitIdelesOutside_empty] at h
      exact h
    have h := NumberField.TateGlobal.ideleNorm_mul (F := ℚ) (NumberField.Idele.partAt ℚ ∅ (t i)) (u i)
    rw [hone, mul_one, hu] at h
    rw [← h]
    congr 1
    exact (mul_inv_cancel_left _ _).symm

  have hD : Units.map (Matrix.diagonalRingHom (Fin 3) (AdeleRing (𝓞 ℚ) ℚ)).toMonoidHom (MulEquiv.piUnits.symm t) =
      Units.map (Matrix.diagonalRingHom (Fin 3) (AdeleRing (𝓞 ℚ) ℚ)).toMonoidHom
          (MulEquiv.piUnits.symm fun i => NumberField.Idele.partAt ℚ ∅ (t i)) *
        Units.map (Matrix.diagonalRingHom (Fin 3) (AdeleRing (𝓞 ℚ) ℚ)).toMonoidHom (MulEquiv.piUnits.symm u) := by
    rw [← map_mul, ← map_mul]
    congr 2
    funext i
    rw [hu, Pi.mul_apply]
    exact (mul_inv_cancel_left _ _).symm
  have huK : Units.map (Matrix.diagonalRingHom (Fin 3) (AdeleRing (𝓞 ℚ) ℚ)).toMonoidHom (MulEquiv.piUnits.symm u) ∈
      K :=
    (hK _).2 ⟨by rw [archComponent3_diag_eq_one hu_arch]; exact one_mem_orth3,
      fun p => componentAt3_diag_mem_localMaximalCompact3 p hu_mem⟩
  obtain ⟨uK, huKv⟩ : ∃ e : K, (e : AdelicGL 3 (𝓞 ℚ) ℚ) =
      Units.map (Matrix.diagonalRingHom (Fin 3) (AdeleRing (𝓞 ℚ) ℚ)).toMonoidHom (MulEquiv.piUnits.symm u) :=
    ⟨⟨_, huK⟩, rfl⟩
  have hpt : ∀ k : K,
      F (Units.map (Matrix.diagonalRingHom (Fin 3) (AdeleRing (𝓞 ℚ) ℚ)).toMonoidHom (MulEquiv.piUnits.symm t) * k) =
        F (Units.map (Matrix.diagonalRingHom (Fin 3) (AdeleRing (𝓞 ℚ) ℚ)).toMonoidHom
            (MulEquiv.piUnits.symm fun i => NumberField.Idele.partAt ℚ ∅ (t i)) * (uK * k)) := by
    intro k
    rw [hD, huKv, mul_assoc]
  simp only [hN]
  simp_rw [hpt]
  simpa only [Subgroup.coe_mul] using lintegral_mul_left_eq_self (μ := κ)
    (fun k : K => F (Units.map (Matrix.diagonalRingHom (Fin 3) (AdeleRing (𝓞 ℚ) ℚ)).toMonoidHom
          (MulEquiv.piUnits.symm fun i => NumberField.Idele.partAt ℚ ∅ (t i)) * k) *
      ENNReal.ofReal
        ((NumberField.TateGlobal.ideleNorm ℚ (NumberField.Idele.partAt ℚ ∅ (t 0)))⁻¹ ^ 2 *
          NumberField.TateGlobal.ideleNorm ℚ (NumberField.Idele.partAt ℚ ∅ (t 2)) ^ 2)) uK

private theorem measurableSet_pi_unitIdelesOutside :
    letI : MeasurableSpace (AdeleRing (𝓞 ℚ) ℚ)ˣ := NumberField.Idele.ideleBorel ℚ
    MeasurableSet
      (Set.pi Set.univ fun _ : Fin 3 =>
          (NumberField.AdeleRing.unitIdelesOutside (𝓞 ℚ) ℚ (↑(∅ : Finset (HeightOneSpectrum (𝓞 ℚ)))) :
            Set (AdeleRing (𝓞 ℚ) ℚ)ˣ)) := by
  letI : MeasurableSpace (AdeleRing (𝓞 ℚ) ℚ)ˣ := NumberField.Idele.ideleBorel ℚ
  haveI : BorelSpace (AdeleRing (𝓞 ℚ) ℚ)ˣ := NumberField.Idele.borelSpace_ideleBorel ℚ
  exact MeasurableSet.univ_pi fun _ => (NumberField.Idele.isOpen_unitIdelesOutside ℚ _).measurableSet

private theorem continuous_normInfty :
    Continuous fun a : (AdeleRing (𝓞 ℚ) ℚ)ˣ => ‖(a : AdeleRing (𝓞 ℚ) ℚ).1 Rat.infinitePlace‖ :=
  continuous_norm.comp ((continuous_apply Rat.infinitePlace).comp (continuous_fst.comp Units.continuous_val))

private theorem exists_map_normInfty_sPartMeasure :
    letI : MeasurableSpace (AdeleRing (𝓞 ℚ) ℚ)ˣ := NumberField.Idele.ideleBorel ℚ
    ∃ c : ℝ, 0 < c ∧
      Measure.map (fun a : (AdeleRing (𝓞 ℚ) ℚ)ˣ => ‖(a : AdeleRing (𝓞 ℚ) ℚ).1 Rat.infinitePlace‖)
          (NumberField.Idele.sPartMeasure ℚ ∅) =
        (volume.restrict (Set.Ioi (0 : ℝ))).withDensity fun t => ENNReal.ofReal (c * t⁻¹) := by
  letI : MeasurableSpace (AdeleRing (𝓞 ℚ) ℚ)ˣ := NumberField.Idele.ideleBorel ℚ
  haveI : BorelSpace (AdeleRing (𝓞 ℚ) ℚ)ˣ := NumberField.Idele.borelSpace_ideleBorel ℚ
  obtain ⟨C, hC0, hCtop, hrow⟩ :=
    NumberField.Idele.exists_lintegral_prod_norm_sPartMeasure_empty_eq_mul_prod_lintegral ℚ
  refine ⟨C.toReal, ENNReal.toReal_pos hC0 hCtop, ?_⟩
  have hm : Measurable fun a : (AdeleRing (𝓞 ℚ) ℚ)ˣ => ‖(a : AdeleRing (𝓞 ℚ) ℚ).1 Rat.infinitePlace‖ :=
    continuous_normInfty.measurable
  ext s hs
  rw [Measure.map_apply hm hs, withDensity_apply _ hs, ← lintegral_indicator_one (hm hs)]
  have h1 : ∀ a : (AdeleRing (𝓞 ℚ) ℚ)ˣ,
      (∏ w : InfinitePlace ℚ, s.indicator (1 : ℝ → ℝ≥0∞) ‖(a : AdeleRing (𝓞 ℚ) ℚ).1 w‖) =
      ((fun a : (AdeleRing (𝓞 ℚ) ℚ)ˣ => ‖(a : AdeleRing (𝓞 ℚ) ℚ).1 Rat.infinitePlace‖) ⁻¹' s).indicator 1 a :=
    fun a => by rw [Fintype.prod_subsingleton _ Rat.infinitePlace]; rfl
  have h2 := hrow (fun _ => s.indicator 1) fun _ => measurable_one.indicator hs
  simp only [h1, Fintype.prod_subsingleton _ Rat.infinitePlace] at h2
  rw [h2, Measure.restrict_restrict hs, ← lintegral_const_mul' _ _ hCtop]
  rw [← lintegral_indicator (hs.inter measurableSet_Ioi), ← lintegral_indicator measurableSet_Ioi]
  refine lintegral_congr fun t => ?_
  by_cases hts : t ∈ s <;> by_cases ht : (0 : ℝ) < t <;>
    simp [Set.indicator, hts, ht, ENNReal.ofReal_mul ENNReal.toReal_nonneg, ENNReal.ofReal_toReal hCtop,
      ENNReal.ofReal_inv_of_pos]

private theorem sigmaFinite_sPartMeasure_empty :
    letI : MeasurableSpace (AdeleRing (𝓞 ℚ) ℚ)ˣ := NumberField.Idele.ideleBorel ℚ
    SigmaFinite (NumberField.Idele.sPartMeasure ℚ ∅) := by
  letI : MeasurableSpace (AdeleRing (𝓞 ℚ) ℚ)ˣ := NumberField.Idele.ideleBorel ℚ
  haveI : BorelSpace (AdeleRing (𝓞 ℚ) ℚ)ˣ := NumberField.Idele.borelSpace_ideleBorel ℚ
  obtain ⟨c, -, hmap⟩ := exists_map_normInfty_sPartMeasure
  refine SigmaFinite.of_map _ continuous_normInfty.measurable.aemeasurable ?_
  rw [hmap]; infer_instance

private theorem pi_sPartMeasure_eq_map :
    letI : MeasurableSpace (AdeleRing (𝓞 ℚ) ℚ)ˣ := NumberField.Idele.ideleBorel ℚ
    (Measure.pi fun _ : Fin 3 => NumberField.Idele.sPartMeasure ℚ ∅) =
      Measure.map (fun t : Fin 3 → (AdeleRing (𝓞 ℚ) ℚ)ˣ => fun i => NumberField.Idele.partAt ℚ ∅ (t i))
        ((Measure.pi fun _ : Fin 3 => NumberField.Idele.idelicHaar ℚ).restrict
          (Set.pi Set.univ fun _ : Fin 3 =>
            (NumberField.AdeleRing.unitIdelesOutside (𝓞 ℚ) ℚ (↑(∅ : Finset (HeightOneSpectrum (𝓞 ℚ)))) :
            Set (AdeleRing (𝓞 ℚ) ℚ)ˣ))) := by
  letI : MeasurableSpace (AdeleRing (𝓞 ℚ) ℚ)ˣ := NumberField.Idele.ideleBorel ℚ
  haveI : ∀ _ : Fin 3, SigmaFinite (NumberField.Idele.idelicHaar ℚ) := fun _ => sigmaFinite_idelicHaar
  haveI : ∀ _ : Fin 3,
      SigmaFinite (Measure.map (NumberField.Idele.partAt ℚ ∅) ((NumberField.Idele.idelicHaar ℚ).restrict
        (NumberField.AdeleRing.unitIdelesOutside (𝓞 ℚ) ℚ (↑(∅ : Finset (HeightOneSpectrum (𝓞 ℚ)))) :
            Set (AdeleRing (𝓞 ℚ) ℚ)ˣ))) :=
    fun _ => sigmaFinite_sPartMeasure_empty
  have hpa : ∀ _ : Fin 3, AEMeasurable (NumberField.Idele.partAt ℚ ∅) ((NumberField.Idele.idelicHaar ℚ).restrict
      (NumberField.AdeleRing.unitIdelesOutside (𝓞 ℚ) ℚ (↑(∅ : Finset (HeightOneSpectrum (𝓞 ℚ)))) :
            Set (AdeleRing (𝓞 ℚ) ℚ)ˣ)) :=
    fun _ => (NumberField.Idele.measurable_partAt ℚ ∅).aemeasurable
  rw [@Measure.restrict_pi_pi _ _ _ _ (fun _ : Fin 3 => NumberField.Idele.idelicHaar ℚ)
      (fun _ => sigmaFinite_idelicHaar) _,
    Measure.pi_map_pi (hμ := fun _ => sigmaFinite_sPartMeasure_empty) hpa]
  rfl

private theorem setLIntegral_pi_idelicHaar_eq_lintegral_pi_sPartMeasure (F : AdelicGL 3 (𝓞 ℚ) ℚ → ℝ≥0∞)
    (hK : ∀ k : AdelicGL 3 (𝓞 ℚ) ℚ, k ∈ K ↔ archComponent3 (𝓞 ℚ) ℚ k ∈ orth3 ∧
      ∀ p : HeightOneSpectrum (𝓞 ℚ), componentAt3 (𝓞 ℚ) ℚ p k ∈ localMaximalCompact3 (𝓞 ℚ) ℚ p) :
    letI : MeasurableSpace (AdelicGL 3 (𝓞 ℚ) ℚ) := NumberField.AdelicHaar.glBorel (Fin 3) (𝓞 ℚ) ℚ
    letI : MeasurableSpace (AdeleRing (𝓞 ℚ) ℚ)ˣ := NumberField.Idele.ideleBorel ℚ
    ∀ (κ : Measure K) [κ.IsHaarMeasure], Measurable F →
      ∫⁻ t in Set.pi Set.univ fun _ : Fin 3 =>
          (NumberField.AdeleRing.unitIdelesOutside (𝓞 ℚ) ℚ (↑(∅ : Finset (HeightOneSpectrum (𝓞 ℚ)))) :
            Set (AdeleRing (𝓞 ℚ) ℚ)ˣ),
          ∫⁻ k : K, F (Units.map (Matrix.diagonalRingHom (Fin 3) (AdeleRing (𝓞 ℚ) ℚ)).toMonoidHom
                (MulEquiv.piUnits.symm t) * k) *
            ENNReal.ofReal ((NumberField.TateGlobal.ideleNorm ℚ (t 0))⁻¹ ^ 2 *
                NumberField.TateGlobal.ideleNorm ℚ (t 2) ^ 2)
          ∂κ ∂(Measure.pi fun _ : Fin 3 => NumberField.Idele.idelicHaar ℚ) =
        ∫⁻ t : Fin 3 → (AdeleRing (𝓞 ℚ) ℚ)ˣ, ∫⁻ k : K,
          F (Units.map (Matrix.diagonalRingHom (Fin 3) (AdeleRing (𝓞 ℚ) ℚ)).toMonoidHom
                (MulEquiv.piUnits.symm t) * k) *
            ENNReal.ofReal ((NumberField.TateGlobal.ideleNorm ℚ (t 0))⁻¹ ^ 2 *
                NumberField.TateGlobal.ideleNorm ℚ (t 2) ^ 2)
          ∂κ ∂(Measure.pi fun _ : Fin 3 => NumberField.Idele.sPartMeasure ℚ ∅) := by
  intro κ _ hF
  letI : MeasurableSpace (AdelicGL 3 (𝓞 ℚ) ℚ) := NumberField.AdelicHaar.glBorel (Fin 3) (𝓞 ℚ) ℚ
  letI : MeasurableSpace (AdeleRing (𝓞 ℚ) ℚ)ˣ := NumberField.Idele.ideleBorel ℚ
  haveI : BorelSpace (AdelicGL 3 (𝓞 ℚ) ℚ) := NumberField.AdelicHaar.borelSpace_glBorel (Fin 3) (𝓞 ℚ) ℚ
  haveI : BorelSpace (AdeleRing (𝓞 ℚ) ℚ)ˣ := NumberField.Idele.borelSpace_ideleBorel ℚ
  haveI := secondCountableTopology_adelicGL
  haveI := secondCountableTopology_idele
  haveI : SigmaFinite κ := sigmaFinite_haar_of_mem_iff K hK κ

  have hh : Measurable fun t : Fin 3 → (AdeleRing (𝓞 ℚ) ℚ)ˣ =>
      ∫⁻ k : K,
          F (Units.map (Matrix.diagonalRingHom (Fin 3) (AdeleRing (𝓞 ℚ) ℚ)).toMonoidHom
                (MulEquiv.piUnits.symm t) * k) *
            ENNReal.ofReal ((NumberField.TateGlobal.ideleNorm ℚ (t 0))⁻¹ ^ 2 *
                NumberField.TateGlobal.ideleNorm ℚ (t 2) ^ 2)
          ∂κ :=
    ((hF.comp (continuous_diagMul K).measurable).mul
      (measurable_normWeight.comp measurable_fst)).lintegral_prod_right'
  have hg : Measurable fun t : Fin 3 → (AdeleRing (𝓞 ℚ) ℚ)ˣ => fun i => NumberField.Idele.partAt ℚ ∅ (t i) :=
    measurable_pi_lambda _ fun i => (NumberField.Idele.measurable_partAt ℚ ∅).comp (measurable_pi_apply i)
  rw [(pi_sPartMeasure_eq_map : (Measure.pi fun _ : Fin 3 => NumberField.Idele.sPartMeasure ℚ ∅) = _),
    lintegral_map hh hg]
  exact setLIntegral_congr_fun measurableSet_pi_unitIdelesOutside fun t ht =>
    lintegral_diag_mul_eq_lintegral_diag_partAt_mul K F hK κ t ht

end ShellReduction

private theorem setLIntegral_zerothShell_eq_mul_lintegral_torus
    (K : Subgroup (AdelicGL 3 (𝓞 ℚ) ℚ))
    (hK : ∀ k : AdelicGL 3 (𝓞 ℚ) ℚ, k ∈ K ↔ archComponent3 (𝓞 ℚ) ℚ k ∈ orth3 ∧
      ∀ p : HeightOneSpectrum (𝓞 ℚ), componentAt3 (𝓞 ℚ) ℚ p k ∈ localMaximalCompact3 (𝓞 ℚ) ℚ p) :
    letI : MeasurableSpace (AdelicGL 3 (𝓞 ℚ) ℚ) := NumberField.AdelicHaar.glBorel (Fin 3) (𝓞 ℚ) ℚ
    letI : MeasurableSpace (AdeleRing (𝓞 ℚ) ℚ)ˣ := NumberField.Idele.ideleBorel ℚ
    ∀ (κ : Measure K) [κ.IsHaarMeasure],
      ∃ c : ℝ≥0∞, c ≠ 0 ∧ c ≠ ⊤ ∧ ∀ F : AdelicGL 3 (𝓞 ℚ) ℚ → ℝ≥0∞, Measurable F →
        (∀ n ∈ WhittakerBlock.unipotentSubgroup3, ∀ g : AdelicGL 3 (𝓞 ℚ) ℚ, F (n * g) = F g) →
        ∫⁻ q in WhittakerBlock.zerothShell ∅, F q.out ∂WhittakerBlock.quotientMeasure =
          c * ∫⁻ t : Fin 3 → (AdeleRing (𝓞 ℚ) ℚ)ˣ, ∫⁻ k : K,
            F (Units.map (Matrix.diagonalRingHom (Fin 3) (AdeleRing (𝓞 ℚ) ℚ)).toMonoidHom
                (MulEquiv.piUnits.symm t) * k) *
              ENNReal.ofReal ((NumberField.TateGlobal.ideleNorm ℚ (t 0))⁻¹ ^ 2 *
                NumberField.TateGlobal.ideleNorm ℚ (t 2) ^ 2)
            ∂κ ∂(Measure.pi fun _ : Fin 3 => NumberField.Idele.sPartMeasure ℚ ∅) := by
  intro κ _
  letI : MeasurableSpace (AdelicGL 3 (𝓞 ℚ) ℚ) := NumberField.AdelicHaar.glBorel (Fin 3) (𝓞 ℚ) ℚ
  letI : MeasurableSpace (AdeleRing (𝓞 ℚ) ℚ)ˣ := NumberField.Idele.ideleBorel ℚ
  obtain ⟨c, hc0, hc, hA⟩ := exists_lintegral_adelicGLHaar_eq_mul_lintegral_iwasawa3 K hK κ
  refine ⟨c, hc0, hc, fun F hF hFN => ?_⟩
  rw [setLIntegral_zerothShell_eq_lintegral_shellLift F hF hFN, hA _ (measurable_shellLift F hF),
    lintegral_iwasawa3_shellLift K F hK κ hF hFN,
    ← setLIntegral_pi_idelicHaar_eq_lintegral_pi_sPartMeasure K F hK κ hF,
    ← lintegral_indicator (measurableSet_pi_unitIdelesOutside)]
  congr 1
  refine lintegral_congr fun t => ?_
  by_cases ht : t ∈ Set.pi Set.univ fun _ : Fin 3 =>
          (NumberField.AdeleRing.unitIdelesOutside (𝓞 ℚ) ℚ (↑(∅ : Finset (HeightOneSpectrum (𝓞 ℚ)))) :
            Set (AdeleRing (𝓞 ℚ) ℚ)ˣ)
  · rw [Set.indicator_of_mem ht]
    exact lintegral_congr fun k => by
      rw [Set.indicator_of_mem ((diag_mul_mem_zerothShellSet_iff K hK t k k.2).2 ht)]
  · rw [Set.indicator_of_notMem ht]
    have h0 : ∀ k : K,
        zerothShellSet.indicator F
              (Units.map (Matrix.diagonalRingHom (Fin 3) (AdeleRing (𝓞 ℚ) ℚ)).toMonoidHom
                (MulEquiv.piUnits.symm t) * k) *
            ENNReal.ofReal ((NumberField.TateGlobal.ideleNorm ℚ (t 0))⁻¹ ^ 2 *
                NumberField.TateGlobal.ideleNorm ℚ (t 2) ^ 2) = 0 :=
      fun k => by
        rw [Set.indicator_of_notMem fun h => ht ((diag_mul_mem_zerothShellSet_iff K hK t k k.2).1 h), zero_mul]
    exact (lintegral_congr h0).trans lintegral_zero

end LanglandsTunnell.CubicInduction.WhittakerBlock

p2m_open "LanglandsTunnell.CubicInduction P2MW.S_LanglandsTunnell_CubicInduction_WhittakerBlock_setLIntegral_zerothShell_eq_mul_lintegral_torus.LanglandsTunnell.CubicInduction P2MW.S_LanglandsTunnell_CubicInduction_WhittakerBlock_setLIntegral_zerothShell_eq_mul_lintegral_torus.LanglandsTunnell.CubicInduction.WhittakerBlock"

theorem solution
    (K : Subgroup (AdelicGL 3 (𝓞 ℚ) ℚ))
    (hK : ∀ k : AdelicGL 3 (𝓞 ℚ) ℚ, k ∈ K ↔ archComponent3 (𝓞 ℚ) ℚ k ∈ orth3 ∧
      ∀ p : HeightOneSpectrum (𝓞 ℚ), componentAt3 (𝓞 ℚ) ℚ p k ∈ localMaximalCompact3 (𝓞 ℚ) ℚ p) :
    letI : MeasurableSpace (AdelicGL 3 (𝓞 ℚ) ℚ) := NumberField.AdelicHaar.glBorel (Fin 3) (𝓞 ℚ) ℚ
    letI : MeasurableSpace (AdeleRing (𝓞 ℚ) ℚ)ˣ := NumberField.Idele.ideleBorel ℚ
    ∀ (κ : Measure K) [κ.IsHaarMeasure],
      ∃ c : ℝ≥0∞, c ≠ 0 ∧ c ≠ ⊤ ∧ ∀ F : AdelicGL 3 (𝓞 ℚ) ℚ → ℝ≥0∞, Measurable F →
        (∀ n ∈ WhittakerBlock.unipotentSubgroup3, ∀ g : AdelicGL 3 (𝓞 ℚ) ℚ, F (n * g) = F g) →
        ∫⁻ q in WhittakerBlock.zerothShell ∅, F q.out ∂WhittakerBlock.quotientMeasure =
          c * ∫⁻ t : Fin 3 → (AdeleRing (𝓞 ℚ) ℚ)ˣ, ∫⁻ k : K,
            F (Units.map (Matrix.diagonalRingHom (Fin 3) (AdeleRing (𝓞 ℚ) ℚ)).toMonoidHom
                (MulEquiv.piUnits.symm t) * k) *
              ENNReal.ofReal ((NumberField.TateGlobal.ideleNorm ℚ (t 0))⁻¹ ^ 2 *
                NumberField.TateGlobal.ideleNorm ℚ (t 2) ^ 2)
            ∂κ ∂(Measure.pi fun _ : Fin 3 => NumberField.Idele.sPartMeasure ℚ ∅) :=
  setLIntegral_zerothShell_eq_mul_lintegral_torus K hK

end S_LanglandsTunnell_CubicInduction_WhittakerBlock_setLIntegral_zerothShell_eq_mul_lintegral_torus
end P2MW
export P2MW.S_LanglandsTunnell_CubicInduction_WhittakerBlock_setLIntegral_zerothShell_eq_mul_lintegral_torus (solution)
