-- Prove2me | solution 1 for OAI.SKGap.actual_logdet_mean
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T06:30:35.968657+00:00
-- url     : https://prove2.me/submissions/d94c583b-e0bc-4f94-86b1-b669fcc574e6

import Mathlib
import Definitions.Def_OAIQ072A000
import Definitions.Def_OAIQ072A001
import Theorems.Thm_OAI_SKGap_actual_projected_path_equivalents
import Theorems.Thm_OAI_SKGap_logPathGood_exponential

section
-- module Solutions.OAIQ072_SK.SKGap_Localization_Quadratic
attribute [-instance] _root_.OAI.SKGap.ComplexMatrix.frobeniusInnerProduct
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open MeasureTheory ProbabilityTheory InformationTheory Real Set
open scoped NNReal ENNReal
open Filter
open scoped Topology
noncomputable section
open Matrix Real
open scoped BigOperators Matrix.Norms.Frobenius ENNReal NNReal
noncomputable section
open Matrix Real
open scoped BigOperators Matrix.Norms.Frobenius NNReal
noncomputable section
open MeasureTheory ProbabilityTheory Real Set Filter
open MeasureTheory.Measure
open scoped ENNReal NNReal MeasureTheory Topology
open MeasureTheory
noncomputable section
noncomputable section
open MeasureTheory Set NormedSpace
open scoped Topology
noncomputable section
open Matrix Real
open scoped BigOperators Matrix.Norms.Frobenius
noncomputable section
open Set Real
open scoped Topology
noncomputable section
open Matrix Set Filter
open scoped Topology Matrix.Norms.Frobenius
namespace SKGap.ComplexSpectral
variable {ι : Type*} [Fintype ι]

lemma continuous_quadratic :
    Continuous (fun p : Matrix ι ι ℂ × EuclideanSpace ℂ ι => quadratic p.1 p.2) := by
  unfold quadratic dotProduct mulVec
  fun_prop

lemma compact_unitSphere : IsCompact (unitSphere ι) := isCompact_sphere _ _

lemma continuous_lowerRayleigh : Continuous (lowerRayleigh (ι := ι)) :=
  compact_unitSphere.continuous_sInf continuous_quadratic

lemma quadratic_neg (M : Matrix ι ι ℂ) (x : EuclideanSpace ℂ ι) :
    quadratic (-M) x = -quadratic M x := by simp [quadratic,Matrix.neg_mulVec,dotProduct_neg]

lemma lowerRayleigh_le (M : Matrix ι ι ℂ) {x : EuclideanSpace ℂ ι}
    (hx : x ∈ unitSphere ι) : lowerRayleigh M ≤ quadratic M x := by
  have hb : BddBelow (quadratic M '' unitSphere ι) :=
    (compact_unitSphere.image (continuous_quadratic.comp (continuous_const.prodMk continuous_id))).bddBelow
  exact csInf_le hb ⟨x,hx,rfl⟩

variable [DecidableEq ι]

lemma quadratic_eigenvector {M : Matrix ι ι ℂ} (hM : M.IsHermitian) (i : ι) :
    quadratic M (hM.eigenvectorBasis i) = hM.eigenvalues i := by
  exact (hM.eigenvalues_eq i).symm

lemma eigenvalue_lower_bound {M : Matrix ι ι ℂ} (hM : M.IsHermitian) (i : ι) :
    lowerRayleigh M ≤ hM.eigenvalues i := by
  rw [← quadratic_eigenvector hM i]
  apply lowerRayleigh_le
  simpa only [unitSphere,Metric.mem_sphere,dist_zero_right] using hM.eigenvectorBasis.orthonormal.1 i

lemma eigenvalue_upper_bound {M : Matrix ι ι ℂ} (hM : M.IsHermitian) (i : ι) :
    hM.eigenvalues i ≤ -lowerRayleigh (-M) := by
  have hh := lowerRayleigh_le (-M) (x := hM.eigenvectorBasis i)
    (by simpa only [unitSphere,Metric.mem_sphere,dist_zero_right] using hM.eigenvectorBasis.orthonormal.1 i)
  rw [quadratic_neg,quadratic_eigenvector] at hh
  linarith

end SKGap.ComplexSpectral

end
end
end
end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Matrix_MatrixCoordinates
attribute [-instance] _root_.OAI.SKGap.ComplexMatrix.frobeniusInnerProduct
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory InformationTheory Real Set
open scoped NNReal ENNReal
open Filter
open scoped Topology
open Matrix Real
open scoped BigOperators Matrix.Norms.Frobenius ENNReal NNReal
namespace SKGap

variable {ι : Type*}

variable [Fintype ι]

lemma rawCoordinateMatrix_norm (g : EuclideanSpace ℝ (MatrixCoordinates ι)) :
    ‖rawCoordinateMatrix g‖ ≤ ‖g‖ := by
  apply nonneg_le_nonneg_of_sq_le_sq (norm_nonneg _)
  simp only [← sq]
  rw [Matrix.frobenius_norm_def,← Real.sqrt_eq_rpow,Real.sq_sqrt (by positivity),
    EuclideanSpace.norm_sq_eq]
  simp only [Real.rpow_two,Real.norm_eq_abs,sq_abs,Fintype.sum_sum_type,Fintype.sum_prod_type,
    rawCoordinateMatrix]
  exact le_add_of_nonneg_right (Finset.sum_nonneg (fun _ _ => sq_nonneg _))

lemma goeMatrix_norm (r : ℝ) (g : EuclideanSpace ℝ (MatrixCoordinates ι)) :
    ‖goeMatrix r g‖ ≤ sqrt (2*r)*‖g‖ := by
  have he : goeMatrix r g = (sqrt (2*r)/2) •
      (rawCoordinateMatrix g+(rawCoordinateMatrix g)ᵀ) := by ext; rfl
  rw [he,norm_smul,Real.norm_eq_abs,abs_of_nonneg (by positivity)]
  calc
    _ ≤ (sqrt (2*r)/2)*(‖rawCoordinateMatrix g‖+‖(rawCoordinateMatrix g)ᵀ‖) :=
      mul_le_mul_of_nonneg_left (norm_add_le _ _) (by positivity)
    _ = sqrt (2*r)*‖rawCoordinateMatrix g‖ := by rw [Matrix.frobenius_norm_transpose]; ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (rawCoordinateMatrix_norm g) (sqrt_nonneg _)

omit [Fintype ι] in
lemma goeMatrix_sub (r : ℝ) (g h : MatrixCoordinates ι → ℝ) :
    goeMatrix r (g-h) = goeMatrix r g-goeMatrix r h := by
  ext i k; simp only [goeMatrix,Pi.sub_apply,Matrix.sub_apply]; ring

lemma goeMatrix_L2_lipschitz (r : ℝ) :
    LipschitzWith ⟨sqrt (2*r),sqrt_nonneg _⟩
      (fun g : EuclideanSpace ℝ (MatrixCoordinates ι) => goeMatrix r g) := by
  apply LipschitzWith.of_dist_le_mul
  intro g h
  simpa only [dist_eq_norm,← goeMatrix_sub] using! goeMatrix_norm r (g-h)

lemma goeMatrix_pi_lipschitz (r : ℝ) :
    LipschitzWith (⟨sqrt (2*r),sqrt_nonneg _⟩ *
      (Fintype.card (MatrixCoordinates ι) : ℝ≥0) ^ (1/(2:ℝ≥0∞)).toReal)
      (goeMatrix (ι := ι) r) := by
  exact (goeMatrix_L2_lipschitz (ι := ι) r).comp
    (PiLp.lipschitzWith_toLp 2 (fun _ : MatrixCoordinates ι => ℝ))

end SKGap

end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Matrix_OpNorm
attribute [-instance] _root_.OAI.SKGap.ComplexMatrix.frobeniusInnerProduct
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory InformationTheory Real Set
open scoped NNReal ENNReal
open Filter
open scoped Topology
open Matrix Real
open scoped BigOperators Matrix.Norms.Frobenius ENNReal NNReal
namespace SKGap
open MeasureTheory ProbabilityTheory Matrix
open scoped BigOperators Matrix.Norms.Frobenius
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma colVec_eq (M : Matrix ι ι ℝ) (k : ι) :
    colVec M k = M.toEuclideanLin.toContinuousLinearMap (EuclideanSpace.single k (1:ℝ)) := by
  ext i
  simp [colVec,Matrix.toLpLin_apply]

lemma colVec_norm_le (M : Matrix ι ι ℝ) (k : ι) : ‖colVec M k‖ ≤ opNorm M := by
  rw [colVec_eq]
  simpa only [PiLp.norm_single,norm_one,mul_one,opNorm] using!
    M.toEuclideanLin.toContinuousLinearMap.le_opNorm (EuclideanSpace.single k (1:ℝ))

lemma matrix_entry_le_opNorm (M : Matrix ι ι ℝ) (i k : ι) : |M i k| ≤ opNorm M := by
  have h : |M i k| ≤ ‖colVec M k‖ := by
    simpa only [colVec,Real.norm_eq_abs] using (PiLp.norm_apply_le (colVec M k) i)
  exact h.trans (colVec_norm_le M k)

lemma opNorm_mul (M N : Matrix ι ι ℝ) : opNorm (M*N) ≤ opNorm M*opNorm N := by
  have he : (M*N).toEuclideanLin.toContinuousLinearMap =
      M.toEuclideanLin.toContinuousLinearMap * N.toEuclideanLin.toContinuousLinearMap := by
    ext x i
    exact congrFun (congrArg (fun T : EuclideanSpace ℝ ι →ₗ[ℝ] EuclideanSpace ℝ ι => (T x).ofLp)
      (Matrix.toLpLin_mul 2 2 2 M N)) i
  exact (congrArg norm he).le.trans (norm_mul_le _ _)

end SKGap

end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Localization_FrobeniusSq
attribute [-instance] _root_.OAI.SKGap.ComplexMatrix.frobeniusInnerProduct
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory InformationTheory Real Set
open scoped NNReal ENNReal
open Filter
open scoped Topology
open Matrix Real
open scoped BigOperators Matrix.Norms.Frobenius ENNReal NNReal
open Matrix Real
open scoped BigOperators Matrix.Norms.Frobenius NNReal
namespace SKGap
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma frobenius_col_sq (M : Matrix ι ι ℝ) : ‖M‖^2 = ∑ k, ‖colVec M k‖^2 := by
  rw [frobenius_sq,Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k _
  rw [EuclideanSpace.norm_sq_eq]
  simp [colVec,Real.norm_eq_abs,sq_abs]

lemma colVec_mul (M N : Matrix ι ι ℝ) (k : ι) :
    colVec (M*N) k = M.toEuclideanLin.toContinuousLinearMap (colVec N k) := by
  ext i
  rfl

lemma frobenius_mul_le_opNorm (M N : Matrix ι ι ℝ) : ‖M*N‖ ≤ opNorm M * ‖N‖ := by
  have hp : 0 ≤ opNorm M := norm_nonneg _
  apply nonneg_le_nonneg_of_sq_le_sq (mul_nonneg hp (norm_nonneg N))
  simp only [← sq]
  rw [frobenius_col_sq,mul_pow,frobenius_col_sq,Finset.mul_sum]
  apply Finset.sum_le_sum
  intro k _
  rw [colVec_mul]
  have hh := M.toEuclideanLin.toContinuousLinearMap.le_opNorm (colVec N k)
  change ‖M.toEuclideanLin.toContinuousLinearMap (colVec N k)‖ ≤ opNorm M * ‖colVec N k‖ at hh
  nlinarith only [hh, norm_nonneg (M.toEuclideanLin.toContinuousLinearMap (colVec N k)),
    mul_nonneg hp (norm_nonneg (colVec N k))]

lemma opNorm_transpose (M : Matrix ι ι ℝ) : opNorm Mᵀ = opNorm M := by
  change ‖Mᵀ.toEuclideanLin.toContinuousLinearMap‖ = ‖M.toEuclideanLin.toContinuousLinearMap‖
  have he : Mᵀ.toEuclideanLin.toContinuousLinearMap =
      ContinuousLinearMap.adjoint M.toEuclideanLin.toContinuousLinearMap := by
    apply ContinuousLinearMap.ext
    intro x
    apply ext_inner_left ℝ
    intro y
    rw [ContinuousLinearMap.adjoint_inner_right]
    change (∑ i, (∑ k, M k i*x k)*y i) = ∑ i, x i * (∑ k, M i k*y k)
    simp only [Finset.sum_mul,Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro k _
    ring
  rw [he,ContinuousLinearMap.adjoint.norm_map]

lemma frobenius_mul_le_opNorm_right (M N : Matrix ι ι ℝ) : ‖M*N‖ ≤ ‖M‖ * opNorm N := by
  rw [← Matrix.frobenius_norm_transpose (M*N),Matrix.transpose_mul]
  exact (frobenius_mul_le_opNorm Nᵀ Mᵀ).trans_eq (by rw [opNorm_transpose,Matrix.frobenius_norm_transpose,mul_comm])

end SKGap

end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Localization_ExpDuhamel
attribute [-instance] _root_.OAI.SKGap.ComplexMatrix.frobeniusInnerProduct
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory InformationTheory Real Set
open scoped NNReal ENNReal
open Filter
open scoped Topology
open Matrix Real
open scoped BigOperators Matrix.Norms.Frobenius ENNReal NNReal
open Matrix Real
open scoped BigOperators Matrix.Norms.Frobenius NNReal
open MeasureTheory ProbabilityTheory Real Set Filter
open MeasureTheory.Measure
open scoped ENNReal NNReal MeasureTheory Topology
open MeasureTheory
open MeasureTheory Set NormedSpace
open scoped Topology
namespace SKGap
section Algebra
variable {A : Type*} [NormedRing A] [NormedAlgebra ℝ A] [NormedAlgebra ℚ A] [CompleteSpace A]

lemma exp_duhamel (a b : A) :
    exp a - exp b = ∫ u : ℝ in (0 : ℝ)..1, exp ((1-u) • a) * (a-b) * exp (u • b) := by
  have hd (u : ℝ) : HasDerivAt (fun u : ℝ => exp ((1-u) • a) * exp (u • b))
      (-(exp ((1-u) • a) * (a-b) * exp (u • b))) u := by
    have h₁ := (hasDerivAt_exp_smul_const a (1-u)).scomp u ((hasDerivAt_const u (1:ℝ)).sub (hasDerivAt_id u))
    have h₂ := hasDerivAt_exp_smul_const' b u
    convert h₁.mul h₂ using 1 <;> (try simp only [zero_sub, neg_smul, one_smul]) <;> noncomm_ring
  have hc : Continuous (fun u : ℝ => -(exp ((1-u) • a) * (a-b) * exp (u • b))) := by fun_prop
  have hh := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun u _ => hd u)
    (hc.intervalIntegrable 0 1)
  simpa only [intervalIntegral.integral_neg, sub_self, zero_smul, NormedSpace.exp_zero, one_mul,
    sub_zero, one_smul, mul_one, neg_neg, neg_sub] using congrArg Neg.neg hh.symm

end Algebra

end SKGap

open Matrix Real
open scoped BigOperators Matrix.Norms.Frobenius
namespace SKGap
namespace ComplexMatrix
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma frobenius_mul_le_opNorm (M N : Matrix ι ι ℂ) : ‖M*N‖ ≤ opNorm M * ‖N‖ := by
  have hp : 0 ≤ opNorm M := norm_nonneg _
  apply nonneg_le_nonneg_of_sq_le_sq (mul_nonneg hp (norm_nonneg N))
  simp only [← sq]
  rw [frobenius_col_sq,mul_pow,frobenius_col_sq,Finset.mul_sum]
  apply Finset.sum_le_sum
  intro k _
  rw [colVec_mul]
  have hh := (lin M).le_opNorm (colVec N k)
  change ‖lin M (colVec N k)‖ ≤ opNorm M * ‖colVec N k‖ at hh
  nlinarith only [hh,norm_nonneg (lin M (colVec N k)),mul_nonneg hp (norm_nonneg (colVec N k))]

lemma opNorm_adjoint (M : Matrix ι ι ℂ) : opNorm Mᴴ = opNorm M := by
  rw [opNorm,lin_adjoint,ContinuousLinearMap.adjoint.norm_map]
  rfl

lemma frobenius_mul_le_opNorm_right (M N : Matrix ι ι ℂ) : ‖M*N‖ ≤ ‖M‖ * opNorm N := by
  rw [← Matrix.frobenius_norm_conjTranspose (M*N),Matrix.conjTranspose_mul]
  exact (frobenius_mul_le_opNorm Nᴴ Mᴴ).trans_eq (by rw [opNorm_adjoint,Matrix.frobenius_norm_conjTranspose,mul_comm])

end ComplexMatrix
end SKGap

end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Localization_LinSub
attribute [-instance] _root_.OAI.SKGap.ComplexMatrix.frobeniusInnerProduct
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory InformationTheory Real Set
open scoped NNReal ENNReal
open Filter
open scoped Topology
open Matrix Real
open scoped BigOperators Matrix.Norms.Frobenius ENNReal NNReal
open Matrix Real
open scoped BigOperators Matrix.Norms.Frobenius NNReal
open MeasureTheory ProbabilityTheory Real Set Filter
open MeasureTheory.Measure
open scoped ENNReal NNReal MeasureTheory Topology
open MeasureTheory
open MeasureTheory Set NormedSpace
open scoped Topology
open Matrix Real
open scoped BigOperators Matrix.Norms.Frobenius
namespace SKGap.ComplexMatrix

section
open MeasureTheory Set NormedSpace
open scoped Topology
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma unitary_exp_smul (M : Matrix ι ι ℂ) (hM : Mᴴ = -M) (u : ℝ) :
    exp (u • M) ∈ unitary (Matrix ι ι ℂ) := by
  apply exp_mem_unitary_of_mem_skewAdjoint
  change (u • M)ᴴ = -(u • M)
  simp [hM]

lemma frobenius_exp_sub (M N : Matrix ι ι ℂ) (hM : Mᴴ = -M) (hN : Nᴴ = -N) :
    ‖exp M-exp N‖ ≤ ‖M-N‖ := by
  rw [show exp M-exp N = _ from SKGap.exp_duhamel M N]
  have hh (u : ℝ) : ‖exp ((1-u) • M) * (M-N) * exp (u • N)‖ = ‖M-N‖ := by
    rw [frobenius_mul_unitary _ _ (unitary_exp_smul N hN u),
      frobenius_unitary_mul _ _ (unitary_exp_smul M hM (1-u))]
  calc
    _ ≤ ∫ u : ℝ in (0 : ℝ)..1, ‖exp ((1-u) • M) * (M-N) * exp (u • N)‖ :=
      intervalIntegral.norm_integral_le_integral_norm (by norm_num)
    _ = ‖M-N‖ := by simp only [hh]; simp

end

open MeasureTheory Set NormedSpace
open scoped Topology FourierTransform SchwartzMap
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

local instance instPseudoMetrizableSpaceMatrixComplex_solutions : TopologicalSpace.PseudoMetrizableSpace (Matrix ι ι ℂ) :=
  inferInstanceAs (TopologicalSpace.PseudoMetrizableSpace (ι → ι → ℂ))

lemma lin_csmul (z : ℂ) (M : Matrix ι ι ℂ) : lin (z • M) = z • lin M :=
  (linEquiv (ι := ι)).map_smul z M

omit [Fintype ι] [DecidableEq ι] in
lemma imaginary_skew (t : ℝ) (M : Matrix ι ι ℂ) (hM : Mᴴ = M) :
    (imaginary t M)ᴴ = -(imaginary t M) := by
  simp [imaginary,Matrix.conjTranspose_smul,hM,star_mul,mul_comm]

lemma imaginary_norm (t : ℝ) (M : Matrix ι ι ℂ) : ‖imaginary t M‖ = |t| * ‖M‖ := by
  simp [imaginary,norm_smul]

omit [Fintype ι] [DecidableEq ι] in
lemma imaginary_sub (t : ℝ) (M N : Matrix ι ι ℂ) :
    imaginary t (M-N) = imaginary t M-imaginary t N := by simp [imaginary,smul_sub]

lemma imaginary_exp_unitary (t : ℝ) (M : Matrix ι ι ℂ) (hM : Mᴴ = M) :
    exp (imaginary t M) ∈ unitary (Matrix ι ι ℂ) := by
  simpa using unitary_exp_smul _ (imaginary_skew t M hM) 1

lemma imaginary_exp_norm (t : ℝ) (M : Matrix ι ι ℂ) (hM : Mᴴ = M) :
    ‖exp (imaginary t M)‖ = ‖(1 : Matrix ι ι ℂ)‖ := by
  simpa using frobenius_unitary_mul (exp (imaginary t M)) 1 (imaginary_exp_unitary t M hM)

lemma imaginary_exp_opNorm_le (t : ℝ) (M : Matrix ι ι ℂ) (hM : Mᴴ = M) :
    opNorm (exp (imaginary t M)) ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by norm_num)
  intro x
  rw [ContinuousLinearMap.norm_map_of_mem_unitary (lin_unitary _ (imaginary_exp_unitary t M hM))]
  simp

attribute [local instance] OAI.SKGap.ComplexMatrix.instContinuousENormMatrixComplex_solutions
lemma kernel_integrable {g : ℝ → ℂ} (hg : Integrable g) (M : Matrix ι ι ℂ) (hM : Mᴴ = M) :
    Integrable (fun t : ℝ => g t • exp (imaginary t M)) := by
  have hc : Continuous (fun t : ℝ => exp (imaginary t M)) := by dsimp [imaginary]; fun_prop
  apply (hg.norm.mul_const ‖(1 : Matrix ι ι ℂ)‖).mono' (hg.aestronglyMeasurable.smul hc.aestronglyMeasurable)
  filter_upwards [] with t
  change ‖g t • exp (imaginary t M)‖ ≤ _
  rw [norm_smul,imaginary_exp_norm t M hM]

lemma kernelMatrix_lipschitz {g : ℝ → ℂ} (hg : Integrable g)
    (hg₁ : Integrable (fun t : ℝ => ‖g t‖*|t|))
    (M N : Matrix ι ι ℂ) (hM : Mᴴ = M) (hN : Nᴴ = N) :
    ‖kernelMatrix g M-kernelMatrix g N‖ ≤ (∫ t : ℝ, ‖g t‖*|t|) * ‖M-N‖ := by
  rw [kernelMatrix,kernelMatrix,← integral_sub (kernel_integrable hg M hM) (kernel_integrable hg N hN)]
  calc
    _ ≤ ∫ t : ℝ, ‖g t • exp (imaginary t M)-g t • exp (imaginary t N)‖ := norm_integral_le_integral_norm _
    _ ≤ ∫ t : ℝ, (‖g t‖*|t|)*‖M-N‖ := by
      apply integral_mono ((kernel_integrable hg M hM).sub (kernel_integrable hg N hN)).norm (hg₁.mul_const _)
      intro t
      dsimp only [Pi.sub_apply]
      rw [← smul_sub,norm_smul]
      have hh := frobenius_exp_sub _ _ (imaginary_skew t M hM) (imaginary_skew t N hN)
      rw [← imaginary_sub,imaginary_norm] at hh
      exact (mul_le_mul_of_nonneg_left hh (norm_nonneg _)).trans_eq (mul_assoc _ _ _).symm
    _ = _ := integral_mul_const _ _

end SKGap.ComplexMatrix

end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Localization_EntryLM
attribute [-instance] _root_.OAI.SKGap.ComplexMatrix.frobeniusInnerProduct
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory InformationTheory Real Set
open scoped NNReal ENNReal
open Filter
open scoped Topology
open Matrix Real
open scoped BigOperators Matrix.Norms.Frobenius ENNReal NNReal
open Matrix Real
open scoped BigOperators Matrix.Norms.Frobenius NNReal
open MeasureTheory ProbabilityTheory Real Set Filter
open MeasureTheory.Measure
open scoped ENNReal NNReal MeasureTheory Topology
open MeasureTheory
open MeasureTheory Set NormedSpace
open scoped Topology
open Matrix Real
open scoped BigOperators Matrix.Norms.Frobenius
namespace SKGap.ComplexMatrix

section
open MeasureTheory Set NormedSpace
open scoped Topology FourierTransform SchwartzMap
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

attribute [local instance] OAI.SKGap.ComplexMatrix.instContinuousENormMatrixComplex_solutions_1
local instance instPseudoMetrizableSpaceMatrixComplex_solutions_1_rfb067a_1 : TopologicalSpace.PseudoMetrizableSpace (Matrix ι ι ℂ) :=
  inferInstanceAs (TopologicalSpace.PseudoMetrizableSpace (ι → ι → ℂ))
lemma integral_entry {F : ℝ → Matrix ι ι ℂ} (hF : Integrable F) (i j : ι) :
    (∫ t : ℝ, F t) i j = ∫ t : ℝ, F t i j := by
  exact ((entryCLM i j).integral_comp_comm hF).symm

lemma conjugate_exp (U : unitary (Matrix ι ι ℂ)) (M : Matrix ι ι ℂ) :
    conjugate U (exp M) = exp (conjugate U M) := by
  exact NormedSpace.map_exp (conjugate U).toRingHom (conjugateCLM U).continuous M

lemma conjugate_imaginary (U : unitary (Matrix ι ι ℂ)) (t : ℝ) (M : Matrix ι ι ℂ) :
    conjugate U (imaginary t M) = imaginary t (conjugate U M) := by
  exact (conjugate U).map_smul' _ _

lemma kernelMatrix_conjugate {g : ℝ → ℂ} (hg : Integrable g) (U : unitary (Matrix ι ι ℂ))
    (M : Matrix ι ι ℂ) (hM : Mᴴ = M) :
    kernelMatrix g (conjugate U M) = conjugate U (kernelMatrix g M) := by
  have hi := (conjugateCLM U).integral_comp_comm (kernel_integrable hg M hM)
  change _ = (conjugateCLM U) (∫ t : ℝ, g t • exp (imaginary t M))
  calc
    _ = ∫ t : ℝ, (conjugateCLM U) (g t • exp (imaginary t M)) := by
      apply integral_congr_ae
      filter_upwards [] with t
      change g t • exp (imaginary t (conjugate U M)) = conjugate U (g t • exp (imaginary t M))
      rw [map_smul,conjugate_exp,conjugate_imaginary]
    _ = _ := hi

lemma kernelMatrix_diagonal {g : ℝ → ℂ} (hg : Integrable g) (x : ι → ℝ) :
    kernelMatrix g (diagonal (fun i => (x i : ℂ))) =
      diagonal (fun i => ∫ t : ℝ, g t * Complex.exp ((t : ℂ)*Complex.I*(x i : ℂ))) := by
  have hD : (diagonal (fun i => (x i : ℂ)))ᴴ = diagonal (fun i => (x i : ℂ)) := by
    simp [Matrix.diagonal_conjTranspose]
  ext i j
  rw [kernelMatrix,integral_entry (kernel_integrable hg _ hD)]
  have hexp (t : ℝ) : exp (imaginary t (diagonal (fun i => (x i : ℂ)))) =
      diagonal (fun i => Complex.exp ((t : ℂ)*Complex.I*(x i : ℂ))) := by
    rw [imaginary,← diagonal_smul,Matrix.exp_diagonal]
    congr 1
    ext i
    rw [Pi.coe_exp,← Complex.exp_eq_exp_ℂ]
    rfl
  simp_rw [hexp,Matrix.smul_apply,smul_eq_mul]
  by_cases hij : i = j
  · subst j; simp
  · simp [hij]

lemma fourier_scalar_inverse (f : 𝓢(ℝ, ℂ)) (x : ℝ) :
    (∫ t : ℝ, (𝓕 f) t * Complex.exp ((t : ℂ)*Complex.I*((2*Real.pi*x : ℝ) : ℂ))) = f x := by
  have hh := congrArg (fun g : 𝓢(ℝ,ℂ) => g x) (show (𝓕⁻ (𝓕 f : 𝓢(ℝ,ℂ)) : 𝓢(ℝ,ℂ)) = f from FourierTransform.fourierInv_fourier_eq f)
  rw [SchwartzMap.fourierInv_coe,Real.fourierInv_eq'] at hh
  rw [← hh]
  apply integral_congr_ae
  filter_upwards [] with t
  simp only [smul_eq_mul,Real.inner_apply]
  conv_lhs => rw [mul_comm]
  congr 1
  congr 1
  push_cast
  ring

lemma schwartzMatrix_diagonal (f : 𝓢(ℝ,ℂ)) (x : ι → ℝ) :
    schwartzMatrix f (diagonal (fun i => (x i : ℂ))) = diagonal (fun i => f (x i)) := by
  rw [schwartzMatrix,← diagonal_smul]
  have heq : (2*Real.pi : ℝ) • (fun i => (x i : ℂ)) = fun i => ((2*Real.pi*x i : ℝ) : ℂ) := by
    ext i; simp
  rw [heq,kernelMatrix_diagonal (𝓕 f).integrable]
  congr 1
  ext i
  exact fourier_scalar_inverse f (x i)

lemma schwartzMatrix_conjugate (f : 𝓢(ℝ,ℂ)) (U : unitary (Matrix ι ι ℂ))
    (M : Matrix ι ι ℂ) (hM : Mᴴ = M) :
    schwartzMatrix f (conjugate U M) = conjugate U (schwartzMatrix f M) := by
  have heq : (2*Real.pi : ℝ) • conjugate U M = conjugate U ((2*Real.pi : ℝ) • M) := by
    simp [conjugate,Unitary.conjStarAlgAut_apply]
  rw [schwartzMatrix,heq]
  exact kernelMatrix_conjugate (𝓕 f).integrable U _ (by simp [hM])

lemma schwartzMatrix_spectral (f : 𝓢(ℝ,ℂ)) (M : Matrix ι ι ℂ) (hM : M.IsHermitian) :
    schwartzMatrix f M = conjugate hM.eigenvectorUnitary (diagonal (fun i => f (hM.eigenvalues i))) := by
  conv_lhs => rw [hM.spectral_theorem]
  change schwartzMatrix f (conjugate hM.eigenvectorUnitary (diagonal (fun i => (hM.eigenvalues i : ℂ)))) = _
  rw [schwartzMatrix_conjugate f _ _ (by simp [Matrix.diagonal_conjTranspose]),schwartzMatrix_diagonal]

end

open MeasureTheory Set NormedSpace
open scoped Topology FourierTransform SchwartzMap
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma opNorm_kernelMatrix {g : ℝ → ℂ} (hg : Integrable g)
    (M : Matrix ι ι ℂ) (hM : Mᴴ = M) :
    opNorm (kernelMatrix g M) ≤ ∫ t : ℝ, ‖g t‖ := by
  let : CompleteSpace (EuclideanSpace ℂ ι →L[ℂ] EuclideanSpace ℂ ι) :=
    ContinuousLinearMap.instCompleteSpace
  have hi := linCLM.integral_comp_comm (kernel_integrable hg M hM)
  change ‖linCLM (∫ t : ℝ, g t • exp (imaginary t M))‖ ≤ _
  calc
    _ = ‖∫ t : ℝ, linCLM (g t • exp (imaginary t M))‖ := congrArg norm hi.symm
    _ ≤ ∫ t : ℝ, ‖linCLM (g t • exp (imaginary t M))‖ := norm_integral_le_integral_norm _
    _ ≤ ∫ t : ℝ, ‖g t‖ := by
      apply integral_mono (linCLM.integrable_comp (kernel_integrable hg M hM)).norm hg.norm
      intro t
      change ‖lin (g t • exp (imaginary t M))‖ ≤ _
      rw [lin_csmul,norm_smul]
      exact (mul_le_mul_of_nonneg_left (imaginary_exp_opNorm_le t M hM) (norm_nonneg _)).trans_eq (mul_one _)

lemma schwartzMatrix_opNorm (f : 𝓢(ℝ,ℂ)) (M : Matrix ι ι ℂ) (hM : Mᴴ = M) :
    opNorm (schwartzMatrix f M) ≤ ∫ t : ℝ, ‖(𝓕 f) t‖ :=
  opNorm_kernelMatrix (𝓕 f).integrable _ (by simp [hM])

lemma schwartzMatrix_eq_inverse (f : 𝓢(ℝ,ℂ)) {lo hi : ℝ} (hlo : 0 < lo)
    (hf : ∀ x ∈ Icc lo hi, f x = (x : ℂ)⁻¹)
    (M : Matrix ι ι ℂ) (hM : M.IsHermitian)
    (hspec : ∀ i, hM.eigenvalues i ∈ Icc lo hi) :
    schwartzMatrix f M = M⁻¹ := by
  rw [schwartzMatrix_spectral f M hM]
  symm
  apply Matrix.inv_eq_left_inv
  conv_lhs => rhs; rw [hM.spectral_theorem]
  change conjugate hM.eigenvectorUnitary (diagonal (fun i => f (hM.eigenvalues i))) *
    conjugate hM.eigenvectorUnitary (diagonal (fun i => (hM.eigenvalues i : ℂ))) = 1
  rw [← map_mul,diagonal_mul_diagonal]
  have hd : diagonal (fun i => f (hM.eigenvalues i) * (hM.eigenvalues i : ℂ)) = (1 : Matrix ι ι ℂ) := by
    have hz (i : ι) : (hM.eigenvalues i : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt (lt_of_lt_of_le hlo (hspec i).1)
    simp_rw [hf _ (hspec _),inv_mul_cancel₀ (hz _)]
    exact diagonal_one
  rw [hd,map_one]

end SKGap.ComplexMatrix

end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Gaussian_FourierMoment
attribute [-instance] _root_.OAI.SKGap.ComplexMatrix.frobeniusInnerProduct
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory InformationTheory Real Set
open scoped NNReal ENNReal
open Filter
open scoped Topology
open Matrix Real
open scoped BigOperators Matrix.Norms.Frobenius ENNReal NNReal
open Matrix Real
open scoped BigOperators Matrix.Norms.Frobenius NNReal
open MeasureTheory ProbabilityTheory Real Set Filter
open MeasureTheory.Measure
open scoped ENNReal NNReal MeasureTheory Topology
open MeasureTheory
open MeasureTheory Set NormedSpace
open scoped Topology
open Matrix Real
open scoped BigOperators Matrix.Norms.Frobenius
namespace SKGap.ComplexMatrix
open MeasureTheory NormedSpace
open scoped FourierTransform SchwartzMap
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma fourierMoment_integrable (f : 𝓢(ℝ,ℂ)) (k : ℕ) :
    Integrable (fun t : ℝ => ‖(𝓕 f) t‖*|t|^k) := by
  simpa only [Real.norm_eq_abs,mul_comm] using (𝓕 f).integrable_pow_mul volume k

lemma schwartzMatrix_lipschitz (f : 𝓢(ℝ,ℂ)) (M N : Matrix ι ι ℂ)
    (hM : Mᴴ = M) (hN : Nᴴ = N) :
    ‖schwartzMatrix f M-schwartzMatrix f N‖ ≤
      (2*Real.pi*fourierMoment f 1)*‖M-N‖ := by
  have hf₁ : Integrable (fun t : ℝ => ‖(𝓕 f) t‖*|t|) := by
    simpa only [pow_one] using fourierMoment_integrable f 1
  have hh := kernelMatrix_lipschitz (𝓕 f).integrable hf₁
    ((2*Real.pi:ℝ) • M) ((2*Real.pi:ℝ) • N) (by simp [hM]) (by simp [hN])
  rw [← smul_sub,norm_smul,Real.norm_eq_abs,abs_of_pos (by positivity : 0 < (2*Real.pi:ℝ))] at hh
  exact hh.trans_eq (by simp only [fourierMoment,pow_one]; ring)

end SKGap.ComplexMatrix

end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Matrix_OpNormKernelMatrixSub
attribute [-instance] _root_.OAI.SKGap.ComplexMatrix.frobeniusInnerProduct
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory InformationTheory Real Set
open scoped NNReal ENNReal
open Filter
open scoped Topology
open Matrix Real
open scoped BigOperators Matrix.Norms.Frobenius ENNReal NNReal
open Matrix Real
open scoped BigOperators Matrix.Norms.Frobenius NNReal
open MeasureTheory ProbabilityTheory Real Set Filter
open MeasureTheory.Measure
open scoped ENNReal NNReal MeasureTheory Topology
open MeasureTheory
open MeasureTheory Set NormedSpace
open scoped Topology
open Matrix Real
open scoped BigOperators Matrix.Norms.Frobenius
namespace SKGap.ComplexMatrix

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma opNorm_nonneg (M : Matrix ι ι ℂ) : 0 ≤ opNorm M := norm_nonneg _
lemma opNorm_add (M N : Matrix ι ι ℂ) : opNorm (M+N) ≤ opNorm M+opNorm N := by
  change ‖linEquiv (M+N)‖ ≤ _
  rw [(linEquiv (ι := ι)).map_add]
  exact norm_add_le _ _
lemma opNorm_sub (M N : Matrix ι ι ℂ) : opNorm (M-N) ≤ opNorm M+opNorm N := by
  change ‖lin (M-N)‖ ≤ _
  have hh : lin (M-N) = lin M-lin N := linEquiv.map_sub M N
  rw [hh]
  exact norm_sub_le _ _
lemma opNorm_mul (M N : Matrix ι ι ℂ) : opNorm (M*N) ≤ opNorm M*opNorm N := by
  change ‖lin (M*N)‖ ≤ _
  rw [lin_mul]
  exact norm_mul_le _ _
lemma opNorm_one_le : opNorm (1 : Matrix ι ι ℂ) ≤ 1 := by
  rw [opNorm,lin_one]
  exact ContinuousLinearMap.norm_id_le

lemma sandwich_frobenius (D E : Matrix ι ι ℂ) :
    ‖D*E*D‖ ≤ opNorm D^2*‖E‖ := by
  calc
    _ ≤ ‖D*E‖*opNorm D := frobenius_mul_le_opNorm_right _ _
    _ ≤ (opNorm D*‖E‖)*opNorm D := mul_le_mul_of_nonneg_right (frobenius_mul_le_opNorm _ _) (opNorm_nonneg _)
    _ = _ := by ring

lemma sandwich_opNorm (D E : Matrix ι ι ℂ) :
    opNorm (D*E*D) ≤ opNorm D^2*opNorm E := by
  calc
    _ ≤ opNorm (D*E)*opNorm D := opNorm_mul _ _
    _ ≤ (opNorm D*opNorm E)*opNorm D := mul_le_mul_of_nonneg_right (opNorm_mul _ _) (opNorm_nonneg _)
    _ = _ := by ring

end SKGap.ComplexMatrix

end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Localization_SandShift
attribute [-instance] _root_.OAI.SKGap.ComplexMatrix.frobeniusInnerProduct
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open MeasureTheory ProbabilityTheory InformationTheory Real Set
open scoped NNReal ENNReal
open Filter
open scoped Topology
noncomputable section
open Matrix Real
open scoped BigOperators Matrix.Norms.Frobenius ENNReal NNReal
noncomputable section
open Matrix Real
open scoped BigOperators Matrix.Norms.Frobenius NNReal
noncomputable section
open MeasureTheory ProbabilityTheory Real Set Filter
open MeasureTheory.Measure
open scoped ENNReal NNReal MeasureTheory Topology
open MeasureTheory
noncomputable section
noncomputable section
open MeasureTheory Set NormedSpace
open scoped Topology
noncomputable section
open Matrix Real
open scoped BigOperators Matrix.Norms.Frobenius
namespace SKGap.ComplexMatrix
open scoped FourierTransform SchwartzMap
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma sandShift_sub (B D M N : Matrix ι ι ℂ) :
    sandShift B D M-sandShift B D N = -(D*(M-N)*D) := by dsimp [sandShift]; noncomm_ring

lemma sandShift_lipschitz (B D M N : Matrix ι ι ℂ) :
    ‖sandShift B D M-sandShift B D N‖ ≤ opNorm D^2*‖M-N‖ := by
  rw [sandShift_sub,norm_neg]
  exact sandwich_frobenius _ _

lemma schwartzMatrix_sandShift_lipschitz (f : 𝓢(ℝ,ℂ)) (B D M N : Matrix ι ι ℂ)
    (hB : Bᴴ = B) (hD : Dᴴ = D) (hM : Mᴴ = M) (hN : Nᴴ = N) :
    ‖schwartzMatrix f (sandShift B D M)-schwartzMatrix f (sandShift B D N)‖ ≤
      (2*Real.pi*fourierMoment f 1)*opNorm D^2*‖M-N‖ := by
  exact (schwartzMatrix_lipschitz f _ _ (sandShift_hermitian _ _ _ hB hD hM)
    (sandShift_hermitian _ _ _ hB hD hN)).trans
    ((mul_le_mul_of_nonneg_left (sandShift_lipschitz B D M N)
      (by positivity [fourierMoment_nonneg f 1])).trans_eq (by ring))

end SKGap.ComplexMatrix

noncomputable section
open Set Real
open scoped Topology
namespace SKGap
section Projection
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

lemma convexProject_mem {K : Set E} (hK : ClosedConvexNonempty K) (x : E) :
    convexProject hK x ∈ K :=
  (Classical.choose_spec (exists_norm_eq_iInf_of_complete_convex hK.nonempty hK.complete hK.convex x)).1

lemma convexProject_minimal {K : Set E} (hK : ClosedConvexNonempty K) (x : E) :
    ‖x-convexProject hK x‖ = ⨅ y : K, ‖x-y‖ :=
  (Classical.choose_spec (exists_norm_eq_iInf_of_complete_convex hK.nonempty hK.complete hK.convex x)).2

lemma convexProject_inner {K : Set E} (hK : ClosedConvexNonempty K) (x : E)
    {y : E} (hy : y ∈ K) :
    inner ℝ (x-convexProject hK x) (y-convexProject hK x) ≤ 0 := by
  exact ((norm_eq_iInf_iff_real_inner_le_zero hK.convex (convexProject_mem hK x)).mp
    (convexProject_minimal hK x)) y hy

lemma convexProject_lipschitz {K : Set E} (hK : ClosedConvexNonempty K) :
    LipschitzWith 1 (convexProject hK) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  simp only [NNReal.coe_one,one_mul,dist_eq_norm]
  let p := convexProject hK x
  let q := convexProject hK y
  have hx := convexProject_inner hK x (convexProject_mem hK y)
  have hy := convexProject_inner hK y (convexProject_mem hK x)
  change inner ℝ (x-p) (q-p) ≤ 0 at hx
  change inner ℝ (y-q) (p-q) ≤ 0 at hy
  have hi : ‖p-q‖^2 ≤ inner ℝ (p-q) (x-y) := by
    rw [← real_inner_self_eq_norm_sq]
    simp only [inner_sub_left,inner_sub_right,real_inner_comm] at *
    nlinarith
  have hb := real_inner_le_norm (p-q) (x-y)
  nlinarith [norm_nonneg (p-q),norm_nonneg (x-y)]

lemma convexProject_eq_self {K : Set E} (hK : ClosedConvexNonempty K) {x : E}
    (hx : x ∈ K) : convexProject hK x = x := by
  have hh := convexProject_inner hK x hx
  rw [real_inner_self_eq_norm_sq] at hh
  have hz : ‖x-convexProject hK x‖ = 0 := by nlinarith [norm_nonneg (x-convexProject hK x)]
  exact (sub_eq_zero.mp (norm_eq_zero.mp hz)).symm

end Projection
end SKGap

end
end
end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Localization_Vectorize
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open MeasureTheory ProbabilityTheory InformationTheory Real Set
open scoped NNReal ENNReal
open Filter
open scoped Topology
noncomputable section
open Matrix Real
open scoped BigOperators Matrix.Norms.Frobenius ENNReal NNReal
noncomputable section
open Matrix Real
open scoped BigOperators Matrix.Norms.Frobenius NNReal
noncomputable section
open MeasureTheory ProbabilityTheory Real Set Filter
open MeasureTheory.Measure
open scoped ENNReal NNReal MeasureTheory Topology
open MeasureTheory
noncomputable section
noncomputable section
open MeasureTheory Set NormedSpace
open scoped Topology
noncomputable section
open Matrix Real
open scoped BigOperators Matrix.Norms.Frobenius
noncomputable section
open Set Real
open scoped Topology
namespace SKGap.ComplexMatrix
open Set
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma matrixProject_lipschitz (R : ℝ) (hR : 0 ≤ R) :
    LipschitzWith 1 (matrixProject (ι := ι) R hR) :=
  SKGap.convexProject_lipschitz _

lemma matrixProject_bound (R : ℝ) (hR : 0 ≤ R) (M : Matrix ι ι ℂ) :
    (matrixProject R hR M)ᴴ = matrixProject R hR M ∧ opNorm (matrixProject R hR M) ≤ R :=
  SKGap.convexProject_mem (hermitianBall_good (ι := ι) hR) M

lemma matrixProject_eq_self (R : ℝ) (hR : 0 ≤ R) (M : Matrix ι ι ℂ)
    (hM : Mᴴ = M) (hMR : opNorm M ≤ R) : matrixProject R hR M = M :=
  SKGap.convexProject_eq_self _ ⟨hM,hMR⟩

end SKGap.ComplexMatrix

namespace SKGap.ComplexMatrix
open scoped FourierTransform SchwartzMap
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma matrixProject_sub_norm (R : ℝ) (hR : 0 ≤ R) (M N : Matrix ι ι ℂ) :
    ‖matrixProject R hR M-matrixProject R hR N‖ ≤ ‖M-N‖ := by
  simpa only [dist_eq_norm,NNReal.coe_one,one_mul] using (matrixProject_lipschitz R hR).dist_le_mul M N

lemma truncatedG_opNorm (f : 𝓢(ℝ,ℂ)) (R : ℝ) (hR : 0 ≤ R) (B D M : Matrix ι ι ℂ)
    (hB : Bᴴ = B) (hD : Dᴴ = D) :
    opNorm (truncatedG f R hR B D M) ≤ opNorm D^2*fourierMoment f 0 := by
  have hS := sandShift_hermitian B D (matrixProject R hR M) hB hD (matrixProject_bound R hR M).1
  apply (sandwich_opNorm D _).trans
  apply mul_le_mul_of_nonneg_left _ (sq_nonneg _)
  simpa only [fourierMoment,pow_zero,mul_one] using schwartzMatrix_opNorm f _ hS

lemma truncatedG_sub_norm (f : 𝓢(ℝ,ℂ)) (R : ℝ) (hR : 0 ≤ R) (B D M N : Matrix ι ι ℂ)
    (hB : Bᴴ = B) (hD : Dᴴ = D) :
    ‖truncatedG f R hR B D M-truncatedG f R hR B D N‖ ≤
      (2*Real.pi*fourierMoment f 1)*opNorm D^4*‖M-N‖ := by
  have hL : 0 ≤ 2*Real.pi*fourierMoment f 1 := by have := fourierMoment_nonneg f 1; positivity
  have hM := (matrixProject_bound R hR M).1
  have hN := (matrixProject_bound R hR N).1
  have hl := schwartzMatrix_sandShift_lipschitz f B D (matrixProject R hR M) (matrixProject R hR N) hB hD hM hN
  have he : truncatedG f R hR B D M-truncatedG f R hR B D N =
      D*(schwartzMatrix f (sandShift B D (matrixProject R hR M))-
        schwartzMatrix f (sandShift B D (matrixProject R hR N)))*D := by dsimp [truncatedG]; noncomm_ring
  rw [he]
  calc
    _ ≤ opNorm D^2*‖schwartzMatrix f (sandShift B D (matrixProject R hR M))-
        schwartzMatrix f (sandShift B D (matrixProject R hR N))‖ := sandwich_frobenius _ _
    _ ≤ opNorm D^2*((2*Real.pi*fourierMoment f 1)*opNorm D^2*‖matrixProject R hR M-matrixProject R hR N‖) :=
      mul_le_mul_of_nonneg_left hl (sq_nonneg _)
    _ ≤ opNorm D^2*((2*Real.pi*fourierMoment f 1)*opNorm D^2*‖M-N‖) := by
      gcongr
      exact matrixProject_sub_norm _ _ _ _
    _ = _ := by ring

lemma truncatedG_eq_inverse (f : 𝓢(ℝ,ℂ)) {lo hi : ℝ} (hlo : 0 < lo)
    (hf : ∀ x ∈ Set.Icc lo hi, f x = (x : ℂ)⁻¹)
    (R : ℝ) (hR : 0 ≤ R) (B D M : Matrix ι ι ℂ) (hB : Bᴴ = B) (hD : Dᴴ = D)
    (hM : Mᴴ = M) (hMR : opNorm M ≤ R)
    (hspec : ∀ i, Matrix.IsHermitian.eigenvalues (sandShift_hermitian B D M hB hD hM) i ∈ Set.Icc lo hi) :
    truncatedG f R hR B D M = D*(sandShift B D M)⁻¹*D := by
  rw [truncatedG,matrixProject_eq_self R hR M hM hMR,
    schwartzMatrix_eq_inverse f hlo hf _ (sandShift_hermitian B D M hB hD hM) hspec]

end SKGap.ComplexMatrix

namespace SKGap.ComplexMatrix
open scoped SchwartzMap
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma diagonalChange_nonneg (D D' : Matrix ι ι ℂ) : 0 ≤ diagonalChange D D' := by
  unfold diagonalChange
  positivity [opNorm_nonneg D,opNorm_nonneg D',opNorm_nonneg (D-D')]
lemma shiftChange_nonneg {R : ℝ} (hR : 0 ≤ R) (B B' D D' : Matrix ι ι ℂ) :
    0 ≤ shiftChange R B B' D D' := by
  unfold shiftChange
  positivity [opNorm_nonneg (B-B'),diagonalChange_nonneg D D']
lemma g_constants_nonneg (f : 𝓢(ℝ,ℂ)) {R : ℝ} (hR : 0 ≤ R)
    (B B' D D' : Matrix ι ι ℂ) :
    0 ≤ gBound f D ∧ 0 ≤ gLip f D ∧ 0 ≤ gChange f R B B' D D' ∧ 0 ≤ gMixed f R B B' D D' := by
  have h₀ := fourierMoment_nonneg f 0
  have h₁ := (fl_nonneg f).1
  have h₂ := (fl_nonneg f).2
  have hd := diagonalChange_nonneg D D'
  have hs := shiftChange_nonneg hR B B' D D'
  unfold gBound gLip gChange gMixed
  exact ⟨by positivity,by positivity,by positivity,by positivity⟩

lemma projected_sub_bound {R : ℝ} (hR : 0 ≤ R) (M C : Matrix ι ι ℂ) :
    opNorm (matrixProject R hR M-C) ≤ R+opNorm C :=
  (opNorm_sub _ _).trans (add_le_add_left (matrixProject_bound R hR M).2 _)

lemma truncatedK_opNorm (f : 𝓢(ℝ,ℂ)) {R : ℝ} (hR : 0 ≤ R)
    (B D C M : Matrix ι ι ℂ) (hB : Bᴴ = B) (hD : Dᴴ = D) :
    opNorm (truncatedK f R hR B D C M) ≤ kBound f R D C := by
  apply (opNorm_add _ _).trans
  apply add_le_add opNorm_one_le
  exact (opNorm_mul _ _).trans
    (mul_le_mul (truncatedG_opNorm _ _ _ _ _ _ hB hD) (projected_sub_bound hR M C)
      (opNorm_nonneg _) (g_constants_nonneg f hR B B D D).1)

lemma truncatedK_sub_norm (f : 𝓢(ℝ,ℂ)) {R : ℝ} (hR : 0 ≤ R)
    (B D C M N : Matrix ι ι ℂ) (hB : Bᴴ = B) (hD : Dᴴ = D) :
    ‖truncatedK f R hR B D C M-truncatedK f R hR B D C N‖ ≤
      kLip f R D C*‖M-N‖ := by
  let G := truncatedG f R hR B D
  let P : Matrix ι ι ℂ → Matrix ι ι ℂ := matrixProject R hR
  have he : truncatedK f R hR B D C M-truncatedK f R hR B D C N =
      (G M-G N)*(P M-C)+G N*(P M-P N) := by dsimp [truncatedK,G,P]; noncomm_ring
  rw [he]
  calc
    _ ≤ ‖(G M-G N)*(P M-C)‖+‖G N*(P M-P N)‖ := norm_add_le _ _
    _ ≤ ‖G M-G N‖*opNorm (P M-C)+opNorm (G N)*‖P M-P N‖ :=
      add_le_add (frobenius_mul_le_opNorm_right _ _) (frobenius_mul_le_opNorm _ _)
    _ ≤ (gLip f D*‖M-N‖)*(R+opNorm C)+gBound f D*‖M-N‖ := by
      apply add_le_add
      · exact mul_le_mul (truncatedG_sub_norm _ _ _ _ _ _ _ hB hD) (projected_sub_bound hR M C)
          (opNorm_nonneg _) (mul_nonneg (g_constants_nonneg f hR B B D D).2.1 (norm_nonneg _))
      · exact mul_le_mul (truncatedG_opNorm _ _ _ _ _ _ hB hD) (matrixProject_sub_norm _ _ _ _)
          (norm_nonneg _) (g_constants_nonneg f hR B B D D).1
    _ = _ := by unfold kLip; ring

end SKGap.ComplexMatrix

end
end
end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Matrix_InverseSubSquareMul
attribute [-instance] _root_.OAI.SKGap.ComplexMatrix.frobeniusInnerProduct
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open MeasureTheory ProbabilityTheory InformationTheory Real Set
open scoped NNReal ENNReal
open Filter
open scoped Topology
noncomputable section
open Matrix Real
open scoped BigOperators Matrix.Norms.Frobenius ENNReal NNReal
noncomputable section
open Matrix Real
open scoped BigOperators Matrix.Norms.Frobenius NNReal
noncomputable section
open MeasureTheory ProbabilityTheory Real Set Filter
open MeasureTheory.Measure
open scoped ENNReal NNReal MeasureTheory Topology
open MeasureTheory
noncomputable section
noncomputable section
open MeasureTheory Set NormedSpace
open scoped Topology
noncomputable section
open Matrix Real
open scoped BigOperators Matrix.Norms.Frobenius
noncomputable section
open Set Real
open scoped Topology
noncomputable section
open Matrix Set Filter
open scoped Topology Matrix.Norms.Frobenius
noncomputable section
open Matrix NormedSpace ContinuousLinearMap
open scoped Matrix.Norms.Frobenius
noncomputable section
open Matrix
namespace SKGap.ResolventIdentity
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {𝕜 : Type*} [RCLike 𝕜]

lemma inverse_one_sub_square_mul (D V : Matrix ι ι 𝕜)
    (hS : IsUnit (1-D*V*D)) :
    (1-D*D*V)⁻¹ = 1+D*(1-D*V*D)⁻¹*D*V := by
  apply Matrix.inv_eq_right_inv
  have hSS : (1-D*V*D)*(1-D*V*D)⁻¹ = 1 :=
    Matrix.mul_nonsing_inv _ (((1-D*V*D).isUnit_iff_isUnit_det).mp hS)
  calc
    _ = (1-D*D*V)+D*((1-D*V*D)*(1-D*V*D)⁻¹)*D*V := by noncomm_ring
    _ = 1 := by rw [hSS]; noncomm_ring

lemma inverse_one_sub_square_mul_unit (D V : Matrix ι ι 𝕜)
    (hS : IsUnit (1-D*V*D)) : IsUnit (1-D*D*V) := by
  have hSS : (1-D*V*D)*(1-D*V*D)⁻¹ = 1 :=
    Matrix.mul_nonsing_inv _ (((1-D*V*D).isUnit_iff_isUnit_det).mp hS)
  apply ((1-D*D*V).isUnit_iff_isUnit_det).mpr
  have hh : (1-D*D*V)*(1+D*(1-D*V*D)⁻¹*D*V) = 1 := by
    calc
      _ = (1-D*D*V)+D*((1-D*V*D)*(1-D*V*D)⁻¹)*D*V := by noncomm_ring
      _ = 1 := by rw [hSS]; noncomm_ring
  exact Matrix.isUnit_det_of_right_inverse hh

end SKGap.ResolventIdentity

end
end
end
end
end
end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Localization_SandShiftSpecial
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open MeasureTheory ProbabilityTheory InformationTheory Real Set
open scoped NNReal ENNReal
open Filter
open scoped Topology
noncomputable section
open Matrix Real
open scoped BigOperators Matrix.Norms.Frobenius ENNReal NNReal
noncomputable section
open Matrix Real
open scoped BigOperators Matrix.Norms.Frobenius NNReal
noncomputable section
open MeasureTheory ProbabilityTheory Real Set Filter
open MeasureTheory.Measure
open scoped ENNReal NNReal MeasureTheory Topology
open MeasureTheory
noncomputable section
noncomputable section
open MeasureTheory Set NormedSpace
open scoped Topology
noncomputable section
open Matrix Real
open scoped BigOperators Matrix.Norms.Frobenius
noncomputable section
open Set Real
open scoped Topology
noncomputable section
open Matrix Set Filter
open scoped Topology Matrix.Norms.Frobenius
noncomputable section
open Matrix NormedSpace ContinuousLinearMap
open scoped Matrix.Norms.Frobenius
noncomputable section
open Matrix
namespace SKGap.ComplexMatrix
open scoped SchwartzMap ComplexOrder
open Set Filter
open scoped Topology
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma sandShift_special (D C M : Matrix ι ι ℂ) :
    sandShift (1+D*C*D) D M = 1-D*(M-C)*D := by
  dsimp [sandShift]; noncomm_ring

lemma truncatedK_eq_inverse (f : 𝓢(ℝ,ℂ)) {lo hi : ℝ} (hlo : 0 < lo)
    (hf : ∀ x ∈ Icc lo hi, f x = (x : ℂ)⁻¹)
    {R : ℝ} (hR : 0 ≤ R) (D C M : Matrix ι ι ℂ)
    (hD : Dᴴ = D) (hC : Cᴴ = C) (hM : Mᴴ = M) (hMR : opNorm M ≤ R)
    (hspec : ∀ i, Matrix.IsHermitian.eigenvalues (sandShift_hermitian (1+D*C*D) D M
      (by simp [Matrix.conjTranspose_mul,hD,hC,mul_assoc]) hD hM) i ∈ Icc lo hi) :
    truncatedK f R hR (1+D*C*D) D C M = (1-D*D*(M-C))⁻¹ := by
  have hB : (1+D*C*D)ᴴ = 1+D*C*D := by simp [Matrix.conjTranspose_mul,hD,hC,mul_assoc]
  have hS : IsUnit (sandShift (1+D*C*D) D M) :=
    ((Matrix.IsHermitian.posDef_iff_eigenvalues_pos (sandShift_hermitian _ _ _ hB hD hM)).mpr
      (fun i => hlo.trans_le (hspec i).1)).isUnit
  rw [truncatedK,truncatedG_eq_inverse f hlo hf R hR _ _ _ hB hD hM hMR hspec,
    matrixProject_eq_self R hR M hM hMR,sandShift_special]
  exact (SKGap.ResolventIdentity.inverse_one_sub_square_mul D (M-C) (by
    simpa only [sandShift_special] using hS)).symm

end SKGap.ComplexMatrix

end
end
end
end
end
end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Matrix_LiftMatrix
attribute [-instance] _root_.OAI.SKGap.ComplexMatrix.frobeniusInnerProduct
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open MeasureTheory ProbabilityTheory InformationTheory Real Set
open scoped NNReal ENNReal
open Filter
open scoped Topology
noncomputable section
open Matrix Real
open scoped BigOperators Matrix.Norms.Frobenius ENNReal NNReal
noncomputable section
open Matrix Real
open scoped BigOperators Matrix.Norms.Frobenius NNReal
noncomputable section
open MeasureTheory ProbabilityTheory Real Set Filter
open MeasureTheory.Measure
open scoped ENNReal NNReal MeasureTheory Topology
open MeasureTheory
noncomputable section
noncomputable section
open MeasureTheory Set NormedSpace
open scoped Topology
noncomputable section
open Matrix Real
open scoped BigOperators Matrix.Norms.Frobenius
noncomputable section
open Set Real
open scoped Topology
noncomputable section
open Matrix Set Filter
open scoped Topology Matrix.Norms.Frobenius
noncomputable section
open Matrix NormedSpace ContinuousLinearMap
open scoped Matrix.Norms.Frobenius
noncomputable section
open Matrix
namespace SKGap.RealComplex
open scoped Matrix.Norms.Frobenius
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in
lemma vec_norm_split (x : EuclideanSpace ℂ ι) :
    ‖x‖^2 = ‖reVec x‖^2+‖imVec x‖^2 := by
  simp only [EuclideanSpace.norm_sq_eq,← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  change ‖x i‖^2 = ‖(x i).re‖^2+‖(x i).im‖^2
  rw [Complex.sq_norm,Complex.normSq_apply]
  simp only [Real.norm_eq_abs]
  rw [sq_abs,sq_abs]
  ring

omit [DecidableEq ι] in
lemma norm_liftVec (x : EuclideanSpace ℝ ι) : ‖liftVec x‖ = ‖x‖ := by
  have hh : ‖liftVec x‖^2 = ‖x‖^2 := by simp [EuclideanSpace.norm_sq_eq,liftVec]
  nlinarith [norm_nonneg (liftVec x),norm_nonneg x]

lemma reVec_clin (M : Matrix ι ι ℝ) (x : EuclideanSpace ℂ ι) :
    reVec (clin (liftMatrix M) x) = rlin M (reVec x) := by
  ext i
  change (∑ j, (M i j : ℂ)*x j).re = ∑ j, M i j*(x j).re
  simp

lemma imVec_clin (M : Matrix ι ι ℝ) (x : EuclideanSpace ℂ ι) :
    imVec (clin (liftMatrix M) x) = rlin M (imVec x) := by
  ext i
  change (∑ j, (M i j : ℂ)*x j).im = ∑ j, M i j*(x j).im
  simp

lemma clin_liftVec (M : Matrix ι ι ℝ) (x : EuclideanSpace ℝ ι) :
    clin (liftMatrix M) (liftVec x) = liftVec (rlin M x) := by
  ext i
  change (∑ j, (M i j : ℂ)*(x j : ℂ)) = ((∑ j, M i j*x j : ℝ) : ℂ)
  simp

lemma operator_norm_lift (M : Matrix ι ι ℝ) : ‖clin (liftMatrix M)‖ = opNorm M := by
  apply le_antisymm
  · apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
    intro x
    apply nonneg_le_nonneg_of_sq_le_sq (mul_nonneg (norm_nonneg _) (norm_nonneg _))
    simp only [← sq]
    change ‖clin (liftMatrix M) x‖^2 ≤ (opNorm M*‖x‖)^2
    rw [vec_norm_split,reVec_clin,imVec_clin,mul_pow,vec_norm_split,mul_add]
    have hr := (rlin M).le_opNorm (reVec x)
    have hi := (rlin M).le_opNorm (imVec x)
    change ‖rlin M (reVec x)‖ ≤ opNorm M*‖reVec x‖ at hr
    change ‖rlin M (imVec x)‖ ≤ opNorm M*‖imVec x‖ at hi
    nlinarith [norm_nonneg (rlin M (reVec x)),norm_nonneg (rlin M (imVec x)),
      mul_nonneg (norm_nonneg (rlin M)) (norm_nonneg (reVec x)),
      mul_nonneg (norm_nonneg (rlin M)) (norm_nonneg (imVec x))]
  · apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
    intro x
    have hh := (clin (liftMatrix M)).le_opNorm (liftVec x)
    rwa [clin_liftVec,norm_liftVec,norm_liftVec] at hh

lemma norm_liftMatrix (M : Matrix ι ι ℝ) : ‖liftMatrix M‖ = ‖M‖ :=
  Matrix.frobenius_norm_map_eq M Complex.ofReal (fun x => by simp)

omit [Fintype ι] [DecidableEq ι] in
lemma liftMatrix_sub (M N : Matrix ι ι ℝ) :
    liftMatrix (M-N) = liftMatrix M-liftMatrix N := by ext i j; simp [liftMatrix]
omit [DecidableEq ι] in
lemma liftMatrix_mul (M N : Matrix ι ι ℝ) :
    liftMatrix (M*N) = liftMatrix M*liftMatrix N := by
  exact Matrix.map_mul (f := Complex.ofRealHom)
omit [Fintype ι] in
lemma liftMatrix_one : liftMatrix (1 : Matrix ι ι ℝ) = 1 :=
  Matrix.map_one Complex.ofReal (by simp) (by simp)
omit [Fintype ι] [DecidableEq ι] in
lemma liftMatrix_conjTranspose (M : Matrix ι ι ℝ) :
    (liftMatrix M)ᴴ = liftMatrix Mᵀ := by ext i j; simp [liftMatrix]
omit [Fintype ι] [DecidableEq ι] in
lemma liftMatrix_hermitian (M : Matrix ι ι ℝ) (hM : Mᵀ = M) :
    (liftMatrix M)ᴴ = liftMatrix M := by rw [liftMatrix_conjTranspose,hM]

end SKGap.RealComplex

end
end
end
end
end
end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Localization_RealPart
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open MeasureTheory ProbabilityTheory InformationTheory Real Set
open scoped NNReal ENNReal
open Filter
open scoped Topology
noncomputable section
open Matrix Real
open scoped BigOperators Matrix.Norms.Frobenius ENNReal NNReal
noncomputable section
open Matrix Real
open scoped BigOperators Matrix.Norms.Frobenius NNReal
noncomputable section
open MeasureTheory ProbabilityTheory Real Set Filter
open MeasureTheory.Measure
open scoped ENNReal NNReal MeasureTheory Topology
open MeasureTheory
noncomputable section
noncomputable section
open MeasureTheory Set NormedSpace
open scoped Topology
noncomputable section
open Matrix Real
open scoped BigOperators Matrix.Norms.Frobenius
noncomputable section
open Set Real
open scoped Topology
noncomputable section
open Matrix Set Filter
open scoped Topology Matrix.Norms.Frobenius
noncomputable section
open Matrix NormedSpace ContinuousLinearMap
open scoped Matrix.Norms.Frobenius
noncomputable section
open Matrix
namespace SKGap.RealComplex
open scoped Matrix.Norms.Frobenius
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma norm_realPart_le (M : Matrix ι ι ℂ) : ‖realPart M‖ ≤ ‖M‖ := by
  rw [Matrix.frobenius_norm_def,Matrix.frobenius_norm_def]
  apply Real.rpow_le_rpow (by positivity) _ (by norm_num)
  apply Finset.sum_le_sum
  intro i _
  apply Finset.sum_le_sum
  intro k _
  simp only [realPart,Matrix.map_apply,Real.rpow_two]
  exact pow_le_pow_left₀ (norm_nonneg _) (by simpa only [Real.norm_eq_abs] using Complex.abs_re_le_norm (M i k)) 2

omit [Fintype ι] [DecidableEq ι] in
lemma realPart_sub (M N : Matrix ι ι ℂ) : realPart (M-N) = realPart M-realPart N := by
  ext i k; simp [realPart]
omit [Fintype ι] [DecidableEq ι] in
lemma realPart_liftMatrix (M : Matrix ι ι ℝ) : realPart (liftMatrix M) = M := by
  ext i k; simp [realPart,liftMatrix]

lemma realPart_lipschitz : LipschitzWith 1 (realPart (ι := ι)) := by
  apply LipschitzWith.of_dist_le_mul
  intro M N
  simpa only [dist_eq_norm,NNReal.coe_one,one_mul,realPart_sub] using norm_realPart_le (M-N)

omit [DecidableEq ι] in
lemma reVec_norm_le (x : EuclideanSpace ℂ ι) : ‖reVec x‖ ≤ ‖x‖ := by
  have h := vec_norm_split x
  nlinarith [sq_nonneg ‖imVec x‖,norm_nonneg (reVec x),norm_nonneg x]

lemma realPart_operator (M : Matrix ι ι ℂ) (x : EuclideanSpace ℝ ι) :
    rlin (realPart M) x = reVec (clin M (liftVec x)) := by
  ext i
  change (∑ k, (M i k).re*x k) = (∑ k, M i k*(x k : ℂ)).re
  simp

lemma operator_realPart_le (M : Matrix ι ι ℂ) : opNorm (realPart M) ≤ ‖clin M‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
  intro x
  rw [realPart_operator]
  exact (reVec_norm_le _).trans ((clin M).le_opNorm (liftVec x) |>.trans_eq (by rw [norm_liftVec]))

lemma liftMatrix_inverse {M : Matrix ι ι ℝ} (hM : IsUnit M) :
    liftMatrix M⁻¹ = (liftMatrix M)⁻¹ := by
  symm
  apply Matrix.inv_eq_right_inv
  rw [← liftMatrix_mul,Matrix.mul_nonsing_inv M (M.isUnit_iff_isUnit_det.mp hM),liftMatrix_one]

end SKGap.RealComplex

namespace SKGap.RealComplex
open scoped Matrix.Norms.Frobenius SchwartzMap ComplexOrder
open SKGap.ComplexMatrix
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma liftMatrix_isUnit_iff (M : Matrix ι ι ℝ) : IsUnit (liftMatrix M) ↔ IsUnit M := by
  rw [(liftMatrix M).isUnit_iff_isUnit_det,M.isUnit_iff_isUnit_det,
    isUnit_iff_ne_zero,isUnit_iff_ne_zero]
  have he : (liftMatrix M).det = (M.det : ℂ) := (Complex.ofRealHom.map_det M).symm
  rw [he]
  exact not_congr Complex.ofReal_eq_zero

lemma realTruncatedK_sub_norm (f : 𝓢(ℝ,ℂ)) {R : ℝ} (hR : 0 ≤ R)
    (D C M N : Matrix ι ι ℝ) (hD : Dᵀ = D) (hC : Cᵀ = C) :
    ‖realTruncatedK f R hR D C M-realTruncatedK f R hR D C N‖ ≤
      kLip f R (liftMatrix D) (liftMatrix C)*‖M-N‖ := by
  have hD' := liftMatrix_hermitian D hD
  have hC' := liftMatrix_hermitian C hC
  have hB : (1+liftMatrix D*liftMatrix C*liftMatrix D)ᴴ =
      1+liftMatrix D*liftMatrix C*liftMatrix D := by simp [Matrix.conjTranspose_mul,hD',hC',mul_assoc]
  unfold realTruncatedK
  rw [← realPart_sub]
  apply (norm_realPart_le _).trans
  simpa only [← liftMatrix_sub,norm_liftMatrix] using
    truncatedK_sub_norm f hR _ _ _ (liftMatrix M) (liftMatrix N) hB hD'

lemma realTruncatedK_opNorm (f : 𝓢(ℝ,ℂ)) {R : ℝ} (hR : 0 ≤ R)
    (D C M : Matrix ι ι ℝ) (hD : Dᵀ = D) (hC : Cᵀ = C) :
    SKGap.opNorm (realTruncatedK f R hR D C M) ≤ kBound f R (liftMatrix D) (liftMatrix C) := by
  have hD' := liftMatrix_hermitian D hD
  have hC' := liftMatrix_hermitian C hC
  have hB : (1+liftMatrix D*liftMatrix C*liftMatrix D)ᴴ =
      1+liftMatrix D*liftMatrix C*liftMatrix D := by simp [Matrix.conjTranspose_mul,hD',hC',mul_assoc]
  exact (operator_realPart_le _).trans (truncatedK_opNorm f hR _ _ _ _ hB hD')

lemma realTruncatedK_eq_inverse (f : 𝓢(ℝ,ℂ)) {lo hi : ℝ} (hlo : 0 < lo)
    (hf : ∀ x ∈ Set.Icc lo hi, f x = (x : ℂ)⁻¹)
    {R : ℝ} (hR : 0 ≤ R) (D C M : Matrix ι ι ℝ)
    (hD : Dᵀ = D) (hC : Cᵀ = C) (hM : Mᵀ = M) (hMR : SKGap.opNorm M ≤ R)
    (hl : lo ≤ SKGap.ComplexSpectral.lowerRayleigh (liftMatrix (1-D*(M-C)*D)))
    (hu : -hi ≤ SKGap.ComplexSpectral.lowerRayleigh (-liftMatrix (1-D*(M-C)*D))) :
    realTruncatedK f R hR D C M = (1-D*D*(M-C))⁻¹ := by
  have hD' := liftMatrix_hermitian D hD
  have hC' := liftMatrix_hermitian C hC
  have hM' := liftMatrix_hermitian M hM
  have hB : (1+liftMatrix D*liftMatrix C*liftMatrix D)ᴴ =
      1+liftMatrix D*liftMatrix C*liftMatrix D := by simp [Matrix.conjTranspose_mul,hD',hC',mul_assoc]
  have hid : sandShift (1+liftMatrix D*liftMatrix C*liftMatrix D) (liftMatrix D) (liftMatrix M) =
      liftMatrix (1-D*(M-C)*D) := by
    rw [sandShift_special]; simp only [liftMatrix_sub,liftMatrix_mul,liftMatrix_one]
  have hS : (sandShift (1+liftMatrix D*liftMatrix C*liftMatrix D) (liftMatrix D) (liftMatrix M)).IsHermitian :=
    sandShift_hermitian _ _ _ hB hD' hM'
  have hspec : ∀ i, hS.eigenvalues i ∈ Set.Icc lo hi := by
    intro i
    have hm := SKGap.ComplexSpectral.eigenvalue_lower_bound hS i
    have hp := SKGap.ComplexSpectral.eigenvalue_upper_bound hS i
    have hl' : lo ≤ SKGap.ComplexSpectral.lowerRayleigh
        (sandShift (1+liftMatrix D*liftMatrix C*liftMatrix D) (liftMatrix D) (liftMatrix M)) := by
      simpa only [hid] using hl
    have hu' : -hi ≤ SKGap.ComplexSpectral.lowerRayleigh
        (-sandShift (1+liftMatrix D*liftMatrix C*liftMatrix D) (liftMatrix D) (liftMatrix M)) := by
      simpa only [hid] using hu
    constructor <;> linarith
  have hsunit : IsUnit (1-liftMatrix D*(liftMatrix M-liftMatrix C)*liftMatrix D) := by
    rw [← sandShift_special]
    exact (hS.posDef_iff_eigenvalues_pos.mpr (fun i => hlo.trans_le (hspec i).1)).isUnit
  have hrunit : IsUnit (1-D*D*(M-C)) := by
    apply (liftMatrix_isUnit_iff _).mp
    simpa only [liftMatrix_sub,liftMatrix_mul,liftMatrix_one] using
      SKGap.ResolventIdentity.inverse_one_sub_square_mul_unit (liftMatrix D) (liftMatrix M-liftMatrix C) hsunit
  unfold realTruncatedK
  rw [truncatedK_eq_inverse f hlo hf hR _ _ _ hD' hC' hM'
    (by simpa only [SKGap.ComplexMatrix.opNorm,SKGap.ComplexMatrix.lin,operator_norm_lift] using hMR) hspec]
  rw [← liftMatrix_one,← liftMatrix_mul,← liftMatrix_sub,← liftMatrix_mul,← liftMatrix_sub,
    ← liftMatrix_inverse hrunit,realPart_liftMatrix]

lemma continuous_realOpNorm : Continuous (SKGap.opNorm : Matrix ι ι ℝ → ℝ) := by
  have h : Continuous (fun M : Matrix ι ι ℝ => liftMatrix M) := by
    dsimp [liftMatrix]; fun_prop
  have hc := SKGap.ComplexMatrix.continuous_lin.norm.comp h
  simpa only [Function.comp_def,SKGap.ComplexMatrix.lin,operator_norm_lift] using hc

end SKGap.RealComplex

end
end
end
end
end
end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Matrix_LipschitzNormedConvolution
attribute [-instance] _root_.OAI.SKGap.ComplexMatrix.frobeniusInnerProduct
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open MeasureTheory ProbabilityTheory InformationTheory Real Set
open scoped NNReal ENNReal
open Filter
open scoped Topology
noncomputable section
open Matrix Real
open scoped BigOperators Matrix.Norms.Frobenius ENNReal NNReal
noncomputable section
open Matrix Real
open scoped BigOperators Matrix.Norms.Frobenius NNReal
noncomputable section
open MeasureTheory ProbabilityTheory Real Set Filter
open MeasureTheory.Measure
open scoped ENNReal NNReal MeasureTheory Topology
namespace SKGap

section StandardGaussian
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

theorem gaussian_integrable_lipschitz {μ : Measure E} [IsGaussian μ]
    {f : E → ℝ} {L : ℝ≥0} (hf : LipschitzWith L f) : Integrable f μ := by
  have hI := ((IsGaussian.integrable_id (μ := μ)).norm.const_mul (L : ℝ)).add
    (integrable_const |f 0|)
  apply hI.mono' hf.continuous.aestronglyMeasurable
  filter_upwards [] with x
  change |f x| ≤ (L : ℝ) * ‖x‖ + |f 0|
  have hh := hf.norm_sub_le x 0
  simp only [sub_zero, Real.norm_eq_abs] at hh ⊢
  have ht := abs_add_le (f x - f 0) (f 0)
  rw [sub_add_cancel] at ht
  linarith

end StandardGaussian

end SKGap
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Gaussian_GaussianProductIntegral
attribute [-instance] _root_.OAI.SKGap.ComplexMatrix.frobeniusInnerProduct
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open MeasureTheory ProbabilityTheory InformationTheory Real Set
open scoped NNReal ENNReal
open Filter
open scoped Topology
noncomputable section
open Matrix Real
open scoped BigOperators Matrix.Norms.Frobenius ENNReal NNReal
noncomputable section
open Matrix Real
open scoped BigOperators Matrix.Norms.Frobenius NNReal
noncomputable section
open MeasureTheory ProbabilityTheory Real Set Filter
open MeasureTheory.Measure
open scoped ENNReal NNReal MeasureTheory Topology
namespace SKGap
open MeasureTheory ProbabilityTheory Real
open scoped Topology
section ProductMoments
variable {κ : Type*} [Fintype κ]

lemma gaussianProduct_integrable_lipschitz {F : EuclideanSpace ℝ κ → ℝ}
    {L : ℝ≥0} (hF : LipschitzWith L F) :
    Integrable (fun g : κ → ℝ => F (WithLp.toLp 2 g))
      (Measure.pi (fun _ => gaussianReal 0 1)) := by
  have hi := gaussian_integrable_lipschitz (μ := stdGaussian (EuclideanSpace ℝ κ)) hF
  rw [← map_pi_eq_stdGaussian] at hi
  exact hi.comp_measurable (by fun_prop)

end ProductMoments
end SKGap

open MeasureTheory
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Localization_TruncationGoodSet
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open MeasureTheory ProbabilityTheory InformationTheory Real Set
open scoped NNReal ENNReal
open Filter
open scoped Topology
noncomputable section
open Matrix Real
open scoped BigOperators Matrix.Norms.Frobenius ENNReal NNReal
noncomputable section
open Matrix Real
open scoped BigOperators Matrix.Norms.Frobenius NNReal
noncomputable section
open MeasureTheory ProbabilityTheory Real Set Filter
open MeasureTheory.Measure
open scoped ENNReal NNReal MeasureTheory Topology
open MeasureTheory
noncomputable section
noncomputable section
open MeasureTheory Set NormedSpace
open scoped Topology
noncomputable section
open Matrix Real
open scoped BigOperators Matrix.Norms.Frobenius
noncomputable section
open Set Real
open scoped Topology
noncomputable section
open Matrix Set Filter
open scoped Topology Matrix.Norms.Frobenius
noncomputable section
open Matrix NormedSpace ContinuousLinearMap
open scoped Matrix.Norms.Frobenius
noncomputable section
open Matrix
namespace SKGap
open Matrix Real MeasureTheory ProbabilityTheory
open SKGap.RealComplex
open scoped BigOperators Matrix.Norms.Frobenius NNReal ENNReal SchwartzMap
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [Fintype ι] [DecidableEq ι] in
lemma goeMatrix_transpose (r : ℝ) (g : MatrixCoordinates ι → ℝ) :
    (goeMatrix r g)ᵀ = goeMatrix r g := by
  ext i k
  simp [goeMatrix,add_comm]

end SKGap

end
end
end
end
end
end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Brownian_PathBiasBase
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
namespace SKGap.ComplexMatrix
open Matrix
open scoped Matrix.Norms.Frobenius SchwartzMap
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma continuous_schwartzMatrix_comp {X : Type*} [TopologicalSpace X]
    (f : 𝓢(ℝ,ℂ)) {S : X → Matrix ι ι ℂ} (hS : Continuous S)
    (hh : ∀ x, (S x)ᴴ=S x) : Continuous (fun x => schwartzMatrix f (S x)) := by
  let H := {M : Matrix ι ι ℂ // Mᴴ=M}
  let : MetricSpace (Matrix ι ι ℂ) := Matrix.frobeniusNormedAddCommGroup.toMetricSpace
  let : MetricSpace H := MetricSpace.induced Subtype.val Subtype.val_injective inferInstance
  have hl : LipschitzWith (Real.toNNReal (2*Real.pi*fourierMoment f 1))
      (fun M : H => schwartzMatrix f M.1) := by
    apply LipschitzWith.of_dist_le_mul
    intro M N
    change dist (schwartzMatrix f M.1) (schwartzMatrix f N.1) ≤
      (Real.toNNReal (2*Real.pi*fourierMoment f 1) : ℝ) * dist M.1 N.1
    simp only [dist_eq_norm]
    exact (schwartzMatrix_lipschitz f M.1 N.1 M.2 N.2).trans
      (mul_le_mul_of_nonneg_right (Real.le_coe_toNNReal _) (norm_nonneg _))
  exact hl.continuous.comp (hS.subtype_mk hh)

lemma continuous_truncatedK_comp {X : Type*} [TopologicalSpace X]
    (f : 𝓢(ℝ,ℂ)) {R : ℝ} (hR : 0 ≤ R) {B D C M : X → Matrix ι ι ℂ}
    (hB : Continuous B) (hD : Continuous D) (hC : Continuous C) (hM : Continuous M)
    (hBh : ∀ x, (B x)ᴴ=B x) (hDh : ∀ x, (D x)ᴴ=D x) :
    Continuous (fun x => truncatedK f R hR (B x) (D x) (C x) (M x)) := by
  have hP := (matrixProject_lipschitz R hR).continuous.comp hM
  have hS : Continuous (fun x => sandShift (B x) (D x) (matrixProject R hR (M x))) := by
    unfold sandShift
    exact hB.sub ((hD.mul hP).mul hD)
  have hF := continuous_schwartzMatrix_comp f hS (fun x =>
    sandShift_hermitian _ _ _ (hBh x) (hDh x) (matrixProject_bound R hR (M x)).1)
  exact continuous_const.add (((hD.mul hF).mul hD).mul (hP.sub hC))

end SKGap.ComplexMatrix

namespace SKGap
open Matrix MeasureTheory ProbabilityTheory Real Set
open RealComplex
open scoped BigOperators Matrix.Norms.Frobenius SchwartzMap
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma continuous_realTruncatedK_comp {X : Type*} [TopologicalSpace X]
    (f : 𝓢(ℝ,ℂ)) {R : ℝ} (hR : 0 ≤ R) {D C M : X → Matrix ι ι ℝ}
    (hD : Continuous D) (hC : Continuous C) (hM : Continuous M)
    (hDh : ∀ x, (D x)ᵀ=D x) (hCh : ∀ x, (C x)ᵀ=C x) :
    Continuous (fun x => realTruncatedK f R hR (D x) (C x) (M x)) := by
  have hlift : Continuous (RealComplex.liftMatrix (ι := ι)) := by
    change Continuous (fun M : Matrix ι ι ℝ => M.map Complex.ofReal)
    fun_prop
  have hdl := hlift.comp hD
  have hcl := hlift.comp hC
  have hml := hlift.comp hM
  have hB : Continuous (fun x => (1 : Matrix ι ι ℂ) +
      liftMatrix (D x)*liftMatrix (C x)*liftMatrix (D x)) :=
    continuous_const.add ((hdl.mul hcl).mul hdl)
  have hh (x : X) : (1+liftMatrix (D x)*liftMatrix (C x)*liftMatrix (D x))ᴴ =
      1+liftMatrix (D x)*liftMatrix (C x)*liftMatrix (D x) := by
    simp only [Matrix.conjTranspose_add,Matrix.conjTranspose_one,Matrix.conjTranspose_mul,
      liftMatrix_hermitian (D x) (hDh x),liftMatrix_hermitian (C x) (hCh x),mul_assoc]
  exact realPart_lipschitz.continuous.comp (ComplexMatrix.continuous_truncatedK_comp
    f hR hB hdl hcl hml hh (fun x => liftMatrix_hermitian _ (hDh x)))

end SKGap

noncomputable section
open Real
namespace SKGap

lemma power_exponential_bound (k : ℕ) {c x : ℝ} (hc : 0 < c) (hx : 0 ≤ x) :
    x^k*Real.exp (-c*x) ≤ (k.factorial:ℝ)/c^k := by
  have hfac : (0:ℝ) < k.factorial := Nat.cast_pos.mpr (Nat.factorial_pos k)
  have h := (div_le_iff₀ hfac).mp (Real.pow_div_factorial_le_exp (c*x) (mul_nonneg hc.le hx) k)
  have hh := mul_le_mul_of_nonneg_right h (Real.exp_pos (-c*x)).le
  have he : Real.exp (c*x)*Real.exp (-c*x)=1 := by rw [← Real.exp_add]; ring_nf; exact Real.exp_zero
  have hr : (Real.exp (c*x)*(k.factorial:ℝ))*Real.exp (-c*x) = (k.factorial:ℝ) := by
    calc
      _ = (k.factorial:ℝ)*(Real.exp (c*x)*Real.exp (-c*x)) := by ring
      _ = _ := by rw [he,mul_one]
  rw [hr,mul_pow] at hh
  apply (le_div_iff₀ (pow_pos hc k)).mpr
  nlinarith only [hh]

lemma exponential_tail_absorptions {c n p : ℝ} (hc : 0 < c) (hn : 1 ≤ n)
    (hp : p ≤ 3*Real.exp (-c*n)) :
    p ≤ (3/c)/n ∧ (n^2+n)*p ≤ (36/c^3)/n ∧
      n*sqrt p ≤ (8*sqrt 3/c^2)/n := by
  have hn0 : 0 < n := zero_lt_one.trans_le hn
  have he1 : n*Real.exp (-c*n) ≤ 1/c := by
    simpa only [pow_one,Nat.factorial_one,Nat.cast_one] using power_exponential_bound 1 hc hn0.le
  have he3 : n^3*Real.exp (-c*n) ≤ 6/c^3 := by
    convert power_exponential_bound 3 hc hn0.le using 1
    all_goals try with_reducible_and_instances rfl
    norm_num
  have he2 : n^2*Real.exp (-(c/2)*n) ≤ 2/(c/2)^2 := by
    convert power_exponential_bound 2 (half_pos hc) hn0.le using 1
    all_goals try with_reducible_and_instances rfl
    norm_num
  have he : 0 ≤ Real.exp (-c*n) := (Real.exp_pos _).le
  refine ⟨?_,?_,?_⟩
  · apply (le_div_iff₀ hn0).mpr
    have hh := mul_le_mul_of_nonneg_right hp hn0.le
    have hx : (3:ℝ)/c=3*(1/c) := by ring
    rw [hx]
    nlinarith only [hh,he1]
  · apply (le_div_iff₀ hn0).mpr
    have hh := mul_le_mul_of_nonneg_right hp (show 0 ≤ (n^2+n)*n by positivity)
    have hnn : (n^2+n)*n ≤ 2*n^3 := by nlinarith [mul_nonneg hn0.le (sub_nonneg.mpr hn)]
    have hh' := mul_le_mul_of_nonneg_right hnn (show 0 ≤ 3*Real.exp (-c*n) by positivity)
    have hx : (36:ℝ)/c^3=6*(6/c^3) := by ring
    rw [hx]
    nlinarith only [hh,hh',he3]
  · have hs : sqrt p ≤ sqrt 3*Real.exp (-(c/2)*n) := by
      apply (sqrt_le_sqrt hp).trans_eq
      rw [sqrt_mul (by norm_num : (0:ℝ) ≤ 3)]
      congr 1
      rw [← Real.exp_half]
      congr 1
      ring
    apply (le_div_iff₀ hn0).mpr
    have hh := mul_le_mul_of_nonneg_left hs (sq_nonneg n)
    have hh' := mul_le_mul_of_nonneg_left he2 (sqrt_nonneg 3)
    have heq : sqrt 3*(2/(c/2)^2)=8*sqrt 3/c^2 := by field_simp; ring
    rw [heq] at hh'
    nlinarith only [hh,hh']

end SKGap

end
end
end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Matrix_OpNormDiagonal
attribute [-instance] _root_.OAI.SKGap.ComplexMatrix.frobeniusInnerProduct
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open MeasureTheory ProbabilityTheory InformationTheory Real Set
open scoped NNReal ENNReal
open Filter
open scoped Topology
noncomputable section
open Matrix Real
open scoped BigOperators Matrix.Norms.Frobenius ENNReal NNReal
noncomputable section
open Matrix Real
open scoped BigOperators Matrix.Norms.Frobenius NNReal
noncomputable section
open MeasureTheory ProbabilityTheory Real Set Filter
open MeasureTheory.Measure
open scoped ENNReal NNReal MeasureTheory Topology
open MeasureTheory
noncomputable section
noncomputable section
open MeasureTheory Set NormedSpace
open scoped Topology
noncomputable section
open Matrix Real
open scoped BigOperators Matrix.Norms.Frobenius
noncomputable section
open Set Real
open scoped Topology
noncomputable section
open Matrix Set Filter
open scoped Topology Matrix.Norms.Frobenius
noncomputable section
open Matrix NormedSpace ContinuousLinearMap
open scoped Matrix.Norms.Frobenius
noncomputable section
open Matrix
noncomputable section
open MeasureTheory ProbabilityTheory Real Set
open scoped ENNReal NNReal
noncomputable section
open MeasureTheory ProbabilityTheory InformationTheory Real Set
open scoped NNReal ENNReal
noncomputable section
open scoped BigOperators
open MeasureTheory ProbabilityTheory
open Real
noncomputable section
open scoped BigOperators Topology
open Filter Real
namespace SKGap
open Matrix Real
open scoped BigOperators Matrix.Norms.Frobenius
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma opNorm_diagonal_eq (d : ι → ℝ) : opNorm (diagonal d) = ‖d‖ :=
  Matrix.l2_opNorm_diagonal d

lemma opNorm_diagonal_le {d : ι → ℝ} {C : ℝ} (hC : 0 ≤ C) (hd : ∀ i, |d i| ≤ C) :
    opNorm (diagonal d) ≤ C := by
  rw [opNorm_diagonal_eq]
  exact (pi_norm_le_iff_of_nonneg hC).mpr (fun i => by simpa only [Real.norm_eq_abs] using hd i)

end SKGap

end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Brownian_PathDiagonal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open MeasureTheory ProbabilityTheory InformationTheory Real Set
open scoped NNReal ENNReal
open Filter
open scoped Topology
noncomputable section
open Matrix Real
open scoped BigOperators Matrix.Norms.Frobenius ENNReal NNReal
noncomputable section
open Matrix Real
open scoped BigOperators Matrix.Norms.Frobenius NNReal
noncomputable section
open MeasureTheory ProbabilityTheory Real Set Filter
open MeasureTheory.Measure
open scoped ENNReal NNReal MeasureTheory Topology
open MeasureTheory
noncomputable section
noncomputable section
open MeasureTheory Set NormedSpace
open scoped Topology
noncomputable section
open Matrix Real
open scoped BigOperators Matrix.Norms.Frobenius
noncomputable section
open Set Real
open scoped Topology
noncomputable section
open Matrix Set Filter
open scoped Topology Matrix.Norms.Frobenius
noncomputable section
open Matrix NormedSpace ContinuousLinearMap
open scoped Matrix.Norms.Frobenius
noncomputable section
open Matrix
noncomputable section
open MeasureTheory ProbabilityTheory Real Set
open scoped ENNReal NNReal
noncomputable section
open MeasureTheory ProbabilityTheory InformationTheory Real Set
open scoped NNReal ENNReal
noncomputable section
open scoped BigOperators
open MeasureTheory ProbabilityTheory
open Real
noncomputable section
open scoped BigOperators Topology
open Filter Real
namespace SKGap
open Matrix MeasureTheory ProbabilityTheory Real Set
open RealComplex ComplexSpectral
open scoped BigOperators Matrix.Norms.Frobenius
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma pathDiagonal_opNorm {a : ι → ℝ} {A z : ℝ} (_hA0 : 0 ≤ A)
    (hA : ∀ i, a i ≤ A) (hz : z ∈ Icc (0:ℝ) 1) :
    opNorm (pathDiagonal a z) ≤ sqrt A := by
  apply opNorm_diagonal_le (sqrt_nonneg _)
  intro i
  rw [abs_of_nonneg (mul_nonneg (sqrt_nonneg _) (sqrt_nonneg _))]
  have hz1 : sqrt z ≤ 1 := by simpa using sqrt_le_sqrt hz.2
  exact (mul_le_mul hz1 (sqrt_le_sqrt (hA i)) (sqrt_nonneg _) (by norm_num)).trans_eq (one_mul _)

lemma pathShift_opNorm {z q : ℝ} (hz : z ∈ Icc (0:ℝ) 1) (hq : 0 ≤ q) :
    opNorm (pathShift (ι := ι) z q) ≤ q := by
  apply opNorm_diagonal_le hq
  intro i
  rw [abs_of_nonneg (mul_nonneg hz.1 hq)]
  exact (mul_le_mul_of_nonneg_right hz.2 hq).trans_eq (one_mul _)

variable [Nonempty ι]
omit [DecidableEq ι] in
lemma diagonal_mean_bounds {j A : ℝ} {a : ι → ℝ} (hj : 0 ≤ j)
    (ha : ∀ i, 0 ≤ a i) (hA : ∀ i, a i ≤ A) :
    0 ≤ (j/(Fintype.card ι:ℝ))*∑ i, a i ∧
    (j/(Fintype.card ι:ℝ))*∑ i, a i ≤ j*A := by
  have hn : (0:ℝ)<Fintype.card ι := Nat.cast_pos.mpr Fintype.card_pos
  refine ⟨mul_nonneg (div_nonneg hj hn.le) (Finset.sum_nonneg (fun i _ => ha i)),?_⟩
  have hs : (∑ i, a i) ≤ (Fintype.card ι:ℝ)*A := by
    simpa using Finset.sum_le_sum (s := Finset.univ) (fun i _ => hA i)
  calc
    _ ≤ (j/(Fintype.card ι:ℝ))*((Fintype.card ι:ℝ)*A) :=
      mul_le_mul_of_nonneg_left hs (div_nonneg hj hn.le)
    _ = _ := by field_simp

end SKGap

namespace SKGap
open Matrix MeasureTheory ProbabilityTheory Real Set
open RealComplex
open scoped BigOperators Matrix.Norms.Frobenius NNReal ENNReal SchwartzMap
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma path_constants_bound (f : 𝓢(ℝ,ℂ)) {R j A z q : ℝ} {a : ι → ℝ}
    (hR : 0 ≤ R) (_hj : 0 ≤ j) (hA0 : 0 ≤ A) (hA : ∀ i, a i ≤ A)
    (hq : 0 ≤ q) (hqA : q ≤ j*A) (hz : z ∈ Icc (0:ℝ) 1) :
    ComplexMatrix.kBound f R (liftMatrix (pathDiagonal a z)) (liftMatrix (pathShift z q)) ≤ pathBound f R j A ∧
    ComplexMatrix.kLip f R (liftMatrix (pathDiagonal a z)) (liftMatrix (pathShift z q)) ≤ pathLip f R j A ∧
    opNorm (pathDiagonal a z*pathDiagonal a z) ≤ A := by
  have hd := pathDiagonal_opNorm hA0 hA hz
  have hc := (pathShift_opNorm (ι := ι) hz hq).trans hqA
  have hd2 : opNorm (pathDiagonal a z)^2 ≤ A := by
    have hh := pow_le_pow_left₀ (show 0 ≤ opNorm (pathDiagonal a z) from norm_nonneg _) hd 2
    rwa [sq_sqrt hA0] at hh
  have hd4 : opNorm (pathDiagonal a z)^4 ≤ A^2 := by
    calc
      _ = (opNorm (pathDiagonal a z)^2)^2 := by ring
      _ ≤ _ := pow_le_pow_left₀ (sq_nonneg _) hd2 2
  have h₀ := ComplexMatrix.fourierMoment_nonneg f 0
  have h₁ := (ComplexMatrix.fl_nonneg f).1
  have hc0 : 0 ≤ R+opNorm (pathShift (ι := ι) z q) := add_nonneg hR (norm_nonneg _)
  unfold ComplexMatrix.kBound ComplexMatrix.kLip ComplexMatrix.gBound ComplexMatrix.gLip pathBound pathLip
  simp only [ComplexMatrix.opNorm,ComplexMatrix.lin,operator_norm_lift]
  refine ⟨?_,?_,?_⟩
  · gcongr
  · gcongr
  · exact (opNorm_mul _ _).trans (by nlinarith)

end SKGap

end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Gaussian_GaussianCoordinateMemLp
attribute [-instance] _root_.OAI.SKGap.ComplexMatrix.frobeniusInnerProduct
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open MeasureTheory ProbabilityTheory InformationTheory Real Set
open scoped NNReal ENNReal
open Filter
open scoped Topology
noncomputable section
open Matrix Real
open scoped BigOperators Matrix.Norms.Frobenius ENNReal NNReal
noncomputable section
open Matrix Real
open scoped BigOperators Matrix.Norms.Frobenius NNReal
noncomputable section
open MeasureTheory ProbabilityTheory Real Set Filter
open MeasureTheory.Measure
open scoped ENNReal NNReal MeasureTheory Topology
open MeasureTheory
noncomputable section
noncomputable section
open MeasureTheory Set NormedSpace
open scoped Topology
noncomputable section
open Matrix Real
open scoped BigOperators Matrix.Norms.Frobenius
noncomputable section
open Set Real
open scoped Topology
noncomputable section
open Matrix Set Filter
open scoped Topology Matrix.Norms.Frobenius
noncomputable section
open Matrix NormedSpace ContinuousLinearMap
open scoped Matrix.Norms.Frobenius
noncomputable section
open Matrix
namespace SKGap
open MeasureTheory ProbabilityTheory Real
open scoped ENNReal NNReal
variable {ι : Type*} [Fintype ι]

lemma gaussianCoordinate_memLp (a : MatrixCoordinates ι) :
    MemLp (fun g : MatrixCoordinates ι → ℝ => g a) 2
      (Measure.pi (fun _ => gaussianReal 0 1)) := by
  exact (IsGaussian.memLp_id (gaussianReal 0 1) 2 (by norm_num)).comp_measurePreserving
    (measurePreserving_eval (fun _ : MatrixCoordinates ι => gaussianReal 0 1) a)

lemma gaussianCoordinate_integral_sq (a : MatrixCoordinates ι) :
    (∫ g : MatrixCoordinates ι → ℝ, (g a)^2 ∂Measure.pi (fun _ => gaussianReal 0 1)) = 1 := by
  rw [integral_comp_eval (μ := fun _ : MatrixCoordinates ι => gaussianReal 0 1) (i := a) (by fun_prop : AEStronglyMeasurable (fun x : ℝ => x^2) (gaussianReal 0 1))]
  have hh := variance_fun_id_gaussianReal (μ := 0) (v := 1)
  rw [variance_eq_integral (by fun_prop),integral_id_gaussianReal] at hh
  simpa only [sub_zero,NNReal.coe_one] using hh

lemma goeEntry_memLp (r : ℝ) (i b : ι) :
    MemLp (fun g => goeMatrix r g i b) 2
      (Measure.pi (fun _ : MatrixCoordinates ι => gaussianReal 0 1)) := by
  exact ((gaussianCoordinate_memLp (.inl (i,b))).add
    (gaussianCoordinate_memLp (.inl (b,i)))).const_mul _

lemma goeEntry_integral_sq_le {r : ℝ} (hr : 0 ≤ r) (i b : ι) :
    (∫ g, (goeMatrix r g i b)^2
      ∂Measure.pi (fun _ : MatrixCoordinates ι => gaussianReal 0 1)) ≤ 2*r := by
  let μ := Measure.pi (fun _ : MatrixCoordinates ι => gaussianReal 0 1)
  have h1 := (gaussianCoordinate_memLp (.inl (i,b))).integrable_sq
  have h2 := (gaussianCoordinate_memLp (.inl (b,i))).integrable_sq
  have hb (g : MatrixCoordinates ι → ℝ) : (goeMatrix r g i b)^2 ≤
      r*((g (.inl (i,b)))^2+(g (.inl (b,i)))^2) := by
    have hx : (g (.inl (i,b))+g (.inl (b,i)))^2 ≤
        2*((g (.inl (i,b)))^2+(g (.inl (b,i)))^2) := by
      nlinarith only [sq_nonneg (g (.inl (i,b))-g (.inl (b,i)))]
    simp only [goeMatrix,mul_pow]
    calc
      _ ≤ (sqrt (2*r)/2)^2*(2*((g (.inl (i,b)))^2+(g (.inl (b,i)))^2)) :=
        mul_le_mul_of_nonneg_left hx (sq_nonneg _)
      _ = _ := by rw [div_pow,sq_sqrt (by positivity)]; ring
  calc
    _ ≤ ∫ g, r*((g (.inl (i,b)))^2+(g (.inl (b,i)))^2) ∂μ :=
      integral_mono (goeEntry_memLp r i b).integrable_sq ((h1.add h2).const_mul r) hb
    _ = 2*r := by
      rw [integral_const_mul,integral_add h1 h2,gaussianCoordinate_integral_sq,
        gaussianCoordinate_integral_sq]
      ring

end SKGap

end
end
end
end
end
end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Localization_IntegralAbsSet
attribute [-instance] _root_.OAI.SKGap.ComplexMatrix.frobeniusInnerProduct
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open MeasureTheory ProbabilityTheory InformationTheory Real Set
open scoped NNReal ENNReal
open Filter
open scoped Topology
noncomputable section
open Matrix Real
open scoped BigOperators Matrix.Norms.Frobenius ENNReal NNReal
noncomputable section
open Matrix Real
open scoped BigOperators Matrix.Norms.Frobenius NNReal
noncomputable section
open MeasureTheory ProbabilityTheory Real Set Filter
open MeasureTheory.Measure
open scoped ENNReal NNReal MeasureTheory Topology
open MeasureTheory
noncomputable section
noncomputable section
open MeasureTheory Set NormedSpace
open scoped Topology
noncomputable section
open Matrix Real
open scoped BigOperators Matrix.Norms.Frobenius
noncomputable section
open Set Real
open scoped Topology
noncomputable section
open Matrix Set Filter
open scoped Topology Matrix.Norms.Frobenius
noncomputable section
open Matrix NormedSpace ContinuousLinearMap
open scoped Matrix.Norms.Frobenius
noncomputable section
open Matrix
noncomputable section
open MeasureTheory ProbabilityTheory Real Set
open scoped ENNReal NNReal
namespace SKGap
variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

lemma integral_abs_on_set_le {F : Ω → ℝ} (hF : MemLp F 2 μ)
    {s : Set Ω} (hs : MeasurableSet s) :
    (∫ x in s, |F x| ∂μ) ≤ sqrt (∫ x, (F x)^2 ∂μ)*sqrt (μ.real s) := by
  have hG : MemLp (s.indicator (fun _ : Ω => (1:ℝ))) 2 μ :=
    memLp_indicator_const 2 hs 1 (Or.inr (measure_ne_top _ _))
  have hh := integral_mul_norm_le_Lp_mul_Lq Real.HolderConjugate.two_two
    (by simpa using hF) (by simpa using hG)
  have he : (fun x => ‖F x‖*‖s.indicator (fun _ : Ω => (1:ℝ)) x‖) =
      s.indicator (fun x => |F x|) := by
    funext x
    by_cases hx : x ∈ s <;> simp [hx,Real.norm_eq_abs]
  have hg : (fun x => ‖s.indicator (fun _ : Ω => (1:ℝ)) x‖^(2:ℝ)) =
      s.indicator (fun _ : Ω => (1:ℝ)) := by
    funext x
    by_cases hx : x ∈ s <;> simp [hx]
  rw [he,hg,integral_indicator hs,integral_indicator hs] at hh
  simpa only [Real.rpow_two,Real.norm_eq_abs,sq_abs,← Real.sqrt_eq_rpow,
    integral_const,smul_eq_mul,mul_one,measureReal_restrict_apply_univ] using hh

end SKGap

end
end
end
end
end
end
end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Brownian_PathExpectation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section

namespace SKGap
open Matrix MeasureTheory ProbabilityTheory Real Set Filter
open RealComplex
open scoped BigOperators Matrix.Norms.Frobenius NNReal ENNReal SchwartzMap Topology

lemma pathRate_pos {j A : ℝ} (hj : 0 < j) (hA : 0 < A) (hs : sqrt j*A < 1) :
    0 < pathRate j A := by
  have hh : 0 < 1-sqrt j*A := sub_pos.mpr hs
  unfold pathRate
  exact lt_min (by positivity) (by positivity)

lemma path_size_eventually {j A : ℝ} (hs : sqrt j*A < 1) :
    ∀ᶠ n : ℕ in atTop,
      2*sqrt A*sqrt (sqrt (2*j^2*A^2/(n:ℝ))) ≤ (1-sqrt j*A)^2/4 := by
  have hgap : 0 < (1-sqrt j*A)^2/4 := by
    have hh := sub_pos.mpr hs
    positivity
  have ht : Tendsto (fun n : ℕ => 2*sqrt A*sqrt (sqrt (2*j^2*A^2/(n:ℝ)))) atTop (𝓝 0) := by
    have hh := ((tendsto_const_div_atTop_nhds_zero_nat (2*j^2*A^2)).sqrt.sqrt).const_mul (2*sqrt A)
    simpa only [sqrt_zero,mul_zero] using hh
  exact (ht.eventually (gt_mem_nhds hgap)).mono (fun _ h => h.le)

end SKGap
end
end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Localization_ProjectedReal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
namespace SKGap
open Matrix MeasureTheory ProbabilityTheory Real
open RealComplex
open scoped BigOperators Matrix.Norms.Frobenius NNReal ENNReal SchwartzMap
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma realProject_opNorm {R : ℝ} (hR : 0 ≤ R) (M : Matrix ι ι ℝ) :
    opNorm (realProject R hR M) ≤ R :=
  (operator_realPart_le _).trans (ComplexMatrix.matrixProject_bound R hR (liftMatrix M)).2

lemma realProject_sub_norm {R : ℝ} (hR : 0 ≤ R) (M N : Matrix ι ι ℝ) :
    ‖realProject R hR M-realProject R hR N‖ ≤ ‖M-N‖ := by
  unfold realProject
  rw [← realPart_sub]
  apply (norm_realPart_le _).trans
  simpa only [← liftMatrix_sub,norm_liftMatrix] using
    ComplexMatrix.matrixProject_sub_norm R hR (liftMatrix M) (liftMatrix N)

lemma realProject_eq_self {R : ℝ} (hR : 0 ≤ R) (M : Matrix ι ι ℝ)
    (hM : Mᵀ=M) (hMR : opNorm M ≤ R) : realProject R hR M=M := by
  unfold realProject
  rw [ComplexMatrix.matrixProject_eq_self R hR (liftMatrix M) (liftMatrix_hermitian M hM)
    (by simpa only [ComplexMatrix.opNorm,ComplexMatrix.lin,operator_norm_lift] using hMR)]
  ext i k
  simp [RealComplex.realPart,liftMatrix]

lemma realProject_lipschitz {R : ℝ} (hR : 0 ≤ R) :
    LipschitzWith 1 (realProject (ι := ι) R hR) := by
  apply LipschitzWith.of_dist_le_mul
  intro M N
  simpa only [dist_eq_norm,NNReal.coe_one,one_mul] using realProject_sub_norm hR M N

lemma realProjectedProduct_opNorm {R B : ℝ} (hR : 0 ≤ R)
    (K : Matrix ι ι ℝ → Matrix ι ι ℝ) (hK : ∀ M, opNorm (K M) ≤ B) (M : Matrix ι ι ℝ) :
    opNorm (realProject R hR M*K M) ≤ R*B := by
  apply (opNorm_mul _ _).trans
  exact mul_le_mul (realProject_opNorm hR M) (hK M) (norm_nonneg _) hR

end SKGap
end
end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Brownian_PathCutoff
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
namespace SKGap
open Matrix MeasureTheory ProbabilityTheory Real Set Filter
open RealComplex
open scoped BigOperators Matrix.Norms.Frobenius NNReal ENNReal SchwartzMap Topology
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma pathK_bounds [Nonempty ι] (f : 𝓢(ℝ,ℂ)) {R j A z : ℝ} (hR : 0 ≤ R) (hj : 0 ≤ j)
    (hA : 0 ≤ A) {a : ι → ℝ} (ha : ∀ i, 0 ≤ a i) (haA : ∀ i, a i ≤ A)
    (hz : z ∈ Icc (0:ℝ) 1) :
    (∀ M, opNorm (pathK f R hR j a z M) ≤ pathBound f R j A) ∧
    (∀ M N, ‖pathK f R hR j a z M-pathK f R hR j a z N‖ ≤ pathLip f R j A*‖M-N‖) := by
  have hq := diagonal_mean_bounds hj ha haA
  have hc := path_constants_bound f hR hj hA haA hq.1 hq.2 hz
  constructor
  · intro M
    exact (realTruncatedK_opNorm f hR _ _ M (diagonal_transpose _) (diagonal_transpose _)).trans hc.1
  · intro M N
    exact (realTruncatedK_sub_norm f hR _ _ M N (diagonal_transpose _) (diagonal_transpose _)).trans
      (mul_le_mul_of_nonneg_right hc.2.1 (norm_nonneg _))

lemma pathK_continuous [Nonempty ι] (f : 𝓢(ℝ,ℂ)) {R j A z : ℝ} (hR : 0 ≤ R) (hj : 0 ≤ j)
    (hA : 0 ≤ A) {a : ι → ℝ} (ha : ∀ i, 0 ≤ a i) (haA : ∀ i, a i ≤ A)
    (hz : z ∈ Icc (0:ℝ) 1) : Continuous (pathK f R hR j a z) := by
  apply LipschitzWith.continuous (K := ⟨pathLip f R j A,(path_constants_nonneg f hR hj hA).2⟩)
  apply LipschitzWith.of_dist_le_mul
  intro M N
  change ‖pathK f R hR j a z M-pathK f R hR j a z N‖ ≤ pathLip f R j A*‖M-N‖
  exact (pathK_bounds f hR hj hA ha haA hz).2 M N

end SKGap
end
end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Brownian_PathAgreement
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
namespace SKGap
open Matrix Real MeasureTheory ProbabilityTheory
open RealComplex
open scoped BigOperators Matrix.Norms.Frobenius NNReal ENNReal SchwartzMap ComplexOrder
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma symmetric_isUnit_of_lower [Nonempty ι] (S : Matrix ι ι ℝ) (hS : Sᵀ=S)
    {lo : ℝ} (hlo : 0 < lo) (hl : lo ≤ ComplexSpectral.lowerRayleigh (liftMatrix S)) : IsUnit S := by
  apply (liftMatrix_isUnit_iff S).mp
  have hh : (liftMatrix S).IsHermitian := liftMatrix_hermitian S hS
  exact (hh.posDef_iff_eigenvalues_pos.mpr (fun i => hlo.trans_le
    (hl.trans (ComplexSpectral.eigenvalue_lower_bound hh i)))).isUnit

end SKGap
end
end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Brownian_LogDetPath
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
namespace SKGap
open Matrix MeasureTheory ProbabilityTheory Real Set
open RealComplex
open scoped BigOperators Matrix.Norms.Frobenius SchwartzMap
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma pathDiagonal_square_at {a : ι → ℝ} (ha : ∀ i, 0 ≤ a i) {z : ℝ} (hz : 0 ≤ z) :
    pathDiagonal a z*pathDiagonal a z=z • diagonal a := by
  simp only [pathDiagonal,diagonal_mul_diagonal]
  ext i k
  by_cases hik : i=k
  · subst k
    simp only [diagonal_apply_eq,Matrix.smul_apply,smul_eq_mul]
    rw [mul_mul_mul_comm,mul_self_sqrt hz,mul_self_sqrt (ha i)]
  · simp [hik]

omit [Fintype ι] in
lemma pathShift_eq (z q : ℝ) : pathShift (ι := ι) z q=(z*q) • 1 := by
  ext i k
  by_cases hik : i=k <;> simp [pathShift,hik]

lemma logPath_eq {a : ι → ℝ} (ha : ∀ i, 0 ≤ a i) {z : ℝ} (hz : 0 ≤ z)
    (q : ℝ) (M : Matrix ι ι ℝ) :
    logPath q a M z=1-pathDiagonal a z*pathDiagonal a z*(M-pathShift z q) := by
  rw [pathDiagonal_square_at ha hz,pathShift_eq]
  simp only [logPath,mul_sub,Matrix.smul_mul,Matrix.mul_smul,mul_one,smul_smul]
  module

lemma hasDerivAt_logPath (q : ℝ) (a : ι → ℝ) (M : Matrix ι ι ℝ) (z : ℝ) (i k : ι) :
    HasDerivAt (fun t => logPath q a M t i k)
      (((2*z*q) • diagonal a-diagonal a*M) i k) z := by
  have hh := (((hasDerivAt_pow 2 z).mul_const q).mul_const (diagonal a i k)).const_add ((1:Matrix ι ι ℝ) i k)
  have h := hh.sub ((hasDerivAt_id z).mul_const ((diagonal a*M) i k))
  convert h using 1 <;> try rfl
  simp only [Nat.cast_ofNat,show 2-1=1 by rfl,pow_one,one_mul,Matrix.sub_apply,Matrix.smul_apply,smul_eq_mul]

lemma pathK_agrees_at [Nonempty ι] (f : 𝓢(ℝ,ℂ)) {lo hi : ℝ} (hlo : 0 < lo)
    (hf : ∀ x ∈ Icc lo hi, f x=(x:ℂ)⁻¹) {R : ℝ} (hR : 0 ≤ R)
    (j : ℝ) {a : ι → ℝ} (ha : ∀ i, 0 ≤ a i) {z : ℝ} (hz : 0 ≤ z)
    (M : Matrix ι ι ℝ) (hM : Mᵀ=M) (hMR : opNorm M ≤ R)
    (hl : lo ≤ ComplexSpectral.lowerRayleigh (liftMatrix
      (1-pathDiagonal a z*(M-pathShift z ((j/(Fintype.card ι:ℝ))*∑ b,a b))*pathDiagonal a z)))
    (hu : -hi ≤ ComplexSpectral.lowerRayleigh (-liftMatrix
      (1-pathDiagonal a z*(M-pathShift z ((j/(Fintype.card ι:ℝ))*∑ b,a b))*pathDiagonal a z))) :
    IsUnit (logPath ((j/(Fintype.card ι:ℝ))*∑ b,a b) a M z) ∧
    pathK f R hR j a z M=(logPath ((j/(Fintype.card ι:ℝ))*∑ b,a b) a M z)⁻¹ := by
  have hsym : (1-pathDiagonal a z*(M-pathShift z ((j/(Fintype.card ι:ℝ))*∑ b,a b))*pathDiagonal a z)ᵀ=
      1-pathDiagonal a z*(M-pathShift z ((j/(Fintype.card ι:ℝ))*∑ b,a b))*pathDiagonal a z := by
    simp only [transpose_sub,transpose_one,transpose_mul,hM,
      show (pathDiagonal a z)ᵀ=pathDiagonal a z from diagonal_transpose _,
      show (pathShift z ((j/(Fintype.card ι:ℝ))*∑ b,a b))ᵀ=pathShift z ((j/(Fintype.card ι:ℝ))*∑ b,a b) from diagonal_transpose _,mul_assoc]
  have hS := symmetric_isUnit_of_lower _ hsym hlo hl
  constructor
  · rw [logPath_eq ha hz]
    exact ResolventIdentity.inverse_one_sub_square_mul_unit _ _ hS
  · change realTruncatedK f R hR _ _ M=_
    rw [logPath_eq ha hz]
    exact realTruncatedK_eq_inverse f hlo hf hR _ _ M
      (diagonal_transpose _) (diagonal_transpose _) hM hMR hl hu

lemma logPath_trace_derivative (q z : ℝ) (a : ι → ℝ) (M K : Matrix ι ι ℝ) :
    (((2*z*q) • diagonal a-diagonal a*M)*K).trace=
      2*z*q*(K*diagonal a).trace-(M*K*diagonal a).trace := by
  rw [sub_mul,Matrix.smul_mul,Matrix.trace_sub,Matrix.trace_smul,smul_eq_mul,
    Matrix.trace_mul_comm (diagonal a) K,mul_assoc (diagonal a) M K,
    Matrix.trace_mul_comm (diagonal a) (M*K)]

lemma continuous_logPathCutoffDerivative (f : 𝓢(ℝ,ℂ)) {R : ℝ} (hR : 0 ≤ R)
    (j : ℝ) (a : ι → ℝ) :
    Continuous (fun p : ℝ × Matrix ι ι ℝ => logPathCutoffDerivative f R hR j a p.2 p.1) := by
  have hc : Continuous (fun p : ℝ × Matrix ι ι ℝ => pathK f R hR j a p.1 p.2) := by
    apply continuous_realTruncatedK_comp
    · dsimp [pathDiagonal]; fun_prop
    · dsimp [pathShift]; fun_prop
    · exact continuous_snd
    · intro p; exact diagonal_transpose _
    · intro p; exact diagonal_transpose _
  have hp : Continuous (fun p : ℝ × Matrix ι ι ℝ => realProject R hR p.2) :=
    (realProject_lipschitz hR).continuous.comp continuous_snd
  unfold logPathCutoffDerivative
  exact ((continuous_const.mul continuous_fst |>.mul continuous_const).mul
      ((hc.mul continuous_const).matrix_trace)).sub
      (((hp.mul hc).mul continuous_const).matrix_trace) |>.div_const _
end SKGap
end
end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Localization_BoundedIntervalFubini
attribute [-instance] _root_.OAI.SKGap.ComplexMatrix.frobeniusInnerProduct
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
namespace SKGap
open MeasureTheory Real Set
lemma interval_product_integrable {Ω : Type*} [TopologicalSpace Ω] [MeasurableSpace Ω]
    [BorelSpace Ω] [SecondCountableTopology Ω] {μ : Measure Ω} [IsFiniteMeasure μ]
    {B : ℝ × Ω → ℝ} (hB : Continuous B) {D : ℝ}
    (hb : ∀ t ∈ Icc (0:ℝ) 1, ∀ g, |B (t,g)| ≤ D) :
    Integrable B ((volume.restrict (Ioc (0:ℝ) 1)).prod μ) := by
  apply Integrable.of_bound hB.aestronglyMeasurable D
  apply (Measure.ae_prod_iff_ae_ae (measurableSet_le hB.norm.measurable measurable_const)).mpr
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
  exact ae_of_all _ (fun g => by simpa only [Real.norm_eq_abs] using hb t ⟨ht.1.le,ht.2⟩ g)

lemma bounded_interval_mean {Ω : Type*} [TopologicalSpace Ω] [MeasurableSpace Ω]
    [BorelSpace Ω] [SecondCountableTopology Ω] {μ : Measure Ω} [IsFiniteMeasure μ]
    {B : ℝ × Ω → ℝ} (hB : Continuous B) {D c ε : ℝ}
    (hb : ∀ t ∈ Icc (0:ℝ) 1, ∀ g, |B (t,g)| ≤ D)
    (hm : ∀ t ∈ Icc (0:ℝ) 1, |(∫ g, B (t,g) ∂μ)-t*c| ≤ ε) :
    Integrable (fun g => ∫ t in (0:ℝ)..1, B (t,g)) μ ∧
    |(∫ g, (∫ t in (0:ℝ)..1, B (t,g)) ∂μ)-c/2| ≤ ε := by
  have hi := interval_product_integrable (μ := μ) hB hb
  have hi' : Integrable (Function.uncurry (fun t g => B (t,g)))
      ((volume.restrict (uIoc (0:ℝ) 1)).prod μ) := by
    have he : Function.uncurry (fun t g => B (t,g)) = B := by
      funext x; rcases x with ⟨t,g⟩; rfl
    rw [he,uIoc_of_le (by norm_num : (0:ℝ)≤1)]
    exact hi
  constructor
  · simpa only [intervalIntegral.integral_of_le (by norm_num : (0:ℝ)≤1)] using hi.integral_prod_right
  · rw [← intervalIntegral_integral_swap hi']
    have hit : IntervalIntegrable (fun t => ∫ g, B (t,g) ∂μ) volume 0 1 := by
      rw [intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num : (0:ℝ)≤1)]
      exact hi.integral_prod_left
    have hid : IntervalIntegrable (fun t : ℝ => t*c) volume 0 1 := (continuous_id.mul_const c).intervalIntegrable 0 1
    have hc : (∫ t in (0:ℝ)..1, t*c)=c/2 := by rw [intervalIntegral.integral_mul_const,integral_id]; ring
    rw [← hc,← intervalIntegral.integral_sub hit hid]
    have hh := intervalIntegral.norm_integral_le_of_norm_le_const (a := (0:ℝ)) (b := 1)
      (f := fun t => (∫ g, B (t,g) ∂μ)-t*c) (C := ε) (fun t ht => by
        have ht' : t ∈ Ioc (0:ℝ) 1 := by simpa only [uIoc_of_le (by norm_num : (0:ℝ)≤1)] using ht
        simpa only [Real.norm_eq_abs] using hm t ⟨ht'.1.le,ht'.2⟩)
    simpa using hh
end SKGap
end
end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Matrix_MatrixLogDet
attribute [-instance] _root_.OAI.SKGap.ComplexMatrix.frobeniusInnerProduct
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
namespace SKGap.LogDet
open Matrix
open scoped BigOperators
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma hasDerivAt_det_update {Q : ℝ → Matrix ι ι ℝ} {Q' : Matrix ι ι ℝ} {t : ℝ}
    (hQ : ∀ i k, HasDerivAt (fun x => Q x i k) (Q' i k) t) :
    HasDerivAt (fun x => (Q x).det) (∑ i, ((Q t).updateRow i (Q' i)).det) t := by
  have hrow (i : ι) : HasDerivAt (fun x => Q x i) (Q' i) t := hasDerivAt_pi.mpr (hQ i)
  have h := (HasFDerivAt.multilinear_comp (f := detMultilinear (ι := ι))
    (fun i => (hrow i).hasFDerivAt)).hasDerivAt
  convert h using 1 <;> try rfl
  simp only [_root_.sum_apply,ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.toSpanSingleton_apply,one_smul,
    ContinuousMultilinearMap.toContinuousLinearMap_apply]
  rfl

lemma det_updateRow_trace (M H : Matrix ι ι ℝ) :
    (∑ i, (M.updateRow i (H i)).det)= (H*M.adjugate).trace := by
  simp only [Matrix.trace,Matrix.diag,Matrix.mul_apply]
  apply Finset.sum_congr rfl
  intro i _
  rw [← Matrix.cramer_transpose_apply,Matrix.cramer_eq_adjugate_mulVec,
    ← Matrix.adjugate_transpose]
  simp only [Matrix.mulVec,Matrix.transpose_apply,dotProduct]
  apply Finset.sum_congr rfl
  intro k _
  ring

lemma hasDerivAt_det_adjugate {Q : ℝ → Matrix ι ι ℝ} {Q' : Matrix ι ι ℝ} {t : ℝ}
    (hQ : ∀ i k, HasDerivAt (fun x => Q x i k) (Q' i k) t) :
    HasDerivAt (fun x => (Q x).det) (Q'*(Q t).adjugate).trace t := by
  simpa only [det_updateRow_trace] using hasDerivAt_det_update hQ

lemma adjugate_eq_det_smul_inv (M : Matrix ι ι ℝ) (hM : IsUnit M) :
    M.adjugate=M.det • M⁻¹ := by
  have hd : M.det ≠ 0 := (Matrix.isUnit_iff_isUnit_det M).mp hM |>.ne_zero
  rw [Matrix.inv_def,Ring.inverse_eq_inv,smul_smul,mul_inv_cancel₀ hd,one_smul]

lemma hasDerivAt_det {Q : ℝ → Matrix ι ι ℝ} {Q' : Matrix ι ι ℝ} {t : ℝ}
    (hQ : ∀ i k, HasDerivAt (fun x => Q x i k) (Q' i k) t) (hunit : IsUnit (Q t)) :
    HasDerivAt (fun x => (Q x).det) ((Q t).det*(Q'*(Q t)⁻¹).trace) t := by
  have h := hasDerivAt_det_adjugate hQ
  rw [adjugate_eq_det_smul_inv _ hunit,Matrix.mul_smul,Matrix.trace_smul,smul_eq_mul] at h
  exact h

lemma hasDerivAt_logdet {Q : ℝ → Matrix ι ι ℝ} {Q' : Matrix ι ι ℝ} {t : ℝ}
    (hQ : ∀ i k, HasDerivAt (fun x => Q x i k) (Q' i k) t) (hunit : IsUnit (Q t)) :
    HasDerivAt (fun x => Real.log (Q x).det) (Q'*(Q t)⁻¹).trace t := by
  have hd : (Q t).det ≠ 0 := (Matrix.isUnit_iff_isUnit_det _).mp hunit |>.ne_zero
  have h := (hasDerivAt_det hQ hunit).log hd
  convert h using 1
  all_goals try with_reducible_and_instances rfl
  field_simp
end SKGap.LogDet
end
end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Matrix_RegularizedLogDet
attribute [-instance] _root_.OAI.SKGap.ComplexMatrix.frobeniusInnerProduct
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
namespace SKGap.LogDet
open Matrix Real
open scoped BigOperators Matrix.Norms.Frobenius
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma regularizedGram_posDef {γ : ℝ} (hγ : 0 < γ) (M : Matrix ι ι ℝ) :
    (regularizedGram γ M).PosDef := by
  exact Matrix.PosDef.posSemidef_add (by simpa using Matrix.posSemidef_conjTranspose_mul_self M)
    (Matrix.PosDef.one.smul hγ)

lemma regularizedGram_transpose (γ : ℝ) (M : Matrix ι ι ℝ) :
    (regularizedGram γ M)ᵀ=regularizedGram γ M := by
  simp [regularizedGram]

lemma frobenius_sq_trace (M : Matrix ι ι ℝ) : ‖M‖^2=(Mᵀ*M).trace := by
  rw [SKGap.frobenius_sq]
  simp only [Matrix.trace,Matrix.diag,Matrix.mul_apply,Matrix.transpose_apply]
  rw [Finset.sum_comm]
  simp only [sq]

lemma trace_inner_abs (M H : Matrix ι ι ℝ) : |(Mᵀ*H).trace| ≤ ‖M‖*‖H‖ := by
  have hc := Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset (ι×ι))
    (fun p => M p.1 p.2) (fun p => H p.1 p.2)
  simp only [Fintype.sum_prod_type] at hc
  have ht : (Mᵀ*H).trace=∑ i,∑ k,M i k*H i k := by
    simp only [Matrix.trace,Matrix.diag,Matrix.mul_apply,Matrix.transpose_apply]
    exact Finset.sum_comm
  rw [ht]
  apply nonneg_le_nonneg_of_sq_le_sq (mul_nonneg (norm_nonneg _) (norm_nonneg _))
  simpa only [← sq,sq_abs,mul_pow,SKGap.frobenius_sq] using hc

lemma regularized_resolvent_square {γ : ℝ} (hγ : 0 < γ) (M : Matrix ι ι ℝ) :
    let Q := regularizedGram γ M
    (1-(2*γ) • Q⁻¹)ᵀ*(1-(2*γ) • Q⁻¹)=1-(4*γ) • ((M*Q⁻¹)ᵀ*(M*Q⁻¹)) := by
  dsimp only
  let Q := regularizedGram γ M
  have hQ := regularizedGram_posDef hγ M |>.isUnit
  have hi : Q⁻¹*Q=1 := Matrix.nonsing_inv_mul Q ((Matrix.isUnit_iff_isUnit_det _).mp hQ)
  have ht : (Q⁻¹)ᵀ=Q⁻¹ := by rw [Matrix.transpose_nonsing_inv,regularizedGram_transpose]
  have he : Q⁻¹*(Mᵀ*M)*Q⁻¹=Q⁻¹-γ • (Q⁻¹*Q⁻¹) := by
    have h := congrArg (fun X : Matrix ι ι ℝ => X*Q⁻¹) hi
    dsimp only [Q,regularizedGram] at h ⊢
    simp only [mul_add,Matrix.mul_smul,mul_one,add_mul,Matrix.smul_mul,one_mul] at h
    exact eq_sub_of_add_eq h
  change (1-(2*γ) • Q⁻¹)ᵀ*(1-(2*γ) • Q⁻¹)=1-(4*γ) • ((M*Q⁻¹)ᵀ*(M*Q⁻¹))
  simp only [Matrix.transpose_sub,Matrix.transpose_one,Matrix.transpose_smul,ht,
    Matrix.transpose_mul,one_sub_mul,mul_sub,mul_one,Matrix.smul_mul,Matrix.mul_smul,smul_smul]
  have he' : Q⁻¹*Mᵀ*(M*Q⁻¹)=Q⁻¹-γ • (Q⁻¹*Q⁻¹) := by simpa only [mul_assoc] using he
  rw [he',smul_sub,smul_smul]
  module

lemma regularized_resolvent_frobenius {γ : ℝ} (hγ : 0 < γ) (M : Matrix ι ι ℝ) :
    4*γ*‖M*(regularizedGram γ M)⁻¹‖^2 ≤ (Fintype.card ι:ℝ) := by
  have hp := Matrix.posSemidef_conjTranspose_mul_self
    (1-(2*γ) • (regularizedGram γ M)⁻¹)
  have ht := hp.trace_nonneg
  rw [Matrix.conjTranspose_eq_transpose_of_trivial] at ht
  rw [regularized_resolvent_square hγ M,Matrix.trace_sub,Matrix.trace_smul,
    Matrix.trace_one,smul_eq_mul,← frobenius_sq_trace] at ht
  linarith

lemma hasDerivAt_regularizedGram (γ : ℝ) (M H : Matrix ι ι ℝ) (t : ℝ) (i k : ι) :
    HasDerivAt (fun s : ℝ => regularizedGram γ (M+s • H) i k)
      ((Hᵀ*(M+t • H)+(M+t • H)ᵀ*H) i k) t := by
  have h (a b : ι) : HasDerivAt (fun s : ℝ => (M+s • H) a b) (H a b) t := by
    convert ((hasDerivAt_id t).mul_const (H a b)).const_add (M a b) using 1 <;> first | rfl | simp
  have hh := (HasDerivAt.fun_sum (u := Finset.univ) (fun l _ => (h l i).mul (h l k))).add_const ((γ • (1:Matrix ι ι ℝ)) i k)
  convert hh using 1 <;> try rfl
  simp only [Matrix.add_apply,Matrix.mul_apply,Matrix.transpose_apply,Finset.sum_add_distrib]

lemma trace_regularized_derivative (M H K : Matrix ι ι ℝ) (hK : Kᵀ=K) :
    ((Hᵀ*M+Mᵀ*H)*K).trace=2*((M*K)ᵀ*H).trace := by
  rw [add_mul,Matrix.trace_add]
  have h₁ : (Hᵀ*M*K).trace=((M*K)ᵀ*H).trace := by
    rw [← Matrix.trace_transpose (Hᵀ*M*K)]
    simp only [Matrix.transpose_mul,Matrix.transpose_transpose,hK,mul_assoc]
  have h₂ : (Mᵀ*H*K).trace=((M*K)ᵀ*H).trace := by
    rw [Matrix.trace_mul_cycle]
    simp only [Matrix.transpose_mul,hK]
  rw [h₁,h₂]
  ring

lemma hasDerivAt_regularizedLogDet (γ : ℝ) (hγ : 0 < γ) (M H : Matrix ι ι ℝ) (t : ℝ) :
    HasDerivAt (fun s : ℝ => regularizedLogDet γ (M+s • H))
      (2*(((M+t • H)*(regularizedGram γ (M+t • H))⁻¹)ᵀ*H).trace/(Fintype.card ι:ℝ)) t := by
  have hh := (hasDerivAt_logdet (hasDerivAt_regularizedGram γ M H t)
    (regularizedGram_posDef hγ (M+t • H)).isUnit).div_const (Fintype.card ι:ℝ)
  rw [trace_regularized_derivative] at hh
  · exact hh
  · rw [Matrix.transpose_nonsing_inv,regularizedGram_transpose]

lemma regularized_gradient_bound [Nonempty ι] {γ : ℝ} (hγ : 0 < γ) (M : Matrix ι ι ℝ) :
    2*‖M*(regularizedGram γ M)⁻¹‖/(Fintype.card ι:ℝ) ≤ 1/sqrt ((Fintype.card ι:ℝ)*γ) := by
  have hn : (0:ℝ) < Fintype.card ι := Nat.cast_pos.mpr Fintype.card_pos
  have hg : 0 < (Fintype.card ι:ℝ)*γ := mul_pos hn hγ
  apply (div_le_div_iff₀ hn (sqrt_pos.mpr hg)).mpr
  rw [one_mul]
  apply nonneg_le_nonneg_of_sq_le_sq hn.le
  simpa only [← sq,mul_pow,sq_sqrt hg.le] using
    (show (2*‖M*(regularizedGram γ M)⁻¹‖)^2*((Fintype.card ι:ℝ)*γ) ≤ (Fintype.card ι:ℝ)^2 by
      have hh := mul_le_mul_of_nonneg_left (regularized_resolvent_frobenius hγ M) hn.le
      nlinarith only [hh])

lemma regularized_derivative_bound [Nonempty ι] {γ : ℝ} (hγ : 0 < γ) (M H : Matrix ι ι ℝ) :
    |2*((M*(regularizedGram γ M)⁻¹)ᵀ*H).trace/(Fintype.card ι:ℝ)| ≤
      1/sqrt ((Fintype.card ι:ℝ)*γ)*‖H‖ := by
  have hn : (0:ℝ) < Fintype.card ι := Nat.cast_pos.mpr Fintype.card_pos
  rw [abs_div,abs_mul,abs_of_pos hn,abs_of_pos (by norm_num : (0:ℝ)<2)]
  calc
    _ ≤ 2*(‖M*(regularizedGram γ M)⁻¹‖*‖H‖)/(Fintype.card ι:ℝ) := by
      gcongr
      exact trace_inner_abs _ _
    _ = (2*‖M*(regularizedGram γ M)⁻¹‖/(Fintype.card ι:ℝ))*‖H‖ := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_right (regularized_gradient_bound hγ M) (norm_nonneg _)

theorem regularizedLogDet_lipschitz [Nonempty ι] {γ : ℝ} (hγ : 0 < γ)
    (M N : Matrix ι ι ℝ) :
    |regularizedLogDet γ M-regularizedLogDet γ N| ≤
      1/sqrt ((Fintype.card ι:ℝ)*γ)*‖M-N‖ := by
  have hh := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    (s := Set.univ) (f := fun t : ℝ => regularizedLogDet γ (N+t • (M-N)))
    (f' := fun t => 2*(((N+t • (M-N))*(regularizedGram γ (N+t • (M-N)))⁻¹)ᵀ*(M-N)).trace/(Fintype.card ι:ℝ))
    (fun t _ => (hasDerivAt_regularizedLogDet γ hγ N (M-N) t).hasDerivWithinAt)
    (fun t _ => by simpa only [Real.norm_eq_abs] using regularized_derivative_bound hγ (N+t • (M-N)) (M-N))
    (convex_univ) (Set.mem_univ (0:ℝ)) (Set.mem_univ (1:ℝ))
  simpa only [one_smul,zero_smul,add_zero,add_sub_cancel,sub_zero,norm_one,mul_one,Real.norm_eq_abs] using hh
end SKGap.LogDet
end
end

section
noncomputable section
namespace SKGap.LogDet
open Matrix Real
open scoped BigOperators Matrix.Norms.Frobenius
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma logdet_le_trace_sub_card {M : Matrix ι ι ℝ} (hM : M.PosDef) :
    log M.det ≤ M.trace-(Fintype.card ι:ℝ) := by
  rw [hM.isHermitian.det_eq_prod_eigenvalues,hM.isHermitian.trace_eq_sum_eigenvalues]
  simp only [RCLike.ofReal_real_eq_id, id_eq]
  rw [Real.log_prod (fun i _ => ne_of_gt (hM.eigenvalues_pos i))]
  have ht := Finset.sum_le_sum (s := Finset.univ) (fun i _ => Real.log_le_sub_one_of_pos (hM.eigenvalues_pos i))
  simpa using ht

lemma regularized_factorization (γ : ℝ) (M : Matrix ι ι ℝ) (hM : IsUnit M) :
    regularizedGram γ M=Mᵀ*(1+γ • (M⁻¹ᵀ*M⁻¹))*M := by
  have hi := (Matrix.isUnit_iff_isUnit_det M).mp hM
  have h₁ := Matrix.nonsing_inv_mul M hi
  have h₂ : Mᵀ*M⁻¹ᵀ=1 := by rw [← Matrix.transpose_mul,h₁,transpose_one]
  unfold regularizedGram
  simp only [mul_add,add_mul,mul_one,Matrix.mul_smul,Matrix.smul_mul]
  rw [← mul_assoc Mᵀ M⁻¹ᵀ,h₂,one_mul,h₁]

lemma regularizedLogDet_le_logdet {γ : ℝ} (hγ : 0 ≤ γ) (M : Matrix ι ι ℝ) (hM : IsUnit M) :
    regularizedLogDet γ M ≤ 2*log M.det/(Fintype.card ι:ℝ)+
      γ*‖M⁻¹‖^2/(Fintype.card ι:ℝ) := by
  let Q := 1+γ • (M⁻¹ᵀ*M⁻¹)
  have hQ : Q.PosDef := Matrix.PosDef.one.add_posSemidef (by
    simpa using (Matrix.posSemidef_conjTranspose_mul_self M⁻¹).smul hγ)
  have hd : M.det ≠ 0 := (Matrix.isUnit_iff_isUnit_det M).mp hM |>.ne_zero
  have hn : (0:ℝ) ≤ Fintype.card ι := Nat.cast_nonneg _
  have hl : log (regularizedGram γ M).det=2*log M.det+log Q.det := by
    rw [regularized_factorization γ M hM,Matrix.det_mul,Matrix.det_mul,Matrix.det_transpose,
      Real.log_mul (mul_ne_zero hd hQ.det_pos.ne') hd,Real.log_mul hd hQ.det_pos.ne']
    ring
  have ht := logdet_le_trace_sub_card hQ
  have hQt : Q.trace-(Fintype.card ι:ℝ)=γ*‖M⁻¹‖^2 := by
    dsimp only [Q]
    rw [Matrix.trace_add,Matrix.trace_one,Matrix.trace_smul,smul_eq_mul,← frobenius_sq_trace]
    ring
  rw [hQt] at ht
  unfold regularizedLogDet
  rw [hl,add_div]
  exact add_le_add_right (div_le_div_of_nonneg_right ht hn) _

lemma frobenius_le_sqrt_card_opNorm (M : Matrix ι ι ℝ) :
    ‖M‖ ≤ sqrt (Fintype.card ι:ℝ)*opNorm M := by
  have hh := SKGap.frobenius_mul_le_opNorm_right (1:Matrix ι ι ℝ) M
  have h1 : ‖(1:Matrix ι ι ℝ)‖=sqrt (Fintype.card ι:ℝ) := by
    have hs := frobenius_sq_trace (1:Matrix ι ι ℝ)
    simp only [transpose_one,one_mul,Matrix.trace_one] at hs
    nlinarith [norm_nonneg (1:Matrix ι ι ℝ),sqrt_nonneg (Fintype.card ι:ℝ),sq_sqrt (Nat.cast_nonneg (Fintype.card ι))]
  simpa only [one_mul,h1] using hh

lemma regularizedLogDet_le_logdet_opNorm [Nonempty ι] {γ B : ℝ} (hγ : 0 ≤ γ)
    (M : Matrix ι ι ℝ) (hM : IsUnit M) (hB : opNorm M⁻¹ ≤ B) :
    regularizedLogDet γ M ≤ 2*log M.det/(Fintype.card ι:ℝ)+γ*B^2 := by
  have hn : (0:ℝ) < Fintype.card ι := Nat.cast_pos.mpr Fintype.card_pos
  have hb0 : 0 ≤ B := (norm_nonneg _).trans hB
  apply (regularizedLogDet_le_logdet hγ M hM).trans
  apply add_le_add_right
  apply (div_le_iff₀ hn).mpr
  have hf := (frobenius_le_sqrt_card_opNorm M⁻¹).trans (mul_le_mul_of_nonneg_left hB (sqrt_nonneg _))
  have hsq := sq_le_sq₀ (norm_nonneg _) (mul_nonneg (sqrt_nonneg _) hb0) |>.mpr hf
  rw [mul_pow,sq_sqrt hn.le] at hsq
  nlinarith [mul_le_mul_of_nonneg_left hsq hγ]

lemma regularizedLogDet_zero [Nonempty ι] {γ : ℝ} (_hγ : 0 < γ) :
    regularizedLogDet γ (0:Matrix ι ι ℝ)=log γ := by
  have hn : (Fintype.card ι:ℝ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  simp only [regularizedLogDet,regularizedGram,transpose_zero,zero_mul,zero_add,
    Matrix.det_smul,Matrix.det_one,mul_one,Real.log_pow]
  exact mul_div_cancel_left₀ _ hn

lemma regularizedLogDet_abs [Nonempty ι] {γ : ℝ} (hγ : 0 < γ) (M : Matrix ι ι ℝ) :
    |regularizedLogDet γ M| ≤ |log γ|+‖M‖/sqrt ((Fintype.card ι:ℝ)*γ) := by
  have hh := regularizedLogDet_lipschitz hγ M 0
  rw [sub_zero,regularizedLogDet_zero hγ] at hh
  have ht := (show |regularizedLogDet γ M| ≤ |regularizedLogDet γ M-log γ|+|log γ| by
    simpa only [sub_add_cancel] using abs_add_le (regularizedLogDet γ M-log γ) (log γ)).trans (add_le_add_left hh _)
  simpa only [div_eq_mul_inv,one_mul,mul_comm,add_comm] using ht
end SKGap.LogDet
end
end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Matrix_LogDetIntegral
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
namespace SKGap
open Matrix MeasureTheory ProbabilityTheory Real Set
open RealComplex
open scoped BigOperators Matrix.Norms.Frobenius SchwartzMap
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma logPathGood_isClosed (R lo hi q : ℝ) (a : ι → ℝ) :
    IsClosed (logPathGood R lo hi q a) := by
  have hc (z : ℝ) : Continuous (fun M : Matrix ι ι ℝ => liftMatrix (1-pathDiagonal a z*(M-pathShift z q)*pathDiagonal a z)) := by
    dsimp only [liftMatrix]; fun_prop
  have hl (z : ℝ) := isClosed_le (continuous_const (y := lo)) (ComplexSpectral.continuous_lowerRayleigh.comp (hc z))
  have hu (z : ℝ) := isClosed_le (continuous_const (y := -hi)) (ComplexSpectral.continuous_lowerRayleigh.comp (hc z).neg)
  change IsClosed ({M | opNorm M ≤ R} ∩ {M | ∀ z ∈ Icc (0:ℝ) 1, _})
  apply (isClosed_le continuous_realOpNorm continuous_const).inter
  simp only [ofPred_forall]
  exact isClosed_iInter (fun z => isClosed_iInter (fun _ => (hl z).inter (hu z)))

lemma logdetPath_integral [Nonempty ι] (f : 𝓢(ℝ,ℂ)) {lo hi : ℝ} (hlo : 0 < lo)
    (hf : ∀ x ∈ Icc lo hi, f x=(x:ℂ)⁻¹) {R : ℝ} (hR : 0 ≤ R)
    (j : ℝ) {a : ι → ℝ} (ha : ∀ i, 0 ≤ a i) (M : Matrix ι ι ℝ) (hM : Mᵀ=M)
    (hg : M ∈ logPathGood R lo hi ((j/(Fintype.card ι:ℝ))*∑ b,a b) a) :
    (∫ z in (0:ℝ)..1, logPathCutoffDerivative f R hR j a M z)=
      log (logPath ((j/(Fintype.card ι:ℝ))*∑ b,a b) a M 1).det/(Fintype.card ι:ℝ) := by
  have hc : Continuous (fun z => logPathCutoffDerivative f R hR j a M z) :=
    (continuous_logPathCutoffDerivative f hR j a).comp (continuous_id.prodMk continuous_const)
  have hh := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (f := fun z => log (logPath ((j/(Fintype.card ι:ℝ))*∑ b,a b) a M z).det/(Fintype.card ι:ℝ))
    (f' := fun z => logPathCutoffDerivative f R hR j a M z)
    (fun z hz => ?_) (hc.intervalIntegrable 0 1)
  · simpa only [logPath,zero_pow (by norm_num : 2 ≠ 0),zero_mul,zero_smul,add_zero,
      sub_zero,Matrix.det_one,log_one,zero_div] using hh
  · have hz' : z ∈ Icc (0:ℝ) 1 := by simpa only [uIcc_of_le (by norm_num : (0:ℝ)≤1)] using hz
    obtain ⟨hunit,hagree⟩ := pathK_agrees_at f hlo hf hR j ha hz'.1 M hM hg.1 (hg.2 z hz').1 (hg.2 z hz').2
    have hd := (LogDet.hasDerivAt_logdet (hasDerivAt_logPath ((j/(Fintype.card ι:ℝ))*∑ b,a b) a M z) hunit).div_const (Fintype.card ι:ℝ)
    rw [logPath_trace_derivative,← hagree] at hd
    simpa only [logPathCutoffDerivative,realProject_eq_self hR M hM hg.1] using hd

lemma trace_abs_le_card_opNorm (M : Matrix ι ι ℝ) : |M.trace| ≤ (Fintype.card ι:ℝ)*opNorm M := by
  unfold Matrix.trace Matrix.diag
  exact (Finset.abs_sum_le_sum_abs _ _).trans (by simpa only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul] using Finset.sum_le_sum (s := Finset.univ) (fun i _ => matrix_entry_le_opNorm M i i))

lemma logPathCutoffDerivative_bound [Nonempty ι] (f : 𝓢(ℝ,ℂ)) {R j : ℝ} (hR : 0 ≤ R) (hj : 0 ≤ j)
    {a : ι → ℝ} (ha : ∀ i, 0 ≤ a i) (haA : ∀ i, a i ≤ 1) {z : ℝ} (hz : z ∈ Icc (0:ℝ) 1)
    (M : Matrix ι ι ℝ) :
    |logPathCutoffDerivative f R hR j a M z| ≤ (2*j+R)*pathBound f R j 1 := by
  have hn : (0:ℝ) < Fintype.card ι := Nat.cast_pos.mpr Fintype.card_pos
  have hB := (path_constants_nonneg f hR hj (by norm_num : (0:ℝ)≤1)).1
  have hq := diagonal_mean_bounds hj ha haA
  simp only [mul_one] at hq
  have hK := (pathK_bounds f hR hj (by norm_num : (0:ℝ)≤1) ha haA hz).1 M
  have hD : opNorm (diagonal a) ≤ 1 := opNorm_diagonal_le (by norm_num) (fun i => by rw [abs_of_nonneg (ha i)]; exact haA i)
  have hKD : opNorm (pathK f R hR j a z M*diagonal a) ≤ pathBound f R j 1 :=
    (opNorm_mul _ _).trans (by simpa only [mul_one] using mul_le_mul hK hD (norm_nonneg _) hB)
  have hWKD : opNorm (realProject R hR M*pathK f R hR j a z M*diagonal a) ≤ R*pathBound f R j 1 := by
    rw [mul_assoc]
    exact (opNorm_mul _ _).trans (mul_le_mul (realProject_opNorm hR M) hKD (norm_nonneg _) hR)
  have ht₁ := (trace_abs_le_card_opNorm _).trans (mul_le_mul_of_nonneg_left hKD hn.le)
  have ht₂ := (trace_abs_le_card_opNorm _).trans (mul_le_mul_of_nonneg_left hWKD hn.le)
  have hzq : |2*z*((j/(Fintype.card ι:ℝ))*∑ b,a b)| ≤ 2*j := by
    rw [abs_of_nonneg (mul_nonneg (mul_nonneg (by norm_num) hz.1) hq.1)]
    nlinarith [mul_le_mul hz.2 hq.2 hq.1 (by norm_num : (0:ℝ)≤1)]
  unfold logPathCutoffDerivative
  rw [abs_div,abs_of_pos hn]
  apply (div_le_iff₀ hn).mpr
  have hterm : |(2*z*((j/(Fintype.card ι:ℝ))*∑ b,a b))*(pathK f R hR j a z M*diagonal a).trace| ≤
      2*j*((Fintype.card ι:ℝ)*pathBound f R j 1) := by
    rw [abs_mul]
    exact mul_le_mul hzq ht₁ (abs_nonneg _) (by positivity)
  have hh := (abs_sub (2*z*((j/(Fintype.card ι:ℝ))*∑ b,a b)*(pathK f R hR j a z M*diagonal a).trace)
    (realProject R hR M*pathK f R hR j a z M*diagonal a).trace).trans (add_le_add hterm ht₂)
  exact hh.trans_eq (by ring)
end SKGap
end
end

section
noncomputable section
namespace SKGap
open Matrix MeasureTheory ProbabilityTheory Real Set
open RealComplex
open scoped BigOperators Matrix.Norms.Frobenius SchwartzMap
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma frobenius_le_sum_abs (M : Matrix ι ι ℝ) : ‖M‖ ≤ ∑ i,∑ k,|M i k| := by
  apply (sq_le_sq₀ (norm_nonneg M) (by positivity : 0 ≤ ∑ i,∑ k,|M i k|)).mp
  rw [frobenius_sq]
  calc
    _ ≤ ∑ i,(∑ k,|M i k|)^2 := Finset.sum_le_sum (fun i _ => by
      simpa only [sq_abs] using Finset.sum_sq_le_sq_sum_of_nonneg (s := Finset.univ) (fun k _ => abs_nonneg (M i k)))
    _ ≤ (∑ i,∑ k,|M i k|)^2 := Finset.sum_sq_le_sq_sum_of_nonneg (fun i _ => by positivity)

lemma frobenius_one : ‖(1:Matrix ι ι ℝ)‖=sqrt (Fintype.card ι:ℝ) := by
  have hs := LogDet.frobenius_sq_trace (1:Matrix ι ι ℝ)
  simp only [transpose_one,one_mul,Matrix.trace_one] at hs
  nlinarith [norm_nonneg (1:Matrix ι ι ℝ),sqrt_nonneg (Fintype.card ι:ℝ),sq_sqrt (Nat.cast_nonneg (Fintype.card ι))]

lemma logPath_one_frobenius [Nonempty ι] {j : ℝ} (hj : 0 ≤ j)
    {a : ι → ℝ} (ha : ∀ i, 0 ≤ a i) (ha1 : ∀ i, a i ≤ 1) (M : Matrix ι ι ℝ) :
    ‖logPath ((j/(Fintype.card ι:ℝ))*∑ i,a i) a M 1‖ ≤ sqrt (Fintype.card ι:ℝ)*(1+j)+‖M‖ := by
  have hq := diagonal_mean_bounds hj ha ha1
  simp only [mul_one] at hq
  have hD : opNorm (diagonal a) ≤ 1 := opNorm_diagonal_le (by norm_num) (fun i => by rw [abs_of_nonneg (ha i)]; exact ha1 i)
  have hDn := (LogDet.frobenius_le_sqrt_card_opNorm (diagonal a)).trans
    (mul_le_mul_of_nonneg_left hD (sqrt_nonneg _))
  simp only [mul_one] at hDn
  have hDM := (frobenius_mul_le_opNorm (diagonal a) M).trans (mul_le_mul_of_nonneg_right hD (norm_nonneg M))
  simp only [one_mul] at hDM
  simp only [logPath,one_pow,one_mul,one_smul]
  apply (norm_sub_le _ _).trans
  apply (add_le_add (norm_add_le _ _) hDM).trans
  rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg hq.1,frobenius_one]
  have hh := mul_le_mul hq.2 hDn (norm_nonneg _) hj
  nlinarith

lemma logPath_one_lipschitz {j : ℝ} {a : ι → ℝ}
    (ha : ∀ i, 0 ≤ a i) (ha1 : ∀ i, a i ≤ 1) :
    LipschitzWith 1 (fun M : Matrix ι ι ℝ => logPath ((j/(Fintype.card ι:ℝ))*∑ i,a i) a M 1) := by
  apply LipschitzWith.of_dist_le_mul
  intro M N
  simp only [dist_eq_norm,NNReal.coe_one,one_mul]
  have he : logPath ((j/(Fintype.card ι:ℝ))*∑ i,a i) a M 1-
      logPath ((j/(Fintype.card ι:ℝ))*∑ i,a i) a N 1= -(diagonal a*(M-N)) := by
    simp only [logPath,one_pow,one_mul,one_smul,Matrix.mul_sub]; abel
  rw [he,norm_neg]
  have hD : opNorm (diagonal a) ≤ 1 := opNorm_diagonal_le (by norm_num) (fun i => by rw [abs_of_nonneg (ha i)]; exact ha1 i)
  exact (frobenius_mul_le_opNorm _ _).trans (by simpa only [one_mul] using mul_le_mul_of_nonneg_right hD (norm_nonneg (M-N)))

lemma logPath_regularized_integrable [Nonempty ι] {j γ : ℝ} (hγ : 0 < γ)
    {a : ι → ℝ} (ha : ∀ i, 0 ≤ a i) (ha1 : ∀ i, a i ≤ 1) :
    Integrable (fun g => LogDet.regularizedLogDet γ (logPath ((j/(Fintype.card ι:ℝ))*∑ i,a i) a
      (goeMatrix (j/(Fintype.card ι:ℝ)) g) 1))
      (Measure.pi (fun _ : MatrixCoordinates ι => gaussianReal 0 1)) := by
  have hF : LipschitzWith ⟨1/sqrt ((Fintype.card ι:ℝ)*γ),by positivity⟩ (LogDet.regularizedLogDet γ : Matrix ι ι ℝ → ℝ) := by
    apply LipschitzWith.of_dist_le_mul
    intro M N
    change |LogDet.regularizedLogDet γ M-LogDet.regularizedLogDet γ N| ≤ (1/sqrt ((Fintype.card ι:ℝ)*γ))*‖M-N‖
    exact LogDet.regularizedLogDet_lipschitz hγ M N
  exact gaussianProduct_integrable_lipschitz (hF.comp ((logPath_one_lipschitz ha ha1).comp (goeMatrix_L2_lipschitz _)))

lemma logPath_regularized_rare [Nonempty ι] {j γ : ℝ} (hj : 0 ≤ j) (hγ : 0 < γ)
    {a : ι → ℝ} (ha : ∀ i, 0 ≤ a i) (ha1 : ∀ i, a i ≤ 1)
    {s : Set (MatrixCoordinates ι → ℝ)} (hs : MeasurableSet s) :
    (∫ g in s, |LogDet.regularizedLogDet γ (logPath ((j/(Fintype.card ι:ℝ))*∑ i,a i) a
      (goeMatrix (j/(Fintype.card ι:ℝ)) g) 1)|
      ∂Measure.pi (fun _ : MatrixCoordinates ι => gaussianReal 0 1)) ≤
      (|log γ|+sqrt (Fintype.card ι:ℝ)*(1+j)/sqrt ((Fintype.card ι:ℝ)*γ))*
        (Measure.pi (fun _ : MatrixCoordinates ι => gaussianReal 0 1)).real s+
      (Fintype.card ι:ℝ)^2*sqrt (2*j/(Fintype.card ι:ℝ))/sqrt ((Fintype.card ι:ℝ)*γ)*
        sqrt ((Measure.pi (fun _ : MatrixCoordinates ι => gaussianReal 0 1)).real s) := by
  let μ := Measure.pi (fun _ : MatrixCoordinates ι => gaussianReal 0 1)
  let r := j/(Fintype.card ι:ℝ)
  have hentry (i k : ι) : Integrable (fun g => |goeMatrix r g i k|) μ :=
    ((goeEntry_memLp r i k).integrable (by norm_num)).abs
  have hsum : Integrable (fun g => ∑ i,∑ k,|goeMatrix r g i k|) μ :=
    integrable_finsetSum _ (fun i _ => integrable_finsetSum _ (fun k _ => hentry i k))
  have hpoint (g) : |LogDet.regularizedLogDet γ (logPath ((j/(Fintype.card ι:ℝ))*∑ i,a i) a (goeMatrix r g) 1)| ≤
      (|log γ|+sqrt (Fintype.card ι:ℝ)*(1+j)/sqrt ((Fintype.card ι:ℝ)*γ))+
        (∑ i,∑ k,|goeMatrix r g i k|)/sqrt ((Fintype.card ι:ℝ)*γ) := by
    apply (LogDet.regularizedLogDet_abs hγ _).trans
    have hh := (logPath_one_frobenius hj ha ha1 (goeMatrix r g)).trans (add_le_add_right (frobenius_le_sum_abs _) _)
    have ht := add_le_add_right (div_le_div_of_nonneg_right hh (sqrt_nonneg ((Fintype.card ι:ℝ)*γ))) |log γ|
    exact ht.trans_eq (by ring)
  have hm := integral_mono (μ := μ.restrict s) (logPath_regularized_integrable hγ ha ha1).abs.integrableOn
    ((integrable_const _).add (hsum.div_const _)).integrableOn hpoint
  simp only [Pi.add_apply] at hm
  rw [integral_add (integrable_const (|log γ|+sqrt (Fintype.card ι:ℝ)*(1+j)/sqrt ((Fintype.card ι:ℝ)*γ)))
      (hsum.div_const (sqrt ((Fintype.card ι:ℝ)*γ))).integrableOn,integral_const,smul_eq_mul,
    measureReal_restrict_apply_univ,integral_div] at hm
  have hsumle : (∫ g in s, (∑ i,∑ k,|goeMatrix r g i k|) ∂μ) ≤
      (Fintype.card ι:ℝ)^2*sqrt (2*j/(Fintype.card ι:ℝ))*sqrt (μ.real s) := by
    rw [integral_finsetSum _ (fun i _ => (integrable_finsetSum _ (fun k _ => hentry i k)).integrableOn)]
    simp_rw [integral_finsetSum _ (fun k _ => (hentry _ k).integrableOn)]
    have ht := Finset.sum_le_sum (s := Finset.univ) (fun i _ => Finset.sum_le_sum (s := Finset.univ) (fun k _ =>
      (integral_abs_on_set_le (goeEntry_memLp r i k) hs).trans (mul_le_mul_of_nonneg_right
        (sqrt_le_sqrt (goeEntry_integral_sq_le (by dsimp [r]; positivity) i k)) (sqrt_nonneg _))))
    simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul] at ht
    exact ht.trans_eq (by
      dsimp only [r,μ]
      rw [show 2*(j/(Fintype.card ι:ℝ))=2*j/(Fintype.card ι:ℝ) by ring]
      ring)
  apply hm.trans
  have hh := div_le_div_of_nonneg_right hsumle (sqrt_nonneg ((Fintype.card ι:ℝ)*γ))
  exact (add_le_add_right hh (μ.real s*(|log γ|+sqrt (Fintype.card ι:ℝ)*(1+j)/sqrt ((Fintype.card ι:ℝ)*γ)))).trans_eq (by ring)
end SKGap

namespace SKGap
open MeasureTheory Real Set
lemma expectation_upper_good {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {F I : Ω → ℝ} {s : Set Ω} (hs : MeasurableSet s) (hF : Integrable F μ) (hI : Integrable I μ)
    {D c : ℝ} (hc : 0 ≤ c) (hD : ∀ x, |I x| ≤ D)
    (hgood : ∀ x ∉ s, F x ≤ 2*I x+c) :
    (∫ x, F x ∂μ) ≤ 2*(∫ x, I x ∂μ)+c+(∫ x in s, |F x| ∂μ)+2*D*μ.real s := by
  have hi : Integrable (fun x => 2*I x+c+s.indicator (fun x => |F x|+2*D) x) μ :=
    ((hI.const_mul 2).add (integrable_const c)).add ((hF.abs.add (integrable_const (2*D))).indicator hs)
  have hp (x) : F x ≤ 2*I x+c+s.indicator (fun x => |F x|+2*D) x := by
    by_cases hx : x ∈ s
    · simp only [Set.indicator_of_mem hx]
      have hh := (abs_le.mp (hD x)).1
      nlinarith [le_abs_self (F x)]
    · simpa only [Set.indicator_of_notMem hx,add_zero] using hgood x hx
  have hh := integral_mono hF hi hp
  have hi₁ : Integrable (fun x => 2*I x+c) μ := (hI.const_mul 2).add (integrable_const c)
  have hi₂ : Integrable (s.indicator (fun x => |F x|+2*D)) μ := (hF.abs.add (integrable_const (2*D))).indicator hs
  rw [integral_add hi₁ hi₂,integral_add (hI.const_mul 2) (integrable_const c),
    integral_const_mul,integral_indicator hs,integral_add hF.abs.integrableOn (integrable_const (2*D)),
    integral_const,integral_const] at hh
  simpa only [probReal_univ,mul_one,smul_eq_mul,measureReal_restrict_apply_univ,one_mul,mul_comm,add_assoc] using hh
end SKGap
end
end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Stability_LogDetMean
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
namespace SKGap
open Matrix MeasureTheory ProbabilityTheory Real Set
open RealComplex
open scoped BigOperators Matrix.Norms.Frobenius SchwartzMap
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma trace_mul_diagonal_right (M : Matrix ι ι ℝ) (a : ι → ℝ) :
    (M*diagonal a).trace=∑ i,M i i*a i := by
  simp only [Matrix.trace,Matrix.diag,Matrix.mul_diagonal]

lemma integral_trace_diagonal {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    (F : Ω → Matrix ι ι ℝ) (a : ι → ℝ) (hF : ∀ i, Integrable (fun g => F g i i) μ) :
    (∫ g, (F g*diagonal a).trace ∂μ)=∑ i,(∫ g, F g i i ∂μ)*a i := by
  simp_rw [trace_mul_diagonal_right]
  rw [integral_finsetSum Finset.univ (fun i _ => (hF i).mul_const (a i))]
  simp only [integral_mul_const]

omit [DecidableEq ι] in
lemma weighted_average_bias [Nonempty ι] {a t : ι → ℝ} {c δ : ℝ}
    (hδ : 0 ≤ δ) (ha : ∀ i, 0 ≤ a i) (ha1 : ∀ i, a i ≤ 1) (ht : ∀ i, |t i-c| ≤ δ) :
    |(∑ i,t i*a i)/(Fintype.card ι:ℝ)-c*((∑ i,a i)/(Fintype.card ι:ℝ))| ≤ δ := by
  have hn : (0:ℝ) < Fintype.card ι := Nat.cast_pos.mpr Fintype.card_pos
  have he : (∑ i,t i*a i)/(Fintype.card ι:ℝ)-c*((∑ i,a i)/(Fintype.card ι:ℝ))=
      (∑ i,(t i-c)*a i)/(Fintype.card ι:ℝ) := by
    simp_rw [sub_mul,Finset.sum_sub_distrib,← Finset.mul_sum]
    ring
  rw [he,abs_div,abs_of_pos hn]
  apply (div_le_iff₀ hn).mpr
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  have hh := Finset.sum_le_sum (s := Finset.univ) (fun i _ =>
    show |(t i-c)*a i| ≤ δ from by rw [abs_mul,abs_of_nonneg (ha i)]; exact (mul_le_mul (ht i) (ha1 i) (ha i) hδ).trans_eq (mul_one δ))
  simpa only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,mul_comm] using hh

lemma logPathCutoffDerivative_mean_error [Nonempty ι] (f : 𝓢(ℝ,ℂ)) {R j C : ℝ}
    (hR : 0 ≤ R) (hj : 0 ≤ j) (hC : 0 ≤ C) {a : ι → ℝ}
    (ha : ∀ i, 0 ≤ a i) (ha1 : ∀ i, a i ≤ 1) {z : ℝ} (hz : z ∈ Icc (0:ℝ) 1)
    (hK : ∀ i, |pathExpected f R hR j a z i-1| ≤ C/(Fintype.card ι:ℝ))
    (hWK : ∀ i, |(∫ g, (realProject R hR (goeMatrix (j/(Fintype.card ι:ℝ)) g)*
      pathK f R hR j a z (goeMatrix (j/(Fintype.card ι:ℝ)) g)) i i
      ∂Measure.pi (fun _ : MatrixCoordinates ι => gaussianReal 0 1))-z*((j/(Fintype.card ι:ℝ))*∑ b,a b)| ≤ C/(Fintype.card ι:ℝ)) :
    |(∫ g, logPathCutoffDerivative f R hR j a (goeMatrix (j/(Fintype.card ι:ℝ)) g) z
      ∂Measure.pi (fun _ : MatrixCoordinates ι => gaussianReal 0 1))-
      z*j*((∑ i,a i)/(Fintype.card ι:ℝ))^2| ≤ (2*j+1)*C/(Fintype.card ι:ℝ) := by
  let μ := Measure.pi (fun _ : MatrixCoordinates ι => gaussianReal 0 1)
  let KG := fun g : MatrixCoordinates ι → ℝ => pathK f R hR j a z (goeMatrix (j/(Fintype.card ι:ℝ)) g)
  let WG := fun g : MatrixCoordinates ι → ℝ => realProject R hR (goeMatrix (j/(Fintype.card ι:ℝ)) g)*KG g
  have hn : (0:ℝ) < Fintype.card ι := Nat.cast_pos.mpr Fintype.card_pos
  have hB := (path_constants_nonneg f hR hj (by norm_num : (0:ℝ)≤1)).1
  have hbnd := (pathK_bounds f hR hj (by norm_num : (0:ℝ)≤1) ha ha1 hz).1
  have hcontK : Continuous KG := (pathK_continuous f hR hj (by norm_num : (0:ℝ)≤1) ha ha1 hz).comp (goeMatrix_pi_lipschitz _).continuous
  have hcontW : Continuous WG := ((realProject_lipschitz hR).continuous.comp (goeMatrix_pi_lipschitz _).continuous).mul hcontK
  have hiK (i : ι) : Integrable (fun g => KG g i i) μ :=
    Integrable.mono' (integrable_const (pathBound f R j 1)) (hcontK.matrix_elem i i).aestronglyMeasurable
      (ae_of_all _ (fun g => by simpa only [Real.norm_eq_abs] using (matrix_entry_le_opNorm _ i i).trans (hbnd _)))
  have hiW (i : ι) : Integrable (fun g => WG g i i) μ :=
    Integrable.mono' (integrable_const (R*pathBound f R j 1)) (hcontW.matrix_elem i i).aestronglyMeasurable
      (ae_of_all _ (fun g => by simpa only [Real.norm_eq_abs] using (matrix_entry_le_opNorm _ i i).trans (realProjectedProduct_opNorm hR _ hbnd _)))
  have htK : Integrable (fun g => (KG g*diagonal a).trace) μ := by
    simp_rw [trace_mul_diagonal_right]
    exact integrable_finsetSum _ (fun i _ => (hiK i).mul_const (a i))
  have htW : Integrable (fun g => (WG g*diagonal a).trace) μ := by
    simp_rw [trace_mul_diagonal_right]
    exact integrable_finsetSum _ (fun i _ => (hiW i).mul_const (a i))
  have heK := weighted_average_bias (div_nonneg hC hn.le) ha ha1 (t := fun i => ∫ g, KG g i i ∂μ) hK
  have heW := weighted_average_bias (div_nonneg hC hn.le) ha ha1 (t := fun i => ∫ g, WG g i i ∂μ) hWK
  rw [← integral_trace_diagonal KG a hiK] at heK
  rw [← integral_trace_diagonal WG a hiW] at heW
  have hq := diagonal_mean_bounds hj ha ha1
  simp only [mul_one] at hq
  have hcoef : |2*z*((j/(Fintype.card ι:ℝ))*∑ i,a i)| ≤ 2*j := by
    rw [abs_of_nonneg (mul_nonneg (mul_nonneg (by norm_num) hz.1) hq.1)]
    nlinarith [mul_le_mul hz.2 hq.2 hq.1 (by norm_num : (0:ℝ)≤1)]
  change |(∫ g, (2*z*((j/(Fintype.card ι:ℝ))*∑ i,a i)*(KG g*diagonal a).trace-(WG g*diagonal a).trace)/(Fintype.card ι:ℝ) ∂μ)-_| ≤ _
  rw [integral_div,integral_sub (htK.const_mul _) htW,integral_const_mul]
  have he : (2*z*((j/(Fintype.card ι:ℝ))*∑ i,a i)*(∫ g, (KG g*diagonal a).trace ∂μ)-(∫ g, (WG g*diagonal a).trace ∂μ))/(Fintype.card ι:ℝ)-z*j*((∑ i,a i)/(Fintype.card ι:ℝ))^2=
      (2*z*((j/(Fintype.card ι:ℝ))*∑ i,a i))*((∫ g, (KG g*diagonal a).trace ∂μ)/(Fintype.card ι:ℝ)-1*((∑ i,a i)/(Fintype.card ι:ℝ)))-
      ((∫ g, (WG g*diagonal a).trace ∂μ)/(Fintype.card ι:ℝ)-z*((j/(Fintype.card ι:ℝ))*∑ i,a i)*((∑ i,a i)/(Fintype.card ι:ℝ))) := by ring
  rw [he]
  apply (abs_sub _ _).trans
  have hm := mul_le_mul hcoef heK (abs_nonneg _) (by positivity : 0 ≤ 2*j)
  rw [← abs_mul] at hm
  exact (add_le_add hm heW).trans_eq (by ring)
end SKGap
end
end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Matrix_LogDetExpected
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
namespace SKGap
open Matrix MeasureTheory ProbabilityTheory Real Set Filter
open RealComplex
open scoped BigOperators Matrix.Norms.Frobenius SchwartzMap Topology
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma rare_logdet_coefficients {n j γ : ℝ} (hn : 0 < n) (hj : 0 ≤ j) (hγ : 0 < γ) :
    sqrt n*(1+j)/sqrt (n*γ)=(1+j)/sqrt γ ∧
    n^2*sqrt (2*j/n)/sqrt (n*γ)=n*sqrt (2*j)/sqrt γ := by
  have hs : 0 < sqrt n := sqrt_pos.mpr hn
  have hg : 0 < sqrt γ := sqrt_pos.mpr hγ
  rw [sqrt_mul hn.le,sqrt_div (by positivity : 0 ≤ 2*j)]
  constructor
  · field_simp
  · field_simp
    rw [sq_sqrt hn.le]
    ring

lemma logdetMeanError_nonneg {j R B C rate γ : ℝ} (hj : 0 ≤ j) (hR : 0 ≤ R)
    (hB : 0 ≤ B) (hC : 0 ≤ C) (hrate : 0 < rate) (hγ : 0 < γ) :
    0 ≤ logdetMeanError j R B C rate γ := by unfold logdetMeanError; positivity

lemma logPath_regularized_expected [Nonempty ι] (f : 𝓢(ℝ,ℂ)) {R lo hi j C γ rate : ℝ}
    (hR : 0 ≤ R) (hlo : 0 < lo) (hf : ∀ x ∈ Icc lo hi, f x=(x:ℂ)⁻¹)
    (hj : 0 ≤ j) (hC : 0 ≤ C) (hγ : 0 < γ) (hrate : 0 < rate)
    {a : ι → ℝ} (ha : ∀ i, 0 ≤ a i) (ha1 : ∀ i, a i ≤ 1)
    (hK : ∀ z ∈ Icc (0:ℝ) 1, ∀ i, |pathExpected f R hR j a z i-1| ≤ C/(Fintype.card ι:ℝ))
    (hWK : ∀ z ∈ Icc (0:ℝ) 1, ∀ i,
      |(∫ g, (realProject R hR (goeMatrix (j/(Fintype.card ι:ℝ)) g)*
        pathK f R hR j a z (goeMatrix (j/(Fintype.card ι:ℝ)) g)) i i
        ∂Measure.pi (fun _ : MatrixCoordinates ι => gaussianReal 0 1))-
          z*((j/(Fintype.card ι:ℝ))*∑ b,a b)| ≤ C/(Fintype.card ι:ℝ))
    (hp : (Measure.pi (fun _ : MatrixCoordinates ι => gaussianReal 0 1)).real
      {g | goeMatrix (j/(Fintype.card ι:ℝ)) g ∉ logPathGood R lo hi ((j/(Fintype.card ι:ℝ))*∑ b,a b) a} ≤
      3*Real.exp (-rate*(Fintype.card ι:ℝ))) :
    (∫ g, LogDet.regularizedLogDet γ (logPath ((j/(Fintype.card ι:ℝ))*∑ b,a b) a
      (goeMatrix (j/(Fintype.card ι:ℝ)) g) 1)
      ∂Measure.pi (fun _ : MatrixCoordinates ι => gaussianReal 0 1)) ≤
      j*((∑ i,a i)/(Fintype.card ι:ℝ))^2+γ*(pathBound f R j 1)^2+
        logdetMeanError j R (pathBound f R j 1) C rate γ/(Fintype.card ι:ℝ) := by
  let μ := Measure.pi (fun _ : MatrixCoordinates ι => gaussianReal 0 1)
  let r := j/(Fintype.card ι:ℝ)
  let q := r*∑ i,a i
  let B := pathBound f R j 1
  let D := (2*j+R)*B
  let T := fun p : ℝ × (MatrixCoordinates ι → ℝ) => logPathCutoffDerivative f R hR j a (goeMatrix r p.2) p.1
  let I := fun g => ∫ z in (0:ℝ)..1, T (z,g)
  let F := fun g => LogDet.regularizedLogDet γ (logPath q a (goeMatrix r g) 1)
  let s := {g | goeMatrix r g ∉ logPathGood R lo hi q a}
  have hn : (0:ℝ) < Fintype.card ι := Nat.cast_pos.mpr Fintype.card_pos
  have hn1 : (1:ℝ) ≤ Fintype.card ι := by exact_mod_cast Fintype.card_pos
  have hB : 0 ≤ B := (path_constants_nonneg f hR hj (by norm_num : (0:ℝ)≤1)).1
  have hD : 0 ≤ D := by dsimp [D]; positivity
  have ht : Continuous T := (continuous_logPathCutoffDerivative f hR j a).comp
    (continuous_fst.prodMk ((goeMatrix_pi_lipschitz r).continuous.comp continuous_snd))
  have htb (z : ℝ) (hz : z ∈ Icc (0:ℝ) 1) (g) : |T (z,g)| ≤ D :=
    logPathCutoffDerivative_bound f hR hj ha ha1 hz _
  have htm (z : ℝ) (hz : z ∈ Icc (0:ℝ) 1) :
      |(∫ g, T (z,g) ∂μ)-z*(j*((∑ i,a i)/(Fintype.card ι:ℝ))^2)| ≤ (2*j+1)*C/(Fintype.card ι:ℝ) := by
    simpa only [mul_assoc] using logPathCutoffDerivative_mean_error f hR hj hC ha ha1 hz (hK z hz) (hWK z hz)
  obtain ⟨hI,hIm⟩ := bounded_interval_mean (μ := μ) ht htb htm
  have hIb (g) : |I g| ≤ D := by
    have hh := intervalIntegral.norm_integral_le_of_norm_le_const (a := (0:ℝ)) (b := 1)
      (f := fun z => T (z,g)) (C := D) (fun z hz => by
        have hz' : z ∈ Ioc (0:ℝ) 1 := by simpa only [uIoc_of_le (by norm_num : (0:ℝ)≤1)] using hz
        simpa only [Real.norm_eq_abs] using htb z ⟨hz'.1.le,hz'.2⟩ g)
    simpa only [I,Real.norm_eq_abs,sub_zero,abs_one,mul_one] using hh
  have hs : MeasurableSet s := ((logPathGood_isClosed R lo hi q a).preimage (goeMatrix_pi_lipschitz r).continuous).measurableSet.compl
  have hF : Integrable F μ := logPath_regularized_integrable hγ ha ha1
  have hgood (g) (hg : g ∉ s) : F g ≤ 2*I g+γ*B^2 := by
    have hg' : goeMatrix r g ∈ logPathGood R lo hi q a := by simpa only [s,mem_ofPred_eq,not_not] using hg
    have hsymm : (goeMatrix r g)ᵀ=goeMatrix r g := goeMatrix_transpose r g
    have hev := logdetPath_integral f hlo hf hR j ha (goeMatrix r g) hsymm hg'
    have hu := pathK_agrees_at f hlo hf hR j ha (by norm_num : (0:ℝ)≤1) (goeMatrix r g) hsymm hg'.1
      (hg'.2 1 (by constructor <;> norm_num)).1 (hg'.2 1 (by constructor <;> norm_num)).2
    have hb : opNorm (logPath q a (goeMatrix r g) 1)⁻¹ ≤ B := by
      rw [← hu.2]
      exact (pathK_bounds f hR hj (by norm_num : (0:ℝ)≤1) ha ha1 (by constructor <;> norm_num)).1 _
    have hh := LogDet.regularizedLogDet_le_logdet_opNorm hγ.le _ hu.1 hb
    change F g ≤ 2*I g+γ*B^2
    dsimp only [I,T]
    rw [hev]
    exact hh.trans_eq (by ring)
  have hex := expectation_upper_good hs hF hI (mul_nonneg hγ.le (sq_nonneg B)) hIb hgood
  have hrare := logPath_regularized_rare hj hγ ha ha1 hs
  obtain ⟨hc₁,hc₂⟩ := rare_logdet_coefficients hn hj hγ
  rw [hc₁,hc₂] at hrare
  obtain ⟨hp₁,_,hp₃⟩ := exponential_tail_absorptions hrate hn1 hp
  have hsmall : (|log γ|+(1+j)/sqrt γ+2*D)*μ.real s+
      (sqrt (2*j)/sqrt γ)*((Fintype.card ι:ℝ)*sqrt (μ.real s)) ≤
      (|log γ|+(1+j)/sqrt γ+2*D)*((3/rate)/(Fintype.card ι:ℝ))+
      (sqrt (2*j)/sqrt γ)*((8*sqrt 3/rate^2)/(Fintype.card ι:ℝ)) := by
    exact add_le_add (mul_le_mul_of_nonneg_left hp₁ (by positivity))
      (mul_le_mul_of_nonneg_left hp₃ (by positivity))
  have hib := (abs_le.mp hIm).2
  dsimp only [F,I,T,q,r,μ,B,D,logdetMeanError] at hex hrare hib hsmall ⊢
  simp only [div_eq_mul_inv] at hex hrare hib hsmall ⊢
  nlinarith only [hex,hrare,hib,hsmall]
end SKGap
end
end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Stability_LogDetUniformMean
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
namespace SKGap
open Matrix MeasureTheory ProbabilityTheory Real Set Filter
open RealComplex
open scoped BigOperators Matrix.Norms.Frobenius SchwartzMap Topology

theorem actual_logdet_mean_oai {j : ℝ} (hj : 0 < j) (hj1 : j < 1) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ γ : ℝ, 0 < γ → ∃ C : ℝ, 0 ≤ C ∧ ∃ N : ℕ, 0 < N ∧
      ∀ n : ℕ, N ≤ n → ∀ a : Fin n → ℝ, (∀ i, 0 ≤ a i) → (∀ i, a i ≤ 1) →
        (∫ g, LogDet.regularizedLogDet γ (logPath ((j/(n:ℝ))*∑ i,a i) a
          (goeMatrix (j/(n:ℝ)) g) 1)
          ∂Measure.pi (fun _ : MatrixCoordinates (Fin n) => gaussianReal 0 1)) ≤
          j*((∑ i,a i)/(n:ℝ))^2+γ*B^2+C/(n:ℝ) := by
  have hs : sqrt j*1 < 1 := by nlinarith [sq_sqrt hj.le,sqrt_nonneg j]
  obtain ⟨f,R,hR,lo,hi,C,N,hReq,hloeq,hhieq,hlo,hf,_hfr,hC,hN,hbias⟩ :=
    actual_projected_path_equivalents hj (by norm_num : (0:ℝ)<1) hs
  have hB := (path_constants_nonneg f hR hj.le (by norm_num : (0:ℝ)≤1)).1
  refine ⟨pathBound f R j 1,hB,?_⟩
  intro γ hγ
  have hr := pathRate_pos hj (by norm_num : (0:ℝ)<1) hs
  refine ⟨logdetMeanError j R (pathBound f R j 1) C (pathRate j 1) γ,
    logdetMeanError_nonneg hj.le hR hB hC.le hr hγ,?_⟩
  obtain ⟨N₁,hN₁⟩ := eventually_atTop.mp (path_size_eventually hs)
  refine ⟨max N N₁,lt_of_lt_of_le hN (le_max_left _ _),?_⟩
  intro n hn a ha ha1
  have hnN := (le_max_left N N₁).trans hn
  have hn0 := hN.trans_le hnN
  let : Nonempty (Fin n) := Fin.pos_iff_nonempty.mp hn0
  have hb (z) (hz : z ∈ Icc (0:ℝ) 1) := hbias n hnN a ha ha1 z hz
  have hp := logPathGood_exponential hj (by norm_num : (0:ℝ)<1) ha ha1 hs
    (by simpa only [Fintype.card_fin] using hN₁ n ((le_max_right N N₁).trans hn))
  rw [← hReq,← hloeq,← hhieq] at hp
  simpa only [Fintype.card_fin] using
    logPath_regularized_expected f hR hlo hf hj.le hC.le hγ hr ha ha1
      (fun z hz i => by simpa only [Fintype.card_fin] using (hb z hz i).1)
      (fun z hz i => by simpa only [Fintype.card_fin] using (hb z hz i).2) hp
end SKGap
end
end

end OAI
end

theorem solution : type_of% @OAI.SKGap.actual_logdet_mean_oai := @OAI.SKGap.actual_logdet_mean_oai
