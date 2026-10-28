-- Prove2me | solution 1 for OAI.SKGap.compact_conditional_uniform_tail
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T06:39:02.061687+00:00
-- url     : https://prove2.me/submissions/5401d252-1c7b-4246-8cd7-f6fbdb31a2a4

import Mathlib
import Definitions.Def_OAIQ072A000
import Theorems.Thm_OAI_SKGap_actual_projected_path_equivalents
import Theorems.Thm_OAI_SKGap_path_all_good_exponential

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
local instance instPseudoMetrizableSpaceMatrixComplex_solutions_1_r0c63af_1 : TopologicalSpace.PseudoMetrizableSpace (Matrix ι ι ℂ) :=
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

lemma convexProject_unique {K : Set E} (hK : ClosedConvexNonempty K) {x p : E}
    (hp : p ∈ K) (hmin : ∀ y ∈ K, inner ℝ (x-p) (y-p) ≤ 0) :
    p = convexProject hK x := by
  let q := convexProject hK x
  have h₁ := hmin q (convexProject_mem hK x)
  have h₂ := convexProject_inner hK x hp
  change inner ℝ (x-q) (p-q) ≤ 0 at h₂
  have hh : ‖p-q‖^2 ≤ 0 := by
    rw [← real_inner_self_eq_norm_sq]
    simp only [inner_sub_right,inner_sub_left,real_inner_comm] at *
    nlinarith
  have hz : ‖p-q‖ = 0 := by nlinarith [norm_nonneg (p-q)]
  exact sub_eq_zero.mp (norm_eq_zero.mp hz)

lemma convexProject_equivariant {K : Set E} (hK : ClosedConvexNonempty K)
    (U : E ≃ₗᵢ[ℝ] E) (hU : ∀ x, U x ∈ K ↔ x ∈ K) (x : E) :
    convexProject hK (U x) = U (convexProject hK x) := by
  apply Eq.symm
  apply convexProject_unique hK ((hU _).mpr (convexProject_mem hK x))
  intro y hy
  have hy' : U.symm y ∈ K := (hU _).mp (by simpa using hy)
  have hh := convexProject_inner hK x hy'
  rw [← U.inner_map_map] at hh
  simpa only [map_sub,LinearIsometryEquiv.apply_symm_apply] using hh

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

lemma inverse_one_sub_square_mul_square (D V : Matrix ι ι 𝕜)
    (hS : IsUnit (1-D*V*D)) :
    (1-D*D*V)⁻¹*(D*D) = D*(1-D*V*D)⁻¹*D := by
  rw [inverse_one_sub_square_mul D V hS]
  have hSS : (1-D*V*D)⁻¹*(1-D*V*D) = 1 :=
    Matrix.nonsing_inv_mul _ (((1-D*V*D).isUnit_iff_isUnit_det).mp hS)
  calc
    _ = D*(1-D*V*D)⁻¹*D+D*(1-(1-D*V*D)⁻¹*(1-D*V*D))*D := by noncomm_ring
    _ = _ := by rw [hSS]; simp

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

section Smoothing
open NormedSpace
open scoped Convolution ContDiff
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

theorem lipschitz_normed_convolution {f : E → ℝ} {L : ℝ≥0}
    (hf : LipschitzWith L f) (φ : ContDiffBump (0 : E))
    (μ : Measure E) [μ.IsAddHaarMeasure] :
    LipschitzWith L (φ.normed μ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, μ] f) := by
  have hcv : ConvolutionExists (φ.normed μ) f (ContinuousLinearMap.lsmul ℝ ℝ) μ :=
    (φ.hasCompactSupport_normed (μ := μ)).convolutionExists_left
      (ContinuousLinearMap.lsmul ℝ ℝ) φ.continuous_normed
      (hf.continuous.locallyIntegrable (μ := μ))
  apply LipschitzWith.of_dist_le_mul
  intro x y
  simp only [dist_eq_norm, convolution_def, ContinuousLinearMap.lsmul_apply, smul_eq_mul]
  have hx : Integrable (fun t => φ.normed μ t * f (x - t)) μ := hcv x
  have hy : Integrable (fun t => φ.normed μ t * f (y - t)) μ := hcv y
  rw [← integral_sub hx hy]
  calc
    _ ≤ ∫ t, φ.normed μ t * ((L : ℝ) * ‖x - y‖) ∂μ := by
      apply norm_integral_le_of_norm_le (φ.integrable_normed.mul_const _)
      filter_upwards [] with t
      rw [← mul_sub, norm_mul, Real.norm_eq_abs (φ.normed μ t),
        abs_of_nonneg (φ.nonneg_normed _)]
      apply mul_le_mul_of_nonneg_left _ (φ.nonneg_normed _)
      simpa only [sub_sub_sub_cancel_right] using hf.norm_sub_le (x - t) (y - t)
    _ = (L : ℝ) * ‖x - y‖ := by rw [integral_mul_const, φ.integral_normed, one_mul]

theorem exists_smooth_lipschitz_approx {f : E → ℝ} {L : ℝ≥0}
    (hf : LipschitzWith L f) {ε : ℝ} (hε : 0 < ε) :
    ∃ g : E → ℝ, ContDiff ℝ ∞ g ∧ LipschitzWith L g ∧
      ∀ x, dist (g x) (f x) ≤ (L : ℝ) * ε := by
  let μ : Measure E := addHaar
  let φ : ContDiffBump (0 : E) := ⟨ε / 2, ε, half_pos hε, half_lt_self hε⟩
  let g := φ.normed μ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, μ] f
  refine ⟨g, ?_, lipschitz_normed_convolution hf φ μ, ?_⟩
  · exact φ.hasCompactSupport_normed.contDiff_convolution_left
      (ContinuousLinearMap.lsmul ℝ ℝ) φ.contDiff_normed hf.continuous.locallyIntegrable
  · intro x
    apply ContDiffBump.dist_normed_convolution_le hf.continuous.aestronglyMeasurable
    intro y hy
    apply (hf.dist_le_mul y x).trans
    exact mul_le_mul_of_nonneg_left (Metric.mem_ball.mp hy).le L.coe_nonneg

end Smoothing

section GaussianMoments
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] [CompleteSpace E]
  {μ : Measure E} [IsGaussian μ]

theorem gaussian_integrable_exp_norm (a : ℝ) :
    Integrable (fun x : E => exp (a * ‖x‖)) μ := by
  obtain ⟨C, hC, hI⟩ := IsGaussian.exists_integrable_exp_sq μ
  apply (hI.const_mul (exp (a ^ 2 / (4 * C)))).mono' (by fun_prop)
  filter_upwards [] with x
  rw [Real.norm_eq_abs, abs_of_pos (exp_pos _), ← exp_add]
  apply exp_le_exp.mpr
  have hs := sq_nonneg (‖x‖ - a / (2 * C))
  have hC0 : C ≠ 0 := ne_of_gt hC
  have heq : C * (‖x‖ - a / (2 * C)) ^ 2 =
      C * ‖x‖ ^ 2 - a * ‖x‖ + a ^ 2 / (4 * C) := by field_simp; ring
  nlinarith [mul_nonneg (le_of_lt hC) hs]

end GaussianMoments

section StandardGaussian
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

theorem stdGaussian_map_dual (L : StrongDual ℝ E) :
    (stdGaussian E).map L = gaussianReal 0 (Real.toNNReal (‖L‖ ^ 2)) := by
  rw [IsGaussian.map_eq_gaussianReal, integral_strongDual_stdGaussian,
    variance_dual_stdGaussian]

theorem stdGaussian_integral_exp_dual (L : StrongDual ℝ E) (r : ℝ) :
    (∫ x, exp (r * L x) ∂stdGaussian E) = exp (r ^ 2 * ‖L‖ ^ 2 / 2) := by
  have hm := mgf_gaussianReal
    (stdGaussian_map_dual L) r
  simpa [mgf, Real.toNNReal_of_nonneg (sq_nonneg _), mul_div_assoc, mul_comm] using hm

theorem gaussian_integrable_exp_lipschitz {μ : Measure E} [IsGaussian μ]
    {f : E → ℝ} {L : ℝ≥0} (hf : LipschitzWith L f) (r : ℝ) :
    Integrable (fun x => exp (r * f x)) μ := by
  have hfc := hf.continuous
  have hI := (gaussian_integrable_exp_norm (μ := μ) (|r| * L)).const_mul
    (exp (|r| * |f 0|))
  apply hI.mono' (by fun_prop)
  filter_upwards [] with x
  rw [Real.norm_eq_abs, abs_of_pos (exp_pos _), ← exp_add]
  apply exp_le_exp.mpr
  have hx : |f x| ≤ |f 0| + L * ‖x‖ := by
    have hh := hf.norm_sub_le x 0
    simp only [sub_zero, Real.norm_eq_abs] at hh
    have ht := abs_add_le (f x - f 0) (f 0)
    rw [sub_add_cancel] at ht
    linarith
  calc
    r * f x ≤ |r * f x| := le_abs_self _
    _ = |r| * |f x| := abs_mul _ _
    _ ≤ |r| * (|f 0| + L * ‖x‖) := mul_le_mul_of_nonneg_left hx (abs_nonneg _)
    _ = _ := by ring

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

theorem exp_interval_average_le {a : ℝ} (ha : 0 < a) {g : ℝ → ℝ}
    (hg : Continuous g) :
    exp (a⁻¹ * ∫ t in (0 : ℝ)..a, g t) ≤
      a⁻¹ * ∫ t in (0 : ℝ)..a, exp (g t) := by
  have h0 : volume (Icc (0 : ℝ) a) ≠ 0 := by
    rw [volume_Icc, sub_zero, ENNReal.ofReal_ne_zero_iff]
    exact ha
  have ht : volume (Icc (0 : ℝ) a) ≠ ∞ := by simp
  have hJ := convexOn_exp.map_set_average_le continuous_exp.continuousOn isClosed_univ
    h0 ht (by filter_upwards [] with x; exact mem_univ _)
    hg.integrableOn_Icc (continuous_exp.comp hg).integrableOn_Icc
  have hvol : volume.real (Icc (0 : ℝ) a) = a := by
    simp [measureReal_def, volume_Icc, ha.le]
  simpa only [setAverage_eq, hvol, smul_eq_mul,
    integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le ha.le] using hJ

section Rotation
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem rotation_snd_norm_le (θ : ℝ) (p : E × E) :
    ‖(ContinuousLinearMap.rotation θ p).2‖ ≤ ‖p.1‖ + ‖p.2‖ := by
  rw [ContinuousLinearMap.rotation_apply]
  calc
    ‖-sin θ • p.1 + cos θ • p.2‖ ≤ ‖-sin θ • p.1‖ + ‖cos θ • p.2‖ := norm_add_le _ _
    _ = |sin θ| * ‖p.1‖ + |cos θ| * ‖p.2‖ := by simp [norm_smul, Real.norm_eq_abs]
    _ ≤ 1 * ‖p.1‖ + 1 * ‖p.2‖ :=
      add_le_add (mul_le_mul_of_nonneg_right (abs_sin_le_one _) (norm_nonneg _))
        (mul_le_mul_of_nonneg_right (abs_cos_le_one _) (norm_nonneg _))
    _ = _ := by ring

theorem hasDerivAt_rotation_fst (θ : ℝ) (p : E × E) :
    HasDerivAt (fun t => (ContinuousLinearMap.rotation t p).1)
      (ContinuousLinearMap.rotation θ p).2 θ := by
  exact ((hasDerivAt_cos θ).smul_const p.1).add
    ((hasDerivAt_sin θ).smul_const p.2)

theorem rotation_fundamental_theorem {f : E → ℝ} {df : E → StrongDual ℝ E}
    (hf : ∀ x, HasFDerivAt f (df x) x) (hdf : Continuous df) (p : E × E) :
    (∫ θ in (0 : ℝ)..π / 2,
      df (ContinuousLinearMap.rotation θ p).1 (ContinuousLinearMap.rotation θ p).2) =
        f p.2 - f p.1 := by
  have hd : ∀ θ, HasDerivAt (fun t => f (ContinuousLinearMap.rotation t p).1)
      (df (ContinuousLinearMap.rotation θ p).1 (ContinuousLinearMap.rotation θ p).2) θ :=
    fun θ => (hf _).comp_hasDerivAt θ (hasDerivAt_rotation_fst θ p)
  have hc : Continuous (fun θ =>
      df (ContinuousLinearMap.rotation θ p).1 (ContinuousLinearMap.rotation θ p).2) := by
    simp only [ContinuousLinearMap.rotation_apply]
    fun_prop
  have hi := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun θ _ => hd θ)
    (hc.intervalIntegrable 0 (π / 2))
  simpa [ContinuousLinearMap.rotation_apply] using hi

theorem rotation_exp_difference_le {f : E → ℝ} {df : E → StrongDual ℝ E}
    (hf : ∀ x, HasFDerivAt f (df x) x) (hdf : Continuous df) (r : ℝ) (p : E × E) :
    exp (r * (f p.2 - f p.1)) ≤ (π / 2)⁻¹ *
      ∫ θ in (0 : ℝ)..π / 2, exp (r * (π / 2) *
        df (ContinuousLinearMap.rotation θ p).1 (ContinuousLinearMap.rotation θ p).2) := by
  have hc : Continuous (fun θ => r * (π / 2) *
      df (ContinuousLinearMap.rotation θ p).1 (ContinuousLinearMap.rotation θ p).2) := by
    simp only [ContinuousLinearMap.rotation_apply]
    fun_prop
  have hJ := exp_interval_average_le (half_pos pi_pos) hc
  rw [intervalIntegral.integral_const_mul, rotation_fundamental_theorem hf hdf] at hJ
  convert hJ using 1
  all_goals try with_reducible_and_instances rfl
  congr 1
  field_simp

theorem exp_dual_le {L : ℝ≥0} (D : StrongDual ℝ E) (hD : ‖D‖ ≤ L) (r : ℝ) (y : E) :
    exp (r * D y) ≤ exp (|r| * L * ‖y‖) := by
  apply exp_le_exp.mpr
  calc
    r * D y ≤ |r * D y| := le_abs_self _
    _ = |r| * ‖D y‖ := by rw [abs_mul, Real.norm_eq_abs]
    _ ≤ |r| * (‖D‖ * ‖y‖) := mul_le_mul_of_nonneg_left (D.le_opNorm y) (abs_nonneg _)
    _ ≤ |r| * ((L : ℝ) * ‖y‖) := by gcongr
    _ = _ := by ring

theorem rotation_exp_dual_le {L : ℝ≥0} {df : E → StrongDual ℝ E}
    (hdf : ∀ x, ‖df x‖ ≤ L) (r θ : ℝ) (p : E × E) :
    exp (r * df (ContinuousLinearMap.rotation θ p).1 (ContinuousLinearMap.rotation θ p).2) ≤
      exp (|r| * L * ‖p.1‖) * exp (|r| * L * ‖p.2‖) := by
  calc
    _ ≤ exp (|r| * L * ‖(ContinuousLinearMap.rotation θ p).2‖) := exp_dual_le _ (hdf _) _ _
    _ ≤ exp (|r| * L * (‖p.1‖ + ‖p.2‖)) := by
      gcongr
      exact rotation_snd_norm_le θ p
    _ = _ := by rw [mul_add, exp_add]

end Rotation

section StandardGaussianRotation
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

theorem stdGaussian_integrable_variable_dual {df : E → StrongDual ℝ E} (hc : Continuous df)
    {L : ℝ≥0} (hdf : ∀ x, ‖df x‖ ≤ L) (r : ℝ) :
    Integrable (fun p : E × E => exp (r * df p.1 p.2))
      ((stdGaussian E).prod (stdGaussian E)) := by
  apply ((gaussian_integrable_exp_norm (μ := stdGaussian E) (|r| * L)).comp_snd
    (stdGaussian E)).mono' (by fun_prop)
  filter_upwards [] with p
  rw [Real.norm_eq_abs, abs_of_pos (exp_pos _)]
  exact exp_dual_le _ (hdf _) _ _

theorem stdGaussian_integral_variable_dual_le {df : E → StrongDual ℝ E} (hc : Continuous df)
    {L : ℝ≥0} (hdf : ∀ x, ‖df x‖ ≤ L) (r : ℝ) :
    (∫ p : E × E, exp (r * df p.1 p.2) ∂(stdGaussian E).prod (stdGaussian E)) ≤
      exp (r ^ 2 * (L : ℝ) ^ 2 / 2) := by
  have hi := stdGaussian_integrable_variable_dual hc hdf r
  have hio := hi.integral_prod_left
  simp only [stdGaussian_integral_exp_dual] at hio
  rw [integral_prod _ hi]
  simp only [stdGaussian_integral_exp_dual]
  calc
    _ ≤ ∫ _x : E, exp (r ^ 2 * (L : ℝ) ^ 2 / 2) ∂stdGaussian E := by
      apply integral_mono hio (integrable_const _)
      intro x
      apply exp_le_exp.mpr
      gcongr
      exact hdf x
    _ = _ := by simp

theorem stdGaussian_integral_rotation_variable_dual_le {df : E → StrongDual ℝ E}
    (hc : Continuous df) {L : ℝ≥0} (hdf : ∀ x, ‖df x‖ ≤ L) (r θ : ℝ) :
    (∫ p : E × E, exp (r * df (ContinuousLinearMap.rotation θ p).1
        (ContinuousLinearMap.rotation θ p).2) ∂(stdGaussian E).prod (stdGaussian E)) ≤
      exp (r ^ 2 * (L : ℝ) ^ 2 / 2) := by
  have hm := IsGaussian.map_rotation_eq_self (μ := stdGaussian E) (by simp) θ
  rw [← integral_map (ContinuousLinearMap.rotation θ).continuous.aemeasurable
    (f := fun p : E × E => exp (r * df p.1 p.2)) (by fun_prop), hm]
  exact stdGaussian_integral_variable_dual_le hc hdf r

theorem stdGaussian_integrable_rotation_variable_dual {df : E → StrongDual ℝ E}
    (hc : Continuous df) {L : ℝ≥0} (hdf : ∀ x, ‖df x‖ ≤ L) (r : ℝ)
    (ν : Measure ℝ) [IsFiniteMeasure ν] :
    Integrable (fun z : ℝ × (E × E) =>
      exp (r * df (ContinuousLinearMap.rotation z.1 z.2).1
        (ContinuousLinearMap.rotation z.1 z.2).2))
      (ν.prod ((stdGaussian E).prod (stdGaussian E))) := by
  have hI := gaussian_integrable_exp_norm (μ := stdGaussian E) (|r| * L)
  apply ((hI.mul_prod hI).comp_snd ν).mono'
  · simp only [ContinuousLinearMap.rotation_apply]
    fun_prop
  · filter_upwards [] with z
    rw [Real.norm_eq_abs, abs_of_pos (exp_pos _)]
    exact rotation_exp_dual_le hdf _ _ _

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
theorem lipschitz_of_bounded_derivative {f : E → ℝ} {df : E → StrongDual ℝ E}
    (hf : ∀ x, HasFDerivAt f (df x) x) {L : ℝ≥0} (hdf : ∀ x, ‖df x‖ ≤ L) :
    LipschitzWith L f := by
  apply lipschitzWith_of_nnnorm_fderiv_le (fun x => (hf x).differentiableAt)
  intro x
  rw [(hf x).fderiv]
  exact hdf x

lemma exp_mul_sub (r a b : ℝ) : exp (r * (a - b)) = exp (-r * b) * exp (r * a) := by
  rw [← exp_add]
  congr 1
  ring

theorem stdGaussian_integrable_exp_difference {f : E → ℝ} {L : ℝ≥0}
    (hf : LipschitzWith L f) (r : ℝ) :
    Integrable (fun p : E × E => exp (r * (f p.2 - f p.1)))
      ((stdGaussian E).prod (stdGaussian E)) := by
  simp_rw [exp_mul_sub]
  exact (gaussian_integrable_exp_lipschitz hf (-r)).mul_prod
    (gaussian_integrable_exp_lipschitz hf r)

theorem stdGaussian_mgf_difference_le {f : E → ℝ} {df : E → StrongDual ℝ E}
    (hf : ∀ x, HasFDerivAt f (df x) x) (hc : Continuous df)
    {L : ℝ≥0} (hdf : ∀ x, ‖df x‖ ≤ L) (r : ℝ) :
    (∫ p : E × E, exp (r * (f p.2 - f p.1)) ∂(stdGaussian E).prod (stdGaussian E)) ≤
      exp (π ^ 2 * r ^ 2 * (L : ℝ) ^ 2 / 8) := by
  let ν : Measure ℝ := volume.restrict (Ioc (0 : ℝ) (π / 2))
  have hν : IsFiniteMeasure ν := by dsimp [ν]; infer_instance
  let R := r * (π / 2)
  let G : ℝ → E × E → ℝ := fun θ p => exp (R *
    df (ContinuousLinearMap.rotation θ p).1 (ContinuousLinearMap.rotation θ p).2)
  have hI : Integrable (Function.uncurry G) (ν.prod ((stdGaussian E).prod (stdGaussian E))) :=
    stdGaussian_integrable_rotation_variable_dual hc hdf R ν
  have hD := stdGaussian_integrable_exp_difference (lipschitz_of_bounded_derivative hf hdf) r
  have hpos : 0 < π / 2 := half_pos pi_pos
  have hvol : ν.real univ = π / 2 := by
    simp [ν, measureReal_def, Real.volume_Ioc, hpos.le]
  have hpoint (p : E × E) : exp (r * (f p.2 - f p.1)) ≤
      (π / 2)⁻¹ * ∫ θ, G θ p ∂ν := by
    simpa only [intervalIntegral.integral_of_le hpos.le] using rotation_exp_difference_le hf hc r p
  calc
    _ ≤ ∫ p : E × E, (π / 2)⁻¹ * (∫ θ, G θ p ∂ν)
        ∂(stdGaussian E).prod (stdGaussian E) :=
      integral_mono hD (hI.integral_prod_right.const_mul _) hpoint
    _ = (π / 2)⁻¹ * ∫ θ, (∫ p : E × E, G θ p
        ∂(stdGaussian E).prod (stdGaussian E)) ∂ν := by
      rw [integral_const_mul, ← integral_integral_swap hI]
    _ ≤ (π / 2)⁻¹ * ∫ _θ, exp (R ^ 2 * (L : ℝ) ^ 2 / 2) ∂ν := by
      apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr hpos.le)
      apply integral_mono hI.integral_prod_left (integrable_const _)
      intro θ
      exact stdGaussian_integral_rotation_variable_dual_le hc hdf R θ
    _ = exp (π ^ 2 * r ^ 2 * (L : ℝ) ^ 2 / 8) := by
      rw [integral_const, smul_eq_mul, hvol, ← mul_assoc, inv_mul_cancel₀ hpos.ne', one_mul]
      congr 1
      dsimp [R]
      ring

theorem stdGaussian_mgf_centered_le {f : E → ℝ} {df : E → StrongDual ℝ E}
    (hf : ∀ x, HasFDerivAt f (df x) x) (hc : Continuous df)
    {L : ℝ≥0} (hdf : ∀ x, ‖df x‖ ≤ L) (r : ℝ) :
    (∫ x, exp (r * (f x - ∫ y, f y ∂stdGaussian E)) ∂stdGaussian E) ≤
      exp (π ^ 2 * r ^ 2 * (L : ℝ) ^ 2 / 8) := by
  have hLip := lipschitz_of_bounded_derivative hf hdf
  have hF := gaussian_integrable_lipschitz (μ := stdGaussian E) hLip
  have hG := gaussian_integrable_exp_lipschitz (μ := stdGaussian E) hLip (-r)
  have hpair := stdGaussian_integrable_exp_difference hLip (-r)
  have hcenter : Integrable (fun x => exp (r * (f x - ∫ y, f y ∂stdGaussian E)))
      (stdGaussian E) := by
    simp_rw [exp_mul_sub]
    exact (gaussian_integrable_exp_lipschitz hLip r).const_mul _
  have hj (x : E) : exp (r * (f x - ∫ y, f y ∂stdGaussian E)) ≤
      ∫ y, exp (r * (f x - f y)) ∂stdGaussian E := by
    have hsub := ((integrable_const (f x)).sub hF).const_mul r
    have he : Integrable (fun y => exp (r * (f x - f y))) (stdGaussian E) := by
      simp_rw [exp_mul_sub]
      exact hG.mul_const _
    have h := convexOn_exp.map_integral_le continuous_exp.continuousOn isClosed_univ
      (by filter_upwards [] with y; exact mem_univ _) hsub he
    simp only [Pi.sub_apply] at h
    simpa only [integral_const_mul, integral_sub (integrable_const _) hF,
      integral_const, probReal_univ, one_smul] using h
  have heq (x y : E) : r * (f x - f y) = -r * (f y - f x) := by ring
  simp_rw [heq] at hj
  calc
    _ ≤ ∫ x, (∫ y, exp (-r * (f y - f x)) ∂stdGaussian E) ∂stdGaussian E :=
      integral_mono hcenter hpair.integral_prod_left hj
    _ = ∫ p : E × E, exp (-r * (f p.2 - f p.1))
        ∂(stdGaussian E).prod (stdGaussian E) := (integral_prod _ hpair).symm
    _ ≤ exp (π ^ 2 * r ^ 2 * (L : ℝ) ^ 2 / 8) := by
      simpa using stdGaussian_mgf_difference_le hf hc hdf (-r)

theorem centered_mgf_le_of_uniform_dist {f g : E → ℝ} {L M : ℝ≥0}
    (hf : LipschitzWith L f) (hg : LipschitzWith M g) {δ : ℝ}
    (hfg : ∀ x, dist (f x) (g x) ≤ δ) (r : ℝ) :
    (∫ x, exp (r * (f x - ∫ y, f y ∂stdGaussian E)) ∂stdGaussian E) ≤
      exp (2 * |r| * δ) *
        (∫ x, exp (r * (g x - ∫ y, g y ∂stdGaussian E)) ∂stdGaussian E) := by
  let μ := stdGaussian E
  have hfi : Integrable f μ := gaussian_integrable_lipschitz hf
  have hgi : Integrable g μ := gaussian_integrable_lipschitz hg
  have hmean : |(∫ y, f y ∂μ) - ∫ y, g y ∂μ| ≤ δ := by
    have hi : ‖∫ x, f x - g x ∂μ‖ ≤ δ * μ.real univ :=
      norm_integral_le_of_norm_le_const (μ := μ)
        (Eventually.of_forall (fun x => by simpa only [dist_eq_norm] using hfg x))
    rw [integral_sub hfi hgi] at hi
    simpa only [Real.norm_eq_abs, probReal_univ, mul_one] using hi
  have he (h : E → ℝ) {K : ℝ≥0} (hh : LipschitzWith K h) :
      Integrable (fun x => exp (r * (h x - ∫ y, h y ∂μ))) μ := by
    simp_rw [exp_mul_sub]
    exact (gaussian_integrable_exp_lipschitz hh r).const_mul _
  rw [← integral_const_mul]
  apply integral_mono (he f hf) ((he g hg).const_mul _)
  intro x
  dsimp only
  rw [← exp_add]
  apply exp_le_exp.mpr
  have hdiff : |(f x - ∫ y, f y ∂μ) - (g x - ∫ y, g y ∂μ)| ≤ 2 * δ := by
    have hx : |f x - g x| ≤ δ := by simpa only [Real.dist_eq] using hfg x
    calc
      _ = |(f x - g x) - ((∫ y, f y ∂μ) - ∫ y, g y ∂μ)| := by congr 1; ring
      _ ≤ |f x - g x| + |(∫ y, f y ∂μ) - ∫ y, g y ∂μ| := by
        simpa only [Real.norm_eq_abs] using norm_sub_le
          (f x - g x) ((∫ y, f y ∂μ) - ∫ y, g y ∂μ)
      _ ≤ 2 * δ := by linarith
  have hh := le_abs_self (r * ((f x - ∫ y, f y ∂μ) - (g x - ∫ y, g y ∂μ)))
  rw [abs_mul] at hh
  have hb := mul_le_mul_of_nonneg_left hdiff (abs_nonneg r)
  dsimp [μ] at *
  nlinarith

end StandardGaussianRotation
end SKGap
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Gaussian_StdGaussianMgfLipschitz
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
section StandardGaussianRotation
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

theorem stdGaussian_mgf_lipschitz_le {f : E → ℝ} {L : ℝ≥0}
    (hf : LipschitzWith L f) (r : ℝ) :
    (∫ x, exp (r * (f x - ∫ y, f y ∂stdGaussian E)) ∂stdGaussian E) ≤
      exp (π ^ 2 * r ^ 2 * (L : ℝ) ^ 2 / 8) := by
  have hε (ε : ℝ) (hε : 0 < ε) :
      (∫ x, exp (r * (f x - ∫ y, f y ∂stdGaussian E)) ∂stdGaussian E) ≤
        exp (2 * |r| * ((L : ℝ) * ε)) * exp (π ^ 2 * r ^ 2 * (L : ℝ) ^ 2 / 8) := by
    obtain ⟨g, hgs, hgl, hgf⟩ := exists_smooth_lipschitz_approx hf hε
    have hmg := stdGaussian_mgf_centered_le
      (fun x => (hgs.differentiable (by simp) x).hasFDerivAt)
      (hgs.continuous_fderiv (by simp)) (fun _ => norm_fderiv_le_of_lipschitz ℝ hgl) r
    exact (centered_mgf_le_of_uniform_dist hf hgl
      (fun x => by simpa only [dist_comm] using hgf x) r).trans
        (mul_le_mul_of_nonneg_left hmg (exp_pos _).le)
  have ht : Tendsto (fun ε : ℝ => exp (2 * |r| * ((L : ℝ) * ε)) *
      exp (π ^ 2 * r ^ 2 * (L : ℝ) ^ 2 / 8)) (𝓝[>] 0)
      (𝓝 (exp (π ^ 2 * r ^ 2 * (L : ℝ) ^ 2 / 8))) := by
    have hc : Continuous (fun ε : ℝ => exp (2 * |r| * ((L : ℝ) * ε)) *
      exp (π ^ 2 * r ^ 2 * (L : ℝ) ^ 2 / 8)) := by fun_prop
    simpa using ((hc.tendsto 0).mono_left (nhdsWithin_le_nhds (s := Ioi (0 : ℝ))))
  apply ge_of_tendsto ht
  filter_upwards [self_mem_nhdsWithin] with ε heps
  exact hε ε heps

theorem stdGaussian_upper_tail_lipschitz {f : E → ℝ} {L : ℝ≥0}
    (hf : LipschitzWith L f) (hL : 0 < L) {u : ℝ} (hu : 0 ≤ u) :
    (stdGaussian E).real {x | u ≤ f x - ∫ y, f y ∂stdGaussian E} ≤
      exp (-2 * u ^ 2 / (π ^ 2 * (L : ℝ) ^ 2)) := by
  let t : ℝ := 4 * u / (π ^ 2 * (L : ℝ) ^ 2)
  have hLr : 0 < (L : ℝ) := hL
  have hden : 0 < π ^ 2 * (L : ℝ) ^ 2 := mul_pos (sq_pos_of_pos pi_pos) (sq_pos_of_pos hLr)
  have ht : 0 ≤ t := div_nonneg (mul_nonneg (by norm_num) hu) hden.le
  have hi : Integrable (fun x => exp (t * (f x - ∫ y, f y ∂stdGaussian E)))
      (stdGaussian E) := by
    simp_rw [exp_mul_sub]
    exact (gaussian_integrable_exp_lipschitz hf t).const_mul _
  calc
    _ ≤ exp (-t * u) * ∫ x, exp (t * (f x - ∫ y, f y ∂stdGaussian E))
        ∂stdGaussian E := measure_ge_le_exp_mul_mgf u ht hi
    _ ≤ exp (-t * u) * exp (π ^ 2 * t ^ 2 * (L : ℝ) ^ 2 / 8) :=
      mul_le_mul_of_nonneg_left (stdGaussian_mgf_lipschitz_le hf t) (exp_pos _).le
    _ = exp (-2 * u ^ 2 / (π ^ 2 * (L : ℝ) ^ 2)) := by
      rw [← exp_add]
      congr 1
      dsimp [t]
      field_simp
      ring

theorem stdGaussian_lower_tail_lipschitz {f : E → ℝ} {L : ℝ≥0}
    (hf : LipschitzWith L f) (hL : 0 < L) {u : ℝ} (hu : 0 ≤ u) :
    (stdGaussian E).real {x | f x - ∫ y, f y ∂stdGaussian E ≤ -u} ≤
      exp (-2 * u ^ 2 / (π ^ 2 * (L : ℝ) ^ 2)) := by
  have h := stdGaussian_upper_tail_lipschitz hf.neg hL hu
  have he : {x | (fun x => -f x) x - ∫ y, -f y ∂stdGaussian E ≥ u} =
      {x | f x - ∫ y, f y ∂stdGaussian E ≤ -u} := by
    ext x
    simp only [mem_ofPred_eq, integral_neg]
    constructor <;> intro hx <;> linarith
  simp only [Pi.neg_apply] at h
  rw [he] at h
  exact h

theorem stdGaussian_tail_lipschitz {f : E → ℝ} {L : ℝ≥0}
    (hf : LipschitzWith L f) (hL : 0 < L) {u : ℝ} (hu : 0 ≤ u) :
    (stdGaussian E).real {x | u ≤ |f x - ∫ y, f y ∂stdGaussian E|} ≤
      2 * exp (-2 * u ^ 2 / (π ^ 2 * (L : ℝ) ^ 2)) := by
  have he : {x | u ≤ |f x - ∫ y, f y ∂stdGaussian E|} =
      {x | u ≤ f x - ∫ y, f y ∂stdGaussian E} ∪
      {x | f x - ∫ y, f y ∂stdGaussian E ≤ -u} := by
    ext x
    simp only [mem_union, mem_ofPred_eq, le_abs]
    constructor <;> rintro (hx | hx)
    · exact Or.inl hx
    · right; linarith
    · exact Or.inl hx
    · right; linarith
  rw [he]
  calc
    _ ≤ (stdGaussian E).real {x | u ≤ f x - ∫ y, f y ∂stdGaussian E} +
        (stdGaussian E).real {x | f x - ∫ y, f y ∂stdGaussian E ≤ -u} :=
      measureReal_union_le _ _
    _ ≤ exp (-2 * u ^ 2 / (π ^ 2 * (L : ℝ) ^ 2)) +
        exp (-2 * u ^ 2 / (π ^ 2 * (L : ℝ) ^ 2)) :=
      add_le_add (stdGaussian_upper_tail_lipschitz hf hL hu)
        (stdGaussian_lower_tail_lipschitz hf hL hu)
    _ = _ := by ring

end StandardGaussianRotation
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
-- module Solutions.OAIQ072_SK.SKGap_Matrix_MatrixEntryCLM
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
namespace SKGap
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma matrixEntry_lipschitz (i k : ι) : LipschitzWith 1 (fun M : Matrix ι ι ℝ => M i k) := by
  apply LipschitzWith.of_dist_le_mul
  intro M N
  simpa only [dist_eq_norm,Real.norm_eq_abs,NNReal.coe_one,one_mul,Matrix.sub_apply] using!
    matrix_entry_le_frobenius (M-N) i k

end SKGap

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

lemma goeEntry_memLp (r : ℝ) (i b : ι) :
    MemLp (fun g => goeMatrix r g i b) 2
      (Measure.pi (fun _ : MatrixCoordinates ι => gaussianReal 0 1)) := by
  exact ((gaussianCoordinate_memLp (.inl (i,b))).add
    (gaussianCoordinate_memLp (.inl (b,i)))).const_mul _

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
-- module Solutions.OAIQ072_SK.SKGap_Localization_Conjugation
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

lemma conjugate_opNorm (U : unitary (Matrix ι ι ℂ)) (M : Matrix ι ι ℂ) :
    opNorm (conjugate U M) = opNorm M := by
  change ‖lin ((U : Matrix ι ι ℂ)*M*(U : Matrix ι ι ℂ)ᴴ)‖ = _
  rw [lin_mul,lin_mul]
  have hstar : lin ((U : Matrix ι ι ℂ)ᴴ) ∈ unitary _ := lin_unitary _ (Unitary.star_mem U.property)
  rw [CStarRing.norm_mul_mem_unitary _ hstar,
    CStarRing.norm_mem_unitary_mul _ (lin_unitary _ U.property)]
  rfl

lemma matrixProject_conjugate (U : unitary (Matrix ι ι ℂ)) {R : ℝ} (hR : 0 ≤ R)
    (M : Matrix ι ι ℂ) :
    matrixProject R hR (conjugate U M) = conjugate U (matrixProject R hR M) := by
  apply convexProject_equivariant (hermitianBall_good hR) (conjugateIsometry U)
  intro N
  change ((conjugate U N)ᴴ = conjugate U N ∧ opNorm (conjugate U N) ≤ R) ↔
    (Nᴴ = N ∧ opNorm N ≤ R)
  have hh : (conjugate U N)ᴴ = conjugate U Nᴴ := (map_star (conjugate U) N).symm
  have he : conjugate U Nᴴ = conjugate U N ↔ Nᴴ=N :=
    ⟨fun h => (conjugate U).injective h,fun h => congrArg (conjugate U) h⟩
  rw [hh,he,conjugate_opNorm]

lemma truncatedG_conjugate (f : 𝓢(ℝ,ℂ)) (U : unitary (Matrix ι ι ℂ)) {R : ℝ} (hR : 0 ≤ R)
    (B D M : Matrix ι ι ℂ) (hB : Bᴴ=B) (hD : Dᴴ=D) :
    truncatedG f R hR (conjugate U B) (conjugate U D) (conjugate U M) =
      conjugate U (truncatedG f R hR B D M) := by
  have hs : sandShift (conjugate U B) (conjugate U D) (matrixProject R hR (conjugate U M)) =
      conjugate U (sandShift B D (matrixProject R hR M)) := by
    simp only [sandShift,matrixProject_conjugate,map_sub,map_mul]
  unfold truncatedG
  rw [hs,schwartzMatrix_conjugate f U _
    (sandShift_hermitian _ _ _ hB hD (matrixProject_bound R hR M).1)]
  simp only [map_mul]

lemma truncatedK_conjugate (f : 𝓢(ℝ,ℂ)) (U : unitary (Matrix ι ι ℂ)) {R : ℝ} (hR : 0 ≤ R)
    (B D C M : Matrix ι ι ℂ) (hB : Bᴴ=B) (hD : Dᴴ=D) :
    truncatedK f R hR (conjugate U B) (conjugate U D) (conjugate U C) (conjugate U M) =
      conjugate U (truncatedK f R hR B D C M) := by
  simp only [truncatedK,truncatedG_conjugate f U hR B D M hB hD,matrixProject_conjugate,
    map_add,map_one,map_mul,map_sub]
end SKGap.ComplexMatrix
end
end

section
noncomputable section
namespace SKGap
open Matrix MeasureTheory ProbabilityTheory
open RealComplex ComplexMatrix
open scoped Matrix.Norms.Frobenius SchwartzMap
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma sign_conjugate_entry (s : ι → ℝ) (hs : ∀ i, s i^2=1) (M : Matrix ι ι ℂ) (i k : ι) :
    conjugate (signUnitary s hs) M i k = (s i:ℂ)*(s k:ℂ)*M i k := by
  change (diagonal (fun b => (s b:ℂ))*M*(diagonal (fun b => (s b:ℂ)))ᴴ) i k = _
  simp only [diagonal_conjTranspose,Pi.star_apply,Complex.star_def,Complex.conj_ofReal,mul_diagonal,diagonal_mul]
  ring

lemma sign_conjugate_diagonal (s : ι → ℝ) (hs : ∀ i, s i^2=1) (d : ι → ℝ) :
    conjugate (signUnitary s hs) (liftMatrix (diagonal d)) = liftMatrix (diagonal d) := by
  ext i k
  rw [sign_conjugate_entry]
  by_cases hik : i=k
  · subst k
    simp only [liftMatrix,Matrix.map_apply,diagonal_apply_eq]
    have h : (s i:ℂ)*(s i:ℂ)=1 := by exact_mod_cast (show s i*s i=1 by nlinarith [hs i])
    rw [h,one_mul]
  · simp [liftMatrix,Matrix.diagonal,hik]

lemma sign_conjugate_lift (s : ι → ℝ) (hs : ∀ i, s i^2=1) (M : Matrix ι ι ℝ) :
    conjugate (signUnitary s hs) (liftMatrix M) = liftMatrix (signConjugate s M) := by
  ext i k
  simp [sign_conjugate_entry,liftMatrix,signConjugate]

lemma realPart_sign_conjugate (s : ι → ℝ) (hs : ∀ i, s i^2=1) (M : Matrix ι ι ℂ) :
    RealComplex.realPart (conjugate (signUnitary s hs) M) = signConjugate s (RealComplex.realPart M) := by
  ext i k
  simp [RealComplex.realPart,sign_conjugate_entry,signConjugate,Complex.mul_re]

lemma realTruncatedK_sign (f : 𝓢(ℝ,ℂ)) {R : ℝ} (hR : 0 ≤ R)
    (s : ι → ℝ) (hs : ∀ i, s i^2=1) (d c : ι → ℝ) (M : Matrix ι ι ℝ) :
    realTruncatedK f R hR (diagonal d) (diagonal c) (signConjugate s M) =
      signConjugate s (realTruncatedK f R hR (diagonal d) (diagonal c) M) := by
  unfold realTruncatedK
  rw [← sign_conjugate_lift s hs M]
  have hd := liftMatrix_hermitian (diagonal d) (diagonal_transpose _)
  have hc := liftMatrix_hermitian (diagonal c) (diagonal_transpose _)
  have hB : (1+liftMatrix (diagonal d)*liftMatrix (diagonal c)*liftMatrix (diagonal d))ᴴ =
      1+liftMatrix (diagonal d)*liftMatrix (diagonal c)*liftMatrix (diagonal d) := by
    simp only [conjTranspose_add,conjTranspose_one,conjTranspose_mul,hd,hc,mul_assoc]
  have he := truncatedK_conjugate f (signUnitary s hs) hR
    (1+liftMatrix (diagonal d)*liftMatrix (diagonal c)*liftMatrix (diagonal d))
    (liftMatrix (diagonal d)) (liftMatrix (diagonal c)) (liftMatrix M) hB hd
  simp only [map_add,map_one,map_mul,sign_conjugate_diagonal] at he
  rw [he,realPart_sign_conjugate]
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

omit [DecidableEq ι] in
lemma signConjugate_mul (s : ι → ℝ) (hs : ∀ i, s i^2=1) (M N : Matrix ι ι ℝ) :
    signConjugate s (M*N) = signConjugate s M*signConjugate s N := by
  ext i k
  change s i*s k*(∑ b, M i b*N b k) = ∑ b, (s i*s b*M i b)*(s b*s k*N b k)
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro b _
  calc
    _ = (s i*s k*(M i b*N b k))*1 := by ring
    _ = (s i*s k*(M i b*N b k))*(s b)^2 := by rw [hs b]
    _ = _ := by ring

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

lemma realProject_sign {R : ℝ} (hR : 0 ≤ R) (s : ι → ℝ) (hs : ∀ i, s i^2=1)
    (M : Matrix ι ι ℝ) : realProject R hR (signConjugate s M) = signConjugate s (realProject R hR M) := by
  unfold realProject
  rw [← sign_conjugate_lift s hs M,ComplexMatrix.matrixProject_conjugate,realPart_sign_conjugate]

lemma realProjectedProduct_sub_norm {R B L : ℝ} (hR : 0 ≤ R)
    (K : Matrix ι ι ℝ → Matrix ι ι ℝ) (hK : ∀ M, opNorm (K M) ≤ B)
    (hLip : ∀ M N, ‖K M-K N‖ ≤ L*‖M-N‖) (M N : Matrix ι ι ℝ) :
    ‖realProject R hR M*K M-realProject R hR N*K N‖ ≤ (B+R*L)*‖M-N‖ := by
  have he : realProject R hR M*K M-realProject R hR N*K N =
      (realProject R hR M-realProject R hR N)*K M+realProject R hR N*(K M-K N) := by noncomm_ring
  rw [he]
  apply (norm_add_le _ _).trans
  calc
    _ ≤ ‖realProject R hR M-realProject R hR N‖*opNorm (K M)+
        opNorm (realProject R hR N)*‖K M-K N‖ :=
      add_le_add (frobenius_mul_le_opNorm_right _ _) (frobenius_mul_le_opNorm _ _)
    _ ≤ ‖M-N‖*B+R*(L*‖M-N‖) := by
      apply add_le_add
      · exact mul_le_mul (realProject_sub_norm hR M N) (hK M) (norm_nonneg _) (norm_nonneg _)
      · exact mul_le_mul (realProject_opNorm hR N) (hLip M N) (norm_nonneg _) hR
    _ = _ := by ring
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

lemma pathK_sign (f : 𝓢(ℝ,ℂ)) {R : ℝ} (hR : 0 ≤ R) (j : ℝ) (a : ι → ℝ)
    (z : ℝ) (s : ι → ℝ) (hs : ∀ i, s i^2=1) (M : Matrix ι ι ℝ) :
    pathK f R hR j a z (signConjugate s M)=signConjugate s (pathK f R hR j a z M) :=
  realTruncatedK_sign f hR s hs _ _ M

end SKGap
end
end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Gaussian_GaussianSign
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
namespace SKGap
open Matrix MeasureTheory ProbabilityTheory
open scoped BigOperators

lemma gaussianSign_map {κ : Type*} [Fintype κ] (q : κ → ℝ) (hq : ∀ b, q b^2=1) :
    (Measure.pi (fun _ : κ => gaussianReal 0 1)).map (gaussianSignEquiv q hq) =
      Measure.pi (fun _ : κ => gaussianReal 0 1) := by
  have he (b : κ) : (gaussianReal 0 1).map (fun x => q b*x) = gaussianReal 0 1 := by
    rcases sq_eq_one_iff.mp (hq b) with h|h
    · simp [h]
    · simpa only [h,neg_one_mul,neg_zero] using (gaussianReal_map_neg (μ := (0:ℝ)) (v := 1))
  change (Measure.pi (fun _ : κ => gaussianReal 0 1)).map (fun g b => q b*g b) = _
  rw [Measure.pi_map_pi (fun _ => by fun_prop)]
  simp only [he]

lemma gaussianSign_integral {κ : Type*} [Fintype κ] (q : κ → ℝ) (hq : ∀ b, q b^2=1)
    (F : (κ → ℝ) → ℝ) :
    (∫ g, F (gaussianSignEquiv q hq g) ∂Measure.pi (fun _ : κ => gaussianReal 0 1)) =
      ∫ g, F g ∂Measure.pi (fun _ : κ => gaussianReal 0 1) := by
  rw [← integral_map_equiv,gaussianSign_map]

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [Fintype ι] [DecidableEq ι] in
lemma goeMatrix_sign (r : ℝ) (s : ι → ℝ) (hs : ∀ i, s i^2=1)
    (g : MatrixCoordinates ι → ℝ) :
    goeMatrix r (gaussianSignEquiv (goeSign s) (goeSign_sq s hs) g) =
      signConjugate s (goeMatrix r g) := by
  ext i k
  dsimp [goeMatrix,gaussianSignEquiv,goeSign,signConjugate]
  ring

lemma goe_equivariant_offdiag (r : ℝ) (F : Matrix ι ι ℝ → Matrix ι ι ℝ)
    (hF : ∀ (s : ι → ℝ), (∀ i, s i^2=1) → ∀ M,
      F (signConjugate s M)=signConjugate s (F M)) (i k : ι) (hik : i ≠ k) :
    (∫ g, F (goeMatrix r g) i k ∂Measure.pi (fun _ : MatrixCoordinates ι => gaussianReal 0 1))=0 := by
  let s : ι → ℝ := fun b => if b=i then -1 else 1
  have hs : ∀ b, s b^2=1 := by intro b; dsimp [s]; split <;> norm_num
  have hi := gaussianSign_integral (goeSign s) (goeSign_sq s hs) (fun g => F (goeMatrix r g) i k)
  have hsi : s i = -1 := by simp [s]
  have hsk : s k = 1 := by simp [s,Ne.symm hik]
  have heq : (fun g => F (goeMatrix r (gaussianSignEquiv (goeSign s) (goeSign_sq s hs) g)) i k) =
      (fun g => -F (goeMatrix r g) i k) := by
    funext g
    rw [goeMatrix_sign r s hs g,hF s hs]
    change s i*s k*F (goeMatrix r g) i k = _
    rw [hsi,hsk,neg_one_mul,neg_mul,one_mul]
  rw [heq,integral_neg] at hi
  linarith
end SKGap
end
end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Localization_Bilinear
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
namespace SKGap
open Matrix MeasureTheory ProbabilityTheory Real
open scoped BigOperators Matrix.Norms.Frobenius NNReal ENNReal
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma operator_le_frobenius (M : Matrix ι ι ℝ) : opNorm M ≤ ‖M‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
  intro x
  have hh := Matrix.frobenius_norm_mul M (Matrix.replicateCol Unit (fun i => x i))
  rw [← Matrix.replicateCol_mulVec,Matrix.frobenius_norm_replicateCol,
    Matrix.frobenius_norm_replicateCol] at hh
  exact hh

lemma matrixBilinear_inner (M : Matrix ι ι ℝ) (u v : EuclideanSpace ℝ ι) :
    matrixBilinear M u v = inner ℝ u (M.toEuclideanLin.toContinuousLinearMap v) := by
  change (∑ i, ∑ k, u i*M i k*v k) = ∑ i, (∑ k, M i k*v k)*u i
  simp only [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro k _
  ring

lemma matrixBilinear_abs_le (M : Matrix ι ι ℝ) (u v : EuclideanSpace ℝ ι) :
    |matrixBilinear M u v| ≤ opNorm M*‖u‖*‖v‖ := by
  rw [matrixBilinear_inner]
  calc
    _ ≤ ‖u‖*‖M.toEuclideanLin.toContinuousLinearMap v‖ := abs_real_inner_le_norm _ _
    _ ≤ ‖u‖*(opNorm M*‖v‖) := mul_le_mul_of_nonneg_left
      (M.toEuclideanLin.toContinuousLinearMap.le_opNorm v) (norm_nonneg _)
    _ = _ := by ring

lemma matrixBilinear_frobenius (M : Matrix ι ι ℝ) (u v : EuclideanSpace ℝ ι) :
    |matrixBilinear M u v| ≤ ‖M‖*‖u‖*‖v‖ :=
  (matrixBilinear_abs_le M u v).trans (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right (operator_le_frobenius M) (norm_nonneg _)) (norm_nonneg _))

omit [DecidableEq ι] in
lemma matrixBilinear_sub (M N : Matrix ι ι ℝ) (u v : EuclideanSpace ℝ ι) :
    matrixBilinear (M-N) u v = matrixBilinear M u v-matrixBilinear N u v := by
  simp only [matrixBilinear,Matrix.sub_apply,mul_sub,sub_mul,Finset.sum_sub_distrib]

omit [DecidableEq ι] in
lemma matrixBilinear_integral {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (F : Ω → Matrix ι ι ℝ) (hF : ∀ i k, Integrable (fun x => F x i k) μ)
    (u v : EuclideanSpace ℝ ι) :
    (∫ x, matrixBilinear (F x) u v ∂μ) =
      matrixBilinear (fun i k => ∫ x, F x i k ∂μ) u v := by
  unfold matrixBilinear
  rw [integral_finsetSum _ (fun i _ => integrable_finsetSum _
    (fun k _ => ((hF i k).const_mul (u i)).mul_const (v k)))]
  apply Finset.sum_congr rfl
  intro i _
  rw [integral_finsetSum _ (fun k _ => ((hF i k).const_mul (u i)).mul_const (v k))]
  simp only [integral_mul_const,integral_const_mul]

lemma matrixBilinear_diagonal_error {e : ι → ℝ} {ε : ℝ} (hε : 0 ≤ ε)
    (he : ∀ i, |e i| ≤ ε) (u v : EuclideanSpace ℝ ι) :
    |matrixBilinear (diagonal e) u v| ≤ ε*‖u‖*‖v‖ :=
  (matrixBilinear_abs_le _ _ _).trans (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right (opNorm_diagonal_le hε he) (norm_nonneg _)) (norm_nonneg _))

lemma goe_bilinear_lipschitz (r : ℝ) (F : Matrix ι ι ℝ → Matrix ι ι ℝ)
    {L : ℝ} (hL : 0 ≤ L) (hF : ∀ M N, ‖F M-F N‖ ≤ L*‖M-N‖)
    (u v : EuclideanSpace ℝ ι) :
    LipschitzWith ⟨L*‖u‖*‖v‖*sqrt (2*r),by positivity⟩
      (fun g : EuclideanSpace ℝ (MatrixCoordinates ι) => matrixBilinear (F (goeMatrix r g)) u v) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  simp only [dist_eq_norm,Real.norm_eq_abs]
  rw [← matrixBilinear_sub]
  calc
    _ ≤ ‖F (goeMatrix r x)-F (goeMatrix r y)‖*‖u‖*‖v‖ := matrixBilinear_frobenius _ _ _
    _ ≤ (L*‖goeMatrix r x-goeMatrix r y‖)*‖u‖*‖v‖ :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (hF _ _) (norm_nonneg _)) (norm_nonneg _)
    _ ≤ (L*(sqrt (2*r)*‖x-y‖))*‖u‖*‖v‖ := by
      apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
      apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
      apply mul_le_mul_of_nonneg_left _ hL
      exact (goeMatrix_L2_lipschitz r).norm_sub_le x y
    _ = _ := by change _ = (L*‖u‖*‖v‖*sqrt (2*r))*‖x-y‖; ring

end SKGap

namespace SKGap
open MeasureTheory ProbabilityTheory Real
open scoped NNReal ENNReal
lemma gaussianProduct_tail_lipschitz {κ : Type*} [Fintype κ]
    {f : (κ → ℝ) → ℝ} {L : ℝ≥0}
    (hf : LipschitzWith L (fun x : EuclideanSpace ℝ κ => f x.ofLp))
    (hL : 0 < L) {u : ℝ} (hu : 0 ≤ u) :
    (Measure.pi (fun _ : κ => gaussianReal 0 1)).real
      {x | u ≤ |f x - ∫ y, f y ∂Measure.pi (fun _ : κ => gaussianReal 0 1)|} ≤
      2*exp (-2*u^2/(π^2*(L:ℝ)^2)) := by
  let e : (κ → ℝ) ≃ᵐ EuclideanSpace ℝ κ := MeasurableEquiv.toLp 2 _
  have hp : MeasurePreserving e (Measure.pi (fun _ : κ => gaussianReal 0 1))
      (stdGaussian (EuclideanSpace ℝ κ)) := ⟨e.measurable,map_pi_eq_stdGaussian⟩
  have hi := hp.integral_comp' (fun x : EuclideanSpace ℝ κ => f x.ofLp)
  change (∫ x, f x ∂Measure.pi (fun _ : κ => gaussianReal 0 1)) = _ at hi
  have h := stdGaussian_tail_lipschitz hf hL hu
  rw [← hi] at h
  have hs : MeasurableSet {x : EuclideanSpace ℝ κ |
      u ≤ |f x.ofLp-∫ y, f y ∂Measure.pi (fun _ : κ => gaussianReal 0 1)|} :=
    measurableSet_le measurable_const ((hf.continuous.measurable.sub_const _).abs)
  have he := congrArg ENNReal.toReal (hp.measure_preimage hs.nullMeasurableSet)
  change (Measure.pi (fun _ : κ => gaussianReal 0 1)).real
      {x | u ≤ |f x-∫ y, f y ∂Measure.pi (fun _ : κ => gaussianReal 0 1)|} = _ at he
  rw [he]
  exact h
end SKGap
end
end

section
noncomputable section
namespace SKGap
open Matrix MeasureTheory ProbabilityTheory Real Set
open scoped BigOperators Matrix.Norms.Frobenius NNReal ENNReal
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma goe_entries_integrable (r : ℝ) (F : Matrix ι ι ℝ → Matrix ι ι ℝ)
    {L : ℝ} (hL : 0 ≤ L) (hF : ∀ M N, ‖F M-F N‖ ≤ L*‖M-N‖) (i k : ι) :
    Integrable (fun g => F (goeMatrix r g) i k)
      (Measure.pi (fun _ : MatrixCoordinates ι => gaussianReal 0 1)) := by
  have hf : LipschitzWith ⟨L,hL⟩ F := by
    apply LipschitzWith.of_dist_le_mul
    intro M N
    change ‖F M-F N‖ ≤ L*‖M-N‖
    exact hF M N
  exact gaussianProduct_integrable_lipschitz ((matrixEntry_lipschitz i k).comp
    (hf.comp (goeMatrix_L2_lipschitz r)))

lemma goe_bilinear_bias (r : ℝ) (F : Matrix ι ι ℝ → Matrix ι ι ℝ)
    (hF : ∀ (s : ι → ℝ), (∀ i, s i^2=1) → ∀ M,
      F (signConjugate s M)=signConjugate s (F M))
    (hI : ∀ i k, Integrable (fun g => F (goeMatrix r g) i k)
      (Measure.pi (fun _ : MatrixCoordinates ι => gaussianReal 0 1)))
    (d : ι → ℝ) {ε : ℝ} (hε : 0 ≤ ε)
    (hd : ∀ i, |(∫ g, F (goeMatrix r g) i i
      ∂Measure.pi (fun _ : MatrixCoordinates ι => gaussianReal 0 1))-d i| ≤ ε)
    (u v : EuclideanSpace ℝ ι) :
    |(∫ g, matrixBilinear (F (goeMatrix r g)) u v
      ∂Measure.pi (fun _ : MatrixCoordinates ι => gaussianReal 0 1))-
      matrixBilinear (diagonal d) u v| ≤ ε*‖u‖*‖v‖ := by
  let e : ι → ℝ := fun i => ∫ g, F (goeMatrix r g) i i
    ∂Measure.pi (fun _ : MatrixCoordinates ι => gaussianReal 0 1)
  have he : (fun i k => ∫ g, F (goeMatrix r g) i k
      ∂Measure.pi (fun _ : MatrixCoordinates ι => gaussianReal 0 1)) = diagonal e := by
    ext i k
    by_cases hik : i=k
    · subst k; simp only [diagonal_apply_eq]; rfl
    · rw [diagonal_apply_ne _ hik]
      exact goe_equivariant_offdiag r F hF i k hik
  rw [matrixBilinear_integral _ _ hI,he,← matrixBilinear_sub,diagonal_sub]
  exact matrixBilinear_diagonal_error hε hd u v

lemma gaussianProduct_tail_from_bias {κ : Type*} [Fintype κ]
    {f : (κ → ℝ) → ℝ} {L : ℝ≥0}
    (hf : LipschitzWith L (fun x : EuclideanSpace ℝ κ => f x.ofLp))
    (hL : 0 < L) {a b t : ℝ} (hb : |(∫ x, f x
      ∂Measure.pi (fun _ : κ => gaussianReal 0 1))-a| ≤ b) (ht : 0 ≤ t) :
    (Measure.pi (fun _ : κ => gaussianReal 0 1)).real {x | b+t ≤ |f x-a|} ≤
      2*exp (-2*t^2/(π^2*(L:ℝ)^2)) := by
  let μ := Measure.pi (fun _ : κ => gaussianReal 0 1)
  apply (measureReal_mono (show {x | b+t ≤ |f x-a|} ⊆
      {x | t ≤ |f x-∫ y, f y ∂μ|} from ?_)).trans (gaussianProduct_tail_lipschitz hf hL ht)
  intro x hx
  have hh : |f x-a| ≤ |f x-∫ y, f y ∂μ|+|(∫ y, f y ∂μ)-a| := abs_sub_le _ _ _
  change b+t ≤ |f x-a| at hx
  change t ≤ |f x-∫ y, f y ∂μ|
  linarith

lemma goe_bilinear_uniform_lipschitz (r : ℝ) (F : Matrix ι ι ℝ → Matrix ι ι ℝ)
    {L U : ℝ} (hL : 0 ≤ L) (hU : 0 ≤ U) (hF : ∀ M N, ‖F M-F N‖ ≤ L*‖M-N‖)
    (u v : EuclideanSpace ℝ ι) (hu : ‖u‖ ≤ U) (hv : ‖v‖ ≤ U) :
    LipschitzWith ⟨(L+1)*(U+1)^2*sqrt (2*r),by positivity⟩
      (fun g : EuclideanSpace ℝ (MatrixCoordinates ι) => matrixBilinear (F (goeMatrix r g)) u v) := by
  apply (goe_bilinear_lipschitz r F hL hF u v).weaken
  change L*‖u‖*‖v‖*sqrt (2*r) ≤ (L+1)*(U+1)^2*sqrt (2*r)
  apply mul_le_mul_of_nonneg_right _ (sqrt_nonneg _)
  calc
    _ ≤ (L+1)*(U+1)*(U+1) := by gcongr <;> linarith
    _ = _ := by ring

lemma goe_bilinear_concentration {j L U ε t : ℝ} (hj : 0 < j) (hL : 0 ≤ L)
    (hU : 0 ≤ U) (hε : 0 ≤ ε) (ht : 0 ≤ t) [Nonempty ι]
    (F : Matrix ι ι ℝ → Matrix ι ι ℝ)
    (hF : ∀ (s : ι → ℝ), (∀ i, s i^2=1) → ∀ M,
      F (signConjugate s M)=signConjugate s (F M))
    (hLip : ∀ M N, ‖F M-F N‖ ≤ L*‖M-N‖)
    (d : ι → ℝ)
    (hd : ∀ i, |(∫ g, F (goeMatrix (j/(Fintype.card ι:ℝ)) g) i i
      ∂Measure.pi (fun _ : MatrixCoordinates ι => gaussianReal 0 1))-d i| ≤ ε)
    (u v : EuclideanSpace ℝ ι) (hu : ‖u‖ ≤ U) (hv : ‖v‖ ≤ U) :
    (Measure.pi (fun _ : MatrixCoordinates ι => gaussianReal 0 1)).real
      {g | ε*U^2+t ≤ |matrixBilinear (F (goeMatrix (j/(Fintype.card ι:ℝ)) g)-diagonal d) u v|} ≤
      2*exp (-(Fintype.card ι:ℝ)*t^2/(π^2*((L+1)*(U+1)^2)^2*j)) := by
  let n : ℝ := Fintype.card ι
  let r := j/n
  let C := (L+1)*(U+1)^2
  have hn : 0 < n := Nat.cast_pos.mpr Fintype.card_pos
  have hr : 0 < r := div_pos hj hn
  have hC : 0 < C := by dsimp [C]; positivity
  have hCF : LipschitzWith ⟨C*sqrt (2*r),by positivity⟩
      (fun g : EuclideanSpace ℝ (MatrixCoordinates ι) => matrixBilinear (F (goeMatrix r g)) u v) :=
    goe_bilinear_uniform_lipschitz r F hL hU hLip u v hu hv
  have hmean := goe_bilinear_bias r F hF (goe_entries_integrable r F hL hLip) d hε hd u v
  have hmean' : |(∫ g, matrixBilinear (F (goeMatrix r g)) u v
      ∂Measure.pi (fun _ : MatrixCoordinates ι => gaussianReal 0 1))-
      matrixBilinear (diagonal d) u v| ≤ ε*U^2 := hmean.trans (by nlinarith [mul_le_mul hu hv (norm_nonneg _) hU])
  have hpos : (0:ℝ≥0) < ⟨C*sqrt (2*r),by positivity⟩ := by
    change (0:ℝ) < C*sqrt (2*r)
    positivity
  have hp := gaussianProduct_tail_from_bias hCF hpos hmean' ht
  simp only [matrixBilinear_sub]
  apply hp.trans_eq
  congr 2
  change -2*t^2/(π^2*(C*sqrt (2*r))^2) = -n*t^2/(π^2*C^2*j)
  rw [mul_pow,sq_sqrt (by positivity : 0 ≤ 2*r)]
  dsimp only [r]
  field_simp
end SKGap
end
end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Localization_AffineBilinear
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
namespace SKGap
open Matrix MeasureTheory ProbabilityTheory Real Set
open scoped BigOperators Matrix.Norms.Frobenius NNReal ENNReal
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in
lemma gaussianCoordinate_mean (a : MatrixCoordinates ι) :
    (∫ g : MatrixCoordinates ι → ℝ, g a ∂Measure.pi (fun _ => gaussianReal 0 1)) = 0 := by
  rw [integral_comp_eval (μ := fun _ : MatrixCoordinates ι => gaussianReal 0 1) (i := a)
    (by fun_prop : AEStronglyMeasurable (fun x : ℝ => x) (gaussianReal 0 1))]
  exact integral_id_gaussianReal

omit [DecidableEq ι] in
lemma goeEntry_integral (r : ℝ) (i k : ι) :
    (∫ g, goeMatrix r g i k ∂Measure.pi (fun _ : MatrixCoordinates ι => gaussianReal 0 1)) = 0 := by
  simp only [goeMatrix,integral_const_mul]
  rw [integral_add ((gaussianCoordinate_memLp (.inl (i,k))).integrable (by norm_num))
    ((gaussianCoordinate_memLp (.inl (k,i))).integrable (by norm_num))]
  simp only [gaussianCoordinate_mean,add_zero,mul_zero]

omit [Fintype ι] in
lemma signConjugate_diagonal (s : ι → ℝ) (hs : ∀ i, s i^2=1) (d : ι → ℝ) :
    signConjugate s (diagonal d)=diagonal d := by
  ext i k
  by_cases h : i=k
  · subst k
    simp only [signConjugate,diagonal_apply_eq]
    rw [← pow_two,hs,one_mul]
  · simp [signConjugate,diagonal_apply_ne _ h]

omit [Fintype ι] [DecidableEq ι] in
lemma signConjugate_sub (s : ι → ℝ) (M N : Matrix ι ι ℝ) :
    signConjugate s (M-N) = signConjugate s M-signConjugate s N := by
  ext i k; simp [signConjugate,mul_sub]

omit [Fintype ι] [DecidableEq ι] in
lemma signConjugate_smul (s : ι → ℝ) (w : ℝ) (M : Matrix ι ι ℝ) :
    signConjugate s (w • M) = w • signConjugate s M := by
  ext i k; simp only [signConjugate,Matrix.smul_apply,smul_eq_mul]; ring

lemma affineRight_sign (F : Matrix ι ι ℝ → Matrix ι ι ℝ) (d e : ι → ℝ) (w : ℝ)
    (hF : ∀ (s : ι → ℝ), (∀ i, s i^2=1) → ∀ M,
      F (signConjugate s M)=signConjugate s (F M))
    (s : ι → ℝ) (hs : ∀ i, s i^2=1) (M : Matrix ι ι ℝ) :
    affineRight F d e w (signConjugate s M)=signConjugate s (affineRight F d e w M) := by
  simp only [affineRight,signConjugate_sub,signConjugate_smul,signConjugate_mul s hs,
    signConjugate_diagonal s hs,hF s hs]

lemma affineRight_lip (F : Matrix ι ι ℝ → Matrix ι ι ℝ) (d e : ι → ℝ) (w : ℝ)
    {L D : ℝ} (hD : 0 ≤ D) (hd : ∀ i, |d i| ≤ D)
    (hF : ∀ M N, ‖F M-F N‖ ≤ L*‖M-N‖) (M N : Matrix ι ι ℝ) :
    ‖affineRight F d e w M-affineRight F d e w N‖ ≤ (L*D+|w|)*‖M-N‖ := by
  have he : affineRight F d e w M-affineRight F d e w N =
      (F M-F N)*diagonal d-w • (M-N) := by
    simp only [affineRight,sub_mul,smul_sub]; abel
  rw [he]
  calc
    _ ≤ ‖(F M-F N)*diagonal d‖+‖w • (M-N)‖ := norm_sub_le _ _
    _ ≤ ‖F M-F N‖*opNorm (diagonal d)+|w| *‖M-N‖ := by
      rw [norm_smul,Real.norm_eq_abs]
      exact add_le_add (frobenius_mul_le_opNorm_right (F M-F N) (diagonal d)) le_rfl
    _ ≤ (L*‖M-N‖)*D+|w| *‖M-N‖ := add_le_add
      (mul_le_mul (hF M N) (opNorm_diagonal_le hD hd) (norm_nonneg _) (le_trans (norm_nonneg _) (hF M N))) le_rfl
    _ = _ := by ring

lemma affineRight_diag (F : Matrix ι ι ℝ → Matrix ι ι ℝ) (d e : ι → ℝ)
    (w : ℝ) (M : Matrix ι ι ℝ) (i : ι) :
    affineRight F d e w M i i=F M i i*d i-e i-w*M i i := by
  simp only [affineRight,Matrix.sub_apply,Matrix.mul_diagonal,diagonal_apply_eq,
    Matrix.smul_apply,smul_eq_mul]

lemma affineRight_bias (r : ℝ) (F : Matrix ι ι ℝ → Matrix ι ι ℝ) (d e k : ι → ℝ) (w : ℝ)
    {ε D : ℝ} (_hD : 0 ≤ D) (hd : ∀ i, |d i| ≤ D)
    (hI : ∀ i k, Integrable (fun g => F (goeMatrix r g) i k)
      (Measure.pi (fun _ : MatrixCoordinates ι => gaussianReal 0 1)))
    (hF : ∀ i, |(∫ g, F (goeMatrix r g) i i
      ∂Measure.pi (fun _ : MatrixCoordinates ι => gaussianReal 0 1))-k i| ≤ ε) (i : ι) :
    |(∫ g, affineRight F d e w (goeMatrix r g) i i
      ∂Measure.pi (fun _ : MatrixCoordinates ι => gaussianReal 0 1))-(k i*d i-e i)| ≤ ε*D := by
  simp_rw [affineRight_diag]
  rw [integral_sub (f := fun g => F (goeMatrix r g) i i*d i-e i)
    (g := fun g => w*goeMatrix r g i i)
    ((hI i i).mul_const (d i) |>.sub (integrable_const (e i)))
    ((goeEntry_memLp r i i).integrable (by norm_num) |>.const_mul w),
    integral_sub (f := fun g => F (goeMatrix r g) i i*d i) (g := fun _ => e i)
    ((hI i i).mul_const (d i)) (integrable_const (e i)),
    integral_mul_const,integral_const,integral_const_mul,goeEntry_integral]
  simp only [probReal_univ,one_smul,mul_zero,sub_zero]
  rw [show (∫ g, F (goeMatrix r g) i i ∂Measure.pi (fun _ : MatrixCoordinates ι => gaussianReal 0 1))*d i-e i-
      (k i*d i-e i) = ((∫ g, F (goeMatrix r g) i i ∂Measure.pi (fun _ : MatrixCoordinates ι => gaussianReal 0 1))-k i)*d i by ring,
    abs_mul]
  exact mul_le_mul (hF i) (hd i) (abs_nonneg _) (le_trans (abs_nonneg _) (hF i))

lemma affineRight_concentration [Nonempty ι] {j L U ε D t : ℝ}
    (hj : 0 < j) (hL : 0 ≤ L) (hU : 0 ≤ U) (hε : 0 ≤ ε) (hD : 0 ≤ D) (ht : 0 ≤ t)
    (F : Matrix ι ι ℝ → Matrix ι ι ℝ) (d e k : ι → ℝ) (w : ℝ)
    (hd : ∀ i, |d i| ≤ D)
    (hF : ∀ (s : ι → ℝ), (∀ i, s i^2=1) → ∀ M,
      F (signConjugate s M)=signConjugate s (F M))
    (hLip : ∀ M N, ‖F M-F N‖ ≤ L*‖M-N‖)
    (hk : ∀ i, |(∫ g, F (goeMatrix (j/(Fintype.card ι:ℝ)) g) i i
      ∂Measure.pi (fun _ : MatrixCoordinates ι => gaussianReal 0 1))-k i| ≤ ε)
    (u v : EuclideanSpace ℝ ι) (hu : ‖u‖ ≤ U) (hv : ‖v‖ ≤ U) :
    (Measure.pi (fun _ : MatrixCoordinates ι => gaussianReal 0 1)).real
      {g | (ε*D)*U^2+t ≤ |matrixBilinear (affineRight F d e w (goeMatrix (j/(Fintype.card ι:ℝ)) g)-
        diagonal (fun i => k i*d i-e i)) u v|} ≤
      2*exp (-(Fintype.card ι:ℝ)*t^2/(π^2*((L*D+|w|+1)*(U+1)^2)^2*j)) := by
  exact goe_bilinear_concentration hj (by positivity) hU (mul_nonneg hε hD) ht
    (affineRight F d e w) (affineRight_sign F d e w hF)
    (affineRight_lip F d e w hD hd hLip) _
    (affineRight_bias _ F d e k w hD hd (goe_entries_integrable _ F hL hLip) hk)
    u v hu hv
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

lemma pathDiagonal_square {a : ι → ℝ} (ha : ∀ i, 0 ≤ a i) :
    pathDiagonal a 1*pathDiagonal a 1=diagonal a := by
  simp only [pathDiagonal,sqrt_one,one_mul,diagonal_mul_diagonal]
  congr 1
  funext i
  exact mul_self_sqrt (ha i)

omit [Fintype ι] in
lemma pathShift_one (q : ℝ) : pathShift (ι := ι) 1 q=q • 1 := by
  ext i k
  by_cases h : i=k <;> simp [pathShift,h]

lemma symmetric_isUnit_of_lower [Nonempty ι] (S : Matrix ι ι ℝ) (hS : Sᵀ=S)
    {lo : ℝ} (hlo : 0 < lo) (hl : lo ≤ ComplexSpectral.lowerRayleigh (liftMatrix S)) : IsUnit S := by
  apply (liftMatrix_isUnit_iff S).mp
  have hh : (liftMatrix S).IsHermitian := liftMatrix_hermitian S hS
  exact (hh.posDef_iff_eigenvalues_pos.mpr (fun i => hlo.trans_le
    (hl.trans (ComplexSpectral.eigenvalue_lower_bound hh i)))).isUnit

lemma pathK_agrees [Nonempty ι] (f : 𝓢(ℝ,ℂ)) {lo hi : ℝ} (hlo : 0 < lo)
    (hf : ∀ x ∈ Set.Icc lo hi, f x=(x:ℂ)⁻¹) {R : ℝ} (hR : 0 ≤ R)
    (j : ℝ) {a : ι → ℝ} (ha : ∀ i, 0 ≤ a i) (M : Matrix ι ι ℝ)
    (hM : Mᵀ=M) (hMR : opNorm M ≤ R)
    (hl : lo ≤ ComplexSpectral.lowerRayleigh (liftMatrix
      (1-pathDiagonal a 1*(M-pathShift 1 ((j/(Fintype.card ι:ℝ))*∑ b,a b))*pathDiagonal a 1)))
    (hu : -hi ≤ ComplexSpectral.lowerRayleigh (-liftMatrix
      (1-pathDiagonal a 1*(M-pathShift 1 ((j/(Fintype.card ι:ℝ))*∑ b,a b))*pathDiagonal a 1))) :
    pathK f R hR j a 1 M=(1-diagonal a*(M-((j/(Fintype.card ι:ℝ))*∑ b,a b) • 1))⁻¹ := by
  change realTruncatedK f R hR (pathDiagonal a 1)
    (pathShift 1 ((j/(Fintype.card ι:ℝ))*∑ b,a b)) M = _
  have he := realTruncatedK_eq_inverse f hlo hf hR (pathDiagonal a 1)
    (pathShift 1 ((j/(Fintype.card ι:ℝ))*∑ b,a b)) M
    (diagonal_transpose _) (diagonal_transpose _) hM hMR hl hu
  simpa only [pathDiagonal_square ha,pathShift_one] using he

lemma inverse_resolvent_relations (D M : Matrix ι ι ℝ) (q : ℝ)
    (hS : IsUnit (1-D*(M-q • 1)*D)) :
    let K := (1-D*D*(M-q • 1))⁻¹
    let G := D*(1-D*(M-q • 1)*D)⁻¹*D
    K*(D*D)=G ∧ G*M=K*(1+q • (D*D))-1 ∧
      M*G*M=(M*K)*(1+q • (D*D))-M := by
  dsimp only
  have hunit := ResolventIdentity.inverse_one_sub_square_mul_unit D (M-q • 1) hS
  have hKG := ResolventIdentity.inverse_one_sub_square_mul_square D (M-q • 1) hS
  have hKK := Matrix.nonsing_inv_mul (1-D*D*(M-q • 1))
    ((Matrix.isUnit_iff_isUnit_det _).mp hunit)
  have hd : D*D*(q • (1:Matrix ι ι ℝ))=q • (D*D) := by simp
  have hGW : (D*(1-D*(M-q • 1)*D)⁻¹*D)*M=
      (1-D*D*(M-q • 1))⁻¹*(1+q • (D*D))-1 := by
    rw [← hKG]
    have hid : (1-D*D*(M-q • 1))⁻¹*(1+q • (D*D))-
        (1-D*D*(M-q • 1))⁻¹*(D*D)*M=
        (1-D*D*(M-q • 1))⁻¹*(1-D*D*(M-q • 1)) := by
      rw [mul_sub,hd]
      noncomm_ring
    rw [hKK] at hid
    exact sub_eq_iff_eq_add.mp hid |>.symm |> (fun h => eq_sub_of_add_eq (by simpa only [add_comm] using h))
  refine ⟨hKG,hGW,?_⟩
  rw [mul_assoc M _ M,hGW,mul_sub,mul_one]
  simp only [mul_assoc]

lemma path_bilinear_agreement [Nonempty ι] (f : 𝓢(ℝ,ℂ)) {lo hi : ℝ} (hlo : 0 < lo)
    (hf : ∀ x ∈ Set.Icc lo hi, f x=(x:ℂ)⁻¹) {R : ℝ} (hR : 0 ≤ R)
    (j : ℝ) {a : ι → ℝ} (ha : ∀ i, 0 ≤ a i) (M : Matrix ι ι ℝ)
    (hM : Mᵀ=M) (hMR : opNorm M ≤ R)
    (hl : lo ≤ ComplexSpectral.lowerRayleigh (liftMatrix
      (1-pathDiagonal a 1*(M-pathShift 1 ((j/(Fintype.card ι:ℝ))*∑ b,a b))*pathDiagonal a 1)))
    (hu : -hi ≤ ComplexSpectral.lowerRayleigh (-liftMatrix
      (1-pathDiagonal a 1*(M-pathShift 1 ((j/(Fintype.card ι:ℝ))*∑ b,a b))*pathDiagonal a 1))) :
    let q := (j/(Fintype.card ι:ℝ))*∑ b,a b
    let G := pathDiagonal a 1*(1-pathDiagonal a 1*(M-q • 1)*pathDiagonal a 1)⁻¹*pathDiagonal a 1
    affineRight (pathK f R hR j a 1) a 0 0 M=G ∧
    affineRight (pathK f R hR j a 1) (fun i => 1+q*a i) 1 0 M=G*M ∧
    affineRight (fun Q => realProject R hR Q*pathK f R hR j a 1 Q)
      (fun i => 1+q*a i) 0 1 M=M*G*M := by
  dsimp only
  have hl' := hl
  rw [pathShift_one] at hl'
  have hsym : (1-pathDiagonal a 1*(M-((j/(Fintype.card ι:ℝ))*∑ b,a b) • 1)*pathDiagonal a 1)ᵀ=
      1-pathDiagonal a 1*(M-((j/(Fintype.card ι:ℝ))*∑ b,a b) • 1)*pathDiagonal a 1 := by
    simp only [transpose_sub,transpose_one,transpose_mul,transpose_smul,hM,
      show (pathDiagonal a 1)ᵀ=pathDiagonal a 1 from diagonal_transpose _,mul_assoc]
  have hS := symmetric_isUnit_of_lower _ hsym hlo hl'
  have hh := inverse_resolvent_relations (pathDiagonal a 1) M
    ((j/(Fintype.card ι:ℝ))*∑ b,a b) hS
  dsimp only at hh
  rw [pathDiagonal_square ha] at hh
  have hid : diagonal (fun i => 1+((j/(Fintype.card ι:ℝ))*∑ b,a b)*a i)=
      1+((j/(Fintype.card ι:ℝ))*∑ b,a b) • diagonal a := by
    ext i k
    by_cases h : i=k <;> simp [h]
  simp only [affineRight,pathK_agrees f hlo hf hR j ha M hM hMR hl hu,
    zero_smul,one_smul,sub_zero,
    realProject_eq_self hR M hM hMR,hid]
  have hz : (diagonal (0 : ι → ℝ))=(0 : Matrix ι ι ℝ) := by ext i k; simp
  have ho : (diagonal (1 : ι → ℝ))=(1 : Matrix ι ι ℝ) := by ext i k; simp [Matrix.diagonal_apply,Matrix.one_apply]
  simpa only [hz,ho,sub_zero] using And.intro hh.1 (And.intro hh.2.1.symm hh.2.2.symm)
end SKGap
end
end

section
noncomputable section
namespace SKGap
open Matrix MeasureTheory ProbabilityTheory Real Set
open scoped BigOperators Matrix.Norms.Frobenius NNReal ENNReal SchwartzMap
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma pathFeatureLip_nonneg (f : 𝓢(ℝ,ℂ)) {R j A : ℝ}
    (hR : 0 ≤ R) (hj : 0 ≤ j) (hA : 0 ≤ A) : 0 ≤ pathFeatureLip f R j A := by
  obtain ⟨hb,hl⟩ := path_constants_nonneg f hR hj hA
  unfold pathFeatureLip
  positivity

lemma pathFeature_lip [Nonempty ι] (p : Bool) (f : 𝓢(ℝ,ℂ)) {R j A : ℝ}
    (hR : 0 ≤ R) (hj : 0 ≤ j) (hA : 0 ≤ A) {a : ι → ℝ}
    (ha : ∀ i, 0 ≤ a i) (haA : ∀ i, a i ≤ A) (M N : Matrix ι ι ℝ) :
    ‖pathFeature p f R hR j a M-pathFeature p f R hR j a N‖ ≤ pathFeatureLip f R j A*‖M-N‖ := by
  have hb := pathK_bounds f hR hj hA ha haA (z := 1) (by constructor <;> norm_num)
  obtain ⟨hB,hL⟩ := path_constants_nonneg f hR hj hA
  cases p
  · exact (hb.2 M N).trans (mul_le_mul_of_nonneg_right
      (show pathLip f R j A ≤ pathFeatureLip f R j A by unfold pathFeatureLip; nlinarith)
      (norm_nonneg _))
  · exact (realProjectedProduct_sub_norm hR _ hb.1 hb.2 M N).trans
      (mul_le_mul_of_nonneg_right
        (show pathBound f R j A+R*pathLip f R j A ≤ pathFeatureLip f R j A by unfold pathFeatureLip; linarith)
        (norm_nonneg _))

lemma pathFeature_sign (p : Bool) (f : 𝓢(ℝ,ℂ)) {R : ℝ} (hR : 0 ≤ R)
    (j : ℝ) (a : ι → ℝ) (s : ι → ℝ) (hs : ∀ i, s i^2=1) (M : Matrix ι ι ℝ) :
    pathFeature p f R hR j a (signConjugate s M)=signConjugate s (pathFeature p f R hR j a M) := by
  cases p <;> simp only [pathFeature,Bool.false_eq_true,ite_false,ite_true,
    pathK_sign f hR j a 1 s hs,realProject_sign hR s hs,signConjugate_mul s hs]

theorem actual_path_affine_tail {j A D U W ε : ℝ}
    (hj : 0 < j) (hA : 0 < A) (hs : sqrt j*A < 1)
    (hD : 0 ≤ D) (hU : 0 ≤ U) (hW : 0 ≤ W) (hε : 0 < ε) :
    ∃ (f : 𝓢(ℝ,ℂ)) (R : ℝ) (hR : 0 ≤ R) (lo hi c : ℝ) (N : ℕ),
      R=2*sqrt j+1+1 ∧ lo=(1-sqrt j*A)^2/4 ∧ hi=2+A*(2*sqrt j+1+j*A) ∧
      0 < lo ∧ (∀ x ∈ Icc lo hi, f x=(x:ℂ)⁻¹) ∧ 0 < c ∧ 0 < N ∧
      ∀ n, N ≤ n → ∀ a : Fin n → ℝ, (∀ i, 0 ≤ a i) → (∀ i, a i ≤ A) →
      ∀ (p : Bool) (d e : Fin n → ℝ) (w : ℝ), (∀ i, |d i| ≤ D) → |w| ≤ W →
      ∀ (u v : EuclideanSpace ℝ (Fin n)), ‖u‖ ≤ U → ‖v‖ ≤ U →
      (Measure.pi (fun _ : MatrixCoordinates (Fin n) => gaussianReal 0 1)).real
        {g | ε ≤ |matrixBilinear (affineRight (pathFeature p f R hR j a) d e w
          (goeMatrix (j/(n:ℝ)) g)-diagonal (fun i =>
            (if p then (j/(n:ℝ))*∑ b,a b else 1)*d i-e i)) u v|} ≤ 2*exp (-c*(n:ℝ)) := by
  obtain ⟨f,R,hR,lo,hi,C,N₀,hReq,hloeq,hhieq,hlo,hf,_hfr,hC,hN₀,hEquiv⟩ :=
    actual_projected_path_equivalents hj hA hs
  let L := pathFeatureLip f R j A
  let denom := π^2*((L*D+W+1)*(U+1)^2)^2*j
  let c := (ε/2)^2/denom
  have hL : 0 ≤ L := pathFeatureLip_nonneg f hR hj.le hA.le
  have hdenom : 0 < denom := by dsimp [denom]; positivity
  have hc : 0 < c := by dsimp [c]; positivity
  obtain ⟨N₁,hN₁⟩ := exists_nat_gt (2*C*D*U^2/ε)
  refine ⟨f,R,hR,lo,hi,c,max N₀ N₁,hReq,hloeq,hhieq,hlo,hf,hc,
    lt_of_lt_of_le hN₀ (le_max_left _ _),?_⟩
  intro n hn a ha haA p d e w hd hw u v hu hv
  have hn₀ := (le_max_left N₀ N₁).trans hn
  have hnpos := hN₀.trans_le hn₀
  let : Nonempty (Fin n) := Fin.pos_iff_nonempty.mp hnpos
  have hnr : (0:ℝ) < n := Nat.cast_pos.mpr hnpos
  have hn₁ : (N₁:ℝ) ≤ n := by exact_mod_cast (le_max_right N₀ N₁).trans hn
  have hbias : (C/(n:ℝ)*D)*U^2 ≤ ε/2 := by
    have h := ((div_lt_iff₀ hε).mp (hN₁.trans_le hn₁)).le
    apply (le_div_iff₀ (by norm_num : (0:ℝ)<2)).mpr
    have he : C/(n:ℝ)*D*U^2*2=(2*C*D*U^2)/(n:ℝ) := by ring
    rw [he,div_le_iff₀ hnr]
    nlinarith
  have hk (i : Fin n) : |(∫ g, pathFeature p f R hR j a (goeMatrix (j/(n:ℝ)) g) i i
      ∂Measure.pi (fun _ : MatrixCoordinates (Fin n) => gaussianReal 0 1))-
      (if p then (j/(n:ℝ))*∑ b,a b else 1)| ≤ C/(n:ℝ) := by
    have heq := hEquiv n hn₀ a ha haA 1 (by constructor <;> norm_num) i
    cases p
    · simpa only [pathFeature,Bool.false_eq_true,ite_false,pathExpected,expectedCutoff,pathK,Fintype.card_fin] using heq.1
    · simpa only [pathFeature,ite_true,one_mul,Fintype.card_fin] using heq.2
  have hp := affineRight_concentration hj hL hU (div_nonneg hC.le hnr.le) hD
    (show 0 ≤ ε/2 by positivity) (pathFeature p f R hR j a) d e
    (fun _ => if p then (j/(n:ℝ))*∑ b,a b else 1) w hd
    (pathFeature_sign p f hR j a) (pathFeature_lip p f hR hj.le hA.le ha haA)
    (by simpa only [Fintype.card_fin] using hk) u v hu hv
  simp only [Fintype.card_fin] at hp
  have hmono : (Measure.pi (fun _ : MatrixCoordinates (Fin n) => gaussianReal 0 1)).real
      {g | ε ≤ |matrixBilinear (affineRight (pathFeature p f R hR j a) d e w
        (goeMatrix (j/(n:ℝ)) g)-diagonal (fun i =>
          (if p then (j/(n:ℝ))*∑ b,a b else 1)*d i-e i)) u v|} ≤
      (Measure.pi (fun _ : MatrixCoordinates (Fin n) => gaussianReal 0 1)).real
      {g | (C/(n:ℝ)*D)*U^2+ε/2 ≤ |matrixBilinear (affineRight (pathFeature p f R hR j a) d e w
        (goeMatrix (j/(n:ℝ)) g)-diagonal (fun i =>
          (if p then (j/(n:ℝ))*∑ b,a b else 1)*d i-e i)) u v|} := by
    apply measureReal_mono ?_ (measure_ne_top _ _)
    intro g hg
    change ε ≤ _ at hg
    change (C/(n:ℝ)*D)*U^2+ε/2 ≤ _
    linarith
  apply hmono.trans (hp.trans ?_)
  apply mul_le_mul_of_nonneg_left (exp_le_exp.mpr ?_) (by norm_num)
  have hden : π^2*((L*D+|w|+1)*(U+1)^2)^2*j ≤ denom := by
    dsimp [denom]
    gcongr
  have hdenpos : 0 < π^2*((L*D+|w|+1)*(U+1)^2)^2*j := by positivity
  have hrat := div_le_div_of_nonneg_left (show 0 ≤ (n:ℝ)*(ε/2)^2 by positivity) hdenpos hden
  dsimp only [c]
  calc
    _ = -((n:ℝ)*(ε/2)^2/(π^2*((L*D+|w|+1)*(U+1)^2)^2*j)) := by ring
    _ ≤ -((n:ℝ)*(ε/2)^2/denom) := neg_le_neg hrat
    _ = -((ε/2)^2/denom)*(n:ℝ) := by ring
end SKGap
end
end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Localization_Bilinear2
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

omit [DecidableEq ι] in
lemma bilinearData_bound [Nonempty ι] {j A : ℝ} (hj : 0 ≤ j) (hA : 0 ≤ A) {a : ι → ℝ}
    (ha : ∀ i, 0 ≤ a i) (haA : ∀ i, a i ≤ A) (k : Fin 3) (i : ι) :
    |bilinearDataD k ((j/(Fintype.card ι:ℝ))*∑ b,a b) a i| ≤ A+1+j*A^2 := by
  have hq := diagonal_mean_bounds hj ha haA
  have hq0 := hq.1
  have hai := ha i
  have haAi := haA i
  unfold bilinearDataD
  split_ifs
  · rw [abs_of_nonneg hai]
    nlinarith [mul_nonneg hj (sq_nonneg A)]
  · rw [abs_of_nonneg (by positivity)]
    have hh := mul_le_mul hq.2 haAi hai (mul_nonneg hj hA)
    nlinarith

lemma bilinearDataW_bound (k : Fin 3) : |bilinearDataW k| ≤ 1 := by
  unfold bilinearDataW
  split_ifs <;> norm_num

lemma bilinearError_agrees [Nonempty ι] (f : 𝓢(ℝ,ℂ)) {lo hi : ℝ} (hlo : 0 < lo)
    (hf : ∀ x ∈ Icc lo hi, f x=(x:ℂ)⁻¹) {R : ℝ} (hR : 0 ≤ R)
    (j : ℝ) {a : ι → ℝ} (ha : ∀ i, 0 ≤ a i) (M : Matrix ι ι ℝ)
    (hM : Mᵀ=M) (hMR : opNorm M ≤ R)
    (hl : lo ≤ ComplexSpectral.lowerRayleigh (liftMatrix
      (1-pathDiagonal a 1*(M-pathShift 1 ((j/(Fintype.card ι:ℝ))*∑ b,a b))*pathDiagonal a 1)))
    (hu : -hi ≤ ComplexSpectral.lowerRayleigh (-liftMatrix
      (1-pathDiagonal a 1*(M-pathShift 1 ((j/(Fintype.card ι:ℝ))*∑ b,a b))*pathDiagonal a 1)))
    (k : Fin 3) :
    let q := (j/(Fintype.card ι:ℝ))*∑ b,a b
    bilinearError k j a M=affineRight (pathFeature (decide (k=2)) f R hR j a)
      (bilinearDataD k q a) (bilinearDataE k) (bilinearDataW k) M-
        diagonal (fun i => (if k=2 then q else 1)*bilinearDataD k q a i-bilinearDataE k i) := by
  dsimp only
  have he := path_bilinear_agreement f hlo hf hR j ha M hM hMR hl hu
  dsimp only at he
  have hd (q : ℝ) : diagonal (fun i => q*a i)=q • diagonal a := by
    ext i k; by_cases h : i=k <;> simp [h]
  have hd₂ (q : ℝ) : diagonal (fun i => q*(1+q*a i))=q • (1:Matrix ι ι ℝ)+q^2 • diagonal a := by
    ext i k; by_cases h : i=k
    · subst k; simp only [diagonal_apply_eq,Matrix.add_apply,Matrix.smul_apply,Matrix.one_apply_eq,smul_eq_mul]; ring
    · simp [h]
  fin_cases k
  · change exactG j a M-diagonal a=affineRight (pathK f R hR j a 1) a 0 0 M-diagonal (fun i => 1*a i-0)
    simpa only [one_mul,sub_zero,exactG] using congrArg (fun Q => Q-diagonal a) he.1.symm
  · change exactG j a M*M-((j/(Fintype.card ι:ℝ))*∑ b,a b) • diagonal a=
      affineRight (pathK f R hR j a 1) (fun i => 1+((j/(Fintype.card ι:ℝ))*∑ b,a b)*a i) 1 0 M-
        diagonal (fun i => 1*(1+((j/(Fintype.card ι:ℝ))*∑ b,a b)*a i)-1)
    rw [he.2.1]
    simp only [one_mul,add_sub_cancel_left,hd,exactG]
  · change M*exactG j a M*M-((j/(Fintype.card ι:ℝ))*∑ b,a b) • 1-
      ((j/(Fintype.card ι:ℝ))*∑ b,a b)^2 • diagonal a=
      affineRight (fun Q => realProject R hR Q*pathK f R hR j a 1 Q)
        (fun i => 1+((j/(Fintype.card ι:ℝ))*∑ b,a b)*a i) 0 1 M-
        diagonal (fun i => ((j/(Fintype.card ι:ℝ))*∑ b,a b)*(1+((j/(Fintype.card ι:ℝ))*∑ b,a b)*a i)-0)
    rw [he.2.2]
    simp only [sub_zero,hd₂,exactG]
    abel

end SKGap
end
end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Localization_BilinearUnion
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

theorem bilinear_deterministic_equivalents {j A U ε : ℝ}
    (hj : 0 < j) (hA : 0 < A) (hs : sqrt j*A < 1)
    (hU : 0 ≤ U) (hε : 0 < ε) (m : ℕ) :
    ∃ (c : ℝ) (N : ℕ), 0 < c ∧ 0 < N ∧
      ∀ n, N ≤ n → ∀ a : Fin n → ℝ, (∀ i, 0 ≤ a i) → (∀ i, a i ≤ A) →
      ∀ v : Fin m → EuclideanSpace ℝ (Fin n), (∀ r, ‖v r‖ ≤ U) →
      (Measure.pi (fun _ : MatrixCoordinates (Fin n) => gaussianReal 0 1)).real
        {g | ¬bilinearPathGood j A a g ∨ ∃ r s k,
          ε < |matrixBilinear (bilinearError k j a (goeMatrix (j/(n:ℝ)) g)) (v r) (v s)|} ≤
        (3+6*(m:ℝ)^2)*exp (-c*(n:ℝ)) := by
  have hD : 0 ≤ A+1+j*A^2 := by positivity
  obtain ⟨f,R,hR,lo,hi,c₀,N₀,hReq,hloeq,hhieq,hlo,hf,hc₀,hN₀,htail⟩ :=
    actual_path_affine_tail hj hA hs hD hU (by norm_num : (0:ℝ)≤1) hε
  obtain ⟨N₁,hN₁⟩ := eventually_atTop.mp (path_size_eventually hs)
  refine ⟨min c₀ (pathRate j A),max N₀ N₁,lt_min hc₀ (pathRate_pos hj hA hs),
    hN₀.trans_le (le_max_left _ _),?_⟩
  intro n hn a ha haA v hv
  have hn₀ := (le_max_left N₀ N₁).trans hn
  have hn₁ := (le_max_right N₀ N₁).trans hn
  have hnpos := hN₀.trans_le hn₀
  let : Nonempty (Fin n) := Fin.pos_iff_nonempty.mp hnpos
  let μ := Measure.pi (fun _ : MatrixCoordinates (Fin n) => gaussianReal 0 1)
  let B : Set (MatrixCoordinates (Fin n) → ℝ) := {g | ¬bilinearPathGood j A a g}
  let T (p : Fin m × Fin m × Fin 3) : Set (MatrixCoordinates (Fin n) → ℝ) :=
    {g | ε ≤ |matrixBilinear (affineRight (pathFeature (decide (p.2.2=2)) f R hR j a)
      (bilinearDataD p.2.2 ((j/(n:ℝ))*∑ b,a b) a) (bilinearDataE p.2.2) (bilinearDataW p.2.2)
      (goeMatrix (j/(n:ℝ)) g)-diagonal (fun i =>
        (if p.2.2=2 then (j/(n:ℝ))*∑ b,a b else 1)*
          bilinearDataD p.2.2 ((j/(n:ℝ))*∑ b,a b) a i-bilinearDataE p.2.2 i)) (v p.1) (v p.2.1)|}
  have hb : μ.real B ≤ 3*exp (-pathRate j A*(n:ℝ)) := by
    have hh := path_all_good_exponential hj hA ha haA hs (by simpa only [Fintype.card_fin] using hN₁ n hn₁)
    simpa only [B,μ,bilinearPathGood,not_forall,exists_prop,Fintype.card_fin] using hh
  have ht (p : Fin m × Fin m × Fin 3) : μ.real (T p) ≤ 2*exp (-c₀*(n:ℝ)) := by
    have hh := htail n hn₀ a ha haA (decide (p.2.2=2))
      (bilinearDataD p.2.2 ((j/(n:ℝ))*∑ b,a b) a) (bilinearDataE p.2.2) (bilinearDataW p.2.2)
      (fun i => by simpa only [Fintype.card_fin] using bilinearData_bound hj.le hA.le ha haA p.2.2 i)
      (bilinearDataW_bound p.2.2) (v p.1) (v p.2.1) (hv p.1) (hv p.2.1)
    simpa only [T,μ,decide_eq_true_eq] using hh
  have hsub : {g | ¬bilinearPathGood j A a g ∨ ∃ r s k,
        ε < |matrixBilinear (bilinearError k j a (goeMatrix (j/(n:ℝ)) g)) (v r) (v s)|} ⊆ B ∪ ⋃ p,T p := by
    intro g hg
    by_cases hgood : bilinearPathGood j A a g
    · rcases hg with hb | ⟨r,s,k,hk⟩
      · exact (hb hgood).elim
      · apply Or.inr
        refine mem_iUnion.mpr ⟨(r,s,k),?_⟩
        have hg₁ := hgood 1 (by constructor <;> norm_num)
        change opNorm _ < _ ∧ _ < _ ∧ _ < _ at hg₁
        have he := bilinearError_agrees f hlo hf hR j ha
          (goeMatrix (j/(n:ℝ)) g) (goeMatrix_transpose _ g)
          (by simpa only [hReq] using hg₁.1.le)
          (by simpa only [hloeq,Fintype.card_fin] using hg₁.2.1.le)
          (by simpa only [hhieq,Fintype.card_fin] using hg₁.2.2.le) k
        dsimp only at he
        simp only [Fintype.card_fin] at he
        change ε ≤ |matrixBilinear _ (v r) (v s)|
        rw [← he]
        exact hk.le
    · exact Or.inl hgood
  have hbound := (measureReal_mono hsub (measure_ne_top _ _)).trans
    ((measureReal_union_le B (⋃ p,T p)).trans (add_le_add hb
      ((measureReal_iUnion_fintype_le T).trans (Finset.sum_le_sum (fun p _ => ht p)))))
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_prod,Fintype.card_fin,
    nsmul_eq_mul,Nat.cast_mul,Nat.cast_ofNat] at hbound
  have hnr : (0:ℝ) ≤ n := Nat.cast_nonneg _
  have he₀ : exp (-c₀*(n:ℝ)) ≤ exp (-min c₀ (pathRate j A)*(n:ℝ)) :=
    exp_le_exp.mpr (mul_le_mul_of_nonneg_right (neg_le_neg (min_le_left _ _)) hnr)
  have he₁ : exp (-pathRate j A*(n:ℝ)) ≤ exp (-min c₀ (pathRate j A)*(n:ℝ)) :=
    exp_le_exp.mpr (mul_le_mul_of_nonneg_right (neg_le_neg (min_le_right _ _)) hnr)
  apply hbound.trans
  have hh₀ := mul_le_mul_of_nonneg_left he₀ (show 0 ≤ (m:ℝ)*((m:ℝ)*3)*2 by positivity)
  linarith
end SKGap
end
end

section
noncomputable section
namespace SKGap
open Matrix Real
open scoped BigOperators Matrix.Norms.Frobenius
variable {ι κ : Type*} [Fintype ι]

lemma matrixPair_sub (G H : Matrix ι ι ℝ) (x y : ι → ℝ) :
    matrixPair (G-H) x y=matrixPair G x y-matrixPair H x y := by
  simp [matrixPair,Matrix.sub_mulVec,dotProduct_sub]
lemma matrixPair_smul (a : ℝ) (G : Matrix ι ι ℝ) (x y : ι → ℝ) :
    matrixPair (a • G) x y=a*matrixPair G x y := by
  simp [matrixPair,Matrix.smul_mulVec,smul_eq_mul]
lemma matrixPair_sub_right (G : Matrix ι ι ℝ) (x y z : ι → ℝ) :
    matrixPair G x (y-z)=matrixPair G x y-matrixPair G x z := by
  simp [matrixPair,Matrix.mulVec_sub,dotProduct_sub]
lemma matrixPair_sub_left (G : Matrix ι ι ℝ) (x y z : ι → ℝ) :
    matrixPair G (x-y) z=matrixPair G x z-matrixPair G y z := by
  simp [matrixPair,sub_dotProduct]
lemma matrixPair_smul_right (G : Matrix ι ι ℝ) (a : ℝ) (x y : ι → ℝ) :
    matrixPair G x (a • y)=a*matrixPair G x y := by
  simp [matrixPair,Matrix.mulVec_smul,smul_eq_mul]
lemma matrixPair_smul_left (G : Matrix ι ι ℝ) (a : ℝ) (x y : ι → ℝ) :
    matrixPair G (a • x) y=a*matrixPair G x y := by
  simp [matrixPair,smul_eq_mul]
lemma matrixPair_mul_right (G W : Matrix ι ι ℝ) (x y : ι → ℝ) :
    matrixPair G x (W*ᵥy)=matrixPair (G*W) x y := by
  simp [matrixPair,Matrix.mulVec_mulVec]
lemma matrixPair_symm {G : Matrix ι ι ℝ} (hG : Gᵀ=G) (x y : ι → ℝ) :
    matrixPair G x y=matrixPair G y x := by
  simpa only [hG,matrixPair] using Matrix.dotProduct_transpose_mulVec G x y
lemma matrixPair_mul_left {W : Matrix ι ι ℝ} (hW : Wᵀ=W)
    (G : Matrix ι ι ℝ) (x y : ι → ℝ) :
    matrixPair G (W*ᵥx) y=matrixPair (W*G) x y := by
  calc
    _ = (G*ᵥy) ⬝ᵥ (W*ᵥx) := dotProduct_comm _ _
    _ = x ⬝ᵥ (W*ᵥ(G*ᵥy)) := by
      simpa only [hW] using Matrix.dotProduct_transpose_mulVec W (G*ᵥy) x
    _ = _ := by rw [matrixPair,Matrix.mulVec_mulVec]

lemma centered_gram_mixed (G W A : Matrix ι ι ℝ) (B : ℝ) (x u : ι → ℝ) :
    matrixPair G x (residualGramVector B W u)=
      (Real.sqrt B)⁻¹*(matrixPair (G*W-B • A) x u-B*matrixPair (G-A) x u) := by
  simp only [residualGramVector,matrixPair_smul_right,matrixPair_sub_right,
    matrixPair_mul_right,matrixPair_sub,matrixPair_smul]
  ring

lemma centered_gram_diagonal [DecidableEq ι] {G W : Matrix ι ι ℝ} (hG : Gᵀ=G) (hW : Wᵀ=W)
    (A : Matrix ι ι ℝ) {B : ℝ} (hB : 0 < B) (u : ι → ℝ) (hu : u⬝ᵥu=1) :
    matrixPair G (residualGramVector B W u) (residualGramVector B W u)-1=
      B⁻¹*(matrixPair (W*G*W-B • 1-B^2 • A) u u-
        2*B*matrixPair (G*W-B • A) u u+B^2*matrixPair (G-A) u u) := by
  have hs : (Real.sqrt B)⁻¹*(Real.sqrt B)⁻¹=B⁻¹ := by
    rw [← mul_inv,← pow_two,Real.sq_sqrt hB.le]
  have hx : matrixPair G (W*ᵥu) u=matrixPair (G*W) u u := by
    rw [matrixPair_symm hG,matrixPair_mul_right]
  simp only [residualGramVector,matrixPair_smul_left,matrixPair_smul_right,
    matrixPair_sub_left,matrixPair_sub_right,matrixPair_mul_right,
    matrixPair_sub,matrixPair_smul]
  rw [matrixPair_mul_left hW,hx,← Matrix.mul_assoc]
  have hi : matrixPair (1 : Matrix ι ι ℝ) u u=1 := by simp [matrixPair,hu]
  rw [hi]
  calc
    _ = ((Real.sqrt B)⁻¹*(Real.sqrt B)⁻¹)*
        (matrixPair (W*G*W) u u-2*B*matrixPair (G*W) u u+B^2*matrixPair G u u)-1 := by ring
    _ = _ := by rw [hs]; field_simp; ring

lemma centered_gram_mixed_bound (G W A : Matrix ι ι ℝ) {B ε : ℝ}
    (hB : 0 < B) (x u : ι → ℝ)
    (h0 : |matrixPair (G-A) x u| ≤ ε)
    (h1 : |matrixPair (G*W-B • A) x u| ≤ ε) :
    |matrixPair G x (residualGramVector B W u)| ≤ (Real.sqrt B)⁻¹*(1+B)*ε := by
  rw [centered_gram_mixed G W A B x u,abs_mul,abs_of_pos (inv_pos.mpr (Real.sqrt_pos.mpr hB))]
  conv_rhs => rw [mul_assoc]
  apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr (Real.sqrt_nonneg _))
  calc
    _ ≤ |matrixPair (G*W-B • A) x u|+|B*matrixPair (G-A) x u| := abs_sub _ _
    _ ≤ ε+B*ε := by rw [abs_mul,abs_of_pos hB]; exact add_le_add h1 (mul_le_mul_of_nonneg_left h0 hB.le)
    _ = _ := by ring

lemma centered_gram_diagonal_bound [DecidableEq ι] {G W : Matrix ι ι ℝ} (hG : Gᵀ=G) (hW : Wᵀ=W)
    (A : Matrix ι ι ℝ) {B ε : ℝ} (hB : 0 < B) (u : ι → ℝ) (hu : u⬝ᵥu=1)
    (h0 : |matrixPair (G-A) u u| ≤ ε)
    (h1 : |matrixPair (G*W-B • A) u u| ≤ ε)
    (h2 : |matrixPair (W*G*W-B • 1-B^2 • A) u u| ≤ ε) :
    |matrixPair G (residualGramVector B W u) (residualGramVector B W u)-1| ≤
      B⁻¹*(1+2*B+B^2)*ε := by
  rw [centered_gram_diagonal hG hW A hB u hu,abs_mul,abs_of_pos (inv_pos.mpr hB)]
  conv_rhs => rw [mul_assoc]
  apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr hB.le)
  calc
    _ ≤ |matrixPair (W*G*W-B • 1-B^2 • A) u u-2*B*matrixPair (G*W-B • A) u u|+
        |B^2*matrixPair (G-A) u u| := abs_add_le _ _
    _ ≤ (ε+2*B*ε)+B^2*ε := by
      apply add_le_add
      · apply (abs_sub _ _).trans
        rw [abs_mul,abs_of_nonneg (by positivity : 0 ≤ 2*B)]
        exact add_le_add h2 (mul_le_mul_of_nonneg_left h1 (by positivity))
      · rw [abs_mul,abs_of_nonneg (sq_nonneg B)]
        exact mul_le_mul_of_nonneg_left h0 (sq_nonneg B)
    _ = _ := by ring
end SKGap
end
end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Localization_GramColumnBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
namespace SKGap
open Matrix Real
open scoped BigOperators Matrix.Norms.Frobenius
variable {ι κ : Type*} [Fintype ι] [Fintype κ]

lemma frobenius_le_card_bound {M : Matrix κ κ ℝ} {ε : ℝ} (hε : 0 ≤ ε)
    (hM : ∀ i k,|M i k| ≤ ε) : ‖M‖ ≤ (Fintype.card κ:ℝ)*ε := by
  rw [Matrix.frobenius_norm_def]
  simp only [Real.rpow_two]
  rw [← Real.sqrt_eq_rpow]
  apply Real.sqrt_le_iff.mpr
  refine ⟨by positivity,?_⟩
  calc
    _ ≤ ∑ _i : κ,∑ _k : κ, ε^2 := by
      apply Finset.sum_le_sum; intro i _
      apply Finset.sum_le_sum; intro k _
      rw [Real.norm_eq_abs]
      exact (sq_le_sq₀ (abs_nonneg _) hε).mpr (hM i k)
    _ = _ := by simp; ring

omit [Fintype κ] in
lemma gram_entry (G : Matrix ι ι ℝ) (V : Matrix ι κ ℝ) (r s : κ) :
    (Vᵀ*G*V) r s=matrixPair G (fun i => V i r) (fun i => V i s) := by
  simp only [Matrix.mul_apply,Matrix.transpose_apply,matrixPair,Matrix.mulVec, dotProduct,
    Finset.sum_mul,Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl; intro i _
  apply Finset.sum_congr rfl; intro k _
  ring

theorem augmented_gram_error [DecidableEq ι] [DecidableEq κ] {G W : Matrix ι ι ℝ}
    (hG : Gᵀ=G) (hW : Wᵀ=W) (A : Matrix ι ι ℝ) {B ε : ℝ}
    (hB : 0 < B) (hε : 0 ≤ ε) (p : κ → ι → ℝ) (u : ι → ℝ) (hu : u⬝ᵥu=1)
    (h00 : ∀ r s,|matrixPair (G-A) (p r) (p s)| ≤ ε)
    (h0u : ∀ r,|matrixPair (G-A) (p r) u| ≤ ε)
    (h1u : ∀ r,|matrixPair (G*W-B • A) (p r) u| ≤ ε)
    (h0 : |matrixPair (G-A) u u| ≤ ε)
    (h1 : |matrixPair (G*W-B • A) u u| ≤ ε)
    (h2 : |matrixPair (W*G*W-B • 1-B^2 • A) u u| ≤ ε) :
    let V := extendColumns p (residualGramVector B W u)
    ‖Vᵀ*G*V-fromBlocks (fun r s => matrixPair A (p r) (p s)) 0 0 (1 : Matrix Unit Unit ℝ)‖ ≤
      ((Fintype.card κ:ℝ)+1)*
        (ε+(sqrt B)⁻¹*(1+B)*ε+B⁻¹*(1+2*B+B^2)*ε) := by
  dsimp only
  have hx (r : κ) := centered_gram_mixed_bound G W A hB (p r) u (h0u r) (h1u r)
  have hn := centered_gram_diagonal_bound hG hW A hB u hu h0 h1 h2
  let e₁ := (sqrt B)⁻¹*(1+B)*ε
  let e₂ := B⁻¹*(1+2*B+B^2)*ε
  have he₁ : 0 ≤ e₁ := by dsimp [e₁]; positivity
  have he₂ : 0 ≤ e₂ := by dsimp [e₂]; positivity
  have hεle : ε ≤ ε+e₁+e₂ := (le_add_of_nonneg_right he₁).trans (le_add_of_nonneg_right he₂)
  have he₁le : e₁ ≤ ε+e₁+e₂ := (le_add_of_nonneg_left hε).trans (le_add_of_nonneg_right he₂)
  have he₂le : e₂ ≤ ε+e₁+e₂ := le_add_of_nonneg_left (add_nonneg hε he₁)
  have hall : ∀ r s : κ ⊕ Unit,
      |((extendColumns p (residualGramVector B W u))ᵀ*G*extendColumns p (residualGramVector B W u)-
        fromBlocks (fun r s => matrixPair A (p r) (p s)) 0 0 (1 : Matrix Unit Unit ℝ)) r s| ≤ ε+e₁+e₂ := by
    intro r s
    rw [Matrix.sub_apply,gram_entry]
    cases r with
    | inl r => cases s with
      | inl s =>
        change |matrixPair G (p r) (p s)-matrixPair A (p r) (p s)| ≤ ε+e₁+e₂
        rw [← matrixPair_sub]
        exact (h00 r s).trans hεle
      | inr s =>
        change |matrixPair G (p r) (residualGramVector B W u)-0| ≤ ε+e₁+e₂
        rw [sub_zero]
        exact (hx r).trans he₁le
    | inr r => cases s with
      | inl s =>
        change |matrixPair G (residualGramVector B W u) (p s)-0| ≤ ε+e₁+e₂
        rw [sub_zero,matrixPair_symm hG]
        exact (hx s).trans he₁le
      | inr s =>
        cases r; cases s
        change |matrixPair G (residualGramVector B W u) (residualGramVector B W u)-1| ≤ ε+e₁+e₂
        exact hn.trans he₂le
  convert frobenius_le_card_bound (by positivity : 0 ≤ ε+e₁+e₂) hall using 1
  all_goals try with_reducible_and_instances rfl
  simp only [Fintype.card_sum,Fintype.card_unique,Nat.cast_add,Nat.cast_one,e₁,e₂]
end SKGap
end
end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Gaussian_ConditionalGramTail
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
namespace SKGap
open Matrix MeasureTheory ProbabilityTheory Real Set
open scoped BigOperators Matrix.Norms.Frobenius
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in
lemma matrixBilinear_eq_pair (M : Matrix ι ι ℝ) (x y : EuclideanSpace ℝ ι) :
    matrixBilinear M x y=matrixPair M x.ofLp y.ofLp := by
  simp only [matrixBilinear,matrixPair,dotProduct,Matrix.mulVec,Finset.mul_sum]
  congr 1; ext i; congr 1; ext k; ring

lemma exactG_transpose (j : ℝ) (a : ι → ℝ) {W : Matrix ι ι ℝ} (hW : Wᵀ=W) :
    (exactG j a W)ᵀ=exactG j a W := by
  simp only [exactG,Matrix.transpose_mul,Matrix.transpose_nonsing_inv,
    Matrix.transpose_sub,Matrix.transpose_one,Matrix.transpose_smul,hW,
    pathDiagonal,Matrix.diagonal_transpose,Matrix.mul_assoc]

theorem conditional_augmented_gram_tail {j A U ε : ℝ}
    (hj : 0 < j) (hA : 0 < A) (hs : sqrt j*A < 1) (hU : 0 ≤ U) (hε : 0 < ε) :
    ∃ (c : ℝ) (N : ℕ), 0 < c ∧ 0 < N ∧
      ∀ n, N ≤ n → ∀ a : Fin n → ℝ, (∀ i,0 ≤ a i) → (∀ i,a i ≤ A) →
      0 < j/(n:ℝ)*∑ i,a i →
      ∀ (p : Fin 3 → EuclideanSpace ℝ (Fin n)) (u : EuclideanSpace ℝ (Fin n)),
      (∀ r,‖p r‖ ≤ U) → ‖u‖ ≤ U → u.ofLp⬝ᵥu.ofLp=1 →
      (Measure.pi (fun _ : MatrixCoordinates (Fin n) => gaussianReal 0 1)).real
        {g | ¬bilinearPathGood j A a g ∨
          augmentedGramTolerance (j/(n:ℝ)*∑ i,a i) ε <
            ‖actualAugmentedGram j a p u g-diagonalAugmentedGram a p‖} ≤
        99*Real.exp (-c*(n:ℝ)) := by
  obtain ⟨c,N,hc,hN,ht⟩ := bilinear_deterministic_equivalents hj hA hs hU hε 4
  refine ⟨c,N,hc,hN,?_⟩
  intro n hn a ha haA hB p u hp hu hunit
  let v : Fin 4 → EuclideanSpace ℝ (Fin n) := Fin.cons u p
  have hv : ∀ r,‖v r‖ ≤ U := by
    intro r
    refine Fin.cases hu (fun r => hp r) r
  have hh := ht n hn a ha haA v hv
  apply (measureReal_mono (s₂ := {g | ¬bilinearPathGood j A a g ∨ ∃ r s k,
      ε < |matrixBilinear (bilinearError k j a (goeMatrix (j/(n:ℝ)) g)) (v r) (v s)|})
    ?_ (measure_ne_top _ _)).trans (by norm_num only [Nat.cast_ofNat,show (3:ℝ)+6*4^2=99 by norm_num] at hh; exact hh)
  intro g hg
  by_contra hbad
  change ¬(¬bilinearPathGood j A a g ∨ ∃ r s k,
    ε < |matrixBilinear (bilinearError k j a (goeMatrix (j/(n:ℝ)) g)) (v r) (v s)|) at hbad
  push Not at hbad
  rcases hbad with ⟨hpath,hpair⟩
  have he (r s : Fin 4) (k : Fin 3) :
      |matrixPair (bilinearError k j a (goeMatrix (j/(n:ℝ)) g)) (v r).ofLp (v s).ofLp| ≤ ε := by
    rw [← matrixBilinear_eq_pair]
    exact hpair r s k
  have h00 (r s : Fin 3) := he r.succ s.succ 0
  have h0u (r : Fin 3) := he r.succ 0 0
  have h1u (r : Fin 3) := he r.succ 0 1
  have h0 := he 0 0 0
  have h1 := he 0 0 1
  have h2 := he 0 0 2
  simp only [v,Fin.cons_succ,Fin.cons_zero,bilinearError,ite_true,ite_false,
    Fin.reduceEq,Fintype.card_fin] at h00 h0u h1u h0 h1 h2
  have hb := augmented_gram_error (exactG_transpose j a (goeMatrix_transpose _ g))
    (goeMatrix_transpose _ g) (diagonal a) hB hε.le (fun r => (p r).ofLp) u.ofLp hunit
    h00 h0u h1u h0 h1 h2
  have hb' : ‖actualAugmentedGram j a p u g-diagonalAugmentedGram a p‖ ≤
      augmentedGramTolerance (j/(n:ℝ)*∑ i,a i) ε := by
    simpa only [actualAugmentedGram,diagonalAugmentedGram,augmentedGramTolerance,
      Fintype.card_fin,Nat.cast_ofNat,show (3:ℝ)+1=4 by norm_num] using hb
  exact hg.elim (fun hn => hn hpath) (fun he => not_lt_of_ge hb' he)
end SKGap
end
end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Localization_FiniteRankPositive
attribute [-instance] _root_.OAI.SKGap.ComplexMatrix.frobeniusInnerProduct
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open Real Matrix Set
open scoped BigOperators
namespace SKGap
variable {ι : Type*} [Fintype ι]

lemma continuous_rayleigh : Continuous (fun p : Matrix ι ι ℝ × EuclideanSpace ℝ ι => rayleigh p.1 p.2) := by
  unfold rayleigh dotProduct mulVec
  fun_prop

lemma rayleigh_smul (M : Matrix ι ι ℝ) (v : EuclideanSpace ℝ ι) (c : ℝ) :
    rayleigh M (c • v) = c^2*rayleigh M v := by
  simp only [rayleigh, WithLp.ofLp_smul, mulVec_smul, dotProduct_smul, smul_dotProduct,
    smul_eq_mul]
  ring

lemma rayleigh_zero (M : Matrix ι ι ℝ) : rayleigh M 0 = 0 := by
  simp [rayleigh]

lemma isCompact_unitEuclidean : IsCompact (unitEuclidean ι) := by
  simpa only [unitEuclidean, Metric.sphere, dist_zero_right] using
    (isCompact_sphere (0 : EuclideanSpace ℝ ι) 1)

lemma unitEuclidean_nonempty [Nonempty ι] : (unitEuclidean ι).Nonempty := by
  classical
  obtain ⟨i⟩ := ‹Nonempty ι›
  refine ⟨EuclideanSpace.single i (1:ℝ),?_⟩
  simp [unitEuclidean]

lemma continuous_lowerRayleigh : Continuous (lowerRayleigh (ι := ι)) := by
  exact isCompact_unitEuclidean.continuous_sInf continuous_rayleigh

lemma lowerRayleigh_attained [Nonempty ι] (M : Matrix ι ι ℝ) :
    ∃ v ∈ unitEuclidean ι, lowerRayleigh M = rayleigh M v ∧
      ∀ w ∈ unitEuclidean ι, rayleigh M v ≤ rayleigh M w := by
  exact isCompact_unitEuclidean.exists_sInf_image_eq_and_le unitEuclidean_nonempty
    (continuous_rayleigh.comp (continuous_const.prodMk continuous_id)).continuousOn

lemma lowerRayleigh_le [Nonempty ι] (M : Matrix ι ι ℝ) {v : EuclideanSpace ℝ ι}
    (hv : v ∈ unitEuclidean ι) : lowerRayleigh M ≤ rayleigh M v := by
  obtain ⟨w,_,he,hw⟩ := lowerRayleigh_attained M
  rw [he]
  exact hw v hv

lemma unitEuclidean_normalize {v : EuclideanSpace ℝ ι} (hv : v ≠ 0) :
    ‖v‖⁻¹ • v ∈ unitEuclidean ι := by
  change ‖‖v‖⁻¹ • v‖ = 1
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.mpr (norm_nonneg _)),
    inv_mul_cancel₀ (norm_ne_zero_iff.mpr hv)]

lemma nonneg_rayleigh_of_unit {M : Matrix ι ι ℝ}
    (h : ∀ v ∈ unitEuclidean ι, 0 ≤ rayleigh M v) (v : EuclideanSpace ℝ ι) :
    0 ≤ rayleigh M v := by
  by_cases hv : v = 0
  · simp [hv,rayleigh_zero]
  have hh := h _ (unitEuclidean_normalize hv)
  rw [rayleigh_smul] at hh
  exact nonneg_of_mul_nonneg_right hh (sq_pos_of_pos (inv_pos.mpr (norm_pos_iff.mpr hv)))

lemma rayleigh_pos_of_unit {M : Matrix ι ι ℝ}
    (h : ∀ v ∈ unitEuclidean ι, 0 < rayleigh M v) {v : EuclideanSpace ℝ ι} (hv : v ≠ 0) :
    0 < rayleigh M v := by
  have hh := h _ (unitEuclidean_normalize hv)
  rw [rayleigh_smul] at hh
  exact pos_of_mul_pos_right hh (sq_nonneg _)

lemma lowerRayleigh_nonneg_iff [Nonempty ι] {M : Matrix ι ι ℝ} (hM : M.IsHermitian) :
    0 ≤ lowerRayleigh M ↔ M.PosSemidef := by
  constructor
  · intro h
    apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg hM
    intro x
    exact nonneg_rayleigh_of_unit (fun v hv => h.trans (lowerRayleigh_le M hv)) (WithLp.toLp 2 x)
  · intro h
    obtain ⟨v,_,he,_⟩ := lowerRayleigh_attained M
    rw [he]
    exact h.dotProduct_mulVec_nonneg _

lemma lowerRayleigh_pos_iff [Nonempty ι] {M : Matrix ι ι ℝ} (hM : M.IsHermitian) :
    0 < lowerRayleigh M ↔ M.PosDef := by
  constructor
  · intro h
    apply Matrix.PosDef.of_dotProduct_mulVec_pos hM
    intro x hx
    apply rayleigh_pos_of_unit (fun v hv => h.trans_le (lowerRayleigh_le M hv))
      (v := WithLp.toLp 2 x)
    exact fun hz => hx (congrArg WithLp.ofLp hz)
  · intro h
    obtain ⟨v,hv,he,_⟩ := lowerRayleigh_attained M
    rw [he]
    exact h.dotProduct_mulVec_pos (fun hz => by
      have hz' : v = 0 := WithLp.ofLp_injective 2 hz
      have hv' : ‖v‖ = 1 := hv
      simp [hz'] at hv')

theorem matrix_path_posDef [DecidableEq ι] {a : ℝ} (ha : 0 ≤ a) (M : ℝ → Matrix ι ι ℝ)
    (hcont : Continuous M) (hherm : ∀ t ∈ Icc 0 a, (M t).IsHermitian)
    (hdet : ∀ t ∈ Icc 0 a, (M t).det ≠ 0) (hzero : (M 0).PosDef) : (M a).PosDef := by
  cases isEmpty_or_nonempty ι with
  | inl h =>
    let := h
    apply Matrix.PosDef.of_dotProduct_mulVec_pos (hherm a ⟨ha,le_rfl⟩)
    intro x hx
    exact (hx (Subsingleton.elim _ _)).elim
  | inr h =>
    let := h
    let f := fun t => lowerRayleigh (M t)
    have hf : Continuous f := continuous_lowerRayleigh.comp hcont
    have hnz : ∀ t ∈ Icc 0 a, f t ≠ 0 := by
      intro t ht hz
      have hpsd := (lowerRayleigh_nonneg_iff (hherm t ht)).mp (le_of_eq hz.symm)
      have hpd := hpsd.posDef_iff_det_ne_zero.mpr (hdet t ht)
      have hh := (lowerRayleigh_pos_iff (hherm t ht)).mpr hpd
      exact (ne_of_gt hh) hz
    have h0 : 0 < f 0 := (lowerRayleigh_pos_iff hzero.1).mpr hzero
    apply (lowerRayleigh_pos_iff (hherm a ⟨ha,le_rfl⟩)).mp
    by_contra hh
    have han : f a < 0 := lt_of_le_of_ne (not_lt.mp hh) (hnz a ⟨ha,le_rfl⟩)
    obtain ⟨t,ht,he⟩ := intermediate_value_Icc' ha hf.continuousOn ⟨han.le,h0.le⟩
    exact hnz t ht he

end SKGap

noncomputable section
open Real Matrix Set
open scoped BigOperators
namespace SKGap

lemma limiting_rank_determinant (j b e s : ℝ) :
    (1-limitingGram b e s * rankCoefficient j b s).det =
      (1-j*b+2*j*e)*(1-j*b+j*e)^2 := by
  simp [Matrix.det_fin_three, limitingGram, rankCoefficient,
    Matrix.sub_apply, cons_val_two, vecHead, vecTail]
  ring

lemma rankCoefficient_hermitian (j b s : ℝ) : (rankCoefficient j b s).IsHermitian := by
  ext i k
  fin_cases i <;> fin_cases k <;> simp [rankCoefficient, Matrix.conjTranspose_apply]

end SKGap

end
end
end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Localization_GramRobust
attribute [-instance] _root_.OAI.SKGap.ComplexMatrix.frobeniusInnerProduct
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section

namespace SKGap
open Matrix Set Filter
open scoped Topology Matrix.Norms.Frobenius

lemma positive_from_gram_path {ι κ : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype κ] [DecidableEq κ] {a d : ℝ} (ha : 0 ≤ a) (hd : 0 < d)
    (Q : Matrix ι κ ℝ) (C : ℝ → Matrix κ κ ℝ) (hc : Continuous C)
    (hherm : ∀ r ∈ Icc 0 a, (C r).IsHermitian) (hz : C 0=0)
    (hdet : ∀ r ∈ Icc 0 a, (1-(d⁻¹ • (Qᵀ*Q)) * C r).det ≠ 0) :
    (d • (1 : Matrix ι ι ℝ)-Q*C a*Qᵀ).PosDef := by
  apply matrix_path_posDef ha (fun r => d • (1 : Matrix ι ι ℝ)-Q*C r*Qᵀ)
  · fun_prop
  · intro r hr
    apply (Matrix.isHermitian_one.smul (R := ℝ) (isSelfAdjoint_iff.mpr (star_trivial d))).sub
    simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using
      Matrix.isHermitian_mul_mul_conjTranspose Q (hherm r hr)
  · intro r hr
    have hid : d • (1 : Matrix ι ι ℝ)-Q*C r*Qᵀ =
        d • (1-((d⁻¹ • Q)*C r)*Qᵀ) := by
      simp only [smul_sub,Matrix.smul_mul,smul_smul,mul_inv_cancel₀ hd.ne',one_smul]
    rw [hid,Matrix.det_smul]
    apply mul_ne_zero (pow_ne_zero _ hd.ne')
    rw [Matrix.det_one_sub_mul_comm,← Matrix.mul_assoc,Matrix.mul_smul,← Matrix.smul_mul]
    simpa only [Matrix.smul_mul] using hdet r hr
  · simpa only [hz,Matrix.mul_zero,Matrix.zero_mul,sub_zero] using
      (Matrix.PosDef.one : (1 : Matrix ι ι ℝ).PosDef).smul hd

end SKGap
end
end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Localization_GramUniformRobust
attribute [-instance] _root_.OAI.SKGap.ComplexMatrix.frobeniusInnerProduct
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
namespace SKGap
open Matrix Set Filter
open scoped Topology Matrix.Norms.Frobenius

theorem compact_gram_path_robust {α κ : Type*} [TopologicalSpace α] [CompactSpace α]
    [Fintype κ] [DecidableEq κ] {a : ℝ} (ha : 0 < a)
    (H : α → Matrix κ κ ℝ) (C₀ : α → ℝ → Matrix κ κ ℝ)
    (hH : Continuous H) (hc₀ : Continuous (Function.uncurry C₀))
    (hherm : ∀ x r, r ∈ Icc 0 a → (C₀ x r).IsHermitian)
    (hzero : ∀ x, C₀ x 0=0)
    (hdet : ∀ x r, r ∈ Icc 0 a → (1-H x*C₀ x r).det ≠ 0) :
    ∃ δ ρ : ℝ, 0 < δ ∧ δ < 1 ∧ 0 < ρ ∧
      ∀ x (ι : Type) [Fintype ι] [DecidableEq ι] (Q : Matrix ι κ ℝ)
        (C : Matrix κ κ ℝ), C.IsHermitian → ‖Qᵀ*Q-H x‖ < ρ →
        ‖C-C₀ x a‖ < ρ → ((1-δ) • (1 : Matrix ι ι ℝ)-Q*C*Qᵀ).PosDef := by
  let F := fun (p : ℝ × (Matrix κ κ ℝ × Matrix κ κ ℝ)) (z : α × ℝ) =>
    (1-((1-p.1)⁻¹ • (H z.1+p.2.1)) * (C₀ z.1 z.2+(z.2/a) • p.2.2)).det
  have hnear : ∀ᶠ p in 𝓝 (0,(0,0)), ∀ z ∈ (univ : Set α) ×ˢ Icc 0 a, F p z ≠ 0 := by
    apply (isCompact_univ.prod isCompact_Icc).eventually_forall_of_forall_eventually
    intro z hz
    have hbase : F (0,(0,0)) z ≠ 0 := by
      simpa only [F,sub_zero,inv_one,one_smul,smul_zero,add_zero] using hdet z.1 z.2 hz.2
    have hc : ContinuousAt (fun z => F z.1 z.2) ((0,(0,0)),z) := by
      unfold F
      have hc' : Continuous (fun z : (ℝ × (Matrix κ κ ℝ × Matrix κ κ ℝ)) × (α × ℝ) =>
          C₀ z.2.1 z.2.2) := hc₀.comp continuous_snd
      fun_prop (disch := norm_num)
    exact hc.eventually (eventually_ne_nhds hbase)
  obtain ⟨ε,hε,hball⟩ := Metric.eventually_nhds_iff.mp hnear
  let δ := min (ε/2) (1/2)
  have hδ : 0 < δ := lt_min (half_pos hε) (by norm_num)
  have hδ1 : δ < 1 := (min_le_right _ _).trans_lt (by norm_num)
  have hδε : δ < ε := (min_le_left _ _).trans_lt (half_lt_self hε)
  refine ⟨δ,ε,hδ,hδ1,hε,?_⟩
  intro x ι _ _ Q C hC hQ hCC
  have hin : dist (δ,(Qᵀ*Q-H x,C-C₀ x a)) (0,(0,0)) < ε := by
    simp only [Prod.dist_eq,dist_zero_right,Real.norm_eq_abs,abs_of_pos hδ,max_lt_iff]
    exact ⟨hδε,hQ,hCC⟩
  have hh := hball hin
  let D := fun r => C₀ x r+(r/a) • (C-C₀ x a)
  have hc : Continuous D := by
    have hx : Continuous (fun r => C₀ x r) := hc₀.comp (continuous_const.prodMk continuous_id)
    unfold D
    fun_prop
  have hhD : ∀ r ∈ Icc 0 a, (D r).IsHermitian := by
    intro r hr
    exact (hherm x r hr).add
      ((hC.sub (hherm x a ⟨ha.le,le_rfl⟩)).smul (R := ℝ) (isSelfAdjoint_iff.mpr (star_trivial (r/a))))
  have hz : D 0=0 := by simp [D,hzero]
  have heq : D a=C := by simp [D,div_self ha.ne']
  rw [← heq]
  apply positive_from_gram_path ha.le (sub_pos.mpr hδ1) Q D hc hhD hz
  intro r hr
  simpa only [F,add_sub_cancel] using hh (x,r) ⟨mem_univ _,hr⟩
end SKGap
end
end

section
noncomputable section
namespace SKGap
open Matrix Set Filter
open scoped Topology Matrix.Norms.Frobenius

variable {κ ν : Type*} [Fintype κ] [DecidableEq κ] [Fintype ν] [DecidableEq ν]

lemma augmented_determinant (H C : Matrix κ κ ℝ) (V : Matrix κ ν ℝ) :
    (1-augmentedGram (ν := ν) H*augmentedCoefficient C V).det=(1-H*C).det := by
  have he : (1 : Matrix (κ ⊕ ν) (κ ⊕ ν) ℝ)-augmentedGram H*augmentedCoefficient C V =
      fromBlocks (1-H*(C-V*Vᵀ)) (-H*V) (-Vᵀ) 1 := by
    simp only [augmentedGram,augmentedCoefficient,Matrix.fromBlocks_multiply]
    ext i k
    cases i <;> cases k <;> simp [Matrix.one_apply]
  rw [he,Matrix.det_fromBlocks_one₂₂]
  congr 1
  simp only [Matrix.mul_sub,Matrix.neg_mul,Matrix.mul_neg,neg_neg,Matrix.mul_assoc]
  abel

omit [Fintype κ] [DecidableEq κ] [DecidableEq ν] in
lemma augmentedCoefficient_hermitian {C : Matrix κ κ ℝ} (hC : C.IsHermitian)
    (V : Matrix κ ν ℝ) : (augmentedCoefficient C V).IsHermitian := by
  apply Matrix.IsHermitian.fromBlocks
  · apply hC.sub
    simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using Matrix.isHermitian_mul_conjTranspose_self V
  · simp only [Matrix.conjTranspose_eq_transpose_of_trivial]
  · exact Matrix.isHermitian_zero

omit [Fintype κ] [DecidableEq κ] [DecidableEq ν] in
lemma continuous_augmentedCoefficient {α : Type*} [TopologicalSpace α]
    {C : α → Matrix κ κ ℝ} {V : α → Matrix κ ν ℝ} (hC : Continuous C) (hV : Continuous V) :
    Continuous (fun x => augmentedCoefficient (C x) (V x)) := by
  unfold augmentedCoefficient
  fun_prop

omit [Fintype κ] [DecidableEq κ] [DecidableEq ν] in
lemma augmentedCoefficient_zero : augmentedCoefficient (0 : Matrix κ κ ℝ) (0 : Matrix κ ν ℝ)=0 := by
  ext i k
  cases i <;> cases k <;> simp [augmentedCoefficient]

end SKGap
end
end

section
noncomputable section
namespace SKGap
open Matrix Set Filter
open scoped Topology Matrix.Norms.Frobenius

theorem compact_limiting_augmented_gram_robust {α ν : Type*}
    [TopologicalSpace α] [CompactSpace α] [Fintype ν] [DecidableEq ν]
    {j : ℝ} (hj : 0 < j) (hj1 : j < 1) (b e s : α → ℝ)
    (V : α → Matrix (Fin 3) ν ℝ) (hb : Continuous b) (he : Continuous e)
    (hs : Continuous s) (hV : Continuous V)
    (hb1 : ∀ x, b x ≤ 1) (he0 : ∀ x, 0 ≤ e x) (hs0 : ∀ x, s x ≠ 0) :
    ∃ δ ρ : ℝ, 0 < δ ∧ δ < 1 ∧ 0 < ρ ∧
      ∀ x (ι : Type) [Fintype ι] [DecidableEq ι] (Q : Matrix ι ((Fin 3) ⊕ ν) ℝ)
        (C : Matrix ((Fin 3) ⊕ ν) ((Fin 3) ⊕ ν) ℝ), C.IsHermitian →
        ‖Qᵀ*Q-augmentedGram (limitingGram (b x) (e x) (s x))‖ < ρ →
        ‖C-augmentedCoefficient (rankCoefficient j (b x) (s x)) (V x)‖ < ρ →
        ((1-δ) • (1 : Matrix ι ι ℝ)-Q*C*Qᵀ).PosDef := by
  let H := fun x => augmentedGram (ν := ν) (limitingGram (b x) (e x) (s x))
  let C₀ := fun x r => augmentedCoefficient (rankCoefficient r (b x) (s x)) ((r/j) • V x)
  have hH : Continuous H := by
    unfold H augmentedGram limitingGram
    fun_prop (disch := aesop)
  have hC : Continuous (Function.uncurry C₀) := by
    apply continuous_augmentedCoefficient
    · unfold rankCoefficient
      fun_prop (disch := aesop)
    · fun_prop
  have hherm : ∀ x r, r ∈ Icc 0 j → (C₀ x r).IsHermitian := by
    intro x r _
    exact augmentedCoefficient_hermitian (rankCoefficient_hermitian r (b x) (s x)) _
  have hz : ∀ x, C₀ x 0=0 := by
    intro x
    have hc : rankCoefficient 0 (b x) (s x)=0 := by
      ext i k; fin_cases i <;> fin_cases k <;> simp [rankCoefficient]
    simp only [C₀,hc,zero_div,zero_smul,augmentedCoefficient_zero]
  have hd : ∀ x r, r ∈ Icc 0 j → (1-H x*C₀ x r).det ≠ 0 := by
    intro x r hr
    change (1-augmentedGram (limitingGram (b x) (e x) (s x))*
      augmentedCoefficient (rankCoefficient r (b x) (s x)) ((r/j) • V x)).det ≠ 0
    rw [augmented_determinant,limiting_rank_determinant]
    have hrb : r*b x < 1 := lt_of_le_of_lt (mul_le_of_le_one_right hr.1 (hb1 x)) (hr.2.trans_lt hj1)
    have hre : 0 ≤ r*e x := mul_nonneg hr.1 (he0 x)
    exact ne_of_gt (mul_pos (by nlinarith) (sq_pos_of_pos (by linarith)))
  obtain ⟨δ,ρ,hδ,hδ1,hρ,hfinal⟩ := compact_gram_path_robust hj H C₀ hH hC hherm hz hd
  refine ⟨δ,ρ,hδ,hδ1,hρ,?_⟩
  intro x ι _ _ Q C hc hq hcc
  apply hfinal x ι Q C hc hq
  simpa only [C₀,div_self hj.ne',one_smul] using hcc
end SKGap
end
end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Matrix_MatrixWhitening
attribute [-instance] _root_.OAI.SKGap.ComplexMatrix.frobeniusInnerProduct
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
namespace SKGap
open Matrix
open scoped MatrixOrder Matrix.Norms.Frobenius
variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ]

omit [Fintype κ] in
lemma positive_sqrt_data {S : Matrix ι ι ℝ} (hS : S.PosDef) :
    ∃ R : Matrix ι ι ℝ, R.IsHermitian ∧ R*R=S ∧ IsUnit R.det := by
  let R := CFC.sqrt S
  have hR : R.IsHermitian := (CFC.sqrt_nonneg S).posSemidef.isHermitian
  have hsq : R*R=S := CFC.sqrt_mul_sqrt_self S hS.posSemidef.nonneg
  have hu : IsUnit R := isUnit_of_mul_isUnit_left (hsq.symm ▸ hS.isUnit)
  exact ⟨R,hR,hsq,(Matrix.isUnit_iff_isUnit_det R).mp hu⟩

omit [Fintype κ] in

theorem positive_whitening_gram {S : Matrix ι ι ℝ} (hS : S.PosDef)
    (D : Matrix ι ι ℝ) (hD : D.IsHermitian) (V : Matrix ι κ ℝ) :
    ∃ R : Matrix ι ι ℝ, R.IsHermitian ∧ R*R=S ∧ IsUnit R.det ∧
      (R⁻¹*D*V)ᵀ*(R⁻¹*D*V)=Vᵀ*D*S⁻¹*D*V := by
  obtain ⟨R,hR,hsq,hu⟩ := positive_sqrt_data hS
  refine ⟨R,hR,hsq,hu,?_⟩
  have ht : Rᵀ=R := by simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using hR.eq
  have htD : Dᵀ=D := by simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using hD.eq
  have hi : R⁻¹*R⁻¹=S⁻¹ := by rw [← hsq,Matrix.mul_inv_rev]
  simp only [Matrix.transpose_mul,Matrix.transpose_nonsing_inv,ht,htD,Matrix.mul_assoc]
  rw [← Matrix.mul_assoc R⁻¹ R⁻¹,hi]

theorem positive_unwhitening {S R D : Matrix ι ι ℝ} (hR : R.IsHermitian)
    (hD : D.IsHermitian) (hRR : R*R=S) (hu : IsUnit R.det)
    (V : Matrix ι κ ℝ) (C : Matrix κ κ ℝ) (δ : ℝ)
    (hpos : ((1-δ) • (1 : Matrix ι ι ℝ)-
      (R⁻¹*D*V)*C*(R⁻¹*D*V)ᵀ).PosDef) :
    ((1-δ) • S-D*V*C*Vᵀ*D).PosDef := by
  have ht : Rᵀ=R := by simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using hR.eq
  have htD : Dᵀ=D := by simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using hD.eq
  have hinj : Function.Injective R.mulVec := by
    intro x y hxy
    have h := congrArg (fun z => R⁻¹*ᵥz) hxy
    simpa only [Matrix.mulVec_mulVec,Matrix.nonsing_inv_mul _ hu,Matrix.one_mulVec] using h
  have hp := hpos.conjTranspose_mul_mul_same hinj
  simp only [Matrix.conjTranspose_eq_transpose_of_trivial,ht,Matrix.mul_sub,Matrix.sub_mul,
    Matrix.mul_smul,Matrix.smul_mul,Matrix.mul_one,hRR] at hp
  convert hp using 1
  all_goals try with_reducible_and_instances rfl
  congr 1
  simp only [Matrix.transpose_mul,Matrix.transpose_nonsing_inv,ht,htD,Matrix.mul_assoc]
  simp only [← Matrix.mul_assoc R R⁻¹,Matrix.mul_nonsing_inv _ hu,Matrix.one_mul]
  simp only [← Matrix.mul_assoc,Matrix.nonsing_inv_mul_cancel_right _ _ hu]

end SKGap
end
end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Localization_ConditionalRankAlgebra
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
namespace SKGap
open Matrix Real
open scoped BigOperators
variable {ι : Type*}

lemma conditional_schur_coefficient {j b s q κ : ℝ} (hb : 0 < b) (hj : 0 < j)
    (hs : 0 < s) (hq : 0 < q) (hk : κ^2=1-j*q/s) :
    (2*j*q+2*(j*b)*(κ-1))/q = j*(2-j*b/s)-((κ-1)*√(j*b)/√q)^2 := by
  have hB : 0 < j*b := mul_pos hj hb
  have hq0 : √q ≠ 0 := ne_of_gt (Real.sqrt_pos.2 hq)
  rw [div_pow,mul_pow,Real.sq_sqrt hB.le,Real.sq_sqrt hq.le]
  field_simp
  have hk' : κ^2*s=s-j*q := by
    calc
      _ = (1-j*q/s)*s := by rw [hk]
      _ = _ := by field_simp
  nlinarith [hk']

lemma conditionalCoefficient_at_equality {j b s q κ : ℝ} (hb : 0 < b) (hj : 0 < j)
    (hs : 0 < s) (hq : 0 < q) (hk : κ^2=1-j*q/s) :
    conditionalCoefficient j ((2*j*q+2*(j*b)*(κ-1))/q) j ((κ-1)*√(j*b)/√q)=
      augmentedCoefficient (rankCoefficient j b s) (conditionalCoupling ((κ-1)*√(j*b)/√q)) := by
  have h := conditional_schur_coefficient hb hj hs hq hk
  ext i k
  cases i with
  | inl i => cases k with
    | inl k => fin_cases i <;> fin_cases k <;>
        simp [conditionalCoefficient,augmentedCoefficient,rankCoefficient,conditionalCoupling,
          Matrix.mul_apply,h,pow_two]
    | inr k => simp [conditionalCoefficient,augmentedCoefficient]
  | inr i => cases k <;> simp [conditionalCoefficient,augmentedCoefficient]

end SKGap
end
end

section
noncomputable section
namespace SKGap
open Matrix Set Real
open scoped MatrixOrder Matrix.Norms.Frobenius

theorem compact_conditional_rank_criterion {α : Type*} [TopologicalSpace α] [CompactSpace α]
    {j : ℝ} (hj : 0 < j) (hj1 : j < 1) (b e s q κ : α → ℝ)
    (hb : Continuous b) (he : Continuous e) (hs : Continuous s)
    (hq : Continuous q) (hκ : Continuous κ)
    (hb0 : ∀ x, 0 < b x) (hb1 : ∀ x, b x ≤ 1) (he0 : ∀ x, 0 ≤ e x)
    (hs0 : ∀ x, 0 < s x) (hq0 : ∀ x, 0 < q x)
    (hκsq : ∀ x, κ x^2=1-j*q x/s x) :
    ∃ δ ρ : ℝ, 0 < δ ∧ δ < 1 ∧ 0 < ρ ∧
      ∀ x (ι : Type) [Fintype ι] [DecidableEq ι]
        (S D : Matrix ι ι ℝ) (V : Matrix ι ((Fin 3) ⊕ Unit) ℝ)
        (C : Matrix ((Fin 3) ⊕ Unit) ((Fin 3) ⊕ Unit) ℝ) (c : ℝ),
        S.PosDef → D.IsHermitian → C.IsHermitian →
        (S-c • (1 : Matrix ι ι ℝ)).PosSemidef →
        ‖Vᵀ*D*S⁻¹*D*V-augmentedGram (ν := Unit) (limitingGram (b x) (e x) (s x))‖ < ρ →
        ‖C-conditionalCoefficient j ((2*j*q x+2*(j*b x)*(κ x-1))/q x)
          j ((κ x-1)*√(j*b x)/√(q x))‖ < ρ →
        (S-D*V*C*Vᵀ*D-(δ*c) • (1 : Matrix ι ι ℝ)).PosDef := by
  let coupling := fun x => conditionalCoupling ((κ x-1)*√(j*b x)/√(q x))
  have hcoupling : Continuous coupling := by
    unfold coupling conditionalCoupling
    fun_prop (disch := intro x; exact ne_of_gt (Real.sqrt_pos.2 (hq0 x)))
  obtain ⟨δ,ρ,hδ,hδ1,hρ,hcrit⟩ := compact_limiting_augmented_gram_robust hj hj1
    b e s coupling hb he hs hcoupling hb1 he0 (fun x => (hs0 x).ne')
  refine ⟨δ,ρ,hδ,hδ1,hρ,?_⟩
  intro x ι _ _ S D V C c hS hD hC hc hg hcc
  obtain ⟨R,hR,hRR,hu,hgram⟩ := positive_whitening_gram hS D hD V
  have hcc' : ‖C-augmentedCoefficient (rankCoefficient j (b x) (s x)) (coupling x)‖ < ρ := by
    rw [conditionalCoefficient_at_equality (hb0 x) hj (hs0 x) (hq0 x) (hκsq x)] at hcc
    exact hcc
  have hh := hcrit x ι (R⁻¹*D*V) C hC (by rw [hgram]; exact hg) hcc'
  have hp := positive_unwhitening hR hD hRR hu V C δ hh
  have hp' := hp.add_posSemidef (hc.smul hδ.le)
  convert hp' using 1
  all_goals try with_reducible_and_instances rfl
  rw [smul_sub,smul_smul,sub_smul,one_smul]
  abel
end SKGap
end
end

section
noncomputable section
namespace SKGap
open Matrix Real Set
open scoped BigOperators MatrixOrder Matrix.Norms.Frobenius
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in
lemma quadratic_lift_real (M : Matrix ι ι ℝ) (v : EuclideanSpace ℝ ι) :
    ComplexSpectral.quadratic (RealComplex.liftMatrix M) (RealComplex.liftVec v)=rayleigh M v := by
  simp [ComplexSpectral.quadratic,RealComplex.liftMatrix,RealComplex.liftVec,
    rayleigh,dotProduct,mulVec]

lemma complex_lowerRayleigh_margin {M : Matrix ι ι ℝ} (hM : M.IsHermitian)
    {c : ℝ} (hc : c < ComplexSpectral.lowerRayleigh (RealComplex.liftMatrix M)) :
    (M-c • (1 : Matrix ι ι ℝ)).PosDef := by
  apply Matrix.PosDef.of_dotProduct_mulVec_pos (hM.sub
    (Matrix.isHermitian_one.smul (R := ℝ) (isSelfAdjoint_iff.mpr (star_trivial c))))
  intro x hx
  apply rayleigh_pos_of_unit (M := M-c • (1 : Matrix ι ι ℝ)) (fun v hv => ?_)
    (v := WithLp.toLp 2 x) (fun hz => hx (congrArg WithLp.ofLp hz))
  have hv' : ‖v‖=1 := hv
  have hh := ComplexSpectral.lowerRayleigh_le (RealComplex.liftMatrix M)
    (x := RealComplex.liftVec v) (by
      simp only [ComplexSpectral.unitSphere,Metric.mem_sphere,dist_zero_right,
        RealComplex.norm_liftVec,hv'])
  rw [quadratic_lift_real] at hh
  have hsq : v.ofLp⬝ᵥv.ofLp=1 := by
    have hn := EuclideanSpace.real_norm_sq_eq v
    rw [hv'] at hn
    simpa only [dotProduct,pow_two,one_mul] using hn.symm
  change 0 < v.ofLp⬝ᵥ((M-c • (1 : Matrix ι ι ℝ))*ᵥv.ofLp)
  rw [Matrix.sub_mulVec,Matrix.smul_mulVec,Matrix.one_mulVec,dotProduct_sub,
    dotProduct_smul,smul_eq_mul,hsq,mul_one]
  exact sub_pos.mpr (lt_of_lt_of_le hc hh)

theorem bilinearPathGood_margin {n : ℕ} {j A : ℝ} (a : Fin n → ℝ)
    (g : MatrixCoordinates (Fin n) → ℝ) (hg : bilinearPathGood j A a g) :
    ((1-pathDiagonal a 1*(goeMatrix (j/(n:ℝ)) g-
      ((j/(n:ℝ))*∑ i,a i) • 1)*pathDiagonal a 1)-
      ((1-sqrt j*A)^2/4) • (1 : Matrix (Fin n) (Fin n) ℝ)).PosDef := by
  have hh := hg 1 ⟨by norm_num,le_rfl⟩
  change _ ∧ _ ∧ _ at hh
  have he : pathShift 1 ((j/(n:ℝ))*∑ i,a i)=((j/(n:ℝ))*∑ i,a i) •
      (1 : Matrix (Fin n) (Fin n) ℝ) := by
    ext i k
    simp [pathShift,Matrix.diagonal,Matrix.one_apply]
  rw [he] at hh
  apply complex_lowerRayleigh_margin ?_ hh.2.1
  apply Matrix.isHermitian_one.sub
  have hD : (pathDiagonal a 1).IsHermitian := by
    exact isHermitian_diagonal_iff.mpr (fun i => isSelfAdjoint_iff.mpr (star_trivial _))
  have hW : (goeMatrix (j/(n:ℝ)) g).IsHermitian := by
    change (goeMatrix (j/(n:ℝ)) g)ᴴ=goeMatrix (j/(n:ℝ)) g
    simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using goeMatrix_transpose (j/(n:ℝ)) g
  change (pathDiagonal a 1*(goeMatrix (j/(n:ℝ)) g-((j/(n:ℝ))*∑ i,a i) • 1)*pathDiagonal a 1).IsHermitian
  unfold Matrix.IsHermitian
  simp only [Matrix.conjTranspose_mul,Matrix.conjTranspose_sub,Matrix.conjTranspose_smul,
    Matrix.conjTranspose_one,hD.eq,hW.eq,star_trivial,Matrix.mul_assoc]
end SKGap
end
end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Gaussian_GOEScalarTail
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
namespace SKGap
open Matrix MeasureTheory ProbabilityTheory Real
open scoped BigOperators Matrix.Norms.Frobenius

theorem goe_scalar_tail {n : ℕ} (hn : 0 < n) {j U ε : ℝ}
    (hj : 0 < j) (hU : 0 ≤ U) (hε : 0 ≤ ε)
    (u : EuclideanSpace ℝ (Fin n)) (hu : ‖u‖ ≤ U) :
    (Measure.pi (fun _ : MatrixCoordinates (Fin n) => gaussianReal 0 1)).real
      {g | ε ≤ |matrixBilinear (goeMatrix (j/(n:ℝ)) g) u u|} ≤
      2*exp (-(n:ℝ)*ε^2/(π^2*(2*(U+1)^2)^2*j)) := by
  let : Nonempty (Fin n) := Fin.pos_iff_nonempty.mp hn
  have h := goe_bilinear_concentration hj (by norm_num : (0:ℝ)≤1) hU
    (by norm_num : (0:ℝ)≤0) hε (fun M => M) (fun _ _ _ => rfl)
    (fun M N => by simp) 0 (by intro i; simp [goeEntry_integral]) u u hu hu
  have hz : (diagonal (0 : Fin n → ℝ) : Matrix (Fin n) (Fin n) ℝ)=0 := by
    ext i k; simp [Matrix.diagonal]
  rw [hz] at h
  simpa only [Fintype.card_fin,zero_mul,zero_add,sub_zero,
    show (1:ℝ)+1=2 by norm_num] using h
end SKGap
end
end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Gaussian_ConditionalUniformTail
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
namespace SKGap
open Matrix MeasureTheory ProbabilityTheory Real Set
open scoped BigOperators MatrixOrder Matrix.Norms.Frobenius

theorem compact_conditional_uniform_tail_oai {α : Type*} [TopologicalSpace α] [CompactSpace α]
    {j A : ℝ} (hj : 0 < j) (hj1 : j < 1) (hA : 0 < A)
    (hsub : sqrt j*A < 1)
    (b e s q κ : α → ℝ) (hb : Continuous b) (he : Continuous e)
    (hs : Continuous s) (hq : Continuous q) (hk : Continuous κ)
    (hb0 : ∀ x,0 < b x) (hb1 : ∀ x,b x ≤ 1) (he0 : ∀ x,0 ≤ e x)
    (hs0 : ∀ x,0 < s x) (hq0 : ∀ x,0 < q x)
    (hkq : ∀ x,κ x^2=1-j*q x/s x) :
    ∃ δ ρ : ℝ, 0 < δ ∧ δ < 1 ∧ 0 < ρ ∧
    ∀ U : ℝ, 0 ≤ U → ∀ ε τ : ℝ, 0 < ε → 0 < τ → ∃ c : ℝ, ∃ N : ℕ, 0 < c ∧ 0 < N ∧
    ∀ n, N ≤ n → ∀ a : Fin n → ℝ, (∀ i,0 ≤ a i) → (∀ i,a i ≤ A) →
    0 < j/(n:ℝ)*∑ i,a i →
    augmentedGramTolerance (j/(n:ℝ)*∑ i,a i) ε < ρ/2 →
    ∀ p : Fin 3 → EuclideanSpace ℝ (Fin n), ∀ u : EuclideanSpace ℝ (Fin n),
    (∀ r,‖p r‖ ≤ U) → ‖u‖ ≤ U → u.ofLp⬝ᵥu.ofLp=1 →
    ∀ x (C E : Matrix ((Fin 3) ⊕ Unit) ((Fin 3) ⊕ Unit) ℝ),
    C.IsHermitian → E.IsHermitian → τ*‖E‖ < ρ/2 →
    ‖diagonalAugmentedGram a p-augmentedGram (ν := Unit) (limitingGram (b x) (e x) (s x))‖ < ρ/2 →
    ‖C-conditionalCoefficient j ((2*j*q x+2*(j*b x)*(κ x-1))/q x)
      j ((κ x-1)*√(j*b x)/√(q x))‖ < ρ/2 →
    (Measure.pi (fun _ : MatrixCoordinates (Fin n) => gaussianReal 0 1)).real
      {g | ¬(conditionalBase j a g-
        pathDiagonal a 1*conditionalUpdateColumns j a p u g*
        (C+matrixBilinear (goeMatrix (j/(n:ℝ)) g) u u • E)*
        (conditionalUpdateColumns j a p u g)ᵀ*pathDiagonal a 1-
        (δ*((1-sqrt j*A)^2/4)) • (1 : Matrix (Fin n) (Fin n) ℝ)).PosDef} ≤
      101*exp (-c*(n:ℝ)) := by
  obtain ⟨δ,ρ,hδ,hδ1,hρ,hcrit⟩ := compact_conditional_rank_criterion hj hj1 b e s q κ
    hb he hs hq hk hb0 hb1 he0 hs0 hq0 hkq
  refine ⟨δ,ρ,hδ,hδ1,hρ,?_⟩
  intro U hU ε τ hε hτ
  obtain ⟨c₀,N,hc₀,hN,hgram⟩ := conditional_augmented_gram_tail hj hA hsub hU hε
  let c₁ := τ^2/(π^2*(2*(U+1)^2)^2*j)
  have hc₁ : 0 < c₁ := by dsimp [c₁]; positivity
  refine ⟨min c₀ c₁,N,lt_min hc₀ hc₁,hN,?_⟩
  intro n hn a ha haA hB heps p u hp hu hunit x C E hC hE hEbound hdiag hcoef
  let μ := Measure.pi (fun _ : MatrixCoordinates (Fin n) => gaussianReal 0 1)
  let badG := {g | ¬bilinearPathGood j A a g ∨
    augmentedGramTolerance (j/(n:ℝ)*∑ i,a i) ε <
      ‖actualAugmentedGram j a p u g-diagonalAugmentedGram a p‖}
  let badS := {g | τ ≤ |matrixBilinear (goeMatrix (j/(n:ℝ)) g) u u|}
  have hnpos := hN.trans_le hn
  have hgprob : μ.real badG ≤ 99*exp (-c₀*(n:ℝ)) := hgram n hn a ha haA hB p u hp hu hunit
  have hsprob : μ.real badS ≤ 2*exp (-c₁*(n:ℝ)) := by
    have hh := goe_scalar_tail hnpos hj hU hτ.le u hu
    convert hh using 1
    all_goals try with_reducible_and_instances rfl
    congr 2
    dsimp [c₁]
    ring
  have hsubsets : {g | ¬(conditionalBase j a g-
        pathDiagonal a 1*conditionalUpdateColumns j a p u g*
        (C+matrixBilinear (goeMatrix (j/(n:ℝ)) g) u u • E)*
        (conditionalUpdateColumns j a p u g)ᵀ*pathDiagonal a 1-
        (δ*((1-sqrt j*A)^2/4)) • (1 : Matrix (Fin n) (Fin n) ℝ)).PosDef} ⊆ badG ∪ badS := by
    intro g hg
    by_contra hbad
    have hgG : g ∉ badG := fun hh => hbad (Or.inl hh)
    have hgS : g ∉ badS := fun hh => hbad (Or.inr hh)
    simp only [badG,mem_ofPred_eq,not_or,not_lt] at hgG
    have hgS' : |matrixBilinear (goeMatrix (j/(n:ℝ)) g) u u| < τ := lt_of_not_ge hgS
    let D := pathDiagonal a 1
    let S := conditionalBase j a g
    let V := conditionalUpdateColumns j a p u g
    let Cg := C+matrixBilinear (goeMatrix (j/(n:ℝ)) g) u u • E
    let lo := (1-sqrt j*A)^2/4
    have hmargin : (S-lo • (1 : Matrix (Fin n) (Fin n) ℝ)).PosDef :=
      bilinearPathGood_margin a g (not_not.mp hgG.1)
    have hlo : 0 ≤ lo := by dsimp [lo]; positivity
    have hSpos : S.PosDef := by
      have hh := hmargin.add_posSemidef ((Matrix.PosSemidef.one : (1 : Matrix (Fin n) (Fin n) ℝ).PosSemidef).smul hlo)
      convert hh using 1; abel
    have hD : D.IsHermitian := isHermitian_diagonal_iff.mpr
      (fun i => isSelfAdjoint_iff.mpr (star_trivial _))
    have hCg : Cg.IsHermitian := hC.add (hE.smul (R := ℝ)
      (isSelfAdjoint_iff.mpr (star_trivial _)))
    have hG : ‖Vᵀ*D*S⁻¹*D*V-augmentedGram (ν := Unit) (limitingGram (b x) (e x) (s x))‖ < ρ := by
      have hh := norm_sub_le_norm_sub_add_norm_sub (actualAugmentedGram j a p u g) (diagonalAugmentedGram a p)
        (augmentedGram (ν := Unit) (limitingGram (b x) (e x) (s x)))
      have heq : Vᵀ*D*S⁻¹*D*V=actualAugmentedGram j a p u g := by
        simp only [V,D,S,conditionalUpdateColumns,conditionalBase,actualAugmentedGram,
          exactG,Fintype.card_fin,Matrix.mul_assoc]
      rw [heq]
      exact hh.trans_lt (by linarith [hgG.2])
    have hCgclose : ‖Cg-conditionalCoefficient j ((2*j*q x+2*(j*b x)*(κ x-1))/q x)
        j ((κ x-1)*√(j*b x)/√(q x))‖ < ρ := by
      have hn : ‖matrixBilinear (goeMatrix (j/(n:ℝ)) g) u u • E‖ ≤ τ*‖E‖ := by
        rw [norm_smul,Real.norm_eq_abs]
        exact mul_le_mul_of_nonneg_right hgS'.le (norm_nonneg _)
      have hh := norm_add_le (C-conditionalCoefficient j ((2*j*q x+2*(j*b x)*(κ x-1))/q x)
        j ((κ x-1)*√(j*b x)/√(q x))) (matrixBilinear (goeMatrix (j/(n:ℝ)) g) u u • E)
      have heq : Cg-conditionalCoefficient j ((2*j*q x+2*(j*b x)*(κ x-1))/q x)
          j ((κ x-1)*√(j*b x)/√(q x))=
          (C-conditionalCoefficient j ((2*j*q x+2*(j*b x)*(κ x-1))/q x)
          j ((κ x-1)*√(j*b x)/√(q x)))+matrixBilinear (goeMatrix (j/(n:ℝ)) g) u u • E := by
        dsimp [Cg]; abel
      rw [heq]
      exact hh.trans_lt (by linarith)
    exact hg (hcrit x (Fin n) S D V Cg lo hSpos hD hCg hmargin.posSemidef hG hCgclose)
  apply (measureReal_mono hsubsets (measure_ne_top _ _)).trans
  apply (measureReal_union_le badG badS).trans
  apply (add_le_add hgprob hsprob).trans
  have he₀ : exp (-c₀*(n:ℝ)) ≤ exp (-min c₀ c₁*(n:ℝ)) := by
    apply exp_le_exp.mpr; simpa only [neg_mul] using neg_le_neg (mul_le_mul_of_nonneg_right (min_le_left c₀ c₁) (Nat.cast_nonneg n : (0:ℝ) ≤ n))
  have he₁ : exp (-c₁*(n:ℝ)) ≤ exp (-min c₀ c₁*(n:ℝ)) := by
    apply exp_le_exp.mpr; simpa only [neg_mul] using neg_le_neg (mul_le_mul_of_nonneg_right (min_le_right c₀ c₁) (Nat.cast_nonneg n : (0:ℝ) ≤ n))
  nlinarith
end SKGap
end
end

end OAI
end

theorem solution.{u_1} : type_of% @OAI.SKGap.compact_conditional_uniform_tail_oai.{u_1} := @OAI.SKGap.compact_conditional_uniform_tail_oai.{u_1}
