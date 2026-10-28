-- Prove2me | solution 1 for OAI.SKGap.actualWord_expected_recursion_s2
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T10:53:39.916688+00:00
-- url     : https://prove2.me/submissions/f8806375-5443-4be3-a158-db9f4495bdfb

import Mathlib
import Definitions.Def_OAIQ072A000
import Theorems.Thm_OAI_SKGap_actualWord_loop
import Theorems.Thm_OAI_SKGap_path_goodSet_exponential

section
-- module Solutions.OAIQ074_CM.SKGap_Matrix_MatrixCoordinates
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
-- module Solutions.OAIQ074_CM.SKGap_Matrix_OpNorm
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

lemma mul_symmetricElementary_mul (P Q : Matrix ι ι ℝ) (a b i k : ι) :
    (P*symmetricElementary a b*Q) i k = P i a*Q b k+P i b*Q a k := by
  simp [symmetricElementary,Matrix.mul_add,
    Matrix.mul_apply,Matrix.single_apply,ite_and,add_mul,Finset.sum_add_distrib,ite_mul]

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
-- module Solutions.OAIQ074_CM.SKGap_Localization_FrobeniusSq
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
-- module Solutions.OAIQ074_CM.SKGap_Localization_ExpDuhamel
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
-- module Solutions.OAIQ074_CM.SKGap_Localization_LinSub
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
-- module Solutions.OAIQ074_CM.SKGap_Localization_EntryLM
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

end SKGap.ComplexMatrix

end

end OAI
end

section
-- module Solutions.OAIQ074_CM.SKGap_Gaussian_FourierMoment
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
-- module Solutions.OAIQ074_CM.SKGap_Matrix_OpNormKernelMatrixSub
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
-- module Solutions.OAIQ074_CM.SKGap_Localization_SandShift
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
-- module Solutions.OAIQ074_CM.SKGap_Localization_Vectorize
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
-- module Solutions.OAIQ074_CM.SKGap_Matrix_LiftMatrix
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
-- module Solutions.OAIQ074_CM.SKGap_Localization_RealPart
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

end SKGap.RealComplex

namespace SKGap.RealComplex
open scoped Matrix.Norms.Frobenius SchwartzMap ComplexOrder
open SKGap.ComplexMatrix
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

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
-- module Solutions.OAIQ074_CM.SKGap_Matrix_LipschitzNormedConvolution
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
-- module Solutions.OAIQ074_CM.SKGap_Gaussian_StdGaussianMgfLipschitz
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
-- module Solutions.OAIQ074_CM.SKGap_Terminal_PowExponentialPair
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
section SubgaussianMoments
variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {X : Ω → ℝ} {c : ℝ≥0}

lemma pow_le_exponential_pair (x : ℝ) {r : ℝ} (hr : 0 < r) (k : ℕ) :
    |x|^k ≤ ((k.factorial : ℝ)/r^k) * (exp (r*x)+exp (-r*x)) := by
  have hk : 0 < (k.factorial : ℝ) := by exact_mod_cast k.factorial_pos
  have hh := Real.pow_div_factorial_le_exp (r*|x|) (mul_nonneg hr.le (abs_nonneg x)) k
  have he : exp (r*|x|) ≤ exp (r*x)+exp (-r*x) := by
    rcases le_total 0 x with hx | hx
    · rw [abs_of_nonneg hx]; exact le_add_of_nonneg_right (exp_nonneg _)
    · rw [abs_of_nonpos hx]; have hid : r * -x = -r*x := by ring
      rw [hid]; exact le_add_of_nonneg_left (exp_nonneg _)
  have hg := hh.trans he
  rw [div_le_iff₀ hk,mul_pow] at hg
  rw [div_mul_eq_mul_div]
  apply (le_div_iff₀ (pow_pos hr k)).mpr
  convert hg using 1 <;> ring

lemma subgaussian_abs_moment {r : ℝ} (hr : 0 < r) (hX : HasSubgaussianMGF X c μ) (k : ℕ) :
    (∫ x, |X x|^k ∂μ) ≤
      2*((k.factorial : ℝ)/r^k)*exp ((c : ℝ)*r^2/2) := by
  let C := (k.factorial : ℝ)/r^k
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have he : Integrable (fun x => C*(exp (r*X x)+exp (-r*X x))) μ :=
    ((hX.integrable_exp_mul r).add (hX.integrable_exp_mul (-r))).const_mul C
  have hp (x : Ω) : |X x|^k ≤ C*(exp (r*X x)+exp (-r*X x)) := pow_le_exponential_pair (X x) hr k
  have hi : Integrable (fun x => |X x|^k) μ := by
    apply he.mono' (hX.integrable.aestronglyMeasurable.norm.pow k)
    filter_upwards [] with x
    simpa only [Pi.pow_apply,Real.norm_eq_abs,abs_pow,abs_abs] using hp x
  calc
    _ ≤ ∫ x, C*(exp (r*X x)+exp (-r*X x)) ∂μ := integral_mono hi he hp
    _ = C*(mgf X μ r+mgf X μ (-r)) := by
      rw [integral_const_mul,integral_add (hX.integrable_exp_mul r) (hX.integrable_exp_mul (-r))]
      rfl
    _ ≤ C*(exp ((c:ℝ)*r^2/2)+exp ((c:ℝ)*r^2/2)) := by
      apply mul_le_mul_of_nonneg_left _ hC
      simpa only [neg_sq] using add_le_add (hX.mgf_le r) (hX.mgf_le (-r))
    _ = _ := by dsimp only [C]; ring
end SubgaussianMoments

section GaussianMoments
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

lemma stdGaussian_subgaussian_lipschitz {f : E → ℝ} {L : ℝ≥0} (hf : LipschitzWith L f) :
    HasSubgaussianMGF (fun x => f x-∫ y, f y ∂stdGaussian E)
      ⟨π^2*(L:ℝ)^2/4,by positivity⟩ (stdGaussian E) where
  integrable_exp_mul r := by
    apply gaussian_integrable_exp_lipschitz (L := L) _ r
    apply LipschitzWith.of_dist_le_mul
    intro x y
    simpa only [Real.dist_eq,sub_sub_sub_cancel_right] using hf.dist_le_mul x y
  mgf_le r := by
    have hh := stdGaussian_mgf_lipschitz_le hf r
    change (∫ x, exp (r*(f x-∫ y, f y ∂stdGaussian E)) ∂stdGaussian E) ≤ _
    apply hh.trans_eq
    change exp (π^2*r^2*(L:ℝ)^2/8) = exp ((π^2*(L:ℝ)^2/4)*r^2/2)
    congr 1
    ring

lemma stdGaussian_abs_centered_moment {f : E → ℝ} {L : ℝ≥0} (hf : LipschitzWith L f)
    (hL : 0 < L) (k : ℕ) :
    (∫ x, |f x-∫ y, f y ∂stdGaussian E|^k ∂stdGaussian E) ≤
      (2*(k.factorial : ℝ)*exp (π^2/8))*(L:ℝ)^k := by
  have hLr : 0 < (L:ℝ) := hL
  have hh := subgaussian_abs_moment (inv_pos.mpr hLr) (stdGaussian_subgaussian_lipschitz hf) k
  convert hh using 1
  all_goals try with_reducible_and_instances rfl
  have he : π^2*(L:ℝ)^2/4*((L:ℝ)⁻¹)^2/2 = π^2/8 := by field_simp [ne_of_gt hLr]; ring
  change 2*(k.factorial : ℝ)*exp (π^2/8)*(L:ℝ)^k =
    2*((k.factorial:ℝ)/(L:ℝ)⁻¹^k)*exp ((π^2*(L:ℝ)^2/4)*(L:ℝ)⁻¹^2/2)
  rw [he,inv_pow,div_inv_eq_mul]
  ring
end GaussianMoments
end SKGap

end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ074_CM.SKGap_Gaussian_GaussianProductIntegral
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

lemma gaussianProduct_integral (F : EuclideanSpace ℝ κ → ℝ) (hF : Continuous F) :
    (∫ g : κ → ℝ, F (WithLp.toLp 2 g) ∂Measure.pi (fun _ => gaussianReal 0 1)) =
      ∫ x, F x ∂stdGaussian (EuclideanSpace ℝ κ) := by
  rw [← map_pi_eq_stdGaussian]
  exact (integral_map (by fun_prop) hF.aestronglyMeasurable).symm

lemma gaussianProduct_integrable_lipschitz {F : EuclideanSpace ℝ κ → ℝ}
    {L : ℝ≥0} (hF : LipschitzWith L F) :
    Integrable (fun g : κ → ℝ => F (WithLp.toLp 2 g))
      (Measure.pi (fun _ => gaussianReal 0 1)) := by
  have hi := gaussian_integrable_lipschitz (μ := stdGaussian (EuclideanSpace ℝ κ)) hF
  rw [← map_pi_eq_stdGaussian] at hi
  exact hi.comp_measurable (by fun_prop)

lemma gaussianProduct_abs_centered_moment {F : EuclideanSpace ℝ κ → ℝ}
    {L : ℝ≥0} (hF : LipschitzWith L F) (hL : 0 < L) (k : ℕ) :
    (∫ g : κ → ℝ, |F (WithLp.toLp 2 g)-
      ∫ h : κ → ℝ, F (WithLp.toLp 2 h) ∂Measure.pi (fun _ => gaussianReal 0 1)|^k
        ∂Measure.pi (fun _ => gaussianReal 0 1)) ≤
      (2*(k.factorial : ℝ)*exp (π^2/8))*(L:ℝ)^k := by
  rw [gaussianProduct_integral F hF.continuous]
  rw [gaussianProduct_integral (fun x => |F x-∫ y, F y ∂stdGaussian _|^k) ((hF.continuous.sub continuous_const).abs.pow k)]
  exact stdGaussian_abs_centered_moment hF hL k

lemma gaussianProduct_centered_L1 {F : EuclideanSpace ℝ κ → ℝ}
    {L : ℝ≥0} (hF : LipschitzWith L F) (hL : 0 < L) :
    (∫ g : κ → ℝ, |F (WithLp.toLp 2 g)-
      ∫ h : κ → ℝ, F (WithLp.toLp 2 h) ∂Measure.pi (fun _ => gaussianReal 0 1)|
        ∂Measure.pi (fun _ => gaussianReal 0 1)) ≤
      (2*exp (π^2/8))*(L:ℝ) := by
  simpa using gaussianProduct_abs_centered_moment hF hL 1

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
-- module Solutions.OAIQ074_CM.SKGap_Localization_IntegralProductDeviation
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
namespace SKGap
variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

lemma integral_product_deviation {X Y : Ω → ℝ} {C T : ℝ}
    (hX : Integrable X μ) (hY : AEStronglyMeasurable Y μ)
    (hC : ∀ᵐ x ∂μ, ‖Y x‖ ≤ C)
    (hT : (∫ x, |X x-∫ y, X y ∂μ| ∂μ) ≤ T) :
    |(∫ x, X x*Y x ∂μ)-(∫ x, X x ∂μ)*(∫ x, Y x ∂μ)| ≤ C*T := by
  have hC0 : 0 ≤ C := by
    obtain ⟨x,hx⟩ := hC.exists
    exact (norm_nonneg _).trans hx
  have hYi : Integrable Y μ := (integrable_const C).mono' hY hC
  have hXY : Integrable (fun x => X x*Y x) μ := by
    simpa only [mul_comm] using hX.bdd_mul hY hC
  have hcenter : Integrable (fun x => X x-∫ y, X y ∂μ) μ := hX.sub (integrable_const _)
  have hci : Integrable (fun x => (X x-∫ y, X y ∂μ)*Y x) μ := by
    simpa only [mul_comm] using hcenter.bdd_mul hY hC
  have he : (∫ x, X x*Y x ∂μ)-(∫ x, X x ∂μ)*(∫ x, Y x ∂μ) =
      ∫ x, (X x-∫ y, X y ∂μ)*Y x ∂μ := by
    simp_rw [sub_mul]
    rw [integral_sub hXY (hYi.const_mul _),integral_const_mul]
  rw [he]
  calc
    _ ≤ ∫ x, ‖(X x-∫ y, X y ∂μ)*Y x‖ ∂μ := norm_integral_le_integral_norm _
    _ ≤ ∫ x, C*|X x-∫ y, X y ∂μ| ∂μ := by
      apply integral_mono_ae hci.norm (hcenter.norm.const_mul C)
      filter_upwards [hC] with x hx
      simpa only [norm_mul,Real.norm_eq_abs,mul_comm] using
        mul_le_mul_of_nonneg_left hx (norm_nonneg (X x-∫ y, X y ∂μ))
    _ = C*(∫ x, |X x-∫ y, X y ∂μ| ∂μ) := integral_const_mul _ _
    _ ≤ _ := mul_le_mul_of_nonneg_left hT hC0

lemma integral_loop_deviation {X Y Z V : Ω → ℝ} {r C T B E : ℝ}
    (hr : 0 ≤ r) (hX : Integrable X μ) (hY : AEStronglyMeasurable Y μ)
    (hC : ∀ᵐ x ∂μ, ‖Y x‖ ≤ C)
    (hZ : Integrable Z μ) (hB : ∀ᵐ x ∂μ, ‖Z x‖ ≤ B)
    (hT : (∫ x, |X x-∫ y, X y ∂μ| ∂μ) ≤ T)
    (hE : |(∫ x, V x ∂μ)-r*(∫ x, X x*Y x+Z x ∂μ)| ≤ E) :
    |(∫ x, V x ∂μ)-r*(∫ x, X x ∂μ)*(∫ x, Y x ∂μ)| ≤ E+r*(C*T+B) := by
  have hXY : Integrable (fun x => X x*Y x) μ := by
    simpa only [mul_comm] using hX.bdd_mul hY hC
  have hbound := integral_product_deviation hX hY hC hT
  have hb : |∫ x, Z x ∂μ| ≤ B := by
    exact (norm_integral_le_integral_norm _).trans ((integral_mono_ae hZ.norm (integrable_const B) hB).trans_eq (by simp))
  have he : (∫ x, V x ∂μ)-r*(∫ x, X x ∂μ)*(∫ x, Y x ∂μ) =
      ((∫ x, V x ∂μ)-r*(∫ x, X x*Y x+Z x ∂μ))+
      r*((∫ x, X x*Y x ∂μ)-(∫ x, X x ∂μ)*(∫ x, Y x ∂μ)+(∫ x, Z x ∂μ)) := by
    rw [integral_add hXY hZ]; ring
  rw [he]
  exact (abs_add_le _ _).trans (add_le_add hE (by
    rw [abs_mul,abs_of_nonneg hr]
    exact mul_le_mul_of_nonneg_left ((abs_add_le _ _).trans (add_le_add hbound hb)) hr))

end SKGap

end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ074_CM.SKGap_Matrix_MatrixEntryCLM
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

lemma diagonalVector_norm_le (M : Matrix ι ι ℝ) : ‖diagonalVector M‖ ≤ ‖M‖ := by
  apply nonneg_le_nonneg_of_sq_le_sq (norm_nonneg M)
  simp only [← sq]
  rw [EuclideanSpace.norm_sq_eq,frobenius_sq]
  apply Finset.sum_le_sum
  intro i _
  simpa only [diagonalVector,Real.norm_eq_abs,sq_abs] using
    (Finset.single_le_sum (fun j _ => sq_nonneg (M i j)) (Finset.mem_univ i))

lemma abs_trace_le_frobenius (M : Matrix ι ι ℝ) :
    |Matrix.trace M| ≤ sqrt (Fintype.card ι)*‖M‖ := by
  let v : EuclideanSpace ℝ ι := WithLp.toLp 2 (fun _ => 1)
  have hv : ‖v‖ = sqrt (Fintype.card ι) := by
    rw [EuclideanSpace.norm_eq]; simp [v]
  have hi := abs_real_inner_le_norm (diagonalVector M) v
  change |∑ i, 1*M i i| ≤ ‖diagonalVector M‖*‖v‖ at hi
  simp only [one_mul,hv] at hi
  change |Matrix.trace M| ≤ ‖diagonalVector M‖*sqrt (Fintype.card ι) at hi
  exact hi.trans ((mul_le_mul_of_nonneg_right (diagonalVector_norm_le M) (sqrt_nonneg _)).trans_eq (mul_comm _ _))

end SKGap

end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ074_CM.SKGap_Brownian_PathBiasBase
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section

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

end SKGap

end
end
end

end OAI
end

section
-- module Solutions.OAIQ074_CM.SKGap_Matrix_OpNormDiagonal
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

lemma opNorm_one_le : opNorm (1 : Matrix ι ι ℝ) ≤ 1 := by
  change ‖Matrix.toEuclideanCLM (n := ι) (𝕜 := ℝ) (1 : Matrix ι ι ℝ)‖ ≤ _
  rw [map_one]
  exact ContinuousLinearMap.norm_id_le

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
-- module Solutions.OAIQ074_CM.SKGap_Brownian_PathDiagonal
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
-- module Solutions.OAIQ074_CM.SKGap_Brownian_PathExpectation
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

lemma path_interval {j A : ℝ} (hj : 0 ≤ j) (hA : 0 ≤ A) (hs : sqrt j*A < 1) :
    0 < (1-sqrt j*A)^2/4 ∧
    (1-sqrt j*A)^2/4 ≤ 2+A*(2*sqrt j+1+j*A) := by
  have hh := mul_nonneg (sqrt_nonneg j) hA
  have hgap : 0 < 1-sqrt j*A := sub_pos.mpr hs
  have hp : (1-sqrt j*A)^2 ≤ 1 := by nlinarith
  refine ⟨by positivity,?_⟩
  have hx : 0 ≤ A*(2*sqrt j+1+j*A) := by positivity
  linarith

end SKGap
end
end

end OAI
end

section
-- module Solutions.OAIQ074_CM.SKGap_Localization_ProjectedReal
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

lemma realProject_lipschitz {R : ℝ} (hR : 0 ≤ R) :
    LipschitzWith 1 (realProject (ι := ι) R hR) := by
  apply LipschitzWith.of_dist_le_mul
  intro M N
  simpa only [dist_eq_norm,NNReal.coe_one,one_mul] using realProject_sub_norm hR M N

end SKGap
end
end

end OAI
end

section
-- module Solutions.OAIQ074_CM.SKGap_Brownian_PathCutoff
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

end SKGap
end
end

end OAI
end

section
-- module Solutions.OAIQ074_CM.SKGap_Matrix_MatrixWordRegularity
attribute [-instance] _root_.OAI.SKGap.ComplexMatrix.frobeniusInnerProduct
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
namespace SKGap
open Real Matrix MeasureTheory ProbabilityTheory
open scoped BigOperators Matrix.Norms.Frobenius
variable {ι X : Type*} [Fintype ι] [DecidableEq ι] [PseudoMetricSpace X]

omit [PseudoMetricSpace X] in
lemma matrixFactorProduct_opNorm (F : List (X→Matrix ι ι ℝ)) {R : NNReal}
    (hF : ∀ f∈F,∀ x,opNorm (f x) ≤ R) (x : X) :
    opNorm (matrixFactorProduct F x) ≤ (R:ℝ)^F.length := by
  induction F with
  | nil => simpa using opNorm_one_le (ι:=ι)
  | cons f F ih =>
    rw [matrixFactorProduct_cons,List.length_cons,pow_succ']
    exact (opNorm_mul _ _).trans (mul_le_mul (hF f (List.mem_cons_self) x)
      (ih (fun p hp=>hF p (List.mem_cons_of_mem f hp))) (show 0 ≤ opNorm (matrixFactorProduct F x) from norm_nonneg _) R.coe_nonneg)

theorem matrixFactorProduct_lipschitz (F : List (X→Matrix ι ι ℝ)) {R : NNReal}
    (hF : ∀ f∈F,∀ x,opNorm (f x) ≤ R)
    (hL : ∀ f∈F,LipschitzWith R f) :
    LipschitzWith ((F.length:NNReal)*R^F.length) (matrixFactorProduct F) := by
  induction F with
  | nil => simp [matrixFactorProduct]
  | cons f F ih =>
    have hFt : ∀ p∈F,∀ x,opNorm (p x) ≤ R := fun p hp=>hF p (List.mem_cons_of_mem f hp)
    have hLt : ∀ p∈F,LipschitzWith R p := fun p hp=>hL p (List.mem_cons_of_mem f hp)
    have ht := ih hFt hLt
    apply LipschitzWith.of_dist_le_mul
    intro x y
    rw [dist_eq_norm,matrixFactorProduct_cons,matrixFactorProduct_cons]
    have he : f x*matrixFactorProduct F x-f y*matrixFactorProduct F y=
        f x*(matrixFactorProduct F x-matrixFactorProduct F y)+(f x-f y)*matrixFactorProduct F y := by noncomm_ring
    rw [he]
    apply (norm_add_le _ _).trans
    apply (add_le_add (frobenius_mul_le_opNorm _ _) (frobenius_mul_le_opNorm_right _ _)).trans
    have hd : ‖matrixFactorProduct F x-matrixFactorProduct F y‖ ≤ ((F.length:ℝ)*(R:ℝ)^F.length)*dist x y := by
      simpa only [dist_eq_norm,NNReal.coe_mul,NNReal.coe_natCast,NNReal.coe_pow] using ht.dist_le_mul x y
    have hf : ‖f x-f y‖ ≤ (R:ℝ)*dist x y := by
      simpa only [dist_eq_norm] using (hL f List.mem_cons_self).dist_le_mul x y
    have hb := matrixFactorProduct_opNorm F hFt y
    have hp := hF f List.mem_cons_self x
    have h1 := mul_le_mul hp hd (norm_nonneg _) R.coe_nonneg
    have h2 := mul_le_mul hf hb (show 0 ≤ opNorm (matrixFactorProduct F y) from norm_nonneg _) (mul_nonneg R.coe_nonneg dist_nonneg)
    apply (add_le_add h1 h2).trans_eq
    norm_num only [NNReal.coe_mul,NNReal.coe_natCast,NNReal.coe_pow,List.length_cons,Nat.cast_add,Nat.cast_one,NNReal.coe_add,NNReal.coe_one,pow_succ]
    ring

lemma matrixFactorProduct_trace_lipschitz (F : List (X→Matrix ι ι ℝ)) {R : NNReal}
    (hF : ∀ f∈F,∀ x,opNorm (f x) ≤ R) (hL : ∀ f∈F,LipschitzWith R f) :
    LipschitzWith (⟨sqrt (Fintype.card ι),sqrt_nonneg _⟩*((F.length:NNReal)*R^F.length))
      (fun x=>trace (matrixFactorProduct F x)) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  have hh := (matrixFactorProduct_lipschitz F hF hL).dist_le_mul x y
  have ht := abs_trace_le_frobenius (matrixFactorProduct F x-matrixFactorProduct F y)
  rw [trace_sub] at ht
  have hm := mul_le_mul_of_nonneg_left hh (sqrt_nonneg (Fintype.card ι:ℝ))
  change |trace (matrixFactorProduct F x)-trace (matrixFactorProduct F y)| ≤
    (sqrt (Fintype.card ι)*((F.length:ℝ)*(R:ℝ)^F.length))*dist x y
  simpa only [dist_eq_norm,NNReal.coe_mul,NNReal.coe_natCast,NNReal.coe_pow,mul_assoc] using ht.trans hm

lemma goe_word_normalized_trace_lipschitz (F : List (Matrix ι ι ℝ→Matrix ι ι ℝ)) {R : NNReal}
    (hF : ∀ f∈F,∀ M,opNorm (f M) ≤ R) (hL : ∀ f∈F,LipschitzWith R f) (r : ℝ) :
    LipschitzWith (⟨(Fintype.card ι:ℝ)⁻¹,inv_nonneg.mpr (Nat.cast_nonneg _)⟩*
      (⟨sqrt (Fintype.card ι),sqrt_nonneg _⟩*((F.length:NNReal)*R^F.length))*⟨sqrt (2*r),sqrt_nonneg _⟩)
      (fun z : EuclideanSpace ℝ (MatrixCoordinates ι)=>trace (matrixFactorProduct F (goeMatrix r z))/(Fintype.card ι:ℝ)) := by
  apply LipschitzWith.of_dist_le_mul
  intro z w
  have hg := (goeMatrix_L2_lipschitz (ι:=ι) r).dist_le_mul z w
  have ht := (matrixFactorProduct_trace_lipschitz F hF hL).dist_le_mul (goeMatrix r z) (goeMatrix r w)
  change dist (goeMatrix r z) (goeMatrix r w) ≤ sqrt (2*r)*dist z w at hg
  change dist (trace (matrixFactorProduct F (goeMatrix r z))) (trace (matrixFactorProduct F (goeMatrix r w))) ≤
    (sqrt (Fintype.card ι)*((F.length:ℝ)*(R:ℝ)^F.length))*dist (goeMatrix r z) (goeMatrix r w) at ht
  have hc : 0 ≤ sqrt (Fintype.card ι)*((F.length:ℝ)*(R:ℝ)^F.length) := by positivity
  have hi : 0 ≤ (Fintype.card ι:ℝ)⁻¹ := inv_nonneg.mpr (Nat.cast_nonneg _)
  have hb := mul_le_mul_of_nonneg_left (ht.trans (mul_le_mul_of_nonneg_left hg hc)) hi
  change dist (trace (matrixFactorProduct F (goeMatrix r z))/(Fintype.card ι:ℝ))
    (trace (matrixFactorProduct F (goeMatrix r w))/(Fintype.card ι:ℝ)) ≤
    ((Fintype.card ι:ℝ)⁻¹*(sqrt (Fintype.card ι)*((F.length:ℝ)*(R:ℝ)^F.length))*sqrt (2*r))*dist z w
  rw [Real.dist_eq,← sub_div,abs_div]
  simp only [abs_of_nonneg (show (0:ℝ) ≤ (Fintype.card ι:ℝ) by positivity)]
  simpa only [Real.dist_eq,div_eq_mul_inv,mul_assoc,mul_comm (Fintype.card ι:ℝ)⁻¹] using hb
end SKGap
end
end

end OAI
end

section
-- module Solutions.OAIQ074_CM.SKGap_Gaussian_MatrixWordMoments
attribute [-instance] _root_.OAI.SKGap.ComplexMatrix.frobeniusInnerProduct
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
namespace SKGap
open Real Matrix MeasureTheory ProbabilityTheory
open scoped BigOperators Matrix.Norms.Frobenius

lemma goe_word_trace_lip_scaled {n : ℕ} (hn : 0<n) {j : ℝ} (hj : 0≤j)
    (F : List (Matrix (Fin n) (Fin n) ℝ→Matrix (Fin n) (Fin n) ℝ)) {R : NNReal}
    (hF : ∀ f∈F,∀ M,opNorm (f M) ≤ R) (hL : ∀ f∈F,LipschitzWith R f) :
    LipschitzWith ⟨((F.length:ℝ)*(R:ℝ)^F.length)*sqrt (2*j)/(n:ℝ),by positivity⟩
      (fun z : EuclideanSpace ℝ (MatrixCoordinates (Fin n))=>
        trace (matrixFactorProduct F (goeMatrix (j/n) z))/(n:ℝ)) := by
  have hnr : (0:ℝ)<n := Nat.cast_pos.mpr hn
  have he : (n:ℝ)⁻¹*(sqrt (n:ℝ)*((F.length:ℝ)*(R:ℝ)^F.length))*sqrt (2*(j/n))=
      ((F.length:ℝ)*(R:ℝ)^F.length)*sqrt (2*j)/(n:ℝ) := by
    rw [show 2*(j/(n:ℝ))=(2*j)/(n:ℝ) by ring,sqrt_div (mul_nonneg (by norm_num) hj)]
    field_simp [ne_of_gt hnr,ne_of_gt (sqrt_pos.2 hnr)]
  have hh := goe_word_normalized_trace_lipschitz F hF hL (j/n)
  simpa only [Fintype.card_fin,show (⟨(n:ℝ)⁻¹,inv_nonneg.mpr (Nat.cast_nonneg n)⟩ *
      (⟨sqrt (n:ℝ),sqrt_nonneg _⟩*((F.length:NNReal)*R^F.length))*⟨sqrt (2*(j/n)),sqrt_nonneg _⟩ : NNReal)=
      ⟨((F.length:ℝ)*(R:ℝ)^F.length)*sqrt (2*j)/(n:ℝ),by positivity⟩ from NNReal.eq he] using hh

theorem goe_word_trace_centered_L1 {n : ℕ} (hn : 0<n) {j : ℝ} (hj : 0<j)
    (F : List (Matrix (Fin n) (Fin n) ℝ→Matrix (Fin n) (Fin n) ℝ))
    (hFl : 0<F.length) {R : NNReal} (hR : 0<R)
    (hF : ∀ f∈F,∀ M,opNorm (f M) ≤ R) (hL : ∀ f∈F,LipschitzWith R f) :
    (∫ g : MatrixCoordinates (Fin n)→ℝ,
      |trace (matrixFactorProduct F (goeMatrix (j/n) g))/(n:ℝ)-
        ∫ h : MatrixCoordinates (Fin n)→ℝ,trace (matrixFactorProduct F (goeMatrix (j/n) h))/(n:ℝ)
          ∂Measure.pi (fun _=>gaussianReal 0 1)|
        ∂Measure.pi (fun _=>gaussianReal 0 1)) ≤
      (2*exp (π^2/8))*((F.length:ℝ)*(R:ℝ)^F.length)*sqrt (2*j)/(n:ℝ) := by
  have hnr : (0:ℝ)<n := Nat.cast_pos.mpr hn
  have hRr : (0:ℝ)<R := hR
  have hlr : (0:ℝ)<F.length := Nat.cast_pos.mpr hFl
  have hh := gaussianProduct_centered_L1 (goe_word_trace_lip_scaled hn hj.le F hF hL)
    (by change 0<((F.length:ℝ)*(R:ℝ)^F.length)*sqrt (2*j)/(n:ℝ); positivity)
  apply hh.trans_eq
  change (2*exp (π^2/8))*(((F.length:ℝ)*(R:ℝ)^F.length)*sqrt (2*j)/(n:ℝ))=_
  ring

lemma goe_word_trace_centered_L1_all {n : ℕ} (hn : 0<n) {j : ℝ} (hj : 0<j)
    (F : List (Matrix (Fin n) (Fin n) ℝ→Matrix (Fin n) (Fin n) ℝ))
    {R : NNReal} (hR : 0<R)
    (hF : ∀ f∈F,∀ M,opNorm (f M) ≤ R) (hL : ∀ f∈F,LipschitzWith R f) :
    (∫ g : MatrixCoordinates (Fin n)→ℝ,
      |trace (matrixFactorProduct F (goeMatrix (j/n) g))/(n:ℝ)-
        ∫ h : MatrixCoordinates (Fin n)→ℝ,trace (matrixFactorProduct F (goeMatrix (j/n) h))/(n:ℝ)
          ∂Measure.pi (fun _=>gaussianReal 0 1)|
        ∂Measure.pi (fun _=>gaussianReal 0 1)) ≤
      (2*exp (π^2/8))*((F.length:ℝ)*(R:ℝ)^F.length)*sqrt (2*j)/(n:ℝ) := by
  by_cases he : F=[]
  · subst F
    simp only [matrixFactorProduct_nil,List.length_nil,Nat.cast_zero,zero_mul,mul_zero,zero_div]
    simp
  · exact goe_word_trace_centered_L1 hn hj F (List.length_pos_iff.mpr he) hR hF hL
end SKGap
end
end

end OAI
end

section
-- module Solutions.OAIQ074_CM.SKGap_Matrix_Word
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
namespace SKGap
open Real Matrix MeasureTheory ProbabilityTheory Set
open RealComplex
open scoped BigOperators Matrix.Norms.Frobenius SchwartzMap

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma WordLetter.eval_bounds [Nonempty ι] (f : 𝓢(ℝ,ℂ)) {R j A D z : ℝ}
    (hR : 0≤R) (hj : 0≤j) (hA : 0≤A) (hD : 0≤D) {a : ι→ℝ}
    (ha : ∀ i,0≤a i) (haA : ∀ i,a i≤A) (hz : z∈Icc (0:ℝ) 1)
    (l : WordLetter ι) (hl : l.bounded D) :
    (∀ M,opNorm (l.eval f R hR j a z M) ≤ actualWordBound f R j A D) ∧
    LipschitzWith ⟨actualWordBound f R j A D,(actualWordBound_pos f hR hj hA hD).le⟩
      (l.eval f R hR j a z) := by
  have hconst := path_constants_nonneg f hR hj hA
  have hD' : D ≤ actualWordBound f R j A D := by unfold actualWordBound;linarith
  have hR' : R ≤ actualWordBound f R j A D := by unfold actualWordBound;linarith
  have h1 : 1 ≤ actualWordBound f R j A D := by unfold actualWordBound;linarith
  have hB : pathBound f R j A ≤ actualWordBound f R j A D := by unfold actualWordBound;linarith
  have hL : pathLip f R j A ≤ actualWordBound f R j A D := by unfold actualWordBound;linarith
  cases l with
  | diag d =>
    constructor
    · intro M;exact (opNorm_diagonal_le hD hl).trans hD'
    · exact (LipschitzWith.const (diagonal d)).weaken (show (0:NNReal) ≤ _ from zero_le)
  | noise =>
    constructor
    · intro M;exact (realProject_opNorm hR M).trans hR'
    · exact (realProject_lipschitz hR).weaken h1
  | inverse =>
    have hh := pathK_bounds f hR hj hA ha haA hz
    constructor
    · intro M;exact (hh.1 M).trans hB
    · apply LipschitzWith.of_dist_le_mul
      intro M N
      change ‖pathK f R hR j a z M-pathK f R hR j a z N‖ ≤ actualWordBound f R j A D*‖M-N‖
      exact (hh.2 M N).trans (mul_le_mul_of_nonneg_right hL (norm_nonneg _))

theorem actualWord_bounds [Nonempty ι] (f : 𝓢(ℝ,ℂ)) {R j A D z : ℝ}
    (hR : 0≤R) (hj : 0≤j) (hA : 0≤A) (hD : 0≤D) {a : ι→ℝ}
    (ha : ∀ i,0≤a i) (haA : ∀ i,a i≤A) (hz : z∈Icc (0:ℝ) 1)
    (F : List (WordLetter ι)) (hF : ∀ l∈F,l.bounded D) :
    (∀ M,opNorm (actualWord f R hR j a z F M) ≤ (actualWordBound f R j A D)^F.length) ∧
    LipschitzWith ((F.length:NNReal)*⟨actualWordBound f R j A D,(actualWordBound_pos f hR hj hA hD).le⟩^F.length)
      (actualWord f R hR j a z F) := by
  let B : NNReal := ⟨actualWordBound f R j A D,(actualWordBound_pos f hR hj hA hD).le⟩
  let G := F.map (WordLetter.eval f R hR j a z)
  have hGb : ∀ p∈G,∀ M,opNorm (p M) ≤ B := by
    intro p hp
    obtain ⟨l,hl,rfl⟩ := List.mem_map.mp hp
    exact (l.eval_bounds f hR hj hA hD ha haA hz (hF l hl)).1
  have hGl : ∀ p∈G,LipschitzWith B p := by
    intro p hp
    obtain ⟨l,hl,rfl⟩ := List.mem_map.mp hp
    exact (l.eval_bounds f hR hj hA hD ha haA hz (hF l hl)).2
  constructor
  · intro M
    simpa only [G,B,actualWord,List.length_map,NNReal.coe_mk] using! matrixFactorProduct_opNorm G hGb M
  · simpa only [G,B,actualWord,List.length_map] using! (@matrixFactorProduct_lipschitz ι (Matrix ι ι ℝ) _ _ (inferInstance : MetricSpace (Matrix ι ι ℝ)).toPseudoMetricSpace G B hGb hGl)
end SKGap
end
end

end OAI
end

section
-- module Solutions.OAIQ074_CM.SKGap_Matrix_MarkedWordIBP
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
namespace SKGap
open Matrix Real MeasureTheory ProbabilityTheory Set
open scoped BigOperators Matrix.Norms.Frobenius SchwartzMap
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma actualWord_append (f : 𝓢(ℝ,ℂ)) {R : ℝ} (hR : 0≤R) (j : ℝ) (a : ι→ℝ) (z : ℝ)
    (F G : List (WordLetter ι)) (M : Matrix ι ι ℝ) :
    actualWord f R hR j a z (F++G) M=actualWord f R hR j a z F M*actualWord f R hR j a z G M := by
  simp only [actualWord,matrixFactorProduct,List.map_append,List.prod_append]

end SKGap
end
end

section
noncomputable section
namespace SKGap
open Matrix Real
open scoped BigOperators Matrix.Norms.Frobenius
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma matrix_word_contraction (U V Q : Matrix ι ι ℝ) (i : ι) :
    (∑ a,∑ b,U i a*(V*symmetricElementary a b*Q) b i) =
      (U*Q) i i*trace V+(U*Vᵀ*Q) i i := by
  simp_rw [mul_symmetricElementary_mul,mul_add]
  simp only [Finset.sum_add_distrib]
  have h1 : (∑ a,∑ b,U i a*(V b a*Q b i))=(U*Vᵀ*Q) i i := by
    simp only [Matrix.mul_apply,transpose_apply,Finset.sum_mul]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro b _;apply Finset.sum_congr rfl
    intro a _;ring
  have h2 : (∑ a,∑ b,U i a*(V b b*Q a i))=(U*Q) i i*trace V := by
    simp only [Matrix.mul_apply,Matrix.trace,Finset.sum_mul,Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro a _;apply Finset.sum_congr rfl
    intro b _;dsimp only [Matrix.diag];ring
  rw [h1,h2,add_comm]

lemma matrix_word_reverse_bound (U V Q : Matrix ι ι ℝ) (i : ι) :
    |(U*Vᵀ*Q) i i| ≤ opNorm U*opNorm V*opNorm Q := by
  apply (matrix_entry_le_opNorm (U*Vᵀ*Q) i i).trans
  apply (opNorm_mul (U*Vᵀ) Q).trans
  have hh := mul_le_mul_of_nonneg_right (opNorm_mul U Vᵀ) (show 0 ≤ opNorm Q from norm_nonneg _)
  simpa only [opNorm_transpose] using hh

end SKGap
end
end

end OAI
end

section
-- module Solutions.OAIQ074_CM.SKGap_Localization_MarkedErrorRate
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
namespace SKGap
open Real
open scoped NNReal ENNReal

lemma power_tail_absorptions (k : ℕ) {c n p : ℝ} (hc : 0 < c) (hn : 0<n)
    (hp : p≤3*exp (-c*n)) :
    n^k*p≤(3*((k+1).factorial:ℝ)/c^(k+1))/n ∧
      n^k*sqrt p≤(sqrt 3*((k+1).factorial:ℝ)/(c/2)^(k+1))/n := by
  have h1 := power_exponential_bound (k+1) hc hn.le
  have h2 := power_exponential_bound (k+1) (half_pos hc) hn.le
  have hsp : sqrt p≤ sqrt 3*exp (-(c/2)*n) := by
    apply (sqrt_le_sqrt hp).trans_eq
    rw [sqrt_mul (by norm_num : (0:ℝ)≤3),← exp_half]
    congr 2
    ring
  constructor
  · apply (le_div_iff₀ hn).mpr
    have hh := mul_le_mul_of_nonneg_left hp (pow_nonneg hn.le (k+1))
    calc
      n^k*p*n=n^(k+1)*p := by rw [pow_succ];ring
      _ ≤ n^(k+1)*(3*exp (-c*n)) := hh
      _ = 3*(n^(k+1)*exp (-c*n)) := by ring
      _ ≤ 3*(((k+1).factorial:ℝ)/c^(k+1)) := mul_le_mul_of_nonneg_left h1 (by norm_num)
      _ = _ := by ring
  · apply (le_div_iff₀ hn).mpr
    calc
      n^k*sqrt p*n=n^(k+1)*sqrt p := by rw [pow_succ];ring
      _ ≤ n^(k+1)*(sqrt 3*exp (-(c/2)*n)) := mul_le_mul_of_nonneg_left hsp (pow_nonneg hn.le _)
      _ = sqrt 3*(n^(k+1)*exp (-(c/2)*n)) := by ring
      _ ≤ sqrt 3*(((k+1).factorial:ℝ)/(c/2)^(k+1)) := mul_le_mul_of_nonneg_left h2 (sqrt_nonneg _)
      _ = _ := by ring

lemma marked_coordinate_factor {n : ℕ} (hn : 0<n) :
    (((Fintype.card (MatrixCoordinates (Fin n)):NNReal)^(1/(2:ℝ≥0∞)).toReal:NNReal):ℝ)≤2*(n:ℝ)^2 := by
  have hnr : (1:ℝ)≤n := by exact_mod_cast hn
  have he : (1/(2:ℝ≥0∞)).toReal=(1/2:ℝ) := by norm_num
  rw [NNReal.coe_rpow,NNReal.coe_natCast,he]
  have hcard : (Fintype.card (MatrixCoordinates (Fin n)):ℝ)=(n:ℝ)^2+n := by
    simp [MatrixCoordinates,pow_two]
  rw [hcard]
  exact (rpow_le_self_of_one_le (by nlinarith : (1:ℝ)≤(n:ℝ)^2+n) (by norm_num : (1/2:ℝ)≤1)).trans
    (by nlinarith)

theorem markedError_absorption {n : ℕ} (hn : 0<n) {j R c p : ℝ}
    (hj : 0≤j) (hR : 0≤R) (hc : 0 < c) (hp0 : 0≤p) (hp : p≤3*exp (-c*(n:ℝ)))
    (L K B C : NNReal) {D E : ℝ} (hD : 0≤D) (hE : 0≤E) :
    markedError (ι:=Fin n) (j/(n:ℝ)) R L K B C D E p≤
      markedRateConstant j R c L K B C D E/(n:ℝ) := by
  have hnr : (1:ℝ)≤n := by exact_mod_cast hn
  have hn0 : (0:ℝ)<n := by exact_mod_cast hn
  have hr : j/(n:ℝ)≤j := div_le_self hj hnr
  have hs : sqrt (2*(j/(n:ℝ)))≤ sqrt (2*j) := sqrt_le_sqrt (by linarith)
  have hcoord := marked_coordinate_factor hn
  have h0 := (power_tail_absorptions 0 hc hn0 hp).1
  have h2 := (power_tail_absorptions 2 hc hn0 hp).2
  have h4 := (power_tail_absorptions 4 hc hn0 hp).1
  norm_num only [pow_zero,one_mul,Nat.factorial_succ,Nat.factorial_zero,Nat.cast_mul,Nat.cast_one,Nat.cast_ofNat] at h0 h2 h4
  let S := sqrt (2*j)
  let V : ℝ := (L*C+B*K:NNReal)
  let Z : ℝ := D*C+B*E
  have hS : 0≤S := sqrt_nonneg _
  have hV : 0≤V := NNReal.coe_nonneg _
  have hZ : 0≤Z := by dsimp [Z];positivity
  have ht : sqrt (2*(j/(n:ℝ)))*
      ((L*C+B*K:NNReal)*(⟨sqrt (2*(j/(n:ℝ))),sqrt_nonneg _⟩*
        (Fintype.card (MatrixCoordinates (Fin n)):NNReal)^(1/(2:ℝ≥0∞)).toReal):NNReal)≤
        2*S^2*V*(n:ℝ)^2 := by
    simp only [NNReal.coe_mul]
    have hh := mul_le_mul hs
      (mul_le_mul_of_nonneg_left (mul_le_mul hs hcoord
        (NNReal.coe_nonneg _) hS) hV) (by positivity) hS
    apply hh.trans_eq
    dsimp [S,V]
    ring
  have hu : sqrt (2*(j/(n:ℝ)))*
      ((L*C+B*K:NNReal)*(⟨sqrt (2*(j/(n:ℝ))),sqrt_nonneg _⟩*
        (Fintype.card (MatrixCoordinates (Fin n)):NNReal)^(1/(2:ℝ≥0∞)).toReal):NNReal)+
        (j/(n:ℝ))*(D*C+B*E)≤(2*S^2*V+j*Z)*(n:ℝ)^2 := by
    have hnn : (1:ℝ)≤(n:ℝ)^2 := one_le_pow₀ hnr
    have h1 := add_le_add ht (mul_le_mul_of_nonneg_right hr hZ)
    have h2 : j*Z≤j*Z*(n:ℝ)^2 := by nlinarith [mul_nonneg (mul_nonneg hj hZ) (sub_nonneg.mpr hnn)]
    dsimp only [Z] at h1 h2 ⊢
    nlinarith only [h1,h2]
  have hm : markedError (ι:=Fin n) (j/(n:ℝ)) R L K B C D E p≤
      (B:ℝ)*R*C*p+B*C*S*((n:ℝ)^2*sqrt p)+(2*S^2*V+j*Z)*((n:ℝ)^4*p) := by
    unfold markedError
    simp only [Fintype.card_fin]
    apply add_le_add
    · apply add_le_add le_rfl
      have hh := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hs
        (show 0≤(B:ℝ)*C*(n:ℝ)^2 by positivity)) (sqrt_nonneg p)
      convert hh using 1; dsimp [S]; ring
    · have hh := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hu (sq_nonneg (n:ℝ))) hp0
      convert hh using 1 <;> first | rfl | ring
  apply hm.trans
  have hb0 := mul_le_mul_of_nonneg_left h0 (show 0≤(B:ℝ)*R*C by positivity)
  have hb2 := mul_le_mul_of_nonneg_left h2 (show 0≤(B:ℝ)*C*S by positivity)
  have hb4 := mul_le_mul_of_nonneg_left h4 (show 0≤2*S^2*V+j*Z by positivity)
  apply (add_le_add (add_le_add hb0 hb2) hb4).trans_eq
  unfold markedRateConstant
  dsimp only [S,V,Z]
  ring
end SKGap
end
end

end OAI
end

section
-- module Solutions.OAIQ074_CM.SKGap_Matrix_WordBaseBias
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
namespace SKGap
open Real Matrix MeasureTheory ProbabilityTheory
open scoped BigOperators Matrix.Norms.Frobenius

lemma matrix_word_expectation_contraction {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] {n : ℕ} (hn : 0<n)
    (U V Q : Ω→Matrix (Fin n) (Fin n) ℝ) (i : Fin n)
    {j BU BQ BV T : ℝ} (hj : 0≤j) (hBU : 0≤BU) (_hBQ : 0≤BQ) (hBV : 0≤BV)
    (hU : ∀ ω,opNorm (U ω) ≤ BU) (hQ : ∀ ω,opNorm (Q ω) ≤ BQ)
    (hV : ∀ ω,opNorm (V ω) ≤ BV)
    (hY : AEStronglyMeasurable (fun ω=>(U ω*Q ω) i i) μ)
    (hZ : AEStronglyMeasurable (fun ω=>(U ω*(V ω)ᵀ*Q ω) i i) μ)
    (hX : Integrable (fun ω=>trace (V ω)/(n:ℝ)) μ)
    (hT : (∫ ω,|trace (V ω)/(n:ℝ)-∫ v,trace (V v)/(n:ℝ) ∂μ| ∂μ) ≤ T) :
    |(j/(n:ℝ))*(∫ ω,∑ a,∑ b,U ω i a*(V ω*symmetricElementary a b*Q ω) b i ∂μ)-
      j*(∫ ω,trace (V ω)/(n:ℝ) ∂μ)*(∫ ω,(U ω*Q ω) i i ∂μ)| ≤
      j*(BU*BQ*T+BU*BV*BQ/(n:ℝ)) := by
  have hnr : (0:ℝ)<n := Nat.cast_pos.mpr hn
  have hYb : ∀ ω,‖(U ω*Q ω) i i‖ ≤ BU*BQ := by
    intro ω
    exact (matrix_entry_le_opNorm _ i i).trans ((opNorm_mul _ _).trans
      (mul_le_mul (hU ω) (hQ ω) (norm_nonneg _) hBU))
  have hZb : ∀ ω,‖(U ω*(V ω)ᵀ*Q ω) i i/(n:ℝ)‖ ≤ BU*BV*BQ/(n:ℝ) := by
    intro ω
    rw [norm_div,Real.norm_of_nonneg hnr.le]
    apply div_le_div_of_nonneg_right _ hnr.le
    exact (matrix_word_reverse_bound (U ω) (V ω) (Q ω) i).trans
      (mul_le_mul (mul_le_mul (hU ω) (hV ω) (norm_nonneg _) hBU) (hQ ω) (norm_nonneg _) (mul_nonneg hBU hBV))
  have hZi : Integrable (fun ω=>(U ω*(V ω)ᵀ*Q ω) i i/(n:ℝ)) μ :=
    (integrable_const (BU*BV*BQ/(n:ℝ))).mono' (by simpa only [div_eq_mul_inv,Pi.mul_apply] using! hZ.mul (g := fun _ => (n:ℝ)⁻¹) aestronglyMeasurable_const) (ae_of_all _ hZb)
  have he : (∫ ω,(j/(n:ℝ))*(∑ a,∑ b,U ω i a*(V ω*symmetricElementary a b*Q ω) b i) ∂μ) =
      j*(∫ ω,(trace (V ω)/(n:ℝ))*((U ω*Q ω) i i)+(U ω*(V ω)ᵀ*Q ω) i i/(n:ℝ) ∂μ) := by
    rw [← integral_const_mul]
    apply integral_congr_ae
    filter_upwards [] with ω
    rw [matrix_word_contraction]
    ring
  have hh := integral_loop_deviation (μ:=μ) hj hX hY (ae_of_all _ hYb)
    hZi (ae_of_all _ hZb) hT
    (V:=fun ω=>(j/(n:ℝ))*(∑ a,∑ b,U ω i a*(V ω*symmetricElementary a b*Q ω) b i))
    (E:=0) (by rw [he,sub_self,abs_zero])
  simpa only [integral_const_mul,zero_add] using hh

theorem goe_word_leading_contraction {n : ℕ} (hn : 0<n) {j : ℝ} (hj : 0<j)
    (F : List (Matrix (Fin n) (Fin n) ℝ→Matrix (Fin n) (Fin n) ℝ))
    {R : NNReal} (hR : 0<R)
    (hF : ∀ f∈F,∀ M,opNorm (f M) ≤ R) (hL : ∀ f∈F,LipschitzWith R f)
    (U Q : Matrix (Fin n) (Fin n) ℝ→Matrix (Fin n) (Fin n) ℝ)
    (hUc : Continuous U) (hQc : Continuous Q) {BU BQ : ℝ} (hBU : 0≤BU) (hBQ : 0≤BQ)
    (hU : ∀ M,opNorm (U M) ≤ BU) (hQ : ∀ M,opNorm (Q M) ≤ BQ) (i : Fin n) :
    let μ := Measure.pi (fun _ : MatrixCoordinates (Fin n)=>gaussianReal 0 1)
    let W := goeMatrix (j/n)
    |(j/(n:ℝ))*(∫ g,∑ a,∑ b,U (W g) i a*
      (matrixFactorProduct F (W g)*symmetricElementary a b*Q (W g)) b i ∂μ)-
      j*(∫ g,trace (matrixFactorProduct F (W g))/(n:ℝ) ∂μ)*(∫ g,(U (W g)*Q (W g)) i i ∂μ)| ≤
      (j*(BU*BQ*((2*exp (π^2/8))*((F.length:ℝ)*(R:ℝ)^F.length)*sqrt (2*j))+
        BU*(R:ℝ)^F.length*BQ))/(n:ℝ) := by
  dsimp only
  have hG := (goeMatrix_pi_lipschitz (ι:=Fin n) (j/n)).continuous
  have hW := (matrixFactorProduct_lipschitz F hF hL).continuous.comp hG
  have hUc' := hUc.comp hG
  have hQc' := hQc.comp hG
  have hY : Continuous (fun g : MatrixCoordinates (Fin n)→ℝ=>(U (goeMatrix (j/n) g)*Q (goeMatrix (j/n) g)) i i) := by
    exact (continuous_apply i).comp ((continuous_apply i).comp (hUc'.mul hQc'))
  have hZ : Continuous (fun g : MatrixCoordinates (Fin n)→ℝ=>
      (U (goeMatrix (j/n) g)*(matrixFactorProduct F (goeMatrix (j/n) g))ᵀ*Q (goeMatrix (j/n) g)) i i) := by
    exact (continuous_apply i).comp ((continuous_apply i).comp ((hUc'.mul hW.matrix_transpose).mul hQc'))
  have hh := matrix_word_expectation_contraction
    (Measure.pi (fun _ : MatrixCoordinates (Fin n)=>gaussianReal 0 1)) hn
    (fun g=>U (goeMatrix (j/n) g)) (fun g=>matrixFactorProduct F (goeMatrix (j/n) g))
    (fun g=>Q (goeMatrix (j/n) g)) i hj.le hBU hBQ (pow_nonneg R.coe_nonneg _)
    (fun g=>hU _) (fun g=>hQ _) (fun g=>matrixFactorProduct_opNorm F hF _)
    hY.aestronglyMeasurable hZ.aestronglyMeasurable
    (gaussianProduct_integrable_lipschitz (goe_word_trace_lip_scaled hn hj.le F hF hL))
    (goe_word_trace_centered_L1_all hn hj F hR hF hL)
  apply hh.trans_eq
  ring
end SKGap
end
end

end OAI
end

section
-- module Solutions.OAIQ074_CM.SKGap_Matrix_WordLeading
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
namespace SKGap
open Matrix Real MeasureTheory ProbabilityTheory Set
open scoped BigOperators Matrix.Norms.Frobenius SchwartzMap
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma actualWord_entry_integrable [Nonempty ι] (f : 𝓢(ℝ,ℂ)) {R j A D z r : ℝ}
    (hR : 0≤R) (hj : 0≤j) (hA : 0≤A) (hD : 0≤D) {a : ι→ℝ}
    (ha : ∀ i,0≤a i) (haA : ∀ i,a i≤A) (hz : z∈Icc (0:ℝ) 1)
    (F : List (WordLetter ι)) (hF : ∀ l∈F,l.bounded D) (i b : ι) :
    Integrable (fun g : MatrixCoordinates ι→ℝ=>actualWord f R hR j a z F (goeMatrix r g) i b)
      (Measure.pi (fun _=>gaussianReal 0 1)) := by
  have hw := actualWord_bounds f hR hj hA hD ha haA hz F hF
  have hc := hw.2.continuous.comp (goeMatrix_pi_lipschitz (ι:=ι) r).continuous
  have he : Continuous (fun g : MatrixCoordinates ι→ℝ=>actualWord f R hR j a z F (goeMatrix r g) i b) :=
    (continuous_apply b).comp ((continuous_apply i).comp hc)
  exact (integrable_const ((actualWordBound f R j A D)^F.length)).mono' he.aestronglyMeasurable
    (ae_of_all _ (fun g=>(matrix_entry_le_opNorm _ i b).trans (hw.1 _)))

lemma wordAverageExpected_integral [Nonempty ι] (f : 𝓢(ℝ,ℂ)) {R j A D z : ℝ}
    (hR : 0≤R) (hj : 0≤j) (hA : 0≤A) (hD : 0≤D) {a : ι→ℝ}
    (ha : ∀ i,0≤a i) (haA : ∀ i,a i≤A) (hz : z∈Icc (0:ℝ) 1)
    (F : List (WordLetter ι)) (hF : ∀ l∈F,l.bounded D) :
    (∫ g : MatrixCoordinates ι→ℝ,trace (actualWord f R hR j a z F
      (goeMatrix (j/(Fintype.card ι:ℝ)) g))/(Fintype.card ι:ℝ)
        ∂Measure.pi (fun _=>gaussianReal 0 1))=wordAverageExpected f hR j a z F := by
  rw [integral_div]
  unfold trace
  simp only [Matrix.diag]
  rw [integral_finsetSum _ (fun i _=>actualWord_entry_integrable f hR hj hA hD ha haA hz F hF i i)]
  rfl

theorem actualWord_leading {n : ℕ} (hn : 0<n) (f : 𝓢(ℝ,ℂ)) {R j A D z : ℝ}
    (hR : 0≤R) (hj : 0<j) (hA : 0≤A) (hD : 0≤D) {a : Fin n→ℝ}
    (ha : ∀ i,0≤a i) (haA : ∀ i,a i≤A) (hz : z∈Icc (0:ℝ) 1)
    (U V Q : List (WordLetter (Fin n))) (hU : ∀ l∈U,l.bounded D)
    (hV : ∀ l∈V,l.bounded D) (hQ : ∀ l∈Q,l.bounded D) (i : Fin n) :
    let μ := Measure.pi (fun _ : MatrixCoordinates (Fin n)=>gaussianReal 0 1)
    |(j/(n:ℝ))*(∫ g,markedContraction
      (actualWord f R hR j a z U (goeMatrix (j/n) g))
      (actualWord f R hR j a z V (goeMatrix (j/n) g))
      (actualWord f R hR j a z Q (goeMatrix (j/n) g)) i ∂μ)-
        j*wordAverageExpected f hR j a z V*wordExpected f hR j a z (U++Q) i|≤
      wordLeadingCost j (actualWordBound f R j A D) U.length V.length Q.length/(n:ℝ) := by
  let : Nonempty (Fin n) := Fin.pos_iff_nonempty.mp hn
  dsimp only
  let B : NNReal := ⟨actualWordBound f R j A D,(actualWordBound_pos f hR hj.le hA hD).le⟩
  let G := V.map (WordLetter.eval f R hR j a z)
  have hGb : ∀ p∈G,∀ M,opNorm (p M)≤B := by
    intro p hp
    obtain ⟨l,hl,rfl⟩ := List.mem_map.mp hp
    exact (l.eval_bounds f hR hj.le hA hD ha haA hz (hV l hl)).1
  have hGl : ∀ p∈G,LipschitzWith B p := by
    intro p hp
    obtain ⟨l,hl,rfl⟩ := List.mem_map.mp hp
    exact (l.eval_bounds f hR hj.le hA hD ha haA hz (hV l hl)).2
  have hu := actualWord_bounds f hR hj.le hA hD ha haA hz U hU
  have hq := actualWord_bounds f hR hj.le hA hD ha haA hz Q hQ
  have hh := goe_word_leading_contraction hn hj G
    (show 0<B from actualWordBound_pos f hR hj.le hA hD) hGb hGl
    (actualWord f R hR j a z U) (actualWord f R hR j a z Q) hu.2.continuous hq.2.continuous
    (pow_nonneg B.coe_nonneg U.length) (pow_nonneg B.coe_nonneg Q.length) hu.1 hq.1 i
  have he := wordAverageExpected_integral f hR hj.le hA hD ha haA hz V hV
  simp only [G,List.length_map,matrix_word_contraction,B] at hh
  simp only [Fintype.card_fin,actualWord] at he
  rw [he] at hh
  have heq : wordExpected f hR j a z (U++Q) i=
      ∫ g : MatrixCoordinates (Fin n)→ℝ,(actualWord f R hR j a z U (goeMatrix (j/n) g)*
        actualWord f R hR j a z Q (goeMatrix (j/n) g)) i i
          ∂Measure.pi (fun _=>gaussianReal 0 1) := by
    simp only [wordExpected,Fintype.card_fin,actualWord_append]
  rw [← heq] at hh
  simpa only [actualWord,wordLeadingCost,markedContraction] using! hh
end SKGap
end
end

end OAI
end

section
-- module Solutions.OAIQ074_CM.SKGap_Matrix_WordLoop
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
namespace SKGap
variable {ι : Type*}

lemma wordPartners_preserves_bound {a : ι→ℝ} {D : ℝ} (ha : ∀ i,|a i|≤D)
    (F : List (WordLetter ι)) (hF : ∀ l∈F,l.bounded D) (c : WordCut ι)
    (hc : c∈wordPartners a F) :
    (∀ l∈c.left,l.bounded D) ∧ (∀ l∈c.right,l.bounded D) := by
  induction F generalizing c with
  | nil => simp [wordPartners] at hc
  | cons l F ih =>
    have hFt : ∀ l∈F,l.bounded D := fun m hm=>hF m (List.mem_cons_of_mem _ hm)
    rw [wordPartners_cons,List.mem_append] at hc
    rcases hc with hc|hc
    · cases l with
      | diag d => simp at hc
      | noise =>
        simp only [List.mem_singleton] at hc;subst c
        simpa using hFt
      | inverse =>
        simp only [List.mem_singleton] at hc;subst c
        constructor
        · intro m hm
          simp only [List.mem_cons,List.not_mem_nil,or_false] at hm
          rcases hm with rfl|rfl
          · trivial
          · exact ha
        · intro m hm
          rcases List.mem_cons.mp hm with rfl|hm
          · trivial
          · exact hFt m hm
    · obtain ⟨d,hd,rfl⟩ := List.mem_map.mp hc
      have hh := ih hFt d hd
      constructor
      · intro m hm
        rcases List.mem_cons.mp hm with rfl|hm
        · exact hF m List.mem_cons_self
        · exact hh.1 m hm
      · exact hh.2

end SKGap
end
end

end OAI
end

section
-- module Solutions.OAIQ074_CM.SKGap_Matrix_WordLoopLeading
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
namespace SKGap
open Matrix Real MeasureTheory ProbabilityTheory Set
open scoped BigOperators Matrix.Norms.Frobenius SchwartzMap
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma actualWord_marked_integrable [Nonempty ι] (f : 𝓢(ℝ,ℂ)) {R j A D z r : ℝ}
    (hR : 0≤R) (hj : 0≤j) (hA : 0≤A) (hD : 0≤D) {a : ι→ℝ}
    (ha : ∀ i,0≤a i) (haA : ∀ i,a i≤A) (hz : z∈Icc (0:ℝ) 1)
    (U V Q : List (WordLetter ι)) (hU : ∀ l∈U,l.bounded D)
    (hV : ∀ l∈V,l.bounded D) (hQ : ∀ l∈Q,l.bounded D) (i : ι) :
    Integrable (fun g : MatrixCoordinates ι→ℝ=>markedContraction
      (actualWord f R hR j a z U (goeMatrix r g))
      (actualWord f R hR j a z V (goeMatrix r g))
      (actualWord f R hR j a z Q (goeMatrix r g)) i)
        (Measure.pi (fun _=>gaussianReal 0 1)) := by
  let B := actualWordBound f R j A D
  have hB : 0≤B := (actualWordBound_pos f hR hj hA hD).le
  have hb (F : List (WordLetter ι)) (hF : ∀ l∈F,l.bounded D) :=
    actualWord_bounds f hR hj hA hD ha haA hz F hF
  have hc (F : List (WordLetter ι)) (hF : ∀ l∈F,l.bounded D) :=
    (hb F hF).2.continuous.comp (goeMatrix_pi_lipschitz (ι:=ι) r).continuous
  have he : Continuous (fun g : MatrixCoordinates ι→ℝ=>markedContraction
      (actualWord f R hR j a z U (goeMatrix r g))
      (actualWord f R hR j a z V (goeMatrix r g))
      (actualWord f R hR j a z Q (goeMatrix r g)) i) := by
    have huc := hc U hU
    have hvc := hc V hV
    have hqc := hc Q hQ
    unfold markedContraction Matrix.trace
    fun_prop
  apply (integrable_const ((Fintype.card ι:ℝ)*B^U.length*B^V.length*B^Q.length+
    B^U.length*B^V.length*B^Q.length)).mono' he.aestronglyMeasurable
  filter_upwards [] with g
  let u := actualWord f R hR j a z U (goeMatrix r g)
  let v := actualWord f R hR j a z V (goeMatrix r g)
  let q := actualWord f R hR j a z Q (goeMatrix r g)
  have hu : opNorm u≤B^U.length := (hb U hU).1 _
  have hv : opNorm v≤B^V.length := (hb V hV).1 _
  have hq : opNorm q≤B^Q.length := (hb Q hQ).1 _
  have ht : |trace v|≤(Fintype.card ι:ℝ)*B^V.length := by
    apply (Finset.abs_sum_le_sum_abs _ _).trans
    apply (Finset.sum_le_sum (fun k _=>(matrix_entry_le_opNorm v k k).trans hv)).trans_eq
    simp
  have huq : |(u*q) i i|≤B^U.length*B^Q.length :=
    (matrix_entry_le_opNorm _ i i).trans ((opNorm_mul _ _).trans
      (mul_le_mul hu hq (norm_nonneg _) (pow_nonneg hB _)))
  have hzq : |(u*vᵀ*q) i i|≤B^U.length*B^V.length*B^Q.length :=
    (matrix_word_reverse_bound u v q i).trans
      (mul_le_mul (mul_le_mul hu hv (norm_nonneg _) (pow_nonneg hB _)) hq
        (norm_nonneg _) (by positivity))
  change |(u*q) i i*trace v+(u*vᵀ*q) i i|≤_
  apply (abs_add_le _ _).trans
  rw [abs_mul]
  apply (add_le_add (mul_le_mul huq ht (abs_nonneg _) (by positivity)) hzq).trans_eq
  ring

omit [Fintype ι] [DecidableEq ι] in
lemma integrable_list_map_sum {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (C : List ι) (F : ι→Ω→ℝ) (hF : ∀ c∈C,Integrable (F c) μ) :
    Integrable (fun x=>(C.map (fun c=>F c x)).sum) μ := by
  induction C with
  | nil => simp
  | cons c C ih =>
    simpa only [List.map_cons,List.sum_cons,Pi.add_apply] using!
      (hF c List.mem_cons_self).add (ih (fun c hc=>hF c (List.mem_cons_of_mem _ hc)))

omit [Fintype ι] [DecidableEq ι] in
lemma integral_list_sum_bound {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (r : ℝ) (C : List ι) (F : ι→Ω→ℝ) (p e : ι→ℝ)
    (hF : ∀ c∈C,Integrable (F c) μ)
    (hb : ∀ c∈C,|r*(∫ x,F c x ∂μ)-p c|≤e c) :
    |r*(∫ x,(C.map (fun c=>F c x)).sum ∂μ)-(C.map p).sum|≤(C.map e).sum := by
  induction C with
  | nil => simp
  | cons c C ih =>
    have hFi := integrable_list_map_sum μ C F (fun c hc=>hF c (List.mem_cons_of_mem _ hc))
    simp only [List.map_cons,List.sum_cons]
    rw [integral_add (hF c List.mem_cons_self) hFi,mul_add]
    have ht := ih (fun c hc=>hF c (List.mem_cons_of_mem _ hc))
      (fun c hc=>hb c (List.mem_cons_of_mem _ hc))
    calc
      |r*(∫ x,F c x ∂μ)+r*(∫ x,(C.map (fun c=>F c x)).sum ∂μ)-(p c+(C.map p).sum)| =
        |(r*(∫ x,F c x ∂μ)-p c)+(r*(∫ x,(C.map (fun c=>F c x)).sum ∂μ)-(C.map p).sum)| := by
          congr 1
          ring
      _ ≤ _ := (abs_add_le _ _).trans (add_le_add (hb c List.mem_cons_self) ht)

omit [Fintype ι] [DecidableEq ι] in
lemma weighted_integral_error {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (F : Ω→ℝ) (c r p e : ℝ) (h : |r*(∫ x,F x ∂μ)-p|≤e) :
    |r*(∫ x,c*F x ∂μ)-c*p|≤|c| *e := by
  rw [integral_const_mul]
  have he : r*(c*(∫ x,F x ∂μ))-c*p=c*(r*(∫ x,F x ∂μ)-p) := by ring
  rw [he,abs_mul]
  exact mul_le_mul_of_nonneg_left h (abs_nonneg c)

theorem actualWord_loop_leading {n : ℕ} (hn : 0<n) (f : 𝓢(ℝ,ℂ)) {R j A D z : ℝ}
    (hR : 0≤R) (hj : 0<j) (hA : 0≤A) (hD : 0≤D) {a : Fin n→ℝ}
    (ha : ∀ i,0≤a i) (haA : ∀ i,a i≤A) (haD : ∀ i,|a i|≤D) (hz : z∈Icc (0:ℝ) 1)
    (P Q : List (WordLetter (Fin n))) (hP : ∀ l∈P,l.bounded D)
    (hQ : ∀ l∈Q,l.bounded D) (i : Fin n) :
    let μ := Measure.pi (fun _ : MatrixCoordinates (Fin n)=>gaussianReal 0 1)
    |(j/(n:ℝ))*(∫ g,actualWordLoop f hR j a z P Q (goeMatrix (j/n) g) i ∂μ)-
      wordRecursionAtExpected f hR j a z P Q i|≤
        wordRecursionAtCost j (actualWordBound f R j A D) z a P Q/(n:ℝ) := by
  let : Nonempty (Fin n) := Fin.pos_iff_nonempty.mp hn
  intro μ
  let B := actualWordBound f R j A D
  let L := fun (c : WordCut (Fin n)) (g : MatrixCoordinates (Fin n)→ℝ)=>
    c.leftContraction f hR j a z (goeMatrix (j/n) g)
      (actualWord f R hR j a z Q (goeMatrix (j/n) g)) i
  let Rf := fun (c : WordCut (Fin n)) (g : MatrixCoordinates (Fin n)→ℝ)=>
    c.rightContraction f hR j a z (goeMatrix (j/n) g)
      (actualWord f R hR j a z P (goeMatrix (j/n) g)) i
  let pL := fun c : WordCut (Fin n)=>(if c.inversePartner then z else 1)*j*
    wordAverageExpected f hR j a z c.right*wordExpected f hR j a z (c.left++Q) i
  let pR := fun c : WordCut (Fin n)=>(if c.inversePartner then z else 1)*j*
    wordAverageExpected f hR j a z c.left*wordExpected f hR j a z (P++c.right) i
  let eL := fun c : WordCut (Fin n)=>|if c.inversePartner then z else 1| *
    wordLeadingCost j B c.left.length c.right.length Q.length/(n:ℝ)
  let eR := fun c : WordCut (Fin n)=>|if c.inversePartner then z else 1| *
    wordLeadingCost j B P.length c.left.length c.right.length/(n:ℝ)
  have hLb (c : WordCut (Fin n)) (hc : c∈wordPartners a P) := wordPartners_preserves_bound haD P hP c hc
  have hRb (c : WordCut (Fin n)) (hc : c∈wordPartners a Q) := wordPartners_preserves_bound haD Q hQ c hc
  have hLi : ∀ c∈wordPartners a P,Integrable (L c) μ := by
    intro c hc
    exact (actualWord_marked_integrable f hR hj.le hA hD ha haA hz c.left c.right Q
      (hLb c hc).1 (hLb c hc).2 hQ i).const_mul _
  have hRi : ∀ c∈wordPartners a Q,Integrable (Rf c) μ := by
    intro c hc
    exact (actualWord_marked_integrable f hR hj.le hA hD ha haA hz P c.left c.right
      hP (hRb c hc).1 (hRb c hc).2 i).const_mul _
  have hLe : ∀ c∈wordPartners a P,|(j/(n:ℝ))*(∫ g,L c g ∂μ)-pL c|≤eL c := by
    intro c hc
    have hh := weighted_integral_error μ _ (if c.inversePartner then z else 1) _ _ _
      (actualWord_leading hn f hR hj hA hD ha haA hz c.left c.right Q
        (hLb c hc).1 (hLb c hc).2 hQ i)
    simpa only [L,pL,eL,WordCut.leftContraction,mul_assoc,mul_div_assoc,B] using hh
  have hRe : ∀ c∈wordPartners a Q,|(j/(n:ℝ))*(∫ g,Rf c g ∂μ)-pR c|≤eR c := by
    intro c hc
    have hh := weighted_integral_error μ _ (if c.inversePartner then z else 1) _ _ _
      (actualWord_leading hn f hR hj hA hD ha haA hz P c.left c.right
        hP (hRb c hc).1 (hRb c hc).2 i)
    simpa only [Rf,pR,eR,WordCut.rightContraction,mul_assoc,mul_div_assoc,B] using hh
  have hL := integral_list_sum_bound μ (j/(n:ℝ)) (wordPartners a P) L pL eL hLi hLe
  have hR' := integral_list_sum_bound μ (j/(n:ℝ)) (wordPartners a Q) Rf pR eR hRi hRe
  have hI1 := integrable_list_map_sum μ (wordPartners a P) L hLi
  have hI2 := integrable_list_map_sum μ (wordPartners a Q) Rf hRi
  have heI : (∫ g,actualWordLoop f hR j a z P Q (goeMatrix (j/n) g) i ∂μ)=
      (∫ g,((wordPartners a P).map (fun c=>L c g)).sum ∂μ)+
        (∫ g,((wordPartners a Q).map (fun c=>Rf c g)).sum ∂μ) :=
    integral_add hI1 hI2
  have heP : wordRecursionAtExpected f hR j a z P Q i=
      ((wordPartners a P).map pL).sum+((wordPartners a Q).map pR).sum := by
    simp [wordRecursionAtExpected,wordRecursionAt,List.map_map,Function.comp_def,WordCut.asLeft,WordCut.asRight,pL,pR]
    rfl
  have heE : ((wordPartners a P).map eL).sum+((wordPartners a Q).map eR).sum=
      wordRecursionAtCost j B z a P Q/(n:ℝ) := by
    simp only [eL,eR,wordRecursionAtCost,add_div]
    congr 1 <;> induction wordPartners a _ with
    | nil => simp
    | cons c C ih => simp only [List.map_cons,List.sum_cons,add_div,ih]
  rw [heI,heP]
  have hsum := (abs_add_le ((j/(n:ℝ))*(∫ g,((wordPartners a P).map (fun c=>L c g)).sum ∂μ)-((wordPartners a P).map pL).sum)
    ((j/(n:ℝ))*(∫ g,((wordPartners a Q).map (fun c=>Rf c g)).sum ∂μ)-((wordPartners a Q).map pR).sum)).trans
      (add_le_add hL hR')
  rw [heE] at hsum
  have he : (j/(n:ℝ))*((∫ g,((wordPartners a P).map (fun c=>L c g)).sum ∂μ)+
      (∫ g,((wordPartners a Q).map (fun c=>Rf c g)).sum ∂μ))-
      (((wordPartners a P).map pL).sum+((wordPartners a Q).map pR).sum)=
      ((j/(n:ℝ))*(∫ g,((wordPartners a P).map (fun c=>L c g)).sum ∂μ)-((wordPartners a P).map pL).sum)+
      ((j/(n:ℝ))*(∫ g,((wordPartners a Q).map (fun c=>Rf c g)).sum ∂μ)-((wordPartners a Q).map pR).sum) := by ring
  rw [he]
  exact hsum

end SKGap
end
end

end OAI
end

section
-- module Solutions.OAIQ074_CM.SKGap_Matrix_WordExpectedRecursion
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
namespace SKGap
open Matrix Real MeasureTheory ProbabilityTheory Set
open scoped BigOperators Matrix.Norms.Frobenius SchwartzMap

theorem actualWord_expected_recursion_s2_oai {n : ℕ} (hn : 0<n) (f : 𝓢(ℝ,ℂ))
    {j A D z : ℝ} (hj : 0<j) (hA : 0<A) (hD : 0≤D) (hs : sqrt j*A<1)
    (hf : ∀ x∈Icc ((1-sqrt j*A)^2/4) (2+A*(2*sqrt j+1+j*A)),f x=(x:ℂ)⁻¹)
    (herr : 2*sqrt A*sqrt (sqrt (2*j^2*A^2/(n:ℝ)))≤(1-sqrt j*A)^2/4)
    {a : Fin n→ℝ} (ha : ∀ i,0≤a i) (haA : ∀ i,a i≤A) (haD : ∀ i,|a i|≤D)
    (hz : z∈Icc (0:ℝ) 1) (P Q : List (WordLetter (Fin n)))
    (hP : ∀ l∈P,l.bounded D) (hQ : ∀ l∈Q,l.bounded D) (i : Fin n) :
    let R := 2*sqrt j+1+1
    let hR : 0≤R := by dsimp [R];positivity
    let B : NNReal := ⟨actualWordBound f R j A D,(actualWordBound_pos f hR hj.le hA.le hD).le⟩
    |wordExpected f hR j a z (P++(.noise::Q)) i-wordRecursionAtExpected f hR j a z P Q i|≤
      (wordMarkedCost B j R A (pathRate j A) z P.length Q.length+
        wordRecursionAtCost j B z a P Q)/(n:ℝ) := by
  intro R hR B
  let : Nonempty (Fin n) := Fin.pos_iff_nonempty.mp hn
  have hr : 0≤j/(n:ℝ) := by positivity
  have hh := actualWord_loop f (path_interval hj.le hA.le hs).1 hf hR hj.le hA.le hD hr ha haA hz P Q hP hQ i
  have hg := path_goodSet_exponential hj hA ha haA hs (by simpa only [Fintype.card_fin] using herr) hz
  have hd (k : ℕ) : 0≤wordDifferentialBound B A z k := by
    unfold wordDifferentialBound
    positivity
  have hb := markedError_absorption hn hj.le hR (pathRate_pos hj hA hs)
    (measureReal_nonneg) (by simpa only [Fintype.card_fin] using hg)
    ((P.length:NNReal)*B^P.length) ((Q.length:NNReal)*B^Q.length)
    (B^P.length) (B^Q.length) (hd P.length) (hd Q.length)
  have hl := actualWord_loop_leading hn f hR hj hA.le hD ha haA haD hz P Q hP hQ i
  simp only [Fintype.card_fin] at hh
  have he := hh.trans hb
  have he' : |wordExpected f hR j a z (P++(.noise::Q)) i-
      (j/(n:ℝ))*(∫ g : MatrixCoordinates (Fin n)→ℝ,
      actualWordLoop f hR j a z P Q (goeMatrix (j/n) g) i
        ∂Measure.pi (fun _=>gaussianReal 0 1))|≤
      wordMarkedCost B j R A (pathRate j A) z P.length Q.length/(n:ℝ) := by
    simpa only [wordExpected,Fintype.card_fin,wordMarkedCost] using he
  have ht := (abs_sub_le (wordExpected f hR j a z (P++(.noise::Q)) i)
    ((j/(n:ℝ))*(∫ g : MatrixCoordinates (Fin n)→ℝ,
      actualWordLoop f hR j a z P Q (goeMatrix (j/n) g) i
        ∂Measure.pi (fun _=>gaussianReal 0 1)))
      (wordRecursionAtExpected f hR j a z P Q i)).trans (add_le_add he' hl)
  simpa only [wordExpected,Fintype.card_fin,wordMarkedCost,add_div,B,NNReal.coe_mk] using! ht
end SKGap
end
end

end OAI
end

theorem solution : type_of% @OAI.SKGap.actualWord_expected_recursion_s2_oai := @OAI.SKGap.actualWord_expected_recursion_s2_oai
