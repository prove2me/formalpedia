-- Prove2me | solution 1 for OAI.SKGap.actual_word_simultaneous_prediction_of_cutoff
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T06:34:14.771499+00:00
-- url     : https://prove2.me/submissions/0309fd20-8f86-4588-ae2b-85f3c069bc36

import Mathlib
import Definitions.Def_OAIQ072A000
import Theorems.Thm_OAI_SKGap_actualWord_loop
import Theorems.Thm_OAI_SKGap_all_actualWords_gaussian_chaining
import Theorems.Thm_OAI_SKGap_path_goodSet_exponential
import Theorems.Thm_OAI_SKGap_path_self_consistency

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

lemma schwartzMatrix_conjugate (f : 𝓢(ℝ,ℂ)) (U : unitary (Matrix ι ι ℂ))
    (M : Matrix ι ι ℂ) (hM : Mᴴ = M) :
    schwartzMatrix f (conjugate U M) = conjugate U (schwartzMatrix f M) := by
  have heq : (2*Real.pi : ℝ) • conjugate U M = conjugate U ((2*Real.pi : ℝ) • M) := by
    simp [conjugate,Unitary.conjStarAlgAut_apply]
  rw [schwartzMatrix,heq]
  exact kernelMatrix_conjugate (𝓕 f).integrable U _ (by simp [hM])

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
-- module Solutions.OAIQ072_SK.SKGap_Terminal_PowExponentialPair
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
-- module Solutions.OAIQ072_SK.SKGap_Localization_IntegralProductDeviation
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

lemma realTruncatedK_lipschitz (f : 𝓢(ℝ,ℂ)) {R : ℝ} (hR : 0 ≤ R)
    (D C : Matrix ι ι ℝ) (hD : Dᵀ = D) (hC : Cᵀ = C) :
    LipschitzWith (Real.toNNReal (ComplexMatrix.kLip f R (liftMatrix D) (liftMatrix C)))
      (realTruncatedK f R hR D C) := by
  apply LipschitzWith.of_dist_le_mul
  intro M N
  simp only [dist_eq_norm]
  exact (realTruncatedK_sub_norm f hR D C M N hD hC).trans
    (mul_le_mul_of_nonneg_right (Real.le_coe_toNNReal _) (norm_nonneg _))

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

lemma continuousOn_expected_realTruncatedK (f : 𝓢(ℝ,ℂ)) {R : ℝ} (hR : 0 ≤ R)
    {D C : ℝ → Matrix ι ι ℝ} (r : ℝ) (i : ι) (s : Set ℝ) (B : ℝ)
    (hD : Continuous D) (hC : Continuous C)
    (hDh : ∀ z, (D z)ᵀ=D z) (hCh : ∀ z, (C z)ᵀ=C z)
    (hB : ∀ z ∈ s, ComplexMatrix.kBound f R (liftMatrix (D z)) (liftMatrix (C z)) ≤ B) :
    ContinuousOn (fun z => ∫ g, realTruncatedK f R hR (D z) (C z) (goeMatrix r g) i i
      ∂(Measure.pi (fun _ : MatrixCoordinates ι => gaussianReal 0 1))) s := by
  apply continuousOn_of_dominated (bound := fun _ => B)
  · intro z _
    exact (((realTruncatedK_lipschitz f hR (D z) (C z) (hDh z) (hCh z)).continuous.comp
      (goeMatrix_pi_lipschitz r).continuous).matrix_elem i i).aestronglyMeasurable
  · intro z hz
    filter_upwards [] with g
    simpa only [Real.norm_eq_abs] using (matrix_entry_le_opNorm _ i i).trans
      ((realTruncatedK_opNorm f hR (D z) (C z) _ (hDh z) (hCh z)).trans (hB z hz))
  · exact integrable_const B
  · filter_upwards [] with g
    exact ((continuous_realTruncatedK_comp f hR hD hC continuous_const hDh hCh).matrix_elem i i).continuousOn

lemma realTruncatedK_zero_diagonal (f : 𝓢(ℝ,ℂ)) {R : ℝ} (hR : 0 ≤ R)
    (C M : Matrix ι ι ℝ) : realTruncatedK f R hR 0 C M=1 := by
  simp [realTruncatedK,ComplexMatrix.truncatedK,ComplexMatrix.truncatedG,RealComplex.liftMatrix,RealComplex.realPart]

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

end SKGap

namespace SKGap
open Real

lemma loopErrorConstants_nonneg (j A B L rate : ℝ)
    (hj : 0 ≤ j) (hA : 0 ≤ A) (hB : 0 ≤ B) (hL : 0 ≤ L) (hc : 0 < rate) :
    0 ≤ loopErrorConstantOne j A B L rate ∧ 0 ≤ loopErrorConstantTwo j A B rate := by
  unfold loopErrorConstantOne loopErrorConstantTwo
  exact ⟨by positivity,by positivity⟩

end SKGap

noncomputable section
open Set Finset
open scoped BigOperators
namespace SKGap

lemma continuous_no_exit {h : ℝ → ℝ} {δ ε : ℝ} (hδ : 0 < δ)
    (hε : ε < δ) (hh : ContinuousOn h (Icc 0 1)) (hzero : h 0 = 0)
    (hlocal : ∀ z ∈ Icc (0:ℝ) 1, |h z| ≤ δ → |h z| ≤ ε) :
    ∀ z ∈ Icc (0:ℝ) 1, |h z| ≤ ε := by
  intro z hz
  by_cases hs : |h z| ≤ δ
  · exact hlocal z hz hs
  · have hzz : 0 ≤ z := hz.1
    have habs : ContinuousOn (fun z => |h z|) (Icc 0 z) :=
      hh.abs.mono (Icc_subset_Icc le_rfl hz.2)
    have hδrange : δ ∈ Icc (|h 0|) (|h z|) := by
      rw [hzero,abs_zero]
      exact ⟨hδ.le,le_of_lt (lt_of_not_ge hs)⟩
    obtain ⟨t, ht, heq⟩ := intermediate_value_Icc hzz habs hδrange
    change |h t| = δ at heq
    have ht' : t ∈ Icc (0:ℝ) 1 := ⟨ht.1,ht.2.trans hz.2⟩
    have hb := hlocal t ht' (by rw [heq])
    rw [heq] at hb
    exact False.elim ((not_le_of_gt hε) hb)

section Loop
variable {ι : Type*} [Fintype ι]

lemma weighted_abs_sum_le {w v : ι → ℝ} {C : ℝ}
    (hw : ∀ i, 0 ≤ w i) (hv : ∀ i, |v i| ≤ C) :
    |∑ i, w i*v i| ≤ (∑ i, w i)*C := by
  calc
    _ ≤ ∑ i, |w i*v i| := Finset.abs_sum_le_sum_abs _ _
    _ = ∑ i, w i*|v i| := by simp_rw [abs_mul,abs_of_nonneg (hw _)]
    _ ≤ ∑ i, w i*C := Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (hv i) (hw i)
    _ = _ := (Finset.sum_mul _ _ _).symm

lemma loop_local_control {w a k : ι → ℝ} {j A M z h ε δ γ : ℝ}
    (hw : ∀ i, 0 ≤ w i) (hws : ∑ i, w i = 1)
    (ha : ∀ i, 0 ≤ a i) (haA : ∀ i, a i ≤ A) (hA : 0 ≤ A)
    (hj : 0 ≤ j) (hz : z ∈ Icc (0:ℝ) 1) (hM : ∀ i, |k i| ≤ M)
    (_hε : 0 ≤ ε) (hδ : 0 ≤ δ) (hγ : 0 < γ)
    (hh : h = ∑ i, w i*a i*(k i-1)) (hsmall : |h| ≤ δ)
    (hloop : ∀ i, |k i-1-z^2*j*a i*h*k i| ≤ ε)
    (hmargin : j*A^2*(1+j*A*M*δ+ε) ≤ 1-γ) :
    |h| ≤ A*ε/γ := by
  have hz2 : 0 ≤ z^2 := sq_nonneg z
  have hz2le : z^2 ≤ 1 := by nlinarith [hz.1,hz.2]
  have hki (i : ι) : |k i-1| ≤ j*A*M*δ+ε := by
    have hM0 : 0 ≤ M := (abs_nonneg (k i)).trans (hM i)
    have hmul : |z^2*j*a i*h*k i| ≤ j*A*δ*M := by
      simp only [abs_mul,abs_of_nonneg hz2,abs_of_nonneg hj,abs_of_nonneg (ha i)]
      calc
        _ ≤ 1*j*A*δ*M := by
          gcongr <;> first | exact ha i | exact hz2le | exact haA i | exact hsmall | exact hM i
        _ = _ := by ring
    have he := abs_add_le (k i-1-z^2*j*a i*h*k i) (z^2*j*a i*h*k i)
    have hid : k i-1-z^2*j*a i*h*k i+(z^2*j*a i*h*k i) = k i-1 := by ring
    rw [hid] at he
    nlinarith [hloop i]
  let c := ∑ i, w i*(z^2*j*(a i)^2*k i)
  have hc : |c| ≤ 1-γ := by
    have hki' (i : ι) : |k i| ≤ 1+j*A*M*δ+ε := by
      have hh' := abs_add_le (k i-1) 1
      simp only [sub_add_cancel,abs_one] at hh'
      linarith [hki i]
    have hc' : |c| ≤ j*A^2*(1+j*A*M*δ+ε) := by
      calc
        _ ≤ (∑ i, w i)*(j*A^2*(1+j*A*M*δ+ε)) := by
          apply weighted_abs_sum_le hw
          intro i
          simp only [abs_mul,abs_of_nonneg hz2,abs_of_nonneg hj,abs_of_nonneg (sq_nonneg (a i))]
          calc
            _ ≤ 1*j*A^2*(1+j*A*M*δ+ε) := by
              gcongr <;> first | exact ha i | exact hz2le | exact haA i | exact hki' i
            _ = _ := by ring
        _ = _ := by rw [hws,one_mul]
    exact hc'.trans hmargin
  have herr : |h-c*h| ≤ A*ε := by
    have heq : h-c*h = ∑ i, w i*(a i*(k i-1-z^2*j*a i*h*k i)) := by
      rw [hh]
      dsimp only [c]
      rw [Finset.sum_mul,← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro i _
      ring
    rw [heq]
    calc
      _ ≤ (∑ i, w i)*(A*ε) := by
        apply weighted_abs_sum_le hw
        intro i
        rw [abs_mul,abs_of_nonneg (ha i)]
        exact mul_le_mul (haA i) (hloop i) (abs_nonneg _) hA
      _ = _ := by rw [hws,one_mul]
  have hlast := abs_add_le (h-c*h) (c*h)
  have heqh : h-c*h+c*h = h := by ring
  rw [heqh,abs_mul] at hlast
  have hch := mul_le_mul_of_nonneg_right hc (abs_nonneg h)
  apply (le_div_iff₀ hγ).mpr
  nlinarith

lemma loop_global_control {w a : ι → ℝ} {k : ℝ → ι → ℝ} {j A M ε δ γ : ℝ}
    (hw : ∀ i, 0 ≤ w i) (hws : ∑ i, w i = 1)
    (ha : ∀ i, 0 ≤ a i) (haA : ∀ i, a i ≤ A) (hA : 0 ≤ A)
    (hj : 0 ≤ j) (hk : ∀ i, ContinuousOn (fun z => k z i) (Icc 0 1))
    (hk0 : ∀ i, k 0 i = 1) (hM : ∀ z ∈ Icc (0:ℝ) 1, ∀ i, |k z i| ≤ M)
    (hε : 0 ≤ ε) (hδ : 0 < δ) (hγ : 0 < γ)
    (hloop : ∀ z ∈ Icc (0:ℝ) 1, ∀ i,
      |k z i-1-z^2*j*a i*(∑ b, w b*a b*(k z b-1))*k z i| ≤ ε)
    (hmargin : j*A^2*(1+j*A*M*δ+ε) ≤ 1-γ) (hexit : A*ε/γ < δ) :
    ∀ z ∈ Icc (0:ℝ) 1,
      |∑ i, w i*a i*(k z i-1)| ≤ A*ε/γ ∧
      ∀ i, |k z i-1| ≤ j*A*M*(A*ε/γ)+ε := by
  let h : ℝ → ℝ := fun z => ∑ i, w i*a i*(k z i-1)
  have hh : ContinuousOn h (Icc 0 1) := by
    apply continuousOn_finsetSum
    intro i _
    exact continuousOn_const.mul ((hk i).sub continuousOn_const)
  have hh0 : h 0 = 0 := by simp [h,hk0]
  have hg : ∀ z ∈ Icc (0:ℝ) 1, |h z| ≤ A*ε/γ := by
    apply continuous_no_exit hδ hexit hh hh0
    intro z hz hs
    exact loop_local_control hw hws ha haA hA hj hz (hM z hz) hε hδ.le hγ rfl hs
      (hloop z hz) hmargin
  intro z hz
  refine ⟨hg z hz, ?_⟩
  intro i
  have hM0 : 0 ≤ M := (abs_nonneg (k z i)).trans (hM z hz i)
  have hs0 : 0 ≤ A*ε/γ := by positivity
  have hz2le : z^2 ≤ 1 := by nlinarith [hz.1,hz.2]
  have hm : |z^2*j*a i*h z*k z i| ≤ j*A*(A*ε/γ)*M := by
    simp only [abs_mul,abs_of_nonneg (sq_nonneg z),abs_of_nonneg hj,abs_of_nonneg (ha i)]
    calc
      _ ≤ 1*j*A*(A*ε/γ)*M := by
        gcongr <;> first | exact ha i | exact hz2le | exact haA i | exact hg z hz | exact hM z hz i
      _ = _ := by ring
  have hs := abs_add_le (k z i-1-z^2*j*a i*h z*k z i) (z^2*j*a i*h z*k z i)
  have he : k z i-1-z^2*j*a i*h z*k z i+(z^2*j*a i*h z*k z i) = k z i-1 := by ring
  rw [he] at hs
  have hl : |k z i-1-z^2*j*a i*h z*k z i| ≤ ε := hloop z hz i
  nlinarith

end Loop
end SKGap

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
-- module Solutions.OAIQ072_SK.SKGap_Brownian_PathExpectation
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
open scoped BigOperators Matrix.Norms.Frobenius NNReal ENNReal SchwartzMap
variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]

lemma pathExpected_continuous (f : 𝓢(ℝ,ℂ)) {R j A : ℝ} {a : ι → ℝ}
    (hR : 0 ≤ R) (hj : 0 ≤ j) (hA0 : 0 ≤ A)
    (ha : ∀ i, 0 ≤ a i) (hA : ∀ i, a i ≤ A) (i : ι) :
    ContinuousOn (fun z => pathExpected f R hR j a z i) (Icc 0 1) := by
  have hq := diagonal_mean_bounds hj ha hA
  apply continuousOn_expected_realTruncatedK f hR _ i _ (pathBound f R j A)
  · unfold pathDiagonal; fun_prop
  · unfold pathShift; fun_prop
  · intro z; exact diagonal_transpose _
  · intro z; exact diagonal_transpose _
  · intro z hz
    exact (path_constants_bound f hR hj hA0 hA hq.1 hq.2 hz).1

omit [Nonempty ι] in
lemma pathExpected_zero (f : 𝓢(ℝ,ℂ)) {R : ℝ} (hR : 0 ≤ R) (j : ℝ)
    (a : ι → ℝ) (i : ι) : pathExpected f R hR j a 0 i = 1 := by
  unfold pathExpected expectedCutoff
  have hd : pathDiagonal a 0 = 0 := by simp [pathDiagonal]
  simp only [hd,realTruncatedK_zero_diagonal,Matrix.one_apply_eq,integral_const,probReal_univ,one_smul]

lemma pathExpected_bound (f : 𝓢(ℝ,ℂ)) {R j A z : ℝ} {a : ι → ℝ}
    (hR : 0 ≤ R) (hj : 0 ≤ j) (hA0 : 0 ≤ A)
    (ha : ∀ i, 0 ≤ a i) (hA : ∀ i, a i ≤ A) (hz : z ∈ Icc (0:ℝ) 1) (i : ι) :
    |pathExpected f R hR j a z i| ≤ pathBound f R j A := by
  have hq := diagonal_mean_bounds hj ha hA
  have hb := (path_constants_bound f hR hj hA0 hA hq.1 hq.2 hz).1
  have hm := norm_integral_le_of_norm_le_const (μ := Measure.pi (fun _ : MatrixCoordinates ι => gaussianReal 0 1))
    (ae_of_all _ (fun g => show ‖realTruncatedK f R hR (pathDiagonal a z)
      (pathShift z ((j/(Fintype.card ι:ℝ))*∑ b, a b)) (goeMatrix (j/(Fintype.card ι:ℝ)) g) i i‖ ≤ pathBound f R j A from by
      rw [Real.norm_eq_abs]
      exact (matrix_entry_le_opNorm _ i i).trans
        ((realTruncatedK_opNorm f hR _ _ _ (diagonal_transpose _) (diagonal_transpose _)).trans hb)))
  simpa only [pathExpected,expectedCutoff,Real.norm_eq_abs,probReal_univ,mul_one] using hm

end SKGap
end
end

section
noncomputable section
namespace SKGap

lemma exists_bootstrap_constants {j A M : ℝ} (hj : 0 ≤ j) (hA : 0 ≤ A)
    (hM : 0 ≤ M) (hsub : j*A^2 < 1) :
    ∃ δ γ e : ℝ, 0 < δ ∧ 0 < γ ∧ 0 < e ∧
      ∀ ε, 0 ≤ ε → ε ≤ e →
        j*A^2*(1+j*A*M*δ+ε) ≤ 1-γ ∧ A*ε/γ < δ := by
  let g := 1-j*A^2
  let d := j*A^2*(j*A*M+1)
  let δ := g/(4*(d+1))
  let γ := g/2
  have hg : 0 < g := sub_pos.mpr hsub
  have hd : 0 ≤ d := by dsimp [d]; positivity
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hγ : 0 < γ := half_pos hg
  have hdδ : (d+1)*δ = g/4 := by dsimp [δ]; field_simp
  refine ⟨δ,γ,min δ (δ*γ/(2*(A+1))),hδ,hγ,lt_min hδ (by positivity),?_⟩
  intro ε hε he
  have heδ := he.trans (min_le_left _ _)
  have he' := (le_div_iff₀ (show (0:ℝ)<2*(A+1) by positivity)).mp
    (he.trans (min_le_right _ _))
  constructor
  · have hdδ' : d*δ ≤ g/4 := by nlinarith
    have hf : j*A^2*(1+j*A*M*δ+ε) ≤ j*A^2+d*δ := by
      dsimp only [d]
      nlinarith [mul_nonneg (mul_nonneg hj (sq_nonneg A)) (sub_nonneg.mpr heδ)]
    apply hf.trans
    dsimp only [γ,g] at *
    linarith
  · apply (div_lt_iff₀ hγ).mpr
    have hh : A*ε ≤ (A+1)*ε := by nlinarith
    have hp : 0 < δ*γ := mul_pos hδ hγ
    nlinarith
end SKGap

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
-- module Solutions.OAIQ072_SK.SKGap_Brownian_PathBiasCutoff
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

theorem actual_path_bias_of_cutoff {j A : ℝ} (hj : 0 < j) (hA : 0 < A)
    (hs : sqrt j*A < 1) (f : 𝓢(ℝ,ℂ))
    (hf : ∀ x∈Icc ((1-sqrt j*A)^2/4) (2+A*(2*sqrt j+1+j*A)),f x=(x:ℂ)⁻¹)
    (hR : 0 ≤ 2*sqrt j+1+1) :
    ∃ (C : ℝ) (N : ℕ),0<C ∧ 0<N ∧
      ∀ n,N≤n → ∀ a : Fin n→ℝ,(∀ i,0≤a i) → (∀ i,a i≤A) →
        ∀ z∈Icc (0:ℝ) 1,∀ i,
          |pathExpected f (2*sqrt j+1+1) hR j a z i-1|≤C/(n:ℝ) := by
  let R := 2*sqrt j+1+1
  let lo := (1-sqrt j*A)^2/4
  let hi := 2+A*(2*sqrt j+1+j*A)
  have hinterval := path_interval hj.le hA.le hs
  let B := pathBound f R j A
  let L := pathLip f R j A
  let rate := pathRate j A
  have hrate : 0 < rate := pathRate_pos hj hA hs
  have hBL := path_constants_nonneg f hR hj.le hA.le
  have hB : 0 ≤ B := hBL.1
  let C₁ := loopErrorConstantOne j A B L rate
  let C₂ := loopErrorConstantTwo j A B rate
  let C₀ := C₂+A*C₁
  have hCs := loopErrorConstants_nonneg j A B L rate hj.le hA.le hBL.1 hBL.2 hrate
  have hC₀ : 0 ≤ C₀ := add_nonneg hCs.2 (mul_nonneg hA.le hCs.1)
  have hsub : j*A^2 < 1 := by
    have hp := mul_nonneg (sqrt_nonneg j) hA.le
    have he : (sqrt j*A)^2=j*A^2 := by rw [mul_pow,sq_sqrt hj.le]
    nlinarith [mul_nonneg hp (sub_nonneg.mpr hs.le)]
  obtain ⟨δ,γ,e,hδ,hγ,he,hboot⟩ := exists_bootstrap_constants hj.le hA.le hBL.1 hsub
  have hev : ∀ᶠ n : ℕ in atTop, C₀/(n:ℝ) < e :=
    (tendsto_const_div_atTop_nhds_zero_nat C₀).eventually (gt_mem_nhds he)
  obtain ⟨N,hN⟩ := eventually_atTop.mp ((path_size_eventually hs).and hev)
  let C := (j*A*B*A/γ+1)*C₀+1
  have hC : 0 < C := by dsimp [C]; positivity
  refine ⟨C,N+1,hC,Nat.succ_pos _,?_⟩
  intro n hn a ha haA z hz i
  have hn0 : 0 < n := lt_of_lt_of_le (Nat.succ_pos N) hn
  let : Nonempty (Fin n) := Fin.pos_iff_nonempty.mp hn0
  have hnr : (0:ℝ) < n := Nat.cast_pos.mpr hn0
  have hsize := (hN n (Nat.le_of_succ_le hn)).1
  have hsmall := (hN n (Nat.le_of_succ_le hn)).2
  have hm := hboot (C₀/(n:ℝ)) (div_nonneg hC₀ hnr.le) hsmall.le
  have hw : ∀ _ : Fin n, 0 ≤ (1/(n:ℝ)) := fun _ => by positivity
  have hws : (∑ _ : Fin n, (1/(n:ℝ)))=1 := by simp [hn0.ne']
  have hb := loop_global_control hw hws ha haA hA.le hj.le
    (fun b => pathExpected_continuous f hR hj.le hA.le ha haA b)
    (fun b => pathExpected_zero f hR j a b)
    (fun u hu b => pathExpected_bound f hR hj.le hA.le ha haA hu b)
    (div_nonneg hC₀ hnr.le) hδ hγ
    (fun u hu b => by
      have hp := path_goodSet_exponential hj hA ha haA hs
        (by simpa only [Fintype.card_fin] using hsize) hu
      simpa only [Fintype.card_fin] using path_self_consistency f hinterval.1 hf hR
        hj.le hA.le hrate ha haA hu hp b)
    hm.1 hm.2 z hz
  have hh := hb.2 i
  apply hh.trans
  change j*A*B*(A*(C₀/(n:ℝ))/γ)+C₀/(n:ℝ) ≤ C/(n:ℝ)
  calc
    _ = ((j*A*B*A/γ+1)*C₀)/(n:ℝ) := by ring
    _ ≤ C/(n:ℝ) := by apply div_le_div_of_nonneg_right _ hnr.le; dsimp [C]; linarith
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

lemma realProject_sign {R : ℝ} (hR : 0 ≤ R) (s : ι → ℝ) (hs : ∀ i, s i^2=1)
    (M : Matrix ι ι ℝ) : realProject R hR (signConjugate s M) = signConjugate s (realProject R hR M) := by
  unfold realProject
  rw [← sign_conjugate_lift s hs M,ComplexMatrix.matrixProject_conjugate,realPart_sign_conjugate]

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
-- module Solutions.OAIQ072_SK.SKGap_Matrix_MatrixWordRegularity
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
-- module Solutions.OAIQ072_SK.SKGap_Matrix_Word
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
-- module Solutions.OAIQ072_SK.SKGap_Matrix_MarkedWordIBP
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

section
noncomputable section
namespace SKGap
open Matrix Real
open scoped BigOperators Matrix.Norms.Frobenius SchwartzMap

variable {ι : Type*}

variable [Fintype ι] [DecidableEq ι]

lemma actualWord_nil (f : 𝓢(ℝ,ℂ)) {R : ℝ} (hR : 0≤R) (j : ℝ) (a : ι→ℝ) (z : ℝ)
    (M : Matrix ι ι ℝ) : actualWord f R hR j a z [] M=1 := rfl
lemma actualWord_cons (f : 𝓢(ℝ,ℂ)) {R : ℝ} (hR : 0≤R) (j : ℝ) (a : ι→ℝ) (z : ℝ)
    (M : Matrix ι ι ℝ) (l : WordLetter ι) (F : List (WordLetter ι)) :
    actualWord f R hR j a z (l::F) M=l.eval f R hR j a z M*actualWord f R hR j a z F M := rfl

end SKGap
end
end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Localization_MarkedErrorRate
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
-- module Solutions.OAIQ072_SK.SKGap_Gaussian_MatrixWordMoments
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
-- module Solutions.OAIQ072_SK.SKGap_Matrix_WordPartnerContraction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
namespace SKGap
open scoped BigOperators
variable {ι : Type*}

lemma wordPartners_inverse_sides (a : ι→ℝ) (F : List (WordLetter ι)) (c : WordCut ι)
    (hc : c∈wordPartners a F) (hi : c.inversePartner=true) :
    1≤ inverseCount c.left ∧ 1≤ inverseCount c.right := by
  induction F generalizing c with
  | nil => simp [wordPartners] at hc
  | cons l F ih =>
    rw [wordPartners_cons,List.mem_append] at hc
    rcases hc with hc|hc
    · cases l with
      | diag d => simp at hc
      | noise => simp only [List.mem_singleton] at hc;subst c;contradiction
      | inverse =>
        simp only [List.mem_singleton] at hc
        subst c
        simp [inverseCount]
    · obtain ⟨d,hd,rfl⟩ := List.mem_map.mp hc
      have hh := ih d hd hi
      cases l <;> simp [WordCut.prepend,inverseCount] at * <;> tauto

lemma wordRecursionAt_one_inverse (a : ι→ℝ) (P Q : List (WordLetter ι))
    (hI : inverseCount (P++(.noise::Q))≤1)
    (t : WordRecursionTerm ι) (ht : t∈wordRecursionAt a P Q) :
    inverseCount t.outer≤1 ∧ inverseCount t.inner≤1 := by
  dsimp only [wordRecursionAt] at ht
  rw [List.mem_append] at ht
  simp only [inverseCount_append,inverseCount_noise] at hI
  rcases ht with ht|ht
  · obtain ⟨c,hc,rfl⟩ := List.mem_map.mp ht
    have hh := (wordPartners_counts a P c hc).2
    cases hi : c.inversePartner
    · simp [WordCut.asLeft,hi] at *;omega
    · have hs := wordPartners_inverse_sides a P c hc hi
      simp [WordCut.asLeft,hi] at *;omega
  · obtain ⟨c,hc,rfl⟩ := List.mem_map.mp ht
    have hh := (wordPartners_counts a Q c hc).2
    cases hi : c.inversePartner
    · simp [WordCut.asRight,hi] at *;omega
    · have hs := wordPartners_inverse_sides a Q c hc hi
      simp [WordCut.asRight,hi] at *;omega

lemma firstNoiseSplit_none (F : List (WordLetter ι)) : firstNoiseSplit F=none ↔ ordinaryCount F=0 := by
  induction F with
  | nil => simp [firstNoiseSplit,ordinaryCount]
  | cons l F ih => cases l <;> simp [firstNoiseSplit,ordinaryCount] at * <;> exact ih

lemma wordRecursionTerms_one_inverse (a : ι→ℝ) (F : List (WordLetter ι))
    (hI : inverseCount F≤1) (t : WordRecursionTerm ι) (ht : t∈wordRecursionTerms a F) :
    inverseCount t.outer≤1 ∧ inverseCount t.inner≤1 := by
  unfold wordRecursionTerms at ht
  cases hs : firstNoiseSplit F with
  | none => simp [hs] at ht
  | some pq =>
    rcases pq with ⟨P,Q⟩
    have he := firstNoiseSplit_some F P Q hs
    simp only [hs] at ht
    exact wordRecursionAt_one_inverse a P Q (by simpa only [he] using hI) t ht

end SKGap
end
end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Matrix_WordBaseBias
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

lemma actualWord_all_diagonal (f : 𝓢(ℝ,ℂ)) {R : ℝ} (hR : 0≤R) (j : ℝ)
    (a : ι→ℝ) (z : ℝ) (F : List (WordLetter ι)) (M : Matrix ι ι ℝ)
    (hO : ordinaryCount F=0) (hI : inverseCount F=0) :
    actualWord f R hR j a z F M=diagonal (wordDiagonal F) := by
  induction F with
  | nil =>
    change (1:Matrix ι ι ℝ)=Matrix.diagonal (fun _=>1)
    simp
  | cons l F ih =>
    cases l with
    | noise => simp [ordinaryCount] at hO
    | inverse => simp [inverseCount] at hI
    | diag d =>
      simp only [ordinaryCount,List.countP_cons] at hO
      simp only [inverseCount,List.countP_cons] at hI
      have hh := ih (by simpa [ordinaryCount] using hO) (by simpa [inverseCount] using hI)
      rw [actualWord_cons,hh]
      simp only [WordLetter.eval,Matrix.diagonal_mul_diagonal]
      rfl

lemma actualWord_no_noise_entry (f : 𝓢(ℝ,ℂ)) {R : ℝ} (hR : 0≤R) (j : ℝ)
    (a : ι→ℝ) (z : ℝ) (F : List (WordLetter ι)) (M : Matrix ι ι ℝ) (i : ι)
    (hO : ordinaryCount F=0) (hI : inverseCount F≤1) :
    actualWord f R hR j a z F M i i=wordDiagonal F i*
      (if inverseCount F=0 then 1 else pathK f R hR j a z M i i) := by
  induction F with
  | nil => simp [actualWord_nil,inverseCount]
  | cons l F ih =>
    cases l with
    | noise => simp [ordinaryCount] at hO
    | diag d =>
      have hOt : ordinaryCount F=0 := by simpa [ordinaryCount] using hO
      have hIt : inverseCount F≤1 := by simpa [inverseCount] using hI
      rw [actualWord_cons]
      simp only [WordLetter.eval,Matrix.diagonal_mul,ih hOt hIt,wordDiagonal_diag]
      have he : inverseCount (.diag d::F)=inverseCount F := by simp [inverseCount]
      rw [he]
      ring
    | inverse =>
      have hOt : ordinaryCount F=0 := by simpa [ordinaryCount] using hO
      have hIt : inverseCount F=0 := by simp [inverseCount] at hI ⊢;omega
      rw [actualWord_cons,actualWord_all_diagonal f hR j a z F M hOt hIt]
      simp only [WordLetter.eval,Matrix.mul_diagonal,wordDiagonal_inverse]
      have hh : inverseCount (.inverse::F)≠0 := by simp [inverseCount]
      rw [ite_eq_right hh,mul_comm]

omit [Fintype ι] [DecidableEq ι] in
lemma wordDiagonal_bound (D : ℝ) (hD : 1≤D) (F : List (WordLetter ι))
    (hF : ∀ l∈F,l.bounded D) (i : ι) : |wordDiagonal F i|≤D^F.length := by
  induction F with
  | nil => simp
  | cons l F ih =>
    have hFt : ∀ l∈F,l.bounded D := fun l hl=>hF l (List.mem_cons_of_mem _ hl)
    have hD0 : 0≤D := zero_le_one.trans hD
    cases l with
    | diag d =>
      rw [wordDiagonal_diag,abs_mul]
      simpa only [List.length_cons,pow_succ'] using mul_le_mul (hF (.diag d) List.mem_cons_self i)
        (ih hFt) (abs_nonneg _) hD0
    | noise =>
      simp only [wordDiagonal_noise,List.length_cons]
      exact (ih hFt).trans (pow_le_pow_right₀ hD (Nat.le_succ _))
    | inverse =>
      simp only [wordDiagonal_inverse,List.length_cons]
      exact (ih hFt).trans (pow_le_pow_right₀ hD (Nat.le_succ _))

theorem word_base_bias (f : 𝓢(ℝ,ℂ)) {R : ℝ} (hR : 0≤R) (j : ℝ)
    (a : ι→ℝ) (z : ℝ) (F : List (WordLetter ι)) (i : ι)
    (hO : ordinaryCount F=0) (hI : inverseCount F≤1) {D E : ℝ}
    (hD : 1≤D) (hF : ∀ l∈F,l.bounded D) (hE : 0≤E)
    (hb : |pathExpected f R hR j a z i-1|≤E) :
    |wordExpected f hR j a z F i-wordDiagonal F i|≤D^F.length*E := by
  have he (g : MatrixCoordinates ι→ℝ) := actualWord_no_noise_entry f hR j a z F
    (goeMatrix (j/(Fintype.card ι:ℝ)) g) i hO hI
  by_cases hIc : inverseCount F=0
  · have hh : wordExpected f hR j a z F i=wordDiagonal F i := by simp [wordExpected,he,hIc]
    rw [hh,sub_self,abs_zero]
    positivity
  · have hh : wordExpected f hR j a z F i=wordDiagonal F i*pathExpected f R hR j a z i := by
      simp only [wordExpected,he,ite_eq_right hIc,integral_const_mul,pathExpected,pathK,expectedCutoff]
    rw [hh,← mul_sub_one,abs_mul]
    exact mul_le_mul (wordDiagonal_bound D hD F hF i) hb (abs_nonneg _) (pow_nonneg (zero_le_one.trans hD) _)
end SKGap
end
end

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
-- module Solutions.OAIQ072_SK.SKGap_Matrix_WordLeading
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
-- module Solutions.OAIQ072_SK.SKGap_Matrix_WordLoop
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
namespace SKGap
variable {ι : Type*}

lemma wordPartners_lengths (a : ι→ℝ) (F : List (WordLetter ι)) (c : WordCut ι)
    (hc : c∈wordPartners a F) :
    c.left.length+c.right.length+(if c.inversePartner then 0 else 1)=
      F.length+(if c.inversePartner then 2 else 0) := by
  induction F generalizing c with
  | nil => simp [wordPartners] at hc
  | cons l F ih =>
    rw [wordPartners_cons,List.mem_append] at hc
    rcases hc with hc|hc
    · cases l with
      | diag d => simp at hc
      | noise => simp only [List.mem_singleton] at hc;subst c;simp
      | inverse => simp only [List.mem_singleton] at hc;subst c;simp;omega
    · obtain ⟨d,hd,rfl⟩ := List.mem_map.mp hc
      have hh := ih d hd
      simp only [WordCut.prepend,List.length_cons] at *
      by_cases hi : d.inversePartner=true <;> simp [hi] at hh ⊢ <;> omega

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

lemma wordPartners_card_bound (a : ι→ℝ) (F : List (WordLetter ι)) :
    (wordPartners a F).length≤F.length := by
  induction F with
  | nil => simp [wordPartners]
  | cons l F ih => cases l <;> simp [wordPartners] <;> omega

lemma wordRecursionAt_lengths (a : ι→ℝ) (P Q : List (WordLetter ι))
    (t : WordRecursionTerm ι) (ht : t∈wordRecursionAt a P Q) :
    t.outer.length≤(P++(.noise::Q)).length ∧ t.inner.length≤(P++(.noise::Q)).length := by
  dsimp only [wordRecursionAt] at ht
  rw [List.mem_append] at ht
  rcases ht with ht|ht
  · obtain ⟨c,hc,rfl⟩ := List.mem_map.mp ht
    have hh := wordPartners_lengths a P c hc
    cases hi : c.inversePartner
    · simp [WordCut.asLeft,hi] at *;omega
    · have hs := wordPartners_inverse_sides a P c hc hi
      have hL : inverseCount c.left ≤ c.left.length := List.countP_le_length
      have hR : inverseCount c.right ≤ c.right.length := List.countP_le_length
      simp [WordCut.asLeft,hi] at *;omega
  · obtain ⟨c,hc,rfl⟩ := List.mem_map.mp ht
    have hh := wordPartners_lengths a Q c hc
    cases hi : c.inversePartner
    · simp [WordCut.asRight,hi] at *;omega
    · have hs := wordPartners_inverse_sides a Q c hc hi
      have hL : inverseCount c.left ≤ c.left.length := List.countP_le_length
      have hR : inverseCount c.right ≤ c.right.length := List.countP_le_length
      simp [WordCut.asRight,hi] at *;omega

lemma wordRecursionAt_bounds {a : ι→ℝ} {D : ℝ} (ha : ∀ i,|a i|≤D)
    (P Q : List (WordLetter ι)) (hP : ∀ l∈P,l.bounded D) (hQ : ∀ l∈Q,l.bounded D)
    (t : WordRecursionTerm ι) (ht : t∈wordRecursionAt a P Q) :
    (∀ l∈t.outer,l.bounded D) ∧ (∀ l∈t.inner,l.bounded D) := by
  dsimp only [wordRecursionAt] at ht
  rw [List.mem_append] at ht
  rcases ht with ht|ht
  · obtain ⟨c,hc,rfl⟩ := List.mem_map.mp ht
    have hh := wordPartners_preserves_bound ha P hP c hc
    exact ⟨fun l hl=>(List.mem_append.mp hl).elim (hh.1 l) (hQ l),hh.2⟩
  · obtain ⟨c,hc,rfl⟩ := List.mem_map.mp ht
    have hh := wordPartners_preserves_bound ha Q hQ c hc
    exact ⟨fun l hl=>(List.mem_append.mp hl).elim (hP l) (hh.2 l),hh.1⟩

lemma wordRecursionTerms_lengths (a : ι→ℝ) (F : List (WordLetter ι))
    (t : WordRecursionTerm ι) (ht : t∈wordRecursionTerms a F) :
    t.outer.length≤F.length ∧ t.inner.length≤F.length := by
  unfold wordRecursionTerms at ht
  cases hs : firstNoiseSplit F with
  | none => simp [hs] at ht
  | some pq =>
    rcases pq with ⟨P,Q⟩
    have he := firstNoiseSplit_some F P Q hs
    simp only [hs] at ht
    simpa only [he] using wordRecursionAt_lengths a P Q t ht

lemma wordRecursionTerms_bounds {a : ι→ℝ} {D : ℝ} (ha : ∀ i,|a i|≤D)
    (F : List (WordLetter ι)) (hF : ∀ l∈F,l.bounded D)
    (t : WordRecursionTerm ι) (ht : t∈wordRecursionTerms a F) :
    (∀ l∈t.outer,l.bounded D) ∧ (∀ l∈t.inner,l.bounded D) := by
  unfold wordRecursionTerms at ht
  cases hs : firstNoiseSplit F with
  | none => simp [hs] at ht
  | some pq =>
    rcases pq with ⟨P,Q⟩
    have he := firstNoiseSplit_some F P Q hs
    simp only [hs] at ht
    have hP : ∀ l∈P,l.bounded D := fun l hl=>hF l (by rw [he];exact List.mem_append_left _ hl)
    have hQ : ∀ l∈Q,l.bounded D := fun l hl=>hF l (by rw [he];exact List.mem_append_right _ (List.mem_cons_of_mem _ hl))
    exact wordRecursionAt_bounds ha P Q hP hQ t ht

lemma wordRecursionTerms_card_bound (a : ι→ℝ) (F : List (WordLetter ι)) :
    (wordRecursionTerms a F).length≤F.length := by
  unfold wordRecursionTerms
  cases hs : firstNoiseSplit F with
  | none => simp
  | some pq =>
    rcases pq with ⟨P,Q⟩
    have he := firstNoiseSplit_some F P Q hs
    simp only [wordRecursionAt,List.length_append,List.length_map,he,List.length_cons]
    have h1 := wordPartners_card_bound a P
    have h2 := wordPartners_card_bound a Q
    omega
end SKGap
end
end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Matrix_WordLoopLeading
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
-- module Solutions.OAIQ072_SK.SKGap_Matrix_WordExpectedRecursion
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

theorem actualWord_expected_recursion {n : ℕ} (hn : 0<n) (f : 𝓢(ℝ,ℂ))
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

section
-- module Solutions.OAIQ072_SK.SKGap_Entropy_WordUniformCost
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
namespace SKGap
open Matrix Real Set
open scoped BigOperators SchwartzMap

lemma finite_cost_bound (g : ℕ→ℕ→ℕ→ℝ) (L : ℕ) :
    ∃ C : ℝ,0≤C ∧ ∀ u≤L,∀ v≤L,∀ q≤L,g u v q≤C := by
  let C := ∑ u∈Finset.range (L+1),∑ v∈Finset.range (L+1),∑ q∈Finset.range (L+1),|g u v q|
  refine ⟨C,by dsimp [C];positivity,?_⟩
  intro u hu v hv q hq
  calc
    g u v q ≤ |g u v q| := le_abs_self _
    _ ≤ ∑ r∈Finset.range (L+1),|g u v r| := Finset.single_le_sum (f := fun r => |g u v r|) (fun _ _=>abs_nonneg _) (Finset.mem_range.mpr (Nat.lt_succ_of_le hq))
    _ ≤ ∑ w∈Finset.range (L+1),∑ r∈Finset.range (L+1),|g u w r| := Finset.single_le_sum (f := fun w => ∑ r∈Finset.range (L+1),|g u w r|) (fun w _=>Finset.sum_nonneg (fun r _=>abs_nonneg (g u w r))) (Finset.mem_range.mpr (Nat.lt_succ_of_le hv))
    _ ≤ C := by
      dsimp only [C]
      exact Finset.single_le_sum (f := fun w => ∑ v∈Finset.range (L+1),∑ r∈Finset.range (L+1),|g w v r|) (fun w _=>Finset.sum_nonneg (fun v _=>Finset.sum_nonneg (fun r _=>abs_nonneg (g w v r)))) (Finset.mem_range.mpr (Nat.lt_succ_of_le hu))

lemma continuous_wordMarkedCost (B : NNReal) (j R A c : ℝ) (p q : ℕ) :
    Continuous (fun z=>wordMarkedCost B j R A c z p q) := by
  unfold wordMarkedCost markedRateConstant wordDifferentialBound
  fun_prop

lemma wordMarkedCost_uniform (B : NNReal) (j R A c : ℝ) (L : ℕ) :
    ∃ C : ℝ,0≤C ∧ ∀ z∈Icc (0:ℝ) 1,∀ p≤L,∀ q≤L,
      wordMarkedCost B j R A c z p q≤C := by
  let H : ℝ→ℝ := fun z=>∑ p∈Finset.range (L+1),∑ q∈Finset.range (L+1),|wordMarkedCost B j R A c z p q|
  have hH : Continuous H := by
    unfold H
    exact continuous_finsetSum _ (fun p _=>continuous_finsetSum _ (fun q _=>(continuous_wordMarkedCost B j R A c p q).abs))
  obtain ⟨C,hC⟩ := isCompact_Icc.exists_bound_of_continuousOn hH.continuousOn
  refine ⟨max 0 C,le_max_left _ _,?_⟩
  intro z hz p hp q hq
  have hb : wordMarkedCost B j R A c z p q≤H z := by
    calc
      _ ≤ |wordMarkedCost B j R A c z p q| := le_abs_self _
      _ ≤ ∑ r∈Finset.range (L+1),|wordMarkedCost B j R A c z p r| :=
        Finset.single_le_sum (f := fun r=>|wordMarkedCost B j R A c z p r|) (fun _ _=>abs_nonneg _) (Finset.mem_range.mpr (Nat.lt_succ_of_le hq))
      _ ≤ H z := by
        dsimp only [H]
        exact Finset.single_le_sum (f := fun w=>∑ r∈Finset.range (L+1),|wordMarkedCost B j R A c z w r|) (fun w _=>Finset.sum_nonneg (fun r _=>abs_nonneg (wordMarkedCost B j R A c z w r)))
          (Finset.mem_range.mpr (Nat.lt_succ_of_le hp))
  have hbH : |H z|≤C := hC z hz
  exact hb.trans ((le_abs_self _).trans (hbH.trans (le_max_right _ _)))

variable {ι : Type*}
lemma wordPartners_length_sides (a : ι→ℝ) (F : List (WordLetter ι)) (c : WordCut ι)
    (hc : c∈wordPartners a F) : c.left.length≤F.length+1 ∧ c.right.length≤F.length+1 := by
  have hh := wordPartners_lengths a F c hc
  cases hi : c.inversePartner
  · simp only [hi,Bool.false_eq_true,ite_false] at hh
    omega
  · have hs := wordPartners_inverse_sides a F c hc hi
    have hL : inverseCount c.left ≤ c.left.length := List.countP_le_length
    have hR : inverseCount c.right ≤ c.right.length := List.countP_le_length
    simp only [hi,ite_true] at hh
    omega

lemma wordRecursionAtCost_uniform {j B z C : ℝ} (hz : z∈Icc (0:ℝ) 1)
    (hC : 0≤C) (L : ℕ) (hc : ∀ u≤L,∀ v≤L,∀ q≤L,wordLeadingCost j B u v q≤C)
    (a : ι→ℝ) (P Q : List (WordLetter ι)) (hP : P.length+1+Q.length≤L) :
    wordRecursionAtCost j B z a P Q≤(L:ℝ)*C := by
  have hp : P.length≤L := by omega
  have hq : Q.length≤L := by omega
  have hz' (b : Bool) : |if b then z else 1|≤1 := by
    split
    · rw [abs_of_nonneg hz.1];exact hz.2
    · simp
  have hl (c : WordCut ι) (h : c∈wordPartners a P) :
      |if c.inversePartner then z else 1| *wordLeadingCost j B c.left.length c.right.length Q.length≤C := by
    have hb := wordPartners_length_sides a P c h
    have hcost := hc c.left.length (by omega) c.right.length (by omega) Q.length hq
    have hh := mul_le_mul_of_nonneg_left hcost (abs_nonneg (if c.inversePartner then z else 1))
    exact hh.trans ((mul_le_mul_of_nonneg_right (hz' _) hC).trans_eq (one_mul C))
  have hr (c : WordCut ι) (h : c∈wordPartners a Q) :
      |if c.inversePartner then z else 1| *wordLeadingCost j B P.length c.left.length c.right.length≤C := by
    have hb := wordPartners_length_sides a Q c h
    have hcost := hc P.length hp c.left.length (by omega) c.right.length (by omega)
    exact (mul_le_mul_of_nonneg_left hcost (abs_nonneg (if c.inversePartner then z else 1))).trans
      ((mul_le_mul_of_nonneg_right (hz' _) hC).trans_eq (one_mul C))
  have hb (X : List (WordCut ι)) (f : WordCut ι→ℝ) (hf : ∀ x∈X,f x≤C) :
      (X.map f).sum≤(X.length:ℝ)*C := by
    induction X with
    | nil => simp
    | cons x X ih =>
      simp only [List.map_cons,List.sum_cons,List.length_cons,Nat.cast_add,Nat.cast_one]
      exact (add_le_add (hf x List.mem_cons_self) (ih (fun x hx=>hf x (List.mem_cons_of_mem _ hx)))).trans_eq (by ring)
  have hsum := add_le_add (hb _ _ hl) (hb _ _ hr)
  have hlen : ((wordPartners a P).length:ℝ)+(wordPartners a Q).length≤L := by
    exact_mod_cast (show (wordPartners a P).length+(wordPartners a Q).length≤L by
      have hh1 := wordPartners_card_bound a P
      have hh2 := wordPartners_card_bound a Q
      omega)
  apply hsum.trans
  nlinarith [mul_nonneg hC (sub_nonneg.mpr hlen)]
end SKGap
end
end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Matrix_MatrixSeminorm
attribute [-instance] _root_.OAI.SKGap.ComplexMatrix.frobeniusInnerProduct
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
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

local instance instFactLeENNRealOfNat_solutions : Fact (1≤(4:ENNReal)) := ⟨by norm_num⟩

omit [DecidableEq ι] in
lemma diagonalSeminorm_sq (M : Matrix ι ι ℝ) : diagonalSeminorm M^2=∑ i,(M i i)^2 := by
  simp only [diagonalSeminorm,EuclideanSpace.norm_sq_eq,diagonalVector,Real.norm_eq_abs,sq_abs]

omit [DecidableEq ι] in
lemma diagonalSeminorm_add (M N : Matrix ι ι ℝ) :
    diagonalSeminorm (M+N)≤diagonalSeminorm M+diagonalSeminorm N := by
  simpa only [diagonalSeminorm,diagonalVector_add] using norm_add_le (diagonalVector M) (diagonalVector N)
lemma offDiagonalSeminorm_add (M N : Matrix ι ι ℝ) :
    offDiagonalSeminorm (M+N)≤offDiagonalSeminorm M+offDiagonalSeminorm N := by
  simpa only [offDiagonalSeminorm,offDiagonalVector_add] using norm_add_le (offDiagonalVector M) (offDiagonalVector N)
end SKGap
end
end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Gaussian_MatrixNormTail
attribute [-instance] _root_.OAI.SKGap.ComplexMatrix.frobeniusInnerProduct
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
namespace SKGap
open Matrix Real MeasureTheory ProbabilityTheory Set
open scoped BigOperators Matrix.Norms.Frobenius
variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ]

lemma matrixWordSeminorm_add (p : Bool) (M N : Matrix ι ι ℝ) :
    matrixWordSeminorm p (M+N)≤ matrixWordSeminorm p M+matrixWordSeminorm p N := by
  cases p
  · exact diagonalSeminorm_add M N
  · exact offDiagonalSeminorm_add M N
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

omit [Fintype ι] in
lemma signConjugate_diagonal (s : ι → ℝ) (hs : ∀ i, s i^2=1) (d : ι → ℝ) :
    signConjugate s (diagonal d)=diagonal d := by
  ext i k
  by_cases h : i=k
  · subst k
    simp only [signConjugate,diagonal_apply_eq]
    rw [← pow_two,hs,one_mul]
  · simp [signConjugate,diagonal_apply_ne _ h]

end SKGap
end
end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Stability_WordPredictionStability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
namespace SKGap
open Real Matrix Set
open scoped BigOperators
variable {ι : Type*} [Fintype ι] [Nonempty ι]

lemma wordAverage_abs_le (e : List (WordLetter ι)→ι→ℝ) (F : List (WordLetter ι))
    {B : ℝ} (hB : ∀ i,|e F i|≤B) : |wordAverage e F|≤B := by
  have hn : (0:ℝ)<Fintype.card ι := Nat.cast_pos.mpr Fintype.card_pos
  rw [wordAverage,abs_div,abs_of_pos hn]
  apply (div_le_iff₀ hn).mpr
  calc
    |∑ k,e F k| ≤ ∑ k,|e F k| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _ : ι,B := Finset.sum_le_sum (fun i _=>hB i)
    _ = _ := by simp [mul_comm]

lemma wordAverage_sub_abs_le (e p : List (WordLetter ι)→ι→ℝ) (F : List (WordLetter ι))
    {E : ℝ} (hE : ∀ i,|e F i-p F i|≤E) : |wordAverage e F-wordAverage p F|≤E := by
  have hh := wordAverage_abs_le (fun G i=>e G i-p G i) F hE
  simpa only [wordAverage,Finset.sum_sub_distrib,sub_div] using hh

omit [Fintype ι] [Nonempty ι] in
lemma abs_list_difference_le (C : List ι) (p q : ι→ℝ) {E : ℝ}
    (h : ∀ c∈C,|p c-q c|≤E) : |(C.map p).sum-(C.map q).sum|≤(C.length:ℝ)*E := by
  induction C with
  | nil => simp
  | cons c C ih =>
    have hh := ih (fun c hc=>h c (List.mem_cons_of_mem _ hc))
    simp only [List.map_cons,List.sum_cons,List.length_cons,Nat.cast_add,Nat.cast_one]
    calc
      |(p c+(C.map p).sum)-(q c+(C.map q).sum)|=
        |(p c-q c)+((C.map p).sum-(C.map q).sum)| := by congr 1;ring
      _ ≤ |p c-q c|+|(C.map p).sum-(C.map q).sum| := abs_add_le _ _
      _ ≤ E+(C.length:ℝ)*E := add_le_add (h c List.mem_cons_self) hh
      _ = _ := by ring

omit [Nonempty ι] in
lemma wordPrediction_recursion (j : ℝ) (a : ι→ℝ) (z : ℝ) (F : List (WordLetter ι)) (i : ι)
    (hO : ordinaryCount F≠0) :
    wordPrediction j a z F i=wordRecursionValue j a z (wordPrediction j a z) F i := by
  rw [wordPrediction,ite_eq_right hO]
  simp only [wordRecursionValue,wordAverage]
  apply congrArg List.sum
  exact List.attach_map_val (l:=wordRecursionTerms a F) (f:=fun (t : WordRecursionTerm ι)=>
    (if t.inversePartner then z else 1)*j*((∑ k,wordPrediction j a z t.inner k)/(Fintype.card ι:ℝ))*wordPrediction j a z t.outer i)

omit [Nonempty ι] in
lemma wordPrediction_base (j : ℝ) (a : ι→ℝ) (z : ℝ) (F : List (WordLetter ι)) (i : ι)
    (hO : ordinaryCount F=0) : wordPrediction j a z F i=wordDiagonal F i := by
  rw [wordPrediction,ite_eq_left hO]

omit [Fintype ι] [Nonempty ι] in
lemma scalar_product_prediction_error {u v p q B δ E : ℝ}
    (hB : 0≤B) (hδ : 0≤δ) (hE : δ≤E)
    (hu : |u|≤B) (hv : |v|≤B) (hup : |u-p|≤δ) (hvq : |v-q|≤δ) :
    |u*v-p*q|≤(2*B+E)*δ := by
  have he : u*v-p*q=u*(v-q)+(u-p)*q := by ring
  have hq : |q|≤B+δ := by
    calc
      |q|=|v-(v-q)| := by congr 1;ring
      _ ≤ |v|+|v-q| := abs_sub _ _
      _ ≤ B+δ := add_le_add hv hvq
  rw [he]
  calc
    |u*(v-q)+(u-p)*q| ≤ |u*(v-q)|+|(u-p)*q| := abs_add_le _ _
    _ = |u| *|v-q|+|u-p| *|q| := by rw [abs_mul,abs_mul]
    _ ≤ B*δ+δ*(B+δ) := add_le_add (mul_le_mul hu hvq (abs_nonneg _) hB)
      (mul_le_mul hup hq (abs_nonneg _) hδ)
    _ ≤ (2*B+E)*δ := by nlinarith [mul_nonneg hδ (sub_nonneg.mpr hE)]

theorem wordRecursionValue_stability {j z n B E : ℝ} (hj : 0≤j)
    (hz : z∈Icc (0:ℝ) 1) (hn : 1≤n) (hB : 0≤B) (hE : 0≤E)
    (a : ι→ℝ) (F : List (WordLetter ι)) (p q : List (WordLetter ι)→ι→ℝ)
    (hb : ∀ t∈wordRecursionTerms a F,∀ i,|p t.inner i|≤B ∧ |p t.outer i|≤B)
    (he : ∀ t∈wordRecursionTerms a F,∀ i,|p t.inner i-q t.inner i|≤E/n ∧
      |p t.outer i-q t.outer i|≤E/n) (i : ι) :
    |wordRecursionValue j a z p F i-wordRecursionValue j a z q F i|≤
      (F.length:ℝ)*j*(2*B+E)*E/n := by
  have hn0 : 0<n := zero_lt_one.trans_le hn
  have hd : 0≤E/n := div_nonneg hE hn0.le
  have hdn : E/n≤E := div_le_self hE hn
  have hterm (t : WordRecursionTerm ι) (ht : t∈wordRecursionTerms a F) :
      |(if t.inversePartner then z else 1)*j*wordAverage p t.inner*p t.outer i-
        (if t.inversePartner then z else 1)*j*wordAverage q t.inner*q t.outer i|≤
          j*(2*B+E)*E/n := by
    have hp := wordAverage_abs_le p t.inner (fun k=>(hb t ht k).1)
    have hep := wordAverage_sub_abs_le p q t.inner (fun k=>(he t ht k).1)
    have hh := scalar_product_prediction_error hB hd hdn hp (hb t ht i).2 hep (he t ht i).2
    have hcoef : |if t.inversePartner then z else 1|≤1 := by
      split
      · rw [abs_of_nonneg hz.1]; exact hz.2
      · simp
    have hcj : |(if t.inversePartner then z else 1)*j|≤j := by
      rw [abs_mul,abs_of_nonneg hj]
      exact (mul_le_mul_of_nonneg_right hcoef hj).trans_eq (one_mul _)
    calc
      _=|(if t.inversePartner then z else 1)*j| *
        |wordAverage p t.inner*p t.outer i-wordAverage q t.inner*q t.outer i| := by
          rw [← abs_mul]
          congr 1
          ring
      _ ≤ j*((2*B+E)*(E/n)) := mul_le_mul hcj hh (abs_nonneg _) hj
      _ = _ := by ring
  have hh := abs_list_difference_le (wordRecursionTerms a F) _ _ hterm
  have hcard : ((wordRecursionTerms a F).length:ℝ)≤F.length := by
    exact_mod_cast wordRecursionTerms_card_bound a F
  apply hh.trans
  have hm := mul_le_mul_of_nonneg_right hcard (show 0≤j*(2*B+E)*E/n by positivity)
  simpa only [mul_div_assoc,mul_assoc] using hm
end SKGap
end
end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Matrix_WordBiasInduction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
namespace SKGap
open Real Set
open scoped BigOperators

lemma wordBiasConstant_nonneg (L : ℕ) {j B C : ℝ} (hj : 0≤j) (hB : 0≤B) (hC : 0≤C) (k : ℕ) :
    0≤wordBiasConstant L j B C k := by
  induction k with
  | zero => exact hC
  | succ k ih => simp only [wordBiasConstant];positivity

lemma wordBiasConstant_ge (L : ℕ) {j B C : ℝ} (hj : 0≤j) (hB : 0≤B) (hC : 0≤C) (k : ℕ) :
    C≤wordBiasConstant L j B C k := by
  cases k with
  | zero => exact le_rfl
  | succ k =>
    have hh := wordBiasConstant_nonneg L hj hB hC k
    change C≤C+(L:ℝ)*j*(2*B+wordBiasConstant L j B C k)*wordBiasConstant L j B C k+wordBiasConstant L j B C k
    have hp : 0≤(L:ℝ)*j*(2*B+wordBiasConstant L j B C k)*wordBiasConstant L j B C k := by positivity
    linarith

theorem word_bias_induction {ι : Type*} [Fintype ι] [Nonempty ι]
    {j B C D n z : ℝ} (hj : 0≤j) (hB : 0≤B) (hC : 0≤C) (hn : 1≤n)
    (hz : z∈Icc (0:ℝ) 1) (a : ι → ℝ) (ha : ∀ i,|a i|≤D) (L : ℕ)
    (e : List (WordLetter ι) → ι → ℝ)
    (hb : ∀ F : List (WordLetter ι),F.length≤L → (∀ l∈F,l.bounded D) →
      inverseCount F≤1 → ∀ i,|e F i|≤B)
    (hbase : ∀ F : List (WordLetter ι),F.length≤L → (∀ l∈F,l.bounded D) →
      inverseCount F≤1 → ordinaryCount F=0 → ∀ i,|e F i-wordDiagonal F i|≤C/n)
    (hloop : ∀ F : List (WordLetter ι),F.length≤L → (∀ l∈F,l.bounded D) →
      inverseCount F≤1 → ordinaryCount F≠0 → ∀ i,
        |e F i-wordRecursionValue j a z e F i|≤C/n) :
    ∀ k,∀ F : List (WordLetter ι),F.length≤L → (∀ l∈F,l.bounded D) →
      inverseCount F≤1 → ordinaryCount F≤k → ∀ i,
        |e F i-wordPrediction j a z F i|≤wordBiasConstant L j B C k/n := by
  intro k
  induction k with
  | zero =>
    intro F hlen hF hI hO i
    have ho : ordinaryCount F=0 := Nat.eq_zero_of_le_zero hO
    rw [wordPrediction_base j a z F i ho]
    exact hbase F hlen hF hI ho i
  | succ k ih =>
    intro F hlen hF hI hO i
    have hn0 : 0<n := zero_lt_one.trans_le hn
    by_cases ho : ordinaryCount F=0
    · rw [wordPrediction_base j a z F i ho]
      exact (hbase F hlen hF hI ho i).trans
        (div_le_div_of_nonneg_right (wordBiasConstant_ge L hj hB hC (k+1)) hn0.le)
    have he := wordBiasConstant_nonneg L hj hB hC k
    have hsub (t : WordRecursionTerm ι) (ht : t∈wordRecursionTerms a F) :
        t.outer.length≤L ∧ t.inner.length≤L ∧
        (∀ l∈t.outer,l.bounded D) ∧ (∀ l∈t.inner,l.bounded D) ∧
        inverseCount t.outer≤1 ∧ inverseCount t.inner≤1 ∧
        ordinaryCount t.outer≤k ∧ ordinaryCount t.inner≤k := by
      have h1 := wordRecursionTerms_lengths a F t ht
      have h2 := wordRecursionTerms_bounds ha F hF t ht
      have h3 := wordRecursionTerms_one_inverse a F hI t ht
      have h4 := wordRecursionTerms_decreases a F t ht
      exact ⟨h1.1.trans hlen,h1.2.trans hlen,h2.1,h2.2,h3.1,h3.2,by omega,by omega⟩
    have hreg := wordRecursionValue_stability hj hz hn hB he a F e (wordPrediction j a z)
      (by intro t ht u;have hh:=hsub t ht;exact ⟨hb _ hh.2.1 hh.2.2.2.1 hh.2.2.2.2.2.1 u,hb _ hh.1 hh.2.2.1 hh.2.2.2.2.1 u⟩)
      (by intro t ht u;have hh:=hsub t ht;exact ⟨ih _ hh.2.1 hh.2.2.2.1 hh.2.2.2.2.2.1 hh.2.2.2.2.2.2.2 u,
        ih _ hh.1 hh.2.2.1 hh.2.2.2.2.1 hh.2.2.2.2.2.2.1 u⟩) i
    rw [wordPrediction_recursion j a z F i ho]
    apply (abs_sub_le (e F i) (wordRecursionValue j a z e F i)
      (wordRecursionValue j a z (wordPrediction j a z) F i)).trans
    apply (add_le_add (hloop F hlen hF hI ho i) hreg).trans
    have hl : (F.length:ℝ)≤L := by exact_mod_cast hlen
    have hmul := mul_le_mul_of_nonneg_right hl
      (show 0≤j*(2*B+wordBiasConstant L j B C k)*wordBiasConstant L j B C k by positivity)
    apply (div_le_div_of_nonneg_right (show C+(F.length:ℝ)*j*(2*B+wordBiasConstant L j B C k)*wordBiasConstant L j B C k≤
      wordBiasConstant L j B C (k+1) by
        simp only [wordBiasConstant]
        nlinarith only [hmul,he]) hn0.le).trans_eq'
    ring
end SKGap
end
end

section
noncomputable section
namespace SKGap
open Matrix Real MeasureTheory ProbabilityTheory Set Filter
open scoped BigOperators Matrix.Norms.Frobenius SchwartzMap Topology

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
lemma wordExpected_abs_bound [Nonempty ι] (f : 𝓢(ℝ,ℂ)) {R j A D z : ℝ}
    (hR : 0≤R) (hj : 0≤j) (hA : 0≤A) (hD : 0≤D) {a : ι→ℝ}
    (ha : ∀ i,0≤a i) (haA : ∀ i,a i≤A) (hz : z∈Icc (0:ℝ) 1)
    (F : List (WordLetter ι)) (hF : ∀ l∈F,l.bounded D) (i : ι) :
    |wordExpected f hR j a z F i|≤(actualWordBound f R j A D)^F.length := by
  have hh := norm_integral_le_of_norm_le_const (μ:=Measure.pi (fun _ : MatrixCoordinates ι=>gaussianReal 0 1))
    (f:=fun g=>actualWord f R hR j a z F (goeMatrix (j/(Fintype.card ι:ℝ)) g) i i)
    (C:=(actualWordBound f R j A D)^F.length) (Filter.Eventually.of_forall (fun g=>
      (matrix_entry_le_opNorm _ i i).trans ((actualWord_bounds f hR hj hA hD ha haA hz F hF).1 _)))
  simpa [wordExpected,Real.norm_eq_abs,Measure.real] using hh

lemma wordRecursionValue_split (f : 𝓢(ℝ,ℂ)) {R : ℝ} (hR : 0≤R) (j : ℝ)
    (a : ι→ℝ) (z : ℝ) (F P Q : List (WordLetter ι)) (i : ι)
    (hs : firstNoiseSplit F=some (P,Q)) :
    wordRecursionValue j a z (wordExpected f hR j a z) F i=
      wordRecursionAtExpected f hR j a z P Q i := by
  simp only [wordRecursionValue,wordRecursionTerms,hs]
  rfl

end SKGap
end
end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Matrix_WordTemplateSurjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
namespace SKGap
open Matrix Real MeasureTheory ProbabilityTheory
open scoped BigOperators SchwartzMap Matrix.Norms.Frobenius
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma WordLetter.sign (f : 𝓢(ℝ,ℂ)) {R : ℝ} (hR : 0≤R) (j : ℝ) (a : ι→ℝ) (z : ℝ)
    (s : ι→ℝ) (hs : ∀ i,s i^2=1) (M : Matrix ι ι ℝ) (l : WordLetter ι) :
    l.eval f R hR j a z (signConjugate s M)=signConjugate s (l.eval f R hR j a z M) := by
  cases l with
  | diag d => exact (signConjugate_diagonal s hs d).symm
  | noise => exact realProject_sign hR s hs M
  | inverse => exact pathK_sign f hR j a z s hs M

lemma actualWord_sign (f : 𝓢(ℝ,ℂ)) {R : ℝ} (hR : 0≤R) (j : ℝ) (a : ι→ℝ) (z : ℝ)
    (s : ι→ℝ) (hs : ∀ i,s i^2=1) (M : Matrix ι ι ℝ) (F : List (WordLetter ι)) :
    actualWord f R hR j a z F (signConjugate s M)=signConjugate s (actualWord f R hR j a z F M) := by
  induction F with
  | nil =>
    change (1:Matrix ι ι ℝ)=signConjugate s 1
    simpa only [diagonal_one] using (signConjugate_diagonal s hs (fun _=>1)).symm
  | cons l F ih =>
    change l.eval f R hR j a z (signConjugate s M)*actualWord f R hR j a z F (signConjugate s M)=
      signConjugate s (l.eval f R hR j a z M*actualWord f R hR j a z F M)
    rw [l.sign f hR j a z s hs M,ih,signConjugate_mul s hs]

theorem actualWord_offdiag_mean (f : 𝓢(ℝ,ℂ)) {R : ℝ} (hR : 0≤R) (j r : ℝ) (a : ι→ℝ) (z : ℝ)
    (F : List (WordLetter ι)) (i k : ι) (hik : i≠k) :
    (∫ g,actualWord f R hR j a z F (goeMatrix r g) i k
      ∂Measure.pi (fun _ : MatrixCoordinates ι=>gaussianReal 0 1))=0 :=
  goe_equivariant_offdiag r (actualWord f R hR j a z F)
    (fun s hs M=>actualWord_sign f hR j a z s hs M F) i k hik
end SKGap
end
end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Stability_WordMeanSeminorm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
namespace SKGap
open Matrix Real Set MeasureTheory ProbabilityTheory
open scoped BigOperators Matrix.Norms.Frobenius SchwartzMap
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
local instance instFactLeENNRealOfNat_solutions_1 : Fact (1≤(4:ENNReal)) := ⟨by norm_num⟩

lemma actualWord_mean_diagonal (f : 𝓢(ℝ,ℂ)) {R : ℝ} (hR : 0≤R) (j : ℝ)
    (a : ι→ℝ) (z : ℝ) (F : List (WordLetter ι)) :
    matrixEntryMean (fun x : EuclideanSpace ℝ (MatrixCoordinates ι)=>
      actualWord f R hR j a z F (goeMatrix (j/(Fintype.card ι:ℝ)) x))=
      Matrix.diagonal (wordExpected f hR j a z F) := by
  ext i k
  by_cases h : i=k
  · subst k
    simp only [matrixEntryMean,Matrix.diagonal_apply_eq,wordExpected]
  · rw [Matrix.diagonal_apply_ne _ h]
    exact actualWord_offdiag_mean f hR j _ a z F i k h

lemma offDiagonalSeminorm_diagonal (d : ι→ℝ) :
    offDiagonalSeminorm (Matrix.diagonal d)=0 := by
  have he : offDiagonalVector (Matrix.diagonal d)=0 := by
    ext p
    simp only [offDiagonalVector,WithLp.ofLp_toLp,PiLp.zero_apply]
    split_ifs with h
    · rfl
    · exact Matrix.diagonal_apply_ne _ h
  change ‖offDiagonalVector (Matrix.diagonal d)‖=0
  rw [he,norm_zero]

lemma diagonalSeminorm_diagonal_bound {n : ℕ} (hn : 1≤n) {C : ℝ} (hC : 0≤C)
    {d : Fin n→ℝ} (hd : ∀ i,|d i|≤C/(n:ℝ)) :
    diagonalSeminorm (Matrix.diagonal d)≤C := by
  have hnr : (1:ℝ)≤n := by exact_mod_cast hn
  have hn0 : (0:ℝ)<n := lt_of_lt_of_le zero_lt_one hnr
  apply le_of_pow_le_pow_left₀ (by decide : 2≠0) hC
  rw [diagonalSeminorm_sq]
  have hi (i : Fin n) : (Matrix.diagonal d i i)^2≤(C/(n:ℝ))^2 := by
    rw [Matrix.diagonal_apply_eq,←sq_abs]
    exact pow_le_pow_left₀ (abs_nonneg _) (hd i) 2
  calc
    _ ≤ ∑ i : Fin n,(C/(n:ℝ))^2 := Finset.sum_le_sum (fun i _=>hi i)
    _ = C^2/(n:ℝ) := by simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul];field_simp
    _ ≤ C^2 := (div_le_self (sq_nonneg _) hnr)

lemma actualWord_diagonal_prediction_decompose (f : 𝓢(ℝ,ℂ)) {R j : ℝ} (hR : 0≤R)
    (a : ι→ℝ) (z : ℝ) (F : List (WordLetter ι)) (g : MatrixCoordinates ι→ℝ) :
    actualWord f R hR j a z F (goeMatrix (j/(Fintype.card ι:ℝ)) g)-
      Matrix.diagonal (wordPrediction j a z F)=
      matrixCentered (fun x : EuclideanSpace ℝ (MatrixCoordinates ι)=>actualWord f R hR j a z F
        (goeMatrix (j/(Fintype.card ι:ℝ)) x)) (WithLp.toLp 2 g)+
      Matrix.diagonal (fun i=>wordExpected f hR j a z F i-wordPrediction j a z F i) := by
  rw [matrixCentered,actualWord_mean_diagonal]
  ext i k
  by_cases h : i=k
  · subst k
    simp only [Matrix.sub_apply,Matrix.add_apply,Matrix.diagonal_apply_eq]
    ring
  · simp only [Matrix.sub_apply,Matrix.add_apply,Matrix.diagonal_apply_ne _ h,sub_zero,add_zero]
end SKGap
end
end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Matrix_WordBiasCutoff
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
namespace SKGap
open Matrix Real MeasureTheory ProbabilityTheory Set Filter
open scoped BigOperators Matrix.Norms.Frobenius SchwartzMap Topology

theorem actual_word_uniform_bias_of_cutoff {j A D : ℝ} (hj : 0<j) (hA : 0<A)
    (hs : sqrt j*A<1) (hD : 1≤D) (hAD : A≤D) (L : ℕ) (f : 𝓢(ℝ,ℂ))
    (hf : ∀ x∈Icc ((1-sqrt j*A)^2/4) (2+A*(2*sqrt j+1+j*A)),f x=(x:ℂ)⁻¹)
    (hR : 0≤2*sqrt j+1+1) :
    ∃ (C : ℝ) (N : ℕ),0<C ∧ 0<N ∧
      ∀ n,N≤n → ∀ a : Fin n→ℝ,(∀ i,0≤a i) → (∀ i,a i≤A) →
        ∀ z∈Icc (0:ℝ) 1,∀ F : List (WordLetter (Fin n)),F.length≤L →
          (∀ l∈F,l.bounded D) → inverseCount F≤1 → ∀ i,
            |wordExpected f hR j a z F i-wordPrediction j a z F i|≤C/(n:ℝ) := by
  obtain ⟨C0,N0,hC0,hN0,hbase⟩ := actual_path_bias_of_cutoff hj hA hs f hf hR
  let R := 2*sqrt j+1+1
  have hD0 : 0≤D := zero_le_one.trans hD
  let B : NNReal := ⟨actualWordBound f R j A D,(actualWordBound_pos f hR hj.le hA.le hD0).le⟩
  have hB1 : (1:ℝ)≤B := by
    have hh := path_constants_nonneg f hR hj.le hA.le
    change 1≤1+R+D+pathBound f R j A+pathLip f R j A
    linarith
  obtain ⟨CM,hCM,hmarked⟩ := wordMarkedCost_uniform B j R A (pathRate j A) L
  obtain ⟨CL,hCL,hlead⟩ := finite_cost_bound (wordLeadingCost j B) L
  let Cbase := CM+(L:ℝ)*CL+D^L*C0+1
  have hCb : 0≤Cbase := by dsimp [Cbase];positivity
  obtain ⟨N1,hsize⟩ := eventually_atTop.mp (path_size_eventually hs)
  let C := wordBiasConstant L j ((B:ℝ)^L) Cbase L+1
  have hC : 0<C := by
    have hh := wordBiasConstant_nonneg L hj.le (pow_nonneg B.coe_nonneg L) hCb L
    dsimp [C]
    linarith
  refine ⟨C,max N0 (N1+1),hC,lt_of_lt_of_le hN0 (le_max_left _ _),?_⟩
  intro n hn a ha haA z hz F hlen hF hI i
  have hn0 : 0<n := lt_of_lt_of_le hN0 ((le_max_left _ _).trans hn)
  let : Nonempty (Fin n) := Fin.pos_iff_nonempty.mp hn0
  have hnr : (1:ℝ)≤n := by exact_mod_cast hn0
  have hnpos : (0:ℝ)<n := by exact_mod_cast hn0
  have haD : ∀ i,|a i|≤D := fun i=>(abs_of_nonneg (ha i)).trans_le ((haA i).trans hAD)
  have hbnd (G : List (WordLetter (Fin n))) (hGlen : G.length≤L)
      (hG : ∀ l∈G,l.bounded D) (_hGI : inverseCount G≤1) (u : Fin n) :
      |wordExpected f hR j a z G u|≤(B:ℝ)^L := by
    exact (wordExpected_abs_bound f hR hj.le hA.le hD0 ha haA hz G hG u).trans
      (pow_le_pow_right₀ hB1 hGlen)
  have hbas (G : List (WordLetter (Fin n))) (hGlen : G.length≤L)
      (hG : ∀ l∈G,l.bounded D) (hGI : inverseCount G≤1) (hGO : ordinaryCount G=0) (u : Fin n) :
      |wordExpected f hR j a z G u-wordDiagonal G u|≤Cbase/(n:ℝ) := by
    have hh := word_base_bias f hR j a z G u hGO hGI hD hG (div_nonneg hC0.le hnpos.le)
      (hbase n ((le_max_left _ _).trans hn) a ha haA z hz u)
    apply hh.trans
    have hpow := mul_le_mul_of_nonneg_right (pow_le_pow_right₀ hD hGlen) hC0.le
    have hc : D^G.length*C0≤Cbase := by
      dsimp [Cbase]
      nlinarith [mul_nonneg (Nat.cast_nonneg L) hCL]
    simpa only [mul_div_assoc] using div_le_div_of_nonneg_right hc hnpos.le
  have hloop (G : List (WordLetter (Fin n))) (hGlen : G.length≤L)
      (hG : ∀ l∈G,l.bounded D) (_hGI : inverseCount G≤1) (hGO : ordinaryCount G≠0) (u : Fin n) :
      |wordExpected f hR j a z G u-wordRecursionValue j a z (wordExpected f hR j a z) G u|≤Cbase/(n:ℝ) := by
    cases hsplit : firstNoiseSplit G with
    | none => exact False.elim (hGO ((firstNoiseSplit_none G).mp hsplit))
    | some pq =>
      rcases pq with ⟨P,Q⟩
      have he := firstNoiseSplit_some G P Q hsplit
      have hP : ∀ l∈P,l.bounded D := fun l hl=>hG l (by rw [he];exact List.mem_append_left _ hl)
      have hQ : ∀ l∈Q,l.bounded D := fun l hl=>hG l (by rw [he];exact List.mem_append_right _ (List.mem_cons_of_mem _ hl))
      have hlenPQ : P.length+1+Q.length≤L := by simpa [he,List.length_append,List.length_cons,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using hGlen
      have herr := hsize n (by have hh := (le_max_right N0 (N1+1)).trans hn;omega)
      have hh := actualWord_expected_recursion hn0 f hj hA hD0 hs hf herr ha haA haD hz P Q hP hQ u
      rw [wordRecursionValue_split f hR j a z G P Q u hsplit,he]
      apply hh.trans
      have hmc := hmarked z hz P.length (by omega) Q.length (by omega)
      have hlc := wordRecursionAtCost_uniform hz hCL L hlead a P Q hlenPQ
      have hcost : wordMarkedCost B j R A (pathRate j A) z P.length Q.length+
          wordRecursionAtCost j B z a P Q≤Cbase := by
        dsimp [Cbase]
        have hh0 : 0≤D^L*C0 := by positivity
        linarith
      exact div_le_div_of_nonneg_right hcost hnpos.le
  have hh := word_bias_induction hj.le (pow_nonneg B.coe_nonneg L) hCb hnr hz a haD L
    (wordExpected f hR j a z) hbnd hbas hloop L F hlen hF hI
    ((show ordinaryCount F≤F.length from List.countP_le_length).trans hlen) i
  apply hh.trans
  exact div_le_div_of_nonneg_right (by dsimp [C];linarith) hnpos.le
end SKGap
end
end

section
noncomputable section
namespace SKGap
open Matrix Real Set MeasureTheory ProbabilityTheory Filter
open scoped BigOperators Matrix.Norms.Frobenius SchwartzMap Topology

theorem actual_word_simultaneous_prediction_of_cutoff_oai {j A D : ℝ} (hj : 0<j) (hA : 0<A)
    (hs : sqrt j*A<1) (hD : 1≤D) (hAD : A≤D) (L : ℕ) (f : 𝓢(ℝ,ℂ))
    (hf : ∀ x∈Icc ((1-sqrt j*A)^2/4) (2+A*(2*sqrt j+1+j*A)),f x=(x:ℂ)⁻¹)
    (hR : 0≤2*sqrt j+1+1) :
    ∃ (C : ℝ) (N : ℕ),0<C ∧ 0<N ∧
      ∀ n,N≤n → ∀ p : Bool,
        (Measure.pi (fun _ : MatrixCoordinates (Fin n)=>gaussianReal 0 1))
        {g | ∃ (a : Fin n→ℝ) (F : List (WordLetter (Fin n))),
          (∀ i,a i∈Icc 0 A) ∧ F.length≤L ∧ (∀ l∈F,l.bounded D) ∧ inverseCount F≤1 ∧
          C< matrixWordSeminorm p
            (actualWord f (2*sqrt j+1+1) hR j a 1 F (goeMatrix (j/n) g)-Matrix.diagonal (wordPrediction j a 1 F))} ≤
          (wordPatternSet L L).card*ENNReal.ofReal (3*exp (-(n:ℝ))) := by
  obtain ⟨Cb,N,hCb,hN,hbias⟩ := actual_word_uniform_bias_of_cutoff hj hA hs hD hAD L f hf hR
  let R := 2*sqrt j+1+1
  obtain ⟨C0,hC0,hchain⟩ := all_actualWords_gaussian_chaining f hR hj.le hA (lt_of_lt_of_le zero_lt_one hD) L
  refine ⟨C0+Cb,N,by positivity,hN,?_⟩
  intro n hn p
  have hn0 : 1≤n := (Nat.succ_le_iff.mpr hN).trans hn
  apply (measure_mono ?_).trans (hchain n hn0 p)
  intro g hg
  obtain ⟨a,F,ha,hFL,hF,hFI,hg⟩ := hg
  refine ⟨a,F,ha,hFL,hF,?_⟩
  have hb : matrixWordSeminorm p (Matrix.diagonal (fun i=>wordExpected f hR j a 1 F i-wordPrediction j a 1 F i))≤Cb := by
    cases p with
    | false =>
      exact diagonalSeminorm_diagonal_bound hn0 hCb.le
        (hbias n hn a (fun i=>(ha i).1) (fun i=>(ha i).2) 1 ⟨zero_le_one,le_rfl⟩ F hFL hF hFI)
    | true =>
      change offDiagonalSeminorm (Matrix.diagonal _)≤Cb
      rw [offDiagonalSeminorm_diagonal]
      exact hCb.le
  have hdecomp := actualWord_diagonal_prediction_decompose (j:=j) f hR a 1 F g
  simp only [Fintype.card_fin] at hdecomp
  rw [hdecomp] at hg
  have hh := matrixWordSeminorm_add p
    (matrixCentered (fun x : EuclideanSpace ℝ (MatrixCoordinates (Fin n))=>
      actualWord f R hR j a 1 F (goeMatrix (j/n) x)) (WithLp.toLp 2 g))
    (Matrix.diagonal (fun i=>wordExpected f hR j a 1 F i-wordPrediction j a 1 F i))
  linarith
end SKGap
end
end

end OAI
end

theorem solution : type_of% @OAI.SKGap.actual_word_simultaneous_prediction_of_cutoff_oai := @OAI.SKGap.actual_word_simultaneous_prediction_of_cutoff_oai
