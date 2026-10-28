-- Prove2me | solution 1 for OAI.SKGap.actual_path_affine_tail_s2
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T10:53:41.120902+00:00
-- url     : https://prove2.me/submissions/11a7b878-dbc0-4ddd-b448-e3a6fb662918

import Mathlib
import Definitions.Def_OAIQ072A000
import Theorems.Thm_OAI_SKGap_actual_projected_path_equivalents

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
-- module Solutions.OAIQ074_CM.SKGap_Gaussian_GaussianCoordinateMemLp
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
-- module Solutions.OAIQ074_CM.SKGap_Localization_Conjugation
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
-- module Solutions.OAIQ074_CM.SKGap_Gaussian_GaussianSign
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
-- module Solutions.OAIQ074_CM.SKGap_Localization_Bilinear
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
-- module Solutions.OAIQ074_CM.SKGap_Localization_AffineBilinear
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
-- module Solutions.OAIQ074_CM.SKGap_Brownian_PathAgreement
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

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

theorem actual_path_affine_tail_s2_oai {j A D U W ε : ℝ}
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

theorem solution : type_of% @OAI.SKGap.actual_path_affine_tail_s2_oai := @OAI.SKGap.actual_path_affine_tail_s2_oai
