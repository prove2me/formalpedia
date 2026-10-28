-- Prove2me | solution 1 for OAI.SKGap.actual_path_bias
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T06:33:48.309853+00:00
-- url     : https://prove2.me/submissions/fd5357dd-56d2-454f-8284-b20cf8c35d24

import Mathlib
import Definitions.Def_OAIQ072A000
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

noncomputable section
open Set Filter MeasureTheory
open scoped Topology SchwartzMap FourierTransform ContDiff
namespace SKGap

lemma exists_schwartz_inverse {lo hi : ℝ} (hlo : 0 < lo) (hhi : lo ≤ hi) :
    ∃ f : 𝓢(ℝ, ℂ), (∀ x ∈ Icc lo hi, f x = (x : ℂ)⁻¹) ∧
      (∀ x, star (f x) = f x) := by
  let b : ContDiffBump hi := {
    rIn := hi-lo/2
    rOut := hi-lo/4
    rIn_pos := by linarith
    rIn_lt_rOut := by linarith }
  let g : ℝ → ℂ := fun x => (b x : ℂ) * (x : ℂ)⁻¹
  have hgcompact : HasCompactSupport g := by
    exact (b.hasCompactSupport.comp_left Complex.ofReal_zero).mul_right
  have hb0 : (0 : ℝ) ∉ tsupport (b : ℝ → ℝ) := by
    rw [b.tsupport_eq,Metric.mem_closedBall,Real.dist_eq,zero_sub,abs_neg,
      abs_of_pos (lt_of_lt_of_le hlo hhi)]
    change ¬ hi ≤ hi-lo/4
    linarith
  have hgsmooth : ContDiff ℝ ∞ g := by
    rw [contDiff_iff_contDiffAt]
    intro x
    by_cases hx : x = 0
    · subst x
      apply (contDiffAt_const (c := (0 : ℂ))).congr_of_eventuallyEq
      filter_upwards [notMem_tsupport_iff_eventuallyEq.mp hb0] with y hy
      simp [g,hy]
    · have hbr : ContDiffAt ℝ ∞ (fun y : ℝ => (b y : ℂ)) x := by
        exact Complex.ofRealCLM.contDiff.contDiffAt.comp x b.contDiff.contDiffAt
      have hxr : ContDiffAt ℝ ∞ (fun y : ℝ => (y : ℂ)) x :=
        Complex.ofRealCLM.contDiff.contDiffAt
      exact hbr.mul (hxr.inv (by exact_mod_cast hx))
  refine ⟨hgcompact.toSchwartzMap hgsmooth, ?_, ?_⟩
  · intro x hx
    have hxball : x ∈ Metric.closedBall hi b.rIn := by
      rw [Metric.mem_closedBall,Real.dist_eq,abs_of_nonpos (sub_nonpos.mpr hx.2)]
      change -(x-hi) ≤ hi-lo/2
      linarith [hx.1]
    simp [g,b.one_of_mem_closedBall hxball]
  · intro x
    simp [g]

end SKGap
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
-- module Solutions.OAIQ072_SK.SKGap_Brownian_PathBias
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

theorem actual_path_bias_oai {j A : ℝ} (hj : 0 < j) (hA : 0 < A) (hs : sqrt j*A < 1) :
    ∃ (f : 𝓢(ℝ,ℂ)) (R : ℝ) (hR : 0 ≤ R) (lo hi C : ℝ) (N : ℕ),
      R = 2*sqrt j+1+1 ∧ lo = (1-sqrt j*A)^2/4 ∧ hi = 2+A*(2*sqrt j+1+j*A) ∧
      0 < lo ∧ (∀ x ∈ Icc lo hi, f x=(x:ℂ)⁻¹) ∧ (∀ x, star (f x)=f x) ∧
      0 < C ∧ 0 < N ∧
      (∀ (n : ℕ), N ≤ n → ∀ (a : Fin n → ℝ), (∀ i, 0 ≤ a i) →
        (∀ i, a i ≤ A) → ∀ z ∈ Icc (0:ℝ) 1, ∀ i,
          |pathExpected f R hR j a z i-1| ≤ C/(n:ℝ)) := by
  let R := 2*sqrt j+1+1
  let lo := (1-sqrt j*A)^2/4
  let hi := 2+A*(2*sqrt j+1+j*A)
  have hR : 0 ≤ R := by dsimp [R]; positivity
  have hinterval := path_interval hj.le hA.le hs
  obtain ⟨f,hf,hfr⟩ := exists_schwartz_inverse hinterval.1 hinterval.2
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
  refine ⟨f,R,hR,lo,hi,C,N+1,rfl,rfl,rfl,hinterval.1,hf,hfr,hC,Nat.succ_pos _,?_⟩
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

theorem solution : type_of% @OAI.SKGap.actual_path_bias_oai := @OAI.SKGap.actual_path_bias_oai
