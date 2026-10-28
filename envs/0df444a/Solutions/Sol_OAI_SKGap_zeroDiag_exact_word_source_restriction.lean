-- Prove2me | solution 1 for OAI.SKGap.zeroDiag_exact_word_source_restriction
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T06:52:50.825162+00:00
-- url     : https://prove2.me/submissions/3d93fcb2-68f4-434d-8731-7a0b8419f6fb

import Mathlib
import Definitions.Def_OAIQ072A000
import Theorems.Thm_OAI_SKGap_actual_word_simultaneous_prediction_of_cutoff

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

lemma lowerRayleigh_ge [Nonempty ι] {M : Matrix ι ι ℂ} {c : ℝ}
    (hc : ∀ x ∈ unitSphere ι, c ≤ quadratic M x) : c ≤ lowerRayleigh M := by
  classical
  obtain ⟨i⟩ := ‹Nonempty ι›
  have hn : (quadratic M '' unitSphere ι).Nonempty := by
    refine ⟨quadratic M (EuclideanSpace.single i (1:ℂ)),?_⟩
    exact ⟨_,by simp [unitSphere],rfl⟩
  exact le_csInf hn (by rintro _ ⟨x,hx,rfl⟩; exact hc x hx)

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
local instance instPseudoMetrizableSpaceMatrixComplex_solutions_1_r8e999b_1 : TopologicalSpace.PseudoMetrizableSpace (Matrix ι ι ℂ) :=
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
-- module Solutions.OAIQ072_SK.SKGap_Brownian_PathBiasBase
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section

noncomputable section
open Real

noncomputable section
open Set Finset
open scoped BigOperators

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
-- module Solutions.OAIQ072_SK.SKGap_Localization_RealQuadratic
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
namespace SKGap.RealComplex
open SKGap.ComplexSpectral
open scoped BigOperators Matrix.Norms.Frobenius
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma quadratic_eq_inner (M : Matrix ι ι ℂ) (x : EuclideanSpace ℂ ι) :
    quadratic M x = (inner ℂ x (clin M x)).re := by
  rw [PiLp.inner_apply]
  change (∑ i, star (x i)*(∑ k, M i k*x k)).re =
    (∑ i, (∑ k, M i k*x k)*star (x i)).re
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  ring

lemma lowerRayleigh_ge_neg_norm [Nonempty ι] (M : Matrix ι ι ℂ) :
    -‖clin M‖ ≤ _root_.OAI.SKGap.ComplexSpectral.lowerRayleigh M := by
  apply lowerRayleigh_ge
  intro x hx
  have hn : ‖x‖ = 1 := by simpa only [unitSphere,Metric.mem_sphere,dist_zero_right] using hx
  rw [quadratic_eq_inner]
  have hh := (norm_inner_le_norm (𝕜 := ℂ) x (clin M x)).trans
    (mul_le_mul_of_nonneg_left ((clin M).le_opNorm x) (norm_nonneg x))
  rw [hn,mul_one,one_mul] at hh
  exact (neg_le_neg ((Complex.abs_re_le_norm _).trans hh)).trans (neg_abs_le _)

lemma lowerRayleigh_neg_lift_ge [Nonempty ι] (M : Matrix ι ι ℝ) :
    -opNorm M ≤ _root_.OAI.SKGap.ComplexSpectral.lowerRayleigh (-liftMatrix M) := by
  have h := lowerRayleigh_ge_neg_norm (-liftMatrix M)
  have he : clin (-liftMatrix M) = -clin (liftMatrix M) := by
    ext x i
    change (∑ k, -(liftMatrix M i k)*x k) = -(∑ k, liftMatrix M i k*x k)
    simp only [neg_mul,Finset.sum_neg_distrib]
  rw [he,norm_neg,operator_norm_lift] at h
  exact h

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

lemma opNorm_sub (M N : Matrix ι ι ℝ) : opNorm (M-N) ≤ opNorm M+opNorm N := by
  change ‖Matrix.toEuclideanCLM (n := ι) (𝕜 := ℝ) (M-N)‖ ≤ _
  rw [map_sub]
  exact norm_sub_le _ _

lemma real_sandwich_opNorm (D V : Matrix ι ι ℝ) :
    opNorm (D*V*D) ≤ opNorm D^2*opNorm V := by
  change ‖Matrix.toEuclideanCLM (n := ι) (𝕜 := ℝ) (D*V*D)‖ ≤
    ‖Matrix.toEuclideanCLM (n := ι) (𝕜 := ℝ) D‖^2*‖Matrix.toEuclideanCLM (n := ι) (𝕜 := ℝ) V‖
  simp only [map_mul]
  have h := (norm_mul_le (Matrix.toEuclideanCLM (n := ι) (𝕜 := ℝ) D*Matrix.toEuclideanCLM (n := ι) (𝕜 := ℝ) V)
    (Matrix.toEuclideanCLM (n := ι) (𝕜 := ℝ) D)).trans
    (mul_le_mul_of_nonneg_right (norm_mul_le (Matrix.toEuclideanCLM (n := ι) (𝕜 := ℝ) D) (Matrix.toEuclideanCLM (n := ι) (𝕜 := ℝ) V))
      (norm_nonneg _))
  exact h.trans_eq (by ring)

lemma real_sandwich_stability_norm (D C M : Matrix ι ι ℝ) :
    opNorm (1-D*(M-C)*D) ≤ 1+opNorm D^2*(opNorm M+opNorm C) := by
  calc
    _ ≤ opNorm (1 : Matrix ι ι ℝ)+opNorm (D*(M-C)*D) := opNorm_sub _ _
    _ ≤ 1+opNorm D^2*(opNorm M+opNorm C) :=
      add_le_add opNorm_one_le ((real_sandwich_opNorm _ _).trans
        (mul_le_mul_of_nonneg_left (opNorm_sub _ _) (sq_nonneg _)))

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
-- module Solutions.OAIQ072_SK.SKGap_Gaussian_GaussianProductUpperTailLipschitz
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
namespace SKGap
section ProductGaussianConcentration
variable {κ : Type*} [Fintype κ]

theorem gaussianProduct_upper_tail_lipschitz {f : (κ → ℝ) → ℝ} {L : ℝ≥0}
    (hf : LipschitzWith L (fun x : EuclideanSpace ℝ κ => f x.ofLp))
    (hL : 0 < L) {u : ℝ} (hu : 0 ≤ u) :
    (Measure.pi (fun _ : κ => gaussianReal 0 1)).real
      {x | u ≤ f x - ∫ y, f y ∂Measure.pi (fun _ : κ => gaussianReal 0 1)} ≤
      Real.exp (-2*u^2/(π^2*(L:ℝ)^2)) := by
  let e : (κ → ℝ) ≃ᵐ EuclideanSpace ℝ κ := MeasurableEquiv.toLp 2 _
  have hp : MeasurePreserving e (Measure.pi (fun _ : κ => gaussianReal 0 1))
      (stdGaussian (EuclideanSpace ℝ κ)) :=
    ⟨e.measurable, map_pi_eq_stdGaussian⟩
  have hi := hp.integral_comp' (fun x : EuclideanSpace ℝ κ => f x.ofLp)
  change (∫ x, f x ∂Measure.pi (fun _ : κ => gaussianReal 0 1)) = _ at hi
  have h := stdGaussian_upper_tail_lipschitz hf hL hu
  rw [← hi] at h
  have hs : MeasurableSet {x : EuclideanSpace ℝ κ |
      u ≤ f x.ofLp - ∫ y, f y ∂Measure.pi (fun _ : κ => gaussianReal 0 1)} :=
    measurableSet_le measurable_const (hf.continuous.measurable.sub_const _)
  have he := hp.measure_preimage hs.nullMeasurableSet
  have her := congrArg ENNReal.toReal he
  change (Measure.pi (fun _ : κ => gaussianReal 0 1)).real
      {x | u ≤ f x - ∫ y, f y ∂Measure.pi (fun _ : κ => gaussianReal 0 1)} = _ at her
  rw [her]
  exact h

end ProductGaussianConcentration
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

lemma stabilityMatrix_path_rep (a : ι → ℝ) (ha : ∀ i, 0 ≤ a i) {z : ℝ}
    (hz : 0 ≤ z) (q : ℝ) (M : Matrix ι ι ℝ) :
    stabilityMatrix a z q M = 1-pathDiagonal a z*(M-pathShift z q)*pathDiagonal a z := by
  ext i k
  simp only [stabilityMatrix,Matrix.sub_apply,pathDiagonal,pathShift,Matrix.diagonal_mul,
    Matrix.mul_diagonal,Matrix.one_apply,Matrix.diagonal_apply]
  by_cases hik : i=k
  · subst k
    simp only [↓reduceIte]
    have hz2 := sq_sqrt hz
    have ha2 := sq_sqrt (ha i)
    ring_nf
    rw [hz2,ha2]
    ring
  · simp only [hik,↓reduceIte,sub_zero]
    have hz2 := sq_sqrt hz
    nlinarith only [congrArg (fun x : ℝ => x*sqrt (a i)*M i k*sqrt (a k)) hz2]

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

lemma stabilityMatrix_opNorm {a : ι → ℝ} {A z q R : ℝ} {M : Matrix ι ι ℝ}
    (ha : ∀ i, 0 ≤ a i) (hA : ∀ i, a i ≤ A) (hA0 : 0 ≤ A)
    (hz : z ∈ Icc (0:ℝ) 1) (hq : 0 ≤ q) (hM : opNorm M ≤ R) :
    opNorm (stabilityMatrix a z q M) ≤ 1+A*(R+q) := by
  rw [stabilityMatrix_path_rep a ha hz.1 q M]
  have hD := pathDiagonal_opNorm hA0 hA hz
  have hd2 : opNorm (pathDiagonal a z)^2 ≤ A := by
    have h := pow_le_pow_left₀ (norm_nonneg _) hD 2
    rwa [sq_sqrt hA0] at h
  apply (real_sandwich_stability_norm _ _ _).trans
  apply add_le_add le_rfl
  exact mul_le_mul hd2 (add_le_add hM (pathShift_opNorm hz hq))
    (add_nonneg (norm_nonneg _) (norm_nonneg _)) hA0

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
open Matrix MeasureTheory ProbabilityTheory Real Set Filter
open RealComplex
open scoped BigOperators Matrix.Norms.Frobenius NNReal ENNReal SchwartzMap Topology

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

end SKGap
end
end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Gaussian_GaussianRegression
attribute [-instance] _root_.OAI.SKGap.ComplexMatrix.frobeniusInnerProduct
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
namespace SKGap
open MeasureTheory ProbabilityTheory Matrix
open scoped BigOperators ENNReal

lemma coordinate_hasLaw {κ : Type*} [Fintype κ] (i : κ) :
    HasLaw (fun g : κ → ℝ => g i) (gaussianReal 0 1) (gaussianCoordinates κ) :=
  ⟨(measurable_pi_apply i).aemeasurable,
    (measurePreserving_eval (fun _ : κ => gaussianReal 0 1) i).map_eq⟩

lemma linear_gaussian_mean {κ : Type*} [Fintype κ] (a : κ → ℝ) :
    (∫ g, ∑ i, a i*g i ∂gaussianCoordinates κ) = 0 := by
  rw [integral_finsetSum _ (fun i _ => (coordinate_hasLaw i).hasGaussianLaw.integrable.const_mul _)]
  simp [integral_const_mul,(coordinate_hasLaw _).integral_eq]

end SKGap
end
end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Gaussian_GOEGaussian
attribute [-instance] _root_.OAI.SKGap.ComplexMatrix.frobeniusInnerProduct
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
namespace SKGap
open MeasureTheory ProbabilityTheory Matrix Real
open scoped BigOperators ENNReal

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma goeEntryCoeff_sample (r : ℝ) (g : MatrixCoordinates ι → ℝ) (i k : ι) :
    (goeEntryCoeff r*ᵥg) (i,k) = goeMatrix r g i k := by
  simp only [mulVec,dotProduct,goeEntryCoeff,mul_assoc,add_mul]
  rw [← Finset.mul_sum,Finset.sum_add_distrib]
  simp [goeMatrix]

lemma goe_mean_zero (r : ℝ) (i k : ι) :
    (∫ g, goeMatrix r g i k ∂gaussianCoordinates (MatrixCoordinates ι))=0 := by
  simpa only [← goeEntryCoeff_sample,mulVec,dotProduct] using linear_gaussian_mean (goeEntryCoeff (ι := ι) r (i,k))

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

lemma offDiagonalSeminorm_fourth (M : Matrix ι ι ℝ) :
    offDiagonalSeminorm M^4=∑ p : ι×ι,if p.1=p.2 then 0 else (M p.1 p.2)^4 := by
  rw [offDiagonalSeminorm,PiLp.norm_eq_of_nat (p:=4) 4 (by norm_num)]
  rw [←Real.rpow_natCast,←Real.rpow_mul (Finset.sum_nonneg (fun _ _=>pow_nonneg (norm_nonneg _) _))]
  norm_num only [Nat.cast_ofNat,one_div,mul_inv_cancel₀ (by norm_num : (4:ℝ)≠0),Real.rpow_one]
  apply Finset.sum_congr rfl
  intro p _
  simp only [offDiagonalVector,WithLp.ofLp_toLp]
  split_ifs
  · simp
  · rw [Real.norm_eq_abs]
    calc
      |M p.1 p.2|^4=(|M p.1 p.2|^2)^2 := by ring
      _ = ((M p.1 p.2)^2)^2 := by rw [sq_abs]
      _ = (M p.1 p.2)^4 := by ring

lemma diagonalSeminorm_le (M : Matrix ι ι ℝ) : diagonalSeminorm M≤‖M‖ := by
  apply le_of_pow_le_pow_left₀ (by decide : 2≠0) (norm_nonneg _)
  rw [diagonalSeminorm_sq,frobenius_sq]
  exact Finset.sum_le_sum (fun i _=>Finset.single_le_sum (fun k _=>sq_nonneg (M i k)) (Finset.mem_univ i))

lemma offDiagonalSeminorm_le (M : Matrix ι ι ℝ) : offDiagonalSeminorm M≤‖M‖ := by
  let a : ι×ι→ℝ := fun p=>if p.1=p.2 then 0 else (M p.1 p.2)^2
  have ha : ∀ p,0≤a p := by intro p;dsimp [a];split_ifs <;> positivity
  have hs : (∑ p,a p)≤‖M‖^2 := by
    rw [frobenius_sq]
    rw [show (∑ i,∑ k,(M i k)^2) = ∑ p : ι×ι,(M p.1 p.2)^2 from (Fintype.sum_prod_type fun p : ι×ι=>(M p.1 p.2)^2).symm]
    apply Finset.sum_le_sum
    intro p _
    dsimp [a]
    split_ifs
    · exact sq_nonneg _
    · exact le_rfl
  apply le_of_pow_le_pow_left₀ (by decide : 4≠0) (norm_nonneg _)
  rw [offDiagonalSeminorm_fourth]
  calc
    _ = ∑ p,a p^2 := by
      apply Finset.sum_congr rfl
      intro p _
      dsimp [a]
      split_ifs <;> ring
    _ ≤ (∑ p,a p)^2 := Finset.sum_sq_le_sq_sum_of_nonneg (fun p _=>ha p)
    _ ≤ (‖M‖^2)^2 := pow_le_pow_left₀ (Finset.sum_nonneg (fun p _=>ha p)) hs 2
    _ = ‖M‖^4 := by ring

lemma diagonalSeminorm_lipschitz : LipschitzWith 1 (diagonalSeminorm (ι:=ι)) := by
  apply LipschitzWith.of_dist_le_mul
  intro M N
  simpa only [NNReal.coe_one,one_mul,dist_eq_norm,Real.norm_eq_abs,diagonalSeminorm,←diagonalVector_sub] using!
    (abs_norm_sub_norm_le (diagonalVector M) (diagonalVector N)).trans (diagonalSeminorm_le (M-N))
lemma offDiagonalSeminorm_lipschitz : LipschitzWith 1 (offDiagonalSeminorm (ι:=ι)) := by
  apply LipschitzWith.of_dist_le_mul
  intro M N
  have hh : ‖offDiagonalVector M-offDiagonalVector N‖≤‖M-N‖ := by
    simpa only [←offDiagonalVector_sub,offDiagonalSeminorm] using! offDiagonalSeminorm_le (M-N)
  simpa only [NNReal.coe_one,one_mul,dist_eq_norm,Real.norm_eq_abs,offDiagonalSeminorm] using!
    (abs_norm_sub_norm_le (offDiagonalVector M) (offDiagonalVector N)).trans hh
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
-- module Solutions.OAIQ072_SK.SKGap_Gaussian_GaussianProductPower
attribute [-instance] _root_.OAI.SKGap.ComplexMatrix.frobeniusInnerProduct
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
namespace SKGap
open Real MeasureTheory ProbabilityTheory
open scoped BigOperators
variable {κ : Type*} [Fintype κ]

lemma gaussianProduct_integrable_exp_lipschitz {F : EuclideanSpace ℝ κ→ℝ}
    {L : NNReal} (hF : LipschitzWith L F) (r : ℝ) :
    Integrable (fun g : κ→ℝ=>exp (r*F (WithLp.toLp 2 g))) (Measure.pi (fun _=>gaussianReal 0 1)) := by
  have hi := gaussian_integrable_exp_lipschitz (μ:=stdGaussian (EuclideanSpace ℝ κ)) hF r
  rw [←map_pi_eq_stdGaussian] at hi
  exact hi.comp_measurable (by fun_prop)

lemma gaussianProduct_integrable_abs_pow_lipschitz {F : EuclideanSpace ℝ κ→ℝ}
    {L : NNReal} (hF : LipschitzWith L F) (k : ℕ) :
    Integrable (fun g : κ→ℝ=>|F (WithLp.toLp 2 g)|^k) (Measure.pi (fun _=>gaussianReal 0 1)) := by
  let μ := Measure.pi (fun _ : κ=>gaussianReal 0 1)
  have h1 := gaussianProduct_integrable_exp_lipschitz hF 1
  have h2 := gaussianProduct_integrable_exp_lipschitz hF (-1)
  have hh := (h1.add h2).const_mul (k.factorial:ℝ)
  apply hh.mono'
  · exact ((hF.continuous.comp (by fun_prop : Continuous (WithLp.toLp 2 : (κ→ℝ)→EuclideanSpace ℝ κ))).abs.pow k).aestronglyMeasurable
  · filter_upwards [] with g
    simpa only [Real.norm_eq_abs,abs_pow,abs_abs,one_pow,div_one,Pi.add_apply] using
      pow_le_exponential_pair (F (WithLp.toLp 2 g)) (by norm_num : (0:ℝ)<1) k

lemma gaussianProduct_integrable_pow_lipschitz {F : EuclideanSpace ℝ κ→ℝ}
    {L : NNReal} (hF : LipschitzWith L F) (k : ℕ) :
    Integrable (fun g : κ→ℝ=>F (WithLp.toLp 2 g)^k) (Measure.pi (fun _=>gaussianReal 0 1)) := by
  apply (gaussianProduct_integrable_abs_pow_lipschitz hF k).mono'
  · exact ((hF.continuous.comp (by fun_prop : Continuous (WithLp.toLp 2 : (κ→ℝ)→EuclideanSpace ℝ κ))).pow k).aestronglyMeasurable
  · filter_upwards [] with g
    simp only [Real.norm_eq_abs,abs_pow,le_refl]
end SKGap
end
end

section
noncomputable section
namespace SKGap
open Real Matrix MeasureTheory ProbabilityTheory Set
open scoped BigOperators Matrix.Norms.Frobenius
variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ]

lemma matrixCentered_lipschitz {F : EuclideanSpace ℝ κ→Matrix ι ι ℝ}
    {L : NNReal} (hF : LipschitzWith L F) : LipschitzWith L (matrixCentered F) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  simpa only [matrixCentered,dist_sub_right] using hF.dist_le_mul x y

lemma matrixEntry_lip {F : EuclideanSpace ℝ κ→Matrix ι ι ℝ}
    {L : NNReal} (hF : LipschitzWith L F) (i k : ι) : LipschitzWith L (fun x=>F x i k) := by
  simpa only [one_mul,Function.comp_def] using (matrixEntry_lipschitz i k).comp hF

lemma diagonalCentered_lip {F : EuclideanSpace ℝ κ→Matrix ι ι ℝ}
    {L : NNReal} (hF : LipschitzWith L F) : LipschitzWith L (fun x=>diagonalSeminorm (matrixCentered F x)) := by
  simpa only [one_mul,Function.comp_def] using diagonalSeminorm_lipschitz.comp (matrixCentered_lipschitz hF)
lemma offDiagonalCentered_lip {F : EuclideanSpace ℝ κ→Matrix ι ι ℝ}
    {L : NNReal} (hF : LipschitzWith L F) : LipschitzWith L (fun x=>offDiagonalSeminorm (matrixCentered F x)) := by
  simpa only [one_mul,Function.comp_def] using offDiagonalSeminorm_lipschitz.comp (matrixCentered_lipschitz hF)

lemma matrixCentered_even_moment {F : EuclideanSpace ℝ κ→Matrix ι ι ℝ}
    {L : NNReal} (hF : LipschitzWith L F) (hL : 0<L) (i b : ι) (k : ℕ) :
    (∫ g : κ→ℝ,(matrixCentered F (WithLp.toLp 2 g) i b)^(2*k) ∂Measure.pi (fun _=>gaussianReal 0 1))≤
      (2*((2*k).factorial:ℝ)*exp (π^2/8))*(L:ℝ)^(2*k) := by
  have hh := gaussianProduct_abs_centered_moment (matrixEntry_lip hF i b) hL (2*k)
  simpa only [matrixCentered,matrixEntryMean,Matrix.sub_apply,pow_mul,sq_abs] using hh

lemma diagonalCentered_second_moment {F : EuclideanSpace ℝ κ→Matrix ι ι ℝ}
    {L : NNReal} (hF : LipschitzWith L F) (hL : 0<L) :
    (∫ g : κ→ℝ,diagonalSeminorm (matrixCentered F (WithLp.toLp 2 g))^2 ∂Measure.pi (fun _=>gaussianReal 0 1))≤
      (Fintype.card ι:ℝ)*(4*exp (π^2/8))*(L:ℝ)^2 := by
  simp_rw [diagonalSeminorm_sq]
  rw [integral_finsetSum _ (fun i _=>gaussianProduct_integrable_pow_lipschitz (matrixEntry_lip (matrixCentered_lipschitz hF) i i) 2)]
  apply (Finset.sum_le_sum (fun i _=>matrixCentered_even_moment hF hL i i 1)).trans_eq
  norm_num [Finset.sum_const,mul_assoc]

lemma offDiagonalCentered_fourth_moment {F : EuclideanSpace ℝ κ→Matrix ι ι ℝ}
    {L : NNReal} (hF : LipschitzWith L F) (hL : 0<L) :
    (∫ g : κ→ℝ,offDiagonalSeminorm (matrixCentered F (WithLp.toLp 2 g))^4 ∂Measure.pi (fun _=>gaussianReal 0 1))≤
      (Fintype.card ι:ℝ)^2*(48*exp (π^2/8))*(L:ℝ)^4 := by
  simp_rw [offDiagonalSeminorm_fourth]
  have hi (p : ι×ι) : Integrable (fun g : κ→ℝ=>if p.1=p.2 then 0 else matrixCentered F (WithLp.toLp 2 g) p.1 p.2^4)
      (Measure.pi (fun _=>gaussianReal 0 1)) := by
    split_ifs
    · exact integrable_const _
    · exact gaussianProduct_integrable_pow_lipschitz (matrixEntry_lip (matrixCentered_lipschitz hF) p.1 p.2) 4
  rw [integral_finsetSum _ (fun p _=>hi p)]
  have hb (p : ι×ι) : (∫ g : κ→ℝ,(if p.1=p.2 then 0 else matrixCentered F (WithLp.toLp 2 g) p.1 p.2^4)
      ∂Measure.pi (fun _=>gaussianReal 0 1)) ≤ (48*exp (π^2/8))*(L:ℝ)^4 := by
    split_ifs
    · simp only [integral_zero];positivity
    · have hh := matrixCentered_even_moment hF hL p.1 p.2 2
      norm_num at hh
      exact hh
  apply (Finset.sum_le_sum (fun p _=>hb p)).trans_eq
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_prod,nsmul_eq_mul,Nat.cast_mul]
  ring

lemma gaussianProduct_jensen_pow {F : EuclideanSpace ℝ κ→ℝ} {L : NNReal}
    (hF : LipschitzWith L F) (hpos : ∀ x,0≤F x) (k : ℕ) :
    (∫ g : κ→ℝ,F (WithLp.toLp 2 g) ∂Measure.pi (fun _=>gaussianReal 0 1))^k≤
      ∫ g : κ→ℝ,F (WithLp.toLp 2 g)^k ∂Measure.pi (fun _=>gaussianReal 0 1) := by
  exact (convexOn_pow (𝕜:=ℝ) k).map_integral_le (by fun_prop) isClosed_Ici
    (ae_of_all _ (fun g=>hpos (WithLp.toLp 2 g))) (gaussianProduct_integrable_lipschitz hF)
    (gaussianProduct_integrable_pow_lipschitz hF k)

omit [Fintype ι] [DecidableEq ι] [Fintype κ] in
lemma matrixNormConstant_bounds : 1≤ matrixNormConstant ∧
    4*exp (π^2/8)≤ matrixNormConstant^2 ∧ 48*exp (π^2/8)≤ matrixNormConstant^4 := by
  have hE := (exp_pos (π^2/8)).le
  have hC : 1≤ matrixNormConstant := by unfold matrixNormConstant;linarith
  have hC2 : matrixNormConstant≤ matrixNormConstant^2 := by
    simpa only [pow_one] using pow_le_pow_right₀ hC (by decide : 1≤2)
  have hC4 : matrixNormConstant≤ matrixNormConstant^4 := by
    simpa only [pow_one] using pow_le_pow_right₀ hC (by decide : 1≤4)
  refine ⟨hC,?_,?_⟩ <;> unfold matrixNormConstant at * <;> linarith

lemma gaussianProduct_centered_matrix_norms {F : EuclideanSpace ℝ κ→Matrix ι ι ℝ}
    {L : NNReal} (hF : LipschitzWith L F) (hL : 0<L) :
    (∫ g : κ→ℝ,diagonalSeminorm (matrixCentered F (WithLp.toLp 2 g)) ∂Measure.pi (fun _=>gaussianReal 0 1))≤
      matrixNormConstant*sqrt (Fintype.card ι)*(L:ℝ) ∧
    (∫ g : κ→ℝ,offDiagonalSeminorm (matrixCentered F (WithLp.toLp 2 g)) ∂Measure.pi (fun _=>gaussianReal 0 1))≤
      matrixNormConstant*sqrt (Fintype.card ι)*(L:ℝ) := by
  let : Fact (1≤(4:ENNReal)) := ⟨by norm_num⟩
  have hC0 : 0≤ matrixNormConstant := zero_le_one.trans matrixNormConstant_bounds.1
  have hcn : (0:ℝ)≤Fintype.card ι := Nat.cast_nonneg _
  constructor
  · apply le_of_pow_le_pow_left₀ (by decide : 2≠0) (by positivity)
    have hJ := gaussianProduct_jensen_pow (diagonalCentered_lip hF) (fun x=>norm_nonneg (diagonalVector (matrixCentered F x))) 2
    apply (hJ.trans (diagonalCentered_second_moment hF hL)).trans
    rw [mul_pow,mul_pow,sq_sqrt hcn]
    have hh := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left matrixNormConstant_bounds.2.1 hcn) (sq_nonneg (L:ℝ))
    nlinarith only [hh]
  · apply le_of_pow_le_pow_left₀ (by decide : 4≠0) (by positivity)
    have hJ := gaussianProduct_jensen_pow (offDiagonalCentered_lip hF) (fun x=>norm_nonneg (offDiagonalVector (matrixCentered F x))) 4
    apply (hJ.trans (offDiagonalCentered_fourth_moment hF hL)).trans
    have hs : sqrt (Fintype.card ι)^4=(Fintype.card ι:ℝ)^2 := by
      calc
        _ = (sqrt (Fintype.card ι)^2)^2 := by ring
        _ = _ := by rw [sq_sqrt hcn]
    rw [mul_pow,mul_pow,hs]
    have hh := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left matrixNormConstant_bounds.2.2 (sq_nonneg (Fintype.card ι:ℝ))) (by positivity : (0:ℝ)≤(L:ℝ)^4)
    nlinarith only [hh]
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

lemma matrixWordSeminorm_lipschitz (p : Bool) : LipschitzWith 1 (matrixWordSeminorm (ι:=ι) p) := by
  cases p
  · exact diagonalSeminorm_lipschitz
  · exact offDiagonalSeminorm_lipschitz
lemma matrixWordSeminorm_add (p : Bool) (M N : Matrix ι ι ℝ) :
    matrixWordSeminorm p (M+N)≤ matrixWordSeminorm p M+matrixWordSeminorm p N := by
  cases p
  · exact diagonalSeminorm_add M N
  · exact offDiagonalSeminorm_add M N

lemma gaussianProduct_centered_matrix_tail {F : EuclideanSpace ℝ κ→Matrix ι ι ℝ}
    {L : NNReal} (hF : LipschitzWith L F) (hL : 0<L) (p : Bool) {u : ℝ} (hu : 0≤u) :
    (Measure.pi (fun _ : κ=>gaussianReal 0 1))
      {g | matrixNormConstant*sqrt (Fintype.card ι)*(L:ℝ)+u<
        matrixWordSeminorm p (matrixCentered F (WithLp.toLp 2 g))}≤
      ENNReal.ofReal (exp (-2*u^2/(π^2*(L:ℝ)^2))) := by
  let μ := Measure.pi (fun _ : κ=>gaussianReal 0 1)
  let X : (κ→ℝ)→ℝ := fun g=>matrixWordSeminorm p (matrixCentered F (WithLp.toLp 2 g))
  have hXL : LipschitzWith L (fun x : EuclideanSpace ℝ κ=>X x.ofLp) := by
    simpa only [X,WithLp.toLp_ofLp,one_mul,Function.comp_def] using
      (matrixWordSeminorm_lipschitz p).comp (matrixCentered_lipschitz hF)
  have hE : (∫ g,X g ∂μ)≤ matrixNormConstant*sqrt (Fintype.card ι)*(L:ℝ) := by
    cases p
    · exact (gaussianProduct_centered_matrix_norms hF hL).1
    · exact (gaussianProduct_centered_matrix_norms hF hL).2
  have htail := gaussianProduct_upper_tail_lipschitz hXL hL hu
  have hmono : μ {g | matrixNormConstant*sqrt (Fintype.card ι)*(L:ℝ)+u<X g}≤
      μ {g | u≤X g-∫ h,X h ∂μ} := by
    apply measure_mono
    intro g hg
    change matrixNormConstant*sqrt (Fintype.card ι)*(L:ℝ)+u<X g at hg
    change u≤X g-∫ h,X h ∂μ
    linarith only [hg,hE]
  apply hmono.trans
  rw [←ENNReal.ofReal_toReal (measure_ne_top μ _)]
  exact ENNReal.ofReal_le_ofReal htail
end SKGap
end
end

section
noncomputable section
namespace SKGap
open Matrix Real MeasureTheory ProbabilityTheory Set
open scoped BigOperators Matrix.Norms.Frobenius
variable {κ : Type*} [Fintype κ]

lemma gaussianMatrix_scaled_semnorm_tail {n : ℕ} (hn : 1 ≤ n)
    {F : EuclideanSpace ℝ κ→Matrix (Fin n) (Fin n) ℝ} {H r T s : ℝ}
    (hH : 0<H) (hr : 0 < r) (hT : 0 ≤ T) (hs : 0 ≤ s)
    (hF : LipschitzWith (Real.toNNReal (H*r/sqrt n)) F) (p : Bool) :
    (Measure.pi (fun _ : κ=>gaussianReal 0 1))
      {g | (matrixNormConstant*H+T*s)*r< matrixWordSeminorm p (matrixCentered F (WithLp.toLp 2 g))} ≤
      ENNReal.ofReal (exp (-2*T^2*s^2*(n:ℝ)/(π^2*H^2))) := by
  have hn0 : (0:ℝ)<n := by exact_mod_cast (show 0<n by omega)
  have hnS := sqrt_pos.mpr hn0
  have hL : 0<Real.toNNReal (H*r/sqrt n) := by exact_mod_cast (Real.toNNReal_pos.mpr (div_pos (mul_pos hH hr) hnS))
  have hh := gaussianProduct_centered_matrix_tail hF hL p (mul_nonneg (mul_nonneg hT hs) hr.le)
  have he : (matrixNormConstant*sqrt (Fintype.card (Fin n))*(Real.toNNReal (H*r/sqrt n):ℝ)+T*s*r)=
      (matrixNormConstant*H+T*s)*r := by
    rw [Fintype.card_fin,Real.coe_toNNReal _ (by positivity)]
    field_simp
  have he' : -2*(T*s*r)^2/(π^2*(Real.toNNReal (H*r/sqrt n):ℝ)^2)=
      -2*T^2*s^2*(n:ℝ)/(π^2*H^2) := by
    rw [Real.coe_toNNReal _ (by positivity)]
    field_simp
    rw [sq_sqrt hn0.le]
  rw [he,he'] at hh
  exact hh
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
-- module Solutions.OAIQ072_SK.SKGap_Matrix_GOEDiagonalSquare
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

lemma gaussian_goe_centered {ι : Type*} [Fintype ι] [DecidableEq ι] (r : ℝ)
    (x : EuclideanSpace ℝ (MatrixCoordinates ι)) :
    matrixCentered (fun y : EuclideanSpace ℝ (MatrixCoordinates ι)=>goeMatrix r y) x=goeMatrix r x := by
  have hm : matrixEntryMean (fun y : EuclideanSpace ℝ (MatrixCoordinates ι)=>goeMatrix r y)=0 := by
    ext i k
    exact goe_mean_zero r i k
  simp only [matrixCentered,hm,sub_zero]

theorem goe_diagonal_frobenius_tail {j : ℝ} (hj : 0<j) {n : ℕ} (hn : 1≤n) :
    (Measure.pi (fun _ : MatrixCoordinates (Fin n)=>gaussianReal 0 1))
      {g | matrixNormConstant*sqrt (2*j)+1<
        ‖Matrix.diagonal (fun i=>goeMatrix (j/n) g i i)‖}≤
      ENNReal.ofReal (exp (-2*(n:ℝ)/(π^2*(sqrt (2*j))^2))) := by
  have hs : 0 < sqrt (2*j) := sqrt_pos.mpr (by positivity)
  have hL : LipschitzWith (Real.toNNReal (sqrt (2*j)*1/sqrt n))
      (fun x : EuclideanSpace ℝ (MatrixCoordinates (Fin n))=>goeMatrix (j/n) x) := by
    apply (goeMatrix_L2_lipschitz (j/n)).weaken
    change sqrt (2*(j/n))≤(Real.toNNReal (sqrt (2*j)*1/sqrt n):ℝ)
    rw [Real.coe_toNNReal _ (by positivity),mul_one,show 2*(j/n)=(2*j)/n by ring,Real.sqrt_div (by positivity)]
  have ht := gaussianMatrix_scaled_semnorm_tail hn hs (by norm_num : (0:ℝ)<1)
    (by norm_num : (0:ℝ)≤1) (by norm_num : (0:ℝ)≤1) hL false
  simpa only [one_pow,mul_one,gaussian_goe_centered,matrixWordSeminorm,Bool.false_eq_true,ite_false,
    Matrix.frobenius_norm_diagonal,diagonalSeminorm,diagonalVector] using ht
end SKGap
end
end

section
noncomputable section
namespace SKGap
open Matrix Real Set MeasureTheory ProbabilityTheory Filter
open scoped BigOperators Matrix.Norms.Frobenius SchwartzMap Topology
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma matrixWordSeminorm_le (p : Bool) (M : Matrix ι ι ℝ) : matrixWordSeminorm p M≤‖M‖ := by
  cases p
  · exact diagonalSeminorm_le M
  · exact offDiagonalSeminorm_le M

lemma actualWord_removeDiagonal [Nonempty ι] (f : 𝓢(ℝ,ℂ)) {R j A D : ℝ}
    (hR : 0≤R) (hj : 0≤j) (hA : 0≤A) (hD : 0≤D) {a : ι→ℝ}
    (ha : ∀ i,0≤a i) (haA : ∀ i,a i≤A) (L : ℕ) (F : List (WordLetter ι))
    (hFL : F.length≤L) (hF : ∀ l∈F,l.bounded D) (M : Matrix ι ι ℝ) :
    ‖actualWord f R hR j a 1 F (removeDiagonal M)-actualWord f R hR j a 1 F M‖≤
      (L:ℝ)*(actualWordBound f R j A D)^L*‖Matrix.diagonal (fun i=>M i i)‖ := by
  have hB : 1≤actualWordBound f R j A D := by
    have hh := path_constants_nonneg f hR hj hA
    unfold actualWordBound
    linarith
  have ht := ((actualWord_bounds f hR hj hA hD ha haA
    (show (1:ℝ)∈Icc 0 1 from ⟨zero_le_one,le_rfl⟩) F hF).2).dist_le_mul (removeDiagonal M) M
  have hd : ‖removeDiagonal M-M‖=‖Matrix.diagonal (fun i=>M i i)‖ := by
    rw [show removeDiagonal M-M= -Matrix.diagonal (fun i=>M i i) by unfold removeDiagonal;abel,norm_neg]
  simp only [dist_eq_norm,NNReal.coe_mul,NNReal.coe_natCast,hd] at ht
  apply ht.trans
  apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
  exact mul_le_mul (by exact_mod_cast hFL) (pow_le_pow_right₀ hB hFL)
    (pow_nonneg (zero_le_one.trans hB) _) (Nat.cast_nonneg _)

theorem actual_word_simultaneous_zerodiag_of_cutoff {j A D : ℝ} (hj : 0<j) (hA : 0<A)
    (hs : sqrt j*A<1) (hD : 1≤D) (hAD : A≤D) (L : ℕ) (f : 𝓢(ℝ,ℂ))
    (hf : ∀ x∈Icc ((1-sqrt j*A)^2/4) (2+A*(2*sqrt j+1+j*A)),f x=(x:ℂ)⁻¹)
    (hR : 0≤2*sqrt j+1+1) :
    ∃ (C : ℝ) (N : ℕ),0<C ∧ 0<N ∧
      ∀ n,N≤n → ∀ p : Bool,
        (Measure.pi (fun _ : MatrixCoordinates (Fin n)=>gaussianReal 0 1))
        {g | ∃ (a : Fin n→ℝ) (F : List (WordLetter (Fin n))),
          (∀ i,a i∈Icc 0 A) ∧ F.length≤L ∧ (∀ l∈F,l.bounded D) ∧ inverseCount F≤1 ∧
          C< matrixWordSeminorm p
            (actualWord f (2*sqrt j+1+1) hR j a 1 F (removeDiagonal (goeMatrix (j/n) g))-
              Matrix.diagonal (wordPrediction j a 1 F))} ≤
          (wordPatternSet L L).card*ENNReal.ofReal (3*exp (-(n:ℝ)))+
            ENNReal.ofReal (exp (-2*(n:ℝ)/(π^2*(sqrt (2*j))^2))) := by
  obtain ⟨C,N,hC,hN,hw⟩ := actual_word_simultaneous_prediction_of_cutoff hj hA hs hD hAD L f hf hR
  let R := 2*sqrt j+1+1
  let B := actualWordBound f R j A D
  let T := matrixNormConstant*sqrt (2*j)+1
  have hD0 := zero_le_one.trans hD
  have hB : 0≤B := (actualWordBound_pos f hR hj.le hA.le hD0).le
  have hT : 0≤T := by
    have hc := matrixNormConstant_bounds.1
    dsimp [T]
    positivity
  let K := (L:ℝ)*B^L*T
  have hK : 0≤K := by dsimp [K];positivity
  refine ⟨C+K,N,by linarith,hN,?_⟩
  intro n hn p
  have hn0 : 0<n := hN.trans_le hn
  let : Nonempty (Fin n) := Fin.pos_iff_nonempty.mp hn0
  let E := {g : MatrixCoordinates (Fin n)→ℝ | ∃ (a : Fin n→ℝ) (F : List (WordLetter (Fin n))),
    (∀ i,a i∈Icc 0 A) ∧ F.length≤L ∧ (∀ l∈F,l.bounded D) ∧ inverseCount F≤1 ∧
      C < matrixWordSeminorm p (actualWord f R hR j a 1 F (goeMatrix (j/n) g)-Matrix.diagonal (wordPrediction j a 1 F))}
  let V := {g : MatrixCoordinates (Fin n)→ℝ | T<‖Matrix.diagonal (fun i=>goeMatrix (j/n) g i i)‖}
  have hsub : {g | ∃ (a : Fin n→ℝ) (F : List (WordLetter (Fin n))),
      (∀ i,a i∈Icc 0 A) ∧ F.length≤L ∧ (∀ l∈F,l.bounded D) ∧ inverseCount F≤1 ∧
      C+K < matrixWordSeminorm p (actualWord f R hR j a 1 F (removeDiagonal (goeMatrix (j/n) g))-
        Matrix.diagonal (wordPrediction j a 1 F))}⊆E∪V := by
    intro g hg
    by_contra hh
    obtain ⟨a,F,ha,hFL,hF,hI,hbad⟩ := hg
    have hd : ‖Matrix.diagonal (fun i=>goeMatrix (j/n) g i i)‖≤T := by
      by_contra hd
      exact hh (Or.inr (lt_of_not_ge hd))
    have he : matrixWordSeminorm p (actualWord f R hR j a 1 F (goeMatrix (j/n) g)-Matrix.diagonal (wordPrediction j a 1 F))≤C := by
      by_contra he
      exact hh (Or.inl ⟨a,F,ha,hFL,hF,hI,lt_of_not_ge he⟩)
    have hp := (matrixWordSeminorm_le p _).trans (actualWord_removeDiagonal f hR hj.le hA.le hD0
      (fun i=>(ha i).1) (fun i=>(ha i).2) L F hFL hF (goeMatrix (j/n) g))
    have hp' : matrixWordSeminorm p
        (actualWord f R hR j a 1 F (removeDiagonal (goeMatrix (j/n) g))-actualWord f R hR j a 1 F (goeMatrix (j/n) g))≤K :=
      hp.trans (mul_le_mul_of_nonneg_left hd (mul_nonneg (Nat.cast_nonneg _) (pow_nonneg hB _)))
    have hac := matrixWordSeminorm_add p
      (actualWord f R hR j a 1 F (removeDiagonal (goeMatrix (j/n) g))-actualWord f R hR j a 1 F (goeMatrix (j/n) g))
      (actualWord f R hR j a 1 F (goeMatrix (j/n) g)-Matrix.diagonal (wordPrediction j a 1 F))
    rw [sub_add_sub_cancel] at hac
    linarith
  exact (measure_mono hsub).trans ((measure_union_le E V).trans
    (add_le_add (hw n hn p) (goe_diagonal_frobenius_tail hj (Nat.succ_le_iff.mpr hn0))))
end SKGap
end
end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Stability_WordStableAgreement
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
namespace SKGap
open Matrix Real Set
open RealComplex
open scoped BigOperators Matrix.Norms.Frobenius SchwartzMap
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem actualWord_agrees [Nonempty ι] (f : 𝓢(ℝ,ℂ)) {lo hi : ℝ} (hlo : 0<lo)
    (hf : ∀ x∈Icc lo hi,f x=(x:ℂ)⁻¹) {R : ℝ} (hR : 0≤R)
    (j : ℝ) {a : ι→ℝ} (ha : ∀ i,0≤a i) (M : Matrix ι ι ℝ)
    (hM : Mᵀ=M) (hMR : opNorm M≤R)
    (hl : lo≤ComplexSpectral.lowerRayleigh (liftMatrix
      (1-pathDiagonal a 1*(M-pathShift 1 ((j/(Fintype.card ι:ℝ))*∑ b,a b))*pathDiagonal a 1)))
    (hu : -hi≤ComplexSpectral.lowerRayleigh (-liftMatrix
      (1-pathDiagonal a 1*(M-pathShift 1 ((j/(Fintype.card ι:ℝ))*∑ b,a b))*pathDiagonal a 1)))
    (F : List (WordLetter ι)) : actualWord f R hR j a 1 F M=exactWord j a F M := by
  have he (l : WordLetter ι) : l.eval f R hR j a 1 M=l.exactEval j a M := by
    cases l with
    | diag d => rfl
    | noise => exact realProject_eq_self hR M hM hMR
    | inverse => exact pathK_agrees f hlo hf hR j ha M hM hMR hl hu
  induction F with
  | nil => rfl
  | cons l F ih =>
    change l.eval f R hR j a 1 M*actualWord f R hR j a 1 F M=l.exactEval j a M*exactWord j a F M
    rw [he,ih]
end SKGap
end
end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Stability_WordOrdinaryAgreement
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
namespace SKGap
open Matrix Real Set
open RealComplex
open scoped BigOperators Matrix.Norms.Frobenius SchwartzMap
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma actualWord_agrees_no_inverse (f : 𝓢(ℝ,ℂ)) {R : ℝ} (hR : 0≤R)
    (j : ℝ) (a : ι→ℝ) (M : Matrix ι ι ℝ) (hM : Mᵀ=M) (hMR : opNorm M≤R)
    (F : List (WordLetter ι)) (hF : inverseCount F=0) :
    actualWord f R hR j a 1 F M=exactWord j a F M := by
  induction F with
  | nil => rfl
  | cons l F ih =>
    cases l with
    | inverse => simp [inverseCount] at hF
    | diag d =>
      have ht : inverseCount F=0 := by simpa [inverseCount] using hF
      change diagonal d*actualWord f R hR j a 1 F M=diagonal d*exactWord j a F M
      rw [ih ht]
    | noise =>
      have ht : inverseCount F=0 := by simpa [inverseCount] using hF
      change realProject R hR M*actualWord f R hR j a 1 F M=M*exactWord j a F M
      rw [realProject_eq_self hR M hM hMR,ih ht]
end SKGap
end
end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Matrix_WordDiag
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
namespace SKGap
open Matrix Real Set MeasureTheory ProbabilityTheory Filter
open RealComplex
open scoped BigOperators Matrix.Norms.Frobenius SchwartzMap Topology

theorem zeroDiag_exact_word_source_restriction_oai {j A D c : ℝ} (hj : 0<j) (hA : 0<A)
    (hs : sqrt j*A<1) (hD : 1≤D) (hAD : A≤D) (hc : 0 < c) (L : ℕ) :
    ∃ (C : ℝ) (N : ℕ),0<C ∧ 0<N ∧ ∀ n,N≤n → ∀ p : Bool,
      (Measure.pi (fun _ : MatrixCoordinates (Fin n)=>gaussianReal 0 1))
      {g | opNorm (removeDiagonal (goeMatrix (j/n) g))≤2*sqrt j+1+1 ∧
        ∃ (a : Fin n→ℝ) (F : List (WordLetter (Fin n))),
          (∀ i,a i∈Icc 0 A) ∧ F.length≤L ∧ (∀ l∈F,l.bounded D) ∧ inverseCount F≤1 ∧
          (inverseCount F=0 ∨ c≤ComplexSpectral.lowerRayleigh (liftMatrix (stabilityMatrix a 1
            ((j/(n:ℝ))*∑ b,a b) (removeDiagonal (goeMatrix (j/n) g))))) ∧
          C< matrixWordSeminorm p
            (exactWord j a F (removeDiagonal (goeMatrix (j/n) g))-Matrix.diagonal (wordPrediction j a 1 F))} ≤
      (wordPatternSet L L).card*ENNReal.ofReal (3*exp (-(n:ℝ)))+
        ENNReal.ofReal (exp (-2*(n:ℝ)/(π^2*(sqrt (2*j))^2))) := by
  let R := 2*sqrt j+1+1
  let lo := min c ((1-sqrt j*A)^2/4)
  let hi := 2+A*(R+j*A)
  have hR : 0≤R := by dsimp [R];positivity
  have hint := path_interval hj.le hA.le hs
  have hlo : 0<lo := lt_min hc hint.1
  have hhi : 2+A*(2*sqrt j+1+j*A)≤hi := by dsimp [hi,R];nlinarith
  have hlohi : lo≤hi := (min_le_right _ _).trans (hint.2.trans hhi)
  obtain ⟨f,hf,_⟩ := exists_schwartz_inverse hlo hlohi
  have hfb : ∀ x∈Icc ((1-sqrt j*A)^2/4) (2+A*(2*sqrt j+1+j*A)),f x=(x:ℂ)⁻¹ := by
    intro x hx
    exact hf x ⟨(min_le_right _ _).trans hx.1,hx.2.trans hhi⟩
  obtain ⟨C,N,hC,hN,ht⟩ := actual_word_simultaneous_zerodiag_of_cutoff hj hA hs hD hAD L f hfb hR
  refine ⟨C,N,hC,hN,?_⟩
  intro n hn p
  have hn0 : 0<n := hN.trans_le hn
  let : Nonempty (Fin n) := Fin.pos_iff_nonempty.mp hn0
  apply (measure_mono ?_).trans (ht n hn p)
  intro g hg
  obtain ⟨hMR,a,F,ha,hFL,hF,hFI,hstable,hbad⟩ := hg
  refine ⟨a,F,ha,hFL,hF,hFI,?_⟩
  rcases hstable with hordinary|hstable
  · have he := actualWord_agrees_no_inverse f hR j a (removeDiagonal (goeMatrix (j/n) g))
      (by simp [removeDiagonal,Matrix.transpose_sub,goeMatrix_transpose]) hMR F hordinary
    rwa [he]
  · have haq : ∀ i,0≤a i := fun i=>(ha i).1
    have haA : ∀ i,a i≤A := fun i=>(ha i).2
    have hq := diagonal_mean_bounds hj.le haq haA
    simp only [Fintype.card_fin] at hq
    have hb := stabilityMatrix_opNorm haq haA hA.le (show (1:ℝ)∈Icc 0 1 from ⟨zero_le_one,le_rfl⟩) hq.1 hMR
    have hnrm : opNorm (stabilityMatrix a 1 ((j/(n:ℝ))*∑ b,a b) (removeDiagonal (goeMatrix (j/n) g)))≤hi := by
      apply hb.trans
      dsimp [hi,R]
      nlinarith
    have hu : -hi≤ComplexSpectral.lowerRayleigh (-liftMatrix (stabilityMatrix a 1
        ((j/(n:ℝ))*∑ b,a b) (removeDiagonal (goeMatrix (j/n) g)))) :=
      (neg_le_neg hnrm).trans (lowerRayleigh_neg_lift_ge _)
    have hl : lo≤ComplexSpectral.lowerRayleigh (liftMatrix (stabilityMatrix a 1
        ((j/(n:ℝ))*∑ b,a b) (removeDiagonal (goeMatrix (j/n) g)))) := (min_le_left _ _).trans hstable
    rw [stabilityMatrix_path_rep a haq zero_le_one] at hl hu
    have he := actualWord_agrees f hlo hf hR j haq (removeDiagonal (goeMatrix (j/n) g))
      (by simp [removeDiagonal,Matrix.transpose_sub,goeMatrix_transpose]) hMR (by simpa only [Fintype.card_fin] using hl)
        (by simpa only [Fintype.card_fin] using hu) F
    rwa [he]
end SKGap
end
end

end OAI
end

theorem solution : type_of% @OAI.SKGap.zeroDiag_exact_word_source_restriction_oai := @OAI.SKGap.zeroDiag_exact_word_source_restriction_oai
