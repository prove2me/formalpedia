-- Prove2me | solution 1 for OAI.SKGap.FullMain.quenched_posterior_covariance
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T06:54:24.108567+00:00
-- url     : https://prove2.me/submissions/041016d0-62aa-42db-9ab3-53217137c085

import Mathlib
import Definitions.Def_SKHighTemperature
import Definitions.Def_OAIQ072A002
import Theorems.Thm_OAI_SKGapCutoff_Recipe_buffered_posterior_covariance
import Theorems.Thm_OAI_SKGapCutoff_Recipe_disorder_closed_word_event
import Theorems.Thm_OAI_SKGapCutoff_Recipe_disorder_norm_event
import Theorems.Thm_OAI_SKGapCutoff_Recipe_disorder_word_event

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
local instance instPseudoMetrizableSpaceMatrixComplex_solutions_1_r4d1f93_1 : TopologicalSpace.PseudoMetrizableSpace (Matrix ι ι ℂ) :=
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
-- module Solutions.OAIQ072_SK.SKGap_Terminal_FiniteSpinCalculus
attribute [-instance] _root_.OAI.SKGap.ComplexMatrix.frobeniusInnerProduct
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
open MeasureTheory ProbabilityTheory Filter

namespace SKGap

section FiniteSpinCalculus

variable {n : ℕ}

theorem coupling_symm (g : Disorder n) (i k : Fin n) : coupling g i k = coupling g k i := by
  rcases lt_trichotomy i k with hik | rfl | hki
  · simp [coupling, hik, not_lt_of_gt hik]
  · rfl
  · simp [coupling, hki, not_lt_of_gt hki]

end FiniteSpinCalculus

end SKGap

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
-- module Solutions.OAIQ072_SK.SKGap_Localization_ScalarVariance
attribute [-instance] _root_.OAI.SKGap.ComplexMatrix.frobeniusInnerProduct
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators NNReal
open MeasureTheory ProbabilityTheory
open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators NNReal
open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal ENNReal
open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators NNReal ENNReal
open MeasureTheory ProbabilityTheory
open scoped BigOperators Matrix Matrix.Norms.Elementwise
open scoped BigOperators
open MeasureTheory ProbabilityTheory
open scoped BigOperators Matrix Matrix.Norms.Elementwise
open scoped BigOperators
namespace SKGapCutoff

lemma scalarVariance_pos (y : ℝ) : 0 < scalarVariance y :=
  sub_pos.mpr (Real.tanh_sq_lt_one y)

lemma scalarVariance_le_one (y : ℝ) : scalarVariance y ≤ 1 := by
  unfold scalarVariance
  nlinarith [sq_nonneg (Real.tanh y)]

end SKGapCutoff

open scoped BigOperators NNReal ENNReal
open MeasureTheory Metric Set

end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Localization_PhiAlgebra
attribute [-instance] _root_.OAI.SKGap.ComplexMatrix.frobeniusInnerProduct
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
namespace SKGap.Stein

namespace KernelExpr

lemma mass_nonneg (f : KernelExpr) : 0 ≤ mass f := by
  induction f <;> simp only [mass] <;> positivity

end KernelExpr

end SKGap.Stein

end
end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Localization_PhiFrechet
attribute [-instance] _root_.OAI.SKGap.ComplexMatrix.frobeniusInnerProduct
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open Filter
open scoped Topology
namespace SKGap.Stein

namespace KernelExpr
lemma dBudget_nonneg (f : KernelExpr) (R : ℝ) : 0≤f.dBudget R := by
  unfold dBudget
  exact mul_nonneg (add_nonneg (add_nonneg f.dz.mass_nonneg f.dr.mass_nonneg) f.da.mass_nonneg)
    (Real.exp_pos _).le
lemma ddBudget_nonneg (f : KernelExpr) (R : ℝ) : 0≤f.ddBudget R :=
  add_nonneg (add_nonneg (f.dz.dBudget_nonneg R) (f.dr.dBudget_nonneg R)) (f.da.dBudget_nonneg R)

end KernelExpr

end SKGap.Stein

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
-- module Solutions.OAIQ072_SK.SKGap_Matrix_DiscreteMatrixCalculus
attribute [-instance] _root_.OAI.SKGap.ComplexMatrix.frobeniusInnerProduct
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped BigOperators Matrix.Norms.Frobenius
namespace SKGapCutoff.Primary
open SKGap Matrix
variable {n : ℕ}

local instance instFactLeENNRealOfNat_solutions_r4d1f93_1 : Fact (1≤(4:ENNReal)) := ⟨by norm_num⟩
lemma opNorm_eq (M : Interaction n) :
    SKGap.opNorm M = ‖Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) M‖ := rfl

lemma opNorm_smul (c : ℝ) (M : Interaction n) : SKGap.opNorm (c • M) = |c| * SKGap.opNorm M := by
  simp only [opNorm_eq,map_smul,norm_smul,Real.norm_eq_abs]

end SKGapCutoff.Primary
end
end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Localization_SeparateCut
attribute [-instance] _root_.OAI.SKGap.ComplexMatrix.frobeniusInnerProduct
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
namespace SKGap.Noncrossing
universe u v
namespace Diagram
variable {D : Type*}

section Value
variable {ι : Type*} [Fintype ι]

lemma mean_const_mul (c : ℝ) (a : ι→ℝ) :
    mean (fun i => c*a i) = c*mean a := by
  simp only [mean,← Finset.mul_sum,mul_div_assoc]

end Value

end Diagram
end SKGap.Noncrossing

end
end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Matrix_InverseDiagram
attribute [-instance] _root_.OAI.SKGap.ComplexMatrix.frobeniusInnerProduct
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
noncomputable section
open scoped BigOperators
namespace SKGap.Noncrossing

namespace InverseDiagram

variable {ι : Type*} [Fintype ι]

lemma sum_flatMap {α : Type*} {R : Type*} [AddMonoid R]
    (l : List α) (f : α → List R) : (l.flatMap f).sum = (l.map (fun x => (f x).sum)).sum := by
  induction l with
  | nil => rfl
  | cons x l ih => simp only [List.flatMap_cons, List.sum_append, List.map_cons, List.sum_cons, ih]

end InverseDiagram
end SKGap.Noncrossing

end
end
end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Localization_PrimaryPrediction
attribute [-instance] _root_.OAI.SKGap.ComplexMatrix.frobeniusInnerProduct _root_.OAI.SKGap.Noncrossing.Diagram.noiseSplitFinite _root_.OAI.SKGap.Noncrossing.Diagram.noiseSplitFintype _root_.OAI.SKGap.Noncrossing.Diagram.pairedNilUnique _root_.OAI.SKGap.Noncrossing.WordSeries.noiseSplitNilIsEmpty _root_.OAI.SKGap.Noncrossing.noiseSplitDiagIsEmpty _root_.OAI.SKGap.Noncrossing.noiseSplitNoiseUnique
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped BigOperators
namespace SKGap.Noncrossing.Primary
open Diagram

namespace Partial
variable {D : Type*}
lemma word_contract (p q : Partial D) (h : p.contract=some q) : q.word = .noise :: p.word := by
  cases p with
  | done d => simp [contract] at h
  | more d p => cases p <;> simp only [contract,Option.some.injEq] at h <;> subst q <;>
      simp [word,Diagram.word,List.append_assoc]
lemma diag_injective (a : D) : Function.Injective (diag a : Partial D → Partial D) := by
  intro p q h; cases p <;> cases q <;> simp_all [diag]
lemma create_injective : Function.Injective (create : Partial D → Partial D) := by
  intro p q h; exact Partial.more.inj h |>.2
lemma contract_injective {p q r : Partial D} (hp : p.contract=some r) (hq : q.contract=some r) : p=q := by
  cases p with
  | done d => simp [contract] at hp
  | more d p =>
    cases q with
    | done e => simp [contract] at hq
    | more e q =>
      cases p <;> cases q <;> simp only [contract,Option.some.injEq] at hp hq <;>
        subst r <;> simp_all
lemma create_ne_contract (p q r : Partial D) (h : q.contract=some r) : p.create≠r := by
  cases q with
  | done d => simp [contract] at h
  | more d q => cases q <;> simp only [contract,Option.some.injEq] at h <;> subst r <;> simp [create]

lemma diag_preimage (a : D) (F : List (Letter D)) (p : Partial D)
    (h : p.word = .diag a :: F) : ∃ q : Partial D, q.word=F ∧ p=q.diag a := by
  cases p with
  | done d => cases d <;> simp only [word,Diagram.word] at h
              case diag b d => simp only [List.cons.injEq,Letter.diag.injEq] at h
                               obtain ⟨rfl,h⟩ := h; exact ⟨.done d,h,rfl⟩
              all_goals simp at h
  | more d p =>
    cases d with
    | nil => simp [word,Diagram.word] at h
    | arch d e => simp [word,Diagram.word] at h
    | diag b d =>
      simp only [word,Diagram.word,List.cons_append,List.cons.injEq,Letter.diag.injEq] at h
      obtain ⟨rfl,h⟩ := h; exact ⟨.more d p,h,rfl⟩
lemma noise_preimage (F : List (Letter D)) (p : Partial D)
    (h : p.word = .noise :: F) :
    ∃ q : Partial D, q.word=F ∧ (p=q.create ∨ q.contract=some p) := by
  cases p with
  | done d =>
    cases d with
    | nil => simp [word,Diagram.word] at h
    | diag a d => simp [word,Diagram.word] at h
    | arch d e =>
      simp only [word,Diagram.word,List.cons.injEq,true_and] at h
      exact ⟨.more d (.done e),h,Or.inr rfl⟩
  | more d p =>
    cases d with
    | nil =>
      simp only [word,Diagram.word,List.nil_append,List.cons.injEq,true_and] at h
      exact ⟨p,h,Or.inl rfl⟩
    | diag a d => simp [word,Diagram.word] at h
    | arch d e =>
      simp only [word,Diagram.word,List.cons_append,List.cons.injEq,true_and,List.append_assoc] at h
      exact ⟨.more d (.more e p),h,Or.inr rfl⟩

@[simp] lemma mem_enumerate (F : List (Letter D)) (p : Partial D) :
    p∈enumerate F ↔ p.word=F := by
  induction F generalizing p with
  | nil =>
    cases p with
    | done d => cases d <;> simp [enumerate,word,Diagram.word]
    | more d p => simp [enumerate,word]
  | cons a F ih =>
    cases a with
    | diag a =>
      simp only [enumerate,List.mem_map,ih]
      constructor
      · rintro ⟨q,hq,rfl⟩; simp [hq]
      · intro hp; obtain ⟨q,hq,hp⟩ := diag_preimage a F p hp; exact ⟨q,hq,hp.symm⟩
    | noise =>
      simp only [enumerate,List.mem_flatMap,noise,List.mem_cons,Option.mem_toList,ih]
      constructor
      · rintro ⟨q,hq,hp|hp⟩
        · subst p; simp [hq]
        · rw [word_contract q p hp,hq]
      · intro hp; obtain ⟨q,hq,hp⟩ := noise_preimage F p hp; exact ⟨q,hq,hp⟩

lemma noise_nodup (p : Partial D) : p.noise.Nodup := by
  cases p with
  | done d => simp [noise,contract]
  | more d p => cases p <;> simp [noise,contract,create]
lemma noise_disjoint {p q : Partial D} (h : p≠q) : List.Disjoint p.noise q.noise := by
  apply List.disjoint_left.mpr
  intro r hr hq
  simp only [noise,List.mem_cons,Option.mem_toList] at hr hq
  rcases hr with hr|hr <;> rcases hq with hq|hq
  · exact h (create_injective (hr.symm.trans hq))
  · exact create_ne_contract p q r hq hr.symm
  · exact create_ne_contract q p r hr hq.symm
  · exact h (contract_injective hr hq)
lemma enumerate_nodup (F : List (Letter D)) : (enumerate F).Nodup := by
  induction F with
  | nil => simp [enumerate]
  | cons a F ih =>
    cases a with
    | diag a => exact ih.map (diag_injective a)
    | noise =>
      rw [enumerate,List.nodup_flatMap]
      exact ⟨fun p _ => noise_nodup p, List.Pairwise.imp (fun h => noise_disjoint h) ih⟩
end Partial

section Fock
variable {ι : Type*} [Fintype ι]

lemma value_factor (j : ℝ) (d : Diagram (D (ι:=ι))) (i : ι) :
    d.value j i=coefficient j d * outer d i := by
  induction d with
  | nil => simp [Diagram.value,coefficient,outer]
  | diag a d ih => simp [Diagram.value,coefficient,outer,ih]; ring
  | arch a b ia ib => simp [Diagram.value,coefficient,outer,ib]; ring
lemma mean_value (j : ℝ) (d : Diagram (D (ι:=ι))) :
    Diagram.mean (d.value j)=coefficient j d * Diagram.mean (outer d) := by
  simp only [funext (value_factor j d),Diagram.mean_const_mul]

lemma Partial.state_diag (j : ℝ) (a : D (ι:=ι)) (p : Partial (D (ι:=ι))) :
    (p.diag a).state j = diagonal a (p.state j) := by
  cases p <;> simp [state,stack,Partial.diag,Partial.coefficient,Primary.coefficient,Primary.outer]
lemma Partial.state_create (j : ℝ) (p : Partial (D (ι:=ι))) :
    p.create.state j = creation (p.state j) := by
  simp [state,stack,create,Partial.coefficient,Primary.coefficient,Primary.outer]
lemma Partial.state_contract (j : ℝ) (p : Partial (D (ι:=ι))) :
    ((p.contract.toList).map (Partial.state j)).sum = j • annihilation (p.state j) := by
  cases p with
  | done d => simp [state,stack,Partial.contract]
  | more d p =>
    cases p <;> simp [state,stack,Partial.contract,Partial.coefficient,
      Primary.coefficient,Primary.outer,mean_value,smul_smul,mul_assoc,mul_left_comm,mul_comm]
lemma Partial.state_noise (j : ℝ) (p : Partial (D (ι:=ι))) :
    ((p.noise).map (Partial.state j)).sum = Primary.noise j (p.state j) := by
  simp only [Partial.noise,List.map_cons,List.sum_cons,state_create,state_contract]
  rfl

lemma word_vacuum (j : ℝ) (F : List (Letter (D (ι:=ι)))) :
    word j F vacuum = ((Partial.enumerate F).map (Partial.state j)).sum := by
  induction F with
  | nil => simp [word,vacuum,Partial.enumerate,Partial.state,Partial.stack,
      Partial.coefficient,Primary.coefficient,Primary.outer]
  | cons a F ih =>
    cases a with
    | diag a =>
      simp only [word,letter,LinearMap.comp_apply,ih,Partial.enumerate,List.map_map]
      simp only [map_list_sum,Function.comp_def,Partial.state_diag,List.map_map]
    | noise =>
      simp only [word,letter,LinearMap.comp_apply,ih,Partial.enumerate,List.map_flatMap]
      rw [SKGap.Noncrossing.InverseDiagram.sum_flatMap]
      simp only [Partial.state_noise,map_list_sum,List.map_map,Function.comp_def]

lemma Partial.project_state_done (j : ℝ) (d : Diagram (D (ι:=ι))) (i : ι) :
    project ((.done d : Partial _).state j) i = d.value j i := by
  simp [Partial.state,Partial.stack,Partial.coefficient,value_factor]
lemma Partial.project_state_more (j : ℝ) (d : Diagram (D (ι:=ι)))
    (p : Partial (D (ι:=ι))) : project ((Partial.more d p).state j) = 0 := by
  simp [Partial.state,Partial.stack]

lemma prediction_as_finset (j : ℝ) (F : List (Letter (D (ι:=ι)))) (i : ι) :
    Diagram.prediction j F i = ∑ d∈Diagram.enumerate F, d.value j i := by
  classical
  let e : Diagram.Paired F ≃ {d // d∈Diagram.enumerate F} :=
    { toFun := fun d => ⟨d.val,(Diagram.mem_enumerate F d.val).mpr d.property⟩
      invFun := fun d => ⟨d.val,(Diagram.mem_enumerate F d.val).mp d.property⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  change (∑ d : Diagram.Paired F, d.val.value j i) = _
  calc
    _ = ∑ d : {d // d∈Diagram.enumerate F}, d.val.value j i :=
      Fintype.sum_equiv e _ _ (fun _ => rfl)
    _ = _ := Finset.sum_coe_sort (Diagram.enumerate F) (fun d => d.value j i)

theorem project_word (j : ℝ) (F : List (Letter (D (ι:=ι)))) (i : ι) :
    project (word j F vacuum) i = Diagram.prediction j F i := by
  classical
  rw [word_vacuum,map_list_sum,List.map_map]
  change (((Partial.enumerate F).map (fun p => project (p.state j))).sum) i = _
  have heval : (((Partial.enumerate F).map (fun p => project (p.state j))).sum) i =
      ((Partial.enumerate F).map (fun p => project (p.state j) i)).sum := by
    induction Partial.enumerate F with
    | nil => rfl
    | cons p L ih => simp [ih]
  rw [heval,← List.sum_toFinset _ (Partial.enumerate_nodup F),prediction_as_finset]
  have hsub : (Diagram.enumerate F).image Partial.done ⊆ (Partial.enumerate F).toFinset := by
    intro p hp
    obtain ⟨d,hd,rfl⟩ := Finset.mem_image.mp hp
    simpa [Partial.word] using hd
  rw [← Finset.sum_subset hsub (fun p hp hn => ?_)]
  · rw [Finset.sum_image (fun d _ e _ h => Partial.done.inj h)]
    exact Finset.sum_congr rfl (fun d _ => Partial.project_state_done j d i)
  · cases p with
    | done d =>
      exfalso; apply hn
      exact Finset.mem_image.mpr ⟨d,by simpa [Partial.word] using hp,rfl⟩
    | more d p => simp [Partial.project_state_more]

theorem primaryOperator_vacuum (j : ℝ) (a : ℕ → D (ι:=ι)) (n : ℕ) :
    primaryOperator j a n vacuum = ket (1,creationLabels a n) := by
  induction n using Nat.twoStepInduction with
  | zero => rfl
  | one => simp [primaryOperator,noise,vacuum,creationLabels,previousDiagonal]
  | more n hn hn1 =>
    simp [primaryOperator,LinearMap.comp_apply,hn,hn1,noise,creationLabels,
      previousDiagonal,smul_smul]

theorem primaryOperator_prediction_zero (j : ℝ) (a : ℕ → D (ι:=ι))
    (n : ℕ) (hn : 0<n) : project (primaryOperator j a n vacuum) = 0 := by
  cases n with
  | zero => omega
  | succ n => rw [primaryOperator_vacuum]; simp [creationLabels]

lemma word_append (j : ℝ) (F G : List (Letter (D (ι:=ι)))) :
    word j (F++G) = (word j F).comp (word j G) := by
  induction F with
  | nil => simp [word]
  | cons a F ih => simp [word,ih,LinearMap.comp_assoc]
lemma polynomialOperator_append (j : ℝ) (P Q : WordPolynomial (ι:=ι)) :
    polynomialOperator j (P++Q) = polynomialOperator j P + polynomialOperator j Q := by
  simp [polynomialOperator]
lemma polynomialOperator_prefix (j : ℝ) (F : List (Letter (D (ι:=ι))))
    (P : WordPolynomial (ι:=ι)) :
    polynomialOperator j (prependWords F P) = (word j F).comp (polynomialOperator j P) := by
  induction P with
  | nil => simp [prependWords,polynomialOperator]
  | cons p P ih =>
    simp only [prependWords,List.map_cons,polynomialOperator,List.sum_cons] at *
    rw [word_append,ih,LinearMap.comp_add,LinearMap.comp_smul]
lemma polynomialOperator_scale (j c : ℝ) (P : WordPolynomial (ι:=ι)) :
    polynomialOperator j (scale c P)=c • polynomialOperator j P := by
  induction P with
  | nil => simp [scale,polynomialOperator]
  | cons p P ih =>
    simp only [scale,List.map_cons,polynomialOperator,List.sum_cons] at *
    rw [ih,smul_add,mul_smul]

lemma primaryPolynomial_operator (j : ℝ) (a : ℕ → D (ι:=ι)) (n : ℕ) :
    polynomialOperator j (primaryPolynomial j a n)=primaryOperator j a n := by
  induction n using Nat.twoStepInduction with
  | zero => simp [primaryPolynomial,polynomialOperator,primaryOperator,word]
  | one => simp [primaryPolynomial,polynomialOperator,primaryOperator,word,letter]
  | more n hn hn1 =>
    simp only [primaryPolynomial,polynomialOperator_append,polynomialOperator_prefix,
      polynomialOperator_scale,hn,hn1,word,letter,LinearMap.comp_id,primaryOperator]
    ext v k
    simp [LinearMap.comp_apply,sub_eq_add_neg,neg_smul]

lemma polynomialPrediction_eq_project (j : ℝ) (P : WordPolynomial (ι:=ι)) (i : ι) :
    polynomialPrediction j P i = project (polynomialOperator j P vacuum) i := by
  induction P with
  | nil => simp [polynomialPrediction,polynomialOperator]
  | cons p P ih =>
    simp only [polynomialPrediction,polynomialOperator,List.map_cons,List.sum_cons,
      LinearMap.add_apply,LinearMap.smul_apply,map_add,map_smul,Pi.add_apply,Pi.smul_apply,
      smul_eq_mul] at *
    rw [project_word,ih]

theorem primaryPolynomial_prediction_zero (j : ℝ) (a : ℕ → D (ι:=ι))
    (n : ℕ) (hn : 0<n) (i : ι) :
    polynomialPrediction j (primaryPolynomial j a n) i = 0 := by
  rw [polynomialPrediction_eq_project,primaryPolynomial_operator,
    primaryOperator_prediction_zero j a n hn]
  rfl

end Fock
end SKGap.Noncrossing.Primary
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
-- module Solutions.OAIQ072_SK.SKGap_Matrix_WordDiagUniform
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

theorem exactWord_uniform_opNorm {j A D c R : ℝ} (hj : 0≤j) (hA : 0≤A)
    (hD : 0≤D) (hc : 0 < c) (hR : 0≤R) (L : ℕ) :
    ∃ C : ℝ,0<C ∧ ∀ n,0<n → ∀ (a : Fin n→ℝ) (F : List (WordLetter (Fin n)))
      (M : Matrix (Fin n) (Fin n) ℝ),
      (∀ i,a i∈Icc 0 A) → F.length≤L → (∀ l∈F,l.bounded D) → Mᵀ=M → opNorm M≤R →
      (inverseCount F=0 ∨ c≤ComplexSpectral.lowerRayleigh (liftMatrix (stabilityMatrix a 1 ((j/(n:ℝ))*∑ b,a b) M))) →
      opNorm (exactWord j a F M)≤C := by
  let hi := max c (2+A*(R+j*A))
  obtain ⟨f,hf,_⟩ := exists_schwartz_inverse hc (le_max_left c (2+A*(R+j*A)))
  let B := actualWordBound f R j A D
  have hB : 1≤B := by
    have hh := path_constants_nonneg f hR hj hA
    unfold B actualWordBound
    linarith
  refine ⟨B^L,pow_pos (lt_of_lt_of_le zero_lt_one hB) _,?_⟩
  intro n hn a F M ha hFL hF hM hMR hstable
  let : Nonempty (Fin n) := Fin.pos_iff_nonempty.mp hn
  rcases hstable with hordinary|hstable
  · have he := actualWord_agrees_no_inverse f hR j a M hM hMR F hordinary
    rw [←he]
    exact ((actualWord_bounds f hR hj hA hD (fun i=>(ha i).1) (fun i=>(ha i).2)
      (show (1:ℝ)∈Icc 0 1 from ⟨zero_le_one,le_rfl⟩) F hF).1 M).trans (pow_le_pow_right₀ hB hFL)
  · have haq : ∀ i,0≤a i := fun i=>(ha i).1
    have haA : ∀ i,a i≤A := fun i=>(ha i).2
    have hq := diagonal_mean_bounds hj haq haA
    simp only [Fintype.card_fin] at hq
    have hb := stabilityMatrix_opNorm haq haA hA (show (1:ℝ)∈Icc 0 1 from ⟨zero_le_one,le_rfl⟩) hq.1 hMR
    have hnrm : opNorm (stabilityMatrix a 1 ((j/(n:ℝ))*∑ b,a b) M)≤hi := by
      apply hb.trans
      apply le_trans _ (le_max_right c (2+A*(R+j*A)))
      nlinarith
    have hu : -hi≤ComplexSpectral.lowerRayleigh (-liftMatrix (stabilityMatrix a 1 ((j/(n:ℝ))*∑ b,a b) M)) :=
      (neg_le_neg hnrm).trans (lowerRayleigh_neg_lift_ge _)
    rw [stabilityMatrix_path_rep a haq zero_le_one] at hstable hu
    have he := actualWord_agrees f hc hf hR j haq M hM hMR
      (by simpa only [Fintype.card_fin] using hstable) (by simpa only [Fintype.card_fin] using hu) F
    rw [←he]
    exact ((actualWord_bounds f hR hj hA hD haq haA
      (show (1:ℝ)∈Icc 0 1 from ⟨zero_le_one,le_rfl⟩) F hF).1 M).trans (pow_le_pow_right₀ hB hFL)
end SKGap
end
end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Matrix_PrimaryMatrix
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped BigOperators
namespace SKGap.Noncrossing.Primary
open WordSeries
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma matrixWord_append (J : Matrix ι ι ℝ) (F G : List (Letter (ι→ℝ))) :
    matrixWord J (F++G)=matrixWord J F*matrixWord J G := by simp [matrixWord]
lemma matrixPolynomial_append (J : Matrix ι ι ℝ) (P Q : WordPolynomial (ι:=ι)) :
    matrixPolynomial J (P++Q)=matrixPolynomial J P+matrixPolynomial J Q := by
  simp [matrixPolynomial]
lemma matrixPolynomial_prefix (J : Matrix ι ι ℝ) (F : List (Letter (ι→ℝ)))
    (P : WordPolynomial (ι:=ι)) :
    matrixPolynomial J (prependWords F P)=matrixWord J F*matrixPolynomial J P := by
  induction P with
  | nil => simp [prependWords,matrixPolynomial]
  | cons p P ih =>
    simp only [prependWords,List.map_cons,matrixPolynomial,List.sum_cons] at *
    rw [matrixWord_append,ih,mul_add,mul_smul_comm]
lemma matrixPolynomial_scale (J : Matrix ι ι ℝ) (c : ℝ) (P : WordPolynomial (ι:=ι)) :
    matrixPolynomial J (scale c P)=c • matrixPolynomial J P := by
  induction P with
  | nil => simp [scale,matrixPolynomial]
  | cons p P ih =>
    simp only [scale,List.map_cons,matrixPolynomial,List.sum_cons] at *
    rw [ih,smul_add,mul_smul]

lemma primaryPolynomial_matrix (j : ℝ) (J : Matrix ι ι ℝ) (a : ℕ→ι→ℝ) (n : ℕ) :
    matrixPolynomial J (primaryPolynomial j a n)=primaryMatrix j J a n := by
  induction n using Nat.twoStepInduction with
  | zero => simp [primaryPolynomial,matrixPolynomial,primaryMatrix,matrixWord]
  | one => simp [primaryPolynomial,matrixPolynomial,primaryMatrix,matrixWord,matrixLetter]
  | more n hn hn1 =>
    simp only [primaryPolynomial,matrixPolynomial_append,matrixPolynomial_prefix,
      matrixPolynomial_scale,hn,hn1,primaryMatrix,matrixWord,List.map_cons,List.map_nil,
      List.prod_cons,List.prod_nil,mul_one,matrixLetter]
    simp [mul_assoc,sub_eq_add_neg,neg_smul]

lemma matrixWordSeminorm_zero (p : Bool) : matrixWordSeminorm (ι:=ι) p 0=0 := by
  let : Fact (1≤(4:ENNReal)) := ⟨by norm_num⟩
  have hd : diagonalVector (0 : Matrix ι ι ℝ)=0 := by ext i; rfl
  have ho : offDiagonalVector (0 : Matrix ι ι ℝ)=0 := by ext ⟨i,k⟩; simp [offDiagonalVector]
  cases p <;> simp [matrixWordSeminorm,diagonalSeminorm,offDiagonalSeminorm,hd,ho]
lemma matrixWordSeminorm_smul (p : Bool) (c : ℝ) (J : Matrix ι ι ℝ) :
    matrixWordSeminorm p (c • J)=|c| *matrixWordSeminorm p J := by
  let : Fact (1≤(4:ENNReal)) := ⟨by norm_num⟩
  have hd : diagonalVector (c • J)=c • diagonalVector J := by ext i; rfl
  have ho : offDiagonalVector (c • J)=c • offDiagonalVector J := by
    ext ⟨i,k⟩
    by_cases h : i=k <;> simp [offDiagonalVector,h]
  cases p
  · simp [matrixWordSeminorm,diagonalSeminorm,hd,norm_smul,Real.norm_eq_abs]
  · simp [matrixWordSeminorm,offDiagonalSeminorm,ho,norm_smul,Real.norm_eq_abs]

lemma polynomial_error (p : Bool) (j : ℝ) (J : Matrix ι ι ℝ)
    (P : WordPolynomial (ι:=ι)) {C : ℝ}
    (h : ∀ t∈P, matrixWordSeminorm p
      (matrixWord J t.2-Matrix.diagonal (Diagram.prediction j t.2))≤C) :
    matrixWordSeminorm p (matrixPolynomial J P-Matrix.diagonal (polynomialPrediction j P))≤
      coefficientMass P*C := by
  induction P with
  | nil => simp [matrixPolynomial,polynomialPrediction,coefficientMass,matrixWordSeminorm_zero]
  | cons t P ih =>
    have he : matrixPolynomial J (t::P)-Matrix.diagonal (polynomialPrediction j (t::P))=
        t.1 • (matrixWord J t.2-Matrix.diagonal (Diagram.prediction j t.2))+
        (matrixPolynomial J P-Matrix.diagonal (polynomialPrediction j P)) := by
      have hp : polynomialPrediction j (t::P)=
          t.1 • Diagram.prediction j t.2+polynomialPrediction j P := by
        ext i; simp [polynomialPrediction]
      have hd (u v : ι→ℝ) : Matrix.diagonal (u+v)=Matrix.diagonal u+Matrix.diagonal v :=
        (Matrix.diagonal_add u v).symm
      simp only [matrixPolynomial,List.map_cons,List.sum_cons,hp,hd,Matrix.diagonal_smul]
      rw [smul_sub]
      abel
    rw [he]
    calc
      _ ≤ matrixWordSeminorm p (t.1 • (matrixWord J t.2-Matrix.diagonal (Diagram.prediction j t.2)))+
          matrixWordSeminorm p (matrixPolynomial J P-Matrix.diagonal (polynomialPrediction j P)) :=
        matrixWordSeminorm_add _ _ _
      _ ≤ |t.1| *C+coefficientMass P*C := by
        rw [matrixWordSeminorm_smul]
        exact add_le_add (mul_le_mul_of_nonneg_left (h t (by simp)) (abs_nonneg _))
          (ih (fun q hq=>h q (List.mem_cons_of_mem _ hq)))
      _ = coefficientMass (t::P)*C := by simp [coefficientMass,add_mul]

theorem primaryMatrix_seminorm (p : Bool) (j : ℝ) (J : Matrix ι ι ℝ)
    (a : ℕ→ι→ℝ) (n : ℕ) (hn : 0<n) {C : ℝ}
    (h : ∀ t∈primaryPolynomial j a n, matrixWordSeminorm p
      (matrixWord J t.2-Matrix.diagonal (Diagram.prediction j t.2))≤C) :
    matrixWordSeminorm p (primaryMatrix j J a n) ≤ coefficientMass (primaryPolynomial j a n)*C := by
  have hz : polynomialPrediction j (primaryPolynomial j a n)=0 :=
    funext (primaryPolynomial_prediction_zero j a n hn)
  simpa only [primaryPolynomial_matrix,hz,Matrix.diagonal_zero',sub_zero] using
    polynomial_error p j J (primaryPolynomial j a n) h

omit [DecidableEq ι]

omit [Fintype ι] in
lemma coefficientMass_nonneg (P : WordPolynomial (ι:=ι)) : 0 ≤ coefficientMass P :=
  List.sum_nonneg (by intro x hx; obtain ⟨t,ht,rfl⟩ := List.mem_map.mp hx; exact abs_nonneg _)
omit [Fintype ι] in
lemma coefficientMass_append (P Q : WordPolynomial (ι:=ι)) :
    coefficientMass (P++Q)=coefficientMass P+coefficientMass Q := by simp [coefficientMass]
omit [Fintype ι] in
lemma coefficientMass_prefix (F : List (Letter (ι→ℝ))) (P : WordPolynomial (ι:=ι)) :
    coefficientMass (prependWords F P)=coefficientMass P := by
  simp [coefficientMass,prependWords,Function.comp_def]
omit [Fintype ι] in
lemma coefficientMass_scale (c : ℝ) (P : WordPolynomial (ι:=ι)) :
    coefficientMass (scale c P)=|c| *coefficientMass P := by
  simp [coefficientMass,scale,Function.comp_def,abs_mul,List.sum_map_mul_left]

lemma mean_abs_le_one [Nonempty ι] {a : ι→ℝ} (ha : ∀ i,|a i|≤1) :
    |Diagram.mean a|≤1 := by
  have hn : (0:ℝ)<Fintype.card ι := Nat.cast_pos.mpr Fintype.card_pos
  calc
    |Diagram.mean a| = |∑ i,a i|/(Fintype.card ι:ℝ) := by
      rw [Diagram.mean,abs_div,abs_of_pos hn]
    _ ≤ (∑ i,|a i|)/(Fintype.card ι:ℝ) :=
      div_le_div_of_nonneg_right (Finset.abs_sum_le_sum_abs _ _) hn.le
    _ ≤ 1 := by
      rw [div_le_one hn]
      simpa using Finset.sum_le_sum (fun i (_ : i∈Finset.univ) => ha i)

lemma massBound_pos (j : ℝ) (n : ℕ) : 0< massBound j n := by
  induction n using Nat.twoStepInduction with
  | zero => norm_num [massBound]
  | one => norm_num [massBound]
  | more n hn hn1 => exact add_pos_of_pos_of_nonneg hn1 (mul_nonneg (abs_nonneg _) hn.le)
lemma primaryMass_bound [Nonempty ι] (j : ℝ) (a : ℕ→ι→ℝ)
    (ha : ∀ n i,|a n i|≤1) (n : ℕ) :
    coefficientMass (primaryPolynomial j a n)≤ massBound j n := by
  induction n using Nat.twoStepInduction with
  | zero => simp [primaryPolynomial,coefficientMass,massBound]
  | one => simp [primaryPolynomial,coefficientMass,massBound]
  | more n hn hn1 =>
    simp only [primaryPolynomial,coefficientMass_append,coefficientMass_prefix,
      coefficientMass_scale,abs_neg,abs_mul,massBound]
    apply add_le_add hn1
    calc
      |j| * |Diagram.mean (a n)| * coefficientMass (primaryPolynomial j a n) ≤
          |j| * 1 * coefficientMass (primaryPolynomial j a n) :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left (mean_abs_le_one (ha n)) (abs_nonneg _))
          (coefficientMass_nonneg _)
      _ ≤ |j| * massBound j n := by simpa using mul_le_mul_of_nonneg_left hn (abs_nonneg j)

lemma primaryPolynomial_admissible (j : ℝ) (a : ℕ→ι→ℝ)
    (ha : ∀ n i,|a n i|≤1) (n : ℕ) :
    ∀ t∈primaryPolynomial j a n, t.2.length≤2*n ∧
      ∀ l∈liftWord t.2,l.bounded 1 := by
  have hp (n : ℕ) : ∀ i,|previousDiagonal a n i|≤1 := by
    cases n <;> simp [previousDiagonal,ha]
  induction n using Nat.twoStepInduction with
  | zero => simp [primaryPolynomial,liftWord]
  | one =>
    intro t ht
    simp only [primaryPolynomial,List.mem_singleton] at ht
    subst t
    simp [liftWord,Letter.toWord,WordLetter.bounded]
  | more n hn hn1 =>
    intro t ht
    simp only [primaryPolynomial,List.mem_append,prependWords,scale,List.mem_map] at ht
    rcases ht with ⟨q,hq,rfl⟩ | ⟨u,⟨q,hq,rfl⟩,rfl⟩
    · obtain ⟨hql,hqb⟩ := hn1 q hq
      constructor
      · simp only [List.length_append,List.length_cons,List.length_nil]; omega
      · intro l hl
        simp only [liftWord_append,liftWord_cons,liftWord_nil,Letter.toWord,
          List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at hl
        rcases hl with (rfl|rfl)|hl
        · trivial
        · exact ha n
        · exact hqb l hl
    · obtain ⟨hql,hqb⟩ := hn q hq
      constructor
      · simp only [List.length_append,List.length_cons,List.length_nil]; omega
      · intro l hl
        simp only [liftWord_append,liftWord_cons,liftWord_nil,Letter.toWord,
          List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at hl
        rcases hl with rfl|hl
        · exact hp n
        · exact hqb l hl

end SKGap.Noncrossing.Primary
end
end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Localization_PrimaryDifferentiation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped BigOperators Matrix.Norms.Frobenius
namespace SKGapCutoff.Primary
open SKGap Matrix
variable {n : ℕ}

lemma primaryDiagonal_bounded (j : ℝ) (J : Interaction n) (h : Fin n→ℝ) (x : Spin n) :
    ∀ k i, |primaryDiagonal j J h x k i|≤1 := by
  intro k i
  rw [primaryDiagonal,abs_of_pos (scalarVariance_pos _)]
  exact scalarVariance_le_one _

end SKGapCutoff.Primary

end
end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Gaussian_SteinRecipeRegularity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped BigOperators
namespace SKGapCutoff.Recipe
open SKGap.Stein
variable {n : ℕ} {ι κ σ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] [Fintype σ]

lemma steinCoefficientBudget_nonneg (R : ℝ) : 0 ≤ steinCoefficientBudget R := by
  have h0:= (KernelExpr.atom 0 0 false).mass_nonneg
  have h1:= (KernelExpr.atom 0 0 false).dBudget_nonneg R
  have h2:= (KernelExpr.atom 0 0 false).ddBudget_nonneg R
  unfold steinCoefficientBudget
  positivity

end SKGapCutoff.Recipe

end
end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Localization_MarkedDiagnostic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped BigOperators
namespace SKGapCutoff.Recipe
open SKGap.Noncrossing SKGap.Noncrossing.Primary SKGap.Noncrossing.Primary.MarkedPolynomial
variable {n : ℕ}

lemma wordBounded_mono {A B : ℝ} {u : OrdinaryWord n} (h : wordBounded A u) (hab : A≤B) :
    wordBounded B u := by
  intro l hl; cases l with
  | noise=>trivial
  | diag p=>exact fun i=>(h (.diag p) hl i).trans hab

end SKGapCutoff.Recipe

end
end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Localization_PrimaryQuenched
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped BigOperators Matrix.Norms.Frobenius
namespace SKGapCutoff.Primary
open SKGap Matrix MeasureTheory ProbabilityTheory Real Set
open SKGap.Noncrossing.Primary

variable {n : ℕ}

lemma formalOpBound_nonneg (j : ℝ) {R : ℝ} (hR : 0≤R) (k : ℕ) :
    0≤formalOpBound j R k := by
  induction k using Nat.twoStepInduction with
  | zero => norm_num [formalOpBound]
  | one => exact hR
  | more k hk hk1 => dsimp only [formalOpBound]; positivity

lemma primaryMatrix_opNorm {j R : ℝ} (J : Interaction n) (a : ℕ→Fin n→ℝ)
    (hn : 0<n) (hR : 0≤R) (hJ : SKGap.opNorm J≤R) (ha : ∀ l i,|a l i|≤1) (k : ℕ) :
    SKGap.opNorm (primaryMatrix j J a k)≤formalOpBound j R k := by
  let : Nonempty (Fin n) := Fin.pos_iff_nonempty.mp hn
  have hd (l : ℕ) : SKGap.opNorm (Matrix.diagonal (a l))≤1 :=
    SKGap.opNorm_diagonal_le zero_le_one (ha l)
  have hp (l : ℕ) : SKGap.opNorm (Matrix.diagonal (previousDiagonal a l))≤1 := by
    apply SKGap.opNorm_diagonal_le zero_le_one
    cases l with
    | zero => simp [previousDiagonal]
    | succ l => exact ha l
  induction k using Nat.twoStepInduction with
  | zero => exact SKGap.opNorm_one_le
  | one => exact hJ
  | more k hk hk1 =>
    dsimp only [primaryMatrix,formalOpBound]
    apply (SKGap.opNorm_sub _ _).trans
    apply add_le_add
    · apply (SKGap.opNorm_mul _ _).trans
      have hJD : SKGap.opNorm (J*Matrix.diagonal (a k))≤R :=
        (SKGap.opNorm_mul _ _).trans ((mul_le_mul hJ (hd k) (norm_nonneg _) hR).trans_eq (mul_one _))
      exact mul_le_mul hJD hk1 (norm_nonneg _) hR
    · rw [opNorm_smul,abs_mul]
      have hm : SKGap.opNorm (Matrix.diagonal (previousDiagonal a k)*primaryMatrix j J a k)≤
          formalOpBound j R k :=
        (SKGap.opNorm_mul _ _).trans ((mul_le_mul (hp k) hk (norm_nonneg _)
          zero_le_one).trans_eq (one_mul _))
      calc
        _ ≤ (|j| *1)*formalOpBound j R k := mul_le_mul
          (mul_le_mul_of_nonneg_left (mean_abs_le_one (ha k)) (abs_nonneg _)) hm
          (norm_nonneg _) (by positivity)
        _ = _ := by ring

end SKGapCutoff.Primary

end
end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Stability_OrdinaryWordEvent
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped BigOperators
namespace SKGapCutoff.Recipe
open SKGap SKGap.Noncrossing SKGap.Noncrossing.Primary MeasureTheory ProbabilityTheory Real Set
variable {n : ℕ}

lemma wordBounded_lift (A : ℝ) (w : OrdinaryWord n) :
    wordBounded A w ↔ ∀l∈liftWord w,l.bounded A := by
  constructor
  · intro h l hl
    obtain ⟨a,ha,rfl⟩:=List.mem_map.mp hl
    cases a <;> exact h _ ha
  · intro h l hl
    have hh:=h (Letter.toWord l) (List.mem_map.mpr ⟨l,hl,rfl⟩)
    cases l <;> exact hh

lemma wordSeminormBound_diagram {J : Interaction n} {j A C : ℝ} {L : ℕ}
    (h : WordSeminormBound J j A C L) : WordDiagramBound J j A C L := h false

lemma offDiagonalSeminorm_sub_diagonal (M : Interaction n) (a : Fin n→ℝ) :
    SKGap.offDiagonalSeminorm (M-Matrix.diagonal a)=SKGap.offDiagonalSeminorm M := by
  unfold SKGap.offDiagonalSeminorm
  congr 1
  ext ⟨i,k⟩
  by_cases hik:i=k <;> simp [SKGap.offDiagonalVector,Matrix.diagonal_apply,hik]

lemma matrixWord_opNorm (J : Interaction n) (hn : 0<n) {R : ℝ}
    (hR : 1≤R) (hJ : SKGap.opNorm J≤R) (w : OrdinaryWord n) (hw : wordBounded R w) :
    SKGap.opNorm (matrixWord J w)≤R^w.length := by
  let : Nonempty (Fin n):=Fin.pos_iff_nonempty.mp hn
  induction w with
  | nil=>simpa [matrixWord] using (SKGap.opNorm_one_le (ι:=Fin n))
  | cons l w ih=>
    have hl : SKGap.opNorm (matrixLetter J l)≤R := by
      cases l with
      | noise=>exact hJ
      | diag a=>exact SKGap.opNorm_diagonal_le (by linarith) (hw (.diag a) (List.mem_cons_self))
    have hh:=ih (fun a ha=>hw a (List.mem_cons_of_mem _ ha))
    simp only [matrixWord,List.map_cons,List.prod_cons,List.length_cons,pow_succ]
    exact (SKGap.opNorm_mul _ _).trans ((mul_le_mul hl hh (norm_nonneg _) (by linarith)).trans_eq (mul_comm _ _))

lemma wordSeminormBound_test {J : Interaction n} {j A C R : ℝ} {L : ℕ}
    (h : WordSeminormBound J j A C L) (hn : 0<n) (hR : 1≤R) (hA : A≤R) (hJ : SKGap.opNorm J≤R) :
    WordTestBound J A (R^L+C) L := by
  intro w hw hb
  have hs:=h true w hw hb
  simp only [matrixWordSeminorm,↓reduceIte,offDiagonalSeminorm_sub_diagonal] at hs
  exact add_le_add ((matrixWord_opNorm J hn hR hJ w (wordBounded_mono hb hA)).trans
    (pow_le_pow_right₀ hR hw)) hs

end SKGapCutoff.Recipe

end
end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Matrix_PrimaryWordEventBinding
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped BigOperators
namespace SKGapCutoff.Recipe
open Primary SKGap SKGap.Noncrossing SKGap.Noncrossing.Primary MeasureTheory ProbabilityTheory Real Set
variable {n : ℕ}

lemma WordSeminormBound.mono {J : Interaction n} {j A C : ℝ} {L K : ℕ}
    (h : WordSeminormBound J j A C L) (hK : K≤L) : WordSeminormBound J j A C K :=
  fun p w hw hb=>h p w (hw.trans hK) hb

lemma primaryEventBudget_nonneg {j R C : ℝ} (hR : 0≤R) (hC : 0≤C) (M : ℕ) :
    0≤primaryEventBudget j R C M :=
  Finset.sum_nonneg (fun _ _=>add_nonneg (formalOpBound_nonneg j hR _) (mul_nonneg (massBound_pos j _).le hC))

lemma wordEvent_formal {j R A C : ℝ} (J : Interaction n) (hn : 0<n)
    (hR : 0≤R) (hC : 0≤C) (hA : 1≤A) (hJ : SKGap.opNorm J≤R) (M L : ℕ) (hML : 2*M≤L)
    (hw : WordSeminormBound J j A C L) (h : Fin n→ℝ) (x : Spin n) (l : ℕ) (hl : l<M) :
    ShapeBound (formalField j J h x l) (primaryEventBudget j R C M) := by
  let : Nonempty (Fin n):=Fin.pos_iff_nonempty.mp hn
  let q:Fin M:=⟨l,hl⟩
  have hnon := formalOpBound_nonneg j hR (l+1)
  have hmass := mul_nonneg (massBound_pos j (l+1)).le hC
  have hb:=Finset.single_le_sum (s:=Finset.univ)
    (f:=fun q:Fin M=>formalOpBound j R (q.val+1)+massBound j (q.val+1)*C)
    (fun q _=>add_nonneg (formalOpBound_nonneg j hR _) (mul_nonneg (massBound_pos j _).le hC))
    (Finset.mem_univ q)
  have ho : formalOpBound j R (l+1)≤primaryEventBudget j R C M :=
    (le_add_of_nonneg_right hmass).trans hb
  have hm : massBound j (l+1)*C≤primaryEventBudget j R C M :=
    (le_add_of_nonneg_left hnon).trans hb
  have ha:=primaryDiagonal_bounded j J h x
  have hp (p : Bool) : matrixWordSeminorm p (formalField j J h x l)≤primaryEventBudget j R C M := by
    apply (primaryMatrix_seminorm p j J (primaryDiagonal j J h x) (l+1) (by omega) ?_).trans
    · exact (mul_le_mul_of_nonneg_right (primaryMass_bound j _ ha (l+1)) hC).trans hm
    · intro t ht
      have htB:=primaryPolynomial_admissible j _ ha (l+1) t ht
      exact hw p t.2 (htB.1.trans (by omega))
        (wordBounded_mono ((wordBounded_lift 1 _).mpr htB.2) hA)
  exact ⟨(primaryMatrix_opNorm J _ hn hR hJ ha (l+1)).trans ho,hp false,hp true⟩

lemma wordEvent_recipeEvent {j R A C : ℝ} (J : Interaction n) (hn : 0<n)
    (hR : 1≤R) (hA : 1≤A) (hAR : A≤R) (hC : 0≤C) (hJ : SKGap.opNorm J≤R)
    (M Nmax : ℕ) (hw : WordSeminormBound J j A C (2*M+2*Nmax+3)) :
    RecipeMatrixEvent j R A (primaryEventBudget j R C M) (R^(2*Nmax+3)+C) C M Nmax J := by
  refine ⟨hJ,fun h x l hl=>wordEvent_formal J hn (by linarith) hC hA hJ M _ (by omega) hw h x l hl,
    wordSeminormBound_test (hw.mono (by omega)) hn hR hAR hJ,?_⟩
  exact wordSeminormBound_diagram (hw.mono (by omega))

end SKGapCutoff.Recipe

end
end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Gaussian_GaussianRecipeEvent
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped BigOperators Topology
open Filter MeasureTheory ProbabilityTheory Real
namespace SKGapCutoff.Recipe
open SKGap SKGap.Noncrossing SKGap.Noncrossing.Primary

lemma exp_rate_limit {c : ℝ} (hc : 0 < c) :
    Tendsto (fun n : ℕ=>exp (-c*(n:ℝ))) atTop (𝓝 0) := by
  simpa using (summable_pow_mul_exp_neg_nat_mul 0 hc).tendsto_atTop_zero
lemma n_exp_rate_limit {c : ℝ} (hc : 0 < c) :
    Tendsto (fun n : ℕ=>(n:ℝ)*exp (-c*(n:ℝ))) atTop (𝓝 0) := by
  simpa using (summable_pow_mul_exp_neg_nat_mul 1 hc).tendsto_atTop_zero

lemma recipeNormTail_limit {j : ℝ} (hj : 0<j) :
    Tendsto (recipeNormTail j) atTop (𝓝 0) := by
  have h₁ : Tendsto (fun n : ℕ=>ENNReal.ofReal (2*exp (-(n:ℝ)/(π^2*j)))) atTop (𝓝 0) := by
    have H:=ENNReal.tendsto_ofReal ((exp_rate_limit (c:=1/(π^2*j)) (by positivity)).const_mul 2)
    simpa only [mul_zero,ENNReal.ofReal_zero,show ∀(n : ℕ),-(1/(π^2*j))*(n:ℝ)=-(n:ℝ)/(π^2*j) by intro n;ring] using H
  have h₂ : Tendsto (fun n : ℕ=>ENNReal.ofReal (2*(n:ℝ)*exp (-1/(8*(j/n))))) atTop (𝓝 0) := by
    have H:=ENNReal.tendsto_ofReal ((n_exp_rate_limit (c:=1/(8*j)) (by positivity)).const_mul 2)
    have HH : Tendsto (fun n : ℕ=>ENNReal.ofReal (2*((n:ℝ)*exp (-(1/(8*j))*(n:ℝ))))) atTop (𝓝 0):=by simpa using H
    apply HH.congr'
    filter_upwards [eventually_ge_atTop 1] with n hn
    have hn0 : (n:ℝ)≠0:=by exact_mod_cast (by omega : n≠0)
    congr 1
    rw [mul_assoc]
    congr 2
    field_simp
  convert h₁.add h₂ using 1 <;> first | rfl | simp

lemma ordinaryWordTail_limit {j : ℝ} (hj : 0<j) (L : ℕ) :
    Tendsto (ordinaryWordTail j L) atTop (𝓝 0) := by
  have h₁ : Tendsto (fun n : ℕ=>ENNReal.ofReal (3*exp (-(n:ℝ)))) atTop (𝓝 0) := by
    simpa using ENNReal.tendsto_ofReal ((exp_rate_limit (c:=1) (by norm_num)).const_mul 3)
  have h₂ : Tendsto (fun n : ℕ=>ENNReal.ofReal (exp (-2*(n:ℝ)/(π^2*(sqrt (2*j))^2)))) atTop (𝓝 0) := by
    have hsq : 0<(sqrt (2*j))^2:=by rw [sq_sqrt (by positivity)]; positivity
    have H:=ENNReal.tendsto_ofReal (exp_rate_limit (c:=2/(π^2*(sqrt (2*j))^2)) (by positivity))
    simpa only [ENNReal.ofReal_zero,show ∀(n : ℕ),-(2/(π^2*(sqrt (2*j))^2))*(n:ℝ)= -2*(n:ℝ)/(π^2*(sqrt (2*j))^2) by intro n;ring] using H
  have h₃:=(ENNReal.Tendsto.const_mul h₁ (a:=((wordPatternSet L L).card:ENNReal)) (Or.inr (by simp))).add h₂ |>.add (recipeNormTail_limit hj)
  convert ENNReal.Tendsto.const_mul h₃ (a:=2) (Or.inr (by simp)) using 1 <;> first | rfl | simp

end SKGapCutoff.Recipe

end
end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Matrix_FixedNormRecipeEvent
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped BigOperators Topology
open Filter MeasureTheory ProbabilityTheory Real
namespace SKGapCutoff.Recipe
open SKGap SKGap.Noncrossing SKGap.Noncrossing.Primary

lemma physicalNormBound_pos (j : ℝ) : 0<physicalNormBound j := by
  unfold physicalNormBound
  positivity

end SKGapCutoff.Recipe

end
end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Localization_DisorderRecipeEvent
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped BigOperators Matrix.Norms.Frobenius

noncomputable section
open scoped BigOperators Topology
namespace SKGapCutoff.Recipe
open SKGap SKGap.ObservationBridge SKGap.Noncrossing SKGap.Noncrossing.Primary
open MeasureTheory ProbabilityTheory Real Set Filter

theorem disorder_fixed_norm_recipe_probability {β A : ℝ} (hβ : 0<β) (hβ1 : β<1)
    (hA : 1≤A) (M Nmax : ℕ) : ∃B W C : ℝ,0≤B ∧ 0≤W ∧ 0<C ∧
      Tendsto (fun n=>SKGap.disorderLaw β n
        {g | ¬RecipeMatrixEvent (β^2) (physicalNormBound (β^2)) A B W C M Nmax
          (coupling g)}) atTop (𝓝 0) := by
  let j:=β^2
  have hj : 0<j:=sq_pos_of_pos hβ
  let R:=max A (physicalNormBound j)
  have hAR : A≤R:=le_max_left _ _
  have hR : 1≤R:=hA.trans hAR
  obtain ⟨C,N,hC,hN,hword⟩:=disorder_word_event hβ hβ1 hA (2*M+2*Nmax+3)
  refine ⟨primaryEventBudget j R C M,R^(2*Nmax+3)+C,C,
    primaryEventBudget_nonneg (by linarith) hC.le M,
    add_nonneg (pow_nonneg (by linarith) _) hC.le,hC,?_⟩
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds
    (show Tendsto (fun n=>recipeNormTail j n+ordinaryWordTail j (2*M+2*Nmax+3) n) atTop (𝓝 0) from
      by simpa using (recipeNormTail_limit hj).add (ordinaryWordTail_limit hj _))
    (Filter.Eventually.of_forall (fun _=>bot_le))
  filter_upwards [eventually_ge_atTop N] with n hn
  have hn0 : 0<n:=hN.trans_le hn
  let E:Set (Disorder n):={g | physicalNormBound j<SKGap.opNorm (coupling g)}
  let F:Set (Disorder n):={g | ¬WordSeminormBound (coupling g) j A C (2*M+2*Nmax+3)}
  have hE : SKGap.disorderLaw β n E ≤ recipeNormTail j n:=disorder_norm_event hβ hn0
  have hF : SKGap.disorderLaw β n F≤ordinaryWordTail j (2*M+2*Nmax+3) n:=hword n hn
  apply (measure_mono (t:=E∪F) ?_).trans ((measure_union_le _ _).trans (add_le_add hE hF))
  intro g hg
  by_contra hh
  have hp : SKGap.opNorm (coupling g)≤physicalNormBound j:=le_of_not_gt (fun hbad=>hh (.inl hbad))
  have hw : WordSeminormBound (coupling g) j A C (2*M+2*Nmax+3):=by
    by_contra hbad;exact hh (.inr hbad)
  have hev:=wordEvent_recipeEvent (coupling g) hn0 hR hA hAR hC.le
    (hp.trans (le_max_right _ _)) M Nmax hw
  exact hg ⟨hp,hev.2⟩

end SKGapCutoff.Recipe

end
end
end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Matrix_StartedWordClosure
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped BigOperators
namespace SKGapCutoff.Recipe
open Matrix SKGap SKGap.Noncrossing SKGap.Noncrossing.Primary MeasureTheory ProbabilityTheory Real Set
variable {n : ℕ}

lemma closedWordBounded_iff (A : ℝ) (w : List (WordLetter (Fin n))) :
    closedWordBounded A w ↔ ∀l∈w,l.bounded A := by
  constructor <;> intro h l hl <;> cases l <;> exact h _ hl

lemma ClosedWordSeminormBound.diagram {j A C : ℝ} {a : Fin n→ℝ} {J : Interaction n} {L : ℕ}
    (h : ClosedWordSeminormBound j a J A C L) : ClosedWordDiagramBound j a J A C L := h false

theorem closed_word_test_budget {j A D c R : ℝ} (hj : 0≤j) (hA : 0≤A)
    (hD : 0≤D) (hc : 0 < c) (hR : 0≤R) (L : ℕ) :
    ∃W : ℝ,0<W ∧ ∀n,0<n→∀(a:Fin n→ℝ) (J:Interaction n) (C:ℝ),
      (∀i,a i∈Icc 0 A)→Jᵀ=J→SKGap.opNorm J≤R→
      c≤ComplexSpectral.lowerRayleigh (RealComplex.liftMatrix (stabilityMatrix a 1 ((j/n)*∑i,a i) J))→
      ClosedWordSeminormBound j a J D C L→ClosedWordTestBound j a J D (W+C) L := by
  obtain ⟨W,hW,hw⟩:=exactWord_uniform_opNorm hj hA hD hc hR L
  refine ⟨W,hW,?_⟩
  intro n hn a J C ha hJ hR' hs hb w hl hi hwb
  have hop:=hw n hn a w J ha hl ((closedWordBounded_iff D w).mp hwb) hJ hR' (Or.inr hs)
  have hoff:=hb true w hl hi hwb
  simp only [matrixWordSeminorm,↓reduceIte,offDiagonalSeminorm_sub_diagonal] at hoff
  exact add_le_add hop hoff

end SKGapCutoff.Recipe

end
end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Matrix_StartedMatrixEvent
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped BigOperators Topology
namespace SKGapCutoff.Recipe
open Primary Matrix SKGap SKGap.Noncrossing SKGap.Noncrossing.Primary MeasureTheory ProbabilityTheory Real Set Filter
variable {n : ℕ}

lemma ClosedWordTestBound.mono {j A W : ℝ} {a : Fin n→ℝ} {J : Interaction n} {L K : ℕ}
    (h : ClosedWordTestBound j a J A W L) (hK : K≤L) : ClosedWordTestBound j a J A W K :=
  fun w hw hi hb=>h w (hw.trans hK) hi hb
lemma ClosedWordDiagramBound.mono {j A C : ℝ} {a : Fin n→ℝ} {J : Interaction n} {L K : ℕ}
    (h : ClosedWordDiagramBound j a J A C L) (hK : K≤L) : ClosedWordDiagramBound j a J A C K :=
  fun w hw hi hb=>h w (hw.trans hK) hi hb

end SKGapCutoff.Recipe

end
end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Localization_UniformResidual
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped BigOperators
namespace SKGapCutoff.Recipe
open Primary Static
universe u
variable {Ω : Type u} {n : Ω→ℕ} {M Nmax : ℕ} {A j : ℝ}
variable {J : ∀a,Interaction (n a)} {h : ∀a,Fin (n a)→ℝ}
variable {P : ∀a,Observables (n a)}

lemma residualCoefficientBudget_ge (j : ℝ) {K : ℝ} (hK : 0≤K) (t p : ℕ) :
    K ≤ residualCoefficientBudget j K t p := by
  simpa only [mul_one,residualCoefficientBudget] using mul_le_mul_of_nonneg_left
    (one_le_pow₀ (by linarith [steinCoefficientBudget_nonneg |j|]) :
      1≤(1+4*steinCoefficientBudget |j|)^(t-p)) hK

end SKGapCutoff.Recipe

end
end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Localization_LocalExtraction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped BigOperators

noncomputable section
open scoped BigOperators
namespace SKGapCutoff.Recipe
open Primary Static
variable {n : ℕ}

lemma StartedMatrixEvent.mono_budget {j R A₀ A A' c B W C : ℝ} {M N : ℕ}
    {J : Interaction n} (H : StartedMatrixEvent j R A₀ A c B W C M N J) (hA : A'≤A) :
    StartedMatrixEvent j R A₀ A' c B W C M N J := by
  refine ⟨H.1,H.2.1,?_⟩
  intro a ha hc
  have h:=(H.2.2 a ha hc)
  have hb : ∀w : List (SKGap.WordLetter (Fin n)),closedWordBounded A' w→closedWordBounded A w := by
    intro w hw l hl
    have hh:=hw l hl
    cases l with
    | diag p=>exact fun i=>(hh i).trans hA
    | noise=>trivial
    | inverse=>trivial
  exact ⟨fun w hw hi hwa=>h.1 w hw hi (hb w hwa),fun w hw hi hwa=>h.2 w hw hi (hb w hwa)⟩

end SKGapCutoff.Recipe

end
end
end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Localization_QuenchedHelpers
attribute [-instance] _root_.OAI.SKGap.ComplexMatrix.frobeniusInnerProduct _root_.OAI.SKGap.disorderLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SKGap.FullMain
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology ENNReal NNReal BigOperators
noncomputable section

lemma Whp.mono {β : ℝ} {P Q : ∀n,Disorder n→Prop} (hP : Whp β P)
    (hPQ : ∀ᶠ n : ℕ in atTop,∀g,P n g→Q n g) : Whp β Q := by
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hP
    (Eventually.of_forall (fun _=>bot_le))
  filter_upwards [hPQ] with n hn
  apply measure_mono
  intro g hg hp
  exact hg (hn g hp)

lemma Whp.of_eventually {β : ℝ} {P : ℕ→Prop} (hP : ∀ᶠ n : ℕ in atTop,P n) :
    Whp β (fun n _=>P n) := by
  apply Tendsto.congr' _ tendsto_const_nhds
  filter_upwards [hP] with n hn
  simp [hn]

lemma Whp.and {β : ℝ} {P Q : ∀n,Disorder n→Prop} (hP : Whp β P) (hQ : Whp β Q) :
    Whp β (fun n g=>P n g ∧ Q n g) := by
  classical
  have H:=hP.add hQ
  rw [add_zero] at H
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds H
    (Eventually.of_forall (fun _=>bot_le))
  apply Eventually.of_forall
  intro n
  have he : {g:Disorder n | ¬(P n g ∧ Q n g)}={g | ¬P n g}∪{g | ¬Q n g} := by
    ext g
    simp only [mem_ofPred_eq,mem_union]
    tauto
  rw [he]
  exact measure_union_le _ _

lemma whp_finset {β : ℝ} {ι : Type*} (s : Finset ι) (P : ι→∀n,Disorder n→Prop)
    (hP : ∀i∈s,Whp β (P i)) : Whp β (fun n g=>∀i∈s,P i n g) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    apply Whp.mono (Whp.of_eventually (β:=β) (P:=fun _=>True) (Eventually.of_forall (fun _=>True.intro)))
    exact Eventually.of_forall (fun n g _=>by simp)
  | @insert i s hi ih =>
    have H := (hP i (by simp)).and (ih (fun j hj=>hP j (by simp [hj])))
    exact H.mono (Eventually.of_forall (fun n g hg=>by simpa only [Finset.mem_insert,forall_eq_or_imp] using hg))

end
end SKGap.FullMain

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Matrix_BufferedClosedWord
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped BigOperators Topology
namespace SKGapCutoff.Recipe
open Primary Matrix SKGap SKGap.Noncrossing SKGap.Noncrossing.Primary MeasureTheory ProbabilityTheory Real Set Filter

theorem disorder_started_matrix_event {β A₀ A c : ℝ} (hβ : 0<β) (hβ1 : β<1)
    (hA₀ : 0<A₀) (hs : sqrt (β^2)*A₀<1) (hAA : A₀≤A) (hA : 1≤A) (hc : 0 < c)
    (M Nmax : ℕ) : ∃B W C : ℝ,0≤B ∧ 0≤W ∧ 0<C ∧
      Tendsto (fun n=>SKGap.disorderLaw β n
        {g | ¬StartedMatrixEvent (β^2) (physicalNormBound (β^2)) A₀ A c B W C M Nmax
          (coupling g)}) atTop (𝓝 0) := by
  let j:=β^2
  have hj : 0<j:=sq_pos_of_pos hβ
  let R:=max A (physicalNormBound j)
  have hAR : A≤R:=le_max_left _ _
  have hR : 1≤R:=hA.trans hAR
  obtain ⟨C,N,hC,hN,hclosed⟩:=disorder_closed_word_event hβ hA₀ hs hA hAA hc (2*M+2*Nmax+5)
  obtain ⟨B,N',hB,hN',hordinary⟩:=disorder_word_event hβ hβ1 hA (2*M+2*Nmax+5)
  obtain ⟨W,hW,htest⟩:=closed_word_test_budget hj.le hA₀.le
    (by linarith : 0≤A) hc (by unfold physicalNormBound; positivity : 0≤physicalNormBound j) (2*M+2*Nmax+5)
  refine ⟨primaryEventBudget j R B M,W+C,C,
    primaryEventBudget_nonneg (by linarith) hB.le _,by positivity,hC,?_⟩
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds
    (show Tendsto (fun n=>recipeNormTail j n+ordinaryWordTail j (2*M+2*Nmax+5) n+
      ordinaryWordTail j (2*M+2*Nmax+5) n) atTop (𝓝 0) from by
      simpa using ((recipeNormTail_limit hj).add (ordinaryWordTail_limit hj _)).add (ordinaryWordTail_limit hj _))
    (Filter.Eventually.of_forall (fun _=>bot_le))
  filter_upwards [eventually_ge_atTop (max N N')] with n hn
  have hnN : N≤n:=(le_max_left ..).trans hn
  have hnN' : N'≤n:=(le_max_right ..).trans hn
  have hn0 : 0<n:=hN.trans_le hnN
  let μ:=SKGap.disorderLaw β n
  let V : Set (Disorder n):={g | physicalNormBound j<SKGap.opNorm (coupling g)}
  let U : Set (Disorder n):={g | ¬WordSeminormBound (coupling g) j A B (2*M+2*Nmax+5)}
  let F : Set (Disorder n):={g | ¬ClosedWordEvent j A₀ A c C (2*M+2*Nmax+5) (coupling g)}
  have hV : μ V ≤ recipeNormTail j n:=disorder_norm_event hβ hn0
  have hU : μ U≤ordinaryWordTail j (2*M+2*Nmax+5) n:=hordinary n hnN'
  have hF : μ F≤ordinaryWordTail j (2*M+2*Nmax+5) n:=hclosed n hnN
  apply (measure_mono (t:=(V∪U)∪F) ?_).trans ((measure_union_le _ _).trans
    (add_le_add ((measure_union_le _ _).trans (add_le_add hV hU)) hF))
  intro g hg
  by_contra hh
  have hJ : SKGap.opNorm (coupling g)≤physicalNormBound j:=
    le_of_not_gt (fun hbad=>hh (.inl (.inl hbad)))
  have hu : WordSeminormBound (coupling g) j A B (2*M+2*Nmax+5):=by
    by_contra hbad; exact hh (.inl (.inr hbad))
  have hf : ClosedWordEvent j A₀ A c C (2*M+2*Nmax+5) (coupling g):=by
    by_contra hbad; exact hh (.inr hbad)
  apply hg
  refine ⟨hJ,fun h x l hl=>wordEvent_formal _ hn0 (by linarith) hB.le hA (hJ.trans (le_max_right _ _)) M _ (by omega) hu h x l hl,?_⟩
  intro a ha hstable
  have hb:=hf a ha hstable
  have hsym : (coupling g)ᵀ=coupling g := by
    ext i k;exact coupling_symm g k i
  exact ⟨(htest n hn0 a _ C ha hsym hJ hstable hb).mono (by omega),hb.diagram.mono (by omega)⟩

end SKGapCutoff.Recipe

end
end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Posterior_BufferedPosteriorCovariance
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open Filter Topology
namespace SKGapCutoff.Recipe
open SKGap.Stein Primary Static

theorem posterior_buffer_exists (j K c r₀ R ε : ℝ)
    (hc : 0 < c) (hr₀ : 0 < r₀) (hR : 0<R) (hε : 0<ε) :
    ∃ρ : ℝ,0<ρ ∧
      (K+4*j)*(2*ρ) < r₀ ∧
      (1+2*j)*(1+(1+(K+3*j)/c)*(K+4*j))*(2*ρ)≤R ∧
      (3*Real.exp (R/2)+2)*((1+2*j)*(1+(1+(K+3*j)/c)*(K+4*j))*(2*ρ))≤ε ∧
      (1+2*j)*(1+(1+(K+3*j)/c)*(K+4*j))*(2*ρ)≤
        c/(2*(|j| *Real.exp (R/2)*(3*Real.exp (R/2)+16)+1)) ∧
      (|j| *|literalSizeBudget j c R K
          (KernelExpr.dr (KernelExpr.atom 0 0 false))|)*
        ((1+2*j)*(1+(1+(K+3*j)/c)*(K+4*j))*(2*ρ))≤(1:ℝ)/2 := by
  have small (a b : ℝ) (hb : 0<b) : ∀ᶠ ρ : ℝ in 𝓝[>] 0,a*(2*ρ)<b := by
    have H : Tendsto (fun ρ : ℝ => a*(2*ρ)) (𝓝[>] 0) (𝓝 (0:ℝ)) := by
      have C : ContinuousAt (fun ρ : ℝ => a*(2*ρ)) 0 := by fun_prop
      simpa using C.tendsto.mono_left nhdsWithin_le_nhds
    exact H.eventually_lt_const hb
  let q := (1+2*j)*(1+(1+(K+3*j)/c)*(K+4*j))
  let d := c/(2*(|j| *Real.exp (R/2)*(3*Real.exp (R/2)+16)+1))
  have hd : 0<d := by dsimp [d]; positivity
  let z := |j| *|literalSizeBudget j c R K
    (KernelExpr.dr (KernelExpr.atom 0 0 false))|
  have hp : ∀ᶠ ρ : ℝ in 𝓝[>] 0,0<ρ := self_mem_nhdsWithin
  have H : ∀ᶠ ρ : ℝ in 𝓝[>] 0, 0<ρ ∧ (K+4*j)*(2*ρ) < r₀ ∧
      q*(2*ρ)<R ∧ (3*Real.exp (R/2)+2)*(q*(2*ρ))<ε ∧
      q*(2*ρ)<d ∧ z*(q*(2*ρ))<(1:ℝ)/2 := by
    filter_upwards [hp,small (K+4*j) r₀ hr₀,small q R hR,
      small ((3*Real.exp (R/2)+2)*q) ε hε,small q d hd,
      small (z*q) ((1:ℝ)/2) (by norm_num)] with ρ hp h1 h2 h3 h4 h5
    exact ⟨hp,h1,h2,by simpa only [mul_assoc] using h3,h4,
      by simpa only [mul_assoc] using h5⟩
  obtain ⟨ρ,hp,h1,h2,h3,h4,h5⟩:=H.exists
  exact ⟨ρ,hp,h1,h2.le,h3.le,h4.le,h5.le⟩

theorem posterior_selection_parameters {ρ : ℝ} (hρ : 0<ρ) :
    ∃ m : ℕ, 0 < m ∧ ∃ δ : ℝ, 0 < δ ∧ 2 <(m:ℝ)*ρ^2/4 ∧
      2*(2*m:ℕ)*δ≤1 := by
  obtain ⟨m,hm⟩:=exists_nat_gt ((8:ℝ)/ρ^2)
  have hp : 0<(m:ℝ) := lt_trans (div_pos (by norm_num) (sq_pos_of_pos hρ)) hm
  have hd : 0<4*(m:ℝ)+1 := by positivity
  have hmul : 8<(m:ℝ)*ρ^2 := (div_lt_iff₀ (sq_pos_of_pos hρ)).mp hm
  refine ⟨m,by exact_mod_cast hp,(4*(m:ℝ)+1)⁻¹,inv_pos.mpr hd,by nlinarith,?_⟩
  have H : 4*(m:ℝ)/(4*(m:ℝ)+1)≤1 := by
    apply (div_le_iff₀ hd).mpr
    linarith
  simpa only [Nat.cast_mul,Nat.cast_ofNat,div_eq_mul_inv,show (2:ℝ)*(2*(m:ℝ))=4*m by ring] using H

end SKGapCutoff.Recipe

end
end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Posterior_QuenchedPosterior
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SKGap.FullMain
open MeasureTheory ProbabilityTheory Filter Set Real
open scoped Topology BigOperators
open SKGapCutoff SKGapCutoff.Recipe SKGapCutoff.Primary SKGapCutoff.Static
noncomputable section

lemma recipe_increase_diagnostics {n M N : ℕ} {j K A B W C W' C' : ℝ}
    {J : Interaction n} (H : RecipeMatrixEvent j K A B W C M N J)
    (hW : W≤W') (hC : C≤C') : RecipeMatrixEvent j K A B W' C' M N J := by
  exact ⟨H.1,H.2.1,fun w hl hw=>(H.2.2.1 w hl hw).trans hW,
    fun w hl hw=>(H.2.2.2 w hl hw).trans hC⟩

lemma started_replace_shapes {n M N : ℕ} {j K A₀ A c B B' W C W' C' : ℝ}
    {J : Interaction n} (H : StartedMatrixEvent j K A₀ A c B W C M N J)
    (hf : ∀h x l,l<M→ShapeBound (formalField j J h x l) B')
    (hW : W≤W') (hC : C≤C') : StartedMatrixEvent j K A₀ A c B' W' C' M N J := by
  refine ⟨H.1,hf,?_⟩
  intro a ha hc
  have ht:=H.2.2 a ha hc
  exact ⟨fun w hl hi hw=>(ht.1 w hl hi hw).trans hW,fun w hl hi hw=>(ht.2 w hl hi hw).trans hC⟩

theorem quenched_posterior_covariance_oai {β Aroot ε c r₀ : ℝ}
    (hβ : 0<β) (hβ1 : β<1) (hAroot : 1<Aroot) (hs : β*Aroot<1)
    (hε : 0<ε) (hc : 0 < c) (hr₀ : 0 < r₀) :
    ∃D : ℝ,0≤D ∧ Whp β (fun n g=>PosteriorCovarianceProperty (n := n) (β^2) Aroot ε c r₀ D g) := by
  classical
  let j:=β^2
  let K:=physicalNormBound j
  let R:=2*log Aroot
  have hj : 0≤j:=sq_nonneg β
  have hK : 0≤K:=(physicalNormBound_pos j).le
  have hR : 0<R:=mul_pos (by norm_num) (log_pos hAroot)
  have hAR : exp (R/2)=Aroot:=by dsimp [R]; rw [mul_div_cancel_left₀ _ (by norm_num : (2:ℝ)≠0),exp_log (by linarith)]
  obtain ⟨ρ,hρ,h1,h2,h3,h4,h5⟩:=posterior_buffer_exists j K c r₀ R ε hc hr₀ hR hε
  obtain ⟨m,hm,δ,hδ,hdepth,hδm⟩:=posterior_selection_parameters hρ
  have hbudget : 1 ≤ residualCoefficientBudget j 2 (2*m) 0 :=
    (by norm_num : (1:ℝ)≤2).trans (residualCoefficientBudget_ge j (by norm_num) (2*m) 0)
  obtain ⟨B,W,C,hB,hW,hC,hevent⟩:=disorder_fixed_norm_recipe_probability hβ hβ1 hbudget (2*m+1) (2*(2*m))
  obtain ⟨A,hA,hbound⟩:=buffered_posterior_covariance.{0} hj hK hB hAroot.le hc hr₀ hρ hε.le hAR.le h1 h2 h3 h4 h5
  let r:=2*m-1
  have hex : ∀k:Fin r,∃Bk Wk Ck:ℝ,0≤Bk ∧ 0≤Wk ∧ 0<Ck ∧
      Whp β (fun n g=>StartedMatrixEvent j K Aroot (max Aroot (A k)) (c/2)
        Bk Wk Ck (k+3) (2+2*(k+1)) (coupling g)) := by
    intro k
    exact disorder_started_matrix_event hβ hβ1 (by linarith) (by simpa only [sqrt_sq hβ.le] using hs)
      (le_max_left _ _) ((hA k).trans (le_max_right _ _)) (half_pos hc) _ _
  choose Bk Wk Ck hBk hWk hCk hpk using hex
  let W':=W+∑k:Fin r,Wk k
  let C':=C+∑k:Fin r,Ck k
  have hW' : W≤W':=le_add_of_nonneg_right (Finset.sum_nonneg (fun k _=>hWk k))
  have hC' : C≤C':=le_add_of_nonneg_right (Finset.sum_nonneg (fun k _=>(hCk k).le))
  have hwk (k:Fin r) : Wk k≤W':=by
    have hsum:=Finset.single_le_sum (fun k _=>hWk k) (Finset.mem_univ k)
    dsimp [W']
    linarith
  have hck (k:Fin r) : Ck k≤C':=by
    have hsum:=Finset.single_le_sum (fun k _=>(hCk k).le) (Finset.mem_univ k)
    dsimp [C']
    linarith
  let P : ∀n,Disorder n→Prop:=fun n g=>
    RecipeMatrixEvent j K (residualCoefficientBudget j 2 (2*m) 0) B W C (2*m+1) (2*(2*m)) (coupling g) ∧
    ∀k:Fin r,StartedMatrixEvent j K Aroot (max Aroot (A k)) (c/2) (Bk k) (Wk k) (Ck k)
      (k+3) (2+2*(k+1)) (coupling g)
  have hP : Whp β P:=by
    have hh:=whp_finset Finset.univ
      (fun (k:Fin r) n g=>StartedMatrixEvent j K Aroot (max Aroot (A k)) (c/2) (Bk k) (Wk k) (Ck k)
        (k+3) (2+2*(k+1)) (coupling g)) (fun k _=>hpk k)
    simpa only [Finset.mem_univ,forall_true_left] using (show Whp β _ from hevent).and hh
  let Dim (n:ℕ) : Prop:=∀k < r,4*(residualDerivativeBudget j K B k+residualDerivativeBudget j K B (k+1))≤ρ*sqrt (n:ℝ)
  have hDim : ∀ᶠ n:ℕ in atTop,Dim n:=by
    have ht : Tendsto (fun n:ℕ=>ρ*sqrt (n:ℝ)) atTop atTop:=
      (tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop).const_mul_atTop hρ
    have hh : ∀k:Fin r,∀ᶠ n:ℕ in atTop,4*(residualDerivativeBudget j K B k+residualDerivativeBudget j K B (k+1))≤ρ*sqrt (n:ℝ):=
      fun k=>ht.eventually_ge_atTop _
    have hh':=Filter.eventually_all.mpr hh
    filter_upwards [hh'] with n hn
    exact fun k hk=>hn ⟨k,hk⟩
  let Ω:Type:={a:Σn,Disorder n × (Fin n→ℝ) // 0<a.1 ∧ P a.1 a.2.1 ∧
      ¬rootBad j Aroot ε c r₀ (coupling a.2.1) a.2.2 ∧ Dim a.1}
  obtain ⟨D,hD,hDall⟩:=hbound m δ hδ hdepth hδm W' C' (hW.trans hW') (hC.le.trans hC')
    Ω (fun a=>a.1.1) (fun a=>coupling a.1.2.1) (fun a=>a.1.2.2)
    (fun a=>a.2.1) (fun a=>by ext i k;exact coupling_symm a.1.2.1 k i)
    (fun a=>coupling_diag a.1.2.1)
    (fun a k hk=>by
      have ht:=(a.2.2.1.2 ⟨k,hk⟩).mono_budget (le_max_right Aroot (A k))
      have ht' : StartedMatrixEvent j K (exp (R/2)) (A k) (c/2) (Bk ⟨k,hk⟩) (Wk ⟨k,hk⟩) (Ck ⟨k,hk⟩) (k+3) (2+2*(k+1)) (coupling a.1.2.1) := by
        simpa only [hAR] using ht
      apply started_replace_shapes ht' _ (hwk ⟨k,hk⟩) (hck ⟨k,hk⟩)
      intro h x l hl
      exact a.2.2.1.1.2.1 h x l (by omega))
    (fun a=>recipe_increase_diagnostics a.2.2.1.1 hW' hC')
    (fun a=>a.2.2.2.1) (fun a=>a.2.2.2.2)
  refine ⟨D,hD,hP.mono ?_⟩
  filter_upwards [eventually_ge_atTop 1,hDim] with n hn hd
  intro g hg h hb f
  apply hDall ⟨⟨n,g,h⟩,?_⟩ f
  exact ⟨show 0<n from by omega,hg,hb,hd⟩

end
end SKGap.FullMain

end OAI
end

theorem solution : type_of% @OAI.SKGap.FullMain.quenched_posterior_covariance_oai := @OAI.SKGap.FullMain.quenched_posterior_covariance_oai
