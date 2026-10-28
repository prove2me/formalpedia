-- Prove2me | solution 1 for OAI.SKGap.generalTemplateMatrix_increments_s2
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T10:56:20.478061+00:00
-- url     : https://prove2.me/submissions/841d282e-c202-4b7b-8ea7-17f67727ca97

import Mathlib
import Definitions.Def_OAIQ072A000

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

variable {A : Type*} [NormedRing A] [NormedAlgebra ℝ A] [NormedAlgebra ℚ A] [CompleteSpace A]
  [StarRing A] [ContinuousStar A] [CStarRing A]

omit [CStarRing A] in
lemma exp_skew_unitary (a : A) (ha : star a = -a) (t : ℝ)
    [StarModule ℝ A] : exp (t • a) ∈ unitary A := by
  apply exp_mem_unitary_of_mem_skewAdjoint
  change star (t • a) = -(t • a)
  simp [ha]

lemma exp_skew_difference [StarModule ℝ A] (a b : A)
    (ha : star a = -a) (hb : star b = -b) : ‖exp a - exp b‖ ≤ ‖a-b‖ := by
  rw [exp_duhamel]
  have hc : Continuous (fun u : ℝ => exp ((1-u) • a) * (a-b) * exp (u • b)) := by fun_prop
  have hh : ∀ u : ℝ, ‖exp ((1-u) • a) * (a-b) * exp (u • b)‖ = ‖a-b‖ := by
    intro u
    rw [CStarRing.norm_mul_coe_unitary _ ⟨_,exp_skew_unitary b hb u⟩,
      CStarRing.norm_coe_unitary_mul ⟨_,exp_skew_unitary a ha (1-u)⟩]
  calc
    ‖∫ u : ℝ in (0 : ℝ)..1, exp ((1-u) • a) * (a-b) * exp (u • b)‖ ≤
        ∫ u : ℝ in (0 : ℝ)..1, ‖exp ((1-u) • a) * (a-b) * exp (u • b)‖ :=
      intervalIntegral.norm_integral_le_integral_norm (by norm_num)
    _ = ‖a-b‖ := by simp only [hh]; simp

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

namespace SKGap.ComplexMatrix
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma lin_exp (M : Matrix ι ι ℂ) : lin (NormedSpace.exp M) = NormedSpace.exp (lin M) :=
  NormedSpace.map_exp linHom continuous_lin M

end SKGap.ComplexMatrix

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

lemma lin_sub (M N : Matrix ι ι ℂ) : lin (M-N) = lin M - lin N := linEquiv.map_sub M N
lemma lin_neg (M : Matrix ι ι ℂ) : lin (-M) = - lin M := linEquiv.map_neg M
lemma opNorm_smul (t : ℝ) (M : Matrix ι ι ℂ) : opNorm (t • M) = |t| * opNorm M := by
  change ‖lin (t • M)‖ = _
  have hh : lin (t • M) = t • lin M := by ext x i; simp [lin,Matrix.toEuclideanLin,Matrix.toLpLin_apply,Matrix.smul_mulVec]
  rw [hh,norm_smul,Real.norm_eq_abs]
  rfl

lemma unitary_exp_smul (M : Matrix ι ι ℂ) (hM : Mᴴ = -M) (u : ℝ) :
    exp (u • M) ∈ unitary (Matrix ι ι ℂ) := by
  apply exp_mem_unitary_of_mem_skewAdjoint
  change (u • M)ᴴ = -(u • M)
  simp [hM]

lemma opNorm_exp_sub (M N : Matrix ι ι ℂ) (hM : Mᴴ = -M) (hN : Nᴴ = -N) :
    opNorm (exp M-exp N) ≤ opNorm (M-N) := by
  have hMl : star (lin M) = -lin M := by rw [ContinuousLinearMap.star_eq_adjoint,← lin_adjoint,hM,lin_neg]
  have hNl : star (lin N) = -lin N := by rw [ContinuousLinearMap.star_eq_adjoint,← lin_adjoint,hN,lin_neg]
  let : NormedAlgebra ℚ (EuclideanSpace ℂ ι →L[ℂ] EuclideanSpace ℂ ι) := .restrictScalars ℚ ℝ _
  let : CompleteSpace (EuclideanSpace ℂ ι →L[ℂ] EuclideanSpace ℂ ι) :=
    ContinuousLinearMap.instCompleteSpace
  have hh := SKGap.exp_skew_difference (lin M) (lin N) hMl hNl
  simpa only [opNorm,lin_sub,lin_exp] using hh

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

lemma exp_four_point (a b c d : Matrix ι ι ℂ)
    (ha : aᴴ = -a) (hb : bᴴ = -b) (hc : cᴴ = -c) (hd : dᴴ = -d) :
    ‖(exp a-exp b)-(exp c-exp d)‖ ≤
      ‖(a-b)-(c-d)‖ + (opNorm (a-c)+opNorm (b-d))*‖c-d‖ := by
  let F := fun a b : Matrix ι ι ℂ => fun u : ℝ => exp ((1-u) • a) * (a-b) * exp (u • b)
  have hF (a b : Matrix ι ι ℂ) : Continuous (F a b) := by dsimp [F]; fun_prop
  have hbound (u : ℝ) (hu : u ∈ Icc (0 : ℝ) 1) :
      ‖F a b u-F c d u‖ ≤ ‖(a-b)-(c-d)‖ + (opNorm (a-c)+opNorm (b-d))*‖c-d‖ := by
    have hsa : ((1-u) • a)ᴴ = -((1-u) • a) := by simp [ha]
    have hsc : ((1-u) • c)ᴴ = -((1-u) • c) := by simp [hc]
    have hsb : (u • b)ᴴ = -(u • b) := by simp [hb]
    have hsd : (u • d)ᴴ = -(u • d) := by simp [hd]
    have h₁ := opNorm_exp_sub ((1-u) • a) ((1-u) • c) hsa hsc
    have h₂ := opNorm_exp_sub (u • b) (u • d) hsb hsd
    rw [← smul_sub,opNorm_smul,abs_of_nonneg (sub_nonneg.mpr hu.2)] at h₁
    rw [← smul_sub,opNorm_smul,abs_of_nonneg hu.1] at h₂
    have ha0 : 0 ≤ opNorm (a-c) := norm_nonneg _
    have hb0 : 0 ≤ opNorm (b-d) := norm_nonneg _
    have h₁' : opNorm (exp ((1-u) • a)-exp ((1-u) • c)) ≤ opNorm (a-c) := by nlinarith [hu.1]
    have h₂' : opNorm (exp (u • b)-exp (u • d)) ≤ opNorm (b-d) := by nlinarith [hu.2]
    have hid : F a b u-F c d u =
        exp ((1-u) • a)*((a-b)-(c-d))*exp (u • b) +
        (exp ((1-u) • a)-exp ((1-u) • c))*(c-d)*exp (u • b) +
        exp ((1-u) • c)*(c-d)*(exp (u • b)-exp (u • d)) := by dsimp [F]; noncomm_ring
    rw [hid]
    have hfirst : ‖exp ((1-u) • a)*((a-b)-(c-d))*exp (u • b)‖ = ‖(a-b)-(c-d)‖ := by
      rw [frobenius_mul_unitary _ _ (unitary_exp_smul b hb u),
        frobenius_unitary_mul _ _ (unitary_exp_smul a ha (1-u))]
    have hsecond : ‖(exp ((1-u) • a)-exp ((1-u) • c))*(c-d)*exp (u • b)‖ ≤ opNorm (a-c)*‖c-d‖ := by
      rw [frobenius_mul_unitary _ _ (unitary_exp_smul b hb u)]
      exact (frobenius_mul_le_opNorm _ _).trans (mul_le_mul_of_nonneg_right h₁' (norm_nonneg _))
    have hthird : ‖exp ((1-u) • c)*(c-d)*(exp (u • b)-exp (u • d))‖ ≤ opNorm (b-d)*‖c-d‖ := by
      rw [mul_assoc,frobenius_unitary_mul _ _ (unitary_exp_smul c hc (1-u))]
      exact (frobenius_mul_le_opNorm_right _ _).trans (by nlinarith [norm_nonneg (c-d)])
    calc
      _ ≤ ‖exp ((1-u) • a)*((a-b)-(c-d))*exp (u • b)‖ +
        ‖(exp ((1-u) • a)-exp ((1-u) • c))*(c-d)*exp (u • b)‖ +
        ‖exp ((1-u) • c)*(c-d)*(exp (u • b)-exp (u • d))‖ := norm_add₃_le
      _ ≤ _ := by rw [hfirst]; nlinarith
  rw [show exp a-exp b = _ from SKGap.exp_duhamel a b, show exp c-exp d = _ from SKGap.exp_duhamel c d]
  change ‖(∫ u : ℝ in (0 : ℝ)..1, F a b u)-(∫ u : ℝ in (0 : ℝ)..1, F c d u)‖ ≤ _
  rw [← intervalIntegral.integral_sub ((hF a b).intervalIntegrable 0 1) ((hF c d).intervalIntegrable 0 1)]
  calc
    _ ≤ ∫ u : ℝ in (0 : ℝ)..1, ‖F a b u-F c d u‖ := intervalIntegral.norm_integral_le_integral_norm (by norm_num)
    _ ≤ ∫ _ : ℝ in (0 : ℝ)..1, ‖(a-b)-(c-d)‖ + (opNorm (a-c)+opNorm (b-d))*‖c-d‖ := by
      apply intervalIntegral.integral_mono_on (by norm_num) (((hF a b).sub (hF c d)).norm.intervalIntegrable 0 1)
        (intervalIntegrable_const)
      exact hbound
    _ = _ := by simp

end

open MeasureTheory Set NormedSpace
open scoped Topology FourierTransform SchwartzMap
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

local instance instPseudoMetrizableSpaceMatrixComplex_solutions : TopologicalSpace.PseudoMetrizableSpace (Matrix ι ι ℂ) :=
  inferInstanceAs (TopologicalSpace.PseudoMetrizableSpace (ι → ι → ℂ))

lemma lin_csmul (z : ℂ) (M : Matrix ι ι ℂ) : lin (z • M) = z • lin M :=
  (linEquiv (ι := ι)).map_smul z M

lemma opNorm_csmul (z : ℂ) (M : Matrix ι ι ℂ) : opNorm (z • M) = ‖z‖ * opNorm M := by
  simp only [opNorm,lin_csmul,norm_smul]

omit [Fintype ι] [DecidableEq ι] in
lemma imaginary_skew (t : ℝ) (M : Matrix ι ι ℂ) (hM : Mᴴ = M) :
    (imaginary t M)ᴴ = -(imaginary t M) := by
  simp [imaginary,Matrix.conjTranspose_smul,hM,star_mul,mul_comm]

lemma imaginary_norm (t : ℝ) (M : Matrix ι ι ℂ) : ‖imaginary t M‖ = |t| * ‖M‖ := by
  simp [imaginary,norm_smul]

lemma imaginary_opNorm (t : ℝ) (M : Matrix ι ι ℂ) : opNorm (imaginary t M) = |t| * opNorm M := by
  simp [imaginary,opNorm_csmul]

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

lemma kernelMatrix_four_point {g : ℝ → ℂ} (hg : Integrable g)
    (hg₁ : Integrable (fun t : ℝ => ‖g t‖*|t|))
    (hg₂ : Integrable (fun t : ℝ => ‖g t‖*|t|^2))
    (a b c d : Matrix ι ι ℂ) (ha : aᴴ = a) (hb : bᴴ = b) (hc : cᴴ = c) (hd : dᴴ = d) :
    ‖(kernelMatrix g a-kernelMatrix g b)-(kernelMatrix g c-kernelMatrix g d)‖ ≤
      (∫ t : ℝ, ‖g t‖*|t|)*‖(a-b)-(c-d)‖ +
      (∫ t : ℝ, ‖g t‖*|t|^2)*(opNorm (a-c)+opNorm (b-d))*‖c-d‖ := by
  let F := fun (M : Matrix ι ι ℂ) (t : ℝ) => g t • exp (imaginary t M)
  have hi (M : Matrix ι ι ℂ) (hM : Mᴴ = M) : Integrable (F M) := kernel_integrable hg M hM
  have hi' := ((hi a ha).sub (hi b hb)).sub ((hi c hc).sub (hi d hd))
  change ‖((∫ t, F a t)-(∫ t, F b t))-((∫ t, F c t)-(∫ t, F d t))‖ ≤ _
  rw [← integral_sub (hi a ha) (hi b hb),← integral_sub (hi c hc) (hi d hd),
    ← integral_sub (f := fun t => F a t-F b t) (g := fun t => F c t-F d t)
      ((hi a ha).sub (hi b hb)) ((hi c hc).sub (hi d hd))]
  calc
    _ ≤ ∫ t : ℝ, ‖(F a t-F b t)-(F c t-F d t)‖ := norm_integral_le_integral_norm _
    _ ≤ ∫ t : ℝ, (‖g t‖*|t|)*‖(a-b)-(c-d)‖ +
        (‖g t‖*|t|^2)*(opNorm (a-c)+opNorm (b-d))*‖c-d‖ := by
      apply integral_mono hi'.norm ((hg₁.mul_const _).add ((hg₂.mul_const _).mul_const _))
      intro t
      dsimp only [F,Pi.sub_apply]
      rw [← smul_sub,← smul_sub,← smul_sub,norm_smul]
      have hh := exp_four_point (imaginary t a) (imaginary t b) (imaginary t c) (imaginary t d)
        (imaginary_skew t a ha) (imaginary_skew t b hb) (imaginary_skew t c hc) (imaginary_skew t d hd)
      simp only [← imaginary_sub,imaginary_norm,imaginary_opNorm] at hh
      exact (mul_le_mul_of_nonneg_left hh (norm_nonneg _)).trans_eq (by dsimp only [Pi.add_apply]; ring)
    _ = _ := by rw [integral_add (hg₁.mul_const _) ((hg₂.mul_const _).mul_const _)]; simp only [integral_mul_const]

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

lemma opNorm_rsmul (r : ℝ) (M : Matrix ι ι ℂ) : opNorm (r • M) = |r| * opNorm M := by
  change opNorm ((r:ℂ) • M) = _
  rw [opNorm_csmul,Complex.norm_real,Real.norm_eq_abs]

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

lemma schwartzMatrix_four_point (f : 𝓢(ℝ,ℂ)) (a b c d : Matrix ι ι ℂ)
    (ha : aᴴ = a) (hb : bᴴ = b) (hc : cᴴ = c) (hd : dᴴ = d) :
    ‖(schwartzMatrix f a-schwartzMatrix f b)-(schwartzMatrix f c-schwartzMatrix f d)‖ ≤
      (2*Real.pi*fourierMoment f 1)*‖(a-b)-(c-d)‖ +
      ((2*Real.pi)^2*fourierMoment f 2)*(opNorm (a-c)+opNorm (b-d))*‖c-d‖ := by
  have hf₁ : Integrable (fun t : ℝ => ‖(𝓕 f) t‖*|t|) := by
    simpa only [pow_one] using fourierMoment_integrable f 1
  have hh := kernelMatrix_four_point (𝓕 f).integrable hf₁ (fourierMoment_integrable f 2)
    ((2*Real.pi:ℝ) • a) ((2*Real.pi:ℝ) • b) ((2*Real.pi:ℝ) • c) ((2*Real.pi:ℝ) • d)
    (by simp [ha]) (by simp [hb]) (by simp [hc]) (by simp [hd])
  simp only [← smul_sub,norm_smul,opNorm_rsmul,Real.norm_eq_abs,
    abs_of_pos (by positivity : 0 < (2*Real.pi:ℝ))] at hh
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

section
open MeasureTheory NormedSpace
open scoped FourierTransform SchwartzMap
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

attribute [local instance] OAI.SKGap.ComplexMatrix.instContinuousENormMatrixComplex_solutions_3
local instance instPseudoMetrizableSpaceMatrixComplex_solutions_3_rf6779d_1 : TopologicalSpace.PseudoMetrizableSpace (Matrix ι ι ℂ) :=
  inferInstanceAs (TopologicalSpace.PseudoMetrizableSpace (ι → ι → ℂ))
lemma opNorm_kernelMatrix_sub {g : ℝ → ℂ} (hg : Integrable g)
    (hg₁ : Integrable (fun t : ℝ => ‖g t‖*|t|))
    (M N : Matrix ι ι ℂ) (hM : Mᴴ = M) (hN : Nᴴ = N) :
    opNorm (kernelMatrix g M-kernelMatrix g N) ≤
      (∫ t : ℝ, ‖g t‖*|t|)*opNorm (M-N) := by
  let F := fun t : ℝ => g t • exp (imaginary t M)-g t • exp (imaginary t N)
  have hi : Integrable F := (kernel_integrable hg M hM).sub (kernel_integrable hg N hN)
  let : CompleteSpace (EuclideanSpace ℂ ι →L[ℂ] EuclideanSpace ℂ ι) :=
    ContinuousLinearMap.instCompleteSpace
  have hh := linCLM.integral_comp_comm hi
  have he : kernelMatrix g M-kernelMatrix g N = ∫ t : ℝ, F t := by
    exact (integral_sub (kernel_integrable hg M hM) (kernel_integrable hg N hN)).symm
  rw [he]
  change ‖linCLM (∫ t : ℝ, F t)‖ ≤ _
  calc
    _ = ‖∫ t : ℝ, linCLM (F t)‖ := congrArg norm hh.symm
    _ ≤ ∫ t : ℝ, ‖linCLM (F t)‖ := norm_integral_le_integral_norm _
    _ ≤ ∫ t : ℝ, (‖g t‖*|t|)*opNorm (M-N) := by
      apply integral_mono (linCLM.integrable_comp hi).norm (hg₁.mul_const _)
      intro t
      have hb := opNorm_exp_sub (imaginary t M) (imaginary t N) (imaginary_skew t M hM) (imaginary_skew t N hN)
      rw [← imaginary_sub,imaginary_opNorm] at hb
      change opNorm (F t) ≤ _
      dsimp only [F]
      rw [← smul_sub,opNorm_csmul]
      exact (mul_le_mul_of_nonneg_left hb (norm_nonneg _)).trans_eq (by ring)
    _ = _ := integral_mul_const _ _

lemma schwartzMatrix_opNorm_lipschitz (f : 𝓢(ℝ,ℂ)) (M N : Matrix ι ι ℂ)
    (hM : Mᴴ = M) (hN : Nᴴ = N) :
    opNorm (schwartzMatrix f M-schwartzMatrix f N) ≤
      (2*Real.pi*fourierMoment f 1)*opNorm (M-N) := by
  have hf₁ : Integrable (fun t : ℝ => ‖(𝓕 f) t‖*|t|) := by
    simpa only [pow_one] using fourierMoment_integrable f 1
  have hh := opNorm_kernelMatrix_sub (𝓕 f).integrable hf₁
    ((2*Real.pi:ℝ) • M) ((2*Real.pi:ℝ) • N) (by simp [hM]) (by simp [hN])
  rw [← smul_sub,opNorm_smul,abs_of_pos (by positivity : 0 < (2*Real.pi:ℝ))] at hh
  exact hh.trans_eq (by simp only [fourierMoment,pow_one]; ring)

end

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
lemma opNorm_neg (M : Matrix ι ι ℂ) : opNorm (-M) = opNorm M := by
  change ‖lin (-M)‖ = _
  have hh : lin (-M) = -lin M := linEquiv.map_neg M
  rw [hh,norm_neg]
  rfl
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

lemma sandwich_difference_frobenius (D D' E : Matrix ι ι ℂ) :
    ‖D*E*D-D'*E*D'‖ ≤ (opNorm D+opNorm D')*opNorm (D-D')*‖E‖ := by
  have he : D*E*D-D'*E*D' = (D-D')*E*D+D'*E*(D-D') := by noncomm_ring
  rw [he]
  calc
    _ ≤ ‖(D-D')*E*D‖+‖D'*E*(D-D')‖ := norm_add_le _ _
    _ ≤ (opNorm (D-D')*‖E‖)*opNorm D+(opNorm D'*‖E‖)*opNorm (D-D') := by
      apply add_le_add
      · exact (frobenius_mul_le_opNorm_right _ _).trans
          (mul_le_mul_of_nonneg_right (frobenius_mul_le_opNorm _ _) (opNorm_nonneg _))
      · exact (frobenius_mul_le_opNorm_right _ _).trans
          (mul_le_mul_of_nonneg_right (frobenius_mul_le_opNorm _ _) (opNorm_nonneg _))
    _ = _ := by ring

lemma sandwich_difference_opNorm (D D' E : Matrix ι ι ℂ) :
    opNorm (D*E*D-D'*E*D') ≤ (opNorm D+opNorm D')*opNorm (D-D')*opNorm E := by
  have he : D*E*D-D'*E*D' = (D-D')*E*D+D'*E*(D-D') := by noncomm_ring
  rw [he]
  calc
    _ ≤ opNorm ((D-D')*E*D)+opNorm (D'*E*(D-D')) := opNorm_add _ _
    _ ≤ (opNorm (D-D')*opNorm E)*opNorm D+(opNorm D'*opNorm E)*opNorm (D-D') := by
      apply add_le_add
      · exact (opNorm_mul _ _).trans
          (mul_le_mul_of_nonneg_right (opNorm_mul _ _) (opNorm_nonneg _))
      · exact (opNorm_mul _ _).trans
          (mul_le_mul_of_nonneg_right (opNorm_mul _ _) (opNorm_nonneg _))
    _ = _ := by ring

lemma product_four_point (a b c d e f g h : Matrix ι ι ℂ) :
    ‖(a*e-b*f)-(c*g-d*h)‖ ≤
      ‖(a-b)-(c-d)‖*opNorm e + ‖c-d‖*opNorm (e-g) +
      opNorm (b-d)*‖e-f‖ + opNorm d*‖(e-f)-(g-h)‖ := by
  have he : (a*e-b*f)-(c*g-d*h) =
      ((a-b)-(c-d))*e+(c-d)*(e-g)+(b-d)*(e-f)+d*((e-f)-(g-h)) := by noncomm_ring
  rw [he]
  calc
    _ ≤ ‖((a-b)-(c-d))*e+(c-d)*(e-g)+(b-d)*(e-f)‖+‖d*((e-f)-(g-h))‖ := norm_add_le _ _
    _ ≤ (‖((a-b)-(c-d))*e+(c-d)*(e-g)‖+‖(b-d)*(e-f)‖)+‖d*((e-f)-(g-h))‖ := by gcongr; exact norm_add_le _ _
    _ ≤ ((‖((a-b)-(c-d))*e‖+‖(c-d)*(e-g)‖)+‖(b-d)*(e-f)‖)+‖d*((e-f)-(g-h))‖ := by gcongr; exact norm_add_le _ _
    _ ≤ _ := by
      gcongr
      · exact frobenius_mul_le_opNorm_right _ _
      · exact frobenius_mul_le_opNorm_right _ _
      · exact frobenius_mul_le_opNorm _ _
      · exact frobenius_mul_le_opNorm _ _

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

lemma sandShift_parameter (B B' D D' M : Matrix ι ι ℂ) :
    opNorm (sandShift B D M-sandShift B' D' M) ≤
      opNorm (B-B')+(opNorm D+opNorm D')*opNorm (D-D')*opNorm M := by
  have he : sandShift B D M-sandShift B' D' M = (B-B')-(D*M*D-D'*M*D') := by dsimp [sandShift]; abel
  rw [he]
  calc
    _ ≤ opNorm (B-B')+opNorm (D*M*D-D'*M*D') := opNorm_sub (B-B') (D*M*D-D'*M*D')
    _ ≤ _ := by
      have hh := sandwich_difference_opNorm D D' M
      linarith only [hh]

lemma sandShift_four_point (B B' D D' M N : Matrix ι ι ℂ) :
    ‖(sandShift B D M-sandShift B D N)-(sandShift B' D' M-sandShift B' D' N)‖ ≤
      (opNorm D+opNorm D')*opNorm (D-D')*‖M-N‖ := by
  rw [sandShift_sub,sandShift_sub,← norm_neg]
  have he : -(-(D*(M-N)*D)- -(D'*(M-N)*D')) = D*(M-N)*D-D'*(M-N)*D' := by abel
  rw [he]
  exact sandwich_difference_frobenius _ _ _

lemma schwartzMatrix_sandShift_lipschitz (f : 𝓢(ℝ,ℂ)) (B D M N : Matrix ι ι ℂ)
    (hB : Bᴴ = B) (hD : Dᴴ = D) (hM : Mᴴ = M) (hN : Nᴴ = N) :
    ‖schwartzMatrix f (sandShift B D M)-schwartzMatrix f (sandShift B D N)‖ ≤
      (2*Real.pi*fourierMoment f 1)*opNorm D^2*‖M-N‖ := by
  exact (schwartzMatrix_lipschitz f _ _ (sandShift_hermitian _ _ _ hB hD hM)
    (sandShift_hermitian _ _ _ hB hD hN)).trans
    ((mul_le_mul_of_nonneg_left (sandShift_lipschitz B D M N)
      (by positivity [fourierMoment_nonneg f 1])).trans_eq (by ring))

lemma schwartzMatrix_sandShift_four_point (f : 𝓢(ℝ,ℂ)) (B B' D D' M N : Matrix ι ι ℂ)
    (hB : Bᴴ = B) (hB' : B'ᴴ = B') (hD : Dᴴ = D) (hD' : D'ᴴ = D')
    (hM : Mᴴ = M) (hN : Nᴴ = N) :
    ‖(schwartzMatrix f (sandShift B D M)-schwartzMatrix f (sandShift B D N))-
      (schwartzMatrix f (sandShift B' D' M)-schwartzMatrix f (sandShift B' D' N))‖ ≤
      ((2*Real.pi*fourierMoment f 1)*(opNorm D+opNorm D')*opNorm (D-D')+
        ((2*Real.pi)^2*fourierMoment f 2)*
          (2*opNorm (B-B')+(opNorm D+opNorm D')*opNorm (D-D')*(opNorm M+opNorm N))*opNorm D'^2)*‖M-N‖ := by
  have hL : 0 ≤ 2*Real.pi*fourierMoment f 1 := by have := fourierMoment_nonneg f 1; positivity
  have hQ : 0 ≤ (2*Real.pi)^2*fourierMoment f 2 := by have := fourierMoment_nonneg f 2; positivity
  have hP : 0 ≤ (opNorm D+opNorm D')*opNorm (D-D') :=
    mul_nonneg (add_nonneg (opNorm_nonneg _) (opNorm_nonneg _)) (opNorm_nonneg _)
  have hp := add_le_add (sandShift_parameter B B' D D' M) (sandShift_parameter B B' D D' N)
  have hp' : opNorm (sandShift B D M-sandShift B' D' M)+opNorm (sandShift B D N-sandShift B' D' N) ≤
      2*opNorm (B-B')+(opNorm D+opNorm D')*opNorm (D-D')*(opNorm M+opNorm N) := by nlinarith only [hp]
  have hx := schwartzMatrix_four_point f (sandShift B D M) (sandShift B D N) (sandShift B' D' M) (sandShift B' D' N)
    (sandShift_hermitian _ _ _ hB hD hM) (sandShift_hermitian _ _ _ hB hD hN)
    (sandShift_hermitian _ _ _ hB' hD' hM) (sandShift_hermitian _ _ _ hB' hD' hN)
  apply hx.trans
  calc
    _ ≤ (2*Real.pi*fourierMoment f 1)*((opNorm D+opNorm D')*opNorm (D-D')*‖M-N‖)+
      ((2*Real.pi)^2*fourierMoment f 2)*
        (2*opNorm (B-B')+(opNorm D+opNorm D')*opNorm (D-D')*(opNorm M+opNorm N))*(opNorm D'^2*‖M-N‖) := by
      apply add_le_add
      · exact mul_le_mul_of_nonneg_left (sandShift_four_point _ _ _ _ _ _) hL
      · apply mul_le_mul (mul_le_mul_of_nonneg_left hp' hQ) (sandShift_lipschitz B' D' M N) (norm_nonneg _)
        exact mul_nonneg hQ (add_nonneg (mul_nonneg (by norm_num) (opNorm_nonneg _))
          (mul_nonneg hP (add_nonneg (opNorm_nonneg _) (opNorm_nonneg _))))
    _ = _ := by ring

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

lemma truncatedG_parameter (f : 𝓢(ℝ,ℂ)) {R : ℝ} (hR : 0 ≤ R)
    (B B' D D' M : Matrix ι ι ℂ)
    (hB : Bᴴ = B) (hB' : B'ᴴ = B') (hD : Dᴴ = D) (hD' : D'ᴴ = D') :
    opNorm (truncatedG f R hR B D M-truncatedG f R hR B' D' M) ≤
      gChange f R B B' D D' := by
  let P := matrixProject R hR M
  let F := schwartzMatrix f (sandShift B D P)
  let F' := schwartzMatrix f (sandShift B' D' P)
  have hP := matrixProject_bound R hR M
  have hF : opNorm F ≤ fourierMoment f 0 := by
    simpa only [F,fourierMoment,pow_zero,mul_one] using
      schwartzMatrix_opNorm f _ (sandShift_hermitian _ _ _ hB hD hP.1)
  have hs : opNorm (sandShift B D P-sandShift B' D' P) ≤ shiftChange R B B' D D' := by
    apply (sandShift_parameter B B' D D' P).trans
    unfold shiftChange diagonalChange
    exact add_le_add_right (mul_le_mul_of_nonneg_left hP.2 (diagonalChange_nonneg D D')) _
  have hL : opNorm (F-F') ≤ fl1 f*shiftChange R B B' D D' :=
    (schwartzMatrix_opNorm_lipschitz f _ _ (sandShift_hermitian _ _ _ hB hD hP.1)
      (sandShift_hermitian _ _ _ hB' hD' hP.1)).trans
      (mul_le_mul_of_nonneg_left hs (fl_nonneg f).1)
  have he : truncatedG f R hR B D M-truncatedG f R hR B' D' M =
      (D*F*D-D'*F*D')+D'*(F-F')*D' := by dsimp [truncatedG,F,F',P]; noncomm_ring
  rw [he]
  calc
    _ ≤ opNorm (D*F*D-D'*F*D')+opNorm (D'*(F-F')*D') := opNorm_add _ _
    _ ≤ diagonalChange D D'*opNorm F+opNorm D'^2*opNorm (F-F') :=
      add_le_add (sandwich_difference_opNorm _ _ _) (sandwich_opNorm _ _)
    _ ≤ diagonalChange D D'*fourierMoment f 0+opNorm D'^2*(fl1 f*shiftChange R B B' D D') :=
      add_le_add (mul_le_mul_of_nonneg_left hF (diagonalChange_nonneg _ _))
        (mul_le_mul_of_nonneg_left hL (sq_nonneg _))
    _ = _ := by unfold gChange; ring

lemma truncatedG_four_point (f : 𝓢(ℝ,ℂ)) {R : ℝ} (hR : 0 ≤ R)
    (B B' D D' M N : Matrix ι ι ℂ)
    (hB : Bᴴ = B) (hB' : B'ᴴ = B') (hD : Dᴴ = D) (hD' : D'ᴴ = D') :
    ‖(truncatedG f R hR B D M-truncatedG f R hR B D N)-
      (truncatedG f R hR B' D' M-truncatedG f R hR B' D' N)‖ ≤
      gMixed f R B B' D D'*‖M-N‖ := by
  let P := matrixProject R hR M
  let Q := matrixProject R hR N
  let F := schwartzMatrix f (sandShift B D P)-schwartzMatrix f (sandShift B D Q)
  let F' := schwartzMatrix f (sandShift B' D' P)-schwartzMatrix f (sandShift B' D' Q)
  have hP := matrixProject_bound R hR M
  have hQ := matrixProject_bound R hR N
  have hPQ : ‖P-Q‖ ≤ ‖M-N‖ := matrixProject_sub_norm _ _ _ _
  have hF : ‖F‖ ≤ fl1 f*opNorm D^2*‖M-N‖ :=
    (schwartzMatrix_sandShift_lipschitz f B D P Q hB hD hP.1 hQ.1).trans
      (mul_le_mul_of_nonneg_left hPQ (mul_nonneg (fl_nonneg f).1 (sq_nonneg _)))
  have hFF : ‖F-F'‖ ≤
      (fl1 f*diagonalChange D D'+fl2 f*(2*shiftChange R B B' D D')*opNorm D'^2)*‖M-N‖ := by
    apply (schwartzMatrix_sandShift_four_point f B B' D D' P Q hB hB' hD hD' hP.1 hQ.1).trans
    simp only [mul_assoc (2*Real.pi*fourierMoment f 1) (opNorm D+opNorm D')]
    change (fl1 f*diagonalChange D D'+fl2 f*
      (2*opNorm (B-B')+diagonalChange D D'*(opNorm P+opNorm Q))*opNorm D'^2)*‖P-Q‖ ≤ _
    have hd := diagonalChange_nonneg D D'
    have hs := shiftChange_nonneg hR B B' D D'
    have hc : 2*opNorm (B-B')+diagonalChange D D'*(opNorm P+opNorm Q) ≤
        2*shiftChange R B B' D D' := by
      calc
        _ ≤ 2*opNorm (B-B')+diagonalChange D D'*(R+R) :=
          add_le_add_right (mul_le_mul_of_nonneg_left (add_le_add hP.2 hQ.2) hd) _
        _ = _ := by unfold shiftChange; ring
    have hc' := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hc (fl_nonneg f).2) (sq_nonneg (opNorm D'))
    have hcoef := add_le_add_right hc' (fl1 f*diagonalChange D D')
    have hn : 0 ≤ fl1 f*diagonalChange D D'+fl2 f*(2*shiftChange R B B' D D')*opNorm D'^2 :=
      add_nonneg (mul_nonneg (fl_nonneg f).1 hd)
        (mul_nonneg (mul_nonneg (fl_nonneg f).2 (mul_nonneg (by norm_num) hs)) (sq_nonneg _))
    exact mul_le_mul hcoef hPQ (norm_nonneg _) hn
  have he : (truncatedG f R hR B D M-truncatedG f R hR B D N)-
      (truncatedG f R hR B' D' M-truncatedG f R hR B' D' N) =
      (D*F*D-D'*F*D')+D'*(F-F')*D' := by dsimp [truncatedG,F,F',P,Q]; noncomm_ring
  rw [he]
  calc
    _ ≤ ‖D*F*D-D'*F*D'‖+‖D'*(F-F')*D'‖ := norm_add_le _ _
    _ ≤ diagonalChange D D'*‖F‖+opNorm D'^2*‖F-F'‖ :=
      add_le_add (sandwich_difference_frobenius _ _ _) (sandwich_frobenius _ _)
    _ ≤ diagonalChange D D'*(fl1 f*opNorm D^2*‖M-N‖)+opNorm D'^2*
        ((fl1 f*diagonalChange D D'+fl2 f*(2*shiftChange R B B' D D')*opNorm D'^2)*‖M-N‖) :=
      add_le_add (mul_le_mul_of_nonneg_left hF (diagonalChange_nonneg _ _))
        (mul_le_mul_of_nonneg_left hFF (sq_nonneg _))
    _ = _ := by unfold gMixed; ring

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

lemma truncatedK_four_point (f : 𝓢(ℝ,ℂ)) {R : ℝ} (hR : 0 ≤ R)
    (B B' D D' C C' M N : Matrix ι ι ℂ)
    (hB : Bᴴ = B) (hB' : B'ᴴ = B') (hD : Dᴴ = D) (hD' : D'ᴴ = D') :
    ‖(truncatedK f R hR B D C M-truncatedK f R hR B D C N)-
      (truncatedK f R hR B' D' C' M-truncatedK f R hR B' D' C' N)‖ ≤
      kMixed f R B B' D D' C C'*‖M-N‖ := by
  let G := truncatedG f R hR B D
  let G' := truncatedG f R hR B' D'
  let P : Matrix ι ι ℂ → Matrix ι ι ℂ := matrixProject R hR
  have he : (truncatedK f R hR B D C M-truncatedK f R hR B D C N)-
      (truncatedK f R hR B' D' C' M-truncatedK f R hR B' D' C' N) =
      (G M*(P M-C)-G N*(P N-C))-(G' M*(P M-C')-G' N*(P N-C')) := by
    dsimp [truncatedK,G,G',P]; abel
  rw [he]
  have h₁ : (P M-C)-(P M-C') = -(C-C') := by abel
  have h₂ : (P M-C)-(P N-C) = P M-P N := by abel
  have h₃ : ((P M-C)-(P N-C))-((P M-C')-(P N-C')) = 0 := by abel
  have hh := product_four_point (G M) (G N) (G' M) (G' N) (P M-C) (P N-C) (P M-C') (P N-C')
  rw [h₃,h₁,h₂,opNorm_neg,norm_zero,mul_zero,add_zero] at hh
  apply hh.trans
  calc
    _ ≤ (gMixed f R B B' D D'*‖M-N‖)*(R+opNorm C)+
        (gLip f D'*‖M-N‖)*opNorm (C-C')+gChange f R B B' D D'*‖M-N‖ := by
      apply add_le_add
      · apply add_le_add
        · exact mul_le_mul (truncatedG_four_point f hR B B' D D' M N hB hB' hD hD')
            (projected_sub_bound hR M C) (opNorm_nonneg _)
            (mul_nonneg (g_constants_nonneg f hR B B' D D').2.2.2 (norm_nonneg _))
        · exact mul_le_mul_of_nonneg_right (truncatedG_sub_norm _ _ _ _ _ _ _ hB' hD') (opNorm_nonneg _)
      · exact mul_le_mul (truncatedG_parameter f hR B B' D D' N hB hB' hD hD')
          (matrixProject_sub_norm _ _ _ _) (norm_nonneg _)
          (g_constants_nonneg f hR B B' D D').2.2.1
    _ = _ := by unfold kMixed; ring

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

lemma opNorm_sub (M N : Matrix ι ι ℝ) : opNorm (M-N) ≤ opNorm M+opNorm N := by
  change ‖Matrix.toEuclideanCLM (n := ι) (𝕜 := ℝ) (M-N)‖ ≤ _
  rw [map_sub]
  exact norm_sub_le _ _

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
-- module Solutions.OAIQ074_CM.SKGap_Localization_RealParameterIncrement
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open Matrix Real Set
open scoped Matrix.Norms.Frobenius SchwartzMap
namespace SKGap.ComplexMatrix
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
lemma truncatedK_parameter (f : 𝓢(ℝ,ℂ)) {R : ℝ} (hR : 0≤R)
    (B B' D D' C C' M : Matrix ι ι ℂ)
    (hB : Bᴴ=B) (hB' : B'ᴴ=B') (hD : Dᴴ=D) (hD' : D'ᴴ=D') :
    opNorm (truncatedK f R hR B D C M-truncatedK f R hR B' D' C' M)≤
      kChange f R B B' D D' C C' := by
  have he : truncatedK f R hR B D C M-truncatedK f R hR B' D' C' M=
    (truncatedG f R hR B D M-truncatedG f R hR B' D' M)*(matrixProject R hR M-C)+
      truncatedG f R hR B' D' M*(C'-C) := by unfold truncatedK;noncomm_ring
  rw [he]
  apply (opNorm_add _ _).trans
  apply (add_le_add (opNorm_mul _ _) (opNorm_mul _ _)).trans
  have h1 := mul_le_mul (truncatedG_parameter f hR B B' D D' M hB hB' hD hD')
    (projected_sub_bound hR M C) (opNorm_nonneg _) (g_constants_nonneg f hR B B' D D').2.2.1
  have h2 := mul_le_mul_of_nonneg_right (truncatedG_opNorm f R hR B' D' M hB' hD')
    (opNorm_nonneg (C'-C))
  have hs : opNorm (C'-C)=opNorm (C-C') := by rw [← neg_sub C C',opNorm_neg]
  rw [hs] at h2
  simpa only [kChange,hs,gBound] using add_le_add h1 h2
end SKGap.ComplexMatrix
namespace SKGap.RealComplex
open SKGap.ComplexMatrix
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
lemma liftedSand_hermitian (D C : Matrix ι ι ℝ) (hD : Dᵀ=D) (hC : Cᵀ=C) :
    (1+liftMatrix D*liftMatrix C*liftMatrix D)ᴴ=1+liftMatrix D*liftMatrix C*liftMatrix D := by
  simp [Matrix.conjTranspose_mul,liftMatrix_hermitian D hD,liftMatrix_hermitian C hC,mul_assoc]
lemma realTruncatedK_parameter (f : 𝓢(ℝ,ℂ)) {R : ℝ} (hR : 0≤R)
    (D D' C C' M : Matrix ι ι ℝ) (hD : Dᵀ=D) (hD' : D'ᵀ=D') (hC : Cᵀ=C) (hC' : C'ᵀ=C') :
    SKGap.opNorm (realTruncatedK f R hR D C M-realTruncatedK f R hR D' C' M)≤
      kChange f R (1+liftMatrix D*liftMatrix C*liftMatrix D)
        (1+liftMatrix D'*liftMatrix C'*liftMatrix D') (liftMatrix D) (liftMatrix D') (liftMatrix C) (liftMatrix C') := by
  unfold realTruncatedK
  rw [← realPart_sub]
  exact (operator_realPart_le _).trans (truncatedK_parameter f hR _ _ _ _ _ _ _
    (liftedSand_hermitian D C hD hC) (liftedSand_hermitian D' C' hD' hC')
    (liftMatrix_hermitian D hD) (liftMatrix_hermitian D' hD'))

lemma realTruncatedK_four_point (f : 𝓢(ℝ,ℂ)) {R : ℝ} (hR : 0≤R)
    (D D' C C' M N : Matrix ι ι ℝ) (hD : Dᵀ=D) (hD' : D'ᵀ=D') (hC : Cᵀ=C) (hC' : C'ᵀ=C') :
    ‖(realTruncatedK f R hR D C M-realTruncatedK f R hR D C N)-
      (realTruncatedK f R hR D' C' M-realTruncatedK f R hR D' C' N)‖≤
      kMixed f R (1+liftMatrix D*liftMatrix C*liftMatrix D)
        (1+liftMatrix D'*liftMatrix C'*liftMatrix D') (liftMatrix D) (liftMatrix D') (liftMatrix C) (liftMatrix C')*‖M-N‖ := by
  unfold realTruncatedK
  rw [← realPart_sub,← realPart_sub,← realPart_sub]
  apply (norm_realPart_le _).trans
  simpa only [← liftMatrix_sub,norm_liftMatrix] using! truncatedK_four_point f hR _ _ _ _ _ _
    (liftMatrix M) (liftMatrix N) (liftedSand_hermitian D C hD hC)
    (liftedSand_hermitian D' C' hD' hC') (liftMatrix_hermitian D hD) (liftMatrix_hermitian D' hD')
end SKGap.RealComplex
end
end

section
noncomputable section
namespace SKGap.ComplexMatrix
open Matrix Real
open scoped Matrix.Norms.Frobenius SchwartzMap
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem cutoff_parameter_constants (f : 𝓢(ℝ,ℂ))
    {R V T H δ : ℝ} (hR : 0≤R) (hV : 0≤V) (_hT : 0≤T) (hH : 0≤H) (hδ : 0≤δ)
    (B B' D D' C C' : Matrix ι ι ℂ)
    (hD : opNorm D≤V) (hD' : opNorm D'≤V) (hC : opNorm C≤T)
    (hBD : opNorm (B-B')≤H*δ) (hDD : opNorm (D-D')≤δ) (hCD : opNorm (C-C')≤δ) :
    kChange f R B B' D D' C C'≤parameterKC f R V T H*δ ∧
    kMixed f R B B' D D' C C'≤parameterKM f R V T H*δ := by
  have hf0 := fourierMoment_nonneg f 0
  obtain ⟨hf1,hf2⟩ := fl_nonneg f
  have hDC : diagonalChange D D'≤(2*V)*δ := by
    unfold diagonalChange
    exact mul_le_mul (by linarith) hDD (opNorm_nonneg _) (by positivity)
  have hSC : shiftChange R B B' D D'≤(H+2*V*R)*δ := by
    unfold shiftChange
    have hh := add_le_add hBD (mul_le_mul_of_nonneg_right hDC hR)
    nlinarith only [hh]
  have hGH : 0≤H+2*V*R := by positivity
  have hgc : gChange f R B B' D D'≤parameterGC f R V H*δ := by
    unfold gChange parameterGC
    calc
      _ ≤ ((2*V)*δ)*fourierMoment f 0+V^2*fl1 f*((H+2*V*R)*δ) := by
        apply add_le_add (mul_le_mul_of_nonneg_right hDC hf0)
        apply mul_le_mul _ hSC (shiftChange_nonneg hR _ _ _ _) (by positivity)
        exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (opNorm_nonneg D') hD' 2) hf1
      _ = _ := by ring
  have hgm : gMixed f R B B' D D'≤parameterGM f R V H*δ := by
    unfold gMixed parameterGM
    calc
      _ ≤ ((2*V)*δ)*fl1 f*V^2+V^2*(fl1 f*((2*V)*δ)+fl2 f*(2*((H+2*V*R)*δ))*V^2) := by
        apply add_le_add
        · apply mul_le_mul _ (pow_le_pow_left₀ (opNorm_nonneg D) hD 2) (by positivity [fl_nonneg f]) (by positivity)
          exact mul_le_mul_of_nonneg_right hDC hf1
        · apply mul_le_mul (pow_le_pow_left₀ (opNorm_nonneg D') hD' 2) _ (by positivity [diagonalChange_nonneg D D',shiftChange_nonneg hR B B' D D']) (by positivity)
          apply add_le_add (mul_le_mul_of_nonneg_left hDC hf1)
          apply mul_le_mul _ (pow_le_pow_left₀ (opNorm_nonneg D') hD' 2) (by positivity [opNorm_nonneg D']) (by positivity)
          exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hSC (by norm_num)) hf2
      _ = _ := by ring
  have hgc0 : 0≤parameterGC f R V H := by unfold parameterGC;positivity
  have hgm0 : 0≤parameterGM f R V H := by unfold parameterGM;positivity
  constructor
  · unfold kChange parameterKC
    calc
      _ ≤ (parameterGC f R V H*δ)*(R+T)+(V^2*fourierMoment f 0)*δ := by
        apply add_le_add
        · exact mul_le_mul hgc (add_le_add le_rfl hC) (by positivity [opNorm_nonneg C]) (by positivity)
        · exact mul_le_mul (mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (opNorm_nonneg D') hD' 2) hf0) hCD (opNorm_nonneg _) (by positivity)
      _ = _ := by ring
  · unfold kMixed parameterKM
    calc
      _ ≤ (parameterGM f R V H*δ)*(R+T)+(fl1 f*V^4)*δ+parameterGC f R V H*δ := by
        apply add_le_add _ hgc
        apply add_le_add
        · exact mul_le_mul hgm (add_le_add le_rfl hC) (by positivity [opNorm_nonneg C]) (by positivity)
        · exact mul_le_mul (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (opNorm_nonneg D') hD' 4) hf1) hCD (opNorm_nonneg _) (by positivity)
      _ = _ := by ring
end SKGap.ComplexMatrix
end
end

end OAI
end

section
-- module Solutions.OAIQ074_CM.SKGap_Brownian_PathParameter
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

lemma sqrt_parameter_holder {a b δ : ℝ} (ha : 0≤a) (hb : 0≤b) (hδ : 0≤δ)
    (hab : |a-b|≤δ) : |sqrt a-sqrt b|≤ sqrt δ := by
  have ha2 := sq_sqrt ha
  have hb2 := sq_sqrt hb
  have hd2 := sq_sqrt hδ
  rcases le_total a b with hab'|hba
  · have hxy := sqrt_le_sqrt hab'
    rw [abs_of_nonpos (sub_nonpos.mpr hxy)]
    have hmul := mul_le_mul_of_nonneg_left hxy (sqrt_nonneg a)
    have hbd : b-a≤δ := by linarith [neg_le_abs (a-b)]
    nlinarith [sqrt_nonneg a,sqrt_nonneg b,sqrt_nonneg δ]
  · have hxy := sqrt_le_sqrt hba
    rw [abs_of_nonneg (sub_nonneg.mpr hxy)]
    have hmul := mul_le_mul_of_nonneg_left hxy (sqrt_nonneg b)
    have had : a-b≤δ := (le_abs_self _).trans hab
    nlinarith [sqrt_nonneg a,sqrt_nonneg b,sqrt_nonneg δ]

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
lemma pathDiagonal_parameter {a b : ι→ℝ} {δ : ℝ} (ha : ∀ i,0≤a i) (hb : ∀ i,0≤b i)
    (hδ : 0≤δ) (hab : ∀ i,|a i-b i|≤δ) :
    opNorm (pathDiagonal a 1-pathDiagonal b 1)≤ sqrt δ := by
  simp only [pathDiagonal,sqrt_one,one_mul,diagonal_sub]
  exact opNorm_diagonal_le (sqrt_nonneg _) (fun i=>sqrt_parameter_holder (ha i) (hb i) hδ (hab i))

omit [DecidableEq ι] in
lemma mean_parameter [Nonempty ι] {a b : ι→ℝ} {j δ : ℝ} (hj : 0≤j) (_hδ : 0≤δ)
    (hab : ∀ i,|a i-b i|≤δ) :
    |(j/(Fintype.card ι:ℝ))*(∑ i,a i)-(j/(Fintype.card ι:ℝ))*(∑ i,b i)|≤j*δ := by
  have hn : (0:ℝ)<Fintype.card ι := Nat.cast_pos.mpr Fintype.card_pos
  rw [← mul_sub,← Finset.sum_sub_distrib,abs_mul,abs_of_nonneg (div_nonneg hj hn.le)]
  have hh : |∑ i,(a i-b i)|≤(Fintype.card ι:ℝ)*δ := by
    apply (Finset.abs_sum_le_sum_abs _ _).trans
    simpa only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul] using Finset.sum_le_sum (fun i (_ : i∈Finset.univ)=>hab i)
  apply (mul_le_mul_of_nonneg_left hh (div_nonneg hj hn.le)).trans_eq
  field_simp

lemma pathShift_parameter [Nonempty ι] {a b : ι→ℝ} {j δ : ℝ} (hj : 0≤j) (hδ : 0≤δ)
    (hab : ∀ i,|a i-b i|≤δ) :
    opNorm (pathShift (ι:=ι) 1 ((j/(Fintype.card ι:ℝ))*∑ i,a i)-
      pathShift 1 ((j/(Fintype.card ι:ℝ))*∑ i,b i))≤j*δ := by
  simp only [pathShift,one_mul,diagonal_sub]
  exact opNorm_diagonal_le (mul_nonneg hj hδ) (fun _=>mean_parameter hj hδ hab)
end SKGap
namespace SKGap.ComplexMatrix
open Matrix Real
open scoped Matrix.Norms.Frobenius SchwartzMap
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
lemma spectralShift_difference (D D' C C' : Matrix ι ι ℂ) : (1+D*C*D)-(1+D'*C'*D')=(D-D')*C*D+D'*(C-C')*D+D'*C'*(D-D') := by noncomm_ring

lemma complex_product_bound (M N : Matrix ι ι ℂ) {x y : ℝ} (hx : 0≤x)
    (hM : opNorm M≤x) (hN : opNorm N≤y) : opNorm (M*N)≤x*y :=
  (opNorm_mul M N).trans (mul_le_mul hM hN (opNorm_nonneg N) hx)

lemma complex_triple_bound (M N P : Matrix ι ι ℂ) {x y z : ℝ}
    (hx : 0≤x) (hy : 0≤y) (hM : opNorm M≤x) (hN : opNorm N≤y) (hP : opNorm P≤z) :
    opNorm (M*N*P)≤x*y*z :=
  complex_product_bound (M*N) P (mul_nonneg hx hy) (complex_product_bound M N hx hM hN) hP

lemma complex_sum_three_bound (M N P : Matrix ι ι ℂ) :
    opNorm (M+N+P)≤opNorm M+opNorm N+opNorm P :=
  (opNorm_add (M+N) P).trans (add_le_add (opNorm_add M N) le_rfl)

lemma spectralShift_parameter (D D' C C' : Matrix ι ι ℂ) {V T δ : ℝ}
    (hV : 0≤V) (hT : 0≤T) (hδ : 0≤δ)
    (hD : opNorm D≤V) (hD' : opNorm D'≤V) (hC : opNorm C≤T) (hC' : opNorm C'≤T)
    (hDD : opNorm (D-D')≤δ) (hCD : opNorm (C-C')≤δ) :
    opNorm ((1+D*C*D)-(1+D'*C'*D'))≤(2*V*T+V^2)*δ := by
  rw [spectralShift_difference]
  have h1 := complex_triple_bound (D-D') C D hδ hT hDD hC hD
  have h2 := complex_triple_bound D' (C-C') D hV hδ hD' hCD hD
  have h3 := complex_triple_bound D' C' (D-D') hV hT hD' hC' hDD
  calc
    _ ≤ opNorm ((D-D')*C*D)+opNorm (D'*(C-C')*D)+opNorm (D'*C'*(D-D')) := complex_sum_three_bound _ _ _
    _ ≤ δ*T*V+V*δ*V+V*T*δ := add_le_add (add_le_add h1 h2) h3
    _ = _ := by ring
end SKGap.ComplexMatrix
end
end

section
noncomputable section
namespace SKGap
open Matrix Real Set
open RealComplex
open scoped BigOperators Matrix.Norms.Frobenius SchwartzMap
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma parameter_sqrt_small {δ : ℝ} (hδ : 0≤δ) (hδ1 : δ≤1) : δ≤ sqrt δ := by
  have hh := sq_sqrt hδ
  nlinarith [sqrt_nonneg δ,mul_nonneg hδ (sub_nonneg.mpr hδ1)]

lemma path_parameter_factors [Nonempty ι] {a b : ι→ℝ} {j A δ : ℝ}
    (hj : 0≤j) (hA : 0≤A) (hδ : 0≤δ) (hδ1 : δ≤1)
    (ha : ∀ i,0≤a i) (hb : ∀ i,0≤b i) (haA : ∀ i,a i≤A) (hbA : ∀ i,b i≤A)
    (hab : ∀ i,|a i-b i|≤δ) :
    let D := liftMatrix (pathDiagonal a 1)
    let D' := liftMatrix (pathDiagonal b 1)
    let C := liftMatrix (pathShift (ι:=ι) 1 ((j/(Fintype.card ι:ℝ))*∑ i,a i))
    let C' := liftMatrix (pathShift (ι:=ι) 1 ((j/(Fintype.card ι:ℝ))*∑ i,b i))
    ComplexMatrix.opNorm D≤ sqrt A ∧ ComplexMatrix.opNorm D'≤ sqrt A ∧
    ComplexMatrix.opNorm C≤j*A ∧ ComplexMatrix.opNorm C'≤j*A ∧
    ComplexMatrix.opNorm (D-D')≤(1+j)*sqrt δ ∧
    ComplexMatrix.opNorm (C-C')≤(1+j)*sqrt δ ∧
    ComplexMatrix.opNorm ((1+D*C*D)-(1+D'*C'*D'))≤
      (2*sqrt A*(j*A)+(sqrt A)^2)*((1+j)*sqrt δ) := by
  intro D D' C C'
  have hz : (1:ℝ)∈Icc (0:ℝ) 1 := ⟨zero_le_one,le_rfl⟩
  have hDa : ComplexMatrix.opNorm D≤ sqrt A := by
    simpa only [D,ComplexMatrix.opNorm,ComplexMatrix.lin,operator_norm_lift] using pathDiagonal_opNorm hA haA hz
  have hDb : ComplexMatrix.opNorm D'≤ sqrt A := by
    simpa only [D',ComplexMatrix.opNorm,ComplexMatrix.lin,operator_norm_lift] using pathDiagonal_opNorm hA hbA hz
  have hqa := diagonal_mean_bounds hj ha haA
  have hqb := diagonal_mean_bounds hj hb hbA
  have hCa : ComplexMatrix.opNorm C≤j*A := by
    simpa only [C,ComplexMatrix.opNorm,ComplexMatrix.lin,operator_norm_lift] using
      (pathShift_opNorm (ι:=ι) hz hqa.1).trans hqa.2
  have hCb : ComplexMatrix.opNorm C'≤j*A := by
    simpa only [C',ComplexMatrix.opNorm,ComplexMatrix.lin,operator_norm_lift] using
      (pathShift_opNorm (ι:=ι) hz hqb.1).trans hqb.2
  have hDD : ComplexMatrix.opNorm (D-D')≤(1+j)*sqrt δ := by
    have hh : opNorm (pathDiagonal a 1-pathDiagonal b 1)≤(1+j)*sqrt δ :=
      (pathDiagonal_parameter ha hb hδ hab).trans (by nlinarith [sqrt_nonneg δ])
    simpa only [D,D',← liftMatrix_sub,ComplexMatrix.opNorm,ComplexMatrix.lin,operator_norm_lift] using hh
  have hCC : ComplexMatrix.opNorm (C-C')≤(1+j)*sqrt δ := by
    have hh := pathShift_parameter hj hδ hab
    have hh' : j*δ≤(1+j)*sqrt δ := by
      have hmul := mul_le_mul_of_nonneg_left (parameter_sqrt_small hδ hδ1) hj
      nlinarith [sqrt_nonneg δ]
    simpa only [C,C',← liftMatrix_sub,ComplexMatrix.opNorm,ComplexMatrix.lin,operator_norm_lift] using hh.trans hh'
  exact ⟨hDa,hDb,hCa,hCb,hDD,hCC,ComplexMatrix.spectralShift_parameter _ _ _ _
    (sqrt_nonneg _) (mul_nonneg hj hA) (mul_nonneg (by linarith) (sqrt_nonneg _)) hDa hDb hCa hCb hDD hCC⟩

theorem pathK_parameter_holder [Nonempty ι] (f : 𝓢(ℝ,ℂ)) {R j A δ : ℝ}
    (hR : 0≤R) (hj : 0≤j) (hA : 0≤A) (hδ : 0≤δ) (hδ1 : δ≤1)
    {a b : ι→ℝ} (ha : ∀ i,0≤a i) (hb : ∀ i,0≤b i) (haA : ∀ i,a i≤A) (hbA : ∀ i,b i≤A)
    (hab : ∀ i,|a i-b i|≤δ) (M N : Matrix ι ι ℝ) :
    let H := 2*sqrt A*(j*A)+(sqrt A)^2
    opNorm (pathK f R hR j a 1 M-pathK f R hR j b 1 M)≤
      ComplexMatrix.parameterKC f R (sqrt A) (j*A) H*((1+j)*sqrt δ) ∧
    ‖(pathK f R hR j a 1 M-pathK f R hR j a 1 N)-
      (pathK f R hR j b 1 M-pathK f R hR j b 1 N)‖≤
      ComplexMatrix.parameterKM f R (sqrt A) (j*A) H*((1+j)*sqrt δ)*‖M-N‖ := by
  intro H
  obtain ⟨hDa,hDb,hCa,hCb,hDD,hCC,hBB⟩ := path_parameter_factors hj hA hδ hδ1 ha hb haA hbA hab
  let D := pathDiagonal a 1
  let D' := pathDiagonal b 1
  let C := pathShift (ι:=ι) 1 ((j/(Fintype.card ι:ℝ))*∑ i,a i)
  let C' := pathShift (ι:=ι) 1 ((j/(Fintype.card ι:ℝ))*∑ i,b i)
  have hH : 0≤H := by dsimp [H];positivity
  have hh := ComplexMatrix.cutoff_parameter_constants f hR (sqrt_nonneg A) (mul_nonneg hj hA) hH
    (show 0≤(1+j)*sqrt δ by positivity)
    (1+liftMatrix D*liftMatrix C*liftMatrix D) (1+liftMatrix D'*liftMatrix C'*liftMatrix D')
    (liftMatrix D) (liftMatrix D') (liftMatrix C) (liftMatrix C') hDa hDb hCa hBB hDD hCC
  constructor
  · exact (realTruncatedK_parameter f hR D D' C C' M (diagonal_transpose _)
      (diagonal_transpose _) (diagonal_transpose _) (diagonal_transpose _)).trans hh.1
  · exact (realTruncatedK_four_point f hR D D' C C' M N (diagonal_transpose _)
      (diagonal_transpose _) (diagonal_transpose _) (diagonal_transpose _)).trans
        (mul_le_mul_of_nonneg_right hh.2 (norm_nonneg _))
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

end SKGap
end
end

end OAI
end

section
-- module Solutions.OAIQ074_CM.SKGap_Matrix_MatrixWordIncrement
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
variable {ι X : Type*} [Fintype ι] [DecidableEq ι] [PseudoMetricSpace X]

omit [PseudoMetricSpace X] in
lemma word_opNorm_add (M N : Matrix ι ι ℝ) : opNorm (M+N) ≤ opNorm M+opNorm N := by
  unfold opNorm
  rw [map_add,map_add]
  exact norm_add_le _ _

omit [PseudoMetricSpace X] in
lemma real_product_four_point (a b c d e f g h : Matrix ι ι ℝ) :
    ‖(a*e-b*f)-(c*g-d*h)‖ ≤
      ‖(a-b)-(c-d)‖*opNorm e+‖c-d‖*opNorm (e-g)+
      opNorm (b-d)*‖e-f‖+opNorm d*‖(e-f)-(g-h)‖ := by
  have he : (a*e-b*f)-(c*g-d*h)=
      ((a-b)-(c-d))*e+(c-d)*(e-g)+(b-d)*(e-f)+d*((e-f)-(g-h)) := by noncomm_ring
  rw [he]
  calc
    _ ≤ ‖((a-b)-(c-d))*e+(c-d)*(e-g)+(b-d)*(e-f)‖+‖d*((e-f)-(g-h))‖ := norm_add_le _ _
    _ ≤ (‖((a-b)-(c-d))*e+(c-d)*(e-g)‖+‖(b-d)*(e-f)‖)+‖d*((e-f)-(g-h))‖ := by gcongr;exact norm_add_le _ _
    _ ≤ ((‖((a-b)-(c-d))*e‖+‖(c-d)*(e-g)‖)+‖(b-d)*(e-f)‖)+‖d*((e-f)-(g-h))‖ := by gcongr;exact norm_add_le _ _
    _ ≤ _ := by
      gcongr
      · exact frobenius_mul_le_opNorm_right _ _
      · exact frobenius_mul_le_opNorm_right _ _
      · exact frobenius_mul_le_opNorm _ _
      · exact frobenius_mul_le_opNorm _ _

theorem matrixWord_pair_increments (F : List ((X→Matrix ι ι ℝ)×(X→Matrix ι ι ℝ)))
    {B Δ : NNReal} (hF : ∀ p∈F,MatrixFactorPairBounds B Δ p.1 p.2) :
    (∀ x,opNorm (matrixFactorProduct (F.map Prod.fst) x-matrixFactorProduct (F.map Prod.snd) x)≤
      (wordParameterCoeff B F.length:ℝ)*Δ) ∧
    LipschitzWith (wordMixedCoeff B F.length*Δ)
      (fun x=>matrixFactorProduct (F.map Prod.fst) x-matrixFactorProduct (F.map Prod.snd) x) := by
  induction F with
  | nil =>
    constructor
    · intro x;simp [matrixFactorProduct,wordParameterCoeff,opNorm]
    · simp [matrixFactorProduct,wordMixedCoeff]
  | cons p F ih =>
    have hp := hF p List.mem_cons_self
    have hFt : ∀ q∈F,MatrixFactorPairBounds B Δ q.1 q.2 := fun q hq=>hF q (List.mem_cons_of_mem p hq)
    have ht := ih hFt
    have hbL : ∀ f∈F.map Prod.fst,∀ x,opNorm (f x)≤B := by
      intro f hf;obtain ⟨q,hq,rfl⟩ := List.mem_map.mp hf;exact (hFt q hq).leftBound
    have hlL : ∀ f∈F.map Prod.fst,LipschitzWith B f := by
      intro f hf;obtain ⟨q,hq,rfl⟩ := List.mem_map.mp hf;exact (hFt q hq).leftLip
    have htl := matrixFactorProduct_lipschitz (F.map Prod.fst) hbL hlL
    constructor
    · intro x
      simp only [List.map_cons,matrixFactorProduct_cons,List.length_cons,wordParameterCoeff,NNReal.coe_add,NNReal.coe_mul,NNReal.coe_pow]
      have he : p.1 x*matrixFactorProduct (F.map Prod.fst) x-p.2 x*matrixFactorProduct (F.map Prod.snd) x=
        (p.1 x-p.2 x)*matrixFactorProduct (F.map Prod.fst) x+
        p.2 x*(matrixFactorProduct (F.map Prod.fst) x-matrixFactorProduct (F.map Prod.snd) x) := by noncomm_ring
      rw [he]
      apply (word_opNorm_add _ _).trans
      apply (add_le_add (opNorm_mul _ _) (opNorm_mul _ _)).trans
      have h1 := mul_le_mul (hp.parameter x) (matrixFactorProduct_opNorm (F.map Prod.fst) hbL x)
        (show 0≤opNorm (matrixFactorProduct (F.map Prod.fst) x) from norm_nonneg _) Δ.coe_nonneg
      have h2 := mul_le_mul (hp.rightBound x) (ht.1 x) (show 0≤opNorm
        (matrixFactorProduct (F.map Prod.fst) x-matrixFactorProduct (F.map Prod.snd) x) from norm_nonneg _) B.coe_nonneg
      apply (add_le_add h1 h2).trans_eq
      simp only [List.length_map]
      ring
    · apply LipschitzWith.of_dist_le_mul
      intro x y
      simp only [dist_eq_norm,List.map_cons,matrixFactorProduct_cons]
      have he : (p.1 x*matrixFactorProduct (F.map Prod.fst) x-p.2 x*matrixFactorProduct (F.map Prod.snd) x)-
          (p.1 y*matrixFactorProduct (F.map Prod.fst) y-p.2 y*matrixFactorProduct (F.map Prod.snd) y)=
        (p.1 x*matrixFactorProduct (F.map Prod.fst) x-p.1 y*matrixFactorProduct (F.map Prod.fst) y)-
          (p.2 x*matrixFactorProduct (F.map Prod.snd) x-p.2 y*matrixFactorProduct (F.map Prod.snd) y) := by abel
      rw [he]
      apply (real_product_four_point _ _ _ _ _ _ _ _).trans
      have hi : ‖(p.1 x-p.1 y)-(p.2 x-p.2 y)‖≤(Δ:ℝ)*dist x y := by
        have hh := hp.increment.dist_le_mul x y
        rw [dist_eq_norm] at hh
        convert! hh using 1
        all_goals try with_reducible_and_instances rfl
        congr 1;abel
      have hr : ‖p.2 x-p.2 y‖≤(B:ℝ)*dist x y := by simpa only [dist_eq_norm] using hp.rightLip.dist_le_mul x y
      have hli : ‖matrixFactorProduct (F.map Prod.fst) x-matrixFactorProduct (F.map Prod.fst) y‖≤
          ((F.length:ℝ)*(B:ℝ)^F.length)*dist x y := by
        simpa only [dist_eq_norm,List.length_map,NNReal.coe_mul,NNReal.coe_natCast,NNReal.coe_pow] using htl.dist_le_mul x y
      have hm : ‖(matrixFactorProduct (F.map Prod.fst) x-matrixFactorProduct (F.map Prod.fst) y)-
          (matrixFactorProduct (F.map Prod.snd) x-matrixFactorProduct (F.map Prod.snd) y)‖≤
          ((wordMixedCoeff B F.length:ℝ)*Δ)*dist x y := by
        have hh := ht.2.dist_le_mul x y
        rw [dist_eq_norm] at hh
        convert! hh using 1
        all_goals try with_reducible_and_instances rfl
        congr 1;abel
      have h1 := mul_le_mul hi (matrixFactorProduct_opNorm (F.map Prod.fst) hbL x)
        (show 0≤opNorm (matrixFactorProduct (F.map Prod.fst) x) from norm_nonneg _) (mul_nonneg Δ.coe_nonneg dist_nonneg)
      have h2 := mul_le_mul hr (ht.1 x) (show 0≤opNorm
        (matrixFactorProduct (F.map Prod.fst) x-matrixFactorProduct (F.map Prod.snd) x) from norm_nonneg _)
        (mul_nonneg B.coe_nonneg dist_nonneg)
      have h3 := mul_le_mul (hp.parameter y) hli (norm_nonneg _) Δ.coe_nonneg
      have h4 := mul_le_mul (hp.rightBound y) hm (norm_nonneg _) B.coe_nonneg
      apply (add_le_add (add_le_add (add_le_add h1 h2) h3) h4).trans_eq
      simp only [List.length_map,List.length_cons,wordMixedCoeff,NNReal.coe_add,NNReal.coe_mul,
        NNReal.coe_natCast,NNReal.coe_pow]
      ring
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

end SKGap
end
end

end OAI
end

section
-- module Solutions.OAIQ074_CM.SKGap_Matrix_WordIncrement
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
namespace SKGap
open Matrix Real Set
open scoped BigOperators Matrix.Norms.Frobenius SchwartzMap
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma wordHolderScale_constants (f : 𝓢(ℝ,ℂ)) (R A : ℝ) {j : ℝ} (hj : 0≤j) :
    ComplexMatrix.parameterKC f R (sqrt A) (j*A) (2*sqrt A*(j*A)+(sqrt A)^2)*(1+j)≤wordHolderScale f R j A ∧
    ComplexMatrix.parameterKM f R (sqrt A) (j*A) (2*sqrt A*(j*A)+(sqrt A)^2)*(1+j)≤wordHolderScale f R j A := by
  have hc := le_abs_self (ComplexMatrix.parameterKC f R (sqrt A) (j*A) (2*sqrt A*(j*A)+(sqrt A)^2))
  have hm := le_abs_self (ComplexMatrix.parameterKM f R (sqrt A) (j*A) (2*sqrt A*(j*A)+(sqrt A)^2))
  have hc0 := abs_nonneg (ComplexMatrix.parameterKC f R (sqrt A) (j*A) (2*sqrt A*(j*A)+(sqrt A)^2))
  have hm0 := abs_nonneg (ComplexMatrix.parameterKM f R (sqrt A) (j*A) (2*sqrt A*(j*A)+(sqrt A)^2))
  have h1 : 0≤1+j := by linarith
  unfold wordHolderScale
  constructor
  · have h := mul_le_mul_of_nonneg_right hc h1
    nlinarith
  · have h := mul_le_mul_of_nonneg_right hm h1
    nlinarith

lemma WordLetter.eval_pair [Nonempty ι] (f : 𝓢(ℝ,ℂ)) {R j A D δ : ℝ}
    (hR : 0≤R) (hj : 0≤j) (hA : 0≤A) (hD : 0≤D) (hδ : 0≤δ) (hδ1 : δ≤1)
    {a b : ι→ℝ} (ha : ∀ i,0≤a i) (hb : ∀ i,0≤b i) (haA : ∀ i,a i≤A) (hbA : ∀ i,b i≤A)
    (hab : ∀ i,|a i-b i|≤δ) (l m : WordLetter ι) (hl : l.bounded D) (hm : m.bounded D)
    (hlm : l.close δ m) :
    let B : NNReal := ⟨actualWordBound f R j A D,(actualWordBound_pos f hR hj hA hD).le⟩
    let Δ : NNReal := ⟨wordHolderScale f R j A*sqrt δ,mul_nonneg (zero_le_one.trans (wordHolderScale_ge_one f R A hj)) (sqrt_nonneg _)⟩
    MatrixFactorPairBounds B Δ (l.eval f R hR j a 1) (m.eval f R hR j b 1) := by
  intro B Δ
  obtain ⟨hlb,hll⟩ := l.eval_bounds f hR hj hA hD ha haA ⟨zero_le_one,le_rfl⟩ hl
  obtain ⟨hmb,hml⟩ := m.eval_bounds f hR hj hA hD hb hbA ⟨zero_le_one,le_rfl⟩ hm
  refine ⟨hlb,hmb,hll,hml,?_,?_⟩
  · intro M
    cases l <;> cases m <;> try contradiction
    · rename_i d e
      change opNorm (diagonal d-diagonal e)≤wordHolderScale f R j A*sqrt δ
      rw [Matrix.diagonal_sub]
      exact (opNorm_diagonal_le hδ hlm).trans ((parameter_sqrt_small hδ hδ1).trans
        (by nlinarith [wordHolderScale_ge_one f R A hj,sqrt_nonneg δ]))
    · simp [WordLetter.eval,opNorm]
    · exact ((pathK_parameter_holder f hR hj hA hδ hδ1 ha hb haA hbA hab M M).1).trans
        (by have hh := mul_le_mul_of_nonneg_right (wordHolderScale_constants f R A hj).1 (sqrt_nonneg δ)
            simpa only [mul_assoc,Δ,NNReal.coe_mk] using! hh)
  · cases l <;> cases m <;> try contradiction
    · rename_i d e
      exact (LipschitzWith.const (diagonal d-diagonal e)).weaken (show (0:NNReal)≤Δ from zero_le)
    · simpa only [WordLetter.eval,sub_self] using (LipschitzWith.const (0:Matrix ι ι ℝ)).weaken (show (0:NNReal)≤Δ from zero_le)
    · apply LipschitzWith.of_dist_le_mul
      intro M N
      change ‖(pathK f R hR j a 1 M-pathK f R hR j b 1 M)-
        (pathK f R hR j a 1 N-pathK f R hR j b 1 N)‖≤wordHolderScale f R j A*sqrt δ*‖M-N‖
      have he : (pathK f R hR j a 1 M-pathK f R hR j b 1 M)-
          (pathK f R hR j a 1 N-pathK f R hR j b 1 N)=
          (pathK f R hR j a 1 M-pathK f R hR j a 1 N)-
          (pathK f R hR j b 1 M-pathK f R hR j b 1 N) := by abel
      rw [he]
      apply ((pathK_parameter_holder f hR hj hA hδ hδ1 ha hb haA hbA hab M N).2).trans
      apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
      have hh := mul_le_mul_of_nonneg_right (wordHolderScale_constants f R A hj).2 (sqrt_nonneg δ)
      simpa only [mul_assoc,Δ,NNReal.coe_mk] using! hh

end SKGap
end
end

section
noncomputable section
namespace SKGap
open Matrix Real Set
open scoped BigOperators Matrix.Norms.Frobenius SchwartzMap
variable {ι : Type*} [Fintype ι] [DecidableEq ι] {m : ℕ}

omit [Fintype ι] [DecidableEq ι] in
lemma templateInverse_bounds {A : ℝ} (hA : 0 ≤ A) (θ : WordParameter m ι) (i : ι) :
    0 ≤ templateInverse A θ i ∧ templateInverse A θ i ≤ A := by
  obtain ⟨h0,h1⟩ := (θ (none,i)).property
  dsimp [templateInverse]
  constructor
  · positivity
  · nlinarith only [mul_le_mul_of_nonneg_left h1 hA]

omit [Fintype ι] [DecidableEq ι] in
lemma templateDiagonal_bound {D : ℝ} (hD : 0 ≤ D) (θ : WordParameter m ι) (k : Fin m) (i : ι) :
    |templateDiagonal D θ k i| ≤ D := by
  obtain ⟨h0,h1⟩ := (θ (some k,i)).property
  rw [templateDiagonal,abs_mul,abs_of_nonneg hD]
  have hf : |2*(θ (some k,i):ℝ)-1| ≤ 1 := abs_le.mpr ⟨by linarith,by linarith⟩
  simpa only [mul_one] using mul_le_mul_of_nonneg_left hf hD

omit [Fintype ι] [DecidableEq ι] in
lemma templateWord_bounded {D : ℝ} (hD : 0 ≤ D) (θ : WordParameter m ι)
    (F : List (WordTemplateLetter m)) : ∀ l∈templateWord D θ F,l.bounded D := by
  intro l hl
  obtain ⟨q,hq,rfl⟩ := List.mem_map.mp hl
  cases q with
  | diag k => exact templateDiagonal_bound hD θ k
  | noise => trivial
  | inverse => trivial

omit [DecidableEq ι] in
lemma template_coord_dist (θ η : WordParameter m ι) (s : Option (Fin m)×ι) :
    |(θ s:ℝ)-(η s:ℝ)| ≤ dist θ η := by
  simpa only [Subtype.dist_eq,Real.dist_eq] using dist_le_pi_dist θ η s

omit [DecidableEq ι] in
lemma templateInverse_dist {A D : ℝ} (hA : 0 ≤ A) (hD : 0 ≤ D)
    (θ η : WordParameter m ι) (i : ι) :
    |templateInverse A θ i-templateInverse A η i| ≤ templateScale A D*dist θ η := by
  rw [templateInverse,templateInverse,←mul_sub,abs_mul,abs_of_nonneg hA]
  apply (mul_le_mul_of_nonneg_left (template_coord_dist θ η (none,i)) hA).trans
  apply mul_le_mul_of_nonneg_right _ dist_nonneg
  dsimp [templateScale]
  linarith

omit [DecidableEq ι] in
lemma templateLetter_close {A D : ℝ} (hA : 0 ≤ A) (hD : 0 ≤ D)
    (θ η : WordParameter m ι) (l : WordTemplateLetter m) :
    (l.realize D θ).close (templateScale A D*dist θ η) (l.realize D η) := by
  cases l with
  | noise => trivial
  | inverse => trivial
  | diag k =>
    intro i
    change |D*(2*(θ (some k,i):ℝ)-1)-D*(2*(η (some k,i):ℝ)-1)| ≤ _
    have he : D*(2*(θ (some k,i):ℝ)-1)-D*(2*(η (some k,i):ℝ)-1)=
        (2*D)*((θ (some k,i):ℝ)-(η (some k,i):ℝ)) := by ring
    rw [he,abs_mul,abs_of_nonneg (by positivity : 0 ≤ 2*D)]
    apply (mul_le_mul_of_nonneg_left (template_coord_dist θ η (some k,i)) (by positivity : 0 ≤ 2*D)).trans
    apply mul_le_mul_of_nonneg_right _ dist_nonneg
    dsimp [templateScale]
    linarith

omit [DecidableEq ι] in
lemma templateWord_paired {A D : ℝ} (hA : 0 ≤ A) (hD : 0 ≤ D)
    (θ η : WordParameter m ι) (F : List (WordTemplateLetter m)) :
    ∀ p∈F.map (fun l=>(l.realize D θ,l.realize D η)),
      p.1.bounded D ∧ p.2.bounded D ∧ p.1.close (templateScale A D*dist θ η) p.2 := by
  intro p hp
  obtain ⟨l,hl,rfl⟩ := List.mem_map.mp hp
  exact ⟨templateWord_bounded hD θ F _ (List.mem_map.mpr ⟨l,hl,rfl⟩),
    templateWord_bounded hD η F _ (List.mem_map.mpr ⟨l,hl,rfl⟩),templateLetter_close hA hD θ η l⟩
end SKGap
end
end

end OAI
end

section
-- module Solutions.OAIQ074_CM.SKGap_Matrix_GlobalWordIncrement
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
namespace SKGap
open Matrix Real Set
open scoped BigOperators Matrix.Norms.Frobenius SchwartzMap
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma WordLetter.eval_pair_global [Nonempty ι] (f : 𝓢(ℝ,ℂ)) {R j A D δ : ℝ}
    (hR : 0 ≤ R) (hj : 0 ≤ j) (hA : 0 ≤ A) (hD : 0 ≤ D) (hδ : 0 ≤ δ)
    {a b : ι→ℝ} (ha : ∀ i,0 ≤ a i) (hb : ∀ i,0 ≤ b i) (haA : ∀ i,a i ≤ A) (hbA : ∀ i,b i ≤ A)
    (hab : ∀ i,|a i-b i| ≤ δ) (l m : WordLetter ι) (hl : l.bounded D) (hm : m.bounded D)
    (hlm : l.close δ m) :
    let B : NNReal := ⟨actualWordBound f R j A D,(actualWordBound_pos f hR hj hA hD).le⟩
    let Δ : NNReal := ⟨globalWordHolder f R j A D*sqrt δ,mul_nonneg (globalWordHolder_nonneg f hR hj hA hD) (sqrt_nonneg _)⟩
    MatrixFactorPairBounds B Δ (l.eval f R hR j a 1) (m.eval f R hR j b 1) := by
  intro B Δ
  have hG : wordHolderScale f R j A ≤ globalWordHolder f R j A D := by
    have hh := actualWordBound_pos f hR hj hA hD
    dsimp [globalWordHolder]
    linarith
  by_cases hs : δ ≤ 1
  · have hh := l.eval_pair f hR hj hA hD hδ hs ha hb haA hbA hab m hl hm hlm
    have hΔ : (⟨wordHolderScale f R j A*sqrt δ,mul_nonneg (zero_le_one.trans (wordHolderScale_ge_one f R A hj)) (sqrt_nonneg _)⟩:NNReal) ≤ Δ :=
      mul_le_mul_of_nonneg_right hG (sqrt_nonneg _)
    exact ⟨hh.leftBound,hh.rightBound,hh.leftLip,hh.rightLip,
      fun M=>(hh.parameter M).trans hΔ,hh.increment.weaken hΔ⟩
  · have hδ1 : 1 ≤ sqrt δ := by simpa only [sqrt_one] using sqrt_le_sqrt (le_of_not_ge hs)
    have hGB : 2*(B:ℝ) ≤ globalWordHolder f R j A D := by
      have hh := wordHolderScale_ge_one f R A hj
      change 2*actualWordBound f R j A D ≤ wordHolderScale f R j A+2*actualWordBound f R j A D+1
      linarith
    have hBΔ : 2*(B:ℝ) ≤ (Δ:ℝ) := by
      change 2*(B:ℝ) ≤ globalWordHolder f R j A D*sqrt δ
      exact (le_mul_of_one_le_right (by positivity : 0 ≤ 2*(B:ℝ)) hδ1).trans
        (mul_le_mul_of_nonneg_right hGB (sqrt_nonneg _))
    obtain ⟨h1,h2⟩ := l.eval_bounds f hR hj hA hD ha haA ⟨zero_le_one,le_rfl⟩ hl
    obtain ⟨h3,h4⟩ := m.eval_bounds f hR hj hA hD hb hbA ⟨zero_le_one,le_rfl⟩ hm
    refine ⟨h1,h3,h2,h4,?_,?_⟩
    · intro M
      exact (opNorm_sub _ _).trans ((add_le_add (h1 M) (h3 M)).trans (by
        change actualWordBound f R j A D + actualWordBound f R j A D ≤ (Δ:ℝ)
        change 2*actualWordBound f R j A D ≤ (Δ:ℝ) at hBΔ
        linarith))
    · apply LipschitzWith.of_dist_le_mul
      intro M N
      rw [dist_eq_norm]
      have he : (l.eval f R hR j a 1 M-m.eval f R hR j b 1 M)-
          (l.eval f R hR j a 1 N-m.eval f R hR j b 1 N)=
          (l.eval f R hR j a 1 M-l.eval f R hR j a 1 N)-
          (m.eval f R hR j b 1 M-m.eval f R hR j b 1 N) := by abel
      rw [he]
      apply (norm_sub_le _ _).trans
      have h2' := h2.dist_le_mul M N
      have h4' := h4.dist_le_mul M N
      rw [dist_eq_norm] at h2' h4'
      calc
        _ ≤ (B:ℝ)*dist M N+(B:ℝ)*dist M N := add_le_add h2' h4'
        _ = (2*(B:ℝ))*dist M N := by ring
        _ ≤ (Δ:ℝ)*dist M N := mul_le_mul_of_nonneg_right hBΔ dist_nonneg

theorem actualWord_pair_global [Nonempty ι] (f : 𝓢(ℝ,ℂ)) {R j A D δ : ℝ}
    (hR : 0 ≤ R) (hj : 0 ≤ j) (hA : 0 ≤ A) (hD : 0 ≤ D) (hδ : 0 ≤ δ)
    {a b : ι→ℝ} (ha : ∀ i,0 ≤ a i) (hb : ∀ i,0 ≤ b i) (haA : ∀ i,a i ≤ A) (hbA : ∀ i,b i ≤ A)
    (hab : ∀ i,|a i-b i| ≤ δ) (F : List (WordLetter ι×WordLetter ι))
    (hF : ∀ p∈F,p.1.bounded D ∧ p.2.bounded D ∧ p.1.close δ p.2) :
    let B : NNReal := ⟨actualWordBound f R j A D,(actualWordBound_pos f hR hj hA hD).le⟩
    let Δ : NNReal := ⟨globalWordHolder f R j A D*sqrt δ,mul_nonneg (globalWordHolder_nonneg f hR hj hA hD) (sqrt_nonneg _)⟩
    (∀ M,opNorm (actualWord f R hR j a 1 (F.map Prod.fst) M-actualWord f R hR j b 1 (F.map Prod.snd) M) ≤
      (wordParameterCoeff B F.length:ℝ)*Δ) ∧
    LipschitzWith (wordMixedCoeff B F.length*Δ)
      (fun M=>actualWord f R hR j a 1 (F.map Prod.fst) M-actualWord f R hR j b 1 (F.map Prod.snd) M) := by
  intro B Δ
  let G := F.map (fun p=>(p.1.eval f R hR j a 1,p.2.eval f R hR j b 1))
  have hG : ∀ p∈G,MatrixFactorPairBounds B Δ p.1 p.2 := by
    intro p hp
    obtain ⟨q,hq,rfl⟩ := List.mem_map.mp hp
    obtain ⟨h1,h2,h3⟩ := hF q hq
    exact WordLetter.eval_pair_global f hR hj hA hD hδ ha hb haA hbA hab q.1 q.2 h1 h2 h3
  simpa only [G,List.length_map,List.map_map,Function.comp_def,actualWord] using! matrixWord_pair_increments G hG
end SKGap
end
end

end OAI
end

section
-- module Solutions.OAIQ074_CM.SKGap_Localization_GeneralTemplateRegularity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
namespace SKGap
open Matrix Real Set
open scoped BigOperators Matrix.Norms.Frobenius SchwartzMap
variable {ι : Type*} [Fintype ι] [DecidableEq ι] {m : ℕ}

theorem generalTemplateMatrix_increments_s2_oai [Nonempty ι] (f : 𝓢(ℝ,ℂ)) {R j A D : ℝ}
    (hR : 0 ≤ R) (hj : 0 ≤ j) (hA : 0 ≤ A) (hD : 0 ≤ D)
    (F : List (WordTemplateLetter m)) (θ η : WordParameter m ι) :
    let B : NNReal := ⟨actualWordBound f R j A D,(actualWordBound_pos f hR hj hA hD).le⟩
    let Δ : NNReal := ⟨generalTemplateHolder f R j A D*sqrt (dist θ η),mul_nonneg (generalTemplateHolder_nonneg f hR hj hA hD) (sqrt_nonneg _)⟩
    (∀ M,opNorm (generalTemplateMatrix f R hR j A D F θ M-generalTemplateMatrix f R hR j A D F η M) ≤
      (wordParameterCoeff B F.length:ℝ)*Δ) ∧
    LipschitzWith (wordMixedCoeff B F.length*Δ)
      (fun M=>generalTemplateMatrix f R hR j A D F θ M-generalTemplateMatrix f R hR j A D F η M) := by
  intro B Δ
  have hK : 0 ≤ templateScale A D := by dsimp [templateScale];positivity
  have hh := actualWord_pair_global f hR hj hA hD (mul_nonneg hK dist_nonneg)
    (fun i=>(templateInverse_bounds hA θ i).1) (fun i=>(templateInverse_bounds hA η i).1)
    (fun i=>(templateInverse_bounds hA θ i).2) (fun i=>(templateInverse_bounds hA η i).2)
    (templateInverse_dist hA hD θ η)
    (F.map (fun l=>(l.realize D θ,l.realize D η))) (templateWord_paired hA hD θ η F)
  simpa only [generalTemplateMatrix,generalTemplateHolder,B,Δ,List.length_map,List.map_map,
    Function.comp_def,templateWord,Real.sqrt_mul hK,mul_assoc] using! hh
end SKGap
end
end

end OAI
end

theorem solution.{u_1} : type_of% @OAI.SKGap.generalTemplateMatrix_increments_s2_oai.{u_1} := @OAI.SKGap.generalTemplateMatrix_increments_s2_oai.{u_1}
