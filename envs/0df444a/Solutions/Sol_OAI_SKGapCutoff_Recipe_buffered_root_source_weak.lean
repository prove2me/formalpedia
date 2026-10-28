-- Prove2me | solution 1 for OAI.SKGapCutoff.Recipe.buffered_root_source_weak
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T06:59:24.26242+00:00
-- url     : https://prove2.me/submissions/3f67758a-1ac6-4cba-930d-de20c4ca50d2

import Mathlib
import Definitions.Def_OAIQ072A002
import Theorems.Thm_OAI_SKGapCutoff_Recipe_literal_complete_diagnostics
import Theorems.Thm_OAI_SKGapCutoff_Recipe_literal_local_weak_comparison_targets

section
-- module Solutions.OAIQ072_SK.Compat
attribute [-instance] _root_.OAI.SKGap.ComplexMatrix.frobeniusInnerProduct
namespace OAI

/-! Compatibility with the newer Lean core OpenAI's code was written against: lemmas it uses by
names this environment (Lean 4.33.1, Mathlib 0df444a) does not have yet. Each is the
corresponding `if_pos` / `if_neg` / `dif_pos` / `dif_neg`. The `dite` forms are stated as
`dite p a b`, not with the `if hp : p then …` notation: its eta-expanded lambdas form is a higher-order pattern
that `rw` cannot find (DepthThree, PeriodicTiling 2026-10-25). -/
section OAICompat434
theorem dite_eq_left {α : Sort _} {p : Prop} {_ : Decidable p} {a : p → α} {b : ¬p → α} (h : p) :
    dite p a b = a h := dif_pos h
end OAICompat434

end OAI
end

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

lemma lowerRayleigh_ge [Nonempty ι] {M : Matrix ι ι ℂ} {c : ℝ}
    (hc : ∀ x ∈ unitSphere ι, c ≤ quadratic M x) : c ≤ lowerRayleigh M := by
  classical
  obtain ⟨i⟩ := ‹Nonempty ι›
  have hn : (quadratic M '' unitSphere ι).Nonempty := by
    refine ⟨quadratic M (EuclideanSpace.single i (1:ℂ)),?_⟩
    exact ⟨_,by simp [unitSphere],rfl⟩
  exact le_csInf hn (by rintro _ ⟨x,hx,rfl⟩; exact hc x hx)

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

lemma colVec_eq (M : Matrix ι ι ℝ) (k : ι) :
    colVec M k = M.toEuclideanLin.toContinuousLinearMap (EuclideanSpace.single k (1:ℝ)) := by
  ext i
  simp [colVec,Matrix.toLpLin_apply]

lemma colVec_norm_le (M : Matrix ι ι ℝ) (k : ι) : ‖colVec M k‖ ≤ opNorm M := by
  rw [colVec_eq]
  simpa only [PiLp.norm_single,norm_one,mul_one,opNorm] using!
    M.toEuclideanLin.toContinuousLinearMap.le_opNorm (EuclideanSpace.single k (1:ℝ))

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

omit [DecidableEq ι] in
lemma quadratic_lift_split (M : Matrix ι ι ℝ) (x : EuclideanSpace ℂ ι) :
    quadratic (liftMatrix M) x = realQuadratic M (reVec x)+realQuadratic M (imVec x) := by
  change (∑ i, star (x i)*∑ k, (M i k:ℂ)*x k).re = _
  simp only [Finset.mul_sum,Complex.re_sum,Complex.mul_re,Complex.mul_im,Complex.star_def,
    Complex.conj_re,Complex.conj_im,Complex.ofReal_re,Complex.ofReal_im,
    zero_mul,sub_zero,realQuadratic,reVec,imVec,PiLp.toLp_apply,
    ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro k _
  ring

omit [DecidableEq ι] in
lemma lowerRayleigh_lift_ge [Nonempty ι] {M : Matrix ι ι ℝ} {c : ℝ}
    (hc : ∀ x : EuclideanSpace ℝ ι, c*‖x‖^2 ≤ realQuadratic M x) :
    c ≤ _root_.OAI.SKGap.ComplexSpectral.lowerRayleigh (liftMatrix M) := by
  apply lowerRayleigh_ge
  intro x hx
  have hn : ‖x‖ = 1 := by simpa only [unitSphere,Metric.mem_sphere,dist_zero_right] using hx
  have h := add_le_add (hc (reVec x)) (hc (imVec x))
  rw [← mul_add,← vec_norm_split,hn,one_pow,mul_one,← quadratic_lift_split] at h
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

end SKGap

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
-- module Solutions.OAIQ072_SK.SKGap_Matrix_MatrixQuad
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
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in
lemma matrixQuad_smul (M : Matrix ι ι ℝ) (p : EuclideanSpace ℝ ι) (c : ℝ) :
    matrixQuad M (c • p) = c^2 * matrixQuad M p := by
  simp only [matrixQuad, PiLp.smul_apply, smul_eq_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro k _
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
-- module Solutions.OAIQ072_SK.SKGap_Gaussian_PhiStein
attribute [-instance] _root_.OAI.SKGap.ComplexMatrix.frobeniusInnerProduct
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open MeasureTheory Filter
open scoped Topology
namespace SKGap.Stein

lemma hasDerivAt_integral01 {F F' : ℝ→ℝ→ℝ}
    (hF : Continuous (fun p : ℝ×ℝ=>F p.1 p.2))
    (hF' : Continuous (fun p : ℝ×ℝ=>F' p.1 p.2))
    (hd : ∀ z u,HasDerivAt (fun z=>F z u) (F' z u) z) (z : ℝ) :
    HasDerivAt (fun z=>∫u in (0:ℝ)..1,F z u) (∫u in (0:ℝ)..1,F' z u) z := by
  obtain ⟨C,hC⟩ := (isCompact_Icc.prod isCompact_Icc).exists_bound_of_continuousOn
    (hF'.continuousOn : ContinuousOn (fun p : ℝ×ℝ=>F' p.1 p.2)
      ((Set.Icc (z-1) (z+1))×ˢ(Set.Icc (0:ℝ) 1)))
  have hc (x : ℝ) : Continuous (F x) := hF.comp (continuous_const.prodMk continuous_id)
  have hc' (x : ℝ) : Continuous (F' x) := hF'.comp (continuous_const.prodMk continuous_id)
  exact (intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F:=F) (F':=F') (bound:=fun _=>C)
    (s:=Set.Icc (z-1) (z+1)) (Icc_mem_nhds (by linarith) (by linarith))
    (Eventually.of_forall (fun x=>(hc x).aestronglyMeasurable))
    (hc z|>.intervalIntegrable _ _) (hc' z).aestronglyMeasurable
    (Eventually.of_forall (by
      intro u hu x hx
      rw [Set.uIoc_of_le (by norm_num : (0:ℝ)≤1)] at hu
      exact hC (x,u) ⟨hx,hu.1.le,hu.2⟩))
    intervalIntegrable_const
    (Eventually.of_forall (fun u _ x _=>hd x u))).2

lemma continuous_weight (a : ℝ) : Continuous (weight a) := by unfold weight; fun_prop

lemma phi_eq (z r a : ℝ) : phi z r a=numerator z r a/(Real.cosh z*Real.cosh r) := by
  exact intervalIntegral.integral_div _ _

lemma numerator_hasDerivAt (z r a : ℝ) :
    HasDerivAt (fun z=>numerator z r a) (numeratorZ z r a) z := by
  unfold numerator numeratorZ
  apply hasDerivAt_integral01 (F:=fun z u=>weight a u*Real.cosh (u*(z-r)))
    (F':=fun z u=>weight a u*u*Real.sinh (u*(z-r)))
  · unfold weight; fun_prop
  · unfold weight; fun_prop
  · intro z u
    convert! ((Real.hasDerivAt_cosh (u*(z-r))).comp z
      (((hasDerivAt_id z).sub_const r).const_mul u)).const_mul (weight a u) using 1
    all_goals try with_reducible_and_instances rfl
    ring

lemma phi_hasDerivAt (z r a : ℝ) : HasDerivAt (fun z=>phi z r a) (phiZ z r a) z := by
  have h := (numerator_hasDerivAt z r a).div
    ((Real.hasDerivAt_cosh z).mul_const (Real.cosh r))
    (ne_of_gt (mul_pos (Real.cosh_pos z) (Real.cosh_pos r)))
  convert! h using 1
  · funext x; exact phi_eq x r a
  · rw [phiZ,phi_eq,Real.tanh_eq_sinh_div_cosh]
    field_simp [ne_of_gt (Real.cosh_pos z),ne_of_gt (Real.cosh_pos r)]

lemma weight_hasDerivAt (a u : ℝ) : HasDerivAt (weight a) (-a*u*weight a u) u := by
  unfold weight
  convert! (Real.hasDerivAt_exp _).comp u
    ((((hasDerivAt_id u).pow 2).const_sub 1).const_mul a |>.div_const 2) using 1
  all_goals try with_reducible_and_instances rfl
  dsimp
  ring

lemma boundary_hasDerivAt (z r a u : ℝ) :
    HasDerivAt (fun u=>weight a u*Real.sinh (u*(z-r)))
      (weight a u*((z-r)*Real.cosh (u*(z-r))-a*u*Real.sinh (u*(z-r)))) u := by
  convert! (weight_hasDerivAt a u).mul
    ((Real.hasDerivAt_sinh (u*(z-r))).comp u ((hasDerivAt_id u).mul_const (z-r))) using 1
  all_goals try with_reducible_and_instances rfl
  dsimp
  ring

lemma numerator_boundary (z r a : ℝ) :
    (z-r)*numerator z r a-a*numeratorZ z r a=Real.sinh (z-r) := by
  have hc1 : Continuous (fun u=>weight a u*Real.cosh (u*(z-r))) := by
    exact (continuous_weight a).mul (by fun_prop)
  have hc2 : Continuous (fun u=>weight a u*u*Real.sinh (u*(z-r))) := by
    exact ((continuous_weight a).mul continuous_id).mul (by fun_prop)
  have he : (fun u=>weight a u*((z-r)*Real.cosh (u*(z-r))-a*u*Real.sinh (u*(z-r))))=
      (fun u=>(z-r)*(weight a u*Real.cosh (u*(z-r)))-a*(weight a u*u*Real.sinh (u*(z-r)))) := by
    funext u; ring
  have H:=intervalIntegral.integral_eq_sub_of_hasDerivAt
    (a:=(0:ℝ)) (b:=1) (fun u _=>boundary_hasDerivAt z r a u)
    (show IntervalIntegrable (fun u=>weight a u*((z-r)*Real.cosh (u*(z-r))-a*u*Real.sinh (u*(z-r)))) volume 0 1 from by
      rw [he]; exact ((hc1.const_mul (z-r)).sub (hc2.const_mul a)).intervalIntegrable _ _)
  rw [he,intervalIntegral.integral_sub ((hc1.const_mul (z-r)).intervalIntegrable _ _)
    ((hc2.const_mul a).intervalIntegrable _ _),intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul] at H
  simpa only [numerator,numeratorZ,weight,one_pow,sub_self,mul_zero,zero_div,
    Real.exp_zero,one_mul,zero_mul,Real.sinh_zero,sub_zero] using H

theorem phi_stein (z r a : ℝ) :
    (z-r-a*Real.tanh z)*phi z r a-a*phiZ z r a=Real.tanh z-Real.tanh r := by
  rw [phiZ,phi_eq]
  have H:=numerator_boundary z r a
  have hId : Real.sinh (z-r)/(Real.cosh z*Real.cosh r)=Real.tanh z-Real.tanh r := by
    rw [Real.sinh_sub,Real.tanh_eq_sinh_div_cosh,Real.tanh_eq_sinh_div_cosh]
    field_simp [ne_of_gt (Real.cosh_pos z),ne_of_gt (Real.cosh_pos r)]
  rw [←hId]
  field_simp [ne_of_gt (Real.cosh_pos z),ne_of_gt (Real.cosh_pos r)]
  nlinarith [H]

lemma phi_pos (z r a : ℝ) : 0<phi z r a := by
  apply intervalIntegral.integral_pos (by norm_num : (0:ℝ)<1)
  · apply Continuous.continuousOn; unfold weight
    exact Continuous.div_const (by fun_prop) _
  · intro u _; exact (div_pos (mul_pos (Real.exp_pos _) (Real.cosh_pos _))
      (mul_pos (Real.cosh_pos _) (Real.cosh_pos _))).le
  · exact ⟨0,by norm_num,div_pos (mul_pos (Real.exp_pos _) (Real.cosh_pos _))
      (mul_pos (Real.cosh_pos _) (Real.cosh_pos _))⟩

lemma phiZ_at_diagonal (r a : ℝ) : phiZ r r a= -Real.tanh r*phi r r a := by
  simp [phiZ,numeratorZ]

end SKGap.Stein

end
end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Terminal_Spin
attribute [-instance] _root_.OAI.SKGap.ComplexMatrix.frobeniusInnerProduct
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open scoped BigOperators

namespace SKGapCutoff

theorem halfDiff_mul {n : ℕ} (i : Fin n) (f g : Spin n → ℝ) (x : Spin n) :
    halfDiff i (fun y => f y * g y) x =
      f x * halfDiff i g x + g x * halfDiff i f x -
        2 * spin x i * halfDiff i f x * halfDiff i g x := by
  have hx : replace x i (x i) = x := replace_self x i
  cases h : x i <;> simp only [h] at hx
  · simp only [halfDiff, spin, h, Bool.false_eq_true, ↓reduceIte]
    rw [hx]
    ring
  · simp only [halfDiff, spin, h, ↓reduceIte]
    rw [hx]
    ring

theorem halfDiff_sub {n : ℕ} (i : Fin n) (f g : Spin n → ℝ) (x : Spin n) :
    halfDiff i (fun y => f y - g y) x = halfDiff i f x - halfDiff i g x := by
  simp only [halfDiff]
  ring

end SKGapCutoff
end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Terminal_GibbsExpectation
attribute [-instance] _root_.OAI.SKGap.ComplexMatrix.frobeniusInnerProduct
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators
namespace SKGapCutoff
open Filter Topology

lemma flip_sub {n : ℕ} (i : Fin n) (f : Observables n) (x : Spin n) :
    f (flip x i) - f x = -2 * spin x i * halfDiff i f x := by
  have hx := replace_self x i
  cases hi : x i <;> simp only [hi] at hx
  · simp only [flip, hi, Bool.not_false, spin, Bool.false_eq_true, ↓reduceIte, halfDiff]
    rw [hx]; ring
  · simp only [flip, hi, Bool.not_true, spin, ↓reduceIte, halfDiff]
    rw [hx]; ring

end SKGapCutoff

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

lemma scalarVariance_eq (y : ℝ) : scalarVariance y = 1 / Real.cosh y ^ 2 := by
  have hc := Real.cosh_sq_sub_sinh_sq y
  unfold scalarVariance
  rw [Real.tanh_eq_sinh_div_cosh]
  field_simp
  nlinarith

lemma tanh_hasDerivAt (y : ℝ) : HasDerivAt Real.tanh (scalarVariance y) y := by
  have h := (Real.hasDerivAt_sinh y).div (Real.hasDerivAt_cosh y) (Real.cosh_pos y).ne'
  convert! h using 1
  · ext z; exact Real.tanh_eq_sinh_div_cosh z
  · rw [scalarVariance_eq]
    congr 1
    nlinarith [Real.cosh_sq_sub_sinh_sq y]

lemma tanh_lipschitz (x y : ℝ) : |Real.tanh y - Real.tanh x| ≤ |y-x| := by
  have h := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun z (_ : z ∈ (Set.univ : Set ℝ)) => (tanh_hasDerivAt z).hasDerivWithinAt)
    (fun z _ => (show ‖scalarVariance z‖ ≤ 1 by
      rw [Real.norm_eq_abs, abs_of_pos (scalarVariance_pos z)]
      exact scalarVariance_le_one z)) convex_univ (Set.mem_univ x) (Set.mem_univ y)
  simpa only [one_mul, Real.norm_eq_abs] using h

lemma scalarVariance_lipschitz (x y : ℝ) : |scalarVariance y - scalarVariance x| ≤ 2*|y-x| := by
  have h1 := tanh_lipschitz x y
  have h2 : |Real.tanh y + Real.tanh x| ≤ 2 :=
    (abs_add_le _ _).trans (by linarith [Real.abs_tanh_lt_one x, Real.abs_tanh_lt_one y])
  have he : scalarVariance y - scalarVariance x =
      -(Real.tanh y - Real.tanh x) * (Real.tanh y + Real.tanh x) := by
    unfold scalarVariance
    ring
  rw [he, abs_mul, abs_neg]
  nlinarith [mul_le_mul h1 h2 (abs_nonneg _) (abs_nonneg _)]

lemma tanh_linear_remainder (x y : ℝ) :
    |Real.tanh y - Real.tanh x - scalarVariance x * (y-x)| ≤ 2 * |y-x| ^ 2 := by
  let f (z : ℝ) := Real.tanh z - Real.tanh x - scalarVariance x * (z-x)
  have hd (z : ℝ) : HasDerivAt f (scalarVariance z - scalarVariance x) z := by
    convert! ((tanh_hasDerivAt z).sub_const (Real.tanh x)).sub
      (((hasDerivAt_id z).sub_const x).const_mul (scalarVariance x)) using 1
    all_goals try with_reducible_and_instances rfl
    simp only [mul_one]
  have hb (z : ℝ) (hz : z ∈ segment ℝ x y) : ‖scalarVariance z - scalarVariance x‖ ≤
      2 * |y-x| := by
    have hh : |z-x| ≤ |y-x| := by simpa only [Real.norm_eq_abs] using norm_sub_le_of_mem_segment hz
    simpa only [Real.norm_eq_abs] using (scalarVariance_lipschitz x z).trans
      (mul_le_mul_of_nonneg_left hh (by norm_num))
  have h := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun z (_ : z ∈ segment ℝ x y) => (hd z).hasDerivWithinAt) hb
    (convex_segment x y) (left_mem_segment ℝ x y) (right_mem_segment ℝ x y)
  simpa only [f, sub_self, mul_zero, sub_zero, Real.norm_eq_abs, pow_two, mul_assoc] using h

lemma halfDiff_as_flip {n : ℕ} (f : Observables n) (x : Spin n) (i : Fin n) :
    halfDiff i f x = spin x i * (f x - f (flip x i)) / 2 := by
  have hx := replace_self x i
  cases hi : x i <;> simp only [hi] at hx
  · simp only [spin, hi, Bool.false_eq_true, ↓reduceIte, flip, Bool.not_false, halfDiff]
    rw [hx]; ring
  · simp only [spin, hi, ↓reduceIte, flip, Bool.not_true, halfDiff]
    rw [hx]; ring

lemma abs_spin_eq_one {n : ℕ} (x : Spin n) (i : Fin n) : |spin x i| = 1 := by
  cases hi : x i <;> simp [spin, hi]

end SKGapCutoff

open scoped BigOperators NNReal ENNReal
open MeasureTheory Metric Set

end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Localization_PhiBounds
attribute [-instance] _root_.OAI.SKGap.ComplexMatrix.frobeniusInnerProduct
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open MeasureTheory
namespace SKGap.Stein

lemma phi_zero_diagonal (r : ℝ) : phi r r 0=1/(Real.cosh r)^2 := by
  simp [phi,weight,pow_two]

lemma phi_zero_le_one (z r : ℝ) : phi z r 0≤1 := by
  by_cases h : z=r
  · subst z
    rw [phi_zero_diagonal,←SKGapCutoff.scalarVariance_eq]
    exact SKGapCutoff.scalarVariance_le_one _
  · have H:=phi_stein z r 0
    simp only [zero_mul,sub_zero] at H
    have H':=congrArg abs H
    rw [abs_mul,abs_of_pos (phi_pos z r 0)] at H'
    have hz : 0 < |z-r| := abs_pos.mpr (sub_ne_zero.mpr h)
    have hl:=SKGapCutoff.tanh_lipschitz r z
    nlinarith

lemma weight_le (a u : ℝ) (hu : u∈Set.Icc (0:ℝ) 1) : weight a u≤Real.exp (|a|/2) := by
  unfold weight
  apply Real.exp_le_exp.mpr
  have hu2 : u^2≤1 := by nlinarith [hu.1,hu.2]
  have hm : a*(1-u^2)≤|a| := by
    calc
      _ ≤ |a| *(1-u^2) := mul_le_mul_of_nonneg_right (le_abs_self _) (by linarith)
      _ ≤ |a| *1 := mul_le_mul_of_nonneg_left (by nlinarith [sq_nonneg u]) (abs_nonneg _)
      _ = |a| := mul_one _
  linarith

lemma continuous_integrand (z r a : ℝ) : Continuous (fun u=>
    weight a u*Real.cosh (u*(z-r))/(Real.cosh z*Real.cosh r)) := by
  exact Continuous.div_const ((continuous_weight a).mul (by fun_prop)) _

lemma phi_le_exp (z r a : ℝ) : phi z r a≤Real.exp (|a|/2) := by
  have H:=intervalIntegral.integral_mono_on (μ:=volume) (a:=(0:ℝ)) (b:=1) (by norm_num)
    ((continuous_integrand z r a).intervalIntegrable 0 1)
    (((continuous_integrand z r 0).const_mul (Real.exp (|a|/2))).intervalIntegrable 0 1)
    (by
      intro u hu
      simp only [weight,zero_mul,zero_div,Real.exp_zero,one_mul]
      rw [←mul_div_assoc]
      apply div_le_div_of_nonneg_right _ (le_of_lt (mul_pos (Real.cosh_pos _) (Real.cosh_pos _)))
      exact mul_le_mul_of_nonneg_right (weight_le a u hu) (Real.cosh_pos _).le)
  rw [intervalIntegral.integral_const_mul] at H
  exact H.trans ((mul_le_mul_of_nonneg_left (phi_zero_le_one z r) (Real.exp_pos _).le).trans_eq (mul_one _))

lemma abs_sinh_le_cosh (t : ℝ) : |Real.sinh t|≤Real.cosh t := by
  have h:=Real.cosh_sq_sub_sinh_sq t
  have ha:=sq_abs (Real.sinh t)
  nlinarith [Real.cosh_pos t,abs_nonneg (Real.sinh t)]

lemma numerator_pos (z r a : ℝ) : 0<numerator z r a := by
  have h:=phi_pos z r a
  rw [phi_eq] at h
  exact (div_pos_iff_of_pos_right (mul_pos (Real.cosh_pos z) (Real.cosh_pos r))).mp h

lemma abs_numeratorZ_le (z r a : ℝ) : |numeratorZ z r a|≤numerator z r a := by
  unfold numeratorZ numerator
  apply (intervalIntegral.abs_integral_le_integral_abs (by norm_num : (0:ℝ)≤1)).trans
  apply intervalIntegral.integral_mono_on (by norm_num : (0:ℝ)≤1)
  · exact ((continuous_weight a|>.mul continuous_id).mul (by fun_prop) |>.abs).intervalIntegrable _ _
  · exact ((continuous_weight a).mul (by fun_prop)).intervalIntegrable _ _
  · intro u hu
    rw [abs_mul,abs_mul,abs_of_pos (show 0<weight a u from Real.exp_pos _),abs_of_nonneg hu.1]
    calc
      _ ≤ weight a u*u*Real.cosh (u*(z-r)) :=
        mul_le_mul_of_nonneg_left (abs_sinh_le_cosh _) (mul_nonneg (Real.exp_pos _).le hu.1)
      _ ≤ weight a u*Real.cosh (u*(z-r)) := by
        have H:=mul_le_mul_of_nonneg_left hu.2 (mul_pos (Real.exp_pos (a*(1-u^2)/2)) (Real.cosh_pos (u*(z-r)))).le
        dsimp [weight] at *
        nlinarith only [H]

lemma phiZ_relative_bound (z r a : ℝ) : |phiZ z r a|≤2*phi z r a := by
  unfold phiZ
  apply (abs_sub _ _).trans
  have hd : 0<Real.cosh z*Real.cosh r := mul_pos (Real.cosh_pos _) (Real.cosh_pos _)
  rw [abs_div,abs_of_pos hd,abs_mul,abs_of_pos (phi_pos z r a)]
  have h1:=div_le_div_of_nonneg_right (abs_numeratorZ_le z r a) hd.le
  have h2:=mul_le_mul_of_nonneg_right (Real.abs_tanh_lt_one z).le (phi_pos z r a).le
  rw [←phi_eq] at h1
  nlinarith

lemma numeratorZ_hasDerivAt (z r a : ℝ) :
    HasDerivAt (fun z=>numeratorZ z r a) (numeratorZZ z r a) z := by
  unfold numeratorZ numeratorZZ
  apply hasDerivAt_integral01 (F:=fun z u=>weight a u*u*Real.sinh (u*(z-r)))
    (F':=fun z u=>weight a u*u^2*Real.cosh (u*(z-r)))
  · unfold weight; fun_prop
  · unfold weight; fun_prop
  · intro z u
    convert! ((Real.hasDerivAt_sinh (u*(z-r))).comp z
      (((hasDerivAt_id z).sub_const r).const_mul u)).const_mul (weight a u*u) using 1
    all_goals try with_reducible_and_instances rfl
    ring

lemma numeratorZZ_nonneg (z r a : ℝ) : 0≤numeratorZZ z r a := by
  apply intervalIntegral.integral_nonneg (by norm_num : (0:ℝ)≤1)
  intro u _; exact mul_nonneg (mul_nonneg (Real.exp_pos _).le (sq_nonneg _)) (Real.cosh_pos _).le

lemma numeratorZZ_le (z r a : ℝ) : numeratorZZ z r a≤numerator z r a := by
  apply intervalIntegral.integral_mono_on (by norm_num : (0:ℝ)≤1)
  · apply Continuous.intervalIntegrable; unfold weight; fun_prop
  · exact ((continuous_weight a).mul (by fun_prop)).intervalIntegrable _ _
  · intro u hu
    have hu2 : u^2≤1 := by nlinarith [hu.1,hu.2]
    have H:=mul_le_mul_of_nonneg_left hu2
      (mul_pos (Real.exp_pos (a*(1-u^2)/2)) (Real.cosh_pos (u*(z-r)))).le
    dsimp [weight] at *
    nlinarith only [H]

lemma logSlope_eq (z r a : ℝ) : logSlope z r a=
    numeratorZ z r a/numerator z r a-Real.tanh z := by
  rw [logSlope,phiZ,phi_eq]
  field_simp [ne_of_gt (numerator_pos z r a),ne_of_gt (Real.cosh_pos z),ne_of_gt (Real.cosh_pos r)]

lemma logSlope_hasDerivAt (z r a : ℝ) :
    HasDerivAt (fun z=>logSlope z r a) (logSlopeZ z r a) z := by
  have H:=((numeratorZ_hasDerivAt z r a).div (numerator_hasDerivAt z r a)
    (ne_of_gt (numerator_pos z r a))).sub (SKGapCutoff.tanh_hasDerivAt z)
  convert! H using 1
  · funext x; exact logSlope_eq x r a
  · unfold logSlopeZ
    field_simp [ne_of_gt (numerator_pos z r a)]

lemma logSlopeZ_bound (z r a : ℝ) : |logSlopeZ z r a|≤3 := by
  have hN : 0<numerator z r a := numerator_pos z r a
  have h0 : 0≤numeratorZZ z r a/numerator z r a := div_nonneg (numeratorZZ_nonneg z r a) hN.le
  have h1 : numeratorZZ z r a/numerator z r a≤1 := (div_le_one hN).mpr (numeratorZZ_le z r a)
  have h2 : |numeratorZ z r a/numerator z r a|≤1 := by
    rw [abs_div,abs_of_pos hN]; exact (div_le_one hN).mpr (abs_numeratorZ_le z r a)
  have h3:=pow_le_pow_left₀ (abs_nonneg (numeratorZ z r a/numerator z r a)) h2 2
  rw [sq_abs,one_pow] at h3
  rw [logSlopeZ,abs_le]
  constructor <;> nlinarith [SKGapCutoff.scalarVariance_pos z,SKGapCutoff.scalarVariance_le_one z,
    sq_nonneg (numeratorZ z r a/numerator z r a)]

lemma logSlope_lipschitz (z z' r a : ℝ) : |logSlope z' r a-logSlope z r a|≤3*|z'-z| := by
  have H:=Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun q (_ : q∈(Set.univ : Set ℝ))=>(logSlope_hasDerivAt q r a).hasDerivWithinAt)
    (fun q _=>show ‖logSlopeZ q r a‖≤3 by simpa only [Real.norm_eq_abs] using logSlopeZ_bound q r a)
    convex_univ (Set.mem_univ z) (Set.mem_univ z')
  simpa only [Real.norm_eq_abs] using H

lemma logSlope_diagonal (r a : ℝ) : logSlope r r a= -Real.tanh r := by
  rw [logSlope,phiZ_at_diagonal]
  exact mul_div_cancel_right₀ _ (ne_of_gt (phi_pos r r a))

theorem logSlope_near_diagonal (z r a : ℝ) : |logSlope z r a+Real.tanh r|≤3*|z-r| := by
  simpa only [logSlope_diagonal,sub_neg_eq_add] using logSlope_lipschitz r z r a

end SKGap.Stein

end
end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Gaussian_PhiMoments
attribute [-instance] _root_.OAI.SKGap.ComplexMatrix.frobeniusInnerProduct
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open MeasureTheory
namespace SKGap.Stein

lemma continuous_hyper (b : Bool) : Continuous (hyper b) := by unfold hyper; split_ifs <;> fun_prop
lemma hyper_hasDerivAt (b : Bool) (x : ℝ) : HasDerivAt (hyper b) (hyper (!b) x) x := by
  cases b <;> simpa only [hyper,Bool.not_false,Bool.not_true,Bool.false_eq_true,ite_false,ite_true] using
    (show HasDerivAt _ _ x from (by first | exact Real.hasDerivAt_cosh x | exact Real.hasDerivAt_sinh x))

lemma moment_base (z r a : ℝ) : moment 0 0 false z r a=phi z r a := by
  rw [phi_eq]
  simp only [moment,momentNum,numerator,pow_zero,mul_one,hyper,Bool.false_eq_true,ite_false]

lemma momentNum_hasDerivAt_d (p q : ℕ) (b : Bool) (d a : ℝ) :
    HasDerivAt (fun d=>momentNum p q b d a) (momentNum (p+1) q (!b) d a) d := by
  unfold momentNum
  apply hasDerivAt_integral01
    (F:=fun d u=>weight a u*u^p*((1-u^2)/2)^q*hyper b (u*d))
    (F':=fun d u=>weight a u*u^(p+1)*((1-u^2)/2)^q*hyper (!b) (u*d))
  · exact (((continuous_weight a).comp continuous_snd).mul (continuous_snd.pow p)|>.mul
      (((continuous_const.sub (continuous_snd.pow 2)).div_const 2).pow q)).mul
      ((continuous_hyper b).comp (continuous_snd.mul continuous_fst))
  · exact (((continuous_weight a).comp continuous_snd).mul (continuous_snd.pow (p+1))|>.mul
      (((continuous_const.sub (continuous_snd.pow 2)).div_const 2).pow q)).mul
      ((continuous_hyper (!b)).comp (continuous_snd.mul continuous_fst))
  · intro d u
    have H:=((hyper_hasDerivAt b (u*d)).comp d ((hasDerivAt_id d).const_mul u)).const_mul
      (weight a u*u^p*((1-u^2)/2)^q)
    convert! H using 1
    all_goals try with_reducible_and_instances rfl
    simp only [pow_succ]
    ring

lemma moment_hasDerivAt_z (p q : ℕ) (b : Bool) (z r a : ℝ) :
    HasDerivAt (fun z=>moment p q b z r a)
      (moment (p+1) q (!b) z r a-Real.tanh z*moment p q b z r a) z := by
  have H:=((momentNum_hasDerivAt_d p q b (z-r) a).comp z ((hasDerivAt_id z).sub_const r)).div
    ((Real.hasDerivAt_cosh z).mul_const (Real.cosh r))
    (ne_of_gt (mul_pos (Real.cosh_pos _) (Real.cosh_pos _)))
  convert! H using 1
  all_goals try with_reducible_and_instances rfl
  dsimp [moment]
  rw [Real.tanh_eq_sinh_div_cosh]
  field_simp [ne_of_gt (Real.cosh_pos z),ne_of_gt (Real.cosh_pos r)]

end SKGap.Stein

end
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

lemma hasDerivAt_z (f : KernelExpr) (z r a : ℝ) :
    HasDerivAt (fun z => eval f z r a) (eval (dz f) z r a) z := by
  induction f with
  | atom p q b  =>  simpa only [eval,dz,neg_mul,one_mul,←sub_eq_add_neg] using moment_hasDerivAt_z p q b z r a
  | add f g hf hg  =>  exact hf.add hg
  | scale c f hf  =>  exact hf.const_mul c
  | tz f hf  =>
    convert! (SKGapCutoff.tanh_hasDerivAt z).mul hf using 1
    all_goals try with_reducible_and_instances rfl
    dsimp only [eval,dz,SKGapCutoff.scalarVariance]
    ring
  | tr f hf  =>  exact hf.const_mul _

end KernelExpr

end SKGap.Stein

end
end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Stability_StableFields
attribute [-instance] _root_.OAI.SKGap.ComplexMatrix.frobeniusInnerProduct
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped BigOperators
open Real Matrix
namespace SKGap

theorem overlap_nonneg {n : ℕ} (y : Field n) : 0 ≤ overlap y :=
  div_nonneg (Finset.sum_nonneg (fun _ _ => sq_nonneg _)) (Nat.cast_nonneg _)

theorem overlap_lt_one {n : ℕ} (hn : 0 < n) (y : Field n) : overlap y < 1 := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  apply (div_lt_iff₀ hn').mpr
  simp only [one_mul]
  calc
    (∑ i, magnetization y i ^ 2) < ∑ _ : Fin n, (1 : ℝ) := by
      apply Finset.sum_lt_sum_of_nonempty
      · exact Finset.univ_nonempty_iff.mpr ⟨⟨0, hn⟩⟩
      · intro i _
        exact tanh_sq_lt_one (y i)
    _ = n := by simp

theorem spinVariance_pos {n : ℕ} (y : Field n) (i : Fin n) :
    0 < spinVariance y i := sub_pos.mpr (tanh_sq_lt_one _)

theorem spinVariance_le_one {n : ℕ} (y : Field n) (i : Fin n) :
    spinVariance y i ≤ 1 := sub_le_self _ (sq_nonneg _)

theorem magnetization_hasFDerivAt {n : ℕ} (y : Field n) (i : Fin n) :
    HasFDerivAt (fun z : Field n => magnetization z i)
      (spinVariance y i • (ContinuousLinearMap.proj i : Field n →L[ℝ] ℝ)) y :=
  (hasDerivAt_tanh (y i)).comp_hasFDerivAt y (hasFDerivAt_apply i y)

theorem overlap_hasFDerivAt {n : ℕ} (y : Field n) :
    HasFDerivAt overlap (overlapDerivative y) y := by
  have hd := (HasFDerivAt.sum (u := Finset.univ)
    (fun k _ => (magnetization_hasFDerivAt y k).pow 2)).const_mul (n : ℝ)⁻¹
  convert! hd using 1
  · ext z
    simp only [overlap, Finset.sum_apply, div_eq_mul_inv]
    ring
  · ext v
    simp only [overlapDerivative, _root_.smul_apply,
      _root_.sum_apply, ContinuousLinearMap.proj_apply,
      smul_eq_mul, Nat.cast_ofNat, Nat.reduceSub, pow_one,
      nsmul_eq_mul]
    simp_rw [mul_assoc]
    rw [← Finset.mul_sum]
    ring

theorem onsager_hasFDerivAt {n : ℕ} (j : ℝ) (y : Field n) :
    HasFDerivAt (onsager j) (-j • overlapDerivative y) y := by
  convert! ((overlap_hasFDerivAt y).const_sub 1).const_mul j using 1
  all_goals try with_reducible_and_instances rfl
  ext v
  simp only [_root_.smul_apply, smul_eq_mul, _root_.neg_apply]
  ring

theorem tapField_hasFDerivAt {n : ℕ} (j : ℝ)
    (J : Matrix (Fin n) (Fin n) ℝ) (h y : Field n) :
    HasFDerivAt (tapField j J h)
      ((fieldJacobian j J y).mulVecLin.toContinuousLinearMap) y := by
  rw [hasFDerivAt_pi']
  intro i
  have hfirst := ((hasFDerivAt_apply i y).sub_const (h i)).add
    ((onsager_hasFDerivAt j y).mul (magnetization_hasFDerivAt y i))
  have hlast := HasFDerivAt.sum (u := Finset.univ)
    (fun k _ => (magnetization_hasFDerivAt y k).const_mul (J i k))
  convert! hfirst.sub hlast using 1
  · ext z
    simp only [tapField, Pi.sub_apply, Pi.add_apply, Pi.mul_apply, Finset.sum_apply]
  · ext v
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.proj_apply,
      LinearMap.coe_toContinuousLinearMap', Matrix.mulVecLin_apply, Matrix.mulVec,
      dotProduct, fieldJacobian, hessianCore, _root_.sub_apply,
      _root_.add_apply, _root_.smul_apply,
      _root_.sum_apply, smul_eq_mul, overlapDerivative]
    have hdelta : (∑ k : Fin n, (if i = k then 1 else (0 : ℝ)) * v k) = v i := by
      simp
    have hdeltaV : (∑ k : Fin n, (if i = k then 1 else (0 : ℝ)) *
        spinVariance y k * v k) = spinVariance y i * v i := by simp
    calc
      _ = (∑ k : Fin n, (if i = k then 1 else (0 : ℝ)) * v k) +
          onsager j y * (∑ k : Fin n, (if i = k then 1 else (0 : ℝ)) *
            spinVariance y k * v k) -
          (∑ k, J i k * (spinVariance y k * v k)) -
          (2 * j / n) * magnetization y i *
            (∑ k, (magnetization y k * spinVariance y k) * v k) := by
        simp only [Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro k _
        ring
      _ = _ := by
        rw [hdelta, hdeltaV]
        ring

theorem fieldHessian_variance_intertwine {n : ℕ} (j : ℝ)
    (J : Matrix (Fin n) (Fin n) ℝ) (y : Field n) (i k : Fin n) :
    fieldHessian j J y (spinVariance y) i k * sqrt (spinVariance y k) =
      sqrt (spinVariance y i) * fieldJacobian j J y i k := by
  have hk := sq_sqrt (spinVariance_pos y k).le
  by_cases hik : i = k
  · subst k
    simp only [fieldHessian, fieldJacobian, ↓reduceIte]
    nlinarith only [congrArg (fun z => sqrt (spinVariance y i) * hessianCore j J y i i * z) hk]
  · simp only [fieldHessian, fieldJacobian, ite_eq_right hik, zero_add]
    nlinarith only [congrArg (fun z => sqrt (spinVariance y i) * hessianCore j J y i k * z) hk]

theorem fieldHessian_variance_mulVec {n : ℕ} (j : ℝ)
    (J : Matrix (Fin n) (Fin n) ℝ) (y v : Field n) :
    (fieldHessian j J y (spinVariance y)).mulVec
      (fun k => sqrt (spinVariance y k) * v k) =
    fun i => sqrt (spinVariance y i) * (fieldJacobian j J y).mulVec v i := by
  ext i
  simp only [Matrix.mulVec, dotProduct, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k _
  rw [← mul_assoc, fieldHessian_variance_intertwine]
  ring

theorem quadraticForm_eq_dot_mulVec {n : ℕ}
    (J : Matrix (Fin n) (Fin n) ℝ) (x : Field n) :
    quadraticForm J x = ∑ i, x i * J.mulVec x i := by
  simp only [quadraticForm, Matrix.mulVec, dotProduct, Finset.mul_sum, mul_assoc]

theorem vectorNorm_nonneg {n : ℕ} (x : Field n) : 0 ≤ vectorNorm x := norm_nonneg _

theorem vectorNorm_sq {n : ℕ} (x : Field n) : vectorNorm x ^ 2 = vectorSqNorm x := by
  exact EuclideanSpace.real_norm_sq_eq (WithLp.toLp 2 x)

theorem vectorNorm_add_le {n : ℕ} (x z : Field n) :
    vectorNorm (x + z) ≤ vectorNorm x + vectorNorm z := by
  exact norm_add_le (WithLp.toLp 2 x : EuclideanSpace ℝ (Fin n)) (WithLp.toLp 2 z)

theorem vectorNorm_sub_le {n : ℕ} (x z : Field n) :
    vectorNorm (x - z) ≤ vectorNorm x + vectorNorm z := by
  exact norm_sub_le (WithLp.toLp 2 x : EuclideanSpace ℝ (Fin n)) (WithLp.toLp 2 z)

theorem vectorNorm_smul {n : ℕ} (a : ℝ) (x : Field n) :
    vectorNorm (fun i => a * x i) = |a| * vectorNorm x := by
  exact norm_smul a (WithLp.toLp 2 x : EuclideanSpace ℝ (Fin n))

theorem vector_dot_abs_le {n : ℕ} (x z : Field n) :
    |∑ i, x i * z i| ≤ vectorNorm x * vectorNorm z := by
  simpa only [vectorNorm, PiLp.inner_apply, RCLike.inner_apply, conj_trivial,
    PiLp.toLp_apply, mul_comm] using
    abs_real_inner_le_norm (WithLp.toLp 2 x : EuclideanSpace ℝ (Fin n)) (WithLp.toLp 2 z)

theorem vectorNorm_diag_le {n : ℕ} {a : Field n} {M : ℝ} (hM : 0 ≤ M)
    (ha : ∀ i, |a i| ≤ M) (x : Field n) :
    vectorNorm (fun i => a i * x i) ≤ M * vectorNorm x := by
  apply (sq_le_sq₀ (vectorNorm_nonneg _) (mul_nonneg hM (vectorNorm_nonneg _))).mp
  rw [mul_pow, vectorNorm_sq, vectorNorm_sq]
  unfold vectorSqNorm
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i _
  rw [mul_pow]
  have hi : a i ^ 2 ≤ M ^ 2 := by
    simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg (a i)) hM).mpr (ha i)
  exact mul_le_mul_of_nonneg_right hi (sq_nonneg (x i))

theorem sqrtVarianceMul_norm_le {n : ℕ} (y v : Field n) :
    vectorNorm (sqrtVarianceMul y v) ≤ vectorNorm v := by
  change vectorNorm (fun i => sqrt (spinVariance y i) * v i) ≤ vectorNorm v
  calc
    _ ≤ 1 * vectorNorm v := vectorNorm_diag_le zero_le_one (fun i => by
      rw [abs_of_nonneg (sqrt_nonneg _)]
      exact sqrt_le_one.mpr (spinVariance_le_one y i)) v
    _ = _ := one_mul _

theorem sqrtVarianceMul_twice {n : ℕ} (y v : Field n) :
    sqrtVarianceMul y (sqrtVarianceMul y v) = fun i => spinVariance y i * v i := by
  ext i
  dsimp [sqrtVarianceMul]
  rw [← mul_assoc, mul_self_sqrt (spinVariance_pos y i).le]

theorem weighted_inverse_bound {n : ℕ} {c j : ℝ} (_hc : 0 < c)
    (J : Matrix (Fin n) (Fin n) ℝ) (y v : Field n)
    (hH : ∀ x : Field n, c * vectorSqNorm x ≤
      quadraticForm (fieldHessian j J y (spinVariance y)) x) :
    c * vectorNorm (sqrtVarianceMul y v) ≤
      vectorNorm ((fieldJacobian j J y).mulVec v) := by
  let w := sqrtVarianceMul y v
  let z := (fieldJacobian j J y).mulVec v
  have hi : (fieldHessian j J y (spinVariance y)).mulVec w = sqrtVarianceMul y z :=
    fieldHessian_variance_mulVec j J y v
  have hq := hH w
  rw [quadraticForm_eq_dot_mulVec, hi] at hq
  have hdot := (le_abs_self (∑ i, w i * sqrtVarianceMul y z i)).trans
    (vector_dot_abs_le w (sqrtVarianceMul y z))
  have hz := mul_le_mul_of_nonneg_left (sqrtVarianceMul_norm_le y z) (vectorNorm_nonneg w)
  rw [← vectorNorm_sq] at hq
  change c * vectorNorm w ≤ vectorNorm z
  by_cases hw : vectorNorm w = 0
  · rw [hw, mul_zero]
    exact vectorNorm_nonneg z
  · have hw' : 0 < vectorNorm w := lt_of_le_of_ne (vectorNorm_nonneg w) (Ne.symm hw)
    nlinarith [hq.trans (hdot.trans hz)]

theorem hessianCore_mulVec {n : ℕ} (j : ℝ)
    (J : Matrix (Fin n) (Fin n) ℝ) (y v : Field n) :
    (hessianCore j J y).mulVec v =
      (fun i => onsager j y * v i) - J.mulVec v -
      (fun i => ((2 * j / n) * (∑ k, magnetization y k * v k)) * magnetization y i) := by
  ext i
  change (∑ k, hessianCore j J y i k * v k) =
    onsager j y * v i - (∑ k, J i k * v k) -
      ((2 * j / n) * (∑ k, magnetization y k * v k)) * magnetization y i
  calc
    _ = ∑ k, (onsager j y * ((if i = k then 1 else 0) * v k) - J i k * v k -
        ((2 * j / n) * magnetization y i) * (magnetization y k * v k)) := by
      apply Finset.sum_congr rfl
      intro k _
      simp only [hessianCore]
      ring
    _ = _ := by
      simp only [Finset.sum_sub_distrib, ← Finset.mul_sum]
      simp
      ring

attribute [local irreducible] vectorNorm

theorem hessianCore_norm_le {n : ℕ} (hn : 0 < n) {j K : ℝ} (hj : 0 ≤ j)
    (J : Matrix (Fin n) (Fin n) ℝ) (y v : Field n)
    (hJ : ∀ z : Field n, vectorNorm (J.mulVec z) ≤ K * vectorNorm z) :
    vectorNorm ((hessianCore j J y).mulVec v) ≤ (K + 3 * j) * vectorNorm v := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hq0 := overlap_nonneg y
  have hq1 := (overlap_lt_one hn y).le
  have hB0 : 0 ≤ onsager j y := mul_nonneg hj (sub_nonneg.mpr hq1)
  have hB : onsager j y ≤ j := by
    dsimp [onsager]
    nlinarith
  have hfirst : vectorNorm (fun i => onsager j y * v i) ≤ j * vectorNorm v := by
    rw [vectorNorm_smul, abs_of_nonneg hB0]
    exact mul_le_mul_of_nonneg_right hB (vectorNorm_nonneg v)
  have hm : vectorNorm (magnetization y) ^ 2 = (n : ℝ) * overlap y := by
    rw [vectorNorm_sq]
    dsimp [vectorSqNorm, overlap]
    field_simp
  have hm_bound : vectorNorm (magnetization y) ^ 2 ≤ n := by nlinarith
  have hs : 0 ≤ 2 * j / (n : ℝ) := by positivity
  have hcs := vector_dot_abs_le (magnetization y) v
  have hrank : vectorNorm (fun i => ((2 * j / n) *
      (∑ k, magnetization y k * v k)) * magnetization y i) ≤ 2 * j * vectorNorm v := by
    rw [vectorNorm_smul, abs_mul, abs_of_nonneg hs]
    calc
      _ ≤ ((2 * j / n) * (vectorNorm (magnetization y) * vectorNorm v)) *
          vectorNorm (magnetization y) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hcs hs)
          (vectorNorm_nonneg _)
      _ = (2 * j / n) * vectorNorm (magnetization y) ^ 2 * vectorNorm v := by ring
      _ ≤ (2 * j / n) * n * vectorNorm v :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hm_bound hs)
          (vectorNorm_nonneg _)
      _ = _ := by field_simp
  rw [hessianCore_mulVec]
  calc
    _ ≤ vectorNorm ((fun i => onsager j y * v i) - J.mulVec v) +
        vectorNorm (fun i => ((2 * j / n) * (∑ k, magnetization y k * v k)) *
          magnetization y i) := vectorNorm_sub_le _ _
    _ ≤ (vectorNorm (fun i => onsager j y * v i) + vectorNorm (J.mulVec v)) +
        vectorNorm (fun i => ((2 * j / n) * (∑ k, magnetization y k * v k)) *
          magnetization y i) := add_le_add (vectorNorm_sub_le _ _) le_rfl
    _ ≤ (j * vectorNorm v + K * vectorNorm v) + 2 * j * vectorNorm v :=
      add_le_add (add_le_add hfirst (hJ v)) hrank
    _ = _ := by ring

theorem fieldJacobian_mulVec {n : ℕ} (j : ℝ)
    (J : Matrix (Fin n) (Fin n) ℝ) (y v : Field n) :
    (fieldJacobian j J y).mulVec v = v +
      (hessianCore j J y).mulVec (fun i => spinVariance y i * v i) := by
  ext i
  simp only [Matrix.mulVec, dotProduct, fieldJacobian, add_mul,
    Finset.sum_add_distrib, Pi.add_apply, mul_assoc]
  simp

theorem fieldJacobian_inverse_bound {n : ℕ} (hn : 0 < n) {c j K : ℝ}
    (hc : 0 < c) (hj : 0 ≤ j) (hK : 0 ≤ K)
    (J : Matrix (Fin n) (Fin n) ℝ) (y v : Field n)
    (hJ : ∀ z : Field n, vectorNorm (J.mulVec z) ≤ K * vectorNorm z)
    (hH : ∀ x : Field n, c * vectorSqNorm x ≤
      quadraticForm (fieldHessian j J y (spinVariance y)) x) :
    vectorNorm v ≤ (1 + (K + 3 * j) / c) *
      vectorNorm ((fieldJacobian j J y).mulVec v) := by
  let z := (fieldJacobian j J y).mulVec v
  let w : Field n := fun i => spinVariance y i * v i
  have hw : vectorNorm w ≤ vectorNorm (sqrtVarianceMul y v) := by
    simpa only [sqrtVarianceMul_twice] using sqrtVarianceMul_norm_le y (sqrtVarianceMul y v)
  have hcv : c * vectorNorm w ≤ vectorNorm z :=
    (mul_le_mul_of_nonneg_left hw hc.le).trans (weighted_inverse_bound hc J y v hH)
  have hv : vectorNorm w ≤ vectorNorm z / c := (le_div_iff₀ hc).mpr (by
    simpa only [mul_comm] using hcv)
  have he : v = z - (hessianCore j J y).mulVec w := by
    have hid := fieldJacobian_mulVec j J y v
    change z = v + (hessianCore j J y).mulVec w at hid
    rw [hid, add_sub_cancel_right]
  have hL := hessianCore_norm_le hn hj J y w hJ
  have hD : 0 ≤ K + 3 * j := by positivity
  calc
    vectorNorm v ≤ vectorNorm z + vectorNorm ((hessianCore j J y).mulVec w) := by
      conv_lhs => rw [he]
      exact vectorNorm_sub_le _ _
    _ ≤ vectorNorm z + (K + 3 * j) * vectorNorm w := add_le_add le_rfl hL
    _ ≤ vectorNorm z + (K + 3 * j) * (vectorNorm z / c) :=
      add_le_add le_rfl (mul_le_mul_of_nonneg_left hv hD)
    _ = (1 + (K + 3 * j) / c) * vectorNorm z := by ring

end SKGap
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
-- module Solutions.OAIQ072_SK.SKGap_Gaussian_SquaredGaussianFourth
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
open scoped BigOperators NNReal ENNReal
open MeasureTheory Metric Set
open scoped BigOperators NNReal ENNReal
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators NNReal ENNReal Matrix.Norms.L2Operator
open MeasureTheory ProbabilityTheory Filter Set
namespace SKGapCutoff.RandomMatrix

lemma matrix_opNorm_sq_le_frobenius {n : ℕ} (A : Interaction n) :
    ‖Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) A‖^2 ≤ ∑ i, ∑ j, A i j^2 := by
  let S := ∑ i, ∑ j, A i j^2
  have hS : 0 ≤ S := by unfold S; positivity
  have hN : ‖Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) A‖ ≤ Real.sqrt S := by
    apply ContinuousLinearMap.opNorm_le_bound _ (Real.sqrt_nonneg _)
    intro x
    apply (sq_le_sq₀ (norm_nonneg _) (by positivity : 0 ≤ Real.sqrt S * ‖x‖)).mp
    rw [mul_pow, Real.sq_sqrt hS]
    rw [EuclideanSpace.real_norm_sq_eq, EuclideanSpace.real_norm_sq_eq]
    change ∑ i, (∑ j, A i j*x j)^2 ≤ S * ∑ j, x j^2
    calc
      _ ≤ ∑ i, (∑ j, A i j^2)*(∑ j, x j^2) :=
        Finset.sum_le_sum (fun i _ => Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (A i) x)
      _ = _ := by rw [← Finset.sum_mul]
  exact (pow_le_pow_left₀ (norm_nonneg _) hN 2).trans_eq (Real.sq_sqrt hS)

end SKGapCutoff.RandomMatrix

open scoped BigOperators Matrix.Norms.L2Operator
open MeasureTheory ProbabilityTheory Filter Set

end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Localization_PreparationGrowth
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
open scoped BigOperators NNReal ENNReal
open MeasureTheory Metric Set
open scoped BigOperators NNReal ENNReal
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators NNReal ENNReal Matrix.Norms.L2Operator
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Matrix.Norms.L2Operator
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Matrix Matrix.Norms.Elementwise
open MeasureTheory ProbabilityTheory Filter Set
open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators ENNReal NNReal
open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators NNReal ENNReal Matrix
open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators ENNReal NNReal
open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators NNReal ENNReal
open scoped BigOperators
open MeasureTheory ProbabilityTheory
open scoped BigOperators Matrix Matrix.Norms.Elementwise NNReal ENNReal
open scoped BigOperators
open Filter Topology
open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal BigOperators Topology
open MeasureTheory ProbabilityTheory Filter
open Matrix
open scoped NNReal ENNReal BigOperators Topology Matrix.Norms.Elementwise
open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators NNReal ENNReal Topology
open MeasureTheory ProbabilityTheory Filter Matrix
open scoped NNReal ENNReal BigOperators Topology
open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators NNReal ENNReal Topology
open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal BigOperators Topology
open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal BigOperators Topology
open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal BigOperators Topology
open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal BigOperators Topology
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal Topology
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology BigOperators
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology BigOperators
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology BigOperators
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology BigOperators
open MeasureTheory ProbabilityTheory Filter Matrix
open scoped NNReal ENNReal BigOperators Topology
open MeasureTheory ProbabilityTheory Filter Matrix
open scoped NNReal ENNReal BigOperators Topology
open MeasureTheory ProbabilityTheory Filter Matrix
open scoped NNReal ENNReal BigOperators Topology
open MeasureTheory ProbabilityTheory Filter Matrix
open scoped NNReal ENNReal BigOperators Topology
open MeasureTheory ProbabilityTheory Filter Matrix
open scoped NNReal ENNReal BigOperators Topology
open MeasureTheory ProbabilityTheory Filter Matrix
open scoped NNReal ENNReal BigOperators Topology Matrix Matrix.Norms.Elementwise
open MeasureTheory ProbabilityTheory Filter Matrix
open scoped NNReal ENNReal BigOperators Topology Matrix Matrix.Norms.Elementwise
open MeasureTheory ProbabilityTheory Filter Matrix
open scoped NNReal ENNReal BigOperators Topology Matrix Matrix.Norms.Elementwise
open MeasureTheory ProbabilityTheory Filter Matrix
open scoped NNReal ENNReal BigOperators Topology Matrix Matrix.Norms.Elementwise
open MeasureTheory ProbabilityTheory Filter Matrix
open scoped NNReal ENNReal BigOperators Topology Matrix Matrix.Norms.Elementwise
open MeasureTheory ProbabilityTheory Filter Matrix
open scoped NNReal ENNReal BigOperators Topology Matrix Matrix.Norms.Elementwise
open MeasureTheory ProbabilityTheory Filter Matrix
open scoped NNReal ENNReal BigOperators Topology Matrix Matrix.Norms.Elementwise
open MeasureTheory ProbabilityTheory Filter Set Matrix
open scoped BigOperators NNReal ENNReal Matrix.Norms.L2Operator
open MeasureTheory ProbabilityTheory Filter Matrix
open scoped NNReal ENNReal BigOperators Topology Matrix Matrix.Norms.Elementwise
open MeasureTheory ProbabilityTheory Filter Matrix
open scoped NNReal ENNReal BigOperators Topology Matrix Matrix.Norms.Elementwise
open MeasureTheory ProbabilityTheory Filter Matrix
open scoped NNReal ENNReal BigOperators Topology Matrix Matrix.Norms.Elementwise
open MeasureTheory ProbabilityTheory Filter Matrix
open scoped NNReal ENNReal BigOperators Topology Matrix Matrix.Norms.Elementwise
open MeasureTheory ProbabilityTheory Filter Matrix
open scoped NNReal ENNReal BigOperators Topology Matrix Matrix.Norms.Elementwise
open Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal
open Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal
open MeasureTheory Filter
open scoped Topology NNReal ENNReal
open MeasureTheory Filter ProbabilityTheory
open scoped Topology NNReal ENNReal
open MeasureTheory Filter
open scoped Topology
open MeasureTheory Filter ProbabilityTheory
open scoped Topology NNReal ENNReal
open MeasureTheory Filter ProbabilityTheory
open scoped Topology NNReal ENNReal
open MeasureTheory Filter ProbabilityTheory
open scoped Topology NNReal ENNReal
open MeasureTheory Filter ProbabilityTheory
open scoped Topology NNReal ENNReal
open MeasureTheory Filter ProbabilityTheory ContinuousLinearMap
open scoped Topology NNReal ENNReal
open Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal
open MeasureTheory Filter
open scoped BigOperators Topology
open MeasureTheory Filter
open scoped BigOperators Topology
open MeasureTheory Filter
open scoped BigOperators Topology
open MeasureTheory Filter
open scoped BigOperators Topology
open MeasureTheory Filter
open scoped BigOperators Topology
open Filter Set Metric
open scoped Topology RealInnerProductSpace
open scoped BigOperators
open ContinuousLinearMap
open scoped BigOperators
open ContinuousLinearMap
namespace SKGapCutoff

lemma refreshField_flip {n : ℕ} (H : VectorFields n) (x : Spin n) (i j : Fin n) :
    H (flip x i) j = H x j - 2*spin x i*halfDiff i (fun y => H y j) x := by
  have h := flip_sub i (fun y => H y j) x
  linarith

lemma refreshField_abs_change {n : ℕ} (H : VectorFields n) (x : Spin n) (i j : Fin n) :
    |H x j-H (flip x i) j| = 2*|halfDiff i (fun y => H y j) x| := by
  rw [refreshField_flip H x i j]
  ring_nf
  simp [abs_mul, abs_spin_eq_one, mul_comm]

lemma refreshInfluence_error_le {n : ℕ} (H : VectorFields n) (x : Spin n) (i j : Fin n) :
    |refreshInfluence (fun y k => Real.tanh (H y k)) x i j -
      halfDiff i (fun y => H y j) x*scalarVariance (H x j)| ≤
        4*(halfDiff i (fun y => H y j) x)^2 := by
  have hr := tanh_linear_remainder (H x j) (H (flip x i) j)
  have he : refreshInfluence (fun y k => Real.tanh (H y k)) x i j -
      halfDiff i (fun y => H y j) x*scalarVariance (H x j) =
      -(spin x i/2)*(Real.tanh (H (flip x i) j)-Real.tanh (H x j)-
        scalarVariance (H x j)*(H (flip x i) j-H x j)) := by
    simp only [refreshInfluence, halfDiff_as_flip]
    ring
  rw [he, abs_mul, abs_neg, abs_div, abs_spin_eq_one]
  norm_num only [abs_of_pos (show (0:ℝ)<2 by norm_num)]
  have ha : |H (flip x i) j-H x j| = 2*|halfDiff i (fun y => H y j) x| := by
    rw [abs_sub_comm, refreshField_abs_change]
  rw [ha] at hr
  nlinarith [sq_abs (halfDiff i (fun y => H y j) x)]

open RandomMatrix

end SKGapCutoff
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
local instance instFactLeENNRealOfNat_solutions : Fact (1≤(4:ENNReal)) := ⟨by norm_num⟩

lemma opNorm_eq (M : Interaction n) :
    SKGap.opNorm M = ‖Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) M‖ := rfl

lemma opNorm_le_frobenius (M : Interaction n) : SKGap.opNorm M ≤ ‖M‖ := by
  apply nonneg_le_nonneg_of_sq_le_sq (norm_nonneg M)
  simp only [← sq]
  rw [SKGap.frobenius_sq,opNorm_eq]
  exact RandomMatrix.matrix_opNorm_sq_le_frobenius M

lemma opNorm_add (M N : Interaction n) : SKGap.opNorm (M+N) ≤ SKGap.opNorm M+SKGap.opNorm N := by
  simp only [opNorm_eq,map_add]
  exact norm_add_le _ _

lemma opNorm_smul (c : ℝ) (M : Interaction n) : SKGap.opNorm (c • M) = |c| * SKGap.opNorm M := by
  simp only [opNorm_eq,map_smul,norm_smul,Real.norm_eq_abs]

lemma ShapeBound.mono {M : Interaction n} {C D : ℝ} (h : ShapeBound M C) (hCD : C≤D) :
    ShapeBound M D := ⟨h.1.trans hCD,h.2.1.trans hCD,h.2.2.trans hCD⟩

lemma ShapeBound.add {M N : Interaction n} {C D : ℝ}
    (hM : ShapeBound M C) (hN : ShapeBound N D) : ShapeBound (M+N) (C+D) := by
  exact ⟨(opNorm_add M N).trans (add_le_add hM.1 hN.1),
    (SKGap.diagonalSeminorm_add M N).trans (add_le_add hM.2.1 hN.2.1),
    (SKGap.offDiagonalSeminorm_add M N).trans (add_le_add hM.2.2 hN.2.2)⟩

lemma shapeBound_of_frobenius {M : Interaction n} {C : ℝ} (h : ‖M‖≤C) : ShapeBound M C :=
  ⟨(opNorm_le_frobenius M).trans h,(SKGap.diagonalSeminorm_le M).trans h,
    (SKGap.offDiagonalSeminorm_le M).trans h⟩

lemma ShapeBound.perturb {M H : Interaction n} {C E : ℝ}
    (hH : ShapeBound H C) (hE : ‖M-H‖≤E) : ShapeBound M (C+E) := by
  simpa only [add_sub_cancel] using hH.add (shapeBound_of_frobenius hE)

lemma fourth_sum (M : Interaction n) :
    (∑ i,∑ k,(M i k)^4) = (∑ i,(M i i)^4)+SKGap.offDiagonalSeminorm M^4 := by
  rw [SKGap.offDiagonalSeminorm_fourth,Fintype.sum_prod_type,← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  have hs : (M i i)^4 = ∑ k : Fin n, if i=k then (M i k)^4 else 0 := by simp
  rw [hs,← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro k _
  by_cases h : i=k <;> simp [h]

lemma fourth_sum_le {M : Interaction n} {C : ℝ} (hC : 0≤C) (hM : ShapeBound M C) :
    (∑ i,∑ k,(M i k)^4) ≤ 2*C^4 := by
  rw [fourth_sum]
  have hd : (∑ i,(M i i)^4) ≤ SKGap.diagonalSeminorm M^4 := by
    rw [show (4:ℕ)=2*2 by rfl,pow_mul,SKGap.diagonalSeminorm_sq]
    simpa only [pow_mul] using
      (Finset.sum_sq_le_sq_sum_of_nonneg (s:=Finset.univ) (f:=fun i => (M i i)^2)
        (fun i _ => sq_nonneg _))
  have hdC := (pow_le_pow_iff_left₀ (norm_nonneg (SKGap.diagonalVector M)) hC
    (by decide : 4 ≠ 0)).2 hM.2.1
  have hoC := pow_le_pow_left₀ (norm_nonneg (SKGap.offDiagonalVector M)) hM.2.2 4
  dsimp only [SKGap.diagonalSeminorm,SKGap.offDiagonalSeminorm] at hd ⊢
  nlinarith

lemma quadratic_entry_error {D R : Interaction n} {C A : ℝ} (hC : 0≤C) (hA : 0≤A)
    (hD : ShapeBound D C) (he : ∀ i k, |R i k|≤A*(D i k)^2) :
    ‖R‖ ≤ 2*A*C^2 := by
  have hs : ‖R‖^2 ≤ A^2*(2*C^4) := by
    rw [SKGap.frobenius_sq]
    calc
      _ ≤ ∑ i,∑ k,A^2*(D i k)^4 := by
        apply Finset.sum_le_sum
        intro i _
        apply Finset.sum_le_sum
        intro k _
        have h := pow_le_pow_left₀ (abs_nonneg (R i k)) (he i k) 2
        nlinarith only [h,sq_abs (R i k)]
      _ = A^2*(∑ i,∑ k,(D i k)^4) := by simp_rw [← Finset.mul_sum]
      _ ≤ A^2*(2*C^4) := mul_le_mul_of_nonneg_left (fourth_sum_le hC hD) (sq_nonneg _)
  have hp : 0≤2*A*C^2 := by positivity
  nlinarith [sq_nonneg (A*C^2)]

lemma diagonal_mul_shape {M : Interaction n} {C : ℝ} {a : Fin n→ℝ}
    (ha : ∀ i,|a i|≤1) (hM : ShapeBound M C) :
    ShapeBound (Matrix.diagonal a*M) C := by
  have haN : SKGap.opNorm (Matrix.diagonal a)≤1 := SKGap.opNorm_diagonal_le (by norm_num) ha
  refine ⟨(SKGap.opNorm_mul _ _).trans ?_,?_,?_⟩
  · calc
      _ ≤ 1*SKGap.opNorm M := mul_le_mul_of_nonneg_right haN (norm_nonneg _)
      _ = SKGap.opNorm M := one_mul _
      _ ≤ C := hM.1
  · apply le_trans ?_ hM.2.1
    apply le_of_pow_le_pow_left₀ (by decide : 2≠0) (norm_nonneg _)
    change SKGap.diagonalSeminorm _ ^2 ≤ SKGap.diagonalSeminorm M ^2
    simp only [SKGap.diagonalSeminorm_sq,Matrix.diagonal_mul]
    apply Finset.sum_le_sum
    intro i _
    have hi := pow_le_pow_left₀ (abs_nonneg (a i)) (ha i) 2
    simp only [sq_abs,one_pow] at hi
    simpa only [mul_pow,one_mul] using mul_le_mul_of_nonneg_right hi (sq_nonneg (M i i))
  · apply le_trans ?_ hM.2.2
    apply le_of_pow_le_pow_left₀ (by decide : 4≠0) (norm_nonneg _)
    change SKGap.offDiagonalSeminorm _ ^4 ≤ SKGap.offDiagonalSeminorm M ^4
    simp only [SKGap.offDiagonalSeminorm_fourth]
    apply Finset.sum_le_sum
    intro p _
    split_ifs
    · exact le_rfl
    · simp only [Matrix.diagonal_mul,mul_pow]
      have hi := pow_le_pow_left₀ (abs_nonneg (a p.1)) (ha p.1) 4
      rw [← abs_pow,abs_of_nonneg (by positivity : 0≤a p.1^4)] at hi
      simpa only [one_pow,one_mul] using mul_le_mul_of_nonneg_right hi
        (by positivity : 0≤(M p.1 p.2)^4)

lemma tanh_derivative_error {F : VectorFields n} {x : Spin n} {C : ℝ}
    (hC : 0≤C) (hD : ShapeBound (derivativeMatrix F x) C) :
    ‖derivativeMatrix (fun y i => Real.tanh (F y i)) x-
      Matrix.diagonal (fun i => scalarVariance (F x i))*derivativeMatrix F x‖ ≤ 8*C^2 := by
  convert quadratic_entry_error hC (by norm_num : (0:ℝ)≤4) hD ?_ using 1 <;> try norm_num
  intro i k
  simpa only [derivativeMatrix,Matrix.sub_apply,Matrix.diagonal_mul,mul_comm,
    refreshInfluence] using refreshInfluence_error_le F x k i

lemma tanh_derivative_shape {F : VectorFields n} {x : Spin n} {C : ℝ}
    (hC : 0≤C) (hD : ShapeBound (derivativeMatrix F x) C) :
    ShapeBound (derivativeMatrix (fun y i => Real.tanh (F y i)) x) (C+8*C^2) := by
  apply ShapeBound.perturb _ (tanh_derivative_error hC hD)
  apply diagonal_mul_shape ?_ hD
  intro i
  rw [abs_of_pos (scalarVariance_pos _)]
  exact scalarVariance_le_one _

lemma siteMean_derivative (F : VectorFields n) (x : Spin n) :
    derivativeVector (siteMean F) x = (n:ℝ)⁻¹ •
      (Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) ((derivativeMatrix F x)ᵀ))
        (WithLp.toLp 2 (fun _ => 1)) := by
  ext k
  change halfDiff k (siteMean F) x = (n:ℝ)⁻¹*(∑ i,halfDiff k (fun y => F y i) x*1)
  simp only [mul_one,halfDiff,siteMean]
  rw [← Finset.sum_div,Finset.sum_sub_distrib]
  ring

lemma euclidean_ones_norm_sq :
    ‖(WithLp.toLp 2 (fun _ : Fin n => (1:ℝ)) : EuclideanSpace ℝ (Fin n))‖^2 = n := by
  simp [EuclideanSpace.real_norm_sq_eq]

lemma siteMean_derivative_square (F : VectorFields n) (x : Spin n) (hn : 0<n) :
    (n:ℝ)*‖derivativeVector (siteMean F) x‖^2 ≤ SKGap.opNorm (derivativeMatrix F x)^2 := by
  have hnR : (0:ℝ)<n := Nat.cast_pos.mpr hn
  have h := (Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) ((derivativeMatrix F x)ᵀ)).le_opNorm
    (WithLp.toLp 2 (fun _ : Fin n => (1:ℝ)))
  change ‖(Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) ((derivativeMatrix F x)ᵀ))
    (WithLp.toLp 2 (fun _ : Fin n => (1:ℝ)))‖ ≤
    SKGap.opNorm ((derivativeMatrix F x)ᵀ) * ‖(WithLp.toLp 2 (fun _ : Fin n => (1:ℝ)) : EuclideanSpace ℝ (Fin n))‖ at h
  rw [SKGap.opNorm_transpose] at h
  have hs := pow_le_pow_left₀ (norm_nonneg _) h 2
  rw [mul_pow,euclidean_ones_norm_sq] at hs
  rw [siteMean_derivative,norm_smul,Real.norm_eq_abs,abs_inv,abs_of_pos hnR,mul_pow]
  field_simp
  nlinarith

lemma siteMean_derivative_square_bound {F : VectorFields n} {x : Spin n} {B : ℝ}
    (hn : 0<n) (hB : SKGap.opNorm (derivativeMatrix F x)≤B) :
    (n:ℝ)*‖derivativeVector (siteMean F) x‖^2 ≤ B^2 :=
  (siteMean_derivative_square F x hn).trans
    (pow_le_pow_left₀ (norm_nonneg _) hB 2)

lemma derivative_norm_of_mean_square {f : Spin n→ℝ} {x : Spin n} {B : ℝ}
    (hn : 0<n) (hB : 0≤B) (h : (n:ℝ)*‖derivativeVector f x‖^2≤B^2) :
    ‖derivativeVector f x‖≤B := by
  have hn1 : (1:ℝ)≤n := by exact_mod_cast hn
  nlinarith [sq_nonneg ‖derivativeVector f x‖,norm_nonneg (derivativeVector f x)]

lemma outer_frobenius_bound {v : Fin n→ℝ} {f : Spin n→ℝ} {x : Spin n} {B : ℝ}
    (hv : ∀ i,|v i|≤1) (hB : 0≤B)
    (h : (n:ℝ)*‖derivativeVector f x‖^2≤B^2) :
    ‖Matrix.of (fun i k => v i*halfDiff k f x)‖≤B := by
  apply nonneg_le_nonneg_of_sq_le_sq hB
  simp only [← sq]
  rw [SKGap.frobenius_sq]
  calc
    _ ≤ ∑ _i : Fin n,∑ k,(halfDiff k f x)^2 := by
      apply Finset.sum_le_sum
      intro i _
      apply Finset.sum_le_sum
      intro k _
      have hi := pow_le_pow_left₀ (abs_nonneg (v i)) (hv i) 2
      simp only [sq_abs,one_pow] at hi
      change (v i*halfDiff k f x)^2 ≤ _
      rw [mul_pow]
      nlinarith [sq_nonneg (halfDiff k f x)]
    _ = (n:ℝ)*‖derivativeVector f x‖^2 := by
      simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,
        EuclideanSpace.real_norm_sq_eq,derivativeVector]
    _ ≤ B^2 := h

lemma spin_diagonal_frobenius (f : Spin n→ℝ) (x : Spin n) :
    ‖Matrix.diagonal (fun k => spin x k*halfDiff k f x)‖ = ‖derivativeVector f x‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [SKGap.frobenius_sq,EuclideanSpace.real_norm_sq_eq]
  simp [Matrix.diagonal_apply,derivativeVector,mul_pow,spin_sq]

lemma derivativeMatrix_product (f : Spin n→ℝ) (F : VectorFields n) (x : Spin n) :
    derivativeMatrix (fun y i => f y*F y i) x = f x • derivativeMatrix F x +
      Matrix.of (fun i k => F x i*halfDiff k f x) -
      (2:ℝ) • (derivativeMatrix F x*Matrix.diagonal (fun k => spin x k*halfDiff k f x)) := by
  ext i k
  simp only [derivativeMatrix,Matrix.sub_apply,Matrix.add_apply,Matrix.smul_apply,
    smul_eq_mul,Matrix.mul_diagonal,halfDiff_mul,Matrix.of_apply]
  ring

lemma product_derivative_error {f : Spin n→ℝ} {F : VectorFields n} {x : Spin n} {B C : ℝ}
    (hn : 0<n) (hB : 0≤B) (hC : SKGap.opNorm (derivativeMatrix F x)≤C)
    (hF : ∀ i,|F x i|≤1) (hf : (n:ℝ)*‖derivativeVector f x‖^2≤B^2) :
    ‖derivativeMatrix (fun y i => f y*F y i) x-f x • derivativeMatrix F x‖ ≤ B+2*C*B := by
  have hdb := derivative_norm_of_mean_square hn hB hf
  have hC0 : 0≤C := (norm_nonneg _).trans hC
  rw [derivativeMatrix_product]
  have he (A R T : Interaction n) : A+R-T-A=R-T := by abel
  rw [he]
  calc
    _ ≤ ‖Matrix.of (fun i k => F x i*halfDiff k f x)‖+
        ‖(2:ℝ) • (derivativeMatrix F x*Matrix.diagonal (fun k => spin x k*halfDiff k f x))‖ := norm_sub_le _ _
    _ ≤ B+2*C*B := by
      apply add_le_add (outer_frobenius_bound hF hB hf)
      rw [norm_smul,Real.norm_eq_abs,abs_of_pos (by norm_num : (0:ℝ)<2)]
      calc
        _ ≤ 2*(SKGap.opNorm (derivativeMatrix F x)*‖Matrix.diagonal (fun k => spin x k*halfDiff k f x)‖) :=
          mul_le_mul_of_nonneg_left (SKGap.frobenius_mul_le_opNorm _ _) (by norm_num)
        _ ≤ 2*(C*B) := by
          rw [spin_diagonal_frobenius]
          exact mul_le_mul_of_nonneg_left (mul_le_mul hC hdb (norm_nonneg _) hC0) (by norm_num)
        _ = _ := by ring

lemma derivativeMatrix_linear (J : Interaction n) (F : VectorFields n) (h : Fin n→ℝ)
    (x : Spin n) :
    derivativeMatrix (fun y i => h i+∑ k,J i k*F y k) x = J*derivativeMatrix F x := by
  ext i l
  simp only [derivativeMatrix,Matrix.mul_apply,halfDiff]
  simp_rw [← mul_div_assoc,mul_sub]
  rw [← Finset.sum_div,Finset.sum_sub_distrib]
  ring

lemma derivativeMatrix_sub (F G : VectorFields n) (x : Spin n) :
    derivativeMatrix (fun y i => F y i-G y i) x=derivativeMatrix F x-derivativeMatrix G x := by
  ext i k
  exact halfDiff_sub k (fun y => F y i) (fun y => G y i) x

lemma derivativeMatrix_smul (c : ℝ) (F : VectorFields n) (x : Spin n) :
    derivativeMatrix (fun y i => c*F y i) x=c • derivativeMatrix F x := by
  ext i k
  simp only [derivativeMatrix,halfDiff,Matrix.smul_apply,smul_eq_mul]
  ring

lemma derivativeMatrix_spin (x : Spin n) : derivativeMatrix spin x=1 := by
  ext i k
  simp [derivativeMatrix,Matrix.one_apply,eq_comm]

lemma variance_derivative_error {F : VectorFields n} {x : Spin n} {C : ℝ}
    (hC : 0≤C) (hD : ShapeBound (derivativeMatrix F x) C) :
    ‖derivativeMatrix (fun y i => 1-(F y i)^2) x-
      (-2:ℝ) • (Matrix.diagonal (F x)*derivativeMatrix F x)‖ ≤ 4*C^2 := by
  convert quadratic_entry_error hC (by norm_num : (0:ℝ)≤2) hD ?_ using 1 <;> try norm_num
  intro i k
  have hs : halfDiff k (fun y => 1-(F y i)^2) x =
      -2*F x i*halfDiff k (fun y => F y i) x+
        2*spin x k*(halfDiff k (fun y => F y i) x)^2 := by
    have hh := halfDiff_mul k (fun y => F y i) (fun y => F y i) x
    rw [halfDiff_sub,halfDiff_const]
    simpa only [pow_two,zero_sub] using (show -(halfDiff k (fun y => F y i*F y i) x) =
      -2*F x i*halfDiff k (fun y => F y i) x+
        2*spin x k*(halfDiff k (fun y => F y i) x)^2 by rw [hh]; ring)
  simp only [derivativeMatrix,hs]
  have he (a b c : ℝ) : -2*a*b+2*c*b^2+2*(a*b)=2*c*b^2 := by ring
  rw [he,abs_mul,abs_mul,abs_spin_eq_one,mul_one]
  norm_num [abs_of_nonneg (sq_nonneg (halfDiff k (fun y => F y i) x))]

lemma variance_derivative_opNorm {F : VectorFields n} {x : Spin n} {C : ℝ}
    (hC : 0≤C) (hF : ∀ i,|F x i|≤1) (hD : ShapeBound (derivativeMatrix F x) C) :
    SKGap.opNorm (derivativeMatrix (fun y i => 1-(F y i)^2) x) ≤ 2*C+4*C^2 := by
  let A := (-2:ℝ) • (Matrix.diagonal (F x)*derivativeMatrix F x)
  have hA : SKGap.opNorm A≤2*C := by
    dsimp only [A]
    rw [opNorm_smul]
    norm_num only [abs_neg,abs_of_nonneg (by norm_num : (0:ℝ)≤2)]
    exact mul_le_mul_of_nonneg_left (diagonal_mul_shape hF hD).1 (by norm_num)
  have hE := (opNorm_le_frobenius
    (derivativeMatrix (fun y i => 1-(F y i)^2) x-A)).trans (variance_derivative_error hC hD)
  have he : derivativeMatrix (fun y i => 1-(F y i)^2) x =
      A+(derivativeMatrix (fun y i => 1-(F y i)^2) x-A) := by abel
  rw [he]
  exact (opNorm_add _ _).trans (add_le_add hA hE)

lemma tanh_derivative_formal_error {F : VectorFields n} {x : Spin n}
    {H : Interaction n} {C E : ℝ} (hC : 0≤C) (hD : ShapeBound (derivativeMatrix F x) C)
    (hE : ‖derivativeMatrix F x-H‖≤E) :
    ‖derivativeMatrix (fun y i => Real.tanh (F y i)) x-
      Matrix.diagonal (fun i => scalarVariance (F x i))*H‖ ≤ 8*C^2+E := by
  let V := Matrix.diagonal (fun i => scalarVariance (F x i))
  have hV : SKGap.opNorm V≤1 := by
    apply SKGap.opNorm_diagonal_le (by norm_num)
    intro i
    rw [abs_of_pos (scalarVariance_pos _)]
    exact scalarVariance_le_one _
  have he : derivativeMatrix (fun y i => Real.tanh (F y i)) x-V*H =
      (derivativeMatrix (fun y i => Real.tanh (F y i)) x-V*derivativeMatrix F x)+
        V*(derivativeMatrix F x-H) := by noncomm_ring
  change ‖derivativeMatrix (fun y i => Real.tanh (F y i)) x-V*H‖≤_
  rw [he]
  apply (norm_add_le _ _).trans
  apply add_le_add (tanh_derivative_error hC hD)
  exact (SKGap.frobenius_mul_le_opNorm _ _).trans
    ((mul_le_mul_of_nonneg_right hV (norm_nonneg _)).trans (by simpa using hE))

end SKGapCutoff.Primary
end
end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Localization_Error
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped BigOperators Matrix.Norms.Frobenius
namespace SKGap.SourceError
open Matrix
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

local instance instFactLeENNRealOfNat_solutions_rf52313_1 : Fact (1≤(4:ENNReal)) := ⟨by norm_num⟩
lemma matrix_column_square_le (P : Matrix ι ι ℝ) (i : ι) :
    (∑k,(P k i)^2)≤(opNorm P)^2 := by
  have H:=pow_le_pow_left₀ (norm_nonneg (colVec P i)) (colVec_norm_le P i) 2
  simpa only [colVec,EuclideanSpace.real_norm_sq_eq] using H

end SKGap.SourceError

end
end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Localization_Operation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped BigOperators Matrix.Norms.Frobenius
namespace SKGapCutoff.Recipe
open Primary Matrix
variable {n : ℕ}

lemma vectorNorm_sq (u : Fin n→ℝ) : vectorNorm u^2=∑i,(u i)^2 := by
  exact EuclideanSpace.real_norm_sq_eq _

lemma vectorNorm_nonneg (u : Fin n→ℝ) : 0 ≤ vectorNorm u := norm_nonneg _

end SKGapCutoff.Recipe

end
end

section

noncomputable section
open scoped BigOperators Matrix.Norms.Frobenius
namespace SKGapCutoff.Recipe
open Primary Matrix
variable {n : ℕ}

lemma vectorNorm_add (u v : Fin n→ℝ) :
    vectorNorm (u+v) ≤ vectorNorm u+vectorNorm v := by
  exact norm_add_le (WithLp.toLp 2 u : EuclideanSpace ℝ (Fin n)) (WithLp.toLp 2 v)

lemma vectorNorm_smul (c : ℝ) (u : Fin n→ℝ) :
    vectorNorm (c • u)=|c| *vectorNorm u := by
  exact norm_smul c (WithLp.toLp 2 u : EuclideanSpace ℝ (Fin n))

lemma vectorNorm_mono {u v : Fin n→ℝ} (h : ∀i,|u i|≤|v i|) : vectorNorm u ≤ vectorNorm v := by
  apply nonneg_le_nonneg_of_sq_le_sq (vectorNorm_nonneg _)
  simp only [←sq,vectorNorm_sq]
  exact Finset.sum_le_sum fun i _=>by
    simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg (u i)) (h i) 2

lemma vectorNorm_abs (u : Fin n→ℝ) : vectorNorm (fun i=>|u i|)=vectorNorm u := by
  apply (sq_eq_sq₀ (vectorNorm_nonneg _) (vectorNorm_nonneg _)).mp
  simp [vectorNorm_sq]

lemma vectorNorm_matrix_mul (J : Interaction n) (u : Fin n→ℝ) :
    vectorNorm (J.mulVec u) ≤ SKGap.opNorm J*vectorNorm u := by
  exact (Matrix.toEuclideanCLM (𝕜:=ℝ) J).le_opNorm (WithLp.toLp 2 u)

lemma siteMean_square (U : VectorFields n) (x : Spin n) (hn : 0<n) :
    (n:ℝ)*(siteMean U x)^2 ≤ (vectorNorm (U x))^2 := by
  have H:=sq_sum_le_card_mul_sum_sq (s:=Finset.univ) (f:=U x)
  simp only [Finset.card_univ,Fintype.card_fin] at H
  have hnR : (0:ℝ)<n := Nat.cast_pos.mpr hn
  dsimp only [siteMean]
  rw [div_pow,vectorNorm_sq]
  apply (mul_le_mul_iff_left₀ hnR).mp
  field_simp
  nlinarith

end SKGapCutoff.Recipe

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

omit [DecidableEq ι]

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

lemma primaryState_mag_bounded (j : ℝ) (J : Interaction n) (h : Fin n→ℝ) (k : ℕ)
    (x : Spin n) (i : Fin n) : |(primaryState j J h k).1 x i|≤1 := by
  cases k with
  | zero => simp [primaryState,abs_spin_eq_one]
  | succ k => exact (Real.abs_tanh_lt_one _).le

lemma formalMag_previous (j : ℝ) (J : Interaction n) (h : Fin n→ℝ) (x : Spin n) (k : ℕ) :
    formalMag j J h x k =
      Matrix.diagonal (SKGap.Noncrossing.Primary.previousDiagonal (primaryDiagonal j J h x) k)*
        SKGap.Noncrossing.Primary.primaryMatrix j J (primaryDiagonal j J h x) k := by
  cases k <;> simp [formalMag,formalField,SKGap.Noncrossing.Primary.previousDiagonal,
    SKGap.Noncrossing.Primary.primaryMatrix]

lemma formalField_succ (j : ℝ) (J : Interaction n) (h : Fin n→ℝ) (x : Spin n) (k : ℕ) :
    formalField j J h x (k+1) = J*formalMag j J h x (k+1)-
      (j*SKGap.Noncrossing.Diagram.mean (primaryDiagonal j J h x k)) • formalMag j J h x k := by
  change SKGap.Noncrossing.Primary.primaryMatrix j J (primaryDiagonal j J h x) (k+2) =
    J*(Matrix.diagonal (primaryDiagonal j J h x k)*
      SKGap.Noncrossing.Primary.primaryMatrix j J (primaryDiagonal j J h x) (k+1))-
      (j*SKGap.Noncrossing.Diagram.mean (primaryDiagonal j J h x k)) • formalMag j J h x k
  rw [formalMag_previous,SKGap.Noncrossing.Primary.primaryMatrix,Matrix.mul_assoc]

lemma onsager_derivative_error {F G : VectorFields n} {x : Spin n} {H P : Interaction n}
    (j : ℝ) (J : Interaction n) (h : Fin n→ℝ) {C R : ℝ} (hn : 0<n)
    (hC : 0≤C) (hR : 0≤R) (hJ : SKGap.opNorm J≤R)
    (hF : ShapeBound (derivativeMatrix F x) C) (hFE : ‖derivativeMatrix F x-H‖≤C)
    (hGE : ‖derivativeMatrix G x-P‖≤C) (hG : SKGap.opNorm (derivativeMatrix G x)≤C)
    (hGb : ∀ i,|G x i|≤1) :
    let m : VectorFields n := fun y i => Real.tanh (F y i)
    let b : Spin n→ℝ := siteMean (fun y i => 1-(m y i)^2)
    let T := C+8*C^2
    let Q := 2*T+4*T^2
    ‖derivativeMatrix (fun y i => h i+∑ a,J i a*m y a-j*b y*G y i) x-
      (J*(Matrix.diagonal (fun i => scalarVariance (F x i))*H)-(j*b x) • P)‖ ≤
      R*T+|j| *(C+Q+2*C*Q) := by
  let m : VectorFields n := fun y i => Real.tanh (F y i)
  let b : Spin n→ℝ := siteMean (fun y i => 1-(m y i)^2)
  let T := C+8*C^2
  let Q := 2*T+4*T^2
  change ‖derivativeMatrix (fun y i => h i+∑ a,J i a*m y a-j*b y*G y i) x-
    (J*(Matrix.diagonal (fun i => scalarVariance (F x i))*H)-(j*b x) • P)‖≤_
  have hT : 0≤T := by dsimp [T]; positivity
  have hQ : 0≤Q := by dsimp [Q]; positivity
  have hm : ShapeBound (derivativeMatrix m x) T := tanh_derivative_shape hC hF
  have hmE : ‖derivativeMatrix m x-Matrix.diagonal (fun i => scalarVariance (F x i))*H‖≤T := by
    convert tanh_derivative_formal_error hC hF hFE using 1
    all_goals try with_reducible_and_instances rfl
    dsimp [T]
    ring
  have hbQ : (n:ℝ)*‖derivativeVector b x‖^2≤Q^2 :=
    siteMean_derivative_square_bound hn (variance_derivative_opNorm hT
      (fun i => (Real.abs_tanh_lt_one _).le) hm)
  have hp : ‖derivativeMatrix (fun y i => b y*G y i) x-b x • derivativeMatrix G x‖≤Q+2*C*Q :=
    product_derivative_error hn hQ hG hGb hbQ
  have hb : |b x|≤1 := by
    let : Nonempty (Fin n) := Fin.pos_iff_nonempty.mp hn
    have hv (i : Fin n) : |1-(m x i)^2|≤1 := by
      change |scalarVariance (F x i)|≤1
      rw [abs_of_pos (scalarVariance_pos _)]
      exact scalarVariance_le_one _
    simpa only [b,siteMean,SKGap.Noncrossing.Diagram.mean,Fintype.card_fin] using
      SKGap.Noncrossing.Primary.mean_abs_le_one hv
  have hpE : ‖derivativeMatrix (fun y i => b y*G y i) x-b x • P‖≤C+Q+2*C*Q := by
    have he : derivativeMatrix (fun y i => b y*G y i) x-b x • P =
        (derivativeMatrix (fun y i => b y*G y i) x-b x • derivativeMatrix G x)+
          b x • (derivativeMatrix G x-P) := by module
    rw [he]
    apply (norm_add_le _ _).trans
    have hs : ‖b x • (derivativeMatrix G x-P)‖≤C := by
      rw [norm_smul,Real.norm_eq_abs]
      exact (mul_le_mul_of_nonneg_right hb (norm_nonneg _)).trans (by simpa using hGE)
    have hh := add_le_add hp hs
    linarith
  have hd : derivativeMatrix (fun y i => h i+∑ a,J i a*m y a-j*b y*G y i) x =
      J*derivativeMatrix m x-j • derivativeMatrix (fun y i => b y*G y i) x := by
    rw [derivativeMatrix_sub,derivativeMatrix_linear]
    congr 1
    convert derivativeMatrix_smul j (fun y i => b y*G y i) x using 1
    all_goals try with_reducible_and_instances rfl
    congr 1
    funext y i
    ring
  rw [hd]
  have he : J*derivativeMatrix m x-j • derivativeMatrix (fun y i => b y*G y i) x-
      (J*(Matrix.diagonal (fun i => scalarVariance (F x i))*H)-(j*b x) • P) =
      J*(derivativeMatrix m x-Matrix.diagonal (fun i => scalarVariance (F x i))*H)-
        j • (derivativeMatrix (fun y i => b y*G y i) x-b x • P) := by
    simp only [mul_sub,smul_sub,mul_smul]
    abel
  rw [he]
  apply (norm_sub_le _ _).trans
  apply add_le_add
  · exact (SKGap.frobenius_mul_le_opNorm _ _).trans (mul_le_mul hJ hmE (norm_nonneg _) hR)
  · rw [norm_smul,Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_left hpE (abs_nonneg _)

theorem primary_differentiation {j R B : ℝ} (J : Interaction n) (h : Fin n→ℝ)
    (x : Spin n) (hn : 0<n) (hR : 0≤R) (hB : 0≤B) (hJ : SKGap.opNorm J≤R) (k : ℕ)
    (hformal : ∀ l≤k, ShapeBound (formalField j J h x l) B) :
    let C := differentiationBound j R B k
    ‖derivativeMatrix (primaryState j J h k).2 x-formalField j J h x k‖≤C ∧
    ‖derivativeMatrix (primaryState j J h k).1 x-formalMag j J h x k‖≤C ∧
    SKGap.opNorm (derivativeMatrix (primaryState j J h k).1 x)≤C ∧
    ShapeBound (derivativeMatrix (primaryState j J h k).2 x) C := by
  induction k with
  | zero =>
    have hd : derivativeMatrix (primaryState j J h 0).2 x=J := by
      change derivativeMatrix (fun y i => h i+∑ a,J i a*spin y a) x=J
      rw [derivativeMatrix_linear,derivativeMatrix_spin,mul_one]
    have hm : derivativeMatrix (primaryState j J h 0).1 x=1 := derivativeMatrix_spin x
    have hf : formalField j J h x 0=J := rfl
    change _≤B+1 ∧ _≤B+1 ∧ _≤B+1 ∧ ShapeBound _ (B+1)
    rw [hd,hm,hf,formalMag,sub_self,norm_zero,sub_self,norm_zero]
    refine ⟨by positivity,by positivity,(SKGap.opNorm_one_le).trans ?_,?_⟩
    · linarith
    · exact (show ShapeBound J B by simpa only [hf] using hformal 0 le_rfl).mono (by linarith)
  | succ k ih =>
    obtain ⟨hFE,hGE,hG,hF⟩ := ih (fun l hl => hformal l (hl.trans (Nat.le_succ _)))
    let C := differentiationBound j R B k
    let T := C+8*C^2
    let Q := 2*T+4*T^2
    let E := R*T+|j| *(C+Q+2*C*Q)
    have hC : 0≤C := differentiationBound_nonneg hR hB k
    have hT : 0≤T := by dsimp [T]; positivity
    have hQ : 0≤Q := by dsimp [Q]; positivity
    have hE : 0≤E := by dsimp [E]; positivity
    have hnext : differentiationBound j R B (k+1)=B+1+E+T := rfl
    have hFE' : ‖derivativeMatrix (primaryState j J h (k+1)).2 x-formalField j J h x (k+1)‖≤E := by
      have hh := onsager_derivative_error (F := (primaryState j J h k).2)
        (G := (primaryState j J h k).1) j J h hn hC hR hJ hF hFE hGE hG
        (primaryState_mag_bounded j J h k x)
      have hb : siteMean (fun y i => 1-(Real.tanh ((primaryState j J h k).2 y i))^2) x =
          SKGap.Noncrossing.Diagram.mean (primaryDiagonal j J h x k) := by
        simp only [siteMean,SKGap.Noncrossing.Diagram.mean,primaryDiagonal,scalarVariance,Fintype.card_fin]
      dsimp only at hh
      rw [hb] at hh
      rw [formalField_succ]
      exact hh
    have hGE' : ‖derivativeMatrix (primaryState j J h (k+1)).1 x-formalMag j J h x (k+1)‖≤T := by
      have hh := tanh_derivative_formal_error hC hF hFE
      change ‖derivativeMatrix (fun y i => Real.tanh ((primaryState j J h k).2 y i)) x-
        Matrix.diagonal (fun i => scalarVariance ((primaryState j J h k).2 x i))*formalField j J h x k‖≤T
      convert hh using 1
      all_goals try with_reducible_and_instances rfl
      dsimp [T]
      ring
    have hG' : SKGap.opNorm (derivativeMatrix (primaryState j J h (k+1)).1 x)≤T :=
      (tanh_derivative_shape hC hF).1
    have hF' : ShapeBound (derivativeMatrix (primaryState j J h (k+1)).2 x) (B+E) :=
      (hformal (k+1) le_rfl).perturb hFE'
    rw [hnext]
    exact ⟨hFE'.trans (by linarith),hGE'.trans (by linarith),hG'.trans (by linarith),
      hF'.mono (by linarith)⟩

theorem primary_average_differentiation {j R B : ℝ} (J : Interaction n) (h : Fin n→ℝ)
    (x : Spin n) (hn : 0<n) (hR : 0≤R) (hB : 0≤B) (hJ : SKGap.opNorm J≤R) (k : ℕ)
    (hformal : ∀ l≤k, ShapeBound (formalField j J h x l) B) :
    let C := differentiationBound j R B k
    let T := C+8*C^2
    (n:ℝ)*‖derivativeVector (siteMean (fun y i =>
        scalarVariance ((primaryState j J h k).2 y i))) x‖^2≤(2*T+4*T^2)^2 := by
  have hC := differentiationBound_nonneg (j:=j) hR hB k
  have hF := (primary_differentiation J h x hn hR hB hJ k hformal).2.2.2
  apply siteMean_derivative_square_bound hn
  exact variance_derivative_opNorm (by positivity)
    (fun i => (Real.abs_tanh_lt_one _).le) (tanh_derivative_shape hC hF)

end SKGapCutoff.Primary

end
end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Localization_ResidualInduction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped BigOperators
namespace SKGapCutoff.Primary
open Matrix SKGap.Stein
variable {n : ℕ}

lemma mag_zero (j : ℝ) (J : Interaction n) (h : Fin n→ℝ) : mag j J h 0=spin := rfl
lemma mag_succ (j : ℝ) (J : Interaction n) (h : Fin n→ℝ) (k : ℕ) (x : Spin n) (i : Fin n) :
    mag j J h (k+1) x i=Real.tanh (fld j J h k x i) := rfl
lemma onsager_zero (j : ℝ) (J : Interaction n) (h : Fin n→ℝ) (x : Spin n) :
    onsager j J h 0 x=0 := by simp [onsager,siteMean,mag_zero,spin_sq]

lemma fld_eq (j : ℝ) (J : Interaction n) (h : Fin n→ℝ) (k : ℕ) (x : Spin n) (i : Fin n) :
    fld j J h k x i=h i+∑a,J i a*mag j J h k x a-
      j*onsager j J h k x*mag j J h (k-1) x i := by
  cases k with
  | zero => simp [fld,primaryState,mag,onsager_zero]
  | succ k => rfl

lemma residual_inner_product (hn : 0<n) (j : ℝ) (J : Interaction n) (h : Fin n→ℝ)
    (k : ℕ) (x : Spin n) :
    (∑i,residual j J h k x i*mag j J h k x i)=
      (n:ℝ)*(onsager j J h (k+1) x-onsager j J h k x)-
      ∑i,residual j J h k x i*mag j J h (k+1) x i := by
  have hnR : (n:ℝ)≠0 := ne_of_gt (Nat.cast_pos.mpr hn)
  simp only [onsager,siteMean,mul_sub,mul_div_cancel₀ _ hnR]
  rw [←Finset.sum_sub_distrib,←Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i _
  dsimp [residual]
  ring

lemma mulVec_pair_symmetric (J : Interaction n) (hJ : J.IsSymm) (u v : Fin n→ℝ) :
    (∑i,(∑l,J i l*u l)*v i)=∑l,u l*(∑i,J l i*v i) := by
  simp only [Finset.sum_mul,Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl; intro l _
  apply Finset.sum_congr rfl; intro i _
  rw [hJ.apply i l]
  ring

end SKGapCutoff.Primary

end
end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Stability_OrdinaryGraph
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
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

namespace SourceTree
variable {D : Type*}

lemma sourceMatrix_leaf (j c : ℝ) (J : Matrix ι ι ℝ) :
    sourceMatrix j J (.leaf c)=c • 1 := by simp [sourceMatrix,words,matrixPolynomial,matrixWord]
lemma fieldMatrix_leaf (j c : ℝ) (J : Matrix ι ι ℝ) :
    fieldMatrix j J (.leaf c)=c • J := by
  simp [fieldMatrix,words,matrixPolynomial,matrixWord,matrixLetter]
lemma sourceMatrix_branch (j : ℝ) (J : Matrix ι ι ℝ) (p : ι→ℝ) (a b : SourceTree (ι→ℝ)) :
    sourceMatrix j J (.branch p a b)=Matrix.diagonal p*fieldMatrix j J a+sourceMatrix j J b := by
  simp [sourceMatrix,fieldMatrix,words,matrixPolynomial_append,matrixPolynomial_prefix,
    matrixWord,matrixLetter]
lemma fieldMatrix_branch (j : ℝ) (J : Matrix ι ι ℝ) (p : ι→ℝ) (a b : SourceTree (ι→ℝ)) :
    fieldMatrix j J (.branch p a b)=J*(Matrix.diagonal p*fieldMatrix j J a)-
      (j*Diagram.mean p) • sourceMatrix j J a+fieldMatrix j J b := by
  simp [sourceMatrix,fieldMatrix,words,matrixPolynomial_append,matrixPolynomial_prefix,
    matrixPolynomial_scale,matrixWord,matrixLetter,mul_assoc,sub_eq_add_neg,add_assoc]
end SourceTree
end SKGap.Noncrossing.Primary

end
end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Localization_RecipeGraph
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped BigOperators
namespace SKGapCutoff.Primary
open SKGap.Noncrossing.Primary
variable {n : ℕ}

lemma primaryTree_matrices (j : ℝ) (J : Interaction n) (h : Fin n→ℝ) (x : Spin n) (k : ℕ) :
    SourceTree.sourceMatrix j J (primaryTree j J h x k)=formalMag j J h x k ∧
    SourceTree.fieldMatrix j J (primaryTree j J h x k)=formalField j J h x k := by
  induction k with
  | zero => simp [primaryTree,SourceTree.sourceMatrix_leaf,SourceTree.fieldMatrix_leaf,
      formalMag,formalField,primaryMatrix]
  | succ k ih =>
    constructor
    · simp [primaryTree,SourceTree.sourceMatrix_branch,SourceTree.sourceMatrix_leaf,ih.2,formalMag]
    · simp only [primaryTree,SourceTree.fieldMatrix_branch,SourceTree.fieldMatrix_leaf,zero_smul,
        add_zero,ih.1,ih.2]
      rw [formalField_succ,formalMag]

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
-- module Solutions.OAIQ072_SK.SKGap_Stability_ConditionalMean
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
open scoped BigOperators NNReal ENNReal
open MeasureTheory Metric Set
open scoped BigOperators NNReal ENNReal
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators NNReal ENNReal Matrix.Norms.L2Operator
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Matrix.Norms.L2Operator
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Matrix Matrix.Norms.Elementwise
open MeasureTheory ProbabilityTheory Filter Set
open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators ENNReal NNReal
open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators NNReal ENNReal Matrix
open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators ENNReal NNReal
open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators NNReal ENNReal
open scoped BigOperators
namespace SKGapCutoff.Static

lemma conditionalMean_abs_le {n : ℕ} (Q : Spin n → ℝ)
    (hQ : ∀ x, 0 ≤ Q x) (x : Spin n) (i : Fin n) :
    |conditionalMean Q x i| ≤ 1 := by
  have hs : |spin x i| = 1 := by cases hx : x i <;> simp [spin,hx]
  simp only [conditionalMean, abs_mul, hs, one_mul, abs_div]
  rw [abs_of_nonneg (add_nonneg (hQ x) (hQ _))]
  apply div_le_one_of_le₀ _ (add_nonneg (hQ x) (hQ _))
  exact abs_sub_le_iff.2 ⟨by linarith [hQ (flip x i)], by linarith [hQ x]⟩

end SKGapCutoff.Static

open MeasureTheory ProbabilityTheory
open scoped BigOperators Matrix Matrix.Norms.Elementwise NNReal ENNReal

end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Localization_WeakResidual
attribute [-instance] _root_.OAI.SKGap.ComplexMatrix.frobeniusInnerProduct
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped BigOperators
namespace SKGapCutoff.Static
variable {n : ℕ}

lemma conditionalVariance_nonneg (P : Spin n→ℝ) (hP : ∀ x,0≤P x)
    (x : Spin n) (i : Fin n) : 0 ≤ conditionalVariance P x i := by
  have h:=conditionalMean_abs_le P hP x i
  have hh:=pow_le_pow_left₀ (abs_nonneg (conditionalMean P x i)) h 2
  simpa only [sq_abs,one_pow,conditionalVariance,sub_nonneg] using hh

lemma conditionalVariance_le_one (P : Spin n→ℝ) (x : Spin n) (i : Fin n) :
    conditionalVariance P x i≤1 := by dsimp [conditionalVariance]; nlinarith [sq_nonneg (conditionalMean P x i)]

lemma varianceEnergy_nonneg (P : Spin n→ℝ) (hP : ∀ x,0≤P x) (f : Observables n) :
    0≤varianceEnergy P f := by
  exact Finset.sum_nonneg (fun x _=>mul_nonneg (hP x)
    (Finset.sum_nonneg (fun i _=>mul_nonneg (conditionalVariance_nonneg P hP x i) (sq_nonneg _))))

end SKGapCutoff.Static

end
end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Matrix_NormalizedPrimaryRecipe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped BigOperators Matrix.Norms.Frobenius
namespace SKGapCutoff.Recipe
open Primary
variable {n M : ℕ} {κ σ : Type*} [Fintype κ] [DecidableEq κ]

lemma normalized_pair_cancel (hn : 0<n) (R U : VectorFields n) (a : Spin n→ℝ) (x : Spin n) :
    (Real.sqrt (n:ℝ)*a x)*(∑i,R x i*(U x i/Real.sqrt (n:ℝ)))=
      a x*(∑i,R x i*U x i) := by
  have hs : Real.sqrt (n:ℝ)≠0 := ne_of_gt (Real.sqrt_pos.mpr (Nat.cast_pos.mpr hn))
  simp only [div_eq_mul_inv,←mul_assoc,←Finset.sum_mul]
  field_simp

end SKGapCutoff.Recipe

end
end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Localization_ResidualMultiplier
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped BigOperators
namespace SKGapCutoff.Static
variable {n : ℕ}

lemma halfDiff_mul_flipped (i : Fin n) (θ G : Observables n) (x : Spin n) :
    halfDiff i (fun y=>θ y*G y) x=θ (flip x i)*halfDiff i G x+G x*halfDiff i θ x := by
  rw [halfDiff_mul]
  have h:=flip_sub i θ x
  rw [show θ (flip x i)=θ x-2*spin x i*halfDiff i θ x by linarith]
  ring

end SKGapCutoff.Static

end
end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Localization_UniformRecipeClass
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped BigOperators
namespace SKGapCutoff.Primary
variable {n : ℕ}
lemma onsager_bounds (j : ℝ) (J : Interaction n) (h : Fin n→ℝ) (k : ℕ) (x : Spin n) :
    0≤onsager j J h k x ∧ onsager j J h k x≤1 := by
  have hm (i : Fin n) : (mag j J h k x i)^2≤1 := by
    have H:=primaryState_mag_bounded j J h k x i
    have H':=sq_le_sq₀ (abs_nonneg (mag j J h k x i)) (by norm_num : (0:ℝ)≤1)
    simpa only [sq_abs,one_pow] using H'.mpr H
  constructor
  · exact div_nonneg (Finset.sum_nonneg (fun i _=>sub_nonneg.mpr (hm i))) (Nat.cast_nonneg n)
  · by_cases hn : n=0
    · simp [onsager,siteMean,hn]
    · apply (div_le_iff₀ (Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn))).mpr
      calc
        (∑i:Fin n,(1-(mag j J h k x i)^2)) ≤ ∑i:Fin n,(1:ℝ) :=
          Finset.sum_le_sum fun i _=>sub_le_self _ (sq_nonneg _)
        _ = _ := by simp
end SKGapCutoff.Primary

end
end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Localization_PrimaryLocalInput
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped BigOperators Matrix.Norms.Frobenius
namespace SKGapCutoff.Primary
open Recipe SKGap.Noncrossing.Primary
variable {n : ℕ}

lemma localPrimaryBudget_bounds {j R B : ℝ} (hR : 0≤R) (hB : 0≤B) (M : ℕ) (q : Fin M) :
    differentiationBound j R B q.val≤localPrimaryBudget j R B M ∧
    averageBudget j R B q.val≤localPrimaryBudget j R B M := by
  have hh:=Finset.single_le_sum (s:=Finset.univ)
    (fun r (_:r∈Finset.univ)=>add_nonneg (differentiationBound_nonneg (j:=j) hR hB r.val)
      (averageBudget_nonneg (j:=j) hR hB r.val)) (Finset.mem_univ q)
  have h1:=differentiationBound_nonneg (j:=j) hR hB q.val
  have h2:=averageBudget_nonneg (j:=j) hR hB q.val
  exact ⟨(le_add_of_nonneg_right h2).trans hh,(le_add_of_nonneg_left h1).trans hh⟩

lemma onsager_derivative_bound {j R B : ℝ} (J : Interaction n) (h : Fin n→ℝ) (x : Spin n)
    (hn : 0<n) (hR : 0≤R) (hB : 0≤B) (hJ : SKGap.opNorm J≤R) (M : ℕ)
    (hformal : ∀l<M,ShapeBound (formalField j J h x l) B) {q : ℕ} (hq : q≤M) :
    ‖derivativeVector (onsager j J h q) x‖≤localPrimaryBudget j R B M := by
  cases q with
  | zero=>
    have he : onsager j J h 0=0:=funext (onsager_zero j J h)
    rw [he]
    have hz : derivativeVector (0 : Spin n→ℝ) x=0 := by
      ext i; simp [derivativeVector,halfDiff]
    rw [hz,norm_zero]
    exact localPrimaryBudget_nonneg (j:=j) hR hB M
  | succ k=>
    have hh:=primary_average_differentiation J h x hn hR hB hJ k (fun l hl=>hformal l (by omega))
    have hh':(n:ℝ)*‖derivativeVector (onsager j J h (k+1)) x‖^2≤(averageBudget j R B k)^2 := by
      simpa only [onsager,mag,primaryState,scalarVariance,averageBudget] using hh
    exact (derivative_norm_of_mean_square hn (averageBudget_nonneg hR hB k) hh').trans
      (localPrimaryBudget_bounds hR hB M ⟨k,by omega⟩).2

end SKGapCutoff.Primary

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
-- module Solutions.OAIQ072_SK.SKGap_Terminal_ResidualPairMoments
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped BigOperators Matrix.Norms.Frobenius
namespace SKGapCutoff.Recipe
open Primary Static
variable {n : ℕ}

lemma mag_vectorNorm (j : ℝ) (J : Interaction n) (h : Fin n→ℝ) (k : ℕ) (x : Spin n) :
    vectorNorm (mag j J h k x)≤Real.sqrt (n:ℝ) := by
  apply nonneg_le_nonneg_of_sq_le_sq (Real.sqrt_nonneg _)
  simp only [←sq,vectorNorm_sq,Real.sq_sqrt (Nat.cast_nonneg n)]
  calc
    _ ≤ ∑_i:Fin n,(1:ℝ)^2 := Finset.sum_le_sum (fun i _=>by
      simpa only [sq_abs,mag] using pow_le_pow_left₀ (abs_nonneg _) (primaryState_mag_bounded j J h k x i) 2)
    _ = _ := by simp

end SKGapCutoff.Recipe

end
end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Localization_SmoothSelection
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped BigOperators NNReal ContDiff
namespace SKGapCutoff.Recipe
open Primary Static
variable {n : ℕ}

lemma residualScalarCutoff_zero {u : ℝ} (hu : 1≤u) : residualScalarCutoff u=0 := by
  simp [residualScalarCutoff,Real.smoothTransition.zero_of_nonpos (by linarith : (1-u)*4/3≤0)]

end SKGapCutoff.Recipe

end
end

section

noncomputable section
open scoped BigOperators NNReal
namespace SKGapCutoff.Recipe
open Primary Static
variable {n : ℕ}

lemma residualStepCutoff_support (hn : 0<n) {ρ j : ℝ} (hρ : 0<ρ)
    (J : Interaction n) (h : Fin n→ℝ) (k : ℕ) (x : Spin n)
    (hc : residualStepCutoff ρ j J h k x≠0) :
    vectorNorm (residual j J h k x)≤ρ*Real.sqrt (n:ℝ) := by
  have hr : residualEnergy j J h k x/ρ^2<1 :=
    lt_of_not_ge (fun hh=>hc (residualScalarCutoff_zero hh))
  have he : residualEnergy j J h k x≤ρ^2 := by
    exact ((div_lt_one (sq_pos_of_pos hρ)).mp hr).le
  apply nonneg_le_nonneg_of_sq_le_sq (by positivity)
  simp only [←sq,mul_pow,Real.sq_sqrt (Nat.cast_nonneg n)]
  exact (div_le_iff₀ (Nat.cast_pos.mpr hn)).mp he

lemma residualCutoff_support (hn : 0<n) {ρ j : ℝ} (hρ : 0<ρ)
    (J : Interaction n) (h : Fin n→ℝ) (k : ℕ) (x : Spin n)
    (hc : residualCutoff ρ j J h k x≠0) :
    vectorNorm (residual j J h k x)≤ρ*Real.sqrt (n:ℝ) ∧
    vectorNorm (residual j J h (k+1) x)≤ρ*Real.sqrt (n:ℝ) := by
  have H:=mul_ne_zero_iff.mp hc
  exact ⟨residualStepCutoff_support hn hρ J h k x H.1,residualStepCutoff_support hn hρ J h (k+1) x H.2⟩

end SKGapCutoff.Recipe

end
end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Localization_ConstantRecipe
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
variable {n : ℕ}

lemma residualDerivativeBudget_nonneg {j R B : ℝ} (hR : 0≤R) (hB : 0≤B) (k : ℕ) :
    0 ≤ residualDerivativeBudget j R B k :=
  add_nonneg (differentiationBound_nonneg hR hB k) (differentiationBound_nonneg hR hB (k+1))

lemma residual_derivative_bound (hn : 0<n) {j R B : ℝ} (hR : 0≤R) (hB : 0≤B)
    (J : Interaction n) (h : Fin n→ℝ) (hJ : SKGap.opNorm J≤R) (k : ℕ)
    (hformal : ∀x l,l≤k+1→ShapeBound (formalField j J h x l) B) (x : Spin n) :
    SKGap.opNorm (derivativeMatrix (residual j J h k) x) ≤ residualDerivativeBudget j R B k := by
  have hm (l : ℕ) (hl : l≤k+1) :
      SKGap.opNorm (derivativeMatrix (mag j J h l) x)≤differentiationBound j R B l :=
    (primary_differentiation J h x hn hR hB hJ l (fun t ht=>hformal x t (ht.trans hl))).2.2.1
  rw [show derivativeMatrix (residual j J h k) x=
    derivativeMatrix (mag j J h k) x-derivativeMatrix (mag j J h (k+1)) x from derivativeMatrix_sub _ _ x]
  simp only [opNorm_eq,map_sub]
  exact (norm_sub_le _ _).trans (add_le_add (hm _ (by omega)) (hm _ le_rfl))

universe u

end SKGapCutoff.Recipe

end
end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Localization_TapPotential
attribute [-instance] _root_.OAI.SKGap.ComplexMatrix.frobeniusInnerProduct
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped BigOperators
open Real Matrix Set Filter Function
open scoped Topology
namespace SKGap

lemma quadraticForm_derivative_algebra {n : ℕ} {J : Matrix (Fin n) (Fin n) ℝ}
    (hJ : J.IsSymm) (m w : Field n) :
    (∑ i, ∑ k, (w i * J i k * m k + m i * J i k * w k)) =
      2 * ∑ i, w i * (∑ k, J i k * m k) := by
  simp only [Finset.sum_add_distrib]
  have he : (∑ i, ∑ k, m i * J i k * w k) = ∑ i, ∑ k, w i * J i k * m k := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro k _
    rw [hJ.apply k i]
    ring
  rw [he]
  simp only [← Finset.mul_sum, mul_assoc]
  ring

lemma quadratic_magnetization_hasFDerivAt {n : ℕ} {J : Matrix (Fin n) (Fin n) ℝ}
    (hJ : J.IsSymm) (y : Field n) :
    HasFDerivAt (fun z => quadraticForm J (magnetization z))
      (2 • ∑ i, (spinVariance y i * (∑ k, J i k * magnetization y k)) •
        (ContinuousLinearMap.proj i : Field n →L[ℝ] ℝ)) y := by
  have hd := HasFDerivAt.sum (u := Finset.univ) (fun i _ =>
    HasFDerivAt.sum (u := Finset.univ) (fun k _ =>
      ((magnetization_hasFDerivAt y i).mul_const (J i k)).mul
        (magnetization_hasFDerivAt y k)))
  convert! hd using 1
  · ext z
    simp only [quadraticForm, Finset.sum_apply, Pi.mul_apply]
  ext v
  simp only [_root_.smul_apply, _root_.sum_apply, _root_.add_apply,
    ContinuousLinearMap.proj_apply, smul_eq_mul, nsmul_eq_mul]
  have he := quadraticForm_derivative_algebra hJ (magnetization y)
    (fun i => spinVariance y i * v i)
  calc
    _ = 2 * ∑ i, (spinVariance y i * v i) * (∑ k, J i k * magnetization y k) := by
      congr 1
      apply Finset.sum_congr rfl
      intro i _
      ring
    _ = ∑ i, ∑ k, ((spinVariance y i * v i) * J i k * magnetization y k +
        magnetization y i * J i k * (spinVariance y k * v k)) := he.symm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro k _
      ring

lemma squared_magnetization_hasFDerivAt {n : ℕ} (y : Field n) :
    HasFDerivAt (fun z => vectorSqNorm (magnetization z))
      (∑ i, (2*magnetization y i*spinVariance y i) •
        (ContinuousLinearMap.proj i : Field n →L[ℝ] ℝ)) y := by
  convert! (HasFDerivAt.sum (u := Finset.univ)
    (fun i _ => (magnetization_hasFDerivAt y i).pow 2)) using 1
  · ext z
    simp only [vectorSqNorm, Finset.sum_apply]
  ext v
  simp only [_root_.sum_apply, _root_.smul_apply, ContinuousLinearMap.proj_apply,
    smul_eq_mul, Nat.reduceSub, pow_one]
  apply Finset.sum_congr rfl
  intro i _
  ring

lemma tapPotential_hasFDerivAt {n : ℕ} (j : ℝ)
    {J : Matrix (Fin n) (Fin n) ℝ} (hJ : J.IsSymm) (h y : Field n) :
    HasFDerivAt (tapPotential j J h)
      (∑ i, weightedTap j J h y i •
        (ContinuousLinearMap.proj i : Field n →L[ℝ] ℝ)) y := by
  have hsinglei (i : Fin n) :
      HasFDerivAt (fun z : Field n => z i * tanh (z i) - log (cosh (z i)))
        ((y i*(1-tanh (y i)^2)) • (ContinuousLinearMap.proj i : Field n →L[ℝ] ℝ)) y := by
    have hd := ((hasFDerivAt_apply (𝕜 := ℝ) i y).mul
      (magnetization_hasFDerivAt y i)).sub
      (((hasFDerivAt_apply (𝕜 := ℝ) i y).cosh).log (cosh_pos (y i)).ne')
    convert! hd using 1
    all_goals try with_reducible_and_instances rfl
    ext v
    simp only [_root_.smul_apply, _root_.sub_apply, _root_.add_apply,
      ContinuousLinearMap.proj_apply, smul_eq_mul, spinVariance, magnetization,
      tanh_eq_sinh_div_cosh]
    ring
  have hsingle := HasFDerivAt.sum (u := Finset.univ) (fun i _ => hsinglei i)
  have hext := HasFDerivAt.sum (u := Finset.univ) (fun i _ =>
    (magnetization_hasFDerivAt y i).const_mul (h i))
  have hquad := (quadratic_magnetization_hasFDerivAt hJ y).const_mul (1/2:ℝ)
  have hsq := (squared_magnetization_hasFDerivAt y).const_mul (j/2)
  have hfour := ((squared_magnetization_hasFDerivAt y).pow 2).const_mul (j/(4*n))
  convert! (((hsingle.sub hext).sub hquad).add hsq).sub hfour using 1
  · ext z
    simp only [tapPotential, Finset.sum_apply, Pi.sub_apply, Pi.add_apply, magnetization]
  ext v
  simp only [_root_.sum_apply, _root_.smul_apply, _root_.sub_apply, _root_.add_apply,
    ContinuousLinearMap.proj_apply, smul_eq_mul, nsmul_eq_mul,
    Nat.cast_ofNat, Nat.reduceSub, pow_one]
  simp only [weightedTap, tapField, onsager, overlap, vectorSqNorm, spinVariance,
    magnetization]
  simp only [Finset.mul_sum, Finset.sum_mul, ← Finset.sum_sub_distrib,
    ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  simp only [← Finset.mul_sum, ← Finset.sum_mul]
  ring

lemma contDiff_tanh_SK {m : WithTop ℕ∞} : ContDiff ℝ m tanh := by
  have he : tanh = sinh / cosh := funext tanh_eq_sinh_div_cosh
  rw [he]
  exact contDiff_sinh.div contDiff_cosh (fun x => (cosh_pos x).ne')

lemma magnetization_contDiff {n : ℕ} {m : WithTop ℕ∞} (i : Fin n) :
    ContDiff ℝ m (fun y : Field n => magnetization y i) :=
  contDiff_tanh_SK.comp (contDiff_apply ℝ ℝ i)

lemma spinVariance_contDiff {n : ℕ} {m : WithTop ℕ∞} (i : Fin n) :
    ContDiff ℝ m (fun y : Field n => spinVariance y i) :=
  contDiff_const.sub ((magnetization_contDiff i).pow 2)

lemma overlap_contDiff {n : ℕ} {m : WithTop ℕ∞} :
    ContDiff ℝ m (overlap (n := n)) :=
  (ContDiff.sum (fun i _ => (magnetization_contDiff i).pow 2)).div_const _

lemma tapField_contDiff {n : ℕ} {m : WithTop ℕ∞} (j : ℝ)
    (J : Matrix (Fin n) (Fin n) ℝ) (h : Field n) : ContDiff ℝ m (tapField j J h) := by
  apply contDiff_pi.mpr
  intro i
  exact ((contDiff_apply ℝ ℝ i).sub contDiff_const).add
    ((contDiff_const.mul (contDiff_const.sub overlap_contDiff)).mul
      (magnetization_contDiff i)) |>.sub
        (ContDiff.sum (fun k _ => contDiff_const.mul (magnetization_contDiff k)))

lemma weightedTap_contDiff {n : ℕ} {m : WithTop ℕ∞} (j : ℝ)
    (J : Matrix (Fin n) (Fin n) ℝ) (h : Field n) : ContDiff ℝ m (weightedTap j J h) := by
  apply contDiff_pi.mpr
  intro i
  exact (spinVariance_contDiff i).mul (contDiff_pi.mp (tapField_contDiff j J h) i)

lemma weightedTapE_contDiff {n : ℕ} {m : WithTop ℕ∞} (j : ℝ)
    (J : Matrix (Fin n) (Fin n) ℝ) (h : Field n) : ContDiff ℝ m (weightedTapE j J h) :=
  (EuclideanSpace.equiv (ι := Fin n) (𝕜 := ℝ)).symm.contDiff.comp
    ((weightedTap_contDiff j J h).comp
      (EuclideanSpace.equiv (ι := Fin n) (𝕜 := ℝ)).contDiff)

lemma tapPotentialE_hasFDerivAt {n : ℕ} (j : ℝ)
    {J : Matrix (Fin n) (Fin n) ℝ} (hJ : J.IsSymm) (h : Field n) (y : EField n) :
    HasFDerivAt (tapPotentialE j J h) (innerSL ℝ (weightedTapE j J h y)) y := by
  have hd := (tapPotential_hasFDerivAt j hJ h (WithLp.ofLp y)).comp y
    (EuclideanSpace.equiv (ι := Fin n) (𝕜 := ℝ)).hasFDerivAt
  convert! hd using 1
  all_goals try with_reducible_and_instances rfl
  ext v
  simp only [innerSL_apply_apply, weightedTapE, PiLp.inner_apply, RCLike.inner_apply,
    conj_trivial, ContinuousLinearMap.comp_apply,
    _root_.sum_apply, _root_.smul_apply, ContinuousLinearMap.proj_apply, smul_eq_mul]
  apply Finset.sum_congr rfl
  intro i _
  change v i * weightedTap j J h (WithLp.ofLp y) i =
    weightedTap j J h (WithLp.ofLp y) i * v i
  ring

lemma weightedTap_hasFDerivAt_zero {n : ℕ} (j : ℝ)
    (J : Matrix (Fin n) (Fin n) ℝ) (h y : Field n)
    (hz : tapField j J h y = 0) :
    HasFDerivAt (weightedTap j J h) (weightedJacobianMap j J y) y := by
  rw [hasFDerivAt_pi']
  intro i
  have hV := ((spinVariance_contDiff i (m := 1)).differentiable (by norm_num) y).hasFDerivAt
  have hF := hasFDerivAt_pi'.mp (tapField_hasFDerivAt j J h y) i
  have hzi : tapField j J h y i = 0 := congrFun hz i
  have hd := hV.mul hF
  simp only [hzi, zero_smul, add_zero] at hd
  convert! hd using 1
  all_goals try with_reducible_and_instances rfl

lemma weightedTapE_fderiv_zero {n : ℕ} (j : ℝ)
    (J : Matrix (Fin n) (Fin n) ℝ) (h : Field n) (y v : EField n)
    (hz : tapField j J h (WithLp.ofLp y) = 0) (i : Fin n) :
    (fderiv ℝ (weightedTapE j J h) y v) i =
      spinVariance (WithLp.ofLp y) i *
        ((fieldJacobian j J (WithLp.ofLp y)).mulVec (WithLp.ofLp v)) i := by
  let e := EuclideanSpace.equiv (ι := Fin n) (𝕜 := ℝ)
  have hd := e.symm.hasFDerivAt.comp y
    ((weightedTap_hasFDerivAt_zero j J h (WithLp.ofLp y) hz).comp y e.hasFDerivAt)
  have he : fderiv ℝ (weightedTapE j J h) y =
      e.symm.toContinuousLinearMap.comp ((weightedJacobianMap j J (WithLp.ofLp y)).comp
        e.toContinuousLinearMap) := hd.fderiv
  rw [he]
  rfl

lemma weighted_jacobian_quadratic_form {n : ℕ} (j : ℝ)
    (J : Matrix (Fin n) (Fin n) ℝ) (y v : Field n) :
    (∑ i, v i * (spinVariance y i * ((fieldJacobian j J y).mulVec v) i)) =
      quadraticForm (fieldHessian j J y (spinVariance y)) (sqrtVarianceMul y v) := by
  simp only [Matrix.mulVec, dotProduct, quadraticForm, sqrtVarianceMul,
    Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro k _
  have hi := sq_sqrt (spinVariance_pos y i).le
  calc
    _ = (sqrt (spinVariance y i) * v i) *
        (sqrt (spinVariance y i)*fieldJacobian j J y i k) * v k := by
      conv_lhs => rw [← hi]
      ring
    _ = _ := by rw [← fieldHessian_variance_intertwine]; ring

lemma weightedTapE_derivative_energy {n : ℕ} (j : ℝ)
    (J : Matrix (Fin n) (Fin n) ℝ) (h : Field n) (y v : EField n)
    (hz : tapField j J h (WithLp.ofLp y) = 0) :
    inner ℝ v (fderiv ℝ (weightedTapE j J h) y v) =
      quadraticForm (fieldHessian j J (WithLp.ofLp y) (spinVariance (WithLp.ofLp y)))
        (sqrtVarianceMul (WithLp.ofLp y) (WithLp.ofLp v)) := by
  rw [← weighted_jacobian_quadratic_form]
  simp only [PiLp.inner_apply, RCLike.inner_apply, conj_trivial]
  apply Finset.sum_congr rfl
  intro i _
  rw [weightedTapE_fderiv_zero j J h y v hz i]
  ring

lemma spinVariance_eq_inv_cosh_sq {n : ℕ} (y : Field n) (i : Fin n) :
    spinVariance y i = 1 / cosh (y i)^2 := by
  simp only [spinVariance, magnetization, tanh_eq_sinh_div_cosh]
  field_simp
  exact cosh_sq_sub_sinh_sq _

lemma spinVariance_bound_on_box {n : ℕ} (y : Field n) {R : ℝ} (hR : 0 ≤ R)
    (hy : ∀ i, |y i| ≤ R) (i : Fin n) :
    1 / cosh R^2 ≤ spinVariance y i := by
  rw [spinVariance_eq_inv_cosh_sq]
  apply one_div_le_one_div_of_le (sq_pos_of_pos (cosh_pos (y i)))
  have h : cosh (y i) ≤ cosh R := cosh_le_cosh.mpr
    (by simpa only [abs_of_nonneg hR] using hy i)
  exact pow_le_pow_left₀ (cosh_pos (y i)).le h 2

lemma tapField_shift_bound {n : ℕ} (hn : 0 < n) {j : ℝ} (hj : 0 ≤ j)
    (J : Matrix (Fin n) (Fin n) ℝ) (h y : Field n) (i : Fin n) :
    |y i - tapField j J h y i| ≤ |h i| + j + ∑ k, |J i k| := by
  have hm (k : Fin n) : |magnetization y k| ≤ 1 := by
    exact (abs_lt.mpr ⟨neg_one_lt_tanh _, tanh_lt_one _⟩).le
  have hB0 : 0 ≤ onsager j y := mul_nonneg hj (sub_nonneg.mpr (overlap_lt_one hn y).le)
  have hBj : onsager j y ≤ j := by
    dsimp [onsager]
    nlinarith [overlap_nonneg y]
  have hBm : |onsager j y * magnetization y i| ≤ j := by
    rw [abs_mul, abs_of_nonneg hB0]
    exact (mul_le_of_le_one_right hB0 (hm i)).trans hBj
  have hJm : |∑ k, J i k * magnetization y k| ≤ ∑ k, |J i k| := by
    exact (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun k _ => by
      rw [abs_mul]
      exact mul_le_of_le_one_right (abs_nonneg _) (hm k))
  have he : y i-tapField j J h y i = h i-onsager j y*magnetization y i +
      ∑ k, J i k*magnetization y k := by simp only [tapField]; ring
  rw [he]
  have hs : |h i-onsager j y*magnetization y i| ≤ |h i|+j := by
    calc
      _ ≤ |h i|+|onsager j y*magnetization y i| := by
        simpa only [sub_eq_add_neg, abs_neg] using
          abs_add_le (h i) (-(onsager j y*magnetization y i))
      _ ≤ _ := add_le_add_right hBm _
  exact (abs_add_le _ _).trans (add_le_add hs hJm)

lemma exists_tapBox_radius {n : ℕ} (hn : 0 < n) {j : ℝ} (hj : 0 ≤ j)
    (J : Matrix (Fin n) (Fin n) ℝ) (h : Field n) :
    ∃ R : ℝ, 0 < R ∧ ∀ y : Field n, ∀ i, |y i-tapField j J h y i| ≤ R := by
  let b := fun i => |h i| + j + ∑ k, |J i k|
  have hb (i : Fin n) : 0 ≤ b i := by dsimp [b]; positivity
  refine ⟨1+∑ i, b i, by positivity, fun y i => ?_⟩
  exact (tapField_shift_bound hn hj J h y i).trans
    ((Finset.single_le_sum (fun k _ => hb k) (Finset.mem_univ i)).trans (by linarith))

lemma weightedTap_step_box {n : ℕ} (j : ℝ) (J : Matrix (Fin n) (Fin n) ℝ)
    (h y : Field n) {R ε : ℝ} (hε : ε ∈ Set.Icc (0:ℝ) 1)
    (hbound : ∀ i, |y i-tapField j J h y i| ≤ R) (hy : ∀ i, |y i| ≤ R) :
    ∀ i, |(y-ε • weightedTap j J h y) i| ≤ R := by
  intro i
  let a := ε*spinVariance y i
  have ha0 : 0 ≤ a := mul_nonneg hε.1 (spinVariance_pos y i).le
  have ha1 : a ≤ 1 := (mul_le_mul_of_nonneg_left (spinVariance_le_one y i) hε.1).trans
    (by simpa using hε.2)
  have he : (y-ε • weightedTap j J h y) i =
      (1-a)*y i + a*(y i-tapField j J h y i) := by
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, weightedTap, a]
    ring
  rw [he]
  calc
    _ ≤ |(1-a)*y i| + |a*(y i-tapField j J h y i)| := abs_add_le _ _
    _ = (1-a)*|y i| + a*|y i-tapField j J h y i| := by
      rw [abs_mul, abs_mul, abs_of_nonneg ha0, abs_of_nonneg (sub_nonneg.mpr ha1)]
    _ ≤ (1-a)*R+a*R := add_le_add
      (mul_le_mul_of_nonneg_left (hy i) (sub_nonneg.mpr ha1))
      (mul_le_mul_of_nonneg_left (hbound i) ha0)
    _ = R := by ring

lemma mem_fieldBoxE {n : ℕ} {R : ℝ} (hR : 0 ≤ R) (y : EField n) :
    y ∈ fieldBoxE n R ↔ ∀ i, |y i| ≤ R := by
  simp only [fieldBoxE, Set.mem_image]
  constructor
  · rintro ⟨x, hx, rfl⟩
    have hn : ‖x‖ ≤ R := by simpa only [Metric.mem_closedBall, dist_zero_right] using hx
    change ∀ i, |x i| ≤ R
    simpa only [Real.norm_eq_abs] using (pi_norm_le_iff_of_nonneg hR).mp hn
  · intro hy
    refine ⟨WithLp.ofLp y, ?_, rfl⟩
    rw [Metric.mem_closedBall, dist_zero_right, pi_norm_le_iff_of_nonneg hR]
    exact hy

lemma isCompact_fieldBoxE (n : ℕ) (R : ℝ) : IsCompact (fieldBoxE n R) :=
  (isCompact_closedBall (0:Field n) R).image
    (EuclideanSpace.equiv (ι := Fin n) (𝕜 := ℝ)).symm.continuous

lemma convex_fieldBoxE (n : ℕ) (R : ℝ) : Convex ℝ (fieldBoxE n R) :=
  (convex_closedBall (0:Field n) R).linear_image
    (EuclideanSpace.equiv (ι := Fin n) (𝕜 := ℝ)).symm.toLinearMap

lemma nonempty_fieldBoxE (n : ℕ) {R : ℝ} (hR : 0 ≤ R) : (fieldBoxE n R).Nonempty :=
  ⟨0, (mem_fieldBoxE hR 0).mpr (fun _ => by simpa using hR)⟩

theorem lyapunov_eventually_hits {X : Type*} [TopologicalSpace X] [CompactSpace X]
    (T : X → X) (hT : Continuous T) (φ : X → ℝ) (hφ : Continuous φ)
    (hstrict : ∀ x, T x ≠ x → φ (T x) < φ x)
    {U : Set X} (hU : IsOpen U) (hfix : ∀ x, T x = x → x ∈ U) (x : X) :
    ∃ n : ℕ, T^[n] x ∈ U := by
  by_contra! hnever
  have hK : IsCompact Uᶜ := hU.isClosed_compl.isCompact
  have hne : Uᶜ.Nonempty := ⟨x, by simpa using hnever 0⟩
  obtain ⟨y, hy, hmin⟩ := hK.exists_isMinOn hne (hφ.sub (hφ.comp hT)).continuousOn
  let δ := φ y - φ (T y)
  have hd : 0 < δ := sub_pos.mpr (hstrict y (fun h => hy (hfix y h)))
  have hdec (n : ℕ) : δ ≤ φ (T^[n] x) - φ (T (T^[n] x)) :=
    hmin (hnever n)
  obtain ⟨m, hm⟩ := isCompact_univ.bddBelow_image hφ.continuousOn
  have hlower (z : X) : m ≤ φ z := hm ⟨z, mem_univ _, rfl⟩
  have hbound (n : ℕ) : φ (T^[n] x) ≤ φ x - (n:ℝ)*δ := by
    induction n with
    | zero => simp
    | succ n ih =>
      rw [iterate_succ_apply']
      have h := hdec n
      push_cast
      nlinarith
  obtain ⟨n, hn⟩ := exists_nat_gt ((φ x - m)/δ)
  have hn' : φ x - m < (n:ℝ)*δ := (div_lt_iff₀ hd).mp hn
  have hb := hbound n
  have hl := hlower (T^[n] x)
  linarith

theorem lyapunov_fixed_point {X : Type*} [TopologicalSpace X] [CompactSpace X]
    [Nonempty X] (T : X → X) (φ : X → ℝ) (hφ : Continuous φ)
    (hstrict : ∀ x, T x ≠ x → φ (T x) < φ x) : ∃ x, T x = x := by
  obtain ⟨x, _, hx⟩ := isCompact_univ.exists_isMinOn univ_nonempty hφ.continuousOn
  refine ⟨x, by_contra fun h => ?_⟩
  exact (not_lt_of_ge (hx (mem_univ (T x)))) (hstrict x h)

section Basins
variable {X : Type*} [TopologicalSpace X] (T : X → X)

lemma mem_attractionBasin_iterate_iff (p x : X) (k : ℕ) :
    T^[k] x ∈ attractionBasin T p ↔ x ∈ attractionBasin T p := by
  simpa only [attractionBasin, mem_ofPred_eq, iterate_add_apply] using
    (tendsto_add_atTop_iff_nat (f := fun n : ℕ => T^[n] x) (l := 𝓝 p) k)

lemma fixed_mem_attractionBasin {p : X} (hp : T p = p) : p ∈ attractionBasin T p := by
  simp only [attractionBasin, mem_ofPred_eq, iterate_fixed hp]
  exact tendsto_const_nhds

end Basins
end SKGap
end
end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Localization_AttractionBasinIUnion
attribute [-instance] _root_.OAI.SKGap.ComplexMatrix.frobeniusInnerProduct
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open scoped BigOperators
open Real Matrix Set Filter Function
open scoped Topology
namespace SKGap
section Basins
variable {X : Type*} [TopologicalSpace X] (T : X → X)

lemma attractionBasin_eq_iUnion {p : X} {U : Set X} (hU : IsOpen U) (hp : p ∈ U)
    (hatt : U ⊆ attractionBasin T p) :
    attractionBasin T p = ⋃ k : ℕ, (T^[k]) ⁻¹' U := by
  ext x
  constructor
  · intro hx
    have h := hx.eventually (hU.mem_nhds hp)
    obtain ⟨k, hk⟩ := h.exists
    exact mem_iUnion.mpr ⟨k, hk⟩
  · intro hx
    obtain ⟨k, hk⟩ := mem_iUnion.mp hx
    exact (mem_attractionBasin_iterate_iff T p x k).mp (hatt hk)

lemma isOpen_attractionBasin (hT : Continuous T) {p : X} {U : Set X}
    (hU : IsOpen U) (hp : p ∈ U) (hatt : U ⊆ attractionBasin T p) :
    IsOpen (attractionBasin T p) := by
  rw [attractionBasin_eq_iUnion T hU hp hatt]
  exact isOpen_iUnion (fun k => hU.preimage (hT.iterate k))

lemma disjoint_attractionBasins [T2Space X] {p q : X} (hpq : p ≠ q) :
    Disjoint (attractionBasin T p) (attractionBasin T q) := by
  rw [disjoint_left]
  intro x hx hy
  exact hpq (tendsto_nhds_unique hx hy)

end Basins

theorem lyapunov_unique_fixed_point {X : Type*} [TopologicalSpace X] [CompactSpace X]
    [ConnectedSpace X] [T2Space X]
    (T : X → X) (hT : Continuous T) (φ : X → ℝ) (hφ : Continuous φ)
    (hstrict : ∀ x, T x ≠ x → φ (T x) < φ x)
    (hattract : ∀ p, T p = p → ∃ U : Set X, IsOpen U ∧ p ∈ U ∧
      U ⊆ attractionBasin T p) : ∃! p, T p = p := by
  have hopen (p) (hp : T p = p) : IsOpen (attractionBasin T p) := by
    obtain ⟨U, hU, hpU, hatt⟩ := hattract p hp
    exact isOpen_attractionBasin T hT hU hpU hatt
  have hcover (x : X) : ∃ p, T p = p ∧ x ∈ attractionBasin T p := by
    let U := ⋃ p : {p // T p = p}, attractionBasin T p.val
    have hU : IsOpen U := isOpen_iUnion (fun p => hopen p.val p.property)
    have hfixed (p) (hp : T p = p) : p ∈ U :=
      mem_iUnion.mpr ⟨⟨p, hp⟩, fixed_mem_attractionBasin T hp⟩
    obtain ⟨k, hk⟩ := lyapunov_eventually_hits T hT φ hφ hstrict hU hfixed x
    obtain ⟨p, hp⟩ := mem_iUnion.mp hk
    exact ⟨p.val, p.property, (mem_attractionBasin_iterate_iff T p.val x k).mp hp⟩
  obtain ⟨p, hp⟩ := lyapunov_fixed_point T φ hφ hstrict
  refine ⟨p, hp, fun q hq => ?_⟩
  by_contra hqp
  let V := ⋃ q : {q // T q = q ∧ q ≠ p}, attractionBasin T q.val
  have hV : IsOpen V := isOpen_iUnion (fun q => hopen q.val q.property.1)
  have hdisj : Disjoint (attractionBasin T p) V := by
    rw [disjoint_iUnion_right]
    intro q
    exact disjoint_attractionBasins T q.property.2.symm
  have hcov : (univ : Set X) ⊆ attractionBasin T p ∪ V := by
    intro x _
    obtain ⟨r, hr, hx⟩ := hcover x
    by_cases he : r = p
    · subst r
      exact Or.inl hx
    · exact Or.inr (mem_iUnion.mpr ⟨⟨r, hr, he⟩, hx⟩)
  have hconn := IsPreconnected.subset_or_subset (hopen p hp) hV hdisj hcov
    isPreconnected_univ
  rcases hconn with hconn | hconn
  · have hqp' := tendsto_nhds_unique (hconn (mem_univ q))
      (fixed_mem_attractionBasin T hq)
    exact hqp hqp'.symm
  · exact disjoint_left.mp hdisj (fixed_mem_attractionBasin T hp) (hconn (mem_univ p))

theorem local_contraction_attracts {X : Type*} [MetricSpace X]
    {T : X → X} {p : X} (hp : T p = p) {K : NNReal} (hK : K < 1)
    {U : Set X} (hU : U ∈ 𝓝 p) (hlip : LipschitzOnWith K T U) :
    ∃ V : Set X, IsOpen V ∧ p ∈ V ∧ V ⊆ attractionBasin T p := by
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp hU
  have hpU : p ∈ U := hball (Metric.mem_ball_self hε)
  have hmaps : MapsTo T (Metric.ball p ε) (Metric.ball p ε) := by
    intro x hx
    have h := hlip.dist_le_mul x (hball hx) p hpU
    rw [hp] at h
    exact h.trans_lt ((mul_le_of_le_one_left (dist_nonneg : 0 ≤ dist x p)
      (show (K:ℝ) ≤ 1 by exact_mod_cast hK.le)).trans_lt hx)
  refine ⟨Metric.ball p ε, Metric.isOpen_ball, Metric.mem_ball_self hε, ?_⟩
  intro x hx
  have hbd (n : ℕ) : dist (T^[n] x) p ≤ (K:ℝ)^n * dist x p := by
    induction n with
    | zero => simp
    | succ n ih =>
      rw [iterate_succ_apply']
      have h := hlip.dist_le_mul (T^[n] x) (hball (hmaps.iterate n hx)) p hpU
      rw [hp] at h
      exact h.trans (by simpa only [pow_succ', mul_assoc] using
        mul_le_mul_of_nonneg_left ih K.coe_nonneg)
  have ht := (tendsto_pow_atTop_nhds_zero_of_lt_one K.coe_nonneg
    (show (K:ℝ) < 1 by exact_mod_cast hK)).mul_const (dist x p)
  rw [zero_mul] at ht
  exact Metric.tendsto_atTop.mpr (fun δ hδ => by
    obtain ⟨N, hN⟩ := eventually_atTop.mp (ht.eventually (gt_mem_nhds hδ))
    exact ⟨N, fun n hn => (hbd n).trans_lt (hN n hn)⟩)

end SKGap

noncomputable section
open Set Function Real
open scoped Topology NNReal
namespace SKGap
section GradientDescent
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem lipschitz_gradient_remainder {φ : E → ℝ} {G : E → E} {s : Set E}
    (hs : Convex ℝ s) (hgrad : ∀ x ∈ s, HasFDerivAt φ (innerSL ℝ (G x)) x)
    {L : ℝ≥0} (hG : LipschitzOnWith L G s) {x y : E} (hx : x ∈ s) (hy : y ∈ s) :
    |φ y - φ x - inner ℝ (G x) (y-x)| ≤ (L:ℝ)*‖y-x‖^2 := by
  let d := y-x
  let ℓ : ℝ →ᵃ[ℝ] E := AffineMap.lineMap x y
  let f := fun t : ℝ => φ (ℓ t) - t * inner ℝ (G x) d
  let f' := fun t : ℝ => inner ℝ (G (ℓ t) - G x) d
  have hℓ (t : ℝ) : ℓ t = x + t • d := by
    simp only [ℓ, d, AffineMap.lineMap_apply_module]
    module
  have hmem (t : ℝ) (ht : t ∈ Icc (0:ℝ) 1) : ℓ t ∈ s :=
    hs.mapsTo_lineMap hx hy ht
  have hf (t : ℝ) (ht : t ∈ Icc (0:ℝ) 1) :
      HasDerivWithinAt f (f' t) (Icc (0:ℝ) 1) t := by
    have hd := ((hgrad (ℓ t) (hmem t ht)).comp_hasDerivAt t
      AffineMap.hasDerivAt_lineMap).sub
      ((hasDerivAt_id t).mul_const (inner ℝ (G x) d))
    convert! (hd.hasDerivWithinAt (s := Icc (0:ℝ) 1)) using 1
    all_goals try with_reducible_and_instances rfl
    simp only [f', innerSL_apply_apply, inner_sub_left, d, one_mul]
  have hb (t : ℝ) (ht : t ∈ Ico (0:ℝ) 1) :
      ‖f' t‖ ≤ (L:ℝ)*‖d‖^2 := by
    have hdiff : ‖ℓ t-x‖ ≤ ‖d‖ := by
      rw [hℓ, add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_nonneg ht.1]
      exact mul_le_of_le_one_left (norm_nonneg _) ht.2.le
    have h := (hG.norm_sub_le (hmem t ⟨ht.1, ht.2.le⟩) hx).trans
      (mul_le_mul_of_nonneg_left hdiff L.coe_nonneg)
    calc
      ‖f' t‖ ≤ ‖G (ℓ t)-G x‖*‖d‖ := norm_inner_le_norm _ _
      _ ≤ ((L:ℝ)*‖d‖)*‖d‖ := mul_le_mul_of_nonneg_right h (norm_nonneg d)
      _ = _ := by ring
  have h := norm_image_sub_le_of_norm_deriv_le_segment_01' hf hb
  simpa only [f, ℓ, AffineMap.lineMap_apply_zero, AffineMap.lineMap_apply_one,
    zero_mul, sub_zero, one_mul, Real.norm_eq_abs, d, sub_right_comm] using h

theorem gradient_step_strict_descent {φ : E → ℝ} {G : E → E} {s : Set E}
    (hs : Convex ℝ s) (hgrad : ∀ x ∈ s, HasFDerivAt φ (innerSL ℝ (G x)) x)
    {L : ℝ≥0} (hG : LipschitzOnWith L G s) {ε : ℝ} (hε : 0 < ε)
    (hsmall : (L:ℝ)*ε < 1) {x : E} (hx : x ∈ s) (hstep : x-ε • G x ∈ s)
    (hGx : G x ≠ 0) : φ (x-ε • G x) < φ x := by
  have h := (le_abs_self _).trans (lipschitz_gradient_remainder hs hgrad hG hx hstep)
  have he : x-ε • G x-x = -ε • G x := by module
  rw [he, inner_smul_right, real_inner_self_eq_norm_sq,
    norm_smul, Real.norm_eq_abs, abs_of_neg (neg_neg_of_pos hε)] at h
  have hn : 0 < ‖G x‖^2 := sq_pos_of_pos (norm_pos_iff.mpr hGx)
  have hc : 0 < ε*(1-(L:ℝ)*ε)*‖G x‖^2 := by positivity
  nlinarith only [h, hc]

theorem gradient_step_derivative_sq_bound {D : E →L[ℝ] E} {c M ε : ℝ}
    (_hc : 0 ≤ c) (_hM : 0 ≤ M) (hε : 0 ≤ ε)
    (hcoercive : ∀ v, c*‖v‖^2 ≤ inner ℝ v (D v)) (hbound : ‖D‖ ≤ M)
    (v : E) :
    ‖v-ε • D v‖^2 ≤ (1-2*ε*c+ε^2*M^2)*‖v‖^2 := by
  have hD : ‖D v‖ ≤ M*‖v‖ := D.le_of_opNorm_le hbound v
  have hD2 : ‖D v‖^2 ≤ M^2*‖v‖^2 := by
    nlinarith [norm_nonneg (D v), mul_nonneg _hM (norm_nonneg v)]
  have h := mul_le_mul_of_nonneg_left (hcoercive v) (show 0 ≤ 2*ε by positivity)
  have h' := mul_le_mul_of_nonneg_left hD2 (sq_nonneg ε)
  rw [norm_sub_sq_real, inner_smul_right, norm_smul, Real.norm_eq_abs,
    abs_of_nonneg hε]
  nlinarith only [h, h']

end GradientDescent
end SKGap

end
end
end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Stability_TapFieldE
attribute [-instance] _root_.OAI.SKGap.ComplexMatrix.frobeniusInnerProduct
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open scoped BigOperators
open Real Matrix Set Filter Function
open scoped Topology
noncomputable section
open Set Function Real
open scoped Topology NNReal
namespace SKGap
section GradientRoots
open Set Function Filter Real
open scoped Topology NNReal
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

lemma exists_small_gradient_step {c M : ℝ} (hc : 0 < c) (hM : 0 ≤ M) :
    ∃ ε : ℝ, 0 < ε ∧ ε ≤ 1 ∧ M*ε < 1 ∧ 2*ε*c ≤ 1 ∧ ε*M^2 < c := by
  have h1 : 0 < 1/(M+1) := by positivity
  have h2 : 0 < 1/(2*c+1) := by positivity
  have h3 : 0 < c/(M^2+1) := by positivity
  obtain ⟨ε, hε, he⟩ := exists_between
    (lt_min (by norm_num : (0:ℝ) < 1) (lt_min h1 (lt_min h2 h3)))
  have he1 := (lt_min_iff.mp he).1
  have he2 := (lt_min_iff.mp (lt_min_iff.mp he).2).1
  have he3 := (lt_min_iff.mp (lt_min_iff.mp (lt_min_iff.mp he).2).2).1
  have he4 := (lt_min_iff.mp (lt_min_iff.mp (lt_min_iff.mp he).2).2).2
  have hp2 := (lt_div_iff₀ (show 0 < M+1 by positivity)).mp he2
  have hp3 := (lt_div_iff₀ (show 0 < 2*c+1 by positivity)).mp he3
  have hp4 := (lt_div_iff₀ (show 0 < M^2+1 by positivity)).mp he4
  exact ⟨ε, hε, he1.le, by nlinarith, by nlinarith, by nlinarith⟩

lemma gradient_step_derivative_norm_lt {D : E →L[ℝ] E} {c M ε : ℝ}
    (hc : 0 < c) (hM : 0 ≤ M) (hε : 0 < ε)
    (hsmall0 : 2*ε*c ≤ 1) (hsmall1 : ε*M^2 < c)
    (hcoercive : ∀ v, c*‖v‖^2 ≤ inner ℝ v (D v)) (hbound : ‖D‖ ≤ M) :
    ‖ContinuousLinearMap.id ℝ E - ε • D‖ < 1 := by
  let k := 1-2*ε*c+ε^2*M^2
  have hk0 : 0 ≤ k := by dsimp [k]; nlinarith [sq_nonneg (ε*M)]
  have hk1 : k < 1 := by
    dsimp [k]
    have h := mul_lt_mul_of_pos_left hsmall1 hε
    nlinarith
  have hb : ‖ContinuousLinearMap.id ℝ E - ε • D‖ ≤ sqrt k := by
    refine (ContinuousLinearMap.id ℝ E - ε • D).opNorm_le_bound (sqrt_nonneg k) ?_
    intro v
    change ‖v-ε • D v‖ ≤ sqrt k * ‖v‖
    have h := gradient_step_derivative_sq_bound hc.le hM hε.le hcoercive hbound v
    have hp : 0 ≤ sqrt k*‖v‖ := by positivity
    apply (sq_le_sq₀ (norm_nonneg _) hp).mp
    calc
      ‖v-ε • D v‖^2 ≤ k*‖v‖^2 := h
      _ = (sqrt k*‖v‖)^2 := by rw [mul_pow, sq_sqrt hk0]
  exact hb.trans_lt (by simpa using sqrt_lt_sqrt hk0 hk1)

theorem gradient_unique_zero_on_compact
    {φ : E → ℝ} {G : E → E} {s : Set E}
    (hcompact : IsCompact s) (hne : s.Nonempty) (hconv : Convex ℝ s)
    (hgrad : ∀ x, HasFDerivAt φ (innerSL ℝ (G x)) x)
    (hG : ContDiff ℝ 1 G)
    {c : ℝ} (hc : 0 < c)
    (hcoercive : ∀ x ∈ s, G x = 0 → ∀ v, c*‖v‖^2 ≤ inner ℝ v (fderiv ℝ G x v))
    (hinvariant : ∀ ε ∈ Icc (0:ℝ) 1, MapsTo (fun x => x-ε • G x) s s) :
    ∃! x : s, G x = 0 := by
  let : CompactSpace s := isCompact_iff_compactSpace.mp hcompact
  let : Nonempty s := hne.to_subtype
  let : ConnectedSpace s := isConnected_iff_connectedSpace.mp (hconv.isConnected hne)
  have hbound : ∃ M : ℝ, 0 ≤ M ∧ ∀ x ∈ s, ‖fderiv ℝ G x‖ ≤ M := by
    obtain ⟨M, hM⟩ := hcompact.bddAbove_image
      (hG.continuous_fderiv (by norm_num)).norm.continuousOn
    refine ⟨max M 0, le_max_right _ _, fun x hx => ?_⟩
    exact (hM ⟨x, hx, rfl⟩).trans (le_max_left _ _)
  obtain ⟨M, hM, hbound⟩ := hbound
  obtain ⟨ε, hε, hε1, hεM, hεc, hεM2⟩ := exists_small_gradient_step hc hM
  let L : ℝ≥0 := ⟨M, hM⟩
  have hLip : LipschitzOnWith L G s :=
    hconv.lipschitzOnWith_of_nnnorm_hasFDerivWithin_le
      (fun x _ => (hG.differentiable (by norm_num) x).hasFDerivAt.hasFDerivWithinAt)
      (fun x hx => by exact_mod_cast hbound x hx)
  let T : s → s := fun x => ⟨x.val-ε • G x.val, hinvariant ε ⟨hε.le,hε1⟩ x.property⟩
  have hT : Continuous T := by
    apply Continuous.subtype_mk
    exact continuous_subtype_val.sub
      (continuous_const.smul (hG.continuous.comp continuous_subtype_val))
  let ψ : s → ℝ := fun x => φ x.val
  have hψ : Continuous ψ :=
    (continuous_iff_continuousAt.mpr fun x => (hgrad x).continuousAt).comp continuous_subtype_val
  have hzero (x : s) : T x = x ↔ G x.val = 0 := by
    rw [Subtype.ext_iff]
    change x.val-ε • G x.val = x.val ↔ G x.val = 0
    simp only [sub_eq_self, smul_eq_zero, hε.ne', false_or]
  have hstrict (x : s) (hx : T x ≠ x) : ψ (T x) < ψ x := by
    exact gradient_step_strict_descent hconv (fun x _ => hgrad x) hLip hε hεM
      x.property (T x).property (fun h => hx ((hzero x).mpr h))
  have hattract (p : s) (hp : T p = p) :
      ∃ U : Set s, IsOpen U ∧ p ∈ U ∧ U ⊆ attractionBasin T p := by
    let D := ContinuousLinearMap.id ℝ E - ε • fderiv ℝ G p.val
    have hD : HasStrictFDerivAt (fun x : E => x-ε • G x) D p.val :=
      (hasStrictFDerivAt_id p.val).sub
        ((hG.contDiffAt.hasStrictFDerivAt (by norm_num)).const_smul ε)
    have hDn : ‖D‖ < 1 := gradient_step_derivative_norm_lt hc hM hε hεc hεM2
      (hcoercive p.val p.property ((hzero p).mp hp)) (hbound p.val p.property)
    have hDnn : ‖D‖₊ < 1 := by exact_mod_cast hDn
    obtain ⟨K, hDK, hK⟩ := exists_between hDnn
    obtain ⟨U, hU, hULip⟩ := hD.exists_lipschitzOnWith_of_nnnorm_lt K hDK
    have hpre : Subtype.val ⁻¹' U ∈ 𝓝 p := continuous_subtype_val.continuousAt.preimage_mem_nhds hU
    have hpreLip : LipschitzOnWith K T (Subtype.val ⁻¹' U) := by
      rw [lipschitzOnWith_iff_dist_le_mul]
      intro x hx y hy
      exact hULip.dist_le_mul x.val hx y.val hy
    exact local_contraction_attracts hp hK hpre hpreLip
  obtain ⟨p, hp, huniq⟩ := lyapunov_unique_fixed_point T hT ψ hψ hstrict hattract
  exact ⟨p, (hzero p).mp hp, fun q hq => huniq q ((hzero q).mpr hq)⟩

end GradientRoots

lemma weightedTapE_eq_zero_iff {n : ℕ} (j : ℝ)
    (J : Matrix (Fin n) (Fin n) ℝ) (h : Field n) (y : EField n) :
    weightedTapE j J h y = 0 ↔ tapField j J h (WithLp.ofLp y) = 0 := by
  constructor
  · intro hz
    ext i
    have he := congrArg (fun z : EField n => z i) hz
    change spinVariance (WithLp.ofLp y) i * tapField j J h (WithLp.ofLp y) i = 0 at he
    exact (mul_eq_zero.mp he).resolve_left (spinVariance_pos (WithLp.ofLp y) i).ne'
  · intro hz
    ext i
    change spinVariance (WithLp.ofLp y) i * tapField j J h (WithLp.ofLp y) i = 0
    rw [hz, Pi.zero_apply, mul_zero]

lemma weightedTapE_coercive_on_box {n : ℕ} (j : ℝ)
    (J : Matrix (Fin n) (Fin n) ℝ) (h : Field n) {R c : ℝ}
    (hR : 0 ≤ R) (hc : 0 ≤ c) (y : EField n) (hy : y ∈ fieldBoxE n R)
    (hz : tapField j J h (WithLp.ofLp y) = 0)
    (hH : ∀ x : Field n, c*vectorSqNorm x ≤
      quadraticForm (fieldHessian j J (WithLp.ofLp y) (spinVariance (WithLp.ofLp y))) x)
    (v : EField n) :
    (c / cosh R^2)*‖v‖^2 ≤ inner ℝ v (fderiv ℝ (weightedTapE j J h) y v) := by
  rw [weightedTapE_derivative_energy j J h y v hz]
  have hV := spinVariance_bound_on_box (WithLp.ofLp y) hR ((mem_fieldBoxE hR y).mp hy)
  have hb : (1 / cosh R^2)*‖v‖^2 ≤ vectorSqNorm (sqrtVarianceMul (WithLp.ofLp y) (WithLp.ofLp v)) := by
    rw [EuclideanSpace.real_norm_sq_eq]
    simp only [vectorSqNorm, sqrtVarianceMul, Finset.mul_sum, mul_pow,
      sq_sqrt (spinVariance_pos _ _).le]
    apply Finset.sum_le_sum
    intro i _
    exact mul_le_mul_of_nonneg_right (hV i) (sq_nonneg _)
  have h := (mul_le_mul_of_nonneg_left hb hc).trans (hH _)
  simpa only [mul_assoc, div_eq_mul_inv, one_mul] using h

theorem tap_unique_zero {n : ℕ} (hn : 0 < n) {j c : ℝ} (hj : 0 ≤ j) (hc : 0 < c)
    {J : Matrix (Fin n) (Fin n) ℝ} (hJ : J.IsSymm) (h : Field n)
    (hH : ∀ y : Field n, tapField j J h y = 0 → ∀ x : Field n,
      c*vectorSqNorm x ≤ quadraticForm (fieldHessian j J y (spinVariance y)) x) :
    ∃! r : Field n, tapField j J h r = 0 := by
  obtain ⟨R, hR, hbound⟩ := exists_tapBox_radius hn hj J h
  have hco : ∀ y ∈ fieldBoxE n R, weightedTapE j J h y = 0 → ∀ v,
      (c / cosh R^2)*‖v‖^2 ≤ inner ℝ v (fderiv ℝ (weightedTapE j J h) y v) := by
    intro y hy hz v
    have hz' := (weightedTapE_eq_zero_iff j J h y).mp hz
    exact weightedTapE_coercive_on_box j J h hR.le hc.le y hy hz' (hH _ hz') v
  have hmaps : ∀ ε ∈ Set.Icc (0:ℝ) 1,
      Set.MapsTo (fun y => y-ε • weightedTapE j J h y) (fieldBoxE n R) (fieldBoxE n R) := by
    intro ε hε y hy
    rw [mem_fieldBoxE hR.le] at hy ⊢
    exact weightedTap_step_box j J h (WithLp.ofLp y) hε (hbound _) hy
  obtain ⟨r, hr, huniq⟩ := gradient_unique_zero_on_compact
    (isCompact_fieldBoxE n R) (nonempty_fieldBoxE n hR.le) (convex_fieldBoxE n R)
    (tapPotentialE_hasFDerivAt j hJ h) (weightedTapE_contDiff j J h)
    (show 0 < c / cosh R^2 by positivity) hco hmaps
  refine ⟨WithLp.ofLp r.val, (weightedTapE_eq_zero_iff j J h r.val).mp hr, ?_⟩
  intro y hy
  have hys : WithLp.toLp 2 y ∈ fieldBoxE n R := by
    rw [mem_fieldBoxE hR.le]
    intro i
    have hb := hbound y i
    simpa only [hy, Pi.zero_apply, sub_zero] using hb
  have hye : weightedTapE j J h (WithLp.toLp 2 y) = 0 :=
    (weightedTapE_eq_zero_iff j J h (WithLp.toLp 2 y)).mpr hy
  have he := congrArg (fun z : fieldBoxE n R => WithLp.ofLp z.val)
    (huniq ⟨WithLp.toLp 2 y, hys⟩ hye)
  exact he

theorem inverseOnConvex_bound {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [CompleteSpace E] {f : E → E} {U : Set E}
    (hU : IsOpen U) (hconv : Convex ℝ U) (hf : ContDiff ℝ 1 f)
    (hunique : ∀ z ∈ U, ∃! y, f y = z) {C : ℝ} (hC : 0 ≤ C)
    (hbound : ∀ y, f y ∈ U → ∀ v, ‖v‖ ≤ C * ‖fderiv ℝ f y v‖)
    {x y : E} (hx : f x ∈ U) (hy : f y ∈ U) :
    ‖y-x‖ ≤ C * ‖f y-f x‖ := by
  classical
  let g : E → E := fun z => if hz : z ∈ U then (hunique z hz).choose else 0
  have hg (z : E) (hz : z ∈ U) : f (g z) = z := by
    simp only [g, dite_eq_left hz]
    exact (hunique z hz).choose_spec.1
  have hgf (z : E) (hz : f z ∈ U) : g (f z) = z := by
    simp only [g, dite_eq_left hz]
    exact ((hunique (f z) hz).choose_spec.2 z rfl).symm
  have hinj (z : E) (hz : f z ∈ U) : Function.Injective (fderiv ℝ f z) := by
    intro a b hab
    apply sub_eq_zero.mp
    apply norm_eq_zero.mp
    have hh := hbound z hz (a-b)
    rw [map_sub, hab, sub_self, norm_zero, mul_zero] at hh
    exact le_antisymm hh (norm_nonneg _)
  let D (z : E) : E →L[ℝ] E := fderiv ℝ f z
  let e (z : E) (hz : f z ∈ U) : E ≃L[ℝ] E :=
    (LinearEquiv.ofInjectiveEndo (D z).toLinearMap (hinj z hz)).toContinuousLinearEquiv
  have he (z : E) (hz : f z ∈ U) : (e z hz : E →L[ℝ] E) = D z := by
    ext v
    rfl
  have hgder (z : E) (hz : z ∈ U) :
      HasFDerivAt g ((e (g z) (by rw [hg z hz]; exact hz)).symm : E →L[ℝ] E) z := by
    let p := g z
    have hp : f p = z := hg z hz
    have hpU : f p ∈ U := hp ▸ hz
    have hder : HasStrictFDerivAt f (e p hpU : E →L[ℝ] E) p := by
      rw [he p hpU]
      exact hf.contDiffAt.hasStrictFDerivAt (by norm_num)
    have hleft : ∀ᶠ w in 𝓝 p, g (f w) = w := by
      filter_upwards [hf.continuous.continuousAt.preimage_mem_nhds (hU.mem_nhds hpU)] with w hw
      exact hgf w hw
    have H := (hder.to_local_left_inverse hleft).hasFDerivAt
    simpa only [hp] using H
  have hnorm (z : E) (hz : z ∈ U) :
      ‖((e (g z) (by rw [hg z hz]; exact hz)).symm : E →L[ℝ] E)‖ ≤ C := by
    apply ContinuousLinearMap.opNorm_le_bound _ hC
    intro v
    have hh := hbound (g z) (by rw [hg z hz]; exact hz)
      ((e (g z) (by rw [hg z hz]; exact hz)).symm v)
    change ‖_‖ ≤ C*‖D (g z) _‖ at hh
    rw [← he (g z) (by rw [hg z hz]; exact hz)] at hh
    simpa using hh
  have hd : DifferentiableOn ℝ g U := fun z hz => (hgder z hz).differentiableAt.differentiableWithinAt
  have hn : ∀ z ∈ U, ‖fderivWithin ℝ g U z‖ ≤ C := by
    intro z hz
    rw [(hgder z hz).hasFDerivWithinAt.fderivWithin (hU.uniqueDiffWithinAt hz)]
    exact hnorm z hz
  have H := hconv.norm_image_sub_le_of_norm_fderivWithin_le hd hn hx hy
  simpa only [hgf x hx, hgf y hy] using H

lemma tapFieldE_contDiff {n : ℕ} {m : WithTop ℕ∞} (j : ℝ)
    (J : Matrix (Fin n) (Fin n) ℝ) (h : Field n) : ContDiff ℝ m (tapFieldE j J h) :=
  (EuclideanSpace.equiv (ι := Fin n) (𝕜 := ℝ)).symm.contDiff.comp
    ((tapField_contDiff j J h).comp
      (EuclideanSpace.equiv (ι := Fin n) (𝕜 := ℝ)).contDiff)

lemma norm_EField_eq {n : ℕ} (v : EField n) : ‖v‖ = vectorNorm (WithLp.ofLp v) := by
  simp only [EuclideanSpace.norm_eq, vectorNorm, Real.norm_eq_abs, sq_abs]

lemma tapFieldE_fderiv {n : ℕ} (j : ℝ) (J : Matrix (Fin n) (Fin n) ℝ)
    (h : Field n) (y v : EField n) :
    fderiv ℝ (tapFieldE j J h) y v =
      WithLp.toLp 2 ((fieldJacobian j J (WithLp.ofLp y)).mulVec (WithLp.ofLp v)) := by
  let e := EuclideanSpace.equiv (ι := Fin n) (𝕜 := ℝ)
  have hd := e.symm.hasFDerivAt.comp y
    ((tapField_hasFDerivAt j J h (WithLp.ofLp y)).comp y e.hasFDerivAt)
  change HasFDerivAt (tapFieldE j J h) _ y at hd
  rw [hd.fderiv]
  rfl

lemma vectorNorm_zero (n : ℕ) : vectorNorm (0 : Field n) = 0 := by
  simp [vectorNorm]

lemma tapField_shift {n : ℕ} (j : ℝ) (J : Matrix (Fin n) (Fin n) ℝ)
    (h z y : Field n) : tapField j J (h+z) y = tapField j J h y-z := by
  ext i
  simp only [tapField, Pi.add_apply, Pi.sub_apply]
  ring

theorem tap_root_and_distance {n : ℕ} (hn : 0 < n) {j K c R : ℝ}
    (hj : 0 ≤ j) (hK : 0 ≤ K) (hc : 0 < c) (hR : 0 < R)
    {J : Matrix (Fin n) (Fin n) ℝ} (hJsymm : J.IsSymm) (h : Field n)
    (hJ : ∀ z : Field n, vectorNorm (J.mulVec z) ≤ K*vectorNorm z)
    (hH : ∀ y : Field n, vectorNorm (tapField j J h y) ≤ R → ∀ x : Field n,
      c*vectorSqNorm x ≤ quadraticForm (fieldHessian j J y (spinVariance y)) x) :
    ∃ r : Field n, tapField j J h r = 0 ∧
      (∀ y, tapField j J h y = 0 → y = r) ∧
      ∀ y, vectorNorm (tapField j J h y) < R →
        vectorNorm (y-r) ≤ (1+(K+3*j)/c)*vectorNorm (tapField j J h y) := by
  have hH0 : ∀ y : Field n, tapField j J h y = 0 → ∀ x : Field n,
      c*vectorSqNorm x ≤ quadraticForm (fieldHessian j J y (spinVariance y)) x := by
    intro y hy
    apply hH y
    simpa only [hy, vectorNorm_zero] using hR.le
  obtain ⟨r, hr, huniq⟩ := tap_unique_zero hn hj hc hJsymm h hH0
  refine ⟨r, hr, huniq, ?_⟩
  intro y hy
  let F := tapFieldE j J h
  let U := Metric.ball (0 : EField n) R
  have hmem (v : EField n) : F v ∈ U ↔ vectorNorm (tapField j J h (WithLp.ofLp v)) < R := by
    simp only [U, Metric.mem_ball, dist_zero_right, F, norm_EField_eq, tapFieldE]
  have hsurj : ∀ z ∈ U, ∃! v, F v = z := by
    intro z hz
    have hzn : vectorNorm (WithLp.ofLp z) < R := by
      simpa only [U, Metric.mem_ball, dist_zero_right, norm_EField_eq] using hz
    have hHz : ∀ v : Field n, tapField j J (h+WithLp.ofLp z) v = 0 → ∀ x : Field n,
        c*vectorSqNorm x ≤ quadraticForm (fieldHessian j J v (spinVariance v)) x := by
      intro v hv
      rw [tapField_shift, sub_eq_zero] at hv
      exact hH v (by rw [hv]; exact hzn.le)
    obtain ⟨v, hv, huv⟩ := tap_unique_zero hn hj hc hJsymm (h+WithLp.ofLp z) hHz
    have hv' : tapField j J h v = WithLp.ofLp z := by
      simpa only [tapField_shift, sub_eq_zero] using hv
    refine ⟨WithLp.toLp 2 v, ?_, ?_⟩
    · change WithLp.toLp 2 (tapField j J h v) = z
      rw [hv', WithLp.toLp_ofLp]
    · intro w hw
      apply (WithLp.ofLp_injective 2)
      apply huv
      rw [tapField_shift, sub_eq_zero]
      exact congrArg WithLp.ofLp hw
  have hbound : ∀ v, F v ∈ U → ∀ w, ‖w‖ ≤ (1+(K+3*j)/c)*‖fderiv ℝ F v w‖ := by
    intro v hv w
    rw [tapFieldE_fderiv, norm_EField_eq, norm_EField_eq]
    exact fieldJacobian_inverse_bound hn hc hj hK J (WithLp.ofLp v) (WithLp.ofLp w)
      hJ (hH _ ((hmem v).mp hv).le)
  have hrmem : F (WithLp.toLp 2 r) ∈ U := by
    rw [hmem]
    simpa only [WithLp.ofLp_toLp, hr, vectorNorm_zero] using hR
  have hymem : F (WithLp.toLp 2 y) ∈ U := (hmem _).mpr hy
  have H := inverseOnConvex_bound Metric.isOpen_ball (convex_ball _ _) (tapFieldE_contDiff j J h)
    hsurj (show 0 ≤ 1+(K+3*j)/c by positivity) hbound hrmem hymem
  simpa only [norm_EField_eq, WithLp.ofLp_sub, WithLp.ofLp_toLp, F, tapFieldE, hr,
    sub_zero, WithLp.toLp_zero] using H

end SKGap

end
end
end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Stability_ResidualRoot
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped BigOperators
namespace SKGapCutoff.Recipe
open Primary Static Matrix
variable {n : ℕ}

lemma primary_onsager_tap (hn : 0<n) (j : ℝ) (J : Interaction n) (h : Fin n→ℝ)
    (k : ℕ) (x : Spin n) :
    SKGap.onsager j (fld j J h k x)=j*onsager j J h (k+1) x := by
  have hnR : (n:ℝ)≠0:=ne_of_gt (Nat.cast_pos.mpr hn)
  simp only [SKGap.onsager,SKGap.overlap,SKGap.magnetization,onsager,siteMean,mag_succ,
    Finset.sum_sub_distrib,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,mul_one,sub_div,div_self hnR]

lemma primary_tap_residual (hn : 0<n) (j : ℝ) (J : Interaction n) (h : Fin n→ℝ)
    (k : ℕ) (x : Spin n) :
    SKGap.tapField j J h (fld j J h (k+1) x)=
      J.mulVec (Primary.residual j J h (k+1) x)-
      (fun i=>j*onsager j J h (k+1) x*(Primary.residual j J h k x i+Primary.residual j J h (k+1) x i))+
      (fun i=>j*(onsager j J h (k+2) x-onsager j J h (k+1) x)*mag j J h (k+2) x i) := by
  ext i
  simp only [SKGap.tapField,primary_onsager_tap hn,SKGap.magnetization,←mag_succ,
    Pi.add_apply,Pi.sub_apply,Matrix.mulVec,dotProduct]
  rw [fld_eq]
  simp only [Nat.add_sub_cancel,Primary.residual,mul_sub,Finset.sum_sub_distrib]
  ring

lemma onsager_residual_difference (hn : 0<n) (j : ℝ) (J : Interaction n)
    (h : Fin n→ℝ) (k : ℕ) (x : Spin n) :
    |onsager j J h (k+1) x-onsager j J h k x| *Real.sqrt (n:ℝ) ≤
      2*vectorNorm (Primary.residual j J h k x) := by
  have hnR : (0:ℝ)<n:=Nat.cast_pos.mpr hn
  have hs : 0<Real.sqrt (n:ℝ):=Real.sqrt_pos.mpr hnR
  have hd : onsager j J h (k+1) x-onsager j J h k x=
      (∑i,Primary.residual j J h k x i*(mag j J h k x i+mag j J h (k+1) x i))/(n:ℝ) := by
    simp only [onsager,siteMean,←sub_div,←Finset.sum_sub_distrib]
    congr 1
    apply Finset.sum_congr rfl; intro i _; dsimp [Primary.residual]; ring
  have hv : vectorNorm (fun i=>mag j J h k x i+mag j J h (k+1) x i)≤2*Real.sqrt (n:ℝ) := by
    exact (SKGap.vectorNorm_add_le _ _).trans
      ((add_le_add (mag_vectorNorm j J h k x) (mag_vectorNorm j J h (k+1) x)).trans_eq (by ring))
  have hp := (SKGap.vector_dot_abs_le (Primary.residual j J h k x)
    (fun i=>mag j J h k x i+mag j J h (k+1) x i)).trans
      (mul_le_mul_of_nonneg_left hv (vectorNorm_nonneg _))
  rw [hd,abs_div,abs_of_pos hnR]
  rw [div_mul_eq_mul_div]
  apply (div_le_iff₀ hnR).mpr
  convert mul_le_mul_of_nonneg_right hp (Real.sqrt_nonneg (n:ℝ)) using 1
  all_goals try with_reducible_and_instances rfl
  simp only [SKGap.vectorNorm,vectorNorm]
  ring_nf
  rw [Real.sq_sqrt hnR.le]

lemma primary_tap_norm (hn : 0<n) {j K : ℝ} (hj : 0≤j) (hK : 0≤K)
    (J : Interaction n) (h : Fin n→ℝ) (k : ℕ) (x : Spin n)
    (hop : ∀v,vectorNorm (J.mulVec v)≤K*vectorNorm v) :
    vectorNorm (SKGap.tapField j J h (fld j J h (k+1) x)) ≤
      j*vectorNorm (Primary.residual j J h k x)+(K+3*j)*vectorNorm (Primary.residual j J h (k+1) x) := by
  have hb:=onsager_bounds j J h (k+1) x
  have hJ : SKGap.opNorm J≤K := by
    apply ContinuousLinearMap.opNorm_le_bound _ hK
    intro value
    exact hop (WithLp.ofLp value)
  have hterm : vectorNorm (fun i=>j*onsager j J h (k+1) x*
      (Primary.residual j J h k x i+Primary.residual j J h (k+1) x i))≤
      j*(vectorNorm (Primary.residual j J h k x)+vectorNorm (Primary.residual j J h (k+1) x)) := by
    rw [show vectorNorm (fun i=>j*onsager j J h (k+1) x*
      (Primary.residual j J h k x i+Primary.residual j J h (k+1) x i))=
      |j*onsager j J h (k+1) x| *vectorNorm (Primary.residual j J h k x+Primary.residual j J h (k+1) x) from SKGap.vectorNorm_smul ..,
      abs_of_nonneg (mul_nonneg hj hb.1)]
    exact mul_le_mul (mul_le_of_le_one_right hj hb.2) (SKGap.vectorNorm_add_le _ _) (vectorNorm_nonneg _) hj
  have hlast : vectorNorm (fun i=>j*(onsager j J h (k+2) x-onsager j J h (k+1) x)*mag j J h (k+2) x i)≤
      2*j*vectorNorm (Primary.residual j J h (k+1) x) := by
    rw [show vectorNorm (fun i=>j*(onsager j J h (k+2) x-onsager j J h (k+1) x)*mag j J h (k+2) x i)=
      |j*(onsager j J h (k+2) x-onsager j J h (k+1) x)| *vectorNorm (mag j J h (k+2) x) from SKGap.vectorNorm_smul ..,
      abs_mul,abs_of_nonneg hj]
    calc
      _ ≤ j*|onsager j J h (k+2) x-onsager j J h (k+1) x| *Real.sqrt (n:ℝ) :=
        mul_le_mul_of_nonneg_left (mag_vectorNorm j J h (k+2) x) (by positivity)
      _ ≤ j*(2*vectorNorm (Primary.residual j J h (k+1) x)) := by
        rw [mul_assoc]
        exact mul_le_mul_of_nonneg_left (onsager_residual_difference hn j J h (k+1) x) hj
      _ = _ := by ring
  rw [primary_tap_residual hn]
  exact (SKGap.vectorNorm_add_le _ _).trans ((add_le_add
    ((SKGap.vectorNorm_sub_le _ _).trans (add_le_add
      ((vectorNorm_matrix_mul _ _).trans (mul_le_mul_of_nonneg_right hJ (vectorNorm_nonneg _)))
      hterm)) hlast).trans_eq (by ring))

lemma magnetization_vector_lipschitz (y r : Fin n→ℝ) :
    vectorNorm (SKGap.magnetization y-SKGap.magnetization r)≤vectorNorm (y-r) := by
  apply (sq_le_sq₀ (vectorNorm_nonneg _) (vectorNorm_nonneg _)).mp
  simp only [vectorNorm_sq,Pi.sub_apply,SKGap.magnetization]
  exact Finset.sum_le_sum fun i _=>by
    simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg _) (tanh_lipschitz (r i) (y i)) 2

end SKGapCutoff.Recipe

end
end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Entropy_WeightedMean
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
variable {Ω : Type u} {N : Ω→ℕ} {j R B W C ρ : ℝ}
variable {J : ∀a,Interaction (N a)} {h e : ∀a,Fin (N a)→ℝ}

lemma magnetization_norm {n : ℕ} (r : Fin n→ℝ) :
    vectorNorm (SKGap.magnetization r)≤Real.sqrt (n:ℝ) := by
  apply nonneg_le_nonneg_of_sq_le_sq (Real.sqrt_nonneg _)
  simp only [←sq,vectorNorm_sq,Real.sq_sqrt (Nat.cast_nonneg n)]
  calc
    _ ≤ ∑_i:Fin n,(1:ℝ) := Finset.sum_le_sum (fun i _=>(Real.tanh_sq_lt_one (r i)).le)
    _ = _ := by simp

end SKGapCutoff.Recipe

end
end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Stability_ImplicitComparison
attribute [-instance] _root_.OAI.SKGap.ComplexMatrix.frobeniusInnerProduct
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped BigOperators
namespace SKGapCutoff.Recipe
open Matrix SKGap.Stein
variable {n : ℕ}

lemma implicit_scalar_cancellation (m t v : Fin n→ℝ) (b b₀ q : ℝ)
    (hb : (∑i,(m i)^2)=(n:ℝ)*(1-b)) (hq : (∑i,(t i)^2)=(n:ℝ)*q) :
    (∑i,(m i-t i)*(v i+t i))+(n:ℝ)*(b-b₀)=
      (n:ℝ)*(1-b₀-q)+(∑i,(v i-m i)*(m i-t i)) := by
  have HH : (∑i,(m i-t i)*(v i+t i))-(∑i,(v i-m i)*(m i-t i))=
      (∑i,(m i)^2)-(∑i,(t i)^2) := by
    rw [←Finset.sum_sub_distrib,←Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl;intro i _;ring
  rw [hb,hq] at HH
  linarith

theorem implicit_comparison (J : Interaction n) (hJ : J.IsSymm)
    (z r h v w y w₀ d₀ : Fin n→ℝ) (j b b₀ q χ c : ℝ)
    (hroot : ∀i,r i-h i-J.mulVec (fun k=>Real.tanh (r k)) i+j*(1-q)*Real.tanh (r i)=0)
    (hb : (∑i,(Real.tanh (z i))^2)=(n:ℝ)*(1-b))
    (hq : (∑i,(Real.tanh (r i))^2)=(n:ℝ)*q)
    (hw : ∀i,w i=w₀ i+phi (z i) (r i) (j*(1-b₀-q))*(y i-j*c*Real.tanh (r i)))
    (hy : ∀i,y i=J.mulVec w i-j*χ*w i-j*c*v i)
    (hc : (n:ℝ)*c=∑i,(d₀ i+phiZ (z i) (r i) (j*(1-b₀-q))*(y i-j*c*Real.tanh (r i)))) :
    (∑i,(z i-h i-J.mulVec (fun k=>Real.tanh (z k)) i+j*b₀*Real.tanh (z i))*w i)-j*(b-b₀)*(n:ℝ)*c=
      (∑i,((z i-r i-j*(1-b₀-q)*Real.tanh (z i))*w₀ i-j*(1-b₀-q)*d₀ i))+
      j*(1-q-χ)*(∑i,(Real.tanh (z i)-Real.tanh (r i))*w i)-
      j*c*(∑i,(v i-Real.tanh (z i))*(Real.tanh (z i)-Real.tanh (r i))) := by
  let m:=fun i=>Real.tanh (z i)
  let t:=fun i=>Real.tanh (r i)
  let p:=m-t
  let a:=j*(1-b₀-q)
  have hfield (i : Fin n) : z i-h i-J.mulVec m i+j*b₀*m i=
      z i-r i-a*m i-J.mulVec p i+j*(1-q)*p i := by
    have hr:=hroot i
    dsimp only [p,m,t,a,Pi.sub_apply]
    rw [Matrix.mulVec_sub]
    simp only [Pi.sub_apply]
    linarith
  have hcoord (i : Fin n) :
      (z i-r i-a*m i)*w i=(z i-r i-a*m i)*w₀ i-a*d₀ i+
        p i*(y i-j*c*t i)+a*(d₀ i+phiZ (z i) (r i) a*(y i-j*c*t i)) := by
    have hh:=phi_stein (z i) (r i) a
    rw [hw i]
    dsimp only [p,m,t,a,Pi.sub_apply] at *
    linear_combination (y i-j*c*Real.tanh (r i))*hh
  have hsym : (∑i,J.mulVec p i*w i)=(∑i,p i*J.mulVec w i) := by
    have hh:=dotProduct_transpose_mulVec J w p
    rw [hJ] at hh
    simpa only [dotProduct,mul_comm] using hh
  have hscalar:=implicit_scalar_cancellation m t v b b₀ q hb hq
  have hc' : (n:ℝ)*c=∑i,(d₀ i+phiZ (z i) (r i) a*(y i-j*c*t i)) := hc
  have hcoords : (∑i,(z i-r i-a*m i)*w i)=
      (∑i,((z i-r i-a*m i)*w₀ i-a*d₀ i))+
      (∑i,p i*(y i-j*c*t i))+a*((n:ℝ)*c) := by
    simp_rw [hcoord]
    rw [Finset.sum_add_distrib,Finset.sum_add_distrib,←Finset.mul_sum,hc']
  have hpy : (∑i,p i*(y i-j*c*t i))=(∑i,p i*J.mulVec w i)-
      j*χ*(∑i,p i*w i)-j*c*(∑i,p i*(v i+t i)) := by
    simp only [hy,Finset.mul_sum,←Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl;intro i _;ring
  have hsum : (∑i,(z i-h i-J.mulVec m i+j*b₀*m i)*w i)=
      (∑i,((z i-r i-a*m i)*w₀ i-a*d₀ i))+a*((n:ℝ)*c)+
      j*(1-q-χ)*(∑i,p i*w i)-j*c*(∑i,p i*(v i+t i)) := by
    calc
      _ = (∑i,(z i-r i-a*m i)*w i)-(∑i,J.mulVec p i*w i)+j*(1-q)*(∑i,p i*w i) := by
        simp only [hfield,sub_mul,add_mul,Finset.sum_add_distrib,Finset.sum_sub_distrib,Finset.mul_sum]
        congr 1;apply Finset.sum_congr rfl;intros;ring
      _ = _ := by rw [hcoords,hpy,hsym];ring
  change (∑i,(z i-h i-J.mulVec m i+j*b₀*m i)*w i)-j*(b-b₀)*(n:ℝ)*c=_
  rw [hsum]
  dsimp only [a,p,m,t,Pi.sub_apply] at *
  linear_combination -j*c*hscalar

end SKGapCutoff.Recipe

end
end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Localization_LiteralInitialRecipe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped BigOperators
namespace SKGapCutoff.Recipe
open SKGap.Stein Primary
variable {n : ℕ}

lemma initialKernel_phi (r : ℝ) (u : InitialArgs) :
    initialKernel phiExpr r u=phi (u (.inl ())) r (u (.inr false)) := moment_base _ _ _
lemma phiExpr_dz (z r a : ℝ) : phiExpr.dz.eval z r a=phiZ z r a := by
  have H:=phiExpr.hasDerivAt_z z r a
  have He : phiExpr.eval=phi := funext fun _=>funext fun _=>funext fun _=>moment_base _ _ _
  rw [He] at H
  exact H.unique (phi_hasDerivAt z r a)

lemma initialGradient_primary (f : KernelExpr) (r : ℝ) (u : InitialArgs) :
    partialAt (initialGradient f r u) (.inl ())=f.dz.eval (u (.inl ())) r (u (.inr false)) := by
  simp [partialAt,initialGradient,phiSelect,KernelExpr.gradient,grad3,grad2,
    ContinuousLinearMap.toSpanSingleton_apply,eval3]

lemma literalInitial_coefficient (J : Interaction n) (j d : ℝ) (f : KernelExpr)
    (z m : VectorFields n) (a c : Spin n→ℝ) (r e : Fin n→ℝ) (x : Spin n) (i : Fin n) :
    (literalInitial J j d f z m a c r e).implicitCoefficient x i=phi (z x i) (r i) (a x) := by
  simp [OrdinaryData.implicitCoefficient,OrdinaryData.auxCoefficient,literalInitial,
    coefficient,initialKernel_phi,localArgs]

lemma literalInitial_source (J : Interaction n) (j d : ℝ) (f : KernelExpr)
    (z m y : VectorFields n) (a c : Spin n→ℝ) (r e : Fin n→ℝ) (hd : d≠0) (x : Spin n) (i : Fin n) :
    (literalInitial J j d f z m a c r e).sourceOf 1 (fun _=>y) x i=
      f.eval (z x i) (r i) (a x)*e i+
        phi (z x i) (r i) (a x)*(y x i-j*c x*Real.tanh (r i)) := by
  simp [OrdinaryData.sourceOf,OrdinaryData.seedCoefficient,OrdinaryData.auxCoefficient,
    literalInitial,coefficient,initialKernel,phiExpr,KernelExpr.eval,moment_base,localArgs]
  field_simp
  ring

lemma literalInitial_partial (J : Interaction n) (j d : ℝ) (f : KernelExpr)
    (z m y : VectorFields n) (a c : Spin n→ℝ) (r e : Fin n→ℝ) (hd : d≠0) (x : Spin n) (i : Fin n) :
    (literalInitial J j d f z m a c r e).implicitPartial y x i=
      f.dz.eval (z x i) (r i) (a x)*e i+
        phiZ (z x i) (r i) (a x)*(y x i-j*c x*Real.tanh (r i)) := by
  simp only [OrdinaryData.implicitPartial,OrdinaryData.partialOf,OrdinaryData.seedPartial,
    OrdinaryData.auxPartial,localPartial,literalInitial,Fintype.sum_bool,Fin.sum_univ_one]
  simp only [Bool.false_eq_true,↓reduceIte,initialGradient_primary]
  simp [partialAt,initialGradient,phiSelect,KernelExpr.gradient,grad3,grad2,
    ContinuousLinearMap.toSpanSingleton_apply,eval3,localArgs,phiExpr_dz]
  field_simp
  ring

end SKGapCutoff.Recipe

end
end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Localization_PhiCoefficient
attribute [-instance] _root_.OAI.SKGap.ComplexMatrix.frobeniusInnerProduct
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open MeasureTheory
namespace SKGap.Stein

lemma phi_hasDerivAt_a (z r a : ℝ) : HasDerivAt (fun a=>phi z r a) (phiA z r a) a := by
  unfold phi phiA
  apply hasDerivAt_integral01
    (F:=fun a u=>weight a u*Real.cosh (u*(z-r))/(Real.cosh z*Real.cosh r))
    (F':=fun a u=>((1-u^2)/2)*(weight a u*Real.cosh (u*(z-r))/(Real.cosh z*Real.cosh r)))
  · unfold weight; fun_prop
  · unfold weight; fun_prop
  · intro a u
    have h:=((((hasDerivAt_id a).mul_const (1-u^2)).div_const 2).exp.mul_const
      (Real.cosh (u*(z-r)))).div_const (Real.cosh z*Real.cosh r)
    convert! h using 1
    all_goals try with_reducible_and_instances rfl
    try dsimp [weight]
    ring

lemma phiA_nonneg (z r a : ℝ) : 0≤phiA z r a := by
  apply intervalIntegral.integral_nonneg (by norm_num : (0:ℝ)≤1)
  intro u hu
  have hu2 : u^2≤1 := by nlinarith [hu.1,hu.2]
  apply mul_nonneg (by linarith)
  exact div_nonneg (mul_pos (Real.exp_pos _) (Real.cosh_pos _)).le
    (mul_pos (Real.cosh_pos _) (Real.cosh_pos _)).le

lemma phiA_relative_bound (z r a : ℝ) : phiA z r a≤phi z r a/2 := by
  have H:=intervalIntegral.integral_mono_on (μ:=volume) (a:=(0:ℝ)) (b:=1) (by norm_num)
    (f:=fun u=>((1-u^2)/2)*(weight a u*Real.cosh (u*(z-r))/(Real.cosh z*Real.cosh r)))
    (g:=fun u=>(weight a u*Real.cosh (u*(z-r))/(Real.cosh z*Real.cosh r))/2)
    (by apply Continuous.intervalIntegrable; unfold weight; fun_prop)
    (((continuous_integrand z r a).div_const 2).intervalIntegrable _ _)
    (by
      intro u hu
      have hp : 0≤weight a u*Real.cosh (u*(z-r))/(Real.cosh z*Real.cosh r) := by
        apply div_nonneg (mul_pos (Real.exp_pos _) (Real.cosh_pos _)).le
        exact (mul_pos (Real.cosh_pos _) (Real.cosh_pos _)).le
      nlinarith [mul_nonneg (sq_nonneg u) hp])
  simpa only [intervalIntegral.integral_div,phiA,phi] using H

lemma phi_lipschitz_z (z z' r a : ℝ) :
    |phi z' r a-phi z r a|≤(2*Real.exp (|a|/2))*|z'-z| := by
  have H:=Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun q (_ : q∈(Set.univ : Set ℝ))=>(phi_hasDerivAt q r a).hasDerivWithinAt)
    (fun q _=>show ‖phiZ q r a‖≤2*Real.exp (|a|/2) by
      rw [Real.norm_eq_abs]
      exact (phiZ_relative_bound q r a).trans (by nlinarith [phi_le_exp q r a]))
    convex_univ (Set.mem_univ z) (Set.mem_univ z')
  simpa only [Real.norm_eq_abs] using H

lemma phi_lipschitz_a (z r a : ℝ) :
    |phi z r a-phi z r 0|≤(Real.exp (|a|/2)/2)*|a| := by
  have H:=Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun q (_ : q∈Set.Icc (-|a|) |a|)=>(phi_hasDerivAt_a z r q).hasDerivWithinAt)
    (fun q hq=>show ‖phiA z r q‖≤Real.exp (|a|/2)/2 by
      rw [Real.norm_eq_abs,abs_of_nonneg (phiA_nonneg _ _ _)]
      have hq' : |q|≤|a| := abs_le.mpr hq
      have he : Real.exp (|q|/2)≤Real.exp (|a|/2) := Real.exp_le_exp.mpr (by linarith)
      exact (phiA_relative_bound z r q).trans (by linarith [phi_le_exp z r q]))
    (convex_Icc (-|a|) |a|)
    (show (0:ℝ)∈Set.Icc (-|a|) |a| by constructor <;> linarith [abs_nonneg a])
    (show a∈Set.Icc (-|a|) |a| from ⟨neg_abs_le a,le_abs_self a⟩)
  simpa only [Real.norm_eq_abs,sub_zero] using H

theorem phi_near_root (z r a : ℝ) :
    |phi z r a-SKGapCutoff.scalarVariance r|≤
      Real.exp (|a|/2)*(2*|z-r|+|a|/2) := by
  have he : phi r r 0=SKGapCutoff.scalarVariance r := by
    rw [phi_zero_diagonal,SKGapCutoff.scalarVariance_eq]
  have h1:=phi_lipschitz_z r z r a
  have h2:=phi_lipschitz_a r r a
  have h3:=abs_add_le (phi z r a-phi r r a) (phi r r a-phi r r 0)
  rw [he] at h2 h3
  have hh : phi z r a-phi r r a+(phi r r a-SKGapCutoff.scalarVariance r)=
      phi z r a-SKGapCutoff.scalarVariance r := by ring
  rw [hh] at h3
  nlinarith only [h1,h2,h3]

end SKGap.Stein

end
end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Stability_ImplicitLinear
attribute [-instance] _root_.OAI.SKGap.ComplexMatrix.frobeniusInnerProduct
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
namespace SKGap.ImplicitLinear
local notation "⟪" x ", " y "⟫" => inner ℝ x y
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

lemma quadratic_perturbation (M S : E →L[ℝ] E) {c e : ℝ}
    (hS : ∀v,c*‖v‖^2 ≤ ⟪v, S v⟫) (hMS : ‖M-S‖≤e) (v : E) :
    (c-e)*‖v‖^2 ≤ ⟪v, M v⟫ := by
  have hI:=abs_real_inner_le_norm v ((M-S) v)
  have hO:=(M-S).le_opNorm v
  have hm:=mul_le_mul_of_nonneg_right hMS (norm_nonneg v)
  have hh:=mul_le_mul_of_nonneg_left (hO.trans hm) (norm_nonneg v)
  have he : ⟪v, (M-S) v⟫=⟪v, M v⟫-⟪v, S v⟫ := by simp only [sub_apply,inner_sub_right]
  rw [he] at hI
  have H := (neg_abs_le (⟪v, M v⟫-⟪v, S v⟫)).trans (le_refl _)
  nlinarith [hS v]

end SKGap.ImplicitLinear

end
end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Stability_ImplicitCoefficient
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped BigOperators
namespace SKGapCutoff.Recipe
open SKGap.Stein Primary
variable {n : ℕ}

lemma vectorNorm_const (c : ℝ) : vectorNorm (fun _ : Fin n=>c)=|c| *Real.sqrt n := by
  apply (sq_eq_sq₀ (vectorNorm_nonneg _) (by positivity)).mp
  rw [vectorNorm_sq,mul_pow,sq_abs,Real.sq_sqrt (Nat.cast_nonneg n)]
  simp [mul_comm]

lemma vectorNorm_neg (v : Fin n→ℝ) : vectorNorm (-v)=vectorNorm v := by
  exact norm_neg (WithLp.toLp 2 v : EuclideanSpace ℝ (Fin n))
lemma vectorNorm_tanh (z : Fin n→ℝ) : vectorNorm (fun i=>Real.tanh (z i))≤Real.sqrt n := by
  simpa only [vectorNorm_const,abs_one,one_mul] using
    (vectorNorm_mono (u:=fun i=>Real.tanh (z i)) (v:=fun _=>1)
      (fun i=>by simpa using (Real.abs_tanh_lt_one (z i)).le))
lemma vectorNorm_tanh_diff (z r : Fin n→ℝ) :
    vectorNorm (fun i=>Real.tanh (z i)-Real.tanh (r i))≤vectorNorm (z-r) :=
  vectorNorm_mono fun i=>tanh_lipschitz (r i) (z i)

lemma abs_logSlope_le_two (z r a : ℝ) : |logSlope z r a|≤2 := by
  rw [logSlope,abs_div,abs_of_pos (phi_pos z r a),div_le_iff₀ (phi_pos z r a)]
  exact phiZ_relative_bound z r a

lemma vectorNorm_logSlope (z r : Fin n→ℝ) (a : ℝ) :
    vectorNorm (fun i=>logSlope (z i) (r i) a)≤2*Real.sqrt n := by
  simpa only [vectorNorm_const,abs_of_pos (by norm_num : (0:ℝ)<2)] using
    (vectorNorm_mono (u:=fun i=>logSlope (z i) (r i) a) (v:=fun _=>2)
      (fun i=>by simpa using abs_logSlope_le_two (z i) (r i) a))

lemma vectorNorm_logSlope_near (z r : Fin n→ℝ) (a : ℝ) :
    vectorNorm (fun i=>logSlope (z i) (r i) a+Real.tanh (r i))≤3*vectorNorm (z-r) := by
  have h:=vectorNorm_mono (u:=fun i=>logSlope (z i) (r i) a+Real.tanh (r i))
    (v:=fun i=>3*(z i-r i)) (fun i=>by simpa only [abs_mul,abs_of_pos (by norm_num : (0:ℝ)<3)] using
      (logSlope_near_diagonal (z i) (r i) a))
  apply h.trans_eq
  convert! vectorNorm_smul 3 (z-r) using 1
  all_goals try with_reducible_and_instances rfl
  norm_num

lemma phi_near_current (z r a : ℝ) {R : ℝ} (ha : |a|≤R) :
    |phi z r a-scalarVariance z|≤
      (2*Real.exp (R/2)+2)*|z-r|+(Real.exp (R/2)/2)*|a| := by
  have he:=Real.exp_le_exp.mpr (show |a|/2≤R/2 by linarith)
  have h₁:=(phi_near_root z r a).trans (mul_le_mul_of_nonneg_right he (by positivity))
  have h₂:=scalarVariance_lipschitz r z
  have h₃:=abs_sub_le (phi z r a) (scalarVariance r) (scalarVariance z)
  rw [abs_sub_comm (scalarVariance r)] at h₃
  linarith

lemma vectorNorm_phi_near_current (z r : Fin n→ℝ) (a : ℝ) {R : ℝ} (ha : |a|≤R) :
    vectorNorm (fun i=>phi (z i) (r i) a-scalarVariance (z i))≤
      (2*Real.exp (R/2)+2)*vectorNorm (z-r)+(Real.exp (R/2)/2)*|a| *Real.sqrt n := by
  let E:=Real.exp (R/2)
  have he:0≤E := (Real.exp_pos _).le
  have hmono:=vectorNorm_mono (u:=fun i=>phi (z i) (r i) a-scalarVariance (z i))
    (v:=fun i=>(2*E+2)*|z i-r i|+(E/2)*|a|) (fun i=>by
      rw [abs_of_nonneg (show 0≤(2*E+2)*|z i-r i|+(E/2)*|a| from by positivity)]
      exact phi_near_current _ _ _ ha)
  apply hmono.trans
  have ht:=vectorNorm_add ((2*E+2) • (fun i=>|z i-r i|)) (fun _=>(E/2)*|a|)
  rw [vectorNorm_smul,abs_of_nonneg (by positivity : 0≤2*E+2),
    vectorNorm_abs,vectorNorm_const,abs_of_nonneg (by positivity : 0≤(E/2)*|a|)] at ht
  exact ht

lemma normalized_mean_bound (u : Fin n→ℝ) (hn : 0<n) :
    |(∑i,u i)/(n:ℝ)|≤vectorNorm u/Real.sqrt n := by
  have hnR : (0:ℝ)<n:=Nat.cast_pos.mpr hn
  have hs : 0<Real.sqrt n:=Real.sqrt_pos.mpr hnR
  have hh:=siteMean_square (fun _=>u) (fun _=>false) hn
  change (n:ℝ)*((∑i,u i)/(n:ℝ))^2≤(vectorNorm u)^2 at hh
  apply (sq_le_sq₀ (abs_nonneg _) (div_nonneg (vectorNorm_nonneg _) hs.le)).mp
  rw [sq_abs, div_pow, div_pow, Real.sq_sqrt hnR.le]
  exact (le_div_iff₀ hnR).mpr (by simpa only [div_pow, mul_comm] using hh)

theorem implicit_coefficient_bounds (z r : Fin n→ℝ) (a : ℝ) (hn : 0<n)
    {R ρ : ℝ} (hρ : 0≤ρ) (ha : |a|≤R) (haρ : |a|≤ρ)
    (hz : vectorNorm (z-r)≤ρ*Real.sqrt n) :
    let E:=Real.exp (R/2)
    let A:=fun i=>phi (z i) (r i) a
    let ell:=fun i=>logSlope (z i) (r i) a
    let q:=fun i=>Real.tanh (z i)
    (∀i,0<A i ∧ A i≤E) ∧
    vectorNorm (A-(fun i=>scalarVariance (z i)))≤(3*E+2)*ρ*Real.sqrt n ∧
    |(∑i,A i)/(n:ℝ)-(∑i,scalarVariance (z i))/(n:ℝ)|≤(3*E+2)*ρ ∧
    vectorNorm (ell+q)≤4*ρ*Real.sqrt n ∧
    vectorNorm ell≤2*Real.sqrt n ∧ vectorNorm q≤Real.sqrt n := by
  dsimp only
  have hnR : (0:ℝ)<n:=Nat.cast_pos.mpr hn
  have hs : 0<Real.sqrt n:=Real.sqrt_pos.mpr hnR
  have he:0<Real.exp (R/2):=Real.exp_pos _
  have hA : vectorNorm (fun i=>phi (z i) (r i) a-scalarVariance (z i))≤
      (3*Real.exp (R/2)+2)*ρ*Real.sqrt n := by
    apply (vectorNorm_phi_near_current z r a ha).trans
    have h₁:=mul_le_mul_of_nonneg_left hz (by positivity : 0≤2*Real.exp (R/2)+2)
    have h₂:=mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left haρ
      (by positivity : 0≤Real.exp (R/2)/2)) hs.le
    nlinarith only [h₁,h₂,mul_nonneg he.le (mul_nonneg hρ hs.le)]
  refine ⟨fun i=>⟨phi_pos _ _ _,(phi_le_exp ..).trans (Real.exp_le_exp.mpr (by linarith))⟩,hA,?_,?_,
    vectorNorm_logSlope z r a,vectorNorm_tanh z⟩
  · rw [←sub_div,←Finset.sum_sub_distrib]
    exact (normalized_mean_bound _ hn).trans ((div_le_div_of_nonneg_right hA hs.le).trans_eq (by field_simp))
  · have h₁:=vectorNorm_logSlope_near z r a
    have h₂:=vectorNorm_tanh_diff z r
    have h₃:=vectorNorm_add (fun i=>logSlope (z i) (r i) a+Real.tanh (r i))
      (fun i=>Real.tanh (z i)-Real.tanh (r i))
    have heq : (fun i=>logSlope (z i) (r i) a+Real.tanh (r i))+
        (fun i=>Real.tanh (z i)-Real.tanh (r i))=
        (fun i=>logSlope (z i) (r i) a)+(fun i=>Real.tanh (z i)) := by ext i; dsimp; ring
    rw [heq] at h₃
    nlinarith only [h₁,h₂,h₃,hz]

end SKGapCutoff.Recipe

end
end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Stability_ImplicitPerturb
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped BigOperators
namespace SKGapCutoff.Recipe
open SKGap.Stein Primary SKGap.ImplicitSystem
variable {n : ℕ}

lemma vectorNorm_implicit_rank (z r m : Fin n→ℝ) {ρ : ℝ}
    (hz : vectorNorm (z-r)≤ρ*Real.sqrt n)
    (hm : vectorNorm (m-(fun i=>Real.tanh (r i)))≤ρ*Real.sqrt n) :
    vectorNorm (m+(fun i=>Real.tanh (r i))-(2:ℝ) • (fun i=>Real.tanh (z i)))≤
      3*ρ*Real.sqrt n := by
  let q:=fun i=>Real.tanh (z i)
  let t:=fun i=>Real.tanh (r i)
  have ht:=vectorNorm_tanh_diff z r
  have ht' : vectorNorm (t-q)≤ρ*Real.sqrt n := by
    have he : t-q= -(q-t) := by ext i; dsimp; ring
    rw [he,vectorNorm_neg]
    exact ht.trans hz
  have hh:=vectorNorm_add (m-t) ((2:ℝ) • (t-q))
  rw [vectorNorm_smul,abs_of_pos (by norm_num : (0:ℝ)<2)] at hh
  have he : (m-t)+(2:ℝ) • (t-q)=m+t-(2:ℝ) • q := by ext i; dsimp; ring
  rw [he] at hh
  exact hh.trans (by nlinarith only [hm,ht'])

theorem implicit_normalized_perturbation (z r m : Fin n→ℝ) (a j : ℝ)
    (X : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (hn : 0<n) {R ρ : ℝ} (hρ : 0≤ρ) (ha : |a|≤R) (haρ : |a|≤ρ)
    (hz : vectorNorm (z-r)≤ρ*Real.sqrt n)
    (hm : vectorNorm (m-(fun i=>Real.tanh (r i)))≤ρ*Real.sqrt n)
    (hX : ‖X‖^2≤Real.exp (R/2)) :
    let χ:=(∑i,phi (z i) (r i) a)/(n:ℝ)
    let b:=(∑i,scalarVariance (z i))/(n:ℝ)
    let ell:EuclideanSpace ℝ (Fin n):=WithLp.toLp 2 (fun i=>logSlope (z i) (r i) a)
    let q:EuclideanSpace ℝ (Fin n):=WithLp.toLp 2 (fun i=>Real.tanh (z i))
    let t:EuclideanSpace ℝ (Fin n):=WithLp.toLp 2 (fun i=>Real.tanh (r i))
    let M:EuclideanSpace ℝ (Fin n):=WithLp.toLp 2 m
    |j| *|χ-b| *‖X‖^2+|j*(n:ℝ)⁻¹| *‖X‖^2*
      (‖M+t-(2:ℝ) • q‖*‖ell‖+2*‖q‖*‖ell+q‖)≤
        |j| *Real.exp (R/2)*(3*Real.exp (R/2)+16)*ρ := by
  dsimp only
  obtain ⟨hA,hAv,hχ,hEllq,hEll,hq⟩:=implicit_coefficient_bounds z r a hn hρ ha haρ hz
  have hnR : (0:ℝ)<n:=Nat.cast_pos.mpr hn
  have hs : 0≤Real.sqrt n:=Real.sqrt_nonneg _
  have he:0≤Real.exp (R/2):=(Real.exp_pos _).le
  have hv:=vectorNorm_implicit_rank z r m hz hm
  have hbr : vectorNorm (m+(fun i=>Real.tanh (r i))-(2:ℝ) • (fun i=>Real.tanh (z i)))*
      vectorNorm (fun i=>logSlope (z i) (r i) a)+
      2*vectorNorm (fun i=>Real.tanh (z i))*
      vectorNorm ((fun i=>logSlope (z i) (r i) a)+(fun i=>Real.tanh (z i)))≤14*ρ*(n:ℝ) := by
    have h₁:=mul_le_mul hv hEll (vectorNorm_nonneg _) (by positivity : 0≤3*ρ*Real.sqrt n)
    have h₂:=mul_le_mul (mul_le_mul_of_nonneg_left hq (by norm_num : (0:ℝ)≤2)) hEllq
      (vectorNorm_nonneg _) (by positivity : 0≤2*Real.sqrt n)
    apply (add_le_add h₁ h₂).trans_eq
    calc
      _ = 14*ρ*(Real.sqrt n)^2 := by ring
      _ = _ := by rw [Real.sq_sqrt hnR.le]
  change |j| *|_| *‖X‖^2+|j*(n:ℝ)⁻¹| *‖X‖^2*
    (vectorNorm _*vectorNorm _+2*vectorNorm _*vectorNorm _)≤_
  calc
    _ ≤ |j| *((3*Real.exp (R/2)+2)*ρ)*Real.exp (R/2)+
        |j*(n:ℝ)⁻¹| *Real.exp (R/2)*(14*ρ*(n:ℝ)) := by
      apply add_le_add
      · exact mul_le_mul (mul_le_mul_of_nonneg_left hχ (abs_nonneg _)) hX (sq_nonneg _) (by positivity)
      · exact mul_le_mul (mul_le_mul_of_nonneg_left hX (abs_nonneg _)) hbr
          (add_nonneg (mul_nonneg (vectorNorm_nonneg _) (vectorNorm_nonneg _))
            (mul_nonneg (mul_nonneg (by norm_num) (vectorNorm_nonneg _)) (vectorNorm_nonneg _))) (by positivity)
    _ = _ := by
      rw [abs_mul,abs_inv,abs_of_pos hnR]
      field_simp
      ring

lemma implicit_rho_threshold (j R δ ρ : ℝ) (hδ : 0<δ)
    (hρ : ρ≤δ/(2*(|j| *Real.exp (R/2)*(3*Real.exp (R/2)+16)+1))) :
    |j| *Real.exp (R/2)*(3*Real.exp (R/2)+16)*ρ≤δ/2 := by
  let K:=|j| *Real.exp (R/2)*(3*Real.exp (R/2)+16)
  have hK : 0≤K := by dsimp [K]; positivity
  have hp : 0<2*(K+1) := by positivity
  apply (mul_le_mul_of_nonneg_left hρ hK).trans
  change K*(δ/(2*(K+1)))≤δ/2
  apply (le_div_iff₀ (by norm_num : (0:ℝ)<2)).mpr
  rw [mul_assoc,div_mul_eq_mul_div,←mul_div_assoc]
  apply (div_le_iff₀ hp).mpr
  nlinarith

end SKGapCutoff.Recipe

end
end

section

noncomputable section
open scoped BigOperators
namespace SKGapCutoff.Recipe
open SKGap.Stein Primary SKGap.ImplicitSystem Matrix
variable {n : ℕ}

lemma phiSqrt_bound (z r : Fin n→ℝ) (a : ℝ) {R : ℝ} (ha : |a|≤R) :
    ‖phiSqrt z r a‖^2≤Real.exp (R/2) := by
  have he : 0≤Real.exp (R/2):=(Real.exp_pos _).le
  have hh : ‖phiSqrt z r a‖≤Real.sqrt (Real.exp (R/2)) := by
    apply SKGap.opNorm_diagonal_le (Real.sqrt_nonneg _)
    intro i
    rw [abs_of_nonneg (Real.sqrt_nonneg _)]
    exact Real.sqrt_le_sqrt ((phi_le_exp ..).trans (Real.exp_le_exp.mpr (by linarith)))
  exact (pow_le_pow_left₀ (norm_nonneg _) hh 2).trans_eq (Real.sq_sqrt he)

end SKGapCutoff.Recipe

end
end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Localization_LiteralInitialSystem
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped BigOperators
namespace SKGapCutoff.Recipe
open SKGap.Stein Primary SKGap.ImplicitSystem Matrix
variable {n : ℕ}

lemma literalInitial_partial_source (J : Interaction n) (j d : ℝ) (f : KernelExpr)
    (z m w y : VectorFields n) (a c : Spin n→ℝ) (r e : Fin n→ℝ) (hd : d≠0) (x : Spin n)
    (hw : w x=(literalInitial J j d f z m a c r e).sourceOf 1 (fun _=>y) x) :
    (literalInitial J j d f z m a c r e).implicitPartial y x=
      fun i=>logSlope (z x i) (r i) (a x)*w x i+initialP f z a r e x i := by
  ext i
  rw [literalInitial_partial _ _ _ _ _ _ _ _ _ _ _ hd,hw,literalInitial_source _ _ _ _ _ _ _ _ _ _ _ hd]
  dsimp only [initialP,logSlope]
  field_simp [(phi_pos (z x i) (r i) (a x)).ne']
  ring

lemma literalInitial_field (J : Interaction n) (j d : ℝ) (f : KernelExpr)
    (z m w y : VectorFields n) (a c : Spin n→ℝ) (r e : Fin n→ℝ) (x : Spin n)
    (hw : w x=(literalInitial J j d f z m a c r e).sourceOf 1 (fun _=>y) x)
    (hc : c x=siteMean ((literalInitial J j d f z m a c r e).implicitPartial y) x) :
    (literalInitial J j d f z m a c r e).fieldOf 1 (fun _=>w) (fun _=>y) x=
      fun i=>J.mulVec (w x) i-j*siteMean (fun x i=>phi (z x i) (r i) (a x)) x*w x i-j*c x*m x i := by
  ext i
  simp only [OrdinaryData.fieldOf,←hw,Fintype.sum_unique]
  change J.mulVec (w x) i-j*(siteMean ((literalInitial J j d f z m a c r e).implicitPartial y) x*m x i)-
    j*(siteMean ((literalInitial J j d f z m a c r e).implicitCoefficient) x*w x i)=_
  have he : (literalInitial J j d f z m a c r e).implicitCoefficient=fun x i=>phi (z x i) (r i) (a x) := by
    ext v k; exact literalInitial_coefficient ..
  rw [he,←hc]
  ring

lemma initial_scalar_equation (f : KernelExpr) (z w : VectorFields n)
    (a c : Spin n→ℝ) (r e : Fin n→ℝ) (x : Spin n) :
    c x=(n:ℝ)⁻¹*inner ℝ (WithLp.toLp 2 (fun i=>logSlope (z x i) (r i) (a x)) : Euclid n)
        (WithLp.toLp 2 (w x))+siteMean (initialP f z a r e) x ↔
      c x=siteMean (fun x i=>logSlope (z x i) (r i) (a x)*w x i+initialP f z a r e x i) x := by
  simp only [EuclideanSpace.inner_eq_star_dotProduct,star_trivial,dotProduct,siteMean,
    Finset.sum_add_distrib,div_eq_mul_inv]
  simp [mul_comm,add_comm,mul_add]

end SKGapCutoff.Recipe

end
end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Localization_LiteralSystemBridge
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped BigOperators
namespace SKGapCutoff.Recipe
open SKGap.Stein Primary SKGap.ImplicitSystem Matrix
variable {n : ℕ}

lemma phiDiagonal_apply (z r : Fin n→ℝ) (a : ℝ) (v : Euclid n) (i : Fin n) :
    phiDiagonal z r a v i=phi (z i) (r i) a*v i := by
  change (toEuclideanCLM (𝕜:=ℝ) (diagonal (fun k=>phi (z k) (r k) a)) (WithLp.toLp 2 v.ofLp)) i=_
  simp only [toEuclideanCLM_toLp,WithLp.ofLp_toLp,mulVec_diagonal]

lemma literal_first_equation (J : Interaction n) (j d : ℝ) (f : KernelExpr)
    (z m w y : VectorFields n) (a c : Spin n→ℝ) (r e : Fin n→ℝ) (hd : d≠0) (x : Spin n) :
    ((WithLp.toLp 2 (w x) : Euclid n)=phiDiagonal (z x) r (a x)
      (WithLp.toLp 2 (initialU f z a r e x)+WithLp.toLp 2 (y x)-
        (j*c x) • WithLp.toLp 2 (fun i=>Real.tanh (r i)))) ↔
      w x=(literalInitial J j d f z m a c r e).sourceOf 1 (fun _=>y) x := by
  have he : (phiDiagonal (z x) r (a x)
      (WithLp.toLp 2 (initialU f z a r e x)+WithLp.toLp 2 (y x)-
        (j*c x) • WithLp.toLp 2 (fun i=>Real.tanh (r i)))).ofLp=
      (literalInitial J j d f z m a c r e).sourceOf 1 (fun _=>y) x := by
    ext i
    rw [literalInitial_source _ _ _ _ _ _ _ _ _ _ _ hd]
    change phiDiagonal _ _ _ _ i=_
    rw [phiDiagonal_apply]
    change phi (z x i) (r i) (a x)*
      (f.eval (z x i) (r i) (a x)/phi (z x i) (r i) (a x)*e i+y x i-j*c x*Real.tanh (r i))=_
    field_simp [(phi_pos (z x i) (r i) (a x)).ne']
    ring
  constructor
  · intro h; exact (congrArg WithLp.ofLp h).trans he
  · intro h; exact WithLp.ofLp_injective 2 (h.trans he.symm)

lemma literalEquations_recipe (J : Interaction n) (j d : ℝ) (f : KernelExpr)
    (z m w y : VectorFields n) (a c : Spin n→ℝ) (r e : Fin n→ℝ) (hd : d≠0) (x : Spin n) :
    LiteralEquations J j f z m w y a c r e x ↔
      w x=(literalInitial J j d f z m a c r e).sourceOf 1 (fun _=>y) x ∧
      y x=(literalInitial J j d f z m a c r e).fieldOf 1 (fun _=>w) (fun _=>y) x ∧
      c x=siteMean ((literalInitial J j d f z m a c r e).implicitPartial y) x := by
  have hc (hw : w x=(literalInitial J j d f z m a c r e).sourceOf 1 (fun _=>y) x) :
      c x=(n:ℝ)⁻¹*inner ℝ (WithLp.toLp 2 (fun i=>logSlope (z x i) (r i) (a x)) : Euclid n)
          (WithLp.toLp 2 (w x))+siteMean (initialP f z a r e) x ↔
        c x=siteMean ((literalInitial J j d f z m a c r e).implicitPartial y) x := by
    rw [initial_scalar_equation]
    change c x=(∑i,(logSlope (z x i) (r i) (a x)*w x i+initialP f z a r e x i))/(n:ℝ) ↔ _
    rw [siteMean,literalInitial_partial_source _ _ _ _ _ _ _ _ _ _ _ _ hd x hw]
  have hy (hw : w x=(literalInitial J j d f z m a c r e).sourceOf 1 (fun _=>y) x)
      (hc : c x=siteMean ((literalInitial J j d f z m a c r e).implicitPartial y) x) :
      (WithLp.toLp 2 (y x) : Euclid n)=toEuclideanCLM (𝕜:=ℝ) J (WithLp.toLp 2 (w x))-
        (j*siteMean (fun v i=>phi (z v i) (r i) (a v)) x) • WithLp.toLp 2 (w x)-
        (j*c x) • WithLp.toLp 2 (m x) ↔
      y x=(literalInitial J j d f z m a c r e).fieldOf 1 (fun _=>w) (fun _=>y) x := by
    rw [literalInitial_field _ _ _ _ _ _ _ _ _ _ _ _ x hw hc]
    constructor
    · intro h; exact congrArg WithLp.ofLp h
    · intro h; exact WithLp.ofLp_injective 2 h
  constructor
  · intro h
    have hw:=(literal_first_equation J j d f z m w y a c r e hd x).mp h.1
    have hs:=(hc hw).mp h.2.2
    exact ⟨hw,(hy hw hs).mp h.2.1,hs⟩
  · rintro ⟨hw,hy',hc'⟩
    exact ⟨(literal_first_equation J j d f z m w y a c r e hd x).mpr hw,
      (hy hw hc').mpr hy',(hc hw).mpr hc'⟩
end SKGapCutoff.Recipe

end
end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Stability_ImplicitUniformControl
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped BigOperators Matrix.Norms.Frobenius
namespace SKGapCutoff.Recipe
open Primary SKGap.ImplicitSystem
variable {n : ℕ}

lemma halfDiff_column (U : VectorFields n) (x : Spin n) (k : Fin n) :
    ((spin x k/2) • ((WithLp.toLp 2 (U x) : Euclid n)-WithLp.toLp 2 (U (flip x k))))=
      WithLp.toLp 2 (fun i=>derivativeMatrix U x i k) := by
  ext i
  change (spin x k/2)*(U x i-U (flip x k) i)=halfDiff k (fun y=>U y i) x
  rw [halfDiff_as_flip]; ring

end SKGapCutoff.Recipe

end
end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Stability_LiteralStableControl
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped BigOperators Matrix.Norms.Frobenius
namespace SKGapCutoff.Recipe
open SKGap.Stein Primary SKGap.ImplicitSystem Matrix
variable {n : ℕ}

lemma LiteralStableAt.perturbation {J : Interaction n} {j : ℝ}
    {z m : VectorFields n} {a : Spin n→ℝ} {r : Fin n→ℝ}
    {R ρ δ : ℝ} {x : Spin n} (H : LiteralStableAt J j z m a r R ρ δ x)
    (hn : 0<n) (hδ : 0<δ) (hρ : 0≤ρ)
    (hsmall : ρ≤δ/(2*(|j| *Real.exp (R/2)*(3*Real.exp (R/2)+16)+1))) :
    |j| *|siteMean (fun v i=>phi (z v i) (r i) (a v)) x-
      (∑i,scalarVariance (z x i))/(n:ℝ)| *‖phiSqrt (z x) r (a x)‖^2+
      |j*(n:ℝ)⁻¹| *‖phiSqrt (z x) r (a x)‖^2*
      (‖(WithLp.toLp 2 (m x) : Euclid n)+WithLp.toLp 2 (fun i=>Real.tanh (r i))-
        (2:ℝ) • WithLp.toLp 2 (fun i=>Real.tanh (z x i))‖*
          ‖(WithLp.toLp 2 (fun i=>logSlope (z x i) (r i) (a x)) : Euclid n)‖+
       2*‖(WithLp.toLp 2 (fun i=>Real.tanh (z x i)) : Euclid n)‖*
        ‖(WithLp.toLp 2 (fun i=>logSlope (z x i) (r i) (a x)) : Euclid n)+
          WithLp.toLp 2 (fun i=>Real.tanh (z x i))‖)≤δ/2 :=
  (implicit_normalized_perturbation (z x) r (m x) (a x) j (phiSqrt (z x) r (a x))
    hn hρ H.a_bound H.a_small H.z_near H.m_near (phiSqrt_bound _ _ _ H.a_bound)).trans
      (implicit_rho_threshold j R δ ρ hδ hsmall)

end SKGapCutoff.Recipe

end
end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Matrix_LiteralTrace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped BigOperators
namespace SKGap.ImplicitSystem
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
lemma ordinary_matrix_margin (j χ b r δ : ℝ) (X J : E→L[ℝ]E) (q : E)
    (hj : 0≤j) (hr : 0 ≤ r)
    (hself : ∀u v,inner ℝ u (X v)=inner ℝ (X u) v)
    (hStable : ∀v,δ*‖v‖^2≤ inner ℝ v (stableMatrix j b r X J q v))
    (hSmall : |j| *|χ-b| *‖X‖^2≤δ/2) (v : E) :
    (δ/2)*‖v‖^2≤ inner ℝ v ((1-X*(J-(j*χ) • 1)*X) v) := by
  let S:=1+(j*b) • (X*X)-X*J*X
  have hS : ∀u,δ*‖u‖^2≤ inner ℝ u (S u) := by
    intro u
    have hh : inner ℝ u ((X*rank q q*X) u)=(inner ℝ q (X u))^2 := by
      simp only [mul_apply_eq_comp,rank_apply,map_smul,inner_smul_right]
      rw [hself u q,real_inner_comm (X u) q]
      ring
    have hs:=hStable u
    change δ*‖u‖^2≤ inner ℝ u ((S-(2*j*r) • (X*rank q q*X)) u) at hs
    simp only [sub_apply,smul_apply,inner_sub_right,
      inner_smul_right,hh] at hs
    nlinarith [mul_nonneg (by positivity : 0≤2*j*r) (sq_nonneg (inner ℝ q (X u)))]
  have hd : (1-X*(J-(j*χ) • 1)*X)-S=(j*(χ-b)) • (X*X) := by
    dsimp only [S]
    simp only [mul_sub,sub_mul,mul_smul_comm,smul_mul_assoc,mul_one,sub_smul]
    module
  have hnorm : ‖(1-X*(J-(j*χ) • 1)*X)-S‖≤δ/2 := by
    rw [hd,norm_smul,Real.norm_eq_abs,abs_mul]
    exact ((mul_le_mul_of_nonneg_left (norm_mul_le X X) (by positivity)).trans_eq
      (by ring)).trans hSmall
  have hp:=SKGap.ImplicitLinear.quadratic_perturbation (1-X*(J-(j*χ) • 1)*X) S hS hnorm v
  convert hp using 1
  all_goals try with_reducible_and_instances rfl
  ring
end SKGap.ImplicitSystem

namespace SKGapCutoff.Recipe
open SKGap.Stein Primary SKGap.ImplicitSystem Matrix
variable {n : ℕ}
lemma phiSqrt_inner (z r : Fin n→ℝ) (a : ℝ) (u v : Euclid n) :
    inner ℝ u (phiSqrt z r a v)=inner ℝ (phiSqrt z r a u) v := by
  simp only [phiSqrt,EuclideanSpace.inner_eq_star_dotProduct,
    star_trivial,ofLp_toEuclideanCLM,dotProduct,mulVec_diagonal]
  apply Finset.sum_congr rfl
  intro i _
  ring

end SKGapCutoff.Recipe

end
end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Localization_LiteralMargin
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped BigOperators
namespace SKGapCutoff.Recipe
open SKGap.Stein Primary SKGap.ImplicitSystem Matrix
variable {n : ℕ}

lemma realQuadratic_eq_inner (M : Interaction n) (v : Euclid n) :
    SKGap.RealComplex.realQuadratic M v=inner ℝ v (toEuclideanCLM (𝕜:=ℝ) M v) := by
  rw [inner_toEuclideanCLM]
  simp only [SKGap.RealComplex.realQuadratic,dotProduct,mulVec,Finset.mul_sum,mul_assoc]

lemma literal_inverse_margin (J : Interaction n) (j : ℝ)
    (z m : VectorFields n) (a : Spin n→ℝ) (r : Fin n→ℝ) (x : Spin n)
    (hn : 0<n) (hj : 0≤j) {R ρ δ : ℝ} (hδ : 0<δ) (hρ : 0≤ρ)
    (hsmall : ρ≤δ/(2*(|j| *Real.exp (R/2)*(3*Real.exp (R/2)+16)+1)))
    (H : LiteralStableAt J j z m a r R ρ δ x) :
    δ/2≤SKGap.ComplexSpectral.lowerRayleigh (SKGap.RealComplex.liftMatrix
      (SKGap.stabilityMatrix (fun i=>phi (z x i) (r i) (a x)) 1
        ((j/n)*∑i,phi (z x i) (r i) (a x)) J)) := by
  have : Nonempty (Fin n):=Fin.pos_iff_nonempty.mp hn
  let D:=SKGap.pathDiagonal (fun i=>phi (z x i) (r i) (a x)) 1
  let χ:=siteMean (fun v i=>phi (z v i) (r i) (a v)) x
  have hq : (j/n)*∑i,phi (z x i) (r i) (a x)=j*χ := by dsimp [χ,siteMean];ring
  have hshift : SKGap.pathShift 1 (j*χ)=(j*χ) • (1:Interaction n) := by
    simp only [SKGap.pathShift,one_mul,Matrix.smul_one_eq_diagonal]
  rw [SKGap.stabilityMatrix_path_rep _ (fun i=>(phi_pos _ _ _).le) (by norm_num),hq,hshift]
  apply SKGap.RealComplex.lowerRayleigh_lift_ge
  intro v
  rw [realQuadratic_eq_inner]
  have hpert:=H.perturbation hn hδ hρ hsmall
  have hsmall' : |j| *|χ-(∑i,scalarVariance (z x i))/(n:ℝ)| *‖phiSqrt (z x) r (a x)‖^2≤δ/2 :=
    (le_add_of_nonneg_right (by positivity)).trans hpert
  have hp:=ordinary_matrix_margin j χ _ (n:ℝ)⁻¹ δ (phiSqrt (z x) r (a x))
    (toEuclideanCLM (𝕜:=ℝ) J) (WithLp.toLp 2 (fun i=>Real.tanh (z x i)))
    hj (by positivity) (phiSqrt_inner _ _ _) H.stable hsmall' v
  have hrep : toEuclideanCLM (𝕜:=ℝ) (1-D*(J-(j*χ) • 1)*D)=
      1-phiSqrt (z x) r (a x)*(toEuclideanCLM (𝕜:=ℝ) J-(j*χ) • 1)*phiSqrt (z x) r (a x) := by
    simp only [map_sub,map_mul,map_one,map_smul,D,SKGap.pathDiagonal,Real.sqrt_one,one_mul,phiSqrt]
  simpa only [←hrep] using hp

lemma literal_closed_word_event (J : Interaction n) (j : ℝ)
    (z m : VectorFields n) (a : Spin n→ℝ) (r : Fin n→ℝ) (x : Spin n)
    (hn : 0<n) (hj : 0≤j) {R ρ δ A L B W C : ℝ} {M Nmax : ℕ}
    (hδ : 0<δ) (hρ : 0≤ρ)
    (hsmall : ρ≤δ/(2*(|j| *Real.exp (R/2)*(3*Real.exp (R/2)+16)+1)))
    (H : LiteralStableAt J j z m a r R ρ δ x)
    (hEvent : StartedMatrixEvent j L (Real.exp (R/2)) A (δ/2) B W C M Nmax J) :
    ClosedWordTestBound j (fun i=>phi (z x i) (r i) (a x)) J A W (2*Nmax+5) ∧
    ClosedWordDiagramBound j (fun i=>phi (z x i) (r i) (a x)) J A C (2*M+2*Nmax+4) := by
  apply hEvent.2.2 _
  · intro i
    refine ⟨(phi_pos _ _ _).le,?_⟩
    exact (phi_le_exp ..).trans (Real.exp_le_exp.mpr (by linarith [H.a_bound]))
  · exact literal_inverse_margin J j z m a r x hn hj hδ hρ hsmall H
end SKGapCutoff.Recipe

end
end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Localization_PhiHessianBridge
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped BigOperators Matrix
namespace SKGapCutoff.Recipe
open SKGap.Stein Primary SKGap.ImplicitSystem Matrix
variable {n : ℕ}

lemma rank_toEuclideanCLM (m : Fin n→ℝ) :
    toEuclideanCLM (𝕜:=ℝ) (vecMulVec m m)=rank (WithLp.toLp 2 m) (WithLp.toLp 2 m) := by
  ext v i
  change ((vecMulVec m m).mulVec v.ofLp) i=(inner ℝ (WithLp.toLp 2 m) v)*m i
  simp only [mulVec, dotProduct, vecMulVec]
  change (∑k,m i*m k*v k)=(∑k,v k*m k)*m i
  rw [Finset.sum_mul]
  congr 1
  ext k
  ring

lemma fieldHessian_matrix (j : ℝ) (J : Interaction n) (z A : Fin n→ℝ) :
    SKGap.fieldHessian j J z A=
      1+(SKGap.onsager j z) • ((diagonal (fun i=>Real.sqrt (A i)))*(diagonal (fun i=>Real.sqrt (A i))))-
        diagonal (fun i=>Real.sqrt (A i))*J*diagonal (fun i=>Real.sqrt (A i))-
        (2*j/(n:ℝ)) • (diagonal (fun i=>Real.sqrt (A i))*
          vecMulVec (SKGap.magnetization z) (SKGap.magnetization z)*diagonal (fun i=>Real.sqrt (A i))) := by
  ext i k
  simp only [SKGap.fieldHessian,SKGap.hessianCore,Matrix.add_apply,Matrix.sub_apply,
    Matrix.smul_apply,smul_eq_mul,Matrix.one_apply,Matrix.diagonal_mul,Matrix.mul_diagonal,
    Matrix.diagonal_apply,vecMulVec,Matrix.of_apply]
  by_cases h:i=k
  · subst k; simp only [ite_true];ring
  · simp only [h,ite_false];ring

lemma onsager_scalarVariance (hn : 0<n) (j : ℝ) (z : Fin n→ℝ) :
    SKGap.onsager j z=j*((∑i,scalarVariance (z i))/(n:ℝ)) := by
  have hn0 : (n:ℝ)≠0:=ne_of_gt (Nat.cast_pos.mpr hn)
  simp only [SKGap.onsager,SKGap.overlap,SKGap.magnetization,scalarVariance]
  rw [Finset.sum_sub_distrib]
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,mul_one]
  field_simp

lemma literal_stableMatrix_eq_hessian (hn : 0<n) (j : ℝ) (J : Interaction n)
    (z r : Fin n→ℝ) (a : ℝ) :
    stableMatrix j ((∑i,scalarVariance (z i))/(n:ℝ)) (n:ℝ)⁻¹
      (phiSqrt z r a) (toEuclideanCLM (𝕜:=ℝ) J)
      (WithLp.toLp 2 (fun i=>Real.tanh (z i)))=
      toEuclideanCLM (𝕜:=ℝ) (SKGap.fieldHessian j J z (fun i=>phi (z i) (r i) a)) := by
  rw [fieldHessian_matrix]
  simp only [map_sub,map_add,map_one,map_smul,map_mul,rank_toEuclideanCLM]
  rw [onsager_scalarVariance hn]
  simp only [stableMatrix,phiSqrt,div_eq_mul_inv]
  rfl

lemma literal_stableMatrix_quadratic (hn : 0<n) (j : ℝ) (J : Interaction n)
    (z r : Fin n→ℝ) (a : ℝ) (v : Euclid n) :
    inner ℝ v (stableMatrix j ((∑i,scalarVariance (z i))/(n:ℝ)) (n:ℝ)⁻¹
      (phiSqrt z r a) (toEuclideanCLM (𝕜:=ℝ) J)
      (WithLp.toLp 2 (fun i=>Real.tanh (z i))) v)=
      SKGap.quadraticForm (SKGap.fieldHessian j J z (fun i=>phi (z i) (r i) a)) v.ofLp := by
  rw [literal_stableMatrix_eq_hessian hn,Matrix.inner_toEuclideanCLM]
  simp only [dotProduct,mulVec,SKGap.quadraticForm,Finset.mul_sum]
  congr 1
  ext i
  congr 1
  ext k
  ring

end SKGapCutoff.Recipe

end
end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Stability_StableRootInverse
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
namespace SKGap.ObservationBridge
open Matrix Real Set MeasureTheory ProbabilityTheory Filter
open scoped BigOperators ENNReal NNReal Topology

lemma stable_hessian_coercive {n : ℕ} {j A ε c ρ : ℝ}
    {J : Matrix (Fin n) (Fin n) ℝ} {h y a : Field n}
    (hbad : ¬rootBad j A ε c ρ J h)
    (hy : vectorNorm (tapField j J h y) ≤ ρ*sqrt (n:ℝ))
    (ha : ∀ i,a i∈Icc 0 A) (hd : (∑ i,(a i-spinVariance y i)^2)≤ε^2*(n:ℝ)) :
    ∀ v : Field n,c*vectorSqNorm v ≤ quadraticForm (fieldHessian j J y a) v := by
  intro v
  let x : EuclideanSpace ℝ (Fin n) := WithLp.toLp 2 v
  let H := fieldHessian j J y a
  have hunit : ∀ z : EuclideanSpace ℝ (Fin n),‖z‖=1 → c < matrixQuad H z := by
    intro z hz
    exact lt_of_not_ge (fun hh=>hbad ⟨y,hy,a,ha,hd,z,hz,hh⟩)
  by_cases hx : x=0
  · have hv : v=0 := congrArg WithLp.ofLp hx
    simp [hv,vectorSqNorm,quadraticForm]
  · have hx0 : 0<‖x‖ := norm_pos_iff.mpr hx
    have hu : ‖(‖x‖⁻¹:ℝ) • x‖=1 := by
      rw [norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr hx0),inv_mul_cancel₀ hx0.ne']
    have hh := (hunit (‖x‖⁻¹ • x) hu).le
    rw [matrixQuad_smul] at hh
    have hmul := mul_le_mul_of_nonneg_left hh (sq_nonneg ‖x‖)
    have he : ‖x‖^2*((‖x‖⁻¹)^2*matrixQuad H x)=matrixQuad H x := by
      field_simp
    rw [he] at hmul
    have hn : ‖x‖^2=vectorSqNorm v := vectorNorm_sq v
    rw [hn,mul_comm] at hmul
    exact hmul

end SKGap.ObservationBridge

end
end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Stability_LiteralStableEvent
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped BigOperators Matrix
namespace SKGapCutoff.Recipe
open SKGap SKGap.Stein Primary SKGap.ImplicitSystem Matrix SKGap.ObservationBridge
variable {n : ℕ}

lemma phi_hessian_stable (hn : 0<n) {j A ε c r₀ R ρ : ℝ}
    (hρ : 0≤ρ) (_ : 0≤ε) (hAR : Real.exp (R/2)≤A)
    (hsmall : (3*Real.exp (R/2)+2)*ρ≤ε)
    (J : Interaction n) (h z r : Fin n→ℝ) (a : ℝ)
    (hbad : ¬rootBad j A ε c r₀ J h)
    (htap : vectorNorm (SKGap.tapField j J h z) ≤ r₀*Real.sqrt (n:ℝ))
    (ha : |a|≤R) (haρ : |a|≤ρ)
    (hz : vectorNorm (z-r)≤ρ*Real.sqrt (n:ℝ)) :
    ∀v : Euclid n,c*‖v‖^2≤ inner ℝ v
      (stableMatrix j ((∑i,scalarVariance (z i))/(n:ℝ)) (n:ℝ)⁻¹
        (phiSqrt z r a) (toEuclideanCLM (𝕜:=ℝ) J)
        (WithLp.toLp 2 (fun i=>Real.tanh (z i))) v) := by
  obtain ⟨hb,hvar,hrest⟩:=implicit_coefficient_bounds z r a hn hρ ha haρ hz
  have hdiag : (∑i,(phi (z i) (r i) a-SKGap.spinVariance z i)^2)≤ε^2*(n:ℝ) := by
    have hv : vectorNorm (fun i=>phi (z i) (r i) a-SKGap.spinVariance z i)≤ε*Real.sqrt (n:ℝ) := by
      apply (show vectorNorm (fun i=>phi (z i) (r i) a-SKGap.spinVariance z i)≤
          (3*Real.exp (R/2)+2)*ρ*Real.sqrt (n:ℝ) by
        change SKGapCutoff.Recipe.vectorNorm ((fun i=>phi (z i) (r i) a)-(fun i=>scalarVariance (z i))) ≤ _ at hvar
        exact hvar).trans
      exact mul_le_mul_of_nonneg_right hsmall (Real.sqrt_nonneg _)
    have hs:=pow_le_pow_left₀ (vectorNorm_nonneg _) hv 2
    simpa only [vectorNorm_sq,mul_pow,Real.sq_sqrt (Nat.cast_nonneg n)] using hs
  have H:=stable_hessian_coercive hbad htap
    (fun i=>⟨(hb i).1.le,(hb i).2.trans hAR⟩) hdiag
  intro v
  rw [literal_stableMatrix_quadratic hn]
  have hvnorm : SKGap.vectorSqNorm v.ofLp=‖v‖^2 := by
    simpa only [SKGap.vectorNorm,WithLp.toLp_ofLp] using (SKGap.vectorNorm_sq v.ofLp).symm
  simpa only [hvnorm] using H v.ofLp

lemma literalStableAt_of_stableField (hn : 0<n) {j A ε c r₀ R ρ : ℝ}
    (hρ : 0≤ρ) (hε : 0≤ε) (hAR : Real.exp (R/2)≤A)
    (hsmall : (3*Real.exp (R/2)+2)*ρ≤ε)
    (J : Interaction n) (h r : Fin n→ℝ) (z m : VectorFields n) (a : Spin n→ℝ)
    (x : Spin n) (hbad : ¬rootBad j A ε c r₀ J h)
    (htap : vectorNorm (SKGap.tapField j J h (z x)) ≤ r₀*Real.sqrt (n:ℝ))
    (ha : |a x|≤R) (haρ : |a x|≤ρ)
    (hz : vectorNorm (z x-r)≤ρ*Real.sqrt (n:ℝ))
    (hm : vectorNorm (m x-(fun i=>Real.tanh (r i)))≤ρ*Real.sqrt (n:ℝ))
    (hmb : ∀i,|m x i|≤1) :
    LiteralStableAt J j z m a r R ρ c x :=
  ⟨ha,haρ,hz,hm,hmb,phi_hessian_stable hn hρ hε hAR hsmall J h (z x) r (a x)
    hbad htap ha haρ hz⟩

end SKGapCutoff.Recipe

end
end

section

noncomputable section
open scoped BigOperators Matrix
namespace SKGapCutoff.Recipe
open SKGap Primary Static SKGap.ObservationBridge SKGap.Stein
variable {n : ℕ}

lemma square_average_difference (hn : 0<n) (v t : Fin n→ℝ)
    (hv : vectorNorm v≤Real.sqrt (n:ℝ)) (ht : vectorNorm t≤Real.sqrt (n:ℝ)) :
    |(∑i,(v i)^2)/(n:ℝ)-(∑i,(t i)^2)/(n:ℝ)| *Real.sqrt (n:ℝ)≤
      2*vectorNorm (v-t) := by
  have hnR : (0:ℝ)<n:=Nat.cast_pos.mpr hn
  have hd : (∑i,(v i)^2)-(∑i,(t i)^2)=∑i,(v i-t i)*(v i+t i) := by
    rw [←Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl;intros;ring
  have hp:=(SKGap.vector_dot_abs_le (v-t) (v+t)).trans
    (mul_le_mul_of_nonneg_left ((SKGap.vectorNorm_add_le v t).trans
      ((add_le_add hv ht).trans_eq (show Real.sqrt (n:ℝ)+Real.sqrt (n:ℝ)=2*Real.sqrt (n:ℝ) by ring))) (vectorNorm_nonneg _))
  rw [←sub_div,hd,abs_div,abs_of_pos hnR,div_mul_eq_mul_div]
  apply (div_le_iff₀ hnR).mpr
  have H:=mul_le_mul_of_nonneg_right hp (Real.sqrt_nonneg (n:ℝ))
  have he : (SKGap.vectorNorm (v-t)*(2*Real.sqrt (n:ℝ)))*Real.sqrt (n:ℝ)=2*SKGap.vectorNorm (v-t)*(n:ℝ) := by
    calc
      _ = 2*SKGap.vectorNorm (v-t)*(Real.sqrt (n:ℝ))^2 := by ring
      _ = _ := by rw [Real.sq_sqrt hnR.le]
  simpa only [Pi.add_apply,Pi.sub_apply,SKGap.vectorNorm,vectorNorm] using H.trans_eq he

lemma primary_auxiliary_small (hn : 0<n) {j D ρ : ℝ} (hj : 0≤j)
    (J : Interaction n) (h r : Fin n→ℝ) (k : ℕ) (x : Spin n)
    (hnear : vectorNorm (mag j J h k x-SKGap.magnetization r)≤D*ρ*Real.sqrt (n:ℝ)) :
    |j*(1-onsager j J h k x-SKGap.overlap r)|≤2*j*D*ρ := by
  have hs : 0<Real.sqrt (n:ℝ):=Real.sqrt_pos.mpr (Nat.cast_pos.mpr hn)
  have hv : vectorNorm (SKGap.magnetization r)≤Real.sqrt (n:ℝ) := by
    exact magnetization_norm r
  have havg : 1-onsager j J h k x-SKGap.overlap r=
      (∑i,(mag j J h k x i)^2)/(n:ℝ)-(∑i,(SKGap.magnetization r i)^2)/(n:ℝ) := by
    have hn0 : (n:ℝ)≠0:=ne_of_gt (Nat.cast_pos.mpr hn)
    simp only [Primary.onsager,siteMean,SKGap.overlap,Finset.sum_sub_distrib,
      Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,mul_one,
      sub_div,div_self hn0]
    ring
  have H:=(square_average_difference hn (mag j J h k x) (SKGap.magnetization r)
    (mag_vectorNorm j J h k x) hv).trans (mul_le_mul_of_nonneg_left hnear (by norm_num))
  rw [abs_mul,abs_of_nonneg hj,havg]
  apply (mul_le_mul_iff_left₀ hs).mp
  calc
    _ = j*(|((∑i,(mag j J h k x i)^2)/(n:ℝ))-(∑i,(SKGap.magnetization r i)^2)/(n:ℝ)| *Real.sqrt (n:ℝ)) := by ring
    _ ≤ j*(2*(D*ρ*Real.sqrt (n:ℝ))) := mul_le_mul_of_nonneg_left H hj
    _ = _ := by ring

theorem stable_primary_buffer (hn : 0<n) {j K A ε c r₀ R ρ : ℝ}
    (hj : 0≤j) (hK : 0≤K) (hA : 1≤A) (hc : 0 < c) (hr₀ : 0 < r₀) (hρ : 0≤ρ)
    (hε : 0≤ε) (hAR : Real.exp (R/2)≤A)
    (hbuffer : (K+4*j)*ρ < r₀)
    (hR : (1+2*j)*(1+(1+(K+3*j)/c)*(K+4*j))*ρ≤R)
    (hsmall : (3*Real.exp (R/2)+2)*((1+2*j)*(1+(1+(K+3*j)/c)*(K+4*j))*ρ)≤ε)
    (J : Interaction n) (hJ : J.IsSymm) (h : Fin n→ℝ)
    (hop : ∀v,vectorNorm (J.mulVec v)≤K*vectorNorm v)
    (hbad : ¬rootBad j A ε c r₀ J h) :
    ∃r:Fin n→ℝ,SKGap.tapField j J h r=0 ∧ (∀y,SKGap.tapField j J h y=0→y=r) ∧
      ∀k x,
      vectorNorm (Primary.residual j J h k x)≤ρ*Real.sqrt (n:ℝ)→
      vectorNorm (Primary.residual j J h (k+1) x)≤ρ*Real.sqrt (n:ℝ)→
      LiteralStableAt J j (fld j J h (k+1)) (mag j J h (k+1))
        (fun v=>j*(1-onsager j J h (k+1) v-SKGap.overlap r)) r R
        ((1+2*j)*(1+(1+(K+3*j)/c)*(K+4*j))*ρ) c x := by
  let C:=(1+(K+3*j)/c)*(K+4*j)
  let D:=(1+2*j)*(1+C)
  have hC : 0≤C:=by dsimp [C];positivity
  have hD : 0≤D:=by dsimp [D];positivity
  have hCD : C≤D:=by dsimp [D];nlinarith
  have h1CD : 1+C≤D:=by dsimp [D];nlinarith
  have h2CD : 2*j*(1+C)≤D:=by dsimp [D];nlinarith
  have hs : 0<Real.sqrt (n:ℝ):=Real.sqrt_pos.mpr (Nat.cast_pos.mpr hn)
  have hH : ∀y,vectorNorm (SKGap.tapField j J h y) ≤ r₀*Real.sqrt (n:ℝ)→∀v,
      c*SKGap.vectorSqNorm v≤SKGap.quadraticForm (SKGap.fieldHessian j J y (SKGap.spinVariance y)) v := by
    intro y hy
    apply stable_hessian_coercive hbad hy
    · intro i
      exact ⟨(SKGap.spinVariance_pos y i).le,(SKGap.spinVariance_le_one y i).trans hA⟩
    · simp only [sub_self,zero_pow (by decide : 2≠0),Finset.sum_const_zero]
      positivity
  obtain ⟨r,hr,hu,hd⟩:=SKGap.tap_root_and_distance hn hj hK hc (mul_pos hr₀ hs) hJ h hop hH
  refine ⟨r,hr,hu,?_⟩
  intro k x h0 h1
  have htap : vectorNorm (SKGap.tapField j J h (fld j J h (k+1) x))≤(K+4*j)*ρ*Real.sqrt (n:ℝ) :=
    (primary_tap_norm hn hj hK J h k x hop).trans
      ((add_le_add (mul_le_mul_of_nonneg_left h0 hj)
        (mul_le_mul_of_nonneg_left h1 (by positivity))).trans_eq (by ring))
  have htap' := htap.trans_lt (mul_lt_mul_of_pos_right hbuffer hs)
  have hz : vectorNorm (fld j J h (k+1) x-r)≤C*ρ*Real.sqrt (n:ℝ) :=
    (hd _ htap').trans ((mul_le_mul_of_nonneg_left htap (by positivity)).trans_eq (by dsimp [C];ring))
  have ht : vectorNorm (mag j J h (k+2) x-SKGap.magnetization r)≤C*ρ*Real.sqrt (n:ℝ) :=
    (magnetization_vector_lipschitz (fld j J h (k+1) x) r).trans hz
  have hm : vectorNorm (mag j J h (k+1) x-SKGap.magnetization r)≤(1+C)*ρ*Real.sqrt (n:ℝ) := by
    have he : mag j J h (k+1) x-SKGap.magnetization r=
        Primary.residual j J h (k+1) x+(mag j J h (k+2) x-SKGap.magnetization r) := by
      ext i;simp only [Primary.residual,Pi.sub_apply,Pi.add_apply];ring
    rw [he]
    exact (SKGap.vectorNorm_add_le _ _).trans ((add_le_add h1 ht).trans_eq (by ring))
  have ha := (primary_auxiliary_small hn hj J h r (k+1) x hm).trans
    (mul_le_mul_of_nonneg_right h2CD hρ)
  apply literalStableAt_of_stableField hn (mul_nonneg hD hρ) hε hAR hsmall J h r _ _ _ x hbad
    htap'.le (ha.trans hR) ha
  · exact hz.trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hCD hρ) hs.le)
  · exact hm.trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right h1CD hρ) hs.le)
  · intro i
    exact primaryState_mag_bounded j J h (k+1) x i

end SKGapCutoff.Recipe

end
end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Localization_BufferedFlip
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped BigOperators Matrix
namespace SKGapCutoff.Recipe
open SKGap Primary Static SKGap.ObservationBridge SKGap.Stein
variable {n : ℕ}

lemma vector_column_opNorm (M : Interaction n) (k : Fin n) :
    vectorNorm (fun i=>M i k)≤SKGap.opNorm M := by
  apply nonneg_le_nonneg_of_sq_le_sq (norm_nonneg _)
  simp only [←pow_two]
  rw [vectorNorm_sq]
  exact SKGap.SourceError.matrix_column_square_le M k

lemma vector_flip_opNorm (F : VectorFields n) (x : Spin n) (k : Fin n) :
    vectorNorm (F (flip x k)-F x)≤2*SKGap.opNorm (derivativeMatrix F x) := by
  have H:=congrArg norm (halfDiff_column F x k)
  rw [norm_smul,Real.norm_eq_abs,abs_div,abs_spin_eq_one,abs_of_pos (by norm_num : (0:ℝ)<2),norm_sub_rev] at H
  have hcol:=vector_column_opNorm (derivativeMatrix F x) k
  change (1/2:ℝ)*vectorNorm (F (flip x k)-F x)=vectorNorm (fun i=>derivativeMatrix F x i k) at H
  linarith

end SKGapCutoff.Recipe

end
end

section

noncomputable section
open scoped BigOperators Matrix.Norms.Frobenius
namespace SKGapCutoff.Recipe
open Primary SKGap.Stein
variable {n : ℕ}

lemma auxiliary_derivative (j q : ℝ) (b : Spin n→ℝ) (x : Spin n) :
    derivativeVector (fun y=>j*(1-b y-q)) x= -j • derivativeVector b x := by
  ext i
  simp only [derivativeVector,WithLp.ofLp_toLp,PiLp.smul_apply,halfDiff]
  ring

lemma primary_literal_derivative_diagnostics (hn : 0<n) {j K B : ℝ}
    (hK : 0≤K) (hB : 0≤B) (J : Interaction n) (h : Fin n→ℝ)
    (hop : SKGap.opNorm J≤K) (k : ℕ)
    (hformal : ∀x l,l<k+3→ShapeBound (formalField j J h x l) B)
    (r : Fin n→ℝ) (x : Spin n) :
    let C:=localPrimaryBudget j K B (k+3)
    let T:=(1+|j|)*C
    let a:=fun v=>j*(1-Primary.onsager j J h (k+1) v-SKGap.overlap r)
    SKGap.opNorm (derivativeMatrix (fld j J h (k+1)) x)+‖derivativeVector a x‖≤T ∧
    SKGap.opNorm (derivativeMatrix (mag j J h (k+1)) x)≤T ∧
    ‖derivativeMatrix (fld j J h (k+1)) x-(primaryTree j J h x (k+1)).fieldMatrix j J‖≤C ∧
    ‖derivativeMatrix (mag j J h (k+1)) x-(primaryTree j J h x (k+1)).sourceMatrix j J‖≤C ∧
    (∑i,∑v,(derivativeMatrix (fld j J h (k+1)) x i v)^4)≤(2*C)^4 ∧
    (∑i,(derivativeMatrix (fld j J h (k+1)) x i i)^2)≤T^2 := by
  dsimp only
  let C:=localPrimaryBudget j K B (k+3)
  have hC : 0≤C:=localPrimaryBudget_nonneg hK hB _
  have hT : C≤(1+|j|)*C := by nlinarith [abs_nonneg j]
  have hh:=primary_differentiation J h x hn hK hB hop (k+1)
    (fun l hl=>hformal x l (by omega))
  have hb:=(localPrimaryBudget_bounds (j:=j) hK hB (k+3) ⟨k+1,by omega⟩).1
  have hz : ShapeBound (derivativeMatrix (fld j J h (k+1)) x) C := hh.2.2.2.mono hb
  have ha := onsager_derivative_bound (j:=j) J h x hn hK hB hop (k+3)
    (hformal x) (show k+1≤k+3 by omega)
  refine ⟨?_,(hh.2.2.1.trans hb).trans hT,?_,?_,?_,?_⟩
  · rw [auxiliary_derivative,norm_smul,Real.norm_eq_abs,abs_neg]
    exact (add_le_add hz.1 (mul_le_mul_of_nonneg_left ha (abs_nonneg j))).trans_eq (by dsimp [C];ring)
  · rw [(primaryTree_matrices j J h x (k+1)).2]
    exact hh.1.trans hb
  · rw [(primaryTree_matrices j J h x (k+1)).1]
    exact hh.2.1.trans hb
  · exact (fourth_sum_le hC hz).trans (by nlinarith [pow_nonneg hC 4])
  · have H:=pow_le_pow_left₀ (norm_nonneg _) (hz.2.1.trans hT) 2
    change (SKGap.diagonalSeminorm (derivativeMatrix (fld j J h (k+1)) x))^2≤((1+|j|)*C)^2 at H
    simpa only [SKGap.diagonalSeminorm_sq] using H

end SKGapCutoff.Recipe

end
end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Localization_BufferedSelectionDiagnostics
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped BigOperators Matrix.Norms.Frobenius
namespace SKGapCutoff.Recipe
open SKGap.Stein Primary Static
variable {n : ℕ}

lemma vector_flip_additive (F : VectorFields n) (x : Spin n) (k : Fin n) {B : ℝ}
    (hD : SKGap.opNorm (derivativeMatrix F x)≤B) :
    vectorNorm (F (flip x k))≤vectorNorm (F x)+2*B := by
  have H : vectorNorm (F (flip x k))≤vectorNorm (F x)+vectorNorm (F (flip x k)-F x) := by
    calc
      _ = vectorNorm (F x+(F (flip x k)-F x)) := by congr 1;ext i;simp
      _ ≤ _ := SKGap.vectorNorm_add_le _ _
  have H' := (vector_flip_opNorm F x k).trans
    (mul_le_mul_of_nonneg_left hD (by norm_num : (0:ℝ)≤2))
  linarith

lemma vector_neighborhood_twice_buffer (F : VectorFields n) (E : Set (Spin n))
    {B ρ : ℝ} (hB : 0≤B) (hD : ∀x,SKGap.opNorm (derivativeMatrix F x)≤B)
    (hsmall : 4*B≤ρ*Real.sqrt (n:ℝ))
    (hF : ∀x∈E,vectorNorm (F x)≤ρ*Real.sqrt (n:ℝ)) (x : Spin n)
    (hx : x∈flipNeighborhood E) :
    vectorNorm (F x)≤(2*ρ)*Real.sqrt (n:ℝ) ∧
      ∀k,vectorNorm (F (flip x k))≤(2*ρ)*Real.sqrt (n:ℝ) := by
  have hbase : vectorNorm (F x)≤ρ*Real.sqrt (n:ℝ)+2*B := by
    rcases hx with hx|⟨k,hk⟩
    · exact (hF x hx).trans (le_add_of_nonneg_right (by positivity))
    · have H:=vector_flip_additive F (flip x k) k (hD (flip x k))
      simp only [flip_flip] at H
      have H' := hF _ hk
      linarith
  refine ⟨by linarith,?_⟩
  intro k
  have H:=vector_flip_additive F x k (hD x)
  linarith

end SKGapCutoff.Recipe

end
end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Localization_StartedResidualStep
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped BigOperators
namespace SKGapCutoff.Static
variable {n : ℕ}

lemma halfDiff_zero_off_neighborhood (E : Set (Spin n)) (G : Observables n)
    (hG : ∀x,x∉E→G x=0) (x : Spin n) (i : Fin n) (hx : x∉E) (hi : flip x i∉E) :
    halfDiff i G x=0 := by
  simp [halfDiff_as_flip,hG x hx,hG (flip x i) hi]

lemma local_multiplier_energy (P : Spin n→ℝ) (hP : ∀x,0≤P x)
    (E : Set (Spin n)) (θ G : Observables n) {B L : ℝ}
    (hG : ∀x,x∉E→G x=0) (hθ : ∀x∈flipNeighborhood E,|θ x|≤B)
    (hd : ∀x∈E,∑i,(halfDiff i θ x)^2≤L^2) :
    varianceEnergy P (fun x=>θ x*G x)≤
      2*B^2*varianceEnergy P G+2*L^2*(∑x,P x*(G x)^2) := by
  have ht (x : Spin n) (i : Fin n) :
      (θ (flip x i))^2*(halfDiff i G x)^2≤B^2*(halfDiff i G x)^2 := by
    by_cases hx:x∈E
    · have hf : flip x i∈flipNeighborhood E:=Or.inr ⟨i,by simpa⟩
      exact mul_le_mul_of_nonneg_right (by
        simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg _) (hθ _ hf) 2) (sq_nonneg _)
    · by_cases hi:flip x i∈E
      · exact mul_le_mul_of_nonneg_right (by
          simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg _) (hθ _ (Or.inl hi)) 2) (sq_nonneg _)
      · simp [halfDiff_zero_off_neighborhood E G hG x i hx hi]
  calc
    _ ≤ ∑x,P x*∑i,conditionalVariance P x i*
        (2*B^2*(halfDiff i G x)^2+2*(G x)^2*(halfDiff i θ x)^2) := by
      apply Finset.sum_le_sum; intro x _
      apply mul_le_mul_of_nonneg_left _ (hP x)
      apply Finset.sum_le_sum; intro i _
      apply mul_le_mul_of_nonneg_left _ (conditionalVariance_nonneg P hP x i)
      rw [halfDiff_mul_flipped]
      nlinarith only [ht x i,sq_nonneg (θ (flip x i)*halfDiff i G x-G x*halfDiff i θ x)]
    _ ≤ ∑x,P x*(2*B^2*(∑i,conditionalVariance P x i*(halfDiff i G x)^2)+2*(G x)^2*L^2) := by
      apply Finset.sum_le_sum; intro x _
      apply mul_le_mul_of_nonneg_left _ (hP x)
      simp only [mul_add,Finset.sum_add_distrib]
      have h1 : (∑i,conditionalVariance P x i*(2*B^2*(halfDiff i G x)^2))=
          2*B^2*(∑i,conditionalVariance P x i*(halfDiff i G x)^2) := by
        simp only [Finset.mul_sum]; apply Finset.sum_congr rfl; intro i _; ring
      rw [h1]
      apply add_le_add_right
      calc
        _ ≤ ∑i,2*(G x)^2*(halfDiff i θ x)^2 := by
          apply Finset.sum_le_sum; intro i _
          exact mul_le_of_le_one_left (by positivity) (conditionalVariance_le_one P x i)
        _ = 2*(G x)^2*(∑i,(halfDiff i θ x)^2) := by rw [Finset.mul_sum]
        _ ≤ _ := by
          by_cases hx:x∈E
          · exact mul_le_mul_of_nonneg_left (hd x hx) (by positivity)
          · simp [hG x hx]
    _ = _ := by
      simp only [mul_add,Finset.sum_add_distrib,varianceEnergy,Finset.mul_sum]
      congr 1 <;> apply Finset.sum_congr rfl <;> intro x _ <;> ring_nf

lemma local_multiplier_starSquared (P : Spin n→ℝ) (hP : ∀x,0≤P x)
    (E : Set (Spin n)) (θ G : Observables n) {B L : ℝ}
    (hG : ∀x,x∉E→G x=0) (hθ : ∀x∈flipNeighborhood E,|θ x|≤B)
    (hd : ∀x∈E,∑i,(halfDiff i θ x)^2≤L^2) :
    starSquared P (fun x=>θ x*G x)≤(3*B^2+2*L^2)*starSquared P G := by
  have hs : (∑x,P x*(θ x*G x)^2)≤B^2*(∑x,P x*(G x)^2) := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum; intro x _
    by_cases hx:x∈E
    · have ht : (θ x)^2≤B^2 := by
        simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg _) (hθ x (Or.inl hx)) 2
      have hm := mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_right ht (sq_nonneg (G x))) (hP x)
      nlinarith only [hm]
    · simp [hG x hx]
  have he:=local_multiplier_energy P hP E θ G hG hθ hd
  have hn:=varianceEnergy_nonneg P hP G
  have hn' : 0≤∑x,P x*(G x)^2 := Finset.sum_nonneg fun x _=>mul_nonneg (hP x) (sq_nonneg _)
  dsimp only [starSquared]
  nlinarith [mul_nonneg (sq_nonneg B) hn,mul_nonneg (sq_nonneg L) hn,
    mul_nonneg (sq_nonneg B) hn']

lemma local_star_multiplier (P : Spin n→ℝ) (hP : ∀x,0≤P x)
    (E : Set (Spin n)) (θ G : Observables n) {B L : ℝ}
    (hG : ∀x,x∉E→G x=0) (hθ : ∀x∈flipNeighborhood E,|θ x|≤B)
    (hd : ∀x∈E,∑i,(halfDiff i θ x)^2≤L^2) :
    starNorm P (fun x=>θ x*G x)≤Real.sqrt (3*B^2+2*L^2)*starNorm P G := by
  exact (Real.sqrt_le_sqrt (local_multiplier_starSquared P hP E θ G hG hθ hd)).trans_eq
    (Real.sqrt_mul (by positivity) _)

end SKGapCutoff.Static

end
end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Localization_LocalUniformWeak
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped BigOperators
namespace SKGapCutoff.Static
open Primary Recipe
universe u
variable {Ω : Type u} {n : Ω→ℕ}

variable {E : ∀a,Set (Spin (n a))}

lemma LocalUniformWeak.add {P F H : ∀a,Observables (n a)} (hF : LocalUniformWeak E P F)
    (hH : LocalUniformWeak E P H) : LocalUniformWeak E P (fun a x=>F a x+H a x) := by
  obtain ⟨C,hC,hF⟩:=hF
  obtain ⟨D,hD,hH⟩:=hH
  refine ⟨C+D,add_nonneg hC hD,fun a G hG=>?_⟩
  simp only [mul_add,Finset.sum_add_distrib]
  exact (abs_add_le _ _).trans ((add_le_add (hF a G hG) (hH a G hG)).trans_eq (by ring))

lemma LocalUniformWeak.neg {P F : ∀a,Observables (n a)} (hF : LocalUniformWeak E P F) :
    LocalUniformWeak E P (fun a x=>-F a x) := by
  obtain ⟨C,hC,hF⟩:=hF
  refine ⟨C,hC,fun a G hG=>?_⟩
  simpa using hF a G hG

lemma LocalUniformWeak.sub {P F H : ∀a,Observables (n a)} (hF : LocalUniformWeak E P F)
    (hH : LocalUniformWeak E P H) : LocalUniformWeak E P (fun a x=>F a x-H a x) := by
  simpa only [sub_eq_add_neg] using hF.add hH.neg

lemma LocalUniformWeak.mul {P F θ : ∀a,Observables (n a)} (hP : ∀a x,0≤P a x)
    (hF : LocalUniformWeak E P F) (hθ : LocalUniformMultiplier E θ) :
    LocalUniformWeak E P (fun a x=>θ a x*F a x) := by
  obtain ⟨C,hC,hF⟩:=hF
  obtain ⟨B,L,hB,hL,hθ,hd⟩:=hθ
  refine ⟨C*Real.sqrt (3*B^2+2*L^2),by positivity,fun a G hG=>?_⟩
  have hf:=hF a (fun x=>θ a x*G x) (by intro x hx; simp [hG x hx])
  have hm:=mul_le_mul_of_nonneg_left (local_star_multiplier (P a) (hP a) (E a) (θ a) G hG (hθ a) (hd a)) hC
  calc
    _ = |∑x,P a x*(θ a x*G x)*F a x| := by
      congr 1; apply Finset.sum_congr rfl; intro x _; ring
    _ ≤ C*(Real.sqrt (3*B^2+2*L^2)*starNorm (P a) G) := hf.trans hm
    _ = _ := by ring

lemma LocalUniformMultiplier.const (E : ∀a,Set (Spin (n a))) (c : ℝ) : LocalUniformMultiplier (n:=n) E (fun _ _=>c) := by
  refine ⟨|c|,0,abs_nonneg _,le_rfl,fun _ _ _=>le_rfl,?_⟩
  intro a x hx
  simp [halfDiff]

lemma LocalUniformWeak.smul {P F : ∀a,Observables (n a)} (hP : ∀a x,0≤P a x)
    (hF : LocalUniformWeak E P F) (c : ℝ) : LocalUniformWeak E P (fun a x=>c*F a x) :=
  hF.mul hP (LocalUniformMultiplier.const E c)

end SKGapCutoff.Static

end
end

section

noncomputable section
open scoped BigOperators
namespace SKGapCutoff.Static
open Primary Recipe
universe u
variable {Ω : Type u} {n : Ω→ℕ} {E : ∀a,Set (Spin (n a))}

lemma LocalUniformWeak.congr_on {P F F' : ∀a,Observables (n a)} (h : LocalUniformWeak E P F)
    (he : ∀a x,x∈E a→F a x=F' a x) : LocalUniformWeak E P F' := by
  obtain ⟨C,hC,hh⟩:=h
  refine ⟨C,hC,fun a G hG=>?_⟩
  convert hh a G hG using 2
  all_goals try with_reducible_and_instances rfl
  apply Finset.sum_congr rfl
  intro x _
  by_cases hx:x∈E a
  · rw [he a x hx]
  · simp [hG x hx]

end SKGapCutoff.Static

end
end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Stability_StableLiteralWeak
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped BigOperators Matrix.Norms.Frobenius
namespace SKGapCutoff.Recipe
open SKGap.Stein Primary Static
universe u

lemma LiteralInitialDiagnostics.monoCoefficient {n : ℕ}
    {D : OrdinaryData n Unit Bool Bool} {w y : VectorFields n}
    {t : SKGap.Noncrossing.Primary.SourceTree (Fin n→ℝ)} {x : Spin n} {V S F A A' : ℝ}
    (H : LiteralInitialDiagnostics D w y t x V S F A) (hA : A≤A') :
    LiteralInitialDiagnostics D w y t x V S F A' :=
  {H with coefficient_bound:=fun i=>(H.coefficient_bound i).trans hA}

lemma literalResidualBudget_exp (j : ℝ) (f : KernelExpr) (R B : ℝ) (p : ℕ) :
    Real.exp (R/2)≤literalResidualBudget j f R B p := by
  have h0:=le_abs_self (literalCoefficientBudget f j R B)
  have hF : 0≤f.mass*Real.exp (R/2):=mul_nonneg f.mass_nonneg (Real.exp_pos _).le
  have hJ : 0≤|j| *|B| *Real.exp (R/2):=by positivity
  have hh : Real.exp (R/2)≤literalCoefficientBudget f j R B := by
    simp only [literalCoefficientBudget,phiExpr,KernelExpr.mass]
    nlinarith [abs_nonneg (initialRegularBudget f j R B)]
  exact (show Real.exp (R/2)≤2+|literalCoefficientBudget f j R B| by linarith).trans
    (residualCoefficientBudget_ge j (by positivity) p 0)

end SKGapCutoff.Recipe

end
end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Terminal_TerminalIdentity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped BigOperators
namespace SKGapCutoff.Primary
open Matrix
variable {n : ℕ}

lemma terminal_field_identity (j : ℝ) (J : Interaction n) (h : Fin n→ℝ)
    (k : ℕ) (x : Spin n) (i : Fin n) :
    fld j J h (k+1) x i-h i-J.mulVec (mag j J h (k+2) x) i+
        j*onsager j J h (k+1) x*mag j J h (k+2) x i =
      J.mulVec (residual j J h (k+1) x) i-
        j*onsager j J h (k+1) x*(residual j J h k x i+residual j J h (k+1) x i) := by
  rw [fld_eq]
  simp only [Nat.add_sub_cancel,residual,Matrix.mulVec,dotProduct,mul_sub,Finset.sum_sub_distrib]
  ring

theorem terminal_residual_identity (hn : 0<n) (j : ℝ) (J : Interaction n)
    (hJ : J.IsSymm) (h : Fin n→ℝ) (k : ℕ) (x : Spin n)
    (w y : Fin n→ℝ) (χ c : ℝ)
    (hy : ∀i,y i=J.mulVec w i-j*χ*w i-j*c*mag j J h (k+1) x i) :
    (∑i,(fld j J h (k+1) x i-h i-J.mulVec (mag j J h (k+2) x) i+
        j*onsager j J h (k+1) x*mag j J h (k+2) x i)*w i)-
        j*(onsager j J h (k+2) x-onsager j J h (k+1) x)*(n:ℝ)*c =
      (∑i,residual j J h (k+1) x i*y i)+
      j*(χ-onsager j J h (k+1) x)*(∑i,residual j J h (k+1) x i*w i)-
      j*onsager j J h (k+1) x*(∑i,residual j J h k x i*w i)-
      j*c*(∑i,residual j J h (k+1) x i*mag j J h (k+2) x i) := by
  have hsym:=mulVec_pair_symmetric J hJ (residual j J h (k+1) x) w
  have hinner:=residual_inner_product hn j J h (k+1) x
  have hfield : (∑i,residual j J h (k+1) x i*J.mulVec w i)=
      (∑i,residual j J h (k+1) x i*y i)+
      j*χ*(∑i,residual j J h (k+1) x i*w i)+
      j*c*(∑i,residual j J h (k+1) x i*mag j J h (k+1) x i) := by
    simp only [hy,Finset.mul_sum,←Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    ring
  have ht : (∑i,(fld j J h (k+1) x i-h i-J.mulVec (mag j J h (k+2) x) i+
        j*onsager j J h (k+1) x*mag j J h (k+2) x i)*w i)=
      (∑i,residual j J h (k+1) x i*J.mulVec w i)-
      j*onsager j J h (k+1) x*(∑i,residual j J h k x i*w i)-
      j*onsager j J h (k+1) x*(∑i,residual j J h (k+1) x i*w i) := by
    simp_rw [terminal_field_identity]
    simp only [sub_mul,mul_add,add_mul,Finset.sum_sub_distrib,Finset.sum_add_distrib]
    rw [show (∑i,J.mulVec (residual j J h (k+1) x) i*w i)=
      ∑i,residual j J h (k+1) x i*J.mulVec w i from hsym]
    simp only [Finset.mul_sum]
    ring_nf
  rw [ht,hfield,hinner]
  ring

end SKGapCutoff.Primary

end
end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Terminal_StableLiteralTerminal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped BigOperators Matrix.Norms.Frobenius
namespace SKGapCutoff.Recipe
open Primary Static SKGap.Stein
universe u
variable {Ω : Type u} {n : Ω→ℕ}

 theorem literal_terminal_weak (j : ℝ) (J : ∀b,Interaction (n b))
    (h r e : ∀b,Fin (n b)→ℝ) (k : ℕ) (f : KernelExpr)
    (a c : ∀b,Observables (n b)) (w y : ∀b,VectorFields (n b))
    (E : ∀b,Set (Spin (n b))) (P : ∀b,Observables (n b))
    (hn : ∀b,0<n b) (hJ : ∀b,(J b).IsSymm) (hP : ∀b x,0≤P b x)
    (heq : ∀b x,x∈E b→LiteralEquations (J b) j f (fld j (J b) (h b) (k+1))
      (mag j (J b) (h b) (k+1)) (w b) (y b) (a b) (c b) (r b) (e b) x)
    (hw : ∀p≤k+1,LocalUniformWeak E P (fun b x=>∑i,residual j (J b) (h b) p x i*w b x i))
    (hy : LocalUniformWeak E P (fun b x=>∑i,residual j (J b) (h b) (k+1) x i*y b x i))
    (hm : LocalUniformWeak E P (fun b x=>∑i,residual j (J b) (h b) (k+1) x i*
      (Real.tanh (fld j (J b) (h b) (k+1) x i)/Real.sqrt (n b:ℝ))))
    (hχ : LocalUniformMultiplier E (fun b=>siteMean (fun x i=>phi (fld j (J b) (h b) (k+1) x i) (r b i) (a b x))))
    (ho : LocalUniformMultiplier E (fun b x=>j*onsager j (J b) (h b) (k+1) x))
    (hc : LocalUniformMultiplier E (fun b x=>Real.sqrt (n b:ℝ)*c b x)) :
    LocalUniformWeak E P (fun b=>literalTerminal j (J b) (h b) k (w b) (c b)) := by
  have hc' := (hm.mul hP hc).smul hP j
  have hh:=(((hy.add (((hw (k+1) le_rfl).mul hP hχ).smul hP j)).sub
    ((hw (k+1) le_rfl).mul hP ho)).sub ((hw k (by omega)).mul hP ho)).sub hc'
  apply hh.congr_on
  intro b x hx
  have he:=(literalEquations_recipe (J b) j (Real.sqrt (n b:ℝ)) f
    (fld j (J b) (h b) (k+1)) (mag j (J b) (h b) (k+1)) (w b) (y b)
    (a b) (c b) (r b) (e b) (Real.sqrt_pos.mpr (Nat.cast_pos.mpr (hn b))).ne' x).mp (heq b x hx)
  have hf:=he.2.1.trans (literalInitial_field (J b) j (Real.sqrt (n b:ℝ)) f
    (fld j (J b) (h b) (k+1)) (mag j (J b) (h b) (k+1)) (w b) (y b)
    (a b) (c b) (r b) (e b) x he.1 he.2.2)
  have ht:=terminal_residual_identity (hn b) j (J b) (hJ b) (h b) k x (w b x) (y b x)
    (siteMean (fun v i=>phi (fld j (J b) (h b) (k+1) v i) (r b i) (a b v)) x) (c b x)
    (fun i=>congrFun hf i)
  change _=literalTerminal j (J b) (h b) k (w b) (c b) x
  unfold literalTerminal
  rw [ht]
  have hnorm : (Real.sqrt (n b:ℝ)*c b x)*
      (∑i,residual j (J b) (h b) (k+1) x i*(Real.tanh (fld j (J b) (h b) (k+1) x i)/Real.sqrt (n b:ℝ)))=
      c b x*(∑i,residual j (J b) (h b) (k+1) x i*mag j (J b) (h b) (k+2) x i) := by
    exact normalized_pair_cancel (hn b) (residual j (J b) (h b) (k+1))
      (fun v i=>Real.tanh (fld j (J b) (h b) (k+1) v i)) (c b) x
  rw [hnorm]
  ring

end SKGapCutoff.Recipe

end
end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Stability_StableLiteralComparison
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped BigOperators Matrix.Norms.Frobenius
namespace SKGapCutoff.Recipe
open SKGap.Stein Primary Static
universe u
theorem stable_literal_comparison_targets {j K B R ρ δ : ℝ}
    (hj : 0≤j) (hK : 0≤K) (hB : 0≤B) (hδ : 0<δ) (hρ : 0≤ρ)
    (hsmall : ρ≤δ/(2*(|j| *Real.exp (R/2)*(3*Real.exp (R/2)+16)+1)))
    (k : ℕ) (f : KernelExpr) :
    ∃A≥1,∀W C : ℝ,0≤W→0≤C→∀(Ω : Type u) (n : Ω→ℕ)
      (J : ∀b,Interaction (n b)) (h r e : ∀b,Fin (n b)→ℝ)
      (E : ∀b,Set (Spin (n b))) (P : ∀b,Observables (n b)),
      (∀b,0<n b)→(∀b,(J b).IsSymm)→(∀b,vectorNorm (e b)≤1)→
      (∀b,StartedMatrixEvent j K (Real.exp (R/2)) A (δ/2) B W C (k+3) (2+2*(k+1)) (J b))→
      (∀b x,x∈flipNeighborhood (flipNeighborhood (E b))→
        LiteralStableAt (J b) j (fld j (J b) (h b) (k+1)) (mag j (J b) (h b) (k+1))
          (fun v=>j*(1-onsager j (J b) (h b) (k+1) v-SKGap.overlap (r b))) (r b) R ρ δ x)→
      (∀b x,0≤P b x)→(∀b,∑x,P b x=1)→
      (∀b x i,conditionalMean (P b) x i=mag j (J b) (h b) 1 x i)→
      ∃w y : ∀b,VectorFields (n b),∃c : ∀b,Observables (n b),
        (∀b x,x∈E b→LiteralEquations (J b) j f (fld j (J b) (h b) (k+1))
          (mag j (J b) (h b) (k+1)) (w b) (y b)
          (fun v=>j*(1-onsager j (J b) (h b) (k+1) v-SKGap.overlap (r b))) (c b) (r b) (e b) x) ∧
        ((∀p≤k+1,LocalUniformWeak E P (fun b x=>∑i,residual j (J b) (h b) p x i*w b x i)) ∧
        LocalUniformWeak E P (fun b x=>∑i,residual j (J b) (h b) (k+1) x i*y b x i) ∧
        LocalUniformWeak E P (fun b x=>∑i,residual j (J b) (h b) (k+1) x i*
          (Real.tanh (fld j (J b) (h b) (k+1) x i)/Real.sqrt (n b:ℝ))) ∧
        LocalUniformMultiplier E (fun b=>siteMean (fun x i=>phi (fld j (J b) (h b) (k+1) x i) (r b i)
          (j*(1-onsager j (J b) (h b) (k+1) x-SKGap.overlap (r b))))) ∧
        LocalUniformMultiplier E (fun b x=>j*onsager j (J b) (h b) (k+1) x) ∧
        LocalUniformMultiplier E (fun b x=>Real.sqrt (n b:ℝ)*c b x)) ∧
        LocalUniformWeak E P (fun b x=>j*c b x*(∑i,residual j (J b) (h b) (k+1) x i*
          (Real.tanh (fld j (J b) (h b) (k+1) x i)-Real.tanh (r b i)))) := by
  let Cp:=localPrimaryBudget j K B (k+3)
  let T:=(1+|j|)*Cp
  have hCp : 0≤Cp:=localPrimaryBudget_nonneg hK hB _
  have hT : 0≤T:=by dsimp [T];positivity
  obtain ⟨V,hV,S,hS,F,hF,Bc,hBc,Vc,hVc,hsol⟩:=
    literal_complete_diagnostics j R ρ δ T K (2*Cp) Cp f hj hδ hρ hT
      (mul_nonneg (by norm_num) hCp) hsmall
  let A:=literalResidualBudget j f R Bc (k+1)
  have hA : 1≤A:=
    (show 1≤2+|literalCoefficientBudget f j R Bc| by linarith [abs_nonneg (literalCoefficientBudget f j R Bc)]).trans
      (residualCoefficientBudget_ge j (by positivity) (k+1) 0)
  refine ⟨A,hA,?_⟩
  intro W C hW hC Ω n J h r e E P hn hJ he hevent hstable hP hp hm
  let a:=fun b v=>j*(1-onsager j (J b) (h b) (k+1) v-SKGap.overlap (r b))
  choose w y c heq hc hDc hdiag using fun b=>hsol (n b) (hn b) (J b)
    (fld j (J b) (h b) (k+1)) (mag j (J b) (h b) (k+1)) (a b) (r b) (e b)
    (hJ b) (hevent b).1 (he b)
  have hs (b) (x : Spin (n b)) (hx : x∈flipNeighborhood (E b)) :=
    hstable b x (Or.inl hx)
  have hsf (b) (x : Spin (n b)) (hx : x∈flipNeighborhood (E b)) (i : Fin (n b)) :=
    hstable b (flip x i) (Or.inr ⟨i,by simpa only [flip_flip] using hx⟩)
  have hb (b) (x : Spin (n b)):=primary_literal_derivative_diagnostics (hn b) hK hB (J b) (h b)
    (hevent b).1 k (fun v q hq=>(hevent b).2.1 (h b) v q hq) (r b) x
  have heqE : ∀b x,x∈E b→LiteralEquations (J b) j f (fld j (J b) (h b) (k+1))
      (mag j (J b) (h b) (k+1)) (w b) (y b) (a b) (c b) (r b) (e b) x := by
    intro b x hx;exact heq b x (hs b x (Or.inl hx))
  refine ⟨w,y,c,heqE,?_⟩
  apply literal_local_weak_comparison_targets j J h ⟨k+1,by omega⟩ f a c r e w y E hn he
    hK hB hBc hT hVc hV hS hF hW hC
    (fun b=>(hevent b).1) (fun b x q hq=>(hevent b).2.1 (h b) x q hq)
  · intro b x hx;exact (hstable b x hx).a_bound
  · intro b x hx;exact hc b x (hstable b x hx)
  · intro b x hx
    have hh:=(hb b x).1
    exact (le_add_of_nonneg_left (show 0≤SKGap.opNorm (derivativeMatrix (fld j (J b) (h b) (k+1)) x) from norm_nonneg _)).trans hh
  · intro b x hx;exact hDc b x (hs b x hx) (hsf b x hx) (hb b x).1 (hb b x).2.1
  · exact heqE
  · intro b x hx
    exact (hdiag b x (primaryTree j (J b) (h b) x (k+1)) (hs b x hx) (hsf b x hx)
      (hb b x).1 (hb b x).2.1 (primaryState_mag_bounded j (J b) (h b) (k+1) x)
      (hb b x).2.2.1 (hb b x).2.2.2.1 (hb b x).2.2.2.2.1 (hb b x).2.2.2.2.2).monoCoefficient
        (literalResidualBudget_exp j f R Bc (k+1))
  · exact hP
  · exact hp
  · exact hm
  · exact hJ
  · intro b x hx
    exact (literal_closed_word_event (J b) j _ _ (a b) (r b) x (hn b) hj hδ hρ hsmall
      (hs b x hx) (hevent b)).1
  · intro b x hx
    exact (literal_closed_word_event (J b) j _ _ (a b) (r b) x (hn b) hj hδ hρ hsmall
      (hs b x hx) (hevent b)).2

end SKGapCutoff.Recipe

end
end

section

noncomputable section
open scoped BigOperators Matrix.Norms.Frobenius
namespace SKGapCutoff.Recipe
open Primary Static SKGap.Stein
universe u
theorem stable_literal_comparison_weak {j K B R ρ δ : ℝ}
    (hj : 0≤j) (hK : 0≤K) (hB : 0≤B) (hδ : 0<δ) (hρ : 0≤ρ)
    (hsmall : ρ≤δ/(2*(|j| *Real.exp (R/2)*(3*Real.exp (R/2)+16)+1)))
    (k : ℕ) (f : KernelExpr) :
    ∃A≥1,∀W C : ℝ,0≤W→0≤C→∀(Ω : Type u) (n : Ω→ℕ)
      (J : ∀b,Interaction (n b)) (h r e : ∀b,Fin (n b)→ℝ)
      (E : ∀b,Set (Spin (n b))) (P : ∀b,Observables (n b)),
      (∀b,0<n b)→(∀b,(J b).IsSymm)→(∀b,vectorNorm (e b)≤1)→
      (∀b,StartedMatrixEvent j K (Real.exp (R/2)) A (δ/2) B W C (k+3) (2+2*(k+1)) (J b))→
      (∀b x,x∈flipNeighborhood (flipNeighborhood (E b))→
        LiteralStableAt (J b) j (fld j (J b) (h b) (k+1)) (mag j (J b) (h b) (k+1))
          (fun v=>j*(1-onsager j (J b) (h b) (k+1) v-SKGap.overlap (r b))) (r b) R ρ δ x)→
      (∀b x,0≤P b x)→(∀b,∑x,P b x=1)→
      (∀b x i,conditionalMean (P b) x i=mag j (J b) (h b) 1 x i)→
      ∃w y : ∀b,VectorFields (n b),∃c : ∀b,Observables (n b),
        (∀b x,x∈E b→LiteralEquations (J b) j f (fld j (J b) (h b) (k+1))
          (mag j (J b) (h b) (k+1)) (w b) (y b)
          (fun v=>j*(1-onsager j (J b) (h b) (k+1) v-SKGap.overlap (r b))) (c b) (r b) (e b) x) ∧
        LocalUniformWeak E P (fun b=>literalTerminal j (J b) (h b) k (w b) (c b)) ∧
        LocalUniformWeak E P (fun b x=>j*c b x*(∑i,residual j (J b) (h b) (k+1) x i*
          (Real.tanh (fld j (J b) (h b) (k+1) x i)-Real.tanh (r b i)))) := by
  obtain ⟨A,hA,hh⟩:=stable_literal_comparison_targets hj hK hB hδ hρ hsmall k f
  refine ⟨A,hA,?_⟩
  intro W C hW hC Ω n J h r e E P hn hJ he hevent hstable hP hp hm
  obtain ⟨w,y,c,heq,⟨hw,hy,hmag,hχ,ho,hc⟩,hrem⟩:=hh W C hW hC Ω n J h r e E P
    hn hJ he hevent hstable hP hp hm
  exact ⟨w,y,c,heq,literal_terminal_weak j J h r e k f
    (fun b v=>j*(1-onsager j (J b) (h b) (k+1) v-SKGap.overlap (r b))) c w y E P hn hJ hP
    heq hw hy hmag hχ ho hc,hrem⟩

end SKGapCutoff.Recipe

end
end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Localization_BufferedComparisonBound
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped BigOperators Matrix.Norms.Frobenius
namespace SKGapCutoff.Recipe
open SKGap.Stein Primary Static
universe u

theorem buffered_root_comparison_weak {j K B Aroot ε c r₀ R ρ : ℝ}
    (hj : 0≤j) (hK : 0≤K) (hB : 0≤B) (hA : 1≤Aroot) (hc : 0 < c)
    (hr₀ : 0 < r₀) (hρ : 0<ρ) (hε : 0≤ε) (hAR : Real.exp (R/2)≤Aroot)
    (hbuffer : (K+4*j)*(2*ρ) < r₀)
    (hR : (1+2*j)*(1+(1+(K+3*j)/c)*(K+4*j))*(2*ρ)≤R)
    (hsmall : (3*Real.exp (R/2)+2)*((1+2*j)*(1+(1+(K+3*j)/c)*(K+4*j))*(2*ρ))≤ε)
    (himplicit : (1+2*j)*(1+(1+(K+3*j)/c)*(K+4*j))*(2*ρ)≤
      c/(2*(|j| *Real.exp (R/2)*(3*Real.exp (R/2)+16)+1)))
    (k : ℕ) (f : KernelExpr) :
    ∃A≥1,∀W C : ℝ,0≤W→0≤C→∀(Ω : Type u) (n : Ω→ℕ)
      (J : ∀b,Interaction (n b)) (h e : ∀b,Fin (n b)→ℝ) (P : ∀b,Observables (n b)),
      (∀b,0<n b)→(∀b,(J b).IsSymm)→(∀b,vectorNorm (e b)≤1)→
      (∀b,StartedMatrixEvent j K (Real.exp (R/2)) A (c/2) B W C (k+3) (2+2*(k+1)) (J b))→
      (∀b,¬SKGap.rootBad j Aroot ε c r₀ (J b) (h b))→
      (∀b,4*(residualDerivativeBudget j K B k+residualDerivativeBudget j K B (k+1))≤ρ*Real.sqrt (n b:ℝ))→
      (∀b x,0≤P b x)→(∀b,∑x,P b x=1)→
      (∀b x i,conditionalMean (P b) x i=mag j (J b) (h b) 1 x i)→
      ∃r : ∀b,Fin (n b)→ℝ,(∀b,SKGap.tapField j (J b) (h b) (r b)=0 ∧
          ∀v,SKGap.tapField j (J b) (h b) v=0→v=r b) ∧
      ∃w y : ∀b,VectorFields (n b),∃c₀ : ∀b,Observables (n b),
        (∀b x,residualCutoff ρ j (J b) (h b) k x≠0→
          LiteralEquations (J b) j f (fld j (J b) (h b) (k+1)) (mag j (J b) (h b) (k+1))
            (w b) (y b) (fun v=>j*(1-onsager j (J b) (h b) (k+1) v-SKGap.overlap (r b)))
            (c₀ b) (r b) (e b) x) ∧
        LocalUniformWeak (fun b=>{x | residualCutoff ρ j (J b) (h b) k x≠0}) P
          (fun b=>literalTerminal j (J b) (h b) k (w b) (c₀ b)) ∧
        LocalUniformWeak (fun b=>{x | residualCutoff ρ j (J b) (h b) k x≠0}) P
          (fun b x=>j*c₀ b x*(∑i,residual j (J b) (h b) (k+1) x i*
            (Real.tanh (fld j (J b) (h b) (k+1) x i)-Real.tanh (r b i)))) := by
  let η:=(1+2*j)*(1+(1+(K+3*j)/c)*(K+4*j))*(2*ρ)
  have hη : 0≤η:=by dsimp [η];positivity
  obtain ⟨A,hA',hh⟩:=stable_literal_comparison_weak hj hK hB hc hη himplicit k f
  refine ⟨A,hA',?_⟩
  intro W C hW hC Ω n J h e P hn hJ he hevent hbad hdim hP hp hm
  have hact (b) (v : Fin (n b)→ℝ) : vectorNorm ((J b).mulVec v)≤K*vectorNorm v :=
    (vectorNorm_matrix_mul _ v).trans (mul_le_mul_of_nonneg_right (hevent b).1 (vectorNorm_nonneg v))
  choose r hr hu hs using fun b=>stable_primary_buffer (hn b) hj hK hA hc hr₀
    (mul_nonneg (by norm_num) hρ.le) hε hAR hbuffer hR hsmall (J b) (hJ b) (h b) (hact b) (hbad b)
  let E:=fun b=>{x | residualCutoff ρ j (J b) (h b) k x≠0}
  have hstable : ∀b x,x∈flipNeighborhood (flipNeighborhood (E b))→
      LiteralStableAt (J b) j (fld j (J b) (h b) (k+1)) (mag j (J b) (h b) (k+1))
        (fun v=>j*(1-onsager j (J b) (h b) (k+1) v-SKGap.overlap (r b))) (r b) R η c x := by
    intro b x hx
    let BB:=residualDerivativeBudget j K B k+residualDerivativeBudget j K B (k+1)
    have hBB : 0≤BB:=add_nonneg (residualDerivativeBudget_nonneg hK hB _)
      (residualDerivativeBudget_nonneg hK hB _)
    have hD₀ (v : Spin (n b)) : SKGap.opNorm (derivativeMatrix (residual j (J b) (h b) k) v)≤BB :=
      (residual_derivative_bound (hn b) hK hB (J b) (h b) (hevent b).1 k
        (fun v l hl=>(hevent b).2.1 (h b) v l (by omega)) v).trans
        (le_add_of_nonneg_right (residualDerivativeBudget_nonneg hK hB _))
    have hD₁ (v : Spin (n b)) : SKGap.opNorm (derivativeMatrix (residual j (J b) (h b) (k+1)) v)≤BB :=
      (residual_derivative_bound (hn b) hK hB (J b) (h b) (hevent b).1 (k+1)
        (fun v l hl=>(hevent b).2.1 (h b) v l (by omega)) v).trans
        (le_add_of_nonneg_left (residualDerivativeBudget_nonneg hK hB _))
    have H0:=vector_neighborhood_twice_buffer (residual j (J b) (h b) k) (E b) hBB hD₀ (hdim b)
      (fun v hv=>(residualCutoff_support (hn b) hρ (J b) (h b) k v hv).1)
    have H1:=vector_neighborhood_twice_buffer (residual j (J b) (h b) (k+1)) (E b) hBB hD₁ (hdim b)
      (fun v hv=>(residualCutoff_support (hn b) hρ (J b) (h b) k v hv).2)
    rcases hx with hx|⟨i,hx⟩
    · exact hs b k x (H0 x hx).1 (H1 x hx).1
    · have h0:=(H0 (flip x i) hx).2 i
      have h1:=(H1 (flip x i) hx).2 i
      simp only [flip_flip] at h0 h1
      exact hs b k x h0 h1
  obtain ⟨w,y,c₀,heq,hw⟩:=hh W C hW hC Ω n J h r e E P hn hJ he hevent hstable hP hp hm
  exact ⟨r,fun b=>⟨hr b,hu b⟩,w,y,c₀,heq,hw⟩

end SKGapCutoff.Recipe

end
end

section

noncomputable section
open scoped BigOperators
namespace SKGapCutoff.Recipe
open Primary Static SKGap.Stein Matrix
variable {n : ℕ}

 theorem literal_comparison_identity (hn : 0<n) (j : ℝ) (J : Interaction n)
    (hJ : J.IsSymm) (h r e : Fin n→ℝ) (k : ℕ) (f : KernelExpr)
    (w y : VectorFields n) (c : Observables n) (x : Spin n)
    (hr : SKGap.tapField j J h r=0)
    (heq : LiteralEquations J j f (fld j J h (k+1)) (mag j J h (k+1)) w y
      (fun v=>j*(1-onsager j J h (k+1) v-SKGap.overlap r)) c r e x) :
    literalTerminal j J h k w c x=
      (∑i,((fld j J h (k+1) x i-r i-
        j*(1-onsager j J h (k+1) x-SKGap.overlap r)*Real.tanh (fld j J h (k+1) x i))*
          f.eval (fld j J h (k+1) x i) (r i) (j*(1-onsager j J h (k+1) x-SKGap.overlap r))*e i-
        j*(1-onsager j J h (k+1) x-SKGap.overlap r)*
          f.dz.eval (fld j J h (k+1) x i) (r i) (j*(1-onsager j J h (k+1) x-SKGap.overlap r))*e i))+
      j*(1-SKGap.overlap r-siteMean (fun v i=>phi (fld j J h (k+1) v i) (r i)
        (j*(1-onsager j J h (k+1) v-SKGap.overlap r))) x)*
        (∑i,(Real.tanh (fld j J h (k+1) x i)-Real.tanh (r i))*w x i)-
      j*c x*(∑i,residual j J h (k+1) x i*(Real.tanh (fld j J h (k+1) x i)-Real.tanh (r i))) := by
  let z:=fld j J h (k+1)
  let m:=mag j J h (k+1)
  let a:=fun v=>j*(1-onsager j J h (k+1) v-SKGap.overlap r)
  have hn0 : (n:ℝ)≠0:=ne_of_gt (Nat.cast_pos.mpr hn)
  have ht := (literalEquations_recipe J j 1 f z m w y a c r e one_ne_zero x).mp heq
  have hw := fun i=>congrFun ht.1 i
  simp only [literalInitial_source J j 1 f z m y a c r e one_ne_zero x] at hw
  have hy := ht.2.1.trans (literalInitial_field J j 1 f z m w y a c r e x ht.1 ht.2.2)
  have hc : (n:ℝ)*c x=∑i,(f.dz.eval (z x i) (r i) (a x)*e i+
      phiZ (z x i) (r i) (a x)*(y x i-j*c x*Real.tanh (r i))) := by
    calc
      _ = (n:ℝ)*siteMean ((literalInitial J j 1 f z m a c r e).implicitPartial y) x := by rw [←ht.2.2]
      _ = _ := ?_
    rw [siteMean,mul_div_cancel₀ _ hn0]
    apply Finset.sum_congr rfl
    intro i _
    exact literalInitial_partial J j 1 f z m y a c r e one_ne_zero x i
  have hroot (i) : r i-h i-J.mulVec (fun q=>Real.tanh (r q)) i+
      j*(1-SKGap.overlap r)*Real.tanh (r i)=0 := by
    have hh:=congrFun hr i
    simp only [SKGap.tapField,SKGap.onsager,SKGap.magnetization,Pi.zero_apply] at hh
    simpa only [mulVec,dotProduct] using (by linear_combination hh :
      r i-h i-(∑q,J i q*Real.tanh (r q))+j*(1-SKGap.overlap r)*Real.tanh (r i)=0)
  have hb : (∑i,(Real.tanh (z x i))^2)=(n:ℝ)*(1-onsager j J h (k+2) x) := by
    simp only [onsager,siteMean,mag_succ,z,Finset.sum_sub_distrib,Finset.sum_const,
      Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,mul_one]
    field_simp
    ring
  have hq : (∑i,(Real.tanh (r i))^2)=(n:ℝ)*SKGap.overlap r := by
    simp only [SKGap.overlap,SKGap.magnetization,mul_div_cancel₀ _ hn0]
  have hh:=implicit_comparison J hJ (z x) r h (m x) (w x) (y x)
    (fun i=>f.eval (z x i) (r i) (a x)*e i)
    (fun i=>f.dz.eval (z x i) (r i) (a x)*e i)
    j (onsager j J h (k+2) x) (onsager j J h (k+1) x) (SKGap.overlap r)
    (siteMean (fun v i=>phi (z v i) (r i) (a v)) x) (c x)
    hroot hb hq hw (fun i=>congrFun hy i) hc
  have hmag : mag j J h (k+2) x=(fun i=>Real.tanh (z x i)):=funext fun i=>mag_succ ..
  simpa only [literalTerminal,Primary.residual,hmag,mag_succ,z,m,a,mul_assoc] using hh

end SKGapCutoff.Recipe

end
end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Localization_LiteralWeak
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped BigOperators
namespace SKGapCutoff.Recipe
open Primary Static SKGap.Stein
universe u
variable {n : ℕ}

variable {Ω : Type u} {N : Ω→ℕ}
theorem literal_source_middle_weak (j : ℝ) (J : ∀b,Interaction (N b))
    (h r e : ∀b,Fin (N b)→ℝ) (k : ℕ) (f : KernelExpr)
    (w y : ∀b,VectorFields (N b)) (c : ∀b,Observables (N b))
    (E : ∀b,Set (Spin (N b))) (P : ∀b,Observables (N b))
    (hn : ∀b,0<N b) (hJ : ∀b,(J b).IsSymm)
    (hroot : ∀b,SKGap.tapField j (J b) (h b) (r b)=0)
    (heq : ∀b x,x∈E b→LiteralEquations (J b) j f (fld j (J b) (h b) (k+1))
      (mag j (J b) (h b) (k+1)) (w b) (y b)
      (fun v=>j*(1-onsager j (J b) (h b) (k+1) v-SKGap.overlap (r b))) (c b) (r b) (e b) x)
    (hT : LocalUniformWeak E P (fun b=>literalTerminal j (J b) (h b) k (w b) (c b)))
    (hR : LocalUniformWeak E P (fun b x=>j*c b x*(∑i,residual j (J b) (h b) (k+1) x i*
      (Real.tanh (fld j (J b) (h b) (k+1) x i)-Real.tanh (r b i))))) :
    LocalUniformWeak E P (fun b x=>literalSourceBracket j (J b) (h b) (r b) (e b) k f x+
      literalMiddle j (J b) (h b) (r b) k (w b) x) := by
  apply (hT.add hR).congr_on
  intro b x hx
  rw [literal_comparison_identity (hn b) j (J b) (hJ b) (h b) (r b) (e b) k f
    (w b) (y b) (c b) x (hroot b) (heq b x hx)]
  dsimp only [literalSourceBracket,literalMiddle]
  ring

end SKGapCutoff.Recipe

end
end

section

noncomputable section
open scoped BigOperators Matrix.Norms.Frobenius
namespace SKGapCutoff.Recipe
open SKGap.Stein Primary Static
universe u

theorem buffered_root_source_weak_oai {j K B Aroot ε c r₀ R ρ : ℝ}
    (hj : 0≤j) (hK : 0≤K) (hB : 0≤B) (hA : 1≤Aroot) (hc : 0 < c)
    (hr₀ : 0 < r₀) (hρ : 0<ρ) (hε : 0≤ε) (hAR : Real.exp (R/2)≤Aroot)
    (hbuffer : (K+4*j)*(2*ρ) < r₀)
    (hR : (1+2*j)*(1+(1+(K+3*j)/c)*(K+4*j))*(2*ρ)≤R)
    (hsmall : (3*Real.exp (R/2)+2)*((1+2*j)*(1+(1+(K+3*j)/c)*(K+4*j))*(2*ρ))≤ε)
    (himplicit : (1+2*j)*(1+(1+(K+3*j)/c)*(K+4*j))*(2*ρ)≤
      c/(2*(|j| *Real.exp (R/2)*(3*Real.exp (R/2)+16)+1)))
    (k : ℕ) (f : KernelExpr) :
    ∃A≥1,∀W C : ℝ,0≤W→0≤C→∀(Ω : Type u) (n : Ω→ℕ)
      (J : ∀b,Interaction (n b)) (h e : ∀b,Fin (n b)→ℝ) (P : ∀b,Observables (n b)),
      (∀b,0<n b)→(∀b,(J b).IsSymm)→(∀b,vectorNorm (e b)≤1)→
      (∀b,StartedMatrixEvent j K (Real.exp (R/2)) A (c/2) B W C (k+3) (2+2*(k+1)) (J b))→
      (∀b,¬SKGap.rootBad j Aroot ε c r₀ (J b) (h b))→
      (∀b,4*(residualDerivativeBudget j K B k+residualDerivativeBudget j K B (k+1))≤ρ*Real.sqrt (n b:ℝ))→
      (∀b x,0≤P b x)→(∀b,∑x,P b x=1)→
      (∀b x i,conditionalMean (P b) x i=mag j (J b) (h b) 1 x i)→
      ∃r : ∀b,Fin (n b)→ℝ,(∀b,SKGap.tapField j (J b) (h b) (r b)=0 ∧
          ∀v,SKGap.tapField j (J b) (h b) v=0→v=r b) ∧
      ∃w y : ∀b,VectorFields (n b),∃c₀ : ∀b,Observables (n b),
        (∀b x,residualCutoff ρ j (J b) (h b) k x≠0→
          LiteralEquations (J b) j f (fld j (J b) (h b) (k+1)) (mag j (J b) (h b) (k+1))
            (w b) (y b) (fun v=>j*(1-onsager j (J b) (h b) (k+1) v-SKGap.overlap (r b)))
            (c₀ b) (r b) (e b) x) ∧
        LocalUniformWeak (fun b=>{x | residualCutoff ρ j (J b) (h b) k x≠0}) P
          (fun b x=>literalSourceBracket j (J b) (h b) (r b) (e b) k f x+
            literalMiddle j (J b) (h b) (r b) k (w b) x) := by
  obtain ⟨A,hA',hh⟩:=buffered_root_comparison_weak hj hK hB hA hc hr₀ hρ hε
    hAR hbuffer hR hsmall himplicit k f
  refine ⟨A,hA',?_⟩
  intro W C hW hC Ω n J h e P hn hJ he hevent hbad hdim hP hp hm
  obtain ⟨r,hr,w,y,c₀,heq,hT,hrem⟩:=hh W C hW hC Ω n J h e P hn hJ he hevent hbad hdim hP hp hm
  exact ⟨r,hr,w,y,c₀,heq,literal_source_middle_weak j J h r e k f w y c₀ _ P hn hJ
    (fun b=>(hr b).1) heq hT hrem⟩

end SKGapCutoff.Recipe

end
end

end OAI
end

theorem solution.{u} : type_of% @OAI.SKGapCutoff.Recipe.buffered_root_source_weak_oai.{u} := @OAI.SKGapCutoff.Recipe.buffered_root_source_weak_oai.{u}
