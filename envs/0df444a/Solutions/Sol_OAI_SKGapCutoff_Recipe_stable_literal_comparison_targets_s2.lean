-- Prove2me | solution 1 for OAI.SKGapCutoff.Recipe.stable_literal_comparison_targets_s2
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T11:17:34.100735+00:00
-- url     : https://prove2.me/submissions/ed96dfea-e9e3-4864-97f2-0472e0ec1956

import Mathlib
import Definitions.Def_OAIQ072A002
import Theorems.Thm_OAI_SKGapCutoff_Recipe_literal_complete_diagnostics
import Theorems.Thm_OAI_SKGapCutoff_Recipe_literal_local_weak_comparison_targets

section
-- module Solutions.OAIQ074_CM.SKGap_Localization_Quadratic
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
-- module Solutions.OAIQ074_CM.SKGap_Localization_RealQuadratic
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

end SKGap

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
-- module Solutions.OAIQ074_CM.SKGap_Gaussian_PhiStein
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
-- module Solutions.OAIQ074_CM.SKGap_Terminal_Spin
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
-- module Solutions.OAIQ074_CM.SKGap_Terminal_GibbsExpectation
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
-- module Solutions.OAIQ074_CM.SKGap_Gaussian_SquaredGaussianFourth
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
-- module Solutions.OAIQ074_CM.SKGap_Localization_ScalarVariance
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
-- module Solutions.OAIQ074_CM.SKGap_Localization_PhiBounds
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
-- module Solutions.OAIQ074_CM.SKGap_Localization_PhiAlgebra
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
-- module Solutions.OAIQ074_CM.SKGap_Localization_PhiFrechet
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
-- module Solutions.OAIQ074_CM.SKGap_Localization_PreparationGrowth
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
-- module Solutions.OAIQ074_CM.SKGap_Matrix_MatrixSeminorm
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
-- module Solutions.OAIQ074_CM.SKGap_Matrix_DiscreteMatrixCalculus
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
-- module Solutions.OAIQ074_CM.SKGap_Localization_Operation
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
-- module Solutions.OAIQ074_CM.SKGap_Matrix_PrimaryMatrix
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
-- module Solutions.OAIQ074_CM.SKGap_Localization_PrimaryDifferentiation
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
-- module Solutions.OAIQ074_CM.SKGap_Localization_ResidualInduction
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
lemma onsager_zero (j : ℝ) (J : Interaction n) (h : Fin n→ℝ) (x : Spin n) :
    onsager j J h 0 x=0 := by simp [onsager,siteMean,mag_zero,spin_sq]

end SKGapCutoff.Primary

end
end

end OAI
end

section
-- module Solutions.OAIQ074_CM.SKGap_Gaussian_SteinRecipeRegularity
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
-- module Solutions.OAIQ074_CM.SKGap_Stability_OrdinaryGraph
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
-- module Solutions.OAIQ074_CM.SKGap_Localization_RecipeGraph
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
-- module Solutions.OAIQ074_CM.SKGap_Localization_PhiCoefficient
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
-- module Solutions.OAIQ074_CM.SKGap_Stability_ImplicitLinear
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
-- module Solutions.OAIQ074_CM.SKGap_Stability_ImplicitCoefficient
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
-- module Solutions.OAIQ074_CM.SKGap_Stability_ImplicitPerturb
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
-- module Solutions.OAIQ074_CM.SKGap_Stability_LiteralStableControl
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
-- module Solutions.OAIQ074_CM.SKGap_Matrix_LiteralTrace
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
-- module Solutions.OAIQ074_CM.SKGap_Localization_LiteralMargin
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
-- module Solutions.OAIQ074_CM.SKGap_Localization_PrimaryLocalInput
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
-- module Solutions.OAIQ074_CM.SKGap_Localization_UniformResidual
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
-- module Solutions.OAIQ074_CM.SKGap_Localization_BufferedFlip
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

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
-- module Solutions.OAIQ074_CM.SKGap_Stability_StableLiteralWeak
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
-- module Solutions.OAIQ074_CM.SKGap_Stability_StableLiteralComparison
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
theorem stable_literal_comparison_targets_s2_oai {j K B R ρ δ : ℝ}
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

end OAI
end

theorem solution.{u} : type_of% @OAI.SKGapCutoff.Recipe.stable_literal_comparison_targets_s2_oai.{u} := @OAI.SKGapCutoff.Recipe.stable_literal_comparison_targets_s2_oai.{u}
