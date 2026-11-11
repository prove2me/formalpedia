-- Prove2me | solution 1 for OAI.HigherDimensionalBallPacking.Rigidity.exact_marked_local_jet_cauchy_bp240
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T01:50:50.745672+00:00
-- url     : https://prove2.me/submissions/190e1377-178c-4bab-8824-981d2d7dfbc3

import Mathlib
import Definitions.Def_BallPacking
import Definitions.Def_OAIQ240Bp021
import Theorems.Thm_OAI_HigherDimensionalBallPacking_Rigidity_HolderCompletion_compatibleFrame_intertwine_bp240
import Theorems.Thm_OAI_HigherDimensionalBallPacking_Rigidity_HolderCompletion_compatibleFrame_inverse_left_bp240
import Theorems.Thm_OAI_HigherDimensionalBallPacking_Rigidity_HolderCompletion_disk_nonlinear_jet_cauchy_bp240
import Theorems.Thm_OAI_HigherDimensionalBallPacking_Rigidity_exact_marked_line_gradient_bound_bp240

section
-- module Solutions.OAIQ240_BP.BallPacking_Holder_BanachSpace
attribute [-instance] _root_.OAI.PackingSufficiencySupport.Comparison.convexMaps_nonempty _root_.OAI.PackingSufficiencySupport.FiniteMoment.Radial.instInhabitedQuadrant _root_.OAI.PackingSufficiencySupport.Hamiltonian.flatProduct_chartedSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace HigherDimensionalBallPacking.Rigidity.HolderCompletion
open scoped BoundedContinuousFunction Topology ContDiff
open Set Filter
section

variable (X E : Type*) [MetricSpace X] [NormedAddCommGroup E] [NormedSpace ℝ E]

lemma graph_closed (α : ℝ) : IsClosed (graph X E α : Set (Ambient X E)) := by
  change IsClosed {u : Ambient X E | ∀ p : Pairs X, _}
  simp only [← Set.iInter_ofPred]
  apply isClosed_iInter
  intro p
  exact isClosed_eq
    ((BoundedContinuousFunction.evalCLM ℝ p).continuous.comp continuous_snd)
    ((((BoundedContinuousFunction.evalCLM ℝ p.val.1).continuous.comp continuous_fst).sub
      ((BoundedContinuousFunction.evalCLM ℝ p.val.2).continuous.comp continuous_fst)).const_smul _)

instance instCompleteSpaceSubtypeAmbientMemSubmoduleRealHolder (α : ℝ) [CompleteSpace E] : CompleteSpace (Holder X E α) :=
  (graph_closed X E α).completeSpace_coe

variable {X E}

variable {α : ℝ}

variable (D : Type*) [NormedAddCommGroup D] [NormedSpace ℝ D]

lemma jetGraph_closed (α : ℝ) : IsClosed (jetGraph (E := E) D α : Set (JetAmbient (E := E) D α)) := by
  apply isSeqClosed_iff_isClosed.mp
  intro u v hu huv x
  have hv0 : Tendsto (fun n => valueCLM α (u n).1) atTop (𝓝 (valueCLM α v.1)) :=
    ((valueCLM α).continuous.comp continuous_fst).tendsto v |>.comp huv
  have hv1 : Tendsto (fun n => valueCLM α (u n).2) atTop (𝓝 (valueCLM α v.2)) :=
    ((valueCLM α).continuous.comp continuous_snd).tendsto v |>.comp huv
  have huni := BoundedContinuousFunction.tendsto_iff_tendstoUniformly.mp hv1
  exact hasFDerivAt_of_tendstoUniformly huni (fun n => hu n)
    (fun y => (BoundedContinuousFunction.evalCLM ℝ y).continuous.tendsto _ |>.comp hv0) x

instance instCompleteSpaceSubtypeJetAmbientMemSubmoduleRealCOneHolder (α : ℝ) [CompleteSpace E] : CompleteSpace (COneHolder (E := E) D α) :=
  (jetGraph_closed (E := E) D α).completeSpace_coe

end

end HigherDimensionalBallPacking.Rigidity.HolderCompletion
end

end OAI
end

section
-- module Solutions.OAIQ240_BP.BallPacking_Rigidity_CompatibleStructures
attribute [-instance] _root_.OAI.PackingSufficiencySupport.Hamiltonian.flatProduct_chartedSpace
attribute [-simp] _root_.OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.compatibleFrameJet_value _root_.OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.compatibleFrame_apply _root_.OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.compatibleInverseJet_value _root_.OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.completedDX_value _root_.OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.completedFrameJet_value _root_.OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.completedInverseJet_value _root_.OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.completedPrincipal_value _root_.OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.completedQ_value _root_.OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.completedStructureJet_value _root_.OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.curveMarkCoefficientHolder_value _root_.OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.curveMarkCoefficient_apply _root_.OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.curveZeroOrderHolder_value _root_.OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.curveZeroOrder_apply _root_.OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.frozenTargetCoefficient_zero _root_.OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.smoothAlongJet_value _root_.OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.smoothMarkedPrincipal_value _root_.OAI.HigherDimensionalBallPacking.Rigidity.capacity_eq_stdDot _root_.OAI.HigherDimensionalBallPacking.Rigidity.geometricHolder_value _root_.OAI.HigherDimensionalBallPacking.Rigidity.lineHomotopy_one _root_.OAI.HigherDimensionalBallPacking.Rigidity.lineHomotopy_zero _root_.OAI.HigherDimensionalBallPacking.Rigidity.normalizedPrimitive_apply _root_.OAI.HigherDimensionalBallPacking.Rigidity.realCurve_zero _root_.OAI.HigherDimensionalBallPacking.Rigidity.stdDot_J_right _root_.OAI.HigherDimensionalBallPacking.Rigidity.stdOmega_apply _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.infinity_end_count _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.sqrt_sq_complex
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped ContDiff Topology
open Set Function Filter
namespace HigherDimensionalBallPacking.Rigidity

theorem stdDot_symm {n : ℕ} (v w : Phase n) : stdDot n v w = stdDot n w v := by
  simp only [stdDot_apply]
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem stdDot_nonneg {n : ℕ} (v : Phase n) : 0 ≤ stdDot n v v := by
  by_cases hv : v = 0
  · subst v
    simp
  · exact (stdDot_pos hv).le

theorem standardForm_skew {n : ℕ} (v w : Phase n) :
    standardForm v w = -standardForm w v := by
  unfold standardForm
  rw [←Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem compatible_metric_symm {n : ℕ} {J : End n} (hJ : Compatible J)
    (v w : Phase n) : standardForm v (J w) = standardForm w (J v) := by
  calc
    standardForm v (J w) = standardForm (J v) (J (J w)) := (hJ.2.1 v (J w)).symm
    _ = -standardForm (J v) w := by rw [hJ.1, standardForm_neg_right]
    _ = standardForm w (J v) := by rw [standardForm_skew, neg_neg]

theorem compatible_of_sq_symmetric_positive {n : ℕ} {J : End n}
    (hJsq : ∀ v, J (J v) = -v)
    (hsym : ∀ v w, standardForm v (J w) = standardForm w (J v))
    (hpos : ∀ v, v ≠ 0 → 0 < standardForm v (J v)) : Compatible J := by
  refine ⟨hJsq, ?_, hpos⟩
  intro v w
  rw [hsym, hJsq, standardForm_neg_right, standardForm_skew, neg_neg]

theorem relativeOperator_selfadjoint {n : ℕ} {J : End n} (hJ : Compatible J)
    (v w : Phase n) :
    stdDot n (relativeOperator J v) w = stdDot n v (relativeOperator J w) := by
  rw [stdDot_symm, stdDot_relativeOperator, stdDot_relativeOperator]
  exact compatible_metric_symm hJ w v

theorem cayleyP_commute {n : ℕ} (J : End n) (a b : ℝ) (v : Phase n) :
    cayleyP J b a (cayleyP J a b v) = cayleyP J a b (cayleyP J b a v) := by
  simp only [cayleyP_apply, map_add, map_smul]
  module

theorem cayleyP_J_identity {n : ℕ} {J : End n} (hJ : Compatible J)
    (a b : ℝ) (v : Phase n) :
    cayleyP J a b (standardJ n (cayleyP J a b v)) =
      cayleyP J b a (standardJ n (cayleyP J b a v)) := by
  simp only [cayleyP_apply, map_add, map_smul, relativeOperator_J_relativeOperator hJ]
  module

theorem cayleyP_stdDot_identity {n : ℕ} {J : End n} (hJ : Compatible J)
    (a b : ℝ) (v w : Phase n) :
    stdDot n (cayleyP J b a v) (cayleyP J a b w) =
      stdDot n (cayleyP J a b v) (cayleyP J b a w) := by
  simp only [cayleyP_apply, map_add, map_smul,
    add_apply, smul_apply, smul_eq_mul]
  rw [relativeOperator_selfadjoint hJ v w]
  ring

theorem cayleyP_stdDot_positive {n : ℕ} {J : End n} (hJ : Compatible J)
    {a b : ℝ} (ha : 0 < a) (hb : 0 ≤ b) {v : Phase n} (hv : v ≠ 0) :
    0 < stdDot n (cayleyP J b a v) (cayleyP J a b v) := by
  have he : stdDot n (cayleyP J b a v) (cayleyP J a b v) =
      a * b * (stdDot n (relativeOperator J v) (relativeOperator J v) + stdDot n v v) +
      (a ^ 2 + b ^ 2) * stdDot n v (relativeOperator J v) := by
    simp only [cayleyP_apply, map_add, map_smul,
      add_apply, smul_apply, smul_eq_mul]
    rw [relativeOperator_selfadjoint hJ v v]
    ring
  rw [he]
  have hfirst : 0 ≤ a * b *
      (stdDot n (relativeOperator J v) (relativeOperator J v) + stdDot n v v) :=
    mul_nonneg (mul_nonneg ha.le hb) (add_nonneg (stdDot_nonneg _) (stdDot_nonneg _))
  have hcoeff : 0 < a ^ 2 + b ^ 2 := by nlinarith [sq_pos_of_pos ha, sq_nonneg b]
  exact add_pos_of_nonneg_of_pos hfirst (mul_pos hcoeff (relativeOperator_positive hJ hv))

theorem denominator_cayleyOperator {n : ℕ} {J : End n} {a b : ℝ}
    (hQ : (cayleyP J b a).IsInvertible) (v : Phase n) :
    cayleyP J b a (cayleyOperator J a b v) = cayleyP J a b v := by
  change cayleyP J b a (cayleyP J a b ((cayleyP J b a).inverse v)) = _
  rw [cayleyP_commute]
  obtain ⟨e,he⟩ := hQ
  simp [←he]

theorem cayleyOperator_selfadjoint {n : ℕ} {J : End n} (hJ : Compatible J)
    {a b : ℝ} (hQ : (cayleyP J b a).IsInvertible) (v w : Phase n) :
    stdDot n (cayleyOperator J a b v) w = stdDot n v (cayleyOperator J a b w) := by
  obtain ⟨e,he⟩ := hQ
  obtain ⟨x,rfl⟩ := e.surjective v
  obtain ⟨y,rfl⟩ := e.surjective w
  change stdDot n (cayleyOperator J a b ((e : End n) x)) ((e : End n) y) =
    stdDot n ((e : End n) x) (cayleyOperator J a b ((e : End n) y))
  rw [he, cayleyOperator_on_denominator ⟨e,he⟩,
    cayleyOperator_on_denominator ⟨e,he⟩]
  exact (cayleyP_stdDot_identity hJ a b x y).symm

theorem cayleyOperator_positive {n : ℕ} {J : End n} (hJ : Compatible J)
    {a b : ℝ} (ha : 0 < a) (hb : 0 ≤ b) {v : Phase n} (hv : v ≠ 0) :
    0 < stdDot n v (cayleyOperator J a b v) := by
  obtain ⟨e,he⟩ := cayleyP_invertible hJ ha hb
  obtain ⟨x,rfl⟩ := e.surjective v
  have hx : x ≠ 0 := by simpa using hv
  change 0 < stdDot n ((e : End n) x) (cayleyOperator J a b ((e : End n) x))
  rw [he, cayleyOperator_on_denominator ⟨e,he⟩]
  exact cayleyP_stdDot_positive hJ ha hb hx

theorem cayleyOperator_J_identity {n : ℕ} {J : End n} (hJ : Compatible J)
    {a b : ℝ} (hQ : (cayleyP J b a).IsInvertible) (v : Phase n) :
    cayleyOperator J a b (standardJ n (cayleyOperator J a b v)) = standardJ n v := by
  obtain ⟨e,he⟩ := hQ
  obtain ⟨x,rfl⟩ := e.surjective v
  apply e.injective
  change (e : End n) (cayleyOperator J a b (standardJ n (cayleyOperator J a b ((e : End n) x)))) =
    (e : End n) (standardJ n ((e : End n) x))
  rw [he, denominator_cayleyOperator ⟨e,he⟩, cayleyOperator_on_denominator ⟨e,he⟩]
  exact cayleyP_J_identity hJ a b x

theorem compatible_interpolateJ {n : ℕ} {J : End n} (hJ : Compatible J)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) : Compatible (interpolateJ J t) := by
  have ha : 0 < 1 + t := by linarith [ht.1]
  have hb : 0 ≤ 1 - t := by linarith [ht.2]
  have hQ := cayleyP_invertible hJ ha hb
  apply compatible_of_sq_symmetric_positive
  · intro v
    change standardJ n (cayleyOperator J (1+t) (1-t)
      (standardJ n (cayleyOperator J (1+t) (1-t) v))) = -v
    rw [cayleyOperator_J_identity hJ hQ, standardJ_sq]
  · intro v w
    change standardForm v (standardJ n (cayleyOperator J (1+t) (1-t) w)) =
      standardForm w (standardJ n (cayleyOperator J (1+t) (1-t) v))
    rw [standardForm_J_right, standardForm_J_right,
      ←cayleyOperator_selfadjoint hJ hQ, stdDot_symm]
  · intro v hv
    change 0 < standardForm v (standardJ n (cayleyOperator J (1+t) (1-t) v))
    rw [standardForm_J_right]
    exact cayleyOperator_positive hJ ha hb hv

end HigherDimensionalBallPacking.Rigidity

end

end OAI
end

section
-- module Solutions.OAIQ240_BP.BallPacking_Rigidity_Adapted
attribute [-instance] _root_.OAI.PackingSufficiencySupport.Hamiltonian.flatProduct_chartedSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace HigherDimensionalBallPacking.Rigidity

section
open scoped ContDiff Topology
open Set Function Filter

theorem lineHomotopy_compatible {n : ℕ} {J : Phase n → End n}
    (hJ : ∀ x, Compatible (J x)) {t : ℝ} (ht : t ∈ Icc (0:ℝ) 1) (x : Phase n) :
    Compatible (lineHomotopy J t x) := compatible_interpolateJ (hJ x) ht


end

open scoped ContDiff Topology
open Set Function Filter MeasureTheory



end HigherDimensionalBallPacking.Rigidity
end

end OAI
end

section
-- module Solutions.OAIQ240_BP.BallPacking_Compactness_GradientBounds
attribute [-instance] _root_.OAI.PackingSufficiencySupport.Comparison.convexMaps_nonempty _root_.OAI.PackingSufficiencySupport.FiniteMoment.Radial.instInhabitedQuadrant _root_.OAI.PackingSufficiencySupport.Hamiltonian.flatProduct_chartedSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace HigherDimensionalBallPacking.Rigidity.HolderCompletion

section
open scoped ContDiff Topology BoundedContinuousFunction
open Set Filter
variable {X E F : Type*} [MetricSpace X] [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

lemma clm_pair_difference (A B : E →L[ℝ] F) (u v : E) :
    ‖A u-B v‖≤‖A‖*‖u-v‖+‖A-B‖*‖v‖ := by
  have he : A u-B v=A (u-v)+(A-B) v := by simp only [map_sub,sub_apply]; abel
  rw [he]
  exact (norm_add_le _ _).trans (add_le_add (A.le_opNorm _) ((A-B).le_opNorm _))


end
open scoped Topology BoundedContinuousFunction
open Set Filter
variable {X E : Type*} [MetricSpace X] [NormedAddCommGroup E] [NormedSpace ℝ E]

omit [MetricSpace X] [NormedSpace ℝ E] in
lemma uniform_cauchy_of_tendstoUniformly {v : ℕ → X → E} {w : X → E}
    (hv : TendstoUniformly v w atTop) :
    ∀ ε : ℝ,0<ε →∃ N : ℕ,∀ i≥N,∀ j≥N,∀ x,‖v i x-v j x‖≤ε := by
  intro ε hε
  have hh := (Metric.tendstoUniformly_iff.mp hv) (ε/2) (half_pos hε)
  obtain ⟨N,hN⟩ := eventually_atTop.mp hh
  refine ⟨N,fun i hi j hj x => ?_⟩
  have h1 := hN i hi x
  have h2 := hN j hj x
  rw [dist_comm,dist_eq_norm] at h1 h2
  have he : v i x-v j x=(v i x-w x)-(v j x-w x) := by abel
  rw [he]
  exact (norm_sub_le _ _).trans (by linarith)



end HigherDimensionalBallPacking.Rigidity.HolderCompletion
end

end OAI
end

section
-- module Solutions.OAIQ240_BP.BallPacking_Compactness_FrozenCR
attribute [-instance] _root_.OAI.PackingSufficiencySupport.Comparison.convexMaps_nonempty _root_.OAI.PackingSufficiencySupport.FiniteMoment.Radial.instInhabitedQuadrant _root_.OAI.PackingSufficiencySupport.Hamiltonian.flatProduct_chartedSpace
attribute [-simp] _root_.OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.completedDX_value _root_.OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.completedFrameJet_value _root_.OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.completedInverseJet_value _root_.OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.completedPrincipal_value _root_.OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.completedQ_value _root_.OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.completedStructureJet_value _root_.OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.curveMarkCoefficientHolder_value _root_.OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.curveMarkCoefficient_apply _root_.OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.curveZeroOrderHolder_value _root_.OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.curveZeroOrder_apply _root_.OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.smoothAlongJet_value _root_.OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.smoothMarkedPrincipal_value _root_.OAI.HigherDimensionalBallPacking.Rigidity.geometricHolder_value _root_.OAI.HigherDimensionalBallPacking.Rigidity.normalizedPrimitive_apply _root_.OAI.HigherDimensionalBallPacking.Rigidity.realCurve_zero _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.infinity_end_count _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.sqrt_sq_complex
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace HigherDimensionalBallPacking.Rigidity.HolderCompletion
open scoped ContDiff Topology BoundedContinuousFunction
open Set Filter
variable {n : ℕ}

local instance fcrInst1_rfb59fc_1 : NormedAddCommGroup (End n) := ContinuousLinearMap.toNormedAddCommGroup
local instance fcrInst2_rfb59fc_1 : NormedSpace ℝ (End n) := ContinuousLinearMap.toNormedSpace
lemma frozenTargetCoefficient_continuous {J : Phase n → End n} (hJ : Continuous J) (x : Phase n) :
    Continuous (frozenTargetCoefficient J x) := by
  exact (continuous_const.clm_comp ((hJ.comp (continuous_const.add (compatibleFrame (J x)).inverse.continuous)).sub continuous_const)).clm_comp continuous_const

lemma frozenTargetCoefficient_difference (J : Phase n → End n) (x v w : Phase n) :
    frozenTargetCoefficient J x v-frozenTargetCoefficient J x w=
      ((compatibleFrame (J x)).comp (J (x+(compatibleFrame (J x)).inverse v)-
        J (x+(compatibleFrame (J x)).inverse w))).comp (compatibleFrame (J x)).inverse := by
  apply ContinuousLinearMap.ext
  intro a
  simp only [frozenTargetCoefficient,ContinuousLinearMap.comp_apply,sub_apply,map_sub]
  abel

lemma frozenTargetCoefficient_lipschitz {J : Phase n → End n} {x : Phase n} {L G : ℝ}
    (hL : 0≤L) (hG : 0≤G)
    (hJ : ∀ v w,‖J v-J w‖≤L*‖v-w‖)
    (hP : ‖compatibleFrame (J x)‖≤G) (hPi : ‖(compatibleFrame (J x)).inverse‖≤G) :
    ∀ v w,‖frozenTargetCoefficient J x v-frozenTargetCoefficient J x w‖≤(G^3*L)*‖v-w‖ := by
  intro v w
  let P := compatibleFrame (J x)
  have hp : ∀ z,‖P.inverse z‖≤G*‖z‖ := fun z =>
    (P.inverse.le_opNorm z).trans (mul_le_mul_of_nonneg_right hPi (norm_nonneg _))
  have hj : ‖J (x+P.inverse v)-J (x+P.inverse w)‖≤L*(G*‖v-w‖) := by
    have hh := hJ (x+P.inverse v) (x+P.inverse w)
    rw [add_sub_add_left_eq_sub,←map_sub] at hh
    exact hh.trans (mul_le_mul_of_nonneg_left (hp _) hL)
  rw [frozenTargetCoefficient_difference]
  have h1 : ‖P.comp (J (x+P.inverse v)-J (x+P.inverse w))‖≤G*(L*(G*‖v-w‖)) :=
    (P.opNorm_comp_le _).trans (mul_le_mul hP hj (norm_nonneg _) hG)
  have hh := (P.comp (J (x+P.inverse v)-J (x+P.inverse w))).opNorm_comp_le P.inverse
  exact hh.trans ((mul_le_mul h1 hPi (norm_nonneg _) (by positivity)).trans_eq (by ring))

lemma frozenCurve_fderiv {J : Phase n → End n} (x : Phase n) {u : ℂ → Phase n}
    {z : ℂ} (hu : DifferentiableAt ℝ u z) :
    fderiv ℝ (frozenCurve J x u) z=(compatibleFrame (J x)).comp (fderiv ℝ u z) := by
  exact ((compatibleFrame (J x)).hasFDerivAt.comp z (hu.hasFDerivAt.sub_const x)).fderiv

lemma frozenCurve_CR {J : Phase n → End n} {x : Phase n} (hx : Compatible (J x))
    {u : ℂ → Phase n} {z : ℂ} (hu : DifferentiableAt ℝ u z)
    (hcr : fderiv ℝ u z Complex.I=J (u z) (fderiv ℝ u z 1)) :
    fderiv ℝ (frozenCurve J x u) z Complex.I-Complex.I • fderiv ℝ (frozenCurve J x u) z 1=
      frozenTargetCoefficient J x (frozenCurve J x u z) (fderiv ℝ (frozenCurve J x u) z 1) := by
  rw [frozenCurve_fderiv x hu]
  simp only [frozenTargetCoefficient,frozenCurve,ContinuousLinearMap.comp_apply]
  rw [compatibleFrame_inverse_left_bp240 hx,compatibleFrame_inverse_left_bp240 hx]
  rw [add_sub_cancel,hcr,sub_apply,map_sub]
  have hh := compatibleFrame_intertwine_bp240 hx (fderiv ℝ u z 1)
  change compatibleFrame (J x) (J (u z) (fderiv ℝ u z 1))-
      standardJ n (compatibleFrame (J x) (fderiv ℝ u z 1))=_
  rw [←hh]

end HigherDimensionalBallPacking.Rigidity.HolderCompletion

namespace HigherDimensionalBallPacking.Rigidity
open scoped ContDiff Topology
open Set Filter
open HolderCompletion
open scoped BoundedContinuousFunction
section
variable {n : ℕ}

attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.hcbInst1
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.hcbInst2
local instance hcbInst3_rfb59fc_1 : NormedAddCommGroup (Phase n →L[ℝ] End n) := ContinuousLinearMap.toNormedAddCommGroup
local instance hcbInst4_rfb59fc_1 : NormedSpace ℝ (Phase n →L[ℝ] End n) := ContinuousLinearMap.toNormedSpace
lemma lineHomotopy_joint_contDiffAt {J : Phase n → End n}
    (hJs : ContDiff ℝ ∞ J) (hJ : ∀ x,Compatible (J x)) {v : ℝ × Phase n}
    (ht : v.1∈Icc (0:ℝ) 1) :
    ContDiffAt ℝ ∞ (fun v : ℝ × Phase n => lineHomotopy J v.1 v.2) v :=
  contDiffAt_interpolateJ (hJs.contDiffAt.comp v contDiffAt_snd) contDiffAt_fst (hJ _) ht

lemma lineHomotopy_partial_deriv {J : Phase n → End n}
    (hJs : ContDiff ℝ ∞ J) (hJ : ∀ x,Compatible (J x)) {t : ℝ} (ht : t∈Icc (0:ℝ) 1) (x : Phase n) :
    fderiv ℝ (lineHomotopy J t) x=
      (fderiv ℝ (fun v : ℝ × Phase n => lineHomotopy J v.1 v.2) (t,x)).comp
        (ContinuousLinearMap.inr ℝ ℝ (Phase n)) := by
  have hj := (lineHomotopy_joint_contDiffAt hJs hJ (v := (t,x)) ht).differentiableAt (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)
  have hg := (hasFDerivAt_const (𝕜 := ℝ) (x := x) t).prodMk (hasFDerivAt_id (𝕜 := ℝ) x)
  exact (hj.hasFDerivAt.comp x hg).fderiv

lemma lineHomotopy_eventually_standard {J : Phase n → End n} {t : ℝ} (ht : t∈Icc (0:ℝ) 1)
    {x : Phase n} (hx : x∉tsupport (fun x => J x-standardJ n)) :
    lineHomotopy J t =ᶠ[𝓝 x] fun _ => standardJ n := by
  have he := notMem_tsupport_iff_eventuallyEq.mp hx
  filter_upwards [he] with y hy
  have hy' : J y=standardJ n := sub_eq_zero.mp hy
  change interpolateJ (J y) t=standardJ n
  rw [hy']
  exact interpolateJ_standard ht

lemma compatibleFrame_contDiffAt {D : Type*} [NormedAddCommGroup D] [NormedSpace ℝ D]
    {A : D → End n} {x : D} (hA : ContDiffAt ℝ ∞ A x) :
    ContDiffAt ℝ ∞ (fun z => compatibleFrame (A z)) x := by
  simpa only [compatibleFrame,cayleyP,one_smul,relativeOperator] using
    ((contDiffAt_const.clm_comp hA).neg.add (contDiffAt_const (c := ContinuousLinearMap.id ℝ (Phase n))))

theorem exact_homotopy_target_bounds {J : Phase n → End n}
    (hJs : ContDiff ℝ ∞ J) (hJ : ∀ x,Compatible (J x))
    (hJc : HasCompactSupport (fun x => J x-standardJ n)) :
    ∃ L G : ℝ,0≤L ∧ 1≤G ∧
      (∀ t∈Icc (0:ℝ) 1,∀ x y,‖lineHomotopy J t x-lineHomotopy J t y‖≤L*‖x-y‖) ∧
      (∀ t∈Icc (0:ℝ) 1,∀ x,‖compatibleFrame (lineHomotopy J t x)‖≤G) ∧
      (∀ t∈Icc (0:ℝ) 1,∀ x,‖(compatibleFrame (lineHomotopy J t x)).inverse‖≤G) := by
  let K := (Icc (0:ℝ) 1) ×ˢ tsupport (fun x => J x-standardJ n)
  have hK : IsCompact K := isCompact_Icc.prod hJc
  let A : ℝ × Phase n → End n := fun v => lineHomotopy J v.1 v.2
  let D : ℝ × Phase n → Phase n →L[ℝ] End n := fun v =>
    (fderiv ℝ A v).comp (ContinuousLinearMap.inr ℝ ℝ (Phase n))
  have hDc : ContinuousOn D K := by
    intro v hv
    exact (((lineHomotopy_joint_contDiffAt hJs hJ hv.1).continuousAt_fderiv (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)).clm_comp continuousAt_const).continuousWithinAt
  have hPc : ContinuousOn (fun v => compatibleFrame (A v)) K := by
    intro v hv
    exact (compatibleFrame_contDiffAt (lineHomotopy_joint_contDiffAt hJs hJ hv.1)).continuousAt.continuousWithinAt
  have hPic : ContinuousOn (fun v => (compatibleFrame (A v)).inverse) K := by
    intro v hv
    have hp := compatibleFrame_contDiffAt (lineHomotopy_joint_contDiffAt hJs hJ hv.1)
    exact ((compatibleFrame_invertible (lineHomotopy_compatible hJ hv.1 v.2)).contDiffAt_map_inverse.comp v hp).continuousAt.continuousWithinAt
  obtain ⟨B,hB⟩ := hK.exists_bound_of_continuousOn hDc
  obtain ⟨P,hP⟩ := hK.exists_bound_of_continuousOn hPc
  obtain ⟨Q,hQ⟩ := hK.exists_bound_of_continuousOn hPic
  let L := max B 0
  let G := |P|+|Q|+‖compatibleFrame (standardJ n)‖+‖(compatibleFrame (standardJ n)).inverse‖+1
  have hL : 0≤L := le_max_right B 0
  have hG : 1≤G := by dsimp [G] <;> linarith [abs_nonneg P,abs_nonneg Q,norm_nonneg (compatibleFrame (standardJ n)),norm_nonneg ((compatibleFrame (standardJ n)).inverse)]
  have hLd : ∀ t∈Icc (0:ℝ) 1,∀ x,‖fderiv ℝ (lineHomotopy J t) x‖≤L := by
    intro t ht x
    by_cases hx : x∈tsupport (fun x => J x-standardJ n)
    · rw [lineHomotopy_partial_deriv hJs hJ ht x]
      exact (hB (t,x) ⟨ht,hx⟩).trans (le_max_left B 0)
    · rw [(lineHomotopy_eventually_standard ht hx).fderiv_eq]
      simpa only [fderiv_fun_const,Pi.zero_apply,norm_zero] using hL
  refine ⟨L,G,hL,hG,?_,?_,?_⟩
  · intro t ht x y
    exact norm_sub_le_of_deriv_bound ((lineHomotopy_slice_contDiff hJs hJ ht).differentiable (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)) (hLd t ht) x y
  · intro t ht x
    by_cases hx : x∈tsupport (fun x => J x-standardJ n)
    · have hh := (hP (t,x) ⟨ht,hx⟩).trans (le_abs_self P)
      exact hh.trans (by dsimp [G] <;> linarith [abs_nonneg P,abs_nonneg Q,norm_nonneg (compatibleFrame (standardJ n)),norm_nonneg ((compatibleFrame (standardJ n)).inverse)])
    · rw [(lineHomotopy_eventually_standard ht hx).eq_of_nhds]
      dsimp [G]
      linarith [abs_nonneg P,abs_nonneg Q,norm_nonneg (compatibleFrame (standardJ n)),norm_nonneg ((compatibleFrame (standardJ n)).inverse)]
  · intro t ht x
    by_cases hx : x∈tsupport (fun x => J x-standardJ n)
    · have hh := (hQ (t,x) ⟨ht,hx⟩).trans (le_abs_self Q)
      exact hh.trans (by dsimp [G] <;> linarith [abs_nonneg P,abs_nonneg Q,norm_nonneg (compatibleFrame (standardJ n)),norm_nonneg ((compatibleFrame (standardJ n)).inverse)])
    · rw [(lineHomotopy_eventually_standard ht hx).eq_of_nhds]
      dsimp [G]
      linarith [abs_nonneg P,abs_nonneg Q,norm_nonneg (compatibleFrame (standardJ n)),norm_nonneg ((compatibleFrame (standardJ n)).inverse)]

end
section

variable {n : ℕ}

attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.fhcInst1
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.fhcInst2
lemma frozenHomotopy_joint_contDiffAt {J : Phase n → End n}
    (hJs : ContDiff ℝ ∞ J) (hJ : ∀ x,Compatible (J x))
    {v : (ℝ × Phase n) × Phase n} (ht : v.1.1∈Icc (0:ℝ) 1) :
    ContDiffAt ℝ ∞ (fun w : (ℝ × Phase n) × Phase n =>
      frozenTargetCoefficient (lineHomotopy J w.1.1) w.1.2 w.2) v := by
  have htfun : ContDiffAt ℝ ∞ (fun w : (ℝ × Phase n) × Phase n => w.1.1) v :=
    contDiffAt_fst.comp v contDiffAt_fst
  have hxfun : ContDiffAt ℝ ∞ (fun w : (ℝ × Phase n) × Phase n => w.1.2) v :=
    contDiffAt_snd.comp v contDiffAt_fst
  let A : (ℝ × Phase n) × Phase n → End n := fun w => lineHomotopy J w.1.1 w.1.2
  have hA : ContDiffAt ℝ ∞ A v :=
    contDiffAt_interpolateJ (hJs.contDiffAt.comp v hxfun) htfun (hJ _) ht
  let P : (ℝ × Phase n) × Phase n → End n := fun w => compatibleFrame (A w)
  have hP : ContDiffAt ℝ ∞ P v := compatibleFrame_contDiffAt hA
  have hi : ContDiffAt ℝ ∞ (fun T : End n => T.inverse) (P v) :=
    (compatibleFrame_invertible (lineHomotopy_compatible hJ ht v.1.2)).contDiffAt_map_inverse
  have hPi : ContDiffAt ℝ ∞ (fun w => (P w).inverse) v := hi.comp v hP
  have harg : ContDiffAt ℝ ∞ (fun w => w.1.2+(P w).inverse w.2) v :=
    hxfun.add (hPi.clm_apply contDiffAt_snd)
  have hB : ContDiffAt ℝ ∞ (fun w => lineHomotopy J w.1.1 (w.1.2+(P w).inverse w.2)) v :=
    contDiffAt_interpolateJ (hJs.contDiffAt.comp v harg) htfun (hJ _) ht
  exact (hP.clm_comp (hB.sub hA)).clm_comp hPi

lemma frozenHomotopy_tendstoUniformlyOn {J : Phase n → End n}
    (hJs : ContDiff ℝ ∞ J) (hJ : ∀ x,Compatible (J x))
    {t : ℕ → ℝ} (ht : ∀ i,t i∈Icc (0:ℝ) 1) {s : ℝ} (hs : Tendsto t atTop (𝓝 s))
    {x : ℕ → Phase n} {y : Phase n} (hx : Tendsto x atTop (𝓝 y))
    {K : Set (Phase n)} (hK : IsCompact K) :
    TendstoUniformlyOn (fun i => frozenTargetCoefficient (lineHomotopy J (t i)) (x i))
      (frozenTargetCoefficient (lineHomotopy J s) y) atTop K := by
  have hsI : s∈Icc (0:ℝ) 1 := isClosed_Icc.mem_of_tendsto hs (Eventually.of_forall ht)
  let U : Set (ℝ × Phase n) := (Icc (0:ℝ) 1) ×ˢ insert y (range x)
  have hU : IsCompact U := isCompact_Icc.prod hx.isCompact_insert_range
  have hc : ContinuousOn (fun w : (ℝ × Phase n) × Phase n =>
      frozenTargetCoefficient (lineHomotopy J w.1.1) w.1.2 w.2) (U ×ˢ K) := by
    intro w hw
    exact (frozenHomotopy_joint_contDiffAt hJs hJ hw.1.1).continuousAt.continuousWithinAt
  have huc := (hU.prod hK).uniformContinuousOn_of_continuous hc
  have hlim := UniformContinuousOn.tendstoUniformlyOn
    (F := fun a : ℝ × Phase n => frozenTargetCoefficient (lineHomotopy J a.1) a.2) huc (show (s,y)∈U from ⟨hsI,mem_insert _ _⟩)
  have hp : Tendsto (fun i => (t i,x i)) atTop (𝓝[U] (s,y)) :=
    tendsto_nhdsWithin_iff.mpr ⟨hs.prodMk_nhds hx,Eventually.of_forall (fun i => ⟨ht i,mem_insert_of_mem _ ⟨i,rfl⟩⟩)⟩
  intro W hW
  exact hp (hlim W hW)

lemma exact_frame_tendsto {J : Phase n → End n}
    (hJs : ContDiff ℝ ∞ J) (hJ : ∀ x,Compatible (J x))
    {t : ℕ → ℝ} (ht : ∀ i,t i∈Icc (0:ℝ) 1) {s : ℝ} (hs : Tendsto t atTop (𝓝 s))
    {x : ℕ → Phase n} {y : Phase n} (hx : Tendsto x atTop (𝓝 y)) :
    Tendsto (fun i => compatibleFrame (lineHomotopy J (t i) (x i))) atTop
      (𝓝 (compatibleFrame (lineHomotopy J s y))) ∧
    Tendsto (fun i => (compatibleFrame (lineHomotopy J (t i) (x i))).inverse) atTop
      (𝓝 (compatibleFrame (lineHomotopy J s y)).inverse) := by
  have hsI : s∈Icc (0:ℝ) 1 := isClosed_Icc.mem_of_tendsto hs (Eventually.of_forall ht)
  have hP := compatibleFrame_contDiffAt (lineHomotopy_joint_contDiffAt hJs hJ (v := (s,y)) hsI)
  have hp := hP.continuousAt.tendsto.comp (hs.prodMk_nhds hx)
  refine ⟨hp,?_⟩
  have hi : ContDiffAt ℝ ∞ (fun T : End n => T.inverse) (compatibleFrame (lineHomotopy J s y)) :=
    (compatibleFrame_invertible (lineHomotopy_compatible hJ hsI y)).contDiffAt_map_inverse
  exact hi.continuousAt.tendsto.comp hp

end

variable {n : ℕ}

local instance ecgInst1_rfb59fc_1 : NormedAddCommGroup (End n) := ContinuousLinearMap.toNormedAddCommGroup
local instance ecgInst2_rfb59fc_1 : NormedSpace ℝ (End n) := ContinuousLinearMap.toNormedSpace
lemma rescaledCurve_fderiv {u : ℂ → Phase n} (hu : ContDiff ℝ ∞ u) (y : ℂ) (r : ℝ) (z : ℂ) :
    fderiv ℝ (rescaledCurve u y r) z=r • fderiv ℝ u (y+r • z) := by
  have hh := (hu.differentiable (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top) (y+r • z)).hasFDerivAt.comp z
    (((ContinuousLinearMap.id ℝ ℂ).hasFDerivAt.const_smul r).const_add y)
  have he : (fderiv ℝ u (y+r • z)).comp (r • ContinuousLinearMap.id ℝ ℂ)=
      r • fderiv ℝ u (y+r • z) := by ext h; simp only [ContinuousLinearMap.comp_apply,smul_apply,ContinuousLinearMap.id_apply,map_smul]
  rw [he] at hh
  exact hh.fderiv

lemma rescaledCurve_CR {J : Phase n → End n} {u : ℂ → Phase n}
    (hu : ContDiff ℝ ∞ u) (hcr : ∀ z,PseudoHolomorphicAt J u z) (y : ℂ) (r : ℝ) (z : ℂ) :
    fderiv ℝ (rescaledCurve u y r) z Complex.I=
      J (rescaledCurve u y r z) (fderiv ℝ (rescaledCurve u y r) z 1) := by
  rw [rescaledCurve_fderiv hu y r z]
  simp only [smul_apply,map_smul]
  have hh := (hcr (y+r • z)).2 1
  simp only [mul_one] at hh
  exact congrArg (fun v => r • v) hh

end HigherDimensionalBallPacking.Rigidity

namespace HigherDimensionalBallPacking.Rigidity.HolderCompletion
open scoped Topology ContDiff
open Set Filter
variable {X E F : Type*} [MetricSpace X] [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

omit [MetricSpace X] [NormedSpace ℝ E] in
lemma uniform_values_cauchy_on {u : ℕ → X → E} {v : X → E} {K : Set X}
    (hu : TendstoUniformlyOn u v atTop K) :
    ∀ ε : ℝ,0<ε →∃ N : ℕ,∀ i≥N,∀ j≥N,∀ x∈K,‖u i x-u j x‖≤ε := by
  have hh := (tendstoUniformlyOn_iff_restrict.mp hu)
  have hc := uniform_cauchy_of_tendstoUniformly hh
  intro ε hε
  obtain ⟨N,hN⟩ := hc ε hε
  exact ⟨N,fun i hi j hj x hx => hN i hi j hj ⟨x,hx⟩⟩

omit [MetricSpace X] in
lemma uniform_clm_cauchy_on {P : ℕ → E →L[ℝ] F} {u : ℕ → X → E} {K : Set X}
    {G M : ℝ} (hG : 0≤G) (hM : 0≤M)
    (hP : ∀ i,‖P i‖≤G) (hu : ∀ i,∀ x∈K,‖u i x‖≤M)
    (hPc : CauchySeq P)
    (huc : ∀ ε : ℝ,0<ε →∃ N : ℕ,∀ i≥N,∀ j≥N,∀ x∈K,‖u i x-u j x‖≤ε) :
    ∀ ε : ℝ,0<ε →∃ N : ℕ,∀ i≥N,∀ j≥N,∀ x∈K,‖P i (u i x)-P j (u j x)‖≤ε := by
  intro ε hε
  have hh : 0<G+M+1 := by linarith
  let d := ε/(G+M+1)
  have hd : 0<d := div_pos hε hh
  obtain ⟨N,hN⟩ := huc d hd
  obtain ⟨Q,hQ⟩ := Metric.cauchySeq_iff.mp hPc d hd
  refine ⟨max N Q,fun i hi j hj x hx => ?_⟩
  have h1 := hN i ((le_max_left _ _).trans hi) j ((le_max_left _ _).trans hj) x hx
  have h2 := hQ i ((le_max_right _ _).trans hi) j ((le_max_right _ _).trans hj)
  rw [dist_eq_norm] at h2
  have hbound := clm_pair_difference (P i) (P j) (u i x) (u j x)
  have hA := mul_le_mul (hP i) h1 (norm_nonneg _) hG
  have hB := mul_le_mul h2.le (hu j x hx) (norm_nonneg _) hd.le
  have he : G*d+d*M≤ε := by
    have hid : (G+M+1)*d=ε := mul_div_cancel₀ ε (ne_of_gt hh)
    nlinarith
  exact hbound.trans ((add_le_add hA hB).trans he)

variable {n : ℕ}
lemma centered_rescaled_cauchy {u : ℕ → ℂ → Phase n} {v : ℂ → Phase n}
    (hu : ∀ K : Set ℂ,IsCompact K →TendstoUniformlyOn u v atTop K) (c : ℂ) (r : ℝ) :
    ∀ ε : ℝ,0<ε →∃ N : ℕ,∀ i≥N,∀ j≥N,∀ z,‖z‖≤2 →
      ‖(rescaledCurve (u i) c r z-u i c)-(rescaledCurve (u j) c r z-u j c)‖≤ε := by
  let K := (fun z : ℂ => c+r • z) '' Metric.closedBall (0:ℂ) 2
  have hK : IsCompact K := (isCompact_closedBall (0:ℂ) 2).image (continuous_const.add (continuous_id.const_smul r))
  have hval := uniform_values_cauchy_on (hu K hK)
  intro ε hε
  obtain ⟨N,hN⟩ := hval (ε/2) (half_pos hε)
  refine ⟨N,fun i hi j hj z hz => ?_⟩
  have hzK : c+r • z∈K := ⟨z,by simpa only [Metric.mem_closedBall,dist_zero_right] using hz,rfl⟩
  have hcK : c∈K := ⟨0,by simp,by simp⟩
  have h1 := hN i hi j hj (c+r • z) hzK
  have h2 := hN i hi j hj c hcK
  have he : (rescaledCurve (u i) c r z-u i c)-(rescaledCurve (u j) c r z-u j c)=
      (u i (c+r • z)-u j (c+r • z))-(u i c-u j c) := by dsimp [rescaledCurve]; abel
  rw [he]
  exact (norm_sub_le _ _).trans (by linarith)

end HigherDimensionalBallPacking.Rigidity.HolderCompletion
end

end OAI
end

section
-- module Solutions.OAIQ240_BP.BallPacking_Compactness_MarkedCurves
attribute [-instance] _root_.OAI.PackingSufficiencySupport.Comparison.convexMaps_nonempty _root_.OAI.PackingSufficiencySupport.FiniteMoment.Radial.instInhabitedQuadrant _root_.OAI.PackingSufficiencySupport.Hamiltonian.flatProduct_chartedSpace
attribute [-simp] _root_.OAI.HigherDimensionalBallPacking.Rigidity.geometricHolder_value _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.infinity_end_count _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.sqrt_sq_complex
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace HigherDimensionalBallPacking.Rigidity
open scoped ContDiff Topology
open Set Function Filter MeasureTheory
open HolderCompletion
open scoped BoundedContinuousFunction
variable {n : ℕ}

attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.eljcInst2
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.eljcInst3
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.eljcInst4
lemma markedLocalCurve_bound {u : ℂ → Phase n} (hu : ContDiff ℝ ∞ u) {M : ℝ}
    (hd : ∀ z,‖fderiv ℝ u z‖≤M) (c : ℂ) {r : ℝ} (hr : 0 ≤ r) (z : ℂ) :
    ‖markedLocalCurve u c r z‖≤M*r*‖z‖ := by
  have hh := norm_sub_le_of_deriv_bound (hu.differentiable (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)) hd (c+r • z) c
  rw [add_sub_cancel_left,norm_smul,Real.norm_eq_abs,abs_of_nonneg hr] at hh
  exact hh.trans_eq (by ring)

lemma bilinear_cauchy {X Y Z : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y] [NormedAddCommGroup Z] [NormedSpace ℝ Z]
    [CompleteSpace X] [CompleteSpace Y] (B : X →L[ℝ] Y →L[ℝ] Z)
    {x : ℕ → X} {y : ℕ → Y} (hx : CauchySeq x) (hy : CauchySeq y) :
    CauchySeq (fun i => B (x i) (y i)) := by
  obtain ⟨a,ha⟩ := cauchySeq_tendsto_of_complete hx
  obtain ⟨b,hb⟩ := cauchySeq_tendsto_of_complete hy
  have hc : Continuous (fun p : X × Y => B p.1 p.2) :=
    (B.continuous.comp continuous_fst).clm_apply continuous_snd
  exact ((hc.tendsto (a,b)).comp (ha.prodMk_nhds hb)).cauchySeq

attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.eljcInst1
lemma cauchy_mapJet {P : ℕ → End n} {v : ℕ → COne ℂ (Phase n)}
    (hP : CauchySeq P) (hv : CauchySeq v) :
    CauchySeq (fun i => mapJetBilinear (D := ℂ) (E := Phase n) (F := Phase n) (P i) (v i)) :=
  bilinear_cauchy (mapJetBilinear (D := ℂ) (E := Phase n) (F := Phase n)) hP hv

lemma undo_frozen_cutoff {A : Phase n → End n} {x : Phase n} (hx : Compatible (A x))
    {u : ℂ → Phase n} (hu : ContDiff ℝ ∞ u) (b : ContDiffBump (0:ℂ)) :
    mapJetBilinear (D := ℂ) (E := Phase n) (F := Phase n) (compatibleFrame (A x)).inverse
      (cutoffCurveJet b (frozenCurve_smooth (J := A) x hu))=
      cutoffCurveJet b (hu.sub (contDiff_const (c := x))) := by
  apply cValue_ext
  intro z
  rw [mapJetBilinear_value,cutoffCurveJet_value,cutoffCurveJet_value,map_smul]
  change b z • ((compatibleFrame (A x)).inverse (compatibleFrame (A x) (u z-x)))=b z • (u z-x)
  rw [compatibleFrame_inverse_left_bp240 hx]

theorem exact_marked_local_jet_cauchy_bp240_oai {J : Phase n → End n}
    (hJs : ContDiff ℝ ∞ J) (hJ : ∀ x,Compatible (J x))
    (hJc : HasCompactSupport (fun x => J x-standardJ n))
    {S T : ℝ} (hST : S<T) (hT : T<1)
    (hout : ∀ x,S < capacity x →J x=standardJ n)
    {p q : Phase n} {t : ℕ → ℝ} (ht : ∀ i,t i∈Icc (0:ℝ) 1)
    {s : ℝ} (hs : Tendsto t atTop (𝓝 s))
    {u : ℕ → ℂ → Phase n} (hu : ∀ i,AffineLineCurve (lineHomotopy J (t i)) p q (u i))
    {v : ℂ → Phase n} (huc : ∀ K : Set ℂ,IsCompact K →TendstoUniformlyOn u v atTop K) :
    ∃ r : ℝ,0 < r ∧ r≤1 ∧ ∀ c : ℂ,
      CauchySeq (fun i => cutoffCurveJet smallDiskBump (markedLocalCurve_smooth (hu i).1 c r)) := by
  obtain ⟨M,hM,hgrad⟩ := exact_marked_line_gradient_bound_bp240 hJs hJ hJc hST hT hout p q
  obtain ⟨L,G,hL,hG,hJL,hP,hPi⟩ := exact_homotopy_target_bounds hJs hJ hJc
  have hG0 : 0≤G := by linarith
  have hGM : 0≤G*M := mul_nonneg hG0 hM.le
  obtain ⟨δ,hδ,hdisk⟩ := disk_nonlinear_jet_cauchy_bp240 (E := Phase n) (by positivity : 0≤G^3*L) hGM
  let r := min 1 (δ/(2*(G*M+1)))
  have hr : 0 < r := lt_min zero_lt_one (div_pos hδ (by positivity))
  have hr1 : r≤1 := min_le_left _ _
  have hrδ : G*(M*r*2)≤δ := by
    have hh := (le_div_iff₀ (by positivity : 0<2*(G*M+1))).mp (min_le_right (1:ℝ) (δ/(2*(G*M+1))))
    nlinarith
  refine ⟨r,hr,hr1,?_⟩
  intro c
  let A : ℕ → Phase n → End n := fun i => lineHomotopy J (t i)
  let P : ℕ → End n := fun i => compatibleFrame (A i (u i c))
  let R : ℕ → ℂ → Phase n := fun i => rescaledCurve (u i) c r
  let W : ℕ → ℂ → Phase n := fun i => frozenCurve (A i) (u i c) (R i)
  let F : ℕ → Phase n → End n := fun i => frozenTargetCoefficient (A i) (u i c)
  have hR : ∀ i,ContDiff ℝ ∞ (R i) := fun i => rescaledCurve_smooth (hu i).1 c r
  have hW : ∀ i,ContDiff ℝ ∞ (W i) := fun i => frozenCurve_smooth (u i c) (hR i)
  have hc : Tendsto (fun i => u i c) atTop (𝓝 (v c)) :=
    (huc {c} isCompact_singleton).tendsto_at (mem_singleton c)
  have hPc := exact_frame_tendsto hJs hJ ht hs hc
  have hFL : ∀ i x y,‖F i x-F i y‖≤(G^3*L)*‖x-y‖ := fun i =>
    frozenTargetCoefficient_lipschitz hL hG0 (hJL (t i) (ht i)) (hP (t i) (ht i) _) (hPi (t i) (ht i) _)
  have hW0 : ∀ i,W i 0=0 := by
    intro i
    simp only [W,frozenCurve,R,rescaledCurve,smul_zero,add_zero,sub_self,map_zero]
  have hzbound : ∀ i z,‖z‖≤2 →‖markedLocalCurve (u i) c r z‖≤M*r*2 := by
    intro i z hz
    exact (markedLocalCurve_bound (hu i).1 (hgrad (t i) (ht i) (u i) (hu i)) c hr.le z).trans
      (mul_le_mul_of_nonneg_left hz (mul_nonneg hM.le hr.le))
  have hWb : ∀ i z,‖z‖≤2 →‖W i z‖≤δ := by
    intro i z hz
    have hh := (P i).le_opNorm (markedLocalCurve (u i) c r z)
    exact hh.trans ((mul_le_mul (hP (t i) (ht i) _) (hzbound i z hz) (norm_nonneg _) hG0).trans hrδ)
  have hWD : ∀ i z,‖z‖≤2 →‖fderiv ℝ (W i) z‖≤G*M := by
    intro i z _
    rw [frozenCurve_fderiv (u i c) ((hR i).differentiable (by simp) z),rescaledCurve_fderiv (hu i).1]
    have hd : ‖r • fderiv ℝ (u i) (c+r • z)‖≤M := by
      rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg hr.le]
      exact (mul_le_mul_of_nonneg_left (hgrad (t i) (ht i) (u i) (hu i) _) hr.le).trans
        (by nlinarith)
    exact ((P i).opNorm_comp_le _).trans (mul_le_mul (hP (t i) (ht i) _) hd (norm_nonneg _) hG0)
  have hZb : ∀ i,∀ z∈Metric.closedBall (0:ℂ) 2,‖markedLocalCurve (u i) c r z‖≤M*2 := by
    intro i z hz
    have hz' : ‖z‖≤2 := by simpa only [Metric.mem_closedBall,dist_zero_right] using hz
    exact (hzbound i z hz').trans (by nlinarith)
  have hZc : ∀ ε : ℝ,0<ε →∃ N : ℕ,∀ i≥N,∀ j≥N,∀ z∈Metric.closedBall (0:ℂ) 2,
      ‖markedLocalCurve (u i) c r z-markedLocalCurve (u j) c r z‖≤ε := by
    intro ε hε
    obtain ⟨N,hN⟩ := centered_rescaled_cauchy huc c r ε hε
    exact ⟨N,fun i hi j hj z hz => hN i hi j hj z (by simpa only [Metric.mem_closedBall,dist_zero_right] using hz)⟩
  have hWc' := uniform_clm_cauchy_on hG0 (mul_nonneg hM.le (by norm_num : (0:ℝ)≤2))
    (fun i => hP (t i) (ht i) (u i c)) hZb hPc.1.cauchySeq hZc
  have hWc : ∀ ε : ℝ,0<ε →∃ N : ℕ,∀ i≥N,∀ j≥N,∀ z,‖z‖≤2 →‖W i z-W j z‖≤ε := by
    intro ε hε
    obtain ⟨N,hN⟩ := hWc' ε hε
    exact ⟨N,fun i hi j hj z hz => hN i hi j hj z (by simpa only [Metric.mem_closedBall,dist_zero_right] using hz)⟩
  have hFc' := uniform_values_cauchy_on
    (frozenHomotopy_tendstoUniformlyOn hJs hJ ht hs hc (isCompact_closedBall (0:Phase n) δ))
  have hFc : ∀ ε : ℝ,0<ε →∃ N : ℕ,∀ i≥N,∀ j≥N,∀ x,‖x‖≤δ →‖F i x-F j x‖≤ε := by
    intro ε hε
    obtain ⟨N,hN⟩ := hFc' ε hε
    exact ⟨N,fun i hi j hj x hx => hN i hi j hj x (by simpa only [Metric.mem_closedBall,dist_zero_right] using hx)⟩
  have hcr : ∀ i z,‖z‖<2 →fderiv ℝ (W i) z Complex.I-Complex.I • fderiv ℝ (W i) z 1=
      F i (W i z) (fderiv ℝ (W i) z 1) := by
    intro i z _
    exact frozenCurve_CR (lineHomotopy_compatible hJ (ht i) _) ((hR i).differentiable (by simp) z)
      (rescaledCurve_CR (hu i).1 (hu i).2.1 c r z)
  have hwcauchy := hdisk W hW F
    (fun i => frozenTargetCoefficient_continuous (lineHomotopy_slice_contDiff hJs hJ (ht i)).continuous _)
    (fun i => frozenTargetCoefficient_zero _ _) hFL hW0 hWb hWD hWc hFc hcr
  have hmapped := cauchy_mapJet hPc.2.cauchySeq hwcauchy
  have he (i : ℕ) : mapJetBilinear (D := ℂ) (E := Phase n) (F := Phase n) (P i).inverse (cutoffCurveJet smallDiskBump (hW i))=
      cutoffCurveJet smallDiskBump (markedLocalCurve_smooth (hu i).1 c r) :=
    undo_frozen_cutoff (lineHomotopy_compatible hJ (ht i) _) (hR i) smallDiskBump
  change CauchySeq (fun i => mapJetBilinear (D := ℂ) (E := Phase n) (F := Phase n)
    (P i).inverse (cutoffCurveJet smallDiskBump (hW i))) at hmapped
  simpa only [he] using hmapped

end HigherDimensionalBallPacking.Rigidity

end

end OAI
end

theorem solution : type_of% @OAI.HigherDimensionalBallPacking.Rigidity.exact_marked_local_jet_cauchy_bp240_oai := @OAI.HigherDimensionalBallPacking.Rigidity.exact_marked_local_jet_cauchy_bp240_oai
