-- Prove2me | solution 1 for OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.fullLineEquation_initial_bp240
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T01:53:52.657977+00:00
-- url     : https://prove2.me/submissions/7fecc1ec-355c-431c-9445-92299018b0ed

import Mathlib
import Definitions.Def_BallPacking
import Definitions.Def_OAIQ240Bp021

section
-- module Solutions.OAIQ240_BP.BallPacking_Holder_MarkedFrame
attribute [-instance] _root_.OAI.PackingSufficiencySupport.Hamiltonian.flatProduct_chartedSpace
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
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]

variable (b : ContDiffBump (0:ℂ))

attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.affineCutInst1
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.affineCutInst2
local instance affineCutInst3_r3f9a6e_1 : NormedAddCommGroup (HMap ℂ E) := inferInstance
local instance affineCutInst4_r3f9a6e_1 : NormedSpace ℝ (HMap ℂ E) := inferInstance
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.affineCutInst5
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.affineCutInst6
omit [CompleteSpace E] in
lemma markedSlope_add (p q : E) (u h : COne ℂ E) :
    markedSlope p q (u+h) = markedSlope p q u-cValue h 1 := by
  simp only [markedSlope,cValue_add]
  abel


end
open scoped ContDiff Topology BoundedContinuousFunction
open Set Filter



end HigherDimensionalBallPacking.Rigidity.HolderCompletion
end

end OAI
end

section
-- module Solutions.OAIQ240_BP.BallPacking_Fredholm_FrameFredholm
attribute [-instance] _root_.OAI.PackingSufficiencySupport.Hamiltonian.flatProduct_chartedSpace
attribute [-simp] _root_.OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.completedDX_value _root_.OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.completedQ_value _root_.OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.freePrincipal_value _root_.OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.freeZeroOrder_value _root_.OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.holderTranslate_value _root_.OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.jetTest_value _root_.OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.jetTranslate_deriv _root_.OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.jetTranslate_value _root_.OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.markedDerivEval_value _root_.OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.markedDerivativeVariation_value _root_.OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.markedVariation_value _root_.OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.realConstantJet_value _root_.OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.supportedEval_value _root_.OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.translationVariation_deriv _root_.OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.translationVariation_value _root_.OAI.HigherDimensionalBallPacking.Rigidity.geometricHolder_value _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.infinity_end_count _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.sqrt_sq_complex
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace HigherDimensionalBallPacking.Rigidity.HolderCompletion

open scoped ContDiff Topology BoundedContinuousFunction
open Set Filter
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]

attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.markedChartInst1
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.markedChartInst2
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.markedChartInst3
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.markedChartInst4
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.markedChartInst5
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.markedChartInst6
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.markedChartInst7
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.markedChartInst8
local instance markedChartInst13_r3f9a6e_1 : NormedAddCommGroup (ℂ →L[ℝ] E) := ContinuousLinearMap.toNormedAddCommGroup
local instance markedChartInst14_r3f9a6e_1 : NormedSpace ℝ (ℂ →L[ℝ] E) := ContinuousLinearMap.toNormedSpace
omit [CompleteSpace E] in
@[simp] lemma markedDX_value [CompleteSpace E] (p q : E) (u h : COne ℂ E) (z : ℂ) :
    valueCLM _ (markedDX p q u h) z = fderiv ℝ (markedCurve p q (u+h)) z 1 := by
  rw [markedCurve_fderiv,markedSlope_add]
  simp only [add_apply,complexSlope_apply,one_smul]
  rfl



end HigherDimensionalBallPacking.Rigidity.HolderCompletion
end

end OAI
end

section
-- module Solutions.OAIQ240_BP.BallPacking_Continuation_CompatibleHomotopy
attribute [-instance] _root_.OAI.PackingSufficiencySupport.Hamiltonian.flatProduct_chartedSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace HigherDimensionalBallPacking.Rigidity
open scoped ContDiff Topology
open Set Function Filter

variable {n : ℕ}

attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.ghInst1
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.ghInst2
variable {J : Phase n → End n} (hJs : ContDiff ℝ ∞ J) (hJ : ∀ x, Compatible (J x))

include hJ in
lemma fullCoefficient_zero (x : Phase n) : fullCoefficient J (0,x)=0 := by
  simp only [fullCoefficient,fullTime_zero,interpolateJ_zero (hJ x),sub_self,smul_zero]

end HigherDimensionalBallPacking.Rigidity

namespace HigherDimensionalBallPacking.Rigidity.HolderCompletion
open scoped ContDiff Topology BoundedContinuousFunction
open Set Function Filter
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
variable (b₁ : ContDiffBump (0:ℂ)) (p q : E)

attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.gmc1
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.gmc2
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.gmc3
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.gmc4
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.gmc5
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.gmc6
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.gmc7
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.gmc8
omit [CompleteSpace E] in
lemma globalParameterJet_value [CompleteSpace E] (v : ℝ × COne ℂ E) (z : ℂ) :
    cValue (globalParameterJet b₁ p q v) z=(v.1,cValue (globalMarkedJet b₁ p q v.2) z) := by
  change (v.1,0)+(0,cValue (globalMarkedJet b₁ p q v.2) z)=_
  simp only [Prod.mk_add_mk,zero_add,add_zero]

variable {P : ℝ × E → E →L[ℝ] E} (hP : BoundedCThree P)

lemma globalCoefficient_value (v : ℝ × COne ℂ E) (z : ℂ) :
    valueCLM _ (globalCoefficient b₁ p q hP v) z=P (v.1,cValue (globalMarkedJet b₁ p q v.2) z) := by
  change P (0+cValue (globalParameterJet b₁ p q v) z)=_
  rw [zero_add,globalParameterJet_value]

end HigherDimensionalBallPacking.Rigidity.HolderCompletion
end

end OAI
end

section
-- module Solutions.OAIQ240_BP.BallPacking_Continuation_ParameterizedImplicit
attribute [-instance] _root_.OAI.PackingSufficiencySupport.Hamiltonian.flatProduct_chartedSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace HigherDimensionalBallPacking.Rigidity.HolderCompletion
open scoped ContDiff Topology
open Filter
open scoped BoundedContinuousFunction
open Set Function
section
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
variable (b b₁ : ContDiffBump (0:ℂ)) (p q : E)
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.gmChartInst1
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.gmChartInst2
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.gmChartInst3
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.gmChartInst4
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.gmChartInst5
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.gmChartInst6
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.gmChartInst7
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.gmChartInst8
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.gmChartInst9
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.gmChartInst10
local instance gmChartInst11_r3f9a6e_1 : AddCommGroup (markedModel (E := E) (Metric.closedBall (0:ℂ) b.rOut)) := (gmChartInst9 b).toAddCommGroup
local instance gmChartInst12_r3f9a6e_1 : Module ℝ (markedModel (E := E) (Metric.closedBall (0:ℂ) b.rOut)) := (gmChartInst10 b).toModule
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.gmChartInst13
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.gmChartInst14
local instance gmChartInst15_r3f9a6e_1 : AddCommGroup (supportedHolder (E := E) (Metric.closedBall (0:ℂ) b.rOut)) := (gmChartInst13 b).toAddCommGroup
local instance gmChartInst16_r3f9a6e_1 : Module ℝ (supportedHolder (E := E) (Metric.closedBall (0:ℂ) b.rOut)) := (gmChartInst14 b).toModule
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.gmChartInst17
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.gmChartInst18
local instance gmChartInst19_r3f9a6e_1 : AddCommGroup (ℝ × markedModel (E := E) (Metric.closedBall (0:ℂ) b.rOut)) := (gmChartInst17 b).toAddCommGroup
local instance gmChartInst20_r3f9a6e_1 : Module ℝ (ℝ × markedModel (E := E) (Metric.closedBall (0:ℂ) b.rOut)) := (gmChartInst18 b).toModule
variable {P : ℝ × E → E →L[ℝ] E} (hP : BoundedCThree P)

lemma globalChart_value (t : ℝ) (w : markedModel (E := E) (Metric.closedBall (0:ℂ) b.rOut)) (z : ℂ) :
    valueCLM _ (globalChart b b₁ p q hP (t,w)).val z=valueCLM _ (standardJetCR w.val) z-
      b z • P (t,cValue (globalMarkedJet b₁ p q w.val) z) (fderiv ℝ (markedCurve p q w.val) z 1) := by
  change valueCLM _ (standardJetCR w.val) z-b z • valueCLM _ (globalNonlinearity b b₁ p q hP (t,w)) z=_
  simp only [globalNonlinearity,bilinCLM_value,globalCoefficient_value,markedDX_value,zero_add]
  rfl

lemma globalChart_at_zero (hP0 : ∀ x,P (0,x)=0)
    (w : markedModel (E := E) (Metric.closedBall (0:ℂ) b.rOut)) :
    globalChart b b₁ p q hP (0,w)=markedCR (E := E) (K := Metric.closedBall (0:ℂ) b.rOut) w := by
  apply Subtype.ext
  apply value_ext
  intro z
  have hV := globalChart_value b b₁ p q hP 0 w z
  have hz := hP0 (cValue (globalMarkedJet b₁ p q w.val) z)
  have hzero : P (0,cValue (globalMarkedJet b₁ p q w.val) z)
      (fderiv ℝ (markedCurve p q w.val) z 1)=0 := by
    rw [hz,zero_apply]
  rw [hzero,smul_zero,sub_zero] at hV
  exact hV

end
section
variable {n : ℕ}
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.gle1
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.gle2
local instance gle3_r3f9a6e_1 : NormedAddCommGroup (COne ℂ (Phase n)) := inferInstance
local instance gle4_r3f9a6e_1 : NormedSpace ℝ (COne ℂ (Phase n)) := inferInstance
local instance gle5_r3f9a6e_1 : NormedAddCommGroup (HMap ℂ (Phase n)) := inferInstance
local instance gle6_r3f9a6e_1 : NormedSpace ℝ (HMap ℂ (Phase n)) := inferInstance
variable {J : Phase n → End n} (hJs : ContDiff ℝ ∞ J) (hJ : ∀ x,Compatible (J x))
  (hJc : HasCompactSupport (fun x => J x-standardJ n))
variable (b b₁ : ContDiffBump (0:ℂ)) (p q : Phase n)

local instance gle7_r3f9a6e_1 : NormedAddCommGroup (markedModel (E := Phase n) (Metric.closedBall (0:ℂ) b.rOut)) := inferInstance
local instance gle8_r3f9a6e_1 : NormedSpace ℝ (markedModel (E := Phase n) (Metric.closedBall (0:ℂ) b.rOut)) := inferInstance
local instance gle9_r3f9a6e_1 : NormedAddCommGroup (supportedHolder (E := Phase n) (Metric.closedBall (0:ℂ) b.rOut)) := inferInstance
local instance gle10_r3f9a6e_1 : NormedSpace ℝ (supportedHolder (E := Phase n) (Metric.closedBall (0:ℂ) b.rOut)) := inferInstance
lemma fullLineEquation_initial_bp240_oai
    (w : markedModel (E := Phase n) (Metric.closedBall (0:ℂ) b.rOut)) :
    fullLineEquation hJs hJ hJc b b₁ p q (0,w)=
      markedCR (E := Phase n) (K := Metric.closedBall (0:ℂ) b.rOut) w :=
  globalChart_at_zero b b₁ p q (fullCoefficientBound hJs hJ hJc) (fullCoefficient_zero hJ) w

end

end HigherDimensionalBallPacking.Rigidity.HolderCompletion

end

end OAI
end

theorem solution : type_of% @OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.fullLineEquation_initial_bp240_oai := @OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.fullLineEquation_initial_bp240_oai
