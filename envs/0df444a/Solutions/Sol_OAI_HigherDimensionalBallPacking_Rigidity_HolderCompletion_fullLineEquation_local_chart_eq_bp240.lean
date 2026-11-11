-- Prove2me | solution 1 for OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.fullLineEquation_local_chart_eq_bp240
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T01:56:02.803653+00:00
-- url     : https://prove2.me/submissions/567d5a26-cee9-4b68-9e8f-f60ff5229f01

import Mathlib
import Definitions.Def_BallPacking
import Definitions.Def_OAIQ240Bp022
import Theorems.Thm_OAI_HigherDimensionalBallPacking_Rigidity_HolderCompletion_actualMarkedChart_value_bp240

section
-- module Solutions.OAIQ240_BP.BallPacking_Holder_MarkedJets
attribute [-instance] _root_.OAI.PackingSufficiencySupport.Hamiltonian.flatProduct_chartedSpace
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

variable {K : Set ℂ} (hK : IsCompact K)

local instance markedAffineInst1_r2ccd7b_1 : NormedAddCommGroup (COne ℂ E) := inferInstance
local instance markedAffineInst2_r2ccd7b_1 : NormedSpace ℝ (COne ℂ E) := inferInstance
local instance markedAffineInst3_r2ccd7b_1 : NormedAddCommGroup (HMap ℂ E) := inferInstance
local instance markedAffineInst4_r2ccd7b_1 : NormedSpace ℝ (HMap ℂ E) := inferInstance
local instance markedAffineInst5_r2ccd7b_1 : NormedAddCommGroup (markedModel (E := E) K) := inferInstance
local instance markedAffineInst6_r2ccd7b_1 : NormedSpace ℝ (markedModel (E := E) K) := inferInstance
local instance markedAffineInst7_r2ccd7b_1 : NormedAddCommGroup (supportedHolder (E := E) K) := inferInstance
local instance markedAffineInst8_r2ccd7b_1 : NormedSpace ℝ (supportedHolder (E := E) K) := inferInstance
omit [CompleteSpace E] in
lemma markedCurve_standardResidual (p q : E) (u : COne ℂ E) (z : ℂ) :
    fderiv ℝ (markedCurve p q u) z Complex.I -
      Complex.I • fderiv ℝ (markedCurve p q u) z 1 = valueCLM _ (standardJetCR u) z := by
  rw [markedCurve_fderiv,standardJetCR_value]
  simp only [add_apply,complexSlope_apply,one_smul,smul_add]
  abel



end HigherDimensionalBallPacking.Rigidity.HolderCompletion
end

end OAI
end

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
local instance affineCutInst3_r2ccd7b_1 : NormedAddCommGroup (HMap ℂ E) := inferInstance
local instance affineCutInst4_r2ccd7b_1 : NormedSpace ℝ (HMap ℂ E) := inferInstance
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
local instance markedChartInst13_r2ccd7b_1 : NormedAddCommGroup (ℂ →L[ℝ] E) := ContinuousLinearMap.toNormedAddCommGroup
local instance markedChartInst14_r2ccd7b_1 : NormedSpace ℝ (ℂ →L[ℝ] E) := ContinuousLinearMap.toNormedSpace
omit [CompleteSpace E] in
@[simp] lemma markedDX_value [CompleteSpace E] (p q : E) (u h : COne ℂ E) (z : ℂ) :
    valueCLM _ (markedDX p q u h) z = fderiv ℝ (markedCurve p q (u+h)) z 1 := by
  rw [markedCurve_fderiv,markedSlope_add]
  simp only [add_apply,complexSlope_apply,one_smul]
  rfl

variable {P : E → E →L[ℝ] E} (hP : BoundedCThree P) (b : ContDiffBump (0:ℂ))

@[simp] lemma chartNonlinearity_value (p q : E) (u h : COne ℂ E) (z : ℂ) :
    valueCLM _ (chartNonlinearity hP b p q u h) z = P (truncatedCurve b p q u h z)
      (fderiv ℝ (markedCurve p q (u+h)) z 1) := by
  rw [chartNonlinearity,bilinCLM_value,truncatedCoefficient_value,markedDX_value]
  rfl

omit [CompleteSpace E] in
lemma cutoff_action_eq [CompleteSpace E] {A₀ A₁ : E →L[ℝ] E} {z : ℂ} (hA : A₀ = A₁)
    (hz0 : z ∉ Metric.closedBall 0 b.rIn → A₁ = 0) (v : E) :
    b z • A₀ v = A₁ v := by
  subst A₀
  by_cases hz : z ∈ Metric.closedBall 0 b.rIn
  · calc
      b z • A₁ v = (1:ℝ) • A₁ v := congrArg (fun c : ℝ => c • A₁ v) (b.one_of_mem_closedBall hz)
      _ = A₁ v := one_smul ℝ _
  · have ha : A₁ v = 0 := congrArg (fun A : E →L[ℝ] E => A v) (hz0 hz)
    calc
      b z • A₁ v = b z • (0:E) := congrArg (fun w : E => b z • w) ha
      _ = 0 := smul_zero _
      _ = A₁ v := ha.symm



end HigherDimensionalBallPacking.Rigidity.HolderCompletion
end

end OAI
end

section
-- module Solutions.OAIQ240_BP.BallPacking_Continuation_CompatibleHomotopy
attribute [-instance] _root_.OAI.PackingSufficiencySupport.Hamiltonian.flatProduct_chartedSpace
attribute [-simp] _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.infinity_end_count _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.sqrt_sq_complex
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

lemma fullCoefficient_outside {B : ℝ} (hstd : ∀ x, B<‖x‖ → J x=standardJ n) :
    ∀ t x, B<‖x‖ → fullCoefficient J (t,x)=0 := by
  intro t x hx
  simp only [fullCoefficient,hstd x hx,interpolateJ_standard_initial
    ⟨lt_of_lt_of_le (by norm_num) (fullTime_range _).1,(fullTime_range _).2⟩,sub_self,smul_zero]

lemma fullCoefficient_exact {t : ℝ} (ht : t∈Icc (0:ℝ) 1) (x : Phase n) :
    standardJ n+fullCoefficient J (t,x)=lineHomotopy J (fullTime t) x := by
  have hb : t∈Metric.closedBall (0:ℝ) fullTimeBump.rIn := by
    rw [Metric.mem_closedBall,dist_zero_right,Real.norm_eq_abs,abs_of_nonneg ht.1]
    exact ht.2.trans (by norm_num [fullTimeBump])
  rw [fullCoefficient,fullTimeBump.one_of_mem_closedBall hb,one_smul]
  change standardJ n+(interpolateJ (J x) (fullTime t)-standardJ n)=_
  abel

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
lemma globalMarkedJet_value [CompleteSpace E] (w : COne ℂ E) (z : ℂ) :
    cValue (globalMarkedJet b₁ p q w) z=p+b₁ z • (z • markedSlope p q w)+cValue w z := by
  change p+cValue (cutoffSlope b₁ (markedSlope p q w)) z+cValue w z=_
  rw [cutoffSlope_value]

lemma globalMarkedJet_eq_marked (w : COne ℂ E) {z : ℂ}
    (hz : z∈Metric.closedBall (0:ℂ) b₁.rIn) :
    cValue (globalMarkedJet b₁ p q w) z=markedCurve p q w z := by
  rw [globalMarkedJet_value,b₁.one_of_mem_closedBall hz,one_smul]
  rfl

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
local instance gmChartInst11_r2ccd7b_1 : AddCommGroup (markedModel (E := E) (Metric.closedBall (0:ℂ) b.rOut)) := (gmChartInst9 b).toAddCommGroup
local instance gmChartInst12_r2ccd7b_1 : Module ℝ (markedModel (E := E) (Metric.closedBall (0:ℂ) b.rOut)) := (gmChartInst10 b).toModule
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.gmChartInst13
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.gmChartInst14
local instance gmChartInst15_r2ccd7b_1 : AddCommGroup (supportedHolder (E := E) (Metric.closedBall (0:ℂ) b.rOut)) := (gmChartInst13 b).toAddCommGroup
local instance gmChartInst16_r2ccd7b_1 : Module ℝ (supportedHolder (E := E) (Metric.closedBall (0:ℂ) b.rOut)) := (gmChartInst14 b).toModule
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.gmChartInst17
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.gmChartInst18
local instance gmChartInst19_r2ccd7b_1 : AddCommGroup (ℝ × markedModel (E := E) (Metric.closedBall (0:ℂ) b.rOut)) := (gmChartInst17 b).toAddCommGroup
local instance gmChartInst20_r2ccd7b_1 : Module ℝ (ℝ × markedModel (E := E) (Metric.closedBall (0:ℂ) b.rOut)) := (gmChartInst18 b).toModule
variable {P : ℝ × E → E →L[ℝ] E} (hP : BoundedCThree P)

lemma globalChart_value (t : ℝ) (w : markedModel (E := E) (Metric.closedBall (0:ℂ) b.rOut)) (z : ℂ) :
    valueCLM _ (globalChart b b₁ p q hP (t,w)).val z=valueCLM _ (standardJetCR w.val) z-
      b z • P (t,cValue (globalMarkedJet b₁ p q w.val) z) (fderiv ℝ (markedCurve p q w.val) z 1) := by
  change valueCLM _ (standardJetCR w.val) z-b z • valueCLM _ (globalNonlinearity b b₁ p q hP (t,w)) z=_
  simp only [globalNonlinearity,bilinCLM_value,globalCoefficient_value,markedDX_value,zero_add]
  rfl

lemma globalChart_actual_value
    (hb₁ : Metric.closedBall (0:ℂ) b.rOut⊆Metric.closedBall (0:ℂ) b₁.rIn)
    {B : ℝ} (hPB : ∀ t x,B<‖x‖ → P (t,x)=0) (t : ℝ)
    (w : markedModel (E := E) (Metric.closedBall (0:ℂ) b.rOut))
    (he : ∀ z,b.rIn≤‖z‖ → B<‖markedCurve p q w.val z‖) (z : ℂ) :
    valueCLM _ (globalChart b b₁ p q hP (t,w)).val z=
      fderiv ℝ (markedCurve p q w.val) z Complex.I-
        (Complex.I • fderiv ℝ (markedCurve p q w.val) z 1+
          P (t,markedCurve p q w.val z) (fderiv ℝ (markedCurve p q w.val) z 1)) := by
  have hz0 : z∉Metric.closedBall (0:ℂ) b.rIn → P (t,markedCurve p q w.val z)=0 := by
    intro hz
    apply hPB
    apply he
    exact (lt_of_not_ge (by simpa only [Metric.mem_closedBall,dist_zero_right] using hz)).le
  have hN : b z • P (t,cValue (globalMarkedJet b₁ p q w.val) z)
      (fderiv ℝ (markedCurve p q w.val) z 1)=
      P (t,markedCurve p q w.val z) (fderiv ℝ (markedCurve p q w.val) z 1) := by
    by_cases hz : z∈Metric.closedBall (0:ℂ) b.rOut
    · apply cutoff_action_eq b _ hz0
      rw [globalMarkedJet_eq_marked b₁ p q w.val (hb₁ hz)]
    · have hb0 : b z=0 := image_eq_zero_of_notMem_tsupport (by rwa [b.tsupport_eq])
      have hz' : z∉Metric.closedBall (0:ℂ) b.rIn :=
        fun h => hz (Metric.closedBall_subset_closedBall b.rIn_lt_rOut.le h)
      rw [hb0,hz0 hz',zero_apply,zero_smul]
  have hS := markedCurve_standardResidual p q w.val z
  calc
    _ = valueCLM _ (standardJetCR w.val) z-b z •
        P (t,cValue (globalMarkedJet b₁ p q w.val) z) (fderiv ℝ (markedCurve p q w.val) z 1) :=
      globalChart_value b b₁ p q hP t w z
    _ = (fderiv ℝ (markedCurve p q w.val) z Complex.I-
        Complex.I • fderiv ℝ (markedCurve p q w.val) z 1)-
        P (t,markedCurve p q w.val z) (fderiv ℝ (markedCurve p q w.val) z 1) :=
      congrArg₂ (· - ·) hS.symm hN
    _ = _ := sub_sub _ _ _

end
section
variable {n : ℕ}
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.gle1
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.gle2
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.gle3
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.gle4
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.gle5
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.gle6
variable {J : Phase n → End n} (hJs : ContDiff ℝ ∞ J) (hJ : ∀ x,Compatible (J x))
  (hJc : HasCompactSupport (fun x => J x-standardJ n))
variable (b b₁ : ContDiffBump (0:ℂ)) (p q : Phase n)

attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.gle7
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.gle8
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.gle9
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.gle10
local instance gle11_r2ccd7b_1 : AddCommGroup (markedModel (E := Phase n) (Metric.closedBall (0:ℂ) b.rOut)) := (gle7 (n := n) b).toAddCommGroup
local instance gle12_r2ccd7b_1 : Module ℝ (markedModel (E := Phase n) (Metric.closedBall (0:ℂ) b.rOut)) := (gle8 (n := n) b).toModule
local instance gle13_r2ccd7b_1 : AddCommGroup (supportedHolder (E := Phase n) (Metric.closedBall (0:ℂ) b.rOut)) := (gle9 (n := n) b).toAddCommGroup
local instance gle14_r2ccd7b_1 : Module ℝ (supportedHolder (E := Phase n) (Metric.closedBall (0:ℂ) b.rOut)) := (gle10 (n := n) b).toModule
variable (hb₁ : Metric.closedBall (0:ℂ) b.rOut⊆Metric.closedBall (0:ℂ) b₁.rIn)
  {B : ℝ} (hstd : ∀ x,B<‖x‖ → J x=standardJ n)
  {t : ℝ} (ht : t∈Icc (0:ℝ) 1)
  (w : markedModel (E := Phase n) (Metric.closedBall (0:ℂ) b.rOut))
  (he : ∀ z,b.rIn≤‖z‖ → B<‖markedCurve p q w.val z‖)

include hb₁ hstd ht he in
lemma fullLineEquation_value (z : ℂ) :
    valueCLM _ (fullLineEquation hJs hJ hJc b b₁ p q (t,w)).val z=
      fderiv ℝ (markedCurve p q w.val) z Complex.I-
        lineHomotopy J (fullTime t) (markedCurve p q w.val z)
          (fderiv ℝ (markedCurve p q w.val) z 1) := by
  have hx := globalChart_actual_value b b₁ p q (fullCoefficientBound hJs hJ hJc)
    hb₁ (fullCoefficient_outside hstd) t w he z
  have hc := congrArg (fun A : End n => A (fderiv ℝ (markedCurve p q w.val) z 1))
    (fullCoefficient_exact (J := J) ht (markedCurve p q w.val z))
  change Complex.I • fderiv ℝ (markedCurve p q w.val) z 1+
    fullCoefficient J (t,markedCurve p q w.val z) (fderiv ℝ (markedCurve p q w.val) z 1)=_ at hc
  exact hx.trans (congrArg (fun v : Phase n => fderiv ℝ (markedCurve p q w.val) z Complex.I-v) hc)

end
section

variable {n : ℕ}
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.glf1
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.glf2
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.glf3
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.glf4
variable {J : Phase n → End n} (hJs : ContDiff ℝ ∞ J) (hJ : ∀ x,Compatible (J x))
  (hJc : HasCompactSupport (fun x => J x-standardJ n))
  (b b₁ : ContDiffBump (0:ℂ)) (p q : Phase n)
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.glf5
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.glf6
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.glf7
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.glf8
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.glf9
local instance glf10_r2ccd7b_1 : Module ℝ (markedModel (E := Phase n) (Metric.closedBall (0:ℂ) b.rOut)) := (glf6 (n := n) b).toModule
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.glf11
local instance glf12_r2ccd7b_1 : Module ℝ (supportedHolder (E := Phase n) (Metric.closedBall (0:ℂ) b.rOut)) := (glf8 (n := n) b).toModule
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.glf13
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.glf14
variable (hb₁ : Metric.closedBall (0:ℂ) b.rOut⊆Metric.closedBall (0:ℂ) b₁.rIn)
  {B : ℝ} (hstd : ∀ x,B<‖x‖ →J x=standardJ n)
  {t : ℝ} (ht : t∈Icc (0:ℝ) 1)
  (w : markedModel (E := Phase n) (Metric.closedBall (0:ℂ) b.rOut))
  (he : MarkedEscapeNeighborhood b p q w.val B)

include hb₁ hstd ht he in
lemma fullLineEquation_local_chart_eq_bp240_oai :
    (fun h => fullLineEquation hJs hJ hJc b b₁ p q (t,w+h)) =ᶠ[𝓝 0]
      actualMarkedChart (lineHomotopy_slice_contDiff hJs hJ (fullTime_range t))
        (fullTime_slice_outside hstd (t := t)) b p q w := by
  filter_upwards [he] with h hh
  apply Subtype.ext
  apply value_ext
  intro z
  have hv := fullLineEquation_value hJs hJ hJc b b₁ p q hb₁ hstd ht (w+h)
    (fun z hz => (hh z hz).1) z
  have ha := actualMarkedChart_value_bp240 (lineHomotopy_slice_contDiff hJs hJ (fullTime_range t))
    (fullTime_slice_outside hstd (t := t)) b p q w h hh z
  exact hv.trans ha.symm

end

end HigherDimensionalBallPacking.Rigidity.HolderCompletion

end

end OAI
end

theorem solution : type_of% @OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.fullLineEquation_local_chart_eq_bp240_oai := @OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.fullLineEquation_local_chart_eq_bp240_oai
