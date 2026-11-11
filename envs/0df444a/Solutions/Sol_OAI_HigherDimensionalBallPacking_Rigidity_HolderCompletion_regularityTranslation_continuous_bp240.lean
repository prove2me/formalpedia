-- Prove2me | solution 1 for OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.regularityTranslation_continuous_bp240
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T02:20:49.082677+00:00
-- url     : https://prove2.me/submissions/6a3e4927-1823-482a-80d1-55a23e36a956

import Mathlib
import Definitions.Def_BallPacking
import Definitions.Def_OAIQ240Bp022
import Theorems.Thm_OAI_HigherDimensionalBallPacking_Rigidity_HolderCompletion_completedFreePrincipal_fredholm_bp240
import Theorems.Thm_OAI_HigherDimensionalBallPacking_Rigidity_HolderCompletion_freeTranslation_zero_bp240
import Theorems.Thm_OAI_HigherDimensionalBallPacking_Rigidity_HolderCompletion_jetObservations_translation_smooth_bp240
import Theorems.Thm_OAI_HigherDimensionalBallPacking_Rigidity_HolderCompletion_jetTest_separates_bp240
import Theorems.Thm_OAI_HigherDimensionalBallPacking_Rigidity_HolderCompletion_jetValue_translate_tendsto_bp240
import Theorems.Thm_OAI_HigherDimensionalBallPacking_Rigidity_finite_separating_family_bp240
import Theorems.Thm_OAI_HigherDimensionalBallPacking_Rigidity_fredholm_stabilized_leftInverse_bp240

section
-- module Solutions.OAIQ240_BP.BallPacking_Compactness_AffineCorrectionInfinity
attribute [-instance] _root_.OAI.PackingSufficiencySupport.Hamiltonian.flatProduct_chartedSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped ContDiff Topology BoundedContinuousFunction
open Set Filter
namespace HigherDimensionalBallPacking.Rigidity.HolderCompletion
variable {D E : Type*} [NormedAddCommGroup D] [NormedSpace ℝ D]
  [NormedAddCommGroup E] [NormedSpace ℝ E]

attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.transInst1
local instance transInst2_r4a87a2_1 : NormedSpace ℝ (HMap D E) := inferInstance
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.transInst3
local instance transInst4_r4a87a2_1 : NormedSpace ℝ (COne D E) := inferInstance
omit [NormedSpace ℝ D] in
lemma holderTranslate_norm_le [NormedSpace ℝ D] (t : D) (u : HMap D E) : ‖holderTranslate t u‖ ≤ ‖u‖ := by
  apply (norm_le_of_bounds _ (norm_nonneg u) (norm_nonneg u) ?_ ?_).trans (max_self _).le
  · intro z; exact norm_value_le u _
  · intro x y
    simpa only [holderTranslate_value,dist_add_right] using norm_sub_value_le u (x+t) (y+t)

end HigherDimensionalBallPacking.Rigidity.HolderCompletion

end

end OAI
end

section
-- module Solutions.OAIQ240_BP.BallPacking_Fredholm_FreeLinearization
attribute [-instance] _root_.OAI.PackingSufficiencySupport.Hamiltonian.flatProduct_chartedSpace
attribute [-simp] _root_.OAI.HigherDimensionalBallPacking.Rigidity.geometricHolder_value _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.infinity_end_count _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.sqrt_sq_complex
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace HigherDimensionalBallPacking.Rigidity

section
open scoped Topology BoundedContinuousFunction ContDiff
open Set Function Filter
namespace HolderCompletion
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
section Generic
variable {X I : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
omit [CompleteSpace E] in
lemma observed_fredholm_leftInverse [CompleteSpace E] (P : X →L[ℝ] F) (hP : P.IsFredholm)
    (O : I → X →L[ℝ] E) (hO : ∀ x, (∀ i, O i x=0) → x=0) :
    ∃ (s : Finset I) (L : F × (s → E) →L[ℝ] X),
      LeftInverse L (P.prod (ContinuousLinearMap.pi (fun i : s => O i.val))) := by
  let := hP.finite_ker
  obtain ⟨s,hs⟩ := finite_separating_family_bp240 (fun i => (O i).comp P.ker.subtypeL)
    (by
      intro v hv
      apply Subtype.ext
      exact hO v.val hv)
  let Q : X →L[ℝ] (s → E) := ContinuousLinearMap.pi (fun i : s => O i.val)
  have hQ : Injective (Q.comp P.ker.subtypeL) := by
    intro u v huv
    apply sub_eq_zero.mp
    apply hs (u-v)
    intro i hi
    have hh := congrArg (fun f : s → E => f ⟨i,hi⟩) huv
    change O i u.val=O i v.val at hh
    change O i (u.val-v.val)=0
    rw [map_sub,hh,sub_self]
  obtain ⟨L,hL⟩ := fredholm_stabilized_leftInverse_bp240 P hP Q hQ
  exact ⟨s,L,hL⟩
end Generic

variable (S : Submodule ℝ (COne ℂ E))

attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.jetObsInst1
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.jetObsInst2
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.jetObsInst3
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.jetObsInst4
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.jetObsInst5
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.jetObsInst6
lemma exists_jet_fredholm_observations (P : S →L[ℝ] F) (hP : P.IsFredholm) :
    ∃ (s : Finset PlaneTest) (L : F × (s → E) →L[ℝ] S),
      LeftInverse L (P.prod (subspaceObservations S s)) := by
  let O : PlaneTest → S →L[ℝ] E := fun g => (jetTestCLM g).comp S.subtypeL
  have hO : ∀ u : S, (∀ g, O g u=0) → u=0 := by
    intro u hu
    apply Subtype.ext
    exact jetTest_separates_bp240 u.val hu
  have hh := observed_fredholm_leftInverse P hP O hO
  obtain ⟨s,L,hL⟩ := hh
  exact ⟨s,L,hL⟩

end HolderCompletion

end
section
open scoped ContDiff Topology BoundedContinuousFunction
open Set Function Filter
namespace HolderCompletion
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]

variable {R S : ℝ} (hRS : R+1 ≤ S) (a : E)
  (u : freeModel (E := E) (Metric.closedBall (0:ℂ) R))

attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.freeTransInst1
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.freeTransInst2
local instance freeTransInst3_r4a87a2_1 : NormedAddCommGroup (HMap ℂ E) := inferInstance
local instance freeTransInst4_r4a87a2_1 : NormedSpace ℝ (HMap ℂ E) := inferInstance
local instance freeTransInst5_r4a87a2_1 : NormedAddCommGroup (freeModel (E := E) (Metric.closedBall (0:ℂ) S)) := inferInstance
local instance freeTransInst6_r4a87a2_1 : NormedSpace ℝ (freeModel (E := E) (Metric.closedBall (0:ℂ) S)) := inferInstance
lemma freeTranslation_near : ∀ᶠ t in 𝓝 (0:ℂ), (freeTranslation hRS a u t).val=translationVariation a u.val t := by
  filter_upwards [Metric.ball_mem_nhds (0:ℂ) (show (0:ℝ)<1 by norm_num)] with t ht
  have ht' : ‖t‖≤1 := (show ‖t‖<1 by simpa only [Metric.mem_ball,dist_zero_right] using ht).le
  simp only [freeTranslation,dite_eq_left ht']

variable [FiniteDimensional ℝ E]

lemma translationVariation_observation_smooth (s : Finset PlaneTest) :
    ContDiff ℝ ∞ (fun t => jetObservations s (translationVariation a u.val t)) := by
  have he : (fun t => jetObservations s (translationVariation a u.val t)) =
      (fun t => jetObservations s (constJetCLM (complexSlope a t))+
        jetObservations s (jetTranslate t u.val-u.val)) := by
    funext t
    rw [←map_add]
    apply congrArg (jetObservations s)
    change constJet (t • a)+jetTranslate t u.val-u.val = constJet (t • a)+(jetTranslate t u.val-u.val)
    abel
  rw [he]
  exact ((jetObservations s).contDiff.comp ((constJetCLM (E := E)).contDiff.comp
    (complexSlope a).contDiff)).add (jetObservations_translation_smooth_bp240 s u.val)

lemma freeTranslation_observation_smoothAt (s : Finset PlaneTest) :
    ContDiffAt ℝ ∞ (fun t => subspaceObservations (freeModel (E := E) (Metric.closedBall (0:ℂ) S)) s
      (freeTranslation hRS a u t)) 0 := by
  apply (translationVariation_observation_smooth a u s).contDiffAt.congr_of_eventuallyEq
  filter_upwards [freeTranslation_near hRS a u] with t ht
  exact congrArg (jetObservations s) ht

end HolderCompletion

end

end HigherDimensionalBallPacking.Rigidity
end

end OAI
end

section
-- module Solutions.OAIQ240_BP.BallPacking_Fredholm_TranslationContinuity
attribute [-instance] _root_.OAI.PackingSufficiencySupport.Hamiltonian.flatProduct_chartedSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace HigherDimensionalBallPacking.Rigidity.HolderCompletion
open scoped ContDiff Topology BoundedContinuousFunction
open Set Function Filter
section
section BilinearLimit
variable {T X Y Z : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y] [NormedAddCommGroup Z] [NormedSpace ℝ Z]
lemma bilinear_tendsto_zero_of_bounded (B : X →L[ℝ] Y →L[ℝ] Z) {l : Filter T}
    {A : T → X} (hA : Tendsto A l (𝓝 0)) (V : T → Y) (M : ℝ) (hM : ∀ t, ‖V t‖≤M) :
    Tendsto (fun t => B (A t) (V t)) l (𝓝 0) := by
  have hbound (t : T) : ‖B (A t) (V t)‖≤‖B‖*‖A t‖*M :=
    (B.le_opNorm₂ _ _).trans (mul_le_mul_of_nonneg_left (hM t) (by positivity))
  have hl : Tendsto (fun t => ‖B‖*‖A t‖*M) l (𝓝 0) := by
    simpa only [norm_zero,mul_zero,zero_mul] using (tendsto_const_nhds.mul hA.norm).mul_const M
  exact squeeze_zero_norm hbound hl
end BilinearLimit

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]

attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.tcInst1
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.tcInst2
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.tcInst3
local instance tcInst4_r4a87a2_1 : NormedSpace ℝ (COne ℂ E) := inferInstance
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.tcInst5
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.tcInst6
local instance tcInst7_r4a87a2_1 : NormedAddCommGroup (COne ℂ (E →L[ℝ] E)) := inferInstance
local instance tcInst8_r4a87a2_1 : NormedSpace ℝ (COne ℂ (E →L[ℝ] E)) := inferInstance
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.tcInst9
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.tcInst10
omit [CompleteSpace E] in
lemma translationError_value [CompleteSpace E] (A : COne ℂ (E →L[ℝ] E)) (a : E) (u : COne ℂ E) (t z : ℂ) :
    valueCLM _ (translationError A a u t) z =
      (cValue A (z+t)-cValue A z) (a+cDeriv u (z+t) 1) := rfl

omit [CompleteSpace E] in
lemma translation_second_factor_bound [CompleteSpace E] (a : E) (u : COne ℂ E) (t : ℂ) :
    ‖const (X := ℂ) ((1:ℝ)/3) a+holderTranslate t (jetDirection 1 u)‖ ≤
      ‖const (X := ℂ) ((1:ℝ)/3) a‖+‖jetDirection 1 u‖ := by
  have ht : ‖holderTranslate t (jetDirection 1 u)‖ ≤ ‖jetDirection 1 u‖ := holderTranslate_norm_le t (jetDirection 1 u)
  exact (norm_add_le (const (X := ℂ) ((1:ℝ)/3) a) (holderTranslate t (jetDirection 1 u))).trans
    (add_le_add le_rfl ht)

lemma translationError_tendsto (A : COne ℂ (E →L[ℝ] E)) (a : E) (u : COne ℂ E) :
    Tendsto (translationError A a u) (𝓝 0) (𝓝 0) := by
  have hA : Tendsto (fun t => holderTranslate t (jetValueCLM _ A)-jetValueCLM _ A) (𝓝 0) (𝓝 0) := by
    simpa only [sub_self] using (jetValue_translate_tendsto_bp240 A).sub_const (jetValueCLM _ A)
  exact bilinear_tendsto_zero_of_bounded
    (bilinCLM (X := ℂ) (α := (1:ℝ)/3) (ContinuousLinearMap.apply (E := E) ℝ E).flip) hA
    (fun t => const _ a+holderTranslate t (jetDirection 1 u))
    (‖const (X := ℂ) ((1:ℝ)/3) a‖+‖jetDirection 1 u‖) (translation_second_factor_bound a u)

omit [CompleteSpace E] in
lemma translation_CR_algebra [CompleteSpace E] (A0 A1 : E →L[ℝ] E) (a dx0 dy0 dx1 dy1 : E)
    (h0 : Complex.I • a+dy0=A0 (a+dx0)) (h1 : Complex.I • a+dy1=A1 (a+dx1)) :
    (dy1-dy0)-A0 (dx1-dx0)=(A1-A0) (a+dx1) := by
  rw [map_sub,sub_apply,map_add,map_add]
  rw [map_add] at h0 h1
  calc
    _ = (Complex.I • a+dy1)-(Complex.I • a+dy0)-A0 dx1+A0 dx0 := by abel
    _ = _ := by rw [h1,h0]; abel

variable {R S : ℝ} (hRS : R+1 ≤ S) (a : E)
  (u : freeModel (E := E) (Metric.closedBall (0:ℂ) R))
  (A : COne ℂ (E →L[ℝ] E))
  (hA : ∀ z ∉ Metric.closedBall (0:ℂ) S, cValue A z=complexI (E := E))
  (hcr : ∀ z, Complex.I • a+cDeriv u.val z Complex.I = cValue A z (a+cDeriv u.val z 1))

local instance tcInst11_r4a87a2_1 : NormedAddCommGroup (freeModel (E := E) (Metric.closedBall (0:ℂ) S)) := inferInstance
local instance tcInst12_r4a87a2_1 : NormedSpace ℝ (freeModel (E := E) (Metric.closedBall (0:ℂ) S)) := inferInstance
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.tcInst13
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.tcInst14
include hcr in
lemma freeTranslation_principal_near :
    ∀ᶠ t in 𝓝 (0:ℂ),
      (freePrincipal (jetValueCLM _ A) hA (freeTranslation hRS a u t)).val=translationError A a u.val t := by
  filter_upwards [freeTranslation_near hRS a u] with t ht
  apply value_ext
  intro z
  have hv := freePrincipal_value (jetValueCLM _ A) hA (freeTranslation hRS a u t) z
  have he : cDeriv (freeTranslation hRS a u t).val z = cDeriv u.val (z+t)-cDeriv u.val z :=
    (congrArg (fun w : COne ℂ E => cDeriv w z) ht).trans (translationVariation_deriv a u.val t z)
  have hh := congrArg (fun L : ℂ →L[ℝ] E => L Complex.I-cValue A z (L 1)) he
  apply hv.trans (hh.trans _)
  exact (translation_CR_algebra (cValue A z) (cValue A (z+t)) a
    (cDeriv u.val z 1) (cDeriv u.val z Complex.I)
    (cDeriv u.val (z+t) 1) (cDeriv u.val (z+t) Complex.I) (hcr z) (hcr (z+t))).trans
      (translationError_value A a u.val t z).symm

include hcr in
lemma freeTranslation_principal_tendsto :
    Tendsto (fun t => freePrincipal (jetValueCLM _ A) hA (freeTranslation hRS a u t)) (𝓝 0) (𝓝 0) := by
  have heq : (fun t => (freePrincipal (jetValueCLM _ A) hA (freeTranslation hRS a u t)).val) =ᶠ[𝓝 0]
      translationError A a u.val := freeTranslation_principal_near hRS a u A hA hcr
  have hh : Tendsto (fun t => (freePrincipal (jetValueCLM _ A) hA (freeTranslation hRS a u t)).val)
      (𝓝 0) (𝓝 (0 : HMap ℂ E)) :=
    (translationError_tendsto A a u.val).congr' heq.symm
  exact tendsto_subtype_rng.mpr hh

variable [FiniteDimensional ℝ E]
include hcr in
lemma elliptic_freeTranslation_continuous
    (hP : (freePrincipal (jetValueCLM _ A) hA).IsFredholm) :
    ContinuousAt (freeTranslation hRS a u) 0 := by
  obtain ⟨s,L,hL⟩ := exists_jet_fredholm_observations
    (freeModel (E := E) (Metric.closedBall (0:ℂ) S)) (freePrincipal (jetValueCLM _ A) hA) hP
  have hQ := (freeTranslation_observation_smoothAt hRS a u s).continuousAt
  have hQt : Tendsto (fun t => subspaceObservations (freeModel (E := E) (Metric.closedBall (0:ℂ) S)) s
      (freeTranslation hRS a u t)) (𝓝 0) (𝓝 0) := by
    simpa only [freeTranslation_zero_bp240,map_zero] using hQ.tendsto
  have hb := (freeTranslation_principal_tendsto hRS a u A hA hcr).prodMk_nhds hQt
  have hh := (L.continuous.tendsto (0,0)).comp hb
  have he (t : ℂ) : L (freePrincipal (jetValueCLM _ A) hA (freeTranslation hRS a u t),
      subspaceObservations (freeModel (E := E) (Metric.closedBall (0:ℂ) S)) s (freeTranslation hRS a u t)) =
      freeTranslation hRS a u t := hL _
  change Tendsto (freeTranslation hRS a u) _ _
  simpa only [Function.comp_def,he,freeTranslation_zero_bp240,Prod.mk_zero_zero,map_zero] using hh

end

end HigherDimensionalBallPacking.Rigidity.HolderCompletion

namespace HigherDimensionalBallPacking.Rigidity.HolderCompletion
open scoped ContDiff Topology BoundedContinuousFunction
open Set Function Filter
section
variable {n : ℕ}
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.srInst1
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.srInst2
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.srInst3
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.srInst4
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.srInst5
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.srInst6
variable {J : Phase n → End n} (hJ : ContDiff ℝ ∞ J) (hc : ∀ x, Compatible (J x)) {B : ℝ}
  (hstd : ∀ x, B<‖x‖ → J x=standardJ n) (b : ContDiffBump (0:ℂ)) (p q : Phase n)
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.srInst10
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.srInst11
variable (w : freeModel (E := Phase n) (Metric.closedBall (0:ℂ) b.rOut)) {R : ℝ}
  (hRS : R+1≤b.rOut) (hsupp : w.val ∈ freeModel (E := Phase n) (Metric.closedBall (0:ℂ) R))
  (hesc : FreeEscapeNeighborhood b p (markedSlope p q w.val) w.val B)
  (hcr : ∀ z, fderiv ℝ (markedCurve p q w.val) z Complex.I =
    J (markedCurve p q w.val z) (fderiv ℝ (markedCurve p q w.val) z 1))

attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.srInst7
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.srInst8
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.srInst9
include hJ hstd hc hesc hcr hRS hsupp in
lemma regularityTranslation_continuous_bp240_oai : ContinuousAt (regularityTranslation b p q w hRS hsupp) 0 := by
  let A := completedStructureJet hJ hstd p q w.val
  have he := free_escape_base p q b w hesc
  have hA : ∀ z ∉ Metric.closedBall (0:ℂ) b.rOut, cValue A z=complexI (E := Phase n) :=
    fun z hz => hstd _ (he z hz)
  have hcr' : ∀ z, Complex.I • markedSlope p q w.val+cDeriv w.val z Complex.I =
      cValue A z (markedSlope p q w.val+cDeriv w.val z 1) := by
    intro z
    simpa only [A,completedStructureJet_value,markedCurve_fderiv,add_apply,complexSlope_apply,one_smul] using hcr z
  have hp : (freePrincipal (jetValueCLM _ A) hA).IsFredholm :=
    completedFreePrincipal_fredholm_bp240 hJ hc hstd p q w.val (isCompact_closedBall (0:ℂ) b.rOut) he
  exact elliptic_freeTranslation_continuous hRS (markedSlope p q w.val) ⟨w.val,hsupp⟩ A hA hcr' hp

end

end HigherDimensionalBallPacking.Rigidity.HolderCompletion
end

end OAI
end

theorem solution : type_of% @OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.regularityTranslation_continuous_bp240_oai := @OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.regularityTranslation_continuous_bp240_oai
