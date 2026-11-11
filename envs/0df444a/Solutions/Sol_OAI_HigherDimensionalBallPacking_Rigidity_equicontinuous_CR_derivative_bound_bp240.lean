-- Prove2me | solution 1 for OAI.HigherDimensionalBallPacking.Rigidity.equicontinuous_CR_derivative_bound_bp240
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T01:50:47.787194+00:00
-- url     : https://prove2.me/submissions/a1b2c67f-6590-4f8f-afdf-8a161587b95e

import Mathlib
import Definitions.Def_BallPacking
import Definitions.Def_OAIQ240Bp019
import Theorems.Thm_OAI_HigherDimensionalBallPacking_Rigidity_HolderCompletion_compatibleFrame_intertwine_bp240
import Theorems.Thm_OAI_HigherDimensionalBallPacking_Rigidity_HolderCompletion_compatibleFrame_inverse_left_bp240

section
-- module Solutions.OAIQ240_BP.BallPacking_Holder_BanachSpace
attribute [-instance] _root_.OAI.PackingSufficiencySupport.Hamiltonian.flatProduct_chartedSpace
attribute [-simp] _root_.OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.affineJetDeriv_value _root_.OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.affineJetSuperpose_value _root_.OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.affineJetValue_value _root_.OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.coefficient_value _root_.OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.ofBoundedCThree_deriv _root_.OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.ofBoundedCThree_value _root_.OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.structureAlongDeriv_value _root_.OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.structureAlong_value _root_.OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.superposeDeriv_value _root_.OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.superpose_value _root_.OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.truncatedCoefficient_value _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.infinity_end_count _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.sqrt_sq_complex
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace HigherDimensionalBallPacking.Rigidity.HolderCompletion
open scoped BoundedContinuousFunction Topology ContDiff
open Set Filter
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

namespace BoundedCThree
variable {f : E → F}

lemma norm_sub_le (hf : BoundedCThree f) (x y : E) :
    ‖f x - f y‖ ≤ hf.bound * ‖x-y‖ :=
  norm_sub_le_of_deriv_bound (hf.smooth.differentiable (by simp)) hf.norm_fderiv_le x y

end BoundedCThree

end HigherDimensionalBallPacking.Rigidity.HolderCompletion
end

end OAI
end

section
-- module Solutions.OAIQ240_BP.BallPacking_Holder_MarkedFrame
attribute [-instance] _root_.OAI.PackingSufficiencySupport.Hamiltonian.flatProduct_chartedSpace
attribute [-simp] _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.infinity_end_count _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.sqrt_sq_complex
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace HigherDimensionalBallPacking.Rigidity.HolderCompletion

open scoped ContDiff Topology BoundedContinuousFunction
open Set Filter
variable {X E : Type*} [MetricSpace X] [NormedAddCommGroup E] [NormedSpace ℝ E]

lemma exists_small_third_scale {A : ℝ} (hA : 0 < A) (L : ℝ) :
    ∃ s > 0, L*s^((2:ℝ)/3) < A := by
  have ht : Tendsto (fun s : ℝ => L*s^((2:ℝ)/3)) (𝓝[>] 0) (𝓝 0) := by
    have h := (Real.continuousAt_rpow_const (0:ℝ) ((2:ℝ)/3) (Or.inr (by norm_num))).const_mul L
    simpa using h.tendsto.mono_left nhdsWithin_le_nhds
  have he : ∀ᶠ s : ℝ in 𝓝[>] 0, L*s^((2:ℝ)/3) < A := ht.eventually (gt_mem_nhds hA)
  have hh : ∀ᶠ s : ℝ in 𝓝[>] 0, 0 < s ∧ L*s^((2:ℝ)/3) < A := by
    filter_upwards [self_mem_nhdsWithin,he] with s hs h
    exact ⟨hs,h⟩
  exact hh.exists

attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.holderCompInst1
local instance holderCompInst2_r617f9a_1 : NormedSpace ℝ (HMap X E) := inferInstance
lemma holder_small_of_small_value {L ε : ℝ} (hL : 0 ≤ L) (hε : 0 < ε) :
    ∃ δ > 0, ∀ u : HMap X E,
      (∀ x, ‖valueCLM _ u x‖ ≤ δ) →
      (∀ x y, ‖valueCLM _ u x-valueCLM _ u y‖ ≤ L*dist x y) → ‖u‖ < ε := by
  obtain ⟨s,hs,hscale⟩ := exists_small_third_scale (half_pos hε) L
  let δ : ℝ := min (ε/2) (ε/4*s^((1:ℝ)/3))
  have hδ : 0 < δ := lt_min (half_pos hε) (by positivity)
  refine ⟨δ,hδ,fun u hb hl => ?_⟩
  have hlarge : 2*δ ≤ ε/2*s^((1:ℝ)/3) := by
    have hh : δ ≤ ε/4*s^((1:ℝ)/3) := min_le_right _ _
    linarith
  have hh := third_interpolation hδ.le hL (half_pos hε).le hs hb hl hscale.le hlarge
  have hn : ‖u‖ ≤ ε/2 := (norm_le_of_bounds u hδ.le (half_pos hε).le hb hh).trans
    (max_le (min_le_left _ _) le_rfl)
  exact hn.trans_lt (half_lt_self hε)



end HigherDimensionalBallPacking.Rigidity.HolderCompletion
end

end OAI
end

section
-- module Solutions.OAIQ240_BP.BallPacking_Compactness_GradientBounds
attribute [-instance] _root_.OAI.PackingSufficiencySupport.Hamiltonian.flatProduct_chartedSpace
attribute [-simp] _root_.OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.affineJetDeriv_value _root_.OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.affineJetSuperpose_value _root_.OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.affineJetValue_value _root_.OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.compactPerturbationJet_value _root_.OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.compatibleFrameJet_value _root_.OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.compatibleInverseJet_value _root_.OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.completedDX_value _root_.OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.completedFrameJet_value _root_.OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.completedInverseJet_value _root_.OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.completedPrincipal_value _root_.OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.completedQ_value _root_.OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.completedStructureJet_value _root_.OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.curveMarkCoefficientHolder_value _root_.OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.curveZeroOrderHolder_value _root_.OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.frameCRCoefficient_value _root_.OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.freePrincipal_value _root_.OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.freeSum_deriv _root_.OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.freeSum_value _root_.OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.freeZeroOrder_value _root_.OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.holderTranslate_value _root_.OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.jetTranslate_deriv _root_.OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.jetTranslate_value _root_.OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.jetZeroOrder_value _root_.OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.markedDerivEval_value _root_.OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.markedDerivativeVariation_value _root_.OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.markedEval_value _root_.OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.markedFiniteCorrection_value _root_.OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.markedPrincipal_value _root_.OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.markedVariation_value _root_.OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.markedZeroOrder_value _root_.OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.principalCR_value _root_.OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.smoothAlongJet_value _root_.OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.smoothMarkedPrincipal_value _root_.OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.supportedEval_value _root_.OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.supportedFieldAction_value _root_.OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.truncatedCoefficient_value _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.infinity_end_count _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.sqrt_sq_complex
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

attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.scsInst1
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.scsInst2
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.scsInst3
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.scsInst4
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.scsInst5
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.scsInst6
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.scsInst7
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.scsInst8
omit [CompleteSpace E] in
lemma holderCoefficientAction_norm_le (A : HMap ℂ (E →L[ℝ] E)) (v : HMap ℂ E) :
    ‖holderCoefficientAction A v‖≤
      ‖bilinCLM (X := ℂ) (α := (1:ℝ)/3) (ContinuousLinearMap.apply (E := E) ℝ E).flip‖*‖A‖*‖v‖ :=
  (bilinCLM (X := ℂ) (α := (1:ℝ)/3) (ContinuousLinearMap.apply (E := E) ℝ E).flip).le_opNorm₂ A v

lemma compact_zeroMarked_schauder {K : Set ℂ} (hK : IsCompact K) (v : COne ℂ E)
    (hv : cValue v 0=0) (hs : standardJetCR v∈supportedHolder K) :
    ‖v‖≤‖standardHolderInverse (E := E) hK‖*‖standardJetCR v‖ := by
  let g : supportedHolder (E := E) K := ⟨standardJetCR v,hs⟩
  have he : standardHolderInverse hK g=v := standardJetCR_injective_zeroMarked
    (standardHolderInverse_zero hK g) hv (standardHolderInverse_residual hK g)
  have hh := (standardHolderInverse hK).le_opNorm g
  rw [he] at hh
  exact hh

lemma scalar_absorption {D B N a v f : ℝ} (hD : 0≤D) (hB : 0≤B) (hN : 0≤N)
    (hf : 0≤f) (hv : 0≤v) (ha : a≤(2*(D*B*N+1))⁻¹)
    (hb : v≤D*((B*a*N)*v+f)) : v≤(2*D+1)*f := by
  have ht : D*B*N*(2*(D*B*N+1))⁻¹≤(1:ℝ)/2 := by
    rw [←div_eq_mul_inv]
    apply (div_le_iff₀ (by positivity : 0<2*(D*B*N+1))).mpr
    nlinarith
  have hs : D*B*N*a≤(1:ℝ)/2 :=
    (mul_le_mul_of_nonneg_left ha (by positivity)).trans ht
  have hh := mul_le_mul_of_nonneg_right hs hv
  nlinarith

lemma small_coefficient_schauder {K : Set ℂ} (hK : IsCompact K) :
    ∃ ε C : ℝ,0<ε ∧ 0<C ∧ ∀ (v : COne ℂ E),cValue v 0=0 →
      standardJetCR v∈supportedHolder K →∀ (A : HMap ℂ (E →L[ℝ] E)),‖A‖≤ε →
      ∀ f : HMap ℂ E,standardJetCR v=holderCoefficientAction A (jetDirectional 1 v)+f →
        ‖v‖≤C*‖f‖ := by
  let D := ‖standardHolderInverse (E := E) hK‖
  let B := ‖bilinCLM (X := ℂ) (α := (1:ℝ)/3) (ContinuousLinearMap.apply (E := E) ℝ E).flip‖
  let N := ‖jetDirectional (E := E) 1‖
  have hD : 0≤D := norm_nonneg (standardHolderInverse (E := E) hK)
  have hB : 0≤B := norm_nonneg (bilinCLM (X := ℂ) (α := (1:ℝ)/3)
    (ContinuousLinearMap.apply (E := E) ℝ E).flip)
  have hN : 0≤N := norm_nonneg (jetDirectional (E := E) 1)
  have hpos : 0<(2*(D*B*N+1))⁻¹ := by positivity
  refine ⟨(2*(D*B*N+1))⁻¹,2*D+1,hpos,by positivity,?_⟩
  intro v hv hs A hA f he
  have hi := compact_zeroMarked_schauder hK v hv hs
  have hp := holderCoefficientAction_norm_le A (jetDirectional 1 v)
  have hd := (jetDirectional (E := E) 1).le_opNorm v
  have hm := mul_le_mul_of_nonneg_left hd (by positivity : 0≤B*‖A‖)
  have hb : ‖holderCoefficientAction A (jetDirectional 1 v)‖≤(B*‖A‖*N)*‖v‖ :=
    hp.trans (hm.trans_eq (by ring))
  have hres : ‖standardJetCR v‖≤(B*‖A‖*N)*‖v‖+‖f‖ := by
    rw [he]
    exact (norm_add_le _ _).trans (add_le_add hb (le_refl _))
  exact scalar_absorption hD hB hN (norm_nonneg f) (norm_nonneg v) hA
    (hi.trans (mul_le_mul_of_nonneg_left hres hD))


end
section
open scoped ContDiff Topology BoundedContinuousFunction
open Set Filter
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]

variable (b : ContDiffBump (0:ℂ)) {u : ℂ → E} (hu : ContDiff ℝ ∞ u)

omit [CompleteSpace E] in
lemma cutoffCurveJet_deriv (z h : ℂ) :
    cDeriv (cutoffCurveJet b hu) z h=
      (fderiv ℝ b z h) • u z+b z • fderiv ℝ u z h := by
  rw [←c_fderiv]
  change fderiv ℝ (fun z => b z • u z) z h=_
  rw [fderiv_fun_smul (b.contDiff.differentiable (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top : (∞ : WithTop ℕ∞) ≠ 0) z) (hu.differentiable (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top : (∞ : WithTop ℕ∞) ≠ 0) z)]
  simp only [add_apply,smul_apply,ContinuousLinearMap.smulRight_apply]
  exact add_comm _ _

omit [CompleteSpace E] in
lemma cutoffCurveJet_zero (h0 : u 0=0) : cValue (cutoffCurveJet b hu) 0=0 := by
  rw [cutoffCurveJet_value,h0,smul_zero]

attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.ccInst1
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.ccInst2
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.ccInst3
local instance ccInst4_r617f9a_1 : NormedSpace ℝ (COne ℂ E) := inferInstance
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.ccInst5
local instance ccInst6_r617f9a_1 : NormedSpace ℝ (HMap ℂ E) := inferInstance
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.ccInst7
local instance ccInst8_r617f9a_1 : NormedSpace ℝ (HMap ℂ (E →L[ℝ] E)) := inferInstance
omit [CompleteSpace E] in
lemma cutoffCurveJet_supported : standardJetCR (cutoffCurveJet b hu)∈
    supportedHolder (Metric.closedBall (0:ℂ) b.rOut) := by
  apply (mem_supportedHolder _ _).mpr
  intro z hz
  have hb : z∉tsupport b := by
    rw [b.tsupport_eq]
    exact hz
  have hb0 := image_eq_zero_of_notMem_tsupport hb
  have hbd := fderiv_of_notMem_tsupport ℝ hb
  rw [standardJetCR_value]
  change cDeriv (cutoffCurveJet b hu) z Complex.I-Complex.I • cDeriv (cutoffCurveJet b hu) z 1=0
  rw [cutoffCurveJet_deriv,cutoffCurveJet_deriv,hbd,hb0]
  simp

omit [CompleteSpace E] in
lemma cutoffCurveJet_CR {A : ℂ → E →L[ℝ] E}
    (hcr : ∀ z,b z≠0 → fderiv ℝ u z Complex.I-Complex.I • fderiv ℝ u z 1=A z (fderiv ℝ u z 1))
    (ac : HMap ℂ (E →L[ℝ] E)) (hac : ∀ z,b z≠0 → valueCLM _ ac z=A z)
    (f : HMap ℂ E) (hf : ∀ z,valueCLM _ f z=
      (fderiv ℝ b z Complex.I) • u z-Complex.I • ((fderiv ℝ b z 1) • u z)-
        valueCLM _ ac z ((fderiv ℝ b z 1) • u z)) :
    standardJetCR (cutoffCurveJet b hu)=
      holderCoefficientAction ac (jetDirectional 1 (cutoffCurveJet b hu))+f := by
  apply value_ext
  intro z
  rw [standardJetCR_value]
  change cDeriv (cutoffCurveJet b hu) z Complex.I-Complex.I • cDeriv (cutoffCurveJet b hu) z 1=
    valueCLM _ ac z (cDeriv (cutoffCurveJet b hu) z 1)+valueCLM _ f z
  rw [cutoffCurveJet_deriv,cutoffCurveJet_deriv,hf]
  have he : b z • (fderiv ℝ u z Complex.I-Complex.I • fderiv ℝ u z 1)=
      valueCLM _ ac z (b z • fderiv ℝ u z 1) := by
    by_cases hb : b z=0
    · simp [hb]
    · rw [hac z hb,hcr z hb,map_smul]
  rw [map_add]
  simp only [smul_add,smul_sub] at *
  rw [smul_comm Complex.I (b z)]
  rw [←he]
  abel

lemma small_value_elliptic_estimate {K : Set ℂ} (hK : IsCompact K)
    {L M η : ℝ} (hL : 0≤L) (hM : 0≤M) (hη : 0<η) :
    ∃ δ : ℝ,0<δ ∧ ∀ (v : COne ℂ E),cValue v 0=0 →
      standardJetCR v∈supportedHolder K → ∀ (A : HMap ℂ (E →L[ℝ] E)) (f : HMap ℂ E),
      (∀ z,‖valueCLM _ A z‖≤δ) → (∀ x y,‖valueCLM _ A x-valueCLM _ A y‖≤L*dist x y) →
      (∀ z,‖valueCLM _ f z‖≤δ) → (∀ x y,‖valueCLM _ f x-valueCLM _ f y‖≤M*dist x y) →
      standardJetCR v=holderCoefficientAction A (jetDirectional 1 v)+f → ‖v‖<η := by
  obtain ⟨ε,C,hε,hC,hest⟩ := small_coefficient_schauder (E := E) hK
  obtain ⟨d,hd,hda⟩ := holder_small_of_small_value (E := E →L[ℝ] E) (X := ℂ) hL hε
  obtain ⟨e,he,hef⟩ := holder_small_of_small_value (E := E) (X := ℂ) hM (div_pos hη hC)
  refine ⟨min d e,lt_min hd he,?_⟩
  intro v hv hs A f hA hAL hf hfL hres
  have hAn : ‖A‖<ε := hda A (fun z => (hA z).trans (min_le_left _ _)) hAL
  have hfn : ‖f‖<η/C := hef f (fun z => (hf z).trans (min_le_right _ _)) hfL
  have hh := hest v hv hs A hAn.le f hres
  have ht : C*‖f‖<η := by
    have h := (lt_div_iff₀ hC).mp hfn
    simpa only [mul_comm] using h
  exact hh.trans_lt ht


end
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

lemma clm_pair_bounds {A : X → E →L[ℝ] F} {u : X → E} {B C L M : ℝ}
    (hB : 0≤B) (_hC : 0≤C) (hL : 0≤L) (_hM : 0≤M)
    (hA : ∀ z,‖A z‖≤B) (hu : ∀ z,‖u z‖≤C)
    (hAL : ∀ x y,‖A x-A y‖≤L*dist x y)
    (huL : ∀ x y,‖u x-u y‖≤M*dist x y) :
    (∀ z,‖A z (u z)‖≤B*C) ∧
    (∀ x y,‖A x (u x)-A y (u y)‖≤(B*M+L*C)*dist x y) := by
  constructor
  · intro z
    exact ((A z).le_opNorm _).trans (mul_le_mul (hA z) (hu z) (norm_nonneg _) hB)
  · intro x y
    apply (clm_pair_difference _ _ _ _).trans
    have h1 := mul_le_mul (hA x) (huL x y) (norm_nonneg _) hB
    have h2 := mul_le_mul (hAL x y) (hu y) (norm_nonneg _) (by positivity : 0≤L*dist x y)
    exact (add_le_add h1 h2).trans_eq (by ring)

lemma cutoff_forcing_bounds {u : X → E} {A C D : X → E →L[ℝ] E}
    {δ H L B : ℝ} (hδ : 0≤δ) (hδ1 : δ≤1) (hH : 0≤H) (hL : 0≤L) (hB : 0≤B)
    (hu : ∀ z,‖u z‖≤δ) (huL : ∀ x y,‖u x-u y‖≤H*dist x y)
    (hA : ∀ z,‖A z‖≤L*δ) (hAL : ∀ x y,‖A x-A y‖≤(L*H)*dist x y)
    (hC : ∀ z,‖C z‖≤B) (hCL : ∀ x y,‖C x-C y‖≤B*dist x y)
    (hD : ∀ z,‖D z‖≤B) (hDL : ∀ x y,‖D x-D y‖≤B*dist x y) :
    (∀ z,‖C z (u z)-A z (D z (u z))‖≤((1+L)*B)*δ) ∧
    (∀ x y,‖(C x (u x)-A x (D x (u x)))-(C y (u y)-A y (D y (u y)))‖≤
      (B*(H+1)+L*(B*(H+1))+L*H*B)*dist x y) := by
  have hHL : 0≤B*(H+1) := by positivity
  have hbδ : B*δ≤B := by nlinarith
  have hstep : B*H+B*δ≤B*(H+1) := by nlinarith
  obtain ⟨hc,hcl⟩ := clm_pair_bounds hB hδ hB hH hC hu hCL huL
  obtain ⟨hd,hdl⟩ := clm_pair_bounds hB hδ hB hH hD hu hDL huL
  have hAu : ∀ z,‖A z‖≤L := fun z => (hA z).trans (by nlinarith)
  have hDu : ∀ z,‖D z (u z)‖≤B := fun z => (hd z).trans hbδ
  have hDul : ∀ x y,‖D x (u x)-D y (u y)‖≤B*(H+1)*dist x y :=
    fun x y => (hdl x y).trans (mul_le_mul_of_nonneg_right hstep (dist_nonneg))
  obtain ⟨ _,hal⟩ := clm_pair_bounds hL hB (mul_nonneg hL hH) hHL hAu hDu hAL hDul
  refine ⟨?_,?_⟩
  · intro z
    have hh : ‖A z (D z (u z))‖≤L*(B*δ) :=
      ((A z).le_opNorm _).trans (mul_le_mul (hAu z) (hd z) (norm_nonneg _) hL)
    exact (norm_sub_le _ _).trans ((add_le_add (hc z) hh).trans_eq (by ring))
  · intro x y
    have he : (C x (u x)-A x (D x (u x)))-(C y (u y)-A y (D y (u y)))=
        (C x (u x)-C y (u y))-(A x (D x (u x))-A y (D y (u y))) := by abel
    rw [he]
    have hc' := (hcl x y).trans (mul_le_mul_of_nonneg_right hstep (dist_nonneg))
    exact (norm_sub_le _ _).trans ((add_le_add hc' (hal x y)).trans_eq (by ring))


end
section
open scoped ContDiff Topology BoundedContinuousFunction
open Set Filter
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
variable (b : ContDiffBump (0:ℂ))

attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.ctInst1
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.ctInst2
omit [CompleteSpace E] in
lemma cutoffTransport_smooth (h : ℂ) : ContDiff ℝ ∞ (cutoffTransport (E := E) b h) := by
  exact ((b.contDiff.fderiv_right (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top : (∞ : WithTop ℕ∞)+1≤∞)).clm_apply contDiff_const).smul contDiff_const

omit [CompleteSpace E] in
lemma cutoffTransport_compact (h : ℂ) : HasCompactSupport (cutoffTransport (E := E) b h) :=
  (b.hasCompactSupport.fderiv_apply ℝ h).smul_right

omit [CompleteSpace E] in
lemma cutoffCommute_smooth : ContDiff ℝ ∞ (cutoffCommute (E := E) b) :=
  (cutoffTransport_smooth b Complex.I).sub (contDiff_const.clm_comp (cutoffTransport_smooth b 1))

omit [CompleteSpace E] in
lemma cutoffCommute_compact : HasCompactSupport (cutoffCommute (E := E) b) := by
  apply HasCompactSupport.of_support_subset_isCompact b.hasCompactSupport
  intro z hz
  by_contra hn
  apply hz
  have hd := fderiv_of_notMem_tsupport ℝ hn
  simp only [cutoffCommute,cutoffTransport,hd,zero_apply,zero_smul,
    ContinuousLinearMap.comp_zero,sub_zero]

omit [CompleteSpace E] in
lemma cutoff_transport_bounds : ∃ B : ℝ,0<B ∧
    (∀ z,‖cutoffTransport (E := E) b 1 z‖≤B) ∧
    (∀ x y,‖cutoffTransport (E := E) b 1 x-cutoffTransport b 1 y‖≤B*dist x y) ∧
    (∀ z,‖cutoffCommute (E := E) b z‖≤B) ∧
    (∀ x y,‖cutoffCommute (E := E) b x-cutoffCommute b y‖≤B*dist x y) := by
  have hd := boundedCThree_of_compactSupport (cutoffTransport_smooth (E := E) b 1) (cutoffTransport_compact b 1)
  have hc := boundedCThree_of_compactSupport (cutoffCommute_smooth (E := E) b) (cutoffCommute_compact b)
  let B := hd.bound+hc.bound+1
  have hB : 0<B := by dsimp [B] <;> linarith [hd.bound_nonneg,hc.bound_nonneg]
  have hdb : hd.bound≤B := by dsimp [B] <;> linarith [hc.bound_nonneg]
  have hcb : hc.bound≤B := by dsimp [B] <;> linarith [hd.bound_nonneg]
  refine ⟨B,hB,fun z => (hd.norm_le z).trans hdb,?_,fun z => (hc.norm_le z).trans hcb,?_⟩
  · intro x y
    exact (hd.norm_sub_le x y).trans (by rw [dist_eq_norm]; exact mul_le_mul_of_nonneg_right hdb (norm_nonneg _))
  · intro x y
    exact (hc.norm_sub_le x y).trans (by rw [dist_eq_norm]; exact mul_le_mul_of_nonneg_right hcb (norm_nonneg _))


end
open scoped Topology BoundedContinuousFunction
open Set Filter



end HigherDimensionalBallPacking.Rigidity.HolderCompletion
end

end OAI
end

section
-- module Solutions.OAIQ240_BP.BallPacking_Compactness_JetCauchy
attribute [-instance] _root_.OAI.PackingSufficiencySupport.Hamiltonian.flatProduct_chartedSpace
attribute [-simp] _root_.OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.affineJetDeriv_value _root_.OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.affineJetSuperpose_value _root_.OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.affineJetValue_value _root_.OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.compactPerturbationJet_value _root_.OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.completedDX_value _root_.OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.completedFrameJet_value _root_.OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.completedInverseJet_value _root_.OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.completedPrincipal_value _root_.OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.completedQ_value _root_.OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.completedStructureJet_value _root_.OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.curveMarkCoefficientHolder_value _root_.OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.curveZeroOrderHolder_value _root_.OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.frameCRCoefficient_value _root_.OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.freePrincipal_value _root_.OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.freeSum_deriv _root_.OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.freeSum_value _root_.OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.freeZeroOrder_value _root_.OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.holderTranslate_value _root_.OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.jetTranslate_deriv _root_.OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.jetTranslate_value _root_.OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.jetZeroOrder_value _root_.OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.markedDerivEval_value _root_.OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.markedDerivativeVariation_value _root_.OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.markedEval_value _root_.OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.markedFiniteCorrection_value _root_.OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.markedPrincipal_value _root_.OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.markedVariation_value _root_.OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.markedZeroOrder_value _root_.OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.principalCR_value _root_.OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.smoothAlongJet_value _root_.OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.smoothMarkedPrincipal_value _root_.OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.supportedEval_value _root_.OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.supportedFieldAction_value _root_.OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.truncatedCoefficient_value _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.infinity_end_count _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.sqrt_sq_complex
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

lemma common_small_value_scale {L K d : ℝ} (hL : 0≤L) (hK : 0≤K) (hd : 0<d) :
    ∃ δ : ℝ,0<δ ∧ δ≤1 ∧ L*δ≤d ∧ K*δ≤d := by
  have hp : 0<L+K+1 := by linarith
  let δ := min 1 (d/(L+K+1))
  have hδ : 0<δ := lt_min zero_lt_one (div_pos hd hp)
  have hm : (L+K+1)*δ≤d := by
    have h := (le_div_iff₀ hp).mp (min_le_right 1 (d/(L+K+1)))
    simpa only [mul_comm] using h
  refine ⟨δ,hδ,min_le_left _ _,?_,?_⟩ <;> nlinarith

omit [CompleteSpace E] in
lemma cutoffCurveJet_deriv_zero (b : ContDiffBump (0:ℂ)) {u : ℂ → E}
    (hu : ContDiff ℝ ∞ u) (h0 : u 0=0) :
    cDeriv (cutoffCurveJet b hu) 0=fderiv ℝ u 0 := by
  ext h
  rw [cutoffCurveJet_deriv,h0,smul_zero,zero_add,
    b.one_of_mem_closedBall (Metric.mem_closedBall_self b.rIn_pos.le),one_smul]

attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.lsoInst1
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.lsoInst2
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.lsoInst3
local instance lsoInst4_r617f9a_1 : NormedSpace ℝ (COne ℂ E) := inferInstance
local instance lsoInst5_r617f9a_1 : NormedAddCommGroup (HMap ℂ E) := inferInstance
local instance lsoInst6_r617f9a_1 : NormedSpace ℝ (HMap ℂ E) := inferInstance
local instance lsoInst7_r617f9a_1 : NormedAddCommGroup (HMap ℂ (E →L[ℝ] E)) := inferInstance
local instance lsoInst8_r617f9a_1 : NormedSpace ℝ (HMap ℂ (E →L[ℝ] E)) := inferInstance
theorem bounded_cutoff_gradient_small (b : ContDiffBump (0:ℂ))
    {L H η : ℝ} (hL : 0≤L) (hH : 0≤H) (hη : 0<η) :
    ∃ δ : ℝ,0<δ ∧ ∀ (F : E → E →L[ℝ] E),Continuous F → F 0=0 →
      (∀ x y,‖F x-F y‖≤L*‖x-y‖) → ∀ u : ℂ → E,ContDiff ℝ ∞ u → u 0=0 →
      (∀ z,‖u z‖≤δ) → (∀ x y,‖u x-u y‖≤H*dist x y) →
      (∀ z,b z≠0 → fderiv ℝ u z Complex.I-Complex.I • fderiv ℝ u z 1=
        F (u z) (fderiv ℝ u z 1)) → ‖fderiv ℝ u 0‖<η := by
  obtain ⟨B,hB,hD,hDL,hC,hCL⟩ := cutoff_transport_bounds (E := E) b
  let M : ℝ := B*(H+1)+L*(B*(H+1))+L*H*B
  have hM : 0≤M := by dsimp [M] <;> positivity
  obtain ⟨d,hd,hsmall⟩ := small_value_elliptic_estimate (E := E)
    (isCompact_closedBall (0:ℂ) b.rOut) (mul_nonneg hL hH) hM hη
  obtain ⟨δ,hδ,hδ1,hδA,hδf⟩ := common_small_value_scale hL
    (by positivity : 0≤(1+L)*B) hd
  refine ⟨δ,hδ,?_⟩
  intro F hF hF0 hFL u hu h0 hub hul hcr
  let A : ℂ → E →L[ℝ] E := fun z => F (u z)
  have hAc : Continuous A := hF.comp hu.continuous
  have hAb : ∀ z,‖A z‖≤L*δ := by
    intro z
    have hh := hFL (u z) 0
    rw [hF0,sub_zero,sub_zero] at hh
    exact hh.trans (mul_le_mul_of_nonneg_left (hub z) hL)
  have hAl : ∀ x y,‖A x-A y‖≤(L*H)*dist x y := by
    intro x y
    exact (hFL (u x) (u y)).trans ((mul_le_mul_of_nonneg_left (hul x y) hL).trans_eq (by ring))
  let ac : HMap ℂ (E →L[ℝ] E) := ofBoundedLipschitz A hAc (L*δ) (L*H)
    (mul_nonneg hL hδ.le) (mul_nonneg hL hH) hAb hAl
  have hbds := cutoff_forcing_bounds hδ.le hδ1 hH hL hB.le hub hul hAb hAl hC hCL hD hDL
  let g : ℂ → E := fun z => cutoffCommute b z (u z)-A z (cutoffTransport b 1 z (u z))
  have hgc : Continuous g := ((cutoffCommute_smooth b).continuous.clm_apply hu.continuous).sub
    (hAc.clm_apply ((cutoffTransport_smooth b 1).continuous.clm_apply hu.continuous))
  let f : HMap ℂ E := ofBoundedLipschitz g hgc (((1+L)*B)*δ) M
    (by positivity) hM hbds.1 hbds.2
  have hAe : ∀ z,valueCLM _ ac z=A z := fun _ => rfl
  have hfe : ∀ z,valueCLM _ f z=g z := fun _ => rfl
  have heq : standardJetCR (cutoffCurveJet b hu)=
      holderCoefficientAction ac (jetDirectional 1 (cutoffCurveJet b hu))+f := by
    apply cutoffCurveJet_CR b hu hcr ac (fun z _ => hAe z) f
    intro z
    rw [hfe,hAe]
    exact rfl
  have hh := hsmall (cutoffCurveJet b hu) (cutoffCurveJet_zero b hu h0)
    (cutoffCurveJet_supported b hu) ac f (fun z => (hAb z).trans hδA) hAl
    (fun z => (hbds.1 z).trans hδf) hbds.2 heq
  have hder : ‖fderiv ℝ u 0‖≤‖cutoffCurveJet b hu‖ := by
    rw [←cutoffCurveJet_deriv_zero b hu h0]
    exact c_deriv_bound _ _
  exact hder.trans_lt hh


end
section
open scoped ContDiff Topology BoundedContinuousFunction
open Set Filter
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]

local instance legInst2_r617f9a_1 : NormedSpace ℝ (E →L[ℝ] E) := ContinuousLinearMap.toNormedSpace
omit [CompleteSpace E] in
lemma smooth_cutoff_local_bounds (b : ContDiffBump (0:ℂ)) {u : ℂ → E}
    (hu : ContDiff ℝ ∞ u) {R δ H : ℝ} (hR : b.rOut≤R) (hδ : 0≤δ) (hδ1 : δ≤1) (hH : 0≤H)
    (hb : ∀ z,‖z‖≤R → ‖u z‖≤δ) (hd : ∀ z,‖z‖≤R → ‖fderiv ℝ u z‖≤H) :
    ∃ K : ℝ,0≤K ∧ K=(boundedCThree_of_compactSupport b.contDiff b.hasCompactSupport).bound ∧
    (∀ z,‖b z • u z‖≤δ) ∧
    (∀ z,‖fderiv ℝ (fun z => b z • u z) z‖≤H+K) := by
  let hs := boundedCThree_of_compactSupport b.contDiff b.hasCompactSupport
  let K := hs.bound
  have hK : 0≤K := hs.bound_nonneg
  have hbn (z : ℂ) : ‖b z‖≤1 := by
    rw [Real.norm_eq_abs,abs_of_nonneg b.nonneg]
    exact b.le_one
  have hder (z : ℂ) : fderiv ℝ (fun z => b z • u z) z=
      b z • fderiv ℝ u z+(fderiv ℝ b z).smulRight (u z) :=
    fderiv_fun_smul (b.contDiff.differentiable (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top : (∞ : WithTop ℕ∞)≠0) z)
      (hu.differentiable (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top : (∞ : WithTop ℕ∞)≠0) z)
  have hzouts (z : ℂ) (hz : ¬‖z‖≤R) : b z=0 ∧ fderiv ℝ b z=0 := by
    have hn : z∉tsupport b := by
      rw [b.tsupport_eq,Metric.mem_closedBall,dist_zero_right]
      exact fun hh => hz (hh.trans hR)
    exact ⟨image_eq_zero_of_notMem_tsupport hn,fderiv_of_notMem_tsupport ℝ hn⟩
  refine ⟨K,hK,rfl,?_,?_⟩
  · intro z
    by_cases hz : ‖z‖≤R
    · rw [norm_smul]
      exact (mul_le_mul (hbn z) (hb z hz) (norm_nonneg _) zero_le_one).trans_eq (one_mul _)
    · rw [(hzouts z hz).1,zero_smul,norm_zero]; exact hδ
  · intro z
    by_cases hz : ‖z‖≤R
    · rw [hder]
      have h1 : ‖b z • fderiv ℝ u z‖≤H := by
        rw [norm_smul]
        exact (mul_le_mul (hbn z) (hd z hz) (norm_nonneg _) zero_le_one).trans_eq (one_mul _)
      have h2 : ‖(fderiv ℝ b z).smulRight (u z)‖≤K := by
        rw [ContinuousLinearMap.norm_smulRight_apply]
        have h := mul_le_mul (hs.norm_fderiv_le z) (hb z hz) (norm_nonneg _) hK
        exact h.trans (by nlinarith)
      exact (norm_add_le _ _).trans (add_le_add h1 h2)
    · rw [hder,(hzouts z hz).1,(hzouts z hz).2]
      simp only [zero_smul,ContinuousLinearMap.zero_smulRight,add_zero,norm_zero]
      positivity

theorem local_nonlinear_gradient_small {L H η : ℝ} (hL : 0≤L) (hH : 0≤H) (hη : 0<η) :
    ∃ δ : ℝ,0<δ ∧ ∀ (F : E → E →L[ℝ] E),Continuous F → F 0=0 →
      (∀ x y,‖F x-F y‖≤L*‖x-y‖) → ∀ u : ℂ → E,ContDiff ℝ ∞ u → u 0=0 →
      (∀ z,‖z‖≤2 → ‖u z‖≤δ) → (∀ z,‖z‖≤2 → ‖fderiv ℝ u z‖≤H) →
      (∀ z,‖z‖<2 → fderiv ℝ u z Complex.I-Complex.I • fderiv ℝ u z 1=
        F (u z) (fderiv ℝ u z 1)) → ‖fderiv ℝ u 0‖<η := by
  let b : ContDiffBump (0:ℂ) := ⟨1/4,1/2,by norm_num,by norm_num⟩
  let c : ContDiffBump (0:ℂ) := ⟨1,3/2,by norm_num,by norm_num⟩
  let hc := boundedCThree_of_compactSupport c.contDiff c.hasCompactSupport
  have hH' : 0≤H+hc.bound := add_nonneg hH hc.bound_nonneg
  obtain ⟨d,hd,hsmall⟩ := bounded_cutoff_gradient_small (E := E) b hL hH' hη
  let δ := min d 1
  have hδ : 0<δ := lt_min hd zero_lt_one
  refine ⟨δ,hδ,?_⟩
  intro F hF hF0 hFL u hu h0 hb hdu hcr
  let w : ℂ → E := fun z => c z • u z
  have hw : ContDiff ℝ ∞ w := c.contDiff.smul hu
  have hw0 : w 0=0 := by simp only [w,h0,smul_zero]
  obtain ⟨K,hK,hKe,hwb,hwd⟩ := smooth_cutoff_local_bounds c hu (by change (3:ℝ)/2≤2; norm_num)
    hδ.le (min_le_right _ _) hH hb hdu
  have hwl : ∀ x y,‖w x-w y‖≤(H+hc.bound)*dist x y := by
    intro x y
    rw [dist_eq_norm]
    apply norm_sub_le_of_deriv_bound (hw.differentiable (by simp))
    intro z
    simpa only [hKe] using hwd z
  have hwne (z : ℂ) (hz : ‖z‖<1) : w =ᶠ[𝓝 z] u := by
    have he := c.eventuallyEq_one_of_mem_ball (show z∈Metric.ball (0:ℂ) c.rIn by
      simpa only [Metric.mem_ball,dist_zero_right] using hz)
    filter_upwards [he] with y hy
    change c y • u y=u y
    rw [hy]; exact one_smul ℝ (u y)
  have hcrw : ∀ z,b z≠0 → fderiv ℝ w z Complex.I-Complex.I • fderiv ℝ w z 1=
      F (w z) (fderiv ℝ w z 1) := by
    intro z hz
    have hz' : ‖z‖<(1:ℝ)/2 := by
      have hs : z∈Function.support b := hz
      rw [b.support_eq] at hs
      simpa only [Metric.mem_ball,dist_zero_right] using hs
    have he := hwne z (by linarith)
    rw [he.fderiv_eq,he.eq_of_nhds]
    exact hcr z (by linarith)
  have hh := hsmall F hF hF0 hFL w hw hw0 (fun z => (hwb z).trans (min_le_left _ _)) hwl hcrw
  rwa [(hwne 0 (by simp)).fderiv_eq] at hh


end
open scoped ContDiff Topology BoundedContinuousFunction
open Set Filter



end HigherDimensionalBallPacking.Rigidity.HolderCompletion
end

end OAI
end

section
-- module Solutions.OAIQ240_BP.BallPacking_Compactness_FrozenCR
attribute [-instance] _root_.OAI.PackingSufficiencySupport.Hamiltonian.flatProduct_chartedSpace
attribute [-simp] _root_.OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.completedDX_value _root_.OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.completedFrameJet_value _root_.OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.completedInverseJet_value _root_.OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.completedPrincipal_value _root_.OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.completedQ_value _root_.OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.completedStructureJet_value _root_.OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.curveMarkCoefficientHolder_value _root_.OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.curveMarkCoefficient_apply _root_.OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.curveZeroOrderHolder_value _root_.OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.curveZeroOrder_apply _root_.OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.smoothAlongJet_value _root_.OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.smoothMarkedPrincipal_value _root_.OAI.HigherDimensionalBallPacking.Rigidity.normalizedPrimitive_apply _root_.OAI.HigherDimensionalBallPacking.Rigidity.realCurve_zero _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.infinity_end_count _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.sqrt_sq_complex
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

local instance fcrInst1_r617f9a_1 : NormedAddCommGroup (End n) := ContinuousLinearMap.toNormedAddCommGroup
local instance fcrInst2_r617f9a_1 : NormedSpace ℝ (End n) := ContinuousLinearMap.toNormedSpace
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

lemma weighted_gradient_selection {X : Type*} [MetricSpace X] [ProperSpace X]
    {f : X → ℝ} (hf : Continuous f) (hn : ∀ x,0≤f x)
    (x : X) {R : ℝ} (hR : 0<R) (hx : 0<f x) :
    ∃ y : X,∃ r : ℝ,0 < r ∧ dist y x+r≤R ∧ 0<f y ∧
      R*f x≤2*r*f y ∧ ∀ z,dist z y ≤ r → f z≤2*f y := by
  let g : X → ℝ := fun y => (R-dist y x)*f y
  have hg : Continuous g := (continuous_const.sub (continuous_id.dist continuous_const)).mul hf
  obtain ⟨y,hy,hmax⟩ := (isCompact_closedBall x R).exists_isMaxOn
    ⟨x,Metric.mem_closedBall_self hR.le⟩ hg.continuousOn
  have hm : R*f x≤(R-dist y x)*f y := by
    have hh := hmax (Metric.mem_closedBall_self hR.le)
    change (R-dist x x)*f x≤(R-dist y x)*f y at hh
    simpa only [dist_self,sub_zero] using hh
  have hdy : dist y x<R := by
    by_contra! h
    have hnz : (R-dist y x)*f y≤0 := mul_nonpos_of_nonpos_of_nonneg (by linarith) (hn y)
    have hp := mul_pos hR hx
    linarith
  have hfy : 0<f y := by
    by_contra! h
    have hh : f y=0 := le_antisymm h (hn y)
    rw [hh,mul_zero] at hm
    exact (not_le_of_gt (mul_pos hR hx)) hm
  let r : ℝ := (R-dist y x)/2
  have hr : 0 < r := by dsimp [r] <;> linarith
  have hrr : dist y x+r≤R := by dsimp [r] <;> linarith
  refine ⟨y,r,hr,hrr,hfy,by dsimp [r] <;> nlinarith [hm],?_⟩
  intro z hz
  have hzx : dist z x≤R := (dist_triangle z y x).trans (by linarith)
  have hzg := hmax (show z∈Metric.closedBall x R from hzx)
  change (R-dist z x)*f z≤(R-dist y x)*f y at hzg
  have hcoef : r≤R-dist z x := by
    have hh := dist_triangle z y x
    dsimp [r] at *
    linarith
  have hh := mul_le_mul_of_nonneg_right hcoef (hn z)
  have he : R-dist y x=2*r := by dsimp [r] <;> ring
  rw [he] at hzg
  have hmul : r*f z ≤ r*(2*f y) := (hh.trans hzg).trans_eq (by ring)
  exact (mul_le_mul_iff_right₀ hr).mp hmul

variable {n : ℕ}

local instance ecgInst1_r617f9a_1 : NormedAddCommGroup (End n) := ContinuousLinearMap.toNormedAddCommGroup
local instance ecgInst2_r617f9a_1 : NormedSpace ℝ (End n) := ContinuousLinearMap.toNormedSpace
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

lemma rescaledCurve_source_dist (y z : ℂ) {r : ℝ} (hr : 0 ≤ r) : dist (y+r • z) y=r*‖z‖ := by
  rw [dist_eq_norm,add_sub_cancel_left,norm_smul,Real.norm_eq_abs,abs_of_nonneg hr]

theorem equicontinuous_CR_derivative_bound_bp240_oai {ι : Type*} (J : ι → Phase n → End n)
    (u : ι → ℂ → Phase n) (hu : ∀ i,ContDiff ℝ ∞ (u i))
    (hJc : ∀ i,Continuous (J i)) (hJ : ∀ i x,Compatible (J i x))
    (hcr : ∀ i z,PseudoHolomorphicAt (J i) (u i) z)
    {L G : ℝ} (hL : 0≤L) (hG : 1≤G)
    (hJL : ∀ i x y,‖J i x-J i y‖≤L*‖x-y‖)
    (hP : ∀ i x,‖compatibleFrame (J i x)‖≤G)
    (hPi : ∀ i x,‖(compatibleFrame (J i x)).inverse‖≤G)
    (hm : ∀ ε : ℝ,0<ε →∃ δ : ℝ,0<δ ∧ ∀ i x y,dist x y<δ →dist (u i x) (u i y)<ε) :
    ∃ M : ℝ,0<M ∧ ∀ i z,‖fderiv ℝ (u i) z‖≤M := by
  have hG0 : 0<G := lt_of_lt_of_le zero_lt_one hG
  obtain ⟨e,he,hell⟩ := local_nonlinear_gradient_small (E := Phase n)
    (by positivity : 0≤G^3*L) (by positivity : 0≤G*2) (div_pos zero_lt_one hG0)
  obtain ⟨d,hd,hmod⟩ := hm (e/G) (div_pos he hG0)
  let M := max 4 (4/d)+1
  have hM : 0<M := by dsimp [M] <;> linarith [le_max_left (4:ℝ) (4/d)]
  refine ⟨M,hM,?_⟩
  intro i x
  by_contra! hgt
  let f : ℂ → ℝ := fun z => ‖fderiv ℝ (u i) z‖
  have hfx : 0<f x := hM.trans hgt
  have hfc : Continuous f := ((hu i).continuous_fderiv (by simp)).norm
  obtain ⟨y,s,hs,hsy,hfy,hweight,hsel⟩ := weighted_gradient_selection hfc (fun _ => norm_nonneg _) x zero_lt_one hfx
  have hs1 : s≤1 := by linarith [dist_nonneg (x := y) (y := x)]
  have hfx4 : 4<f x := by have hh := le_max_left (4:ℝ) (4/d); dsimp [M] at hgt <;> linarith
  have hfxd : 4/d<f x := by have hh := le_max_right (4:ℝ) (4/d); dsimp [M] at hgt <;> linarith
  have hfxfy : f x≤2*f y := by
    have hh := mul_le_mul_of_nonneg_right hs1 hfy.le
    nlinarith only [hweight,hh]
  have hradius : 2/f y < s := by
    apply (div_lt_iff₀ hfy).mpr
    nlinarith only [hweight,hfx4]
  have hor : 2/f y<d := by
    have hh := (div_lt_iff₀ hd).mp hfxd
    apply (div_lt_iff₀ hfy).mpr
    nlinarith [mul_le_mul_of_nonneg_right hfxfy hd.le]
  let r : ℝ := (f y)⁻¹
  have hr : 0 < r := inv_pos.mpr hfy
  let v := rescaledCurve (u i) y r
  have hv : ContDiff ℝ ∞ v := rescaledCurve_smooth (hu i) y r
  have hv0 : v 0=u i y := by simp only [v,rescaledCurve,smul_zero,add_zero]
  have hdist : ∀ z,‖z‖≤2 →dist (y+r • z) y≤2/f y := by
    intro z hz
    rw [rescaledCurve_source_dist y z hr.le]
    have hh := mul_le_mul_of_nonneg_left hz hr.le
    simpa only [r,mul_comm,div_eq_mul_inv] using hh
  have hvd : ∀ z,‖z‖≤2 →‖fderiv ℝ v z‖≤2 := by
    intro z hz
    rw [rescaledCurve_fderiv (hu i),norm_smul,Real.norm_eq_abs,abs_of_nonneg hr.le]
    have hh := hsel (y+r • z) ((hdist z hz).trans hradius.le)
    have hm := mul_le_mul_of_nonneg_left hh hr.le
    have hid : r*(2*f y)=2 := by dsimp [r]; field_simp
    exact hm.trans_eq hid
  have hvd0 : ‖fderiv ℝ v 0‖=1 := by
    rw [rescaledCurve_fderiv (hu i),smul_zero,add_zero,norm_smul,Real.norm_eq_abs,abs_of_nonneg hr.le]
    change (f y)⁻¹*f y=1
    exact inv_mul_cancel₀ hfy.ne'
  let a := u i y
  let w := frozenCurve (J i) a v
  have hw : ContDiff ℝ ∞ w := frozenCurve_smooth a hv
  have hw0 : w 0=0 := by simp only [w,frozenCurve,hv0,a,sub_self,map_zero]
  have hwb : ∀ z,‖z‖≤2 →‖w z‖≤e := by
    intro z hz
    have ho := hmod i (y+r • z) y ((hdist z hz).trans_lt hor)
    rw [dist_eq_norm] at ho
    have ht : G*‖v z-a‖<e := by
      have hh := (lt_div_iff₀ hG0).mp ho
      simpa only [v,rescaledCurve,a,mul_comm] using hh
    exact ((compatibleFrame (J i a)).le_opNorm _).trans
      ((mul_le_mul_of_nonneg_right (hP i a) (norm_nonneg _)).trans ht.le)
  have hwD : ∀ z,‖z‖≤2 →‖fderiv ℝ w z‖≤G*2 := by
    intro z hz
    rw [frozenCurve_fderiv a (hv.differentiable (by simp) z)]
    exact ((compatibleFrame (J i a)).opNorm_comp_le _).trans
      (mul_le_mul (hP i a) (hvd z hz) (norm_nonneg _) hG0.le)
  have hwcr : ∀ z,‖z‖<2 → fderiv ℝ w z Complex.I-Complex.I • fderiv ℝ w z 1=
      frozenTargetCoefficient (J i) a (w z) (fderiv ℝ w z 1) := by
    intro z _
    exact frozenCurve_CR (hJ i a) (hv.differentiable (by simp) z)
      (rescaledCurve_CR (hu i) (hcr i) y r z)
  have hh := hell (frozenTargetCoefficient (J i) a) (frozenTargetCoefficient_continuous (hJc i) a)
    (frozenTargetCoefficient_zero _ _) (frozenTargetCoefficient_lipschitz hL hG0.le (hJL i) (hP i a) (hPi i a))
    w hw hw0 hwb hwD hwcr
  have heD : ((compatibleFrame (J i a)).inverse).comp (fderiv ℝ w 0)=fderiv ℝ v 0 := by
    rw [frozenCurve_fderiv a (hv.differentiable (by simp) 0)]
    apply ContinuousLinearMap.ext
    intro z
    exact compatibleFrame_inverse_left_bp240 (hJ i a) _
  have hnorm := ((compatibleFrame (J i a)).inverse).opNorm_comp_le (fderiv ℝ w 0)
  rw [heD,hvd0] at hnorm
  have hc : 1≤G*‖fderiv ℝ w 0‖ := hnorm.trans
    (mul_le_mul_of_nonneg_right (hPi i a) (norm_nonneg _))
  have hlt := (lt_div_iff₀ hG0).mp hh
  nlinarith

end HigherDimensionalBallPacking.Rigidity

end

end OAI
end

theorem solution.{u_1} : type_of% @OAI.HigherDimensionalBallPacking.Rigidity.equicontinuous_CR_derivative_bound_bp240_oai.{u_1} := @OAI.HigherDimensionalBallPacking.Rigidity.equicontinuous_CR_derivative_bound_bp240_oai.{u_1}
