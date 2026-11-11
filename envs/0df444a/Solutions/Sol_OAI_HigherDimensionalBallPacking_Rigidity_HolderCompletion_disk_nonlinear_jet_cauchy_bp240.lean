-- Prove2me | solution 1 for OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.disk_nonlinear_jet_cauchy_bp240
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T01:06:06.403845+00:00
-- url     : https://prove2.me/submissions/3198b5da-f959-43a5-a648-1fcc1b162d91

import Mathlib
import Definitions.Def_OAIQ240Bp014
import Definitions.Def_OAIQ240Bp015

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

end
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
local instance holderCompInst2_r859b9c_1 : NormedSpace ℝ (HMap X E) := inferInstance
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
attribute [-instance] _root_.OAI.PackingSufficiencySupport.Comparison.convexMaps_nonempty _root_.OAI.PackingSufficiencySupport.FiniteMoment.Radial.instInhabitedQuadrant _root_.OAI.PackingSufficiencySupport.Hamiltonian.flatProduct_chartedSpace
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

attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.csInst1
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.csInst2
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.csInst9
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.csInst10
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.csInst11
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.csInst12
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.csInst3
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.csInst4
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.csInst5
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.csInst6
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.csInst7
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.csInst8
omit [CompleteSpace E] in
lemma standardJetCR_sub_explicit (v w : COne ℂ E) :
    standardJetCR (v-w)=standardJetCR v-standardJetCR w := by
  apply value_ext
  intro z
  rw [(valueCLM ((1:ℝ)/3)).map_sub]
  simp only [BoundedContinuousFunction.sub_apply,standardJetCR_value]
  change ((cDeriv v z Complex.I-cDeriv w z Complex.I)-
      Complex.I • (cDeriv v z 1-cDeriv w z 1))=
      (cDeriv v z Complex.I-Complex.I • cDeriv v z 1)-
      (cDeriv w z Complex.I-Complex.I • cDeriv w z 1)
  rw [smul_sub]
  abel

omit [CompleteSpace E] in
lemma clm_principal_sub_algebra (A B : E →L[ℝ] E) (x y f g : E) :
    (A x+f)-(B y+g)=A (x-y)+((A-B) y+(f-g)) := by
  simp only [map_sub,sub_apply]
  abel

omit [CompleteSpace E] in
lemma principal_difference_identity (v w : COne ℂ E) (A B : HMap ℂ (E →L[ℝ] E))
    (f g : HMap ℂ E)
    (hv : standardJetCR v=holderCoefficientAction A (jetDirectional 1 v)+f)
    (hw : standardJetCR w=holderCoefficientAction B (jetDirectional 1 w)+g) :
    standardJetCR (v-w)=holderCoefficientAction A (jetDirectional 1 (v-w))+
      (holderCoefficientAction (A-B) (jetDirectional 1 w)+(f-g)) := by
  rw [standardJetCR_sub_explicit,hv,hw]
  apply value_ext
  intro z
  change (valueCLM _ A z (cDeriv v z 1)+valueCLM _ f z)-
      (valueCLM _ B z (cDeriv w z 1)+valueCLM _ g z)=
      valueCLM _ A z (cDeriv v z 1-cDeriv w z 1)+
        ((valueCLM _ A z-valueCLM _ B z) (cDeriv w z 1)+(valueCLM _ f z-valueCLM _ g z))
  exact clm_principal_sub_algebra (valueCLM _ A z) (valueCLM _ B z)
    (cDeriv v z 1) (cDeriv w z 1) (valueCLM _ f z) (valueCLM _ g z)

omit [CompleteSpace E] in
lemma holderCoefficientAction_jet_norm_le (A : HMap ℂ (E →L[ℝ] E)) (w : COne ℂ E) :
    ‖holderCoefficientAction A (jetDirectional 1 w)‖≤
      (‖bilinCLM (X := ℂ) (α := (1:ℝ)/3) (ContinuousLinearMap.apply (E := E) ℝ E).flip‖*
      ‖jetDirectional (E := E) 1‖)*‖A‖*‖w‖ := by
  have hp := holderCoefficientAction_norm_le A (jetDirectional 1 w)
  have hd := (jetDirectional (E := E) 1).le_opNorm w
  exact hp.trans ((mul_le_mul_of_nonneg_left hd (by positivity)).trans_eq (by ring))

omit [CompleteSpace E] in
lemma zeroMarked_sub (v w : COne ℂ E) (hv : cValue v 0=0) (hw : cValue w 0=0) :
    cValue (v-w) 0=0 := by
  change cValue v 0-cValue w 0=0
  rw [hv,hw,sub_self]

omit [CompleteSpace E] in
lemma jet_residual_sub_supported {K : Set ℂ} (v w : COne ℂ E)
    (hv : standardJetCR v∈supportedHolder K) (hw : standardJetCR w∈supportedHolder K) :
    standardJetCR (v-w)∈supportedHolder K := by
  rw [standardJetCR_sub_explicit]
  exact (supportedHolder (E := E) K).sub_mem hv hw

lemma small_coefficient_difference_estimate {K : Set ℂ} (hK : IsCompact K) :
    ∃ ε C D : ℝ,0<ε ∧ 0<C ∧ 0≤D ∧
    ∀ (v w : COne ℂ E),cValue v 0=0 →cValue w 0=0 →
      standardJetCR v∈supportedHolder K →standardJetCR w∈supportedHolder K →
    ∀ (A B : HMap ℂ (E →L[ℝ] E)),‖A‖≤ε →‖B‖≤ε →
    ∀ (f g : HMap ℂ E),
      standardJetCR v=holderCoefficientAction A (jetDirectional 1 v)+f →
      standardJetCR w=holderCoefficientAction B (jetDirectional 1 w)+g →
      ‖v‖≤C*‖f‖ ∧ ‖v-w‖≤C*(D*‖A-B‖*‖w‖+‖f-g‖) := by
  obtain ⟨ε,C,hε,hC,he⟩ := small_coefficient_schauder (E := E) hK
  let D := ‖bilinCLM (X := ℂ) (α := (1:ℝ)/3) (ContinuousLinearMap.apply (E := E) ℝ E).flip‖*
    ‖jetDirectional (E := E) 1‖
  have hD : 0≤D := by dsimp [D] <;> positivity
  refine ⟨ε,C,D,hε,hC,hD,?_⟩
  intro v w hv hw hvs hws A B hA hB f g hve hwe
  refine ⟨he v hv hvs A hA f hve,?_⟩
  have hest := he (v-w) (zeroMarked_sub v w hv hw) (jet_residual_sub_supported v w hvs hws)
    A hA _ (principal_difference_identity v w A B f g hve hwe)
  have hp' : ‖holderCoefficientAction (A-B) (jetDirectional 1 w)‖≤D*‖A-B‖*‖w‖ :=
    holderCoefficientAction_jet_norm_le (A-B) w
  exact hest.trans (mul_le_mul_of_nonneg_left
    ((norm_add_le _ _).trans (add_le_add hp' (le_refl _))) hC.le)

lemma cauchySeq_of_pair_distance_bound {X Y Z : Type*} [PseudoMetricSpace X]
    [PseudoMetricSpace Y] [PseudoMetricSpace Z] {u : ℕ →X} {a : ℕ →Y} {b : ℕ →Z}
    {P Q : ℝ} (hP : 0≤P) (hQ : 0≤Q) (ha : CauchySeq a) (hb : CauchySeq b)
    (hu : ∀ i j,dist (u i) (u j)≤P*dist (a i) (a j)+Q*dist (b i) (b j)) :
    CauchySeq u := by
  rw [Metric.cauchySeq_iff] at ha hb ⊢
  intro ε hε
  have hp : 0<P+Q+1 := by linarith
  obtain ⟨N,hN⟩ := ha (ε/(P+Q+1)) (div_pos hε hp)
  obtain ⟨M,hM⟩ := hb (ε/(P+Q+1)) (div_pos hε hp)
  refine ⟨max N M,fun i hi j hj => ?_⟩
  have h1 := hN i (le_trans (le_max_left _ _) hi) j (le_trans (le_max_left _ _) hj)
  have h2 := hM i (le_trans (le_max_right _ _) hi) j (le_trans (le_max_right _ _) hj)
  have hh := add_le_add (mul_le_mul_of_nonneg_left h1.le hP) (mul_le_mul_of_nonneg_left h2.le hQ)
  have he : P*(ε/(P+Q+1))+Q*(ε/(P+Q+1))<ε := by
    have hδ := div_pos hε hp
    have hid : (P+Q+1)*(ε/(P+Q+1))=ε := mul_div_cancel₀ ε (ne_of_gt hp)
    nlinarith
  exact (hu i j).trans_lt (hh.trans_lt he)

theorem small_coefficient_cauchy {K : Set ℂ} (hK : IsCompact K) :
    ∃ ε : ℝ,0<ε ∧ ∀ (v : ℕ → COne ℂ E) (A : ℕ → HMap ℂ (E →L[ℝ] E))
      (f : ℕ → HMap ℂ E),
      (∀ i,cValue (v i) 0=0) →(∀ i,standardJetCR (v i)∈supportedHolder K) →
      (∀ i,‖A i‖≤ε) →
      (∀ i,standardJetCR (v i)=holderCoefficientAction (A i) (jetDirectional 1 (v i))+f i) →
      CauchySeq A → CauchySeq f → CauchySeq v := by
  obtain ⟨ε,C,D,hε,hC,hD,he⟩ := small_coefficient_difference_estimate (E := E) hK
  refine ⟨ε,hε,?_⟩
  intro v A f hv hs hA hres hAc hfc
  obtain ⟨M,hM,hMf'⟩ := hfc.isBounded_range.exists_pos_norm_le
  have hMf : ∀ i,‖f i‖≤M := fun i => hMf' (f i) ⟨i,rfl⟩
  have hbound : ∀ j,‖v j‖≤C*M := fun j =>
    ((he (v j) (v j) (hv j) (hv j) (hs j) (hs j) (A j) (A j) (hA j) (hA j)
      (f j) (f j) (hres j) (hres j)).1).trans (mul_le_mul_of_nonneg_left (hMf j) hC.le)
  apply cauchySeq_of_pair_distance_bound (P := C*D*(C*M)) (Q := C)
    (by positivity) hC.le hAc hfc
  intro i j
  simp only [dist_eq_norm]
  have hh := (he (v i) (v j) (hv i) (hv j) (hs i) (hs j) (A i) (A j) (hA i) (hA j)
    (f i) (f j) (hres i) (hres j)).2
  have hb := mul_le_mul_of_nonneg_left (hbound j) (by positivity : 0≤D*‖A i-A j‖)
  exact hh.trans ((mul_le_mul_of_nonneg_left (add_le_add hb (le_refl _)) hC.le).trans_eq (by ring))


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
local instance ccInst4_r859b9c_1 : NormedSpace ℝ (COne ℂ E) := inferInstance
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.ccInst5
local instance ccInst6_r859b9c_1 : NormedSpace ℝ (HMap ℂ E) := inferInstance
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.ccInst7
local instance ccInst8_r859b9c_1 : NormedSpace ℝ (HMap ℂ (E →L[ℝ] E)) := inferInstance
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
variable {X E : Type*} [MetricSpace X] [NormedAddCommGroup E] [NormedSpace ℝ E]

local instance uhcInst1_r859b9c_1 : NormedAddCommGroup (HMap X E) := inferInstance
local instance uhcInst2_r859b9c_1 : NormedSpace ℝ (HMap X E) := inferInstance
lemma holder_cauchy_of_uniform_values {v : ℕ → HMap X E} {L : ℝ} (hL : 0≤L)
    (hl : ∀ i x y,‖valueCLM _ (v i) x-valueCLM _ (v i) y‖≤L*dist x y)
    (hv : ∀ ε : ℝ,0<ε →∃ N : ℕ,∀ i≥N,∀ j≥N,∀ x,
      ‖valueCLM _ (v i) x-valueCLM _ (v j) x‖≤ε) : CauchySeq v := by
  rw [Metric.cauchySeq_iff]
  intro ε hε
  obtain ⟨δ,hδ,hd⟩ := holder_small_of_small_value (X := X) (E := E) (by linarith : 0≤2*L) hε
  obtain ⟨N,hN⟩ := hv δ hδ
  refine ⟨N,fun i hi j hj => ?_⟩
  rw [dist_eq_norm]
  apply hd (v i-v j)
  · intro x
    exact hN i hi j hj x
  · intro x y
    change ‖(valueCLM _ (v i) x-valueCLM _ (v j) x)-
      (valueCLM _ (v i) y-valueCLM _ (v j) y)‖≤2*L*dist x y
    have he : (valueCLM _ (v i) x-valueCLM _ (v j) x)-
        (valueCLM _ (v i) y-valueCLM _ (v j) y)=
        (valueCLM _ (v i) x-valueCLM _ (v i) y)-
        (valueCLM _ (v j) x-valueCLM _ (v j) y) := by abel
    rw [he]
    exact (norm_sub_le _ _).trans ((add_le_add (hl i x y) (hl j x y)).trans_eq (by ring))



end HigherDimensionalBallPacking.Rigidity.HolderCompletion
end

end OAI
end

section
-- module Solutions.OAIQ240_BP.BallPacking_Compactness_JetCauchy
attribute [-instance] _root_.OAI.PackingSufficiencySupport.Comparison.convexMaps_nonempty _root_.OAI.PackingSufficiencySupport.FiniteMoment.Radial.instInhabitedQuadrant _root_.OAI.PackingSufficiencySupport.Hamiltonian.flatProduct_chartedSpace
attribute [-simp] _root_.OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.affineJetDeriv_value _root_.OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.affineJetSuperpose_value _root_.OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.affineJetValue_value _root_.OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.compactPerturbationJet_value _root_.OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.completedDX_value _root_.OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.completedFrameJet_value _root_.OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.completedInverseJet_value _root_.OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.completedPrincipal_value _root_.OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.completedQ_value _root_.OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.completedStructureJet_value _root_.OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.curveMarkCoefficientHolder_value _root_.OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.curveZeroOrderHolder_value _root_.OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.frameCRCoefficient_value _root_.OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.freePrincipal_value _root_.OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.freeSum_deriv _root_.OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.freeSum_value _root_.OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.freeZeroOrder_value _root_.OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.holderTranslate_value _root_.OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.jetTranslate_deriv _root_.OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.jetTranslate_value _root_.OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.jetZeroOrder_value _root_.OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.markedDerivEval_value _root_.OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.markedDerivativeVariation_value _root_.OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.markedEval_value _root_.OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.markedFiniteCorrection_value _root_.OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.markedPrincipal_value _root_.OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.markedVariation_value _root_.OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.markedZeroOrder_value _root_.OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.principalCR_value _root_.OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.smoothMarkedPrincipal_value _root_.OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.supportedEval_value _root_.OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.supportedFieldAction_value _root_.OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.truncatedCoefficient_value _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.infinity_end_count _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.sqrt_sq_complex
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

attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.ljcInst1
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.ljcInst2
local instance ljcInst3_r859b9c_1 : NormedAddCommGroup (COne ℂ E) := inferInstance
local instance ljcInst4_r859b9c_1 : NormedSpace ℝ (COne ℂ E) := inferInstance
local instance ljcInst5_r859b9c_1 : NormedAddCommGroup (HMap ℂ E) := inferInstance
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.ljcInst6
local instance ljcInst7_r859b9c_1 : NormedAddCommGroup (HMap ℂ (E →L[ℝ] E)) := inferInstance
local instance ljcInst8_r859b9c_1 : NormedSpace ℝ (HMap ℂ (E →L[ℝ] E)) := inferInstance
lemma cauchy_coefficient_action {A : ℕ → HMap ℂ (E →L[ℝ] E)} {v : ℕ → HMap ℂ E}
    (hA : CauchySeq A) (hv : CauchySeq v) :
    CauchySeq (fun i => holderCoefficientAction (A i) (v i)) := by
  obtain ⟨a,ha⟩ := cauchySeq_tendsto_of_complete hA
  obtain ⟨w,hw⟩ := cauchySeq_tendsto_of_complete hv
  have hAc : Continuous (fun x : HMap ℂ (E →L[ℝ] E) => holderCoefficientAction x) :=
    (bilinCLM (X := ℂ) (α := (1:ℝ)/3) (ContinuousLinearMap.apply (E := E) ℝ E).flip).continuous
  have hc : Continuous (fun p : HMap ℂ (E →L[ℝ] E) × HMap ℂ E =>
      holderCoefficientAction p.1 p.2) := (hAc.comp continuous_fst).clm_apply continuous_snd
  exact ((hc.tendsto (a,w)).comp (ha.prodMk_nhds hw)).cauchySeq

lemma cutoff_forcing_holder_cauchy (C D : HMap ℂ (E →L[ℝ] E))
    {A : ℕ → HMap ℂ (E →L[ℝ] E)} {v : ℕ → HMap ℂ E}
    (hA : CauchySeq A) (hv : CauchySeq v) :
    CauchySeq (fun i => holderCoefficientAction C (v i)-
      holderCoefficientAction (A i) (holderCoefficientAction D (v i))) := by
  have hC := cauchy_coefficient_action (E := E) (cauchySeq_const (x := C)) hv
  have hD := cauchy_coefficient_action (E := E) (cauchySeq_const (x := D)) hv
  obtain ⟨c,hc⟩ := cauchySeq_tendsto_of_complete hC
  obtain ⟨d,hd⟩ := cauchySeq_tendsto_of_complete (cauchy_coefficient_action hA hD)
  exact (hc.sub hd).cauchySeq

theorem cutoff_jet_cauchy (b : ContDiffBump (0:ℂ)) {L : ℝ} (hL : 0≤L) :
    ∃ δ : ℝ,0<δ ∧ ∀ (u : ℕ → ℂ → E) (hu : ∀ i,ContDiff ℝ ∞ (u i))
      (A : ℕ → ℂ → E →L[ℝ] E),
      (∀ i,Continuous (A i)) →(∀ i,u i 0=0) →
      (∀ i z,‖A i z‖≤δ) →
      (∀ i x y,‖A i x-A i y‖≤L*dist x y) →
      (∃ M H : ℝ,0≤M ∧ 0≤H ∧ (∀ i z,‖u i z‖≤M) ∧
        ∀ i x y,‖u i x-u i y‖≤H*dist x y) →
      (∀ ε : ℝ,0<ε →∃ N : ℕ,∀ i≥N,∀ j≥N,∀ z,‖u i z-u j z‖≤ε) →
      (∀ ε : ℝ,0<ε →∃ N : ℕ,∀ i≥N,∀ j≥N,∀ z,‖A i z-A j z‖≤ε) →
      (∀ i z,b z≠0 →fderiv ℝ (u i) z Complex.I-Complex.I • fderiv ℝ (u i) z 1=
        A i z (fderiv ℝ (u i) z 1)) →
      CauchySeq (fun i => cutoffCurveJet b (hu i)) := by
  obtain ⟨ε,hε,hcauchy⟩ := small_coefficient_cauchy (E := E) (isCompact_closedBall (0:ℂ) b.rOut)
  obtain ⟨δ,hδ,hsmall⟩ := holder_small_of_small_value (X := ℂ) (E := E →L[ℝ] E) hL hε
  refine ⟨δ,hδ,?_⟩
  intro u hu A hAc h0 hAb hAl hUb hUc hAcc hcr
  obtain ⟨M,H,hM,hH,hUb,hUl⟩ := hUb
  obtain ⟨B,hB,hD,hDL,hC,hCL⟩ := cutoff_transport_bounds (E := E) b
  let V : ℕ → HMap ℂ E := fun i => ofBoundedLipschitz (u i) (hu i).continuous M H hM hH (hUb i) (hUl i)
  let T : ℕ → HMap ℂ (E →L[ℝ] E) := fun i => ofBoundedLipschitz (A i) (hAc i) δ L hδ.le hL (hAb i) (hAl i)
  let C : HMap ℂ (E →L[ℝ] E) := ofBoundedLipschitz (cutoffCommute b)
    (cutoffCommute_smooth b).continuous B B hB.le hB.le hC hCL
  let D : HMap ℂ (E →L[ℝ] E) := ofBoundedLipschitz (cutoffTransport b 1)
    (cutoffTransport_smooth b 1).continuous B B hB.le hB.le hD hDL
  let f : ℕ → HMap ℂ E := fun i => holderCoefficientAction C (V i)-
    holderCoefficientAction (T i) (holderCoefficientAction D (V i))
  have hVc : CauchySeq V := holder_cauchy_of_uniform_values hH hUl hUc
  have hTc : CauchySeq T := holder_cauchy_of_uniform_values hL hAl hAcc
  have hfc : CauchySeq f := cutoff_forcing_holder_cauchy C D hTc hVc
  apply hcauchy (fun i => cutoffCurveJet b (hu i)) T f
    (fun i => cutoffCurveJet_zero b (hu i) (h0 i)) (fun i => cutoffCurveJet_supported b (hu i))
    (fun i => (hsmall (T i) (hAb i) (hAl i)).le) ?_ hTc hfc
  intro i
  apply cutoffCurveJet_CR b (hu i) (hcr i) (T i) (fun _ _ => rfl) (f i)
  intro z
  rfl


end
section
open scoped ContDiff Topology BoundedContinuousFunction
open Set Filter
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]

local instance legInst2_r859b9c_1 : NormedSpace ℝ (E →L[ℝ] E) := ContinuousLinearMap.toNormedSpace
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


end
section
open scoped ContDiff Topology BoundedContinuousFunction
open Set Filter
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]

lemma uniform_cauchy_comp_lipschitz {X Y Z : Type*} [NormedAddCommGroup Y]
    [NormedAddCommGroup Z] {F : ℕ → Y → Z} {u : ℕ → X → Y} {L M : ℝ}
    (hL : 0≤L) (hF : ∀ i x y,‖F i x-F i y‖≤L*‖x-y‖)
    (hb : ∀ i x,‖u i x‖≤M)
    (hu : ∀ ε : ℝ,0<ε →∃ N : ℕ,∀ i≥N,∀ j≥N,∀ x,‖u i x-u j x‖≤ε)
    (hFc : ∀ ε : ℝ,0<ε →∃ N : ℕ,∀ i≥N,∀ j≥N,∀ y,‖y‖≤M →‖F i y-F j y‖≤ε) :
    ∀ ε : ℝ,0<ε →∃ N : ℕ,∀ i≥N,∀ j≥N,∀ x,‖F i (u i x)-F j (u j x)‖≤ε := by
  intro ε hε
  obtain ⟨N,hN⟩ := hu (ε/(2*(L+1))) (div_pos hε (by linarith))
  obtain ⟨M,hM⟩ := hFc (ε/2) (half_pos hε)
  refine ⟨max N M,fun i hi j hj x => ?_⟩
  have h1 := hN i ((le_max_left _ _).trans hi) j ((le_max_left _ _).trans hj) x
  have h2 := hM i ((le_max_right _ _).trans hi) j ((le_max_right _ _).trans hj) (u j x) (hb j x)
  have hp : 0<L+1 := by linarith
  have hscale : L*(ε/(2*(L+1)))≤ε/2 := by
    apply (le_div_iff₀ (by norm_num : (0:ℝ)<2)).mpr
    have he : (2*(L+1))*(ε/(2*(L+1)))=ε := mul_div_cancel₀ ε (by positivity)
    have hd : 0≤ε/(2*(L+1)) := by positivity
    nlinarith
  have hbound : ‖F i (u i x)-F i (u j x)‖≤ε/2 :=
    (hF i _ _).trans ((mul_le_mul_of_nonneg_left h1 hL).trans hscale)
  exact (norm_sub_le_norm_sub_add_norm_sub _ _ _).trans (by linarith)

omit [CompleteSpace E] in
lemma cutoff_uniform_cauchy (c : ContDiffBump (0:ℂ)) {R : ℝ} (hc : c.rOut≤R)
    {u : ℕ → ℂ → E}
    (hu : ∀ ε : ℝ,0<ε →∃ N : ℕ,∀ i≥N,∀ j≥N,∀ z,‖z‖≤R →‖u i z-u j z‖≤ε) :
    ∀ ε : ℝ,0<ε →∃ N : ℕ,∀ i≥N,∀ j≥N,∀ z,‖c z • u i z-c z • u j z‖≤ε := by
  intro ε hε
  obtain ⟨N,hN⟩ := hu ε hε
  refine ⟨N,fun i hi j hj z => ?_⟩
  by_cases hz : ‖z‖≤R
  · rw [←smul_sub,norm_smul,Real.norm_eq_abs,abs_of_nonneg c.nonneg]
    exact (mul_le_mul c.le_one (hN i hi j hj z hz) (norm_nonneg _) zero_le_one).trans_eq (one_mul _)
  · have hz' : z∉tsupport c := by
      rw [c.tsupport_eq,Metric.mem_closedBall,dist_zero_right]
      exact fun hh => hz (hh.trans hc)
    simp only [image_eq_zero_of_notMem_tsupport hz',zero_smul,sub_self,norm_zero]
    exact hε.le

attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.djcInst1
local instance djcInst2_r859b9c_1 : NormedSpace ℝ (E →L[ℝ] E) := ContinuousLinearMap.toNormedSpace
local instance djcInst3_r859b9c_1 : NormedAddCommGroup (COne ℂ E) := inferInstance
local instance djcInst4_r859b9c_1 : NormedSpace ℝ (COne ℂ E) := inferInstance
omit [CompleteSpace E] in
lemma double_disk_cutoff {u : ℂ → E} (hu : ContDiff ℝ ∞ u) :
    cutoffCurveJet smallDiskBump (largerDiskBump.contDiff.smul hu)=cutoffCurveJet smallDiskBump hu := by
  apply cValue_ext
  intro z
  simp only [cutoffCurveJet_value]
  by_cases hz : smallDiskBump z=0
  · rw [hz,zero_smul,zero_smul]
  · have hr : ‖z‖<(1:ℝ)/2 := by
      have hh : z∈Function.support smallDiskBump := hz
      rw [smallDiskBump.support_eq,Metric.mem_ball,dist_zero_right] at hh
      exact hh
    have hc : largerDiskBump z=1 := largerDiskBump.one_of_mem_closedBall (by
      rw [Metric.mem_closedBall,dist_zero_right]
      change ‖z‖≤(1:ℝ)
      linarith)
    change smallDiskBump z • (largerDiskBump z • u z)=_
    rw [hc,one_smul]

theorem disk_nonlinear_jet_cauchy_bp240_oai {L H : ℝ} (hL : 0≤L) (hH : 0≤H) :
    ∃ δ : ℝ,0<δ ∧ ∀ (u : ℕ → ℂ → E) (hu : ∀ i,ContDiff ℝ ∞ (u i))
      (F : ℕ → E → E →L[ℝ] E),
      (∀ i,Continuous (F i)) →(∀ i,F i 0=0) →
      (∀ i x y,‖F i x-F i y‖≤L*‖x-y‖) →(∀ i,u i 0=0) →
      (∀ i z,‖z‖≤2 →‖u i z‖≤δ) →
      (∀ i z,‖z‖≤2 →‖fderiv ℝ (u i) z‖≤H) →
      (∀ ε : ℝ,0<ε →∃ N : ℕ,∀ i≥N,∀ j≥N,∀ z,‖z‖≤2 →‖u i z-u j z‖≤ε) →
      (∀ ε : ℝ,0<ε →∃ N : ℕ,∀ i≥N,∀ j≥N,∀ v,‖v‖≤δ →‖F i v-F j v‖≤ε) →
      (∀ i z,‖z‖<2 →fderiv ℝ (u i) z Complex.I-Complex.I • fderiv ℝ (u i) z 1=
        F i (u i z) (fderiv ℝ (u i) z 1)) →
      CauchySeq (fun i => cutoffCurveJet smallDiskBump (hu i)) := by
  let c := largerDiskBump
  let B := (boundedCThree_of_compactSupport c.contDiff c.hasCompactSupport).bound
  have hB : 0≤B := (boundedCThree_of_compactSupport c.contDiff c.hasCompactSupport).bound_nonneg
  obtain ⟨d,hd,hcauchy⟩ := cutoff_jet_cauchy (E := E) smallDiskBump (mul_nonneg hL (add_nonneg hH hB))
  let δ := min 1 (d/(L+1))
  have hδ : 0<δ := lt_min zero_lt_one (div_pos hd (by linarith))
  have hδd : L*δ≤d := by
    have hh := (le_div_iff₀ (by linarith : 0<L+1)).mp (min_le_right (1:ℝ) (d/(L+1)))
    nlinarith
  refine ⟨δ,hδ,?_⟩
  intro u hu F hFc hF0 hFL h0 hUb hUd hUc hFuc hcr
  let w : ℕ → ℂ → E := fun i z => c z • u i z
  have hw : ∀ i,ContDiff ℝ ∞ (w i) := fun i => c.contDiff.smul (hu i)
  have hw0 : ∀ i,w i 0=0 := by intro i; simp only [w,h0 i,smul_zero]
  have hwb : ∀ i z,‖w i z‖≤δ := by
    intro i
    exact (smooth_cutoff_local_bounds c (hu i) (by change (3:ℝ)/2≤2; norm_num)
      hδ.le (min_le_left _ _) hH (hUb i) (hUd i)).choose_spec.2.2.1
  have hwd : ∀ i z,‖fderiv ℝ (w i) z‖≤H+B := by
    intro i
    obtain ⟨K,hK,hKe,_,hh⟩ := smooth_cutoff_local_bounds c (hu i) (by change (3:ℝ)/2≤2; norm_num)
      hδ.le (min_le_left _ _) hH (hUb i) (hUd i)
    simpa only [hKe] using hh
  have hwl : ∀ i x y,‖w i x-w i y‖≤(H+B)*dist x y := by
    intro i x y
    rw [dist_eq_norm]
    exact norm_sub_le_of_deriv_bound ((hw i).differentiable (by simp)) (hwd i) x y
  have hwc := cutoff_uniform_cauchy (E := E) c (by change (3:ℝ)/2≤2; norm_num) hUc
  let A : ℕ → ℂ → E →L[ℝ] E := fun i z => F i (w i z)
  have hAb : ∀ i z,‖A i z‖≤d := by
    intro i z
    have hh := hFL i (w i z) 0
    rw [hF0 i,sub_zero,sub_zero] at hh
    exact hh.trans ((mul_le_mul_of_nonneg_left (hwb i z) hL).trans hδd)
  have hAl : ∀ i x y,‖A i x-A i y‖≤(L*(H+B))*dist x y := by
    intro i x y
    exact (hFL i _ _).trans ((mul_le_mul_of_nonneg_left (hwl i x y) hL).trans_eq (by ring))
  have hAc := uniform_cauchy_comp_lipschitz hL hFL hwb hwc hFuc
  have heq (i : ℕ) (z : ℂ) (hz : ‖z‖<1) : w i =ᶠ[𝓝 z] u i := by
    have he := c.eventuallyEq_one_of_mem_ball (show z∈Metric.ball (0:ℂ) c.rIn by
      rw [Metric.mem_ball,dist_zero_right]
      change ‖z‖<(1:ℝ)
      exact hz)
    filter_upwards [he] with y hy
    change c y • u i y=u i y
    rw [hy]; exact one_smul ℝ (u i y)
  have hres : ∀ i z,smallDiskBump z≠0 →
      fderiv ℝ (w i) z Complex.I-Complex.I • fderiv ℝ (w i) z 1=A i z (fderiv ℝ (w i) z 1) := by
    intro i z hz
    have hr : ‖z‖<(1:ℝ)/2 := by
      have hh : z∈Function.support smallDiskBump := hz
      rw [smallDiskBump.support_eq,Metric.mem_ball,dist_zero_right] at hh
      exact hh
    have he := heq i z (by linarith)
    change _=F i (w i z) _
    rw [he.fderiv_eq,he.eq_of_nhds]
    exact hcr i z (by linarith)
  have hh := hcauchy w hw A (fun i => (hFc i).comp (hw i).continuous) hw0 hAb hAl
    ⟨δ,H+B,hδ.le,add_nonneg hH hB,hwb,hwl⟩ hwc hAc hres
  have he (i : ℕ) : cutoffCurveJet smallDiskBump (hw i)=cutoffCurveJet smallDiskBump (hu i) := by
    change cutoffCurveJet smallDiskBump (largerDiskBump.contDiff.smul (hu i))=_
    exact double_disk_cutoff (hu i)
  simpa only [he] using hh


end
open scoped ContDiff Topology BoundedContinuousFunction
open Set Filter



end HigherDimensionalBallPacking.Rigidity.HolderCompletion
end

end OAI
end

theorem solution.{u_1} : type_of% @OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.disk_nonlinear_jet_cauchy_bp240_oai.{u_1} := @OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.disk_nonlinear_jet_cauchy_bp240_oai.{u_1}
