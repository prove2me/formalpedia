-- Prove2me | solution 1 for OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.jetZeroOrder_isCompact_bp240
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T01:50:46.684383+00:00
-- url     : https://prove2.me/submissions/44344e8f-49d0-4209-bcd8-18eea1ef3058

import Mathlib
import Definitions.Def_OAIQ240Bp011
import Definitions.Def_OAIQ240Bp025

section
-- module Solutions.OAIQ240_BP.BallPacking_Holder_BanachSpace
attribute [-instance] _root_.OAI.PackingSufficiencySupport.Hamiltonian.flatProduct_chartedSpace
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

variable {D}

lemma jet_norm_value_le (u : COneHolder (E := E) D α) (x : D) :
    ‖valueCLM α (jetValueCLM α u) x‖ ≤ ‖u‖ :=
  (norm_value_le _ _).trans (jetValue_norm_le u)

end

end HigherDimensionalBallPacking.Rigidity.HolderCompletion
end

end OAI
end

section
-- module Solutions.OAIQ240_BP.BallPacking_Holder_NonlinearCR
attribute [-instance] _root_.OAI.PackingSufficiencySupport.Hamiltonian.flatProduct_chartedSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace HigherDimensionalBallPacking.Rigidity

section
open scoped ContDiff Topology BoundedContinuousFunction
open Set Filter

namespace HolderCompletion
variable {D E F : Type*} [NormedAddCommGroup D] [NormedSpace ℝ D]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]

lemma c_value_bound (u : COne D E) (x : D) : ‖cValue u x‖ ≤ ‖u‖ := jet_norm_value_le u x
end HolderCompletion

end

end HigherDimensionalBallPacking.Rigidity
end

end OAI
end

section
-- module Solutions.OAIQ240_BP.BallPacking_Holder_MarkedFrame
attribute [-instance] _root_.OAI.PackingSufficiencySupport.Hamiltonian.flatProduct_chartedSpace
attribute [-simp] _root_.OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.affineJetDeriv_value _root_.OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.affineJetSuperpose_value _root_.OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.affineJetValue_value _root_.OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.compactPerturbationJet_value _root_.OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.compatibleFrameJet_value _root_.OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.compatibleInverseJet_value _root_.OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.completedFrameJet_value _root_.OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.completedInverseJet_value _root_.OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.completedPrincipal_value _root_.OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.completedStructureJet_value _root_.OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.cutoffCurveJet_value _root_.OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.frameCRCoefficient_value _root_.OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.freeSum_deriv _root_.OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.freeSum_value _root_.OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.holderTranslate_value _root_.OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.jetDirectional_value _root_.OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.jetTranslate_deriv _root_.OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.jetTranslate_value _root_.OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.jetZeroOrder_value _root_.OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.markedEval_value _root_.OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.markedFiniteCorrection_value _root_.OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.markedPrincipal_value _root_.OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.markedZeroOrder_value _root_.OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.ofBoundedLipschitz_value _root_.OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.principalCR_value _root_.OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.smoothAlongJet_value _root_.OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.smoothMarkedPrincipal_value _root_.OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.supportedFieldAction_value _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.infinity_end_count _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.sqrt_sq_complex
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
local instance holderCompInst2_rf89b68_1 : NormedSpace ℝ (HMap X E) := inferInstance
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

lemma restrictedValue_uniformInducing (K : Set X) (M : ℝ) {L : ℝ} (hL : 0 ≤ L) :
    IsUniformInducing (fun u : lipHolderSet (E := E) K M L => restrictedValue K u.val) := by
  apply Metric.isUniformInducing_iff.mpr
  refine ⟨(restrictedValue (E := E) K).uniformContinuous.comp uniformContinuous_subtype_val,?_⟩
  intro ε hε
  obtain ⟨δ,hδ,hd⟩ := holder_small_of_small_value (X := X) (E := E) (by linarith : 0 ≤ 2*L) hε
  refine ⟨δ,hδ,fun {u v} huv => ?_⟩
  change dist u.val v.val < ε
  rw [dist_eq_norm]
  apply hd (u.val-v.val)
  · intro x
    change ‖valueCLM _ u.val x-valueCLM _ v.val x‖ ≤ δ
    by_cases hx : x ∈ K
    · have h := BoundedContinuousFunction.dist_coe_le_dist (f := restrictedValue K u.val)
        (g := restrictedValue K v.val) (⟨x,hx⟩ : K)
      have hh : ‖valueCLM _ u.val x-valueCLM _ v.val x‖ ≤
          dist (restrictedValue K u.val) (restrictedValue K v.val) := by
        simpa only [restrictedValue_apply,dist_eq_norm] using h
      exact hh.trans huv.le
    · rw [u.property.2.2 x hx,v.property.2.2 x hx,sub_self,norm_zero]
      exact hδ.le
  · intro x y
    change ‖(valueCLM _ u.val x-valueCLM _ v.val x)-
      (valueCLM _ u.val y-valueCLM _ v.val y)‖ ≤ 2*L*dist x y
    have he : (valueCLM _ u.val x-valueCLM _ v.val x)-
        (valueCLM _ u.val y-valueCLM _ v.val y) =
        (valueCLM _ u.val x-valueCLM _ u.val y)-
        (valueCLM _ v.val x-valueCLM _ v.val y) := by abel
    rw [he]
    exact (norm_sub_le _ _).trans (by linarith [u.property.2.1 x y,v.property.2.1 x y])

lemma lipHolderSet_totallyBounded [ProperSpace E] {K : Set X} (hK : IsCompact K)
    (M : ℝ) {L : ℝ} (hL : 0 ≤ L) : TotallyBounded (lipHolderSet (E := E) K M L) := by
  let : CompactSpace K := isCompact_iff_compactSpace.mp hK
  let A : Set (K →ᵇ E) := restrictedValue K '' lipHolderSet (E := E) K M L
  have heq : Equicontinuous ((↑) : A → K → E) := by
    apply UniformEquicontinuous.equicontinuous
    rw [Metric.uniformEquicontinuous_iff]
    intro ε hε
    refine ⟨ε/(L+1),div_pos hε (by linarith),?_⟩
    intro x y hxy f
    obtain ⟨u,hu,huf⟩ := f.property
    change restrictedValue K u = f.val at huf
    rw [← huf,restrictedValue_apply,restrictedValue_apply,dist_eq_norm]
    have hdist : dist x.val y.val < ε/(L+1) := hxy
    have hb := hu.2.1 x.val y.val
    have hmul := (lt_div_iff₀ (by linarith : 0 < L+1)).mp hdist
    nlinarith [show 0 ≤ dist x.val y.val from dist_nonneg]
  have hc : IsCompact (closure A) := BoundedContinuousFunction.arzela_ascoli
    (Metric.closedBall (0:E) M) (isCompact_closedBall _ _) A (by
      intro f x hf
      obtain ⟨u,hu,rfl⟩ := hf
      simpa only [Metric.mem_closedBall,dist_zero_right,restrictedValue_apply] using hu.1 x.val) heq
  let F : lipHolderSet (E := E) K M L → (K →ᵇ E) := fun u => restrictedValue K u.val
  have ht : TotallyBounded (F '' Set.univ) := hc.totallyBounded.subset (by
    rintro _ ⟨u,_,rfl⟩
    exact subset_closure ⟨u.val,u.property,rfl⟩)
  have hu : TotallyBounded (Set.univ : Set (lipHolderSet (E := E) K M L)) :=
    (totallyBounded_image_iff (restrictedValue_uniformInducing K M hL)).mp ht
  have hh := hu.image uniformContinuous_subtype_val
  simpa only [Set.image_univ,Subtype.range_coe_subtype,Set.ofPred_mem_eq] using hh

variable (b : ContDiffBump (0:ℂ))

attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.holderLocInst1
local instance holderLocInst2_rf89b68_1 : NormedSpace ℝ (COne ℂ E) := inferInstance
lemma localizedJetValue_bounds (u : COne ℂ E) (hu : ‖u‖ ≤ 1) :
    localizedJetValue b u ∈ lipHolderSet (Metric.closedBall (0:ℂ) b.rOut) 1
      (1+(boundedCThree_of_compactSupport b.contDiff b.hasCompactSupport).bound) := by
  let hb := boundedCThree_of_compactSupport b.contDiff b.hasCompactSupport
  have hbu : ∀ z : ℂ, ‖b z‖ ≤ 1 := fun z => by
    rw [Real.norm_of_nonneg b.nonneg]; exact b.le_one
  have huv : ∀ z : ℂ, ‖cValue u z‖ ≤ 1 := fun z => (c_value_bound u z).trans hu
  have hul : ∀ x y : ℂ, ‖cValue u x-cValue u y‖ ≤ dist x y := by
    intro x y
    have hd : ∀ z, ‖fderiv ℝ (cValue u) z‖ ≤ (1:ℝ) := fun z => by
      rw [c_fderiv]; exact (c_deriv_bound u z).trans hu
    simpa only [one_mul,dist_eq_norm] using norm_sub_le_of_deriv_bound (c_differentiable u) hd x y
  have hbl : ∀ x y : ℂ, ‖b x-b y‖ ≤ hb.bound*dist x y := by
    intro x y
    simpa only [dist_eq_norm] using norm_sub_le_of_deriv_bound
      (b.contDiff.differentiable (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top : (∞ : WithTop ℕ∞) ≠ 0)) hb.norm_fderiv_le x y
  refine ⟨?_,?_,?_⟩
  · intro z
    rw [localizedJetValue_apply,norm_smul]
    calc
      _ ≤ (1:ℝ)*1 := mul_le_mul (hbu z) (huv z) (norm_nonneg _) zero_le_one
      _ = 1 := one_mul _
  · intro x y
    change ‖b x • cValue u x-b y • cValue u y‖ ≤ (1+hb.bound)*dist x y
    have he : b x • cValue u x-b y • cValue u y =
        b x • (cValue u x-cValue u y)+(b x-b y) • cValue u y := by module
    rw [he]
    calc
      _ ≤ ‖b x • (cValue u x-cValue u y)‖+‖(b x-b y) • cValue u y‖ := norm_add_le _ _
      _ = ‖b x‖*‖cValue u x-cValue u y‖+‖b x-b y‖*‖cValue u y‖ := by rw [norm_smul,norm_smul]
      _ ≤ 1*dist x y+(hb.bound*dist x y)*1 := add_le_add
        (mul_le_mul (hbu x) (hul x y) (norm_nonneg _) zero_le_one)
        (mul_le_mul (hbl x y) (huv y) (norm_nonneg _) (by positivity [hb.bound_nonneg]))
      _ = _ := by ring
  · intro z hz
    rw [localizedJetValue_apply,b.zero_of_le_dist (by
      simp only [Metric.mem_closedBall] at hz
      exact (lt_of_not_ge hz).le),zero_smul]

lemma localizedJetValue_isCompact [ProperSpace E] : IsCompactOperator (localizedJetValue (E := E) b) := by
  let hb := boundedCThree_of_compactSupport b.contDiff b.hasCompactSupport
  have ht := lipHolderSet_totallyBounded (E := E) (isCompact_closedBall (0:ℂ) b.rOut) 1
    (show 0 ≤ 1+hb.bound by linarith [hb.bound_nonneg])
  have hT : TotallyBounded (localizedJetValue (E := E) b '' Metric.closedBall 0 1) := ht.subset (by
    rintro _ ⟨u,hu,rfl⟩
    exact localizedJetValue_bounds b u (by simpa only [Metric.mem_closedBall,dist_zero_right] using hu))
  apply (isCompactOperator_iff_exists_mem_nhds_isCompact_closure_image
    (localizedJetValue (E := E) b)).mpr
  exact ⟨Metric.closedBall 0 1,Metric.closedBall_mem_nhds _ (by norm_num),
    hT.closure.isCompact_of_isClosed isClosed_closure⟩



end HigherDimensionalBallPacking.Rigidity.HolderCompletion
end

end OAI
end

section
-- module Solutions.OAIQ240_BP.BallPacking_Fredholm_FiniteExtensions
attribute [-instance] _root_.OAI.PackingSufficiencySupport.Hamiltonian.flatProduct_chartedSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace HigherDimensionalBallPacking.Rigidity

section
open scoped ContDiff Topology BoundedContinuousFunction
open Set Filter
namespace HolderCompletion
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [completeSpaceE : CompleteSpace E]

attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.zeroOrderInst1
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.zeroOrderInst2
local instance zeroOrderInst3_rf89b68_1 : NormedAddCommGroup (COne ℂ E) := inferInstance
local instance zeroOrderInst4_rf89b68_1 : NormedSpace ℝ (COne ℂ E) := inferInstance
local instance zeroOrderInst5_rf89b68_1 : NormedAddCommGroup (HMap ℂ E) := inferInstance
local instance zeroOrderInst6_rf89b68_1 : NormedSpace ℝ (HMap ℂ E) := inferInstance
omit completeSpaceE in
lemma jetZeroOrder_eq_localized [CompleteSpace E]
    (C : HMap ℂ (E →L[ℝ] E)) (b : ContDiffBump (0:ℂ))
    (hC : ∀ z ∉ Metric.closedBall (0:ℂ) b.rIn, valueCLM _ C z = 0) :
    jetZeroOrder C = (holderCoefficientAction C).comp (localizedJetValue b) := by
  apply ContinuousLinearMap.ext
  intro u
  apply value_ext
  intro z
  change valueCLM _ C z (cValue u z) = valueCLM _ C z (b z • cValue u z)
  by_cases hz : z ∈ Metric.closedBall (0:ℂ) b.rIn
  · rw [b.one_of_mem_closedBall hz,one_smul]
  · rw [hC z hz,zero_apply,zero_apply]

lemma jetZeroOrder_isCompact_bp240_oai [ProperSpace E] (C : HMap ℂ (E →L[ℝ] E))
    (b : ContDiffBump (0:ℂ))
    (hC : ∀ z ∉ Metric.closedBall (0:ℂ) b.rIn, valueCLM _ C z = 0) :
    IsCompactOperator (jetZeroOrder C) := by
  rw [jetZeroOrder_eq_localized C b hC]
  exact (localizedJetValue_isCompact (E := E) b).clm_comp (holderCoefficientAction C)

end HolderCompletion

end

end HigherDimensionalBallPacking.Rigidity
end

end OAI
end

theorem solution.{u_1} : type_of% @OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.jetZeroOrder_isCompact_bp240_oai.{u_1} := @OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.jetZeroOrder_isCompact_bp240_oai.{u_1}
