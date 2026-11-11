-- Prove2me | solution 1 for OAI.HigherDimensionalBallPacking.Rigidity.exact_marked_zeroSet_compact_bp240
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T01:55:57.800703+00:00
-- url     : https://prove2.me/submissions/4dffc8cc-2470-41ce-a1a5-9fe8e6d035ae

import Mathlib
import Definitions.Def_BallPacking
import Definitions.Def_OAIQ240Bp021
import Theorems.Thm_OAI_HigherDimensionalBallPacking_Rigidity_HolderCompletion_supportedHolder_closed_bp240
import Theorems.Thm_OAI_HigherDimensionalBallPacking_Rigidity_completed_line_closed_bp240
import Theorems.Thm_OAI_HigherDimensionalBallPacking_Rigidity_exact_marked_line_czero_compactness_bp240
import Theorems.Thm_OAI_HigherDimensionalBallPacking_Rigidity_exact_marked_line_uniform_defect_support_bp240
import Theorems.Thm_OAI_HigherDimensionalBallPacking_Rigidity_exact_marked_local_jet_cauchy_bp240

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

attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.instNormedAddCommGroupSubtypeJetAmbientHDivRealOfNatMemSubmoduleCOne_1
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.instNormedSpaceRealSubtypeJetAmbientHDivOfNatMemSubmoduleCOne_1
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.instNormedAddCommGroupSubtypeJetAmbientHDivRealOfNatMemSubmoduleCOne_2
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.instNormedSpaceRealSubtypeJetAmbientHDivOfNatMemSubmoduleCOne_2
local instance instNormedAddCommGroupContinuousLinearMapRealIdSubtypeJetAmbientHDivOfNatMemSubmoduleCOne_r117b4f_1 : NormedAddCommGroup (COne D E →L[ℝ] COne D F) := ContinuousLinearMap.toNormedAddCommGroup
local instance instNormedSpaceRealContinuousLinearMapIdSubtypeJetAmbientHDivOfNatMemSubmoduleCOne_r117b4f_1 : NormedSpace ℝ (COne D E →L[ℝ] COne D F) := ContinuousLinearMap.toNormedSpace
instance instCompleteSpaceSubtypeAmbientMemSubmoduleRealHMapSupportedHolder (K : Set D) [CompleteSpace E] : CompleteSpace (supportedHolder (E := E) K) :=
  (supportedHolder_closed_bp240 K).completeSpace_coe

end HolderCompletion

end

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

theorem lineHomotopy_support {n : ℕ} (J : Phase n → End n)
    {t : ℝ} (ht : t ∈ Icc (0:ℝ) 1) :
    tsupport (fun x => lineHomotopy J t x - standardJ n) ⊆
      tsupport (fun x => J x - standardJ n) := by
  apply closure_minimal _ (isClosed_tsupport _)
  intro x hx
  by_contra hn
  have hzero := image_eq_zero_of_notMem_tsupport hn
  have hJx : J x = standardJ n := sub_eq_zero.mp hzero
  apply hx
  change interpolateJ (J x) t - standardJ n = 0
  rw [hJx,interpolateJ_standard ht,sub_self]

theorem lineHomotopy_compact {n : ℕ} {J : Phase n → End n}
    (hJc : HasCompactSupport (fun x => J x - standardJ n))
    {t : ℝ} (ht : t ∈ Icc (0:ℝ) 1) :
    HasCompactSupport (fun x => lineHomotopy J t x - standardJ n) :=
  hJc.of_isClosed_subset (isClosed_tsupport _) (lineHomotopy_support J ht)


end

open scoped ContDiff Topology
open Set Function Filter MeasureTheory



end HigherDimensionalBallPacking.Rigidity
end

end OAI
end

section
-- module Solutions.OAIQ240_BP.BallPacking_Rigidity_RadialForm
attribute [-instance] _root_.OAI.PackingSufficiencySupport.Hamiltonian.flatProduct_chartedSpace
attribute [-simp] _root_.OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.compatibleFrameJet_value _root_.OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.compatibleFrame_apply _root_.OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.compatibleInverseJet_value _root_.OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.completedDX_value _root_.OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.completedFrameJet_value _root_.OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.completedInverseJet_value _root_.OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.completedPrincipal_value _root_.OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.completedQ_value _root_.OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.completedStructureJet_value _root_.OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.curveMarkCoefficientHolder_value _root_.OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.curveMarkCoefficient_apply _root_.OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.curveZeroOrderHolder_value _root_.OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.curveZeroOrder_apply _root_.OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.frozenTargetCoefficient_zero _root_.OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.smoothMarkedPrincipal_value _root_.OAI.HigherDimensionalBallPacking.Rigidity.geometricHolder_value _root_.OAI.HigherDimensionalBallPacking.Rigidity.normalizedPrimitive_apply _root_.OAI.HigherDimensionalBallPacking.Rigidity.realCurve_zero _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.infinity_end_count _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.sqrt_sq_complex
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace HigherDimensionalBallPacking.Rigidity
open scoped ContDiff Topology
open Set Function Filter MeasureTheory

theorem linear_asymptotic_norm_tendsto {n : ℕ} {u : ℂ → Phase n} {v : Phase n}
    (hv : v ≠ 0) (hlim : Tendsto (fun z : ℂ => z⁻¹ • u z) (cocompact ℂ) (𝓝 v)) :
    Tendsto (fun z => ‖u z‖) (cocompact ℂ) atTop := by
  have hp : 0 < ‖v‖ := norm_pos_iff.mpr hv
  have hev : ∀ᶠ z : ℂ in cocompact ℂ, ‖v‖ / 2 < ‖z⁻¹ • u z‖ :=
    (tendsto_order.mp hlim.norm).1 _ (by linarith)
  have hb : (fun z : ℂ => (‖v‖ / 2) * ‖z‖) ≤ᶠ[cocompact ℂ] fun z => ‖u z‖ := by
    filter_upwards [hev,(isCompact_singleton (x := (0:ℂ))).compl_mem_cocompact] with z hz hz0
    have hn : 0 < ‖z‖ := norm_pos_iff.mpr (by simpa using hz0)
    rw [norm_smul,norm_inv,inv_mul_eq_div] at hz
    exact ((lt_div_iff₀ hn).mp hz).le
  exact tendsto_atTop_mono' _ hb
    (Tendsto.const_mul_atTop (by linarith : 0 < ‖v‖ / 2) tendsto_norm_cocompact_atTop)

theorem AffineLineCurve.tendsto_cocompact {n : ℕ} {J : Phase n → End n}
    {p q : Phase n} {u : ℂ → Phase n} (hu : AffineLineCurve J p q u) :
    Tendsto u (cocompact ℂ) (cocompact (Phase n)) := by
  obtain ⟨v,hv,hlim⟩ := hu.2.2.2.2
  rw [←Metric.cobounded_eq_cocompact (α := Phase n),←tendsto_norm_atTop_iff_cobounded]
  exact linear_asymptotic_norm_tendsto hv hlim

theorem AffineLineCurve.isProperMap {n : ℕ} {J : Phase n → End n}
    {p q : Phase n} {u : ℂ → Phase n} (hu : AffineLineCurve J p q u) : IsProperMap u :=
  isProperMap_iff_tendsto_cocompact.mpr ⟨hu.1.continuous,hu.tendsto_cocompact⟩

end HigherDimensionalBallPacking.Rigidity

end

end OAI
end

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

local instance markedAffineInst1_r117b4f_1 : NormedAddCommGroup (COne ℂ E) := inferInstance
local instance markedAffineInst2_r117b4f_1 : NormedSpace ℝ (COne ℂ E) := inferInstance
local instance markedAffineInst3_r117b4f_1 : NormedAddCommGroup (HMap ℂ E) := inferInstance
local instance markedAffineInst4_r117b4f_1 : NormedSpace ℝ (HMap ℂ E) := inferInstance
local instance markedAffineInst5_r117b4f_1 : NormedAddCommGroup (markedModel (E := E) K) := inferInstance
local instance markedAffineInst6_r117b4f_1 : NormedSpace ℝ (markedModel (E := E) K) := inferInstance
local instance markedAffineInst7_r117b4f_1 : NormedAddCommGroup (supportedHolder (E := E) K) := inferInstance
local instance markedAffineInst8_r117b4f_1 : NormedSpace ℝ (supportedHolder (E := E) K) := inferInstance
omit [CompleteSpace E] in
lemma markedSlope_continuous (p q : E) : Continuous (markedSlope p q : COne ℂ E → E) :=
  continuous_const.sub (jetEval (E := E) 1).continuous

omit [CompleteSpace E] in
lemma markedCurve_asymptote (p q : E) (u : COne ℂ E) :
    Tendsto (fun z : ℂ => z⁻¹ • markedCurve p q u z) (cocompact ℂ)
      (𝓝 (markedSlope p q u)) := by
  have hi : Tendsto (fun z : ℂ => z⁻¹) (cocompact ℂ) (𝓝 0) := by
    simpa only [← Metric.cobounded_eq_cocompact] using (tendsto_inv₀_cobounded (α := ℂ))
  have hb : IsBoundedUnder (· ≤ ·) (cocompact ℂ) (norm ∘ (cValue u : ℂ → E)) :=
    ⟨‖cValue u‖, eventually_map.mpr (Eventually.of_forall fun z => (cValue u).norm_coe_le_norm z)⟩
  have hzero := hi.zero_smul_isBoundedUnder_le hb
  have ht := ((hi.smul_const p).add_const (markedSlope p q u)).add hzero
  simp only [zero_smul,zero_add,add_zero] at ht
  apply ht.congr'
  filter_upwards [(isCompact_singleton (x := (0:ℂ))).compl_mem_cocompact] with z hz
  have hz0 : z ≠ 0 := by simpa only [mem_compl_iff,mem_singleton_iff] using hz
  simp only [markedCurve,smul_add,smul_smul,inv_mul_cancel₀ hz0,one_smul]



end HigherDimensionalBallPacking.Rigidity.HolderCompletion
end

end OAI
end

section
-- module Solutions.OAIQ240_BP.BallPacking_Compactness_AffineCorrectionInfinity
attribute [-instance] _root_.OAI.PackingSufficiencySupport.Hamiltonian.flatProduct_chartedSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped Topology
open Set Filter
namespace HigherDimensionalBallPacking.Rigidity.HolderCompletion
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]

lemma entire_affine_of_asymptote {f : ℂ → E} (hf : Differentiable ℂ f) {a : E}
    (ha : Tendsto (fun z : ℂ => z⁻¹ • f z) (cocompact ℂ) (𝓝 a)) (z : ℂ) :
    f z=f 0+z • a := by
  have hs : Differentiable ℂ (dslope f 0) :=
    differentiableOn_univ.mp ((Complex.differentiableOn_dslope (s := univ) (c := (0:ℂ))
      univ_mem).mpr hf.differentiableOn)
  have hi : Tendsto (fun w : ℂ => w⁻¹) (cocompact ℂ) (𝓝 0) := by
    simpa only [←Metric.cobounded_eq_cocompact] using (tendsto_inv₀_cobounded (α := ℂ))
  have ht : Tendsto (dslope f 0) (cocompact ℂ) (𝓝 a) := by
    have hsub := ha.sub (hi.smul_const (f 0))
    simp only [zero_smul,sub_zero] at hsub
    apply hsub.congr'
    filter_upwards [(isCompact_singleton (x := (0:ℂ))).compl_mem_cocompact] with w hw
    have hw0 : w≠0 := by simpa only [mem_compl_iff,mem_singleton_iff] using hw
    rw [dslope_of_ne f hw0,slope_def_module,sub_zero,smul_sub]
  have hvalue := sub_smul_dslope f 0 z
  rw [sub_zero,hs.apply_eq_of_tendsto_cocompact z ht] at hvalue
  exact (sub_eq_iff_eq_add.mp hvalue.symm).trans (add_comm _ _)

end HigherDimensionalBallPacking.Rigidity.HolderCompletion

end

end OAI
end

section
-- module Solutions.OAIQ240_BP.BallPacking_Compactness_FrozenCR
attribute [-instance] _root_.OAI.PackingSufficiencySupport.Hamiltonian.flatProduct_chartedSpace
attribute [-simp] _root_.OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.completedDX_value _root_.OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.completedFrameJet_value _root_.OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.completedInverseJet_value _root_.OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.completedPrincipal_value _root_.OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.completedQ_value _root_.OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.completedStructureJet_value _root_.OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.curveMarkCoefficientHolder_value _root_.OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.curveMarkCoefficient_apply _root_.OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.curveZeroOrderHolder_value _root_.OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.curveZeroOrder_apply _root_.OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.smoothMarkedPrincipal_value _root_.OAI.HigherDimensionalBallPacking.Rigidity.geometricHolder_value _root_.OAI.HigherDimensionalBallPacking.Rigidity.normalizedPrimitive_apply _root_.OAI.HigherDimensionalBallPacking.Rigidity.realCurve_zero _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.infinity_end_count _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.sqrt_sq_complex
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace HigherDimensionalBallPacking.Rigidity
open scoped ContDiff Topology
open Set Filter
open HolderCompletion
open scoped BoundedContinuousFunction

variable {n : ℕ}

local instance ecgInst1_r117b4f_1 : NormedAddCommGroup (End n) := ContinuousLinearMap.toNormedAddCommGroup
local instance ecgInst2_r117b4f_1 : NormedSpace ℝ (End n) := ContinuousLinearMap.toNormedSpace
lemma rescaledCurve_fderiv {u : ℂ → Phase n} (hu : ContDiff ℝ ∞ u) (y : ℂ) (r : ℝ) (z : ℂ) :
    fderiv ℝ (rescaledCurve u y r) z=r • fderiv ℝ u (y+r • z) := by
  have hh := (hu.differentiable (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top) (y+r • z)).hasFDerivAt.comp z
    (((ContinuousLinearMap.id ℝ ℂ).hasFDerivAt.const_smul r).const_add y)
  have he : (fderiv ℝ u (y+r • z)).comp (r • ContinuousLinearMap.id ℝ ℂ)=
      r • fderiv ℝ u (y+r • z) := by ext h; simp only [ContinuousLinearMap.comp_apply,smul_apply,ContinuousLinearMap.id_apply,map_smul]
  rw [he] at hh
  exact hh.fderiv

end HigherDimensionalBallPacking.Rigidity

end

end OAI
end

section
-- module Solutions.OAIQ240_BP.BallPacking_Fredholm_TranslationContinuity
attribute [-instance] _root_.OAI.PackingSufficiencySupport.Hamiltonian.flatProduct_chartedSpace
attribute [-simp] _root_.OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.frozenTargetCoefficient_zero _root_.OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.realConstantJet_value _root_.OAI.HigherDimensionalBallPacking.Rigidity.geometricHolder_value _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.infinity_end_count _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.sqrt_sq_complex
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace HigherDimensionalBallPacking.Rigidity.HolderCompletion
open scoped ContDiff Topology BoundedContinuousFunction
open Set Function Filter

variable {n : ℕ}

local instance gcInst1_r117b4f_1 : NormedAddCommGroup (End n) := ContinuousLinearMap.toNormedAddCommGroup
local instance gcInst2_r117b4f_1 : NormedSpace ℝ (End n) := ContinuousLinearMap.toNormedSpace
local instance gcInst3_r117b4f_1 : NormedAddCommGroup (COne ℂ (Phase n)) := inferInstance
local instance gcInst4_r117b4f_1 : NormedSpace ℝ (COne ℂ (Phase n)) := inferInstance
local instance gcInst5_r117b4f_1 : NormedAddCommGroup (HMap ℂ (Phase n)) := inferInstance
local instance gcInst6_r117b4f_1 : NormedSpace ℝ (HMap ℂ (Phase n)) := inferInstance
local instance gcInst7_r117b4f_1 (K : Set ℂ) : NormedAddCommGroup (markedModel (E := Phase n) K) := inferInstance
local instance gcInst8_r117b4f_1 (K : Set ℂ) : NormedSpace ℝ (markedModel (E := Phase n) K) := inferInstance
local instance gcInst9_r117b4f_1 (K : Set ℂ) : NormedAddCommGroup (supportedHolder (E := Phase n) K) := inferInstance
local instance gcInst10_r117b4f_1 (K : Set ℂ) : NormedSpace ℝ (supportedHolder (E := Phase n) K) := inferInstance
lemma geometricResidual_compact {J : Phase n → End n} {p q : Phase n} {u : ℂ → Phase n}
    (hu : AffineLineCurve J p q u) (hJc : HasCompactSupport (fun x => J x-standardJ n)) :
    HasCompactSupport (geometricResidual u) := by
  apply HasCompactSupport.of_support_subset_isCompact (hu.isProperMap.isCompact_preimage hJc)
  intro z hz
  by_contra hn
  have hstd : J (u z)=standardJ n := sub_eq_zero.mp
    (image_eq_zero_of_notMem_tsupport (f := fun x => J x-standardJ n) hn)
  have hcr := (hu.2.1 z).2 1
  simp only [mul_one,hstd] at hcr
  apply hz
  exact sub_eq_zero.mpr hcr

lemma inverse_correction_holomorphic {u : ℂ → Phase n} (hu : ContDiff ℝ ∞ u)
    {K : Set ℂ} (hK : IsCompact K) (g : supportedHolder (E := Phase n) K)
    (hg : ∀ z, valueCLM _ g.val z=geometricResidual u z) :
    Differentiable ℂ (fun z => u z-cValue (standardHolderInverse hK g) z) := by
  let v := standardHolderInverse hK g
  intro z
  have hd := ((hu.differentiable (by simp)) z).hasFDerivAt.sub (c_hasFDerivAt v z)
  apply complex_differentiable_of_curl_zero hd.differentiableAt
  have hres : cDeriv v z Complex.I-Complex.I • cDeriv v z 1=geometricResidual u z := by
    have he := congrArg (fun w : HMap ℂ (Phase n) => valueCLM _ w z)
      (standardHolderInverse_residual hK g)
    simpa only [standardJetCR_value] using he.trans (hg z)
  rw [hd.fderiv]
  change Complex.I • (fderiv ℝ u z 1-cDeriv v z 1)-
    (fderiv ℝ u z Complex.I-cDeriv v z Complex.I)=0
  rw [smul_sub]
  calc
    _ = (cDeriv v z Complex.I-Complex.I • cDeriv v z 1)-geometricResidual u z := by
      unfold geometricResidual
      abel
    _ = 0 := sub_eq_zero.mpr hres

lemma inverse_correction_asymptote {u : ℂ → Phase n} {a : Phase n}
    (ha : Tendsto (fun z : ℂ => z⁻¹ • u z) (cocompact ℂ) (𝓝 a))
    (v : COne ℂ (Phase n)) :
    Tendsto (fun z : ℂ => z⁻¹ • (u z-cValue v z)) (cocompact ℂ) (𝓝 a) := by
  have hi : Tendsto (fun z : ℂ => z⁻¹) (cocompact ℂ) (𝓝 0) := by
    simpa only [←Metric.cobounded_eq_cocompact] using (tendsto_inv₀_cobounded (α := ℂ))
  have hb : IsBoundedUnder (· ≤ ·) (cocompact ℂ) (norm ∘ (cValue v : ℂ → Phase n)) :=
    ⟨‖cValue v‖,eventually_map.mpr (Eventually.of_forall fun z => (cValue v).norm_coe_le_norm z)⟩
  simpa only [smul_sub,sub_zero] using ha.sub (hi.zero_smul_isBoundedUnder_le hb)

lemma affine_reconstruction_from_correction {u : ℂ → Phase n} {p a : Phase n}
    (v : COne ℂ (Phase n))
    (hd : Differentiable ℂ (fun z => u z-cValue v z))
    (ha : Tendsto (fun z : ℂ => z⁻¹ • (u z-cValue v z)) (cocompact ℂ) (𝓝 a))
    (h0 : u 0=p) (hv0 : cValue v 0=0) (z : ℂ) :
    u z=p+z • a+cValue v z := by
  have he := entire_affine_of_asymptote hd ha z
  rw [h0,hv0,sub_zero] at he
  exact sub_eq_iff_eq_add.mp he

lemma marked_reconstruction_from_correction {u : ℂ → Phase n} {p q a : Phase n}
    (v : COne ℂ (Phase n))
    (hd : Differentiable ℂ (fun z => u z-cValue v z))
    (ha : Tendsto (fun z : ℂ => z⁻¹ • u z) (cocompact ℂ) (𝓝 a))
    (h0 : u 0=p) (h1 : u 1=q) (hv0 : cValue v 0=0) :
    markedCurve p q v=u ∧ markedSlope p q v=a := by
  have hinf := inverse_correction_asymptote ha v
  have hrec := affine_reconstruction_from_correction v hd hinf h0 hv0
  have hslope : markedSlope p q v=a := by
    have he := hrec 1
    rw [h1,one_smul] at he
    rw [markedSlope,he]
    abel
  refine ⟨?_,hslope⟩
  funext z
  rw [markedCurve,hslope]
  exact (hrec z).symm

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

namespace HigherDimensionalBallPacking.Rigidity.HolderCompletion
open scoped Topology BoundedContinuousFunction
open Set Filter
variable {X E : Type*} [MetricSpace X] [NormedAddCommGroup E] [NormedSpace ℝ E]

local instance chpInst1_r117b4f_1 : NormedAddCommGroup (HMap X E) := inferInstance
local instance chpInst2_r117b4f_1 : NormedSpace ℝ (HMap X E) := inferInstance
lemma compact_local_holder_cauchy {K : Set X} (hK : IsCompact K) {ρ : ℝ} (hρ : 0<ρ)
    {g : ℕ → HMap X E} (hg : ∀ i x,x∉K →valueCLM _ (g i) x=0)
    (hl : ∀ c : X,∀ ε : ℝ,0<ε →∃ N : ℕ,∀ i≥N,∀ j≥N,
      (∀ x,dist x c<ρ →‖valueCLM _ (g i-g j) x‖≤ε) ∧
      (∀ x y,dist x c<ρ →dist y c<ρ →
        ‖valueCLM _ (g i-g j) x-valueCLM _ (g i-g j) y‖≤ε*dist x y^((1:ℝ)/3))) :
    CauchySeq g := by
  classical
  rw [Metric.cauchySeq_iff]
  intro ε hε
  let δ := ρ/2
  have hδ : 0<δ := half_pos hρ
  have hdα : 0<δ^((1:ℝ)/3) := Real.rpow_pos_of_pos hδ _
  let e := min (ε/2) (ε/4*δ^((1:ℝ)/3))
  have he : 0<e := lt_min (half_pos hε) (mul_pos (by positivity) hdα)
  obtain ⟨a,_,ha,hcover⟩ := hK.finite_cover_balls hδ
  choose N hN using fun c => hl c e he
  let m := ha.toFinset.sup N
  have hm {c : X} (hc : c∈a) : N c ≤ m := Finset.le_sup (ha.mem_toFinset.mpr hc)
  refine ⟨m,fun i hi j hj => ?_⟩
  have hchoose {x : X} (hx : x∈K) : ∃ c∈a,dist x c<δ := by
    have hh := hcover hx
    simp only [mem_iUnion] at hh
    obtain ⟨c,hc,hxc⟩ := hh
    exact ⟨c,hc,hxc⟩
  have hv (x : X) : ‖valueCLM _ (g i-g j) x‖≤e := by
    by_cases hx : x∈K
    · obtain ⟨c,hc,hxc⟩ := hchoose hx
      exact (hN c i ((hm hc).trans hi) j ((hm hc).trans hj)).1 x (by dsimp [δ] at hxc <;> linarith)
    · change ‖valueCLM _ (g i) x-valueCLM _ (g j) x‖≤e
      rw [hg i x hx,hg j x hx,sub_self,norm_zero]
      exact he.le
  have hnear {x y : X} (hx : x∈K) (hxy : dist x y<δ) :
      ‖valueCLM _ (g i-g j) x-valueCLM _ (g i-g j) y‖≤(ε/2)*dist x y^((1:ℝ)/3) := by
    obtain ⟨c,hc,hxc⟩ := hchoose hx
    have hyc : dist y c<ρ := by
      have ht := dist_triangle y x c
      rw [dist_comm y x] at ht
      dsimp [δ] at hxy hxc
      linarith
    have hh := (hN c i ((hm hc).trans hi) j ((hm hc).trans hj)).2 x y
      (by dsimp [δ] at hxc <;> linarith) hyc
    exact hh.trans (mul_le_mul_of_nonneg_right (min_le_left _ _) (Real.rpow_nonneg (dist_nonneg) _))
  have hh (x y : X) :
      ‖valueCLM _ (g i-g j) x-valueCLM _ (g i-g j) y‖≤(ε/2)*dist x y^((1:ℝ)/3) := by
    by_cases hxy : dist x y<δ
    · by_cases hx : x∈K
      · exact hnear hx hxy
      by_cases hy : y∈K
      · have hn := hnear hy (by rwa [dist_comm] : dist y x<δ)
        rw [norm_sub_rev,dist_comm y x] at hn
        exact hn
      · change ‖(valueCLM _ (g i) x-valueCLM _ (g j) x)-
          (valueCLM _ (g i) y-valueCLM _ (g j) y)‖≤_
        simp only [hg i x hx,hg j x hx,hg i y hy,hg j y hy,sub_self,norm_zero]
        positivity
    · have hpow : δ^((1:ℝ)/3)≤dist x y^((1:ℝ)/3) :=
        Real.rpow_le_rpow hδ.le (le_of_not_gt hxy) (by norm_num)
      have he2 : 2*e≤(ε/2)*δ^((1:ℝ)/3) := by
        have hi := min_le_right (ε/2) (ε/4*δ^((1:ℝ)/3))
        dsimp [e]
        nlinarith
      exact (norm_sub_le _ _).trans ((add_le_add (hv x) (hv y)).trans
        ((by linarith : e+e≤(ε/2)*δ^((1:ℝ)/3)).trans
          (mul_le_mul_of_nonneg_left hpow (half_pos hε).le)))
  have hnorm := norm_le_of_bounds (g i-g j) (half_pos hε).le (half_pos hε).le
    (fun x => (hv x).trans (min_le_left _ _)) hh
  rw [max_self] at hnorm
  rw [dist_eq_norm]
  exact hnorm.trans_lt (half_lt_self hε)

end HigherDimensionalBallPacking.Rigidity.HolderCompletion

namespace HigherDimensionalBallPacking.Rigidity
open scoped ContDiff Topology
open Set Function Filter MeasureTheory
open scoped BoundedContinuousFunction
open HolderCompletion
variable {n : ℕ}

attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.lrInst1
local instance lrInst2_r117b4f_1 : NormedSpace ℝ (COne ℂ (Phase n)) := inferInstance
local instance lrInst3_r117b4f_1 : NormedAddCommGroup (HMap ℂ (Phase n)) := inferInstance
local instance lrInst4_r117b4f_1 : NormedSpace ℝ (HMap ℂ (Phase n)) := inferInstance
lemma cutoffCurveJet_local_fderiv {u : ℂ → Phase n} (hu : ContDiff ℝ ∞ u)
    (b : ContDiffBump (0:ℂ)) {z : ℂ} (hz : ‖z‖<b.rIn) :
    cDeriv (cutoffCurveJet b hu) z=fderiv ℝ u z := by
  rw [←c_fderiv]
  have hb := b.eventuallyEq_one_of_mem_ball (by simpa only [Metric.mem_ball,dist_zero_right] using hz)
  have he : (cValue (cutoffCurveJet b hu) : ℂ → Phase n)=ᶠ[𝓝 z] u := by
    filter_upwards [hb] with w hw
    rw [cutoffCurveJet_value,hw]
    exact one_smul ℝ (u w)
  exact he.fderiv_eq

lemma localResidual_value {u : ℂ → Phase n} (hu : ContDiff ℝ ∞ u)
    (c : ℂ) (r : ℝ) {z : ℂ} (hz : ‖z‖<(1:ℝ)/4) :
    valueCLM _ (localResidual hu c r) z=r • geometricResidual u (c+r • z) := by
  rw [localResidual,standardJetCR_value,cutoffCurveJet_local_fderiv (markedLocalCurve_smooth hu c r) smallDiskBump hz]
  have he : fderiv ℝ (markedLocalCurve u c r) z=fderiv ℝ (rescaledCurve u c r) z := by
    exact (((rescaledCurve_smooth hu c r).differentiable (by simp) z).hasFDerivAt.sub_const (u c)).fderiv
  rw [he,rescaledCurve_fderiv hu]
  simp only [smul_apply,geometricResidual,smul_sub]
  rw [smul_comm Complex.I r]

lemma localResidual_at_original {u : ℂ → Phase n} (hu : ContDiff ℝ ∞ u)
    (c : ℂ) {r : ℝ} (hr : 0 < r) {x : ℂ} (hx : dist x c < r/4) :
    geometricResidual u x=r⁻¹ • valueCLM _ (localResidual hu c r) (r⁻¹ • (x-c)) := by
  have hz : ‖r⁻¹ • (x-c)‖<(1:ℝ)/4 := by
    rw [norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr hr),←dist_eq_norm]
    apply (inv_mul_lt_iff₀ hr).mpr
    linarith
  rw [localResidual_value hu c r hz,inv_smul_smul₀ hr.ne',smul_inv_smul₀ hr.ne',add_sub_cancel]

lemma localResidual_cauchy {u : ℕ → ℂ → Phase n} (hu : ∀ i,ContDiff ℝ ∞ (u i))
    (c : ℂ) (r : ℝ)
    (hc : CauchySeq (fun i => cutoffCurveJet smallDiskBump (markedLocalCurve_smooth (hu i) c r))) :
    CauchySeq (fun i => localResidual (hu i) c r) :=
  (standardJetCR (E := Phase n)).uniformContinuous.comp_cauchySeq hc

end HigherDimensionalBallPacking.Rigidity
end

end OAI
end

section
-- module Solutions.OAIQ240_BP.BallPacking_Compactness_ResidualCauchy
attribute [-instance] _root_.OAI.PackingSufficiencySupport.Comparison.convexMaps_nonempty _root_.OAI.PackingSufficiencySupport.FiniteMoment.Radial.instInhabitedQuadrant _root_.OAI.PackingSufficiencySupport.Hamiltonian.flatProduct_chartedSpace
attribute [-simp] _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.infinity_end_count _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.sqrt_sq_complex
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
open HolderCompletion
variable {n : ℕ}

lemma affineSource_distance (c x y : ℂ) {r : ℝ} (hr : 0 < r) :
    dist (r⁻¹ • (x-c)) (r⁻¹ • (y-c))=r⁻¹*dist x y := by
  rw [dist_eq_norm,←smul_sub]
  have he : (x-c)-(y-c)=x-y := by abel
  rw [he,norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr hr),dist_eq_norm]

attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.grcInst1
local instance grcInst2_r117b4f_1 : NormedSpace ℝ (HMap ℂ (Phase n)) := inferInstance
lemma residual_difference_pullback {u : ℕ → ℂ → Phase n} (hu : ∀ i,ContDiff ℝ ∞ (u i))
    {g : ℕ → HMap ℂ (Phase n)} (hg : ∀ i z,valueCLM _ (g i) z=geometricResidual (u i) z)
    (c : ℂ) {r : ℝ} (hr : 0 < r) (i j : ℕ) {x : ℂ} (hx : dist x c < r/4) :
    valueCLM _ (g i-g j) x=r⁻¹ •
      valueCLM _ (localResidual (hu i) c r-localResidual (hu j) c r) (r⁻¹ • (x-c)) := by
  change valueCLM _ (g i) x-valueCLM _ (g j) x=_
  rw [hg,hg,localResidual_at_original (hu i) c hr hx,localResidual_at_original (hu j) c hr hx,←smul_sub]
  rfl

lemma local_residual_small_differences {u : ℕ → ℂ → Phase n} (hu : ∀ i,ContDiff ℝ ∞ (u i))
    {g : ℕ → HMap ℂ (Phase n)} (hg : ∀ i z,valueCLM _ (g i) z=geometricResidual (u i) z)
    (c : ℂ) {r : ℝ} (hr : 0 < r)
    (hlocal : CauchySeq (fun i => localResidual (hu i) c r)) :
    ∀ ε : ℝ,0<ε →∃ N : ℕ,∀ i≥N,∀ j≥N,
      (∀ x,dist x c < r/4 →‖valueCLM _ (g i-g j) x‖≤ε) ∧
      (∀ x y,dist x c < r/4 →dist y c < r/4 →
        ‖valueCLM _ (g i-g j) x-valueCLM _ (g i-g j) y‖≤ε*dist x y^((1:ℝ)/3)) := by
  intro ε hε
  let a := r⁻¹
  have ha : 0<a := inv_pos.mpr hr
  have haα : 0<a^((1:ℝ)/3) := Real.rpow_pos_of_pos ha _
  let C := a+a*a^((1:ℝ)/3)+1
  have hC : 0<C := by dsimp [C] <;> positivity
  have hCa : a≤C := by dsimp [C] <;> nlinarith [mul_nonneg ha.le haα.le]
  have hCap : a*a^((1:ℝ)/3)≤C := by dsimp [C] <;> linarith
  obtain ⟨N,hN⟩ := Metric.cauchySeq_iff.mp hlocal (ε/C) (div_pos hε hC)
  refine ⟨N,fun i hi j hj => ?_⟩
  let v := localResidual (hu i) c r-localResidual (hu j) c r
  have hv : ‖v‖≤ε/C := by simpa only [dist_eq_norm] using (hN i hi j hj).le
  have haV : a*‖v‖≤ε := by
    calc
      a*‖v‖≤C*‖v‖ := mul_le_mul_of_nonneg_right hCa (norm_nonneg v)
      _≤C*(ε/C) := mul_le_mul_of_nonneg_left hv hC.le
      _=ε := mul_div_cancel₀ ε hC.ne'
  have hapV : (a*a^((1:ℝ)/3))*‖v‖≤ε := by
    calc
      (a*a^((1:ℝ)/3))*‖v‖≤C*‖v‖ := mul_le_mul_of_nonneg_right hCap (norm_nonneg v)
      _≤C*(ε/C) := mul_le_mul_of_nonneg_left hv hC.le
      _=ε := mul_div_cancel₀ ε hC.ne'
  refine ⟨?_,?_⟩
  · intro x hx
    rw [residual_difference_pullback hu hg c hr i j hx,norm_smul,Real.norm_eq_abs,abs_of_pos ha]
    exact (mul_le_mul_of_nonneg_left (norm_value_le v _) ha.le).trans haV
  · intro x y hx hy
    rw [residual_difference_pullback hu hg c hr i j hx,
      residual_difference_pullback hu hg c hr i j hy,←smul_sub,norm_smul,Real.norm_eq_abs,abs_of_pos ha]
    have hh := norm_sub_value_le v (r⁻¹ • (x-c)) (r⁻¹ • (y-c))
    rw [affineSource_distance c x y hr,Real.mul_rpow ha.le dist_nonneg] at hh
    have hd : 0≤dist x y^((1:ℝ)/3) := Real.rpow_nonneg dist_nonneg _
    exact (mul_le_mul_of_nonneg_left hh ha.le).trans ((by
      nlinarith [mul_le_mul_of_nonneg_right hapV hd] :
        a*(‖v‖*(a^((1:ℝ)/3)*dist x y^((1:ℝ)/3)))≤ε*dist x y^((1:ℝ)/3)))

lemma geometric_residual_cauchy {u : ℕ → ℂ → Phase n} (hu : ∀ i,ContDiff ℝ ∞ (u i))
    {g : ℕ → HMap ℂ (Phase n)} (hg : ∀ i z,valueCLM _ (g i) z=geometricResidual (u i) z)
    {K : Set ℂ} (hK : IsCompact K) (hsupp : ∀ i z,z∉K  → geometricResidual (u i) z=0)
    {r : ℝ} (hr : 0 < r)
    (hlocal : ∀ c,CauchySeq (fun i => cutoffCurveJet smallDiskBump (markedLocalCurve_smooth (hu i) c r))) :
    CauchySeq g := by
  apply compact_local_holder_cauchy hK (div_pos hr (by norm_num : (0:ℝ)<4))
  · intro i z hz
    rw [hg,hsupp i z hz]
  · intro c
    exact local_residual_small_differences hu hg c hr (localResidual_cauchy hu c r (hlocal c))


end
section
open scoped ContDiff Topology BoundedContinuousFunction
open Set Filter
open HolderCompletion
variable {n : ℕ}

attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.clcInst2
local instance clcInst3_r117b4f_1 : NormedAddCommGroup (COne ℂ (Phase n)) := inferInstance
local instance clcInst4_r117b4f_1 : NormedSpace ℝ (COne ℂ (Phase n)) := inferInstance
lemma marked_value_continuous (p q : Phase n) (z : ℂ) :
    Continuous (fun w : COne ℂ (Phase n) => markedCurve p q w z) :=
  (continuous_const.add ((markedSlope_continuous p q).const_smul z)).add (jetEval z).continuous


end
section
open scoped ContDiff Topology BoundedContinuousFunction
open Set Filter
open HolderCompletion
variable {n : ℕ}

local instance eccInst1_r117b4f_1 : NormedAddCommGroup (COne ℂ (Phase n)) := inferInstance
local instance eccInst2_r117b4f_1 : NormedSpace ℝ (COne ℂ (Phase n)) := inferInstance
local instance eccInst3_r117b4f_1 : NormedAddCommGroup (HMap ℂ (Phase n)) := inferInstance
local instance eccInst4_r117b4f_1 : NormedSpace ℝ (HMap ℂ (Phase n)) := inferInstance
local instance eccInst5_r117b4f_1 (K : Set ℂ) : NormedAddCommGroup (supportedHolder (E := Phase n) K) := inferInstance
local instance eccInst6_r117b4f_1 (K : Set ℂ) : NormedSpace ℝ (supportedHolder (E := Phase n) K) := inferInstance
lemma represented_line_by_inverse {J : Phase n → End n} {p q : Phase n} {u : ℂ → Phase n}
    (hu : AffineLineCurve J p q u) {K : Set ℂ} (hK : IsCompact K)
    (g : supportedHolder (E := Phase n) K) (hg : ∀ z,valueCLM _ g.val z=geometricResidual u z) :
    markedCurve p q (standardHolderInverse hK g)=u := by
  obtain ⟨a,_,ha⟩ := hu.2.2.2.2
  exact (marked_reconstruction_from_correction (standardHolderInverse hK g)
    (inverse_correction_holomorphic hu.1 hK g hg) ha hu.2.2.1 hu.2.2.2.1
      (standardHolderInverse_zero hK g)).1

lemma subtype_cauchySeq_of_val {X : Type*} [PseudoMetricSpace X] {A : Set X} {g : ℕ → A}
    (hg : CauchySeq (fun i => (g i).val)) : CauchySeq g := by
  rw [Metric.cauchySeq_iff] at hg ⊢
  exact hg

theorem exact_marked_completed_convergence {J : Phase n → End n}
    (hJs : ContDiff ℝ ∞ J) (hJ : ∀ x,Compatible (J x))
    (hJc : HasCompactSupport (fun x => J x-standardJ n))
    {S T : ℝ} (hST : S<T) (hT : T<1) (hout : ∀ x,S < capacity x →J x=standardJ n)
    {p q : Phase n} (hpq : p≠q) {t : ℕ → ℝ} (ht : ∀ i,t i∈Icc (0:ℝ) 1)
    {s : ℝ} (hs : Tendsto t atTop (𝓝 s))
    {u : ℕ → ℂ → Phase n} (hu : ∀ i,AffineLineCurve (lineHomotopy J (t i)) p q (u i))
    {v : ℂ → Phase n} (hv : ∀ K : Set ℂ,IsCompact K →TendstoUniformlyOn u v atTop K) :
    ∃ (w : ℕ → COne ℂ (Phase n)) (a : COne ℂ (Phase n)),
      (∀ i,markedCurve p q (w i)=u i ∧ cValue (w i) 0=0) ∧
      Tendsto w atTop (𝓝 a) ∧ markedCurve p q a=v ∧
      AffineLineCurve (lineHomotopy J s) p q v := by
  obtain ⟨R,hR,hsupp⟩ := exact_marked_line_uniform_defect_support_bp240 hJs hJ hJc hST hT hout p q hpq
  let K := Metric.closedBall (0:ℂ) R
  have hK : IsCompact K := isCompact_closedBall _ _
  have hc (i : ℕ) : HasCompactSupport (geometricResidual (u i)) :=
    geometricResidual_compact (hu i) (lineHomotopy_compact hJc (ht i))
  let G : ℕ → HMap ℂ (Phase n) := fun i => geometricHolder (hu i).1 (hc i)
  have hG (i : ℕ) (z : ℂ) : valueCLM _ (G i) z=geometricResidual (u i) z := rfl
  have hsupp' (i : ℕ) (z : ℂ) (hz : z∉K) : geometricResidual (u i) z=0 := by
    have hz' : R<‖z‖ := by simpa only [K,Metric.mem_closedBall,dist_zero_right,not_le] using hz
    exact (hsupp (t i) (ht i) (u i) (hu i) z hz').2
  have hGK (i : ℕ) : G i∈supportedHolder K := by
    apply (mem_supportedHolder _ _).mpr
    intro z hz
    rw [hG,hsupp' i z hz]
  let g : ℕ → supportedHolder (E := Phase n) K := fun i => ⟨G i,hGK i⟩
  obtain ⟨r,hr,_,hlocal⟩ := exact_marked_local_jet_cauchy_bp240 hJs hJ hJc hST hT hout ht hs hu hv
  have hGC : CauchySeq G := geometric_residual_cauchy (fun i => (hu i).1) hG hK hsupp' hr hlocal
  have hgC : CauchySeq g := subtype_cauchySeq_of_val hGC
  obtain ⟨g₀,hg₀⟩ := cauchySeq_tendsto_of_complete hgC
  let w := fun i => standardHolderInverse hK (g i)
  let a := standardHolderInverse hK g₀
  have hw : Tendsto w atTop (𝓝 a) := ((standardHolderInverse hK).continuous.tendsto g₀).comp hg₀
  have hrec (i : ℕ) : markedCurve p q (w i)=u i := represented_line_by_inverse (hu i) hK (g i) (hG i)
  have hw0 (i : ℕ) : cValue (w i) 0=0 := standardHolderInverse_zero hK (g i)
  have hline (i : ℕ) : AffineLineCurve (lineHomotopy J (t i)) p q (markedCurve p q (w i)) := by
    rw [hrec i]
    exact hu i
  have haline := completed_line_closed_bp240 hJs hJ hJc hST hT hout hpq ht hs hw hw0 hline
  have hav : markedCurve p q a=v := by
    funext z
    have hpoint := ((marked_value_continuous p q z).tendsto a).comp hw
    have huv := (hv {z} isCompact_singleton).tendsto_at (mem_singleton z)
    apply tendsto_nhds_unique hpoint
    simpa only [Function.comp_def,hrec] using huv
  exact ⟨w,a,fun i => ⟨hrec i,hw0 i⟩,hw,hav,hav ▸ haline⟩

theorem exact_marked_completed_compactness {J : Phase n → End n}
    (hJs : ContDiff ℝ ∞ J) (hJ : ∀ x,Compatible (J x))
    (hJc : HasCompactSupport (fun x => J x-standardJ n))
    {S T : ℝ} (hST : S<T) (hT : T<1) (hout : ∀ x,S < capacity x →J x=standardJ n)
    {p q : Phase n} (hpq : p≠q) {t : ℕ → ℝ} (ht : ∀ i,t i∈Icc (0:ℝ) 1)
    {s : ℝ} (hs : Tendsto t atTop (𝓝 s))
    {u : ℕ → ℂ → Phase n} (hu : ∀ i,AffineLineCurve (lineHomotopy J (t i)) p q (u i)) :
    ∃ (φ : ℕ → ℕ),StrictMono φ ∧ ∃ (w : ℕ → COne ℂ (Phase n)) (a : COne ℂ (Phase n)),
      (∀ i,markedCurve p q (w i)=u (φ i) ∧ cValue (w i) 0=0) ∧
      Tendsto w atTop (𝓝 a) ∧ AffineLineCurve (lineHomotopy J s) p q (markedCurve p q a) := by
  obtain ⟨v,_,_,φ,hφ,hsub⟩ := exact_marked_line_czero_compactness_bp240 hJs hJ hJc hST hT hout ht hu
  obtain ⟨w,a,hrec,hw,hav,haline⟩ := exact_marked_completed_convergence hJs hJ hJc hST hT hout hpq
    (fun i => ht (φ i)) (hs.comp hφ.tendsto_atTop) (fun i => hu (φ i)) hsub
  exact ⟨φ,hφ,w,a,hrec,hw,hav.symm ▸ haline⟩


end
open scoped ContDiff Topology BoundedContinuousFunction
open Set Filter
open HolderCompletion
variable {n : ℕ}

local instance empInst1_r117b4f_1 : NormedAddCommGroup (COne ℂ (Phase n)) := inferInstance
local instance empInst2_r117b4f_1 : NormedSpace ℝ (COne ℂ (Phase n)) := inferInstance
lemma markedCurve_injective (p q : Phase n) : Function.Injective (markedCurve p q) := by
  intro v w hvw
  have hs : markedSlope p q v=markedSlope p q w := by
    apply tendsto_nhds_unique (markedCurve_asymptote p q v)
    rw [hvw]
    exact markedCurve_asymptote p q w
  apply cValue_ext
  intro z
  have hz := congrFun hvw z
  change p+z • markedSlope p q v+cValue v z=p+z • markedSlope p q w+cValue w z at hz
  rw [hs] at hz
  exact add_left_cancel hz

lemma correction_limit_zero {w : ℕ → COne ℂ (Phase n)} {v : COne ℂ (Phase n)}
    (hw : Tendsto w atTop (𝓝 v)) (hw0 : ∀ i,cValue (w i) 0=0) : cValue v 0=0 := by
  have hh := ((jetEval (E := Phase n) 0).continuous.tendsto v).comp hw
  apply tendsto_nhds_unique hh
  simpa only [Function.comp_def,jetEval_apply,hw0] using
    (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0:Phase n)) atTop (𝓝 0))

theorem exact_marked_zeroSet_compact_bp240_oai {J : Phase n → End n}
    (hJs : ContDiff ℝ ∞ J) (hJ : ∀ x,Compatible (J x))
    (hJc : HasCompactSupport (fun x => J x-standardJ n))
    {S T : ℝ} (hST : S<T) (hT : T<1) (hout : ∀ x,S < capacity x →J x=standardJ n)
    {p q : Phase n} (hpq : p≠q) : IsCompact (exactMarkedZeroSet J p q) := by
  apply IsSeqCompact.isCompact
  intro x hx
  obtain ⟨s,hsI,ψ,hψ,hs⟩ := isCompact_Icc.isSeqCompact (fun i => (hx i).1)
  have htime : Tendsto (fun i => (x (ψ i)).1) atTop (𝓝 s) := hs
  obtain ⟨φ,hφ,w,a,hrec,hwa,haline⟩ := exact_marked_completed_compactness hJs hJ hJc hST hT hout hpq
    (fun i => (hx (ψ i)).1) htime (fun i => (hx (ψ i)).2.2)
  have he (i : ℕ) : w i=(x (ψ (φ i))).2 := markedCurve_injective p q (hrec i).1
  have ha0 : cValue a 0=0 := correction_limit_zero hwa (fun i => (hrec i).2)
  refine ⟨(s,a),⟨hsI,ha0,haline⟩,ψ ∘ φ,hψ.comp hφ,?_⟩
  have htend := htime.comp hφ.tendsto_atTop
  have hw' : Tendsto (fun i => (x (ψ (φ i))).2) atTop (𝓝 a) := by
    have hew : w=(fun i => (x (ψ (φ i))).2) := funext he
    rw [hew] at hwa
    exact hwa
  exact htend.prodMk_nhds hw'



end HigherDimensionalBallPacking.Rigidity
end

end OAI
end

theorem solution : type_of% @OAI.HigherDimensionalBallPacking.Rigidity.exact_marked_zeroSet_compact_bp240_oai := @OAI.HigherDimensionalBallPacking.Rigidity.exact_marked_zeroSet_compact_bp240_oai
