-- Prove2me | solution 1 for OAI.LogConcaveSampling.kernelActionPicard_rms
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-27T13:58:36.538513+00:00
-- url     : https://prove2.me/submissions/85e707d1-4d22-43a3-b8cf-ca484ab1e994

import Mathlib
import Definitions.Def_LogConcaveQuery
import Definitions.Def_OAIQ048L004
import Theorems.Thm_OAI_LogConcaveSampling_kernelCorrectionPicard_rms
import Theorems.Thm_OAI_LogConcaveSampling_stationary_lie_taylor_rms

section
-- module Solutions.OAIQ048_LC.LogConcave_Dynamics_Curve
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open MeasureTheory Filter
open scoped ENNReal NNReal Topology

section UpperProof
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal RealInnerProductSpace Topology
open Function MeasureTheory Set Filter
open scoped Topology NNReal

namespace LogConcaveSampling.GlobalODE
open Set Function
open scoped Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] [ProperSpace E] {a b : ℝ} (hab : a≤b)
    {f : ℝ → E → E} (hc : Continuous (uncurry f))
    {K : ℝ≥0} (hL : ∀ t∈Icc a b,LipschitzWith K (f t))
    {D : ℝ → E → E →L[ℝ] E} (hD : Continuous (uncurry D))
    (hf : ∀ t z,HasFDerivAt (f t) (D t z) z)

include hab hD hf in
lemma flow_contDiff_one_to_left (t : Icc a b) :
    ContDiff ℝ 1 (fun x => flow hL hc t x a) := by
  let H := flowHomeomorph hL hc ⟨a,le_rfl,hab⟩ t
  let J (x : E) := fundamentalEquiv
    (flowSpatialCoefficient_continuous hab hc hL hD x)
    (flowSpatialCoefficient_bound hab hc hL hf x) ⟨a,le_rfl,hab⟩ t
  have hJ (x : E) : HasFDerivAt H (J x : E →L[ℝ] E) x :=
    flow_hasFDerivAt_left hab hc hL hD hf x t
  exact H.contDiff_symm hJ (flow_contDiff_one_left hab hc hL hD hf t)

include hab hD hf in

theorem flow_contDiff_one (s t : Icc a b) :
    ContDiff ℝ 1 (fun x => flow hL hc s x t) := by
  have hh := (flow_contDiff_one_left hab hc hL hD hf t).comp
    (flow_contDiff_one_to_left hab hc hL hD hf s)
  convert! hh using 1
  all_goals try with_reducible_and_instances rfl
  funext x
  exact (flow_cocycle hL hc s ⟨a,le_rfl,hab⟩ t x).symm
end LogConcaveSampling.GlobalODE

end UpperProof
end
end
end

end OAI
end

section
-- module Solutions.OAIQ048_LC.LogConcave_Dynamics_TriangularEquiv
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open MeasureTheory Filter
open scoped ENNReal NNReal Topology

section UpperProof
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal RealInnerProductSpace Topology
open Function MeasureTheory Set Filter
open scoped Topology NNReal

namespace LogConcaveSampling.GlobalODE
open Set Function Filter
open scoped Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

variable [CompleteSpace E] [ProperSpace E]
    {a b : ℝ} (hab : a≤b) {f : ℝ → E → E} (hc : Continuous (uncurry f))
    {K : ℝ≥0} (hL : ∀ t∈Icc a b,LipschitzWith K (f t))
    {D : ℝ → E → E →L[ℝ] E} (hD : Continuous (uncurry D))
    (hf : ∀ t z,HasFDerivAt (f t) (D t z) z)

include hD hf in

theorem spaceTimeBackward_differentiableAt (p : ℝ × E) (hp : p.1∈Ioo a b) :
    DifferentiableAt ℝ (spaceTimeBackward hab hc hL) p := by
  have hh := spaceTimeForward_hasFDerivAt hab hc hL hD hf
    (spaceTimeBackward hab hc hL p) hp
  exact (hh.of_local_left_inverse (spaceTimeBackward_continuous hab hc hL).continuousAt
    (Filter.Eventually.of_forall (spaceTime_right_inverse hab hc hL))).differentiableAt
end LogConcaveSampling.GlobalODE
namespace LogConcaveSampling.GlobalODE
open Set Function Filter
open scoped Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {a b : ℝ} (hab : a≤b) {f : ℝ → E → E} (hc : Continuous (uncurry f))
    {K : ℝ≥0} (hL : ∀ t∈Icc a b,LipschitzWith K (f t))

lemma backwardTest_eq (T : Icc a b) (φ : E → ℝ) (p : ℝ × E) :
    backwardTest hab hc hL T φ p=φ (flow hL hc (projIcc a b hab p.1) p.2 T) := by
  unfold backwardTest spaceTimeBackward
  rw [flow_cocycle hL hc (projIcc a b hab p.1) ⟨a,le_rfl,hab⟩ T]

lemma backwardTest_continuous (T : Icc a b) {φ : E → ℝ} (hφ : Continuous φ) :
    Continuous (backwardTest hab hc hL T φ) :=
  hφ.comp ((flow_lipschitz hL hc ⟨a,le_rfl,hab⟩ T).continuous.comp
    (spaceTimeBackward_continuous hab hc hL).snd)

lemma backwardTest_lipschitz (T : Icc a b) {φ : E → ℝ} {L : ℝ≥0}
    (hφ : LipschitzWith L φ) (t : ℝ) :
    LipschitzWith (L*⟨Real.exp ((K:ℝ)*(b-a)),(Real.exp_pos _).le⟩)
      (fun z => backwardTest hab hc hL T φ (t,z)) := by
  simp only [backwardTest_eq]
  apply hφ.comp
  apply (flow_lipschitz hL hc (projIcc a b hab t) T).weaken
  change Real.exp _≤Real.exp _
  apply Real.exp_le_exp.mpr
  apply mul_le_mul_of_nonneg_left _ K.coe_nonneg
  rw [abs_le]
  constructor <;> linarith [T.2.1,T.2.2,(projIcc a b hab t).2.1,(projIcc a b hab t).2.2]

variable [ProperSpace E] {D : ℝ → E → E →L[ℝ] E} (hD : Continuous (uncurry D))
    (hf : ∀ t z,HasFDerivAt (f t) (D t z) z)

include hD hf in
lemma backwardTest_differentiableAt (T : Icc a b) {φ : E → ℝ}
    (hφ : Differentiable ℝ φ) (p : ℝ × E) (hp : p.1∈Ioo a b) :
    DifferentiableAt ℝ (backwardTest hab hc hL T φ) p :=
  (hφ _).comp p (((flow_contDiff_one_left hab hc hL hD hf T).differentiable (by norm_num) _).comp p
    (spaceTimeBackward_differentiableAt hab hc hL hD hf p hp).snd)

include hD hf in

theorem backwardTest_material_zero (T : Icc a b) {φ : E → ℝ}
    (hφ : Differentiable ℝ φ) (p : ℝ × E) (hp : p.1∈Ioo a b) :
    fderiv ℝ (backwardTest hab hc hL T φ) p (1,f p.1 p.2)=0 := by
  let B := spaceTimeBackward hab hc hL
  let G := fun z => φ (flow hL hc ⟨a,le_rfl,hab⟩ z T)
  have hG : Differentiable ℝ G := hφ.comp
    ((flow_contDiff_one_left hab hc hL hD hf T).differentiable (by norm_num))
  have hv : f (B p).1 (spaceTimeForward hab hc hL (B p)).2=f p.1 p.2 := by
    rw [spaceTime_right_inverse hab hc hL p]
    rfl
  have hB := (spaceTimeForward_hasFDerivAt hab hc hL hD hf (B p) hp).of_local_left_inverse
    (spaceTimeBackward_continuous hab hc hL).continuousAt
    (Filter.Eventually.of_forall (spaceTime_right_inverse hab hc hL))
  have hcomp := (hG (B p).2).hasFDerivAt.comp p hB.snd
  change (fderiv ℝ (G ∘ fun x => (spaceTimeBackward hab hc hL x).2) p) (1,f p.1 p.2)=0
  rw [hcomp.fderiv]
  change (fderiv ℝ G (B p).2) _=0
  have he : (((triangularEquiv (f (B p).1 (spaceTimeForward hab hc hL (B p)).2)
      (fundamentalEquiv (flowSpatialCoefficient_continuous hab hc hL hD (B p).2)
        (flowSpatialCoefficient_bound hab hc hL hf (B p).2) ⟨a,le_rfl,hab⟩
          ⟨(B p).1,hp.1.le,hp.2.le⟩)).symm : (ℝ × E) →L[ℝ] (ℝ × E)) (1,f p.1 p.2)).2=0 := by
    change (fundamentalEquiv _ _ _ _).symm (f p.1 p.2-1 • _)=0
    rw [hv,one_smul,sub_self,map_zero]
  convert! (congrArg (fderiv ℝ G (B p).2) he).trans (map_zero _) using 1
  all_goals try with_reducible_and_instances rfl
end LogConcaveSampling.GlobalODE
namespace LogConcaveSampling.GlobalODE
open Set Function Filter
open scoped Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    [ProperSpace E] {a b : ℝ} (hab : a≤b) {f : ℝ → E → E}
    (hc : Continuous (uncurry f)) {K : ℝ≥0} (hL : ∀ t∈Icc a b,LipschitzWith K (f t))
    {D : ℝ → E → E →L[ℝ] E} (hD : Continuous (uncurry D))
    (hf : ∀ t z,HasFDerivAt (f t) (D t z) z)

include hD hf in

theorem backwardTest_chain (T : Icc a b) {φ : E → ℝ}
    (hφ : Differentiable ℝ φ) {γ : ℝ → E} {γ' : E} {t : ℝ}
    (ht : t∈Ioo a b) (hγ : HasDerivAt γ γ' t) :
    HasDerivAt (fun s => backwardTest hab hc hL T φ (s,γ s))
      (fderiv ℝ (fun z => backwardTest hab hc hL T φ (t,z)) (γ t) (γ'-f t (γ t))) t := by
  let A := fderiv ℝ (backwardTest hab hc hL T φ) (t,γ t)
  have hd := (backwardTest_differentiableAt hab hc hL hD hf T hφ (t,γ t) ht).hasFDerivAt
  have hsp := hd.comp (γ t) ((hasFDerivAt_const (𝕜:=ℝ) t (γ t)).prodMk (hasFDerivAt_id _))
  have hchain := hd.comp_hasDerivAt t ((hasDerivAt_id t).prodMk hγ)
  have hzero : A (1,f t (γ t))=0 := backwardTest_material_zero hab hc hL hD hf T hφ _ ht
  have he : A (1,γ')=A (0,γ'-f t (γ t)) := by
    have hp : ((1:ℝ),γ')=(1,f t (γ t))+(0,γ'-f t (γ t)) := by ext <;> simp
    rw [hp,map_add,hzero,zero_add]
  convert! hchain using 1
  all_goals try with_reducible_and_instances rfl
  change (fderiv ℝ (backwardTest hab hc hL T φ ∘ Prod.mk t) (γ t)) (γ'-f t (γ t))=A (1,γ')
  rw [hsp.fderiv]
  change A (0,γ'-f t (γ t))=A (1,γ')
  exact he.symm

end LogConcaveSampling.GlobalODE

end UpperProof
end
end
end

end OAI
end

section
-- module Solutions.OAIQ048_LC.LogConcave_Sampling_ContinuousFirstOrderReply
attribute [-instance] _root_.OAI.LogConcaveSampling.LowerBound.couplingLaw_probability _root_.OAI.LogConcaveSampling.LowerBound.remainingHaar_probability _root_.OAI.LogConcaveSampling.LowerBound.roundRandomLaw_probability _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_invInvariant _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_isHaar _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_probability _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_rightInvariant _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_compactSpace _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_measurableInv _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_measurableMul _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_secondCountable _root_.OAI.LogConcaveSampling.MeanTree.instIsProbabilityMeasureRowTapeRowLaw _root_.OAI.LogConcaveSampling.OracleCompiler.topSeedLaw_probability _root_.OAI.LogConcaveSampling.noiseKernel_markov
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open MeasureTheory Filter
open scoped ENNReal NNReal Topology

section UpperProof

namespace LogConcaveSampling
open scoped RealInnerProductSpace

theorem Admissible.contDiff_gradient {d : ℕ} {V : Point d → ℝ}
    (hV : Admissible V) : ContDiff ℝ 1 (gradient V) := by
  exact (InnerProductSpace.toDual ℝ (Point d)).symm.contDiff.comp
    (hV.smooth.fderiv_right (by norm_num))

theorem Admissible.quadratic_bounds {d : ℕ} {V : Point d → ℝ}
    (hV : Admissible V) (x : Point d) :
    ‖x‖ ^ 2 / 2 ≤ V x ∧ V x ≤ ‖x‖ ^ 2 := by
  let f : ℝ → ℝ := fun t => V (t • x)
  let g : ℝ → ℝ := fun t => inner ℝ x (gradient V (t • x))
  let h : ℝ → ℝ := fun t => inner ℝ x (fderiv ℝ (gradient V) (t • x) x)
  have hp : ∀ t : ℝ, HasDerivAt (fun s : ℝ => s • x) x t := fun t => by
    simpa using (hasDerivAt_id t).smul_const x
  have hdg := hV.contDiff_gradient.differentiable (by norm_num)
  have hf : ∀ t, HasDerivAt f (g t) t := by
    intro t
    have hh := ((hV.smooth.differentiable (by norm_num) (t • x)).hasFDerivAt).comp_hasDerivAt t (hp t)
    convert! hh using 1
    all_goals try with_reducible_and_instances rfl
    change inner ℝ x (gradient V (t • x)) = fderiv ℝ V (t • x) x
    rw [real_inner_comm]
    exact InnerProductSpace.toDual_symm_apply
  have hg : ∀ t, HasDerivAt g (h t) t := by
    intro t
    have hh := (hdg (t • x)).hasFDerivAt.comp_hasDerivAt t (hp t)
    simpa [g, h, Function.comp_def] using
      (hasDerivAt_const t x).inner ℝ hh
  have ht := quadratic_bounds_of_hasDerivAt hf hg
    (fun t => hV.hessian_bounds (t • x) x)
  dsimp only [f, g] at ht
  rw [zero_smul, one_smul, hV.value_zero, hV.gradient_zero, inner_zero_right, zero_add] at ht
  constructor <;> linarith [ht.1, ht.2]

theorem Admissible.integrable_exp_neg {d : ℕ} {V : Point d → ℝ}
    (hV : Admissible V) : Integrable (fun x => Real.exp (-V x)) := by
  apply (integrable_gaussian_envelope d (b := 1 / 2) (by norm_num)).mono'
    ((Real.continuous_exp.comp hV.smooth.continuous.neg).aestronglyMeasurable)
  exact Filter.Eventually.of_forall fun x => by
    dsimp only [Function.comp_apply, Pi.neg_apply]
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    apply Real.exp_le_exp.mpr
    have := (hV.quadratic_bounds x).1
    linarith

end LogConcaveSampling

end UpperProof
end
end
end

end OAI
end

section
-- module Solutions.OAIQ048_LC.LogConcave_Sampling_MeasureSmoothLipschitz
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open MeasureTheory Filter
open scoped ENNReal NNReal Topology

section UpperProof
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal RealInnerProductSpace Topology
open Function MeasureTheory Set Filter
open scoped Topology NNReal

namespace LogConcaveSampling
open MeasureTheory Filter
open scoped Topology NNReal

theorem measure_eq_of_smooth_lipschitz {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    {μ ν : Measure E} [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (h : ∀ (f : E → ℝ),ContDiff ℝ 1 f → (∃ L : ℝ≥0,LipschitzWith L f) →
      (∃ B : ℝ,∀ x,‖f x‖≤B) → (∫ x,f x ∂μ)=(∫ x,f x ∂ν)) : μ=ν := by
  apply Measure.ext_of_integral_eq_on_compactlySupported
  intro f
  have huf := f.hasCompactSupport.uniformContinuous_of_continuous f.continuous
  obtain ⟨B,hB⟩ := f.hasCompactSupport.exists_bound_of_continuous f.continuous
  have hε (n : ℕ) : 0<1/((n:ℝ)+1) := by positivity
  choose g hgc hgd using fun n : ℕ => huf.exists_contDiff_dist_le (hε n)
  have hge (n : ℕ) : 1/((n:ℝ)+1)≤1 := by
    exact (div_le_one (by positivity)).mpr (le_add_of_nonneg_left (Nat.cast_nonneg n))
  have hgb : ∀ n x,‖g n x‖≤B+1 := by
    intro n x
    have hd := (hgd n x).le.trans (hge n)
    rw [dist_eq_norm] at hd
    exact (norm_le_norm_add_norm_sub' (g n x) (f x)).trans (add_le_add (hB x) hd)
  have hgt (x : E) : Tendsto (fun n => g n x) atTop (𝓝 (f x)) := by
    apply tendsto_iff_dist_tendsto_zero.mpr
    exact squeeze_zero (fun _ => dist_nonneg) (fun n => (hgd n x).le)
      tendsto_one_div_add_atTop_nhds_zero_nat
  let u : ℕ → E → ℝ := fun n => PoincareCutoff.truncation (g n) n
  have huc (n : ℕ) : ContDiff ℝ 1 (u n) :=
    PoincareCutoff.truncation_smooth ((hgc n).of_le (by simp)) n
  have huk (n : ℕ) : HasCompactSupport (u n) := PoincareCutoff.truncation_compact _ _
  have hub : ∀ n x,‖u n x‖≤B+1 := by
    intro n x
    exact (PoincareCutoff.truncation_abs (g n) n x).trans (hgb n x)
  have huL (n : ℕ) : ∃ L : ℝ≥0,LipschitzWith L (u n) := by
    obtain ⟨C,hC⟩ := ((huk n).fderiv ℝ).exists_bound_of_continuous
      ((huc n).continuous_fderiv (by norm_num))
    let L : ℝ≥0 := ⟨C,(norm_nonneg _).trans (hC 0)⟩
    exact ⟨L,lipschitzWith_of_nnnorm_fderiv_le ((huc n).differentiable (by norm_num)) hC⟩
  have hut (x : E) : Tendsto (fun n => u n x) atTop (𝓝 (f x)) := by
    simpa only [u,PoincareCutoff.truncation,one_mul] using (PoincareCutoff.cutoff_tendsto x).mul (hgt x)
  have hlim (η : Measure E) [IsFiniteMeasure η] :
      Tendsto (fun n => ∫ x,u n x ∂η) atTop (𝓝 (∫ x,f x ∂η)) := by
    exact tendsto_integral_of_dominated_convergence (fun _ => B+1)
      (fun n => (huc n).continuous.aestronglyMeasurable) (integrable_const (B+1))
      (fun n => Eventually.of_forall (hub n)) (Eventually.of_forall hut)
  have he : (fun n => ∫ x,u n x ∂μ)=(fun n => ∫ x,u n x ∂ν) :=
    funext fun n => h (u n) (huc n) (huL n) ⟨B+1,hub n⟩
  exact tendsto_nhds_unique (hlim μ) (he ▸ hlim ν)
end LogConcaveSampling

end UpperProof
end
end
end

end OAI
end

section
-- module Solutions.OAIQ048_LC.LogConcave_Dynamics_Truncated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
namespace LogConcaveSampling.LinearGrowthODE
open Set Function Filter
open scoped Topology NNReal

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]

theorem unique {f : E → E} (hf : ContDiff ℝ 1 f) {a b : ℝ} {α β : ℝ → E}
    (hα : ContinuousOn α (Icc a b)) (hβ : ContinuousOn β (Icc a b))
    (hdα : ∀t∈Icc a b,HasDerivWithinAt α (f (α t)) (Icc a b) t)
    (hdβ : ∀t∈Icc a b,HasDerivWithinAt β (f (β t)) (Icc a b) t)
    (h0 : α a=β a) : Set.EqOn α β (Icc a b) := by
  obtain ⟨A,hA⟩ := isCompact_Icc.exists_bound_of_continuousOn hα
  obtain ⟨B,hB⟩ := isCompact_Icc.exists_bound_of_continuousOn hβ
  obtain ⟨L,hL⟩ := hf.contDiffOn.exists_lipschitzOnWith (by norm_num : (1:WithTop ℕ∞)≠0)
    (convex_closedBall (0:E) (max A B)) (isCompact_closedBall (0:E) (max A B))
  intro t ht
  have hh := dist_le_of_trajectories_ODE_of_mem (v:=fun (_ : ℝ) => f)
    (s:=fun _ => Metric.closedBall (0:E) (max A B))
    (fun _ _ => hL) hα (GlobalODE.right_deriv hdα)
    (fun u hu => by simpa only [Metric.mem_closedBall,dist_zero_right] using
      (hA u ⟨hu.1,hu.2.le⟩).trans (le_max_left A B))
    hβ (GlobalODE.right_deriv hdβ)
    (fun u hu => by simpa only [Metric.mem_closedBall,dist_zero_right] using
      (hB u ⟨hu.1,hu.2.le⟩).trans (le_max_right A B)) (show dist (α a) (β a)≤0 by simp [h0]) t ht
  simpa only [h0,dist_self,zero_mul,dist_le_zero] using hh
end LogConcaveSampling.LinearGrowthODE

end

end

section

noncomputable section
namespace LogConcaveSampling.LinearGrowthODE
open Set Function Filter Metric
open scoped Topology NNReal

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

lemma growth_from_right {a b K B R : ℝ} {α β : ℝ → E}
    (hc : ContinuousOn α (Icc a b))
    (hd : ∀t∈Icc a b,HasDerivWithinAt α (β t) (Icc a b) t)
    (hb : ‖α b‖≤R) (hg : ∀t∈Icc a b,‖β t‖≤K*‖α t‖+B)
    (t : ℝ) (ht : t∈Icc a b) : ‖α t‖≤gronwallBound R K B (b-t) := by
  let q : ℝ → ℝ := fun u => a+b-u
  have hq (u : ℝ) (hu : u∈Icc a b) : q u∈Icc a b := by
    constructor <;> dsimp [q] <;> linarith [hu.1,hu.2]
  have hqc : Continuous q := by dsimp [q]; fun_prop
  have hαc : ContinuousOn (α ∘ q) (Icc a b) := hc.comp hqc.continuousOn hq
  have hαd (u : ℝ) (hu : u∈Icc a b) :
      HasDerivWithinAt (α ∘ q) (-β (q u)) (Icc a b) u := by
    have hqd : HasDerivWithinAt q (-1) (Icc a b) u := by
      convert! ((hasDerivWithinAt_const u (Icc a b) (a+b)).sub
        (hasDerivWithinAt_id u (Icc a b))) using 1
      all_goals try with_reducible_and_instances rfl
      simp
    simpa only [neg_one_smul] using (hd (q u) (hq u hu)).scomp u hqd hq
  have h0 : ‖(α ∘ q) a‖≤R := by simpa [q] using hb
  have hβb (u : ℝ) (_hu : u∈Ico a b) :
      ‖-β (q u)‖≤K*‖(α ∘ q) u‖+B := by
    simpa only [norm_neg,comp_apply] using hg (q u) (hq u ⟨_hu.1,_hu.2.le⟩)
  have hh := norm_le_gronwallBound_of_norm_deriv_right_le hαc
    (GlobalODE.right_deriv (f := fun u (_ : E) => -β (q u)) hαd) h0 hβb (q t) (hq t ht)
  simpa only [comp_apply,q,show a+b-(a+b-t)=t by ring,show a+b-t-a=b-t by ring] using hh

lemma gronwallBound_initial_mono {R S K B t : ℝ} (h : R≤S) :
    gronwallBound R K B t≤gronwallBound S K B t := by
  unfold gronwallBound
  split_ifs <;> gcongr

variable [FiniteDimensional ℝ E]

lemma flow_continuous {f : E → E} (hf : ContDiff ℝ 1 f) {K B a b : ℝ}
    (hK : 0≤K) (hB : 0≤B) (hg : ∀x,‖f x‖≤K*‖x‖+B) (hab : a≤b) (x : E) :
    Continuous (flow hf hK hB hg hab x) := (exists_curve hf hK hB hg hab x).choose_spec.1
lemma flow_initial {f : E → E} (hf : ContDiff ℝ 1 f) {K B a b : ℝ}
    (hK : 0≤K) (hB : 0≤B) (hg : ∀x,‖f x‖≤K*‖x‖+B) (hab : a≤b) (x : E) :
    flow hf hK hB hg hab x a=x := (exists_curve hf hK hB hg hab x).choose_spec.2.1
lemma flow_deriv {f : E → E} (hf : ContDiff ℝ 1 f) {K B a b : ℝ}
    (hK : 0≤K) (hB : 0≤B) (hg : ∀x,‖f x‖≤K*‖x‖+B) (hab : a≤b) (x : E) :
    ∀t∈Icc a b,HasDerivWithinAt (flow hf hK hB hg hab x)
      (f (flow hf hK hB hg hab x t)) (Icc a b) t :=
  (exists_curve hf hK hB hg hab x).choose_spec.2.2.1
end LogConcaveSampling.LinearGrowthODE

end

end

section

noncomputable section
namespace LogConcaveSampling.LinearGrowthODE
open Set Function Filter Metric
open scoped Topology NNReal

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]

lemma truncated_flow_growth {f : E → E} (hf : ContDiff ℝ 1 f) {K B a b : ℝ}
    (hg : ∀x,‖f x‖≤K*‖x‖+B) (hab : a≤b) (n : ℕ)
    {L : ℝ≥0} (hL : LipschitzWith L (truncated f n)) (y : E) :
    ∀t∈Icc a b,‖GlobalODE.flow (fun _ _ => hL)
      (truncated_continuous hf n) ⟨a,le_rfl,hab⟩ y t‖≤
        gronwallBound ‖y‖ K B (t-a) := by
  apply norm_le_gronwallBound_of_norm_deriv_right_le
    (GlobalODE.flow_continuous _ _ _ _).continuousOn
    (GlobalODE.right_deriv (GlobalODE.flow_deriv _ _ _ _))
    (by rw [GlobalODE.flow_initial])
  exact fun _ _ => truncated_growth hg n _

lemma eq_truncated_flow {f : E → E} (hf : ContDiff ℝ 1 f) {K B a b R : ℝ}
    (hK : 0≤K) (hB : 0≤B) (hg : ∀x,‖f x‖≤K*‖x‖+B) (hab : a≤b)
    (n : ℕ) {L : ℝ≥0} (hL : LipschitzWith L (truncated f n))
    (hn : gronwallBound R K B (b-a)≤(n:ℝ)+1) {y : E} (hy : ‖y‖≤R) :
    EqOn (flow hf hK hB hg hab y)
      (GlobalODE.flow (fun _ _ => hL) (truncated_continuous hf n)
        ⟨a,le_rfl,hab⟩ y) (Icc a b) := by
  let α := GlobalODE.flow (fun _ _ => hL)
    (truncated_continuous hf n) (⟨a,le_rfl,hab⟩ : Icc a b) y
  have hd (t : ℝ) (ht : t∈Icc a b) : HasDerivWithinAt α (f (α t)) (Icc a b) t := by
    have hb := truncated_flow_growth hf hg hab n hL y t ht
    have hb' : ‖α t‖≤(n:ℝ)+1 := hb.trans ((gronwallBound_initial_mono hy).trans
      ((gronwallBound_mono ((norm_nonneg y).trans hy) hB hK (sub_le_sub_right ht.2 a)).trans hn))
    have he := truncated_eq (f:=f) hb'
    exact he ▸ GlobalODE.flow_deriv (fun _ _ => hL) _ _ y t ht
  apply unique hf (flow_continuous hf hK hB hg hab y).continuousOn
    (GlobalODE.flow_continuous _ _ _ _).continuousOn (flow_deriv hf hK hB hg hab y) hd
  rw [flow_initial,GlobalODE.flow_initial]

lemma flow_continuous_initial {f : E → E} (hf : ContDiff ℝ 1 f) {K B a b : ℝ}
    (hK : 0≤K) (hB : 0≤B) (hg : ∀x,‖f x‖≤K*‖x‖+B) (hab : a≤b)
    (t : ℝ) (ht : t∈Icc a b) : Continuous (fun y => flow hf hK hB hg hab y t) := by
  apply continuous_iff_continuousAt.mpr
  intro x
  obtain ⟨n,hn⟩ := exists_nat_gt (gronwallBound (‖x‖+1) K B (b-a))
  obtain ⟨L,hL⟩ := truncated_lipschitz hf n
  have hh := (GlobalODE.flow_lipschitz (fun _ _ => hL)
    (truncated_continuous hf n) ⟨a,le_rfl,hab⟩ ⟨t,ht⟩).continuous.continuousAt (x:=x)
  apply hh.congr_of_eventuallyEq
  filter_upwards [Metric.ball_mem_nhds x (by norm_num : (0:ℝ)<1)] with y hy
  apply (eq_truncated_flow hf hK hB hg hab n hL (by linarith) ?_ ht)
  calc ‖y‖≤‖x‖+dist y x := norm_le_norm_add_const_of_dist_le le_rfl
       _≤‖x‖+1 := by gcongr; exact (Metric.mem_ball.mp hy).le

lemma backwardTest_vanish {f : E → E} (hf : ContDiff ℝ 1 f) {K B a b R : ℝ}
    (hK : 0≤K) (hB : 0≤B) (hg : ∀x,‖f x‖≤K*‖x‖+B) (hab : a≤b)
    (hR : 0≤R) {φ : E → ℝ} (hφ : ∀x,R<‖x‖ → φ x=0)
    (n : ℕ) {L : ℝ≥0} (hL : LipschitzWith L (truncated f n)) (t : ℝ) (y : E)
    (hy : gronwallBound R K B (b-a)<‖y‖) :
    GlobalODE.backwardTest (f:=fun (_ : ℝ) => truncated f n) hab
      (truncated_continuous hf n) (fun _ _ => hL)
      ⟨b,hab,le_rfl⟩ φ (t,y)=0 := by
  rw [GlobalODE.backwardTest_eq]
  apply hφ
  by_contra! h
  let s := projIcc a b hab t
  let α := GlobalODE.flow (fun _ _ => hL)
    (truncated_continuous hf n) s y
  have hh := growth_from_right (GlobalODE.flow_continuous _ _ _ _).continuousOn
    (GlobalODE.flow_deriv (fun _ _ => hL) _ s y) h
    (fun u _ => truncated_growth hg n (α u)) s s.2
  rw [GlobalODE.flow_initial] at hh
  have hm := gronwallBound_mono hR hB hK (sub_le_sub_left s.2.1 b)
  exact (not_lt_of_ge (hh.trans hm)) hy
end LogConcaveSampling.LinearGrowthODE

end

end

section

noncomputable section
namespace LogConcaveSampling.GlobalODE
open Set Function Filter MeasureTheory
open scoped Topology NNReal

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

theorem stationary_integral_of_backward_flux {f : E → E} (hf : ContDiff ℝ 1 f)
    {K : ℝ≥0} (hL : LipschitzWith K f) {μ : Measure E} [IsFiniteMeasure μ]
    (hfi : Integrable (fun x => ‖f x‖) μ)
    {a b : ℝ} (hab : a<b) {φ : E → ℝ} (hφ : ContDiff ℝ 1 φ)
    {L : ℝ≥0} (hφL : LipschitzWith L φ) {B : ℝ} (hφB : ∀x,‖φ x‖≤B)
    (hflux : ∀t : ℝ,(∫y,(fderiv ℝ (fun z =>
      backwardTest (f:=fun (_ : ℝ) => f) hab.le (hf.continuous.comp continuous_snd) (fun _ _ => hL)
        ⟨b,hab.le,le_rfl⟩ φ (t,z)) y) (f y) ∂μ)=0) :
    (∫y,φ (flow (fun _ _ => hL) (hf.continuous.comp continuous_snd)
      ⟨a,le_rfl,hab.le⟩ y b) ∂μ)=∫y,φ y ∂μ := by
  let hc : Continuous (uncurry (fun (_ : ℝ) => f)) := hf.continuous.comp continuous_snd
  let hD : Continuous (uncurry (fun (_ : ℝ) => fderiv ℝ f)) :=
    (hf.continuous_fderiv (by norm_num)).comp continuous_snd
  let hd : ∀ (u : ℝ) (z : E),HasFDerivAt f (fderiv ℝ f z) z :=
    fun _ z => (hf.differentiable (by norm_num) z).hasFDerivAt
  let T : Icc a b := ⟨b,hab.le,le_rfl⟩
  let ψ := backwardTest hab.le hc (fun _ _ => hL) T φ
  let S := fun t => fderiv ℝ (fun y => ψ (t,y))
  let C : ℝ := (L:ℝ)*Real.exp ((K:ℝ)*(b-a))
  have hC : 0≤C := by dsimp [C]; positivity
  have hψ : Continuous ψ := backwardTest_continuous hab.le hc (fun _ _ => hL) T hφ.continuous
  have hψc (t : ℝ) : ContDiff ℝ 1 (fun y => ψ (t,y)) := by
    have he : (fun y => ψ (t,y))=φ ∘ (fun y =>
        flow (fun _ _ => hL) hc (projIcc a b hab.le t) y T) := by
      funext y
      exact backwardTest_eq hab.le hc (fun _ _ => hL) T φ (t,y)
    rw [he]
    exact hφ.comp (flow_contDiff_one hab.le hc (fun _ _ => hL) hD hd _ T)
  have hψL (t : ℝ) := backwardTest_lipschitz hab.le hc (fun _ _ => hL) T hφL t
  have hψB (t : ℝ) (y : E) : ‖ψ (t,y)‖≤B := hφB _
  have hSb (t : ℝ) (y : E) : ‖S t y‖≤C := norm_fderiv_le_of_lipschitz ℝ (hψL t)
  have him (t : ℝ) : Integrable (fun y => ψ (t,y)) μ :=
    (integrable_const B).mono' (hψ.measurable.comp (measurable_const.prodMk measurable_id)).aestronglyMeasurable
      (Eventually.of_forall (hψB t))
  have hdm (t : ℝ) : Measurable (fun y => -(S t y (f y))) :=
    ((continuous_fst.clm_apply continuous_snd).measurable.comp
      ((measurable_fderiv ℝ (fun y => ψ (t,y))).prodMk hf.continuous.measurable)).neg
  have hdb (t : ℝ) (y : E) : ‖-(S t y (f y))‖≤C*‖f y‖ := by
    rw [norm_neg]
    exact (ContinuousLinearMap.le_opNorm _ _).trans (mul_le_mul_of_nonneg_right (hSb t y) (norm_nonneg _))
  have hpd (t : ℝ) (ht : t∈Ioo a b) (y : E) :
      HasDerivAt (fun t => ψ (t,y)) (-(S t y (f y))) t := by
    have hh := backwardTest_chain hab.le hc (fun _ _ => hL) hD hd T
      (hφ.differentiable (by norm_num)) ht (hasDerivAt_const t y)
    simpa only [zero_sub,map_neg] using hh
  have hQd (t : ℝ) (ht : t∈Ioo a b) : HasDerivAt (fun t => ∫y,ψ (t,y) ∂μ) 0 t := by
    have hh := hasDerivAt_integral_of_dominated_loc_of_deriv_le
      (F:=fun t y => ψ (t,y)) (F':=fun t y => -(S t y (f y)))
      (Ioo_mem_nhds ht.1 ht.2)
      (Eventually.of_forall fun _ =>
        (hψ.measurable.comp (measurable_const.prodMk measurable_id)).aestronglyMeasurable)
      (him t) (hdm t).aestronglyMeasurable
      (Eventually.of_forall fun y s _ => hdb s y) (hfi.const_mul C)
      (Eventually.of_forall fun y s hs => hpd s hs y)
    have hz := hflux t
    have he : (∫y,-(S t y (f y)) ∂μ)=0 := by rw [integral_neg]; exact neg_eq_zero.mpr hz
    rw [he] at hh
    exact hh.2
  have hQc : Continuous (fun t => ∫y,ψ (t,y) ∂μ) :=
    continuous_of_dominated
      (fun _ => (hψ.measurable.comp (measurable_const.prodMk measurable_id)).aestronglyMeasurable)
      (fun t => Eventually.of_forall (hψB t)) (integrable_const B)
      (Eventually.of_forall fun y => hψ.comp (continuous_id.prodMk continuous_const))
  obtain ⟨t,ht,he⟩ := exists_deriv_eq_slope (fun t => ∫y,ψ (t,y) ∂μ) hab hQc.continuousOn
    (fun t ht => (hQd t ht).differentiableAt.differentiableWithinAt)
  rw [(hQd t ht).deriv] at he
  have heq : (∫y,ψ (b,y) ∂μ)=(∫y,ψ (a,y) ∂μ) :=
    sub_eq_zero.mp ((div_eq_zero_iff).mp he.symm |>.resolve_right (sub_ne_zero.mpr hab.ne'))
  have ha : (fun y => ψ (a,y))=(fun y => φ (flow (fun _ _ => hL) hc ⟨a,le_rfl,hab.le⟩ y b)) := by
    funext y
    dsimp [ψ]
    rw [backwardTest_eq,projIcc_of_mem _ (show a∈Icc a b from ⟨le_rfl,hab.le⟩)]
  have hb : (fun y => ψ (b,y))=φ := by
    funext y
    dsimp [ψ]
    rw [backwardTest_eq,projIcc_of_mem _ (show b∈Icc a b from ⟨hab.le,le_rfl⟩)]
    exact congrArg φ (flow_initial (fun _ _ => hL) hc T y)
  rw [ha,hb] at heq
  exact heq.symm

end LogConcaveSampling.GlobalODE

end

end

section

noncomputable section
namespace LogConcaveSampling.LinearGrowthODE
open Set Function Filter Metric MeasureTheory
open scoped Topology NNReal

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
lemma fderiv_zero_of_vanish_outside {ψ : E → ℝ} {C : ℝ}
    (hψ : ∀z,C<‖z‖ → ψ z=0) {y : E} (hy : C<‖y‖) : fderiv ℝ ψ y=0 := by
  have he : ψ =ᶠ[𝓝 y] fun _ => (0:ℝ) := by
    filter_upwards [(isOpen_lt continuous_const continuous_norm).mem_nhds hy] with z hz
    exact hψ z hz
  exact ((hasFDerivAt_const (𝕜:=ℝ) (0:ℝ) y).congr_of_eventuallyEq he).fderiv

theorem stationary_integral_compact {f : E → E} (hf : ContDiff ℝ 1 f) {K B a b : ℝ}
    (hK : 0≤K) (hB : 0≤B) (hg : ∀x,‖f x‖≤K*‖x‖+B) (hab : a<b)
    {μ : Measure E} [IsFiniteMeasure μ] (hfi : Integrable (fun x => ‖f x‖) μ)
    (hflux : ∀ψ : E → ℝ,ContDiff ℝ 1 ψ → HasCompactSupport ψ →
      (∫x,(fderiv ℝ ψ x) (f x) ∂μ)=0)
    {φ : E → ℝ} (hφ : ContDiff ℝ 1 φ) (hφc : HasCompactSupport φ) :
    (∫y,φ (flow hf hK hB hg hab.le y b) ∂μ)=∫y,φ y ∂μ := by
  obtain ⟨R,hR,hRb⟩ := hφc.isCompact.isBounded.exists_pos_norm_le
  have hφv (z : E) (hz : R<‖z‖) : φ z=0 := by
    by_contra hh
    exact (not_lt_of_ge (hRb z (subset_tsupport φ hh))) hz
  let C := gronwallBound R K B (b-a)
  obtain ⟨n,hn⟩ := exists_nat_gt (max C (gronwallBound C K B (b-a)))
  have hnC : C≤(n:ℝ)+1 := by have := le_max_left C (gronwallBound C K B (b-a)); linarith
  have hnG : gronwallBound C K B (b-a)≤(n:ℝ)+1 := by
    have := le_max_right C (gronwallBound C K B (b-a)); linarith
  obtain ⟨L,hL⟩ := truncated_lipschitz hf n
  let hc := truncated_continuous hf n
  let T : Icc a b := ⟨b,hab.le,le_rfl⟩
  let ψ := GlobalODE.backwardTest hab.le hc (fun _ _ => hL) T φ
  have hψv (t : ℝ) (z : E) (hz : C<‖z‖) : ψ (t,z)=0 :=
    backwardTest_vanish hf hK hB hg hab.le hR.le hφv n hL t z hz
  have hψc (t : ℝ) : ContDiff ℝ 1 (fun z => ψ (t,z)) := by
    have he : (fun z => ψ (t,z))=φ ∘ (fun z =>
        GlobalODE.flow (fun _ _ => hL) hc (projIcc a b hab.le t) z T) := by
      funext z
      exact GlobalODE.backwardTest_eq hab.le hc (fun _ _ => hL) T φ (t,z)
    rw [he]
    apply hφ.comp
    apply GlobalODE.flow_contDiff_one (D:=fun _ => fderiv ℝ (truncated f n)) hab.le hc (fun _ _ => hL)
      (((truncated_smooth hf n).continuous_fderiv (by norm_num)).comp continuous_snd)
      (fun _ z => ((truncated_smooth hf n).differentiable (by norm_num) z).hasFDerivAt)
  have hψcompact (t : ℝ) : HasCompactSupport (fun z => ψ (t,z)) :=
    HasCompactSupport.intro (isCompact_closedBall (0:E) C) fun z hz =>
      hψv t z (by simpa only [mem_closedBall,dist_zero_right,not_le] using hz)
  have hψflux (t : ℝ) : (∫y,(fderiv ℝ (fun z => ψ (t,z)) y) (truncated f n y) ∂μ)=0 := by
    rw [show (fun y => (fderiv ℝ (fun z => ψ (t,z)) y) (truncated f n y))=
      (fun y => (fderiv ℝ (fun z => ψ (t,z)) y) (f y)) by
        funext y
        by_cases hy : ‖y‖≤C
        · rw [truncated_eq (hy.trans hnC)]
        · rw [fderiv_zero_of_vanish_outside (hψv t) (lt_of_not_ge hy)]
          rfl]
    exact hflux _ (hψc t) (hψcompact t)
  have hni : Integrable (fun x => ‖truncated f n x‖) μ :=
    hfi.mono' (truncated_smooth hf n).continuous.norm.aestronglyMeasurable
      (Eventually.of_forall fun x => by
        rw [norm_norm,truncated,norm_smul,Real.norm_eq_abs,
          abs_of_nonneg (PoincareCutoff.cutoff_nonneg n x)]
        exact mul_le_of_le_one_left (norm_nonneg _) (PoincareCutoff.cutoff_le_one n x))
  obtain ⟨J,hJ⟩ := ContDiff.lipschitzWith_of_hasCompactSupport hφc hφ (by norm_num)
  obtain ⟨D,hD⟩ := hφc.exists_bound_of_continuous hφ.continuous
  have hh := GlobalODE.stationary_integral_of_backward_flux (truncated_smooth hf n) hL hni
    hab hφ hJ hD hψflux
  rw [←hh]
  apply integral_congr_ae
  filter_upwards [] with y
  by_cases hy : ‖y‖≤C
  · exact congrArg φ (eq_truncated_flow hf hK hB hg hab.le n hL hnG hy ⟨hab.le,le_rfl⟩)
  · have hy' : C<‖y‖ := lt_of_not_ge hy
    have hv : φ (flow hf hK hB hg hab.le y b)=0 := by
      apply hφv
      by_contra! h
      have hh := growth_from_right (flow_continuous hf hK hB hg hab.le y).continuousOn
        (flow_deriv hf hK hB hg hab.le y) h (fun _ _ => hg _) a ⟨le_rfl,hab.le⟩
      rw [flow_initial] at hh
      exact (not_lt_of_ge hh) hy'
    rw [hv]
    exact (by
      have hh := hψv a y hy'
      dsimp [ψ] at hh
      rw [GlobalODE.backwardTest_eq,projIcc_of_mem _ (show a∈Icc a b from ⟨le_rfl,hab.le⟩)] at hh
      exact hh.symm)
theorem stationary_law {f : E → E} (hf : ContDiff ℝ 1 f) {K B a b : ℝ}
    (hK : 0≤K) (hB : 0≤B) (hg : ∀x,‖f x‖≤K*‖x‖+B) (hab : a<b)
    {μ : Measure E} [IsFiniteMeasure μ] (hfi : Integrable (fun x => ‖f x‖) μ)
    (hflux : ∀ψ : E → ℝ,ContDiff ℝ 1 ψ → HasCompactSupport ψ →
      (∫x,(fderiv ℝ ψ x) (f x) ∂μ)=0) :
    μ.map (fun y => flow hf hK hB hg hab.le y b)=μ := by
  let T := fun y => flow hf hK hB hg hab.le y b
  have hTc : Continuous T := flow_continuous_initial hf hK hB hg hab.le b ⟨hab.le,le_rfl⟩
  apply measure_eq_of_smooth_lipschitz
  intro φ hφ _hφL hφB
  obtain ⟨D,hD⟩ := hφB
  let u := PoincareCutoff.truncation φ
  have hul (η : Measure E) [IsFiniteMeasure η] :
      Tendsto (fun n => ∫y,u n y ∂η) atTop (𝓝 (∫y,φ y ∂η)) := by
    apply tendsto_integral_of_dominated_convergence (fun _ => D)
      (fun n => (PoincareCutoff.truncation_smooth hφ n).continuous.aestronglyMeasurable)
      (integrable_const D)
    · exact fun n => Eventually.of_forall fun y =>
        (PoincareCutoff.truncation_abs φ n y).trans (hD y)
    · exact Eventually.of_forall (PoincareCutoff.truncation_tendsto φ)
  have he : (fun n => ∫y,u n y ∂μ.map T)=(fun n => ∫y,u n y ∂μ) := by
    funext n
    rw [integral_map hTc.aemeasurable
      (PoincareCutoff.truncation_smooth hφ n).continuous.aestronglyMeasurable]
    exact stationary_integral_compact hf hK hB hg hab hfi hflux
      (PoincareCutoff.truncation_smooth hφ n) (PoincareCutoff.truncation_compact φ n)
  exact tendsto_nhds_unique (hul (μ.map T)) (he ▸ hul μ)
end LogConcaveSampling.LinearGrowthODE

end

end

end

end OAI
end

section
-- module Solutions.OAIQ048_LC.LogConcave_Analysis_GaussianProposalPotential
attribute [-instance] _root_.OAI.LogConcaveSampling.LowerBound.couplingLaw_probability _root_.OAI.LogConcaveSampling.LowerBound.remainingHaar_probability _root_.OAI.LogConcaveSampling.LowerBound.roundRandomLaw_probability _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_invInvariant _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_isHaar _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_probability _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_rightInvariant _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_compactSpace _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_measurableInv _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_measurableMul _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_secondCountable _root_.OAI.LogConcaveSampling.MeanTree.instIsProbabilityMeasureRowTapeRowLaw _root_.OAI.LogConcaveSampling.OracleCompiler.topSeedLaw_probability _root_.OAI.LogConcaveSampling.noiseKernel_markov
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open MeasureTheory Filter
open scoped ENNReal NNReal Topology

section UpperProof
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal RealInnerProductSpace Topology
open Function MeasureTheory Set Filter
open scoped Topology NNReal

namespace LogConcaveSampling
open scoped RealInnerProductSpace

lemma gaussianProposalPotential_eq (d : ℕ) (x : Point d) :
    gaussianProposalPotential d x = ‖x‖^2/2 := by
  simp [gaussianProposalPotential]

end LogConcaveSampling

end UpperProof
end
end
end

end OAI
end

section
-- module Solutions.OAIQ048_LC.LogConcave_JetEstimates_NormalizedLaplace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open MeasureTheory Filter
open scoped ENNReal NNReal Topology

section UpperProof
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal RealInnerProductSpace Topology

namespace LogConcaveSampling
namespace JetCalculus
open scoped Topology

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] {ι κ : Type*}

lemma dir_zero (f : E → ℝ) : dir 0 f=fun _ => 0 := by funext x; simp [dir]

end JetCalculus
end LogConcaveSampling

end UpperProof
end
end
end

end OAI
end

section
-- module Solutions.OAIQ048_LC.LogConcave_Sampling_Directional
attribute [-instance] _root_.OAI.LogConcaveSampling.LowerBound.couplingLaw_probability _root_.OAI.LogConcaveSampling.LowerBound.remainingHaar_probability _root_.OAI.LogConcaveSampling.LowerBound.roundRandomLaw_probability _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_invInvariant _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_isHaar _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_probability _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_rightInvariant _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_compactSpace _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_measurableInv _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_measurableMul _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_secondCountable _root_.OAI.LogConcaveSampling.MeanTree.instIsProbabilityMeasureRowTapeRowLaw _root_.OAI.LogConcaveSampling.OracleCompiler.topSeedLaw_probability _root_.OAI.LogConcaveSampling.noiseKernel_markov
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open MeasureTheory Filter
open scoped ENNReal NNReal Topology

section UpperProof
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal RealInnerProductSpace Topology
open Function MeasureTheory Set Filter
open scoped Topology NNReal

namespace LogConcaveSampling
open scoped RealInnerProductSpace
open MeasureTheory

lemma directional_mul {d : ℕ} {f g : Point d → ℝ} (hf : Differentiable ℝ f)
    (hg : Differentiable ℝ g) (v : Point d) :
    directional v (fun x => f x*g x)=fun x => directional v f x*g x+f x*directional v g x := by
  funext x
  unfold directional
  change (fderiv ℝ (f*g) x) v=_
  rw [((hf x).hasFDerivAt.mul (hg x).hasFDerivAt).fderiv]
  simp only [add_apply,smul_apply,smul_eq_mul]
  ring

lemma directional_add {d : ℕ} {f g : Point d → ℝ} (hf : Differentiable ℝ f)
    (hg : Differentiable ℝ g) (v : Point d) :
    directional v (fun x => f x+g x)=fun x => directional v f x+directional v g x := by
  funext x
  exact congrArg (fun A : Point d →L[ℝ] ℝ => A v) ((hf x).hasFDerivAt.add (hg x).hasFDerivAt).fderiv

lemma directional_sum {d : ℕ} {ι : Type*} (s : Finset ι) {f : ι → Point d → ℝ}
    (hf : ∀ i∈s,Differentiable ℝ (f i)) (v : Point d) :
    directional v (fun x => ∑ i∈s,f i x)=fun x => ∑ i∈s,directional v (f i) x := by
  funext x
  have hh := HasFDerivAt.fun_sum (u:=s) (fun i hi => (hf i hi x).hasFDerivAt)
  simpa only [directional,sum_apply] using
    congrArg (fun A : Point d →L[ℝ] ℝ => A v) hh.fderiv

end LogConcaveSampling

end UpperProof
end
end
end

end OAI
end

section
-- module Solutions.OAIQ048_LC.LogConcave_JetEstimates_PolyC1
attribute [-instance] _root_.OAI.LogConcaveSampling.LowerBound.couplingLaw_probability _root_.OAI.LogConcaveSampling.LowerBound.remainingHaar_probability _root_.OAI.LogConcaveSampling.LowerBound.roundRandomLaw_probability _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_invInvariant _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_isHaar _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_probability _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_rightInvariant _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_compactSpace _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_measurableInv _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_measurableMul _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_secondCountable _root_.OAI.LogConcaveSampling.MeanTree.instIsProbabilityMeasureRowTapeRowLaw _root_.OAI.LogConcaveSampling.OracleCompiler.topSeedLaw_probability _root_.OAI.LogConcaveSampling.noiseKernel_markov
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open MeasureTheory Filter
open scoped ENNReal NNReal Topology

section UpperProof
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal RealInnerProductSpace Topology
open Function MeasureTheory Set Filter
open scoped Topology NNReal

namespace LogConcaveSampling
open MeasureTheory
open scoped RealInnerProductSpace

lemma integrable_polynomial_gibbs {d : ℕ} {H f : Point d → ℝ}
    (hH : Continuous H) (ht : HasGaussianLowerTail H) (hf : Continuous f)
    (hg : HasPolynomialGrowth f) : Integrable f (gibbs H) := by
  apply integrable_gibbs_of_weighted hH (ht.integrable_exp hH)
  simpa using integrable_tilted H hH hf ht hg 0

namespace PolyC1
variable {d : ℕ} {f g : Point d → ℝ}
lemma differentiable (hf : PolyC1 f) : Differentiable ℝ f := hf.smooth.differentiable (by norm_num)
end PolyC1

end LogConcaveSampling

end UpperProof
end
end
end

end OAI
end

section
-- module Solutions.OAIQ048_LC.LogConcave_Analysis_CompactGibbsIbp
attribute [-instance] _root_.OAI.LogConcaveSampling.LowerBound.couplingLaw_probability _root_.OAI.LogConcaveSampling.LowerBound.remainingHaar_probability _root_.OAI.LogConcaveSampling.LowerBound.roundRandomLaw_probability _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_invInvariant _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_isHaar _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_probability _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_rightInvariant _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_compactSpace _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_measurableInv _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_measurableMul _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_secondCountable _root_.OAI.LogConcaveSampling.MeanTree.instIsProbabilityMeasureRowTapeRowLaw _root_.OAI.LogConcaveSampling.OracleCompiler.topSeedLaw_probability _root_.OAI.LogConcaveSampling.noiseKernel_markov
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
namespace LogConcaveSampling
open MeasureTheory Function
open scoped RealInnerProductSpace

lemma compact_gibbs_ibp {d : ℕ} {H g : Point d → ℝ}
    (hH : ContDiff ℝ 1 H) (hi : Integrable (fun z => Real.exp (-H z)))
    (hg : ContDiff ℝ 1 g) (hgc : HasCompactSupport g) (v : Point d) :
    (∫z,directional v g z ∂gibbs H)=
      ∫z,(inner ℝ (gradient H z) v)*g z ∂gibbs H := by
  have he : ContDiff ℝ 1 (fun z => Real.exp (-H z)) := hH.neg.exp
  have hdg : Continuous (directional v g) := (hg.continuous_fderiv (by norm_num)).clm_apply continuous_const
  have hdgc : HasCompactSupport (directional v g) := hgc.fderiv_apply ℝ v
  have hD (z : Point d) : fderiv ℝ (fun z => Real.exp (-H z)) z v=
      -(Real.exp (-H z)*inner ℝ (gradient H z) v) := by
    change (fderiv ℝ (fun z => Real.exp ((-H) z)) z) v=_
    rw [((hH.differentiable (by norm_num) z).hasFDerivAt.neg.exp).fderiv]
    simp only [smul_apply,neg_apply,smul_eq_mul,←toDual_gradient,
      InnerProductSpace.toDual_apply_apply,Pi.neg_apply]
    ring
  have hh := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable (μ:=volume)
    (f:=fun z => Real.exp (-H z)) (g:=g) (v:=v)
    (((he.continuous_fderiv (by norm_num)).clm_apply continuous_const).mul hg.continuous
      |>.integrable_of_hasCompactSupport hgc.mul_left)
    ((he.continuous.mul hdg).integrable_of_hasCompactSupport hdgc.mul_left)
    ((he.continuous.mul hg.continuous).integrable_of_hasCompactSupport hgc.mul_left)
    (fun z _ => he.differentiable (by norm_num) z)
    (fun z _ => hg.differentiable (by norm_num) z)
  simp only [hD,neg_mul,mul_assoc,integral_neg,neg_neg] at hh
  rw [integral_gibbs_vector hH.continuous hi,integral_gibbs_vector hH.continuous hi]
  simpa only [smul_eq_mul,directional] using congrArg (fun a => (∫z,Real.exp (-H z))⁻¹*a) hh

end LogConcaveSampling

end

end

section

noncomputable section
namespace LogConcaveSampling
open MeasureTheory ProbabilityTheory EulerDensity
open scoped RealInnerProductSpace ENNReal

lemma standardGaussian_eq_gibbs (d : ℕ) :
    stdGaussian (Point d)=gibbs (gaussianProposalPotential d) := by
  have he : (fun z : Point d => ENNReal.ofReal (Real.exp (-‖z‖^2/2)))=
      gibbsDensity (gaussianProposalPotential d) := by
    funext z
    simp only [gibbsDensity,gaussianProposalPotential_eq,neg_div]
  have hd := standard_density d
  rw [he] at hd
  have hp := congrArg (fun μ : Measure (Point d) => μ Set.univ) hd
  rw [measure_univ,Measure.smul_apply,withDensity_apply _ MeasurableSet.univ,
    Measure.restrict_univ,smul_eq_mul] at hp
  change (1:ℝ≥0∞)=gaussianCoefficient d*partition (gaussianProposalPotential d) at hp
  rw [hd,ENNReal.eq_inv_of_mul_eq_one_left hp.symm]
  rfl

lemma compact_gaussian_ibp {d : ℕ} {g : Point d → ℝ}
    (hg : ContDiff ℝ 1 g) (hgc : HasCompactSupport g) (v : Point d) :
    (∫z,fderiv ℝ g z v ∂stdGaussian (Point d))=
      ∫z,inner ℝ z v*g z ∂stdGaussian (Point d) := by
  rw [standardGaussian_eq_gibbs]
  have hH := (gaussianProposalPotential_admissible d).smooth.of_le (by norm_num : (1:WithTop ℕ∞)≤2)
  simpa only [directional,gaussianProposalPotential_gradient,id_eq] using
    compact_gibbs_ibp hH (gaussianProposalPotential_admissible d).integrable_exp_neg hg hgc v
end LogConcaveSampling

end

end

end

end OAI
end

section
-- module Solutions.OAIQ048_LC.LogConcave_Sampling_SkewCenteringField
attribute [-instance] _root_.OAI.LogConcaveSampling.LowerBound.couplingLaw_probability _root_.OAI.LogConcaveSampling.LowerBound.remainingHaar_probability _root_.OAI.LogConcaveSampling.LowerBound.roundRandomLaw_probability _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_invInvariant _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_isHaar _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_probability _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_rightInvariant _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_compactSpace _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_measurableInv _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_measurableMul _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_secondCountable _root_.OAI.LogConcaveSampling.MeanTree.instIsProbabilityMeasureRowTapeRowLaw _root_.OAI.LogConcaveSampling.OracleCompiler.topSeedLaw_probability _root_.OAI.LogConcaveSampling.noiseKernel_markov
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
namespace LogConcaveSampling
open Set Function MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace

lemma compact_slice_left {E F : Type*} [TopologicalSpace E] [TopologicalSpace F]
    [T1Space F] {φ : E × F → ℝ} (hφ : HasCompactSupport φ) (z : F) :
    HasCompactSupport (fun y => φ (y,z)) := by
  apply hφ.comp_isClosedEmbedding
  refine ⟨isEmbedding_prodMkLeft z,?_⟩
  convert isClosed_univ.prod (isClosed_singleton (x:=z)) using 1
  all_goals try with_reducible_and_instances rfl
  ext ⟨a,b⟩
  simp only [mem_range,Prod.mk.injEq,mem_prod,mem_univ,mem_singleton_iff,true_and]
  aesop

lemma compact_slice_right {E F : Type*} [TopologicalSpace E] [TopologicalSpace F]
    [T1Space E] {φ : E × F → ℝ} (hφ : HasCompactSupport φ) (y : E) :
    HasCompactSupport (fun z => φ (y,z)) := by
  apply hφ.comp_isClosedEmbedding
  refine ⟨isEmbedding_prodMkRight y,?_⟩
  convert (isClosed_singleton (x:=y)).prod isClosed_univ using 1
  all_goals try with_reducible_and_instances rfl
  ext ⟨a,b⟩
  simp only [mem_range,Prod.mk.injEq,mem_prod,mem_univ,mem_singleton_iff,and_true]
  aesop

lemma compact_derivative_field {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {φ : E → ℝ} (hφ : HasCompactSupport φ) (W : E → E) :
    HasCompactSupport (fun p => fderiv ℝ φ p (W p)) := by
  apply HasCompactSupport.intro hφ.isCompact
  intro p hp
  rw [(HasFDerivAt.of_notMem_tsupport ℝ hp).fderiv]
  rfl

theorem product_stein_flux {d : ℕ} {μ : Measure (Point d)} [IsFiniteMeasure μ]
    {K : Point d → Point d →L[ℝ] Point d} {m : Point d → Point d}
    (hK : Continuous K) (hm : Continuous m)
    (hstein : ∀u : Point d,∀φ : Point d → ℝ,ContDiff ℝ 1 φ → HasCompactSupport φ →
      (∫y,inner ℝ u (m y)*φ y ∂μ)=∫y,fderiv ℝ φ y ((K y).adjoint u) ∂μ)
    (s : ℝ) {φ : Point d × Point d → ℝ} (hφ : ContDiff ℝ 1 φ)
    (hφc : HasCompactSupport φ) :
    (∫p,fderiv ℝ φ p (skewCenteringField K m s p) ∂μ.prod (stdGaussian (Point d)))=0 := by
  let ν := stdGaussian (Point d)
  let A := fun p : Point d × Point d => fderiv ℝ φ p ((K p.1).adjoint p.2,0)
  let B := fun p : Point d × Point d => fderiv ℝ φ p (0,m p.1)
  let C := fun p : Point d × Point d => inner ℝ p.2 (m p.1)*φ p
  have hD := hφ.continuous_fderiv (by norm_num)
  have hKA : Continuous (fun p : Point d × Point d => ((K p.1).adjoint p.2,(0:Point d))) :=
    (((ContinuousLinearMap.adjoint.continuous.comp hK).comp continuous_fst).clm_apply continuous_snd).prodMk continuous_const
  have hMB : Continuous (fun p : Point d × Point d => ((0:Point d),m p.1)) :=
    continuous_const.prodMk (hm.comp continuous_fst)
  have hAi : Integrable A (μ.prod ν) :=
    (hD.clm_apply hKA).integrable_of_hasCompactSupport (compact_derivative_field hφc _)
  have hBi : Integrable B (μ.prod ν) :=
    (hD.clm_apply hMB).integrable_of_hasCompactSupport (compact_derivative_field hφc _)
  have hCi : Integrable C (μ.prod ν) :=
    ((continuous_snd.inner (hm.comp continuous_fst)).mul hφ.continuous).integrable_of_hasCompactSupport hφc.mul_left
  have hA (g : Point d) : (∫y,A (y,g) ∂μ)=∫y,C (y,g) ∂μ := by
    have hh := hstein g (fun y => φ (y,g)) (hφ.comp (contDiff_id.prodMk contDiff_const)) (compact_slice_left hφc g)
    have hd (y : Point d) : fderiv ℝ (fun y => φ (y,g)) y=
        (fderiv ℝ φ (y,g)).comp (ContinuousLinearMap.inl ℝ (Point d) (Point d)) := by
      exact ((hφ.differentiable (by norm_num) (y,g)).hasFDerivAt.comp y
        ((hasFDerivAt_id y).prodMk (hasFDerivAt_const g y))).fderiv
    simpa only [hd,ContinuousLinearMap.comp_apply,ContinuousLinearMap.inl_apply,A,C] using hh.symm
  have hB (y : Point d) : (∫g,B (y,g) ∂ν)=∫g,C (y,g) ∂ν := by
    have hh := compact_gaussian_ibp (g:=fun g => φ (y,g)) (hφ.comp (contDiff_const.prodMk contDiff_id)) (compact_slice_right hφc y) (m y)
    have hd (g : Point d) : fderiv ℝ (fun g => φ (y,g)) g=
        (fderiv ℝ φ (y,g)).comp (ContinuousLinearMap.inr ℝ (Point d) (Point d)) := by
      exact ((hφ.differentiable (by norm_num) (y,g)).hasFDerivAt.comp g
        ((hasFDerivAt_const y g).prodMk (hasFDerivAt_id g))).fderiv
    simpa only [hd,ContinuousLinearMap.comp_apply,ContinuousLinearMap.inr_apply,B,C,ν] using hh
  have he (p : Point d × Point d) : fderiv ℝ φ p (skewCenteringField K m s p)=
      -s⁻¹*A p+s⁻¹*B p := by
    have he : skewCenteringField K m s p=
        (-s⁻¹) • ((K p.1).adjoint p.2,0)+s⁻¹ • (0,m p.1) := by
      ext <;> simp [skewCenteringField]
    rw [he,map_add,map_smul,map_smul]
    rfl
  simp_rw [he]
  rw [integral_add (hAi.const_mul _) (hBi.const_mul _),integral_const_mul,integral_const_mul]
  have hAC : (∫p,A p ∂μ.prod ν)=∫p,C p ∂μ.prod ν := by
    rw [integral_prod_symm _ hAi,integral_prod_symm _ hCi]
    exact integral_congr_ae (Filter.Eventually.of_forall hA)
  have hBC : (∫p,B p ∂μ.prod ν)=∫p,C p ∂μ.prod ν := by
    rw [integral_prod _ hBi,integral_prod _ hCi]
    exact integral_congr_ae (Filter.Eventually.of_forall hB)
  change -s⁻¹*(∫p,A p ∂μ.prod ν)+s⁻¹*(∫p,B p ∂μ.prod ν)=0
  rw [hAC,hBC]
  ring
end LogConcaveSampling

end

end

end

end OAI
end

section
-- module Solutions.OAIQ048_LC.LogConcave_Sampling_SkewCenteringFieldSmooth
attribute [-instance] _root_.OAI.LogConcaveSampling.LowerBound.couplingLaw_probability _root_.OAI.LogConcaveSampling.LowerBound.remainingHaar_probability _root_.OAI.LogConcaveSampling.LowerBound.roundRandomLaw_probability _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_invInvariant _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_isHaar _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_probability _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_rightInvariant _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_compactSpace _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_measurableInv _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_measurableMul _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_secondCountable _root_.OAI.LogConcaveSampling.MeanTree.instIsProbabilityMeasureRowTapeRowLaw _root_.OAI.LogConcaveSampling.OracleCompiler.topSeedLaw_probability _root_.OAI.LogConcaveSampling.noiseKernel_markov
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
namespace LogConcaveSampling
open Set Function MeasureTheory ProbabilityTheory
open scoped NNReal RealInnerProductSpace

lemma skewCenteringField_smooth {d : ℕ} {K : Point d → Point d →L[ℝ] Point d}
    {m : Point d → Point d} (hK : ContDiff ℝ 1 K) (hm : ContDiff ℝ 1 m) (s : ℝ) :
    ContDiff ℝ 1 (skewCenteringField K m s) := by
  have hA : ContDiff ℝ 1 (fun y : Point d => (K y).adjoint) :=
    (ContinuousLinearMap.adjoint (𝕜:=ℝ) (E:=Point d) (F:=Point d)).contDiff.comp hK
  have hAp : ContDiff ℝ 1 (fun p : Point d × Point d => (K p.1).adjoint p.2) :=
    (hA.comp contDiff_fst).clm_apply contDiff_snd
  have hmp : ContDiff ℝ 1 (fun p : Point d × Point d => m p.1) := hm.comp contDiff_fst
  exact (hAp.const_smul (-s⁻¹)).prodMk (hmp.const_smul s⁻¹)

lemma skewCenteringField_growth {d : ℕ} {K : Point d → Point d →L[ℝ] Point d}
    {m : Point d → Point d} {C : ℝ} {L : ℝ≥0} (hC : 0≤C) (hK : ∀y,‖K y‖≤C)
    (hm : LipschitzWith L m) {s : ℝ} (hs : 0 < s) (p : Point d × Point d) :
    ‖skewCenteringField K m s p‖≤ s⁻¹*(C+L)*‖p‖+s⁻¹*‖m 0‖ := by
  have hmn : ‖m p.1‖≤L*‖p.1‖+‖m 0‖ := by
    have h1 := hm.norm_sub_le p.1 0
    simpa only [sub_zero] using (norm_le_norm_sub_add (m p.1) (m 0)).trans (add_le_add h1 le_rfl)
  have hkn : ‖(K p.1).adjoint p.2‖≤C*‖p.2‖ := by
    exact (ContinuousLinearMap.le_opNorm _ _).trans (by rw [ContinuousLinearMap.adjoint.norm_map]; gcongr; exact hK _)
  change max ‖-s⁻¹ • (K p.1).adjoint p.2‖ ‖s⁻¹ • m p.1‖≤_
  rw [norm_smul,norm_smul,Real.norm_eq_abs,Real.norm_eq_abs,abs_neg,
    abs_of_pos (inv_pos.mpr hs)]
  apply max_le
  · calc
      _≤ s⁻¹*(C*‖p.2‖) := mul_le_mul_of_nonneg_left hkn (inv_nonneg.mpr hs.le)
      _≤ s⁻¹*((C+L)*‖p‖)+s⁻¹*‖m 0‖ := by
        have hp : ‖p.2‖≤‖p‖ := norm_snd_le p
        have hL : C≤C+L := le_add_of_nonneg_right L.coe_nonneg
        have hh : C*‖p.2‖≤(C+L)*‖p‖ := mul_le_mul hL hp (norm_nonneg _) (by positivity)
        exact (mul_le_mul_of_nonneg_left hh (inv_nonneg.mpr hs.le)).trans (le_add_of_nonneg_right (by positivity))
      _=_ := by ring
  · calc
      _≤ s⁻¹*(L*‖p.1‖+‖m 0‖) := mul_le_mul_of_nonneg_left hmn (inv_nonneg.mpr hs.le)
      _≤ s⁻¹*((C+L)*‖p‖+‖m 0‖) := by
        apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr hs.le)
        apply add_le_add_left
        exact mul_le_mul (le_add_of_nonneg_left hC) (norm_fst_le p) (norm_nonneg _) (by positivity)
      _=_ := by ring

lemma integrable_product_norm {E F : Type*} [NormedAddCommGroup E] [NormedAddCommGroup F]
    [MeasurableSpace E] [MeasurableSpace F] [BorelSpace E] [BorelSpace F]
    [SecondCountableTopology E] [SecondCountableTopology F]
    {μ : Measure E} {ν : Measure F} [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (hμ : Integrable (fun x => ‖x‖) μ) (hν : Integrable (fun y => ‖y‖) ν) :
    Integrable (fun p : E × F => ‖p‖) (μ.prod ν) := by
  apply ((hμ.comp_fst ν).add (hν.comp_snd μ)).mono' continuous_norm.aestronglyMeasurable
  filter_upwards [] with p
  rw [norm_norm]
  exact max_le (le_add_of_nonneg_right (norm_nonneg _)) (le_add_of_nonneg_left (norm_nonneg _))

end LogConcaveSampling

end

end

end

end OAI
end

section
-- module Solutions.OAIQ048_LC.LogConcave_Dynamics_FlowRestrict
attribute [-instance] _root_.OAI.LogConcaveSampling.LowerBound.couplingLaw_probability _root_.OAI.LogConcaveSampling.LowerBound.remainingHaar_probability _root_.OAI.LogConcaveSampling.LowerBound.roundRandomLaw_probability _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_invInvariant _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_isHaar _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_probability _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_rightInvariant _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_compactSpace _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_measurableInv _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_measurableMul _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_secondCountable _root_.OAI.LogConcaveSampling.MeanTree.instIsProbabilityMeasureRowTapeRowLaw _root_.OAI.LogConcaveSampling.OracleCompiler.topSeedLaw_probability _root_.OAI.LogConcaveSampling.noiseKernel_markov
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
namespace LogConcaveSampling.LinearGrowthODE
open Set MeasureTheory

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

omit [MeasurableSpace E] [BorelSpace E] in
lemma flow_restrict {f : E → E} (hf : ContDiff ℝ 1 f) {K B a b c : ℝ}
    (hK : 0≤K) (hB : 0≤B) (hg : ∀x,‖f x‖≤K*‖x‖+B) (hab : a≤b)
    (hc : c∈Icc a b) (x : E) :
    EqOn (flow hf hK hB hg hab x) (flow hf hK hB hg hc.1 x) (Icc a c) := by
  apply unique hf (flow_continuous hf hK hB hg hab x).continuousOn
    (flow_continuous hf hK hB hg hc.1 x).continuousOn
  · intro t ht
    exact (flow_deriv hf hK hB hg hab x t ⟨ht.1,ht.2.trans hc.2⟩).mono
      (Icc_subset_Icc le_rfl hc.2)
  · exact flow_deriv hf hK hB hg hc.1 x
  · rw [flow_initial,flow_initial]

theorem stationary_at {f : E → E} (hf : ContDiff ℝ 1 f) {K B a b : ℝ}
    (hK : 0≤K) (hB : 0≤B) (hg : ∀x,‖f x‖≤K*‖x‖+B) (hab : a≤b)
    {μ : Measure E} [IsFiniteMeasure μ] (hfi : Integrable (fun x => ‖f x‖) μ)
    (hflux : ∀ψ : E → ℝ,ContDiff ℝ 1 ψ → HasCompactSupport ψ →
      (∫x,(fderiv ℝ ψ x) (f x) ∂μ)=0) {t : ℝ} (ht : t∈Icc a b) :
    μ.map (fun y => flow hf hK hB hg hab y t)=μ := by
  obtain he|hlt := ht.1.eq_or_lt
  · subst t
    simp only [flow_initial]
    exact Measure.map_id
  · have hEq : (fun y => flow hf hK hB hg hab y t)=
        (fun y => flow hf hK hB hg hlt.le y t) := by
      funext y
      exact flow_restrict hf hK hB hg hab ht y ⟨ht.1,le_rfl⟩
    rw [hEq]
    exact stationary_law hf hK hB hg hlt hfi hflux
end LogConcaveSampling.LinearGrowthODE

end

end

section

noncomputable section
namespace LogConcaveSampling
open Set Function MeasureTheory ProbabilityTheory
open scoped NNReal RealInnerProductSpace

theorem exists_skew_centering_flow {d : ℕ} {μ : Measure (Point d)} [IsFiniteMeasure μ]
    {K : Point d → Point d →L[ℝ] Point d} {m : Point d → Point d}
    (hK : ContDiff ℝ 1 K) (hm : ContDiff ℝ 1 m) {C : ℝ} {L : ℝ≥0}
    (hC : 0≤C) (hKb : ∀y,‖K y‖≤C) (hmL : LipschitzWith L m)
    (hμ : Integrable (fun y => ‖y‖) μ)
    (hstein : ∀u : Point d,∀φ : Point d → ℝ,ContDiff ℝ 1 φ → HasCompactSupport φ →
      (∫y,inner ℝ u (m y)*φ y ∂μ)=∫y,fderiv ℝ φ y ((K y).adjoint u) ∂μ)
    {s a b : ℝ} (hs : 0 < s) (hab : a≤b) :
    ∃Ψ : (Point d × Point d) → ℝ → (Point d × Point d),
      (∀p,Continuous (Ψ p) ∧ Ψ p a=p ∧ ∀t∈Icc a b,
        HasDerivWithinAt (Ψ p) (skewCenteringField K m s (Ψ p t)) (Icc a b) t) ∧
      (∀t∈Icc a b,Continuous (fun p => Ψ p t)) ∧
      (∀t∈Icc a b,(μ.prod (stdGaussian (Point d))).map (fun p => Ψ p t)=μ.prod (stdGaussian (Point d))) := by
  let f := skewCenteringField K m s
  have hf : ContDiff ℝ 1 f := skewCenteringField_smooth hK hm s
  have hk : 0≤ s⁻¹*(C+L) := by positivity
  have hb : 0≤ s⁻¹*‖m 0‖ := by positivity
  have hg : ∀p,‖f p‖≤ s⁻¹*(C+L)*‖p‖+s⁻¹*‖m 0‖ := skewCenteringField_growth hC hKb hmL hs
  let Ψ := LinearGrowthODE.flow hf hk hb hg hab
  refine ⟨Ψ,?_,?_,?_⟩
  · intro p
    exact ⟨LinearGrowthODE.flow_continuous hf hk hb hg hab p,
      LinearGrowthODE.flow_initial hf hk hb hg hab p,
      LinearGrowthODE.flow_deriv hf hk hb hg hab p⟩
  · exact fun t ht => LinearGrowthODE.flow_continuous_initial hf hk hb hg hab t ht
  · have hi : Integrable (fun g : Point d => ‖g‖) (stdGaussian (Point d)) := IsGaussian.integrable_id.norm
    have hprod := integrable_product_norm hμ hi
    have hfi : Integrable (fun p => ‖f p‖) (μ.prod (stdGaussian (Point d))) := by
      apply ((hprod.const_mul (s⁻¹*(C+L))).add (integrable_const (s⁻¹*‖m 0‖))).mono' hf.continuous.norm.aestronglyMeasurable
      filter_upwards [] with p
      rw [norm_norm]
      exact hg p
    exact fun t ht => LinearGrowthODE.stationary_at hf hk hb hg hab hfi
      (fun φ hφ hφc => product_stein_flux hK.continuous hm.continuous hstein s hφ hφc) ht

end LogConcaveSampling

end

end

end

end OAI
end

section
-- module Solutions.OAIQ048_LC.LogConcave_Analysis_InterpolationPotential
attribute [-instance] _root_.OAI.LogConcaveSampling.LowerBound.couplingLaw_probability _root_.OAI.LogConcaveSampling.LowerBound.remainingHaar_probability _root_.OAI.LogConcaveSampling.LowerBound.roundRandomLaw_probability _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_invInvariant _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_isHaar _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_probability _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_rightInvariant _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_compactSpace _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_measurableInv _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_measurableMul _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_secondCountable _root_.OAI.LogConcaveSampling.MeanTree.instIsProbabilityMeasureRowTapeRowLaw _root_.OAI.LogConcaveSampling.OracleCompiler.topSeedLaw_probability _root_.OAI.LogConcaveSampling.noiseKernel_markov
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open MeasureTheory Filter
open scoped ENNReal NNReal Topology

section UpperProof
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal RealInnerProductSpace Topology

namespace LogConcaveSampling
open MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace ENNReal

lemma interpolation_exponent {d : ℕ} (F : Point d → ℝ) (x : Point d)
    (r ρ : ℝ) (y z : Point d) (ha : 1-ρ^2≠0) :
    -primitivePotential F x r z-‖y-ρ • z‖^2/(2*(1-ρ^2))=
      -‖y‖^2/(2*(1-ρ^2))+
        (inner ℝ (conditionalParameter (ρ,y)).1 z-
          (conditionalParameter (ρ,y)).2*‖z‖^2-primitivePotential F x r z) := by
  simp only [norm_sub_sq_real,norm_smul,Real.norm_eq_abs,mul_pow,sq_abs,
    inner_smul_right,inner_smul_left,conditionalParameter,conj_trivial]
  rw [real_inner_comm z y]
  field_simp
  ring

lemma interpolation_density_integral {d : ℕ} {F : Point d → ℝ} {lam : ℝ≥0}
    (hF : Primitive F lam) (x : Point d) {r ρ : ℝ} (hr : 0 ≤ r)
    (hl : (lam:ℝ)*r^2<1) (hρ : ρ^2<1) (y : Point d) :
    (∫⁻ z,ENNReal.ofReal (Real.exp (-primitivePotential F x r z-
      ‖y-ρ • z‖^2/(2*(1-ρ^2)))))=gibbsDensity (interpolationPotential F x r ρ) y := by
  obtain ⟨m,hm,C,ht⟩ := hF.hasGaussianLowerTail x hr hl
  let p := conditionalParameter (ρ,y)
  have hp : 0 < m+p.2 := by dsimp [p,conditionalParameter]; positivity
  have hi := integrable_quadraticTilt (hF.continuous_potential x r) continuous_const ht
    (growth_const (1:ℝ)) p hp
  have hz := quadratic_partition_pos (hF.continuous_potential x r) ht p hp
  have he : ∀ z,Real.exp (-primitivePotential F x r z-‖y-ρ • z‖^2/(2*(1-ρ^2)))=
      Real.exp (-‖y‖^2/(2*(1-ρ^2)))*
        Real.exp (inner ℝ p.1 z-p.2*‖z‖^2-primitivePotential F x r z) := by
    intro z
    rw [interpolation_exponent F x r ρ y z (by linarith),Real.exp_add]
  simp_rw [he,ENNReal.ofReal_mul (Real.exp_pos _).le]
  have hH := (hF.continuous_potential x r).measurable
  rw [lintegral_const_mul _ (by fun_prop)]
  have ht' : (∫⁻ z, ENNReal.ofReal (Real.exp (inner ℝ p.1 z-p.2*‖z‖^2-
      primitivePotential F x r z)))=ENNReal.ofReal (quadraticTilt (primitivePotential F x r) (fun _ => (1:ℝ)) p) := by
    dsimp [quadraticTilt]
    simp only [smul_eq_mul,mul_one] at hi ⊢
    rw [integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall fun _ => (Real.exp_pos _).le)
      hi.aestronglyMeasurable,ENNReal.ofReal_toReal
        ((lintegral_ofReal_ne_top_iff_integrable hi.aestronglyMeasurable
          (Filter.Eventually.of_forall fun _ => (Real.exp_pos _).le)).2 hi)]
  rw [ht',←ENNReal.ofReal_mul (Real.exp_pos _).le]
  unfold gibbsDensity interpolationPotential
  congr 1
  rw [neg_sub,Real.exp_sub,Real.exp_log hz]
  dsimp [p]
  rw [neg_div,Real.exp_neg]
  ring

end LogConcaveSampling

end UpperProof
end
end
end

end OAI
end

section
-- module Solutions.OAIQ048_LC.LogConcave_Analysis_GaussianMarginalLowerTail
attribute [-instance] _root_.OAI.LogConcaveSampling.LowerBound.couplingLaw_probability _root_.OAI.LogConcaveSampling.LowerBound.remainingHaar_probability _root_.OAI.LogConcaveSampling.LowerBound.roundRandomLaw_probability _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_invInvariant _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_isHaar _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_probability _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_rightInvariant _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_compactSpace _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_measurableInv _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_measurableMul _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_secondCountable _root_.OAI.LogConcaveSampling.MeanTree.instIsProbabilityMeasureRowTapeRowLaw _root_.OAI.LogConcaveSampling.OracleCompiler.topSeedLaw_probability _root_.OAI.LogConcaveSampling.noiseKernel_markov
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
namespace LogConcaveSampling
open MeasureTheory
open scoped RealInnerProductSpace NNReal

lemma gaussian_marginal_lowerTail {d : ℕ} {P H : Point d → ℝ}
    (hP : Continuous P) (ht : HasGaussianLowerTail P) {a ρ : ℝ}
    (ha : 0<a) (hρ : ρ^2≤1)
    (hD : ∀y,(∫⁻z,ENNReal.ofReal (Real.exp (-P z-‖y-ρ • z‖^2/(2*a))))=
      ENNReal.ofReal (Real.exp (-H y))) : HasGaussianLowerTail H := by
  obtain ⟨m,hm,C,hC⟩ := ht
  let b := min m a⁻¹/4
  have hb : 0<b := div_pos (lt_min hm (inv_pos.mpr ha)) (by norm_num)
  have hb1 : 2*b≤ m/2 := by dsimp [b]; linarith [min_le_left m a⁻¹]
  have hb2 : 2*b≤1/(2*a) := by
    have he : a⁻¹/2=1/(2*a) := by field_simp
    rw [←he]
    dsimp [b]; linarith [min_le_right m a⁻¹]
  let J := ∫z : Point d,Real.exp (-(m/2)*‖z‖^2)
  have hJ : 0≤J := integral_nonneg (fun _ => (Real.exp_pos _).le)
  refine ⟨b,hb,C+Real.log (J+1),fun y => ?_⟩
  have hpoint : ∀z : Point d,Real.exp (-P z-‖y-ρ • z‖^2/(2*a))≤
      Real.exp (C-b*‖y‖^2)*Real.exp (-(m/2)*‖z‖^2) := by
    intro z
    have hsum := norm_add_le (y-ρ • z) (ρ • z)
    rw [sub_add_cancel] at hsum
    have hy : ‖y‖^2≤2*‖y-ρ • z‖^2+2*‖z‖^2 := by
      have hs := pow_le_pow_left₀ (norm_nonneg y) hsum 2
      have hz : ‖ρ • z‖^2≤‖z‖^2 := by
        rw [norm_smul,mul_pow,Real.norm_eq_abs,sq_abs]
        exact mul_le_of_le_one_left (sq_nonneg _) hρ
      nlinarith [sq_nonneg (‖y-ρ • z‖-‖ρ • z‖)]
    have hby := mul_le_mul_of_nonneg_left hy hb.le
    have h1 := mul_le_mul_of_nonneg_right hb1 (sq_nonneg ‖z‖)
    have h2 := mul_le_mul_of_nonneg_right hb2 (sq_nonneg ‖y-ρ • z‖)
    rw [←Real.exp_add]
    apply Real.exp_le_exp.mpr
    have he : ‖y-ρ • z‖^2/(2*a)=(1/(2*a))*‖y-ρ • z‖^2 := by ring
    rw [he]
    nlinarith [hC z]
  have hbound : Integrable (fun z : Point d =>
      Real.exp (C-b*‖y‖^2)*Real.exp (-(m/2)*‖z‖^2)) :=
    (integrable_gaussian_envelope d (by positivity : 0 < m/2)).const_mul _
  have hk : Integrable (fun z : Point d => Real.exp (-P z-‖y-ρ • z‖^2/(2*a))) := by
    apply hbound.mono' (by fun_prop)
    filter_upwards [] with z
    simpa only [Real.norm_eq_abs,abs_of_pos (Real.exp_pos _)] using hpoint z
  have he : (∫z,Real.exp (-P z-‖y-ρ • z‖^2/(2*a)))=Real.exp (-H y) := by
    have hh := hD y
    rw [←ofReal_integral_eq_lintegral_ofReal hk
      (Filter.Eventually.of_forall (fun _ => (Real.exp_pos _).le))] at hh
    have h := congrArg ENNReal.toReal hh
    simpa only [ENNReal.toReal_ofReal (integral_nonneg (fun _ => (Real.exp_pos _).le)),
      ENNReal.toReal_ofReal (Real.exp_pos _).le] using h
  have hi := integral_mono hk hbound hpoint
  rw [he,integral_const_mul] at hi
  change Real.exp (-H y)≤Real.exp (C-b*‖y‖^2)*J at hi
  have hh : Real.exp (-H y)≤Real.exp (C-b*‖y‖^2+Real.log (J+1)) := by
    rw [Real.exp_add,Real.exp_log (by linarith : 0<J+1)]
    exact hi.trans (mul_le_mul_of_nonneg_left (by linarith) (Real.exp_pos _).le)
  have := Real.exp_le_exp.mp hh
  linarith

lemma interpolationPotential_lowerTail {d : ℕ} {F : Point d → ℝ} {lam : ℝ≥0}
    (hF : Primitive F lam) (x : Point d) {r ρ : ℝ} (hr : 0 ≤ r)
    (hl : (lam:ℝ)*r^2<1) (hρ0 : 0≤ρ) (hρ1 : ρ<1) :
    HasGaussianLowerTail (interpolationPotential F x r ρ) := by
  have ha := (probability_time hρ0 hρ1).1
  apply gaussian_marginal_lowerTail (hF.continuous_potential x r)
    (hF.hasGaussianLowerTail x hr hl) ha (by linarith)
  intro y
  exact interpolation_density_integral hF x hr hl (by linarith) y

lemma interpolationPotential_gradient_lipschitz {d : ℕ} {F : Point d → ℝ} {lam : ℝ≥0}
    (hF : Primitive F lam) (x : Point d) {r ρ : ℝ} (hr : 0 ≤ r)
    (hl : (lam:ℝ)*r^2≤1/2) (hρ0 : 0≤ρ) (hρ1 : ρ<1) :
    LipschitzWith (1+‖r*ρ‖₊*⟨(Real.pi^2/2)*ρ*((lam:ℝ)*r),by positivity⟩)
      (gradient (interpolationPotential F x r ρ)) := by
  have he := funext (interpolationPotential_gradient hF x hr hl hρ0 hρ1)
  rw [he]
  exact LipschitzWith.id.add ((lipschitzWith_smul (r*ρ)).comp (conditionalFieldMean_lipschitz hF x hr hl hρ0 hρ1))

end LogConcaveSampling

end

end

end

end OAI
end

section
-- module Solutions.OAIQ048_LC.LogConcave_Sampling_AdjointCoordinateContinuous
attribute [-instance] _root_.OAI.LogConcaveSampling.LowerBound.couplingLaw_probability _root_.OAI.LogConcaveSampling.LowerBound.remainingHaar_probability _root_.OAI.LogConcaveSampling.LowerBound.roundRandomLaw_probability _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_invInvariant _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_isHaar _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_probability _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_rightInvariant _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_compactSpace _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_measurableInv _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_measurableMul _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_secondCountable _root_.OAI.LogConcaveSampling.MeanTree.instIsProbabilityMeasureRowTapeRowLaw _root_.OAI.LogConcaveSampling.OracleCompiler.topSeedLaw_probability _root_.OAI.LogConcaveSampling.noiseKernel_markov
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open MeasureTheory Filter
open scoped ENNReal NNReal Topology

section UpperProof
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal RealInnerProductSpace Topology
open Function MeasureTheory Set Filter
open scoped Topology NNReal

namespace LogConcaveSampling
open MeasureTheory
open scoped RealInnerProductSpace NNReal

lemma jet_neg {d : ℕ} {ι : Type*} {f : Point d → ℝ}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (v : ι → Point d) (l : List ι) :
    JetCalculus.jet v l (fun x => -f x)=fun x => -JetCalculus.jet v l f x := by
  simpa only [neg_one_mul] using JetCalculus.jet_const_mul hf v l (-1)

end LogConcaveSampling

end UpperProof
end
end
end

end OAI
end

section
-- module Solutions.OAIQ048_LC.LogConcave_JetEstimates_PolySmooth
attribute [-instance] _root_.OAI.LogConcaveSampling.LowerBound.couplingLaw_probability _root_.OAI.LogConcaveSampling.LowerBound.remainingHaar_probability _root_.OAI.LogConcaveSampling.LowerBound.roundRandomLaw_probability _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_invInvariant _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_isHaar _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_probability _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_rightInvariant _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_compactSpace _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_measurableInv _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_measurableMul _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_secondCountable _root_.OAI.LogConcaveSampling.MeanTree.instIsProbabilityMeasureRowTapeRowLaw _root_.OAI.LogConcaveSampling.OracleCompiler.topSeedLaw_probability _root_.OAI.LogConcaveSampling.noiseKernel_markov
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open MeasureTheory Filter
open scoped ENNReal NNReal Topology

section UpperProof
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal RealInnerProductSpace Topology
open Function MeasureTheory Set Filter
open scoped Topology NNReal

namespace LogConcaveSampling
open MeasureTheory
open scoped RealInnerProductSpace NNReal

namespace PolySmooth
variable {d : ℕ} {f g H : Point d → ℝ}

lemma jet_growth (hf : PolySmooth f) {ι : Type*} (b : ι → Point d) (l : List ι) :
    HasPolynomialGrowth (JetCalculus.jet b l f) := by
  have hh := hf.growth (l.map b)
  simpa only [JetCalculus.jet_map,Function.id_comp] using hh

lemma directional (hf : PolySmooth f) (v : Point d) : PolySmooth (LogConcaveSampling.directional v f) := by
  refine ⟨directional_smooth hf.smooth v,fun l => ?_⟩
  have he : JetCalculus.jet id [v] f=LogConcaveSampling.directional v f := rfl
  have hh := hf.growth (l++[v])
  rw [JetCalculus.jet_append,he] at hh
  exact hh

lemma jet (hf : PolySmooth f) {ι : Type*} (b : ι → Point d) (l : List ι) :
    PolySmooth (JetCalculus.jet b l f) := by
  induction l with
  | nil => exact hf
  | cons i l ih => exact ih.directional (b i)

lemma polyC1 (hf : PolySmooth f) : PolyC1 f :=
  ⟨hf.smooth.of_le (by simp),hf.growth [],fun v => (hf.directional v).growth []⟩

lemma add (hf : PolySmooth f) (hg : PolySmooth g) : PolySmooth (fun x => f x+g x) := by
  refine ⟨hf.smooth.add hg.smooth,fun l => ?_⟩
  rw [JetCalculus.jet_add hf.smooth hg.smooth]
  exact Appell.HasGrowth.add (hf.growth l) (hg.growth l)

lemma neg (hf : PolySmooth f) : PolySmooth (fun x => -f x) := by
  refine ⟨hf.smooth.neg,fun l => ?_⟩
  rw [jet_neg hf.smooth]
  simpa only [HasPolynomialGrowth,Appell.HasGrowth,neg_one_mul] using
    Appell.HasGrowth.mul (growth_const (-1:ℝ)) (hf.growth l)

lemma mul (hf : PolySmooth f) (hg : PolySmooth g) : PolySmooth (fun x => f x*g x) := by
  refine ⟨hf.smooth.mul hg.smooth,fun l => ?_⟩
  induction l generalizing f g with
  | nil => exact Appell.HasGrowth.mul (hf.growth []) (hg.growth [])
  | cons v l ih =>
    change HasPolynomialGrowth (LogConcaveSampling.directional v
      (JetCalculus.jet id l (fun x => f x*g x)))
    rw [←jet_directional (hf.smooth.mul hg.smooth),
      directional_mul hf.polyC1.differentiable hg.polyC1.differentiable,
      JetCalculus.jet_add ((hf.directional v).smooth.mul hg.smooth)
        (hf.smooth.mul (hg.directional v).smooth)]
    exact Appell.HasGrowth.add (ih (hf.directional v) hg) (ih hf (hg.directional v))

lemma sum {ι : Type*} (s : Finset ι) {f : ι → Point d → ℝ}
    (hf : ∀i∈s,PolySmooth (f i)) : PolySmooth (fun x => ∑i∈s,f i x) := by
  refine ⟨ContDiff.sum (fun i hi => (hf i hi).smooth),fun l => ?_⟩
  rw [JetCalculus.jet_sum s (fun i hi => (hf i hi).smooth)]
  exact Appell.HasGrowth.sum s (fun i hi => (hf i hi).growth l)

lemma adjoint (hH : PolySmooth H) (hf : PolySmooth f) (v : Point d) :
    PolySmooth (adjointCoordinate H v f) :=
  (hf.directional v).neg.add ((hH.directional v).mul hf)

lemma const (c : ℝ) : PolySmooth (fun _ : Point d => c) := by
  refine ⟨contDiff_const,fun l => ?_⟩
  rw [JetCalculus.jet_const]
  split_ifs <;> exact growth_const _

lemma integrable (hf : PolySmooth f) (hH : Continuous H) (ht : HasGaussianLowerTail H) :
    Integrable f (gibbs H) :=
  integrable_polynomial_gibbs hH ht hf.smooth.continuous (hf.growth [])

lemma tensorAdjoint {ι : Type*} [Fintype ι] {V : ι → Point d → ℝ}
    (hH : PolySmooth H) (hV : ∀i,PolySmooth (V i)) (b : ι → Point d) :
    PolySmooth (LogConcaveSampling.tensorAdjoint H b V) :=
  sum Finset.univ (fun i _ => hH.adjoint (hV i) (b i))
end PolySmooth
end LogConcaveSampling

end UpperProof
end
end
end

end OAI
end

section
-- module Solutions.OAIQ048_LC.LogConcave_JetEstimates_SpaceBasis
attribute [-instance] _root_.OAI.LogConcaveSampling.LowerBound.couplingLaw_probability _root_.OAI.LogConcaveSampling.LowerBound.remainingHaar_probability _root_.OAI.LogConcaveSampling.LowerBound.roundRandomLaw_probability _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_invInvariant _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_isHaar _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_probability _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_rightInvariant _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_compactSpace _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_measurableInv _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_measurableMul _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_secondCountable _root_.OAI.LogConcaveSampling.MeanTree.instIsProbabilityMeasureRowTapeRowLaw _root_.OAI.LogConcaveSampling.OracleCompiler.topSeedLaw_probability _root_.OAI.LogConcaveSampling.noiseKernel_markov
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
namespace LogConcaveSampling
open MeasureTheory
open scoped Classical BigOperators NNReal RealInnerProductSpace

lemma PolySmooth.linear {d : ℕ} (L : Point d →L[ℝ] ℝ) : PolySmooth L := by
  apply PolySmooth.of_basis_growth L.contDiff
  intro l
  cases l with
  | nil => exact growth_of_lipschitz L.lipschitz
  | cons i l =>
    change HasPolynomialGrowth (LogConcaveSampling.directional (EuclideanSpace.basisFun (Fin d) ℝ i)
      (JetCalculus.jet (EuclideanSpace.basisFun (Fin d) ℝ) l L))
    rw [←jet_directional L.contDiff]
    have he : LogConcaveSampling.directional (EuclideanSpace.basisFun (Fin d) ℝ i) L=
        fun _ => L (EuclideanSpace.basisFun (Fin d) ℝ i) := by
      funext y
      simp [LogConcaveSampling.directional]
    rw [he,JetCalculus.jet_const]
    split_ifs <;> exact growth_const _

lemma growth_potential_of_gradient_lipschitz {d : ℕ} {H : Point d → ℝ} {K : ℝ≥0}
    (hH : ContDiff ℝ 2 H) (hK : LipschitzWith K (gradient H)) : HasPolynomialGrowth H := by
  let C := |H 0|+‖gradient H 0‖+(K:ℝ)+1
  have hC : 0≤C := by dsimp [C]; positivity
  refine ⟨C,hC,2,fun y => ?_⟩
  have ht := quadratic_remainder_of_gradient_lipschitz hH hK 0 y
  rw [zero_add] at ht
  have hi := abs_real_inner_le_norm y (gradient H 0)
  have hb : |H y|≤|H 0|+‖y‖*‖gradient H 0‖+(K:ℝ)*‖y‖^2/2 := by
    have he : H y=(H y-H 0-inner ℝ y (gradient H 0))+H 0+inner ℝ y (gradient H 0) := by ring
    calc
      |H y| = |(H y-H 0-inner ℝ y (gradient H 0))+H 0+inner ℝ y (gradient H 0)| := congrArg abs he
      _ ≤ |H y-H 0-inner ℝ y (gradient H 0)|+|H 0|+|inner ℝ y (gradient H 0)| :=
        (abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
      _ ≤ _ := by linarith
  have hy : ‖y‖≤1+‖y‖^2 := by nlinarith [sq_nonneg (‖y‖-1)]
  have hh := mul_le_mul_of_nonneg_right hy (norm_nonneg (gradient H 0))
  change ‖H y‖≤C*(1+‖y‖^2)
  rw [Real.norm_eq_abs]
  dsimp [C]
  nlinarith [mul_nonneg (abs_nonneg (H 0)) (sq_nonneg ‖y‖),
    mul_nonneg (show (0:ℝ)≤K from K.coe_nonneg) (sq_nonneg ‖y‖)]

lemma interpolationPotential_polySmooth {d : ℕ} {F : Point d → ℝ} {lam : ℝ≥0}
    (hF : Primitive F lam) (x : Point d) {r ρ : ℝ} (hr : 0 < r)
    (hlam : 0 < lam) (hl : (lam:ℝ)*r^2≤1/2) (hρ0 : 0≤ρ) (hρ1 : ρ<1) :
    PolySmooth (interpolationPotential F x r ρ) := by
  have hs := interpolationPotential_smooth hF x hr.le hl hρ0 hρ1
  apply PolySmooth.of_basis_growth hs
  intro l
  cases l with
  | nil =>
    exact growth_potential_of_gradient_lipschitz (hs.of_le (WithTop.coe_le_coe.mpr (show (2:ℕ∞)≤⊤ from le_top)))
      (interpolationPotential_gradient_lipschitz hF x hr.le hl hρ0 hρ1)
  | cons i l =>
    let v := EuclideanSpace.basisFun (Fin d) ℝ i
    change HasPolynomialGrowth (directional v
      (JetCalculus.jet (EuclideanSpace.basisFun (Fin d) ℝ) l (interpolationPotential F x r ρ)))
    rw [←jet_directional hs]
    have he : directional v (interpolationPotential F x r ρ)=fun y =>
        inner ℝ v y+(r*ρ)*inner ℝ v (conditionalFieldMean F x r ρ y) := by
      funext y
      rw [directional_gradient,interpolationPotential_gradient hF x hr.le hl hρ0 hρ1,
        real_inner_comm,inner_add_right,inner_smul_right]
    rw [he]
    exact ((PolySmooth.linear (innerSL ℝ v)).add ((PolySmooth.const (r*ρ)).mul
      (conditionalFieldMean_component_polySmooth hF x hr hlam hl hρ0 hρ1 i))).jet_growth _ l

end LogConcaveSampling

end

end

end

end OAI
end

section
-- module Solutions.OAIQ048_LC.LogConcave_Dynamics_VariationalField
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section

noncomputable section
namespace LogConcaveSampling.GlobalODE
open Set Function Filter Metric
open scoped Topology NNReal

lemma flow_congr {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {a b : ℝ} {f g : ℝ → E → E} {K L : ℝ≥0}
    (hf : Continuous (uncurry f)) (hg : Continuous (uncurry g))
    (hL : ∀t∈Icc a b,LipschitzWith K (f t))
    (hJ : ∀t∈Icc a b,LipschitzWith L (g t))
    (he : ∀t∈Icc a b,∀x,f t x=g t x) (s t : Icc a b) (x : E) :
    flow hL hf s x t=flow hJ hg s x t := by
  have hd (u : ℝ) (hu : u∈Icc a b) := flow_deriv hJ hg s x u hu
  have hh := trajectory_dist hL (flow_continuous hL hf s x).continuousOn
    (flow_deriv hL hf s x) (flow_continuous hJ hg s x).continuousOn
    (fun u hu => (he u hu _) ▸ flow_deriv hJ hg s x u hu) s t
  simpa only [flow_initial,dist_self,zero_mul,dist_le_zero] using hh
end LogConcaveSampling.GlobalODE

end

end

end

end OAI
end

section
-- module Solutions.OAIQ048_LC.LogConcave_Sampling_TimeBump
attribute [-instance] _root_.OAI.LogConcaveSampling.LowerBound.couplingLaw_probability _root_.OAI.LogConcaveSampling.LowerBound.remainingHaar_probability _root_.OAI.LogConcaveSampling.LowerBound.roundRandomLaw_probability _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_invInvariant _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_isHaar _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_probability _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_rightInvariant _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_compactSpace _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_measurableInv _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_measurableMul _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_secondCountable _root_.OAI.LogConcaveSampling.MeanTree.instIsProbabilityMeasureRowTapeRowLaw _root_.OAI.LogConcaveSampling.OracleCompiler.topSeedLaw_probability _root_.OAI.LogConcaveSampling.noiseKernel_markov
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
namespace LogConcaveSampling
open Set Function Filter Metric
open scoped Topology NNReal

lemma probabilityTransport_contDiff {d : ℕ} {F : Point d → ℝ} {lam : ℝ≥0}
    (hF : Primitive F lam) (x : Point d) {r T : ℝ} (hr : 0 ≤ r)
    (hl : (lam:ℝ)*r^2≤1/2) (hT0 : 0≤T) (hT1 : T<1)
    (s t : Icc (0:ℝ) T) (n : ℕ) :
    ContDiff ℝ (n:WithTop ℕ∞) (probabilityTransport hF x hr hl hT0 hT1 s t) := by
  let f := smoothProbabilityVelocity F x r hT0 hT1
  have hf := smoothProbabilityVelocity_contDiff hF x hr hl hT0 hT1 n
  have hL : ∀u∈Icc 0 T,LipschitzWith ⟨(Real.pi^2/2)*(lam:ℝ)*r^2,by positivity⟩ (f u) := by
    intro u hu
    change LipschitzWith _ (fun y => probabilityVelocity F x r (smoothTimeClip hT0 hT1 u) y)
    rw [smoothTimeClip_eq hT0 hT1 hu]
    exact probabilityVelocity_lipschitz hF x hr hl hu hT1
  have he : probabilityTransport hF x hr hl hT0 hT1 s t=
      (fun z => GlobalODE.flow hL hf.continuous s z t) := by
    funext z
    apply GlobalODE.flow_congr
    intro u hu y
    rw [clampedProbabilityVelocity_eq F x r T hT0 hu]
    dsimp [f,smoothProbabilityVelocity]
    rw [smoothTimeClip_eq hT0 hT1 hu]
  rw [he]
  exact GlobalODE.smooth_flow hf hL hT0 s t
end LogConcaveSampling

end

end

end

end OAI
end

section
-- module Solutions.OAIQ048_LC.LogConcave_Sampling_TerminalBackward
attribute [-instance] _root_.OAI.LogConcaveSampling.LowerBound.couplingLaw_probability _root_.OAI.LogConcaveSampling.LowerBound.remainingHaar_probability _root_.OAI.LogConcaveSampling.LowerBound.roundRandomLaw_probability _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_invInvariant _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_isHaar _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_probability _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_rightInvariant _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_compactSpace _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_measurableInv _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_measurableMul _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_secondCountable _root_.OAI.LogConcaveSampling.MeanTree.instIsProbabilityMeasureRowTapeRowLaw _root_.OAI.LogConcaveSampling.OracleCompiler.topSeedLaw_probability _root_.OAI.LogConcaveSampling.noiseKernel_markov
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
namespace LogConcaveSampling
open Set Function MeasureTheory ProbabilityTheory
open scoped Topology NNReal

variable {d : ℕ} {F : Point d → ℝ} {lam : ℝ≥0}
  (hF : Primitive F lam) (x : Point d) {r T : ℝ} (hr : 0 ≤ r)
  (hl : (lam:ℝ)*r^2≤1/2) (hT0 : 0≤T) (hT1 : T<1)

lemma probabilityTransport_continuous (s t : Icc (0:ℝ) T) :
    Continuous (probabilityTransport hF x hr hl hT0 hT1 s t) :=
  (GlobalODE.flow_lipschitz _ _ s t).continuous

end LogConcaveSampling

end

end

end

end OAI
end

section
-- module Solutions.OAIQ048_LC.LogConcave_Sampling_SpatialTensor
attribute [-instance] _root_.OAI.LogConcaveSampling.LowerBound.couplingLaw_probability _root_.OAI.LogConcaveSampling.LowerBound.remainingHaar_probability _root_.OAI.LogConcaveSampling.LowerBound.roundRandomLaw_probability _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_invInvariant _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_isHaar _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_probability _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_rightInvariant _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_compactSpace _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_measurableInv _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_measurableMul _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_secondCountable _root_.OAI.LogConcaveSampling.MeanTree.instIsProbabilityMeasureRowTapeRowLaw _root_.OAI.LogConcaveSampling.OracleCompiler.topSeedLaw_probability _root_.OAI.LogConcaveSampling.noiseKernel_markov
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
namespace LogConcaveSampling
open MeasureTheory
open scoped Classical BigOperators NNReal RealInnerProductSpace

universe u

lemma spatialTensor_relabel {d : ℕ} {S T K J : Type u}
    (F : (S → Fin d) → Point d → ℝ) (hF : ∀c,ContDiff ℝ (⊤ : ℕ∞) (F c))
    (e : S ≃ T) (f : K ≃ J) (l : List K) (m : List J)
    (hlm : (l.map f).Perm m) (y : Point d) (c : J ⊕ T → Fin d) :
    spatialTensor F l y (c ∘ (f.sumCongr e))=
      spatialTensor (fun a => F (a ∘ e)) m y c := by
  unfold spatialTensor
  simp only [Function.comp_def,Equiv.sumCongr_apply,Sum.map_inl,Sum.map_inr]
  have hh := congrFun (JetCalculus.jet_perm (hF (fun s => c (Sum.inr (e s))))
    (fun j => EuclideanSpace.basisFun (Fin d) ℝ (c (Sum.inl j))) hlm) y
  rw [JetCalculus.jet_map] at hh
  exact hh

lemma spatialTensor_polySmooth {d : ℕ} {S K : Type u}
    (F : (S → Fin d) → Point d → ℝ) (hF : ∀c,PolySmooth (F c))
    (l : List K) (c : K ⊕ S → Fin d) : PolySmooth (fun y => spatialTensor F l y c) :=
  (hF _).jet _ l

lemma spatialTensor_allSplit_relabel {d : ℕ} {S T K J : Type u}
    [Fintype S] [Fintype T] [Fintype K] [Fintype J]
    (F : (S → Fin d) → Point d → ℝ) (hF : ∀c,ContDiff ℝ (⊤ : ℕ∞) (F c))
    (e : S ≃ T) (f : K ≃ J) (l : List K) (m : List J)
    (hlm : (l.map f).Perm m) (y : Point d) (B : ℝ)
    (hB : TensorEnergy.AllSplitBound (spatialTensor F l y) B) :
    TensorEnergy.AllSplitBound (spatialTensor (fun a => F (a ∘ e)) m y) B := by
  have hh := hB.reindex (f.sumCongr e)
  simpa only [spatialTensor_relabel F hF e f l m hlm y] using hh

end LogConcaveSampling

end

end

end

end OAI
end

section
-- module Solutions.OAIQ048_LC.LogConcave_Sampling_ScoreSlots
attribute [-instance] _root_.OAI.LogConcaveSampling.LowerBound.couplingLaw_probability _root_.OAI.LogConcaveSampling.LowerBound.remainingHaar_probability _root_.OAI.LogConcaveSampling.LowerBound.roundRandomLaw_probability _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_invInvariant _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_isHaar _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_probability _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_rightInvariant _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_compactSpace _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_measurableInv _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_measurableMul _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_secondCountable _root_.OAI.LogConcaveSampling.MeanTree.instIsProbabilityMeasureRowTapeRowLaw _root_.OAI.LogConcaveSampling.OracleCompiler.topSeedLaw_probability _root_.OAI.LogConcaveSampling.noiseKernel_markov
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section

noncomputable section
namespace LogConcaveSampling
open MeasureTheory
open scoped Classical BigOperators NNReal

lemma scoreField_polySmooth {d : ℕ} {H : Point d → ℝ} (hH : PolySmooth H)
    (c : Empty ⊕ Unit → Fin d) : PolySmooth (scoreField H c) := hH.directional _

end LogConcaveSampling

end

end

end

end OAI
end

section
-- module Solutions.OAIQ048_LC.LogConcave_JetEstimates_Slice
attribute [-instance] _root_.OAI.LogConcaveSampling.LowerBound.couplingLaw_probability _root_.OAI.LogConcaveSampling.LowerBound.remainingHaar_probability _root_.OAI.LogConcaveSampling.LowerBound.roundRandomLaw_probability _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_invInvariant _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_isHaar _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_probability _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_rightInvariant _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_compactSpace _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_measurableInv _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_measurableMul _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_secondCountable _root_.OAI.LogConcaveSampling.MeanTree.instIsProbabilityMeasureRowTapeRowLaw _root_.OAI.LogConcaveSampling.OracleCompiler.topSeedLaw_probability _root_.OAI.LogConcaveSampling.noiseKernel_markov
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
namespace LogConcaveSampling
open MeasureTheory TensorExpression
open scoped Classical BigOperators ENNReal NNReal

lemma spatialTensor_const_mul {S : Type} {d j : ℕ}
    (V : (S → Fin d) → Point d → ℝ) (hV : ∀c,ContDiff ℝ (⊤:ℕ∞) (V c))
    (a : ℝ) (y : Point d) :
    spatialTensor (fun c z => a*V c z) (List.finRange j) y=
      fun c => a*spatialTensor V (List.finRange j) y c := by
  funext c
  exact congrFun (JetCalculus.jet_const_mul (hV _) _ _ a) y

end LogConcaveSampling

end

end

section

noncomputable section
namespace LogConcaveSampling
open scoped Classical BigOperators

namespace TensorEnergy
variable {I J S : Type} [Fintype I] [Fintype J] [Fintype S]

lemma Bound.frobeniusSquared_row {A : I → J → ℝ} {C : ℝ} (h : Bound A C) (hC : 0≤C) :
    ∑i,∑j,(A i j)^2≤Fintype.card I*C := by
  have hb (i : I) : ∑j,(A i j)^2≤C := by
    have hh := h.transpose hC (fun k => if k=i then 1 else 0)
    simpa using hh
  exact (Finset.sum_le_sum (fun i _ => hb i)).trans_eq (by simp)

lemma AllSplitBound.frobeniusSquared {d : ℕ} {T : (S → Fin d) → ℝ} {M : ℝ}
    (h : AllSplitBound T M) [Nonempty I] (e : S ≃ I ⊕ Unit) :
    ∑c,(T c)^2≤d*M^2 := by
  let A : (Unit → Fin d) → (I → Fin d) → ℝ :=
    fun o i => T (fun s => Sum.elim i o (e s))
  have hb : Bound A (M^2) := h I Unit e
  have he : (∑c,(T c)^2)=∑o : Unit → Fin d,∑i : I → Fin d,(A o i)^2 := by
    let ec : ((Unit → Fin d) × (I → Fin d)) ≃ (S → Fin d) :=
      ((Equiv.prodComm _ _).trans (Equiv.sumArrowEquivProdArrow I Unit (Fin d)).symm).trans
        (Equiv.arrowCongr e.symm (Equiv.refl (Fin d)))
    have hh := Equiv.sum_comp ec (fun c => (T c)^2)
    rw [Fintype.sum_prod_type] at hh
    exact hh.symm
  rw [he]
  simpa using hb.frobeniusSquared_row (sq_nonneg M)
end TensorEnergy
end LogConcaveSampling

end

end

end

end OAI
end

section
-- module Solutions.OAIQ048_LC.LogConcave_JetEstimates_Extend
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
namespace LogConcaveSampling.TensorEnergy
open Function
open scoped Classical BigOperators

lemma zeroExtend_out {I J : Type*} (e : I ↪ J) (f : I → ℝ) {j : J} (hj : j∉Set.range e) :
    zeroExtend e f j=0 := Function.extend_apply' _ _ _ hj

lemma zeroExtend_sum {I J : Type*} [Fintype I] [Fintype J] (e : I ↪ J) (f : I → ℝ) :
    (∑j,zeroExtend e f j)=∑i,f i :=
  (Fintype.sum_of_injective e e.injective f (zeroExtend e f)
    (fun _ hj => zeroExtend_out e f hj) (fun i => (zeroExtend_apply e f i).symm)).symm

lemma zeroExtend_sq {I J : Type*} (e : I ↪ J) (f : I → ℝ) :
    (fun j => (zeroExtend e f j)^2)=zeroExtend e (fun i => (f i)^2) := by
  funext j
  by_cases hj : j∈Set.range e
  · obtain ⟨i,rfl⟩ := hj; simp
  · rw [zeroExtend_out e f hj,zeroExtend_out e _ hj]; norm_num

lemma zeroExtend_mul {I J : Type*} (e : I ↪ J) (f : I → ℝ) (g : J → ℝ) :
    (fun j => zeroExtend e f j*g j)=zeroExtend e (fun i => f i*g (e i)) := by
  funext j
  by_cases hj : j∈Set.range e
  · obtain ⟨i,rfl⟩ := hj; simp
  · rw [zeroExtend_out e f hj,zeroExtend_out e _ hj]; simp

lemma sum_restrict_le {I J : Type*} [Fintype I] [Fintype J] (e : I ↪ J) (f : J → ℝ)
    (hf : ∀j,0≤f j) : (∑i,f (e i))≤∑j,f j := by
  rw [←Finset.sum_image (f:=f) (g:=(e : I → J)) (by intro i _ j _ h; exact e.injective h)]
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun j _ _ => hf j)

lemma Bound.zeroExtend {I O I' O' : Type*} [Fintype I] [Fintype O] [Fintype I'] [Fintype O']
    {A : O → I → ℝ} {C : ℝ} (hA : Bound A C) (hC : 0≤C)
    (eI : I ↪ I') (eO : O ↪ O') :
    Bound (fun o i => TensorEnergy.zeroExtend eO (fun o => TensorEnergy.zeroExtend eI (A o) i) o) C := by
  intro v
  have he : (fun o => ∑i,TensorEnergy.zeroExtend eO (fun o => TensorEnergy.zeroExtend eI (A o) i) o*v i)=
      TensorEnergy.zeroExtend eO (fun o => ∑i,A o i*v (eI i)) := by
    funext o
    by_cases ho : o∈Set.range eO
    · obtain ⟨o,rfl⟩ := ho
      simp only [zeroExtend_apply]
      rw [zeroExtend_mul,zeroExtend_sum]
    · simp only [zeroExtend_out eO _ ho,zero_mul,Finset.sum_const_zero]
  change (∑o,((fun o => ∑i,TensorEnergy.zeroExtend eO (fun o => TensorEnergy.zeroExtend eI (A o) i) o*v i) o)^2)≤_
  rw [he,zeroExtend_sq,zeroExtend_sum]
  exact (hA (fun i => v (eI i))).trans
    (mul_le_mul_of_nonneg_left (sum_restrict_le eI (fun i => (v i)^2) (fun _ => sq_nonneg _)) hC)

end LogConcaveSampling.TensorEnergy

end

end

section

noncomputable section
namespace LogConcaveSampling.TensorEnergy
open Function
open scoped Classical BigOperators

lemma AllSplitBound.zeroExtend {S : Type} [Fintype S] {d D : ℕ}
    {T : (S → Fin d) → ℝ} {M : ℝ} (hT : AllSplitBound T M) (ι : S → Fin d ↪ Fin D) :
    AllSplitBound (TensorEnergy.zeroExtend (slotEmbedding ι) T) M := by
  intro I O _ _ _ _ _ _ e
  let ei := slotEmbedding (fun i => ι (e.symm (.inl i)))
  let eo := slotEmbedding (fun o => ι (e.symm (.inr o)))
  have he (i : I → Fin d) (o : O → Fin d) :
      (fun s => Sum.elim (ei i) (eo o) (e s))=
      slotEmbedding ι (fun s => Sum.elim i o (e s)) := by
    funext s
    rcases h : e s with a|b <;>
      simp only [h,Sum.elim_inl,Sum.elim_inr,ei,eo,slotEmbedding_apply,e.symm_apply_eq.mpr h.symm]
  have hrow (o : O → Fin D) (i : I → Fin D) :
      TensorEnergy.zeroExtend (slotEmbedding ι) T (fun s => Sum.elim i o (e s))=
      TensorEnergy.zeroExtend eo (fun o => TensorEnergy.zeroExtend ei (fun i => T (fun s => Sum.elim i o (e s))) i) o := by
    by_cases hi : i∈Set.range ei
    · obtain ⟨a,rfl⟩ := hi
      by_cases ho : o∈Set.range eo
      · obtain ⟨b,rfl⟩ := ho
        rw [he,zeroExtend_apply,zeroExtend_apply,zeroExtend_apply]
      · rw [zeroExtend_out eo _ ho,zeroExtend_out]
        rintro ⟨c,hc⟩
        apply ho
        refine ⟨fun b => c (e.symm (.inr b)),?_⟩
        funext b
        have hh := congrFun hc (e.symm (.inr b))
        change ι (e.symm (.inr b)) (c (e.symm (.inr b)))=o b
        simpa only [slotEmbedding_apply,Equiv.apply_symm_apply,Sum.elim_inr] using hh
    · rw [zeroExtend_out]
      · by_cases ho : o∈Set.range eo
        · obtain ⟨b,rfl⟩ := ho
          rw [zeroExtend_apply,zeroExtend_out ei _ hi]
        · rw [zeroExtend_out eo _ ho]
      · rintro ⟨c,hc⟩
        apply hi
        refine ⟨fun a => c (e.symm (.inl a)),?_⟩
        funext a
        have hh := congrFun hc (e.symm (.inl a))
        change ι (e.symm (.inl a)) (c (e.symm (.inl a)))=i a
        simpa only [slotEmbedding_apply,Equiv.apply_symm_apply,Sum.elim_inl] using hh
  have hb := (hT I O e).zeroExtend (sq_nonneg M) ei eo
  convert hb using 1
  all_goals try with_reducible_and_instances rfl
  ext o i
  exact hrow o i
end LogConcaveSampling.TensorEnergy

end

end

end

end OAI
end

section
-- module Solutions.OAIQ048_LC.LogConcave_JetEstimates_Squared
attribute [-instance] _root_.OAI.LogConcaveSampling.LowerBound.couplingLaw_probability _root_.OAI.LogConcaveSampling.LowerBound.remainingHaar_probability _root_.OAI.LogConcaveSampling.LowerBound.roundRandomLaw_probability _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_invInvariant _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_isHaar _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_probability _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_rightInvariant _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_compactSpace _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_measurableInv _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_measurableMul _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_secondCountable _root_.OAI.LogConcaveSampling.MeanTree.instIsProbabilityMeasureRowTapeRowLaw _root_.OAI.LogConcaveSampling.OracleCompiler.topSeedLaw_probability _root_.OAI.LogConcaveSampling.noiseKernel_markov
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section

noncomputable section
namespace LogConcaveSampling
open MeasureTheory
open scoped Classical BigOperators NNReal
open TensorEnergy

lemma PolySmooth.sq {d : ℕ} {f : Point d → ℝ} (hf : PolySmooth f) : PolySmooth (fun y => (f y)^2) := by
  simpa only [pow_two] using hf.mul hf

lemma spatialSquared_polySmooth {d : ℕ} {S : Type} [Fintype S]
    (F : (S → Fin d) → Point d → ℝ) (hF : ∀c,PolySmooth (F c)) (j : ℕ) :
    PolySmooth (spatialSquared F j) :=
  PolySmooth.sum _ (fun c _ => (spatialTensor_polySmooth F hF _ c).sq)

lemma singleContract_polySmooth {d : ℕ} {S T : Type}
    (F : (S ⊕ Unit → Fin d) → Point d → ℝ)
    (G : (T ⊕ Unit → Fin d) → Point d → ℝ)
    (hF : ∀c,PolySmooth (F c)) (hG : ∀c,PolySmooth (G c))
    (a : S ⊕ T → Fin d) :
    PolySmooth (fun y => singleContract (fun c => F c y) (fun c => G c y) a) :=
  PolySmooth.sum _ (fun _z _ => (hF _).mul (hG _))

end LogConcaveSampling

end

end

end

end OAI
end

section
-- module Solutions.OAIQ048_LC.LogConcave_Sampling_CoordinateProjection
attribute [-instance] _root_.OAI.LogConcaveSampling.LowerBound.couplingLaw_probability _root_.OAI.LogConcaveSampling.LowerBound.remainingHaar_probability _root_.OAI.LogConcaveSampling.LowerBound.roundRandomLaw_probability _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_invInvariant _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_isHaar _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_probability _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_rightInvariant _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_compactSpace _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_measurableInv _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_measurableMul _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_secondCountable _root_.OAI.LogConcaveSampling.MeanTree.instIsProbabilityMeasureRowTapeRowLaw _root_.OAI.LogConcaveSampling.OracleCompiler.topSeedLaw_probability _root_.OAI.LogConcaveSampling.noiseKernel_markov
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
namespace LogConcaveSampling
open Function
open scoped Classical BigOperators
open TensorEnergy

lemma coordinateProjection_basis_in {d D : ℕ} (e : Fin d ↪ Fin D) (i : Fin d) :
    coordinateProjection e (EuclideanSpace.basisFun (Fin D) ℝ (e i))=
      EuclideanSpace.basisFun (Fin d) ℝ i := by
  ext j
  simp only [coordinateProjection_apply,EuclideanSpace.basisFun_apply,PiLp.single_apply]
  simp only [e.injective.eq_iff]

lemma coordinateProjection_basis_out {d D : ℕ} (e : Fin d ↪ Fin D) {i : Fin D}
    (hi : i∉Set.range e) : coordinateProjection e (EuclideanSpace.basisFun (Fin D) ℝ i)=0 := by
  ext j
  simp only [coordinateProjection_apply,EuclideanSpace.basisFun_apply,PiLp.single_apply,PiLp.zero_apply]
  exact ite_eq_right (fun h => hi ⟨j,h⟩)

lemma slotEmbedding_mem_range {S : Type*} {d D : ℕ} (e : S → Fin d ↪ Fin D) (c : S → Fin D) :
    c∈Set.range (slotEmbedding e) ↔ ∀s,c s∈Set.range (e s) := by
  constructor
  · rintro ⟨a,rfl⟩ s
    exact ⟨a s,rfl⟩
  · intro h
    choose a ha using h
    exact ⟨a,funext ha⟩

namespace JetCalculus
lemma jet_eq_zero_of_direction {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {S : Type*} (v : S → E) (l : List S) (f : E → ℝ) {s : S} (hs : s∈l) (hv : v s=0) :
    jet v l f=fun _ => 0 := by
  induction l with
  | nil => simp at hs
  | cons i l ih =>
    rcases List.mem_cons.mp hs with rfl|hs
    · simp only [jet,hv,dir_zero]
    · rw [jet,ih hs]
      funext x
      simp [dir]
end JetCalculus

lemma arrayCoordinateLift_smooth {S : Type} {d D : ℕ} (e : Fin d ↪ Fin D)
    (ι : S → Fin d ↪ Fin D) (F : (S → Fin d) → Point d → ℝ)
    (hF : ∀c,ContDiff ℝ (⊤:ℕ∞) (F c)) (c : S → Fin D) :
    ContDiff ℝ (⊤:ℕ∞) (arrayCoordinateLift e ι F c) := by
  by_cases hc : c∈Set.range (slotEmbedding ι)
  · obtain ⟨a,rfl⟩ := hc
    change ContDiff ℝ (⊤:ℕ∞) (fun y => TensorEnergy.zeroExtend (slotEmbedding ι) (fun a => F a (coordinateProjection e y)) (slotEmbedding ι a))
    simp only [zeroExtend_apply]
    exact (hF a).comp (coordinateProjection e).contDiff
  · have he : arrayCoordinateLift e ι F c=fun _ => 0 := by
      funext y; exact zeroExtend_out _ _ hc
    rw [he]; exact contDiff_const

lemma spatialTensor_coordinateLift {S J : Type} [Fintype J] {d D : ℕ}
    (e : Fin d ↪ Fin D) (ι : S → Fin d ↪ Fin D) (F : (S → Fin d) → Point d → ℝ)
    (hF : ∀c,ContDiff ℝ (⊤:ℕ∞) (F c)) (l : List J) (hl : ∀j,j∈l) (y : Point D) :
    spatialTensor (arrayCoordinateLift e ι F) l y=
      TensorEnergy.zeroExtend (slotEmbedding (Sum.elim (fun _ : J => e) ι))
        (spatialTensor F l (coordinateProjection e y)) := by
  funext c
  by_cases hc : c∈Set.range (slotEmbedding (Sum.elim (fun _ : J => e) ι))
  · obtain ⟨a,rfl⟩ := hc
    rw [zeroExtend_apply]
    unfold spatialTensor arrayCoordinateLift
    have hc : (fun s => slotEmbedding (Sum.elim (fun _ : J => e) ι) a (.inr s))=
        slotEmbedding ι (fun s => a (.inr s)) := rfl
    rw [hc]
    simp only [zeroExtend_apply,slotEmbedding_apply,Sum.elim_inl]
    have hh := JetCalculus.jet_comp_affine (hF (fun s => a (.inr s))) (coordinateProjection e) 0
      (fun j => EuclideanSpace.basisFun (Fin D) ℝ (e (a (.inl j)))) l
    simp only [add_zero,coordinateProjection_basis_in] at hh
    exact congrFun hh y
  · rw [zeroExtend_out _ _ hc]
    by_cases hs : (fun s => c (.inr s))∈Set.range (slotEmbedding ι)
    · obtain ⟨a,ha⟩ := hs
      have hj : ∃j : J,c (.inl j)∉Set.range e := by
        by_contra! hj
        apply hc
        rw [slotEmbedding_mem_range]
        rintro (j|s)
        · exact hj j
        · exact ⟨a s,congrFun ha s⟩
      obtain ⟨j,hj⟩ := hj
      unfold spatialTensor arrayCoordinateLift
      rw [←ha]
      simp only [zeroExtend_apply]
      have hh := JetCalculus.jet_comp_affine (hF a) (coordinateProjection e) 0
        (fun j => EuclideanSpace.basisFun (Fin D) ℝ (c (.inl j))) l
      simp only [add_zero] at hh
      rw [hh,JetCalculus.jet_eq_zero_of_direction _ l _ (hl j) (coordinateProjection_basis_out e hj)]
    · have he : arrayCoordinateLift e ι F (fun s => c (.inr s))=fun _ => 0 := by
        funext z; exact zeroExtend_out _ _ hs
      change JetCalculus.jet _ l (arrayCoordinateLift e ι F _) y=0
      rw [he,JetCalculus.jet_const]
      split_ifs <;> rfl

lemma AllSplitBound.coordinateLift {S : Type} [Fintype S] {d D j : ℕ}
    (e : Fin d ↪ Fin D) (ι : S → Fin d ↪ Fin D) (F : (S → Fin d) → Point d → ℝ)
    (hF : ∀c,ContDiff ℝ (⊤:ℕ∞) (F c)) {M : ℝ}
    (hb : ∀x,AllSplitBound (spatialTensor F (List.finRange j) x) M) (y : Point D) :
    AllSplitBound (spatialTensor (arrayCoordinateLift e ι F) (List.finRange j) y) M := by
  rw [spatialTensor_coordinateLift e ι F hF _ (fun k => List.mem_finRange k) y]
  exact (hb _).zeroExtend _
end LogConcaveSampling

end

end

section

noncomputable section
namespace LogConcaveSampling
open MeasureTheory
open scoped Classical BigOperators
open TensorEnergy

lemma squared_zeroExtend {S : Type} [Fintype S] {d D : ℕ}
    (e : (S → Fin d) ↪ (S → Fin D)) (F : (S → Fin d) → ℝ) :
    squared (zeroExtend e F)=squared F := by
  exact (congrArg (fun f : (S → Fin D) → ℝ => ∑c,f c) (zeroExtend_sq e F)).trans
    (zeroExtend_sum e (fun a => (F a)^2))
end LogConcaveSampling

end

end

section

noncomputable section
namespace LogConcaveSampling
open MeasureTheory
open scoped Classical BigOperators RealInnerProductSpace

lemma productPointEquiv_volume (d e : ℕ) :
    MeasurePreserving (productPointEquiv d e) := by
  have h₁ := (LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ
    (finSumFinEquiv.symm : Fin (d+e) ≃ Fin d ⊕ Fin e)).measurePreserving
  have h₂ := (PiLp.sumPiLpEquivProdLpPiLp 2 (fun _ : Fin d ⊕ Fin e => ℝ)).measurePreserving
  have h₃ := WithLp.volume_preserving_ofLp (Point d) (Point e)
  exact h₃.comp (h₂.comp h₁)

lemma productPointEquiv_norm_sq {d e : ℕ} (y : Point (d+e)) :
    ‖y‖^2=‖(productPointEquiv d e y).1‖^2+‖(productPointEquiv d e y).2‖^2 := by
  let T := LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ
    (finSumFinEquiv.symm : Fin (d+e) ≃ Fin d ⊕ Fin e)
  have hh := PiLp.norm_sq_eq_of_L2 (fun _ : Fin d ⊕ Fin e => ℝ) (T y)
  simp only [Real.norm_eq_abs,sq_abs,Fintype.sum_sum_type] at hh
  rw [T.norm_map] at hh
  simpa [productPointEquiv,T,EuclideanSpace.finAddEquivProd,EuclideanSpace.sumEquivProd,EuclideanSpace.real_norm_sq_eq] using hh

lemma productPotential_density {d e : ℕ} (H : Point d → ℝ) (G : Point e → ℝ)
    (y : Point (d+e)) : gibbsDensity (productPotential H G) y=
      gibbsDensity H (productPointEquiv d e y).1*gibbsDensity G (productPointEquiv d e y).2 := by
  simp only [gibbsDensity,productPotential,neg_add,Real.exp_add,ENNReal.ofReal_mul (Real.exp_nonneg _)]
end LogConcaveSampling

end

end

end

end OAI
end

section
-- module Solutions.OAIQ048_LC.LogConcave_Analysis_ProductPotentialMeasurable
attribute [-instance] _root_.OAI.LogConcaveSampling.LowerBound.couplingLaw_probability _root_.OAI.LogConcaveSampling.LowerBound.remainingHaar_probability _root_.OAI.LogConcaveSampling.LowerBound.roundRandomLaw_probability _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_invInvariant _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_isHaar _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_probability _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_rightInvariant _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_compactSpace _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_measurableInv _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_measurableMul _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_secondCountable _root_.OAI.LogConcaveSampling.MeanTree.instIsProbabilityMeasureRowTapeRowLaw _root_.OAI.LogConcaveSampling.OracleCompiler.topSeedLaw_probability _root_.OAI.LogConcaveSampling.noiseKernel_markov
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
namespace LogConcaveSampling
open MeasureTheory Set ProbabilityTheory
open scoped ENNReal NNReal

lemma productPotential_measurable {d e : ℕ} {H : Point d → ℝ} {G : Point e → ℝ}
    (hH : Measurable H) (hG : Measurable G) : Measurable (productPotential H G) :=
  (hH.comp ((productPointEquiv d e).continuous.measurable.fst)).add
    (hG.comp ((productPointEquiv d e).continuous.measurable.snd))

lemma productPotential_unnormalized {d e : ℕ} {H : Point d → ℝ} {G : Point e → ℝ}
    (hH : Measurable H) (hG : Measurable G) :
    (volume.withDensity (gibbsDensity (productPotential H G))).map (productPointEquiv d e)=
      (volume.withDensity (gibbsDensity H)).prod (volume.withDensity (gibbsDensity G)) := by
  let E := (productPointEquiv d e).toHomeomorph.toMeasurableEquiv
  have hd : Measurable (gibbsDensity (productPotential H G)) :=
    (Real.measurable_exp.comp (productPotential_measurable hH hG).neg).ennreal_ofReal
  have hHd : Measurable (gibbsDensity H) := (Real.measurable_exp.comp hH.neg).ennreal_ofReal
  have hGd : Measurable (gibbsDensity G) := (Real.measurable_exp.comp hG.neg).ennreal_ofReal
  rw [show (productPointEquiv d e : Point (d+e) → Point d × Point e)=E from rfl,
    map_withDensity_of_measurePreserving E (productPointEquiv_volume d e) hd,
    prod_withDensity hHd hGd]
  congr 1
  funext p
  rw [productPotential_density]
  change gibbsDensity H (E (E.symm p)).1*gibbsDensity G (E (E.symm p)).2=_
  rw [E.apply_symm_apply]

lemma productPotential_partition {d e : ℕ} {H : Point d → ℝ} {G : Point e → ℝ}
    (hH : Measurable H) (hG : Measurable G) :
    partition (productPotential H G)=partition H*partition G := by
  have he := congrArg (fun μ : Measure (Point d × Point e) => μ univ)
    (productPotential_unnormalized hH hG)
  rw [Measure.map_apply (productPointEquiv d e).continuous.measurable MeasurableSet.univ,
    preimage_univ] at he
  have hp : ((volume.withDensity (gibbsDensity H)).prod (volume.withDensity (gibbsDensity G))) univ=
      (volume.withDensity (gibbsDensity H)) univ*(volume.withDensity (gibbsDensity G)) univ := by
    rw [← univ_prod_univ,Measure.prod_prod]
  rw [hp] at he
  simpa only [withDensity_apply _ MeasurableSet.univ,Measure.restrict_univ,partition] using he

theorem productPotential_gibbs {d e : ℕ} {H : Point d → ℝ} {G : Point e → ℝ}
    (hH : Continuous H) (hG : Continuous G) :
    (gibbs (productPotential H G)).map (productPointEquiv d e)=(gibbs H).prod (gibbs G) := by
  unfold gibbs
  rw [Measure.map_smul,
    productPotential_unnormalized hH.measurable hG.measurable,productPotential_partition hH.measurable hG.measurable,
    ENNReal.mul_inv (Or.inl (partition_pos_of_continuous hH).ne') (Or.inr (partition_pos_of_continuous hG).ne'),Measure.prod_smul_left,Measure.prod_smul_right,smul_smul]

lemma gaussianPotential_gibbs (d : ℕ) :
    gibbs (fun y : Point d => ‖y‖^2/2)=stdGaussian (Point d) := by
  have he := congrArg (fun μ : Measure (Point d) => μ univ) (EulerDensity.standard_density d)
  have hmul : EulerDensity.gaussianCoefficient d*partition (fun y : Point d => ‖y‖^2/2)=1 := by
    simpa only [measure_univ,Measure.smul_apply,smul_eq_mul,
      withDensity_apply _ MeasurableSet.univ,Measure.restrict_univ,partition,gibbsDensity,neg_div] using he.symm
  have hi : (partition (fun y : Point d => ‖y‖^2/2))⁻¹=EulerDensity.gaussianCoefficient d := by
    exact (ENNReal.eq_inv_of_mul_eq_one_left hmul).symm
  rw [EulerDensity.standard_density,gibbs,hi]
  congr 2
  funext y
  simp only [gibbsDensity,neg_div]
end LogConcaveSampling

end

end

end

end OAI
end

section
-- module Solutions.OAIQ048_LC.LogConcave_JetEstimates_MatrixArray
attribute [-instance] _root_.OAI.LogConcaveSampling.LowerBound.couplingLaw_probability _root_.OAI.LogConcaveSampling.LowerBound.remainingHaar_probability _root_.OAI.LogConcaveSampling.LowerBound.roundRandomLaw_probability _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_invInvariant _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_isHaar _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_probability _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_rightInvariant _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_compactSpace _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_measurableInv _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_measurableMul _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_secondCountable _root_.OAI.LogConcaveSampling.MeanTree.instIsProbabilityMeasureRowTapeRowLaw _root_.OAI.LogConcaveSampling.OracleCompiler.topSeedLaw_probability _root_.OAI.LogConcaveSampling.noiseKernel_markov
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section

noncomputable section
namespace LogConcaveSampling.TensorEnergy
open scoped Classical BigOperators RealInnerProductSpace

lemma matrixArray_apply {d : ℕ} (A : Point d →L[ℝ] Point d) (c : Unit ⊕ Unit → Fin d) :
    matrixArray d A c=inner ℝ (EuclideanSpace.basisFun (Fin d) ℝ (c (Sum.inl ())))
      (A (EuclideanSpace.basisFun (Fin d) ℝ (c (Sum.inr ())))) := rfl

end LogConcaveSampling.TensorEnergy

end

end

end

end OAI
end

section
-- module Solutions.OAIQ048_LC.LogConcave_Sampling_TransportMajorant
attribute [-instance] _root_.OAI.LogConcaveSampling.LowerBound.couplingLaw_probability _root_.OAI.LogConcaveSampling.LowerBound.remainingHaar_probability _root_.OAI.LogConcaveSampling.LowerBound.roundRandomLaw_probability _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_invInvariant _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_isHaar _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_probability _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_rightInvariant _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_compactSpace _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_measurableInv _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_measurableMul _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_secondCountable _root_.OAI.LogConcaveSampling.MeanTree.instIsProbabilityMeasureRowTapeRowLaw _root_.OAI.LogConcaveSampling.OracleCompiler.topSeedLaw_probability _root_.OAI.LogConcaveSampling.noiseKernel_markov
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
namespace LogConcaveSampling
open Set Function
open scoped NNReal BigOperators
open TensorEnergy

lemma probabilityTransport_smooth {d : ℕ} {F : Point d → ℝ} {lam : ℝ≥0}
    (hF : Primitive F lam) (x : Point d) {r T : ℝ} (hr : 0 ≤ r)
    (hl : (lam:ℝ)*r^2≤1/2) (hT0 : 0≤T) (hT1 : T<1) (s t : Icc (0:ℝ) T) :
    ContDiff ℝ (⊤:ℕ∞) (probabilityTransport hF x hr hl hT0 hT1 s t) := by
  have he : probabilityTransport hF x hr hl hT0 hT1 s t=
      fun z => spatialTransport hF x hr hl hT0 hT1 s (t,z) :=
    funext (fun z => (spatialTransport_eq hF x hr hl hT0 hT1 s t z).symm)
  rw [he]
  exact (spatialTransport_smooth hF x hr hl hT0 hT1 s).comp (contDiff_const.prodMk contDiff_id)

end LogConcaveSampling

end

end

end

end OAI
end

section
-- module Solutions.OAIQ048_LC.LogConcave_JetEstimates_CompLinear
attribute [-instance] _root_.OAI.LogConcaveSampling.LowerBound.couplingLaw_probability _root_.OAI.LogConcaveSampling.LowerBound.remainingHaar_probability _root_.OAI.LogConcaveSampling.LowerBound.roundRandomLaw_probability _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_invInvariant _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_isHaar _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_probability _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_rightInvariant _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_compactSpace _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_measurableInv _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_measurableMul _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_secondCountable _root_.OAI.LogConcaveSampling.MeanTree.instIsProbabilityMeasureRowTapeRowLaw _root_.OAI.LogConcaveSampling.OracleCompiler.topSeedLaw_probability _root_.OAI.LogConcaveSampling.noiseKernel_markov
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
namespace LogConcaveSampling
open scoped Classical BigOperators

lemma Appell.HasGrowth.comp_linear {E F Z : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup Z]
    {f : F → Z} (hf : Appell.HasGrowth f) (L : E →L[ℝ] F) :
    Appell.HasGrowth (fun x => f (L x)) := by
  obtain ⟨C,hC,n,hf⟩ := hf
  refine ⟨C*(1+‖L‖^n),by positivity,n,fun x => (hf (L x)).trans ?_⟩
  have hp : ‖L x‖^n≤‖L‖^n*‖x‖^n := by
    simpa only [mul_pow] using pow_le_pow_left₀ (norm_nonneg _) (L.le_opNorm x) n
  have hLn := pow_nonneg (norm_nonneg L) n
  have hxn := pow_nonneg (norm_nonneg x) n
  nlinarith [mul_le_mul_of_nonneg_left hp hC,mul_nonneg hC hLn,mul_nonneg hC hxn]

lemma PolySmooth.comp_linear {d e : ℕ} {f : Point e → ℝ}
    (hf : PolySmooth f) (L : Point d →L[ℝ] Point e) : PolySmooth (fun x => f (L x)) := by
  refine ⟨hf.smooth.comp L.contDiff,fun l => ?_⟩
  have he := JetCalculus.jet_comp_affine hf.smooth L 0 id l
  simp only [add_zero,id_eq] at he
  rw [he]
  have hh := hf.growth (l.map L)
  rw [JetCalculus.jet_map] at hh
  exact Appell.HasGrowth.comp_linear hh L

lemma productPotential_polySmooth {d e : ℕ} {H : Point d → ℝ} {G : Point e → ℝ}
    (hH : PolySmooth H) (hG : PolySmooth G) : PolySmooth (productPotential H G) :=
  (hH.comp_linear ((ContinuousLinearMap.fst ℝ (Point d) (Point e)).comp
    (productPointEquiv d e).toContinuousLinearMap)).add
    (hG.comp_linear ((ContinuousLinearMap.snd ℝ (Point d) (Point e)).comp
      (productPointEquiv d e).toContinuousLinearMap))

lemma gaussianPotential_polySmooth (d : ℕ) : PolySmooth (fun y : Point d => ‖y‖^2/2) := by
  have h (i : Fin d) : PolySmooth (fun y : Point d => y i) := PolySmooth.linear (PiLp.proj 2 _ i)
  have hs := PolySmooth.sum Finset.univ (fun i _ => (h i).mul (h i))
  have hh := (PolySmooth.const (1/2)).mul hs
  have he : (fun y : Point d => ‖y‖^2/2)=(fun y : Point d => (1/2 : ℝ)*(∑i,y i*y i)) := by
    funext y
    rw [EuclideanSpace.real_norm_sq_eq]
    simp only [pow_two]
    ring
  rw [he]
  exact hh

lemma productPotential_lowerTail {d e : ℕ} {H : Point d → ℝ} {G : Point e → ℝ}
    (hH : HasGaussianLowerTail H) (hG : HasGaussianLowerTail G) :
    HasGaussianLowerTail (productPotential H G) := by
  obtain ⟨a,ha,A,hA⟩ := hH
  obtain ⟨b,hb,B,hB⟩ := hG
  refine ⟨min a b,lt_min ha hb,A+B,fun y => ?_⟩
  rw [productPointEquiv_norm_sq]
  have h₁ := mul_le_mul_of_nonneg_right (min_le_left a b) (sq_nonneg ‖(productPointEquiv d e y).1‖)
  have h₂ := mul_le_mul_of_nonneg_right (min_le_right a b) (sq_nonneg ‖(productPointEquiv d e y).2‖)
  have h₃ := hA (productPointEquiv d e y).1
  have h₄ := hB (productPointEquiv d e y).2
  dsimp [productPotential]
  nlinarith

lemma gaussianPotential_lowerTail (d : ℕ) : HasGaussianLowerTail (fun y : Point d => ‖y‖^2/2) := by
  exact ⟨1/2,by norm_num,0,fun _ => by linarith⟩
end LogConcaveSampling

end

end

end

end OAI
end

section
-- module Solutions.OAIQ048_LC.LogConcave_Sampling_FinsetSumSum
attribute [-instance] _root_.OAI.LogConcaveSampling.LowerBound.couplingLaw_probability _root_.OAI.LogConcaveSampling.LowerBound.remainingHaar_probability _root_.OAI.LogConcaveSampling.LowerBound.roundRandomLaw_probability _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_invInvariant _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_isHaar _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_probability _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_rightInvariant _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_compactSpace _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_measurableInv _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_measurableMul _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_secondCountable _root_.OAI.LogConcaveSampling.MeanTree.instIsProbabilityMeasureRowTapeRowLaw _root_.OAI.LogConcaveSampling.OracleCompiler.topSeedLaw_probability _root_.OAI.LogConcaveSampling.noiseKernel_markov
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
namespace LogConcaveSampling
open MeasureTheory
open scoped Classical BigOperators NNReal
open TensorEnergy

lemma tensorAdjoint_polySmooth {S : Type} {d : ℕ} {H : Point d → ℝ}
    (hH : PolySmooth H) (F : (S ⊕ Unit → Fin d) → Point d → ℝ) (hF : ∀c,PolySmooth (F c))
    (a : S → Fin d) : PolySmooth
      (tensorAdjoint H (EuclideanSpace.basisFun (Fin d) ℝ) (fun z => F (Sum.elim a (fun _ => z)))) :=
  hH.tensorAdjoint (fun _ => hF _) _

end LogConcaveSampling

end

end

end

end OAI
end

section
-- module Solutions.OAIQ048_LC.LogConcave_Sampling_TensorGrad
attribute [-instance] _root_.OAI.LogConcaveSampling.LowerBound.couplingLaw_probability _root_.OAI.LogConcaveSampling.LowerBound.remainingHaar_probability _root_.OAI.LogConcaveSampling.LowerBound.roundRandomLaw_probability _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_invInvariant _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_isHaar _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_probability _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_rightInvariant _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_compactSpace _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_measurableInv _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_measurableMul _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_secondCountable _root_.OAI.LogConcaveSampling.MeanTree.instIsProbabilityMeasureRowTapeRowLaw _root_.OAI.LogConcaveSampling.OracleCompiler.topSeedLaw_probability _root_.OAI.LogConcaveSampling.noiseKernel_markov
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
namespace LogConcaveSampling
open MeasureTheory
open scoped Classical BigOperators
open TensorEnergy

lemma spatialSquared_coordinateLift {S : Type} [Fintype S] {d D : ℕ}
    (e : Fin d ↪ Fin D) (ι : S → Fin d ↪ Fin D) (F : (S → Fin d) → Point d → ℝ)
    (hF : ∀c,ContDiff ℝ (⊤:ℕ∞) (F c)) (j : ℕ) (y : Point D) :
    spatialSquared (arrayCoordinateLift e ι F) j y=
      spatialSquared F j (coordinateProjection e y) := by
  unfold spatialSquared
  rw [spatialTensor_coordinateLift e ι F hF _ (fun k => List.mem_finRange k) y,squared_zeroExtend]

lemma arrayCoordinateLift_polySmooth {S : Type} {d D : ℕ}
    (e : Fin d ↪ Fin D) (ι : S → Fin d ↪ Fin D) (F : (S → Fin d) → Point d → ℝ)
    (hF : ∀c,PolySmooth (F c)) (c : S → Fin D) :
    PolySmooth (arrayCoordinateLift e ι F c) := by
  by_cases hc : c∈Set.range (slotEmbedding ι)
  · obtain ⟨a,rfl⟩ := hc
    change PolySmooth (fun y => zeroExtend (slotEmbedding ι) (fun a => F a (coordinateProjection e y)) (slotEmbedding ι a))
    simp only [zeroExtend_apply]
    exact (hF a).comp_linear _
  · have he : arrayCoordinateLift e ι F c=fun _ => 0 := by
      funext y; exact zeroExtend_out _ _ hc
    rw [he]
    exact PolySmooth.const 0

end LogConcaveSampling

end

end

section

noncomputable section
namespace LogConcaveSampling
open MeasureTheory
open scoped Classical BigOperators
open TensorEnergy

lemma tensorGrad_polySmooth {S : Type} {d : ℕ} (F : (S → Fin d) → Point d → ℝ)
    (hF : ∀c,PolySmooth (F c)) (c : S ⊕ Unit → Fin d) : PolySmooth (tensorGrad F c) :=
  (hF _).directional _

end LogConcaveSampling

end

end

section

noncomputable section
namespace LogConcaveSampling
open MeasureTheory
open scoped Classical BigOperators NNReal
open TensorEnergy

lemma lieInside_polySmooth {S : Type} {d : ℕ} (A : (Unit ⊕ Unit → Fin d) → Point d → ℝ)
    (F : (S → Fin d) → Point d → ℝ) (hA : ∀c,PolySmooth (A c)) (hF : ∀c,PolySmooth (F c))
    (c : S ⊕ Unit → Fin d) : PolySmooth (lieInside A F c) :=
  singleContract_polySmooth A (tensorGrad F) hA (tensorGrad_polySmooth F hF) _

lemma tensorLie_polySmooth {S : Type} {d : ℕ} {H : Point d → ℝ} (hH : PolySmooth H)
    (A : (Unit ⊕ Unit → Fin d) → Point d → ℝ) (F : (S → Fin d) → Point d → ℝ)
    (hA : ∀c,PolySmooth (A c)) (hF : ∀c,PolySmooth (F c)) (c : S → Fin d) : PolySmooth (tensorLie H A F c) :=
  tensorAdjoint_polySmooth hH (lieInside A F) (lieInside_polySmooth A F hA hF) c

lemma productEnergyBudget_nonneg {C E : ℕ → ℝ} (hE : ∀j,0 ≤ E j) (j : ℕ) :
    0 ≤ productEnergyBudget C E j :=
  mul_nonneg (by positivity) (Finset.sum_nonneg (fun s _ => mul_nonneg (sq_nonneg _) (hE _)))

end LogConcaveSampling

end

end

end

end OAI
end

section
-- module Solutions.OAIQ048_LC.LogConcave_Complexity_ProductEnergyBudgetScaled
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
namespace LogConcaveSampling
open scoped Classical BigOperators

lemma adjointEnergyBudget_nonneg {K : ℝ} (hK : 0 ≤ K) (C : ℕ → ℝ)
    {B : ℕ → ℝ} (hB : ∀j,0 ≤ B j) (j : ℕ) : 0 ≤ adjointEnergyBudget K C B j := by
  unfold adjointEnergyBudget
  apply mul_nonneg (by norm_num)
  apply add_nonneg (add_nonneg (hB _) (mul_nonneg hK (hB _)))
  exact mul_nonneg (by positivity) (Finset.sum_nonneg (fun s _ => mul_nonneg (sq_nonneg _) (hB _)))

end LogConcaveSampling

end

end

end

end OAI
end

section
-- module Solutions.OAIQ048_LC.LogConcave_Sampling_IterTensorLie
attribute [-instance] _root_.OAI.LogConcaveSampling.LowerBound.couplingLaw_probability _root_.OAI.LogConcaveSampling.LowerBound.remainingHaar_probability _root_.OAI.LogConcaveSampling.LowerBound.roundRandomLaw_probability _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_invInvariant _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_isHaar _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_probability _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_rightInvariant _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_compactSpace _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_measurableInv _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_measurableMul _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_secondCountable _root_.OAI.LogConcaveSampling.MeanTree.instIsProbabilityMeasureRowTapeRowLaw _root_.OAI.LogConcaveSampling.OracleCompiler.topSeedLaw_probability _root_.OAI.LogConcaveSampling.noiseKernel_markov
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
namespace LogConcaveSampling
open MeasureTheory
open scoped Classical NNReal BigOperators
open TensorEnergy

lemma iterEnergyBudget_nonneg {K : ℝ} (hK : 0 ≤ K) (C D : ℕ → ℝ)
    {B : ℕ → ℝ} (hB : ∀k,0 ≤ B k) (n j : ℕ) : 0 ≤ iterEnergyBudget K C D B n j := by
  induction n generalizing j with
  | zero => exact hB j
  | succ n ih => exact adjointEnergyBudget_nonneg hK D (fun k => productEnergyBudget_nonneg ih k) j

lemma iterTensorLie_polySmooth {S : Type} {d : ℕ} {H : Point d → ℝ} (hH : PolySmooth H)
    (A : (Unit ⊕ Unit → Fin d) → Point d → ℝ) (F : (S → Fin d) → Point d → ℝ)
    (hA : ∀c,PolySmooth (A c)) (hF : ∀c,PolySmooth (F c)) (n : ℕ) (c : S → Fin d) :
    PolySmooth (iterTensorLie H A F n c) := by
  induction n generalizing c with
  | zero => exact hF c
  | succ n ih => exact tensorLie_polySmooth hH A _ hA ih c

end LogConcaveSampling

end

end

section

noncomputable section
namespace LogConcaveSampling
open MeasureTheory
open scoped Classical BigOperators
open TensorEnergy

lemma adjointCoordinate_sum {d : ℕ} {ι : Type*} [Fintype ι] (H : Point d → ℝ)
    (v : Point d) (f : ι → Point d → ℝ) (hf : ∀i,Differentiable ℝ (f i)) :
    adjointCoordinate H v (fun y => ∑i,f i y)=fun y => ∑i,adjointCoordinate H v (f i) y := by
  unfold adjointCoordinate
  rw [directional_sum _ (fun i _ => hf i)]
  funext y
  simp only [Finset.sum_add_distrib,Finset.sum_neg_distrib,Finset.mul_sum]

lemma adjointCoordinate_mul {d : ℕ} (H : Point d → ℝ) (v : Point d)
    {f g : Point d → ℝ} (hf : Differentiable ℝ f) (hg : Differentiable ℝ g) :
    adjointCoordinate H v (fun y => f y*g y)=fun y =>
      adjointCoordinate H v f y*g y-f y*directional v g y := by
  unfold adjointCoordinate
  rw [directional_mul hf hg]
  funext y
  ring

lemma tensorLie_eq_directional {S : Type} {d : ℕ} (H : Point d → ℝ)
    (A : (Unit ⊕ Unit → Fin d) → Point d → ℝ) (F : (S → Fin d) → Point d → ℝ)
    (hA : ∀c,ContDiff ℝ (⊤:ℕ∞) (A c)) (hF : ∀c,ContDiff ℝ (⊤:ℕ∞) (F c))
    (hsk : ∀i z y,A (Sum.elim (fun _ => i) (fun _ => z)) y=
      -A (Sum.elim (fun _ => z) (fun _ => i)) y) (c : S → Fin d) (y : Point d) :
    tensorLie H A F c y=directional (skewLieField H A y) (F c) y := by
  let b := EuclideanSpace.basisFun (Fin d) ℝ
  have hess : (∑i : Fin d,∑z : Fin d,A (Sum.elim (fun _ => i) (fun _ => z)) y*
      directional (b i) (directional (b z) (F c)) y)=0 := by
    have he : (∑i : Fin d,∑z : Fin d,A (Sum.elim (fun _ => i) (fun _ => z)) y*
        directional (b i) (directional (b z) (F c)) y)=
        -(∑i : Fin d,∑z : Fin d,A (Sum.elim (fun _ => i) (fun _ => z)) y*
        directional (b i) (directional (b z) (F c)) y) := by
      conv_rhs => rw [Finset.sum_comm]
      rw [←Finset.sum_neg_distrib]
      apply Finset.sum_congr rfl
      intro i _
      rw [←Finset.sum_neg_distrib]
      apply Finset.sum_congr rfl
      intro z _
      rw [hsk i z y,directional_commute (hF c) (b i) (b z)]
      ring
    linarith
  have hin (i : Fin d) : lieInside A F (Sum.elim c (fun _ => i))=
      fun y => ∑z : Fin d,A (Sum.elim (fun _ => i) (fun _ => z)) y*directional (b z) (F c) y := rfl
  have hadj (i : Fin d) : adjointCoordinate H (b i)
      (lieInside A F (Sum.elim c (fun _ => i))) y=
      ∑z : Fin d,(adjointCoordinate H (b i) (A (Sum.elim (fun _ => i) (fun _ => z))) y*
        directional (b z) (F c) y-A (Sum.elim (fun _ => i) (fun _ => z)) y*
        directional (b i) (directional (b z) (F c)) y) := by
    rw [hin i,adjointCoordinate_sum H (b i) (fun z y => A (Sum.elim (fun _ => i) (fun _ => z)) y*directional (b z) (F c) y) (fun z =>
      ((hA (Sum.elim (fun _ => i) (fun _ => z))).differentiable (by simp)).mul ((directional_smooth (hF c) (b z)).differentiable (by simp)))]
    apply Finset.sum_congr rfl
    intro z _
    exact congrFun (adjointCoordinate_mul H (b i) ((hA _).differentiable (by simp))
      ((directional_smooth (hF c) (b z)).differentiable (by simp))) y
  unfold tensorLie tensorAdjoint
  change (∑i : Fin d,adjointCoordinate H (b i) (lieInside A F (Sum.elim c (fun _ => i))) y)=_
  simp_rw [hadj]
  simp only [Finset.sum_sub_distrib]
  rw [hess,sub_zero,Finset.sum_comm]
  simp only [directional,skewLieField,map_sum,map_smul,smul_eq_mul,Finset.sum_mul]
  rfl

end LogConcaveSampling

end

end

section

noncomputable section
namespace LogConcaveSampling
open MeasureTheory Set
open scoped Classical BigOperators NNReal
open TensorEnergy

lemma spatialEnergy_from_split {d j : ℕ} {H : Point d → ℝ}
    (hH : Continuous H) (ht : HasGaussianLowerTail H) [IsProbabilityMeasure (gibbs H)]
    (F : (Unit → Fin d) → Point d → ℝ) (hF : ∀c,PolySmooth (F c))
    {M : ℝ} (hj : 0<j) (hb : ∀y,AllSplitBound (spatialTensor F (List.finRange j) y) M) :
    spatialEnergy F j (gibbs H) ≤ d*M^2 := by
  let : Nonempty (Fin j) := ⟨⟨0,hj⟩⟩
  have hh (y : Point d) : spatialSquared F j y≤d*M^2 :=
    (hb y).frobeniusSquared (Equiv.refl (Fin j ⊕ Unit))
  have hi := (spatialSquared_polySmooth F hF j).integrable hH ht
  exact (integral_mono hi (integrable_const _) hh).trans_eq (by simp)

end LogConcaveSampling

end

end

end

end OAI
end

section
-- module Solutions.OAIQ048_LC.LogConcave_Sampling_TensorVector
attribute [-instance] _root_.OAI.LogConcaveSampling.LowerBound.couplingLaw_probability _root_.OAI.LogConcaveSampling.LowerBound.remainingHaar_probability _root_.OAI.LogConcaveSampling.LowerBound.roundRandomLaw_probability _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_invInvariant _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_isHaar _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_probability _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_rightInvariant _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_compactSpace _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_measurableInv _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_measurableMul _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_secondCountable _root_.OAI.LogConcaveSampling.MeanTree.instIsProbabilityMeasureRowTapeRowLaw _root_.OAI.LogConcaveSampling.OracleCompiler.topSeedLaw_probability _root_.OAI.LogConcaveSampling.noiseKernel_markov
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
namespace LogConcaveSampling
open MeasureTheory
open scoped Classical BigOperators
open TensorEnergy

lemma lie_chain {S : Type} {d : ℕ} {H : Point d → ℝ}
    (hH : PolySmooth H) (A : (Unit ⊕ Unit → Fin d) → Point d → ℝ)
    (F : (S → Fin d) → Point d → ℝ) (hA : ∀c,PolySmooth (A c)) (hF : ∀c,PolySmooth (F c))
    (hsk : ∀i z y,A (Sum.elim (fun _ => i) (fun _ => z)) y=
      -A (Sum.elim (fun _ => z) (fun _ => i)) y)
    {s : Set ℝ} (γ : ℝ → Point d)
    (hγ : ∀t∈s,HasDerivWithinAt γ (skewLieField H A (γ t)) s t)
    (n : ℕ) (c : S → Fin d) {t : ℝ} (ht : t∈s) :
    HasDerivWithinAt (fun u => iterTensorLie H A F n c (γ u))
      (iterTensorLie H A F (n+1) c (γ t)) s t := by
  have hf := (iterTensorLie_polySmooth hH A F hA hF n c).smooth.differentiable (by simp)
  have hd := (hf (γ t)).hasFDerivAt.comp_hasDerivWithinAt t (hγ t ht)
  change HasDerivWithinAt ((iterTensorLie H A F n c) ∘ γ)
    (tensorLie H A (iterTensorLie H A F n) c (γ t)) s t
  rw [tensorLie_eq_directional H A (iterTensorLie H A F n)
    (fun c => (hA c).smooth) (fun c => (iterTensorLie_polySmooth hH A F hA hF n c).smooth)
    hsk c (γ t)]
  exact hd

lemma tensorVector_contDiff {S : Type} [Fintype S] {d : ℕ}
    (F : (S → Fin d) → Point d → ℝ) (hF : ∀c,ContDiff ℝ (⊤:ℕ∞) (F c)) :
    ContDiff ℝ (⊤:ℕ∞) (tensorVector F) := by
  exact (PiLp.continuousLinearEquiv 2 ℝ (fun _ : S → Fin d => ℝ)).symm.contDiff.comp
    (contDiff_pi.mpr hF)

lemma lie_vector_chain {S : Type} [Fintype S] {d : ℕ} {H : Point d → ℝ}
    (hH : PolySmooth H) (A : (Unit ⊕ Unit → Fin d) → Point d → ℝ)
    (F : (S → Fin d) → Point d → ℝ) (hA : ∀c,PolySmooth (A c)) (hF : ∀c,PolySmooth (F c))
    (hsk : ∀i z y,A (Sum.elim (fun _ => i) (fun _ => z)) y=
      -A (Sum.elim (fun _ => z) (fun _ => i)) y)
    {s : Set ℝ} (γ : ℝ → Point d)
    (hγ : ∀t∈s,HasDerivWithinAt γ (skewLieField H A (γ t)) s t)
    (n : ℕ) {t : ℝ} (ht : t∈s) :
    HasDerivWithinAt (fun u => tensorVector (iterTensorLie H A F n) (γ u))
      (tensorVector (iterTensorLie H A F (n+1)) (γ t)) s t := by
  have h := hasDerivWithinAt_pi.mpr (fun c => lie_chain hH A F hA hF hsk γ hγ n c ht)
  exact (PiLp.continuousLinearEquiv 2 ℝ (fun _ : S → Fin d => ℝ)).symm.toContinuousLinearMap.hasFDerivAt.comp_hasDerivWithinAt t h
end LogConcaveSampling

end

end

section

noncomputable section
namespace LogConcaveSampling
open scoped Classical BigOperators RealInnerProductSpace
open TensorEnergy

lemma coordinateProjection_left {d e : ℕ} (y : Point (d+e)) :
    coordinateProjection (leftCoordinates d e) y=(productPointEquiv d e y).1 := by
  ext i
  rfl
lemma coordinateProjection_right {d e : ℕ} (y : Point (d+e)) :
    coordinateProjection (rightCoordinates d e) y=(productPointEquiv d e y).2 := by
  ext i
  rfl

lemma productPointEquiv_basis_left {d e : ℕ} (i : Fin d) :
    productPointEquiv d e (EuclideanSpace.basisFun (Fin (d+e)) ℝ (i.castAdd e))=
      (EuclideanSpace.basisFun (Fin d) ℝ i,0) := by
  apply Prod.ext
  · rw [←coordinateProjection_left]
    exact coordinateProjection_basis_in (leftCoordinates d e) i
  · rw [←coordinateProjection_right]
    apply coordinateProjection_basis_out
    rintro ⟨j,hj⟩
    have hh := congrArg Fin.val hj
    dsimp [rightCoordinates] at hh
    omega
lemma productPointEquiv_basis_right {d e : ℕ} (i : Fin e) :
    productPointEquiv d e (EuclideanSpace.basisFun (Fin (d+e)) ℝ (i.natAdd d))=
      (0,EuclideanSpace.basisFun (Fin e) ℝ i) := by
  apply Prod.ext
  · rw [←coordinateProjection_left]
    apply coordinateProjection_basis_out
    rintro ⟨j,hj⟩
    have hh := congrArg Fin.val hj
    dsimp [leftCoordinates] at hh
    omega
  · rw [←coordinateProjection_right]
    exact coordinateProjection_basis_in (rightCoordinates d e) i

lemma directional_comp_linear {d e : ℕ} {f : Point e → ℝ}
    (hf : Differentiable ℝ f) (L : Point d →L[ℝ] Point e) (v y : Point d) :
    directional v (fun z => f (L z)) y=directional (L v) f (L y) := by
  exact congrArg (fun A : Point d →L[ℝ] ℝ => A v)
    ((hf (L y)).hasFDerivAt.comp y L.hasFDerivAt).fderiv

lemma productPotential_directional_left {d e : ℕ} {H : Point d → ℝ} {G : Point e → ℝ}
    (hH : Differentiable ℝ H) (hG : Differentiable ℝ G) (i : Fin d) (y : Point (d+e)) :
    directional (EuclideanSpace.basisFun (Fin (d+e)) ℝ (i.castAdd e))
      (productPotential H G) y=
      directional (EuclideanSpace.basisFun (Fin d) ℝ i) H (productPointEquiv d e y).1 := by
  let L := coordinateProjection (leftCoordinates d e)
  let R := coordinateProjection (rightCoordinates d e)
  have he : productPotential H G=(fun z => H (L z)+G (R z)) := by
    funext z; simp [productPotential,L,R,coordinateProjection_left,coordinateProjection_right]
  rw [he,directional_add (f:=fun z => H (L z)) (g:=fun z => G (R z))
    (hH.comp L.differentiable) (hG.comp R.differentiable)]
  dsimp only
  rw [directional_comp_linear hH L,directional_comp_linear hG R]
  have hb := productPointEquiv_basis_left (e:=e) i
  have hbL := congrArg Prod.fst hb
  have hbR := congrArg Prod.snd hb
  rw [←coordinateProjection_left] at hbL
  rw [←coordinateProjection_right] at hbR
  change L _=_ at hbL
  change R _=_ at hbR
  rw [hbL,hbR]
  simp [directional,L,coordinateProjection_left]

lemma productPotential_directional_right {d e : ℕ} {H : Point d → ℝ} {G : Point e → ℝ}
    (hH : Differentiable ℝ H) (hG : Differentiable ℝ G) (i : Fin e) (y : Point (d+e)) :
    directional (EuclideanSpace.basisFun (Fin (d+e)) ℝ (i.natAdd d))
      (productPotential H G) y=
      directional (EuclideanSpace.basisFun (Fin e) ℝ i) G (productPointEquiv d e y).2 := by
  let L := coordinateProjection (leftCoordinates d e)
  let R := coordinateProjection (rightCoordinates d e)
  have he : productPotential H G=(fun z => H (L z)+G (R z)) := by
    funext z; simp [productPotential,L,R,coordinateProjection_left,coordinateProjection_right]
  rw [he,directional_add (f:=fun z => H (L z)) (g:=fun z => G (R z))
    (hH.comp L.differentiable) (hG.comp R.differentiable)]
  dsimp only
  rw [directional_comp_linear hH L,directional_comp_linear hG R]
  have hb := productPointEquiv_basis_right (d:=d) i
  have hbL := congrArg Prod.fst hb
  have hbR := congrArg Prod.snd hb
  rw [←coordinateProjection_left] at hbL
  rw [←coordinateProjection_right] at hbR
  change L _=_ at hbL
  change R _=_ at hbR
  rw [hbL,hbR]
  simp [directional,R,coordinateProjection_right]
end LogConcaveSampling

end

end

section

noncomputable section
namespace LogConcaveSampling
open MeasureTheory
open scoped Classical BigOperators
open TensorEnergy

lemma spatialEnergy_leftLift {S : Type} [Fintype S] {d e : ℕ} {H : Point d → ℝ}
    (hH : Continuous H) [SFinite (gibbs H)] (F : (S → Fin d) → Point d → ℝ)
    (hF : ∀c,ContDiff ℝ (⊤:ℕ∞) (F c)) (ι : S → Fin d ↪ Fin (d+e)) (j : ℕ) :
    spatialEnergy (arrayCoordinateLift (leftCoordinates d e) ι F) j
      (gibbs (productPotential H (fun y : Point e => ‖y‖^2/2)))=spatialEnergy F j (gibbs H) := by
  let E := productPointEquiv d e
  have hmeas : AEStronglyMeasurable (fun p : Point d × Point e => spatialSquared F j p.1)
      ((gibbs (productPotential H (fun y : Point e => ‖y‖^2/2))).map E) := by
    apply Continuous.aestronglyMeasurable
    unfold spatialSquared squared
    exact continuous_finsetSum _ (fun _ _ =>
      ((JetCalculus.smooth_jet (hF _) _ _).continuous.comp continuous_fst).pow 2)
  unfold spatialEnergy
  simp_rw [spatialSquared_coordinateLift _ _ _ hF,coordinateProjection_left]
  rw [←integral_map E.continuous.measurable.aemeasurable hmeas,
    productPotential_gibbs hH (gaussianPotential_polySmooth e).smooth.continuous,gaussianPotential_gibbs]
  rw [integral_fun_fst]
  simp
end LogConcaveSampling

end

end

section

noncomputable section
namespace LogConcaveSampling
open scoped Classical BigOperators RealInnerProductSpace
open TensorEnergy

lemma jointSkew_skew {d : ℕ} (K : Point d → Point d →L[ℝ] Point d) (s : ℝ)
    (i z : Fin (d+d)) (y : Point (d+d)) :
    jointSkew K s (Sum.elim (fun _ => i) (fun _ => z)) y=
      -jointSkew K s (Sum.elim (fun _ => z) (fun _ => i)) y := by
  induction i using Fin.addCases <;> induction z using Fin.addCases <;>
    simp only [jointSkew,jointSkewEntry,Sum.elim_inl,Sum.elim_inr,Fin.addCases_left,Fin.addCases_right,mul_zero,mul_neg,neg_neg,neg_zero]

lemma jointSkew_polySmooth {d : ℕ} {K : Point d → Point d →L[ℝ] Point d}
    (hK : ∀i j,PolySmooth (fun y => inner ℝ (EuclideanSpace.basisFun (Fin d) ℝ i)
      (K y (EuclideanSpace.basisFun (Fin d) ℝ j)))) (s : ℝ) (c : Unit ⊕ Unit → Fin (d+d)) :
    PolySmooth (jointSkew K s c) := by
  suffices h : ∀i z : Fin (d+d),PolySmooth (jointSkewEntry K s i z) from h _ _
  intro i z
  let L := (ContinuousLinearMap.fst ℝ (Point d) (Point d)).comp
    (productPointEquiv d d).toContinuousLinearMap
  have hL (y : Point (d+d)) : L y=(productPointEquiv d d y).1 := rfl
  change PolySmooth (fun y => jointSkewEntry K s i z y)
  induction i using Fin.addCases <;> induction z using Fin.addCases
  · simpa only [jointSkewEntry,Fin.addCases_left,Fin.addCases_right,mul_zero] using (PolySmooth.const (0:ℝ) : PolySmooth (fun _ : Point (d+d) => 0))
  · simpa only [jointSkewEntry,Fin.addCases_left,Fin.addCases_right,hL] using (PolySmooth.const s⁻¹).mul ((hK _ _).comp_linear L)
  · simpa only [jointSkewEntry,Fin.addCases_left,Fin.addCases_right,hL] using (PolySmooth.const s⁻¹).mul (((hK _ _).comp_linear L).neg)
  · simpa only [jointSkewEntry,Fin.addCases_left,Fin.addCases_right,mul_zero] using (PolySmooth.const (0:ℝ) : PolySmooth (fun _ : Point (d+d) => 0))

lemma skewLieField_coordinate {D : ℕ} (H : Point D → ℝ)
    (A : (Unit ⊕ Unit → Fin D) → Point D → ℝ) (y : Point D) (z : Fin D) :
    skewLieField H A y z=∑i : Fin D,adjointCoordinate H (EuclideanSpace.basisFun (Fin D) ℝ i)
      (A (Sum.elim (fun _ => i) (fun _ => z))) y := by
  simp [skewLieField,EuclideanSpace.basisFun_apply,Pi.single_apply]

lemma directional_gaussianPotential {d : ℕ} (v y : Point d) :
    directional v (fun z : Point d => ‖z‖^2/2) y=inner ℝ y v := by
  have hd := ((hasFDerivAt_id y).norm_sq.const_mul (1/2 : ℝ)).fderiv
  change (fderiv ℝ (fun z : Point d => ‖z‖^2/2) y) v=_
  have he : (fun z : Point d => ‖z‖^2/2)=(fun z : Point d => (1/2:ℝ)*‖z‖^2) := by funext z; ring
  dsimp only [id_eq] at hd
  rw [he,hd]
  simp

lemma adjointCoordinate_const_mul {d : ℕ} {H f : Point d → ℝ}
    (hf : Differentiable ℝ f) (v : Point d) (c : ℝ) :
    adjointCoordinate H v (fun y => c*f y)=fun y => c*adjointCoordinate H v f y := by
  unfold adjointCoordinate
  rw [directional_mul (differentiable_const c) hf]
  funext y
  simp only [directional,fderiv_fun_const]
  change -(0*f y+c*(fderiv ℝ f y) v)+(fderiv ℝ H y) v*(c*f y)=_
  ring

lemma adjointCoordinate_zero {d : ℕ} (H : Point d → ℝ) (v : Point d) :
    adjointCoordinate H v (fun _ => 0)=fun _ => 0 := by
  funext y
  simp [adjointCoordinate,directional]
end LogConcaveSampling

end

end

section

noncomputable section
namespace LogConcaveSampling
open scoped Classical BigOperators RealInnerProductSpace
open TensorEnergy

lemma eq_pairLabels {D : ℕ} (c : Unit ⊕ Unit → Fin D) : c=pairLabels (c (.inl ())) (c (.inr ())) := by
  funext a
  rcases a with ⟨⟩|⟨⟩ <;> rfl

lemma pair_lift_in {d D : ℕ} (e e₁ e₂ : Fin d ↪ Fin D)
    (F : (Unit ⊕ Unit → Fin d) → Point d → ℝ) (i j : Fin d) (y : Point D) :
    arrayCoordinateLift e (Sum.elim (fun _ => e₁) (fun _ => e₂)) F
      (pairLabels (e₁ i) (e₂ j)) y=F (pairLabels i j) (coordinateProjection e y) := by
  have he : pairLabels (e₁ i) (e₂ j)=slotEmbedding (Sum.elim (fun _ => e₁) (fun _ => e₂)) (pairLabels i j) := by
    funext a; rcases a with ⟨⟩|⟨⟩ <;> rfl
  rw [he]
  exact zeroExtend_apply _ _ _

lemma pair_lift_out_left {d D : ℕ} (e e₁ e₂ : Fin d ↪ Fin D)
    (F : (Unit ⊕ Unit → Fin d) → Point d → ℝ) (i j : Fin D) (hi : i∉Set.range e₁) (y : Point D) :
    arrayCoordinateLift e (Sum.elim (fun _ => e₁) (fun _ => e₂)) F (pairLabels i j) y=0 := by
  apply zeroExtend_out
  rintro ⟨c,hc⟩
  exact hi ⟨c (.inl ()),congrFun hc (.inl ())⟩
lemma pair_lift_out_right {d D : ℕ} (e e₁ e₂ : Fin d ↪ Fin D)
    (F : (Unit ⊕ Unit → Fin d) → Point d → ℝ) (i j : Fin D) (hj : j∉Set.range e₂) (y : Point D) :
    arrayCoordinateLift e (Sum.elim (fun _ => e₁) (fun _ => e₂)) F (pairLabels i j) y=0 := by
  apply zeroExtend_out
  rintro ⟨c,hc⟩
  exact hj ⟨c (.inr ()),congrFun hc (.inr ())⟩

lemma left_not_right {d e : ℕ} (i : Fin d) : i.castAdd e∉Set.range (rightCoordinates d e) := by
  rintro ⟨j,hj⟩
  have hh := congrArg Fin.val hj
  dsimp [rightCoordinates] at hh
  omega
lemma right_not_left {d e : ℕ} (i : Fin e) : i.natAdd d∉Set.range (leftCoordinates d e) := by
  rintro ⟨j,hj⟩
  have hh := congrArg Fin.val hj
  dsimp [leftCoordinates] at hh
  omega

lemma jointSkew_eq_lifts {d : ℕ} (K : Point d → Point d →L[ℝ] Point d) (s : ℝ) :
    jointSkew K s=fun c y =>
      s⁻¹*arrayCoordinateLift (leftCoordinates d d)
        (Sum.elim (fun _ => leftCoordinates d d) (fun _ => rightCoordinates d d))
        (fun c y => matrixArray d (K y) (c ∘ Equiv.sumComm Unit Unit)) c y+
      (-s⁻¹)*arrayCoordinateLift (leftCoordinates d d)
        (Sum.elim (fun _ => rightCoordinates d d) (fun _ => leftCoordinates d d))
        (fun c y => matrixArray d (K y) c) c y := by
  funext c y
  rw [eq_pairLabels c]
  generalize c (.inl ())=i,c (.inr ())=j
  induction i using Fin.addCases <;> induction j using Fin.addCases
  · rw [pair_lift_out_right _ _ _ _ _ _ (left_not_right _),
      pair_lift_out_left _ _ _ _ _ _ (left_not_right _)]
    simp only [jointSkew,pairLabels,Sum.elim_inl,Sum.elim_inr,jointSkewEntry,Fin.addCases_left,mul_zero,add_zero]
  · change _=s⁻¹*arrayCoordinateLift _ _ _
      (pairLabels (leftCoordinates d d _) (rightCoordinates d d _)) y+_
    rw [pair_lift_in,pair_lift_out_left _ _ _ _ _ _ (left_not_right _)]
    simp only [jointSkew,pairLabels,Sum.elim_inl,Sum.elim_inr,jointSkewEntry,Fin.addCases_left,
      Fin.addCases_right,mul_zero,add_zero,coordinateProjection_left]
    rfl
  · change _=_+(-s⁻¹)*arrayCoordinateLift _ _ _
      (pairLabels (rightCoordinates d d _) (leftCoordinates d d _)) y
    rw [pair_lift_out_left _ _ _ _ _ _ (right_not_left _),pair_lift_in]
    simp only [jointSkew,pairLabels,Sum.elim_inl,Sum.elim_inr,jointSkewEntry,Fin.addCases_left,
      Fin.addCases_right,mul_zero,zero_add,coordinateProjection_left,mul_neg,neg_mul]
    rfl
  · rw [pair_lift_out_left _ _ _ _ _ _ (right_not_left _),
      pair_lift_out_right _ _ _ _ _ _ (right_not_left _)]
    simp only [jointSkew,pairLabels,Sum.elim_inl,Sum.elim_inr,jointSkewEntry,Fin.addCases_right,mul_zero,add_zero]
end LogConcaveSampling

end

end

section

noncomputable section
namespace LogConcaveSampling
open scoped Classical BigOperators RealInnerProductSpace NNReal
open TensorEnergy

lemma spatialTensor_add {S J : Type} {d : ℕ}
    (F G : (S → Fin d) → Point d → ℝ)
    (hF : ∀c,ContDiff ℝ (⊤:ℕ∞) (F c))
    (hG : ∀c,ContDiff ℝ (⊤:ℕ∞) (G c)) (l : List J) (y : Point d) :
    spatialTensor (fun c z => F c z+G c z) l y=
      fun c => spatialTensor F l y c+spatialTensor G l y c := by
  funext c
  exact congrFun (JetCalculus.jet_add (hF _) (hG _) _ l) y

theorem jointSkew_spatial_bound {d n : ℕ} {K : Point d → Point d →L[ℝ] Point d}
    (hK : ∀c,ContDiff ℝ (⊤:ℕ∞) (fun y => matrixArray d (K y) c))
    {M : ℝ} (hM : 0≤M)
    (hb : ∀y,AllSplitBound (spatialTensor (fun c z => matrixArray d (K z) c) (List.finRange n) y) M)
    (s : ℝ) (y : Point (d+d)) :
    AllSplitBound (spatialTensor (jointSkew K s) (List.finRange n) y) (2*|s⁻¹| *M) := by
  let F := fun c z => matrixArray d (K z) c
  let G := fun c => F (c ∘ Equiv.sumComm Unit Unit)
  have hG : ∀c,ContDiff ℝ (⊤:ℕ∞) (G c) := fun _ => hK _
  have hbg (z : Point d) : AllSplitBound (spatialTensor G (List.finRange n) z) M := by
    apply spatialTensor_allSplit_relabel F hK (Equiv.sumComm Unit Unit) (Equiv.refl (Fin n))
      (List.finRange n) (List.finRange n) _ z M (hb z)
    simp
  let L := arrayCoordinateLift (leftCoordinates d d)
    (Sum.elim (fun _ => leftCoordinates d d) (fun _ => rightCoordinates d d)) G
  let R := arrayCoordinateLift (leftCoordinates d d)
    (Sum.elim (fun _ => rightCoordinates d d) (fun _ => leftCoordinates d d)) F
  have hL : ∀c,ContDiff ℝ (⊤:ℕ∞) (L c) := arrayCoordinateLift_smooth _ _ _ hG
  have hR : ∀c,ContDiff ℝ (⊤:ℕ∞) (R c) := arrayCoordinateLift_smooth _ _ _ hK
  have hbL : AllSplitBound (spatialTensor L (List.finRange n) y) M :=
    AllSplitBound.coordinateLift _ _ _ hG hbg y
  have hbR : AllSplitBound (spatialTensor R (List.finRange n) y) M :=
    AllSplitBound.coordinateLift _ _ _ hK hb y
  have he : jointSkew K s=fun c z => s⁻¹*L c z+(-s⁻¹)*R c z := jointSkew_eq_lifts K s
  rw [he,spatialTensor_add _ _ (fun c => contDiff_const.mul (hL c))
    (fun c => contDiff_const.mul (hR c)),spatialTensor_const_mul L hL,
    spatialTensor_const_mul R hR]
  have hh := (hbL.abs_const_mul s⁻¹).add (hbR.abs_const_mul (-s⁻¹))
    (mul_nonneg (abs_nonneg _) hM) (mul_nonneg (abs_nonneg _) hM)
  convert hh using 1
  all_goals try with_reducible_and_instances rfl
  rw [abs_neg]
  ring

end LogConcaveSampling

end

end

section

noncomputable section
namespace LogConcaveSampling
open scoped Classical BigOperators
open TensorEnergy

lemma scoreLabels_eq {d : ℕ} (c : Empty ⊕ Unit → Fin d) :
    c=fun _ => c (.inr ()) := by
  funext a
  rcases a with e|⟨⟩
  · exact e.elim
  · rfl

lemma scalarSlot_lift_in {d D : ℕ} (e e₁ : Fin d ↪ Fin D)
    (F : (Empty ⊕ Unit → Fin d) → Point d → ℝ) (i : Fin d) (y : Point D) :
    arrayCoordinateLift e (fun _ => e₁) F (fun _ => e₁ i) y=
      F (fun _ => i) (coordinateProjection e y) := by
  exact zeroExtend_apply (slotEmbedding (fun _ : Empty ⊕ Unit => e₁))
    (fun a => F a (coordinateProjection e y)) (fun _ => i)

lemma scalarSlot_lift_out {d D : ℕ} (e e₁ : Fin d ↪ Fin D)
    (F : (Empty ⊕ Unit → Fin d) → Point d → ℝ) (i : Fin D) (hi : i∉Set.range e₁) (y : Point D) :
    arrayCoordinateLift e (fun _ => e₁) F (fun _ => i) y=0 := by
  apply zeroExtend_out
  rintro ⟨a,ha⟩
  exact hi ⟨a (.inr ()),congrFun ha (.inr ())⟩

lemma scoreField_product {d e : ℕ} {H : Point d → ℝ} {G : Point e → ℝ}
    (hH : Differentiable ℝ H) (hG : Differentiable ℝ G) :
    scoreField (productPotential H G)=fun c y =>
      arrayCoordinateLift (leftCoordinates d e) (fun _ => leftCoordinates d e) (scoreField H) c y+
      arrayCoordinateLift (rightCoordinates d e) (fun _ => rightCoordinates d e) (scoreField G) c y := by
  funext c y
  rw [scoreLabels_eq c]
  generalize c (.inr ())=i
  induction i using Fin.addCases with
  | left i =>
    change _=arrayCoordinateLift _ _ _ (fun _ => leftCoordinates d e i) y+_
    rw [scalarSlot_lift_in,scalarSlot_lift_out _ _ _ _ (left_not_right i),add_zero,coordinateProjection_left]
    exact productPotential_directional_left hH hG i y
  | right i =>
    change _=_+arrayCoordinateLift _ _ _ (fun _ => rightCoordinates d e i) y
    rw [scalarSlot_lift_out _ _ _ _ (right_not_left i),scalarSlot_lift_in,zero_add,coordinateProjection_right]
    exact productPotential_directional_right hH hG i y

lemma scoreField_product_allSplit {d e n : ℕ} {H : Point d → ℝ} {G : Point e → ℝ}
    (hH : PolySmooth H) (hG : PolySmooth G) {M N : ℝ} (hM : 0≤M) (hN : 0≤N)
    (hbH : ∀y,AllSplitBound (spatialTensor (scoreField H) (List.finRange n) y) M)
    (hbG : ∀y,AllSplitBound (spatialTensor (scoreField G) (List.finRange n) y) N)
    (y : Point (d+e)) :
    AllSplitBound (spatialTensor (scoreField (productPotential H G)) (List.finRange n) y) (M+N) := by
  have hsH (c) := (scoreField_polySmooth hH c).smooth
  have hsG (c) := (scoreField_polySmooth hG c).smooth
  rw [scoreField_product (hH.smooth.differentiable (by simp)) (hG.smooth.differentiable (by simp)),
    spatialTensor_add _ _ (arrayCoordinateLift_smooth _ _ _ hsH) (arrayCoordinateLift_smooth _ _ _ hsG)]
  exact (AllSplitBound.coordinateLift _ _ _ hsH hbH y).add
    (AllSplitBound.coordinateLift _ _ _ hsG hbG y) hM hN
end LogConcaveSampling

end

end

end

end OAI
end

section
-- module Solutions.OAIQ048_LC.LogConcave_Sampling_AdjointCoordinateProductLeft
attribute [-instance] _root_.OAI.LogConcaveSampling.LowerBound.couplingLaw_probability _root_.OAI.LogConcaveSampling.LowerBound.remainingHaar_probability _root_.OAI.LogConcaveSampling.LowerBound.roundRandomLaw_probability _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_invInvariant _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_isHaar _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_probability _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_rightInvariant _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_compactSpace _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_measurableInv _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_measurableMul _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_secondCountable _root_.OAI.LogConcaveSampling.MeanTree.instIsProbabilityMeasureRowTapeRowLaw _root_.OAI.LogConcaveSampling.OracleCompiler.topSeedLaw_probability _root_.OAI.LogConcaveSampling.noiseKernel_markov
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
namespace LogConcaveSampling
open scoped Classical BigOperators RealInnerProductSpace
open TensorEnergy

lemma adjointCoordinate_product_left {d e : ℕ} {H f : Point d → ℝ} {G : Point e → ℝ}
    (hH : Differentiable ℝ H) (hG : Differentiable ℝ G) (hf : Differentiable ℝ f)
    (i : Fin d) (y : Point (d+e)) :
    adjointCoordinate (productPotential H G) (EuclideanSpace.basisFun (Fin (d+e)) ℝ (i.castAdd e))
      (fun z => f (productPointEquiv d e z).1) y=
      adjointCoordinate H (EuclideanSpace.basisFun (Fin d) ℝ i) f (productPointEquiv d e y).1 := by
  let L := coordinateProjection (leftCoordinates d e)
  have he : (fun z => f (productPointEquiv d e z).1)=(fun z => f (L z)) := by
    funext z; rw [coordinateProjection_left]
  unfold adjointCoordinate
  rw [he,productPotential_directional_left hH hG,directional_comp_linear hf L]
  have hb := coordinateProjection_basis_in (leftCoordinates d e) i
  change L (EuclideanSpace.basisFun (Fin (d+e)) ℝ (i.castAdd e)) = _ at hb
  rw [hb]
  simp only [L,coordinateProjection_left]

lemma adjointCoordinate_product_right {d e : ℕ} {H f : Point d → ℝ} {G : Point e → ℝ}
    (hH : Differentiable ℝ H) (hG : Differentiable ℝ G) (hf : Differentiable ℝ f)
    (i : Fin e) (y : Point (d+e)) :
    adjointCoordinate (productPotential H G) (EuclideanSpace.basisFun (Fin (d+e)) ℝ (i.natAdd d))
      (fun z => f (productPointEquiv d e z).1) y=
      directional (EuclideanSpace.basisFun (Fin e) ℝ i) G (productPointEquiv d e y).2*
        f (productPointEquiv d e y).1 := by
  let L := coordinateProjection (leftCoordinates d e)
  have he : (fun z => f (productPointEquiv d e z).1)=(fun z => f (L z)) := by
    funext z; rw [coordinateProjection_left]
  unfold adjointCoordinate
  rw [he,productPotential_directional_right hH hG,directional_comp_linear hf L]
  have hb := congrArg Prod.fst (productPointEquiv_basis_right (d:=d) i)
  rw [←coordinateProjection_left] at hb
  change L _=0 at hb
  rw [hb]
  simp only [directional,map_zero,neg_zero,zero_add,L,coordinateProjection_left]

lemma jointSkewEntry_LL {d : ℕ} (K : Point d → Point d →L[ℝ] Point d) (s : ℝ) (i j : Fin d) :
    jointSkewEntry K s (i.castAdd d) (j.castAdd d)=fun _ => 0 := by
  funext y; simp only [jointSkewEntry,Fin.addCases_left,mul_zero]
lemma jointSkewEntry_RR {d : ℕ} (K : Point d → Point d →L[ℝ] Point d) (s : ℝ) (i j : Fin d) :
    jointSkewEntry K s (i.natAdd d) (j.natAdd d)=fun _ => 0 := by
  funext y; simp only [jointSkewEntry,Fin.addCases_right,mul_zero]
lemma jointSkewEntry_LR {d : ℕ} (K : Point d → Point d →L[ℝ] Point d) (s : ℝ) (i j : Fin d) :
    jointSkewEntry K s (i.castAdd d) (j.natAdd d)=fun y => s⁻¹*
      inner ℝ (EuclideanSpace.basisFun (Fin d) ℝ j)
        (K (productPointEquiv d d y).1 (EuclideanSpace.basisFun (Fin d) ℝ i)) := by
  funext y; simp only [jointSkewEntry,Fin.addCases_left,Fin.addCases_right]
lemma jointSkewEntry_RL {d : ℕ} (K : Point d → Point d →L[ℝ] Point d) (s : ℝ) (i j : Fin d) :
    jointSkewEntry K s (i.natAdd d) (j.castAdd d)=fun y => (-s⁻¹)*
      inner ℝ (EuclideanSpace.basisFun (Fin d) ℝ i)
        (K (productPointEquiv d d y).1 (EuclideanSpace.basisFun (Fin d) ℝ j)) := by
  funext y; simp only [jointSkewEntry,Fin.addCases_left,Fin.addCases_right,mul_neg,neg_mul]
end LogConcaveSampling

end

end

end

end OAI
end

section
-- module Solutions.OAIQ048_LC.LogConcave_Sampling_InnerBasisCoordinate
attribute [-instance] _root_.OAI.LogConcaveSampling.LowerBound.couplingLaw_probability _root_.OAI.LogConcaveSampling.LowerBound.remainingHaar_probability _root_.OAI.LogConcaveSampling.LowerBound.roundRandomLaw_probability _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_invInvariant _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_isHaar _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_probability _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_rightInvariant _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_compactSpace _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_measurableInv _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_measurableMul _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_secondCountable _root_.OAI.LogConcaveSampling.MeanTree.instIsProbabilityMeasureRowTapeRowLaw _root_.OAI.LogConcaveSampling.OracleCompiler.topSeedLaw_probability _root_.OAI.LogConcaveSampling.noiseKernel_markov
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
namespace LogConcaveSampling
open scoped Classical BigOperators RealInnerProductSpace
open TensorEnergy

lemma inner_basis_coordinate {d : ℕ} (y : Point d) (i : Fin d) :
    inner ℝ (EuclideanSpace.basisFun (Fin d) ℝ i) y=y i := by
  simp [EuclideanSpace.basisFun_apply,PiLp.inner_apply]

theorem jointSkew_field {d : ℕ} {H : Point d → ℝ}
    {K : Point d → Point d →L[ℝ] Point d} {m : Point d → Point d}
    (hH : Differentiable ℝ H)
    (hK : ∀i j,Differentiable ℝ (fun y => inner ℝ (EuclideanSpace.basisFun (Fin d) ℝ i)
      (K y (EuclideanSpace.basisFun (Fin d) ℝ j))))
    (hstein : ∀u : Point d,tensorAdjoint H (EuclideanSpace.basisFun (Fin d) ℝ)
      (fun i y => inner ℝ u (K y (EuclideanSpace.basisFun (Fin d) ℝ i)))=
      fun y => inner ℝ u (m y))
    (s : ℝ) (y : Point (d+d)) :
    productPointEquiv d d (skewLieField (productPotential H (fun z : Point d => ‖z‖^2/2))
      (jointSkew K s) y)=skewCenteringField K m s (productPointEquiv d d y) := by
  let L := coordinateProjection (leftCoordinates d d)
  have hf (i j : Fin d) : Differentiable ℝ (fun z => inner ℝ
      (EuclideanSpace.basisFun (Fin d) ℝ i)
      (K (productPointEquiv d d z).1 (EuclideanSpace.basisFun (Fin d) ℝ j))) :=
    (hK i j).comp L.differentiable
  have hG := (gaussianPotential_polySmooth d).smooth.differentiable (by simp)
  apply Prod.ext
  · ext z
    change skewLieField _ _ y (z.castAdd d)=(-s⁻¹ • (K (productPointEquiv d d y).1).adjoint
      (productPointEquiv d d y).2) z
    rw [skewLieField_coordinate,Fin.sum_univ_add]
    simp only [jointSkew,Sum.elim_inl,Sum.elim_inr,jointSkewEntry_LL,jointSkewEntry_RL,
      adjointCoordinate_zero,Finset.sum_const_zero,zero_add]
    simp_rw [adjointCoordinate_const_mul (hf _ _)]
    simp_rw [adjointCoordinate_product_right hH hG (hK _ _),directional_gaussianPotential]
    rw [←Finset.mul_sum]
    change (-s⁻¹)*(∑i : Fin d,inner ℝ (productPointEquiv d d y).2
      (EuclideanSpace.basisFun (Fin d) ℝ i)*inner ℝ (EuclideanSpace.basisFun (Fin d) ℝ i)
      (K (productPointEquiv d d y).1 (EuclideanSpace.basisFun (Fin d) ℝ z)))=
      (-s⁻¹)*((K (productPointEquiv d d y).1).adjoint (productPointEquiv d d y).2) z
    congr 1
    rw [←inner_basis_coordinate,ContinuousLinearMap.adjoint_inner_right]
    simp_rw [real_inner_comm (productPointEquiv d d y).2,inner_basis_coordinate]
    rw [real_inner_comm,PiLp.inner_apply]
    simp only [RCLike.inner_apply,conj_trivial]
    apply Finset.sum_congr rfl
    intro i _
    rw [real_inner_comm,inner_basis_coordinate]
  · ext z
    change skewLieField _ _ y (z.natAdd d)=(s⁻¹ • m (productPointEquiv d d y).1) z
    rw [skewLieField_coordinate,Fin.sum_univ_add]
    simp only [jointSkew,Sum.elim_inl,Sum.elim_inr,jointSkewEntry_RR,jointSkewEntry_LR,
      adjointCoordinate_zero,Finset.sum_const_zero,add_zero]
    simp_rw [adjointCoordinate_const_mul (hf _ _)]
    simp_rw [adjointCoordinate_product_left hH hG (hK _ _)]
    rw [←Finset.mul_sum]
    change s⁻¹*tensorAdjoint H (EuclideanSpace.basisFun (Fin d) ℝ)
      (fun i w => inner ℝ (EuclideanSpace.basisFun (Fin d) ℝ z)
        (K w (EuclideanSpace.basisFun (Fin d) ℝ i))) (productPointEquiv d d y).1=_
    rw [hstein]
    dsimp only
    rw [inner_basis_coordinate]
    rfl
end LogConcaveSampling

end

end

end

end OAI
end

section
-- module Solutions.OAIQ048_LC.LogConcave_Sampling_ConditionalMeanArray
attribute [-instance] _root_.OAI.LogConcaveSampling.LowerBound.couplingLaw_probability _root_.OAI.LogConcaveSampling.LowerBound.remainingHaar_probability _root_.OAI.LogConcaveSampling.LowerBound.roundRandomLaw_probability _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_invInvariant _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_isHaar _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_probability _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_rightInvariant _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_compactSpace _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_measurableInv _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_measurableMul _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_secondCountable _root_.OAI.LogConcaveSampling.MeanTree.instIsProbabilityMeasureRowTapeRowLaw _root_.OAI.LogConcaveSampling.OracleCompiler.topSeedLaw_probability _root_.OAI.LogConcaveSampling.noiseKernel_markov
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
namespace LogConcaveSampling
open scoped Classical BigOperators RealInnerProductSpace NNReal
open TensorEnergy

lemma scoreAugmented_gaussian {d : ℕ} {K : Type} (l : List K)
    (y : Point d) (c : (K ⊕ Unit) ⊕ Unit → Fin d) :
    scoreAugmented (fun z : Point d => ‖z‖^2/2) l y c=
      if l=[] then (if c (.inl (.inr ()))=c (.inr ()) then 1 else 0) else 0 := by
  let v := EuclideanSpace.basisFun (Fin d) ℝ
  have hg : directional (v (c (.inr ()))) (fun z : Point d => ‖z‖^2/2)=
      fun z => inner ℝ (v (c (.inr ()))) z := by
    funext z
    rw [directional_gaussianPotential,real_inner_comm]
  have hd : directional (v (c (.inl (.inr ()))))
      (fun z => inner ℝ (v (c (.inr ()))) z)=fun _ =>
      inner ℝ (v (c (.inr ()))) (v (c (.inl (.inr ())))) := by
    funext z
    exact congrArg (fun A : Point d →L[ℝ] ℝ => A (v (c (.inl (.inr ())))))
      (innerSL ℝ (v (c (.inr ())))).hasFDerivAt.fderiv
  unfold scoreAugmented
  change JetCalculus.jet _ l (directional _ (directional (v (c (.inr ()))) _)) y=_
  rw [hg,hd,JetCalculus.jet_const]
  by_cases hl : l=[]
  · simp only [hl,↓reduceIte]
    rw [EuclideanSpace.basisFun_inner]
    simp [EuclideanSpace.basisFun_apply,v,eq_comm]
  · simp only [hl,↓reduceIte]

lemma scoreField_gaussian_allSplit {d n : ℕ} (hn : 0<n) (y : Point d) :
    AllSplitBound (spatialTensor (scoreField (fun z : Point d => ‖z‖^2/2))
      (List.finRange n) y) 1 := by
  obtain ⟨h,rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn.ne'
  have hh := (allSplitBound_spatial_delta (d:=d) (List.finRange h) (by simp)).reindex (scoreSpatialSlots h)
  have he : (fun c => (if List.finRange h=[] then
        (if (c ∘ scoreSpatialSlots h) (.inl (.inr ()))=(c ∘ scoreSpatialSlots h) (.inr ()) then (1:ℝ) else 0) else 0))=
      spatialTensor (scoreField (fun z : Point d => ‖z‖^2/2)) (List.finRange (h+1)) y := by
    funext c
    rw [←scoreAugmented_gaussian,scoreSpatial_eq]
  change AllSplitBound (fun c => (if List.finRange h=[] then
        (if (c ∘ scoreSpatialSlots h) (.inl (.inr ()))=(c ∘ scoreSpatialSlots h) (.inr ()) then (1:ℝ) else 0) else 0)) _ at hh
  rw [he] at hh
  apply hh.mono
  · split_ifs <;> norm_num
  · split_ifs <;> norm_num

lemma centeringScore_allSplit {d n : ℕ} {F : Point d → ℝ} {lam : ℝ≥0}
    (hF : Primitive F lam) (x : Point d) {r T : ℝ} (hr : 0 < r)
    (hlam : 0<lam) (hl : (lam:ℝ)*r^2≤1/2) (hT0 : 0≤T) (hT1 : T<1)
    (hn : 0<n) (y : Point (d+d)) :
    AllSplitBound (spatialTensor (scoreField (productPotential
      (interpolationPotential F x r T) (fun z : Point d => ‖z‖^2/2)))
      (List.finRange n) y) (2+normalizedTensorMajorant (n+1) (1-T^2)) := by
  convert scoreField_product_allSplit
    (interpolationPotential_polySmooth hF x hr hlam hl hT0 hT1) (gaussianPotential_polySmooth d)
    (add_nonneg (by norm_num : (0:ℝ)≤1) (normalizedTensorMajorant_nonneg _ _))
    (by norm_num : (0:ℝ)≤1) (scoreField_spatial_allSplit hF x hr hlam hl hT0 hT1 n hn)
    (scoreField_gaussian_allSplit hn) y using 1
  all_goals try with_reducible_and_instances rfl
  ring
end LogConcaveSampling

end

end

section

noncomputable section
namespace LogConcaveSampling
open MeasureTheory
open scoped Classical BigOperators NNReal RealInnerProductSpace
open TensorEnergy

lemma probability_gibbs_of_gaussianTail {d : ℕ} {H : Point d → ℝ}
    (hH : Continuous H) (ht : HasGaussianLowerTail H) : IsProbabilityMeasure (gibbs H) := by
  have hi : Integrable (fun z => Real.exp (-H z)) := by
    simpa only [inner_zero_left,zero_sub,smul_eq_mul,mul_one] using
      integrable_tilted H hH continuous_const ht (growth_const (1:ℝ)) 0
  exact probability_gibbs_of_partition (partition_pos_of_continuous hH).ne'
    (partition_ne_top_of_integrable hi)

end LogConcaveSampling

end

end

section

noncomputable section
namespace LogConcaveSampling
open scoped Classical BigOperators NNReal RealInnerProductSpace

lemma directional_basis_gradient {d : ℕ} (H : Point d → ℝ) (y : Point d) (i : Fin d) :
    directional (EuclideanSpace.basisFun (Fin d) ℝ i) H y=gradient H y i := by
  rw [directional_gradient]
  have hh (v : Point d) : inner ℝ v (EuclideanSpace.basisFun (Fin d) ℝ i)=v i := by
    simp [EuclideanSpace.basisFun_apply,PiLp.inner_apply]
  exact hh (gradient H y)

lemma gradient_productPotential {d e : ℕ} {H : Point d → ℝ} {G : Point e → ℝ}
    (hH : Differentiable ℝ H) (hG : Differentiable ℝ G) (y : Point (d+e)) :
    productPointEquiv d e (gradient (productPotential H G) y)=
      (gradient H (productPointEquiv d e y).1,gradient G (productPointEquiv d e y).2) := by
  apply Prod.ext
  · ext i
    change gradient (productPotential H G) y (Fin.castAdd e i)=_
    rw [←directional_basis_gradient,productPotential_directional_left hH hG,directional_basis_gradient]
  · ext i
    change gradient (productPotential H G) y (Fin.natAdd d i)=_
    rw [←directional_basis_gradient,productPotential_directional_right hH hG,directional_basis_gradient]

lemma productPointEquiv_fst_norm_le {d e : ℕ} (y : Point (d+e)) :
    ‖(productPointEquiv d e y).1‖≤‖y‖ := by
  nlinarith [productPointEquiv_norm_sq y,sq_nonneg ‖(productPointEquiv d e y).2‖,
    norm_nonneg y,norm_nonneg (productPointEquiv d e y).1]
lemma productPointEquiv_snd_norm_le {d e : ℕ} (y : Point (d+e)) :
    ‖(productPointEquiv d e y).2‖≤‖y‖ := by
  nlinarith [productPointEquiv_norm_sq y,sq_nonneg ‖(productPointEquiv d e y).1‖,
    norm_nonneg y,norm_nonneg (productPointEquiv d e y).2]

lemma productPotential_gradient_lipschitz {d e : ℕ} {H : Point d → ℝ} {G : Point e → ℝ}
    (hH : Differentiable ℝ H) (hG : Differentiable ℝ G) {K L : ℝ≥0}
    (hK : LipschitzWith K (gradient H)) (hL : LipschitzWith L (gradient G)) :
    LipschitzWith (K+L) (gradient (productPotential H G)) := by
  apply LipschitzWith.of_dist_le_mul
  intro y z
  simp only [dist_eq_norm,NNReal.coe_add]
  have h1 := hK.dist_le_mul (productPointEquiv d e y).1 (productPointEquiv d e z).1
  have h2 := hL.dist_le_mul (productPointEquiv d e y).2 (productPointEquiv d e z).2
  simp only [dist_eq_norm] at h1 h2
  have hp := productPointEquiv_norm_sq (gradient (productPotential H G) y-gradient (productPotential H G) z)
  rw [map_sub,gradient_productPotential hH hG,gradient_productPotential hH hG] at hp
  simp only [Prod.fst_sub,Prod.snd_sub] at hp
  have h1' := productPointEquiv_fst_norm_le (y-z)
  have h2' := productPointEquiv_snd_norm_le (y-z)
  simp only [map_sub,Prod.fst_sub,Prod.snd_sub] at h1' h2'
  have h1'' := h1.trans (mul_le_mul_of_nonneg_left h1' K.2)
  have h2'' := h2.trans (mul_le_mul_of_nonneg_left h2' L.2)
  have hn : ‖gradient (productPotential H G) y-gradient (productPotential H G) z‖≤
      ‖gradient H (productPointEquiv d e y).1-gradient H (productPointEquiv d e z).1‖+
      ‖gradient G (productPointEquiv d e y).2-gradient G (productPointEquiv d e z).2‖ := by
    nlinarith [norm_nonneg (gradient (productPotential H G) y-gradient (productPotential H G) z),
      norm_nonneg (gradient H (productPointEquiv d e y).1-gradient H (productPointEquiv d e z).1),
      norm_nonneg (gradient G (productPointEquiv d e y).2-gradient G (productPointEquiv d e z).2),
      mul_nonneg (norm_nonneg (gradient H (productPointEquiv d e y).1-gradient H (productPointEquiv d e z).1))
        (norm_nonneg (gradient G (productPointEquiv d e y).2-gradient G (productPointEquiv d e z).2))]
  exact hn.trans ((add_le_add h1'' h2'').trans_eq (by ring))
end LogConcaveSampling

end

end

end

end OAI
end

section
-- module Solutions.OAIQ048_LC.LogConcave_Numerics_NormSubSqTwo
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
namespace LogConcaveSampling.RMSIntegral
open MeasureTheory

variable {Ω E : Type*} [MeasurableSpace Ω] {ν : Measure Ω}
  [NormedAddCommGroup E]

lemma norm_sub_sq_le_two (x y : E) : ‖x-y‖^2≤2*‖x‖^2+2*‖y‖^2 := by
  have h := pow_le_pow_left₀ (norm_nonneg (x-y)) (norm_sub_le x y) 2
  nlinarith [sq_nonneg (‖x‖-‖y‖)]

lemma sub_sq_bound {f g : Ω → E} (hf : AEStronglyMeasurable f ν)
    (hg : AEStronglyMeasurable g ν)
    (hfi : Integrable (fun z => ‖f z‖^2) ν) (hgi : Integrable (fun z => ‖g z‖^2) ν)
    {A B : ℝ} (hA : (∫z,‖f z‖^2 ∂ν)≤A) (hB : (∫z,‖g z‖^2 ∂ν)≤B) :
    Integrable (fun z => ‖f z-g z‖^2) ν ∧
      (∫z,‖f z-g z‖^2 ∂ν)≤2*A+2*B := by
  have hi : Integrable (fun z => 2*‖f z‖^2+2*‖g z‖^2) ν :=
    (hfi.const_mul 2).add (hgi.const_mul 2)
  have hm : AEStronglyMeasurable (fun z => ‖f z-g z‖^2) ν := (hf.sub hg).norm.pow 2
  have hs : Integrable (fun z => ‖f z-g z‖^2) ν :=
    hi.mono' hm (Filter.Eventually.of_forall (fun z => by
      simpa only [Real.norm_eq_abs,abs_sq] using norm_sub_sq_le_two (f z) (g z)))
  refine ⟨hs,(integral_mono hs hi (fun z => norm_sub_sq_le_two (f z) (g z))).trans ?_⟩
  rw [integral_add (hfi.const_mul 2) (hgi.const_mul 2),integral_const_mul,integral_const_mul]
  linarith
end LogConcaveSampling.RMSIntegral

end

end

end

end OAI
end

section
-- module Solutions.OAIQ048_LC.LogConcave_Numerics_Basis
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section

noncomputable section
namespace LogConcaveSampling.RMSIntegral
open MeasureTheory Set
open scoped BigOperators

variable {I β E : Type*} [Fintype I] [MeasurableSpace β]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  {ν : Measure β}

omit [CompleteSpace E] in
lemma norm_weighted_sum_sq (w : I → ℝ) (v : I → E) :
    ‖∑i,w i • v i‖^2≤(∑i,|w i|)*(∑i,|w i| *‖v i‖^2) := by
  have h := norm_sum_le Finset.univ (fun i => w i • v i)
  simp only [norm_smul,Real.norm_eq_abs] at h
  apply (pow_le_pow_left₀ (norm_nonneg _) h 2).trans
  apply Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul Finset.univ
    (r:=fun i => |w i| * ‖v i‖) (f:=fun i => |w i|) (g:=fun i => |w i| *‖v i‖^2)
  · exact fun i _ => abs_nonneg _
  · exact fun i _ => mul_nonneg (abs_nonneg _) (sq_nonneg _)
  · intro index _; exact le_of_eq (by ring)

omit [CompleteSpace E] in
theorem weighted_sum_sq (w : I → ℝ) (f : I → β → E) {B : ℝ}
    (hm : ∀i,AEStronglyMeasurable (f i) ν)
    (hi : ∀i,Integrable (fun z => ‖f i z‖^2) ν)
    (hB : ∀i,(∫z,‖f i z‖^2 ∂ν)≤B) :
    Integrable (fun z => ‖∑i,w i • f i z‖^2) ν ∧
      (∫z,‖∑i,w i • f i z‖^2 ∂ν)≤(∑i,|w i|)^2*B := by
  have hw0 : 0≤∑i,|w i| := Finset.sum_nonneg (fun _ _ => abs_nonneg _)
  have hs : Integrable (fun z => (∑i,|w i|)*(∑i,|w i| *‖f i z‖^2)) ν := by
    apply Integrable.const_mul
    exact integrable_finsetSum _ (fun i _ => (hi i).const_mul _)
  have hmeas : AEStronglyMeasurable (fun z => ‖∑i,w i • f i z‖^2) ν := by
    have hh := (Finset.aestronglyMeasurable_sum Finset.univ
        (fun i _ => (hm i).const_smul (w i))).norm.pow 2
    convert hh using 1
    all_goals try with_reducible_and_instances rfl
    ext z
    simp only [Finset.sum_apply,Pi.smul_apply,Pi.pow_apply]
  have ho : Integrable (fun z => ‖∑i,w i • f i z‖^2) ν :=
    hs.mono' hmeas (Filter.Eventually.of_forall (fun z => by
      simpa only [Real.norm_eq_abs,abs_sq] using norm_weighted_sum_sq w (fun i => f i z)))
  refine ⟨ho,(integral_mono ho hs (fun z => norm_weighted_sum_sq w (fun i => f i z))).trans ?_⟩
  rw [integral_const_mul,integral_finsetSum]
  · simp only [integral_const_mul]
    have hh := Finset.sum_le_sum (fun (i : I) (_ : i∈Finset.univ) =>
      mul_le_mul_of_nonneg_left (hB i) (abs_nonneg (w i)))
    have h := mul_le_mul_of_nonneg_left hh hw0
    simpa only [←Finset.sum_mul,pow_two,mul_assoc] using h
  · intro i _
    exact (hi i).const_mul _
end LogConcaveSampling.RMSIntegral

end

end

end

end OAI
end

section
-- module Solutions.OAIQ048_LC.LogConcave_Numerics_ChainTaylor
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
namespace LogConcaveSampling.RMSIntegral
open MeasureTheory
open scoped BigOperators

variable {I Ω E : Type*} [Fintype I] [MeasurableSpace Ω]
  [NormedAddCommGroup E] [NormedSpace ℝ E] {μ : Measure Ω}

lemma weighted_sum_sq_varying (w : I → ℝ) (f : I → Ω → E) (B : I → ℝ)
    (hm : ∀i,AEStronglyMeasurable (f i) μ)
    (hi : ∀i,Integrable (fun y => ‖f i y‖^2) μ)
    (hB : ∀i,(∫y,‖f i y‖^2 ∂μ)≤B i) :
    Integrable (fun y => ‖∑i,w i • f i y‖^2) μ ∧
      (∫y,‖∑i,w i • f i y‖^2 ∂μ)≤(∑i,|w i|)*(∑i,|w i| *B i) := by
  have hw0 : 0≤∑i,|w i| := Finset.sum_nonneg (fun _ _ => abs_nonneg _)
  have hs : Integrable (fun y => (∑i,|w i|)*(∑i,|w i| *‖f i y‖^2)) μ := by
    apply Integrable.const_mul
    exact integrable_finsetSum _ (fun i _ => (hi i).const_mul _)
  have hmeas : AEStronglyMeasurable (fun y => ‖∑i,w i • f i y‖^2) μ := by
    have h := (Finset.aestronglyMeasurable_sum Finset.univ
      (fun i _ => (hm i).const_smul (w i))).norm.pow 2
    convert h using 1
    all_goals try with_reducible_and_instances rfl
    ext y
    simp only [Finset.sum_apply,Pi.smul_apply,Pi.pow_apply]
  have ho : Integrable (fun y => ‖∑i,w i • f i y‖^2) μ :=
    hs.mono' hmeas (Filter.Eventually.of_forall (fun y => by
      simpa only [Real.norm_eq_abs,abs_sq] using norm_weighted_sum_sq w (fun i => f i y)))
  refine ⟨ho,(integral_mono ho hs (fun y => norm_weighted_sum_sq w (fun i => f i y))).trans ?_⟩
  rw [integral_const_mul,integral_finsetSum]
  · simp only [integral_const_mul]
    exact mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun i _ =>
      mul_le_mul_of_nonneg_left (hB i) (abs_nonneg _))) hw0
  · exact fun i _ => (hi i).const_mul _
end LogConcaveSampling.RMSIntegral

end

end

end

end OAI
end

section
-- module Solutions.OAIQ048_LC.LogConcave_Analysis_CenteringPotential
attribute [-instance] _root_.OAI.LogConcaveSampling.LowerBound.couplingLaw_probability _root_.OAI.LogConcaveSampling.LowerBound.remainingHaar_probability _root_.OAI.LogConcaveSampling.LowerBound.roundRandomLaw_probability _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_invInvariant _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_isHaar _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_probability _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_rightInvariant _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_compactSpace _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_measurableInv _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_measurableMul _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_secondCountable _root_.OAI.LogConcaveSampling.MeanTree.instIsProbabilityMeasureRowTapeRowLaw _root_.OAI.LogConcaveSampling.OracleCompiler.topSeedLaw_probability _root_.OAI.LogConcaveSampling.noiseKernel_markov
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
namespace LogConcaveSampling
open Set MeasureTheory
open scoped Classical BigOperators NNReal RealInnerProductSpace
open TensorEnergy Quadrature

lemma gradient_gaussianPotential {d : ℕ} (y : Point d) :
    gradient (fun z : Point d => ‖z‖^2/2) y=y := by
  ext i
  rw [←directional_basis_gradient,directional_gaussianPotential]
  simp [EuclideanSpace.basisFun_apply,PiLp.inner_apply]

lemma gaussianPotential_gradient_lipschitz (d : ℕ) :
    LipschitzWith 1 (gradient (fun z : Point d => ‖z‖^2/2)) := by
  have he : gradient (fun z : Point d => ‖z‖^2/2)=id := funext gradient_gaussianPotential
  rw [he]
  exact LipschitzWith.id

lemma centeringPotential_gradient_lipschitz {d : ℕ} {F : Point d → ℝ} {lam : ℝ≥0}
    (hF : Primitive F lam) (x : Point d) {r T : ℝ} (hr : 0 < r)
    (hl : (lam:ℝ)*r^2≤1/2) (hT0 : 0≤T) (hT1 : T<1) :
    LipschitzWith (centeringGradientBound lam r T (by positivity))
      (gradient (centeringPotential F x r T)) :=
  productPotential_gradient_lipschitz
    ((interpolationPotential_smooth hF x hr.le hl hT0 hT1).differentiable (by simp))
    ((gaussianPotential_polySmooth d).smooth.differentiable (by simp))
    (interpolationPotential_gradient_lipschitz hF x hr.le hl hT0 hT1)
    (gaussianPotential_gradient_lipschitz d)

lemma centeringScore_scaled_bound {d : ℕ} {F : Point d → ℝ} {lam : ℝ≥0}
    (hF : Primitive F lam) (x : Point d) {r T : ℝ} (hr : 0 < r)
    (hlam : 0<lam) (hl : (lam:ℝ)*r^2≤1/2) (hT0 : 0≤T) (hT1 : T<1) :
    ∀k,0<k → ∀y,AllSplitBound
      (spatialTensor (scoreField (centeringPotential F x r T)) (List.finRange k) y)
      ((2+normalizedTensorMajorant (k+1) (1-T^2))*1^k) := by
  intro k hk y
  simpa only [centeringPotential,one_pow,mul_one] using
    centeringScore_allSplit hF x hr hlam hl hT0 hT1 hk y

end LogConcaveSampling

end

end

end

end OAI
end

section
-- module Solutions.OAIQ048_LC.LogConcave_JetEstimates_FlowJetMajorant
attribute [-instance] _root_.OAI.LogConcaveSampling.LowerBound.couplingLaw_probability _root_.OAI.LogConcaveSampling.LowerBound.remainingHaar_probability _root_.OAI.LogConcaveSampling.LowerBound.roundRandomLaw_probability _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_invInvariant _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_isHaar _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_probability _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_rightInvariant _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_compactSpace _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_measurableInv _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_measurableMul _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_secondCountable _root_.OAI.LogConcaveSampling.MeanTree.instIsProbabilityMeasureRowTapeRowLaw _root_.OAI.LogConcaveSampling.OracleCompiler.topSeedLaw_probability _root_.OAI.LogConcaveSampling.noiseKernel_markov
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
namespace LogConcaveSampling.TensorEnergy
open Set Function
open scoped Classical BigOperators RealInnerProductSpace

lemma flowJetMajorant_nonneg (A : ℕ → ℝ) (hA : ∀k,0≤A k) (n : ℕ) :
    0≤flowJetMajorant A hA n := (smoothTensorCurve_bounds A hA n).choose_spec.1

lemma flowCorrectionMajorant_nonneg (A : ℕ → ℝ) (hA : ∀k,0≤A k) (n : ℕ) :
    0≤flowCorrectionMajorant A hA n :=
  Finset.sum_nonneg (fun _ _ => mul_nonneg (hA _) (Finset.prod_nonneg (fun _ _ => flowJetMajorant_nonneg A hA _)))

lemma multilinearTensor_sub {d n : ℕ} (f g : Point d → Point d)
    (hf : ContDiff ℝ (⊤:ℕ∞) f) (hg : ContDiff ℝ (⊤:ℕ∞) g) (y : Point d) :
    multilinearTensor (iteratedFDeriv ℝ n (fun z => f z-g z) y)=
      multilinearTensor (iteratedFDeriv ℝ n f y)-multilinearTensor (iteratedFDeriv ℝ n g y) := by
  change multilinearTensor (iteratedFDeriv ℝ n (f-g) y)=_
  rw [iteratedFDeriv_sub_apply (hf.contDiffAt.of_le (by exact_mod_cast (le_top : (n:ℕ∞)≤⊤)))
    (hg.contDiffAt.of_le (by exact_mod_cast (le_top : (n:ℕ∞)≤⊤)))]
  ext c
  simp only [multilinearTensor,sub_apply,inner_sub_right,Pi.sub_apply]

theorem smoothTensorCurve_correction {d n : ℕ} (hn : 0<n) (A : ℕ → ℝ) (hA : ∀k,0≤A k)
    {R b η : ℝ} (hR : 0<R) (hR1 : R≤1) (hb : 0≤b) (hb1 : b≤1) (hη : 0≤η)
    (X : ℝ × Point d → Point d) (V : ℝ → Point d → Point d)
    (hX : SmoothTensorCurve d A R b X V)
    (hv : ∀k u,u∈Icc 0 b → ∀z,AllSplitBound
      (multilinearTensor (iteratedFDeriv ℝ k (V u) z)) (η*A k/R^(k-1)))
    {t : ℝ} (ht : t∈Icc 0 b) (y : Point d) :
    AllSplitBound (multilinearTensor (iteratedFDeriv ℝ n (fun z => X (t,z)-z) y))
      (η*flowCorrectionMajorant A hA n/R^(n-1)) := by
  let T (u : ℝ) := multilinearTensor (iteratedFDeriv ℝ n (fun z => X (u,z)) y)-
    multilinearTensor (iteratedFDeriv ℝ n (id : Point d → Point d) y)
  let D (u : ℝ) := multilinearTensor (iteratedFDeriv ℝ n (fun z => V u (X (u,z))) y)
  let M (k : ℕ) := (η*A k)/R^(k-1)
  let N (k : ℕ) := flowJetMajorant A hA k/R^(k-1)
  have hM (k : ℕ) : 0≤M k := by exact div_nonneg (mul_nonneg hη (hA k)) (pow_nonneg hR.le _)
  have hN (k : ℕ) : 0≤N k := div_nonneg (flowJetMajorant_nonneg A hA _) (pow_nonneg hR.le _)
  have hflow (k : ℕ) (u : ℝ) (hu : u∈Icc 0 b) :
      AllSplitBound (multilinearTensor (iteratedFDeriv ℝ k (fun z => X (u,z)) y)) (N k) :=
    (smoothTensorCurve_bounds A hA k).choose_spec.2 d R b X V hR hR1 hb hb1 hX u hu y
  have hbound (u : ℝ) (hu : u∈Ico 0 b) :
      AllSplitBound (D u) (η*flowCorrectionMajorant A hA n/R^(n-1)) := by
    have hs : ContDiff ℝ (⊤:ℕ∞) (fun z => X (u,z)) := hX.smooth.comp (contDiff_const.prodMk contDiff_id)
    have hvs := (hX.velocity_smooth u ⟨hu.1,hu.2.le⟩).contDiffAt (x:=X (u,y))
    have he := iteratedFDeriv_comp_allSplit y
      (hs.contDiffAt.of_le (by exact_mod_cast (le_top : (n:ℕ∞)≤⊤)))
      (hvs.of_le (by exact_mod_cast (le_top : (n:ℕ∞)≤⊤))) M N hM hN
      (fun k hk => hv k u ⟨hu.1,hu.2.le⟩ (X (u,y)))
      (fun k hk => hflow k u ⟨hu.1,hu.2.le⟩)
    have heq : (∑c : OrderedFinpartition n,M c.length*∏i,N (c.partSize i))=
        η*flowCorrectionMajorant A hA n/R^(n-1) := by
      dsimp only [M,N]
      rw [partition_sum_scale hn (fun k => η*A k) (flowJetMajorant A hA) R]
      simp only [flowCorrectionMajorant,←Finset.mul_sum,mul_assoc]
    rw [heq] at he
    exact he
  have hinit : AllSplitBound (T 0) 0 := by
    have he : (fun z => X (0,z))=(id : Point d → Point d) := funext hX.initial
    dsimp only [T]
    rw [he,sub_self]
    exact allSplitBound_zero
  have hpos : 0≤η*flowCorrectionMajorant A hA n/R^(n-1) :=
    div_nonneg (mul_nonneg hη (flowCorrectionMajorant_nonneg A hA n)) (pow_nonneg hR.le _)
  have hg := allSplit_gronwall (T:=T) (D:=D) (K:=0)
    ((spatialTensor_continuous hX.smooth y).sub continuous_const).continuousOn
    (fun u hu => ((spatialTensor_time_deriv hX.smooth (V u) u
      (hX.equation u ⟨hu.1,hu.2.le⟩) y).sub_const _).hasDerivWithinAt)
    (le_refl (0:ℝ)) hpos (le_refl (0:ℝ)) hinit
    (fun u hu => by simpa only [zero_mul,zero_add] using hbound u hu) ht
  simp only [gronwallBound_K0,zero_add,sub_zero] at hg
  have hfinal := hg.mono (mul_nonneg hpos ht.1) (mul_le_of_le_one_right hpos (ht.2.trans hb1))
  have hs : ContDiff ℝ (⊤:ℕ∞) (fun z => X (t,z)) := hX.smooth.comp (contDiff_const.prodMk contDiff_id)
  rw [multilinearTensor_sub (fun z => X (t,z)) (fun z => z) hs contDiff_id]
  exact hfinal
end LogConcaveSampling.TensorEnergy

end

end

end

end OAI
end

section
-- module Solutions.OAIQ048_LC.LogConcave_Sampling_HarmonicKernel
attribute [-instance] _root_.OAI.LogConcaveSampling.LowerBound.couplingLaw_probability _root_.OAI.LogConcaveSampling.LowerBound.remainingHaar_probability _root_.OAI.LogConcaveSampling.LowerBound.roundRandomLaw_probability _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_invInvariant _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_isHaar _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_probability _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_rightInvariant _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_compactSpace _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_measurableInv _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_measurableMul _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_secondCountable _root_.OAI.LogConcaveSampling.MeanTree.instIsProbabilityMeasureRowTapeRowLaw _root_.OAI.LogConcaveSampling.OracleCompiler.topSeedLaw_probability _root_.OAI.LogConcaveSampling.noiseKernel_markov
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
namespace LogConcaveSampling
open scoped Classical BigOperators RealInnerProductSpace
open TensorEnergy

lemma harmonicKernel_strong {d : ℕ} (H : Point d → ℝ) (u : Point d) :
    tensorAdjoint H (EuclideanSpace.basisFun (Fin d) ℝ)
      (fun i y => inner ℝ u (harmonicKernel d y (EuclideanSpace.basisFun (Fin d) ℝ i)))=
      fun y => inner ℝ u (-gradient H y) := by
  funext y
  simp only [tensorAdjoint,adjointCoordinate,harmonicKernel,neg_apply,
    ContinuousLinearMap.id_apply,inner_neg_right]
  simp only [directional,fderiv_fun_const,Pi.zero_apply,zero_apply,neg_zero,zero_add]
  change (∑i : Fin d,directional (EuclideanSpace.basisFun (Fin d) ℝ i) H y*
    (-inner ℝ u (EuclideanSpace.basisFun (Fin d) ℝ i)))= -inner ℝ u (gradient H y)
  have hcu (i : Fin d) : inner ℝ u (EuclideanSpace.basisFun (Fin d) ℝ i)=u i := by
    rw [real_inner_comm]
    exact inner_basis_coordinate u i
  simp only [directional_basis_gradient,hcu,mul_neg,Finset.sum_neg_distrib]
  congr 1

lemma harmonicSkew_field {d : ℕ} {H : Point d → ℝ} (hH : Differentiable ℝ H)
    (y : Point (d+d)) :
    productPointEquiv d d (skewLieField (productPotential H (fun z : Point d => ‖z‖^2/2))
      (harmonicSkew d) y)=((productPointEquiv d d y).2,-gradient H (productPointEquiv d d y).1) := by
  have ha (z : Point d) : (harmonicKernel d z).adjoint=-(ContinuousLinearMap.id ℝ (Point d)) := by
    change ContinuousLinearMap.adjoint (-(ContinuousLinearMap.id ℝ (Point d)))=_
    rw [map_neg,ContinuousLinearMap.adjoint_id]
  have h := jointSkew_field (K:=harmonicKernel d) (m:=fun z => -gradient H z)
    hH (fun _ _ => by simpa only [harmonicKernel] using (differentiable_const _)) (harmonicKernel_strong H) 1 y
  simpa only [harmonicSkew,skewCenteringField,ha,inv_one,one_smul,neg_smul,
    neg_apply,ContinuousLinearMap.id_apply,neg_neg] using h
end LogConcaveSampling

end

end

section

noncomputable section
namespace LogConcaveSampling
open scoped Classical BigOperators RealInnerProductSpace
open TensorEnergy

lemma harmonicKernel_spatial_bound {d n : ℕ} (y : Point d) :
    AllSplitBound (spatialTensor (fun c z => matrixArray d (harmonicKernel d z) c)
      (List.finRange n) y) 1 := by
  have hh := ((allSplitBound_spatial_delta (d:=d) (List.finRange n) (by simp)).reindex
    (Equiv.sumAssoc (Fin n) Unit Unit)).abs_const_mul (-1)
  have he : spatialTensor (fun c z => matrixArray d (harmonicKernel d z) c) (List.finRange n) y=
      fun c => (-1:ℝ)*(if List.finRange n=[] then
        (if c (.inr (.inl ()))=c (.inr (.inr ())) then (1:ℝ) else 0) else 0) := by
    funext c
    unfold spatialTensor
    simp only [matrixArray_apply,harmonicKernel,neg_apply,ContinuousLinearMap.id_apply,
      inner_neg_right,EuclideanSpace.basisFun_inner,JetCalculus.jet_const]
    by_cases hn : List.finRange n=[] <;> simp [hn,EuclideanSpace.basisFun_apply,eq_comm]
    split_ifs <;> norm_num
  rw [he]
  apply hh.mono
  · split_ifs <;> norm_num
  · split_ifs <;> norm_num

lemma harmonicSkew_polySmooth (d : ℕ) : ∀c,PolySmooth (harmonicSkew d c) :=
  jointSkew_polySmooth (fun _ _ => PolySmooth.const _) 1

lemma harmonicSkew_scaled_bound (d : ℕ) : ∀k y,
    AllSplitBound (spatialTensor (harmonicSkew d) (List.finRange k) y) ((2:ℝ)*1*1^k) := by
  intro k y
  simpa only [harmonicSkew,inv_one,abs_one,mul_one,one_pow] using
    jointSkew_spatial_bound (n:=k) (K:=harmonicKernel d) (fun _ => by simpa only [harmonicKernel] using (contDiff_const (c:=_)))
      (by norm_num : (0:ℝ)≤1) harmonicKernel_spatial_bound 1 y
end LogConcaveSampling

end

end

end

end OAI
end

section
-- module Solutions.OAIQ048_LC.LogConcave_Sampling_TransportCorrectionMajorant
attribute [-instance] _root_.OAI.LogConcaveSampling.LowerBound.couplingLaw_probability _root_.OAI.LogConcaveSampling.LowerBound.remainingHaar_probability _root_.OAI.LogConcaveSampling.LowerBound.roundRandomLaw_probability _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_invInvariant _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_isHaar _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_probability _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_rightInvariant _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_compactSpace _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_measurableInv _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_measurableMul _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_secondCountable _root_.OAI.LogConcaveSampling.MeanTree.instIsProbabilityMeasureRowTapeRowLaw _root_.OAI.LogConcaveSampling.OracleCompiler.topSeedLaw_probability _root_.OAI.LogConcaveSampling.noiseKernel_markov
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
namespace LogConcaveSampling
open Set Function TensorEnergy
open scoped NNReal BigOperators

lemma probabilityVelocity_iterated_small {d n : ℕ} {F : Point d → ℝ} {lam : ℝ≥0}
    (hF : Primitive F lam) (x : Point d) {r ρ R : ℝ} (hr : 0 < r)
    (hlam : 0<lam) (hl : (lam:ℝ)*r^2≤1/2) (hρ0 : 0≤ρ) (hρ1 : ρ<1)
    (hR : 0<R) (ha : R^2≤1-ρ^2) (y : Point d) :
    AllSplitBound (multilinearTensor (iteratedFDeriv ℝ n (probabilityVelocity F x r ρ) y))
      (((lam:ℝ)*r^2)*normalizedTensorMajorant (n+1) 1/R^(n-1)) := by
  have hh := (conditionalMean_iterated_uniform_split hF x hr hlam hl hρ0 hρ1 hR ha y (n:=n)).abs_const_mul (-r)
  rw [←multilinearTensor_const_smul (-r) _
    (conditionalFieldMean_smooth hF x hr.le hl hρ0 hρ1)] at hh
  change AllSplitBound _ _ at hh
  rw [abs_neg,abs_of_pos hr] at hh
  convert hh using 1 <;> first | rfl | ring

lemma transportCorrectionMajorant_nonneg (n : ℕ) : 0≤transportCorrectionMajorant n :=
  flowCorrectionMajorant_nonneg _ _ _

theorem probabilityTransport_correction_split {d n : ℕ} (hn : 0<n)
    {F : Point d → ℝ} {lam : ℝ≥0} (hF : Primitive F lam) (x : Point d) {r R T : ℝ}
    (hr : 0 < r) (hlam : 0<lam) (hl : (lam:ℝ)*r^2≤1/2)
    (hR : 0<R) (hRT : R^2≤1-T^2) (hT0 : 0≤T) (hT1 : T<1)
    (s t : Icc (0:ℝ) T) (y : Point d) :
    AllSplitBound (multilinearTensor (iteratedFDeriv ℝ n
      (fun z => probabilityTransport hF x hr.le hl hT0 hT1 s t z-z) y))
      (((lam:ℝ)*r^2)*transportCorrectionMajorant n/R^(n-1)) := by
  let a : ℝ := (t:ℝ)-(s:ℝ)
  let q (u : ℝ) := (s:ℝ)+a*u
  have hq (u : ℝ) (hu : u∈Icc (0:ℝ) 1) : q u∈Icc 0 T := by
    dsimp [q,a]
    constructor
    · nlinarith [s.2.1,t.2.1,mul_nonneg s.2.1 (sub_nonneg.mpr hu.2),mul_nonneg t.2.1 hu.1]
    · nlinarith [s.2.2,t.2.2,mul_nonneg (sub_nonneg.mpr s.2.2) (sub_nonneg.mpr hu.2),
        mul_nonneg (sub_nonneg.mpr t.2.2) hu.1]
  have ha : |a|≤1 := (abs_le).mpr ⟨by dsimp [a]; linarith [t.2.1,s.2.2],by dsimp [a]; linarith [t.2.2,s.2.1]⟩
  let X (p : ℝ × Point d) := spatialTransport hF x hr.le hl hT0 hT1 s (q p.1,p.2)
  let V (u : ℝ) (z : Point d) := a • probabilityVelocity F x r (q u) z
  have hVX : TensorEnergy.SmoothTensorCurve d (fun k => normalizedTensorMajorant (k+1) 1) R 1 X V := by
    constructor
    · exact (spatialTransport_smooth hF x hr.le hl hT0 hT1 s).comp
        ((contDiff_const.add (contDiff_const.mul contDiff_fst)).prodMk contDiff_snd)
    · intro z
      dsimp [X,q]
      simp only [mul_zero,add_zero]
      exact spatialTransport_initial hF x hr.le hl hT0 hT1 s z
    · intro u hu z
      have hd := (spatialTransport_deriv hF x hr.le hl hT0 hT1 s (hq u hu) z).scomp u
        ((hasDerivAt_const u (s:ℝ)).add ((hasDerivAt_const u a).mul (hasDerivAt_id u)))
      simpa only [zero_mul,one_mul,mul_one,zero_add,X,V,q,Function.comp_def] using hd
    · intro u hu
      exact (contDiff_const (c:=a)).smul ((contDiff_const (c:=(-r:ℝ))).smul
        (conditionalFieldMean_smooth hF x hr.le hl (hq u hu).1 ((hq u hu).2.trans_lt hT1)))
    · intro k u hu z
      have huT := hq u hu
      have hρ : R^2≤1-(q u)^2 := by nlinarith [mul_nonneg (sub_nonneg.mpr huT.2) (add_nonneg hT0 huT.1)]
      have hh := (probabilityVelocity_iterated_split hF x hr hlam hl huT.1
        (huT.2.trans_lt hT1) hR hρ z (n:=k)).abs_const_mul a
      have hvs : ContDiff ℝ (⊤:ℕ∞) (probabilityVelocity F x r (q u)) :=
        (contDiff_const (c:=(-r:ℝ))).smul (conditionalFieldMean_smooth hF x hr.le hl huT.1 (huT.2.trans_lt hT1))
      rw [←TensorEnergy.multilinearTensor_const_smul a (probabilityVelocity F x r (q u)) hvs z] at hh
      apply hh.mono (mul_nonneg (abs_nonneg _) (div_nonneg (normalizedTensorMajorant_nonneg _ _) (pow_nonneg hR.le _)))
      exact mul_le_of_le_one_left (div_nonneg (normalizedTensorMajorant_nonneg _ _) (pow_nonneg hR.le _)) ha
  have hv (k : ℕ) (u : ℝ) (hu : u∈Icc (0:ℝ) 1) (z : Point d) :
      AllSplitBound (multilinearTensor (iteratedFDeriv ℝ k (V u) z))
        (((lam:ℝ)*r^2)*normalizedTensorMajorant (k+1) 1/R^(k-1)) := by
    have huT := hq u hu
    have hρ : R^2≤1-(q u)^2 := by nlinarith [mul_nonneg (sub_nonneg.mpr huT.2) (add_nonneg hT0 huT.1)]
    have hh := (probabilityVelocity_iterated_small hF x hr hlam hl huT.1
      (huT.2.trans_lt hT1) hR hρ z (n:=k)).abs_const_mul a
    have hvs : ContDiff ℝ (⊤:ℕ∞) (probabilityVelocity F x r (q u)) :=
      (contDiff_const (c:=(-r:ℝ))).smul (conditionalFieldMean_smooth hF x hr.le hl huT.1 (huT.2.trans_lt hT1))
    rw [←multilinearTensor_const_smul a (probabilityVelocity F x r (q u)) hvs z] at hh
    have hp : 0≤((lam:ℝ)*r^2)*normalizedTensorMajorant (k+1) 1/R^(k-1) :=
      div_nonneg (mul_nonneg (mul_nonneg lam.coe_nonneg (sq_nonneg r))
        (normalizedTensorMajorant_nonneg _ _)) (pow_nonneg hR.le _)
    exact hh.mono (mul_nonneg (abs_nonneg _) hp) (mul_le_of_le_one_left hp ha)
  have hR1 : R≤1 := by nlinarith [sq_nonneg T]
  have hh := smoothTensorCurve_correction hn (fun k => normalizedTensorMajorant (k+1) 1)
    (fun k => normalizedTensorMajorant_nonneg _ _) hR hR1 (by norm_num : (0:ℝ)≤1)
    le_rfl (mul_nonneg lam.coe_nonneg (sq_nonneg r)) X V hVX hv (t:=1) ⟨by norm_num,le_rfl⟩ y
  have he : (fun z => X (1,z))=probabilityTransport hF x hr.le hl hT0 hT1 s t := by
    funext z
    dsimp [X,q,a]
    rw [mul_one,add_sub_cancel]
    exact spatialTransport_eq hF x hr.le hl hT0 hT1 s t z
  have he' (z : Point d) : X (1,z)=probabilityTransport hF x hr.le hl hT0 hT1 s t z := congrFun he z
  simp_rw [he'] at hh
  exact hh
end LogConcaveSampling

end

end

section

noncomputable section
namespace LogConcaveSampling
open Set MeasureTheory
open scoped Classical BigOperators NNReal RealInnerProductSpace
open TensorEnergy

lemma vectorArray_spatial {d n : ℕ} {f : Point d → Point d}
    (hf : ContDiff ℝ (⊤:ℕ∞) f) (y : Point d) :
    spatialTensor (vectorArray f) (List.finRange n) y=
      fun c => multilinearTensor (iteratedFDeriv ℝ n f y) (c ∘ Equiv.sumComm Unit (Fin n)) := by
  funext c
  let L := innerSL ℝ (EuclideanSpace.basisFun (Fin d) ℝ (c (.inr ())))
  change JetCalculus.jet _ _ (L ∘ f) y=_
  rw [JetCalculus.jet_finRange_eq_iteratedFDeriv (L.contDiff.comp hf),
    L.iteratedFDeriv_comp_left hf.contDiffAt (by exact_mod_cast (le_top : (n:ℕ∞)≤⊤))]
  rfl

lemma vectorArray_polySmooth {d : ℕ} {f : Point d → Point d} {L : ℝ≥0}
    (hf : ContDiff ℝ (⊤:ℕ∞) f) (hL : LipschitzWith L f)
    (M : ℕ → ℝ) (hM : ∀n,0≤M n)
    (hB : ∀n,0<n → ∀y,AllSplitBound (multilinearTensor (iteratedFDeriv ℝ n f y)) (M n))
    (c : Unit → Fin d) : PolySmooth (vectorArray f c) := by
  apply PolySmooth.of_basis_growth ((innerSL ℝ (EuclideanSpace.basisFun (Fin d) ℝ (c ()))).contDiff.comp hf)
  intro l
  by_cases hl : l=[]
  · subst l
    exact growth_of_lipschitz ((innerSL ℝ _).lipschitz.comp hL)
  · have hn : 0<l.length := List.length_pos_iff.mpr hl
    apply growth_of_bounded (hM l.length)
    intro y
    have hh := (hB l.length hn y).reindex (Equiv.sumComm Unit (Fin l.length))
    rw [←vectorArray_spatial hf y] at hh
    have hb := hh.entry_le (hM _) (by simp only [Fintype.card_sum,Fintype.card_fin,Fintype.card_unique]; omega)
      (Sum.elim l.get c)
    change |JetCalculus.jet ((EuclideanSpace.basisFun (Fin d) ℝ) ∘ l.get)
      (List.finRange l.length) (vectorArray f c) y|≤_ at hb
    rw [←JetCalculus.jet_map,List.map_get_finRange] at hb
    exact hb

lemma vectorArray_energy {d n : ℕ} {H : Point d → ℝ} {f : Point d → Point d}
    (hH : Continuous H) (ht : HasGaussianLowerTail H) (hf : ContDiff ℝ (⊤:ℕ∞) f)
    (hp : ∀c,PolySmooth (vectorArray f c)) (hn : 0<n) {M : ℝ}
    (hB : ∀y,AllSplitBound (multilinearTensor (iteratedFDeriv ℝ n f y)) M) :
    spatialEnergy (vectorArray f) n (gibbs H)≤d*M^2 := by
  let := probability_gibbs_of_gaussianTail hH ht
  apply spatialEnergy_from_split hH ht _ hp hn
  intro y
  rw [vectorArray_spatial hf y]
  exact (hB y).reindex (Equiv.sumComm Unit (Fin n))
end LogConcaveSampling

end

end

section

noncomputable section
namespace LogConcaveSampling
open Set MeasureTheory
open scoped Classical BigOperators NNReal RealInnerProductSpace
open TensorEnergy

lemma probabilityTransport_lipschitz {d : ℕ} {F : Point d → ℝ} {lam : ℝ≥0}
    (hF : Primitive F lam) (x : Point d) {r T : ℝ} (hr : 0 ≤ r)
    (hl : (lam:ℝ)*r^2≤1/2) (hT0 : 0≤T) (hT1 : T<1) (s t : Icc (0:ℝ) T) :
    LipschitzWith ⟨Real.exp (((Real.pi^2/2)*(lam:ℝ)*r^2)*|(t:ℝ)-(s:ℝ)|),(Real.exp_pos _).le⟩
      (probabilityTransport hF x hr hl hT0 hT1 s t) :=
  GlobalODE.flow_lipschitz _ _ s t

lemma probabilityTransport_infty {d : ℕ} {F : Point d → ℝ} {lam : ℝ≥0}
    (hF : Primitive F lam) (x : Point d) {r T : ℝ} (hr : 0 ≤ r)
    (hl : (lam:ℝ)*r^2≤1/2) (hT0 : 0≤T) (hT1 : T<1) (s t : Icc (0:ℝ) T) :
    ContDiff ℝ (⊤:ℕ∞) (probabilityTransport hF x hr hl hT0 hT1 s t) :=
  contDiff_infty.mpr (probabilityTransport_contDiff hF x hr hl hT0 hT1 s t)

lemma probabilityCorrection_polySmooth {d : ℕ} {F : Point d → ℝ} {lam : ℝ≥0}
    (hF : Primitive F lam) (x : Point d) {r R T : ℝ}
    (hr : 0 < r) (hlam : 0<lam) (hl : (lam:ℝ)*r^2≤1/2)
    (hR : 0<R) (hRT : R^2≤1-T^2) (hT0 : 0≤T) (hT1 : T<1)
    (s t : Icc (0:ℝ) T) :
    ∀c,PolySmooth (vectorArray (fun z => probabilityTransport hF x hr.le hl hT0 hT1 s t z-z) c) :=
  vectorArray_polySmooth ((probabilityTransport_infty hF x hr.le hl hT0 hT1 s t).sub contDiff_id)
    ((probabilityTransport_lipschitz hF x hr.le hl hT0 hT1 s t).sub LipschitzWith.id)
    (fun n => ((lam:ℝ)*r^2)*transportCorrectionMajorant n/R^(n-1))
    (fun n => div_nonneg (mul_nonneg (mul_nonneg lam.2 (sq_nonneg r)) (transportCorrectionMajorant_nonneg n))
      (pow_nonneg hR.le _))
    (fun _ hn => probabilityTransport_correction_split hn hF x hr hlam hl hR hRT hT0 hT1 s t)

lemma probabilityCorrection_energy {d n : ℕ} {F : Point d → ℝ} {lam : ℝ≥0}
    (hF : Primitive F lam) (x : Point d) {r R T : ℝ}
    (hr : 0 < r) (hlam : 0<lam) (hl : (lam:ℝ)*r^2≤1/2)
    (hR : 0<R) (hRT : R^2≤1-T^2) (hT0 : 0≤T) (hT1 : T<1)
    (s t : Icc (0:ℝ) T) (u : Icc (0:ℝ) T) (hn : 0<n) :
    spatialEnergy (vectorArray (fun z => probabilityTransport hF x hr.le hl hT0 hT1 s t z-z)) n
      (gibbs (interpolationPotential F x r u))≤
      d*((lam:ℝ)*r^2)^2*(transportCorrectionMajorant n/R^(n-1))^2 := by
  have hh := vectorArray_energy
    (interpolationPotential_smooth hF x hr.le hl u.2.1 (u.2.2.trans_lt hT1)).continuous
    (interpolationPotential_lowerTail hF x hr.le (by linarith) u.2.1 (u.2.2.trans_lt hT1))
    ((probabilityTransport_infty hF x hr.le hl hT0 hT1 s t).sub contDiff_id)
    (probabilityCorrection_polySmooth hF x hr hlam hl hR hRT hT0 hT1 s t) hn
    (probabilityTransport_correction_split hn hF x hr hlam hl hR hRT hT0 hT1 s t)
  exact hh.trans_eq (by ring)

lemma jointCorrectionArray_energy {d n : ℕ} {F : Point d → ℝ} {lam : ℝ≥0}
    (hF : Primitive F lam) (x : Point d) {r R T : ℝ}
    (hr : 0 < r) (hlam : 0<lam) (hl : (lam:ℝ)*r^2≤1/2)
    (hR : 0<R) (hRT : R^2≤1-T^2) (hT0 : 0≤T) (hT1 : T<1)
    (s t : Icc (0:ℝ) T) (u : Icc (0:ℝ) T) (hn : 0<n) :
    spatialEnergy (jointCorrectionArray (fun z => probabilityTransport hF x hr.le hl hT0 hT1 s t z-z)) n
      (gibbs (centeringPotential F x r u))≤
      d*((lam:ℝ)*r^2)^2*(transportCorrectionMajorant n/R^(n-1))^2 := by
  have hH := interpolationPotential_polySmooth hF x hr hlam hl u.2.1 (u.2.2.trans_lt hT1)
  have ht := interpolationPotential_lowerTail hF x hr.le (by linarith) u.2.1 (u.2.2.trans_lt hT1)
  let := probability_gibbs_of_gaussianTail hH.smooth.continuous ht
  dsimp only [jointCorrectionArray,centeringPotential]
  rw [spatialEnergy_leftLift hH.smooth.continuous _
    (fun c => (probabilityCorrection_polySmooth hF x hr hlam hl hR hRT hT0 hT1 s t c).smooth)]
  exact probabilityCorrection_energy hF x hr hlam hl hR hRT hT0 hT1 s t u hn
end LogConcaveSampling

end

end

section

noncomputable section
namespace LogConcaveSampling
open Set MeasureTheory
open scoped Classical BigOperators NNReal RealInnerProductSpace
open TensorEnergy

lemma normalizedTensorMajorant_inv_scale {k : ℕ} {R a : ℝ}
    (hR : 0<R) (hR1 : R≤1) (ha : R^2≤a) :
    normalizedTensorMajorant (k+1) a≤normalizedTensorMajorant (k+1) 1*(R⁻¹)^k := by
  have hh := normalizedTensorMajorant_scale (n:=k+1) hR ha
  have hp : R^k≤R^(k+1-2) := pow_le_pow_of_le_one hR.le hR1 (by omega)
  apply hh.trans
  rw [inv_pow,←div_eq_mul_inv]
  exact div_le_div_of_nonneg_left (normalizedTensorMajorant_nonneg _ _) (pow_pos hR _) hp

lemma inv_scale_pred {R A : ℝ} (hR : 0<R) (hR1 : R≤1) (hA : 0≤A) (k : ℕ) :
    A/R^(k-1)≤A*(R⁻¹)^k := by
  rw [inv_pow,←div_eq_mul_inv]
  exact div_le_div_of_nonneg_left hA (pow_pos hR _) (pow_le_pow_of_le_one hR.le hR1 (by omega))

lemma centeringPotential_gradient_uniform {d : ℕ} {F : Point d → ℝ} {lam : ℝ≥0}
    (hF : Primitive F lam) (x : Point d) {r T : ℝ}
    (hr : 0 < r) (hl : (lam:ℝ)*r^2≤1/2) (hT0 : 0≤T) (hT1 : T<1) :
    LipschitzWith harmonicGradientBound (gradient (centeringPotential F x r T)) := by
  apply (centeringPotential_gradient_lipschitz hF x hr hl hT0 hT1).weaken
  change (1+‖r*T‖*((Real.pi^2/2)*T*((lam:ℝ)*r)))+1≤2+Real.pi^2
  rw [Real.norm_eq_abs,abs_of_nonneg (mul_nonneg hr.le hT0)]
  have hl0 : 0≤(lam:ℝ)*r^2 := mul_nonneg lam.2 (sq_nonneg r)
  have hT : T^2≤1 := by nlinarith
  have hb : (lam:ℝ)*r^2*T^2≤1/2 := by
    calc
      _ ≤ (lam:ℝ)*r^2*1 := mul_le_mul_of_nonneg_left hT hl0
      _ ≤ _ := by simpa only [mul_one] using hl
  have hp := mul_le_mul_of_nonneg_left hb (sq_nonneg Real.pi)
  nlinarith [sq_nonneg Real.pi]

lemma harmonicSkew_inv_scaled {d : ℕ} {R : ℝ} (hR : 0<R) (hR1 : R≤1) :
    ∀k y,AllSplitBound (spatialTensor (harmonicSkew d) (List.finRange k) y)
      ((2:ℝ)*1*(R⁻¹)^k) := by
  intro k y
  have hh := harmonicSkew_scaled_bound d k y
  apply hh.mono (by norm_num)
  have hi : 1≤R⁻¹ := (one_le_inv₀ hR).mpr hR1
  simpa only [mul_one,one_pow] using mul_le_mul_of_nonneg_left (one_le_pow₀ hi) (by norm_num : (0:ℝ)≤2)

lemma centeringScore_inv_scaled {d : ℕ} {F : Point d → ℝ} {lam : ℝ≥0}
    (hF : Primitive F lam) (x : Point d) {r R T : ℝ}
    (hr : 0 < r) (hlam : 0<lam) (hl : (lam:ℝ)*r^2≤1/2)
    (hR : 0<R) (hRT : R^2≤1-T^2) (hT0 : 0≤T) (hT1 : T<1) :
    ∀k,0<k → ∀y,AllSplitBound (spatialTensor (scoreField (centeringPotential F x r T))
      (List.finRange k) y) ((2+normalizedTensorMajorant (k+1) 1)*(R⁻¹)^k) := by
  have hR1 : R≤1 := by nlinarith [sq_nonneg T]
  have hi : 1≤R⁻¹ := (one_le_inv₀ hR).mpr hR1
  intro k hk y
  have hh := centeringScore_scaled_bound hF x hr hlam hl hT0 hT1 k hk y
  simp only [one_pow,mul_one] at hh
  apply hh.mono (add_nonneg (by norm_num) (normalizedTensorMajorant_nonneg _ _))
  have he := normalizedTensorMajorant_inv_scale (k:=k) hR hR1 hRT
  have hp : (2:ℝ)≤2*(R⁻¹)^k := by nlinarith [one_le_pow₀ hi (n:=k)]
  nlinarith

lemma jointCorrection_inv_scaled {d : ℕ} {F : Point d → ℝ} {lam : ℝ≥0}
    (hF : Primitive F lam) (x : Point d) {r R T : ℝ}
    (hr : 0 < r) (hlam : 0<lam) (hl : (lam:ℝ)*r^2≤1/2)
    (hR : 0<R) (hRT : R^2≤1-T^2) (hT0 : 0≤T) (hT1 : T<1)
    (s t u : Icc (0:ℝ) T) :
    ∀k,0<k → spatialEnergy
      (jointCorrectionArray (fun z => probabilityTransport hF x hr.le hl hT0 hT1 s t z-z)) k
      (gibbs (centeringPotential F x r u))≤
      (d*((lam:ℝ)*r^2)^2)*(R⁻¹)^(2*k)*(transportCorrectionMajorant k)^2 := by
  have hR1 : R≤1 := by nlinarith [sq_nonneg T]
  intro k hk
  apply (jointCorrectionArray_energy hF x hr hlam hl hR hRT hT0 hT1 s t u hk).trans
  have he := pow_le_pow_left₀ (div_nonneg (transportCorrectionMajorant_nonneg k) (pow_nonneg hR.le _))
    (inv_scale_pred hR hR1 (transportCorrectionMajorant_nonneg k) k) 2
  have hh := mul_le_mul_of_nonneg_left he (show 0≤(d:ℝ)*((lam:ℝ)*r^2)^2 by positivity)
  convert hh using 1 <;> first | rfl | simp only [mul_pow,←pow_mul]; ring
end LogConcaveSampling

end

end

end

end OAI
end

section
-- module Solutions.OAIQ048_LC.LogConcave_Complexity_HarmonicCorrectionBudget
attribute [-instance] _root_.OAI.LogConcaveSampling.LowerBound.couplingLaw_probability _root_.OAI.LogConcaveSampling.LowerBound.remainingHaar_probability _root_.OAI.LogConcaveSampling.LowerBound.roundRandomLaw_probability _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_invInvariant _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_isHaar _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_probability _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_rightInvariant _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_compactSpace _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_measurableInv _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_measurableMul _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_secondCountable _root_.OAI.LogConcaveSampling.MeanTree.instIsProbabilityMeasureRowTapeRowLaw _root_.OAI.LogConcaveSampling.OracleCompiler.topSeedLaw_probability _root_.OAI.LogConcaveSampling.noiseKernel_markov
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
namespace LogConcaveSampling
open Set MeasureTheory
open scoped Classical BigOperators NNReal RealInnerProductSpace
open TensorEnergy Quadrature

lemma jointCorrectionArray_polySmooth {d : ℕ} {F : Point d → ℝ} {lam : ℝ≥0}
    (hF : Primitive F lam) (x : Point d) {r R T : ℝ}
    (hr : 0 < r) (hlam : 0<lam) (hl : (lam:ℝ)*r^2≤1/2)
    (hR : 0<R) (hRT : R^2≤1-T^2) (hT0 : 0≤T) (hT1 : T<1)
    (s t : Icc (0:ℝ) T) (c : Unit → Fin (d+d)) :
    PolySmooth (jointCorrectionArray
      (fun z => probabilityTransport hF x hr.le hl hT0 hT1 s t z-z) c) :=
  arrayCoordinateLift_polySmooth _ _ _
    (probabilityCorrection_polySmooth hF x hr hlam hl hR hRT hT0 hT1 s t) c

lemma harmonicCorrectionBudget_nonneg (n : ℕ) : 0≤harmonicCorrectionBudget n :=
  iterEnergyBudget_nonneg harmonicGradientBound.2 _ _ (fun _ => sq_nonneg _) n 0

attribute [local instance] OAI.LogConcaveSampling.instDecidableEqUnit_solutions_4
theorem harmonic_correction_taylor_rms {d : ℕ} {F : Point d → ℝ} {lam : ℝ≥0}
    (hF : Primitive F lam) (x : Point d) {r R T : ℝ}
    (hr : 0 < r) (hlam : 0<lam) (hl : (lam:ℝ)*r^2≤1/2)
    (hR : 0<R) (hRT : R^2≤1-T^2) (hT0 : 0≤T) (hT1 : T<1)
    (s t u : Icc (0:ℝ) T)
    (Ξ : Point (d+d) → ℝ → Point (d+d))
    (hder : ∀y v,v∈Icc (0:ℝ) 1 → HasDerivWithinAt (Ξ y)
      (skewLieField (centeringPotential F x r u) (harmonicSkew d) (Ξ y v)) (Icc (0:ℝ) 1) v)
    (hm : Measurable (fun p : ℝ × Point (d+d) => Ξ p.2 p.1))
    (hlaw : ∀v∈Icc (0:ℝ) 1,(gibbs (centeringPotential F x r u)).map (fun y => Ξ y v)=
      gibbs (centeringPotential F x r u)) :
    let A := jointCorrectionArray (fun z => probabilityTransport hF x hr.le hl hT0 hT1 s t z-z)
    ∀n : ℕ,∀a b : ℝ,0≤a → a≤b → b≤1 →
      Integrable (fun y => ‖tensorVector A (Ξ y b)-chainTaylor
        (fun k v => tensorVector (iterTensorLie (centeringPotential F x r u)
          (harmonicSkew d) A k) (Ξ y v)) n a b‖^2) (gibbs (centeringPotential F x r u)) ∧
      (∫y,‖tensorVector A (Ξ y b)-chainTaylor
        (fun k v => tensorVector (iterTensorLie (centeringPotential F x r u)
          (harmonicSkew d) A k) (Ξ y v)) n a b‖^2 ∂gibbs (centeringPotential F x r u))≤
      ((b-a)^(n+1)/(n.factorial:ℝ))^2*
        ((d*((lam:ℝ)*r^2)^2)*(R⁻¹)^(4*(n+1))*harmonicCorrectionBudget (n+1)) := by
  have hu1 := u.2.2.trans_lt hT1
  have hRu : R^2≤1-(u:ℝ)^2 := by nlinarith [u.2.1,u.2.2]
  have hR1 : R≤1 := by nlinarith [sq_nonneg T]
  have hH : PolySmooth (centeringPotential F x r u) := productPotential_polySmooth
    (interpolationPotential_polySmooth hF x hr hlam hl u.2.1 hu1) (gaussianPotential_polySmooth d)
  have ht : HasGaussianLowerTail (centeringPotential F x r u) := productPotential_lowerTail
    (interpolationPotential_lowerTail hF x hr.le (by linarith) u.2.1 hu1) (gaussianPotential_lowerTail d)
  let := probability_gibbs_of_gaussianTail hH.smooth.continuous ht
  intro A n a b ha hab hb
  have hsub : uIcc a b⊆Icc (0:ℝ) 1 := by
    rw [uIcc_of_le hab]
    intro v h; exact ⟨ha.trans h.1,h.2.trans hb⟩
  have h := stationary_lie_taylor_rms (S:=Unit) (d:=d+d) hH ht
    (centeringPotential_gradient_uniform hF x hr hl u.2.1 hu1)
    (harmonicSkew d) A (harmonicSkew_polySmooth d)
    (jointCorrectionArray_polySmooth hF x hr hlam hl hR hRT hT0 hT1 s t)
    (jointSkew_skew _ 1) (fun _ => 2)
    (fun k => 2+normalizedTensorMajorant (k+1) 1)
    (fun k => (transportCorrectionMajorant k)^2)
    (α:=1) (κ:=d*((lam:ℝ)*r^2)^2) (ρ:=R⁻¹) (by positivity) ((one_le_inv₀ hR).mpr hR1)
    (fun _ => sq_nonneg _) (harmonicSkew_inv_scaled hR hR1)
    (centeringScore_inv_scaled hF x hr hlam hl hR hRu u.2.1 hu1)
    (jointCorrection_inv_scaled hF x hr hlam hl hR hRT hT0 hT1 s t u)
    Ξ hder hm hlaw hab hsub n
  simpa only [one_pow,one_mul,←pow_mul,harmonicCorrectionBudget] using h

end LogConcaveSampling

end

end

end

end OAI
end

section
-- module Solutions.OAIQ048_LC.LogConcave_Numerics_CompositeAngle
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section

noncomputable section
namespace LogConcaveSampling.Quadrature
open MeasureTheory Set Polynomial
open scoped BigOperators

variable {I Ω E : Type*} [Fintype I] [DecidableEq I] [MeasurableSpace Ω]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E] {ν : Measure Ω}

lemma derivative_reproduces_scalar (u : I → ℝ) (hu : Function.Injective u)
    (p : ℝ[X]) (hp : p.degree<Fintype.card I) :
    (∑i,derivativeWeight u i*p.eval (u i))=p.derivative.eval 0 := by
  have he := congrArg (fun q : ℝ[X] => q.derivative.eval 0)
    (Lagrange.eq_interpolate (s:=Finset.univ) hu.injOn (by simpa using hp))
  simpa only [Lagrange.interpolate_apply,derivative_sum,derivative_mul,
    derivative_C,zero_mul,mul_zero,zero_add,add_zero,eval_finsetSum,eval_mul,eval_C,derivativeWeight,mul_comm] using he.symm

lemma derivative_reproduces_power (u : I → ℝ) (hu : Function.Injective u) (k : ℕ)
    (hk : k<Fintype.card I) :
    (∑i,derivativeWeight u i*(u i)^k)=if k=1 then 1 else 0 := by
  have hh := derivative_reproduces_scalar u hu (X^k) (by simpa using hk)
  simp only [eval_pow,eval_X,derivative_X_pow,eval_mul,eval_C] at hh
  rw [hh]
  by_cases h0 : k=0
  · simp [h0]
  by_cases h1 : k=1
  · simp [h1]
  have hk1 : k-1≠0 := by omega
  simp [h1,hk1]

lemma derivative_weights_norm (u : I → ℝ) {ψ : ℝ} (hψ : 0<ψ) :
    (∑i,|derivativeWeight u i/ψ|)=(∑i,|derivativeWeight u i|)/ψ := by
  simp only [abs_div,abs_of_pos hψ,Finset.sum_div]

omit [CompleteSpace E] in
lemma derivative_reproduces_vector (u : I → ℝ) (hu : Function.Injective u)
    (n : ℕ) (hn : 1≤n) (hm : n+1≤Fintype.card I) {ψ : ℝ} (hψ : ψ≠0)
    (v : Fin (n+1) → E) :
    derivativeStencil u ψ (fun i => ∑k : Fin (n+1),(ψ*u i)^(k:ℕ) • v k)=v ⟨1,by omega⟩ := by
  unfold derivativeStencil
  simp_rw [Finset.smul_sum,smul_smul,mul_pow]
  rw [Finset.sum_comm]
  have he (k : Fin (n+1)) :
      (∑i,((derivativeWeight u i/ψ)*(ψ^(k:ℕ)*(u i)^(k:ℕ))) • v k)=
        (if (k:ℕ)=1 then 1 else 0) • v k := by
    rw [←Finset.sum_smul]
    have hc : (∑i,(derivativeWeight u i/ψ)*(ψ^(k:ℕ)*(u i)^(k:ℕ)))=
        (ψ^(k:ℕ)/ψ)*∑i,derivativeWeight u i*(u i)^(k:ℕ) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro _ _
      ring
    rw [hc,derivative_reproduces_power u hu k (lt_of_lt_of_le k.2 hm)]
    by_cases hk : (k:ℕ)=1
    · simp [hk,hψ]
    · simp [hk]
  simp_rw [he]
  simp only [ite_smul,one_smul,zero_smul]
  rw [Finset.sum_eq_single ⟨1,by omega⟩]
  · simp
  · intro b _ hne
    have h : (b:ℕ)≠1 := fun h => hne (Fin.ext h)
    simp [h]
  · simp

omit [CompleteSpace E] in
theorem derivative_stencil_error_rms (u : I → ℝ) (hu : Function.Injective u)
    (n : ℕ) (hn : 1≤n) (hcard : n+1≤Fintype.card I) {ψ B : ℝ}
    (hψ : 0<ψ) (J : ℕ → ℝ → Ω → E)
    (hm : ∀i,AEStronglyMeasurable (fun z => J 0 (ψ*u i) z-
      chainTaylor (fun k t => J k t z) n 0 (ψ*u i)) ν)
    (hi : ∀i,Integrable (fun z => ‖J 0 (ψ*u i) z-
      chainTaylor (fun k t => J k t z) n 0 (ψ*u i)‖^2) ν)
    (hB : ∀i,(∫z,‖J 0 (ψ*u i) z-
      chainTaylor (fun k t => J k t z) n 0 (ψ*u i)‖^2 ∂ν)≤B) :
    Integrable (fun z => ‖derivativeStencil u ψ (fun i => J 0 (ψ*u i) z)-J 1 0 z‖^2) ν ∧
    (∫z,‖derivativeStencil u ψ (fun i => J 0 (ψ*u i) z)-J 1 0 z‖^2 ∂ν)≤
      ((∑i,|derivativeWeight u i|)/ψ)^2*B := by
  have he (z : Ω) : derivativeStencil u ψ (fun i =>
      chainTaylor (fun k t => J k t z) n 0 (ψ*u i))=J 1 0 z := by
    have hh := derivative_reproduces_vector u hu n hn hcard hψ.ne'
      (fun k => ((k:ℕ).factorial:ℝ)⁻¹ • J k 0 z)
    have ht (i : I) : chainTaylor (fun k t => J k t z) n 0 (ψ*u i)=
        ∑k : Fin (n+1),(ψ*u i)^(k:ℕ) • (((k:ℕ).factorial:ℝ)⁻¹ • J k 0 z) := by
      unfold chainTaylor
      rw [←Fin.sum_univ_eq_sum_range]
      apply Finset.sum_congr rfl
      intro _ _
      simp only [sub_zero,mul_smul]
      exact smul_comm _ _ _
    simp_rw [ht]
    simpa only [Nat.factorial_one,Nat.cast_one,inv_one,one_smul] using hh
  have hc (z : Ω) : derivativeStencil u ψ (fun i => J 0 (ψ*u i) z)-J 1 0 z=
      ∑i,(derivativeWeight u i/ψ) • (J 0 (ψ*u i) z-
        chainTaylor (fun k t => J k t z) n 0 (ψ*u i)) := by
    rw [←he z]
    simp only [derivativeStencil,smul_sub,Finset.sum_sub_distrib]
  simp_rw [hc]
  have hh := RMSIntegral.weighted_sum_sq (fun i => derivativeWeight u i/ψ) _ hm hi hB
  rw [derivative_weights_norm u hψ] at hh
  exact hh
end LogConcaveSampling.Quadrature

end

end

end

end OAI
end

section
-- module Solutions.OAIQ048_LC.LogConcave_Sampling_AngleNodes
attribute [-instance] _root_.OAI.LogConcaveSampling.LowerBound.couplingLaw_probability _root_.OAI.LogConcaveSampling.LowerBound.remainingHaar_probability _root_.OAI.LogConcaveSampling.LowerBound.roundRandomLaw_probability _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_invInvariant _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_isHaar _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_probability _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_rightInvariant _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_compactSpace _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_measurableInv _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_measurableMul _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_secondCountable _root_.OAI.LogConcaveSampling.MeanTree.instIsProbabilityMeasureRowTapeRowLaw _root_.OAI.LogConcaveSampling.OracleCompiler.topSeedLaw_probability _root_.OAI.LogConcaveSampling.noiseKernel_markov
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
namespace LogConcaveSampling
open Set MeasureTheory
open scoped Classical BigOperators NNReal RealInnerProductSpace
open TensorEnergy Quadrature

lemma angleNodes_injective (n : ℕ) : Function.Injective (angleNodes n) := by
  intro i j h
  apply Fin.ext
  change (i:ℝ)=(j:ℝ) at h
  exact_mod_cast h

lemma liePathJet_measurable {S : Type} [Fintype S] {d : ℕ} {H : Point d → ℝ}
    (hH : PolySmooth H) (A : (Unit ⊕ Unit → Fin d) → Point d → ℝ)
    (F : (S → Fin d) → Point d → ℝ) (hA : ∀c,PolySmooth (A c)) (hF : ∀c,PolySmooth (F c))
    (Ξ : Point d → ℝ → Point d) (hm : Measurable (fun p : ℝ × Point d => Ξ p.2 p.1))
    (k : ℕ) (v : ℝ) :
    Measurable (fun y => tensorVector (iterTensorLie H A F k) (Ξ y v)) :=
  (tensorVector_contDiff _ (fun c => (iterTensorLie_polySmooth hH A F hA hF k c).smooth)).continuous.measurable.comp
    (hm.comp (measurable_const.prodMk measurable_id))

lemma chainTaylor_measurable {Ω E : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E] [BorelSpace E]
    [SecondCountableTopology E] (J : ℕ → ℝ → Ω → E)
    (hm : ∀k t,Measurable (J k t)) (n : ℕ) (a b : ℝ) :
    Measurable (fun y => chainTaylor (fun k t => J k t y) n a b) := by
  unfold chainTaylor
  exact Finset.measurable_sum _ (fun k _ => (hm k a).const_smul _)

attribute [local instance] OAI.LogConcaveSampling.instDecidableEqUnit_solutions_5
theorem harmonic_correction_stencil_rms {d : ℕ} {F : Point d → ℝ} {lam : ℝ≥0}
    (hF : Primitive F lam) (x : Point d) {r R T : ℝ}
    (hr : 0 < r) (hlam : 0<lam) (hl : (lam:ℝ)*r^2≤1/2)
    (hR : 0<R) (hRT : R^2≤1-T^2) (hT0 : 0≤T) (hT1 : T<1)
    (s t u : Icc (0:ℝ) T)
    (Ξ : Point (d+d) → ℝ → Point (d+d))
    (hder : ∀y v,v∈Icc (0:ℝ) 1 → HasDerivWithinAt (Ξ y)
      (skewLieField (centeringPotential F x r u) (harmonicSkew d) (Ξ y v)) (Icc (0:ℝ) 1) v)
    (hm : Measurable (fun p : ℝ × Point (d+d) => Ξ p.2 p.1))
    (hlaw : ∀v∈Icc (0:ℝ) 1,(gibbs (centeringPotential F x r u)).map (fun y => Ξ y v)=
      gibbs (centeringPotential F x r u)) :
    let A := jointCorrectionArray (fun z => probabilityTransport hF x hr.le hl hT0 hT1 s t z-z)
    let J := fun k v y => tensorVector (iterTensorLie (centeringPotential F x r u) (harmonicSkew d) A k) (Ξ y v)
    ∀n : ℕ,1≤n → ∀ψ : ℝ,0<ψ → ψ*n≤1 →
      Integrable (fun y => ‖derivativeStencil (angleNodes n) ψ (fun i => J 0 (ψ*angleNodes n i) y)-J 1 0 y‖^2)
        (gibbs (centeringPotential F x r u)) ∧
      (∫y,‖derivativeStencil (angleNodes n) ψ (fun i => J 0 (ψ*angleNodes n i) y)-J 1 0 y‖^2
        ∂gibbs (centeringPotential F x r u))≤
      ((∑i,|derivativeWeight (angleNodes n) i|)/ψ)^2*
        (((ψ*n)^(n+1)/(n.factorial:ℝ))^2*
          ((d*((lam:ℝ)*r^2)^2)*(R⁻¹)^(4*(n+1))*harmonicCorrectionBudget (n+1))) := by
  intro A J n hn ψ hψ hψn
  have hu1 := u.2.2.trans_lt hT1
  have hH : PolySmooth (centeringPotential F x r u) := productPotential_polySmooth
    (interpolationPotential_polySmooth hF x hr hlam hl u.2.1 hu1) (gaussianPotential_polySmooth d)
  have hJ (k : ℕ) (v : ℝ) : Measurable (J k v) :=
    liePathJet_measurable hH (harmonicSkew d) A (harmonicSkew_polySmooth d)
      (jointCorrectionArray_polySmooth hF x hr hlam hl hR hRT hT0 hT1 s t) Ξ hm k v
  have hnode (i : Fin (n+1)) : 0≤ψ*angleNodes n i ∧ ψ*angleNodes n i≤ψ*n := by
    constructor
    · exact mul_nonneg hψ.le (Nat.cast_nonneg _)
    · apply mul_le_mul_of_nonneg_left _ hψ.le
      change (i:ℝ)≤(n:ℝ)
      exact_mod_cast Nat.le_of_lt_succ i.2
  have htay (i : Fin (n+1)) := harmonic_correction_taylor_rms hF x hr hlam hl hR hRT hT0 hT1
    s t u Ξ hder hm hlaw n 0 (ψ*angleNodes n i) le_rfl (hnode i).1 ((hnode i).2.trans hψn)
  apply derivative_stencil_error_rms (angleNodes n) (angleNodes_injective n) n hn (by simp) hψ J
  · intro i
    exact ((hJ 0 _).sub (chainTaylor_measurable J hJ n 0 _)).aestronglyMeasurable
  · intro i
    simpa only [J,iterTensorLie,sub_zero] using (htay i).1
  · intro i
    have hh := (htay i).2
    change (∫y,‖J 0 (ψ*angleNodes n i) y-chainTaylor
      (fun k v => J k v y) n 0 (ψ*angleNodes n i)‖^2 ∂gibbs (centeringPotential F x r u))≤_ at hh
    apply hh.trans
    simp only [sub_zero]
    apply mul_le_mul_of_nonneg_right _ (by positivity [harmonicCorrectionBudget_nonneg (n+1)])
    apply pow_le_pow_left₀ (div_nonneg (pow_nonneg (hnode i).1 _) (Nat.cast_nonneg _))
    apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
    exact pow_le_pow_left₀ (hnode i).1 (hnode i).2 _
end LogConcaveSampling

end

end

end

end OAI
end

section
-- module Solutions.OAIQ048_LC.LogConcave_Sampling_ProbabilityNodes
attribute [-instance] _root_.OAI.LogConcaveSampling.LowerBound.couplingLaw_probability _root_.OAI.LogConcaveSampling.LowerBound.remainingHaar_probability _root_.OAI.LogConcaveSampling.LowerBound.roundRandomLaw_probability _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_invInvariant _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_isHaar _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_probability _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_rightInvariant _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_compactSpace _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_measurableInv _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_measurableMul _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_secondCountable _root_.OAI.LogConcaveSampling.MeanTree.instIsProbabilityMeasureRowTapeRowLaw _root_.OAI.LogConcaveSampling.OracleCompiler.topSeedLaw_probability _root_.OAI.LogConcaveSampling.noiseKernel_markov
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section

noncomputable section
namespace LogConcaveSampling
open Set MeasureTheory TensorEnergy Quadrature
open scoped Classical BigOperators NNReal RealInnerProductSpace

lemma finiteCoordinateProjection_norm_le {I J : Type*} [Fintype I] [Fintype J]
    (e : I ↪ J) (v : EuclideanSpace ℝ J) : ‖finiteCoordinateProjection e v‖≤‖v‖ := by
  have he : ‖finiteCoordinateProjection e v‖^2≤‖v‖^2 := by
    rw [EuclideanSpace.real_norm_sq_eq,EuclideanSpace.real_norm_sq_eq]
    change (∑i : I,(v (e i))^2)≤∑j : J,(v j)^2
    calc
      _ = ∑j∈Finset.univ.map e,(v j)^2 := by rw [Finset.sum_map]
      _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
        (fun j _ _ => sq_nonneg _)
  nlinarith [norm_nonneg (finiteCoordinateProjection e v),norm_nonneg v]

end LogConcaveSampling

end

end

section

noncomputable section
namespace LogConcaveSampling
open Set MeasureTheory Quadrature FinitePicard
open scoped Classical BigOperators NNReal

lemma probabilityMeanVelocity_lipschitz {d : ℕ} {F : Point d → ℝ} {lam : ℝ≥0}
    (hF : Primitive F lam) (x : Point d) {r t : ℝ} (hr : 0 ≤ r)
    (hl : (lam:ℝ)*r^2≤1/2) (ht0 : 0≤t) (ht1 : t<1) :
    LipschitzWith (probabilityMeanLipschitz lam r) (probabilityMeanVelocity F x r t) := by
  apply LipschitzWith.of_dist_le_mul
  intro y z
  have he := (conditionalFieldMean_lipschitz hF x hr hl ht0 ht1).dist_le_mul y z
  simp only [probabilityMeanVelocity,dist_smul₀,Real.norm_eq_abs,abs_neg,abs_of_nonneg hr,
    probabilityMeanLipschitz]
  have hh := mul_le_mul_of_nonneg_left he hr
  have hp : 0≤(Real.pi^2/2)*(lam:ℝ)*r^2*dist y z := by positivity
  calc
    _ ≤ r*((Real.pi^2/2)*t*((lam:ℝ)*r)*dist y z) := hh
    _ = t*((Real.pi^2/2)*(lam:ℝ)*r^2*dist y z) := by ring
    _ ≤ _ := mul_le_of_le_one_left hp ht1.le

end LogConcaveSampling

end

end

section

noncomputable section
namespace LogConcaveSampling
open Set MeasureTheory Quadrature FinitePicard
open scoped Classical BigOperators NNReal

lemma harmonicFree_lipschitz {d : ℕ} (n : ℕ) (z : ℝ) :
    LipschitzWith 2 (harmonicFree (d:=d) n z) := by
  apply LipschitzWith.of_dist_le_mul
  intro p q
  apply (dist_pi_le_iff (by positivity)).mpr
  intro i
  have he := (((lipschitzWith_smul (Real.cos (z*probabilityNodes n i))).comp
    (LipschitzWith.prod_fst (α:=Point d) (β:=Point d))).add
    ((lipschitzWith_smul (Real.sin (z*probabilityNodes n i))).comp
      (LipschitzWith.prod_snd (α:=Point d) (β:=Point d)))).dist_le_mul p q
  have hc : ‖Real.cos (z*probabilityNodes n i)‖+‖Real.sin (z*probabilityNodes n i)‖≤2 := by
    have hc := add_le_add (Real.abs_cos_le_one (z*probabilityNodes n i)) (Real.abs_sin_le_one (z*probabilityNodes n i))
    simpa only [Real.norm_eq_abs,show (1:ℝ)+1=2 by norm_num] using hc
  change dist (harmonicFree n z p i) (harmonicFree n z q i)≤_ at he
  simp only [NNReal.coe_add,mul_one,coe_nnnorm] at he
  exact he.trans (mul_le_mul_of_nonneg_right hc dist_nonneg)

lemma harmonicMeanVelocity_lipschitz {d : ℕ} {F : Point d → ℝ} {lam : ℝ≥0}
    (hF : Primitive F lam) (x : Point d) {r ρ : ℝ} (hr : 0 ≤ r)
    (hl : (lam:ℝ)*r^2≤1/2) (hρ0 : 0≤ρ) (hρ1 : ρ<1) :
    LipschitzWith (probabilityMeanLipschitz lam r) (harmonicMeanVelocity F x r ρ) := by
  apply ((lipschitzWith_smul ρ).comp (probabilityMeanVelocity_lipschitz hF x hr hl hρ0 hρ1)).weaken
  change ‖ρ‖*(probabilityMeanLipschitz lam r:ℝ)≤_
  rw [Real.norm_eq_abs,abs_of_nonneg hρ0]
  exact mul_le_of_le_one_left (probabilityMeanLipschitz lam r).2 hρ1.le

end LogConcaveSampling

end

end

end

end OAI
end

section
-- module Solutions.OAIQ048_LC.LogConcave_Numerics_NodesContinuous
attribute [-instance] _root_.OAI.LogConcaveSampling.LowerBound.couplingLaw_probability _root_.OAI.LogConcaveSampling.LowerBound.remainingHaar_probability _root_.OAI.LogConcaveSampling.LowerBound.roundRandomLaw_probability _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_invInvariant _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_isHaar _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_probability _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_rightInvariant _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_compactSpace _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_measurableInv _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_measurableMul _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_secondCountable _root_.OAI.LogConcaveSampling.MeanTree.instIsProbabilityMeasureRowTapeRowLaw _root_.OAI.LogConcaveSampling.OracleCompiler.topSeedLaw_probability _root_.OAI.LogConcaveSampling.noiseKernel_markov
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
namespace LogConcaveSampling
open Set MeasureTheory ProbabilityTheory FinitePicard
open scoped Classical BigOperators NNReal

lemma FinitePicard.nodes_continuous {I E X : Type*} [Fintype I]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [PseudoMetricSpace X]
    (w : I → I → ℝ) (φ : I → E → E) (a : X → I → E)
    (hφ : ∀i,Continuous (φ i)) (ha : Continuous a) (N : ℕ) :
    Continuous (nodes w φ a N) := by
  induction N with
  | zero => exact ha
  | succ N ih =>
    apply continuous_pi
    intro i
    exact ((continuous_apply i).comp ha).add (continuous_finsetSum _ (fun j _ =>
      ((hφ j).comp ((continuous_apply j).comp ih)).const_smul (w i j)))

lemma probabilityAnchored_continuous {d : ℕ} {F : Point d → ℝ} {lam : ℝ≥0}
    (hF : Primitive F lam) (x : Point d) {r T h : ℝ} (hr : 0 ≤ r)
    (hl : (lam:ℝ)*r^2≤1/2) (hT0 : 0<T) (hT1 : T<1) (hh : 0<h)
    (n : ℕ) (hn : 0<n) (N : ℕ) (s i : ProbabilityNode T h n) :
    Continuous (fun y => probabilityAnchoredPicard F x r T h n N s y i) := by
  apply (continuous_apply i).comp
  apply FinitePicard.nodes_continuous
  · intro j
    have hj := probabilityNodeTime_mem hT0 hT1 hh hn j
    exact (probabilityMeanVelocity_lipschitz hF x hr hl hj.1 (hj.2.trans_lt hT1)).continuous
  · exact continuous_pi (fun _ => continuous_id)

end LogConcaveSampling

end

end

end

end OAI
end

section
-- module Solutions.OAIQ048_LC.LogConcave_Numerics_KernelCorrectionPicard
attribute [-instance] _root_.OAI.LogConcaveSampling.LowerBound.couplingLaw_probability _root_.OAI.LogConcaveSampling.LowerBound.remainingHaar_probability _root_.OAI.LogConcaveSampling.LowerBound.roundRandomLaw_probability _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_invInvariant _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_isHaar _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_probability _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_rightInvariant _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_compactSpace _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_measurableInv _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_measurableMul _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_secondCountable _root_.OAI.LogConcaveSampling.MeanTree.instIsProbabilityMeasureRowTapeRowLaw _root_.OAI.LogConcaveSampling.OracleCompiler.topSeedLaw_probability _root_.OAI.LogConcaveSampling.noiseKernel_markov
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
namespace LogConcaveSampling.RMSIntegral
open MeasureTheory
open scoped NNReal

variable {Ω E H : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
  [NormedAddCommGroup E] [SecondCountableTopology E] [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup H] [SecondCountableTopology H] [MeasurableSpace H] [BorelSpace H]

lemma add_error_sq {f g k : Ω → E} (hf : Measurable f) (hg : Measurable g) (hk : Measurable k)
    (hfg : Integrable (fun y => ‖f y-g y‖^2) μ)
    (hgk : Integrable (fun y => ‖g y-k y‖^2) μ)
    {A B : ℝ} (hA : (∫y,‖f y-g y‖^2 ∂μ)≤A) (hB : (∫y,‖g y-k y‖^2 ∂μ)≤B) :
    Integrable (fun y => ‖f y-k y‖^2) μ ∧ (∫y,‖f y-k y‖^2 ∂μ)≤2*A+2*B := by
  have he (y : Ω) : f y-k y=(f y-g y)-(k y-g y) := by abel
  have hi : Integrable (fun y => ‖k y-g y‖^2) μ := by simpa only [norm_sub_rev] using hgk
  have hb : (∫y,‖k y-g y‖^2 ∂μ)≤B := by simpa only [norm_sub_rev] using hB
  simp_rw [he]
  exact sub_sq_bound (hf.sub hg).aestronglyMeasurable (hk.sub hg).aestronglyMeasurable hfg hi hA hb

end LogConcaveSampling.RMSIntegral

end

end

section

noncomputable section
namespace LogConcaveSampling
open Set
open scoped NNReal

lemma harmonicPicard_continuous {d : ℕ} {F : Point d → ℝ} {lam : ℝ≥0}
    (hF : Primitive F lam) (x : Point d) {r ρ : ℝ} (hr : 0 ≤ r)
    (hl : (lam:ℝ)*r^2≤1/2) (hρ0 : 0≤ρ) (hρ1 : ρ<1)
    (z : ℝ) (n N : ℕ) (i : Fin (n+1)) :
    Continuous (fun p => harmonicPicard F x r ρ z n N p i) := by
  apply (continuous_apply i).comp
  apply FinitePicard.nodes_continuous
  · exact fun _ => (harmonicMeanVelocity_lipschitz hF x hr hl hρ0 hρ1).continuous
  · exact (harmonicFree_lipschitz n z).continuous

lemma kernelCorrectionPicard_continuous {d : ℕ} {F : Point d → ℝ} {lam : ℝ≥0}
    (hF : Primitive F lam) (x : Point d) {r T h : ℝ} (hr : 0 ≤ r)
    (hl : (lam:ℝ)*r^2≤1/2) (hT0 : 0<T) (hT1 : T<1) (hh : 0<h)
    (z : ℝ) (n : ℕ) (hn : 0<n) (N : ℕ) (s e : ProbabilityNode T h n) :
    Continuous (kernelCorrectionPicard F x r T h z n N s e) := by
  have hb : Continuous (fun p : Point d × Point d => probabilityAnchoredPicard F x r T h n N e p.1 s) :=
    (probabilityAnchored_continuous hF x hr hl hT0 hT1 hh n hn N e s).comp continuous_fst
  have ht := probabilityNodeTime_mem hT0 hT1 hh hn s
  have hw := (harmonicPicard_continuous hF x hr hl ht.1 (ht.2.trans_lt hT1) z n N (Fin.last n)).comp
    (hb.prodMk continuous_snd)
  exact ((probabilityAnchored_continuous hF x hr hl hT0 hT1 hh n hn (N+1) s e).comp hw).sub hw
end LogConcaveSampling

end

end

end

end OAI
end

section
-- module Solutions.OAIQ048_LC.LogConcave_Sampling_HarmonicPositionDeriv
attribute [-instance] _root_.OAI.LogConcaveSampling.LowerBound.couplingLaw_probability _root_.OAI.LogConcaveSampling.LowerBound.remainingHaar_probability _root_.OAI.LogConcaveSampling.LowerBound.roundRandomLaw_probability _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_invInvariant _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_isHaar _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_probability _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_rightInvariant _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_compactSpace _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_measurableInv _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_measurableMul _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_secondCountable _root_.OAI.LogConcaveSampling.MeanTree.instIsProbabilityMeasureRowTapeRowLaw _root_.OAI.LogConcaveSampling.OracleCompiler.topSeedLaw_probability _root_.OAI.LogConcaveSampling.noiseKernel_markov
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
namespace LogConcaveSampling
open Set MeasureTheory
open scoped NNReal

lemma harmonic_position_deriv {d : ℕ} {H : Point d → ℝ}
    (hH : Differentiable ℝ H) (Ξ : Point (d+d) → ℝ → Point (d+d))
    (hder : ∀y v,v∈Icc (0:ℝ) 1 → HasDerivWithinAt (Ξ y)
      (skewLieField (productPotential H (fun z : Point d => ‖z‖^2/2))
        (harmonicSkew d) (Ξ y v)) (Icc (0:ℝ) 1) v)
    (y : Point (d+d)) {v : ℝ} (hv : v∈Icc (0:ℝ) 1) :
    HasDerivWithinAt (fun u => (productPointEquiv d d (Ξ y u)).1)
      (productPointEquiv d d (Ξ y v)).2 (Icc (0:ℝ) 1) v := by
  have h := (productPointEquiv d d).toContinuousLinearMap.hasFDerivAt.comp_hasDerivWithinAt v (hder y v hv)
  change HasDerivWithinAt (fun u => productPointEquiv d d (Ξ y u))
    (productPointEquiv d d (skewLieField
      (productPotential H (fun z : Point d => ‖z‖^2/2)) (harmonicSkew d) (Ξ y v))) _ _ at h
  rw [harmonicSkew_field hH] at h
  exact h.fst

end LogConcaveSampling

end

end

section

noncomputable section
namespace LogConcaveSampling
open Set MeasureTheory TensorEnergy Quadrature
open scoped Classical BigOperators NNReal RealInnerProductSpace

lemma meanOutputProjection_correction {d : ℕ} (f : Point d → Point d)
    (y : Point (d+d)) :
    meanOutputProjection d (tensorVector (jointCorrectionArray f) y)=
      f (productPointEquiv d d y).1 := by
  ext i
  change TensorEnergy.zeroExtend (slotEmbedding (fun _ : Unit => leftCoordinates d d))
    (fun a => vectorArray f a (coordinateProjection (leftCoordinates d d) y))
    (slotEmbedding (fun _ : Unit => leftCoordinates d d) (fun _ => i))=_
  rw [zeroExtend_apply,coordinateProjection_left]
  simp only [vectorArray,EuclideanSpace.basisFun_inner]

lemma projection_derivativeStencil {I E G : Type*} [Fintype I] [DecidableEq I]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup G] [NormedSpace ℝ G]
    (L : E →L[ℝ] G) (u : I → ℝ) (ψ : ℝ) (v : I → E) :
    L (derivativeStencil u ψ v)=derivativeStencil u ψ (fun i => L (v i)) := by
  simp only [derivativeStencil,map_sum,map_smul]

end LogConcaveSampling

end

end

end

end OAI
end

section
-- module Solutions.OAIQ048_LC.LogConcave_Sampling_KernelTransportAction
attribute [-instance] _root_.OAI.LogConcaveSampling.LowerBound.couplingLaw_probability _root_.OAI.LogConcaveSampling.LowerBound.remainingHaar_probability _root_.OAI.LogConcaveSampling.LowerBound.roundRandomLaw_probability _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_invInvariant _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_isHaar _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_probability _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_rightInvariant _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_compactSpace _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_measurableInv _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_measurableMul _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_secondCountable _root_.OAI.LogConcaveSampling.MeanTree.instIsProbabilityMeasureRowTapeRowLaw _root_.OAI.LogConcaveSampling.OracleCompiler.topSeedLaw_probability _root_.OAI.LogConcaveSampling.noiseKernel_markov
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
namespace LogConcaveSampling
open Set MeasureTheory TensorEnergy Quadrature
open scoped Classical BigOperators NNReal

lemma kernel_action_between_derivative {d : ℕ} {F : Point d → ℝ} {lam : ℝ≥0}
    (hF : Primitive F lam) (x : Point d) {r T : ℝ} (hr : 0 < r)
    (hl : (lam:ℝ)*r^2≤1/2) (hT0 : 0≤T) (hT1 : T<1)
    (s e : Icc (0:ℝ) T) (p : Point (d+d))
    (Ξ : Point (d+d) → ℝ → Point (d+d)) (hinit : ∀p,Ξ p 0=p)
    (hder : ∀p v,v∈Icc (0:ℝ) 1 → HasDerivWithinAt (Ξ p)
      (skewLieField (centeringPotential F x r s) (harmonicSkew d) (Ξ p v)) (Icc (0:ℝ) 1) v) :
    let fw := probabilityTransport hF x hr.le hl hT0 hT1 s e
    let W := fun v => (productPointEquiv d d (Ξ p v)).1
    HasDerivWithinAt (fun v => fw (W v)-W v) (kernelTransportAction fw p) (Icc (0:ℝ) 1) 0 := by
  intro fw W
  have hH := (interpolationPotential_smooth hF x hr.le hl s.2.1 (s.2.2.trans_lt hT1)).differentiable
    (by norm_cast)
  have hw := harmonic_position_deriv hH Ξ hder p (by norm_num : (0:ℝ)∈Icc (0:ℝ) 1)
  rw [hinit] at hw
  have hw0 : W 0=(productPointEquiv d d p).1 := by dsimp [W]; rw [hinit]
  have hf := (probabilityTransport_smooth hF x hr.le hl hT0 hT1 s e).differentiable (by norm_cast)
  have he := ((hf (W 0)).hasFDerivAt.comp_hasDerivWithinAt 0 hw).sub hw
  rw [hw0] at he
  exact he

attribute [local instance] OAI.LogConcaveSampling.instDecidableEqUnit_solutions_9
lemma kernel_between_lie_projection {d : ℕ} {F : Point d → ℝ} {lam : ℝ≥0}
    (hF : Primitive F lam) (x : Point d) {r R T : ℝ} (hr : 0 < r)
    (hlam : 0<lam) (hl : (lam:ℝ)*r^2≤1/2) (hR : 0<R) (hRT : R^2≤1-T^2)
    (hT0 : 0≤T) (hT1 : T<1) (s e : Icc (0:ℝ) T)
    (Ξ : Point (d+d) → ℝ → Point (d+d)) (hinit : ∀p,Ξ p 0=p)
    (hder : ∀p v,v∈Icc (0:ℝ) 1 → HasDerivWithinAt (Ξ p)
      (skewLieField (centeringPotential F x r s) (harmonicSkew d) (Ξ p v)) (Icc (0:ℝ) 1) v)
    (p : Point (d+d)) :
    let fw := probabilityTransport hF x hr.le hl hT0 hT1 s e
    let A := jointCorrectionArray (fun z => fw z-z)
    meanOutputProjection d (tensorVector (iterTensorLie (centeringPotential F x r s)
      (harmonicSkew d) A 1) p)=kernelTransportAction fw p := by
  intro fw A
  have hH : PolySmooth (centeringPotential F x r s) := productPotential_polySmooth
    (interpolationPotential_polySmooth hF x hr hlam hl s.2.1 (s.2.2.trans_lt hT1))
      (gaussianPotential_polySmooth d)
  have hp := lie_vector_chain hH (harmonicSkew d) A (harmonicSkew_polySmooth d)
    (jointCorrectionArray_polySmooth hF x hr hlam hl hR hRT hT0 hT1 s e)
    (jointSkew_skew _ 1) (Ξ p) (hder p) 0 (by norm_num : (0:ℝ)∈Icc (0:ℝ) 1)
  have hproj := (meanOutputProjection d).hasFDerivAt.comp_hasDerivWithinAt 0 hp
  change HasDerivWithinAt (fun v => meanOutputProjection d
    (tensorVector A (Ξ p v))) (meanOutputProjection d (tensorVector
      (iterTensorLie (centeringPotential F x r s) (harmonicSkew d) A 1) (Ξ p 0)))
      (Icc (0:ℝ) 1) 0 at hproj
  simp only [A,meanOutputProjection_correction,hinit] at hproj
  have hd := kernel_action_between_derivative hF x hr hl hT0 hT1 s e p Ξ hinit hder
  have hu := uniqueDiffOn_Icc (by norm_num : (0:ℝ)<1) 0 (by norm_num)
  exact (hproj.derivWithin hu).symm.trans (hd.derivWithin hu)

theorem kernel_action_between_stencil_rms {d : ℕ} {F : Point d → ℝ} {lam : ℝ≥0}
    (hF : Primitive F lam) (x : Point d) {r R T : ℝ} (hr : 0 < r)
    (hlam : 0<lam) (hl : (lam:ℝ)*r^2≤1/2) (hR : 0<R) (hRT : R^2≤1-T^2)
    (hT0 : 0≤T) (hT1 : T<1) (s e : Icc (0:ℝ) T)
    (Ξ : Point (d+d) → ℝ → Point (d+d)) (hinit : ∀p,Ξ p 0=p)
    (hder : ∀p v,v∈Icc (0:ℝ) 1 → HasDerivWithinAt (Ξ p)
      (skewLieField (centeringPotential F x r s) (harmonicSkew d) (Ξ p v)) (Icc (0:ℝ) 1) v)
    (hm : Measurable (fun p : ℝ × Point (d+d) => Ξ p.2 p.1))
    (hlaw : ∀v∈Icc (0:ℝ) 1,(gibbs (centeringPotential F x r s)).map (fun y => Ξ y v)=
      gibbs (centeringPotential F x r s))
    (m : ℕ) (hm1 : 1 ≤ m) (ψ : ℝ) (hψ : 0<ψ) (hψm : ψ*m≤1) :
    let fw := probabilityTransport hF x hr.le hl hT0 hT1 s e
    let W := fun v p => (productPointEquiv d d (Ξ p v)).1
    let K := kernelTransportAction fw
    Measurable K ∧
    Integrable (fun p => ‖derivativeStencil (angleNodes m) ψ
      (fun i => fw (W (ψ*angleNodes m i) p)-W (ψ*angleNodes m i) p)-K p‖^2)
        (gibbs (centeringPotential F x r s)) ∧
    (∫p,‖derivativeStencil (angleNodes m) ψ
      (fun i => fw (W (ψ*angleNodes m i) p)-W (ψ*angleNodes m i) p)-K p‖^2
        ∂gibbs (centeringPotential F x r s))≤
      ((∑i,|derivativeWeight (angleNodes m) i|)/ψ)^2*
        (((ψ*m)^(m+1)/(m.factorial:ℝ))^2*
          ((d*((lam:ℝ)*r^2)^2)*(R⁻¹)^(4*(m+1))*harmonicCorrectionBudget (m+1))) := by
  intro fw W K
  let A := jointCorrectionArray (fun z => fw z-z)
  let J := fun k v p => tensorVector (iterTensorLie (centeringPotential F x r s)
    (harmonicSkew d) A k) (Ξ p v)
  let E := fun p => derivativeStencil (angleNodes m) ψ (fun i => J 0 (ψ*angleNodes m i) p)-J 1 0 p
  have hH : PolySmooth (centeringPotential F x r s) := productPotential_polySmooth
    (interpolationPotential_polySmooth hF x hr hlam hl s.2.1 (s.2.2.trans_lt hT1))
      (gaussianPotential_polySmooth d)
  have hA := jointCorrectionArray_polySmooth hF x hr hlam hl hR hRT hT0 hT1 s e
  have hJ (k : ℕ) (v : ℝ) : Measurable (J k v) := liePathJet_measurable hH
    (harmonicSkew d) A (harmonicSkew_polySmooth d) hA Ξ hm k v
  have hj0 (v : ℝ) (p : Point (d+d)) : meanOutputProjection d (J 0 v p)=fw (W v p)-W v p :=
    meanOutputProjection_correction _ (Ξ p v)
  have hj1 (p : Point (d+d)) : meanOutputProjection d (J 1 0 p)=K p := by
    dsimp only [J]
    rw [hinit]
    exact kernel_between_lie_projection hF x hr hlam hl hR hRT hT0 hT1 s e Ξ hinit hder p
  have hK : Measurable K := by
    have hh := (meanOutputProjection d).continuous.measurable.comp (hJ 1 0)
    simpa only [Function.comp_def,hj1] using hh
  refine ⟨hK,?_⟩
  have he (p : Point (d+d)) : derivativeStencil (angleNodes m) ψ
      (fun i => fw (W (ψ*angleNodes m i) p)-W (ψ*angleNodes m i) p)-K p=
        meanOutputProjection d (E p) := by
    dsimp only [E]
    rw [map_sub,projection_derivativeStencil]
    simp only [hj0,hj1]
  have hb := harmonic_correction_stencil_rms hF x hr hlam hl hR hRT hT0 hT1
    s e s Ξ hder hm hlaw m hm1 ψ hψ hψm
  have hE : Measurable E := (Finset.measurable_sum _ (fun i _ =>
    (hJ 0 (ψ*angleNodes m i)).const_smul (derivativeWeight (angleNodes m) i/ψ))).sub (hJ 1 0)
  have hab (p : Point (d+d)) : ‖meanOutputProjection d (E p)‖^2≤‖E p‖^2 :=
    pow_le_pow_left₀ (norm_nonneg _) (finiteCoordinateProjection_norm_le _ _) 2
  simp_rw [he]
  have hi := hb.1.mono' (((meanOutputProjection d).continuous.measurable.comp hE).norm.pow_const 2).aestronglyMeasurable
    (Filter.Eventually.of_forall (fun p => by simpa only [Real.norm_eq_abs,abs_sq,Function.comp_def,E,J,A,fw] using hab p))
  exact ⟨hi,(integral_mono hi hb.1 hab).trans hb.2⟩
end LogConcaveSampling

end

end

end

end OAI
end

section
-- module Solutions.OAIQ048_LC.LogConcave_Complexity_KernelValueRmsBudget
attribute [-instance] _root_.OAI.LogConcaveSampling.LowerBound.couplingLaw_probability _root_.OAI.LogConcaveSampling.LowerBound.remainingHaar_probability _root_.OAI.LogConcaveSampling.LowerBound.roundRandomLaw_probability _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_invInvariant _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_isHaar _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_probability _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_rightInvariant _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_compactSpace _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_measurableInv _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_measurableMul _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_secondCountable _root_.OAI.LogConcaveSampling.MeanTree.instIsProbabilityMeasureRowTapeRowLaw _root_.OAI.LogConcaveSampling.OracleCompiler.topSeedLaw_probability _root_.OAI.LogConcaveSampling.noiseKernel_markov
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
namespace LogConcaveSampling
open Set MeasureTheory ProbabilityTheory RMSIntegral Quadrature
open scoped Classical BigOperators NNReal

theorem kernelActionPicard_numerical_rms (n : ℕ) (hn : 0<n) :
    ∃Ap Ah Lp Lh : ℝ≥0,∃C J : ℝ,0≤C ∧ 1≤J ∧ ∃k : ℕ,
      ∀{d : ℕ} {F : Point d → ℝ} {lam : ℝ≥0},∀hF : Primitive F lam,
      ∀(x : Point d) {r : ℝ},∀hr : 0 < r,0<lam → ∀hl : (lam:ℝ)*r^2≤1/2,1≤d →
      ∀{T h : ℝ},∀hT0 : 0<T,∀hT1 : T<1,∀hh : 0<h,h≤Real.log 2 →
      Ap*probabilityMeanLipschitz lam r≤1/2 → Ah*probabilityMeanLipschitz lam r≤1/2 →
      Lp*probabilityMeanLipschitz lam r≤1/2 → Lh*probabilityMeanLipschitz lam r≤1/2 →
      ∀N : ℕ,∀s e : ProbabilityNode T h n,
      let S : Icc (0:ℝ) T := ⟨probabilityNodeTime T h n s,probabilityNodeTime_mem hT0 hT1 hh hn s⟩
      let E : Icc (0:ℝ) T := ⟨probabilityNodeTime T h n e,probabilityNodeTime_mem hT0 hT1 hh hn e⟩
      let μ := gibbs (centeringPotential F x r S)
      let fw := probabilityTransport hF x hr.le hl hT0.le hT1 S E
      ∀R : ℝ,0<R → R^2≤1-(S:ℝ)^2 →
      ∀Ξ : Point (d+d) → ℝ → Point (d+d),
      (∀y,Continuous (Ξ y)) → (∀y,Ξ y 0=y) →
      (∀y v,v∈Icc (0:ℝ) 1 → HasDerivWithinAt (Ξ y)
        (skewLieField (centeringPotential F x r S) (harmonicSkew d) (Ξ y v)) (Icc (0:ℝ) 1) v) →
      Measurable (fun p : ℝ × Point (d+d) => Ξ p.2 p.1) →
      (∀v∈Icc (0:ℝ) 1,μ.map (fun y => Ξ y v)=μ) →
      ∀m : ℕ,∀ψ : ℝ,0<ψ → ψ*m≤1 →
      let w := fun z y => (productPointEquiv d d (Ξ y z)).1
      let err := fun y => kernelActionPicard F x r T h ψ n m N s e
        (fw (productPointEquiv d d y).1,(productPointEquiv d d y).2)-
          derivativeStencil (angleNodes m) ψ (fun i => fw (w (ψ*angleNodes m i) y)-w (ψ*angleNodes m i) y)
      Integrable (fun y => ‖err y‖^2) μ ∧
      (∫y,‖err y‖^2 ∂μ)≤
        (∑i,|derivativeWeight (angleNodes m) i/ψ|)*
          (∑i,|derivativeWeight (angleNodes m) i/ψ| *
            kernelValueRmsBudget F x lam Ap Ah Lp r R S h (ψ*angleNodes m i) C J k n N) := by
  obtain ⟨Ap,Ah,Lp,Lh,C,J,hC,hJ,k,hV⟩ := kernelCorrectionPicard_rms n hn
  refine ⟨Ap,Ah,Lp,Lh,C,J,hC,hJ,k,?_⟩
  intro d F lam hF x r hr hlam hl hd T h hT0 hT1 hh hsmall hqp hqh hqlp hqlh N s e
  dsimp only
  let S : Icc (0:ℝ) T := ⟨probabilityNodeTime T h n s,probabilityNodeTime_mem hT0 hT1 hh hn s⟩
  let E : Icc (0:ℝ) T := ⟨probabilityNodeTime T h n e,probabilityNodeTime_mem hT0 hT1 hh hn e⟩
  let μ := gibbs (centeringPotential F x r S)
  let fw := probabilityTransport hF x hr.le hl hT0.le hT1 S E
  intro R hR hRT Ξ hc hinit hder hm hlaw m ψ hψ hψm
  let pos := fun y : Point (d+d) => (productPointEquiv d d y).1
  let mom := fun y : Point (d+d) => (productPointEquiv d d y).2
  let w := fun z y => pos (Ξ y z)
  let inp := fun y => (fw (pos y),mom y)
  let v := fun i y => kernelCorrectionPicard F x r T h (ψ*angleNodes m i) n N s e (inp y)-
    (fw (w (ψ*angleNodes m i) y)-w (ψ*angleNodes m i) y)
  have hz (i : Fin (m+1)) : 0≤ψ*angleNodes m i ∧ ψ*angleNodes m i≤1 := by
    refine ⟨mul_nonneg hψ.le (Nat.cast_nonneg _),le_trans ?_ hψm⟩
    apply mul_le_mul_of_nonneg_left _ hψ.le
    change (i:ℝ)≤(m:ℝ)
    exact_mod_cast Nat.le_of_lt_succ i.2
  have hval (i : Fin (m+1)) : Integrable (fun y => ‖v i y‖^2) μ ∧
      (∫y,‖v i y‖^2 ∂μ)≤kernelValueRmsBudget F x lam Ap Ah Lp r R S h (ψ*angleNodes m i) C J k n N :=
    hV hF x hr hlam hl hd hT0 hT1 hh hsmall hqp hqh hqlp hqlh N s e
      R hR hRT Ξ hc hinit hder hm hlaw _ (hz i).1 (hz i).2
  have hpos : Measurable pos := (productPointEquiv d d).continuous.measurable.fst
  have hmom : Measurable mom := (productPointEquiv d d).continuous.measurable.snd
  have hfw : Measurable fw := (probabilityTransport_continuous hF x hr.le hl hT0.le hT1 S E).measurable
  have hinp : Measurable inp := (hfw.comp hpos).prodMk hmom
  have hw (z : ℝ) : Measurable (w z) := hpos.comp (hm.comp (measurable_const.prodMk measurable_id))
  have hv (i : Fin (m+1)) : Measurable (v i) :=
    ((kernelCorrectionPicard_continuous hF x hr.le hl hT0 hT1 hh _ n hn N s e).measurable.comp hinp).sub
      ((hfw.comp (hw _)).sub (hw _))
  have he (y : Point (d+d)) : kernelActionPicard F x r T h ψ n m N s e (inp y)-
      derivativeStencil (angleNodes m) ψ (fun i => fw (w (ψ*angleNodes m i) y)-w (ψ*angleNodes m i) y)=
        ∑i,(derivativeWeight (angleNodes m) i/ψ) • v i y := by
    simp only [kernelActionPicard,derivativeStencil,←Finset.sum_sub_distrib,←smul_sub]
    rfl
  have hh := weighted_sum_sq_varying (fun i => derivativeWeight (angleNodes m) i/ψ) v _
    (fun i => (hv i).aestronglyMeasurable) (fun i => (hval i).1) (fun i => (hval i).2)
  simpa only [←he] using hh
end LogConcaveSampling

end

end

end

end OAI
end

section
-- module Solutions.OAIQ048_LC.LogConcave_Dynamics_HarmonicFlow
attribute [-instance] _root_.OAI.LogConcaveSampling.LowerBound.couplingLaw_probability _root_.OAI.LogConcaveSampling.LowerBound.remainingHaar_probability _root_.OAI.LogConcaveSampling.LowerBound.roundRandomLaw_probability _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_invInvariant _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_isHaar _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_probability _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_rightInvariant _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_compactSpace _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_measurableInv _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_measurableMul _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_secondCountable _root_.OAI.LogConcaveSampling.MeanTree.instIsProbabilityMeasureRowTapeRowLaw _root_.OAI.LogConcaveSampling.OracleCompiler.topSeedLaw_probability _root_.OAI.LogConcaveSampling.noiseKernel_markov
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
namespace LogConcaveSampling
open Set MeasureTheory ProbabilityTheory
open scoped NNReal RealInnerProductSpace

theorem exists_harmonic_flow {d : ℕ} {H : Point d → ℝ} {L : ℝ≥0}
    (hH : ContDiff ℝ 2 H) (ht : HasGaussianLowerTail H)
    (hL : LipschitzWith L (gradient H)) {a b : ℝ} (hab : a≤b) :
    ∃Ψ : (Point d × Point d) → ℝ → (Point d × Point d),
      (∀p,Continuous (Ψ p) ∧ Ψ p a=p ∧ ∀t∈Icc a b,
        HasDerivWithinAt (Ψ p) ((Ψ p t).2,-gradient H (Ψ p t).1) (Icc a b) t) ∧
      (∀t∈Icc a b,Continuous (fun p => Ψ p t)) ∧
      (∀t∈Icc a b,((gibbs H).prod (stdGaussian (Point d))).map (fun p => Ψ p t)=
        (gibbs H).prod (stdGaussian (Point d))) := by
  have hi : Integrable (fun z => Real.exp (-H z)) := by
    simpa only [inner_zero_left,zero_sub,smul_eq_mul,mul_one] using
      integrable_tilted H hH.continuous continuous_const ht (growth_const (1:ℝ)) 0
  let := probability_gibbs_of_partition (partition_pos_of_continuous hH.continuous).ne'
    (partition_ne_top_of_integrable hi)
  let K : Point d → Point d →L[ℝ] Point d := fun _ => -(ContinuousLinearMap.id ℝ (Point d))
  let m := fun z => -gradient H z
  have hK : ContDiff ℝ 1 K := contDiff_const
  have hm : ContDiff ℝ 1 m := (Trapezoid.contDiff_gradient hH).neg
  have hKb (y : Point d) : ‖K y‖≤(1:ℝ) := by
    dsimp [K]
    rw [norm_neg]
    exact ContinuousLinearMap.norm_id_le
  have hmL : LipschitzWith L m := hL.neg
  have hμ : Integrable (fun z : Point d => ‖z‖) (gibbs H) := by
    simpa only [pow_one] using (ht.hasExpMoments hH.continuous).hasMoments 1
  have hs : ∀u : Point d,∀φ : Point d → ℝ,ContDiff ℝ 1 φ → HasCompactSupport φ →
      (∫y,inner ℝ u (m y)*φ y ∂gibbs H)=∫y,fderiv ℝ φ y ((K y).adjoint u) ∂gibbs H := by
    intro u φ hφ hφc
    have hh := compact_gibbs_ibp (hH.of_le (by norm_num)) hi hφ hφc u
    dsimp [K,m]
    simp only [map_neg,ContinuousLinearMap.adjoint_id,
      neg_apply,ContinuousLinearMap.id_apply,
      inner_neg_right,neg_mul,integral_neg]
    simpa only [directional,real_inner_comm] using congrArg Neg.neg hh.symm
  obtain ⟨Ψ,hΨ,hc,hlaw⟩ := exists_skew_centering_flow hK hm (by norm_num : (0:ℝ)≤1) hKb hmL hμ hs
    (by norm_num : (0:ℝ)<1) hab
  refine ⟨Ψ,fun p => ⟨(hΨ p).1,(hΨ p).2.1,fun t ht => ?_⟩,hc,hlaw⟩
  simpa only [skewCenteringField,K,m,inv_one,one_smul,neg_apply,
    ContinuousLinearMap.id_apply,neg_neg,map_neg,ContinuousLinearMap.adjoint_id,neg_smul] using (hΨ p).2.2 t ht
end LogConcaveSampling

end

end

end

end OAI
end

section
-- module Solutions.OAIQ048_LC.LogConcave_Dynamics_JointHarmonicFlow
attribute [-instance] _root_.OAI.LogConcaveSampling.LowerBound.couplingLaw_probability _root_.OAI.LogConcaveSampling.LowerBound.remainingHaar_probability _root_.OAI.LogConcaveSampling.LowerBound.roundRandomLaw_probability _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_invInvariant _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_isHaar _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_probability _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_rightInvariant _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_compactSpace _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_measurableInv _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_measurableMul _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_secondCountable _root_.OAI.LogConcaveSampling.MeanTree.instIsProbabilityMeasureRowTapeRowLaw _root_.OAI.LogConcaveSampling.OracleCompiler.topSeedLaw_probability _root_.OAI.LogConcaveSampling.noiseKernel_markov
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
namespace LogConcaveSampling
open Set Function MeasureTheory ProbabilityTheory
open scoped Classical BigOperators RealInnerProductSpace NNReal
open TensorEnergy

theorem exists_joint_harmonic_flow {d : ℕ} {H : Point d → ℝ} {L : ℝ≥0}
    (hH : ContDiff ℝ 2 H) (htail : HasGaussianLowerTail H)
    (hL : LipschitzWith L (gradient H)) :
    ∃Ξ : Point (d+d) → ℝ → Point (d+d),
      (∀y,Continuous (Ξ y) ∧ Ξ y 0=y) ∧
      (∀y t,t∈Icc (0:ℝ) 1 → HasDerivWithinAt (Ξ y)
        (skewLieField (productPotential H (fun z : Point d => ‖z‖^2/2))
          (harmonicSkew d) (Ξ y t)) (Icc (0:ℝ) 1) t) ∧
      Measurable (fun p : ℝ × Point (d+d) => Ξ p.2 p.1) ∧
      (∀t∈Icc (0:ℝ) 1,(gibbs (productPotential H (fun z : Point d => ‖z‖^2/2))).map
        (fun y => Ξ y t)=gibbs (productPotential H (fun z : Point d => ‖z‖^2/2))) := by
  obtain ⟨Ψ,hΨ,hc,hlaw⟩ := exists_harmonic_flow hH htail hL (by norm_num : (0:ℝ)≤1)
  let E := productPointEquiv d d
  let τ : ℝ → ℝ := fun t => min (max t 0) 1
  have hτ : Continuous τ := (continuous_id.max continuous_const).min continuous_const
  have hτmem (t : ℝ) : τ t∈Icc (0:ℝ) 1 :=
    ⟨le_min (le_max_right _ _) (by norm_num),min_le_right _ _⟩
  have hτeq (t : ℝ) (ht : t∈Icc (0:ℝ) 1) : τ t=t := by
    exact (min_eq_left (by rw [max_eq_left ht.1]; exact ht.2)).trans (max_eq_left ht.1)
  let Ξ : Point (d+d) → ℝ → Point (d+d) := fun y t => E.symm (Ψ (E y) (τ t))
  have hΞc (y : Point (d+d)) : Continuous (Ξ y) := E.symm.continuous.comp ((hΨ (E y)).1.comp hτ)
  have hΞs (t : ℝ) : Continuous (fun y => Ξ y t) := E.symm.continuous.comp ((hc (τ t) (hτmem t)).comp E.continuous)
  let μ := gibbs (productPotential H (fun z : Point d => ‖z‖^2/2))
  let ν := (gibbs H).prod (stdGaussian (Point d))
  have hm : μ.map E=ν := by
    rw [productPotential_gibbs hH.continuous (gaussianPotential_polySmooth d).smooth.continuous,
      gaussianPotential_gibbs]
  have hmi : ν.map E.symm=μ := by
    rw [←hm,Measure.map_map E.symm.continuous.measurable E.continuous.measurable]
    simp only [Function.comp_def,ContinuousLinearEquiv.symm_apply_apply,Measure.map_id']
  refine ⟨Ξ,fun y => ⟨hΞc y,?_⟩,?_,?_,?_⟩
  · dsimp [Ξ]
    rw [hτeq 0 ⟨le_rfl,by norm_num⟩,(hΨ (E y)).2.1,E.symm_apply_apply]
  · intro y t ht
    have hd := E.symm.toContinuousLinearMap.hasFDerivAt.comp_hasDerivWithinAt t ((hΨ (E y)).2.2 t ht)
    have hfield := harmonicSkew_field (hH.differentiable (by norm_num)) (E.symm (Ψ (E y) t))
    change E _=((E (E.symm (Ψ (E y) t))).2,-gradient H (E (E.symm (Ψ (E y) t))).1) at hfield
    rw [E.apply_symm_apply] at hfield
    have he := congrArg E.symm hfield
    rw [E.symm_apply_apply] at he
    change HasDerivWithinAt (fun u => E.symm (Ψ (E y) u))
      (E.symm ((Ψ (E y) t).2,-gradient H (Ψ (E y) t).1)) _ _ at hd
    rw [←he] at hd
    have hde := hd.congr (f₁:=Ξ y) (fun u hu => by dsimp [Ξ]; rw [hτeq u hu])
      (by dsimp [Ξ]; rw [hτeq t ht])
    simpa only [Ξ,hτeq t ht] using hde
  · exact measurable_uncurry_of_continuous_of_measurable hΞc (fun t => (hΞs t).measurable)
  · intro t ht
    change μ.map (fun y => E.symm (Ψ (E y) (τ t)))=μ
    rw [hτeq t ht]
    have hc' := hc t ht
    calc
      _ = ((μ.map E).map (fun p => Ψ p t)).map E.symm := by
        rw [Measure.map_map E.symm.continuous.measurable hc'.measurable,
          Measure.map_map (E.symm.continuous.measurable.comp hc'.measurable) E.continuous.measurable]
        rfl
      _ = ν.map E.symm := by rw [hm,hlaw t ht]
      _ = μ := hmi
end LogConcaveSampling

end

end

end

end OAI
end

section
-- module Solutions.OAIQ048_LC.LogConcave_Dynamics_ConditionalHarmonicFlow
attribute [-instance] _root_.OAI.LogConcaveSampling.LowerBound.couplingLaw_probability _root_.OAI.LogConcaveSampling.LowerBound.remainingHaar_probability _root_.OAI.LogConcaveSampling.LowerBound.roundRandomLaw_probability _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_invInvariant _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_isHaar _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_probability _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_rightInvariant _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_compactSpace _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_measurableInv _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_measurableMul _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_secondCountable _root_.OAI.LogConcaveSampling.MeanTree.instIsProbabilityMeasureRowTapeRowLaw _root_.OAI.LogConcaveSampling.OracleCompiler.topSeedLaw_probability _root_.OAI.LogConcaveSampling.noiseKernel_markov
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
namespace LogConcaveSampling
open Set MeasureTheory
open scoped NNReal

theorem exists_conditional_harmonic_flow {d : ℕ} {F : Point d → ℝ} {lam : ℝ≥0}
    (hF : Primitive F lam) (x : Point d) {r T : ℝ} (hr : 0 ≤ r)
    (hl : (lam:ℝ)*r^2≤1/2) (hT0 : 0≤T) (hT1 : T<1) :
    ∃Ξ : Point (d+d) → ℝ → Point (d+d),
      (∀y,Continuous (Ξ y) ∧ Ξ y 0=y) ∧
      (∀y t,t∈Icc (0:ℝ) 1 → HasDerivWithinAt (Ξ y)
        (skewLieField (centeringPotential F x r T) (harmonicSkew d)
          (Ξ y t)) (Icc (0:ℝ) 1) t) ∧
      Measurable (fun p : ℝ × Point (d+d) => Ξ p.2 p.1) ∧
      (∀t∈Icc (0:ℝ) 1,(gibbs (centeringPotential F x r T)).map
        (fun y => Ξ y t)=gibbs (centeringPotential F x r T)) :=
  exists_joint_harmonic_flow
    ((interpolationPotential_smooth hF x hr hl hT0 hT1).of_le (by norm_cast))
    (interpolationPotential_lowerTail hF x hr (by linarith) hT0 hT1)
    (interpolationPotential_gradient_lipschitz hF x hr hl hT0 hT1)

end LogConcaveSampling

end

end

end

end OAI
end

section
-- module Solutions.OAIQ048_LC.LogConcave_Numerics_KernelActionPicardRms
attribute [-instance] _root_.OAI.LogConcaveSampling.LowerBound.couplingLaw_probability _root_.OAI.LogConcaveSampling.LowerBound.remainingHaar_probability _root_.OAI.LogConcaveSampling.LowerBound.roundRandomLaw_probability _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_invInvariant _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_isHaar _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_probability _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_rightInvariant _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_compactSpace _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_measurableInv _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_measurableMul _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_secondCountable _root_.OAI.LogConcaveSampling.MeanTree.instIsProbabilityMeasureRowTapeRowLaw _root_.OAI.LogConcaveSampling.OracleCompiler.topSeedLaw_probability _root_.OAI.LogConcaveSampling.noiseKernel_markov
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
namespace LogConcaveSampling
open Set MeasureTheory ProbabilityTheory RMSIntegral Quadrature
open scoped Classical BigOperators NNReal

theorem kernelActionPicard_rms_oai (n : ℕ) (hn : 0<n) :
    ∃Ap Ah Lp Lh : ℝ≥0,∃C J : ℝ,0≤C ∧ 1≤J ∧ ∃k : ℕ,
      ∀{d : ℕ} {F : Point d → ℝ} {lam : ℝ≥0},∀hF : Primitive F lam,
      ∀(x : Point d) {r : ℝ},∀hr : 0 < r,0<lam → ∀hl : (lam:ℝ)*r^2≤1/2,1≤d →
      ∀{T h : ℝ},∀hT0 : 0<T,∀hT1 : T<1,∀hh : 0<h,h≤Real.log 2 →
      Ap*probabilityMeanLipschitz lam r≤1/2 → Ah*probabilityMeanLipschitz lam r≤1/2 →
      Lp*probabilityMeanLipschitz lam r≤1/2 → Lh*probabilityMeanLipschitz lam r≤1/2 →
      ∀N : ℕ,∀s e : ProbabilityNode T h n,
      let S : Icc (0:ℝ) T := ⟨probabilityNodeTime T h n s,probabilityNodeTime_mem hT0 hT1 hh hn s⟩
      let E : Icc (0:ℝ) T := ⟨probabilityNodeTime T h n e,probabilityNodeTime_mem hT0 hT1 hh hn e⟩
      let μ := gibbs (centeringPotential F x r S)
      let fw := probabilityTransport hF x hr.le hl hT0.le hT1 S E
      ∀R : ℝ,0<R → R^2≤1-T^2 →
      ∀m : ℕ,1 ≤ m → ∀ψ : ℝ,0<ψ → ψ*m≤1 →
      let err := fun y => kernelActionPicard F x r T h ψ n m N s e
        (fw (productPointEquiv d d y).1,(productPointEquiv d d y).2)-kernelTransportAction fw y
      Integrable (fun y => ‖err y‖^2) μ ∧
      (∫y,‖err y‖^2 ∂μ)≤
        2*((∑i,|derivativeWeight (angleNodes m) i/ψ|)*
          (∑i,|derivativeWeight (angleNodes m) i/ψ| *
            kernelValueRmsBudget F x lam Ap Ah Lp r R S h (ψ*angleNodes m i) C J k n N))+
        2*(((∑i,|derivativeWeight (angleNodes m) i|)/ψ)^2*
          (((ψ*m)^(m+1)/(m.factorial:ℝ))^2*
            ((d*((lam:ℝ)*r^2)^2)*(R⁻¹)^(4*(m+1))*harmonicCorrectionBudget (m+1)))) := by
  obtain ⟨Ap,Ah,Lp,Lh,C,J,hC,hJ,k,hNum⟩ := kernelActionPicard_numerical_rms n hn
  refine ⟨Ap,Ah,Lp,Lh,C,J,hC,hJ,k,?_⟩
  intro d F lam hF x r hr hlam hl hd T h hT0 hT1 hh hsmall hqp hqh hqlp hqlh N s e
  dsimp only
  let S : Icc (0:ℝ) T := ⟨probabilityNodeTime T h n s,probabilityNodeTime_mem hT0 hT1 hh hn s⟩
  let E : Icc (0:ℝ) T := ⟨probabilityNodeTime T h n e,probabilityNodeTime_mem hT0 hT1 hh hn e⟩
  let μ := gibbs (centeringPotential F x r S)
  let fw := probabilityTransport hF x hr.le hl hT0.le hT1 S E
  intro R hR hRT m hm1 ψ hψ hψm
  have hRS : R^2≤1-(S:ℝ)^2 := by
    have hs := pow_le_pow_left₀ S.2.1 S.2.2 2
    linarith
  obtain ⟨Ξ,hc,hder,hmeas,hlaw⟩ := exists_conditional_harmonic_flow hF x hr.le hl S.2.1 (S.2.2.trans_lt hT1)
  have hnum := hNum hF x hr hlam hl hd hT0 hT1 hh hsmall hqp hqh hqlp hqlh N s e
    R hR hRS Ξ (fun y => (hc y).1) (fun y => (hc y).2) hder hmeas hlaw m ψ hψ hψm
  have hex := kernel_action_between_stencil_rms hF x hr hlam hl hR hRT hT0.le hT1 S E Ξ
    (fun y => (hc y).2) hder hmeas hlaw m hm1 ψ hψ hψm
  let pos := fun y : Point (d+d) => (productPointEquiv d d y).1
  let mom := fun y : Point (d+d) => (productPointEquiv d d y).2
  let inp := fun y => (fw (pos y),mom y)
  let w := fun z y => pos (Ξ y z)
  let num := fun y => kernelActionPicard F x r T h ψ n m N s e (inp y)
  let mid := fun y => derivativeStencil (angleNodes m) ψ
    (fun i => fw (w (ψ*angleNodes m i) y)-w (ψ*angleNodes m i) y)
  have hpos : Measurable pos := (productPointEquiv d d).continuous.measurable.fst
  have hmom : Measurable mom := (productPointEquiv d d).continuous.measurable.snd
  have hfw : Measurable fw := (probabilityTransport_continuous hF x hr.le hl hT0.le hT1 S E).measurable
  have hinp : Measurable inp := (hfw.comp hpos).prodMk hmom
  have hw (z : ℝ) : Measurable (w z) := hpos.comp (hmeas.comp (measurable_const.prodMk measurable_id))
  have hnm : Measurable num := by
    change Measurable (fun y => ∑i,(derivativeWeight (angleNodes m) i/ψ) •
      kernelCorrectionPicard F x r T h (ψ*angleNodes m i) n N s e (inp y))
    apply Finset.measurable_sum
    intro i _
    have hc : Continuous (fun v : Point d => (derivativeWeight (angleNodes m) i/ψ) • v) := continuous_const_smul _
    exact hc.measurable.comp
      ((kernelCorrectionPicard_continuous hF x hr.le hl hT0 hT1 hh (ψ*angleNodes m i) n hn N s e).measurable.comp hinp)
  have hmid : Measurable mid := by
    apply Finset.measurable_sum
    intro i _
    have hc : Continuous (fun v : Point d => (derivativeWeight (angleNodes m) i/ψ) • v) := continuous_const_smul _
    exact hc.measurable.comp
      ((hfw.comp (hw (ψ*angleNodes m i))).sub (hw (ψ*angleNodes m i)))
  exact add_error_sq hnm hmid hex.1 hnum.1 hex.2.1 hnum.2 hex.2.2
end LogConcaveSampling

end

end

end

end OAI
end

theorem solution : type_of% @OAI.LogConcaveSampling.kernelActionPicard_rms_oai := @OAI.LogConcaveSampling.kernelActionPicard_rms_oai
