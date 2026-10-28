-- Prove2me | solution 1 for OAI.LogConcaveSampling.OracleCompiler.CircuitParameters.sampleFrom_squared
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-27T13:37:34.708138+00:00
-- url     : https://prove2.me/submissions/36de94f9-222e-41e4-8b3b-b3dea6218530

import Mathlib
import Definitions.Def_LogConcaveQuery
import Definitions.Def_OAIQ048L004

section
-- module Solutions.OAIQ048_LC.LogConcave_Dynamics_TriangularEquiv
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
namespace LogConcaveSampling.GlobalODE
open Set Function Filter MeasureTheory
open scoped Topology

theorem transport_expectation_of_flux {d : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsFiniteMeasure μ] {a b : ℝ} (hab : a<b)
    {f : ℝ → Point d → Point d} (hc : Continuous (uncurry f)) {K : ℝ≥0}
    (hL : ∀ t∈Icc a b,LipschitzWith K (f t))
    {D : ℝ → Point d → Point d →L[ℝ] Point d} (hD : Continuous (uncurry D))
    (hf : ∀ t z,HasFDerivAt (f t) (D t z) z)
    {X X' : ℝ → Ω → Point d}
    (hXm : ∀ t,Measurable (X t)) (hXc : ∀ ω,Continuous (fun t => X t ω))
    (hXp : ∀ t∈Ioo a b,∀ ω,HasDerivAt (fun t => X t ω) (X' t ω) t)
    (hX'm : ∀ t,Measurable (X' t))
    {g : Ω → ℝ} (hg : Integrable g μ)
    (hgb : ∀ t∈Ioo a b,∀ ω,‖X' t ω-f t (X t ω)‖≤g ω)
    (hflux : ∀ t∈Ioo a b,∀ S : Point d → Point d →L[ℝ] ℝ,Measurable S →
      (∃ C : ℝ,∀ y,‖S y‖≤C) → (∫ ω,S (X t ω) (X' t ω-f t (X t ω)) ∂μ)=0)
    {φ : Point d → ℝ} (hφ : Differentiable ℝ φ) {L : ℝ≥0} (hφL : LipschitzWith L φ)
    {B : ℝ} (hφB : ∀ z,‖φ z‖≤B) :
    (∫ ω,φ (X b ω) ∂μ) =
      ∫ ω,φ (flow hL hc ⟨a,le_rfl,hab.le⟩ (X a ω) b) ∂μ := by
  let T : Icc a b := ⟨b,hab.le,le_rfl⟩
  let ψ := backwardTest hab.le hc hL T φ
  let S := fun t => fderiv ℝ (fun z => ψ (t,z))
  let U := fun t ω => ψ (t,X t ω)
  let U' := fun t ω => S t (X t ω) (X' t ω-f t (X t ω))
  let C : ℝ := (L:ℝ)*Real.exp ((K:ℝ)*(b-a))
  have hC : 0≤C := by dsimp [C]; positivity
  have hSm : ∀ t,Measurable (S t) := fun t => measurable_fderiv ℝ _
  have hSb : ∀ t y,‖S t y‖≤C := by
    intro t y
    exact norm_fderiv_le_of_lipschitz ℝ (backwardTest_lipschitz hab.le hc hL T hφL t)
  have hψ : Continuous ψ := backwardTest_continuous hab.le hc hL T hφ.continuous
  have hUm : ∀ t,Measurable (U t) := fun t => hψ.measurable.comp (measurable_const.prodMk (hXm t))
  have hUb : ∀ t ω,‖U t ω‖≤B := by intro t ω; exact hφB _
  have hU'm : ∀ t,Measurable (U' t) := by
    intro t
    exact (continuous_fst.clm_apply continuous_snd).measurable.comp
      (((hSm t).comp (hXm t)).prodMk ((hX'm t).sub
        (hc.measurable.comp (measurable_const.prodMk (hXm t)))))
  have hUi : ∀ t,Integrable (U t) μ := fun t =>
    (integrable_const B).mono' (hUm t).aestronglyMeasurable (Eventually.of_forall (hUb t))
  have hU'b : ∀ t∈Ioo a b,∀ ω,‖U' t ω‖≤C*g ω := by
    intro t ht ω
    exact ((S t (X t ω)).le_opNorm _).trans
      ((mul_le_mul_of_nonneg_right (hSb t _) (norm_nonneg _)).trans
        (mul_le_mul_of_nonneg_left (hgb t ht ω) hC))
  have hUd : ∀ t∈Ioo a b,∀ ω,HasDerivAt (fun t => U t ω) (U' t ω) t := by
    intro t ht ω
    exact backwardTest_chain hab.le hc hL hD hf T hφ ht (hXp t ht ω)
  have hQd : ∀ t∈Ioo a b,HasDerivAt (fun t => ∫ ω,U t ω ∂μ) 0 t := by
    intro t ht
    have hh := hasDerivAt_integral_of_dominated_loc_of_deriv_le (F:=U) (F':=U')
      (Ioo_mem_nhds ht.1 ht.2) (Eventually.of_forall fun s => (hUm s).aestronglyMeasurable)
      (hUi t) (hU'm t).aestronglyMeasurable
      (Eventually.of_forall fun ω s hs => hU'b s hs ω) (hg.const_mul C)
      (Eventually.of_forall fun ω s hs => hUd s hs ω)
    have hz := hflux t ht (S t) (hSm t) ⟨C,hSb t⟩
    change (∫ ω,U' t ω ∂μ)=0 at hz
    rw [hz] at hh
    exact hh.2
  have hQc : Continuous (fun t => ∫ ω,U t ω ∂μ) :=
    continuous_of_dominated (fun t => (hUm t).aestronglyMeasurable)
      (fun t => Eventually.of_forall (hUb t)) (integrable_const B)
      (Eventually.of_forall fun ω => hψ.comp (continuous_id.prodMk (hXc ω)))
  obtain ⟨t,ht,he⟩ := exists_deriv_eq_slope (fun t => ∫ ω,U t ω ∂μ) hab hQc.continuousOn
    (fun t ht => (hQd t ht).differentiableAt.differentiableWithinAt)
  rw [(hQd t ht).deriv] at he
  have heq : (∫ ω,U b ω ∂μ)=(∫ ω,U a ω ∂μ) :=
    sub_eq_zero.mp ((div_eq_zero_iff).mp he.symm |>.resolve_right (sub_ne_zero.mpr hab.ne'))
  convert! heq using 1 <;> apply integral_congr_ae <;> filter_upwards [] with ω
  · simp only [U,ψ,backwardTest_eq]
    rw [projIcc_of_mem _ (show b∈Icc a b from ⟨hab.le,le_rfl⟩)]
    exact (congrArg φ (flow_initial hL hc ⟨b,hab.le,le_rfl⟩ (X b ω))).symm
  · simp only [U,ψ,backwardTest_eq]
    rw [projIcc_of_mem _ (show a∈Icc a b from ⟨le_rfl,hab.le⟩)]
end LogConcaveSampling.GlobalODE

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
-- module Solutions.OAIQ048_LC.LogConcave_Sampling_JointInterpolationLaw
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
open MeasureTheory
open scoped RealInnerProductSpace

lemma interpolation_conditional_exponent {d : ℕ} (F : Point d → ℝ) (x : Point d)
    (r ρ : ℝ) (y z : Point d) (ha : 1-ρ^2≠0) :
    -primitivePotential F x r z-‖y-ρ • z‖^2/(2*(1-ρ^2))=
      -‖y‖^2/2-conditionalPotential F x r ρ y z := by
  simp only [primitivePotential,conditionalPotential,norm_sub_sq_real,norm_smul,
    Real.norm_eq_abs,mul_pow,sq_abs,inner_smul_right]
  rw [real_inner_comm z y]
  field_simp
  ring

lemma weighted_integral_zero_of_gibbs {d : ℕ} {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] {H : Point d → ℝ}
    (hc : Continuous H) (hi : Integrable (fun z => Real.exp (-H z)))
    {u : Point d → E} (hu : (∫ z,u z ∂gibbs H)=0) :
    (∫ z,Real.exp (-H z) • u z)=0 := by
  rw [integral_gibbs_vector hc hi] at hu
  exact (smul_eq_zero.mp hu).resolve_left (inv_ne_zero (integral_exp_pos hi).ne')

theorem interpolation_joint_integral_zero {d : ℕ} {F : Point d → ℝ} {lam : ℝ≥0}
    (hF : Primitive F lam) (x : Point d) {r ρ : ℝ} (hr : 0 ≤ r)
    (hl : (lam:ℝ)*r^2≤1/2) (hρ0 : 0≤ρ) (hρ1 : ρ<1)
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {u : Point d × Point d → E}
    (hi : Integrable u (jointInterpolationLaw F x r ρ))
    (hu : ∀ y,(∫ z,u (z,y) ∂gibbs (conditionalPotential F x r ρ y))=0) :
    (∫ p,u p ∂jointInterpolationLaw F x r ρ)=0 := by
  unfold jointInterpolationLaw at hi ⊢
  have ha := (probability_time hρ0 hρ1).1
  have hσ := (Real.sqrt_pos.mpr ha).ne'
  have hp0 := (partition_pos_of_continuous (hF.continuous_potential x r)).ne'
  have hpt := partition_ne_top_of_integrable (hF.integrable_exp_neg_potential x hr (by linarith))
  let c := (partition (primitivePotential F x r))⁻¹*
    EulerDensity.noiseCoefficient d (Real.sqrt (1-ρ^2))
  have hc0 : c≠0 := mul_ne_zero (ENNReal.inv_ne_zero.mpr hpt)
    (EulerDensity.noiseCoefficient_positive d hσ).ne'
  have hct : c≠⊤ := ENNReal.mul_ne_top (ENNReal.inv_ne_top.mpr hp0)
    (EulerDensity.noiseCoefficient_finite _ _)
  let w := fun p : Point d × Point d => Real.exp (-primitivePotential F x r p.1-
    ‖p.2-ρ • p.1‖^2/(2*(1-ρ^2)))
  have hw0 : ∀ p,0≤w p := fun _ => (Real.exp_pos _).le
  have hw : Measurable w := by
    have := (hF.continuous_potential x r).measurable
    dsimp [w]; fun_prop
  have hden : Measurable (fun p => ENNReal.ofReal (w p)) := ENNReal.measurable_ofReal.comp hw
  have hd := EulerDensity.joint_density (hF.continuous_potential x r).measurable
    (fun z => ρ • z) (by fun_prop) hσ
  simp only [Real.sq_sqrt ha.le] at hd
  change _=c • ((volume : Measure (Point d)).prod volume).withDensity
    (fun p => ENNReal.ofReal (w p)) at hd
  rw [hd] at hi ⊢
  have hif : Integrable (fun p => w p • u p) ((volume : Measure (Point d)).prod volume) := by
    have hi' := (integrable_smul_measure hc0 hct).mp hi
    rw [integrable_withDensity_iff_integrable_smul' (hden)
      (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)] at hi'
    simpa only [ENNReal.toReal_ofReal (hw0 _)] using hi'
  rw [integral_smul_measure,integral_withDensity_eq_integral_toReal_smul
    hden (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  simp only [ENNReal.toReal_ofReal (hw0 _)]
  rw [integral_prod_symm _ hif]
  have hz : ∀ y,(∫ z,w (z,y) • u (z,y))=0 := by
    intro y
    have hci := (conditional_hasGaussianLowerTail hF x hr hl hρ0 hρ1 y).integrable_exp
      (conditionalPotential_smooth hF x r ρ y).continuous
    have hh := weighted_integral_zero_of_gibbs
      (conditionalPotential_smooth hF x r ρ y).continuous hci (hu y)
    have he : ∀ z,w (z,y)=Real.exp (-‖y‖^2/2)*Real.exp (-conditionalPotential F x r ρ y z) := by
      intro z; dsimp [w]
      rw [interpolation_conditional_exponent F x r ρ y z ha.ne',sub_eq_add_neg,Real.exp_add]
    simp_rw [he,mul_smul]
    rw [integral_smul,hh,smul_zero]
  simp_rw [hz]
  simp
end LogConcaveSampling

end UpperProof
end
end
end

end OAI
end

section
-- module Solutions.OAIQ048_LC.LogConcave_Sampling_InterpolationResidual
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
open scoped RealInnerProductSpace

lemma primitive_identity_integrable {d : ℕ} {F : Point d → ℝ} {lam : ℝ≥0}
    (hF : Primitive F lam) (x : Point d) {r : ℝ} (hr : 0 ≤ r) (hl : (lam:ℝ)*r^2<1) :
    Integrable (fun z => z) (gibbs (primitivePotential F x r)) := by
  let := probability_gibbs_of_partition
    (partition_pos_of_continuous (hF.continuous_potential x r)).ne'
    (partition_ne_top_of_integrable (hF.integrable_exp_neg_potential x hr hl))
  exact (Appell.HasGrowth.lipschitz (LipschitzWith.id (α:=Point d))).integrable
    continuous_id.aestronglyMeasurable (hF.hasExpMoments x hr hl).hasMoments

lemma interpolationResidual_integrable {d : ℕ} {F : Point d → ℝ} {lam : ℝ≥0}
    (hF : Primitive F lam) (x : Point d) {r ρ : ℝ} (hr : 0 ≤ r)
    (hl : (lam:ℝ)*r^2≤1/2) (hρ0 : 0≤ρ) (hρ1 : ρ<1) :
    Integrable (interpolationResidual F x r ρ) (jointInterpolationLaw F x r ρ) := by
  let μ := gibbs (primitivePotential F x r)
  let ν := stdGaussian (Point d)
  let := probability_gibbs_of_partition
    (partition_pos_of_continuous (hF.continuous_potential x r)).ne'
    (partition_ne_top_of_integrable (hF.integrable_exp_neg_potential x hr (by linarith)))
  have hi := primitive_identity_integrable hF x hr (by linarith : (lam:ℝ)*r^2<1)
  have hz : Integrable (fun p : Point d × Point d => p.1) (μ.prod ν) := hi.comp_fst ν
  have hg : Integrable (fun p : Point d × Point d => p.2) (μ.prod ν) :=
    (IsGaussian.integrable_id (μ:=ν)).comp_snd μ
  have hy := (hz.smul ρ).add (hg.smul (Real.sqrt (1-ρ^2)))
  have hM := conditionalFieldMean_lipschitz hF x hr hl hρ0 hρ1
  have hm := integrable_lipschitz_comp_of_integrable hy hM
  have hu := ((hz.sub (hy.smul ρ)).smul (1/(1-ρ^2))).add (hm.smul r)
  have hc : Continuous (interpolationResidual F x r ρ) := by
    unfold interpolationResidual
    exact ((continuous_fst.sub (continuous_snd.const_smul ρ)).const_smul (1/(1-ρ^2))).add
      ((hM.continuous.comp continuous_snd).const_smul r)
  apply (integrable_map_measure hc.aestronglyMeasurable (by fun_prop)).2
  exact hu

lemma conditional_residual_zero {d : ℕ} {F : Point d → ℝ} {lam : ℝ≥0}
    (hF : Primitive F lam) (x : Point d) {r ρ : ℝ} (hr : 0 ≤ r)
    (hl : (lam:ℝ)*r^2≤1/2) (hρ0 : 0≤ρ) (hρ1 : ρ<1) (y : Point d) :
    (∫ z,interpolationResidual F x r ρ (z,y) ∂gibbs (conditionalPotential F x r ρ y))=0 := by
  let := conditionalLaw_probability hF x hr hl hρ0 hρ1 y
  have hi := conditional_identity_integrable hF x hr hl hρ0 hρ1 y
  have hh := integral_scaled_affine_add hi (integrable_const
    (conditionalFieldMean F x r ρ y)) (1/(1-ρ^2)) r (ρ • y)
  rw [show (∫ z,interpolationResidual F x r ρ (z,y) ∂gibbs (conditionalPotential F x r ρ y))=
      (1/(1-ρ^2)) • ((∫ z,z ∂gibbs (conditionalPotential F x r ρ y))-ρ • y)+
        r • (∫ _,conditionalFieldMean F x r ρ y ∂gibbs (conditionalPotential F x r ρ y)) from hh,
    integral_const,probReal_univ,one_smul,conditional_mean_identity hF x hr hl hρ0 hρ1]
  have ha := (probability_time hρ0 hρ1).1
  rw [sub_sub_cancel_left,smul_neg,smul_smul]
  have he : 1/(1-ρ^2)*((1-ρ^2)*r)=r := by field_simp
  rw [he,neg_add_cancel]

lemma integrable_scaled_affine_const {d : ℕ} {μ : Measure (Point d)} [IsFiniteMeasure μ]
    (hi : Integrable (fun z => z) μ) (c : ℝ) (a b : Point d) :
    Integrable (fun z => c • (z-a)+b) μ :=
  ((hi.sub (integrable_const a)).smul c).add (integrable_const b)

lemma conditional_residual_integrable {d : ℕ} {F : Point d → ℝ} {lam : ℝ≥0}
    (hF : Primitive F lam) (x : Point d) {r ρ : ℝ} (hr : 0 ≤ r)
    (hl : (lam:ℝ)*r^2≤1/2) (hρ0 : 0≤ρ) (hρ1 : ρ<1) (y : Point d) :
    Integrable (fun z => interpolationResidual F x r ρ (z,y))
      (gibbs (conditionalPotential F x r ρ y)) := by
  let := conditionalLaw_probability hF x hr hl hρ0 hρ1 y
  exact integrable_scaled_affine_const (conditional_identity_integrable hF x hr hl hρ0 hρ1 y)
    (1/(1-ρ^2)) (ρ • y) (r • conditionalFieldMean F x r ρ y)

theorem interpolation_flux_zero {d : ℕ} {F : Point d → ℝ} {lam : ℝ≥0}
    (hF : Primitive F lam) (x : Point d) {r ρ : ℝ} (hr : 0 ≤ r)
    (hl : (lam:ℝ)*r^2≤1/2) (hρ0 : 0≤ρ) (hρ1 : ρ<1)
    {T : Point d → Point d →L[ℝ] ℝ} (hT : Measurable T)
    {C : ℝ} (hC : ∀ y,‖T y‖≤C) :
    (∫ p,T p.2 (interpolationResidual F x r ρ p) ∂jointInterpolationLaw F x r ρ)=0 := by
  have hi := interpolationResidual_integrable hF x hr hl hρ0 hρ1
  have hM := conditionalFieldMean_lipschitz hF x hr hl hρ0 hρ1
  have hc : Continuous (interpolationResidual F x r ρ) := by
    unfold interpolationResidual
    exact ((continuous_fst.sub (continuous_snd.const_smul ρ)).const_smul (1/(1-ρ^2))).add
      ((hM.continuous.comp continuous_snd).const_smul r)
  have hm : Measurable (fun p => T p.2 (interpolationResidual F x r ρ p)) :=
    (continuous_fst.clm_apply continuous_snd).measurable.comp
      ((hT.comp measurable_snd).prodMk hc.measurable)
  apply interpolation_joint_integral_zero hF x hr hl hρ0 hρ1
  · refine (hi.norm.const_mul C).mono' hm.aestronglyMeasurable (Filter.Eventually.of_forall fun p => ?_)
    exact ((T p.2).le_opNorm _).trans (mul_le_mul_of_nonneg_right (hC p.2) (norm_nonneg _))
  · intro y
    have hrz := conditional_residual_integrable hF x hr hl hρ0 hρ1 y
    rw [(T y).integral_comp_comm hrz,conditional_residual_zero hF x hr hl hρ0 hρ1,map_zero]
end LogConcaveSampling

open Function MeasureTheory Set Filter
open scoped Topology NNReal

end UpperProof
end
end
end

end OAI
end

section
-- module Solutions.OAIQ048_LC.LogConcave_Sampling_ProbabilityVelocity
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
open Set Function MeasureTheory Filter
open scoped Topology

lemma clampedProbabilityDerivative_continuous {d : ℕ} {F : Point d → ℝ} {lam : ℝ≥0}
    (hF : Primitive F lam) (x : Point d) {r T : ℝ} (hr : 0 ≤ r)
    (hl : (lam:ℝ)*r^2≤1/2) (hT0 : 0≤T) (hT1 : T<1) :
    Continuous (uncurry (clampedProbabilityDerivative F x r T hT0)) := by
  apply continuous_iff_continuousAt.mpr
  intro p
  have hcm := (projIcc 0 T hT0 p.1).2
  have hp : (projIcc 0 T hT0 p.1:ℝ)^2<1 := by
    have hh := (probability_time hcm.1 (hcm.2.trans_lt hT1)).1
    linarith
  have hh := (probabilityVelocity_joint_smooth hF x hr (by linarith) (_,p.2) hp).continuousAt_fderiv
    (by simp)
  exact (hh.comp (f:=fun q : ℝ × Point d => ((projIcc 0 T hT0 q.1:ℝ),q.2)) ((continuous_subtype_val.comp (continuous_projIcc.comp continuous_fst)).continuousAt.prodMk
    continuous_snd.continuousAt)).clm_comp continuousAt_const

lemma clampedProbabilityVelocity_hasFDerivAt {d : ℕ} {F : Point d → ℝ} {lam : ℝ≥0}
    (hF : Primitive F lam) (x : Point d) {r T : ℝ} (hr : 0 ≤ r)
    (hl : (lam:ℝ)*r^2≤1/2) (hT0 : 0≤T) (hT1 : T<1) (t : ℝ) (z : Point d) :
    HasFDerivAt (clampedProbabilityVelocity F x r T hT0 t)
      (clampedProbabilityDerivative F x r T hT0 t z) z := by
  have hcm := (projIcc 0 T hT0 t).2
  have hp : (projIcc 0 T hT0 t:ℝ)^2<1 := by
    have hh := (probability_time hcm.1 (hcm.2.trans_lt hT1)).1
    linarith
  have hh := (probabilityVelocity_joint_smooth hF x hr (by linarith) (_,z) hp).differentiableAt
    (by simp)
  convert! hh.hasFDerivAt.comp z ((hasFDerivAt_const (projIcc 0 T hT0 t:ℝ) z).prodMk
    (hasFDerivAt_id z)) using 1
  all_goals try with_reducible_and_instances rfl

end LogConcaveSampling
namespace LogConcaveSampling
open Set Function MeasureTheory
open scoped Topology

lemma interpolationPath_continuous {d : ℕ} (p : Point d × Point d) :
    Continuous (fun t => interpolationPath t p) := by unfold interpolationPath; fun_prop

lemma interpolationPath_measurable {d : ℕ} (t : ℝ) :
    Measurable (interpolationPath (d:=d) t) := by unfold interpolationPath; fun_prop

lemma interpolationPathDerivative_measurable {d : ℕ} (t : ℝ) :
    Measurable (interpolationPathDerivative (d:=d) t) := by unfold interpolationPathDerivative; fun_prop

lemma interpolationPath_hasDerivAt {d : ℕ} {t : ℝ} (ht : t^2<1) (p : Point d × Point d) :
    HasDerivAt (fun t => interpolationPath t p) (interpolationPathDerivative t p) t := by
  have hs₀ : HasDerivAt (fun t : ℝ => 1-t^2) (-2*t) t := by
    convert! (hasDerivAt_const t (1:ℝ)).sub ((hasDerivAt_id t).pow 2) using 1; simp
  have hs := hs₀.sqrt (show 1-t^2≠0 by linarith)
  have hh := ((hasDerivAt_id t).smul_const p.1).add (hs.smul_const p.2)
  convert! hh using 1
  all_goals try with_reducible_and_instances rfl
  simp only [one_smul,interpolationPathDerivative]
  rw [sub_eq_add_neg,←neg_smul]
  congr 1
  congr 1
  ring

lemma interpolationPath_norm_le {d : ℕ} {t T : ℝ} (hT : T≤1) (ht : t∈Icc 0 T)
    (p : Point d × Point d) : ‖interpolationPath t p‖≤‖p.1‖+‖p.2‖ := by
  have ht1 := ht.2.trans hT
  have hs0 := Real.sqrt_nonneg (1-t^2)
  have hs1 : Real.sqrt (1-t^2)≤1 := by
    rw [Real.sqrt_le_one]
    nlinarith [sq_nonneg t]
  calc
    _ ≤ ‖t • p.1‖+‖Real.sqrt (1-t^2) • p.2‖ := norm_add_le _ _
    _ = t*‖p.1‖+Real.sqrt (1-t^2)*‖p.2‖ := by
      simp [norm_smul,Real.norm_eq_abs,abs_of_nonneg ht.1,abs_of_nonneg hs0]
    _ ≤ _ := by nlinarith [norm_nonneg p.1,norm_nonneg p.2]

lemma interpolationPathDerivative_norm_le {d : ℕ} {t T : ℝ} (hT0 : 0≤T) (hT1 : T<1)
    (ht : t∈Icc 0 T) (p : Point d × Point d) :
    ‖interpolationPathDerivative t p‖≤‖p.1‖+(1/Real.sqrt (1-T^2))*‖p.2‖ := by
  have hT : 0<1-T^2 := by nlinarith
  have hs : Real.sqrt (1-T^2)≤Real.sqrt (1-t^2) := by apply Real.sqrt_le_sqrt; nlinarith [ht.1,ht.2]
  have hdiv : t/Real.sqrt (1-t^2)≤1/Real.sqrt (1-T^2) := by
    calc
      _ ≤ 1/Real.sqrt (1-t^2) := div_le_div_of_nonneg_right (ht.2.trans hT1.le) (Real.sqrt_nonneg _)
      _ ≤ _ := one_div_le_one_div_of_le (Real.sqrt_pos.mpr hT) hs
  calc
    _ ≤ ‖p.1‖+‖(t/Real.sqrt (1-t^2)) • p.2‖ := norm_sub_le _ _
    _ = ‖p.1‖+(t/Real.sqrt (1-t^2))*‖p.2‖ := by
      rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg (div_nonneg ht.1 (Real.sqrt_nonneg _))]
    _ ≤ _ := by gcongr

lemma interpolationPath_residual {d : ℕ} {t : ℝ} (ht : t^2<1) (p : Point d × Point d) :
    interpolationPathDerivative t p=(1/(1-t^2)) • (p.1-t • interpolationPath t p) := by
  have ha : 1-t^2≠0 := by linarith
  have hs : Real.sqrt (1-t^2)≠0 := (Real.sqrt_pos.mpr (by linarith)).ne'
  have he₁ : 1/(1-t^2)-(1/(1-t^2))*t*t=1 := by field_simp
  have he₂ : (1/(1-t^2))*t*Real.sqrt (1-t^2)=t/Real.sqrt (1-t^2) := by
    field_simp
    rw [Real.sq_sqrt (show 0≤1-t^2 by linarith)]
  unfold interpolationPathDerivative interpolationPath
  simp only [smul_add,smul_sub,smul_smul]
  rw [sub_add_eq_sub_sub,←mul_assoc,←mul_assoc,←sub_smul,he₁,one_smul,he₂]
end LogConcaveSampling
namespace LogConcaveSampling
open Set Function MeasureTheory Filter ProbabilityTheory
open scoped Topology

lemma interpolationPath_defect {d : ℕ} {F : Point d → ℝ} (x : Point d) (r : ℝ)
    {t : ℝ} (ht : t^2<1) (p : Point d × Point d) :
    interpolationPathDerivative t p-probabilityVelocity F x r t (interpolationPath t p)=
      interpolationResidual F x r t (p.1,interpolationPath t p) := by
  rw [interpolationPath_residual ht]
  simp [probabilityVelocity,interpolationResidual,sub_eq_add_neg]

lemma interpolationPath_flux {d : ℕ} {F : Point d → ℝ} {lam : ℝ≥0}
    (hF : Primitive F lam) (x : Point d) {r t : ℝ} (hr : 0 ≤ r)
    (hl : (lam:ℝ)*r^2≤1/2) (ht0 : 0≤t) (ht1 : t<1)
    {S : Point d → Point d →L[ℝ] ℝ} (hS : Measurable S)
    {C : ℝ} (hC : ∀ y,‖S y‖≤C) :
    (∫ p,S (interpolationPath t p)
      (interpolationPathDerivative t p-probabilityVelocity F x r t (interpolationPath t p))
      ∂(gibbs (primitivePotential F x r)).prod (stdGaussian (Point d)))=0 := by
  have ht : t^2<1 := by have hh := (probability_time ht0 ht1).1; linarith
  simp_rw [interpolationPath_defect x r ht]
  have hM := conditionalFieldMean_lipschitz hF x hr hl ht0 ht1
  have hc : Continuous (interpolationResidual F x r t) := by
    unfold interpolationResidual
    exact ((continuous_fst.sub (continuous_snd.const_smul t)).const_smul (1/(1-t^2))).add
      ((hM.continuous.comp continuous_snd).const_smul r)
  have hm : Measurable (fun p : Point d × Point d => S p.2 (interpolationResidual F x r t p)) :=
    (continuous_fst.clm_apply continuous_snd).measurable.comp
      ((hS.comp measurable_snd).prodMk hc.measurable)
  have hh := interpolation_flux_zero hF x hr hl ht0 ht1 hS hC
  rw [jointInterpolationLaw,integral_map (by fun_prop) hm.aestronglyMeasurable] at hh
  exact hh

lemma interpolationPath_defect_bound {d : ℕ} {F : Point d → ℝ} {lam : ℝ≥0}
    (hF : Primitive F lam) (x : Point d) {r T : ℝ} (hr : 0 ≤ r)
    (hl : (lam:ℝ)*r^2≤1/2) (hT0 : 0≤T) (hT1 : T<1) :
    ∃ g : Point d × Point d → ℝ,
      Integrable g ((gibbs (primitivePotential F x r)).prod (stdGaussian (Point d))) ∧
      ∀ t∈Icc 0 T,∀ p,‖interpolationPathDerivative t p-
        clampedProbabilityVelocity F x r T hT0 t (interpolationPath t p)‖≤g p := by
  let f := clampedProbabilityVelocity F x r T hT0
  let K : ℝ≥0 := ⟨(Real.pi^2/2)*(lam:ℝ)*r^2,by positivity⟩
  have hc := clampedProbabilityVelocity_continuous hF x hr hl hT0 hT1
  have hL : ∀ t,LipschitzWith K (f t) := clampedProbabilityVelocity_lipschitz hF x hr hl hT0 hT1
  obtain ⟨C,hC⟩ := isCompact_Icc.exists_bound_of_continuousOn
    ((hc.comp (continuous_id.prodMk continuous_const)).continuousOn : ContinuousOn (fun t => f t 0) (Icc 0 T))
  let μ := gibbs (primitivePotential F x r)
  let ν := stdGaussian (Point d)
  let := probability_gibbs_of_partition
    (partition_pos_of_continuous (hF.continuous_potential x r)).ne'
    (partition_ne_top_of_integrable (hF.integrable_exp_neg_potential x hr (by linarith)))
  have hz : Integrable (fun p : Point d × Point d => ‖p.1‖) (μ.prod ν) :=
    ((primitive_identity_integrable hF x hr (by linarith)).comp_fst ν).norm
  have hg : Integrable (fun p : Point d × Point d => ‖p.2‖) (μ.prod ν) :=
    ((IsGaussian.integrable_id (μ:=ν)).comp_snd μ).norm
  let g : Point d × Point d → ℝ := fun p =>
    ‖p.1‖+(1/Real.sqrt (1-T^2))*‖p.2‖+C+(K:ℝ)*(‖p.1‖+‖p.2‖)
  refine ⟨g,((hz.add (hg.const_mul _)).add (integrable_const C)).add ((hz.add hg).const_mul _),?_⟩
  intro t ht p
  have hfl := (hL t).dist_le_mul (interpolationPath t p) 0
  rw [dist_eq_norm,dist_zero_right] at hfl
  have hfb : ‖f t (interpolationPath t p)‖≤C+(K:ℝ)*(‖p.1‖+‖p.2‖) := by
    exact (norm_le_norm_add_norm_sub' _ _).trans
      (add_le_add (hC t ht) (hfl.trans (mul_le_mul_of_nonneg_left
        (interpolationPath_norm_le hT1.le ht p) K.coe_nonneg)))
  exact (norm_sub_le _ _).trans (add_le_add
    (interpolationPathDerivative_norm_le hT0 hT1 ht p) hfb) |>.trans_eq (by dsimp [g]; ring)

lemma probabilityFlow_continuous {d : ℕ} {F : Point d → ℝ} {lam : ℝ≥0}
    (hF : Primitive F lam) (x : Point d) {r T : ℝ} (hr : 0 ≤ r)
    (hl : (lam:ℝ)*r^2≤1/2) (hT0 : 0≤T) (hT1 : T<1) :
    Continuous (probabilityFlow hF x hr hl hT0 hT1) :=
  (GlobalODE.flow_lipschitz _ _ ⟨0,le_rfl,hT0⟩ ⟨T,hT0,le_rfl⟩).continuous
end LogConcaveSampling

end UpperProof
end
end
end

end OAI
end

section
-- module Solutions.OAIQ048_LC.LogConcave_Dynamics_ProbabilityFlowIntegral
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
open Set Function MeasureTheory Filter ProbabilityTheory
open scoped Topology

theorem probabilityFlow_integral {d : ℕ} {F : Point d → ℝ} {lam : ℝ≥0}
    (hF : Primitive F lam) (x : Point d) {r T : ℝ} (hr : 0 ≤ r)
    (hl : (lam:ℝ)*r^2≤1/2) (hT0 : 0<T) (hT1 : T<1)
    {φ : Point d → ℝ} (hφ : Differentiable ℝ φ) {L : ℝ≥0} (hφL : LipschitzWith L φ)
    {B : ℝ} (hφB : ∀ z,‖φ z‖≤B) :
    (∫ y,φ y ∂interpolationLaw F x r T) =
      ∫ z,φ (probabilityFlow hF x hr hl hT0.le hT1 z) ∂stdGaussian (Point d) := by
  let μ := gibbs (primitivePotential F x r)
  let ν := stdGaussian (Point d)
  let := probability_gibbs_of_partition
    (partition_pos_of_continuous (hF.continuous_potential x r)).ne'
    (partition_ne_top_of_integrable (hF.integrable_exp_neg_potential x hr (by linarith)))
  have hc := clampedProbabilityVelocity_continuous hF x hr hl hT0.le hT1
  have hL := fun t (_ : t∈Icc 0 T) => clampedProbabilityVelocity_lipschitz hF x hr hl hT0.le hT1 t
  obtain ⟨g,hg,hgb⟩ := interpolationPath_defect_bound hF x hr hl hT0.le hT1
  have hh := GlobalODE.transport_expectation_of_flux (μ:=μ.prod ν) hT0 hc hL
    (clampedProbabilityDerivative_continuous hF x hr hl hT0.le hT1)
    (clampedProbabilityVelocity_hasFDerivAt hF x hr hl hT0.le hT1)
    (X:=interpolationPath) (X':=interpolationPathDerivative)
    interpolationPath_measurable interpolationPath_continuous
    (fun t ht p => interpolationPath_hasDerivAt (by
      have hh := (probability_time ht.1.le (ht.2.trans hT1)).1; linarith) p)
    interpolationPathDerivative_measurable hg (fun t ht => hgb t ⟨ht.1.le,ht.2.le⟩)
    (fun t ht S hS ⟨C,hC⟩ => by
      simp_rw [clampedProbabilityVelocity_eq F x r T hT0.le ⟨ht.1.le,ht.2.le⟩]
      exact interpolationPath_flux hF x hr hl ht.1.le (ht.2.trans hT1) hS hC)
    hφ hφL hφB
  have hfc := probabilityFlow_continuous hF x hr hl hT0.le hT1
  have he := integral_map (μ:=μ.prod ν) measurable_snd.aemeasurable
    (hφ.continuous.comp hfc).aestronglyMeasurable
  rw [Measure.map_snd_prod,measure_univ,one_smul] at he
  change (∫ y,φ y ∂(μ.prod ν).map (interpolationPath T))=_
  rw [integral_map (interpolationPath_measurable T).aemeasurable hφ.continuous.aestronglyMeasurable]
  change (∫ p,φ (interpolationPath T p) ∂μ.prod ν)=_
  rw [hh]
  trans ∫ p,φ (probabilityFlow hF x hr hl hT0.le hT1 p.2) ∂μ.prod ν
  · apply integral_congr_ae
    filter_upwards [] with p
    rw [show interpolationPath 0 p=p.2 by simp [interpolationPath]]
    rfl
  · exact he.symm
end LogConcaveSampling

end UpperProof
end
end
end

end OAI
end

section
-- module Solutions.OAIQ048_LC.LogConcave_Dynamics_ProbabilityFlowPushforward
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
open MeasureTheory ProbabilityTheory

theorem probabilityFlow_pushforward {d : ℕ} {F : Point d → ℝ} {lam : ℝ≥0}
    (hF : Primitive F lam) (x : Point d) {r T : ℝ} (hr : 0 ≤ r)
    (hl : (lam:ℝ)*r^2≤1/2) (hT0 : 0<T) (hT1 : T<1) :
    (stdGaussian (Point d)).map (probabilityFlow hF x hr hl hT0.le hT1)=
      interpolationLaw F x r T := by
  let := probability_gibbs_of_partition
    (partition_pos_of_continuous (hF.continuous_potential x r)).ne'
    (partition_ne_top_of_integrable (hF.integrable_exp_neg_potential x hr (by linarith)))
  have hc := probabilityFlow_continuous hF x hr hl hT0.le hT1
  let hprob : IsProbabilityMeasure (interpolationLaw F x r T) := by
    unfold interpolationLaw
    first | infer_instance | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | (apply Measurable.aemeasurable; measurability) | measurability)
  apply measure_eq_of_smooth_lipschitz
  intro φ hφ ⟨L,hL⟩ ⟨B,hB⟩
  rw [integral_map hc.measurable.aemeasurable hφ.continuous.aestronglyMeasurable]
  exact (probabilityFlow_integral hF x hr hl hT0 hT1 (hφ.differentiable (by norm_num)) hL hB).symm
end LogConcaveSampling

end UpperProof
end
end
end

end OAI
end

section
-- module Solutions.OAIQ048_LC.LogConcave_Sampling_ClosedFieldMean
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
open Set Filter Function
open scoped Topology

lemma fullProbabilityVelocity_eq {d : ℕ} (F : Point d → ℝ) (x : Point d) (r : ℝ)
    {t : ℝ} (ht0 : 0≤t) (ht1 : t<1) (z : Point d) :
    fullProbabilityVelocity F x r t z=probabilityVelocity F x r t z := by
  simp only [fullProbabilityVelocity,projIcc_of_mem _ ⟨ht0,ht1.le⟩,closedFieldMean,ite_eq_left ht1,probabilityVelocity]

end LogConcaveSampling

end UpperProof
end
end
end

end OAI
end

section
-- module Solutions.OAIQ048_LC.LogConcave_Dynamics_FullProbabilityFlow
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
open Set Function MeasureTheory Filter ProbabilityTheory
open scoped Topology

lemma fullProbabilityFlow_time_continuous {d : ℕ} {F : Point d → ℝ} {lam : ℝ≥0}
    (hF : Primitive F lam) (x : Point d) {r : ℝ} (hr : 0 ≤ r)
    (hl : (lam:ℝ)*r^2≤1/2) (z : Point d) : Continuous (fun t => fullProbabilityFlow hF x hr hl t z) :=
  GlobalODE.flow_continuous _ _ _ _

lemma fullProbabilityFlow_lipschitz {d : ℕ} {F : Point d → ℝ} {lam : ℝ≥0}
    (hF : Primitive F lam) (x : Point d) {r t : ℝ} (hr : 0 ≤ r)
    (hl : (lam:ℝ)*r^2≤1/2) (ht : t∈Icc 0 1) :
    LipschitzWith ⟨Real.exp (((Real.pi^2/2)*(lam:ℝ)*r^2)*|t|),(Real.exp_pos _).le⟩
      (fullProbabilityFlow hF x hr hl t) := by
  apply LipschitzWith.of_dist_le_mul
  intro u v
  have hh := GlobalODE.trajectory_dist (a:=0) (b:=1)
    (fun t _ => fullProbabilityVelocity_lipschitz hF x hr hl t)
    (fullProbabilityFlow_time_continuous hF x hr hl u).continuousOn
    (GlobalODE.flow_deriv (a:=0) (b:=1)
      (fun t _ => fullProbabilityVelocity_lipschitz hF x hr hl t)
      (fullProbabilityVelocity_continuous hF x hr hl) ⟨0,le_rfl,by norm_num⟩ u)
    (fullProbabilityFlow_time_continuous hF x hr hl v).continuousOn
    (GlobalODE.flow_deriv (a:=0) (b:=1)
      (fun t _ => fullProbabilityVelocity_lipschitz hF x hr hl t)
      (fullProbabilityVelocity_continuous hF x hr hl) ⟨0,le_rfl,by norm_num⟩ v)
    ⟨0,le_rfl,by norm_num⟩ ⟨t,ht⟩
  have hu0 : fullProbabilityFlow hF x hr hl 0 u=u := GlobalODE.flow_initial _ _ _ _
  have hv0 : fullProbabilityFlow hF x hr hl 0 v=v := GlobalODE.flow_initial _ _ _ _
  change dist (fullProbabilityFlow hF x hr hl t u) (fullProbabilityFlow hF x hr hl t v) ≤
    dist (fullProbabilityFlow hF x hr hl 0 u) (fullProbabilityFlow hF x hr hl 0 v)*_ at hh
  rw [hu0,hv0,sub_zero,mul_comm] at hh
  exact hh

lemma fullProbabilityFlow_eq {d : ℕ} {F : Point d → ℝ} {lam : ℝ≥0}
    (hF : Primitive F lam) (x : Point d) {r T : ℝ} (hr : 0 ≤ r)
    (hl : (lam:ℝ)*r^2≤1/2) (hT0 : 0≤T) (hT1 : T<1) :
    fullProbabilityFlow hF x hr hl T=probabilityFlow hF x hr hl hT0 hT1 := by
  funext z
  let α := fun t => fullProbabilityFlow hF x hr hl t z
  let hL := fun t (_ : t∈Icc 0 T) => clampedProbabilityVelocity_lipschitz hF x hr hl hT0 hT1 t
  let hc := clampedProbabilityVelocity_continuous hF x hr hl hT0 hT1
  let β := GlobalODE.flow hL hc ⟨0,le_rfl,hT0⟩ z
  have hsub : Icc (0:ℝ) T ⊆ Icc 0 1 := Icc_subset_Icc_right hT1.le
  have hdα : ∀ t∈Icc (0:ℝ) T, HasDerivWithinAt α
      (clampedProbabilityVelocity F x r T hT0 t (α t)) (Icc 0 T) t := by
    intro t ht
    have hh := GlobalODE.flow_deriv (a:=0) (b:=1)
      (fun t _ => fullProbabilityVelocity_lipschitz hF x hr hl t)
      (fullProbabilityVelocity_continuous hF x hr hl) ⟨0,le_rfl,by norm_num⟩ z t (hsub ht)
    have he : fullProbabilityVelocity F x r t=clampedProbabilityVelocity F x r T hT0 t := by
      funext y
      rw [fullProbabilityVelocity_eq F x r ht.1 (ht.2.trans_lt hT1),clampedProbabilityVelocity_eq F x r T hT0 ht]
    rw [he] at hh
    exact hh.mono hsub
  have hh := GlobalODE.trajectory_dist hL
    (fullProbabilityFlow_time_continuous hF x hr hl z).continuousOn hdα
    (GlobalODE.flow_continuous hL hc ⟨0,le_rfl,hT0⟩ z).continuousOn
    (GlobalODE.flow_deriv hL hc ⟨0,le_rfl,hT0⟩ z)
    ⟨0,le_rfl,hT0⟩ ⟨T,hT0,le_rfl⟩
  have ha0 : α 0=z := GlobalODE.flow_initial _ _ _ _
  have hb0 : β 0=z := GlobalODE.flow_initial _ _ _ _
  change dist (α T) (β T)≤dist (α 0) (β 0)*_ at hh
  rw [ha0,hb0,dist_self,zero_mul,dist_le_zero] at hh
  exact hh

end LogConcaveSampling

end UpperProof
end
end
end

end OAI
end

section
-- module Solutions.OAIQ048_LC.LogConcave_Sampling_MeanMaterialL2
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
open scoped Classical BigOperators NNReal RealInnerProductSpace

lemma fullProbabilityFlow_interpolation {d : ℕ} {F : Point d → ℝ} {lam : ℝ≥0}
    (hF : Primitive F lam) (x : Point d) {r ρ : ℝ} (hr : 0 ≤ r)
    (hl : (lam:ℝ)*r^2≤1/2) (h0 : 0<ρ) (h1 : ρ<1) :
    (stdGaussian (Point d)).map (fullProbabilityFlow hF x hr hl ρ)=interpolationLaw F x r ρ := by
  rw [fullProbabilityFlow_eq hF x hr hl h0.le h1]
  exact probabilityFlow_pushforward hF x hr hl h0 h1
end LogConcaveSampling

end

end

end

end OAI
end

section
-- module Solutions.OAIQ048_LC.LogConcave_Analysis_PoincareVectorVariance
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
open MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace NNReal

theorem poincare_vector_variance {d e : ℕ} {μ : Measure (Point d)}
    [IsProbabilityMeasure μ] {β : ℝ} (hβ : 0≤β) (hP : HasPoincare μ β)
    (hm : Appell.HasMoments μ) {f : Point d → Point e} {K : ℝ≥0}
    (hf : ContDiff ℝ 1 f) (hK : LipschitzWith K f) :
    Integrable (fun z => ‖f z-∫w,f w ∂μ‖^2) μ ∧
      (∫z,‖f z-∫w,f w ∂μ‖^2 ∂μ)≤(e:ℝ)*β*(K:ℝ)^2 := by
  classical
  let b := EuclideanSpace.basisFun (Fin e) ℝ
  have hi : Integrable f μ := (Appell.HasGrowth.lipschitz hK).integrable hf.continuous.aestronglyMeasurable hm
  have hg : Appell.HasGrowth (fun z => f z-∫w,f w ∂μ) := by
    simpa only [sub_eq_add_neg] using (Appell.HasGrowth.lipschitz hK).add
      (Appell.HasGrowth.const (-(∫w,f w ∂μ)))
  have hisq := (hg.norm.pow 2).integrable ((hf.continuous.sub continuous_const).norm.pow 2).aestronglyMeasurable hm
  have hmj (j : Fin e) : MemLp (fun z => inner ℝ (b j) (f z)) 2 μ :=
    (Appell.HasGrowth.lipschitz ((innerSL ℝ (b j)).lipschitz.comp hK)).memLp
      (by fun_prop) hm
  have hei (j : Fin e) : Integrable (fun z => (inner ℝ (b j) (f z-∫w,f w ∂μ))^2) μ := by
    have h := (hmj j).sub (memLp_const (inner ℝ (b j) (∫w,f w ∂μ)))
    convert h.integrable_sq using 1
    all_goals try with_reducible_and_instances rfl
    ext z
    simp only [inner_sub_right,Pi.sub_apply]
  have hv (j : Fin e) : (∫z,(inner ℝ (b j) (f z-∫w,f w ∂μ))^2 ∂μ)≤β*(K:ℝ)^2 := by
    have h := hP.lipschitz_variance hβ ((innerSL ℝ (b j)).contDiff.comp hf)
      ((innerSL ℝ (b j)).lipschitz.comp hK) (hmj j)
    simp only [NNReal.coe_mul,coe_nnnorm,innerSL_apply_norm,b.norm_eq_one,one_mul] at h
    change Var[fun z => inner ℝ (b j) (f z);μ]≤β*(K:ℝ)^2 at h
    rw [variance_eq_integral (hmj j).aemeasurable] at h
    simpa only [inner_sub_right,integral_inner hi] using h
  refine ⟨hisq,?_⟩
  calc
    _ = ∫z,∑j : Fin e,(inner ℝ (b j) (f z-∫w,f w ∂μ))^2 ∂μ := by
      apply integral_congr_ae
      filter_upwards [] with z
      simpa only [Real.norm_eq_abs,sq_abs] using (b.sum_sq_norm_inner_right (f z-∫w,f w ∂μ)).symm
    _ = ∑j : Fin e,∫z,(inner ℝ (b j) (f z-∫w,f w ∂μ))^2 ∂μ := integral_finsetSum _ (fun j _ => hei j)
    _ ≤ ∑_j : Fin e,β*(K:ℝ)^2 := Finset.sum_le_sum (fun j _ => hv j)
    _ = _ := by simp; ring

theorem poincare_sq_norm_center {d : ℕ} {μ : Measure (Point d)}
    [IsProbabilityMeasure μ] {β : ℝ} (hβ : 0≤β) (hP : HasPoincare μ β)
    (hm : Appell.HasMoments μ) :
    Integrable (fun z => ‖z-∫w,w ∂μ‖^2) μ ∧
      (∫z,‖z-∫w,w ∂μ‖^2 ∂μ)≤(d:ℝ)*β := by
  simpa using poincare_vector_variance hβ hP hm (f:=id) contDiff_id (LipschitzWith.id)

lemma stdGaussian_sq_norm (d : ℕ) :
    (∫z : Point d,‖z‖^2 ∂stdGaussian (Point d))=d := by
  classical
  let b := EuclideanSpace.basisFun (Fin d) ℝ
  have hei (j : Fin d) : Integrable (fun z : Point d => (inner ℝ (b j) z)^2) (stdGaussian (Point d)) :=
    ((IsGaussian.memLp_two_id (μ:=stdGaussian (Point d))).continuousLinearMap_comp (innerSL ℝ (b j))).integrable_sq
  calc
    _ = ∫z,∑j : Fin d,(inner ℝ (b j) z)^2 ∂stdGaussian (Point d) := by
      apply integral_congr_ae
      filter_upwards [] with z
      simpa only [Real.norm_eq_abs,sq_abs] using (b.sum_sq_norm_inner_right z).symm
    _ = ∑j : Fin d,∫z,(inner ℝ (b j) z)^2 ∂stdGaussian (Point d) := integral_finsetSum _ (fun j _ => hei j)
    _ = _ := by
      have hj (j : Fin d) : (∫z : Point d,(inner ℝ (b j) z)^2 ∂stdGaussian (Point d))=1 := by
        change (∫z : Point d,((innerSL ℝ (b j)) z)^2 ∂stdGaussian (Point d))=1
        rw [GaussianPoincare.integral_dual_sq,innerSL_apply_norm,b.norm_eq_one,one_pow]
      simp_rw [hj]
      simp
end LogConcaveSampling

end

end

section

noncomputable section
namespace LogConcaveSampling
open MeasureTheory ProbabilityTheory
open scoped NNReal RealInnerProductSpace

lemma poincare_integral_norm_center_sharp {d : ℕ} {μ : Measure (Point d)}
    [IsProbabilityMeasure μ] {β : ℝ} (hβ : 0≤β) (hP : HasPoincare μ β)
    (hm : Appell.HasMoments μ) :
    (∫z,‖z-∫w,w ∂μ‖ ∂μ)≤Real.sqrt ((d:ℝ)*β) := by
  have hg : Appell.HasGrowth (fun z : Point d => z-∫w,w ∂μ) := by
    simpa only [sub_eq_add_neg,id_eq] using
      (Appell.HasGrowth.lipschitz (LipschitzWith.id (α:=Point d))).add
        (Appell.HasGrowth.const (-(∫w,w ∂μ)))
  have hlp : MemLp (fun z : Point d => ‖z-∫w,w ∂μ‖) 2 μ :=
    hg.norm.memLp (by fun_prop) hm
  have hh := integral_mul_sq_le hlp (memLp_const (1:ℝ) (μ:=μ))
  simp only [mul_one,one_pow,integral_const,probReal_univ,smul_eq_mul] at hh
  apply (Real.le_sqrt (integral_nonneg (fun _ => norm_nonneg _)) (by positivity)).mpr
  exact hh.trans (poincare_sq_norm_center hβ hP hm).2

variable {d : ℕ} {F : Point d → ℝ} {lam : ℝ≥0}
  (hF : Primitive F lam) (x : Point d) {r ρ : ℝ} (hr : 0 ≤ r)
  (hl : (lam:ℝ)*r^2≤1/2) (hρ0 : 0≤ρ) (hρ1 : ρ<1)

include hF hr hl hρ0 hρ1

lemma conditionalFieldMean_center_error_sharp (y : Point d) :
    ‖conditionalFieldMean F x r ρ y-primitiveField F x r
      (ρ • y-((1-ρ^2)*r) • conditionalFieldMean F x r ρ y)‖ ≤
      ((lam:ℝ)*r)*Real.sqrt ((d:ℝ)*((Real.pi^2/2)*(1-ρ^2))) := by
  let := conditionalLaw_probability hF x hr hl hρ0 hρ1 y
  have hh := norm_integral_sub_map_mean_le (primitiveField_lipschitz hF x hr)
    (conditional_identity_integrable hF x hr hl hρ0 hρ1 y)
  have hb := poincare_integral_norm_center_sharp
    (mul_nonneg (by positivity) (probability_time hρ0 hρ1).1.le)
    (conditionalLaw_hasPoincare hF x hr hl hρ0 hρ1 y)
    (conditionalLaw_hasExpMoments hF x hr hl hρ0 hρ1 y).hasMoments
  have hg := hh.trans (mul_le_mul_of_nonneg_left hb (mul_nonneg lam.coe_nonneg hr))
  simpa only [conditional_mean_identity hF x hr hl hρ0 hρ1 y,
    NNReal.coe_mul,NNReal.coe_mk,conditionalFieldMean] using hg

lemma conditionalFieldMean_center_zero_bound (y : Point d) :
    ‖conditionalFieldMean F x r ρ y-primitiveField F x r 0‖ ≤
      2*((lam:ℝ)*r)*(Real.pi*Real.sqrt d+‖y‖+r*‖primitiveField F x r 0‖) := by
  let M := conditionalFieldMean F x r ρ y
  let c := primitiveField F x r 0
  let z := ρ • y-((1-ρ^2)*r) • M
  have he := conditionalFieldMean_center_error_sharp hF x hr hl hρ0 hρ1 y
  have ht := probability_time hρ0 hρ1
  have hs : Real.sqrt ((d:ℝ)*((Real.pi^2/2)*(1-ρ^2)))≤Real.pi*Real.sqrt d := by
    apply (Real.sqrt_le_iff).mpr
    refine ⟨by positivity,?_⟩
    rw [mul_pow,Real.sq_sqrt (Nat.cast_nonneg d)]
    have hb := mul_le_mul_of_nonneg_left ht.2 (by positivity : 0≤(d:ℝ)*(Real.pi^2/2))
    nlinarith [Real.pi_pos,sq_nonneg Real.pi]
  have hz : ‖z‖≤‖y‖+r*‖M‖ := by
    calc
      _ ≤ ‖ρ • y‖+‖((1-ρ^2)*r) • M‖ := norm_sub_le _ _
      _ = ρ*‖y‖+((1-ρ^2)*r)*‖M‖ := by simp only [norm_smul,Real.norm_eq_abs,
        abs_of_nonneg hρ0,abs_of_nonneg (mul_nonneg ht.1.le hr)]
      _ ≤ _ := add_le_add (mul_le_of_le_one_left (norm_nonneg _) hρ1.le)
        (mul_le_mul_of_nonneg_right (mul_le_of_le_one_left hr ht.2) (norm_nonneg _))
  have hc := (primitiveField_lipschitz hF x hr).dist_le_mul z 0
  simp only [dist_eq_norm,sub_zero,NNReal.coe_mul,NNReal.coe_mk] at hc
  have hh : ‖M-c‖≤((lam:ℝ)*r)*(Real.pi*Real.sqrt d)+( (lam:ℝ)*r)*(‖y‖+r*‖M‖) := by
    calc
      _ ≤ ‖M-primitiveField F x r z‖+‖primitiveField F x r z-c‖ :=
        norm_sub_le_norm_sub_add_norm_sub _ _ _
      _ ≤ _ := add_le_add (he.trans (mul_le_mul_of_nonneg_left hs (by positivity)))
        (hc.trans (mul_le_mul_of_nonneg_left hz (by positivity)))
  have hm : ‖M‖≤‖M-c‖+‖c‖ := norm_le_norm_sub_add _ _
  have hh' := hh.trans (add_le_add le_rfl
    (mul_le_mul_of_nonneg_left (add_le_add le_rfl (mul_le_mul_of_nonneg_left hm hr)) (by positivity : 0≤(lam:ℝ)*r)))
  have hb := mul_le_mul_of_nonneg_right hl (norm_nonneg (M-c))
  dsimp [M,c] at hh' hb ⊢
  nlinarith
end LogConcaveSampling

end

end

end

end OAI
end

section
-- module Solutions.OAIQ048_LC.LogConcave_Analysis_GaussianAffineNormMoment
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
open MeasureTheory ProbabilityTheory
open scoped NNReal

lemma conditionalFieldMean_at_zero {d : ℕ} (F : Point d → ℝ) (x : Point d) (r : ℝ) (y : Point d) :
    conditionalFieldMean F x r 0 y=primitiveExpectedField F x r := by
  have he : conditionalPotential F x r 0 y=primitivePotential F x r := by
    funext z
    simp [conditionalPotential,primitivePotential]
  simp only [conditionalFieldMean,he,primitiveExpectedField]

variable {d : ℕ} {F : Point d → ℝ} {lam : ℝ≥0}
  (hF : Primitive F lam) (x : Point d) {r : ℝ} (hr : 0 ≤ r)
  (hl : (lam:ℝ)*r^2≤1/2)

include hF hr hl in
lemma terminal_mean_error (z : Point d) :
    ‖primitiveField F x r z-primitiveExpectedField F x r‖≤
      2*((lam:ℝ)*r)*(Real.pi*Real.sqrt d+‖z‖+r*‖primitiveField F x r 0‖) := by
  have he := conditionalFieldMean_center_zero_bound hF x hr hl (by norm_num : (0:ℝ)≤0)
    (by norm_num : (0:ℝ)<1) (0:Point d)
  rw [conditionalFieldMean_at_zero,norm_zero,add_zero] at he
  have hc := (primitiveField_lipschitz hF x hr).dist_le_mul z 0
  simp only [dist_eq_norm,sub_zero,NNReal.coe_mul,NNReal.coe_mk] at hc
  have hh := (norm_sub_le_norm_sub_add_norm_sub (primitiveField F x r z)
    (primitiveField F x r 0) (primitiveExpectedField F x r)).trans
    (add_le_add hc (by simpa only [norm_sub_rev] using he))
  have hz := mul_nonneg (mul_nonneg lam.coe_nonneg hr) (norm_nonneg z)
  nlinarith

end LogConcaveSampling

end

end

end

end OAI
end

section
-- module Solutions.OAIQ048_LC.LogConcave_Numerics_MeanTree
attribute [-instance] _root_.OAI.LogConcaveSampling.LowerBound.couplingLaw_probability _root_.OAI.LogConcaveSampling.LowerBound.remainingHaar_probability _root_.OAI.LogConcaveSampling.LowerBound.roundRandomLaw_probability _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_invInvariant _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_isHaar _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_probability _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_rightInvariant _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_compactSpace _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_measurableInv _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_measurableMul _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_secondCountable _root_.OAI.LogConcaveSampling.MeanTree.instIsProbabilityMeasureRowTapeRowLaw _root_.OAI.LogConcaveSampling.OracleCompiler.topSeedLaw_probability _root_.OAI.LogConcaveSampling.noiseKernel_markov
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
namespace LogConcaveSampling
open MeasureTheory
open scoped Classical BigOperators NNReal

namespace MeanTree
variable {X : Type*} [MeasurableSpace X] {d : ℕ}

lemma conditionalFieldMean_primitive {F : Point d → ℝ} {lam : ℝ≥0}
    (hF : Primitive F lam) (x : Point d) (r ρ : ℝ) (y : Point d) (ha : 0<1-ρ^2) :
    conditionalFieldMean F x r ρ y=
      primitiveExpectedField F (x+(r*ρ) • y) (r*Real.sqrt (1-ρ^2)) := by
  rw [conditionalFieldMean,←conditionalLaw_map hF x r ρ y ha]
  rw [integral_map (by fun_prop) (primitiveField_contDiff hF x r).continuous.aestronglyMeasurable]
  unfold primitiveExpectedField
  simp only [primitiveField,smul_add,smul_smul]
  congr 1
  funext z
  congr 1
  abel

@[simp] lemma eval_conditional {F : Point d → ℝ} {lam : ℝ≥0} (hF : Primitive F lam)
    (r ρ : ℝ) (x y : MeanTree X d) (z : X) (ha : 0<1-ρ^2) :
    eval F (conditional r ρ x y) z=conditionalFieldMean F (eval F x z) r ρ (eval F y z) := by
  simp only [conditional,eval_mean,eval_add,eval_scale]
  exact (conditionalFieldMean_primitive hF _ r ρ _ ha).symm

end MeanTree
end LogConcaveSampling

end

end

end OAI
end

section
-- module Solutions.OAIQ048_LC.LogConcave_OraclePrograms_Program
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

namespace LogConcaveSampling.OracleCompiler

namespace Program
variable {Ω O : Type*} [MeasurableSpace Ω] [MeasurableSpace O] {d q : ℕ}

lemma history_tail (A : Program Ω d q O) (V : Point d → ℝ) (ω : Ω)
    (n : ℕ) (i : Fin q) (hi : n ≤ i.val) : A.history V ω n i = 0 := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [history]
    split_ifs with hn
    · rw [Function.update_of_ne (by intro h; have H := congrArg Fin.val h; dsimp at H; omega)]
      exact ih (by omega)
    · exact ih (by omega)

lemma history_stable (A : Program Ω d q O) (V : Point d → ℝ) (ω : Ω)
    {m n : ℕ} (hmn : m ≤ n) (i : Fin q) (hi : i.val < m) :
    A.history V ω n i = A.history V ω m i := by
  induction n, hmn using Nat.le_induction with
  | base => rfl
  | succ n hmn ih =>
    simp only [history]
    split_ifs with hn
    · rw [Function.update_of_ne (by intro h; have H := congrArg Fin.val h; dsimp at H; omega)]
      exact ih
    · exact ih

lemma prefix_zero (h : Transcript d q) : mask 0 h = 0 := by
  funext i
  simp [mask]

lemma prefix_full (h : Transcript d q) : mask q h = h := by
  funext i
  simp [mask, i.isLt]

lemma prefix_succ (n : ℕ) (hn : n < q) (h : Transcript d q) :
    mask (n+1) h = Function.update (mask n h) ⟨n,hn⟩ (h ⟨n,hn⟩) := by
  funext i
  by_cases hi : i = ⟨n,hn⟩
  · subst i
    simp [mask]
  · rw [Function.update_of_ne hi]
    simp only [mask]
    have hne : i.val ≠ n := by intro he; exact hi (Fin.ext he)
    have he : (i.val < n+1) ↔ (i.val < n) := by omega
    simp only [he]

lemma history_eq_prefix (A : Program Ω d q O) (V : Point d → ℝ) (ω : Ω)
    {n : ℕ} (hn : n ≤ q) : A.history V ω n = mask n (A.history V ω q) := by
  funext i
  simp only [mask]
  split_ifs with hi
  · exact (A.history_stable V ω hn i hi).symm
  · exact A.history_tail V ω n i (by omega)

lemma history_spec (A : Program Ω d q O) (V : Point d → ℝ) (ω : Ω) (i : Fin q) :
    A.history V ω q i =
      firstOrderReply V (A.query i (ω, mask i.val (A.history V ω q))) := by
  rw [A.history_stable V ω (m := i.val+1) (by omega) i (by omega)]
  rw [history, dite_eq_left i.isLt]
  simp only [Function.update_self]
  rw [A.history_eq_prefix V ω (by omega)]

lemma history_unique (A : Program Ω d q O) (V : Point d → ℝ) (ω : Ω)
    (h : Transcript d q)
    (hh : ∀ i, h i = firstOrderReply V (A.query i (ω, mask i.val h))) :
    A.history V ω q = h := by
  have hp : ∀ n ≤ q, A.history V ω n = mask n h := by
    intro n hn
    induction n with
    | zero => simp [history, prefix_zero]
    | succ n ih =>
      have hnq : n < q := by omega
      rw [history, dite_eq_left hnq, ih (by omega), prefix_succ n hnq h, hh ⟨n,hnq⟩]
  simpa only [prefix_full] using hp q le_rfl

lemma measurable_history (A : Program Ω d q O) (V : Point d → ℝ)
    (hV : Measurable (firstOrderReply V)) (n : ℕ) :
    Measurable (A.history V · n) := by
  induction n with
  | zero => exact measurable_const
  | succ n ih =>
    simp only [history]
    split_ifs with hn
    · apply Measurable.of_eval
      intro i
      by_cases hi : i = ⟨n,hn⟩
      · subst i
        simp only [Function.update_self]
        exact hV.comp ((A.query_measurable _).comp (measurable_id.prodMk ih))
      · simp only [Function.update_of_ne hi]
        exact (measurable_pi_apply i).comp ih
    · exact ih

lemma measurable_run (A : Program Ω d q O) (V : Point d → ℝ)
    (hV : Measurable (firstOrderReply V)) : Measurable (A.run V) :=
  A.output_measurable.comp (measurable_id.prodMk (A.measurable_history V hV q))

end Program
end LogConcaveSampling.OracleCompiler

namespace LogConcaveSampling.OracleCompiler.Program
variable {Ω O R : Type*} [MeasurableSpace Ω] [MeasurableSpace O] [MeasurableSpace R]
  {d q r : ℕ}

lemma leftTrace_prefix_left (h : Transcript d q) (k : Transcript d r) (n : ℕ) :
    leftTrace (mask n (Fin.append h k)) = mask n h := by
  funext i
  simp [leftTrace, mask]

lemma leftTrace_prefix_right (h : Transcript d q) (k : Transcript d r) (n : ℕ) :
    leftTrace (mask (q+n) (Fin.append h k)) = h := by
  funext i
  have hi : i.val < q+n := by omega
  simp [leftTrace, mask, hi]

lemma rightTrace_prefix_right (h : Transcript d q) (k : Transcript d r) (n : ℕ) :
    rightTrace (mask (q+n) (Fin.append h k)) = mask n k := by
  funext i
  simp [rightTrace, mask]

lemma seq_history (A : Program Ω d q O) (B : Program (Ω × O) d r R)
    (V : Point d → ℝ) (ω : Ω) :
    (A.seq B).history V ω (q+r) =
      Fin.append (A.history V ω q) (B.history V (ω,A.run V ω) r) := by
  apply history_unique
  intro i
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i
  · simp only [Fin.append_left, seq, Fin.addCases_left, Fin.val_castAdd,
      leftTrace_prefix_left]
    exact A.history_spec V ω j
  · simp only [Fin.append_right, seq, Fin.addCases_right, Fin.val_natAdd,
      leftTrace_prefix_right, rightTrace_prefix_right]
    exact B.history_spec V (ω,A.run V ω) j

lemma seq_run (A : Program Ω d q O) (B : Program (Ω × O) d r R)
    (V : Point d → ℝ) (ω : Ω) :
    (A.seq B).run V ω = B.run V (ω,A.run V ω) := by
  unfold run
  rw [seq_history]
  simp only [seq, leftTrace_append, rightTrace_append]
  rfl

lemma map_history (A : Program Ω d q O) (f : Ω × O → R) (hf : Measurable f)
    (V : Point d → ℝ) (ω : Ω) (n : ℕ) :
    (A.map f hf).history V ω n = A.history V ω n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [history, ih]
    rfl

lemma map_run (A : Program Ω d q O) (f : Ω × O → R) (hf : Measurable f)
    (V : Point d → ℝ) (ω : Ω) : (A.map f hf).run V ω = f (ω,A.run V ω) := by
  unfold run
  rw [map_history]
  rfl

lemma seedMap_history {Ξ : Type*} [MeasurableSpace Ξ] (A : Program Ω d q O)
    (f : Ξ → Ω) (hf : Measurable f) (V : Point d → ℝ) (ω : Ξ) (n : ℕ) :
    (A.seedMap f hf).history V ω n = A.history V (f ω) n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [history, ih]
    rfl

lemma seedMap_run {Ξ : Type*} [MeasurableSpace Ξ] (A : Program Ω d q O)
    (f : Ξ → Ω) (hf : Measurable f) (V : Point d → ℝ) (ω : Ξ) :
    (A.seedMap f hf).run V ω = A.run V (f ω) := by
  unfold run
  rw [seedMap_history]
  rfl

end LogConcaveSampling.OracleCompiler.Program

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped BigOperators RealInnerProductSpace

namespace LogConcaveSampling.SeedCompiler

variable {ι E : Type*} [Fintype ι] [DecidableEq ι]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]

omit [DecidableEq ι] in
lemma slot_energy (c : ℝ) (a : ι → ℝ)
    (hc : c ^ 2 * (∑ i, a i ^ 2) - 2 * c + 1 = 0) (g : ι → E) :
    (∑ i, ‖slotTransform c a g i‖ ^ 2) + ‖slotSum a g‖ ^ 2 =
      ∑ i, ‖g i‖ ^ 2 := by
  let S := slotSum a g
  have hi : ∑ i, a i * inner ℝ (g i) S = ‖S‖ ^ 2 := by
    simp_rw [← real_inner_smul_left]
    rw [← sum_inner]
    exact real_inner_self_eq_norm_sq S
  have hsum : (∑ i, ‖slotTransform c a g i‖ ^ 2) =
      (∑ i, ‖g i‖ ^ 2) - (2 * c) * (∑ i, a i * inner ℝ (g i) S) +
        c ^ 2 * (∑ i, a i ^ 2) * ‖S‖ ^ 2 := by
    simp only [slotTransform, norm_sub_sq_real, norm_smul, Real.norm_eq_abs,
      mul_pow, sq_abs, real_inner_smul_right]
    dsimp only [S]
    simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib]
    simp only [Finset.mul_sum, Finset.sum_mul]
    simp only [mul_assoc, mul_comm, mul_left_comm]
  rw [hsum, hi]
  change _ + ‖S‖ ^ 2 = _
  nlinarith [mul_eq_zero_of_left hc (‖S‖ ^ 2)]

lemma dual_restored_left (c : ℝ) (a : ι → ℝ) (L : StrongDual ℝ (ι → E)) (j : ι) :
    ((L.comp (restored c a)).comp (ContinuousLinearMap.inl ℝ (ι → E) E)).comp
        (ContinuousLinearMap.single ℝ (fun _ : ι => E) j) =
      L.comp (ContinuousLinearMap.single ℝ (fun _ : ι => E) j) -
        (c * a j) • ∑ i, a i • L.comp (ContinuousLinearMap.single ℝ (fun _ : ι => E) i) := by
  ext x
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.inl_apply,
    ContinuousLinearMap.single_apply]
  have h : restored c a (Pi.single j x,0) =
      Pi.single j x - (c * a j) • ∑ i, a i • Pi.single i x := by
    ext k
    simp [slotTransform, slotSum, Pi.single_apply, smul_smul, mul_comm, mul_left_comm]
  rw [h, map_sub, map_smul, map_sum]
  simp

lemma dual_restored_right (c : ℝ) (a : ι → ℝ) (L : StrongDual ℝ (ι → E)) :
    (L.comp (restored c a)).comp (ContinuousLinearMap.inr ℝ (ι → E) E) =
      -(∑ i, a i • L.comp (ContinuousLinearMap.single ℝ (fun _ : ι => E) i)) := by
  ext x
  have h : restored c a (0,x) = -(∑ i, a i • Pi.single i x) := by
    ext k
    simp [slotTransform, slotSum, Pi.single_apply]
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.inr_apply]
  rw [h, map_neg, map_sum]
  simp

variable [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

theorem restored_gaussian (c : ℝ) (a : ι → ℝ)
    (hc : c ^ 2 * (∑ i, a i ^ 2) - 2 * c + 1 = 0) :
    ((Measure.pi (fun _ : ι => stdGaussian E)).prod (stdGaussian E)).map
      (restored c a) = Measure.pi (fun _ : ι => stdGaussian E) := by
  apply Measure.ext_of_charFunDual
  ext L
  rw [charFunDual_map, charFunDual_prod, charFunDual_pi, charFunDual_pi]
  simp_rw [dual_restored_left, dual_restored_right, charFunDual_stdGaussian,
    ← Complex.exp_sum, ← Complex.exp_add]
  congr 1
  let D := InnerProductSpace.toDual ℝ E
  let l := fun i => L.comp (ContinuousLinearMap.single ℝ (fun _ : ι => E) i)
  have he := slot_energy c a hc (fun i => D.symm (l i))
  simp only [slotTransform, slotSum, ← map_smul, ← map_sum, ← map_sub,
    LinearIsometryEquiv.norm_map] at he
  simp only [norm_neg]
  norm_cast
  dsimp only [l] at he
  simp only [← Finset.sum_div, Finset.sum_neg_distrib]
  linarith

omit [DecidableEq ι] in
lemma sqrtCoefficient_equation (a : ι → ℝ) (ha : (∑ i, a i ^ 2) ≤ 1) :
    (sqrtCoefficient a) ^ 2 * (∑ i, a i ^ 2) - 2 * sqrtCoefficient a + 1 = 0 := by
  have hsq := Real.sq_sqrt (sub_nonneg.mpr ha)
  have hpos : 0 < 1 + Real.sqrt (1 - ∑ i, a i ^ 2) := by positivity
  unfold sqrtCoefficient
  field_simp
  nlinarith

theorem sqrt_restored_gaussian (a : ι → ℝ) (ha : (∑ i, a i ^ 2) ≤ 1) :
    ((Measure.pi (fun _ : ι => stdGaussian E)).prod (stdGaussian E)).map
      (restored (sqrtCoefficient a) a) = Measure.pi (fun _ : ι => stdGaussian E) :=
  restored_gaussian _ _ (sqrtCoefficient_equation a ha)

end LogConcaveSampling.SeedCompiler

namespace LogConcaveSampling.SeedCompiler
variable {ι E O : Type*} [Fintype ι] [DecidableEq ι]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]

omit [DecidableEq ι] in
lemma absorption_pathwise {r D : ℝ} (v : ι → ℝ)
    (M : E → (ι → E) → O) (hM : ShiftInvariant r v M)
    (x : E) (c : ℝ) (g : ι → E) (z : E) :
    M (x + (r / (2 * D)) • z)
        (slotTransform c (fun i => v i / (2 * D)) g) =
      M x (restored c (fun i => v i / (2 * D)) (g,z)) := by
  have h := hM x ((1 / (2 * D)) • z)
    (restored c (fun i => v i / (2 * D)) (g,z))
  have hx : r • ((1 / (2 * D)) • z) = (r / (2 * D)) • z := by
    rw [smul_smul]; congr 1; ring
  have hs : (fun i => restored c (fun i => v i / (2 * D)) (g,z) i +
      v i • ((1 / (2 * D)) • z)) = slotTransform c (fun i => v i / (2 * D)) g := by
    funext i
    simp only [restored_apply, smul_smul]
    have hc : v i * (1 / (2 * D)) = v i / (2 * D) := by ring
    rw [hc, sub_add_cancel]
  simpa only [hx, hs] using h

omit [DecidableEq ι] in
lemma normalized_shift_bound {D : ℝ} (hD : 0 < D) (v : ι → ℝ)
    (hv : (∑ i, v i ^ 2) ≤ D ^ 2) :
    (∑ i, (v i / (2 * D)) ^ 2) ≤ 1 / 4 := by
  simp only [div_pow, ← Finset.sum_div]
  apply (div_le_iff₀ (sq_pos_of_pos (mul_pos (by norm_num) hD))).mpr
  nlinarith

variable [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [MeasurableSpace O]

theorem restored_with_anchors {A : Type*} [MeasurableSpace A]
    (μ : Measure A) [SFinite μ] (a : ι → ℝ) (ha : (∑ i, a i ^ 2) ≤ 1) :
    (μ.prod ((Measure.pi (fun _ : ι => stdGaussian E)).prod (stdGaussian E))).map
      (Prod.map id (restored (sqrtCoefficient a) a)) =
      μ.prod (Measure.pi (fun _ : ι => stdGaussian E)) := by
  rw [← Measure.map_prod_map μ _ measurable_id (by fun_prop), Measure.map_id,
    sqrt_restored_gaussian a ha]

end LogConcaveSampling.SeedCompiler

end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ048_LC.LogConcave_OraclePrograms_TerminalMean
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section

noncomputable section
namespace LogConcaveSampling.SeedCompiler
open MeasureTheory ProbabilityTheory Function
open scoped BigOperators

variable {Ω A ι E : Type*} [MeasurableSpace Ω] [MeasurableSpace A]
  [Fintype ι] [DecidableEq ι]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

theorem restored_from_joint_law (κ : Measure Ω) [SFinite κ] (μ : Measure A) [SFinite μ]
    (anchor : Ω → A) (noise : Ω → E) (ha : Measurable anchor) (hz : Measurable noise)
    (hlaw : κ.map (fun w => (anchor w,noise w))=μ.prod (stdGaussian E))
    (a : ι → ℝ) (ha2 : (∑i,a i^2)≤1) :
    (κ.prod (Measure.pi fun _ : ι => stdGaussian E)).map
      (fun z => (anchor z.1,restored (sqrtCoefficient a) a (z.2,noise z.1)))=
        μ.prod (Measure.pi fun _ : ι => stdGaussian E) := by
  let γ : Measure (ι → E) := Measure.pi fun _ => stdGaussian E
  have hAZ : MeasurePreserving (fun w => (anchor w,noise w)) κ (μ.prod (stdGaussian E)) :=
    ⟨ha.prodMk hz,hlaw⟩
  have hp := hAZ.prod (MeasurePreserving.id γ)
  have hs := (MeasurePreserving.id μ).prod (Measure.measurePreserving_swap (μ:=stdGaussian E) (ν:=γ))
  have ht := hs.comp ((measurePreserving_prodAssoc μ (stdGaussian E) γ).comp hp)
  have hr : MeasurePreserving (Prod.map id (restored (sqrtCoefficient a) a))
      (μ.prod (γ.prod (stdGaussian E))) (μ.prod γ) :=
    ⟨by fun_prop,restored_with_anchors μ a ha2⟩
  exact (hr.comp ht).map_eq

end LogConcaveSampling.SeedCompiler

end

end

end

end OAI
end

section
-- module Solutions.OAIQ048_LC.LogConcave_OraclePrograms_Expression
attribute [-instance] _root_.OAI.LogConcaveSampling.LowerBound.couplingLaw_probability _root_.OAI.LogConcaveSampling.LowerBound.remainingHaar_probability _root_.OAI.LogConcaveSampling.LowerBound.roundRandomLaw_probability _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_invInvariant _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_isHaar _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_probability _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_rightInvariant _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_compactSpace _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_measurableInv _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_measurableMul _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_secondCountable _root_.OAI.LogConcaveSampling.MeanTree.instIsProbabilityMeasureRowTapeRowLaw _root_.OAI.LogConcaveSampling.OracleCompiler.topSeedLaw_probability _root_.OAI.LogConcaveSampling.noiseKernel_markov
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open MeasureTheory

namespace LogConcaveSampling.OracleCompiler

namespace Expression
variable {X : Type*} [MeasurableSpace X] {d : ℕ}

theorem compile_run (C : Expression X d) (V : Point d → ℝ)
    (x : X) (g : Fin C.slots → Point d) : C.compile.run V (x,g)=C.eval V x g := by
  induction C with
  | noise b hb n => rfl
  | add a C k q M P hP T hC hT =>
    simp only [compile,Program.seq_run,Program.seedMap_run,Program.map_run,eval]
    rw [hC,hT]

theorem measurable_eval (C : Expression X d) (V : Point d → ℝ)
    (hV : Measurable (firstOrderReply V)) :
    Measurable (fun z : X × (Fin C.slots → Point d) => C.eval V z.1 z.2) := by
  have hr := C.compile.measurable_run V hV
  convert hr using 1
  all_goals try with_reducible_and_instances rfl
  funext z
  exact (compile_run C V z.1 z.2).symm

end Expression
end LogConcaveSampling.OracleCompiler

end

end

section

noncomputable section
namespace LogConcaveSampling.OracleCompiler.Program
open MeasureTheory

variable {Ω O R Ξ : Type*} [MeasurableSpace Ω] [MeasurableSpace O]
  [MeasurableSpace R] [MeasurableSpace Ξ] {d q r : ℕ}

namespace Equivariant
variable {A : Program Ω d q O} {f : Ω → Ω} {τ : O → O}

theorem history (hA : A.Equivariant f τ) (V : Point d → ℝ) (ω : Ω) (n : ℕ) :
    A.history V (f ω) n=A.history V ω n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [Program.history,ih]
    split_ifs with hn
    · rw [hA.query]
    · rfl

theorem run (hA : A.Equivariant f τ) (V : Point d → ℝ) (ω : Ω) :
    A.run V (f ω)=τ (A.run V ω) := by
  unfold Program.run
  rw [hA.history,hA.output]

end Equivariant

end LogConcaveSampling.OracleCompiler.Program

end

end

section

noncomputable section
namespace LogConcaveSampling.OracleCompiler.Expression
open MeasureTheory

variable {E : Type*} [MeasurableSpace E]

lemma split_slots_preserving (μ : Measure E) [SigmaFinite μ] (c k : ℕ) :
    MeasurePreserving
      (fun g : Fin (c+k) → E =>
        ((fun i : Fin c => g (Fin.castAdd k i)),fun i : Fin k => g (Fin.natAdd c i)))
      (Measure.pi fun _ => μ) ((Measure.pi fun _ : Fin c => μ).prod (Measure.pi fun _ : Fin k => μ)) := by
  have H := (measurePreserving_sumPiEquivProdPi (fun _ : Fin c ⊕ Fin k => μ)).comp
    (measurePreserving_piCongrLeft (fun _ : Fin (c+k) => μ) finSumFinEquiv).symm
  convert H using 1
  all_goals try with_reducible_and_instances rfl
  rfl

end LogConcaveSampling.OracleCompiler.Expression

end

end

end

end OAI
end

section
-- module Solutions.OAIQ048_LC.LogConcave_Numerics_ChildNoise
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
namespace LogConcaveSampling.MeanTree
open MeasureTheory ProbabilityTheory OracleCompiler
open scoped Classical BigOperators

lemma coefficient_energy {k : ℕ} (a : Fin k → ℝ) :
    (∑i,a i^2)≤(∑i,|a i|)^2 := by
  simpa only [sq_abs] using Finset.sum_sq_le_sq_sum_of_nonneg
    (s:=Finset.univ) (fun i _ => abs_nonneg (a i))

variable {ι E : Type*} [Fintype ι] [DecidableEq ι]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

theorem weighted_gaussian_law (a : ι → ℝ) (n : ℝ) (ha : (∑i,a i^2)=n^2) :
    (Measure.pi fun _ : ι => stdGaussian E).map (fun g => ∑i,a i • g i)=
      (stdGaussian E).map (fun z => n • z) := by
  let S : (ι → E) →L[ℝ] E := ∑i,a i • ContinuousLinearMap.proj i
  let T : E →L[ℝ] E := n • ContinuousLinearMap.id ℝ E
  have hS (g : ι → E) : S g=∑i,a i • g i := by simp [S]
  have hT0 (z : E) : T z=n • z := by simp [T]
  simp_rw [←hS,←hT0]
  change (Measure.pi fun _ : ι => stdGaussian E).map S=(stdGaussian E).map T
  apply Measure.ext_of_charFunDual
  ext L
  rw [charFunDual_map,charFunDual_map,charFunDual_pi]
  have hL (i : ι) : (L.comp S).comp (ContinuousLinearMap.single ℝ (fun _ : ι => E) i)=a i • L := by
    ext z
    simp only [ContinuousLinearMap.comp_apply, hS, map_sum, map_smul, ContinuousLinearMap.single_apply]
    rw [Finset.sum_eq_single i]
    · simp
    · intro j _ hji; simp [Pi.single_eq_of_ne hji]
    · simp
  have hT : L.comp T=n • L := by ext z; simp [T]
  simp_rw [hL,hT,charFunDual_stdGaussian]
  rw [←Complex.exp_sum]
  simp only [norm_smul,Real.norm_eq_abs]
  congr 1
  norm_cast
  simp only [mul_pow,sq_abs,←Finset.sum_div,Finset.sum_neg_distrib,←Finset.sum_mul,ha]

end LogConcaveSampling.MeanTree

end

end

section

noncomputable section
namespace LogConcaveSampling.MeanTree
open MeasureTheory ProbabilityTheory OracleCompiler
open scoped Classical BigOperators

variable {X : Type*} [MeasurableSpace X] {d : ℕ}

lemma declaredNoise_energy {k : ℕ} {A : ℝ} (hA : 0<A) (n : ℝ) (a : Fin k → ℝ)
    (ha : (∑i,|a i|)≤A) : (declaredNoise n A)^2*(∑i,a i^2)≤n^2/4 := by
  have hw : 0≤∑i,|a i| := Finset.sum_nonneg fun i _ => abs_nonneg _
  have he := (coefficient_energy a).trans (pow_le_pow_left₀ hw ha 2)
  change (n/(2*A))^2*(∑i,a i^2)≤n^2/4
  rw [div_pow,div_mul_eq_mul_div,div_le_iff₀ (by positivity : 0<(2*A)^2)]
  have hm := mul_le_mul_of_nonneg_left he (sq_nonneg n)
  nlinarith

lemma declaredReserve_variance {k : ℕ} {A : ℝ} (hA : 0<A) (n : ℝ) (a : Fin k → ℝ)
    (ha : (∑i,|a i|)≤A) :
    (declaredReserve n A a)^2+(declaredNoise n A)^2*(∑i,a i^2)=n^2 := by
  have he := declaredNoise_energy hA n a ha
  rw [declaredReserve,Real.sq_sqrt (by nlinarith [sq_nonneg n])]
  ring

end LogConcaveSampling.MeanTree

end

end

end OAI
end

section
-- module Solutions.OAIQ048_LC.LogConcave_Analysis_GaussianPairSumLaw
attribute [-instance] _root_.OAI.LogConcaveSampling.LowerBound.couplingLaw_probability _root_.OAI.LogConcaveSampling.LowerBound.remainingHaar_probability _root_.OAI.LogConcaveSampling.LowerBound.roundRandomLaw_probability _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_invInvariant _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_isHaar _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_probability _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_rightInvariant _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_compactSpace _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_measurableInv _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_measurableMul _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_secondCountable _root_.OAI.LogConcaveSampling.MeanTree.instIsProbabilityMeasureRowTapeRowLaw _root_.OAI.LogConcaveSampling.OracleCompiler.topSeedLaw_probability _root_.OAI.LogConcaveSampling.noiseKernel_markov
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
namespace LogConcaveSampling
open MeasureTheory ProbabilityTheory Function
open scoped Classical BigOperators

variable {d : ℕ}

lemma gaussian_pair_sum_law (a b s : ℝ) (hs : a^2+b^2=s^2) :
    ((stdGaussian (Point d)).prod (stdGaussian (Point d))).map
      (fun z => a • z.1+b • z.2)=
      (stdGaussian (Point d)).map (fun z => s • z) := by
  have h := MeanTree.weighted_gaussian_law (E:=Point d) ![a,b] s (by simpa using hs)
  rw [←(measurePreserving_finTwoArrow (stdGaussian (Point d))).map_eq,
    Measure.map_map (by fun_prop) (by fun_prop)]
  change (Measure.pi (fun _ : Fin 2 => stdGaussian (Point d))).map
    (fun z => a • z 0+b • z 1)=_
  simpa only [Fin.sum_univ_two,Matrix.cons_val_zero,Matrix.cons_val_one] using h

lemma smoothing_add_gaussian {X W : Type*} [MeasurableSpace X] [MeasurableSpace W]
    (μ : Measure X) [IsProbabilityMeasure μ] (θ : Measure W) [IsProbabilityMeasure θ]
    (u : X → Point d) (f : W → Point d) (hu : Measurable u) (hf : Measurable f)
    (a b s : ℝ) (hs : a^2+b^2=s^2)
    (hlaw : μ.map u=(θ.prod (stdGaussian (Point d))).map (fun z => f z.1+a • z.2)) :
    (μ.prod (stdGaussian (Point d))).map (fun z => u z.1+b • z.2)=
      (θ.prod (stdGaussian (Point d))).map (fun z => f z.1+s • z.2) := by
  let γ := stdGaussian (Point d)
  have h := congrArg (fun η : Measure (Point d) => (η.prod γ).map (fun z => z.1+b • z.2)) hlaw
  have hl : (μ.map u).prod γ=(μ.prod γ).map (Prod.map u id) := by
    rw [←Measure.map_prod_map _ _ hu measurable_id,Measure.map_id]
  have hr : ((θ.prod γ).map (fun z => f z.1+a • z.2)).prod γ=
      ((θ.prod γ).prod γ).map (Prod.map (fun z => f z.1+a • z.2) id) := by
    rw [←Measure.map_prod_map _ _ (by fun_prop) measurable_id,Measure.map_id]
  rw [hl,hr,Measure.map_map (by fun_prop) (by fun_prop),
    Measure.map_map (by fun_prop) (by fun_prop)] at h
  apply h.trans
  have hassoc := (measurePreserving_prodAssoc θ γ γ).map_eq
  have hsum : (θ.prod (γ.prod γ)).map
      (fun z => (z.1,a • z.2.1+b • z.2.2))=
      θ.prod (γ.map (fun z => s • z)) := by
    rw [show (fun z : W × (Point d × Point d) => (z.1,a • z.2.1+b • z.2.2))=
      Prod.map id (fun z => a • z.1+b • z.2) from rfl]
    rw [←Measure.map_prod_map _ _ measurable_id (by fun_prop),Measure.map_id]
    rw [gaussian_pair_sum_law a b s hs]
  have hsum' := congrArg (Measure.map (fun z : W × Point d => f z.1+z.2)) hsum
  rw [Measure.map_map (by fun_prop) (by fun_prop)] at hsum'
  have he := congrArg (Measure.map (fun z : W × (Point d × Point d) =>
    f z.1+(a • z.2.1+b • z.2.2))) hassoc
  rw [Measure.map_map (by fun_prop) (by fun_prop)] at he
  have hfinal : (θ.prod (γ.map (fun z => s • z))).map (fun z => f z.1+z.2)=
      (θ.prod γ).map (fun z => f z.1+s • z.2) := by
    rw [show θ.prod (γ.map (fun z => s • z))=(θ.prod γ).map
      (Prod.map id (fun z => s • z)) by
        rw [←Measure.map_prod_map _ _ measurable_id (by fun_prop),Measure.map_id]]
    rw [Measure.map_map (by fun_prop) (by fun_prop)]
    rfl
  have hh := he.trans (hsum'.trans hfinal)
  change ((θ.prod γ).prod γ).map (fun z => f z.1.1+(a • z.1.2+b • z.2))=_ at hh
  change ((θ.prod γ).prod γ).map (fun z => (f z.1.1+a • z.1.2)+b • z.2)=_
  simpa only [add_assoc] using hh
end LogConcaveSampling

end

end

end OAI
end

section
-- module Solutions.OAIQ048_LC.LogConcave_Dynamics_Squared
attribute [-instance] _root_.OAI.LogConcaveSampling.LowerBound.couplingLaw_probability _root_.OAI.LogConcaveSampling.LowerBound.remainingHaar_probability _root_.OAI.LogConcaveSampling.LowerBound.roundRandomLaw_probability _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_invInvariant _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_isHaar _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_probability _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_rightInvariant _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_compactSpace _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_measurableInv _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_measurableMul _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_secondCountable _root_.OAI.LogConcaveSampling.MeanTree.instIsProbabilityMeasureRowTapeRowLaw _root_.OAI.LogConcaveSampling.OracleCompiler.topSeedLaw_probability _root_.OAI.LogConcaveSampling.noiseKernel_markov
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
namespace LogConcaveSampling.Coupling
open MeasureTheory ProbabilityTheory TopologicalSpace Set
open scoped Classical

variable {X Ω Γ : Type*} [PseudoMetricSpace X] [SeparableSpace X] [Nonempty X]
  [MeasurableSpace X] [BorelSpace X] [MeasurableSpace Ω] [MeasurableSpace Γ]

theorem exists_countable_quantizer {e : ℝ} (he : 0<e) :
    ∃q : X → ℕ,Measurable q ∧ ∀x,dist x (denseSeq X (q x))<e := by
  have hp : ∀x : X, ∃n,dist x (denseSeq X n)<e :=
    fun x => (denseRange_denseSeq X).exists_dist_lt x he
  refine ⟨fun x => Nat.find (hp x),measurable_find hp ?_,fun x => Nat.find_spec (hp x)⟩
  intro n
  exact (continuous_id.dist continuous_const).measurable measurableSet_Iio

theorem measurable_coupling_of_pointwise {d : ℕ}
    (μ : Measure Ω) (ν : Measure Γ) (f : X → Ω → Point d) (g : X → Γ → Point d)
    (hf : Measurable (Function.uncurry f)) (hg : Measurable (Function.uncurry g))
    (B : X → ℝ) {Lf Lg e : ℝ} (hLf : 0≤Lf) (hLg : 0≤Lg) (he : 0<e)
    (hfl : ∀x y z,‖f x z-f y z‖≤Lf*dist x y)
    (hgl : ∀x y z,‖g x z-g y z‖≤Lg*dist x y)
    (hc : ∀x,SquaredAt μ ν (f x) (g x) (B x)) :
    ∃q : X → ℕ,Measurable q ∧ (∀x,dist x (denseSeq X (q x))<e) ∧
    ∃K : Kernel X (Ω × Γ),IsMarkovKernel K ∧
      ∀x,(K x).fst=μ ∧ (K x).snd=ν ∧
        Integrable (fun z => ‖f x z.1-g x z.2‖^2) (K x) ∧
        (∫z,‖f x z.1-g x z.2‖^2 ∂K x)≤2*B (denseSeq X (q x))+2*((Lf+Lg)*e)^2 := by
  obtain ⟨q,hq,hqe⟩ := exists_countable_quantizer (X:=X) he
  choose κ hκ hfst hsnd hi hb using (fun n => hc (denseSeq X n))
  let K : Kernel X (Ω × Γ) := ⟨fun x => κ (q x),(measurable_of_countable κ).comp hq⟩
  have : IsMarkovKernel K := ⟨fun x => hκ (q x)⟩
  refine ⟨q,hq,hqe,K,(by first | infer_instance | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | (apply Measurable.aemeasurable; measurability) | measurability)),?_⟩
  intro x
  have : IsProbabilityMeasure (K x) := hκ (q x)
  let y := denseSeq X (q x)
  let C := ((Lf+Lg)*e)^2
  have hdom : Integrable (fun z : Ω × Γ => 2*‖f y z.1-g y z.2‖^2+2*C) (K x) :=
    ((hi (q x)).const_mul 2).add (integrable_const _)
  have hp (z : Ω × Γ) : ‖f x z.1-g x z.2‖^2≤2*‖f y z.1-g y z.2‖^2+2*C := by
    have ht := norm_sub_le_norm_sub_add_norm_sub (f x z.1) (f y z.1) (g x z.2)
    have hh := norm_sub_le_norm_sub_add_norm_sub (f y z.1) (g y z.2) (g x z.2)
    rw [norm_sub_rev (g y z.2)] at hh
    have hf' := (hfl x y z.1).trans (mul_le_mul_of_nonneg_left (hqe x).le hLf)
    have hg' := (hgl x y z.2).trans (mul_le_mul_of_nonneg_left (hqe x).le hLg)
    have hn : ‖f x z.1-g x z.2‖≤‖f y z.1-g y z.2‖+(Lf+Lg)*e := by linarith
    have hn2 := pow_le_pow_left₀ (norm_nonneg _) hn 2
    dsimp only [C]
    nlinarith [sq_nonneg (‖f y z.1-g y z.2‖-(Lf+Lg)*e)]
  have hm : Measurable (fun z : Ω × Γ => ‖f x z.1-g x z.2‖^2) := by
    exact ((hf.of_uncurry_left.comp measurable_fst).sub
      (hg.of_uncurry_left.comp measurable_snd)).norm.pow_const 2
  have hint := hdom.mono' hm.aestronglyMeasurable (Filter.Eventually.of_forall (fun z => by
    simpa only [Real.norm_eq_abs,abs_sq] using hp z))
  refine ⟨hfst (q x),hsnd (q x),hint,(integral_mono hint hdom hp).trans ?_⟩
  change (∫z,2*‖f (denseSeq X (q x)) z.1-g (denseSeq X (q x)) z.2‖^2+2*C ∂κ (q x))≤_
  rw [integral_add ((hi (q x)).const_mul 2) (integrable_const _),integral_const_mul,
    integral_const,probReal_univ,one_smul]
  have hh := hb (q x)
  change 2*(∫z,‖f y z.1-g y z.2‖^2 ∂κ (q x))+2*C≤_
  linarith
end LogConcaveSampling.Coupling

end

end

section

noncomputable section
namespace LogConcaveSampling.Coupling
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

variable {Ω A B : Type*} [MeasurableSpace Ω] [MeasurableSpace A] [MeasurableSpace B]
  [StandardBorelSpace B] [Nonempty B]

lemma lift_fst (ν : Measure Ω) [SFinite ν] (κ : Measure (A × B)) [IsFiniteMeasure κ]
    (T : Ω → A) (hT : Measurable T) : (lift ν κ T hT).fst=ν := by
  exact Measure.fst_compProd _ _

theorem lift_map (ν : Measure Ω) [SFinite ν] (κ : Measure (A × B)) [IsFiniteMeasure κ]
    (T : Ω → A) (hT : Measurable T) (hlaw : ν.map T=κ.fst) :
    (lift ν κ T hT).map (fun z => (T z.1,z.2))=κ := by
  calc
    _ = κ.fst ⊗ₘ κ.condKernel := by
      ext s hs
      have hm : Measurable (fun z : Ω × B => (T z.1,z.2)) := by fun_prop
      rw [Measure.map_apply hm hs]
      rw [lift,Measure.compProd_apply (hs.preimage (by fun_prop)),Measure.compProd_apply hs]
      simp only [Kernel.comap_apply]
      rw [←hlaw]
      rw [lintegral_map (Kernel.measurable_kernel_prodMk_left (κ := κ.condKernel) hs) hT]
      rfl
    _ = κ := Measure.disintegrate κ κ.condKernel

lemma lift_integrable (ν : Measure Ω) [SFinite ν]
    (κ : Measure (A × B)) [IsFiniteMeasure κ] (T : Ω → A) (hT : Measurable T)
    (hlaw : ν.map T=κ.fst) (f : A × B → ℝ) (hf : Integrable f κ) :
    Integrable (fun z => f (T z.1,z.2)) (lift ν κ T hT) ∧
      (∫z,f (T z.1,z.2) ∂lift ν κ T hT)=∫z,f z ∂κ := by
  have hm : Measurable (fun z : Ω × B => (T z.1,z.2)) := by fun_prop
  have he := lift_map ν κ T hT hlaw
  have hi : Integrable f ((lift ν κ T hT).map (fun z => (T z.1,z.2))) := by rw [he]; exact hf
  exact ⟨hi.comp_measurable hm,(integral_map hm.aemeasurable hi.aestronglyMeasurable).symm.trans
    (by rw [he])⟩
end LogConcaveSampling.Coupling

end

end

section

noncomputable section
namespace LogConcaveSampling.Coupling
open MeasureTheory ProbabilityTheory Function SeedCompiler
open scoped BigOperators

variable {Ω A E : Type*} [MeasurableSpace Ω] [MeasurableSpace A]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {k : ℕ}

theorem absorb_coupling (κ : Measure Ω) [IsProbabilityMeasure κ]
    (μ : Measure A) [IsProbabilityMeasure μ] (ν : Measure E)
    (anchor : Ω → A) (noise center : Ω → E)
    (ha : Measurable anchor) (hz : Measurable noise) (hc : Measurable center)
    (hlaw : κ.map (fun w => (anchor w,noise w))=μ.prod (stdGaussian E))
    (x : A → E) (hx : Measurable x) {r D K S B : ℝ}
    (hD : 0<D) (hK : 0≤K) (v : Fin k → ℝ) (hv : (∑i,v i^2)≤D^2)
    (M : E → (Fin k → E) → E) (hm : Measurable (uncurry M))
    (hshift : ShiftInvariant r v M)
    (hLip : ∀x y g,‖M x g-M y g‖≤K*‖x-y‖)
    (Q : A → E → E) (hQ : Measurable (uncurry Q))
    (hci : Integrable (fun w => ‖center w-(x (anchor w)+(r/(2*D)) • noise w)‖^2) κ)
    (hce : (∫w,‖center w-(x (anchor w)+(r/(2*D)) • noise w)‖^2 ∂κ)≤S)
    (π : Measure ((A × (Fin k → E)) × E)) [IsProbabilityMeasure π]
    (hπ : π.fst=μ.prod (Measure.pi fun _ : Fin k => stdGaussian E))
    (hπnoise : π.map (fun z => (z.1.1,z.2))=μ.prod ν)
    (hbi : Integrable (fun z => ‖M (x z.1.1) z.1.2-Q z.1.1 z.2‖^2) π)
    (hbe : (∫z,‖M (x z.1.1) z.1.2-Q z.1.1 z.2‖^2 ∂π)≤B) :
    let a := fun i => v i/(2*D)
    let P := slotTransform (sqrtCoefficient a) a
    ∃Λ : Measure ((Ω × (Fin k → E)) × E),IsProbabilityMeasure Λ ∧
      Λ.fst=κ.prod (Measure.pi fun _ : Fin k => stdGaussian E) ∧
      Λ.map (fun z => (anchor z.1.1,z.2))=μ.prod ν ∧
      Integrable (fun z => ‖M (center z.1.1) (P z.1.2)-Q (anchor z.1.1) z.2‖^2) Λ ∧
      (∫z,‖M (center z.1.1) (P z.1.2)-Q (anchor z.1.1) z.2‖^2 ∂Λ)≤2*K^2*S+2*B := by
  dsimp only
  let a := fun i => v i/(2*D)
  let γ : Measure (Fin k → E) := Measure.pi fun _ => stdGaussian E
  let T : Ω × (Fin k → E) → A × (Fin k → E) := fun z =>
    (anchor z.1,restored (sqrtCoefficient a) a (z.2,noise z.1))
  have hT : Measurable T := by
    exact (ha.comp measurable_fst).prodMk ((restored (sqrtCoefficient a) a).measurable.comp
      (measurable_snd.prodMk (hz.comp measurable_fst)))
  have hTlaw : (κ.prod γ).map T=π.fst := by
    rw [hπ]
    exact restored_from_joint_law κ μ anchor noise ha hz hlaw a
      ((normalized_shift_bound hD v hv).trans (by norm_num))
  let Λ := lift (κ.prod γ) π T hT
  have hΛ : Λ.fst=κ.prod γ := lift_fst _ _ _ _
  have hΛmap := lift_map (κ.prod γ) π T hT hTlaw
  have hC₀ := hci.comp_fst γ
  have hC : Integrable (fun z : (Ω × (Fin k → E)) × E =>
      ‖center z.1.1-(x (anchor z.1.1)+(r/(2*D)) • noise z.1.1)‖^2) Λ := by
    have h : Integrable (fun z : Ω × (Fin k → E) =>
      ‖center z.1-(x (anchor z.1)+(r/(2*D)) • noise z.1)‖^2) Λ.fst := by
      rw [hΛ]; exact hC₀
    exact h.comp_measurable measurable_fst
  have hCeq : (∫z : (Ω × (Fin k → E)) × E,
      ‖center z.1.1-(x (anchor z.1.1)+(r/(2*D)) • noise z.1.1)‖^2 ∂Λ)=
      ∫w,‖center w-(x (anchor w)+(r/(2*D)) • noise w)‖^2 ∂κ := by
    have hmf : Measurable (fun z : Ω × (Fin k → E) =>
      ‖center z.1-(x (anchor z.1)+(r/(2*D)) • noise z.1)‖^2) := by
      exact ((hc.sub ((hx.comp ha).add (hz.const_smul _))).norm.pow_const 2).comp measurable_fst
    rw [←integral_map measurable_fst.aemeasurable hmf.aestronglyMeasurable]
    change (∫z : Ω × (Fin k → E),‖center z.1-(x (anchor z.1)+(r/(2*D)) • noise z.1)‖^2 ∂Λ.fst)=_
    rw [hΛ,integral_prod _ hC₀]
    simp only [integral_const,probReal_univ,one_smul]
  have hJ := lift_integrable (κ.prod γ) π T hT hTlaw
    (fun z => ‖M (x z.1.1) z.1.2-Q z.1.1 z.2‖^2) hbi
  have hmP : Measurable (slotTransform (sqrtCoefficient a) a : (Fin k → E) → _) := by
    unfold slotTransform slotSum; fun_prop
  have hmeas : Measurable (fun z : (Ω × (Fin k → E)) × E =>
      ‖M (center z.1.1) (slotTransform (sqrtCoefficient a) a z.1.2)-Q (anchor z.1.1) z.2‖^2) := by
    exact ((hm.comp ((hc.comp (measurable_fst.comp measurable_fst)).prodMk
      (hmP.comp (measurable_snd.comp measurable_fst)))).sub
      (hQ.comp ((ha.comp (measurable_fst.comp measurable_fst)).prodMk measurable_snd))).norm.pow_const 2
  have hbound (z : (Ω × (Fin k → E)) × E) :
      ‖M (center z.1.1) (slotTransform (sqrtCoefficient a) a z.1.2)-Q (anchor z.1.1) z.2‖^2≤
        2*K^2*‖center z.1.1-(x (anchor z.1.1)+(r/(2*D)) • noise z.1.1)‖^2+
        2*‖M (x (T z.1).1) (T z.1).2-Q (T z.1).1 z.2‖^2 := by
    have he₀ := hLip (center z.1.1) (x (anchor z.1.1)+(r/(2*D)) • noise z.1.1)
      (slotTransform (sqrtCoefficient a) a z.1.2)
    have heq := absorption_pathwise (D:=D) v M hshift (x (anchor z.1.1)) (sqrtCoefficient a) z.1.2 (noise z.1.1)
    rw [heq] at he₀
    have he := he₀
    have ht := norm_sub_le_norm_sub_add_norm_sub
      (M (center z.1.1) (slotTransform (sqrtCoefficient a) a z.1.2))
      (M (x (T z.1).1) (T z.1).2) (Q (anchor z.1.1) z.2)
    have hp := (sq_le_sq₀ (norm_nonneg _)
      (add_nonneg (mul_nonneg hK (norm_nonneg _)) (norm_nonneg _))).2
      (ht.trans (add_le_add he (le_refl _)))
    change _≤2*K^2*‖center z.1.1-(x (anchor z.1.1)+(r/(2*D)) • noise z.1.1)‖^2+
      2*‖M (x (T z.1).1) (T z.1).2-Q (anchor z.1.1) z.2‖^2
    nlinarith [sq_nonneg (K*‖center z.1.1-(x (anchor z.1.1)+(r/(2*D)) • noise z.1.1)‖-
      ‖M (x (T z.1).1) (T z.1).2-Q (anchor z.1.1) z.2‖)]
  have hdom := (hC.const_mul (2*K^2)).add (hJ.1.const_mul 2)
  have hi := hdom.mono' hmeas.aestronglyMeasurable (Filter.Eventually.of_forall (fun z => by
    simpa only [Real.norm_eq_abs,abs_sq,Pi.add_apply] using hbound z))
  refine ⟨Λ,(by first | infer_instance | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | (apply Measurable.aemeasurable; measurability) | measurability)),hΛ,?_,hi,(integral_mono hi hdom hbound).trans ?_⟩
  · rw [←hπnoise,←hΛmap,Measure.map_map (by fun_prop) (by fun_prop)]
    rfl
  · change (∫z : (Ω × (Fin k → E)) × E,
        2*K^2*‖center z.1.1-(x (anchor z.1.1)+(r/(2*D)) • noise z.1.1)‖^2+
        2*‖M (x (T z.1).1) (T z.1).2-Q (T z.1).1 z.2‖^2 ∂Λ)≤_
    rw [integral_add (hC.const_mul _) (hJ.1.const_mul _),integral_const_mul,integral_const_mul,hCeq,hJ.2]
    exact add_le_add (mul_le_mul_of_nonneg_left hce (by positivity))
      (mul_le_mul_of_nonneg_left hbe (by norm_num))
end LogConcaveSampling.Coupling

end

end

section

noncomputable section
namespace LogConcaveSampling.Coupling
open MeasureTheory ProbabilityTheory Function
open scoped Classical BigOperators NNReal

variable {Ω Γ W : Type*} [MeasurableSpace Ω] [MeasurableSpace Γ] [MeasurableSpace W]
  {d : ℕ}

theorem SquaredAt.of_joint (Λ : Measure W) [IsProbabilityMeasure Λ]
    (μ : Measure Ω) (ν : Measure Γ) (T : W → Ω) (U : W → Γ)
    (hT : Measurable T) (hU : Measurable U) (hl : Λ.map T=μ) (hr : Λ.map U=ν)
    (f : Ω → Point d) (g : Γ → Point d) (hf : Measurable f) (hg : Measurable g)
    {B : ℝ} (hi : Integrable (fun w => ‖f (T w)-g (U w)‖^2) Λ)
    (he : (∫w,‖f (T w)-g (U w)‖^2 ∂Λ)≤B) : SquaredAt μ ν f g B := by
  let J : W → Ω × Γ := fun w => (T w,U w)
  have hJ : Measurable J := hT.prodMk hU
  have hm : Measurable (fun z : Ω × Γ => ‖f z.1-g z.2‖^2) := by fun_prop
  refine ⟨Λ.map J,(by first | infer_instance | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | (apply Measurable.aemeasurable; measurability) | measurability)),?_,?_,?_,?_⟩
  · change (Λ.map J).map Prod.fst=μ
    rw [Measure.map_map measurable_fst hJ]
    exact hl
  · change (Λ.map J).map Prod.snd=ν
    rw [Measure.map_map measurable_snd hJ]
    exact hr
  · exact (integrable_map_measure hm.aestronglyMeasurable hJ.aemeasurable).mpr hi
  · rw [integral_map hJ.aemeasurable hm.aestronglyMeasurable]
    exact he

lemma SquaredAt.mono {μ : Measure Ω} {ν : Measure Γ} {f : Ω → Point d} {g : Γ → Point d}
    {B C : ℝ} (h : SquaredAt μ ν f g B) (hBC : B≤C) : SquaredAt μ ν f g C := by
  obtain ⟨κ,hκ,hl,hr,hi,he⟩ := h
  exact ⟨κ,hκ,hl,hr,hi,he.trans hBC⟩

lemma SquaredAt.reindex {Ω' Γ' : Type*} [MeasurableSpace Ω'] [MeasurableSpace Γ']
    {μ : Measure Ω} {ν : Measure Γ} {f : Ω → Point d} {g : Γ → Point d}
    {B : ℝ} (h : SquaredAt μ ν f g B) (T : Ω → Ω') (U : Γ → Γ')
    (hT : Measurable T) (hU : Measurable U)
    (f' : Ω' → Point d) (g' : Γ' → Point d) (hf' : Measurable f') (hg' : Measurable g')
    (hfe : ∀z,f' (T z)=f z) (hge : ∀z,g' (U z)=g z) :
    SquaredAt (μ.map T) (ν.map U) f' g' B := by
  obtain ⟨κ,hκ,hl,hr,hi,he⟩ := h
  have := hκ
  refine SquaredAt.of_joint κ (μ.map T) (ν.map U) (T ∘ Prod.fst) (U ∘ Prod.snd)
    (hT.comp measurable_fst) (hU.comp measurable_snd) ?_ ?_ f' g' hf' hg' ?_ ?_
  · rw [←Measure.map_map hT measurable_fst]; exact congrArg (Measure.map T) hl
  · rw [←Measure.map_map hU measurable_snd]; exact congrArg (Measure.map U) hr
  · simpa only [Function.comp_apply,hfe,hge] using hi
  · simpa only [Function.comp_apply,hfe,hge] using he

end LogConcaveSampling.Coupling

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
-- module Solutions.OAIQ048_LC.LogConcave_Dynamics_AbsorbFixed
attribute [-instance] _root_.OAI.LogConcaveSampling.LowerBound.couplingLaw_probability _root_.OAI.LogConcaveSampling.LowerBound.remainingHaar_probability _root_.OAI.LogConcaveSampling.LowerBound.roundRandomLaw_probability _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_invInvariant _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_isHaar _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_probability _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_rightInvariant _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_compactSpace _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_measurableInv _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_measurableMul _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_secondCountable _root_.OAI.LogConcaveSampling.MeanTree.instIsProbabilityMeasureRowTapeRowLaw _root_.OAI.LogConcaveSampling.OracleCompiler.topSeedLaw_probability _root_.OAI.LogConcaveSampling.noiseKernel_markov
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
namespace LogConcaveSampling.Coupling
open MeasureTheory ProbabilityTheory Function SeedCompiler
open scoped Classical BigOperators

variable {Ω : Type*} [MeasurableSpace Ω] {d k : ℕ}

theorem SquaredAt.absorb_fixed (μ : Measure Ω) [IsProbabilityMeasure μ]
    (f : Ω → Point d) (hf : Measurable f) (c b : Point d) {r D K S B τ : ℝ}
    (hD : 0<D) (hK : 0≤K) (v : Fin k → ℝ) (hv : (∑i,v i^2)≤D^2)
    (M : Point d → (Fin k → Point d) → Point d) (hm : Measurable (uncurry M))
    (hshift : ShiftInvariant r v M)
    (hLip : ∀x y g,‖M x g-M y g‖≤K*‖x-y‖)
    (hC : SquaredAt μ (stdGaussian (Point d)) f (fun g => c+(r/(2*D)) • g) S)
    (hM : SquaredAt (Measure.pi fun _ : Fin k => stdGaussian (Point d)) (stdGaussian (Point d))
      (M c) (fun g => b+τ • g) B) :
    SquaredAt (μ.prod (Measure.pi fun _ : Fin k => stdGaussian (Point d))) (stdGaussian (Point d))
      (fun z => M (f z.1) (slotTransform (sqrtCoefficient (fun i => v i/(2*D)))
        (fun i => v i/(2*D)) z.2)) (fun g => b+τ • g) (2*K^2*S+2*B) := by
  let γ := stdGaussian (Point d)
  let θ := Measure.pi fun _ : Fin k => γ
  obtain ⟨κ,hκ,hcl,hcr,hci,hce⟩ := hC
  let := hκ
  have hMR := hM.reindex (fun g => ((),g)) id (by fun_prop) measurable_id
    (fun z : Unit × (Fin k → Point d) => M c z.2) (fun g => b+τ • g)
    (hm.comp (measurable_const.prodMk measurable_snd)) (by fun_prop) (by intro; rfl) (by intro; rfl)
  rw [←Measure.dirac_prod (),Measure.map_id] at hMR
  obtain ⟨π,hπ,hpl,hpr,hpi,hpe⟩ := hMR
  let := hπ
  have hlaw : κ.map (fun z : Ω × Point d => ((),z.2))=(Measure.dirac ()).prod γ := by
    dsimp only [γ]
    rw [Measure.dirac_prod,←hcr]
    change _=(κ.map Prod.snd).map (Prod.mk ())
    rw [Measure.map_map (by fun_prop) measurable_snd]
    rfl
  have hnoise : π.map (fun z : (Unit × (Fin k → Point d)) × Point d => (z.1.1,z.2))=
      (Measure.dirac ()).prod γ := by
    dsimp only [γ]
    rw [Measure.dirac_prod,←hpr]
    change _=(π.map Prod.snd).map (Prod.mk ())
    rw [Measure.map_map (by fun_prop) measurable_snd]
    rfl
  obtain ⟨Λ,hΛ,hLl,hLr,hLi,hLe⟩ := absorb_coupling κ (Measure.dirac ()) γ
    (fun _ => ()) Prod.snd (fun z => f z.1) measurable_const measurable_snd
    (hf.comp measurable_fst) hlaw (fun _ => c) measurable_const hD hK v hv M hm hshift hLip
    (fun _ g => b+τ • g) (by fun_prop) hci hce π hpl hnoise hpi hpe
  let := hΛ
  let T : ((Ω × Point d) × (Fin k → Point d)) × Point d → Ω × (Fin k → Point d) :=
    fun z => (z.1.1.1,z.1.2)
  have hT : Measurable T := by unfold T; fun_prop
  have hTl : Λ.map T=μ.prod θ := by
    change Λ.map ((Prod.map Prod.fst id) ∘ Prod.fst)=_
    rw [←Measure.map_map (by fun_prop) measurable_fst]
    change Λ.fst.map (Prod.map Prod.fst id)=_
    rw [hLl,←Measure.map_prod_map _ _ measurable_fst measurable_id,Measure.map_id]
    change κ.fst.prod θ=μ.prod θ
    rw [hcl]
  have hLright : Λ.map Prod.snd=γ := by
    have H := congrArg (Measure.map Prod.snd) hLr
    rw [Measure.map_map measurable_snd (by fun_prop),Measure.map_snd_prod] at H
    simpa only [Function.comp_def,measure_univ,one_smul] using H
  exact SquaredAt.of_joint Λ (μ.prod θ) γ T Prod.snd hT measurable_snd hTl hLright
    _ _ (hm.comp ((hf.comp measurable_fst).prodMk (by
      dsimp only [slotTransform,slotSum]; fun_prop))) (by fun_prop) hLi hLe
end LogConcaveSampling.Coupling

end

end

section

noncomputable section
namespace LogConcaveSampling.Coupling
open MeasureTheory ProbabilityTheory
open scoped Classical BigOperators

variable {ι : Type*} [Fintype ι] {Ω Γ : ι → Type*}
  [∀i,MeasurableSpace (Ω i)] [∀i,MeasurableSpace (Γ i)] {d : ℕ}

theorem SquaredAt.weighted_pi (μ : ∀i,Measure (Ω i)) (ν : ∀i,Measure (Γ i))
    [∀i,IsProbabilityMeasure (μ i)] [∀i,IsProbabilityMeasure (ν i)]
    (f : ∀i,Ω i → Point d) (g : ∀i,Γ i → Point d)
    (hf : ∀i,Measurable (f i)) (hg : ∀i,Measurable (g i))
    (w B : ι → ℝ) (h : ∀i,SquaredAt (μ i) (ν i) (f i) (g i) (B i)) :
    SquaredAt (Measure.pi μ) (Measure.pi ν)
      (fun z => ∑i,w i • f i (z i)) (fun z => ∑i,w i • g i (z i))
      ((∑i,|w i|)*(∑i,|w i| * B i)) := by
  choose κ hκ hl hr hi he using h
  let : ∀i,IsProbabilityMeasure (κ i) := hκ
  let Λ := Measure.pi κ
  let T : (∀i,Ω i × Γ i) → (∀i,Ω i) := fun z i => (z i).1
  let U : (∀i,Ω i × Γ i) → (∀i,Γ i) := fun z i => (z i).2
  have hT : Measurable T := by unfold T; fun_prop
  have hU : Measurable U := by unfold U; fun_prop
  have hTl : Λ.map T=Measure.pi μ :=
    (measurePreserving_pi κ μ (fun i => ⟨measurable_fst,hl i⟩)).map_eq
  have hUl : Λ.map U=Measure.pi ν :=
    (measurePreserving_pi κ ν (fun i => ⟨measurable_snd,hr i⟩)).map_eq
  have hm (i : ι) : Measurable (fun z : Ω i × Γ i => f i z.1-g i z.2) := by fun_prop
  have hip (i : ι) : Integrable (fun z : ∀i,Ω i × Γ i => ‖f i (z i).1-g i (z i).2‖^2) Λ :=
    (measurePreserving_eval κ i).integrable_comp_of_integrable (hi i)
  have hep (i : ι) : (∫z : ∀i,Ω i × Γ i,‖f i (z i).1-g i (z i).2‖^2 ∂Λ)≤B i := by
    exact ((measurePreserving_eval κ i).hasLaw.integral_comp
      ((hm i).norm.pow_const 2).aestronglyMeasurable).trans_le (he i)
  have hs := RMSIntegral.weighted_sum_sq_varying w
    (fun i (z : ∀i,Ω i × Γ i) => f i (z i).1-g i (z i).2) B
    (fun i => ((hm i).comp (measurable_pi_apply i)).aestronglyMeasurable) hip hep
  have hid (z : ∀i,Ω i × Γ i) :
      (∑i,w i • f i (T z i))-(∑i,w i • g i (U z i))=
        ∑i,w i • (f i (z i).1-g i (z i).2) := by
    simp only [T,U,smul_sub,Finset.sum_sub_distrib]
  refine SquaredAt.of_joint Λ (Measure.pi μ) (Measure.pi ν) T U hT hU hTl hUl
    _ _ (by fun_prop) (by fun_prop) ?_ ?_
  · simpa only [hid] using hs.1
  · simpa only [hid] using hs.2
end LogConcaveSampling.Coupling

end

end

section

noncomputable section
namespace LogConcaveSampling.Coupling
open MeasureTheory ProbabilityTheory Function
open scoped Classical BigOperators

variable {Ω Γ W : Type*} [MeasurableSpace Ω] [MeasurableSpace Γ] [MeasurableSpace W] {d : ℕ}

theorem SquaredAt.common_noise {μ : Measure Ω} {ν : Measure Γ}
    {f : Ω → Point d} {g : Γ → Point d} (hf : Measurable f) (hg : Measurable g)
    {B : ℝ} (h : SquaredAt μ ν f g B) (ρ : Measure W) [IsProbabilityMeasure ρ]
    (hnoise : W → Point d) (hm : Measurable hnoise) :
    SquaredAt (μ.prod ρ) (ν.prod ρ) (fun z => f z.1+hnoise z.2)
      (fun z => g z.1+hnoise z.2) B := by
  obtain ⟨κ,hκ,hl,hr,hi,he⟩ := h
  let := hκ
  let T : (Ω × Γ) × W → Ω × W := Prod.map Prod.fst id
  let U : (Ω × Γ) × W → Γ × W := Prod.map Prod.snd id
  have hT : Measurable T := by fun_prop
  have hU : Measurable U := by fun_prop
  have hTl : (κ.prod ρ).map T=μ.prod ρ := by
    rw [←Measure.map_prod_map _ _ measurable_fst measurable_id,Measure.map_id]
    change κ.fst.prod ρ=μ.prod ρ
    rw [hl]
  have hUl : (κ.prod ρ).map U=ν.prod ρ := by
    rw [←Measure.map_prod_map _ _ measurable_snd measurable_id,Measure.map_id]
    change κ.snd.prod ρ=ν.prod ρ
    rw [hr]
  have hcost (z : (Ω × Γ) × W) :
      ‖(f (T z).1+hnoise (T z).2)-(g (U z).1+hnoise (U z).2)‖^2=‖f z.1.1-g z.1.2‖^2 := by
    dsimp only [T,U,Prod.map]; rw [add_sub_add_right_eq_sub]
  refine SquaredAt.of_joint (κ.prod ρ) (μ.prod ρ) (ν.prod ρ) T U hT hU hTl hUl
    _ _ (by fun_prop) (by fun_prop) ?_ ?_
  · simpa only [hcost] using hi.comp_fst ρ
  · simp_rw [hcost]
    rw [integral_prod _ (hi.comp_fst ρ)]
    simpa only [integral_const,probReal_univ,one_smul] using he
end LogConcaveSampling.Coupling

end

end

end OAI
end

section
-- module Solutions.OAIQ048_LC.LogConcave_Dynamics_NormSubSqThree
attribute [-instance] _root_.OAI.LogConcaveSampling.LowerBound.couplingLaw_probability _root_.OAI.LogConcaveSampling.LowerBound.remainingHaar_probability _root_.OAI.LogConcaveSampling.LowerBound.roundRandomLaw_probability _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_invInvariant _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_isHaar _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_probability _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_rightInvariant _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_compactSpace _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_measurableInv _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_measurableMul _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_secondCountable _root_.OAI.LogConcaveSampling.MeanTree.instIsProbabilityMeasureRowTapeRowLaw _root_.OAI.LogConcaveSampling.OracleCompiler.topSeedLaw_probability _root_.OAI.LogConcaveSampling.noiseKernel_markov
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
namespace LogConcaveSampling.Coupling
open MeasureTheory ProbabilityTheory Function
open scoped Classical

variable {Ω Γ W : Type*} [MeasurableSpace Ω] [MeasurableSpace Γ] [MeasurableSpace W]
  {d : ℕ}

lemma norm_sub_sq_three (x y z : Point d) : ‖x-z‖^2≤2*‖x-y‖^2+2*‖y-z‖^2 := by
  have h := norm_sub_le_norm_sub_add_norm_sub x y z
  nlinarith [sq_nonneg (‖x-y‖-‖y-z‖),norm_nonneg (x-z),norm_nonneg (x-y),norm_nonneg (y-z)]

theorem SquaredAt.trans [StandardBorelSpace W] [Nonempty W]
    {μ : Measure Ω} {ν : Measure Γ} {θ : Measure W} {f : Ω → Point d}
    {g : Γ → Point d} {h : W → Point d} (hf : Measurable f) (hg : Measurable g) (hh : Measurable h)
    {B C : ℝ} (h₁ : SquaredAt μ ν f g B) (h₂ : SquaredAt ν θ g h C) :
    SquaredAt μ θ f h (2*B+2*C) := by
  obtain ⟨κ,hκ,hl,hr,hi,he⟩ := h₁
  obtain ⟨ι,hι,hll,hrr,hii,hee⟩ := h₂
  let := hκ
  let := hι
  have hlink : κ.map Prod.snd=ι.fst := hr.trans hll.symm
  let Λ := lift κ ι Prod.snd measurable_snd
  have hp : Λ.fst=κ := lift_fst κ ι Prod.snd measurable_snd
  have hm : Λ.map (fun z => (z.1.2,z.2))=ι := lift_map κ ι Prod.snd measurable_snd hlink
  have hi₁ : Integrable (fun z : (Ω × Γ) × W => ‖f z.1.1-g z.1.2‖^2) Λ := by
    have hk : Integrable (fun z : Ω × Γ => ‖f z.1-g z.2‖^2) (Λ.map Prod.fst) := by
      change Integrable _ Λ.fst
      rw [hp]
      exact hi
    exact hk.comp_measurable measurable_fst
  have E₁ : (∫z,‖f z.1.1-g z.1.2‖^2 ∂Λ)≤B := by
    have hm₁ : Measurable (fun z : Ω × Γ => ‖f z.1-g z.2‖^2) := by fun_prop
    rw [←integral_map measurable_fst.aemeasurable hm₁.aestronglyMeasurable]
    change (∫z,‖f z.1-g z.2‖^2 ∂Λ.fst)≤B
    rw [hp]
    exact he
  have H₂ := lift_integrable κ ι Prod.snd measurable_snd hlink _ hii
  have hi₂ : Integrable (fun z : (Ω × Γ) × W => ‖g z.1.2-h z.2‖^2) Λ := H₂.1
  have E₂ : (∫z,‖g z.1.2-h z.2‖^2 ∂Λ)≤C := H₂.2.trans_le hee
  have hdom := (hi₁.const_mul 2).add (hi₂.const_mul 2)
  have hb (z : (Ω × Γ) × W) : ‖f z.1.1-h z.2‖^2≤
      2*‖f z.1.1-g z.1.2‖^2+2*‖g z.1.2-h z.2‖^2 := norm_sub_sq_three _ _ _
  have hcost : Measurable (fun z : (Ω × Γ) × W => ‖f z.1.1-h z.2‖^2) := by fun_prop
  have hnew := hdom.mono' hcost.aestronglyMeasurable
    (Filter.Eventually.of_forall fun z => by simpa only [Real.norm_eq_abs,abs_sq,Pi.add_apply] using hb z)
  refine SquaredAt.of_joint Λ μ θ (fun z => z.1.1) Prod.snd (by fun_prop) measurable_snd
    ?_ ?_ f h hf hh hnew ?_
  · change Measure.map (Prod.fst ∘ Prod.fst) Λ=μ
    rw [←Measure.map_map measurable_fst measurable_fst]
    change Λ.fst.map Prod.fst=μ
    rw [hp]
    exact hl
  · have hs := congrArg (Measure.map Prod.snd) hm
    rw [Measure.map_map measurable_snd (by fun_prop)] at hs
    exact hs.trans hrr
  · apply (integral_mono hnew hdom hb).trans
    simp only [Pi.add_apply]
    rw [integral_add (hi₁.const_mul 2) (hi₂.const_mul 2),integral_const_mul,integral_const_mul]
    linarith

lemma SquaredAt.same_tape (μ : Measure Ω) [IsProbabilityMeasure μ]
    (f g : Ω → Point d) (hf : Measurable f) (hg : Measurable g) {B : ℝ}
    (hi : Integrable (fun z => ‖f z-g z‖^2) μ) (he : (∫z,‖f z-g z‖^2 ∂μ)≤B) :
    SquaredAt μ μ f g B :=
  SquaredAt.of_joint μ μ μ id id measurable_id measurable_id (Measure.map_id) (Measure.map_id)
    f g hf hg hi he
end LogConcaveSampling.Coupling

end

end

end OAI
end

section
-- module Solutions.OAIQ048_LC.LogConcave_Dynamics_SameLaw
attribute [-instance] _root_.OAI.LogConcaveSampling.LowerBound.couplingLaw_probability _root_.OAI.LogConcaveSampling.LowerBound.remainingHaar_probability _root_.OAI.LogConcaveSampling.LowerBound.roundRandomLaw_probability _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_invInvariant _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_isHaar _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_probability _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_rightInvariant _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_compactSpace _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_measurableInv _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_measurableMul _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_secondCountable _root_.OAI.LogConcaveSampling.MeanTree.instIsProbabilityMeasureRowTapeRowLaw _root_.OAI.LogConcaveSampling.OracleCompiler.topSeedLaw_probability _root_.OAI.LogConcaveSampling.noiseKernel_markov
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
namespace LogConcaveSampling.Coupling
open MeasureTheory ProbabilityTheory Function
open scoped Classical

variable {Ω Γ : Type*} [MeasurableSpace Ω] [MeasurableSpace Γ]
  [StandardBorelSpace Γ] [Nonempty Γ] {d : ℕ}

theorem SquaredAt.of_same_law (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ν : Measure Γ) [IsProbabilityMeasure ν] (f : Ω → Point d) (g : Γ → Point d)
    (hf : Measurable f) (hg : Measurable g) (hlaw : μ.map f=ν.map g) :
    SquaredAt μ ν f g 0 := by
  let J : Γ → Point d × Γ := fun z => (g z,z)
  have hJ : Measurable J := hg.prodMk measurable_id
  let ι := ν.map J
  have : IsProbabilityMeasure ι := by first | infer_instance | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | (apply Measurable.aemeasurable; measurability) | measurability)
  have hl : ι.fst=ν.map g := by
    change (ν.map J).map Prod.fst=_
    rw [Measure.map_map measurable_fst hJ]
    rfl
  have hr : ι.snd=ν := by
    change (ν.map J).map Prod.snd=_
    rw [Measure.map_map measurable_snd hJ]
    exact Measure.map_id
  let Λ := lift μ ι f hf
  have hlink : μ.map f=ι.fst := hlaw.trans hl.symm
  have hm : Measurable (fun z : Point d × Γ => ‖z.1-g z.2‖^2) := by fun_prop
  have hi : Integrable (fun z : Point d × Γ => ‖z.1-g z.2‖^2) ι := by
    apply (integrable_map_measure hm.aestronglyMeasurable hJ.aemeasurable).mpr
    change Integrable (fun z => ‖g z-g z‖^2) ν
    simpa only [sub_self,norm_zero,zero_pow (by decide : 2≠0)] using
      (integrable_const (0 : ℝ) : Integrable (fun _ : Γ => (0 : ℝ)) ν)
  have he : (∫z : Point d × Γ,‖z.1-g z.2‖^2 ∂ι)=0 := by
    rw [integral_map hJ.aemeasurable hm.aestronglyMeasurable]
    simp [J]
  obtain ⟨hI,hE⟩ := lift_integrable μ ι f hf hlink _ hi
  refine ⟨Λ,(by first | infer_instance | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | (apply Measurable.aemeasurable; measurability) | measurability)),lift_fst μ ι f hf,?_,hI,hE.trans_le he.le⟩
  have hh := congrArg (Measure.map Prod.snd) (lift_map μ ι f hf hlink)
  rw [Measure.map_map measurable_snd (by fun_prop)] at hh
  exact hh.trans hr

lemma SquaredAt.change_ideal {W : Type*} [MeasurableSpace W]
    {μ : Measure Ω} {ν : Measure W} [IsProbabilityMeasure ν]
    (θ : Measure Γ) [IsProbabilityMeasure θ]
    {f : Ω → Point d} {g : W → Point d} (h : Γ → Point d)
    (hf : Measurable f) (hg : Measurable g) (hh : Measurable h)
    {B : ℝ} (hc : SquaredAt μ ν f g B) (hlaw : ν.map g=θ.map h) :
    SquaredAt μ θ f h (2*B) := by
  have hzero := SquaredAt.of_same_law ν θ g h hg hh hlaw
  simpa only [mul_zero,add_zero] using hc.trans hf hg hh hzero

end LogConcaveSampling.Coupling

end

end

end OAI
end

section
-- module Solutions.OAIQ048_LC.LogConcave_Dynamics_SharedLipschitz
attribute [-instance] _root_.OAI.LogConcaveSampling.LowerBound.couplingLaw_probability _root_.OAI.LogConcaveSampling.LowerBound.remainingHaar_probability _root_.OAI.LogConcaveSampling.LowerBound.roundRandomLaw_probability _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_invInvariant _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_isHaar _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_probability _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_rightInvariant _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_compactSpace _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_measurableInv _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_measurableMul _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_secondCountable _root_.OAI.LogConcaveSampling.MeanTree.instIsProbabilityMeasureRowTapeRowLaw _root_.OAI.LogConcaveSampling.OracleCompiler.topSeedLaw_probability _root_.OAI.LogConcaveSampling.noiseKernel_markov
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
namespace LogConcaveSampling.Coupling
open MeasureTheory ProbabilityTheory Function
open scoped Classical

variable {Ω Γ W : Type*} [MeasurableSpace Ω] [MeasurableSpace Γ] [MeasurableSpace W]
  {d e : ℕ}

theorem SquaredAt.shared_lipschitz {μ : Measure Ω} {ν : Measure Γ}
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (η : Measure W) [IsProbabilityMeasure η]
    {f : Ω → Point d} {g : Γ → Point d} (hf : Measurable f) (hg : Measurable g)
    {B K : ℝ} (hK : 0≤K) (hc : SquaredAt μ ν f g B)
    (H : Point d → W → Point e) (hH : Measurable (uncurry H))
    (hLip : ∀x y w,‖H x w-H y w‖≤K*‖x-y‖) :
    SquaredAt (μ.prod η) (ν.prod η) (fun z => H (f z.1) z.2)
      (fun z => H (g z.1) z.2) (K^2*B) := by
  obtain ⟨κ,hκ,hl,hr,hi,he⟩ := hc
  let := hκ
  let Λ := κ.prod η
  have hΛf : Λ.map (fun z => (z.1.1,z.2))=μ.prod η := by
    rw [show (fun z : (Ω × Γ) × W => (z.1.1,z.2))=Prod.map Prod.fst id from rfl]
    rw [←Measure.map_prod_map _ _ measurable_fst measurable_id,Measure.map_id]
    exact congrArg (fun m => m.prod η) hl
  have hΛg : Λ.map (fun z => (z.1.2,z.2))=ν.prod η := by
    rw [show (fun z : (Ω × Γ) × W => (z.1.2,z.2))=Prod.map Prod.snd id from rfl]
    rw [←Measure.map_prod_map _ _ measurable_snd measurable_id,Measure.map_id]
    exact congrArg (fun m => m.prod η) hr
  have hm : Measurable (fun z : Ω × Γ => ‖f z.1-g z.2‖^2) := by fun_prop
  have hi' : Integrable (fun z : (Ω × Γ) × W => ‖f z.1.1-g z.1.2‖^2) Λ := hi.comp_fst η
  have hp (z : (Ω × Γ) × W) : ‖H (f z.1.1) z.2-H (g z.1.2) z.2‖^2≤
      K^2*‖f z.1.1-g z.1.2‖^2 := by
    simpa only [mul_pow] using pow_le_pow_left₀ (norm_nonneg _) (hLip _ _ _) 2
  have hcmeas : Measurable (fun z : (Ω × Γ) × W => ‖H (f z.1.1) z.2-H (g z.1.2) z.2‖^2) := by
    have h₁ : Measurable (fun z : (Ω × Γ) × W => H (f z.1.1) z.2) := hH.comp ((hf.comp (measurable_fst.comp measurable_fst)).prodMk measurable_snd)
    have h₂ : Measurable (fun z : (Ω × Γ) × W => H (g z.1.2) z.2) := hH.comp ((hg.comp (measurable_snd.comp measurable_fst)).prodMk measurable_snd)
    exact (h₁.sub h₂).norm.pow_const 2
  have hdom := hi'.const_mul (K^2)
  have hIi := hdom.mono' hcmeas.aestronglyMeasurable (Filter.Eventually.of_forall fun z => by
    simpa only [Real.norm_eq_abs,abs_sq] using hp z)
  refine SquaredAt.of_joint Λ (μ.prod η) (ν.prod η)
    (fun z => (z.1.1,z.2)) (fun z => (z.1.2,z.2)) (by fun_prop) (by fun_prop)
    hΛf hΛg _ _ ?_ ?_ hIi ?_
  · exact hH.comp ((hf.comp measurable_fst).prodMk measurable_snd)
  · exact hH.comp ((hg.comp measurable_fst).prodMk measurable_snd)
  · apply (integral_mono hIi hdom hp).trans
    rw [integral_const_mul]
    have hfst : ∫z : (Ω × Γ) × W, ‖f z.1.1-g z.1.2‖^2 ∂Λ = ∫z, ‖f z.1-g z.2‖^2 ∂κ := by
      exact (measurePreserving_fst (μ:=κ) (ν:=η)).hasLaw.integral_comp hm.aestronglyMeasurable
    rw [hfst]
    exact mul_le_mul_of_nonneg_left he (pow_nonneg hK 2)

lemma SquaredAt.add_shared {μ : Measure Ω} {ν : Measure Γ}
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (η : Measure W) [IsProbabilityMeasure η]
    {f : Ω → Point d} {g : Γ → Point d} (hf : Measurable f) (hg : Measurable g)
    {B : ℝ} (hc : SquaredAt μ ν f g B) (h : W → Point d) (hh : Measurable h) :
    SquaredAt (μ.prod η) (ν.prod η) (fun z => f z.1+h z.2) (fun z => g z.1+h z.2) B := by
  simpa only [one_pow,one_mul] using hc.shared_lipschitz η hf hg (by norm_num : (0:ℝ)≤1)
    (fun x w => x+h w) (by fun_prop) (fun x y w => by rw [add_sub_add_right_eq_sub,one_mul])

end LogConcaveSampling.Coupling

end

end

section

noncomputable section
namespace LogConcaveSampling.Coupling
open MeasureTheory ProbabilityTheory Function
open scoped Classical

variable {X Ω Γ : Type*} [MeasurableSpace X] [MeasurableSpace Ω] [MeasurableSpace Γ]
  {d : ℕ}

theorem SquaredAt.mixture (μ : Measure X) [IsProbabilityMeasure μ]
    (ν : Measure Ω) [IsProbabilityMeasure ν] (θ : Measure Γ) [IsProbabilityMeasure θ]
    (K : Kernel X (Ω × Γ)) [IsMarkovKernel K]
    (hl : ∀x,(K x).fst=ν) (hr : ∀x,(K x).snd=θ)
    (f : X → Ω → Point d) (g : X → Γ → Point d)
    (hf : Measurable (uncurry f)) (hg : Measurable (uncurry g))
    (B : X → ℝ) (hB : Integrable B μ)
    (hi : ∀x,Integrable (fun z => ‖f x z.1-g x z.2‖^2) (K x))
    (he : ∀x,(∫z,‖f x z.1-g x z.2‖^2 ∂K x)≤B x) :
    SquaredAt (μ.prod ν) (μ.prod θ) (uncurry f) (uncurry g) (∫x,B x ∂μ) := by
  let Λ := μ ⊗ₘ K
  let F : X × (Ω × Γ) → ℝ := fun z => ‖f z.1 z.2.1-g z.1 z.2.2‖^2
  have hF : Measurable F := by unfold F; fun_prop
  have hFi : Integrable (fun x => ∫z,F (x,z) ∂K x) μ := by
    apply hB.mono' hF.stronglyMeasurable.integral_kernel_prod_right'.aestronglyMeasurable
    exact Filter.Eventually.of_forall (fun x => by
      rw [Real.norm_of_nonneg (integral_nonneg fun _ => sq_nonneg _)]
      exact he x)
  have hI : Integrable F Λ := by
    apply (Measure.integrable_compProd_iff hF.aestronglyMeasurable).mpr
    refine ⟨Filter.Eventually.of_forall hi,?_⟩
    simpa only [F,Real.norm_eq_abs,abs_sq] using hFi
  have hleft : K.map Prod.fst=Kernel.const X ν := by
    ext x s hs
    rw [Kernel.map_apply _ measurable_fst]
    exact congrArg (fun m : Measure Ω => m s) (hl x)
  have hright : K.map Prod.snd=Kernel.const X θ := by
    ext x s hs
    rw [Kernel.map_apply _ measurable_snd]
    exact congrArg (fun m : Measure Γ => m s) (hr x)
  apply SquaredAt.of_joint Λ (μ.prod ν) (μ.prod θ)
    (fun z => (z.1,z.2.1)) (fun z => (z.1,z.2.2)) (by fun_prop) (by fun_prop)
    ?_ ?_ (uncurry f) (uncurry g) hf hg hI
  · change (∫z,F z ∂Λ)≤_
    rw [Measure.integral_compProd hI]
    exact integral_mono hFi hB he
  · change Λ.map (Prod.map id Prod.fst)=_
    dsimp only [Λ]
    rw [←Measure.compProd_map measurable_fst,hleft,Measure.compProd_const]
  · change Λ.map (Prod.map id Prod.snd)=_
    dsimp only [Λ]
    rw [←Measure.compProd_map measurable_snd,hright,Measure.compProd_const]
end LogConcaveSampling.Coupling

end

end

section

noncomputable section
namespace LogConcaveSampling.Coupling
open MeasureTheory ProbabilityTheory Function Set TopologicalSpace
open scoped Classical

variable {X Ω Γ : Type*} [PseudoMetricSpace X] [SeparableSpace X] [Nonempty X]
  [MeasurableSpace X] [BorelSpace X] [MeasurableSpace Ω] [MeasurableSpace Γ]
  {d : ℕ}

theorem SquaredAt.random_anchor (μ : Measure X) [IsProbabilityMeasure μ]
    (ν : Measure Ω) [IsProbabilityMeasure ν] (θ : Measure Γ) [IsProbabilityMeasure θ]
    (f : X → Ω → Point d) (g : X → Γ → Point d)
    (hf : Measurable (uncurry f)) (hg : Measurable (uncurry g))
    (ρ : X → ℝ) (hρ : ∀x,1≤ρ x) (hρlip : ∀x y,ρ y≤ρ x+dist x y)
    (hρi : Integrable (fun x => (ρ x)^2) μ)
    {Lf Lg E : ℝ} (hLf : 0≤Lf) (hLg : 0≤Lg) (hE : 0<E)
    (hfl : ∀x y z,‖f x z-f y z‖≤Lf*dist x y)
    (hgl : ∀x y z,‖g x z-g y z‖≤Lg*dist x y)
    (hc : ∀x,SquaredAt ν θ (f x) (g x) (E^2*(ρ x)^2)) :
    SquaredAt (μ.prod ν) (μ.prod θ) (uncurry f) (uncurry g)
      (10*E^2*(∫x,(ρ x)^2 ∂μ)) := by
  let e := min 1 (E/(Lf+Lg+1))
  have hden : 0<Lf+Lg+1 := by linarith
  have he : 0<e := lt_min (by norm_num) (div_pos hE hden)
  have he1 : e≤1 := min_le_left _ _
  have heE : (Lf+Lg)*e≤E := by
    have hh := (le_div_iff₀ hden).mp (min_le_right (1:ℝ) (E/(Lf+Lg+1)))
    change e*(Lf+Lg+1)≤E at hh
    nlinarith
  obtain ⟨q,hq,hqe,K,hK,hcouple⟩ := measurable_coupling_of_pointwise ν θ f g hf hg
    (fun x => E^2*(ρ x)^2) hLf hLg he hfl hgl hc
  let := hK
  have hb (x) : 2*(E^2*(ρ (denseSeq X (q x)))^2)+2*((Lf+Lg)*e)^2≤10*E^2*(ρ x)^2 := by
    have hh : ρ (denseSeq X (q x)) ≤ ρ x + e := by
      calc
        _ ≤ ρ x + dist x (denseSeq X (q x)) := hρlip _ _
        _ ≤ ρ x + e := by gcongr; exact (hqe x).le
    have hρx := hρ x
    have hρy := hρ (denseSeq X (q x))
    have hy : (ρ (denseSeq X (q x)))^2≤4*(ρ x)^2 := by nlinarith
    have hys := mul_le_mul_of_nonneg_left hy (sq_nonneg E)
    have hz : ((Lf+Lg)*e)^2≤E^2 := pow_le_pow_left₀ (by positivity) heE 2
    nlinarith [sq_nonneg E,mul_nonneg (sq_nonneg E) (show 0≤(ρ x)^2-1 by nlinarith)]
  have hm := SquaredAt.mixture μ ν θ K (fun x => (hcouple x).1) (fun x => (hcouple x).2.1)
    f g hf hg (fun x => 10*E^2*(ρ x)^2) (hρi.const_mul _) (fun x => (hcouple x).2.2.1)
    (fun x => (hcouple x).2.2.2.trans (hb x))
  simpa only [integral_const_mul] using hm

end LogConcaveSampling.Coupling

end

end

end OAI
end

section
-- module Solutions.OAIQ048_LC.LogConcave_Numerics_Correction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
namespace LogConcaveSampling.FinitePicard
open scoped NNReal BigOperators

variable {I E X : Type*} [Fintype I] [NormedAddCommGroup E] [NormedSpace ℝ E]
  [PseudoMetricSpace X]

omit [PseudoMetricSpace X] in
lemma nodes_eq_iterate (w : I → I → ℝ) (φ : I → E → E) (a : X → I → E)
    (n : ℕ) (x : X) : nodes w φ a n x=(step w φ (a x))^[n] (a x) := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [nodes,ih,Function.iterate_succ_apply']

end LogConcaveSampling.FinitePicard

end

end

end

end OAI
end

section
-- module Solutions.OAIQ048_LC.LogConcave_Sampling_KernelTransportAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section

noncomputable section
namespace LogConcaveSampling
open Set MeasureTheory Quadrature
open scoped Classical BigOperators NNReal

lemma finite_weighted_lipschitz {I X E : Type*} [Fintype I]
    [PseudoMetricSpace X] [NormedAddCommGroup E] [NormedSpace ℝ E]
    (w : I → ℝ) (f : I → X → E) {K : ℝ≥0} (hf : ∀i,LipschitzWith K (f i)) :
    LipschitzWith ((∑i,‖w i‖₊)*K) (fun x => ∑i,w i • f i x) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  rw [dist_eq_norm,←Finset.sum_sub_distrib]
  simp_rw [←smul_sub]
  calc
    _ ≤ ∑i,‖w i • (f i x-f i y)‖ := norm_sum_le _ _
    _ = ∑i,|w i| *dist (f i x) (f i y) := by simp only [norm_smul,Real.norm_eq_abs,dist_eq_norm]
    _ ≤ ∑i,|w i| *((K:ℝ)*dist x y) := Finset.sum_le_sum (fun i _ =>
      mul_le_mul_of_nonneg_left ((hf i).dist_le_mul x y) (abs_nonneg _))
    _ = _ := by simp only [←Finset.sum_mul,NNReal.coe_mul,NNReal.coe_sum,coe_nnnorm,Real.norm_eq_abs,mul_assoc]

end LogConcaveSampling

end

end

end

end OAI
end

section
-- module Solutions.OAIQ048_LC.LogConcave_Sampling_ProbabilityEndpoint
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section

noncomputable section
namespace LogConcaveSampling
open Set Quadrature

lemma probabilityEndpoint_time {T h : ℝ} (hT0 : 0<T) (hT1 : T<1) (hh : 0<h)
    (n : ℕ) (hn : 0<n) : probabilityNodeTime T h n (probabilityEndpoint hT0 hT1 hh n)=T := by
  have hlast : probabilityNodes n (Fin.last n)=1 := by
    change (n:ℝ)/(n:ℝ)=1
    exact div_self (by exact_mod_cast hn.ne')
  have hN : logMeshCount T h-1+1=logMeshCount T h := by have := logMeshCount_pos hT0 hT1 hh; omega
  simp only [probabilityNodeTime,probabilityEndpoint,hlast,mul_one,probabilityCellLength]
  rw [hN,logMeshNode_last hT0 hT1 hh]
  ring
end LogConcaveSampling

end

end

end

end OAI
end

section
-- module Solutions.OAIQ048_LC.LogConcave_Numerics_Picard
attribute [-instance] _root_.OAI.LogConcaveSampling.LowerBound.couplingLaw_probability _root_.OAI.LogConcaveSampling.LowerBound.remainingHaar_probability _root_.OAI.LogConcaveSampling.LowerBound.roundRandomLaw_probability _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_invInvariant _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_isHaar _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_probability _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_rightInvariant _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_compactSpace _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_measurableInv _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_measurableMul _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_secondCountable _root_.OAI.LogConcaveSampling.MeanTree.instIsProbabilityMeasureRowTapeRowLaw _root_.OAI.LogConcaveSampling.OracleCompiler.topSeedLaw_probability _root_.OAI.LogConcaveSampling.noiseKernel_markov
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
namespace LogConcaveSampling.MeanTree
open Set MeasureTheory Quadrature FinitePicard
open scoped Classical BigOperators NNReal

variable {X : Type*} [MeasurableSpace X] {d : ℕ}

lemma eval_picard {I : Type*} [Fintype I] (F : Point d → ℝ)
    (w : I → I → ℝ) (φ : I → MeanTree X d → MeanTree X d)
    (a : I → MeanTree X d) (V : X → I → Point d → Point d)
    (hφ : ∀j E z,eval F (φ j E) z=V z j (eval F E z)) (N : ℕ) (z : X) (i : I) :
    eval F (picard w φ a N i) z=
      nodes w (V z) (fun (_ : Unit) j => eval F (a j) z) N () i := by
  induction N generalizing i with
  | zero => rfl
  | succ N ih =>
    simp only [picard,eval_add,eval_sumFamily,eval_scale,hφ,ih,nodes,step,correction,Pi.add_apply]

end LogConcaveSampling.MeanTree

end

end

section

noncomputable section
namespace LogConcaveSampling.MeanTree
open MeasureTheory Quadrature
open scoped Classical BigOperators

variable {X : Type*} [MeasurableSpace X] {d : ℕ}

lemma weight_nonneg (E : MeanTree X d) : 0≤weight E := by
  cases E
  exact Finset.sum_nonneg (fun i _ => abs_nonneg _)
lemma centersBound_sumFin (A : ℝ) (k : ℕ) (E : Fin k → MeanTree X d)
    (hE : ∀i,centersBound A (E i)) : centersBound A (sumFin k E) := by
  induction k with
  | zero => simp [sumFin]
  | succ k ih => exact (centersBound_add _ _ _).2 ⟨hE 0,ih _ (fun i => hE i.succ)⟩
lemma centersBound_sumFamily {I : Type*} [Fintype I] (A : ℝ) (E : I → MeanTree X d)
    (hE : ∀i,centersBound A (E i)) : centersBound A (sumFamily E) := by
  exact centersBound_sumFin A _ _ (fun i => hE _)
lemma centersBound_conditional {A r t : ℝ} {x y : MeanTree X d}
    (hx : centersBound A x) (hy : centersBound A y)
    (hw : weight x+|r*t| * weight y≤A) : centersBound A (conditional r t x y) := by
  simp only [conditional,centersBound_mean,weight_add,weight_scale,centersBound_add,centersBound_scale]
  exact ⟨hw,hx,hy⟩

lemma weight_picard {I : Type*} [Fintype I] (w : I → I → ℝ)
    (φ : I → MeanTree X d → MeanTree X d) (a : I → MeanTree X d)
    {B C : ℝ} (hC : 0≤C) (hw : ∀i,∑j,|w i j|≤B)
    (hφ : ∀i E,weight (φ i E)≤C) (N : ℕ) (i : I) :
    weight (picard w φ a N i)≤weight (a i)+B*C := by
  have hB : 0≤B := (Finset.sum_nonneg (fun _ _ => abs_nonneg _)).trans (hw i)
  cases N with
  | zero => simpa only [picard] using (le_add_of_nonneg_right (a:=weight (a i)) (mul_nonneg hB hC))
  | succ N =>
    simp only [picard,weight_add,weight_sumFamily,weight_scale]
    apply add_le_add_right
    calc
      _≤∑j,|w i j| * C := Finset.sum_le_sum (fun j _ => mul_le_mul_of_nonneg_left (hφ j _) (abs_nonneg _))
      _=(∑j,|w i j|)*C := (Finset.sum_mul _ _ _).symm
      _≤B*C := mul_le_mul_of_nonneg_right (hw i) hC

end LogConcaveSampling.MeanTree

end

end

end OAI
end

section
-- module Solutions.OAIQ048_LC.LogConcave_OraclePrograms_CircuitD
attribute [-instance] _root_.OAI.LogConcaveSampling.LowerBound.couplingLaw_probability _root_.OAI.LogConcaveSampling.LowerBound.remainingHaar_probability _root_.OAI.LogConcaveSampling.LowerBound.roundRandomLaw_probability _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_invInvariant _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_isHaar _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_probability _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_rightInvariant _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_compactSpace _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_measurableInv _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_measurableMul _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_secondCountable _root_.OAI.LogConcaveSampling.MeanTree.instIsProbabilityMeasureRowTapeRowLaw _root_.OAI.LogConcaveSampling.OracleCompiler.topSeedLaw_probability _root_.OAI.LogConcaveSampling.noiseKernel_markov
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
namespace LogConcaveSampling
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators NNReal

lemma circuitD_nonneg {d : ℕ} (F : Point d → ℝ) (x : Point d) : 0 ≤ circuitD F x := by
  unfold circuitD; positivity
lemma sqrt_le_circuitD {d : ℕ} (F : Point d → ℝ) (x : Point d) : Real.sqrt d ≤ circuitD F x := by
  unfold circuitD; exact le_add_of_nonneg_right (norm_nonneg _)
lemma field_zero_eq_gradient {d : ℕ} (F : Point d → ℝ) (x : Point d) (r : ℝ) :
    primitiveField F x r 0=gradient F x := by simp [primitiveField]

end LogConcaveSampling

end

end

section

noncomputable section
namespace LogConcaveSampling
open MeasureTheory Set
open scoped Classical BigOperators NNReal

variable {d : ℕ}

lemma circuitD_change {F : Point d → ℝ} {lam : ℝ≥0} (hF : Primitive F lam)
    (x y : Point d) : circuitD F y ≤ circuitD F x+(lam:ℝ)*‖y-x‖ := by
  have he := hF.gradient_lipschitz.dist_le_mul y x
  rw [dist_eq_norm,dist_eq_norm] at he
  have hn := norm_le_norm_add_norm_sub (gradient F x) (gradient F y)
  rw [norm_sub_rev] at hn
  dsimp [circuitD]
  linarith

lemma primitiveExpectedField_growth {F : Point d → ℝ} {lam : ℝ≥0}
    (hF : Primitive F lam) (x : Point d) {r : ℝ} (hr : 0 ≤ r)
    (hl : (lam:ℝ)*r^2≤1/2) (hL : (lam:ℝ)*r≤1) :
    ‖primitiveExpectedField F x r‖≤(2*Real.pi+2)*circuitD F x := by
  have he := terminal_mean_error hF x hr hl (0:Point d)
  rw [norm_zero,add_zero,field_zero_eq_gradient] at he
  have hn := norm_le_norm_add_norm_sub (gradient F x) (primitiveExpectedField F x r)
  have h₁ := mul_le_mul_of_nonneg_right hL (show 0≤2*Real.pi*Real.sqrt d by positivity)
  have h₂ := mul_le_mul_of_nonneg_right hl (show 0≤2*‖gradient F x‖ by positivity)
  have h₃ := mul_nonneg (show 0≤2*Real.pi by positivity) (norm_nonneg (gradient F x))
  dsimp [circuitD]
  nlinarith [Real.sqrt_nonneg (d:ℝ)]

namespace MeanTree
variable {X : Type*} [MeasurableSpace X]

theorem eval_circuitD_bound {F : Point d → ℝ} {lam : ℝ≥0} (hF : Primitive F lam)
    (x : Point d) (z : X) {A B : ℝ} (hB : 0≤B)
    (hsmall : (lam:ℝ)*A*(2*Real.pi+2)≤1)
    (E : MeanTree X d) (hw : weight E≤A) (hweights : centersBound A E)
    (hb : circuitD F x+(lam:ℝ)*‖base E z-x‖≤B)
    (hc : centers (fun r b => 0 ≤ r ∧ (lam:ℝ)*r^2≤1/2 ∧ (lam:ℝ)*r≤1 ∧
      circuitD F x+(lam:ℝ)*‖b z-x‖≤B) E) :
    circuitD F (E.eval F z)≤((depth E:ℝ)+1)*B := by
  induction E with | node k b hm a r C ih =>
    have hchild (i : Fin k) := ih i (hweights i).1 (hweights i).2 (hc i).1.2.2.2 (hc i).2
    have hd (i : Fin k) : (depth (C i):ℝ)+1≤(depth (node k b hm a r C):ℝ) := by
      exact_mod_cast (Finset.le_sup (f:=fun j => depth (C j)+1) (Finset.mem_univ i))
    have hmean (i : Fin k) : ‖primitiveExpectedField F ((C i).eval F z) (r i)‖≤
        (2*Real.pi+2)*(depth (node k b hm a r C):ℝ)*B := by
      apply (primitiveExpectedField_growth hF _ (hc i).1.1 (hc i).1.2.1 (hc i).1.2.2.1).trans
      exact (mul_le_mul_of_nonneg_left
        ((hchild i).trans (mul_le_mul_of_nonneg_right (hd i) hB)) (by positivity)).trans_eq (by ring)
    have hs : ‖∑i,a i • primitiveExpectedField F ((C i).eval F z) (r i)‖≤
        (∑i,|a i|)*((2*Real.pi+2)*(depth (node k b hm a r C):ℝ)*B) := by
      apply (norm_sum_le _ _).trans
      rw [Finset.sum_mul]
      exact Finset.sum_le_sum (fun i _ => by
        rw [norm_smul,Real.norm_eq_abs]
        exact mul_le_mul_of_nonneg_left (hmean i) (abs_nonneg _))
    have hn : ‖(node k b hm a r C).eval F z-x‖≤‖b z-x‖+
        (∑i,|a i|)*((2*Real.pi+2)*(depth (node k b hm a r C):ℝ)*B) := by
      change ‖b z+(∑i,a i • primitiveExpectedField F ((C i).eval F z) (r i))-x‖≤_
      rw [add_sub_right_comm]
      exact (norm_add_le _ _).trans (add_le_add le_rfl hs)
    have hD := (circuitD_change hF x ((node k b hm a r C).eval F z)).trans
      (add_le_add le_rfl (mul_le_mul_of_nonneg_left hn lam.coe_nonneg))
    change (∑i,|a i|)≤A at hw
    have hmcoef := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hw lam.coe_nonneg)
      (show 0≤2*Real.pi+2 by positivity)
    have hcoef : (lam:ℝ)*(∑i,|a i|)*(2*Real.pi+2)≤1 := hmcoef.trans hsmall
    have hh := mul_le_mul_of_nonneg_right hcoef
      (show 0≤(depth (node k b hm a r C):ℝ)*B by positivity)
    change circuitD F x+(lam:ℝ)*‖b z-x‖≤B at hb
    nlinarith
end MeanTree
end LogConcaveSampling

end

end

end OAI
end

section
-- module Solutions.OAIQ048_LC.LogConcave_Numerics_Forward
attribute [-instance] _root_.OAI.LogConcaveSampling.LowerBound.couplingLaw_probability _root_.OAI.LogConcaveSampling.LowerBound.remainingHaar_probability _root_.OAI.LogConcaveSampling.LowerBound.roundRandomLaw_probability _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_invInvariant _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_isHaar _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_probability _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_rightInvariant _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_compactSpace _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_measurableInv _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_measurableMul _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_secondCountable _root_.OAI.LogConcaveSampling.MeanTree.instIsProbabilityMeasureRowTapeRowLaw _root_.OAI.LogConcaveSampling.OracleCompiler.topSeedLaw_probability _root_.OAI.LogConcaveSampling.noiseKernel_markov
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
namespace LogConcaveSampling
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators NNReal

namespace MeanTree
variable {X : Type*} [MeasurableSpace X] {d : ℕ}

lemma eval_forward {F : Point d → ℝ} {lam : ℝ≥0} (hF : Primitive F lam)
    {r T h : ℝ} {n N : ℕ} (hn : 0<n) (hT0 : 0<T) (hT1 : T<1) (hh : 0<h)
    (x y : MeanTree X d) (z : X) (i : ProbabilityNode T h n) :
    eval F (forward r T h n N x y i) z=
      probabilityPicard F (eval F x z) r T h n N (eval F y z) i := by
  unfold forward probabilityPicard
  have ha (j : ProbabilityNode T h n) : 0<1-(probabilityNodeTime T h n j)^2 := by
    have hj := probabilityNodeTime_mem hT0 hT1 hh hn j
    have ht := hj.2.trans_lt hT1
    nlinarith [hj.1]
  have he := eval_picard F (probabilityWeight T h n)
    (fun j E => scale (-r) (conditional r (probabilityNodeTime T h n j) x E))
    (fun _ => y) (fun z j => probabilityMeanVelocity F (eval F x z) r (probabilityNodeTime T h n j))
    (fun j E z => by simp only [eval_scale,eval_conditional hF r _ x E z (ha j),probabilityMeanVelocity]) N z i
  simpa only [FinitePicard.nodes_eq_iterate] using he

end MeanTree

end LogConcaveSampling

end

end

end OAI
end

section
-- module Solutions.OAIQ048_LC.LogConcave_Numerics_RowTape
attribute [-instance] _root_.OAI.LogConcaveSampling.LowerBound.couplingLaw_probability _root_.OAI.LogConcaveSampling.LowerBound.remainingHaar_probability _root_.OAI.LogConcaveSampling.LowerBound.roundRandomLaw_probability _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_invInvariant _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_isHaar _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_probability _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_rightInvariant _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_compactSpace _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_measurableInv _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_measurableMul _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_secondCountable _root_.OAI.LogConcaveSampling.OracleCompiler.topSeedLaw_probability _root_.OAI.LogConcaveSampling.noiseKernel_markov
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
namespace LogConcaveSampling.MeanTree
open MeasureTheory ProbabilityTheory OracleCompiler
open scoped Classical BigOperators

variable {X : Type*} [MeasurableSpace X] {d : ℕ}

lemma appendSlots_preserving {E : Type*} [MeasurableSpace E]
    (μ : Measure E) [SigmaFinite μ] (c k : ℕ) :
    MeasurePreserving (fun z : (Fin c → E) × (Fin k → E) => Fin.append z.1 z.2)
      ((Measure.pi fun _ : Fin c => μ).prod (Measure.pi fun _ : Fin k => μ))
      (Measure.pi fun _ : Fin (c+k) => μ) := by
  have hm : Measurable (fun z : (Fin c → E) × (Fin k → E) => Fin.append z.1 z.2) := by
    apply Measurable.of_eval
    intro i
    refine Fin.addCases (fun _ => ?_) (fun _ => ?_) i <;> simp only [Fin.append_left,Fin.append_right] <;> fun_prop
  refine ⟨hm,?_⟩
  rw [←(Expression.split_slots_preserving μ c k).map_eq,Measure.map_map hm
    (Expression.split_slots_preserving μ c k).measurable]
  have he : (fun z : (Fin c → E) × (Fin k → E) => Fin.append z.1 z.2) ∘
      (fun g : Fin (c+k) → E => ((fun i => g (Fin.castAdd k i)),fun i => g (Fin.natAdd c i)))=id := by
    funext g; exact Fin.append_castAdd_natAdd
  rw [he,Measure.map_id]

lemma finPi_head_preserving {k : ℕ} {E : Fin (k+1) → Type*} [∀i,MeasurableSpace (E i)]
    (μ : ∀i,Measure (E i)) [∀i,SigmaFinite (μ i)] :
    MeasurePreserving (fun z : ∀i,E i => (z 0,fun i : Fin k => z i.succ))
      (Measure.pi μ) ((μ 0).prod (Measure.pi fun i : Fin k => μ i.succ)) := by
  exact measurePreserving_piFinSuccAbove (m:=fun i => inferInstance) μ 0

lemma concatTerms_preserving (D : ℝ) (k : ℕ) (a : Fin k → ℝ)
    (C : Fin k → Expression X d) (M : Fin k → SeedProgram d) (E : Expression X d) :
    MeasurePreserving (concatTerms D k a C M E)
      ((rowLaw C M).prod (Measure.pi fun _ : Fin E.slots => stdGaussian (Point d)))
      (Measure.pi fun _ : Fin (compileTerms D k a C M E).slots => stdGaussian (Point d)) := by
  induction k with
  | zero =>
    change MeasurePreserving Prod.snd ((rowLaw C M).prod
      (Measure.pi fun _ : Fin E.slots => stdGaussian (Point d))) _
    exact measurePreserving_snd
  | succ k ih =>
    let γ := stdGaussian (Point d)
    let μc := Measure.pi fun _ : Fin (C 0).slots => γ
    let μm := Measure.pi fun _ : Fin (M 0).slots => γ
    let μr := rowLaw (fun i : Fin k => C i.succ) (fun i : Fin k => M i.succ)
    let μe := Measure.pi fun _ : Fin E.slots => γ
    have h₁ := (finPi_head_preserving (fun i =>
      (Measure.pi fun _ : Fin (C i).slots => γ).prod
      (Measure.pi fun _ : Fin (M i).slots => γ))).prod (MeasurePreserving.id μe)
    have h₂ := (measurePreserving_prodAssoc (μc.prod μm) μr μe).comp h₁
    have h₃ := ((MeasurePreserving.id (μc.prod μm)).prod
      (ih (fun i => a i.succ) (fun i => C i.succ) (fun i => M i.succ))).comp h₂
    have h₄ := (measurePreserving_prodAssoc μc μm
      (Measure.pi fun _ : Fin (compileTerms D k (fun i => a i.succ)
        (fun i => C i.succ) (fun i => M i.succ) E).slots => γ)).comp h₃
    have h₅ := ((MeasurePreserving.id μc).prod (appendSlots_preserving γ _ _)).comp h₄
    exact (appendSlots_preserving γ _ _).comp h₅

lemma leftBlock_append {c k t : ℕ} (x : Fin c → Point d) (y : Fin k → Point d) (z : Fin t → Point d) :
    Expression.leftBlock (Fin.append x (Fin.append y z))=x := by
  funext i; exact Fin.append_left _ _ i
lemma middleBlock_append {c k t : ℕ} (x : Fin c → Point d) (y : Fin k → Point d) (z : Fin t → Point d) :
    Expression.middleBlock (Fin.append x (Fin.append y z))=y := by
  funext i
  change Fin.append x (Fin.append y z) (Fin.natAdd c (Fin.castAdd t i))=y i
  rw [Fin.append_right,Fin.append_left]
lemma rightBlock_append {c k t : ℕ} (x : Fin c → Point d) (y : Fin k → Point d) (z : Fin t → Point d) :
    Expression.rightBlock (Fin.append x (Fin.append y z))=z := by
  funext i
  change Fin.append x (Fin.append y z) (Fin.natAdd c (Fin.natAdd k i))=z i
  rw [Fin.append_right,Fin.append_right]

lemma eval_concatTerms (V : Point d → ℝ) (D : ℝ) (k : ℕ) (a : Fin k → ℝ)
    (C : Fin k → Expression X d) (M : Fin k → SeedProgram d) (E : Expression X d)
    (x : X) (z : RowTape C M × (Fin E.slots → Point d)) :
    (compileTerms D k a C M E).eval V x (concatTerms D k a C M E z)=
      (∑i,a i • (M i).program.run V ((C i).eval V x (z.1 i).1,(M i).damping D (z.1 i).2))+
        E.eval V x z.2 := by
  induction k with
  | zero => simp [compileTerms,concatTerms]
  | succ k ih =>
    simp only [compileTerms,concatTerms,Expression.eval,leftBlock_append,middleBlock_append,
      rightBlock_append,ih,Fin.sum_univ_succ,add_assoc]
end LogConcaveSampling.MeanTree

end

end

end OAI
end

section
-- module Solutions.OAIQ048_LC.LogConcave_Numerics_RowGaussian
attribute [-instance] _root_.OAI.LogConcaveSampling.LowerBound.couplingLaw_probability _root_.OAI.LogConcaveSampling.LowerBound.remainingHaar_probability _root_.OAI.LogConcaveSampling.LowerBound.roundRandomLaw_probability _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_invInvariant _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_isHaar _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_probability _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_rightInvariant _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_compactSpace _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_measurableInv _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_measurableMul _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_secondCountable _root_.OAI.LogConcaveSampling.OracleCompiler.topSeedLaw_probability _root_.OAI.LogConcaveSampling.noiseKernel_markov
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
namespace LogConcaveSampling.MeanTree
open MeasureTheory ProbabilityTheory OracleCompiler
open scoped Classical BigOperators

variable {d k : ℕ}

lemma measurable_rowGaussian (a : Fin k → ℝ) (τ ρ n : ℝ) :
    Measurable (rowGaussian (d:=d) a τ ρ n) := by
  unfold rowGaussian; fun_prop

theorem rowGaussian_law (a : Fin k → ℝ) (τ ρ n : ℝ) (hn : n≠0)
    (hv : ρ^2+τ^2*(∑i,a i^2)=n^2) :
    ((Measure.pi fun _ : Fin k => stdGaussian (Point d)).prod
      (Measure.pi fun _ : Fin 1 => stdGaussian (Point d))).map (rowGaussian a τ ρ n)=
      stdGaussian (Point d) := by
  let w : Fin (k+1) → ℝ := Fin.append (fun i => a i*τ) (fun _ => ρ)
  have hw : (∑i,w i^2)=n^2 := by
    simp only [w,Fin.sum_univ_add,Fin.append_left,Fin.append_right,mul_pow,←Finset.sum_mul,
      Fin.sum_univ_one]
    nlinarith only [hv]
  have hsum := weighted_gaussian_law (E:=Point d) w n hw
  have he (z : (Fin k → Point d) × (Fin 1 → Point d)) :
      (∑i,w i • Fin.append z.1 z.2 i)=(∑i,a i • (τ • z.1 i))+ρ • z.2 0 := by
    simp only [w,Fin.sum_univ_add,Fin.append_left,Fin.append_right,mul_smul,Fin.sum_univ_one]
  have hh := congrArg (Measure.map (fun z : Point d => n⁻¹ • z)) hsum
  rw [Measure.map_map (by fun_prop) (by fun_prop),Measure.map_map (by fun_prop) (by fun_prop)] at hh
  have hright : (fun z : Point d => n⁻¹ • z) ∘ (fun z => n • z)=id := by
    funext z; simp [smul_smul,hn]
  rw [hright,Measure.map_id] at hh
  rw [←(appendSlots_preserving (stdGaussian (Point d)) k 1).map_eq,
    Measure.map_map (by fun_prop) (appendSlots_preserving (stdGaussian (Point d)) k 1).measurable] at hh
  simp only [Function.comp_def,he] at hh
  exact hh
end LogConcaveSampling.MeanTree

end

end

section

noncomputable section
namespace LogConcaveSampling.MeanTree
open MeasureTheory ProbabilityTheory OracleCompiler Coupling SeedCompiler
open scoped Classical BigOperators

variable {X : Type*} [MeasurableSpace X] {d k : ℕ}

theorem compileTerms_squared (V : Point d → ℝ) (hV : Measurable (firstOrderReply V))
    {D τ ρ n : ℝ} (hD : 0<D) (hn : n≠0) (a r K S B : Fin k → ℝ)
    (C : Fin k → Expression X d) (M : Fin k → SeedProgram d)
    (b : X → Point d) (hb : Measurable b) (x : X) (c m : Fin k → Point d)
    (hv : ρ^2+τ^2*(∑i,a i^2)=n^2)
    (hK : ∀i,0≤K i) (hvshift : ∀i,(∑j,(M i).shift j^2)≤D^2)
    (hshift : ∀i,ShiftInvariant (r i) (M i).shift (fun c g => (M i).program.run V (c,g)))
    (hLip : ∀i u v g,‖(M i).program.run V (u,g)-(M i).program.run V (v,g)‖≤K i*‖u-v‖)
    (hC : ∀i,SquaredAt (Measure.pi fun _ : Fin (C i).slots => stdGaussian (Point d))
      (stdGaussian (Point d)) ((C i).eval V x) (fun g => c i+(r i/(2*D)) • g) (S i))
    (hM : ∀i,SquaredAt (Measure.pi fun _ : Fin (M i).slots => stdGaussian (Point d))
      (stdGaussian (Point d)) (fun g => (M i).program.run V (c i,g)) (fun g => m i+τ • g) (B i)) :
    SquaredAt (Measure.pi fun _ : Fin (compileTerms D k a C M (.noise b hb ρ)).slots => stdGaussian (Point d))
      (stdGaussian (Point d)) ((compileTerms D k a C M (.noise b hb ρ)).eval V x)
      (fun g => (∑i,a i • m i)+b x+n • g)
      ((∑i,|a i|)*(∑i,|a i| * (2*(K i)^2*S i+2*B i))) := by
  let γ := stdGaussian (Point d)
  let A i := fun z : (Fin (C i).slots → Point d) × (Fin (M i).slots → Point d) =>
    (M i).program.run V ((C i).eval V x z.1,(M i).damping D z.2)
  have hcmeas (i) : Measurable ((C i).eval V x) :=
    ((C i).measurable_eval V hV).comp (measurable_const.prodMk measurable_id)
  have hameas (i) : Measurable (A i) :=
    ((M i).program.measurable_run V hV).comp
      (((hcmeas i).comp measurable_fst).prodMk ((M i).measurable_damping D |>.comp measurable_snd))
  have ha (i) : SquaredAt
      ((Measure.pi fun _ : Fin (C i).slots => γ).prod (Measure.pi fun _ : Fin (M i).slots => γ)) γ
      (A i) (fun g => m i+τ • g) (2*(K i)^2*S i+2*B i) :=
    SquaredAt.absorb_fixed _ _ (hcmeas i) (c i) (m i) hD (hK i) (M i).shift (hvshift i)
      (fun c g => (M i).program.run V (c,g)) ((M i).program.measurable_run V hV)
      (hshift i) (hLip i) (hC i) (hM i)
  have hrow := SquaredAt.weighted_pi _ _ A (fun i g => m i+τ • g) hameas
    (by intro; fun_prop) a (fun i => 2*(K i)^2*S i+2*B i) ha
  have hfrow : Measurable (fun z : RowTape C M => ∑i,a i • A i (z i)) := by fun_prop
  have hgrow : Measurable (fun z : Fin k → Point d => ∑i,a i • (m i+τ • z i)) := by fun_prop
  have hext := hrow.common_noise hfrow hgrow (Measure.pi fun _ : Fin 1 => γ)
    (fun z => b x+ρ • z 0) (by fun_prop)
  have hout : Measurable ((compileTerms D k a C M (.noise b hb ρ)).eval V x) :=
    ((compileTerms D k a C M (.noise b hb ρ)).measurable_eval V hV).comp
      (measurable_const.prodMk measurable_id)
  have hfin := hext.reindex (concatTerms D k a C M (.noise b hb ρ)) (rowGaussian a τ ρ n)
    (concatTerms_preserving D k a C M (.noise b hb ρ)).measurable
    (measurable_rowGaussian a τ ρ n) _ (fun g => (∑i,a i • m i)+b x+n • g) hout (by fun_prop)
    (by intro z; exact eval_concatTerms V D k a C M (.noise b hb ρ) x z)
    (by
      intro z
      dsimp only [rowGaussian]
      rw [smul_smul,mul_inv_cancel₀ hn,one_smul]
      simp only [smul_add,Finset.sum_add_distrib]
      abel)
  have hcmap : Measure.map (concatTerms D k a C M (.noise b hb ρ))
      ((Measure.pi fun i => (Measure.pi fun _ : Fin (C i).slots => γ).prod
        (Measure.pi fun _ : Fin (M i).slots => γ)).prod (Measure.pi fun _ : Fin 1 => γ))=
      (Measure.pi fun _ : Fin (compileTerms D k a C M (.noise b hb ρ)).slots => γ) :=
    (concatTerms_preserving D k a C M (.noise b hb ρ)).map_eq
  have hgmap : Measure.map (rowGaussian a τ ρ n)
      ((Measure.pi fun _ : Fin k => γ).prod (Measure.pi fun _ : Fin 1 => γ))=γ :=
    rowGaussian_law a τ ρ n hn hv
  rw [hcmap,hgmap] at hfin
  exact hfin
end LogConcaveSampling.MeanTree

end

end

section

noncomputable section
namespace LogConcaveSampling.MeanTree
open MeasureTheory ProbabilityTheory OracleCompiler Coupling SeedCompiler
open scoped Classical BigOperators

variable {X : Type*} [MeasurableSpace X] {d : ℕ}

theorem compileDeclared_squared (F V : Point d → ℝ)
    (hV : Measurable (firstOrderReply V)) {D A : ℝ} (hD : 0<D) (hA : 0<A)
    (P : ℝ → ℝ → Prop) (M : ℝ → ℝ → SeedProgram d)
    (K : ℝ → ℝ → ℝ) (B : ℝ → ℝ → Point d → ℝ)
    (hK : ∀r τ,P r τ → 0≤K r τ)
    (hvshift : ∀r τ,P r τ → (∑j,(M r τ).shift j^2)≤D^2)
    (hshift : ∀r τ,P r τ → ShiftInvariant r (M r τ).shift (fun c g => (M r τ).program.run V (c,g)))
    (hLip : ∀r τ,P r τ → ∀u v g,‖(M r τ).program.run V (u,g)-(M r τ).program.run V (v,g)‖≤K r τ*‖u-v‖)
    (hM : ∀r τ,P r τ → ∀c,SquaredAt
      (Measure.pi fun _ : Fin (M r τ).slots => stdGaussian (Point d)) (stdGaussian (Point d))
      (fun g => (M r τ).program.run V (c,g)) (fun g => primitiveExpectedField F c r+τ • g) (B r τ c))
    (E : MeanTree X d) (n : ℝ) (x : X) (hE : DeclaredValid D A P E n) :
    SquaredAt (Measure.pi fun _ : Fin (compileDeclared D A M E n).slots => stdGaussian (Point d))
      (stdGaussian (Point d)) ((compileDeclared D A M E n).eval V x)
      (fun g => E.eval F x+n • g) (declaredError F D A K B E n x) := by
  induction E generalizing n with
  | node k b hb a r C ih =>
    obtain ⟨hn,hw,hc⟩ := hE
    have hi (i) := ih i (r i/(2*D)) (hc i).2
    have hh := compileTerms_squared V hV hD hn.ne' a r
      (fun i => K (r i) (declaredNoise n A))
      (fun i => declaredError F D A K B (C i) (r i/(2*D)) x)
      (fun i => B (r i) (declaredNoise n A) ((C i).eval F x))
      (fun i => compileDeclared D A M (C i) (r i/(2*D)))
      (fun i => M (r i) (declaredNoise n A)) b hb x
      (fun i => (C i).eval F x) (fun i => primitiveExpectedField F ((C i).eval F x) (r i))
      (declaredReserve_variance hA n a hw)
      (fun i => hK _ _ (hc i).1) (fun i => hvshift _ _ (hc i).1)
      (fun i => hshift _ _ (hc i).1) (fun i => hLip _ _ (hc i).1) hi
      (fun i => hM _ _ (hc i).1 _)
    have he : (fun g => (node k b hb a r C).eval F x+n • g)=
        (fun g => (∑i,a i • primitiveExpectedField F ((C i).eval F x) (r i))+b x+n • g) := by
      funext g
      simp only [eval,add_comm (b x)]
    rw [he]
    exact hh
end LogConcaveSampling.MeanTree

end

end

section

noncomputable section
namespace LogConcaveSampling.MeanTree
open MeasureTheory ProbabilityTheory OracleCompiler Coupling SeedCompiler
open scoped Classical BigOperators

variable {X : Type*} [MeasurableSpace X] {d : ℕ}

theorem compileDeclaredRoot_squared (F V : Point d → ℝ)
    (hV : Measurable (firstOrderReply V)) {D A Af : ℝ} (hD : 0<D) (hA : 0<A) (hAf : 0<Af)
    (P : Bool → ℝ → ℝ → Prop) (M : Bool → ℝ → ℝ → SeedProgram d)
    (K : Bool → ℝ → ℝ → ℝ) (B : Bool → ℝ → ℝ → Point d → ℝ)
    (hK : ∀s r τ,P s r τ → 0≤K s r τ)
    (hvshift : ∀s r τ,P s r τ → (∑j,(M s r τ).shift j^2)≤D^2)
    (hshift : ∀s r τ,P s r τ → ShiftInvariant r (M s r τ).shift (fun c g => (M s r τ).program.run V (c,g)))
    (hLip : ∀s r τ,P s r τ → ∀u v g,‖(M s r τ).program.run V (u,g)-(M s r τ).program.run V (v,g)‖≤K s r τ*‖u-v‖)
    (hM : ∀s r τ,P s r τ → ∀c,SquaredAt
      (Measure.pi fun _ : Fin (M s r τ).slots => stdGaussian (Point d)) (stdGaussian (Point d))
      (fun g => (M s r τ).program.run V (c,g)) (fun g => primitiveExpectedField F c r+τ • g) (B s r τ c))
    (E : MeanTree X d) (n : ℝ) (x : X) (hE : DeclaredRootValid D A Af (P true) (P false) E n) :
    SquaredAt (Measure.pi fun _ : Fin (compileDeclaredRoot D A Af (M true) (M false) E n).slots => stdGaussian (Point d))
      (stdGaussian (Point d)) ((compileDeclaredRoot D A Af (M true) (M false) E n).eval V x)
      (fun g => E.eval F x+n • g) (declaredRootError F D A Af (K true) (K false) (B true) (B false) E n x) := by
  cases E with | node k b hb a r C =>
    obtain ⟨hn,hw,hc⟩ := hE
    have hi (i) := compileDeclared_squared F V hV hD hA (P false) (M false) (K false) (B false)
      (hK false) (hvshift false) (hshift false) (hLip false) (hM false) (C i) (r i/(2*D)) x (hc i).2
    have hh := compileTerms_squared V hV hD hn.ne' a r
      (fun i => K true (r i) (declaredNoise n Af))
      (fun i => declaredError F D A (K false) (B false) (C i) (r i/(2*D)) x)
      (fun i => B true (r i) (declaredNoise n Af) ((C i).eval F x))
      (fun i => compileDeclared D A (M false) (C i) (r i/(2*D)))
      (fun i => M true (r i) (declaredNoise n Af)) b hb x
      (fun i => (C i).eval F x) (fun i => primitiveExpectedField F ((C i).eval F x) (r i))
      (declaredReserve_variance hAf n a hw)
      (fun i => hK _ _ _ (hc i).1) (fun i => hvshift _ _ _ (hc i).1)
      (fun i => hshift _ _ _ (hc i).1) (fun i => hLip _ _ _ (hc i).1) hi
      (fun i => hM _ _ _ (hc i).1 _)
    have he : (fun g => (node k b hb a r C).eval F x+n • g)=
        (fun g => (∑i,a i • primitiveExpectedField F ((C i).eval F x) (r i))+b x+n • g) := by
      funext g
      simp only [eval,add_comm (b x)]
    rw [he]
    exact hh
end LogConcaveSampling.MeanTree

end

end

section

noncomputable section
namespace LogConcaveSampling.MeanTree
open Set MeasureTheory Quadrature
open scoped Classical BigOperators

variable {X : Type*} [MeasurableSpace X] {d : ℕ}

omit [MeasurableSpace X] in
lemma DirectCenter.radius {r T v r' : ℝ} {x Y G b : X → Point d}
    (hr : 0 ≤ r) (_hT0 : 0≤T) (_hT1 : T<1)
    (hb : DirectCenter r T v x Y G r' b) :
    r*Real.sqrt (1-T^2) ≤ r' ∧ r' ≤ r := by
  obtain ⟨ρ,hρ,θ,hθ,rfl,hb⟩ := hb
  have hρsq : ρ^2≤T^2 := pow_le_pow_left₀ hρ.1 hρ.2 2
  have hlo := Real.sqrt_le_sqrt (show 1-T^2≤1-ρ^2 by linarith)
  have hhi : Real.sqrt (1-ρ^2)≤1 := by
    apply (Real.sqrt_le_iff).mpr
    exact ⟨by norm_num,by nlinarith [sq_nonneg ρ]⟩
  exact ⟨mul_le_mul_of_nonneg_left hlo hr,(mul_le_mul_of_nonneg_left hhi hr).trans_eq (mul_one r)⟩

omit [MeasurableSpace X] in
lemma DirectCenter.radius_pos {r T v r' : ℝ} {x Y G b : X → Point d}
    (hr : 0 < r) (hT0 : 0≤T) (hT1 : T<1)
    (hb : DirectCenter r T v x Y G r' b) : 0 < r' := by
  have ht : 0<1-T^2 := by nlinarith
  exact lt_of_lt_of_le (mul_pos hr (Real.sqrt_pos.mpr ht)) (hb.radius hr.le hT0 hT1).1

omit [MeasurableSpace X] in
lemma oriented_norm (Y G : X → Point d) (θ : ℝ) (z : X) :
    ‖oriented Y G θ z‖≤‖Y z‖+|θ| *‖G z‖ := by
  apply (norm_add_le _ _).trans
  simp only [norm_smul,Real.norm_eq_abs]
  have hc := mul_le_mul_of_nonneg_right (Real.abs_cos_le_one θ) (norm_nonneg (Y z))
  have hs := mul_le_mul_of_nonneg_right (Real.abs_sin_le_abs (x:=θ)) (norm_nonneg (G z))
  linarith

omit [MeasurableSpace X] in
lemma DirectCenter.norm_displacement {r T v r' : ℝ} {x Y G b : X → Point d}
    (hr : 0 ≤ r) (_hT0 : 0≤T) (hT1 : T≤1)
    (hb : DirectCenter r T v x Y G r' b) (z : X) :
    ‖b z-x z‖ ≤ r*(‖Y z‖+v*‖G z‖) := by
  obtain ⟨ρ,hρ,θ,hθ,hr',rfl⟩ := hb
  simp only [add_sub_cancel_left,norm_smul,Real.norm_eq_abs,abs_mul,
    abs_of_nonneg hr,abs_of_nonneg hρ.1]
  have hY : ‖oriented Y G θ z‖≤‖Y z‖+v*‖G z‖ :=
    by
      have h := oriented_norm Y G θ z
      have hmul := mul_le_mul_of_nonneg_right hθ (norm_nonneg (G z))
      linarith
  have hρ1 := hρ.2.trans hT1
  exact (mul_le_mul_of_nonneg_left hY (mul_nonneg hr hρ.1)).trans
    (by nlinarith [mul_nonneg hr (show 0≤‖Y z‖+v*‖G z‖ by
      have hv := (abs_nonneg θ).trans hθ
      positivity)])

lemma declaredValid_of_radius_bounds {D A lo hi n : ℝ} (hD : 0<D) (hlo : 0<lo)
    (P : ℝ → ℝ → Prop) (E : MeanTree X d) (hw : weight E≤A) (hC : centersBound A E)
    (hscale : centers (fun r _ => lo ≤ r ∧ r≤hi) E)
    (hn : lo/(2*D)≤n ∧ n≤hi/(2*D))
    (hP : ∀r q,lo ≤ r → r≤hi → lo/(2*D)≤q → q≤hi/(2*D) → P r (declaredNoise q A)) :
    DeclaredValid D A P E n := by
  induction E generalizing n with | node k b hb a r C ih =>
    refine ⟨lt_of_lt_of_le (div_pos hlo (by positivity)) hn.1,hw,?_⟩
    intro i
    refine ⟨hP _ _ (hscale i).1.1 (hscale i).1.2 hn.1 hn.2,?_⟩
    exact ih i (hC i).1 (hC i).2 (hscale i).2
      ⟨div_le_div_of_nonneg_right (hscale i).1.1 (by positivity),
       div_le_div_of_nonneg_right (hscale i).1.2 (by positivity)⟩

end LogConcaveSampling.MeanTree

end

end

section

noncomputable section
namespace LogConcaveSampling.MeanTree
open Set MeasureTheory
open scoped Classical BigOperators NNReal

variable {X : Type*} [MeasurableSpace X] {d : ℕ}

lemma child_depth_le (k : ℕ) (b : X → Point d) (hb : Measurable b)
    (a r : Fin k → ℝ) (C : Fin k → MeanTree X d) (i : Fin k) :
    depth (C i)+1≤depth (.node k b hb a r C) :=
  Finset.le_sup (f:=fun j => depth (C j)+1) (Finset.mem_univ i)

lemma centerValues_of_bounds {F : Point d → ℝ} {lam : ℝ≥0} (hF : Primitive F lam)
    (x : Point d) (z : X) {A B : ℝ} (hB : 0≤B)
    (hsmall : (lam:ℝ)*A*(2*Real.pi+2)≤1) (M : ℕ)
    (E : MeanTree X d) (hweights : centersBound A E) (hd : depth E≤M)
    (hc : centers (fun r b => 0 ≤ r ∧ (lam:ℝ)*r^2≤1/2 ∧ (lam:ℝ)*r≤1 ∧
      circuitD F x+(lam:ℝ)*‖b z-x‖≤B) E) :
    centerValues F ((M:ℝ)*B) E z := by
  induction E with | node k b hm a r C ih =>
    intro i
    have hdi := (child_depth_le k b hm a r C i).trans hd
    have hdi' : ((depth (C i):ℝ)+1)≤(M:ℝ) := by exact_mod_cast hdi
    refine ⟨?_,ih i (hweights i).2 (by omega) (hc i).2⟩
    apply (eval_circuitD_bound hF x z hB hsmall (C i) (hweights i).1
      (hweights i).2 (hc i).1.2.2.2 (hc i).2).trans
    exact mul_le_mul_of_nonneg_right hdi' hB

omit [MeasurableSpace X] in
lemma directCenter_scalar_bounds {r T v r' : ℝ} {x Y G b : X → Point d}
    {lam : ℝ≥0} (hr : 0 ≤ r) (hT : 0≤T) (hT1 : T<1)
    (hl : (lam:ℝ)*r^2≤1/2) (hL : (lam:ℝ)*r≤1)
    (hb : DirectCenter r T v x Y G r' b) :
    0 ≤ r' ∧ (lam:ℝ)*r'^2≤1/2 ∧ (lam:ℝ)*r'≤1 := by
  have hrad := hb.radius hr hT hT1
  have hr' : 0 ≤ r' := (mul_nonneg hr (Real.sqrt_nonneg _)).trans hrad.1
  exact ⟨hr',(mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hr' hrad.2 2) lam.coe_nonneg).trans hl,
    (mul_le_mul_of_nonneg_left hrad.2 lam.coe_nonneg).trans hL⟩

theorem centerValues_of_direct {F : Point d → ℝ} {lam : ℝ≥0} (hF : Primitive F lam)
    {r T v A : ℝ} (hr : 0 ≤ r) (hT : 0≤T) (hT1 : T<1) (hv : 0≤v)
    (hl : (lam:ℝ)*r^2≤1/2) (hL : (lam:ℝ)*r≤1)
    (hsmall : (lam:ℝ)*A*(2*Real.pi+2)≤1)
    (x Y G : X → Point d) (z : X) (M : ℕ) (E : MeanTree X d)
    (hweights : centersBound A E) (hd : depth E≤M)
    (hc : centers (DirectCenter r T v x Y G) E) :
    centerValues F ((M:ℝ)*(circuitD F (x z)+(lam:ℝ)*r*(‖Y z‖+v*‖G z‖))) E z := by
  apply centerValues_of_bounds hF (x z) z (by positivity [circuitD_nonneg F (x z)])
    hsmall M E hweights hd
  apply centers_mono E (fun r' b hb => ?_) hc
  have hs := directCenter_scalar_bounds hr hT hT1 hl hL hb
  refine ⟨hs.1,hs.2.1,hs.2.2,?_⟩
  have hdisp := mul_le_mul_of_nonneg_left (hb.norm_displacement hr hT hT1.le z) lam.coe_nonneg
  linarith
end LogConcaveSampling.MeanTree

end

end

section

noncomputable section
namespace LogConcaveSampling.MeanTree
open MeasureTheory
open scoped Classical BigOperators

variable {X : Type*} [MeasurableSpace X] {d : ℕ}

theorem declaredError_uniform (F : Point d → ℝ) (D : ℝ) {A L R : ℝ}
    (_hA : 0≤A) (hR : 0≤R) (hc : 4*A^2*L^2≤1)
    (K : ℝ → ℝ → ℝ) (B : ℝ → ℝ → Point d → ℝ)
    (E : MeanTree X d) (n : ℝ) (x : X) (hw : weight E≤A) (hweights : centersBound A E)
    (hE : ErrorLimits F D A K B L R E n x) :
    declaredError F D A K B E n x≤4*A^2*R := by
  induction E generalizing n with | node k b hb a r C ih =>
    have hchild (i : Fin k) := ih i (r i/(2*D)) (hweights i).1 (hweights i).2 (hE i).2.2
    have hterm (i : Fin k) :
        2*(K (r i) (declaredNoise n A))^2*declaredError F D A K B (C i) (r i/(2*D)) x+
          2*B (r i) (declaredNoise n A) ((C i).eval F x)≤2*L^2*(4*A^2*R)+2*R := by
      have h₁ := mul_le_mul_of_nonneg_left (hchild i) (show 0≤2*(K (r i) (declaredNoise n A))^2 by positivity)
      have h₂ := mul_le_mul_of_nonneg_right (hE i).1 (show 0≤2*(4*A^2*R) by positivity)
      linarith [(hE i).2.1]
    have hs0 : 0≤∑i,|a i| := Finset.sum_nonneg fun i _ => abs_nonneg _
    have hsum := Finset.sum_le_sum (s:=Finset.univ) (fun (i : Fin k) _ => mul_le_mul_of_nonneg_left (hterm i) (abs_nonneg (a i)))
    rw [←Finset.sum_mul] at hsum
    have htot := mul_le_mul_of_nonneg_left hsum hs0
    change (∑i,|a i|)≤A at hw
    have hs := pow_le_pow_left₀ hs0 hw 2
    have hsq := mul_le_mul_of_nonneg_right hs (show 0≤2*L^2*(4*A^2*R)+2*R by positivity)
    have hcon := mul_le_mul_of_nonneg_right hc (show 0≤2*A^2*R by positivity)
    change (∑i,|a i|)*(∑i,|a i| *_)≤_
    nlinarith

theorem declaredRootError_bound (F : Point d → ℝ) (D A : ℝ) {Af L H e Q : ℝ}
    (hAf : 0<Af) (hH : 0≤H)
    (Kf Ki : ℝ → ℝ → ℝ) (Bf Bi : ℝ → ℝ → Point d → ℝ)
    (k : ℕ) (b : X → Point d) (hb : Measurable b) (a r : Fin k → ℝ)
    (C : Fin k → MeanTree X d) (n : ℝ) (x : X) (hw : (∑i,|a i|)≤Af)
    (hK : ∀i,(Kf (r i) (declaredNoise n Af))^2≤L^2)
    (hB : ∀i,Bf (r i) (declaredNoise n Af) ((C i).eval F x)≤(declaredNoise n Af)^2*e^2*Q^2)
    (hchild : ∀i,declaredError F D A Ki Bi (C i) (r i/(2*D)) x≤H) :
    declaredRootError F D A Af Kf Ki Bf Bi (.node k b hb a r C) n x≤
      2*Af^2*L^2*H+n^2*e^2*Q^2/2 := by
  have hterm (i : Fin k) :
      2*(Kf (r i) (declaredNoise n Af))^2*declaredError F D A Ki Bi (C i) (r i/(2*D)) x+
        2*Bf (r i) (declaredNoise n Af) ((C i).eval F x)≤
      2*L^2*H+2*(declaredNoise n Af)^2*e^2*Q^2 := by
    have h₁ := mul_le_mul_of_nonneg_left (hchild i) (show 0≤2*(Kf (r i) (declaredNoise n Af))^2 by positivity)
    have h₂ := mul_le_mul_of_nonneg_right (hK i) (show 0≤2*H by positivity)
    linarith [hB i]
  have hs0 : 0≤∑i,|a i| := Finset.sum_nonneg fun i _ => abs_nonneg _
  have hsum := Finset.sum_le_sum (s:=Finset.univ) (fun (i : Fin k) _ => mul_le_mul_of_nonneg_left (hterm i) (abs_nonneg (a i)))
  rw [←Finset.sum_mul] at hsum
  have htot := mul_le_mul_of_nonneg_left hsum hs0
  have hs := pow_le_pow_left₀ hs0 hw 2
  have hsq := mul_le_mul_of_nonneg_right hs
    (show 0≤2*L^2*H+2*(declaredNoise n Af)^2*e^2*Q^2 by positivity)
  have hid : Af^2*(declaredNoise n Af)^2=n^2/4 := by
    unfold declaredNoise
    field_simp [ne_of_gt hAf]
    ring
  change (∑i,|a i|)*(∑i,|a i| *_)≤_
  nlinarith [mul_nonneg (sq_nonneg e) (sq_nonneg Q)]
end LogConcaveSampling.MeanTree

end

end

section

noncomputable section
namespace LogConcaveSampling.MeanTree
open MeasureTheory
open scoped Classical BigOperators

variable {X : Type*} [MeasurableSpace X] {d : ℕ}

lemma normalizedErrorLimits (F : Point d → ℝ) {D A hi n L e Q : ℝ}
    (hD : 0<D) (hA : 0<A) (hn : 0≤n) (hhi : n≤hi/(2*D))
    (K : ℝ → ℝ → ℝ) (hK : ∀r τ,0 ≤ r → r≤hi → 0≤τ →
      τ≤declaredNoise (hi/(2*D)) A → (K r τ)^2≤L^2)
    (E : MeanTree X d) (x : X)
    (hs : centers (fun r _ => 0 ≤ r ∧ r≤hi) E) (hc : centerValues F Q E x) :
    ErrorLimits F D A K (fun _ τ c => τ^2*e^2*(circuitD F c)^2)
      L ((declaredNoise (hi/(2*D)) A)^2*e^2*Q^2) E n x := by
  induction E generalizing n with | node k b hb a r C ih =>
    have ht0 : 0≤declaredNoise n A := by unfold declaredNoise; positivity
    have ht : declaredNoise n A≤declaredNoise (hi/(2*D)) A :=
      div_le_div_of_nonneg_right hhi (by positivity)
    intro i
    refine ⟨hK _ _ (hs i).1.1 (hs i).1.2 ht0 ht,?_,?_⟩
    · have hnoise := pow_le_pow_left₀ ht0 ht 2
      have hvalue := pow_le_pow_left₀ (circuitD_nonneg F _) (hc i).1 2
      exact mul_le_mul (mul_le_mul_of_nonneg_right hnoise (sq_nonneg e)) hvalue
        (sq_nonneg _) (by positivity)
    · exact ih i (div_nonneg (hs i).1.1 (by positivity))
        (div_le_div_of_nonneg_right (hs i).1.2 (by positivity)) (hs i).2 (hc i).2

theorem declaredError_normalized (F : Point d → ℝ) {D A hi n L e Q : ℝ}
    (hD : 0<D) (hA : 0<A) (hn : 0≤n) (hhi : n≤hi/(2*D))
    (hcon : 4*A^2*L^2≤1)
    (K : ℝ → ℝ → ℝ) (hK : ∀r τ,0 ≤ r → r≤hi → 0≤τ →
      τ≤declaredNoise (hi/(2*D)) A → (K r τ)^2≤L^2)
    (E : MeanTree X d) (x : X) (hw : weight E≤A) (hc : centersBound A E)
    (hs : centers (fun r _ => 0 ≤ r ∧ r≤hi) E) (hv : centerValues F Q E x) :
    declaredError F D A K (fun _ τ c => τ^2*e^2*(circuitD F c)^2) E n x≤
      (hi/(2*D))^2*e^2*Q^2 := by
  have he := declaredError_uniform F D hA.le (by positivity) hcon K
    (fun _ τ c => τ^2*e^2*(circuitD F c)^2) E n x hw hc
    (normalizedErrorLimits F hD hA hn hhi K hK E x hs hv)
  have hid : 4*A^2*((declaredNoise (hi/(2*D)) A)^2*e^2*Q^2)=
      (hi/(2*D))^2*e^2*Q^2 := by
    unfold declaredNoise
    field_simp [hA.ne',hD.ne']
    ring
  rwa [hid] at he

theorem declaredRootError_normalized (F : Point d → ℝ) {D A Af hi n Li Lf ei ef Q : ℝ}
    (hD : 0<D) (hA : 0<A) (hAf : 0<Af) (hcon : 4*A^2*Li^2≤1)
    (Ki Kf : ℝ → ℝ → ℝ)
    (hKi : ∀r τ,0 ≤ r → r≤hi → 0≤τ → τ≤declaredNoise (hi/(2*D)) A → (Ki r τ)^2≤Li^2)
    (k : ℕ) (b : X → Point d) (hb : Measurable b) (a r : Fin k → ℝ)
    (C : Fin k → MeanTree X d) (x : X) (hw : (∑i,|a i|)≤Af)
    (hc : centersBound A (.node k b hb a r C))
    (hs : centers (fun r _ => 0 ≤ r ∧ r≤hi) (.node k b hb a r C))
    (hv : centerValues F Q (.node k b hb a r C) x)
    (hKf : ∀i,(Kf (r i) (declaredNoise n Af))^2≤Lf^2) :
    declaredRootError F D A Af Kf Ki
      (fun _ τ c => τ^2*ef^2*(circuitD F c)^2)
      (fun _ τ c => τ^2*ei^2*(circuitD F c)^2) (.node k b hb a r C) n x≤
      (2*Af^2*Lf^2*(hi/(2*D))^2*ei^2+n^2*ef^2/2)*Q^2 := by
  have hierr (i : Fin k) := declaredError_normalized F (e := ei) hD hA
    (div_nonneg (hs i).1.1 (by positivity))
    (div_le_div_of_nonneg_right (hs i).1.2 (by positivity)) hcon Ki hKi (C i) x
    (hc i).1 (hc i).2 (hs i).2 (hv i).2
  have he := declaredRootError_bound F D A hAf (by positivity) Kf Ki
    (fun _ τ c => τ^2*ef^2*(circuitD F c)^2)
    (fun _ τ c => τ^2*ei^2*(circuitD F c)^2) k b hb a r C n x hw hKf
    (fun i => mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (circuitD_nonneg F _) (hv i).1 2) (by positivity)) hierr
  convert he using 1
  all_goals try with_reducible_and_instances rfl
  ring
end LogConcaveSampling.MeanTree

end

end

end OAI
end

section
-- module Solutions.OAIQ048_LC.LogConcave_Numerics_BaseVariation
attribute [-instance] _root_.OAI.LogConcaveSampling.LowerBound.couplingLaw_probability _root_.OAI.LogConcaveSampling.LowerBound.remainingHaar_probability _root_.OAI.LogConcaveSampling.LowerBound.roundRandomLaw_probability _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_invInvariant _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_isHaar _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_probability _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_rightInvariant _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_compactSpace _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_measurableInv _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_measurableMul _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_secondCountable _root_.OAI.LogConcaveSampling.OracleCompiler.topSeedLaw_probability _root_.OAI.LogConcaveSampling.noiseKernel_markov
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
namespace LogConcaveSampling.MeanTree
open MeasureTheory OracleCompiler OracleCompiler.Expression
open scoped Classical BigOperators

variable {X : Type*} [MeasurableSpace X] {d : ℕ}

lemma compileTerms_variation (D : ℝ) (V : Point d → ℝ) (k : ℕ) (a : Fin k → ℝ)
    (C : Fin k → Expression X d) (M : Fin k → SeedProgram d) (E : Expression X d)
    (B : Fin k → ℝ) (L H : ℝ) (hL : 0≤L) (x y : X)
    (hc : ∀i g,‖(C i).eval V x g-(C i).eval V y g‖ ≤ B i)
    (hm : ∀i u v g,‖(M i).program.run V (u,g)-(M i).program.run V (v,g)‖ ≤ L*‖u-v‖)
    (he : ∀g,‖E.eval V x g-E.eval V y g‖ ≤ H) :
    ∀g,‖(compileTerms D k a C M E).eval V x g-(compileTerms D k a C M E).eval V y g‖ ≤
      (∑i,|a i| *(L*B i))+H := by
  induction k with
  | zero => simpa [compileTerms] using he
  | succ k ih =>
    intro g
    have ht := ih (fun i => a i.succ) (fun i => C i.succ) (fun i => M i.succ)
      (fun i => B i.succ) (fun i => hc i.succ) (fun i => hm i.succ) (rightBlock g)
    have hhead := (hm 0 _ _ ((M 0).damping D (middleBlock g))).trans
      (mul_le_mul_of_nonneg_left (hc 0 (leftBlock g)) hL)
    change ‖a 0 • _+_-(a 0 • _+_)‖ ≤ _
    rw [show ∀u v w z : Point d,u+v-(w+z)=(u-w)+(v-z) by intros; abel]
    apply (norm_add_le _ _).trans
    rw [←smul_sub,norm_smul,Real.norm_eq_abs,Fin.sum_univ_succ]
    have hh := mul_le_mul_of_nonneg_left hhead (abs_nonneg (a 0))
    linarith

theorem compileDeclared_variation {D A L B : ℝ} (hL : 0≤L) (hB : 0≤B)
    (hLA : L*A ≤ 1) (V : Point d → ℝ) (P : ℝ → ℝ → Prop) (M : ℝ → ℝ → SeedProgram d)
    (hm : ∀r τ,P r τ → ∀u v g,‖(M r τ).program.run V (u,g)-(M r τ).program.run V (v,g)‖ ≤ L*‖u-v‖)
    (E : MeanTree X d) (n : ℝ) (x y : X) (hE : BaseVariation B x y E)
    (hw : weight E ≤ A) (hcenters : centersBound A E) (hr : ShiftReady D A P E n) :
    ∀g,‖(compileDeclared D A M E n).eval V x g-(compileDeclared D A M E n).eval V y g‖ ≤
      ((depth E:ℝ)+1)*B := by
  induction E generalizing n with | node k b hb a r C ih =>
    have hc (i : Fin k) (g) := ih i (r i/(2*D)) (hE.2 i) (hcenters i).1 (hcenters i).2 (hr i).2.2 g
    have hd (i : Fin k) : (depth (C i):ℝ)+1 ≤ (depth (node k b hb a r C):ℝ) := by
      exact_mod_cast (Finset.le_sup (f:=fun j => depth (C j)+1) (Finset.mem_univ i))
    have hct (i : Fin k) (g) : ‖(compileDeclared D A M (C i) (r i/(2*D))).eval V x g-
        (compileDeclared D A M (C i) (r i/(2*D))).eval V y g‖ ≤ (depth (node k b hb a r C):ℝ)*B :=
      (hc i g).trans (mul_le_mul_of_nonneg_right (hd i) hB)
    have hh := compileTerms_variation D V k a (fun i => compileDeclared D A M (C i) (r i/(2*D)))
      (fun i => M (r i) (declaredNoise n A)) (.noise b hb (declaredReserve n A a))
      (fun _ => (depth (node k b hb a r C):ℝ)*B) L B hL x y hct
      (fun i => hm _ _ (hr i).2.1) (fun g => by simpa only [Expression.eval,add_sub_add_right_eq_sub] using hE.1)
    intro g
    apply (hh g).trans
    rw [←Finset.sum_mul]
    have hs : (∑i,|a i|)*L ≤ 1 := calc
      _ ≤ A*L := mul_le_mul_of_nonneg_right hw hL
      _ ≤ 1 := by simpa only [mul_comm] using hLA
    have hd0 : 0 ≤ (depth (node k b hb a r C):ℝ)*B := by positivity
    have hmult := mul_le_mul_of_nonneg_right hs hd0
    nlinarith

theorem compileDeclaredRoot_variation {D A Af L Li B Bf : ℝ} (hL : 0≤L) (hLi : 0≤Li)
    (hB : 0≤B) (hLA : Li*A ≤ 1) (V : Point d → ℝ)
    (P : Bool → ℝ → ℝ → Prop) (M : Bool → ℝ → ℝ → SeedProgram d)
    (hm : ∀r τ,P true r τ → ∀u v g,‖(M true r τ).program.run V (u,g)-(M true r τ).program.run V (v,g)‖ ≤ L*‖u-v‖)
    (hmi : ∀r τ,P false r τ → ∀u v g,‖(M false r τ).program.run V (u,g)-(M false r τ).program.run V (v,g)‖ ≤ Li*‖u-v‖)
    (E : MeanTree X d) (n : ℝ) (x y : X)
    (hE : BaseVariation B x y E) (hbase : ‖base E x-base E y‖ ≤ Bf)
    (hw : weight E ≤ Af) (hcenters : centersBound A E)
    (hr : RootShiftReady D A Af (P true) (P false) E n) :
    ∀g,‖(compileDeclaredRoot D A Af (M true) (M false) E n).eval V x g-
      (compileDeclaredRoot D A Af (M true) (M false) E n).eval V y g‖ ≤
      Af*L*(depth E:ℝ)*B+Bf := by
  cases E with | node k b hb a r C =>
    have hd (i : Fin k) : (depth (C i):ℝ)+1 ≤ (depth (node k b hb a r C):ℝ) := by
      exact_mod_cast (Finset.le_sup (f:=fun j => depth (C j)+1) (Finset.mem_univ i))
    have hc (i : Fin k) (g) := (compileDeclared_variation hLi hB hLA V (P false) (M false)
      hmi (C i) (r i/(2*D)) x y (hE.2 i) (hcenters i).1 (hcenters i).2 (hr i).2.2 g).trans
      (mul_le_mul_of_nonneg_right (hd i) hB)
    have hh := compileTerms_variation D V k a (fun i => compileDeclared D A (M false) (C i) (r i/(2*D)))
      (fun i => M true (r i) (declaredNoise n Af)) (.noise b hb (declaredReserve n Af a))
      (fun _ => (depth (node k b hb a r C):ℝ)*B) L Bf hL x y hc
      (fun i => hm _ _ (hr i).2.1) (fun g => by simpa only [Expression.eval,add_sub_add_right_eq_sub,base] using hbase)
    intro g
    apply (hh g).trans
    rw [←Finset.sum_mul]
    change (∑ i, |a i|) ≤ Af at hw
    have hm := mul_le_mul_of_nonneg_right hw (show 0 ≤ L*((depth (node k b hb a r C):ℝ)*B) by positivity)
    nlinarith
end LogConcaveSampling.MeanTree

end

end

end OAI
end

section
-- module Solutions.OAIQ048_LC.LogConcave_Numerics_BaseVariationCenters
attribute [-instance] _root_.OAI.LogConcaveSampling.LowerBound.couplingLaw_probability _root_.OAI.LogConcaveSampling.LowerBound.remainingHaar_probability _root_.OAI.LogConcaveSampling.LowerBound.roundRandomLaw_probability _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_invInvariant _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_isHaar _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_probability _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_rightInvariant _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_compactSpace _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_measurableInv _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_measurableMul _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_secondCountable _root_.OAI.LogConcaveSampling.OracleCompiler.topSeedLaw_probability _root_.OAI.LogConcaveSampling.noiseKernel_markov
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
namespace LogConcaveSampling.MeanTree
open MeasureTheory Quadrature
open scoped Classical

variable {X : Type*} [MeasurableSpace X] {d : ℕ}

lemma baseVariation_of_centers (E : MeanTree X d) (u v : X) (B : ℝ)
    (hb : ‖base E u-base E v‖≤B)
    (hc : centers (fun _ b => ‖b u-b v‖≤B) E) : BaseVariation B u v E := by
  induction E with | node k b hb' a r C ih =>
    exact ⟨hb,fun i => ih i (hc i).1 (hc i).2⟩

omit [MeasurableSpace X] in
lemma DirectCenter.variation {r T v r' : ℝ} {x Y G b : X → Point d}
    (hr : 0 ≤ r) (hT : T≤1) (hb : DirectCenter r T v x Y G r' b) (u z : X) :
    ‖b u-b z‖≤‖x u-x z‖+r*(‖Y u-Y z‖+‖G u-G z‖) := by
  obtain ⟨ρ,hρ,θ,hθ,hr',rfl⟩ := hb
  have hρ1 : ρ≤1 := hρ.2.trans hT
  have hrρ : 0 ≤ r*ρ := mul_nonneg hr hρ.1
  have ho : ‖oriented Y G θ u-oriented Y G θ z‖≤‖Y u-Y z‖+‖G u-G z‖ := by
    rw [show oriented Y G θ u-oriented Y G θ z=
      Real.cos θ • (Y u-Y z)+Real.sin θ • (G u-G z) by dsimp [oriented]; module]
    apply (norm_add_le _ _).trans
    simp only [norm_smul,Real.norm_eq_abs]
    nlinarith [Real.abs_cos_le_one θ,Real.abs_sin_le_one θ,norm_nonneg (Y u-Y z),norm_nonneg (G u-G z)]
  rw [show x u+(r*ρ) • oriented Y G θ u-(x z+(r*ρ) • oriented Y G θ z)=
    (x u-x z)+(r*ρ) • (oriented Y G θ u-oriented Y G θ z) by module]
  apply (norm_add_le _ _).trans
  rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg hrρ]
  have h₁ := mul_le_mul_of_nonneg_left ho hrρ
  have h₂ := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hρ1 hr)
    (show 0≤‖Y u-Y z‖+‖G u-G z‖ by positivity)
  nlinarith

end LogConcaveSampling.MeanTree

end

end

end OAI
end

section
-- module Solutions.OAIQ048_LC.LogConcave_Numerics_CenterValuesMono
attribute [-instance] _root_.OAI.LogConcaveSampling.LowerBound.couplingLaw_probability _root_.OAI.LogConcaveSampling.LowerBound.remainingHaar_probability _root_.OAI.LogConcaveSampling.LowerBound.roundRandomLaw_probability _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_invInvariant _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_isHaar _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_probability _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_rightInvariant _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_compactSpace _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_measurableInv _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_measurableMul _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_secondCountable _root_.OAI.LogConcaveSampling.OracleCompiler.topSeedLaw_probability _root_.OAI.LogConcaveSampling.noiseKernel_markov
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
namespace LogConcaveSampling.MeanTree
open MeasureTheory

variable {X : Type*} [MeasurableSpace X] {d : ℕ}
lemma centerValues_mono {F : Point d → ℝ} {Q Q' : ℝ} (h : Q≤Q') (E : MeanTree X d) (x : X) :
    centerValues F Q E x → centerValues F Q' E x := by
  induction E with | node k b hb a r C ih =>
    intro he i
    exact ⟨(he i).1.trans h,ih i (he i).2⟩
end LogConcaveSampling.MeanTree

end
end

end OAI
end

section
-- module Solutions.OAIQ048_LC.LogConcave_Numerics_CentersBoundPicard
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
namespace LogConcaveSampling.MeanTree
open MeasureTheory Quadrature FinitePicard
open scoped Classical BigOperators

variable {X : Type*} [MeasurableSpace X] {d : ℕ}

lemma centersBound_picard {I : Type*} [Fintype I] (w : I → I → ℝ)
    (φ : I → MeanTree X d → MeanTree X d) (a : I → MeanTree X d)
    {A B C W : ℝ} (_hB : 0≤B) (hC : 0≤C) (hw : ∀i,∑j,|w i j|≤B)
    (hφw : ∀i E,weight (φ i E)≤C)
    (haw : ∀i,weight (a i)≤W) (ha : ∀i,centersBound A (a i))
    (hφ : ∀i E,weight E≤W+B*C → centersBound A E → centersBound A (φ i E))
    (N : ℕ) (i : I) : centersBound A (picard w φ a N i) := by
  induction N generalizing i with
  | zero => exact ha i
  | succ N ih =>
    apply (centersBound_add _ _ _).2
    refine ⟨ha i,centersBound_sumFamily _ _ (fun j => ?_)⟩
    apply (centersBound_scale _ _ _).2
    apply hφ j _ ?_ (ih j)
    exact (weight_picard w φ a hC hw hφw N j).trans (add_le_add_left (haw j) _)

end LogConcaveSampling.MeanTree

end

end

end OAI
end

section
-- module Solutions.OAIQ048_LC.LogConcave_OraclePrograms_ReservedProgram
attribute [-instance] _root_.OAI.LogConcaveSampling.LowerBound.couplingLaw_probability _root_.OAI.LogConcaveSampling.LowerBound.remainingHaar_probability _root_.OAI.LogConcaveSampling.LowerBound.roundRandomLaw_probability _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_invInvariant _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_isHaar _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_probability _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_rightInvariant _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_compactSpace _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_measurableInv _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_measurableMul _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_secondCountable _root_.OAI.LogConcaveSampling.MeanTree.instIsProbabilityMeasureRowTapeRowLaw _root_.OAI.LogConcaveSampling.OracleCompiler.topSeedLaw_probability _root_.OAI.LogConcaveSampling.noiseKernel_markov
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
namespace LogConcaveSampling.OracleCompiler
open MeasureTheory Program Expression
open scoped Classical BigOperators

variable {d : ℕ}

lemma sampleParent_run (E : Expression (Point d × Point d) d) (v : Fin E.slots → ℝ)
    (T η : ℝ) (V : Point d → ℝ) (x : Point d) (g : Fin (1+E.slots) → Point d) :
    (sampleParent E v T η).pre.run V (x,g)=
      E.eval V (x,g (Fin.castAdd E.slots 0)) (fun i => g (Fin.natAdd 1 i)) := by
  change (E.compile.seedMap (fun z : Point d × (Fin (1+E.slots) → Point d) =>
    ((z.1,z.2 (Fin.castAdd E.slots 0)),fun i => z.2 (Fin.natAdd 1 i))) (by fun_prop)).run V (x,g)=_
  rw [Program.seedMap_run,Expression.compile_run]

end LogConcaveSampling.OracleCompiler

end

end

end OAI
end

section
-- module Solutions.OAIQ048_LC.LogConcave_Numerics_CompileDeclaredRootNormalized
attribute [-instance] _root_.OAI.LogConcaveSampling.LowerBound.couplingLaw_probability _root_.OAI.LogConcaveSampling.LowerBound.remainingHaar_probability _root_.OAI.LogConcaveSampling.LowerBound.roundRandomLaw_probability _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_invInvariant _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_isHaar _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_probability _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_rightInvariant _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_compactSpace _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_measurableInv _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_measurableMul _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_secondCountable _root_.OAI.LogConcaveSampling.OracleCompiler.topSeedLaw_probability _root_.OAI.LogConcaveSampling.noiseKernel_markov
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
namespace LogConcaveSampling.MeanTree
open MeasureTheory ProbabilityTheory OracleCompiler Coupling SeedCompiler
open scoped Classical BigOperators

variable {X : Type*} [MeasurableSpace X] {d : ℕ}

theorem compileDeclaredRoot_normalized (F V : Point d → ℝ)
    (hV : Measurable (firstOrderReply V)) {D A Af hi n Li Lf ei ef Q : ℝ}
    (hD : 0<D) (hA : 0<A) (hAf : 0<Af) (hLi : 0≤Li) (hLf : 0≤Lf)
    (hcon : 4*A^2*Li^2≤1)
    (P : Bool → ℝ → ℝ → Prop) (M : Bool → ℝ → ℝ → SeedProgram d)
    (hshift : ∀s r τ,P s r τ → ShiftInvariant r (M s r τ).shift
      (fun c g => (M s r τ).program.run V (c,g)))
    (henergy : ∀s r τ,P s r τ → (∑j,(M s r τ).shift j^2)≤D^2)
    (hLipi : ∀r τ,P false r τ → ∀u v g,
      ‖(M false r τ).program.run V (u,g)-(M false r τ).program.run V (v,g)‖≤Li*‖u-v‖)
    (hLipf : ∀r τ,P true r τ → ∀u v g,
      ‖(M true r τ).program.run V (u,g)-(M true r τ).program.run V (v,g)‖≤Lf*‖u-v‖)
    (hMi : ∀r τ,P false r τ → ∀c,SquaredAt (gaussianTape d (M false r τ).slots)
      (stdGaussian (Point d)) (fun g => (M false r τ).program.run V (c,g))
      (fun g => primitiveExpectedField F c r+τ • g) (τ^2*ei^2*(circuitD F c)^2))
    (hMf : ∀r τ,P true r τ → ∀c,SquaredAt (gaussianTape d (M true r τ).slots)
      (stdGaussian (Point d)) (fun g => (M true r τ).program.run V (c,g))
      (fun g => primitiveExpectedField F c r+τ • g) (τ^2*ef^2*(circuitD F c)^2))
    (E : MeanTree X d) (x : X) (hE : DeclaredRootValid D A Af (P true) (P false) E n)
    (hc : centersBound A E) (hs : centers (fun r _ => 0 ≤ r ∧ r≤hi) E)
    (hv : centerValues F Q E x) :
    SquaredAt (gaussianTape d (compileDeclaredRoot D A Af (M true) (M false) E n).slots)
      (stdGaussian (Point d)) ((compileDeclaredRoot D A Af (M true) (M false) E n).eval V x)
      (fun g => E.eval F x+n • g)
      ((2*Af^2*Lf^2*(hi/(2*D))^2*ei^2+n^2*ef^2/2)*Q^2) := by
  let K : Bool → ℝ → ℝ → ℝ := fun s _ _ => if s then Lf else Li
  let B : Bool → ℝ → ℝ → Point d → ℝ := fun s _ τ c =>
    τ^2*(if s then ef else ei)^2*(circuitD F c)^2
  have hK : ∀s r τ,P s r τ → 0≤K s r τ := by
    intro s r τ _; cases s <;> assumption
  have hLip : ∀s r τ,P s r τ → ∀u v g,
      ‖(M s r τ).program.run V (u,g)-(M s r τ).program.run V (v,g)‖≤K s r τ*‖u-v‖ := by
    intro s; cases s; exact hLipi; exact hLipf
  have hM : ∀s r τ,P s r τ → ∀c,SquaredAt (gaussianTape d (M s r τ).slots)
      (stdGaussian (Point d)) (fun g => (M s r τ).program.run V (c,g))
      (fun g => primitiveExpectedField F c r+τ • g) (B s r τ c) := by
    intro s; cases s; exact hMi; exact hMf
  have hh := compileDeclaredRoot_squared F V hV hD hA hAf P M K B
    hK henergy hshift hLip hM E n x hE
  apply hh.mono
  cases E with | node k b hb a r C =>
    exact declaredRootError_normalized F hD hA hAf hcon (K false) (K true)
      (fun _ _ _ _ _ _ => le_rfl) k b hb a r C x hE.2.1 hc hs hv (fun _ => le_rfl)
end LogConcaveSampling.MeanTree

end

end

section

noncomputable section
namespace LogConcaveSampling.MeanTree
open MeasureTheory Quadrature FinitePicard
open scoped Classical BigOperators

variable {X : Type*} [MeasurableSpace X] {d : ℕ}

lemma forward_weights {r T h P A : ℝ} (hr : 0 ≤ r) (hP : 0≤P) (n N : ℕ)
    (ht : ∀j : ProbabilityNode T h n,|probabilityNodeTime T h n j|≤1)
    (hw : ∀i,∑j,|probabilityWeight T h n i j|≤P)
    (x y : MeanTree X d) (hxw : weight x=0)
    (hx : centersBound A x) (hy : centersBound A y)
    (hA : r*(weight y+P*r)≤A) (i : ProbabilityNode T h n) :
    weight (forward r T h n N x y i)≤weight y+P*r ∧
      centersBound A (forward r T h n N x y i) := by
  have hc (j : ProbabilityNode T h n) (E : MeanTree X d) :
      weight (scale (-r) (conditional r (probabilityNodeTime T h n j) x E)) ≤ r := by
    simp [abs_of_nonneg hr]
  constructor
  · exact weight_picard _ _ _ hr hw hc N i
  · apply centersBound_picard _ _ _ hP hr hw hc (fun _ => le_rfl) (fun _ => hy) ?_ N i
    intro j E hE hEb
    apply (centersBound_scale _ _ _).2
    apply centersBound_conditional hx hEb
    rw [hxw,zero_add,abs_mul,abs_of_nonneg hr]
    calc
      r*|probabilityNodeTime T h n j| * weight E ≤ r*weight E := by
        nlinarith [weight_nonneg E,mul_le_mul_of_nonneg_left (ht j) hr]
      _ ≤ r*(weight y+P*r) := mul_le_mul_of_nonneg_left hE hr
      _≤A := hA

lemma literalSample_weights {r T h P A Af : ℝ} (hr : 0 < r) (hP : 0≤P)
    (hT : 1/2≤T) (n N : ℕ) (e : ProbabilityNode T h n)
    (ht : ∀j : ProbabilityNode T h n,|probabilityNodeTime T h n j|≤1)
    (hw : ∀i,∑j,|probabilityWeight T h n i j|≤P)
    (hPA : P≤A) (hPf : 2*P≤Af) :
    weight (literalSample (d:=d) r T h n N e)≤Af*r ∧
      centersBound (A*r^2) (literalSample (d:=d) r T h n N e) := by
  have hT0 : 0<T := by linarith
  have hTi : |T⁻¹|≤2 := by
    rw [abs_of_pos (inv_pos.mpr hT0)]
    exact (inv_le_comm₀ hT0 (by norm_num)).mpr (by simpa using hT)
  have hf := forward_weights (d:=d) (X:=SampleInput d) hr.le hP n N ht hw
    (anchor Prod.fst (by fun_prop)) (anchor Prod.snd (by fun_prop)) (by simp) (by simp) (by simp)
    (show r*(weight (anchor (Prod.snd : SampleInput d → Point d) (by fun_prop))+P*r)≤A*r^2 by
      simp only [weight_anchor,zero_add]
      nlinarith [mul_le_mul_of_nonneg_right hPA (sq_nonneg r)]) e
  constructor
  · dsimp only [literalSample]
    rw [weight_scale]
    have h0 := weight_nonneg (forward r T h n N (anchor (Prod.fst : SampleInput d → Point d) (by fun_prop)) (anchor Prod.snd (by fun_prop)) e)
    simp only [weight_anchor,zero_add] at hf
    nlinarith [mul_le_mul_of_nonneg_right hPf hr.le]
  · exact (centersBound_scale _ _ _).2 hf.2

end LogConcaveSampling.MeanTree

end

end

section

noncomputable section
namespace LogConcaveSampling.MeanTree
open MeasureTheory

variable {X : Type*} [MeasurableSpace X] {d : ℕ}

lemma DeclaredValid.shiftReady {D A : ℝ} (P : ℝ → ℝ → Prop)
    (hp : ∀r τ,P r τ → r≠0) (E : MeanTree X d) (n : ℝ)
    (he : DeclaredValid D A P E n) : ShiftReady D A P E n := by
  induction E generalizing n with | node k b hb a r C ih =>
    intro i
    exact ⟨hp _ _ (he.2.2 i).1,(he.2.2 i).1,ih i _ (he.2.2 i).2⟩

lemma DeclaredRootValid.shiftReady {D A Af : ℝ} (Pf Pi : ℝ → ℝ → Prop)
    (hpf : ∀r τ,Pf r τ → r≠0) (hpi : ∀r τ,Pi r τ → r≠0)
    (E : MeanTree X d) (n : ℝ) (he : DeclaredRootValid D A Af Pf Pi E n) :
    RootShiftReady D A Af Pf Pi E n := by
  cases E with | node k b hb a r C =>
    intro i
    exact ⟨hpf _ _ (he.2.2 i).1,(he.2.2 i).1,
      (he.2.2 i).2.shiftReady Pi hpi (C i) (r i/(2*D))⟩

lemma declaredRootValid_of_radius_bounds {D A Af lo hi n : ℝ} (hD : 0<D) (hlo : 0<lo)
    (Pf Pi : ℝ → ℝ → Prop) (E : MeanTree X d) (hn : 0<n)
    (hw : weight E≤Af) (hC : centersBound A E)
    (hscale : centers (fun r _ => lo ≤ r ∧ r≤hi) E)
    (hfinal : rootScales (fun r => Pf r (declaredNoise n Af)) E)
    (hPi : ∀r q,lo ≤ r → r≤hi → lo/(2*D)≤q → q≤hi/(2*D) → Pi r (declaredNoise q A)) :
    DeclaredRootValid D A Af Pf Pi E n := by
  cases E with | node k b hb a r C =>
    refine ⟨hn,hw,?_⟩
    intro i
    refine ⟨hfinal i,?_⟩
    exact declaredValid_of_radius_bounds hD hlo Pi (C i) (hC i).1 (hC i).2 (hscale i).2
      ⟨div_le_div_of_nonneg_right (hscale i).1.1 (by positivity),
       div_le_div_of_nonneg_right (hscale i).1.2 (by positivity)⟩ hPi
end LogConcaveSampling.MeanTree

end

end

end OAI
end

section
-- module Solutions.OAIQ048_LC.LogConcave_Sampling_PrimitiveExpectedFieldLipschitz
attribute [-instance] _root_.OAI.LogConcaveSampling.LowerBound.couplingLaw_probability _root_.OAI.LogConcaveSampling.LowerBound.remainingHaar_probability _root_.OAI.LogConcaveSampling.LowerBound.roundRandomLaw_probability _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_invInvariant _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_isHaar _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_probability _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_rightInvariant _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_compactSpace _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_measurableInv _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_measurableMul _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_secondCountable _root_.OAI.LogConcaveSampling.MeanTree.instIsProbabilityMeasureRowTapeRowLaw _root_.OAI.LogConcaveSampling.OracleCompiler.topSeedLaw_probability _root_.OAI.LogConcaveSampling.noiseKernel_markov
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
namespace LogConcaveSampling
open MeasureTheory
open scoped NNReal

theorem primitiveExpectedField_lipschitz {d : ℕ} {F : Point d → ℝ} {lam : ℝ≥0}
    (hF : Primitive F lam) {r : ℝ} (hr : 0 < r) (hl : (lam:ℝ)*r^2≤1/4) :
    LipschitzWith ⟨(Real.pi^2/2)*(lam:ℝ),by positivity⟩ (fun x => primitiveExpectedField F x r) := by
  let a := Real.sqrt 2
  have ha : 0<a := Real.sqrt_pos.mpr (by norm_num)
  have ha2 : a^2=2 := Real.sq_sqrt (by norm_num)
  have hhalf : 0≤1/a := by positivity
  have hhalf1 : 1/a<1 := by rw [div_lt_iff₀ ha]; nlinarith
  have hvar : 1-(1/a)^2=1/2 := by field_simp; nlinarith
  have hsqrt : Real.sqrt (1-(1/a)^2)=1/a := by
    have hs := Real.sq_sqrt (show 0≤1-(1/a)^2 by rw [hvar]; norm_num)
    nlinarith [Real.sqrt_nonneg (1-(1/a)^2)]
  have hscale : (a*r)*Real.sqrt (1-(1/a)^2)=r := by rw [hsqrt]; field_simp
  have hmean (x : Point d) :
      conditionalFieldMean F 0 (a*r) (1/a) ((1/r) • x)=primitiveExpectedField F x r := by
    rw [MeanTree.conditionalFieldMean_primitive hF _ _ _ _ (by rw [hvar]; norm_num),hscale]
    congr 1
    simp only [zero_add,smul_smul]
    have he : a*r*(1/a)*(1/r)=1 := by field_simp
    rw [he,one_smul]
  have hL := conditionalFieldMean_lipschitz hF (0:Point d) (r:=a*r) (ρ:=1/a)
    (by positivity) (by rw [mul_pow,ha2]; nlinarith) hhalf hhalf1
  apply LipschitzWith.of_dist_le_mul
  intro x y
  rw [←hmean x,←hmean y]
  have hh := hL.dist_le_mul ((1/r) • x) ((1/r) • y)
  rw [dist_smul₀,Real.norm_eq_abs,abs_of_pos (by positivity : 0<1/r)] at hh
  apply hh.trans_eq
  change (Real.pi^2/2)*(1/a)*((lam:ℝ)*(a*r))*((1/r)*dist x y)=
    ((Real.pi^2/2)*(lam:ℝ))*dist x y
  field_simp
end LogConcaveSampling

end

end

end OAI
end

section
-- module Solutions.OAIQ048_LC.LogConcave_Numerics_EvalLipschitz
attribute [-instance] _root_.OAI.LogConcaveSampling.LowerBound.couplingLaw_probability _root_.OAI.LogConcaveSampling.LowerBound.remainingHaar_probability _root_.OAI.LogConcaveSampling.LowerBound.roundRandomLaw_probability _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_invInvariant _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_isHaar _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_probability _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_rightInvariant _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_compactSpace _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_measurableInv _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_measurableMul _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_secondCountable _root_.OAI.LogConcaveSampling.MeanTree.instIsProbabilityMeasureRowTapeRowLaw _root_.OAI.LogConcaveSampling.OracleCompiler.topSeedLaw_probability _root_.OAI.LogConcaveSampling.noiseKernel_markov
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
namespace LogConcaveSampling.MeanTree
open MeasureTheory
open scoped Classical BigOperators NNReal

variable {X Z : Type*} [MeasurableSpace X] [PseudoMetricSpace Z] {d : ℕ}

lemma eval_exists_lipschitz {F : Point d → ℝ} {lam : ℝ≥0} (hF : Primitive F lam)
    (E : MeanTree X d) (f : Z → X)
    (hb : ∃K : ℝ≥0,LipschitzWith K (fun z => base E (f z)))
    (hc : centers (fun r b => 0 < r ∧ (lam:ℝ)*r^2≤1/4 ∧
      ∃K : ℝ≥0,LipschitzWith K (fun z => b (f z))) E) :
    ∃K : ℝ≥0,LipschitzWith K (fun z => E.eval F (f z)) := by
  induction E with | node k b hm a r C ih =>
    choose K hK using fun i => ih i (hc i).1.2.2 (hc i).2
    let L : ℝ≥0 := ∑ i,K i
    have hL (i : Fin k) : K i≤L := Finset.single_le_sum (fun j _ => by positivity) (Finset.mem_univ i)
    have hM (i : Fin k) := (primitiveExpectedField_lipschitz hF (hc i).1.1 (hc i).1.2.1).comp ((hK i).weaken (hL i))
    have hs := finite_weighted_lipschitz a (fun i z => primitiveExpectedField F ((C i).eval F (f z)) (r i)) hM
    obtain ⟨L,hL⟩ := hb
    exact ⟨_,hL.add hs⟩

end LogConcaveSampling.MeanTree

end

end

end OAI
end

section
-- module Solutions.OAIQ048_LC.LogConcave_Sampling_SampleCorrelation
attribute [-instance] _root_.OAI.LogConcaveSampling.LowerBound.couplingLaw_probability _root_.OAI.LogConcaveSampling.LowerBound.remainingHaar_probability _root_.OAI.LogConcaveSampling.LowerBound.roundRandomLaw_probability _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_invInvariant _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_isHaar _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_probability _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_rightInvariant _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_compactSpace _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_measurableInv _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_measurableMul _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_secondCountable _root_.OAI.LogConcaveSampling.MeanTree.instIsProbabilityMeasureRowTapeRowLaw _root_.OAI.LogConcaveSampling.OracleCompiler.topSeedLaw_probability _root_.OAI.LogConcaveSampling.noiseKernel_markov
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
namespace LogConcaveSampling
open MeasureTheory ProbabilityTheory Function
open scoped Classical NNReal

variable {d : ℕ}

lemma probability_endpoint_divided_law {F : Point d → ℝ} {lam : ℝ≥0}
    (hF : Primitive F lam) (x : Point d) {r T a : ℝ} (hr : 0 ≤ r)
    (hl : (lam:ℝ)*r^2≤1/2) (hT : 0<T) (hT1 : T<1)
    (ha : T⁻¹*Real.sqrt (1-T^2)=a) :
    (stdGaussian (Point d)).map (fun z => T⁻¹ • fullProbabilityFlow hF x hr hl T z)=
      ((gibbs (primitivePotential F x r)).prod (stdGaussian (Point d))).map
        (fun z => z.1+a • z.2) := by
  have hf := (fullProbabilityFlow_lipschitz hF x hr hl ⟨hT.le,hT1.le⟩).continuous.measurable
  have hp := congrArg (Measure.map (fun z : Point d => T⁻¹ • z))
    (fullProbabilityFlow_interpolation hF x hr hl hT hT1)
  rw [Measure.map_map (by fun_prop) hf] at hp
  unfold interpolationLaw at hp
  rw [Measure.map_map (by fun_prop) (by fun_prop)] at hp
  simpa only [comp_def,smul_add,smul_smul,inv_mul_cancel₀ hT.ne',one_smul,ha] using hp

lemma probability_endpoint_noisy_law {F : Point d → ℝ} {lam : ℝ≥0}
    (hF : Primitive F lam) (x : Point d) {r T a b s : ℝ} (hr : 0 ≤ r)
    (hl : (lam:ℝ)*r^2≤1/2) (hT : 0<T) (hT1 : T<1)
    (ha : T⁻¹*Real.sqrt (1-T^2)=a) (hs : a^2+b^2=s^2) :
    ((stdGaussian (Point d)).prod (stdGaussian (Point d))).map
      (fun z => T⁻¹ • fullProbabilityFlow hF x hr hl T z.1+b • z.2)=
      ((gibbs (primitivePotential F x r)).prod (stdGaussian (Point d))).map
        (fun z => z.1+s • z.2) := by
  let := probability_gibbs_of_partition
    (partition_pos_of_continuous (hF.continuous_potential x r)).ne'
    (partition_ne_top_of_integrable (hF.integrable_exp_neg_potential x hr (by linarith)))
  have hf := (fullProbabilityFlow_lipschitz hF x hr hl ⟨hT.le,hT1.le⟩).continuous.measurable
  exact smoothing_add_gaussian (stdGaussian (Point d)) (gibbs (primitivePotential F x r))
    (fun z => T⁻¹ • fullProbabilityFlow hF x hr hl T z) id (by fun_prop) measurable_id a b s hs
    (probability_endpoint_divided_law hF x hr hl hT hT1 ha)

lemma sample_noise_variance (η : ℝ) :
    (η/2)^2+(η/Real.sqrt 2)^2=(Real.sqrt 3*η/2)^2 := by
  have h2 := Real.sq_sqrt (by norm_num : (0:ℝ)≤2)
  have h3 := Real.sq_sqrt (by norm_num : (0:ℝ)≤3)
  rw [div_pow,div_pow,div_pow,mul_pow,h2,h3]
  ring
end LogConcaveSampling

end

end

end OAI
end

section
-- module Solutions.OAIQ048_LC.LogConcave_OraclePrograms_MeanSize
attribute [-instance] _root_.OAI.LogConcaveSampling.LowerBound.couplingLaw_probability _root_.OAI.LogConcaveSampling.LowerBound.remainingHaar_probability _root_.OAI.LogConcaveSampling.LowerBound.roundRandomLaw_probability _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_invInvariant _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_isHaar _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_probability _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_rightInvariant _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_compactSpace _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_measurableInv _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_measurableMul _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_secondCountable _root_.OAI.LogConcaveSampling.OracleCompiler.topSeedLaw_probability _root_.OAI.LogConcaveSampling.noiseKernel_markov
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
namespace LogConcaveSampling.OracleCompiler
open MeanTree MeasureTheory Quadrature
open scoped Classical NNReal

variable {d : ℕ}

lemma SampleSize.nonneg {lam q r η : ℝ} (hlam : 0 ≤ lam) (h : SampleSize lam q r η) : 0 ≤ q := by
  have hp := (mul_nonneg hlam (sq_nonneg r)).trans h.2.2.2.2
  exact nonneg_of_mul_nonneg_left hp h.2.2.1

lemma internal_meanSize {lam Q r R D A r' n : ℝ}
    (hlam : 0 ≤ lam) (hQ : 0 ≤ Q) (hr : 0 < r) (hr1 : r ≤ 1)
    (hR : 0 < R) (hD : 0 < D) (hA : 0 < A)
    (hl : lam*r^2 ≤ Q) (hlo : r*R ≤ r') (hhi : r' ≤ r)
    (hn : r*R/(2*D) ≤ n) :
    MeanSize lam (Q+4*D*lam*A/R) r' (declaredNoise n A) := by
  have hr' : 0 < r' := (mul_pos hr hR).trans_le hlo
  have hn0 : 0 < n := (div_pos (mul_pos hr hR) (by positivity)).trans_le hn
  have hτ : 0 < declaredNoise n A := by unfold declaredNoise; positivity
  have hloτ : r*R/(4*D*A) ≤ declaredNoise n A := by
    have hh := div_le_div_of_nonneg_right hn (show 0 ≤ 2*A by positivity)
    convert! hh using 1
    all_goals try with_reducible_and_instances rfl
    field_simp
    ring
  refine ⟨hr',hhi.trans hr1,hτ,?_,?_⟩
  · have he := (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hr'.le hhi 2) hlam).trans hl
    exact he.trans (le_add_of_nonneg_right (by positivity))
  · have hh := mul_le_mul_of_nonneg_left hloτ (show 0 ≤ 4*D*lam*A/R by positivity)
    have hid : (4*D*lam*A/R)*(r*R/(4*D*A))=lam*r := by field_simp
    rw [hid] at hh
    have hrh := mul_le_mul_of_nonneg_left hhi hlam
    have hQt := mul_nonneg hQ hτ.le
    nlinarith

namespace CircuitParameters
variable (C : CircuitParameters)

lemma sampleCenterBudget_small {lam q r η : ℝ} (hlam : 0 ≤ lam)
    (h : SampleSize lam q r η) (hA : 0 ≤ C.A) :
    lam*C.sampleCenterBudget r ≤ C.A*q := by
  have hq := h.nonneg hlam
  have he := h.2.2.2.2.trans (mul_le_of_le_one_right hq h.2.2.2.1)
  have hh := mul_le_mul_of_nonneg_left he hA
  unfold sampleCenterBudget
  convert! hh using 1
  all_goals try with_reducible_and_instances rfl
  ring

end CircuitParameters
end LogConcaveSampling.OracleCompiler

end

end

section

noncomputable section
namespace LogConcaveSampling.OracleCompiler
open MeanTree Quadrature FinitePicard
open scoped Classical BigOperators NNReal

lemma fixedProbabilityBudget_spec (n : ℕ) : 0≤fixedProbabilityBudget n ∧
    ∀{T h : ℝ},0<T → T<1 → 0<h →
      ∀i : ProbabilityNode T h (n+1),∑j,|probabilityWeight T h (n+1) i j|≤fixedProbabilityBudget n :=
  (probabilityWeight_budget (n+1) (Nat.succ_pos n)).choose_spec

lemma fixedCenteringBudget_spec (n : ℕ) : 0≤fixedCenteringBudget n ∧
    (∀i,∑j,|centeringWeight n i j|≤fixedCenteringBudget n) ∧
    (∑j,|Quadrature.weight (probabilityNodes n) j 0 1|≤fixedCenteringBudget n) := by
  have h₁ : 0≤∑i : Fin (n+1),∑j,|centeringWeight n i j| := by positivity
  have h₂ : 0≤∑j : Fin (n+1),|Quadrature.weight (probabilityNodes n) j 0 1| := by positivity
  refine ⟨by unfold fixedCenteringBudget; positivity,?_,?_⟩
  · intro i
    have he := Finset.single_le_sum (fun j (_ : j∈Finset.univ) =>
      show 0≤∑k,|centeringWeight n j k| by positivity) (Finset.mem_univ i)
    unfold fixedCenteringBudget
    linarith
  · unfold fixedCenteringBudget
    linarith

namespace CircuitParameters
variable (C : CircuitParameters)

lemma actualA_pos : 0<C.actualA := by
  have hP := (fixedProbabilityBudget_spec C.n).1
  have hB := (fixedCenteringBudget_spec C.nc).1
  have hQ : 0≤C.quadratureBudget := by unfold quadratureBudget; positivity
  have hS : 0≤C.derivativeBudget := by unfold derivativeBudget; positivity
  unfold actualA
  positivity
lemma actualAf_pos : 0<C.actualAf := by
  have hP := (fixedProbabilityBudget_spec C.n).1
  have hB := (fixedCenteringBudget_spec C.nc).1
  unfold actualAf
  positivity

lemma sampleTree_actual_weights {d : ℕ} {r η : ℝ} (hr : 0 < r) (hη : 0<η) (hη1 : η≤1) :
    weight (C.sampleTree (d:=d) r η hη hη1)≤C.actualAf*r ∧
    centersBound (C.actualA*r^2) (C.sampleTree (d:=d) r η hη hη1) := by
  have hp := sampleCorrelation_properties hη hη1
  have hp0 : 0 < sampleCorrelation η := by linarith [hp.1]
  have hP := fixedProbabilityBudget_spec C.n
  have hB := fixedCenteringBudget_spec C.nc
  have hP0 := hP.1
  have hB0 := hB.1
  have hQ : 0≤C.quadratureBudget := by unfold quadratureBudget; positivity
  have hS : 0≤C.derivativeBudget := by unfold derivativeBudget; positivity
  apply literalSample_weights hr hP.1 hp.1 (C.n+1) C.N (C.sampleEndpoint η hη hη1)
  · intro j
    have ht := probabilityNodeTime_mem hp0 hp.2.1 C.h_pos (Nat.succ_pos C.n) j
    rw [abs_of_nonneg ht.1]
    exact ht.2.trans hp.2.1.le
  · exact hP.2 hp0 hp.2.1 C.h_pos
  · unfold actualA
    have he : 0≤2*fixedCenteringBudget C.nc*
      (C.quadratureBudget*C.derivativeBudget*(2*fixedProbabilityBudget C.n)+2) := by positivity
    have hh := (fixedHarmonicBudget C.n).coe_nonneg
    linarith [hP.1]
  · unfold actualAf
    linarith [hB.1]

end CircuitParameters
end LogConcaveSampling.OracleCompiler

end

end

end OAI
end

section
-- module Solutions.OAIQ048_LC.LogConcave_Sampling_LogMeshCountRate
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
namespace LogConcaveSampling
open Filter Quadrature
open scoped Topology

lemma sampleCorrelation_radius_lower {η : ℝ} (hη : 0<η) (hη1 : η≤1) :
    η/4≤Real.sqrt (1-(sampleCorrelation η)^2) := by
  have hp := sampleCorrelation_properties hη hη1
  have ht : 0 < sampleCorrelation η := by linarith
  have he : Real.sqrt (1-(sampleCorrelation η)^2)=sampleCorrelation η*(η/2) := by
    have h := congrArg (fun z : ℝ => sampleCorrelation η*z) hp.2.2
    simpa only [←mul_assoc,mul_inv_cancel₀ ht.ne',one_mul] using h
  rw [he]
  nlinarith

end LogConcaveSampling

end

end

end OAI
end

section
-- module Solutions.OAIQ048_LC.LogConcave_OraclePrograms_MeanCorrect
attribute [-instance] _root_.OAI.LogConcaveSampling.LowerBound.couplingLaw_probability _root_.OAI.LogConcaveSampling.LowerBound.remainingHaar_probability _root_.OAI.LogConcaveSampling.LowerBound.roundRandomLaw_probability _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_invInvariant _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_isHaar _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_probability _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_rightInvariant _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_compactSpace _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_measurableInv _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_measurableMul _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_secondCountable _root_.OAI.LogConcaveSampling.OracleCompiler.topSeedLaw_probability _root_.OAI.LogConcaveSampling.noiseKernel_markov
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
namespace LogConcaveSampling.OracleCompiler
open MeanTree MeasureTheory Quadrature
open scoped Classical NNReal

variable {d : ℕ}

lemma MeanSize.mono {lam q q' r σ : ℝ} (h : MeanSize lam q r σ) (hq : q≤q') :
    MeanSize lam q' r σ :=
  ⟨h.1,h.2.1,h.2.2.1,h.2.2.2.1.trans hq,
    h.2.2.2.2.trans (mul_le_mul_of_nonneg_right hq h.2.2.1.le)⟩

lemma final_sample_size {lam q r η r' Af : ℝ} (hlam : 0≤lam)
    (h : SampleSize lam q r η) (hr' : 0 < r') (hhi : r' ≤ r) (hAf : 0<Af) :
    MeanSize lam ((1+4*Af)*q) r' (declaredNoise (η/Real.sqrt 2) (Af*r)) := by
  have hr := h.1
  have hη0 := h.2.2.1
  have hq := h.nonneg hlam
  have hs2 : 0<Real.sqrt 2 := by positivity
  have hs21 : Real.sqrt 2≤2 := by norm_num
  have hn : 0<declaredNoise (η/Real.sqrt 2) (Af*r) := by unfold declaredNoise; positivity
  have hl : lam*r^2≤q := h.2.2.2.2.trans (mul_le_of_le_one_right hq h.2.2.2.1)
  have hqf : q≤(1+4*Af)*q := by nlinarith
  refine ⟨hr',hhi.trans h.2.1,hn,?_,?_⟩
  · exact (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hr'.le hhi 2) hlam).trans (hl.trans hqf)
  · have hη : η/(4*Af*r)≤declaredNoise (η/Real.sqrt 2) (Af*r) := by
      unfold declaredNoise
      apply (le_div_iff₀ (by positivity : 0<2*(Af*r))).2
      calc
        η/(4*Af*r)*(2*(Af*r))=η/2 := by field_simp [hr.ne']; ring
        _≤η/Real.sqrt 2 := div_le_div_of_nonneg_left h.2.2.1.le hs2 hs21
    have hh := mul_le_mul_of_nonneg_right hη (show 0≤4*Af*q by positivity)
    have hid : (η/(4*Af*r))*(4*Af*q)=q*η/r := by field_simp
    rw [hid] at hh
    have hs : lam*r≤q*η/r := (le_div_iff₀ h.1).2 (by nlinarith [h.2.2.2.2])
    have hm := mul_le_mul_of_nonneg_left hhi hlam
    have he := mul_le_mul_of_nonneg_right (show 4*Af*q≤(1+4*Af)*q by nlinarith) hn.le
    nlinarith

namespace CircuitParameters
variable (C : CircuitParameters)

lemma residual_pos : 0<Real.sqrt (1-C.T^2) := by
  apply Real.sqrt_pos.mpr
  nlinarith [C.T_lower,C.T_upper]

theorem sampleTree_valid {lam q r η R : ℝ} (hlam : 0≤lam) (hs : SampleSize lam q r η)
    (hR : 0<R) (hRη : R≤η) (hD : 0<C.D)
    (hA : C.A=C.actualA) (hAf : C.Af=C.actualAf) :
    DeclaredRootValid C.D (C.sampleCenterBudget r) (C.sampleFinalBudget r)
      (MeanSize lam ((1+4*C.Af)*q))
      (MeanSize lam (q*(1+16*C.D*C.A/R)))
      (C.sampleTree (d:=d) r η hs.2.2.1 hs.2.2.2.1) (η/Real.sqrt 2) := by
  have hA0 : 0<C.A := hA ▸ C.actualA_pos
  have hAf0 : 0<C.Af := hAf ▸ C.actualAf_pos
  have hr := hs.1
  have hη := hs.2.2.1
  have hq := hs.nonneg hlam
  have hb : 0<C.sampleCenterBudget r := by unfold sampleCenterBudget; positivity
  have hw := C.sampleTree_actual_weights (d:=d) hr hη hs.2.2.2.1
  rw [←hA,←hAf] at hw
  have hp := sampleCorrelation_properties hη hs.2.2.2.1
  have hg := (literalSample_geometry (d:=d) (r:=r) (N:=C.N) (Nat.succ_pos C.n)
    (by linarith [hp.1]) hp.2.1 C.h_pos (C.sampleEndpoint η hη hs.2.2.2.1)).2
  have hrad : centers (fun r' (_ : SampleInput d → Point d) => r*(R/4) ≤ r' ∧ r' ≤ r)
      (C.sampleTree r η hη hs.2.2.2.1) := by
    apply centers_mono _ (fun r' b h => ?_) hg
    have hh := h.radius hr.le (by linarith [hp.1]) hp.2.1
    have hlow := sampleCorrelation_radius_lower hη hs.2.2.2.1
    exact ⟨(mul_le_mul_of_nonneg_left (by linarith : R/4≤Real.sqrt (1-(sampleCorrelation η)^2)) hr.le).trans hh.1,hh.2⟩
  have hfinal : rootScales (fun r' => MeanSize lam ((1+4*C.Af)*q) r'
      (declaredNoise (η/Real.sqrt 2) (C.sampleFinalBudget r)))
      (C.sampleTree (d:=d) r η hη hs.2.2.2.1) := by
    cases he : C.sampleTree (d:=d) r η hη hs.2.2.2.1 with | node k b hb a rr cc =>
      rw [he] at hrad
      intro i
      exact final_sample_size hlam hs ((by positivity : 0 < r*(R/4)).trans_le (hrad i).1.1)
        (hrad i).1.2 hAf0
  apply declaredRootValid_of_radius_bounds hD (by positivity : 0 < r*(R/4)) _ _ _
    (by positivity) hw.1 hw.2 hrad hfinal
  intro r' n hlo hhi hn _
  have hl : lam*r^2≤q := hs.2.2.2.2.trans (mul_le_of_le_one_right hq hs.2.2.2.1)
  apply (internal_meanSize hlam hq hr hs.2.1 (by positivity : 0<R/4) hD hb hl hlo hhi hn).mono
  have hsml := C.sampleCenterBudget_small hlam hs hA0.le
  have hh := mul_le_mul_of_nonneg_left hsml (show 0≤16*C.D/R by positivity)
  calc
    q+4*C.D*lam*C.sampleCenterBudget r/(R/4)
        = q+(16*C.D/R)*(lam*C.sampleCenterBudget r) := by ring
    _≤q+(16*C.D/R)*(C.A*q) := add_le_add le_rfl hh
    _=q*(1+16*C.D*C.A/R) := by ring

end CircuitParameters
end LogConcaveSampling.OracleCompiler

end

end

end OAI
end

section
-- module Solutions.OAIQ048_LC.LogConcave_Sampling_AnchorGauge
attribute [-instance] _root_.OAI.LogConcaveSampling.LowerBound.couplingLaw_probability _root_.OAI.LogConcaveSampling.LowerBound.remainingHaar_probability _root_.OAI.LogConcaveSampling.LowerBound.roundRandomLaw_probability _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_invInvariant _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_isHaar _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_probability _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_rightInvariant _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_compactSpace _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_measurableInv _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_measurableMul _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_secondCountable _root_.OAI.LogConcaveSampling.MeanTree.instIsProbabilityMeasureRowTapeRowLaw _root_.OAI.LogConcaveSampling.OracleCompiler.topSeedLaw_probability _root_.OAI.LogConcaveSampling.noiseKernel_markov
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
namespace LogConcaveSampling
open MeasureTheory ProbabilityTheory
open scoped Classical NNReal

variable {d : ℕ}

lemma one_le_anchorGauge {C : ℝ} (hC : 0≤C) (z : Point d) : 1≤anchorGauge C z := by
  unfold anchorGauge; linarith [norm_nonneg z]
lemma anchorGauge_change (C : ℝ) (x y : Point d) :
    anchorGauge C y≤anchorGauge C x+dist x y := by
  have hh := norm_le_norm_add_norm_sub x y
  dsimp [anchorGauge]
  rw [dist_eq_norm]
  linarith
lemma anchorGauge_gaussian_integrable (C : ℝ) :
    Integrable (fun z : Point d => (anchorGauge C z)^2) (stdGaussian (Point d)) := by
  have h := (memLp_const (1+C) (p:=2) (μ:=stdGaussian (Point d))).add
    (IsGaussian.memLp_two_id (μ:=stdGaussian (Point d))).norm
  exact h.integrable_sq
lemma anchorGauge_gaussian_moment (C : ℝ) :
    (∫z : Point d,(anchorGauge C z)^2 ∂stdGaussian (Point d))≤2*(1+C)^2+2*d := by
  have hi2 : Integrable (fun z : Point d => ‖z‖^2) (stdGaussian (Point d)) := by
    simpa only [id_eq] using (IsGaussian.memLp_two_id (μ:=stdGaussian (Point d))).norm.integrable_sq
  have hi : Integrable (fun z : Point d => 2*(1+C)^2+2*‖z‖^2) (stdGaussian (Point d)) :=
    (integrable_const _).add (hi2.const_mul _)
  apply (integral_mono (anchorGauge_gaussian_integrable C) hi (fun z => ?_)).trans_eq
    (show (∫z : Point d,2*(1+C)^2+2*‖z‖^2 ∂stdGaussian (Point d))=2*(1+C)^2+2*d by
      rw [integral_add (integrable_const _) (hi2.const_mul _),
        integral_const,probReal_univ,one_smul,integral_const_mul,stdGaussian_sq_norm])
  dsimp [anchorGauge]
  nlinarith [sq_nonneg (1+C-‖z‖)]
lemma anchorGauge_circuitD_moment (hd : 1≤d) (F : Point d → ℝ) (x : Point d) :
    (∫z : Point d,(anchorGauge (circuitD F x) z)^2 ∂stdGaussian (Point d))≤10*(circuitD F x)^2 := by
  apply (anchorGauge_gaussian_moment _).trans
  have hs := Real.sq_sqrt (Nat.cast_nonneg d : (0:ℝ)≤d)
  have hdim : (1:ℝ)≤d := by exact_mod_cast hd
  have hD := sqrt_le_circuitD F x
  have h0 := circuitD_nonneg F x
  have hr0 := Real.sqrt_nonneg (d:ℝ)
  have hr1 : 1≤Real.sqrt (d:ℝ) := by nlinarith
  have h1 : 1 ≤ circuitD F x := hr1.trans hD
  have hsq := pow_le_pow_left₀ hr0 hD 2
  nlinarith [sq_nonneg (circuitD F x-1)]
end LogConcaveSampling

end

end

end OAI
end

section
-- module Solutions.OAIQ048_LC.LogConcave_Sampling_PairGauge
attribute [-instance] _root_.OAI.LogConcaveSampling.LowerBound.couplingLaw_probability _root_.OAI.LogConcaveSampling.LowerBound.remainingHaar_probability _root_.OAI.LogConcaveSampling.LowerBound.roundRandomLaw_probability _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_invInvariant _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_isHaar _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_probability _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_rightInvariant _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_compactSpace _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_measurableInv _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_measurableMul _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_secondCountable _root_.OAI.LogConcaveSampling.OracleCompiler.topSeedLaw_probability _root_.OAI.LogConcaveSampling.noiseKernel_markov
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
namespace LogConcaveSampling
open MeanTree MeasureTheory ProbabilityTheory
open scoped Classical NNReal

variable {d : ℕ}

namespace OracleCompiler.CircuitParameters
variable (C : CircuitParameters)

lemma sampleTree_centerValues {F : Point d → ℝ} {lam : ℝ≥0} (hF : Primitive F lam)
    {r η : ℝ} (hr : 0 < r) (hη : 0<η) (hη1 : η≤1)
    (hA : C.A=C.actualA) (hl : (lam:ℝ)*r^2≤1/2) (hL : (lam:ℝ)*r≤1)
    (hsmall : (lam:ℝ)*C.sampleCenterBudget r*(2*Real.pi+2)≤1)
    (x Y : Point d) :
    centerValues F ((depth (C.sampleTree (d:=d) r η hη hη1):ℝ)*anchorGauge (circuitD F x) Y)
      (C.sampleTree r η hη hη1) (x,Y) := by
  have hp := sampleCorrelation_properties hη hη1
  have hw := (C.sampleTree_actual_weights (d:=d) hr hη hη1).2
  rw [←hA] at hw
  have hg := (literalSample_geometry (d:=d) (r:=r) (N:=C.N) (Nat.succ_pos C.n)
    (by linarith [hp.1]) hp.2.1 C.h_pos (C.sampleEndpoint η hη hη1)).2
  have hh := centerValues_of_direct hF hr.le (by linarith [hp.1]) hp.2.1 (by norm_num : (0:ℝ)≤0)
    hl hL hsmall Prod.fst Prod.snd (fun _ : SampleInput d => 0) (x,Y)
    (depth (C.sampleTree r η hη hη1)) (C.sampleTree r η hη hη1) hw le_rfl hg
  apply centerValues_mono _ _ _ hh
  have he : circuitD F x+(lam:ℝ)*r*‖Y‖≤anchorGauge (circuitD F x) Y := by
    have hh := mul_le_of_le_one_left (norm_nonneg Y) hL
    unfold anchorGauge; linarith
  simpa using mul_le_mul_of_nonneg_left he (Nat.cast_nonneg (depth (C.sampleTree (d:=d) r η hη hη1)): (0:ℝ)≤_)
end OracleCompiler.CircuitParameters
end LogConcaveSampling

end

end

end OAI
end

section
-- module Solutions.OAIQ048_LC.LogConcave_OraclePrograms_PairDistBounds
attribute [-instance] _root_.OAI.LogConcaveSampling.LowerBound.couplingLaw_probability _root_.OAI.LogConcaveSampling.LowerBound.remainingHaar_probability _root_.OAI.LogConcaveSampling.LowerBound.roundRandomLaw_probability _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_invInvariant _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_isHaar _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_probability _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_rightInvariant _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_compactSpace _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_measurableInv _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_measurableMul _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_secondCountable _root_.OAI.LogConcaveSampling.OracleCompiler.topSeedLaw_probability _root_.OAI.LogConcaveSampling.noiseKernel_markov
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
namespace LogConcaveSampling.OracleCompiler.CircuitParameters
open MeanTree MeasureTheory Quadrature
open scoped Classical NNReal

variable (C : CircuitParameters) {d : ℕ}

lemma sampleTree_anchorVariation {r η : ℝ} (hr : 0 ≤ r) (hη : 0<η) (hη1 : η≤1)
    (x z w : Point d) :
    BaseVariation ((r+|(sampleCorrelation η)⁻¹|)*dist z w) (x,z) (x,w)
      (C.sampleTree r η hη hη1) := by
  have hp := sampleCorrelation_properties hη hη1
  have hg := literalSample_geometry (d:=d) (r:=r) (N:=C.N) (Nat.succ_pos C.n)
    (by linarith [hp.1]) hp.2.1 C.h_pos (C.sampleEndpoint η hη hη1)
  apply baseVariation_of_centers
  · unfold sampleTree
    rw [hg.1]
    simp only [←smul_sub,norm_smul,Real.norm_eq_abs,dist_eq_norm]
    nlinarith [mul_nonneg hr (norm_nonneg (z-w))]
  · exact centers_mono _ (fun r' b hb => by
      have he := hb.variation hr hp.2.1.le (x,z) (x,w)
      simp only [sub_self,norm_zero,zero_add,add_zero] at he
      rw [dist_eq_norm]
      nlinarith [mul_nonneg (abs_nonneg ((sampleCorrelation η)⁻¹)) (norm_nonneg (z-w))]) hg.2

lemma sampleTree_anchor_lipschitz {F : Point d → ℝ} {lam : ℝ≥0} (hF : Primitive F lam)
    {r η : ℝ} (hr : 0 < r) (hη : 0<η) (hη1 : η≤1) (hl : (lam:ℝ)*r^2≤1/4) (x : Point d) :
    ∃K : ℝ≥0,LipschitzWith K (fun z : Point d => (C.sampleTree r η hη hη1).eval F (x,z)) := by
  have hp := sampleCorrelation_properties hη hη1
  have hg := literalSample_geometry (d:=d) (r:=r) (N:=C.N) (Nat.succ_pos C.n)
    (by linarith [hp.1]) hp.2.1 C.h_pos (C.sampleEndpoint η hη hη1)
  apply eval_exists_lipschitz hF (C.sampleTree r η hη hη1) (fun z => (x,z))
  · unfold sampleTree
    rw [hg.1]
    exact ⟨_,lipschitzWith_smul ((sampleCorrelation η)⁻¹)⟩
  · apply centers_mono _ (fun r' b hb => ?_) hg.2
    have hr' := hb.radius_pos hr (by linarith [hp.1]) hp.2.1
    have hb' := hb.radius hr.le (by linarith [hp.1]) hp.2.1
    have hs := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hr'.le hb'.2 2) lam.coe_nonneg
    refine ⟨hr',hs.trans hl,?_⟩
    obtain ⟨ρ,hρ,θ,hθ,he,rfl⟩ := hb
    exact ⟨_,(LipschitzWith.const x).add ((lipschitzWith_smul (r*ρ)).comp
      ((lipschitzWith_smul (Real.cos θ)).add ((lipschitzWith_smul (Real.sin θ)).comp (LipschitzWith.const 0))))⟩

lemma sampleCompiled_anchor_lipschitz {r η Lf Li : ℝ} (hr : 0 < r) (hη : 0<η) (hη1 : η≤1)
    (hA : C.A=C.actualA) (hAf : C.Af=C.actualAf)
    (hLf : 0≤Lf) (hLi : 0≤Li) (hsmall : Li*C.sampleCenterBudget r≤1)
    (V : Point d → ℝ) (P : Bool → ℝ → ℝ → Prop) (M : Bool → ℝ → ℝ → SeedProgram d)
    (hm : ∀r τ,P true r τ → ∀u v g,‖(M true r τ).program.run V (u,g)-(M true r τ).program.run V (v,g)‖≤Lf*‖u-v‖)
    (hmi : ∀r τ,P false r τ → ∀u v g,‖(M false r τ).program.run V (u,g)-(M false r τ).program.run V (v,g)‖≤Li*‖u-v‖)
    (n : ℝ) (hready : RootShiftReady C.D (C.sampleCenterBudget r) (C.sampleFinalBudget r)
      (P true) (P false) (C.sampleTree (d:=d) r η hη hη1) n) (x : Point d) :
    let E := compileDeclaredRoot C.D (C.sampleCenterBudget r) (C.sampleFinalBudget r)
      (M true) (M false) (C.sampleTree (d:=d) r η hη hη1) n
    ∃K : ℝ,0≤K ∧ ∀z w g,‖E.eval V (x,z) g-E.eval V (x,w) g‖≤K*dist z w := by
  have hw := C.sampleTree_actual_weights (d:=d) hr hη hη1
  rw [←hAf,←hA] at hw
  have hAf0 : 0≤C.sampleFinalBudget r := by unfold sampleFinalBudget; rw [hAf]; positivity [C.actualAf_pos]
  let b := r+|(sampleCorrelation η)⁻¹|
  refine ⟨C.sampleFinalBudget r*Lf*(depth (C.sampleTree (d:=d) r η hη hη1):ℝ)*b+b,by dsimp [b]; positivity,?_⟩
  intro z w g
  have hv := C.sampleTree_anchorVariation hr.le hη hη1 x z w
  have hb : ‖base (C.sampleTree r η hη hη1) (x,z)-base (C.sampleTree r η hη hη1) (x,w)‖≤b*dist z w := by
    generalize C.sampleTree (d:=d) r η hη hη1=E at hv ⊢
    cases E
    exact hv.1
  have he := compileDeclaredRoot_variation hLf hLi (show 0≤b*dist z w by dsimp [b]; positivity)
    hsmall V P M hm hmi (C.sampleTree r η hη hη1) n (x,z) (x,w) hv hb hw.1 hw.2 hready g
  convert he using 1 <;> (try simp only [sampleFinalBudget])
  dsimp [b]
  ring

end LogConcaveSampling.OracleCompiler.CircuitParameters

end

end

section

noncomputable section
namespace LogConcaveSampling.OracleCompiler.CircuitParameters
open MeasureTheory ProbabilityTheory MeanTree Quadrature Function
open scoped Classical NNReal

variable (C : CircuitParameters) {d : ℕ}

lemma sampleTree_eval {F : Point d → ℝ} {lam : ℝ≥0} (hF : Primitive F lam)
    (r η : ℝ) (hη : 0<η) (hη1 : η≤1) (x Y : Point d) :
    (C.sampleTree r η hη hη1).eval F (x,Y)=
      sampleMeanCircuit F x r (sampleCorrelation η) C.h (C.n+1) C.N (C.sampleEndpoint η hη hη1) Y := by
  unfold sampleTree literalSample
  rw [eval_scale,eval_forward hF (Nat.succ_pos C.n)
    (by linarith [(sampleCorrelation_properties hη hη1).1])
    (sampleCorrelation_properties hη hη1).2.1 C.h_pos]
  simp only [eval_anchor,sampleMeanCircuit]

end LogConcaveSampling.OracleCompiler.CircuitParameters

end

end

end OAI
end

section
-- module Solutions.OAIQ048_LC.LogConcave_OraclePrograms_ShiftInvariant
attribute [-instance] _root_.OAI.LogConcaveSampling.LowerBound.couplingLaw_probability _root_.OAI.LogConcaveSampling.LowerBound.remainingHaar_probability _root_.OAI.LogConcaveSampling.LowerBound.roundRandomLaw_probability _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_invInvariant _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_isHaar _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_probability _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_rightInvariant _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_compactSpace _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_measurableInv _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_measurableMul _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_secondCountable _root_.OAI.LogConcaveSampling.OracleCompiler.topSeedLaw_probability _root_.OAI.LogConcaveSampling.noiseKernel_markov
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
namespace LogConcaveSampling.OracleCompiler
open MeasureTheory ProbabilityTheory MeanTree Coupling SeedCompiler
open scoped Classical BigOperators NNReal

variable {d : ℕ}

lemma MeanBudget.shiftInvariant {B : ℕ} {r : ℝ} {S : SeedProgram d}
    (h : MeanBudget B r S) (F : Point d → ℝ) :
    ShiftInvariant r S.shift (fun c g => S.program.run F (c,g)) := by
  intro x Δ g
  exact (h.equiv Δ).run F (x,g)

namespace CircuitParameters
variable (C : CircuitParameters)

lemma sampleCompiled_squared {F : Point d → ℝ} {lam : ℝ≥0} (hF : Primitive F lam)
    {q Kf Ki ef ei r η : ℝ} (hs : SampleSize lam q r η) (hl : q≤1/2)
    (hL : (lam:ℝ)*r≤1) (hRη : Real.sqrt (1-C.T^2)≤η) (hD : 0<C.D)
    (hA : C.A=C.actualA) (hAf : C.Af=C.actualAf)
    (hKf : 0≤Kf) (hKi : 0≤Ki)
    (hsmall : (lam:ℝ)*C.sampleCenterBudget r*(2*Real.pi+2)≤1)
    (hcon : 4*(C.sampleCenterBudget r)^2*((lam:ℝ)*Ki)^2≤1)
    (Mf Mi : ℝ → ℝ → SeedProgram d) (B : ℕ) (hBD : (B:ℝ)≤C.D^2)
    (hbudget : ∀(s : Bool) r τ,MeanBudget B r ((if s then Mf else Mi) r τ))
    (hf : MeanCorrect F lam ((1+4*C.Af)*q) Kf ef Mf)
    (hi : MeanCorrect F lam (q*(1+16*C.D*C.A/Real.sqrt (1-C.T^2))) Ki ei Mi)
    (x Y : Point d) :
    let E := compileDeclaredRoot C.D (C.sampleCenterBudget r) (C.sampleFinalBudget r) Mf Mi
      (C.sampleTree (d:=d) r η hs.2.2.1 hs.2.2.2.1) (η/Real.sqrt 2)
    SquaredAt (gaussianTape d E.slots) (stdGaussian (Point d)) (E.eval F (x,Y))
      (fun g => (C.sampleTree r η hs.2.2.1 hs.2.2.2.1).eval F (x,Y)+(η/Real.sqrt 2) • g)
      ((2*(C.sampleFinalBudget r)^2*((lam:ℝ)*Kf)^2*(r/(2*C.D))^2*ei^2+(η/Real.sqrt 2)^2*ef^2/2)*
        ((depth (C.sampleTree (d:=d) r η hs.2.2.1 hs.2.2.2.1):ℝ)*anchorGauge (circuitD F x) Y)^2) := by
  have hr := hs.1
  have hn := hs.2.2.1
  let P : Bool → ℝ → ℝ → Prop := fun s => if s then
    MeanSize lam ((1+4*C.Af)*q) else MeanSize lam (q*(1+16*C.D*C.A/Real.sqrt (1-C.T^2)))
  let M : Bool → ℝ → ℝ → SeedProgram d := fun s => if s then Mf else Mi
  have hb (s : Bool) (r τ : ℝ) := hbudget s r τ
  have hV : Measurable (firstOrderReply F) := hF.smooth.continuous.measurable.prodMk
    hF.gradient_lipschitz.continuous.measurable
  have hv := C.sampleTree_valid (d:=d) lam.coe_nonneg hs C.residual_pos hRη hD hA hAf
  have hw := C.sampleTree_actual_weights (d:=d) hs.1 hs.2.2.1 hs.2.2.2.1
  rw [←hAf,←hA] at hw
  have hp := sampleCorrelation_properties hs.2.2.1 hs.2.2.2.1
  have hg := (literalSample_geometry (d:=d) (r:=r) (N:=C.N) (Nat.succ_pos C.n)
    (by linarith [hp.1]) hp.2.1 C.h_pos (C.sampleEndpoint η hs.2.2.1 hs.2.2.2.1)).2
  have hrs : centers (fun r' _ => 0 ≤ r' ∧ r' ≤ r) (C.sampleTree (d:=d) r η hs.2.2.1 hs.2.2.2.1) :=
    centers_mono _ (fun r' b hb => ⟨(hb.radius_pos hs.1 (by linarith [hp.1]) hp.2.1).le,
      (hb.radius hs.1.le (by linarith [hp.1]) hp.2.1).2⟩) hg
  have hl' : (lam:ℝ)*r^2≤1/2 := hs.2.2.2.2.trans
    ((mul_le_of_le_one_right (hs.nonneg lam.coe_nonneg) hs.2.2.2.1).trans hl)
  exact compileDeclaredRoot_normalized F F hV hD
    (by unfold sampleCenterBudget; rw [hA]; positivity [C.actualA_pos])
    (by unfold sampleFinalBudget; rw [hAf]; positivity [C.actualAf_pos])
    (mul_nonneg lam.coe_nonneg hKi) (mul_nonneg lam.coe_nonneg hKf)
    hcon P M (fun s r τ _ => (hb s r τ).shiftInvariant F)
    (fun s r τ _ => (hb s r τ).energy.trans hBD) hi.lip hf.lip hi.error hf.error
    (C.sampleTree r η hs.2.2.1 hs.2.2.2.1) (x,Y) hv hw.2 hrs
    (C.sampleTree_centerValues hF hs.1 hs.2.2.1 hs.2.2.2.1 hA hl' hL hsmall x Y)
end CircuitParameters
end LogConcaveSampling.OracleCompiler

end

end

section

noncomputable section
namespace LogConcaveSampling.OracleCompiler
open MeanTree MeasureTheory
open scoped Classical

lemma physicalCoefficient_bound {lam r s D Af K ei ef q n : ℝ}
    (hl : 0 ≤ lam) (hr : 0 ≤ r) (hs : 0 < s) (hD : 1 ≤ D) (hAf : 0 ≤ Af)
    (hK : 0 ≤ K) (hi : 0 ≤ ei) (hf : 0 ≤ ef) (hq : lam*r ≤ q*s)
    (hn : 0 ≤ n) (hns : n ≤ s) :
    2*Af^2*(lam*K)^2*(r/(2*D))^2*ei^2+n^2*ef^2/2 ≤
      2*s^2*(Af*K*q*ei+ef)^2 := by
  have hD0 : 0 < 2*D := by linarith
  have hq0 : 0 ≤ q := by nlinarith [mul_nonneg hl hr]
  have hab : lam*r/(2*D) ≤ q*s := by
    apply (div_le_iff₀ hD0).2
    have hh := mul_le_mul_of_nonneg_left (by linarith : (1:ℝ) ≤ 2*D) (mul_nonneg hq0 hs.le)
    nlinarith
  have ha : 0 ≤ Af*K*(lam*r/(2*D))*ei := by positivity
  have hb : Af*K*(lam*r/(2*D))*ei ≤ s*(Af*K*q*ei) := by
    have hh := mul_le_mul_of_nonneg_left hab (show 0 ≤ Af*K*ei by positivity)
    nlinarith
  have hc : n*ef ≤ s*ef := mul_le_mul_of_nonneg_right hns hf
  have ha2 := pow_le_pow_left₀ ha hb 2
  have hb2 := pow_le_pow_left₀ (mul_nonneg hn hf) hc 2
  have hid : Af^2*(lam*K)^2*(r/(2*D))^2*ei^2=(Af*K*(lam*r/(2*D))*ei)^2 := by ring
  have hid2 : 2*Af^2*(lam*K)^2*(r/(2*D))^2*ei^2=2*(Af*K*(lam*r/(2*D))*ei)^2 := by nlinarith [hid]
  rw [hid2]
  nlinarith [mul_nonneg (show 0 ≤ Af*K*q*ei by positivity) hf]

lemma physicalError_bound {c s a dep ρ : ℝ} (_hs : 0 ≤ s) (_ha : 0 ≤ a) (hd : 0 ≤ dep)
    (hc : c ≤ 2*s^2*a^2) :
    c*(dep*ρ)^2 ≤ (2*s*(1+dep)*a)^2*ρ^2 := by
  have hh := mul_le_mul_of_nonneg_right hc (sq_nonneg (dep*ρ))
  have hdep : 2*dep^2 ≤ (2*(1+dep))^2 := by nlinarith
  have hh' := mul_le_mul_of_nonneg_right hdep (show 0 ≤ s^2*a^2*ρ^2 by positivity)
  nlinarith

end LogConcaveSampling.OracleCompiler

end

end

section

noncomputable section
namespace LogConcaveSampling.OracleCompiler.CircuitParameters
open MeanTree MeasureTheory ProbabilityTheory Coupling SeedCompiler
open scoped Classical NNReal

variable (C : CircuitParameters) {d : ℕ}

lemma sampleCompiled_scaled {F : Point d → ℝ} {lam : ℝ≥0} (hF : Primitive F lam)
    {q Kf Ki ef ei r η : ℝ} (hs : SampleSize lam q r η) (hl : q ≤ 1/2)
    (hL : (lam:ℝ)*r ≤ 1) (hRη : Real.sqrt (1-C.T^2) ≤ η) (hD : 1 ≤ C.D)
    (hA : C.A=C.actualA) (hAf : C.Af=C.actualAf)
    (hKf : 0 ≤ Kf) (hKi : 0 ≤ Ki) (hef : 0 ≤ ef) (hei : 0 ≤ ei)
    (hsmall : (lam:ℝ)*C.sampleCenterBudget r*(2*Real.pi+2) ≤ 1)
    (hcon : 4*(C.sampleCenterBudget r)^2*((lam:ℝ)*Ki)^2 ≤ 1)
    (Mf Mi : ℝ → ℝ → SeedProgram d) (B : ℕ) (hBD : (B:ℝ) ≤ C.D^2)
    (hbudget : ∀(s : Bool) r τ,MeanBudget B r ((if s then Mf else Mi) r τ))
    (hf : MeanCorrect F lam ((1+4*C.Af)*q) Kf ef Mf)
    (hi : MeanCorrect F lam (q*(1+16*C.D*C.A/Real.sqrt (1-C.T^2))) Ki ei Mi)
    (x Y : Point d) :
    let E := compileDeclaredRoot C.D (C.sampleCenterBudget r) (C.sampleFinalBudget r) Mf Mi
      (C.sampleTree (d:=d) r η hs.2.2.1 hs.2.2.2.1) (η/Real.sqrt 2)
    let a := 2*(1+(depth (C.sampleTree (d:=d) r η hs.2.2.1 hs.2.2.2.1):ℝ))*(C.Af*Kf*q*ei+ef)
    SquaredAt (gaussianTape d E.slots) (stdGaussian (Point d)) (E.eval F (x,Y))
      (fun g => (C.sampleTree r η hs.2.2.1 hs.2.2.2.1).eval F (x,Y)+(η/Real.sqrt 2) • g)
      ((η*a)^2*(anchorGauge (circuitD F x) Y)^2) := by
  have hAf0 : 0 ≤ C.Af := by rw [hAf]; exact C.actualAf_pos.le
  have hn : η/Real.sqrt 2 ≤ η := by
    exact div_le_self hs.2.2.1.le (by nlinarith [Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2),Real.sqrt_nonneg (2:ℝ)])
  have hc := physicalCoefficient_bound (mul_nonneg lam.coe_nonneg hs.1.le) hs.1.le hs.2.2.1 hD hAf0 hKf hei hef
    (show ((lam:ℝ)*r)*r ≤ q*η by nlinarith [hs.2.2.2.2])
    (show 0 ≤ η/Real.sqrt 2 by positivity [hs.2.2.1]) hn
  have hb := physicalError_bound hs.2.2.1.le
    (show 0 ≤ C.Af*Kf*q*ei+ef by positivity [hs.nonneg lam.coe_nonneg])
    (show 0 ≤ (depth (C.sampleTree (d:=d) r η hs.2.2.1 hs.2.2.2.1):ℝ) by positivity)
    (ρ:=anchorGauge (circuitD F x) Y) hc
  have hp := C.sampleCompiled_squared hF hs hl hL hRη (by linarith) hA hAf hKf hKi hsmall hcon
    Mf Mi B hBD hbudget hf hi x Y
  apply hp.mono
  convert hb using 1 <;> (try unfold sampleFinalBudget) <;> ring
end LogConcaveSampling.OracleCompiler.CircuitParameters

end

end

end OAI
end

section
-- module Solutions.OAIQ048_LC.LogConcave_OraclePrograms_NoisyCircuit
attribute [-instance] _root_.OAI.LogConcaveSampling.LowerBound.couplingLaw_probability _root_.OAI.LogConcaveSampling.LowerBound.remainingHaar_probability _root_.OAI.LogConcaveSampling.LowerBound.roundRandomLaw_probability _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_invInvariant _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_isHaar _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_probability _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_rightInvariant _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_compactSpace _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_measurableInv _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_measurableMul _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_secondCountable _root_.OAI.LogConcaveSampling.MeanTree.instIsProbabilityMeasureRowTapeRowLaw _root_.OAI.LogConcaveSampling.OracleCompiler.topSeedLaw_probability _root_.OAI.LogConcaveSampling.noiseKernel_markov
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
namespace LogConcaveSampling.Coupling
open MeasureTheory ProbabilityTheory Function TopologicalSpace
open scoped Classical

variable {X Ω : Type*} [PseudoMetricSpace X] [SeparableSpace X] [Nonempty X]
  [MeasurableSpace X] [BorelSpace X] [StandardBorelSpace X] [MeasurableSpace Ω]
  {d : ℕ}

theorem SquaredAt.noisy_circuit (μ : Measure X) [IsProbabilityMeasure μ]
    (ν : Measure Ω) [IsProbabilityMeasure ν]
    (f : X → Ω → Point d) (g u : X → Point d)
    (hf : Measurable (uncurry f)) (hg : Measurable g) (hu : Measurable u)
    (ρ : X → ℝ) (hρ : ∀x,1≤ρ x) (hρlip : ∀x y,ρ y≤ρ x+dist x y)
    (hρi : Integrable (fun x => (ρ x)^2) μ)
    {Lf Lg E R n : ℝ} (hLf : 0≤Lf) (hLg : 0≤Lg) (hE : 0<E)
    (hfl : ∀x y z,‖f x z-f y z‖≤Lf*dist x y)
    (hgl : ∀x y,‖g x-g y‖≤Lg*dist x y)
    (hc : ∀x,SquaredAt ν (stdGaussian (Point d)) (f x)
      (fun w => g x+n • w) (E^2*(ρ x)^2))
    (hi : Integrable (fun x => ‖g x-u x‖^2) μ)
    (he : (∫x,‖g x-u x‖^2 ∂μ)≤R) :
    SquaredAt (μ.prod ν) (μ.prod (stdGaussian (Point d))) (uncurry f)
      (fun z => u z.1+n • z.2) (20*E^2*(∫x,(ρ x)^2 ∂μ)+2*R) := by
  have hnmeas : Measurable (fun z : X × Point d => g z.1+n • z.2) := by fun_prop
  have hc' := SquaredAt.random_anchor μ ν (stdGaussian (Point d)) f
    (fun x w => g x+n • w) hf hnmeas ρ hρ hρlip hρi hLf hLg hE hfl
    (fun x y w => by simpa only [add_sub_add_right_eq_sub] using hgl x y) hc
  have hbase := SquaredAt.same_tape μ g u hg hu hi he
  have hnoise := hbase.add_shared (stdGaussian (Point d)) hg hu (fun w => n • w) (by fun_prop)
  have ht := hc'.trans hf hnmeas (by fun_prop) hnoise
  convert ht using 1
  all_goals try with_reducible_and_instances rfl
  ring

theorem SquaredAt.noisy_circuit_target {Γ : Type*} [MeasurableSpace Γ]
    [StandardBorelSpace Γ] [Nonempty Γ]
    (μ : Measure X) [IsProbabilityMeasure μ] (ν : Measure Ω) [IsProbabilityMeasure ν]
    (θ : Measure Γ) [IsProbabilityMeasure θ]
    (f : X → Ω → Point d) (g u : X → Point d) (v : Γ → Point d)
    (hf : Measurable (uncurry f)) (hg : Measurable g) (hu : Measurable u) (hv : Measurable v)
    (ρ : X → ℝ) (hρ : ∀x,1≤ρ x) (hρlip : ∀x y,ρ y≤ρ x+dist x y)
    (hρi : Integrable (fun x => (ρ x)^2) μ)
    {Lf Lg E R n : ℝ} (hLf : 0≤Lf) (hLg : 0≤Lg) (hE : 0<E)
    (hfl : ∀x y z,‖f x z-f y z‖≤Lf*dist x y)
    (hgl : ∀x y,‖g x-g y‖≤Lg*dist x y)
    (hc : ∀x,SquaredAt ν (stdGaussian (Point d)) (f x)
      (fun w => g x+n • w) (E^2*(ρ x)^2))
    (hi : Integrable (fun x => ‖g x-u x‖^2) μ) (he : (∫x,‖g x-u x‖^2 ∂μ)≤R)
    (hlaw : (μ.prod (stdGaussian (Point d))).map (fun z => u z.1+n • z.2)=θ.map v) :
    SquaredAt (μ.prod ν) θ (uncurry f) v (40*E^2*(∫x,(ρ x)^2 ∂μ)+4*R) := by
  have hh := (SquaredAt.noisy_circuit μ ν f g u hf hg hu ρ hρ hρlip hρi
    hLf hLg hE hfl hgl hc hi he).change_ideal θ v hf (by fun_prop) hv hlaw
  convert hh using 1
  all_goals try with_reducible_and_instances rfl
  ring
end LogConcaveSampling.Coupling

end

end

end OAI
end

section
-- module Solutions.OAIQ048_LC.LogConcave_Sampling_PrependTape
attribute [-instance] _root_.OAI.LogConcaveSampling.LowerBound.couplingLaw_probability _root_.OAI.LogConcaveSampling.LowerBound.remainingHaar_probability _root_.OAI.LogConcaveSampling.LowerBound.roundRandomLaw_probability _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_invInvariant _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_isHaar _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_probability _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_rightInvariant _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_compactSpace _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_measurableInv _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_measurableMul _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_secondCountable _root_.OAI.LogConcaveSampling.OracleCompiler.topSeedLaw_probability _root_.OAI.LogConcaveSampling.noiseKernel_markov
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
namespace LogConcaveSampling
open MeasureTheory ProbabilityTheory OracleCompiler Function
open scoped Classical

variable {d : ℕ}

lemma oneSlot_preserving {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [SigmaFinite μ] :
    MeasurePreserving (fun z : Ω => fun _ : Fin 1 => z) μ (Measure.pi fun _ : Fin 1 => μ) := by
  convert (measurePreserving_piUnique (fun _ : Fin 1 => μ)).symm (MeasurableEquiv.piUnique (fun _ : Fin 1 => Ω)) using 1
  all_goals try with_reducible_and_instances rfl
  funext z i
  have hi : i=default := Subsingleton.elim _ _
  subst i
  rfl

lemma prependTape_preserving (k : ℕ) :
    MeasurePreserving (prependTape (d:=d) k) ((stdGaussian (Point d)).prod (gaussianTape d k))
      (gaussianTape d (1+k)) := by
  exact (MeanTree.appendSlots_preserving (stdGaussian (Point d)) 1 k).comp
    ((oneSlot_preserving (stdGaussian (Point d))).prod (MeasurePreserving.id _))

lemma sampleParent_run_prepend (E : Expression (Point d × Point d) d)
    (v : Fin E.slots → ℝ) (T η : ℝ) (V : Point d → ℝ) (x : Point d)
    (z : Point d × (Fin E.slots → Point d)) :
    (sampleParent E v T η).pre.run V (x,prependTape E.slots z)=E.eval V (x,z.1) z.2 := by
  rw [sampleParent_run]
  simp only [prependTape,Fin.append_left,Fin.append_right]

end LogConcaveSampling

end

end

section

noncomputable section
namespace LogConcaveSampling
open MeasureTheory ProbabilityTheory OracleCompiler Coupling Function
open scoped Classical NNReal

variable {d : ℕ}

theorem sampleParent_squared {F : Point d → ℝ} {lam : ℝ≥0} (hF : Primitive F lam)
    (x : Point d) {r T η h : ℝ} (hr : 0 ≤ r) (hl : (lam:ℝ)*r^2≤1/2)
    (hT : 0<T) (hT1 : T<1) (hη : T⁻¹*Real.sqrt (1-T^2)=η/2)
    (n N : ℕ) (e : ProbabilityNode T h n) (_he : probabilityNodeTime T h n e=T)
    (E : Expression (Point d × Point d) d) (v : Fin E.slots → ℝ)
    {Lf Lg err R : ℝ} (hLf : 0≤Lf) (hLg : 0≤Lg) (herr : 0<err)
    (hg : Measurable (sampleMeanCircuit F x r T h n N e))
    (hfl : ∀Y Z g,‖E.eval F (x,Y) g-E.eval F (x,Z) g‖≤Lf*dist Y Z)
    (hgl : ∀Y Z,‖sampleMeanCircuit F x r T h n N e Y-
      sampleMeanCircuit F x r T h n N e Z‖≤Lg*dist Y Z)
    (hc : ∀Y,SquaredAt (gaussianTape d E.slots) (stdGaussian (Point d))
      (E.eval F (x,Y)) (fun z => sampleMeanCircuit F x r T h n N e Y+(η/Real.sqrt 2) • z)
      (err^2*(anchorGauge (circuitD F x) Y)^2))
    (hi : Integrable (fun Y => ‖sampleMeanCircuit F x r T h n N e Y-
      T⁻¹ • fullProbabilityFlow hF x hr hl T Y‖^2) (stdGaussian (Point d)))
    (hnum : (∫Y,‖sampleMeanCircuit F x r T h n N e Y-
      T⁻¹ • fullProbabilityFlow hF x hr hl T Y‖^2 ∂stdGaussian (Point d))≤R) :
    SquaredAt (gaussianTape d (1+E.slots))
      ((gibbs (primitivePotential F x r)).prod (stdGaussian (Point d)))
      (fun g => (sampleParent E v T η).pre.run F (x,g))
      (fun z => z.1+(Real.sqrt 3*η/2) • z.2)
      (40*err^2*(∫z,(anchorGauge (circuitD F x) z)^2 ∂stdGaussian (Point d))+4*R) := by
  have hV : Measurable (fun z => (F z,gradient F z)) :=
    hF.smooth.continuous.measurable.prodMk hF.gradient_lipschitz.continuous.measurable
  have hE := E.measurable_eval F hV
  have hf : Measurable (uncurry (fun Y g => E.eval F (x,Y) g)) :=
    hE.comp (show Measurable (fun z : Point d × (Fin E.slots → Point d) => ((x,z.1),z.2)) by fun_prop)
  have hu : Measurable (fun Y => T⁻¹ • fullProbabilityFlow hF x hr hl T Y) := by
    have hh := (fullProbabilityFlow_lipschitz hF x hr hl ⟨hT.le,hT1.le⟩).continuous.measurable
    fun_prop
  let := probability_gibbs_of_partition
    (partition_pos_of_continuous (hF.continuous_potential x r)).ne'
    (partition_ne_top_of_integrable (hF.integrable_exp_neg_potential x hr (by linarith)))
  have hh := SquaredAt.noisy_circuit_target (stdGaussian (Point d)) (gaussianTape d E.slots)
    ((gibbs (primitivePotential F x r)).prod (stdGaussian (Point d)))
    (fun Y g => E.eval F (x,Y) g) (sampleMeanCircuit F x r T h n N e)
    (fun Y => T⁻¹ • fullProbabilityFlow hF x hr hl T Y)
    (fun z => z.1+(Real.sqrt 3*η/2) • z.2) hf hg hu (by fun_prop)
    (anchorGauge (circuitD F x)) (one_le_anchorGauge (circuitD_nonneg F x))
    (anchorGauge_change _) (anchorGauge_gaussian_integrable _) hLf hLg herr hfl hgl hc hi hnum
    (probability_endpoint_noisy_law hF x hr hl hT hT1 hη (sample_noise_variance η))
  have hp := hh.reindex (prependTape E.slots) id (prependTape_preserving E.slots).measurable measurable_id
    (fun g => (sampleParent E v T η).pre.run F (x,g))
    (fun z => z.1+(Real.sqrt 3*η/2) • z.2) ?_ (by fun_prop)
    (fun z => sampleParent_run_prepend E v T η F x z) (fun _ => rfl)
  · simpa only [(prependTape_preserving E.slots).map_eq,Measure.map_id] using hp
  · exact ((sampleParent E v T η).pre.measurable_run F hV).comp (by fun_prop)
end LogConcaveSampling

end

end

end OAI
end

section
-- module Solutions.OAIQ048_LC.LogConcave_OraclePrograms_FullTape
attribute [-instance] _root_.OAI.LogConcaveSampling.LowerBound.couplingLaw_probability _root_.OAI.LogConcaveSampling.LowerBound.remainingHaar_probability _root_.OAI.LogConcaveSampling.LowerBound.roundRandomLaw_probability _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_invInvariant _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_isHaar _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_probability _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_rightInvariant _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_compactSpace _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_measurableInv _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_measurableMul _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_secondCountable _root_.OAI.LogConcaveSampling.OracleCompiler.topSeedLaw_probability _root_.OAI.LogConcaveSampling.noiseKernel_markov
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
namespace LogConcaveSampling.OracleCompiler.CircuitParameters
open MeasureTheory ProbabilityTheory MeanTree Coupling Function
open scoped Classical NNReal

variable (C : CircuitParameters) {d : ℕ}

theorem sampleFrom_squared_oai {F : Point d → ℝ} {lam : ℝ≥0} (hF : Primitive F lam)
    {q Kf Ki ef ei r η en : ℝ} (hd : 1 ≤ d)
    (hs : SampleSize lam q r η) (hl : q ≤ 1/4) (hL : (lam:ℝ)*r ≤ 1)
    (hRη : Real.sqrt (1-C.T^2) ≤ η) (hD : 1 ≤ C.D)
    (hA : C.A=C.actualA) (hAf : C.Af=C.actualAf)
    (hKf : 0 ≤ Kf) (hKi : 0 ≤ Ki) (hef : 0 < ef) (hei : 0 ≤ ei)
    (hsmall : (lam:ℝ)*C.sampleCenterBudget r*(2*Real.pi+2) ≤ 1)
    (hcon : 4*(C.sampleCenterBudget r)^2*((lam:ℝ)*Ki)^2 ≤ 1)
    (Mf Mi : ℝ → ℝ → SeedProgram d) (B : ℕ) (hBD : (B:ℝ) ≤ C.D^2)
    (hbudget : ∀(s : Bool) r τ,MeanBudget B r ((if s then Mf else Mi) r τ))
    (hf : MeanCorrect F lam ((1+4*C.Af)*q) Kf ef Mf)
    (hi : MeanCorrect F lam (q*(1+16*C.D*C.A/Real.sqrt (1-C.T^2))) Ki ei Mi)
    (x : Point d)
    (hlr : (lam:ℝ)*r^2 ≤ 1/2)
    (hnumi : Integrable (fun Y => ‖sampleMeanCircuit F x r (sampleCorrelation η) C.h
      (C.n+1) C.N (C.sampleEndpoint η hs.2.2.1 hs.2.2.2.1) Y-
      (sampleCorrelation η)⁻¹ • fullProbabilityFlow hF x hs.1.le hlr (sampleCorrelation η) Y‖^2)
      (stdGaussian (Point d)))
    (hnum : (∫Y,‖sampleMeanCircuit F x r (sampleCorrelation η) C.h
      (C.n+1) C.N (C.sampleEndpoint η hs.2.2.1 hs.2.2.2.1) Y-
      (sampleCorrelation η)⁻¹ • fullProbabilityFlow hF x hs.1.le hlr (sampleCorrelation η) Y‖^2
      ∂stdGaussian (Point d)) ≤ (circuitD F x)^2*en^2) :
    let dep := (depth (C.sampleTree (d:=d) r η hs.2.2.1 hs.2.2.2.1):ℝ)
    let a := 2*(1+dep)*(C.Af*Kf*q*ei+ef)
    SquaredAt (gaussianTape d (C.sampleFrom Mf Mi r η).slots)
      ((gibbs (primitivePotential F x r)).prod (stdGaussian (Point d)))
      (fun g => (C.sampleFrom Mf Mi r η).pre.run F (x,g))
      (fun z => z.1+(Real.sqrt 3*η/2) • z.2)
      ((400*(η*a)^2+4*en^2)*(circuitD F x)^2) := by
  let dep := (depth (C.sampleTree (d:=d) r η hs.2.2.1 hs.2.2.2.1):ℝ)
  let a := 2*(1+dep)*(C.Af*Kf*q*ei+ef)
  let P : Bool → ℝ → ℝ → Prop := fun s => if s then
    MeanSize lam ((1+4*C.Af)*q) else MeanSize lam (q*(1+16*C.D*C.A/Real.sqrt (1-C.T^2)))
  let M : Bool → ℝ → ℝ → SeedProgram d := fun s => if s then Mf else Mi
  let E := compileDeclaredRoot C.D (C.sampleCenterBudget r) (C.sampleFinalBudget r) Mf Mi
    (C.sampleTree (d:=d) r η hs.2.2.1 hs.2.2.2.1) (η/Real.sqrt 2)
  have hA0 : 0 < C.A := hA ▸ C.actualA_pos
  have hAf0 : 0 < C.Af := hAf ▸ C.actualAf_pos
  have hbud : 0 ≤ C.sampleCenterBudget r := by unfold sampleCenterBudget; positivity
  have hLip : (lam:ℝ)*Ki*C.sampleCenterBudget r ≤ 1 := by
    have hn : 0 ≤ (lam:ℝ)*Ki*C.sampleCenterBudget r := by positivity
    nlinarith [sq_nonneg ((lam:ℝ)*Ki*C.sampleCenterBudget r)]
  have hrad : (lam:ℝ)*r^2 ≤ 1/4 := hs.2.2.2.2.trans
    ((mul_le_of_le_one_right (hs.nonneg lam.coe_nonneg) hs.2.2.2.1).trans hl)
  have ha : 0 < a := by dsimp [a,dep]; positivity [hs.nonneg lam.coe_nonneg]
  have hv := C.sampleTree_valid (d:=d) lam.coe_nonneg hs C.residual_pos hRη (by linarith) hA hAf
  have hrdy := hv.shiftReady (P true) (P false) (fun _ _ h => h.1.ne') (fun _ _ h => h.1.ne') _ _
  obtain ⟨Lf,hLf,hfl⟩ := C.sampleCompiled_anchor_lipschitz hs.1 hs.2.2.1 hs.2.2.2.1 hA hAf
    (mul_nonneg lam.coe_nonneg hKf) (mul_nonneg lam.coe_nonneg hKi) hLip F P M hf.lip hi.lip
    (η/Real.sqrt 2) hrdy x
  obtain ⟨Lg,hgl⟩ := C.sampleTree_anchor_lipschitz hF hs.1 hs.2.2.1 hs.2.2.2.1 hrad x
  have heval : (fun Y => (C.sampleTree r η hs.2.2.1 hs.2.2.2.1).eval F (x,Y))=
      sampleMeanCircuit F x r (sampleCorrelation η) C.h (C.n+1) C.N
        (C.sampleEndpoint η hs.2.2.1 hs.2.2.2.1) := by
    funext Y; exact C.sampleTree_eval hF r η hs.2.2.1 hs.2.2.2.1 x Y
  rw [heval] at hgl
  have hc Y := C.sampleCompiled_scaled hF hs (by linarith) hL hRη hD hA hAf hKf hKi hef.le hei
    hsmall hcon Mf Mi B hBD hbudget hf hi x Y
  simp only [C.sampleTree_eval hF] at hc
  let v := compileDeclaredRootShift C.D (C.sampleCenterBudget r) (C.sampleFinalBudget r) Mf Mi
    (C.sampleTree (d:=d) r η hs.2.2.1 hs.2.2.2.1) (η/Real.sqrt 2)
    (C.sampleDrift r η hs.1 hs.2.2.1 hs.2.2.2.1)
  have hpr := sampleCorrelation_properties hs.2.2.1 hs.2.2.2.1
  have hp := sampleParent_squared hF x hs.1.le hlr (by linarith [hpr.1]) hpr.2.1 hpr.2.2
    (C.n+1) C.N (C.sampleEndpoint η hs.2.2.1 hs.2.2.2.1)
    (probabilityEndpoint_time _ _ C.h_pos _ (by omega)) E v hLf Lg.coe_nonneg (mul_pos hs.2.2.1 ha)
    hgl.continuous.measurable hfl
    (fun z z' => by simpa only [dist_eq_norm] using hgl.dist_le_mul z z') hc hnumi hnum
  unfold sampleFrom
  rw [dite_eq_left ⟨hs.1,hs.2.2.1,hs.2.2.2.1⟩]
  apply hp.mono
  have hh := mul_le_mul_of_nonneg_left (anchorGauge_circuitD_moment hd F x)
    (show 0 ≤ 40*(η*a)^2 by positivity)
  calc
    _ ≤ 40*(η*a)^2*(10*(circuitD F x)^2)+4*((circuitD F x)^2*en^2) := add_le_add hh le_rfl
    _ = _ := by ring
end LogConcaveSampling.OracleCompiler.CircuitParameters

end

end

end OAI
end

theorem solution : type_of% @OAI.LogConcaveSampling.OracleCompiler.CircuitParameters.sampleFrom_squared_oai := @OAI.LogConcaveSampling.OracleCompiler.CircuitParameters.sampleFrom_squared_oai
