-- Prove2me | solution 1 for OAI.LogConcaveSampling.OracleCompiler.exists_source_numerical_ready
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-27T13:49:11.201247+00:00
-- url     : https://prove2.me/submissions/8f01f196-0dd2-4068-a303-5c83ff5ca333

import Mathlib
import Definitions.Def_LogConcaveQuery
import Definitions.Def_OAIQ048L004
import Theorems.Thm_OAI_LogConcaveSampling_centeringMeanCircuit_rms
import Theorems.Thm_OAI_LogConcaveSampling_centeringPicard_state_rms
import Theorems.Thm_OAI_LogConcaveSampling_centeringVelocityJoint_full_rms
import Theorems.Thm_OAI_LogConcaveSampling_exists_centering_stationaryPath
import Theorems.Thm_OAI_LogConcaveSampling_sampleMeanCircuit_rms
import Theorems.Thm_OAI_LogConcaveSampling_stationaryMeanTarget_identity
import Theorems.Thm_OAI_LogConcaveSampling_stationaryMeanTarget_law

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

lemma map_snd_withDensity {E G : Type*} [MeasurableSpace E] [MeasurableSpace G]
    (μ : Measure E) (ν : Measure G) [SFinite μ] [SFinite ν]
    {w : E × G → ℝ≥0∞} (hw : Measurable w) :
    ((μ.prod ν).withDensity w).map Prod.snd=
      ν.withDensity (fun y => ∫⁻ x,w (x,y) ∂μ) := by
  apply Measure.ext_of_lintegral
  intro f hf
  rw [lintegral_map hf measurable_snd]
  change (∫⁻ a, (f ∘ Prod.snd) a ∂(μ.prod ν).withDensity w)=_
  rw [lintegral_withDensity_eq_lintegral_mul _ hw (hf.comp measurable_snd),
    lintegral_withDensity_eq_lintegral_mul _ hw.lintegral_prod_left' hf,
    lintegral_prod_symm _ (hw.mul (hf.comp measurable_snd)).aemeasurable]
  apply lintegral_congr
  intro y
  exact lintegral_mul_const (f y) (hw.comp (measurable_id.prodMk measurable_const))

lemma probability_density_eq_gibbs {d : ℕ} {H : Point d → ℝ}
    {c : ℝ≥0∞} {μ : Measure (Point d)} [IsProbabilityMeasure μ]
    (he : μ=c • volume.withDensity (gibbsDensity H)) : μ=gibbs H := by
  have hh := congrArg (fun ν : Measure (Point d) => ν Set.univ) he
  rw [measure_univ,Measure.smul_apply,withDensity_apply _ MeasurableSet.univ,
    Measure.restrict_univ,smul_eq_mul] at hh
  have hc : c=(partition H)⁻¹ := ENNReal.eq_inv_of_mul_eq_one_left hh.symm
  simpa [gibbs,hc] using he

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

lemma interpolationLaw_probability {d : ℕ} {F : Point d → ℝ} {lam : ℝ≥0}
    (hF : Primitive F lam) (x : Point d) {r : ℝ} (hr : 0 ≤ r)
    (hl : (lam:ℝ)*r^2<1) (ρ : ℝ) : IsProbabilityMeasure (interpolationLaw F x r ρ) := by
  let := probability_gibbs_of_partition
    (partition_pos_of_continuous (hF.continuous_potential x r)).ne'
    (partition_ne_top_of_integrable (hF.integrable_exp_neg_potential x hr hl))
  unfold interpolationLaw
  first | infer_instance | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | (apply Measurable.aemeasurable; measurability) | measurability)

theorem interpolationLaw_eq_gibbs {d : ℕ} {F : Point d → ℝ} {lam : ℝ≥0}
    (hF : Primitive F lam) (x : Point d) {r ρ : ℝ} (hr : 0 ≤ r)
    (hl : (lam:ℝ)*r^2<1) (hρ : ρ^2<1) :
    interpolationLaw F x r ρ=gibbs (interpolationPotential F x r ρ) := by
  let := interpolationLaw_probability hF x hr hl ρ
  apply probability_density_eq_gibbs
  have ha : 0 < 1-ρ^2 := by linarith
  have hσ : Real.sqrt (1-ρ^2)≠0 := (Real.sqrt_pos.mpr ha).ne'
  have hd := EulerDensity.joint_density (hF.continuous_potential x r).measurable
    (fun z => ρ • z) (by fun_prop) hσ
  have he : interpolationLaw F x r ρ=
      (((gibbs (primitivePotential F x r)).prod (stdGaussian (Point d))).map
        (fun p => (p.1,ρ • p.1+Real.sqrt (1-ρ^2) • p.2))).map Prod.snd := by
    rw [Measure.map_map measurable_snd (by fun_prop)]
    rfl
  rw [he,hd,Measure.map_smul,map_snd_withDensity _ _ (by
    have := (hF.continuous_potential x r).measurable
    fun_prop)]
  congr 1
  congr 1
  funext y
  simp only [Real.sq_sqrt ha.le]
  exact interpolation_density_integral hF x hr hl hρ y
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

lemma directional (hf : PolySmooth f) (v : Point d) : PolySmooth (LogConcaveSampling.directional v f) := by
  refine ⟨directional_smooth hf.smooth v,fun l => ?_⟩
  have he : JetCalculus.jet id [v] f=LogConcaveSampling.directional v f := rfl
  have hh := hf.growth (l++[v])
  rw [JetCalculus.jet_append,he] at hh
  exact hh

lemma polyC1 (hf : PolySmooth f) : PolyC1 f :=
  ⟨hf.smooth.of_le (by simp),hf.growth [],fun v => (hf.directional v).growth []⟩

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

lemma const (c : ℝ) : PolySmooth (fun _ : Point d => c) := by
  refine ⟨contDiff_const,fun l => ?_⟩
  rw [JetCalculus.jet_const]
  split_ifs <;> exact growth_const _

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

end LogConcaveSampling

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
-- module Solutions.OAIQ048_LC.LogConcave_Complexity_PolynomialBudget
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
namespace LogConcaveSampling
open scoped BigOperators

lemma polynomialBudget_nonneg (P : Polynomial ℝ) : 0≤polynomialBudget P :=
  Finset.sum_nonneg (fun _ _ => abs_nonneg _)

end LogConcaveSampling

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

namespace LogConcaveSampling
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators NNReal

lemma interpolationLaw_initial {d : ℕ} {F : Point d → ℝ} {lam : ℝ≥0}
    (hF : Primitive F lam) (x : Point d) {r : ℝ} (hr : 0 ≤ r)
    (hl : (lam:ℝ)*r^2≤1/2) : interpolationLaw F x r 0=stdGaussian (Point d) := by
  let := probability_gibbs_of_partition
    (partition_pos_of_continuous (hF.continuous_potential x r)).ne'
    (partition_ne_top_of_integrable (hF.integrable_exp_neg_potential x hr (by linarith)))
  simp [interpolationLaw,Measure.map_snd_prod]

lemma fullProbabilityFlow_initial {d : ℕ} {F : Point d → ℝ} {lam : ℝ≥0}
    (hF : Primitive F lam) (x : Point d) {r : ℝ} (hr : 0 ≤ r)
    (hl : (lam:ℝ)*r^2≤1/2) : fullProbabilityFlow hF x hr hl 0=id := by
  funext z
  exact GlobalODE.flow_initial _ _ _ _

lemma fullProbabilityFlow_interpolation_closed {d : ℕ} {F : Point d → ℝ} {lam : ℝ≥0}
    (hF : Primitive F lam) (x : Point d) {r ρ : ℝ} (hr : 0 ≤ r)
    (hl : (lam:ℝ)*r^2≤1/2) (h0 : 0≤ρ) (h1 : ρ<1) :
    (stdGaussian (Point d)).map (fullProbabilityFlow hF x hr hl ρ)=interpolationLaw F x r ρ := by
  rcases eq_or_lt_of_le h0 with h|h
  · subst ρ
    rw [fullProbabilityFlow_initial,Measure.map_id,interpolationLaw_initial hF x hr hl]
  · exact fullProbabilityFlow_interpolation hF x hr hl h h1

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
-- module Solutions.OAIQ048_LC.LogConcave_Sampling_TerminalTransportConstant
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
open scoped NNReal

lemma terminalTransportConstant_pos : 0<terminalTransportConstant := by
  unfold terminalTransportConstant
  positivity

variable {d : ℕ} {F : Point d → ℝ} {lam : ℝ≥0}
  (hF : Primitive F lam) (x : Point d) {r : ℝ} (hr : 0 ≤ r)
  (hl : (lam:ℝ)*r^2≤1/2)

include hF hr hl in
lemma probability_affine_residual (z : Point d) {t : ℝ} (ht : t∈Ico (0:ℝ) 1) :
    dist (-r • primitiveField F x r 0)
      (fullProbabilityVelocity F x r t (z-t • (r • primitiveField F x r 0))) ≤
      2*((lam:ℝ)*r^2)*(Real.pi*Real.sqrt d+‖z‖+2*r*‖primitiveField F x r 0‖) := by
  rw [fullProbabilityVelocity_eq F x r ht.1 ht.2]
  unfold probabilityVelocity
  rw [dist_smul₀,Real.norm_eq_abs,abs_neg,abs_of_nonneg hr,dist_comm,dist_eq_norm]
  have hh := conditionalFieldMean_center_zero_bound hF x hr hl ht.1 ht.2
    (z-t • (r • primitiveField F x r 0))
  have hz : ‖z-t • (r • primitiveField F x r 0)‖≤‖z‖+r*‖primitiveField F x r 0‖ := by
    apply (norm_sub_le _ _).trans
    simp only [norm_smul,Real.norm_eq_abs,abs_of_nonneg hr,abs_of_nonneg ht.1]
    exact add_le_add le_rfl (mul_le_of_le_one_left (by positivity) ht.2.le)
  have hn := hh.trans (mul_le_mul_of_nonneg_left
    (add_le_add (add_le_add le_rfl hz) le_rfl) (by positivity : 0≤2*((lam:ℝ)*r)))
  convert mul_le_mul_of_nonneg_left hn hr using 1
  all_goals try with_reducible_and_instances rfl
  first | rfl | ring

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

lemma gaussian_affine_norm_moment (d : ℕ) (a : ℝ) :
    Integrable (fun z : Point d => (a+‖z‖)^2) (stdGaussian (Point d)) ∧
      (∫z : Point d,(a+‖z‖)^2 ∂stdGaussian (Point d))≤2*a^2+2*d := by
  have h : MemLp (fun z : Point d => a+‖z‖) 2 (stdGaussian (Point d)) :=
    (memLp_const a).add (IsGaussian.memLp_two_id (μ:=stdGaussian (Point d))).norm
  have hsq : Integrable (fun z : Point d => ‖z‖^2) (stdGaussian (Point d)) := by
    simpa only [id_eq] using (IsGaussian.memLp_two_id (μ:=stdGaussian (Point d))).integrable_norm_pow
      (by norm_num : (2:ℕ)≠0)
  refine ⟨h.integrable_sq,?_⟩
  calc
    _ ≤ ∫z : Point d,2*a^2+2*‖z‖^2 ∂stdGaussian (Point d) := by
      apply integral_mono h.integrable_sq ((integrable_const _).add (hsq.const_mul 2))
      intro z
      change (a+‖z‖)^2≤2*a^2+2*‖z‖^2
      nlinarith [sq_nonneg (a-‖z‖)]
    _ = _ := by rw [integral_add (integrable_const _) (hsq.const_mul _),
      integral_const,probReal_univ,one_smul,integral_const_mul,stdGaussian_sq_norm]

lemma gaussian_growth_sq_moment {d e : ℕ} {f : Point d → Point e} (hf : Continuous f)
    {K a : ℝ} (hK : 0≤K) (ha : 0≤a) (hbound : ∀z,‖f z‖≤K*(a+‖z‖)) :
    Integrable (fun z => ‖f z‖^2) (stdGaussian (Point d)) ∧
      (∫z,‖f z‖^2 ∂stdGaussian (Point d))≤K^2*(2*a^2+2*d) := by
  have hg := (gaussian_affine_norm_moment d a).1.const_mul (K^2)
  have hb (z : Point d) : ‖f z‖^2≤K^2*(a+‖z‖)^2 := by
    rw [←mul_pow]
    exact (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hK (add_nonneg ha (norm_nonneg z)))).2 (hbound z)
  have hi : Integrable (fun z => ‖f z‖^2) (stdGaussian (Point d)) := by
    apply hg.mono' ((hf.norm.pow 2).aestronglyMeasurable)
    exact Filter.Eventually.of_forall (fun z => by simpa only [Real.norm_eq_abs,Pi.pow_apply,abs_sq] using hb z)
  refine ⟨hi,?_⟩
  calc
    _ ≤ ∫z : Point d,K^2*(a+‖z‖)^2 ∂stdGaussian (Point d) := integral_mono hi hg hb
    _ = K^2*(∫z : Point d,(a+‖z‖)^2 ∂stdGaussian (Point d)) := integral_const_mul _ _
    _ ≤ _ := mul_le_mul_of_nonneg_left (gaussian_affine_norm_moment d a).2 (sq_nonneg K)

end LogConcaveSampling

end

end

section

noncomputable section
namespace LogConcaveSampling
open Set Function MeasureTheory ProbabilityTheory
open scoped NNReal

variable {d : ℕ} {F : Point d → ℝ} {lam : ℝ≥0}
  (hF : Primitive F lam) (x : Point d) {r : ℝ} (hr : 0 ≤ r)
  (hl : (lam:ℝ)*r^2≤1/2)

include hF hr hl in

lemma probabilityFlow_initial_displacement (z : Point d) {t : ℝ} (ht : t∈Icc (0:ℝ) 1) :
    ‖fullProbabilityFlow hF x hr hl t z-z‖≤terminalTransportConstant*
      (r*‖primitiveField F x r 0‖+((lam:ℝ)*r^2)*(Real.pi*Real.sqrt d+‖z‖)) := by
  let c := primitiveField F x r 0
  let D := Real.pi*Real.sqrt d+‖z‖+2*r*‖c‖
  let q := (lam:ℝ)*r^2
  let ε := 2*q*D
  let B := |gronwallBound 0 (Real.pi^2+1) 1 1|+1
  let f (s : ℝ) := fullProbabilityFlow hF x hr hl s z
  let g (s : ℝ) := z-s • (r • c)
  have hv (s : ℝ) : LipschitzWith ⟨Real.pi^2+1,by positivity⟩ (fullProbabilityVelocity F x r s) := by
    apply (fullProbabilityVelocity_lipschitz hF x hr hl s).weaken
    change (Real.pi^2/2)*(lam:ℝ)*r^2≤Real.pi^2+1
    have hh := mul_le_mul_of_nonneg_left hl (by positivity : 0≤Real.pi^2/2)
    nlinarith [sq_nonneg Real.pi]
  have hf : Continuous f := fullProbabilityFlow_time_continuous hF x hr hl z
  have hfd : ∀s∈Icc (0:ℝ) 1,HasDerivWithinAt f
      (fullProbabilityVelocity F x r s (f s)) (Icc 0 1) s := by
    intro s hs
    exact GlobalODE.flow_deriv (a:=0) (b:=1)
      (fun s _ => fullProbabilityVelocity_lipschitz hF x hr hl s)
      (fullProbabilityVelocity_continuous hF x hr hl) ⟨0,le_rfl,by norm_num⟩ z s hs
  have hgd (s : ℝ) : HasDerivAt g (-r • c) s := by
    convert (hasDerivAt_const s z).sub ((hasDerivAt_id s).smul_const (r • c)) using 1 <;> first | rfl | simp
  have hg : Continuous g := by dsimp [g]; fun_prop
  have hh := dist_le_of_approx_trajectories_ODE hv hf.continuousOn
    (GlobalODE.right_deriv hfd) (εf:=0) (fun s _ => by simp) hg.continuousOn
    (fun s _ => (hgd s).hasDerivWithinAt) (εg:=ε)
    (fun s hs => probability_affine_residual hF x hr hl z hs)
    (δ:=0) (by simp only [f,g,fullProbabilityFlow_initial,Function.id_def,zero_smul,sub_zero,dist_self,le_refl]) t ht
  simp only [zero_add,sub_zero] at hh
  rw [GlobalODE.gronwallBound_zero_linear] at hh
  have hmono : gronwallBound 0 (Real.pi^2+1) 1 t≤B :=
    ((gronwallBound_mono (by norm_num) (by norm_num) (by positivity)) ht.2).trans
      (by dsimp [B]; linarith [le_abs_self (gronwallBound 0 (Real.pi^2+1) 1 1)])
  have he : dist (f t) (g t)≤ε*B := hh.trans (mul_le_mul_of_nonneg_left hmono (by dsimp [ε,q,D]; positivity))
  have hgz : dist (g t) z ≤ r*‖c‖ := by
    have he : g t-z=-(t • (r • c)) := by dsimp [g]; abel
    rw [dist_eq_norm,he,norm_neg,norm_smul,norm_smul,Real.norm_eq_abs,
      Real.norm_eq_abs,abs_of_nonneg ht.1,abs_of_nonneg hr]
    exact mul_le_of_le_one_left (by positivity) ht.2
  have ht' := (dist_triangle (f t) (g t) z).trans (add_le_add he hgz)
  change dist (f t) z≤_
  apply ht'.trans
  have hB : 0≤B := by dsimp [B]; positivity
  have hq : 0≤q := by dsimp [q]; positivity
  have hc : 0 ≤ r*‖c‖ := by positivity
  have hbase : 0≤Real.pi*Real.sqrt d+‖z‖ := by positivity
  have habs := mul_le_mul_of_nonneg_right hl (show 0≤2*B*(r*‖c‖) from by positivity)
  dsimp [ε,D,q,B,c,terminalTransportConstant] at habs ⊢
  nlinarith [mul_nonneg hq hbase]

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

end LogConcaveSampling

end

end

end

end OAI
end

section
-- module Solutions.OAIQ048_LC.LogConcave_Sampling_TensorGrad
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
open scoped Classical BigOperators NNReal RealInnerProductSpace

lemma productPointEquiv_fst_norm_le {d e : ℕ} (y : Point (d+e)) :
    ‖(productPointEquiv d e y).1‖≤‖y‖ := by
  nlinarith [productPointEquiv_norm_sq y,sq_nonneg ‖(productPointEquiv d e y).2‖,
    norm_nonneg y,norm_nonneg (productPointEquiv d e y).1]
lemma productPointEquiv_snd_norm_le {d e : ℕ} (y : Point (d+e)) :
    ‖(productPointEquiv d e y).2‖≤‖y‖ := by
  nlinarith [productPointEquiv_norm_sq y,sq_nonneg ‖(productPointEquiv d e y).1‖,
    norm_nonneg y,norm_nonneg (productPointEquiv d e y).2]

end LogConcaveSampling

end

end

end

end OAI
end

section
-- module Solutions.OAIQ048_LC.LogConcave_Complexity_CenteringStateBudgetNonneg
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
namespace LogConcaveSampling
open Set MeasureTheory TensorEnergy Quadrature
open scoped Classical BigOperators NNReal RealInnerProductSpace

lemma centeringStateBudget_nonneg (n : ℕ) : 0 ≤ centeringStateBudget n :=
  iterEnergyBudget_nonneg harmonicGradientBound.2 _ _ (fun _ => by norm_num) n 0

lemma centeringMeanBudget_nonneg (n : ℕ) : 0 ≤ centeringMeanBudget n :=
  iterEnergyBudget_nonneg harmonicGradientBound.2 _ _ (fun _ => sq_nonneg _) n 0

end LogConcaveSampling

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

lemma correction_lipschitz (w : I → I → ℝ) (φ : I → E → E) {A K : ℝ≥0}
    (hw : ∀i,∑j,|w i j|≤A) (hφ : ∀i,LipschitzWith K (φ i)) :
    LipschitzWith (A*K) (correction w φ) := by
  classical
  apply LipschitzWith.of_dist_le_mul
  intro z v
  apply (dist_pi_le_iff (by positivity)).mpr
  intro i
  simp only [correction,dist_eq_norm,←Finset.sum_sub_distrib,←smul_sub]
  calc
    _ ≤ ∑j,‖w i j • (φ j (z j)-φ j (v j))‖ := norm_sum_le _ _
    _ ≤ ∑j,|w i j| *((K:ℝ)*dist z v) := by
      apply Finset.sum_le_sum
      intro j _
      rw [norm_smul,Real.norm_eq_abs]
      apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
      simpa only [dist_eq_norm] using ((hφ j).dist_le_mul (z j) (v j)).trans
        (mul_le_mul_of_nonneg_left (dist_le_pi_dist z v j) (by positivity))
    _ = (∑j,|w i j|)*((K:ℝ)*dist z v) := by rw [Finset.sum_mul]
    _ ≤ (A:ℝ)*((K:ℝ)*dist z v) := mul_le_mul_of_nonneg_right (hw i) (by positivity)
    _ = _ := by simp only [NNReal.coe_mul,dist_eq_norm]; ring

theorem nodes_lipschitz (w : I → I → ℝ) (φ : I → E → E) (a : X → I → E)
    {A K B : ℝ≥0} (hw : ∀i,∑j,|w i j|≤A) (hφ : ∀i,LipschitzWith K (φ i))
    (ha : LipschitzWith B a) (hq : (A*K:ℝ≥0)≤1/2) (n : ℕ) :
    LipschitzWith (2*B) (nodes w φ a n) := by
  induction n with
  | zero => exact ha.weaken (by nlinarith)
  | succ n ih =>
    change LipschitzWith (2*B) (fun x => a x+correction w φ (nodes w φ a n x))
    apply (ha.add ((correction_lipschitz w φ hw hφ).comp ih)).weaken
    nlinarith

theorem nodes_correction_lipschitz (w : I → I → ℝ) (φ : I → E → E) (a : X → I → E)
    {A K B : ℝ≥0} (hw : ∀i,∑j,|w i j|≤A) (hφ : ∀i,LipschitzWith K (φ i))
    (ha : LipschitzWith B a) (hq : (A*K:ℝ≥0)≤1/2) (n : ℕ) :
    LipschitzWith (A*K*(2*B)) (fun x => nodes w φ a (n+1) x-a x) := by
  convert (correction_lipschitz w φ hw hφ).comp (nodes_lipschitz w φ a hw hφ ha hq n) using 1
  all_goals try with_reducible_and_instances rfl
  funext x
  simp only [nodes,step,add_sub_cancel_left,Function.comp_apply]
end LogConcaveSampling.FinitePicard

end

end

end

end OAI
end

section
-- module Solutions.OAIQ048_LC.LogConcave_Numerics_LogMeshLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
namespace LogConcaveSampling.Quadrature
open Real

lemma logMeshCount_bound {T h : ℝ} (hT0 : 0<T) (hT1 : T<1) (hh : 0<h) :
    (logMeshCount T h:ℝ)<logMeshLength T/h+1 :=
  Nat.ceil_lt_add_one (le_of_lt (div_pos (logMeshLength_pos hT0 hT1) hh))

lemma logMeshStep_le {T h : ℝ} (hT0 : 0<T) (hT1 : T<1) (hh : 0<h) :
    logMeshStep T h≤h := by
  have hN : (0:ℝ)<logMeshCount T h := by exact_mod_cast logMeshCount_pos hT0 hT1 hh
  apply (div_le_iff₀ hN).mpr
  have he := (div_le_iff₀ hh).mp (Nat.le_ceil (logMeshLength T/h))
  change logMeshLength T≤(logMeshCount T h:ℝ)*h at he
  nlinarith

lemma logMeshStep_lower {T h : ℝ} (hT0 : 0<T) (hT1 : T<1) (hh : 0<h)
    (hL : h≤logMeshLength T) : h/2≤logMeshStep T h := by
  have hN : (0:ℝ)<logMeshCount T h := by exact_mod_cast logMeshCount_pos hT0 hT1 hh
  have he : (logMeshCount T h:ℝ)<(logMeshLength T+h)/h := by
    simpa only [add_div,div_self (ne_of_gt hh)] using logMeshCount_bound hT0 hT1 hh
  have hN' := (lt_div_iff₀ hh).mp he
  apply (le_div_iff₀ hN).mpr
  nlinarith

lemma logMeshCell_lower {T h : ℝ} (hT0 : 0<T) (hT1 : T<1) (hh : 0<h)
    (hL : h≤logMeshLength T) (hsmall : h≤Real.log 2) (j : ℕ) :
    h/4*(1-logMeshNode T h j)≤logMeshNode T h (j+1)-logMeshNode T h j := by
  have hs0 := logMeshStep_pos hT0 hT1 hh
  have hs := logMeshStep_le hT0 hT1 hh
  have hs' := logMeshStep_lower hT0 hT1 hh hL
  have he : Real.exp (logMeshStep T h)≤2 := by
    simpa only [Real.exp_log (by norm_num : (0:ℝ)<2)] using Real.exp_le_exp.mpr (hs.trans hsmall)
  have he' : (1:ℝ)/2≤Real.exp (-logMeshStep T h) := by
    rw [Real.exp_neg]
    simpa only [one_div] using (one_div_le_one_div_of_le (Real.exp_pos _) he)
  have hw : logMeshStep T h*Real.exp (-logMeshStep T h)≤1-Real.exp (-logMeshStep T h) := by
    have hx := mul_le_mul_of_nonneg_right (Real.add_one_le_exp (logMeshStep T h))
      (Real.exp_pos (-logMeshStep T h)).le
    rw [←Real.exp_add,add_neg_cancel,Real.exp_zero] at hx
    nlinarith
  have hb : h/4≤1-Real.exp (-logMeshStep T h) := by
    have hx := mul_le_mul_of_nonneg_left he' hs0.le
    nlinarith
  have hp : 0≤1-logMeshNode T h j := by
    simpa only [logMeshNode,sub_sub_cancel] using (Real.exp_pos (-(j:ℝ)*logMeshStep T h)).le
  rw [logMeshNode_sub,mul_comm (h/4)]
  exact mul_le_mul_of_nonneg_left hb hp
end LogConcaveSampling.Quadrature

end

end

end

end OAI
end

section
-- module Solutions.OAIQ048_LC.LogConcave_Complexity_HarmonicCorrectionBudget
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

lemma harmonicCorrectionBudget_nonneg (n : ℕ) : 0≤harmonicCorrectionBudget n :=
  iterEnergyBudget_nonneg harmonicGradientBound.2 _ _ (fun _ => sq_nonneg _) n 0

lemma harmonicMeanBudget_nonneg (n : ℕ) : 0≤harmonicMeanBudget n :=
  iterEnergyBudget_nonneg harmonicGradientBound.2 _ _ (fun _ => sq_nonneg _) n 0

end LogConcaveSampling

end

end

end

end OAI
end

section
-- module Solutions.OAIQ048_LC.LogConcave_JetEstimates_LogDegree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
namespace LogConcaveSampling
open scoped Classical BigOperators NNReal ENNReal

namespace TensorSum
variable {S : Type} [Fintype S]

omit [Fintype S] in
lemma momentBudget_polylog (A : TensorSum S) (d j : ℕ) (p : ℝ≥0∞) :
    (A.momentBudget d j p).toReal≤
      A.logCoefficient j p*(1+Real.log ((d:ℝ)+1))^(A.logDegree j) := by
  have hl : 0≤Real.log ((d:ℝ)+1) := Real.log_nonneg (by linarith [Nat.cast_nonneg (α:=ℝ) d])
  have ht : 1≤1+Real.log ((d:ℝ)+1) := by linarith
  have hf (i : A.index) :
      ENNReal.ofReal (polynomialBudget (A.term i).coefficient)*
      ((4*((A.term i).atom.expression.profileConstant:ℝ≥0∞))*
        ENNReal.ofReal (p.toReal+j+Real.log ((d:ℝ)+1)+1))^
        ((A.term i).atom.expression.profileConstant*(j+1))≠⊤ := by
    apply ne_of_lt
    exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top
      (ENNReal.pow_lt_top (ENNReal.mul_lt_top
        (ENNReal.mul_lt_top (by norm_num) (ENNReal.natCast_lt_top _)) ENNReal.ofReal_lt_top))
  rw [momentBudget,ENNReal.toReal_sum (fun i _ => hf i),logCoefficient,Finset.sum_mul]
  apply Finset.sum_le_sum
  intro i _
  simp only [ENNReal.toReal_mul,ENNReal.toReal_pow,ENNReal.toReal_ofNat,
    ENNReal.toReal_natCast,ENNReal.toReal_ofReal (polynomialBudget_nonneg _),
    ENNReal.toReal_ofReal (by positivity : 0≤p.toReal+(j:ℝ)+Real.log ((d:ℝ)+1)+1)]
  let c := (A.term i).atom.expression.profileConstant
  let n := c*(j+1)
  have hb : 4*(c:ℝ)*(p.toReal+j+Real.log ((d:ℝ)+1)+1)≤
      (4*(c:ℝ)*(p.toReal+j+1))*(1+Real.log ((d:ℝ)+1)) := by
    have hh : 0≤(p.toReal+(j:ℝ))*Real.log ((d:ℝ)+1) := by positivity
    have hh' := mul_nonneg (by positivity : 0≤4*(c:ℝ)) hh
    nlinarith
  have hn : n≤A.logDegree j := by
    dsimp [n,c,logDegree]
    exact Finset.single_le_sum (f:=fun i : A.index => (A.term i).atom.expression.profileConstant*(j+1)) (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
  calc
    _ ≤ polynomialBudget (A.term i).coefficient*
        ((4*(c:ℝ)*(p.toReal+j+1))*(1+Real.log ((d:ℝ)+1)))^n :=
      mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) hb _) (polynomialBudget_nonneg _)
    _ = polynomialBudget (A.term i).coefficient*(4*(c:ℝ)*(p.toReal+j+1))^n*
        (1+Real.log ((d:ℝ)+1))^n := by rw [mul_pow]; ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (pow_le_pow_right₀ ht hn) (by
      exact mul_nonneg (polynomialBudget_nonneg _) (by positivity))
end TensorSum
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

lemma probabilityConstantPath_lipschitz {d : ℕ} (T h : ℝ) (n : ℕ) :
    LipschitzWith 1 (fun y : Point d => fun _ : ProbabilityNode T h n => y) := by
  apply LipschitzWith.of_dist_le_mul
  intro y z
  apply (dist_pi_le_iff (by positivity)).mpr
  intro i
  simp

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

theorem harmonicPicard_lipschitz (n : ℕ) (hn : 0<n) :
    ∃A : ℝ≥0,∀{d : ℕ} {F : Point d → ℝ} {lam : ℝ≥0},
      Primitive F lam → ∀(x : Point d) {r ρ z : ℝ},0 ≤ r →
        (lam:ℝ)*r^2≤1/2 → 0≤ρ → ρ<1 → 0≤z → z≤1 →
        A*probabilityMeanLipschitz lam r≤1/2 → ∀N : ℕ,
      LipschitzWith 4 (harmonicPicard F x r ρ z n N) ∧
      LipschitzWith (4*(A*probabilityMeanLipschitz lam r))
        (fun p => harmonicPicard F x r ρ z n (N+1) p-harmonicFree n z p) := by
  obtain ⟨A,hA⟩ := harmonicWeight_budget n hn
  refine ⟨A,?_⟩
  intro d F lam hF x r ρ z hr hl hρ0 hρ1 hz hz1 hq N
  have hφ := harmonicMeanVelocity_lipschitz hF x hr hl hρ0 hρ1
  constructor
  · simpa only [harmonicPicard,show (2:ℝ≥0)*2=4 by norm_num] using
      nodes_lipschitz (harmonicWeight n z) (fun _ => harmonicMeanVelocity F x r ρ)
        (harmonicFree n z) (hA z hz hz1) (fun _ => hφ) (harmonicFree_lipschitz n z) hq N
  · have hh := nodes_correction_lipschitz (harmonicWeight n z) (fun _ => harmonicMeanVelocity F x r ρ)
        (harmonicFree n z) (hA z hz hz1) (fun _ => hφ) (harmonicFree_lipschitz n z) hq N
    convert hh using 1 <;> first | rfl | ring

end LogConcaveSampling

end

end

end

end OAI
end

section
-- module Solutions.OAIQ048_LC.LogConcave_Sampling_ProbabilityInitialRms
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
open scoped Classical BigOperators NNReal

lemma probabilityInitialRms_nonneg {d : ℕ} (F : Point d → ℝ) (x : Point d)
    (lam : ℝ≥0) (r : ℝ) : 0≤probabilityInitialRms F x lam r := Real.sqrt_nonneg _

end LogConcaveSampling

end

end

end

end OAI
end

section
-- module Solutions.OAIQ048_LC.LogConcave_Numerics_ReanchorWeight
attribute [-instance] _root_.OAI.LogConcaveSampling.LowerBound.couplingLaw_probability _root_.OAI.LogConcaveSampling.LowerBound.remainingHaar_probability _root_.OAI.LogConcaveSampling.LowerBound.roundRandomLaw_probability _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_invInvariant _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_isHaar _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_probability _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_rightInvariant _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_compactSpace _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_measurableInv _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_measurableMul _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_secondCountable _root_.OAI.LogConcaveSampling.MeanTree.instIsProbabilityMeasureRowTapeRowLaw _root_.OAI.LogConcaveSampling.OracleCompiler.topSeedLaw_probability _root_.OAI.LogConcaveSampling.noiseKernel_markov
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
namespace LogConcaveSampling.FinitePicard
open MeasureTheory
open scoped BigOperators

variable {I E Ω : Type*} [Fintype I] [NormedAddCommGroup E] [NormedSpace ℝ E]

lemma reanchorWeight_budget (w : I → I → ℝ) {A : ℝ}
    (hw : ∀i,∑j,|w i j|≤A) (s i : I) : ∑j,|reanchorWeight w s i j|≤2*A := by
  calc
    _ ≤ ∑j,(|w i j|+|w s j|) := Finset.sum_le_sum (fun j _ => abs_sub _ _)
    _ = (∑j,|w i j|)+(∑j,|w s j|) := Finset.sum_add_distrib
    _ ≤ 2*A := by linarith [hw i,hw s]

end LogConcaveSampling.FinitePicard

end

end

section

noncomputable section
namespace LogConcaveSampling
open Set MeasureTheory ProbabilityTheory FinitePicard
open scoped Classical BigOperators NNReal

lemma probabilityAnchored_lipschitz (n : ℕ) (hn : 0<n) :
    ∃A : ℝ≥0,∀{d : ℕ} {F : Point d → ℝ} {lam : ℝ≥0},
      Primitive F lam → ∀(x : Point d) {r T h : ℝ},0 ≤ r →
        (lam:ℝ)*r^2≤1/2 → 0<T → T<1 → 0<h →
        A*probabilityMeanLipschitz lam r≤1/2 → ∀N : ℕ,∀s : ProbabilityNode T h n,
      LipschitzWith 2 (probabilityAnchoredPicard F x r T h n N s) ∧
      LipschitzWith (2*(A*probabilityMeanLipschitz lam r))
        (fun y => probabilityAnchoredPicard F x r T h n (N+1) s y-(fun _ => y)) := by
  obtain ⟨A,hA,hA'⟩ := probabilityWeight_budget n hn
  refine ⟨⟨2*A,by positivity⟩,?_⟩
  intro d F lam hF x r T h hr hl hT0 hT1 hh hq N s
  have hφ (j : ProbabilityNode T h n) := probabilityMeanVelocity_lipschitz hF x hr hl
    (probabilityNodeTime_mem hT0 hT1 hh hn j).1
    ((probabilityNodeTime_mem hT0 hT1 hh hn j).2.trans_lt hT1)
  have hw := reanchorWeight_budget (probabilityWeight T h n) (hA' hT0 hT1 hh) s
  constructor
  · simpa only [probabilityAnchoredPicard,mul_one] using
      nodes_lipschitz (A:=⟨2*A,by positivity⟩) _ _ (fun y : Point d => fun _ => y) hw hφ
        (probabilityConstantPath_lipschitz T h n) hq N
  · simpa only [probabilityAnchoredPicard,mul_one,one_mul,mul_comm] using
      nodes_correction_lipschitz (A:=⟨2*A,by positivity⟩) _ _ (fun y : Point d => fun _ => y) hw hφ
        (probabilityConstantPath_lipschitz T h n) hq N

end LogConcaveSampling

end

end

end

end OAI
end

section
-- module Solutions.OAIQ048_LC.LogConcave_Sampling_CenteringJointLaw
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
open scoped NNReal

lemma centering_joint_law {d : ℕ} {F : Point d → ℝ} {lam : ℝ≥0}
    (hF : Primitive F lam) (x : Point d) {r T : ℝ} (hr : 0 ≤ r)
    (hl : (lam:ℝ)*r^2≤1/2) (hT0 : 0≤T) (hT1 : T<1) :
    (gibbs (centeringPotential F x r T)).map (productPointEquiv d d)=
      (interpolationLaw F x r T).prod (stdGaussian (Point d)) := by
  rw [interpolationLaw_eq_gibbs hF x hr (by linarith) (by nlinarith)]
  exact (productPotential_gibbs
    (interpolationPotential_smooth hF x hr hl hT0 hT1).continuous
      (gaussianPotential_polySmooth d).smooth.continuous).trans
    (by rw [gaussianPotential_gibbs])

lemma centering_position_law {d : ℕ} {F : Point d → ℝ} {lam : ℝ≥0}
    (hF : Primitive F lam) (x : Point d) {r T : ℝ} (hr : 0 ≤ r)
    (hl : (lam:ℝ)*r^2≤1/2) (hT0 : 0≤T) (hT1 : T<1) :
    (gibbs (centeringPotential F x r T)).map (fun y => (productPointEquiv d d y).1)=
      interpolationLaw F x r T := by
  change (gibbs (centeringPotential F x r T)).map (Prod.fst ∘ (productPointEquiv d d))=_
  rw [←Measure.map_map measurable_fst (productPointEquiv d d).continuous.measurable,
    centering_joint_law hF x hr hl hT0 hT1]
  simp only [Measure.map_fst_prod,measure_univ,one_smul]

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

theorem kernelActionPicard_lipschitz (n : ℕ) (hn : 0<n) :
    ∃A B : ℝ≥0,∀{d : ℕ} {F : Point d → ℝ} {lam : ℝ≥0},
      Primitive F lam → ∀(x : Point d) {r T h ψ : ℝ},0 ≤ r →
        (lam:ℝ)*r^2≤1/2 → 0<T → T<1 → 0<h → 0<ψ →
        ∀m : ℕ,ψ*m≤1 →
        A*probabilityMeanLipschitz lam r≤1/2 →
        B*probabilityMeanLipschitz lam r≤1/2 →
        ∀N : ℕ,∀s e : ProbabilityNode T h n,
      LipschitzWith ((∑i : Fin (m+1),‖derivativeWeight (angleNodes m) i/ψ‖₊)*
        (16*(A*probabilityMeanLipschitz lam r)))
        (kernelActionPicard F x r T h ψ n m N s e) := by
  obtain ⟨A,hA⟩ := probabilityAnchored_lipschitz n hn
  obtain ⟨B,hB⟩ := harmonicPicard_lipschitz n hn
  refine ⟨A,B,?_⟩
  intro d F lam hF x r T h ψ hr hl hT0 hT1 hh hψ m hψm hq hq' N s e
  have htime := probabilityNodeTime_mem hT0 hT1 hh hn s
  have hb : LipschitzWith 2 (fun p : Point d × Point d =>
      (probabilityAnchoredPicard F x r T h n N e p.1 s,p.2)) := by
    have h := (((LipschitzWith.eval s).comp (hA hF x hr hl hT0 hT1 hh hq N e).1).comp
      (LipschitzWith.prod_fst (α:=Point d) (β:=Point d))).prodMk
      (LipschitzWith.prod_snd (α:=Point d) (β:=Point d))
    convert h using 1 <;> first | rfl | norm_num
  have hc : LipschitzWith (2*(A*probabilityMeanLipschitz lam r))
      (fun w => probabilityAnchoredPicard F x r T h n (N+1) s w e-w) := by
    have h := (LipschitzWith.eval e).comp (hA hF x hr hl hT0 hT1 hh hq N s).2
    convert h using 1 <;> first | rfl | simp only [one_mul]
  apply finite_weighted_lipschitz
  intro i
  have hz0 : 0≤ψ*angleNodes m i := mul_nonneg hψ.le (Nat.cast_nonneg _)
  have hz1 : ψ*angleNodes m i≤1 := by
    apply le_trans _ hψm
    apply mul_le_mul_of_nonneg_left _ hψ.le
    change (i:ℝ)≤(m:ℝ)
    exact_mod_cast (Nat.le_of_lt_succ i.2)
  have hw := ((LipschitzWith.eval (Fin.last n)).comp
    (hB hF x hr hl htime.1 (htime.2.trans_lt hT1) hz0 hz1 hq' N).1).comp hb
  have h := hc.comp hw
  convert h using 1 <;> first | rfl | ring

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
-- module Solutions.OAIQ048_LC.LogConcave_Complexity_KernelActionRmsBudget
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
open Quadrature
open scoped Classical BigOperators NNReal

theorem kernelQuadraturePicard_lipschitz (n : ℕ) (hn : 0<n) :
    ∃A B : ℝ≥0,∀{d : ℕ} {F : Point d → ℝ} {lam : ℝ≥0},
      Primitive F lam → ∀(x : Point d) {r T h ψ : ℝ},0 ≤ r →
        (lam:ℝ)*r^2≤1/2 → 0<T → T<1 → 0<h → 0<ψ →
        ∀m : ℕ,ψ*m≤1 →
        A*probabilityMeanLipschitz lam r≤1/2 →
        B*probabilityMeanLipschitz lam r≤1/2 →
        ∀N : ℕ,∀e : ProbabilityNode T h n,∀w : ProbabilityNode T h n → ℝ,
      LipschitzWith ((∑s,‖w s‖₊)*
        ((∑i : Fin (m+1),‖derivativeWeight (angleNodes m) i/ψ‖₊)*
          (16*(A*probabilityMeanLipschitz lam r))))
        (kernelQuadraturePicard F x r T h ψ n m N e w) := by
  obtain ⟨A,B,hAB⟩ := kernelActionPicard_lipschitz n hn
  refine ⟨A,B,?_⟩
  intro d F lam hF x r T h ψ hr hl hT0 hT1 hh hψ m hψm hq hq' N e w
  exact finite_weighted_lipschitz w
    (fun s => kernelActionPicard F x r T h ψ n m N s e)
    (fun s => hAB hF x hr hl hT0 hT1 hh hψ m hψm hq hq' N s e)
end LogConcaveSampling

end

end

end

end OAI
end

section
-- module Solutions.OAIQ048_LC.LogConcave_Numerics_BasisDerivative
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
namespace LogConcaveSampling.Quadrature
open Set MeasureTheory Polynomial
open scoped BigOperators

variable {I E : Type*} [Fintype I] [DecidableEq I]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

lemma basisDerivative_continuous (u : I → ℝ) (i : I) : Continuous (basisDerivative u i) :=
  Polynomial.continuous _

lemma exists_basisDerivative_budget (u : I → ℝ) :
    ∃C : ℝ,1≤C ∧ ∀t∈Icc (0:ℝ) 1,∑i,|basisDerivative u i t|≤C := by
  have hc : Continuous (fun t => ∑i,|basisDerivative u i t|) :=
    continuous_finsetSum _ (fun i _ => (basisDerivative_continuous u i).abs)
  obtain ⟨C,hC⟩ := isCompact_Icc.exists_bound_of_continuousOn hc.continuousOn
  refine ⟨max C 1,le_max_right _ _,fun t ht => ?_⟩
  have hn : 0≤∑i,|basisDerivative u i t| := Finset.sum_nonneg (fun _ _ => abs_nonneg _)
  have hh : (∑i,|basisDerivative u i t|)≤C := by
    simpa only [Real.norm_eq_abs,abs_of_nonneg hn] using hC t ht
  exact hh.trans (le_max_left _ _)
end LogConcaveSampling.Quadrature

end

end

end OAI
end

section
-- module Solutions.OAIQ048_LC.LogConcave_Complexity_TerminalDerivativeBudget
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
namespace LogConcaveSampling
open Set MeasureTheory ProbabilityTheory Quadrature
open scoped Classical BigOperators NNReal

lemma terminalDerivativeBudget_nonneg (n d : ℕ) (lam : ℝ≥0) (r : ℝ) :
    0≤terminalDerivativeBudget n d lam r := by
  unfold terminalDerivativeBudget
  have h : 0 ≤ r*((lam:ℝ)*r) := by nlinarith [sq_nonneg r,lam.coe_nonneg]
  positivity

end LogConcaveSampling

end

end

end OAI
end

section
-- module Solutions.OAIQ048_LC.LogConcave_Numerics_OrdinaryDerivativeWeight
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
namespace LogConcaveSampling.Quadrature
open Set MeasureTheory Filter
open scoped BigOperators

variable {I E : Type*} [Fintype I] [DecidableEq I]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

lemma ordinaryDerivativeWeight_integrand_continuousOn (u : I → ℝ) (a b : ℝ) (i : I)
    (ha : 0<a) (hab : a≤b) :
    ContinuousOn (fun t => (b-a)⁻¹*t⁻¹*basisDerivative u i ((t-a)/(b-a))) (uIcc a b) := by
  rw [uIcc_of_le hab]
  exact (continuousOn_const.mul (continuousOn_id.inv₀
    (fun t ht => ne_of_gt (ha.trans_le ht.1)))).mul
      ((basisDerivative_continuous u i).comp
        ((continuous_id.sub continuous_const).div_const _)).continuousOn

end LogConcaveSampling.Quadrature

end

end

section

noncomputable section
namespace LogConcaveSampling
open Set MeasureTheory Quadrature
open scoped Classical BigOperators

lemma logMeshNode_pos {T h : ℝ} (hT0 : 0<T) (hT1 : T<1) (hh : 0<h)
    {j : ℕ} (hj : 0<j) : 0<logMeshNode T h j := by
  simpa only [logMeshNode_zero] using logMeshNode_strictMono hT0 hT1 hh hj

lemma logMeshFirst_lower {T h : ℝ} (hT0 : 0<T) (hT1 : T<1) (hh : 0<h)
    (hL : h≤logMeshLength T) (hs : h≤Real.log 2) : h/4≤logMeshNode T h 1 := by
  simpa only [logMeshNode_zero,zero_add,sub_zero,mul_one] using
    logMeshCell_lower hT0 hT1 hh hL hs 0

end LogConcaveSampling

end

end

end OAI
end

section
-- module Solutions.OAIQ048_LC.LogConcave_Complexity_KernelAnalyticBudget
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
namespace LogConcaveSampling
open Set MeasureTheory ProbabilityTheory Quadrature
open scoped Classical BigOperators NNReal

lemma terminalDerivativeBudget_polylog (n d : ℕ) (lam : ℝ≥0) (r : ℝ) :
    terminalDerivativeBudget n d lam r≤(lam:ℝ)*r^2*
      (Real.exp (Real.pi^2/4)*(TensorSum.terminalQ n).val.logCoefficient 0 2)*
      (1+Real.log ((d:ℝ)+1))^((TensorSum.terminalQ n).val.logDegree 0) := by
  have he := mul_le_mul_of_nonneg_left
    ((TensorSum.terminalQ n).val.momentBudget_polylog d 0 2)
    (show 0 ≤ r*((lam:ℝ)*r)*Real.exp (Real.pi^2/4) by
      have hh : 0 ≤ r*((lam:ℝ)*r) := by nlinarith [sq_nonneg r,lam.coe_nonneg]
      positivity)
  convert! he using 1
  all_goals try with_reducible_and_instances rfl
  ring

end LogConcaveSampling

end

end

end OAI
end

section
-- module Solutions.OAIQ048_LC.LogConcave_Numerics_CenteringVelocityPicard
attribute [-instance] _root_.OAI.LogConcaveSampling.LowerBound.couplingLaw_probability _root_.OAI.LogConcaveSampling.LowerBound.remainingHaar_probability _root_.OAI.LogConcaveSampling.LowerBound.roundRandomLaw_probability _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_invInvariant _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_isHaar _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_probability _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_rightInvariant _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_compactSpace _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_measurableInv _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_measurableMul _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_secondCountable _root_.OAI.LogConcaveSampling.MeanTree.instIsProbabilityMeasureRowTapeRowLaw _root_.OAI.LogConcaveSampling.OracleCompiler.topSeedLaw_probability _root_.OAI.LogConcaveSampling.noiseKernel_markov
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
namespace LogConcaveSampling
open Set MeasureTheory ProbabilityTheory Quadrature
open scoped Classical BigOperators NNReal

lemma velocity_scale_cancel {r s : ℝ} (hr : 0 < r) (hs : 0 < s) (lam : ℝ≥0) :
    (‖-(r*s)⁻¹‖₊ : ℝ)*(probabilityMeanLipschitz lam r:ℝ)=
      (Real.pi^2/2)*((lam:ℝ)*r/s) := by
  change |-(r*s)⁻¹| *((Real.pi^2/2)*(lam:ℝ)*r^2)=_
  simp only [abs_neg,abs_inv,abs_mul,abs_of_pos hr,abs_of_pos hs]
  field_simp

theorem centeringVelocityPicard_lipschitz (n : ℕ) :
    ∃A B : ℝ≥0,∀{d : ℕ} {F : Point d → ℝ} {lam : ℝ≥0},
      ∀hF : Primitive F lam,∀(x : Point d) {r T h ψ s : ℝ},∀hr : 0 < r,
        (lam:ℝ)*r^2≤1/2 → ∀hT0 : 0<T,T<1 → 0<h → 0<ψ → 0 < s →
        ∀m : ℕ,ψ*m≤1 →
        A*probabilityMeanLipschitz lam r≤1/2 →
        B*probabilityMeanLipschitz lam r≤1/2 →
        ∀N : ℕ,∀e : ProbabilityNode T h (n+1),
      LipschitzWith
        (‖-(r*s)⁻¹‖₊*((∑i,‖terminalQuadratureWeight T h n i‖₊)*
          ((∑i : Fin (m+1),‖derivativeWeight (angleNodes m) i/ψ‖₊)*
            (16*(A*probabilityMeanLipschitz lam r))))+
          ‖s⁻¹‖₊*⟨(Real.pi^2/2)*T*((lam:ℝ)*r),by positivity⟩)
        (centeringVelocityPicard F x r T h ψ s n m N e) := by
  obtain ⟨A,B,hAB⟩ := kernelQuadraturePicard_lipschitz (n+1) (by omega)
  refine ⟨A,B,?_⟩
  intro d F lam hF x r T h ψ s hr hl hT0 hT1 hh hψ hs m hψm hq hq' N e
  have hfirst := (lipschitzWith_smul (-(r*s)⁻¹)).comp
    (hAB hF x hr.le hl hT0 hT1 hh hψ m hψm hq hq' N e (terminalQuadratureWeight T h n))
  have hmean : LipschitzWith ⟨(Real.pi^2/2)*T*((lam:ℝ)*r),by positivity⟩
      (fun y => conditionalFieldMean F x r T y-primitiveExpectedField F x r) := by
    apply LipschitzWith.of_dist_le_mul
    intro y z
    simpa only [dist_sub_right] using
      (conditionalFieldMean_lipschitz hF x hr.le hl hT0.le hT1).dist_le_mul y z
  have hf : LipschitzWith 1 (Prod.fst : Point d × Point d → Point d) := LipschitzWith.prod_fst
  have hsecond : LipschitzWith (‖s⁻¹‖₊*⟨(Real.pi^2/2)*T*((lam:ℝ)*r),by positivity⟩)
      (fun p : Point d × Point d => s⁻¹ •
        (conditionalFieldMean F x r T p.1-primitiveExpectedField F x r)) := by
    convert! (lipschitzWith_smul s⁻¹).comp (hmean.comp hf) using 1
    all_goals try with_reducible_and_instances rfl
    apply Subtype.ext
    change ‖s⁻¹‖*((Real.pi^2/2)*T*((lam:ℝ)*r))=
      ‖s⁻¹‖*(((Real.pi^2/2)*T*((lam:ℝ)*r))*1)
    ring
  exact (hfirst.prodMk hsecond).weaken
    (max_le (le_add_of_nonneg_right (by positivity))
      (le_add_of_nonneg_left (by positivity)))

lemma centeringVelocityPicard_lipschitz_coefficient {r s T h ψ : ℝ}
    (hr : 0 < r) (hs : 0 < s) (hψ : 0<ψ) (hT0 : 0<T) (hT1 : T<1)
    (lam A : ℝ≥0) (n m : ℕ) :
    ((‖-(r*s)⁻¹‖₊*((∑i,‖terminalQuadratureWeight T h n i‖₊)*
          ((∑i : Fin (m+1),‖derivativeWeight (angleNodes m) i/ψ‖₊)*
            (16*(A*probabilityMeanLipschitz lam r))))+
          ‖s⁻¹‖₊*⟨(Real.pi^2/2)*T*((lam:ℝ)*r),by positivity⟩ : ℝ≥0):ℝ)≤
      (Real.pi^2/2)*((lam:ℝ)*r/s)*
        (16*A*(∑i,|terminalQuadratureWeight T h n i|)*
          ((∑i : Fin (m+1),|derivativeWeight (angleNodes m) i|)/ψ)+1) := by
  have hc := velocity_scale_cancel hr hs lam
  simp only [NNReal.coe_add,NNReal.coe_mul,NNReal.coe_ofNat,NNReal.coe_sum]
  change _ + (‖s⁻¹‖*(Real.pi^2/2*T*((lam:ℝ)*r)))≤_
  simp only [coe_nnnorm,Real.norm_eq_abs,abs_div,abs_of_pos hψ,abs_inv,abs_of_pos hs,
    ←Finset.sum_div] at *
  have he : s⁻¹*((Real.pi^2/2)*T*((lam:ℝ)*r))≤
      (Real.pi^2/2)*((lam:ℝ)*r/s) := by
    have hh := mul_le_mul_of_nonneg_right hT1.le
      (show 0≤(Real.pi^2/2)*((lam:ℝ)*r/s) by positivity)
    convert! hh using 1 <;> ring
  calc
    _ = (16*A*(∑i,|terminalQuadratureWeight T h n i|)*
        ((∑i : Fin (m+1),|derivativeWeight (angleNodes m) i|)/ψ))*
          (‖-(r*s)⁻¹‖*(probabilityMeanLipschitz lam r:ℝ))+
        s⁻¹*((Real.pi^2/2)*T*((lam:ℝ)*r)) := by
      simp only [Real.norm_eq_abs]; ring
    _ ≤ (16*A*(∑i,|terminalQuadratureWeight T h n i|)*
        ((∑i : Fin (m+1),|derivativeWeight (angleNodes m) i|)/ψ))*
          ((Real.pi^2/2)*((lam:ℝ)*r/s))+
        (Real.pi^2/2)*((lam:ℝ)*r/s) := by rw [show ‖-(r*s)⁻¹‖*(probabilityMeanLipschitz lam r:ℝ)=(Real.pi^2/2)*((lam:ℝ)*r/s) from hc]; exact add_le_add le_rfl he
    _ = _ := by ring
end LogConcaveSampling

end

end

end OAI
end

section
-- module Solutions.OAIQ048_LC.LogConcave_Sampling_CenteringVelocityJoint
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

lemma productPointEquiv_lipschitz_one (d e : ℕ) :
    LipschitzWith 1 (productPointEquiv d e) := by
  apply LipschitzWith.of_dist_le_mul
  intro y z
  simp only [NNReal.coe_one,one_mul,dist_eq_norm,←map_sub]
  rw [Prod.norm_def]
  exact max_le (productPointEquiv_fst_norm_le _) (productPointEquiv_snd_norm_le _)

lemma productPointEquiv_symm_norm_le (d e : ℕ) (p : Point d × Point e) :
    ‖(productPointEquiv d e).symm p‖≤2*‖p‖ := by
  have h := productPointEquiv_norm_sq ((productPointEquiv d e).symm p)
  simp only [ContinuousLinearEquiv.apply_symm_apply] at h
  have h1 : ‖p.1‖≤‖p‖ := norm_fst_le p
  have h2 : ‖p.2‖≤‖p‖ := norm_snd_le p
  have h1' := pow_le_pow_left₀ (norm_nonneg p.1) h1 2
  have h2' := pow_le_pow_left₀ (norm_nonneg p.2) h2 2
  nlinarith [norm_nonneg p,norm_nonneg ((productPointEquiv d e).symm p)]

lemma productPointEquiv_symm_lipschitz_two (d e : ℕ) :
    LipschitzWith 2 (productPointEquiv d e).symm := by
  apply LipschitzWith.of_dist_le_mul
  intro y z
  simpa only [NNReal.coe_ofNat,dist_eq_norm,←map_sub] using
    productPointEquiv_symm_norm_le d e (y-z)

end LogConcaveSampling

end

end

end OAI
end

section
-- module Solutions.OAIQ048_LC.LogConcave_Dynamics_StationaryPath
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
namespace LogConcaveSampling
open Set MeasureTheory Quadrature TensorEnergy
open scoped Classical BigOperators NNReal

namespace StationaryPath
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [MeasurableSpace E]
  {μ : Measure E} {V : E → E} (X : StationaryPath μ V)

lemma measurable_slice (t : ℝ) : Measurable (fun y => X.path y t) :=
  X.measurable.comp (measurable_const.prodMk measurable_id)

end StationaryPath

end LogConcaveSampling

end

end

end OAI
end

section
-- module Solutions.OAIQ048_LC.LogConcave_Numerics_CenteringStateQuadratureBudget
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
namespace LogConcaveSampling
open Set MeasureTheory Quadrature TensorEnergy
open scoped Classical BigOperators NNReal

variable {d : ℕ} {F : Point d → ℝ} {lam : ℝ≥0}
  (hF : Primitive F lam) (x : Point d) {r R T s : ℝ}
  (hr : 0 < r) (hlam : 0<lam) (hl : (lam:ℝ)*r^2 ≤ 1/2)
  (hR : 0<R) (hRT : R^2 ≤ 1-T^2) (hT0 : 0 ≤ T) (hT1 : T<1) (hs : 0 < s)
  (X : StationaryPath (gibbs (centeringPotential F x r T))
    (skewLieField (centeringPotential F x r T) (jointSkew (centeringKernel hF x hr hl hT0 hT1) s)))

lemma centeringStateQuadratureBudget_nonneg (n d : ℕ) (lam : ℝ≥0) (r R s : ℝ) :
    0 ≤ centeringStateQuadratureBudget n d lam r R s := by
  unfold centeringStateQuadratureBudget
  positivity [centeringStateBudget_nonneg (n+2)]

end LogConcaveSampling

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

lemma circuitGrowthConstant_pos : 0 < circuitGrowthConstant := by
  unfold circuitGrowthConstant
  positivity [terminalTransportConstant_pos]

lemma probabilityInitialRms_growth {d : ℕ} (F : Point d → ℝ) (x : Point d)
    (lam : ℝ≥0) {r : ℝ} (hr : 0 ≤ r) (hL : (lam:ℝ)*r≤1) :
    probabilityInitialRms F x lam r ≤ circuitGrowthConstant*r*circuitD F x := by
  let C := terminalTransportConstant
  let D := circuitD F x
  have hC : 0<C := terminalTransportConstant_pos
  have hD : 0≤D := circuitD_nonneg F x
  have hdc : ‖primitiveField F x r 0‖≤D := by
    rw [field_zero_eq_gradient]; exact le_add_of_nonneg_left (Real.sqrt_nonneg _)
  have hds : Real.sqrt d≤D := sqrt_le_circuitD F x
  have hL0 : 0≤(lam:ℝ)*r := by positivity
  have ha : r*‖primitiveField F x r 0‖+(lam:ℝ)*r^2*Real.pi*Real.sqrt d ≤ r*(Real.pi+1)*D := by
    have h₁ := mul_le_mul_of_nonneg_left hdc hr
    have h₂ := mul_le_mul_of_nonneg_right hL (show 0 ≤ r*Real.pi*Real.sqrt d by positivity)
    have h₃ := mul_le_mul_of_nonneg_left hds (show 0 ≤ r*Real.pi by positivity)
    nlinarith
  have hb : (lam:ℝ)*r^2*Real.sqrt d ≤ r*D := by
    have h₁ := mul_le_mul_of_nonneg_right hL (show 0 ≤ r*Real.sqrt d by positivity)
    have h₂ := mul_le_mul_of_nonneg_left hds hr
    nlinarith
  have ha' := pow_le_pow_left₀ (show 0 ≤ r*‖primitiveField F x r 0‖+(lam:ℝ)*r^2*Real.pi*Real.sqrt d by positivity) ha 2
  have hb' := pow_le_pow_left₀ (show 0≤(lam:ℝ)*r^2*Real.sqrt d by positivity) hb 2
  have hs := Real.sq_sqrt (show 0≤(d:ℝ) by positivity)
  have hm₁ := mul_le_mul_of_nonneg_left ha' (show 0≤2*C^2 by positivity)
  have hm₂ := mul_le_mul_of_nonneg_left hb' (show 0≤2*C^2 by positivity)
  apply (Real.sqrt_le_iff).mpr
  refine ⟨by exact mul_nonneg (mul_nonneg circuitGrowthConstant_pos.le hr) hD,?_⟩
  change 2*(C*(r*‖primitiveField F x r 0‖+(lam:ℝ)*r^2*Real.pi*Real.sqrt d))^2+
    2*(C*((lam:ℝ)*r^2))^2*d ≤ _
  have hn : 2*C^2*(r*(Real.pi+1)*D)^2+2*C^2*(r*D)^2 ≤
      (circuitGrowthConstant*r*D)^2 := by
    have hp : 1≤Real.pi+1 := by linarith [Real.pi_pos]
    have hmul : r*D ≤ (Real.pi+1)*(r*D) := by
      simpa only [one_mul] using mul_le_mul_of_nonneg_right hp (show 0 ≤ r*D by positivity)
    have h := pow_le_pow_left₀ (by positivity : 0 ≤ r*D) hmul 2
    have hc : 4*C^2 ≤ (8*(C+1))^2 := by nlinarith
    have hh := mul_le_mul_of_nonneg_right hc (sq_nonneg (r*(Real.pi+1)*D))
    dsimp only [circuitGrowthConstant]
    change _ ≤ (8*(C+1)*(Real.pi+1)*r*D)^2
    nlinarith [mul_nonneg (show 0≤2*C^2 by positivity) (sub_nonneg.mpr h)]
  nlinarith [hm₁,hm₂]

lemma conditionalMean_flow_growth {d : ℕ} {F : Point d → ℝ} {lam : ℝ≥0}
    (hF : Primitive F lam) (x : Point d) {r T : ℝ} (hr : 0 ≤ r) (hr1 : r≤1)
    (hl : (lam:ℝ)*r^2≤1/2) (hL : (lam:ℝ)*r≤1) (hT0 : 0≤T) (hT1 : T<1)
    (z : Point d) :
    ‖conditionalFieldMean F x r T (fullProbabilityFlow hF x hr hl T z)‖ ≤
      circuitGrowthConstant*(circuitD F x+‖z‖) := by
  let C := terminalTransportConstant
  let B := Real.pi*Real.sqrt d+‖z‖+‖primitiveField F x r 0‖
  have hC : 0<C := terminalTransportConstant_pos
  have hB : 0≤B := by dsimp [B]; positivity
  have hf := probabilityFlow_initial_displacement hF x hr hl z ⟨hT0,hT1.le⟩
  have hn := norm_le_norm_sub_add (fullProbabilityFlow hF x hr hl T z) z
  have h₁ := mul_le_mul_of_nonneg_right hr1 (norm_nonneg (primitiveField F x r 0))
  have h₂ := mul_le_mul_of_nonneg_right (show (lam:ℝ)*r^2≤1 by linarith)
    (show 0≤Real.pi*Real.sqrt d+‖z‖ by positivity)
  have hfb : ‖fullProbabilityFlow hF x hr hl T z‖ ≤ (C+1)*B := by
    have h := mul_le_mul_of_nonneg_left (add_le_add h₁ h₂) hC.le
    dsimp [C,B] at *
    nlinarith [norm_nonneg (primitiveField F x r 0),Real.sqrt_nonneg (d:ℝ),Real.pi_pos]
  have hm := conditionalFieldMean_center_zero_bound hF x hr hl hT0 hT1
    (fullProbabilityFlow hF x hr hl T z)
  have hmn := norm_le_norm_sub_add (conditionalFieldMean F x r T (fullProbabilityFlow hF x hr hl T z))
    (primitiveField F x r 0)
  have hinside : Real.pi*Real.sqrt d+‖fullProbabilityFlow hF x hr hl T z‖+
      r*‖primitiveField F x r 0‖ ≤ (C+2)*B := by
    dsimp [B] at *
    nlinarith [norm_nonneg z]
  have hmul := mul_le_mul hL hinside (by positivity : 0≤Real.pi*Real.sqrt d+
    ‖fullProbabilityFlow hF x hr hl T z‖+r*‖primitiveField F x r 0‖) (by norm_num : (0:ℝ)≤1)
  have hfin : ‖conditionalFieldMean F x r T (fullProbabilityFlow hF x hr hl T z)‖ ≤ (2*C+5)*B := by
    have hc : ‖primitiveField F x r 0‖≤B := by
      dsimp [B]; exact le_add_of_nonneg_left (by positivity)
    nlinarith
  have hB' : B≤(Real.pi+1)*(circuitD F x+‖z‖) := by
    dsimp [B,circuitD]
    rw [field_zero_eq_gradient]
    nlinarith [mul_nonneg Real.pi_pos.le (norm_nonneg z),
      mul_nonneg Real.pi_pos.le (norm_nonneg (gradient F x)), Real.sqrt_nonneg (d:ℝ)]
  have hc : 2*C+5≤8*(C+1) := by linarith
  exact hfin.trans ((mul_le_mul hc hB' hB (by positivity)).trans_eq (by
    dsimp only [circuitGrowthConstant]; change _=8*(C+1)*(Real.pi+1)*(circuitD F x+‖z‖); ring))

lemma harmonicStationaryMoment_growth {d : ℕ} {F : Point d → ℝ} {lam : ℝ≥0}
    (hF : Primitive F lam) (x : Point d) {r T : ℝ} (hr : 0 ≤ r) (hr1 : r≤1)
    (hl : (lam:ℝ)*r^2≤1/2) (hL : (lam:ℝ)*r≤1) (hT0 : 0≤T) (hT1 : T<1) :
    harmonicStationaryMoment F x r T ≤ 4*circuitGrowthConstant^2*(circuitD F x)^2 := by
  have hm := (conditionalFieldMean_lipschitz hF x hr hl hT0 hT1).continuous
  have hg := gaussian_growth_sq_moment (hm.comp (fullProbabilityFlow_lipschitz hF x hr hl ⟨hT0,hT1.le⟩).continuous)
    circuitGrowthConstant_pos.le (circuitD_nonneg F x)
    (conditionalMean_flow_growth hF x hr hr1 hl hL hT0 hT1)
  have he : harmonicStationaryMoment F x r T =
      ∫z,‖conditionalFieldMean F x r T (fullProbabilityFlow hF x hr hl T z)‖^2 ∂stdGaussian (Point d) := by
    have hm' : AEStronglyMeasurable (fun y => ‖conditionalFieldMean F x r T y‖^2)
        ((gibbs (centeringPotential F x r T)).map (fun y => (productPointEquiv d d y).1)) :=
      (hm.norm.pow 2).aestronglyMeasurable
    have e₁ := integral_map ((productPointEquiv d d).continuous.fst.measurable.aemeasurable) hm'
    change (∫y,‖conditionalFieldMean F x r T y‖^2
      ∂(gibbs (centeringPotential F x r T)).map (fun y => (productPointEquiv d d y).1))=_ at e₁
    rw [centering_position_law hF x hr hl hT0 hT1] at e₁
    have e₂ := integral_map
      ((fullProbabilityFlow_lipschitz hF x hr hl ⟨hT0,hT1.le⟩).continuous.measurable.aemeasurable)
      (show AEStronglyMeasurable (fun y => ‖conditionalFieldMean F x r T y‖^2)
        ((stdGaussian (Point d)).map (fullProbabilityFlow hF x hr hl T)) from
        (hm.norm.pow 2).aestronglyMeasurable)
    rw [fullProbabilityFlow_interpolation_closed hF x hr hl hT0 hT1] at e₂
    exact e₁.symm.trans e₂
  rw [he]
  apply hg.2.trans
  have hs := pow_le_pow_left₀ (Real.sqrt_nonneg (d:ℝ)) (sqrt_le_circuitD F x) 2
  rw [Real.sq_sqrt (Nat.cast_nonneg d)] at hs
  nlinarith [mul_le_mul_of_nonneg_left hs (sq_nonneg circuitGrowthConstant)]
end LogConcaveSampling

end

end

end OAI
end

section
-- module Solutions.OAIQ048_LC.LogConcave_Sampling_ProbabilityNormalizedTerm
attribute [-instance] _root_.OAI.LogConcaveSampling.LowerBound.couplingLaw_probability _root_.OAI.LogConcaveSampling.LowerBound.remainingHaar_probability _root_.OAI.LogConcaveSampling.LowerBound.roundRandomLaw_probability _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_invInvariant _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_isHaar _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_probability _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_rightInvariant _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_compactSpace _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_measurableInv _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_measurableMul _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_secondCountable _root_.OAI.LogConcaveSampling.MeanTree.instIsProbabilityMeasureRowTapeRowLaw _root_.OAI.LogConcaveSampling.OracleCompiler.topSeedLaw_probability _root_.OAI.LogConcaveSampling.noiseKernel_markov
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
namespace LogConcaveSampling
open Set MeasureTheory ProbabilityTheory Quadrature
open scoped Classical BigOperators NNReal

lemma kernel_error_factor {l B D A c p q f u : ℝ}
    (_ : 0≤l) (_ : 0≤B) (_ : 0≤D) (_ : 0≤A) (hc : 0 ≤ c)
    (hp0 : 0≤p) (hq0 : 0≤q) (hf0 : 0≤f) (hu0 : 0≤u)
    (hp : p≤A*B*D) (hq : q≤A*B*D)
    (hf : f≤A*l*(c+1)*B*D) (hu : u ≤ c*l) :
    2*(2*u)^2*(32*p^2+2*q^2)+2*f^2 ≤
      300*((c+1)*A*l*B*D)^2 := by
  have hpp := pow_le_pow_left₀ hp0 hp 2
  have hqq := pow_le_pow_left₀ hq0 hq 2
  have hff := pow_le_pow_left₀ hf0 hf 2
  have huu := pow_le_pow_left₀ hu0 hu 2
  have hinside : 32*p^2+2*q^2≤34*(A*B*D)^2 := by linarith
  have hmul := mul_le_mul (by nlinarith : 2*(2*u)^2≤8*(c*l)^2)
    hinside (by positivity : 0≤32*p^2+2*q^2) (by positivity : 0≤8*(c*l)^2)
  have hc' : c^2≤(c+1)^2 := by nlinarith
  have hlast := mul_le_mul_of_nonneg_right hc' (show 0≤272*(A*l*B*D)^2 by positivity)
  nlinarith [sq_nonneg ((c+1)*A*l*B*D)]

lemma probabilityNormalizedTerm_nonneg (d k n : ℕ) {h : ℝ} (hh : 0≤h) :
    0≤probabilityNormalizedTerm d k n h := by
  unfold probabilityNormalizedTerm
  have hl : 0≤Real.log ((d:ℝ)+1) := Real.log_nonneg (by linarith [Nat.cast_nonneg (α:=ℝ) d])
  positivity

lemma probabilityRmsBudget_normalized {d : ℕ} (F : Point d → ℝ) (x : Point d)
    (lam A : ℝ≥0) {r h C : ℝ} (hr : 0 ≤ r) (hh : 0≤h) (hC : 0≤C)
    (hL : (lam:ℝ)*r≤1) (k n N : ℕ) :
    probabilityRmsBudget F x lam A r h C k n N ≤
      (4*C*((lam:ℝ)*r^2)*probabilityNormalizedTerm d k n h+
        (A*probabilityMeanLipschitz lam r:ℝ≥0)^N*(2*circuitGrowthConstant*r))*circuitD F x := by
  have hds := sqrt_le_circuitD F x
  have hp := probabilityInitialRms_growth F x lam hr hL
  have h₁ := mul_le_mul_of_nonneg_left hds
    (show 0≤4*C*((lam:ℝ)*r^2)*probabilityNormalizedTerm d k n h by
      positivity [probabilityNormalizedTerm_nonneg d k n hh])
  have h₂ := mul_le_mul_of_nonneg_left hp
    (show 0≤2*(A*probabilityMeanLipschitz lam r:ℝ≥0)^N by positivity)
  dsimp [probabilityRmsBudget, probabilityNormalizedTerm] at *
  nlinarith

lemma harmonicNormalizedTerm_nonneg (n : ℕ) {R z : ℝ} (hR : 0≤R) :
    0≤harmonicNormalizedTerm n R z := by unfold harmonicNormalizedTerm; positivity

lemma harmonicRmsBudget_normalized {d : ℕ} {F : Point d → ℝ} {lam : ℝ≥0}
    (hF : Primitive F lam) (x : Point d) (A : ℝ≥0) {r R t z C : ℝ}
    (hr : 0 ≤ r) (hr1 : r≤1) (hR : 0<R) (hz : 0≤z) (hC : 0≤C)
    (hl : (lam:ℝ)*r^2≤1/2) (hL : (lam:ℝ)*r≤1) (ht0 : 0≤t) (ht1 : t<1) (n N : ℕ) :
    harmonicRmsBudget F x lam A r R t z C n N ≤
      (C*((lam:ℝ)*r^2)*harmonicNormalizedTerm n R z+
        (A*probabilityMeanLipschitz lam r:ℝ≥0)^N*(2*circuitGrowthConstant*r))*circuitD F x := by
  have hD := circuitD_nonneg F x
  have hsqrtD : Real.sqrt d ≤ circuitD F x := sqrt_le_circuitD F x
  have hm := harmonicStationaryMoment_growth hF x hr hr1 hl hL ht0 ht1
  have hms : Real.sqrt (harmonicStationaryMoment F x r t)≤2*circuitGrowthConstant*circuitD F x := by
    apply (Real.sqrt_le_iff).mpr
    refine ⟨by positivity [circuitGrowthConstant_pos],?_⟩
    nlinarith
  let E := 2*C*(|z|^(n+1)/(n.factorial:ℝ))*Real.sqrt d*((lam:ℝ)*r)*
    (R⁻¹)^(2*(n+1))*Real.sqrt (harmonicMeanBudget (n+1))
  have hE : 0≤E := by dsimp [E]; positivity
  have heq : 4*C^2*(z^(n+1)/(n.factorial:ℝ))^2*
      ((d*((lam:ℝ)*r)^2)*(R⁻¹)^(4*(n+1))*harmonicMeanBudget (n+1))=E^2 := by
    dsimp [E]
    rw [show 4*(n+1)=2*(2*(n+1)) by omega, pow_mul]
    simp only [abs_of_nonneg hz,mul_pow,div_pow,
      Real.sq_sqrt (show 0≤(d:ℝ) by positivity),Real.sq_sqrt (harmonicMeanBudget_nonneg (n+1))]
    ring
  have hs : Real.sqrt (4*C^2*(z^(n+1)/(n.factorial:ℝ))^2*
      ((d*((lam:ℝ)*r)^2)*(R⁻¹)^(4*(n+1))*harmonicMeanBudget (n+1)))=E := by
    rw [heq,Real.sqrt_sq hE]
  have h₁ := mul_le_mul_of_nonneg_left hsqrtD
    (show 0≤C*((lam:ℝ)*r^2)*harmonicNormalizedTerm n R z by
      positivity [harmonicNormalizedTerm_nonneg (z:=z) n hR.le])
  have h₂ := mul_le_mul_of_nonneg_left ht1.le hE
  have h₃ := mul_le_mul_of_nonneg_left h₂ (show 0≤2*r by positivity)
  have h₄ := mul_le_mul_of_nonneg_left hms
    (show 0≤(A*probabilityMeanLipschitz lam r:ℝ≥0)^N*(r*t) by positivity)
  have h₅ := mul_le_mul_of_nonneg_left ht1.le
    (show 0≤(A*probabilityMeanLipschitz lam r:ℝ≥0)^N*(2*circuitGrowthConstant*r)*circuitD F x by
      positivity [circuitGrowthConstant_pos])
  rw [harmonicRmsBudget,hs]
  dsimp [E,harmonicNormalizedTerm] at *
  nlinarith
end LogConcaveSampling

end

end

section

noncomputable section
namespace LogConcaveSampling
open MeasureTheory Quadrature
open scoped NNReal BigOperators

lemma numericalContractionCoefficient_pos (Ap Ah Lp : ℝ≥0) :
    0<numericalContractionCoefficient Ap Ah Lp := by
  unfold numericalContractionCoefficient
  positivity
lemma numericalErrorCoefficient_pos (C J : ℝ) : 0<numericalErrorCoefficient C J := by
  unfold numericalErrorCoefficient
  positivity [circuitGrowthConstant_pos]

lemma numericalContraction_bound (Ap Ah Lp : ℝ≥0) (lam : ℝ≥0) (r : ℝ) :
    (Ap*probabilityMeanLipschitz lam r:ℝ≥0)≤numericalContractionCoefficient Ap Ah Lp*((lam:ℝ)*r^2) ∧
    (Ah*probabilityMeanLipschitz lam r:ℝ≥0)≤numericalContractionCoefficient Ap Ah Lp*((lam:ℝ)*r^2) ∧
    (Lp*probabilityMeanLipschitz lam r:ℝ≥0)≤numericalContractionCoefficient Ap Ah Lp*((lam:ℝ)*r^2) := by
  have h₁ : (Ap:ℝ)*(Real.pi^2/2)≤numericalContractionCoefficient Ap Ah Lp := by
    dsimp [numericalContractionCoefficient]; nlinarith [Ap.coe_nonneg,Ah.coe_nonneg,Lp.coe_nonneg,sq_nonneg Real.pi]
  have h₂ : (Ah:ℝ)*(Real.pi^2/2)≤numericalContractionCoefficient Ap Ah Lp := by
    dsimp [numericalContractionCoefficient]; nlinarith [Ap.coe_nonneg,Ah.coe_nonneg,Lp.coe_nonneg,sq_nonneg Real.pi]
  have h₃ : (Lp:ℝ)*(Real.pi^2/2)≤numericalContractionCoefficient Ap Ah Lp := by
    dsimp [numericalContractionCoefficient]; nlinarith [Ap.coe_nonneg,Ah.coe_nonneg,Lp.coe_nonneg,sq_nonneg Real.pi]
  refine ⟨?_,?_,?_⟩
  · change (Ap:ℝ)*(Real.pi^2/2*(lam:ℝ)*r^2) ≤ _
    simpa only [mul_assoc] using mul_le_mul_of_nonneg_right h₁ (show 0≤(lam:ℝ)*r^2 by positivity)
  · change (Ah:ℝ)*(Real.pi^2/2*(lam:ℝ)*r^2) ≤ _
    simpa only [mul_assoc] using mul_le_mul_of_nonneg_right h₂ (show 0≤(lam:ℝ)*r^2 by positivity)
  · change (Lp:ℝ)*(Real.pi^2/2*(lam:ℝ)*r^2) ≤ _
    simpa only [mul_assoc] using mul_le_mul_of_nonneg_right h₃ (show 0≤(lam:ℝ)*r^2 by positivity)

theorem kernelValueRmsBudget_normalized {d : ℕ} {F : Point d → ℝ} {lam : ℝ≥0}
    (hF : Primitive F lam) (x : Point d) (Ap Ah Lp : ℝ≥0) {r R ρ h z C J : ℝ}
    (hr : 0 ≤ r) (hr1 : r≤1) (hR : 0<R) (hh : 0≤h) (hz : 0≤z) (hC : 0≤C) (hJ : 0≤J)
    (hl : (lam:ℝ)*r^2≤1/2) (hL : (lam:ℝ)*r≤1) (hρ0 : 0≤ρ) (hρ1 : ρ<1) (k n N : ℕ) :
    kernelValueRmsBudget F x lam Ap Ah Lp r R ρ h z C J k n N ≤
      300*((numericalContractionCoefficient Ap Ah Lp+1)*numericalErrorCoefficient C J*
        ((lam:ℝ)*r^2)*kernelNormalizedTerm d k n N lam Ap Ah Lp r R h z*circuitD F x)^2 := by
  let l := (lam:ℝ)*r^2
  let c := numericalContractionCoefficient Ap Ah Lp
  let A := numericalErrorCoefficient C J
  let D := circuitD F x
  let P := probabilityNormalizedTerm d k n h
  let H := harmonicNormalizedTerm n R z
  let q := (c*l)^N
  let B := P+H+q
  have hl0 : 0≤l := by positivity
  have hl1 : l≤1 := by dsimp [l]; linarith
  have hc : 0 < c := numericalContractionCoefficient_pos Ap Ah Lp
  have hA : 0<A := numericalErrorCoefficient_pos C J
  have hD : 0≤D := circuitD_nonneg F x
  have hP : 0≤P := probabilityNormalizedTerm_nonneg d k n hh
  have hH : 0≤H := harmonicNormalizedTerm_nonneg (z:=z) n hR.le
  have hq : 0≤q := by dsimp [q]; positivity
  have hB : 0≤B := by dsimp [B]; positivity
  have hAP : 4*C≤A := by dsimp [A,numericalErrorCoefficient]; rw [abs_of_nonneg hC]; linarith [abs_nonneg J,circuitGrowthConstant_pos]
  have hAH : J≤A := by dsimp [A,numericalErrorCoefficient]; rw [abs_of_nonneg hJ]; linarith [abs_nonneg C,circuitGrowthConstant_pos]
  have hAI : 2*circuitGrowthConstant≤A := by dsimp [A,numericalErrorCoefficient]; linarith [abs_nonneg C,abs_nonneg J]
  obtain ⟨htp,hth,htl⟩ := numericalContraction_bound Ap Ah Lp lam r
  have htpN := pow_le_pow_left₀ (show (0:ℝ)≤(Ap*probabilityMeanLipschitz lam r:ℝ≥0) by positivity) htp N
  have hthN := pow_le_pow_left₀ (show (0:ℝ)≤(Ah*probabilityMeanLipschitz lam r:ℝ≥0) by positivity) hth N
  change _≤q at htpN hthN
  have hcommon {a v t : ℝ} (ha : 0≤a) (hv : 0≤v) (ht : 0≤t) (hAa : a≤A) (htq : t≤q) :
      a*l*v+t*(2*circuitGrowthConstant*r)≤A*(v+q) := by
    have h₁ := mul_le_mul_of_nonneg_right hl1 (mul_nonneg ha hv)
    have h₂ := mul_le_mul_of_nonneg_right hAa hv
    have h₃ := mul_le_mul_of_nonneg_left hr1 (show 0≤2*circuitGrowthConstant by positivity [circuitGrowthConstant_pos])
    have h₄ := mul_le_mul htq (by simpa using h₃.trans (by simpa using hAI)) (by positivity [circuitGrowthConstant_pos]) hq
    nlinarith
  have hpb := probabilityRmsBudget_normalized F x lam Ap hr hh hC hL k n N
  have hhb := harmonicRmsBudget_normalized hF x Ah hr hr1 hR hz hJ hl hL hρ0 hρ1 n N
  have hp : probabilityRmsBudget F x lam Ap r h C k n N≤A*B*D := by
    apply hpb.trans
    have h₁ := hcommon (a:=4*C) (v:=P) (t:=(Ap*probabilityMeanLipschitz lam r:ℝ≥0)^N)
      (by positivity) hP (by positivity) hAP htpN
    have h₂ := mul_le_mul_of_nonneg_left (show P+q≤B by dsimp [B]; linarith) hA.le
    exact mul_le_mul_of_nonneg_right (h₁.trans h₂) hD
  have hq' : harmonicRmsBudget F x lam Ah r R ρ z J n N≤A*B*D := by
    apply hhb.trans
    have h₁ := hcommon hJ hH (show (0:ℝ)≤(Ah*probabilityMeanLipschitz lam r:ℝ≥0)^N by positivity) hAH hthN
    have h₂ := mul_le_mul_of_nonneg_left (show H+q≤B by dsimp [B]; linarith) hA.le
    exact mul_le_mul_of_nonneg_right (h₁.trans h₂) hD
  have hf : probabilityRmsBudget F x lam Ap r h C k n (N+1)≤A*l*(c+1)*B*D := by
    apply (probabilityRmsBudget_normalized F x lam Ap hr hh hC hL k n (N+1)).trans
    have hnext := mul_le_mul htpN htp (by positivity : (0:ℝ)≤(Ap*probabilityMeanLipschitz lam r:ℝ≥0)) hq
    rw [←pow_succ] at hnext
    have h₁ := mul_le_mul_of_nonneg_right hAP (mul_nonneg hl0 hP)
    have h₂ := mul_le_mul_of_nonneg_left hr1 (show 0≤2*circuitGrowthConstant by positivity [circuitGrowthConstant_pos])
    have h₃ := mul_le_mul hnext (by simpa using h₂.trans (by simpa using hAI)) (by positivity [circuitGrowthConstant_pos]) (by positivity)
    have h₄ := mul_le_mul_of_nonneg_left (show P+c*q≤(c+1)*B by dsimp [B]; nlinarith) (mul_nonneg hA.le hl0)
    apply mul_le_mul_of_nonneg_right _ hD
    change _≤A*l*(c+1)*B
    nlinarith
  have hlog : 0≤1+Real.log ((d:ℝ)+1) := by
    have := Real.log_nonneg (show 1≤(d:ℝ)+1 by linarith [Nat.cast_nonneg (α:=ℝ) d]); linarith
  unfold kernelValueRmsBudget
  apply kernel_error_factor hl0 hB hD hA.le hc.le
    (by unfold probabilityRmsBudget; positivity [probabilityInitialRms_nonneg F x lam r])
    (by unfold harmonicRmsBudget; positivity)
    (by unfold probabilityRmsBudget; positivity [probabilityInitialRms_nonneg F x lam r]) (by positivity) hp hq' hf htl
end LogConcaveSampling

end

end

end OAI
end

section
-- module Solutions.OAIQ048_LC.LogConcave_Complexity_KernelActionNormalizedBudget
attribute [-instance] _root_.OAI.LogConcaveSampling.LowerBound.couplingLaw_probability _root_.OAI.LogConcaveSampling.LowerBound.remainingHaar_probability _root_.OAI.LogConcaveSampling.LowerBound.roundRandomLaw_probability _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_invInvariant _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_isHaar _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_probability _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_rightInvariant _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_compactSpace _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_measurableInv _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_measurableMul _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_secondCountable _root_.OAI.LogConcaveSampling.MeanTree.instIsProbabilityMeasureRowTapeRowLaw _root_.OAI.LogConcaveSampling.OracleCompiler.topSeedLaw_probability _root_.OAI.LogConcaveSampling.noiseKernel_markov
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
namespace LogConcaveSampling
open Set MeasureTheory Quadrature
open scoped Classical BigOperators NNReal

lemma circuitD_dimension {d : ℕ} (F : Point d → ℝ) (x : Point d) :
    (d:ℝ)≤(circuitD F x)^2 := by
  have h := pow_le_pow_left₀ (Real.sqrt_nonneg (d:ℝ)) (sqrt_le_circuitD F x) 2
  simpa only [Real.sq_sqrt (Nat.cast_nonneg d)] using h

lemma harmonicNormalizedTerm_mono (n : ℕ) {R z Z : ℝ} (hR : 0≤R) (hz : 0≤z) (hzZ : z≤Z) :
    harmonicNormalizedTerm n R z≤harmonicNormalizedTerm n R Z := by
  unfold harmonicNormalizedTerm
  rw [abs_of_nonneg hz,abs_of_nonneg (hz.trans hzZ)]
  gcongr

lemma kernelNormalizedTerm_mono (d k n N : ℕ) (lam Ap Ah Lp : ℝ≥0)
    (r R h : ℝ) {z Z : ℝ} (hR : 0≤R) (hz : 0≤z) (hzZ : z≤Z) :
    kernelNormalizedTerm d k n N lam Ap Ah Lp r R h z≤
      kernelNormalizedTerm d k n N lam Ap Ah Lp r R h Z := by
  dsimp only [kernelNormalizedTerm]
  gcongr
  exact harmonicNormalizedTerm_mono n hR hz hzZ

lemma weighted_uniform_upper {ι : Type*} [Fintype ι] (a f : ι → ℝ) {B : ℝ}
    (ha : ∀i,0≤a i) (hf : ∀i,f i≤B) :
    (∑i,a i*f i)≤(∑i,a i)*B := by
  rw [Finset.sum_mul]
  exact Finset.sum_le_sum (fun i _ => mul_le_mul_of_nonneg_left (hf i) (ha i))

lemma kernelActionNormalizedBudget_nonneg (d k n m N : ℕ) (lam Ap Ah Lp : ℝ≥0)
    (r R h ψ C J : ℝ) (hR : 0≤R) : 0≤kernelActionNormalizedBudget d k n m N lam Ap Ah Lp r R h ψ C J := by
  unfold kernelActionNormalizedBudget
  positivity [harmonicCorrectionBudget_nonneg (m+1)]

theorem kernelActionRmsBudget_normalized {d : ℕ} {F : Point d → ℝ} {lam : ℝ≥0}
    (hF : Primitive F lam) (x : Point d) (Ap Ah Lp : ℝ≥0) {r R ρ h ψ C J : ℝ}
    (hr : 0 ≤ r) (hr1 : r≤1) (hR : 0<R) (hh : 0≤h) (hψ : 0<ψ) (hC : 0≤C) (hJ : 0≤J)
    (hl : (lam:ℝ)*r^2≤1/2) (hL : (lam:ℝ)*r≤1) (hρ0 : 0≤ρ) (hρ1 : ρ<1) (k n m N : ℕ) :
    kernelActionRmsBudget F x lam Ap Ah Lp r R ρ h ψ C J k n m N ≤
      (((lam:ℝ)*r^2)*circuitD F x)^2*
        kernelActionNormalizedBudget d k n m N lam Ap Ah Lp r R h ψ C J := by
  let l := (lam:ℝ)*r^2
  let D := circuitD F x
  let S := (∑i,|derivativeWeight (angleNodes m) i|)/ψ
  let V := (numericalContractionCoefficient Ap Ah Lp+1)*numericalErrorCoefficient C J
  let B := kernelNormalizedTerm d k n N lam Ap Ah Lp r R h (ψ*m)
  have hl0 : 0≤l := by positivity
  have hD : 0≤D := circuitD_nonneg F x
  have hV : 0≤V := by dsimp [V]; positivity [numericalContractionCoefficient_pos Ap Ah Lp,
    numericalErrorCoefficient_pos C J]
  have hS : 0≤S := by dsimp [S]; positivity
  have hw : (∑i,|derivativeWeight (angleNodes m) i/ψ|)=S := by
    simp only [abs_div,abs_of_pos hψ,←Finset.sum_div,S]
  have hb (i : Fin (m+1)) : kernelValueRmsBudget F x lam Ap Ah Lp r R ρ h
      (ψ*angleNodes m i) C J k n N≤300*(V*l*B*D)^2 := by
    have hi0 : 0≤angleNodes m i := by dsimp [angleNodes]; positivity
    have hi1 : angleNodes m i≤(m:ℝ) := by dsimp [angleNodes]; exact_mod_cast Nat.le_of_lt_succ i.2
    have hz : 0≤ψ*angleNodes m i := mul_nonneg hψ.le hi0
    apply (kernelValueRmsBudget_normalized hF x Ap Ah Lp hr hr1 hR hh hz hC hJ hl hL hρ0 hρ1 k n N).trans
    have hmono := kernelNormalizedTerm_mono d k n N lam Ap Ah Lp r R h hR.le hz
      (mul_le_mul_of_nonneg_left hi1 hψ.le)
    have hbase : 0≤kernelNormalizedTerm d k n N lam Ap Ah Lp r R h (ψ*angleNodes m i) := by
      unfold kernelNormalizedTerm
      positivity [probabilityNormalizedTerm_nonneg d k n hh,
        harmonicNormalizedTerm_nonneg (z:=ψ*angleNodes m i) n hR.le,
        numericalContractionCoefficient_pos Ap Ah Lp]
    change 300*(V*l*_*D)^2≤_
    gcongr
  have hsum := weighted_uniform_upper (fun i => |derivativeWeight (angleNodes m) i/ψ|)
    (fun i => kernelValueRmsBudget F x lam Ap Ah Lp r R ρ h (ψ*angleNodes m i) C J k n N)
    (fun i => abs_nonneg _) hb
  rw [hw] at hsum
  have hnum := mul_le_mul_of_nonneg_left hsum (show 0≤2*S by positivity)
  have hdim := circuitD_dimension F x
  have hc : 0≤harmonicCorrectionBudget (m+1) := harmonicCorrectionBudget_nonneg (m+1)
  have hang : 2*(S^2*(((ψ*m)^(m+1)/(m.factorial:ℝ))^2*
      ((d*l^2)*(R⁻¹)^(4*(m+1))*harmonicCorrectionBudget (m+1))))≤
      2*(S^2*(((ψ*m)^(m+1)/(m.factorial:ℝ))^2*
      ((D^2*l^2)*(R⁻¹)^(4*(m+1))*harmonicCorrectionBudget (m+1)))) := by
    gcongr
  unfold kernelActionRmsBudget
  rw [hw]
  calc
    _ ≤ 2*S*(S*(300*(V*l*B*D)^2))+2*(S^2*(((ψ*m)^(m+1)/(m.factorial:ℝ))^2*
        ((D^2*l^2)*(R⁻¹)^(4*(m+1))*harmonicCorrectionBudget (m+1)))) := by
      apply add_le_add
      · simpa only [mul_assoc] using hnum
      · exact hang
    _ = _ := by dsimp [kernelActionNormalizedBudget,V,B,S,l,D]; ring
end LogConcaveSampling

end

end

end OAI
end

section
-- module Solutions.OAIQ048_LC.LogConcave_Numerics_TwoendsContinuous
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
namespace LogConcaveSampling.Quadrature
open Set MeasureTheory
open scoped BigOperators

variable {I : Type*} [Fintype I] [DecidableEq I]

lemma twoends_continuousOn {a b : ℝ} (ha : 0<a) (hab : a≤b) (hb : b<1) :
    ContinuousOn (fun t : ℝ => t⁻¹*(1-t)⁻¹) (uIcc a b) := by
  rw [uIcc_of_le hab]
  exact (continuousOn_id.inv₀ (fun _ ht => ne_of_gt (ha.trans_le ht.1))).mul
    ((continuousOn_const.sub continuousOn_id).inv₀ (fun t ht => by change 1-t≠0; linarith [ht.2]))

lemma twoends_integral {a b : ℝ} (ha : 0<a) (hab : a≤b) (hb : b<1) :
    (∫t in a..b,t⁻¹*(1-t)⁻¹)=
      Real.log b-Real.log (1-b)-(Real.log a-Real.log (1-a)) := by
  apply intervalIntegral.integral_eq_sub_of_hasDerivAt (f:=fun t => Real.log t-Real.log (1-t))
  · intro t ht
    rw [uIcc_of_le hab] at ht
    have ht0 : t≠0 := ne_of_gt (ha.trans_le ht.1)
    have ht1 : 1-t≠0 := by linarith [ht.2]
    have hd : HasDerivAt (fun t : ℝ => Real.log t-Real.log (1-t))
        (t⁻¹-(-1/(1-t))) t := by
      convert! (Real.hasDerivAt_log ht0).sub
        (((hasDerivAt_id t).const_sub 1).log ht1) using 1
      all_goals try with_reducible_and_instances rfl
    convert! hd using 1; field_simp [ht0,ht1]; ring
  · exact (twoends_continuousOn ha hab hb).intervalIntegrable

lemma twoends_integral_upper {a T h : ℝ} (ha : 0<a) (haT : a≤T) (hT : T<1)
    (hh : 0<h) (hla : h/4≤a) :
    (∫t in a..T,t⁻¹*(1-t)⁻¹)≤logMeshLength T+|Real.log h|+Real.log 4 := by
  rw [twoends_integral ha haT hT]
  have hT0 : 0<T := ha.trans_le haT
  have h1a : 0<1-a := by linarith
  have hlogT : Real.log T≤0 := Real.log_nonpos hT0.le hT.le
  have hloga : Real.log (1-a)≤0 := Real.log_nonpos h1a.le (by linarith)
  have hl := Real.log_le_log (by positivity : 0<h/4) hla
  rw [Real.log_div (ne_of_gt hh) (by norm_num)] at hl
  have hh' : -Real.log h≤|Real.log h| := neg_le_abs _
  dsimp only [logMeshLength]
  linarith

lemma ordinaryDerivativeWeight_bound (u : I → ℝ) (D : ℝ) (hD : 0≤D)
    (hDu : ∀t∈Icc (0:ℝ) 1,∑i,|basisDerivative u i t|≤D)
    {a b h : ℝ} (ha : 0<a) (hab : a<b) (hb : b<1) (hh : 0<h)
    (hl : h/4*(1-a)≤b-a) (i : I) :
    |ordinaryDerivativeWeight u a b i|≤
      (4*D/h)*(∫t in a..b,t⁻¹*(1-t)⁻¹) := by
  have hc := ordinaryDerivativeWeight_integrand_continuousOn u a b i ha hab.le
  have hk := twoends_continuousOn ha hab.le hb
  have hnorm := intervalIntegral.norm_integral_le_integral_norm (f:=fun t =>
    (b-a)⁻¹*t⁻¹*basisDerivative u i ((t-a)/(b-a))) (μ:=volume) hab.le
  change |ordinaryDerivativeWeight u a b i|≤_ at hnorm
  apply hnorm.trans
  rw [←intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_mono_on hab.le hc.norm.intervalIntegrable
    (continuousOn_const.mul hk).intervalIntegrable
  intro t ht
  have ht0 : 0<t := ha.trans_le ht.1
  have ht1 : 0<1-t := by linarith [ht.2]
  have hba : 0<b-a := sub_pos.mpr hab
  have hur : (t-a)/(b-a)∈Icc (0:ℝ) 1 :=
    ⟨div_nonneg (sub_nonneg.mpr ht.1) hba.le,
      (div_le_one hba).mpr (by linarith [ht.2])⟩
  have hu : |basisDerivative u i ((t-a)/(b-a))|≤D :=
    (Finset.single_le_sum (fun j _ => abs_nonneg (basisDerivative u j ((t-a)/(b-a))))
      (Finset.mem_univ i)).trans (hDu _ hur)
  have hinv : (b-a)⁻¹≤4/h*(1-t)⁻¹ := by
    rw [←one_div,div_le_iff₀ hba]
    have hl' : h*(1-t)≤4*(b-a) := by nlinarith [mul_nonneg hh.le (sub_nonneg.mpr ht.1)]
    have he : 1≤(4*(b-a))/(h*(1-t)) := (one_le_div (mul_pos hh ht1)).mpr hl'
    simpa only [div_eq_mul_inv,mul_inv_rev,mul_comm,mul_left_comm,mul_assoc] using he
  change |(b-a)⁻¹*t⁻¹*basisDerivative u i ((t-a)/(b-a))|≤
    (4*D/h)*(t⁻¹*(1-t)⁻¹)
  simp only [abs_mul,abs_of_nonneg (inv_nonneg.mpr hba.le),
    abs_of_nonneg (inv_nonneg.mpr ht0.le)]
  calc
    _ ≤ (b-a)⁻¹*t⁻¹*D := mul_le_mul_of_nonneg_left hu (by positivity)
    _ ≤ (4/h*(1-t)⁻¹)*t⁻¹*D := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hinv (by positivity)) hD
    _ = _ := by ring
end LogConcaveSampling.Quadrature

end

end

section

noncomputable section
namespace LogConcaveSampling.Quadrature
open Set MeasureTheory
open scoped BigOperators

lemma sum_fin_skip_first_integral {N : ℕ} (hN : 0<N) (a : ℕ → ℝ) (f : ℝ → ℝ)
    (hi : ∀k,1≤k → k<N → IntervalIntegrable f volume (a k) (a (k+1))) :
    (∑i : Fin N,if i.val=0 then 0 else ∫t in a i.val..a (i.val+1),f t)=
      ∫t in a 1..a N,f t := by
  obtain ⟨k,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (ne_of_gt hN)
  rw [Fin.sum_univ_eq_sum_range (fun j => if j=0 then 0 else ∫t in a j..a (j+1),f t),Finset.sum_range_succ']
  simp only [Nat.add_one_ne_zero,ite_false,ite_true,zero_add,add_zero]
  exact intervalIntegral.sum_integral_adjacent_intervals (a:=fun j => a (j+1))
    (fun j hj => hi (j+1) (by omega) (by omega))

lemma sum_fin_first {N : ℕ} (hN : 0<N) (C : ℝ) :
    (∑i : Fin N,if i.val=0 then C else 0)=C := by
  have he (i : Fin N) : (i.val=0)↔i=⟨0,hN⟩ := by
    constructor
    · intro hh; exact Fin.ext hh
    · intro hh; exact congrArg Fin.val hh
  simp_rw [he]
  simp
end LogConcaveSampling.Quadrature

namespace LogConcaveSampling
open Set MeasureTheory Quadrature
open scoped Classical BigOperators

theorem terminalQuadratureWeight_sum {T h : ℝ} (hT0 : 0<T) (hT1 : T<1)
    (hh : 0<h) (hs : h≤Real.log 2) (hL : h≤logMeshLength T)
    (n : ℕ) (D : ℝ) (hD : 0≤D)
    (hDu : ∀t∈Icc (0:ℝ) 1,∑i,|basisDerivative (probabilityNodes (n+1)) i t|≤D) :
    (∑s,|terminalQuadratureWeight T h n s|)≤
      4/h*((∑i,|zeroHermiteWeight (probabilityNodes (n+1)) 0 i|)+
        (n+2)*D*(logMeshLength T+|Real.log h|+Real.log 4)) := by
  let H := ∑i,|zeroHermiteWeight (probabilityNodes (n+1)) 0 i|
  let K := fun t : ℝ => t⁻¹*(1-t)⁻¹
  have hH : 0≤H := Finset.sum_nonneg (fun _ _ => abs_nonneg _)
  have hc (c : Fin (logMeshCount T h)) :
      (∑i,|terminalQuadratureWeight T h n (c,i)|)≤
        (if c.val=0 then 4*H/h else 0)+
        ((n+2:ℕ):ℝ)*(4*D/h)*(if c.val=0 then 0 else
          ∫t in logMeshNode T h c.val..logMeshNode T h (c.val+1),K t) := by
    by_cases hc0 : c.val=0
    · simp only [terminalQuadratureWeight,hc0,ite_true,mul_zero,add_zero,
        abs_div,abs_of_nonneg (probabilityCellLength_pos hT0 hT1 hh c).le,←Finset.sum_div]
      have hb := logMeshFirst_lower hT0 hT1 hh hL hs
      have he : h/4≤probabilityCellLength T h c := by
        simpa only [probabilityCellLength,hc0,logMeshNode_zero,zero_add,sub_zero] using hb
      apply (div_le_iff₀ (probabilityCellLength_pos hT0 hT1 hh c)).mpr
      apply (le_of_eq (by field_simp [ne_of_gt hh] : H=(4*H/h)*(h/4))).trans
      exact mul_le_mul_of_nonneg_left he (by positivity)
    · simp only [terminalQuadratureWeight,hc0,ite_false,zero_add]
      have ha := logMeshNode_pos hT0 hT1 hh (Nat.pos_of_ne_zero hc0)
      have hb := (logMeshNode_mem hT0 hT1 hh (Nat.succ_le_of_lt c.2)).2.trans_lt hT1
      have hab := logMeshNode_strictMono hT0 hT1 hh (Nat.lt_succ_self c.val)
      have he := Finset.sum_le_sum (fun i (_ : i∈Finset.univ) =>
        ordinaryDerivativeWeight_bound (probabilityNodes (n+1)) D hD hDu ha hab hb hh
          (logMeshCell_lower hT0 hT1 hh hL hs c.val) i)
      simpa only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,
        Nat.cast_add,Nat.cast_one,mul_assoc,K,Nat.cast_ofNat,add_assoc,show (1:ℝ)+1=2 by norm_num] using he
  rw [Fintype.sum_prod_type]
  apply (Finset.sum_le_sum (fun c _ => hc c)).trans
  rw [Finset.sum_add_distrib,sum_fin_first (logMeshCount_pos hT0 hT1 hh),←Finset.mul_sum]
  rw [sum_fin_skip_first_integral (logMeshCount_pos hT0 hT1 hh)]
  · rw [logMeshNode_last hT0 hT1 hh]
    have hi := twoends_integral_upper (logMeshNode_pos hT0 hT1 hh (by norm_num : 0<1))
      (logMeshNode_mem hT0 hT1 hh (logMeshCount_pos hT0 hT1 hh)).2 hT1 hh
      (logMeshFirst_lower hT0 hT1 hh hL hs)
    have he := mul_le_mul_of_nonneg_left hi (by positivity : 0≤((n+2:ℕ):ℝ)*(4*D/h))
    change 4*H/h+((n+2:ℕ):ℝ)*(4*D/h)*(∫t in logMeshNode T h 1..T,K t)≤_
    calc
      _ ≤ 4*H/h+((n+2:ℕ):ℝ)*(4*D/h)*(logMeshLength T+|Real.log h|+Real.log 4) := add_le_add le_rfl he
      _ = _ := by dsimp only [H]; push_cast; ring
  · intro j hj hjN
    exact (twoends_continuousOn (logMeshNode_pos hT0 hT1 hh (by omega))
      (logMeshNode_strictMono hT0 hT1 hh (Nat.lt_succ_self j)).le
      ((logMeshNode_mem hT0 hT1 hh (by omega)).2.trans_lt hT1)).intervalIntegrable
end LogConcaveSampling

end

end

end OAI
end

section
-- module Solutions.OAIQ048_LC.LogConcave_Complexity_KernelAnalyticNormalizedBudget
attribute [-instance] _root_.OAI.LogConcaveSampling.LowerBound.couplingLaw_probability _root_.OAI.LogConcaveSampling.LowerBound.remainingHaar_probability _root_.OAI.LogConcaveSampling.LowerBound.roundRandomLaw_probability _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_invInvariant _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_isHaar _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_probability _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_rightInvariant _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_compactSpace _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_measurableInv _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_measurableMul _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_secondCountable _root_.OAI.LogConcaveSampling.MeanTree.instIsProbabilityMeasureRowTapeRowLaw _root_.OAI.LogConcaveSampling.OracleCompiler.topSeedLaw_probability _root_.OAI.LogConcaveSampling.noiseKernel_markov
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
namespace LogConcaveSampling
open Set MeasureTheory Quadrature
open scoped Classical BigOperators NNReal

lemma kernelAnalyticNormalizedBudget_nonneg (n d : ℕ) (T h D : ℝ) :
    0≤kernelAnalyticNormalizedBudget n d T h D := by
  unfold kernelAnalyticNormalizedBudget
  positivity

lemma kernelAnalyticBudget_normalized {d : ℕ} (F : Point d → ℝ) (x : Point d)
    (lam : ℝ≥0) (r D : ℝ) {T h : ℝ} (hT0 : 0<T) (hT1 : T<1) (hh : 0≤h) (n : ℕ) :
    kernelAnalyticBudget n d lam r T h D≤
      (((lam:ℝ)*r^2)*circuitD F x)^2*kernelAnalyticNormalizedBudget n d T h D := by
  have hp := terminalDerivativeBudget_polylog (n+1) d lam r
  have ht := terminalDerivativeBudget_nonneg (n+1) d lam r
  have hlen := (logMeshLength_pos hT0 hT1).le
  have hd := circuitD_dimension F x
  unfold kernelAnalyticBudget kernelAnalyticNormalizedBudget
  calc
    _ ≤ 32*(1+D^2+(∑i,|zeroHermiteWeight (probabilityNodes (n+1)) 0 i|)^2)*
      (2*logMeshLength T*((lam:ℝ)*r^2*
        (Real.exp (Real.pi^2/4)*(TensorSum.terminalQ (n+1)).val.logCoefficient 0 2)*
        (1+Real.log ((d:ℝ)+1))^((TensorSum.terminalQ (n+1)).val.logDegree 0))*2^(n+1)*h^n)^2*
        (circuitD F x)^2 := by gcongr
    _ = _ := by ring

lemma velocityNormalizedBudget_nonneg (d k n m N : ℕ) (lam Ap Ah Lp : ℝ≥0)
    (r R T h ψ C J D : ℝ) (hR : 0≤R) :
    0≤velocityNormalizedBudget d k n m N lam Ap Ah Lp r R T h ψ C J D := by
  unfold velocityNormalizedBudget
  positivity [kernelActionNormalizedBudget_nonneg d k (n+1) m N lam Ap Ah Lp r R h ψ C J hR,
    kernelAnalyticNormalizedBudget_nonneg n d T h D]

theorem velocityRmsBudget_normalized {d : ℕ} {F : Point d → ℝ} {lam : ℝ≥0}
    (hF : Primitive F lam) (x : Point d) (Ap Ah Lp : ℝ≥0) {r R T h ψ s C J D : ℝ}
    (hr : 0 < r) (hr1 : r≤1) (hR : 0<R) (hT0 : 0<T) (hT1 : T<1)
    (hh : 0<h) (hψ : 0<ψ) (hs : 0 < s) (hC : 0≤C) (hJ : 0≤J)
    (hl : (lam:ℝ)*r^2≤1/2) (hL : (lam:ℝ)*r≤1) (k n m N : ℕ) :
    (r*s)⁻¹^2*(2*((∑v,|terminalQuadratureWeight T h n v|)*
      (∑v,|terminalQuadratureWeight T h n v| *
        kernelActionRmsBudget F x lam Ap Ah Lp r R (probabilityNodeTime T h (n+1) v) h ψ C J k (n+1) m N))+
      2*kernelAnalyticBudget n d lam r T h D)≤
      (((lam:ℝ)*r/s)*circuitD F x)^2*
        velocityNormalizedBudget d k n m N lam Ap Ah Lp r R T h ψ C J D := by
  let Q := ∑v,|terminalQuadratureWeight T h n v|
  let E := kernelActionNormalizedBudget d k (n+1) m N lam Ap Ah Lp r R h ψ C J
  let B := (((lam:ℝ)*r^2)*circuitD F x)^2
  have hq : 0≤Q := by dsimp [Q]; positivity
  have hp (v : ProbabilityNode T h (n+1)) :
      kernelActionRmsBudget F x lam Ap Ah Lp r R (probabilityNodeTime T h (n+1) v) h ψ C J k (n+1) m N≤B*E := by
    have hv := probabilityNodeTime_mem hT0 hT1 hh (by omega : 0<n+1) v
    exact kernelActionRmsBudget_normalized hF x Ap Ah Lp hr.le hr1 hR hh.le hψ hC hJ hl hL
      hv.1 (hv.2.trans_lt hT1) k (n+1) m N
  have hw := weighted_uniform_upper (fun v => |terminalQuadratureWeight T h n v|) _
    (fun v => abs_nonneg _) hp
  have ha := kernelAnalyticBudget_normalized F x lam r D hT0 hT1 hh.le n
  have hb := mul_le_mul_of_nonneg_left
    (add_le_add (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hw hq) (by norm_num : (0:ℝ)≤2))
      (mul_le_mul_of_nonneg_left ha (by norm_num : (0:ℝ)≤2)))
    (sq_nonneg ((r*s)⁻¹))
  apply hb.trans_eq
  dsimp [Q,E,B,velocityNormalizedBudget]
  field_simp
end LogConcaveSampling

end

end

section

noncomputable section
namespace LogConcaveSampling
open Set MeasureTheory Quadrature
open scoped Classical BigOperators NNReal

lemma square_root_two_budget {A B : ℝ} (hA : 0≤A) (hB : 0≤B) (q : ℝ) (N : ℕ) :
    (2*Real.sqrt A+q^N*Real.sqrt B)^2≤8*A+2*q^(2*N)*B := by
  have hsA := Real.sq_sqrt hA
  have hsB := Real.sq_sqrt hB
  have he : q^(2*N)*B=(q^N*Real.sqrt B)^2 := by
    rw [show 2*N=N*2 by omega,pow_mul,mul_pow,hsB]
  nlinarith [sq_nonneg (2*Real.sqrt A-q^N*Real.sqrt B)]

lemma centerStateQuadratureEnvelope_nonneg (n : ℕ) (α R : ℝ) :
    0 ≤ centerStateQuadratureEnvelope n α R := by
  unfold centerStateQuadratureEnvelope
  positivity [centeringStateBudget_nonneg (n+2)]
lemma centerInitialEnvelope_nonneg (α R : ℝ) : 0 ≤ centerInitialEnvelope α R := by
  unfold centerInitialEnvelope
  positivity [centeringStateBudget_nonneg 1]
lemma centerStateEnvelope_nonneg (n N : ℕ) (α R q E : ℝ) (hq : 0≤q) (hE : 0≤E) :
    0 ≤ centerStateEnvelope n N α R q E := by
  unfold centerStateEnvelope
  positivity [centerStateQuadratureEnvelope_nonneg n α R,centerInitialEnvelope_nonneg α R]

lemma centeringStateQuadratureBudget_normalized {d : ℕ} (F : Point d → ℝ) (x : Point d)
    (n : ℕ) (lam : ℝ≥0) (r R s : ℝ) :
    centeringStateQuadratureBudget n d lam r R s≤
      (circuitD F x)^2*centerStateQuadratureEnvelope n ((lam:ℝ)*r/s) R := by
  have hd := circuitD_dimension F x
  have hc := centeringStateBudget_nonneg (n+2)
  unfold centeringStateQuadratureBudget centerStateQuadratureEnvelope
  push_cast
  nlinarith [mul_le_mul_of_nonneg_right hd
    (show 0≤8*(singleCellBasisBudget n)^2*(((lam:ℝ)*r/s)^2*(R⁻¹)^4)^(n+2)*centeringStateBudget (n+2) by positivity)]

lemma centeringInitialBudget_normalized {d : ℕ} (F : Point d → ℝ) (x : Point d)
    (lam : ℝ≥0) (r R s : ℝ) :
    centeringInitialBudget d lam r R s≤
      (circuitD F x)^2*centerInitialEnvelope ((lam:ℝ)*r/s) R := by
  have hd := circuitD_dimension F x
  have hc := centeringStateBudget_nonneg 1
  unfold centeringInitialBudget centerInitialEnvelope
  push_cast
  nlinarith [mul_le_mul_of_nonneg_right hd
    (show 0≤2*(((lam:ℝ)*r/s)^2*(R⁻¹)^4)*centeringStateBudget 1 by positivity)]

lemma centeringPicardBudget_normalized {d : ℕ} (F : Point d → ℝ) (x : Point d)
    (n N : ℕ) (lam K : ℝ≥0) (r R s E : ℝ) (hE : 0≤E) :
    centeringPicardBudget n N d lam K r R s ((((lam:ℝ)*r/s)*circuitD F x)^2*E)≤
      (circuitD F x)^2*centerStateEnvelope n N ((lam:ℝ)*r/s) R (centeringRowBudget n*K:ℝ≥0) E := by
  have hQ := centeringStateQuadratureBudget_normalized F x n lam r R s
  have hI := centeringInitialBudget_normalized F x lam r R s
  unfold centeringPicardBudget
  apply (square_root_two_budget
    (by positivity [centeringStateQuadratureBudget_nonneg n d lam r R s])
    (by unfold centeringInitialBudget; positivity [centeringStateBudget_nonneg 1])
      (centeringRowBudget n*K:ℝ≥0) N).trans
  have hq : 0≤((centeringRowBudget n*K:ℝ≥0):ℝ)^(2*N) := by positivity
  have hQ' := mul_le_mul_of_nonneg_left hQ (by norm_num : (0:ℝ)≤16)
  have hI' := mul_le_mul_of_nonneg_left hI (show 0≤2*((centeringRowBudget n*K:ℝ≥0):ℝ)^(2*N) by positivity)
  unfold centerStateEnvelope
  nlinarith

lemma centeringMeanBudget_normalized {d : ℕ} (F : Point d → ℝ) (x : Point d)
    (n : ℕ) (lam : ℝ≥0) (r R : ℝ) {s T Z : ℝ} (hs : 0 < s) (hT0 : 0≤T) (hT1 : T≤1) (hZ : 0≤Z) :
    2*(centeringRowBudget n:ℝ)^2*((Real.pi^2/2)*T*((lam:ℝ)*r))^2*((circuitD F x)^2*Z)+
      2*centeringMeanQuadratureBudget n d lam r R s≤
    (s*circuitD F x)^2*centerMeanEnvelope n ((lam:ℝ)*r/s) R Z := by
  have hd := circuitD_dimension F x
  have hc := centeringMeanBudget_nonneg (n+1)
  have hT : T^2≤1 := by nlinarith
  have he₁ := mul_le_mul_of_nonneg_left hT
    (show 0≤2*(centeringRowBudget n:ℝ)^2*(Real.pi^2/2)^2*((lam:ℝ)*r)^2*(circuitD F x)^2*Z by positivity)
  have he₂ := mul_le_mul_of_nonneg_right hd
    (show 0≤8*(singleCellBasisBudget n)^2*((lam:ℝ)*r)^2*
      (((lam:ℝ)*r/s)^2*(R⁻¹)^4)^(n+1)*centeringMeanBudget (n+1) by positivity)
  have hid : (s*circuitD F x)^2*centerMeanEnvelope n ((lam:ℝ)*r/s) R Z=
      2*(centeringRowBudget n:ℝ)^2*(Real.pi^2/2)^2*((lam:ℝ)*r)^2*(circuitD F x)^2*Z+
        8*(singleCellBasisBudget n)^2*((lam:ℝ)*r)^2*
          (((lam:ℝ)*r/s)^2*(R⁻¹)^4)^(n+1)*centeringMeanBudget (n+1)*(circuitD F x)^2 := by
    unfold centerMeanEnvelope
    field_simp
  rw [hid]
  unfold centeringMeanQuadratureBudget
  nlinarith
end LogConcaveSampling

end

end

section

noncomputable section
namespace LogConcaveSampling
open Filter Asymptotics
open scoped Topology

lemma dimensionLog_nonneg (d : ℕ) : 0≤dimensionLog d := by
  have hh : 0≤Real.log ((d:ℝ)+1) := Real.log_nonneg (by linarith [Nat.cast_nonneg (α:=ℝ) d])
  unfold dimensionLog
  linarith

lemma dimensionLog_isBigO_log : dimensionLog =O[atTop] (fun d : ℕ => Real.log (d:ℝ)) := by
  have ht : Tendsto (fun d : ℕ => (d:ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  have hlog : ∀ᶠ d : ℕ in atTop,1≤Real.log (d:ℝ) :=
    (Real.tendsto_log_atTop.comp ht).eventually_ge_atTop 1
  apply IsBigO.of_bound 3
  filter_upwards [eventually_ge_atTop (2:ℕ),hlog] with d hd hl
  have hd0 : (0:ℝ)<d := by exact_mod_cast (by omega : 0<d)
  have hd1 : (2:ℝ)≤d := by exact_mod_cast hd
  have ht : Real.log ((d:ℝ)+1)≤2*Real.log (d:ℝ) := by
    calc
      _ ≤ Real.log ((d:ℝ)^2) := Real.log_le_log (by positivity) (by nlinarith)
      _ = _ := by rw [Real.log_pow]; norm_num
  rw [Real.norm_of_nonneg (dimensionLog_nonneg d),Real.norm_of_nonneg (by linarith : 0≤Real.log (d:ℝ))]
  unfold dimensionLog
  linarith

lemma dimensionLog_pow_isLittleO (k : ℕ) {s : ℝ} (hs : 0 < s) :
    (fun d : ℕ => dimensionLog d^k) =o[atTop] (fun d : ℕ => (d:ℝ)^s) := by
  have hh := (isLittleO_log_rpow_rpow_atTop (k:ℝ) hs).comp_tendsto
    (tendsto_natCast_atTop_atTop (R:=ℝ))
  simp only [Real.rpow_natCast,Function.comp_def] at hh
  exact (dimensionLog_isBigO_log.pow k).trans_isLittleO hh

theorem polylog_power_absorb (C : ℝ) (k : ℕ) {a b : ℝ} (hab : b<a) :
    ∀ᶠ d : ℕ in atTop, |C| *dimensionLog d^k*(d:ℝ)^(-a)≤(d:ℝ)^(-b) := by
  have hh := ((dimensionLog_pow_isLittleO k (sub_pos.mpr hab)).const_mul_left |C|).mul_isBigO
    (isBigO_refl (fun d : ℕ => (d:ℝ)^(-a)) atTop)
  have he : (fun d : ℕ => (d:ℝ)^(a-b)*(d:ℝ)^(-a)) =ᶠ[atTop]
      (fun d : ℕ => (d:ℝ)^(-b)) := by
    filter_upwards [eventually_ge_atTop (1:ℕ)] with d hd
    have hd0 : (0:ℝ)<d := by exact_mod_cast hd
    rw [←Real.rpow_add hd0]
    congr 1
    ring
  have hbnd := (hh.congr' Filter.EventuallyEq.rfl he).def (by norm_num : (0:ℝ)<1)
  filter_upwards [hbnd] with d hd
  simpa only [one_mul,Real.norm_of_nonneg (by positivity [dimensionLog_nonneg d] : 0≤|C| *dimensionLog d^k*(d:ℝ)^(-a)),
    Real.norm_of_nonneg (by positivity : 0≤(d:ℝ)^(-b))] using hd
end LogConcaveSampling

end

end

section

noncomputable section
namespace LogConcaveSampling
open Filter Asymptotics
open scoped Topology

lemma dimensionLog_one_le (d : ℕ) : 1≤dimensionLog d := by
  unfold dimensionLog
  have h := Real.log_nonneg (by linarith [Nat.cast_nonneg (α:=ℝ) d] : 1≤(d:ℝ)+1)
  linarith

namespace LogPowerRate

lemma congr {f g : ℕ → ℝ} {a : ℝ} (h : LogPowerRate f a) (he : f=ᶠ[atTop] g) : LogPowerRate g a := by
  obtain ⟨k,hk⟩ := h
  exact ⟨k,hk.congr' he Filter.EventuallyEq.rfl⟩

lemma mono {f : ℕ → ℝ} {a b : ℝ} (h : LogPowerRate f a) (hba : b≤a) : LogPowerRate f b := by
  obtain ⟨k,hk⟩ := h
  refine ⟨k,hk.trans (IsBigO.of_bound 1 ?_)⟩
  filter_upwards [eventually_ge_atTop (1:ℕ)] with d hd
  have hd1 : (1:ℝ)≤d := by exact_mod_cast hd
  have hd0 : (0:ℝ)<d := lt_of_lt_of_le zero_lt_one hd1
  simp only [one_mul,Real.norm_of_nonneg (by positivity [dimensionLog_nonneg d] :
    0≤dimensionLog d^k*(d:ℝ)^(-a)), Real.norm_of_nonneg (by positivity [dimensionLog_nonneg d] :
    0≤dimensionLog d^k*(d:ℝ)^(-b))]
  exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hd1 (by linarith)) (by positivity [dimensionLog_nonneg d])

lemma const (C : ℝ) : LogPowerRate (fun _ => C) 0 := by
  refine ⟨0,?_⟩
  simpa only [pow_zero,neg_zero,Real.rpow_zero,mul_one] using
    (isBigO_const_const C (by norm_num : (1:ℝ)≠0) atTop : (fun _ : ℕ => C)=O[atTop] (fun _ => (1:ℝ)))

lemma power (a : ℝ) : LogPowerRate (fun d => (d:ℝ)^(-a)) a := by
  refine ⟨0,?_⟩
  simpa only [pow_zero,one_mul] using (isBigO_refl (fun d : ℕ => (d:ℝ)^(-a)) atTop)

lemma log : LogPowerRate dimensionLog 0 := by
  refine ⟨1,?_⟩
  simpa only [pow_one,neg_zero,Real.rpow_zero,mul_one] using (isBigO_refl dimensionLog atTop)

lemma mul {f g : ℕ → ℝ} {a b : ℝ} (hf : LogPowerRate f a) (hg : LogPowerRate g b) :
    LogPowerRate (fun d => f d*g d) (a+b) := by
  obtain ⟨k,hk⟩ := hf
  obtain ⟨l,hl⟩ := hg
  refine ⟨k+l,(hk.mul hl).congr' Filter.EventuallyEq.rfl ?_⟩
  filter_upwards [eventually_ge_atTop (1:ℕ)] with d hd
  have hd0 : (0:ℝ)<d := by exact_mod_cast hd
  rw [pow_add,neg_add,Real.rpow_add hd0]
  ring

lemma pow {f : ℕ → ℝ} {a : ℝ} (hf : LogPowerRate f a) (n : ℕ) :
    LogPowerRate (fun d => f d^n) (n*a) := by
  induction n with
  | zero => simpa using const 1
  | succ n ih =>
    have h := ih.mul hf
    simpa only [pow_succ,Nat.cast_add,Nat.cast_one,add_mul,one_mul] using h

lemma const_mul {f : ℕ → ℝ} {a : ℝ} (hf : LogPowerRate f a) (C : ℝ) :
    LogPowerRate (fun d => C*f d) a := by
  simpa only [zero_add] using (const C).mul hf

lemma mul_const {f : ℕ → ℝ} {a : ℝ} (hf : LogPowerRate f a) (C : ℝ) :
    LogPowerRate (fun d => f d*C) a := by
  simpa only [add_zero] using hf.mul (const C)

lemma add {f g : ℕ → ℝ} {a : ℝ} (hf : LogPowerRate f a) (hg : LogPowerRate g a) :
    LogPowerRate (fun d => f d+g d) a := by
  obtain ⟨k,hk⟩ := hf
  obtain ⟨l,hl⟩ := hg
  have bound (i j : ℕ) : (fun d : ℕ => dimensionLog d^i*(d:ℝ)^(-a)) =O[atTop]
      (fun d => dimensionLog d^(i+j)*(d:ℝ)^(-a)) := by
    apply IsBigO.of_bound 1
    filter_upwards [] with d
    rw [one_mul,Real.norm_of_nonneg (by positivity [dimensionLog_nonneg d]),
      Real.norm_of_nonneg (by positivity [dimensionLog_nonneg d])]
    exact mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (dimensionLog_one_le d) (by omega)) (by positivity)
  exact ⟨k+l,(hk.trans (bound k l)).add (hl.trans (by simpa only [Nat.add_comm] using bound l k))⟩

lemma of_le_abs {f g : ℕ → ℝ} {a : ℝ} (hg : LogPowerRate g a)
    (hfg : ∀ᶠ d in atTop, |f d|≤|g d|) : LogPowerRate f a := by
  obtain ⟨k,hk⟩ := hg
  exact ⟨k,(IsBigO.of_bound 1 (by simpa only [one_mul,Real.norm_eq_abs] using hfg)).trans hk⟩

lemma eventually_small {f : ℕ → ℝ} {a b : ℝ} (hf : LogPowerRate f a) (hba : b<a) :
    ∀ᶠ d in atTop, |f d|≤(d:ℝ)^(-b) := by
  obtain ⟨k,hk⟩ := hf
  obtain ⟨C,hC⟩ := hk.bound
  have hp := polylog_power_absorb C k hba
  filter_upwards [hC,hp] with d hd hp
  have hdn : 0≤dimensionLog d^k*(d:ℝ)^(-a) := by positivity [dimensionLog_nonneg d]
  rw [Real.norm_eq_abs,Real.norm_of_nonneg hdn] at hd
  calc
    _ ≤ C*(dimensionLog d^k*(d:ℝ)^(-a)) := hd
    _ ≤ |C| *(dimensionLog d^k*(d:ℝ)^(-a)) := mul_le_mul_of_nonneg_right (le_abs_self C) hdn
    _ ≤ _ := by simpa only [mul_assoc] using hp

end LogPowerRate
end LogConcaveSampling

end

end

section

noncomputable section
namespace LogConcaveSampling
open Filter Asymptotics Set MeasureTheory Quadrature
open scoped Topology Classical BigOperators

namespace LogPowerRate
lemma abs {f : ℕ → ℝ} {a : ℝ} (hf : LogPowerRate f a) : LogPowerRate (fun d => |f d|) a := by
  exact of_le_abs hf (Eventually.of_forall (fun d => by simp))

lemma div_const {f : ℕ → ℝ} {a : ℝ} (hf : LogPowerRate f a) (C : ℝ) :
    LogPowerRate (fun d => f d/C) a := by
  simpa only [div_eq_mul_inv] using hf.mul_const C⁻¹

lemma of_le {f g : ℕ → ℝ} {a : ℝ} (hg : LogPowerRate g a)
    (hf : ∀ᶠ d : ℕ in atTop,0≤f d) (hfg : ∀ᶠ d : ℕ in atTop,f d≤g d) : LogPowerRate f a := by
  apply of_le_abs hg
  filter_upwards [hf,hfg] with d hd he
  rw [abs_of_nonneg hd,abs_of_nonneg (hd.trans he)]
  exact he

lemma inv_power (a : ℝ) : LogPowerRate (fun d => ((d:ℝ)^(-a))⁻¹) (-a) := by
  apply (power (-a)).congr
  filter_upwards [eventually_ge_atTop (1:ℕ)] with d hd
  have hd0 : (0:ℝ)≤d := Nat.cast_nonneg d
  rw [Real.rpow_neg hd0]

lemma log_nat : LogPowerRate (fun d : ℕ => Real.log (d:ℝ)) 0 := by
  apply of_le log
  · filter_upwards [eventually_ge_atTop (1:ℕ)] with d hd
    exact Real.log_nonneg (by exact_mod_cast hd)
  · filter_upwards [eventually_ge_atTop (1:ℕ)] with d hd
    have hp : (0:ℝ)<d := by exact_mod_cast hd
    have he := Real.log_le_log hp (by linarith : (d:ℝ)≤(d:ℝ)+1)
    unfold dimensionLog
    linarith

lemma log_power (a : ℝ) : LogPowerRate (fun d : ℕ => Real.log ((d:ℝ)^(-a))) 0 := by
  apply (log_nat.const_mul (-a)).congr
  filter_upwards [eventually_ge_atTop (1:ℕ)] with d hd
  rw [Real.log_rpow (by exact_mod_cast hd : (0:ℝ)<d)]
end LogPowerRate

lemma logMeshLength_le_scale {T R : ℝ} (hT0 : 0<T) (hT1 : T<1)
    (hR : 0<R) (hRT : R^2≤1-T^2) :
    logMeshLength T≤Real.log 2-2*Real.log R := by
  have hden : 0<1-T := by linarith
  have hRR : R^2/2≤1-T := by nlinarith
  have he := Real.log_le_log (by positivity : 0<R^2/2) hRR
  rw [Real.log_div (by positivity : R^2≠0) (by norm_num),Real.log_pow] at he
  unfold logMeshLength
  norm_num at he
  linarith

lemma logMeshLength_rate {T : ℕ → ℝ} (a : ℝ)
    (hT0 : ∀ᶠ d : ℕ in atTop,0<T d) (hT1 : ∀ᶠ d : ℕ in atTop,T d<1)
    (hRT : ∀ᶠ d : ℕ in atTop,((d:ℝ)^(-a))^2≤1-(T d)^2) :
    LogPowerRate (fun d => logMeshLength (T d)) 0 := by
  apply LogPowerRate.of_le ((LogPowerRate.const (Real.log 2)).add
    ((LogPowerRate.log_power a).const_mul (-2)))
  · filter_upwards [hT0,hT1] with d hd0 hd1
    exact (logMeshLength_pos hd0 hd1).le
  · filter_upwards [hT0,hT1,hRT,eventually_ge_atTop (1:ℕ)] with d hd0 hd1 hRT hd
    have hp : (0:ℝ)<d := by exact_mod_cast hd
    simpa only [sub_eq_add_neg,neg_mul] using
      logMeshLength_le_scale hd0 hd1 (Real.rpow_pos_of_pos hp (-a)) hRT

lemma terminalQuadratureWeight_rate (n : ℕ) (D : ℝ) (hD : 0≤D)
    (hDu : ∀t∈Icc (0:ℝ) 1,∑i,|basisDerivative (probabilityNodes (n+1)) i t|≤D)
    {T : ℕ → ℝ} (a b : ℝ)
    (hT0 : ∀ᶠ d : ℕ in atTop,0<T d) (hT1 : ∀ᶠ d : ℕ in atTop,T d<1)
    (hRT : ∀ᶠ d : ℕ in atTop,((d:ℝ)^(-a))^2≤1-(T d)^2)
    (hsmall : ∀ᶠ d : ℕ in atTop,(d:ℝ)^(-b)≤Real.log 2)
    (hlarge : ∀ᶠ d : ℕ in atTop,(d:ℝ)^(-b)≤logMeshLength (T d)) :
    LogPowerRate (fun d => ∑v,|terminalQuadratureWeight (T d) ((d:ℝ)^(-b)) n v|) (-b) := by
  have hlen := logMeshLength_rate a hT0 hT1 hRT
  have he := ((LogPowerRate.inv_power b).const_mul 4).mul
    ((LogPowerRate.const (∑i,|zeroHermiteWeight (probabilityNodes (n+1)) 0 i|)).add
      (((hlen.add (LogPowerRate.log_power b).abs).add (LogPowerRate.const (Real.log 4))).const_mul ((n+2)*D)))
  simp only [add_zero] at he
  apply LogPowerRate.of_le he
  · exact Eventually.of_forall (fun d => by positivity)
  · filter_upwards [hT0,hT1,hsmall,hlarge,eventually_ge_atTop (1:ℕ)] with d hd0 hd1 hs hl hd
    have hp : (0:ℝ)<d := by exact_mod_cast hd
    simpa only [div_eq_mul_inv] using terminalQuadratureWeight_sum hd0 hd1
      (Real.rpow_pos_of_pos hp (-b)) hs hl n D hD hDu
end LogConcaveSampling

end

end

end OAI
end

section
-- module Solutions.OAIQ048_LC.LogConcave_Complexity_EventuallySequences
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
namespace LogConcaveSampling
open Filter
open scoped Classical

theorem eventually_forall_of_sequences {X : Type*} [Nonempty X]
    {P Q : ℕ → X → Prop}
    (hne : ∀ᶠ d : ℕ in atTop, ∃x,P d x)
    (hall : ∀f : ℕ → X,(∀ᶠ d : ℕ in atTop,P d (f d)) →
      ∀ᶠ d : ℕ in atTop,Q d (f d)) :
    ∀ᶠ d : ℕ in atTop,∀x,P d x → Q d x := by
  let f : ℕ → X := fun d => if h : ∃x,P d x ∧ ¬Q d x then Classical.choose h
    else if h' : ∃x,P d x then Classical.choose h' else Classical.choice ‹Nonempty X›
  have hp : ∀ᶠ d : ℕ in atTop,P d (f d) := by
    filter_upwards [hne] with d hd
    dsimp only [f]
    split_ifs with h
    · exact (Classical.choose_spec h).1
    · exact Classical.choose_spec hd
  filter_upwards [hall f hp] with d hd x hx
  by_contra hn
  have he : ∃x,P d x ∧ ¬Q d x := ⟨x,hx,hn⟩
  have hf : f d=Classical.choose he := dite_eq_left he
  rw [hf] at hd
  exact (Classical.choose_spec he).2 hd

lemma logPowerEnvelope_rate (C : ℝ) (k : ℕ) (a : ℝ) :
    LogPowerRate (fun d => C*dimensionLog d^k*(d:ℝ)^(-a)) a := by
  have he := ((LogPowerRate.log.pow k).const_mul C).mul (LogPowerRate.power a)
  simpa only [mul_zero,zero_add] using he

lemma logPowerRate_of_envelope {f : ℕ → ℝ} {a C : ℝ} {k : ℕ}
    (hn : ∀ᶠ d in atTop,0≤f d)
    (he : ∀ᶠ d in atTop,f d≤C*dimensionLog d^k*(d:ℝ)^(-a)) :
    LogPowerRate f a := LogPowerRate.of_le (logPowerEnvelope_rate C k a) hn he
end LogConcaveSampling

end

end

end OAI
end

section
-- module Solutions.OAIQ048_LC.LogConcave_Sampling_NumericalLayerCount
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
namespace LogConcaveSampling
open Filter Set MeasureTheory Quadrature
open scoped Topology Classical BigOperators NNReal

lemma probabilityNormalizedTerm_rate (k n : ℕ) (b : ℝ) :
    LogPowerRate (fun d => probabilityNormalizedTerm d k n ((d:ℝ)^(-b))) ((n+1)*b) := by
  have he := (LogPowerRate.log.pow k).mul (((LogPowerRate.power b).const_mul 2).pow (n+1))
  simpa only [mul_zero,zero_add,Nat.cast_add,Nat.cast_one,probabilityNormalizedTerm,dimensionLog] using he

lemma harmonicNormalizedTerm_rate (n : ℕ) (a c z : ℝ) :
    LogPowerRate (fun d => harmonicNormalizedTerm n ((d:ℝ)^(-a)) (((d:ℝ)^(-c))*z))
      ((n+1)*(c-2*a)) := by
  have he := (((((LogPowerRate.power c).mul_const z).abs.pow (n+1)).div_const (n.factorial:ℝ)).const_mul 4).mul
    ((LogPowerRate.inv_power a).pow (2*(n+1)))
  have he' := he.mul_const (Real.sqrt (harmonicMeanBudget (n+1)))
  convert! he' using 1
  all_goals try with_reducible_and_instances rfl
  first | rfl | (push_cast; ring)

lemma kernelNormalizedTerm_rate (k n N : ℕ) (Ap Ah Lp : ℝ≥0)
    {lam : ℕ → ℝ≥0} {r : ℕ → ℝ} {a b c e u : ℝ} (z : ℝ)
    (hl : LogPowerRate (fun d => (lam d:ℝ)*(r d)^2) u)
    (heP : e≤(n+1)*b) (heH : e≤(n+1)*(c-2*a)) (heN : e≤N*u) :
    LogPowerRate (fun d => kernelNormalizedTerm d k n N (lam d) Ap Ah Lp
      (r d) ((d:ℝ)^(-a)) ((d:ℝ)^(-b)) (((d:ℝ)^(-c))*z)) e := by
  exact ((probabilityNormalizedTerm_rate k n b).mono heP).add
    ((harmonicNormalizedTerm_rate n a c z).mono heH) |>.add
      (((hl.const_mul (numericalContractionCoefficient Ap Ah Lp)).pow N).mono heN)

lemma kernelActionNormalizedBudget_rate (k n m N : ℕ) (Ap Ah Lp : ℝ≥0)
    {lam : ℕ → ℝ≥0} {r : ℕ → ℝ} {a b c e u : ℝ} (C J : ℝ)
    (hB : LogPowerRate (fun d => kernelNormalizedTerm d k n N (lam d) Ap Ah Lp
      (r d) ((d:ℝ)^(-a)) ((d:ℝ)^(-b)) (((d:ℝ)^(-c))*m)) u)
    (heB : e≤2*(u-c)) (heA : e≤2*c*m-4*a*(m+1)) :
    LogPowerRate (fun d => kernelActionNormalizedBudget d k n m N (lam d) Ap Ah Lp
      (r d) ((d:ℝ)^(-a)) ((d:ℝ)^(-b)) ((d:ℝ)^(-c)) C J) e := by
  let S := fun d : ℕ => (∑i,|derivativeWeight (angleNodes m) i|)/(d:ℝ)^(-c)
  have hS : LogPowerRate S (-c) := by
    simpa only [S,div_eq_mul_inv] using (LogPowerRate.inv_power c).const_mul
      (∑i,|derivativeWeight (angleNodes m) i|)
  have hfirst := (((hS.const_mul ((numericalContractionCoefficient Ap Ah Lp+1)*
    numericalErrorCoefficient C J)).mul hB).pow 2).const_mul 600
  have hfirst' : LogPowerRate (fun d => 600*((numericalContractionCoefficient Ap Ah Lp+1)*
      numericalErrorCoefficient C J*S d*kernelNormalizedTerm d k n N (lam d) Ap Ah Lp
        (r d) ((d:ℝ)^(-a)) ((d:ℝ)^(-b)) (((d:ℝ)^(-c))*m))^2) e := by
    apply hfirst.mono
    push_cast
    linarith
  have hp := (((LogPowerRate.power c).mul_const (m:ℝ)).pow (m+1)).div_const (m.factorial:ℝ)
  have hsecond := (((((hS.pow 2).const_mul 2).mul (hp.pow 2)).mul
    ((LogPowerRate.inv_power a).pow (4*(m+1)))).mul_const (harmonicCorrectionBudget (m+1)))
  have hsecond' : LogPowerRate (fun d => 2*(S d)^2*((((d:ℝ)^(-c))*m)^(m+1)/(m.factorial:ℝ))^2*
      (((d:ℝ)^(-a))⁻¹)^(4*(m+1))*harmonicCorrectionBudget (m+1)) e := by
    apply hsecond.mono
    push_cast
    nlinarith [heA]
  exact hfirst'.add hsecond'

lemma kernelAnalyticNormalizedBudget_rate (n : ℕ) (D b : ℝ) {T : ℕ → ℝ}
    (hT : LogPowerRate (fun d => logMeshLength (T d)) 0) :
    LogPowerRate (fun d => kernelAnalyticNormalizedBudget n d (T d) ((d:ℝ)^(-b)) D) (2*n*b) := by
  have he := (((((hT.const_mul 2).mul_const
      (Real.exp (Real.pi^2/4)*(TensorSum.terminalQ (n+1)).val.logCoefficient 0 2)).mul
        (LogPowerRate.log.pow ((TensorSum.terminalQ (n+1)).val.logDegree 0))).mul_const (2^(n+1))).mul
          ((LogPowerRate.power b).pow n))
  have he' := (he.pow 2).const_mul
    (32*(1+D^2+(∑i,|zeroHermiteWeight (probabilityNodes (n+1)) 0 i|)^2))
  convert! he' using 1
  all_goals try with_reducible_and_instances rfl
  first | rfl | ring

lemma velocityNormalizedBudget_rate (k n m N : ℕ) (Ap Ah Lp : ℝ≥0)
    {lam : ℕ → ℝ≥0} {r T : ℕ → ℝ} {a b c e u : ℝ} (C J D : ℝ)
    (hW : LogPowerRate (fun d => ∑v,|terminalQuadratureWeight (T d) ((d:ℝ)^(-b)) n v|) (-b))
    (hA : LogPowerRate (fun d => kernelActionNormalizedBudget d k (n+1) m N (lam d) Ap Ah Lp
      (r d) ((d:ℝ)^(-a)) ((d:ℝ)^(-b)) ((d:ℝ)^(-c)) C J) u)
    (hT : LogPowerRate (fun d => logMeshLength (T d)) 0)
    (heA : e≤u-2*b) (heT : e≤2*n*b) :
    LogPowerRate (fun d => velocityNormalizedBudget d k n m N (lam d) Ap Ah Lp
      (r d) ((d:ℝ)^(-a)) (T d) ((d:ℝ)^(-b)) ((d:ℝ)^(-c)) C J D) e := by
  have he := ((hW.pow 2).const_mul 2).mul hA
  apply (he.mono (by push_cast; linarith)).add
    (((kernelAnalyticNormalizedBudget_rate n D b hT).const_mul 2).mono heT)
end LogConcaveSampling

end

end

section

noncomputable section
namespace LogConcaveSampling

lemma numericalLayerCount_bound (J : ℝ) : 10*(J+2)≤(numericalLayerCount J:ℝ) := Nat.le_ceil _

lemma exists_numerical_order {J t w : ℝ} (ht : 0<t) (hw : 0<w) :
    ∃n : ℕ, w*((n:ℝ)-3)>J+10 ∧ t*((n:ℝ)-3)>J+10 ∧ (n:ℝ)>4*(J+10) := by
  obtain ⟨n,hn⟩ := exists_nat_gt (max (max (3+(J+10)/w) (3+(J+10)/t)) (4*(J+10)))
  have h₁ := lt_of_le_of_lt (le_trans (le_max_left _ _) (le_max_left _ _)) hn
  have h₂ := lt_of_le_of_lt (le_trans (le_max_right _ _) (le_max_left _ _)) hn
  have h₃ := lt_of_le_of_lt (le_max_right _ _) hn
  refine ⟨n,?_,?_,h₃⟩
  · have hh : (J+10)/w<(n:ℝ)-3 := by linarith
    have he := (div_lt_iff₀ hw).mp hh
    nlinarith
  · have hh : (J+10)/t<(n:ℝ)-3 := by linarith
    have he := (div_lt_iff₀ ht).mp hh
    nlinarith

theorem numerical_exponent_margins {J b t w : ℝ} {n N : ℕ}
    (hJ : 1≤J) (hb : 1/2≤b) (_ : 0<t) (htsmall : t<1/100)
    (hw : 0<w) (hwt : w<t)
    (hnw : J+10<w*((n:ℝ)-3)) (hnt : J+10<t*((n:ℝ)-3))
    (hnn : 4*(J+10)<(n:ℝ)) (hN : 10*(J+2)≤(N:ℝ)) :
    J+10≤((n:ℝ)+2)*w ∧ J+10≤((n:ℝ)+2)*(4*t-2*t) ∧ J+10≤N*b ∧
    2*(J+9)≤2*((J+10)-4*t) ∧ 2*(J+9)≤2*(4*t)*n-4*t*((n:ℝ)+1) ∧
    2*(J+8)≤2*(J+9)-2*w ∧ 2*(J+8)≤2*n*w ∧
    1/3≤b-w-4*t ∧ 0≤2*b-4*t ∧
    2*(J+8)≤((n:ℝ)+2)*(2*b-4*t) ∧ J+8≤(N:ℝ)/3 ∧
    2*(J+8)≤2*b+((n:ℝ)+1)*(2*b-4*t) := by
  have hn0 : (0:ℝ)≤n := Nat.cast_nonneg n
  have hN0 : (0:ℝ)≤N := Nat.cast_nonneg N
  have hNb : (N:ℝ)/2≤N*b := by nlinarith [mul_nonneg hN0 (sub_nonneg.mpr hb)]
  have hβ : 1/2≤2*b-4*t := by linarith
  have hnβ : ((n:ℝ)+2)/2≤((n:ℝ)+2)*(2*b-4*t) := by
    nlinarith [mul_nonneg (show 0≤(n:ℝ)+2 by positivity) (sub_nonneg.mpr hβ)]
  have hnβ' : ((n:ℝ)+1)/2≤((n:ℝ)+1)*(2*b-4*t) := by
    nlinarith [mul_nonneg (show 0≤(n:ℝ)+1 by positivity) (sub_nonneg.mpr hβ)]
  refine ⟨?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩ <;> nlinarith

end LogConcaveSampling

end

end

end OAI
end

section
-- module Solutions.OAIQ048_LC.LogConcave_Sampling_VelocityJointLip
attribute [-instance] _root_.OAI.LogConcaveSampling.LowerBound.couplingLaw_probability _root_.OAI.LogConcaveSampling.LowerBound.remainingHaar_probability _root_.OAI.LogConcaveSampling.LowerBound.roundRandomLaw_probability _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_invInvariant _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_isHaar _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_probability _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_rightInvariant _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_compactSpace _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_measurableInv _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_measurableMul _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_secondCountable _root_.OAI.LogConcaveSampling.MeanTree.instIsProbabilityMeasureRowTapeRowLaw _root_.OAI.LogConcaveSampling.OracleCompiler.topSeedLaw_probability _root_.OAI.LogConcaveSampling.noiseKernel_markov
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
namespace LogConcaveSampling
open Set MeasureTheory Quadrature
open scoped Classical BigOperators NNReal

theorem centeringVelocityJoint_lipschitz (n : ℕ) :
    ∃A B : ℝ≥0,∀{d : ℕ} {F : Point d → ℝ} {lam : ℝ≥0},
      Primitive F lam → ∀(x : Point d) {r T h ψ s : ℝ},0 < r →
        (lam:ℝ)*r^2 ≤ 1/2 → 0<T → T<1 → 0<h → 0<ψ → 0 < s →
        ∀m : ℕ,ψ*m ≤ 1 → A*probabilityMeanLipschitz lam r ≤ 1/2 →
        B*probabilityMeanLipschitz lam r ≤ 1/2 → ∀N : ℕ,∀e : ProbabilityNode T h (n+1),
      LipschitzWith (velocityJointLip n m A lam r T h ψ s)
        (centeringVelocityJoint F x r T h ψ s n m N e) := by
  obtain ⟨A,B,hAB⟩ := centeringVelocityPicard_lipschitz n
  refine ⟨A,B,?_⟩
  intro d F lam hF x r T h ψ s hr hl hT0 hT1 hh hψ hs m hψm hq hq' N e
  have h := (productPointEquiv_symm_lipschitz_two d d).comp
    ((hAB hF x hr hl hT0 hT1 hh hψ hs m hψm hq hq' N e).comp
      (productPointEquiv_lipschitz_one d d))
  have ht : Real.toNNReal ((Real.pi^2/2)*T*((lam:ℝ)*r))=
      ⟨(Real.pi^2/2)*T*((lam:ℝ)*r),by positivity⟩ := by
    apply NNReal.eq
    exact Real.coe_toNNReal _ (by positivity)
  convert! h using 1
  all_goals try with_reducible_and_instances rfl
  rw [velocityJointLip,ht,mul_one]

lemma velocityJointLip_coefficient {r s T h ψ : ℝ}
    (hr : 0 < r) (hs : 0 < s) (hψ : 0<ψ) (hT0 : 0<T) (hT1 : T<1)
    (lam A : ℝ≥0) (n m : ℕ) :
    (velocityJointLip n m A lam r T h ψ s:ℝ) ≤
      Real.pi^2*((lam:ℝ)*r/s)*
        (16*A*(∑i,|terminalQuadratureWeight T h n i|)*
          ((∑i : Fin (m+1),|derivativeWeight (angleNodes m) i|)/ψ)+1) := by
  have hh := mul_le_mul_of_nonneg_left
    (centeringVelocityPicard_lipschitz_coefficient (h:=h) hr hs hψ hT0 hT1 lam A n m) (by norm_num : (0:ℝ) ≤ 2)
  have ht : Real.toNNReal ((Real.pi^2/2)*T*((lam:ℝ)*r))=
      ⟨(Real.pi^2/2)*T*((lam:ℝ)*r),by positivity⟩ := by
    apply NNReal.eq
    exact Real.coe_toNNReal _ (by positivity)
  convert! hh using 1
  · rw [velocityJointLip,ht]
    rfl
  · ring

end LogConcaveSampling

end

end

end OAI
end

section
-- module Solutions.OAIQ048_LC.LogConcave_Complexity_VelocityNormalizedBudgetCalibrated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
namespace LogConcaveSampling
open Filter Set MeasureTheory Quadrature
open scoped Topology Classical BigOperators NNReal

theorem velocityNormalizedBudget_calibrated (k n N : ℕ) (Ap Ah Lp : ℝ≥0) (C J₀ D : ℝ)
    {lam : ℕ → ℝ≥0} {r T : ℕ → ℝ} {κ J b t w : ℝ}
    (hκ : 0<κ) (hJ : 1≤J) (hb : 1/2≤b) (ht : 0<t) (htsmall : t<1/100)
    (hw : 0<w) (hwt : w<t)
    (hnw : J+10<w*((n:ℝ)-3)) (hnt : J+10<t*((n:ℝ)-3))
    (hnn : 4*(J+10)<(n:ℝ)) (hN : 10*(J+2)≤(N:ℝ))
    (hl : LogPowerRate (fun d => (lam d:ℝ)*(r d)^2) (κ*b))
    (hT0 : ∀ᶠ d : ℕ in atTop,0<T d) (hT1 : ∀ᶠ d : ℕ in atTop,T d<1)
    (hRT : ∀ᶠ d : ℕ in atTop,((d:ℝ)^(-(κ*t)))^2≤1-(T d)^2)
    (hsmall : ∀ᶠ d : ℕ in atTop,(d:ℝ)^(-(κ*w))≤Real.log 2)
    (hlarge : ∀ᶠ d : ℕ in atTop,(d:ℝ)^(-(κ*w))≤logMeshLength (T d)) :
    LogPowerRate (fun d => velocityNormalizedBudget d k n n N (lam d) Ap Ah Lp
      (r d) ((d:ℝ)^(-(κ*t))) (T d) ((d:ℝ)^(-(κ*w))) ((d:ℝ)^(-(κ*(4*t)))) C J₀ D)
        (2*κ*(J+8)) := by
  obtain ⟨hp,hh,hiter,ha₁,ha₂,hv₁,hv₂,hlip,hbeta,hcq,hniter,hmq⟩ :=
    numerical_exponent_margins hJ hb ht htsmall hw hwt hnw hnt hnn hN
  have hB := kernelNormalizedTerm_rate k (n+1) N Ap Ah Lp (a:=κ*t) (b:=κ*w) (c:=κ*(4*t)) (e:=κ*(J+10)) (n:ℝ) hl
    (show κ*(J+10)≤((n+1:ℕ)+1:ℝ)*(κ*w) by
      have he := mul_le_mul_of_nonneg_left hp hκ.le
      push_cast; nlinarith)
    (show κ*(J+10)≤((n+1:ℕ)+1:ℝ)*(κ*(4*t)-2*(κ*t)) by
      have he := mul_le_mul_of_nonneg_left hh hκ.le
      push_cast; nlinarith)
    (show κ*(J+10)≤N*(κ*b) by
      have he := mul_le_mul_of_nonneg_left hiter hκ.le
      nlinarith)
  have hA := kernelActionNormalizedBudget_rate k (n+1) n N Ap Ah Lp C J₀ hB
    (show 2*κ*(J+9)≤2*(κ*(J+10)-κ*(4*t)) by
      have he := mul_le_mul_of_nonneg_left ha₁ hκ.le
      nlinarith)
    (show 2*κ*(J+9)≤2*(κ*(4*t))*n-4*(κ*t)*((n:ℝ)+1) by
      have he := mul_le_mul_of_nonneg_left ha₂ hκ.le
      nlinarith)
  obtain ⟨Dq,hDq,hDqu⟩ := exists_basisDerivative_budget (probabilityNodes (n+1))
  have hW := terminalQuadratureWeight_rate n Dq (by linarith) hDqu (κ*t) (κ*w)
    hT0 hT1 hRT hsmall hlarge
  exact velocityNormalizedBudget_rate k n n N Ap Ah Lp C J₀ D hW hA
    (logMeshLength_rate (κ*t) hT0 hT1 hRT)
    (by have he := mul_le_mul_of_nonneg_left hv₁ hκ.le; nlinarith)
    (by have he := mul_le_mul_of_nonneg_left hv₂ hκ.le; nlinarith)

lemma velocityJointLip_rate (n m : ℕ) (A : ℝ≥0)
    {lam : ℕ → ℝ≥0} {r s T : ℕ → ℝ} {b c u : ℝ}
    (hbc : 0≤b+c) (hr : ∀ᶠ d : ℕ in atTop,0 < r d) (hs : ∀ᶠ d : ℕ in atTop,0 < s d)
    (hT0 : ∀ᶠ d : ℕ in atTop,0<T d) (hT1 : ∀ᶠ d : ℕ in atTop,T d<1)
    (hW : LogPowerRate (fun d => ∑v,|terminalQuadratureWeight (T d) ((d:ℝ)^(-b)) n v|) (-b))
    (hα : LogPowerRate (fun d => (lam d:ℝ)*r d/s d) u) :
    LogPowerRate (fun d => (velocityJointLip n m A (lam d) (r d) (T d)
      ((d:ℝ)^(-b)) ((d:ℝ)^(-c)) (s d):ℝ)) (u-b-c) := by
  have hS := (LogPowerRate.inv_power c).const_mul (∑i,|derivativeWeight (angleNodes m) i|)
  have hQS := (hW.const_mul (16*(A:ℝ))).mul hS
  have h1 := (LogPowerRate.const 1).mono (show -b+-c≤0 by linarith)
  have he := (hα.const_mul (Real.pi^2)).mul (hQS.add h1)
  have he' : LogPowerRate (fun d => Real.pi^2*((lam d:ℝ)*r d/s d)*
      (16*(A:ℝ)*(∑v,|terminalQuadratureWeight (T d) ((d:ℝ)^(-b)) n v|)*
        ((∑i,|derivativeWeight (angleNodes m) i|)/(d:ℝ)^(-c))+1)) (u-b-c) := by
    convert! he using 1
    all_goals try with_reducible_and_instances rfl
    first | (simp only [div_eq_mul_inv]) | ring
  apply LogPowerRate.of_le he'
  · exact Eventually.of_forall (fun d => NNReal.coe_nonneg _)
  · filter_upwards [hr,hs,hT0,hT1,eventually_ge_atTop (1:ℕ)] with d hdr hds hdT0 hdT1 hd
    have hd0 : (0:ℝ)<d := by exact_mod_cast hd
    exact velocityJointLip_coefficient hdr hds (Real.rpow_pos_of_pos hd0 (-c)) hdT0 hdT1 (lam d) A n m

namespace LogPowerRate
lemma eventually_lt_const {f : ℕ → ℝ} {a C : ℝ} (hf : LogPowerRate f a)
    (ha : 0<a) (hC : 0<C) : ∀ᶠ d : ℕ in atTop, |f d|<C := by
  have he := hf.eventually_small (show a/2<a by linarith)
  have ht := (tendsto_rpow_neg_atTop (show 0<a/2 by linarith)).comp
    (tendsto_natCast_atTop_atTop (R:=ℝ))
  have hb := ht.eventually (gt_mem_nhds hC)
  filter_upwards [he,hb] with d hd hb
  exact hd.trans_lt hb
end LogPowerRate
end LogConcaveSampling

end

end

end OAI
end

section
-- module Solutions.OAIQ048_LC.LogConcave_Sampling_Correlation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
namespace LogConcaveSampling
open Filter
open scoped Topology

lemma centerScaleRate {α : ℕ → ℝ} {u a : ℝ} (hα : LogPowerRate α u) :
    LogPowerRate (fun d => (α d)^2*(((d:ℝ)^(-a))⁻¹)^4) (2*u-4*a) := by
  convert! (hα.pow 2).mul ((LogPowerRate.inv_power a).pow 4) using 1
  all_goals try with_reducible_and_instances rfl
  first | rfl | (norm_num; ring)

lemma centerStateQuadratureEnvelope_rate (n : ℕ) {α : ℕ → ℝ} {u a : ℝ}
    (hα : LogPowerRate α u) :
    LogPowerRate (fun d => centerStateQuadratureEnvelope n (α d) ((d:ℝ)^(-a)))
      ((n+2)*(2*u-4*a)) := by
  have he := (((centerScaleRate (a:=a) hα).pow (n+2)).const_mul (8*(singleCellBasisBudget n)^2)).mul_const
    (centeringStateBudget (n+2))
  simpa only [centerStateQuadratureEnvelope,Nat.cast_add,Nat.cast_ofNat] using he

lemma centerInitialEnvelope_rate {α : ℕ → ℝ} {u a : ℝ} (hα : LogPowerRate α u) :
    LogPowerRate (fun d => centerInitialEnvelope (α d) ((d:ℝ)^(-a))) (2*u-4*a) :=
  ((centerScaleRate hα).const_mul 2).mul_const (centeringStateBudget 1)

lemma centerStateEnvelope_rate (n N : ℕ) {α q E : ℕ → ℝ} {u a v e z : ℝ}
    (hα : LogPowerRate α u) (hq : LogPowerRate q v) (hE : LogPowerRate E e)
    (hz₁ : z≤2*u+e) (hz₂ : z≤(n+2)*(2*u-4*a))
    (hz₃ : z≤(2*N)*v+(2*u-4*a)) :
    LogPowerRate (fun d => centerStateEnvelope n N (α d) ((d:ℝ)^(-a)) (q d) (E d)) z := by
  have hp := ((hα.pow 2).const_mul (2*(centeringRowBudget n:ℝ)^2)).mul hE
  have hp' : LogPowerRate (fun d => 2*(centeringRowBudget n:ℝ)^2*(α d)^2*E d) z := by
    apply hp.mono
    norm_num
    exact hz₁
  have hs := ((centerStateQuadratureEnvelope_rate n hα).const_mul 2).mono hz₂
  have hq' := ((hq.pow (2*N)).const_mul 2).mul (centerInitialEnvelope_rate (a:=a) hα)
  have hq'' : LogPowerRate (fun d => 2*(q d)^(2*N)*centerInitialEnvelope (α d) ((d:ℝ)^(-a))) z := by
    apply hq'.mono
    push_cast
    exact hz₃
  exact ((hp'.add hs).const_mul 8).add hq''

lemma centerMeanEnvelope_rate (n : ℕ) {α Z : ℕ → ℝ} {u a z e : ℝ}
    (hα : LogPowerRate α u) (hZ : LogPowerRate Z z)
    (he₁ : e≤2*u+z) (he₂ : e≤2*u+(n+1)*(2*u-4*a)) :
    LogPowerRate (fun d => centerMeanEnvelope n (α d) ((d:ℝ)^(-a)) (Z d)) e := by
  have hp := ((hα.pow 2).const_mul (2*(centeringRowBudget n:ℝ)^2*(Real.pi^2/2)^2)).mul hZ
  have hp' : LogPowerRate (fun d => 2*(centeringRowBudget n:ℝ)^2*(Real.pi^2/2)^2*(α d)^2*Z d) e := by
    apply hp.mono
    norm_num
    exact he₁
  have hq := (((hα.pow 2).const_mul (8*(singleCellBasisBudget n)^2)).mul
    ((centerScaleRate (a:=a) hα).pow (n+1))).mul_const (centeringMeanBudget (n+1))
  have hq' : LogPowerRate (fun d => 8*(singleCellBasisBudget n)^2*(α d)^2*
      ((α d)^2*(((d:ℝ)^(-a))⁻¹)^4)^(n+1)*centeringMeanBudget (n+1)) e := by
    apply hq.mono
    push_cast
    exact he₂
  exact hp'.add hq'

theorem centeringEnvelopes_calibrated {α q E : ℕ → ℝ} {κ J b t w : ℝ} {n N : ℕ}
    (hκ : 0<κ) (hJ : 1≤J) (hb : 1/2≤b) (ht : 0<t) (htsmall : t<1/100)
    (hw : 0<w) (hwt : w<t)
    (hnw : J+10<w*((n:ℝ)-3)) (hnt : J+10<t*((n:ℝ)-3))
    (hnn : 4*(J+10)<(n:ℝ)) (hN : 10*(J+2)≤(N:ℝ))
    (hα : LogPowerRate α (κ*b)) (hq : LogPowerRate q (κ/3))
    (hE : LogPowerRate E (2*κ*(J+8))) :
    let Z := fun d => centerStateEnvelope n N (α d) ((d:ℝ)^(-(κ*t))) (q d) (E d)
    LogPowerRate Z (2*κ*(J+8)) ∧
    LogPowerRate (fun d => centerMeanEnvelope n (α d) ((d:ℝ)^(-(κ*t))) (Z d)) (2*κ*(J+8)) := by
  intro Z
  obtain ⟨hp,hh,hiter,ha₁,ha₂,hv₁,hv₂,hlip,hbeta,hcq,hniter,hmq⟩ :=
    numerical_exponent_margins hJ hb ht htsmall hw hwt hnw hnt hnn hN
  have hκb : 0≤κ*b := mul_nonneg hκ.le (by linarith)
  have hκβ := mul_nonneg hκ.le hbeta
  have hZ : LogPowerRate Z (2*κ*(J+8)) := by
    apply centerStateEnvelope_rate n N hα hq hE
    · linarith
    · have he := mul_le_mul_of_nonneg_left hcq hκ.le
      nlinarith
    · have he := mul_le_mul_of_nonneg_left hniter hκ.le
      nlinarith
  refine ⟨hZ,?_⟩
  apply centerMeanEnvelope_rate n hα hZ
  · linarith
  · have he := mul_le_mul_of_nonneg_left hmq hκ.le
    nlinarith
end LogConcaveSampling

end

end

section

noncomputable section
namespace LogConcaveSampling
open Filter Quadrature
open scoped Topology

lemma sourceCorrelation_eventually {a : ℝ} (ha : 0<a) :
    ∀ᶠ d : ℕ in atTop,0 < sourceCorrelation a d ∧ sourceCorrelation a d<1 ∧
      ((d:ℝ)^(-a))^2=1-(sourceCorrelation a d)^2 := by
  have ht := (tendsto_rpow_neg_atTop ha).comp (tendsto_natCast_atTop_atTop (R:=ℝ))
  have he := ht.eventually (gt_mem_nhds (by norm_num : (0:ℝ)<1))
  filter_upwards [he,eventually_ge_atTop (1:ℕ)] with d hd hd1
  have hd0 : (0:ℝ)<d := by exact_mod_cast hd1
  change (d:ℝ)^(-a)<1 at hd
  have hp := Real.rpow_pos_of_pos hd0 (-a)
  have hs : 0<1-((d:ℝ)^(-a))^2 := by nlinarith
  have hsq := Real.sq_sqrt hs.le
  refine ⟨Real.sqrt_pos.mpr hs,?_,?_⟩
  · change Real.sqrt _<1
    nlinarith [Real.sqrt_nonneg (1-((d:ℝ)^(-a))^2)]
  · change ((d:ℝ)^(-a))^2=1-Real.sqrt (1-((d:ℝ)^(-a))^2)^2
    linarith

lemma sourceCorrelation_tendsto {a : ℝ} (ha : 0<a) :
    Tendsto (sourceCorrelation a) atTop (nhds 1) := by
  have ht := (tendsto_rpow_neg_atTop ha).comp (tendsto_natCast_atTop_atTop (R:=ℝ))
  change Tendsto (fun d : ℕ => Real.sqrt (1-((d:ℝ)^(-a))^2)) atTop (nhds 1)
  simpa only [Function.comp_def,zero_pow (by omega : (2:ℕ)≠0),sub_zero,Real.sqrt_one] using
    ((tendsto_const_nhds (x:=(1:ℝ))).sub (ht.pow 2)).sqrt

lemma sourceMesh_eventually {a b : ℝ} (ha : 0<a) (hb : 0<b) :
    ∀ᶠ d : ℕ in atTop,(d:ℝ)^(-b) ≤ Real.log 2 ∧
      (d:ℝ)^(-b) ≤ logMeshLength (sourceCorrelation a d) := by
  have ht := (tendsto_rpow_neg_atTop hb).comp (tendsto_natCast_atTop_atTop (R:=ℝ))
  have he := ht.eventually (gt_mem_nhds (Real.log_pos (by norm_num : (1:ℝ)<2)))
  have hc := (sourceCorrelation_tendsto ha).eventually (lt_mem_nhds (by norm_num : (1/2:ℝ)<1))
  filter_upwards [he,hc,sourceCorrelation_eventually ha] with d hd hcd hp
  refine ⟨hd.le,?_⟩
  apply hd.le.trans
  unfold logMeshLength
  rw [←Real.log_inv]
  apply Real.log_le_log (by norm_num)
  rw [inv_eq_one_div]
  apply (le_div_iff₀ (by linarith : 0<1-sourceCorrelation a d)).mpr
  linarith

lemma sourceAngle_eventually {a : ℝ} (ha : 0<a) (n : ℕ) :
    ∀ᶠ d : ℕ in atTop,(d:ℝ)^(-a)*(n:ℝ) ≤ 1 := by
  have ht := ((tendsto_rpow_neg_atTop ha).comp
    (tendsto_natCast_atTop_atTop (R:=ℝ))).mul_const (n:ℝ)
  have ht' : Tendsto (fun d : ℕ => (d:ℝ)^(-a)*(n:ℝ)) atTop (nhds 0) := by
    simpa only [Function.comp_def,zero_mul] using ht
  exact (ht'.eventually (gt_mem_nhds (by norm_num : (0:ℝ)<1))).mono (fun _ h => h.le)
end LogConcaveSampling

end

end

section

noncomputable section
namespace LogConcaveSampling
open Filter Quadrature
open scoped Topology Classical BigOperators NNReal

lemma probabilityMeanLipschitz_rate {lam : ℕ → ℝ≥0} {r : ℕ → ℝ} {u : ℝ}
    (hl : LogPowerRate (fun d => (lam d:ℝ)*(r d)^2) u) (A : ℝ≥0) :
    LogPowerRate (fun d => (A*probabilityMeanLipschitz (lam d) (r d):ℝ≥0)) u := by
  apply (hl.const_mul ((A:ℝ)*(Real.pi^2/2))).congr
  apply Eventually.of_forall
  intro d
  change (A:ℝ)*(Real.pi^2/2)*((lam d:ℝ)*(r d)^2) =
    (A:ℝ)*((Real.pi^2/2)*(lam d:ℝ)*(r d)^2)
  ring

theorem centeringScalarCalibration (k n N : ℕ) (A Ap Ah Lp contraction : ℝ≥0) (C J₀ D : ℝ)
    {lam : ℕ → ℝ≥0} {r s : ℕ → ℝ} {κ J b t w : ℝ}
    (hκ : 0<κ) (hJ : 1≤J) (hb : 1/2≤b) (ht : 0<t) (htsmall : t<1/100)
    (hw : 0<w) (hwt : w<t)
    (hnw : J+10<w*((n:ℝ)-3)) (hnt : J+10<t*((n:ℝ)-3))
    (hnn : 4*(J+10)<(n:ℝ)) (hN : 10*(J+2)≤(N:ℝ))
    (hl : LogPowerRate (fun d => (lam d:ℝ)*(r d)^2) (κ*b))
    (hα : LogPowerRate (fun d => (lam d:ℝ)*r d/s d) (κ*b))
    (hr : ∀ᶠ d : ℕ in atTop,0 < r d) (hs : ∀ᶠ d : ℕ in atTop,0 < s d) :
    let R := fun d : ℕ => (d:ℝ)^(-(κ*t))
    let T := sourceCorrelation (κ*t)
    let h := fun d : ℕ => (d:ℝ)^(-(κ*w))
    let ψ := fun d : ℕ => (d:ℝ)^(-(κ*(4*t)))
    let E := fun d => velocityNormalizedBudget d k n n N (lam d) Ap Ah Lp (r d) (R d) (T d) (h d) (ψ d) C J₀ D
    let q := fun d => centeringRowBudget n*velocityJointLip n n A (lam d) (r d) (T d) (h d) (ψ d) (s d)
    let Z := fun d => centerStateEnvelope n N ((lam d:ℝ)*r d/s d) (R d) (q d:ℝ) (E d)
    ∀ᶠ d : ℕ in atTop,
      (lam d:ℝ)*(r d)^2≤1/2 ∧ contraction*probabilityMeanLipschitz (lam d) (r d)≤1/2 ∧
      q d≤1/2 ∧ Z d≤(d:ℝ)^(-(2*κ*J)) ∧
      centerMeanEnvelope n ((lam d:ℝ)*r d/s d) (R d) (Z d)≤(d:ℝ)^(-(2*κ*J)) := by
  intro R T h ψ E q Z
  have hκt := mul_pos hκ ht
  have hκw := mul_pos hκ hw
  have hκb : 0<κ*b := mul_pos hκ (by linarith)
  have hT := sourceCorrelation_eventually hκt
  have hT0 : ∀ᶠ d : ℕ in atTop,0<T d := hT.mono (fun _ h => h.1)
  have hT1 : ∀ᶠ d : ℕ in atTop,T d<1 := hT.mono (fun _ h => h.2.1)
  have hRT : ∀ᶠ d : ℕ in atTop,(R d)^2≤1-(T d)^2 := hT.mono (fun _ h => h.2.2.le)
  have hmesh := sourceMesh_eventually hκt hκw
  have hsmall := hmesh.mono (fun _ hd => hd.1)
  have hlarge := hmesh.mono (fun _ hd => hd.2)
  have hE : LogPowerRate E (2*κ*(J+8)) := velocityNormalizedBudget_calibrated k n N Ap Ah Lp C J₀ D
    hκ hJ hb ht htsmall hw hwt hnw hnt hnn hN hl hT0 hT1 hRT hsmall hlarge
  obtain ⟨Dq,hDq,hDqu⟩ := exists_basisDerivative_budget (probabilityNodes (n+1))
  have hW := terminalQuadratureWeight_rate n Dq (by linarith) hDqu (κ*t) (κ*w) hT0 hT1 hRT hsmall hlarge
  have hlip := velocityJointLip_rate n n A (show 0≤κ*w+κ*(4*t) by positivity)
    hr hs hT0 hT1 hW hα
  have hmargin : κ/3≤κ*b-κ*w-κ*(4*t) := by
    have hex := (numerical_exponent_margins hJ hb ht htsmall hw hwt hnw hnt hnn hN).2.2.2.2.2.2.2.1
    have he := mul_le_mul_of_nonneg_left hex hκ.le
    nlinarith
  have hq : LogPowerRate (fun d => (q d:ℝ)) (κ/3) := by
    simpa only [q,NNReal.coe_mul] using (hlip.const_mul (centeringRowBudget n:ℝ)).mono hmargin
  have hz := centeringEnvelopes_calibrated hκ hJ hb ht htsmall hw hwt hnw hnt hnn hN hα hq hE
  have hze := hz.1.eventually_small (show 2*κ*J<2*κ*(J+8) by nlinarith)
  have hme := hz.2.eventually_small (show 2*κ*J<2*κ*(J+8) by nlinarith)
  have hle := hl.eventually_lt_const hκb (by norm_num : (0:ℝ)<1/2)
  have hc := (probabilityMeanLipschitz_rate hl contraction).eventually_lt_const hκb (by norm_num : (0:ℝ)<1/2)
  have hqe := hq.eventually_lt_const (by linarith) (by norm_num : (0:ℝ)<1/2)
  filter_upwards [hze,hme,hle,hc,hqe] with d hzd hmd hld hcd hqd
  refine ⟨(le_abs_self _).trans hld.le,?_,?_,(le_abs_self _).trans hzd, (le_abs_self _).trans hmd⟩
  · exact_mod_cast (le_abs_self _).trans hcd.le
  · exact_mod_cast (le_abs_self _).trans hqd.le
end LogConcaveSampling

end

end

end OAI
end

section
-- module Solutions.OAIQ048_LC.LogConcave_Sampling_SampleCorrelation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
namespace LogConcaveSampling
open Filter MeasureTheory ProbabilityTheory
open scoped Classical NNReal

lemma samplingEnvelope_rate (k n N : ℕ) (C : ℝ) {q : ℕ → ℝ} {κ J b w : ℝ}
    (hκ : 0<κ) (hJ : 1≤J) (hb : 1/2≤b) (hw : 0<w)
    (hn : J+10<w*((n:ℝ)-3)) (hN : 10*(J+2)≤(N:ℝ))
    (hq : LogPowerRate q (κ*b)) :
    LogPowerRate (fun d => samplingEnvelope d k n N C (q d) ((d:ℝ)^(-(κ*w)))) (2*κ*(J+9)) := by
  have hn' : κ*(J+9)≤(n+1:ℕ)*(κ*w) := by
    push_cast
    nlinarith
  have hNb : (N:ℝ)/2≤N*b := by nlinarith [mul_nonneg (Nat.cast_nonneg (α:=ℝ) N) (sub_nonneg.mpr hb)]
  have hN' : κ*(J+9)≤N*(κ*b) := by nlinarith
  have hp := (((LogPowerRate.log.pow k).const_mul (2*C)).mul
    (((LogPowerRate.power (κ*w)).const_mul 2).pow (n+1)))
  have hp' : LogPowerRate (fun d => 2*C*dimensionLog d^k*(2*(d:ℝ)^(-(κ*w)))^(n+1)) (κ*(J+9)) := by
    have hp₀ : LogPowerRate (fun d => 2*C*dimensionLog d^k*(2*(d:ℝ)^(-(κ*w)))^(n+1)) ((n+1:ℕ)*(κ*w)) := by
      simpa only [mul_zero,zero_add] using hp
    exact hp₀.mono hn'
  have hq' := ((hq.pow N).const_mul circuitGrowthConstant).mono hN'
  have he := ((hp'.add hq').pow 2).const_mul 4
  convert he using 1 <;> first | rfl | (norm_num; ring)

theorem sampleScalarCalibration_uniform (k n N ksize : ℕ) (A : ℝ≥0) (C : ℝ)
    {S κ J b w : ℝ} (hS : 0≤S) (hκ : 0<κ) (hJ : 1≤J) (hb : 1/2≤b) (hw : 0<w)
    (hn : J+10<w*((n:ℝ)-3)) (hN : 10*(J+2)≤(N:ℝ)) :
    ∀ᶠ d : ℕ in atTop,∀lam : ℝ≥0,∀r : ℝ,0 < r →
      (lam:ℝ)*r^2≤S*dimensionLog d^ksize*(d:ℝ)^(-(κ*b)) →
      (lam:ℝ)*r^2≤1/2 ∧ A*probabilityMeanLipschitz lam r≤1/2 ∧
      samplingEnvelope d k n N C (A*probabilityMeanLipschitz lam r) ((d:ℝ)^(-(κ*w)))≤
        (d:ℝ)^(-(2*κ*J)) := by
  have hseq : ∀ᶠ d : ℕ in atTop,∀v : ℝ≥0 × ℝ,
      (0<v.2 ∧ (v.1:ℝ)*v.2^2≤S*dimensionLog d^ksize*(d:ℝ)^(-(κ*b))) →
      (v.1:ℝ)*v.2^2≤1/2 ∧ A*probabilityMeanLipschitz v.1 v.2≤1/2 ∧
      samplingEnvelope d k n N C (A*probabilityMeanLipschitz v.1 v.2) ((d:ℝ)^(-(κ*w)))≤
        (d:ℝ)^(-(2*κ*J)) := by
    apply eventually_forall_of_sequences
    · exact Eventually.of_forall (fun d => ⟨(0,1),by
        refine ⟨by norm_num,?_⟩
        simp only [NNReal.coe_zero,zero_mul]
        positivity [dimensionLog_nonneg d]⟩)
    · intro f hf
      have hl : LogPowerRate (fun d => ((f d).1:ℝ)*(f d).2^2) (κ*b) :=
        logPowerRate_of_envelope (Eventually.of_forall (fun d => by positivity)) (hf.mono (fun _ h => h.2))
      have hq := probabilityMeanLipschitz_rate hl A
      have he := (samplingEnvelope_rate k n N C hκ hJ hb hw hn hN hq).eventually_small
        (show 2*κ*J<2*κ*(J+9) by nlinarith)
      have hkb : 0<κ*b := mul_pos hκ (by linarith)
      have hl' := hl.eventually_lt_const hkb (by norm_num : (0:ℝ)<1/2)
      have hq' := hq.eventually_lt_const hkb (by norm_num : (0:ℝ)<1/2)
      filter_upwards [he,hl',hq'] with d hd hld hqd
      refine ⟨(le_abs_self _).trans hld.le,?_,(le_abs_self _).trans hd⟩
      exact_mod_cast (le_abs_self _).trans hqd.le
  filter_upwards [hseq] with d hd lam r hr hl
  exact hd (lam,r) ⟨hr,hl⟩

end LogConcaveSampling

end

end

end OAI
end

section
-- module Solutions.OAIQ048_LC.LogConcave_OraclePrograms_MeanSize
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

lemma MeanSize.nonneg {lam q r σ : ℝ} (hlam : 0 ≤ lam) (h : MeanSize lam q r σ) : 0 ≤ q :=
  (mul_nonneg hlam (sq_nonneg r)).trans h.2.2.2.1
lemma SampleSize.nonneg {lam q r η : ℝ} (hlam : 0 ≤ lam) (h : SampleSize lam q r η) : 0 ≤ q := by
  have hp := (mul_nonneg hlam (sq_nonneg r)).trans h.2.2.2.2
  exact nonneg_of_mul_nonneg_left hp h.2.2.1

end LogConcaveSampling.OracleCompiler

end

end

end OAI
end

section
-- module Solutions.OAIQ048_LC.LogConcave_OraclePrograms_CenteringMeanCircuitFull
attribute [-instance] _root_.OAI.LogConcaveSampling.LowerBound.couplingLaw_probability _root_.OAI.LogConcaveSampling.LowerBound.remainingHaar_probability _root_.OAI.LogConcaveSampling.LowerBound.roundRandomLaw_probability _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_invInvariant _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_isHaar _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_probability _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_rightInvariant _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_compactSpace _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_measurableInv _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_measurableMul _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_secondCountable _root_.OAI.LogConcaveSampling.MeanTree.instIsProbabilityMeasureRowTapeRowLaw _root_.OAI.LogConcaveSampling.OracleCompiler.topSeedLaw_probability _root_.OAI.LogConcaveSampling.noiseKernel_markov
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
namespace LogConcaveSampling
open Set MeasureTheory Quadrature ProbabilityTheory
open scoped Classical BigOperators NNReal

theorem centeringMeanCircuit_full_rms (n : ℕ) :
    ∃A B Ap Ah Lp Lh : ℝ≥0,∃C J D : ℝ,0 ≤ C ∧ 1 ≤ J ∧ 1 ≤ D ∧ ∃k : ℕ,
    ∀{d : ℕ} {F : Point d → ℝ} {lam : ℝ≥0},∀hF : Primitive F lam,
    ∀(x : Point d) {r : ℝ},∀hr : 0 < r,r ≤ 1 → 0<lam →
    ∀hl : (lam:ℝ)*r^2 ≤ 1/2,(lam:ℝ)*r ≤ 1 → 1 ≤ d →
    ∀{T h : ℝ},∀hT0 : 0<T,∀hT1 : T<1,∀hh : 0<h,h ≤ Real.log 2 → h ≤ logMeshLength T →
    Ap*probabilityMeanLipschitz lam r ≤ 1/2 → Ah*probabilityMeanLipschitz lam r ≤ 1/2 →
    Lp*probabilityMeanLipschitz lam r ≤ 1/2 → Lh*probabilityMeanLipschitz lam r ≤ 1/2 →
    A*probabilityMeanLipschitz lam r ≤ 1/2 → B*probabilityMeanLipschitz lam r ≤ 1/2 →
    ∀N : ℕ,∀R : ℝ,0<R → R^2 ≤ 1-T^2 → ∀m : ℕ,1 ≤ m → ∀ψ : ℝ,0<ψ → ψ*m ≤ 1 →
    ∀s : ℝ,0 < s → ∀nc Nc : ℕ,0<nc →
    centeringRowBudget nc*velocityJointLip n m A lam r T h ψ s ≤ 1/2 →
    let e := probabilityEndpoint hT0 hT1 hh (n+1)
    let E := velocityNormalizedBudget d k n m N lam Ap Ah Lp r R T h ψ C J D
    let K := velocityJointLip n m A lam r T h ψ s
    let Z := centerStateEnvelope nc Nc ((lam:ℝ)*r/s) R (centeringRowBudget nc*K:ℝ≥0) E
    ∃X : StationaryPath (gibbs (centeringPotential F x r T))
      (skewLieField (centeringPotential F x r T)
        (jointSkew (centeringKernel hF x hr hl hT0.le hT1) s)),
      (∀i,Integrable (fun y => ‖stationaryPicard nc Nc
        (centeringVelocityJoint F x r T h ψ s n m N e) y i-X.path y (probabilityNodes nc i)‖^2)
        (gibbs (centeringPotential F x r T))) ∧
      (∀i,(∫y,‖stationaryPicard nc Nc
        (centeringVelocityJoint F x r T h ψ s n m N e) y i-X.path y (probabilityNodes nc i)‖^2
          ∂gibbs (centeringPotential F x r T)) ≤ (circuitD F x)^2*Z) ∧
      Measurable (stationaryMeanTarget hF x hr hl hT0.le hT1 X) ∧
      (gibbs (centeringPotential F x r T)).map (stationaryMeanTarget hF x hr hl hT0.le hT1 X)=
        (stdGaussian (Point d)).map (fun g => primitiveExpectedField F x r+s • g) ∧
      Integrable (fun y => ‖centeringMeanCircuit F x r T h ψ s n m N nc Nc e y-
        stationaryMeanTarget hF x hr hl hT0.le hT1 X y‖^2) (gibbs (centeringPotential F x r T)) ∧
      (∫y,‖centeringMeanCircuit F x r T h ψ s n m N nc Nc e y-
        stationaryMeanTarget hF x hr hl hT0.le hT1 X y‖^2 ∂gibbs (centeringPotential F x r T)) ≤
        (s*circuitD F x)^2*centerMeanEnvelope nc ((lam:ℝ)*r/s) R Z := by
  obtain ⟨A,B,hLip⟩ := centeringVelocityJoint_lipschitz n
  obtain ⟨Ap,Ah,Lp,Lh,C,J,D,hC,hJ,hD,k,hRms⟩ := centeringVelocityJoint_full_rms n
  refine ⟨A,B,Ap,Ah,Lp,Lh,C,J,D,hC,hJ,hD,k,?_⟩
  intro d F lam hF x r hr hr1 hlam hl hL hd T h hT0 hT1 hh hsmall hlarge hp hharm hlp hlh ha hb N R hR hRT m hm ψ hψ hψm s hs nc Nc hnc hq e E K Z
  have hhat := hLip hF x hr hl hT0 hT1 hh hψ hs m hψm ha hb N e
  have hv := hRms hF x hr hlam hl hd hT0 hT1 hh hsmall hlarge hp hharm hlp hlh N R hR hRT m hm ψ hψ hψm s
  have hE : 0 ≤ E := velocityNormalizedBudget_nonneg d k n m N lam Ap Ah Lp r R T h ψ C J D hR.le
  have hZ : 0 ≤ Z := centerStateEnvelope_nonneg nc Nc _ _ _ E (NNReal.coe_nonneg _) hE
  have hvel := velocityRmsBudget_normalized hF x Ap Ah Lp (C:=C) (J:=J) (D:=D) hr hr1 hR hT0 hT1 hh hψ hs hC (show 0≤J by linarith only [hJ]) hl hL k n m N
  obtain ⟨X⟩ := exists_centering_stationaryPath hF x hr hlam hl hT0.le hT1 hs
  have hstate (i : Fin (nc+1)) := centeringPicard_state_rms hF x hr hlam hl hR hRT hT0.le hT1 hs X
    n m N nc Nc hnc e hhat hq (show 0 ≤ (((lam:ℝ)*r/s)*circuitD F x)^2*E by positivity)
    hv.1 (hv.2.trans hvel) i
  have hstate' (i : Fin (nc+1)) : (∫y,‖stationaryPicard nc Nc
      (centeringVelocityJoint F x r T h ψ s n m N e) y i-X.path y (probabilityNodes nc i)‖^2
        ∂gibbs (centeringPotential F x r T)) ≤ (circuitD F x)^2*Z :=
    (hstate i).2.trans (centeringPicardBudget_normalized F x nc Nc lam K r R s E hE)
  have hmean := centeringMeanCircuit_rms hF x hr hlam hl hR hRT hT0.le hT1 hs X
    n m N nc Nc hnc e hhat (show 0 ≤ (circuitD F x)^2*Z by positivity)
    (fun i => (hstate i).1) hstate'
  refine ⟨X,(fun i => (hstate i).1),hstate',?_,
    stationaryMeanTarget_law hF x hr hlam hl hT0.le hT1 hs X,hmean.1,?_⟩
  · have he : stationaryMeanTarget hF x hr hl hT0.le hT1 X=
        fun y => primitiveExpectedField F x r+s • (productPointEquiv d d (X.path y 1)).2 := by
      funext y
      exact stationaryMeanTarget_identity hF x hr hlam hl hT0.le hT1 hs X y
    rw [he]
    exact measurable_const.add (((productPointEquiv d d).continuous.measurable.comp (X.measurable_slice 1)).snd.const_smul s)
  · exact hmean.2.trans (centeringMeanBudget_normalized F x nc lam r R hs hT0.le hT1.le hZ)
end LogConcaveSampling

end

end

end OAI
end

section
-- module Solutions.OAIQ048_LC.LogConcave_Sampling_NumericalScalars
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
namespace LogConcaveSampling
open Filter Quadrature
open scoped Classical NNReal

theorem centeringScalarCalibration_uniform (k n N ksize : ℕ)
    (A Ap Ah Lp contraction : ℝ≥0) (C J₀ D : ℝ) {S κ J b t w : ℝ}
    (hS : 0≤S) (hκ : 0<κ) (hJ : 1≤J) (hb : 1/2≤b) (ht : 0<t) (htsmall : t<1/100)
    (hw : 0<w) (hwt : w<t)
    (hnw : J+10<w*((n:ℝ)-3)) (hnt : J+10<t*((n:ℝ)-3))
    (hnn : 4*(J+10)<(n:ℝ)) (hN : 10*(J+2)≤(N:ℝ)) :
    ∀ᶠ d : ℕ in atTop,∀v : NumericalScalars,
      v.small (S*dimensionLog d^ksize*(d:ℝ)^(-(κ*b))) →
      centeringCalibrationGood d k n N A Ap Ah Lp contraction C J₀ D κ J t w v := by
  let : Nonempty NumericalScalars := ⟨⟨0,1,1⟩⟩
  apply eventually_forall_of_sequences
  · exact Eventually.of_forall (fun d => ⟨⟨0,1,1⟩,by
      refine ⟨by norm_num,by norm_num,?_,?_⟩ <;>
      simp only [NNReal.coe_zero,zero_mul,zero_div] <;>
      positivity [dimensionLog_nonneg d]⟩)
  · intro f hf
    have hl : LogPowerRate (fun d => ((f d).lam:ℝ)*(f d).r^2) (κ*b) :=
      logPowerRate_of_envelope (Eventually.of_forall (fun d => by positivity))
        (hf.mono (fun _ h => h.2.2.1))
    have hα : LogPowerRate (fun d => ((f d).lam:ℝ)*(f d).r/(f d).s) (κ*b) := by
      apply logPowerRate_of_envelope
      · exact hf.mono (fun _ h => by positivity [h.1,h.2.1])
      · exact hf.mono (fun _ h => h.2.2.2)
    exact centeringScalarCalibration k n N A Ap Ah Lp contraction C J₀ D hκ hJ hb ht htsmall
      hw hwt hnw hnt hnn hN hl hα (hf.mono (fun _ h => h.1)) (hf.mono (fun _ h => h.2.1))
end LogConcaveSampling

end

end

end OAI
end

section
-- module Solutions.OAIQ048_LC.LogConcave_OraclePrograms_CalibratedMeanCircuit
attribute [-instance] _root_.OAI.LogConcaveSampling.LowerBound.couplingLaw_probability _root_.OAI.LogConcaveSampling.LowerBound.remainingHaar_probability _root_.OAI.LogConcaveSampling.LowerBound.roundRandomLaw_probability _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_invInvariant _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_isHaar _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_probability _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_rightInvariant _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_compactSpace _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_measurableInv _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_measurableMul _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_secondCountable _root_.OAI.LogConcaveSampling.MeanTree.instIsProbabilityMeasureRowTapeRowLaw _root_.OAI.LogConcaveSampling.OracleCompiler.topSeedLaw_probability _root_.OAI.LogConcaveSampling.noiseKernel_markov
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
namespace LogConcaveSampling
open Filter Set MeasureTheory Quadrature ProbabilityTheory
open scoped Classical BigOperators NNReal

theorem exists_calibrated_mean_circuit {κ J b t : ℝ}
    (hκ : 0<κ) (hJ : 1≤J) (hb : 1/2≤b) (ht : 0<t) (htsmall : t<1/100) :
    ∀{w : ℝ},0<w → w<t → ∃n : ℕ,
      J+10<w*((n:ℝ)-3) ∧ J+10<t*((n:ℝ)-3) ∧ 4*(J+10)<(n:ℝ) ∧
      ∀{S : ℝ},0≤S → ∀ksize : ℕ,∀ᶠ d : ℕ in atTop,
      let T := sourceCorrelation (κ*t) d
      let h := (d:ℝ)^(-(κ*w))
      let ψ := (d:ℝ)^(-(κ*(4*t)))
      ∃hT0 : 0<T,∃hT1 : T<1,∃hh : 0<h,
      ∀{F : Point d → ℝ} {lam : ℝ≥0},∀hF : Primitive F lam,∀x : Point d,
      ∀{r s : ℝ},∀hr : 0 < r,r≤1 → 0<lam → (lam:ℝ)*r≤1 → 0 < s →
      (lam:ℝ)*r^2≤S*dimensionLog d^ksize*(d:ℝ)^(-(κ*b)) →
      (lam:ℝ)*r/s≤S*dimensionLog d^ksize*(d:ℝ)^(-(κ*b)) →
      ∃hl : (lam:ℝ)*r^2≤1/2,
      CalibratedMeanCircuit (ψ:=ψ) (s:=s) hF x hr hl hT0 hT1 hh n (numericalLayerCount J)
        ((d:ℝ)^(-(2*κ*J))) := by
  intro w hw hwt
  obtain ⟨n,hnw,hnt,hnn⟩ := exists_numerical_order (J:=J) ht hw
  have hn : 0<n := by
    have he : (0:ℝ)<n := by linarith
    exact_mod_cast he
  have hn1 : 1≤n := hn
  obtain ⟨A,B,Ap,Ah,Lp,Lh,C,J₀,D,hC,hJ₀,hD,k,hproducer⟩ := centeringMeanCircuit_full_rms n
  let U := A+B+Ap+Ah+Lp+Lh
  have hU : A≤U ∧ B≤U ∧ Ap≤U ∧ Ah≤U ∧ Lp≤U ∧ Lh≤U := by
    dsimp only [U]
    have ha : (0:ℝ≥0)≤A := bot_le
    have hb : (0:ℝ≥0)≤B := bot_le
    have hc : (0:ℝ≥0)≤Ap := bot_le
    have hd : (0:ℝ≥0)≤Ah := bot_le
    have he : (0:ℝ≥0)≤Lp := bot_le
    have hf : (0:ℝ≥0)≤Lh := bot_le
    constructor <;> first | nlinarith | skip
    constructor <;> first | nlinarith | skip
    constructor <;> first | nlinarith | skip
    constructor <;> first | nlinarith | skip
    constructor <;> nlinarith
  refine ⟨n,hnw,hnt,hnn,?_⟩
  intro S hS ksize
  have hc := centeringScalarCalibration_uniform k n (numericalLayerCount J) ksize A Ap Ah Lp U C J₀ D
    hS hκ hJ hb ht htsmall hw hwt hnw hnt hnn (numericalLayerCount_bound J)
  have hT := sourceCorrelation_eventually (mul_pos hκ ht)
  have hmesh := sourceMesh_eventually (mul_pos hκ ht) (mul_pos hκ hw)
  have hangle := sourceAngle_eventually (show 0<κ*(4*t) by positivity) n
  filter_upwards [hc,hT,hmesh,hangle,eventually_ge_atTop (1:ℕ)] with d hdc hdT hdmesh hdangle hd
  intro T h ψ
  let R := (d:ℝ)^(-(κ*t))
  have hd0 : (0:ℝ)<d := by exact_mod_cast hd
  have hh : 0<h := Real.rpow_pos_of_pos hd0 _
  have hR : 0<R := Real.rpow_pos_of_pos hd0 _
  have hψ : 0<ψ := Real.rpow_pos_of_pos hd0 _
  refine ⟨hdT.1,hdT.2.1,hh,?_⟩
  intro F lam hF x r s hr hr1 hlam hL hs hl₀ hα
  have hgood := hdc ⟨lam,r,s⟩ ⟨hr,hs,hl₀,hα⟩
  rcases hgood with ⟨hl,hcontr,hq,hz,hm⟩
  have bound {K : ℝ≥0} (hK : K≤U) : K*probabilityMeanLipschitz lam r≤1/2 :=
    (mul_le_mul_of_nonneg_right hK bot_le).trans hcontr
  refine ⟨hl,?_⟩
  obtain ⟨X,hsi,hsb,hmeas,hlaw,hmi,hmb⟩ := hproducer hF x hr hr1 hlam hl hL hd
    hdT.1 hdT.2.1 hh hdmesh.1 hdmesh.2
    (bound hU.2.2.1) (bound hU.2.2.2.1) (bound hU.2.2.2.2.1) (bound hU.2.2.2.2.2)
    (bound hU.1) (bound hU.2.1) (numericalLayerCount J) R hR hdT.2.2.le n hn1 ψ hψ hdangle
    s hs n (numericalLayerCount J) hn hq
  refine ⟨X,hsi,?_,hmeas,hlaw,hmi,?_⟩
  · intro i
    exact (hsb i).trans (mul_le_mul_of_nonneg_left hz (sq_nonneg _))
  · exact hmb.trans (mul_le_mul_of_nonneg_left hm (sq_nonneg _))
end LogConcaveSampling

end

end

end OAI
end

section
-- module Solutions.OAIQ048_LC.LogConcave_OraclePrograms_StandaloneCorrect
attribute [-instance] _root_.OAI.LogConcaveSampling.LowerBound.couplingLaw_probability _root_.OAI.LogConcaveSampling.LowerBound.remainingHaar_probability _root_.OAI.LogConcaveSampling.LowerBound.roundRandomLaw_probability _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_invInvariant _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_isHaar _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_probability _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_rightInvariant _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_compactSpace _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_measurableInv _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_measurableMul _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_secondCountable _root_.OAI.LogConcaveSampling.OracleCompiler.topSeedLaw_probability _root_.OAI.LogConcaveSampling.noiseKernel_markov
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
namespace LogConcaveSampling
open Filter MeasureTheory ProbabilityTheory
open scoped Classical NNReal

theorem calibrated_sample_circuit_order {κ J b w : ℝ} (hκ : 0<κ) (hJ : 1≤J)
    (hb : 1/2≤b) (hw : 0<w) (n : ℕ) (hn : 0<n)
    (hnw : J+10<w*((n:ℝ)-3)) :
      ∀{S : ℝ},0≤S → ∀ksize : ℕ,∀ᶠ d : ℕ in atTop,
      let h := (d:ℝ)^(-(κ*w))
      ∃_ : 0<h,∀{F : Point d → ℝ} {lam : ℝ≥0},∀hF : Primitive F lam,∀x : Point d,
      ∀{r : ℝ},∀hr : 0 < r,r≤1 → 0<lam → (lam:ℝ)*r≤1 →
      (lam:ℝ)*r^2≤S*dimensionLog d^ksize*(d:ℝ)^(-(κ*b)) →
      ∃hl : (lam:ℝ)*r^2≤1/2,∀{T : ℝ},1/2≤T → T<1 → ∀e : ProbabilityNode T h n,
      Integrable (fun z => ‖sampleMeanCircuit F x r T h n (numericalLayerCount J) e z-
        T⁻¹ • fullProbabilityFlow hF x hr.le hl (probabilityNodeTime T h n e) z‖^2)
        (stdGaussian (Point d)) ∧
      (∫z,‖sampleMeanCircuit F x r T h n (numericalLayerCount J) e z-
        T⁻¹ • fullProbabilityFlow hF x hr.le hl (probabilityNodeTime T h n e) z‖^2 ∂stdGaussian (Point d))≤
        (circuitD F x)^2*(d:ℝ)^(-(2*κ*J)) := by
  obtain ⟨A,C,hC,k,hproducer⟩ := sampleMeanCircuit_rms n hn
  intro S hS ksize
  have hc := sampleScalarCalibration_uniform k n (numericalLayerCount J) ksize A C hS hκ hJ hb hw hnw
    (numericalLayerCount_bound J)
  have hhsmall := (LogPowerRate.power (κ*w)).eventually_lt_const (mul_pos hκ hw)
    (Real.log_pos (by norm_num : (1:ℝ)<2))
  filter_upwards [hc,hhsmall,eventually_ge_atTop (1:ℕ)] with d hd hdh hdim
  intro h
  have hdpos : (0:ℝ)<d := by exact_mod_cast hdim
  have hh : 0<h := Real.rpow_pos_of_pos hdpos _
  refine ⟨hh,?_⟩
  intro F lam hF x r hr hr1 hlam hL hl₀
  obtain ⟨hl,hq,he⟩ := hd lam r hr hl₀
  refine ⟨hl,?_⟩
  intro T hT hT1 e
  have hp := hproducer hF x hr hr1 hlam hl hL hdim hT hT1 hh
    ((le_abs_self _).trans hdh.le) hq (numericalLayerCount J) e
  exact ⟨hp.1,hp.2.trans (mul_le_mul_of_nonneg_left he (sq_nonneg _))⟩
end LogConcaveSampling

end

end

end OAI
end

section
-- module Solutions.OAIQ048_LC.LogConcave_Complexity_Envelope
attribute [-instance] _root_.OAI.LogConcaveSampling.LowerBound.couplingLaw_probability _root_.OAI.LogConcaveSampling.LowerBound.remainingHaar_probability _root_.OAI.LogConcaveSampling.LowerBound.roundRandomLaw_probability _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_invInvariant _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_isHaar _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_probability _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_rightInvariant _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_compactSpace _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_measurableInv _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_measurableMul _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_secondCountable _root_.OAI.LogConcaveSampling.OracleCompiler.topSeedLaw_probability _root_.OAI.LogConcaveSampling.noiseKernel_markov
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
namespace LogConcaveSampling
open Filter MeasureTheory ProbabilityTheory
open scoped Classical NNReal Topology

lemma LogPowerRate.envelope {q : ℕ → ℝ} {a : ℝ} (hq : LogPowerRate q a) :
    ∃S : ℝ,0≤S ∧ ∃k : ℕ,∀ᶠ d : ℕ in atTop,|q d|≤S*dimensionLog d^k*(d:ℝ)^(-a) := by
  obtain ⟨k,hk⟩ := hq
  obtain ⟨C,hC⟩ := hk.bound
  refine ⟨|C|,abs_nonneg _,k,?_⟩
  filter_upwards [hC] with d hd
  have hn : 0≤dimensionLog d^k*(d:ℝ)^(-a) := by positivity [dimensionLog_nonneg d]
  rw [Real.norm_eq_abs,Real.norm_of_nonneg hn] at hd
  exact (hd.trans (mul_le_mul_of_nonneg_right (le_abs_self C) hn)).trans_eq (by ring)

lemma source_error_square (κ J : ℝ) {d : ℕ} (_ : 0<d) :
    ((d:ℝ)^(-(κ*J)))^2=(d:ℝ)^(-(2*κ*J)) := by
  have hd0 : (0:ℝ)≤d := Nat.cast_nonneg d
  rw [←Real.rpow_natCast,←Real.rpow_mul hd0]
  congr 1
  push_cast
  ring

namespace OracleCompiler

theorem exists_source_numerical_ready_oai {κ J t w : ℝ}
    (hκ : 0<κ) (hJ : 1≤J) (ht : 0<t) (hts : t<1/100)
    (hw : 0<w) (hwt : w<t) : ∃n : ℕ,
    J+10<w*((n:ℝ)-3) ∧ J+10<t*((n:ℝ)-3) ∧ 4*(J+10)<(n:ℝ) ∧
    ∀q : ℕ → ℝ,LogPowerRate q (κ*(1/2)) →
      ∀ᶠ d : ℕ in atTop,∀C : CircuitParameters,
      SourceShape κ t w n (numericalLayerCount J) d C →
      ∀{F : Point d → ℝ} {lam : ℝ≥0},∀hF : Primitive F lam,0<lam → (lam:ℝ)≤1 →
      ∀hql : q d≤1/4,
      C.MeanNumericalReady hF (q d) ((d:ℝ)^(-(κ*J))) hql ∧
      C.SampleNumericalReady hF (q d) ((d:ℝ)^(-(κ*J))) := by
  obtain ⟨n,hnw,hnt,hnn,hmean⟩ := exists_calibrated_mean_circuit hκ hJ
    (b:=1/2) le_rfl ht hts hw hwt
  have hnw' : J+10<w*((n+1:ℕ)-3) := by push_cast; linarith
  refine ⟨n,hnw,hnt,hnn,?_⟩
  intro q hq
  obtain ⟨S,hS,k,henv⟩ := (hq.const_mul 2).envelope
  have hm := hmean hS k
  have hs := calibrated_sample_circuit_order hκ hJ (b:=1/2) le_rfl hw (n+1)
    (Nat.succ_pos n) hnw' hS k
  filter_upwards [hm,hs,henv,eventually_ge_atTop (1:ℕ)] with d hmd hsd hqd hd
  intro C hC F lam hF hlam hlam1 hql
  have hd0 : 0<d := hd
  have hsquare := source_error_square κ J hd0
  have heψ : -(κ*(4*t))=-(4*(κ*t)) := by ring
  obtain ⟨hT0,hT1,hh,hmc⟩ := hmd
  obtain ⟨hh',hsc⟩ := hsd
  have hbound {r σ : ℝ} (hz : MeanSize lam (q d) r σ) :
      (lam:ℝ)*r^2≤S*dimensionLog d^k*(d:ℝ)^(-(κ*(1/2))) ∧
      (lam:ℝ)*r/(σ/2)≤S*dimensionLog d^k*(d:ℝ)^(-(κ*(1/2))) := by
    have hq0 := hz.nonneg lam.coe_nonneg
    have he : 2*q d≤S*dimensionLog d^k*(d:ℝ)^(-(κ*(1/2))) := (le_abs_self _).trans hqd
    constructor
    · linarith [hz.2.2.2.1]
    · apply le_trans _ he
      apply (div_le_iff₀ (by positivity [hz.2.2.1] : 0<σ/2)).mpr
      nlinarith [hz.2.2.2.2]
  constructor
  · intro x r σ hz
    have hL : (lam:ℝ)*r≤1 := (mul_le_of_le_one_left hz.1.le hlam1).trans hz.2.1
    obtain ⟨hl,hp⟩ := hmc hF x hz.1 hz.2.1 hlam hL
      (show 0<σ/2 by positivity [hz.2.2.1]) (hbound hz).1 (hbound hz).2
    simpa only [CircuitParameters.MeanNumericalReady,hC.n_eq,hC.N_eq,hC.T_eq,hC.h_eq,
      hC.ψ_eq,heψ,hsquare] using hp
  · intro x r η hz hl
    have hL : (lam:ℝ)*r≤1 := (mul_le_of_le_one_left hz.1.le hlam1).trans hz.2.1
    have hq0 := hz.nonneg lam.coe_nonneg
    have hb : (lam:ℝ)*r^2≤S*dimensionLog d^k*(d:ℝ)^(-(κ*(1/2))) := by
      have he := hz.2.2.2.2.trans (mul_le_of_le_one_right hq0 hz.2.2.2.1)
      have hhq : 2*q d≤S*dimensionLog d^k*(d:ℝ)^(-(κ*(1/2))) := (le_abs_self _).trans hqd
      linarith
    obtain ⟨hl',hp⟩ := hsc hF x hz.1 hz.2.1 hlam hL hb
    have hη := sampleCorrelation_properties hz.2.2.1 hz.2.2.2.1
    change ∀{T : ℝ},1/2≤T → T<1 → ∀e : ProbabilityNode T ((d:ℝ)^(-(κ*w))) (n+1),
      Integrable (fun z => ‖sampleMeanCircuit F x r T ((d:ℝ)^(-(κ*w))) (n+1) (numericalLayerCount J) e z-
        T⁻¹ • fullProbabilityFlow hF x hz.1.le hl' (probabilityNodeTime T ((d:ℝ)^(-(κ*w))) (n+1) e) z‖^2)
        (stdGaussian (Point d)) ∧
      (∫z,‖sampleMeanCircuit F x r T ((d:ℝ)^(-(κ*w))) (n+1) (numericalLayerCount J) e z-
        T⁻¹ • fullProbabilityFlow hF x hz.1.le hl' (probabilityNodeTime T ((d:ℝ)^(-(κ*w))) (n+1) e) z‖^2
        ∂stdGaussian (Point d)) ≤ circuitD F x^2*(d:ℝ)^(-(2*κ*J)) at hp
    rw [←hC.h_eq,←hC.n_eq,←hC.N_eq] at hp
    have he := hp hη.1 hη.2.1 (C.sampleEndpoint η hz.2.2.1 hz.2.2.2.1)
    simpa only [CircuitParameters.sampleEndpoint,
      probabilityEndpoint_time _ _ _ _ (Nat.succ_pos C.n),hsquare] using he
end OracleCompiler
end LogConcaveSampling

end

end

end OAI
end

theorem solution : type_of% @OAI.LogConcaveSampling.OracleCompiler.exists_source_numerical_ready_oai := @OAI.LogConcaveSampling.OracleCompiler.exists_source_numerical_ready_oai
