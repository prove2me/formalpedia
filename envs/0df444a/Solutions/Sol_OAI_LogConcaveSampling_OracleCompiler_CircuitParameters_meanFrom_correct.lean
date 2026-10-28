-- Prove2me | solution 1 for OAI.LogConcaveSampling.OracleCompiler.CircuitParameters.meanFrom_correct
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-27T13:47:16.942379+00:00
-- url     : https://prove2.me/submissions/e004241b-46dd-40d4-81e3-a7d5ed809ed9

import Mathlib
import Definitions.Def_LogConcaveQuery
import Definitions.Def_OAIQ048L004
import Theorems.Thm_OAI_LogConcaveSampling_OracleCompiler_CircuitParameters_meanCompiled_scaled

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

theorem depth_add_le (E D : MeanTree X d) {N : ℕ} (hE : depth E≤N) (hD : depth D≤N) :
    depth (add E D)≤N := by
  cases E with | node k b hb a r C =>
    cases D with | node l c hc v t B =>
      simp only [depth,Finset.sup_le_iff,Finset.mem_univ,true_implies] at hE hD
      simp only [add,depth,Finset.sup_le_iff,Finset.mem_univ,true_implies]
      intro i
      refine Fin.addCases (fun j => ?_) (fun j => ?_) i
      · simpa only [Fin.addCases_left] using hE j
      · simpa only [Fin.addCases_right] using hD j

lemma depth_sumFin_le (k : ℕ) (E : Fin k → MeanTree X d) {N : ℕ}
    (hE : ∀i,depth (E i)≤N) : depth (sumFin k E)≤N := by
  induction k with
  | zero => simp [sumFin]
  | succ k ih => exact depth_add_le (E 0) (sumFin k _) (hE 0) (ih _ (fun i => hE i.succ))

lemma depth_sumFamily_le {I : Type*} [Fintype I] (E : I → MeanTree X d) {N : ℕ}
    (hE : ∀i,depth (E i)≤N) : depth (sumFamily E)≤N :=
  depth_sumFin_le _ _ (fun _ => hE _)

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

lemma depth_conditional_le (r ρ : ℝ) (x y : MeanTree X d) {N : ℕ}
    (hx : depth x≤N) (hy : depth y≤N) : depth (conditional r ρ x y)≤N+1 := by
  simp only [conditional,depth_mean]
  exact Nat.add_le_add_right (depth_add_le _ _ hx (by simpa using hy)) 1

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

lemma gaussian_pair_shift_law (m : Point d) (a b s : ℝ) (hs : a^2+b^2=s^2) :
    ((stdGaussian (Point d)).prod (stdGaussian (Point d))).map
      (fun z => (m+a • z.1)+b • z.2)=
      (stdGaussian (Point d)).map (fun z => m+s • z) := by
  have h := congrArg (Measure.map (fun z => m+z)) (gaussian_pair_sum_law (d:=d) a b s hs)
  rw [Measure.map_map (by fun_prop) (by fun_prop),Measure.map_map (by fun_prop) (by fun_prop)] at h
  simpa only [comp_def,add_assoc] using h

lemma law_add_gaussian {X : Type*} [MeasurableSpace X]
    (μ : Measure X) [IsProbabilityMeasure μ] (u : X → Point d) (hu : Measurable u)
    (m : Point d) (a b s : ℝ) (hs : a^2+b^2=s^2)
    (hlaw : μ.map u=(stdGaussian (Point d)).map (fun z => m+a • z)) :
    (μ.prod (stdGaussian (Point d))).map (fun z => u z.1+b • z.2)=
      (stdGaussian (Point d)).map (fun z => m+s • z) := by
  have h := congrArg (fun η : Measure (Point d) =>
    (η.prod (stdGaussian (Point d))).map (fun z => z.1+b • z.2)) hlaw
  have left : (μ.map u).prod (stdGaussian (Point d))=
      (μ.prod (stdGaussian (Point d))).map (Prod.map u id) := by
    rw [←Measure.map_prod_map _ _ hu measurable_id,Measure.map_id]
  have right : ((stdGaussian (Point d)).map (fun z => m+a • z)).prod (stdGaussian (Point d))=
      ((stdGaussian (Point d)).prod (stdGaussian (Point d))).map
        (Prod.map (fun z => m+a • z) id) := by
    rw [←Measure.map_prod_map _ _ (by fun_prop) measurable_id,Measure.map_id]
  rw [left,right,Measure.map_map (by fun_prop) (by fun_prop),
    Measure.map_map (by fun_prop) (by fun_prop)] at h
  exact h.trans (gaussian_pair_shift_law m a b s hs)

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
-- module Solutions.OAIQ048_LC.LogConcave_Numerics_ReanchorWeight
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

end LogConcaveSampling

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

lemma depth_picard {I : Type*} [Fintype I] (w : I → I → ℝ)
    (φ : I → MeanTree X d → MeanTree X d) (a : I → MeanTree X d) {b D : ℕ}
    (ha : ∀i,depth (a i)≤b)
    (hφ : ∀i E,depth (φ i E)≤ max b (depth E)+D) (N : ℕ) (i : I) :
    depth (picard w φ a N i)≤b+N*D := by
  induction N generalizing i with
  | zero => simpa [picard] using ha i
  | succ N ih =>
    apply depth_add_le
    · exact (ha i).trans (by omega)
    · apply depth_sumFamily_le
      intro j
      rw [depth_scale]
      have he := hφ j (picard w φ a N j)
      have hi := ih j
      simp only [Nat.succ_mul] at *
      omega

lemma eval_probability {F : Point d → ℝ} {lam : ℝ≥0} (hF : Primitive F lam)
    {r T h : ℝ} {n N : ℕ} (hn : 0<n) (hT0 : 0<T) (hT1 : T<1) (hh : 0<h)
    (s i : ProbabilityNode T h n) (x y : MeanTree X d) (z : X) :
    eval F (probability r T h n N s x y i) z=
      probabilityAnchoredPicard F (eval F x z) r T h n N s (eval F y z) i := by
  unfold probability probabilityAnchoredPicard
  have ha (j : ProbabilityNode T h n) : 0<1-(probabilityNodeTime T h n j)^2 := by
    have hj := probabilityNodeTime_mem hT0 hT1 hh hn j
    have ht := hj.2.trans_lt hT1
    nlinarith [hj.1]
  have he := eval_picard F (reanchorWeight (probabilityWeight T h n) s)
    (fun j E => scale (-r) (conditional r (probabilityNodeTime T h n j) x E))
    (fun _ => y) (fun z j => probabilityMeanVelocity F (eval F x z) r (probabilityNodeTime T h n j))
    (fun j E z => by simp only [eval_scale,eval_conditional hF r _ x E z (ha j),probabilityMeanVelocity]) N z i
  simpa only [nodes_eq_iterate] using he

lemma depth_probability (r T h : ℝ) (n N : ℕ) (s i : ProbabilityNode T h n)
    (x y : MeanTree X d) {b : ℕ} (hx : depth x≤b) (hy : depth y≤b) :
    depth (probability r T h n N s x y i)≤b+N := by
  apply (depth_picard _ _ _ (D:=1) (fun _ => hy) ?_ N i).trans (by omega)
  intro j E
  rw [depth_scale]
  exact depth_conditional_le _ _ _ _ (hx.trans (le_max_left _ _)) (le_max_right _ _)

lemma eval_harmonic {F : Point d → ℝ} {lam : ℝ≥0} (hF : Primitive F lam)
    (r ρ v : ℝ) (ha : 0<1-ρ^2) (n N : ℕ) (x y g : MeanTree X d)
    (z : X) (i : Fin (n+1)) :
    eval F (harmonic r ρ v n N x y g i) z=
      harmonicPicard F (eval F x z) r ρ v n N (eval F y z,eval F g z) i := by
  unfold harmonic harmonicPicard
  have he := eval_picard F (harmonicWeight n v)
    (fun _ E => scale ρ (scale (-r) (conditional r ρ x E)))
    (fun j => add (scale (Real.cos (v*probabilityNodes n j)) y)
      (scale (Real.sin (v*probabilityNodes n j)) g))
    (fun z _ => harmonicMeanVelocity F (eval F x z) r ρ)
    (fun j E z => by simp only [eval_scale,eval_conditional hF r ρ x E z ha,
      harmonicMeanVelocity,probabilityMeanVelocity]) N z i
  simp only [nodes_eq_iterate,eval_add,eval_scale] at he ⊢
  change _ = _ at he
  exact he

lemma depth_harmonic (r ρ v : ℝ) (n N : ℕ) (x y g : MeanTree X d) (i : Fin (n+1))
    {b : ℕ} (hx : depth x≤b) (hy : depth y≤b) (hg : depth g≤b) :
    depth (harmonic r ρ v n N x y g i)≤b+N := by
  apply (depth_picard _ _ _ (D:=1) (fun j => depth_add_le _ _ (by simpa using hy) (by simpa using hg)) ?_ N i).trans (by omega)
  intro j E
  simp only [depth_scale]
  exact depth_conditional_le _ _ _ _ (hx.trans (le_max_left _ _)) (le_max_right _ _)

lemma eval_kernelCorrection {F : Point d → ℝ} {lam : ℝ≥0} (hF : Primitive F lam)
    {r T h v : ℝ} {n N : ℕ} (hn : 0<n) (hT0 : 0<T) (hT1 : T<1) (hh : 0<h)
    (s e : ProbabilityNode T h n) (x y g : MeanTree X d) (z : X) :
    eval F (kernelCorrection r T h v n N s e x y g) z=
      kernelCorrectionPicard F (eval F x z) r T h v n N s e (eval F y z,eval F g z) := by
  have ha (j : ProbabilityNode T h n) : 0<1-(probabilityNodeTime T h n j)^2 := by
    have hj := probabilityNodeTime_mem hT0 hT1 hh hn j
    have ht := hj.2.trans_lt hT1
    nlinarith [hj.1]
  simp only [kernelCorrection,eval_sumFamily,eval_scale,eval_conditional hF _ _ _ _ z (ha _),
    eval_probability hF hn hT0 hT1 hh,eval_harmonic hF _ _ _ (ha s)]
  simp only [kernelCorrectionPicard,probabilityAnchoredPicard,nodes,step,correction,Pi.add_apply,
    add_sub_cancel_left,probabilityMeanVelocity]

lemma depth_kernelCorrection (r T h v : ℝ) (n N : ℕ) (s e : ProbabilityNode T h n)
    (x y g : MeanTree X d) {b : ℕ} (hx : depth x≤b) (hy : depth y≤b) (hg : depth g≤b) :
    depth (kernelCorrection r T h v n N s e x y g)≤b+3*N+1 := by
  have hb := depth_probability r T h n N e s x y hx hy
  have hw := depth_harmonic r (probabilityNodeTime T h n s) v n N x
    (probability r T h n N e x y s) g (Fin.last n)
    (b:=b+N) (hx.trans (by omega)) hb (hg.trans (by omega))
  unfold kernelCorrection
  apply depth_sumFamily_le
  intro j
  simp only [depth_scale]
  apply depth_conditional_le
  · exact hx.trans (by omega)
  · exact (depth_probability r T h n N s j x _ (b:=b+N+N)
      (hx.trans (by omega)) hw).trans (by omega)

end LogConcaveSampling.MeanTree

end

end

section

noncomputable section
namespace LogConcaveSampling.MeanTree
open Set MeasureTheory Quadrature FinitePicard
open scoped Classical BigOperators NNReal

variable {X : Type*} [MeasurableSpace X] {d : ℕ}

lemma eval_kernelAction {F : Point d → ℝ} {lam : ℝ≥0} (hF : Primitive F lam)
    {r T h ψ : ℝ} {n m N : ℕ} (hn : 0<n) (hT0 : 0<T) (hT1 : T<1) (hh : 0<h)
    (s e : ProbabilityNode T h n) (x y g : MeanTree X d) (z : X) :
    eval F (kernelAction r T h ψ n m N s e x y g) z=
      kernelActionPicard F (eval F x z) r T h ψ n m N s e (eval F y z,eval F g z) := by
  simp only [kernelAction,eval_sumFamily,eval_scale,eval_kernelCorrection hF hn hT0 hT1 hh]
  rfl

lemma eval_kernelQuadrature {F : Point d → ℝ} {lam : ℝ≥0} (hF : Primitive F lam)
    {r T h ψ : ℝ} {n m N : ℕ} (hn : 0<n) (hT0 : 0<T) (hT1 : T<1) (hh : 0<h)
    (e : ProbabilityNode T h n) (w : ProbabilityNode T h n → ℝ)
    (x y g : MeanTree X d) (z : X) :
    eval F (kernelQuadrature r T h ψ n m N e w x y g) z=
      kernelQuadraturePicard F (eval F x z) r T h ψ n m N e w (eval F y z,eval F g z) := by
  simp only [kernelQuadrature,eval_sumFamily,eval_scale,eval_kernelAction hF hn hT0 hT1 hh]
  rfl

lemma depth_kernelQuadrature (r T h ψ : ℝ) (n m N : ℕ) (e : ProbabilityNode T h n)
    (w : ProbabilityNode T h n → ℝ) (x y g : MeanTree X d) {b : ℕ}
    (hx : depth x≤b) (hy : depth y≤b) (hg : depth g≤b) :
    depth (kernelQuadrature r T h ψ n m N e w x y g)≤b+3*N+1 := by
  apply depth_sumFamily_le
  intro j
  rw [depth_scale]
  apply depth_sumFamily_le
  intro k
  rw [depth_scale]
  exact depth_kernelCorrection _ _ _ _ _ _ _ _ _ _ _ hx hy hg

lemma eval_velocity {F : Point d → ℝ} {lam : ℝ≥0} (hF : Primitive F lam)
    {r T h ψ s : ℝ} (hT0 : 0<T) (hT1 : T<1) (hh : 0<h)
    (n m N : ℕ) (e : ProbabilityNode T h (n+1)) (x : MeanTree X d)
    (p : MeanTree X d × MeanTree X d) (z : X) :
    pairEval F (velocity r T h ψ s n m N e x p) z=
      centeringVelocityPicard F (eval F x z) r T h ψ s n m N e (pairEval F p z) := by
  have ha : 0<1-T^2 := by nlinarith
  simp only [pairEval,velocity,eval_scale,eval_kernelQuadrature hF (Nat.succ_pos n) hT0 hT1 hh,
    eval_add,eval_conditional hF _ _ _ _ z ha,eval_mean,neg_one_smul,←sub_eq_add_neg]
  rfl

lemma depth_velocity (r T h ψ s : ℝ) (n m N : ℕ) (e : ProbabilityNode T h (n+1))
    (x : MeanTree X d) (p : MeanTree X d × MeanTree X d) {b : ℕ}
    (hx : depth x≤b) (hy : depth p.1≤b) (hg : depth p.2≤b) :
    depth (velocity r T h ψ s n m N e x p).1≤b+(3*N+1) ∧
    depth (velocity r T h ψ s n m N e x p).2≤b+(3*N+1) := by
  constructor
  · simpa only [velocity,depth_scale,Nat.add_assoc] using
      depth_kernelQuadrature r T h ψ (n+1) m N e (terminalQuadratureWeight T h n) x p.1 p.2 hx hy hg
  · simp only [velocity,depth_scale]
    apply depth_add_le
    · exact (depth_conditional_le _ _ _ _ hx hy).trans (by omega)
    · simp only [depth_scale,depth_mean]; omega

lemma eval_pairPicard {I : Type*} [Fintype I] (F : Point d → ℝ) (w : I → I → ℝ)
    (φ : MeanTree X d × MeanTree X d → MeanTree X d × MeanTree X d)
    (a : MeanTree X d × MeanTree X d) (V : X → (Point d × Point d) → Point d × Point d)
    (hφ : ∀p z,pairEval F (φ p) z=V z (pairEval F p z))
    (N : ℕ) (z : X) (i : I) :
    pairEval F (pairPicard w φ a N i) z=
      nodes w (fun _ => V z) (fun p : Point d × Point d => fun _ => p) N (pairEval F a z) i := by
  induction N generalizing i with
  | zero => rfl
  | succ N ih =>
    have hsum (j : I) := hφ (pairPicard w φ a N j) z
    simp only [ih] at hsum
    apply Prod.ext
    · simp only [pairPicard,pairEval,eval_add,eval_sumFamily,eval_scale,nodes,step,correction,
        Pi.add_apply,Prod.fst_add,Prod.fst_sum,Prod.smul_fst]
      congr 1
      apply Finset.sum_congr rfl
      intro j _
      simpa only [pairEval] using congrArg (fun p : Point d × Point d => w i j • p.1) (hsum j)
    · simp only [pairPicard,pairEval,eval_add,eval_sumFamily,eval_scale,nodes,step,correction,
        Pi.add_apply,Prod.snd_add,Prod.snd_sum,Prod.smul_snd]
      congr 1
      apply Finset.sum_congr rfl
      intro j _
      simpa only [pairEval] using congrArg (fun p : Point d × Point d => w i j • p.2) (hsum j)

lemma depth_pairPicard {I : Type*} [Fintype I] (w : I → I → ℝ)
    (φ : MeanTree X d × MeanTree X d → MeanTree X d × MeanTree X d)
    (a : MeanTree X d × MeanTree X d) {b D : ℕ}
    (ha : depth a.1≤b ∧ depth a.2≤b)
    (hφ : ∀p k,b≤k → depth p.1≤k → depth p.2≤k →
      depth (φ p).1≤k+D ∧ depth (φ p).2≤k+D) (N : ℕ) (i : I) :
    depth (pairPicard w φ a N i).1≤b+N*D ∧ depth (pairPicard w φ a N i).2≤b+N*D := by
  induction N generalizing i with
  | zero => simpa [pairPicard] using ha
  | succ N ih =>
    have hstep (j : I) := hφ (pairPicard w φ a N j) (b+N*D) (by omega) (ih j).1 (ih j).2
    constructor
    · apply depth_add_le
      · exact ha.1.trans (by omega)
      · apply depth_sumFamily_le
        intro j
        rw [depth_scale]
        simpa only [Nat.succ_mul,Nat.add_assoc] using (hstep j).1
    · apply depth_add_le
      · exact ha.2.trans (by omega)
      · apply depth_sumFamily_le
        intro j
        rw [depth_scale]
        simpa only [Nat.succ_mul,Nat.add_assoc] using (hstep j).2

end LogConcaveSampling.MeanTree

end

end

section

noncomputable section
namespace LogConcaveSampling.MeanTree
open Set MeasureTheory Quadrature FinitePicard
open scoped Classical BigOperators NNReal

variable {X : Type*} [MeasurableSpace X] {d : ℕ}

lemma nodes_productPointEquiv {I : Type*} [Fintype I] (w : I → I → ℝ)
    (V : Point d × Point d → Point d × Point d) (y : Point (d+d)) (N : ℕ) (i : I) :
    productPointEquiv d d
      (nodes w (fun _ z => (productPointEquiv d d).symm (V (productPointEquiv d d z)))
        (fun z _ => z) N y i)=
      nodes w (fun _ => V) (fun p : Point d × Point d => fun _ => p) N (productPointEquiv d d y) i := by
  induction N generalizing i with
  | zero => rfl
  | succ N ih =>
    simp only [nodes,step,correction,Pi.add_apply,map_add,map_sum,map_smul,
      ContinuousLinearEquiv.apply_symm_apply]
    congr 1
    apply Finset.sum_congr rfl
    intro j _
    rw [ih]

lemma eval_centeringStates {F : Point d → ℝ} {lam : ℝ≥0} (hF : Primitive F lam)
    {r T h ψ s : ℝ} (hT0 : 0<T) (hT1 : T<1) (hh : 0<h)
    (n m N nc Nc : ℕ) (e : ProbabilityNode T h (n+1)) (x y g : MeanTree X d)
    (z : X) (i : Fin (nc+1)) :
    pairEval F (centeringStates r T h ψ s n m N nc Nc e x y g i) z=
      productPointEquiv d d (stationaryPicard nc Nc
        (centeringVelocityJoint F (eval F x z) r T h ψ s n m N e)
        ((productPointEquiv d d).symm (eval F y z,eval F g z)) i) := by
  rw [centeringStates,eval_pairPicard F _ _ _ _ (fun p z => eval_velocity hF hT0 hT1 hh n m N e x p z)]
  unfold stationaryPicard centeringVelocityJoint
  rw [nodes_productPointEquiv]
  simp only [ContinuousLinearEquiv.apply_symm_apply,pairEval]

lemma eval_meanCircuit {F : Point d → ℝ} {lam : ℝ≥0} (hF : Primitive F lam)
    {r T h ψ s : ℝ} (hT0 : 0<T) (hT1 : T<1) (hh : 0<h)
    (n m N nc Nc : ℕ) (e : ProbabilityNode T h (n+1)) (x y g : MeanTree X d) (z : X) :
    eval F (meanCircuit r T h ψ s n m N nc Nc e x y g) z=
      centeringMeanCircuit F (eval F x z) r T h ψ s n m N nc Nc e
        ((productPointEquiv d d).symm (eval F y z,eval F g z)) := by
  have ha : 0<1-T^2 := by nlinarith
  simp only [meanCircuit,eval_add,eval_scale,eval_sumFamily,
    eval_conditional hF _ _ _ _ z ha,centeringMeanCircuit,ContinuousLinearEquiv.apply_symm_apply]
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  have he := congrArg Prod.fst (eval_centeringStates hF (r:=r) (ψ:=ψ) (s:=s) hT0 hT1 hh n m N nc Nc e x y g z j)
  change eval F (centeringStates r T h ψ s n m N nc Nc e x y g j).1 z=_ at he
  rw [he]

lemma depth_centeringStates (r T h ψ s : ℝ) (n m N nc Nc : ℕ)
    (e : ProbabilityNode T h (n+1)) (x y g : MeanTree X d) {b : ℕ}
    (hx : depth x≤b) (hy : depth y≤b) (hg : depth g≤b) (i : Fin (nc+1)) :
    depth (centeringStates r T h ψ s n m N nc Nc e x y g i).1≤b+Nc*(3*N+1) ∧
    depth (centeringStates r T h ψ s n m N nc Nc e x y g i).2≤b+Nc*(3*N+1) := by
  apply depth_pairPicard _ _ _ ⟨hy,hg⟩
  intro p k hk hp hq
  exact depth_velocity r T h ψ s n m N e x p (hx.trans hk) hp hq

lemma depth_meanCircuit (r T h ψ s : ℝ) (n m N nc Nc : ℕ)
    (e : ProbabilityNode T h (n+1)) (x y g : MeanTree X d) {b : ℕ}
    (hx : depth x≤b) (hy : depth y≤b) (hg : depth g≤b) :
    depth (meanCircuit r T h ψ s n m N nc Nc e x y g)≤b+Nc*(3*N+1)+1 := by
  apply depth_add_le
  · simpa only [depth_scale] using hg.trans (by omega)
  · apply depth_sumFamily_le
    intro j
    rw [depth_scale]
    exact depth_conditional_le _ _ _ _ (hx.trans (by omega))
      (depth_centeringStates r T h ψ s n m N nc Nc e x y g hx hy hg j).1

theorem meanCircuit_fixed_depth (r T h ψ s : ℝ) (n m N nc Nc : ℕ) (hNc : Nc≤N)
    (e : ProbabilityNode T h (n+1)) (x y g : X → Point d)
    (hx : Measurable x) (hy : Measurable y) (hg : Measurable g) :
    depth (meanCircuit r T h ψ s n m N nc Nc e (anchor x hx) (anchor y hy) (anchor g hg))≤
      4*(N+1)^2 := by
  have he := depth_meanCircuit r T h ψ s n m N nc Nc e (anchor x hx) (anchor y hy) (anchor g hg)
    (b:=0) (by simp) (by simp) (by simp)
  have hh := Nat.mul_le_mul_right (3*N+1) hNc
  nlinarith

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

lemma circuitGrowthConstant_pos : 0 < circuitGrowthConstant := by
  unfold circuitGrowthConstant
  positivity [terminalTransportConstant_pos]

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

lemma rootScales_add (P : ℝ → Prop) (E B : MeanTree X d)
    (hE : rootScales P E) (hB : rootScales P B) : rootScales P (add E B) := by
  cases E with | node k b hb a r C =>
    cases B with | node l c hc v s D =>
      intro i
      exact Fin.addCases (fun j => by simpa [add] using hE j)
        (fun j => by simpa [add] using hB j) i
lemma rootScales_sumFin (P : ℝ → Prop) (k : ℕ) (E : Fin k → MeanTree X d)
    (hE : ∀i,rootScales P (E i)) : rootScales P (sumFin k E) := by
  induction k with
  | zero => exact rootScales_anchor _ _ _
  | succ k ih => exact rootScales_add P _ _ (hE 0) (ih _ (fun i => hE i.succ))
lemma rootScales_sumFamily {I : Type*} [Fintype I] (P : ℝ → Prop)
    (E : I → MeanTree X d) (hE : ∀i,rootScales P (E i)) : rootScales P (sumFamily E) :=
  rootScales_sumFin P _ _ (fun _ => hE _)

lemma meanCircuit_final_radius (r T h ψ s : ℝ) (n m N nc Nc : ℕ)
    (e : ProbabilityNode T h (n+1)) (xE yE : MeanTree X d)
    (G : X → Point d) (hG : Measurable G) :
    rootScales (fun r' => r'=r*Real.sqrt (1-T^2))
      (meanCircuit r T h ψ s n m N nc Nc e xE yE (anchor G hG)) := by
  apply rootScales_add
  · exact (rootScales_scale _ _ _).2 (rootScales_anchor _ _ _)
  · apply rootScales_sumFamily
    intro j
    apply (rootScales_scale _ _ _).2
    intro i
    rfl

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

namespace ReservedProgram

lemma full_run (S : ReservedProgram d) (V : Point d → ℝ)
    (x : Point d) (g : Fin (S.slots+1) → Point d) :
    S.full.program.run V (x,g)=
      S.pre.run V (x,fun i => g (Fin.castAdd 1 i))+S.reserve • g (Fin.natAdd S.slots 0) := by
  change ((S.pre.seedMap (fun z : Point d × (Fin (S.slots+1) → Point d) =>
    (z.1,fun i => z.2 (Fin.castAdd 1 i))) (by fun_prop)).map
    (fun z => z.2+S.reserve • z.1.2 (Fin.natAdd S.slots 0)) (by fun_prop)).run V (x,g)=_
  rw [Program.map_run,Program.seedMap_run]

end ReservedProgram

lemma meanParent_run (S : SeedProgram d)
    (E : Expression (Point d × (Point d × Point d)) d)
    (u : Fin S.slots → ℝ) (v : Fin E.slots → ℝ) (T : ℝ)
    (V : Point d → ℝ) (x : Point d) (g : Fin (S.slots+(1+E.slots)) → Point d) :
    (meanParent S E u v T).program.run V (x,g)=
      E.eval V (x,(T • S.program.run V (x,leftBlock g),middleBlock g 0)) (rightBlock g) := by
  change ((S.program.seedMap _ _).seq (E.compile.seedMap _ _)).run V (x,g)=_
  rw [Program.seq_run,Program.seedMap_run,Program.seedMap_run,Expression.compile_run]

end LogConcaveSampling.OracleCompiler

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

lemma probability_weights {r T h P A : ℝ} (hr : 0 ≤ r) (hP : 0≤P) (n N : ℕ)
    (s : ProbabilityNode T h n)
    (ht : ∀j : ProbabilityNode T h n,|probabilityNodeTime T h n j|≤1)
    (hw : ∀i,∑j,|reanchorWeight (probabilityWeight T h n) s i j|≤P)
    (x y : MeanTree X d) (hxw : weight x=0)
    (hx : centersBound A x) (hy : centersBound A y)
    (hA : r*(weight y+P*r)≤A) (i : ProbabilityNode T h n) :
    weight (probability r T h n N s x y i)≤weight y+P*r ∧
      centersBound A (probability r T h n N s x y i) := by
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

lemma harmonic_weights {r ρ v H A : ℝ} (hr : 0 ≤ r) (hρ : |ρ|≤1) (hH : 0≤H)
    (n N : ℕ) (hw : ∀i,∑j,|harmonicWeight n v i j|≤H)
    (x y g : MeanTree X d) (hxw : weight x=0)
    (hx : centersBound A x) (hy : centersBound A y) (hg : centersBound A g)
    (hA : r*(weight y+weight g+H*r)≤A) (i : Fin (n+1)) :
    weight (harmonic r ρ v n N x y g i)≤weight y+weight g+H*r ∧
      centersBound A (harmonic r ρ v n N x y g i) := by
  have hc (j : Fin (n+1)) (E : MeanTree X d) :
      weight (scale ρ (scale (-r) (conditional r ρ x E))) ≤ r := by
    simp only [weight_scale,weight_conditional,abs_neg,abs_of_nonneg hr,mul_one]
    nlinarith
  have ha (j : Fin (n+1)) : weight (add (scale (Real.cos (v*probabilityNodes n j)) y)
      (scale (Real.sin (v*probabilityNodes n j)) g))≤weight y+weight g := by
    simp only [weight_add,weight_scale]
    exact add_le_add
      (by nlinarith [Real.abs_cos_le_one (v*probabilityNodes n j),weight_nonneg y])
      (by nlinarith [Real.abs_sin_le_one (v*probabilityNodes n j),weight_nonneg g])
  constructor
  · exact (weight_picard _ _ _ hr hw hc N i).trans (add_le_add_left (ha i) _)
  · apply centersBound_picard _ _ _ hH hr hw hc ha
      (fun _ => (centersBound_add _ _ _).2 ⟨(centersBound_scale _ _ _).2 hy,(centersBound_scale _ _ _).2 hg⟩) ?_ N i
    intro j E hE hEb
    apply (centersBound_scale _ _ _).2
    apply (centersBound_scale _ _ _).2
    apply centersBound_conditional hx hEb
    rw [hxw,zero_add,abs_mul,abs_of_nonneg hr]
    calc
      r*|ρ| * weight E ≤ r*weight E := by nlinarith [weight_nonneg E,mul_le_mul_of_nonneg_left hρ hr]
      _ ≤ r*(weight y+weight g+H*r) := mul_le_mul_of_nonneg_left hE hr
      _≤A := hA

lemma kernelCorrection_weights {r T h v P H A : ℝ} (hr : 0 ≤ r) (hP : 0≤P) (hH : 0≤H)
    (n N : ℕ) (s e : ProbabilityNode T h n)
    (ht : ∀j : ProbabilityNode T h n,|probabilityNodeTime T h n j|≤1)
    (hpw : ∀s i,∑j,|reanchorWeight (probabilityWeight T h n) s i j|≤P)
    (hhw : ∀i,∑j,|harmonicWeight n v i j|≤H)
    (x y g : MeanTree X d) (hxw : weight x=0)
    (hx : centersBound A x) (hy : centersBound A y) (hg : centersBound A g)
    (hA : r*(weight y+weight g+(2*P+H)*r)≤A) :
    weight (kernelCorrection r T h v n N s e x y g)≤P*r ∧
      centersBound A (kernelCorrection r T h v n N s e x y g) := by
  have hB : r*(weight y+P*r)≤A := by
    apply le_trans _ hA
    apply mul_le_mul_of_nonneg_left _ hr
    nlinarith [weight_nonneg g]
  have hb := probability_weights hr hP n N e ht (hpw e) x y hxw hx hy hB s
  let b := probability r T h n N e x y s
  have hW : r*(weight b+weight g+H*r)≤A := by
    apply le_trans _ hA
    apply mul_le_mul_of_nonneg_left _ hr
    dsimp only [b]
    nlinarith [hb.1]
  have hw := harmonic_weights hr (ht s) hH n N hhw x b g hxw hx hb.2 hg hW (Fin.last n)
  let w := harmonic r (probabilityNodeTime T h n s) v n N x b g (Fin.last n)
  have hF : r*(weight w+P*r)≤A := by
    apply le_trans _ hA
    apply mul_le_mul_of_nonneg_left _ hr
    dsimp only [w]
    nlinarith [hw.1,hb.1]
  have hf (j : ProbabilityNode T h n) := probability_weights hr hP n N s ht (hpw s) x w hxw hx hw.2 hF j
  constructor
  · simp only [kernelCorrection,weight_sumFamily,weight_scale,weight_conditional,abs_neg,abs_of_nonneg hr,mul_one]
    rw [←Finset.sum_mul]
    exact mul_le_mul_of_nonneg_right (hpw s e) hr
  · unfold kernelCorrection
    change centersBound A (sumFamily (fun j => scale (reanchorWeight (probabilityWeight T h n) s e j) (scale (-r) (conditional r (probabilityNodeTime T h n j) x (probability r T h n N s x w j)))))
    apply centersBound_sumFamily
    intro j
    apply (centersBound_scale _ _ _).2
    apply (centersBound_scale _ _ _).2
    apply centersBound_conditional hx (hf j).2
    rw [hxw,zero_add,abs_mul,abs_of_nonneg hr]
    apply le_trans _ hF
    calc
      r*|probabilityNodeTime T h n j| * weight (probability r T h n N s x w j)
        ≤r*weight (probability r T h n N s x w j) := by
          nlinarith [weight_nonneg (probability r T h n N s x w j),mul_le_mul_of_nonneg_left (ht j) hr]
      _ ≤ r*(weight w+P*r) := mul_le_mul_of_nonneg_left (hf j).1 hr

end LogConcaveSampling.MeanTree

end

end

section

noncomputable section
namespace LogConcaveSampling.MeanTree
open MeasureTheory Quadrature FinitePicard
open scoped Classical BigOperators

variable {X : Type*} [MeasurableSpace X] {d : ℕ}

lemma kernelQuadrature_weights {r T h ψ P H A Q S : ℝ}
    (hr : 0 ≤ r) (hP : 0≤P) (hH : 0≤H) (_hQ : 0≤Q) (hS : 0≤S)
    (n m N : ℕ) (e : ProbabilityNode T h n) (w : ProbabilityNode T h n → ℝ)
    (ht : ∀j : ProbabilityNode T h n,|probabilityNodeTime T h n j|≤1)
    (hpw : ∀s i,∑j,|reanchorWeight (probabilityWeight T h n) s i j|≤P)
    (hhw : ∀k : Fin (m+1),∀i,∑j,|harmonicWeight n (ψ*angleNodes m k) i j|≤H)
    (hqw : ∑j,|w j|≤Q) (hsw : (∑j : Fin (m+1),|derivativeWeight (angleNodes m) j/ψ|)≤S)
    (x y g : MeanTree X d) (hxw : weight x=0)
    (hx : centersBound A x) (hy : centersBound A y) (hg : centersBound A g)
    (hA : r*(weight y+weight g+(2*P+H)*r)≤A) :
    weight (kernelQuadrature r T h ψ n m N e w x y g)≤Q*S*(P*r) ∧
      centersBound A (kernelQuadrature r T h ψ n m N e w x y g) := by
  have hc (j : ProbabilityNode T h n) (k : Fin (m+1)) :=
    kernelCorrection_weights hr hP hH n N j e ht hpw (hhw k) x y g hxw hx hy hg hA
  have ha (j : ProbabilityNode T h n) : weight (kernelAction r T h ψ n m N j e x y g)≤S*(P*r) := by
    simp only [kernelAction,weight_sumFamily,weight_scale]
    calc
      _≤∑k,|derivativeWeight (angleNodes m) k/ψ| * (P*r) :=
        Finset.sum_le_sum (fun k _ => mul_le_mul_of_nonneg_left (hc j k).1 (abs_nonneg _))
      _=(∑k,|derivativeWeight (angleNodes m) k/ψ|)*(P*r) := (Finset.sum_mul _ _ _).symm
      _≤S*(P*r) := mul_le_mul_of_nonneg_right hsw (mul_nonneg hP hr)
  constructor
  · simp only [kernelQuadrature,weight_sumFamily,weight_scale]
    calc
      _≤∑j,|w j| * (S*(P*r)) := Finset.sum_le_sum (fun j _ => mul_le_mul_of_nonneg_left (ha j) (abs_nonneg _))
      _=(∑j,|w j|)*(S*(P*r)) := (Finset.sum_mul _ _ _).symm
      _≤Q*(S*(P*r)) := mul_le_mul_of_nonneg_right hqw (by positivity)
      _=Q*S*(P*r) := by ring
  · apply centersBound_sumFamily
    intro j
    apply (centersBound_scale _ _ _).2
    apply centersBound_sumFamily
    intro k
    exact (centersBound_scale _ _ _).2 (hc j k).2

lemma velocity_weights {r T h ψ s P H A Q S : ℝ}
    (hr : 0 < r) (hs : 0 < s) (hT : |T|≤1)
    (hP : 0≤P) (hH : 0≤H) (hQ : 0≤Q) (hS : 0≤S)
    (n m N : ℕ) (e : ProbabilityNode T h (n+1))
    (ht : ∀j : ProbabilityNode T h (n+1),|probabilityNodeTime T h (n+1) j|≤1)
    (hpw : ∀s i,∑j,|reanchorWeight (probabilityWeight T h (n+1)) s i j|≤P)
    (hhw : ∀k : Fin (m+1),∀i,∑j,|harmonicWeight (n+1) (ψ*angleNodes m k) i j|≤H)
    (hqw : ∑j,|terminalQuadratureWeight T h n j|≤Q)
    (hsw : (∑j : Fin (m+1),|derivativeWeight (angleNodes m) j/ψ|)≤S)
    (x : MeanTree X d) (p : MeanTree X d × MeanTree X d) (hxw : weight x=0)
    (hx : centersBound A x) (hy : centersBound A p.1) (hg : centersBound A p.2)
    (hA : r*(weight p.1+weight p.2+(2*P+H)*r)≤A) :
    weight (velocity r T h ψ s n m N e x p).1+
      weight (velocity r T h ψ s n m N e x p).2≤(Q*S*P+2)/s ∧
    centersBound A (velocity r T h ψ s n m N e x p).1 ∧
      centersBound A (velocity r T h ψ s n m N e x p).2 := by
  have hk := kernelQuadrature_weights hr.le hP hH hQ hS n.succ m N e _ ht hpw hhw hqw hsw x p.1 p.2 hxw hx hy hg hA
  have hA0 : 0≤A := (mul_nonneg hr.le (by positivity [weight_nonneg p.1,weight_nonneg p.2])).trans hA
  constructor
  · simp only [velocity,weight_scale,weight_add,weight_conditional,weight_mean,
      abs_neg,abs_one,one_mul,abs_inv,abs_mul,abs_of_pos hr,abs_of_pos hs]
    apply le_trans (add_le_add_left (mul_le_mul_of_nonneg_left hk.1 (by positivity)) _)
    have he : (r*s)⁻¹*(Q*S*(P*r))+s⁻¹*(1+1)=(Q*S*P+2)/s := by field_simp; ring
    exact he.le
  · constructor
    · exact (centersBound_scale _ _ _).2 hk.2
    · dsimp only [velocity]
      apply (centersBound_scale _ _ _).2
      apply (centersBound_add _ _ _).2
      constructor
      · apply centersBound_conditional hx hy
        rw [hxw,zero_add,abs_mul,abs_of_pos hr]
        calc
          r*|T| * weight p.1 ≤ r*weight p.1 := by nlinarith [weight_nonneg p.1,mul_le_mul_of_nonneg_left hT hr.le]
          _ ≤ r*(weight p.1+weight p.2+(2*P+H)*r) := by
            apply mul_le_mul_of_nonneg_left _ hr.le
            linarith [weight_nonneg p.2,mul_nonneg (show 0≤2*P+H by positivity) hr.le]
          _≤A := hA
      · apply (centersBound_scale _ _ _).2
        exact (centersBound_mean _ _ _).2 ⟨by simpa [hxw] using hA0,hx⟩

lemma weight_velocity_input_independent (r T h ψ s : ℝ) (n m N : ℕ)
    (e : ProbabilityNode T h (n+1)) (x z : MeanTree X d)
    (p q : MeanTree X d × MeanTree X d) :
    weight (velocity r T h ψ s n m N e x p).1+weight (velocity r T h ψ s n m N e x p).2=
    weight (velocity r T h ψ s n m N e z q).1+weight (velocity r T h ψ s n m N e z q).2 := by
  simp only [velocity,weight_scale,weight_add,weight_mean,weight_conditional,
    kernelQuadrature,kernelAction,kernelCorrection,weight_sumFamily]

lemma velocity_root_weights {r T h ψ s P H Q S : ℝ}
    (hr : 0 < r) (hs : 0 < s) (hT : |T|≤1)
    (hP : 0≤P) (hH : 0≤H) (hQ : 0≤Q) (hS : 0≤S)
    (n m N : ℕ) (e : ProbabilityNode T h (n+1))
    (ht : ∀j : ProbabilityNode T h (n+1),|probabilityNodeTime T h (n+1) j|≤1)
    (hpw : ∀s i,∑j,|reanchorWeight (probabilityWeight T h (n+1)) s i j|≤P)
    (hhw : ∀k : Fin (m+1),∀i,∑j,|harmonicWeight (n+1) (ψ*angleNodes m k) i j|≤H)
    (hqw : ∑j,|terminalQuadratureWeight T h n j|≤Q)
    (hsw : (∑j : Fin (m+1),|derivativeWeight (angleNodes m) j/ψ|)≤S)
    (x : MeanTree X d) (p : MeanTree X d × MeanTree X d) :
    weight (velocity r T h ψ s n m N e x p).1+
      weight (velocity r T h ψ s n m N e x p).2≤(Q*S*P+2)/s := by
  rw [weight_velocity_input_independent r T h ψ s n m N e x zero p (zero,zero)]
  exact (velocity_weights (A:=r*((2*P+H)*r)) hr hs hT hP hH hQ hS n m N e ht hpw hhw hqw hsw
    zero (zero,zero) (by simp) (by simp) (by simp) (by simp) (by simp)).1

lemma pairPicard_weights {I : Type*} [Fintype I] (w : I → I → ℝ)
    (φ : MeanTree X d × MeanTree X d → MeanTree X d × MeanTree X d)
    (a : MeanTree X d × MeanTree X d) {B K : ℝ} (hB : 0≤B) (hK : 0≤K)
    (hw : ∀i,∑j,|w i j|≤B)
    (hφ : ∀p,weight (φ p).1+weight (φ p).2≤K) (N : ℕ) (i : I) :
    weight (pairPicard w φ a N i).1+weight (pairPicard w φ a N i).2≤
      weight a.1+weight a.2+B*K := by
  cases N with
  | zero => simpa only [pairPicard] using le_add_of_nonneg_right (a:=weight a.1+weight a.2) (mul_nonneg hB hK)
  | succ N =>
    simp only [pairPicard,weight_add,weight_sumFamily,weight_scale]
    have he : (∑j,|w i j| * weight (φ (pairPicard w φ a N j)).1)+
        (∑j,|w i j| * weight (φ (pairPicard w φ a N j)).2)≤B*K := by
      rw [←Finset.sum_add_distrib]
      calc
        _≤∑j,|w i j| * K := Finset.sum_le_sum (fun j _ => by rw [←mul_add]; exact mul_le_mul_of_nonneg_left (hφ _) (abs_nonneg _))
        _=(∑j,|w i j|)*K := (Finset.sum_mul _ _ _).symm
        _≤B*K := mul_le_mul_of_nonneg_right (hw i) hK
    linarith

lemma centersBound_pairPicard {I : Type*} [Fintype I] (w : I → I → ℝ)
    (φ : MeanTree X d × MeanTree X d → MeanTree X d × MeanTree X d)
    (a : MeanTree X d × MeanTree X d) {A B K : ℝ} (hB : 0≤B) (hK : 0≤K)
    (hw : ∀i,∑j,|w i j|≤B)
    (hφw : ∀p,weight (φ p).1+weight (φ p).2≤K)
    (ha : centersBound A a.1 ∧ centersBound A a.2)
    (hφ : ∀p,weight p.1+weight p.2≤weight a.1+weight a.2+B*K →
      centersBound A p.1 → centersBound A p.2 →
      centersBound A (φ p).1 ∧ centersBound A (φ p).2) (N : ℕ) (i : I) :
    centersBound A (pairPicard w φ a N i).1 ∧ centersBound A (pairPicard w φ a N i).2 := by
  induction N generalizing i with
  | zero => exact ha
  | succ N ih =>
    have hstep (j : I) := hφ _ (pairPicard_weights w φ a hB hK hw hφw N j) (ih j).1 (ih j).2
    exact ⟨(centersBound_add _ _ _).2 ⟨ha.1,centersBound_sumFamily _ _ (fun j => (centersBound_scale _ _ _).2 (hstep j).1)⟩,
      (centersBound_add _ _ _).2 ⟨ha.2,centersBound_sumFamily _ _ (fun j => (centersBound_scale _ _ _).2 (hstep j).2)⟩⟩
end LogConcaveSampling.MeanTree

end

end

section

noncomputable section
namespace LogConcaveSampling.MeanTree
open MeasureTheory Quadrature FinitePicard
open scoped Classical BigOperators

variable {X : Type*} [MeasurableSpace X] {d : ℕ}

theorem centeringStates_weights {r T h ψ s P H Q S B A : ℝ}
    (hr : 0 < r) (hs : 0 < s) (hT : |T|≤1)
    (hP : 0≤P) (hH : 0≤H) (hQ : 0≤Q) (hS : 0≤S) (hB : 0≤B)
    (n m N nc Nc : ℕ) (e : ProbabilityNode T h (n+1))
    (ht : ∀j : ProbabilityNode T h (n+1),|probabilityNodeTime T h (n+1) j|≤1)
    (hpw : ∀a i,∑j,|reanchorWeight (probabilityWeight T h (n+1)) a i j|≤P)
    (hhw : ∀k : Fin (m+1),∀i,∑j,|harmonicWeight (n+1) (ψ*angleNodes m k) i j|≤H)
    (hqw : ∑j,|terminalQuadratureWeight T h n j|≤Q)
    (hsw : (∑j : Fin (m+1),|derivativeWeight (angleNodes m) j/ψ|)≤S)
    (hcw : ∀i,∑j,|centeringWeight nc i j|≤B)
    (x y g : MeanTree X d) (hxw : weight x=0)
    (hx : centersBound A x) (hy : centersBound A y) (hg : centersBound A g)
    (hA : r*(weight y+weight g+B*((Q*S*P+2)/s)+(2*P+H)*r)≤A)
    (i : Fin (nc+1)) :
    weight (centeringStates r T h ψ s n m N nc Nc e x y g i).1+
      weight (centeringStates r T h ψ s n m N nc Nc e x y g i).2≤
        weight y+weight g+B*((Q*S*P+2)/s) ∧
    centersBound A (centeringStates r T h ψ s n m N nc Nc e x y g i).1 ∧
      centersBound A (centeringStates r T h ψ s n m N nc Nc e x y g i).2 := by
  have hK : 0≤(Q*S*P+2)/s := by positivity
  have hφ := velocity_root_weights (X:=X) (d:=d) hr hs hT hP hH hQ hS n m N e ht hpw hhw hqw hsw x
  constructor
  · exact pairPicard_weights _ _ (y,g) hB hK hcw hφ Nc i
  · apply centersBound_pairPicard _ _ (y,g) hB hK hcw hφ ⟨hy,hg⟩ _ Nc i
    intro p hp hpy hpg
    exact (velocity_weights hr hs hT hP hH hQ hS n m N e ht hpw hhw hqw hsw x p hxw hx hpy hpg
      ((mul_le_mul_of_nonneg_left (add_le_add_left hp _) hr.le).trans hA)).2

theorem meanCircuit_weights {r T h ψ s P H Q S B A : ℝ}
    (hr : 0 < r) (hs : 0 < s) (hT : |T|≤1)
    (hP : 0≤P) (hH : 0≤H) (hQ : 0≤Q) (hS : 0≤S) (hB : 0≤B)
    (n m N nc Nc : ℕ) (e : ProbabilityNode T h (n+1))
    (ht : ∀j : ProbabilityNode T h (n+1),|probabilityNodeTime T h (n+1) j|≤1)
    (hpw : ∀a i,∑j,|reanchorWeight (probabilityWeight T h (n+1)) a i j|≤P)
    (hhw : ∀k : Fin (m+1),∀i,∑j,|harmonicWeight (n+1) (ψ*angleNodes m k) i j|≤H)
    (hqw : ∑j,|terminalQuadratureWeight T h n j|≤Q)
    (hsw : (∑j : Fin (m+1),|derivativeWeight (angleNodes m) j/ψ|)≤S)
    (hcw : ∀i,∑j,|centeringWeight nc i j|≤B)
    (hout : ∑j,|Quadrature.weight (probabilityNodes nc) j 0 1|≤B)
    (x y g : MeanTree X d) (hxw : weight x=0)
    (hx : centersBound A x) (hy : centersBound A y) (hg : centersBound A g)
    (hA : r*(weight y+weight g+B*((Q*S*P+2)/s)+(2*P+H)*r)≤A) :
    weight (meanCircuit r T h ψ s n m N nc Nc e x y g)≤|s| * weight g+B ∧
      centersBound A (meanCircuit r T h ψ s n m N nc Nc e x y g) := by
  have hz := centeringStates_weights hr hs hT hP hH hQ hS hB n m N nc Nc e ht hpw hhw hqw hsw hcw x y g hxw hx hy hg hA
  constructor
  · simpa only [meanCircuit,weight_add,weight_scale,weight_sumFamily,weight_conditional,mul_one]
      using add_le_add_right hout (|s| * weight g)
  · apply (centersBound_add _ _ _).2
    refine ⟨(centersBound_scale _ _ _).2 hg,centersBound_sumFamily _ _ ?_⟩
    intro j
    apply (centersBound_scale _ _ _).2
    apply centersBound_conditional hx (hz j).2.1
    rw [hxw,zero_add,abs_mul,abs_of_pos hr]
    calc
      r*|T| * weight (centeringStates r T h ψ s n m N nc Nc e x y g j).1
          ≤r*weight (centeringStates r T h ψ s n m N nc Nc e x y g j).1 := by
        simpa only [mul_one] using mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hT hr.le) (weight_nonneg (centeringStates r T h ψ s n m N nc Nc e x y g j).1)
      _ ≤ r*(weight y+weight g+B*((Q*S*P+2)/s)+(2*P+H)*r) := by
        apply mul_le_mul_of_nonneg_left _ hr.le
        have hb := (hz j).1
        linarith [weight_nonneg (centeringStates r T h ψ s n m N nc Nc e x y g j).2,
          mul_nonneg (show 0≤2*P+H by positivity) hr.le]
      _≤A := hA
end LogConcaveSampling.MeanTree

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
open MeasureTheory Quadrature FinitePicard
open scoped Classical BigOperators

variable {X : Type*} [MeasurableSpace X] {d : ℕ}

lemma literalMean_weights {r T h ψ σ P H Q S B A Af : ℝ}
    (hr : 0 < r) (hσ : 0<σ) (hT : |T|≤1)
    (hP : 0≤P) (hH : 0≤H) (hQ : 0≤Q) (hS : 0≤S) (hB : 0≤B)
    (n m N nc Nc : ℕ) (e : ProbabilityNode T h (n+1))
    (ht : ∀j : ProbabilityNode T h (n+1),|probabilityNodeTime T h (n+1) j|≤1)
    (hpw : ∀a i,∑j,|reanchorWeight (probabilityWeight T h (n+1)) a i j|≤P)
    (hhw : ∀k : Fin (m+1),∀i,∑j,|harmonicWeight (n+1) (ψ*angleNodes m k) i j|≤H)
    (hqw : ∑j,|terminalQuadratureWeight T h n j|≤Q)
    (hsw : (∑j : Fin (m+1),|derivativeWeight (angleNodes m) j/ψ|)≤S)
    (hcw : ∀i,∑j,|centeringWeight nc i j|≤B)
    (hout : ∑j,|Quadrature.weight (probabilityNodes nc) j 0 1|≤B)
    (hA₁ : 2*B*(Q*S*P+2)≤A) (hA₂ : 2*P+H≤A) (hAf : B≤Af) :
    weight (literalMean (d:=d) r T h ψ σ n m N nc Nc e)≤Af ∧
      centersBound (A*(r/σ+r^2)) (literalMean (d:=d) r T h ψ σ n m N nc Nc e) := by
  have hbound : r*(B*((Q*S*P+2)/(σ/2))+(2*P+H)*r)≤A*(r/σ+r^2) := by
    have h₁ := mul_le_mul_of_nonneg_right hA₁ (show 0 ≤ r/σ by positivity)
    have h₂ := mul_le_mul_of_nonneg_right hA₂ (sq_nonneg r)
    have he : r*(B*((Q*S*P+2)/(σ/2))+(2*P+H)*r)=
        (2*B*(Q*S*P+2))*(r/σ)+(2*P+H)*r^2 := by field_simp
    rw [he]
    nlinarith
  have hh := meanCircuit_weights (d:=d) (X:=MeanInput d) hr (by positivity : 0<σ/2) hT
    hP hH hQ hS hB n m N nc Nc e ht hpw hhw hqw hsw hcw hout
    (anchor Prod.fst (by fun_prop)) (anchor (fun z => z.2.1) (by fun_prop))
    (anchor (fun z => z.2.2) (by fun_prop)) (by simp) (by simp) (by simp) (by simp)
    (by simpa only [weight_anchor,zero_add] using hbound)
  simp only [weight_anchor,mul_zero,zero_add] at hh
  exact ⟨hh.1.trans hAf,hh.2⟩
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

lemma MeanSize.nonneg {lam q r σ : ℝ} (hlam : 0 ≤ lam) (h : MeanSize lam q r σ) : 0 ≤ q :=
  (mul_nonneg hlam (sq_nonneg r)).trans h.2.2.2.1

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
lemma meanCenterBudget_small {lam q r σ : ℝ} (h : MeanSize lam q r σ) (hA : 0 ≤ C.A) :
    lam*C.meanCenterBudget r σ ≤ 2*C.A*q := by
  have hs : lam*r/σ ≤ q := (div_le_iff₀ h.2.2.1).2 h.2.2.2.2
  have hh := mul_le_mul_of_nonneg_left (add_le_add hs h.2.2.2.1) hA
  unfold meanCenterBudget
  convert! hh using 1 <;> ring

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

lemma angle_mem (hψ : 0≤C.ψ) (j : Fin (C.m+1)) :
    C.ψ*angleNodes C.m j∈Set.Icc (0:ℝ) 1 := by
  have hj : 0≤angleNodes C.m j := by simp [angleNodes]
  have hv : C.v≤1 := by
    have hR : Real.sqrt (1-C.T^2)≤1 := by
      apply (Real.sqrt_le_iff).mpr
      exact ⟨by norm_num,by nlinarith [sq_nonneg C.T]⟩
    nlinarith [C.angle_small]
  exact ⟨mul_nonneg hψ hj,(le_abs_self _).trans ((C.angle_bound j).trans hv)⟩

lemma meanTree_actual_weights {d : ℕ} {r σ : ℝ} (hr : 0 < r) (hσ : 0<σ)
    (hψ : 0≤C.ψ) : weight (C.meanTree (d:=d) r σ)≤C.actualAf ∧
    centersBound (C.actualA*(r/σ+r^2)) (C.meanTree (d:=d) r σ) := by
  have hT0 : 0<C.T := by linarith [C.T_lower]
  have hP := fixedProbabilityBudget_spec C.n
  have hB := fixedCenteringBudget_spec C.nc
  have hP0 := hP.1
  have hB0 := hB.1
  have hQ : 0≤C.quadratureBudget := by unfold quadratureBudget; positivity
  have hS : 0≤C.derivativeBudget := by unfold derivativeBudget; positivity
  have hh := (harmonicWeight_budget (C.n+1) (Nat.succ_pos C.n)).choose_spec
  apply literalMean_weights hr hσ (by rw [abs_of_pos hT0]; exact C.T_upper.le)
    (by positivity : 0≤2*fixedProbabilityBudget C.n) (fixedHarmonicBudget C.n).coe_nonneg
    hQ hS hB.1 C.n C.m C.N C.nc C.Nc C.meanEndpoint
  · intro j
    have ht := probabilityNodeTime_mem hT0 C.T_upper C.h_pos (Nat.succ_pos C.n) j
    rw [abs_of_nonneg ht.1]
    exact ht.2.trans C.T_upper.le
  · intro a i
    exact reanchorWeight_budget _ (hP.2 hT0 C.T_upper C.h_pos) a i
  · intro k i
    exact hh _ (C.angle_mem hψ k).1 (C.angle_mem hψ k).2 i
  · exact le_rfl
  · exact le_rfl
  · exact hB.2.1
  · exact hB.2.2
  · unfold actualA
    have h := (fixedHarmonicBudget C.n).coe_nonneg
    linarith [hP.1]
  · unfold actualA
    have he : 0≤2*fixedCenteringBudget C.nc*
      (C.quadratureBudget*C.derivativeBudget*(2*fixedProbabilityBudget C.n)+2) := by positivity
    linarith
  · unfold actualAf
    linarith [hP.1]

end CircuitParameters
end LogConcaveSampling.OracleCompiler

end

end

end OAI
end

section
-- module Solutions.OAIQ048_LC.LogConcave_OraclePrograms_SampleParentEquivariant
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

lemma meanParent_lipschitz (V : Point d → ℝ) (S : SeedProgram d)
    (E : Expression (Point d × (Point d × Point d)) d)
    (u : Fin S.slots → ℝ) (v : Fin E.slots → ℝ) (T Ks Kx Ky : ℝ)
    (hKy : 0≤Ky) (hT : 0≤T)
    (hS : ∀x y g,‖S.program.run V (x,g)-S.program.run V (y,g)‖≤Ks*‖x-y‖)
    (hEx : ∀x y Y G g,‖E.eval V (x,(Y,G)) g-E.eval V (y,(Y,G)) g‖≤Kx*‖x-y‖)
    (hEy : ∀x Y Z G g,‖E.eval V (x,(Y,G)) g-E.eval V (x,(Z,G)) g‖≤Ky*‖Y-Z‖) :
    ∀x y g,‖(meanParent S E u v T).program.run V (x,g)-(meanParent S E u v T).program.run V (y,g)‖≤
      (Kx+Ky*T*Ks)*‖x-y‖ := by
  intro x y g
  rw [meanParent_run S E u v T V x g,meanParent_run S E u v T V y g]
  have hx := hEx x y (T • S.program.run V (x,leftBlock g)) (middleBlock g 0) (rightBlock g)
  have hy := hEy y (T • S.program.run V (x,leftBlock g)) (T • S.program.run V (y,leftBlock g))
    (middleBlock g 0) (rightBlock g)
  rw [←smul_sub,norm_smul,Real.norm_eq_abs,abs_of_nonneg hT] at hy
  have hs := mul_le_mul_of_nonneg_left (hS x y (leftBlock g)) (mul_nonneg hKy hT)
  have hn := norm_sub_le_norm_sub_add_norm_sub
    (E.eval V (x,(T • S.program.run V (x,leftBlock g),middleBlock g 0)) (rightBlock g))
    (E.eval V (y,(T • S.program.run V (x,leftBlock g),middleBlock g 0)) (rightBlock g))
    (E.eval V (y,(T • S.program.run V (y,leftBlock g),middleBlock g 0)) (rightBlock g))
  nlinarith
end LogConcaveSampling.OracleCompiler

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

lemma final_mean_size {lam q r σ R Af : ℝ} (hlam : 0≤lam)
    (h : MeanSize lam q r σ) (hR : 0<R) (hR1 : R≤1) (hAf : 0<Af) :
    MeanSize lam ((1+4*Af)*R*q) (r*R) (declaredNoise (Real.sqrt 3*σ/2) Af) := by
  have hr := h.1
  have hσ := h.2.2.1
  have hq := h.nonneg hlam
  have hroot : 1≤Real.sqrt 3 := by norm_num
  have hn : 0<declaredNoise (Real.sqrt 3*σ/2) Af := by unfold declaredNoise; positivity
  have hrR : r*R ≤ r := mul_le_of_le_one_right h.1.le hR1
  have hR2 : R^2≤R := by nlinarith
  have hsq := mul_le_mul_of_nonneg_right h.2.2.2.1 (sq_nonneg R)
  have hqR := mul_le_mul_of_nonneg_left hR2 hq
  have hAfR : R*q≤(1+4*Af)*R*q := by nlinarith [mul_nonneg hR.le hq]
  refine ⟨mul_pos h.1 hR,hrR.trans h.2.1,hn,?_,?_⟩
  · nlinarith [hsq]
  · have hσ : σ/(4*Af)≤declaredNoise (Real.sqrt 3*σ/2) Af := by
      unfold declaredNoise
      have hh := mul_le_mul_of_nonneg_right hroot h.2.2.1.le
      apply (le_div_iff₀ (by positivity : 0<2*Af)).2
      calc
        σ/(4*Af)*(2*Af)=σ/2 := by field_simp; ring
        _≤Real.sqrt 3*σ/2 := by linarith
    have hs := mul_le_mul_of_nonneg_right h.2.2.2.2 hR.le
    have ht := mul_le_mul_of_nonneg_left hσ (show 0≤4*Af*R*q by positivity)
    have hid : (4*Af*R*q)*(σ/(4*Af))=q*σ*R := by field_simp
    rw [hid] at ht
    have he : 4*Af*R*q≤(1+4*Af)*R*q := by nlinarith [mul_nonneg hR.le hq]
    have hh := mul_le_mul_of_nonneg_right he hn.le
    nlinarith

namespace CircuitParameters
variable (C : CircuitParameters)

lemma residual_pos : 0<Real.sqrt (1-C.T^2) := by
  apply Real.sqrt_pos.mpr
  nlinarith [C.T_lower,C.T_upper]
lemma residual_le_one : Real.sqrt (1-C.T^2)≤1 := by
  apply (Real.sqrt_le_iff).mpr
  exact ⟨by norm_num,by nlinarith [sq_nonneg C.T]⟩

theorem meanTree_valid {lam q r σ : ℝ} (hlam : 0≤lam) (hs : MeanSize lam q r σ)
    (hD : 0<C.D) (hψ : 0≤C.ψ) (hA : C.A=C.actualA) (hAf : C.Af=C.actualAf) :
    DeclaredRootValid C.D (C.meanCenterBudget r σ) C.Af
      (MeanSize lam ((1+4*C.Af)*Real.sqrt (1-C.T^2)*q))
      (MeanSize lam (q*(1+16*C.D*C.A/Real.sqrt (1-C.T^2))))
      (C.meanTree (d:=d) r σ) (Real.sqrt 3*σ/2) := by
  have hA0 : 0<C.A := hA ▸ C.actualA_pos
  have hAf0 : 0<C.Af := hAf ▸ C.actualAf_pos
  have hr := hs.1
  have hσ := hs.2.2.1
  have hb : 0<C.meanCenterBudget r σ := by unfold meanCenterBudget; positivity
  have hR := C.residual_pos
  have hq := hs.nonneg hlam
  have hw := C.meanTree_actual_weights (d:=d) hs.1 hs.2.2.1 hψ
  rw [←hA,←hAf] at hw
  have hg := (literalMean_geometry (d:=d) (r:=r) (σ:=σ) (N:=C.N) (nc:=C.nc) (Nc:=C.Nc)
    (by linarith [C.T_lower]) C.T_upper C.h_pos C.v_nonneg C.angle_bound C.meanEndpoint).2
  apply declaredRootValid_of_radius_bounds hD (mul_pos hs.1 hR) _ _ _ (by positivity) hw.1 hw.2
  · exact centers_mono _ (fun r' b h => h.radius hs.1.le (by linarith [C.T_lower]) C.T_upper) hg
  · have hf := meanCircuit_final_radius (d:=d) r C.T C.h C.ψ (σ/2) C.n C.m C.N C.nc C.Nc C.meanEndpoint
      (anchor Prod.fst (by fun_prop)) (anchor (fun z : MeanInput d => z.2.1) (by fun_prop))
      (fun z : MeanInput d => z.2.2) (by fun_prop)
    cases he : C.meanTree (d:=d) r σ with | node k b hb a rr cc =>
      change ∀i, MeanSize _ _ (rr i) _
      have hf' : ∀i,rr i=r*Real.sqrt (1-C.T^2) := by
        change rootScales (fun r' => r'=r*Real.sqrt (1-C.T^2)) (C.meanTree r σ) at hf
        rw [he] at hf
        exact hf
      intro i
      rw [hf' i]
      exact final_mean_size hlam hs hR C.residual_le_one hAf0
  · intro r' n hlo hhi hn _
    apply (internal_meanSize hlam hq hs.1 hs.2.1 hR hD hb hs.2.2.2.1 hlo hhi hn).mono
    have hsmall := C.meanCenterBudget_small hs hA0.le
    have hh := mul_le_mul_of_nonneg_left hsmall (show 0≤4*C.D/Real.sqrt (1-C.T^2) by positivity)
    have hx : 0≤C.D*C.A*q/Real.sqrt (1-C.T^2) := by positivity
    nlinarith [show (4*C.D/Real.sqrt (1-C.T^2))*(lam*C.meanCenterBudget r σ)=
      4*C.D*lam*C.meanCenterBudget r σ/Real.sqrt (1-C.T^2) by ring,
      show (4*C.D/Real.sqrt (1-C.T^2))*(2*C.A*q)=8*(C.D*C.A*q/Real.sqrt (1-C.T^2)) by ring,
      show q*(1+16*C.D*C.A/Real.sqrt (1-C.T^2))=q+16*(C.D*C.A*q/Real.sqrt (1-C.T^2)) by ring]

lemma mean_anchor_size {lam q r σ : ℝ} (hlam : 0≤lam) (hs : MeanSize lam q r σ)
    (hRT : Real.sqrt (1-C.T^2)≤C.T) :
    SampleSize lam (q/Real.sqrt (1-C.T^2)) r (Real.sqrt (1-C.T^2)/C.T) := by
  have hT : 0<C.T := by linarith [C.T_lower]
  have hR := C.residual_pos
  have hq := hs.nonneg hlam
  refine ⟨hs.1,hs.2.1,div_pos hR hT,(div_le_one hT).2 hRT,?_⟩
  calc
    lam*r^2≤q := hs.2.2.2.1
    _≤q/C.T := (le_div_iff₀ hT).2 (mul_le_of_le_one_right hq C.T_upper.le)
    _=(q/Real.sqrt (1-C.T^2))*(Real.sqrt (1-C.T^2)/C.T) := by field_simp

end CircuitParameters
end LogConcaveSampling.OracleCompiler

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

lemma pairGauge_measurable (C : ℝ) : Measurable (pairGauge (d:=d) C) := by unfold pairGauge; fun_prop
lemma one_le_pairGauge {C : ℝ} (hC : 0≤C) (z : Point d × Point d) : 1≤pairGauge C z := by
  unfold pairGauge; linarith [norm_nonneg z]
lemma pairGauge_change (C : ℝ) (x y : Point d × Point d) :
    pairGauge C y≤pairGauge C x+dist x y := by
  have hh := norm_le_norm_add_norm_sub x y
  dsimp [pairGauge]
  rw [dist_eq_norm]
  linarith

end LogConcaveSampling

end

end

end OAI
end

section
-- module Solutions.OAIQ048_LC.LogConcave_Dynamics_ProbabilityFlowGrowth
attribute [-instance] _root_.OAI.LogConcaveSampling.LowerBound.couplingLaw_probability _root_.OAI.LogConcaveSampling.LowerBound.remainingHaar_probability _root_.OAI.LogConcaveSampling.LowerBound.roundRandomLaw_probability _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_invInvariant _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_isHaar _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_probability _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_rightInvariant _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_compactSpace _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_measurableInv _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_measurableMul _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_secondCountable _root_.OAI.LogConcaveSampling.OracleCompiler.topSeedLaw_probability _root_.OAI.LogConcaveSampling.noiseKernel_markov
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

lemma probabilityFlow_growth {F : Point d → ℝ} {lam : ℝ≥0} (hF : Primitive F lam)
    (x : Point d) {r T : ℝ} (hr : 0 ≤ r) (hr1 : r≤1)
    (hl : (lam:ℝ)*r^2≤1/2) (hT : 0≤T) (hT1 : T<1) (z : Point d) :
    ‖fullProbabilityFlow hF x hr hl T z‖ ≤ circuitGrowthConstant*(circuitD F x+‖z‖) := by
  have hf := probabilityFlow_initial_displacement hF x hr hl z ⟨hT,hT1.le⟩
  have hn := norm_le_norm_sub_add (fullProbabilityFlow hF x hr hl T z) z
  rw [field_zero_eq_gradient] at hf
  have hD : ‖gradient F x‖ ≤ circuitD F x := le_add_of_nonneg_left (Real.sqrt_nonneg _)
  have hd := sqrt_le_circuitD F x
  have hc := circuitD_nonneg F x
  have h₁ := mul_le_mul_of_nonneg_right hr1 (norm_nonneg (gradient F x))
  have h₂ := mul_le_mul_of_nonneg_right (show (lam:ℝ)*r^2≤1 by linarith)
    (show 0≤Real.pi*Real.sqrt d+‖z‖ by positivity)
  have hp := mul_le_mul_of_nonneg_left hd Real.pi_pos.le
  have hb : r*‖gradient F x‖+((lam:ℝ)*r^2)*(Real.pi*Real.sqrt d+‖z‖)≤
      (Real.pi+1)*(circuitD F x+‖z‖) := by
    nlinarith [mul_nonneg Real.pi_pos.le (norm_nonneg z)]
  have hh := mul_le_mul_of_nonneg_left hb terminalTransportConstant_pos.le
  have hz : ‖z‖≤(Real.pi+1)*(circuitD F x+‖z‖) := by
    nlinarith [mul_nonneg Real.pi_pos.le (norm_nonneg z),mul_nonneg Real.pi_pos.le hc]
  have hc' : terminalTransportConstant+1≤8*(terminalTransportConstant+1) := by
    linarith [terminalTransportConstant_pos]
  have hh' := mul_le_mul_of_nonneg_right hc' (show 0≤(Real.pi+1)*(circuitD F x+‖z‖) by positivity)
  dsimp [circuitGrowthConstant]
  nlinarith

lemma interpolationLaw_norm_sq {F : Point d → ℝ} {lam : ℝ≥0} (hF : Primitive F lam)
    (x : Point d) {r T : ℝ} (hr : 0 ≤ r) (hr1 : r≤1)
    (hl : (lam:ℝ)*r^2≤1/2) (hT : 0≤T) (hT1 : T<1) :
    Integrable (fun z : Point d => ‖z‖^2) (interpolationLaw F x r T) ∧
    (∫z : Point d,‖z‖^2 ∂interpolationLaw F x r T)≤4*circuitGrowthConstant^2*(circuitD F x)^2 := by
  have hm := (fullProbabilityFlow_lipschitz hF x hr hl ⟨hT,hT1.le⟩).continuous.measurable
  have hg := gaussian_growth_sq_moment (fullProbabilityFlow_lipschitz hF x hr hl ⟨hT,hT1.le⟩).continuous
    circuitGrowthConstant_pos.le (circuitD_nonneg F x)
    (probabilityFlow_growth hF x hr hr1 hl hT hT1)
  rw [←fullProbabilityFlow_interpolation_closed hF x hr hl hT hT1]
  refine ⟨(integrable_map_measure (by fun_prop) hm.aemeasurable).mpr hg.1,?_⟩
  rw [integral_map hm.aemeasurable (by fun_prop)]
  apply hg.2.trans
  have hs := pow_le_pow_left₀ (Real.sqrt_nonneg (d:ℝ)) (sqrt_le_circuitD F x) 2
  rw [Real.sq_sqrt (Nat.cast_nonneg d)] at hs
  nlinarith [mul_le_mul_of_nonneg_left hs (sq_nonneg circuitGrowthConstant)]

lemma pairGauge_sq_bound {C : ℝ} (hC : 0≤C) (z : Point d × Point d) :
    (pairGauge C z)^2≤4*(1+C)^2+4*‖z.1‖^2+4*‖z.2‖^2 := by
  have hp : ‖z‖≤‖z.1‖+‖z.2‖ := by
    change max ‖z.1‖ ‖z.2‖≤_
    exact max_le (le_add_of_nonneg_right (norm_nonneg _)) (le_add_of_nonneg_left (norm_nonneg _))
  have hq : 0≤pairGauge C z := by unfold pairGauge; positivity
  have hb : pairGauge C z≤1+C+‖z.1‖+‖z.2‖ := by dsimp [pairGauge]; linarith
  have hh := pow_le_pow_left₀ hq hb 2
  nlinarith [sq_nonneg (1+C-‖z.1‖-‖z.2‖),sq_nonneg (‖z.1‖-‖z.2‖)]

lemma pairGauge_moment (μ : Measure (Point d)) [IsProbabilityMeasure μ]
    (hi : Integrable (fun z : Point d => ‖z‖^2) μ) {C : ℝ} (hC : 0≤C) :
    Integrable (fun z => (pairGauge C z)^2) (μ.prod (stdGaussian (Point d))) ∧
    (∫z,(pairGauge C z)^2 ∂μ.prod (stdGaussian (Point d)))≤
      4*(1+C)^2+4*(∫z,‖z‖^2 ∂μ)+4*d := by
  have hj : Integrable (fun z : Point d => ‖z‖^2) (stdGaussian (Point d)) := by
    simpa only [id_eq] using (IsGaussian.memLp_two_id (μ:=stdGaussian (Point d))).norm.integrable_sq
  have hdom : Integrable (fun z : Point d × Point d => 4*(1+C)^2+4*‖z.1‖^2+4*‖z.2‖^2)
      (μ.prod (stdGaussian (Point d))) := ((integrable_const (4*(1+C)^2)).add ((hi.comp_fst (stdGaussian (Point d))).const_mul 4)).add
    ((hj.comp_snd μ).const_mul 4)
  have hgi : Integrable (fun z => (pairGauge C z)^2) (μ.prod (stdGaussian (Point d))) := by
    apply hdom.mono' ((pairGauge_measurable C).pow_const 2).aestronglyMeasurable
    exact Filter.Eventually.of_forall (fun z => by simpa only [Real.norm_eq_abs,abs_sq,Pi.add_apply] using pairGauge_sq_bound hC z)
  refine ⟨hgi,?_⟩
  apply (integral_mono hgi hdom (pairGauge_sq_bound hC)).trans_eq
  have hf : Integrable (fun z : Point d × Point d => 4*‖z.1‖^2) (μ.prod (stdGaussian (Point d))) := (hi.comp_fst _).const_mul _
  have hs : Integrable (fun z : Point d × Point d => 4*‖z.2‖^2) (μ.prod (stdGaussian (Point d))) := (hj.comp_snd _).const_mul _
  have hl : Integrable (fun z : Point d × Point d => 4*(1+C)^2+4*‖z.1‖^2) (μ.prod (stdGaussian (Point d))) := (integrable_const _).add hf
  rw [integral_add hl hs,integral_add (integrable_const _) hf,integral_const,probReal_univ,one_smul,
    integral_const_mul,integral_const_mul]
  rw [integral_fun_fst (fun z : Point d => ‖z‖^2),integral_fun_snd (fun z : Point d => ‖z‖^2)]
  simp only [probReal_univ,one_smul,stdGaussian_sq_norm]

lemma pairGauge_interpolation_moment {F : Point d → ℝ} {lam : ℝ≥0} (hF : Primitive F lam)
    (x : Point d) {r T : ℝ} (hr : 0 ≤ r) (hr1 : r≤1)
    (hl : (lam:ℝ)*r^2≤1/2) (hT : 0≤T) (hT1 : T<1) (hd : 1≤d) :
    Integrable (fun z => (pairGauge (circuitD F x) z)^2)
      ((interpolationLaw F x r T).prod (stdGaussian (Point d))) ∧
    (∫z,(pairGauge (circuitD F x) z)^2 ∂(interpolationLaw F x r T).prod (stdGaussian (Point d)))≤
      (20+16*circuitGrowthConstant^2)*(circuitD F x)^2 := by
  let := interpolationLaw_probability hF x hr (by linarith only [hl]) T
  have hm := interpolationLaw_norm_sq hF x hr hr1 hl hT hT1
  have hg := pairGauge_moment _ hm.1 (circuitD_nonneg F x)
  refine ⟨hg.1,hg.2.trans ?_⟩
  have hs : (1:ℝ)≤Real.sqrt d := by
    exact (by norm_num : (1:ℝ)=Real.sqrt 1).trans_le (Real.sqrt_le_sqrt (by exact_mod_cast hd))
  have hD := hs.trans (sqrt_le_circuitD F x)
  have hd2 := pow_le_pow_left₀ (Real.sqrt_nonneg (d:ℝ)) (sqrt_le_circuitD F x) 2
  rw [Real.sq_sqrt (Nat.cast_nonneg d)] at hd2
  have hs2 := pow_le_pow_left₀ (show 0≤1+circuitD F x by positivity [circuitD_nonneg F x])
    (show 1+circuitD F x≤2*circuitD F x by linarith) 2
  nlinarith [hm.2]

end LogConcaveSampling

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

lemma literalMean_variationX {r T h ψ σ v : ℝ} {n m N nc Nc : ℕ}
    (hr : 0 ≤ r) (hT : 0<T) (hT1 : T<1) (hh : 0<h) (hv : 0≤v)
    (hψ : ∀j : Fin (m+1),|ψ*angleNodes m j|≤v) (e : ProbabilityNode T h (n+1))
    (x y Y G : Point d) :
    BaseVariation ‖x-y‖ (x,(Y,G)) (y,(Y,G)) (literalMean r T h ψ σ n m N nc Nc e) := by
  have hg := literalMean_geometry (d:=d) (r:=r) (σ:=σ) (N:=N) (nc:=nc) (Nc:=Nc) hT hT1 hh hv hψ e
  apply baseVariation_of_centers
  · rw [hg.1]
    simp
  · exact centers_mono _ (fun r' b hb => by
      simpa only [Prod.fst,Prod.snd,sub_self,norm_zero,add_zero,mul_zero] using hb.variation hr hT1.le (x,(Y,G)) (y,(Y,G))) hg.2

lemma literalMean_variationY {r T h ψ σ v : ℝ} {n m N nc Nc : ℕ}
    (hr : 0 ≤ r) (hT : 0<T) (hT1 : T<1) (hh : 0<h) (hv : 0≤v)
    (hψ : ∀j : Fin (m+1),|ψ*angleNodes m j|≤v) (e : ProbabilityNode T h (n+1))
    (x Y Z G : Point d) :
    BaseVariation (r*‖Y-Z‖) (x,(Y,G)) (x,(Z,G)) (literalMean r T h ψ σ n m N nc Nc e) := by
  have hg := literalMean_geometry (d:=d) (r:=r) (σ:=σ) (N:=N) (nc:=nc) (Nc:=Nc) hT hT1 hh hv hψ e
  apply baseVariation_of_centers
  · rw [hg.1]
    simp only [sub_self,norm_zero]
    positivity
  · exact centers_mono _ (fun r' b hb => by
      simpa only [Prod.fst,Prod.snd,sub_self,norm_zero,add_zero,zero_add] using hb.variation hr hT1.le (x,(Y,G)) (x,(Z,G))) hg.2

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
-- module Solutions.OAIQ048_LC.LogConcave_OraclePrograms_MeanTreeBase
attribute [-instance] _root_.OAI.LogConcaveSampling.LowerBound.couplingLaw_probability _root_.OAI.LogConcaveSampling.LowerBound.remainingHaar_probability _root_.OAI.LogConcaveSampling.LowerBound.roundRandomLaw_probability _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_invInvariant _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_isHaar _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_probability _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_rightInvariant _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_compactSpace _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_measurableInv _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_measurableMul _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_secondCountable _root_.OAI.LogConcaveSampling.OracleCompiler.topSeedLaw_probability _root_.OAI.LogConcaveSampling.noiseKernel_markov
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
namespace LogConcaveSampling.OracleCompiler.CircuitParameters
open MeanTree MeasureTheory Quadrature Expression
open scoped Classical

variable (C : CircuitParameters) {d : ℕ}

lemma meanTree_base (r σ : ℝ) :
    base (C.meanTree (d:=d) r σ)=fun z => (σ/2) • z.2.2 := by
  exact (literalMean_geometry (d:=d) (r:=r) (σ:=σ) (N:=C.N) (nc:=C.nc) (Nc:=C.Nc)
    (by linarith [C.T_lower]) C.T_upper C.h_pos C.v_nonneg C.angle_bound C.meanEndpoint).1

lemma meanCompiled_variation {r σ Lf Li : ℝ} (hr : 0 < r) (hσ : 0<σ)
    (hψ : 0≤C.ψ) (hA : C.A=C.actualA) (hAf : C.Af=C.actualAf)
    (hLf : 0≤Lf) (hLi : 0≤Li) (hsmall : Li*C.meanCenterBudget r σ≤1)
    (V : Point d → ℝ) (P : Bool → ℝ → ℝ → Prop) (M : Bool → ℝ → ℝ → SeedProgram d)
    (hm : ∀r τ,P true r τ → ∀u v g,‖(M true r τ).program.run V (u,g)-(M true r τ).program.run V (v,g)‖≤Lf*‖u-v‖)
    (hmi : ∀r τ,P false r τ → ∀u v g,‖(M false r τ).program.run V (u,g)-(M false r τ).program.run V (v,g)‖≤Li*‖u-v‖)
    (n : ℝ) (hready : RootShiftReady C.D (C.meanCenterBudget r σ) C.Af
      (P true) (P false) (C.meanTree (d:=d) r σ) n) :
    let E := compileDeclaredRoot C.D (C.meanCenterBudget r σ) C.Af
      (M true) (M false) (C.meanTree (d:=d) r σ) n
    let K := C.Af*Lf*(depth (C.meanTree (d:=d) r σ):ℝ)
    (∀x y Y G g,‖E.eval V (x,(Y,G)) g-E.eval V (y,(Y,G)) g‖≤K*‖x-y‖) ∧
    (∀x Y Z G g,‖E.eval V (x,(Y,G)) g-E.eval V (x,(Z,G)) g‖≤(K*r)*‖Y-Z‖) := by
  have hw := C.meanTree_actual_weights (d:=d) hr hσ hψ
  rw [←hAf,←hA] at hw
  have hT0 : 0<C.T := by linarith [C.T_lower]
  constructor
  · intro x y Y G g
    have he := compileDeclaredRoot_variation hLf hLi (norm_nonneg (x-y)) hsmall V P M hm hmi
      (C.meanTree r σ) n (x,(Y,G)) (y,(Y,G))
      (literalMean_variationX hr.le hT0 C.T_upper C.h_pos C.v_nonneg C.angle_bound C.meanEndpoint x y Y G)
      (Bf:=0) (by rw [C.meanTree_base]; simp) hw.1 hw.2 hready g
    simpa only [add_zero] using he
  · intro x Y Z G g
    have he := compileDeclaredRoot_variation hLf hLi (mul_nonneg hr.le (norm_nonneg (Y-Z))) hsmall V P M hm hmi
      (C.meanTree r σ) n (x,(Y,G)) (x,(Z,G))
      (literalMean_variationY hr.le hT0 C.T_upper C.h_pos C.v_nonneg C.angle_bound C.meanEndpoint x Y Z G)
      (Bf:=0) (by rw [C.meanTree_base]; simp) hw.1 hw.2 hready g
    simpa only [add_zero,mul_assoc] using he

end LogConcaveSampling.OracleCompiler.CircuitParameters

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

lemma pair_dist_bounds (z w : Point d × Point d) :
    ‖z.1-w.1‖≤dist z w ∧ ‖z.2-w.2‖≤dist z w := by
  change ‖z.1-w.1‖≤ max (dist z.1 w.1) (dist z.2 w.2) ∧
    ‖z.2-w.2‖≤ max (dist z.1 w.1) (dist z.2 w.2)
  simp only [dist_eq_norm]
  exact ⟨le_max_left _ _,le_max_right _ _⟩

lemma meanTree_anchorVariation {r σ : ℝ} (hr : 0 ≤ r) (x : Point d) (z w : Point d × Point d) :
    BaseVariation ((2*r+|σ/2|)*dist z w) (x,z) (x,w) (C.meanTree r σ) := by
  have hg := literalMean_geometry (d:=d) (r:=r) (σ:=σ) (N:=C.N) (nc:=C.nc) (Nc:=C.Nc)
    (by linarith [C.T_lower]) C.T_upper C.h_pos C.v_nonneg C.angle_bound C.meanEndpoint
  have hd := pair_dist_bounds z w
  apply baseVariation_of_centers
  · rw [C.meanTree_base]
    simp only [←smul_sub,norm_smul,Real.norm_eq_abs]
    nlinarith [mul_le_mul_of_nonneg_left hd.2 (abs_nonneg (σ/2)),mul_nonneg hr (dist_nonneg (x:=z) (y:=w))]
  · exact centers_mono _ (fun r' b hb => by
      have he := hb.variation hr C.T_upper.le (x,z) (x,w)
      simp only [sub_self,norm_zero,zero_add] at he
      nlinarith [mul_le_mul_of_nonneg_left (add_le_add hd.1 hd.2) hr,
        mul_nonneg (abs_nonneg (σ/2)) (dist_nonneg (x:=z) (y:=w))]) hg.2

lemma meanTree_anchor_lipschitz {F : Point d → ℝ} {lam : ℝ≥0} (hF : Primitive F lam)
    {r σ : ℝ} (hr : 0 < r) (hl : (lam:ℝ)*r^2≤1/4) (x : Point d) :
    ∃K : ℝ≥0,LipschitzWith K (fun z : Point d × Point d => (C.meanTree r σ).eval F (x,z)) := by
  have hg := literalMean_geometry (d:=d) (r:=r) (σ:=σ) (N:=C.N) (nc:=C.nc) (Nc:=C.Nc)
    (by linarith [C.T_lower]) C.T_upper C.h_pos C.v_nonneg C.angle_bound C.meanEndpoint
  apply eval_exists_lipschitz hF (C.meanTree r σ) (fun z => (x,z))
  · rw [C.meanTree_base]
    exact ⟨_,(lipschitzWith_smul (σ/2)).comp LipschitzWith.prod_snd⟩
  · apply centers_mono _ (fun r' b hb => ?_) hg.2
    have hr' := hb.radius_pos hr (by linarith [C.T_lower]) C.T_upper
    have hb' := hb.radius hr.le (by linarith [C.T_lower]) C.T_upper
    have hs := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hr'.le hb'.2 2) lam.coe_nonneg
    refine ⟨hr',hs.trans hl,?_⟩
    obtain ⟨ρ,hρ,θ,hθ,he,rfl⟩ := hb
    exact ⟨_,(LipschitzWith.const x).add ((lipschitzWith_smul (r*ρ)).comp
      (((lipschitzWith_smul (Real.cos θ)).comp LipschitzWith.prod_fst).add
      ((lipschitzWith_smul (Real.sin θ)).comp LipschitzWith.prod_snd)))⟩

lemma meanCompiled_anchor_lipschitz {r σ Lf Li : ℝ} (hr : 0 < r) (hσ : 0<σ)
    (hψ : 0≤C.ψ) (hA : C.A=C.actualA) (hAf : C.Af=C.actualAf)
    (hLf : 0≤Lf) (hLi : 0≤Li) (hsmall : Li*C.meanCenterBudget r σ≤1)
    (V : Point d → ℝ) (P : Bool → ℝ → ℝ → Prop) (M : Bool → ℝ → ℝ → SeedProgram d)
    (hm : ∀r τ,P true r τ → ∀u v g,‖(M true r τ).program.run V (u,g)-(M true r τ).program.run V (v,g)‖≤Lf*‖u-v‖)
    (hmi : ∀r τ,P false r τ → ∀u v g,‖(M false r τ).program.run V (u,g)-(M false r τ).program.run V (v,g)‖≤Li*‖u-v‖)
    (n : ℝ) (hready : RootShiftReady C.D (C.meanCenterBudget r σ) C.Af
      (P true) (P false) (C.meanTree (d:=d) r σ) n) (x : Point d) :
    let E := compileDeclaredRoot C.D (C.meanCenterBudget r σ) C.Af
      (M true) (M false) (C.meanTree (d:=d) r σ) n
    ∃K : ℝ,0≤K ∧ ∀z w g,‖E.eval V (x,z) g-E.eval V (x,w) g‖≤K*dist z w := by
  have hw := C.meanTree_actual_weights (d:=d) hr hσ hψ
  rw [←hAf,←hA] at hw
  have hAf0 : 0≤C.Af := by rw [hAf]; exact C.actualAf_pos.le
  let b := 2*r+|σ/2|
  refine ⟨C.Af*Lf*(depth (C.meanTree (d:=d) r σ):ℝ)*b+b,by dsimp [b]; positivity,?_⟩
  intro z w g
  have hv := C.meanTree_anchorVariation (σ:=σ) hr.le x z w
  have hb : ‖base (C.meanTree r σ) (x,z)-base (C.meanTree r σ) (x,w)‖≤b*dist z w := by
    generalize C.meanTree (d:=d) r σ=E at hv ⊢
    cases E
    exact hv.1
  have he := compileDeclaredRoot_variation hLf hLi (show 0≤b*dist z w by dsimp [b]; positivity)
    hsmall V P M hm hmi (C.meanTree r σ) n (x,z) (x,w) hv hb hw.1 hw.2 hready g
  convert he using 1
  all_goals try with_reducible_and_instances rfl
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

lemma meanTree_eval {F : Point d → ℝ} {lam : ℝ≥0} (hF : Primitive F lam)
    (r σ : ℝ) (x : Point d) (y : Point d × Point d) :
    (C.meanTree r σ).eval F (x,y)=
      centeringMeanCircuit F x r C.T C.h C.ψ (σ/2) C.n C.m C.N C.nc C.Nc C.meanEndpoint
        ((productPointEquiv d d).symm y) := by
  unfold meanTree literalMean
  rw [eval_meanCircuit hF (by linarith [C.T_lower]) C.T_upper C.h_pos]
  simp only [eval_anchor]

theorem meanTree_numerical {F : Point d → ℝ} {lam : ℝ≥0} (hF : Primitive F lam)
    (x : Point d) {r σ err : ℝ} (hr : 0 < r) (hl : (lam:ℝ)*r^2≤1/4)
    (hm : C.m=C.n) (hnc : C.nc=C.n) (hNc : C.Nc=C.N)
    (hcert : CalibratedMeanCircuit (r:=r) (T:=C.T) (h:=C.h) (ψ:=C.ψ) (s:=σ/2)
      hF x hr (by linarith : (lam:ℝ)*r^2≤1/2) (by linarith [C.T_lower]) C.T_upper
      C.h_pos C.n C.N err) :
    ∃w : Point d × Point d → Point d,Measurable w ∧
      ((interpolationLaw F x r C.T).prod (stdGaussian (Point d))).map w=
        (stdGaussian (Point d)).map (fun z => primitiveExpectedField F x r+(σ/2) • z) ∧
      Integrable (fun z => ‖(C.meanTree r σ).eval F (x,z)-w z‖^2)
        ((interpolationLaw F x r C.T).prod (stdGaussian (Point d))) ∧
      (∫z,‖(C.meanTree r σ).eval F (x,z)-w z‖^2
        ∂(interpolationLaw F x r C.T).prod (stdGaussian (Point d)))≤
          ((σ/2)*circuitD F x)^2*err := by
  obtain ⟨X,hsi,hsb,hw,hlaw,hi,hnum⟩ := hcert
  let w₀ := stationaryMeanTarget hF x hr (by linarith : (lam:ℝ)*r^2≤1/2)
    (by linarith [C.T_lower] : 0≤C.T) C.T_upper X
  let w : Point d × Point d → Point d := fun z => w₀ ((productPointEquiv d d).symm z)
  have hw' : Measurable w := hw.comp (productPointEquiv d d).symm.continuous.measurable
  have hjoint := centering_joint_law hF x hr.le (by linarith : (lam:ℝ)*r^2≤1/2)
    (by linarith [C.T_lower]) C.T_upper
  obtain ⟨K,hK⟩ := C.meanTree_anchor_lipschitz hF hr hl x
  have hg : Measurable (fun z => (C.meanTree r σ).eval F (x,z)) := hK.continuous.measurable
  have hid : ∀y : Point (d+d),
      (C.meanTree r σ).eval F (x,productPointEquiv d d y)-w (productPointEquiv d d y)=
      centeringMeanCircuit F x r C.T C.h C.ψ (σ/2) C.n C.n C.N C.n C.N C.meanEndpoint y-w₀ y := by
    intro y
    rw [C.meanTree_eval hF]
    simp only [hm,hnc,hNc,w,ContinuousLinearEquiv.symm_apply_apply]
  refine ⟨w,hw',?_,?_,?_⟩
  · rw [←hjoint,Measure.map_map hw' (productPointEquiv d d).continuous.measurable]
    simpa only [comp_def,w,ContinuousLinearEquiv.symm_apply_apply] using hlaw
  · rw [←hjoint]
    apply (integrable_map_measure (by fun_prop) (productPointEquiv d d).continuous.measurable.aemeasurable).mpr
    simpa only [hid,comp_def,meanEndpoint,w₀] using hi
  · rw [←hjoint,integral_map (productPointEquiv d d).continuous.measurable.aemeasurable (by fun_prop)]
    simpa only [hid,meanEndpoint,w₀] using hnum

lemma meanTree_numerical_noisy {F : Point d → ℝ} {lam : ℝ≥0} (hF : Primitive F lam)
    (x : Point d) {r σ err : ℝ} (hr : 0 < r) (hl : (lam:ℝ)*r^2≤1/4)
    (hm : C.m=C.n) (hnc : C.nc=C.n) (hNc : C.Nc=C.N)
    (hcert : CalibratedMeanCircuit (r:=r) (T:=C.T) (h:=C.h) (ψ:=C.ψ) (s:=σ/2)
      hF x hr (by linarith : (lam:ℝ)*r^2≤1/2) (by linarith [C.T_lower]) C.T_upper
      C.h_pos C.n C.N err) :
    ∃w : Point d × Point d → Point d,Measurable w ∧
      (((interpolationLaw F x r C.T).prod (stdGaussian (Point d))).prod (stdGaussian (Point d))).map
        (fun z => w z.1+(Real.sqrt 3*σ/2) • z.2)=
        (stdGaussian (Point d)).map (fun z => primitiveExpectedField F x r+σ • z) ∧
      Integrable (fun z => ‖(C.meanTree r σ).eval F (x,z)-w z‖^2)
        ((interpolationLaw F x r C.T).prod (stdGaussian (Point d))) ∧
      (∫z,‖(C.meanTree r σ).eval F (x,z)-w z‖^2
        ∂(interpolationLaw F x r C.T).prod (stdGaussian (Point d)))≤
          ((σ/2)*circuitD F x)^2*err := by
  obtain ⟨w,hw,hlaw,hi,hnum⟩ := C.meanTree_numerical hF x hr hl hm hnc hNc hcert
  let := interpolationLaw_probability hF x hr.le (by linarith : (lam:ℝ)*r^2<1) C.T
  refine ⟨w,hw,?_,hi,hnum⟩
  apply law_add_gaussian _ w hw (primitiveExpectedField F x r) (σ/2) (Real.sqrt 3*σ/2) σ _ hlaw
  rw [div_pow,div_pow,mul_pow,Real.sq_sqrt (by norm_num : (0:ℝ)≤3)]
  ring
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

lemma meanTape_preserving (c k : ℕ) :
    MeasurePreserving (meanTape (d:=d) c k)
      ((gaussianTape d c).prod ((stdGaussian (Point d)).prod (gaussianTape d k)))
      (gaussianTape d (c+(1+k))) := by
  exact (MeanTree.appendSlots_preserving (stdGaussian (Point d)) c (1+k)).comp
    ((MeasurePreserving.id _).prod (prependTape_preserving k))

lemma meanParent_run_meanTape (S : SeedProgram d)
    (E : Expression (Point d × (Point d × Point d)) d)
    (u : Fin S.slots → ℝ) (v : Fin E.slots → ℝ) (T : ℝ) (V : Point d → ℝ) (x : Point d)
    (z : (Fin S.slots → Point d) × (Point d × (Fin E.slots → Point d))) :
    (meanParent S E u v T).program.run V (x,meanTape S.slots E.slots z)=
      E.eval V (x,(T • S.program.run V (x,z.1),z.2.1)) z.2.2 := by
  rw [meanParent_run]
  simp only [meanTape,prependTape,MeanTree.leftBlock_append,MeanTree.middleBlock_append,
    MeanTree.rightBlock_append]
end LogConcaveSampling

end

end

section

noncomputable section
namespace LogConcaveSampling
open MeasureTheory ProbabilityTheory OracleCompiler Coupling Function
open scoped Classical NNReal

variable {d : ℕ}

theorem meanParent_squared {F : Point d → ℝ} {lam : ℝ≥0} (hF : Primitive F lam)
    (x : Point d) (S : SeedProgram d)
    (E : Expression (Point d × (Point d × Point d)) d)
    (u : Fin S.slots → ℝ) (v : Fin E.slots → ℝ) (T : ℝ)
    (μ : Measure (Point d)) [IsProbabilityMeasure μ]
    (g w : Point d × Point d → Point d) (m : Point d) (σ n : ℝ)
    (hg : Measurable g) (hw : Measurable w)
    (ρ : Point d × Point d → ℝ) (hρ : ∀z,1≤ρ z)
    (hρlip : ∀z z',ρ z'≤ρ z+dist z z')
    (hρi : Integrable (fun z => (ρ z)^2) (μ.prod (stdGaussian (Point d))))
    {K Lf Lg err B R : ℝ} (hK : 0≤K) (hLf : 0≤Lf) (hLg : 0≤Lg) (herr : 0<err)
    (hS : SquaredAt (gaussianTape d S.slots) μ
      (fun z => T • S.program.run F (x,z)) id B)
    (hposition : ∀y y' G z,‖E.eval F (x,(y,G)) z-E.eval F (x,(y',G)) z‖≤K*‖y-y'‖)
    (hfl : ∀z z' t,‖E.eval F (x,z) t-E.eval F (x,z') t‖≤Lf*dist z z')
    (hgl : ∀z z',‖g z-g z'‖≤Lg*dist z z')
    (hc : ∀z,SquaredAt (gaussianTape d E.slots) (stdGaussian (Point d))
      (E.eval F (x,z)) (fun t => g z+n • t) (err^2*(ρ z)^2))
    (hi : Integrable (fun z => ‖g z-w z‖^2) (μ.prod (stdGaussian (Point d))))
    (hnum : (∫z,‖g z-w z‖^2 ∂μ.prod (stdGaussian (Point d)))≤R)
    (hlaw : ((μ.prod (stdGaussian (Point d))).prod (stdGaussian (Point d))).map
      (fun z => w z.1+n • z.2)=(stdGaussian (Point d)).map (fun t => m+σ • t)) :
    SquaredAt (gaussianTape d (S.slots+(1+E.slots))) (stdGaussian (Point d))
      (fun z => (meanParent S E u v T).program.run F (x,z))
      (fun t => m+σ • t)
      (2*K^2*B+80*err^2*(∫z,(ρ z)^2 ∂μ.prod (stdGaussian (Point d)))+8*R) := by
  have hV : Measurable (fun z => (F z,gradient F z)) :=
    hF.smooth.continuous.measurable.prodMk hF.gradient_lipschitz.continuous.measurable
  have hE := E.measurable_eval F hV
  have hf : Measurable (uncurry (fun z t => E.eval F (x,z) t)) :=
    hE.comp (show Measurable (fun z : (Point d × Point d) × (Fin E.slots → Point d) =>
      ((x,z.1),z.2)) by fun_prop)
  have hsmeas : Measurable (fun z : Fin S.slots → Point d => T • S.program.run F (x,z)) := by
    have hh := (S.program.measurable_run F hV).comp
      (show Measurable (fun z : Fin S.slots → Point d => (x,z)) by fun_prop)
    exact hh.const_smul T
  let H : Point d → Point d × (Fin E.slots → Point d) → Point d :=
    fun y z => E.eval F (x,(y,z.1)) z.2
  have hH : Measurable (uncurry H) :=
    hE.comp (show Measurable (fun z : Point d × (Point d × (Fin E.slots → Point d)) =>
      ((x,(z.1,z.2.1)),z.2.2)) by fun_prop)
  have hs := hS.shared_lipschitz ((stdGaussian (Point d)).prod (gaussianTape d E.slots))
    hsmeas measurable_id hK H hH (fun a b z => hposition a b z.1 z.2)
  have hn := SquaredAt.noisy_circuit_target (μ.prod (stdGaussian (Point d)))
    (gaussianTape d E.slots) (stdGaussian (Point d)) (fun z t => E.eval F (x,z) t)
    g w (fun t => m+σ • t) hf hg hw (by fun_prop) ρ hρ hρlip hρi hLf hLg herr
    hfl hgl hc hi hnum hlaw
  have hn' := hn.reindex (MeasurableEquiv.prodAssoc (α := Point d) (β := Point d) (γ := Fin E.slots → Point d)) id
    (by fun_prop) measurable_id (uncurry H) (fun t => m+σ • t) hH (by fun_prop)
    (fun _ => rfl) (fun _ => rfl)
  rw [(measurePreserving_prodAssoc μ (stdGaussian (Point d)) (gaussianTape d E.slots)).map_eq,
    Measure.map_id] at hn'
  have hs' : Measurable (fun z : (Fin S.slots → Point d) × (Point d × (Fin E.slots → Point d)) => H (T • S.program.run F (x,z.1)) z.2) :=
    hH.comp ((hsmeas.comp measurable_fst).prodMk measurable_snd)
  have hh := hs.trans hs' (hE.comp (show Measurable (fun z : Point d × (Point d × (Fin E.slots → Point d)) => ((x,(z.1,z.2.1)),z.2.2)) by fun_prop)) (by fun_prop) hn'
  have hp := hh.reindex (meanTape S.slots E.slots) id
    (meanTape_preserving S.slots E.slots).measurable measurable_id
    (fun z => (meanParent S E u v T).program.run F (x,z)) (fun t => m+σ • t)
    (((meanParent S E u v T).program.measurable_run F hV).comp (by fun_prop))
    (by fun_prop) (fun z => meanParent_run_meanTape S E u v T F x z) (fun _ => rfl)
  simp only [(meanTape_preserving S.slots E.slots).map_eq,Measure.map_id] at hp
  convert hp using 1
  all_goals try with_reducible_and_instances rfl
  ring
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
namespace LogConcaveSampling.OracleCompiler.ReservedProgram
open MeasureTheory ProbabilityTheory Function Coupling
open scoped Classical NNReal

variable {d : ℕ}

lemma fullTape_preserving (k : ℕ) :
    MeasurePreserving (fullTape (d:=d) k) ((gaussianTape d k).prod (stdGaussian (Point d)))
      (gaussianTape d (k+1)) := by
  exact (MeanTree.appendSlots_preserving (stdGaussian (Point d)) k 1).comp
    ((MeasurePreserving.id _).prod (oneSlot_preserving (stdGaussian (Point d))))

lemma anchor_squared {F : Point d → ℝ} {lam : ℝ≥0} (hF : Primitive F lam)
    (x : Point d) (S : ReservedProgram d) {r T η B : ℝ}
    (hr : 0 ≤ r) (hl : (lam:ℝ)*r^2<1) (hT : 0≤T)
    (hη : T*η=Real.sqrt (1-T^2)) (hreserve : S.reserve=η/2)
    (hpre : SquaredAt (gaussianTape d S.slots)
      ((gibbs (primitivePotential F x r)).prod (stdGaussian (Point d)))
      (fun g => S.pre.run F (x,g)) (fun z => z.1+(Real.sqrt 3*η/2) • z.2) B) :
    SquaredAt (gaussianTape d S.full.slots) (interpolationLaw F x r T)
      (fun g => T • S.full.program.run F (x,g)) id (T^2*B) := by
  let := probability_gibbs_of_partition
    (partition_pos_of_continuous (hF.continuous_potential x r)).ne'
    (partition_ne_top_of_integrable (hF.integrable_exp_neg_potential x hr hl))
  have hV : Measurable (fun z => (F z,gradient F z)) :=
    hF.smooth.continuous.measurable.prodMk hF.gradient_lipschitz.continuous.measurable
  have hf : Measurable (fun g => S.pre.run F (x,g)) :=
    (S.pre.measurable_run F hV).comp (by fun_prop)
  have hfull : Measurable (fun g => T • S.full.program.run F (x,g)) := by
    have hh := (S.full.program.measurable_run F hV).comp (show Measurable (fun z : Fin S.full.slots → Point d => (x,z)) by fun_prop)
    fun_prop
  let H : Point d → Point d → Point d := fun a g => T • (a+S.reserve • g)
  have hh := hpre.shared_lipschitz (stdGaussian (Point d)) hf (by fun_prop) hT H (by fun_prop)
    (fun a b g => by simp only [H,←smul_sub,add_sub_add_right_eq_sub,norm_smul,Real.norm_eq_abs,abs_of_nonneg hT]; exact le_rfl)
  have hnoise := smoothing_add_gaussian
    ((gibbs (primitivePotential F x r)).prod (stdGaussian (Point d))) (gibbs (primitivePotential F x r))
    (fun z => z.1+(Real.sqrt 3*η/2) • z.2) id (by fun_prop) measurable_id
    (Real.sqrt 3*η/2) (η/2) η (by
      rw [div_pow,mul_pow,Real.sq_sqrt (by norm_num : (0:ℝ)≤3),div_pow]; ring) rfl
  have hnoise' := congrArg (Measure.map (fun z : Point d => T • z)) hnoise
  rw [Measure.map_map (by fun_prop) (by fun_prop),Measure.map_map (by fun_prop) (by fun_prop)] at hnoise'
  have hlaw : (((gibbs (primitivePotential F x r)).prod (stdGaussian (Point d))).prod (stdGaussian (Point d))).map
      (fun z => H (z.1.1+(Real.sqrt 3*η/2) • z.1.2) z.2)=interpolationLaw F x r T := by
    convert hnoise' using 1
    · simp only [H,hreserve,comp_def]
    · simp only [comp_def,smul_add,smul_smul,hη,interpolationLaw,id_eq]
  have hp := hh.reindex (fullTape S.slots)
    (fun z => H (z.1.1+(Real.sqrt 3*η/2) • z.1.2) z.2)
    (fullTape_preserving S.slots).measurable (by fun_prop)
    (fun g : Fin (S.slots+1) → Point d => T • S.full.program.run F (x,g)) id hfull measurable_id
    (fun z => by rw [full_run]; simp only [fullTape,Fin.append_left,Fin.append_right,H])
    (fun _ => rfl)
  rw [(fullTape_preserving S.slots).map_eq,hlaw] at hp
  exact hp
end LogConcaveSampling.OracleCompiler.ReservedProgram

end

end

section

noncomputable section
namespace LogConcaveSampling.OracleCompiler.CircuitParameters
open MeasureTheory ProbabilityTheory MeanTree Coupling Function
open scoped Classical NNReal

variable (C : CircuitParameters) {d : ℕ}

theorem meanFrom_squared {F : Point d → ℝ} {lam : ℝ≥0} (hF : Primitive F lam)
    {q Kf Ki Ks ef ei es ηmin r σ en : ℝ} (hd : 1 ≤ d)
    (hs : MeanSize lam q r σ) (hl : q ≤ 1/4) (hL : (lam:ℝ)*r ≤ 1)
    (hD : 1 ≤ C.D) (hψ : 0 ≤ C.ψ) (hA : C.A=C.actualA) (hAf : C.Af=C.actualAf)
    (hKf : 0 ≤ Kf) (hKi : 0 ≤ Ki) (hef : 0 < ef) (hei : 0 ≤ ei)
    (hsmall : (lam:ℝ)*C.meanCenterBudget r σ*(2*Real.pi+2) ≤ 1)
    (hcon : 4*(C.meanCenterBudget r σ)^2*((lam:ℝ)*Ki)^2 ≤ 1)
    (hRT : Real.sqrt (1-C.T^2) ≤ C.T) (hη : ηmin ≤ Real.sqrt (1-C.T^2)/C.T)
    (hm : C.m=C.n) (hnc : C.nc=C.n) (hNc : C.Nc=C.N)
    (Mf Mi : ℝ → ℝ → SeedProgram d) (S : ℝ → ℝ → ReservedProgram d)
    (B : ℕ) (hBD : (B:ℝ) ≤ C.D^2)
    (hbudget : ∀(s : Bool) r τ,MeanBudget B r ((if s then Mf else Mi) r τ))
    (hf : MeanCorrect F lam ((1+4*C.Af)*Real.sqrt (1-C.T^2)*q) Kf ef Mf)
    (hi : MeanCorrect F lam (q*(1+16*C.D*C.A/Real.sqrt (1-C.T^2))) Ki ei Mi)
    (hS : SampleCorrect F lam (q/Real.sqrt (1-C.T^2)) Ks es ηmin S)
    (hrsv : (S r (Real.sqrt (1-C.T^2)/C.T)).reserve=(Real.sqrt (1-C.T^2)/C.T)/2)
    (x : Point d)
    (hcert : CalibratedMeanCircuit (r:=r) (T:=C.T) (h:=C.h) (ψ:=C.ψ) (s:=σ/2)
      hF x hs.1 (by linarith [hs.2.2.2.1] : (lam:ℝ)*r^2 ≤ 1/2)
      (by linarith [C.T_lower]) C.T_upper C.h_pos C.n C.N (en^2)) :
    let dep := (depth (C.meanTree (d:=d) r σ):ℝ)
    let a := 2*(1+2*dep)*(C.Af*Kf*q*ei+ef)
    SquaredAt (gaussianTape d (C.meanFrom Mf Mi S r σ).slots) (stdGaussian (Point d))
      (fun g => (C.meanFrom Mf Mi S r σ).program.run F (x,g))
      (fun g => primitiveExpectedField F x r+σ • g)
      (2*(C.Af*((lam:ℝ)*Kf)*dep*r)^2*(C.T^2*(es^2*(circuitD F x)^2))+
        80*(σ*a)^2*((20+16*circuitGrowthConstant^2)*(circuitD F x)^2)+
        8*((σ/2)*circuitD F x)^2*en^2) := by
  let dep := (depth (C.meanTree (d:=d) r σ):ℝ)
  let a := 2*(1+2*dep)*(C.Af*Kf*q*ei+ef)
  let P : Bool → ℝ → ℝ → Prop := fun s => if s then
    MeanSize lam ((1+4*C.Af)*Real.sqrt (1-C.T^2)*q) else
    MeanSize lam (q*(1+16*C.D*C.A/Real.sqrt (1-C.T^2)))
  let M : Bool → ℝ → ℝ → SeedProgram d := fun s => if s then Mf else Mi
  let E := compileDeclaredRoot C.D (C.meanCenterBudget r σ) C.Af Mf Mi
    (C.meanTree (d:=d) r σ) (Real.sqrt 3*σ/2)
  have hA0 : 0 < C.A := hA ▸ C.actualA_pos
  have hAf0 : 0 < C.Af := hAf ▸ C.actualAf_pos
  have hbud : 0 ≤ C.meanCenterBudget r σ := by unfold meanCenterBudget; positivity [hs.1,hs.2.2.1]
  have hLip : (lam:ℝ)*Ki*C.meanCenterBudget r σ ≤ 1 := by
    have hn : 0 ≤ (lam:ℝ)*Ki*C.meanCenterBudget r σ := by positivity
    nlinarith [sq_nonneg ((lam:ℝ)*Ki*C.meanCenterBudget r σ)]
  have hrad : (lam:ℝ)*r^2 ≤ 1/4 := hs.2.2.2.1.trans hl
  have hT : 0 ≤ C.T := by linarith [C.T_lower]
  have ha : 0 < a := by dsimp [a,dep]; positivity [hs.nonneg lam.coe_nonneg]
  have hv := C.meanTree_valid (d:=d) lam.coe_nonneg hs (by linarith) hψ hA hAf
  have hrdy := hv.shiftReady (P true) (P false) (fun _ _ h => h.1.ne')
    (fun _ _ h => h.1.ne') _ _
  have hpos := C.meanCompiled_variation hs.1 hs.2.2.1 hψ hA hAf
    (mul_nonneg lam.coe_nonneg hKf) (mul_nonneg lam.coe_nonneg hKi) hLip F P M hf.lip hi.lip
    (Real.sqrt 3*σ/2) hrdy
  obtain ⟨Lf,hLf,hfl⟩ := C.meanCompiled_anchor_lipschitz hs.1 hs.2.2.1 hψ hA hAf
    (mul_nonneg lam.coe_nonneg hKf) (mul_nonneg lam.coe_nonneg hKi) hLip F P M hf.lip hi.lip
    (Real.sqrt 3*σ/2) hrdy x
  obtain ⟨Lg,hgl⟩ := C.meanTree_anchor_lipschitz (σ:=σ) hF hs.1 hrad x
  have hc (z : Point d × Point d) := C.meanCompiled_scaled hF hs (by linarith) hL hD hψ hA hAf hKf hKi hef.le hei
    hsmall hcon Mf Mi B hBD hbudget hf hi x z.1 z.2
  have hanc := C.mean_anchor_size lam.coe_nonneg hs hRT
  have he := hS.error _ _ hanc hη x
  have hanc' := ReservedProgram.anchor_squared hF x _ hs.1.le (by linarith : (lam:ℝ)*r^2 < 1) hT
    (show C.T*(Real.sqrt (1-C.T^2)/C.T)=Real.sqrt (1-C.T^2) by field_simp [ne_of_gt (by linarith [C.T_lower] : 0<C.T)]) hrsv he
  let := interpolationLaw_probability hF x hs.1.le (by linarith : (lam:ℝ)*r^2 < 1) C.T
  obtain ⟨w,hw,hlaw,hwi,hnum⟩ := C.meanTree_numerical_noisy hF x hs.1 hrad hm hnc hNc hcert
  have hmoment := pairGauge_interpolation_moment hF x hs.1.le hs.2.1
    (by linarith : (lam:ℝ)*r^2 ≤ 1/2) hT C.T_upper hd
  let v := compileDeclaredRootShift C.D (C.meanCenterBudget r σ) C.Af Mf Mi
    (C.meanTree (d:=d) r σ) (Real.sqrt 3*σ/2) (C.meanDrift r σ hs.1)
  let anc := S r (Real.sqrt (1-C.T^2)/C.T)
  have hp := meanParent_squared hF x anc.full E (anc.extraShift (-2*Real.sqrt (1-C.T^2)/C.T)) v C.T
    (interpolationLaw F x r C.T) (fun z => (C.meanTree r σ).eval F (x,z)) w
    (primitiveExpectedField F x r) σ (Real.sqrt 3*σ/2) hgl.continuous.measurable hw
    (pairGauge (circuitD F x)) (one_le_pairGauge (circuitD_nonneg F x))
    (pairGauge_change _) hmoment.1
    (show 0 ≤ C.Af*((lam:ℝ)*Kf)*dep*r by positivity [hs.1]) hLf Lg.coe_nonneg
    (mul_pos hs.2.2.1 ha) hanc' (hpos.2 x) hfl
    (fun z z' => by simpa only [dist_eq_norm] using hgl.dist_le_mul z z')
    hc hwi hnum hlaw
  unfold meanFrom
  rw [dite_eq_left hs.1]
  apply hp.mono
  have hh := mul_le_mul_of_nonneg_left hmoment.2 (show 0 ≤ 80*(σ*a)^2 by positivity)
  calc
    _ ≤ 2*(C.Af*((lam:ℝ)*Kf)*dep*r)^2*(C.T^2*(es^2*(circuitD F x)^2))+
      80*(σ*a)^2*((20+16*circuitGrowthConstant^2)*(circuitD F x)^2)+
      8*((σ/2*circuitD F x)^2*en^2) := add_le_add (add_le_add le_rfl hh) le_rfl
    _ = _ := by ring
end LogConcaveSampling.OracleCompiler.CircuitParameters

end

end

section

noncomputable section
namespace LogConcaveSampling.OracleCompiler.CircuitParameters
open MeanTree

variable (C : CircuitParameters) {d : ℕ}

lemma meanTree_depth (hN : C.Nc≤C.N) (r σ : ℝ) :
    depth (C.meanTree (d:=d) r σ)≤C.depthBound := by
  exact meanCircuit_fixed_depth r C.T C.h C.ψ (σ/2) C.n C.m C.N C.nc C.Nc hN C.meanEndpoint _ _ _ _ _ _

end LogConcaveSampling.OracleCompiler.CircuitParameters

end

end

section

noncomputable section
namespace LogConcaveSampling.OracleCompiler
open MeasureTheory MeanTree
open scoped Classical NNReal

variable {d : ℕ}

lemma ReservedProgram.full_fixedSeed_lip (S : ReservedProgram d) (F : Point d → ℝ) (K : ℝ)
    (h : ∀x y g, ‖S.pre.run F (x,g)-S.pre.run F (y,g)‖≤K*‖x-y‖) :
    ∀x y g, ‖S.full.program.run F (x,g)-S.full.program.run F (y,g)‖≤K*‖x-y‖ := by
  intro x y g
  rw [full_run S F x g,full_run S F y g,add_sub_add_right_eq_sub]
  exact h x y _

namespace CircuitParameters
variable (C : CircuitParameters)

lemma meanFrom_lipschitz {F : Point d → ℝ} {lam : ℝ≥0}
    {q Kf Ki Ks ef ei es ηmin r σ : ℝ}
    (hs : MeanSize lam q r σ) (hD : 0<C.D) (hψ : 0≤C.ψ)
    (hA : C.A=C.actualA) (hAf : C.Af=C.actualAf)
    (hKf : 0≤Kf) (hKi : 0≤Ki) (hKs : 0≤Ks)
    (hsmall : (lam:ℝ)*Ki*C.meanCenterBudget r σ≤1)
    (hRT : Real.sqrt (1-C.T^2)≤C.T)
    (hη : ηmin≤Real.sqrt (1-C.T^2)/C.T)
    (Mf Mi : ℝ → ℝ → SeedProgram d) (S : ℝ → ℝ → ReservedProgram d)
    (hf : MeanCorrect F lam ((1+4*C.Af)*Real.sqrt (1-C.T^2)*q) Kf ef Mf)
    (hi : MeanCorrect F lam (q*(1+16*C.D*C.A/Real.sqrt (1-C.T^2))) Ki ei Mi)
    (hS : SampleCorrect F lam (q/Real.sqrt (1-C.T^2)) Ks es ηmin S) :
    ∀x y g, ‖(C.meanFrom Mf Mi S r σ).program.run F (x,g)-
      (C.meanFrom Mf Mi S r σ).program.run F (y,g)‖≤
      (lam:ℝ)*(C.Af*(depth (C.meanTree (d:=d) r σ):ℝ)*Kf*(1+q*Ks))*‖x-y‖ := by
  let P : Bool → ℝ → ℝ → Prop := fun s => if s then
    MeanSize lam ((1+4*C.Af)*Real.sqrt (1-C.T^2)*q) else
    MeanSize lam (q*(1+16*C.D*C.A/Real.sqrt (1-C.T^2)))
  let M : Bool → ℝ → ℝ → SeedProgram d := fun s => if s then Mf else Mi
  have hv := C.meanTree_valid (d:=d) lam.coe_nonneg hs hD hψ hA hAf
  have hrdy := hv.shiftReady (P true) (P false) (fun _ _ h => h.1.ne')
    (fun _ _ h => h.1.ne') _ _
  have hE := C.meanCompiled_variation hs.1 hs.2.2.1 hψ hA hAf
    (mul_nonneg lam.coe_nonneg hKf) (mul_nonneg lam.coe_nonneg hKi) hsmall F P M hf.lip hi.lip
    (Real.sqrt 3*σ/2) hrdy
  have ha := C.mean_anchor_size lam.coe_nonneg hs hRT
  have hSl := ReservedProgram.full_fixedSeed_lip _ F ((lam:ℝ)*r*Ks) (hS.lip _ _ ha hη)
  have hAf0 : 0<C.Af := hAf ▸ C.actualAf_pos
  have hT : 0≤C.T := by linarith [C.T_lower]
  have hK : 0≤C.Af*((lam:ℝ)*Kf)*(depth (C.meanTree (d:=d) r σ):ℝ) := by positivity
  unfold meanFrom
  rw [dite_eq_left hs.1]
  dsimp only
  intro x y g
  have he := meanParent_lipschitz F _ _ _ _ _ _ _ _ (mul_nonneg hK hs.1.le) hT hSl hE.1 hE.2 x y g
  apply he.trans
  have hq := mul_le_mul_of_nonneg_right hs.2.2.2.1 hKs
  have hTq : C.T*((lam:ℝ)*r^2*Ks)≤q*Ks :=
    (mul_le_of_le_one_left (show 0≤(lam:ℝ)*r^2*Ks by positivity) C.T_upper.le).trans hq
  have hh := mul_le_mul_of_nonneg_left hTq hK
  have heq : C.Af*((lam:ℝ)*Kf)*(depth (C.meanTree (d:=d) r σ):ℝ)+
      C.Af*((lam:ℝ)*Kf)*(depth (C.meanTree (d:=d) r σ):ℝ)*r*C.T*((lam:ℝ)*r*Ks)≤
      (lam:ℝ)*(C.Af*(depth (C.meanTree (d:=d) r σ):ℝ)*Kf*(1+q*Ks)) := by nlinarith
  exact mul_le_mul_of_nonneg_right heq (norm_nonneg _)

end CircuitParameters
end LogConcaveSampling.OracleCompiler

end

end

section

noncomputable section
namespace LogConcaveSampling.OracleCompiler
open MeanTree Coupling
open scoped Classical NNReal

lemma mean_error_envelope {u k σ T es a en D M : ℝ}
    (hu : 0≤u) (hk : 0≤k) (_hσ : 0≤σ) (hT : 0≤T) (hT1 : T≤1)
    (hes : 0≤es) (ha : 0≤a) (hen : 0≤en) (hM : 1≤M) (hub : u≤σ*k) :
    2*u^2*(T^2*(es^2*D^2))+80*(σ*a)^2*(M*D^2)+8*(σ/2*D)^2*en^2≤
      σ^2*(2*k*es+10*M*a+2*en)^2*D^2 := by
  have hut : u*T≤σ*k := (mul_le_of_le_one_right hu hT1).trans hub
  have hv := pow_le_pow_left₀ (mul_nonneg hu hT) hut 2
  have hv' := mul_le_mul_of_nonneg_right hv (show 0≤2*es^2 by positivity)
  have hm : 80*M≤100*M^2 := by nlinarith
  have hm' := mul_le_mul_of_nonneg_right hm (sq_nonneg (σ*a))
  have h₁ : 0≤(2*k*es)*(10*M*a) := by positivity
  have h₂ : 0≤(2*k*es)*(2*en) := by positivity
  have h₃ : 0≤(10*M*a)*(2*en) := by positivity
  have hsum : 2*u^2*T^2*es^2+80*(σ*a)^2*M+2*σ^2*en^2≤
      σ^2*(2*k*es+10*M*a+2*en)^2 := by
    have hx := mul_nonneg (sq_nonneg σ) h₁
    have hy := mul_nonneg (sq_nonneg σ) h₂
    have hz := mul_nonneg (sq_nonneg σ) h₃
    nlinarith [sq_nonneg (σ*k*es),sq_nonneg (σ*en)]
  have hres := mul_le_mul_of_nonneg_right hsum (sq_nonneg D)
  nlinarith only [hres]

namespace CircuitParameters
variable (C : CircuitParameters) {d : ℕ}

lemma physical_mean_factor {lam q Kf r σ H : ℝ}
    (hs : MeanSize lam q r σ) (hlam : 0≤lam) (hAf : 0≤C.Af) (hK : 0≤Kf)
    (hH : (depth (C.meanTree (d:=d) r σ):ℝ)≤H) :
    C.Af*(lam*Kf)*(depth (C.meanTree (d:=d) r σ):ℝ)*r≤σ*(C.Af*Kf*H*q) := by
  have hq := hs.nonneg hlam
  have h₁ := mul_le_mul_of_nonneg_left hs.2.2.2.2
    (show 0≤C.Af*Kf*(depth (C.meanTree (d:=d) r σ):ℝ) by positivity)
  have h₂ := mul_le_mul_of_nonneg_left hH (show 0≤σ*C.Af*Kf*q by positivity [hs.2.2.1])
  nlinarith

end CircuitParameters
end LogConcaveSampling.OracleCompiler

end

end

section

noncomputable section
namespace LogConcaveSampling.OracleCompiler
open MeanTree Coupling MeasureTheory ProbabilityTheory
open scoped Classical NNReal

variable {d : ℕ}

namespace CircuitParameters
variable (C : CircuitParameters)

lemma meanCenter_scaled {lam q r σ : ℝ} (hs : MeanSize lam q r σ)
    (_hlam : 0≤lam) (hA : 0≤C.A) : lam*C.meanCenterBudget r σ≤2*C.A*q := by
  have hh : lam*r/σ≤q := (div_le_iff₀ hs.2.2.1).mpr hs.2.2.2.2
  have he : lam*(r/σ+r^2)≤2*q := by rw [mul_add,←mul_div_assoc]; linarith [hs.2.2.2.1]
  have hh := mul_le_mul_of_nonneg_left he hA
  unfold meanCenterBudget
  nlinarith only [hh]

lemma physical_small_of_scaled {lam B A q K : ℝ} (_hA : 0≤A) (_hq : 0≤q) (hK : 0≤K)
    (hB : 0≤lam*B) (hscale : lam*B≤2*A*q)
    (hp : 2*A*q*(2*Real.pi+2)≤1) (hcon : 4*A*q*K≤1) :
    lam*B*(2*Real.pi+2)≤1 ∧ 4*B^2*(lam*K)^2≤1 ∧ lam*K*B≤1 := by
  have hs := mul_le_mul_of_nonneg_right hscale (show 0≤2*Real.pi+2 by positivity [Real.pi_pos])
  have hk := mul_le_mul_of_nonneg_right hscale hK
  have hg : 0≤lam*B*K := mul_nonneg hB hK
  have hu : lam*B*K≤1/2 := by linarith
  refine ⟨hs.trans hp,?_,by nlinarith⟩
  have hh := pow_le_pow_left₀ hg hu 2
  nlinarith only [hh]

lemma compilerError_mono {H H' Kf q ei ef : ℝ} (hHH : H≤H')
    (hAf : 0≤C.Af) (hK : 0≤Kf) (hq : 0≤q) (hei : 0≤ei) (hef : 0≤ef) :
    C.compilerError H Kf q ei ef≤C.compilerError H' Kf q ei ef := by
  unfold compilerError
  nlinarith [mul_nonneg (sub_nonneg.mpr hHH) (show 0≤C.Af*Kf*q*ei+ef by positivity)]

end CircuitParameters
end LogConcaveSampling.OracleCompiler

end

end

section

noncomputable section
namespace LogConcaveSampling.OracleCompiler.CircuitParameters
open MeanTree Coupling MeasureTheory ProbabilityTheory
open scoped Classical NNReal

variable (C : CircuitParameters) {d : ℕ}

theorem meanFrom_correct_oai {F : Point d → ℝ} {lam : ℝ≥0} (hF : Primitive F lam)
    {q Kf Ki Ks ef ei es en ηmin : ℝ} (hd : 1≤d) (hlam : (lam:ℝ)≤1)
    (hq : 0≤q) (hql : q≤1/4) (hRT : Real.sqrt (1-C.T^2)≤C.T)
    (hη : ηmin≤Real.sqrt (1-C.T^2)/C.T)
    (hD : 1≤C.D) (hψ : 0≤C.ψ) (hA : C.A=C.actualA) (hAf : C.Af=C.actualAf)
    (hKf : 0≤Kf) (hKi : 0≤Ki) (hKs : 0≤Ks)
    (hef : 0<ef) (hei : 0≤ei) (hes : 0≤es) (hen : 0≤en)
    (hsmall : 2*C.A*q*(2*Real.pi+2)≤1) (hcon : 4*C.A*q*Ki≤1) (hqs : q*Ks≤1)
    (hm : C.m=C.n) (hnc : C.nc=C.n) (hNc : C.Nc=C.N)
    (Mf Mi : ℝ → ℝ → SeedProgram d) (S : ℝ → ℝ → ReservedProgram d)
    (B : ℕ) (hBD : (B:ℝ)≤C.D^2)
    (hbudget : ∀(s : Bool) r τ,MeanBudget B r ((if s then Mf else Mi) r τ))
    (hf : MeanCorrect F lam ((1+4*C.Af)*Real.sqrt (1-C.T^2)*q) Kf ef Mf)
    (hi : MeanCorrect F lam (q*(1+16*C.D*C.A/Real.sqrt (1-C.T^2))) Ki ei Mi)
    (hS : SampleCorrect F lam (q/Real.sqrt (1-C.T^2)) Ks es ηmin S)
    (hrsv : ∀r,(S r (Real.sqrt (1-C.T^2)/C.T)).reserve=(Real.sqrt (1-C.T^2)/C.T)/2)
    (hnum : C.MeanNumericalReady hF q en hql) :
    MeanCorrect F lam q (2*C.Af*C.depthBound*Kf)
      (C.meanError C.depthBound Kf q es ei ef en) (C.meanFrom Mf Mi S) := by
  have hA0 : 0<C.A := hA ▸ C.actualA_pos
  have hAf0 : 0<C.Af := hAf ▸ C.actualAf_pos
  have hH : 0≤(C.depthBound:ℝ) := Nat.cast_nonneg _
  have small {r σ : ℝ} (hs : MeanSize lam q r σ) :=
    physical_small_of_scaled hA0.le hq hKi
      (show 0≤(lam:ℝ)*C.meanCenterBudget r σ by unfold meanCenterBudget; positivity [hs.1,hs.2.2.1])
      (C.meanCenter_scaled hs lam.coe_nonneg hA0.le) hsmall hcon
  constructor
  · intro r σ hs x y g
    have he := C.meanFrom_lipschitz hs (by linarith) hψ hA hAf hKf hKi hKs
      (small hs).2.2 hRT hη Mf Mi S hf hi hS x y g
    have hdep : (depth (C.meanTree (d:=d) r σ):ℝ)≤C.depthBound :=
      by exact_mod_cast C.meanTree_depth (d:=d) hNc.le r σ
    have hdep0 : 0≤(depth (C.meanTree (d:=d) r σ):ℝ) := Nat.cast_nonneg _
    have hh : (depth (C.meanTree (d:=d) r σ):ℝ)*(1+q*Ks)≤2*C.depthBound := by
      have ht := mul_le_mul_of_nonneg_left hqs hdep0
      nlinarith
    have hk := mul_le_mul_of_nonneg_right hh
      (show 0≤(lam:ℝ)*C.Af*Kf*‖x-y‖ by positivity)
    apply he.trans
    nlinarith only [hk]
  · intro r σ hs x
    have hL : (lam:ℝ)*r≤1 := (mul_le_of_le_one_left hs.1.le hlam).trans hs.2.1
    have hp := C.meanFrom_squared hF hd hs hql hL hD hψ hA hAf hKf hKi hef hei
      (small hs).1 (small hs).2.1 hRT hη hm hnc hNc Mf Mi S B hBD hbudget hf hi hS
      (hrsv r) x (hnum x r σ hs)
    apply hp.mono
    let dep := (depth (C.meanTree (d:=d) r σ):ℝ)
    let a := C.compilerError dep Kf q ei ef
    let k := C.Af*Kf*C.depthBound*q
    have hdep : dep≤C.depthBound := by dsimp only [dep]; exact_mod_cast C.meanTree_depth (d:=d) hNc.le r σ
    have hdep0 : 0≤dep := by dsimp [dep]; positivity
    have ha : 0≤a := by dsimp [a,compilerError]; positivity
    have ha' : a≤C.compilerError C.depthBound Kf q ei ef := C.compilerError_mono hdep hAf0.le hKf hq hei hef.le
    have hu := C.physical_mean_factor hs lam.coe_nonneg hAf0.le hKf hdep
    have he := mean_error_envelope (D:=circuitD F x)
      (show 0≤C.Af*((lam:ℝ)*Kf)*dep*r by positivity [hs.1])
      (show 0≤k by dsimp [k]; positivity) hs.2.2.1.le
      (by linarith [C.T_lower] : 0≤C.T) C.T_upper.le hes ha hen
      (show 1≤20+16*circuitGrowthConstant^2 by nlinarith [sq_nonneg circuitGrowthConstant]) hu
    apply he.trans
    have hem : 2*k*es+10*(20+16*circuitGrowthConstant^2)*a+2*en≤
        C.meanError C.depthBound Kf q es ei ef en := by
      unfold meanError
      have hh := mul_le_mul_of_nonneg_left ha' (show 0≤10*(20+16*circuitGrowthConstant^2) by positivity)
      exact add_le_add (add_le_add le_rfl hh) le_rfl
    have he0 : 0≤2*k*es+10*(20+16*circuitGrowthConstant^2)*a+2*en := by dsimp [k]; positivity
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ he0 hem 2) (sq_nonneg σ)) (sq_nonneg _)
end LogConcaveSampling.OracleCompiler.CircuitParameters

end

end

end OAI
end

theorem solution : type_of% @OAI.LogConcaveSampling.OracleCompiler.CircuitParameters.meanFrom_correct_oai := @OAI.LogConcaveSampling.OracleCompiler.CircuitParameters.meanFrom_correct_oai
