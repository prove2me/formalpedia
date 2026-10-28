-- Prove2me | solution 1 for OAI.LogConcaveSampling.OracleCompiler.uniform_routine_accuracy
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-27T13:37:59.185686+00:00
-- url     : https://prove2.me/submissions/b1763c4e-ee8c-4355-8d9a-6744e1ebfb07

import Mathlib
import Definitions.Def_LogConcaveQuery
import Definitions.Def_OAIQ048L002
import Definitions.Def_OAIQ048L003
import Theorems.Thm_OAI_LogConcaveSampling_OracleCompiler_CircuitParameters_meanFrom_correct
import Theorems.Thm_OAI_LogConcaveSampling_OracleCompiler_CircuitParameters_sampleFrom_squared

section
-- module Solutions.OAIQ048_LC.LogConcave_Dynamics_TriangularEquiv
attribute [-instance] _root_.OAI.LogConcaveSampling.LowerBound.couplingLaw_probability _root_.OAI.LogConcaveSampling.LowerBound.remainingHaar_probability _root_.OAI.LogConcaveSampling.LowerBound.roundRandomLaw_probability _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_invInvariant _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_isHaar _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_probability _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_rightInvariant _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_compactSpace _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_measurableInv _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_measurableMul _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_secondCountable _root_.OAI.LogConcaveSampling.MeanTree.instIsProbabilityMeasureRowTapeRowLaw _root_.OAI.LogConcaveSampling.OracleCompiler.topSeedLaw_probability
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
attribute [-instance] _root_.OAI.LogConcaveSampling.LowerBound.couplingLaw_probability _root_.OAI.LogConcaveSampling.LowerBound.remainingHaar_probability _root_.OAI.LogConcaveSampling.LowerBound.roundRandomLaw_probability _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_invInvariant _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_isHaar _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_probability _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_rightInvariant _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_compactSpace _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_measurableInv _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_measurableMul _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_secondCountable _root_.OAI.LogConcaveSampling.MeanTree.instIsProbabilityMeasureRowTapeRowLaw _root_.OAI.LogConcaveSampling.OracleCompiler.topSeedLaw_probability
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
attribute [-instance] _root_.OAI.LogConcaveSampling.LowerBound.couplingLaw_probability _root_.OAI.LogConcaveSampling.LowerBound.remainingHaar_probability _root_.OAI.LogConcaveSampling.LowerBound.roundRandomLaw_probability _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_invInvariant _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_isHaar _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_probability _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_rightInvariant _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_compactSpace _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_measurableInv _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_measurableMul _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_secondCountable _root_.OAI.LogConcaveSampling.MeanTree.instIsProbabilityMeasureRowTapeRowLaw _root_.OAI.LogConcaveSampling.OracleCompiler.topSeedLaw_probability
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
attribute [-instance] _root_.OAI.LogConcaveSampling.LowerBound.couplingLaw_probability _root_.OAI.LogConcaveSampling.LowerBound.remainingHaar_probability _root_.OAI.LogConcaveSampling.LowerBound.roundRandomLaw_probability _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_invInvariant _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_isHaar _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_probability _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_rightInvariant _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_compactSpace _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_measurableInv _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_measurableMul _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_secondCountable _root_.OAI.LogConcaveSampling.MeanTree.instIsProbabilityMeasureRowTapeRowLaw _root_.OAI.LogConcaveSampling.OracleCompiler.topSeedLaw_probability
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
attribute [-instance] _root_.OAI.LogConcaveSampling.LowerBound.couplingLaw_probability _root_.OAI.LogConcaveSampling.LowerBound.remainingHaar_probability _root_.OAI.LogConcaveSampling.LowerBound.roundRandomLaw_probability _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_invInvariant _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_isHaar _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_probability _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_rightInvariant _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_compactSpace _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_measurableInv _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_measurableMul _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_secondCountable _root_.OAI.LogConcaveSampling.MeanTree.instIsProbabilityMeasureRowTapeRowLaw _root_.OAI.LogConcaveSampling.OracleCompiler.topSeedLaw_probability
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
-- module Solutions.OAIQ048_LC.LogConcave_Sampling_ClosedFieldMean
attribute [-instance] _root_.OAI.LogConcaveSampling.LowerBound.couplingLaw_probability _root_.OAI.LogConcaveSampling.LowerBound.remainingHaar_probability _root_.OAI.LogConcaveSampling.LowerBound.roundRandomLaw_probability _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_invInvariant _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_isHaar _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_probability _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_rightInvariant _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_compactSpace _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_measurableInv _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_measurableMul _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_secondCountable _root_.OAI.LogConcaveSampling.MeanTree.instIsProbabilityMeasureRowTapeRowLaw _root_.OAI.LogConcaveSampling.OracleCompiler.topSeedLaw_probability
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
attribute [-instance] _root_.OAI.LogConcaveSampling.LowerBound.couplingLaw_probability _root_.OAI.LogConcaveSampling.LowerBound.remainingHaar_probability _root_.OAI.LogConcaveSampling.LowerBound.roundRandomLaw_probability _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_invInvariant _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_isHaar _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_probability _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_rightInvariant _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_compactSpace _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_measurableInv _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_measurableMul _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_secondCountable _root_.OAI.LogConcaveSampling.MeanTree.instIsProbabilityMeasureRowTapeRowLaw _root_.OAI.LogConcaveSampling.OracleCompiler.topSeedLaw_probability
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

lemma fullProbabilityFlow_integral {d : ℕ} {F : Point d → ℝ} {lam : ℝ≥0}
    (hF : Primitive F lam) (x : Point d) {r T : ℝ} (hr : 0 ≤ r)
    (hl : (lam:ℝ)*r^2≤1/2) (hT0 : 0<T) (hT1 : T<1)
    {φ : Point d → ℝ} (hφ : Differentiable ℝ φ) {L : ℝ≥0} (hφL : LipschitzWith L φ)
    {B : ℝ} (hB : ∀ z,|φ z|≤B) :
    (∫ z,φ (fullProbabilityFlow hF x hr hl T z) ∂stdGaussian (Point d))=
      ∫ p,φ (interpolationPath T p) ∂(gibbs (primitivePotential F x r)).prod (stdGaussian (Point d)) := by
  rw [fullProbabilityFlow_eq hF x hr hl hT0.le hT1]
  have hh := probabilityFlow_integral hF x hr hl hT0 hT1 hφ hφL hB
  change (∫ y, φ y ∂Measure.map (interpolationPath T)
    ((gibbs (primitivePotential F x r)).prod (stdGaussian (Point d)))) = _ at hh
  rw [integral_map (interpolationPath_measurable T).aemeasurable
    hφ.continuous.aestronglyMeasurable] at hh
  exact hh.symm

lemma fullProbabilityFlow_endpoint_integral {d : ℕ} {F : Point d → ℝ} {lam : ℝ≥0}
    (hF : Primitive F lam) (x : Point d) {r : ℝ} (hr : 0 ≤ r)
    (hl : (lam:ℝ)*r^2≤1/2)
    {φ : Point d → ℝ} (hφ : Differentiable ℝ φ) {L : ℝ≥0} (hφL : LipschitzWith L φ)
    {B : ℝ} (hB : ∀ z,|φ z|≤B) :
    (∫ z,φ (fullProbabilityFlow hF x hr hl 1 z) ∂stdGaussian (Point d))=
      ∫ z,φ z ∂gibbs (primitivePotential F x r) := by
  let μ := gibbs (primitivePotential F x r)
  let ν := stdGaussian (Point d)
  let := probability_gibbs_of_partition
    (partition_pos_of_continuous (hF.continuous_potential x r)).ne'
    (partition_ne_top_of_integrable (hF.integrable_exp_neg_potential x hr (by linarith)))
  let t : ℕ → ℝ := fun n => 1-(1/2:ℝ)^(n+1)
  have ht0 (n : ℕ) : 0<t n := by
    have hh : (1/2:ℝ)^(n+1)<1 := pow_lt_one₀ (by norm_num) (by norm_num) (by omega)
    dsimp [t]; linarith
  have ht1 (n : ℕ) : t n<1 := by
    have hh : 0 < (1/2:ℝ)^(n+1) := by positivity
    dsimp [t]; linarith
  have ht : Tendsto t atTop (𝓝 1) := by
    have hh := (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : 0≤(1/2:ℝ)) (by norm_num)).mul_const (1/2:ℝ)
    simpa only [zero_mul,sub_zero,←pow_succ] using (tendsto_const_nhds (x:=(1:ℝ))).sub hh
  have hleft : Tendsto (fun n => ∫ z,φ (fullProbabilityFlow hF x hr hl (t n) z) ∂ν)
      atTop (𝓝 (∫ z,φ (fullProbabilityFlow hF x hr hl 1 z) ∂ν)) := by
    apply tendsto_integral_of_dominated_convergence (fun _ => B)
      (fun n => (hφ.continuous.comp (fullProbabilityFlow_lipschitz hF x hr hl ⟨(ht0 n).le,(ht1 n).le⟩).continuous).aestronglyMeasurable)
      (integrable_const B)
    · intro n
      exact Filter.Eventually.of_forall (fun z => by simpa only [Function.comp_apply,Real.norm_eq_abs] using hB (fullProbabilityFlow hF x hr hl (t n) z))
    · exact Filter.Eventually.of_forall (fun z => (hφ.continuous.comp
        (fullProbabilityFlow_time_continuous hF x hr hl z)).continuousAt.tendsto.comp ht)
  have hright : Tendsto (fun n => ∫ p,φ (interpolationPath (t n) p) ∂μ.prod ν)
      atTop (𝓝 (∫ p,φ p.1 ∂μ.prod ν)) := by
    apply tendsto_integral_of_dominated_convergence (fun _ => B)
      (fun n => (hφ.continuous.comp (by unfold interpolationPath; fun_prop)).aestronglyMeasurable)
      (integrable_const B)
    · intro n
      exact Filter.Eventually.of_forall (fun p => by simpa only [Function.comp_apply,Real.norm_eq_abs] using hB (interpolationPath (t n) p))
    · filter_upwards [] with p
      have hc : Continuous (fun t : ℝ => φ (interpolationPath t p)) := by
        apply hφ.continuous.comp
        unfold interpolationPath
        fun_prop
      simpa [Function.comp_def,interpolationPath] using hc.continuousAt.tendsto.comp ht
  have he : (fun n => ∫ p,φ (interpolationPath (t n) p) ∂μ.prod ν)=
      (fun n => ∫ z,φ (fullProbabilityFlow hF x hr hl (t n) z) ∂ν) := by
    funext n
    exact (fullProbabilityFlow_integral hF x hr hl (ht0 n) (ht1 n) hφ hφL hB).symm
  rw [he] at hright
  have hh := tendsto_nhds_unique hleft hright
  simpa only [integral_fun_fst,probReal_univ,one_smul] using hh

theorem fullProbabilityFlow_pushforward {d : ℕ} {F : Point d → ℝ} {lam : ℝ≥0}
    (hF : Primitive F lam) (x : Point d) {r : ℝ} (hr : 0 ≤ r)
    (hl : (lam:ℝ)*r^2≤1/2) :
    (stdGaussian (Point d)).map (fullProbabilityFlow hF x hr hl 1)=gibbs (primitivePotential F x r) := by
  let := probability_gibbs_of_partition
    (partition_pos_of_continuous (hF.continuous_potential x r)).ne'
    (partition_ne_top_of_integrable (hF.integrable_exp_neg_potential x hr (by linarith)))
  have hc := (fullProbabilityFlow_lipschitz hF x hr hl (t:=1) ⟨by norm_num,le_rfl⟩).continuous
  apply measure_eq_of_smooth_lipschitz
  intro φ hφ ⟨L,hL⟩ ⟨B,hB⟩
  rw [integral_map hc.measurable.aemeasurable hφ.continuous.aestronglyMeasurable]
  exact fullProbabilityFlow_endpoint_integral hF x hr hl (hφ.differentiable (by norm_num)) hL hB
end LogConcaveSampling

end UpperProof
end
end
end

end OAI
end

section
-- module Solutions.OAIQ048_LC.LogConcave_Sampling_MeanMaterialL2
attribute [-instance] _root_.OAI.LogConcaveSampling.LowerBound.couplingLaw_probability _root_.OAI.LogConcaveSampling.LowerBound.remainingHaar_probability _root_.OAI.LogConcaveSampling.LowerBound.roundRandomLaw_probability _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_invInvariant _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_isHaar _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_probability _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_rightInvariant _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_compactSpace _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_measurableInv _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_measurableMul _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_secondCountable _root_.OAI.LogConcaveSampling.MeanTree.instIsProbabilityMeasureRowTapeRowLaw _root_.OAI.LogConcaveSampling.OracleCompiler.topSeedLaw_probability
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

lemma fullProbabilityFlow_initial {d : ℕ} {F : Point d → ℝ} {lam : ℝ≥0}
    (hF : Primitive F lam) (x : Point d) {r : ℝ} (hr : 0 ≤ r)
    (hl : (lam:ℝ)*r^2≤1/2) : fullProbabilityFlow hF x hr hl 0=id := by
  funext z
  exact GlobalODE.flow_initial _ _ _ _

end LogConcaveSampling

end

end

end

end OAI
end

section
-- module Solutions.OAIQ048_LC.LogConcave_Analysis_PoincareVectorVariance
attribute [-instance] _root_.OAI.LogConcaveSampling.LowerBound.couplingLaw_probability _root_.OAI.LogConcaveSampling.LowerBound.remainingHaar_probability _root_.OAI.LogConcaveSampling.LowerBound.roundRandomLaw_probability _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_invInvariant _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_isHaar _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_probability _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_rightInvariant _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_compactSpace _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_measurableInv _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_measurableMul _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_secondCountable _root_.OAI.LogConcaveSampling.MeanTree.instIsProbabilityMeasureRowTapeRowLaw _root_.OAI.LogConcaveSampling.OracleCompiler.topSeedLaw_probability
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
attribute [-instance] _root_.OAI.LogConcaveSampling.LowerBound.couplingLaw_probability _root_.OAI.LogConcaveSampling.LowerBound.remainingHaar_probability _root_.OAI.LogConcaveSampling.LowerBound.roundRandomLaw_probability _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_invInvariant _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_isHaar _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_probability _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_rightInvariant _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_compactSpace _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_measurableInv _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_measurableMul _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_secondCountable _root_.OAI.LogConcaveSampling.MeanTree.instIsProbabilityMeasureRowTapeRowLaw _root_.OAI.LogConcaveSampling.OracleCompiler.topSeedLaw_probability
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

theorem terminal_transport_error (z : Point d) :
    ‖fullProbabilityFlow hF x hr hl 1 z-(z-r • primitiveField F x r z)‖≤
      terminalTransportConstant*((lam:ℝ)*r^2)*
        (Real.pi*Real.sqrt d+‖z‖+2*r*‖primitiveField F x r 0‖) := by
  let c := primitiveField F x r 0
  let D := Real.pi*Real.sqrt d+‖z‖+2*r*‖c‖
  let ε := 2*((lam:ℝ)*r^2)*D
  let B := |gronwallBound 0 (Real.pi^2+1) 1 1|+1
  let f (t : ℝ) := fullProbabilityFlow hF x hr hl t z
  let g (t : ℝ) := z-t • (r • c)
  have hv (t : ℝ) : LipschitzWith ⟨Real.pi^2+1,by positivity⟩ (fullProbabilityVelocity F x r t) := by
    apply (fullProbabilityVelocity_lipschitz hF x hr hl t).weaken
    change (Real.pi^2/2)*(lam:ℝ)*r^2≤Real.pi^2+1
    have hh := mul_le_mul_of_nonneg_left hl (by positivity : 0≤Real.pi^2/2)
    nlinarith [sq_nonneg Real.pi]
  have hf : Continuous f := fullProbabilityFlow_time_continuous hF x hr hl z
  have hfd : ∀t∈Icc (0:ℝ) 1,HasDerivWithinAt f
      (fullProbabilityVelocity F x r t (f t)) (Icc 0 1) t := by
    intro t ht
    exact GlobalODE.flow_deriv (a:=0) (b:=1)
      (fun t _ => fullProbabilityVelocity_lipschitz hF x hr hl t)
      (fullProbabilityVelocity_continuous hF x hr hl) ⟨0,le_rfl,by norm_num⟩ z t ht
  have hgd (t : ℝ) : HasDerivAt g (-r • c) t := by
    convert (hasDerivAt_const t z).sub ((hasDerivAt_id t).smul_const (r • c)) using 1 <;> first | rfl | simp
  have hg : Continuous g := by dsimp [g]; fun_prop
  have hh := dist_le_of_approx_trajectories_ODE hv hf.continuousOn
    (GlobalODE.right_deriv hfd) (εf:=0) (fun t _ => by simp) hg.continuousOn
    (fun t _ => (hgd t).hasDerivWithinAt) (εg:=ε)
    (fun t ht => probability_affine_residual hF x hr hl z ht)
    (δ:=0) (by simp only [f,g,fullProbabilityFlow_initial,Function.id_def,zero_smul,sub_zero,dist_self,le_refl])
    1 ⟨by norm_num,le_rfl⟩
  simp only [zero_add,sub_zero] at hh
  rw [GlobalODE.gronwallBound_zero_linear] at hh
  change dist (f 1) (g 1)≤ε*gronwallBound 0 (Real.pi^2+1) 1 1 at hh
  have he : dist (f 1) (g 1)≤ε*B := hh.trans (mul_le_mul_of_nonneg_left
    (by dsimp [B]; linarith [le_abs_self (gronwallBound 0 (Real.pi^2+1) 1 1)]) (by dsimp [ε,D]; positivity))
  have hc := (primitiveField_lipschitz hF x hr).dist_le_mul z 0
  simp only [dist_eq_norm,sub_zero,NNReal.coe_mul,NNReal.coe_mk] at hc
  have hbase : dist (g 1) (z-r • primitiveField F x r z)≤((lam:ℝ)*r^2)*‖z‖ := by
    simp only [g,one_smul,dist_sub_left,dist_smul₀,Real.norm_eq_abs,abs_of_nonneg hr]
    rw [dist_comm,dist_eq_norm]
    convert mul_le_mul_of_nonneg_left hc hr using 1
    all_goals try with_reducible_and_instances rfl
    first | rfl | ring
  have hD : ‖z‖≤D := by dsimp [D]; linarith [mul_nonneg Real.pi_pos.le (Real.sqrt_nonneg (d:ℝ)),mul_nonneg (mul_nonneg (by norm_num : (0:ℝ)≤2) hr) (norm_nonneg c)]
  have htot := (dist_triangle (f 1) (g 1) (z-r • primitiveField F x r z)).trans
    (add_le_add he (hbase.trans (mul_le_mul_of_nonneg_left hD (by positivity))))
  change dist (f 1) (z-r • primitiveField F x r z)≤_
  convert htot using 1
  all_goals try with_reducible_and_instances rfl
  first | rfl | (dsimp [ε,B,terminalTransportConstant,D,c]; ring)
end LogConcaveSampling

end

end

end

end OAI
end

section
-- module Solutions.OAIQ048_LC.LogConcave_Analysis_GaussianAffineNormMoment
attribute [-instance] _root_.OAI.LogConcaveSampling.LowerBound.couplingLaw_probability _root_.OAI.LogConcaveSampling.LowerBound.remainingHaar_probability _root_.OAI.LogConcaveSampling.LowerBound.roundRandomLaw_probability _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_invInvariant _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_isHaar _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_probability _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_rightInvariant _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_compactSpace _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_measurableInv _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_measurableMul _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_secondCountable _root_.OAI.LogConcaveSampling.MeanTree.instIsProbabilityMeasureRowTapeRowLaw _root_.OAI.LogConcaveSampling.OracleCompiler.topSeedLaw_probability
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

include hF hr hl in

theorem terminal_mean_squared_error :
    Integrable (fun z => ‖primitiveField F x r z-primitiveExpectedField F x r‖^2)
        (stdGaussian (Point d)) ∧
      (∫z,‖primitiveField F x r z-primitiveExpectedField F x r‖^2 ∂stdGaussian (Point d))≤
        (2*((lam:ℝ)*r))^2*(2*(Real.pi*Real.sqrt d+r*‖primitiveField F x r 0‖)^2+2*d) := by
  apply gaussian_growth_sq_moment ((primitiveField_contDiff hF x r).continuous.sub continuous_const)
    (by positivity) (by positivity)
  intro z
  convert terminal_mean_error hF x hr hl z using 1
  all_goals try with_reducible_and_instances rfl
  first | rfl | ring

theorem terminal_sample_squared_error :
    (stdGaussian (Point d)).map (fullProbabilityFlow hF x hr hl 1)=gibbs (primitivePotential F x r) ∧
    Integrable (fun z => ‖fullProbabilityFlow hF x hr hl 1 z-(z-r • primitiveField F x r z)‖^2)
        (stdGaussian (Point d)) ∧
      (∫z,‖fullProbabilityFlow hF x hr hl 1 z-(z-r • primitiveField F x r z)‖^2 ∂stdGaussian (Point d))≤
        (terminalTransportConstant*((lam:ℝ)*r^2))^2*
          (2*(Real.pi*Real.sqrt d+2*r*‖primitiveField F x r 0‖)^2+2*d) := by
  refine ⟨fullProbabilityFlow_pushforward hF x hr hl,?_⟩
  apply gaussian_growth_sq_moment
    ((fullProbabilityFlow_lipschitz hF x hr hl ⟨by norm_num,le_rfl⟩).continuous.sub
      (continuous_id.sub ((primitiveField_contDiff hF x r).continuous.const_smul r)))
    (mul_nonneg terminalTransportConstant_pos.le (by positivity)) (by positivity)
  intro z
  convert terminal_transport_error hF x hr hl z using 1 <;> first | rfl | ring
end LogConcaveSampling

end

end

end

end OAI
end

section
-- module Solutions.OAIQ048_LC.LogConcave_Numerics_MeanTree
attribute [-instance] _root_.OAI.LogConcaveSampling.LowerBound.couplingLaw_probability _root_.OAI.LogConcaveSampling.LowerBound.remainingHaar_probability _root_.OAI.LogConcaveSampling.LowerBound.roundRandomLaw_probability _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_invInvariant _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_isHaar _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_probability _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_rightInvariant _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_compactSpace _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_measurableInv _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_measurableMul _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_secondCountable _root_.OAI.LogConcaveSampling.MeanTree.instIsProbabilityMeasureRowTapeRowLaw _root_.OAI.LogConcaveSampling.OracleCompiler.topSeedLaw_probability
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
-- module Solutions.OAIQ048_LC.LogConcave_Numerics_Picard
attribute [-instance] _root_.OAI.LogConcaveSampling.LowerBound.couplingLaw_probability _root_.OAI.LogConcaveSampling.LowerBound.remainingHaar_probability _root_.OAI.LogConcaveSampling.LowerBound.roundRandomLaw_probability _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_invInvariant _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_isHaar _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_probability _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_rightInvariant _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_compactSpace _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_measurableInv _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_measurableMul _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_secondCountable _root_.OAI.LogConcaveSampling.MeanTree.instIsProbabilityMeasureRowTapeRowLaw _root_.OAI.LogConcaveSampling.OracleCompiler.topSeedLaw_probability
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
attribute [-instance] _root_.OAI.LogConcaveSampling.LowerBound.couplingLaw_probability _root_.OAI.LogConcaveSampling.LowerBound.remainingHaar_probability _root_.OAI.LogConcaveSampling.LowerBound.roundRandomLaw_probability _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_invInvariant _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_isHaar _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_probability _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_rightInvariant _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_compactSpace _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_measurableInv _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_measurableMul _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_secondCountable _root_.OAI.LogConcaveSampling.MeanTree.instIsProbabilityMeasureRowTapeRowLaw _root_.OAI.LogConcaveSampling.OracleCompiler.topSeedLaw_probability
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

lemma sqrt_le_circuitD {d : ℕ} (F : Point d → ℝ) (x : Point d) : Real.sqrt d ≤ circuitD F x := by
  unfold circuitD; exact le_add_of_nonneg_right (norm_nonneg _)
lemma field_zero_eq_gradient {d : ℕ} (F : Point d → ℝ) (x : Point d) (r : ℝ) :
    primitiveField F x r 0=gradient F x := by simp [primitiveField]

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
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

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
-- module Solutions.OAIQ048_LC.LogConcave_OraclePrograms_Program
attribute [-instance] _root_.OAI.LogConcaveSampling.LowerBound.couplingLaw_probability _root_.OAI.LogConcaveSampling.LowerBound.remainingHaar_probability _root_.OAI.LogConcaveSampling.LowerBound.roundRandomLaw_probability _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_invInvariant _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_isHaar _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_probability _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_rightInvariant _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_compactSpace _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_measurableInv _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_measurableMul _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_secondCountable _root_.OAI.LogConcaveSampling.MeanTree.instIsProbabilityMeasureRowTapeRowLaw _root_.OAI.LogConcaveSampling.OracleCompiler.topSeedLaw_probability
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

lemma oneQuery_run (x : Ω → Point d) (hx : Measurable x)
    (f : Ω × Reply d → O) (hf : Measurable f) (V : Point d → ℝ) (ω : Ω) :
    (oneQuery x hx f hf).run V ω = f (ω, firstOrderReply V (x ω)) := by
  simp [run, history, oneQuery]

end LogConcaveSampling.OracleCompiler.Program

end
end
end

end OAI
end

section
-- module Solutions.OAIQ048_LC.LogConcave_OraclePrograms_TerminalMean
attribute [-instance] _root_.OAI.LogConcaveSampling.LowerBound.couplingLaw_probability _root_.OAI.LogConcaveSampling.LowerBound.remainingHaar_probability _root_.OAI.LogConcaveSampling.LowerBound.roundRandomLaw_probability _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_invInvariant _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_isHaar _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_probability _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_rightInvariant _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_compactSpace _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_measurableInv _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_measurableMul _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_secondCountable _root_.OAI.LogConcaveSampling.MeanTree.instIsProbabilityMeasureRowTapeRowLaw _root_.OAI.LogConcaveSampling.OracleCompiler.topSeedLaw_probability
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

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped BigOperators RealInnerProductSpace

namespace LogConcaveSampling.SeedCompiler
open OracleCompiler
open OracleCompiler.Program

lemma terminalMean_run {d : ℕ} (r σ : ℝ) (V : Point d → ℝ)
    (x : Point d) (g : Fin 2 → Point d) :
    (terminalMean d r σ).run V (x,g) = gradient V (x+r • g 0) + σ • g 1 := by
  rw [terminalMean, oneQuery_run]
  rfl

end LogConcaveSampling.SeedCompiler

end
end

end

end

end OAI
end

section
-- module Solutions.OAIQ048_LC.LogConcave_Dynamics_Squared
attribute [-instance] _root_.OAI.LogConcaveSampling.LowerBound.couplingLaw_probability _root_.OAI.LogConcaveSampling.LowerBound.remainingHaar_probability _root_.OAI.LogConcaveSampling.LowerBound.roundRandomLaw_probability _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_invInvariant _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_isHaar _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_probability _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_rightInvariant _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_compactSpace _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_measurableInv _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_measurableMul _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_secondCountable _root_.OAI.LogConcaveSampling.MeanTree.instIsProbabilityMeasureRowTapeRowLaw _root_.OAI.LogConcaveSampling.OracleCompiler.topSeedLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

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

end LogConcaveSampling.Coupling

end

end

end OAI
end

section
-- module Solutions.OAIQ048_LC.LogConcave_Numerics_Forward
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

lemma depth_forward (r T h : ℝ) (n N : ℕ) (x y : MeanTree X d)
    (i : ProbabilityNode T h n) {b : ℕ} (hx : depth x≤b) (hy : depth y≤b) :
    depth (forward r T h n N x y i)≤b+N := by
  apply (depth_picard _ _ _ (D:=1) (fun _ => hy) ?_ N i).trans (by omega)
  intro j E
  rw [depth_scale]
  exact depth_conditional_le _ _ _ _ (hx.trans (le_max_left _ _)) (le_max_right _ _)
end MeanTree

end LogConcaveSampling

end

end

end OAI
end

section
-- module Solutions.OAIQ048_LC.LogConcave_OraclePrograms_Expression
attribute [-instance] _root_.OAI.LogConcaveSampling.LowerBound.couplingLaw_probability _root_.OAI.LogConcaveSampling.LowerBound.remainingHaar_probability _root_.OAI.LogConcaveSampling.LowerBound.roundRandomLaw_probability _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_invInvariant _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_isHaar _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_probability _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_rightInvariant _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_compactSpace _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_measurableInv _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_measurableMul _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_secondCountable _root_.OAI.LogConcaveSampling.MeanTree.instIsProbabilityMeasureRowTapeRowLaw _root_.OAI.LogConcaveSampling.OracleCompiler.topSeedLaw_probability
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

end Expression
end LogConcaveSampling.OracleCompiler

end

end

section

noncomputable section

namespace LogConcaveSampling.SeedCompiler
open OracleCompiler
open scoped NNReal

variable {d : ℕ} {V : Point d → ℝ} {K : ℝ≥0}

lemma terminalMean_fixedSeed_lip (hV : LipschitzWith K (gradient V))
    (r σ : ℝ) (g : Fin 2 → Point d) :
    LipschitzWith K (fun x => (terminalMean d r σ).run V (x,g)) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  simp only [terminalMean_run,dist_add_right]
  simpa only [dist_add_right] using hV.dist_le_mul (x+r • g 0) (y+r • g 0)

end LogConcaveSampling.SeedCompiler

end

end

end

end OAI
end

section
-- module Solutions.OAIQ048_LC.LogConcave_Numerics_RowGaussian
attribute [-instance] _root_.OAI.LogConcaveSampling.LowerBound.couplingLaw_probability _root_.OAI.LogConcaveSampling.LowerBound.remainingHaar_probability _root_.OAI.LogConcaveSampling.LowerBound.roundRandomLaw_probability _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_invInvariant _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_isHaar _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_probability _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_rightInvariant _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_compactSpace _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_measurableInv _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_measurableMul _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_secondCountable _root_.OAI.LogConcaveSampling.OracleCompiler.topSeedLaw_probability
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
-- module Solutions.OAIQ048_LC.LogConcave_Numerics_BaseVariation
attribute [-instance] _root_.OAI.LogConcaveSampling.LowerBound.couplingLaw_probability _root_.OAI.LogConcaveSampling.LowerBound.remainingHaar_probability _root_.OAI.LogConcaveSampling.LowerBound.roundRandomLaw_probability _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_invInvariant _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_isHaar _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_probability _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_rightInvariant _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_compactSpace _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_measurableInv _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_measurableMul _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_secondCountable _root_.OAI.LogConcaveSampling.OracleCompiler.topSeedLaw_probability
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
attribute [-instance] _root_.OAI.LogConcaveSampling.LowerBound.couplingLaw_probability _root_.OAI.LogConcaveSampling.LowerBound.remainingHaar_probability _root_.OAI.LogConcaveSampling.LowerBound.roundRandomLaw_probability _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_invInvariant _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_isHaar _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_probability _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_rightInvariant _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_compactSpace _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_measurableInv _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_measurableMul _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_secondCountable _root_.OAI.LogConcaveSampling.OracleCompiler.topSeedLaw_probability
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

lemma literalSample_variationX {r T h : ℝ} {n N : ℕ}
    (hr : 0 ≤ r) (hn : 0<n) (hT : 0<T) (hT1 : T<1) (hh : 0<h)
    (e : ProbabilityNode T h n) (x y z : Point d) :
    BaseVariation ‖x-y‖ (x,z) (y,z) (literalSample r T h n N e) := by
  have hg := literalSample_geometry (d:=d) (r:=r) (N:=N) hn hT hT1 hh e
  apply baseVariation_of_centers
  · rw [hg.1]; simp
  · exact centers_mono _ (fun r' b hb => by
      simpa only [Prod.fst,Prod.snd,sub_self,norm_zero,add_zero,mul_zero] using hb.variation hr hT1.le (x,z) (y,z)) hg.2
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
attribute [-instance] _root_.OAI.LogConcaveSampling.LowerBound.couplingLaw_probability _root_.OAI.LogConcaveSampling.LowerBound.remainingHaar_probability _root_.OAI.LogConcaveSampling.LowerBound.roundRandomLaw_probability _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_invInvariant _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_isHaar _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_probability _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_rightInvariant _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_compactSpace _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_measurableInv _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_measurableMul _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_secondCountable _root_.OAI.LogConcaveSampling.MeanTree.instIsProbabilityMeasureRowTapeRowLaw _root_.OAI.LogConcaveSampling.OracleCompiler.topSeedLaw_probability
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
-- module Solutions.OAIQ048_LC.LogConcave_OraclePrograms_TerminalMeanProgram
attribute [-instance] _root_.OAI.LogConcaveSampling.LowerBound.couplingLaw_probability _root_.OAI.LogConcaveSampling.LowerBound.remainingHaar_probability _root_.OAI.LogConcaveSampling.LowerBound.roundRandomLaw_probability _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_invInvariant _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_isHaar _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_probability _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_rightInvariant _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_compactSpace _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_measurableInv _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_measurableMul _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_secondCountable _root_.OAI.LogConcaveSampling.MeanTree.instIsProbabilityMeasureRowTapeRowLaw _root_.OAI.LogConcaveSampling.OracleCompiler.topSeedLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
namespace LogConcaveSampling
open MeasureTheory ProbabilityTheory OracleCompiler Program Coupling
open scoped Classical BigOperators NNReal

variable {d : ℕ}

lemma terminalReservedProgram_pre_run (r η : ℝ) (V : Point d → ℝ)
    (x : Point d) (g : Fin 2 → Point d) :
    (terminalReservedProgram d r η).pre.run V (x,g)=
      g 0-r • gradient V (x+r • g 0)+(Real.sqrt 3*η/2) • g 1 := by
  exact oneQuery_run (fun p : Point d × (Fin 2 → Point d) => p.1+r • p.2 0) (by fun_prop)
    (fun p => p.1.2 0-r • p.2.2+(Real.sqrt 3*η/2) • p.1.2 1) (by fun_prop) V (x,g)

variable {slotCount : ℕ}

lemma gaussianTape_eval (i : Fin slotCount) :
    (gaussianTape d slotCount).map (fun g => g i)=stdGaussian (Point d) :=
  (measurePreserving_eval (fun _ : Fin slotCount => stdGaussian (Point d)) i).map_eq

lemma gaussianTape_integrable_eval (f : Point d → ℝ) (_hf : Measurable f)
    (hi : Integrable f (stdGaussian (Point d))) (i : Fin slotCount) :
    Integrable (fun g : Fin slotCount → Point d => f (g i)) (gaussianTape d slotCount) := by
  have hh : Integrable f ((gaussianTape d slotCount).map (fun g => g i)) := by rw [gaussianTape_eval]; exact hi
  exact hh.comp_measurable (measurable_pi_apply i)

lemma gaussianTape_integral_eval (f : Point d → ℝ) (hf : Measurable f) (i : Fin slotCount) :
    (∫g : Fin slotCount → Point d,f (g i) ∂gaussianTape d slotCount)=∫z,f z ∂stdGaussian (Point d) :=
  (measurePreserving_eval (fun _ : Fin slotCount => stdGaussian (Point d)) i).hasLaw.integral_comp hf.aestronglyMeasurable

theorem terminalMeanProgram_squared {F : Point d → ℝ} {lam : ℝ≥0} (hF : Primitive F lam)
    (x : Point d) {r : ℝ} (hr : 0 ≤ r) (hl : (lam:ℝ)*r^2≤1/2) (σ : ℝ) :
    SquaredAt (gaussianTape d 2) (stdGaussian (Point d))
      (fun g => (terminalMeanProgram d r σ).program.run F (x,g))
      (fun g => primitiveExpectedField F x r+σ • g)
      ((2*((lam:ℝ)*r))^2*(2*(Real.pi*Real.sqrt d+r*‖primitiveField F x r 0‖)^2+2*d)) := by
  have hm : Measurable (fun z => ‖primitiveField F x r z-primitiveExpectedField F x r‖^2) :=
    ((primitiveField_contDiff hF x r).continuous.measurable.sub measurable_const).norm.pow_const 2
  have he (g : Fin 2 → Point d) :
      ‖(terminalMeanProgram d r σ).program.run F (x,g)-
        (primitiveExpectedField F x r+σ • g 1)‖^2=
      ‖primitiveField F x r (g 0)-primitiveExpectedField F x r‖^2 := by
    change ‖(SeedCompiler.terminalMean d r σ).run F (x,g)-_‖^2=_
    rw [SeedCompiler.terminalMean_run,add_sub_add_right_eq_sub]
    rfl
  have ht := terminal_mean_squared_error hF x hr hl
  apply SquaredAt.of_joint (gaussianTape d 2) (gaussianTape d 2) (stdGaussian (Point d))
    id (fun g => g 1) measurable_id (measurable_pi_apply 1) Measure.map_id (gaussianTape_eval 1)
    _ _ ?_ (by fun_prop)
  · simpa only [id_eq,he] using gaussianTape_integrable_eval _ hm ht.1 (0:Fin 2)
  · simpa only [id_eq,he,gaussianTape_integral_eval _ hm (0:Fin 2)] using ht.2
  · change Measurable (fun g => (SeedCompiler.terminalMean d r σ).run F (x,g))
    simp only [SeedCompiler.terminalMean_run]
    have hg := hF.gradient_lipschitz.continuous.measurable
    fun_prop
end LogConcaveSampling

end

end

end OAI
end

section
-- module Solutions.OAIQ048_LC.LogConcave_Numerics_CompileDeclaredRootNormalized
attribute [-instance] _root_.OAI.LogConcaveSampling.LowerBound.couplingLaw_probability _root_.OAI.LogConcaveSampling.LowerBound.remainingHaar_probability _root_.OAI.LogConcaveSampling.LowerBound.roundRandomLaw_probability _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_invInvariant _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_isHaar _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_probability _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_rightInvariant _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_compactSpace _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_measurableInv _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_measurableMul _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_secondCountable _root_.OAI.LogConcaveSampling.OracleCompiler.topSeedLaw_probability
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
-- module Solutions.OAIQ048_LC.LogConcave_OraclePrograms_RoutineKind
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
namespace LogConcaveSampling.OracleCompiler
open scoped Classical

theorem routine_induction {t : ℝ} (ht : 0<t) (hs : t≤1/44)
    (P : RoutineLabel → Prop) (hbase : ∀L,L.terminal → P L)
    (hstep : ∀L,¬L.terminal → (∀C,RoutineStep t L C → P C) → P L) : ∀L,P L := by
  intro L
  induction hn : L.rank t using Nat.strong_induction_on generalizing L with
  | h n ih =>
    by_cases hL : L.terminal
    · exact hbase L hL
    · apply hstep L hL
      intro C hc
      exact ih _ (hn ▸ hc.rank_lt ht hs hL) C rfl
end LogConcaveSampling.OracleCompiler

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

end LogConcaveSampling

end

end

end OAI
end

section
-- module Solutions.OAIQ048_LC.LogConcave_OraclePrograms_MeanSize
attribute [-instance] _root_.OAI.LogConcaveSampling.LowerBound.couplingLaw_probability _root_.OAI.LogConcaveSampling.LowerBound.remainingHaar_probability _root_.OAI.LogConcaveSampling.LowerBound.roundRandomLaw_probability _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_invInvariant _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_isHaar _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_probability _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_rightInvariant _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_compactSpace _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_measurableInv _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_measurableMul _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_secondCountable _root_.OAI.LogConcaveSampling.OracleCompiler.topSeedLaw_probability
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
-- module Solutions.OAIQ048_LC.LogConcave_OraclePrograms_SampleParentEquivariant
attribute [-instance] _root_.OAI.LogConcaveSampling.LowerBound.couplingLaw_probability _root_.OAI.LogConcaveSampling.LowerBound.remainingHaar_probability _root_.OAI.LogConcaveSampling.LowerBound.roundRandomLaw_probability _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_invInvariant _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_isHaar _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_probability _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_rightInvariant _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_compactSpace _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_measurableInv _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_measurableMul _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_secondCountable _root_.OAI.LogConcaveSampling.MeanTree.instIsProbabilityMeasureRowTapeRowLaw _root_.OAI.LogConcaveSampling.OracleCompiler.topSeedLaw_probability
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

lemma sampleParent_lipschitz (V : Point d → ℝ) (E : Expression (Point d × Point d) d)
    (v : Fin E.slots → ℝ) (T η K : ℝ)
    (hE : ∀x y z g,‖E.eval V (x,z) g-E.eval V (y,z) g‖≤K*‖x-y‖) :
    ∀x y g,‖(sampleParent E v T η).pre.run V (x,g)-(sampleParent E v T η).pre.run V (y,g)‖≤K*‖x-y‖ := by
  intro x y g
  rw [sampleParent_run E v T η V x g,sampleParent_run E v T η V y g]
  exact hE _ _ _ _

end LogConcaveSampling.OracleCompiler

end

end

section

noncomputable section
namespace LogConcaveSampling
open MeasureTheory ProbabilityTheory OracleCompiler Program Coupling Expression
open scoped Classical BigOperators NNReal

variable {d : ℕ}

theorem terminalReservedProgram_squared {F : Point d → ℝ} {lam : ℝ≥0} (hF : Primitive F lam)
    (x : Point d) {r : ℝ} (hr : 0 ≤ r) (hl : (lam:ℝ)*r^2≤1/2) (η : ℝ) :
    SquaredAt (gaussianTape d 2) ((gibbs (primitivePotential F x r)).prod (stdGaussian (Point d)))
      (fun g => (terminalReservedProgram d r η).pre.run F (x,g))
      (fun z => z.1+(Real.sqrt 3*η/2) • z.2)
      ((terminalTransportConstant*((lam:ℝ)*r^2))^2*
        (2*(Real.pi*Real.sqrt d+2*r*‖primitiveField F x r 0‖)^2+2*d)) := by
  let f := fullProbabilityFlow hF x hr hl 1
  have hf : Measurable f := (fullProbabilityFlow_lipschitz hF x hr hl ⟨by norm_num,le_rfl⟩).continuous.measurable
  have hm : Measurable (fun z => ‖f z-(z-r • primitiveField F x r z)‖^2) := by
    have hh := (primitiveField_contDiff hF x r).continuous.measurable
    fun_prop
  have hp := terminal_sample_squared_error hF x hr hl
  have hlaw : (gaussianTape d 2).map (fun g => (f (g 0),g 1))=
      (gibbs (primitivePotential F x r)).prod (stdGaussian (Point d)) := by
    have hpair := (measurePreserving_finTwoArrow (stdGaussian (Point d))).map_eq
    have ht := congrArg (Measure.map (Prod.map f id)) hpair
    rw [Measure.map_map (by fun_prop) (by fun_prop),←Measure.map_prod_map _ _ hf measurable_id,
      Measure.map_id,hp.1] at ht
    exact ht
  have he (g : Fin 2 → Point d) :
      ‖(terminalReservedProgram d r η).pre.run F (x,g)-
        (f (g 0)+(Real.sqrt 3*η/2) • g 1)‖^2=
      ‖f (g 0)-((g 0)-r • primitiveField F x r (g 0))‖^2 := by
    rw [terminalReservedProgram_pre_run,add_sub_add_right_eq_sub,norm_sub_rev]
    rfl
  apply SquaredAt.of_joint (gaussianTape d 2) (gaussianTape d 2)
    ((gibbs (primitivePotential F x r)).prod (stdGaussian (Point d)))
    id (fun g => (f (g 0),g 1)) measurable_id (by fun_prop) Measure.map_id hlaw
    _ _ ?_ (by fun_prop)
  · simpa only [id_eq,he] using gaussianTape_integrable_eval _ hm hp.2.1 (0:Fin 2)
  · simpa only [id_eq,he,gaussianTape_integral_eval _ hm (0:Fin 2)] using hp.2.2
  · have hg := hF.gradient_lipschitz.continuous.measurable
    simp only [terminalReservedProgram_pre_run]
    fun_prop

lemma terminalReservedProgram_lipschitz (r η : ℝ) {F : Point d → ℝ} {lam : ℝ≥0}
    (hF : Primitive F lam) : ∀x y g,
    ‖(terminalReservedProgram d r η).pre.run F (x,g)-(terminalReservedProgram d r η).pre.run F (y,g)‖≤
      |r| *(lam:ℝ)*‖x-y‖ := by
  intro x y g
  change Fin 2 → Point d at g
  rw [terminalReservedProgram_pre_run r η F x g,terminalReservedProgram_pre_run r η F y g,add_sub_add_right_eq_sub]
  have he : g 0-r • gradient F (x+r • g 0)-(g 0-r • gradient F (y+r • g 0))=
      (-r) • (gradient F (x+r • g 0)-gradient F (y+r • g 0)) := by module
  rw [he,norm_smul,Real.norm_eq_abs,abs_neg]
  have hh := hF.gradient_lipschitz.dist_le_mul (x+r • g 0) (y+r • g 0)
  rw [dist_eq_norm,dist_eq_norm,add_sub_add_right_eq_sub] at hh
  exact (mul_le_mul_of_nonneg_left hh (abs_nonneg r)).trans_eq (by ring)

end LogConcaveSampling

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
attribute [-instance] _root_.OAI.LogConcaveSampling.LowerBound.couplingLaw_probability _root_.OAI.LogConcaveSampling.LowerBound.remainingHaar_probability _root_.OAI.LogConcaveSampling.LowerBound.roundRandomLaw_probability _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_invInvariant _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_isHaar _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_probability _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_rightInvariant _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_compactSpace _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_measurableInv _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_measurableMul _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_secondCountable _root_.OAI.LogConcaveSampling.OracleCompiler.topSeedLaw_probability
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

section

noncomputable section
namespace LogConcaveSampling.OracleCompiler
open MeasureTheory ProbabilityTheory Coupling
open scoped Classical NNReal

variable {d : ℕ}

lemma primitive_terminal_envelope (F : Point d → ℝ) (x : Point d) {r c : ℝ}
    (hr : 0 ≤ r) (hr1 : r≤1) (hc : 0 ≤ c) :
    2*(Real.pi*Real.sqrt d+c*r*‖primitiveField F x r 0‖)^2+2*d≤
      (2*(Real.pi+c)^2+2)*(circuitD F x)^2 := by
  rw [field_zero_eq_gradient]
  have hs := sqrt_le_circuitD F x
  have hg : ‖gradient F x‖ ≤ circuitD F x := le_add_of_nonneg_left (Real.sqrt_nonneg _)
  have hcr := mul_le_mul_of_nonneg_left hr1 hc
  have hcg := mul_le_mul_of_nonneg_left hg hc
  have hrG := mul_le_mul_of_nonneg_right hcr (norm_nonneg (gradient F x))
  have hp := mul_le_mul_of_nonneg_left hs Real.pi_pos.le
  have hu : Real.pi*Real.sqrt d+c*r*‖gradient F x‖≤(Real.pi+c)*circuitD F x := by nlinarith
  have hu2 := pow_le_pow_left₀ (show 0≤Real.pi*Real.sqrt d+c*r*‖gradient F x‖ by positivity) hu 2
  have hd2 := pow_le_pow_left₀ (Real.sqrt_nonneg (d:ℝ)) hs 2
  rw [Real.sq_sqrt (Nat.cast_nonneg d)] at hd2
  nlinarith

lemma terminalMean_correct {F : Point d → ℝ} {lam : ℝ≥0} (hF : Primitive F lam)
    {q : ℝ} (hq : q≤1/2) :
    MeanCorrect F lam q 1 ((4*(Real.pi+2))*q) (terminalMeanProgram d) := by
  constructor
  · intro r σ hs x y g
    change ‖(SeedCompiler.terminalMean d r σ).run F (x,g)-
      (SeedCompiler.terminalMean d r σ).run F (y,g)‖≤(lam:ℝ)*1*‖x-y‖
    simp only [mul_one]
    exact (SeedCompiler.terminalMean_fixedSeed_lip hF.gradient_lipschitz r σ g).norm_sub_le x y
  · intro r σ hs x
    apply (terminalMeanProgram_squared hF x hs.1.le (hs.2.2.2.1.trans hq) σ).mono
    have hb := primitive_terminal_envelope F x hs.1.le hs.2.1 (c:=1) (by norm_num)
    simp only [one_mul] at hb
    have hq0 := hs.nonneg lam.coe_nonneg
    have hr := hs.1
    have hsq := pow_le_pow_left₀ (show 0≤(lam:ℝ)*r by positivity) hs.2.2.2.2 2
    have hm := mul_le_mul_of_nonneg_left hb (sq_nonneg (2*((lam:ℝ)*r)))
    have hc : 4*(2*(Real.pi+1)^2+2)≤(4*(Real.pi+2))^2 := by nlinarith [Real.pi_pos]
    have h₁ := mul_le_mul_of_nonneg_right hsq (show 0≤4*(2*(Real.pi+1)^2+2)*(circuitD F x)^2 by positivity)
    have h₂ := mul_le_mul_of_nonneg_right hc (show 0≤(q*σ)^2*(circuitD F x)^2 by positivity)
    nlinarith

lemma terminalSample_correct {F : Point d → ℝ} {lam : ℝ≥0} (hF : Primitive F lam)
    {q : ℝ} (hq : q≤1/2) (ηmin : ℝ) :
    SampleCorrect F lam q 1 ((2*terminalTransportConstant*(Real.pi+3))*q) ηmin
      (terminalReservedProgram d) := by
  constructor
  · intro r η hs _ x y g
    have hh := terminalReservedProgram_lipschitz r η hF x y g
    rw [abs_of_pos hs.1] at hh
    simpa only [mul_one,mul_comm r (lam:ℝ)] using hh
  · intro r η hs _ x
    have hq0 := hs.nonneg lam.coe_nonneg
    have hl : (lam:ℝ)*r^2≤q := hs.2.2.2.2.trans
      (mul_le_of_le_one_right hq0 hs.2.2.2.1)
    apply (terminalReservedProgram_squared hF x hs.1.le (hl.trans hq) η).mono
    have hb := primitive_terminal_envelope F x hs.1.le hs.2.1 (c:=2) (by norm_num)
    have hsq := pow_le_pow_left₀ (show 0≤(lam:ℝ)*r^2 by positivity) hl 2
    have hm := mul_le_mul_of_nonneg_left hb (sq_nonneg (terminalTransportConstant*((lam:ℝ)*r^2)))
    have hc : 2*(Real.pi+2)^2+2≤(2*(Real.pi+3))^2 := by nlinarith [Real.pi_pos]
    have h₁ := mul_le_mul_of_nonneg_right hsq (show 0≤terminalTransportConstant^2*(2*(Real.pi+2)^2+2)*(circuitD F x)^2 by positivity)
    have h₂ := mul_le_mul_of_nonneg_right hc (show 0≤terminalTransportConstant^2*q^2*(circuitD F x)^2 by positivity)
    nlinarith
end LogConcaveSampling.OracleCompiler

end

end

end OAI
end

section
-- module Solutions.OAIQ048_LC.LogConcave_OraclePrograms_MeanTreeBase
attribute [-instance] _root_.OAI.LogConcaveSampling.LowerBound.couplingLaw_probability _root_.OAI.LogConcaveSampling.LowerBound.remainingHaar_probability _root_.OAI.LogConcaveSampling.LowerBound.roundRandomLaw_probability _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_invInvariant _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_isHaar _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_probability _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_rightInvariant _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_compactSpace _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_measurableInv _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_measurableMul _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_secondCountable _root_.OAI.LogConcaveSampling.OracleCompiler.topSeedLaw_probability
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

lemma sampleCompiled_variation {r η Lf Li : ℝ} (hr : 0 < r) (hη : 0<η) (hη1 : η≤1)
    (hA : C.A=C.actualA) (hAf : C.Af=C.actualAf)
    (hLf : 0≤Lf) (hLi : 0≤Li) (hsmall : Li*C.sampleCenterBudget r≤1)
    (V : Point d → ℝ) (P : Bool → ℝ → ℝ → Prop) (M : Bool → ℝ → ℝ → SeedProgram d)
    (hm : ∀r τ,P true r τ → ∀u v g,‖(M true r τ).program.run V (u,g)-(M true r τ).program.run V (v,g)‖≤Lf*‖u-v‖)
    (hmi : ∀r τ,P false r τ → ∀u v g,‖(M false r τ).program.run V (u,g)-(M false r τ).program.run V (v,g)‖≤Li*‖u-v‖)
    (n : ℝ) (hready : RootShiftReady C.D (C.sampleCenterBudget r) (C.sampleFinalBudget r)
      (P true) (P false) (C.sampleTree (d:=d) r η hη hη1) n) :
    let E := compileDeclaredRoot C.D (C.sampleCenterBudget r) (C.sampleFinalBudget r)
      (M true) (M false) (C.sampleTree (d:=d) r η hη hη1) n
    ∀x y z g,‖E.eval V (x,z) g-E.eval V (y,z) g‖≤
      (C.sampleFinalBudget r*Lf*(depth (C.sampleTree (d:=d) r η hη hη1):ℝ))*‖x-y‖ := by
  have hw := C.sampleTree_actual_weights (d:=d) hr hη hη1
  rw [←hAf,←hA] at hw
  have hp := sampleCorrelation_properties hη hη1
  have hT0 : 0 < sampleCorrelation η := by linarith [hp.1]
  dsimp only
  intro x y z g
  have hg := literalSample_geometry (d:=d) (r:=r) (N:=C.N) (Nat.succ_pos C.n)
    hT0 hp.2.1 C.h_pos (C.sampleEndpoint η hη hη1)
  have he := compileDeclaredRoot_variation (Af:=C.sampleFinalBudget r) hLf hLi (norm_nonneg (x-y)) hsmall V P M hm hmi
    (C.sampleTree r η hη hη1) n (x,z) (y,z)
    (literalSample_variationX hr.le (Nat.succ_pos C.n) hT0 hp.2.1 C.h_pos (C.sampleEndpoint η hη hη1) x y z)
    (Bf:=0) (by unfold sampleTree; rw [hg.1]; simp) hw.1 hw.2 hready g
  simpa only [add_zero] using he

end LogConcaveSampling.OracleCompiler.CircuitParameters

end

end

end OAI
end

section
-- module Solutions.OAIQ048_LC.LogConcave_OraclePrograms_FullTape
attribute [-instance] _root_.OAI.LogConcaveSampling.LowerBound.couplingLaw_probability _root_.OAI.LogConcaveSampling.LowerBound.remainingHaar_probability _root_.OAI.LogConcaveSampling.LowerBound.roundRandomLaw_probability _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_invInvariant _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_isHaar _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_probability _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_rightInvariant _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_compactSpace _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_measurableInv _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_measurableMul _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_secondCountable _root_.OAI.LogConcaveSampling.OracleCompiler.topSeedLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
namespace LogConcaveSampling.OracleCompiler.CircuitParameters
open MeanTree

variable (C : CircuitParameters) {d : ℕ}

lemma sampleTree_depth (r η : ℝ) (hη : 0<η) (hη1 : η≤1) :
    depth (C.sampleTree (d:=d) r η hη hη1)≤C.depthBound := by
  have hh := depth_forward r (sampleCorrelation η) C.h (C.n+1) C.N
    (anchor (Prod.fst : SampleInput d → Point d) (by fun_prop))
    (anchor Prod.snd (by fun_prop)) (C.sampleEndpoint η hη hη1) (b:=0) (by simp) (by simp)
  dsimp only [sampleTree,literalSample] at ⊢
  rw [depth_scale]
  unfold depthBound
  nlinarith

end LogConcaveSampling.OracleCompiler.CircuitParameters

end

end

section

noncomputable section
namespace LogConcaveSampling.OracleCompiler
open MeasureTheory MeanTree
open scoped Classical NNReal

variable {d : ℕ}

namespace CircuitParameters
variable (C : CircuitParameters)

lemma sampleFrom_lipschitz {F : Point d → ℝ} {lam : ℝ≥0} {q Kf Ki ef ei r η : ℝ}
    (hs : SampleSize lam q r η) (hRη : Real.sqrt (1-C.T^2)≤η) (hD : 0<C.D)
    (hA : C.A=C.actualA) (hAf : C.Af=C.actualAf)
    (hKf : 0≤Kf) (hKi : 0≤Ki)
    (hsmall : (lam:ℝ)*Ki*C.sampleCenterBudget r≤1)
    (Mf Mi : ℝ → ℝ → SeedProgram d)
    (hf : MeanCorrect F lam ((1+4*C.Af)*q) Kf ef Mf)
    (hi : MeanCorrect F lam (q*(1+16*C.D*C.A/Real.sqrt (1-C.T^2))) Ki ei Mi) :
    ∀x y g, ‖(C.sampleFrom Mf Mi r η).pre.run F (x,g)-
      (C.sampleFrom Mf Mi r η).pre.run F (y,g)‖≤
      (lam:ℝ)*r*(C.Af*(depth (C.sampleTree (d:=d) r η hs.2.2.1 hs.2.2.2.1):ℝ)*Kf)*‖x-y‖ := by
  let P : Bool → ℝ → ℝ → Prop := fun s => if s then
    MeanSize lam ((1+4*C.Af)*q) else MeanSize lam (q*(1+16*C.D*C.A/Real.sqrt (1-C.T^2)))
  let M : Bool → ℝ → ℝ → SeedProgram d := fun s => if s then Mf else Mi
  have hv := C.sampleTree_valid (d:=d) lam.coe_nonneg hs C.residual_pos hRη hD hA hAf
  have hrdy := hv.shiftReady (P true) (P false) (fun _ _ h => h.1.ne')
    (fun _ _ h => h.1.ne') _ _
  have hE := C.sampleCompiled_variation hs.1 hs.2.2.1 hs.2.2.2.1 hA hAf
    (mul_nonneg lam.coe_nonneg hKf) (mul_nonneg lam.coe_nonneg hKi) hsmall F P M hf.lip hi.lip
    (η/Real.sqrt 2) hrdy
  unfold sampleFrom
  rw [dite_eq_left ⟨hs.1,hs.2.2.1,hs.2.2.2.1⟩]
  dsimp only
  intro x y g
  have he := sampleParent_lipschitz F _ _ _ _ _ hE x y g
  convert! he using 1
  all_goals try with_reducible_and_instances rfl
  unfold sampleFinalBudget
  ring

end CircuitParameters
end LogConcaveSampling.OracleCompiler

end

end

section

noncomputable section
namespace LogConcaveSampling.OracleCompiler
open MeanTree Coupling
open scoped Classical NNReal

lemma sample_error_envelope {η a en D : ℝ} (hη : 0≤η) (hη1 : η≤1)
    (ha : 0≤a) (hen : 0≤en) :
    (400*(η*a)^2+4*en^2)*D^2≤(20*a+2*en)^2*D^2 := by
  have hη2 : η^2≤1 := by nlinarith
  have hh := mul_le_mul_of_nonneg_right hη2 (sq_nonneg a)
  apply mul_le_mul_of_nonneg_right _ (sq_nonneg D)
  nlinarith [mul_nonneg ha hen]

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

lemma sampleCenter_scaled {lam q r η : ℝ} (hs : SampleSize lam q r η)
    (hlam : 0≤lam) (hA : 0≤C.A) : lam*C.sampleCenterBudget r≤2*C.A*q := by
  have hq := hs.nonneg hlam
  have he := hs.2.2.2.2.trans (mul_le_of_le_one_right hq hs.2.2.2.1)
  unfold sampleCenterBudget
  nlinarith [mul_le_mul_of_nonneg_left he hA,mul_nonneg hA hq]

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

end CircuitParameters
end LogConcaveSampling.OracleCompiler

end

end

end OAI
end

section
-- module Solutions.OAIQ048_LC.LogConcave_OraclePrograms_SampleCorrect
attribute [-instance] _root_.OAI.LogConcaveSampling.LowerBound.couplingLaw_probability _root_.OAI.LogConcaveSampling.LowerBound.remainingHaar_probability _root_.OAI.LogConcaveSampling.LowerBound.roundRandomLaw_probability _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_invInvariant _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_isHaar _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_probability _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_rightInvariant _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_compactSpace _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_measurableInv _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_measurableMul _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_secondCountable _root_.OAI.LogConcaveSampling.OracleCompiler.topSeedLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
namespace LogConcaveSampling.OracleCompiler.CircuitParameters
open MeanTree Coupling MeasureTheory ProbabilityTheory
open scoped Classical NNReal

variable (C : CircuitParameters) {d : ℕ}

theorem sampleFrom_correct {F : Point d → ℝ} {lam : ℝ≥0} (hF : Primitive F lam)
    {q Kf Ki ef ei en ηmin : ℝ} (hd : 1≤d) (hlam : (lam:ℝ)≤1)
    (hq : 0≤q) (hql : q≤1/4) (hR : Real.sqrt (1-C.T^2)≤ηmin)
    (hD : 1≤C.D) (hA : C.A=C.actualA) (hAf : C.Af=C.actualAf)
    (hKf : 0≤Kf) (hKi : 0≤Ki) (hef : 0<ef) (hei : 0≤ei) (hen : 0≤en)
    (hsmall : 2*C.A*q*(2*Real.pi+2)≤1) (hcon : 4*C.A*q*Ki≤1)
    (Mf Mi : ℝ → ℝ → SeedProgram d) (B : ℕ) (hBD : (B:ℝ)≤C.D^2)
    (hbudget : ∀(s : Bool) r τ,MeanBudget B r ((if s then Mf else Mi) r τ))
    (hf : MeanCorrect F lam ((1+4*C.Af)*q) Kf ef Mf)
    (hi : MeanCorrect F lam (q*(1+16*C.D*C.A/Real.sqrt (1-C.T^2))) Ki ei Mi)
    (hnum : C.SampleNumericalReady hF q en) :
    SampleCorrect F lam q (C.Af*C.depthBound*Kf)
      (C.sampleError C.depthBound Kf q ei ef en) ηmin (C.sampleFrom Mf Mi) := by
  have hA0 : 0<C.A := hA ▸ C.actualA_pos
  have hAf0 : 0<C.Af := hAf ▸ C.actualAf_pos
  have small {r η : ℝ} (hs : SampleSize lam q r η) :=
    physical_small_of_scaled hA0.le hq hKi
      (show 0≤(lam:ℝ)*C.sampleCenterBudget r by unfold sampleCenterBudget; positivity)
      (C.sampleCenter_scaled hs lam.coe_nonneg hA0.le) hsmall hcon
  constructor
  · intro r η hs hη x y g
    have he := C.sampleFrom_lipschitz hs (hR.trans hη) (by linarith) hA hAf hKf hKi
      (small hs).2.2 Mf Mi hf hi x y g
    apply he.trans
    have hdep : (depth (C.sampleTree (d:=d) r η hs.2.2.1 hs.2.2.2.1):ℝ)≤C.depthBound :=
      by exact_mod_cast C.sampleTree_depth (d:=d) r η hs.2.2.1 hs.2.2.2.1
    have hh := mul_le_mul_of_nonneg_right hdep
      (show 0≤(lam:ℝ)*r*C.Af*Kf*‖x-y‖ by positivity [hs.1])
    nlinarith only [hh]
  · intro r η hs hη x
    have hL : (lam:ℝ)*r≤1 := (mul_le_of_le_one_left hs.1.le hlam).trans hs.2.1
    have hlr : (lam:ℝ)*r^2≤1/2 := by
      have hh := hs.2.2.2.2.trans (mul_le_of_le_one_right hq hs.2.2.2.1)
      linarith
    have hp := C.sampleFrom_squared hF hd hs hql hL (hR.trans hη) hD hA hAf hKf hKi hef hei
      (small hs).1 (small hs).2.1 Mf Mi B hBD hbudget hf hi x hlr
      (hnum x r η hs hlr).1 (hnum x r η hs hlr).2
    apply hp.mono
    let dep := (depth (C.sampleTree (d:=d) r η hs.2.2.1 hs.2.2.2.1):ℝ)
    let a := 2*(1+dep)*(C.Af*Kf*q*ei+ef)
    have hdep : dep≤C.depthBound := by dsimp only [dep]; exact_mod_cast C.sampleTree_depth (d:=d) r η hs.2.2.1 hs.2.2.2.1
    have hdep0 : 0≤dep := by dsimp [dep]; positivity
    have ha : 0≤a := by dsimp [a]; positivity
    have ha' : a≤C.compilerError C.depthBound Kf q ei ef := by
      unfold compilerError
      dsimp only [a]
      have hh : 0≤C.Af*Kf*q*ei+ef := by positivity
      nlinarith [mul_nonneg hh (sub_nonneg.mpr hdep)]
    apply (sample_error_envelope hs.2.2.1.le hs.2.2.2.1 ha hen).trans
    have he : 20*a+2*en≤C.sampleError C.depthBound Kf q ei ef en := by unfold sampleError; linarith
    exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by positivity : 0≤20*a+2*en) he 2) (sq_nonneg _)
end LogConcaveSampling.OracleCompiler.CircuitParameters

end

end

end OAI
end

section
-- module Solutions.OAIQ048_LC.LogConcave_OraclePrograms_Shape
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
namespace LogConcaveSampling.OracleCompiler
open Filter Quadrature MeanTree
open scoped Topology Classical

lemma source_anchor_radius {a : ℝ} (ha : 0<a) :
    ∀ᶠ d : ℕ in atTop,(d:ℝ)^(-a)≤Real.sqrt (1-(sourceCorrelation a d)^2)/(sourceCorrelation a d) ∧
      Real.sqrt (1-(sourceCorrelation a d)^2)/(sourceCorrelation a d)≤1 := by
  have he := sourceCorrelation_eventually ha
  have ht := (sourceCorrelation_tendsto ha).eventually (lt_mem_nhds (by norm_num : (3/4:ℝ)<1))
  filter_upwards [he,ht,eventually_ge_atTop (1:ℕ)] with d hd hT hd1
  have hd0 : (0:ℝ)<d := by exact_mod_cast hd1
  have hR := Real.rpow_pos_of_pos hd0 (-a)
  have hr : Real.sqrt (1-(sourceCorrelation a d)^2)=(d:ℝ)^(-a) := by
    rw [←hd.2.2,Real.sqrt_sq hR.le]
  rw [hr]
  constructor
  · exact (le_div_iff₀ hd.1).mpr (by nlinarith [mul_le_mul_of_nonneg_left hd.2.1.le hR.le])
  · apply (div_le_one hd.1).mpr
    nlinarith [hd.2.2]

end LogConcaveSampling.OracleCompiler

end

end

section

noncomputable section
namespace LogConcaveSampling.OracleCompiler
open Filter Quadrature
open scoped Topology BigOperators Classical

lemma derivativeBudget_rate (m : ℕ) (a : ℝ) :
    LogPowerRate (fun d : ℕ => ∑j : Fin (m+1),|derivativeWeight (angleNodes m) j/((d:ℝ)^(-a))|) (-a) := by
  apply ((LogPowerRate.inv_power a).const_mul (∑j : Fin (m+1),|derivativeWeight (angleNodes m) j|)).congr
  filter_upwards [eventually_ge_atTop (1:ℕ)] with d hd
  have hp : (0:ℝ)<d := by exact_mod_cast hd
  simp only [div_eq_mul_inv,abs_mul,abs_inv,abs_of_pos (Real.rpow_pos_of_pos hp (-a)),Finset.sum_mul]

theorem actualCoefficient_rate (n m nc : ℕ) {a b : ℝ} (ha : 0<a) (hb : 0<b) :
    LogPowerRate (fun d : ℕ =>
      1+2*fixedCenteringBudget nc*((∑j,|terminalQuadratureWeight (sourceCorrelation a d) ((d:ℝ)^(-b)) n j|)*
        (∑j : Fin (m+1),|derivativeWeight (angleNodes m) j/((d:ℝ)^(-(4*a)))|)*
        (2*fixedProbabilityBudget n)+2)+4*fixedProbabilityBudget n+fixedHarmonicBudget n) (-(b+4*a)) := by
  obtain ⟨D,hD,hDu⟩ := exists_basisDerivative_budget (probabilityNodes (n+1))
  have he := sourceCorrelation_eventually ha
  have hm := sourceMesh_eventually ha hb
  have hq := terminalQuadratureWeight_rate n D (by linarith) hDu a b
    (he.mono (fun _ h => h.1)) (he.mono (fun _ h => h.2.1))
    (he.mono (fun _ h => h.2.2.le)) (hm.mono (fun _ h => h.1)) (hm.mono (fun _ h => h.2))
  have hs := derivativeBudget_rate m (4*a)
  have hr : LogPowerRate (fun d : ℕ =>
      (∑j,|terminalQuadratureWeight (sourceCorrelation a d) ((d:ℝ)^(-b)) n j|)*
        (∑j : Fin (m+1),|derivativeWeight (angleNodes m) j/((d:ℝ)^(-(4*a)))|)) (-(b+4*a)) := by
    simpa only [neg_add] using hq.mul hs
  have hc (c : ℝ) : LogPowerRate (fun _ : ℕ => c) (-(b+4*a)) :=
    (LogPowerRate.const c).mono (by linarith)
  exact (((hc 1).add ((hr.mul_const (2*fixedProbabilityBudget n)).add (hc 2) |>.const_mul
    (2*fixedCenteringBudget nc))).add (hc (4*fixedProbabilityBudget n))).add (hc (fixedHarmonicBudget n))
end LogConcaveSampling.OracleCompiler

end

end

section

noncomputable section
namespace LogConcaveSampling.OracleCompiler
open Filter Quadrature
open scoped Classical Topology

lemma sourceAf_pos (n : ℕ) : 0 < sourceAf n := by
  have hB := (fixedCenteringBudget_spec n).1
  have hP := (fixedProbabilityBudget_spec n).1
  unfold sourceAf
  positivity

lemma SourceShape.A {κ t w : ℝ} {n N d : ℕ} {C : CircuitParameters}
    (h : SourceShape κ t w n N d C) : C.A=sourceA κ t w n d := by
  rw [h.A_eq]
  unfold CircuitParameters.actualA CircuitParameters.quadratureBudget CircuitParameters.derivativeBudget
  rw [h.n_eq,h.m_eq,h.nc_eq,h.T_eq,h.h_eq,h.ψ_eq]
  rfl

lemma SourceShape.Af {κ t w : ℝ} {n N d : ℕ} {C : CircuitParameters}
    (h : SourceShape κ t w n N d C) : C.Af=sourceAf n := by
  rw [h.Af_eq,CircuitParameters.actualAf,h.nc_eq,h.n_eq]
  rfl

lemma SourceShape.depth {κ t w : ℝ} {n N d : ℕ} {C : CircuitParameters}
    (h : SourceShape κ t w n N d C) : C.depthBound=4*(N+1)^2 := by
  simp only [CircuitParameters.depthBound,h.N_eq]

lemma sourceA_rate {κ t w : ℝ} (hκ : 0<κ) (ht : 0<t) (hw : 0<w) (n : ℕ) :
    LogPowerRate (sourceA κ t w n) (-(κ*(w+4*t))) := by
  have h := actualCoefficient_rate n n n (mul_pos hκ ht) (mul_pos hκ hw)
  change LogPowerRate _ (-(κ*(w+4*t)))
  convert h using 1
  · rfl
  · ring

end LogConcaveSampling.OracleCompiler

end

end

section

noncomputable section
namespace LogConcaveSampling.OracleCompiler
open Filter
open scoped Classical Topology

lemma meanFinalSize_rate {κ t b : ℝ} (n : ℕ) {q : ℕ → ℝ}
    (hq : LogPowerRate q (κ*b)) : LogPowerRate (meanFinalSize κ t n q) (κ*(b+t)) := by
  have h := ((LogPowerRate.power (κ*t)).const_mul (1+4*sourceAf n)).mul hq
  convert h using 1
  · rfl
  · ring

lemma sampleFinalSize_rate {κ b : ℝ} (n : ℕ) {q : ℕ → ℝ}
    (hq : LogPowerRate q (κ*b)) : LogPowerRate (sampleFinalSize n q) (κ*b) :=
  hq.const_mul _

lemma internalSize_rate {κ t w b : ℝ} (hκ : 0<κ) (ht : 0<t) (hw : 0<w) (hwt : w<t)
    (n : ℕ) {q : ℕ → ℝ} (hq : LogPowerRate q (κ*b)) :
    LogPowerRate (internalSize κ t w n q) (κ*(b-10*t)) := by
  have hD := LogPowerRate.power (-(κ*t))
  have hA := sourceA_rate hκ ht hw n
  have hR := LogPowerRate.inv_power (κ*t)
  have he := (((hD.const_mul 16).mul hA).mul hR)
  have he' : LogPowerRate (fun d => 16*(d:ℝ)^(κ*t)*sourceA κ t w n d/((d:ℝ)^(-(κ*t))))
      (-(κ*(w+6*t))) := by
    convert he using 1
    · funext d; simp only [neg_neg,div_eq_mul_inv]
    · ring
  have hc := (LogPowerRate.const 1).mono (show -(κ*(w+6*t))≤0 by nlinarith)
  have hi := hq.mul (hc.add he')
  have him := hi.mono (show κ*(b-10*t)≤κ*b+ -(κ*(w+6*t)) by nlinarith)
  exact him

lemma anchorSize_rate {κ t b : ℝ} (hκ : 0≤κ) (ht : 0≤t)
    {q : ℕ → ℝ} (hq : LogPowerRate q (κ*b)) :
    LogPowerRate (anchorSize κ t q) (κ*(b-10*t)) := by
  have h := hq.mul (LogPowerRate.inv_power (κ*t))
  have hm := h.mono (show κ*(b-10*t)≤κ*b+ -(κ*t) by nlinarith)
  change LogPowerRate (fun d => q d/((d:ℝ)^(-(κ*t)))) _
  simpa only [div_eq_mul_inv] using hm

lemma small_coefficient_rate {κ t w b : ℝ} (hκ : 0<κ) (ht : 0<t) (hw : 0<w)
    (hwt : w<t) (hts : t<1/100) (hb : 1/2≤b) (n : ℕ)
    {q : ℕ → ℝ} (hq : LogPowerRate q (κ*b)) :
    LogPowerRate (fun d => sourceA κ t w n d*q d) (κ/3) := by
  exact ((sourceA_rate hκ ht hw n).mul hq).mono (by nlinarith)

lemma parent_intrinsic_rate {κ b p : ℝ} (hκ : 0≤κ) (hb : 1/2≤b)
    {q e : ℕ → ℝ} (hq : LogPowerRate q (κ*b)) (he : LogPowerRate e (κ*(p-1/4))) :
    LogPowerRate (fun d => q d*e d) (κ*p) :=
  (hq.mul he).mono (by nlinarith)

lemma meanError_rate {κ J b p : ℝ} (hκ : 0≤κ) (hb : 1/2≤b) (hp : p≤J)
    (Af H Kf : ℝ) {q es ei ef : ℕ → ℝ} (hq : LogPowerRate q (κ*b))
    (hes : LogPowerRate es (κ*(p-1/4))) (hei : LogPowerRate ei (κ*(p-1/4)))
    (hef : LogPowerRate ef (κ*p)) :
    LogPowerRate (fun d => 2*Af*Kf*H*q d*es d+
      10*(20+16*circuitGrowthConstant^2)*(2*(1+2*H)*(Af*Kf*q d*ei d+ef d))+
      2*(d:ℝ)^(-(κ*J))) (κ*p) := by
  have he := (parent_intrinsic_rate hκ hb hq hei).const_mul (Af*Kf)
  have hc := (he.add hef).const_mul (2*(1+2*H)) |>.const_mul (10*(20+16*circuitGrowthConstant^2))
  have ha := (parent_intrinsic_rate hκ hb hq hes).const_mul (2*Af*Kf*H)
  have hn := ((LogPowerRate.power (κ*J)).mono (show κ*p≤κ*J by nlinarith)).const_mul 2
  apply ((ha.add hc).add hn).congr
  filter_upwards [] with d
  ring

lemma sampleError_rate {κ J b p : ℝ} (hκ : 0≤κ) (hb : 1/2≤b) (hp : p≤J)
    (Af H Kf : ℝ) {q ei ef : ℕ → ℝ} (hq : LogPowerRate q (κ*b))
    (hei : LogPowerRate ei (κ*(p-1/4))) (hef : LogPowerRate ef (κ*p)) :
    LogPowerRate (fun d => 20*(2*(1+2*H)*(Af*Kf*q d*ei d+ef d))+
      2*(d:ℝ)^(-(κ*J))) (κ*p) := by
  have he := (parent_intrinsic_rate hκ hb hq hei).const_mul (Af*Kf)
  have hc := (he.add hef).const_mul (2*(1+2*H)) |>.const_mul 20
  have hn := ((LogPowerRate.power (κ*J)).mono (show κ*p≤κ*J by nlinarith)).const_mul 2
  apply (hc.add hn).congr
  filter_upwards [] with d
  ring
end LogConcaveSampling.OracleCompiler

end

end

section

noncomputable section
namespace LogConcaveSampling.OracleCompiler
open scoped Classical

lemma RoutineLabel.Admissible.b_lower {t K : ℝ} {L : RoutineLabel}
    (h : L.Admissible t K) (ht : 0≤t) : 1/2≤L.b := by
  have he : 0≤40*t*L.p := by positivity [h.1]
  linarith [h.2.2]

lemma RoutineLabel.Admissible.child {t K : ℝ} {P C : RoutineLabel}
    (h : P.Admissible t K) (ht : 0≤t) (hnt : ¬P.terminal)
    (hc : RoutineStep t P C) : C.Admissible t K := by
  have hb := h.b_lower ht
  have hp : P.b<P.p := lt_of_not_ge hnt
  cases hc with
  | meanFinal b p =>
    rcases h with ⟨hp0,hpK,hbp⟩
    dsimp only [RoutineLabel.Admissible] at *
    exact ⟨hp0,hpK,by linarith⟩
  | sampleFinal b p => exact h
  | internal k k' b p =>
    rcases h with ⟨hp0,hpK,hbp⟩
    dsimp only [RoutineLabel.Admissible] at *
    exact ⟨by linarith,by linarith,by nlinarith⟩

end LogConcaveSampling.OracleCompiler

end

end

end OAI
end

section
-- module Solutions.OAIQ048_LC.LogConcave_OraclePrograms_StandaloneCorrect
attribute [-instance] _root_.OAI.LogConcaveSampling.LowerBound.couplingLaw_probability _root_.OAI.LogConcaveSampling.LowerBound.remainingHaar_probability _root_.OAI.LogConcaveSampling.LowerBound.roundRandomLaw_probability _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_invInvariant _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_isHaar _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_probability _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_rightInvariant _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_compactSpace _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_measurableInv _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_measurableMul _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_secondCountable _root_.OAI.LogConcaveSampling.OracleCompiler.topSeedLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
namespace LogConcaveSampling.OracleCompiler
open Filter MeanTree MeasureTheory ProbabilityTheory
open scoped Classical NNReal Topology

variable {d : ℕ}

lemma sourceA_pos (κ t w : ℝ) (n d : ℕ) : 0 < sourceA κ t w n d := by
  have hB := (fixedCenteringBudget_spec n).1
  have hP := (fixedProbabilityBudget_spec n).1
  unfold sourceA
  positivity

lemma childSizes_positive {κ t w : ℝ} (n : ℕ) {q : ℕ → ℝ}
    (hq : ∀ᶠ d : ℕ in atTop,0 < q d) :
    (∀ᶠ d : ℕ in atTop,0 < meanFinalSize κ t n q d) ∧
    (∀ᶠ d : ℕ in atTop,0 < sampleFinalSize n q d) ∧
    (∀ᶠ d : ℕ in atTop,0 < internalSize κ t w n q d) ∧
    (∀ᶠ d : ℕ in atTop,0 < anchorSize κ t q d) := by
  have h : ∀ᶠ d : ℕ in atTop,0 < meanFinalSize κ t n q d ∧ 0 < sampleFinalSize n q d ∧
      0 < internalSize κ t w n q d ∧ 0 < anchorSize κ t q d := by
    filter_upwards [hq,eventually_ge_atTop (1:ℕ)] with d hd hd1
    have hd0 : (0:ℝ)<d := by exact_mod_cast hd1
    have hAf := sourceAf_pos n
    have hA := sourceA_pos κ t w n d
    unfold meanFinalSize sampleFinalSize internalSize anchorSize
    exact ⟨by positivity,by positivity,by positivity,by positivity⟩
  exact ⟨h.mono (fun _ h => h.1),h.mono (fun _ h => h.2.1),h.mono (fun _ h => h.2.2.1),h.mono (fun _ h => h.2.2.2)⟩

lemma uniformAccuracy_terminal {κ t w J K₀ : ℝ} {n N : ℕ} (hκ : 0 < κ)
    (ht : 0 < t) (hts : t≤1/44) (L : RoutineLabel) (hL : L.Admissible t K₀)
    (hterm : L.terminal) : UniformAccuracy κ t w J n N ht hts L := by
  intro q hq hqpos
  have hb := hL.b_lower ht.le
  have hqsmall := hq.eventually_lt_const (show 0 < κ*L.b by positivity [hb])
    (by norm_num : (0:ℝ)<1/2)
  cases L with | mk kind b p =>
    cases kind with
    | mean =>
      let c := 4*(Real.pi+2)
      have hc : 0 < c := by dsimp [c]; positivity [Real.pi_pos]
      refine ⟨1,by norm_num,(fun d => c*q d),(hq.const_mul c).mono (by dsimp [RoutineLabel.terminal] at hterm; nlinarith),?_,?_⟩
      · exact hqpos.mono (fun _ h => mul_pos hc h)
      · filter_upwards [hqsmall] with d hd C hC F lam hF hlam hlam1
        rw [constructRoutine,dite_eq_left hterm]
        exact terminalMean_correct hF ((le_abs_self _).trans hd.le)
    | sample =>
      let c := 2*terminalTransportConstant*(Real.pi+3)
      have hc : 0 < c := by dsimp [c]; positivity [terminalTransportConstant_pos,Real.pi_pos]
      refine ⟨1,by norm_num,(fun d => c*q d),(hq.const_mul c).mono (by dsimp [RoutineLabel.terminal] at hterm; nlinarith),?_,?_⟩
      · exact hqpos.mono (fun _ h => mul_pos hc h)
      · filter_upwards [hqsmall] with d hd C hC F lam hF hlam hlam1
        rw [constructRoutine,dite_eq_left hterm]
        exact terminalSample_correct hF ((le_abs_self _).trans hd.le) _

theorem uniform_routine_accuracy_oai {κ t w J K₀ : ℝ} {n N : ℕ}
    (hκ : 0 < κ) (ht : 0 < t) (hts : t<1/100) (hw : 0 < w) (hwt : w<t)
    (hJK : K₀≤J) (_ : N=numericalLayerCount J)
    (hbudget : ∀ᶠ d : ℕ in atTop,∀C : CircuitParameters,SourceShape κ t w n N d C →
      ∃B : ℕ,(B:ℝ)≤C.D ∧ ∀L : RoutineLabel,L.Admissible t K₀ →
      RoutineBudget B (Real.sqrt (1-C.T^2)/C.T) 1 (constructRoutine d C ht (by linarith) L))
    (hnum : ∀q : ℕ → ℝ,LogPowerRate q (κ*(1/2)) →
      ∀ᶠ d : ℕ in atTop,∀C : CircuitParameters,SourceShape κ t w n N d C →
      ∀{F : Point d → ℝ} {lam : ℝ≥0},∀hF : Primitive F lam,0 < lam → (lam:ℝ)≤1 →
      ∀hql : q d≤1/4,C.MeanNumericalReady hF (q d) ((d:ℝ)^(-(κ*J))) hql ∧
      C.SampleNumericalReady hF (q d) ((d:ℝ)^(-(κ*J)))) :
    ∀L : RoutineLabel,L.Admissible t K₀ → UniformAccuracy κ t w J n N ht (by linarith) L := by
  let hts' : t≤1/44 := by linarith
  apply routine_induction ht hts'
  · intro L hterm hL
    exact uniformAccuracy_terminal hκ ht hts' L hL hterm
  · intro L hnt ih hL q hq hqpos
    have hb := hL.b_lower ht.le
    have hpJ : L.p≤J := hL.2.1.trans hJK
    have hqp := childSizes_positive (κ:=κ) (t:=t) (w:=w) n hqpos
    have hqi := internalSize_rate hκ ht hw hwt n hq
    have hqnum := hnum q (hq.mono (by nlinarith))
    have hsmall := (small_coefficient_rate hκ ht hw hwt hts hb n hq).eventually_lt_const
      (by positivity : 0 < κ/3) (by positivity : (0:ℝ)<1/(2*(2*Real.pi+2)))
    have hqsmall := hq.eventually_lt_const (show 0 < κ*L.b by positivity [hb])
      (by norm_num : (0:ℝ)<1/4)
    have hgeom := sourceCorrelation_eventually (mul_pos hκ ht)
    have hanchor := source_anchor_radius (mul_pos hκ ht)
    let H : ℝ := (4*(N+1)^2:ℕ)
    have hH : 0 ≤ H := Nat.cast_nonneg _
    have hAf : 0 < sourceAf n := sourceAf_pos n
    cases L with | mk kind b p =>
      cases kind with
      | mean =>
        have hLF := RoutineStep.meanFinal (t:=t) b p
        have hLI := RoutineStep.internal (t:=t) RoutineKind.mean RoutineKind.mean b p
        have hLS := RoutineStep.internal (t:=t) RoutineKind.mean RoutineKind.sample b p
        have hAF := hL.child ht.le hnt hLF
        have hAI := hL.child ht.le hnt hLI
        have hAS := hL.child ht.le hnt hLS
        obtain ⟨Kf,hKf,ef,hef,hefpos,hf⟩ := ih _ hLF hAF (meanFinalSize κ t n q) (meanFinalSize_rate n hq) hqp.1
        obtain ⟨Ki,hKi,ei,hei,heipos,hi⟩ := ih _ hLI hAI (internalSize κ t w n q) hqi hqp.2.2.1
        obtain ⟨Ks,hKs,es,hes,hespos,hS⟩ := ih _ hLS hAS (anchorSize κ t q) (anchorSize_rate hκ.le ht.le hq) hqp.2.2.2
        let e := fun d => 2*(sourceAf n*Kf*H*q d)*es d+
          10*(20+16*circuitGrowthConstant^2)*(2*(1+2*H)*(sourceAf n*Kf*q d*ei d+ef d))+
          2*(d:ℝ)^(-(κ*J))
        have he : LogPowerRate e (κ*p) := by
          apply (meanError_rate hκ.le hb hpJ (sourceAf n) H Kf hq hes hei hef).congr
          filter_upwards [] with d
          dsimp only [e]
          ring
        have hepos : ∀ᶠ d : ℕ in atTop,0 < e d := by
          filter_upwards [hqpos,hefpos,heipos,hespos,eventually_ge_atTop (1:ℕ)] with d hqd hfd hid hsd hd1
          have hd0 : (0:ℝ)<d := by exact_mod_cast hd1
          dsimp [e]
          positivity
        refine ⟨2*sourceAf n*H*Kf,by positivity,e,he,hepos,?_⟩
        have hcon := ((small_coefficient_rate hκ ht hw hwt hts hb n hq).const_mul (4*Ki)).eventually_lt_const
          (by positivity : 0 < κ/3) (by norm_num : (0:ℝ)<1)
        have hqs := (hq.mul_const Ks).eventually_lt_const (show 0 < κ*b by positivity [hb]) (by norm_num : (0:ℝ)<1)
        filter_upwards [hf,hi,hS,hbudget,hqnum,hqpos,hefpos,heipos,hespos,hsmall,hcon,hqs,hqsmall,hgeom,hanchor,
          eventually_ge_atTop (1:ℕ)] with d hfd hid hsd hbd hnd hqd hef0 hei0 hes0 hsm hco hqsd hql hdgeom hdanchor hd1
        intro C hC F lam hF hlam hlam1
        have hd0 : (0:ℝ)<d := by exact_mod_cast hd1
        have hR : Real.sqrt (1-C.T^2)=(d:ℝ)^(-(κ*t)) := by
          rw [hC.T_eq,←hdgeom.2.2,Real.sqrt_sq (Real.rpow_pos_of_pos hd0 _).le]
        have hRT : Real.sqrt (1-C.T^2)≤C.T := by
          apply (div_le_one (by linarith [C.T_lower] : 0 < C.T)).mp
          rw [hC.T_eq]
          exact hdanchor.2
        have hη : (d:ℝ)^(-(κ*t))≤Real.sqrt (1-C.T^2)/C.T := by rw [hC.T_eq]; exact hdanchor.1
        have hD : 1≤C.D := by rw [hC.D_eq]; exact Real.one_le_rpow (by exact_mod_cast hd1) (mul_pos hκ ht).le
        have hψ : 0 ≤ C.ψ := by rw [hC.ψ_eq]; positivity
        obtain ⟨B,hBD,hbud⟩ := hbd C hC
        have hB : (B:ℝ)≤C.D^2 := hBD.trans (by nlinarith)
        have hsmall' : 2*C.A*q d*(2*Real.pi+2)≤1 := by
          rw [hC.A]
          have hh := (le_abs_self _).trans hsm.le
          have hp : 0 < 2*(2*Real.pi+2) := by positivity [Real.pi_pos]
          have he := (le_div_iff₀ hp).mp hh
          nlinarith only [he]
        have hcon' : 4*C.A*q d*Ki≤1 := by
          rw [hC.A]
          have he := (le_abs_self _).trans hco.le
          nlinarith only [he]
        have hnmc : C.m=C.n := hC.m_eq.trans hC.n_eq.symm
        have hncc : C.nc=C.n := hC.nc_eq.trans hC.n_eq.symm
        have hNcc : C.Nc=C.N := hC.Nc_eq.trans hC.N_eq.symm
        have hqle : q d≤1/4 := (le_abs_self _).trans hql.le
        have hfc := hfd C hC hF hlam hlam1
        have hic := hid C hC hF hlam hlam1
        have hsc := hsd C hC hF hlam hlam1
        have hf' : MeanCorrect F lam ((1+4*C.Af)*Real.sqrt (1-C.T^2)*q d) Kf (ef d)
            (constructRoutine d C ht hts' ⟨.mean,b+t,p⟩) := by
          simpa only [StandaloneCorrect,meanFinalSize,hC.Af,hR] using hfc
        have hi' : MeanCorrect F lam (q d*(1+16*C.D*C.A/Real.sqrt (1-C.T^2))) Ki (ei d)
            (constructRoutine d C ht hts' ⟨.mean,b-10*t,p-1/4⟩) := by
          simpa only [StandaloneCorrect,internalSize,hC.D_eq,hC.A,hR] using hic
        have hs' : SampleCorrect F lam (q d/Real.sqrt (1-C.T^2)) Ks (es d) ((d:ℝ)^(-(κ*t)))
            (constructRoutine d C ht hts' ⟨.sample,b-10*t,p-1/4⟩) := by
          simpa only [StandaloneCorrect,anchorSize,hR] using hsc
        have hp := C.meanFrom_correct hF hd1 hlam1 hqd.le hqle hRT hη hD hψ hC.A_eq hC.Af_eq
          hKf hKi hKs hef0 hei0.le hes0.le (Real.rpow_pos_of_pos hd0 _).le hsmall' hcon'
          ((le_abs_self _).trans hqsd.le) hnmc hncc hNcc _ _ _ B hB
          (fun s r τ => by cases s; exact hbud _ hAI r τ; exact hbud _ hAF r τ)
          hf' hi' hs' (fun r => (hbud _ hAS r _ (Or.inl rfl)).reserve)
          (hnd C hC hF hlam hlam1 hqle).1
        rw [constructRoutine,dite_eq_right hnt]
        simpa only [StandaloneCorrect,hC.Af,hC.depth,CircuitParameters.meanError,
          CircuitParameters.compilerError,e,H] using hp
      | sample =>
        have hLF := RoutineStep.sampleFinal (t:=t) b p
        have hLI := RoutineStep.internal (t:=t) RoutineKind.sample RoutineKind.mean b p
        have hAF := hL.child ht.le hnt hLF
        have hAI := hL.child ht.le hnt hLI
        obtain ⟨Kf,hKf,ef,hef,hefpos,hf⟩ := ih _ hLF hAF (sampleFinalSize n q) (sampleFinalSize_rate n hq) hqp.2.1
        obtain ⟨Ki,hKi,ei,hei,heipos,hi⟩ := ih _ hLI hAI (internalSize κ t w n q) hqi hqp.2.2.1
        let e := fun d => 20*(2*(1+2*H)*(sourceAf n*Kf*q d*ei d+ef d))+2*(d:ℝ)^(-(κ*J))
        have he : LogPowerRate e (κ*p) := sampleError_rate hκ.le hb hpJ (sourceAf n) H Kf hq hei hef
        have hepos : ∀ᶠ d : ℕ in atTop,0 < e d := by
          filter_upwards [hqpos,hefpos,heipos,eventually_ge_atTop (1:ℕ)] with d hqd hfd hid hd1
          have hd0 : (0:ℝ)<d := by exact_mod_cast hd1
          dsimp [e]
          positivity
        refine ⟨sourceAf n*H*Kf,by positivity,e,he,hepos,?_⟩
        have hcon := ((small_coefficient_rate hκ ht hw hwt hts hb n hq).const_mul (4*Ki)).eventually_lt_const
          (by positivity : 0 < κ/3) (by norm_num : (0:ℝ)<1)
        filter_upwards [hf,hi,hbudget,hqnum,hqpos,hefpos,heipos,hsmall,hcon,hqsmall,hgeom,
          eventually_ge_atTop (1:ℕ)] with d hfd hid hbd hnd hqd hef0 hei0 hsm hco hql hdgeom hd1
        intro C hC F lam hF hlam hlam1
        have hd0 : (0:ℝ)<d := by exact_mod_cast hd1
        have hR : Real.sqrt (1-C.T^2)=(d:ℝ)^(-(κ*t)) := by
          rw [hC.T_eq,←hdgeom.2.2,Real.sqrt_sq (Real.rpow_pos_of_pos hd0 _).le]
        have hD : 1≤C.D := by rw [hC.D_eq]; exact Real.one_le_rpow (by exact_mod_cast hd1) (mul_pos hκ ht).le
        obtain ⟨B,hBD,hbud⟩ := hbd C hC
        have hB : (B:ℝ)≤C.D^2 := hBD.trans (by nlinarith)
        have hsmall' : 2*C.A*q d*(2*Real.pi+2)≤1 := by
          rw [hC.A]
          have hh := (le_abs_self _).trans hsm.le
          have hp : 0 < 2*(2*Real.pi+2) := by positivity [Real.pi_pos]
          have he := (le_div_iff₀ hp).mp hh
          nlinarith only [he]
        have hcon' : 4*C.A*q d*Ki≤1 := by
          rw [hC.A]
          have he := (le_abs_self _).trans hco.le
          nlinarith only [he]
        have hqle : q d≤1/4 := (le_abs_self _).trans hql.le
        have hf' : MeanCorrect F lam ((1+4*C.Af)*q d) Kf (ef d)
            (constructRoutine d C ht hts' ⟨.mean,b,p⟩) := by
          simpa only [StandaloneCorrect,sampleFinalSize,hC.Af] using hfd C hC hF hlam hlam1
        have hi' : MeanCorrect F lam (q d*(1+16*C.D*C.A/Real.sqrt (1-C.T^2))) Ki (ei d)
            (constructRoutine d C ht hts' ⟨.mean,b-10*t,p-1/4⟩) := by
          simpa only [StandaloneCorrect,internalSize,hC.D_eq,hC.A,hR] using hid C hC hF hlam hlam1
        have hp := C.sampleFrom_correct hF hd1 hlam1 hqd.le hqle hR.le hD hC.A_eq hC.Af_eq
          hKf hKi hef0 hei0.le (Real.rpow_pos_of_pos hd0 _).le hsmall' hcon'
          _ _ B hB (fun s r τ => by cases s; exact hbud _ hAI r τ; exact hbud _ hAF r τ)
          hf' hi' (hnd C hC hF hlam hlam1 hqle).2
        rw [constructRoutine,dite_eq_right hnt]
        simpa only [StandaloneCorrect,hC.Af,hC.depth,CircuitParameters.sampleError,
          CircuitParameters.compilerError,e,H] using hp
end LogConcaveSampling.OracleCompiler

end

end

end OAI
end

theorem solution : type_of% @OAI.LogConcaveSampling.OracleCompiler.uniform_routine_accuracy_oai := @OAI.LogConcaveSampling.OracleCompiler.uniform_routine_accuracy_oai
