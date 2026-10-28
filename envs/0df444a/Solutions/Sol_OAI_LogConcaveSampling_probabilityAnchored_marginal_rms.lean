-- Prove2me | solution 1 for OAI.LogConcaveSampling.probabilityAnchored_marginal_rms
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-27T14:02:45.944565+00:00
-- url     : https://prove2.me/submissions/97e55e9a-8c56-4bc0-b8d4-858e0a8042e1

import Mathlib
import Definitions.Def_LogConcaveQuery
import Definitions.Def_OAIQ048L004
import Theorems.Thm_OAI_LogConcaveSampling_TensorSum_matrix_one_energy
import Theorems.Thm_OAI_LogConcaveSampling_TensorSum_matrix_zero_energy

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
-- module Solutions.OAIQ048_LC.LogConcave_Analysis_GrowthInnerGradient
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

lemma growth_inner_gradient {d : ℕ} {H : Point d → ℝ} {K : ℝ≥0}
    (hL : LipschitzWith K (gradient H)) (v : Point d) :
    HasPolynomialGrowth (fun z => inner ℝ (gradient H z) v) := by
  have hh := growth_of_lipschitz (((innerSL ℝ v).lipschitz).comp hL)
  simpa only [Function.comp_def,innerSL_apply_apply,real_inner_comm v] using hh

theorem polynomial_gibbs_ibp {d : ℕ} {H g : Point d → ℝ} {K : ℝ≥0}
    (hH : ContDiff ℝ 1 H) (ht : HasGaussianLowerTail H)
    (hL : LipschitzWith K (gradient H)) (hg : ContDiff ℝ 1 g)
    (hgg : HasPolynomialGrowth g) (v : Point d)
    (hgd : HasPolynomialGrowth (fun z => fderiv ℝ g z v)) :
    (∫ z,fderiv ℝ g z v ∂gibbs H)=
      ∫ z,(inner ℝ (gradient H z) v)*g z ∂gibbs H := by
  have hgc : Continuous (fun z => fderiv ℝ g z v) :=
    (hg.continuous_fderiv (by norm_num)).clm_apply continuous_const
  have hSc : Continuous (fun z => inner ℝ (gradient H z) v) :=
    hL.continuous.inner continuous_const
  have hSg : HasPolynomialGrowth (fun z => (inner ℝ (gradient H z) v)*g z) :=
    Appell.HasGrowth.mul (growth_inner_gradient hL v) hgg
  have hf'g : Integrable (fun z => Real.exp (-H z)*((inner ℝ (gradient H z) v)*g z)) := by
    simpa using integrable_tilted H hH.continuous (hSc.mul hg.continuous) ht hSg 0
  have hfg' : Integrable (fun z => Real.exp (-H z)*fderiv ℝ g z v) := by
    simpa using integrable_tilted H hH.continuous hgc ht hgd 0
  have hfg : Integrable (fun z => Real.exp (-H z)*g z) := by
    simpa using integrable_tilted H hH.continuous hg.continuous ht hgg 0
  have hD (z : Point d) : fderiv ℝ (fun z => Real.exp (-H z)) z v=
      -(Real.exp (-H z)*inner ℝ (gradient H z) v) := by
    change (fderiv ℝ (fun z => Real.exp ((-H) z)) z) v=_
    rw [((hH.differentiable (by norm_num) z).hasFDerivAt.neg.exp).fderiv]
    simp only [smul_apply,neg_apply,smul_eq_mul,←toDual_gradient,
      InnerProductSpace.toDual_apply_apply,Pi.neg_apply]
    ring
  have hh := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable (μ:=volume)
    (f:=fun z => Real.exp (-H z)) (g:=g) (v:=v)
    (by
      convert! hf'g.neg using 1
      all_goals try with_reducible_and_instances rfl
      funext z
      rw [hD]
      change -(Real.exp (-H z)*inner ℝ (gradient H z) v)*g z=
        -(Real.exp (-H z)*(inner ℝ (gradient H z) v*g z))
      ring) hfg' hfg
    (fun z _ => ((hH.differentiable (by norm_num) z).neg).exp)
    (fun z _ => hg.differentiable (by norm_num) z)
  simp only [hD,neg_mul,mul_assoc,integral_neg,neg_neg] at hh
  have hi : Integrable (fun z => Real.exp (-H z)) := by
    simpa using integrable_tilted H hH.continuous continuous_const ht (growth_const (1:ℝ)) 0
  rw [integral_gibbs_vector hH.continuous hi,integral_gibbs_vector hH.continuous hi]
  simp only [smul_eq_mul,hh]
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

lemma directional_neg {d : ℕ} {f : Point d → ℝ} (hf : Differentiable ℝ f) (v : Point d) :
    directional v (fun x => -f x)=fun x => -directional v f x := by
  funext x
  exact congrArg (fun A : Point d →L[ℝ] ℝ => A v) ((hf x).hasFDerivAt.neg).fderiv

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
lemma continuous (hf : PolyC1 f) : Continuous f := hf.smooth.continuous
lemma differentiable (hf : PolyC1 f) : Differentiable ℝ f := hf.smooth.differentiable (by norm_num)
lemma directional_continuous (hf : PolyC1 f) (v : Point d) : Continuous (directional v f) :=
  (hf.smooth.continuous_fderiv (by norm_num)).clm_apply continuous_const
lemma add (hf : PolyC1 f) (hg : PolyC1 g) : PolyC1 (fun x => f x+g x) := by
  refine ⟨hf.smooth.add hg.smooth,Appell.HasGrowth.add hf.growth hg.growth,fun v => ?_⟩
  rw [directional_add hf.differentiable hg.differentiable]
  exact Appell.HasGrowth.add (hf.derivative_growth v) (hg.derivative_growth v)
lemma neg (hf : PolyC1 f) : PolyC1 (fun x => -f x) := by
  refine ⟨hf.smooth.neg,?_,fun v => ?_⟩
  · simpa only [HasPolynomialGrowth,Appell.HasGrowth,neg_one_mul] using Appell.HasGrowth.mul (growth_const (-1:ℝ)) hf.growth
  · rw [directional_neg hf.differentiable]
    simpa only [HasPolynomialGrowth,Appell.HasGrowth,neg_one_mul] using Appell.HasGrowth.mul (growth_const (-1:ℝ)) (hf.derivative_growth v)
lemma mul (hf : PolyC1 f) (hg : PolyC1 g) : PolyC1 (fun x => f x*g x) := by
  refine ⟨hf.smooth.mul hg.smooth,Appell.HasGrowth.mul hf.growth hg.growth,fun v => ?_⟩
  rw [directional_mul hf.differentiable hg.differentiable]
  exact Appell.HasGrowth.add (Appell.HasGrowth.mul (hf.derivative_growth v) hg.growth)
    (Appell.HasGrowth.mul hf.growth (hg.derivative_growth v))
lemma sum {ι : Type*} (s : Finset ι) {f : ι → Point d → ℝ} (hf : ∀i∈s,PolyC1 (f i)) :
    PolyC1 (fun x => ∑i∈s,f i x) := by
  refine ⟨ContDiff.sum (fun i hi => (hf i hi).smooth),
    Appell.HasGrowth.sum s (fun i hi => (hf i hi).growth),fun v => ?_⟩
  rw [directional_sum s (fun i hi => (hf i hi).differentiable)]
  exact Appell.HasGrowth.sum s (fun i hi => (hf i hi).derivative_growth v)
end PolyC1

lemma adjointCoordinate_pairing {d : ℕ} {H f g : Point d → ℝ} {K : ℝ≥0}
    (hH : ContDiff ℝ 1 H) (ht : HasGaussianLowerTail H)
    (hL : LipschitzWith K (gradient H)) (hf : PolyC1 f) (hg : PolyC1 g) (v : Point d) :
    (∫x,adjointCoordinate H v f x*g x ∂gibbs H)=∫x,f x*directional v g x ∂gibbs H := by
  have hs : Continuous (directional v H) := (hH.continuous_fderiv (by norm_num)).clm_apply continuous_const
  have hsg : HasPolynomialGrowth (directional v H) := by
    simpa only [HasPolynomialGrowth,directional_gradient] using growth_inner_gradient hL v
  have hi₁ : Integrable (fun z => directional v f z*g z) (gibbs H) := integrable_polynomial_gibbs hH.continuous ht
    ((hf.directional_continuous v).mul hg.continuous)
    (Appell.HasGrowth.mul (hf.derivative_growth v) hg.growth)
  have hi₂ : Integrable (fun z => f z*directional v g z) (gibbs H) := integrable_polynomial_gibbs hH.continuous ht
    (hf.continuous.mul (hg.directional_continuous v))
    (Appell.HasGrowth.mul hf.growth (hg.derivative_growth v))
  have hi₃ : Integrable (fun z => (directional v H z*f z)*g z) (gibbs H) := integrable_polynomial_gibbs hH.continuous ht
    ((hs.mul hf.continuous).mul hg.continuous)
    (Appell.HasGrowth.mul (Appell.HasGrowth.mul hsg hf.growth) hg.growth)
  have hh := polynomial_gibbs_ibp hH ht hL (hf.mul hg).smooth (hf.mul hg).growth v
    ((hf.mul hg).derivative_growth v)
  change (∫x,directional v (fun x => f x*g x) x ∂gibbs H)=_ at hh
  rw [directional_mul hf.differentiable hg.differentiable,integral_add hi₁ hi₂] at hh
  simp only [←directional_gradient,mul_assoc] at hi₃ ⊢ hh
  change (∫x,(-directional v f x+directional v H x*f x)*g x ∂gibbs H)=_
  simp_rw [add_mul,neg_mul,mul_assoc]
  rw [integral_add (f:=fun z => -(directional v f z*g z)) hi₁.neg hi₃,integral_neg]
  linarith

lemma tensorAdjoint_pairing {d : ℕ} {ι : Type*} [Fintype ι]
    {H g : Point d → ℝ} {V : ι → Point d → ℝ} {K : ℝ≥0}
    (hH : ContDiff ℝ 1 H) (ht : HasGaussianLowerTail H)
    (hL : LipschitzWith K (gradient H)) (hV : ∀i,PolyC1 (V i)) (hg : PolyC1 g)
    (b : ι → Point d) :
    (∫x,tensorAdjoint H b V x*g x ∂gibbs H)=
      ∑i,∫x,V i x*directional (b i) g x ∂gibbs H := by
  have hi (i : ι) : Integrable (fun x => adjointCoordinate H (b i) (V i) x*g x) (gibbs H) := by
    apply integrable_polynomial_gibbs hH.continuous ht
    · exact (((hV i).directional_continuous _).neg.add
        (((hH.continuous_fderiv (by norm_num)).clm_apply continuous_const).mul (hV i).continuous)).mul hg.continuous
    · have hs : HasPolynomialGrowth (directional (b i) H) := by
        simpa only [HasPolynomialGrowth,directional_gradient] using growth_inner_gradient hL (b i)
      exact Appell.HasGrowth.mul
        (Appell.HasGrowth.add (by
          simpa only [HasPolynomialGrowth,Appell.HasGrowth,neg_one_mul] using Appell.HasGrowth.mul (growth_const (-1:ℝ)) ((hV i).derivative_growth (b i)))
          (Appell.HasGrowth.mul hs (hV i).growth)) hg.growth
  simp only [tensorAdjoint,Finset.sum_mul]
  rw [integral_finsetSum Finset.univ (fun i _ => hi i)]
  exact Finset.sum_congr rfl (fun i _ => adjointCoordinate_pairing hH ht hL (hV i) hg (b i))

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
-- module Solutions.OAIQ048_LC.LogConcave_JetEstimates_Lipschitz
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

lemma PolyC1.of_lipschitz {d : ℕ} {f : Point d → ℝ} {K : ℝ≥0}
    (hf : ContDiff ℝ 1 f) (hL : LipschitzWith K f) : PolyC1 f := by
  refine ⟨hf,growth_of_lipschitz hL,fun v => ⟨(K:ℝ)*‖v‖,by positivity,0,fun x => ?_⟩⟩
  have hn := (fderiv ℝ f x).le_opNorm v
  have hb := norm_fderiv_le_of_lipschitz ℝ hL (x₀:=x)
  change ‖(fderiv ℝ f x) v‖ ≤ _
  simp only [pow_zero]
  exact hn.trans ((mul_le_mul_of_nonneg_right hb (norm_nonneg v)).trans (by nlinarith [mul_nonneg K.coe_nonneg (norm_nonneg v)]))

lemma polyC1_directional_potential {d : ℕ} {H : Point d → ℝ} {K : ℝ≥0}
    (hH : ContDiff ℝ (⊤ : ℕ∞) H) (hL : LipschitzWith K (gradient H)) (v : Point d) :
    PolyC1 (directional v H) := by
  apply PolyC1.of_lipschitz ((directional_smooth hH v).of_le (by simp))
  have he : (fun x => (innerSL ℝ v) (gradient H x))=directional v H := by
    funext x
    rw [innerSL_apply_apply,real_inner_comm,directional_gradient]
  simpa only [Function.comp_def,he] using (innerSL ℝ v).lipschitz.comp hL

lemma polyC1_adjointCoordinate {d : ℕ} {H f : Point d → ℝ} {K : ℝ≥0}
    (hH : ContDiff ℝ (⊤ : ℕ∞) H) (hL : LipschitzWith K (gradient H))
    (hf : PolyC1 f) (v : Point d) (hd : PolyC1 (directional v f)) :
    PolyC1 (adjointCoordinate H v f) :=
  hd.neg.add ((polyC1_directional_potential hH hL v).mul hf)

lemma polyC1_tensorAdjoint {d : ℕ} {ι : Type*} [Fintype ι]
    {H : Point d → ℝ} {V : ι → Point d → ℝ} {K : ℝ≥0}
    (hH : ContDiff ℝ (⊤ : ℕ∞) H) (hL : LipschitzWith K (gradient H))
    (b : ι → Point d) (hV : ∀i,PolyC1 (V i)) (hD : ∀i,PolyC1 (directional (b i) (V i))) :
    PolyC1 (tensorAdjoint H b V) :=
  PolyC1.sum Finset.univ (fun i _ => polyC1_adjointCoordinate hH hL (hV i) (b i) (hD i))

end LogConcaveSampling

end UpperProof
end
end
end

end OAI
end

section
-- module Solutions.OAIQ048_LC.LogConcave_Sampling_DirectionalAdjointCoordinate
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

lemma directional_adjointCoordinate {d : ℕ} {H f : Point d → ℝ}
    (hH : ContDiff ℝ (⊤ : ℕ∞) H) (hf : ContDiff ℝ (⊤ : ℕ∞) f) (u v : Point d) :
    directional u (adjointCoordinate H v f)=fun x =>
      adjointCoordinate H v (directional u f) x+directional u (directional v H) x*f x := by
  have hD : Differentiable ℝ (directional v f) := (directional_smooth hf v).differentiable (by simp)
  have hS : Differentiable ℝ (directional v H) := (directional_smooth hH v).differentiable (by simp)
  change directional u (fun x => -directional v f x+directional v H x*f x)=_
  rw [directional_add (f:=fun x => -directional v f x)
    (g:=fun x => directional v H x*f x) hD.neg (hS.mul (hf.differentiable (by simp))),directional_neg hD,
    directional_mul hS (hf.differentiable (by simp)),directional_commute hf u v]
  funext x
  simp only [adjointCoordinate]
  ring

lemma adjointCoordinate_smooth {d : ℕ} {H f : Point d → ℝ}
    (hH : ContDiff ℝ (⊤ : ℕ∞) H) (hf : ContDiff ℝ (⊤ : ℕ∞) f) (v : Point d) :
    ContDiff ℝ (⊤ : ℕ∞) (adjointCoordinate H v f) :=
  (directional_smooth hf v).neg.add ((directional_smooth hH v).mul hf)

lemma directional_tensorAdjoint {d : ℕ} {ι : Type*} [Fintype ι]
    {H : Point d → ℝ} {V : ι → Point d → ℝ}
    (hH : ContDiff ℝ (⊤ : ℕ∞) H) (hV : ∀i,ContDiff ℝ (⊤ : ℕ∞) (V i))
    (b : ι → Point d) (u : Point d) :
    directional u (tensorAdjoint H b V)=fun x =>
      tensorAdjoint H b (fun i => directional u (V i)) x+
      ∑i,directional u (directional (b i) H) x*V i x := by
  unfold tensorAdjoint
  rw [directional_sum Finset.univ
    (fun i _ => (adjointCoordinate_smooth hH (hV i) (b i)).differentiable (by simp))]
  simp_rw [directional_adjointCoordinate hH (hV _)]
  funext x
  exact Finset.sum_add_distrib

end LogConcaveSampling

end UpperProof
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
open scoped RealInnerProductSpace

lemma adjointCoordinate_continuous {d : ℕ} {H f : Point d → ℝ}
    (hH : ContDiff ℝ 1 H) (hf : PolyC1 f) (v : Point d) :
    Continuous (adjointCoordinate H v f) :=
  (hf.directional_continuous v).neg.add
    (((hH.continuous_fderiv (by norm_num)).clm_apply continuous_const).mul hf.continuous)

lemma adjointCoordinate_growth {d : ℕ} {H f : Point d → ℝ} {K : ℝ≥0}
    (hL : LipschitzWith K (gradient H)) (hf : PolyC1 f) (v : Point d) :
    HasPolynomialGrowth (adjointCoordinate H v f) := by
  have hs : HasPolynomialGrowth (directional v H) := by
    simpa only [HasPolynomialGrowth,directional_gradient] using growth_inner_gradient hL v
  exact Appell.HasGrowth.add (by
    simpa only [HasPolynomialGrowth,Appell.HasGrowth,neg_one_mul] using
      Appell.HasGrowth.mul (growth_const (-1:ℝ)) (hf.derivative_growth v))
    (Appell.HasGrowth.mul hs hf.growth)

lemma integrable_adjointCoordinate_mul {d : ℕ} {H f g : Point d → ℝ} {K : ℝ≥0}
    (hH : ContDiff ℝ 1 H) (ht : HasGaussianLowerTail H)
    (hL : LipschitzWith K (gradient H)) (hf : PolyC1 f) (hg : PolyC1 g) (v : Point d) :
    Integrable (fun x => adjointCoordinate H v f x*g x) (gibbs H) :=
  integrable_polynomial_gibbs hH.continuous ht
    ((adjointCoordinate_continuous hH hf v).mul hg.continuous)
    (Appell.HasGrowth.mul (adjointCoordinate_growth hL hf v) hg.growth)

theorem tensorAdjoint_energy_identity {d : ℕ} {ι : Type*} [Fintype ι]
    {H : Point d → ℝ} {V : ι → Point d → ℝ} {K : ℝ≥0}
    (hH : ContDiff ℝ (⊤ : ℕ∞) H) (ht : HasGaussianLowerTail H)
    (hL : LipschitzWith K (gradient H)) (b : ι → Point d)
    (hV : ∀i,ContDiff ℝ (⊤ : ℕ∞) (V i)) (hg : ∀i,PolyC1 (V i))
    (hD : ∀i j,PolyC1 (directional (b i) (V j))) :
    (∫x,(tensorAdjoint H b V x)^2 ∂gibbs H)=
      ∑i,∑j,∫x,directional (b i) (V j) x*directional (b j) (V i) x+
        directional (b i) (directional (b j) H) x*V i x*V j x ∂gibbs H := by
  have hc : ContDiff ℝ 1 H := hH.of_le (by simp)
  have hA := polyC1_tensorAdjoint hH hL b hg (fun i => hD i i)
  have hs (i j : ι) : Integrable (fun x =>
      directional (b i) (directional (b j) H) x*V i x*V j x) (gibbs H) := by
    have hp := polyC1_directional_potential hH hL (b j)
    exact integrable_polynomial_gibbs hc.continuous ht
      (((hp.directional_continuous (b i)).mul (hg i).continuous).mul (hg j).continuous)
      (Appell.HasGrowth.mul (Appell.HasGrowth.mul (hp.derivative_growth (b i)) (hg i).growth) (hg j).growth)
  have hd (i j : ι) : Integrable (fun x => directional (b i) (V j) x*directional (b j) (V i) x) (gibbs H) :=
    integrable_polynomial_gibbs hc.continuous ht
      ((hD i j).continuous.mul (hD j i).continuous)
      (Appell.HasGrowth.mul (hD i j).growth (hD j i).growth)
  have ha (i j : ι) : Integrable (fun x => adjointCoordinate H (b j) (directional (b i) (V j)) x*V i x) (gibbs H) :=
    integrable_adjointCoordinate_mul hc ht hL (hD i j) (hg i) (b j)
  calc
    _ = ∫x,tensorAdjoint H b V x*tensorAdjoint H b V x ∂gibbs H := by simp only [pow_two]
    _ = ∑i,∫x,V i x*directional (b i) (tensorAdjoint H b V) x ∂gibbs H :=
      tensorAdjoint_pairing hc ht hL hg hA b
    _ = _ := by
      apply Finset.sum_congr rfl
      intro i _
      have he : (fun x => V i x*directional (b i) (tensorAdjoint H b V) x)=
          fun x => ∑j,(adjointCoordinate H (b j) (directional (b i) (V j)) x*V i x+
            directional (b i) (directional (b j) H) x*V i x*V j x) := by
        rw [directional_tensorAdjoint hH hV]
        funext x
        simp only [tensorAdjoint,mul_add,Finset.mul_sum,Finset.sum_add_distrib]
        congr 1 <;> apply Finset.sum_congr rfl <;> intro j _ <;> ring
      rw [he,integral_finsetSum Finset.univ
        (f:=fun j x => adjointCoordinate H (b j) (directional (b i) (V j)) x*V i x+
          directional (b i) (directional (b j) H) x*V i x*V j x)
        (fun j _ => (ha i j).add (hs i j))]
      apply Finset.sum_congr rfl
      intro j _
      rw [integral_add (ha i j) (hs i j),integral_add (hd i j) (hs i j),
        adjointCoordinate_pairing hc ht hL (hD i j) (hg i) (b j)]

end LogConcaveSampling
namespace LogConcaveSampling
open scoped RealInnerProductSpace NNReal

lemma matrix_cross_le_squares {ι : Type*} [Fintype ι] (a : ι → ι → ℝ) :
    (∑i,∑j,a i j*a j i) ≤ ∑i,∑j,(a i j)^2 := by
  have hh := Finset.sum_le_sum (s:=Finset.univ) (fun i (_ : i∈(Finset.univ:Finset ι)) =>
    Finset.sum_le_sum (s:=Finset.univ) (fun j (_ : j∈(Finset.univ:Finset ι)) =>
      show 2*(a i j*a j i) ≤ (a i j)^2+(a j i)^2 by nlinarith [sq_nonneg (a i j-a j i)]))
  simp only [Finset.sum_add_distrib,←Finset.mul_sum] at hh
  have he : (∑i,∑j,(a j i)^2)=∑i,∑j,(a i j)^2 := Finset.sum_comm
  rw [he] at hh
  linarith

lemma directional_hessian {d : ℕ} {H : Point d → ℝ}
    (hH : ContDiff ℝ (⊤ : ℕ∞) H) (u v x : Point d) :
    directional u (directional v H) x=inner ℝ (fderiv ℝ (gradient H) x u) v := by
  have hg : ContDiff ℝ (⊤ : ℕ∞) (gradient H) :=
    (InnerProductSpace.toDual ℝ (Point d)).symm.contDiff.comp (hH.fderiv_right (by simp))
  have he : directional v H=(fun z => inner ℝ v (gradient H z)) := by
    funext z
    rw [directional_gradient,real_inner_comm]
  rw [he]
  have hd := (innerSL ℝ v).hasFDerivAt.comp x ((hg.differentiable (by simp) x).hasFDerivAt)
  change (fderiv ℝ (fun z => (innerSL ℝ v) (gradient H z)) x) u=_
  have hde : fderiv ℝ (fun z => (innerSL ℝ v) (gradient H z)) x=
      (innerSL ℝ v).comp (fderiv ℝ (gradient H) x) := hd.fderiv
  rw [hde]
  simp only [ContinuousLinearMap.comp_apply,innerSL_apply_apply,real_inner_comm]

lemma hessian_quadratic_le {d : ℕ} {ι : Type*} [Fintype ι]
    {H : Point d → ℝ} {K : ℝ≥0} (hH : ContDiff ℝ (⊤ : ℕ∞) H)
    (hL : LipschitzWith K (gradient H)) (b : OrthonormalBasis ι ℝ (Point d))
    (a : ι → ℝ) (x : Point d) :
    (∑i,∑j,directional (b i) (directional (b j) H) x*a i*a j) ≤
      (K:ℝ)*∑i,(a i)^2 := by
  classical
  let z : Point d := ∑i,a i • b i
  have hz (i : ι) : inner ℝ (b i) z=a i := by
    simp [z,inner_sum,inner_smul_right,orthonormal_iff_ite.mp b.orthonormal]
  have hn : ‖z‖^2=∑i,(a i)^2 := by simpa only [hz] using (b.sum_sq_inner_right z).symm
  have he : (∑i,∑j,directional (b i) (directional (b j) H) x*a i*a j)=
      inner ℝ (fderiv ℝ (gradient H) x z) z := by
    simp only [z,map_sum,map_smul,directional_hessian hH,sum_inner,inner_smul_left,
      inner_sum,inner_smul_right,starRingEnd_apply,star_trivial,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    have hsym := congrFun (directional_commute hH (b i) (b j)) x
    rw [directional_hessian hH,directional_hessian hH] at hsym
    rw [hsym]
    ring
  rw [he]
  have h₁ := real_inner_le_norm (fderiv ℝ (gradient H) x z) z
  have h₂ := (fderiv ℝ (gradient H) x).le_of_opNorm_le (norm_fderiv_le_of_lipschitz ℝ hL) z
  exact h₁.trans ((mul_le_mul_of_nonneg_right h₂ (norm_nonneg z)).trans_eq (by calc
    (K:ℝ)*‖z‖*‖z‖=(K:ℝ)*‖z‖^2 := by ring
    _ = _ := by rw [hn]))

end LogConcaveSampling
namespace LogConcaveSampling
open MeasureTheory
open scoped RealInnerProductSpace NNReal

lemma integrable_directional_square_sum {d : ℕ} {ι : Type*} [Fintype ι]
    {H : Point d → ℝ} {V : ι → Point d → ℝ} (hH : Continuous H)
    (ht : HasGaussianLowerTail H) (b : ι → Point d)
    (hD : ∀i j,PolyC1 (directional (b i) (V j))) :
    Integrable (fun x => ∑i,∑j,(directional (b i) (V j) x)^2) (gibbs H) := by
  apply integrable_finsetSum Finset.univ
  intro i _
  apply integrable_finsetSum Finset.univ
  intro j _
  exact integrable_polynomial_gibbs hH ht ((hD i j).continuous.pow 2)
    (Appell.HasGrowth.pow (hD i j).growth 2)

lemma integrable_square_sum {d : ℕ} {ι : Type*} [Fintype ι]
    {H : Point d → ℝ} {V : ι → Point d → ℝ} (hH : Continuous H)
    (ht : HasGaussianLowerTail H) (hV : ∀i,PolyC1 (V i)) :
    Integrable (fun x => ∑i,(V i x)^2) (gibbs H) := by
  apply integrable_finsetSum Finset.univ
  intro i _
  exact integrable_polynomial_gibbs hH ht ((hV i).continuous.pow 2)
    (Appell.HasGrowth.pow (hV i).growth 2)

theorem tensorAdjoint_energy_le {d : ℕ} {ι : Type*} [Fintype ι]
    {H : Point d → ℝ} {V : ι → Point d → ℝ} {K : ℝ≥0}
    (hH : ContDiff ℝ (⊤ : ℕ∞) H) (ht : HasGaussianLowerTail H)
    (hL : LipschitzWith K (gradient H)) (b : OrthonormalBasis ι ℝ (Point d))
    (hV : ∀i,ContDiff ℝ (⊤ : ℕ∞) (V i)) (hg : ∀i,PolyC1 (V i))
    (hD : ∀i j,PolyC1 (directional (b i) (V j))) :
    (∫x,(tensorAdjoint H b V x)^2 ∂gibbs H) ≤
      (∫x,∑i,∑j,(directional (b i) (V j) x)^2 ∂gibbs H)+
      (K:ℝ)*(∫x,∑i,(V i x)^2 ∂gibbs H) := by
  let W : ι → ι → Point d → ℝ := fun i j x =>
    directional (b i) (V j) x*directional (b j) (V i) x+
    directional (b i) (directional (b j) H) x*V i x*V j x
  have hi (i j : ι) : Integrable (W i j) (gibbs H) := by
    have hp := polyC1_directional_potential hH hL (b j)
    exact (integrable_polynomial_gibbs hH.continuous ht
      ((hD i j).continuous.mul (hD j i).continuous)
      (Appell.HasGrowth.mul (hD i j).growth (hD j i).growth)).add
      (integrable_polynomial_gibbs hH.continuous ht
        (((hp.directional_continuous (b i)).mul (hg i).continuous).mul (hg j).continuous)
        (Appell.HasGrowth.mul (Appell.HasGrowth.mul (hp.derivative_growth (b i)) (hg i).growth) (hg j).growth))
  have hirow (i : ι) : Integrable (fun x => ∑j,W i j x) (gibbs H) :=
    integrable_finsetSum Finset.univ (fun j _ => hi i j)
  have hiW : Integrable (fun x => ∑i,∑j,W i j x) (gibbs H) :=
    integrable_finsetSum Finset.univ (fun i _ => hirow i)
  have hiD := integrable_directional_square_sum hH.continuous ht b hD
  have hiV := integrable_square_sum hH.continuous ht hg
  calc
    _ = ∑i,∑j,∫x,W i j x ∂gibbs H := tensorAdjoint_energy_identity hH ht hL b hV hg hD
    _ = ∫x,∑i,∑j,W i j x ∂gibbs H := by
      rw [integral_finsetSum Finset.univ (fun i _ => hirow i)]
      apply Finset.sum_congr rfl
      intro i _
      rw [integral_finsetSum Finset.univ (fun j _ => hi i j)]
    _ ≤ ∫x,((∑i,∑j,(directional (b i) (V j) x)^2)+(K:ℝ)*(∑i,(V i x)^2)) ∂gibbs H := by
      apply integral_mono hiW (hiD.add (hiV.const_mul (K:ℝ)))
      intro x
      simp only [W,Finset.sum_add_distrib]
      exact add_le_add (matrix_cross_le_squares (fun i j => directional (b i) (V j) x))
        (hessian_quadratic_le hH hL b (fun i => V i x) x)
    _ = _ := by
      rw [integral_add (f:=fun x => ∑i,∑j,(directional (b i) (V j) x)^2)
        (g:=fun x => (K:ℝ)*(∑i,(V i x)^2)) hiD (hiV.const_mul (K:ℝ)),integral_const_mul]

theorem tensorAdjoint_frobenius_squared {d : ℕ} {ι κ : Type*} [Fintype ι] [Fintype κ]
    {H : Point d → ℝ} {V : κ → ι → Point d → ℝ} {K : ℝ≥0}
    (hH : ContDiff ℝ (⊤ : ℕ∞) H) (ht : HasGaussianLowerTail H)
    (hL : LipschitzWith K (gradient H)) (b : OrthonormalBasis ι ℝ (Point d))
    (hV : ∀a i,ContDiff ℝ (⊤ : ℕ∞) (V a i)) (hg : ∀a i,PolyC1 (V a i))
    (hD : ∀a i j,PolyC1 (directional (b i) (V a j))) :
    (∑a,∫x,(tensorAdjoint H b (V a) x)^2 ∂gibbs H) ≤
      (∑a,∫x,∑i,∑j,(directional (b i) (V a j) x)^2 ∂gibbs H)+
      (K:ℝ)*(∑a,∫x,∑i,(V a i x)^2 ∂gibbs H) := by
  simpa only [Finset.sum_add_distrib,Finset.mul_sum] using
    Finset.sum_le_sum (s:=Finset.univ) (fun a (_ : a∈(Finset.univ:Finset κ)) =>
      tensorAdjoint_energy_le hH ht hL b (hV a) (hg a) (hD a))

theorem tensorAdjoint_frobenius_l2 {d : ℕ} {ι κ : Type*} [Fintype ι] [Fintype κ]
    {H : Point d → ℝ} {V : κ → ι → Point d → ℝ} {K : ℝ≥0}
    (hH : ContDiff ℝ (⊤ : ℕ∞) H) (ht : HasGaussianLowerTail H)
    (hL : LipschitzWith K (gradient H)) (b : OrthonormalBasis ι ℝ (Point d))
    (hV : ∀a i,ContDiff ℝ (⊤ : ℕ∞) (V a i)) (hg : ∀a i,PolyC1 (V a i))
    (hD : ∀a i j,PolyC1 (directional (b i) (V a j))) :
    Real.sqrt (∑a,∫x,(tensorAdjoint H b (V a) x)^2 ∂gibbs H) ≤
      Real.sqrt (∑a,∫x,∑i,∑j,(directional (b i) (V a j) x)^2 ∂gibbs H)+
      Real.sqrt (K:ℝ)*Real.sqrt (∑a,∫x,∑i,(V a i x)^2 ∂gibbs H) := by
  have hh := Real.sqrt_le_sqrt (tensorAdjoint_frobenius_squared hH ht hL b hV hg hD)
  have hs0 (a b : ℝ) : Real.sqrt (a+b) ≤ Real.sqrt a+Real.sqrt b := by
    apply Real.sqrt_le_iff.mpr
    constructor
    · positivity
    · have ha := Real.sq_sqrt' (x:=a)
      have hb := Real.sq_sqrt' (x:=b)
      have hma := le_max_left a 0
      have hmb := le_max_left b 0
      have hp := mul_nonneg (Real.sqrt_nonneg a) (Real.sqrt_nonneg b)
      nlinarith
  have hs := hs0 (∑a,∫x,∑i,∑j,(directional (b i) (V a j) x)^2 ∂gibbs H)
    ((K:ℝ)*(∑a,∫x,∑i,(V a i x)^2 ∂gibbs H))
  rw [Real.sqrt_mul K.coe_nonneg] at hs
  exact hh.trans hs
end LogConcaveSampling
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
-- module Solutions.OAIQ048_LC.LogConcave_JetEstimates_JetRightSlice
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

lemma jointScore_timeSmooth {d : ℕ} {F : Point d → ℝ} {lam : ℝ≥0}
    (hF : Primitive F lam) (x : Point d) {r : ℝ} (hr : 0 ≤ r)
    (hl : (lam:ℝ)*r^2≤1/2) (i : Fin d) : JetCalculus.TimeSmooth (jointScore F x r i) := by
  intro p h0 h1
  exact jointScore_smooth_at hF x hr hl (by nlinarith) i

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
-- module Solutions.OAIQ048_LC.LogConcave_JetEstimates_TensorExpression
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

namespace TensorExpression

lemma eval_polySmooth {d : ℕ} {base : ∀q : ℕ,(Fin (q+2) → Fin d) → Point d → ℝ}
    {H : Point d → ℝ} (hbase : ∀q c,PolySmooth (base q c)) (hH : PolySmooth H)
    {n : ℕ} (A : TensorExpression n) (c : Fin n → Fin d) : PolySmooth (A.eval base H c) := by
  induction A with
  | jet q => exact hbase q c
  | perm e A ih => exact ih _
  | contract hm hn A B ihA ihB =>
    exact PolySmooth.sum Finset.univ (fun z _ => (ihA _).mul (ihB _))
  | adjoint hn A ih => exact hH.tensorAdjoint (fun z => ih _) _

lemma physicalBase_polySmooth {d : ℕ} {F : Point d → ℝ} {lam : ℝ≥0}
    (hF : Primitive F lam) (x : Point d) {r ρ : ℝ} (hr : 0 < r)
    (hlam : 0<lam) (hl : (lam:ℝ)*r^2≤1/2) (hρ0 : 0≤ρ) (hρ1 : ρ<1)
    (q : ℕ) (c : Fin (q+2) → Fin d) : PolySmooth (physicalBase F x r ρ ((lam:ℝ)*r) q c) := by
  exact normalizedTensor_polySmooth hF x hr hlam hl hρ0 hρ1 _ _
    (List.nodup_finRange _) (by simp) (by simp) c

end TensorExpression
end LogConcaveSampling

end

end

section

noncomputable section
namespace LogConcaveSampling
open scoped Classical BigOperators NNReal RealInnerProductSpace

namespace TensorExpression

lemma physicalBase_eq_U {d : ℕ} (F : Point d → ℝ) (x : Point d) (r ρ L : ℝ)
    (hL : L≠0) (q : ℕ) (c : Fin (q+2) → Fin d) (y : Point d) :
    physicalBase F x r ρ L q c y=
      L⁻¹*conditionalU F x r ρ y (JetCalculus.spaceBasis d (c (Fin.last (q+1)))) L
        (fun j : Fin (q+1) => JetCalculus.spaceBasis d (c j.castSucc)) (List.finRange (q+1)) := by
  unfold physicalBase normalizedTensor conditionalU
  rw [List.finRange_succ_last,JetCalculus.jet_append,JetCalculus.jet_map]
  simp only [Fintype.card_fin,Nat.add_sub_cancel,List.length_finRange,Function.comp_def]
  have hv : (fun j : Fin (q+1) => EuclideanSpace.basisFun (Fin d ⊕ Fin d) ℝ
      (conditionalSlotEmbedding d (fun i => decide (i=Fin.last (q+1))) c j.castSucc))=
      fun j : Fin (q+1) => jointPosition d (JetCalculus.spaceBasis d (c j.castSucc)) := by
    funext j
    have he : conditionalSlotEmbedding d (fun i => decide (i=Fin.last (q+1))) c j.castSucc=
        Sum.inl (c j.castSucc) := by simp [conditionalSlotEmbedding]
    rw [he]
    exact (jointPosition_basis _).symm
  rw [hv]
  have hf : conditionalSlotEmbedding d (fun i => decide (i=Fin.last (q+1))) c (Fin.last (q+1))=
      Sum.inr (c (Fin.last (q+1))) := by simp [conditionalSlotEmbedding]
  simp only [JetCalculus.jet,hf]
  rw [←jointField_basis]
  field_simp

lemma jointBase_slice {d : ℕ} (F : Point d → ℝ) (x : Point d) (r ρ L : ℝ)
    (hL : L≠0) (q : ℕ) (c : Fin (q+2) → Fin d) :
    (fun y => jointBase F x r L q c (ρ,y))=physicalBase F x r ρ L q c := by
  funext y
  exact (physicalBase_eq_U F x r ρ L hL q c y).symm

end TensorExpression
end LogConcaveSampling

end

end

section

noncomputable section
namespace LogConcaveSampling
open scoped Classical BigOperators NNReal RealInnerProductSpace

namespace TensorExpression

lemma jointEval_slice {d : ℕ} {F : Point d → ℝ} {lam : ℝ≥0}
    (hF : Primitive F lam) (x : Point d) {r ρ : ℝ} (hr : 0 < r)
    (hlam : 0<lam) (hl : (lam:ℝ)*r^2≤1/2) (hρ0 : 0≤ρ) (hρ1 : ρ<1)
    {n : ℕ} (A : TensorExpression n) (c : Fin n → Fin d) :
    (fun y => A.jointEval F x r ((lam:ℝ)*r) c (ρ,y))=
      A.eval (physicalBase F x r ρ ((lam:ℝ)*r)) (interpolationPotential F x r ρ) c := by
  induction A with
  | jet q => exact jointBase_slice F x r ρ _ (by positivity) q c
  | perm e A ih => exact ih _
  | contract hm hn A B ihA ihB =>
    funext y
    simp only [jointEval,eval]
    apply Finset.sum_congr rfl
    intro z _
    rw [congrFun (ihA _) y,congrFun (ihB _) y]
  | adjoint hn A ih =>
    funext y
    dsimp only [jointEval,eval]
    rw [joint_gadj_slice hF x hr.le hl hρ0 hρ1 (fun z =>
      (A.jointEval_timeSmooth hF x hr hlam hl _ (ρ,y) (by dsimp; linarith) hρ1).differentiableAt (by simp))]
    have he : (fun z y => A.jointEval F x r ((lam:ℝ)*r) (Fin.snoc c z) (ρ,y))=
        fun z => A.eval (physicalBase F x r ρ ((lam:ℝ)*r)) (interpolationPotential F x r ρ) (Fin.snoc c z) := by
      funext z
      exact ih _
    rw [he]

end TensorExpression
end LogConcaveSampling

end

end

end

end OAI
end

section
-- module Solutions.OAIQ048_LC.LogConcave_JetEstimates_TensorTerm
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
open scoped Classical BigOperators NNReal

namespace TensorSum
variable {S T : Type}
lemma relabel_eval {d : ℕ} (A : TensorSum S) (e : S ≃ T) (F : Point d → ℝ)
    (x : Point d) (r L : ℝ) (c : T → Fin d) :
    (A.relabel e).eval F x r L c=A.eval F x r L (c ∘ e) := rfl

end TensorSum
end LogConcaveSampling

end

end

end

end OAI
end

section
-- module Solutions.OAIQ048_LC.LogConcave_JetEstimates_JetMaterial
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
open Filter
open scoped Topology Classical BigOperators NNReal

namespace JetCalculus
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {ι : Type*} [Fintype ι]

lemma dir_congr_nonneg_time {f g : ℝ × E → ℝ} (hf : TimeSmooth f) (hg : TimeSmooth g)
    (he : ∀{t : ℝ},0≤t → t<1 → ∀z,f (t,z)=g (t,z))
    {ρ : ℝ} (h0 : 0≤ρ) (h1 : ρ<1) (v : ℝ × E) (y : E) : dir v f (ρ,y)=dir v g (ρ,y) := by
  have hp {t : ℝ} (ht0 : 0<t) (ht1 : t<1) (z : E) : dir v f (t,z)=dir v g (t,z) := by
    have hh : f=ᶠ[nhds (t,z)]g := by
      have ha := (continuousAt_fst (p:=(t,z))).eventually (Ioo_mem_nhds ht0 ht1)
      filter_upwards [ha] with p hp
      exact he hp.1.le hp.2 p.2
    exact (dir_eventuallyEq hh v).eq_of_nhds
  rcases h0.eq_or_lt with hzero | hpos
  · subst ρ
    have hc : ContinuousAt (fun t : ℝ => (t,y)) 0 := continuousAt_id.prodMk continuousAt_const
    exact eq_zero_of_continuous_pos (f:=fun t => dir v f (t,y)) (g:=fun t => dir v g (t,y))
      ((smooth_dir_at (hf (0,y) (by norm_num) (by norm_num)) v).continuousAt.comp (f:=fun t : ℝ => (t,y)) hc)
      ((smooth_dir_at (hg (0,y) (by norm_num) (by norm_num)) v).continuousAt.comp (f:=fun t : ℝ => (t,y)) hc)
      (fun t ht0 ht1 => hp ht0 ht1 y)
  · exact hp hpos h1 y

lemma mdir_congr_nonneg_time (w : ℝ × E) (b : ι → ℝ × E) (r : ℝ) (M : ι → ℝ × E → ℝ)
    {f g : ℝ × E → ℝ} (hf : TimeSmooth f) (hg : TimeSmooth g)
    (he : ∀{t : ℝ},0≤t → t<1 → ∀z,f (t,z)=g (t,z))
    {ρ : ℝ} (h0 : 0≤ρ) (h1 : ρ<1) (y : E) : mdir w b r M f (ρ,y)=mdir w b r M g (ρ,y) := by
  unfold mdir
  rw [dir_congr_nonneg_time hf hg he h0 h1]
  congr 2
  apply Finset.sum_congr rfl
  intro i _
  rw [dir_congr_nonneg_time hf hg he h0 h1]

lemma materialIter_timeSmooth (w : ℝ × E) (b : ι → ℝ × E) (r : ℝ)
    {M : ι → ℝ × E → ℝ} (hM : ∀i,TimeSmooth (M i)) {f : ℝ × E → ℝ}
    (hf : TimeSmooth f) (n : ℕ) : TimeSmooth (materialIter w b r M n f) := by
  induction n with
  | zero => exact hf
  | succ n ih =>
    intro p h0 h1
    exact smooth_mdir_at w b r (fun i => hM i p h0 h1) (ih p h0 h1)
end JetCalculus

end LogConcaveSampling

end

end

section

noncomputable section
namespace LogConcaveSampling
open scoped Classical BigOperators NNReal RealInnerProductSpace

namespace JetCalculus
lemma gadj_add_at {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {ι : Type*} [Fintype ι] (b : ι → E) (s : ι → E → ℝ) {V W : ι → E → ℝ} {p : E}
    (hV : ∀i,DifferentiableAt ℝ (V i) p) (hW : ∀i,DifferentiableAt ℝ (W i) p) :
    gadj b s (fun i y => V i y+W i y) p=gadj b s V p+gadj b s W p := by
  unfold gadj cadj
  simp_rw [dir_add_at (hV _) (hW _)]
  rw [←Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  ring
end JetCalculus

namespace TensorSum
variable {S : Type} [Fintype S] [Nonempty S]

lemma weightLE_insertOne {A : TensorSum (S ⊕ Unit)} {w : ℕ} (hw : A.weightLE w) :
    A.insertOne.weightLE w := by
  unfold insertOne
  apply weightLE_relabel
  simpa only [zero_add] using weightLE_contract (weightLE_pure TensorAtom.one (by rfl : _≤0)) hw

lemma insertOne_eval {d : ℕ} (A : TensorSum (S ⊕ Unit)) (F : Point d → ℝ)
    (x : Point d) (r L : ℝ) (c : S ⊕ Unit → Fin d) (p : ℝ × Point d) :
    A.insertOne.eval F x r L c p=∑i : Fin d,
      (L⁻¹*jointU F x r L (fun _ : Unit => JetCalculus.spaceBasis d i) [()] (c (Sum.inr ())) p)*
      A.eval F x r L (Sum.elim (fun s => c (Sum.inl s)) (fun _ => i)) p := by
  rw [insertOne,relabel_eval,contract_eval]
  apply Finset.sum_congr rfl
  intro i _
  rw [pure_eval,TensorAtom.one_eval]
  rfl

lemma insertOne_mean {d : ℕ} {F : Point d → ℝ} {lam : ℝ≥0}
    (hF : Primitive F lam) (x : Point d) {r ρ : ℝ} (hr : 0 < r)
    (hlam : 0 < lam) (hl : (lam:ℝ)*r^2≤1/2) (h0 : 0≤ρ) (h1 : ρ<1)
    (A : TensorSum (S ⊕ Unit)) (c : S ⊕ Unit → Fin d) (y : Point d) :
    ∑i : Fin d,JetCalculus.dir (jointSpace i) (jointMean F x r (c (Sum.inr ()))) (ρ,y)*
      A.eval F x r ((lam:ℝ)*r) (Sum.elim (fun s => c (Sum.inl s)) (fun _ => i)) (ρ,y)=
      ((lam:ℝ)*r)*ρ*A.insertOne.eval F x r ((lam:ℝ)*r) c (ρ,y) := by
  rw [insertOne_eval,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [jointMean_direction hF x hr hlam hl h0 h1]
  have hL : (lam:ℝ)*r≠0 := ne_of_gt (mul_pos (by exact_mod_cast hlam) hr)
  field_simp

omit [Fintype S] [Nonempty S] in
lemma outer_timeSmooth {d : ℕ} {F : Point d → ℝ} {lam : ℝ≥0}
    (hF : Primitive F lam) (x : Point d) {r : ℝ} (hr : 0 < r)
    (hlam : 0 < lam) (hl : (lam:ℝ)*r^2≤1/2)
    (A : TensorSum (S ⊕ Unit)) (c : S → Fin d) :
    JetCalculus.TimeSmooth (A.outer F x r ((lam:ℝ)*r) c) := by
  intro p h0 h1
  exact JetCalculus.smooth_gadj_at _ (fun k => jointScore_timeSmooth hF x hr.le hl k p h0 h1)
    (fun k => A.timeSmooth hF x hr hlam hl _ p h0 h1)

omit [Fintype S] [Nonempty S] in
lemma outer_add {d : ℕ} {F : Point d → ℝ} {lam : ℝ≥0}
    (hF : Primitive F lam) (x : Point d) {r ρ : ℝ} (hr : 0 < r)
    (hlam : 0 < lam) (hl : (lam:ℝ)*r^2≤1/2) (h0 : 0≤ρ) (h1 : ρ<1)
    (A B : TensorSum (S ⊕ Unit)) (c : S → Fin d) (y : Point d) :
    (A.add B).outer F x r ((lam:ℝ)*r) c (ρ,y)=
      A.outer F x r ((lam:ℝ)*r) c (ρ,y)+B.outer F x r ((lam:ℝ)*r) c (ρ,y) := by
  have he : (fun k => (A.add B).eval F x r ((lam:ℝ)*r) (Sum.elim c (fun _ => k)))=
      fun k p => A.eval F x r ((lam:ℝ)*r) (Sum.elim c (fun _ => k)) p+
        B.eval F x r ((lam:ℝ)*r) (Sum.elim c (fun _ => k)) p := by
    funext k p
    exact add_eval A B F x r ((lam:ℝ)*r) _ p
  unfold outer
  rw [he]
  exact JetCalculus.gadj_add_at _ _ (fun k =>
    (A.timeSmooth hF x hr hlam hl _ (ρ,y) (by dsimp; linarith) h1).differentiableAt (by simp))
    (fun k => (B.timeSmooth hF x hr hlam hl _ (ρ,y) (by dsimp; linarith) h1).differentiableAt (by simp))

omit [Fintype S] [Nonempty S] in
lemma outer_scale {d : ℕ} {F : Point d → ℝ} {lam : ℝ≥0}
    (hF : Primitive F lam) (x : Point d) {r ρ : ℝ} (hr : 0 < r)
    (hlam : 0 < lam) (hl : (lam:ℝ)*r^2≤1/2) (h0 : 0≤ρ) (h1 : ρ<1)
    (A : TensorSum (S ⊕ Unit)) (n : ℕ) (P : Polynomial ℝ) (c : S → Fin d) (y : Point d) :
    (A.scale n P).outer F x r ((lam:ℝ)*r) c (ρ,y)=
      (r*((lam:ℝ)*r))^n*P.eval ρ*A.outer F x r ((lam:ℝ)*r) c (ρ,y) := by
  have hA k := A.timeSmooth hF x hr hlam hl (Sum.elim c (fun _ => k)) (ρ,y) (by dsimp; linarith) h1
  have he : (fun k => (A.scale n P).eval F x r ((lam:ℝ)*r) (Sum.elim c (fun _ => k)))=
      fun k p => (r*((lam:ℝ)*r))^n*(P.eval p.1*A.eval F x r ((lam:ℝ)*r) (Sum.elim c (fun _ => k)) p) := by
    funext k p
    rw [scale_eval]
    ring
  unfold outer
  rw [he,JetCalculus.gadj_scalar_at _ _ (fun k =>
    (((polynomialTime_smooth P).contDiffAt).mul (hA k)).differentiableAt (by simp)),
    JetCalculus.gadj_time_at _ _ (fun k => (hA k).differentiableAt (by simp))]
  ring

theorem outer_material {d : ℕ} {F : Point d → ℝ} {lam : ℝ≥0}
    (hF : Primitive F lam) (x : Point d) {r ρ : ℝ} (hr : 0 < r)
    (hlam : 0 < lam) (hl : (lam:ℝ)*r^2≤1/2) (h0 : 0≤ρ) (h1 : ρ<1)
    {A B : TensorSum (S ⊕ Unit)} (hAB : A.HasMaterial B) (c : S → Fin d) (y : Point d) :
    JetCalculus.mdir (1,0) jointSpace r (jointMean F x r) (A.outer F x r ((lam:ℝ)*r) c) (ρ,y)=
      (B.add (A.insertOne.scale 1 Polynomial.X)).outer F x r ((lam:ℝ)*r) c (ρ,y) := by
  let L : ℝ := (lam:ℝ)*r
  let V : Fin d → ℝ × Point d → ℝ := fun k => A.eval F x r L (Sum.elim c (fun _ => k))
  let W : Fin d → ℝ × Point d → ℝ := fun k => B.eval F x r L (Sum.elim c (fun _ => k))
  have hV (k : Fin d) := A.timeSmooth hF x hr hlam hl (Sum.elim c (fun _ => k)) (ρ,y) (by dsimp; linarith) h1
  have hW (k : Fin d) := B.timeSmooth hF x hr hlam hl (Sum.elim c (fun _ => k)) (ρ,y) (by dsimp; linarith) h1
  have hp : ρ^2<1 := by nlinarith
  have hM := jointMean_smooth_at hF x hr.le hl (p:=(ρ,y)) hp
  have hda : JetCalculus.gadj jointSpace (jointScore F x r)
      (fun k => JetCalculus.mdir (1,0) jointSpace r (jointMean F x r) (V k)) (ρ,y)=
      JetCalculus.gadj jointSpace (jointScore F x r) W (ρ,y) := by
    apply JetCalculus.gadj_slice_congr_at _
    · intro k; exact (JetCalculus.smooth_mdir_at _ _ _ hM (hV k)).differentiableAt (by simp)
    · intro k; exact (hW k).differentiableAt (by simp)
    · intro k z; exact hAB hF x hr hlam hl h0 h1 _ z
  let I : Fin d → ℝ × Point d → ℝ := fun k => A.insertOne.eval F x r L (Sum.elim c (fun _ => k))
  have hI (k : Fin d) := A.insertOne.timeSmooth hF x hr hlam hl (Sum.elim c (fun _ => k)) (ρ,y) (by dsimp; linarith) h1
  have hdi : JetCalculus.gadj jointSpace (jointScore F x r)
      (fun k p => ∑i,JetCalculus.dir (jointSpace i) (jointMean F x r k) p*V i p) (ρ,y)=
      L*ρ*JetCalculus.gadj jointSpace (jointScore F x r) I (ρ,y) := by
    rw [←JetCalculus.gadj_scalar_at _ _ (fun k => (hI k).differentiableAt (by simp)) (L*ρ)]
    apply JetCalculus.gadj_slice_congr_at _
    · intro k; exact (ContDiffAt.sum (fun i _ =>
        (JetCalculus.smooth_dir_at (hM k) _).mul (hV i))).differentiableAt (by simp)
    · intro k; exact (contDiffAt_const.mul (hI k)).differentiableAt (by simp)
    · intro k z
      simpa only [Sum.elim_inl,Sum.elim_inr] using
        insertOne_mean hF x hr hlam hl h0 h1 A (Sum.elim c (fun _ => k)) z
  change JetCalculus.mdir (1,0) jointSpace r (jointMean F x r)
    (JetCalculus.gadj jointSpace (jointScore F x r) V) (ρ,y)=_
  rw [physical_material_adjoint_nonneg hF x hr hlam hl h0 h1 hV,hda,hdi,
    outer_add hF x hr hlam hl h0 h1,outer_scale hF x hr hlam hl h0 h1]
  simp only [pow_one,Polynomial.eval_X]
  change B.outer F x r L c (ρ,y)+r*(L*ρ*A.insertOne.outer F x r L c (ρ,y))=_
  dsimp only [L]
  ring
end TensorSum
end LogConcaveSampling

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

namespace TensorAtom
variable {S : Type} [Fintype S]

omit [Fintype S] in
lemma slice_polySmooth {d : ℕ} {F : Point d → ℝ} {lam : ℝ≥0}
    (hF : Primitive F lam) (x : Point d) {r ρ : ℝ} (hr : 0 < r)
    (hlam : 0 < lam) (hl : (lam:ℝ)*r^2≤1/2) (h0 : 0≤ρ) (h1 : ρ<1)
    (A : TensorAtom S) (c : S → Fin d) : PolySmooth (A.slice F x r ρ ((lam:ℝ)*r) c) := by
  change PolySmooth (fun y => A.expression.jointEval F x r ((lam:ℝ)*r) (c ∘ A.labels) (ρ,y))
  rw [TensorExpression.jointEval_slice hF x hr hlam hl h0 h1]
  exact TensorExpression.eval_polySmooth (physicalBase_polySmooth hF x hr hlam hl h0 h1)
    (interpolationPotential_polySmooth hF x hr hlam hl h0 h1) A.expression _

end TensorAtom

namespace TensorSum
variable {S : Type} [Fintype S]

omit [Fintype S] in
lemma slice_polySmooth {d : ℕ} {F : Point d → ℝ} {lam : ℝ≥0}
    (hF : Primitive F lam) (x : Point d) {r ρ : ℝ} (hr : 0 < r)
    (hlam : 0 < lam) (hl : (lam:ℝ)*r^2≤1/2) (h0 : 0≤ρ) (h1 : ρ<1)
    (A : TensorSum S) (c : S → Fin d) : PolySmooth (A.slice F x r ρ ((lam:ℝ)*r) c) :=
by
  change PolySmooth (fun z => ∑i, ((r*((lam:ℝ)*r))^(A.term i).power*
    (A.term i).coefficient.eval ρ)*(A.term i).atom.slice F x r ρ ((lam:ℝ)*r) c z)
  exact PolySmooth.sum Finset.univ (fun i _ =>
    (PolySmooth.const _).mul ((A.term i).atom.slice_polySmooth hF x hr hlam hl h0 h1 c))

end TensorSum
end LogConcaveSampling

end

end

end

end OAI
end

section
-- module Solutions.OAIQ048_LC.LogConcave_Analysis_InterpolationHessianBudget
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
open scoped Classical BigOperators NNReal ENNReal RealInnerProductSpace

lemma interpolationPotential_gradient_uniform {d : ℕ} {F : Point d → ℝ} {lam : ℝ≥0}
    (hF : Primitive F lam) (x : Point d) {r ρ : ℝ} (hr : 0 ≤ r)
    (hl : (lam:ℝ)*r^2≤1/2) (h0 : 0≤ρ) (h1 : ρ<1) :
    LipschitzWith interpolationHessianBudget (gradient (interpolationPotential F x r ρ)) := by
  apply (interpolationPotential_gradient_lipschitz hF x hr hl h0 h1).weaken
  apply NNReal.coe_le_coe.mp
  change 1+‖r*ρ‖*((Real.pi^2/2)*ρ*((lam:ℝ)*r))≤1+Real.pi^2/4
  rw [Real.norm_eq_abs,abs_of_nonneg (mul_nonneg hr h0)]
  have hρ : ρ^2≤1 := by nlinarith
  have hh : (lam:ℝ)*r^2*ρ^2≤1/2 :=
    (mul_le_mul_of_nonneg_left hρ (by positivity)).trans (by simpa using hl)
  nlinarith [mul_le_mul_of_nonneg_left hh (sq_nonneg Real.pi)]

lemma sqrt_scaled_square (d : ℕ) {B R : ℝ} (hB : 0≤B) (hR : 0≤R) (n : ℕ) :
    Real.sqrt ((d:ℝ)*B^2*R^(2*n))=Real.sqrt (d:ℝ)*B*R^n := by
  have he : (d:ℝ)*B^2*R^(2*n)=(d:ℝ)*(B*R^n)^2 := by
    rw [mul_pow,←pow_mul]
    ring
  rw [he,Real.sqrt_mul (Nat.cast_nonneg d),Real.sqrt_sq (mul_nonneg hB (pow_nonneg hR _)),mul_assoc]

namespace TensorSum
lemma outer_slice {d : ℕ} {F : Point d → ℝ} {lam : ℝ≥0}
    (hF : Primitive F lam) (x : Point d) {r ρ : ℝ} (hr : 0 < r)
    (hlam : 0 < lam) (hl : (lam:ℝ)*r^2≤1/2) (h0 : 0≤ρ) (h1 : ρ<1)
    (A : TensorSum (Unit ⊕ Unit)) (a : Fin d) (y : Point d) :
    A.outer F x r ((lam:ℝ)*r) (fun _ => a) (ρ,y)=
      tensorAdjoint (interpolationPotential F x r ρ) (EuclideanSpace.basisFun (Fin d) ℝ)
        (fun j => A.slice F x r ρ ((lam:ℝ)*r) (Sum.elim (fun _ => a) (fun _ => j))) y := by
  exact joint_gadj_slice hF x hr.le hl h0 h1 (fun k =>
    (A.timeSmooth hF x hr hlam hl _ (ρ,y) (by dsimp; linarith) h1).differentiableAt (by simp))

theorem outer_l2 {d : ℕ} {F : Point d → ℝ} {lam : ℝ≥0}
    (hF : Primitive F lam) (x : Point d) {r ρ : ℝ} (hr : 0 < r)
    (hlam : 0 < lam) (hl : (lam:ℝ)*r^2≤1/2) (h0 : 0≤ρ) (h1 : ρ<1)
    (hd : 1≤d) (A : TensorSum (Unit ⊕ Unit)) {w : ℕ} (hw : A.weightLE w) :
    Real.sqrt (∑a : Fin d,∫y,(A.outer F x r ((lam:ℝ)*r) (fun _ => a) (ρ,y))^2 ∂interpolationLaw F x r ρ)≤
      Real.sqrt (d:ℝ)*((A.momentBudget d 1 2).toReal+
        Real.sqrt (interpolationHessianBudget:ℝ)*(A.momentBudget d 0 2).toReal)*
        ((Real.sqrt (1-ρ^2))⁻¹)^(w+1) := by
  let V : Fin d → Fin d → Point d → ℝ := fun a j =>
    A.slice F x r ρ ((lam:ℝ)*r) (Sum.elim (fun _ => a) (fun _ => j))
  have hV a j := A.slice_polySmooth hF x hr hlam hl h0 h1 (Sum.elim (fun _ => a) (fun _ => j))
  have hE := tensorAdjoint_frobenius_l2
    (interpolationPotential_smooth hF x hr.le hl h0 h1)
    (interpolationPotential_lowerTail hF x hr.le (by linarith) h0 h1)
    (interpolationPotential_gradient_uniform hF x hr.le hl h0 h1)
    (EuclideanSpace.basisFun (Fin d) ℝ) (fun a j => (hV a j).smooth)
    (fun a j => (hV a j).polyC1) (fun a i j => ((hV a j).directional _).polyC1)
  have hm := interpolationLaw_eq_gibbs hF x hr.le (by linarith) (by nlinarith : ρ^2<1)
  rw [←hm] at hE
  simp_rw [←A.outer_slice hF x hr hlam hl h0 h1] at hE
  let R := (Real.sqrt (1-ρ^2))⁻¹
  have hR0 : 0≤R := by dsimp [R]; positivity
  have hR1 : 1≤R := by
    apply (one_le_inv₀ (Real.sqrt_pos.mpr (by nlinarith))).mpr
    exact Real.sqrt_le_one.mpr (by nlinarith [sq_nonneg ρ])
  have he1 := Real.sqrt_le_sqrt (A.matrix_one_energy hF x hr hlam hl h0 h1 hd hw)
  have he0 := Real.sqrt_le_sqrt (A.matrix_zero_energy hF x hr hlam hl h0 h1 hd hw)
  rw [sqrt_scaled_square d ENNReal.toReal_nonneg hR0 (w+1)] at he1
  rw [sqrt_scaled_square d ENNReal.toReal_nonneg hR0 w] at he0
  have hp := pow_le_pow_right₀ hR1 (Nat.le_succ w)
  have hlast : Real.sqrt (d:ℝ)*(A.momentBudget d 0 2).toReal*R^w≤
      Real.sqrt (d:ℝ)*(A.momentBudget d 0 2).toReal*R^(w+1) :=
    mul_le_mul_of_nonneg_left hp (by positivity)
  apply (hE.trans (add_le_add he1 (mul_le_mul_of_nonneg_left (he0.trans hlast) (Real.sqrt_nonneg _)))).trans_eq
  dsimp only [R]
  ring
end TensorSum
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
-- module Solutions.OAIQ048_LC.LogConcave_Sampling_JointMeanMaterial
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

lemma joint_mean_material {d : ℕ} {F : Point d → ℝ} {lam : ℝ≥0}
    (hF : Primitive F lam) (x : Point d) {r ρ : ℝ} (hr : 0 < r)
    (hlam : 0 < lam) (hl : (lam:ℝ)*r^2≤1/2) (h0 : 0≤ρ) (h1 : ρ<1)
    (i : Fin d) (y : Point d) :
    JetCalculus.mdir (1,0) jointSpace r (jointMean F x r) (jointMean F x r i) (ρ,y)=
      JetCalculus.gadj jointSpace (jointScore F x r) (fun k => jointU F x r ((lam:ℝ)*r)
        (fun _ : Unit => JetCalculus.spaceBasis d k) [()] i) (ρ,y) := by
  have hm := jointMean_timeSmooth hF x hr.le hl i (ρ,y) (by dsimp; linarith) h1
  have ht := joint_mdir_eq_material F x r (hm.differentiableAt (by simp))
  change JetCalculus.mdir (1,0) jointSpace r (jointMean F x r) (jointMean F x r i) (ρ,y)=_ at ht
  rw [ht]
  change materialScalar F x r (fun t y => inner ℝ (EuclideanSpace.basisFun (Fin d) ℝ i)
    (conditionalFieldMean F x r t y)) ρ y=_
  rw [material_conditionalFieldMean hF x hr hlam hl h0 h1]
  rw [joint_gadj_slice hF x hr.le hl h0 h1 (fun k =>
    (jointU_timeSmooth hF x hr hlam hl (fun _ : Unit => JetCalculus.spaceBasis d k) [()]
      (by simp) i (ρ,y) (by dsimp; linarith) h1).differentiableAt (by simp))]
  rfl

lemma joint_mean_outer {d : ℕ} {F : Point d → ℝ} {lam : ℝ≥0}
    (hF : Primitive F lam) (x : Point d) {r ρ : ℝ} (hr : 0 < r)
    (hlam : 0 < lam) (hl : (lam:ℝ)*r^2≤1/2) (h0 : 0≤ρ) (h1 : ρ<1)
    (i : Fin d) (y : Point d) :
    JetCalculus.mdir (1,0) jointSpace r (jointMean F x r) (jointMean F x r i) (ρ,y)=
      ((lam:ℝ)*r)*(TensorSum.pure TensorAtom.one).outer F x r ((lam:ℝ)*r) (fun _ => i) (ρ,y) := by
  rw [joint_mean_material hF x hr hlam hl h0 h1]
  have hL : (lam:ℝ)*r≠0 := ne_of_gt (mul_pos (by exact_mod_cast hlam) hr)
  have he : (fun k => jointU F x r ((lam:ℝ)*r)
      (fun _ : Unit => JetCalculus.spaceBasis d k) [()] i)=
      fun k p => ((lam:ℝ)*r)*(TensorSum.pure TensorAtom.one).eval F x r ((lam:ℝ)*r)
        (Sum.elim (fun _ => i) (fun _ => k)) p := by
    funext k p
    rw [TensorSum.pure_eval,TensorAtom.one_eval]
    dsimp only [Sum.elim_inl,Sum.elim_inr]
    field_simp
  rw [he,JetCalculus.gadj_scalar_at _ _ (fun k =>
    ((TensorSum.pure TensorAtom.one).timeSmooth hF x hr hlam hl _ (ρ,y)
      (by dsimp; linarith) h1).differentiableAt (by simp))]
  rfl

theorem mean_material_representation (n : ℕ) :
    ∃A : TensorSum (Unit ⊕ Unit), A.weightLE (2*n) ∧
      ∀{d : ℕ} {F : Point d → ℝ} {lam : ℝ≥0}, Primitive F lam →
        ∀(x : Point d) {r ρ : ℝ},0 < r → 0 < lam → (lam:ℝ)*r^2≤1/2 → 0≤ρ → ρ<1 →
          ∀(i : Fin d) (y : Point d),
            JetCalculus.materialIter (1,0) jointSpace r (jointMean F x r) (n+1) (jointMean F x r i) (ρ,y)=
              ((lam:ℝ)*r)*A.outer F x r ((lam:ℝ)*r) (fun _ => i) (ρ,y) := by
  induction n with
  | zero =>
    refine ⟨TensorSum.pure TensorAtom.one,TensorSum.weightLE_pure _ (by rfl),?_⟩
    intro d F lam hF x r ρ hr hlam hl h0 h1 i y
    exact joint_mean_outer hF x hr hlam hl h0 h1 i y
  | succ n ih =>
    obtain ⟨A,hA,he⟩ := ih
    obtain ⟨B,hB,hAB⟩ := A.hasMaterial hA
    refine ⟨B.add (A.insertOne.scale 1 Polynomial.X),?_,?_⟩
    · apply TensorSum.weightLE_add
      · convert hB using 1; omega
      · exact TensorSum.weightLE_mono (TensorSum.weightLE_scale
          (TensorSum.weightLE_insertOne hA) _ _) (by omega)
    · intro d F lam hF x r ρ hr hlam hl h0 h1 i y
      have ho := A.outer_timeSmooth hF x hr hlam hl (fun _ : Unit => i)
      have hs : JetCalculus.TimeSmooth (fun p => ((lam:ℝ)*r)*A.outer F x r ((lam:ℝ)*r) (fun _ => i) p) :=
        fun p hp0 hp1 => contDiffAt_const.mul (ho p hp0 hp1)
      change JetCalculus.mdir (1,0) jointSpace r (jointMean F x r)
        (JetCalculus.materialIter (1,0) jointSpace r (jointMean F x r) (n+1) (jointMean F x r i)) (ρ,y)=_
      rw [JetCalculus.mdir_congr_nonneg_time (1,0) jointSpace r (jointMean F x r)
        (JetCalculus.materialIter_timeSmooth _ _ _ (jointMean_timeSmooth hF x hr.le hl)
          (jointMean_timeSmooth hF x hr.le hl i) (n+1)) hs
        (fun ht0 ht1 z => he hF x hr hlam hl ht0 ht1 i z) h0 h1 y,
        JetCalculus.mdir_const_mul_at _ _ _ _ ((ho (ρ,y) (by dsimp; linarith) h1).differentiableAt (by simp)),
        TensorSum.outer_material hF x hr hlam hl h0 h1 hAB]
end LogConcaveSampling

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
open MeasureTheory
open scoped Classical BigOperators NNReal RealInnerProductSpace

theorem mean_material_l2 (n : ℕ) :
    ∃A : TensorSum (Unit ⊕ Unit),∀{d : ℕ} {F : Point d → ℝ} {lam : ℝ≥0},
      Primitive F lam → ∀(x : Point d) {r ρ : ℝ},0 < r → 0 < lam →
        (lam:ℝ)*r^2≤1/2 → 0≤ρ → ρ<1 → 1≤d →
        Real.sqrt (∑i : Fin d,∫y,
          (JetCalculus.materialIter (1,0) jointSpace r (jointMean F x r) (n+1)
            (jointMean F x r i) (ρ,y))^2 ∂interpolationLaw F x r ρ)≤
          ((lam:ℝ)*r)*Real.sqrt (d:ℝ)*((A.momentBudget d 1 2).toReal+
            Real.sqrt (interpolationHessianBudget:ℝ)*(A.momentBudget d 0 2).toReal)*
            ((Real.sqrt (1-ρ^2))⁻¹)^(2*n+2) := by
  obtain ⟨A,hw,he⟩ := mean_material_representation n
  refine ⟨A,?_⟩
  intro d F lam hF x r ρ hr hlam hl h0 h1 hd
  simp_rw [he hF x hr hlam hl h0 h1,mul_pow,integral_const_mul,←Finset.mul_sum]
  rw [←mul_pow,Real.sqrt_mul (sq_nonneg _),Real.sqrt_sq (mul_nonneg lam.coe_nonneg hr.le)]
  have hE := A.outer_l2 hF x hr hlam hl h0 h1 hd hw
  let R := (Real.sqrt (1-ρ^2))⁻¹
  have hR : 1≤R := by
    apply (one_le_inv₀ (Real.sqrt_pos.mpr (by nlinarith))).mpr
    exact Real.sqrt_le_one.mpr (by nlinarith [sq_nonneg ρ])
  have hp : R^(2*n+1)≤R^(2*n+2) := pow_le_pow_right₀ hR (by omega)
  apply (mul_le_mul_of_nonneg_left hE (mul_nonneg lam.coe_nonneg hr.le)).trans
  have hb : 0≤(lam:ℝ)*r*Real.sqrt (d:ℝ)*((A.momentBudget d 1 2).toReal+
      Real.sqrt (interpolationHessianBudget:ℝ)*(A.momentBudget d 0 2).toReal) := by positivity
  simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hp hb
end LogConcaveSampling

end

end

section

noncomputable section
namespace LogConcaveSampling
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators NNReal RealInnerProductSpace

lemma joint_material_direction {d : ℕ} (F : Point d → ℝ) (x : Point d) (r : ℝ)
    {A : ℝ × Point d → ℝ} {ρ : ℝ} {y : Point d}
    (hA : DifferentiableAt ℝ A (ρ,y)) :
    (fderiv ℝ A (ρ,y)) (1,-r • conditionalFieldMean F x r ρ y)=
      JetCalculus.mdir (1,0) jointSpace r (jointMean F x r) A (ρ,y) := by
  have ht := joint_mdir_eq_material F x r hA
  change JetCalculus.mdir (1,0) jointSpace r (jointMean F x r) A (ρ,y)=_ at ht
  rw [ht]
  unfold materialScalar
  rw [JetCalculus.dir_left_slice_at hA]
  change _=JetCalculus.dir (1,0) A (ρ,y)-r*JetCalculus.dir (conditionalFieldMean F x r ρ y)
    (fun z => A (ρ,z)) y
  rw [JetCalculus.dir_right_slice_at hA]
  unfold JetCalculus.dir
  have he : ((1:ℝ),-r • conditionalFieldMean F x r ρ y)=
      (1,0)+(-r) • (0,conditionalFieldMean F x r ρ y) := by simp
  rw [he,map_add,map_smul]
  simp only [smul_eq_mul,neg_mul]
  ring

lemma fullProbabilityFlow_deriv {d : ℕ} {F : Point d → ℝ} {lam : ℝ≥0}
    (hF : Primitive F lam) (x z : Point d) {r ρ : ℝ} (hr : 0 ≤ r)
    (hl : (lam:ℝ)*r^2≤1/2) (h0 : 0≤ρ) (h1 : ρ<1) :
    HasDerivWithinAt (fun t => fullProbabilityFlow hF x hr hl t z)
      (-r • conditionalFieldMean F x r ρ (fullProbabilityFlow hF x hr hl ρ z)) (Icc 0 1) ρ := by
  have hh := GlobalODE.flow_deriv (a:=0) (b:=1)
    (fun t _ => fullProbabilityVelocity_lipschitz hF x hr hl t)
    (fullProbabilityVelocity_continuous hF x hr hl) ⟨0,le_rfl,by norm_num⟩ z ρ ⟨h0,h1.le⟩
  rw [fullProbabilityVelocity_eq F x r h0 h1] at hh
  exact hh

lemma material_path_chain {d : ℕ} {F : Point d → ℝ} {lam : ℝ≥0}
    (hF : Primitive F lam) (x z : Point d) {r ρ : ℝ} (hr : 0 ≤ r)
    (hl : (lam:ℝ)*r^2≤1/2) (h0 : 0≤ρ) (h1 : ρ<1)
    {A : ℝ × Point d → ℝ} (hA : DifferentiableAt ℝ A (ρ,fullProbabilityFlow hF x hr hl ρ z)) :
    HasDerivWithinAt (fun t => A (t,fullProbabilityFlow hF x hr hl t z))
      (JetCalculus.mdir (1,0) jointSpace r (jointMean F x r) A
        (ρ,fullProbabilityFlow hF x hr hl ρ z)) (Icc 0 1) ρ := by
  have hh := hA.hasFDerivAt.comp_hasDerivWithinAt ρ
    ((hasDerivWithinAt_id ρ (Icc 0 1)).prodMk (fullProbabilityFlow_deriv hF x z hr hl h0 h1))
  rwa [joint_material_direction F x r hA] at hh

lemma mean_material_path_deriv {d : ℕ} {F : Point d → ℝ} {lam : ℝ≥0}
    (hF : Primitive F lam) (x z : Point d) {r ρ : ℝ} (hr : 0 ≤ r)
    (hl : (lam:ℝ)*r^2≤1/2) (h0 : 0≤ρ) (h1 : ρ<1) (i : Fin d) (n : ℕ) :
    HasDerivWithinAt (fun t => JetCalculus.materialIter (1,0) jointSpace r (jointMean F x r) n
      (jointMean F x r i) (t,fullProbabilityFlow hF x hr hl t z))
      (JetCalculus.materialIter (1,0) jointSpace r (jointMean F x r) (n+1)
        (jointMean F x r i) (ρ,fullProbabilityFlow hF x hr hl ρ z)) (Icc 0 1) ρ := by
  apply material_path_chain hF x z hr hl h0 h1
  exact (JetCalculus.materialIter_timeSmooth _ _ _ (jointMean_timeSmooth hF x hr hl)
    (jointMean_timeSmooth hF x hr hl i) n _ (by dsimp; linarith) h1).differentiableAt (by simp)

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

lemma JetCalculus.TimeSmooth.slice_continuous {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {A : ℝ × E → ℝ} (hA : JetCalculus.TimeSmooth A) {ρ : ℝ} (h0 : -1<ρ) (h1 : ρ<1) :
    Continuous (fun y => A (ρ,y)) := by
  apply continuous_iff_continuousAt.mpr
  intro y
  exact (hA (ρ,y) h0 h1).continuousAt.comp (continuousAt_const.prodMk continuousAt_id)

lemma mean_material_path_energy {d : ℕ} {F : Point d → ℝ} {lam : ℝ≥0}
    (hF : Primitive F lam) (x : Point d) {r ρ : ℝ} (hr : 0 ≤ r)
    (hl : (lam:ℝ)*r^2≤1/2) (h0 : 0≤ρ) (h1 : ρ<1) (n : ℕ) :
    (∑i : Fin d,∫z,(JetCalculus.materialIter (1,0) jointSpace r (jointMean F x r) n
      (jointMean F x r i) (ρ,fullProbabilityFlow hF x hr hl ρ z))^2 ∂stdGaussian (Point d))=
    ∑i : Fin d,∫y,(JetCalculus.materialIter (1,0) jointSpace r (jointMean F x r) n
      (jointMean F x r i) (ρ,y))^2 ∂interpolationLaw F x r ρ := by
  have hm := fullProbabilityFlow_interpolation_closed hF x hr hl h0 h1
  have hc := (fullProbabilityFlow_lipschitz hF x hr hl ⟨h0,h1.le⟩).continuous
  apply Finset.sum_congr rfl
  intro i _
  rw [←hm,integral_map hc.measurable.aemeasurable]
  exact ((JetCalculus.materialIter_timeSmooth _ _ _ (jointMean_timeSmooth hF x hr hl)
    (jointMean_timeSmooth hF x hr hl i) n).slice_continuous (by linarith) h1).pow 2 |>.aestronglyMeasurable
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
open Set Function MeasureTheory ProbabilityTheory
open scoped NNReal

lemma gaussian_lipschitz_memLp {d e : ℕ} {f : Point d → Point e} {K : ℝ≥0}
    (hf : LipschitzWith K f) : MemLp f 2 (stdGaussian (Point d)) := by
  have hh : LipschitzWith K (fun z => f z-f 0) :=
    LipschitzWith.of_dist_le_mul (fun z w => by simpa using hf.dist_le_mul z w)
  have hz : (fun z => f z-f 0) 0=0 := sub_self _
  have he := hh.comp_memLp hz (IsGaussian.memLp_two_id (μ:=stdGaussian (Point d)))
  have hp : MemLp (fun z => f z-f 0+f 0) 2 (stdGaussian (Point d)) :=
    he.add (memLp_const (f 0))
  simpa only [sub_add_cancel] using hp

lemma gaussian_scaled_growth_sq_moment {d e : ℕ} {f : Point d → Point e} (hf : Continuous f)
    {a b : ℝ} (ha : 0≤a) (hb : 0≤b) (hbound : ∀z,‖f z‖≤a+b*‖z‖) :
    Integrable (fun z => ‖f z‖^2) (stdGaussian (Point d)) ∧
      (∫z,‖f z‖^2 ∂stdGaussian (Point d))≤2*a^2+2*b^2*d := by
  have h : MemLp (fun z : Point d => a+b*‖z‖) 2 (stdGaussian (Point d)) :=
    (memLp_const a).add ((IsGaussian.memLp_two_id (μ:=stdGaussian (Point d))).norm.const_mul b)
  have hsq : Integrable (fun z : Point d => ‖z‖^2) (stdGaussian (Point d)) := by
    simpa only [id_eq] using (IsGaussian.memLp_two_id (μ:=stdGaussian (Point d))).integrable_norm_pow
      (by norm_num : (2:ℕ)≠0)
  have hdom : Integrable (fun z : Point d => 2*a^2+2*b^2*‖z‖^2) (stdGaussian (Point d)) :=
    (integrable_const _).add (hsq.const_mul _)
  have hb' (z : Point d) : ‖f z‖^2≤2*a^2+2*b^2*‖z‖^2 := by
    have hh := (sq_le_sq₀ (norm_nonneg _) (add_nonneg ha (mul_nonneg hb (norm_nonneg z)))).2 (hbound z)
    nlinarith [sq_nonneg (a-b*‖z‖)]
  have hi : Integrable (fun z => ‖f z‖^2) (stdGaussian (Point d)) :=
    hdom.mono' (hf.norm.pow 2).aestronglyMeasurable
      (Filter.Eventually.of_forall fun z => by simpa only [Real.norm_eq_abs,abs_sq] using hb' z)
  refine ⟨hi,?_⟩
  calc
    _ ≤ ∫z : Point d,2*a^2+2*b^2*‖z‖^2 ∂stdGaussian (Point d) := integral_mono hi hdom hb'
    _ = _ := by rw [integral_add (integrable_const _) (hsq.const_mul _),integral_const,
      probReal_univ,one_smul,integral_const_mul,stdGaussian_sq_norm]

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

include hF hr hl in
lemma probabilityFlow_initial_rms {t : ℝ} (ht : t∈Icc (0:ℝ) 1) :
    Integrable (fun z => ‖z-fullProbabilityFlow hF x hr hl t z‖^2) (stdGaussian (Point d)) ∧
    (∫z,‖z-fullProbabilityFlow hF x hr hl t z‖^2 ∂stdGaussian (Point d))≤
      2*(terminalTransportConstant*(r*‖primitiveField F x r 0‖+(lam:ℝ)*r^2*Real.pi*Real.sqrt d))^2+
      2*(terminalTransportConstant*((lam:ℝ)*r^2))^2*d := by
  apply gaussian_scaled_growth_sq_moment
    (continuous_id.sub (fullProbabilityFlow_lipschitz hF x hr hl ht).continuous)
    (mul_nonneg terminalTransportConstant_pos.le (by positivity))
    (mul_nonneg terminalTransportConstant_pos.le (by positivity))
  intro z
  simp only [Pi.sub_apply,id_eq]
  rw [norm_sub_rev]
  convert probabilityFlow_initial_displacement hF x hr hl z ht using 1
  all_goals try with_reducible_and_instances rfl
  first | rfl | ring
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
lemma logCoefficient_nonneg (A : TensorSum S) (j : ℕ) (p : ℝ≥0∞) :
    0≤A.logCoefficient j p := by
  apply Finset.sum_nonneg
  intro i _
  exact mul_nonneg (polynomialBudget_nonneg _) (by positivity)

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
namespace LogConcaveSampling.Quadrature
open MeasureTheory Set Polynomial
open scoped BigOperators

variable {I E : Type*} [Fintype I] [DecidableEq I]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

lemma weight_integral (u : I → ℝ) (f : I → E) (a b : ℝ) :
    ∫t in a..b,interpolation u f t=∑i,weight u i a b • f i := by
  simp only [interpolation]
  rw [intervalIntegral.integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro i _
    exact intervalIntegral.integral_smul_const (basis u i) (f i)
  · intro i _
    exact ((basis_continuous u i).smul continuous_const).intervalIntegrable a b

lemma reproduces_scalar (u : I → ℝ) (hu : Function.Injective u)
    (p : ℝ[X]) (hp : p.degree<Fintype.card I) (t : ℝ) :
    (∑i,basis u i t*p.eval (u i))=p.eval t := by
  have he := congrArg (fun q : ℝ[X] => q.eval t)
    (Lagrange.eq_interpolate (s:=Finset.univ) hu.injOn (by simpa using hp))
  simpa only [Lagrange.interpolate_apply,eval_finsetSum,eval_mul,eval_C,basis,mul_comm] using he.symm

lemma reproduces_power (u : I → ℝ) (hu : Function.Injective u) (k : ℕ)
    (hk : k<Fintype.card I) (t : ℝ) :
    (∑i,basis u i t*(u i)^k)=t^k := by
  have hh := reproduces_scalar u hu (X^k) (by simpa using hk) t
  simpa only [eval_pow,eval_X] using hh

omit [CompleteSpace E] in
lemma reproduces_vector (u : I → ℝ) (hu : Function.Injective u) (m : ℕ)
    (hm : m≤Fintype.card I) (v : Fin m → E) (t : ℝ) :
    interpolation u (fun i => ∑k : Fin m,(u i)^(k:ℕ) • v k) t=
      ∑k : Fin m,t^(k:ℕ) • v k := by
  unfold interpolation
  simp_rw [Finset.smul_sum,smul_smul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k _
  rw [←Finset.sum_smul,reproduces_power u hu k (lt_of_lt_of_le k.2 hm)]

end LogConcaveSampling.Quadrature

end

end

section

noncomputable section
namespace LogConcaveSampling.RMSIntegral
open MeasureTheory Set

variable {α β E : Type*} [MeasurableSpace α] [MeasurableSpace β]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  {μ : Measure α} {ν : Measure β} [IsFiniteMeasure μ]

omit [CompleteSpace E] in
lemma norm_integral_sq (f : α → E) (hf : MemLp f 2 μ) :
    ‖∫x,f x ∂μ‖^2 ≤ μ.real univ * ∫x,‖f x‖^2 ∂μ := by
  have hh := integral_mul_le_Lp_mul_Lq_of_nonneg
    (show (2:ℝ).HolderConjugate 2 from by constructor <;> norm_num)
    (Filter.Eventually.of_forall (fun x => norm_nonneg (f x)))
    (Filter.Eventually.of_forall (fun _ : α => (by norm_num : (0:ℝ)≤1)))
    (by simpa using hf.norm) (by simpa using (memLp_const (μ:=μ) (1:ℝ) : MemLp (fun _ : α => (1:ℝ)) 2 μ))
  simp only [mul_one,Real.rpow_two,one_pow,integral_const,smul_eq_mul,mul_one] at hh
  rw [←Real.sqrt_eq_rpow,←Real.sqrt_eq_rpow] at hh
  have hi : 0≤∫x,‖f x‖^2 ∂μ := integral_nonneg (fun _ => sq_nonneg _)
  have ha := (norm_integral_le_integral_norm f).trans hh
  have hs := pow_le_pow_left₀ (norm_nonneg _) ha 2
  simpa only [mul_pow,Real.sq_sqrt hi,Real.sq_sqrt (show 0≤μ.real univ from measureReal_nonneg),mul_comm] using hs

omit [CompleteSpace E] in
lemma time_seed_sq [SFinite ν] {f : α × β → E}
    (hf : AEStronglyMeasurable f (μ.prod ν))
    (hi : Integrable (fun p => ‖f p‖^2) (μ.prod ν)) :
    Integrable (fun z => ‖∫t,f (t,z) ∂μ‖^2) ν ∧
      (∫z,‖∫t,f (t,z) ∂μ‖^2 ∂ν)≤
        μ.real univ * (∫t,∫z,‖f (t,z)‖^2 ∂ν ∂μ) := by
  have hsq := hi.integral_prod_right
  have hm : AEStronglyMeasurable (fun z => ∫t,f (t,z) ∂μ) ν :=
    hf.prod_swap.integral_prod_right'
  have hbound : ∀ᵐ z ∂ν,‖∫t,f (t,z) ∂μ‖^2≤μ.real univ*(∫t,‖f (t,z)‖^2 ∂μ) := by
    filter_upwards [hi.prod_left_ae,hf.prodMk_right] with z hz hzm
    exact norm_integral_sq _ ((memLp_two_iff_integrable_sq_norm hzm).mpr hz)
  have hiout : Integrable (fun z => ‖∫t,f (t,z) ∂μ‖^2) ν := by
    apply (hsq.const_mul (μ.real univ)).mono' (hm.norm.pow 2)
    filter_upwards [hbound] with z hz
    simpa only [Real.norm_eq_abs,Pi.pow_apply,abs_sq] using hz
  refine ⟨hiout,?_⟩
  calc
    _ ≤ ∫z,μ.real univ*(∫t,‖f (t,z)‖^2 ∂μ) ∂ν := integral_mono_ae hiout (hsq.const_mul _) hbound
    _ = _ := by
      rw [integral_const_mul]
      congr 1
      exact (integral_integral_swap (f:=fun t z => ‖f (t,z)‖^2) hi).symm
end LogConcaveSampling.RMSIntegral

end

end

section

noncomputable section
namespace LogConcaveSampling.RMSIntegral
open MeasureTheory Set

variable {α β E : Type*} [MeasurableSpace α] [MeasurableSpace β]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  {μ : Measure α} {ν : Measure β} [IsFiniteMeasure μ] [SFinite ν]

omit [NormedSpace ℝ E] [CompleteSpace E] in
lemma integrable_sq_of_uniform {f : α × β → E}
    (hf : AEStronglyMeasurable f (μ.prod ν)) {B : ℝ}
    (hslice : ∀ᵐ t ∂μ,Integrable (fun z => ‖f (t,z)‖^2) ν)
    (hB : ∀ᵐ t ∂μ,(∫z,‖f (t,z)‖^2 ∂ν)≤B) :
    Integrable (fun p => ‖f p‖^2) (μ.prod ν) := by
  apply (integrable_prod_iff (hf.norm.pow 2)).mpr
  refine ⟨hslice,?_⟩
  simp only [Pi.pow_apply,Real.norm_eq_abs,abs_sq]
  apply (integrable_const B).mono' ((hf.norm.pow 2).integral_prod_right')
  filter_upwards [hB] with t ht
  have hn : 0≤∫z,‖f (t,z)‖^2 ∂ν := integral_nonneg (fun _ => sq_nonneg _)
  simpa only [Real.norm_eq_abs,abs_of_nonneg hn,Pi.pow_apply] using ht

omit [CompleteSpace E] in
theorem time_seed_uniform {f : α × β → E}
    (hf : AEStronglyMeasurable f (μ.prod ν)) {B : ℝ}
    (hslice : ∀ᵐ t ∂μ,Integrable (fun z => ‖f (t,z)‖^2) ν)
    (hB : ∀ᵐ t ∂μ,(∫z,‖f (t,z)‖^2 ∂ν)≤B) :
    Integrable (fun z => ‖∫t,f (t,z) ∂μ‖^2) ν ∧
      (∫z,‖∫t,f (t,z) ∂μ‖^2 ∂ν)≤(μ.real univ)^2*B := by
  have hi := integrable_sq_of_uniform hf hslice hB
  obtain ⟨ho,hv⟩ := time_seed_sq hf hi
  refine ⟨ho,hv.trans ?_⟩
  have hh := integral_mono_ae hi.integral_prod_left (integrable_const B) hB
  simp only [integral_const,smul_eq_mul] at hh
  convert mul_le_mul_of_nonneg_left hh (measureReal_nonneg (μ:=μ) (s:=univ)) using 1
  all_goals try with_reducible_and_instances rfl
  ring
end LogConcaveSampling.RMSIntegral

end

end

section

noncomputable section
namespace LogConcaveSampling.Quadrature
open MeasureTheory Set
open scoped BigOperators

variable {I Ω E : Type*} [Fintype I] [DecidableEq I] [MeasurableSpace Ω]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  {ν : Measure Ω} [SFinite ν]

omit [CompleteSpace E] in
lemma interpolation_continuous (u : I → ℝ) (v : I → E) : Continuous (interpolation u v) :=
  continuous_finsetSum _ (fun i _ => (basis_continuous u i).smul continuous_const)

lemma cellQuadrature_eq_integral (u : I → ℝ) (v : I → E) (ℓ θ : ℝ) :
    cellQuadrature u v ℓ θ=ℓ • ∫t in 0..θ,interpolation u v t := by
  rw [weight_integral,Finset.smul_sum]
  simp only [cellQuadrature,smul_smul]

theorem cellQuadrature_error_rms (u : I → ℝ) (f : ℝ → Ω → E) (ℓ : ℝ) {θ B : ℝ}
    (hθ : 0≤θ)
    (hf : ∀z,IntervalIntegrable (fun t => f t z) volume 0 θ)
    (hm : AEStronglyMeasurable
      (fun p : ℝ × Ω => f p.1 p.2-interpolation u (fun i => f (u i) p.2) p.1)
      ((volume.restrict (Ioc 0 θ)).prod ν))
    (hi : ∀t∈Ioc 0 θ,Integrable
      (fun z => ‖f t z-interpolation u (fun i => f (u i) z) t‖^2) ν)
    (hB : ∀t∈Ioc 0 θ,(∫z,‖f t z-interpolation u (fun i => f (u i) z) t‖^2 ∂ν)≤B) :
    Integrable (fun z => ‖ℓ • (∫t in 0..θ,f t z)-cellQuadrature u (fun i => f (u i) z) ℓ θ‖^2) ν ∧
      (∫z,‖ℓ • (∫t in 0..θ,f t z)-cellQuadrature u (fun i => f (u i) z) ℓ θ‖^2 ∂ν)≤ℓ^2*θ^2*B := by
  let μ : Measure ℝ := volume.restrict (Ioc 0 θ)
  have hs : ∀ᵐ t ∂μ,Integrable
      (fun z => ‖f t z-interpolation u (fun i => f (u i) z) t‖^2) ν := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    exact hi t ht
  have hb : ∀ᵐ t ∂μ,(∫z,‖f t z-interpolation u (fun i => f (u i) z) t‖^2 ∂ν)≤B := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    exact hB t ht
  have hv := RMSIntegral.time_seed_uniform hm hs hb
  have he (z : Ω) : ℓ • (∫t in 0..θ,f t z)-cellQuadrature u (fun i => f (u i) z) ℓ θ=
      ℓ • (∫t,(f t z-interpolation u (fun i => f (u i) z) t) ∂μ) := by
    rw [cellQuadrature_eq_integral,←smul_sub,←intervalIntegral.integral_sub (hf z)
      ((interpolation_continuous u (fun i => f (u i) z)).intervalIntegrable 0 θ),
      intervalIntegral.integral_of_le hθ]
  have hnorm (v : E) : ‖ℓ • v‖^2=ℓ^2*‖v‖^2 := by
    rw [norm_smul,mul_pow,Real.norm_eq_abs,sq_abs]
  simp_rw [he,hnorm]
  refine ⟨hv.1.const_mul _,?_⟩
  rw [integral_const_mul]
  have hμ : μ.real univ=θ := by
    dsimp only [μ,Measure.real]
    rw [Measure.restrict_apply_univ]
    change volume.real (Ioc 0 θ)=θ
    rw [Real.volume_real_Ioc_of_le hθ,sub_zero]
  rw [hμ] at hv
  exact (mul_le_mul_of_nonneg_left hv.2 (sq_nonneg ℓ)).trans_eq (by ring)
end LogConcaveSampling.Quadrature

end

end

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

section

noncomputable section
namespace LogConcaveSampling.Quadrature
open MeasureTheory Set

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

lemma taylor_kernel_bound {a x t : ℝ} (hat : a≤t) (htx : t≤x) (n : ℕ) :
    |(x-t)^n/(n.factorial:ℝ)|≤(x-a)^n/(n.factorial:ℝ) := by
  have hn : (0:ℝ)<n.factorial := by positivity
  rw [abs_of_nonneg (by positivity)]
  exact div_le_div_of_nonneg_right (pow_le_pow_left₀ (by linarith) (by linarith) n) hn.le
end LogConcaveSampling.Quadrature

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
open MeasureTheory Set

variable {α β E : Type*} [MeasurableSpace α] [MeasurableSpace β]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  {μ : Measure α} {ν : Measure β} [IsFiniteMeasure μ] [SFinite ν]

theorem weighted_time_seed {f : α × β → E} {w : α → ℝ}
    (hf : AEStronglyMeasurable f (μ.prod ν)) (hw : AEStronglyMeasurable w μ)
    {K B : ℝ} (hB0 : 0≤B) (hK : ∀ᵐ t ∂μ,|w t|≤K)
    (hslice : ∀ᵐ t ∂μ,Integrable (fun z => ‖f (t,z)‖^2) ν)
    (hB : ∀ᵐ t ∂μ,(∫z,‖f (t,z)‖^2 ∂ν)≤B) :
    Integrable (fun z => ‖∫t,w t • f (t,z) ∂μ‖^2) ν ∧
      (∫z,‖∫t,w t • f (t,z) ∂μ‖^2 ∂ν)≤(μ.real univ)^2*K^2*B := by
  have he (t : α) (z : β) : ‖w t • f (t,z)‖^2=(w t)^2*‖f (t,z)‖^2 := by
    rw [norm_smul,Real.norm_eq_abs,mul_pow,sq_abs]
  have hs : ∀ᵐ t ∂μ,Integrable (fun z => ‖w t • f (t,z)‖^2) ν := by
    filter_upwards [hslice] with t ht
    simp only [he]
    exact ht.const_mul _
  have hb : ∀ᵐ t ∂μ,(∫z,‖w t • f (t,z)‖^2 ∂ν)≤K^2*B := by
    filter_upwards [hK,hB] with t ht hb
    simp only [he,integral_const_mul]
    have ht2 : (w t)^2≤K^2 := by simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg (w t)) ht 2
    exact (mul_le_mul_of_nonneg_left hb (sq_nonneg _)).trans (mul_le_mul_of_nonneg_right ht2 hB0)
  simpa only [mul_assoc] using time_seed_uniform (f:=fun p => w p.1 • f p)
    (hw.comp_fst.smul hf) hs hb
end LogConcaveSampling.RMSIntegral

end

end

section

noncomputable section
namespace LogConcaveSampling.Quadrature
open MeasureTheory Set
open scoped BigOperators

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

omit [CompleteSpace E] in
lemma iteratedDerivWithin_chain (J : ℕ → ℝ → E) {s : Set ℝ} (hs : UniqueDiffOn ℝ s)
    (hJ : ∀n t,t∈s → HasDerivWithinAt (J n) (J (n+1) t) s t) (n : ℕ) :
    EqOn (iteratedDerivWithin n (J 0) s) (J n) s := by
  induction n with
  | zero => intro _ _; rfl
  | succ n ih =>
    intro t ht
    rw [iteratedDerivWithin_succ,derivWithin_congr ih (ih ht)]
    exact (hJ n t ht).derivWithin (hs t ht)

omit [CompleteSpace E] in
lemma contDiffOn_chain (J : ℕ → ℝ → E) {s : Set ℝ} (hs : UniqueDiffOn ℝ s)
    (hJ : ∀n t,t∈s → HasDerivWithinAt (J n) (J (n+1) t) s t) :
    ContDiffOn ℝ (⊤:ℕ∞) (J 0) s := by
  rw [contDiffOn_infty]
  intro n
  rw [contDiffOn_nat_iff_continuousOn_differentiableOn_deriv hs]
  constructor
  · intro m _
    apply (show ContinuousOn (J m) s from fun t ht => (hJ m t ht).continuousWithinAt).congr
    intro t ht
    exact iteratedDerivWithin_chain J hs hJ m ht
  · intro m _
    apply (show DifferentiableOn ℝ (J m) s from fun t ht => (hJ m t ht).differentiableWithinAt).congr
    intro t ht
    exact iteratedDerivWithin_chain J hs hJ m ht

omit [CompleteSpace E] in
lemma chainTaylor_eq {J : ℕ → ℝ → E} {s : Set ℝ} (hs : UniqueDiffOn ℝ s)
    (hJ : ∀n t,t∈s → HasDerivWithinAt (J n) (J (n+1) t) s t)
    (n : ℕ) {a : ℝ} (ha : a∈s) (x : ℝ) :
    taylorWithinEval (J 0) n s a x=chainTaylor J n a x := by
  rw [taylor_within_apply]
  apply Finset.sum_congr rfl
  intro k _
  rw [iteratedDerivWithin_chain J hs hJ k ha]

lemma chainTaylor_remainder {J : ℕ → ℝ → E} {s : Set ℝ}
    (hJ : ∀n t,t∈s → HasDerivWithinAt (J n) (J (n+1) t) s t)
    {a x : ℝ} (hsub : uIcc a x⊆s) (n : ℕ) :
    J 0 x-chainTaylor J n a x=
      ∫t in a..x,((x-t)^n/(n.factorial:ℝ)) • J (n+1) t := by
  by_cases hax : a=x
  · subst x
    simp [chainTaylor, Finset.sum_range_succ']
  have hs := uniqueDiffOn_uIcc hax
  have hJ' (n : ℕ) (t : ℝ) (ht : t∈uIcc a x) :
      HasDerivWithinAt (J n) (J (n+1) t) (uIcc a x) t := (hJ n t (hsub ht)).mono hsub
  rw [←chainTaylor_eq hs hJ' n left_mem_uIcc x,
    taylor_integral_remainder ((contDiffOn_chain J hs hJ').of_le (by exact_mod_cast (show (n+1:ℕ∞)≤⊤ from le_top)))]
  apply intervalIntegral.integral_congr
  intro t ht
  dsimp only
  rw [iteratedDerivWithin_chain J hs hJ' _ ht]
end LogConcaveSampling.Quadrature

end

end

section

noncomputable section
namespace LogConcaveSampling.Quadrature
open MeasureTheory Set

variable {β E : Type*} [MeasurableSpace β]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  {ν : Measure β} [SFinite ν]

theorem chainTaylor_remainder_rms {J : ℕ → ℝ → β → E} {s : Set ℝ} {n : ℕ} {a x B : ℝ}
    (hax : a≤x) (hB0 : 0≤B) (hsub : uIcc a x⊆s)
    (hf : ∀z n t,t∈s → HasDerivWithinAt (fun t => J n t z) (J (n+1) t z) s t)
    (hm : AEStronglyMeasurable (fun p : ℝ × β => J (n+1) p.1 p.2)
      ((volume.restrict (Ioc a x)).prod ν))
    (hi : ∀t∈Ioc a x,Integrable (fun z => ‖J (n+1) t z‖^2) ν)
    (hB : ∀t∈Ioc a x,(∫z,‖J (n+1) t z‖^2 ∂ν)≤B) :
    Integrable (fun z => ‖J 0 x z-chainTaylor (fun k t => J k t z) n a x‖^2) ν ∧
      (∫z,‖J 0 x z-chainTaylor (fun k t => J k t z) n a x‖^2 ∂ν)≤
        ((x-a)^(n+1)/(n.factorial:ℝ))^2*B := by
  let μ : Measure ℝ := volume.restrict (Ioc a x)
  let w : ℝ → ℝ := fun t => (x-t)^n/(n.factorial:ℝ)
  have hw : AEStronglyMeasurable w μ := by
    apply Continuous.aestronglyMeasurable
    dsimp [w]; fun_prop
  have hk : ∀ᵐ t ∂μ,|w t|≤(x-a)^n/(n.factorial:ℝ) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    exact taylor_kernel_bound ht.1.le ht.2 n
  have hs : ∀ᵐ t ∂μ,Integrable (fun z => ‖J (n+1) t z‖^2) ν := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    exact hi t ht
  have hb : ∀ᵐ t ∂μ,(∫z,‖J (n+1) t z‖^2 ∂ν)≤B := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    exact hB t ht
  have hv := RMSIntegral.weighted_time_seed hm hw hB0 hk hs hb
  have he (z : β) : J 0 x z-chainTaylor (fun k t => J k t z) n a x=
      ∫t,w t • J (n+1) t z ∂μ := by
    rw [chainTaylor_remainder (hf z) hsub,intervalIntegral.integral_of_le hax]
  have hμ : μ.real univ=x-a := by
    dsimp only [μ,Measure.real]
    rw [Measure.restrict_apply_univ]
    exact Real.volume_real_Ioc_of_le hax
  simp_rw [he]
  refine ⟨hv.1,hv.2.trans_eq ?_⟩
  rw [hμ,pow_succ]
  ring
end LogConcaveSampling.Quadrature

end

end

section

noncomputable section
namespace LogConcaveSampling.Quadrature
open MeasureTheory Set Polynomial
open scoped BigOperators

variable {I E : Type*} [Fintype I] [DecidableEq I]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

omit [CompleteSpace E] in
lemma chainTaylor_scaled_eval (J : ℕ → ℝ → E) (n : ℕ) (a ℓ t : ℝ) :
    chainTaylor J n a (a+ℓ*t)=
      ∑k : Fin (n+1),t^(k:ℕ) •
        (((k.val.factorial:ℝ)⁻¹*ℓ^(k:ℕ)) • J k a) := by
  unfold chainTaylor
  rw [←Fin.sum_univ_eq_sum_range]
  apply Finset.sum_congr rfl
  intro k _
  rw [show a+ℓ*t-a=ℓ*t by ring,mul_pow,smul_smul]
  congr 1
  ring

omit [CompleteSpace E] in
lemma reproduces_cell_chainTaylor (u : I → ℝ) (hu : Function.Injective u) (n : ℕ)
    (hn : n+1≤Fintype.card I) (J : ℕ → ℝ → E) (a ℓ t : ℝ) :
    interpolation u (fun i => chainTaylor J n a (a+ℓ*u i)) t=
      chainTaylor J n a (a+ℓ*t) := by
  simp_rw [chainTaylor_scaled_eval]
  exact reproduces_vector u hu (n+1) hn _ t

omit [CompleteSpace E] in
lemma interpolation_sub_unused (u : I → ℝ) (f g : I → E) (t : ℝ) :
    interpolation u (fun i => f i-g i) t=interpolation u f t-interpolation u g t := by
  simp [interpolation,smul_sub,Finset.sum_sub_distrib]

omit [CompleteSpace E] in
lemma cell_chain_error_eq (u : I → ℝ) (hu : Function.Injective u) (n : ℕ)
    (hn : n+1≤Fintype.card I) (J : ℕ → ℝ → E) (a ℓ t : ℝ) :
    J 0 (a+ℓ*t)-interpolation u (fun i => J 0 (a+ℓ*u i)) t=
      (J 0 (a+ℓ*t)-chainTaylor J n a (a+ℓ*t))-
        interpolation u (fun i => J 0 (a+ℓ*u i)-chainTaylor J n a (a+ℓ*u i)) t := by
  rw [interpolation_sub_unused,reproduces_cell_chainTaylor u hu n hn]
  abel
end LogConcaveSampling.Quadrature

end

end

section

noncomputable section
namespace LogConcaveSampling.Quadrature
open MeasureTheory Set
open scoped BigOperators

variable {I Ω E : Type*} [Fintype I] [DecidableEq I] [MeasurableSpace Ω]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E] {ν : Measure Ω}

omit [CompleteSpace E] in
theorem cell_chain_error_rms (u : I → ℝ) (hu : Function.Injective u) (n : ℕ)
    (hn : n+1≤Fintype.card I) (J : ℕ → ℝ → Ω → E) (a ℓ t : ℝ) {B C : ℝ}
    (hB : 0≤B) (hC : 1≤C) (hc : ∑i,|basis u i t|≤C)
    (hm : ∀s∈insert t (Set.range u),AEStronglyMeasurable
      (fun z => J 0 (a+ℓ*s) z-chainTaylor (fun k v => J k v z) n a (a+ℓ*s)) ν)
    (hi : ∀s∈insert t (Set.range u),Integrable
      (fun z => ‖J 0 (a+ℓ*s) z-chainTaylor (fun k v => J k v z) n a (a+ℓ*s)‖^2) ν)
    (hR : ∀s∈insert t (Set.range u),(∫z,
      ‖J 0 (a+ℓ*s) z-chainTaylor (fun k v => J k v z) n a (a+ℓ*s)‖^2 ∂ν)≤B) :
    Integrable (fun z => ‖J 0 (a+ℓ*t) z-interpolation u (fun i => J 0 (a+ℓ*u i) z) t‖^2) ν ∧
      (∫z,‖J 0 (a+ℓ*t) z-interpolation u (fun i => J 0 (a+ℓ*u i) z) t‖^2 ∂ν)≤4*C^2*B := by
  let R (s : ℝ) (z : Ω) := J 0 (a+ℓ*s) z-chainTaylor (fun k v => J k v z) n a (a+ℓ*s)
  have hmt := hm t (mem_insert t _)
  have hmn (i : I) := hm (u i) (mem_insert_of_mem t (mem_range_self i))
  have hit := hi t (mem_insert t _)
  have hin (i : I) := hi (u i) (mem_insert_of_mem t (mem_range_self i))
  have hRn (i : I) := hR (u i) (mem_insert_of_mem t (mem_range_self i))
  have hsum := RMSIntegral.weighted_sum_sq (fun i => basis u i t) (fun i => R (u i)) hmn hin hRn
  have hms : AEStronglyMeasurable (fun z => interpolation u (fun i => R (u i) z) t) ν := by
    have hs := Finset.aestronglyMeasurable_sum Finset.univ (fun i _ => (hmn i).const_smul (basis u i t))
    convert hs using 1
    all_goals try with_reducible_and_instances rfl
    ext z
    simp only [interpolation,Finset.sum_apply,Pi.smul_apply,R]
  have hsb : (∫z,‖interpolation u (fun i => R (u i) z) t‖^2 ∂ν)≤C^2*B := by
    apply hsum.2.trans
    exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀
      (Finset.sum_nonneg (fun _ _ => abs_nonneg _)) hc 2) hB
  have hs := RMSIntegral.sub_sq_bound hmt hms hit hsum.1 (hR t (mem_insert t _)) hsb
  have he (z : Ω) := cell_chain_error_eq u hu n hn (fun k v => J k v z) a ℓ t
  simp_rw [he]
  refine ⟨hs.1,hs.2.trans ?_⟩
  have hc2 : 1≤C^2 := by nlinarith
  nlinarith [mul_le_mul_of_nonneg_right hc2 hB]
end LogConcaveSampling.Quadrature

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
open Set MeasureTheory
open scoped BigOperators

variable {I : Type*} [Fintype I] [DecidableEq I]

lemma compositeWeight_sum {N : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] (u : I → ℝ) (ℓ : Fin N → ℝ) (v : Fin N × I → E) (i : Fin N × I) :
    (∑j,compositeWeight u ℓ i j • v j)=
      ∑c,cellQuadrature u (fun j => v (c,j)) (ℓ c) (compositeAngle u i c) := by
  rw [Fintype.sum_prod_type]
  rfl

lemma composite_error_rms {N : ℕ} {Ω E : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E] {ν : Measure Ω}
    (ℓ : Fin N → ℝ) (R : Fin N → Ω → E) {B : ℝ}
    (hℓ : ∀c,0≤ℓ c) (hsum : (∑c,ℓ c)≤1) (hB : 0≤B)
    (hm : ∀c,AEStronglyMeasurable (R c) ν)
    (hi : ∀c,Integrable (fun z => ‖R c z‖^2) ν)
    (hb : ∀c,(∫z,‖R c z‖^2 ∂ν)≤B) :
    Integrable (fun z => ‖∑c,ℓ c • R c z‖^2) ν ∧
      (∫z,‖∑c,ℓ c • R c z‖^2 ∂ν)≤B := by
  have he := RMSIntegral.weighted_sum_sq ℓ R hm hi hb
  simp only [abs_of_nonneg (hℓ _)] at he
  refine ⟨he.1,he.2.trans ?_⟩
  have hn : 0≤∑c,ℓ c := Finset.sum_nonneg (fun c _ => hℓ c)
  exact mul_le_of_le_one_left hB (by nlinarith)
end LogConcaveSampling.Quadrature

end

end

section

noncomputable section
namespace LogConcaveSampling.Quadrature
open Set MeasureTheory
open scoped BigOperators

variable {I E : Type*} [Fintype I] [DecidableEq I]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

omit [Fintype I] [DecidableEq I] [CompleteSpace E] in
lemma compositeIntegral_sum {N : ℕ} (u : I → ℝ) (t : ℕ → ℝ)
    (f : ℝ → E) (hf : Continuous f) (i : Fin N × I) :
    (∑c : Fin N,(t (c.val+1)-t c.val) •
      ∫s in 0..compositeAngle u i c,f (t c.val+(t (c.val+1)-t c.val)*s))=
      ∫s in t 0..(t i.1.val+(t (i.1.val+1)-t i.1.val)*u i.2),f s := by
  let v := t i.1.val+(t (i.1.val+1)-t i.1.val)*u i.2
  let τ : ℕ → ℝ := fun k => if k≤ i.1.val then t k else v
  have hc (c : Fin N) : (t (c.val+1)-t c.val) •
      (∫s in 0..compositeAngle u i c,f (t c.val+(t (c.val+1)-t c.val)*s))=
        ∫s in τ c.val..τ (c.val+1),f s := by
    rw [intervalIntegral.smul_integral_comp_add_mul]
    simp only [mul_zero,add_zero]
    rcases lt_trichotomy c i.1 with hlt | heq | hgt
    · have hnat : c.val< i.1.val := hlt
      have hnext : c.val+1≤ i.1.val := by omega
      simp only [compositeAngle,ite_eq_left hlt,τ,ite_eq_left hnat.le,
        ite_eq_left hnext,mul_one,add_sub_cancel]
    · subst c
      have hnot : ¬i.1.val+1≤ i.1.val := by omega
      simp only [compositeAngle,lt_self_iff_false,ite_false,τ,le_refl,ite_true,ite_eq_right hnot,v]
    · have hnot : ¬c< i.1 := not_lt_of_gt hgt
      have hne : c≠i.1 := ne_of_gt hgt
      have hnat : ¬c.val≤ i.1.val := not_le_of_gt hgt
      have hnext : ¬c.val+1≤ i.1.val := by omega
      simp only [compositeAngle,ite_eq_right hnot,ite_eq_right hne,τ,
        ite_eq_right hnat,ite_eq_right hnext,mul_zero,add_zero,
        intervalIntegral.integral_same]
  simp_rw [hc]
  rw [Fin.sum_univ_eq_sum_range (fun k => ∫s in τ k..τ (k+1),f s),
    intervalIntegral.sum_integral_adjacent_intervals (fun _ _ => hf.intervalIntegrable _ _)]
  have hnot : ¬N≤ i.1.val := not_le_of_gt i.1.2
  simp only [τ,Nat.zero_le,ite_true,ite_eq_right hnot,v]

lemma compositeQuadrature_defect {N : ℕ} (u : I → ℝ) (t : ℕ → ℝ)
    (f : ℝ → E) (hf : Continuous f) (i : Fin N × I) :
    (∫s in t 0..(t i.1.val+(t (i.1.val+1)-t i.1.val)*u i.2),f s)-
      (∑j : Fin N × I,compositeWeight u (fun c => t (c.val+1)-t c.val) i j •
        f (t j.1.val+(t (j.1.val+1)-t j.1.val)*u j.2))=
      ∑c : Fin N,(t (c.val+1)-t c.val) •
        (∫s in 0..compositeAngle u i c,f (t c.val+(t (c.val+1)-t c.val)*s)-
          interpolation u (fun j => f (t c.val+(t (c.val+1)-t c.val)*u j)) s) := by
  rw [←compositeIntegral_sum u t f hf i,compositeWeight_sum,←Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro _ _
  rw [cellQuadrature_eq_integral,←smul_sub,intervalIntegral.integral_sub]
  · exact (hf.comp (continuous_const.add (continuous_const.mul continuous_id))).intervalIntegrable _ _
  · exact (interpolation_continuous _ _).intervalIntegrable _ _
end LogConcaveSampling.Quadrature

end

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

lemma step_lipschitz (w : I → I → ℝ) (φ : I → E → E) (a : I → E) {A K : ℝ≥0}
    (hw : ∀i,∑j,|w i j|≤A) (hφ : ∀i,LipschitzWith K (φ i)) :
    LipschitzWith (A*K) (step w φ a) := by
  apply LipschitzWith.of_dist_le_mul
  intro z v
  simpa only [step,dist_add_left] using (correction_lipschitz w φ hw hφ).dist_le_mul z v

theorem iterate_defect {Y : Type*} [PseudoMetricSpace Y] {q : ℝ≥0}
    {G : Y → Y} (hG : LipschitzWith q G) (hq : (q:ℝ)≤1/2)
    (a e : Y) {D : ℝ} (hD : 0≤D) (he : dist (G e) e≤D) (n : ℕ) :
    dist (G^[n] a) e≤2*D+(q:ℝ)^n*dist a e := by
  induction n with
  | zero => simp only [Function.iterate_zero_apply,pow_zero,one_mul]; linarith
  | succ n ih =>
    rw [Function.iterate_succ_apply']
    calc
      _ ≤ dist (G (G^[n] a)) (G e)+dist (G e) e := dist_triangle _ _ _
      _ ≤ (q:ℝ)*dist (G^[n] a) e+D := add_le_add (hG.dist_le_mul _ _) he
      _ ≤ (q:ℝ)*(2*D+(q:ℝ)^n*dist a e)+D := add_le_add (mul_le_mul_of_nonneg_left ih q.coe_nonneg) le_rfl
      _ ≤ 2*D+(q:ℝ)^(n+1)*dist a e := by
        rw [pow_succ]
        nlinarith [mul_le_mul_of_nonneg_right hq hD]

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

lemma logMeshStep_le {T h : ℝ} (hT0 : 0<T) (hT1 : T<1) (hh : 0<h) :
    logMeshStep T h≤h := by
  have hN : (0:ℝ)<logMeshCount T h := by exact_mod_cast logMeshCount_pos hT0 hT1 hh
  apply (div_le_iff₀ hN).mpr
  have he := (div_le_iff₀ hh).mp (Nat.le_ceil (logMeshLength T/h))
  change logMeshLength T≤(logMeshCount T h:ℝ)*h at he
  nlinarith

lemma logMeshCell_upper {T h : ℝ} (hT0 : 0<T) (hT1 : T<1) (hh : 0<h) (j : ℕ) :
    logMeshNode T h (j+1)-logMeshNode T h j≤h*(1-logMeshNode T h j) := by
  have hb : 1-Real.exp (-logMeshStep T h)≤h := by
    have hx := Real.add_one_le_exp (-logMeshStep T h)
    have hs := logMeshStep_le hT0 hT1 hh
    linarith
  have hp : 0≤1-logMeshNode T h j := by
    simpa only [logMeshNode,sub_sub_cancel] using (Real.exp_pos (-(j:ℝ)*logMeshStep T h)).le
  rw [logMeshNode_sub,mul_comm h]
  exact mul_le_mul_of_nonneg_left hb hp

end LogConcaveSampling.Quadrature

end

end

section

noncomputable section
namespace LogConcaveSampling.Quadrature

lemma logMeshCell_upper_right {T h : ℝ} (hT0 : 0<T) (hT1 : T<1) (hh : 0<h)
    (hsmall : h≤Real.log 2) (j : ℕ) :
    logMeshNode T h (j+1)-logMeshNode T h j≤2*h*(1-logMeshNode T h (j+1)) := by
  have hs := logMeshStep_le hT0 hT1 hh
  have he : Real.exp (logMeshStep T h)≤2 := by
    simpa only [Real.exp_log (by norm_num : (0:ℝ)<2)] using Real.exp_le_exp.mpr (hs.trans hsmall)
  have hid : (1-logMeshNode T h (j+1))*Real.exp (logMeshStep T h)=1-logMeshNode T h j := by
    simp only [logMeshNode,sub_sub_cancel,←Real.exp_add]
    congr 1
    push_cast
    ring
  have hn : 0≤1-logMeshNode T h (j+1) := by
    simpa only [logMeshNode,sub_sub_cancel] using (Real.exp_pos _).le
  have hb := mul_le_mul_of_nonneg_left he hn
  rw [hid] at hb
  calc
    _ ≤ h*(1-logMeshNode T h j) := logMeshCell_upper hT0 hT1 hh j
    _ ≤ h*((1-logMeshNode T h (j+1))*2) := mul_le_mul_of_nonneg_left hb hh.le
    _ = _ := by ring

lemma cell_singularity_cancel {a b t h : ℝ} (ha : 0≤a) (hat : a≤t) (htb : t≤b)
    (hb : b<1) (hh : 0≤h) (hcell : b-a≤h*(1-b)) (n : ℕ) :
    (t-a)^(n+1)*((Real.sqrt (1-b^2))⁻¹)^(2*n+2)≤h^(n+1) := by
  have hb0 : 0≤b := ha.trans (hat.trans htb)
  have hp : 0<1-b^2 := by nlinarith
  have hlen : t-a≤h*(1-b^2) := by
    have he : 1-b≤1-b^2 := by nlinarith
    have hm := mul_le_mul_of_nonneg_left he hh
    linarith
  have hr : (t-a)*(1-b^2)⁻¹≤h := by
    rw [←div_eq_mul_inv,div_le_iff₀ hp]
    exact hlen
  rw [show 2*n+2=2*(n+1) by omega,pow_mul,inv_pow,Real.sq_sqrt hp.le,←mul_pow]
  exact pow_le_pow_left₀ (mul_nonneg (sub_nonneg.mpr hat) (inv_nonneg.mpr hp.le)) hr _

lemma cell_taylor_budget {a b t h A : ℝ} (ha : 0≤a) (hat : a≤t) (htb : t≤b)
    (hb : b<1) (hh : 0≤h) (hcell : b-a≤h*(1-b)) (hA : 0≤A) (n : ℕ) :
    ((t-a)^(n+1)/(n.factorial:ℝ))^2*(A*((Real.sqrt (1-b^2))⁻¹)^(2*n+2))^2≤
      (A*h^(n+1))^2 := by
  have hfac : (1:ℝ)≤n.factorial := by exact_mod_cast Nat.factorial_pos n
  have hfp : (0:ℝ)<n.factorial := by positivity
  have hd : (t-a)^(n+1)/(n.factorial:ℝ)≤(t-a)^(n+1) := by
    rw [div_le_iff₀ hfp]
    exact le_mul_of_one_le_right (pow_nonneg (sub_nonneg.mpr hat) _) hfac
  have hB := cell_singularity_cancel ha hat htb hb hh hcell n
  have hR : 0≤((Real.sqrt (1-b^2))⁻¹)^(2*n+2) := by positivity
  have he : ((t-a)^(n+1)/(n.factorial:ℝ))*(A*((Real.sqrt (1-b^2))⁻¹)^(2*n+2))≤
      A*h^(n+1) := by
    calc
      _ ≤ (t-a)^(n+1)*(A*((Real.sqrt (1-b^2))⁻¹)^(2*n+2)) :=
        mul_le_mul_of_nonneg_right hd (mul_nonneg hA hR)
      _ = A*((t-a)^(n+1)*((Real.sqrt (1-b^2))⁻¹)^(2*n+2)) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hB hA
  rw [←mul_pow]
  apply pow_le_pow_left₀ _ he 2
  positivity
end LogConcaveSampling.Quadrature

end

end

end

end OAI
end

section
-- module Solutions.OAIQ048_LC.LogConcave_Numerics_NodeLp
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
open scoped BigOperators NNReal RealInnerProductSpace

variable {Ω E I : Type*} [MeasurableSpace Ω] {ν : Measure Ω} [IsFiniteMeasure ν]
  [NormedAddCommGroup E]

lemma nodeLp_ae {K : ℝ≥0} {φ : E → E} (hφ : LipschitzWith K φ) (f : Lp E 2 ν) :
    (nodeLp hφ f : Ω → E)=ᵐ[ν] fun z => φ (f z) := by
  filter_upwards [Lp.coeFn_add ((lipschitz_zero_shift hφ).compLp (by simp) f)
      (Lp.const 2 ν (φ 0)),
    (lipschitz_zero_shift hφ).coeFn_compLp (by simp) f,
    Lp.coeFn_const 2 ν (φ 0)] with z hz hφz hc
  simp only [nodeLp,hz,Pi.add_apply,hφz,Function.comp_apply,hc,Function.const_apply,sub_add_cancel]

lemma nodeLp_lipschitz {K : ℝ≥0} {φ : E → E} (hφ : LipschitzWith K φ) :
    LipschitzWith K (nodeLp (ν:=ν) hφ) := by
  apply LipschitzWith.of_dist_le_mul
  intro f g
  simpa only [nodeLp,dist_add_right] using
    ((lipschitz_zero_shift hφ).lipschitzWith_compLp (by simp)).dist_le_mul f g

variable [NormedSpace ℝ E] [Fintype I]

lemma stepLp_lipschitz (w : I → I → ℝ) (φ : I → E → E) {A K : ℝ≥0}
    (hφ : ∀i,LipschitzWith K (φ i)) (a : I → Lp E 2 ν)
    (hw : ∀i,∑j,|w i j|≤A) : LipschitzWith (A*K) (stepLp w φ hφ a) :=
  step_lipschitz w _ a hw (fun j => nodeLp_lipschitz (hφ j))

lemma stepLp_ae (w : I → I → ℝ) (φ : I → E → E) {K : ℝ≥0}
    (hφ : ∀i,LipschitzWith K (φ i)) (a z : I → Lp E 2 ν) (i : I) :
    (stepLp w φ hφ a z i : Ω → E)=ᵐ[ν]
      fun ω => step w φ (fun j => a j ω) (fun j => z j ω) i := by
  classical
  have ha := Lp.coeFn_add (a i) (∑j,w i j • nodeLp (hφ j) (z j))
  have hs := Lp.coeFn_fun_finsetSum Finset.univ (fun j => w i j • nodeLp (hφ j) (z j))
  have hm : ∀ᵐω ∂ν,∀j,(w i j • nodeLp (hφ j) (z j) : Lp E 2 ν) ω=
      w i j • φ j (z j ω) := by
    rw [ae_all_iff]
    intro j
    filter_upwards [Lp.coeFn_smul (w i j) (nodeLp (hφ j) (z j)),nodeLp_ae (hφ j) (z j)] with ω h1 h2
    simp only [h1,Pi.smul_apply,h2]
  filter_upwards [ha,hs,hm] with ω h1 h2 h3
  simp only [stepLp,step,correction,Pi.add_apply,h1,h2,h3]

theorem rms_picard_defect (w : I → I → ℝ) (φ : I → E → E) {A K : ℝ≥0}
    (hφ : ∀i,LipschitzWith K (φ i)) (a e : I → Lp E 2 ν)
    (hw : ∀i,∑j,|w i j|≤A) (hq : (A*K:ℝ≥0)≤1/2)
    {D : ℝ} (hD : 0≤D) (he : ∀i,dist (stepLp w φ hφ a e i) (e i)≤D) (n : ℕ) :
    dist ((stepLp w φ hφ a)^[n] a) e≤2*D+(A*K:ℝ≥0)^n*dist a e := by
  apply iterate_defect (stepLp_lipschitz w φ hφ a hw) (by exact_mod_cast hq) a e hD
    ((dist_pi_le_iff hD).mpr he) n

section Inner
omit [NormedSpace ℝ E] [IsFiniteMeasure ν]
variable [InnerProductSpace ℝ E]

lemma lp_norm_sq_integral (f : Lp E 2 ν) : ‖f‖^2=∫ω,‖f ω‖^2 ∂ν := by
  rw [←real_inner_self_eq_norm_sq,L2.inner_def]
  simp only [real_inner_self_eq_norm_sq]

end Inner
end LogConcaveSampling.FinitePicard

end

end

section

noncomputable section
namespace LogConcaveSampling.FinitePicard
open MeasureTheory
open scoped BigOperators NNReal RealInnerProductSpace

variable {Ω E I : Type*} [MeasurableSpace Ω] {ν : Measure Ω} [IsFiniteMeasure ν]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [Fintype I]

omit [IsFiniteMeasure ν] in
lemma lp_rms_eq (f g : Lp E 2 ν) {u v : Ω → E}
    (hf : (f : Ω → E)=ᵐ[ν] u) (hg : (g : Ω → E)=ᵐ[ν] v) :
    Integrable (fun ω => ‖u ω-v ω‖^2) ν ∧
      (∫ω,‖u ω-v ω‖^2 ∂ν)=dist f g^2 := by
  have he : (fun ω => (f-g : Lp E 2 ν) ω)=ᵐ[ν] fun ω => u ω-v ω := by
    filter_upwards [Lp.coeFn_sub f g,hf,hg] with ω h1 h2 h3
    simp only [h1,Pi.sub_apply,h2,h3]
  have hi := (Lp.memLp (f-g)).integrable_norm_pow (by norm_num : (2:ℕ)≠0)
  have hn : (fun ω => ‖(f-g : Lp E 2 ν) ω‖^2)=ᵐ[ν] fun ω => ‖u ω-v ω‖^2 :=
    he.fun_comp (fun z => ‖z‖^2)
  refine ⟨hi.congr hn,?_⟩
  rw [dist_eq_norm,lp_norm_sq_integral]
  exact integral_congr_ae hn.symm

lemma iterateLp_nodes_ae (w : I → I → ℝ) (φ : I → E → E) {K : ℝ≥0}
    (hφ : ∀i,LipschitzWith K (φ i)) (a : I → Ω → E) (aLp : I → Lp E 2 ν)
    (ha : ∀i,(aLp i : Ω → E)=ᵐ[ν] a i) (N : ℕ) (i : I) :
    ((stepLp w φ hφ aLp)^[N] aLp i : Ω → E)=ᵐ[ν]
      fun ω => nodes w φ (fun ω j => a j ω) N ω i := by
  induction N generalizing i with
  | zero => simpa only [Function.iterate_zero_apply,nodes] using ha i
  | succ N ih =>
    rw [Function.iterate_succ_apply']
    have hia : ∀ᵐω ∂ν,∀j,aLp j ω=a j ω := ae_all_iff.mpr ha
    have hii : ∀ᵐω ∂ν,∀j,((stepLp w φ hφ aLp)^[N] aLp j : Ω → E) ω=
        nodes w φ (fun ω j => a j ω) N ω j := ae_all_iff.mpr ih
    filter_upwards [stepLp_ae w φ hφ aLp ((stepLp w φ hφ aLp)^[N] aLp) i,hia,hii] with ω h1 h2 h3
    simp only [h1,nodes,step,correction,Pi.add_apply,h2,h3]

theorem nodes_rms (w : I → I → ℝ) (φ : I → E → E) {A K : ℝ≥0}
    (hφ : ∀i,LipschitzWith K (φ i)) (a e : I → Ω → E)
    (ha : ∀i,MemLp (a i) 2 ν) (he : ∀i,MemLp (e i) 2 ν)
    (hw : ∀i,∑j,|w i j|≤A) (hq : (A*K:ℝ≥0)≤1/2)
    {D H : ℝ} (hD : 0≤D) (hH : 0≤H)
    (hdef : ∀i,(∫ω,‖step w φ (fun j => a j ω) (fun j => e j ω) i-e i ω‖^2 ∂ν)≤D^2)
    (hinit : ∀i,(∫ω,‖a i ω-e i ω‖^2 ∂ν)≤H^2) (N : ℕ) (i : I) :
    Integrable (fun ω => ‖nodes w φ (fun ω j => a j ω) N ω i-e i ω‖^2) ν ∧
      (∫ω,‖nodes w φ (fun ω j => a j ω) N ω i-e i ω‖^2 ∂ν)≤
        (2*D+(A*K:ℝ≥0)^N*H)^2 := by
  let aLp : I → Lp E 2 ν := fun j => (ha j).toLp (a j)
  let eLp : I → Lp E 2 ν := fun j => (he j).toLp (e j)
  have ha' (j : I) : (aLp j : Ω → E)=ᵐ[ν] a j := (ha j).coeFn_toLp
  have he' (j : I) : (eLp j : Ω → E)=ᵐ[ν] e j := (he j).coeFn_toLp
  have hstep (j : I) : (stepLp w φ hφ aLp eLp j : Ω → E)=ᵐ[ν]
      fun ω => step w φ (fun i => a i ω) (fun i => e i ω) j := by
    filter_upwards [stepLp_ae w φ hφ aLp eLp j,ae_all_iff.mpr ha',ae_all_iff.mpr he'] with ω h1 h2 h3
    simpa only [h2,h3] using h1
  have hdef' (j : I) : dist (stepLp w φ hφ aLp eLp j) (eLp j)≤D := by
    have hh := (lp_rms_eq _ _ (hstep j) (he' j)).2
    have hb := hdef j
    rw [hh] at hb
    nlinarith [dist_nonneg (x:=stepLp w φ hφ aLp eLp j) (y:=eLp j)]
  have hinit' : dist aLp eLp≤H := by
    apply (dist_pi_le_iff hH).mpr
    intro j
    have hh := (lp_rms_eq _ _ (ha' j) (he' j)).2
    have hb := hinit j
    rw [hh] at hb
    nlinarith [dist_nonneg (x:=aLp j) (y:=eLp j)]
  have hb := rms_picard_defect w φ hφ aLp eLp hw hq hD hdef' N
  have hrms := lp_rms_eq _ _ (iterateLp_nodes_ae w φ hφ a aLp ha' N i) (he' i)
  refine ⟨hrms.1,?_⟩
  rw [hrms.2]
  apply pow_le_pow_left₀ dist_nonneg _ 2
  exact (dist_le_pi_dist _ _ i).trans (hb.trans
    (add_le_add le_rfl (mul_le_mul_of_nonneg_left hinit' (show 0≤((A*K:ℝ≥0):ℝ)^N from by positivity))))
end LogConcaveSampling.FinitePicard

end

end

end

end OAI
end

section
-- module Solutions.OAIQ048_LC.LogConcave_Sampling_MeanMaterialVector
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
open scoped Classical BigOperators NNReal

theorem mean_material_polylog (n : ℕ) :
    ∃C : ℝ,0≤C ∧ ∃k : ℕ,∀{d : ℕ} {F : Point d → ℝ} {lam : ℝ≥0},
      Primitive F lam → ∀(x : Point d) {r ρ : ℝ},0 < r → 0 < lam →
        (lam:ℝ)*r^2≤1/2 → 0≤ρ → ρ<1 → 1≤d →
        Real.sqrt (∑i : Fin d,∫y,
          (JetCalculus.materialIter (1,0) jointSpace r (jointMean F x r) (n+1)
            (jointMean F x r i) (ρ,y))^2 ∂interpolationLaw F x r ρ)≤
          C*((lam:ℝ)*r)*Real.sqrt (d:ℝ)*(1+Real.log ((d:ℝ)+1))^k*
            ((Real.sqrt (1-ρ^2))⁻¹)^(2*n+2) := by
  obtain ⟨A,hA⟩ := mean_material_l2 n
  let C := A.logCoefficient 1 2+Real.sqrt (interpolationHessianBudget:ℝ)*A.logCoefficient 0 2
  let k := A.logDegree 1+A.logDegree 0
  refine ⟨C,add_nonneg (A.logCoefficient_nonneg 1 2)
    (mul_nonneg (Real.sqrt_nonneg _) (A.logCoefficient_nonneg 0 2)), k,?_⟩
  intro d F lam hF x r ρ hr hlam hl h0 h1 hd
  have ht : 1≤1+Real.log ((d:ℝ)+1) := by
    have hh := Real.log_nonneg (show 1≤(d:ℝ)+1 by linarith [Nat.cast_nonneg (α:=ℝ) d])
    linarith
  have hB (j : ℕ) (hj : A.logDegree j≤k) :
      (A.momentBudget d j 2).toReal≤A.logCoefficient j 2*(1+Real.log ((d:ℝ)+1))^k :=
    (A.momentBudget_polylog d j 2).trans
      (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ ht hj) (A.logCoefficient_nonneg j 2))
  have hb : (A.momentBudget d 1 2).toReal+Real.sqrt (interpolationHessianBudget:ℝ)*(A.momentBudget d 0 2).toReal≤
      C*(1+Real.log ((d:ℝ)+1))^k := by
    have hh := add_le_add (hB 1 (Nat.le_add_right _ _))
      (mul_le_mul_of_nonneg_left (hB 0 (Nat.le_add_left _ _)) (Real.sqrt_nonneg (interpolationHessianBudget:ℝ)))
    simpa only [C,add_mul,mul_assoc] using hh
  apply (hA hF x hr hlam hl h0 h1 hd).trans
  have hh := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left hb (show 0≤(lam:ℝ)*r*Real.sqrt (d:ℝ) by positivity))
    (show 0≤((Real.sqrt (1-ρ^2))⁻¹)^(2*n+2) by positivity)
  convert hh using 1
  all_goals try with_reducible_and_instances rfl
  ring

theorem mean_path_polylog (n : ℕ) :
    ∃C : ℝ,0≤C ∧ ∃k : ℕ,∀{d : ℕ} {F : Point d → ℝ} {lam : ℝ≥0},
      ∀hF : Primitive F lam, ∀(x : Point d) {r ρ : ℝ},∀hr : 0 < r,
        0 < lam → ∀hl : (lam:ℝ)*r^2≤1/2,0≤ρ → ρ<1 → 1≤d →
        Real.sqrt (∑i : Fin d,∫z,
          (JetCalculus.materialIter (1,0) jointSpace r (jointMean F x r) (n+1)
            (jointMean F x r i) (ρ,fullProbabilityFlow hF x hr.le hl ρ z))^2 ∂stdGaussian (Point d))≤
          C*((lam:ℝ)*r)*Real.sqrt (d:ℝ)*(1+Real.log ((d:ℝ)+1))^k*
            ((Real.sqrt (1-ρ^2))⁻¹)^(2*n+2) := by
  obtain ⟨C,hC,k,hk⟩ := mean_material_polylog n
  refine ⟨C,hC,k,?_⟩
  intro d F lam hF x r ρ hr hlam hl h0 h1 hd
  rw [mean_material_path_energy hF x hr.le hl h0 h1]
  exact hk hF x hr hlam hl h0 h1 hd
end LogConcaveSampling

end

end

section

noncomputable section
namespace LogConcaveSampling
open MeasureTheory Set ProbabilityTheory
open scoped Classical BigOperators NNReal RealInnerProductSpace

lemma meanMaterialVector_norm_sq {d : ℕ} (F : Point d → ℝ) (x : Point d) (r : ℝ)
    (n : ℕ) (p : ℝ × Point d) :
    ‖meanMaterialVector F x r n p‖^2=∑i : Fin d,
      (JetCalculus.materialIter (1,0) jointSpace r (jointMean F x r) n
        (jointMean F x r i) p)^2 := EuclideanSpace.real_norm_sq_eq _

lemma meanMaterial_slice_polySmooth {d : ℕ} {F : Point d → ℝ} {lam : ℝ≥0}
    (hF : Primitive F lam) (x : Point d) {r ρ : ℝ} (hr : 0 < r) (hlam : 0<lam)
    (hl : (lam:ℝ)*r^2≤1/2) (h0 : 0≤ρ) (h1 : ρ<1) (i : Fin d) (n : ℕ) :
    PolySmooth (fun y => JetCalculus.materialIter (1,0) jointSpace r (jointMean F x r) n
      (jointMean F x r i) (ρ,y)) := by
  cases n with
  | zero => exact conditionalFieldMean_component_polySmooth hF x hr hlam hl h0 h1 i
  | succ n =>
    obtain ⟨A,_,he⟩ := mean_material_representation n
    have hp := (interpolationPotential_polySmooth hF x hr hlam hl h0 h1).tensorAdjoint
      (fun j => A.slice_polySmooth hF x hr hlam hl h0 h1 (Sum.elim (fun _ => i) (fun _ => j)))
      (EuclideanSpace.basisFun (Fin d) ℝ)
    have heq : (fun y => JetCalculus.materialIter (1,0) jointSpace r (jointMean F x r) (n+1)
        (jointMean F x r i) (ρ,y))=
        fun y => ((lam:ℝ)*r)*tensorAdjoint (interpolationPotential F x r ρ)
          (EuclideanSpace.basisFun (Fin d) ℝ)
          (fun j => A.slice F x r ρ ((lam:ℝ)*r) (Sum.elim (fun _ => i) (fun _ => j))) y := by
      funext y
      rw [he hF x hr hlam hl h0 h1 i y,A.outer_slice hF x hr hlam hl h0 h1]
    rw [heq]
    exact (PolySmooth.const _).mul hp

lemma meanMaterial_square_integrable {d : ℕ} {F : Point d → ℝ} {lam : ℝ≥0}
    (hF : Primitive F lam) (x : Point d) {r ρ : ℝ} (hr : 0 < r) (hlam : 0<lam)
    (hl : (lam:ℝ)*r^2≤1/2) (h0 : 0≤ρ) (h1 : ρ<1) (i : Fin d) (n : ℕ) :
    Integrable (fun y => (JetCalculus.materialIter (1,0) jointSpace r (jointMean F x r) n
      (jointMean F x r i) (ρ,y))^2) (interpolationLaw F x r ρ) := by
  have hp := meanMaterial_slice_polySmooth hF x hr hlam hl h0 h1 i n
  rw [interpolationLaw_eq_gibbs hF x hr.le (by linarith : (lam:ℝ)*r^2<1)
    (by nlinarith : ρ^2<1)]
  simpa only [pow_two] using (hp.mul hp).integrable
    (interpolationPotential_smooth hF x hr.le hl h0 h1).continuous
    (interpolationPotential_lowerTail hF x hr.le (by linarith) h0 h1)

lemma meanMaterial_path_square_integrable {d : ℕ} {F : Point d → ℝ} {lam : ℝ≥0}
    (hF : Primitive F lam) (x : Point d) {r ρ : ℝ} (hr : 0 < r) (hlam : 0<lam)
    (hl : (lam:ℝ)*r^2≤1/2) (h0 : 0≤ρ) (h1 : ρ<1) (i : Fin d) (n : ℕ) :
    Integrable (fun z => (JetCalculus.materialIter (1,0) jointSpace r (jointMean F x r) n
      (jointMean F x r i) (ρ,fullProbabilityFlow hF x hr.le hl ρ z))^2) (stdGaussian (Point d)) := by
  have hm := fullProbabilityFlow_interpolation_closed hF x hr.le hl h0 h1
  have hc := (fullProbabilityFlow_lipschitz hF x hr.le hl ⟨h0,h1.le⟩).continuous.measurable
  have hg := (((meanMaterial_slice_polySmooth hF x hr hlam hl h0 h1 i n).smooth.continuous).pow 2).aestronglyMeasurable (μ:=(stdGaussian (Point d)).map (fullProbabilityFlow hF x hr.le hl ρ))
  apply (integrable_map_measure hg hc.aemeasurable).mp
  rw [hm]
  exact meanMaterial_square_integrable hF x hr hlam hl h0 h1 i n

lemma meanMaterial_path_norm_integrable {d : ℕ} {F : Point d → ℝ} {lam : ℝ≥0}
    (hF : Primitive F lam) (x : Point d) {r ρ : ℝ} (hr : 0 < r) (hlam : 0<lam)
    (hl : (lam:ℝ)*r^2≤1/2) (h0 : 0≤ρ) (h1 : ρ<1) (n : ℕ) :
    Integrable (fun z => ‖meanMaterialVector F x r n
      (ρ,fullProbabilityFlow hF x hr.le hl ρ z)‖^2) (stdGaussian (Point d)) := by
  simp_rw [meanMaterialVector_norm_sq]
  exact integrable_finsetSum _ (fun i _ => meanMaterial_path_square_integrable hF x hr hlam hl h0 h1 i n)

lemma meanMaterial_path_norm_integral {d : ℕ} {F : Point d → ℝ} {lam : ℝ≥0}
    (hF : Primitive F lam) (x : Point d) {r ρ : ℝ} (hr : 0 < r) (hlam : 0<lam)
    (hl : (lam:ℝ)*r^2≤1/2) (h0 : 0≤ρ) (h1 : ρ<1) (n : ℕ) :
    (∫z,‖meanMaterialVector F x r n (ρ,fullProbabilityFlow hF x hr.le hl ρ z)‖^2
      ∂stdGaussian (Point d))=
    ∑i : Fin d,∫z,(JetCalculus.materialIter (1,0) jointSpace r (jointMean F x r) n
      (jointMean F x r i) (ρ,fullProbabilityFlow hF x hr.le hl ρ z))^2 ∂stdGaussian (Point d) := by
  simp_rw [meanMaterialVector_norm_sq]
  exact integral_finsetSum _ (fun i _ => meanMaterial_path_square_integrable hF x hr hlam hl h0 h1 i n)

lemma meanMaterial_path_chain {d : ℕ} {F : Point d → ℝ} {lam : ℝ≥0}
    (hF : Primitive F lam) (x z : Point d) {r T t : ℝ} (hr : 0 ≤ r)
    (hl : (lam:ℝ)*r^2≤1/2) (hT : T<1) (ht : t∈Icc 0 T) (n : ℕ) :
    HasDerivWithinAt (fun u => meanMaterialVector F x r n (u,fullProbabilityFlow hF x hr hl u z))
      (meanMaterialVector F x r (n+1) (t,fullProbabilityFlow hF x hr hl t z)) (Icc 0 T) t := by
  have hd := hasDerivWithinAt_pi.mpr (fun i =>
    (mean_material_path_deriv hF x z hr hl ht.1 (ht.2.trans_lt hT) i n).mono
      (show Icc (0:ℝ) T⊆Icc 0 1 by intro u hu; exact ⟨hu.1,hu.2.trans hT.le⟩))
  exact (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin d => ℝ)).symm.toContinuousLinearMap.hasFDerivAt.comp_hasDerivWithinAt t hd
end LogConcaveSampling

end

end

section

noncomputable section
namespace LogConcaveSampling
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators NNReal

lemma meanMaterialVector_continuousAt {d : ℕ} {F : Point d → ℝ} {lam : ℝ≥0}
    (hF : Primitive F lam) (x : Point d) {r : ℝ} (hr : 0 ≤ r)
    (hl : (lam:ℝ)*r^2≤1/2) (n : ℕ) {p : ℝ × Point d} (h0 : -1<p.1) (h1 : p.1<1) :
    ContinuousAt (meanMaterialVector F x r n) p := by
  have hc := continuousAt_pi.mpr (fun i =>
    (JetCalculus.materialIter_timeSmooth (1,0) jointSpace r (jointMean_timeSmooth hF x hr hl)
      (jointMean_timeSmooth hF x hr hl i) n p h0 h1).continuousAt)
  exact (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin d => ℝ)).symm.continuous.continuousAt.comp hc

lemma probabilityTimeClamp_continuous (T : ℝ) : Continuous (probabilityTimeClamp T) :=
  (continuous_id.max continuous_const).min continuous_const

lemma probabilityTimeClamp_mem {T : ℝ} (hT : 0≤T) (t : ℝ) :
    probabilityTimeClamp T t∈Icc 0 T := ⟨le_min (le_max_right _ _) hT,min_le_right _ _⟩

lemma probabilityTimeClamp_eq {T t : ℝ} (ht : t∈Icc 0 T) : probabilityTimeClamp T t=t := by
  dsimp [probabilityTimeClamp]
  rw [max_eq_left ht.1,min_eq_left ht.2]

lemma meanPathJet_eq {d : ℕ} {F : Point d → ℝ} {lam : ℝ≥0}
    (hF : Primitive F lam) (x : Point d) {r T t : ℝ} (hr : 0 ≤ r)
    (hl : (lam:ℝ)*r^2≤1/2) (ht : t∈Icc 0 T) (n : ℕ) (z : Point d) :
    meanPathJet hF x hr hl T n t z=
      meanMaterialVector F x r n (t,fullProbabilityFlow hF x hr hl t z) := by
  simp only [meanPathJet,probabilityTimeClamp_eq ht]

lemma meanPathJet_time_continuous {d : ℕ} {F : Point d → ℝ} {lam : ℝ≥0}
    (hF : Primitive F lam) (x : Point d) {r T : ℝ} (hr : 0 ≤ r)
    (hl : (lam:ℝ)*r^2≤1/2) (hT0 : 0≤T) (hT1 : T<1) (n : ℕ) (z : Point d) :
    Continuous (fun t => meanPathJet hF x hr hl T n t z) := by
  have hτ := probabilityTimeClamp_continuous T
  have hp := hτ.prodMk ((fullProbabilityFlow_time_continuous hF x hr hl z).comp hτ)
  apply continuous_iff_continuousAt.mpr
  intro t
  exact (meanMaterialVector_continuousAt hF x hr hl n
    (by have hh := (probabilityTimeClamp_mem hT0 t).1; change -1<probabilityTimeClamp T t; linarith)
    ((probabilityTimeClamp_mem hT0 t).2.trans_lt hT1)).comp hp.continuousAt

lemma meanPathJet_space_continuous {d : ℕ} {F : Point d → ℝ} {lam : ℝ≥0}
    (hF : Primitive F lam) (x : Point d) {r T : ℝ} (hr : 0 ≤ r)
    (hl : (lam:ℝ)*r^2≤1/2) (hT0 : 0≤T) (hT1 : T<1) (n : ℕ) (t : ℝ) :
    Continuous (meanPathJet hF x hr hl T n t) := by
  have ht := probabilityTimeClamp_mem hT0 t
  have hp : Continuous (fun z : Point d => (probabilityTimeClamp T t,
      fullProbabilityFlow hF x hr hl (probabilityTimeClamp T t) z)) :=
    continuous_const.prodMk (fullProbabilityFlow_lipschitz hF x hr hl
    (show probabilityTimeClamp T t∈Icc 0 1 from ⟨ht.1,ht.2.trans hT1.le⟩)).continuous
  apply continuous_iff_continuousAt.mpr
  intro z
  exact (meanMaterialVector_continuousAt hF x hr hl n
    (by change -1<probabilityTimeClamp T t; linarith [ht.1]) (ht.2.trans_lt hT1)).comp hp.continuousAt

lemma meanPathJet_measurable {d : ℕ} {F : Point d → ℝ} {lam : ℝ≥0}
    (hF : Primitive F lam) (x : Point d) {r T : ℝ} (hr : 0 ≤ r)
    (hl : (lam:ℝ)*r^2≤1/2) (hT0 : 0≤T) (hT1 : T<1) (n : ℕ) :
    Measurable (fun p : ℝ × Point d => meanPathJet hF x hr hl T n p.1 p.2) :=
  measurable_uncurry_of_continuous_of_measurable
    (meanPathJet_time_continuous hF x hr hl hT0 hT1 n)
    (fun t => (meanPathJet_space_continuous hF x hr hl hT0 hT1 n t).measurable)

lemma meanPathJet_chain {d : ℕ} {F : Point d → ℝ} {lam : ℝ≥0}
    (hF : Primitive F lam) (x z : Point d) {r T t : ℝ} (hr : 0 ≤ r)
    (hl : (lam:ℝ)*r^2≤1/2) (hT1 : T<1) (ht : t∈Icc 0 T) (n : ℕ) :
    HasDerivWithinAt (fun u => meanPathJet hF x hr hl T n u z)
      (meanPathJet hF x hr hl T (n+1) t z) (Icc 0 T) t := by
  rw [meanPathJet_eq hF x hr hl ht]
  exact (meanMaterial_path_chain hF x z hr hl hT1 ht n).congr
    (fun u hu => meanPathJet_eq hF x hr hl hu n z) (meanPathJet_eq hF x hr hl ht n z)
end LogConcaveSampling

end

end

section

noncomputable section
namespace LogConcaveSampling
open Set MeasureTheory ProbabilityTheory Quadrature
open scoped Classical BigOperators NNReal

lemma inverse_sqrt_time_mono {t T : ℝ} (h0 : 0≤t) (ht : t≤T) (hT : T<1) :
    (Real.sqrt (1-t^2))⁻¹≤(Real.sqrt (1-T^2))⁻¹ := by
  have hT0 : 0≤T := h0.trans ht
  have hpos : 0<1-T^2 := by nlinarith
  have hle : 1-T^2≤1-t^2 := by nlinarith
  simpa only [one_div] using one_div_le_one_div_of_le (Real.sqrt_pos.mpr hpos)
    (Real.sqrt_le_sqrt hle)

theorem mean_path_taylor_rms (n : ℕ) :
    ∃C : ℝ,0≤C ∧ ∃k : ℕ,∀{d : ℕ} {F : Point d → ℝ} {lam : ℝ≥0},
      ∀hF : Primitive F lam,∀(x : Point d) {r T : ℝ},∀hr : 0 < r,
      0<lam → ∀hl : (lam:ℝ)*r^2≤1/2,0≤T → T<1 → 1≤d →
      ∀a b : ℝ,0≤a → a≤b → b≤T →
      Integrable (fun z => ‖meanPathJet hF x hr.le hl T 0 b z-
        chainTaylor (fun j t => meanPathJet hF x hr.le hl T j t z) n a b‖^2)
        (stdGaussian (Point d)) ∧
      (∫z,‖meanPathJet hF x hr.le hl T 0 b z-
        chainTaylor (fun j t => meanPathJet hF x hr.le hl T j t z) n a b‖^2
        ∂stdGaussian (Point d))≤((b-a)^(n+1)/(n.factorial:ℝ))^2*
        (C*((lam:ℝ)*r)*Real.sqrt (d:ℝ)*(1+Real.log ((d:ℝ)+1))^k*
          ((Real.sqrt (1-T^2))⁻¹)^(2*n+2))^2 := by
  obtain ⟨C,hC,k,hk⟩ := mean_path_polylog n
  refine ⟨C,hC,k,?_⟩
  intro d F lam hF x r T hr hlam hl hT0 hT1 hd a b ha hab hb
  have hsub : uIcc a b⊆Icc (0:ℝ) T := by
    rw [uIcc_of_le hab]
    intro t ht; exact ⟨ha.trans ht.1,ht.2.trans hb⟩
  have htI {t : ℝ} (ht : t∈Ioc a b) : t∈Icc (0:ℝ) T := ⟨ha.trans ht.1.le,ht.2.trans hb⟩
  apply chainTaylor_remainder_rms hab (sq_nonneg _) hsub
    (fun z j _ ht => meanPathJet_chain hF x z hr.le hl hT1 ht j)
    (meanPathJet_measurable hF x hr.le hl hT0 hT1 (n+1)).aestronglyMeasurable
  · intro t ht
    simp_rw [meanPathJet_eq hF x hr.le hl (htI ht)]
    exact meanMaterial_path_norm_integrable hF x hr hlam hl (htI ht).1
      ((htI ht).2.trans_lt hT1) (n+1)
  · intro t ht
    simp_rw [meanPathJet_eq hF x hr.le hl (htI ht)]
    let q := ∫z,‖meanMaterialVector F x r (n+1)
      (t,fullProbabilityFlow hF x hr.le hl t z)‖^2 ∂stdGaussian (Point d)
    have hq : 0≤q := integral_nonneg (fun _ => sq_nonneg _)
    have hbnd : Real.sqrt q≤C*((lam:ℝ)*r)*Real.sqrt (d:ℝ)*
        (1+Real.log ((d:ℝ)+1))^k*((Real.sqrt (1-T^2))⁻¹)^(2*n+2) := by
      have he : q=∑i : Fin d,∫z,(JetCalculus.materialIter (1,0) jointSpace r
          (jointMean F x r) (n+1) (jointMean F x r i)
          (t,fullProbabilityFlow hF x hr.le hl t z))^2 ∂stdGaussian (Point d) :=
        meanMaterial_path_norm_integral hF x hr hlam hl (htI ht).1 ((htI ht).2.trans_lt hT1) (n+1)
      rw [he]
      apply (hk hF x hr hlam hl (htI ht).1 ((htI ht).2.trans_lt hT1) hd).trans
      apply mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ (by positivity) (inverse_sqrt_time_mono (htI ht).1 (htI ht).2 hT1) _) _
      have hlog : 0≤Real.log ((d:ℝ)+1) := Real.log_nonneg (by linarith [Nat.cast_nonneg (α:=ℝ) d])
      positivity
    have hsq := mul_self_le_mul_self (Real.sqrt_nonneg q) hbnd
    simpa only [←sq,Real.sq_sqrt hq] using hsq
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
open Set MeasureTheory ProbabilityTheory Quadrature
open scoped Classical BigOperators NNReal

theorem mean_cell_taylor_rms (n : ℕ) :
    ∃C : ℝ,0≤C ∧ ∃k : ℕ,∀{d : ℕ} {F : Point d → ℝ} {lam : ℝ≥0},
      ∀hF : Primitive F lam,∀(x : Point d) {r : ℝ},∀hr : 0 < r,
      0<lam → ∀hl : (lam:ℝ)*r^2≤1/2,1≤d →
      ∀a b h : ℝ,0≤a → a≤b → b<1 → 0≤h → b-a≤h*(1-b) →
      ∀t∈Icc a b,
      Integrable (fun z => ‖meanPathJet hF x hr.le hl b 0 t z-
        chainTaylor (fun j v => meanPathJet hF x hr.le hl b j v z) n a t‖^2)
        (stdGaussian (Point d)) ∧
      (∫z,‖meanPathJet hF x hr.le hl b 0 t z-
        chainTaylor (fun j v => meanPathJet hF x hr.le hl b j v z) n a t‖^2
        ∂stdGaussian (Point d))≤
        (C*((lam:ℝ)*r)*Real.sqrt (d:ℝ)*(1+Real.log ((d:ℝ)+1))^k*h^(n+1))^2 := by
  obtain ⟨C,hC,k,hk⟩ := mean_path_taylor_rms n
  refine ⟨C,hC,k,?_⟩
  intro d F lam hF x r hr hlam hl hd a b h ha hab hb hh hcell t ht
  have hg := hk hF x hr hlam hl (ha.trans hab) hb hd a t ha ht.1 ht.2
  refine ⟨hg.1,hg.2.trans ?_⟩
  apply cell_taylor_budget ha ht.1 ht.2 hb hh hcell
  have hlog : 0≤Real.log ((d:ℝ)+1) := Real.log_nonneg (by linarith [Nat.cast_nonneg (α:=ℝ) d])
  positivity

lemma meanPathJet_taylor_continuous {d : ℕ} {F : Point d → ℝ} {lam : ℝ≥0}
    (hF : Primitive F lam) (x : Point d) {r b : ℝ} (hr : 0 ≤ r)
    (hl : (lam:ℝ)*r^2≤1/2) (hb0 : 0≤b) (hb1 : b<1) (n : ℕ) (a t : ℝ) :
    Continuous (fun z => chainTaylor (fun j v => meanPathJet hF x hr hl b j v z) n a t) := by
  unfold chainTaylor
  apply continuous_finsetSum
  intro j _
  exact (meanPathJet_space_continuous hF x hr hl hb0 hb1 j a).const_smul
    ((j.factorial:ℝ)⁻¹*(t-a)^j)
end LogConcaveSampling

end

end

section

noncomputable section
namespace LogConcaveSampling
open Set MeasureTheory ProbabilityTheory Quadrature
open scoped Classical BigOperators NNReal

lemma probabilityNodes_injective {n : ℕ} (hn : 0<n) : Function.Injective (probabilityNodes n) := by
  intro i j hij
  apply Fin.ext
  have hne : (n:ℝ)≠0 := by exact_mod_cast ne_of_gt hn
  have he : (i:ℝ)=(j:ℝ) := (div_left_inj' hne).mp hij
  exact_mod_cast he

theorem mean_cell_interpolation_rms (n : ℕ) (hn : 0<n) :
    ∃C : ℝ,0≤C ∧ ∃k : ℕ,∀{d : ℕ} {F : Point d → ℝ} {lam : ℝ≥0},
      ∀hF : Primitive F lam,∀(x : Point d) {r : ℝ},∀hr : 0 < r,
      0<lam → ∀hl : (lam:ℝ)*r^2≤1/2,1≤d →
      ∀a b h : ℝ,0≤a → a≤b → b<1 → 0≤h → b-a≤h*(1-b) →
      ∀t∈Icc (0:ℝ) 1,
      Integrable (fun z => ‖meanPathJet hF x hr.le hl b 0 (a+(b-a)*t) z-
        interpolation (probabilityNodes n)
          (fun i => meanPathJet hF x hr.le hl b 0 (a+(b-a)*probabilityNodes n i) z) t‖^2)
        (stdGaussian (Point d)) ∧
      (∫z,‖meanPathJet hF x hr.le hl b 0 (a+(b-a)*t) z-
        interpolation (probabilityNodes n)
          (fun i => meanPathJet hF x hr.le hl b 0 (a+(b-a)*probabilityNodes n i) z) t‖^2
        ∂stdGaussian (Point d))≤
        (C*((lam:ℝ)*r)*Real.sqrt (d:ℝ)*(1+Real.log ((d:ℝ)+1))^k*h^(n+1))^2 := by
  obtain ⟨C,hC,k,hk⟩ := mean_cell_taylor_rms n
  obtain ⟨A,hA,hA'⟩ := exists_basis_budget (probabilityNodes n)
  refine ⟨2*A*C,by positivity,k,?_⟩
  intro d F lam hF x r hr hlam hl hd a b h ha hab hb hh hcell t ht
  have hs {s : ℝ} (hs : s∈insert t (Set.range (probabilityNodes n))) : s∈Icc (0:ℝ) 1 := by
    rcases hs with he|⟨i,rfl⟩
    · simpa only [he] using ht
    · exact probabilityNodes_mem hn i
  have hscale {s : ℝ} (hs' : s∈Icc (0:ℝ) 1) : a+(b-a)*s∈Icc a b := by
    constructor <;> nlinarith [mul_nonneg (sub_nonneg.mpr hab) hs'.1,
      mul_le_mul_of_nonneg_left hs'.2 (sub_nonneg.mpr hab)]
  have htay (s : ℝ) (hs' : s∈insert t (Set.range (probabilityNodes n))) :=
    hk hF x hr hlam hl hd a b h ha hab hb hh hcell _ (hscale (hs hs'))
  have hm (s : ℝ) (_ : s∈insert t (Set.range (probabilityNodes n))) :
      AEStronglyMeasurable (fun z => meanPathJet hF x hr.le hl b 0 (a+(b-a)*s) z-
        chainTaylor (fun j v => meanPathJet hF x hr.le hl b j v z) n a (a+(b-a)*s))
        (stdGaussian (Point d)) :=
    ((meanPathJet_space_continuous hF x hr.le hl (ha.trans hab) hb 0 _).sub
      (meanPathJet_taylor_continuous hF x hr.le hl (ha.trans hab) hb n a _)).aestronglyMeasurable
  have he := cell_chain_error_rms (probabilityNodes n) (probabilityNodes_injective hn) n
    (by simp) (meanPathJet hF x hr.le hl b) a (b-a) t (sq_nonneg _) hA (hA' t ht)
    hm (fun s hs => (htay s hs).1) (fun s hs => (htay s hs).2)
  refine ⟨he.1,he.2.trans_eq ?_⟩
  ring
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

end

end OAI
end

section
-- module Solutions.OAIQ048_LC.LogConcave_Sampling_HarmonicStationaryMoment
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
open Set MeasureTheory ProbabilityTheory Quadrature
open scoped Classical BigOperators NNReal

lemma meanCell_error_measurable {d : ℕ} {F : Point d → ℝ} {lam : ℝ≥0}
    (hF : Primitive F lam) (x : Point d) {r b : ℝ} (hr : 0 ≤ r)
    (hl : (lam:ℝ)*r^2≤1/2) (hb0 : 0≤b) (hb1 : b<1) (n : ℕ) (a : ℝ) :
    Measurable (fun p : ℝ × Point d =>
      meanPathJet hF x hr hl b 0 (a+(b-a)*p.1) p.2-
      interpolation (probabilityNodes n)
        (fun i => meanPathJet hF x hr hl b 0 (a+(b-a)*probabilityNodes n i) p.2) p.1) := by
  apply measurable_uncurry_of_continuous_of_measurable (u:=fun t z =>
    meanPathJet hF x hr hl b 0 (a+(b-a)*t) z-
    interpolation (probabilityNodes n)
      (fun i => meanPathJet hF x hr hl b 0 (a+(b-a)*probabilityNodes n i) z) t)
  · intro z
    exact ((meanPathJet_time_continuous hF x hr hl hb0 hb1 0 z).comp
      (continuous_const.add (continuous_const.mul continuous_id))).sub
      (interpolation_continuous _ _)
  · intro t
    apply Continuous.measurable
    apply (meanPathJet_space_continuous hF x hr hl hb0 hb1 0 _).sub
    apply continuous_finsetSum
    intro i _
    exact (meanPathJet_space_continuous hF x hr hl hb0 hb1 0 _).const_smul (basis (probabilityNodes n) i t)

end LogConcaveSampling

end

end

section

noncomputable section
namespace LogConcaveSampling
open Set MeasureTheory ProbabilityTheory Quadrature
open scoped Classical BigOperators NNReal

lemma meanCellResidual_measurable {d : ℕ} {F : Point d → ℝ} {lam : ℝ≥0}
    (hF : Primitive F lam) (x : Point d) {r b θ : ℝ} (hr : 0 ≤ r)
    (hl : (lam:ℝ)*r^2≤1/2) (hb0 : 0≤b) (hb1 : b<1) (n : ℕ) (a : ℝ) (hθ : 0≤θ) :
    StronglyMeasurable (meanCellResidual hF x hr hl n a b θ) := by
  unfold meanCellResidual
  simp only [intervalIntegral.integral_of_le hθ]
  exact (meanCell_error_measurable hF x hr hl hb0 hb1 n a).stronglyMeasurable.integral_prod_left'

lemma meanCellResidual_eq {d : ℕ} {F : Point d → ℝ} {lam : ℝ≥0}
    (hF : Primitive F lam) (x : Point d) {r b : ℝ} (hr : 0 ≤ r)
    (hl : (lam:ℝ)*r^2≤1/2) (hb0 : 0≤b) (hb1 : b<1) (n : ℕ) (a θ : ℝ) (z : Point d) :
    meanCellResidual hF x hr hl n a b θ z=
      (∫t in 0..θ,meanPathJet hF x hr hl b 0 (a+(b-a)*t) z)-
        cellQuadrature (probabilityNodes n)
          (fun i => meanPathJet hF x hr hl b 0 (a+(b-a)*probabilityNodes n i) z) 1 θ := by
  rw [cellQuadrature_eq_integral,one_smul,meanCellResidual,intervalIntegral.integral_sub]
  · exact ((meanPathJet_time_continuous hF x hr hl hb0 hb1 0 z).comp
      (continuous_const.add (continuous_const.mul continuous_id))).intervalIntegrable 0 θ
  · exact (interpolation_continuous _ _).intervalIntegrable 0 θ

theorem mean_cell_residual_rms (n : ℕ) (hn : 0<n) :
    ∃C : ℝ,0≤C ∧ ∃k : ℕ,∀{d : ℕ} {F : Point d → ℝ} {lam : ℝ≥0},
      ∀hF : Primitive F lam,∀(x : Point d) {r : ℝ},∀hr : 0 < r,
      0<lam → ∀hl : (lam:ℝ)*r^2≤1/2,1≤d →
      ∀a b h : ℝ,0≤a → a≤b → b<1 → 0≤h → b-a≤h*(1-b) →
      ∀θ∈Icc (0:ℝ) 1,
      Integrable (fun z => ‖meanCellResidual hF x hr.le hl n a b θ z‖^2)
        (stdGaussian (Point d)) ∧
      (∫z,‖meanCellResidual hF x hr.le hl n a b θ z‖^2 ∂stdGaussian (Point d))≤
        (C*((lam:ℝ)*r)*Real.sqrt (d:ℝ)*(1+Real.log ((d:ℝ)+1))^k*h^(n+1))^2 := by
  obtain ⟨C,hC,k,hk⟩ := mean_cell_interpolation_rms n hn
  refine ⟨C,hC,k,?_⟩
  intro d F lam hF x r hr hlam hl hd a b h ha hab hb hh hcell θ hθ
  have he := cellQuadrature_error_rms (ν:=stdGaussian (Point d)) (probabilityNodes n)
    (fun t z => meanPathJet hF x hr.le hl b 0 (a+(b-a)*t) z) 1 hθ.1
    (fun z => ((meanPathJet_time_continuous hF x hr.le hl (ha.trans hab) hb 0 z).comp
      (continuous_const.add (continuous_const.mul continuous_id))).intervalIntegrable 0 θ)
    (meanCell_error_measurable hF x hr.le hl (ha.trans hab) hb n a).aestronglyMeasurable
    (fun t ht => (hk hF x hr hlam hl hd a b h ha hab hb hh hcell t ⟨ht.1.le,ht.2.trans hθ.2⟩).1)
    (fun t ht => (hk hF x hr hlam hl hd a b h ha hab hb hh hcell t ⟨ht.1.le,ht.2.trans hθ.2⟩).2)
  simp only [one_smul,one_pow,one_mul] at he
  simp_rw [meanCellResidual_eq hF x hr.le hl (ha.trans hab) hb]
  refine ⟨he.1,he.2.trans ?_⟩
  apply mul_le_of_le_one_left (sq_nonneg _)
  nlinarith [hθ.1,hθ.2]
end LogConcaveSampling

end

end

section

noncomputable section
namespace LogConcaveSampling
open Set MeasureTheory ProbabilityTheory Quadrature
open scoped Classical BigOperators NNReal

lemma affineUnit_mem {a b s : ℝ} (hab : a≤b) (hs : s∈Icc (0:ℝ) 1) :
    a+(b-a)*s∈Icc a b := by
  constructor <;> nlinarith [mul_nonneg (sub_nonneg.mpr hab) hs.1,
    mul_le_mul_of_nonneg_left hs.2 (sub_nonneg.mpr hab)]

lemma meanPathJet_cutoff {d : ℕ} {F : Point d → ℝ} {lam : ℝ≥0}
    (hF : Primitive F lam) (x : Point d) {r b T t : ℝ} (hr : 0 ≤ r)
    (hl : (lam:ℝ)*r^2≤1/2) (hbT : b≤T) (ht : t∈Icc 0 b) (n : ℕ) (z : Point d) :
    meanPathJet hF x hr hl T n t z=meanPathJet hF x hr hl b n t z := by
  rw [meanPathJet_eq hF x hr hl ⟨ht.1,ht.2.trans hbT⟩,meanPathJet_eq hF x hr hl ht]

lemma meanCellResidual_cutoff {d : ℕ} {F : Point d → ℝ} {lam : ℝ≥0}
    (hF : Primitive F lam) (x : Point d) {r a b T θ : ℝ} (hr : 0 ≤ r)
    (hl : (lam:ℝ)*r^2≤1/2) (ha : 0≤a) (hab : a≤b) (hbT : b≤T)
    (n : ℕ) (hn : 0<n) (hθ : θ∈Icc (0:ℝ) 1) (z : Point d) :
    (∫s in 0..θ,meanPathJet hF x hr hl T 0 (a+(b-a)*s) z-
      interpolation (probabilityNodes n)
        (fun j => meanPathJet hF x hr hl T 0 (a+(b-a)*probabilityNodes n j) z) s)=
      meanCellResidual hF x hr hl n a b θ z := by
  have ht {s : ℝ} (hs : s∈Icc (0:ℝ) 1) : a+(b-a)*s∈Icc 0 b :=
    ⟨ha.trans (affineUnit_mem hab hs).1,(affineUnit_mem hab hs).2⟩
  have he : (fun j => meanPathJet hF x hr hl T 0 (a+(b-a)*probabilityNodes n j) z)=
      (fun j => meanPathJet hF x hr hl b 0 (a+(b-a)*probabilityNodes n j) z) :=
    funext (fun j => meanPathJet_cutoff hF x hr hl hbT (ht (probabilityNodes_mem hn j)) 0 z)
  rw [he]
  unfold meanCellResidual
  apply intervalIntegral.integral_congr
  intro s hs
  rw [uIcc_of_le hθ.1] at hs
  dsimp only
  rw [meanPathJet_cutoff hF x hr hl hbT (ht ⟨hs.1,hs.2.trans hθ.2⟩)]

lemma probabilityMeanDefect_eq {d : ℕ} {F : Point d → ℝ} {lam : ℝ≥0}
    (hF : Primitive F lam) (x : Point d) {r T h : ℝ} (hr : 0 ≤ r)
    (hl : (lam:ℝ)*r^2≤1/2) (hT0 : 0<T) (hT1 : T<1) (hh : 0<h)
    (n : ℕ) (hn : 0<n) (i : ProbabilityNode T h n) (z : Point d) :
    probabilityMeanDefect hF x hr hl T h n i z=
      ∑c,probabilityCellLength T h c • meanCellResidual hF x hr hl n
        (logMeshNode T h c.val) (logMeshNode T h (c.val+1)) (compositeAngle (probabilityNodes n) i c) z := by
  have he := compositeQuadrature_defect (probabilityNodes n) (logMeshNode T h)
    (fun t => meanPathJet hF x hr hl T 0 t z)
    (meanPathJet_time_continuous hF x hr hl hT0.le hT1 0 z) i
  simp only [logMeshNode_zero] at he
  change probabilityMeanDefect hF x hr hl T h n i z=_ at he
  rw [he]
  apply Finset.sum_congr rfl
  intro c hc
  apply congrArg (fun v => probabilityCellLength T h c • v)
  exact meanCellResidual_cutoff hF x hr hl
    (logMeshNode_mem hT0 hT1 hh c.2.le).1
    (logMeshNode_strictMono hT0 hT1 hh (Nat.lt_succ_self _)).le
    (logMeshNode_mem hT0 hT1 hh (Nat.succ_le_of_lt c.2)).2 n hn
    (compositeAngle_mem (probabilityNodes_mem hn) i c) z

theorem probability_mean_defect_rms (n : ℕ) (hn : 0<n) :
    ∃C : ℝ,0≤C ∧ ∃k : ℕ,∀{d : ℕ} {F : Point d → ℝ} {lam : ℝ≥0},
      ∀hF : Primitive F lam,∀(x : Point d) {r : ℝ},∀hr : 0 < r,
      0<lam → ∀hl : (lam:ℝ)*r^2≤1/2,1≤d →
      ∀{T h : ℝ},0<T → T<1 → 0<h → h≤Real.log 2 → ∀i : ProbabilityNode T h n,
      Integrable (fun z => ‖probabilityMeanDefect hF x hr.le hl T h n i z‖^2)
        (stdGaussian (Point d)) ∧
      (∫z,‖probabilityMeanDefect hF x hr.le hl T h n i z‖^2 ∂stdGaussian (Point d))≤
        (C*((lam:ℝ)*r)*Real.sqrt (d:ℝ)*(1+Real.log ((d:ℝ)+1))^k*(2*h)^(n+1))^2 := by
  obtain ⟨C,hC,k,hk⟩ := mean_cell_residual_rms n hn
  refine ⟨C,hC,k,?_⟩
  intro d F lam hF x r hr hlam hl hd T h hT0 hT1 hh hsmall i
  simp_rw [probabilityMeanDefect_eq hF x hr.le hl hT0 hT1 hh n hn]
  have hcell (c : Fin (logMeshCount T h)) := hk hF x hr hlam hl hd
    (logMeshNode T h c.val) (logMeshNode T h (c.val+1)) (2*h)
    (logMeshNode_mem hT0 hT1 hh c.2.le).1
    (logMeshNode_strictMono hT0 hT1 hh (Nat.lt_succ_self _)).le
    ((logMeshNode_mem hT0 hT1 hh (Nat.succ_le_of_lt c.2)).2.trans_lt hT1)
    (by positivity) (logMeshCell_upper_right hT0 hT1 hh hsmall c.val)
    (compositeAngle (probabilityNodes n) i c) (compositeAngle_mem (probabilityNodes_mem hn) i c)
  apply composite_error_rms _ _ (fun c => (probabilityCellLength_pos hT0 hT1 hh c).le)
    (by rw [probabilityCellLength_sum hT0 hT1 hh]; exact hT1.le) (sq_nonneg _)
  · intro c
    exact (meanCellResidual_measurable hF x hr.le hl
      (logMeshNode_mem hT0 hT1 hh (Nat.succ_le_of_lt c.2)).1
      ((logMeshNode_mem hT0 hT1 hh (Nat.succ_le_of_lt c.2)).2.trans_lt hT1) n _
      (compositeAngle_mem (probabilityNodes_mem hn) i c).1).aestronglyMeasurable
  · exact fun c => (hcell c).1
  · exact fun c => (hcell c).2
end LogConcaveSampling

end

end

section

noncomputable section
namespace LogConcaveSampling
open Set MeasureTheory
open scoped Classical BigOperators NNReal RealInnerProductSpace

lemma meanMaterialVector_zero {d : ℕ} (F : Point d → ℝ) (x : Point d)
    (r t : ℝ) (y : Point d) :
    meanMaterialVector F x r 0 (t,y)=conditionalFieldMean F x r t y := by
  ext i
  change inner ℝ (EuclideanSpace.basisFun (Fin d) ℝ i) (conditionalFieldMean F x r t y)=_
  simp only [EuclideanSpace.basisFun_inner]

lemma meanPathJet_zero {d : ℕ} {F : Point d → ℝ} {lam : ℝ≥0}
    (hF : Primitive F lam) (x : Point d) {r T t : ℝ} (hr : 0 ≤ r)
    (hl : (lam:ℝ)*r^2≤1/2) (ht : t∈Icc 0 T) (z : Point d) :
    meanPathJet hF x hr hl T 0 t z=
      conditionalFieldMean F x r t (fullProbabilityFlow hF x hr hl t z) := by
  rw [meanPathJet_eq hF x hr hl ht,meanMaterialVector_zero]

lemma probabilityFlow_mean_integral {d : ℕ} {F : Point d → ℝ} {lam : ℝ≥0}
    (hF : Primitive F lam) (x : Point d) {r T t : ℝ} (hr : 0 ≤ r)
    (hl : (lam:ℝ)*r^2≤1/2) (hT0 : 0≤T) (hT1 : T<1)
    (ht : t∈Icc 0 T) (z : Point d) :
    fullProbabilityFlow hF x hr hl t z=z-r • (∫s in 0..t,meanPathJet hF x hr hl T 0 s z) := by
  have hc := meanPathJet_time_continuous hF x hr hl hT0 hT1 0 z
  have he := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le ht.1
    (fullProbabilityFlow_time_continuous hF x hr hl z).continuousOn
    (f':=fun s => -r • meanPathJet hF x hr hl T 0 s z)
    (fun s hs => by
      rw [meanPathJet_zero hF x hr hl ⟨hs.1.le,hs.2.le.trans ht.2⟩]
      exact (fullProbabilityFlow_deriv hF x z hr hl hs.1.le ((hs.2.trans_le ht.2).trans hT1)).hasDerivAt
        (Icc_mem_nhds hs.1 ((hs.2.trans_le ht.2).trans hT1)))
    ((hc.const_smul (-r)).intervalIntegrable 0 t)
  rw [intervalIntegral.integral_smul,fullProbabilityFlow_initial] at he
  simp only [Function.id_def,neg_smul] at he
  exact (sub_eq_iff_eq_add.mp he.symm).trans (by abel)

lemma probabilityPicard_exact_defect {d : ℕ} {F : Point d → ℝ} {lam : ℝ≥0}
    (hF : Primitive F lam) (x : Point d) {r T h : ℝ} (hr : 0 ≤ r)
    (hl : (lam:ℝ)*r^2≤1/2) (hT0 : 0<T) (hT1 : T<1) (hh : 0<h)
    (n : ℕ) (hn : 0<n) (i : ProbabilityNode T h n) (z : Point d) :
    FinitePicard.step (probabilityWeight T h n)
      (fun j => probabilityMeanVelocity F x r (probabilityNodeTime T h n j))
      (fun _ => z) (fun j => fullProbabilityFlow hF x hr hl (probabilityNodeTime T h n j) z) i-
      fullProbabilityFlow hF x hr hl (probabilityNodeTime T h n i) z=
      r • probabilityMeanDefect hF x hr hl T h n i z := by
  have hj (j : ProbabilityNode T h n) := probabilityNodeTime_mem hT0 hT1 hh hn j
  have hv (j : ProbabilityNode T h n) :
      probabilityMeanVelocity F x r (probabilityNodeTime T h n j)
        (fullProbabilityFlow hF x hr hl (probabilityNodeTime T h n j) z)=
      -r • meanPathJet hF x hr hl T 0 (probabilityNodeTime T h n j) z := by
    rw [meanPathJet_zero hF x hr hl (hj j)]
    rfl
  change z+∑j,probabilityWeight T h n i j •
    probabilityMeanVelocity F x r (probabilityNodeTime T h n j)
        (fullProbabilityFlow hF x hr hl (probabilityNodeTime T h n j) z)-_=_
  simp_rw [hv,smul_comm (probabilityWeight T h n i _) (-r)]
  rw [←Finset.smul_sum,probabilityFlow_mean_integral hF x hr hl hT0.le hT1 (hj i)]
  unfold probabilityMeanDefect
  rw [smul_sub,neg_smul]
  abel
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

lemma probabilityInitialRms_sq {d : ℕ} (F : Point d → ℝ) (x : Point d)
    (lam : ℝ≥0) (r : ℝ) :
    probabilityInitialRms F x lam r^2=
      2*(terminalTransportConstant*(r*‖primitiveField F x r 0‖+(lam:ℝ)*r^2*Real.pi*Real.sqrt d))^2+
      2*(terminalTransportConstant*((lam:ℝ)*r^2))^2*d := Real.sq_sqrt (by positivity)

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

lemma step_reanchor_defect (w : I → I → ℝ) (φ : I → E → E) (e : I → E)
    (z : E) (s i : I) :
    step (reanchorWeight w s) φ (fun _ => e s) e i-e i=
      (step w φ (fun _ => z) e i-e i)-(step w φ (fun _ => z) e s-e s) := by
  simp only [step,correction,reanchorWeight,Pi.add_apply,sub_smul,Finset.sum_sub_distrib]
  abel

omit [NormedSpace ℝ E] in
lemma integral_norm_sub_sq_bound [MeasurableSpace Ω] (ν : Measure Ω) (f g : Ω → E)
    {D H : ℝ} (hf : Integrable (fun ω => ‖f ω‖^2) ν)
    (hg : Integrable (fun ω => ‖g ω‖^2) ν)
    (hb : (∫ω,‖f ω‖^2 ∂ν)≤D) (hc : (∫ω,‖g ω‖^2 ∂ν)≤H) :
    (∫ω,‖f ω-g ω‖^2 ∂ν)≤2*D+2*H := by
  have hp (ω : Ω) : ‖f ω-g ω‖^2≤2*‖f ω‖^2+2*‖g ω‖^2 := by
    have he := norm_sub_le (f ω) (g ω)
    have hn := norm_nonneg (f ω-g ω)
    nlinarith [sq_nonneg (‖f ω‖-‖g ω‖),norm_nonneg (f ω),norm_nonneg (g ω)]
  have he := integral_mono_of_nonneg (Filter.Eventually.of_forall (fun ω => sq_nonneg ‖f ω-g ω‖))
    ((hf.const_mul 2).add (hg.const_mul 2)) (Filter.Eventually.of_forall hp)
  simp only [Pi.add_apply] at he
  rw [integral_add (hf.const_mul 2) (hg.const_mul 2),integral_const_mul,integral_const_mul] at he
  linarith
end LogConcaveSampling.FinitePicard

end

end

section

noncomputable section
namespace LogConcaveSampling
open Set MeasureTheory ProbabilityTheory FinitePicard
open scoped Classical BigOperators NNReal

theorem probabilityAnchored_rms (n : ℕ) (hn : 0<n) :
    ∃A : ℝ≥0,∃C : ℝ,0≤C ∧ ∃k : ℕ,∀{d : ℕ} {F : Point d → ℝ} {lam : ℝ≥0},
      ∀hF : Primitive F lam,∀(x : Point d) {r : ℝ},∀hr : 0 < r,
      0<lam → ∀hl : (lam:ℝ)*r^2≤1/2,1≤d →
      ∀{T h : ℝ},0<T → T<1 → 0<h → h≤Real.log 2 →
      A*probabilityMeanLipschitz lam r≤1/2 → ∀N : ℕ,∀s i : ProbabilityNode T h n,
      Integrable (fun z => ‖probabilityAnchoredPicard F x r T h n N s
          (fullProbabilityFlow hF x hr.le hl (probabilityNodeTime T h n s) z) i-
        fullProbabilityFlow hF x hr.le hl (probabilityNodeTime T h n i) z‖^2) (stdGaussian (Point d)) ∧
      (∫z,‖probabilityAnchoredPicard F x r T h n N s
          (fullProbabilityFlow hF x hr.le hl (probabilityNodeTime T h n s) z) i-
        fullProbabilityFlow hF x hr.le hl (probabilityNodeTime T h n i) z‖^2 ∂stdGaussian (Point d))≤
        (4*C*((lam:ℝ)*r^2)*Real.sqrt d*(1+Real.log ((d:ℝ)+1))^k*(2*h)^(n+1)+
          (A*probabilityMeanLipschitz lam r:ℝ≥0)^N*(2*probabilityInitialRms F x lam r))^2 := by
  obtain ⟨A,hA,hA'⟩ := probabilityWeight_budget n hn
  obtain ⟨C,hC,k,hk⟩ := probability_mean_defect_rms n hn
  refine ⟨⟨2*A,by positivity⟩,C,hC,k,?_⟩
  intro d F lam hF x r hr hlam hl hd T h hT0 hT1 hh hsmall hq N s i
  have hi (j : ProbabilityNode T h n) := probabilityNodeTime_mem hT0 hT1 hh hn j
  have hi' (j : ProbabilityNode T h n) : probabilityNodeTime T h n j∈Icc (0:ℝ) 1 :=
    ⟨(hi j).1,(hi j).2.trans hT1.le⟩
  let e := fun j : ProbabilityNode T h n => fullProbabilityFlow hF x hr.le hl (probabilityNodeTime T h n j)
  let φ := fun j : ProbabilityNode T h n => probabilityMeanVelocity F x r (probabilityNodeTime T h n j)
  let D := C*((lam:ℝ)*r^2)*Real.sqrt d*(1+Real.log ((d:ℝ)+1))^k*(2*h)^(n+1)
  have hlog : 0≤Real.log ((d:ℝ)+1) := Real.log_nonneg (by have := Nat.cast_nonneg (α:=ℝ) d; linarith)
  have hD : 0≤D := by dsimp [D]; positivity
  have hφ (j : ProbabilityNode T h n) := probabilityMeanVelocity_lipschitz hF x hr.le hl
    (hi j).1 ((hi j).2.trans_lt hT1)
  have hd0 (j : ProbabilityNode T h n) :
      Integrable (fun z => ‖step (probabilityWeight T h n) φ (fun _ => z) (fun j => e j z) j-e j z‖^2)
        (stdGaussian (Point d)) ∧
      (∫z,‖step (probabilityWeight T h n) φ (fun _ => z) (fun j => e j z) j-e j z‖^2
        ∂stdGaussian (Point d))≤D^2 := by
    dsimp only [φ,e]
    simp_rw [probabilityPicard_exact_defect hF x hr.le hl hT0 hT1 hh n hn,
      norm_smul,Real.norm_eq_abs,abs_of_pos hr,mul_pow]
    refine ⟨(hk hF x hr hlam hl hd hT0 hT1 hh hsmall j).1.const_mul (r^2),?_⟩
    rw [integral_const_mul]
    convert mul_le_mul_of_nonneg_left (hk hF x hr hlam hl hd hT0 hT1 hh hsmall j).2 (sq_nonneg r) using 1 <;>
      first | rfl | (dsimp [D]; ring)
  have hdef (j : ProbabilityNode T h n) :
      (∫z,‖step (reanchorWeight (probabilityWeight T h n) s) φ (fun _ => e s z)
        (fun j => e j z) j-e j z‖^2 ∂stdGaussian (Point d))≤(2*D)^2 := by
    have heq (z : Point d) := step_reanchor_defect (probabilityWeight T h n) φ (fun j => e j z) z s j
    simp_rw [heq]
    exact (integral_norm_sub_sq_bound _ _ _ (hd0 j).1 (hd0 s).1 (hd0 j).2 (hd0 s).2).trans (by ring_nf; rfl)
  have hinit (j : ProbabilityNode T h n) :
      (∫z,‖e s z-e j z‖^2 ∂stdGaussian (Point d))≤(2*probabilityInitialRms F x lam r)^2 := by
    have hj := probabilityFlow_initial_rms hF x hr.le hl (hi' j)
    have hs := probabilityFlow_initial_rms hF x hr.le hl (hi' s)
    rw [←probabilityInitialRms_sq] at hj hs
    have heq (z : Point d) : e s z-e j z=(z-e j z)-(z-e s z) := by abel
    simp_rw [heq]
    exact (integral_norm_sub_sq_bound _ _ _ hj.1 hs.1 hj.2 hs.2).trans (by ring_nf; rfl)
  have he := nodes_rms (ν:=stdGaussian (Point d)) (A:=⟨2*A,by positivity⟩)
    (reanchorWeight (probabilityWeight T h n) s) φ hφ (fun _ => e s) e
    (fun _ => gaussian_lipschitz_memLp (fullProbabilityFlow_lipschitz hF x hr.le hl (hi' s)))
    (fun j => gaussian_lipschitz_memLp (fullProbabilityFlow_lipschitz hF x hr.le hl (hi' j)))
    (reanchorWeight_budget (probabilityWeight T h n) (hA' hT0 hT1 hh) s) hq
    (show 0≤2*D by positivity) (show 0≤2*probabilityInitialRms F x lam r by
      exact mul_nonneg (by norm_num) (probabilityInitialRms_nonneg F x lam r)) hdef hinit N i
  have heq : 2*(2*D)=4*C*((lam:ℝ)*r^2)*Real.sqrt d*(1+Real.log ((d:ℝ)+1))^k*(2*h)^(n+1) := by
    dsimp [D]; ring
  rw [heq] at he
  simpa only [probabilityAnchoredPicard,nodes_eq_iterate,φ,e] using he
end LogConcaveSampling

end

end

end

end OAI
end

section
-- module Solutions.OAIQ048_LC.LogConcave_Sampling_ProbabilityTransportTrajectory
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

variable {d : ℕ} {F : Point d → ℝ} {lam : ℝ≥0}
  (hF : Primitive F lam) (x : Point d) {r T : ℝ} (hr : 0 ≤ r)
  (hl : (lam:ℝ)*r^2≤1/2) (hT0 : 0≤T) (hT1 : T<1)

lemma probabilityTransport_zero_trajectory (t : Icc (0:ℝ) T) (z : Point d) :
    probabilityTransport hF x hr hl hT0 hT1 ⟨0,le_rfl,hT0⟩ t z=
      fullProbabilityFlow hF x hr hl t z := by
  apply GlobalODE.flow_restrict
    (clampedProbabilityVelocity_continuous hF x hr hl hT0 hT1)
    (fullProbabilityVelocity_continuous hF x hr hl)
    (fun u _ => clampedProbabilityVelocity_lipschitz hF x hr hl hT0 hT1 u)
    (fun u _ => fullProbabilityVelocity_lipschitz hF x hr hl u)
    (Icc_subset_Icc_right hT1.le)
  intro u hu y
  rw [clampedProbabilityVelocity_eq F x r T hT0 hu,
    fullProbabilityVelocity_eq F x r hu.1 (hu.2.trans_lt hT1)]

lemma probabilityTransport_trajectory (s t : Icc (0:ℝ) T) (z : Point d) :
    probabilityTransport hF x hr hl hT0 hT1 s t
      (fullProbabilityFlow hF x hr hl s z)=fullProbabilityFlow hF x hr hl t z := by
  rw [←probabilityTransport_zero_trajectory hF x hr hl hT0 hT1 s z,
    probabilityTransport_cocycle,probabilityTransport_zero_trajectory]

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

theorem probabilityAnchored_marginal_rms_oai (n : ℕ) (hn : 0<n) :
    ∃A : ℝ≥0,∃C : ℝ,0≤C ∧ ∃k : ℕ,∀{d : ℕ} {F : Point d → ℝ} {lam : ℝ≥0},
      ∀hF : Primitive F lam,∀(x : Point d) {r : ℝ},∀hr : 0 < r,
      0<lam → ∀hl : (lam:ℝ)*r^2≤1/2,1≤d →
      ∀{T h : ℝ},∀hT0 : 0<T,∀hT1 : T<1,∀hh : 0<h,h≤Real.log 2 →
      A*probabilityMeanLipschitz lam r≤1/2 → ∀N : ℕ,∀s i : ProbabilityNode T h n,
      let S : Icc (0:ℝ) T := ⟨probabilityNodeTime T h n s,probabilityNodeTime_mem hT0 hT1 hh hn s⟩
      let I : Icc (0:ℝ) T := ⟨probabilityNodeTime T h n i,probabilityNodeTime_mem hT0 hT1 hh hn i⟩
      Integrable (fun y => ‖probabilityAnchoredPicard F x r T h n N s y i-
        probabilityTransport hF x hr.le hl hT0.le hT1 S I y‖^2)
          (interpolationLaw F x r S) ∧
      (∫y,‖probabilityAnchoredPicard F x r T h n N s y i-
        probabilityTransport hF x hr.le hl hT0.le hT1 S I y‖^2
          ∂interpolationLaw F x r S)≤
        (4*C*((lam:ℝ)*r^2)*Real.sqrt d*(1+Real.log ((d:ℝ)+1))^k*(2*h)^(n+1)+
          (A*probabilityMeanLipschitz lam r:ℝ≥0)^N*(2*probabilityInitialRms F x lam r))^2 := by
  obtain ⟨A,C,hC,k,h⟩ := probabilityAnchored_rms n hn
  refine ⟨A,C,hC,k,?_⟩
  intro d F lam hF x r hr hlam hl hd T hstep hT0 hT1 hh hsmall hq N s i
  dsimp only
  let S : Icc (0:ℝ) T := ⟨probabilityNodeTime T hstep n s,probabilityNodeTime_mem hT0 hT1 hh hn s⟩
  let I : Icc (0:ℝ) T := ⟨probabilityNodeTime T hstep n i,probabilityNodeTime_mem hT0 hT1 hh hn i⟩
  let E := fun y => ‖probabilityAnchoredPicard F x r T hstep n N s y i-
    probabilityTransport hF x hr.le hl hT0.le hT1 S I y‖^2
  have hE : Continuous E := ((probabilityAnchored_continuous hF x hr.le hl hT0 hT1 hh n hn N s i).sub
    (probabilityTransport_continuous hF x hr.le hl hT0.le hT1 S I)).norm.pow 2
  have hm := fullProbabilityFlow_interpolation_closed hF x hr.le hl S.2.1 (S.2.2.trans_lt hT1)
  have hf := (fullProbabilityFlow_lipschitz hF x hr.le hl ⟨S.2.1,S.2.2.trans hT1.le⟩).continuous.measurable
  have heq (z : Point d) : E (fullProbabilityFlow hF x hr.le hl S z)=
      ‖probabilityAnchoredPicard F x r T hstep n N s
          (fullProbabilityFlow hF x hr.le hl S z) i-fullProbabilityFlow hF x hr.le hl I z‖^2 := by
    dsimp only [E]
    rw [probabilityTransport_trajectory]
  have he := h hF x hr hlam hl hd hT0 hT1 hh hsmall hq N s i
  change Integrable E (interpolationLaw F x r S) ∧ _
  constructor
  · rw [←hm]
    apply (integrable_map_measure hE.aestronglyMeasurable hf.aemeasurable).mpr
    simpa only [Function.comp_def,heq] using he.1
  · change (∫y,E y ∂interpolationLaw F x r S)≤_
    rw [←hm,integral_map hf.aemeasurable hE.aestronglyMeasurable]
    simpa only [heq] using he.2

end LogConcaveSampling

end

end

end

end OAI
end

theorem solution : type_of% @OAI.LogConcaveSampling.probabilityAnchored_marginal_rms_oai := @OAI.LogConcaveSampling.probabilityAnchored_marginal_rms_oai
