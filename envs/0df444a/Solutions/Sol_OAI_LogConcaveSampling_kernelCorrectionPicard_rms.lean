-- Prove2me | solution 1 for OAI.LogConcaveSampling.kernelCorrectionPicard_rms
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-27T13:58:38.063599+00:00
-- url     : https://prove2.me/submissions/8d6dcdf6-34e9-48d8-82d5-ffa5e1b76fc0

import Mathlib
import Definitions.Def_LogConcaveQuery
import Definitions.Def_OAIQ048L004
import Theorems.Thm_OAI_LogConcaveSampling_probabilityAnchored_marginal_rms
import Theorems.Thm_OAI_LogConcaveSampling_stationary_lie_taylor_rms

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

include hF hr hl in
lemma interpolationLaw_zero : interpolationLaw F x r 0=stdGaussian (Point d) := by
  let := probability_gibbs_of_partition
    (partition_pos_of_continuous (hF.continuous_potential x r)).ne'
    (partition_ne_top_of_integrable (hF.integrable_exp_neg_potential x hr (by linarith)))
  simp only [interpolationLaw,zero_smul,zero_pow (by norm_num : (2:ℕ)≠0),sub_zero,
    Real.sqrt_one,one_smul,zero_add]
  simpa only [measure_univ,one_smul] using (Measure.map_snd_prod (μ:=gibbs (primitivePotential F x r)) (ν:=stdGaussian (Point d)))

lemma probabilityTransport_from_zero (t : Icc (0:ℝ) T) :
    (stdGaussian (Point d)).map
      (probabilityTransport hF x hr hl hT0 hT1 ⟨0,le_rfl,hT0⟩ t)=
        interpolationLaw F x r t := by
  by_cases ht : (t:ℝ)=0
  · have he : t=⟨0,le_rfl,hT0⟩ := Subtype.ext ht
    rw [he]
    have hz : probabilityTransport hF x hr hl hT0 hT1 ⟨0,le_rfl,hT0⟩ ⟨0,le_rfl,hT0⟩=id :=
      funext (probabilityTransport_initial hF x hr hl hT0 hT1 _)
    rw [hz,Measure.map_id,interpolationLaw_zero hF x hr hl]
  · have htp : 0<(t:ℝ) := lt_of_le_of_ne t.2.1 (Ne.symm ht)
    have ht1 : (t:ℝ)<1 := t.2.2.trans_lt hT1
    have he : probabilityTransport hF x hr hl hT0 hT1 ⟨0,le_rfl,hT0⟩ t=
        probabilityFlow hF x hr hl htp.le ht1 := by
      funext z
      exact (GlobalODE.flow_restrict
        (clampedProbabilityVelocity_continuous hF x hr hl htp.le ht1)
        (clampedProbabilityVelocity_continuous hF x hr hl hT0 hT1)
        (fun u _ => clampedProbabilityVelocity_lipschitz hF x hr hl htp.le ht1 u)
        (fun u _ => clampedProbabilityVelocity_lipschitz hF x hr hl hT0 hT1 u)
        (Icc_subset_Icc_right t.2.2)
        (fun u hu y => by rw [clampedProbabilityVelocity_eq F x r t htp.le hu,
          clampedProbabilityVelocity_eq F x r T hT0 ⟨hu.1,hu.2.trans t.2.2⟩])
        ⟨0,le_rfl,htp.le⟩ ⟨t,htp.le,le_rfl⟩ z).symm
    rw [he]
    exact probabilityFlow_pushforward hF x hr hl htp ht1

theorem probabilityTransport_pushforward (s t : Icc (0:ℝ) T) :
    (interpolationLaw F x r s).map (probabilityTransport hF x hr hl hT0 hT1 s t)=
      interpolationLaw F x r t := by
  rw [←probabilityTransport_from_zero hF x hr hl hT0 hT1 s,
    Measure.map_map (probabilityTransport_continuous hF x hr hl hT0 hT1 s t).measurable
      (probabilityTransport_continuous hF x hr hl hT0 hT1 _ s).measurable]
  simp only [comp_def,probabilityTransport_cocycle]
  exact probabilityTransport_from_zero hF x hr hl hT0 hT1 t
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

lemma tensorVector_contDiff {S : Type} [Fintype S] {d : ℕ}
    (F : (S → Fin d) → Point d → ℝ) (hF : ∀c,ContDiff ℝ (⊤:ℕ∞) (F c)) :
    ContDiff ℝ (⊤:ℕ∞) (tensorVector F) := by
  exact (PiLp.continuousLinearEquiv 2 ℝ (fun _ : S → Fin d => ℝ)).symm.contDiff.comp
    (contDiff_pi.mpr hF)

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

lemma conditionalMeanArray_polySmooth {d : ℕ} {F : Point d → ℝ} {lam : ℝ≥0}
    (hF : Primitive F lam) (x : Point d) {r T : ℝ} (hr : 0 < r)
    (hlam : 0<lam) (hl : (lam:ℝ)*r^2≤1/2) (hT0 : 0≤T) (hT1 : T<1)
    (c : Unit → Fin d) : PolySmooth (conditionalMeanArray F x r T c) :=
  conditionalFieldMean_component_polySmooth hF x hr hlam hl hT0 hT1 (c ())

lemma conditionalMeanArray_allSplit {d n : ℕ} {F : Point d → ℝ} {lam : ℝ≥0}
    (hF : Primitive F lam) (x : Point d) {r T : ℝ} (hr : 0 < r)
    (hlam : 0<lam) (hl : (lam:ℝ)*r^2≤1/2) (hT0 : 0≤T) (hT1 : T<1)
    (y : Point d) :
    AllSplitBound (spatialTensor (conditionalMeanArray F x r T) (List.finRange n) y)
      ((lam:ℝ)*r*normalizedTensorMajorant (n+1) (1-T^2)) := by
  let mask : Fin n ⊕ Unit → Bool := Sum.elim (fun _ => false) (fun _ => true)
  let l : List (Fin n ⊕ Unit) := (List.finRange n).map Sum.inl++[Sum.inr ()]
  have hnodup : l.Nodup := by
    simpa [l] using JetCalculus.nodup_sum_append (List.nodup_finRange n)
      (by simp : ([()] : List Unit).Nodup)
  have hall : ∀s,s∈l := by intro s; cases s <;> simp [l]
  have hh := (normalizedTensor_allSplit hF x hr hlam hl hT0 hT1 y mask l hnodup hall).const_mul
    (T^n*((lam:ℝ)*r))
  have he : spatialTensor (conditionalMeanArray F x r T) (List.finRange n) y=
      fun c => T^n*((lam:ℝ)*r)*normalizedTensor F x r T ((lam:ℝ)*r) y mask l c := by
    funext c
    unfold spatialTensor
    have hf : conditionalMeanArray F x r T (fun s => c (Sum.inr s))=
        (fun z => inner ℝ (EuclideanSpace.basisFun (Fin d) ℝ (c (Sum.inr ())))
          (conditionalFieldMean F x r T z)) := rfl
    rw [hf]
    simpa only [Fintype.card_fin,mask,l] using
      conditionalFieldMean_jet_normalized hF x hr hlam hl hT0 hT1 y
        (List.finRange n) (by simp) c
  rw [he]
  simp only [Fintype.card_sum,Fintype.card_fin,Fintype.card_unique] at hh
  apply hh.mono
  · exact mul_nonneg (mul_nonneg (pow_nonneg hT0 _) (mul_nonneg lam.2 hr.le))
      (normalizedTensorMajorant_nonneg _ _)
  ·
    have ht : T^n≤1 := pow_le_one₀ hT0 hT1.le
    have ht' : T^n*((lam:ℝ)*r)≤(lam:ℝ)*r := by
      calc
        _ ≤ 1*((lam:ℝ)*r) := mul_le_mul_of_nonneg_right ht (mul_nonneg lam.2 hr.le)
        _ = _ := one_mul _
    exact mul_le_mul_of_nonneg_right ht' (normalizedTensorMajorant_nonneg _ _)

lemma conditionalMeanArray_energy {d n : ℕ} {F : Point d → ℝ} {lam : ℝ≥0}
    (hF : Primitive F lam) (x : Point d) {r T : ℝ} (hr : 0 < r)
    (hlam : 0<lam) (hl : (lam:ℝ)*r^2≤1/2) (hT0 : 0≤T) (hT1 : T<1)
    (hn : 0<n) :
    spatialEnergy (conditionalMeanArray F x r T) n (gibbs (interpolationPotential F x r T))≤
      d*((lam:ℝ)*r)^2*(normalizedTensorMajorant (n+1) (1-T^2))^2 := by
  have hH := interpolationPotential_polySmooth hF x hr hlam hl hT0 hT1
  have ht := interpolationPotential_lowerTail hF x hr.le (by linarith) hT0 hT1
  let := probability_gibbs_of_gaussianTail hH.smooth.continuous ht
  exact (spatialEnergy_from_split hH.smooth.continuous ht _
    (conditionalMeanArray_polySmooth hF x hr hlam hl hT0 hT1) hn
    (conditionalMeanArray_allSplit hF x hr hlam hl hT0 hT1)).trans_eq (by ring)
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
namespace LogConcaveSampling.Quadrature
open MeasureTheory Set Polynomial
open scoped BigOperators

variable {I E : Type*} [Fintype I] [DecidableEq I]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

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

lemma centeringMeanArray_polySmooth {d : ℕ} {F : Point d → ℝ} {lam : ℝ≥0}
    (hF : Primitive F lam) (x : Point d) {r T : ℝ} (hr : 0 < r)
    (hlam : 0<lam) (hl : (lam:ℝ)*r^2≤1/2) (hT0 : 0≤T) (hT1 : T<1)
    (c : Unit → Fin (d+d)) : PolySmooth (centeringMeanArray F x r T c) :=
  arrayCoordinateLift_polySmooth _ _ _ (conditionalMeanArray_polySmooth hF x hr hlam hl hT0 hT1) c

lemma centeringMeanArray_energy {d n : ℕ} {F : Point d → ℝ} {lam : ℝ≥0}
    (hF : Primitive F lam) (x : Point d) {r T : ℝ} (hr : 0 < r)
    (hlam : 0<lam) (hl : (lam:ℝ)*r^2≤1/2) (hT0 : 0≤T) (hT1 : T<1)
    (hn : 0<n) :
    spatialEnergy (centeringMeanArray F x r T) n (gibbs (centeringPotential F x r T))≤
      d*((lam:ℝ)*r)^2*(normalizedTensorMajorant (n+1) (1-T^2))^2 := by
  have hH := interpolationPotential_polySmooth hF x hr hlam hl hT0 hT1
  have ht := interpolationPotential_lowerTail hF x hr.le (by linarith) hT0 hT1
  let := probability_gibbs_of_gaussianTail hH.smooth.continuous ht
  dsimp only [centeringMeanArray,centeringPotential]
  rw [spatialEnergy_leftLift hH.smooth.continuous _
    (fun c => (conditionalMeanArray_polySmooth hF x hr hlam hl hT0 hT1 c).smooth)]
  exact conditionalMeanArray_energy hF x hr hlam hl hT0 hT1 hn

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

lemma centeringMean_inv_scaled {d : ℕ} {F : Point d → ℝ} {lam : ℝ≥0}
    (hF : Primitive F lam) (x : Point d) {r R T : ℝ}
    (hr : 0 < r) (hlam : 0<lam) (hl : (lam:ℝ)*r^2≤1/2)
    (hR : 0<R) (hRT : R^2≤1-T^2) (hT0 : 0≤T) (hT1 : T<1) :
    ∀k,0<k → spatialEnergy (centeringMeanArray F x r T) k (gibbs (centeringPotential F x r T))≤
      (d*((lam:ℝ)*r)^2)*(R⁻¹)^(2*k)*(normalizedTensorMajorant (k+1) 1)^2 := by
  have hR1 : R≤1 := by nlinarith [sq_nonneg T]
  intro k hk
  apply (centeringMeanArray_energy hF x hr hlam hl hT0 hT1 hk).trans
  have he := pow_le_pow_left₀ (normalizedTensorMajorant_nonneg (k+1) (1-T^2))
    (normalizedTensorMajorant_inv_scale (k:=k) hR hR1 hRT) 2
  have hh := mul_le_mul_of_nonneg_left he (show 0≤(d:ℝ)*((lam:ℝ)*r)^2 by positivity)
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

lemma harmonicMeanBudget_nonneg (n : ℕ) : 0≤harmonicMeanBudget n :=
  iterEnergyBudget_nonneg harmonicGradientBound.2 _ _ (fun _ => sq_nonneg _) n 0

attribute [local instance] OAI.LogConcaveSampling.instDecidableEqUnit_solutions_4
theorem harmonic_mean_taylor_uniform {d : ℕ} {F : Point d → ℝ} {lam : ℝ≥0}
    (hF : Primitive F lam) (x : Point d) {r R T : ℝ}
    (hr : 0 < r) (hlam : 0<lam) (hl : (lam:ℝ)*r^2≤1/2)
    (hR : 0<R) (hRT : R^2≤1-T^2) (hT0 : 0≤T) (hT1 : T<1)
    (Ξ : Point (d+d) → ℝ → Point (d+d))
    (hder : ∀y t,t∈Icc (0:ℝ) 1 → HasDerivWithinAt (Ξ y)
      (skewLieField (centeringPotential F x r T) (harmonicSkew d) (Ξ y t)) (Icc (0:ℝ) 1) t)
    (hm : Measurable (fun p : ℝ × Point (d+d) => Ξ p.2 p.1))
    (hlaw : ∀t∈Icc (0:ℝ) 1,(gibbs (centeringPotential F x r T)).map (fun y => Ξ y t)=
      gibbs (centeringPotential F x r T)) :
    ∀n : ℕ,∀a b : ℝ,0≤a → a≤b → b≤1 →
      Integrable (fun y => ‖tensorVector (centeringMeanArray F x r T) (Ξ y b)-chainTaylor
        (fun k t => tensorVector (iterTensorLie (centeringPotential F x r T)
          (harmonicSkew d) (centeringMeanArray F x r T) k) (Ξ y t)) n a b‖^2)
        (gibbs (centeringPotential F x r T)) ∧
      (∫y,‖tensorVector (centeringMeanArray F x r T) (Ξ y b)-chainTaylor
        (fun k t => tensorVector (iterTensorLie (centeringPotential F x r T)
          (harmonicSkew d) (centeringMeanArray F x r T) k) (Ξ y t)) n a b‖^2
        ∂gibbs (centeringPotential F x r T))≤
      ((b-a)^(n+1)/(n.factorial:ℝ))^2*
        ((d*((lam:ℝ)*r)^2)*(R⁻¹)^(4*(n+1))*harmonicMeanBudget (n+1)) := by
  have hR1 : R≤1 := by nlinarith [sq_nonneg T]
  have hH : PolySmooth (centeringPotential F x r T) := productPotential_polySmooth
    (interpolationPotential_polySmooth hF x hr hlam hl hT0 hT1) (gaussianPotential_polySmooth d)
  have ht : HasGaussianLowerTail (centeringPotential F x r T) := productPotential_lowerTail
    (interpolationPotential_lowerTail hF x hr.le (by linarith) hT0 hT1) (gaussianPotential_lowerTail d)
  let := probability_gibbs_of_gaussianTail hH.smooth.continuous ht
  intro n a b ha hab hb
  have hsub : uIcc a b⊆Icc (0:ℝ) 1 := by
    rw [uIcc_of_le hab]
    intro t h; exact ⟨ha.trans h.1,h.2.trans hb⟩
  have h := stationary_lie_taylor_rms (S:=Unit) (d:=d+d) hH ht
    (centeringPotential_gradient_uniform hF x hr hl hT0 hT1)
    (harmonicSkew d) (centeringMeanArray F x r T)
    (harmonicSkew_polySmooth d) (centeringMeanArray_polySmooth hF x hr hlam hl hT0 hT1)
    (jointSkew_skew _ 1) (fun _ => 2)
    (fun k => 2+normalizedTensorMajorant (k+1) 1)
    (fun k => (normalizedTensorMajorant (k+1) 1)^2)
    (α:=1) (κ:=d*((lam:ℝ)*r)^2) (ρ:=R⁻¹) (by positivity) ((one_le_inv₀ hR).mpr hR1)
    (fun _ => sq_nonneg _) (harmonicSkew_inv_scaled hR hR1)
    (centeringScore_inv_scaled hF x hr hlam hl hR hRT hT0 hT1)
    (centeringMean_inv_scaled hF x hr hlam hl hR hRT hT0 hT1)
    Ξ hder hm hlaw hab hsub n
  simpa only [one_pow,one_mul,←pow_mul,harmonicMeanBudget] using h
end LogConcaveSampling

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

lemma probabilityNodes_injective {n : ℕ} (hn : 0<n) : Function.Injective (probabilityNodes n) := by
  intro i j hij
  apply Fin.ext
  have hne : (n:ℝ)≠0 := by exact_mod_cast ne_of_gt hn
  have he : (i:ℝ)=(j:ℝ) := (div_left_inj' hne).mp hij
  exact_mod_cast he

end LogConcaveSampling

end

end

section

noncomputable section
namespace LogConcaveSampling
open Set MeasureTheory
open scoped Classical BigOperators NNReal RealInnerProductSpace
open TensorEnergy Quadrature

attribute [local instance] OAI.LogConcaveSampling.instDecidableEqUnit_solutions_6
theorem harmonic_mean_interpolation_rms (n : ℕ) (hn : 0<n) :
    ∃C : ℝ,1≤C ∧ ∀{d : ℕ} {F : Point d → ℝ} {lam : ℝ≥0},
      ∀_ : Primitive F lam,∀(x : Point d) {r R T : ℝ},
      0 < r → 0<lam → (lam:ℝ)*r^2≤1/2 → 0<R → R^2≤1-T^2 → 0≤T → T<1 →
      ∀Ξ : Point (d+d) → ℝ → Point (d+d),
      (∀y v,v∈Icc (0:ℝ) 1 → HasDerivWithinAt (Ξ y)
        (skewLieField (centeringPotential F x r T) (harmonicSkew d) (Ξ y v)) (Icc (0:ℝ) 1) v) →
      Measurable (fun p : ℝ × Point (d+d) => Ξ p.2 p.1) →
      (∀v∈Icc (0:ℝ) 1,(gibbs (centeringPotential F x r T)).map (fun y => Ξ y v)=
        gibbs (centeringPotential F x r T)) →
      ∀z : ℝ,0≤z → z≤1 → ∀v∈Icc (0:ℝ) 1,
      let M := fun s y => tensorVector (centeringMeanArray F x r T) (Ξ y s)
      Integrable (fun y => ‖M (z*v) y-interpolation (probabilityNodes n)
        (fun i => M (z*probabilityNodes n i) y) v‖^2) (gibbs (centeringPotential F x r T)) ∧
      (∫y,‖M (z*v) y-interpolation (probabilityNodes n)
        (fun i => M (z*probabilityNodes n i) y) v‖^2 ∂gibbs (centeringPotential F x r T))≤
        4*C^2*(z^(n+1)/(n.factorial:ℝ))^2*
          ((d*((lam:ℝ)*r)^2)*(R⁻¹)^(4*(n+1))*harmonicMeanBudget (n+1)) := by
  obtain ⟨C,hC,hC'⟩ := exists_basis_budget (probabilityNodes n)
  refine ⟨C,hC,?_⟩
  intro d F lam hF x r R T hr hlam hl hR hRT hT0 hT1 Ξ hder hm hlaw z hz hz1 v hv M
  let J := fun k s y => tensorVector (iterTensorLie (centeringPotential F x r T)
    (harmonicSkew d) (centeringMeanArray F x r T) k) (Ξ y s)
  have hH : PolySmooth (centeringPotential F x r T) := productPotential_polySmooth
    (interpolationPotential_polySmooth hF x hr hlam hl hT0 hT1) (gaussianPotential_polySmooth d)
  have hJ (k : ℕ) (s : ℝ) : Measurable (J k s) :=
    liePathJet_measurable hH (harmonicSkew d) (centeringMeanArray F x r T)
      (harmonicSkew_polySmooth d) (centeringMeanArray_polySmooth hF x hr hlam hl hT0 hT1) Ξ hm k s
  have hs (s : ℝ) (hs : s∈insert v (range (probabilityNodes n))) : s∈Icc (0:ℝ) 1 := by
    rcases hs with he|⟨i,rfl⟩
    · simpa only [he] using hv
    · exact probabilityNodes_mem hn i
  have hsz (s : ℝ) (hs' : s∈insert v (range (probabilityNodes n))) : 0≤z*s ∧ z*s≤z :=
    ⟨mul_nonneg hz (hs s hs').1,mul_le_of_le_one_right hz (hs s hs').2⟩
  have htay (s : ℝ) (hs' : s∈insert v (range (probabilityNodes n))) :=
    harmonic_mean_taylor_uniform hF x hr hlam hl hR hRT hT0 hT1 Ξ hder hm hlaw n 0 (z*s)
      le_rfl (hsz s hs').1 ((hsz s hs').2.trans hz1)
  have h := cell_chain_error_rms (probabilityNodes n) (probabilityNodes_injective hn) n
    (by simp) J 0 z v
    (B:=(z^(n+1)/(n.factorial:ℝ))^2*((d*((lam:ℝ)*r)^2)*(R⁻¹)^(4*(n+1))*harmonicMeanBudget (n+1)))
    (by positivity [harmonicMeanBudget_nonneg (n+1)]) hC (hC' v hv)
    (fun s _ => ((hJ 0 _).sub (chainTaylor_measurable J hJ n 0 _)).aestronglyMeasurable)
    (fun s hs' => by simpa only [zero_add,sub_zero,J,iterTensorLie] using (htay s hs').1)
    (fun s hs' => by
      have hh := (htay s hs').2
      change (∫y,‖J 0 (z*s) y-chainTaylor (fun k v => J k v y) n 0 (z*s)‖^2 ∂gibbs (centeringPotential F x r T))≤_ at hh
      simp only [zero_add]
      apply hh.trans
      simp only [sub_zero]
      apply mul_le_mul_of_nonneg_right _ (by positivity [harmonicMeanBudget_nonneg (n+1)])
      apply pow_le_pow_left₀ (div_nonneg (pow_nonneg (hsz s hs').1 _) (Nat.cast_nonneg _))
      apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
      exact pow_le_pow_left₀ (hsz s hs').1 (hsz s hs').2 _)
  simpa only [zero_add,J,iterTensorLie,M,mul_assoc] using h
end LogConcaveSampling

end

end

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

lemma meanOutputProjection_mean {d : ℕ} (F : Point d → ℝ) (x : Point d) (r T : ℝ)
    (y : Point (d+d)) : meanOutputProjection d (tensorVector (centeringMeanArray F x r T) y)=
      conditionalFieldMean F x r T (productPointEquiv d d y).1 := by
  ext i
  change TensorEnergy.zeroExtend (slotEmbedding (fun _ : Unit => leftCoordinates d d))
    (fun a => conditionalMeanArray F x r T a (coordinateProjection (leftCoordinates d d) y))
    (slotEmbedding (fun _ : Unit => leftCoordinates d d) (fun _ => i))=_
  rw [zeroExtend_apply,coordinateProjection_left]
  simp only [conditionalMeanArray,EuclideanSpace.basisFun_inner]

lemma projection_interpolation {I E G : Type*} [Fintype I] [DecidableEq I]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup G] [NormedSpace ℝ G]
    (L : E →L[ℝ] G) (u : I → ℝ) (v : I → E) (t : ℝ) :
    L (interpolation u v t)=interpolation u (fun i => L (v i)) t := by
  simp only [interpolation,map_sum,map_smul]

attribute [local instance] OAI.LogConcaveSampling.instDecidableEqUnit_solutions_7
theorem harmonic_point_interpolation_rms (n : ℕ) (hn : 0<n) :
    ∃C : ℝ,1≤C ∧ ∀{d : ℕ} {F : Point d → ℝ} {lam : ℝ≥0},
      ∀_ : Primitive F lam,∀(x : Point d) {r R T : ℝ},
      0 < r → 0<lam → (lam:ℝ)*r^2≤1/2 → 0<R → R^2≤1-T^2 → 0≤T → T<1 →
      ∀Ξ : Point (d+d) → ℝ → Point (d+d),
      (∀y v,v∈Icc (0:ℝ) 1 → HasDerivWithinAt (Ξ y)
        (skewLieField (centeringPotential F x r T) (harmonicSkew d) (Ξ y v)) (Icc (0:ℝ) 1) v) →
      Measurable (fun p : ℝ × Point (d+d) => Ξ p.2 p.1) →
      (∀v∈Icc (0:ℝ) 1,(gibbs (centeringPotential F x r T)).map (fun y => Ξ y v)=
        gibbs (centeringPotential F x r T)) →
      ∀z : ℝ,0≤z → z≤1 → ∀v∈Icc (0:ℝ) 1,
      let M := fun s y => conditionalFieldMean F x r T (productPointEquiv d d (Ξ y s)).1
      Integrable (fun y => ‖M (z*v) y-interpolation (probabilityNodes n)
        (fun i => M (z*probabilityNodes n i) y) v‖^2) (gibbs (centeringPotential F x r T)) ∧
      (∫y,‖M (z*v) y-interpolation (probabilityNodes n)
        (fun i => M (z*probabilityNodes n i) y) v‖^2 ∂gibbs (centeringPotential F x r T))≤
        4*C^2*(z^(n+1)/(n.factorial:ℝ))^2*
          ((d*((lam:ℝ)*r)^2)*(R⁻¹)^(4*(n+1))*harmonicMeanBudget (n+1)) := by
  obtain ⟨C,hC,hC'⟩ := harmonic_mean_interpolation_rms n hn
  refine ⟨C,hC,?_⟩
  intro d F lam hF x r R T hr hlam hl hR hRT hT0 hT1 Ξ hder hm hlaw z hz hz1 v hv M
  let Q := fun s y => tensorVector (centeringMeanArray F x r T) (Ξ y s)
  let E := fun y => Q (z*v) y-interpolation (probabilityNodes n)
    (fun i => Q (z*probabilityNodes n i) y) v
  have hb := hC' hF x hr hlam hl hR hRT hT0 hT1 Ξ hder hm hlaw z hz hz1 v hv
  have he (y : Point (d+d)) : M (z*v) y-interpolation (probabilityNodes n)
      (fun i => M (z*probabilityNodes n i) y) v=meanOutputProjection d (E y) := by
    simp only [E,map_sub,Q,projection_interpolation,meanOutputProjection_mean,M]
  have hQ (s : ℝ) : Measurable (Q s) :=
    (tensorVector_contDiff _ (fun c =>
      (centeringMeanArray_polySmooth hF x hr hlam hl hT0 hT1 c).smooth)).continuous.measurable.comp
      (hm.comp (measurable_const.prodMk measurable_id))
  have hE : Measurable E := (hQ _).sub
    (Finset.measurable_sum _ (fun i _ => by
      change Measurable (fun y => basis (probabilityNodes n) i v • Q (z*probabilityNodes n i) y)
      exact (hQ _).const_smul (basis (probabilityNodes n) i v)))
  have hab (y : Point (d+d)) : ‖meanOutputProjection d (E y)‖^2≤‖E y‖^2 :=
    pow_le_pow_left₀ (norm_nonneg _) (finiteCoordinateProjection_norm_le _ _) 2
  simp_rw [he]
  have hi := hb.1.mono' (((meanOutputProjection d).continuous.measurable.comp hE).norm.pow_const 2).aestronglyMeasurable
    (Filter.Eventually.of_forall (fun y => by simpa only [Real.norm_eq_abs,abs_sq,Function.comp_def,E,Q] using hab y))
  exact ⟨hi,(integral_mono hi hb.1 hab).trans hb.2⟩
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

section

noncomputable section
namespace LogConcaveSampling
open MeasureTheory Set Quadrature
open scoped BigOperators

variable {E Ω : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace Ω] {ν : Measure Ω} [SFinite ν]

lemma harmonicWeight_sum_integral (n : ℕ) (z : ℝ) (i : Fin (n+1)) (v : Fin (n+1) → E) :
    (∑j,harmonicWeight n z i j • v j)=z • (∫t in 0..probabilityNodes n i,
      Real.sin (z*(probabilityNodes n i-t)) • interpolation (probabilityNodes n) v t) := by
  simp_rw [interpolation,Finset.smul_sum,smul_smul]
  rw [intervalIntegral.integral_finsetSum]
  · rw [Finset.smul_sum]
    apply Finset.sum_congr rfl
    intro j hj
    rw [intervalIntegral.integral_smul_const]
    simp only [harmonicWeight,smul_smul]
  · intro j hj
    exact ((Real.continuous_sin.comp
      (continuous_const.mul (continuous_const.sub continuous_id))).mul
      (basis_continuous (probabilityNodes n) j)).smul continuous_const |>.intervalIntegrable _ _

theorem harmonic_quadrature_error_rms (n : ℕ) (z : ℝ) (i : Fin (n+1))
    (f : ℝ → Ω → E) (hi0 : 0≤probabilityNodes n i) {B : ℝ} (hB0 : 0≤B)
    (hf : ∀y,Continuous (fun t => f t y))
    (hm : AEStronglyMeasurable (fun p : ℝ × Ω => f p.1 p.2-
      interpolation (probabilityNodes n) (fun j => f (probabilityNodes n j) p.2) p.1)
      ((volume.restrict (Ioc 0 (probabilityNodes n i))).prod ν))
    (hi : ∀t∈Ioc 0 (probabilityNodes n i),Integrable (fun y => ‖f t y-
      interpolation (probabilityNodes n) (fun j => f (probabilityNodes n j) y) t‖^2) ν)
    (hB : ∀t∈Ioc 0 (probabilityNodes n i),(∫y,‖f t y-
      interpolation (probabilityNodes n) (fun j => f (probabilityNodes n j) y) t‖^2 ∂ν)≤B) :
    Integrable (fun y => ‖z • (∫t in 0..probabilityNodes n i,
      Real.sin (z*(probabilityNodes n i-t)) • f t y)-
      ∑j,harmonicWeight n z i j • f (probabilityNodes n j) y‖^2) ν ∧
    (∫y,‖z • (∫t in 0..probabilityNodes n i,
      Real.sin (z*(probabilityNodes n i-t)) • f t y)-
      ∑j,harmonicWeight n z i j • f (probabilityNodes n j) y‖^2 ∂ν)≤
      z^2*(probabilityNodes n i)^2*B := by
  let μ : Measure ℝ := volume.restrict (Ioc 0 (probabilityNodes n i))
  let w : ℝ → ℝ := fun t => Real.sin (z*(probabilityNodes n i-t))
  have hw : Continuous w := by dsimp [w]; fun_prop
  have hs : ∀ᵐ t ∂μ,Integrable (fun y => ‖f t y-
      interpolation (probabilityNodes n) (fun j => f (probabilityNodes n j) y) t‖^2) ν := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    exact hi t ht
  have hb : ∀ᵐ t ∂μ,(∫y,‖f t y-
      interpolation (probabilityNodes n) (fun j => f (probabilityNodes n j) y) t‖^2 ∂ν)≤B := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    exact hB t ht
  have hv := RMSIntegral.weighted_time_seed hm hw.aestronglyMeasurable hB0
    (Filter.Eventually.of_forall (fun t => Real.abs_sin_le_one (z*(probabilityNodes n i-t)))) hs hb
  have he (y : Ω) : z • (∫t in 0..probabilityNodes n i,w t • f t y)-
      ∑j,harmonicWeight n z i j • f (probabilityNodes n j) y=
      z • (∫t,w t • (f t y-interpolation (probabilityNodes n)
        (fun j => f (probabilityNodes n j) y) t) ∂μ) := by
    rw [harmonicWeight_sum_integral,←smul_sub]
    change z • ((∫t in 0..probabilityNodes n i,w t • f t y)-
      ∫t in 0..probabilityNodes n i,w t • interpolation (probabilityNodes n)
        (fun j => f (probabilityNodes n j) y) t)=_
    rw [←intervalIntegral.integral_sub (f:=fun t => w t • f t y)
      (g:=fun t => w t • interpolation (probabilityNodes n) (fun j => f (probabilityNodes n j) y) t)
      ((hw.smul (hf y)).intervalIntegrable _ _)
      ((hw.smul (interpolation_continuous _ _)).intervalIntegrable _ _)]
    simp_rw [←smul_sub]
    rw [intervalIntegral.integral_of_le hi0]
  have hnorm (v : E) : ‖z • v‖^2=z^2*‖v‖^2 := by
    rw [norm_smul,mul_pow,Real.norm_eq_abs,sq_abs]
  dsimp only [w] at he
  simp_rw [he,hnorm]
  refine ⟨hv.1.const_mul (z^2),?_⟩
  rw [integral_const_mul]
  have hμ : μ.real univ=probabilityNodes n i := by
    dsimp only [μ,Measure.real]
    rw [Measure.restrict_apply_univ]
    change volume.real (Ioc 0 (probabilityNodes n i))=probabilityNodes n i
    rw [Real.volume_real_Ioc_of_le hi0,sub_zero]
  rw [hμ,one_pow,mul_one] at hv
  exact (mul_le_mul_of_nonneg_left hv.2 (sq_nonneg z)).trans_eq (by ring)
end LogConcaveSampling

end

end

end

end OAI
end

section
-- module Solutions.OAIQ048_LC.LogConcave_Sampling_HarmonicMeanDefect
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
open scoped Classical BigOperators RealInnerProductSpace NNReal

theorem harmonic_integral_equation {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [CompleteSpace E] {Y P : ℝ → E} {f : E → E}
    (hY : Continuous Y) (hP : Continuous P) (hf : Continuous f)
    (hderY : ∀v∈Icc (0:ℝ) 1,HasDerivWithinAt Y (P v) (Icc (0:ℝ) 1) v)
    (hderP : ∀v∈Icc (0:ℝ) 1,HasDerivWithinAt P (-Y v-f (Y v)) (Icc (0:ℝ) 1) v)
    {t : ℝ} (ht : t∈Icc (0:ℝ) 1) :
    Y t=Real.cos t • Y 0+Real.sin t • P 0-
      ∫v in 0..t,Real.sin (t-v) • f (Y v) := by
  let g : ℝ → E := fun v => Real.cos (t-v) • Y v+Real.sin (t-v) • P v
  have hg : Continuous g := by unfold g; fun_prop
  have hfg : Continuous (fun v => -Real.sin (t-v) • f (Y v)) := by fun_prop
  have he := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le ht.1 hg.continuousOn
    (f':=fun v => -Real.sin (t-v) • f (Y v))
    (fun v hv => by
      have hm : v∈Icc (0:ℝ) 1 := ⟨hv.1.le,hv.2.le.trans ht.2⟩
      have hn := Icc_mem_nhds hv.1 (hv.2.trans_le ht.2)
      have hDY := (hderY v hm).hasDerivAt hn
      have hDP := (hderP v hm).hasDerivAt hn
      have hcos : HasDerivAt (fun u => Real.cos (t-u)) (Real.sin (t-v)) v := by
        convert ((hasDerivAt_const v t).sub (hasDerivAt_id v)).cos using 1 <;> simp
      have hsin : HasDerivAt (fun u => Real.sin (t-u)) (-Real.cos (t-v)) v := by
        convert ((hasDerivAt_const v t).sub (hasDerivAt_id v)).sin using 1 <;> simp
      convert (hcos.smul hDY).add (hsin.smul hDP) using 1
      all_goals try with_reducible_and_instances rfl
      module)
    (hfg.intervalIntegrable 0 t)
  change (∫v in 0..t,-Real.sin (t-v) • f (Y v))=g t-g 0 at he
  simp only [g,sub_self,Real.cos_zero,Real.sin_zero,one_smul,zero_smul,add_zero,sub_zero] at he
  simp_rw [neg_smul] at he
  rw [intervalIntegral.integral_neg] at he
  exact (sub_eq_iff_eq_add.mp he.symm).trans (by abel)

theorem conditional_harmonic_integral {d : ℕ} {F : Point d → ℝ} {lam : ℝ≥0}
    (hF : Primitive F lam) (x : Point d) {r T : ℝ} (hr : 0 ≤ r)
    (hl : (lam:ℝ)*r^2≤1/2) (hT0 : 0≤T) (hT1 : T<1)
    (Ξ : Point (d+d) → ℝ → Point (d+d))
    (hc : ∀y,Continuous (Ξ y))
    (hder : ∀y v,v∈Icc (0:ℝ) 1 → HasDerivWithinAt (Ξ y)
      (skewLieField (productPotential (interpolationPotential F x r T) (fun z : Point d => ‖z‖^2/2)) (harmonicSkew d) (Ξ y v)) (Icc (0:ℝ) 1) v)
    (y : Point (d+d)) {t : ℝ} (ht : t∈Icc (0:ℝ) 1) :
    let W := fun v => (productPointEquiv d d (Ξ y v)).1
    let P := fun v => (productPointEquiv d d (Ξ y v)).2
    W t=Real.cos t • W 0+Real.sin t • P 0-
      (r*T) • (∫v in 0..t,Real.sin (t-v) • conditionalFieldMean F x r T (W v)) := by
  intro W P
  have hH : Differentiable ℝ (interpolationPotential F x r T) :=
    (interpolationPotential_smooth hF x hr hl hT0 hT1).differentiable (by norm_cast)
  have hD (v : ℝ) (hv : v∈Icc (0:ℝ) 1) :
      HasDerivWithinAt (fun s => productPointEquiv d d (Ξ y s))
        (P v,-W v-(r*T) • conditionalFieldMean F x r T (W v)) (Icc (0:ℝ) 1) v := by
    have h := (productPointEquiv d d).toContinuousLinearMap.hasFDerivAt.comp_hasDerivWithinAt v (hder y v hv)
    change HasDerivWithinAt (fun s => productPointEquiv d d (Ξ y s))
      (productPointEquiv d d (skewLieField
        (productPotential (interpolationPotential F x r T) (fun z : Point d => ‖z‖^2/2))
        (harmonicSkew d) (Ξ y v))) (Icc (0:ℝ) 1) v at h
    rw [harmonicSkew_field hH] at h
    rw [interpolationPotential_gradient hF x hr hl hT0 hT1] at h
    simpa only [W,P,neg_add_rev,sub_eq_add_neg,add_comm] using h
  have he := harmonic_integral_equation ((productPointEquiv d d).continuous.comp (hc y)).fst
    ((productPointEquiv d d).continuous.comp (hc y)).snd
    ((conditionalFieldMean_lipschitz hF x hr hl hT0 hT1).continuous.const_smul (r*T))
    (fun v hv => (hD v hv).fst) (fun v hv => (hD v hv).snd) ht
  change W t=Real.cos t • W 0+Real.sin t • P 0-
    ∫v in 0..t,Real.sin (t-v) • ((r*T) • conditionalFieldMean F x r T (W v)) at he
  simp_rw [smul_comm (Real.sin (t-_)) (r*T)] at he
  rw [intervalIntegral.integral_smul] at he
  exact he

end LogConcaveSampling

end

end

section

noncomputable section
namespace LogConcaveSampling
open Set MeasureTheory TensorEnergy Quadrature
open scoped Classical BigOperators NNReal RealInnerProductSpace

lemma interpolation_error_measurable {I E Ω : Type*} [Fintype I] [DecidableEq I]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E] [BorelSpace E]
    [MeasurableSpace Ω] [SecondCountableTopology E] (u : I → ℝ) (f : ℝ × Ω → E)
    (hf : Measurable f) : Measurable (fun p : ℝ × Ω => f p-
      interpolation u (fun j => f (u j,p.2)) p.1) := by
  apply hf.sub
  apply Finset.measurable_sum
  intro j hj
  exact ((basis_continuous u j).measurable.comp measurable_fst).smul
    (hf.comp (measurable_const.prodMk measurable_snd))

lemma harmonicMean_measurable {d : ℕ} {F : Point d → ℝ} {lam : ℝ≥0}
    (hF : Primitive F lam) (x : Point d) {r T z : ℝ} (hr : 0 ≤ r)
    (hl : (lam:ℝ)*r^2≤1/2) (hT0 : 0≤T) (hT1 : T<1)
    (Ξ : Point (d+d) → ℝ → Point (d+d))
    (hm : Measurable (fun p : ℝ × Point (d+d) => Ξ p.2 p.1)) :
    Measurable (fun p : ℝ × Point (d+d) =>
      conditionalFieldMean F x r T (productPointEquiv d d (Ξ p.2 (z*p.1))).1) := by
  have h1 : Measurable (fun p : ℝ × Point (d+d) => Ξ p.2 (z*p.1)) :=
    hm.comp ((measurable_const.mul measurable_fst).prodMk measurable_snd)
  have h2 : Measurable (fun p : ℝ × Point (d+d) => (productPointEquiv d d (Ξ p.2 (z*p.1))).1) :=
    ((productPointEquiv d d).continuous.measurable.comp h1).fst
  exact (conditionalFieldMean_lipschitz hF x hr hl hT0 hT1).continuous.measurable.comp h2

theorem harmonic_mean_quadrature_rms (n : ℕ) (hn : 0<n) :
    ∃C : ℝ,1≤C ∧ ∀{d : ℕ} {F : Point d → ℝ} {lam : ℝ≥0},
      ∀_ : Primitive F lam,∀(x : Point d) {r R T : ℝ},
      0 < r → 0<lam → (lam:ℝ)*r^2≤1/2 → 0<R → R^2≤1-T^2 → 0≤T → T<1 →
      ∀Ξ : Point (d+d) → ℝ → Point (d+d),
      (∀y,Continuous (Ξ y)) →
      (∀y v,v∈Icc (0:ℝ) 1 → HasDerivWithinAt (Ξ y)
        (skewLieField (centeringPotential F x r T) (harmonicSkew d) (Ξ y v)) (Icc (0:ℝ) 1) v) →
      Measurable (fun p : ℝ × Point (d+d) => Ξ p.2 p.1) →
      (∀v∈Icc (0:ℝ) 1,(gibbs (centeringPotential F x r T)).map (fun y => Ξ y v)=
        gibbs (centeringPotential F x r T)) →
      ∀z : ℝ,0≤z → z≤1 → ∀i : Fin (n+1),
      Integrable (fun y => ‖harmonicMeanDefect F x r T z Ξ n i y‖^2)
          (gibbs (centeringPotential F x r T)) ∧
      (∫y,‖harmonicMeanDefect F x r T z Ξ n i y‖^2 ∂gibbs (centeringPotential F x r T))≤
        4*C^2*(z^(n+1)/(n.factorial:ℝ))^2*
          ((d*((lam:ℝ)*r)^2)*(R⁻¹)^(4*(n+1))*harmonicMeanBudget (n+1)) := by
  obtain ⟨C,hC,hC'⟩ := harmonic_point_interpolation_rms n hn
  refine ⟨C,hC,?_⟩
  intro d F lam hF x r R T hr hlam hl hR hRT hT0 hT1 Ξ hc hder hm hlaw z hz hz1 i
  have hH := productPotential_polySmooth
    (interpolationPotential_polySmooth hF x hr hlam hl hT0 hT1) (gaussianPotential_polySmooth d)
  have ht := productPotential_lowerTail
    (interpolationPotential_lowerTail hF x hr.le (by linarith) hT0 hT1) (gaussianPotential_lowerTail d)
  let : IsProbabilityMeasure (gibbs (centeringPotential F x r T)) :=
    probability_gibbs_of_gaussianTail hH.smooth.continuous ht
  let M := fun t y => conditionalFieldMean F x r T (productPointEquiv d d (Ξ y (z*t))).1
  let B := 4*C^2*(z^(n+1)/(n.factorial:ℝ))^2*
    ((d*((lam:ℝ)*r)^2)*(R⁻¹)^(4*(n+1))*harmonicMeanBudget (n+1))
  have hB0 : 0≤B := by dsimp [B]; positivity [harmonicMeanBudget_nonneg (n+1)]
  have hMcont := (conditionalFieldMean_lipschitz hF x hr.le hl hT0 hT1).continuous
  have hMc (y : Point (d+d)) : Continuous (fun t => M t y) :=
    hMcont.comp (((productPointEquiv d d).continuous.comp
      ((hc y).comp (continuous_const.mul continuous_id))).fst)
  have hMm := harmonicMean_measurable (z:=z) hF x hr.le hl hT0 hT1 Ξ hm
  have hErr := interpolation_error_measurable (probabilityNodes n) _ hMm
  have hi := probabilityNodes_mem hn i
  have hmem (t : ℝ) (ht : t∈Ioc 0 (probabilityNodes n i)) : t∈Icc (0:ℝ) 1 :=
    ⟨ht.1.le,ht.2.trans hi.2⟩
  have he := harmonic_quadrature_error_rms n z i M hi.1 hB0 hMc hErr.aestronglyMeasurable
    (fun t ht => (hC' hF x hr hlam hl hR hRT hT0 hT1 Ξ hder hm hlaw z hz hz1 t (hmem t ht)).1)
    (fun t ht => (hC' hF x hr hlam hl hR hRT hT0 hT1 Ξ hder hm hlaw z hz hz1 t (hmem t ht)).2)
  refine ⟨he.1,he.2.trans ?_⟩
  have hz2 : z^2≤1 := pow_le_one₀ hz hz1
  have hi2 : (probabilityNodes n i)^2≤1 := pow_le_one₀ hi.1 hi.2
  exact (mul_le_mul_of_nonneg_right ((mul_le_of_le_one_left (sq_nonneg _) hz2).trans hi2) hB0).trans_eq (one_mul _)

lemma harmonicPicard_exact_defect {d : ℕ} {F : Point d → ℝ} {lam : ℝ≥0}
    (hF : Primitive F lam) (x : Point d) {r T z : ℝ} (hr : 0 ≤ r)
    (hl : (lam:ℝ)*r^2≤1/2) (hT0 : 0≤T) (hT1 : T<1)
    (Ξ : Point (d+d) → ℝ → Point (d+d)) (hc : ∀y,Continuous (Ξ y))
    (hinit : ∀y,Ξ y 0=y)
    (hder : ∀y v,v∈Icc (0:ℝ) 1 → HasDerivWithinAt (Ξ y)
      (skewLieField (centeringPotential F x r T) (harmonicSkew d) (Ξ y v)) (Icc (0:ℝ) 1) v)
    (hz : 0≤z) (hz1 : z≤1) (n : ℕ) (hn : 0<n) (i : Fin (n+1)) (y : Point (d+d)) :
    FinitePicard.step (harmonicWeight n z) (fun _ => harmonicMeanVelocity F x r T)
      (harmonicFree n z (productPointEquiv d d y))
      (fun j => (productPointEquiv d d (Ξ y (z*probabilityNodes n j))).1) i-
      (productPointEquiv d d (Ξ y (z*probabilityNodes n i))).1=
      (r*T) • harmonicMeanDefect F x r T z Ξ n i y := by
  have hi := probabilityNodes_mem hn i
  have hzi : z*probabilityNodes n i∈Icc (0:ℝ) 1 :=
    ⟨mul_nonneg hz hi.1,(mul_le_of_le_one_right hz hi.2).trans hz1⟩
  have he := conditional_harmonic_integral hF x hr hl hT0 hT1 Ξ hc hder y hzi
  dsimp only at he
  rw [hinit] at he
  have hchange := intervalIntegral.smul_integral_comp_mul_left
    (fun v => Real.sin (z*probabilityNodes n i-v) •
      conditionalFieldMean F x r T (productPointEquiv d d (Ξ y v)).1)
    (a:=0) (b:=probabilityNodes n i) z
  simp only [mul_zero] at hchange
  simp_rw [←mul_sub] at hchange
  rw [←hchange] at he
  change (harmonicFree n z (productPointEquiv d d y) i+
    ∑j,harmonicWeight n z i j • harmonicMeanVelocity F x r T
      (productPointEquiv d d (Ξ y (z*probabilityNodes n j))).1)-_= _
  have hvel (u : Point d) : harmonicMeanVelocity F x r T u=-(r*T) • conditionalFieldMean F x r T u := by
    simp only [harmonicMeanVelocity,probabilityMeanVelocity,smul_smul,mul_neg,mul_comm]
  simp_rw [hvel,smul_comm (harmonicWeight n z i _) (-(r*T))]
  rw [←Finset.smul_sum,neg_smul,he]
  dsimp only [harmonicFree,harmonicMeanDefect]
  rw [smul_sub]
  abel
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
open Set MeasureTheory
open scoped NNReal RealInnerProductSpace

lemma growth_vector_memLp {d e : ℕ} {μ : Measure (Point d)} [IsFiniteMeasure μ]
    {f : Point d → Point e} (hg : Appell.HasGrowth f) (hm : AEStronglyMeasurable f μ)
    (hμ : Appell.HasMoments μ) : MemLp f 2 μ := by
  exact (memLp_two_iff_integrable_sq_norm hm).mpr ((hg.norm.pow 2).integrable (hm.norm.pow 2) hμ)

lemma centering_lipschitz_memLp {d e : ℕ} {F : Point d → ℝ} {lam K : ℝ≥0}
    (hF : Primitive F lam) (x : Point d) {r T : ℝ} (hr : 0 < r)
    (hlam : 0<lam) (hl : (lam:ℝ)*r^2≤1/2) (hT0 : 0≤T) (hT1 : T<1)
    {f : Point (d+d) → Point e} (hf : LipschitzWith K f) :
    MemLp f 2 (gibbs (centeringPotential F x r T)) := by
  have hH := productPotential_polySmooth
    (interpolationPotential_polySmooth hF x hr hlam hl hT0 hT1) (gaussianPotential_polySmooth d)
  have ht := productPotential_lowerTail
    (interpolationPotential_lowerTail hF x hr.le (by linarith) hT0 hT1) (gaussianPotential_lowerTail d)
  let : IsProbabilityMeasure (gibbs (centeringPotential F x r T)) :=
    probability_gibbs_of_gaussianTail hH.smooth.continuous ht
  exact growth_vector_memLp (Appell.HasGrowth.lipschitz hf) hf.continuous.aestronglyMeasurable
    (ht.hasExpMoments hH.smooth.continuous).hasMoments

lemma stationary_sq_integral {d e : ℕ} {μ : Measure (Point d)}
    {f : Point d → Point e} (hf : Measurable f) (hi : MemLp f 2 μ)
    {Ψ : Point d → Point d} (hm : Measurable Ψ) (hlaw : μ.map Ψ=μ) :
    Integrable (fun y => ‖f (Ψ y)‖^2) μ ∧
    (∫y,‖f (Ψ y)‖^2 ∂μ)=∫y,‖f y‖^2 ∂μ := by
  have hmap : MeasurePreserving Ψ μ μ := ⟨hm,hlaw⟩
  refine ⟨(hi.comp_measurePreserving hmap).integrable_norm_pow (by norm_num : (2:ℕ)≠0),?_⟩
  exact (integral_map hm.aemeasurable (hf.norm.pow_const 2).aestronglyMeasurable).symm.trans
    (by rw [hlaw])

lemma harmonicStationaryMoment_nonneg {d : ℕ} (F : Point d → ℝ) (x : Point d) (r T : ℝ) :
    0≤harmonicStationaryMoment F x r T := integral_nonneg (fun _ => sq_nonneg _)

lemma harmonicMean_stationary_sq {d : ℕ} {F : Point d → ℝ} {lam : ℝ≥0}
    (hF : Primitive F lam) (x : Point d) {r T : ℝ} (hr : 0 < r)
    (hlam : 0<lam) (hl : (lam:ℝ)*r^2≤1/2) (hT0 : 0≤T) (hT1 : T<1)
    {Ψ : Point (d+d) → Point (d+d)} (hm : Measurable Ψ)
    (hlaw : (gibbs (centeringPotential F x r T)).map Ψ=gibbs (centeringPotential F x r T)) :
    Integrable (fun y => ‖conditionalFieldMean F x r T (productPointEquiv d d (Ψ y)).1‖^2)
      (gibbs (centeringPotential F x r T)) ∧
    (∫y,‖conditionalFieldMean F x r T (productPointEquiv d d (Ψ y)).1‖^2
      ∂gibbs (centeringPotential F x r T))=harmonicStationaryMoment F x r T := by
  have hL := (conditionalFieldMean_lipschitz hF x hr.le hl hT0 hT1).comp
    (LipschitzWith.prod_fst.comp (productPointEquiv d d).toContinuousLinearMap.lipschitz)
  exact stationary_sq_integral hL.continuous.measurable
    (centering_lipschitz_memLp hF x hr hlam hl hT0 hT1 hL) hm hlaw

lemma harmonicFree_initial_rms {d : ℕ} {F : Point d → ℝ} {lam : ℝ≥0}
    (hF : Primitive F lam) (x : Point d) {r T z : ℝ} (hr : 0 < r)
    (hlam : 0<lam) (hl : (lam:ℝ)*r^2≤1/2) (hT0 : 0≤T) (hT1 : T<1)
    (Ξ : Point (d+d) → ℝ → Point (d+d)) (hc : ∀y,Continuous (Ξ y))
    (hinit : ∀y,Ξ y 0=y)
    (hder : ∀y v,v∈Icc (0:ℝ) 1 → HasDerivWithinAt (Ξ y)
      (skewLieField (centeringPotential F x r T) (harmonicSkew d) (Ξ y v)) (Icc (0:ℝ) 1) v)
    (hm : Measurable (fun p : ℝ × Point (d+d) => Ξ p.2 p.1))
    (hlaw : ∀v∈Icc (0:ℝ) 1,(gibbs (centeringPotential F x r T)).map (fun y => Ξ y v)=
      gibbs (centeringPotential F x r T))
    (hz : 0≤z) (hz1 : z≤1) (n : ℕ) (hn : 0<n) (i : Fin (n+1)) :
    Integrable (fun y => ‖harmonicFree n z (productPointEquiv d d y) i-
      (productPointEquiv d d (Ξ y (z*probabilityNodes n i))).1‖^2)
        (gibbs (centeringPotential F x r T)) ∧
    (∫y,‖harmonicFree n z (productPointEquiv d d y) i-
      (productPointEquiv d d (Ξ y (z*probabilityNodes n i))).1‖^2
        ∂gibbs (centeringPotential F x r T))≤(r*T)^2*harmonicStationaryMoment F x r T := by
  have hH := productPotential_polySmooth
    (interpolationPotential_polySmooth hF x hr hlam hl hT0 hT1) (gaussianPotential_polySmooth d)
  have ht := productPotential_lowerTail
    (interpolationPotential_lowerTail hF x hr.le (by linarith) hT0 hT1) (gaussianPotential_lowerTail d)
  let : IsProbabilityMeasure (gibbs (centeringPotential F x r T)) :=
    probability_gibbs_of_gaussianTail hH.smooth.continuous ht
  let q := z*probabilityNodes n i
  have hi := probabilityNodes_mem hn i
  have hq : q∈Icc (0:ℝ) 1 :=
    ⟨mul_nonneg hz hi.1,(mul_le_of_le_one_right hz hi.2).trans hz1⟩
  let μ := volume.restrict (Ioc (0:ℝ) q)
  let M := fun v y => conditionalFieldMean F x r T (productPointEquiv d d (Ξ y v)).1
  have hMm : Measurable (fun p : ℝ × Point (d+d) => M p.1 p.2) := by
    simpa only [one_mul,M] using harmonicMean_measurable (z:=1) hF x hr.le hl hT0 hT1 Ξ hm
  have hs : ∀ᵐv ∂μ,Integrable (fun y => ‖M v y‖^2) (gibbs (centeringPotential F x r T)) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with v hv
    exact (harmonicMean_stationary_sq hF x hr hlam hl hT0 hT1
      (hm.comp (measurable_const.prodMk measurable_id)) (hlaw v ⟨hv.1.le,hv.2.trans hq.2⟩)).1
  have hb : ∀ᵐv ∂μ,(∫y,‖M v y‖^2 ∂gibbs (centeringPotential F x r T))≤
      harmonicStationaryMoment F x r T := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with v hv
    exact (harmonicMean_stationary_sq hF x hr hlam hl hT0 hT1
      (hm.comp (measurable_const.prodMk measurable_id)) (hlaw v ⟨hv.1.le,hv.2.trans hq.2⟩)).2.le
  have he := RMSIntegral.weighted_time_seed hMm.aestronglyMeasurable
    (show AEStronglyMeasurable (fun v => Real.sin (q-v)) μ from by fun_prop)
    (harmonicStationaryMoment_nonneg F x r T)
    (Filter.Eventually.of_forall (fun v => Real.abs_sin_le_one (q-v))) hs hb
  have hid (y : Point (d+d)) : harmonicFree n z (productPointEquiv d d y) i-
      (productPointEquiv d d (Ξ y q)).1=
      (r*T) • (∫v,Real.sin (q-v) • M v y ∂μ) := by
    have hh := conditional_harmonic_integral hF x hr.le hl hT0 hT1 Ξ hc hder y hq
    dsimp only at hh
    rw [hinit,intervalIntegral.integral_of_le hq.1] at hh
    change _=harmonicFree n z (productPointEquiv d d y) i- (r*T) • _ at hh
    rw [hh]
    abel
  have hnorm (v : Point d) : ‖(r*T) • v‖^2=(r*T)^2*‖v‖^2 := by
    rw [norm_smul,mul_pow,Real.norm_eq_abs,sq_abs]
  change Integrable (fun y => ‖harmonicFree n z (productPointEquiv d d y) i-
      (productPointEquiv d d (Ξ y q)).1‖^2) _ ∧
    (∫y,‖harmonicFree n z (productPointEquiv d d y) i-
      (productPointEquiv d d (Ξ y q)).1‖^2 ∂gibbs (centeringPotential F x r T))≤_
  simp_rw [hid,hnorm]
  refine ⟨he.1.const_mul _,?_⟩
  rw [integral_const_mul]
  have hμ : μ.real univ=q := by
    dsimp only [μ,Measure.real]
    rw [Measure.restrict_apply_univ]
    change volume.real (Ioc 0 q)=q
    rw [Real.volume_real_Ioc_of_le hq.1,sub_zero]
  rw [hμ,one_pow,mul_one] at he
  exact mul_le_mul_of_nonneg_left (he.2.trans
    (mul_le_of_le_one_left (harmonicStationaryMoment_nonneg F x r T)
      (pow_le_one₀ hq.1 hq.2))) (sq_nonneg _)
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

section

noncomputable section
namespace LogConcaveSampling
open Set MeasureTheory
open scoped Classical BigOperators NNReal

theorem harmonicPicard_stationary_rms (n : ℕ) (hn : 0<n) :
    ∃A : ℝ≥0,∃C : ℝ,1≤C ∧ ∀{d : ℕ} {F : Point d → ℝ} {lam : ℝ≥0},
      Primitive F lam → ∀(x : Point d) {r R T : ℝ},
      0 < r → 0<lam → (lam:ℝ)*r^2≤1/2 → 0<R → R^2≤1-T^2 → 0≤T → T<1 →
      ∀Ξ : Point (d+d) → ℝ → Point (d+d),
      (∀y,Continuous (Ξ y)) → (∀y,Ξ y 0=y) →
      (∀y v,v∈Icc (0:ℝ) 1 → HasDerivWithinAt (Ξ y)
        (skewLieField (centeringPotential F x r T) (harmonicSkew d) (Ξ y v)) (Icc (0:ℝ) 1) v) →
      Measurable (fun p : ℝ × Point (d+d) => Ξ p.2 p.1) →
      (∀v∈Icc (0:ℝ) 1,(gibbs (centeringPotential F x r T)).map (fun y => Ξ y v)=
        gibbs (centeringPotential F x r T)) →
      ∀z : ℝ,0≤z → z≤1 → A*probabilityMeanLipschitz lam r≤1/2 →
      ∀N : ℕ,∀i : Fin (n+1),
      Integrable (fun y => ‖harmonicPicard F x r T z n N (productPointEquiv d d y) i-
        (productPointEquiv d d (Ξ y (z*probabilityNodes n i))).1‖^2)
          (gibbs (centeringPotential F x r T)) ∧
      (∫y,‖harmonicPicard F x r T z n N (productPointEquiv d d y) i-
        (productPointEquiv d d (Ξ y (z*probabilityNodes n i))).1‖^2
          ∂gibbs (centeringPotential F x r T))≤
        (2*(r*T)*Real.sqrt (4*C^2*(z^(n+1)/(n.factorial:ℝ))^2*
          ((d*((lam:ℝ)*r)^2)*(R⁻¹)^(4*(n+1))*harmonicMeanBudget (n+1)))+
          (A*probabilityMeanLipschitz lam r:ℝ≥0)^N*(r*T)*
            Real.sqrt (harmonicStationaryMoment F x r T))^2 := by
  obtain ⟨A,hA⟩ := harmonicWeight_budget n hn
  obtain ⟨C,hC,hErr⟩ := harmonic_mean_quadrature_rms n hn
  refine ⟨A,C,hC,?_⟩
  intro d F lam hF x r R T hr hlam hl hR hRT hT0 hT1 Ξ hc hinit hder hm hlaw z hz hz1 hq N i
  have hH := productPotential_polySmooth
    (interpolationPotential_polySmooth hF x hr hlam hl hT0 hT1) (gaussianPotential_polySmooth d)
  have ht := productPotential_lowerTail
    (interpolationPotential_lowerTail hF x hr.le (by linarith) hT0 hT1) (gaussianPotential_lowerTail d)
  let : IsProbabilityMeasure (gibbs (centeringPotential F x r T)) :=
    probability_gibbs_of_gaussianTail hH.smooth.continuous ht
  let B := 4*C^2*(z^(n+1)/(n.factorial:ℝ))^2*
    ((d*((lam:ℝ)*r)^2)*(R⁻¹)^(4*(n+1))*harmonicMeanBudget (n+1))
  have hB : 0≤B := by dsimp [B]; positivity [harmonicMeanBudget_nonneg (n+1)]
  let D := (r*T)*Real.sqrt B
  let H := (r*T)*Real.sqrt (harmonicStationaryMoment F x r T)
  have hD : 0≤D := by dsimp [D]; positivity
  have hH0 : 0≤H := by dsimp [H]; positivity
  have ha (j : Fin (n+1)) : MemLp (fun y : Point (d+d) =>
      harmonicFree n z (productPointEquiv d d y) j) 2 (gibbs (centeringPotential F x r T)) := by
    apply centering_lipschitz_memLp hF x hr hlam hl hT0 hT1
    exact (LipschitzWith.eval j).comp ((harmonicFree_lipschitz n z).comp (productPointEquiv d d).lipschitz)
  have hi (j : Fin (n+1)) : z*probabilityNodes n j∈Icc (0:ℝ) 1 :=
    ⟨mul_nonneg hz (probabilityNodes_mem hn j).1,
      (mul_le_of_le_one_right hz (probabilityNodes_mem hn j).2).trans hz1⟩
  have he (j : Fin (n+1)) : MemLp (fun y : Point (d+d) =>
      (productPointEquiv d d (Ξ y (z*probabilityNodes n j))).1) 2
        (gibbs (centeringPotential F x r T)) := by
    have hproj := centering_lipschitz_memLp hF x hr hlam hl hT0 hT1
      (LipschitzWith.prod_fst.comp (productPointEquiv d d).lipschitz)
    exact hproj.comp_measurePreserving ⟨hm.comp (measurable_const.prodMk measurable_id),hlaw _ (hi j)⟩
  have hdef (j : Fin (n+1)) :
      (∫y,‖FinitePicard.step (harmonicWeight n z) (fun _ => harmonicMeanVelocity F x r T)
        (harmonicFree n z (productPointEquiv d d y))
        (fun j => (productPointEquiv d d (Ξ y (z*probabilityNodes n j))).1) j-
        (productPointEquiv d d (Ξ y (z*probabilityNodes n j))).1‖^2
          ∂gibbs (centeringPotential F x r T))≤D^2 := by
    simp_rw [harmonicPicard_exact_defect hF x hr.le hl hT0 hT1 Ξ hc hinit hder hz hz1 n hn,
      norm_smul,mul_pow,Real.norm_eq_abs,sq_abs]
    rw [integral_const_mul]
    dsimp only [D]
    simp only [mul_pow,Real.sq_sqrt hB]
    exact mul_le_mul_of_nonneg_left
      (hErr hF x hr hlam hl hR hRT hT0 hT1 Ξ hc hder hm hlaw z hz hz1 j).2
        (mul_nonneg (sq_nonneg r) (sq_nonneg T))
  have hstart (j : Fin (n+1)) :
      (∫y,‖harmonicFree n z (productPointEquiv d d y) j-
        (productPointEquiv d d (Ξ y (z*probabilityNodes n j))).1‖^2
          ∂gibbs (centeringPotential F x r T))≤H^2 := by
    dsimp only [H]
    rw [mul_pow,Real.sq_sqrt (harmonicStationaryMoment_nonneg F x r T)]
    exact (harmonicFree_initial_rms hF x hr hlam hl hT0 hT1 Ξ hc hinit hder hm hlaw hz hz1 n hn j).2
  have hout := FinitePicard.nodes_rms (A:=A) (harmonicWeight n z)
    (fun _ => harmonicMeanVelocity F x r T)
    (fun _ => harmonicMeanVelocity_lipschitz hF x hr.le hl hT0 hT1)
    (fun j y => harmonicFree n z (productPointEquiv d d y) j)
    (fun j y => (productPointEquiv d d (Ξ y (z*probabilityNodes n j))).1)
    ha he (hA z hz hz1) hq hD hH0 hdef hstart N i
  simpa only [harmonicPicard,FinitePicard.nodes_eq_iterate,D,H,B,mul_assoc] using hout
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

lemma harmonic_position_law {d : ℕ} {F : Point d → ℝ} {lam : ℝ≥0}
    (hF : Primitive F lam) (x : Point d) {r T : ℝ} (hr : 0 ≤ r)
    (hl : (lam:ℝ)*r^2≤1/2) (hT0 : 0≤T) (hT1 : T<1)
    {Ψ : Point (d+d) → Point (d+d)} (hm : Measurable Ψ)
    (hlaw : (gibbs (centeringPotential F x r T)).map Ψ=gibbs (centeringPotential F x r T)) :
    (gibbs (centeringPotential F x r T)).map (fun y => (productPointEquiv d d (Ψ y)).1)=
      interpolationLaw F x r T := by
  change (gibbs (centeringPotential F x r T)).map ((fun y => (productPointEquiv d d y).1) ∘ Ψ)=_
  rw [←Measure.map_map ((productPointEquiv d d).continuous.measurable.fst) hm,hlaw]
  exact centering_position_law hF x hr hl hT0 hT1

lemma rms_bound_pullback {X Y E : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    [NormedAddCommGroup E] [MeasurableSpace E] [BorelSpace E]
    {μ : Measure X} {ν : Measure Y} {f : X → Y} (hf : Measurable f) (hlaw : μ.map f=ν)
    {e : Y → E} (he : Measurable e) (hi : Integrable (fun y => ‖e y‖^2) ν)
    {B : ℝ} (hB : (∫y,‖e y‖^2 ∂ν)≤B) :
    Integrable (fun x => ‖e (f x)‖^2) μ ∧ (∫x,‖e (f x)‖^2 ∂μ)≤B := by
  rw [←hlaw] at hi
  refine ⟨hi.comp_measurable hf,?_⟩
  rw [←integral_map hf.aemeasurable (he.norm.pow_const 2).aestronglyMeasurable,hlaw]
  exact hB

end LogConcaveSampling

end

end

end

end OAI
end

section
-- module Solutions.OAIQ048_LC.LogConcave_Complexity_ProbabilityRmsBudget
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

theorem kernel_probability_errors (n : ℕ) (hn : 0<n) :
    ∃A : ℝ≥0,∃C : ℝ,0≤C ∧ ∃k : ℕ,∀{d : ℕ} {F : Point d → ℝ} {lam : ℝ≥0},
      ∀hF : Primitive F lam,∀(x : Point d) {r : ℝ},∀hr : 0 < r,
      0<lam → ∀hl : (lam:ℝ)*r^2≤1/2,1≤d →
      ∀{T h : ℝ},∀hT0 : 0<T,∀hT1 : T<1,∀hh : 0<h,h≤Real.log 2 →
      A*probabilityMeanLipschitz lam r≤1/2 → ∀N : ℕ,∀s e : ProbabilityNode T h n,
      let S : Icc (0:ℝ) T := ⟨probabilityNodeTime T h n s,probabilityNodeTime_mem hT0 hT1 hh hn s⟩
      let E : Icc (0:ℝ) T := ⟨probabilityNodeTime T h n e,probabilityNodeTime_mem hT0 hT1 hh hn e⟩
      let μ := gibbs (centeringPotential F x r S)
      let forward := probabilityTransport hF x hr.le hl hT0.le hT1 S E
      let pos := fun y : Point (d+d) => (productPointEquiv d d y).1
      (Integrable (fun y => ‖probabilityAnchoredPicard F x r T h n N e (forward (pos y)) s-pos y‖^2) μ ∧
        (∫y,‖probabilityAnchoredPicard F x r T h n N e (forward (pos y)) s-pos y‖^2 ∂μ)≤
          (probabilityRmsBudget F x lam A r h C k n N)^2) ∧
      ∀Ψ : Point (d+d) → Point (d+d),Measurable Ψ → μ.map Ψ=μ →
      Integrable (fun y => ‖probabilityAnchoredPicard F x r T h n (N+1) s (pos (Ψ y)) e-
        forward (pos (Ψ y))‖^2) μ ∧
      (∫y,‖probabilityAnchoredPicard F x r T h n (N+1) s (pos (Ψ y)) e-
        forward (pos (Ψ y))‖^2 ∂μ)≤(probabilityRmsBudget F x lam A r h C k n (N+1))^2 := by
  obtain ⟨A,C,hC,k,hErr⟩ := probabilityAnchored_marginal_rms n hn
  refine ⟨A,C,hC,k,?_⟩
  intro d F lam hF x r hr hlam hl hd T h hT0 hT1 hh hsmall hq N s e
  dsimp only
  let S : Icc (0:ℝ) T := ⟨probabilityNodeTime T h n s,probabilityNodeTime_mem hT0 hT1 hh hn s⟩
  let E : Icc (0:ℝ) T := ⟨probabilityNodeTime T h n e,probabilityNodeTime_mem hT0 hT1 hh hn e⟩
  let μ := gibbs (centeringPotential F x r S)
  let fw := probabilityTransport hF x hr.le hl hT0.le hT1 S E
  let bw := probabilityTransport hF x hr.le hl hT0.le hT1 E S
  let pos := fun y : Point (d+d) => (productPointEquiv d d y).1
  have hpos : Measurable pos := (productPointEquiv d d).continuous.measurable.fst
  have hfw : Continuous fw := probabilityTransport_continuous hF x hr.le hl hT0.le hT1 S E
  have hbw : Continuous bw := probabilityTransport_continuous hF x hr.le hl hT0.le hT1 E S
  have hp : μ.map pos=interpolationLaw F x r S :=
    centering_position_law hF x hr.le hl S.2.1 (S.2.2.trans_lt hT1)
  have hfp : μ.map (fun y => fw (pos y))=interpolationLaw F x r E := by
    change μ.map (fw ∘ pos)=_
    rw [←Measure.map_map hfw.measurable hpos,hp]
    exact probabilityTransport_pushforward hF x hr.le hl hT0.le hT1 S E
  constructor
  · have he := hErr hF x hr hlam hl hd hT0 hT1 hh hsmall hq N e s
    have hm := ((probabilityAnchored_continuous hF x hr.le hl hT0 hT1 hh n hn N e s).sub hbw).measurable
    have h := rms_bound_pullback (hfw.measurable.comp hpos) hfp hm he.1 he.2
    have hc (y : Point d) : bw (fw y)=y := by
      dsimp [bw,fw]
      rw [probabilityTransport_cocycle,probabilityTransport_initial]
    simpa only [Pi.sub_apply,Function.comp_def,hc,probabilityRmsBudget] using h
  · intro Ψ hm hlaw
    have he := hErr hF x hr hlam hl hd hT0 hT1 hh hsmall hq (N+1) s e
    have hΨ := harmonic_position_law hF x hr.le hl S.2.1 (S.2.2.trans_lt hT1) hm hlaw
    exact rms_bound_pullback (hpos.comp hm) hΨ
      ((probabilityAnchored_continuous hF x hr.le hl hT0 hT1 hh n hn (N+1) s e).sub hfw).measurable
      he.1 he.2

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

omit [SecondCountableTopology E] in
lemma lipschitz_error_sq {f g : Ω → E} (hf : Measurable f) (hg : Measurable g)
    {Q : E → H} {K : ℝ≥0} (hQ : LipschitzWith K Q)
    (hi : Integrable (fun y => ‖f y-g y‖^2) μ)
    {B : ℝ} (hB : (∫y,‖f y-g y‖^2 ∂μ)≤B) :
    Integrable (fun y => ‖Q (f y)-Q (g y)‖^2) μ ∧
    (∫y,‖Q (f y)-Q (g y)‖^2 ∂μ)≤(K:ℝ)^2*B := by
  have hpt (y : Ω) : ‖Q (f y)-Q (g y)‖^2≤(K:ℝ)^2*‖f y-g y‖^2 := by
    simpa only [dist_eq_norm,mul_pow] using pow_le_pow_left₀ (dist_nonneg)
      (hQ.dist_le_mul (f y) (g y)) 2
  have hs : Integrable (fun y => ‖Q (f y)-Q (g y)‖^2) μ :=
    (hi.const_mul ((K:ℝ)^2)).mono'
      (((hQ.continuous.measurable.comp hf).sub (hQ.continuous.measurable.comp hg)).norm.pow_const 2).aestronglyMeasurable
      (Filter.Eventually.of_forall (fun y => by simpa only [Real.norm_eq_abs,abs_sq] using hpt y))
  refine ⟨hs,?_⟩
  have hb := integral_mono hs (hi.const_mul ((K:ℝ)^2)) hpt
  rw [integral_const_mul] at hb
  exact hb.trans (mul_le_mul_of_nonneg_left hB (sq_nonneg _))

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

omit [SecondCountableTopology E] in
lemma compose_error_sq {f g : Ω → E} {k : Ω → H}
    (hf : Measurable f) (hg : Measurable g) (hk : Measurable k)
    {Q : E → H} {K : ℝ≥0} (hQ : LipschitzWith K Q)
    (hfg : Integrable (fun y => ‖f y-g y‖^2) μ)
    (hgk : Integrable (fun y => ‖Q (g y)-k y‖^2) μ)
    {A B : ℝ} (hA : (∫y,‖f y-g y‖^2 ∂μ)≤A) (hB : (∫y,‖Q (g y)-k y‖^2 ∂μ)≤B) :
    Integrable (fun y => ‖Q (f y)-k y‖^2) μ ∧
      (∫y,‖Q (f y)-k y‖^2 ∂μ)≤2*(K:ℝ)^2*A+2*B := by
  have hh := lipschitz_error_sq hf hg hQ hfg hA
  simpa only [Function.comp_def,mul_assoc] using add_error_sq (hQ.continuous.measurable.comp hf) (hQ.continuous.measurable.comp hg) hk
    hh.1 hgk hh.2 hB
end LogConcaveSampling.RMSIntegral

end

end

section

noncomputable section
namespace LogConcaveSampling
open Set MeasureTheory ProbabilityTheory RMSIntegral
open scoped Classical NNReal

theorem kernelCorrectionPicard_rms_oai (n : ℕ) (hn : 0<n) :
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
      ∀z : ℝ,0≤z → z≤1 →
      let w := fun y => (productPointEquiv d d (Ξ y z)).1
      let err := fun y => kernelCorrectionPicard F x r T h z n N s e
        (fw (productPointEquiv d d y).1,(productPointEquiv d d y).2)-(fw (w y)-w y)
      Integrable (fun y => ‖err y‖^2) μ ∧
      (∫y,‖err y‖^2 ∂μ)≤
        2*(2*(Lp*probabilityMeanLipschitz lam r):ℝ≥0)^2*
          (32*(probabilityRmsBudget F x lam Ap r h C k n N)^2+
            2*(harmonicRmsBudget F x lam Ah r R S z J n N)^2)+
          2*(probabilityRmsBudget F x lam Ap r h C k n (N+1))^2 := by
  obtain ⟨Ap,C,hC,k,hP⟩ := kernel_probability_errors n hn
  obtain ⟨Ah,J,hJ,hH⟩ := harmonicPicard_stationary_rms n hn
  obtain ⟨Lp,hLp⟩ := probabilityAnchored_lipschitz n hn
  obtain ⟨Lh,hLh⟩ := harmonicPicard_lipschitz n hn
  refine ⟨Ap,Ah,Lp,Lh,C,J,hC,hJ,k,?_⟩
  intro d F lam hF x r hr hlam hl hd T h hT0 hT1 hh hsmall hqp hqh hqlp hqlh N s e
  dsimp only
  let S : Icc (0:ℝ) T := ⟨probabilityNodeTime T h n s,probabilityNodeTime_mem hT0 hT1 hh hn s⟩
  let E : Icc (0:ℝ) T := ⟨probabilityNodeTime T h n e,probabilityNodeTime_mem hT0 hT1 hh hn e⟩
  let μ := gibbs (centeringPotential F x r S)
  let fw := probabilityTransport hF x hr.le hl hT0.le hT1 S E
  intro R hR hRT Ξ hc hinit hder hm hlaw z hz hz1
  let pos := fun y : Point (d+d) => (productPointEquiv d d y).1
  let mom := fun y : Point (d+d) => (productPointEquiv d d y).2
  let b := fun y => probabilityAnchoredPicard F x r T h n N e (fw (pos y)) s
  let H := fun p => harmonicPicard F x r S z n N p (Fin.last n)
  let Q := fun v => probabilityAnchoredPicard F x r T h n (N+1) s v e-v
  let w := fun y => pos (Ξ y z)
  let u := fun y => H (b y,mom y)
  have hpos : Measurable pos := (productPointEquiv d d).continuous.measurable.fst
  have hmom : Measurable mom := (productPointEquiv d d).continuous.measurable.snd
  have hfw : Continuous fw := probabilityTransport_continuous hF x hr.le hl hT0.le hT1 S E
  have hb : Measurable b := (probabilityAnchored_continuous hF x hr.le hl hT0 hT1 hh n hn N e s).measurable.comp
    (hfw.measurable.comp hpos)
  have hW : Measurable w := hpos.comp (hm.comp (measurable_const.prodMk measurable_id))
  have hHL : LipschitzWith 4 H := by
    have he := (LipschitzWith.eval (Fin.last n)).comp
      (hLh hF x hr.le hl S.2.1 (S.2.2.trans_lt hT1) hz hz1 hqlh N).1
    convert he using 1 <;> first | rfl | simp only [one_mul]
  have hQL : LipschitzWith (2*(Lp*probabilityMeanLipschitz lam r)) Q := by
    have he := (LipschitzWith.eval e).comp (hLp hF x hr.le hl hT0 hT1 hh hqlp N s).2
    convert he using 1 <;> first | rfl | simp only [one_mul]
  have hu : Measurable u := hHL.continuous.measurable.comp (hb.prodMk hmom)
  have hprob := hP hF x hr hlam hl hd hT0 hT1 hh hsmall hqp N s e
  have hnorm (y : Point (d+d)) : ‖(b y,mom y)-(pos y,mom y)‖^2=‖b y-pos y‖^2 := by
    simp only [Prod.mk_sub_mk,sub_self,Prod.norm_def,norm_zero,max_eq_left (norm_nonneg _)]
  have hi : Integrable (fun y => ‖(b y,mom y)-(pos y,mom y)‖^2) μ := by
    simpa only [hnorm] using hprob.1.1
  have hbnd : (∫y,‖(b y,mom y)-(pos y,mom y)‖^2 ∂μ)≤
      (probabilityRmsBudget F x lam Ap r h C k n N)^2 := by
    simpa only [hnorm] using hprob.1.2
  have hnum := lipschitz_error_sq (hb.prodMk hmom) (hpos.prodMk hmom) hHL hi hbnd
  have hlast : probabilityNodes n (Fin.last n)=1 := by
    change (n:ℝ)/(n:ℝ)=1
    exact div_self (by exact_mod_cast hn.ne')
  have hharm := hH hF x hr hlam hl hR hRT S.2.1 (S.2.2.trans_lt hT1)
    Ξ hc hinit hder hm hlaw z hz hz1 hqh N (Fin.last n)
  rw [hlast,mul_one] at hharm
  have hharm' : Integrable (fun y => ‖H (pos y,mom y)-w y‖^2) μ ∧
      (∫y,‖H (pos y,mom y)-w y‖^2 ∂μ)≤(harmonicRmsBudget F x lam Ah r R S z J n N)^2 := hharm
  have hstate := add_error_sq hu (hHL.continuous.measurable.comp (hpos.prodMk hmom)) hW
    hnum.1 hharm'.1 hnum.2 hharm'.2
  have hstate' : Integrable (fun y => ‖u y-w y‖^2) μ ∧
      (∫y,‖u y-w y‖^2 ∂μ)≤32*(probabilityRmsBudget F x lam Ap r h C k n N)^2+
        2*(harmonicRmsBudget F x lam Ah r R S z J n N)^2 := by
    simpa only [NNReal.coe_ofNat,show (4:ℝ)^2=16 by norm_num,show (2:ℝ)*16=32 by norm_num,←mul_assoc] using hstate
  have hforward := hprob.2 (fun y => Ξ y z) (hm.comp (measurable_const.prodMk measurable_id)) (hlaw z ⟨hz,hz1⟩)
  have hcancel (y : Point (d+d)) : Q (w y)-(fw (w y)-w y)=
      probabilityAnchoredPicard F x r T h n (N+1) s (w y) e-fw (w y) := by dsimp [Q]; abel
  have hforw' : Integrable (fun y => ‖Q (w y)-(fw (w y)-w y)‖^2) μ ∧
      (∫y,‖Q (w y)-(fw (w y)-w y)‖^2 ∂μ)≤(probabilityRmsBudget F x lam Ap r h C k n (N+1))^2 := by
    simpa only [hcancel] using hforward
  exact compose_error_sq hu hW ((hfw.measurable.comp hW).sub hW) hQL
    hstate'.1 hforw'.1 hstate'.2 hforw'.2

end LogConcaveSampling

end

end

end

end OAI
end

theorem solution : type_of% @OAI.LogConcaveSampling.kernelCorrectionPicard_rms_oai := @OAI.LogConcaveSampling.kernelCorrectionPicard_rms_oai
