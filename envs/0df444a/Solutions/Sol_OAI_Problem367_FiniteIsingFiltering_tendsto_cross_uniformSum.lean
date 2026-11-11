-- Prove2me | solution 1 for OAI.Problem367.FiniteIsingFiltering.tendsto_cross_uniformSum
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T01:42:52.079484+00:00
-- url     : https://prove2.me/submissions/81423f0e-eeb8-4b52-ae0d-b1c2bcd6ae72

import Mathlib
import Definitions.Def_FreeIsing
import Definitions.Def_Q243FI005

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Stochastic_SimpleIntegralIsometry
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory

namespace Problem367.SimpleIntegral

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {μ : Measure Ω}

theorem integral_mul_eq_zero_of_condExp_eq_zero [IsFiniteMeasure μ]
    {m : MeasurableSpace Ω} (hm : m ≤ mΩ) {H D : Ω → ℝ}
    (hH : StronglyMeasurable[m] H) (hD : Integrable D μ)
    (hHD : Integrable (H * D) μ) (hzero : μ[D | m] =ᵐ[μ] 0) :
    ∫ ω, H ω * D ω ∂μ = 0 := by
  have hpull := condExp_mul_of_stronglyMeasurable_left hH hHD hD
  have hCE : μ[H * D | m] =ᵐ[μ] 0 := by
    filter_upwards [hpull, hzero] with ω hp hz
    simp only [Pi.mul_apply, Pi.zero_apply] at hp hz ⊢
    rw [hp, hz, mul_zero]
  calc
    ∫ ω, H ω * D ω ∂μ = ∫ ω, μ[H * D | m] ω ∂μ :=
      (integral_condExp hm).symm
    _ = 0 := by rw [integral_congr_ae hCE]; simp

end Problem367.SimpleIntegral

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Energy_EnergyRiemannApproximation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Filter Set
open scoped NNReal Topology BigOperators

namespace Problem367.EnergyRiemann

theorem point_end (T : ℝ) {n : ℕ} (hn : 0 < n) : point T n n = T := by
  dsimp [point]
  field_simp

theorem point_step (T : ℝ) (n i : ℕ) :
    point T n (i + 1) - point T n i = T / n := by
  simp only [point, Nat.cast_add, Nat.cast_one]
  ring

theorem point_mono {T : ℝ} (hT : 0 ≤ T) (n : ℕ) : Monotone (point T n) := by
  intro i j hij
  exact mul_le_mul_of_nonneg_right (by exact_mod_cast hij) (by positivity)

theorem point_mem {T : ℝ} (hT : 0 ≤ T) {n i : ℕ} (hn : 0 < n) (hi : i ≤ n) :
    point T n i ∈ Icc 0 T := by
  constructor
  · dsimp [point] <;> positivity
  · exact (point_mono hT n hi).trans_eq (point_end T hn)

end Problem367.EnergyRiemann

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Energy_CrossEnergyRiemann
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Filter Set
open scoped NNReal Topology BigOperators

namespace Problem367.CrossEnergyRiemann

open EnergyRiemann

theorem error_le {f : ℝ → ℝ → ℝ} (hf : Continuous (Function.uncurry f))
    {T ε : ℝ} (hT : 0 ≤ T) {n : ℕ} (hn : 0 < n)
    (hmod : ∀ i < n, ∀ r ∈ Icc (point T n i) (point T n (i + 1)),
      |f (point T n i) r - f r r| ≤ ε) :
    |sum f T n - ∫ r in (0 : ℝ)..T, f r r| ≤ ε * T := by
  have hd : Continuous (fun r => f r r) := hf.comp (continuous_id.prodMk continuous_id)
  have hs (x : ℝ) : Continuous (f x) := hf.comp (continuous_const.prodMk continuous_id)
  have hpart := intervalIntegral.sum_integral_adjacent_intervals
    (μ := volume) (a := point T n) (n := n) (fun i _ => hd.intervalIntegrable _ _)
  rw [point_zero, point_end T hn] at hpart
  have heq : sum f T n - (∫ r in (0 : ℝ)..T, f r r) =
      ∑ i ∈ Finset.range n, ∫ r in point T n i..point T n (i + 1),
        f (point T n i) r - f r r := by
    rw [sum, ← hpart, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    exact (intervalIntegral.integral_sub ((hs _).intervalIntegrable _ _)
      (hd.intervalIntegrable _ _)).symm
  rw [heq]
  calc
    _ ≤ ∑ i ∈ Finset.range n,
        |∫ r in point T n i..point T n (i + 1), f (point T n i) r - f r r| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i ∈ Finset.range n, ε * (T / n) := by
      apply Finset.sum_le_sum
      intro i hi
      have hle := point_mono hT n (Nat.le_succ i)
      have hb := intervalIntegral.norm_integral_le_of_norm_le_const
        (a := point T n i) (b := point T n (i + 1)) (C := ε)
        (f := fun r => f (point T n i) r - f r r) (fun r hr => ?_)
      · simpa only [Real.norm_eq_abs, point_step,
          abs_of_nonneg (div_nonneg hT (Nat.cast_nonneg n))] using hb
      · rw [uIoc_of_le hle] at hr
        exact hmod i (Finset.mem_range.mp hi) r ⟨hr.1.le, hr.2⟩
    _ = ε * T := by
      simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hn)
      field_simp

theorem tendsto_sum {f : ℝ → ℝ → ℝ} (hf : Continuous (Function.uncurry f))
    {T : ℝ} (hT : 0 ≤ T) :
    Tendsto (sum f T) atTop (𝓝 (∫ r in (0 : ℝ)..T, f r r)) := by
  apply Metric.tendsto_atTop.mpr
  intro ε hε
  let η := ε / (T + 1)
  have hη : 0 < η := div_pos hε (by linarith)
  have hu := (isCompact_Icc.prod isCompact_Icc).uniformContinuousOn_of_continuous
    (s := (Icc (0 : ℝ) T) ×ˢ (Icc (0 : ℝ) T)) hf.continuousOn
  obtain ⟨δ, hδ, hmod⟩ := Metric.uniformContinuousOn_iff.mp hu η hη
  have hw : Tendsto (fun n : ℕ => T / (n : ℝ)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
  obtain ⟨N, hN⟩ := ((hw.eventually (gt_mem_nhds hδ)).and
    (eventually_ge_atTop 1)).exists_forall_of_atTop
  refine ⟨N, ?_⟩
  intro n hn
  obtain ⟨hnδ, hnpos⟩ := hN n hn
  have he := error_le hf hT (show 0 < n from hnpos) (ε := η) ?_
  · change |sum f T n - ∫ r in (0 : ℝ)..T, f r r| < ε
    apply he.trans_lt
    change ε / (T + 1) * T < ε
    rw [div_mul_eq_mul_div]
    apply (div_lt_iff₀ (by linarith : 0 < T + 1)).mpr
    nlinarith
  · intro i hi r hr
    have hl := point_mem hT hnpos hi.le
    have hh := point_mem hT hnpos (Nat.succ_le_of_lt hi)
    have hrT : r ∈ Icc (0 : ℝ) T := ⟨hl.1.trans hr.1, hr.2.trans hh.2⟩
    have hdist : dist (point T n i) r < δ := by
      rw [Real.dist_eq, abs_of_nonpos (sub_nonpos.mpr hr.1)]
      have hstep := point_step T n i
      linarith [hr.2]
    have hpdist : dist (point T n i, r) (r, r) < δ := by
      simpa only [Prod.dist_eq, dist_self, max_eq_left dist_nonneg] using hdist
    exact (hmod _ ⟨hl, hrT⟩ _ ⟨hrT, hrT⟩ hpdist).le

theorem continuous_crossMoment {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsFiniteMeasure P] {H : ℝ≥0 → Ω → ℝ}
    (hm : ∀ t, AEStronglyMeasurable (H t) P)
    (hc : ∀ᵐ ω ∂P, Continuous (fun t => H t ω))
    {C : ℝ} (hC : 0 ≤ C) (hb : ∀ᵐ ω ∂P, ∀ t, |H t ω| ≤ C) :
    Continuous (fun p : ℝ≥0 × ℝ≥0 => ∫ ω, H p.1 ω * H p.2 ω ∂P) := by
  apply continuous_of_dominated (bound := fun _ => C ^ 2)
  · intro p
    exact (hm p.1).mul (hm p.2)
  · intro p
    filter_upwards [hb] with ω hω
    rw [Real.norm_eq_abs, abs_mul, pow_two]
    exact mul_le_mul (hω p.1) (hω p.2) (abs_nonneg _) hC
  · exact integrable_const _
  · filter_upwards [hc] with ω hω
    exact (hω.comp continuous_fst).mul (hω.comp continuous_snd)

theorem tendsto_cross_energy {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsFiniteMeasure P] {H : ℝ≥0 → Ω → ℝ}
    (hm : ∀ t, AEStronglyMeasurable (H t) P)
    (hc : ∀ᵐ ω ∂P, Continuous (fun t => H t ω))
    {C : ℝ} (hC : 0 ≤ C) (hb : ∀ᵐ ω ∂P, ∀ t, |H t ω| ≤ C)
    (T : ℝ≥0) :
    Tendsto (fun n : ℕ => ∑ i ∈ Finset.range n,
      ∫ r in (BrownianGrid.uniformGrid T n i : ℝ)..(BrownianGrid.uniformGrid T n (i + 1) : ℝ),
        ∫ ω, H (BrownianGrid.uniformGrid T n i) ω * H r.toNNReal ω ∂P)
      atTop (𝓝 (∫ r in (0 : ℝ)..(T : ℝ), ∫ ω, H r.toNNReal ω ^ 2 ∂P)) := by
  have hcont : Continuous (fun p : ℝ × ℝ =>
      ∫ ω, H p.1.toNNReal ω * H p.2.toNNReal ω ∂P) :=
    (continuous_crossMoment hm hc hC hb).comp
      (show Continuous (fun p : ℝ × ℝ => (p.1.toNNReal, p.2.toNNReal)) by fun_prop)
  have hp (n i : ℕ) : point (T : ℝ) n i = (BrownianGrid.uniformGrid T n i : ℝ) := by
    simp only [point, BrownianGrid.uniformGrid, NNReal.coe_mul, NNReal.coe_div,
      NNReal.coe_natCast]
    ring
  have hl := tendsto_sum (f := fun (s t : ℝ) =>
    ∫ ω, H s.toNNReal ω * H t.toNNReal ω ∂P) hcont T.coe_nonneg
  change Tendsto (fun n => CrossEnergyRiemann.sum
    (fun (s t : ℝ) => ∫ ω, H s.toNNReal ω * H t.toNNReal ω ∂P) (T : ℝ) n)
    atTop (𝓝 (∫ r in (0 : ℝ)..(T : ℝ), ∫ ω, H r.toNNReal ω * H r.toNNReal ω ∂P)) at hl
  simpa only [CrossEnergyRiemann.sum, hp, Real.toNNReal_coe, pow_two] using hl

end Problem367.CrossEnergyRiemann

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Posterior_FinitePosterior
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open scoped BigOperators

namespace Problem367.FinitePosterior

variable {ι : Type*} [Fintype ι]

lemma partition_ne_zero [Nonempty ι] (energy signal : ι → ℝ) (t : ℝ) :
    partition energy signal t ≠ 0 := ne_of_gt (partition_pos energy signal t)

lemma mass_pos [Nonempty ι] (energy signal : ι → ℝ) (t : ℝ) (s : ι) :
    0 < mass energy signal t s :=
  div_pos (weight_pos energy signal t s) (partition_pos energy signal t)

lemma sum_mass [Nonempty ι] (energy signal : ι → ℝ) (t : ℝ) :
    ∑ s, mass energy signal t s = 1 := by
  simp only [mass, ← Finset.sum_div]
  change partition energy signal t / partition energy signal t = 1
  exact div_self (partition_ne_zero energy signal t)

lemma mean_eq_sum_mass (energy signal observable : ι → ℝ) (t : ℝ) :
    mean energy signal observable t = ∑ s, observable s * mass energy signal t s := by
  simp only [mean, mass, ← mul_div_assoc, ← Finset.sum_div]

end Problem367.FinitePosterior

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Posterior_DerivativeBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open scoped BigOperators

namespace Problem367.FinitePosterior

variable {S : Type*} [Fintype S] [Nonempty S]

theorem abs_mean_le (energy signal observable : S → ℝ) (t A : ℝ)
    (hbound : ∀ s, |observable s| ≤ A) :
    |mean energy signal observable t| ≤ A := by
  rw [mean_eq_sum_mass]
  calc
    |∑ s, observable s * mass energy signal t s| ≤
        ∑ s, |observable s * mass energy signal t s| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ s, A * mass energy signal t s := by
      apply Finset.sum_le_sum
      intro s _
      rw [abs_mul, abs_of_pos (mass_pos energy signal t s)]
      exact mul_le_mul_of_nonneg_right (hbound s) (mass_pos energy signal t s).le
    _ = A := by rw [← Finset.mul_sum, sum_mass, mul_one]

omit [Fintype S] [Nonempty S] in
lemma abs_spin_eq_one (signal : S → ℝ)
    (hsignal : ∀ s, signal s = -1 ∨ signal s = 1) (s : S) : |signal s| = 1 := by
  rcases hsignal s with hs | hs <;> simp [hs]

theorem abs_mean_spin_le_one (energy signal : S → ℝ) (t : ℝ)
    (hsignal : ∀ s, signal s = -1 ∨ signal s = 1) :
    |mean energy signal signal t| ≤ 1 :=
  abs_mean_le energy signal signal t 1 (fun s => (abs_spin_eq_one signal hsignal s).le)

theorem abs_tiltCovariance_le (energy signal observable : S → ℝ) (t A : ℝ)
    (hsignal : ∀ s, signal s = -1 ∨ signal s = 1)
    (hbound : ∀ s, |observable s| ≤ A) :
    |tiltCovariance energy signal observable t| ≤ 2 * A := by
  have hA : 0 ≤ A := (abs_nonneg (observable (Classical.arbitrary S))).trans
    (hbound (Classical.arbitrary S))
  have hprod : ∀ s, |observable s * signal s| ≤ A := by
    intro s
    rw [abs_mul, abs_spin_eq_one signal hsignal s, mul_one]
    exact hbound s
  unfold tiltCovariance
  calc
    |mean energy signal (fun s => observable s * signal s) t -
        mean energy signal observable t * mean energy signal signal t| ≤
      |mean energy signal (fun s => observable s * signal s) t| +
        |mean energy signal observable t * mean energy signal signal t| := abs_sub _ _
    _ ≤ A + A * 1 := add_le_add (abs_mean_le energy signal _ t A hprod)
      (by
        rw [abs_mul]
        exact mul_le_mul (abs_mean_le energy signal observable t A hbound)
          (abs_mean_spin_le_one energy signal t hsignal) (abs_nonneg _) hA)
    _ = 2 * A := by ring

section Fields

variable {V : Type*} [Fintype V]

theorem abs_fieldCovariance_le (energy : S → ℝ) (spin : S → V → ℝ)
    (observable : S → ℝ) (x : V → ℝ) (u : V) (A : ℝ)
    (hcoord : ∀ s, spin s u = -1 ∨ spin s u = 1)
    (hbound : ∀ s, |observable s| ≤ A) :
    |fieldCovariance energy spin observable x u| ≤ 2 * A := by
  have h := abs_tiltCovariance_le (fieldEnergy energy spin x) (fun s => spin s u)
    observable 0 A hcoord hbound
  simpa only [tiltCovariance, mean_fieldEnergy_zero, fieldCovariance] using h

end Fields

end Problem367.FinitePosterior

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Posterior_GaussianTimeDerivative
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped BigOperators Topology

namespace Problem367.FinitePosterior

variable {V : Type*} [Fintype V]

section Posterior

variable {S : Type*} [Fintype S] [Nonempty S]

theorem continuous_fieldCovariance (energy : S → ℝ) (spin : S → V → ℝ)
    (observable : S → ℝ) (v : V) :
    Continuous (fun x => fieldCovariance energy spin observable x v) := by
  exact (continuous_fieldMean energy spin (fun s => observable s * spin s v)).sub
    ((continuous_fieldMean energy spin observable).mul
      (continuous_fieldMean energy spin (fun s => spin s v)))

end Posterior

end Problem367.FinitePosterior

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Stochastic_FiniteIsingBrownianEnergy
attribute [-instance] _root_.OAI.Problem367.WienerSampler.pathMeasurableSpace _root_.OAI.Problem367.reducedTailFintype _root_.OAI.Problem367.treeBallFintype _root_.OAI.Problem367.treeShellFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal

namespace Problem367

theorem finiteBrownianNoise_restrict_measurePreserving
    {ι Ω : Type*} [MeasurableSpace Ω]
    (ν : ι → Measure Ω) {B : ι → ℝ≥0 → Ω → ℝ}
    (hB : ∀ i, IsPreBrownianReal (B i) (ν i))
    (hmB : ∀ i t, Measurable (B i t)) (D : Finset ι) (t : ℝ≥0) :
    MeasurePreserving (fun ω (v : D) => B v t (ω v))
      (Measure.infinitePi ν) (Measure.pi (fun _ : D => gaussianReal 0 t)) := by
  have (i : ι) : IsProbabilityMeasure (ν i) :=
    (hB i).isGaussianProcess.isProbabilityMeasure
  have hr : MeasurePreserving (D.restrict : (ι → Ω) → D → Ω)
      (Measure.infinitePi ν) (Measure.pi fun v : D => ν v) :=
    ⟨D.measurable_restrict, Measure.infinitePi_map_restrict ν⟩
  have he : MeasurePreserving (fun ω (v : D) => B v t (ω v))
      (Measure.pi fun v : D => ν v) (Measure.pi fun _ : D => gaussianReal 0 t) := by
    refine ⟨Measurable.of_eval (fun vertex => (hmB vertex t).comp
      (measurable_pi_apply vertex)), ?_⟩
    rw [Measure.pi_map_pi (μ := fun v : D => ν v)
      (f := fun v ω => B v t ω) (fun v => (hmB v t).aemeasurable)]
    congr 1
    funext v
    exact (hB v).hasLaw_eval t |>.map_eq
  exact he.comp hr

end Problem367

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Posterior_FiniteIsingFilteringRepresentation
attribute [-instance] _root_.OAI.Problem367.IsingConditionalCopyBounds.graphLaw_isProbabilityMeasure _root_.OAI.Problem367.IsingObservationFactor.copies_probability _root_.OAI.Problem367.IsingObservationFactor.kernel_markov _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_observationLaw_probability _root_.OAI.Problem367.IsingObservationInnovation.observationLaw_probability _root_.OAI.Problem367.TreeKoopman.labelProbability _root_.OAI.Problem367.WienerSampler.pathMeasurableSpace _root_.OAI.Problem367.freeIsingMeasure_probability _root_.OAI.Problem367.reducedTailFintype _root_.OAI.Problem367.treeBallFintype _root_.OAI.Problem367.treeShellFintype
attribute [-simp] _root_.OAI.Problem367.ConnectedHull.pathAssignment_path _root_.OAI.Problem367.ConnectedHull.path_last _root_.OAI.Problem367.ConnectedHull.path_zero _root_.OAI.Problem367.ConnectedHull.prefix_length _root_.OAI.Problem367.ConnectedHull.prefix_zero _root_.OAI.Problem367.CutContinuationChannels.averageChannel_globalCone _root_.OAI.Problem367.CutContinuationChannels.continuationChannel_globalCone _root_.OAI.Problem367.FactorObservable.centeredSpinLp_coe _root_.OAI.Problem367.FiniteIsingSplit.splitEquiv_fst _root_.OAI.Problem367.FiniteIsingSplit.splitEquiv_snd _root_.OAI.Problem367.FinitePathGibbs.tailPartition_zero _root_.OAI.Problem367.GaussianTreeResponseNaturality.fieldEquiv_apply_image _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_apply _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_uniformObservation _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_zero _root_.OAI.Problem367.IsingObservationInnovation.uniformObservation_relabel _root_.OAI.Problem367.IsingOrientedPath.attenuation_outward _root_.OAI.Problem367.IsingOrientedPath.endpoint_extensionAt _root_.OAI.Problem367.LocalSupportGeometry.prefixVertex_length _root_.OAI.Problem367.PathSideBranches.parent_sideVertex _root_.OAI.Problem367.PathSideBranches.restrictNoisyRegion_array _root_.OAI.Problem367.PathSideBranches.sideVertex_length _root_.OAI.Problem367.PathSideBranches.sideVertex_val _root_.OAI.Problem367.PosteriorChain.transition_spinMean _root_.OAI.Problem367.PosteriorChain.transition_sum _root_.OAI.Problem367.RootedBroadcast.flipBranchToComplement_val _root_.OAI.Problem367.RootedBroadcast.pos_spinMul _root_.OAI.Problem367.RootedBroadcast.prefixFlip_branchRoot _root_.OAI.Problem367.RootedBroadcast.prefixFlip_root _root_.OAI.Problem367.RootedBroadcast.prefixTreeAut_symm_branchRoot _root_.OAI.Problem367.RootedBroadcast.prefixTreeAut_symm_root _root_.OAI.Problem367.RootedBroadcast.spinMul_pos _root_.OAI.Problem367.RootedBroadcast.spinMul_self _root_.OAI.Problem367.TreeConeCoding.length_vertex _root_.OAI.Problem367.TreeConeCoding.vertex_nil _root_.OAI.Problem367.TreeConeCoding.vertex_val _root_.OAI.Problem367.TreeGibbsAut.spinEquiv_apply_image _root_.OAI.Problem367.TreeKoopman.centeredAverage_apply_coe _root_.OAI.Problem367.TreeKoopman.centeredAverage_pow_apply_coe _root_.OAI.Problem367.TreeKoopman.centeredGenerator_apply_coe _root_.OAI.Problem367.TreeKoopman.centeredGenerator_sq _root_.OAI.Problem367.TreeKoopman.generatorOperator_sq _root_.OAI.Problem367.TreeKoopman.reverseVertex_twice _root_.OAI.Problem367.TreeKoopman.wordRelabel_cons _root_.OAI.Problem367.TreeKoopman.wordRelabel_nil _root_.OAI.Problem367.TreeLawKoopman.centeredAverage_apply_coe _root_.OAI.Problem367.TreeLawKoopman.generatorOperator_sq _root_.OAI.Problem367.TreePathGibbs.vertexEquiv_val _root_.OAI.Problem367.branchColorAut_length _root_.OAI.Problem367.branchColorAut_singleton _root_.OAI.Problem367.branchColorAut_val _root_.OAI.Problem367.branchColorMap_symm_apply _root_.OAI.Problem367.card_treeBallFinset _root_.OAI.Problem367.card_treeNeighborFinset _root_.OAI.Problem367.colorPermAut_length _root_.OAI.Problem367.colorPermAut_nil _root_.OAI.Problem367.colorPermAut_val _root_.OAI.Problem367.colorPermMap_symm_apply _root_.OAI.Problem367.colorPermMap_val _root_.OAI.Problem367.connectedSpinEncode_apply_root _root_.OAI.Problem367.connectedSpinEquiv_apply _root_.OAI.Problem367.dropVertex_length _root_.OAI.Problem367.dropVertex_val _root_.OAI.Problem367.iUnion_treeBallFinset _root_.OAI.Problem367.mem_rootComplementFinset _root_.OAI.Problem367.mem_rootComponentFinset _root_.OAI.Problem367.mem_rootComponentIndices _root_.OAI.Problem367.mem_treeBallFinset _root_.OAI.Problem367.mem_treeNeighborFinset _root_.OAI.Problem367.parentVertex_length _root_.OAI.Problem367.parentVertex_val _root_.OAI.Problem367.prefixColorAut_length _root_.OAI.Problem367.prefixColorAut_val _root_.OAI.Problem367.prefixColorMap_symm_apply _root_.OAI.Problem367.prefixFlip_twice _root_.OAI.Problem367.spinAgreementCode_eq_neg_iff _root_.OAI.Problem367.spinAgreementCode_eq_pos_iff _root_.OAI.Problem367.spinSign_flip _root_.OAI.Problem367.sum_treeShell_zero _root_.OAI.Problem367.tsum_treeShell_radial _root_.OAI.Problem367.vertexSampler_relabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal Topology

namespace Problem367.FiniteIsingFiltering

local instance finiteIsingFilteringNonemptySpin : Nonempty IsingSpin := ⟨.neg⟩

variable {d : ℕ} {Ω : Type*} [MeasurableSpace Ω]

lemma observationFiltration_le_signal
    (B : TreeVertex d → ℝ≥0 → Ω → ℝ)
    (hmB : ∀ i t, Measurable (B i t)) (D : Finset (TreeVertex d)) :
    observationFiltration B hmB D ≤ signalArrayFiltration B hmB := by
  apply arrayNaturalFiltration_le
  intro i t
  exact (arrayNaturalFiltration_stronglyAdapted (plantedArrayObservation B signal)
    (plantedArrayObservation_measurable hmB measurable_signal) i t).mono
      (arrayObservationFiltration_le_signalArrayFiltration B hmB signal measurable_signal t)

lemma observationFiltration_eq_comap
    (B : TreeVertex d → ℝ≥0 → Ω → ℝ)
    (hmB : ∀ i t, Measurable (B i t)) (D : Finset (TreeVertex d)) (t : ℝ≥0) :
    observationFiltration B hmB D t = MeasurableSpace.comap
      (fun p : State d Ω => fun i : D => fun s : Set.Iic t =>
        (s.1 : ℝ) * spinSign (p.1 i) + B i s.1 (p.2 i)) inferInstance := by
  rw [observationFiltration, arrayNaturalFiltration_eq_comap]
  congr 1
  ext p i s
  simp only [plantedArrayObservation, signal, add_comm]

omit [MeasurableSpace Ω] in
lemma mean_eq_fieldMean (beta : ℝ) (D : Finset (TreeVertex d)) (v : D)
    (B : TreeVertex d → ℝ≥0 → Ω → ℝ) (t : ℝ≥0) (p : State d Ω) :
    mean beta D v B t p = FinitePosterior.fieldMean (finiteIsingEnergy beta D)
      (fun eta u => spinSign (eta u)) (fun eta => spinSign (eta v))
      (fun i : D => plantedArrayObservation B signal i t p) := by
  unfold mean finiteIsingBrownianMean
  congr 1
  ext i
  simp only [finiteIsingBrownianObservation, Real.toNNReal_coe,
    plantedArrayObservation, signal, add_comm]

omit [MeasurableSpace Ω] in
lemma covariance_eq_fieldCovariance (beta : ℝ) (D : Finset (TreeVertex d)) (v u : D)
    (B : TreeVertex d → ℝ≥0 → Ω → ℝ) (t : ℝ≥0) (p : State d Ω) :
    covariance beta D v u B t p = FinitePosterior.fieldCovariance (finiteIsingEnergy beta D)
      (fun eta w => spinSign (eta w)) (fun eta => spinSign (eta v))
      (fun i : D => plantedArrayObservation B signal i t p) u := by
  unfold covariance finiteIsingBrownianCovariance
  congr 1
  ext i
  simp only [finiteIsingBrownianObservation, Real.toNNReal_coe,
    plantedArrayObservation, signal, add_comm]

omit [MeasurableSpace Ω] in
lemma abs_covariance_le_two (beta : ℝ) (D : Finset (TreeVertex d)) (v u : D)
    (B : TreeVertex d → ℝ≥0 → Ω → ℝ) (t : ℝ≥0) (p : State d Ω) :
    |covariance beta D v u B t p| ≤ 2 := by
  rw [covariance_eq_fieldCovariance]
  apply (FinitePosterior.abs_fieldCovariance_le _ _ _ _ _ 1 ?_ ?_).trans_eq
    (by norm_num)
  · intro eta
    cases eta u <;> simp [spinSign]
  · intro eta
    cases eta v <;> simp [spinSign]

lemma stronglyAdapted_mean (beta : ℝ) (D : Finset (TreeVertex d)) (v : D)
    (B : TreeVertex d → ℝ≥0 → Ω → ℝ) (hmB : ∀ i t, Measurable (B i t)) :
    StronglyAdapted (observationFiltration B hmB D) (mean beta D v B) := by
  intro t
  have hobs : StronglyMeasurable[observationFiltration B hmB D t]
      (fun p : State d Ω => fun i : D => plantedArrayObservation B signal i t p) := by
    apply Measurable.stronglyMeasurable
    refine @Measurable.of_eval (State d Ω) D (fun _ => ℝ)
      (observationFiltration B hmB D t) (fun _ => inferInstance) _ ?_
    intro i
    exact (arrayNaturalFiltration_stronglyAdapted
      (fun j : D => plantedArrayObservation B signal j)
      (fun j r => plantedArrayObservation_measurable hmB measurable_signal j r) i t).measurable
  have h := (FinitePosterior.continuous_fieldMean (finiteIsingEnergy beta D)
    (fun eta u => spinSign (eta u)) (fun eta => spinSign (eta v))).comp_stronglyMeasurable hobs
  change StronglyMeasurable[observationFiltration B hmB D t]
    (fun p => mean beta D v B t p)
  simp_rw [mean_eq_fieldMean]
  exact h

lemma stronglyAdapted_covariance (beta : ℝ) (D : Finset (TreeVertex d)) (v u : D)
    (B : TreeVertex d → ℝ≥0 → Ω → ℝ) (hmB : ∀ i t, Measurable (B i t)) :
    StronglyAdapted (observationFiltration B hmB D) (covariance beta D v u B) := by
  intro t
  have hobs : StronglyMeasurable[observationFiltration B hmB D t]
      (fun p : State d Ω => fun i : D => plantedArrayObservation B signal i t p) := by
    apply Measurable.stronglyMeasurable
    refine @Measurable.of_eval (State d Ω) D (fun _ => ℝ)
      (observationFiltration B hmB D t) (fun _ => inferInstance) _ ?_
    intro i
    exact (arrayNaturalFiltration_stronglyAdapted
      (fun j : D => plantedArrayObservation B signal j)
      (fun j r => plantedArrayObservation_measurable hmB measurable_signal j r) i t).measurable
  have h := (FinitePosterior.continuous_fieldCovariance (finiteIsingEnergy beta D)
    (fun eta w => spinSign (eta w)) (fun eta => spinSign (eta v)) u).comp_stronglyMeasurable hobs
  change StronglyMeasurable[observationFiltration B hmB D t]
    (fun p => covariance beta D v u B t p)
  simp_rw [covariance_eq_fieldCovariance]
  exact h

omit [MeasurableSpace Ω] in
lemma continuous_mean (beta : ℝ) (D : Finset (TreeVertex d)) (v : D)
    (B : TreeVertex d → ℝ≥0 → Ω → ℝ)
    (hcB : ∀ i omega, Continuous (fun t => B i t omega)) (p : State d Ω) :
    Continuous (fun t => mean beta D v B t p) := by
  simp only [mean_eq_fieldMean]
  apply (FinitePosterior.continuous_fieldMean _ _ _).comp
  apply continuous_pi
  intro i
  exact (hcB i (p.2 i)).add (NNReal.continuous_coe.mul continuous_const)

omit [MeasurableSpace Ω] in
lemma continuous_covariance (beta : ℝ) (D : Finset (TreeVertex d)) (v u : D)
    (B : TreeVertex d → ℝ≥0 → Ω → ℝ)
    (hcB : ∀ i omega, Continuous (fun t => B i t omega)) (p : State d Ω) :
    Continuous (fun t => covariance beta D v u B t p) := by
  simp only [covariance_eq_fieldCovariance]
  apply (FinitePosterior.continuous_fieldCovariance _ _ _ _).comp
  apply continuous_pi
  intro i
  exact (hcB i (p.2 i)).add (NNReal.continuous_coe.mul continuous_const)

lemma progressive_mean (beta : ℝ) (D : Finset (TreeVertex d)) (v : D)
    (B : TreeVertex d → ℝ≥0 → Ω → ℝ) (hmB : ∀ i t, Measurable (B i t))
    (hcB : ∀ i omega, Continuous (fun t => B i t omega)) :
    IsStronglyProgressive (observationFiltration B hmB D) (mean beta D v B) :=
  (stronglyAdapted_mean beta D v B hmB).isStronglyProgressive_of_continuous
    (continuous_mean beta D v B hcB)

end Problem367.FiniteIsingFiltering

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Estimates_ProgressivePrimitive
attribute [-instance] _root_.OAI.Problem367.WienerSampler.pathMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace Problem367

theorem compensated_observation_martingale_of_progressive_bounded
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsFiniteMeasure P]
    {F G : Filtration ℝ≥0 mΩ} {B m : ℝ≥0 → Ω → ℝ} {σ : Ω → ℝ}
    (hB : Martingale B G P) (hFG : ∀ t, F t ≤ G t) (hσ : Integrable σ P)
    (hXad : StronglyAdapted F (fun t ω => B t ω + (t : ℝ) * σ ω))
    (hm : IsStronglyProgressive F m)
    (hposterior : ∀ t, m t =ᵐ[P] P[σ | F t])
    (C : ℝ) (hbound : ∀ t, ∀ᵐ ω ∂P, |m t ω| ≤ C) :
    Martingale (fun t ω => B t ω + (t : ℝ) * σ ω -
      nnrealTimePrimitive m t ω) F P := by
  exact compensated_observation_martingale_of_posterior_version hB hFG hσ hXad
    hm.stronglyAdapted hposterior (stronglyAdapted_nnrealTimePrimitive hm)
    (fun s t _ => integrable_nnreal_process_interval_of_progressive_bounded hm C hbound s t)

theorem compensated_observation_martingale_of_bounded_signal
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsFiniteMeasure P]
    {F G : Filtration ℝ≥0 mΩ} {B m : ℝ≥0 → Ω → ℝ} {σ : Ω → ℝ}
    (hB : Martingale B G P) (hFG : ∀ t, F t ≤ G t) (hσ : Integrable σ P)
    (hXad : StronglyAdapted F (fun t ω => B t ω + (t : ℝ) * σ ω))
    (hm : IsStronglyProgressive F m)
    (hposterior : ∀ t, m t =ᵐ[P] P[σ | F t])
    (C : ℝ) (hbound : ∀ᵐ ω ∂P, |σ ω| ≤ C) :
    Martingale (fun t ω => B t ω + (t : ℝ) * σ ω -
      nnrealTimePrimitive m t ω) F P := by
  apply compensated_observation_martingale_of_progressive_bounded hB hFG hσ hXad
    hm hposterior C
  intro t
  filter_upwards [hposterior t, ae_bdd_abs_condExp_of_ae_bdd_abs (m := F t) hbound]
    with ω heq hb
  rwa [heq]

end Problem367

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Posterior_FilteringCrossEnergy
attribute [-instance] _root_.OAI.Problem367.WienerSampler.pathMeasurableSpace
attribute [-simp] _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_apply _root_.OAI.Problem367.innovationPath_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal

namespace Problem367.FilteringCrossEnergy

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}

theorem integral_test_condExp [IsFiniteMeasure P]
    {m : MeasurableSpace Ω} (hm : m ≤ mΩ) {Q H : Ω → ℝ}
    (hQ : Integrable Q P) (hH : StronglyMeasurable[m] H)
    (hHQ : Integrable (H * Q) P) :
    (∫ ω, H ω * P[Q | m] ω ∂P) = ∫ ω, H ω * Q ω ∂P := by
  have hp := condExp_mul_of_stronglyMeasurable_left hH hHQ hQ
  calc
    _ = ∫ ω, P[H * Q | m] ω ∂P := by
      apply integral_congr_ae
      filter_upwards [hp] with ω hω
      exact hω.symm
    _ = _ := integral_condExp hm

theorem integrable_bounded_mul {Q H : Ω → ℝ} {A : ℝ}
    (hQ : Integrable Q P) (hH : AEStronglyMeasurable H P)
    (hHb : ∀ᵐ ω ∂P, |H ω| ≤ A) :
    Integrable (fun ω => H ω * Q ω) P := by
  apply hQ.bdd_mul hH
  simpa only [Real.norm_eq_abs] using hHb

theorem integral_test_covariance [IsFiniteMeasure P]
    {m : MeasurableSpace Ω} (hm : m ≤ mΩ) {Q S H a : Ω → ℝ} {A C : ℝ}
    (hQ : Integrable Q P) (hQS : Integrable (fun ω => Q ω * S ω) P)
    (hH : StronglyMeasurable[m] H) (ha : StronglyMeasurable[m] a)
    (hHb : ∀ᵐ ω ∂P, |H ω| ≤ A) (hab : ∀ᵐ ω ∂P, |a ω| ≤ C) :
    (∫ ω, H ω * (P[(fun ω => Q ω * S ω) | m] ω -
      P[Q | m] ω * a ω) ∂P) =
      (∫ ω, Q ω * H ω * S ω ∂P) - ∫ ω, Q ω * H ω * a ω ∂P := by
  let : MeasurableSpace Ω := mΩ
  have hHm : AEStronglyMeasurable[mΩ] H P := (hH.mono hm).aestronglyMeasurable
  have hHam : AEStronglyMeasurable[mΩ] (fun ω => H ω * a ω) P :=
    ((hH.mul ha).mono hm).aestronglyMeasurable
  have hHab : ∀ᵐ ω ∂P, |H ω * a ω| ≤ A * C := by
    filter_upwards [hHb, hab] with ω hHω haω
    rw [abs_mul]
    exact mul_le_mul hHω haω (abs_nonneg _) ((abs_nonneg _).trans hHω)
  have hHK := integrable_bounded_mul
    (integrable_condExp (m := m) (f := fun ω => Q ω * S ω)) hHm hHb
  have hHMa := integrable_bounded_mul (integrable_condExp (m := m) (f := Q)) hHam hHab
  have hHQS := integrable_bounded_mul hQS hHm hHb
  have hHaQ := integrable_bounded_mul hQ hHam hHab
  calc
    _ = (∫ ω, H ω * P[(fun ω => Q ω * S ω) | m] ω ∂P) -
        ∫ ω, (H ω * a ω) * P[Q | m] ω ∂P := by
      rw [← integral_sub hHK hHMa]
      congr 1
      funext ω
      ring
    _ = (∫ ω, H ω * (Q ω * S ω) ∂P) -
        ∫ ω, (H ω * a ω) * Q ω ∂P := by
      have he := integral_test_condExp hm hQ (hH.mul ha) hHaQ
      simp only [Pi.mul_apply] at he
      rw [integral_test_condExp hm hQS hH hHQS, he]
    _ = _ := by
      congr 1 <;> apply integral_congr_ae <;>
        exact Eventually.of_forall (fun ω => by ring)

theorem integrable_weighted_process [IsFiniteMeasure P]
    {F : Filtration ℝ≥0 mΩ} {m : ℝ≥0 → Ω → ℝ} {H : Ω → ℝ} {A C : ℝ}
    (hm : IsStronglyProgressive F m) (hH : StronglyMeasurable H)
    (hHb : ∀ᵐ ω ∂P, |H ω| ≤ A)
    (hmb : ∀ r, ∀ᵐ ω ∂P, |m r ω| ≤ C) (s t : ℝ≥0) :
    Integrable (fun p : ℝ × Ω => H p.2 * m p.1.toNNReal p.2)
      ((volume.restrict (Ioc (s : ℝ) (t : ℝ))).prod P) := by
  apply integrable_bounded_mul
    (integrable_nnreal_process_interval_of_progressive_bounded hm C hmb s t)
    (hH.comp_measurable measurable_snd).aestronglyMeasurable
  exact Measure.quasiMeasurePreserving_snd.ae hHb

theorem integral_weighted_primitive_increment [IsFiniteMeasure P]
    {F : Filtration ℝ≥0 mΩ} {m : ℝ≥0 → Ω → ℝ} {H : Ω → ℝ} {A C : ℝ}
    (hm : IsStronglyProgressive F m) (hH : StronglyMeasurable H)
    (hHb : ∀ᵐ ω ∂P, |H ω| ≤ A)
    (hmb : ∀ r, ∀ᵐ ω ∂P, |m r ω| ≤ C)
    {s t : ℝ≥0} (hst : s ≤ t) :
    (∫ ω, H ω * (nnrealTimePrimitive m t ω - nnrealTimePrimitive m s ω) ∂P) =
      ∫ r in (s : ℝ)..(t : ℝ), ∫ ω, H ω * m r.toNNReal ω ∂P := by
  have hinc := nnrealTimePrimitive_increment_ae hst
    (integrable_nnreal_process_interval_of_progressive_bounded hm C hmb 0 s)
    (integrable_nnreal_process_interval_of_progressive_bounded hm C hmb s t)
  have hi := integrable_weighted_process hm hH hHb hmb s t
  calc
    _ = ∫ ω, H ω * (∫ r in (s : ℝ)..(t : ℝ), m r.toNNReal ω) ∂P := by
      apply integral_congr_ae
      filter_upwards [hinc] with ω hω
      rw [show nnrealTimePrimitive m t ω - nnrealTimePrimitive m s ω = _ from hω]
    _ = ∫ ω, (∫ r in (s : ℝ)..(t : ℝ), H ω * m r.toNNReal ω) ∂P := by
      simp only [intervalIntegral.integral_const_mul]
    _ = _ := by
      simp only [intervalIntegral.integral_of_le (show (s : ℝ) ≤ (t : ℝ) from hst)]
      exact (integral_integral_swap (f := fun (r : ℝ) (ω : Ω) =>
        H ω * m r.toNNReal ω) hi).symm

theorem integral_bounded_mul_martingale_increment_eq_zero [IsFiniteMeasure P]
    {G : Filtration ℝ≥0 mΩ} {B : ℝ≥0 → Ω → ℝ}
    (hB : Martingale B G P) {s t : ℝ≥0} (hst : s ≤ t)
    {H : Ω → ℝ} {A : ℝ} (hH : StronglyMeasurable[G s] H)
    (hHb : ∀ᵐ ω ∂P, |H ω| ≤ A) :
    (∫ ω, H ω * (B t ω - B s ω) ∂P) = 0 := by
  have hD : Integrable (B t - B s) P := (hB.integrable t).sub (hB.integrable s)
  exact SimpleIntegral.integral_mul_eq_zero_of_condExp_eq_zero (G.le s) hH hD
    (integrable_bounded_mul hD (hH.mono (G.le s)).aestronglyMeasurable hHb)
    (martingale_increment_condExp_subfiltration hB (fun _ => le_rfl) hst)

theorem integral_latent_mul_innovation_increment [IsFiniteMeasure P]
    {F G : Filtration ℝ≥0 mΩ} {B m : ℝ≥0 → Ω → ℝ}
    (hB : Martingale B G P) (hFG : ∀ r, F r ≤ G r)
    {Q S H : Ω → ℝ} {A C D : ℝ} {s t : ℝ≥0} (hst : s ≤ t)
    (hQ : StronglyMeasurable[G s] Q) (hQb : ∀ᵐ ω ∂P, |Q ω| ≤ D)
    (hS : Integrable S P) (hSb : ∀ᵐ ω ∂P, |S ω| ≤ C)
    (hH : StronglyMeasurable[F s] H) (hHb : ∀ᵐ ω ∂P, |H ω| ≤ A)
    (hm : IsStronglyProgressive F m)
    (hpost : ∀ r, m r =ᵐ[P] P[S | F r]) :
    (∫ ω, Q ω * H ω * (innovation B S m t ω - innovation B S m s ω) ∂P) =
      ∫ r in (s : ℝ)..(t : ℝ), ∫ ω, H ω *
        (P[(fun ω => Q ω * S ω) | F r.toNNReal] ω -
          P[Q | F r.toNNReal] ω * m r.toNNReal ω) ∂P := by
  have hQm : StronglyMeasurable Q := hQ.mono (G.le s)
  have hQint : Integrable Q P := by
    apply Integrable.of_bound hQm.aestronglyMeasurable D
    simpa only [Real.norm_eq_abs] using hQb
  have hQH : StronglyMeasurable[G s] (fun ω => Q ω * H ω) :=
    hQ.mul (hH.mono (hFG s))
  have hQHm : StronglyMeasurable (fun ω => Q ω * H ω) := hQH.mono (G.le s)
  have hQHb : ∀ᵐ ω ∂P, |Q ω * H ω| ≤ D * A := by
    filter_upwards [hQb, hHb] with ω hq hh
    rw [abs_mul]
    exact mul_le_mul hq hh (abs_nonneg _) ((abs_nonneg _).trans hq)
  have hmb := posterior_version_ae_abs_le hpost hSb
  have hQS := integrable_bounded_mul hS hQm.aestronglyMeasurable hQb
  have hQHS := integrable_bounded_mul hS hQHm.aestronglyMeasurable hQHb
  have hnoise := integral_bounded_mul_martingale_increment_eq_zero hB hst hQH hQHb
  have hnoiseInt := integrable_bounded_mul
    ((hB.integrable t).sub (hB.integrable s)) hQHm.aestronglyMeasurable hQHb
  have hprimInt (u : ℝ≥0) : Integrable (nnrealTimePrimitive m u) P :=
    nnrealTimePrimitive_integrable
      (integrable_nnreal_process_interval_of_progressive_bounded hm C hmb 0 u)
  have hprimProd := integrable_bounded_mul ((hprimInt t).sub (hprimInt s))
    hQHm.aestronglyMeasurable hQHb
  have htime := integrable_weighted_process hm hQHm hQHb hmb s t
  have htimeInt : IntervalIntegrable
      (fun r : ℝ => ∫ ω, (Q ω * H ω) * m r.toNNReal ω ∂P) volume s t :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le
      (show (s : ℝ) ≤ (t : ℝ) from hst)).mpr htime.integral_prod_left
  calc
    _ = (∫ ω, (Q ω * H ω) * (B t ω - B s ω) +
          ((t : ℝ) - (s : ℝ)) * ((Q ω * H ω) * S ω) -
          (Q ω * H ω) * (nnrealTimePrimitive m t ω - nnrealTimePrimitive m s ω) ∂P) := by
      apply integral_congr_ae
      exact Eventually.of_forall (fun ω => by unfold innovation; ring)
    _ = ((t : ℝ) - (s : ℝ)) * (∫ ω, Q ω * H ω * S ω ∂P) -
        ∫ r in (s : ℝ)..(t : ℝ), ∫ ω, (Q ω * H ω) * m r.toNNReal ω ∂P := by
      have hh := integral_sub
        (hnoiseInt.add (hQHS.const_mul ((t : ℝ) - (s : ℝ)))) hprimProd
      have ha := integral_add hnoiseInt (hQHS.const_mul ((t : ℝ) - (s : ℝ)))
      simp only [Pi.add_apply, Pi.sub_apply] at hh ha
      rw [hh, ha, integral_const_mul, hnoise, zero_add,
        integral_weighted_primitive_increment hm hQHm hQHb hmb hst]
    _ = ∫ r in (s : ℝ)..(t : ℝ),
        ((∫ ω, Q ω * H ω * S ω ∂P) - ∫ ω, Q ω * H ω * m r.toNNReal ω ∂P) := by
      rw [intervalIntegral.integral_sub intervalIntegrable_const htimeInt,
        intervalIntegral.integral_const, smul_eq_mul]
    _ = _ := by
      apply intervalIntegral.integral_congr
      intro r hr
      have hsr : s ≤ r.toNNReal := by
        have hr' : (s : ℝ) ≤ r := (uIcc_of_le (show (s : ℝ) ≤ (t : ℝ) from hst) ▸ hr).1
        simpa using Real.toNNReal_mono hr'
      exact (integral_test_covariance (F.le r.toNNReal) hQint hQS
        (hH.mono (F.mono hsr)) (hm.stronglyAdapted r.toNNReal) hHb (hmb r.toNNReal)).symm

theorem integral_terminal_posterior_mul_increment [IsFiniteMeasure P]
    {F : Filtration ℝ≥0 mΩ} {W : ℝ≥0 → Ω → ℝ}
    (hW : Martingale W F P) {Q H : Ω → ℝ} {A D : ℝ}
    (hQ : Integrable Q P) (hQb : ∀ᵐ ω ∂P, |Q ω| ≤ D)
    {s t T : ℝ≥0} (hst : s ≤ t) (htT : t ≤ T)
    (hH : StronglyMeasurable[F s] H) (hHb : ∀ᵐ ω ∂P, |H ω| ≤ A) :
    (∫ ω, P[Q | F T] ω * H ω * (W t ω - W s ω) ∂P) =
      ∫ ω, Q ω * H ω * (W t ω - W s ω) ∂P := by
  have hHm : AEStronglyMeasurable H P := (hH.mono (F.le s)).aestronglyMeasurable
  have hQHb : ∀ᵐ ω ∂P, |Q ω * H ω| ≤ D * A := by
    filter_upwards [hQb, hHb] with ω hq hh
    rw [abs_mul]
    exact mul_le_mul hq hh (abs_nonneg _) ((abs_nonneg _).trans hq)
  have hi := integrable_bounded_mul ((hW.integrable t).sub (hW.integrable s))
    (hQ.aestronglyMeasurable.mul hHm) hQHb
  have hm : StronglyMeasurable[F T] (fun ω => H ω * (W t ω - W s ω)) :=
    (hH.mono (F.mono (hst.trans htT))).mul
      (((hW.stronglyAdapted t).mono (F.mono htT)).sub
        ((hW.stronglyAdapted s).mono (F.mono (hst.trans htT))))
  have hip : Integrable ((fun ω => H ω * (W t ω - W s ω)) * Q) P := by
    change Integrable (fun ω => (H ω * (W t ω - W s ω)) * Q ω) P
    simpa only [Pi.mul_apply, Pi.sub_apply, mul_assoc, mul_comm, mul_left_comm] using hi
  simpa only [mul_assoc, mul_comm, mul_left_comm] using
    integral_test_condExp (F.le T) hQ hm hip

theorem integral_posterior_mul_innovation_increment [IsFiniteMeasure P]
    {F G : Filtration ℝ≥0 mΩ} {B m : ℝ≥0 → Ω → ℝ}
    (hB : Martingale B G P) (hFG : ∀ r, F r ≤ G r)
    {Q S H : Ω → ℝ} {A C D : ℝ} {s t T : ℝ≥0}
    (hst : s ≤ t) (htT : t ≤ T)
    (hQ : StronglyMeasurable[G s] Q) (hQb : ∀ᵐ ω ∂P, |Q ω| ≤ D)
    (hS : Integrable S P) (hSb : ∀ᵐ ω ∂P, |S ω| ≤ C)
    (hX : StronglyAdapted F (fun r ω => B r ω + (r : ℝ) * S ω))
    (hH : StronglyMeasurable[F s] H) (hHb : ∀ᵐ ω ∂P, |H ω| ≤ A)
    (hm : IsStronglyProgressive F m)
    (hpost : ∀ r, m r =ᵐ[P] P[S | F r]) :
    (∫ ω, P[Q | F T] ω * H ω *
      (innovation B S m t ω - innovation B S m s ω) ∂P) =
      ∫ r in (s : ℝ)..(t : ℝ), ∫ ω, H ω *
        (P[(fun ω => Q ω * S ω) | F r.toNNReal] ω -
          P[Q | F r.toNNReal] ω * m r.toNNReal ω) ∂P := by
  have hQint : Integrable Q P := by
    apply Integrable.of_bound (hQ.mono (G.le s)).aestronglyMeasurable D
    simpa only [Real.norm_eq_abs] using hQb
  have hW : Martingale (innovation B S m) F P :=
    compensated_observation_martingale_of_bounded_signal hB hFG hS hX hm hpost C hSb
  rw [integral_terminal_posterior_mul_increment hW hQint hQb hst htT hH hHb]
  exact integral_latent_mul_innovation_increment hB hFG hst hQ hQb hS hSb hH hHb hm hpost

end Problem367.FilteringCrossEnergy

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Posterior_FilteringSimpleCrossEnergy
attribute [-instance] _root_.OAI.Problem367.WienerSampler.pathMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal BigOperators

namespace Problem367.FilteringCrossEnergy

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}

theorem integrable_posterior_weighted_increment [IsFiniteMeasure P]
    {F : Filtration ℝ≥0 mΩ} {W : ℝ≥0 → Ω → ℝ}
    (hW : Martingale W F P) {Q H : Ω → ℝ} {A D : ℝ}
    (hQb : ∀ᵐ ω ∂P, |Q ω| ≤ D) {s t T : ℝ≥0}
    (hH : StronglyMeasurable[F s] H) (hHb : ∀ᵐ ω ∂P, |H ω| ≤ A) :
    Integrable (fun ω => P[Q | F T] ω * H ω * (W t ω - W s ω)) P := by
  have hb : ∀ᵐ ω ∂P, |P[Q | F T] ω * H ω| ≤ D * A := by
    filter_upwards [ae_bdd_abs_condExp_of_ae_bdd_abs (m := F T) hQb, hHb]
      with ω hq hh
    rw [abs_mul]
    exact mul_le_mul hq hh (abs_nonneg _) ((abs_nonneg _).trans hq)
  apply integrable_bounded_mul ((hW.integrable t).sub (hW.integrable s))
    (((stronglyMeasurable_condExp.mono (F.le T)).mul
      (hH.mono (F.le s))).aestronglyMeasurable) hb

theorem integral_posterior_mul_integralSum [IsFiniteMeasure P]
    {F G : Filtration ℝ≥0 mΩ} {B m : ℝ≥0 → Ω → ℝ}
    (hB : Martingale B G P) (hFG : ∀ r, F r ≤ G r)
    {Q S : Ω → ℝ} {C D : ℝ}
    (hQ : StronglyMeasurable[G 0] Q) (hQb : ∀ᵐ ω ∂P, |Q ω| ≤ D)
    (hS : Integrable S P) (hSb : ∀ᵐ ω ∂P, |S ω| ≤ C)
    (hX : StronglyAdapted F (fun r ω => B r ω + (r : ℝ) * S ω))
    (hm : IsStronglyProgressive F m) (hpost : ∀ r, m r =ᵐ[P] P[S | F r])
    (τ : ℕ → ℝ≥0) (hτ : Monotone τ) (H : ℕ → Ω → ℝ) (A : ℕ → ℝ)
    (hH : ∀ i, StronglyMeasurable[F (τ i)] (H i))
    (hHb : ∀ i, ∀ᵐ ω ∂P, |H i ω| ≤ A i)
    (n : ℕ) {T : ℝ≥0} (hT : τ n ≤ T) :
    (∫ ω, P[Q | F T] ω * BrownianGrid.integralSum (innovation B S m) τ H n ω ∂P) =
      ∑ i ∈ Finset.range n, ∫ r in (τ i : ℝ)..(τ (i + 1) : ℝ),
        ∫ ω, H i ω * (P[(fun ω => Q ω * S ω) | F r.toNNReal] ω -
          P[Q | F r.toNNReal] ω * m r.toNNReal ω) ∂P := by
  have hW : Martingale (innovation B S m) F P :=
    compensated_observation_martingale_of_bounded_signal hB hFG hS hX hm hpost C hSb
  have hint (i : ℕ) : Integrable (fun ω => P[Q | F T] ω * H i ω *
      (innovation B S m (τ (i + 1)) ω - innovation B S m (τ i) ω)) P :=
    integrable_posterior_weighted_increment hW hQb (hH i) (hHb i)
  calc
    _ = ∫ ω, ∑ i ∈ Finset.range n, P[Q | F T] ω * H i ω *
        (innovation B S m (τ (i + 1)) ω - innovation B S m (τ i) ω) ∂P := by
      congr 1
      funext ω
      simp only [BrownianGrid.integralSum, Finset.mul_sum, mul_assoc]
    _ = ∑ i ∈ Finset.range n, ∫ ω, P[Q | F T] ω * H i ω *
        (innovation B S m (τ (i + 1)) ω - innovation B S m (τ i) ω) ∂P :=
      integral_finsetSum _ (fun i _ => hint i)
    _ = _ := by
      apply Finset.sum_congr rfl
      intro i hi
      exact integral_posterior_mul_innovation_increment hB hFG
        (hτ (Nat.le_succ i)) ((hτ (Finset.mem_range.mp hi)).trans hT)
        (hQ.mono (G.mono (bot_le : (0 : ℝ≥0) ≤ τ i))) hQb hS hSb hX
        (hH i) (hHb i) hm hpost

theorem integral_posterior_mul_uniformSum [IsFiniteMeasure P]
    {F G : Filtration ℝ≥0 mΩ} {B m H : ℝ≥0 → Ω → ℝ}
    (hB : Martingale B G P) (hFG : ∀ r, F r ≤ G r)
    {Q S : Ω → ℝ} {A C D : ℝ}
    (hQ : StronglyMeasurable[G 0] Q) (hQb : ∀ᵐ ω ∂P, |Q ω| ≤ D)
    (hS : Integrable S P) (hSb : ∀ᵐ ω ∂P, |S ω| ≤ C)
    (hX : StronglyAdapted F (fun r ω => B r ω + (r : ℝ) * S ω))
    (hm : IsStronglyProgressive F m) (hpost : ∀ r, m r =ᵐ[P] P[S | F r])
    (hH : StronglyAdapted F H) (hHb : ∀ r, ∀ᵐ ω ∂P, |H r ω| ≤ A)
    (T : ℝ≥0) {n : ℕ} (hn : 0 < n) :
    (∫ ω, P[Q | F T] ω * BrownianGrid.uniformSum (innovation B S m) H T n ω ∂P) =
      ∑ i ∈ Finset.range n,
        ∫ r in (BrownianGrid.uniformGrid T n i : ℝ)..(BrownianGrid.uniformGrid T n (i + 1) : ℝ),
          ∫ ω, H (BrownianGrid.uniformGrid T n i) ω *
            (P[(fun ω => Q ω * S ω) | F r.toNNReal] ω -
              P[Q | F r.toNNReal] ω * m r.toNNReal ω) ∂P := by
  exact integral_posterior_mul_integralSum hB hFG hQ hQb hS hSb hX hm hpost
    (BrownianGrid.uniformGrid T n) (BrownianGrid.uniformGrid_mono T n)
    (fun i => H (BrownianGrid.uniformGrid T n i)) (fun _ => A)
    (fun i => hH _) (fun i => hHb _) n (by rw [BrownianGrid.uniformGrid_end T hn])

end Problem367.FilteringCrossEnergy

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Posterior_FilteringCrossLimit
attribute [-instance] _root_.OAI.Problem367.WienerSampler.pathMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal Topology BigOperators

namespace Problem367.FilteringCrossEnergy

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}

theorem tendsto_posterior_uniformSum_cross_energy [IsFiniteMeasure P]
    {F G : Filtration ℝ≥0 mΩ} {B m K : ℝ≥0 → Ω → ℝ}
    (hB : Martingale B G P) (hFG : ∀ r, F r ≤ G r)
    {Q S : Ω → ℝ} {A C D : ℝ}
    (hQ : StronglyMeasurable[G 0] Q) (hQb : ∀ᵐ ω ∂P, |Q ω| ≤ D)
    (hS : Integrable S P) (hSb : ∀ᵐ ω ∂P, |S ω| ≤ C)
    (hX : StronglyAdapted F (fun r ω => B r ω + (r : ℝ) * S ω))
    (hm : IsStronglyProgressive F m) (hpost : ∀ r, m r =ᵐ[P] P[S | F r])
    (hK : StronglyAdapted F K)
    (hKc : ∀ᵐ ω ∂P, Continuous (fun r => K r ω))
    (hA : 0 ≤ A) (hKb : ∀ᵐ ω ∂P, ∀ r, |K r ω| ≤ A)
    (hKversion : ∀ r, K r =ᵐ[P] fun ω =>
      P[(fun ω => Q ω * S ω) | F r] ω - P[Q | F r] ω * m r ω)
    (T : ℝ≥0) :
    Tendsto (fun n : ℕ => ∫ ω, P[Q | F T] ω *
      BrownianGrid.uniformSum (innovation B S m) K T n ω ∂P) atTop
      (𝓝 (∫ r in (0 : ℝ)..(T : ℝ), ∫ ω, K r.toNNReal ω ^ 2 ∂P)) := by
  have hlim := CrossEnergyRiemann.tendsto_cross_energy
    (fun r => (hK r).mono (F.le r) |>.aestronglyMeasurable) hKc hA hKb T
  apply hlim.congr'
  filter_upwards [eventually_ge_atTop 1] with n hn
  have he := integral_posterior_mul_uniformSum hB hFG hQ hQb hS hSb hX hm hpost hK
    (fun r => hKb.mono (fun ω hω => hω r)) T (show 0 < n from hn)
  rw [he]
  apply Finset.sum_congr rfl
  intro i hi
  apply intervalIntegral.integral_congr
  intro r hr
  apply integral_congr_ae
  filter_upwards [hKversion r.toNNReal] with ω hω
  rw [hω]

end Problem367.FilteringCrossEnergy

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Posterior_PlantedArrayCrossEnergy
attribute [-instance] _root_.OAI.Problem367.WienerSampler.pathMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal Topology

namespace Problem367

theorem stronglyMeasurable_latent_signalArrayFiltration
    {ι S Ω : Type*} [MeasurableSpace S] [MeasurableSpace Ω]
    (B : ι → ℝ≥0 → Ω → ℝ) (hmB : ∀ i t, Measurable (B i t))
    {Q : S → ℝ} (hQ : Measurable Q) (t : ℝ≥0) :
    StronglyMeasurable[signalArrayFiltration B hmB t]
      (fun q : S × (ι → Ω) => Q q.1) := by
  have hm : StronglyMeasurable[MeasurableSpace.comap
      (Prod.fst : S × (ι → Ω) → S) inferInstance] (fun q => Q q.1) :=
    (hQ.comp (comap_measurable Prod.fst)).stronglyMeasurable
  exact hm.mono le_sup_left

end Problem367

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Stochastic_FiniteIsingBrownianPosterior
attribute [-instance] _root_.OAI.Problem367.IsingConditionalCopyBounds.graphLaw_isProbabilityMeasure _root_.OAI.Problem367.IsingObservationFactor.copies_probability _root_.OAI.Problem367.IsingObservationFactor.kernel_markov _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_observationLaw_probability _root_.OAI.Problem367.IsingObservationInnovation.observationLaw_probability _root_.OAI.Problem367.TreeKoopman.labelProbability _root_.OAI.Problem367.WienerSampler.pathMeasurableSpace _root_.OAI.Problem367.freeIsingMeasure_probability _root_.OAI.Problem367.reducedTailFinite _root_.OAI.Problem367.reducedTailFintype _root_.OAI.Problem367.treeBallFinite _root_.OAI.Problem367.treeBallFintype _root_.OAI.Problem367.treeShellFinite _root_.OAI.Problem367.treeShellFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal

namespace Problem367

local instance finiteIsingBrownianPosteriorNonemptySpin : Nonempty IsingSpin := ⟨.neg⟩

theorem finiteIsingBrownian_joint_law
    {d : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure (TreeVertex d → IsingSpin)) [IsProbabilityMeasure μ]
    (ν : TreeVertex d → Measure Ω)
    {B : TreeVertex d → ℝ≥0 → Ω → ℝ}
    (hB : ∀ i, IsPreBrownianReal (B i) (ν i))
    (hmB : ∀ i t, Measurable (B i t))
    (D : Finset (TreeVertex d)) (t : ℝ≥0) :
    (μ.prod (Measure.infinitePi ν)).map
      (fun p : (TreeVertex d → IsingSpin) × (TreeVertex d → Ω) =>
        (D.restrict p.1, finiteIsingBrownianObservation B D t p)) =
    (μ.map D.restrict) ⊗ₘ finiteGaussianObservationKernel t
      (fun eta (v : D) => spinSign (eta v)) := by
  have (i : TreeVertex d) : IsProbabilityMeasure (ν i) :=
    (hB i).isGaussianProcess.isProbabilityMeasure
  let π := μ.map D.restrict
  let : IsProbabilityMeasure π := by first | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)
  let spin : (D → IsingSpin) → D → ℝ := fun eta v => spinSign (eta v)
  have hr : MeasurePreserving D.restrict μ π := ⟨D.measurable_restrict, rfl⟩
  have hp := hr.prod (finiteBrownianNoise_restrict_measurePreserving ν hB hmB D t)
  let Y : (D → IsingSpin) × (D → ℝ) → (D → IsingSpin) × (D → ℝ) :=
    fun p => (p.1, fun v => (t : ℝ) * spin p.1 v + p.2 v)
  have hY : Measurable Y := by
    apply measurable_fst.prodMk
    apply Measurable.of_eval
    intro v
    exact (measurable_const.mul
      ((measurable_of_finite (fun eta => spin eta v)).comp measurable_fst)).add
      ((measurable_pi_apply v).comp measurable_snd)
  have h := finiteGaussianPlanted_joint_law π t spin
  change Measure.map Y _ = _ at h
  rw [← hp.map_eq, Measure.map_map hY hp.measurable] at h
  unfold finiteIsingBrownianObservation
  simpa only [Y, spin, Function.comp_def, Prod.map_fst, Prod.map_snd,
    Finset.restrict, Real.toNNReal_coe] using h

theorem measurable_finiteIsingBrownianObservation
    {d : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    {B : TreeVertex d → ℝ≥0 → Ω → ℝ}
    (hmB : ∀ i t, Measurable (B i t))
    (D : Finset (TreeVertex d)) (t : ℝ) :
    Measurable (finiteIsingBrownianObservation B D t) := by
  apply Measurable.of_eval
  intro v
  exact (measurable_const.mul
    ((measurable_of_finite spinSign).comp
      ((measurable_pi_apply (v : TreeVertex d)).comp measurable_fst))).add
    ((hmB v t.toNNReal).comp
      ((measurable_pi_apply (v : TreeVertex d)).comp measurable_snd))

theorem HasFreeIsingLaw.condExp_finiteIsingBrownian_observable
    {d : ℕ} {beta : ℝ} {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure (TreeVertex d → IsingSpin)}
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ)
    (ν : TreeVertex d → Measure Ω)
    {B : TreeVertex d → ℝ≥0 → Ω → ℝ}
    (hB : ∀ i, IsPreBrownianReal (B i) (ν i))
    (hmB : ∀ i t, Measurable (B i t))
    (D : Finset (TreeVertex d)) (hD : ConnectedFinset D)
    (t : ℝ≥0) (q : (D → IsingSpin) → ℝ) :
    let ρ := μ.prod (Measure.infinitePi ν)
    ρ[fun p => q (D.restrict p.1) |
      MeasurableSpace.comap (finiteIsingBrownianObservation B D t) inferInstance] =ᵐ[ρ]
      fun p => FinitePosterior.fieldMean (finiteIsingEnergy beta D)
        (fun eta (v : D) => spinSign (eta v)) q
        (finiteIsingBrownianObservation B D t p) := by
  let : IsProbabilityMeasure μ := hμ.isProbabilityMeasure
  have (i : TreeVertex d) : IsProbabilityMeasure (ν i) :=
    (hB i).isGaussianProcess.isProbabilityMeasure
  let : IsProbabilityMeasure (μ.map D.restrict) := by first | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)
  dsimp only
  exact FiniteBayes.condExp_state_eq_of_posterior_integral
    (μ.prod (Measure.infinitePi ν)) (μ.map D.restrict)
    (finiteGaussianObservationKernel t (fun eta (v : D) => spinSign (eta v)))
    (fun p => D.restrict p.1) (finiteIsingBrownianObservation B D t)
    (D.measurable_restrict.comp measurable_fst)
    (measurable_finiteIsingBrownianObservation hmB D t)
    (finiteIsingBrownian_joint_law μ ν hB hmB D t) q
    (FinitePosterior.fieldMean (finiteIsingEnergy beta D)
      (fun eta (v : D) => spinSign (eta v)) q)
    (hμ.gaussian_restrict_posterior_mean D hD t q)

end Problem367

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Stochastic_SelectedBrownianSufficiency
attribute [-instance] _root_.OAI.Problem367.WienerSampler.pathMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace Problem367.TerminalSufficiency

theorem condExp_planted_selected_past_eq_terminal
    {ι κ S Ω : Type*} [MeasurableSpace S] [MeasurableSpace Ω]
    (ν : Measure S) (μ : κ → Measure Ω) [IsProbabilityMeasure ν]
    {B : κ → ℝ≥0 → Ω → ℝ} (hB : ∀ i, IsPreBrownianReal (B i) (μ i))
    (hmB : ∀ i t, Measurable (B i t))
    (v : ι → κ) (hv : Function.Injective v)
    (signal : S → κ → ℝ) (f : S → ℝ)
    (hSignal : Measurable signal) (hf : Measurable f) (hfint : Integrable f ν)
    (T : ℝ≥0) :
    (ν.prod (Measure.infinitePi μ))[(fun q : S × (κ → Ω) => f q.1) |
      MeasurableSpace.comap
        (fun q : S × (κ → Ω) => fun i (s : Set.Iic T) =>
          (s.1 : ℝ) * signal q.1 (v i) + B (v i) s.1 (q.2 (v i))) inferInstance]
        =ᵐ[ν.prod (Measure.infinitePi μ)]
    (ν.prod (Measure.infinitePi μ))[(fun q : S × (κ → Ω) => f q.1) |
      MeasurableSpace.comap
        (fun q : S × (κ → Ω) => fun i =>
          (T : ℝ) * signal q.1 (v i) + B (v i) T (q.2 (v i))) inferInstance] := by
  have (i : κ) : IsProbabilityMeasure (μ i) :=
    (hB i).isGaussianProcess.isProbabilityMeasure
  let R : S × (κ → Ω) → S × (ι → Ω) :=
    Prod.map id (fun ω i => ω (v i))
  have hselect : MeasurePreserving (fun ω : κ → Ω => fun i => ω (v i))
      (Measure.infinitePi μ) (Measure.infinitePi (fun i => μ (v i))) :=
    ⟨Measurable.of_eval (fun i => measurable_pi_apply (v i)),
      Measure.map_infinitePi_infinitePi_of_inj hv⟩
  have hR : MeasurePreserving R (ν.prod (Measure.infinitePi μ))
      (ν.prod (Measure.infinitePi (fun i => μ (v i)))) :=
    (MeasurePreserving.id ν).prod hselect
  let ambient : MeasurableSpace (S × (ι → Ω)) := inferInstance
  let P : MeasurableSpace (S × (ι → Ω)) := MeasurableSpace.comap
    (fun q : S × (ι → Ω) => fun i (s : Set.Iic T) =>
      (s.1 : ℝ) * signal q.1 (v i) + B (v i) s.1 (q.2 i)) inferInstance
  let Q : MeasurableSpace (S × (ι → Ω)) := MeasurableSpace.comap
    (fun q : S × (ι → Ω) => fun i =>
      (T : ℝ) * signal q.1 (v i) + B (v i) T (q.2 i)) inferInstance
  let : MeasurableSpace (S × (ι → Ω)) := ambient
  have hP : P ≤ (inferInstance : MeasurableSpace (S × (ι → Ω))) := by
    apply Measurable.comap_le
    apply Measurable.of_eval
    intro i
    apply Measurable.of_eval
    intro s
    exact (measurable_const.mul
      (((measurable_pi_apply (v i)).comp hSignal).comp measurable_fst)).add
      ((hmB (v i) s.1).comp ((measurable_pi_apply i).comp measurable_snd))
  have hQ : Q ≤ (inferInstance : MeasurableSpace (S × (ι → Ω))) := by
    apply Measurable.comap_le
    apply Measurable.of_eval
    intro i
    exact (measurable_const.mul
      (((measurable_pi_apply (v i)).comp hSignal).comp measurable_fst)).add
      ((hmB (v i) T).comp ((measurable_pi_apply i).comp measurable_snd))
  have hf' : Integrable (fun q : S × (ι → Ω) => f q.1)
      (ν.prod (Measure.infinitePi (fun i => μ (v i)))) := hfint.comp_fst _
  have hPast := Problem367.condExp_comp_measurePreserving
    (ν.prod (Measure.infinitePi μ))
    (ν.prod (Measure.infinitePi (fun i => μ (v i)))) R hR P hP hf'
  have hTerm := Problem367.condExp_comp_measurePreserving
    (ν.prod (Measure.infinitePi μ))
    (ν.prod (Measure.infinitePi (fun i => μ (v i)))) R hR Q hQ hf'
  have hCore := condExp_planted_infinite_past_eq_terminal ν (fun i => μ (v i))
    (fun i => hB (v i)) (fun i t => hmB (v i) t)
    (fun x i => signal x (v i)) f
    (Measurable.of_eval (fun i => (measurable_pi_apply (v i)).comp hSignal))
    hf hfint T
  have hPull := hR.quasiMeasurePreserving.ae_eq_comp hCore
  simp only [P, Q, MeasurableSpace.comap_comp] at hPast hTerm
  filter_upwards [hPast, hTerm, hPull] with q hp ht hc
  exact hp.trans (hc.trans ht.symm)

end Problem367.TerminalSufficiency

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Stochastic_FiniteIsingBrownianHistory
attribute [-instance] _root_.OAI.Problem367.IsingConditionalCopyBounds.graphLaw_isProbabilityMeasure _root_.OAI.Problem367.IsingObservationFactor.copies_probability _root_.OAI.Problem367.IsingObservationFactor.kernel_markov _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_observationLaw_probability _root_.OAI.Problem367.IsingObservationInnovation.observationLaw_probability _root_.OAI.Problem367.TreeKoopman.labelProbability _root_.OAI.Problem367.WienerSampler.pathMeasurableSpace _root_.OAI.Problem367.freeIsingMeasure_probability _root_.OAI.Problem367.reducedTailFinite _root_.OAI.Problem367.reducedTailFintype _root_.OAI.Problem367.treeBallFinite _root_.OAI.Problem367.treeBallFintype _root_.OAI.Problem367.treeShellFinite _root_.OAI.Problem367.treeShellFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal

namespace Problem367

local instance finiteIsingBrownianHistoryNonemptySpin_r2c6f49_1 : Nonempty IsingSpin := ⟨.neg⟩
theorem HasFreeIsingLaw.condExp_finiteIsingBrownian_past
    {d : ℕ} {beta : ℝ} {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure (TreeVertex d → IsingSpin)}
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ)
    (ν : TreeVertex d → Measure Ω)
    {B : TreeVertex d → ℝ≥0 → Ω → ℝ}
    (hB : ∀ i, IsPreBrownianReal (B i) (ν i))
    (hmB : ∀ i t, Measurable (B i t))
    (D : Finset (TreeVertex d)) (hD : ConnectedFinset D)
    (q : (D → IsingSpin) → ℝ) (t : ℝ≥0) :
    let ρ := μ.prod (Measure.infinitePi ν)
    ρ[fun p => q (D.restrict p.1) |
      MeasurableSpace.comap
        (fun p : (TreeVertex d → IsingSpin) × (TreeVertex d → Ω) =>
          fun i : D => fun s : Iic t =>
            (s.1 : ℝ) * spinSign (p.1 i) + B i s.1 (p.2 i)) inferInstance] =ᵐ[ρ]
      fun p => FinitePosterior.fieldMean (finiteIsingEnergy beta D)
        (fun eta (v : D) => spinSign (eta v)) q
        (finiteIsingBrownianObservation B D t p) := by
  let : IsProbabilityMeasure μ := hμ.isProbabilityMeasure
  have hq : Measurable (fun sigma : TreeVertex d → IsingSpin => q (D.restrict sigma)) :=
    (measurable_of_finite q).comp D.measurable_restrict
  have hqi : Integrable (fun sigma : TreeVertex d → IsingSpin => q (D.restrict sigma)) μ := by
    classical
    apply (integrable_const (∑ eta, |q eta|)).mono' hq.aestronglyMeasurable
    filter_upwards with sigma
    exact Finset.single_le_sum (fun eta _ => abs_nonneg (q eta))
      (Finset.mem_univ (D.restrict sigma))
  have hs : Measurable (fun sigma : TreeVertex d → IsingSpin =>
      fun i : TreeVertex d => spinSign (sigma i)) := by
    apply Measurable.of_eval
    intro i
    exact (measurable_of_finite spinSign).comp (measurable_pi_apply (i : TreeVertex d))
  have h := TerminalSufficiency.condExp_planted_selected_past_eq_terminal
    μ ν hB hmB (fun i : D => (i : TreeVertex d)) Subtype.val_injective
    (fun sigma i => spinSign (sigma i))
    (fun sigma => q (D.restrict sigma)) hs hq hqi t
  dsimp only
  apply h.trans
  have hc := hμ.condExp_finiteIsingBrownian_observable ν hB hmB D hD t q
  unfold finiteIsingBrownianObservation at hc ⊢
  simpa only [Real.toNNReal_coe] using hc

theorem HasFreeIsingLaw.finiteIsingBrownianCovariance_eq_past
    {d : ℕ} {beta : ℝ} {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure (TreeVertex d → IsingSpin)}
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ)
    (ν : TreeVertex d → Measure Ω)
    {B : TreeVertex d → ℝ≥0 → Ω → ℝ}
    (hB : ∀ i, IsPreBrownianReal (B i) (ν i))
    (hmB : ∀ i t, Measurable (B i t))
    (D : Finset (TreeVertex d)) (hD : ConnectedFinset D)
    (v u : D) (t : ℝ≥0) :
    let ρ := μ.prod (Measure.infinitePi ν)
    finiteIsingBrownianCovariance beta D v u B t =ᵐ[ρ]
      posteriorCovariance ρ
        (MeasurableSpace.comap
          (fun p : (TreeVertex d → IsingSpin) × (TreeVertex d → Ω) =>
            fun i : D => fun s : Iic t =>
              (s.1 : ℝ) * spinSign (p.1 i) + B i s.1 (p.2 i)) inferInstance)
        (fun p => spinSign (p.1 (v : TreeVertex d)))
        (fun p => spinSign (p.1 (u : TreeVertex d))) := by
  filter_upwards [hμ.condExp_finiteIsingBrownian_past ν hB hmB D hD
      (fun eta => spinSign (eta v) * spinSign (eta u)) t,
    hμ.condExp_finiteIsingBrownian_past ν hB hmB D hD
      (fun eta => spinSign (eta v)) t,
    hμ.condExp_finiteIsingBrownian_past ν hB hmB D hD
      (fun eta => spinSign (eta u)) t] with p hp hv hu
  exact congrArg₂ (fun a b : ℝ => a - b) hp.symm
    (congrArg₂ (· * ·) hv.symm hu.symm)

end Problem367

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Energy_FiniteIsingCrossEnergy
attribute [-instance] _root_.OAI.Problem367.IsingConditionalCopyBounds.graphLaw_isProbabilityMeasure _root_.OAI.Problem367.IsingObservationFactor.copies_probability _root_.OAI.Problem367.IsingObservationFactor.kernel_markov _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_observationLaw_probability _root_.OAI.Problem367.IsingObservationInnovation.observationLaw_probability _root_.OAI.Problem367.TreeKoopman.labelProbability _root_.OAI.Problem367.WienerSampler.pathMeasurableSpace _root_.OAI.Problem367.freeIsingMeasure_probability
attribute [-simp] _root_.OAI.Problem367.ConnectedHull.pathAssignment_path _root_.OAI.Problem367.ConnectedHull.path_last _root_.OAI.Problem367.ConnectedHull.path_zero _root_.OAI.Problem367.CutContinuationChannels.averageChannel_globalCone _root_.OAI.Problem367.CutContinuationChannels.continuationChannel_globalCone _root_.OAI.Problem367.FactorObservable.centeredSpinLp_coe _root_.OAI.Problem367.FiniteIsingSplit.splitEquiv_fst _root_.OAI.Problem367.FiniteIsingSplit.splitEquiv_snd _root_.OAI.Problem367.FinitePathGibbs.tailPartition_zero _root_.OAI.Problem367.GaussianTreeResponseNaturality.fieldEquiv_apply_image _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_apply _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_uniformObservation _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_zero _root_.OAI.Problem367.IsingObservationInnovation.uniformObservation_relabel _root_.OAI.Problem367.IsingOrientedPath.attenuation_outward _root_.OAI.Problem367.IsingOrientedPath.endpoint_extensionAt _root_.OAI.Problem367.LocalSupportGeometry.prefixVertex_length _root_.OAI.Problem367.PathSideBranches.parent_sideVertex _root_.OAI.Problem367.PathSideBranches.restrictNoisyRegion_array _root_.OAI.Problem367.PathSideBranches.sideVertex_length _root_.OAI.Problem367.PathSideBranches.sideVertex_val _root_.OAI.Problem367.PosteriorChain.transition_spinMean _root_.OAI.Problem367.PosteriorChain.transition_sum _root_.OAI.Problem367.RootedBroadcast.flipBranchToComplement_val _root_.OAI.Problem367.RootedBroadcast.pos_spinMul _root_.OAI.Problem367.RootedBroadcast.prefixFlip_branchRoot _root_.OAI.Problem367.RootedBroadcast.prefixFlip_root _root_.OAI.Problem367.RootedBroadcast.prefixTreeAut_symm_branchRoot _root_.OAI.Problem367.RootedBroadcast.prefixTreeAut_symm_root _root_.OAI.Problem367.RootedBroadcast.spinMul_pos _root_.OAI.Problem367.RootedBroadcast.spinMul_self _root_.OAI.Problem367.TreeConeCoding.length_vertex _root_.OAI.Problem367.TreeConeCoding.vertex_nil _root_.OAI.Problem367.TreeConeCoding.vertex_val _root_.OAI.Problem367.TreeGibbsAut.spinEquiv_apply_image _root_.OAI.Problem367.TreeKoopman.centeredAverage_apply_coe _root_.OAI.Problem367.TreeKoopman.centeredAverage_pow_apply_coe _root_.OAI.Problem367.TreeKoopman.centeredGenerator_apply_coe _root_.OAI.Problem367.TreeKoopman.centeredGenerator_sq _root_.OAI.Problem367.TreeKoopman.generatorOperator_sq _root_.OAI.Problem367.TreeKoopman.reverseVertex_twice _root_.OAI.Problem367.TreeKoopman.wordRelabel_cons _root_.OAI.Problem367.TreeKoopman.wordRelabel_nil _root_.OAI.Problem367.TreeLawKoopman.centeredAverage_apply_coe _root_.OAI.Problem367.TreeLawKoopman.generatorOperator_sq _root_.OAI.Problem367.TreePathGibbs.vertexEquiv_val _root_.OAI.Problem367.branchColorAut_length _root_.OAI.Problem367.branchColorAut_singleton _root_.OAI.Problem367.branchColorAut_val _root_.OAI.Problem367.branchColorMap_symm_apply _root_.OAI.Problem367.colorPermAut_length _root_.OAI.Problem367.colorPermAut_nil _root_.OAI.Problem367.colorPermAut_val _root_.OAI.Problem367.colorPermMap_symm_apply _root_.OAI.Problem367.colorPermMap_val _root_.OAI.Problem367.connectedSpinEncode_apply_root _root_.OAI.Problem367.connectedSpinEquiv_apply _root_.OAI.Problem367.dropVertex_length _root_.OAI.Problem367.dropVertex_val _root_.OAI.Problem367.innovationPath_apply _root_.OAI.Problem367.mem_rootComplementFinset _root_.OAI.Problem367.mem_rootComponentFinset _root_.OAI.Problem367.mem_rootComponentIndices _root_.OAI.Problem367.parentVertex_length _root_.OAI.Problem367.parentVertex_val _root_.OAI.Problem367.prefixColorAut_length _root_.OAI.Problem367.prefixColorAut_val _root_.OAI.Problem367.prefixColorMap_symm_apply _root_.OAI.Problem367.prefixFlip_twice _root_.OAI.Problem367.spinAgreementCode_eq_neg_iff _root_.OAI.Problem367.spinAgreementCode_eq_pos_iff _root_.OAI.Problem367.spinSign_flip _root_.OAI.Problem367.tsum_treeShell_radial _root_.OAI.Problem367.vertexSampler_relabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal Topology

namespace Problem367.FiniteIsingFiltering

variable {d : ℕ} {Ω : Type*} [MeasurableSpace Ω]

theorem mean_eq_condExp_history {beta : ℝ}
    {μ : Measure (TreeVertex d → IsingSpin)}
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ)
    (ν : TreeVertex d → Measure Ω)
    {B : TreeVertex d → ℝ≥0 → Ω → ℝ}
    (hB : ∀ i, IsPreBrownianReal (B i) (ν i))
    (hmB : ∀ i t, Measurable (B i t))
    (D : Finset (TreeVertex d)) (hD : ConnectedFinset D) (v : D) (t : ℝ≥0) :
    mean beta D v B t =ᵐ[μ.prod (Measure.infinitePi ν)]
      (μ.prod (Measure.infinitePi ν))[(fun p : State d Ω => spinSign (p.1 v)) |
        observationFiltration B hmB D t] := by
  rw [observationFiltration_eq_comap]
  exact (hμ.condExp_finiteIsingBrownian_past ν hB hmB D hD
    (fun eta => spinSign (eta v)) t).symm

theorem covariance_eq_condExp_history {beta : ℝ}
    {μ : Measure (TreeVertex d → IsingSpin)}
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ)
    (ν : TreeVertex d → Measure Ω)
    {B : TreeVertex d → ℝ≥0 → Ω → ℝ}
    (hB : ∀ i, IsPreBrownianReal (B i) (ν i))
    (hmB : ∀ i t, Measurable (B i t))
    (D : Finset (TreeVertex d)) (hD : ConnectedFinset D) (v u : D) (t : ℝ≥0) :
    let P := μ.prod (Measure.infinitePi ν)
    let F := observationFiltration B hmB D
    covariance beta D v u B t =ᵐ[P] fun p =>
      P[(fun p : State d Ω => spinSign (p.1 v) * spinSign (p.1 u)) | F t] p -
      P[(fun p : State d Ω => spinSign (p.1 v)) | F t] p * mean beta D u B t p := by
  have hc := hμ.finiteIsingBrownianCovariance_eq_past ν hB hmB D hD v u t
  rw [← observationFiltration_eq_comap B hmB D t] at hc
  filter_upwards [hc, mean_eq_condExp_history hμ ν hB hmB D hD u t] with p hp hu
  dsimp only [posteriorCovariance] at hp
  exact hp.trans (by rw [hu])

theorem tendsto_cross_uniformSum_oai {beta : ℝ}
    {μ : Measure (TreeVertex d → IsingSpin)}
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ)
    (ν : TreeVertex d → Measure Ω)
    {B : TreeVertex d → ℝ≥0 → Ω → ℝ}
    (hB : ∀ i, IsPreBrownianReal (B i) (ν i))
    (hmB : ∀ i t, Measurable (B i t))
    (hcB : ∀ i omega, Continuous (fun t => B i t omega))
    (D : Finset (TreeVertex d)) (hD : ConnectedFinset D) (v u : D) (T : ℝ≥0) :
    Tendsto (fun n : ℕ => ∫ p, mean beta D v B T p *
      BrownianGrid.uniformSum
        (fun t p => plantedArrayObservation B signal u t p -
          nnrealTimePrimitive (mean beta D u B) t p)
        (covariance beta D v u B) T n p ∂μ.prod (Measure.infinitePi ν))
      atTop (𝓝 (∫ r in (0 : ℝ)..(T : ℝ),
        ∫ p, covariance beta D v u B r.toNNReal p ^ 2 ∂μ.prod (Measure.infinitePi ν))) := by
  let : IsProbabilityMeasure μ := hμ.isProbabilityMeasure
  have (index : TreeVertex d) : IsProbabilityMeasure (ν index) :=
    (hB index).isGaussianProcess.isProbabilityMeasure
  have hs (i : TreeVertex d) : Measurable (fun sigma : TreeVertex d → IsingSpin =>
      spinSign (sigma i)) := (measurable_pi_apply i).comp measurable_signal
  have hbound (i : TreeVertex d) : ∀ p : State d Ω, |spinSign (p.1 i)| ≤ (1 : ℝ) := by
    intro p
    cases p.1 i <;> norm_num [spinSign]
  have hint : Integrable (fun p : State d Ω => spinSign (p.1 u))
      (μ.prod (Measure.infinitePi ν)) :=
    Integrable.of_bound ((hs u).comp measurable_fst).aestronglyMeasurable 1
      (Eventually.of_forall (hbound u))
  have hobs : StronglyAdapted (observationFiltration B hmB D)
      (fun t p => B u t (p.2 u) + (t : ℝ) * spinSign (p.1 u)) :=
    arrayNaturalFiltration_stronglyAdapted
      (fun i : D => plantedArrayObservation B signal i)
      (fun i t => plantedArrayObservation_measurable hmB measurable_signal i t) u
  have hl := FilteringCrossEnergy.tendsto_posterior_uniformSum_cross_energy
    (preBrownian_martingale_signalArrayFiltration μ ν hB hmB (u : TreeVertex d))
    (observationFiltration_le_signal B hmB D)
    (stronglyMeasurable_latent_signalArrayFiltration B hmB (hs v) 0)
    (Eventually.of_forall (hbound v)) hint (Eventually.of_forall (hbound u)) hobs
    (progressive_mean beta D u B hmB hcB)
    (mean_eq_condExp_history hμ ν hB hmB D hD u)
    (stronglyAdapted_covariance beta D v u B hmB)
    (Eventually.of_forall (continuous_covariance beta D v u B hcB))
    (show (0 : ℝ) ≤ 2 by norm_num)
    (Eventually.of_forall (fun p t => abs_covariance_le_two beta D v u B t p))
    (covariance_eq_condExp_history hμ ν hB hmB D hD v u) T
  apply hl.congr
  intro n
  apply integral_congr_ae
  filter_upwards [mean_eq_condExp_history hμ ν hB hmB D hD v T] with p hp
  exact congrArg (fun x : ℝ => x * BrownianGrid.uniformSum
    (fun t p => plantedArrayObservation B signal u t p -
      nnrealTimePrimitive (mean beta D u B) t p)
    (covariance beta D v u B) T n p) hp.symm

end Problem367.FiniteIsingFiltering

end

end OAI
end

theorem solution.{u_1} : type_of% @OAI.Problem367.FiniteIsingFiltering.tendsto_cross_uniformSum_oai.{u_1} := @OAI.Problem367.FiniteIsingFiltering.tendsto_cross_uniformSum_oai.{u_1}
