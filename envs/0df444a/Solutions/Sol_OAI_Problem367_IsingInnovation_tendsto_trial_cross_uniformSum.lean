-- Prove2me | solution 1 for OAI.Problem367.IsingInnovation.tendsto_trial_cross_uniformSum
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T01:44:20.338026+00:00
-- url     : https://prove2.me/submissions/184037af-e183-47af-9425-3fa1420ba63c

import Mathlib
import Definitions.Def_FreeIsing
import Definitions.Def_Q243FI005

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
-- module Solutions.Q243_FreeIsing.FreeIsing_Energy_MixedCrossEnergyRiemann
attribute [-instance] _root_.OAI.Problem367.WienerSampler.pathMeasurableSpace
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

theorem error_le_of_integrable {f : ℝ → ℝ → ℝ}
    (hsec : ∀ s a b, IntervalIntegrable (f s) volume a b)
    (hdiag : ∀ a b, IntervalIntegrable (fun r => f r r) volume a b)
    {T ε : ℝ} (hT : 0 ≤ T) {n : ℕ} (hn : 0 < n)
    (hmod : ∀ i < n, ∀ r ∈ Icc (point T n i) (point T n (i + 1)),
      |f (point T n i) r - f r r| ≤ ε) :
    |sum f T n - ∫ r in (0 : ℝ)..T, f r r| ≤ ε * T := by
  have hpart := intervalIntegral.sum_integral_adjacent_intervals
    (μ := volume) (a := point T n) (n := n) (fun i _ => hdiag _ _)
  rw [point_zero, point_end T hn] at hpart
  have heq : sum f T n - (∫ r in (0 : ℝ)..T, f r r) =
      ∑ i ∈ Finset.range n, ∫ r in point T n i..point T n (i + 1),
        f (point T n i) r - f r r := by
    rw [sum, ← hpart, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    exact (intervalIntegral.integral_sub (hsec _ _ _)
      (hdiag _ _)).symm
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

theorem tendsto_sum_of_first_uniform {f : ℝ → ℝ → ℝ}
    (hsec : ∀ s a b, IntervalIntegrable (f s) volume a b)
    (hdiag : ∀ a b, IntervalIntegrable (fun r => f r r) volume a b)
    {T : ℝ} (hT : 0 ≤ T)
    (huniform : ∀ ε > (0 : ℝ), ∃ δ > (0 : ℝ),
      ∀ s ∈ Icc 0 T, ∀ t ∈ Icc 0 T, dist s t < δ → |f s t - f t t| ≤ ε) :
    Tendsto (sum f T) atTop (𝓝 (∫ r in (0 : ℝ)..T, f r r)) := by
  apply Metric.tendsto_atTop.mpr
  intro ε hε
  let η := ε / (T + 1)
  have hη : 0 < η := div_pos hε (by linarith)
  obtain ⟨δ, hδ, hmod⟩ := huniform η hη
  have hw : Tendsto (fun n : ℕ => T / (n : ℝ)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
  obtain ⟨N, hN⟩ := ((hw.eventually (gt_mem_nhds hδ)).and
    (eventually_ge_atTop 1)).exists_forall_of_atTop
  refine ⟨N, ?_⟩
  intro n hn
  obtain ⟨hnδ, hnpos⟩ := hN n hn
  have he := error_le_of_integrable hsec hdiag hT (show 0 < n from hnpos) (ε := η) ?_
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
    exact hmod _ hl r hrT hdist

theorem intervalIntegrable_crossMoment
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsFiniteMeasure P]
    {H K : ℝ → Ω → ℝ}
    (hH : Measurable (Function.uncurry H)) (hK : Measurable (Function.uncurry K))
    {A B : ℝ} (hA : 0 ≤ A) (_hB : 0 ≤ B)
    (hbH : ∀ t ω, |H t ω| ≤ A) (hbK : ∀ t ω, |K t ω| ≤ B)
    (a b : ℝ) : IntervalIntegrable (fun t => ∫ ω, H t ω * K t ω ∂P) volume a b := by
  let : IsFiniteMeasure (volume.restrict (uIoc a b)) :=
    isFiniteMeasure_restrict.mpr (by exact measure_Ioc_lt_top.ne)
  have hi : Integrable (fun p : ℝ × Ω => H p.1 p.2 * K p.1 p.2)
      ((volume.restrict (uIoc a b)).prod P) := by
    apply (integrable_const (A * B)).mono' (hH.mul hK).aestronglyMeasurable
    exact Eventually.of_forall fun p => by
      change ‖H p.1 p.2 * K p.1 p.2‖ ≤ A * B
      rw [Real.norm_eq_abs, abs_mul]
      exact mul_le_mul (hbH p.1 p.2) (hbK p.1 p.2) (abs_nonneg _) hA
  exact intervalIntegrable_iff.mpr hi.integral_prod_left

theorem tendsto_sum_mixed_crossMoment
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsFiniteMeasure P]
    {H K : ℝ → Ω → ℝ}
    (hH : ∀ t, Measurable (H t)) (hcH : ∀ ω, Continuous (fun t => H t ω))
    (hK : Measurable (Function.uncurry K))
    {A B : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hbH : ∀ t ω, |H t ω| ≤ A) (hbK : ∀ t ω, |K t ω| ≤ B)
    {T : ℝ} (hT : 0 ≤ T) :
    Tendsto (sum (fun s t => ∫ ω, H s ω * K t ω ∂P) T) atTop
      (𝓝 (∫ t in (0 : ℝ)..T, ∫ ω, H t ω * K t ω ∂P)) := by
  have hmH : Measurable (Function.uncurry H) :=
    measurable_uncurry_of_continuous_of_measurable hcH hH
  have hmK (t : ℝ) : Measurable (K t) :=
    hK.comp (measurable_const.prodMk measurable_id)
  have hint (s t : ℝ) : Integrable (fun ω => H s ω * K t ω) P := by
    apply (integrable_const (A * B)).mono' ((hH s).mul (hmK t)).aestronglyMeasurable
    exact Eventually.of_forall fun ω => by
      change ‖H s ω * K t ω‖ ≤ A * B
      rw [Real.norm_eq_abs, abs_mul]
      exact mul_le_mul (hbH s ω) (hbK t ω) (abs_nonneg _) hA
  let g : ℝ × ℝ → ℝ := fun p => ∫ ω, |H p.1 ω - H p.2 ω| ∂P
  have hg : Continuous g := by
    apply continuous_of_dominated (bound := fun _ => 2 * A)
    · intro p
      exact ((hH p.1).sub (hH p.2)).abs.aestronglyMeasurable
    · intro p
      exact Eventually.of_forall fun ω => by
        rw [Real.norm_eq_abs, abs_abs]
        exact (abs_sub _ _).trans (by linarith [hbH p.1 ω, hbH p.2 ω])
    · exact integrable_const _
    · exact Eventually.of_forall fun ω =>
        (((hcH ω).comp continuous_fst).sub ((hcH ω).comp continuous_snd)).abs
  apply tendsto_sum_of_first_uniform
  · intro s a b
    exact intervalIntegrable_crossMoment (H := fun _ ω => H s ω) ((hH s).comp measurable_snd) hK hA hB
      (fun _ ω => hbH s ω) hbK a b
  · exact intervalIntegrable_crossMoment hmH hK hA hB hbH hbK
  · exact hT
  · intro ε hε
    have hη : 0 < ε / (B + 1) := div_pos hε (by linarith)
    have hu := (isCompact_Icc.prod isCompact_Icc).uniformContinuousOn_of_continuous
      (s := (Icc (0 : ℝ) T) ×ˢ (Icc (0 : ℝ) T)) hg.continuousOn
    obtain ⟨δ, hδ, hmod⟩ := Metric.uniformContinuousOn_iff.mp hu (ε / (B + 1)) hη
    refine ⟨δ, hδ, ?_⟩
    intro s hs t ht hst
    have hpdist : dist (s, t) (t, t) < δ := by
      simpa only [Prod.dist_eq, dist_self, max_eq_left dist_nonneg] using hst
    have hsmall := hmod (s, t) ⟨hs, ht⟩ (t, t) ⟨ht, ht⟩ hpdist
    have hg0 : g (t, t) = 0 := by simp [g]
    rw [hg0, dist_zero_right, Real.norm_eq_abs] at hsmall
    have hgpos : 0 ≤ g (s, t) := integral_nonneg fun _ => abs_nonneg _
    rw [abs_of_nonneg hgpos] at hsmall
    calc
      _ = |∫ ω, (H s ω - H t ω) * K t ω ∂P| := by
        rw [← integral_sub (hint s t) (hint t t)]
        congr 2
        funext ω
        ring
      _ ≤ ∫ ω, |(H s ω - H t ω) * K t ω| ∂P := abs_integral_le_integral_abs
      _ ≤ ∫ ω, |H s ω - H t ω| * B ∂P := by
        apply integral_mono
        · have hsub : Integrable (fun ω => (H s ω - H t ω) * K t ω) P := by
            apply ((hint s t).sub (hint t t)).congr
            filter_upwards with ω
            change H s ω * K t ω - H t ω * K t ω = (H s ω - H t ω) * K t ω
            ring
          exact hsub.abs
        · apply (integrable_const (2 * A * B)).mono'
            (((hH s).sub (hH t)).abs.mul measurable_const).aestronglyMeasurable
          exact Eventually.of_forall fun ω => by
            change ‖|H s ω - H t ω| * B‖ ≤ 2 * A * B
            rw [Real.norm_eq_abs, abs_mul, abs_abs, abs_of_nonneg hB]
            exact mul_le_mul_of_nonneg_right
              ((abs_sub _ _).trans (by linarith [hbH s ω, hbH t ω])) hB
        · intro ω
          change |(H s ω - H t ω) * K t ω| ≤ |H s ω - H t ω| * B
          rw [abs_mul]
          exact mul_le_mul_of_nonneg_left (hbK t ω) (abs_nonneg _)
      _ = g (s, t) * B := by rw [integral_mul_const]
      _ ≤ (ε / (B + 1)) * B := mul_le_mul_of_nonneg_right hsmall.le hB
      _ ≤ ε := by
        rw [div_mul_eq_mul_div]
        exact (div_le_iff₀ (by linarith : 0 < B + 1)).mpr (by nlinarith)

theorem tendsto_mixed_cross_energy
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsFiniteMeasure P]
    {H K : ℝ≥0 → Ω → ℝ}
    (hH : ∀ t, Measurable (H t)) (hcH : ∀ ω, Continuous (fun t => H t ω))
    (hK : Measurable (Function.uncurry K))
    {A B : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hbH : ∀ t ω, |H t ω| ≤ A) (hbK : ∀ t ω, |K t ω| ≤ B)
    (T : ℝ≥0) :
    Tendsto (fun n : ℕ => ∑ i ∈ Finset.range n,
      ∫ r in (BrownianGrid.uniformGrid T n i : ℝ)..(BrownianGrid.uniformGrid T n (i + 1) : ℝ),
        ∫ ω, H (BrownianGrid.uniformGrid T n i) ω * K r.toNNReal ω ∂P)
      atTop (𝓝 (∫ r in (0 : ℝ)..(T : ℝ), ∫ ω, H r.toNNReal ω * K r.toNNReal ω ∂P)) := by
  have hp (n i : ℕ) : point (T : ℝ) n i = (BrownianGrid.uniformGrid T n i : ℝ) := by
    simp only [point, BrownianGrid.uniformGrid, NNReal.coe_mul, NNReal.coe_div,
      NNReal.coe_natCast]
    ring
  have hl := tendsto_sum_mixed_crossMoment (P := P)
    (H := fun r => H r.toNNReal) (K := fun r => K r.toNNReal)
    (fun r => hH r.toNNReal)
    (fun ω => (hcH ω).comp (by fun_prop))
    (hK.comp ((measurable_real_toNNReal.comp measurable_fst).prodMk measurable_snd))
    hA hB (fun r ω => hbH r.toNNReal ω) (fun r ω => hbK r.toNNReal ω) T.coe_nonneg
  change Tendsto (fun n => CrossEnergyRiemann.sum
    (fun (s t : ℝ) => ∫ ω, H s.toNNReal ω * K t.toNNReal ω ∂P) (T : ℝ) n)
    atTop (𝓝 (∫ r in (0 : ℝ)..(T : ℝ), ∫ ω, H r.toNNReal ω * K r.toNNReal ω ∂P)) at hl
  simpa only [CrossEnergyRiemann.sum, hp, Real.toNNReal_coe] using hl

end Problem367.CrossEnergyRiemann

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Energy_ProgressiveIsingCovariance
attribute [-instance] _root_.OAI.Problem367.IsingConditionalCopyBounds.graphLaw_isProbabilityMeasure _root_.OAI.Problem367.IsingObservationFactor.copies_probability _root_.OAI.Problem367.IsingObservationFactor.kernel_markov _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_observationLaw_probability _root_.OAI.Problem367.IsingObservationInnovation.observationLaw_probability _root_.OAI.Problem367.TreeKoopman.labelProbability _root_.OAI.Problem367.WienerSampler.pathMeasurableSpace _root_.OAI.Problem367.freeIsingMeasure_probability
attribute [-simp] _root_.OAI.Problem367.ConnectedHull.pathAssignment_path _root_.OAI.Problem367.ConnectedHull.path_last _root_.OAI.Problem367.ConnectedHull.path_zero _root_.OAI.Problem367.CutContinuationChannels.averageChannel_globalCone _root_.OAI.Problem367.CutContinuationChannels.continuationChannel_globalCone _root_.OAI.Problem367.FactorObservable.centeredSpinLp_coe _root_.OAI.Problem367.FiniteIsingSplit.splitEquiv_fst _root_.OAI.Problem367.FiniteIsingSplit.splitEquiv_snd _root_.OAI.Problem367.FinitePathGibbs.tailPartition_zero _root_.OAI.Problem367.GaussianTreeResponseNaturality.fieldEquiv_apply_image _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_apply _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_uniformObservation _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_zero _root_.OAI.Problem367.IsingObservationInnovation.uniformObservation_relabel _root_.OAI.Problem367.IsingOrientedPath.attenuation_outward _root_.OAI.Problem367.IsingOrientedPath.endpoint_extensionAt _root_.OAI.Problem367.LocalSupportGeometry.prefixVertex_length _root_.OAI.Problem367.PathSideBranches.parent_sideVertex _root_.OAI.Problem367.PathSideBranches.restrictNoisyRegion_array _root_.OAI.Problem367.PathSideBranches.sideVertex_length _root_.OAI.Problem367.PathSideBranches.sideVertex_val _root_.OAI.Problem367.PosteriorChain.transition_spinMean _root_.OAI.Problem367.PosteriorChain.transition_sum _root_.OAI.Problem367.RootedBroadcast.flipBranchToComplement_val _root_.OAI.Problem367.RootedBroadcast.pos_spinMul _root_.OAI.Problem367.RootedBroadcast.prefixFlip_branchRoot _root_.OAI.Problem367.RootedBroadcast.prefixFlip_root _root_.OAI.Problem367.RootedBroadcast.prefixTreeAut_symm_branchRoot _root_.OAI.Problem367.RootedBroadcast.prefixTreeAut_symm_root _root_.OAI.Problem367.RootedBroadcast.spinMul_pos _root_.OAI.Problem367.RootedBroadcast.spinMul_self _root_.OAI.Problem367.TreeConeCoding.length_vertex _root_.OAI.Problem367.TreeConeCoding.vertex_nil _root_.OAI.Problem367.TreeConeCoding.vertex_val _root_.OAI.Problem367.TreeGibbsAut.spinEquiv_apply_image _root_.OAI.Problem367.TreeKoopman.centeredAverage_apply_coe _root_.OAI.Problem367.TreeKoopman.centeredAverage_pow_apply_coe _root_.OAI.Problem367.TreeKoopman.centeredGenerator_apply_coe _root_.OAI.Problem367.TreeKoopman.centeredGenerator_sq _root_.OAI.Problem367.TreeKoopman.generatorOperator_sq _root_.OAI.Problem367.TreeKoopman.reverseVertex_twice _root_.OAI.Problem367.TreeKoopman.wordRelabel_cons _root_.OAI.Problem367.TreeKoopman.wordRelabel_nil _root_.OAI.Problem367.TreeLawKoopman.centeredAverage_apply_coe _root_.OAI.Problem367.TreeLawKoopman.generatorOperator_sq _root_.OAI.Problem367.TreePathGibbs.vertexEquiv_val _root_.OAI.Problem367.branchColorAut_length _root_.OAI.Problem367.branchColorAut_singleton _root_.OAI.Problem367.branchColorAut_val _root_.OAI.Problem367.branchColorMap_symm_apply _root_.OAI.Problem367.colorPermAut_length _root_.OAI.Problem367.colorPermAut_nil _root_.OAI.Problem367.colorPermAut_val _root_.OAI.Problem367.colorPermMap_symm_apply _root_.OAI.Problem367.colorPermMap_val _root_.OAI.Problem367.connectedSpinEncode_apply_root _root_.OAI.Problem367.connectedSpinEquiv_apply _root_.OAI.Problem367.dropVertex_length _root_.OAI.Problem367.dropVertex_val _root_.OAI.Problem367.mem_rootComplementFinset _root_.OAI.Problem367.mem_rootComponentFinset _root_.OAI.Problem367.mem_rootComponentIndices _root_.OAI.Problem367.parentVertex_length _root_.OAI.Problem367.parentVertex_val _root_.OAI.Problem367.prefixColorAut_length _root_.OAI.Problem367.prefixColorAut_val _root_.OAI.Problem367.prefixColorMap_symm_apply _root_.OAI.Problem367.prefixFlip_twice _root_.OAI.Problem367.spinAgreementCode_eq_neg_iff _root_.OAI.Problem367.spinAgreementCode_eq_pos_iff _root_.OAI.Problem367.spinSign_flip _root_.OAI.Problem367.tsum_treeShell_radial _root_.OAI.Problem367.vertexSampler_relabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal Topology

namespace Problem367

open PlantedSymmetry

local instance progressiveIsingCovarianceNonemptySpin : Nonempty IsingSpin := ⟨.neg⟩

lemma pairExhaustion_monotone {d : ℕ} (v w : TreeVertex d) :
    Monotone (pairExhaustion v w) := by
  intro n m hnm
  exact connectedExhaustion_monotone v (Nat.add_le_add_right hnm _)

lemma pairExhaustion_connected {d : ℕ} (v w : TreeVertex d) (n : ℕ) :
    ConnectedFinset (pairExhaustion v w n) := connectedExhaustion_connected v _

lemma exists_mem_pairExhaustion {d : ℕ} (v w u : TreeVertex d) :
    ∃ n, u ∈ pairExhaustion v w n := by
  obtain ⟨n, hn⟩ := (eventually_mem_connectedExhaustion v u).exists
  exact ⟨n, connectedExhaustion_monotone v (Nat.le_add_right n _) hn⟩

lemma continuous_finiteGibbsPairMean {d : ℕ} (beta : ℝ) (v w : TreeVertex d) (n : ℕ) :
    Continuous (finiteGibbsPairMean beta v w n) := by
  apply (FinitePosterior.continuous_fieldMean _ _ _).comp
  exact continuous_pi (fun u => continuous_apply u.1)

lemma measurable_infiniteGibbsPairMean {d : ℕ} (beta : ℝ) (v w : TreeVertex d) :
    Measurable (infiniteGibbsPairMean beta v w) := by
  have hm : StronglyMeasurable (fun y =>
      limUnder atTop (fun n => finiteGibbsPairMean beta v w n y)) :=
    StronglyMeasurable.limUnder
      (fun n => (continuous_finiteGibbsPairMean beta v w n).measurable.stronglyMeasurable)
  exact measurable_const.max (measurable_const.min hm.measurable)

lemma infiniteGibbsPairMean_abs_le_one {d : ℕ} (beta : ℝ) (v w : TreeVertex d)
    (y : TreeVertex d → ℝ) : |infiniteGibbsPairMean beta v w y| ≤ 1 := by
  rw [abs_le]
  exact ⟨le_max_left _ _, max_le (by norm_num) (min_le_left _ _)⟩

lemma spinSign_pair_norm_le_one {d : ℕ} (v w : TreeVertex d)
    (sigma : TreeVertex d → IsingSpin) : ‖spinSign (sigma v) * spinSign (sigma w)‖ ≤ 1 := by
  cases hv : sigma v <;> cases hw : sigma w <;> norm_num [spinSign, hv, hw]

theorem HasFreeIsingLaw.infiniteGibbsPairMean_eq_posterior {d : ℕ} {beta : ℝ}
    {μ : Measure (TreeVertex d → IsingSpin)}
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (t : ℝ≥0) (v w : TreeVertex d) :
    (fun p => infiniteGibbsPairMean beta v w (observation t p)) =ᵐ[
        μ.prod (gaussianNoiseLaw (TreeVertex d) t)]
      (μ.prod (gaussianNoiseLaw (TreeVertex d) t))[
        fun p => spinSign (p.1 v) * spinSign (p.1 w) |
        observationSigma (TreeVertex d) t] := by
  let : IsProbabilityMeasure μ := hμ.isProbabilityMeasure
  have hce (n : ℕ) := hμ.finiteObservation_condExp (pairExhaustion v w n)
    (pairExhaustion_connected v w n) t
    (fun eta => spinSign (eta ⟨v, mem_pairExhaustion_left v w n⟩) *
      spinSign (eta ⟨w, mem_pairExhaustion_right v w n⟩))
  have hlim := tendsto_ae_condExp (μ := μ.prod (gaussianNoiseLaw (TreeVertex d) t))
    (ℱ := finiteObservationFiltration (pairExhaustion v w)
      (pairExhaustion_monotone v w) t)
    (fun p => spinSign (p.1 v) * spinSign (p.1 w))
  rw [finiteObservationFiltration_iSup (pairExhaustion v w)
    (pairExhaustion_monotone v w) (exists_mem_pairExhaustion v w) t] at hlim
  have hb := ae_bdd_norm_condExp_of_ae_bdd_norm
    (μ := μ.prod (gaussianNoiseLaw (TreeVertex d) t))
    (m := observationSigma (TreeVertex d) t)
    (Eventually.of_forall (fun p => spinSign_pair_norm_le_one v w p.1))
  filter_upwards [ae_all_iff.mpr hce, hlim, hb] with p hp hlim hb
  have hseq : Tendsto (fun n => finiteGibbsPairMean beta v w n (observation t p)) atTop
      (𝓝 ((μ.prod (gaussianNoiseLaw (TreeVertex d) t))[
        fun p => spinSign (p.1 v) * spinSign (p.1 w) |
        observationSigma (TreeVertex d) t] p)) := by
    convert hlim using 1
    all_goals try with_reducible_and_instances rfl
    ext n
    exact (hp n).symm
  change max (-1) (min 1 (limUnder atTop _)) = _
  rw [hseq.limUnder_eq, min_eq_right (abs_le.mp hb).2, max_eq_right (abs_le.mp hb).1]

theorem HasFreeIsingLaw.infiniteGibbsPairMean_eq_brownian_past
    {d : ℕ} {beta : ℝ} {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure (TreeVertex d → IsingSpin)}
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ)
    (ν : TreeVertex d → Measure Ω)
    {B : TreeVertex d → ℝ≥0 → Ω → ℝ}
    (hB : ∀ i, IsPreBrownianReal (B i) (ν i))
    (hmB : ∀ i t, Measurable (B i t)) (t : ℝ≥0) (v w : TreeVertex d) :
    (fun p : (TreeVertex d → IsingSpin) × (TreeVertex d → Ω) =>
      infiniteGibbsPairMean beta v w
        (fun i => (t : ℝ) * spinSign (p.1 i) + B i t (p.2 i))) =ᵐ[
        μ.prod (Measure.infinitePi ν)]
      (μ.prod (Measure.infinitePi ν))[fun p => spinSign (p.1 v) * spinSign (p.1 w) |
        MeasurableSpace.comap
          (fun p : (TreeVertex d → IsingSpin) × (TreeVertex d → Ω) =>
            fun i (s : Set.Iic t) => (s.1 : ℝ) * spinSign (p.1 i) + B i s.1 (p.2 i))
          inferInstance] := by
  let : IsProbabilityMeasure μ := hμ.isProbabilityMeasure
  have (i : TreeVertex d) : IsProbabilityMeasure (ν i) :=
    (hB i).isGaussianProcess.isProbabilityMeasure
  let T : ((TreeVertex d → IsingSpin) × (TreeVertex d → Ω)) →
      (TreeVertex d → IsingSpin) × (TreeVertex d → ℝ) :=
    Prod.map id (fun omega i => B i t (omega i))
  have hT : MeasurePreserving T (μ.prod (Measure.infinitePi ν))
      (μ.prod (gaussianNoiseLaw (TreeVertex d) t)) :=
    (MeasurePreserving.id μ).prod (brownian_array_eval_measurePreserving ν hB hmB t)
  have hsign : Measurable spinSign := by intro s hs; trivial
  have hpair : Measurable (fun sigma : TreeVertex d → IsingSpin =>
      spinSign (sigma v) * spinSign (sigma w)) :=
    (hsign.comp (measurable_pi_apply v)).mul (hsign.comp (measurable_pi_apply w))
  have hpairi : Integrable (fun sigma : TreeVertex d → IsingSpin =>
      spinSign (sigma v) * spinSign (sigma w)) μ :=
    Integrable.of_bound hpair.aestronglyMeasurable 1
      (Eventually.of_forall (spinSign_pair_norm_le_one v w))
  have hpairpi : Integrable (fun p :
      (TreeVertex d → IsingSpin) × (TreeVertex d → ℝ) =>
      spinSign (p.1 v) * spinSign (p.1 w))
      (μ.prod (gaussianNoiseLaw (TreeVertex d) t)) :=
    Integrable.of_bound (hpair.comp measurable_fst).aestronglyMeasurable 1
      (Eventually.of_forall (fun p => spinSign_pair_norm_le_one v w p.1))
  have hpull := condExp_comp_measurePreserving_comap hT
    (hpair.comp measurable_fst).stronglyMeasurable hpairpi
    (observationSigma_le (TreeVertex d) t)
  have hpast := TerminalSufficiency.condExp_planted_infinite_past_eq_terminal
    μ ν hB hmB (fun sigma i => spinSign (sigma i))
    (fun sigma => spinSign (sigma v) * spinSign (sigma w))
    measurable_spinSign_array hpair hpairi t
  have heq := hμ.infiniteGibbsPairMean_eq_posterior t v w
  rw [← hT.map_eq] at heq
  have heq' := ae_of_ae_map hT.measurable.aemeasurable heq
  rw [hT.map_eq] at heq'
  have hsame : (observationSigma (TreeVertex d) (t : ℝ)).comap T =
      MeasurableSpace.comap
        (fun p : (TreeVertex d → IsingSpin) × (TreeVertex d → Ω) =>
          fun i => (t : ℝ) * spinSign (p.1 i) + B i t (p.2 i)) inferInstance := by
    rw [observationSigma, MeasurableSpace.comap_comp]
    rfl
  rw [hsame] at hpull
  filter_upwards [hpast, hpull, heq'] with p hpast hpull heq
  simp only [Function.comp_def, T, Prod.map_fst, id_eq] at hpull
  rw [hpast, hpull]
  exact heq

lemma measurable_infiniteGibbsCovariance {d : ℕ} (beta : ℝ) (v w : TreeVertex d) :
    Measurable (infiniteGibbsCovariance beta v w) :=
  (measurable_infiniteGibbsPairMean beta v w).sub
    ((measurable_infiniteGibbsSpinMean beta v).mul
      (measurable_infiniteGibbsSpinMean beta w))

lemma infiniteGibbsCovariance_abs_le_two {d : ℕ} (beta : ℝ) (v w : TreeVertex d)
    (y : TreeVertex d → ℝ) : |infiniteGibbsCovariance beta v w y| ≤ 2 := by
  have hp := infiniteGibbsPairMean_abs_le_one beta v w y
  have hv := infiniteGibbsSpinMean_abs_le_one beta v y
  have hw := infiniteGibbsSpinMean_abs_le_one beta w y
  have hprod : |infiniteGibbsSpinMean beta v y * infiniteGibbsSpinMean beta w y| ≤ 1 := by
    rw [abs_mul]
    simpa using mul_le_mul hv hw (abs_nonneg _) (by norm_num : (0 : ℝ) ≤ 1)
  exact (abs_sub _ _).trans (by linarith)

theorem HasFreeIsingLaw.infiniteGibbsCovariance_eq_brownian_past
    {d : ℕ} {beta : ℝ} {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure (TreeVertex d → IsingSpin)}
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ)
    (ν : TreeVertex d → Measure Ω)
    {B : TreeVertex d → ℝ≥0 → Ω → ℝ}
    (hB : ∀ i, IsPreBrownianReal (B i) (ν i))
    (hmB : ∀ i t, Measurable (B i t)) (t : ℝ≥0) (v w : TreeVertex d) :
    (fun p : (TreeVertex d → IsingSpin) × (TreeVertex d → Ω) =>
      infiniteGibbsCovariance beta v w
        (fun i => (t : ℝ) * spinSign (p.1 i) + B i t (p.2 i))) =ᵐ[
        μ.prod (Measure.infinitePi ν)]
      posteriorCovariance (μ.prod (Measure.infinitePi ν))
        (MeasurableSpace.comap
          (fun p : (TreeVertex d → IsingSpin) × (TreeVertex d → Ω) =>
            fun i (s : Set.Iic t) => (s.1 : ℝ) * spinSign (p.1 i) + B i s.1 (p.2 i))
          inferInstance)
        (fun p => spinSign (p.1 v)) (fun p => spinSign (p.1 w)) := by
  filter_upwards [hμ.infiniteGibbsPairMean_eq_brownian_past ν hB hmB t v w,
    hμ.infiniteGibbsSpinMean_eq_brownian_past ν hB hmB t v,
    hμ.infiniteGibbsSpinMean_eq_brownian_past ν hB hmB t w] with p hp hv hw
  exact congrArg₂ (fun a b : ℝ => a - b) hp (congrArg₂ (· * ·) hv hw)

end Problem367

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
-- module Solutions.Q243_FreeIsing.FreeIsing_Posterior_MixedFilteringCrossLimit
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

theorem tendsto_posterior_uniformSum_mixed_cross_energy
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsFiniteMeasure P]
    {F G : Filtration ℝ≥0 mΩ} {B m H K : ℝ≥0 → Ω → ℝ}
    (hB : Martingale B G P) (hFG : ∀ r, F r ≤ G r)
    {Q S : Ω → ℝ} {A C D L : ℝ}
    (hQ : StronglyMeasurable[G 0] Q) (hQb : ∀ᵐ ω ∂P, |Q ω| ≤ D)
    (hS : Integrable S P) (hSb : ∀ᵐ ω ∂P, |S ω| ≤ C)
    (hX : StronglyAdapted F (fun r ω => B r ω + (r : ℝ) * S ω))
    (hm : IsStronglyProgressive F m) (hpost : ∀ r, m r =ᵐ[P] P[S | F r])
    (hH : StronglyAdapted F H) (hcH : ∀ ω, Continuous (fun r => H r ω))
    (hA : 0 ≤ A) (hbH : ∀ r ω, |H r ω| ≤ A)
    (hK : Measurable (Function.uncurry K)) (hL : 0 ≤ L)
    (hbK : ∀ r ω, |K r ω| ≤ L)
    (hKversion : ∀ r, K r =ᵐ[P] fun ω =>
      P[(fun ω => Q ω * S ω) | F r] ω - P[Q | F r] ω * m r ω)
    (T : ℝ≥0) :
    Tendsto (fun n : ℕ => ∫ ω, P[Q | F T] ω *
      BrownianGrid.uniformSum (innovation B S m) H T n ω ∂P) atTop
      (𝓝 (∫ r in (0 : ℝ)..(T : ℝ), ∫ ω, H r.toNNReal ω * K r.toNNReal ω ∂P)) := by
  have hlim := CrossEnergyRiemann.tendsto_mixed_cross_energy (P := P)
    (fun r => ((hH r).mono (F.le r)).measurable) hcH hK hA hL hbH hbK T
  apply hlim.congr'
  filter_upwards [eventually_ge_atTop 1] with n hn
  have he := integral_posterior_mul_uniformSum hB hFG hQ hQb hS hSb hX hm hpost hH
    (fun r => Eventually.of_forall (hbH r)) T (show 0 < n from hn)
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
-- module Solutions.Q243_FreeIsing.FreeIsing_Ising_MixedFiltering
attribute [-instance] _root_.OAI.Problem367.IsingConditionalCopyBounds.graphLaw_isProbabilityMeasure _root_.OAI.Problem367.IsingObservationFactor.copies_probability _root_.OAI.Problem367.IsingObservationFactor.kernel_markov _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_observationLaw_probability _root_.OAI.Problem367.IsingObservationInnovation.observationLaw_probability _root_.OAI.Problem367.TreeKoopman.labelProbability _root_.OAI.Problem367.freeIsingMeasure_probability
attribute [-simp] _root_.OAI.Problem367.ConnectedHull.pathAssignment_path _root_.OAI.Problem367.ConnectedHull.path_last _root_.OAI.Problem367.ConnectedHull.path_zero _root_.OAI.Problem367.CutContinuationChannels.averageChannel_globalCone _root_.OAI.Problem367.CutContinuationChannels.continuationChannel_globalCone _root_.OAI.Problem367.FactorObservable.centeredSpinLp_coe _root_.OAI.Problem367.FiniteIsingSplit.splitEquiv_fst _root_.OAI.Problem367.FiniteIsingSplit.splitEquiv_snd _root_.OAI.Problem367.FinitePathGibbs.tailPartition_zero _root_.OAI.Problem367.GaussianTreeResponseNaturality.fieldEquiv_apply_image _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_apply _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_uniformObservation _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_zero _root_.OAI.Problem367.IsingObservationInnovation.uniformObservation_relabel _root_.OAI.Problem367.IsingOrientedPath.attenuation_outward _root_.OAI.Problem367.IsingOrientedPath.endpoint_extensionAt _root_.OAI.Problem367.LocalSupportGeometry.prefixVertex_length _root_.OAI.Problem367.PathSideBranches.parent_sideVertex _root_.OAI.Problem367.PathSideBranches.restrictNoisyRegion_array _root_.OAI.Problem367.PathSideBranches.sideVertex_length _root_.OAI.Problem367.PathSideBranches.sideVertex_val _root_.OAI.Problem367.PosteriorChain.transition_spinMean _root_.OAI.Problem367.PosteriorChain.transition_sum _root_.OAI.Problem367.RootedBroadcast.flipBranchToComplement_val _root_.OAI.Problem367.RootedBroadcast.pos_spinMul _root_.OAI.Problem367.RootedBroadcast.prefixFlip_branchRoot _root_.OAI.Problem367.RootedBroadcast.prefixFlip_root _root_.OAI.Problem367.RootedBroadcast.prefixTreeAut_symm_branchRoot _root_.OAI.Problem367.RootedBroadcast.prefixTreeAut_symm_root _root_.OAI.Problem367.RootedBroadcast.spinMul_pos _root_.OAI.Problem367.RootedBroadcast.spinMul_self _root_.OAI.Problem367.TreeConeCoding.length_vertex _root_.OAI.Problem367.TreeConeCoding.vertex_nil _root_.OAI.Problem367.TreeConeCoding.vertex_val _root_.OAI.Problem367.TreeGibbsAut.spinEquiv_apply_image _root_.OAI.Problem367.TreeKoopman.centeredAverage_apply_coe _root_.OAI.Problem367.TreeKoopman.centeredAverage_pow_apply_coe _root_.OAI.Problem367.TreeKoopman.centeredGenerator_apply_coe _root_.OAI.Problem367.TreeKoopman.centeredGenerator_sq _root_.OAI.Problem367.TreeKoopman.generatorOperator_sq _root_.OAI.Problem367.TreeKoopman.reverseVertex_twice _root_.OAI.Problem367.TreeKoopman.wordRelabel_cons _root_.OAI.Problem367.TreeKoopman.wordRelabel_nil _root_.OAI.Problem367.TreeLawKoopman.centeredAverage_apply_coe _root_.OAI.Problem367.TreeLawKoopman.generatorOperator_sq _root_.OAI.Problem367.TreePathGibbs.vertexEquiv_val _root_.OAI.Problem367.branchColorAut_length _root_.OAI.Problem367.branchColorAut_singleton _root_.OAI.Problem367.branchColorAut_val _root_.OAI.Problem367.branchColorMap_symm_apply _root_.OAI.Problem367.colorPermAut_length _root_.OAI.Problem367.colorPermAut_nil _root_.OAI.Problem367.colorPermAut_val _root_.OAI.Problem367.colorPermMap_symm_apply _root_.OAI.Problem367.colorPermMap_val _root_.OAI.Problem367.connectedSpinEncode_apply_root _root_.OAI.Problem367.connectedSpinEquiv_apply _root_.OAI.Problem367.dropVertex_length _root_.OAI.Problem367.dropVertex_val _root_.OAI.Problem367.mem_rootComplementFinset _root_.OAI.Problem367.mem_rootComponentFinset _root_.OAI.Problem367.mem_rootComponentIndices _root_.OAI.Problem367.parentVertex_length _root_.OAI.Problem367.parentVertex_val _root_.OAI.Problem367.prefixColorAut_length _root_.OAI.Problem367.prefixColorAut_val _root_.OAI.Problem367.prefixColorMap_symm_apply _root_.OAI.Problem367.prefixFlip_twice _root_.OAI.Problem367.spinAgreementCode_eq_neg_iff _root_.OAI.Problem367.spinAgreementCode_eq_pos_iff _root_.OAI.Problem367.spinSign_flip _root_.OAI.Problem367.tsum_treeShell_radial
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped NNReal Topology
namespace Problem367.IsingInnovation

variable {d : ℕ} {A : Type*} [MeasurableSpace A]

lemma measurable_covariance_joint
    (beta : ℝ) (B : ℝ≥0 → A → ℝ) (hmB : ∀ t, Measurable (B t))
    (hcB : ∀ a, Continuous (fun t => B t a)) (v u : TreeVertex d) :
    Measurable (Function.uncurry (covariance beta B v u)) := by
  apply (measurable_infiniteGibbsCovariance beta v u).comp
  apply Measurable.of_eval
  intro i
  apply StronglyMeasurable.measurable
  change StronglyMeasurable (Function.uncurry
    (plantedArrayObservation (fun _ : TreeVertex d => B) ArrayPosteriorStationarity.spinArray i))
  apply stronglyMeasurable_uncurry_of_continuous_of_stronglyMeasurable
  · intro q
    exact (hcB (q.2 i)).add (continuous_subtype_val.mul continuous_const)
  · intro t
    exact (plantedArrayObservation_measurable (fun _ => hmB)
      ArrayPosteriorStationarity.measurable_spinArray i t).stronglyMeasurable

omit [MeasurableSpace A] in
lemma covariance_abs_le_two (beta : ℝ) (B : ℝ≥0 → A → ℝ)
    (v u : TreeVertex d) (t : ℝ≥0) (q : State d A) :
    |covariance beta B v u t q| ≤ 2 :=
  infiniteGibbsCovariance_abs_le_two beta v u _

lemma covariance_eq_condExp
    {beta : ℝ} {μ : Measure (TreeVertex d → IsingSpin)}
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ)
    (ν : Measure A) {B : ℝ≥0 → A → ℝ} (hB : IsPreBrownianReal B ν)
    (hmB : ∀ t, Measurable (B t)) (t : ℝ≥0) (v u : TreeVertex d) :
    let P := μ.prod (Measure.infinitePi (fun _ : TreeVertex d => ν))
    let F := ArrayPosteriorStationarity.filtration B hmB
    covariance beta B v u t =ᵐ[P] fun q =>
      P[(fun q : State d A => spinSign (q.1 v) * spinSign (q.1 u)) | F t] q -
      P[(fun q : State d A => spinSign (q.1 v)) | F t] q * posterior beta B u t q := by
  have hc := hμ.infiniteGibbsCovariance_eq_brownian_past
    (fun _ : TreeVertex d => ν) (fun _ => hB) (fun _ => hmB) t v u
  have hF : ArrayPosteriorStationarity.filtration (d := d) B hmB t =
      MeasurableSpace.comap
        (fun q : State d A => fun i (s : Set.Iic t) =>
          (s.1 : ℝ) * spinSign (q.1 i) + B s.1 (q.2 i)) inferInstance := by
    change arrayNaturalFiltration
      (plantedArrayObservation (fun _ : TreeVertex d => B) ArrayPosteriorStationarity.spinArray)
      (plantedArrayObservation_measurable (fun _ => hmB)
        ArrayPosteriorStationarity.measurable_spinArray) t = _
    rw [arrayNaturalFiltration_eq_comap]
    congr 1
    funext q i s
    exact add_comm _ _
  rw [← hF] at hc
  have hp := posterior_eq_condExp hμ ν hB hmB t u
  filter_upwards [hc, hp] with q hq hu
  dsimp only [posteriorCovariance] at hq
  rw [hu]
  simpa only [covariance, plantedArrayObservation, ArrayPosteriorStationarity.spinArray,
    ArrayPosteriorStationarity.posterior, add_comm] using hq

theorem tendsto_trial_cross_uniformSum_oai
    {beta : ℝ} {μ : Measure (TreeVertex d → IsingSpin)}
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ)
    (ν : Measure A) {B : ℝ≥0 → A → ℝ} (hB : IsPreBrownianReal B ν)
    (hmB : ∀ t, Measurable (B t)) (hcB : ∀ a, Continuous (fun t => B t a))
    (v u : TreeVertex d) {H : ℝ≥0 → State d A → ℝ} {L : ℝ}
    (hH : StronglyAdapted (ArrayPosteriorStationarity.filtration B hmB) H)
    (hcH : ∀ q, Continuous (fun t => H t q))
    (hL : 0 ≤ L) (hbH : ∀ t q, |H t q| ≤ L) (T : ℝ≥0) :
    Tendsto (fun n : ℕ => ∫ q, posterior beta B v T q *
      BrownianGrid.uniformSum (innovation beta B u) H T n q
        ∂μ.prod (Measure.infinitePi (fun _ : TreeVertex d => ν))) atTop
      (𝓝 (∫ r in (0 : ℝ)..(T : ℝ), ∫ q,
        H r.toNNReal q * covariance beta B v u r.toNNReal q
          ∂μ.prod (Measure.infinitePi (fun _ : TreeVertex d => ν)))) := by
  let : IsProbabilityMeasure μ := hμ.isProbabilityMeasure
  let : IsProbabilityMeasure ν := hB.isGaussianProcess.isProbabilityMeasure
  let P := μ.prod (Measure.infinitePi (fun _ : TreeVertex d => ν))
  have hs (i : TreeVertex d) : Measurable (fun sigma : TreeVertex d → IsingSpin =>
      spinSign (sigma i)) := (measurable_of_finite spinSign).comp (measurable_pi_apply i)
  have hb (i : TreeVertex d) : ∀ q : State d A, |spinSign (q.1 i)| ≤ (1 : ℝ) := by
    intro q
    cases q.1 i <;> norm_num [spinSign]
  have hobs := arrayNaturalFiltration_stronglyAdapted
    (plantedArrayObservation (fun _ : TreeVertex d => B) ArrayPosteriorStationarity.spinArray)
    (plantedArrayObservation_measurable (fun _ => hmB)
      ArrayPosteriorStationarity.measurable_spinArray) u
  have hl := FilteringCrossEnergy.tendsto_posterior_uniformSum_mixed_cross_energy
    (preBrownian_martingale_signalArrayFiltration μ (fun _ : TreeVertex d => ν)
      (fun _ => hB) (fun _ => hmB) u)
    (arrayObservationFiltration_le_signalArrayFiltration (fun _ : TreeVertex d => B)
      (fun _ => hmB) ArrayPosteriorStationarity.spinArray
      ArrayPosteriorStationarity.measurable_spinArray)
    (stronglyMeasurable_latent_signalArrayFiltration (fun _ : TreeVertex d => B)
      (fun _ => hmB) (hs v) 0)
    (Eventually.of_forall (hb v))
    (ArrayPosteriorStationarity.integrable_spin_coordinate P u)
    (Eventually.of_forall (hb u)) hobs (posterior_progressive beta B hmB hcB u)
    (fun t => posterior_eq_condExp hμ ν hB hmB t u)
    hH hcH hL hbH (measurable_covariance_joint beta B hmB hcB v u)
    (show (0 : ℝ) ≤ 2 by norm_num) (covariance_abs_le_two beta B v u)
    (fun t => covariance_eq_condExp hμ ν hB hmB t v u) T
  apply hl.congr
  intro n
  apply integral_congr_ae
  filter_upwards [posterior_eq_condExp hμ ν hB hmB T v] with q hq
  rw [hq]
  rfl

end Problem367.IsingInnovation

end

end OAI
end

theorem solution.{u_1} : type_of% @OAI.Problem367.IsingInnovation.tendsto_trial_cross_uniformSum_oai.{u_1} := @OAI.Problem367.IsingInnovation.tendsto_trial_cross_uniformSum_oai.{u_1}
