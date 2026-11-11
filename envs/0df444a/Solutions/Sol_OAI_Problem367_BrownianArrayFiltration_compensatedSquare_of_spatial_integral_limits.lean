-- Prove2me | solution 1 for OAI.Problem367.BrownianArrayFiltration.compensatedSquare_of_spatial_integral_limits
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T01:41:24.491997+00:00
-- url     : https://prove2.me/submissions/d21f254b-41bf-4208-9084-3b44ff77286e

import Mathlib
import Definitions.Def_Q243FI003
import Theorems.Thm_OAI_Problem367_BrownianArrayFiltration_exists_global_continuous_spatial_integral_compensatedSquare

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Brownian_UniformGrid
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace Problem367.BrownianGrid

lemma integral_sq_sub_le_two {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {X Y Z : Ω → ℝ} (hX : MemLp X 2 P) (hY : MemLp Y 2 P) (hZ : MemLp Z 2 P) :
    (∫ ω, (X ω - Y ω) ^ 2 ∂P) ≤
      2 * (∫ ω, (X ω - Z ω) ^ 2 ∂P) + 2 * (∫ ω, (Y ω - Z ω) ^ 2 ∂P) := by
  have hXY : Integrable (fun ω => (X ω - Y ω) ^ 2) P := (hX.sub hY).integrable_sq
  have hXZ : Integrable (fun ω => (X ω - Z ω) ^ 2) P := (hX.sub hZ).integrable_sq
  have hYZ : Integrable (fun ω => (Y ω - Z ω) ^ 2) P := (hY.sub hZ).integrable_sq
  calc
    _ ≤ ∫ ω, 2 * (X ω - Z ω) ^ 2 + 2 * (Y ω - Z ω) ^ 2 ∂P := by
      apply integral_mono hXY ((hXZ.const_mul 2).add (hYZ.const_mul 2))
      intro ω
      change (X ω - Y ω) ^ 2 ≤ 2 * (X ω - Z ω) ^ 2 + 2 * (Y ω - Z ω) ^ 2
      nlinarith [sq_nonneg (X ω + Y ω - 2 * Z ω)]
    _ = _ := by
      rw [integral_add (hXZ.const_mul 2) (hYZ.const_mul 2), integral_const_mul, integral_const_mul]

end Problem367.BrownianGrid

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Factors_ContinuousRecovery
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Filter TopologicalSpace

namespace Problem367

theorem ae_eq_of_integral_sq_sub_eq_zero
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {f g : Ω → ℝ}
    (hInt : Integrable (fun ω => (f ω - g ω) ^ 2) μ)
    (hzero : (∫ ω, (f ω - g ω) ^ 2 ∂μ) = 0) : f =ᵐ[μ] g := by
  have h := (integral_eq_zero_iff_of_nonneg (fun ω => sq_nonneg (f ω - g ω))
    hInt).mp hzero
  filter_upwards [h] with ω hω
  exact sub_eq_zero.mp (sq_eq_zero_iff.mp hω)

end Problem367

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Brownian_IntegralProperties
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped NNReal Topology

namespace Problem367.BrownianGrid

theorem ae_eq_of_mean_square_limits
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {X : ℕ → Ω → ℝ} {I J : Ω → ℝ}
    (hX : ∀ n, MemLp (X n) 2 P) (hI : MemLp I 2 P) (hJ : MemLp J 2 P)
    (hlimI : Tendsto (fun n => ∫ ω, (X n ω - I ω) ^ 2 ∂P) atTop (𝓝 0))
    (hlimJ : Tendsto (fun n => ∫ ω, (X n ω - J ω) ^ 2 ∂P) atTop (𝓝 0)) :
    I =ᵐ[P] J := by
  have hb (n : ℕ) : (∫ ω, (I ω - J ω) ^ 2 ∂P) ≤
      2 * (∫ ω, (X n ω - I ω) ^ 2 ∂P) + 2 * (∫ ω, (X n ω - J ω) ^ 2 ∂P) := by
    simpa only [sub_sq_comm] using integral_sq_sub_le_two hI hJ (hX n)
  have hz : (∫ ω, (I ω - J ω) ^ 2 ∂P) ≤ 0 := by
    apply le_of_tendsto_of_tendsto tendsto_const_nhds
      (show Tendsto (fun n => 2 * (∫ ω, (X n ω - I ω) ^ 2 ∂P) +
        2 * (∫ ω, (X n ω - J ω) ^ 2 ∂P)) atTop (𝓝 0) from ?_)
      (Filter.Eventually.of_forall hb)
    simpa only [mul_zero, add_zero] using (hlimI.const_mul 2).add (hlimJ.const_mul 2)
  exact ae_eq_of_integral_sq_sub_eq_zero (hI.sub hJ).integrable_sq
    (le_antisymm hz (integral_nonneg (fun ω => sq_nonneg _)))

end Problem367.BrownianGrid

end

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

end Problem367.EnergyRiemann

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Stochastic_RandomRiemannCompensator
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Filter Set
open scoped Topology ENNReal NNReal

namespace Problem367.RandomRiemann

theorem partition_error_le {f : ℝ → ℝ} (hf : Continuous f)
    {τ : ℕ → ℝ} (hτ : Monotone τ) (n : ℕ) {ε : ℝ}
    (hmod : ∀ i < n, ∀ x ∈ Icc (τ i) (τ (i + 1)), |f (τ i) - f x| ≤ ε) :
    |partitionSum f τ n - ∫ x in τ 0..τ n, f x| ≤ ε * (τ n - τ 0) := by
  have hsplit := intervalIntegral.sum_integral_adjacent_intervals
    (μ := volume) (a := τ) (n := n) (fun i _ => hf.intervalIntegrable _ _)
  have heq : partitionSum f τ n - (∫ x in τ 0..τ n, f x) =
      ∑ i ∈ Finset.range n, ∫ x in τ i..τ (i + 1), f (τ i) - f x := by
    rw [partitionSum, ← hsplit, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    rw [intervalIntegral.integral_sub intervalIntegrable_const (hf.intervalIntegrable _ _),
      intervalIntegral.integral_const, smul_eq_mul]
  rw [heq]
  calc
    _ ≤ ∑ i ∈ Finset.range n, |∫ x in τ i..τ (i + 1), f (τ i) - f x| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i ∈ Finset.range n, ε * (τ (i + 1) - τ i) := by
      apply Finset.sum_le_sum
      intro i hi
      have hle := hτ (Nat.le_succ i)
      have h := intervalIntegral.norm_integral_le_of_norm_le_const
        (a := τ i) (b := τ (i + 1)) (C := ε)
        (f := fun x => f (τ i) - f x) (fun x hx => ?_)
      · simpa only [Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr hle)] using h
      · rw [uIoc_of_le hle] at hx
        exact hmod i (Finset.mem_range.mp hi) x ⟨hx.1.le, hx.2⟩
    _ = _ := by rw [← Finset.mul_sum, Finset.sum_range_sub]

theorem stoppedPoint_mono {T : ℝ} (hT : 0 ≤ T) (t : ℝ) (n : ℕ) :
    Monotone (stoppedPoint T t n) := fun _ _ hij =>
  min_le_min_left t (EnergyRiemann.point_mono hT n hij)

theorem stoppedPoint_zero (T : ℝ) {t : ℝ} (ht : 0 ≤ t) (n : ℕ) :
    stoppedPoint T t n 0 = 0 := by simp [stoppedPoint, ht]

theorem stoppedPoint_end (T t : ℝ) {n : ℕ} (hn : 0 < n) :
    stoppedPoint T t n n = min t T := by rw [stoppedPoint, EnergyRiemann.point_end T hn]

theorem stoppedPoint_step_le {T : ℝ} (hT : 0 ≤ T) (t : ℝ) (n i : ℕ) :
    stoppedPoint T t n (i + 1) - stoppedPoint T t n i ≤ T / n := by
  have hle := EnergyRiemann.point_mono hT n (Nat.le_succ i)
  have hstep := EnergyRiemann.point_step T n i
  unfold stoppedPoint
  by_cases hi : EnergyRiemann.point T n i ≤ t
  · rw [min_eq_right hi]
    exact (sub_le_sub_right (min_le_right t _) _).trans_eq hstep
  · have ht : t ≤ EnergyRiemann.point T n i := le_of_not_ge hi
    rw [min_eq_left ht, min_eq_left (ht.trans hle), sub_self]
    positivity

theorem stoppedSum_eq_partitionSum {T : ℝ} (hT : 0 ≤ T)
    (f : ℝ → ℝ) (t : ℝ) (n : ℕ) :
    stoppedSum f T t n = partitionSum f (stoppedPoint T t n) n := by
  apply Finset.sum_congr rfl
  intro i hi
  by_cases hit : EnergyRiemann.point T n i ≤ t
  · simp only [stoppedPoint, min_eq_right hit]
  · have ht : t ≤ EnergyRiemann.point T n i := le_of_not_ge hit
    have ht' := ht.trans (EnergyRiemann.point_mono hT n (Nat.le_succ i))
    simp only [stoppedPoint, min_eq_left ht, min_eq_left ht', sub_self, zero_mul]

theorem tendsto_stoppedSum {f : ℝ → ℝ} (hf : Continuous f)
    {T t : ℝ} (hT : 0 ≤ T) (ht : 0 ≤ t) :
    Tendsto (stoppedSum f T t) atTop (𝓝 (∫ x in (0 : ℝ)..min t T, f x)) := by
  apply Metric.tendsto_atTop.mpr
  intro ε hε
  let η := ε / (T + 1)
  have hη : 0 < η := div_pos hε (by linarith)
  have hUC := isCompact_Icc.uniformContinuousOn_of_continuous
    (s := Icc (0 : ℝ) T) hf.continuousOn
  obtain ⟨δ, hδ, hδmod⟩ := Metric.uniformContinuousOn_iff.mp hUC η hη
  have hwidth : Tendsto (fun n : ℕ => T / (n : ℝ)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
  have hev : ∀ᶠ n : ℕ in atTop, T / (n : ℝ) < δ := hwidth.eventually (gt_mem_nhds hδ)
  obtain ⟨N, hN⟩ := (hev.and (eventually_ge_atTop 1)).exists_forall_of_atTop
  refine ⟨N, ?_⟩
  intro n hn
  obtain ⟨hmesh, hnpos⟩ := hN n hn
  have hn' : 0 < n := hnpos
  have hmem (i : ℕ) (hi : i ≤ n) : stoppedPoint T t n i ∈ Icc (0 : ℝ) T := by
    constructor
    · rw [← stoppedPoint_zero T ht n]
      exact stoppedPoint_mono hT t n (Nat.zero_le i)
    · exact (stoppedPoint_mono hT t n hi).trans
        ((stoppedPoint_end T t hn').le.trans (min_le_right t T))
  have he := partition_error_le hf (stoppedPoint_mono hT t n) n (ε := η) ?_
  · rw [stoppedPoint_zero T ht, stoppedPoint_end T t hn',
      ← stoppedSum_eq_partitionSum hT] at he
    change |stoppedSum f T t n - ∫ x in (0 : ℝ)..min t T, f x| < ε
    calc
      _ ≤ η * (min t T - 0) := he
      _ ≤ η * T := by gcongr; simp
      _ < ε := by
        dsimp [η]
        rw [div_mul_eq_mul_div]
        apply (div_lt_iff₀ (by linarith : 0 < T + 1)).mpr
        nlinarith
  · intro i hi x hx
    have hleft := hmem i hi.le
    have hright := hmem (i + 1) (Nat.succ_le_of_lt hi)
    have hxT : x ∈ Icc (0 : ℝ) T := ⟨hleft.1.trans hx.1, hx.2.trans hright.2⟩
    have hdist : dist (stoppedPoint T t n i) x < δ := by
      rw [Real.dist_eq, abs_of_nonpos (sub_nonpos.mpr hx.1)]
      have hstep := stoppedPoint_step_le hT t n i
      linarith [hx.2]
    exact (hδmod _ hleft x hxT hdist).le

end Problem367.RandomRiemann

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Stochastic_SelectedCompensator
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped NNReal ENNReal Topology

namespace Problem367.SelectedCompensator

variable {Ω : Type*} [mΩ : MeasurableSpace Ω]

theorem coe_uniformGrid (T : ℝ≥0) (n i : ℕ) :
    (BrownianGrid.uniformGrid T n i : ℝ) = EnergyRiemann.point T n i := by
  simp only [BrownianGrid.uniformGrid, NNReal.coe_div, NNReal.coe_mul,
    NNReal.coe_natCast, EnergyRiemann.point]
  ring

omit mΩ in
theorem squareSum_eq_stoppedSum (H : ℝ≥0 → Ω → ℝ) (T : ℝ≥0) (n : ℕ) (t : ℝ≥0) :
    squareSum H T n t = fun ω => RandomRiemann.stoppedSum
      (fun s => (H s.toNNReal ω) ^ 2) T t n := by
  funext ω
  unfold squareSum RandomRiemann.stoppedSum RandomRiemann.stoppedPoint
  apply Finset.sum_congr rfl
  intro i hi
  simp only [← coe_uniformGrid, Real.toNNReal_coe]

omit mΩ in
theorem selected_eq_integral_of_continuous {H : ℝ≥0 → Ω → ℝ} {ω : Ω}
    (hc : Continuous (fun s => H s ω)) (T t : ℝ≥0) :
    selected H T t ω = ∫ s in (0 : ℝ)..min (t : ℝ) T, (H s.toNNReal ω) ^ 2 := by
  apply Filter.Tendsto.limUnder_eq
  have hcR : Continuous (fun s : ℝ => (H s.toNNReal ω) ^ 2) := by fun_prop
  have h := RandomRiemann.tendsto_stoppedSum hcR T.coe_nonneg t.coe_nonneg
  simpa only [squareSum_eq_stoppedSum, Function.comp_apply, Pi.pow_apply] using h

end Problem367.SelectedCompensator

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Estimates_NonnegativeSeriesL1
attribute [-instance] _root_.OAI.Problem367.WienerSampler.pathMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Filter
open scoped Topology ENNReal

namespace Problem367.NonnegativeSeriesL1

variable {Ω ι : Type*} [MeasurableSpace Ω] [Countable ι] {μ : Measure Ω}

theorem integrable_tsum_of_nonnegative
    {f : ι → Ω → ℝ} (hf : ∀ i, Integrable (f i) μ)
    (hn : ∀ i ω, 0 ≤ f i ω) (hs : Summable (fun i => ∫ ω, f i ω ∂μ)) :
    (∀ᵐ ω ∂μ, Summable (fun i => f i ω)) ∧
      Integrable (fun ω => ∑' i, f i ω) μ ∧
      (∫ ω, ∑' i, f i ω ∂μ) = ∑' i, ∫ ω, f i ω ∂μ := by
  have hm (i : ι) : AEMeasurable (fun ω => ENNReal.ofReal (f i ω)) μ :=
    (hf i).aemeasurable.ennreal_ofReal
  have hfin : (∫⁻ ω, ∑' i, ENNReal.ofReal (f i ω) ∂μ) < ∞ := by
    rw [lintegral_tsum hm]
    calc
      (∑' i, ∫⁻ ω, ENNReal.ofReal (f i ω) ∂μ) =
          ∑' i, ENNReal.ofReal (∫ ω, f i ω ∂μ) := by
        apply tsum_congr
        intro i
        exact (ofReal_integral_eq_lintegral_ofReal (hf i)
          (Eventually.of_forall (hn i))).symm
      _ < ∞ := hs.tsum_ofReal_lt_top
  have hae : ∀ᵐ ω ∂μ, Summable (fun i => f i ω) := by
    filter_upwards [ae_lt_top' (AEMeasurable.tsum hm) hfin.ne] with ω hω
    simpa only [ENNReal.toReal_ofReal (hn _ _)] using ENNReal.summable_toReal hω.ne
  have hint : Integrable (fun ω => ∑' i, f i ω) μ := by
    have h := integrable_toReal_of_lintegral_ne_top (AEMeasurable.tsum hm) hfin.ne
    simpa only [ENNReal.tsum_toReal_eq (fun i => ENNReal.ofReal_ne_top),
      ENNReal.toReal_ofReal (hn _ _)] using h
  refine ⟨hae, hint, ?_⟩
  exact (integral_tsum_of_summable_integral_norm hf
    (by simpa only [Real.norm_eq_abs, abs_of_nonneg (hn _ _)] using hs)).symm

end Problem367.NonnegativeSeriesL1

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Estimates_ProgressivePrimitive
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace Problem367

theorem continuous_nnreal_primitive_of_integrable_horizons
    (f : ℝ → ℝ) (hf : ∀ n : ℕ, IntervalIntegrable f volume 0 (n : ℝ)) :
    Continuous (fun t : ℝ≥0 => ∫ u in (0 : ℝ)..(t : ℝ), f u) := by
  rw [continuous_iff_continuousAt]
  intro t
  obtain ⟨n, hn⟩ := exists_nat_gt (t : ℝ)
  have hcont : Continuous (fun s : ℝ≥0 => ∫ u in (0 : ℝ)..min (s : ℝ) (n : ℝ), f u) := by
    apply (intervalIntegral.continuousOn_primitive_interval' (hf n)
      (Set.left_mem_uIcc : (0 : ℝ) ∈ Set.uIcc 0 (n : ℝ))).comp_continuous
        (NNReal.continuous_coe.min continuous_const)
    intro s
    rw [Set.uIcc_of_le (Nat.cast_nonneg n)]
    exact ⟨le_min s.coe_nonneg (Nat.cast_nonneg n), min_le_right _ _⟩
  apply hcont.continuousAt.congr_of_eventuallyEq
  filter_upwards [NNReal.continuous_coe.continuousAt.eventually (gt_mem_nhds hn)] with s hs
  simp only [min_eq_left hs.le]

end Problem367

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Brownian_SpatialPrimitive
attribute [-instance] _root_.OAI.Problem367.WienerSampler.pathMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal Topology

namespace Problem367.BrownianArrayFiltration

variable {Ω ι : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}

omit mΩ in
theorem nonnegativeCompensator_eq_integral_of_continuous
    {H : ℝ≥0 → Ω → ℝ} {ω : Ω} (hc : Continuous (fun t => H t ω)) (t : ℝ≥0) :
    nonnegativeCompensator H t ω = ∫ s in (0 : ℝ)..(t : ℝ), (H s.toNNReal ω) ^ 2 := by
  unfold nonnegativeCompensator BrownianIntegralProcess.globalCompensator
  rw [SelectedCompensator.selected_eq_integral_of_continuous hc, min_self]
  exact max_eq_left (intervalIntegral.integral_nonneg t.coe_nonneg (fun s _ => sq_nonneg _))

theorem summable_integral_sq_of_integer
    {h : ι → ℝ≥0 → ℝ} (hc : ∀ a, Continuous (h a))
    (hs : ∀ N : ℕ, Summable (fun a => ∫ s in (0 : ℝ)..(N : ℝ), (h a s.toNNReal) ^ 2))
    (t : ℝ≥0) : Summable (fun a => ∫ s in (0 : ℝ)..(t : ℝ), (h a s.toNNReal) ^ 2) := by
  obtain ⟨N, hN⟩ := exists_nat_ge (t : ℝ)
  apply Summable.of_nonneg_of_le
    (fun a => intervalIntegral.integral_nonneg t.coe_nonneg (fun s _ => sq_nonneg _))
    (fun a => ?_) (hs N)
  have hf : Continuous (fun s : ℝ => (h a s.toNNReal) ^ 2) := by fun_prop
  exact intervalIntegral.integral_mono_interval le_rfl t.coe_nonneg hN
    (Eventually.of_forall (fun s => sq_nonneg _)) (hf.intervalIntegrable _ _)

theorem integral_spatial_sq_tsum [Countable ι]
    {h : ι → ℝ≥0 → ℝ} (hc : ∀ a, Continuous (h a))
    (hs : ∀ N : ℕ, Summable (fun a => ∫ s in (0 : ℝ)..(N : ℝ), (h a s.toNNReal) ^ 2))
    (t : ℝ≥0) :
    IntervalIntegrable (fun s : ℝ => ∑' a, (h a s.toNNReal) ^ 2) volume 0 (t : ℝ) ∧
      (∫ s in (0 : ℝ)..(t : ℝ), ∑' a, (h a s.toNNReal) ^ 2) =
        ∑' a, ∫ s in (0 : ℝ)..(t : ℝ), (h a s.toNNReal) ^ 2 := by
  have hi (a : ι) : Integrable (fun s : ℝ => (h a s.toNNReal) ^ 2)
      (volume.restrict (Set.Ioc (0 : ℝ) (t : ℝ))) := by
    have hf : Continuous (fun s : ℝ => (h a s.toNNReal) ^ 2) := by fun_prop
    exact (intervalIntegrable_iff_integrableOn_Ioc_of_le t.coe_nonneg).mp
      (hf.intervalIntegrable _ _)
  have hsum : Summable (fun a => ∫ s in Set.Ioc (0 : ℝ) (t : ℝ), (h a s.toNNReal) ^ 2) := by
    simpa only [intervalIntegral.integral_of_le t.coe_nonneg] using
      summable_integral_sq_of_integer hc hs t
  obtain ⟨_, hint, heq⟩ := NonnegativeSeriesL1.integrable_tsum_of_nonnegative
    hi (fun a s => sq_nonneg _) hsum
  exact ⟨(intervalIntegrable_iff_integrableOn_Ioc_of_le t.coe_nonneg).mpr hint,
    by simpa only [intervalIntegral.integral_of_le t.coe_nonneg] using heq⟩

theorem ae_spatialCompensator_eq_primitive [Countable ι]
    {H : ι → ℝ≥0 → Ω → ℝ}
    (hc : ∀ a, ∀ᵐ ω ∂P, Continuous (fun t => H a t ω))
    (hs : ∀ N : ℕ, ∀ᵐ ω ∂P,
      Summable (fun a => nonnegativeCompensator (H a) (N : ℝ≥0) ω)) :
    ∀ᵐ ω ∂P,
      (∀ t, spatialCompensator H t ω = nnrealTimePrimitive (spatialSquareDensity H) t ω) ∧
      Continuous (fun t => nnrealTimePrimitive (spatialSquareDensity H) t ω) ∧
      (∀ t : ℝ≥0, IntervalIntegrable (fun s : ℝ => spatialSquareDensity H s.toNNReal ω)
        volume 0 (t : ℝ)) := by
  filter_upwards [ae_all_iff.mpr hc, ae_all_iff.mpr hs] with ω hcω hsω
  have hsum (N : ℕ) : Summable (fun a => ∫ s in (0 : ℝ)..(N : ℝ), (H a s.toNNReal ω) ^ 2) := by
    simpa only [nonnegativeCompensator_eq_integral_of_continuous (hcω _),
      NNReal.coe_natCast] using hsω N
  have hi (t : ℝ≥0) := integral_spatial_sq_tsum hcω hsum t
  refine ⟨?_, ?_, fun t => (hi t).1⟩
  · intro t
    change (∑' a, nonnegativeCompensator (H a) t ω) =
      ∫ s in (0 : ℝ)..(t : ℝ), ∑' a, (H a s.toNNReal ω) ^ 2
    rw [(hi t).2]
    exact tsum_congr (fun a => nonnegativeCompensator_eq_integral_of_continuous (hcω a) t)
  · exact continuous_nnreal_primitive_of_integrable_horizons _
      (fun N => by simpa only [NNReal.coe_natCast, spatialSquareDensity] using (hi (N : ℝ≥0)).1)

theorem spatialSquareDensity_isStronglyProgressive [Countable ι]
    {F : Filtration ℝ≥0 mΩ} {H : ι → ℝ≥0 → Ω → ℝ}
    (hH : ∀ a, IsStronglyProgressive F (H a)) :
    IsStronglyProgressive F (spatialSquareDensity H) := by
  intro t
  have hm (a : ι) := (hH a t).pow 2
  let : MeasurableSpace Ω := F t
  exact StronglyMeasurable.tsum hm

theorem compensatedSquare_spatial_primitive [Countable ι]
    {F : Filtration ℝ≥0 mΩ} {H : ι → ℝ≥0 → Ω → ℝ} {Y : ℝ≥0 → Ω → ℝ}
    (hH : ∀ a, IsStronglyProgressive F (H a))
    (hc : ∀ a, ∀ᵐ ω ∂P, Continuous (fun t => H a t ω))
    (hs : ∀ N : ℕ, ∀ᵐ ω ∂P,
      Summable (fun a => nonnegativeCompensator (H a) (N : ℝ≥0) ω))
    (hY : StronglyAdapted F Y)
    (hQ : Martingale (fun t ω => Y t ω ^ 2 - spatialCompensator H t ω) F P) :
    Martingale (fun t ω => Y t ω ^ 2 - nnrealTimePrimitive (spatialSquareDensity H) t ω) F P := by
  apply hQ.congr (fun t => ((hY t).pow 2).sub
    (stronglyAdapted_nnrealTimePrimitive (spatialSquareDensity_isStronglyProgressive hH) t))
  intro t
  filter_upwards [ae_spatialCompensator_eq_primitive hc hs] with ω hω
  change Y t ω ^ 2 - spatialCompensator H t ω =
    Y t ω ^ 2 - nnrealTimePrimitive (spatialSquareDensity H) t ω
  rw [hω.1 t]

end Problem367.BrownianArrayFiltration

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Stochastic_StoppedIntegralAssociativity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped NNReal Topology

namespace Problem367.StoppedIntegralAssociativity

open BrownianGrid BrownianIntegralProcess

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}

theorem stoppedUniformSum_memLp [IsFiniteMeasure P]
    {M K : ℝ≥0 → Ω → ℝ} {F : Filtration ℝ≥0 mΩ}
    (hM2 : ∀ t, MemLp (M t) 2 P) (hK : StronglyAdapted F K)
    {D : ℝ} (hbK : ∀ᵐ ω ∂P, ∀ t, |K t ω| ≤ D)
    (T : ℝ≥0) (n : ℕ) (t : ℝ≥0) :
    MemLp (stoppedUniformSum M K T n t) 2 P := by
  apply memLp_finsetSum
  intro i hi
  exact BrownianGrid.memLp_compose_of_bounded
    ((hM2 (min t (uniformGrid T n (i + 1)))).sub (hM2 (min t (uniformGrid T n i))))
    ((hK _).mono (F.le _)).aestronglyMeasurable (hbK.mono (fun ω hω => hω _))

end Problem367.StoppedIntegralAssociativity

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Conditioning_CopyCompensatedSquare
attribute [-instance] _root_.OAI.Problem367.WienerSampler.pathMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped NNReal Topology

namespace Problem367.BrownianArrayFiltration

variable {Ω ι : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}

theorem compensatedSquare_of_spatial_integral_limits_oai
    [Countable ι] [IsProbabilityMeasure P]
    {F : Filtration ℝ≥0 mΩ} {B H I : ι → ℝ≥0 → Ω → ℝ}
    {Y : ℝ≥0 → Ω → ℝ}
    (hB : ∀ a, IsPreBrownianReal (B a) P)
    (hAd : ∀ a, StronglyAdapted F (B a))
    (hpast : ∀ s t, s ≤ t → Indep (MeasurableSpace.comap
      (fun ω a => B a t ω - B a s ω) inferInstance) (F s) P)
    (hind : ∀ s t, s ≤ t → Pairwise fun a b =>
      IndepFun (fun ω => B a t ω - B a s ω)
        (fun ω => B b t ω - B b s ω) P)
    (hBc : ∀ a, ∀ᵐ ω ∂P, Continuous (fun t => B a t ω))
    (hH : ∀ a, IsStronglyProgressive F (H a))
    (hc : ∀ a, ∀ᵐ ω ∂P, Continuous (fun t => H a t ω))
    {C : ι → ℝ} (hC : ∀ a, 0 ≤ C a)
    (hb : ∀ a, ∀ᵐ ω ∂P, ∀ t, |H a t ω| ≤ C a)
    (henergy : ∀ N : ℕ, Summable (fun a =>
      ∫ s in (0 : ℝ)..(N : ℝ), ∫ ω, H a s.toNNReal ω ^ 2 ∂P))
    (hI2 : ∀ a t, MemLp (I a t) 2 P)
    (hYad : StronglyAdapted F Y) (hY2 : ∀ t, MemLp (Y t) 2 P)
    (hlim : ∀ a (N : ℕ), 0 < N → ∀ t ≤ (N : ℝ≥0),
      Tendsto (fun n => ∫ ω,
        (BrownianIntegralProcess.stoppedUniformSum (B a) (H a) N n t ω -
          I a t ω) ^ 2 ∂P) atTop (𝓝 0))
    (hsum : ∀ t, HasSum (fun a => (hI2 a t).toLp (I a t))
      ((hY2 t).toLp (Y t))) :
    Martingale Y F P ∧
      Martingale (fun t ω => Y t ω ^ 2 -
        nnrealTimePrimitive (spatialSquareDensity H) t ω) F P := by
  obtain ⟨J, Z, hJ2, hZ2, hJ, hJlim, hZp, hZM, hZc, hZ0,
      hZiso, hZsum, hZmax, hZQ, hZA, hZseries⟩ :=
    exists_global_continuous_spatial_integral_compensatedSquare
      hB hAd hpast hind hBc (fun a => (hH a).stronglyAdapted)
      hc hC hb henergy
  have hIJ (a : ι) (t : ℝ≥0) : I a t =ᵐ[P] J a t := by
    obtain ⟨N, htN⟩ := exists_nat_gt (t : ℝ)
    have hN : 0 < N := by exact_mod_cast (t.coe_nonneg.trans_lt htN)
    have htN' : t ≤ (N : ℝ≥0) := by exact_mod_cast htN.le
    apply BrownianGrid.ae_eq_of_mean_square_limits
      (fun n => StoppedIntegralAssociativity.stoppedUniformSum_memLp
        (fun s => (hB a).isGaussianProcess.hasGaussianLaw_eval s |>.memLp_two)
        (hH a).stronglyAdapted (hb a) (N : ℝ≥0) n t)
      (hI2 a t) (hJ2 a t)
    · exact hlim a N hN t htN'
    · exact hJlim a N hN t htN'
  have hYZ (t : ℝ≥0) : Y t =ᵐ[P] Z t := by
    have heq : (fun a => (hI2 a t).toLp (I a t)) =
        (fun a => (hJ2 a t).toLp (J a t)) :=
      funext (fun a => MemLp.toLp_congr (hI2 a t) (hJ2 a t) (hIJ a t))
    have hs := hsum t
    rw [heq] at hs
    exact (MemLp.toLp_eq_toLp_iff (hY2 t) (hZ2 t)).mp (hs.unique (hZsum t))
  have hQ := compensatedSquare_spatial_primitive hH hc
    (fun N => hZseries (N : ℝ≥0)) hZM.stronglyAdapted hZQ
  refine ⟨hZM.congr hYad (fun t => (hYZ t).symm), ?_⟩
  apply hQ.congr (fun t => ((hYad t).pow 2).sub
    (stronglyAdapted_nnrealTimePrimitive (spatialSquareDensity_isStronglyProgressive hH) t))
  intro t
  filter_upwards [hYZ t] with ω hω
  exact congrArg (fun z => z ^ 2 - nnrealTimePrimitive (spatialSquareDensity H) t ω) hω.symm

end Problem367.BrownianArrayFiltration

end

end OAI
end

theorem solution.{u_1, u_2} : type_of% @OAI.Problem367.BrownianArrayFiltration.compensatedSquare_of_spatial_integral_limits_oai.{u_1, u_2} := @OAI.Problem367.BrownianArrayFiltration.compensatedSquare_of_spatial_integral_limits_oai.{u_1, u_2}
