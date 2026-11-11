-- Prove2me | solution 1 for OAI.Problem367.IsingJoinedResponseIntegrals.exists_integrals
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T01:47:25.829847+00:00
-- url     : https://prove2.me/submissions/cb2c44c7-4cd7-4b2a-8046-65a89a390597

import Mathlib
import Mathlib.MeasureTheory.Integral.Marginal
import Definitions.Def_FreeIsing
import Definitions.Def_Q243FI005
import Theorems.Thm_OAI_Problem367_BrownianArrayFiltration_compensatedSquare_of_spatial_integral_limits
import Theorems.Thm_OAI_Problem367_BrownianArrayFiltration_exists_global_continuous_spatial_integral_compensatedSquare
import Theorems.Thm_OAI_Problem367_IsingContinuousCopyCoefficients_response_continuous_ae
import Theorems.Thm_OAI_Problem367_IsingContinuousCopyCoefficients_response_row_energy

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

theorem integral_sq_mul_of_condExp_sq [IsFiniteMeasure μ]
    {m : MeasurableSpace Ω} (hm : m ≤ mΩ) {H D : Ω → ℝ} {v : ℝ}
    (hH : StronglyMeasurable[m] H)
    (hDsq : Integrable (fun ω => D ω ^ 2) μ)
    (hHDsq : Integrable (fun ω => (H ω * D ω) ^ 2) μ)
    (hvar : μ[(fun ω => D ω ^ 2) | m] =ᵐ[μ] fun _ => v) :
    ∫ ω, (H ω * D ω) ^ 2 ∂μ = v * ∫ ω, H ω ^ 2 ∂μ := by
  have hHsq : StronglyMeasurable[m] (fun ω => H ω ^ 2) := by
    simpa only [pow_two, Pi.mul_def] using hH.mul hH
  have hprod : Integrable ((fun ω => H ω ^ 2) * (fun ω => D ω ^ 2)) μ := by
    simpa only [Pi.mul_def, mul_pow] using hHDsq
  have hpull := condExp_mul_of_stronglyMeasurable_left hHsq hprod hDsq
  calc
    ∫ ω, (H ω * D ω) ^ 2 ∂μ =
        ∫ ω, μ[(fun ω => H ω ^ 2) * (fun ω => D ω ^ 2) | m] ω ∂μ := by
      simpa only [Pi.mul_def, mul_pow] using (integral_condExp hm).symm
    _ = ∫ ω, v * H ω ^ 2 ∂μ := by
      apply integral_congr_ae
      filter_upwards [hpull, hvar] with ω hp hv
      simp only [Pi.mul_apply] at hp
      rw [hp, hv, mul_comm]
    _ = v * ∫ ω, H ω ^ 2 ∂μ := integral_const_mul _ _

theorem predictable_increments_orthogonal [IsFiniteMeasure μ]
    (ℱ : Filtration ℕ mΩ) (H D : ℕ → Ω → ℝ)
    (hH : ∀ i, StronglyMeasurable[ℱ i] (H i))
    (hD : ∀ i, StronglyMeasurable[ℱ (i + 1)] (D i))
    (hDint : ∀ i, Integrable (D i) μ)
    (hHD : ∀ i, MemLp (fun ω => H i ω * D i ω) 2 μ)
    (hzero : ∀ i, μ[D i | ℱ i] =ᵐ[μ] 0)
    {i j : ℕ} (hij : i < j) :
    ∫ ω, (H i ω * D i ω) * (H j ω * D j ω) ∂μ = 0 := by
  have hcoeff : StronglyMeasurable[ℱ j]
      (fun ω => (H i ω * D i ω) * H j ω) := by
    simpa only [Pi.mul_def] using
      (((hH i).mono (ℱ.mono hij.le)).mul
        ((hD i).mono (ℱ.mono (Nat.succ_le_of_lt hij)))).mul (hH j)
  have hprod : Integrable
      ((fun ω => (H i ω * D i ω) * H j ω) * D j) μ := by
    simpa only [Pi.mul_def, mul_assoc] using (hHD i).integrable_mul (hHD j)
  simpa only [mul_assoc] using
    integral_mul_eq_zero_of_condExp_eq_zero (ℱ.le j) hcoeff (hDint j) hprod (hzero j)

theorem predictable_sum_isometry [IsFiniteMeasure μ]
    (ℱ : Filtration ℕ mΩ) (H D : ℕ → Ω → ℝ) (v : ℕ → ℝ)
    (hH : ∀ i, StronglyMeasurable[ℱ i] (H i))
    (hD : ∀ i, StronglyMeasurable[ℱ (i + 1)] (D i))
    (hD2 : ∀ i, MemLp (D i) 2 μ)
    (hHD : ∀ i, MemLp (fun ω => H i ω * D i ω) 2 μ)
    (hzero : ∀ i, μ[D i | ℱ i] =ᵐ[μ] 0)
    (hvar : ∀ i, μ[(fun ω => D i ω ^ 2) | ℱ i] =ᵐ[μ] fun _ => v i)
    (s : Finset ℕ) :
    ∫ ω, (∑ i ∈ s, H i ω * D i ω) ^ 2 ∂μ =
      ∑ i ∈ s, v i * ∫ ω, H i ω ^ 2 ∂μ := by
  have hint : ∀ i ∈ s, ∀ j ∈ s,
      Integrable (fun ω => (H i ω * D i ω) * (H j ω * D j ω)) μ := by
    intro i _ j _
    simpa only [Pi.mul_def] using (hHD i).integrable_mul (hHD j)
  have hDint : ∀ i, Integrable (D i) μ := fun i =>
    MemLp.integrable (by norm_num) (hD2 i)
  have horth : ∀ i ∈ s, ∀ j ∈ s, i ≠ j →
      ∫ ω, (H i ω * D i ω) * (H j ω * D j ω) ∂μ = 0 := by
    intro i _ j _ hij
    rcases lt_or_gt_of_ne hij with hij | hji
    · exact predictable_increments_orthogonal ℱ H D hH hD hDint hHD hzero hij
    · simpa only [mul_comm] using
        predictable_increments_orthogonal ℱ H D hH hD hDint hHD hzero hji
  rw [integral_sq_sum_of_orthogonal s (fun i ω => H i ω * D i ω) hint horth]
  apply Finset.sum_congr rfl
  intro i _
  exact integral_sq_mul_of_condExp_sq (ℱ.le i) (hH i)
    (hD2 i).integrable_sq (hHD i).integrable_sq (hvar i)

end Problem367.SimpleIntegral

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Brownian_FiltrationIntegral
attribute [-instance] _root_.OAI.Problem367.WienerSampler.pathMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace Problem367.BrownianFiltration

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
  {B : ℝ≥0 → Ω → ℝ} {F : Filtration ℝ≥0 mΩ}

theorem increment_condExp_zero
    (hB : IsPreBrownianReal B P) (hAd : StronglyAdapted F B)
    {s t : ℝ≥0}
    (hind : Indep
      (MeasurableSpace.comap (fun ω => B t ω - B s ω) inferInstance) (F s) P) :
    P[(fun ω => B t ω - B s ω) | F s] =ᵐ[P] fun _ => 0 := by
  let : IsProbabilityMeasure P := hB.isGaussianProcess.isProbabilityMeasure
  have hm : Measurable (fun ω => B t ω - B s ω) :=
    ((hAd t).mono (F.le t)).measurable.sub ((hAd s).mono (F.le s)).measurable
  have hce := condExp_indep_eq hm.comap_le (F.le s)
    (show StronglyMeasurable[MeasurableSpace.comap
      (fun ω => B t ω - B s ω) inferInstance] (fun ω => B t ω - B s ω) from
      (measurable_iff_comap_le.mpr le_rfl).stronglyMeasurable) hind
  have hmean : (∫ ω, B t ω - B s ω ∂P) = 0 := by
    rw [integral_sub (hB.integrable_eval t) (hB.integrable_eval s),
      hB.integral_eval, hB.integral_eval, sub_self]
  simpa only [hmean] using hce

theorem increment_sq_condExp
    (hB : IsPreBrownianReal B P) (hAd : StronglyAdapted F B)
    {s t : ℝ≥0} (hst : s ≤ t)
    (hind : Indep
      (MeasurableSpace.comap (fun ω => B t ω - B s ω) inferInstance) (F s) P) :
    P[(fun ω => (B t ω - B s ω) ^ 2) | F s] =ᵐ[P]
      fun _ => (t : ℝ) - (s : ℝ) := by
  let : IsProbabilityMeasure P := hB.isGaussianProcess.isProbabilityMeasure
  have hm : Measurable (fun ω => B t ω - B s ω) :=
    ((hAd t).mono (F.le t)).measurable.sub ((hAd s).mono (F.le s)).measurable
  have hd : StronglyMeasurable[MeasurableSpace.comap
      (fun ω => B t ω - B s ω) inferInstance] (fun ω => B t ω - B s ω) :=
    (measurable_iff_comap_le.mpr le_rfl).stronglyMeasurable
  have hce := condExp_indep_eq hm.comap_le (F.le s) (hd.pow 2) hind
  have hmean : (∫ ω, (B t ω - B s ω) ^ 2 ∂P) = (t : ℝ) - (s : ℝ) := by
    have h := preBrownian_integral_sq (hB.shift s) (t - s)
    simpa [add_tsub_cancel_of_le hst, NNReal.coe_sub hst] using h
  change P[(fun ω => (B t ω - B s ω) ^ 2) | F s] =ᵐ[P]
    fun _ => ∫ ω, (B t ω - B s ω) ^ 2 ∂P at hce
  simpa only [hmean] using hce

theorem predictable_sum_isometry
    (hB : IsPreBrownianReal B P) (hAd : StronglyAdapted F B)
    (hind : ∀ s t, s ≤ t → Indep
      (MeasurableSpace.comap (fun ω => B t ω - B s ω) inferInstance) (F s) P)
    (t : ℕ → ℝ≥0) (ht : Monotone t) (H : ℕ → Ω → ℝ)
    (hH : ∀ i, StronglyMeasurable[F (t i)] (H i))
    (hH2 : ∀ i, MemLp (H i) 2 P) (s : Finset ℕ) :
    (∫ ω, (∑ i ∈ s, H i ω * (B (t (i + 1)) ω - B (t i) ω)) ^ 2 ∂P) =
      ∑ i ∈ s, ((t (i + 1) : ℝ) - (t i : ℝ)) * ∫ ω, H i ω ^ 2 ∂P := by
  let : IsProbabilityMeasure P := hB.isGaussianProcess.isProbabilityMeasure
  let G : Filtration ℕ mΩ :=
    ⟨fun i => F (t i), fun _ _ hij => F.mono (ht hij), fun i => F.le (t i)⟩
  let D : ℕ → Ω → ℝ := fun i ω => B (t (i + 1)) ω - B (t i) ω
  have hD (i : ℕ) : StronglyMeasurable[G (i + 1)] (D i) :=
    (hAd (t (i + 1))).sub ((hAd (t i)).mono (F.mono (ht (Nat.le_succ i))))
  have hD2 (i : ℕ) : MemLp (D i) 2 P :=
    (hB.isGaussianProcess.hasGaussianLaw_eval (t (i + 1))).memLp_two.sub
      (hB.isGaussianProcess.hasGaussianLaw_eval (t i)).memLp_two
  exact SimpleIntegral.predictable_sum_isometry G H D
    (fun i => (t (i + 1) : ℝ) - (t i : ℝ)) hH hD hD2
    (fun i => predictable_mul_memLp_two hB
      (hind (t i) (t (i + 1)) (ht (Nat.le_succ i))) (hH i) (hH2 i))
    (fun i => increment_condExp_zero hB hAd
      (hind (t i) (t (i + 1)) (ht (Nat.le_succ i))))
    (fun i => increment_sq_condExp hB hAd (ht (Nat.le_succ i))
      (hind (t i) (t (i + 1)) (ht (Nat.le_succ i)))) s

end Problem367.BrownianFiltration

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Martingales_PredictableL2Completion
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators Topology NNReal

namespace Problem367.PredictableL2

theorem inner_toLp {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {f g : Ω → ℝ} (hf : MemLp f 2 μ) (hg : MemLp g 2 μ) :
    inner ℝ (hf.toLp f) (hg.toLp g) = ∫ ω, f ω * g ω ∂μ := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [hf.coeFn_toLp, hg.coeFn_toLp] with ω hfω hgω
  simp only [hfω, hgω, Real.inner_apply]

theorem norm_toLp_sq {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {f : Ω → ℝ} (hf : MemLp f 2 μ) :
    ‖hf.toLp f‖ ^ 2 = ∫ ω, f ω ^ 2 ∂μ := by
  rw [← real_inner_self_eq_norm_sq, inner_toLp]
  simp only [sq]

end Problem367.PredictableL2

end

end OAI
end

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

lemma uniformGrid_le_horizon (T : ℝ≥0) {n i : ℕ} (hn : 0 < n) (hi : i ≤ n) :
    uniformGrid T n i ≤ T := by
  simpa only [uniformGrid_end T hn] using uniformGrid_mono T n hi

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
-- module Solutions.Q243_FreeIsing.FreeIsing_Brownian_UniformIntegral
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped NNReal Topology

namespace Problem367.BrownianGrid

lemma norm_sq_L2_eq_integral {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    (f : Lp ℝ 2 P) : ‖f‖ ^ 2 = ∫ ω, (f ω) ^ 2 ∂P := by
  rw [← real_inner_self_eq_norm_sq, L2.inner_def]
  simp only [real_inner_self_eq_norm_sq, Real.norm_eq_abs, sq_abs]

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

theorem point_mem {T : ℝ} (hT : 0 ≤ T) {n i : ℕ} (hn : 0 < n) (hi : i ≤ n) :
    point T n i ∈ Icc 0 T := by
  constructor
  · dsimp [point] <;> positivity
  · exact (point_mono hT n hi).trans_eq (point_end T hn)

theorem error_le {f : ℝ → ℝ} (hf : Continuous f) {T ε : ℝ}
    (hT : 0 ≤ T) {n : ℕ} (hn : 0 < n)
    (hmod : ∀ i < n, ∀ x ∈ Icc (point T n i) (point T n (i + 1)),
      |f (point T n i) - f x| ≤ ε) :
    |sum f T n - ∫ x in (0 : ℝ)..T, f x| ≤ ε * T := by
  have hpart := intervalIntegral.sum_integral_adjacent_intervals
    (μ := volume) (a := point T n) (n := n) (fun i _ => hf.intervalIntegrable _ _)
  rw [point_zero, point_end T hn] at hpart
  have hcluster (i : ℕ) :
      (T / n) * f (point T n i) -
          (∫ x in point T n i..point T n (i + 1), f x) =
        ∫ x in point T n i..point T n (i + 1), f (point T n i) - f x := by
    rw [intervalIntegral.integral_sub intervalIntegrable_const (hf.intervalIntegrable _ _),
      intervalIntegral.integral_const, smul_eq_mul, point_step]
  have hdecomp : sum f T n - (∫ x in (0 : ℝ)..T, f x) =
      ∑ i ∈ Finset.range n,
        ∫ x in point T n i..point T n (i + 1), f (point T n i) - f x := by
    rw [sum, Finset.mul_sum, ← hpart, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl (fun i _ => hcluster i)
  rw [hdecomp]
  calc
    _ ≤ ∑ i ∈ Finset.range n,
        |∫ x in point T n i..point T n (i + 1), f (point T n i) - f x| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i ∈ Finset.range n, ε * (T / n) := by
      apply Finset.sum_le_sum
      intro i hi
      have hle := point_mono hT n (Nat.le_succ i)
      have hbound := intervalIntegral.norm_integral_le_of_norm_le_const
        (a := point T n i) (b := point T n (i + 1)) (C := ε)
        (f := fun x => f (point T n i) - f x) (fun x hx => ?_)
      · simpa only [Real.norm_eq_abs, point_step, abs_of_nonneg (div_nonneg hT
          (Nat.cast_nonneg n))] using hbound
      · rw [uIoc_of_le hle] at hx
        exact hmod i (Finset.mem_range.mp hi) x ⟨hx.1.le, hx.2⟩
    _ = ε * T := by
      simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hn)
      field_simp

theorem tendsto_sum {f : ℝ → ℝ} (hf : Continuous f) {T : ℝ} (hT : 0 ≤ T) :
    Tendsto (sum f T) atTop (𝓝 (∫ x in (0 : ℝ)..T, f x)) := by
  apply Metric.tendsto_atTop.mpr
  intro ε hε
  let η := ε / (T + 1)
  have hη : 0 < η := div_pos hε (by linarith)
  have hUC := isCompact_Icc.uniformContinuousOn_of_continuous
    (s := Icc (0 : ℝ) T) hf.continuousOn
  obtain ⟨δ, hδ, hδmod⟩ := Metric.uniformContinuousOn_iff.mp hUC η hη
  have hwidth : Tendsto (fun n : ℕ => T / (n : ℝ)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
  have hev : ∀ᶠ n : ℕ in atTop, T / (n : ℝ) < δ :=
    hwidth.eventually (gt_mem_nhds hδ)
  obtain ⟨N, hN⟩ := (hev.and (eventually_ge_atTop 1)).exists_forall_of_atTop
  refine ⟨N, ?_⟩
  intro n hn
  obtain ⟨hmesh, hnpos⟩ := hN n hn
  have hn' : 0 < n := hnpos
  have he := error_le hf hT hn' (ε := η) ?_
  · change |sum f T n - ∫ x in (0 : ℝ)..T, f x| < ε
    apply he.trans_lt
    change ε / (T + 1) * T < ε
    rw [div_mul_eq_mul_div]
    apply (div_lt_iff₀ (by linarith : 0 < T + 1)).mpr
    nlinarith
  · intro i hi x hx
    have hleft := point_mem hT hn' hi.le
    have hright := point_mem hT hn' (Nat.succ_le_of_lt hi)
    have hxT : x ∈ Icc (0 : ℝ) T := ⟨hleft.1.trans hx.1, hx.2.trans hright.2⟩
    have hdist : dist (point T n i) x < δ := by
      rw [Real.dist_eq, abs_of_nonpos (sub_nonpos.mpr hx.1)]
      have hstep := point_step T n i
      linarith [hx.2]
    exact (hδmod _ hleft x hxT hdist).le

theorem continuous_energy {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsFiniteMeasure P] {H : ℝ≥0 → Ω → ℝ}
    (hm : ∀ t, AEStronglyMeasurable (H t) P)
    (hc : ∀ᵐ ω ∂P, Continuous (fun t => H t ω))
    {C : ℝ} (hC : 0 ≤ C) (hb : ∀ᵐ ω ∂P, ∀ t, |H t ω| ≤ C) :
    Continuous (energy P H) := by
  apply continuous_of_dominated (bound := fun _ => C ^ 2)
  · intro t
    exact (hm t).pow 2
  · intro t
    filter_upwards [hb] with ω hω
    simpa only [Real.norm_eq_abs, abs_sq, sq_abs] using
      (sq_le_sq₀ (abs_nonneg _) hC).mpr (hω t)
  · exact integrable_const _
  · filter_upwards [hc] with ω hω
    exact hω.pow 2

theorem tendsto_energy_sum {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsFiniteMeasure P] {H : ℝ≥0 → Ω → ℝ}
    (hm : ∀ t, AEStronglyMeasurable (H t) P)
    (hc : ∀ᵐ ω ∂P, Continuous (fun t => H t ω))
    {C : ℝ} (hC : 0 ≤ C) (hb : ∀ᵐ ω ∂P, ∀ t, |H t ω| ≤ C)
    (T : ℝ≥0) :
    Tendsto (fun n : ℕ => ((T : ℝ) / n) *
      ∑ i ∈ Finset.range n,
        ∫ ω, (H ((i : ℝ≥0) * T / n) ω) ^ 2 ∂P)
      atTop (𝓝 (∫ t in (0 : ℝ)..(T : ℝ), ∫ ω, (H t.toNNReal ω) ^ 2 ∂P)) := by
  have hcont : Continuous (fun t : ℝ => energy P H t.toNNReal) :=
    (continuous_energy hm hc hC hb).comp (by fun_prop)
  have hlim := tendsto_sum hcont T.coe_nonneg
  convert hlim using 1
  all_goals try with_reducible_and_instances rfl
  funext n
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  congr 1
  funext ω
  congr 2
  apply NNReal.eq
  simp only [NNReal.coe_mul, NNReal.coe_div, NNReal.coe_natCast, point,
    Real.coe_toNNReal' ]
  rw [max_eq_left (by positivity)]
  ring
  all_goals rfl

end Problem367.EnergyRiemann

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Brownian_UniformIsometry
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped NNReal Topology

namespace Problem367.BrownianGrid

lemma uniformGrid_step (T : ℝ≥0) (n i : ℕ) :
    (uniformGrid T n (i + 1) : ℝ) - (uniformGrid T n i : ℝ) = (T : ℝ) / n := by
  simp only [uniformGrid, NNReal.coe_div, NNReal.coe_mul, NNReal.coe_natCast,
    Nat.cast_add, Nat.cast_one, NNReal.coe_add, NNReal.coe_one]
  ring

end Problem367.BrownianGrid

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Brownian_FiltrationUniformIntegral
attribute [-instance] _root_.OAI.Problem367.WienerSampler.pathMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped NNReal Topology

namespace Problem367.BrownianFiltrationGrid
open BrownianGrid

lemma coe_uniformSumLp
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {B : ℝ≥0 → Ω → ℝ} (hB : IsPreBrownianReal B P)
    {F : Filtration ℝ≥0 mΩ} (hAd : StronglyAdapted F B)
    (hind : ∀ s t, s ≤ t → Indep
      (MeasurableSpace.comap (fun ω => B t ω - B s ω) inferInstance) (F s) P) (H : ℝ≥0 → Ω → ℝ)
    (hH : StronglyAdapted (F) H)
    (hH2 : ∀ t, MemLp (H t) 2 P) (T : ℝ≥0) (n : ℕ) :
    (uniformSumLp hB hAd hind H hH hH2 T n : Ω → ℝ) =ᵐ[P] uniformSum B H T n :=
  (uniformSum_memLp hB hAd hind H hH hH2 T n).coeFn_toLp

theorem uniformSumLp_norm_sq
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {B : ℝ≥0 → Ω → ℝ} (hB : IsPreBrownianReal B P)
    {F : Filtration ℝ≥0 mΩ} (hAd : StronglyAdapted F B)
    (hind : ∀ s t, s ≤ t → Indep
      (MeasurableSpace.comap (fun ω => B t ω - B s ω) inferInstance) (F s) P) (H : ℝ≥0 → Ω → ℝ)
    (hH : StronglyAdapted (F) H)
    (hH2 : ∀ t, MemLp (H t) 2 P) (T : ℝ≥0) (n : ℕ) :
    ‖uniformSumLp hB hAd hind H hH hH2 T n‖ ^ 2 =
      ((T : ℝ) / n) * ∑ i ∈ Finset.range n, ∫ ω, (H (uniformGrid T n i) ω) ^ 2 ∂P := by
  calc
    _ = ∫ ω, (uniformSum B H T n ω) ^ 2 ∂P := by
      rw [norm_sq_L2_eq_integral]
      apply integral_congr_ae
      filter_upwards [coe_uniformSumLp hB hAd hind H hH hH2 T n] with ω hω
      rw [hω]
    _ = ∑ i ∈ Finset.range n,
        ((uniformGrid T n (i + 1) : ℝ) - (uniformGrid T n i : ℝ)) *
          ∫ ω, (H (uniformGrid T n i) ω) ^ 2 ∂P :=
      BrownianFiltration.predictable_sum_isometry hB hAd hind (uniformGrid T n) (uniformGrid_mono T n)
        (fun i => H (uniformGrid T n i)) (fun i => hH _) (fun i => hH2 _) (Finset.range n)
    _ = _ := by simp_rw [uniformGrid_step]; rw [← Finset.mul_sum]

theorem uniformSumLp_limit_isometry
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {B : ℝ≥0 → Ω → ℝ} (hB : IsPreBrownianReal B P)
    {F : Filtration ℝ≥0 mΩ} (hAd : StronglyAdapted F B)
    (hind : ∀ s t, s ≤ t → Indep
      (MeasurableSpace.comap (fun ω => B t ω - B s ω) inferInstance) (F s) P) (H : ℝ≥0 → Ω → ℝ)
    (hH : StronglyAdapted (F) H)
    (hH2 : ∀ t, MemLp (H t) 2 P)
    (hc : ∀ᵐ ω ∂P, Continuous (fun t => H t ω))
    {C : ℝ} (hC : 0 ≤ C) (hb : ∀ᵐ ω ∂P, ∀ t, |H t ω| ≤ C)
    (T : ℝ≥0) {I : Lp ℝ 2 P}
    (hI : Tendsto (uniformSumLp hB hAd hind H hH hH2 T) atTop (𝓝 I)) :
    (∫ ω, (I ω) ^ 2 ∂P) =
      ∫ t in (0 : ℝ)..(T : ℝ), ∫ ω, (H t.toNNReal ω) ^ 2 ∂P := by
  let : IsProbabilityMeasure P := hB.isGaussianProcess.isProbabilityMeasure
  have henergy := EnergyRiemann.tendsto_energy_sum
    (fun t => (hH2 t).aestronglyMeasurable) hc hC hb T
  have hnorm := hI.norm.pow 2
  have henergy' : Tendsto
      (fun n => ((T : ℝ) / n) * ∑ i ∈ Finset.range n,
        ∫ ω, (H (uniformGrid T n i) ω) ^ 2 ∂P) atTop (𝓝 (‖I‖ ^ 2)) := by
    apply hnorm.congr'
    exact Filter.Eventually.of_forall (uniformSumLp_norm_sq hB hAd hind H hH hH2 T)
  rw [← norm_sq_L2_eq_integral]
  exact tendsto_nhds_unique henergy' henergy

end Problem367.BrownianFiltrationGrid

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Brownian_ArrayFiltrationIntegral
attribute [-instance] _root_.OAI.Problem367.WienerSampler.pathMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal Topology BigOperators

namespace Problem367.BrownianArrayFiltration

variable {Ω ι : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
  {B : ι → ℝ≥0 → Ω → ℝ} {F : Filtration ℝ≥0 mΩ}

theorem coordinate_increment_indep_past {s t : ℝ≥0}
    (hind : Indep
      (MeasurableSpace.comap (fun ω a => B a t ω - B a s ω) inferInstance) (F s) P)
    (a : ι) :
    Indep (MeasurableSpace.comap (fun ω => B a t ω - B a s ω) inferInstance)
      (F s) P := by
  have hm : Measurable[
      MeasurableSpace.comap (fun ω a => B a t ω - B a s ω) inferInstance]
      (fun ω => B a t ω - B a s ω) :=
    (measurable_pi_apply a).comp (show Measurable[
      MeasurableSpace.comap (fun ω a => B a t ω - B a s ω) inferInstance]
      (fun ω a => B a t ω - B a s ω) from measurable_iff_comap_le.mpr le_rfl)
  exact indep_of_indep_of_le_left hind hm.comap_le

end Problem367.BrownianArrayFiltration

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Stochastic_IntegralAssociativityLimit
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory Filter
open scoped Topology NNReal

namespace Problem367.SimpleIntegral

section Limits

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {μ : Measure Ω}

theorem tendsto_toLp_iff_meanSquare {α : Type*} {l : Filter α}
    {X : α → Ω → ℝ} (hX : ∀ a, MemLp (X a) 2 μ)
    {Y : Ω → ℝ} (hY : MemLp Y 2 μ) :
    Tendsto (fun a => (hX a).toLp (X a)) l (𝓝 (hY.toLp Y)) ↔
      Tendsto (fun a => ∫ ω, (X a ω - Y ω) ^ 2 ∂μ) l (𝓝 0) := by
  have heq (a : α) :
      ‖(hX a).toLp (X a) - hY.toLp Y‖ ^ 2 =
        ∫ ω, (X a ω - Y ω) ^ 2 ∂μ := by
    rw [← MemLp.toLp_sub (hX a) hY]
    exact PredictableL2.norm_toLp_sq ((hX a).sub hY)
  rw [tendsto_iff_norm_sub_tendsto_zero]
  constructor
  · intro h
    simpa only [heq, zero_pow (by decide : (2 : ℕ) ≠ 0)] using h.pow 2
  · intro h
    have hs := Real.continuous_sqrt.continuousAt.tendsto.comp h
    simpa only [Function.comp_def, ← heq, Real.sqrt_sq (norm_nonneg _),
      Real.sqrt_zero] using hs

end Limits
end Problem367.SimpleIntegral

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Brownian_ArrayCrossIsometry
attribute [-instance] _root_.OAI.Problem367.WienerSampler.pathMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped NNReal Topology BigOperators

namespace Problem367

namespace BrownianGrid

theorem uniformSum_sub_coeff {Ω : Type*} (B H K : ℝ≥0 → Ω → ℝ)
    (T : ℝ≥0) (n : ℕ) (ω : Ω) :
    uniformSum B (fun t ω => H t ω - K t ω) T n ω =
      uniformSum B H T n ω - uniformSum B K T n ω := by
  simp only [uniformSum, integralSum, sub_mul, Finset.sum_sub_distrib]

end BrownianGrid

namespace SimpleIntegral

theorem meanSquare_limit_sub {Ω α : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {l : Filter α} {X Y : α → Ω → ℝ} {I J : Ω → ℝ}
    (hX : ∀ a, MemLp (X a) 2 P) (hY : ∀ a, MemLp (Y a) 2 P)
    (hI : MemLp I 2 P) (hJ : MemLp J 2 P)
    (hx : Tendsto (fun a => ∫ ω, (X a ω - I ω) ^ 2 ∂P) l (𝓝 0))
    (hy : Tendsto (fun a => ∫ ω, (Y a ω - J ω) ^ 2 ∂P) l (𝓝 0)) :
    Tendsto (fun a => ∫ ω, ((X a ω - Y a ω) - (I ω - J ω)) ^ 2 ∂P)
      l (𝓝 0) := by
  apply (tendsto_toLp_iff_meanSquare (fun a => (hX a).sub (hY a)) (hI.sub hJ)).mp
  change Tendsto (fun a => (hX a).toLp (X a) - (hY a).toLp (Y a)) l
    (𝓝 (hI.toLp I - hJ.toLp J))
  exact ((tendsto_toLp_iff_meanSquare hX hI).mpr hx).sub
    ((tendsto_toLp_iff_meanSquare hY hJ).mpr hy)

end SimpleIntegral

namespace BrownianFiltrationGrid

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {B : ℝ≥0 → Ω → ℝ} {F : Filtration ℝ≥0 mΩ}

theorem uniform_meanSquare_limit_isometry
    (hB : IsPreBrownianReal B P) (hAd : StronglyAdapted F B)
    (hind : ∀ s t, s ≤ t → Indep
      (MeasurableSpace.comap (fun ω => B t ω - B s ω) inferInstance) (F s) P)
    (H : ℝ≥0 → Ω → ℝ) (hH : StronglyAdapted F H)
    (hc : ∀ᵐ ω ∂P, Continuous (fun t => H t ω))
    {C : ℝ} (hC : 0 ≤ C) (hb : ∀ᵐ ω ∂P, ∀ t, |H t ω| ≤ C)
    (T : ℝ≥0) {I : Ω → ℝ} (hI : MemLp I 2 P)
    (happrox : Tendsto (fun n => ∫ ω,
      (BrownianGrid.uniformSum B H T n ω - I ω) ^ 2 ∂P) atTop (𝓝 0)) :
    (∫ ω, I ω ^ 2 ∂P) =
      ∫ t in (0 : ℝ)..(T : ℝ), ∫ ω, H t.toNNReal ω ^ 2 ∂P := by
  let : IsProbabilityMeasure P := hB.isGaussianProcess.isProbabilityMeasure
  have hH2 (t : ℝ≥0) : MemLp (H t) 2 P := by
    apply MemLp.of_bound ((hH t).mono (F.le t)).aestronglyMeasurable C
    filter_upwards [hb] with ω hω
    simpa only [Real.norm_eq_abs] using hω t
  have hlim := (SimpleIntegral.tendsto_toLp_iff_meanSquare
    (uniformSum_memLp hB hAd hind H hH hH2 T) hI).mpr happrox
  have hiso := uniformSumLp_limit_isometry hB hAd hind H hH hH2 hc hC hb T hlim
  calc
    (∫ ω, I ω ^ 2 ∂P) = ∫ ω, (hI.toLp I ω) ^ 2 ∂P := by
      apply integral_congr_ae
      filter_upwards [hI.coeFn_toLp] with ω hω
      rw [hω]
    _ = _ := hiso

theorem uniform_meanSquare_difference_isometry
    (hB : IsPreBrownianReal B P) (hAd : StronglyAdapted F B)
    (hind : ∀ s t, s ≤ t → Indep
      (MeasurableSpace.comap (fun ω => B t ω - B s ω) inferInstance) (F s) P)
    (H K : ℝ≥0 → Ω → ℝ) (hH : StronglyAdapted F H) (hK : StronglyAdapted F K)
    (hcH : ∀ᵐ ω ∂P, Continuous (fun t => H t ω))
    (hcK : ∀ᵐ ω ∂P, Continuous (fun t => K t ω))
    {C D : ℝ} (hC : 0 ≤ C) (hD : 0 ≤ D)
    (hbH : ∀ᵐ ω ∂P, ∀ t, |H t ω| ≤ C)
    (hbK : ∀ᵐ ω ∂P, ∀ t, |K t ω| ≤ D)
    (T : ℝ≥0) {I J : Ω → ℝ} (hI : MemLp I 2 P) (hJ : MemLp J 2 P)
    (haI : Tendsto (fun n => ∫ ω,
      (BrownianGrid.uniformSum B H T n ω - I ω) ^ 2 ∂P) atTop (𝓝 0))
    (haJ : Tendsto (fun n => ∫ ω,
      (BrownianGrid.uniformSum B K T n ω - J ω) ^ 2 ∂P) atTop (𝓝 0)) :
    (∫ ω, (I ω - J ω) ^ 2 ∂P) =
      ∫ t in (0 : ℝ)..(T : ℝ), ∫ ω, (H t.toNNReal ω - K t.toNNReal ω) ^ 2 ∂P := by
  let : IsProbabilityMeasure P := hB.isGaussianProcess.isProbabilityMeasure
  have hH2 (t : ℝ≥0) : MemLp (H t) 2 P := by
    apply MemLp.of_bound ((hH t).mono (F.le t)).aestronglyMeasurable C
    filter_upwards [hbH] with ω hω
    simpa only [Real.norm_eq_abs] using hω t
  have hK2 (t : ℝ≥0) : MemLp (K t) 2 P := by
    apply MemLp.of_bound ((hK t).mono (F.le t)).aestronglyMeasurable D
    filter_upwards [hbK] with ω hω
    simpa only [Real.norm_eq_abs] using hω t
  refine uniform_meanSquare_limit_isometry hB hAd hind (fun t ω => H t ω - K t ω)
    (fun t => (hH t).sub (hK t)) ?_ (add_nonneg hC hD) ?_ T (hI.sub hJ) ?_
  · filter_upwards [hcH, hcK] with ω hωH hωK
    exact hωH.sub hωK
  · filter_upwards [hbH, hbK] with ω hωH hωK
    intro t
    exact (abs_sub _ _).trans (add_le_add (hωH t) (hωK t))
  · simpa only [BrownianGrid.uniformSum_sub_coeff, Pi.sub_apply] using
      SimpleIntegral.meanSquare_limit_sub
        (uniformSum_memLp hB hAd hind H hH hH2 T)
        (uniformSum_memLp hB hAd hind K hK hK2 T) hI hJ haI haJ

end BrownianFiltrationGrid

end Problem367

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Brownian_ContinuousIntegral
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal Topology

namespace Problem367.BrownianIntegralProcess

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}

omit mΩ in
theorem stoppedUniformSum_terminal (B H : ℝ≥0 → Ω → ℝ) (T : ℝ≥0) (n : ℕ) :
    stoppedUniformSum B H T n T = BrownianGrid.uniformSum B H T n := by
  funext ω
  unfold stoppedUniformSum BrownianGrid.uniformSum BrownianGrid.integralSum
  apply Finset.sum_congr rfl
  intro i hi
  have hin : i < n := Finset.mem_range.mp hi
  have hn : 0 < n := lt_of_le_of_lt (Nat.zero_le i) hin
  have ha := BrownianGrid.uniformGrid_le_horizon T hn hin.le
  have hb := BrownianGrid.uniformGrid_le_horizon T hn hin
  simp only [StoppedSimpleIntegral.intervalSum, min_eq_right ha, min_eq_right hb]

end Problem367.BrownianIntegralProcess

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Brownian_RowComparisonConstruction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal Topology BigOperators

namespace Problem367.SimpleIntegral

theorem summable_integral_sq_sub {Ω ι : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {I J : ι → Ω → ℝ}
    (hI : ∀ a, MemLp (I a) 2 P) (hJ : ∀ a, MemLp (J a) 2 P)
    (hsI : Summable fun a => ∫ ω, I a ω ^ 2 ∂P)
    (hsJ : Summable fun a => ∫ ω, J a ω ^ 2 ∂P) :
    Summable fun a => ∫ ω, (I a ω - J a ω) ^ 2 ∂P := by
  apply Summable.of_nonneg_of_le
    (fun a => integral_nonneg fun ω => sq_nonneg _) _
    ((hsI.mul_left 2).add (hsJ.mul_left 2))
  intro a
  simpa using BrownianGrid.integral_sq_sub_le_two (hI a) (hJ a)
    (MemLp.zero' : MemLp (fun _ : Ω => (0 : ℝ)) 2 P)

end Problem367.SimpleIntegral

namespace Problem367.BrownianArrayFiltration

variable {Ω ι : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {B : ι → ℝ≥0 → Ω → ℝ} {F : Filtration ℝ≥0 mΩ}
    (hB : ∀ a, IsPreBrownianReal (B a) P)
    (hAd : ∀ a, StronglyAdapted F (B a))
    (hind : ∀ s t, s ≤ t → Indep
      (MeasurableSpace.comap (fun ω a => B a t ω - B a s ω) inferInstance) (F s) P)
    (H K : ι → ℝ≥0 → Ω → ℝ)
    (hH : ∀ a, StronglyAdapted F (H a)) (hK : ∀ a, StronglyAdapted F (K a))
    (hcH : ∀ a, ∀ᵐ ω ∂P, Continuous (fun t => H a t ω))
    (hcK : ∀ a, ∀ᵐ ω ∂P, Continuous (fun t => K a t ω))
    (C D : ι → ℝ) (hC : ∀ a, 0 ≤ C a) (hD : ∀ a, 0 ≤ D a)
    (hbH : ∀ a, ∀ᵐ ω ∂P, ∀ t, |H a t ω| ≤ C a)
    (hbK : ∀ a, ∀ᵐ ω ∂P, ∀ t, |K a t ω| ≤ D a)
    (T : ℝ≥0)
    (heH : Summable fun a =>
      ∫ t in (0 : ℝ)..(T : ℝ), ∫ ω, H a t.toNNReal ω ^ 2 ∂P)
    (heK : Summable fun a =>
      ∫ t in (0 : ℝ)..(T : ℝ), ∫ ω, K a t.toNNReal ω ^ 2 ∂P)

include hB hAd hind hH hK hcH hcK hC hD hbH hbK heH heK in

theorem summable_difference_energy_of_row_energies
    {I J : ι → Ω → ℝ}
    (hI : ∀ a, MemLp (I a) 2 P) (hJ : ∀ a, MemLp (J a) 2 P)
    (haI : ∀ a, Tendsto (fun n => ∫ ω,
      (BrownianGrid.uniformSum (B a) (H a) T n ω - I a ω) ^ 2 ∂P) atTop (𝓝 0))
    (haJ : ∀ a, Tendsto (fun n => ∫ ω,
      (BrownianGrid.uniformSum (B a) (K a) T n ω - J a ω) ^ 2 ∂P) atTop (𝓝 0)) :
    Summable fun a => ∫ t in (0 : ℝ)..(T : ℝ),
      ∫ ω, (H a t.toNNReal ω - K a t.toNNReal ω) ^ 2 ∂P := by
  have hi (a : ι) (s t : ℝ≥0) (hst : s ≤ t) :=
    coordinate_increment_indep_past (hind s t hst) a
  have hIE (a : ι) := BrownianFiltrationGrid.uniform_meanSquare_limit_isometry
    (hB a) (hAd a) (hi a) (H a) (hH a) (hcH a) (hC a) (hbH a) T (hI a) (haI a)
  have hJE (a : ι) := BrownianFiltrationGrid.uniform_meanSquare_limit_isometry
    (hB a) (hAd a) (hi a) (K a) (hK a) (hcK a) (hD a) (hbK a) T (hJ a) (haJ a)
  have hs := SimpleIntegral.summable_integral_sq_sub hI hJ
    (by simpa only [hIE] using heH) (by simpa only [hJE] using heK)
  have hDE (a : ι) := BrownianFiltrationGrid.uniform_meanSquare_difference_isometry
    (hB a) (hAd a) (hi a) (H a) (K a) (hH a) (hK a) (hcH a) (hcK a)
    (hC a) (hD a) (hbH a) (hbK a) T (hI a) (hJ a) (haI a) (haJ a)
  simpa only [hDE] using hs

end Problem367.BrownianArrayFiltration

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Estimates_FilteredFutureIndependence
attribute [-instance] _root_.OAI.Problem367.WienerSampler.pathMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory

namespace Problem367.FilteredFutureIndependence

variable {Ω A B C : Type*} [mΩ : MeasurableSpace Ω]
  [MeasurableSpace A] [MeasurableSpace B] [MeasurableSpace C]
  {P : Measure Ω} [IsProbabilityMeasure P]

theorem indepFun_pair_right {X : Ω → A} {Y : Ω → B} {Z : Ω → C}
    (hX : Measurable X) (hY : Measurable Y) (hZ : Measurable Z)
    (hXY : IndepFun X Y P) (hXYZ : IndepFun (fun ω => (X ω, Y ω)) Z P) :
    IndepFun X (fun ω => (Y ω, Z ω)) P := by
  have hYZ : IndepFun Y Z P := hXYZ.comp measurable_snd measurable_id
  rw [indepFun_iff_map_prod_eq_prod_map_map hX.aemeasurable
    (hY.prodMk hZ).aemeasurable]
  have h := congrArg (fun μ : Measure ((A × B) × C) =>
    μ.map MeasurableEquiv.prodAssoc)
    (hXYZ.map_prod_eq_prod_map_map (hX.prodMk hY).aemeasurable hZ.aemeasurable)
  rw [Measure.map_map MeasurableEquiv.prodAssoc.measurable
    ((hX.prodMk hY).prodMk hZ),
    hXY.map_prod_eq_prod_map_map hX.aemeasurable hY.aemeasurable, Measure.prodAssoc_prod] at h
  rw [hYZ.map_prod_eq_prod_map_map hY.aemeasurable hZ.aemeasurable]
  exact h

variable {T E : Type*} [LinearOrder T] [MeasurableSpace E]
  [AddCommGroup E] [MeasurableAdd₂ E] [MeasurableSub₂ E]
  {F : Filtration T mΩ} {X : T → Ω → E}

theorem indepFun_finite_future
    (hX : ∀ t, Measurable[F t] (X t))
    (hind : ∀ s t, s ≤ t →
      Indep (MeasurableSpace.comap (fun ω => X t ω - X s ω) inferInstance) (F s) P)
    (s : T) {Y : Ω → A} (hY : Measurable[F s] Y)
    (I : Finset (Set.Ici s)) :
    IndepFun Y (fun ω (t : I) => X t.val.val ω - X s ω) P := by
  classical
  have hXm (t : T) : Measurable (X t) := (hX t).mono (F.le t) le_rfl
  have hYm : Measurable Y := hY.mono (F.le s) le_rfl
  induction I using Finset.induction_on_max with
  | empty =>
      have heq : (fun ω (t : (∅ : Finset (Set.Ici s))) =>
          X t.val.val ω - X s ω) = (fun _ : Ω => fun _ :
            (∅ : Finset (Set.Ici s)) => (0 : E)) := by
        funext ω t
        exact False.elim (Finset.notMem_empty _ t.property)
      rw [heq]
      exact indepFun_const_right Y _
  | insert t I hlt ih =>
      rcases I.eq_empty_or_nonempty with rfl | hI
      · have hi : IndepFun Y (fun ω => X t.val ω - X s ω) P :=
          indep_of_indep_of_le_left (hind s t.val t.property).symm hY.comap_le
        have hcomp := hi.comp measurable_id
          (Measurable.of_eval (fun _ : ↥(insert t (∅ : Finset (Set.Ici s))) =>
            measurable_id))
        change IndepFun Y (fun ω (_ : ↥(insert t (∅ : Finset (Set.Ici s)))) =>
          X t.val ω - X s ω) P at hcomp
        convert hcomp using 1
        all_goals try with_reducible_and_instances rfl
        funext ω u
        have hu : u.val = t :=
          (Finset.mem_insert.mp u.property).resolve_right (Finset.notMem_empty _)
        simp only [hu]
      · let r : Set.Ici s := I.max' hI
        have hrI : r ∈ I := Finset.max'_mem I hI
        have hrt : r.val ≤ t.val := (hlt r hrI).le
        have hIr (u : I) : u.val.val ≤ r.val := I.le_max' u.val u.property
        let V : Ω → (I → E) := fun ω u => X u.val.val ω - X s ω
        let D : Ω → E := fun ω => X t.val ω - X r.val ω
        have hV : Measurable[F r.val] V := by
          let : MeasurableSpace Ω := F r.val
          exact Measurable.of_eval (fun index : I =>
            ((hX index.val.val).mono (F.mono (hIr index)) le_rfl).sub
              ((hX s).mono (F.mono r.property) le_rfl))
        have hYV : Measurable[F r.val] (fun ω => (Y ω, V ω)) :=
          (hY.mono (F.mono r.property) le_rfl).prodMk hV
        have hYVD : IndepFun (fun ω => (Y ω, V ω)) D P :=
          indep_of_indep_of_le_left (hind r.val t.val hrt).symm hYV.comap_le
        have hvd := indepFun_pair_right hYm (hV.mono (F.le r.val) le_rfl)
          ((hXm t.val).sub (hXm r.val)) ih hYVD
        let assemble : (I → E) × E → (↥(insert t I) → E) := fun q u =>
          if h : u.val = t then q.1 ⟨r, hrI⟩ + q.2
          else q.1 ⟨u.val, (Finset.mem_insert.mp u.property).resolve_left h⟩
        have ha : Measurable assemble := by
          apply Measurable.of_eval
          intro u
          dsimp [assemble]
          split_ifs
          · exact ((measurable_pi_apply _).comp measurable_fst).add measurable_snd
          · exact (measurable_pi_apply _).comp measurable_fst
        have hh := hvd.comp measurable_id ha
        change IndepFun Y (fun ω => assemble (V ω, D ω)) P at hh
        convert hh using 1
        all_goals try with_reducible_and_instances rfl
        funext ω u
        dsimp [assemble, V, D]
        split_ifs with hu
        · rw [hu]
          abel
        · rfl

theorem indepFun_future
    (hX : ∀ t, Measurable[F t] (X t))
    (hind : ∀ s t, s ≤ t →
      Indep (MeasurableSpace.comap (fun ω => X t ω - X s ω) inferInstance) (F s) P)
    (s : T) {Y : Ω → A} (hY : Measurable[F s] Y) :
    IndepFun Y (fun ω (t : Set.Ici s) => X t.val ω - X s ω) P := by
  exact IndepFun.indepFun_process (P := P)
    (Y := fun (t : Set.Ici s) ω => X t.val ω - X s ω)
    (hY.mono (F.le s) le_rfl)
    (fun (t : Set.Ici s) => ((hX t.val).mono (F.le t.val) le_rfl).sub
      ((hX s).mono (F.le s) le_rfl))
    (indepFun_finite_future hX hind s hY)

theorem indep_future
    (hX : ∀ t, Measurable[F t] (X t))
    (hind : ∀ s t, s ≤ t →
      Indep (MeasurableSpace.comap (fun ω => X t ω - X s ω) inferInstance) (F s) P)
    (s : T) :
    Indep (F s) (MeasurableSpace.comap
      (fun ω (t : Set.Ici s) => X t.val ω - X s ω) inferInstance) P := by
  let : MeasurableSpace Ω := F s
  have h := indepFun_future (mΩ := mΩ) hX hind s (Y := id)
    (show Measurable[F s, F s] (id : Ω → Ω) from measurable_id)
  change Indep ((F s).comap id) _ P at h
  simpa only [MeasurableSpace.comap_id] using h

end Problem367.FilteredFutureIndependence

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Estimates_KernelCompatibility
attribute [-instance] _root_.OAI.Problem367.WienerSampler.pathMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace Problem367.KernelCompatibility

variable {P F X : Type*} [MeasurableSpace P] [MeasurableSpace F] [MeasurableSpace X]

theorem map_compProd_comap {W : Type*} [MeasurableSpace W]
    (mu : Measure W) [SFinite mu] (f : W → P) (hf : Measurable f)
    (kappa : Kernel P X) [IsSFiniteKernel kappa] :
    (mu ⊗ₘ kappa.comap f hf).map (Prod.map f id) = mu.map f ⊗ₘ kappa := by
  apply Measure.ext_of_lintegral
  intro g hg
  rw [lintegral_map hg (by fun_prop),
    Measure.lintegral_compProd (by fun_prop), Measure.lintegral_compProd hg,
    lintegral_map hg.lintegral_kernel_prod_right' hf]
  rfl

theorem map_compProd_of_kernel_map_ae {W O : Type*}
    [MeasurableSpace W] [MeasurableSpace O]
    (mu : Measure W) [SFinite mu] (f : W → P) (hf : Measurable f)
    (g : O → X) (hg : Measurable g)
    (eta : Kernel W O) [IsSFiniteKernel eta]
    (kappa : Kernel P X) [IsSFiniteKernel kappa]
    (h : (fun w => (eta.map g) w) =ᵐ[mu] (fun w => kappa (f w))) :
    (mu ⊗ₘ eta).map (Prod.map f g) = mu.map f ⊗ₘ kappa := by
  have h' : eta.map g =ᵐ[mu] kappa.comap f hf := h
  calc
    (mu ⊗ₘ eta).map (Prod.map f g) =
        (mu ⊗ₘ eta.map g).map (Prod.map f id) := by
      rw [Measure.compProd_map hg, Measure.map_map (by fun_prop) (by fun_prop)]
      rfl
    _ = (mu ⊗ₘ kappa.comap f hf).map (Prod.map f id) := by
      rw [Measure.compProd_congr h']
    _ = mu.map f ⊗ₘ kappa := map_compProd_comap mu f hf kappa

theorem map_reorder_compProd (mu : Measure P) (nu : Measure F)
    [SFinite mu] [SFinite nu] (kappa : Kernel P X) [IsSFiniteKernel kappa] :
    ((mu.prod nu) ⊗ₘ kappa.comap Prod.fst measurable_fst).map
        (fun q : (P × F) × X => ((q.1.1, q.2), q.1.2)) =
      (mu ⊗ₘ kappa).prod nu := by
  apply Measure.ext_of_lintegral
  intro f hf
  rw [lintegral_map hf (by fun_prop)]
  rw [Measure.lintegral_compProd (by fun_prop)]
  have hF : Measurable (fun q : (P × F) × X => f ((q.1.1, q.2), q.1.2)) :=
    hf.comp (by fun_prop)
  rw [lintegral_prod _ hF.lintegral_kernel_prod_right'.aemeasurable]
  rw [lintegral_prod _ hf.aemeasurable]
  rw [Measure.lintegral_compProd (by fun_prop)]
  apply lintegral_congr
  intro p
  simp only [Kernel.comap_apply]
  exact lintegral_lintegral_swap (by fun_prop)

theorem map_conditionalCopies_of_jointLaw {W O : Type*}
    [MeasurableSpace W] [MeasurableSpace O]
    (rho : Measure W) [SFinite rho]
    (mu : Measure P) (nu : Measure F) [SFinite mu] [SFinite nu]
    (p : W → P) (hp : Measurable p) (future : W → F) (hf : Measurable future)
    (hlaw : rho.map (fun w => (p w, future w)) = mu.prod nu)
    (eta : Kernel W O) [IsSFiniteKernel eta]
    (past : O → X) (hpast : Measurable past)
    (kappa : Kernel P X) [IsSFiniteKernel kappa]
    (h : (fun w => (eta.map past) w) =ᵐ[rho] (fun w => kappa (p w))) :
    (rho ⊗ₘ (eta ×ₖ eta)).map
        (fun q : W × (O × O) =>
          ((p q.1, (past q.2.1, past q.2.2)), future q.1)) =
      (mu ⊗ₘ (kappa ×ₖ kappa)).prod nu := by
  have hcopy : (fun w => ((eta ×ₖ eta).map (Prod.map past past)) w) =ᵐ[rho]
      (fun w => ((kappa ×ₖ kappa).comap Prod.fst measurable_fst :
        Kernel (P × F) (X × X)) (p w, future w)) := by
    filter_upwards [h] with w hw
    rw [← Kernel.map_prod_map eta eta hpast hpast]
    simp only [Kernel.prod_apply, Kernel.comap_apply, hw]
  have hpush := map_compProd_of_kernel_map_ae rho (fun w => (p w, future w))
    (hp.prodMk hf) (Prod.map past past) (hpast.prodMap hpast)
    (eta ×ₖ eta) ((kappa ×ₖ kappa).comap Prod.fst measurable_fst) hcopy
  have hm := congrArg (fun m : Measure ((P × F) × (X × X)) =>
    m.map (fun q => ((q.1.1, q.2), q.1.2))) hpush
  rw [Measure.map_map (by fun_prop) (by fun_prop), hlaw,
    map_reorder_compProd mu nu (kappa ×ₖ kappa)] at hm
  simpa [Function.comp_def, Prod.map] using hm

theorem indepFun_of_joint_product {W : Type*} [MeasurableSpace W]
    (rho : Measure W) [IsFiniteMeasure rho]
    (mu : Measure P) (nu : Measure F)
    [IsProbabilityMeasure mu] [IsProbabilityMeasure nu]
    (p : W → P) (hp : Measurable p) (future : W → F) (hf : Measurable future)
    (hlaw : rho.map (fun w => (p w, future w)) = mu.prod nu) :
    IndepFun p future rho := by
  have hplaw : rho.map p = mu := by
    have hh := congrArg (fun m : Measure (P × F) => m.map Prod.fst) hlaw
    rw [Measure.map_map measurable_fst (hp.prodMk hf)] at hh
    simpa [Function.comp_def] using hh
  have hflaw : rho.map future = nu := by
    have hh := congrArg (fun m : Measure (P × F) => m.map Prod.snd) hlaw
    rw [Measure.map_map measurable_snd (hp.prodMk hf)] at hh
    simpa [Function.comp_def] using hh
  apply (indepFun_iff_map_prod_eq_prod_map_map hp.aemeasurable hf.aemeasurable).2
  rw [hplaw, hflaw]
  exact hlaw

theorem indepFun_future_conditionalCopies_of_jointLaw {W O : Type*}
    [MeasurableSpace W] [MeasurableSpace O]
    (rho : Measure W) [IsProbabilityMeasure rho]
    (mu : Measure P) (nu : Measure F)
    [IsProbabilityMeasure mu] [IsProbabilityMeasure nu]
    (p : W → P) (hp : Measurable p) (future : W → F) (hf : Measurable future)
    (hlaw : rho.map (fun w => (p w, future w)) = mu.prod nu)
    (eta : Kernel W O) [IsMarkovKernel eta]
    (past : O → X) (hpast : Measurable past)
    (kappa : Kernel P X) [IsMarkovKernel kappa]
    (h : (fun w => (eta.map past) w) =ᵐ[rho] (fun w => kappa (p w))) :
    IndepFun (fun q : W × (O × O) => (p q.1, (past q.2.1, past q.2.2)))
      (fun q => future q.1) (rho ⊗ₘ (eta ×ₖ eta)) := by
  apply indepFun_of_joint_product (rho ⊗ₘ (eta ×ₖ eta))
    (mu ⊗ₘ (kappa ×ₖ kappa)) nu _ (by fun_prop) _ (by fun_prop)
  exact map_conditionalCopies_of_jointLaw rho mu nu p hp future hf hlaw
    eta past hpast kappa h

theorem exists_past_kernel_of_indep_of_embedding {W O : Type*}
    [MeasurableSpace W] [MeasurableSpace O]
    [StandardBorelSpace X] [Nonempty X]
    (rho : Measure W) [IsProbabilityMeasure rho]
    (mu : Measure P) (nu : Measure F)
    [IsProbabilityMeasure mu] [IsProbabilityMeasure nu]
    (p : W → P) (hp : Measurable p) (future : W → F) (hf : Measurable future)
    (hsplit : MeasurableEmbedding (fun w => (p w, future w)))
    (hlaw : rho.map (fun w => (p w, future w)) = mu.prod nu)
    (eta : Kernel W O) [IsMarkovKernel eta]
    (past : O → X) (hpast : Measurable past)
    (hind : IndepFun (fun q : W × O => (p q.1, past q.2))
      (fun q => future q.1) (rho ⊗ₘ eta)) :
    ∃ kappa : Kernel P X, IsMarkovKernel kappa ∧
      (fun w => (eta.map past) w) =ᵐ[rho] (fun w => kappa (p w)) := by
  let joint := rho ⊗ₘ eta
  let lam := joint.map (fun q : W × O => (p q.1, past q.2))
  have hbase : joint.map Prod.fst = rho := Measure.fst_compProd _ _
  have hplaw : rho.map p = mu := by
    have h := congrArg (fun m : Measure (P × F) => m.map Prod.fst) hlaw
    rw [Measure.map_map measurable_fst (hp.prodMk hf)] at h
    simpa [Function.comp_def] using h
  have hflaw : rho.map future = nu := by
    have h := congrArg (fun m : Measure (P × F) => m.map Prod.snd) hlaw
    rw [Measure.map_map measurable_snd (hp.prodMk hf)] at h
    simpa [Function.comp_def] using h
  have hfirst : lam.fst = mu := by
    change (joint.map (fun q : W × O => (p q.1, past q.2))).map Prod.fst = mu
    rw [Measure.map_map measurable_fst (by fun_prop)]
    change joint.map (p ∘ Prod.fst) = mu
    rw [← Measure.map_map hp measurable_fst, hbase, hplaw]
  have hfuture : joint.map (fun q : W × O => future q.1) = nu := by
    change joint.map (future ∘ Prod.fst) = nu
    rw [← Measure.map_map hf measurable_fst, hbase, hflaw]
  let kappa : Kernel P X := lam.condKernel
  have hdis : mu ⊗ₘ kappa = lam := by
    rw [← hfirst]
    exact Measure.disintegrate lam lam.condKernel
  have horiginal : joint.map (fun q : W × O =>
      ((p q.1, past q.2), future q.1)) = lam.prod nu := by
    rw [hind.map_prod_eq_prod_map_map (by fun_prop) (by fun_prop)]
    change lam.prod (joint.map (fun q : W × O => future q.1)) = lam.prod nu
    rw [hfuture]
  have hobs : (rho ⊗ₘ eta.map past).map
      (fun q : W × X => ((p q.1, q.2), future q.1)) = lam.prod nu := by
    rw [Measure.compProd_map hpast, Measure.map_map (by fun_prop) (by fun_prop)]
    exact horiginal
  have htransport : (rho ⊗ₘ kappa.comap p hp).map
      (Prod.map (fun w => (p w, future w)) id) =
      rho.map (fun w => (p w, future w)) ⊗ₘ
        kappa.comap Prod.fst measurable_fst :=
    map_compProd_comap rho (fun w => (p w, future w)) (hp.prodMk hf)
      (kappa.comap Prod.fst measurable_fst)
  have hnew : (rho ⊗ₘ kappa.comap p hp).map
      (fun q : W × X => ((p q.1, q.2), future q.1)) = lam.prod nu := by
    have h := congrArg (fun m : Measure ((P × F) × X) =>
      m.map (reorderEquiv : ((P × F) × X) ≃ᵐ ((P × X) × F))) htransport
    rw [Measure.map_map (reorderEquiv.measurable) (by fun_prop), hlaw] at h
    change (rho ⊗ₘ kappa.comap p hp).map
      (fun q : W × X => ((p q.1, q.2), future q.1)) =
      ((mu.prod nu) ⊗ₘ kappa.comap Prod.fst measurable_fst).map
        (fun q : (P × F) × X => ((q.1.1, q.2), q.1.2)) at h
    rw [map_reorder_compProd, hdis] at h
    exact h
  have hemb : MeasurableEmbedding (fun q : W × X => ((p q.1, q.2), future q.1)) :=
    reorderEquiv.measurableEmbedding.comp (hsplit.prodMap MeasurableEmbedding.id)
  have heq : rho ⊗ₘ eta.map past = rho ⊗ₘ kappa.comap p hp :=
    hemb.map_injective (hobs.trans hnew.symm)
  exact ⟨kappa, (by first | exact Measure.isProbabilityMeasure_map (by first | exact hpast.aemeasurable | (apply Measurable.aemeasurable; apply measurable_past <;> assumption)) | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)), Kernel.ae_eq_of_compProd_eq heq⟩

theorem indepFun_future_conditionalCopies_of_embedding {W O : Type*}
    [MeasurableSpace W] [MeasurableSpace O]
    [StandardBorelSpace X] [Nonempty X]
    (rho : Measure W) [IsProbabilityMeasure rho]
    (mu : Measure P) (nu : Measure F)
    [IsProbabilityMeasure mu] [IsProbabilityMeasure nu]
    (p : W → P) (hp : Measurable p) (future : W → F) (hf : Measurable future)
    (hsplit : MeasurableEmbedding (fun w => (p w, future w)))
    (hlaw : rho.map (fun w => (p w, future w)) = mu.prod nu)
    (eta : Kernel W O) [IsMarkovKernel eta]
    (past : O → X) (hpast : Measurable past)
    (hind : IndepFun (fun q : W × O => (p q.1, past q.2))
      (fun q => future q.1) (rho ⊗ₘ eta)) :
    IndepFun (fun q : W × (O × O) => (p q.1, (past q.2.1, past q.2.2)))
      (fun q => future q.1) (rho ⊗ₘ (eta ×ₖ eta)) := by
  obtain ⟨kappa, hkappa, h⟩ := exists_past_kernel_of_indep_of_embedding
    rho mu nu p hp future hf hsplit hlaw eta past hpast hind
  let := hkappa
  exact indepFun_future_conditionalCopies_of_jointLaw rho mu nu p hp future hf hlaw
    eta past hpast kappa h

theorem indepFun_future_conditionalCopies_of_reconstructible_split {W O : Type*}
    [MeasurableSpace W] [MeasurableSpace O]
    [StandardBorelSpace X] [Nonempty X]
    (rho : Measure W) [IsProbabilityMeasure rho]
    (p : W → P) (hp : Measurable p) (future : W → F) (hf : Measurable future)
    (hsplit : MeasurableEmbedding (fun w => (p w, future w)))
    (eta : Kernel W O) [IsMarkovKernel eta]
    (past : O → X) (hpast : Measurable past)
    (hind : IndepFun (fun q : W × O => (p q.1, past q.2))
      (fun q => future q.1) (rho ⊗ₘ eta)) :
    IndepFun (fun q : W × (O × O) => (p q.1, (past q.2.1, past q.2.2)))
      (fun q => future q.1) (rho ⊗ₘ (eta ×ₖ eta)) := by
  have hbaseind : IndepFun (fun q : W × O => p q.1)
      (fun q => future q.1) (rho ⊗ₘ eta) := hind.comp measurable_fst measurable_id
  have hlaw := hbaseind.map_prod_eq_prod_map_map (by fun_prop) (by fun_prop)
  change (rho ⊗ₘ eta).map ((fun w => (p w, future w)) ∘ Prod.fst) =
    ((rho ⊗ₘ eta).map (p ∘ Prod.fst)).prod
      ((rho ⊗ₘ eta).map (future ∘ Prod.fst)) at hlaw
  rw [← Measure.map_map (hp.prodMk hf) measurable_fst,
    ← Measure.map_map hp measurable_fst, ← Measure.map_map hf measurable_fst] at hlaw
  change ((rho ⊗ₘ eta).fst.map (fun w => (p w, future w))) =
    ((rho ⊗ₘ eta).fst.map p).prod ((rho ⊗ₘ eta).fst.map future) at hlaw
  rw [Measure.fst_compProd] at hlaw
  haveI : IsProbabilityMeasure (rho.map p) := Measure.isProbabilityMeasure_map hp.aemeasurable
  haveI : IsProbabilityMeasure (rho.map future) := Measure.isProbabilityMeasure_map hf.aemeasurable
  exact indepFun_future_conditionalCopies_of_embedding rho (rho.map p) (rho.map future)
    p hp future hf hsplit hlaw eta past hpast hind

end Problem367.KernelCompatibility

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Estimates_ContinuousModification
attribute [-instance] _root_.OAI.Problem367.WienerSampler.pathMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology

namespace Problem367
namespace ContinuousModification

variable {T Ω : Type*}

theorem isStronglyProgressive_sampledLimit [Preorder T] [MeasurableSpace T]
    [mΩ : MeasurableSpace Ω] (ℱ : Filtration T mΩ)
    {q : T → ℕ → T} {F : T → Ω → ℝ}
    (hF : ∀ n, IsStronglyProgressive ℱ (fun t ω => F (q t n) ω)) :
    IsStronglyProgressive ℱ (sampledLimit q F) := by
  intro t
  let : MeasurableSpace Ω := ℱ t
  exact StronglyMeasurable.limUnder (fun n => hF n t)

end ContinuousModification
end Problem367

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Posterior_ContinuousObservationHistory
attribute [-instance] _root_.OAI.Problem367.IsingConditionalCopyBounds.graphLaw_isProbabilityMeasure _root_.OAI.Problem367.IsingObservationFactor.copies_probability _root_.OAI.Problem367.IsingObservationFactor.kernel_markov _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_observationLaw_probability _root_.OAI.Problem367.IsingObservationInnovation.observationLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace Problem367.ContinuousObservationHistory

open WienerSampler

variable {ι : Type*}

theorem measurable_stoppedArray_of_eval {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (s : ℝ≥0) (F : Ω → ι → Path)
    (hF : ∀ i t, t ≤ s → Measurable (fun ω => F ω i t)) :
    Measurable (fun ω => stoppedArray s (F ω)) := by
  apply Measurable.of_eval
  intro i
  apply measurable_path_of_eval
  intro t
  exact hF i (min t s) (min_le_right t s)

end Problem367.ContinuousObservationHistory

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Conditioning_ConstructedConditionalCopies
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace Problem367.ConstructedConditionalCopies

open WienerSampler ContinuousObservationHistory

theorem indepFun_map_of_comp {Ω Z A B : Type*}
    [MeasurableSpace Ω] [MeasurableSpace Z] [MeasurableSpace A] [MeasurableSpace B]
    {P : Measure Ω} [IsProbabilityMeasure P]
    {z : Ω → Z} (hz : Measurable z) {f : Z → A} {g : Z → B}
    (hf : Measurable f) (hg : Measurable g)
    (hind : IndepFun (f ∘ z) (g ∘ z) P) : IndepFun f g (P.map z) := by
  let : IsProbabilityMeasure (P.map z) := by first | exact Measure.isProbabilityMeasure_map (by first | exact hz.aemeasurable) | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)
  rw [indepFun_iff_map_prod_eq_prod_map_map hf.aemeasurable hg.aemeasurable]
  rw [Measure.map_map (hf.prodMk hg) hz, Measure.map_map hf hz, Measure.map_map hg hz]
  exact hind.map_prod_eq_prod_map_map (hf.comp hz).aemeasurable (hg.comp hz).aemeasurable

end Problem367.ConstructedConditionalCopies

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Gaussian_ContinuousNoiseSplit
attribute [-instance] _root_.OAI.Problem367.IsingConditionalCopyBounds.graphLaw_isProbabilityMeasure _root_.OAI.Problem367.IsingObservationFactor.copies_probability _root_.OAI.Problem367.IsingObservationFactor.kernel_markov _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_observationLaw_probability _root_.OAI.Problem367.IsingObservationInnovation.observationLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace Problem367.ContinuousNoiseSplit

open WienerSampler ContinuousObservationHistory

theorem measurable_futurePath (s : ℝ≥0) : Measurable (futurePath s) := by
  apply measurable_path_of_eval
  intro t
  exact (continuous_eval_const (s + t)).measurable.sub (continuous_eval_const s).measurable

variable {ι : Type*}

theorem measurable_futureArray (s : ℝ≥0) : Measurable (futureArray (ι := ι) s) :=
  Measurable.of_eval fun i => (measurable_futurePath s).comp (measurable_pi_apply i)

theorem injective_split (s : ℝ≥0) : Function.Injective
    (fun f : ι → Path => (stoppedArray s f, futureArray s f)) := by
  intro f g h
  have hp := congrArg Prod.fst h
  have hf := congrArg Prod.snd h
  funext i
  apply ContinuousMap.ext
  intro t
  have hs : f i s = g i s := by
    have hh := congrArg (fun a : ι → Path => a i s) hp
    simpa only [stoppedArray, stoppedPath_apply, min_self] using hh
  by_cases hts : t ≤ s
  · have hh := congrArg (fun a : ι → Path => a i t) hp
    simpa only [stoppedArray, stoppedPath_apply, min_eq_left hts] using hh
  · have hst : s ≤ t := (lt_of_not_ge hts).le
    have hh := congrArg (fun a : ι → Path => a i (t - s)) hf
    simp only [futureArray, futurePath_apply, add_tsub_cancel_of_le hst, hs] at hh
    linarith

theorem measurableEmbedding_split [Countable ι] (s : ℝ≥0) : MeasurableEmbedding
    (fun f : ι → Path => (stoppedArray s f, futureArray s f)) :=
  ((measurable_stoppedArray s).prodMk (measurable_futureArray s)).measurableEmbedding
    (injective_split s)

theorem indepFun_future_conditionalCopies [Countable ι]
    {O X : Type*} [MeasurableSpace O] [MeasurableSpace X]
    [StandardBorelSpace X] [Nonempty X]
    (s : ℝ≥0) (rho : Measure (ι → Path)) [IsProbabilityMeasure rho]
    (eta : Kernel (ι → Path) O) [IsMarkovKernel eta]
    (past : O → X) (hpast : Measurable past)
    (hind : IndepFun (fun q : (ι → Path) × O => (stoppedArray s q.1, past q.2))
      (fun q => futureArray s q.1) (rho ⊗ₘ eta)) :
    IndepFun (fun q : (ι → Path) × (O × O) =>
      (stoppedArray s q.1, (past q.2.1, past q.2.2)))
      (fun q => futureArray s q.1) (rho ⊗ₘ (eta ×ₖ eta)) :=
  KernelCompatibility.indepFun_future_conditionalCopies_of_reconstructible_split
    rho (stoppedArray s) (measurable_stoppedArray s)
    (futureArray s) (measurable_futureArray s) (measurableEmbedding_split s)
    eta past hpast hind

end Problem367.ContinuousNoiseSplit

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Stochastic_ContinuousCopyBrownian
attribute [-instance] _root_.OAI.Problem367.IsingConditionalCopyBounds.graphLaw_isProbabilityMeasure _root_.OAI.Problem367.IsingObservationFactor.copies_probability _root_.OAI.Problem367.IsingObservationFactor.kernel_markov _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_observationLaw_probability _root_.OAI.Problem367.IsingObservationInnovation.observationLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace Problem367.ContinuousCopyBrownian

open WienerSampler ContinuousObservationHistory ContinuousNoiseSplit

variable {ι : Type*}

theorem isBrownian_commonNoise
    (i : ι) (rho : Measure (ι → Path)) [IsProbabilityMeasure rho]
    (hB : IsPreBrownianReal (fun t (w : ι → Path) => w i t) rho)
    (eta : Kernel (ι → Path) (ι → Path)) [IsMarkovKernel eta] :
    IsBrownianReal (fun t (q : Joint (ι := ι)) => q.1 i t) (rho ⊗ₘ (eta ×ₖ eta)) := by
  have hmp : MeasurePreserving (Prod.fst : Joint (ι := ι) → (ι → Path))
      (rho ⊗ₘ (eta ×ₖ eta)) rho := ⟨measurable_fst, Measure.fst_compProd _ _⟩
  exact ⟨⟨fun I => (hB.hasLaw I).comp hmp.hasLaw⟩,
    Filter.Eventually.of_forall (fun q => (q.1 i).continuous)⟩

end Problem367.ContinuousCopyBrownian

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Conditioning_ConstructedContinuousCopies
attribute [-instance] _root_.OAI.Problem367.IsingConditionalCopyBounds.graphLaw_isProbabilityMeasure _root_.OAI.Problem367.IsingObservationFactor.copies_probability _root_.OAI.Problem367.IsingObservationFactor.kernel_markov _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_observationLaw_probability _root_.OAI.Problem367.IsingObservationInnovation.observationLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace Problem367.ConstructedContinuousCopies

open WienerSampler ContinuousObservationHistory ContinuousNoiseSplit

variable {ι Ω : Type*} [mΩ : MeasurableSpace Ω]

theorem measurable_futureArray_of_eval (s : ℝ≥0) (W : Ω → ι → Path)
    (hW : ∀ i t, Measurable (fun ω => W ω i (s + t) - W ω i s)) :
    Measurable (fun ω => futureArray s (W ω)) := by
  apply Measurable.of_eval
  intro i
  apply measurable_path_of_eval
  intro t
  exact hW i t

theorem indepFun_continuous_future
    (P : Measure Ω) [IsProbabilityMeasure P] (F : Filtration ℝ≥0 mΩ)
    (W Y : Ω → ι → Path)
    (hW : ∀ i t, Measurable[F t] (fun ω => W ω i t))
    (hY : ∀ i t, Measurable[F t] (fun ω => Y ω i t))
    (hind : ∀ s t, s ≤ t → Indep
      (MeasurableSpace.comap (fun ω i => W ω i t - W ω i s) inferInstance) (F s) P)
    (s : ℝ≥0) :
    IndepFun (fun ω => (stoppedArray s (W ω), stoppedArray s (Y ω)))
      (fun ω => futureArray s (W ω)) P := by
  let X : ℝ≥0 → Ω → ι → ℝ := fun t ω i => W ω i t
  have hX (t : ℝ≥0) : Measurable[F t] (X t) := by
    let : MeasurableSpace Ω := F t
    exact Measurable.of_eval fun i => hW i t
  let mFuture := MeasurableSpace.comap
    (fun ω (t : Set.Ici s) => X t ω - X s ω) inferInstance
  have hRaw : @Measurable Ω (Set.Ici s → ι → ℝ) mFuture inferInstance
      (fun ω t => X t ω - X s ω) := comap_measurable _
  have hFut : @Measurable Ω (ι → Path) mFuture inferInstance
      (fun ω => futureArray s (W ω)) :=
    measurable_futureArray_of_eval (mΩ := mFuture) s W (fun i t =>
      (measurable_pi_apply i).comp
        ((measurable_pi_apply (⟨s + t, by change s ≤ s + t; exact le_self_add⟩ : Set.Ici s)).comp hRaw))
  have hPast : Measurable[F s]
      (fun ω => (stoppedArray s (W ω), stoppedArray s (Y ω))) :=
    (measurable_stoppedArray_of_eval (mΩ := F s) s W
      (fun i t ht => (hW i t).mono (F.mono ht) le_rfl)).prodMk
      (measurable_stoppedArray_of_eval (mΩ := F s) s Y
        (fun i t ht => (hY i t).mono (F.mono ht) le_rfl))
  have hi : Indep (F s) mFuture P :=
    FilteredFutureIndependence.indep_future (mΩ := mΩ) (P := P) hX hind s
  exact indep_of_indep_of_le (μ := P) hi hPast.comap_le hFut.comap_le

end Problem367.ConstructedContinuousCopies

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Conditioning_ContinuousCopyIndependence
attribute [-instance] _root_.OAI.Problem367.IsingConditionalCopyBounds.graphLaw_isProbabilityMeasure _root_.OAI.Problem367.IsingObservationFactor.copies_probability _root_.OAI.Problem367.IsingObservationFactor.kernel_markov _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_observationLaw_probability _root_.OAI.Problem367.IsingObservationInnovation.observationLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace Problem367.ContinuousCopyBrownian

open WienerSampler ContinuousObservationHistory ContinuousNoiseSplit

variable {ι : Type*}

theorem measurable_commonNoise_joinedFiltration (t : ℝ≥0) :
    Measurable[joinedFiltration (ι := ι) t]
      (fun q : Joint (ι := ι) => fun i => q.1 i t) := by
  change Measurable[pastSpace (ι := ι) t] _
  have hh : Measurable[pastSpace (ι := ι) t] (history (ι := ι) t) :=
    comap_measurable _
  let : MeasurableSpace (Joint (ι := ι)) := pastSpace (ι := ι) t
  apply Measurable.of_eval
  intro i
  have hm := (continuous_eval_const t).measurable.comp
    ((measurable_pi_apply i).comp (measurable_fst.comp hh))
  simpa only [Function.comp_def, history, stoppedArray, stoppedPath_apply, min_self] using hm

theorem indep_increment_joinedFiltration [Countable ι]
    (rho : Measure (ι → Path)) [IsProbabilityMeasure rho]
    (eta : Kernel (ι → Path) (ι → Path)) [IsMarkovKernel eta]
    {s t : ℝ≥0} (hst : s ≤ t)
    (hind : IndepFun (fun q : (ι → Path) × (ι → Path) =>
      (stoppedArray s q.1, stoppedArray s q.2))
      (fun q => futureArray s q.1) (rho ⊗ₘ eta)) :
    Indep (MeasurableSpace.comap
      (fun q : Joint (ι := ι) => fun i => q.1 i t - q.1 i s) inferInstance)
      (joinedFiltration s) (rho ⊗ₘ (eta ×ₖ eta)) := by
  have hcopy := ContinuousNoiseSplit.indepFun_future_conditionalCopies s rho eta
    (stoppedArray s) (measurable_stoppedArray s) hind
  have heval : Measurable (fun w : ι → Path => fun i => w i (t - s)) :=
    Measurable.of_eval fun i =>
      (continuous_eval_const (t - s)).measurable.comp (measurable_pi_apply i)
  have hi := hcopy.symm.comp heval measurable_id
  change IndepFun (fun q : Joint (ι := ι) => fun i => q.1 i t - q.1 i s)
    (fun q => (stoppedArray s q.1, (stoppedArray s q.2.1, stoppedArray s q.2.2)))
      (rho ⊗ₘ (eta ×ₖ eta))
  simpa only [Function.comp_def, id_eq, futureArray, futurePath_apply,
    add_tsub_cancel_of_le hst] using hi

end Problem367.ContinuousCopyBrownian

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

theorem difference_compensatedSquare_of_spatial_integral_limits
    [Countable ι] [IsProbabilityMeasure P]
    {F : Filtration ℝ≥0 mΩ} {B H K I J : ι → ℝ≥0 → Ω → ℝ}
    {Y Z : ℝ≥0 → Ω → ℝ}
    (hB : ∀ a, IsPreBrownianReal (B a) P)
    (hAd : ∀ a, StronglyAdapted F (B a))
    (hpast : ∀ s t, s ≤ t → Indep (MeasurableSpace.comap
      (fun ω a => B a t ω - B a s ω) inferInstance) (F s) P)
    (hind : ∀ s t, s ≤ t → Pairwise fun a b =>
      IndepFun (fun ω => B a t ω - B a s ω)
        (fun ω => B b t ω - B b s ω) P)
    (hBc : ∀ a, ∀ᵐ ω ∂P, Continuous (fun t => B a t ω))
    (hH : ∀ a, IsStronglyProgressive F (H a))
    (hK : ∀ a, IsStronglyProgressive F (K a))
    (hcH : ∀ a, ∀ᵐ ω ∂P, Continuous (fun t => H a t ω))
    (hcK : ∀ a, ∀ᵐ ω ∂P, Continuous (fun t => K a t ω))
    {C D : ι → ℝ} (hC : ∀ a, 0 ≤ C a) (hD : ∀ a, 0 ≤ D a)
    (hbH : ∀ a, ∀ᵐ ω ∂P, ∀ t, |H a t ω| ≤ C a)
    (hbK : ∀ a, ∀ᵐ ω ∂P, ∀ t, |K a t ω| ≤ D a)
    (heH : ∀ N : ℕ, Summable (fun a =>
      ∫ s in (0 : ℝ)..(N : ℝ), ∫ ω, H a s.toNNReal ω ^ 2 ∂P))
    (heK : ∀ N : ℕ, Summable (fun a =>
      ∫ s in (0 : ℝ)..(N : ℝ), ∫ ω, K a s.toNNReal ω ^ 2 ∂P))
    (hI2 : ∀ a t, MemLp (I a t) 2 P) (hJ2 : ∀ a t, MemLp (J a t) 2 P)
    (hYad : StronglyAdapted F Y) (hZad : StronglyAdapted F Z)
    (hY2 : ∀ t, MemLp (Y t) 2 P) (hZ2 : ∀ t, MemLp (Z t) 2 P)
    (hlimI : ∀ a (N : ℕ), 0 < N → ∀ t ≤ (N : ℝ≥0),
      Tendsto (fun n => ∫ ω,
        (BrownianIntegralProcess.stoppedUniformSum (B a) (H a) N n t ω -
          I a t ω) ^ 2 ∂P) atTop (𝓝 0))
    (hlimJ : ∀ a (N : ℕ), 0 < N → ∀ t ≤ (N : ℝ≥0),
      Tendsto (fun n => ∫ ω,
        (BrownianIntegralProcess.stoppedUniformSum (B a) (K a) N n t ω -
          J a t ω) ^ 2 ∂P) atTop (𝓝 0))
    (hsY : ∀ t, HasSum (fun a => (hI2 a t).toLp (I a t))
      ((hY2 t).toLp (Y t)))
    (hsZ : ∀ t, HasSum (fun a => (hJ2 a t).toLp (J a t))
      ((hZ2 t).toLp (Z t))) :
    Martingale (fun t ω => Y t ω - Z t ω) F P ∧
      Martingale (fun t ω => (Y t ω - Z t ω) ^ 2 -
        nnrealTimePrimitive
          (spatialSquareDensity (fun a t ω => H a t ω - K a t ω)) t ω) F P := by
  have hc (a : ι) : ∀ᵐ ω ∂P, Continuous (fun t => H a t ω - K a t ω) := by
    filter_upwards [hcH a, hcK a] with ω hω kω
    exact hω.sub kω
  have hb (a : ι) : ∀ᵐ ω ∂P, ∀ t, |H a t ω - K a t ω| ≤ C a + D a := by
    filter_upwards [hbH a, hbK a] with ω hω kω
    exact fun t => (abs_sub _ _).trans (add_le_add (hω t) (kω t))
  have he (N : ℕ) : Summable (fun a => ∫ s in (0 : ℝ)..(N : ℝ),
      ∫ ω, (H a s.toNNReal ω - K a s.toNNReal ω) ^ 2 ∂P) := by
    by_cases hN : 0 < N
    · apply summable_difference_energy_of_row_energies hB hAd hpast H K
        (fun a => (hH a).stronglyAdapted) (fun a => (hK a).stronglyAdapted)
        hcH hcK C D hC hD hbH hbK (N : ℝ≥0) (heH N) (heK N)
        (fun a => hI2 a N) (fun a => hJ2 a N)
      · intro a
        simpa only [BrownianIntegralProcess.stoppedUniformSum_terminal] using
          hlimI a N hN N le_rfl
      · intro a
        simpa only [BrownianIntegralProcess.stoppedUniformSum_terminal] using
          hlimJ a N hN N le_rfl
    · have hn : N = 0 := Nat.eq_zero_of_not_pos hN
      simp only [hn, Nat.cast_zero, intervalIntegral.integral_same]
      exact summable_zero
  apply compensatedSquare_of_spatial_integral_limits hB hAd hpast hind hBc
    (fun a t => (hH a t).sub (hK a t)) hc (fun a => add_nonneg (hC a) (hD a)) hb he
    (fun a t => (hI2 a t).sub (hJ2 a t))
    (fun t => (hYad t).sub (hZad t)) (fun t => (hY2 t).sub (hZ2 t))
  · intro a N hN t htN
    have hM2 (s : ℝ≥0) := (hB a).isGaussianProcess.hasGaussianLaw_eval s |>.memLp_two
    have h := SimpleIntegral.meanSquare_limit_sub
      (fun n => StoppedIntegralAssociativity.stoppedUniformSum_memLp
        hM2 (hH a).stronglyAdapted (hbH a) N n t)
      (fun n => StoppedIntegralAssociativity.stoppedUniformSum_memLp
        hM2 (hK a).stronglyAdapted (hbK a) N n t)
      (hI2 a t) (hJ2 a t) (hlimI a N hN t htN) (hlimJ a N hN t htN)
    have heq (n : ℕ) (ω : Ω) :
        BrownianIntegralProcess.stoppedUniformSum (B a)
          (fun s ω => H a s ω - K a s ω) N n t ω =
        BrownianIntegralProcess.stoppedUniformSum (B a) (H a) N n t ω -
          BrownianIntegralProcess.stoppedUniformSum (B a) (K a) N n t ω := by
      simp only [BrownianIntegralProcess.stoppedUniformSum,
        StoppedSimpleIntegral.intervalSum, sub_mul, Finset.sum_sub_distrib]
    simpa only [heq, Pi.sub_apply] using h
  · intro t
    exact (hsY t).sub (hsZ t)

end Problem367.BrownianArrayFiltration

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Conditioning_GaussianVector
attribute [-instance] _root_.OAI.Problem367.WienerSampler.pathMeasurableSpace _root_.OAI.Problem367.reducedTailFintype _root_.OAI.Problem367.treeBallFintype _root_.OAI.Problem367.treeShellFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped NNReal RealInnerProductSpace

namespace Problem367.ConditionalGaussianVector

variable {Ω : Type*} {m : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω]

section ArbitraryArray

variable {ι : Type*}

theorem infinite_product_gaussian_law_and_indep_of_condExp_linear_character
    {P : Measure Ω} [IsProbabilityMeasure P]
    (hm : m ≤ mΩ) {X : Ω → ι → ℝ} (hX : Measurable[mΩ] X)
    (v : ι → ℝ≥0)
    (hchar : ∀ (I : Finset ι) (a : I → ℝ),
      P[(fun ω => Complex.exp (((∑ i : I, a i * X ω i : ℝ) : ℂ) * Complex.I)) | m] =ᵐ[P]
        fun _ => Complex.exp (-((∑ i : I, (v i : ℝ) * (a i) ^ 2 : ℝ) : ℂ) / 2))
    {E : Type*} [MeasurableSpace E] {Y : Ω → E} (hY : Measurable[m] Y) :
    HasLaw X (Measure.infinitePi (fun i => gaussianReal 0 (v i))) P ∧
      iIndepFun (fun i ω => X ω i) P ∧ IndepFun X Y P := by
  classical
  have hfinite (I : Finset ι) :
      HasLaw (fun ω (i : I) => X ω i) (Measure.pi (fun i : I => gaussianReal 0 (v i))) P ∧
        IndepFun (fun ω (i : I) => X ω i) Y P :=
    product_gaussian_law_and_indep_of_condExp_linear_character hm
      (by fun_prop) (fun i : I => v i) (hchar I) hY
  have hcoordinate (i : ι) : HasLaw (fun ω => X ω i) (gaussianReal 0 (v i)) P := by
    let j : ({i} : Finset ι) := ⟨i, Finset.mem_singleton_self i⟩
    exact (measurePreserving_eval (fun k : ({i} : Finset ι) => gaussianReal 0 (v k)) j).fun_comp_hasLaw (hfinite {i}).1
  have hind : iIndepFun (fun i ω => X ω i) P := by
    apply iIndepFun_iff_finset.mpr
    intro I
    exact (iIndepFun_iff_hasLaw_pi_pi (fun i : I => hcoordinate i)).mpr (hfinite I).1
  refine ⟨hind.hasLaw_infinitePi hcoordinate hX.aemeasurable, hind, ?_⟩
  exact IndepFun.process_indepFun (fun i => (measurable_pi_apply i).comp hX)
    (hY.mono hm le_rfl) (fun I => (hfinite I).2)

end ArbitraryArray

end Problem367.ConditionalGaussianVector

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Energy_Attenuation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Problem367

lemma lipschitzWith_tanh_response : LipschitzWith 1 Real.tanh := by
  apply lipschitzWith_of_nnnorm_deriv_le
  · intro x
    exact (hasDerivAt_tanh_response x).differentiableAt
  · intro x
    have h : |deriv Real.tanh x| ≤ 1 := by
      rw [(hasDerivAt_tanh_response x).deriv,
        abs_of_nonneg (sub_nonneg.mpr (le_of_lt (Real.tanh_sq_lt_one x)))]
      nlinarith [sq_nonneg (Real.tanh x)]
    exact_mod_cast h

end Problem367

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Energy_DiscrepancyRowEnergy
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Filter Set
open scoped Topology ENNReal

namespace Problem367.DiscrepancyEnergy

theorem hasSum_integral_sq_row
    {Ω ι : Type*} [MeasurableSpace Ω] [Countable ι] {μ : Measure Ω}
    {c : ι → Ω → ℝ} (hc : ∀ i, AEStronglyMeasurable (c i) μ)
    (hsum : ∀ᵐ ω ∂μ, Summable (fun i => (c i ω) ^ 2))
    (hA : Integrable (fun ω => ∑' i, (c i ω) ^ 2) μ) :
    HasSum (fun i => ∫ ω, (c i ω) ^ 2 ∂μ) (∫ ω, (∑' i, (c i ω) ^ 2) ∂μ) := by
  refine hasSum_integral_of_dominated_convergence (fun i ω => (c i ω) ^ 2)
    (fun i => (hc i).pow 2) ?_ hsum hA ?_
  · intro i
    filter_upwards with ω
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  · filter_upwards [hsum] with ω hω
    exact hω.hasSum

end Problem367.DiscrepancyEnergy

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Energy_ShiftedFieldVariance
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory

namespace Problem367

section Probability

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
variable {G : Ω → ℝ} {beta : ℝ}

lemma continuous_responseAttenuation {theta : ℝ} (hθ : theta ^ 2 ≤ 1) :
    Continuous (responseAttenuation theta) := by
  have ht := lipschitzWith_tanh_response.continuous
  exact (continuous_const.sub (ht.pow 2)).div
    (continuous_const.sub (continuous_const.mul (ht.pow 2)))
    (fun z => ne_of_gt (attenuation_denominator_pos hθ z))

end Probability

end Problem367

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Estimates_ProgressiveVersionPushforward
attribute [-instance] _root_.OAI.Problem367.WienerSampler.pathMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Filter Set
open scoped NNReal Topology

namespace Problem367.ProgressiveVersionPushforward
open ContinuousModification

lemma leftTime_le (t : ℝ≥0) (n : ℕ) : leftTime t n ≤ t := by
  simpa only [leftTime, Real.toNNReal_coe] using Real.toNNReal_mono (dyadicLeft_le t n)

lemma measurable_leftTime (n : ℕ) : Measurable (fun t => leftTime t n) := by
  unfold leftTime dyadicLeft
  fun_prop

lemma progressive_version {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {F : Filtration ℝ≥0 mΩ} {M : ℝ≥0 → Ω → ℝ}
    (hM : IsStronglyProgressive F M) : IsStronglyProgressive F (version M) := by
  apply isStronglyProgressive_sampledLimit F
  intro n
  apply hM.comp _ (fun t _ => leftTime_le t n)
  intro T
  exact ((measurable_leftTime n).comp measurable_fst.subtype_val).stronglyMeasurable

end Problem367.ProgressiveVersionPushforward

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Ising_ConditionalCopyBounds
attribute [-instance] _root_.OAI.Problem367.IsingObservationFactor.copies_probability _root_.OAI.Problem367.IsingObservationFactor.kernel_markov _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_observationLaw_probability _root_.OAI.Problem367.IsingObservationInnovation.observationLaw_probability _root_.OAI.Problem367.TreeKoopman.labelProbability _root_.OAI.Problem367.freeIsingMeasure_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped NNReal

namespace Problem367.IsingConditionalCopyBounds

open PlantedSymmetry IsingObservationInnovation WienerSampler

theorem progressive_leftObservation {d : ℕ} (v : TreeVertex d) :
    IsStronglyProgressive ContinuousCopyBrownian.joinedFiltration
      (fun t (q : CopySpace d) => q.2.1 v t) := by
  have had : StronglyAdapted ContinuousCopyBrownian.joinedFiltration
      (fun t (q : CopySpace d) => q.2.1 v t) := by
    intro t
    change StronglyMeasurable[ContinuousCopyBrownian.pastSpace t]
      (fun q : CopySpace d => q.2.1 v t)
    have hh : Measurable[ContinuousCopyBrownian.pastSpace t]
        (ContinuousCopyBrownian.history (ι := TreeVertex d) t) := comap_measurable _
    have hm := (continuous_eval_const t).measurable.comp
      ((measurable_pi_apply v).comp
        ((measurable_fst.comp measurable_snd).comp hh))
    simpa only [Function.comp_def, ContinuousCopyBrownian.history,
      ContinuousObservationHistory.stoppedArray,
      ContinuousObservationHistory.stoppedPath_apply, min_self] using hm.stronglyMeasurable
  exact had.isStronglyProgressive_of_continuous (fun q => (q.2.1 v).continuous)

theorem progressive_rightObservation {d : ℕ} (v : TreeVertex d) :
    IsStronglyProgressive ContinuousCopyBrownian.joinedFiltration
      (fun t (q : CopySpace d) => q.2.2 v t) := by
  have had : StronglyAdapted ContinuousCopyBrownian.joinedFiltration
      (fun t (q : CopySpace d) => q.2.2 v t) := by
    intro t
    change StronglyMeasurable[ContinuousCopyBrownian.pastSpace t]
      (fun q : CopySpace d => q.2.2 v t)
    have hh : Measurable[ContinuousCopyBrownian.pastSpace t]
        (ContinuousCopyBrownian.history (ι := TreeVertex d) t) := comap_measurable _
    have hm := (continuous_eval_const t).measurable.comp
      ((measurable_pi_apply v).comp
        ((measurable_snd.comp measurable_snd).comp hh))
    simpa only [Function.comp_def, ContinuousCopyBrownian.history,
      ContinuousObservationHistory.stoppedArray,
      ContinuousObservationHistory.stoppedPath_apply, min_self] using hm.stronglyMeasurable
  exact had.isStronglyProgressive_of_continuous (fun q => (q.2.2 v).continuous)

end Problem367.IsingConditionalCopyBounds

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Ising_InnovationIndependence
attribute [-instance] _root_.OAI.Problem367.IsingConditionalCopyBounds.graphLaw_isProbabilityMeasure _root_.OAI.Problem367.IsingObservationFactor.copies_probability _root_.OAI.Problem367.IsingObservationFactor.kernel_markov _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_observationLaw_probability _root_.OAI.Problem367.IsingObservationInnovation.observationLaw_probability _root_.OAI.Problem367.TreeKoopman.labelProbability _root_.OAI.Problem367.freeIsingMeasure_probability
attribute [-simp] _root_.OAI.Problem367.ConnectedHull.pathAssignment_path _root_.OAI.Problem367.ConnectedHull.path_last _root_.OAI.Problem367.ConnectedHull.path_zero _root_.OAI.Problem367.CutContinuationChannels.averageChannel_globalCone _root_.OAI.Problem367.CutContinuationChannels.continuationChannel_globalCone _root_.OAI.Problem367.FactorObservable.centeredSpinLp_coe _root_.OAI.Problem367.FiniteIsingSplit.splitEquiv_fst _root_.OAI.Problem367.FiniteIsingSplit.splitEquiv_snd _root_.OAI.Problem367.FinitePathGibbs.tailPartition_zero _root_.OAI.Problem367.GaussianTreeResponseNaturality.fieldEquiv_apply_image _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_apply _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_uniformObservation _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_zero _root_.OAI.Problem367.IsingObservationInnovation.uniformObservation_relabel _root_.OAI.Problem367.IsingOrientedPath.attenuation_outward _root_.OAI.Problem367.IsingOrientedPath.endpoint_extensionAt _root_.OAI.Problem367.LocalSupportGeometry.prefixVertex_length _root_.OAI.Problem367.PathSideBranches.parent_sideVertex _root_.OAI.Problem367.PathSideBranches.restrictNoisyRegion_array _root_.OAI.Problem367.PathSideBranches.sideVertex_length _root_.OAI.Problem367.PathSideBranches.sideVertex_val _root_.OAI.Problem367.PosteriorChain.transition_spinMean _root_.OAI.Problem367.PosteriorChain.transition_sum _root_.OAI.Problem367.RootedBroadcast.flipBranchToComplement_val _root_.OAI.Problem367.RootedBroadcast.pos_spinMul _root_.OAI.Problem367.RootedBroadcast.prefixFlip_branchRoot _root_.OAI.Problem367.RootedBroadcast.prefixFlip_root _root_.OAI.Problem367.RootedBroadcast.prefixTreeAut_symm_branchRoot _root_.OAI.Problem367.RootedBroadcast.prefixTreeAut_symm_root _root_.OAI.Problem367.RootedBroadcast.spinMul_pos _root_.OAI.Problem367.RootedBroadcast.spinMul_self _root_.OAI.Problem367.TreeConeCoding.length_vertex _root_.OAI.Problem367.TreeConeCoding.vertex_nil _root_.OAI.Problem367.TreeConeCoding.vertex_val _root_.OAI.Problem367.TreeGibbsAut.spinEquiv_apply_image _root_.OAI.Problem367.TreeKoopman.centeredAverage_apply_coe _root_.OAI.Problem367.TreeKoopman.centeredAverage_pow_apply_coe _root_.OAI.Problem367.TreeKoopman.centeredGenerator_apply_coe _root_.OAI.Problem367.TreeKoopman.centeredGenerator_sq _root_.OAI.Problem367.TreeKoopman.generatorOperator_sq _root_.OAI.Problem367.TreeKoopman.reverseVertex_twice _root_.OAI.Problem367.TreeKoopman.wordRelabel_cons _root_.OAI.Problem367.TreeKoopman.wordRelabel_nil _root_.OAI.Problem367.TreeLawKoopman.centeredAverage_apply_coe _root_.OAI.Problem367.TreeLawKoopman.generatorOperator_sq _root_.OAI.Problem367.TreePathGibbs.vertexEquiv_val _root_.OAI.Problem367.branchColorAut_length _root_.OAI.Problem367.branchColorAut_singleton _root_.OAI.Problem367.branchColorAut_val _root_.OAI.Problem367.branchColorMap_symm_apply _root_.OAI.Problem367.colorPermAut_length _root_.OAI.Problem367.colorPermAut_nil _root_.OAI.Problem367.colorPermAut_val _root_.OAI.Problem367.colorPermMap_symm_apply _root_.OAI.Problem367.colorPermMap_val _root_.OAI.Problem367.connectedSpinEncode_apply_root _root_.OAI.Problem367.connectedSpinEquiv_apply _root_.OAI.Problem367.dropVertex_length _root_.OAI.Problem367.dropVertex_val _root_.OAI.Problem367.innovationPath_apply _root_.OAI.Problem367.mem_rootComplementFinset _root_.OAI.Problem367.mem_rootComponentFinset _root_.OAI.Problem367.mem_rootComponentIndices _root_.OAI.Problem367.parentVertex_length _root_.OAI.Problem367.parentVertex_val _root_.OAI.Problem367.prefixColorAut_length _root_.OAI.Problem367.prefixColorAut_val _root_.OAI.Problem367.prefixColorMap_symm_apply _root_.OAI.Problem367.prefixFlip_twice _root_.OAI.Problem367.spinAgreementCode_eq_neg_iff _root_.OAI.Problem367.spinAgreementCode_eq_pos_iff _root_.OAI.Problem367.spinSign_flip _root_.OAI.Problem367.tsum_treeShell_radial
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace Problem367.IsingInnovation

variable {d : ℕ} {A : Type*} [MeasurableSpace A]
  {beta : ℝ} {μ : Measure (TreeVertex d → IsingSpin)}
  (hμ : HasFreeIsingLaw (Real.tanh beta) μ)
  (ν : Measure A) {B : ℝ≥0 → A → ℝ} (hB : IsPreBrownianReal B ν)
  (hmB : ∀ t, Measurable (B t)) (hcB : ∀ a, Continuous (fun t => B t a))

private theorem spin_bound (v : TreeVertex d) :
    ∀ᵐ sigma ∂μ, |ArrayPosteriorStationarity.spinArray sigma v| ≤ (1 : ℝ≥0) := by
  apply Filter.Eventually.of_forall
  intro sigma
  cases hs : sigma v <;> norm_num [ArrayPosteriorStationarity.spinArray, spinSign, hs]

include hμ hB hcB

theorem innovation_martingale (v : TreeVertex d) :
    Martingale (innovation beta B v) (ArrayPosteriorStationarity.filtration B hmB)
      (μ.prod (Measure.infinitePi (fun _ : TreeVertex d => ν))) := by
  let := hμ.isProbabilityMeasure
  exact preBrownian_array_innovation_martingale_of_progressive_posterior
    μ (fun _ : TreeVertex d => ν) (fun _ => hB) (fun _ => hmB)
    ArrayPosteriorStationarity.measurable_spinArray v (spin_bound v)
    (posterior_progressive beta B hmB hcB v)
    (fun t => posterior_eq_condExp hμ ν hB hmB t v)

theorem innovation_increment_law_and_indep
    {E : Type*} [mE : MeasurableSpace E] {Y : State d A → E}
    (s t : ℝ≥0) (hst : s ≤ t)
    (hY : Measurable[ArrayPosteriorStationarity.filtration B hmB s] Y) :
    HasLaw (fun q v => innovation beta B v t q - innovation beta B v s q)
      (Measure.infinitePi (fun _ : TreeVertex d => gaussianReal 0 (t - s)))
      (μ.prod (Measure.infinitePi (fun _ : TreeVertex d => ν))) ∧
    iIndepFun (fun v q => innovation beta B v t q - innovation beta B v s q)
      (μ.prod (Measure.infinitePi (fun _ : TreeVertex d => ν))) ∧
    IndepFun (fun q v => innovation beta B v t q - innovation beta B v s q) Y
      (μ.prod (Measure.infinitePi (fun _ : TreeVertex d => ν))) := by
  let := hμ.isProbabilityMeasure
  let : IsProbabilityMeasure ν := hB.isGaussianProcess.isProbabilityMeasure
  apply ConditionalGaussianVector.infinite_product_gaussian_law_and_indep_of_condExp_linear_character
    (ArrayPosteriorStationarity.filtration B hmB |>.le s) _
    (fun _ : TreeVertex d => t - s) _ hY
  · apply Measurable.of_eval
    intro v
    exact ((innovation_martingale hμ ν hB hmB hcB v).stronglyMeasurable t).measurable.mono
      (ArrayPosteriorStationarity.filtration B hmB |>.le t) le_rfl |>.sub
        (((innovation_martingale hμ ν hB hmB hcB v).stronglyMeasurable s).measurable.mono
          (ArrayPosteriorStationarity.filtration B hmB |>.le s) le_rfl)
  · intro I a
    have h := ArrayInnovationLaw.conditional_weighted_character μ
      (fun _ : TreeVertex d => ν) (fun _ => hB) (fun _ => hmB)
      ArrayPosteriorStationarity.measurable_spinArray (fun v => spin_bound v)
      (posterior_progressive beta B hmB hcB)
      (fun v t => posterior_eq_condExp hμ ν hB hmB t v) I s t hst a
    have heq : ConditionalCharacteristic.character
        (fun q => ∑ i : I, a i * (innovation beta B i.1 t q - innovation beta B i.1 s q)) 1 =
        (fun q => Complex.exp (((∑ i : I, a i *
          (innovation beta B i.1 t q - innovation beta B i.1 s q) : ℝ) : ℂ) * Complex.I)) := by
      funext q
      simp [ConditionalCharacteristic.character]
    change (μ.prod (Measure.infinitePi (fun _ : TreeVertex d => ν)))[
      ConditionalCharacteristic.character
        (fun q => ∑ i : I, a i * (innovation beta B i.1 t q - innovation beta B i.1 s q)) 1 |
        ArrayPosteriorStationarity.filtration B hmB s] =ᵐ[_] _ at h
    rw [heq] at h
    simpa only [Complex.ofReal_sum, Complex.ofReal_mul, Complex.ofReal_pow] using h

theorem innovation_increment_indep_filtration (s t : ℝ≥0) (hst : s ≤ t) :
    Indep (MeasurableSpace.comap
      (fun q v => innovation beta B v t q - innovation beta B v s q) inferInstance)
      (ArrayPosteriorStationarity.filtration B hmB s)
      (μ.prod (Measure.infinitePi (fun _ : TreeVertex d => ν))) := by
  have h := (innovation_increment_law_and_indep hμ ν hB hmB hcB
    (mE := ArrayPosteriorStationarity.filtration B hmB s)
    (Y := id) s t hst measurable_id).2.2
  change Indep _ ((ArrayPosteriorStationarity.filtration B hmB s).comap id) _ at h
  simpa only [MeasurableSpace.comap_id] using h

theorem innovation_future_indep_filtration (s : ℝ≥0) :
    Indep (ArrayPosteriorStationarity.filtration B hmB s)
      (MeasurableSpace.comap
        (fun q (t : Set.Ici s) v => innovation beta B v t.val q - innovation beta B v s q)
        inferInstance)
      (μ.prod (Measure.infinitePi (fun _ : TreeVertex d => ν))) := by
  let := hμ.isProbabilityMeasure
  let : IsProbabilityMeasure ν := hB.isGaussianProcess.isProbabilityMeasure
  apply FilteredFutureIndependence.indep_future
    (X := fun t q v => innovation beta B v t q)
  · intro t
    let : MeasurableSpace (State d A) := ArrayPosteriorStationarity.filtration B hmB t
    exact Measurable.of_eval (fun v =>
      (innovation_martingale hμ ν hB hmB hcB v).stronglyAdapted.adapted t)
  · exact innovation_increment_indep_filtration hμ ν hB hmB hcB

omit hB hmB hcB ν in

theorem uniformInnovation_future_indep_filtration (s : ℝ≥0) :
    Indep (uniformObservationFiltration d s)
      (MeasurableSpace.comap
        (fun q (t : Set.Ici s) v => uniformInnovation beta q v t.val -
          uniformInnovation beta q v s) inferInstance)
      (μ.prod (labelMeasure d)) := by
  exact innovation_future_indep_filtration hμ uniform01
    WienerSampler.sample_isBrownianReal.toIsPreBrownianReal
    (fun t => WienerSampler.measurable_sample_eval.comp
      (measurable_const.prodMk measurable_id))
    (fun u => (WienerSampler.sample u).continuous) s

end Problem367.IsingInnovation

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Ising_ObservationLaw
attribute [-instance] _root_.OAI.Problem367.IsingConditionalCopyBounds.graphLaw_isProbabilityMeasure _root_.OAI.Problem367.IsingObservationFactor.copies_probability _root_.OAI.Problem367.IsingObservationFactor.kernel_markov _root_.OAI.Problem367.TreeKoopman.labelProbability _root_.OAI.Problem367.freeIsingMeasure_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace Problem367.IsingObservationInnovation

theorem filtration_eq_comap_past (d : ℕ) (t : ℝ≥0) :
    filtration d t = MeasurableSpace.comap (past t) inferInstance :=
  arrayNaturalFiltration_eq_comap evaluation measurable_evaluation t

theorem filtration_comap_uniformObservation (d : ℕ) (t : ℝ≥0)
    (hm : ∀ s, Measurable (fun u => WienerSampler.sample u s)) :
    (filtration d t).comap uniformObservation =
      ArrayPosteriorStationarity.filtration
        (fun s u => WienerSampler.sample u s) hm t := by
  rw [filtration_eq_comap_past, MeasurableSpace.comap_comp]
  unfold ArrayPosteriorStationarity.filtration arrayObservationFiltration
  rw [arrayNaturalFiltration_eq_comap]
  rfl

end Problem367.IsingObservationInnovation

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Ising_ObservationComparison
attribute [-instance] _root_.OAI.Problem367.TreeKoopman.labelProbability _root_.OAI.Problem367.freeIsingMeasure_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace Problem367.IsingObservationFactor

open IsingObservationInnovation

variable {d : ℕ} {beta : ℝ} {μ : Measure (TreeVertex d → IsingSpin)}
variable [IsProbabilityMeasure μ]

theorem kernel_graphLaw :
    ((observationLaw μ).map (innovationMap beta)) ⊗ₘ kernel beta μ =
      IsingConditionalCopyBounds.graphLaw beta μ :=
  ObservableDisintegration.compProd_kernel (observationLaw μ)
    (measurable_innovationMap beta)

end Problem367.IsingObservationFactor

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Posterior_ContinuousPosteriorInterior
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

theorem isStronglyProgressive_artanh
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (F : Filtration ℝ≥0 mΩ) {m : ℝ≥0 → Ω → ℝ}
    (hm : IsStronglyProgressive F m) :
    IsStronglyProgressive F (fun t ω => Real.artanh (m t ω)) := by
  have ha : Measurable Real.artanh := by
    unfold Real.artanh
    fun_prop
  intro t
  let : MeasurableSpace Ω := F t
  exact (ha.comp (hm t).measurable).stronglyMeasurable

end Problem367

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Ising_ContinuousRootResponse
attribute [-simp] _root_.OAI.Problem367.CutContinuationChannels.averageChannel_globalCone _root_.OAI.Problem367.CutContinuationChannels.continuationChannel_globalCone _root_.OAI.Problem367.FactorObservable.centeredSpinLp_coe _root_.OAI.Problem367.IsingOrientedPath.attenuation_outward _root_.OAI.Problem367.IsingOrientedPath.endpoint_extensionAt _root_.OAI.Problem367.PathSideBranches.parent_sideVertex _root_.OAI.Problem367.PathSideBranches.restrictNoisyRegion_array _root_.OAI.Problem367.PathSideBranches.sideVertex_length _root_.OAI.Problem367.PathSideBranches.sideVertex_val _root_.OAI.Problem367.TreeConeCoding.length_vertex _root_.OAI.Problem367.TreeConeCoding.vertex_nil _root_.OAI.Problem367.TreeConeCoding.vertex_val _root_.OAI.Problem367.TreeKoopman.centeredGenerator_apply_coe _root_.OAI.Problem367.TreeKoopman.centeredGenerator_sq _root_.OAI.Problem367.TreeKoopman.reverseVertex_twice _root_.OAI.Problem367.dropVertex_length _root_.OAI.Problem367.dropVertex_val _root_.OAI.Problem367.mem_rootComplementFinset _root_.OAI.Problem367.mem_rootComponentFinset _root_.OAI.Problem367.mem_rootComponentIndices _root_.OAI.Problem367.prefixColorAut_length _root_.OAI.Problem367.prefixColorAut_val _root_.OAI.Problem367.prefixColorMap_symm_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped NNReal Topology BigOperators

namespace Problem367.IsingObservationFactor
open IsingObservationInnovation

variable {d : ℕ} {beta : ℝ}

lemma continuous_siteRootResponse (hb : 0 ≤ beta) (v : TreeVertex d) :
    Continuous (siteRootResponse hb v) := by
  unfold siteRootResponse
  apply Continuous.const_mul
  apply continuous_finsetProd
  intro i hi
  exact (continuous_responseAttenuation (Real.tanh_sq_lt_one beta).le).comp
    (continuous_fst.comp ((continuous_cavityFromSites
      (tanh_nonneg_of_beta_nonneg hb) (Real.tanh_lt_one beta)).comp
      ((continuous_apply _).prodMk (continuous_apply _))))

lemma siteRootResponse_mem_Icc (hb : 0 ≤ beta) (v : TreeVertex d)
    (H : TreeVertex d → ℝ) :
    0 ≤ siteRootResponse hb v H ∧ siteRootResponse hb v H ≤ 1 := by
  have hp0 : 0 ≤ ∏ i ∈ Finset.range v.1.length, responseAttenuation (Real.tanh beta)
      (CavityArray.field (tanh_nonneg_of_beta_nonneg hb) (Real.tanh_lt_one beta)
        H (ConnectedHull.takeVertex v (i + 1)) (ConnectedHull.takeVertex v i)) :=
    Finset.prod_nonneg fun i _ => (responseAttenuation_pos (Real.tanh_sq_lt_one beta).le _).le
  have hp1 : (∏ i ∈ Finset.range v.1.length, responseAttenuation (Real.tanh beta)
      (CavityArray.field (tanh_nonneg_of_beta_nonneg hb) (Real.tanh_lt_one beta)
        H (ConnectedHull.takeVertex v (i + 1)) (ConnectedHull.takeVertex v i))) ≤ 1 :=
    Finset.prod_le_one
      (fun i _ => (responseAttenuation_pos (Real.tanh_sq_lt_one beta).le _).le)
      (fun i _ => responseAttenuation_le_one (Real.tanh_sq_lt_one beta).le _)
  have ht0 := pow_nonneg (tanh_nonneg_of_beta_nonneg hb) v.1.length
  have ht1 : Real.tanh beta ^ v.1.length ≤ 1 :=
    pow_le_one₀ (tanh_nonneg_of_beta_nonneg hb) (Real.tanh_lt_one beta).le
  exact ⟨mul_nonneg ht0 hp0, (mul_le_mul ht1 hp1 hp0 (by norm_num)).trans_eq (one_mul 1)⟩

lemma continuousRootResponse_abs_le_one (hb : 0 ≤ beta) (v : TreeVertex d)
    (t : ℝ≥0) (x : Paths d) : |continuousRootResponse hb v t x| ≤ 1 := by
  obtain ⟨h0, h1⟩ := siteRootResponse_mem_Icc hb v (fun i => continuousField beta i t x)
  exact (abs_of_nonneg h0).trans_le h1

end Problem367.IsingObservationFactor

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Ising_ObservationIndependence
attribute [-instance] _root_.OAI.Problem367.IsingConditionalCopyBounds.graphLaw_isProbabilityMeasure _root_.OAI.Problem367.IsingObservationFactor.copies_probability _root_.OAI.Problem367.IsingObservationFactor.kernel_markov _root_.OAI.Problem367.TreeKoopman.labelProbability _root_.OAI.Problem367.freeIsingMeasure_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace Problem367.IsingObservationInnovation

private theorem indep_map_of_comap {Ω E : Type*}
    [mΩ : MeasurableSpace Ω] [mE : MeasurableSpace E]
    {P : Measure Ω} {f : Ω → E} (hf : Measurable f)
    {m n : MeasurableSpace E} (hm : m ≤ mE) (hn : n ≤ mE)
    (h : Indep (m.comap f) (n.comap f) P) :
    Indep m n (@Measure.map Ω E mΩ mE f P) := by
  rw [Indep_iff]
  intro A B hA hB
  rw [Measure.map_apply (μ := P) hf ((hm A hA).inter (hn B hB)),
    Measure.map_apply (μ := P) hf (hm A hA), Measure.map_apply (μ := P) hf (hn B hB)]
  exact (Indep_iff _ _ _).mp h _ _
    ((comap_measurable (m := m) f) hA) ((comap_measurable (m := n) f) hB)

theorem measurable_futureInnovation {d : ℕ} (beta : ℝ) (s : ℝ≥0) :
    Measurable (futureInnovation (d := d) beta s) := by
  apply Measurable.of_eval
  intro t
  apply Measurable.of_eval
  intro v
  exact ((measurable_evaluation v t.val).comp (measurable_innovationMap beta)).sub
    ((measurable_evaluation v s).comp (measurable_innovationMap beta))

theorem innovationMap_stronglyAdapted {d : ℕ} (beta : ℝ) (v : TreeVertex d) :
    StronglyAdapted (filtration d) (fun t x => innovationMap beta x v t) := by
  exact (arrayNaturalFiltration_stronglyAdapted evaluation measurable_evaluation v).sub
    (stronglyAdapted_nnrealTimePrimitive (posterior_progressive beta v))

theorem innovationMap_future_indep_filtration {d : ℕ} {beta : ℝ}
    {μ : Measure (TreeVertex d → IsingSpin)}
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (s : ℝ≥0) :
    Indep (filtration d s)
      (MeasurableSpace.comap (futureInnovation beta s) inferInstance)
      (observationLaw μ) := by
  change Indep _ _ ((μ.prod (labelMeasure d)).map (uniformObservation (d := d)))
  refine indep_map_of_comap (P := μ.prod (labelMeasure d))
    (f := uniformObservation) measurable_uniformObservation (filtration d |>.le s)
    (measurable_futureInnovation beta s).comap_le ?_
  have h := IsingInnovation.uniformInnovation_future_indep_filtration hμ s
  rw [MeasurableSpace.comap_comp]
  rw [filtration_comap_uniformObservation d s
    (fun t => WienerSampler.measurable_sample_eval.comp
      (measurable_const.prodMk measurable_id))]
  exact h

theorem innovationMap_increment_indep_filtration {d : ℕ} {beta : ℝ}
    {μ : Measure (TreeVertex d → IsingSpin)}
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (s t : ℝ≥0) (hst : s ≤ t) :
    Indep (MeasurableSpace.comap
      (fun x v => innovationMap beta x v t - innovationMap beta x v s) inferInstance)
      (filtration d s) (observationLaw μ) := by
  apply (indep_of_indep_of_le_right (innovationMap_future_indep_filtration hμ s) ?_).symm
  exact ((measurable_pi_apply (⟨t, hst⟩ : Set.Ici s)).comp
    (comap_measurable (futureInnovation beta s))).comap_le

end Problem367.IsingObservationInnovation

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Ising_CopyBrownian
attribute [-instance] _root_.OAI.Problem367.TreeKoopman.labelProbability _root_.OAI.Problem367.freeIsingMeasure_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace Problem367.IsingCopyBrownian

open IsingObservationInnovation IsingObservationFactor
open ContinuousObservationHistory ContinuousNoiseSplit

variable {d : ℕ} {beta : ℝ}
variable {μ : Measure (TreeVertex d → IsingSpin)} [IsProbabilityMeasure μ]

theorem graph_future_indep
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (s : ℝ≥0) :
    IndepFun (fun q : Paths d × Paths d =>
      (stoppedArray s q.1, stoppedArray s q.2))
      (fun q => futureArray s q.1)
      (((observationLaw μ).map (innovationMap beta)) ⊗ₘ kernel beta μ) := by
  rw [kernel_graphLaw]
  unfold IsingConditionalCopyBounds.graphLaw
  apply ConstructedConditionalCopies.indepFun_map_of_comp
    ((measurable_innovationMap beta).prodMk measurable_id)
    (((measurable_stoppedArray s).comp measurable_fst).prodMk
      ((measurable_stoppedArray s).comp measurable_snd))
    ((measurable_futureArray s).comp measurable_fst)
  exact ConstructedContinuousCopies.indepFun_continuous_future
    (observationLaw μ) (filtration d) (innovationMap beta) id
    (fun v t => (innovationMap_stronglyAdapted beta v t).measurable)
    (fun v t => (arrayNaturalFiltration_stronglyAdapted
      evaluation measurable_evaluation v t).measurable)
    (innovationMap_increment_indep_filtration hμ) s

theorem increment_indep_joinedFiltration
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) {s t : ℝ≥0} (hst : s ≤ t) :
    Indep (MeasurableSpace.comap
      (fun q : Paths d × (Paths d × Paths d) => fun v => q.1 v t - q.1 v s)
      inferInstance) (ContinuousCopyBrownian.joinedFiltration s) (copies beta μ) := by
  have : IsProbabilityMeasure ((observationLaw μ).map (innovationMap beta)) :=
    (by first | exact Measure.isProbabilityMeasure_map (by first | (apply Measurable.aemeasurable; apply measurable_innovationMap <;> assumption)) | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability))
  exact ContinuousCopyBrownian.indep_increment_joinedFiltration
    ((observationLaw μ).map (innovationMap beta)) (kernel beta μ) hst
    (graph_future_indep hμ s)

theorem commonNoise_stronglyAdapted (v : TreeVertex d) :
    StronglyAdapted ContinuousCopyBrownian.joinedFiltration
      (fun t (q : Paths d × (Paths d × Paths d)) => q.1 v t) := by
  intro t
  exact ((measurable_pi_apply v).comp
    (ContinuousCopyBrownian.measurable_commonNoise_joinedFiltration t)).stronglyMeasurable

omit [IsProbabilityMeasure μ] in
private theorem innovationLaw_coordinate_preBrownian [_hprob : IsProbabilityMeasure μ]
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (v : TreeVertex d) :
    IsPreBrownianReal (fun t (w : Paths d) => w v t)
      ((observationLaw μ).map (innovationMap beta)) := by
  rw [map_innovationMap_observationLaw hμ]
  exact ⟨fun I => (WienerSampler.coordinate_isBrownianReal.hasLaw I).comp
    (measurePreserving_eval_infinitePi
      (fun _ : TreeVertex d => WienerSampler.wienerMeasure) v).hasLaw⟩

theorem commonNoise_isBrownianReal
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (v : TreeVertex d) :
    IsBrownianReal (fun t (q : Paths d × (Paths d × Paths d)) => q.1 v t)
      (copies beta μ) := by
  have : IsProbabilityMeasure ((observationLaw μ).map (innovationMap beta)) :=
    (by first | exact Measure.isProbabilityMeasure_map (by first | (apply Measurable.aemeasurable; apply measurable_innovationMap <;> assumption)) | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability))
  exact ContinuousCopyBrownian.isBrownian_commonNoise v
    ((observationLaw μ).map (innovationMap beta))
    (innovationLaw_coordinate_preBrownian hμ v) (kernel beta μ)

theorem commonNoise_increments_indep
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (s t : ℝ≥0)
    {v w : TreeVertex d} (hvw : v ≠ w) :
    IndepFun (fun q : Paths d × (Paths d × Paths d) => q.1 v t - q.1 v s)
      (fun q => q.1 w t - q.1 w s) (copies beta μ) := by
  have : IsProbabilityMeasure ((observationLaw μ).map (innovationMap beta)) :=
    (by first | exact Measure.isProbabilityMeasure_map (by first | (apply Measurable.aemeasurable; apply measurable_innovationMap <;> assumption)) | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability))
  have hp : MeasurePreserving (Prod.fst : Paths d × (Paths d × Paths d) → Paths d)
      (copies beta μ) ((observationLaw μ).map (innovationMap beta)) :=
    ⟨measurable_fst, Measure.fst_compProd _ _⟩
  apply indepFun_comp_measurePreserving hp
    ((measurable_evaluation v t).sub (measurable_evaluation v s))
    ((measurable_evaluation w t).sub (measurable_evaluation w s))
  rw [map_innovationMap_observationLaw hμ]
  exact (iIndepFun_infinitePi (P := fun _ : TreeVertex d => WienerSampler.wienerMeasure)
    (fun _ => (continuous_eval_const t).measurable.sub
      (continuous_eval_const s).measurable)).indepFun hvw

end Problem367.IsingCopyBrownian

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Ising_ContinuousCopyCoefficients
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal Topology

namespace Problem367.IsingContinuousCopyCoefficients
open IsingObservationInnovation IsingObservationFactor IsingCopyEnergy

variable {d : ℕ} {beta : ℝ}

lemma field_progressive (j : Bool) (v : TreeVertex d) :
    IsStronglyProgressive ContinuousCopyBrownian.joinedFiltration
      (fun t (q : Joint d) => continuousField beta v t (projection j q)) := by
  have hobs (i : TreeVertex d) : IsStronglyProgressive
      ContinuousCopyBrownian.joinedFiltration
      (fun t (q : Joint d) => projection j q i t) := by
    cases j
    · exact IsingConditionalCopyBounds.progressive_rightObservation i
    · exact IsingConditionalCopyBounds.progressive_leftObservation i
  have hraw := isStronglyProgressive_artanh _
    (isStronglyProgressive_infiniteGibbsSpinMean _ beta v _ hobs)
  exact ProgressiveVersionPushforward.progressive_version hraw

lemma response_progressive (hb : 0 ≤ beta) (j : Bool) (v : TreeVertex d) :
    IsStronglyProgressive ContinuousCopyBrownian.joinedFiltration (response hb j v) := by
  intro T
  let : MeasurableSpace (Joint d) := ContinuousCopyBrownian.joinedFiltration T
  exact ((continuous_siteRootResponse hb v).measurable.comp
    (Measurable.of_eval (fun vertex => (field_progressive j vertex T).measurable))).stronglyMeasurable

lemma response_abs_le_one (hb : 0 ≤ beta) (j : Bool) (v : TreeVertex d)
    (t : ℝ≥0) (q : Joint d) : |response hb j v t q| ≤ 1 :=
  continuousRootResponse_abs_le_one hb v t (projection j q)

variable {μ : Measure (TreeVertex d → IsingSpin)} [IsProbabilityMeasure μ]

private lemma real_measurable {X : ℝ≥0 → Joint d → ℝ}
    (hX : IsStronglyProgressive ContinuousCopyBrownian.joinedFiltration X) :
    Measurable (fun p : ℝ × Joint d => X p.1.toNNReal p.2) :=
  (stronglyMeasurable_joint_of_isStronglyProgressive hX).measurable.comp
    ((measurable_real_toNNReal.comp measurable_fst).prodMk measurable_snd)

private lemma sq_time_integrable {X : ℝ≥0 → Joint d → ℝ}
    (hX : IsStronglyProgressive ContinuousCopyBrownian.joinedFiltration X)
    (hb : ∀ t q, |X t q| ≤ 1) (T : ℝ≥0) :
    Integrable (fun p : ℝ × Joint d => X p.1.toNNReal p.2 ^ 2)
      ((volume.restrict (Ioc (0 : ℝ) (T : ℝ))).prod (copies beta μ)) := by
  have hp : IsStronglyProgressive ContinuousCopyBrownian.joinedFiltration
      (fun t q => X t q ^ 2) := fun t => (hX t).pow 2
  have h := integrable_nnreal_process_interval_of_progressive_bounded
    (P := copies beta μ) hp 1
    (fun t => Eventually.of_forall fun q => by
      rw [abs_of_nonneg (sq_nonneg _)]
      nlinarith [hb t q, neg_abs_le (X t q), le_abs_self (X t q)]) 0 T
  simpa only [NNReal.coe_zero] using h

theorem response_energy_summable (hd : 3 ≤ d)
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hb : 0 ≤ beta)
    (hcrit : ((d - 1 : ℕ) : ℝ) * Real.tanh beta ^ 2 ≤ 1)
    (j : Bool) (T : ℝ≥0) :
    Summable (fun v => ∫ s in (0 : ℝ)..(T : ℝ), ∫ q,
      response hb j v s.toNNReal q ^ 2 ∂copies beta μ) := by
  obtain ⟨hs, hi⟩ := response_row_energy hd hμ hb hcrit j T
  have h := (DiscrepancyEnergy.hasSum_integral_sq_row
    (fun v => (real_measurable (response_progressive hb j v)).aestronglyMeasurable) hs hi).summable
  have he (v : TreeVertex d) :
      (∫ p : ℝ × Joint d, response hb j v p.1.toNNReal p.2 ^ 2
        ∂(volume.restrict (Ioc (0 : ℝ) (T : ℝ))).prod (copies beta μ)) =
      ∫ s in (0 : ℝ)..(T : ℝ), ∫ q, response hb j v s.toNNReal q ^ 2 ∂copies beta μ := by
    rw [integral_prod _ (sq_time_integrable (response_progressive hb j v)
      (response_abs_le_one hb j v) T), intervalIntegral.integral_of_le T.coe_nonneg]
  simpa only [he] using h

end Problem367.IsingContinuousCopyCoefficients

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Ising_JoinedResponseIntegrals
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped NNReal Topology

namespace Problem367.IsingJoinedResponseIntegrals
open IsingObservationInnovation IsingObservationFactor IsingCopyEnergy
open IsingContinuousCopyCoefficients BrownianArrayFiltration

variable {d : ℕ} {beta : ℝ}

theorem exists_integrals_oai
    {μ : Measure (TreeVertex d → IsingSpin)} [IsProbabilityMeasure μ]
    (hd : 3 ≤ d) (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hb : 0 ≤ beta)
    (hcrit : ((d - 1 : ℕ) : ℝ) * Real.tanh beta ^ 2 ≤ 1) :
    Nonempty (IntegralSystem hb μ) := by
  have hB (v : TreeVertex d) := (IsingCopyBrownian.commonNoise_isBrownianReal hμ v).toIsPreBrownianReal
  have hBc (v : TreeVertex d) : ∀ᵐ q ∂copies beta μ,
      Continuous (fun t => q.1 v t) :=
    (IsingCopyBrownian.commonNoise_isBrownianReal hμ v).cont
  have hpast (s t : ℝ≥0) (hst : s ≤ t) :=
    IsingCopyBrownian.increment_indep_joinedFiltration hμ hst
  have hind (s t : ℝ≥0) (_hst : s ≤ t) : Pairwise fun v w =>
      IndepFun (fun q : Joint d => q.1 v t - q.1 v s)
        (fun q : Joint d => q.1 w t - q.1 w s) (copies beta μ) :=
    fun _ _ hvw => IsingCopyBrownian.commonNoise_increments_indep hμ s t hvw
  have hex (j : Bool) := exists_global_continuous_spatial_integral_compensatedSquare
    hB IsingCopyBrownian.commonNoise_stronglyAdapted hpast hind hBc
    (fun v => (response_progressive hb j v).stronglyAdapted)
    (response_continuous_ae hd hμ hb hcrit j)
    (C := fun _ => (1 : ℝ)) (fun _ => zero_le_one)
    (fun v => Eventually.of_forall (fun q t => response_abs_le_one hb j v t q))
    (fun N => by simpa only [NNReal.coe_natCast] using
      response_energy_summable hd hμ hb hcrit j (N : ℝ≥0))
  choose I Y hI2 hY2 hI hlim hYp hYM hYc hY0 hYiso hYsum hYmax hYQ hYA hYseries using hex
  have hdiff := difference_compensatedSquare_of_spatial_integral_limits
    hB IsingCopyBrownian.commonNoise_stronglyAdapted hpast hind hBc
    (response_progressive hb true) (response_progressive hb false)
    (response_continuous_ae hd hμ hb hcrit true)
    (response_continuous_ae hd hμ hb hcrit false)
    (C := fun _ => (1 : ℝ)) (D := fun _ => (1 : ℝ))
    (fun _ => zero_le_one) (fun _ => zero_le_one)
    (fun v => Eventually.of_forall (fun q t => response_abs_le_one hb true v t q))
    (fun v => Eventually.of_forall (fun q t => response_abs_le_one hb false v t q))
    (fun N => by simpa only [NNReal.coe_natCast] using
      response_energy_summable hd hμ hb hcrit true (N : ℝ≥0))
    (fun N => by simpa only [NNReal.coe_natCast] using
      response_energy_summable hd hμ hb hcrit false (N : ℝ≥0))
    (hI2 true) (hI2 false) (hYM true).stronglyAdapted (hYM false).stronglyAdapted
    (hY2 true) (hY2 false) (hlim true) (hlim false) (hYsum true) (hYsum false)
  exact ⟨{
    channel := I
    total := Y
    channel_memLp := hI2
    total_memLp := hY2
    channel_predictable := fun j v => (hI j v).1
    channel_martingale := fun j v => (hI j v).2.1
    channel_continuous := fun j v => (hI j v).2.2
    channel_limit := hlim
    total_predictable := hYp
    total_martingale := hYM
    total_continuous := hYc
    total_zero := hY0
    total_sum := hYsum
    difference_compensatedSquare := hdiff.2 }⟩

end Problem367.IsingJoinedResponseIntegrals

end

end OAI
end

theorem solution : type_of% @OAI.Problem367.IsingJoinedResponseIntegrals.exists_integrals_oai := @OAI.Problem367.IsingJoinedResponseIntegrals.exists_integrals_oai
