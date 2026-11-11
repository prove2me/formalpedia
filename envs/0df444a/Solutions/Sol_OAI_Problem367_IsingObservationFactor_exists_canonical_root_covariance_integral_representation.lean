-- Prove2me | solution 1 for OAI.Problem367.IsingObservationFactor.exists_canonical_root_covariance_integral_representation
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T01:48:35.125435+00:00
-- url     : https://prove2.me/submissions/d726cb15-3cb5-4ab8-9266-e723cf7ab6f8

import Mathlib
import Mathlib.MeasureTheory.Integral.Marginal
import Definitions.Def_FreeIsing
import Definitions.Def_Q243FI005
import Theorems.Thm_OAI_Problem367_BrownianIntegralProcess_exists_global_continuous_uniform_integral
import Theorems.Thm_OAI_Problem367_IsingInnovation_exists_continuous_posterior
import Theorems.Thm_OAI_Problem367_IsingInnovation_exists_posterior_integral_representation
import Theorems.Thm_OAI_Problem367_IsingObservationFactor_continuousRootCovariance_uniformObservation_eq_covariance_ae

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

theorem toLp_finsetSum {Ω ι : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    (f : ι → Ω → ℝ) (hf : ∀ i, MemLp (f i) 2 μ) (s : Finset ι) :
    (memLp_finsetSum s (fun i _ => hf i)).toLp (fun ω => ∑ i ∈ s, f i ω) =
      ∑ i ∈ s, (hf i).toLp (f i) := by
  apply Lp.ext
  apply (MemLp.coeFn_toLp _).trans
  apply Filter.EventuallyEq.symm
  apply (Lp.coeFn_fun_finsetSum s (fun i => (hf i).toLp (f i))).trans
  have heq : ∀ᵐ ω ∂μ, ∀ i ∈ s, (hf i).toLp (f i) ω = f i ω :=
    (Filter.eventually_all_finite s.finite_toSet).mpr (fun i _ => (hf i).coeFn_toLp)
  filter_upwards [heq] with ω hω
  exact Finset.sum_congr rfl (fun i hi => hω i hi)

theorem tendsto_integral_sq_error_of_hasSum
    {Ω ι : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    (f : ι → Ω → ℝ) (hf : ∀ i, MemLp (f i) 2 μ)
    {Y : Ω → ℝ} (hY : MemLp Y 2 μ)
    (hYsum : HasSum (fun i => (hf i).toLp (f i)) (hY.toLp Y)) :
    Tendsto (fun s : Finset ι => ∫ ω, ((∑ i ∈ s, f i ω) - Y ω) ^ 2 ∂μ)
      atTop (𝓝 0) := by
  have h := ((hYsum.sub_const (hY.toLp Y)).norm).pow 2
  change Tendsto _ atTop _ at h
  simp only [sub_self, norm_zero, zero_pow (by decide : 2 ≠ 0)] at h
  convert h using 1
  all_goals try with_reducible_and_instances rfl
  funext s
  calc
    _ = ‖((memLp_finsetSum s (fun i _ => hf i)).sub hY).toLp
        ((fun ω => ∑ i ∈ s, f i ω) - Y)‖ ^ 2 :=
      (norm_toLp_sq ((memLp_finsetSum s (fun i _ => hf i)).sub hY)).symm
    _ = _ := by
      change ‖(memLp_finsetSum s (fun i _ => hf i)).toLp
        (fun ω => ∑ i ∈ s, f i ω) - hY.toLp Y‖ ^ 2 = _
      rw [toLp_finsetSum]

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
-- module Solutions.Q243_FreeIsing.FreeIsing_Brownian_CoefficientApproximationIdentification
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal Topology

namespace Problem367.BrownianFiltrationGrid

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {B : ℝ≥0 → Ω → ℝ} {F : Filtration ℝ≥0 mΩ}
    (hB : IsPreBrownianReal B P) (hAd : StronglyAdapted F B)
    (hind : ∀ s t, s ≤ t → Indep
      (MeasurableSpace.comap (fun ω => B t ω - B s ω) inferInstance) (F s) P)
    (K : ℕ → ℝ≥0 → Ω → ℝ) (H : ℝ≥0 → Ω → ℝ)
    (hK : ∀ n, StronglyAdapted F (K n)) (hH : StronglyAdapted F H)
    (hcK : ∀ n, ∀ᵐ ω ∂P, Continuous (fun t => K n t ω))
    (hcH : ∀ᵐ ω ∂P, Continuous (fun t => H t ω))
    (C : ℕ → ℝ) (D : ℝ) (hC : ∀ n, 0 ≤ C n) (hD : 0 ≤ D)
    (hbK : ∀ n, ∀ᵐ ω ∂P, ∀ t, |K n t ω| ≤ C n)
    (hbH : ∀ᵐ ω ∂P, ∀ t, |H t ω| ≤ D)
    (T : ℝ≥0) {X : ℕ → Ω → ℝ} {J : Ω → ℝ}
    (hX : ∀ n, MemLp (X n) 2 P) (hJ : MemLp J 2 P)
    (haX : ∀ n, Tendsto (fun k => ∫ ω,
      (BrownianGrid.uniformSum B (K n) T k ω - X n ω) ^ 2 ∂P) atTop (𝓝 0))
    (haJ : Tendsto (fun k => ∫ ω,
      (BrownianGrid.uniformSum B H T k ω - J ω) ^ 2 ∂P) atTop (𝓝 0))

include hB hAd hind hK hH hcK hcH hC hD hbK hbH hX hJ haX haJ

theorem tendsto_meanSquare_of_coefficient_interval
    (hcoeff : Tendsto (fun n => ∫ t in (0 : ℝ)..(T : ℝ), ∫ ω,
      (K n t.toNNReal ω - H t.toNNReal ω) ^ 2 ∂P) atTop (𝓝 0)) :
    Tendsto (fun n => ∫ ω, (X n ω - J ω) ^ 2 ∂P) atTop (𝓝 0) := by
  have he (n : ℕ) := uniform_meanSquare_difference_isometry
    hB hAd hind (K n) H (hK n) hH (hcK n) hcH (hC n) hD
    (hbK n) hbH T (hX n) hJ (haX n) haJ
  simpa only [he] using hcoeff

end Problem367.BrownianFiltrationGrid

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Martingales_SquareMaximal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Filter
open scoped NNReal ENNReal

namespace Problem367.MartingaleSquareMaximal

variable {Ω ι : Type*} [mΩ : MeasurableSpace Ω] [Preorder ι]
  {μ : Measure Ω} {F : Filtration ι mΩ} {M : ι → Ω → ℝ}

theorem submartingale_sq (hM : Martingale M F μ)
    (h2 : ∀ t, MemLp (M t) 2 μ) :
    Submartingale (fun t ω => M t ω ^ 2) F μ := by
  refine ⟨fun t => (hM.stronglyMeasurable t).pow 2, ?_, fun t => (h2 t).integrable_sq⟩
  intro s t hst
  have hint : Integrable (fun ω => ‖M t ω‖ ^ (2 : ℝ)) μ := by
    simpa only [Real.rpow_two, Real.norm_eq_abs, sq_abs] using (h2 t).integrable_sq
  have hj := Integrable.norm_condExp_rpow_le (m := F s) (by norm_num : (1 : ℝ) ≤ 2) hint
  have hj' : (fun ω => μ[M t | F s] ω ^ 2) ≤ᵐ[μ]
      μ[(fun ω => M t ω ^ 2) | F s] := by
    simpa only [Real.rpow_two, Real.norm_eq_abs, sq_abs] using hj
  filter_upwards [hj', hM.condExp_ae_eq hst] with ω hω heq
  simpa only [heq] using hω

theorem integral_sq_le [IsFiniteMeasure μ]
    (hM : Martingale M F μ) (h2 : ∀ t, MemLp (M t) 2 μ)
    {s t : ι} (hst : s ≤ t) :
    (∫ ω, M s ω ^ 2 ∂μ) ≤ ∫ ω, M t ω ^ 2 ∂μ := by
  have hs := submartingale_sq hM h2
  calc
    _ ≤ ∫ ω, μ[(fun ω => M t ω ^ 2) | F s] ω ∂μ :=
      integral_mono_ae (h2 s).integrable_sq integrable_condExp (hs.2.1 s t hst)
    _ = _ := integral_condExp (F.le s)

end Problem367.MartingaleSquareMaximal

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
-- module Solutions.Q243_FreeIsing.FreeIsing_Brownian_IntegralTransport
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory Filter TopologicalSpace
open scoped NNReal Topology

namespace Problem367.BrownianGrid

theorem integral_sq_sub_comp
    {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    {P : Measure Ω} {Q : Measure Ω'} {φ : Ω' → Ω}
    (hφ : MeasurePreserving φ Q P) {X I : Ω → ℝ}
    (hX : AEStronglyMeasurable X P) (hI : AEStronglyMeasurable I P) :
    (∫ ω, (X (φ ω) - I (φ ω)) ^ 2 ∂Q) =
      ∫ ω, (X ω - I ω) ^ 2 ∂P := by
  have hm : AEStronglyMeasurable (fun ω => (X ω - I ω) ^ 2) (Q.map φ) := by
    rw [hφ.map_eq]
    exact (hX.sub hI).pow 2
  simpa only [hφ.map_eq] using (integral_map hφ.aemeasurable hm).symm

theorem meanSquare_limit_comp
    {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    {P : Measure Ω} {Q : Measure Ω'} {φ : Ω' → Ω}
    (hφ : MeasurePreserving φ Q P) {X : ℕ → Ω → ℝ} {I : Ω → ℝ}
    (hX : ∀ n, AEStronglyMeasurable (X n) P) (hI : AEStronglyMeasurable I P)
    (hlim : Tendsto (fun n => ∫ ω, (X n ω - I ω) ^ 2 ∂P) atTop (𝓝 0)) :
    Tendsto (fun n => ∫ ω, (X n (φ ω) - I (φ ω)) ^ 2 ∂Q) atTop (𝓝 0) := by
  have heq : (fun n => ∫ ω, (X n (φ ω) - I (φ ω)) ^ 2 ∂Q) =
      (fun n => ∫ ω, (X n ω - I ω) ^ 2 ∂P) :=
    funext (fun n => integral_sq_sub_comp hφ (hX n) hI)
  rw [heq]
  exact hlim

end Problem367.BrownianGrid

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Posterior_FilteringRepresentationClosure
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators

namespace Problem367.FilteringRepresentationClosure

section RandomVariables

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

theorem tendsto_toLp_of_integral_sq_error
    {α : Type*} {l : Filter α} {F : α → Ω → ℝ} {Y : Ω → ℝ}
    (hF : ∀ n, MemLp (F n) 2 μ) (hY : MemLp Y 2 μ)
    (hlim : Tendsto (fun n => ∫ ω, (F n ω - Y ω) ^ 2 ∂μ) l (𝓝 0)) :
    Tendsto (fun n => (hF n).toLp (F n)) l (𝓝 (hY.toLp Y)) := by
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  have heq (n : α) : (∫ ω, (F n ω - Y ω) ^ 2 ∂μ) =
      ‖(hF n).toLp (F n) - hY.toLp Y‖ ^ 2 := by
    exact (PredictableL2.norm_toLp_sq ((hF n).sub hY)).symm
  have h := hlim.sqrt
  simpa only [heq, Real.sqrt_sq (norm_nonneg _), Real.sqrt_zero] using h

end RandomVariables

end Problem367.FilteringRepresentationClosure

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Brownian_MeanSquareDescent
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators

namespace Problem367.BrownianGrid

variable {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
  {P : Measure Ω} {Q : Measure Ω'} {φ : Ω' → Ω}

theorem meanSquare_limit_comp_iff
    {α : Type*} {l : Filter α}
    (hφ : MeasurePreserving φ Q P) {X : α → Ω → ℝ} {I : Ω → ℝ}
    (hX : ∀ a, AEStronglyMeasurable (X a) P)
    (hI : AEStronglyMeasurable I P) :
    Tendsto (fun a => ∫ ω, (X a (φ ω) - I (φ ω)) ^ 2 ∂Q) l (𝓝 0) ↔
      Tendsto (fun a => ∫ ω, (X a ω - I ω) ^ 2 ∂P) l (𝓝 0) := by
  have heq : (fun a => ∫ ω, (X a (φ ω) - I (φ ω)) ^ 2 ∂Q) =
      (fun a => ∫ ω, (X a ω - I ω) ^ 2 ∂P) :=
    funext (fun a => integral_sq_sub_comp hφ (hX a) hI)
  rw [heq]

theorem meanSquare_limit_iff_of_comp_ae
    {α : Type*} {l : Filter α}
    (hφ : MeasurePreserving φ Q P)
    {X : α → Ω → ℝ} {I : Ω → ℝ}
    {Y : α → Ω' → ℝ} {J : Ω' → ℝ}
    (hX : ∀ a, AEStronglyMeasurable (X a) P)
    (hI : AEStronglyMeasurable I P)
    (hY : ∀ a, Y a =ᵐ[Q] X a ∘ φ) (hJ : J =ᵐ[Q] I ∘ φ) :
    Tendsto (fun a => ∫ ω, (Y a ω - J ω) ^ 2 ∂Q) l (𝓝 0) ↔
      Tendsto (fun a => ∫ ω, (X a ω - I ω) ^ 2 ∂P) l (𝓝 0) := by
  have heq : (fun a => ∫ ω, (Y a ω - J ω) ^ 2 ∂Q) =
      (fun a => ∫ ω, (X a (φ ω) - I (φ ω)) ^ 2 ∂Q) := by
    funext a
    apply integral_congr_ae
    filter_upwards [hY a, hJ] with ω hω hωJ
    simp only [hω, hωJ, Function.comp_apply]
  rw [heq]
  exact meanSquare_limit_comp_iff hφ hX hI

end Problem367.BrownianGrid

namespace Problem367.PredictableL2

theorem hasSum_toLp_iff_meanSquare
    {Ω ι : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    (f : ι → Ω → ℝ) (hf : ∀ i, MemLp (f i) 2 P)
    {Y : Ω → ℝ} (hY : MemLp Y 2 P) :
    HasSum (fun i => (hf i).toLp (f i)) (hY.toLp Y) ↔
      Tendsto (fun s : Finset ι => ∫ ω,
        ((∑ i ∈ s, f i ω) - Y ω) ^ 2 ∂P) atTop (𝓝 0) := by
  constructor
  · exact tendsto_integral_sq_error_of_hasSum f hf hY
  · intro hlim
    have h := FilteringRepresentationClosure.tendsto_toLp_of_integral_sq_error
      (fun s : Finset ι => memLp_finsetSum s (fun i _ => hf i)) hY hlim
    change Tendsto (fun s : Finset ι => ∑ i ∈ s, (hf i).toLp (f i))
      atTop (𝓝 (hY.toLp Y))
    convert h using 1
    all_goals try with_reducible_and_instances rfl
    funext s
    exact (toLp_finsetSum f hf s).symm

theorem hasSum_toLp_descend_of_comp_ae
    {Ω Ω' ι : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    {P : Measure Ω} {Q : Measure Ω'} {φ : Ω' → Ω}
    (hφ : MeasurePreserving φ Q P)
    (f : ι → Ω → ℝ) (hf : ∀ i, MemLp (f i) 2 P)
    {Y : Ω → ℝ} (hY : MemLp Y 2 P)
    (g : ι → Ω' → ℝ) (hg : ∀ i, MemLp (g i) 2 Q)
    {Z : Ω' → ℝ} (hZ : MemLp Z 2 Q)
    (hfg : ∀ i, g i =ᵐ[Q] f i ∘ φ) (hYZ : Z =ᵐ[Q] Y ∘ φ)
    (hsum : HasSum (fun i => (hg i).toLp (g i)) (hZ.toLp Z)) :
    HasSum (fun i => (hf i).toLp (f i)) (hY.toLp Y) := by
  apply (hasSum_toLp_iff_meanSquare f hf hY).mpr
  apply (BrownianGrid.meanSquare_limit_iff_of_comp_ae hφ
    (fun s : Finset ι => (memLp_finsetSum s (fun i _ => hf i)).aestronglyMeasurable)
    hY.aestronglyMeasurable (Y := fun s ω => ∑ i ∈ s, g i ω)
    (J := Z) ?_ hYZ).mp
  · exact tendsto_integral_sq_error_of_hasSum g hg hZ hsum
  · intro s
    have hall : ∀ᵐ ω ∂Q, ∀ i ∈ s, g i ω = f i (φ ω) :=
      (Filter.eventually_all_finite s.finite_toSet).mpr (fun i _ => hfg i)
    filter_upwards [hall] with ω hω
    exact Finset.sum_congr rfl (fun i hi => hω i hi)

end Problem367.PredictableL2

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
-- module Solutions.Q243_FreeIsing.FreeIsing_Posterior_Limit
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology

namespace Problem367

theorem tendsto_conditional_covariance_ae
    {Ω : Type*} [m : MeasurableSpace Ω] (μ : Measure Ω) [IsFiniteMeasure μ]
    (ℱ : Filtration ℕ m) (f g : Ω → ℝ) :
    ∀ᵐ ω ∂μ, Tendsto
      (fun n => (μ[fun x => f x * g x | ℱ n]) ω -
        (μ[f | ℱ n]) ω * (μ[g | ℱ n]) ω)
      atTop (𝓝 ((μ[fun x => f x * g x | ⨆ n, ℱ n]) ω -
        (μ[f | ⨆ n, ℱ n]) ω * (μ[g | ⨆ n, ℱ n]) ω)) := by
  filter_upwards [tendsto_ae_condExp (μ := μ) (ℱ := ℱ) (fun x => f x * g x),
    tendsto_ae_condExp (μ := μ) (ℱ := ℱ) f,
    tendsto_ae_condExp (μ := μ) (ℱ := ℱ) g] with ω hfg hf hg
  exact hfg.sub (hf.mul hg)

end Problem367

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
-- module Solutions.Q243_FreeIsing.FreeIsing_Brownian_PosteriorField
attribute [-instance] _root_.OAI.Problem367.IsingConditionalCopyBounds.graphLaw_isProbabilityMeasure _root_.OAI.Problem367.IsingObservationFactor.copies_probability _root_.OAI.Problem367.IsingObservationFactor.kernel_markov _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_observationLaw_probability _root_.OAI.Problem367.IsingObservationInnovation.observationLaw_probability _root_.OAI.Problem367.TreeKoopman.labelProbability _root_.OAI.Problem367.WienerSampler.pathMeasurableSpace _root_.OAI.Problem367.freeIsingMeasure_probability
attribute [-simp] _root_.OAI.Problem367.ConnectedHull.pathAssignment_path _root_.OAI.Problem367.ConnectedHull.path_last _root_.OAI.Problem367.ConnectedHull.path_zero _root_.OAI.Problem367.CutContinuationChannels.averageChannel_globalCone _root_.OAI.Problem367.CutContinuationChannels.continuationChannel_globalCone _root_.OAI.Problem367.FactorObservable.centeredSpinLp_coe _root_.OAI.Problem367.FiniteIsingSplit.splitEquiv_fst _root_.OAI.Problem367.FiniteIsingSplit.splitEquiv_snd _root_.OAI.Problem367.FinitePathGibbs.tailPartition_zero _root_.OAI.Problem367.GaussianTreeResponseNaturality.fieldEquiv_apply_image _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_apply _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_uniformObservation _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_zero _root_.OAI.Problem367.IsingObservationInnovation.uniformObservation_relabel _root_.OAI.Problem367.IsingOrientedPath.attenuation_outward _root_.OAI.Problem367.IsingOrientedPath.endpoint_extensionAt _root_.OAI.Problem367.LocalSupportGeometry.prefixVertex_length _root_.OAI.Problem367.PathSideBranches.parent_sideVertex _root_.OAI.Problem367.PathSideBranches.restrictNoisyRegion_array _root_.OAI.Problem367.PathSideBranches.sideVertex_length _root_.OAI.Problem367.PathSideBranches.sideVertex_val _root_.OAI.Problem367.PosteriorChain.transition_spinMean _root_.OAI.Problem367.PosteriorChain.transition_sum _root_.OAI.Problem367.RootedBroadcast.flipBranchToComplement_val _root_.OAI.Problem367.RootedBroadcast.pos_spinMul _root_.OAI.Problem367.RootedBroadcast.prefixFlip_branchRoot _root_.OAI.Problem367.RootedBroadcast.prefixFlip_root _root_.OAI.Problem367.RootedBroadcast.prefixTreeAut_symm_branchRoot _root_.OAI.Problem367.RootedBroadcast.prefixTreeAut_symm_root _root_.OAI.Problem367.RootedBroadcast.spinMul_pos _root_.OAI.Problem367.RootedBroadcast.spinMul_self _root_.OAI.Problem367.TreeConeCoding.length_vertex _root_.OAI.Problem367.TreeConeCoding.vertex_nil _root_.OAI.Problem367.TreeConeCoding.vertex_val _root_.OAI.Problem367.TreeGibbsAut.spinEquiv_apply_image _root_.OAI.Problem367.TreeKoopman.centeredAverage_apply_coe _root_.OAI.Problem367.TreeKoopman.centeredAverage_pow_apply_coe _root_.OAI.Problem367.TreeKoopman.centeredGenerator_apply_coe _root_.OAI.Problem367.TreeKoopman.centeredGenerator_sq _root_.OAI.Problem367.TreeKoopman.generatorOperator_sq _root_.OAI.Problem367.TreeKoopman.reverseVertex_twice _root_.OAI.Problem367.TreeKoopman.wordRelabel_cons _root_.OAI.Problem367.TreeKoopman.wordRelabel_nil _root_.OAI.Problem367.TreeLawKoopman.centeredAverage_apply_coe _root_.OAI.Problem367.TreeLawKoopman.generatorOperator_sq _root_.OAI.Problem367.TreePathGibbs.vertexEquiv_val _root_.OAI.Problem367.branchColorAut_length _root_.OAI.Problem367.branchColorAut_singleton _root_.OAI.Problem367.branchColorAut_val _root_.OAI.Problem367.branchColorMap_symm_apply _root_.OAI.Problem367.colorPermAut_length _root_.OAI.Problem367.colorPermAut_nil _root_.OAI.Problem367.colorPermAut_val _root_.OAI.Problem367.colorPermMap_symm_apply _root_.OAI.Problem367.colorPermMap_val _root_.OAI.Problem367.connectedSpinEncode_apply_root _root_.OAI.Problem367.connectedSpinEquiv_apply _root_.OAI.Problem367.dropVertex_length _root_.OAI.Problem367.dropVertex_val _root_.OAI.Problem367.mem_rootComplementFinset _root_.OAI.Problem367.mem_rootComponentFinset _root_.OAI.Problem367.mem_rootComponentIndices _root_.OAI.Problem367.parentVertex_length _root_.OAI.Problem367.parentVertex_val _root_.OAI.Problem367.prefixColorAut_length _root_.OAI.Problem367.prefixColorAut_val _root_.OAI.Problem367.prefixColorMap_symm_apply _root_.OAI.Problem367.prefixFlip_twice _root_.OAI.Problem367.spinAgreementCode_eq_neg_iff _root_.OAI.Problem367.spinAgreementCode_eq_pos_iff _root_.OAI.Problem367.spinSign_flip _root_.OAI.Problem367.tsum_treeShell_radial _root_.OAI.Problem367.vertexSampler_relabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace Problem367

open PlantedSymmetry

theorem HasFreeIsingLaw.brownian_past_posterior_field_bound
    {d : ℕ} {beta : ℝ} {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure (TreeVertex d → IsingSpin)}
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hbeta : 0 ≤ beta)
    (ν : TreeVertex d → Measure Ω)
    {B : TreeVertex d → ℝ≥0 → Ω → ℝ}
    (hB : ∀ i, IsPreBrownianReal (B i) (ν i))
    (hmB : ∀ i t, Measurable (B i t)) (t : ℝ≥0) (v : TreeVertex d) :
    let ρ := μ.prod (Measure.infinitePi ν)
    let m := ρ[fun p => spinSign (p.1 v) |
      MeasurableSpace.comap
        (fun p : (TreeVertex d → IsingSpin) × (TreeVertex d → Ω) =>
          fun i (s : Set.Iic t) => (s.1 : ℝ) * spinSign (p.1 i) + B i s.1 (p.2 i))
        inferInstance]
    ∀ᵐ p ∂ρ, m p ∈ Set.Ioo (-1 : ℝ) 1 ∧
      |Real.artanh (m p) - ((t : ℝ) * spinSign (p.1 v) + B v t (p.2 v))| ≤
        (d : ℝ) * beta := by
  let : IsProbabilityMeasure μ := hμ.isProbabilityMeasure
  have (i : TreeVertex d) : IsProbabilityMeasure (ν i) :=
    (hB i).isGaussianProcess.isProbabilityMeasure
  let T : ((TreeVertex d → IsingSpin) × (TreeVertex d → Ω)) →
      (TreeVertex d → IsingSpin) × (TreeVertex d → ℝ) :=
    Prod.map id (fun ω i => B i t (ω i))
  have hT : MeasurePreserving T (μ.prod (Measure.infinitePi ν))
      (μ.prod (gaussianNoiseLaw (TreeVertex d) t)) :=
    (MeasurePreserving.id μ).prod (brownian_array_eval_measurePreserving ν hB hmB t)
  have hsign : Measurable spinSign := by intro s hs; trivial
  have hspin : Measurable (fun sigma : TreeVertex d → IsingSpin => spinSign (sigma v)) :=
    hsign.comp (measurable_pi_apply v)
  have hspini : Integrable (fun sigma : TreeVertex d → IsingSpin => spinSign (sigma v)) μ := by
    apply Integrable.of_bound hspin.aestronglyMeasurable 1
    apply Filter.Eventually.of_forall
    intro sigma
    cases hs : sigma v <;> norm_num [spinSign, hs]
  have hpull := condExp_comp_measurePreserving_comap hT
    (hspin.comp measurable_fst).stronglyMeasurable
    (integrable_plantedSpin (μ.prod (gaussianNoiseLaw (TreeVertex d) t)) v)
    (observationSigma_le (TreeVertex d) t)
  have hpast := TerminalSufficiency.condExp_planted_infinite_past_eq_terminal
    μ ν hB hmB (fun sigma i => spinSign (sigma i))
    (fun sigma => spinSign (sigma v))
    (Measurable.of_eval (fun i => hsign.comp (measurable_pi_apply i))) hspin hspini t
  have hb := hμ.gaussian_posterior_field_bound hbeta t v
  rw [← hT.map_eq] at hb
  have hb' := ae_of_ae_map hT.measurable.aemeasurable hb
  rw [hT.map_eq] at hb'
  dsimp only
  filter_upwards [hpast, hpull, hb'] with p hpast hpull hb
  change _ = posteriorMagnetization (μ.prod (gaussianNoiseLaw (TreeVertex d) t)) t v (T p)
    at hpull
  have hsame : (observationSigma (TreeVertex d) (t : ℝ)).comap T =
      MeasurableSpace.comap
        (fun p : (TreeVertex d → IsingSpin) × (TreeVertex d → Ω) =>
          fun i => (t : ℝ) * spinSign (p.1 i) + B i t (p.2 i)) inferInstance := by
    rw [observationSigma, MeasurableSpace.comap_comp]
    rfl
  rw [hsame] at hpull
  simp only [Function.comp_def, T, Prod.map_fst, id_eq] at hpull
  rw [hpast, hpull]
  exact hb

end Problem367

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Conditioning_CovarianceLimit
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

variable {Ω : Type*} [mΩ : MeasurableSpace Ω]

theorem tendsto_ae_posteriorCovariance (μ : Measure Ω) [IsFiniteMeasure μ]
    (F : Filtration ℕ mΩ) (f g : Ω → ℝ) :
    ∀ᵐ ω ∂μ, Tendsto (fun n => posteriorCovariance μ (F n) f g ω) atTop
      (𝓝 (posteriorCovariance μ (⨆ n, F n) f g ω)) := by
  exact tendsto_conditional_covariance_ae μ F f g

theorem tendsto_integral_sq_sub_of_bounded_ae
    (μ : Measure Ω) [IsFiniteMeasure μ] {X : ℕ → Ω → ℝ} {Y : Ω → ℝ}
    (hX : ∀ n, AEStronglyMeasurable (X n) μ) (hY : AEStronglyMeasurable Y μ)
    {R : ℝ} (hR : 0 ≤ R)
    (hbX : ∀ n, ∀ᵐ ω ∂μ, ‖X n ω‖ ≤ R)
    (hbY : ∀ᵐ ω ∂μ, ‖Y ω‖ ≤ R)
    (hlim : ∀ᵐ ω ∂μ, Tendsto (fun n => X n ω) atTop (𝓝 (Y ω))) :
    Tendsto (fun n => ∫ ω, (X n ω - Y ω) ^ 2 ∂μ) atTop (𝓝 0) := by
  have hbound (n : ℕ) : ∀ᵐ ω ∂μ, ‖(X n ω - Y ω) ^ 2‖ ≤ (2 * R) ^ 2 := by
    filter_upwards [hbX n, hbY] with ω hx hy
    have hdiff : ‖X n ω - Y ω‖ ≤ 2 * R := by
      calc
        ‖X n ω - Y ω‖ ≤ ‖X n ω‖ + ‖Y ω‖ := norm_sub_le _ _
        _ ≤ 2 * R := by linarith
    rw [norm_pow]
    nlinarith [norm_nonneg (X n ω - Y ω)]
  have ht := tendsto_integral_of_dominated_convergence (μ := μ)
    (fun _ : Ω => (2 * R) ^ 2)
    (fun n => ((hX n).sub hY).pow 2) (integrable_const _) hbound
    (hlim.mono (fun ω hω => by
      simpa using (hω.sub tendsto_const_nhds).pow 2))
  simpa using ht

theorem tendsto_integral_prod_sq_sub_of_bounded_ae
    {T : Type*} [MeasurableSpace T]
    (ν : Measure T) (μ : Measure Ω) [IsFiniteMeasure ν] [IsFiniteMeasure μ]
    {X : ℕ → T × Ω → ℝ} {Y : T × Ω → ℝ}
    (hX : ∀ n, Measurable (X n)) (hY : Measurable Y)
    {R : ℝ} (hR : 0 ≤ R)
    (hbX : ∀ n, ∀ᵐ t ∂ν, ∀ᵐ ω ∂μ, ‖X n (t, ω)‖ ≤ R)
    (hbY : ∀ᵐ t ∂ν, ∀ᵐ ω ∂μ, ‖Y (t, ω)‖ ≤ R)
    (hlim : ∀ᵐ t ∂ν, ∀ᵐ ω ∂μ,
      Tendsto (fun n => X n (t, ω)) atTop (𝓝 (Y (t, ω)))) :
    Tendsto (fun n => ∫ p, (X n p - Y p) ^ 2 ∂ν.prod μ) atTop (𝓝 0) := by
  apply tendsto_integral_sq_sub_of_bounded_ae (ν.prod μ)
    (fun n => (hX n).aestronglyMeasurable) hY.aestronglyMeasurable hR
  · intro n
    exact (Measure.ae_prod_iff_ae_ae (measurableSet_le (hX n).norm measurable_const)).mpr (hbX n)
  · exact (Measure.ae_prod_iff_ae_ae (measurableSet_le hY.norm measurable_const)).mpr hbY
  · exact (Measure.ae_prod_iff_ae_ae (measurableSet_tendsto_fun hX hY)).mpr hlim

end Problem367

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
-- module Solutions.Q243_FreeIsing.FreeIsing_Posterior_ProgressiveIsingPosterior
attribute [-instance] _root_.OAI.Problem367.IsingConditionalCopyBounds.graphLaw_isProbabilityMeasure _root_.OAI.Problem367.IsingObservationFactor.copies_probability _root_.OAI.Problem367.IsingObservationFactor.kernel_markov _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_observationLaw_probability _root_.OAI.Problem367.IsingObservationInnovation.observationLaw_probability _root_.OAI.Problem367.TreeKoopman.labelProbability _root_.OAI.Problem367.WienerSampler.pathMeasurableSpace _root_.OAI.Problem367.freeIsingMeasure_probability
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

attribute [local instance] OAI.Problem367.progressiveIsingPosteriorNonemptyIsingSpin
theorem HasFreeIsingLaw.infiniteGibbsSpinMean_brownian_field_bound
    {d : ℕ} {beta : ℝ} {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure (TreeVertex d → IsingSpin)}
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hbeta : 0 ≤ beta)
    (ν : TreeVertex d → Measure Ω)
    {B : TreeVertex d → ℝ≥0 → Ω → ℝ}
    (hB : ∀ i, IsPreBrownianReal (B i) (ν i))
    (hmB : ∀ i t, Measurable (B i t)) (t : ℝ≥0) (v : TreeVertex d) :
    ∀ᵐ p ∂μ.prod (Measure.infinitePi ν),
      let y := fun i => (t : ℝ) * spinSign (p.1 i) + B i t (p.2 i)
      infiniteGibbsSpinMean beta v y ∈ Set.Ioo (-1 : ℝ) 1 ∧
        |Real.artanh (infiniteGibbsSpinMean beta v y) - y v| ≤ (d : ℝ) * beta := by
  filter_upwards [hμ.infiniteGibbsSpinMean_eq_brownian_past ν hB hmB t v,
    hμ.brownian_past_posterior_field_bound hbeta ν hB hmB t v] with p heq hb
  dsimp only
  rw [heq]
  exact hb

end Problem367

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

theorem HasFreeIsingLaw.infiniteGibbsCovariance_eq_posterior {d : ℕ} {beta : ℝ}
    {μ : Measure (TreeVertex d → IsingSpin)}
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (t : ℝ≥0) (v w : TreeVertex d) :
    (fun p => infiniteGibbsCovariance beta v w (observation t p)) =ᵐ[
        μ.prod (gaussianNoiseLaw (TreeVertex d) t)]
      posteriorCovariance (μ.prod (gaussianNoiseLaw (TreeVertex d) t))
        (observationSigma (TreeVertex d) t)
        (fun p => spinSign (p.1 v)) (fun p => spinSign (p.1 w)) := by
  filter_upwards [hμ.infiniteGibbsPairMean_eq_posterior t v w,
    hμ.infiniteGibbsSpinMean_eq_posterior t v,
    hμ.infiniteGibbsSpinMean_eq_posterior t w] with p hp hv hw
  exact congrArg₂ (fun a b : ℝ => a - b) hp (congrArg₂ (· * ·) hv hw)

end Problem367

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

theorem measurable_sampledLimit_at [MeasurableSpace Ω]
    {q : T → ℕ → T} {F : T → Ω → ℝ} (t : T)
    (hF : ∀ n, Measurable (F (q t n))) : Measurable (sampledLimit q F t) := by
  exact (StronglyMeasurable.limUnder (fun n => (hF n).stronglyMeasurable)).measurable

theorem ae_all_eq_of_continuous_modification [TopologicalSpace T] [MeasurableSpace Ω]
    {μ : Measure Ω} {q : T → ℕ → T} {F G : T → Ω → ℝ}
    {S : Set T} (hS : S.Countable)
    (hqS : ∀ t n, q t n ∈ S)
    (hq : ∀ t, Tendsto (q t) atTop (𝓝 t))
    (hFG : ∀ s ∈ S, F s =ᵐ[μ] G s)
    (hG : ∀ᵐ ω ∂μ, Continuous (fun t => G t ω)) :
    ∀ᵐ ω ∂μ, ∀ t, sampledLimit q F t ω = G t ω := by
  let : Countable S := hS.to_subtype
  have hEq : ∀ᵐ ω ∂μ, ∀ s : S, F s ω = G s ω :=
    ae_all_iff.mpr (fun s => hFG s s.property)
  filter_upwards [hEq, hG] with ω hEqω hGω
  intro t
  have hseq : (fun n => F (q t n) ω) = (fun n => G (q t n) ω) :=
    funext (fun n => hEqω ⟨q t n, hqS t n⟩)
  unfold sampledLimit
  rw [hseq]
  exact ((hGω.tendsto t).comp (hq t)).limUnder_eq

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

attribute [local instance] OAI.Problem367.ProgressiveVersionPushforward.instMeasurableSpaceContinuousMapNNRealReal_solutions
local instance instBorelSpaceContinuousMapNNRealReal_solutions : BorelSpace C(ℝ≥0, ℝ) := ⟨rfl⟩

lemma leftTime_le (t : ℝ≥0) (n : ℕ) : leftTime t n ≤ t := by
  simpa only [leftTime, Real.toNNReal_coe] using Real.toNNReal_mono (dyadicLeft_le t n)

lemma tendsto_leftTime (t : ℝ≥0) : Tendsto (leftTime t) atTop (𝓝 t) := by
  change Tendsto (fun n => (dyadicLeft (t : ℝ) n).toNNReal) atTop (𝓝 t)
  simpa only [ Function.comp_def, Real.toNNReal_coe] using
    continuous_real_toNNReal.continuousAt.tendsto.comp (tendsto_dyadicLeft (t : ℝ))

lemma leftTime_mem_range (t : ℝ≥0) (n : ℕ) : leftTime t n ∈ range gridTime :=
  ⟨(⌊(2 : ℝ)^n * (t : ℝ)⌋, n), rfl⟩

lemma denseRange_gridTime : DenseRange gridTime := by
  intro t
  exact mem_closure_of_tendsto (tendsto_leftTime t)
    (Eventually.of_forall (leftTime_mem_range t))

lemma measurable_leftTime (n : ℕ) : Measurable (fun t => leftTime t n) := by
  unfold leftTime dyadicLeft
  fun_prop

lemma measurable_version {Ω : Type*} [MeasurableSpace Ω]
    {M : ℝ≥0 → Ω → ℝ} (hm : ∀ t, Measurable (M t)) (t : ℝ≥0) :
    Measurable (version M t) :=
  measurable_sampledLimit_at t (fun n => hm (leftTime t n))

lemma progressive_version {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {F : Filtration ℝ≥0 mΩ} {M : ℝ≥0 → Ω → ℝ}
    (hM : IsStronglyProgressive F M) : IsStronglyProgressive F (version M) := by
  apply isStronglyProgressive_sampledLimit F
  intro n
  apply hM.comp _ (fun t _ => leftTime_le t n)
  intro T
  exact ((measurable_leftTime n).comp measurable_fst.subtype_val).stronglyMeasurable

lemma version_eq_of_grid {Ω : Type*} {M : ℝ≥0 → Ω → ℝ} {ω : Ω}
    (f : C(ℝ≥0, ℝ)) (h : ∀ p, M (gridTime p) ω = f (gridTime p)) :
    ∀ t, version M t ω = f t := by
  intro t
  have he : (fun n => M (leftTime t n) ω) = fun n => f (leftTime t n) := by
    funext n
    exact h (⌊(2 : ℝ)^n * (t : ℝ)⌋, n)
  unfold version sampledLimit
  rw [he]
  exact ((f.continuous.tendsto t).comp (tendsto_leftTime t)).limUnder_eq

lemma ae_all_version_eq {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {M G : ℝ≥0 → Ω → ℝ} (he : ∀ t, M t =ᵐ[μ] G t)
    (hc : ∀ᵐ ω ∂μ, Continuous (fun t => G t ω)) :
    ∀ᵐ ω ∂μ, ∀ t, version M t ω = G t ω := by
  apply ae_all_eq_of_continuous_modification (Set.countable_range gridTime)
    leftTime_mem_range tendsto_leftTime (fun t _ => he t) hc

lemma measurableEmbedding_gridEval : MeasurableEmbedding
    (fun f : C(ℝ≥0, ℝ) => fun p : ℤ × ℕ => f (gridTime p)) := by
  apply Measurable.measurableEmbedding
  · exact Measurable.of_eval (fun _ => (continuous_eval_const _).measurable)
  · intro f g h
    apply ContinuousMap.coe_injective
    exact denseRange_gridTime.equalizer f.continuous g.continuous h

theorem continuous_progressive_version_of_pullback
    {Ω Ξ : Type*} [MeasurableSpace Ω] [mΞ : MeasurableSpace Ξ]
    {μ : Measure Ω} {φ : Ω → Ξ} (hφ : Measurable φ)
    {F : Filtration ℝ≥0 mΞ} {M : ℝ≥0 → Ξ → ℝ}
    (hM : IsStronglyProgressive F M)
    {G : ℝ≥0 → Ω → ℝ}
    (hcG : ∀ᵐ ω ∂μ, Continuous (fun t => G t ω))
    (heG : ∀ t, G t =ᵐ[μ] fun ω => M t (φ ω)) :
    IsStronglyProgressive F (version M) ∧
      (∀ᵐ x ∂μ.map φ, Continuous (fun t => version M t x)) ∧
      (∀ t, version M t =ᵐ[μ.map φ] M t) := by
  have hm (t : ℝ≥0) : Measurable (M t) :=
    ((hM.stronglyAdapted t).mono (F.le t)).measurable
  let samples : Ξ → (ℤ × ℕ → ℝ) := fun x p => M (gridTime p) x
  let encode : C(ℝ≥0, ℝ) → (ℤ × ℕ → ℝ) := fun f p => f (gridTime p)
  have hms : Measurable samples := Measurable.of_eval (fun point => hm (gridTime point))
  have hgoodSet : MeasurableSet {x : Ξ | samples x ∈ range encode} :=
    measurableEmbedding_gridEval.measurableSet_range.preimage hms
  have hgoodPullback : ∀ᵐ ω ∂μ, samples (φ ω) ∈ range encode := by
    have heGrid : ∀ᵐ ω ∂μ, ∀ p : ℤ × ℕ, G (gridTime p) ω = M (gridTime p) (φ ω) :=
      ae_all_iff.mpr (fun p => heG (gridTime p))
    filter_upwards [hcG, heGrid] with ω hc he
    exact ⟨⟨fun t => G t ω, hc⟩, funext he⟩
  have hgood : ∀ᵐ x ∂μ.map φ, samples x ∈ range encode :=
    (ae_map_iff hφ.aemeasurable hgoodSet).mpr hgoodPullback
  have hid : ∀ᵐ ω ∂μ, ∀ t, version M t (φ ω) = G t ω :=
    ae_all_version_eq (fun t => (heG t).symm) hcG
  refine ⟨progressive_version hM, ?_, ?_⟩
  · filter_upwards [hgood] with x hx
    obtain ⟨f, hf⟩ := hx
    have he := version_eq_of_grid f (fun p => (congrFun hf p).symm)
    simpa only [he] using f.continuous
  · intro t
    apply (ae_map_iff hφ.aemeasurable
      (measurableSet_eq_fun (measurable_version hm t) (hm t))).mpr
    filter_upwards [hid, heG t] with ω hi he
    exact (hi t).trans he

end Problem367.ProgressiveVersionPushforward

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Gaussian_NoiseSlope
attribute [-instance] _root_.OAI.Problem367.WienerSampler.pathMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory ProbabilityTheory Filter
open scoped Topology ENNReal NNReal

namespace Problem367

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

theorem ae_tendsto_zero_of_tail_tsum_ne_top (X : ℕ → Ω → ℝ)
    (hX : ∀ ε : ℝ, 0 < ε → (∑' n, μ {ω | ε ≤ |X n ω|}) ≠ ∞) :
    ∀ᵐ ω ∂μ, Tendsto (fun n => X n ω) atTop (𝓝 0) := by
  have hsmall : ∀ k : ℕ, ∀ᵐ ω ∂μ,
      ∀ᶠ n in atTop, |X n ω| < 1 / (k + 1 : ℝ) := by
    intro k
    have h := ae_eventually_notMem (hX (1 / (k + 1 : ℝ)) (by positivity))
    simpa only [Set.mem_ofPred_eq, not_le] using h
  filter_upwards [ae_all_iff.mpr hsmall] with ω hω
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨k, hk⟩ := exists_nat_one_div_lt hε
  obtain ⟨N, hN⟩ := eventually_atTop.mp (hω k)
  exact ⟨N, fun n hn => by simpa [Real.dist_eq] using (hN n hn).trans hk⟩

theorem ae_tendsto_zero_of_summable_tail [IsFiniteMeasure μ] (X : ℕ → Ω → ℝ)
    (hX : ∀ ε : ℝ, 0 < ε → Summable (fun n => μ.real {ω | ε ≤ |X n ω|})) :
    ∀ᵐ ω ∂μ, Tendsto (fun n => X n ω) atTop (𝓝 0) := by
  apply ae_tendsto_zero_of_tail_tsum_ne_top X
  intro ε hε
  have h := (hX ε hε).tsum_ofReal_ne_top
  simpa only [Measure.real, ENNReal.ofReal_toReal (measure_ne_top _ _)] using h

theorem ae_tendsto_zero_of_exp_tail [IsFiniteMeasure μ] (X : ℕ → Ω → ℝ)
    (hX : ∀ ε : ℝ, 0 < ε → ∃ C c : ℝ, 0 < c ∧
      ∀ n, μ.real {ω | ε ≤ |X n ω|} ≤ C * Real.exp (-(n : ℝ) * c)) :
    ∀ᵐ ω ∂μ, Tendsto (fun n => X n ω) atTop (𝓝 0) := by
  apply ae_tendsto_zero_of_summable_tail X
  intro ε hε
  obtain ⟨C, c, hc, hbound⟩ := hX ε hε
  have hsum : Summable (fun n : ℕ => C * Real.exp (-(n : ℝ) * c)) := by
    simpa only [mul_neg, neg_mul] using
      (Real.summable_exp_nat_mul_iff.mpr (neg_neg_of_pos hc)).mul_left C
  exact hsum.of_nonneg_of_le (fun _ => measureReal_nonneg) hbound

theorem subgaussian_abs_tail [IsFiniteMeasure μ] {X : Ω → ℝ} {c : ℝ≥0}
    (hX : HasSubgaussianMGF X c μ) {ε : ℝ} (hε : 0 ≤ ε) :
    μ.real {ω | ε ≤ |X ω|} ≤ 2 * Real.exp (-ε ^ 2 / (2 * c)) := by
  have hset : {ω | ε ≤ |X ω|} = {ω | ε ≤ X ω} ∪ {ω | ε ≤ -X ω} := by
    ext ω
    simpa only [Set.mem_ofPred_eq, Set.mem_union] using (le_abs (a := ε) (b := X ω))
  rw [hset]
  calc
    μ.real ({ω | ε ≤ X ω} ∪ {ω | ε ≤ -X ω}) ≤
        μ.real {ω | ε ≤ X ω} + μ.real {ω | ε ≤ -X ω} := measureReal_union_le _ _
    _ ≤ Real.exp (-ε ^ 2 / (2 * c)) + Real.exp (-ε ^ 2 / (2 * c)) :=
      add_le_add (hX.measure_ge_le hε) (hX.neg.measure_ge_le hε)
    _ = 2 * Real.exp (-ε ^ 2 / (2 * c)) := by ring

theorem ae_tendsto_div_succ_zero_of_subgaussian [IsFiniteMeasure μ]
    (X : ℕ → Ω → ℝ)
    (hX : ∀ n, HasSubgaussianMGF (X n) ((n : ℝ≥0) + 1) μ) :
    ∀ᵐ ω ∂μ, Tendsto (fun n => X n ω / ((n : ℝ) + 1)) atTop (𝓝 0) := by
  apply ae_tendsto_zero_of_exp_tail
  intro ε hε
  refine ⟨2, ε ^ 2 / 2, by positivity, ?_⟩
  intro n
  have hn : 0 < (n : ℝ) + 1 := by positivity
  have hset : {ω | ε ≤ |X n ω / ((n : ℝ) + 1)|} =
      {ω | ε * ((n : ℝ) + 1) ≤ |X n ω|} := by
    ext ω
    simp only [Set.mem_ofPred_eq, abs_div, abs_of_pos hn, le_div_iff₀ hn]
  rw [hset]
  have ht := subgaussian_abs_tail (hX n) (mul_nonneg hε.le hn.le)
  simp only [NNReal.coe_add, NNReal.coe_natCast, NNReal.coe_one] at ht
  refine ht.trans ?_
  have heq : -(ε * ((n : ℝ) + 1)) ^ 2 / (2 * ((n : ℝ) + 1)) =
      -((n : ℝ) + 1) * (ε ^ 2 / 2) := by
    field_simp [ne_of_gt hn]
  rw [heq]
  gcongr
  nlinarith [sq_nonneg ε]

theorem hasSubgaussianMGF_of_hasLaw_gaussian {X : Ω → ℝ} {v : ℝ≥0}
    (hX : HasLaw X (gaussianReal 0 v) μ) : HasSubgaussianMGF X v μ := by
  have hg : HasSubgaussianMGF id v (gaussianReal 0 v) := by
    constructor
    · intro t
      exact integrable_exp_mul_gaussianReal t
    · intro t
      simp [mgf_id_gaussianReal]
  rw [← hX.map_eq] at hg
  simpa only [Function.id_comp] using hg.of_map hX.aemeasurable

theorem ae_brownian_div_succ_tendsto_zero (B : ℝ≥0 → Ω → ℝ)
    (hB : IsPreBrownianReal B μ) :
    ∀ᵐ ω ∂μ, Tendsto (fun n : ℕ => B ((n : ℝ≥0) + 1) ω / ((n : ℝ) + 1))
      atTop (𝓝 0) := by
  let : IsProbabilityMeasure μ := (hB.hasLaw_eval 0).isProbabilityMeasure
  exact ae_tendsto_div_succ_zero_of_subgaussian
    (fun n => B ((n : ℝ≥0) + 1))
    (fun n => hasSubgaussianMGF_of_hasLaw_gaussian (hB.hasLaw_eval _))

theorem ae_brownian_div_nat_tendsto_zero (B : ℝ≥0 → Ω → ℝ)
    (hB : IsPreBrownianReal B μ) :
    ∀ᵐ ω ∂μ, Tendsto (fun n : ℕ => B n ω / (n : ℝ)) atTop (𝓝 0) := by
  filter_upwards [ae_brownian_div_succ_tendsto_zero B hB] with ω hω
  apply (tendsto_add_atTop_iff_nat 1).mp
  simpa only [Nat.cast_add, Nat.cast_one] using hω

end Problem367

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

section Fields

variable {V : Type*} [Fintype V]

theorem abs_fieldMean_le (energy : S → ℝ) (spin : S → V → ℝ)
    (observable : S → ℝ) (x : V → ℝ) (A : ℝ)
    (hbound : ∀ s, |observable s| ≤ A) :
    |fieldMean energy spin observable x| ≤ A := by
  rw [← mean_fieldEnergy_zero energy spin (fun _ => 0)]
  exact abs_mean_le _ _ _ _ _ hbound

end Fields

end Problem367.FinitePosterior

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Gibbs_CovarianceL2Limit
attribute [-instance] _root_.OAI.Problem367.IsingConditionalCopyBounds.graphLaw_isProbabilityMeasure _root_.OAI.Problem367.IsingObservationFactor.copies_probability _root_.OAI.Problem367.IsingObservationFactor.kernel_markov _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_observationLaw_probability _root_.OAI.Problem367.IsingObservationInnovation.observationLaw_probability _root_.OAI.Problem367.TreeKoopman.labelProbability _root_.OAI.Problem367.WienerSampler.pathMeasurableSpace _root_.OAI.Problem367.freeIsingMeasure_probability
attribute [-simp] _root_.OAI.Problem367.ConnectedHull.pathAssignment_path _root_.OAI.Problem367.ConnectedHull.path_last _root_.OAI.Problem367.ConnectedHull.path_zero _root_.OAI.Problem367.CutContinuationChannels.averageChannel_globalCone _root_.OAI.Problem367.CutContinuationChannels.continuationChannel_globalCone _root_.OAI.Problem367.FactorObservable.centeredSpinLp_coe _root_.OAI.Problem367.FiniteIsingSplit.splitEquiv_fst _root_.OAI.Problem367.FiniteIsingSplit.splitEquiv_snd _root_.OAI.Problem367.FinitePathGibbs.tailPartition_zero _root_.OAI.Problem367.GaussianTreeResponseNaturality.fieldEquiv_apply_image _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_apply _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_uniformObservation _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_zero _root_.OAI.Problem367.IsingObservationInnovation.uniformObservation_relabel _root_.OAI.Problem367.IsingOrientedPath.attenuation_outward _root_.OAI.Problem367.IsingOrientedPath.endpoint_extensionAt _root_.OAI.Problem367.LocalSupportGeometry.prefixVertex_length _root_.OAI.Problem367.PathSideBranches.parent_sideVertex _root_.OAI.Problem367.PathSideBranches.restrictNoisyRegion_array _root_.OAI.Problem367.PathSideBranches.sideVertex_length _root_.OAI.Problem367.PathSideBranches.sideVertex_val _root_.OAI.Problem367.PosteriorChain.transition_spinMean _root_.OAI.Problem367.PosteriorChain.transition_sum _root_.OAI.Problem367.RootedBroadcast.flipBranchToComplement_val _root_.OAI.Problem367.RootedBroadcast.pos_spinMul _root_.OAI.Problem367.RootedBroadcast.prefixFlip_branchRoot _root_.OAI.Problem367.RootedBroadcast.prefixFlip_root _root_.OAI.Problem367.RootedBroadcast.prefixTreeAut_symm_branchRoot _root_.OAI.Problem367.RootedBroadcast.prefixTreeAut_symm_root _root_.OAI.Problem367.RootedBroadcast.spinMul_pos _root_.OAI.Problem367.RootedBroadcast.spinMul_self _root_.OAI.Problem367.TreeConeCoding.length_vertex _root_.OAI.Problem367.TreeConeCoding.vertex_nil _root_.OAI.Problem367.TreeConeCoding.vertex_val _root_.OAI.Problem367.TreeGibbsAut.spinEquiv_apply_image _root_.OAI.Problem367.TreeKoopman.centeredAverage_apply_coe _root_.OAI.Problem367.TreeKoopman.centeredAverage_pow_apply_coe _root_.OAI.Problem367.TreeKoopman.centeredGenerator_apply_coe _root_.OAI.Problem367.TreeKoopman.centeredGenerator_sq _root_.OAI.Problem367.TreeKoopman.generatorOperator_sq _root_.OAI.Problem367.TreeKoopman.reverseVertex_twice _root_.OAI.Problem367.TreeKoopman.wordRelabel_cons _root_.OAI.Problem367.TreeKoopman.wordRelabel_nil _root_.OAI.Problem367.TreeLawKoopman.centeredAverage_apply_coe _root_.OAI.Problem367.TreeLawKoopman.generatorOperator_sq _root_.OAI.Problem367.TreePathGibbs.vertexEquiv_val _root_.OAI.Problem367.branchColorAut_length _root_.OAI.Problem367.branchColorAut_singleton _root_.OAI.Problem367.branchColorAut_val _root_.OAI.Problem367.branchColorMap_symm_apply _root_.OAI.Problem367.colorPermAut_length _root_.OAI.Problem367.colorPermAut_nil _root_.OAI.Problem367.colorPermAut_val _root_.OAI.Problem367.colorPermMap_symm_apply _root_.OAI.Problem367.colorPermMap_val _root_.OAI.Problem367.connectedSpinEncode_apply_root _root_.OAI.Problem367.connectedSpinEquiv_apply _root_.OAI.Problem367.dropVertex_length _root_.OAI.Problem367.dropVertex_val _root_.OAI.Problem367.mem_rootComplementFinset _root_.OAI.Problem367.mem_rootComponentFinset _root_.OAI.Problem367.mem_rootComponentIndices _root_.OAI.Problem367.parentVertex_length _root_.OAI.Problem367.parentVertex_val _root_.OAI.Problem367.prefixColorAut_length _root_.OAI.Problem367.prefixColorAut_val _root_.OAI.Problem367.prefixColorMap_symm_apply _root_.OAI.Problem367.prefixFlip_twice _root_.OAI.Problem367.spinAgreementCode_eq_neg_iff _root_.OAI.Problem367.spinAgreementCode_eq_pos_iff _root_.OAI.Problem367.spinSign_flip _root_.OAI.Problem367.tsum_treeShell_radial _root_.OAI.Problem367.vertexSampler_relabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators Topology NNReal

namespace Problem367

open PlantedSymmetry

local instance covarianceL2LimitNonemptyIsingSpin : Nonempty IsingSpin := ⟨.neg⟩

lemma continuous_finiteGibbsCovarianceOn {d : ℕ} (beta : ℝ)
    (D : Finset (TreeVertex d)) (v w : D) :
    Continuous (finiteGibbsCovarianceOn beta D v w) := by
  exact (FinitePosterior.continuous_fieldMean _ _ _).sub
    ((FinitePosterior.continuous_fieldMean _ _ _).mul
      (FinitePosterior.continuous_fieldMean _ _ _))

lemma finiteGibbsCovarianceOn_abs_le_two {d : ℕ} (beta : ℝ)
    (D : Finset (TreeVertex d)) (v w : D) (y : D → ℝ) :
    |finiteGibbsCovarianceOn beta D v w y| ≤ 2 := by
  have hv := FinitePosterior.abs_fieldMean_le (finiteIsingEnergy beta D)
    (fun (eta : D → IsingSpin) u => spinSign (eta u))
    (fun eta => spinSign (eta v)) y 1
    (fun eta => show |spinSign (eta v)| ≤ 1 by cases eta v <;> norm_num [spinSign])
  have hw := FinitePosterior.abs_fieldMean_le (finiteIsingEnergy beta D)
    (fun (eta : D → IsingSpin) u => spinSign (eta u))
    (fun eta => spinSign (eta w)) y 1
    (fun eta => show |spinSign (eta w)| ≤ 1 by cases eta w <;> norm_num [spinSign])
  have hp := FinitePosterior.abs_fieldMean_le (finiteIsingEnergy beta D)
    (fun (eta : D → IsingSpin) u => spinSign (eta u))
    (fun eta => spinSign (eta v) * spinSign (eta w)) y 1
    (fun eta => show |spinSign (eta v) * spinSign (eta w)| ≤ 1 by
      cases eta v <;> cases eta w <;> norm_num [spinSign])
  have hprod : |FinitePosterior.fieldMean (finiteIsingEnergy beta D)
      (fun (eta : D → IsingSpin) u => spinSign (eta u))
      (fun eta => spinSign (eta v)) y *
    FinitePosterior.fieldMean (finiteIsingEnergy beta D)
      (fun (eta : D → IsingSpin) u => spinSign (eta u))
      (fun eta => spinSign (eta w)) y| ≤ 1 := by
    rw [abs_mul]
    simpa using mul_le_mul hv hw (abs_nonneg _) (by norm_num : (0 : ℝ) ≤ 1)
  exact (abs_sub _ _).trans (by linarith)

lemma continuous_finiteGibbsCovariance {d : ℕ} (beta : ℝ)
    (v w : TreeVertex d) (n : ℕ) : Continuous (finiteGibbsCovariance beta v w n) := by
  classical
  unfold finiteGibbsCovariance
  split_ifs with hw
  · exact (continuous_finiteGibbsCovarianceOn _ _ _ _).comp
      (continuous_pi fun u => continuous_apply u.1)
  · exact continuous_const

lemma finiteGibbsCovariance_abs_le_two {d : ℕ} (beta : ℝ)
    (v w : TreeVertex d) (n : ℕ) (y : TreeVertex d → ℝ) :
    |finiteGibbsCovariance beta v w n y| ≤ 2 := by
  classical
  unfold finiteGibbsCovariance
  split_ifs with hw
  · exact finiteGibbsCovarianceOn_abs_le_two _ _ _ _ _
  · norm_num

theorem HasFreeIsingLaw.finiteGibbsCovarianceOn_eq_posterior
    {d : ℕ} {beta : ℝ} {μ : Measure (TreeVertex d → IsingSpin)}
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ)
    (D : Finset (TreeVertex d)) (hD : ConnectedFinset D)
    (v w : D) (t : ℝ≥0) :
    (fun p => finiteGibbsCovarianceOn beta D v w (finiteObservation D t p)) =ᵐ[
      μ.prod (gaussianNoiseLaw (TreeVertex d) t)]
      posteriorCovariance (μ.prod (gaussianNoiseLaw (TreeVertex d) t))
        (MeasurableSpace.comap (finiteObservation D t) inferInstance)
        (fun p => spinSign (p.1 v.1)) (fun p => spinSign (p.1 w.1)) := by
  filter_upwards [hμ.finiteObservation_condExp D hD t
      (fun eta => spinSign (eta v) * spinSign (eta w)),
    hμ.finiteObservation_condExp D hD t (fun eta => spinSign (eta v)),
    hμ.finiteObservation_condExp D hD t (fun eta => spinSign (eta w))]
      with p hp hv hw
  exact congrArg₂ (fun a b : ℝ => a - b) hp.symm
    (congrArg₂ (· * ·) hv.symm hw.symm)

theorem HasFreeIsingLaw.finiteGibbsCovariance_tendsto_ae
    {d : ℕ} {beta : ℝ} {μ : Measure (TreeVertex d → IsingSpin)}
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (t : ℝ≥0) (v w : TreeVertex d) :
    ∀ᵐ p ∂μ.prod (gaussianNoiseLaw (TreeVertex d) t),
      Tendsto (fun n => finiteGibbsCovariance beta v w n (observation t p)) atTop
        (𝓝 (infiniteGibbsCovariance beta v w (observation t p))) := by
  classical
  let : IsProbabilityMeasure μ := hμ.isProbabilityMeasure
  let F := finiteObservationFiltration (connectedExhaustion v)
    (connectedExhaustion_monotone v) t
  have hlim := tendsto_ae_posteriorCovariance
    (μ.prod (gaussianNoiseLaw (TreeVertex d) t)) F
    (fun p => spinSign (p.1 v)) (fun p => spinSign (p.1 w))
  have hsup : (⨆ n, F n) = observationSigma (TreeVertex d) t :=
    finiteObservationFiltration_iSup (connectedExhaustion v)
      (connectedExhaustion_monotone v)
      (fun u => (eventually_mem_connectedExhaustion v u).exists) t
  rw [hsup] at hlim
  have hfinite (n : ℕ) : ∀ᵐ p ∂μ.prod (gaussianNoiseLaw (TreeVertex d) t),
      w ∈ connectedExhaustion v n →
      finiteGibbsCovariance beta v w n (observation t p) =
        posteriorCovariance (μ.prod (gaussianNoiseLaw (TreeVertex d) t)) (F n)
          (fun p => spinSign (p.1 v)) (fun p => spinSign (p.1 w)) p := by
    by_cases hw : w ∈ connectedExhaustion v n
    · filter_upwards [hμ.finiteGibbsCovarianceOn_eq_posterior
        (connectedExhaustion v n) (connectedExhaustion_connected v n)
        ⟨v, mem_connectedExhaustion v n⟩ ⟨w, hw⟩ t] with p hp
      intro _
      simpa only [finiteGibbsCovariance, dite_eq_left hw, F,
        finiteObservationFiltration, finiteObservation] using hp
    · exact Eventually.of_forall fun _ h => (hw h).elim
  filter_upwards [hlim, ae_all_iff.mpr hfinite,
    hμ.infiniteGibbsCovariance_eq_posterior t v w] with p hp hfinite hinf
  rw [← hinf] at hp
  apply hp.congr'
  filter_upwards [eventually_mem_connectedExhaustion v w] with n hn
  exact (hfinite n hn).symm

theorem HasFreeIsingLaw.finiteGibbsCovariance_brownian_tendsto_ae
    {d : ℕ} {beta : ℝ} {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure (TreeVertex d → IsingSpin)}
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ)
    (ν : TreeVertex d → Measure Ω) {B : TreeVertex d → ℝ≥0 → Ω → ℝ}
    (hB : ∀ i, IsPreBrownianReal (B i) (ν i))
    (hmB : ∀ i t, Measurable (B i t)) (t : ℝ≥0) (v w : TreeVertex d) :
    ∀ᵐ p ∂μ.prod (Measure.infinitePi ν),
      Tendsto (fun n => finiteGibbsCovariance beta v w n
        (fun i => (t : ℝ) * spinSign (p.1 i) + B i t (p.2 i))) atTop
        (𝓝 (infiniteGibbsCovariance beta v w
          (fun i => (t : ℝ) * spinSign (p.1 i) + B i t (p.2 i)))) := by
  let : IsProbabilityMeasure μ := hμ.isProbabilityMeasure
  have (i : TreeVertex d) : IsProbabilityMeasure (ν i) :=
    (hB i).isGaussianProcess.isProbabilityMeasure
  let T : ((TreeVertex d → IsingSpin) × (TreeVertex d → Ω)) →
      (TreeVertex d → IsingSpin) × (TreeVertex d → ℝ) :=
    Prod.map id (fun omega i => B i t (omega i))
  have hT : MeasurePreserving T (μ.prod (Measure.infinitePi ν))
      (μ.prod (gaussianNoiseLaw (TreeVertex d) t)) :=
    (MeasurePreserving.id μ).prod (brownian_array_eval_measurePreserving ν hB hmB t)
  exact hT.quasiMeasurePreserving.ae (hμ.finiteGibbsCovariance_tendsto_ae t v w)

end Problem367

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Martingales_SpatialLimit
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Filter Finset
open scoped NNReal Topology

namespace Problem367.MartingaleSpatialLimit

variable {Ω ι : Type*} [mΩ : MeasurableSpace Ω] {μ : Measure Ω}

theorem finiteSum_memLp {M : ι → ℝ≥0 → Ω → ℝ}
    (h2 : ∀ i t, MemLp (M i t) 2 μ) (s : Finset ι) (t : ℝ≥0) :
    MemLp (finiteSum M s t) 2 μ :=
  memLp_finsetSum s (fun i _ => h2 i t)

theorem finiteSum_martingale {F : Filtration ℝ≥0 mΩ} {M : ι → ℝ≥0 → Ω → ℝ}
    (hM : ∀ i, Martingale (M i) F μ) (s : Finset ι) :
    Martingale (finiteSum M s) F μ := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    have heq : finiteSum M ∅ = 0 := by funext t ω; simp [finiteSum]
    rw [heq]
    exact martingale_zero ℝ F μ
  | @insert i s hi ih =>
    have heq : finiteSum M (insert i s) = M i + finiteSum M s := by
      funext t ω
      simp only [finiteSum, sum_insert hi, Pi.add_apply]
    rw [heq]
    exact (hM i).add ih

end Problem367.MartingaleSpatialLimit

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
-- module Solutions.Q243_FreeIsing.FreeIsing_Ising_MixedFiltering
attribute [-instance] _root_.OAI.Problem367.IsingConditionalCopyBounds.graphLaw_isProbabilityMeasure _root_.OAI.Problem367.IsingObservationFactor.copies_probability _root_.OAI.Problem367.IsingObservationFactor.kernel_markov _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_observationLaw_probability _root_.OAI.Problem367.IsingObservationInnovation.observationLaw_probability _root_.OAI.Problem367.TreeKoopman.labelProbability _root_.OAI.Problem367.freeIsingMeasure_probability
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

lemma finiteCovariance_stronglyAdapted
    (beta : ℝ) (B : ℝ≥0 → A → ℝ) (hmB : ∀ t, Measurable (B t))
    (v u : TreeVertex d) (n : ℕ) :
    StronglyAdapted (ArrayPosteriorStationarity.filtration B hmB)
      (finiteCovariance beta B v u n) := by
  intro t
  have hobs : StronglyMeasurable[ArrayPosteriorStationarity.filtration B hmB t]
      (fun q : State d A => fun i => plantedArrayObservation (fun _ : TreeVertex d => B)
        ArrayPosteriorStationarity.spinArray i t q) := by
    apply Measurable.stronglyMeasurable
    refine @Measurable.of_eval (State d A) (TreeVertex d) (fun _ => ℝ)
      (ArrayPosteriorStationarity.filtration B hmB t) (fun _ => inferInstance) _ ?_
    intro i
    exact (arrayNaturalFiltration_stronglyAdapted
      (plantedArrayObservation (fun _ : TreeVertex d => B) ArrayPosteriorStationarity.spinArray)
      (plantedArrayObservation_measurable (fun _ => hmB)
        ArrayPosteriorStationarity.measurable_spinArray) i t).measurable
  exact (continuous_finiteGibbsCovariance beta v u n).comp_stronglyMeasurable hobs

omit [MeasurableSpace A] in
lemma finiteCovariance_continuous
    (beta : ℝ) (B : ℝ≥0 → A → ℝ)
    (hcB : ∀ a, Continuous (fun t => B t a))
    (v u : TreeVertex d) (n : ℕ) (q : State d A) :
    Continuous (fun t => finiteCovariance beta B v u n t q) := by
  apply (continuous_finiteGibbsCovariance beta v u n).comp
  apply continuous_pi
  intro i
  exact (hcB (q.2 i)).add (continuous_subtype_val.mul continuous_const)

omit [MeasurableSpace A] in
lemma finiteCovariance_abs_le_two (beta : ℝ) (B : ℝ≥0 → A → ℝ)
    (v u : TreeVertex d) (n : ℕ) (t : ℝ≥0) (q : State d A) :
    |finiteCovariance beta B v u n t q| ≤ 2 :=
  finiteGibbsCovariance_abs_le_two beta v u n _

end Problem367.IsingInnovation

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Ising_CoordinateIntegrals
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

lemma interval_integral_eq_timeSpace
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [SFinite P]
    (T : ℝ≥0) {f : ℝ × Ω → ℝ}
    (hf : Integrable f ((volume.restrict (Set.Ioc (0 : ℝ) (T : ℝ))).prod P)) :
    (∫ r in (0 : ℝ)..(T : ℝ), ∫ q, f (r, q) ∂P) =
      ∫ p, f p ∂(volume.restrict (Set.Ioc (0 : ℝ) (T : ℝ))).prod P := by
  rw [intervalIntegral.integral_of_le T.coe_nonneg]
  exact (integral_prod f hf).symm

end Problem367.IsingInnovation

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Ising_CovarianceTimeL2
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

lemma measurable_finiteCovariance_joint
    (beta : ℝ) (B : ℝ≥0 → A → ℝ) (hmB : ∀ t, Measurable (B t))
    (hcB : ∀ a, Continuous (fun t => B t a))
    (v u : TreeVertex d) (n : ℕ) :
    Measurable (Function.uncurry (finiteCovariance beta B v u n)) := by
  apply measurable_uncurry_of_continuous_of_measurable
  · exact finiteCovariance_continuous beta B hcB v u n
  · intro t
    exact ((finiteCovariance_stronglyAdapted beta B hmB v u n t).mono
      ((ArrayPosteriorStationarity.filtration B hmB).le t)).measurable

theorem finiteCovariance_tendsto_ae
    {beta : ℝ} {μ : Measure (TreeVertex d → IsingSpin)}
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ)
    (ν : Measure A) {B : ℝ≥0 → A → ℝ} (hB : IsPreBrownianReal B ν)
    (hmB : ∀ t, Measurable (B t)) (t : ℝ≥0) (v u : TreeVertex d) :
    ∀ᵐ q ∂μ.prod (Measure.infinitePi (fun _ : TreeVertex d => ν)),
      Tendsto (fun n => finiteCovariance beta B v u n t q) atTop
        (𝓝 (covariance beta B v u t q)) := by
  simpa only [finiteCovariance, covariance, plantedArrayObservation,
    ArrayPosteriorStationarity.spinArray, add_comm] using
    hμ.finiteGibbsCovariance_brownian_tendsto_ae
      (fun _ : TreeVertex d => ν) (fun _ => hB) (fun _ => hmB) t v u

theorem finiteCovariance_tendsto_finiteMeasureMeanSquare
    {beta : ℝ} {μ : Measure (TreeVertex d → IsingSpin)}
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ)
    (ν : Measure A) {B : ℝ≥0 → A → ℝ} (hB : IsPreBrownianReal B ν)
    (hmB : ∀ t, Measurable (B t)) (hcB : ∀ a, Continuous (fun t => B t a))
    (τ : Measure ℝ) [IsFiniteMeasure τ] (v u : TreeVertex d) :
    Tendsto (fun n => ∫ p : ℝ × State d A,
      (finiteCovariance beta B v u n p.1.toNNReal p.2 -
        covariance beta B v u p.1.toNNReal p.2) ^ 2
        ∂τ.prod (μ.prod (Measure.infinitePi (fun _ : TreeVertex d => ν))))
      atTop (𝓝 0) := by
  let : IsProbabilityMeasure μ := hμ.isProbabilityMeasure
  let : IsProbabilityMeasure ν := hB.isGaussianProcess.isProbabilityMeasure
  have hm : Measurable (fun p : ℝ × State d A => (p.1.toNNReal, p.2)) :=
    (measurable_real_toNNReal.comp measurable_fst).prodMk measurable_snd
  apply tendsto_integral_prod_sq_sub_of_bounded_ae τ
    (μ.prod (Measure.infinitePi (fun _ : TreeVertex d => ν)))
    (fun n => (measurable_finiteCovariance_joint beta B hmB hcB v u n).comp hm)
    ((measurable_covariance_joint beta B hmB hcB v u).comp hm)
    (by norm_num : (0 : ℝ) ≤ 2)
  · intro n
    exact Eventually.of_forall fun t => Eventually.of_forall fun q =>
      by simpa only [Function.comp_apply, Function.uncurry_apply_pair, Real.norm_eq_abs] using
        finiteCovariance_abs_le_two beta B v u n t.toNNReal q
  · exact Eventually.of_forall fun t => Eventually.of_forall fun q =>
      by simpa only [Function.comp_apply, Function.uncurry_apply_pair, Real.norm_eq_abs] using
        covariance_abs_le_two beta B v u t.toNNReal q
  · exact Eventually.of_forall fun t =>
      finiteCovariance_tendsto_ae hμ ν hB hmB t.toNNReal v u

theorem finiteCovariance_tendsto_timeMeanSquare
    {beta : ℝ} {μ : Measure (TreeVertex d → IsingSpin)}
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ)
    (ν : Measure A) {B : ℝ≥0 → A → ℝ} (hB : IsPreBrownianReal B ν)
    (hmB : ∀ t, Measurable (B t)) (hcB : ∀ a, Continuous (fun t => B t a))
    (v u : TreeVertex d) (T : ℝ≥0) :
    Tendsto (fun n => ∫ p : ℝ × State d A,
      (finiteCovariance beta B v u n p.1.toNNReal p.2 -
        covariance beta B v u p.1.toNNReal p.2) ^ 2
        ∂(volume.restrict (Set.Ioc (0 : ℝ) (T : ℝ))).prod
          (μ.prod (Measure.infinitePi (fun _ : TreeVertex d => ν))))
      atTop (𝓝 0) := by
  exact finiteCovariance_tendsto_finiteMeasureMeanSquare hμ ν hB hmB hcB _ v u

lemma memLp_finiteCovariance_time
    (beta : ℝ) (B : ℝ≥0 → A → ℝ) (hmB : ∀ t, Measurable (B t))
    (hcB : ∀ a, Continuous (fun t => B t a))
    (P : Measure (State d A)) [IsFiniteMeasure P]
    (τ : Measure ℝ) [IsFiniteMeasure τ] (v u : TreeVertex d) (n : ℕ) :
    MemLp (fun p : ℝ × State d A =>
      finiteCovariance beta B v u n p.1.toNNReal p.2) 2 (τ.prod P) := by
  apply MemLp.of_bound
    ((measurable_finiteCovariance_joint beta B hmB hcB v u n).comp
      ((measurable_real_toNNReal.comp measurable_fst).prodMk measurable_snd)).aestronglyMeasurable
    2
  exact Eventually.of_forall fun p => by
    simpa only [Function.comp_apply, Function.uncurry_apply_pair, Real.norm_eq_abs] using
      finiteCovariance_abs_le_two beta B v u n p.1.toNNReal p.2

lemma memLp_covariance_time
    (beta : ℝ) (B : ℝ≥0 → A → ℝ) (hmB : ∀ t, Measurable (B t))
    (hcB : ∀ a, Continuous (fun t => B t a))
    (P : Measure (State d A)) [IsFiniteMeasure P]
    (τ : Measure ℝ) [IsFiniteMeasure τ] (v u : TreeVertex d) :
    MemLp (fun p : ℝ × State d A =>
      covariance beta B v u p.1.toNNReal p.2) 2 (τ.prod P) := by
  apply MemLp.of_bound
    ((measurable_covariance_joint beta B hmB hcB v u).comp
      ((measurable_real_toNNReal.comp measurable_fst).prodMk measurable_snd)).aestronglyMeasurable
    2
  exact Eventually.of_forall fun p => by
    simpa only [Function.comp_apply, Function.uncurry_apply_pair, Real.norm_eq_abs] using
      covariance_abs_le_two beta B v u p.1.toNNReal p.2

end Problem367.IsingInnovation

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Spins_Recovery
attribute [-instance] _root_.OAI.Problem367.IsingConditionalCopyBounds.graphLaw_isProbabilityMeasure _root_.OAI.Problem367.IsingObservationFactor.copies_probability _root_.OAI.Problem367.IsingObservationFactor.kernel_markov _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_observationLaw_probability _root_.OAI.Problem367.IsingObservationInnovation.observationLaw_probability _root_.OAI.Problem367.WienerSampler.pathMeasurableSpace _root_.OAI.Problem367.freeIsingMeasure_probability
attribute [-simp] _root_.OAI.Problem367.ConnectedHull.pathAssignment_path _root_.OAI.Problem367.CutContinuationChannels.averageChannel_globalCone _root_.OAI.Problem367.CutContinuationChannels.continuationChannel_globalCone _root_.OAI.Problem367.FactorObservable.centeredSpinLp_coe _root_.OAI.Problem367.FiniteIsingSplit.splitEquiv_fst _root_.OAI.Problem367.FiniteIsingSplit.splitEquiv_snd _root_.OAI.Problem367.FinitePathGibbs.tailPartition_zero _root_.OAI.Problem367.IsingObservationInnovation.uniformObservation_relabel _root_.OAI.Problem367.IsingSpin.flip_eq_iff _root_.OAI.Problem367.IsingSpin.flip_flip _root_.OAI.Problem367.IsingSpin.toReal_neg _root_.OAI.Problem367.IsingSpin.toReal_pos _root_.OAI.Problem367.PathSideBranches.restrictNoisyRegion_array _root_.OAI.Problem367.PosteriorChain.transition_spinMean _root_.OAI.Problem367.PosteriorChain.transition_sum _root_.OAI.Problem367.RootedBroadcast.pos_spinMul _root_.OAI.Problem367.RootedBroadcast.spinMul_pos _root_.OAI.Problem367.RootedBroadcast.spinMul_self _root_.OAI.Problem367.TreeGibbsAut.spinEquiv_apply_image _root_.OAI.Problem367.connectedSpinEncode_apply_root _root_.OAI.Problem367.connectedSpinEquiv_apply _root_.OAI.Problem367.extendFiniteSpin_apply _root_.OAI.Problem367.finiteFreeIsingPMF_apply _root_.OAI.Problem367.flipConfig_apply _root_.OAI.Problem367.flipConfig_flipConfig _root_.OAI.Problem367.flipConfig_preimage_spin _root_.OAI.Problem367.freeCylinderWeight_flipConfig _root_.OAI.Problem367.freeCylinderWeight_singleton _root_.OAI.Problem367.isingSpin_neg_ne_pos _root_.OAI.Problem367.isingSpin_pos_ne_neg _root_.OAI.Problem367.restrict_extendFiniteSpin _root_.OAI.Problem367.spinAgreementCode_eq_neg_iff _root_.OAI.Problem367.spinAgreementCode_eq_pos_iff _root_.OAI.Problem367.spinSign_flip _root_.OAI.Problem367.spinSign_mul_self _root_.OAI.Problem367.spinSign_neg _root_.OAI.Problem367.spinSign_pos _root_.OAI.Problem367.spinSign_sq _root_.OAI.Problem367.sum_spinSign _root_.OAI.Problem367.transitionKernel_one _root_.OAI.Problem367.transitionKernel_spinSum _root_.OAI.Problem367.transitionKernel_sum _root_.OAI.Problem367.transitionKernel_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology

namespace Problem367.SpinRecovery

theorem measurable_decode : Measurable decode := by
  unfold decode
  apply Measurable.ite
  · exact measurableSet_tendsto (𝓝 (-1 : ℝ))
      (f := fun (n : ℕ) (x : ℕ → ℝ) => x n / (n : ℝ))
      (by intro n; fun_prop)
  · exact measurable_const
  · exact measurable_const

theorem decode_of_tendsto {x : ℕ → ℝ} {s : IsingSpin}
    (h : Tendsto (fun n : ℕ => x n / (n : ℝ)) atTop (𝓝 (spinSign s))) :
    decode x = s := by
  cases s with
  | neg =>
      simp only [spinSign] at h
      simp [decode, h]
  | pos =>
      have hn : ¬ Tendsto (fun n : ℕ => x n / (n : ℝ)) atTop (𝓝 (-1 : ℝ)) := by
        intro hm
        have he : (-1 : ℝ) = 1 := tendsto_nhds_unique hm h
        norm_num at he
      simp [decode, hn]

theorem decode_signal_add_noise (s : IsingSpin) {z : ℕ → ℝ}
    (hz : Tendsto (fun n : ℕ => z n / (n : ℝ)) atTop (𝓝 (0 : ℝ))) :
    decode (fun n : ℕ => (n : ℝ) * spinSign s + z n) = s := by
  apply decode_of_tendsto
  have he : (fun n : ℕ => ((n : ℝ) * spinSign s + z n) / (n : ℝ)) =ᶠ[atTop]
      (fun n : ℕ => spinSign s + z n / (n : ℝ)) := by
    filter_upwards [eventually_ge_atTop 1] with n hn
    have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast (by omega : n ≠ 0)
    field_simp
  apply (tendsto_congr' he).2
  simpa using tendsto_const_nhds.add hz

theorem measurable_decodeArray {V : Type*} :
    Measurable (decodeArray (V := V)) := by
  exact Measurable.of_eval fun vertex =>
    measurable_decode.comp (measurable_pi_apply vertex)

end Problem367.SpinRecovery

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
-- module Solutions.Q243_FreeIsing.FreeIsing_Ising_ObservationRecovery
attribute [-instance] _root_.OAI.Problem367.IsingConditionalCopyBounds.graphLaw_isProbabilityMeasure _root_.OAI.Problem367.IsingObservationFactor.copies_probability _root_.OAI.Problem367.IsingObservationFactor.kernel_markov _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_observationLaw_probability _root_.OAI.Problem367.IsingObservationInnovation.observationLaw_probability _root_.OAI.Problem367.TreeKoopman.labelProbability _root_.OAI.Problem367.freeIsingMeasure_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal Topology

namespace Problem367.IsingObservationRecovery

open IsingObservationInnovation

theorem measurable_decode {d : ℕ} : Measurable (decode (d := d)) := by
  apply SpinRecovery.measurable_decodeArray.comp
  exact Measurable.of_eval fun v => Measurable.of_eval fun n =>
    (continuous_eval_const (n : ℝ≥0)).measurable.comp (measurable_pi_apply v)

theorem decode_uniformObservation_ae {d : ℕ}
    (μ : Measure (TreeVertex d → IsingSpin)) [IsProbabilityMeasure μ] :
    (fun q : IsingInnovation.State d ℝ => decode (uniformObservation q)) =ᵐ[
      μ.prod (labelMeasure d)] Prod.fst := by
  have hnoise := ae_brownian_div_nat_tendsto_zero
    (fun t u => WienerSampler.sample u t)
    WienerSampler.sample_isBrownianReal.toIsPreBrownianReal
  have hall : ∀ᵐ q : IsingInnovation.State d ℝ ∂μ.prod (labelMeasure d),
      ∀ v : TreeVertex d, Tendsto
        (fun n : ℕ => WienerSampler.sample (q.2 v) n / (n : ℝ)) atTop (𝓝 0) := by
    apply ae_all_iff.mpr
    intro v
    exact (planted_noise_coordinate_measurePreserving μ
      (fun _ : TreeVertex d => uniform01) v).quasiMeasurePreserving.ae hnoise
  filter_upwards [hall] with q hq
  funext v
  have h := SpinRecovery.decode_signal_add_noise (q.1 v) (hq v)
  change SpinRecovery.decode (fun n : ℕ => WienerSampler.sample (q.2 v) n +
    ((n : ℝ≥0) : ℝ) * spinSign (q.1 v)) = q.1 v
  have hsign (s : IsingSpin) : SpinRecovery.spinSign s = spinSign s := by
    cases s <;> rfl
  convert h using 1
  all_goals try with_reducible_and_instances rfl
  congr 1
  funext n
  rw [NNReal.coe_natCast, hsign]
  exact add_comm _ _

end Problem367.IsingObservationRecovery

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Posterior_InteriorLocalization
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory Filter TopologicalSpace
open scoped NNReal Topology

namespace Problem367.PosteriorInteriorLocalization

theorem field_bound_iff_tanh_bounds {m X K : ℝ} :
    (m ∈ Set.Ioo (-1 : ℝ) 1 ∧ |Real.artanh m - X| ≤ K) ↔
      (Real.tanh (X - K) ≤ m ∧ m ≤ Real.tanh (X + K)) := by
  constructor
  · rintro ⟨hm, hb⟩
    constructor
    · apply (Real.artanh_le_artanh_iff
        ⟨Real.neg_one_lt_tanh _, Real.tanh_lt_one _⟩ hm).mp
      rw [Real.artanh_tanh]
      linarith [(abs_le.mp hb).1]
    · apply (Real.artanh_le_artanh_iff hm
        ⟨Real.neg_one_lt_tanh _, Real.tanh_lt_one _⟩).mp
      rw [Real.artanh_tanh]
      linarith [(abs_le.mp hb).2]
  · intro hb
    have h := posterior_field_limit_of_tanh_bounds
      (u := fun _ : ℕ => m) tendsto_const_nhds (fun _ => hb)
    exact ⟨h.1, h.2.1⟩

private theorem continuous_tanh : Continuous Real.tanh :=
  continuous_iff_continuousAt.mpr fun t => (hasDerivAt_tanh_response t).continuousAt

theorem ae_all_field_bound_of_continuous
    {T Ω : Type*} [TopologicalSpace T] [SeparableSpace T]
    [MeasurableSpace Ω] {P : Measure Ω} {M X : T → Ω → ℝ} {K : ℝ}
    (hM : ∀ᵐ ω ∂P, Continuous (fun t => M t ω))
    (hX : ∀ᵐ ω ∂P, Continuous (fun t => X t ω))
    (hb : ∀ t, ∀ᵐ ω ∂P,
      M t ω ∈ Set.Ioo (-1 : ℝ) 1 ∧ |Real.artanh (M t ω) - X t ω| ≤ K) :
    ∀ᵐ ω ∂P, ∀ t,
      M t ω ∈ Set.Ioo (-1 : ℝ) 1 ∧ |Real.artanh (M t ω) - X t ω| ≤ K := by
  obtain ⟨S, hSc, hSd⟩ := TopologicalSpace.exists_countable_dense T
  let : Countable S := hSc.to_subtype
  have hS : ∀ᵐ ω ∂P, ∀ t : S,
      M t ω ∈ Set.Ioo (-1 : ℝ) 1 ∧ |Real.artanh (M t ω) - X t ω| ≤ K :=
    ae_all_iff.mpr (fun t => hb t)
  filter_upwards [hM, hX, hS] with ω hMω hXω hSω
  have hall : ∀ t, Real.tanh (X t ω - K) ≤ M t ω ∧
      M t ω ≤ Real.tanh (X t ω + K) := by
    refine isClosed_property hSd.denseRange_val
      (p := fun t => Real.tanh (X t ω - K) ≤ M t ω ∧
        M t ω ≤ Real.tanh (X t ω + K)) ?_ ?_
    · exact (isClosed_le (continuous_tanh.comp (hXω.sub continuous_const)) hMω).inter
        (isClosed_le hMω (continuous_tanh.comp (hXω.add continuous_const)))
    · intro t
      exact field_bound_iff_tanh_bounds.mp (hSω t)
  exact fun t => field_bound_iff_tanh_bounds.mpr (hall t)

theorem continuous_artanh_of_interior
    {T : Type*} [TopologicalSpace T] {m : T → ℝ}
    (hm : Continuous m) (hi : ∀ t, m t ∈ Set.Ioo (-1 : ℝ) 1) :
    Continuous (fun t => Real.artanh (m t)) := by
  apply continuous_iff_continuousAt.mpr
  intro t
  exact (hasDerivAt_artanh_interval (hi t)).continuousAt.comp (hm.continuousAt)

end Problem367.PosteriorInteriorLocalization

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Posterior_ContinuousPosteriorInterior
attribute [-instance] _root_.OAI.Problem367.IsingConditionalCopyBounds.graphLaw_isProbabilityMeasure _root_.OAI.Problem367.IsingObservationFactor.copies_probability _root_.OAI.Problem367.IsingObservationFactor.kernel_markov _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_observationLaw_probability _root_.OAI.Problem367.IsingObservationInnovation.observationLaw_probability _root_.OAI.Problem367.TreeKoopman.labelProbability _root_.OAI.Problem367.WienerSampler.pathMeasurableSpace _root_.OAI.Problem367.freeIsingMeasure_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal Topology

namespace Problem367

theorem HasFreeIsingLaw.continuous_posterior_all_time_field_bound
    {d : ℕ} {beta : ℝ} {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure (TreeVertex d → IsingSpin)}
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hbeta : 0 ≤ beta)
    (ν : TreeVertex d → Measure Ω)
    {B : TreeVertex d → ℝ≥0 → Ω → ℝ}
    (hB : ∀ v, IsBrownianReal (B v) (ν v))
    (hmB : ∀ v t, Measurable (B v t))
    {m : TreeVertex d → ℝ≥0 →
      ((TreeVertex d → IsingSpin) × (TreeVertex d → Ω)) → ℝ}
    (hcm : ∀ v, ∀ᵐ p ∂μ.prod (Measure.infinitePi ν), Continuous (fun t => m v t p))
    (hversion : ∀ v t, m v t =ᵐ[μ.prod (Measure.infinitePi ν)]
      (fun p => infiniteGibbsSpinMean beta v
        (fun i => (t : ℝ) * spinSign (p.1 i) + B i t (p.2 i)))) :
    ∀ᵐ p ∂μ.prod (Measure.infinitePi ν), ∀ v,
      (∀ t, m v t p ∈ Set.Ioo (-1 : ℝ) 1 ∧
        |Real.artanh (m v t p) - ((t : ℝ) * spinSign (p.1 v) + B v t (p.2 v))| ≤
          (d : ℝ) * beta) ∧
      Continuous (fun t => Real.artanh (m v t p)) := by
  let : IsProbabilityMeasure μ := hμ.isProbabilityMeasure
  have (vertex : TreeVertex d) : IsProbabilityMeasure (ν vertex) :=
    (hB vertex).isGaussianProcess.isProbabilityMeasure
  apply ae_all_iff.mpr
  intro v
  have hX : ∀ᵐ p ∂μ.prod (Measure.infinitePi ν),
      Continuous (fun t : ℝ≥0 => (t : ℝ) * spinSign (p.1 v) + B v t (p.2 v)) := by
    have hnoise := (planted_noise_coordinate_measurePreserving μ ν v).quasiMeasurePreserving.ae
      (hB v).cont
    filter_upwards [hnoise] with p hp
    exact (continuous_subtype_val.mul continuous_const).add hp
  have hb : ∀ t, ∀ᵐ p ∂μ.prod (Measure.infinitePi ν),
      m v t p ∈ Set.Ioo (-1 : ℝ) 1 ∧
      |Real.artanh (m v t p) - ((t : ℝ) * spinSign (p.1 v) + B v t (p.2 v))| ≤
        (d : ℝ) * beta := by
    intro t
    filter_upwards [hversion v t,
      hμ.infiniteGibbsSpinMean_brownian_field_bound hbeta ν
        (fun i => (hB i).toIsPreBrownianReal) hmB t v] with p hp hb
    rw [hp]
    exact hb
  filter_upwards [hcm v,
    PosteriorInteriorLocalization.ae_all_field_bound_of_continuous (hcm v) hX hb]
      with p hp hb
  exact ⟨hb, PosteriorInteriorLocalization.continuous_artanh_of_interior hp
    (fun t => (hb t).1)⟩

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
-- module Solutions.Q243_FreeIsing.FreeIsing_Ising_CanonicalContinuousFields
attribute [-instance] _root_.OAI.Problem367.TreeKoopman.labelProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped NNReal Topology

namespace Problem367.IsingObservationFactor
open IsingObservationInnovation

lemma field_progressive {d : ℕ} (beta : ℝ) (v : TreeVertex d) :
    IsStronglyProgressive (filtration d) (field beta v) :=
  isStronglyProgressive_artanh (filtration d) (posterior_progressive beta v)

lemma continuousField_progressive {d : ℕ} (beta : ℝ) (v : TreeVertex d) :
    IsStronglyProgressive (filtration d) (continuousField beta v) :=
  ProgressiveVersionPushforward.progressive_version (field_progressive beta v)

theorem continuousField_modification
    {d : ℕ} (hd : 3 ≤ d) {beta : ℝ} {μ : Measure (TreeVertex d → IsingSpin)}
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hb : 0 ≤ beta)
    (hcrit : ((d - 1 : ℕ) : ℝ) * Real.tanh beta ^ 2 ≤ 1) (v : TreeVertex d) :
    (∀ᵐ x ∂observationLaw μ, Continuous (fun t => continuousField beta v t x)) ∧
      (∀ t, continuousField beta v t =ᵐ[observationLaw μ] field beta v t) := by
  let B : ℝ≥0 → ℝ → ℝ := fun t u => WienerSampler.sample u t
  have hmB (t : ℝ≥0) : Measurable (B t) :=
    (continuous_eval_const t).measurable.comp WienerSampler.measurable_sample
  have hcB (u : ℝ) : Continuous (fun t => B t u) := (WienerSampler.sample u).continuous
  obtain ⟨Z, hZ⟩ := Classical.axiomOfChoice
    (fun w : TreeVertex d => IsingInnovation.exists_continuous_posterior
      hd hμ hb hcrit uniform01 WienerSampler.sample_isBrownianReal.toIsPreBrownianReal
      hmB hcB w)
  have hcont (w : TreeVertex d) : ∀ᵐ q ∂μ.prod (labelMeasure d),
      Continuous (fun t => Z w t q) := (hZ w).2.2.1
  have hver (w : TreeVertex d) (t : ℝ≥0) : Z w t =ᵐ[μ.prod (labelMeasure d)]
      (fun q => infiniteGibbsSpinMean beta w
        (fun i => (t : ℝ) * spinSign (q.1 i) + B t (q.2 i))) := by
    filter_upwards [(hZ w).2.2.2.2.2 t] with q hq
    refine hq.trans ?_
    change infiniteGibbsSpinMean beta w
      (fun i => B t (q.2 i) + (t : ℝ) * spinSign (q.1 i)) = _
    apply congrArg (infiniteGibbsSpinMean beta w)
    funext i
    exact add_comm _ _
  have hfields := hμ.continuous_posterior_all_time_field_bound hb
    (fun _ : TreeVertex d => uniform01) (fun _ => WienerSampler.sample_isBrownianReal)
    (fun _ => hmB) hcont hver
  have hc : ∀ᵐ q ∂μ.prod (labelMeasure d),
      Continuous (fun t => Real.artanh (Z v t q)) :=
    hfields.mono (fun q hq => (hq v).2)
  have he (t : ℝ≥0) : (fun q => Real.artanh (Z v t q)) =ᵐ[μ.prod (labelMeasure d)]
      (fun q => field beta v t (uniformObservation q)) := by
    filter_upwards [hver v t] with q hq
    change Real.artanh (Z v t q) = Real.artanh
      (infiniteGibbsSpinMean beta v
        (fun i => B t (q.2 i) + (t : ℝ) * spinSign (q.1 i)))
    apply congrArg Real.artanh
    refine hq.trans ?_
    apply congrArg (infiniteGibbsSpinMean beta v)
    funext i
    exact add_comm _ _
  exact (ProgressiveVersionPushforward.continuous_progressive_version_of_pullback
    measurable_uniformObservation (field_progressive beta v) hc he).2

end Problem367.IsingObservationFactor

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

private lemma continuous_tanh : Continuous Real.tanh :=
  continuous_iff_continuousAt.mpr (fun z => (hasDerivAt_tanh_response z).continuousAt)

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

lemma continuousRootResponse_progressive (hb : 0 ≤ beta) (v : TreeVertex d) :
    IsStronglyProgressive (filtration d) (continuousRootResponse hb v) := by
  intro t
  let : MeasurableSpace (Paths d) := filtration d t
  exact ((continuous_siteRootResponse hb v).measurable.comp
    (Measurable.of_eval (fun i => (continuousField_progressive beta i t).measurable))).stronglyMeasurable

lemma continuousRootResponse_abs_le_one (hb : 0 ≤ beta) (v : TreeVertex d)
    (t : ℝ≥0) (x : Paths d) : |continuousRootResponse hb v t x| ≤ 1 := by
  obtain ⟨h0, h1⟩ := siteRootResponse_mem_Icc hb v (fun i => continuousField beta i t x)
  exact (abs_of_nonneg h0).trans_le h1

theorem continuousRootResponse_continuous_ae
    (hd : 3 ≤ d) {μ : Measure (TreeVertex d → IsingSpin)}
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hb : 0 ≤ beta)
    (hcrit : ((d - 1 : ℕ) : ℝ) * Real.tanh beta ^ 2 ≤ 1) (v : TreeVertex d) :
    ∀ᵐ x ∂observationLaw μ, Continuous (fun t => continuousRootResponse hb v t x) := by
  have hc (i : TreeVertex d) := (continuousField_modification hd hμ hb hcrit i).1
  filter_upwards [ae_all_iff.mpr hc] with x hx
  exact (continuous_siteRootResponse hb v).comp (continuous_pi hx)

lemma continuousRootCovariance_progressive (hb : 0 ≤ beta) (v : TreeVertex d) :
    IsStronglyProgressive (filtration d) (continuousRootCovariance hb v) := by
  intro t
  have hf := continuousField_progressive beta (ConnectedHull.root d) t
  exact (stronglyMeasurable_const.sub
    ((continuous_tanh.comp_stronglyMeasurable hf).pow 2)).mul
      (continuousRootResponse_progressive hb v t)

lemma continuousRootCovariance_abs_le_one (hb : 0 ≤ beta) (v : TreeVertex d)
    (t : ℝ≥0) (x : Paths d) : |continuousRootCovariance hb v t x| ≤ 1 := by
  have h0 := (sub_pos.mpr (Real.tanh_sq_lt_one
    (continuousField beta (ConnectedHull.root d) t x))).le
  have h1 : 1 - Real.tanh (continuousField beta (ConnectedHull.root d) t x) ^ 2 ≤ 1 :=
    sub_le_self _ (sq_nonneg _)
  rw [continuousRootCovariance, abs_mul, abs_of_nonneg h0]
  exact (mul_le_mul h1 (continuousRootResponse_abs_le_one hb v t x)
    (abs_nonneg _) (by norm_num)).trans_eq (one_mul 1)

theorem continuousRootCovariance_continuous_ae
    (hd : 3 ≤ d) {μ : Measure (TreeVertex d → IsingSpin)}
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hb : 0 ≤ beta)
    (hcrit : ((d - 1 : ℕ) : ℝ) * Real.tanh beta ^ 2 ≤ 1) (v : TreeVertex d) :
    ∀ᵐ x ∂observationLaw μ, Continuous (fun t => continuousRootCovariance hb v t x) := by
  filter_upwards [(continuousField_modification hd hμ hb hcrit (ConnectedHull.root d)).1,
    continuousRootResponse_continuous_ae hd hμ hb hcrit v] with x hf hr
  exact (continuous_const.sub ((continuous_tanh.comp hf).pow 2)).mul hr

end Problem367.IsingObservationFactor

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Ising_ObservationPosteriorTransport
attribute [-instance] _root_.OAI.Problem367.IsingConditionalCopyBounds.graphLaw_isProbabilityMeasure _root_.OAI.Problem367.IsingObservationFactor.copies_probability _root_.OAI.Problem367.IsingObservationFactor.kernel_markov _root_.OAI.Problem367.TreeKoopman.labelProbability _root_.OAI.Problem367.freeIsingMeasure_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace Problem367.IsingObservationInnovation

theorem measurePreserving_uniformObservation {d : ℕ}
    (μ : Measure (TreeVertex d → IsingSpin)) :
    MeasurePreserving (uniformObservation (d := d))
      (μ.prod (labelMeasure d)) (observationLaw μ) :=
  ⟨measurable_uniformObservation, rfl⟩

end Problem367.IsingObservationInnovation

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Ising_CanonicalCovariancePullback
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped NNReal

namespace Problem367.IsingObservationInnovation

theorem progressive_uniformObservation {d : ℕ}
    (hmB : ∀ t, Measurable (fun u => WienerSampler.sample u t))
    {H : ℝ≥0 → Paths d → ℝ} (hH : IsStronglyProgressive (filtration d) H) :
    IsStronglyProgressive
      (ArrayPosteriorStationarity.filtration (fun t u => WienerSampler.sample u t) hmB)
      (fun t q => H t (uniformObservation q)) := by
  intro t
  have hφ : Measurable[
      ArrayPosteriorStationarity.filtration (fun s u => WienerSampler.sample u s) hmB t,
      filtration d t] uniformObservation := by
    rw [← filtration_comap_uniformObservation d t hmB]
    exact comap_measurable _
  let : MeasurableSpace (IsingInnovation.State d ℝ) :=
    ArrayPosteriorStationarity.filtration (fun s u => WienerSampler.sample u s) hmB t
  let : MeasurableSpace (Paths d) := filtration d t
  exact (hH t).comp_measurable (measurable_id.prodMap hφ)

end Problem367.IsingObservationInnovation

namespace Problem367.IsingObservationFactor
open IsingObservationInnovation

variable {d : ℕ} {beta : ℝ}

theorem continuousRootCovariance_uniformObservation_progressive
    (hmB : ∀ t, Measurable (fun u => WienerSampler.sample u t))
    (hb : 0 ≤ beta) (v : TreeVertex d) :
    IsStronglyProgressive
      (ArrayPosteriorStationarity.filtration (fun t u => WienerSampler.sample u t) hmB)
      (fun t q => continuousRootCovariance hb v t (uniformObservation q)) :=
  progressive_uniformObservation hmB (continuousRootCovariance_progressive hb v)

theorem continuousRootCovariance_uniformObservation_stronglyAdapted
    (hmB : ∀ t, Measurable (fun u => WienerSampler.sample u t))
    (hb : 0 ≤ beta) (v : TreeVertex d) :
    StronglyAdapted
      (ArrayPosteriorStationarity.filtration (fun t u => WienerSampler.sample u t) hmB)
      (fun t q => continuousRootCovariance hb v t (uniformObservation q)) :=
  (continuousRootCovariance_uniformObservation_progressive hmB hb v).stronglyAdapted

theorem continuousRootCovariance_uniformObservation_abs_le_one
    (hb : 0 ≤ beta) (v : TreeVertex d) (t : ℝ≥0) (q : IsingInnovation.State d ℝ) :
    |continuousRootCovariance hb v t (uniformObservation q)| ≤ 1 :=
  continuousRootCovariance_abs_le_one hb v t (uniformObservation q)

theorem continuousRootCovariance_uniformObservation_continuous_ae
    (hd : 3 ≤ d) {μ : Measure (TreeVertex d → IsingSpin)}
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hb : 0 ≤ beta)
    (hcrit : ((d - 1 : ℕ) : ℝ) * Real.tanh beta ^ 2 ≤ 1) (v : TreeVertex d) :
    ∀ᵐ q ∂μ.prod (labelMeasure d),
      Continuous (fun t => continuousRootCovariance hb v t (uniformObservation q)) :=
  (measurePreserving_uniformObservation μ).quasiMeasurePreserving.ae
    (continuousRootCovariance_continuous_ae hd hμ hb hcrit v)

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

theorem innovationMap_isBrownianReal {d : ℕ} {beta : ℝ}
    {μ : Measure (TreeVertex d → IsingSpin)}
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (v : TreeVertex d) :
    IsBrownianReal (fun t x => innovationMap beta x v t) (observationLaw μ) := by
  have hpath : HasLaw (fun x => innovationMap beta x v)
      WienerSampler.wienerMeasure (observationLaw μ) := by
    refine ⟨((measurable_pi_apply v).comp (measurable_innovationMap beta)).aemeasurable, ?_⟩
    rw [show (fun x => innovationMap beta x v) =
      (fun y : Paths d => y v) ∘ innovationMap beta from rfl,
      ← Measure.map_map (measurable_pi_apply v) (measurable_innovationMap beta),
      map_innovationMap_observationLaw hμ, Measure.infinitePi_map_eval]
  exact { hasLaw := fun I => (WienerSampler.coordinate_isBrownianReal.hasLaw I).comp hpath
          cont := Filter.Eventually.of_forall (fun x => (innovationMap beta x v).continuous) }

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
-- module Solutions.Q243_FreeIsing.FreeIsing_Ising_CanonicalCoordinateIdentification
attribute [-simp] _root_.OAI.Problem367.CutContinuationChannels.averageChannel_globalCone _root_.OAI.Problem367.CutContinuationChannels.continuationChannel_globalCone _root_.OAI.Problem367.FactorObservable.centeredSpinLp_coe _root_.OAI.Problem367.FiniteIsingSplit.splitEquiv_fst _root_.OAI.Problem367.FiniteIsingSplit.splitEquiv_snd _root_.OAI.Problem367.IsingOrientedPath.attenuation_outward _root_.OAI.Problem367.IsingOrientedPath.endpoint_extensionAt _root_.OAI.Problem367.PathSideBranches.parent_sideVertex _root_.OAI.Problem367.PathSideBranches.restrictNoisyRegion_array _root_.OAI.Problem367.PathSideBranches.sideVertex_length _root_.OAI.Problem367.PathSideBranches.sideVertex_val _root_.OAI.Problem367.TreeConeCoding.length_vertex _root_.OAI.Problem367.TreeConeCoding.vertex_nil _root_.OAI.Problem367.TreeConeCoding.vertex_val _root_.OAI.Problem367.TreeKoopman.centeredGenerator_apply_coe _root_.OAI.Problem367.TreeKoopman.centeredGenerator_sq _root_.OAI.Problem367.TreeKoopman.reverseVertex_twice _root_.OAI.Problem367.dropVertex_length _root_.OAI.Problem367.dropVertex_val _root_.OAI.Problem367.mem_rootComplementFinset _root_.OAI.Problem367.mem_rootComponentFinset _root_.OAI.Problem367.mem_rootComponentIndices _root_.OAI.Problem367.prefixColorAut_length _root_.OAI.Problem367.prefixColorAut_val _root_.OAI.Problem367.prefixColorMap_symm_apply
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

theorem finiteCovariance_tendsto_version_timeMeanSquare
    {beta : ℝ} {μ : Measure (TreeVertex d → IsingSpin)}
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ)
    (ν : Measure A) {B : ℝ≥0 → A → ℝ} (hB : IsPreBrownianReal B ν)
    (hmB : ∀ t, Measurable (B t)) (hcB : ∀ a, Continuous (fun t => B t a))
    (v u : TreeVertex d) (T : ℝ≥0)
    {H : ℝ≥0 → State d A → ℝ}
    (hver : ∀ t, H t =ᵐ[μ.prod (Measure.infinitePi (fun _ : TreeVertex d => ν))]
      covariance beta B v u t) :
    Tendsto (fun n => ∫ t in (0 : ℝ)..(T : ℝ), ∫ q,
      (finiteCovariance beta B v u n t.toNNReal q - H t.toNNReal q) ^ 2
        ∂μ.prod (Measure.infinitePi (fun _ : TreeVertex d => ν))) atTop (𝓝 0) := by
  let : IsProbabilityMeasure μ := hμ.isProbabilityMeasure
  let : IsProbabilityMeasure ν := hB.isGaussianProcess.isProbabilityMeasure
  let P := μ.prod (Measure.infinitePi (fun _ : TreeVertex d => ν))
  let τ := volume.restrict (Set.Ioc (0 : ℝ) (T : ℝ))
  have heq (n : ℕ) :
      (∫ t in (0 : ℝ)..(T : ℝ), ∫ q,
        (finiteCovariance beta B v u n t.toNNReal q - H t.toNNReal q) ^ 2 ∂P) =
      ∫ p : ℝ × State d A,
        (finiteCovariance beta B v u n p.1.toNNReal p.2 -
          covariance beta B v u p.1.toNNReal p.2) ^ 2 ∂τ.prod P := by
    calc
      _ = ∫ t in (0 : ℝ)..(T : ℝ), ∫ q,
          (finiteCovariance beta B v u n t.toNNReal q -
            covariance beta B v u t.toNNReal q) ^ 2 ∂P := by
        apply intervalIntegral.integral_congr
        intro t ht
        apply integral_congr_ae
        filter_upwards [hver t.toNNReal] with q hq
        rw [hq]
      _ = _ := interval_integral_eq_timeSpace T
        ((memLp_finiteCovariance_time beta B hmB hcB P τ v u n).sub
          (memLp_covariance_time beta B hmB hcB P τ v u)).integrable_sq
  exact (finiteCovariance_tendsto_timeMeanSquare hμ ν hB hmB hcB v u T).congr'
    (Eventually.of_forall fun n => (heq n).symm)

end Problem367.IsingInnovation

namespace Problem367.IsingObservationFactor
open IsingObservationInnovation

theorem canonical_covariance_coordinate_integral_eq_pullback
    {d : ℕ} (hd : 3 ≤ d) {beta : ℝ}
    {μ : Measure (TreeVertex d → IsingSpin)}
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hb : 0 ≤ beta)
    (hcrit : ((d - 1 : ℕ) : ℝ) * Real.tanh beta ^ 2 ≤ 1)
    (u : TreeVertex d) (T : ℝ≥0)
    {X : ℕ → IsingInnovation.State d ℝ → ℝ}
    {I : IsingInnovation.State d ℝ → ℝ}
    (hX : ∀ n, MemLp (X n) 2 (μ.prod (labelMeasure d)))
    (hI : MemLp I 2 (μ.prod (labelMeasure d)))
    (hXlim : ∀ n, Tendsto (fun k => ∫ q,
      (BrownianGrid.uniformSum
        (IsingInnovation.innovation beta (fun t r => WienerSampler.sample r t) u)
        (IsingInnovation.finiteCovariance beta (fun t r => WienerSampler.sample r t)
          (ConnectedHull.root d) u n) T k q - X n q) ^ 2
        ∂μ.prod (labelMeasure d)) atTop (𝓝 0))
    (hXI : Tendsto (fun n => ∫ q, (X n q - I q) ^ 2
      ∂μ.prod (labelMeasure d)) atTop (𝓝 0))
    {J : Paths d → ℝ} (hJ : MemLp J 2 (observationLaw μ))
    (hJlim : Tendsto (fun k => ∫ x,
      (BrownianGrid.uniformSum (fun t x => innovationMap beta x u t)
        (continuousRootCovariance hb u) T k x - J x) ^ 2
        ∂observationLaw μ) atTop (𝓝 0)) :
    I =ᵐ[μ.prod (labelMeasure d)] J ∘ uniformObservation := by
  let : IsProbabilityMeasure μ := hμ.isProbabilityMeasure
  let B : ℝ≥0 → ℝ → ℝ := fun t r => WienerSampler.sample r t
  have hmB (t : ℝ≥0) : Measurable (B t) :=
    (continuous_eval_const t).measurable.comp WienerSampler.measurable_sample
  have hcB (r : ℝ) : Continuous (fun t => B t r) :=
    (WienerSampler.sample r).continuous
  have hB : IsPreBrownianReal B uniform01 :=
    WienerSampler.sample_isBrownianReal.toIsPreBrownianReal
  have hφ : MeasurePreserving (uniformObservation (d := d))
      (μ.prod (labelMeasure d)) (observationLaw μ) :=
    ⟨measurable_uniformObservation, rfl⟩
  let H : ℝ≥0 → IsingInnovation.State d ℝ → ℝ :=
    fun t q => continuousRootCovariance hb u t (uniformObservation q)
  have hH := continuousRootCovariance_uniformObservation_stronglyAdapted hmB hb u
  have hcH := continuousRootCovariance_uniformObservation_continuous_ae hd hμ hb hcrit u
  have hbH : ∀ᵐ q ∂μ.prod (labelMeasure d), ∀ t, |H t q| ≤ (1 : ℝ) :=
    Eventually.of_forall fun q t =>
      continuousRootCovariance_uniformObservation_abs_le_one hb u t q
  have hver := continuousRootCovariance_uniformObservation_eq_covariance_ae hd hμ hb hcrit u
  have hC2 (t : ℝ≥0) : MemLp (continuousRootCovariance hb u t) 2
      (observationLaw μ) := by
    apply MemLp.of_bound
      (((continuousRootCovariance_progressive hb u).stronglyAdapted t).mono
        ((filtration d).le t)).aestronglyMeasurable 1
    exact Eventually.of_forall fun x => by
      simpa only [Real.norm_eq_abs] using continuousRootCovariance_abs_le_one hb u t x
  have hi (s t : ℝ≥0) (hst : s ≤ t) :=
    BrownianArrayFiltration.coordinate_increment_indep_past
      (B := fun v t x => innovationMap beta x v t) (F := filtration d)
      (s := s) (t := t)
      (innovationMap_increment_indep_filtration hμ s t hst) u
  have hS (k : ℕ) := BrownianFiltrationGrid.uniformSum_memLp
    (innovationMap_isBrownianReal hμ u).toIsPreBrownianReal
    (innovationMap_stronglyAdapted beta u) hi
    (continuousRootCovariance hb u)
    (continuousRootCovariance_progressive hb u).stronglyAdapted hC2 T k
  have hJpull := BrownianGrid.meanSquare_limit_comp hφ
    (fun k => (hS k).aestronglyMeasurable) hJ.aestronglyMeasurable hJlim
  have hcoeff := IsingInnovation.finiteCovariance_tendsto_version_timeMeanSquare
    hμ uniform01 hB hmB hcB (ConnectedHull.root d) u T hver
  apply BrownianGrid.ae_eq_of_mean_square_limits hX hI
    (hJ.comp_measurePreserving hφ) hXI
  exact BrownianFiltrationGrid.tendsto_meanSquare_of_coefficient_interval
    (IsingInnovation.isBrownianReal_innovation hμ uniform01 hB hmB hcB u).toIsPreBrownianReal
    (IsingInnovation.innovation_martingale hμ uniform01 hB hmB hcB u).stronglyAdapted
    (fun s t hst => BrownianArrayFiltration.coordinate_increment_indep_past
      (IsingInnovation.innovation_increment_indep_filtration hμ uniform01 hB hmB hcB s t hst) u)
    (fun n => IsingInnovation.finiteCovariance beta B (ConnectedHull.root d) u n) H
    (fun n => IsingInnovation.finiteCovariance_stronglyAdapted beta B hmB
      (ConnectedHull.root d) u n) hH
    (fun n => Eventually.of_forall
      (IsingInnovation.finiteCovariance_continuous beta B hcB (ConnectedHull.root d) u n)) hcH
    (fun _ => 2) 1 (fun _ => by norm_num) (by norm_num)
    (fun n => Eventually.of_forall fun q t =>
      IsingInnovation.finiteCovariance_abs_le_two beta B (ConnectedHull.root d) u n t q) hbH
    T hX (hJ.comp_measurePreserving hφ) hXlim hJpull hcoeff

end Problem367.IsingObservationFactor

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Ising_CanonicalCovarianceIntegrals
attribute [-simp] _root_.OAI.Problem367.CutContinuationChannels.averageChannel_globalCone _root_.OAI.Problem367.CutContinuationChannels.continuationChannel_globalCone _root_.OAI.Problem367.FactorObservable.centeredSpinLp_coe _root_.OAI.Problem367.FiniteIsingSplit.splitEquiv_fst _root_.OAI.Problem367.FiniteIsingSplit.splitEquiv_snd _root_.OAI.Problem367.IsingOrientedPath.attenuation_outward _root_.OAI.Problem367.IsingOrientedPath.endpoint_extensionAt _root_.OAI.Problem367.PathSideBranches.parent_sideVertex _root_.OAI.Problem367.PathSideBranches.restrictNoisyRegion_array _root_.OAI.Problem367.PathSideBranches.sideVertex_length _root_.OAI.Problem367.PathSideBranches.sideVertex_val _root_.OAI.Problem367.TreeConeCoding.length_vertex _root_.OAI.Problem367.TreeConeCoding.vertex_nil _root_.OAI.Problem367.TreeConeCoding.vertex_val _root_.OAI.Problem367.TreeKoopman.centeredGenerator_apply_coe _root_.OAI.Problem367.TreeKoopman.centeredGenerator_sq _root_.OAI.Problem367.TreeKoopman.reverseVertex_twice _root_.OAI.Problem367.dropVertex_length _root_.OAI.Problem367.dropVertex_val _root_.OAI.Problem367.mem_rootComplementFinset _root_.OAI.Problem367.mem_rootComponentFinset _root_.OAI.Problem367.mem_rootComponentIndices _root_.OAI.Problem367.prefixColorAut_length _root_.OAI.Problem367.prefixColorAut_val _root_.OAI.Problem367.prefixColorMap_symm_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped NNReal Topology

namespace Problem367.IsingObservationFactor
open IsingObservationInnovation

variable {d : ℕ} {beta : ℝ}
variable {μ : Measure (TreeVertex d → IsingSpin)}

theorem exists_canonical_root_covariance_integrals
    (hd : 3 ≤ d) (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hb : 0 ≤ beta)
    (hcrit : ((d - 1 : ℕ) : ℝ) * Real.tanh beta ^ 2 ≤ 1) :
    ∃ J : TreeVertex d → ℝ≥0 → Paths d → ℝ,
      (∀ w, IsStronglyPredictable (filtration d) (J w)) ∧
      (∀ w, Martingale (J w) (filtration d) (observationLaw μ)) ∧
      (∀ w, ∀ᵐ x ∂observationLaw μ, Continuous (fun t => J w t x)) ∧
      (∀ w t, MemLp (J w t) 2 (observationLaw μ)) ∧
      (∀ w, J w 0 =ᵐ[observationLaw μ] 0) ∧
      (∀ w t, (∫ x, J w t x ∂observationLaw μ) = 0) ∧
      (∀ w t, (∫ x, J w t x ^ 2 ∂observationLaw μ) =
        ∫ s in (0 : ℝ)..(t : ℝ), ∫ x,
          continuousRootCovariance hb w s.toNNReal x ^ 2 ∂observationLaw μ) ∧
      (∀ w (N : ℕ), 0 < N → ∀ t ≤ (N : ℝ≥0),
        Tendsto (fun n => ∫ x,
          (BrownianIntegralProcess.stoppedUniformSum
            (fun s x => innovationMap beta x w s)
            (continuousRootCovariance hb w) N n t x - J w t x) ^ 2
            ∂observationLaw μ) atTop (𝓝 0)) := by
  have hex (w : TreeVertex d) :=
    BrownianIntegralProcess.exists_global_continuous_uniform_integral
      (innovationMap_isBrownianReal hμ w).toIsPreBrownianReal
      (innovationMap_stronglyAdapted beta w)
      (fun s t hst => BrownianArrayFiltration.coordinate_increment_indep_past
        (B := fun w s x => innovationMap beta x w s)
        (F := filtration d)
        (innovationMap_increment_indep_filtration hμ s t hst) w)
      (innovationMap_isBrownianReal hμ w).cont
      (continuousRootCovariance_progressive hb w).stronglyAdapted
      (continuousRootCovariance_continuous_ae hd hμ hb hcrit w)
      (show (0 : ℝ) ≤ 1 by norm_num)
      (Eventually.of_forall (fun x t => continuousRootCovariance_abs_le_one hb w t x))
  choose J hJp hJM hJc hJ2 hJ0 hJmean hJenergy hJlim using hex
  exact ⟨J, hJp, hJM, hJc, hJ2, hJ0, hJmean, hJenergy, hJlim⟩

end Problem367.IsingObservationFactor

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Ising_ObservationPosteriorMartingale
attribute [-instance] _root_.OAI.Problem367.IsingConditionalCopyBounds.graphLaw_isProbabilityMeasure _root_.OAI.Problem367.IsingObservationFactor.copies_probability _root_.OAI.Problem367.IsingObservationFactor.kernel_markov _root_.OAI.Problem367.TreeKoopman.labelProbability _root_.OAI.Problem367.freeIsingMeasure_probability
attribute [-simp] _root_.OAI.Problem367.ConnectedHull.pathAssignment_path _root_.OAI.Problem367.ConnectedHull.path_last _root_.OAI.Problem367.ConnectedHull.path_zero _root_.OAI.Problem367.ContinuousNoiseSplit.futurePath_apply _root_.OAI.Problem367.ContinuousObservationHistory.stoppedPath_apply _root_.OAI.Problem367.CutContinuationChannels.averageChannel_globalCone _root_.OAI.Problem367.CutContinuationChannels.continuationChannel_globalCone _root_.OAI.Problem367.FactorObservable.centeredSpinLp_coe _root_.OAI.Problem367.FiniteIsingSplit.splitEquiv_fst _root_.OAI.Problem367.FiniteIsingSplit.splitEquiv_snd _root_.OAI.Problem367.FinitePathGibbs.tailPartition_zero _root_.OAI.Problem367.GaussianTreeResponseNaturality.fieldEquiv_apply_image _root_.OAI.Problem367.IsingOrientedPath.attenuation_outward _root_.OAI.Problem367.IsingOrientedPath.endpoint_extensionAt _root_.OAI.Problem367.LocalSupportGeometry.prefixVertex_length _root_.OAI.Problem367.PathSideBranches.parent_sideVertex _root_.OAI.Problem367.PathSideBranches.restrictNoisyRegion_array _root_.OAI.Problem367.PathSideBranches.sideVertex_length _root_.OAI.Problem367.PathSideBranches.sideVertex_val _root_.OAI.Problem367.PosteriorChain.transition_spinMean _root_.OAI.Problem367.PosteriorChain.transition_sum _root_.OAI.Problem367.RootedBroadcast.flipBranchToComplement_val _root_.OAI.Problem367.RootedBroadcast.pos_spinMul _root_.OAI.Problem367.RootedBroadcast.prefixFlip_branchRoot _root_.OAI.Problem367.RootedBroadcast.prefixFlip_root _root_.OAI.Problem367.RootedBroadcast.prefixTreeAut_symm_branchRoot _root_.OAI.Problem367.RootedBroadcast.prefixTreeAut_symm_root _root_.OAI.Problem367.RootedBroadcast.spinMul_pos _root_.OAI.Problem367.RootedBroadcast.spinMul_self _root_.OAI.Problem367.TreeConeCoding.length_vertex _root_.OAI.Problem367.TreeConeCoding.vertex_nil _root_.OAI.Problem367.TreeConeCoding.vertex_val _root_.OAI.Problem367.TreeGibbsAut.spinEquiv_apply_image _root_.OAI.Problem367.TreeKoopman.centeredAverage_apply_coe _root_.OAI.Problem367.TreeKoopman.centeredAverage_pow_apply_coe _root_.OAI.Problem367.TreeKoopman.centeredGenerator_apply_coe _root_.OAI.Problem367.TreeKoopman.centeredGenerator_sq _root_.OAI.Problem367.TreeKoopman.generatorOperator_sq _root_.OAI.Problem367.TreeKoopman.reverseVertex_twice _root_.OAI.Problem367.TreeKoopman.wordRelabel_cons _root_.OAI.Problem367.TreeKoopman.wordRelabel_nil _root_.OAI.Problem367.TreeLawKoopman.centeredAverage_apply_coe _root_.OAI.Problem367.TreeLawKoopman.generatorOperator_sq _root_.OAI.Problem367.TreePathGibbs.vertexEquiv_val _root_.OAI.Problem367.branchColorAut_length _root_.OAI.Problem367.branchColorAut_singleton _root_.OAI.Problem367.branchColorAut_val _root_.OAI.Problem367.branchColorMap_symm_apply _root_.OAI.Problem367.colorPermAut_length _root_.OAI.Problem367.colorPermAut_nil _root_.OAI.Problem367.colorPermAut_val _root_.OAI.Problem367.colorPermMap_symm_apply _root_.OAI.Problem367.colorPermMap_val _root_.OAI.Problem367.connectedSpinEncode_apply_root _root_.OAI.Problem367.connectedSpinEquiv_apply _root_.OAI.Problem367.dropVertex_length _root_.OAI.Problem367.dropVertex_val _root_.OAI.Problem367.mem_rootComplementFinset _root_.OAI.Problem367.mem_rootComponentFinset _root_.OAI.Problem367.mem_rootComponentIndices _root_.OAI.Problem367.parentVertex_length _root_.OAI.Problem367.parentVertex_val _root_.OAI.Problem367.prefixColorAut_length _root_.OAI.Problem367.prefixColorAut_val _root_.OAI.Problem367.prefixColorMap_symm_apply _root_.OAI.Problem367.prefixFlip_twice _root_.OAI.Problem367.spinAgreementCode_eq_neg_iff _root_.OAI.Problem367.spinAgreementCode_eq_pos_iff _root_.OAI.Problem367.spinSign_flip _root_.OAI.Problem367.tsum_treeShell_radial
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace Problem367.IsingObservationInnovation
open IsingObservationRecovery

theorem integrable_decodedSpin {d : ℕ}
    (μ : Measure (TreeVertex d → IsingSpin)) [IsProbabilityMeasure μ]
    (v : TreeVertex d) :
    Integrable (fun x : Paths d => spinSign (decode x v)) (observationLaw μ) := by
  have hs : Measurable spinSign := by intro s hs; trivial
  apply Integrable.of_bound
    (hs.comp ((measurable_pi_apply v).comp measurable_decode)).aestronglyMeasurable 1
  exact Filter.Eventually.of_forall fun x => by
    cases h : decode x v <;> norm_num [spinSign, h]

theorem posterior_eq_condExp_decodedSpin {d : ℕ} {beta : ℝ}
    {μ : Measure (TreeVertex d → IsingSpin)}
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (v : TreeVertex d) (t : ℝ≥0) :
    posterior beta v t =ᵐ[observationLaw μ]
      (observationLaw μ)[fun x => spinSign (decode x v) | filtration d t] := by
  let : IsProbabilityMeasure μ := hμ.isProbabilityMeasure
  let : IsProbabilityMeasure (labelMeasure d) := by unfold labelMeasure; (first | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability))
  have hp := condExp_comp_measurePreserving (μ.prod (labelMeasure d)) (observationLaw μ)
    uniformObservation (measurePreserving_uniformObservation μ) (filtration d t)
    ((filtration d).le t) (integrable_decodedSpin μ v)
  have hd : (fun q : IsingInnovation.State d ℝ => spinSign (decode (uniformObservation q) v)) =ᵐ[
      μ.prod (labelMeasure d)] (fun q => spinSign (q.1 v)) :=
    (decode_uniformObservation_ae μ).fun_comp (fun sigma => spinSign (sigma v))
  have hc := condExp_congr_ae (m := (filtration d t).comap uniformObservation) hd
  have hmB (s : ℝ≥0) : Measurable (fun u => WienerSampler.sample u s) :=
    (continuous_eval_const s).measurable.comp WienerSampler.measurable_sample
  have hactual := hμ.infiniteGibbsSpinMean_eq_brownian_past
    (fun _ : TreeVertex d => uniform01)
    (fun _ => WienerSampler.sample_isBrownianReal.toIsPreBrownianReal)
    (fun _ => hmB) t v
  apply (ae_eq_iff_comp_measurePreserving (μ.prod (labelMeasure d)) (observationLaw μ)
    uniformObservation (measurePreserving_uniformObservation μ)
    (measurable_posterior beta v t)
    ((stronglyMeasurable_condExp.mono ((filtration d).le t)).measurable)).mpr
  filter_upwards [hp, hc, hactual] with q hp hc ha
  change posterior beta v t (uniformObservation q) = _
  simp only [Function.comp_def] at hp ⊢
  rw [← hp, hc]
  rw [filtration_comap_uniformObservation d t hmB]
  simpa only [posterior, uniformObservation, ContinuousMap.coe_mk,
    ArrayPosteriorStationarity.filtration, arrayObservationFiltration,
    arrayNaturalFiltration_eq_comap, plantedArrayObservation,
    ArrayPosteriorStationarity.spinArray, labelMeasure, add_comm] using ha

theorem posterior_martingale {d : ℕ} {beta : ℝ}
    {μ : Measure (TreeVertex d → IsingSpin)}
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (v : TreeVertex d) :
    Martingale (posterior beta v) (filtration d) (observationLaw μ) := by
  let : IsProbabilityMeasure μ := hμ.isProbabilityMeasure
  exact (martingale_condExp (fun x => spinSign (decode x v))
    (filtration d) (observationLaw μ)).congr
    (posterior_progressive beta v).stronglyAdapted
    (fun t => (posterior_eq_condExp_decodedSpin hμ v t).symm)

end Problem367.IsingObservationInnovation

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Martingales_IntegerIdentification
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Filter
open scoped NNReal Topology

namespace Problem367.MartingaleIntegerIdentification

variable {Ω : Type*} [mΩ : MeasurableSpace Ω]
  {μ : Measure Ω} {F : Filtration ℝ≥0 mΩ}

theorem meanSquare_limit_of_positive_integer [IsFiniteMeasure μ]
    {α : Type*} {l : Filter α} {X : α → ℝ≥0 → Ω → ℝ}
    {Y : ℝ≥0 → Ω → ℝ}
    (hX : ∀ a, Martingale (X a) F μ) (hY : Martingale Y F μ)
    (hX2 : ∀ a t, MemLp (X a t) 2 μ) (hY2 : ∀ t, MemLp (Y t) 2 μ)
    (hlim : ∀ N : ℕ, 0 < N → Tendsto (fun a =>
      ∫ ω, (X a N ω - Y N ω) ^ 2 ∂μ) l (𝓝 0)) (t : ℝ≥0) :
    Tendsto (fun a => ∫ ω, (X a t ω - Y t ω) ^ 2 ∂μ) l (𝓝 0) := by
  obtain ⟨N, hN⟩ := exists_nat_gt t
  have hN0 : 0 < N := by
    have hn : (0 : ℝ≥0) < (N : ℝ≥0) := lt_of_le_of_lt (show (0 : ℝ≥0) ≤ t from zero_le) hN
    exact_mod_cast hn
  apply squeeze_zero (fun a => integral_nonneg (fun ω => sq_nonneg _))
    (fun a => ?_) (hlim N hN0)
  exact MartingaleSquareMaximal.integral_sq_le ((hX a).sub hY)
    (fun s => (hX2 a s).sub (hY2 s)) hN.le

theorem finiteSum_meanSquare_of_positive_integer [IsFiniteMeasure μ]
    {ι : Type*} {M : ι → ℝ≥0 → Ω → ℝ} {Y : ℝ≥0 → Ω → ℝ}
    (hM : ∀ i, Martingale (M i) F μ) (hY : Martingale Y F μ)
    (hM2 : ∀ i t, MemLp (M i t) 2 μ) (hY2 : ∀ t, MemLp (Y t) 2 μ)
    (hlim : ∀ N : ℕ, 0 < N → Tendsto (fun s : Finset ι =>
      ∫ ω, ((∑ i ∈ s, M i N ω) - Y N ω) ^ 2 ∂μ) atTop (𝓝 0))
    (t : ℝ≥0) :
    Tendsto (fun s : Finset ι =>
      ∫ ω, ((∑ i ∈ s, M i t ω) - Y t ω) ^ 2 ∂μ) atTop (𝓝 0) := by
  exact meanSquare_limit_of_positive_integer
    (fun s => MartingaleSpatialLimit.finiteSum_martingale hM s) hY
    (fun s t => MartingaleSpatialLimit.finiteSum_memLp hM2 s t) hY2 hlim t

theorem hasSum_of_positive_integer [IsFiniteMeasure μ]
    {ι : Type*} {M : ι → ℝ≥0 → Ω → ℝ} {Y : ℝ≥0 → Ω → ℝ}
    (hM : ∀ i, Martingale (M i) F μ) (hY : Martingale Y F μ)
    (hM2 : ∀ i t, MemLp (M i t) 2 μ) (hY2 : ∀ t, MemLp (Y t) 2 μ)
    (hlim : ∀ N : ℕ, 0 < N → Tendsto (fun s : Finset ι =>
      ∫ ω, ((∑ i ∈ s, M i N ω) - Y N ω) ^ 2 ∂μ) atTop (𝓝 0))
    (t : ℝ≥0) :
    HasSum (fun i => (hM2 i t).toLp (M i t)) ((hY2 t).toLp (Y t)) := by
  have hh := (SimpleIntegral.tendsto_toLp_iff_meanSquare
    (fun s => MartingaleSpatialLimit.finiteSum_memLp hM2 s t) (hY2 t)).mpr
      (finiteSum_meanSquare_of_positive_integer hM hY hM2 hY2 hlim t)
  have he (s : Finset ι) :
      (MartingaleSpatialLimit.finiteSum_memLp hM2 s t).toLp
        (MartingaleSpatialLimit.finiteSum M s t) =
        ∑ i ∈ s, (hM2 i t).toLp (M i t) :=
    PredictableL2.toLp_finsetSum (fun i => M i t) (fun i => hM2 i t) s
  change Tendsto (fun s : Finset ι => ∑ i ∈ s, (hM2 i t).toLp (M i t))
    atTop (𝓝 ((hY2 t).toLp (Y t)))
  simpa only [he] using hh

end Problem367.MartingaleIntegerIdentification

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Ising_CanonicalIntegralRepresentation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped NNReal Topology

namespace Problem367.IsingObservationFactor
open IsingObservationInnovation

variable {d : ℕ} {beta : ℝ}
variable {μ : Measure (TreeVertex d → IsingSpin)} [IsProbabilityMeasure μ]

theorem canonical_root_covariance_integrals_hasSum
    (hd : 3 ≤ d) (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hb : 0 ≤ beta)
    (hcrit : ((d - 1 : ℕ) : ℝ) * Real.tanh beta ^ 2 ≤ 1)
    (T : ℝ≥0) (J : TreeVertex d → Paths d → ℝ)
    (hJ : ∀ w, MemLp (J w) 2 (observationLaw μ))
    (hJlim : ∀ w, Tendsto (fun n => ∫ x,
      (BrownianGrid.uniformSum (fun s x => innovationMap beta x w s)
        (continuousRootCovariance hb w) T n x - J w x) ^ 2 ∂observationLaw μ)
      atTop (𝓝 0)) :
    HasSum (fun w => (hJ w).toLp (J w))
      ((posterior_memLp beta μ (ConnectedHull.root d) T 2).toLp
        (posterior beta (ConnectedHull.root d) T)) := by
  let B : ℝ≥0 → ℝ → ℝ := fun s r => WienerSampler.sample r s
  have hmB (s : ℝ≥0) : Measurable (B s) :=
    (continuous_eval_const s).measurable.comp WienerSampler.measurable_sample
  have hcB (r : ℝ) : Continuous (fun s => B s r) :=
    (WienerSampler.sample r).continuous
  obtain ⟨X, I, hI, hM, hX, hXlim, hXI, _hmI, _htI, _hzero, hsum, _herror⟩ :=
    IsingInnovation.exists_posterior_integral_representation hμ hd hb hcrit
      uniform01 WienerSampler.sample_isBrownianReal.toIsPreBrownianReal
      hmB hcB (ConnectedHull.root d) T
  have hIJ (w : TreeVertex d) : I w =ᵐ[μ.prod (labelMeasure d)]
      J w ∘ uniformObservation := by
    exact canonical_covariance_coordinate_integral_eq_pullback hd hμ hb hcrit w T
      (fun n => hX n w) (hI w) (fun n => hXlim n w) (hXI w) (hJ w) (hJlim w)
  exact PredictableL2.hasSum_toLp_descend_of_comp_ae
    (measurePreserving_uniformObservation μ) J hJ
    (posterior_memLp beta μ (ConnectedHull.root d) T 2)
    I hI hM hIJ (Eventually.of_forall (fun _ => rfl)) hsum

theorem canonical_root_covariance_integrals_hasSum_all_time
    (hd : 3 ≤ d) (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hb : 0 ≤ beta)
    (hcrit : ((d - 1 : ℕ) : ℝ) * Real.tanh beta ^ 2 ≤ 1)
    (J : TreeVertex d → ℝ≥0 → Paths d → ℝ)
    (hJM : ∀ w, Martingale (J w) (filtration d) (observationLaw μ))
    (hJ2 : ∀ w t, MemLp (J w t) 2 (observationLaw μ))
    (hJlim : ∀ w (N : ℕ), 0 < N → ∀ t ≤ (N : ℝ≥0),
      Tendsto (fun n => ∫ x,
        (BrownianIntegralProcess.stoppedUniformSum
          (fun s x => innovationMap beta x w s)
          (continuousRootCovariance hb w) N n t x - J w t x) ^ 2
          ∂observationLaw μ) atTop (𝓝 0)) (t : ℝ≥0) :
    HasSum (fun w => (hJ2 w t).toLp (J w t))
      ((posterior_memLp beta μ (ConnectedHull.root d) t 2).toLp
        (posterior beta (ConnectedHull.root d) t)) := by
  apply MartingaleIntegerIdentification.hasSum_of_positive_integer hJM
    (posterior_martingale hμ (ConnectedHull.root d)) hJ2
    (fun s => posterior_memLp beta μ (ConnectedHull.root d) s 2) ?_ t
  intro N hN
  have happrox (w : TreeVertex d) : Tendsto (fun n => ∫ x,
      (BrownianGrid.uniformSum (fun s x => innovationMap beta x w s)
        (continuousRootCovariance hb w) N n x - J w N x) ^ 2 ∂observationLaw μ)
      atTop (𝓝 0) := by
    simpa only [BrownianIntegralProcess.stoppedUniformSum_terminal] using
      hJlim w N hN N le_rfl
  have hterminal := canonical_root_covariance_integrals_hasSum hd hμ hb hcrit
    (N : ℝ≥0) (fun w => J w N) (fun w => hJ2 w N) happrox
  exact PredictableL2.tendsto_integral_sq_error_of_hasSum
    (fun w => J w N) (fun w => hJ2 w N)
    (posterior_memLp beta μ (ConnectedHull.root d) N 2) hterminal

theorem exists_canonical_root_covariance_integral_representation_oai
    (hd : 3 ≤ d) (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hb : 0 ≤ beta)
    (hcrit : ((d - 1 : ℕ) : ℝ) * Real.tanh beta ^ 2 ≤ 1) :
    ∃ (J : TreeVertex d → ℝ≥0 → Paths d → ℝ)
      (hJ2 : ∀ w t, MemLp (J w t) 2 (observationLaw μ)),
      (∀ w, IsStronglyPredictable (filtration d) (J w)) ∧
      (∀ w, Martingale (J w) (filtration d) (observationLaw μ)) ∧
      (∀ w, ∀ᵐ x ∂observationLaw μ, Continuous (fun t => J w t x)) ∧
      (∀ w, J w 0 =ᵐ[observationLaw μ] 0) ∧
      (∀ w t, (∫ x, J w t x ∂observationLaw μ) = 0) ∧
      (∀ w t, (∫ x, J w t x ^ 2 ∂observationLaw μ) =
        ∫ s in (0 : ℝ)..(t : ℝ), ∫ x,
          continuousRootCovariance hb w s.toNNReal x ^ 2 ∂observationLaw μ) ∧
      (∀ w (N : ℕ), 0 < N → ∀ t ≤ (N : ℝ≥0),
        Tendsto (fun n => ∫ x,
          (BrownianIntegralProcess.stoppedUniformSum
            (fun s x => innovationMap beta x w s)
            (continuousRootCovariance hb w) N n t x - J w t x) ^ 2
            ∂observationLaw μ) atTop (𝓝 0)) ∧
      (∀ t, HasSum (fun w => (hJ2 w t).toLp (J w t))
        ((posterior_memLp beta μ (ConnectedHull.root d) t 2).toLp
          (posterior beta (ConnectedHull.root d) t))) := by
  obtain ⟨J, hJp, hJM, hJc, hJ2, hJ0, hJmean, hJenergy, hJlim⟩ :=
    exists_canonical_root_covariance_integrals hd hμ hb hcrit
  exact ⟨J, hJ2, hJp, hJM, hJc, hJ0, hJmean, hJenergy, hJlim,
    canonical_root_covariance_integrals_hasSum_all_time hd hμ hb hcrit J hJM hJ2 hJlim⟩

end Problem367.IsingObservationFactor

end

end OAI
end

theorem solution : type_of% @OAI.Problem367.IsingObservationFactor.exists_canonical_root_covariance_integral_representation_oai := @OAI.Problem367.IsingObservationFactor.exists_canonical_root_covariance_integral_representation_oai
