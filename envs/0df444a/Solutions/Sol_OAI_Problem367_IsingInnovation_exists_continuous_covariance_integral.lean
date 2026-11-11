-- Prove2me | solution 1 for OAI.Problem367.IsingInnovation.exists_continuous_covariance_integral
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T01:44:14.885869+00:00
-- url     : https://prove2.me/submissions/2e6a059e-ba04-48a4-8ca9-f951ec683457

import Mathlib
import Mathlib.MeasureTheory.Integral.Marginal
import Definitions.Def_FreeIsing
import Definitions.Def_Q243FI005
import Theorems.Thm_OAI_Problem367_BrownianArrayFiltration_exists_global_continuous_spatial_integral
import Theorems.Thm_OAI_Problem367_IsingInnovation_finiteCovariance_fullTime_interval_energy_cauchy

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
-- module Solutions.Q243_FreeIsing.FreeIsing_Martingales_SpatialPredictableL2
attribute [-instance] _root_.OAI.Problem367.WienerSampler.pathMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators Topology

namespace Problem367.PredictableL2

theorem memLp_two_mul_of_indep
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {f g : Ω → ℝ} (hind : IndepFun f g μ)
    (hf : MemLp f 2 μ) (hg : MemLp g 2 μ) :
    MemLp (fun ω => f ω * g ω) 2 μ := by
  apply (memLp_two_iff_integrable_sq (hf.aestronglyMeasurable.mul
    hg.aestronglyMeasurable)).2
  have hi := (hind.comp (measurable_id.pow_const 2) (measurable_id.pow_const 2)).integrable_mul
    hf.integrable_sq hg.integrable_sq
  simpa only [Function.comp_def, Pi.mul_def, mul_pow, id_eq] using hi

theorem weighted_array_orthogonal
    {Ω ι : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {H D : Ω → ι → ℝ} (hind : IndepFun H D μ)
    (hH : ∀ i, MemLp (fun ω => H ω i) 2 μ)
    (hD : ∀ i, MemLp (fun ω => D ω i) 2 μ)
    (horth : Pairwise fun i j => ∫ ω, D ω i * D ω j ∂μ = 0) :
    Pairwise fun i j => ∫ ω, (H ω i * D ω i) * (H ω j * D ω j) ∂μ = 0 := by
  intro i j hij
  have hp := hind.comp ((measurable_pi_apply i).mul (measurable_pi_apply j))
    ((measurable_pi_apply i).mul (measurable_pi_apply j))
  have hi := hp.integral_fun_mul_eq_mul_integral
    ((hH i).aestronglyMeasurable.mul (hH j).aestronglyMeasurable)
    ((hD i).aestronglyMeasurable.mul (hD j).aestronglyMeasurable)
  calc
    _ = ∫ ω, (H ω i * H ω j) * (D ω i * D ω j) ∂μ := by
      congr 1
      funext ω
      ring
    _ = (∫ ω, H ω i * H ω j ∂μ) * ∫ ω, D ω i * D ω j ∂μ := hi
    _ = 0 := by rw [horth hij, mul_zero]

end Problem367.PredictableL2

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Brownian_ArraySimpleIntegral
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped NNReal BigOperators

namespace Problem367.SimpleIntegral

theorem predictable_array_increments_orthogonal
    {Ω ι : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsFiniteMeasure P]
    (F : Filtration ℕ mΩ) (H D : ι → ℕ → Ω → ℝ)
    (hH : ∀ a k, StronglyMeasurable[F k] (H a k))
    (hD : ∀ a k, StronglyMeasurable[F (k + 1)] (D a k))
    (hDi : ∀ a k, Integrable (D a k) P)
    (hHD : ∀ a k, MemLp (fun ω => H a k ω * D a k ω) 2 P)
    (hz : ∀ a k, P[D a k | F k] =ᵐ[P] 0)
    (hsame : ∀ k, Pairwise fun a b =>
      ∫ ω, (H a k ω * D a k ω) * (H b k ω * D b k ω) ∂P = 0) :
    Pairwise fun p q : ι × ℕ => ∫ ω,
      (H p.1 p.2 ω * D p.1 p.2 ω) * (H q.1 q.2 ω * D q.1 q.2 ω) ∂P = 0 := by
  have hoff (a b : ι) (i j : ℕ) (hij : i < j) :
      (∫ ω, (H a i ω * D a i ω) * (H b j ω * D b j ω) ∂P) = 0 := by
    have hc : StronglyMeasurable[F j] (fun ω => (H a i ω * D a i ω) * H b j ω) := by
      simpa only [Pi.mul_def] using
        (((hH a i).mono (F.mono hij.le)).mul
          ((hD a i).mono (F.mono (Nat.succ_le_of_lt hij)))).mul (hH b j)
    have hp : Integrable ((fun ω => (H a i ω * D a i ω) * H b j ω) * D b j) P := by
      simpa only [Pi.mul_def, mul_assoc] using (hHD a i).integrable_mul (hHD b j)
    simpa only [mul_assoc] using
      integral_mul_eq_zero_of_condExp_eq_zero (F.le j) hc (hDi b j) hp (hz b j)
  intro p q hpq
  rcases lt_trichotomy p.2 q.2 with h | h | h
  · exact hoff p.1 q.1 p.2 q.2 h
  · have hab : p.1 ≠ q.1 := fun ha => hpq (Prod.ext ha h)
    simpa only [h] using hsame q.2 hab
  · simpa only [mul_comm] using hoff q.1 p.1 q.2 p.2 h

theorem integral_mul_sums_eq_zero
    {Ω ι κ : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    (X : ι → Ω → ℝ) (Y : κ → Ω → ℝ)
    (hX : ∀ i, MemLp (X i) 2 P) (hY : ∀ j, MemLp (Y j) 2 P)
    (horth : ∀ i j, ∫ ω, X i ω * Y j ω ∂P = 0)
    (s : Finset ι) (t : Finset κ) :
    (∫ ω, (∑ i ∈ s, X i ω) * (∑ j ∈ t, Y j ω) ∂P) = 0 := by
  have hint (i : ι) (j : κ) : Integrable (fun ω => X i ω * Y j ω) P :=
    (hX i).integrable_mul (hY j)
  simp_rw [Finset.sum_mul_sum]
  rw [integral_finsetSum s (fun i _ =>
    integrable_finsetSum t (fun j _ => hint i j))]
  apply Finset.sum_eq_zero
  intro i hi
  rw [integral_finsetSum t (fun j _ => hint i j)]
  exact Finset.sum_eq_zero fun j _ => horth i j

end Problem367.SimpleIntegral

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

theorem ae_eq_of_dense_evaluations
    {Ω T E I : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [TopologicalSpace T] [TopologicalSpace E] [T2Space E] [Countable I]
    (e : I → T) (he : DenseRange e) {f g : Ω → T → E}
    (hf : ∀ᵐ ω ∂μ, Continuous (f ω)) (hg : ∀ᵐ ω ∂μ, Continuous (g ω))
    (hfg : ∀ i, ∀ᵐ ω ∂μ, f ω (e i) = g ω (e i)) : f =ᵐ[μ] g := by
  have hall : ∀ᵐ ω ∂μ, ∀ i, f ω (e i) = g ω (e i) :=
    ae_all_iff.mpr hfg
  filter_upwards [hf, hg, hall] with ω hfω hgω hω
  exact he.equalizer hfω hgω (funext hω)

theorem ae_eq_of_continuous_of_evaluation_ae_eq
    {Ω T E : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [TopologicalSpace T] [SeparableSpace T] [Nonempty T]
    [TopologicalSpace E] [T2Space E] {f g : Ω → T → E}
    (hf : ∀ᵐ ω ∂μ, Continuous (f ω)) (hg : ∀ᵐ ω ∂μ, Continuous (g ω))
    (hfg : ∀ t, ∀ᵐ ω ∂μ, f ω t = g ω t) : f =ᵐ[μ] g := by
  exact ae_eq_of_dense_evaluations (TopologicalSpace.denseSeq T)
    (TopologicalSpace.denseRange_denseSeq T) hf hg (fun _ => hfg _)

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

theorem coefficients_indep_increments {s t : ℝ≥0}
    (hind : Indep
      (MeasurableSpace.comap (fun ω a => B a t ω - B a s ω) inferInstance) (F s) P)
    {H : ι → Ω → ℝ} (hH : ∀ a, StronglyMeasurable[F s] (H a)) :
    IndepFun (fun ω a => H a ω) (fun ω a => B a t ω - B a s ω) P := by
  have hm : Measurable[F s] (fun ω a => H a ω) := by
    let : MeasurableSpace Ω := F s
    exact Measurable.of_eval fun a => (hH a).measurable
  exact indep_of_indep_of_le_left hind.symm hm.comap_le

theorem grid_orthogonal [IsProbabilityMeasure P]
    (hB : ∀ a, IsPreBrownianReal (B a) P)
    (hAd : ∀ a, StronglyAdapted F (B a))
    (hind : ∀ s t, s ≤ t → Indep
      (MeasurableSpace.comap (fun ω a => B a t ω - B a s ω) inferInstance) (F s) P)
    (hcross : ∀ s t, s ≤ t → Pairwise fun a b =>
      IndepFun (fun ω => B a t ω - B a s ω) (fun ω => B b t ω - B b s ω) P)
    (t : ℕ → ℝ≥0) (ht : Monotone t) (H : ι → ℕ → Ω → ℝ)
    (hH : ∀ a k, StronglyMeasurable[F (t k)] (H a k))
    (hH2 : ∀ a k, MemLp (H a k) 2 P) :
    Pairwise fun p q : ι × ℕ => ∫ ω,
      (H p.1 p.2 ω * (B p.1 (t (p.2 + 1)) ω - B p.1 (t p.2) ω)) *
      (H q.1 q.2 ω * (B q.1 (t (q.2 + 1)) ω - B q.1 (t q.2) ω)) ∂P = 0 := by
  let G : Filtration ℕ mΩ :=
    ⟨fun k => F (t k), fun _ _ h => F.mono (ht h), fun k => F.le (t k)⟩
  let D : ι → ℕ → Ω → ℝ := fun a k ω => B a (t (k + 1)) ω - B a (t k) ω
  have hD2 (a : ι) (k : ℕ) : MemLp (D a k) 2 P :=
    ((hB a).isGaussianProcess.hasGaussianLaw_eval (t (k + 1))).memLp_two.sub
      ((hB a).isGaussianProcess.hasGaussianLaw_eval (t k)).memLp_two
  have hi (k : ℕ) : IndepFun (fun ω a => H a k ω) (fun ω a => D a k ω) P :=
    coefficients_indep_increments (hind _ _ (ht (Nat.le_succ k))) (fun a => hH a k)
  have hHD (a : ι) (k : ℕ) : MemLp (fun ω => H a k ω * D a k ω) 2 P :=
    PredictableL2.memLp_two_mul_of_indep
      ((hi k).comp (measurable_pi_apply a) (measurable_pi_apply a)) (hH2 a k) (hD2 a k)
  have hz (a : ι) (k : ℕ) : (∫ ω, D a k ω ∂P) = 0 := by
    change (∫ ω, B a (t (k + 1)) ω - B a (t k) ω ∂P) = 0
    rw [integral_sub ((hB a).integrable_eval _) ((hB a).integrable_eval _),
      (hB a).integral_eval, (hB a).integral_eval, sub_self]
  have hnoise (k : ℕ) : Pairwise fun a b => ∫ ω, D a k ω * D b k ω ∂P = 0 := by
    intro a b hab
    have heq := (hcross _ _ (ht (Nat.le_succ k)) hab).integral_fun_mul_eq_mul_integral
      (hD2 a k).aestronglyMeasurable (hD2 b k).aestronglyMeasurable
    change (∫ ω, D a k ω * D b k ω ∂P) =
      (∫ ω, D a k ω ∂P) * ∫ ω, D b k ω ∂P at heq
    simpa only [hz, zero_mul] using heq
  apply SimpleIntegral.predictable_array_increments_orthogonal G H D hH
  · intro a k
    exact (hAd a (t (k + 1))).sub
      ((hAd a (t k)).mono (F.mono (ht (Nat.le_succ k))))
  · exact fun a k => (hD2 a k).integrable (by norm_num)
  · exact hHD
  · intro a k
    exact BrownianFiltration.increment_condExp_zero (hB a) (hAd a)
      (coordinate_increment_indep_past (hind _ _ (ht (Nat.le_succ k))) a)
  · intro k
    exact PredictableL2.weighted_array_orthogonal (hi k) (fun a => hH2 a k)
      (fun a => hD2 a k) (hnoise k)

theorem grid_sums_orthogonal [IsProbabilityMeasure P]
    (hB : ∀ a, IsPreBrownianReal (B a) P)
    (hAd : ∀ a, StronglyAdapted F (B a))
    (hind : ∀ s t, s ≤ t → Indep
      (MeasurableSpace.comap (fun ω a => B a t ω - B a s ω) inferInstance) (F s) P)
    (hcross : ∀ s t, s ≤ t → Pairwise fun a b =>
      IndepFun (fun ω => B a t ω - B a s ω) (fun ω => B b t ω - B b s ω) P)
    (t : ℕ → ℝ≥0) (ht : Monotone t) (H : ι → ℕ → Ω → ℝ)
    (hH : ∀ a k, StronglyMeasurable[F (t k)] (H a k))
    (hH2 : ∀ a k, MemLp (H a k) 2 P)
    {a b : ι} (hab : a ≠ b) (u v : Finset ℕ) :
    (∫ ω, (∑ k ∈ u, H a k ω * (B a (t (k + 1)) ω - B a (t k) ω)) *
      (∑ k ∈ v, H b k ω * (B b (t (k + 1)) ω - B b (t k) ω)) ∂P) = 0 := by
  have hHD (a : ι) (k : ℕ) : MemLp
      (fun ω => H a k ω * (B a (t (k + 1)) ω - B a (t k) ω)) 2 P :=
    BrownianFiltration.predictable_mul_memLp_two (hB a)
      (coordinate_increment_indep_past (hind _ _ (ht (Nat.le_succ k))) a)
      (hH a k) (hH2 a k)
  apply SimpleIntegral.integral_mul_sums_eq_zero
    (fun k ω => H a k ω * (B a (t (k + 1)) ω - B a (t k) ω))
    (fun k ω => H b k ω * (B b (t (k + 1)) ω - B b (t k) ω))
    (hHD a) (hHD b) _ u v
  intro k l
  exact grid_orthogonal hB hAd hind hcross t ht H hH hH2
    (show (a, k) ≠ (b, l) from fun h => hab (congrArg Prod.fst h))

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

namespace BrownianArrayFiltration

variable {Ω ι : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
  {B : ι → ℝ≥0 → Ω → ℝ} {F : Filtration ℝ≥0 mΩ}

theorem uniform_meanSquare_limits_orthogonal [IsProbabilityMeasure P]
    (hB : ∀ a, IsPreBrownianReal (B a) P)
    (hAd : ∀ a, StronglyAdapted F (B a))
    (hind : ∀ s t, s ≤ t → Indep
      (MeasurableSpace.comap (fun ω a => B a t ω - B a s ω) inferInstance) (F s) P)
    (hcross : ∀ s t, s ≤ t → Pairwise fun a b =>
      IndepFun (fun ω => B a t ω - B a s ω) (fun ω => B b t ω - B b s ω) P)
    (H : ι → ℝ≥0 → Ω → ℝ) (hH : ∀ a, StronglyAdapted F (H a))
    (hH2 : ∀ a t, MemLp (H a t) 2 P) (T : ℝ≥0)
    {I : ι → Ω → ℝ} (hI : ∀ a, MemLp (I a) 2 P)
    (ha : ∀ a, Tendsto (fun n => ∫ ω,
      (BrownianGrid.uniformSum (B a) (H a) T n ω - I a ω) ^ 2 ∂P) atTop (𝓝 0)) :
    Pairwise fun a b => ∫ ω, I a ω * I b ω ∂P = 0 := by
  have hi (a : ι) (s t : ℝ≥0) (hst : s ≤ t) :=
    coordinate_increment_indep_past (hind s t hst) a
  have hS (a : ι) := BrownianFiltrationGrid.uniformSum_memLp
    (hB a) (hAd a) (hi a) (H a) (hH a) (hH2 a) T
  have hlim (a : ι) := (SimpleIntegral.tendsto_toLp_iff_meanSquare (hS a) (hI a)).mpr (ha a)
  intro a b hab
  have hliminner := (hlim a).inner (𝕜 := ℝ) (hlim b)
  have hz (n : ℕ) : inner ℝ
      ((hS a n).toLp (BrownianGrid.uniformSum (B a) (H a) T n))
      ((hS b n).toLp (BrownianGrid.uniformSum (B b) (H b) T n)) = 0 := by
    rw [PredictableL2.inner_toLp]
    exact grid_sums_orthogonal hB hAd hind hcross
      (BrownianGrid.uniformGrid T n) (BrownianGrid.uniformGrid_mono T n)
      (fun a k => H a (BrownianGrid.uniformGrid T n k))
      (fun a k => hH a _) (fun a k => hH2 a _) hab (Finset.range n) (Finset.range n)
  have heq : inner ℝ ((hI a).toLp (I a)) ((hI b).toLp (I b)) = 0 :=
    tendsto_nhds_unique hliminner (by simpa only [hz] using
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 0)))
  exact (PredictableL2.inner_toLp (hI a) (hI b)).symm.trans heq

theorem uniform_meanSquare_differences_orthogonal [IsProbabilityMeasure P]
    (hB : ∀ a, IsPreBrownianReal (B a) P)
    (hAd : ∀ a, StronglyAdapted F (B a))
    (hind : ∀ s t, s ≤ t → Indep
      (MeasurableSpace.comap (fun ω a => B a t ω - B a s ω) inferInstance) (F s) P)
    (hcross : ∀ s t, s ≤ t → Pairwise fun a b =>
      IndepFun (fun ω => B a t ω - B a s ω) (fun ω => B b t ω - B b s ω) P)
    (H K : ι → ℝ≥0 → Ω → ℝ)
    (hH : ∀ a, StronglyAdapted F (H a)) (hK : ∀ a, StronglyAdapted F (K a))
    (hH2 : ∀ a t, MemLp (H a t) 2 P) (hK2 : ∀ a t, MemLp (K a t) 2 P)
    (T : ℝ≥0) {I J : ι → Ω → ℝ}
    (hI : ∀ a, MemLp (I a) 2 P) (hJ : ∀ a, MemLp (J a) 2 P)
    (haI : ∀ a, Tendsto (fun n => ∫ ω,
      (BrownianGrid.uniformSum (B a) (H a) T n ω - I a ω) ^ 2 ∂P) atTop (𝓝 0))
    (haJ : ∀ a, Tendsto (fun n => ∫ ω,
      (BrownianGrid.uniformSum (B a) (K a) T n ω - J a ω) ^ 2 ∂P) atTop (𝓝 0)) :
    Pairwise fun a b => ∫ ω, (I a ω - J a ω) * (I b ω - J b ω) ∂P = 0 := by
  apply uniform_meanSquare_limits_orthogonal hB hAd hind hcross
    (fun a t ω => H a t ω - K a t ω)
    (fun a t => (hH a t).sub (hK a t)) (fun a t => (hH2 a t).sub (hK2 a t)) T
    (fun a => (hI a).sub (hJ a))
  intro a
  have hi (s t : ℝ≥0) (hst : s ≤ t) :=
    coordinate_increment_indep_past (hind s t hst) a
  simpa only [BrownianGrid.uniformSum_sub_coeff, Pi.sub_apply] using
    SimpleIntegral.meanSquare_limit_sub
      (BrownianFiltrationGrid.uniformSum_memLp (hB a) (hAd a) hi (H a) (hH a) (hH2 a) T)
      (BrownianFiltrationGrid.uniformSum_memLp (hB a) (hAd a) hi (K a) (hK a) (hK2 a) T)
      (hI a) (hJ a) (haI a) (haJ a)

section RowComparison

variable [IsProbabilityMeasure P]
    (hB : ∀ a, IsPreBrownianReal (B a) P)
    (hAd : ∀ a, StronglyAdapted F (B a))
    (hind : ∀ s t, s ≤ t → Indep
      (MeasurableSpace.comap (fun ω a => B a t ω - B a s ω) inferInstance) (F s) P)
    (hcross : ∀ s t, s ≤ t → Pairwise fun a b =>
      IndepFun (fun ω => B a t ω - B a s ω) (fun ω => B b t ω - B b s ω) P)
    (H K : ι → ℝ≥0 → Ω → ℝ)
    (hH : ∀ a, StronglyAdapted F (H a)) (hK : ∀ a, StronglyAdapted F (K a))
    (hcH : ∀ a, ∀ᵐ ω ∂P, Continuous (fun t => H a t ω))
    (hcK : ∀ a, ∀ᵐ ω ∂P, Continuous (fun t => K a t ω))
    (C D : ι → ℝ) (hC : ∀ a, 0 ≤ C a) (hD : ∀ a, 0 ≤ D a)
    (hbH : ∀ a, ∀ᵐ ω ∂P, ∀ t, |H a t ω| ≤ C a)
    (hbK : ∀ a, ∀ᵐ ω ∂P, ∀ t, |K a t ω| ≤ D a)
    (T : ℝ≥0) {I J : ι → Ω → ℝ}
    (hI : ∀ a, MemLp (I a) 2 P) (hJ : ∀ a, MemLp (J a) 2 P)
    (haI : ∀ a, Tendsto (fun n => ∫ ω,
      (BrownianGrid.uniformSum (B a) (H a) T n ω - I a ω) ^ 2 ∂P) atTop (𝓝 0))
    (haJ : ∀ a, Tendsto (fun n => ∫ ω,
      (BrownianGrid.uniformSum (B a) (K a) T n ω - J a ω) ^ 2 ∂P) atTop (𝓝 0))

include hB hAd hind hcross hH hK hcH hcK hC hD hbH hbK hI hJ haI haJ in

theorem finite_row_difference_isometry (s : Finset ι) :
    (∫ ω, ((∑ a ∈ s, I a ω) - ∑ a ∈ s, J a ω) ^ 2 ∂P) =
      ∑ a ∈ s, ∫ t in (0 : ℝ)..(T : ℝ),
        ∫ ω, (H a t.toNNReal ω - K a t.toNNReal ω) ^ 2 ∂P := by
  have hH2 (a : ι) (t : ℝ≥0) : MemLp (H a t) 2 P := by
    apply MemLp.of_bound ((hH a t).mono (F.le t)).aestronglyMeasurable (C a)
    filter_upwards [hbH a] with ω hω
    simpa only [Real.norm_eq_abs] using hω t
  have hK2 (a : ι) (t : ℝ≥0) : MemLp (K a t) 2 P := by
    apply MemLp.of_bound ((hK a t).mono (F.le t)).aestronglyMeasurable (D a)
    filter_upwards [hbK a] with ω hω
    simpa only [Real.norm_eq_abs] using hω t
  have horth := uniform_meanSquare_differences_orthogonal hB hAd hind hcross H K hH hK
    hH2 hK2 T hI hJ haI haJ
  simp_rw [← Finset.sum_sub_distrib]
  rw [SimpleIntegral.integral_sq_sum_of_orthogonal s
    (fun a ω => I a ω - J a ω)
    (fun a _ b _ => ((hI a).sub (hJ a)).integrable_mul ((hI b).sub (hJ b)))
    (fun a _ b _ hab => horth hab)]
  apply Finset.sum_congr rfl
  intro a ha
  exact BrownianFiltrationGrid.uniform_meanSquare_difference_isometry
    (hB a) (hAd a) (fun s t hst => coordinate_increment_indep_past (hind s t hst) a)
    (H a) (K a) (hH a) (hK a) (hcH a) (hcK a) (hC a) (hD a)
    (hbH a) (hbK a) T (hI a) (hJ a) (haI a) (haJ a)

include hB hAd hind hcross hH hK hcH hcK hC hD hbH hbK hI hJ haI haJ in

theorem infinite_row_difference_isometry
    {Y Z : Ω → ℝ} (hY : MemLp Y 2 P) (hZ : MemLp Z 2 P)
    (hsY : Tendsto (fun s : Finset ι => ∫ ω,
      ((∑ a ∈ s, I a ω) - Y ω) ^ 2 ∂P) atTop (𝓝 0))
    (hsZ : Tendsto (fun s : Finset ι => ∫ ω,
      ((∑ a ∈ s, J a ω) - Z ω) ^ 2 ∂P) atTop (𝓝 0))
    (henergy : Summable fun a => ∫ t in (0 : ℝ)..(T : ℝ),
      ∫ ω, (H a t.toNNReal ω - K a t.toNNReal ω) ^ 2 ∂P) :
    (∫ ω, (Y ω - Z ω) ^ 2 ∂P) =
      ∑' a, ∫ t in (0 : ℝ)..(T : ℝ),
        ∫ ω, (H a t.toNNReal ω - K a t.toNNReal ω) ^ 2 ∂P := by
  have hIs (s : Finset ι) : MemLp (fun ω => ∑ a ∈ s, I a ω) 2 P :=
    memLp_finsetSum s (fun a _ => hI a)
  have hJs (s : Finset ι) : MemLp (fun ω => ∑ a ∈ s, J a ω) 2 P :=
    memLp_finsetSum s (fun a _ => hJ a)
  have hd := SimpleIntegral.meanSquare_limit_sub hIs hJs hY hZ hsY hsZ
  have hlp := (SimpleIntegral.tendsto_toLp_iff_meanSquare
    (fun s => (hIs s).sub (hJs s)) (hY.sub hZ)).mpr hd
  have hnorm : Tendsto (fun s : Finset ι => ∫ ω,
      ((∑ a ∈ s, I a ω) - ∑ a ∈ s, J a ω) ^ 2 ∂P) atTop
      (𝓝 (∫ ω, (Y ω - Z ω) ^ 2 ∂P)) := by
    simpa only [PredictableL2.norm_toLp_sq, Pi.sub_apply] using hlp.norm.pow 2
  have heq (s : Finset ι) := finite_row_difference_isometry hB hAd hind hcross
    H K hH hK hcH hcK C D hC hD hbH hbK T hI hJ haI haJ s
  apply tendsto_nhds_unique hnorm
  simpa only [HasSum, SummationFilter.unconditional, heq] using henergy.hasSum

end RowComparison
end BrownianArrayFiltration
end Problem367

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Martingales_PredictableMeshApproximation
attribute [-instance] _root_.OAI.Problem367.WienerSampler.pathMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Filter Set
open scoped NNReal Topology

namespace Problem367.PredictableMesh

theorem left_eq_of_mem_Ioc {n k : ℕ} {t : ℝ≥0}
    (ht : t ∈ Ioc (point n k) (point n (k + 1))) :
    left n t = point n k := by
  have hN : (0 : ℝ≥0) < (n + 1 : ℕ) := by positivity
  have hc : ⌈(n + 1 : ℕ) * t⌉₊ = k + 1 := by
    apply (Nat.ceil_eq_iff (Nat.succ_ne_zero k)).2
    constructor
    · have := (div_lt_iff₀ hN).1 ht.1
      simpa only [mul_comm, Nat.succ_sub_one] using this
    · have := (le_div_iff₀ hN).1 ht.2
      simpa only [mul_comm, Nat.succ_sub_one] using this
  change point n (⌈(n + 1 : ℕ) * t⌉₊ - 1) = point n k
  rw [hc, Nat.add_sub_cancel]

theorem mem_mesh_Ioc {n : ℕ} {t : ℝ≥0} (ht : 0 < t) :
    t ∈ Ioc (left n t)
      (point n (⌈(n + 1 : ℕ) * t⌉₊ - 1 + 1)) := by
  have hN : (0 : ℝ≥0) < (n + 1 : ℕ) := by positivity
  have hc : 1 ≤ ⌈(n + 1 : ℕ) * t⌉₊ :=
    Nat.one_le_ceil_iff.mpr (mul_pos hN ht)
  have hh := (Nat.ceil_eq_iff (show ⌈(n + 1 : ℕ) * t⌉₊ ≠ 0 by omega)).mp rfl
  constructor
  · apply (div_lt_iff₀ hN).2
    simpa only [mul_comm] using hh.1
  · dsimp [point]
    rw [Nat.sub_add_cancel hc]
    apply (le_div_iff₀ hN).2
    simpa only [mul_comm] using hh.2

theorem left_le (n : ℕ) (t : ℝ≥0) : left n t ≤ t := by
  by_cases ht : t = 0
  · simp [ht]
  · exact (mem_mesh_Ioc (n := n) (pos_iff_ne_zero.mpr ht)).1.le

theorem le_left_add_width (n : ℕ) (t : ℝ≥0) :
    t ≤ left n t + 1 / (n + 1 : ℕ) := by
  by_cases ht : t = 0
  · simp [ht]
  · have h := (mem_mesh_Ioc (n := n) (pos_iff_ne_zero.mpr ht)).2
    simpa only [point, left, Nat.cast_add, Nat.cast_one, add_div] using h

theorem tendsto_left (t : ℝ≥0) : Tendsto (fun n => left n t) atTop (𝓝 t) := by
  apply NNReal.tendsto_coe.mp
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  apply squeeze_zero (fun n => norm_nonneg _)
    (fun n => show ‖(left n t : ℝ) - (t : ℝ)‖ ≤ 1 / ((n : ℝ) + 1) from ?_)
    tendsto_one_div_add_atTop_nhds_zero_nat
  have hl : (left n t : ℝ) ≤ (t : ℝ) := left_le n t
  have hu := le_left_add_width n t
  have hu' : (t : ℝ) ≤ (left n t : ℝ) + 1 / ((n : ℝ) + 1) := by
    exact_mod_cast hu
  rw [Real.norm_eq_abs, abs_of_nonpos (sub_nonpos.mpr hl)]
  linarith

theorem sample_isStronglyPredictable {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {F : Filtration ℝ≥0 mΩ} {u : ℝ≥0 → Ω → ℝ}
    (hu : StronglyAdapted F u) (n : ℕ) : IsStronglyPredictable F (sample u n) := by
  apply Measurable.stronglyMeasurable
  intro s hs
  have heq : (Function.uncurry (sample u n)) ⁻¹' s =
      ({0} ×ˢ (u 0 ⁻¹' s)) ∪
        ⋃ k : ℕ, (Ioc (point n k) (point n (k + 1))) ×ˢ (u (point n k) ⁻¹' s) := by
    ext ⟨t, ω⟩
    simp only [mem_preimage, Function.uncurry_apply_pair, mem_union, mem_prod,
      mem_singleton_iff, mem_iUnion]
    constructor
    · intro h
      by_cases ht : t = 0
      · exact Or.inl ⟨ht, by simpa [ht, sample] using h⟩
      · exact Or.inr ⟨⌈(n + 1 : ℕ) * t⌉₊ - 1,
          mem_mesh_Ioc (pos_iff_ne_zero.mpr ht), h⟩
    · rintro (⟨ht, h⟩ | ⟨k, ht, h⟩)
      · simpa [ht, sample] using h
      · simpa only [sample, left_eq_of_mem_Ioc ht] using h
  rw [heq]
  apply MeasurableSet.union
  · exact measurableSet_predictable_singleton_bot_prod ((hu 0).measurable hs)
  · exact MeasurableSet.iUnion fun k =>
      measurableSet_predictable_Ioc_prod _ _ ((hu (point n k)).measurable hs)

end Problem367.PredictableMesh

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

theorem finite_maximal_sq [IsFiniteMeasure μ]
    {F : Filtration ℕ mΩ} {M : ℕ → Ω → ℝ}
    (hM : Martingale M F μ) (h2 : ∀ t, MemLp (M t) 2 μ)
    (ε : ℝ≥0) (n : ℕ) :
    (ε : ℝ≥0∞) ^ 2 * μ {ω | ∃ k ≤ n, (ε : ℝ) ≤ |M k ω|} ≤
      ENNReal.ofReal (∫ ω, M n ω ^ 2 ∂μ) := by
  have hs := submartingale_sq hM h2
  have hmax := maximal_ineq hs (fun t ω => sq_nonneg (M t ω)) (ε := ε ^ 2) n
  have hevent : {ω | ((ε ^ 2 : ℝ≥0) : ℝ) ≤
      (Finset.range (n + 1)).sup' Finset.nonempty_range_add_one (fun k => M k ω ^ 2)} =
      {ω | ∃ k ≤ n, (ε : ℝ) ≤ |M k ω|} := by
    ext ω
    simp only [Set.mem_ofPred_eq, Finset.le_sup'_iff, Finset.mem_range, Nat.lt_succ_iff,
      NNReal.coe_pow]
    constructor
    · rintro ⟨k, hk, hval⟩
      refine ⟨k, hk, ?_⟩
      nlinarith [abs_nonneg (M k ω), sq_abs (M k ω), ε.coe_nonneg]
    · rintro ⟨k, hk, hval⟩
      refine ⟨k, hk, ?_⟩
      nlinarith [abs_nonneg (M k ω), sq_abs (M k ω), ε.coe_nonneg]
  rw [hevent] at hmax
  calc
    _ ≤ ENNReal.ofReal (∫ ω in {ω | ∃ k ≤ n, (ε : ℝ) ≤ |M k ω|}, M n ω ^ 2 ∂μ) := by
      simpa only [ENNReal.coe_pow] using hmax
    _ ≤ _ := ENNReal.ofReal_le_ofReal (setIntegral_le_integral (h2 n).integrable_sq
      (Filter.Eventually.of_forall (fun ω => sq_nonneg (M n ω))))

theorem integral_sq_le [IsFiniteMeasure μ]
    (hM : Martingale M F μ) (h2 : ∀ t, MemLp (M t) 2 μ)
    {s t : ι} (hst : s ≤ t) :
    (∫ ω, M s ω ^ 2 ∂μ) ≤ ∫ ω, M t ω ^ 2 ∂μ := by
  have hs := submartingale_sq hM h2
  calc
    _ ≤ ∫ ω, μ[(fun ω => M t ω ^ 2) | F s] ω ∂μ :=
      integral_mono_ae (h2 s).integrable_sq integrable_condExp (hs.2.1 s t hst)
    _ = _ := integral_condExp (F.le s)

theorem sampled_maximal_sq [IsFiniteMeasure μ]
    (hM : Martingale M F μ) (h2 : ∀ t, MemLp (M t) 2 μ)
    (q : ℕ → ι) (hq : Monotone q) (ε : ℝ≥0) (n : ℕ)
    {T : ι} (hT : q n ≤ T) :
    (ε : ℝ≥0∞) ^ 2 * μ {ω | ∃ k ≤ n, (ε : ℝ) ≤ |M (q k) ω|} ≤
      ENNReal.ofReal (∫ ω, M T ω ^ 2 ∂μ) := by
  let G : Filtration ℕ mΩ := ⟨fun k => F (q k),
    fun _ _ h => F.mono (hq h), fun k => F.le (q k)⟩
  have hMq : Martingale (fun k => M (q k)) G μ :=
    ⟨fun k => hM.stronglyMeasurable (q k), fun i j hij => hM.condExp_ae_eq (hq hij)⟩
  exact (finite_maximal_sq hMq (fun k => h2 (q k)) ε n).trans
    (ENNReal.ofReal_le_ofReal (integral_sq_le hM h2 hT))

end Problem367.MartingaleSquareMaximal

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Martingales_ContinuousMaximal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Filter Set
open scoped NNReal ENNReal Topology

namespace Problem367.MartingaleSquareMaximal

private lemma dyadicPoint_mono (n : ℕ) : Monotone (dyadicPoint n) := by
  intro i j hij
  dsimp [dyadicPoint]
  gcongr

private lemma dyadicPoint_double (n k : ℕ) :
    dyadicPoint (n + 1) (2 * k) = dyadicPoint n k := by
  simp only [dyadicPoint, pow_succ, Nat.cast_mul, Nat.cast_ofNat]
  field_simp

private lemma dyadicPoint_eq_mesh (n k : ℕ) :
    dyadicPoint n k = PredictableMesh.point (2 ^ n - 1) k := by
  have hn : 1 ≤ 2 ^ n := Nat.one_le_pow n 2 (by norm_num)
  simp only [dyadicPoint, PredictableMesh.point, Nat.sub_add_cancel hn]

variable {Ω : Type*} [mΩ : MeasurableSpace Ω]
  {μ : Measure Ω} [IsFiniteMeasure μ]
  {F : Filtration ℝ≥0 mΩ} {M : ℝ≥0 → Ω → ℝ}

theorem continuous_maximal_sq
    (hM : Martingale M F μ) (h2 : ∀ t, MemLp (M t) 2 μ)
    (hc : ∀ᵐ ω ∂μ, Continuous (fun t => M t ω))
    (ε T : ℝ≥0) :
    (ε : ℝ≥0∞) ^ 2 * μ {ω | ∃ t ≤ T, (ε : ℝ) < |M t ω|} ≤
      ENNReal.ofReal (∫ ω, M T ω ^ 2 ∂μ) := by
  let A : ℕ → Set Ω := fun n =>
    {ω | ∃ k : ℕ, dyadicPoint n k ≤ T ∧ (ε : ℝ) < |M (dyadicPoint n k) ω|}
  have hAmono : Monotone A := by
    apply monotone_nat_of_le_succ
    intro n ω hω
    obtain ⟨k, hk, hv⟩ := hω
    exact ⟨2 * k, by simpa only [dyadicPoint_double] using hk,
      by simpa only [dyadicPoint_double] using hv⟩
  have hAn (n : ℕ) : (ε : ℝ≥0∞) ^ 2 * μ (A n) ≤
      ENNReal.ofReal (∫ ω, M T ω ^ 2 ∂μ) := by
    let N : ℕ := ⌊(2 ^ n : ℕ) * T⌋₊
    have hp : (0 : ℝ≥0) < (2 ^ n : ℕ) := by positivity
    have hlast : dyadicPoint n N ≤ T := by
      apply (div_le_iff₀ hp).2
      simpa only [N, mul_comm] using Nat.floor_le (show (0 : ℝ≥0) ≤ ((2 ^ n : ℕ) : ℝ≥0) * T from by positivity)
    have hsub : A n ⊆ {ω | ∃ k ≤ N, (ε : ℝ) ≤ |M (dyadicPoint n k) ω|} := by
      intro ω hω
      obtain ⟨k, hk, hv⟩ := hω
      refine ⟨k, ?_, hv.le⟩
      apply Nat.le_floor
      simpa only [mul_comm] using (div_le_iff₀ hp).mp hk
    exact (mul_le_mul_right (measure_mono hsub) ((ε : ℝ≥0∞) ^ 2)).trans
      (sampled_maximal_sq hM h2 (dyadicPoint n) (dyadicPoint_mono n) ε N hlast)
  have hUnion : (ε : ℝ≥0∞) ^ 2 * μ (⋃ n, A n) ≤
      ENNReal.ofReal (∫ ω, M T ω ^ 2 ∂μ) := by
    rw [hAmono.measure_iUnion, ENNReal.mul_iSup]
    exact iSup_le hAn
  have hsub : {ω | ∃ t ≤ T, (ε : ℝ) < |M t ω|} ≤ᵐ[μ] ⋃ n, A n := by
    filter_upwards [hc] with ω hcω
    rintro ⟨t, ht, hv⟩
    have hp : Tendsto (fun n : ℕ => 2 ^ n - 1) atTop atTop :=
      (tendsto_sub_atTop_nat 1).comp
        (tendsto_pow_atTop_atTop_of_one_lt (by norm_num : (1 : ℕ) < 2))
    have hlim : Tendsto (fun n : ℕ => |M (PredictableMesh.left (2 ^ n - 1) t) ω|)
        atTop (𝓝 |M t ω|) :=
      ((hcω.tendsto t).comp ((PredictableMesh.tendsto_left t).comp hp)).abs
    obtain ⟨n, hn⟩ := ((tendsto_order.1 hlim).1 (ε : ℝ) hv).exists
    apply Set.mem_iUnion.mpr
    refine ⟨n, ?_⟩
    let k := ⌈((2 ^ n - 1 + 1 : ℕ) : ℝ≥0) * t⌉₊ - 1
    have heq : dyadicPoint n k = PredictableMesh.left (2 ^ n - 1) t :=
      dyadicPoint_eq_mesh n k
    refine ⟨k, ?_, ?_⟩
    · rw [heq]
      exact (PredictableMesh.left_le _ t).trans ht
    · rw [heq]
      exact hn
  exact (mul_le_mul_right (measure_mono_ae hsub) ((ε : ℝ≥0∞) ^ 2)).trans hUnion

end Problem367.MartingaleSquareMaximal

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Martingales_ContinuousLimit
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Filter Set
open scoped NNReal ENNReal Topology

namespace Problem367.MartingaleSquareMaximal

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {μ : Measure Ω}
  {M : ℕ → ℝ≥0 → Ω → ℝ}

theorem ae_exists_continuous_limit_of_summable_crossings
    (hc : ∀ n, ∀ᵐ ω ∂μ, Continuous (fun t => M n t ω)) (T : ℝ≥0)
    (hsum : (∑' n : ℕ, μ {ω | ∃ t ≤ T,
      ((1 / 2 : ℝ) ^ n) < |M (n + 1) t ω - M n t ω|}) ≠ ∞) :
    ∀ᵐ ω ∂μ, ∃ f : C(Set.Iic T, ℝ),
      ∀ t : Set.Iic T, Tendsto (fun n => M n t ω) atTop (𝓝 (f t)) := by
  have hbc := ae_eventually_notMem hsum
  filter_upwards [ae_all_iff.mpr hc, hbc] with ω hcω hω
  have hcompact : IsCompact (Set.Iic T) := by
    convert (isCompact_Icc (a := (0 : ℝ≥0)) (b := T)) using 1
    all_goals try with_reducible_and_instances rfl
    ext t
    simp only [Set.mem_Iic, Set.mem_Icc]
    exact ⟨fun ht => ⟨zero_le, ht⟩, And.right⟩
  let : CompactSpace (Set.Iic T) := isCompact_iff_compactSpace.mp hcompact
  let f : ℕ → C(Set.Iic T, ℝ) := fun n =>
    ⟨fun t => M n t ω, (hcω n).comp continuous_subtype_val⟩
  have hgeom : Summable (fun n : ℕ => (1 / 2 : ℝ) ^ n) :=
    summable_geometric_of_norm_lt_one (by norm_num)
  have hdist : Summable (fun n : ℕ => dist (f n) (f (n + 1))) := by
    apply hgeom.of_norm_bounded_eventually_nat
    filter_upwards [hω] with n hn
    rw [Real.norm_eq_abs, abs_of_nonneg dist_nonneg]
    apply (ContinuousMap.dist_le (by positivity : (0 : ℝ) ≤ (1 / 2 : ℝ) ^ n)).2
    intro t
    have hv : |M (n + 1) t ω - M n t ω| ≤ (1 / 2 : ℝ) ^ n := by
      by_contra! h
      exact hn ⟨t, t.property, h⟩
    simpa only [f, ContinuousMap.coe_mk, Real.dist_eq, abs_sub_comm] using hv
  obtain ⟨g, hg⟩ := cauchySeq_tendsto_of_complete (cauchySeq_of_summable_dist hdist)
  refine ⟨g, fun t => ?_⟩
  exact ((continuous_eval_const t).tendsto g).comp hg

theorem ae_exists_continuous_limit_of_summable_energy [IsFiniteMeasure μ]
    {F : Filtration ℝ≥0 mΩ}
    (hM : ∀ n, Martingale (M n) F μ)
    (h2 : ∀ n t, MemLp (M n t) 2 μ)
    (hc : ∀ n, ∀ᵐ ω ∂μ, Continuous (fun t => M n t ω)) (T : ℝ≥0)
    (hsum : (∑' n : ℕ,
      ENNReal.ofReal (∫ ω, (M (n + 1) T ω - M n T ω) ^ 2 ∂μ) /
        (((1 / 2 : ℝ≥0) ^ n : ℝ≥0) : ℝ≥0∞) ^ 2) ≠ ∞) :
    ∀ᵐ ω ∂μ, ∃ f : C(Set.Iic T, ℝ),
      ∀ t : Set.Iic T, Tendsto (fun n => M n t ω) atTop (𝓝 (f t)) := by
  apply ae_exists_continuous_limit_of_summable_crossings hc T
  apply ne_top_of_le_ne_top hsum
  apply ENNReal.tsum_le_tsum
  intro n
  have hcont : ∀ᵐ ω ∂μ, Continuous
      (fun t => (M (n + 1) - M n) t ω) := by
    filter_upwards [hc (n + 1), hc n] with ω ha hb
    exact ha.sub hb
  have hb := continuous_maximal_sq ((hM (n + 1)).sub (hM n))
    (fun t => (h2 (n + 1) t).sub (h2 n t)) hcont ((1 / 2 : ℝ≥0) ^ n) T
  apply (ENNReal.le_div_iff_mul_le (Or.inl (by positivity))
    (Or.inl (by simp))).2
  simpa only [NNReal.coe_pow, NNReal.coe_div, NNReal.coe_one, NNReal.coe_ofNat,
    Pi.sub_apply, mul_comm] using hb

end Problem367.MartingaleSquareMaximal

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Martingales_ContinuousSubsequence
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Filter Set
open scoped NNReal ENNReal Topology

namespace Problem367.MartingaleSquareMaximal

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {μ : Measure Ω} [IsFiniteMeasure μ]
  {F : Filtration ℝ≥0 mΩ} {M : ℕ → ℝ≥0 → Ω → ℝ}

theorem exists_continuous_subsequence_of_terminal_L2_cauchy
    (hM : ∀ n, Martingale (M n) F μ)
    (h2 : ∀ n t, MemLp (M n t) 2 μ)
    (hc : ∀ n, ∀ᵐ ω ∂μ, Continuous (fun t => M n t ω)) (T : ℝ≥0)
    (hC : CauchySeq (fun n => (h2 n T).toLp (M n T))) :
    ∃ v : ℕ → ℕ, StrictMono v ∧
      ∀ᵐ ω ∂μ, ∃ f : C(Set.Iic T, ℝ),
        ∀ t : Set.Iic T, Tendsto (fun n => M (v n) t ω) atTop (𝓝 (f t)) := by
  let u : ℕ → Lp ℝ 2 μ := fun n => (h2 n T).toLp (M n T)
  obtain ⟨v, hv, hb⟩ := Metric.exists_subseq_bounded_of_cauchySeq u hC
    (fun n => (1 / 4 : ℝ) ^ n) (fun n => by positivity)
  refine ⟨v, hv, ae_exists_continuous_limit_of_summable_energy
    (fun n => hM (v n)) (fun n => h2 (v n)) (fun n => hc (v n)) T ?_⟩
  have hfinite : (∑' n : ℕ, (1 / 4 : ℝ≥0∞) ^ n) ≠ ∞ :=
    (tsum_geometric_lt_top.mpr (by norm_num)).ne
  apply ne_top_of_le_ne_top hfinite
  apply ENNReal.tsum_le_tsum
  intro n
  have hnorm : ‖u (v (n + 1)) - u (v n)‖ < (1 / 4 : ℝ) ^ n := by
    simpa only [dist_eq_norm] using hb n (v (n + 1)) (hv.monotone (Nat.le_succ n))
  have heq : ‖u (v (n + 1)) - u (v n)‖ ^ 2 =
      ∫ ω, (M (v (n + 1)) T ω - M (v n) T ω) ^ 2 ∂μ := by
    rw [← real_inner_self_eq_norm_sq, L2.inner_def]
    simp only [real_inner_self_eq_norm_sq, Real.norm_eq_abs, sq_abs]
    apply integral_congr_ae
    filter_upwards [Lp.coeFn_sub (u (v (n + 1))) (u (v n)),
      (h2 (v (n + 1)) T).coeFn_toLp, (h2 (v n) T).coeFn_toLp] with ω hsub ha hb
    simp only [Pi.sub_apply] at hsub
    rw [hsub, ha, hb]
  have henergy : (∫ ω, (M (v (n + 1)) T ω - M (v n) T ω) ^ 2 ∂μ) ≤
      ((1 / 4 : ℝ) ^ n) ^ 2 := by
    rw [← heq]
    nlinarith [norm_nonneg (u (v (n + 1)) - u (v n))]
  have henergy' : ENNReal.ofReal
      (∫ ω, (M (v (n + 1)) T ω - M (v n) T ω) ^ 2 ∂μ) ≤
      ((1 / 4 : ℝ≥0∞) ^ n) ^ 2 := by
    have hh : ENNReal.ofReal (((1 / 4 : ℝ) ^ n) ^ 2) =
        ((1 / 4 : ℝ≥0∞) ^ n) ^ 2 := by
      rw [ENNReal.ofReal_pow (by positivity), ENNReal.ofReal_pow (by norm_num)]
      congr 2
      rw [ENNReal.ofReal_div_of_pos (by norm_num : (0 : ℝ) < 4)]
      norm_num
    exact (ENNReal.ofReal_le_ofReal henergy).trans_eq hh
  calc
    _ ≤ ((1 / 4 : ℝ≥0∞) ^ n) ^ 2 /
        ((((1 / 2 : ℝ≥0) ^ n : ℝ≥0) : ℝ≥0∞) ^ 2) :=
      ENNReal.div_le_div_right henergy' _
    _ = (1 / 4 : ℝ≥0∞) ^ n := by
      have hh : ((((1 / 2 : ℝ≥0) ^ n : ℝ≥0) : ℝ≥0∞) ^ 2) =
          ((1 / 2 : ℝ≥0∞) ^ n) ^ 2 := by
        norm_num [ENNReal.coe_pow, ENNReal.coe_div (by norm_num : (2 : ℝ≥0) ≠ 0)]
      rw [hh]
      simp only [div_eq_mul_inv, ENNReal.inv_pow, ← mul_pow, ← pow_mul]
      rw [Nat.mul_comm n 2, pow_mul]
      congr 1
      apply (ENNReal.toReal_eq_toReal_iff' (by simp [ENNReal.mul_ne_top]) (by simp)).mp
      norm_num

end Problem367.MartingaleSquareMaximal

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Martingales_ContinuousSelection
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Filter Set
open scoped NNReal Topology

namespace Problem367.PredictableMesh

theorem repair_isStronglyPredictable {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {F : Filtration ℝ≥0 mΩ} {u : ℝ≥0 → Ω → ℝ}
    (hu : StronglyAdapted F u) : IsStronglyPredictable F (repair u) := by
  let : MeasurableSpace (ℝ≥0 × Ω) := F.predictable
  exact StronglyMeasurable.limUnder (fun n => sample_isStronglyPredictable hu n)

theorem repair_eq_of_continuousOn {Ω : Type*} {u : ℝ≥0 → Ω → ℝ}
    {T : ℝ≥0} {ω : Ω} (hc : ContinuousOn (fun t => u t ω) (Iic T))
    {t : ℝ≥0} (ht : t ≤ T) : repair u t ω = u t ω := by
  apply Filter.Tendsto.limUnder_eq
  apply (hc t ht).tendsto.comp
  apply tendsto_nhdsWithin_iff.mpr
  exact ⟨tendsto_left t, Filter.Eventually.of_forall
    (fun n => (left_le n t).trans ht)⟩

end Problem367.PredictableMesh

namespace Problem367.MartingaleSquareMaximal

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {μ : Measure Ω} [IsFiniteMeasure μ]
  {F : Filtration ℝ≥0 mΩ} {M : ℕ → ℝ≥0 → Ω → ℝ}

theorem exists_predictable_continuous_subsequence_of_terminal_L2_cauchy
    (hM : ∀ n, Martingale (M n) F μ)
    (h2 : ∀ n t, MemLp (M n t) 2 μ)
    (hc : ∀ n, ∀ᵐ ω ∂μ, Continuous (fun t => M n t ω)) (T : ℝ≥0)
    (hC : CauchySeq (fun n => (h2 n T).toLp (M n T))) :
    ∃ (v : ℕ → ℕ) (L : ℝ≥0 → Ω → ℝ), StrictMono v ∧
      IsStronglyPredictable F L ∧
      (∀ᵐ ω ∂μ, ContinuousOn (fun t => L t ω) (Iic T)) ∧
      (∀ᵐ ω ∂μ, ∀ t ≤ T,
        Tendsto (fun n => M (v n) t ω) atTop (𝓝 (L t ω))) := by
  obtain ⟨v, hv, hlim⟩ :=
    exists_continuous_subsequence_of_terminal_L2_cauchy hM h2 hc T hC
  let R : ℝ≥0 → Ω → ℝ := fun t ω => limUnder atTop (fun n => M (v n) t ω)
  have hR : StronglyAdapted F R := fun t => by
    let : MeasurableSpace Ω := F t
    exact StronglyMeasurable.limUnder (fun n => (hM (v n)).stronglyMeasurable t)
  have hpath : ∀ᵐ ω ∂μ, ContinuousOn (fun t => R t ω) (Iic T) ∧
      ∀ t ≤ T, Tendsto (fun n => M (v n) t ω) atTop (𝓝 (R t ω)) := by
    filter_upwards [hlim] with ω hω
    obtain ⟨f, hf⟩ := hω
    have heq (t : Iic T) : R t ω = f t := (hf t).limUnder_eq
    constructor
    · rw [continuousOn_iff_continuous_domRestrict]
      exact f.continuous.congr (fun t => (heq t).symm)
    · intro t ht
      simpa only [heq ⟨t, ht⟩] using hf ⟨t, ht⟩
  refine ⟨v, PredictableMesh.repair R, hv,
    PredictableMesh.repair_isStronglyPredictable hR, ?_, ?_⟩
  · filter_upwards [hpath] with ω hω
    exact hω.1.congr (fun t ht => PredictableMesh.repair_eq_of_continuousOn hω.1 ht)
  · filter_upwards [hpath] with ω hω
    intro t ht
    rw [PredictableMesh.repair_eq_of_continuousOn hω.1 ht]
    exact hω.2 t ht

end Problem367.MartingaleSquareMaximal

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Martingales_ContinuousL2Limit
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Filter Set
open scoped NNReal Topology

namespace Problem367.MartingaleSquareMaximal

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {μ : Measure Ω} [IsFiniteMeasure μ]

omit [IsFiniteMeasure μ] in
theorem dist_toLp_sq {f g : Ω → ℝ} (hf : MemLp f 2 μ) (hg : MemLp g 2 μ) :
    dist (hf.toLp f) (hg.toLp g) ^ 2 = ∫ ω, (f ω - g ω) ^ 2 ∂μ := by
  rw [dist_eq_norm, ← real_inner_self_eq_norm_sq, L2.inner_def]
  simp only [real_inner_self_eq_norm_sq, Real.norm_eq_abs, sq_abs]
  apply integral_congr_ae
  filter_upwards [Lp.coeFn_sub (hf.toLp f) (hg.toLp g), hf.coeFn_toLp,
    hg.coeFn_toLp] with ω hsub ha hb
  simp only [Pi.sub_apply] at hsub
  rw [hsub, ha, hb]

theorem dist_toLp_le_of_le {F : Filtration ℝ≥0 mΩ} {M N : ℝ≥0 → Ω → ℝ}
    (hM : Martingale M F μ) (hN : Martingale N F μ)
    (hM2 : ∀ t, MemLp (M t) 2 μ) (hN2 : ∀ t, MemLp (N t) 2 μ)
    {s t : ℝ≥0} (hst : s ≤ t) :
    dist ((hM2 s).toLp (M s)) ((hN2 s).toLp (N s)) ≤
      dist ((hM2 t).toLp (M t)) ((hN2 t).toLp (N t)) := by
  have hsq := integral_sq_le (hM.sub hN) (fun r => (hM2 r).sub (hN2 r)) hst
  simp only [Pi.sub_apply] at hsq
  rw [← dist_toLp_sq (hM2 s) (hN2 s), ← dist_toLp_sq (hM2 t) (hN2 t)] at hsq
  exact (sq_le_sq₀ dist_nonneg dist_nonneg).mp hsq

theorem L2_cauchy_of_le {F : Filtration ℝ≥0 mΩ} {M : ℕ → ℝ≥0 → Ω → ℝ}
    (hM : ∀ n, Martingale (M n) F μ) (h2 : ∀ n t, MemLp (M n t) 2 μ)
    {s T : ℝ≥0} (hs : s ≤ T)
    (hC : CauchySeq (fun n => (h2 n T).toLp (M n T))) :
    CauchySeq (fun n => (h2 n s).toLp (M n s)) := by
  apply Metric.cauchySeq_iff.mpr
  intro ε hε
  obtain ⟨N, hN⟩ := Metric.cauchySeq_iff.mp hC ε hε
  refine ⟨N, fun n hn m hm => ?_⟩
  exact (dist_toLp_le_of_le (hM n) (hM m) (h2 n) (h2 m) hs).trans_lt
    (hN n hn m hm)

theorem memLp_tendsto_of_cauchy_of_ae_subsequence
    {X : ℕ → Ω → ℝ} (h2 : ∀ n, MemLp (X n) 2 μ) {L : Ω → ℝ}
    (hC : CauchySeq (fun n => (h2 n).toLp (X n)))
    {v : ℕ → ℕ} (hv : Tendsto v atTop atTop)
    (hL : ∀ᵐ ω ∂μ, Tendsto (fun n => X (v n) ω) atTop (𝓝 (L ω))) :
    ∃ hL2 : MemLp L 2 μ,
      Tendsto (fun n => (h2 n).toLp (X n)) atTop (𝓝 (hL2.toLp L)) := by
  obtain ⟨I, hI⟩ := cauchySeq_tendsto_of_complete hC
  have hraw : TendstoInMeasure μ X atTop I :=
    (tendstoInMeasure_of_tendsto_Lp hI).congr_left (fun n => (h2 n).coeFn_toLp)
  have heq : L =ᵐ[μ] I := tendstoInMeasure_ae_unique
    (tendstoInMeasure_of_tendsto_ae (fun n => (h2 (v n)).aestronglyMeasurable) hL)
    (hraw.comp hv)
  have hL2 : MemLp L 2 μ := (Lp.memLp I).ae_eq heq.symm
  refine ⟨hL2, ?_⟩
  have hclass : hL2.toLp L = I :=
    (hL2.toLp_congr (Lp.memLp I) heq).trans (Lp.toLp_coeFn I (Lp.memLp I))
  rw [hclass]
  exact hI

theorem exists_predictable_continuous_L2_limit
    {F : Filtration ℝ≥0 mΩ} {M : ℕ → ℝ≥0 → Ω → ℝ}
    (hM : ∀ n, Martingale (M n) F μ)
    (h2 : ∀ n t, MemLp (M n t) 2 μ)
    (hc : ∀ n, ∀ᵐ ω ∂μ, Continuous (fun t => M n t ω)) (T : ℝ≥0)
    (hC : CauchySeq (fun n => (h2 n T).toLp (M n T))) :
    ∃ L : ℝ≥0 → Ω → ℝ, IsStronglyPredictable F L ∧
      (∀ᵐ ω ∂μ, ContinuousOn (fun t => L t ω) (Iic T)) ∧
      ∀ t ≤ T, ∃ hL2 : MemLp (L t) 2 μ,
        Tendsto (fun n => (h2 n t).toLp (M n t)) atTop (𝓝 (hL2.toLp (L t))) := by
  obtain ⟨v, L, hv, hpred, hcont, hlim⟩ :=
    exists_predictable_continuous_subsequence_of_terminal_L2_cauchy hM h2 hc T hC
  refine ⟨L, hpred, hcont, fun t ht => ?_⟩
  apply memLp_tendsto_of_cauchy_of_ae_subsequence (fun n => h2 n t)
    (L2_cauchy_of_le hM h2 ht hC) hv.tendsto_atTop
  filter_upwards [hlim] with ω hω
  exact hω t ht

end Problem367.MartingaleSquareMaximal

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Martingales_L2Closure
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Filter Set
open scoped NNReal Topology

namespace Problem367.MartingaleSquareMaximal

variable {Ω ι : Type*} [mΩ : MeasurableSpace Ω] [Preorder ι]
  {μ : Measure Ω} [IsFiniteMeasure μ] {F : Filtration ι mΩ}

theorem condExp_ae_eq_of_L2_limits {M : ℕ → ι → Ω → ℝ}
    (hM : ∀ n, Martingale (M n) F μ)
    (h2 : ∀ n t, MemLp (M n t) 2 μ)
    {s t : ι} (hst : s ≤ t) {X Y : Ω → ℝ}
    (hX : MemLp X 2 μ) (hY : MemLp Y 2 μ)
    (hs : Tendsto (fun n => (h2 n s).toLp (M n s)) atTop (𝓝 (hX.toLp X)))
    (ht : Tendsto (fun n => (h2 n t).toLp (M n t)) atTop (𝓝 (hY.toLp Y))) :
    μ[Y | F s] =ᵐ[μ] X := by
  let C := condExpL2 ℝ ℝ (F.le s) (μ := μ)
  have hC : Continuous (fun f : Lp ℝ 2 μ => (C f : Lp ℝ 2 μ)) :=
    continuous_subtype_val.comp C.continuous
  have heq (n : ℕ) : (C ((h2 n t).toLp (M n t)) : Lp ℝ 2 μ) =
      (h2 n s).toLp (M n s) := by
    apply Lp.ext
    exact ((h2 n t).condExpL2_ae_eq_condExp (𝕜 := ℝ) (F.le s)).trans
      (((hM n).condExp_ae_eq hst).trans (h2 n s).coeFn_toLp.symm)
  have hclass : (C (hY.toLp Y) : Lp ℝ 2 μ) = hX.toLp X := by
    apply tendsto_nhds_unique ((hC.tendsto _).comp ht)
    convert hs using 1
    all_goals try with_reducible_and_instances rfl
    funext n
    exact heq n
  have hae : (C (hY.toLp Y) : Ω → ℝ) =ᵐ[μ] X := by
    change ((C (hY.toLp Y) : Lp ℝ 2 μ) : Ω → ℝ) =ᵐ[μ] X
    rw [hclass]
    exact hX.coeFn_toLp
  exact (hY.condExpL2_ae_eq_condExp (𝕜 := ℝ) (F.le s)).symm.trans hae

theorem martingale_of_L2_limits {M : ℕ → ι → Ω → ℝ} {L : ι → Ω → ℝ}
    (hM : ∀ n, Martingale (M n) F μ) (h2 : ∀ n t, MemLp (M n t) 2 μ)
    (hL : StronglyAdapted F L) (hL2 : ∀ t, MemLp (L t) 2 μ)
    (hlim : ∀ t, Tendsto (fun n => (h2 n t).toLp (M n t)) atTop
      (𝓝 ((hL2 t).toLp (L t)))) : Martingale L F μ := by
  refine ⟨hL, fun s t hst => ?_⟩
  exact condExp_ae_eq_of_L2_limits hM h2 hst (hL2 s) (hL2 t) (hlim s) (hlim t)

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

theorem integral_sq_sub_tendsto_of_L2_tendsto
    {X : ℕ → Ω → ℝ} {L : Ω → ℝ}
    (hX : ∀ n, MemLp (X n) 2 P) (hL : MemLp L 2 P)
    (hlim : Tendsto (fun n => (hX n).toLp (X n)) atTop (𝓝 (hL.toLp L))) :
    Tendsto (fun n => ∫ ω, (X n ω - L ω) ^ 2 ∂P) atTop (𝓝 0) := by
  have hdist := (tendsto_iff_dist_tendsto_zero.mp hlim).pow 2
  simpa only [MartingaleSquareMaximal.dist_toLp_sq, zero_pow (by decide : 2 ≠ 0)] using hdist

end Problem367.BrownianIntegralProcess

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Brownian_StoppedIsometry
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal Topology

namespace Problem367.BrownianIntegralProcess

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}

theorem L2_tendsto_of_integral_sq_sub_tendsto
    {X : ℕ → Ω → ℝ} {L : Ω → ℝ}
    (hX : ∀ n, MemLp (X n) 2 P) (hL : MemLp L 2 P)
    (hlim : Tendsto (fun n => ∫ ω, (X n ω - L ω) ^ 2 ∂P) atTop (𝓝 0)) :
    Tendsto (fun n => (hX n).toLp (X n)) atTop (𝓝 (hL.toLp L)) := by
  apply tendsto_iff_dist_tendsto_zero.mpr
  have hsq : Tendsto (fun n => dist ((hX n).toLp (X n)) (hL.toLp L) ^ 2)
      atTop (𝓝 0) := by
    simpa only [MartingaleSquareMaximal.dist_toLp_sq] using hlim
  have hsqrt := hsq.sqrt
  simpa only [Real.sqrt_sq_eq_abs, abs_of_nonneg dist_nonneg, Real.sqrt_zero] using hsqrt

end Problem367.BrownianIntegralProcess

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Estimates_ContinuousHorizonGluing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Filter Set
open scoped NNReal Topology

namespace Problem367.ContinuousHorizonGluing

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {μ : Measure Ω}

theorem glue_isStronglyPredictable {F : Filtration ℝ≥0 mΩ}
    {L : ℕ → ℝ≥0 → Ω → ℝ} (hL : ∀ n, IsStronglyPredictable F (L n)) :
    IsStronglyPredictable F (glue L) := by
  let : MeasurableSpace (ℝ≥0 × Ω) := F.predictable
  exact StronglyMeasurable.limUnder hL

theorem ae_all_eq_on_Iic {f g : ℝ≥0 → Ω → ℝ} (T : ℝ≥0)
    (hf : ∀ᵐ ω ∂μ, ContinuousOn (fun t => f t ω) (Iic T))
    (hg : ∀ᵐ ω ∂μ, ContinuousOn (fun t => g t ω) (Iic T))
    (hfg : ∀ t ≤ T, f t =ᵐ[μ] g t) :
    ∀ᵐ ω ∂μ, ∀ t ≤ T, f t ω = g t ω := by
  let : Nonempty (Iic T) := ⟨⟨0, by simp⟩⟩
  have hf' : ∀ᵐ ω ∂μ, Continuous (fun t : Iic T => f t ω) := by
    filter_upwards [hf] with ω hω
    exact continuousOn_iff_continuous_domRestrict.mp hω
  have hg' : ∀ᵐ ω ∂μ, Continuous (fun t : Iic T => g t ω) := by
    filter_upwards [hg] with ω hω
    exact continuousOn_iff_continuous_domRestrict.mp hω
  have heq := ae_eq_of_continuous_of_evaluation_ae_eq hf' hg'
    (fun t : Iic T => hfg t t.property)
  filter_upwards [heq] with ω hω
  intro t ht
  exact congrFun hω ⟨t, ht⟩

theorem ae_all_glue_eq {L : ℕ → ℝ≥0 → Ω → ℝ}
    (hc : ∀ n, ∀ᵐ ω ∂μ, ContinuousOn (fun t => L n t ω) (Iic (n : ℝ≥0)))
    (hcompat : ∀ (n m : ℕ) (t : ℝ≥0), t ≤ (n : ℝ≥0) → t ≤ (m : ℝ≥0) →
      L n t =ᵐ[μ] L m t) :
    ∀ᵐ ω ∂μ, ∀ (n : ℕ) (t : ℝ≥0), t ≤ (n : ℝ≥0) → glue L t ω = L n t ω := by
  have heq (n m : ℕ) : ∀ᵐ ω ∂μ, ∀ t ≤ min (n : ℝ≥0) (m : ℝ≥0),
      L n t ω = L m t ω := by
    apply ae_all_eq_on_Iic
    · filter_upwards [hc n] with ω hω
      exact hω.mono (Iic_subset_Iic.mpr (min_le_left _ _))
    · filter_upwards [hc m] with ω hω
      exact hω.mono (Iic_subset_Iic.mpr (min_le_right _ _))
    · intro t ht
      exact hcompat n m t (ht.trans (min_le_left _ _)) (ht.trans (min_le_right _ _))
  have hall : ∀ᵐ ω ∂μ, ∀ (n m : ℕ) (t : ℝ≥0), t ≤ min (n : ℝ≥0) (m : ℝ≥0) →
      L n t ω = L m t ω := ae_all_iff.mpr (fun n => ae_all_iff.mpr (heq n))
  filter_upwards [hall] with ω hω
  intro n t ht
  apply Filter.Tendsto.limUnder_eq
  apply tendsto_const_nhds.congr'
  filter_upwards [eventually_ge_atTop n] with m hm
  exact hω n m t (le_min ht (ht.trans (by exact_mod_cast hm)))

theorem ae_continuous_glue {L : ℕ → ℝ≥0 → Ω → ℝ}
    (hc : ∀ n, ∀ᵐ ω ∂μ, ContinuousOn (fun t => L n t ω) (Iic (n : ℝ≥0)))
    (hcompat : ∀ (n m : ℕ) (t : ℝ≥0), t ≤ (n : ℝ≥0) → t ≤ (m : ℝ≥0) →
      L n t =ᵐ[μ] L m t) :
    ∀ᵐ ω ∂μ, Continuous (fun t => glue L t ω) := by
  filter_upwards [ae_all_iff.mpr hc, ae_all_glue_eq hc hcompat] with ω hcω hω
  apply continuous_iff_continuousAt.mpr
  intro t
  obtain ⟨n, hn⟩ := exists_nat_gt t
  have hlocal : ContinuousOn (fun s => glue L s ω) (Iic (n : ℝ≥0)) :=
    (hcω n).congr (fun s hs => hω n s hs)
  exact hlocal.continuousAt (Iic_mem_nhds hn)

end Problem367.ContinuousHorizonGluing

namespace Problem367.MartingaleSquareMaximal

theorem exists_global_predictable_continuous_L2_limit
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {μ : Measure Ω} [IsFiniteMeasure μ]
    {F : Filtration ℝ≥0 mΩ} {M : ℕ → ℝ≥0 → Ω → ℝ}
    (hM : ∀ n, Martingale (M n) F μ)
    (h2 : ∀ n t, MemLp (M n t) 2 μ)
    (hc : ∀ n, ∀ᵐ ω ∂μ, Continuous (fun t => M n t ω))
    (hC : ∀ N : ℕ, CauchySeq (fun n => (h2 n (N : ℝ≥0)).toLp (M n N))) :
    ∃ L : ℝ≥0 → Ω → ℝ, IsStronglyPredictable F L ∧
      (∀ᵐ ω ∂μ, Continuous (fun t => L t ω)) ∧
      ∀ t, ∃ hL2 : MemLp (L t) 2 μ,
        Tendsto (fun n => (h2 n t).toLp (M n t)) atTop (𝓝 (hL2.toLp (L t))) := by
  have hlocal (N : ℕ) := exists_predictable_continuous_L2_limit hM h2 hc
    (N : ℝ≥0) (hC N)
  choose L hpred hcont hlim using hlocal
  have hcompat (n m : ℕ) (t : ℝ≥0) (hn : t ≤ n) (hm : t ≤ m) :
      L n t =ᵐ[μ] L m t := by
    obtain ⟨hn2, hnlim⟩ := hlim n t hn
    obtain ⟨hm2, hmlim⟩ := hlim m t hm
    have hclass := tendsto_nhds_unique hnlim hmlim
    filter_upwards [hn2.coeFn_toLp, hm2.coeFn_toLp] with ω hnω hmω
    rw [← hnω, ← hmω, hclass]
  refine ⟨ContinuousHorizonGluing.glue L,
    ContinuousHorizonGluing.glue_isStronglyPredictable hpred,
    ContinuousHorizonGluing.ae_continuous_glue hcont hcompat, ?_⟩
  intro t
  obtain ⟨n, hn⟩ := exists_nat_ge t
  obtain ⟨hn2, hnlim⟩ := hlim n t hn
  have heq : ContinuousHorizonGluing.glue L t =ᵐ[μ] L n t := by
    filter_upwards [ContinuousHorizonGluing.ae_all_glue_eq hcont hcompat] with ω hω
    exact hω n t hn
  have hL2 : MemLp (ContinuousHorizonGluing.glue L t) 2 μ := hn2.ae_eq heq.symm
  refine ⟨hL2, ?_⟩
  rw [hL2.toLp_congr hn2 heq]
  exact hnlim

end Problem367.MartingaleSquareMaximal

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Martingales_StrongMaximal
attribute [-instance] _root_.OAI.Problem367.WienerSampler.pathMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Filter Finset
open scoped NNReal ENNReal Topology

namespace Problem367.MartingaleStrongMaximal

theorem self_le_runningMax (x : ℕ → ℝ) (n : ℕ) : x n ≤ runningMax x n := by
  cases n with
  | zero => rfl
  | succ n => exact le_max_right _ _

theorem runningMax_mono (x : ℕ → ℝ) : Monotone (runningMax x) := by
  apply monotone_nat_of_le_succ
  intro n
  exact le_max_left _ _

theorem le_runningMax (x : ℕ → ℝ) {i n : ℕ} (h : i ≤ n) : x i ≤ runningMax x n :=
  (self_le_runningMax x i).trans (runningMax_mono x h)

theorem runningMax_sq_le_twice (x : ℕ → ℝ) (n : ℕ) :
    runningMax x n ^ 2 ≤ 2 * runningMax x n * x n -
      2 * ∑ k ∈ range n, runningMax x k * (x (k + 1) - x k) := by
  induction n with
  | zero =>
    simp only [sum_range_zero, mul_zero, sub_zero, runningMax_zero]
    nlinarith [sq_nonneg (x 0)]
  | succ n ih =>
    rw [sum_range_succ, runningMax_succ]
    rcases le_total (x (n + 1)) (runningMax x n) with h | h
    · rw [max_eq_left h]
      nlinarith
    · rw [max_eq_right h]
      nlinarith [sq_nonneg (x (n + 1) - runningMax x n)]

theorem runningMax_sq_le_four (x : ℕ → ℝ) (n : ℕ) :
    runningMax x n ^ 2 ≤ 4 * x n ^ 2 -
      4 * ∑ k ∈ range n, runningMax x k * (x (k + 1) - x k) := by
  have h := runningMax_sq_le_twice x n
  nlinarith [sq_nonneg (runningMax x n - 2 * x n)]

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {μ : Measure Ω}

theorem runningMax_memLp {X : ℕ → Ω → ℝ} (h2 : ∀ n, MemLp (X n) 2 μ) (n : ℕ) :
    MemLp (fun ω => runningMax (fun k => X k ω) n) 2 μ := by
  induction n with
  | zero => exact h2 0
  | succ n ih => exact ih.sup (h2 (n + 1))

theorem runningMax_stronglyAdapted {F : Filtration ℕ mΩ} {X : ℕ → Ω → ℝ}
    (hX : StronglyAdapted F X) :
    StronglyAdapted F (fun n ω => runningMax (fun k => X k ω) n) := by
  intro n
  induction n with
  | zero => exact hX 0
  | succ n ih =>
    let : MeasurableSpace Ω := F (n + 1)
    have hi : StronglyMeasurable[F (n + 1)]
        (fun ω => runningMax (fun k => X k ω) n) := ih.mono (F.mono (Nat.le_succ n))
    exact hi.sup (hX (n + 1))

theorem integral_mul_sub_nonneg [IsFiniteMeasure μ]
    {F : Filtration ℕ mΩ} {X : ℕ → Ω → ℝ} (hX : Submartingale X F μ)
    (n : ℕ) {H : Ω → ℝ} (hH : StronglyMeasurable[F n] H)
    (hHnonneg : ∀ ω, 0 ≤ H ω)
    (hprod : Integrable (fun ω => H ω * (X (n + 1) ω - X n ω)) μ) :
    0 ≤ ∫ ω, H ω * (X (n + 1) ω - X n ω) ∂μ := by
  have hpull := condExp_mul_of_stronglyMeasurable_left hH hprod
    ((hX.integrable (n + 1)).sub (hX.integrable n))
  rw [← integral_condExp (F.le n)]
  apply integral_nonneg_of_ae
  filter_upwards [hpull, hX.condExp_sub_nonneg (Nat.le_succ n)] with ω hp hn
  change 0 ≤ μ[H * (fun ω => X (n + 1) ω - X n ω) | F n] ω
  rw [hp]
  exact mul_nonneg (hHnonneg ω) hn

theorem finite_submartingale_maximal_sq [IsFiniteMeasure μ]
    {F : Filtration ℕ mΩ} {X : ℕ → Ω → ℝ}
    (hX : Submartingale X F μ) (h2 : ∀ n, MemLp (X n) 2 μ)
    (hnonneg : ∀ n ω, 0 ≤ X n ω) (n : ℕ) :
    (∫ ω, runningMax (fun k => X k ω) n ^ 2 ∂μ) ≤
      4 * ∫ ω, X n ω ^ 2 ∂μ := by
  have hmax2 := runningMax_memLp h2
  have hmaxA := runningMax_stronglyAdapted hX.stronglyAdapted
  have hprod (k : ℕ) : Integrable (fun ω =>
      runningMax (fun j => X j ω) k * (X (k + 1) ω - X k ω)) μ :=
    (hmax2 k).integrable_mul ((h2 (k + 1)).sub (h2 k))
  have hsum : Integrable (fun ω => ∑ k ∈ range n,
      runningMax (fun j => X j ω) k * (X (k + 1) ω - X k ω)) μ :=
    integrable_finsetSum _ (fun k _ => hprod k)
  have hbound := integral_mono (hmax2 n).integrable_sq
    (((h2 n).integrable_sq.const_mul 4).sub (hsum.const_mul 4))
    (fun ω => runningMax_sq_le_four (fun k => X k ω) n)
  simp only [Pi.sub_apply] at hbound
  rw [integral_sub ((h2 n).integrable_sq.const_mul 4) (hsum.const_mul 4),
    integral_const_mul, integral_const_mul,
    integral_finsetSum _ (fun k _ => hprod k)] at hbound
  have hsum_nonneg : 0 ≤ ∑ k ∈ range n, ∫ ω,
      runningMax (fun j => X j ω) k * (X (k + 1) ω - X k ω) ∂μ := by
    apply sum_nonneg
    intro k hk
    exact integral_mul_sub_nonneg hX k (hmaxA k)
      (fun ω => (hnonneg k ω).trans (self_le_runningMax (fun j => X j ω) k)) (hprod k)
  linarith

theorem submartingale_abs {F : Filtration ℕ mΩ} {M : ℕ → Ω → ℝ}
    (hM : Martingale M F μ) : Submartingale (fun n ω => |M n ω|) F μ := by
  refine ⟨fun n => ?_, ?_, fun n => (hM.integrable n).abs⟩
  · simpa only [Real.norm_eq_abs] using (hM.stronglyMeasurable n).norm
  · intro i j hij
    have hj := norm_condExp_le (m := F i) (μ := μ) (M j)
    filter_upwards [hj, hM.condExp_ae_eq hij] with ω hω heq
    simpa only [Real.norm_eq_abs, heq] using hω

theorem finite_martingale_maximal_sq [IsFiniteMeasure μ]
    {F : Filtration ℕ mΩ} {M : ℕ → Ω → ℝ}
    (hM : Martingale M F μ) (h2 : ∀ n, MemLp (M n) 2 μ) (n : ℕ) :
    (∫ ω, runningMax (fun k => |M k ω|) n ^ 2 ∂μ) ≤
      4 * ∫ ω, M n ω ^ 2 ∂μ := by
  simpa only [sq_abs] using finite_submartingale_maximal_sq (submartingale_abs hM)
    (fun n => (h2 n).norm) (fun n ω => abs_nonneg (M n ω)) n

theorem runningMax_le {x : ℕ → ℝ} {n : ℕ} {a : ℝ}
    (h : ∀ k ≤ n, x k ≤ a) : runningMax x n ≤ a := by
  induction n with
  | zero => exact h 0 le_rfl
  | succ n ih =>
    exact max_le (ih (fun k hk => h k (hk.trans (Nat.le_succ n)))) (h (n + 1) le_rfl)

theorem sampled_martingale_maximal_sq [IsFiniteMeasure μ]
    {ι : Type*} [Preorder ι] {F : Filtration ι mΩ} {M : ι → Ω → ℝ}
    (hM : Martingale M F μ) (h2 : ∀ t, MemLp (M t) 2 μ)
    (q : ℕ → ι) (hq : Monotone q) (n : ℕ) {T : ι} (hT : q n ≤ T) :
    (∫ ω, runningMax (fun k => |M (q k) ω|) n ^ 2 ∂μ) ≤
      4 * ∫ ω, M T ω ^ 2 ∂μ := by
  let G : Filtration ℕ mΩ := ⟨fun k => F (q k),
    fun _ _ h => F.mono (hq h), fun k => F.le (q k)⟩
  have hMq : Martingale (fun k => M (q k)) G μ :=
    ⟨fun k => hM.stronglyMeasurable (q k), fun i j hij => hM.condExp_ae_eq (hq hij)⟩
  exact (finite_martingale_maximal_sq hMq (fun k => h2 (q k)) n).trans
    (mul_le_mul_of_nonneg_left (MartingaleSquareMaximal.integral_sq_le hM h2 hT)
      (by norm_num))

theorem dyadicPoint_mono (n : ℕ) : Monotone (dyadicPoint n) := by
  intro i j hij
  dsimp [dyadicPoint]
  gcongr

theorem dyadicPoint_double (n k : ℕ) :
    dyadicPoint (n + 1) (2 * k) = dyadicPoint n k := by
  simp only [dyadicPoint, pow_succ, Nat.cast_mul, Nat.cast_ofNat]
  field_simp

theorem dyadicPoint_le_iff {n k : ℕ} {T : ℝ≥0} :
    dyadicPoint n k ≤ T ↔ k ≤ dyadicCount n T := by
  have hp : (0 : ℝ≥0) < (2 ^ n : ℕ) := by positivity
  rw [dyadicPoint, div_le_iff₀ hp, dyadicCount, Nat.le_floor_iff (by positivity)]
  rw [mul_comm]

theorem dyadicPoint_eq_mesh (n k : ℕ) :
    dyadicPoint n k = PredictableMesh.point (2 ^ n - 1) k := by
  have hn : 1 ≤ 2 ^ n := Nat.one_le_pow n 2 (by norm_num)
  simp only [dyadicPoint, PredictableMesh.point, Nat.sub_add_cancel hn]

omit mΩ in
theorem gridMax_nonneg (M : ℝ≥0 → Ω → ℝ) (T : ℝ≥0) (n : ℕ) (ω : Ω) :
    0 ≤ gridMax M T n ω :=
  (abs_nonneg _).trans (self_le_runningMax
    (fun k => |M (dyadicPoint n k) ω|) (dyadicCount n T))

omit mΩ in
theorem gridMax_mono (M : ℝ≥0 → Ω → ℝ) (T : ℝ≥0) (ω : Ω) :
    Monotone (fun n => gridMax M T n ω) := by
  apply monotone_nat_of_le_succ
  intro n
  apply runningMax_le
  intro k hk
  have ht : dyadicPoint (n + 1) (2 * k) ≤ T := by
    rw [dyadicPoint_double]
    exact dyadicPoint_le_iff.mpr hk
  have hb := le_runningMax (fun j => |M (dyadicPoint (n + 1) j) ω|)
    (dyadicPoint_le_iff.mp ht)
  simpa only [dyadicPoint_double, gridMax] using hb

theorem gridMax_memLp {M : ℝ≥0 → Ω → ℝ} (h2 : ∀ t, MemLp (M t) 2 μ)
    (T : ℝ≥0) (n : ℕ) : MemLp (gridMax M T n) 2 μ :=
  runningMax_memLp (fun k => (h2 (dyadicPoint n k)).norm) _

theorem gridMax_integral_sq_le [IsFiniteMeasure μ]
    {F : Filtration ℝ≥0 mΩ} {M : ℝ≥0 → Ω → ℝ}
    (hM : Martingale M F μ) (h2 : ∀ t, MemLp (M t) 2 μ) (T : ℝ≥0) (n : ℕ) :
    (∫ ω, gridMax M T n ω ^ 2 ∂μ) ≤ 4 * ∫ ω, M T ω ^ 2 ∂μ :=
  sampled_martingale_maximal_sq hM h2 (dyadicPoint n) (dyadicPoint_mono n) _
    (dyadicPoint_le_iff.mpr le_rfl)

omit mΩ in

theorem supremumSq_eq_iSup_gridMax {M : ℝ≥0 → Ω → ℝ} {ω : Ω}
    (hc : Continuous (fun t => M t ω)) (T : ℝ≥0) :
    supremumSq M T ω = ⨆ n : ℕ, ENNReal.ofReal (gridMax M T n ω ^ 2) := by
  apply le_antisymm
  · apply iSup_le
    intro t
    have hp : Tendsto (fun n : ℕ => 2 ^ n - 1) atTop atTop :=
      (tendsto_sub_atTop_nat 1).comp
        (tendsto_pow_atTop_atTop_of_one_lt (by norm_num : (1 : ℕ) < 2))
    have hlim : Tendsto (fun n : ℕ => ENNReal.ofReal
        (M (PredictableMesh.left (2 ^ n - 1) t) ω ^ 2)) atTop
        (𝓝 (ENNReal.ofReal (M t ω ^ 2))) :=
      ENNReal.tendsto_ofReal (((hc.tendsto t).comp
        ((PredictableMesh.tendsto_left t).comp hp)).pow 2)
    apply le_of_tendsto hlim
    apply Filter.Eventually.of_forall
    intro n
    apply le_iSup_of_le n
    apply ENNReal.ofReal_le_ofReal
    rw [← sq_abs (M (PredictableMesh.left (2 ^ n - 1) t) ω)]
    apply (sq_le_sq₀ (abs_nonneg _) (gridMax_nonneg M T n ω)).mpr
    let k := ⌈((2 ^ n - 1 + 1 : ℕ) : ℝ≥0) * t⌉₊ - 1
    have heq : dyadicPoint n k = PredictableMesh.left (2 ^ n - 1) t :=
      dyadicPoint_eq_mesh n k
    have ht : dyadicPoint n k ≤ T := by
      rw [heq]
      exact (PredictableMesh.left_le _ t).trans t.property
    have hb := le_runningMax (fun j => |M (dyadicPoint n j) ω|)
      (dyadicPoint_le_iff.mp ht)
    simpa only [heq, gridMax] using hb
  · apply iSup_le
    intro n
    have hmax : ∃ k ≤ dyadicCount n T,
        gridMax M T n ω = |M (dyadicPoint n k) ω| := by
      dsimp only [gridMax]
      generalize dyadicCount n T = N
      induction N with
      | zero => exact ⟨0, le_rfl, rfl⟩
      | succ N ih =>
        obtain ⟨k, hk, heq⟩ := ih
        rcases le_total |M (dyadicPoint n (N + 1)) ω|
          (runningMax (fun k => |M (dyadicPoint n k) ω|) N) with h | h
        · exact ⟨k, hk.trans (Nat.le_succ N), (max_eq_left h).trans heq⟩
        · exact ⟨N + 1, le_rfl, max_eq_right h⟩
    obtain ⟨k, hk, heq⟩ := hmax
    rw [heq, sq_abs]
    exact le_iSup_of_le ⟨dyadicPoint n k, dyadicPoint_le_iff.mpr hk⟩ le_rfl

theorem continuous_martingale_maximal_sq [IsFiniteMeasure μ]
    {F : Filtration ℝ≥0 mΩ} {M : ℝ≥0 → Ω → ℝ}
    (hM : Martingale M F μ) (h2 : ∀ t, MemLp (M t) 2 μ)
    (hc : ∀ᵐ ω ∂μ, Continuous (fun t => M t ω)) (T : ℝ≥0) :
    (∫⁻ ω, supremumSq M T ω ∂μ) ≤
      ENNReal.ofReal (4 * ∫ ω, M T ω ^ 2 ∂μ) := by
  have heq : supremumSq M T =ᵐ[μ]
      (fun ω => ⨆ n : ℕ, ENNReal.ofReal (gridMax M T n ω ^ 2)) := by
    filter_upwards [hc] with ω hω
    exact supremumSq_eq_iSup_gridMax hω T
  rw [lintegral_congr_ae heq, lintegral_iSup']
  · apply iSup_le
    intro n
    rw [← ofReal_integral_eq_lintegral_ofReal (gridMax_memLp h2 T n).integrable_sq
      (Filter.Eventually.of_forall (fun ω => sq_nonneg _))]
    exact ENNReal.ofReal_le_ofReal (gridMax_integral_sq_le hM h2 T n)
  · intro n
    exact ((gridMax_memLp h2 T n).aestronglyMeasurable.pow 2).aemeasurable.ennreal_ofReal
  · exact Filter.Eventually.of_forall fun ω n m hnm =>
      ENNReal.ofReal_le_ofReal ((sq_le_sq₀ (gridMax_nonneg M T n ω)
        (gridMax_nonneg M T m ω)).mpr (gridMax_mono M T ω hnm))

theorem supremumSq_aemeasurable {M : ℝ≥0 → Ω → ℝ}
    (h2 : ∀ t, MemLp (M t) 2 μ)
    (hc : ∀ᵐ ω ∂μ, Continuous (fun t => M t ω)) (T : ℝ≥0) :
    AEMeasurable (supremumSq M T) μ := by
  have hg : AEMeasurable
      (fun ω => ⨆ n : ℕ, ENNReal.ofReal (gridMax M T n ω ^ 2)) μ :=
    AEMeasurable.iSup (fun n =>
      ((gridMax_memLp h2 T n).aestronglyMeasurable.pow 2).aemeasurable.ennreal_ofReal)
  apply hg.congr
  filter_upwards [hc] with ω hω
  exact (supremumSq_eq_iSup_gridMax hω T).symm

theorem ae_supremumSq_lt_top [IsFiniteMeasure μ]
    {F : Filtration ℝ≥0 mΩ} {M : ℝ≥0 → Ω → ℝ}
    (hM : Martingale M F μ) (h2 : ∀ t, MemLp (M t) 2 μ)
    (hc : ∀ᵐ ω ∂μ, Continuous (fun t => M t ω)) (T : ℝ≥0) :
    ∀ᵐ ω ∂μ, supremumSq M T ω < ∞ :=
  ae_lt_top' (supremumSq_aemeasurable h2 hc T)
    (ne_top_of_le_ne_top ENNReal.ofReal_ne_top (continuous_martingale_maximal_sq hM h2 hc T))

theorem integral_maximalSquare_le [IsFiniteMeasure μ]
    {F : Filtration ℝ≥0 mΩ} {M : ℝ≥0 → Ω → ℝ}
    (hM : Martingale M F μ) (h2 : ∀ t, MemLp (M t) 2 μ)
    (hc : ∀ᵐ ω ∂μ, Continuous (fun t => M t ω)) (T : ℝ≥0) :
    (∫ ω, maximalSquare M T ω ∂μ) ≤ 4 * ∫ ω, M T ω ^ 2 ∂μ := by
  change (∫ ω, (supremumSq M T ω).toReal ∂μ) ≤ _
  rw [integral_toReal (supremumSq_aemeasurable h2 hc T) (ae_supremumSq_lt_top hM h2 hc T)]
  have h := ENNReal.toReal_mono ENNReal.ofReal_ne_top
    (continuous_martingale_maximal_sq hM h2 hc T)
  simpa only [ENNReal.toReal_ofReal (mul_nonneg (by norm_num : (0 : ℝ) ≤ 4)
    (integral_nonneg (fun ω => sq_nonneg (M T ω))))] using h

end Problem367.MartingaleStrongMaximal

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

variable [IsProbabilityMeasure P]
    (hcross : ∀ s t, s ≤ t → Pairwise fun a b =>
      IndepFun (fun ω => B a t ω - B a s ω) (fun ω => B b t ω - B b s ω) P)

include hB hAd hind hcross hH hK hcH hcK hC hD hbH hbK heH heK in

theorem infinite_row_difference_isometry_of_row_energies
    {I J : ι → Ω → ℝ}
    (hI : ∀ a, MemLp (I a) 2 P) (hJ : ∀ a, MemLp (J a) 2 P)
    (haI : ∀ a, Tendsto (fun n => ∫ ω,
      (BrownianGrid.uniformSum (B a) (H a) T n ω - I a ω) ^ 2 ∂P) atTop (𝓝 0))
    (haJ : ∀ a, Tendsto (fun n => ∫ ω,
      (BrownianGrid.uniformSum (B a) (K a) T n ω - J a ω) ^ 2 ∂P) atTop (𝓝 0))
    {Y Z : Ω → ℝ} (hY : MemLp Y 2 P) (hZ : MemLp Z 2 P)
    (hsY : Tendsto (fun s : Finset ι => ∫ ω,
      ((∑ a ∈ s, I a ω) - Y ω) ^ 2 ∂P) atTop (𝓝 0))
    (hsZ : Tendsto (fun s : Finset ι => ∫ ω,
      ((∑ a ∈ s, J a ω) - Z ω) ^ 2 ∂P) atTop (𝓝 0)) :
    (∫ ω, (Y ω - Z ω) ^ 2 ∂P) =
      ∑' a, ∫ t in (0 : ℝ)..(T : ℝ),
        ∫ ω, (H a t.toNNReal ω - K a t.toNNReal ω) ^ 2 ∂P := by
  exact infinite_row_difference_isometry hB hAd hind hcross
    H K hH hK hcH hcK C D hC hD hbH hbK T hI hJ haI haJ hY hZ hsY hsZ
    (summable_difference_energy_of_row_energies hB hAd hind
      H K hH hK hcH hcK C D hC hD hbH hbK T heH heK hI hJ haI haJ)

end Problem367.BrownianArrayFiltration

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Brownian_ContinuousRowCompletion
attribute [-instance] _root_.OAI.Problem367.WienerSampler.pathMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped NNReal Topology BigOperators

namespace Problem367.MartingaleSquareMaximal

theorem exists_global_continuous_meanSquare_limit
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsFiniteMeasure P]
    {F : Filtration ℝ≥0 mΩ} {M : ℕ → ℝ≥0 → Ω → ℝ}
    (hM : ∀ n, Martingale (M n) F P)
    (h2 : ∀ n t, MemLp (M n t) 2 P)
    (hc : ∀ n, ∀ᵐ ω ∂P, Continuous (fun t => M n t ω))
    (hC : ∀ N : ℕ, 0 < N → ∀ ε > (0 : ℝ), ∃ k : ℕ,
      ∀ n ≥ k, ∀ m ≥ k, (∫ ω, (M n N ω - M m N ω) ^ 2 ∂P) < ε) :
    ∃ (Z : ℝ≥0 → Ω → ℝ) (_hZ2 : ∀ t, MemLp (Z t) 2 P),
      IsStronglyPredictable F Z ∧ Martingale Z F P ∧
      (∀ᵐ ω ∂P, Continuous (fun t => Z t ω)) ∧
      (∀ t, Tendsto (fun n => ∫ ω, (M n t ω - Z t ω) ^ 2 ∂P) atTop (𝓝 0)) ∧
      (∀ t, Tendsto (fun n => ∫ ω, M n t ω ^ 2 ∂P) atTop
        (𝓝 (∫ ω, Z t ω ^ 2 ∂P))) ∧
      (∀ T, Tendsto (fun n => ∫ ω,
        MartingaleStrongMaximal.maximalSquare (M n - Z) T ω ∂P) atTop (𝓝 0)) := by
  have hCpos (N : ℕ) (hN : 0 < N) :
      CauchySeq (fun n => (h2 n (N : ℝ≥0)).toLp (M n N)) := by
    apply Metric.cauchySeq_iff.mpr
    intro ε hε
    obtain ⟨k, hk⟩ := hC N hN (ε ^ 2) (sq_pos_of_pos hε)
    refine ⟨k, fun n hn m hm => ?_⟩
    have hs := hk n hn m hm
    rw [← dist_toLp_sq (h2 n N) (h2 m N)] at hs
    nlinarith [dist_nonneg (x := (h2 n N).toLp (M n N))
      (y := (h2 m N).toLp (M m N))]
  have hCall (N : ℕ) : CauchySeq (fun n => (h2 n (N : ℝ≥0)).toLp (M n N)) :=
    L2_cauchy_of_le hM h2 (by exact_mod_cast Nat.le_succ N)
      (hCpos (N + 1) (Nat.succ_pos N))
  obtain ⟨Z, hpZ, hcZ, hlZ⟩ :=
    exists_global_predictable_continuous_L2_limit hM h2 hc hCall
  choose hZ2 hl using hlZ
  have hmartZ : Martingale Z F P :=
    martingale_of_L2_limits hM h2 hpZ.stronglyAdapted hZ2 hl
  have hmean (t : ℝ≥0) := BrownianIntegralProcess.integral_sq_sub_tendsto_of_L2_tendsto
    (fun n => h2 n t) (hZ2 t) (hl t)
  refine ⟨Z, hZ2, hpZ, hmartZ, hcZ, hmean, ?_, ?_⟩
  · intro t
    simpa only [PredictableL2.norm_toLp_sq] using (hl t).norm.pow 2
  · intro T
    apply squeeze_zero (fun n => integral_nonneg (fun ω => ENNReal.toReal_nonneg))
      (fun n => ?_) (show Tendsto
        (fun n => 4 * ∫ ω, (M n T ω - Z T ω) ^ 2 ∂P) atTop (𝓝 0) from by
          simpa only [mul_zero] using (hmean T).const_mul 4)
    exact MartingaleStrongMaximal.integral_maximalSquare_le
      ((hM n).sub hmartZ) (fun t => (h2 n t).sub (hZ2 t))
      (by filter_upwards [hc n, hcZ] with ω hn hz; exact hn.sub hz) T

end Problem367.MartingaleSquareMaximal

namespace Problem367.BrownianArrayFiltration

theorem exists_global_continuous_integral_limit_of_row_energy_cauchy
    {Ω ι : Type*} [mΩ : MeasurableSpace Ω] [Countable ι]
    {P : Measure Ω} [IsProbabilityMeasure P]
    {B : ι → ℝ≥0 → Ω → ℝ} {F : Filtration ℝ≥0 mΩ}
    (hB : ∀ a, IsPreBrownianReal (B a) P)
    (hAd : ∀ a, StronglyAdapted F (B a))
    (hind : ∀ s t, s ≤ t → Indep
      (MeasurableSpace.comap (fun ω a => B a t ω - B a s ω) inferInstance) (F s) P)
    (hcross : ∀ s t, s ≤ t → Pairwise fun a b =>
      IndepFun (fun ω => B a t ω - B a s ω) (fun ω => B b t ω - B b s ω) P)
    (hBc : ∀ a, ∀ᵐ ω ∂P, Continuous (fun t => B a t ω))
    (H : ℕ → ι → ℝ≥0 → Ω → ℝ)
    (hH : ∀ n a, StronglyAdapted F (H n a))
    (hcH : ∀ n a, ∀ᵐ ω ∂P, Continuous (fun t => H n a t ω))
    (C : ℕ → ι → ℝ) (hC : ∀ n a, 0 ≤ C n a)
    (hbH : ∀ n a, ∀ᵐ ω ∂P, ∀ t, |H n a t ω| ≤ C n a)
    (he : ∀ n (N : ℕ), Summable fun a => ∫ t in (0 : ℝ)..(N : ℝ),
      ∫ ω, H n a t.toNNReal ω ^ 2 ∂P)
    (hCauchy : ∀ N : ℕ, 0 < N → ∀ ε > (0 : ℝ), ∃ k : ℕ,
      ∀ n ≥ k, ∀ m ≥ k, (∑' a, ∫ t in (0 : ℝ)..(N : ℝ),
        ∫ ω, (H n a t.toNNReal ω - H m a t.toNNReal ω) ^ 2 ∂P) < ε) :
    ∃ (I : ℕ → ι → ℝ≥0 → Ω → ℝ) (Y : ℕ → ℝ≥0 → Ω → ℝ)
      (Z : ℝ≥0 → Ω → ℝ)
      (hI2 : ∀ n a t, MemLp (I n a t) 2 P)
      (hY2 : ∀ n t, MemLp (Y n t) 2 P) (_hZ2 : ∀ t, MemLp (Z t) 2 P),
      (∀ n, IsStronglyPredictable F (Y n) ∧ Martingale (Y n) F P ∧
        (∀ᵐ ω ∂P, Continuous (fun t => Y n t ω))) ∧
      (∀ n a (N : ℕ), 0 < N → Tendsto (fun k => ∫ ω,
        (BrownianGrid.uniformSum (B a) (H n a) N k ω - I n a N ω) ^ 2 ∂P)
          atTop (𝓝 0)) ∧
      (∀ n t, HasSum (fun a => (hI2 n a t).toLp (I n a t))
        ((hY2 n t).toLp (Y n t))) ∧
      (∀ n t, (∫ ω, Y n t ω ^ 2 ∂P) =
        ∑' a, ∫ s in (0 : ℝ)..(t : ℝ), ∫ ω, H n a s.toNNReal ω ^ 2 ∂P) ∧
      (∀ n m (N : ℕ), 0 < N → (∫ ω, (Y n N ω - Y m N ω) ^ 2 ∂P) =
        ∑' a, ∫ s in (0 : ℝ)..(N : ℝ),
          ∫ ω, (H n a s.toNNReal ω - H m a s.toNNReal ω) ^ 2 ∂P) ∧
      IsStronglyPredictable F Z ∧ Martingale Z F P ∧
      (∀ᵐ ω ∂P, Continuous (fun t => Z t ω)) ∧ Z 0 =ᵐ[P] 0 ∧
      (∀ t, (∫ ω, Z t ω ∂P) = 0) ∧
      (∀ t, Tendsto (fun n => ∫ ω, (Y n t ω - Z t ω) ^ 2 ∂P) atTop (𝓝 0)) ∧
      (∀ t : ℝ≥0, Tendsto (fun n => ∑' a, ∫ s in (0 : ℝ)..(t : ℝ),
        ∫ ω, H n a s.toNNReal ω ^ 2 ∂P) atTop (𝓝 (∫ ω, Z t ω ^ 2 ∂P))) ∧
      (∀ T, Tendsto (fun n => ∫ ω,
        MartingaleStrongMaximal.maximalSquare (Y n - Z) T ω ∂P) atTop (𝓝 0)) := by
  have hex (n : ℕ) := exists_global_continuous_spatial_integral
    hB hAd hind hcross hBc (H n) (hH n) (hcH n) (C n) (hC n) (hbH n) (he n)
  choose I Y hI2 hY2 hIprop haI hpY hmY hcY hzY hmeanY heY hsY hmaxY using hex
  have ha (n : ℕ) (a : ι) (N : ℕ) (hN : 0 < N) :
      Tendsto (fun k => ∫ ω,
        (BrownianGrid.uniformSum (B a) (H n a) N k ω - I n a N ω) ^ 2 ∂P)
          atTop (𝓝 0) := by
    simpa only [BrownianIntegralProcess.stoppedUniformSum_terminal] using
      haI n a N hN N le_rfl
  have hs (n : ℕ) (t : ℝ≥0) : Tendsto (fun s : Finset ι => ∫ ω,
      ((∑ a ∈ s, I n a t ω) - Y n t ω) ^ 2 ∂P) atTop (𝓝 0) :=
    PredictableL2.tendsto_integral_sq_error_of_hasSum
      (fun a => I n a t) (fun a => hI2 n a t) (hY2 n t) (hsY n t)
  have hpair (n m N : ℕ) (hN : 0 < N) :
      (∫ ω, (Y n N ω - Y m N ω) ^ 2 ∂P) =
        ∑' a, ∫ s in (0 : ℝ)..(N : ℝ),
          ∫ ω, (H n a s.toNNReal ω - H m a s.toNNReal ω) ^ 2 ∂P :=
    infinite_row_difference_isometry_of_row_energies hB hAd hind
      (H n) (H m) (hH n) (hH m) (hcH n) (hcH m)
      (C n) (C m) (hC n) (hC m) (hbH n) (hbH m) N (he n N) (he m N)
      hcross (fun a => hI2 n a N) (fun a => hI2 m a N)
      (fun a => ha n a N hN) (fun a => ha m a N hN)
      (hY2 n N) (hY2 m N) (hs n N) (hs m N)
  have hCY (N : ℕ) (hN : 0 < N) : ∀ ε > (0 : ℝ), ∃ k : ℕ,
      ∀ n ≥ k, ∀ m ≥ k, (∫ ω, (Y n N ω - Y m N ω) ^ 2 ∂P) < ε := by
    simpa only [hpair _ _ N hN] using hCauchy N hN
  obtain ⟨Z, hZ2, hpZ, hmZ, hcZ, hlZ, heZ, hmaxZ⟩ :=
    MartingaleSquareMaximal.exists_global_continuous_meanSquare_limit hmY hY2 hcY hCY
  have hzZ : Z 0 =ᵐ[P] 0 := by
    have hzero (n : ℕ) : (∫ ω, Y n 0 ω ^ 2 ∂P) = 0 := by
      simp only [heY, NNReal.coe_zero, intervalIntegral.integral_same, tsum_zero]
    have henergy0 : (∫ ω, Z 0 ω ^ 2 ∂P) = 0 :=
      tendsto_nhds_unique (heZ 0) (by simpa only [hzero] using
        (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 0)))
    apply ae_eq_of_integral_sq_sub_eq_zero
    · simpa only [Pi.zero_apply, sub_zero] using (hZ2 0).integrable_sq
    · simpa only [Pi.zero_apply, sub_zero] using henergy0
  have hcenter (t : ℝ≥0) : (∫ ω, Z t ω ∂P) = 0 := by
    have hlim := BrownianIntegralProcess.L2_tendsto_of_integral_sq_sub_tendsto
      (fun n => hY2 n t) (hZ2 t) (hlZ t)
    have hi := (tendsto_const_nhds (x := (memLp_const (1 : ℝ)).toLp
      (fun _ : Ω => (1 : ℝ)))).inner (𝕜 := ℝ) hlim
    simp only [PredictableL2.inner_toLp, one_mul, hmeanY] at hi
    exact tendsto_nhds_unique hi tendsto_const_nhds
  refine ⟨I, Y, Z, hI2, hY2, hZ2, (fun n => ⟨hpY n, hmY n, hcY n⟩), ha,
    hsY, heY, hpair, hpZ, hmZ, hcZ, hzZ, hcenter, hlZ, ?_, hmaxZ⟩
  intro t
  simpa only [heY] using heZ t

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
attribute [-instance] _root_.OAI.Problem367.IsingConditionalCopyBounds.graphLaw_isProbabilityMeasure _root_.OAI.Problem367.IsingObservationFactor.copies_probability _root_.OAI.Problem367.IsingObservationFactor.kernel_markov _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_observationLaw_probability _root_.OAI.Problem367.IsingObservationInnovation.observationLaw_probability _root_.OAI.Problem367.TreeKoopman.labelProbability _root_.OAI.Problem367.freeIsingMeasure_probability
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

end Problem367

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
-- module Solutions.Q243_FreeIsing.FreeIsing_Ising_ContinuousCovarianceIntegral
attribute [-instance] _root_.OAI.Problem367.IsingConditionalCopyBounds.graphLaw_isProbabilityMeasure _root_.OAI.Problem367.IsingObservationFactor.copies_probability _root_.OAI.Problem367.IsingObservationFactor.kernel_markov _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_observationLaw_probability _root_.OAI.Problem367.IsingObservationInnovation.observationLaw_probability _root_.OAI.Problem367.TreeKoopman.labelProbability
attribute [-simp] _root_.OAI.Problem367.CutContinuationChannels.averageChannel_globalCone _root_.OAI.Problem367.CutContinuationChannels.continuationChannel_globalCone _root_.OAI.Problem367.FactorObservable.centeredSpinLp_coe _root_.OAI.Problem367.FiniteIsingSplit.splitEquiv_fst _root_.OAI.Problem367.FiniteIsingSplit.splitEquiv_snd _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_apply _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_uniformObservation _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_zero _root_.OAI.Problem367.IsingObservationInnovation.uniformObservation_relabel _root_.OAI.Problem367.IsingOrientedPath.attenuation_outward _root_.OAI.Problem367.IsingOrientedPath.endpoint_extensionAt _root_.OAI.Problem367.LocalSupportGeometry.prefixVertex_length _root_.OAI.Problem367.PathSideBranches.parent_sideVertex _root_.OAI.Problem367.PathSideBranches.restrictNoisyRegion_array _root_.OAI.Problem367.PathSideBranches.sideVertex_length _root_.OAI.Problem367.PathSideBranches.sideVertex_val _root_.OAI.Problem367.TreeConeCoding.length_vertex _root_.OAI.Problem367.TreeConeCoding.vertex_nil _root_.OAI.Problem367.TreeConeCoding.vertex_val _root_.OAI.Problem367.TreeKoopman.centeredAverage_apply_coe _root_.OAI.Problem367.TreeKoopman.centeredAverage_pow_apply_coe _root_.OAI.Problem367.TreeKoopman.centeredGenerator_apply_coe _root_.OAI.Problem367.TreeKoopman.centeredGenerator_sq _root_.OAI.Problem367.TreeKoopman.generatorOperator_sq _root_.OAI.Problem367.TreeKoopman.reverseVertex_twice _root_.OAI.Problem367.TreeKoopman.wordRelabel_cons _root_.OAI.Problem367.TreeKoopman.wordRelabel_nil _root_.OAI.Problem367.TreeLawKoopman.centeredAverage_apply_coe _root_.OAI.Problem367.TreeLawKoopman.generatorOperator_sq _root_.OAI.Problem367.dropVertex_length _root_.OAI.Problem367.dropVertex_val _root_.OAI.Problem367.mem_rootComplementFinset _root_.OAI.Problem367.mem_rootComponentFinset _root_.OAI.Problem367.mem_rootComponentIndices _root_.OAI.Problem367.prefixColorAut_length _root_.OAI.Problem367.prefixColorAut_val _root_.OAI.Problem367.prefixColorMap_symm_apply _root_.OAI.Problem367.spinSign_flip
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped NNReal Topology BigOperators

namespace Problem367.IsingInnovation

variable {d : ℕ} {A : Type*} [MeasurableSpace A]

theorem exists_continuous_covariance_integral_oai
    (hd : 3 ≤ d) {beta : ℝ} {μ : Measure (TreeVertex d → IsingSpin)}
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hb : 0 ≤ beta)
    (hcrit : ((d - 1 : ℕ) : ℝ) * Real.tanh beta ^ 2 ≤ 1)
    (ν : Measure A) {B : ℝ≥0 → A → ℝ} (hB : IsPreBrownianReal B ν)
    (hmB : ∀ t, Measurable (B t)) (hcB : ∀ a, Continuous (fun t => B t a))
    (v : TreeVertex d) :
    let P := μ.prod (Measure.infinitePi (fun _ : TreeVertex d => ν))
    let F := ArrayPosteriorStationarity.filtration B hmB
    ∃ (I : ℕ → TreeVertex d → ℝ≥0 → State d A → ℝ)
      (Y : ℕ → ℝ≥0 → State d A → ℝ) (Z : ℝ≥0 → State d A → ℝ)
      (hI2 : ∀ n u t, MemLp (I n u t) 2 P)
      (hY2 : ∀ n t, MemLp (Y n t) 2 P) (_hZ2 : ∀ t, MemLp (Z t) 2 P),
      (∀ n, IsStronglyPredictable F (Y n) ∧ Martingale (Y n) F P ∧
        (∀ᵐ q ∂P, Continuous (fun t => Y n t q))) ∧
      (∀ n u (N : ℕ), 0 < N → Tendsto (fun k => ∫ q,
        (BrownianGrid.uniformSum (innovation beta B u) (finiteCovariance beta B v u n)
          N k q - I n u N q) ^ 2 ∂P) atTop (𝓝 0)) ∧
      (∀ n t, HasSum (fun u => (hI2 n u t).toLp (I n u t))
        ((hY2 n t).toLp (Y n t))) ∧
      (∀ n t, (∫ q, Y n t q ^ 2 ∂P) =
        ∑' u, ∫ s in (0 : ℝ)..(t : ℝ),
          ∫ q, finiteCovariance beta B v u n s.toNNReal q ^ 2 ∂P) ∧
      (∀ n m (N : ℕ), 0 < N → (∫ q, (Y n N q - Y m N q) ^ 2 ∂P) =
        ∑' u, ∫ s in (0 : ℝ)..(N : ℝ), ∫ q,
          (finiteCovariance beta B v u n s.toNNReal q -
            finiteCovariance beta B v u m s.toNNReal q) ^ 2 ∂P) ∧
      IsStronglyPredictable F Z ∧ Martingale Z F P ∧
      (∀ᵐ q ∂P, Continuous (fun t => Z t q)) ∧ Z 0 =ᵐ[P] 0 ∧
      (∀ t, (∫ q, Z t q ∂P) = 0) ∧
      (∀ t, Tendsto (fun n => ∫ q, (Y n t q - Z t q) ^ 2 ∂P) atTop (𝓝 0)) ∧
      (∀ t : ℝ≥0, Tendsto (fun n => ∑' u, ∫ s in (0 : ℝ)..(t : ℝ),
        ∫ q, finiteCovariance beta B v u n s.toNNReal q ^ 2 ∂P) atTop
          (𝓝 (∫ q, Z t q ^ 2 ∂P))) ∧
      (∀ T, Tendsto (fun n => ∫ q,
        MartingaleStrongMaximal.maximalSquare (Y n - Z) T q ∂P) atTop (𝓝 0)) := by
  let : IsProbabilityMeasure μ := hμ.isProbabilityMeasure
  let : IsProbabilityMeasure ν := hB.isGaussianProcess.isProbabilityMeasure
  let P := μ.prod (Measure.infinitePi (fun _ : TreeVertex d => ν))
  have hW (u : TreeVertex d) := isBrownianReal_innovation hμ ν hB hmB hcB u
  have hAd (u : TreeVertex d) :=
    (innovation_martingale hμ ν hB hmB hcB u).stronglyAdapted
  have hcross (s t : ℝ≥0) (hst : s ≤ t) : Pairwise fun u w =>
      IndepFun (fun q => innovation beta B u t q - innovation beta B u s q)
        (fun q => innovation beta B w t q - innovation beta B w s q) P := by
    intro u w huw
    exact (innovation_increment_law_and_indep hμ ν hB hmB hcB
      (Y := fun _ => ()) s t hst measurable_const).2.1.indepFun huw
  have hrow (N : ℕ) := finiteCovariance_fullTime_interval_energy_cauchy
    hd hμ hb hcrit ν hB hmB hcB v (Nat.cast_nonneg N)
  exact BrownianArrayFiltration.exists_global_continuous_integral_limit_of_row_energy_cauchy
    (fun u => (hW u).toIsPreBrownianReal) hAd
    (innovation_increment_indep_filtration hμ ν hB hmB hcB) hcross
    (fun u => (hW u).cont)
    (fun n u => finiteCovariance beta B v u n)
    (fun n u => finiteCovariance_stronglyAdapted beta B hmB v u n)
    (fun n u => Eventually.of_forall (finiteCovariance_continuous beta B hcB v u n))
    (fun _ _ => 2) (fun _ _ => by norm_num)
    (fun n u => Eventually.of_forall (fun q t => finiteCovariance_abs_le_two beta B v u n t q))
    (fun n N => (hrow N).1 n) (fun N _hN => (hrow N).2.2)

end Problem367.IsingInnovation

end

end OAI
end

theorem solution.{u_1} : type_of% @OAI.Problem367.IsingInnovation.exists_continuous_covariance_integral_oai.{u_1} := @OAI.Problem367.IsingInnovation.exists_continuous_covariance_integral_oai.{u_1}
