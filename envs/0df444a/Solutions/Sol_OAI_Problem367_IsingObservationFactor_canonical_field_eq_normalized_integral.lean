-- Prove2me | solution 1 for OAI.Problem367.IsingObservationFactor.canonical_field_eq_normalized_integral
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T01:48:01.41803+00:00
-- url     : https://prove2.me/submissions/1cecc9d0-eadd-4e15-b378-3db7e5faa7e7

import Mathlib
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.MeasureTheory.Integral.Marginal
import Mathlib.Probability.Martingale.Basic
import Mathlib.Probability.Process.Stopping
import Definitions.Def_FreeIsing
import Definitions.Def_Q243FI005
import Theorems.Thm_OAI_Problem367_IsingInnovation_exists_continuous_posterior
import Theorems.Thm_OAI_Problem367_IsingObservationFactor_canonicalPosteriorExit_localizing
import Theorems.Thm_OAI_Problem367_IsingObservationFactor_canonicalResponseDrift_primitive_continuous
import Theorems.Thm_OAI_Problem367_IsingObservationFactor_canonical_stopped_field_eq_of_integral_limits
import Theorems.Thm_OAI_Problem367_IsingObservationFactor_exists_canonical_root_covariance_integral_representation

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
-- module Solutions.Q243_FreeIsing.FreeIsing_Brownian_GridRefinement
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace Problem367.BrownianGrid

lemma sum_range_blocks {E : Type*} [AddCommMonoid E] (f : ℕ → E) (n k : ℕ) :
    ∑ i ∈ Finset.range (n * k), f i =
      ∑ j ∈ Finset.range n, ∑ l ∈ Finset.range k, f (j * k + l) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Nat.succ_mul, Finset.sum_range_add, ih, Finset.sum_range_succ]

lemma weighted_sum_refinement (x H : ℕ → ℝ) (n : ℕ) {k : ℕ} (hk : 0 < k) :
    (∑ j ∈ Finset.range n, H j * (x ((j + 1) * k) - x (j * k))) =
      ∑ i ∈ Finset.range (n * k), H (i / k) * (x (i + 1) - x i) := by
  rw [sum_range_blocks]
  apply Finset.sum_congr rfl
  intro j hj
  calc
    H j * (x ((j + 1) * k) - x (j * k)) =
        H j * (∑ l ∈ Finset.range k, (x (j * k + (l + 1)) - x (j * k + l))) := by
      rw [Finset.sum_range_sub (fun l => x (j * k + l)) k]
      simp [Nat.add_mul]
    _ = ∑ l ∈ Finset.range k, H j * (x (j * k + (l + 1)) - x (j * k + l)) :=
      Finset.mul_sum _ _ _
    _ = _ := by
      apply Finset.sum_congr rfl
      intro l hl
      have hdiv : (j * k + l) / k = j := by
        rw [Nat.mul_comm j k, Nat.mul_add_div hk, Nat.div_eq_of_lt (Finset.mem_range.mp hl)]
        omega
      rw [hdiv]
      congr 3

theorem integralSum_refinement {Ω : Type*} (B : ℝ≥0 → Ω → ℝ)
    (t : ℕ → ℝ≥0) (H : ℕ → Ω → ℝ) (n : ℕ) {k : ℕ} (hk : 0 < k) :
    integralSum B (fun j => t (j * k)) H n =
      integralSum B t (fun i => H (i / k)) (n * k) := by
  funext ω
  exact weighted_sum_refinement (fun i => B (t i) ω) (fun i => H i ω) n hk

end Problem367.BrownianGrid

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

lemma uniformGrid_refine (T : ℝ≥0) {n k : ℕ} (hn : 0 < n) (hk : 0 < k)
    (j : ℕ) : uniformGrid T (n * k) (j * k) = uniformGrid T n j := by
  have hn0 : (n : ℝ≥0) ≠ 0 := by exact_mod_cast (ne_of_gt hn)
  have hk0 : (k : ℝ≥0) ≠ 0 := by exact_mod_cast (ne_of_gt hk)
  simp only [uniformGrid, Nat.cast_mul]
  field_simp

lemma uniformGrid_le_horizon (T : ℝ≥0) {n i : ℕ} (hn : 0 < n) (hi : i ≤ n) :
    uniformGrid T n i ≤ T := by
  simpa only [uniformGrid_end T hn] using uniformGrid_mono T n hi

lemma uniformGrid_floor_le (T : ℝ≥0) {n k : ℕ} (hn : 0 < n) (hk : 0 < k)
    (i : ℕ) : uniformGrid T n (i / k) ≤ uniformGrid T (n * k) i := by
  rw [← uniformGrid_refine T hn hk]
  exact uniformGrid_mono T (n * k) (Nat.div_mul_le_self i k)

lemma uniformGrid_floor_sub_le (T : ℝ≥0) {n k : ℕ} (hn : 0 < n) (hk : 0 < k)
    (i : ℕ) :
    (uniformGrid T (n * k) i : ℝ) - (uniformGrid T n (i / k) : ℝ) ≤
      (T : ℝ) / (n : ℝ) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk
  have hindex : i ≤ (i / k) * k + k := by
    have hmod := Nat.mod_lt i hk
    have hdecomp := Nat.mod_add_div i k
    rw [Nat.mul_comm k (i / k)] at hdecomp
    omega
  have hiR : (i : ℝ) ≤ (i / k : ℕ) * (k : ℝ) + (k : ℝ) := by exact_mod_cast hindex
  simp only [uniformGrid, NNReal.coe_div, NNReal.coe_mul, NNReal.coe_natCast, Nat.cast_mul]
  apply (sub_le_iff_le_add).2
  apply (div_le_iff₀ (mul_pos hnR hkR)).2
  field_simp
  nlinarith [mul_le_mul_of_nonneg_right hiR T.coe_nonneg]

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
-- module Solutions.Q243_FreeIsing.FreeIsing_Estimates_MeanSquareContinuity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Filter Set
open scoped NNReal Topology

namespace Problem367.MeanSquareContinuity

theorem discrepancy_nonneg {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (u : ℝ≥0 → Ω → ℝ) (s t : ℝ≥0) :
    0 ≤ discrepancy P u s t := integral_nonneg (fun _ => sq_nonneg _)

theorem continuous_discrepancy {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsFiniteMeasure P] {u : ℝ≥0 → Ω → ℝ}
    (hm : ∀ t, AEStronglyMeasurable (u t) P)
    (hc : ∀ᵐ ω ∂P, Continuous (fun t => u t ω))
    {C : ℝ} (hC : 0 ≤ C) (hb : ∀ᵐ ω ∂P, ∀ t, |u t ω| ≤ C) :
    Continuous (fun p : ℝ≥0 × ℝ≥0 => discrepancy P u p.1 p.2) := by
  apply continuous_of_dominated (bound := fun _ => (2 * C) ^ 2)
  · intro p
    exact ((hm p.1).sub (hm p.2)).pow 2
  · intro p
    filter_upwards [hb] with ω hω
    have hn : |u p.1 ω - u p.2 ω| ≤ 2 * C :=
      (abs_sub _ _).trans (by linarith [hω p.1, hω p.2])
    simpa only [Real.norm_eq_abs, abs_sq, sq_abs] using
      (sq_le_sq₀ (abs_nonneg _) (mul_nonneg (by norm_num) hC)).mpr hn
  · exact integrable_const _
  · filter_upwards [hc] with ω hω
    exact ((hω.comp continuous_fst).sub (hω.comp continuous_snd)).pow 2

theorem uniform_discrepancy_small {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsFiniteMeasure P] {u : ℝ≥0 → Ω → ℝ}
    (hm : ∀ t, AEStronglyMeasurable (u t) P)
    (hc : ∀ᵐ ω ∂P, Continuous (fun t => u t ω))
    {C : ℝ} (hC : 0 ≤ C) (hb : ∀ᵐ ω ∂P, ∀ t, |u t ω| ≤ C)
    (T : ℝ≥0) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > 0, ∀ s ∈ Icc (0 : ℝ≥0) T, ∀ t ∈ Icc (0 : ℝ≥0) T,
      dist s t < δ → discrepancy P u s t < ε := by
  have hcompact : IsCompact ((Icc (0 : ℝ≥0) T) ×ˢ (Icc (0 : ℝ≥0) T)) :=
    isCompact_Icc.prod isCompact_Icc
  have hUC := hcompact.uniformContinuousOn_of_continuous
    (continuous_discrepancy hm hc hC hb).continuousOn
  obtain ⟨δ, hδ, hsmall⟩ := Metric.uniformContinuousOn_iff.mp hUC ε hε
  refine ⟨δ, hδ, ?_⟩
  intro s hs t ht hst
  have hh := hsmall (s, t) ⟨hs, ht⟩ (t, t) ⟨ht, ht⟩
    (by simpa only [Prod.dist_eq, dist_self, max_eq_left (dist_nonneg)] using hst)
  simpa only [discrepancy_self, Real.dist_eq, sub_zero,
    abs_of_nonneg (discrepancy_nonneg P u s t)] using hh

theorem uniform_integral_sq_sub_le {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsFiniteMeasure P] {u : ℝ≥0 → Ω → ℝ}
    (hm : ∀ t, AEStronglyMeasurable (u t) P)
    (hc : ∀ᵐ ω ∂P, Continuous (fun t => u t ω))
    {C : ℝ} (hC : 0 ≤ C) (hb : ∀ᵐ ω ∂P, ∀ t, |u t ω| ≤ C)
    (T : ℝ≥0) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > 0, ∀ s t : ℝ≥0, s ≤ t → t ≤ T →
      (t : ℝ) - (s : ℝ) ≤ δ → (∫ ω, (u s ω - u t ω) ^ 2 ∂P) ≤ ε := by
  obtain ⟨δ, hδ, hsmall⟩ := uniform_discrepancy_small hm hc hC hb T hε
  refine ⟨δ / 2, half_pos hδ, ?_⟩
  intro s t hst ht hd
  apply (hsmall s ⟨bot_le, hst.trans ht⟩ t ⟨bot_le, ht⟩ ?_).le
  rw [NNReal.dist_eq, abs_of_nonpos (sub_nonpos.mpr (show (s : ℝ) ≤ t from hst))]
  linarith

end Problem367.MeanSquareContinuity

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

end Problem367

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

theorem preBrownian_difference_isometry
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {B : ℝ≥0 → Ω → ℝ} (hB : IsPreBrownianReal B P)
    {F : Filtration ℝ≥0 mΩ} (hAd : StronglyAdapted F B)
    (hind : ∀ s t, s ≤ t → Indep
      (MeasurableSpace.comap (fun ω => B t ω - B s ω) inferInstance) (F s) P)
    (t : ℕ → ℝ≥0) (ht : Monotone t) (H K : ℕ → Ω → ℝ)
    {k : ℕ} (hk : 0 < k)
    (hH : ∀ j, StronglyMeasurable[F (t (j * k))] (H j))
    (hK : ∀ i, StronglyMeasurable[F (t i)] (K i))
    (hH2 : ∀ j, MemLp (H j) 2 P) (hK2 : ∀ i, MemLp (K i) 2 P) (n : ℕ) :
    (∫ ω, (integralSum B (fun j => t (j * k)) H n ω -
      integralSum B t K (n * k) ω) ^ 2 ∂P) =
      ∑ i ∈ Finset.range (n * k), ((t (i + 1) : ℝ) - (t i : ℝ)) *
        ∫ ω, (H (i / k) ω - K i ω) ^ 2 ∂P := by
  rw [integralSum_refinement B t H n hk]
  simpa only [integralSum, sub_mul, Finset.sum_sub_distrib] using
    BrownianFiltration.predictable_sum_isometry hB hAd hind t ht
    (fun i ω => H (i / k) ω - K i ω)
    (fun i => ((hH (i / k)).mono (F.mono (ht (Nat.div_mul_le_self i k)))).sub (hK i))
    (fun i => (hH2 (i / k)).sub (hK2 i)) (Finset.range (n * k))

theorem preBrownian_uniform_difference_isometry
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {B : ℝ≥0 → Ω → ℝ} (hB : IsPreBrownianReal B P)
    {F : Filtration ℝ≥0 mΩ} (hAd : StronglyAdapted F B)
    (hind : ∀ s t, s ≤ t → Indep
      (MeasurableSpace.comap (fun ω => B t ω - B s ω) inferInstance) (F s) P) (H : ℝ≥0 → Ω → ℝ)
    (hH : StronglyAdapted (F) H)
    (hH2 : ∀ t, MemLp (H t) 2 P)
    (T : ℝ≥0) {n k : ℕ} (hn : 0 < n) (hk : 0 < k) :
    (∫ ω, (uniformSum B H T n ω - uniformSum B H T (n * k) ω) ^ 2 ∂P) =
      ∑ i ∈ Finset.range (n * k),
        ((uniformGrid T (n * k) (i + 1) : ℝ) - (uniformGrid T (n * k) i : ℝ)) *
          ∫ ω, (H (uniformGrid T n (i / k)) ω - H (uniformGrid T (n * k) i) ω) ^ 2 ∂P := by
  have hgrid : (fun j => uniformGrid T (n * k) (j * k)) = uniformGrid T n := by
    funext j
    exact uniformGrid_refine T hn hk j
  have hcoeff : ∀ j, StronglyMeasurable[
      F (uniformGrid T (n * k) (j * k))]
      (H (uniformGrid T n j)) := by
    intro j
    rw [uniformGrid_refine T hn hk]
    exact hH _
  simpa only [hgrid, uniformSum] using preBrownian_difference_isometry hB hAd hind
    (uniformGrid T (n * k)) (uniformGrid_mono T (n * k))
    (fun j => H (uniformGrid T n j)) (fun i => H (uniformGrid T (n * k) i)) hk
    hcoeff (fun i => hH _) (fun j => hH2 _) (fun i => hH2 _) n

theorem preBrownian_uniform_difference_bound
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {B : ℝ≥0 → Ω → ℝ} (hB : IsPreBrownianReal B P)
    {F : Filtration ℝ≥0 mΩ} (hAd : StronglyAdapted F B)
    (hind : ∀ s t, s ≤ t → Indep
      (MeasurableSpace.comap (fun ω => B t ω - B s ω) inferInstance) (F s) P) (H : ℝ≥0 → Ω → ℝ)
    (hH : StronglyAdapted (F) H)
    (hH2 : ∀ t, MemLp (H t) 2 P)
    (T : ℝ≥0) {n k : ℕ} (hn : 0 < n) (hk : 0 < k) {ε : ℝ}
    (happrox : ∀ i < n * k,
      (∫ ω, (H (uniformGrid T n (i / k)) ω -
        H (uniformGrid T (n * k) i) ω) ^ 2 ∂P) ≤ ε) :
    (∫ ω, (uniformSum B H T n ω - uniformSum B H T (n * k) ω) ^ 2 ∂P) ≤
      (T : ℝ) * ε := by
  rw [preBrownian_uniform_difference_isometry hB hAd hind H hH hH2 T hn hk]
  calc
    _ ≤ ∑ i ∈ Finset.range (n * k),
        ((uniformGrid T (n * k) (i + 1) : ℝ) - (uniformGrid T (n * k) i : ℝ)) * ε := by
      apply Finset.sum_le_sum
      intro i hi
      apply mul_le_mul_of_nonneg_left (happrox i (Finset.mem_range.mp hi))
      exact sub_nonneg.mpr (NNReal.coe_le_coe.mpr (uniformGrid_mono T (n * k) (Nat.le_succ i)))
    _ = (T : ℝ) * ε := by
      rw [← Finset.sum_mul, Finset.sum_range_sub (fun i => (uniformGrid T (n * k) i : ℝ))]
      simp [uniformGrid_end T (Nat.mul_pos hn hk)]

theorem preBrownian_uniform_difference_bound_of_modulus
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {B : ℝ≥0 → Ω → ℝ} (hB : IsPreBrownianReal B P)
    {F : Filtration ℝ≥0 mΩ} (hAd : StronglyAdapted F B)
    (hind : ∀ s t, s ≤ t → Indep
      (MeasurableSpace.comap (fun ω => B t ω - B s ω) inferInstance) (F s) P) (H : ℝ≥0 → Ω → ℝ)
    (hH : StronglyAdapted (F) H)
    (hH2 : ∀ t, MemLp (H t) 2 P)
    (T : ℝ≥0) {n k : ℕ} (hn : 0 < n) (hk : 0 < k) {ε δ : ℝ}
    (hmesh : (T : ℝ) / (n : ℝ) ≤ δ)
    (hmod : ∀ s t : ℝ≥0, s ≤ t → t ≤ T → (t : ℝ) - (s : ℝ) ≤ δ →
      (∫ ω, (H s ω - H t ω) ^ 2 ∂P) ≤ ε) :
    (∫ ω, (uniformSum B H T n ω - uniformSum B H T (n * k) ω) ^ 2 ∂P) ≤
      (T : ℝ) * ε := by
  apply preBrownian_uniform_difference_bound hB hAd hind H hH hH2 T hn hk
  intro i hi
  apply hmod
  · exact uniformGrid_floor_le T hn hk i
  · exact uniformGrid_le_horizon T (Nat.mul_pos hn hk) hi.le
  · exact (uniformGrid_floor_sub_le T hn hk i).trans hmesh

theorem preBrownian_uniform_pair_bound
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {B : ℝ≥0 → Ω → ℝ} (hB : IsPreBrownianReal B P)
    {F : Filtration ℝ≥0 mΩ} (hAd : StronglyAdapted F B)
    (hind : ∀ s t, s ≤ t → Indep
      (MeasurableSpace.comap (fun ω => B t ω - B s ω) inferInstance) (F s) P) (H : ℝ≥0 → Ω → ℝ)
    (hH : StronglyAdapted (F) H)
    (hH2 : ∀ t, MemLp (H t) 2 P)
    (T : ℝ≥0) {n m : ℕ} (hn : 0 < n) (hmn : 0 < m) {ε δ : ℝ}
    (hmeshN : (T : ℝ) / (n : ℝ) ≤ δ) (hmeshM : (T : ℝ) / (m : ℝ) ≤ δ)
    (hmod : ∀ s t : ℝ≥0, s ≤ t → t ≤ T → (t : ℝ) - (s : ℝ) ≤ δ →
      (∫ ω, (H s ω - H t ω) ^ 2 ∂P) ≤ ε) :
    (∫ ω, (uniformSum B H T n ω - uniformSum B H T m ω) ^ 2 ∂P) ≤
      4 * (T : ℝ) * ε := by
  have hN := preBrownian_uniform_difference_bound_of_modulus hB hAd hind H hH hH2 T hn hmn hmeshN hmod
  have hM := preBrownian_uniform_difference_bound_of_modulus hB hAd hind H hH hH2 T hmn hn hmeshM hmod
  rw [Nat.mul_comm m n] at hM
  have htriangle := integral_sq_sub_le_two (uniformSum_memLp hB hAd hind H hH hH2 T n)
    (uniformSum_memLp hB hAd hind H hH hH2 T m) (uniformSum_memLp hB hAd hind H hH hH2 T (n * m))
  linarith

end Problem367.BrownianFiltrationGrid

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Stochastic_StoppedBrownianIntegral
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

theorem martingale_of_independent_past
    (hB : IsPreBrownianReal B P) (hAd : StronglyAdapted F B)
    (hind : ∀ s t, s ≤ t → Indep
      (MeasurableSpace.comap (fun ω => B t ω - B s ω) inferInstance) (F s) P) :
    Martingale B F P := by
  let : IsProbabilityMeasure P := hB.isGaussianProcess.isProbabilityMeasure
  refine ⟨hAd, ?_⟩
  intro s t hst
  have hsub := condExp_sub (hB.integrable_eval t) (hB.integrable_eval s) (F s)
  have hself := condExp_of_stronglyMeasurable (F.le s) (hAd s) (hB.integrable_eval s)
  filter_upwards [hsub, increment_condExp_zero hB hAd (hind s t hst)] with ω hs hz
  change P[(fun ω => B t ω - B s ω) | F s] ω =
    P[B t | F s] ω - P[B s | F s] ω at hs
  rw [hz, hself] at hs
  linarith

end Problem367.BrownianFiltration

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Martingales_PredictableMeshApproximation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Filter Set
open scoped NNReal Topology

namespace Problem367.PredictableMesh

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
-- module Solutions.Q243_FreeIsing.FreeIsing_Brownian_RationalHorizon
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Filter
open scoped NNReal Topology

namespace Problem367.BrownianIntegralProcess

variable {Ω : Type*}

theorem uniformGrid_mul_nat_horizon (T : ℝ≥0) {b : ℕ} (hb : 0 < b)
    (n i : ℕ) :
    BrownianGrid.uniformGrid ((b : ℝ≥0) * T) (b * n) i =
      BrownianGrid.uniformGrid T n i := by
  have hb0 : (b : ℝ≥0) ≠ 0 := by exact_mod_cast hb.ne'
  by_cases hn : n = 0
  · simp [hn, BrownianGrid.uniformGrid]
  · have hn0 : (n : ℝ≥0) ≠ 0 := by exact_mod_cast hn
    simp only [BrownianGrid.uniformGrid, Nat.cast_mul]
    field_simp

theorem stoppedUniformSum_mul_nat_horizon (B H : ℝ≥0 → Ω → ℝ)
    (T : ℝ≥0) {b : ℕ} (hb : 0 < b) (n : ℕ) {t : ℝ≥0} (ht : t ≤ T) :
    stoppedUniformSum B H ((b : ℝ≥0) * T) (b * n) t =
      stoppedUniformSum B H T n t := by
  have hg : BrownianGrid.uniformGrid ((b : ℝ≥0) * T) (b * n) =
      BrownianGrid.uniformGrid T n := by
    funext i
    exact uniformGrid_mul_nat_horizon T hb n i
  by_cases hn : n = 0
  · funext ω
    simp [hn, stoppedUniformSum]
  · have hnpos : 0 < n := Nat.pos_of_ne_zero hn
    funext ω
    simp only [stoppedUniformSum, hg]
    symm
    apply Finset.sum_subset (Finset.range_mono (by nlinarith : n ≤ b * n))
    intro i hi hni
    have hindex : n ≤ i := Nat.le_of_not_gt (fun h => hni (Finset.mem_range.mpr h))
    have hta : t ≤ BrownianGrid.uniformGrid T n i :=
      ht.trans ((BrownianGrid.uniformGrid_end T hnpos).symm.le.trans
        (BrownianGrid.uniformGrid_mono T n hindex))
    have htb : t ≤ BrownianGrid.uniformGrid T n (i + 1) :=
      hta.trans (BrownianGrid.uniformGrid_mono T n (Nat.le_succ i))
    simp only [StoppedSimpleIntegral.intervalSum, min_eq_left hta,
      min_eq_left htb, sub_self, mul_zero]

theorem uniformSum_nat_div_eq_stopped (B H : ℝ≥0 → Ω → ℝ)
    (a : ℕ) {b : ℕ} (hb : 0 < b) (n : ℕ) :
    BrownianGrid.uniformSum B H ((a : ℝ≥0) / b) n =
      stoppedUniformSum B H a (b * n) ((a : ℝ≥0) / b) := by
  have hb0 : (b : ℝ≥0) ≠ 0 := by exact_mod_cast hb.ne'
  have he : (b : ℝ≥0) * ((a : ℝ≥0) / b) = a := by field_simp
  rw [← stoppedUniformSum_terminal]
  exact (he ▸ stoppedUniformSum_mul_nat_horizon B H
    ((a : ℝ≥0) / b) hb n le_rfl).symm

theorem tendsto_uniformSum_nat_div_of_integer_limits
    [MeasurableSpace Ω] {P : Measure Ω} {B H I : ℝ≥0 → Ω → ℝ}
    (hlim : ∀ (N : ℕ), 0 < N → ∀ t ≤ (N : ℝ≥0),
      Tendsto (fun n => ∫ ω,
        (stoppedUniformSum B H N n t ω - I t ω) ^ 2 ∂P) atTop (𝓝 0))
    {a b : ℕ} (ha : 0 < a) (hb : 0 < b) :
    Tendsto (fun n => ∫ ω,
      (BrownianGrid.uniformSum B H ((a : ℝ≥0) / b) n ω -
        I ((a : ℝ≥0) / b) ω) ^ 2 ∂P) atTop (𝓝 0) := by
  have hbone : (1 : ℝ≥0) ≤ b := by exact_mod_cast hb
  have ht : (a : ℝ≥0) / b ≤ a := div_le_self (by positivity) hbone
  have hcofinal : Tendsto (fun n : ℕ => b * n) atTop atTop := by
    apply tendsto_atTop_mono (fun n => ?_) tendsto_id
    change n ≤ b * n
    have hbn : 1 ≤ b := hb
    simpa only [one_mul] using Nat.mul_le_mul_right n hbn
  simpa only [uniformSum_nat_div_eq_stopped B H a hb, Function.comp_def] using
    (hlim a ha ((a : ℝ≥0) / b) ht).comp hcofinal

theorem tendsto_uniformSum_pos_rat_of_integer_limits
    [MeasurableSpace Ω] {P : Measure Ω} {B H I : ℝ≥0 → Ω → ℝ}
    (hlim : ∀ (N : ℕ), 0 < N → ∀ t ≤ (N : ℝ≥0),
      Tendsto (fun n => ∫ ω,
        (stoppedUniformSum B H N n t ω - I t ω) ^ 2 ∂P) atTop (𝓝 0))
    (q : ℚ) (hq : 0 < q) :
    Tendsto (fun n => ∫ ω,
      (BrownianGrid.uniformSum B H (q : ℝ).toNNReal n ω -
        I (q : ℝ).toNNReal ω) ^ 2 ∂P) atTop (𝓝 0) := by
  have hnum : 0 < q.num := Rat.num_pos.mpr hq
  have hqR : 0 ≤ (q : ℝ) := by exact_mod_cast hq.le
  have hcast : (q.num.toNat : ℝ) = (q.num : ℝ) := by
    exact_mod_cast Int.toNat_of_nonneg hnum.le
  have he : (q : ℝ).toNNReal = (q.num.toNat : ℝ≥0) / q.den := by
    apply NNReal.eq
    simp only [Real.coe_toNNReal _ hqR, NNReal.coe_div, NNReal.coe_natCast]
    rw [Rat.cast_def, hcast]
  rw [he]
  exact tendsto_uniformSum_nat_div_of_integer_limits hlim
    (by omega) q.pos

end Problem367.BrownianIntegralProcess

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

theorem integrable_maximalSquare [IsFiniteMeasure μ]
    {F : Filtration ℝ≥0 mΩ} {M : ℝ≥0 → Ω → ℝ}
    (hM : Martingale M F μ) (h2 : ∀ t, MemLp (M t) 2 μ)
    (hc : ∀ᵐ ω ∂μ, Continuous (fun t => M t ω)) (T : ℝ≥0) :
    Integrable (maximalSquare M T) μ :=
  integrable_toReal_of_lintegral_ne_top (supremumSq_aemeasurable h2 hc T)
    (ne_top_of_le_ne_top ENNReal.ofReal_ne_top (continuous_martingale_maximal_sq hM h2 hc T))

theorem ae_all_sq_le_maximalSquare [IsFiniteMeasure μ]
    {F : Filtration ℝ≥0 mΩ} {M : ℝ≥0 → Ω → ℝ}
    (hM : Martingale M F μ) (h2 : ∀ t, MemLp (M t) 2 μ)
    (hc : ∀ᵐ ω ∂μ, Continuous (fun t => M t ω)) (T : ℝ≥0) :
    ∀ᵐ ω ∂μ, ∀ t ≤ T, M t ω ^ 2 ≤ maximalSquare M T ω := by
  filter_upwards [ae_supremumSq_lt_top hM h2 hc T] with ω hω
  intro t ht
  have hle : ENNReal.ofReal (M t ω ^ 2) ≤ supremumSq M T ω :=
    le_iSup_of_le ⟨t, ht⟩ le_rfl
  simpa only [ENNReal.toReal_ofReal (sq_nonneg _), maximalSquare] using
    ENNReal.toReal_mono hω.ne hle

end Problem367.MartingaleStrongMaximal

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Brownian_UniformErrorContinuity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Filter Set
open scoped NNReal Topology

namespace Problem367.BrownianUniformErrorContinuity

open BrownianGrid MartingaleStrongMaximal

theorem uniformSum_sq_le {Ω : Type*} (B H : ℝ≥0 → Ω → ℝ)
    {ω : Ω} {T N : ℝ≥0} (hTN : T ≤ N) {C R : ℝ}
    (hC : 0 ≤ C) (hB : ∀ t ≤ N, B t ω ^ 2 ≤ R)
    (hH : ∀ t, |H t ω| ≤ C) (n : ℕ) :
    uniformSum B H T n ω ^ 2 ≤ 4 * (n : ℝ) ^ 2 * C ^ 2 * R := by
  let f : ℕ → ℝ := fun i => H (uniformGrid T n i) ω *
    (B (uniformGrid T n (i + 1)) ω - B (uniformGrid T n i) ω)
  have hterm (i : ℕ) (hi : i ∈ Finset.range n) : f i ^ 2 ≤ 4 * C ^ 2 * R := by
    have hin : i < n := Finset.mem_range.mp hi
    have hn : 0 < n := (Nat.zero_le i).trans_lt hin
    have ha := hB (uniformGrid T n i)
      ((uniformGrid_le_horizon T hn hin.le).trans hTN)
    have hb := hB (uniformGrid T n (i + 1))
      ((uniformGrid_le_horizon T hn (Nat.succ_le_of_lt hin)).trans hTN)
    have hcoef : H (uniformGrid T n i) ω ^ 2 ≤ C ^ 2 := by
      simpa only [sq_abs] using
        (sq_le_sq₀ (abs_nonneg _) hC).mpr (hH (uniformGrid T n i))
    have hinc : (B (uniformGrid T n (i + 1)) ω - B (uniformGrid T n i) ω) ^ 2 ≤ 4 * R := by
      nlinarith [sq_nonneg (B (uniformGrid T n (i + 1)) ω + B (uniformGrid T n i) ω)]
    calc
      f i ^ 2 = H (uniformGrid T n i) ω ^ 2 *
          (B (uniformGrid T n (i + 1)) ω - B (uniformGrid T n i) ω) ^ 2 := mul_pow _ _ _
      _ ≤ C ^ 2 * (4 * R) := mul_le_mul hcoef hinc (sq_nonneg _) (sq_nonneg _)
      _ = 4 * C ^ 2 * R := by ring
  calc
    uniformSum B H T n ω ^ 2 = (∑ i ∈ Finset.range n, f i) ^ 2 := rfl
    _ ≤ (n : ℝ) * ∑ i ∈ Finset.range n, f i ^ 2 := by
      simpa only [Finset.card_range] using
        (sq_sum_le_card_mul_sum_sq (s := Finset.range n) (f := f))
    _ ≤ (n : ℝ) * ∑ _i ∈ Finset.range n, 4 * C ^ 2 * R :=
      mul_le_mul_of_nonneg_left (Finset.sum_le_sum hterm) (Nat.cast_nonneg n)
    _ = 4 * (n : ℝ) ^ 2 * C ^ 2 * R := by simp <;> ring

theorem continuous_uniformSum_horizon {Ω : Type*} (B H : ℝ≥0 → Ω → ℝ)
    {ω : Ω} (hB : Continuous (fun t => B t ω))
    (hH : Continuous (fun t => H t ω)) (n : ℕ) :
    Continuous (fun T : ℝ≥0 => uniformSum B H T n ω) := by
  have hg (i : ℕ) : Continuous (fun T : ℝ≥0 => uniformGrid T n i) :=
    (continuous_id.const_mul (i : ℝ≥0)).div_const (n : ℝ≥0)
  unfold uniformSum integralSum
  apply continuous_finsetSum
  intro i _
  exact (hH.comp (hg i)).mul ((hB.comp (hg (i + 1))).sub (hB.comp (hg i)))

theorem continuousOn_uniformSum_meanSquare_error
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsFiniteMeasure P]
    {F : Filtration ℝ≥0 mΩ} {B H I : ℝ≥0 → Ω → ℝ}
    (hB : Martingale B F P) (hI : Martingale I F P)
    (hB2 : ∀ t, MemLp (B t) 2 P) (hI2 : ∀ t, MemLp (I t) 2 P)
    (hcB : ∀ᵐ ω ∂P, Continuous (fun t => B t ω))
    (hcI : ∀ᵐ ω ∂P, Continuous (fun t => I t ω))
    (hH : StronglyAdapted F H)
    (hcH : ∀ᵐ ω ∂P, Continuous (fun t => H t ω))
    {C : ℝ} (hC : 0 ≤ C) (hbH : ∀ᵐ ω ∂P, ∀ t, |H t ω| ≤ C)
    (n : ℕ) (N : ℝ≥0) :
    ContinuousOn (fun T : ℝ≥0 => ∫ ω,
      (uniformSum B H T n ω - I T ω) ^ 2 ∂P) (Icc 0 N) := by
  have hmS (T : ℝ≥0) : AEStronglyMeasurable (uniformSum B H T n) P := by
    unfold uniformSum integralSum
    have hs := Finset.aestronglyMeasurable_sum (Finset.range n) (fun i _ =>
      (((hH (uniformGrid T n i)).mono (F.le _)).aestronglyMeasurable).mul
        ((hB2 (uniformGrid T n (i + 1))).aestronglyMeasurable.sub
          (hB2 (uniformGrid T n i)).aestronglyMeasurable))
    convert hs using 1
    all_goals try with_reducible_and_instances rfl
    funext ω
    simp only [Finset.sum_apply, Pi.mul_apply, Pi.sub_apply]
  let D : Ω → ℝ := fun ω =>
    (8 * (n : ℝ) ^ 2 * C ^ 2) * maximalSquare B N ω + 2 * maximalSquare I N ω
  apply continuousOn_of_dominated (bound := D)
  · intro T _
    exact ((hmS T).sub (hI2 T).aestronglyMeasurable).pow 2
  · intro T hT
    filter_upwards [hbH, ae_all_sq_le_maximalSquare hB hB2 hcB N,
      ae_all_sq_le_maximalSquare hI hI2 hcI N] with ω hHω hBω hIω
    have hS := uniformSum_sq_le B H hT.2 hC hBω hHω n
    have hIt := hIω T hT.2
    rw [Real.norm_of_nonneg (sq_nonneg _)]
    dsimp [D]
    nlinarith [sq_nonneg (uniformSum B H T n ω + I T ω)]
  · exact ((integrable_maximalSquare hB hB2 hcB N).const_mul _).add
      ((integrable_maximalSquare hI hI2 hcI N).const_mul 2)
  · filter_upwards [hcB, hcH, hcI] with ω hBω hHω hIω
    exact (((continuous_uniformSum_horizon B H hBω hHω n).sub hIω).pow 2).continuousOn

end Problem367.BrownianUniformErrorContinuity

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Brownian_ArbitraryHorizon
attribute [-instance] _root_.OAI.Problem367.WienerSampler.pathMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal Topology
namespace Problem367.BrownianArbitraryHorizon

lemma continuousOn_le_of_pos_rat {f : ℝ≥0 → ℝ} {N T : ℝ≥0} {c : ℝ}
    (hf : ContinuousOn f (Icc 0 N)) (hTN : T < N)
    (hrat : ∀ q : ℚ, 0 < q → (q : ℝ).toNNReal ≤ N →
      f (q : ℝ).toNNReal ≤ c) : f T ≤ c := by
  obtain ⟨q, _, hq, hlim⟩ := Real.exists_seq_rat_strictAnti_tendsto (T : ℝ)
  have hqp (n : ℕ) : 0 < q n := by
    have hr : (0 : ℝ) < q n := lt_of_le_of_lt T.coe_nonneg (hq n)
    exact_mod_cast hr
  have hl : Tendsto (fun n => (q n : ℝ).toNNReal) atTop (𝓝 T) := by
    simpa only [Function.comp_def, Real.toNNReal_coe] using (continuous_real_toNNReal.tendsto (T : ℝ)).comp hlim
  have he : ∀ᶠ n in atTop, (q n : ℝ).toNNReal ∈ Icc 0 N := by
    filter_upwards [hl.eventually (gt_mem_nhds hTN)] with n hn
    exact ⟨zero_le, hn.le⟩
  have hwithin := tendsto_nhdsWithin_iff.mpr ⟨hl, he⟩
  apply le_of_tendsto ((hf T ⟨zero_le, hTN.le⟩).tendsto.comp hwithin)
  filter_upwards [he] with n hn
  exact hrat (q n) (hqp n) hn.2

theorem uniformSum_tendsto_of_rat_limits
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {B H I : ℝ≥0 → Ω → ℝ} {F : Filtration ℝ≥0 mΩ}
    (hB : IsPreBrownianReal B P) (hAd : StronglyAdapted F B)
    (hind : ∀ s t, s ≤ t → Indep
      (MeasurableSpace.comap (fun ω => B t ω - B s ω) inferInstance) (F s) P)
    (hH : StronglyAdapted F H)
    (hcH : ∀ᵐ ω ∂P, Continuous (fun t => H t ω))
    {C : ℝ} (hC : 0 ≤ C) (hbH : ∀ᵐ ω ∂P, ∀ t, |H t ω| ≤ C)
    (hI2 : ∀ t, MemLp (I t) 2 P)
    (hcont : ∀ n N, ContinuousOn (fun T : ℝ≥0 => ∫ ω,
      (BrownianGrid.uniformSum B H T n ω - I T ω) ^ 2 ∂P) (Icc 0 N))
    (hrat : ∀ q : ℚ, 0 < q → Tendsto (fun n => ∫ ω,
      (BrownianGrid.uniformSum B H (q : ℝ).toNNReal n ω - I (q : ℝ).toNNReal ω)^2 ∂P)
        atTop (𝓝 0)) (T : ℝ≥0) :
    Tendsto (fun n => ∫ ω, (BrownianGrid.uniformSum B H T n ω - I T ω)^2 ∂P)
      atTop (𝓝 0) := by
  let : IsProbabilityMeasure P := hB.isGaussianProcess.isProbabilityMeasure
  have hH2 (t : ℝ≥0) : MemLp (H t) 2 P :=
    MemLp.of_bound ((hH t).mono (F.le t)).aestronglyMeasurable C
      (hbH.mono (fun ω hω => hω t))
  have hS2 (t : ℝ≥0) (n : ℕ) : MemLp (BrownianGrid.uniformSum B H t n) 2 P :=
    BrownianFiltrationGrid.uniformSum_memLp hB hAd hind H hH hH2 t n
  let K : ℝ≥0 := T + 1
  have hTK : T < K := by dsimp [K]; exact lt_add_one T
  apply Metric.tendsto_atTop.mpr
  intro ε hε
  let η : ℝ := ε / (8 * (K : ℝ) + 1)
  have hden : 0 < 8 * (K : ℝ) + 1 := by positivity
  have hη : 0 < η := div_pos hε hden
  obtain ⟨δ, hδ, hmod⟩ := MeanSquareContinuity.uniform_integral_sq_sub_le
    (fun t => (hH2 t).aestronglyMeasurable) hcH hC hbH K hη
  obtain ⟨M, hM⟩ := exists_nat_gt ((K : ℝ) / δ)
  have hmesh (t : ℝ≥0) (ht : t ≤ K) (n : ℕ) (hn : M + 1 ≤ n) :
      (t : ℝ) / (n : ℝ) ≤ δ := by
    have hn0 : 0 < n := by omega
    have hnR : (0 : ℝ) < n := by exact_mod_cast hn0
    apply (div_le_iff₀ hnR).mpr
    have hM' : (K : ℝ) < (M : ℝ) * δ := (div_lt_iff₀ hδ).mp hM
    have hMn : (M : ℝ) ≤ (n : ℝ) := by exact_mod_cast (show M ≤ n by omega)
    have ht' : (t : ℝ) ≤ K := ht
    nlinarith
  have hpair (t : ℝ≥0) (ht : t ≤ K) (n m : ℕ)
      (hn : M + 1 ≤ n) (hm : M + 1 ≤ m) :
      (∫ ω, (BrownianGrid.uniformSum B H t n ω -
        BrownianGrid.uniformSum B H t m ω)^2 ∂P) ≤ 4 * (K : ℝ) * η := by
    have hh := BrownianFiltrationGrid.preBrownian_uniform_pair_bound hB hAd hind H hH hH2 t
      (by omega : 0 < n) (by omega : 0 < m) (hmesh t ht n hn) (hmesh t ht m hm)
      (fun s r hsr hr hd => hmod s r hsr (hr.trans ht) hd)
    apply hh.trans
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (show (t : ℝ) ≤ K from ht) (by norm_num)) hη.le
  refine ⟨M + 1, ?_⟩
  intro n hn
  have hrbound (q : ℚ) (hq : 0 < q) (hqK : (q : ℝ).toNNReal ≤ K) :
      (∫ ω, (BrownianGrid.uniformSum B H (q : ℝ).toNNReal n ω -
        I (q : ℝ).toNNReal ω)^2 ∂P) ≤ 8 * (K : ℝ) * η := by
    have hlim : Tendsto (fun m => 8 * (K : ℝ) * η + 2 * ∫ ω,
        (BrownianGrid.uniformSum B H (q : ℝ).toNNReal m ω -
          I (q : ℝ).toNNReal ω)^2 ∂P) atTop (𝓝 (8 * (K : ℝ) * η)) := by
      simpa using tendsto_const_nhds.add ((hrat q hq).const_mul 2)
    apply le_of_tendsto_of_tendsto tendsto_const_nhds hlim
    filter_upwards [eventually_ge_atTop (M + 1)] with m hm
    have htri := BrownianGrid.integral_sq_sub_le_two
      (hS2 (q : ℝ).toNNReal n) (hI2 (q : ℝ).toNNReal) (hS2 (q : ℝ).toNNReal m)
    have hp := hpair (q : ℝ).toNNReal hqK n m hn hm
    simp only [sub_sq_comm (I (q : ℝ).toNNReal _) (BrownianGrid.uniformSum B H (q : ℝ).toNNReal m _)] at htri
    linarith
  have hb := continuousOn_le_of_pos_rat (hcont n K) hTK hrbound
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (integral_nonneg (fun ω => sq_nonneg _))]
  apply hb.trans_lt
  dsimp [η]
  rw [← mul_div_assoc]
  apply (div_lt_iff₀ hden).mpr
  nlinarith

theorem uniformSum_tendsto_of_integer_stopped_limits
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {B H I : ℝ≥0 → Ω → ℝ} {F : Filtration ℝ≥0 mΩ}
    (hB : IsPreBrownianReal B P) (hAd : StronglyAdapted F B)
    (hind : ∀ s t, s ≤ t → Indep
      (MeasurableSpace.comap (fun ω => B t ω - B s ω) inferInstance) (F s) P)
    (hcB : ∀ᵐ ω ∂P, Continuous (fun t => B t ω))
    (hH : StronglyAdapted F H)
    (hcH : ∀ᵐ ω ∂P, Continuous (fun t => H t ω))
    {C : ℝ} (hC : 0 ≤ C) (hbH : ∀ᵐ ω ∂P, ∀ t, |H t ω| ≤ C)
    (hI : Martingale I F P) (hI2 : ∀ t, MemLp (I t) 2 P)
    (hcI : ∀ᵐ ω ∂P, Continuous (fun t => I t ω))
    (hlim : ∀ (N : ℕ), 0 < N → ∀ t ≤ (N : ℝ≥0),
      Tendsto (fun n => ∫ ω,
        (BrownianIntegralProcess.stoppedUniformSum B H N n t ω - I t ω)^2 ∂P)
        atTop (𝓝 0)) (T : ℝ≥0) :
    Tendsto (fun n => ∫ ω, (BrownianGrid.uniformSum B H T n ω - I T ω)^2 ∂P)
      atTop (𝓝 0) := by
  let : IsProbabilityMeasure P := hB.isGaussianProcess.isProbabilityMeasure
  have hBM : Martingale B F P :=
    BrownianFiltration.martingale_of_independent_past hB hAd hind
  have hB2 (t : ℝ≥0) : MemLp (B t) 2 P :=
    (hB.isGaussianProcess.hasGaussianLaw_eval t).memLp_two
  apply uniformSum_tendsto_of_rat_limits hB hAd hind hH hcH hC hbH hI2
  · intro n N
    exact BrownianUniformErrorContinuity.continuousOn_uniformSum_meanSquare_error
      hBM hI hB2 hI2 hcB hcI hH hcH hC hbH n N
  · exact BrownianIntegralProcess.tendsto_uniformSum_pos_rat_of_integer_limits hlim

end Problem367.BrownianArbitraryHorizon

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
-- module Solutions.Q243_FreeIsing.FreeIsing_Martingales_StoppedTimePrimitive
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal Topology
namespace Problem367.StoppedTimePrimitive

theorem continuous_stoppedProcess {Ω E : Type*} [TopologicalSpace E]
    {X : ℝ≥0 → Ω → E} {ω : Ω} (hX : Continuous (fun t => X t ω))
    (τ : Ω → WithTop ℝ≥0) : Continuous (fun t => stoppedProcess X τ t ω) := by
  cases hτ : τ ω with
  | top => simpa only [stoppedProcess, hτ, min_eq_left le_top, WithTop.untopA, WithTop.untopD_coe] using hX
  | coe u =>
    simpa only [stoppedProcess, hτ, ← WithTop.coe_min, WithTop.untopA,
      WithTop.untopD_coe, Function.comp_def, id_eq] using hX.comp (continuous_id.min continuous_const)

end Problem367.StoppedTimePrimitive

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
-- module Solutions.Q243_FreeIsing.FreeIsing_Martingales_StoppedProcessExhaustion
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped NNReal

namespace Problem367.StoppedProcessExhaustion

variable {Ω E : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

theorem ae_all_eq_of_stopped_eq
    {X Y : ℝ≥0 → Ω → E} {τ : ℕ → Ω → WithTop ℝ≥0}
    (heq : ∀ n, ∀ᵐ ω ∂μ, ∀ t,
      stoppedProcess X (τ n) t ω = stoppedProcess Y (τ n) t ω)
    (hexit : ∀ N : ℕ, ∀ᵐ ω ∂μ, ∀ᶠ n in atTop,
      ((N : ℝ≥0) : WithTop ℝ≥0) ≤ τ n ω) :
    ∀ᵐ ω ∂μ, ∀ t, X t ω = Y t ω := by
  filter_upwards [ae_all_iff.mpr heq, ae_all_iff.mpr hexit] with ω he hx
  intro t
  obtain ⟨N, hN⟩ := exists_nat_ge (t : ℝ)
  obtain ⟨n, hn⟩ := (hx N).exists
  have ht : (t : WithTop ℝ≥0) ≤ τ n ω :=
    (WithTop.coe_le_coe.mpr (show t ≤ (N : ℝ≥0) from hN)).trans hn
  simpa only [stoppedProcess_eq_of_le ht] using he n t

theorem ae_all_add_of_stopped_add
    {X M A : ℝ≥0 → Ω → ℝ} {τ : ℕ → Ω → WithTop ℝ≥0}
    (heq : ∀ n, ∀ᵐ ω ∂μ, ∀ t,
      stoppedProcess X (τ n) t ω =
        stoppedProcess M (τ n) t ω + stoppedProcess A (τ n) t ω)
    (hexit : ∀ N : ℕ, ∀ᵐ ω ∂μ, ∀ᶠ n in atTop,
      ((N : ℝ≥0) : WithTop ℝ≥0) ≤ τ n ω) :
    ∀ᵐ ω ∂μ, ∀ t, X t ω = M t ω + A t ω :=
  ae_all_eq_of_stopped_eq (Y := fun t ω => M t ω + A t ω) heq hexit

end Problem367.StoppedProcessExhaustion

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Martingales_StoppedIdentityExhaustion
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped NNReal Topology

namespace Problem367.StoppedIdentityExhaustion

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {μ : Measure Ω}

theorem ae_all_stopped_add_of_evaluation
    {X M A : ℝ≥0 → Ω → ℝ} (τ : Ω → WithTop ℝ≥0)
    (hcX : ∀ᵐ ω ∂μ, Continuous (fun t => X t ω))
    (hcM : ∀ᵐ ω ∂μ, Continuous (fun t => M t ω))
    (hcA : ∀ᵐ ω ∂μ, Continuous (fun t => A t ω))
    (heq : ∀ t, stoppedProcess X τ t =ᵐ[μ]
      fun ω => stoppedProcess M τ t ω + stoppedProcess A τ t ω) :
    ∀ᵐ ω ∂μ, ∀ t, stoppedProcess X τ t ω =
      stoppedProcess M τ t ω + stoppedProcess A τ t ω := by
  have hx := hcX.mono (fun ω hω =>
    StoppedTimePrimitive.continuous_stoppedProcess hω τ)
  have hma : ∀ᵐ ω ∂μ, Continuous (fun t =>
      stoppedProcess M τ t ω + stoppedProcess A τ t ω) := by
    filter_upwards [hcM, hcA] with ω hm ha
    exact (StoppedTimePrimitive.continuous_stoppedProcess hm τ).add
      (StoppedTimePrimitive.continuous_stoppedProcess ha τ)
  have h := ae_eq_of_continuous_of_evaluation_ae_eq hx hma heq
  exact h.mono (fun ω hω t => congrFun hω t)

theorem ae_all_add_of_localizing_stopped_add
    {F : Filtration ℝ≥0 mΩ} {τ : ℕ → Ω → WithTop ℝ≥0}
    {X M A : ℝ≥0 → Ω → ℝ} (hτ : IsLocalizingSequence F τ μ)
    (hcX : ∀ᵐ ω ∂μ, Continuous (fun t => X t ω))
    (hcM : ∀ᵐ ω ∂μ, Continuous (fun t => M t ω))
    (hcA : ∀ᵐ ω ∂μ, Continuous (fun t => A t ω))
    (heq : ∀ n t, stoppedProcess X (τ n) t =ᵐ[μ]
      fun ω => stoppedProcess M (τ n) t ω + stoppedProcess A (τ n) t ω) :
    ∀ᵐ ω ∂μ, ∀ t, X t ω = M t ω + A t ω := by
  apply StoppedProcessExhaustion.ae_all_add_of_stopped_add
  · intro n
    exact ae_all_stopped_add_of_evaluation (τ n) hcX hcM hcA (heq n)
  · intro N
    filter_upwards [hτ.tendsto_top] with ω hω
    exact ((WithTop.tendsto_nhds_top_iff _).mp hω (N : ℝ≥0)).mono
      (fun n hn => hn.le)

end Problem367.StoppedIdentityExhaustion

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Ising_CanonicalNormalizedField
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
open IsingObservationInnovation BrownianGrid

theorem canonical_field_eq_normalized_integral_oai
    {d : ℕ} (hd : 3 ≤ d) {beta : ℝ} {μ : Measure (TreeVertex d → IsingSpin)}
    [IsProbabilityMeasure μ]
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hb : 0 ≤ beta)
    (hcrit : ((d - 1 : ℕ) : ℝ) * Real.tanh beta ^ 2 ≤ 1)
    {J : TreeVertex d → ℝ≥0 → Paths d → ℝ} {Z : ℝ≥0 → Paths d → ℝ}
    (hJM : ∀ a, Martingale (J a) (filtration d) (observationLaw μ))
    (hZM : Martingale Z (filtration d) (observationLaw μ))
    (hJ2 : ∀ a t, MemLp (J a t) 2 (observationLaw μ))
    (hZ2 : ∀ t, MemLp (Z t) 2 (observationLaw μ))
    (hcJ : ∀ a, ∀ᵐ x ∂observationLaw μ, Continuous (fun t => J a t x))
    (hcZ : ∀ᵐ x ∂observationLaw μ, Continuous (fun t => Z t x))
    (hsumJ : ∀ t, HasSum (fun a => (hJ2 a t).toLp (J a t)) ((hZ2 t).toLp (Z t)))
    (hJlim : ∀ a (N : ℕ), 0 < N → ∀ t ≤ (N : ℝ≥0),
      Tendsto (fun k => ∫ x,
        (BrownianIntegralProcess.stoppedUniformSum
          (fun s x => innovationMap beta x a s) (continuousRootResponse hb a)
          N k t x - J a t x) ^ 2 ∂observationLaw μ) atTop (𝓝 0)) :
    ∀ᵐ x ∂observationLaw μ, ∀ t,
      continuousField beta (ConnectedHull.root d) t x = Z t x +
        nnrealTimePrimitive (canonicalResponseDrift beta (ConnectedHull.root d)) t x := by
  obtain ⟨I, hI2, hIp, hIM, hcI, hI0, hImean, hIenergy, hIlim, hsumI⟩ :=
    exists_canonical_root_covariance_integral_representation hd hμ hb hcrit
  have hind (a : TreeVertex d) (s t : ℝ≥0) (hst : s ≤ t) :=
    BrownianArrayFiltration.coordinate_increment_indep_past
      (B := fun a t x => innovationMap beta x a t) (F := filtration d)
      (innovationMap_increment_indep_filtration hμ s t hst) a
  have hIuniform (a : TreeVertex d) (T : ℝ≥0) :=
    BrownianArbitraryHorizon.uniformSum_tendsto_of_integer_stopped_limits
      (innovationMap_isBrownianReal hμ a).toIsPreBrownianReal
      (innovationMap_stronglyAdapted beta a) (hind a)
      (innovationMap_isBrownianReal hμ a).cont
      (continuousRootCovariance_progressive hb a).stronglyAdapted
      (continuousRootCovariance_continuous_ae hd hμ hb hcrit a)
      (show (0 : ℝ) ≤ 1 by norm_num)
      (Eventually.of_forall (fun x t => continuousRootCovariance_abs_le_one hb a t x))
      (hIM a) (hI2 a) (hcI a) (hIlim a) T
  have hJuniform (a : TreeVertex d) (T : ℝ≥0) :=
    BrownianArbitraryHorizon.uniformSum_tendsto_of_integer_stopped_limits
      (innovationMap_isBrownianReal hμ a).toIsPreBrownianReal
      (innovationMap_stronglyAdapted beta a) (hind a)
      (innovationMap_isBrownianReal hμ a).cont
      (continuousRootResponse_progressive hb a).stronglyAdapted
      (continuousRootResponse_continuous_ae hd hμ hb hcrit a)
      (show (0 : ℝ) ≤ 1 by norm_num)
      (Eventually.of_forall (fun x t => continuousRootResponse_abs_le_one hb a t x))
      (hJM a) (hJ2 a) (hcJ a) (hJlim a) T
  have hstop (n : ℕ) (T : ℝ≥0) :=
    canonical_stopped_field_eq_of_integral_limits hd hμ hb hcrit
      (fun a => (hIp a).isStronglyProgressive) hIM hJM hZM hI2 hJ2 hZ2 hcI hcJ hcZ
      n T (hsumI T) (hsumJ T) (fun a => hIuniform a T) (fun a => hJuniform a T)
  exact StoppedIdentityExhaustion.ae_all_add_of_localizing_stopped_add
    (canonicalPosteriorExit_localizing hd hμ hb hcrit (ConnectedHull.root d))
    (continuousField_modification hd hμ hb hcrit (ConnectedHull.root d)).1
    hcZ (canonicalResponseDrift_primitive_continuous hμ hb (ConnectedHull.root d)) hstop

end Problem367.IsingObservationFactor

end

end OAI
end

theorem solution : type_of% @OAI.Problem367.IsingObservationFactor.canonical_field_eq_normalized_integral_oai := @OAI.Problem367.IsingObservationFactor.canonical_field_eq_normalized_integral_oai
