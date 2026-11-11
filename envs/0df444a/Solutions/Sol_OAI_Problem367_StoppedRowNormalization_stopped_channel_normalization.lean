-- Prove2me | solution 1 for OAI.Problem367.StoppedRowNormalization.stopped_channel_normalization
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T01:39:40.706236+00:00
-- url     : https://prove2.me/submissions/c55cb138-3a3e-481e-aeb0-1cad8a4f1a33

import Mathlib
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Probability.Process.Stopping
import Definitions.Def_Q243FI000
import Definitions.Def_Q243FI001

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

lemma norm_sq_toLp_sub {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {f g : Ω → ℝ} (hf : MemLp f 2 P) (hg : MemLp g 2 P) :
    ‖hf.toLp f - hg.toLp g‖ ^ 2 = ∫ ω, (f ω - g ω) ^ 2 ∂P := by
  rw [norm_sq_L2_eq_integral]
  apply integral_congr_ae
  filter_upwards [Lp.coeFn_sub (hf.toLp f) (hg.toLp g), hf.coeFn_toLp, hg.coeFn_toLp]
    with ω hsub hfw hgw
  simp only [Pi.sub_apply] at hsub
  rw [hsub, hfw, hgw]

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

theorem cauchySeq_uniformSumLp
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {B : ℝ≥0 → Ω → ℝ} (hB : IsPreBrownianReal B P)
    {F : Filtration ℝ≥0 mΩ} (hAd : StronglyAdapted F B)
    (hind : ∀ s t, s ≤ t → Indep
      (MeasurableSpace.comap (fun ω => B t ω - B s ω) inferInstance) (F s) P) (H : ℝ≥0 → Ω → ℝ)
    (hH : StronglyAdapted (F) H)
    (hH2 : ∀ t, MemLp (H t) 2 P) (T : ℝ≥0)
    (hcont : ∀ ε > (0 : ℝ), ∃ δ > (0 : ℝ),
      ∀ s t : ℝ≥0, s ≤ t → t ≤ T → (t : ℝ) - (s : ℝ) ≤ δ →
        (∫ ω, (H s ω - H t ω) ^ 2 ∂P) ≤ ε) :
    CauchySeq (uniformSumLp hB hAd hind H hH hH2 T) := by
  apply Metric.cauchySeq_iff.mpr
  intro ε hε
  let η := ε ^ 2 / (4 * (T : ℝ) + 1)
  have hden : 0 < 4 * (T : ℝ) + 1 := by positivity
  have hη : 0 < η := div_pos (sq_pos_of_pos hε) hden
  obtain ⟨δ, hδ, hmod⟩ := hcont η hη
  obtain ⟨N, hN⟩ := exists_nat_gt ((T : ℝ) / δ)
  have hmesh (n : ℕ) (hn : N + 1 ≤ n) : (T : ℝ) / (n : ℝ) ≤ δ := by
    have hn0 : 0 < n := by omega
    have hnR : (0 : ℝ) < n := by exact_mod_cast hn0
    apply (div_le_iff₀ hnR).2
    have hN' : (T : ℝ) < (N : ℝ) * δ := (div_lt_iff₀ hδ).mp hN
    have hNn : (N : ℝ) ≤ (n : ℝ) := by exact_mod_cast (show N ≤ n by omega)
    nlinarith
  refine ⟨N + 1, ?_⟩
  intro n hn m hmn
  have hn0 : 0 < n := by omega
  have hm0 : 0 < m := by omega
  have hb := preBrownian_uniform_pair_bound hB hAd hind H hH hH2 T hn0 hm0
    (hmesh n hn) (hmesh m hmn) hmod
  have hnorm : ‖uniformSumLp hB hAd hind H hH hH2 T n - uniformSumLp hB hAd hind H hH hH2 T m‖ ^ 2 ≤
      4 * (T : ℝ) * η := by
    rw [uniformSumLp, uniformSumLp, norm_sq_toLp_sub]
    exact hb
  have hsmall : 4 * (T : ℝ) * η < ε ^ 2 := by
    dsimp [η]
    rw [← mul_div_assoc]
    apply (div_lt_iff₀ hden).2
    nlinarith [sq_pos_of_pos hε]
  rw [dist_eq_norm]
  nlinarith [norm_nonneg
    (uniformSumLp hB hAd hind H hH hH2 T n - uniformSumLp hB hAd hind H hH hH2 T m)]

theorem exists_uniformSumLp_limit
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {B : ℝ≥0 → Ω → ℝ} (hB : IsPreBrownianReal B P)
    {F : Filtration ℝ≥0 mΩ} (hAd : StronglyAdapted F B)
    (hind : ∀ s t, s ≤ t → Indep
      (MeasurableSpace.comap (fun ω => B t ω - B s ω) inferInstance) (F s) P) (H : ℝ≥0 → Ω → ℝ)
    (hH : StronglyAdapted (F) H)
    (hH2 : ∀ t, MemLp (H t) 2 P) (T : ℝ≥0)
    (hcont : ∀ ε > (0 : ℝ), ∃ δ > (0 : ℝ),
      ∀ s t : ℝ≥0, s ≤ t → t ≤ T → (t : ℝ) - (s : ℝ) ≤ δ →
        (∫ ω, (H s ω - H t ω) ^ 2 ∂P) ≤ ε) :
    ∃ I : Lp ℝ 2 P, Tendsto (uniformSumLp hB hAd hind H hH hH2 T) atTop (𝓝 I) :=
  cauchySeq_tendsto_of_complete (cauchySeq_uniformSumLp hB hAd hind H hH hH2 T hcont)

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
-- module Solutions.Q243_FreeIsing.FreeIsing_Brownian_FiltrationIntegralProperties
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

theorem uniformSum_stronglyMeasurable_terminal
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {B : ℝ≥0 → Ω → ℝ} {F : Filtration ℝ≥0 mΩ} (hAd : StronglyAdapted F B)
    (_hind : ∀ s t, s ≤ t → Indep
      (MeasurableSpace.comap (fun ω => B t ω - B s ω) inferInstance) (F s) P)
    (H : ℝ≥0 → Ω → ℝ) (hH : StronglyAdapted (F) H)
    (T : ℝ≥0) (n : ℕ) :
    StronglyMeasurable[F T] (uniformSum B H T n) := by
  by_cases hn : n = 0
  · subst n
    have hz : uniformSum B H T 0 = fun _ : Ω => (0 : ℝ) := by
      funext ω
      simp [uniformSum, integralSum]
    rw [hz]
    exact stronglyMeasurable_const
  have hn0 : 0 < n := Nat.pos_of_ne_zero hn
  unfold uniformSum integralSum
  apply Finset.stronglyMeasurable_fun_sum
  intro i hi
  have hi0 : i ≤ n := (Finset.mem_range.mp hi).le
  have hi1 : i + 1 ≤ n := Finset.mem_range.mp hi
  have hti := uniformGrid_le_horizon T hn0 hi0
  have hti1 := uniformGrid_le_horizon T hn0 hi1
  exact ((hH _).mono ((F).mono hti)).mul
    (((hAd _).mono ((F).mono hti1)).sub
      ((hAd _).mono ((F).mono hti)))

theorem integral_integralSum_eq_zero
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {B : ℝ≥0 → Ω → ℝ} (hB : IsPreBrownianReal B P)
    {F : Filtration ℝ≥0 mΩ} (hAd : StronglyAdapted F B)
    (hind : ∀ s t, s ≤ t → Indep
      (MeasurableSpace.comap (fun ω => B t ω - B s ω) inferInstance) (F s) P) (t : ℕ → ℝ≥0) (ht : Monotone t)
    (H : ℕ → Ω → ℝ)
    (hH : ∀ i, StronglyMeasurable[F (t i)] (H i))
    (hH2 : ∀ i, MemLp (H i) 2 P) (n : ℕ) :
    (∫ ω, integralSum B t H n ω ∂P) = 0 := by
  let : IsProbabilityMeasure P := hB.isGaussianProcess.isProbabilityMeasure
  have hD2 (i : ℕ) : MemLp (fun ω => B (t (i + 1)) ω - B (t i) ω) 2 P :=
    (hB.isGaussianProcess.hasGaussianLaw_eval _).memLp_two.sub
      (hB.isGaussianProcess.hasGaussianLaw_eval _).memLp_two
  have hint (i : ℕ) : Integrable (fun ω => H i ω * (B (t (i + 1)) ω - B (t i) ω)) P :=
    (hH2 i).integrable_mul (hD2 i)
  unfold integralSum
  rw [integral_finsetSum _ (fun i _ => hint i)]
  apply Finset.sum_eq_zero
  intro i hi
  exact SimpleIntegral.integral_mul_eq_zero_of_condExp_eq_zero
    ((F).le _) (hH i) ((hD2 i).integrable (by norm_num)) (hint i)
    (BrownianFiltration.increment_condExp_zero hB hAd (hind _ _ (ht (Nat.le_succ i))))

theorem integral_sq_error_tendsto_of_Lp_tendsto
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {B : ℝ≥0 → Ω → ℝ} (hB : IsPreBrownianReal B P)
    {F : Filtration ℝ≥0 mΩ} (hAd : StronglyAdapted F B)
    (hind : ∀ s t, s ≤ t → Indep
      (MeasurableSpace.comap (fun ω => B t ω - B s ω) inferInstance) (F s) P) (H : ℝ≥0 → Ω → ℝ)
    (hH : StronglyAdapted (F) H)
    (hH2 : ∀ t, MemLp (H t) 2 P) (T : ℝ≥0) {I : Lp ℝ 2 P}
    (hI : Tendsto (uniformSumLp hB hAd hind H hH hH2 T) atTop (𝓝 I)) :
    Tendsto (fun n => ∫ ω, (uniformSum B H T n ω - I ω) ^ 2 ∂P) atTop (𝓝 0) := by
  have hnorm := (hI.sub (tendsto_const_nhds (x := I))).norm.pow 2
  simp only [sub_self, norm_zero, zero_pow (by norm_num : (2 : ℕ) ≠ 0)] at hnorm
  apply hnorm.congr'
  apply Filter.Eventually.of_forall
  intro n
  dsimp only
  rw [norm_sq_L2_eq_integral]
  apply integral_congr_ae
  filter_upwards [Lp.coeFn_sub (uniformSumLp hB hAd hind H hH hH2 T n) I,
    coe_uniformSumLp hB hAd hind H hH hH2 T n] with ω hsub hsum
  simp only [Pi.sub_apply] at hsub
  rw [hsub, hsum]

theorem uniformSumLp_limit_terminal_centered
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {B : ℝ≥0 → Ω → ℝ} (hB : IsPreBrownianReal B P)
    {F : Filtration ℝ≥0 mΩ} (hAd : StronglyAdapted F B)
    (hind : ∀ s t, s ≤ t → Indep
      (MeasurableSpace.comap (fun ω => B t ω - B s ω) inferInstance) (F s) P) (H : ℝ≥0 → Ω → ℝ)
    (hH : StronglyAdapted (F) H)
    (hH2 : ∀ t, MemLp (H t) 2 P) (T : ℝ≥0) {I : Lp ℝ 2 P}
    (hI : Tendsto (uniformSumLp hB hAd hind H hH hH2 T) atTop (𝓝 I)) :
    AEStronglyMeasurable[F T] (I : Ω → ℝ) P ∧
      (∫ ω, I ω ∂P) = 0 := by
  let : IsProbabilityMeasure P := hB.isGaussianProcess.isProbabilityMeasure
  constructor
  · apply (isClosed_aestronglyMeasurable ((F).le T)).mem_of_tendsto hI
    apply Filter.Eventually.of_forall
    intro n
    exact (uniformSum_stronglyMeasurable_terminal hAd hind H hH T n).aestronglyMeasurable.congr
      (coe_uniformSumLp hB hAd hind H hH hH2 T n).symm
  · have hinner := ((innerSL ℝ (Lp.const 2 P (1 : ℝ))).continuous.tendsto I).comp hI
    have hzero (n : ℕ) : inner ℝ (Lp.const 2 P (1 : ℝ)) (uniformSumLp hB hAd hind H hH hH2 T n) = 0 := by
      rw [inner_const_one_eq_integral]
      rw [integral_congr_ae (coe_uniformSumLp hB hAd hind H hH hH2 T n)]
      exact integral_integralSum_eq_zero hB hAd hind (uniformGrid T n) (uniformGrid_mono T n)
        (fun i => H (uniformGrid T n i)) (fun i => hH _) (fun i => hH2 _) n
    change Tendsto (fun n => inner ℝ (Lp.const 2 P (1 : ℝ))
      (uniformSumLp hB hAd hind H hH hH2 T n)) atTop
      (𝓝 (inner ℝ (Lp.const 2 P (1 : ℝ)) I)) at hinner
    have heq : inner ℝ (Lp.const 2 P (1 : ℝ)) I = 0 := by
      apply tendsto_nhds_unique hinner
      simpa only [hzero] using
        (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 0))
    simpa only [inner_const_one_eq_integral] using heq

theorem exists_terminal_uniform_integral_isometry
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {B : ℝ≥0 → Ω → ℝ} (hB : IsPreBrownianReal B P)
    {F : Filtration ℝ≥0 mΩ} (hAd : StronglyAdapted F B)
    (hind : ∀ s t, s ≤ t → Indep
      (MeasurableSpace.comap (fun ω => B t ω - B s ω) inferInstance) (F s) P) (H : ℝ≥0 → Ω → ℝ)
    (hH : StronglyAdapted (F) H)
    (hc : ∀ᵐ ω ∂P, Continuous (fun t => H t ω))
    {C : ℝ} (hC : 0 ≤ C) (hb : ∀ᵐ ω ∂P, ∀ t, |H t ω| ≤ C)
    (T : ℝ≥0) :
    ∃ I : Ω → ℝ, StronglyMeasurable[F T] I ∧ MemLp I 2 P ∧
      (∫ ω, I ω ∂P) = 0 ∧
      (∫ ω, (I ω) ^ 2 ∂P) = (∫ t in (0 : ℝ)..(T : ℝ), ∫ ω, (H t.toNNReal ω) ^ 2 ∂P) ∧
      Tendsto (fun n => ∫ ω, (uniformSum B H T n ω - I ω) ^ 2 ∂P) atTop (𝓝 0) := by
  let : IsProbabilityMeasure P := hB.isGaussianProcess.isProbabilityMeasure
  have hHm : ∀ t, AEStronglyMeasurable (H t) P := fun t =>
    ((hH t).mono ((F).le t)).aestronglyMeasurable
  have hH2 : ∀ t, MemLp (H t) 2 P := by
    intro t
    apply MemLp.of_bound (hHm t) C
    filter_upwards [hb] with ω hω
    simpa only [Real.norm_eq_abs] using hω t
  obtain ⟨I, hI⟩ := exists_uniformSumLp_limit hB hAd hind H hH hH2 T
    (fun _ hε => MeanSquareContinuity.uniform_integral_sq_sub_le hHm hc hC hb T hε)
  obtain ⟨hIm, hIzero⟩ := uniformSumLp_limit_terminal_centered hB hAd hind H hH hH2 T hI
  have hiso := uniformSumLp_limit_isometry hB hAd hind H hH hH2 hc hC hb T hI
  refine ⟨hIm.mk I, hIm.stronglyMeasurable_mk, MemLp.ae_eq hIm.ae_eq_mk (Lp.memLp I), ?_, ?_, ?_⟩
  · exact (integral_congr_ae hIm.ae_eq_mk).symm.trans hIzero
  · rw [← hiso]
    apply integral_congr_ae
    filter_upwards [hIm.ae_eq_mk] with ω hω
    rw [hω]
  · apply (integral_sq_error_tendsto_of_Lp_tendsto hB hAd hind H hH hH2 T hI).congr'
    apply Filter.Eventually.of_forall
    intro n
    apply integral_congr_ae
    filter_upwards [hIm.ae_eq_mk] with ω hω
    rw [hω]

end Problem367.BrownianFiltrationGrid

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Stochastic_StoppedSimpleIntegral
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology

namespace Problem367.StoppedSimpleIntegral

variable {Ω ι : Type*} [mΩ : MeasurableSpace Ω] [LinearOrder ι]
  {P : Measure Ω} [IsFiniteMeasure P] {F : Filtration ι mΩ}
  {B : ι → Ω → ℝ}

theorem condExp_eval_eq_min (hB : Martingale B F P) (s t : ι) :
    P[B t | F s] =ᵐ[P] B (min s t) := by
  rcases le_total s t with hst | hts
  · simpa only [min_eq_left hst] using hB.condExp_ae_eq hst
  · rw [min_eq_right hts]
    exact (condExp_of_stronglyMeasurable (F.le s)
      ((hB.stronglyMeasurable t).mono (F.mono hts)) (hB.integrable t)).eventuallyEq

omit [IsFiniteMeasure P] in
theorem intervalSum_stronglyAdapted
    (hB : Martingale B F P) {a b : ι} (hab : a ≤ b)
    {H : Ω → ℝ} (hH : StronglyMeasurable[F a] H) :
    StronglyAdapted F (intervalSum B H a b) := by
  intro t
  rcases le_total t a with hta | hat
  · have heq : intervalSum B H a b t = 0 := by
      funext ω
      simp only [intervalSum, min_eq_left hta, min_eq_left (hta.trans hab),
        sub_self, mul_zero, Pi.zero_apply]
    rw [heq]
    exact stronglyMeasurable_zero
  · exact ((hH.mono (F.mono hat)).mul
      (((hB.stronglyMeasurable (min t b)).mono (F.mono (min_le_left _ _))).sub
        ((hB.stronglyMeasurable (min t a)).mono (F.mono (min_le_left _ _)))))

theorem intervalSum_eq_condExp_terminal
    (hB : Martingale B F P) {a b : ι} (hab : a ≤ b)
    {H : Ω → ℝ} (hH : StronglyMeasurable[F a] H) {K : ℝ}
    (hbound : ∀ᵐ ω ∂P, ‖H ω‖ ≤ K) (t : ι) :
    P[(fun ω => H ω * (B b ω - B a ω)) | F t] =ᵐ[P]
      intervalSum B H a b t := by
  have hDint : Integrable (fun ω => B b ω - B a ω) P :=
    (hB.integrable b).sub (hB.integrable a)
  have hYint : Integrable (fun ω => H ω * (B b ω - B a ω)) P :=
    hDint.bdd_mul (hH.mono (F.le a)).aestronglyMeasurable hbound
  rcases le_total t a with hta | hat
  · have hzero : P[(fun ω => B b ω - B a ω) | F a] =ᵐ[P] fun _ => 0 := by
      have hs := condExp_sub (hB.integrable b) (hB.integrable a) (F a)
      filter_upwards [hs, hB.condExp_ae_eq hab, hB.condExp_ae_eq (le_refl a)]
        with ω hs hb ha
      change P[(fun ω => B b ω - B a ω) | F a] ω =
        P[B b | F a] ω - P[B a | F a] ω at hs
      simpa only [hb, ha, sub_self] using hs
    have hyzero : P[(fun ω => H ω * (B b ω - B a ω)) | F a] =ᵐ[P] fun _ => 0 := by
      have hp := condExp_mul_of_stronglyMeasurable_left hH hYint hDint
      filter_upwards [hp, hzero] with ω hp hz
      change P[(fun ω => H ω * (B b ω - B a ω)) | F a] ω =
        H ω * P[(fun ω => B b ω - B a ω) | F a] ω at hp
      simpa only [hz, mul_zero] using hp
    have htower := condExp_condExp_of_le (μ := P) (F.mono hta) (F.le a)
      (f := fun ω => H ω * (B b ω - B a ω))
    calc
      P[(fun ω => H ω * (B b ω - B a ω)) | F t] =ᵐ[P]
          P[P[(fun ω => H ω * (B b ω - B a ω)) | F a] | F t] := htower.symm
      _ =ᵐ[P] P[(fun _ : Ω => (0 : ℝ)) | F t] := condExp_congr_ae hyzero
      _ =ᵐ[P] intervalSum B H a b t := by
        change P[(0 : Ω → ℝ) | F t] =ᵐ[P] intervalSum B H a b t
        rw [condExp_zero]
        apply Filter.Eventually.of_forall
        intro ω
        simp only [intervalSum, min_eq_left hta, min_eq_left (hta.trans hab),
          Pi.zero_apply, sub_self, mul_zero]
  · have hp := condExp_mul_of_stronglyMeasurable_left (hH.mono (F.mono hat)) hYint hDint
    have hs := condExp_sub (hB.integrable b) (hB.integrable a) (F t)
    filter_upwards [hp, hs, condExp_eval_eq_min hB t b, condExp_eval_eq_min hB t a]
      with ω hp hs hb ha
    change P[(fun ω => H ω * (B b ω - B a ω)) | F t] ω =
      H ω * P[(fun ω => B b ω - B a ω) | F t] ω at hp
    change P[(fun ω => B b ω - B a ω) | F t] ω =
      P[B b | F t] ω - P[B a | F t] ω at hs
    rw [hp, hs, hb, ha]
    rfl

theorem intervalSum_martingale
    (hB : Martingale B F P) {a b : ι} (hab : a ≤ b)
    {H : Ω → ℝ} (hH : StronglyMeasurable[F a] H) {K : ℝ}
    (hbound : ∀ᵐ ω ∂P, ‖H ω‖ ≤ K) :
    Martingale (intervalSum B H a b) F P :=
  (martingale_condExp (fun ω => H ω * (B b ω - B a ω)) F P).congr
    (intervalSum_stronglyAdapted hB hab hH)
    (intervalSum_eq_condExp_terminal hB hab hH hbound)

theorem finite_intervalSum_martingale {J : Type*}
    (hB : Martingale B F P) (s : Finset J) (a b : J → ι) (H : J → Ω → ℝ)
    (hab : ∀ i ∈ s, a i ≤ b i)
    (hH : ∀ i ∈ s, StronglyMeasurable[F (a i)] (H i))
    (K : J → ℝ) (hbound : ∀ i ∈ s, ∀ᵐ ω ∂P, ‖H i ω‖ ≤ K i) :
    Martingale (fun t ω => ∑ i ∈ s, intervalSum B (H i) (a i) (b i) t ω) F P := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    convert martingale_zero ℝ F P using 1
    all_goals try with_reducible_and_instances rfl
    ext t ω
    simp
  | @insert i s his ih =>
    have hi := intervalSum_martingale hB (hab i (Finset.mem_insert_self i s))
      (hH i (Finset.mem_insert_self i s)) (hbound i (Finset.mem_insert_self i s))
    have hs := ih (fun j hj => hab j (Finset.mem_insert_of_mem hj))
      (fun j hj => hH j (Finset.mem_insert_of_mem hj))
      (fun j hj => hbound j (Finset.mem_insert_of_mem hj))
    convert hi.add hs using 1
    all_goals try with_reducible_and_instances rfl
    ext t ω
    simp only [Finset.sum_insert his, Pi.add_apply]

end Problem367.StoppedSimpleIntegral

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

theorem stopped_predictable_sum_memLp_two
    (hB : IsPreBrownianReal B P)
    (hind : ∀ s t, s ≤ t → Indep
      (MeasurableSpace.comap (fun ω => B t ω - B s ω) inferInstance) (F s) P)
    (τ : ℕ → ℝ≥0) (hτ : Monotone τ) (H : ℕ → Ω → ℝ)
    (hH : ∀ i, StronglyMeasurable[F (τ i)] (H i))
    (hH2 : ∀ i, MemLp (H i) 2 P) (s : Finset ℕ) (t : ℝ≥0) :
    MemLp (fun ω => ∑ i ∈ s,
      StoppedSimpleIntegral.intervalSum B (H i) (τ i) (τ (i + 1)) t ω) 2 P := by
  apply memLp_finsetSum s
  intro i hi
  change MemLp (fun ω => H i ω *
    (B (min t (τ (i + 1))) ω - B (min t (τ i)) ω)) 2 P
  by_cases hit : τ i ≤ t
  · have hle : τ i ≤ min t (τ (i + 1)) := le_min hit (hτ (Nat.le_succ i))
    simpa only [min_eq_right hit] using
      predictable_mul_memLp_two hB (hind (τ i) (min t (τ (i + 1))) hle) (hH i) (hH2 i)
  · have hti : t ≤ τ i := le_of_not_ge hit
    have hti' : t ≤ τ (i + 1) := hti.trans (hτ (Nat.le_succ i))
    simp only [min_eq_left hti,
      min_eq_left hti', sub_self, mul_zero]
    exact MemLp.zero

theorem stopped_predictable_sum_martingale
    (hB : IsPreBrownianReal B P) (hAd : StronglyAdapted F B)
    (hind : ∀ s t, s ≤ t → Indep
      (MeasurableSpace.comap (fun ω => B t ω - B s ω) inferInstance) (F s) P)
    (τ : ℕ → ℝ≥0) (hτ : Monotone τ) (H : ℕ → Ω → ℝ)
    (hH : ∀ i, StronglyMeasurable[F (τ i)] (H i))
    (K : ℕ → ℝ) (hbound : ∀ i, ∀ᵐ ω ∂P, ‖H i ω‖ ≤ K i) (s : Finset ℕ) :
    Martingale (fun t ω => ∑ i ∈ s,
      StoppedSimpleIntegral.intervalSum B (H i) (τ i) (τ (i + 1)) t ω) F P := by
  let : IsProbabilityMeasure P := hB.isGaussianProcess.isProbabilityMeasure
  exact StoppedSimpleIntegral.finite_intervalSum_martingale
    (martingale_of_independent_past hB hAd hind) s τ (fun i => τ (i + 1)) H
    (fun i _ => hτ (Nat.le_succ i)) (fun i _ => hH i) K (fun i _ => hbound i)

end Problem367.BrownianFiltration

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Brownian_IntegralProcess
attribute [-instance] _root_.OAI.Problem367.WienerSampler.pathMeasurableSpace
attribute [-simp] _root_.OAI.Problem367.BrownianIntegralProcess.stoppedUniformSum_zero
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

theorem meanSquare_condExp_sub_le [IsFiniteMeasure P]
    (m : MeasurableSpace Ω) {X Y : Ω → ℝ}
    (hX : MemLp X 2 P) (hY : MemLp Y 2 P) :
    (∫ ω, (P[X | m] ω - P[Y | m] ω) ^ 2 ∂P) ≤
      ∫ ω, (X ω - Y ω) ^ 2 ∂P := by
  have hsub := condExp_sub (hX.integrable (by norm_num))
    (hY.integrable (by norm_num)) m
  calc
    _ = ∫ ω, (P[X - Y | m] ω) ^ 2 ∂P := by
      apply integral_congr_ae
      filter_upwards [hsub] with ω hω
      change P[X - Y | m] ω = P[X | m] ω - P[Y | m] ω at hω
      rw [hω]
    _ ≤ _ := by
      have hbound := integral_norm_condExp_rpow_le (m := m)
        (by norm_num : (1 : ℝ) ≤ 2)
        (f := X - Y) (by
          simpa only [Real.rpow_two, Real.norm_eq_abs, sq_abs, Pi.sub_apply] using
            (hX.sub hY).integrable_sq)
      simpa only [Real.rpow_two, Real.norm_eq_abs, sq_abs, Pi.sub_apply] using hbound

theorem finite_stoppedSum_eq_condExp [IsFiniteMeasure P]
    {F : Filtration ℝ≥0 mΩ} {B : ℝ≥0 → Ω → ℝ}
    (hB : Martingale B F P) (s : Finset ℕ) (a b : ℕ → ℝ≥0)
    (H : ℕ → Ω → ℝ) (hab : ∀ i ∈ s, a i ≤ b i)
    (hH : ∀ i ∈ s, StronglyMeasurable[F (a i)] (H i))
    (C : ℕ → ℝ) (hb : ∀ i ∈ s, ∀ᵐ ω ∂P, ‖H i ω‖ ≤ C i) (t : ℝ≥0) :
    P[(fun ω => ∑ i ∈ s, H i ω * (B (b i) ω - B (a i) ω)) | F t] =ᵐ[P]
      fun ω => ∑ i ∈ s, StoppedSimpleIntegral.intervalSum B (H i) (a i) (b i) t ω := by
  have hint (i : ℕ) (hi : i ∈ s) :
      Integrable (fun ω => H i ω * (B (b i) ω - B (a i) ω)) P :=
    ((hB.integrable (b i)).sub (hB.integrable (a i))).bdd_mul
      ((hH i hi).mono (F.le (a i))).aestronglyMeasurable (hb i hi)
  have hsum := condExp_finsetSum hint (F t)
  have hsumFun : (∑ i ∈ s, fun ω => H i ω * (B (b i) ω - B (a i) ω)) =
      (fun ω => ∑ i ∈ s, H i ω * (B (b i) ω - B (a i) ω)) := by
    funext ω
    simp only [Finset.sum_apply]
  rw [hsumFun] at hsum
  have heach : ∀ᵐ ω ∂P, ∀ i ∈ s,
      P[(fun ω => H i ω * (B (b i) ω - B (a i) ω)) | F t] ω =
        StoppedSimpleIntegral.intervalSum B (H i) (a i) (b i) t ω :=
    s.eventually_all.mpr (fun i hi =>
      StoppedSimpleIntegral.intervalSum_eq_condExp_terminal hB (hab i hi) (hH i hi) (hb i hi) t)
  filter_upwards [hsum, heach] with ω hsum heach
  simp only [Finset.sum_apply] at hsum
  rw [hsum]
  exact Finset.sum_congr rfl (fun i hi => heach i hi)

theorem stoppedUniformSum_eq_condExp
    {B H : ℝ≥0 → Ω → ℝ} {F : Filtration ℝ≥0 mΩ}
    (hB : IsPreBrownianReal B P) (hAd : StronglyAdapted F B)
    (hind : ∀ s t, s ≤ t → Indep
      (MeasurableSpace.comap (fun ω => B t ω - B s ω) inferInstance) (F s) P)
    (hH : StronglyAdapted F H) {C : ℝ}
    (hb : ∀ᵐ ω ∂P, ∀ t, |H t ω| ≤ C) (T : ℝ≥0) (n : ℕ) (t : ℝ≥0) :
    P[BrownianGrid.uniformSum B H T n | F t] =ᵐ[P] stoppedUniformSum B H T n t := by
  let : IsProbabilityMeasure P := hB.isGaussianProcess.isProbabilityMeasure
  apply finite_stoppedSum_eq_condExp (BrownianFiltration.martingale_of_independent_past hB hAd hind)
    (Finset.range n) (BrownianGrid.uniformGrid T n)
    (fun i => BrownianGrid.uniformGrid T n (i + 1))
    (fun i => H (BrownianGrid.uniformGrid T n i))
    (fun i _ => BrownianGrid.uniformGrid_mono T n (Nat.le_succ i))
    (fun i _ => hH _) (fun _ => C)
  intro i hi
  filter_upwards [hb] with ω hω
  simpa only [Real.norm_eq_abs] using hω (BrownianGrid.uniformGrid T n i)

theorem exists_stopped_uniform_integral_process
    {B H : ℝ≥0 → Ω → ℝ} {F : Filtration ℝ≥0 mΩ}
    (hB : IsPreBrownianReal B P) (hAd : StronglyAdapted F B)
    (hind : ∀ s t, s ≤ t → Indep
      (MeasurableSpace.comap (fun ω => B t ω - B s ω) inferInstance) (F s) P)
    (hH : StronglyAdapted F H)
    (hc : ∀ᵐ ω ∂P, Continuous (fun t => H t ω))
    {C : ℝ} (hC : 0 ≤ C) (hb : ∀ᵐ ω ∂P, ∀ t, |H t ω| ≤ C) (T : ℝ≥0) :
    ∃ M : ℝ≥0 → Ω → ℝ, Martingale M F P ∧
      (∀ t, MemLp (M t) 2 P) ∧
      (∀ t, (∫ ω, M t ω ∂P) = 0) ∧
      (∀ t, T ≤ t → M t = M T) ∧
      (∫ ω, (M T ω) ^ 2 ∂P) =
        (∫ t in (0 : ℝ)..(T : ℝ), ∫ ω, (H t.toNNReal ω) ^ 2 ∂P) ∧
      (∀ t, Tendsto (fun n => ∫ ω,
        (stoppedUniformSum B H T n t ω - M t ω) ^ 2 ∂P) atTop (𝓝 0)) := by
  let : IsProbabilityMeasure P := hB.isGaussianProcess.isProbabilityMeasure
  obtain ⟨I, hIm, hI2, hIzero, hIiso, hIlim⟩ :=
    BrownianFiltrationGrid.exists_terminal_uniform_integral_isometry
      hB hAd hind H hH hc hC hb T
  let M : ℝ≥0 → Ω → ℝ := fun t => P[I | F t]
  have hIint : Integrable I P := hI2.integrable (by norm_num)
  have hafter (t : ℝ≥0) (ht : T ≤ t) : M t = I :=
    condExp_of_stronglyMeasurable (F.le t) (hIm.mono (F.mono ht)) hIint
  have hH2 (t : ℝ≥0) : MemLp (H t) 2 P := by
    apply MemLp.of_bound ((hH t).mono (F.le t)).aestronglyMeasurable C
    filter_upwards [hb] with ω hω
    simpa only [Real.norm_eq_abs] using hω t
  refine ⟨M, martingale_condExp I F P, ?_, ?_, ?_, ?_, ?_⟩
  · intro t
    exact hI2.condExp (by norm_num)
  · intro t
    exact (integral_condExp (F.le t)).trans hIzero
  · intro t ht
    exact (hafter t ht).trans (hafter T le_rfl).symm
  · rw [hafter T le_rfl]
    exact hIiso
  · intro t
    apply squeeze_zero (fun n => integral_nonneg (fun ω => sq_nonneg _)) ?_ hIlim
    intro n
    calc
      _ = ∫ ω, (P[BrownianGrid.uniformSum B H T n | F t] ω - P[I | F t] ω) ^ 2 ∂P := by
        apply integral_congr_ae
        filter_upwards [stoppedUniformSum_eq_condExp hB hAd hind hH hb T n t] with ω hω
        change (stoppedUniformSum B H T n t ω - P[I | F t] ω) ^ 2 = _
        rw [hω]
      _ ≤ _ := meanSquare_condExp_sub_le (F t)
        (BrownianFiltrationGrid.uniformSum_memLp hB hAd hind H hH hH2 T n) hI2

end Problem367.BrownianIntegralProcess

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Brownian_IntegralContinuitySupport
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped NNReal Topology

namespace Problem367.BrownianIntegralProcess

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}

omit [MeasurableSpace Ω] in
theorem continuous_stoppedUniformSum
    {B H : ℝ≥0 → Ω → ℝ} {ω : Ω}
    (hB : Continuous (fun t => B t ω)) (T : ℝ≥0) (n : ℕ) :
    Continuous (fun t => stoppedUniformSum B H T n t ω) := by
  unfold stoppedUniformSum
  apply continuous_finsetSum
  intro i hi
  exact continuous_const.mul
    ((hB.comp (continuous_id.min continuous_const)).sub
      (hB.comp (continuous_id.min continuous_const)))

theorem ae_continuous_stoppedUniformSum
    {B H : ℝ≥0 → Ω → ℝ}
    (hB : ∀ᵐ ω ∂P, Continuous (fun t => B t ω)) (T : ℝ≥0) (n : ℕ) :
    ∀ᵐ ω ∂P, Continuous (fun t => stoppedUniformSum B H T n t ω) := by
  filter_upwards [hB] with ω hω
  exact continuous_stoppedUniformSum hω T n

theorem initial_zero_of_stopped_uniform_limit
    {B H M : ℝ≥0 → Ω → ℝ} (T : ℝ≥0) (hM : MemLp (M 0) 2 P)
    (hlim : Tendsto (fun n => ∫ ω,
      (stoppedUniformSum B H T n 0 ω - M 0 ω) ^ 2 ∂P) atTop (𝓝 0)) :
    M 0 =ᵐ[P] 0 := by
  have hlim' : Tendsto (fun _ : ℕ => ∫ ω, (M 0 ω) ^ 2 ∂P) atTop (𝓝 0) := by
    simpa only [stoppedUniformSum_zero, Pi.zero_apply, zero_sub, neg_sq] using hlim
  have hzero : (∫ ω, (M 0 ω) ^ 2 ∂P) = 0 :=
    tendsto_nhds_unique tendsto_const_nhds hlim'
  apply ae_eq_of_integral_sq_sub_eq_zero
  · simpa only [Pi.zero_apply, sub_zero] using hM.integrable_sq
  · simpa only [Pi.zero_apply, sub_zero] using hzero

end Problem367.BrownianIntegralProcess

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
-- module Solutions.Q243_FreeIsing.FreeIsing_Brownian_ContinuousIntegral
attribute [-instance] _root_.OAI.Problem367.WienerSampler.pathMeasurableSpace
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

theorem exists_continuous_stopped_uniform_integral
    {B H : ℝ≥0 → Ω → ℝ} {F : Filtration ℝ≥0 mΩ}
    (hB : IsPreBrownianReal B P) (hAd : StronglyAdapted F B)
    (hind : ∀ s t, s ≤ t → Indep
      (MeasurableSpace.comap (fun ω => B t ω - B s ω) inferInstance) (F s) P)
    (hBc : ∀ᵐ ω ∂P, Continuous (fun t => B t ω))
    (hH : StronglyAdapted F H)
    (hc : ∀ᵐ ω ∂P, Continuous (fun t => H t ω))
    {C : ℝ} (hC : 0 ≤ C) (hb : ∀ᵐ ω ∂P, ∀ t, |H t ω| ≤ C) (T : ℝ≥0) :
    ∃ I : ℝ≥0 → Ω → ℝ, IsStronglyPredictable F I ∧ Martingale I F P ∧
      (∀ᵐ ω ∂P, Continuous (fun t => I t ω)) ∧
      (∀ t, MemLp (I t) 2 P) ∧ I 0 =ᵐ[P] 0 ∧
      (∀ t, (∫ ω, I t ω ∂P) = 0) ∧
      (∀ᵐ ω ∂P, ∀ t, T ≤ t → I t ω = I T ω) ∧
      (∫ ω, (I T ω) ^ 2 ∂P) =
        (∫ t in (0 : ℝ)..(T : ℝ), ∫ ω, (H t.toNNReal ω) ^ 2 ∂P) ∧
      (∀ t, Tendsto (fun n => ∫ ω,
        (stoppedUniformSum B H T n t ω - I t ω) ^ 2 ∂P) atTop (𝓝 0)) := by
  let : IsProbabilityMeasure P := hB.isGaussianProcess.isProbabilityMeasure
  have hH2 (t : ℝ≥0) : MemLp (H t) 2 P := by
    apply MemLp.of_bound ((hH t).mono (F.le t)).aestronglyMeasurable C
    filter_upwards [hb] with ω hω
    simpa only [Real.norm_eq_abs] using hω t
  have hS2 (n : ℕ) (t : ℝ≥0) : MemLp (stoppedUniformSum B H T n t) 2 P :=
    BrownianFiltration.stopped_predictable_sum_memLp_two hB hind
      (BrownianGrid.uniformGrid T n) (BrownianGrid.uniformGrid_mono T n)
      (fun i => H (BrownianGrid.uniformGrid T n i)) (fun i => hH _) (fun i => hH2 _)
      (Finset.range n) t
  have hSM (n : ℕ) : Martingale (stoppedUniformSum B H T n) F P := by
    apply BrownianFiltration.stopped_predictable_sum_martingale hB hAd hind
      (BrownianGrid.uniformGrid T n) (BrownianGrid.uniformGrid_mono T n)
      (fun i => H (BrownianGrid.uniformGrid T n i)) (fun i => hH _) (fun _ => C)
      (fun i => ?_) (Finset.range n)
    filter_upwards [hb] with ω hω
    simpa only [Real.norm_eq_abs] using hω (BrownianGrid.uniformGrid T n i)
  have hSC : CauchySeq (fun n => (hS2 n T).toLp (stoppedUniformSum B H T n T)) := by
    have hclass : (fun n => (hS2 n T).toLp (stoppedUniformSum B H T n T)) =
        BrownianFiltrationGrid.uniformSumLp hB hAd hind H hH hH2 T := by
      funext n
      apply Lp.ext
      exact (hS2 n T).coeFn_toLp.trans
        ((stoppedUniformSum_terminal B H T n).eventuallyEq.trans
          (BrownianFiltrationGrid.coe_uniformSumLp hB hAd hind H hH hH2 T n).symm)
    rw [hclass]
    exact BrownianFiltrationGrid.cauchySeq_uniformSumLp hB hAd hind H hH hH2 T
      (fun ε hε => MeanSquareContinuity.uniform_integral_sq_sub_le
        (fun t => (hH2 t).aestronglyMeasurable) hc hC hb T hε)
  obtain ⟨L, hLp, hLc, hLlim⟩ :=
    MartingaleSquareMaximal.exists_predictable_continuous_L2_limit hSM hS2
      (ae_continuous_stoppedUniformSum hBc T) T hSC
  obtain ⟨M, hM, hM2, hMzero, hMstop, hMiso, hMlim⟩ :=
    exists_stopped_uniform_integral_process hB hAd hind hH hc hC hb T
  have hLM (t : ℝ≥0) (ht : t ≤ T) : L t =ᵐ[P] M t := by
    obtain ⟨hL2, hlim⟩ := hLlim t ht
    exact BrownianGrid.ae_eq_of_mean_square_limits (fun n => hS2 n t) hL2 (hM2 t)
      (integral_sq_sub_tendsto_of_L2_tendsto (fun n => hS2 n t) hL2 hlim) (hMlim t)
  let R : ℝ≥0 → Ω → ℝ := fun t => L (min t T)
  have hRad : StronglyAdapted F R := fun t =>
    (hLp.stronglyAdapted (min t T)).mono (F.mono (min_le_left _ _))
  have hRc : ∀ᵐ ω ∂P, Continuous (fun t => R t ω) := by
    filter_upwards [hLc] with ω hω
    exact hω.comp_continuous (continuous_id.min continuous_const) (fun t => min_le_right t T)
  let I := PredictableMesh.repair R
  have hIp : IsStronglyPredictable F I := PredictableMesh.repair_isStronglyPredictable hRad
  have hIR : ∀ᵐ ω ∂P, ∀ t, I t ω = R t ω := by
    filter_upwards [hRc] with ω hω
    intro t
    exact PredictableMesh.repair_eq_of_continuousOn (T := t) hω.continuousOn le_rfl
  have hIM (t : ℝ≥0) : I t =ᵐ[P] M t := by
    filter_upwards [hIR, hLM (min t T) (min_le_right _ _)] with ω hIω hω
    rw [hIω t]
    change L (min t T) ω = M t ω
    rw [hω]
    by_cases ht : t ≤ T
    · rw [min_eq_left ht]
    · rw [min_eq_right (le_of_not_ge ht), hMstop t (le_of_not_ge ht)]
  refine ⟨I, hIp, hM.congr hIp.stronglyAdapted (fun t => (hIM t).symm), ?_,
    (fun t => (hM2 t).ae_eq (hIM t).symm), ?_, ?_, ?_, ?_, ?_⟩
  · filter_upwards [hIR, hRc] with ω hIω hω
    exact hω.congr (fun t => (hIω t).symm)
  · exact (hIM 0).trans (initial_zero_of_stopped_uniform_limit T (hM2 0) (hMlim 0))
  · intro t
    exact (integral_congr_ae (hIM t)).trans (hMzero t)
  · filter_upwards [hIR] with ω hω
    intro t ht
    rw [hω t, hω T]
    dsimp [R]
    rw [min_eq_right ht, min_self]
  · rw [← hMiso]
    apply integral_congr_ae
    filter_upwards [hIM T] with ω hω
    rw [hω]
  · intro t
    apply (hMlim t).congr'
    apply Filter.Eventually.of_forall
    intro n
    apply integral_congr_ae
    filter_upwards [hIM t] with ω hω
    rw [hω]

end Problem367.BrownianIntegralProcess

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
-- module Solutions.Q243_FreeIsing.FreeIsing_Martingales_TransformL2
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Filter
open scoped Topology

namespace Problem367.MartingaleTransformL2

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {μ : Measure Ω}

theorem condExp_increment_zero [IsFiniteMeasure μ]
    {ι : Type*} [Preorder ι] {F : Filtration ι mΩ} {M : ι → Ω → ℝ}
    (hM : Martingale M F μ) {s t : ι} (hst : s ≤ t) :
    μ[(fun ω => M t ω - M s ω) | F s] =ᵐ[μ] fun _ => 0 := by
  change μ[M t - M s | F s] =ᵐ[μ] fun _ => 0
  have hsub := condExp_sub (hM.integrable t) (hM.integrable s) (F s)
  have hs := hM.condExp_ae_eq (le_refl s)
  filter_upwards [hsub, hM.condExp_ae_eq hst, hs] with ω hω htω hsω
  simpa only [Pi.sub_apply, htω, hsω, sub_self] using hω

theorem bounded_mul_memLp_two {H D : Ω → ℝ} {K : ℝ}
    (hH : AEStronglyMeasurable H μ) (hD : MemLp D 2 μ)
    (hbound : ∀ᵐ ω ∂μ, |H ω| ≤ K) :
    MemLp (fun ω => H ω * D ω) 2 μ := by
  apply hD.of_le_mul (c := K) (hH.mul hD.aestronglyMeasurable)
  filter_upwards [hbound] with ω hω
  simpa only [Real.norm_eq_abs, Pi.mul_apply, abs_mul] using
    mul_le_mul_of_nonneg_right hω (abs_nonneg (D ω))

theorem integral_sq_transform [IsFiniteMeasure μ]
    {F : Filtration ℕ mΩ} {M H : ℕ → Ω → ℝ}
    (hM : Martingale M F μ) (hM2 : ∀ i, MemLp (M i) 2 μ)
    (hH : StronglyAdapted F H) {K : ℝ}
    (hbound : ∀ i, ∀ᵐ ω ∂μ, |H i ω| ≤ K) (s : Finset ℕ) :
    (∫ ω, (∑ i ∈ s, H i ω * (M (i + 1) ω - M i ω)) ^ 2 ∂μ) =
      ∑ i ∈ s, ∫ ω, (H i ω * (M (i + 1) ω - M i ω)) ^ 2 ∂μ := by
  let D : ℕ → Ω → ℝ := fun i ω => M (i + 1) ω - M i ω
  have hD (i : ℕ) : StronglyMeasurable[F (i + 1)] (D i) :=
    (hM.stronglyMeasurable (i + 1)).sub
      ((hM.stronglyMeasurable i).mono (F.mono (Nat.le_succ i)))
  have hD2 (i : ℕ) : MemLp (D i) 2 μ := (hM2 (i + 1)).sub (hM2 i)
  have hHD (i : ℕ) : MemLp (fun ω => H i ω * D i ω) 2 μ :=
    bounded_mul_memLp_two ((hH i).mono (F.le i)).aestronglyMeasurable
      (hD2 i) (hbound i)
  have hzero (i : ℕ) : μ[D i | F i] =ᵐ[μ] 0 :=
    condExp_increment_zero hM (Nat.le_succ i)
  apply SimpleIntegral.integral_sq_sum_of_orthogonal s (fun i ω => H i ω * D i ω)
  · intro i hi j hj
    exact (hHD i).integrable_mul (hHD j)
  · intro i hi j hj hij
    rcases lt_or_gt_of_ne hij with hij | hji
    · exact SimpleIntegral.predictable_increments_orthogonal F H D hH hD
        (fun i => (hD2 i).integrable (by norm_num)) hHD hzero hij
    · simpa only [mul_comm] using
        SimpleIntegral.predictable_increments_orthogonal F H D hH hD
          (fun i => (hD2 i).integrable (by norm_num)) hHD hzero hji

theorem sum_integral_sq_increment [IsFiniteMeasure μ]
    {F : Filtration ℕ mΩ} {M : ℕ → Ω → ℝ}
    (hM : Martingale M F μ) (hM2 : ∀ i, MemLp (M i) 2 μ) (n : ℕ) :
    (∑ i ∈ Finset.range n, ∫ ω, (M (i + 1) ω - M i ω) ^ 2 ∂μ) =
      ∫ ω, (M n ω - M 0 ω) ^ 2 ∂μ := by
  have h := integral_sq_transform hM hM2
    (H := fun _ _ => (1 : ℝ)) (fun _ => stronglyMeasurable_const)
    (K := 1) (fun _ => Filter.Eventually.of_forall (fun _ => by simp))
    (Finset.range n)
  simp only [one_mul] at h
  rw [← h]
  congr 1
  funext ω
  congr 1
  clear h
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, ih]
    ring

theorem integral_sq_transform_le [IsFiniteMeasure μ]
    {F : Filtration ℕ mΩ} {M H : ℕ → Ω → ℝ}
    (hM : Martingale M F μ) (hM2 : ∀ i, MemLp (M i) 2 μ)
    (hH : StronglyAdapted F H) {K : ℝ} (hK : 0 ≤ K)
    (hbound : ∀ i, ∀ᵐ ω ∂μ, |H i ω| ≤ K) (n : ℕ) :
    (∫ ω, (∑ i ∈ Finset.range n,
      H i ω * (M (i + 1) ω - M i ω)) ^ 2 ∂μ) ≤
      K ^ 2 * ∫ ω, (M n ω - M 0 ω) ^ 2 ∂μ := by
  rw [integral_sq_transform hM hM2 hH hbound,
    ← sum_integral_sq_increment hM hM2, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i hi
  have hD2 := (hM2 (i + 1)).sub (hM2 i)
  have hHD := bounded_mul_memLp_two
    ((hH i).mono (F.le i)).aestronglyMeasurable hD2 (hbound i)
  rw [← integral_const_mul]
  apply integral_mono_ae hHD.integrable_sq (hD2.integrable_sq.const_mul (K ^ 2))
  filter_upwards [hbound i] with ω hω
  rw [mul_pow]
  apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
  simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg _) hK).2 hω

theorem integral_sq_increment_eq [IsFiniteMeasure μ]
    {ι : Type*} [Preorder ι] {F : Filtration ι mΩ} {M : ι → Ω → ℝ}
    (hM : Martingale M F μ) {s t : ι} (hst : s ≤ t)
    (hs2 : MemLp (M s) 2 μ) (ht2 : MemLp (M t) 2 μ) :
    (∫ ω, (M t ω - M s ω) ^ 2 ∂μ) =
      (∫ ω, M t ω ^ 2 ∂μ) - ∫ ω, M s ω ^ 2 ∂μ := by
  have hD2 : MemLp (fun ω => M t ω - M s ω) 2 μ := ht2.sub hs2
  have hcross : Integrable (fun ω => M s ω * (M t ω - M s ω)) μ :=
    hs2.integrable_mul hD2
  have horth : (∫ ω, M s ω * (M t ω - M s ω) ∂μ) = 0 :=
    SimpleIntegral.integral_mul_eq_zero_of_condExp_eq_zero (F.le s)
      (hM.stronglyMeasurable s) (hD2.integrable (by norm_num)) hcross
      (condExp_increment_zero hM hst)
  have heq : (∫ ω, M t ω ^ 2 ∂μ) =
      (∫ ω, (M t ω - M s ω) ^ 2 ∂μ) +
        2 * (∫ ω, M s ω * (M t ω - M s ω) ∂μ) +
          ∫ ω, M s ω ^ 2 ∂μ := by
    calc
      _ = ∫ ω, (M t ω - M s ω) ^ 2 +
          2 * (M s ω * (M t ω - M s ω)) + M s ω ^ 2 ∂μ := by
        apply integral_congr_ae
        exact Filter.Eventually.of_forall (fun ω => by ring)
      _ = _ := by
        have h1 := integral_add hD2.integrable_sq (hcross.const_mul 2)
        have h2 := integral_add (hD2.integrable_sq.add (hcross.const_mul 2)) hs2.integrable_sq
        simp only [Pi.add_apply] at h1 h2
        rw [h1, integral_const_mul] at h2
        exact h2
  rw [horth] at heq
  linarith

theorem integral_sq_increment_le [IsFiniteMeasure μ]
    {ι : Type*} [Preorder ι] {F : Filtration ι mΩ} {M : ι → Ω → ℝ}
    (hM : Martingale M F μ) {s t : ι} (hst : s ≤ t)
    (hs2 : MemLp (M s) 2 μ) (ht2 : MemLp (M t) 2 μ) :
    (∫ ω, (M t ω - M s ω) ^ 2 ∂μ) ≤ ∫ ω, M t ω ^ 2 ∂μ := by
  rw [integral_sq_increment_eq hM hst hs2 ht2]
  exact sub_le_self _ (integral_nonneg (fun ω => sq_nonneg _))

theorem integral_sq_grid_transform_le_terminal [IsFiniteMeasure μ]
    {ι : Type*} [Preorder ι] {F : Filtration ι mΩ} {M : ι → Ω → ℝ}
    (hM : Martingale M F μ) (hM2 : ∀ t, MemLp (M t) 2 μ)
    (t : ℕ → ι) (ht : Monotone t) (H : ℕ → Ω → ℝ)
    (hH : ∀ i, StronglyMeasurable[F (t i)] (H i)) {K : ℝ} (hK : 0 ≤ K)
    (hbound : ∀ i, ∀ᵐ ω ∂μ, |H i ω| ≤ K) (n : ℕ) :
    (∫ ω, (∑ i ∈ Finset.range n,
      H i ω * (M (t (i + 1)) ω - M (t i) ω)) ^ 2 ∂μ) ≤
      K ^ 2 * ∫ ω, M (t n) ω ^ 2 ∂μ := by
  let G : Filtration ℕ mΩ :=
    ⟨fun i => F (t i), fun _ _ hij => F.mono (ht hij), fun i => F.le (t i)⟩
  have hMG : Martingale (fun i => M (t i)) G μ :=
    ⟨by intro i; exact hM.stronglyMeasurable (t i),
      by intro i j hij; exact hM.condExp_ae_eq (ht hij)⟩
  exact (integral_sq_transform_le hMG (fun i => hM2 (t i)) hH hK hbound n).trans
    (mul_le_mul_of_nonneg_left
      (integral_sq_increment_le hM (ht (Nat.zero_le n)) (hM2 _) (hM2 _)) (sq_nonneg K))

theorem tendsto_integral_sq_grid_transform [IsFiniteMeasure μ]
    {ι : Type*} [Preorder ι] {F : Filtration ι mΩ}
    {M : ℕ → ι → Ω → ℝ} (hM : ∀ k, Martingale (M k) F μ)
    (hM2 : ∀ k t, MemLp (M k t) 2 μ) (t : ℕ → ℕ → ι)
    (ht : ∀ k, Monotone (t k)) (N : ℕ → ℕ) {T : ι}
    (hterminal : ∀ k, t k (N k) = T) (H : ℕ → ℕ → Ω → ℝ)
    (hH : ∀ k i, StronglyMeasurable[F (t k i)] (H k i))
    {K : ℝ} (hK : 0 ≤ K) (hbound : ∀ k i, ∀ᵐ ω ∂μ, |H k i ω| ≤ K)
    (hlim : Tendsto (fun k => ∫ ω, M k T ω ^ 2 ∂μ) atTop (𝓝 0)) :
    Tendsto (fun k => ∫ ω, (∑ i ∈ Finset.range (N k),
      H k i ω * (M k (t k (i + 1)) ω - M k (t k i) ω)) ^ 2 ∂μ)
      atTop (𝓝 0) := by
  apply squeeze_zero (fun k => integral_nonneg (fun ω => sq_nonneg _))
    (fun k => ?_) (by simpa using hlim.const_mul (K ^ 2))
  simpa only [hterminal k] using
    integral_sq_grid_transform_le_terminal (hM k) (hM2 k) (t k) (ht k)
      (H k) (hH k) hK (hbound k) (N k)

end Problem367.MartingaleTransformL2

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Stochastic_SimpleIntegralAssociativity
attribute [-instance] _root_.OAI.Problem367.WienerSampler.pathMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace Problem367.BrownianGrid

theorem integralSum_succ_sub {Ω : Type*} (B : ℝ≥0 → Ω → ℝ)
    (t : ℕ → ℝ≥0) (H : ℕ → Ω → ℝ) (n : ℕ) (ω : Ω) :
    integralSum B t H (n + 1) ω - integralSum B t H n ω =
      H n ω * (B (t (n + 1)) ω - B (t n) ω) := by
  simp only [integralSum, Finset.sum_range_succ, add_sub_cancel_left]

theorem integralSum_compose_refined {Ω : Type*} (B : ℝ≥0 → Ω → ℝ)
    (t : ℕ → ℝ≥0) (H K : ℕ → Ω → ℝ) (n : ℕ) {k : ℕ}
    (hk : 0 < k) (ω : Ω) :
    (∑ j ∈ Finset.range n, K j ω *
      (integralSum B t H ((j + 1) * k) ω - integralSum B t H (j * k) ω)) =
      integralSum B t (fun i ω => K (i / k) ω * H i ω) (n * k) ω := by
  rw [weighted_sum_refinement (fun i => integralSum B t H i ω)
    (fun j => K j ω) n hk]
  simp_rw [integralSum_succ_sub]
  simp only [integralSum, mul_assoc]

theorem stronglyMeasurable_compose_refined
    {Ω : Type*} [mΩ : MeasurableSpace Ω] (F : Filtration ℝ≥0 mΩ)
    {t : ℕ → ℝ≥0} (ht : Monotone t) {H K : ℕ → Ω → ℝ} {k : ℕ}
    (hH : ∀ i, StronglyMeasurable[F (t i)] (H i))
    (hK : ∀ j, StronglyMeasurable[F (t (j * k))] (K j)) (i : ℕ) :
    StronglyMeasurable[F (t i)] (fun ω => K (i / k) ω * H i ω) :=
  ((hK (i / k)).mono (F.mono (ht (Nat.div_mul_le_self i k)))).mul (hH i)

theorem composed_integralSum_difference_isometry
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {B : ℝ≥0 → Ω → ℝ} {F : Filtration ℝ≥0 mΩ}
    (hB : IsPreBrownianReal B P) (hAd : StronglyAdapted F B)
    (hind : ∀ s t, s ≤ t → Indep
      (MeasurableSpace.comap (fun ω => B t ω - B s ω) inferInstance) (F s) P)
    (t : ℕ → ℝ≥0) (ht : Monotone t) (H K J : ℕ → Ω → ℝ)
    {k : ℕ} (hk : 0 < k)
    (hH : ∀ i, StronglyMeasurable[F (t i)] (H i))
    (hK : ∀ j, StronglyMeasurable[F (t (j * k))] (K j))
    (hJ : ∀ i, StronglyMeasurable[F (t i)] (J i))
    (hKH2 : ∀ i, MemLp (fun ω => K (i / k) ω * H i ω) 2 P)
    (hJ2 : ∀ i, MemLp (J i) 2 P) (n : ℕ) :
    (∫ ω, ((∑ j ∈ Finset.range n, K j ω *
      (integralSum B t H ((j + 1) * k) ω - integralSum B t H (j * k) ω)) -
        integralSum B t J (n * k) ω) ^ 2 ∂P) =
      ∑ i ∈ Finset.range (n * k), ((t (i + 1) : ℝ) - (t i : ℝ)) *
        ∫ ω, (K (i / k) ω * H i ω - J i ω) ^ 2 ∂P := by
  simp_rw [integralSum_compose_refined B t H K n hk]
  simpa only [integralSum, sub_mul, Finset.sum_sub_distrib] using
    BrownianFiltration.predictable_sum_isometry hB hAd hind t ht
      (fun i ω => K (i / k) ω * H i ω - J i ω)
      (fun i => (stronglyMeasurable_compose_refined F ht hH hK i).sub (hJ i))
      (fun i => (hKH2 i).sub (hJ2 i)) (Finset.range (n * k))

theorem composed_integralSum_difference_bound
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {B : ℝ≥0 → Ω → ℝ} {F : Filtration ℝ≥0 mΩ}
    (hB : IsPreBrownianReal B P) (hAd : StronglyAdapted F B)
    (hind : ∀ s t, s ≤ t → Indep
      (MeasurableSpace.comap (fun ω => B t ω - B s ω) inferInstance) (F s) P)
    (t : ℕ → ℝ≥0) (ht : Monotone t) (H K J : ℕ → Ω → ℝ)
    {k : ℕ} (hk : 0 < k)
    (hH : ∀ i, StronglyMeasurable[F (t i)] (H i))
    (hK : ∀ j, StronglyMeasurable[F (t (j * k))] (K j))
    (hJ : ∀ i, StronglyMeasurable[F (t i)] (J i))
    (hKH2 : ∀ i, MemLp (fun ω => K (i / k) ω * H i ω) 2 P)
    (hJ2 : ∀ i, MemLp (J i) 2 P) (n : ℕ) {ε : ℝ}
    (happrox : ∀ i < n * k,
      (∫ ω, (K (i / k) ω * H i ω - J i ω) ^ 2 ∂P) ≤ ε) :
    (∫ ω, ((∑ j ∈ Finset.range n, K j ω *
      (integralSum B t H ((j + 1) * k) ω - integralSum B t H (j * k) ω)) -
        integralSum B t J (n * k) ω) ^ 2 ∂P) ≤
      ((t (n * k) : ℝ) - (t 0 : ℝ)) * ε := by
  rw [composed_integralSum_difference_isometry hB hAd hind t ht H K J hk
    hH hK hJ hKH2 hJ2 n]
  calc
    _ ≤ ∑ i ∈ Finset.range (n * k), ((t (i + 1) : ℝ) - (t i : ℝ)) * ε := by
      apply Finset.sum_le_sum
      intro i hi
      exact mul_le_mul_of_nonneg_left (happrox i (Finset.mem_range.mp hi))
        (sub_nonneg.mpr (NNReal.coe_le_coe.mpr (ht (Nat.le_succ i))))
    _ = _ := by
      rw [← Finset.sum_mul, Finset.sum_range_sub (fun i => (t i : ℝ)) (n * k)]

end Problem367.BrownianGrid

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

theorem meanSquare_limit_of_close {α : Type*} {l : Filter α}
    {X Y : α → Ω → ℝ} (hX : ∀ a, MemLp (X a) 2 μ)
    (hY : ∀ a, MemLp (Y a) 2 μ) {Z : Ω → ℝ} (hZ : MemLp Z 2 μ)
    (hclose : Tendsto (fun a => ∫ ω, (X a ω - Y a ω) ^ 2 ∂μ) l (𝓝 0))
    (hlim : Tendsto (fun a => ∫ ω, (X a ω - Z ω) ^ 2 ∂μ) l (𝓝 0)) :
    Tendsto (fun a => ∫ ω, (Y a ω - Z ω) ^ 2 ∂μ) l (𝓝 0) := by
  apply (tendsto_toLp_iff_meanSquare hY hZ).mp
  apply ((tendsto_toLp_iff_meanSquare hX hZ).mpr hlim).congr_dist
  have heq (a : α) :
      dist ((hX a).toLp (X a)) ((hY a).toLp (Y a)) ^ 2 =
        ∫ ω, (X a ω - Y a ω) ^ 2 ∂μ := by
    rw [dist_eq_norm, ← MemLp.toLp_sub (hX a) (hY a)]
    exact PredictableL2.norm_toLp_sq ((hX a).sub (hY a))
  have hs := Real.continuous_sqrt.continuousAt.tendsto.comp hclose
  simpa only [Function.comp_def, ← heq, Real.sqrt_sq dist_nonneg,
    Real.sqrt_zero] using hs

theorem coarseTransform_memLp (K : ℕ → Ω → ℝ)
    (hK : ∀ j, AEStronglyMeasurable (K j) μ) (C : ℕ → ℝ)
    (hbound : ∀ j, ∀ᵐ ω ∂μ, |K j ω| ≤ C j)
    {M : ℕ → Ω → ℝ} (hM : ∀ j, MemLp (M j) 2 μ) (n : ℕ) :
    MemLp (coarseTransform K M n) 2 μ := by
  exact memLp_finsetSum _ fun j _ =>
    bounded_mul_memLp (hK j) (hbound j) ((hM (j + 1)).sub (hM j))

end Limits
end Problem367.SimpleIntegral

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Brownian_ContinuousAssociativity
attribute [-instance] _root_.OAI.Problem367.WienerSampler.pathMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal Topology

namespace Problem367.BrownianIntegralProcess

variable {Ω : Type*}

theorem stopped_sum_at_grid (B : ℝ≥0 → Ω → ℝ)
    (τ : ℕ → ℝ≥0) (hτ : Monotone τ) (H : ℕ → Ω → ℝ)
    {n j : ℕ} (hj : j ≤ n) :
    (fun ω => ∑ i ∈ Finset.range n,
      StoppedSimpleIntegral.intervalSum B (H i) (τ i) (τ (i + 1)) (τ j) ω) =
      BrownianGrid.integralSum B τ H j := by
  funext ω
  calc
    _ = ∑ i ∈ Finset.range j,
        StoppedSimpleIntegral.intervalSum B (H i) (τ i) (τ (i + 1)) (τ j) ω := by
      symm
      apply Finset.sum_subset (Finset.range_mono hj)
      intro i hi hij
      have hji : j ≤ i := by simpa only [Finset.mem_range, not_lt] using hij
      simp only [StoppedSimpleIntegral.intervalSum, min_eq_left (hτ hji),
        min_eq_left (hτ (hji.trans (Nat.le_succ i))), sub_self, mul_zero]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro i hi
      have hij : i + 1 ≤ j := Finset.mem_range.mp hi
      simp only [StoppedSimpleIntegral.intervalSum,
        min_eq_right (hτ hij), min_eq_right (hτ (Nat.le_of_succ_le hij))]

theorem stoppedUniformSum_at_grid (B H : ℝ≥0 → Ω → ℝ)
    (T : ℝ≥0) {n j : ℕ} (hj : j ≤ n) :
    stoppedUniformSum B H T n (BrownianGrid.uniformGrid T n j) =
      BrownianGrid.integralSum B (BrownianGrid.uniformGrid T n)
        (fun i => H (BrownianGrid.uniformGrid T n i)) j :=
  stopped_sum_at_grid B _ (BrownianGrid.uniformGrid_mono T n) _ hj

end Problem367.BrownianIntegralProcess

namespace Problem367.BrownianContinuousAssociativity

open BrownianGrid BrownianIntegralProcess

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
  {B H K : ℝ≥0 → Ω → ℝ} {F : Filtration ℝ≥0 mΩ}

theorem mixedSum_difference_bound
    (hB : IsPreBrownianReal B P) (hAd : StronglyAdapted F B)
    (hind : ∀ s t, s ≤ t → Indep
      (MeasurableSpace.comap (fun ω => B t ω - B s ω) inferInstance) (F s) P)
    (hH : StronglyAdapted F H) (hK : StronglyAdapted F K)
    {C D : ℝ} (hC : 0 ≤ C) (_hD : 0 ≤ D)
    (hbH : ∀ᵐ ω ∂P, ∀ t, |H t ω| ≤ C)
    (hbK : ∀ᵐ ω ∂P, ∀ t, |K t ω| ≤ D)
    (T : ℝ≥0) {n k : ℕ} (hn : 0 < n) (hk : 0 < k) {ε : ℝ}
    (happrox : ∀ i < n * k,
      (∫ ω, (K (uniformGrid T n (i / k)) ω -
        K (uniformGrid T (n * k) i) ω) ^ 2 ∂P) ≤ ε) :
    (∫ ω, (mixedSum B H K T n k ω -
      uniformSum B (fun t ω => K t ω * H t ω) T (n * k) ω) ^ 2 ∂P) ≤
        (T : ℝ) * (C ^ 2 * ε) := by
  let : IsProbabilityMeasure P := hB.isGaussianProcess.isProbabilityMeasure
  have hH2 (t : ℝ≥0) : MemLp (H t) 2 P := by
    apply MemLp.of_bound ((hH t).mono (F.le t)).aestronglyMeasurable C
    filter_upwards [hbH] with ω hω
    exact hω t
  have hK2 (t : ℝ≥0) : MemLp (K t) 2 P := by
    apply MemLp.of_bound ((hK t).mono (F.le t)).aestronglyMeasurable D
    filter_upwards [hbK] with ω hω
    exact hω t
  have hKH2 (s t : ℝ≥0) : MemLp (fun ω => K s ω * H t ω) 2 P :=
    memLp_compose_of_bounded (hH2 t) (hK2 s).aestronglyMeasurable
      (hbK.mono (fun ω hω => hω s))
  have hbound := composed_integralSum_difference_bound hB hAd hind
    (uniformGrid T (n * k)) (uniformGrid_mono T (n * k))
    (fun i => H (uniformGrid T (n * k) i))
    (fun j => K (uniformGrid T n j))
    (fun i ω => K (uniformGrid T (n * k) i) ω * H (uniformGrid T (n * k) i) ω)
    hk (fun i => hH _) (fun j => by rw [uniformGrid_refine T hn hk]; exact hK _)
    (fun i => (hK _).mul (hH _)) (fun i => hKH2 _ _) (fun i => hKH2 _ _)
    n (ε := C ^ 2 * ε) ?_
  · simpa only [integralSum_compose_refined B _ _ _ n hk, uniformGrid_end T (Nat.mul_pos hn hk),
      uniformGrid_zero, NNReal.coe_zero, sub_zero, mixedSum, uniformSum] using hbound
  · intro i hi
    let s := uniformGrid T n (i / k)
    let t := uniformGrid T (n * k) i
    calc
      _ ≤ ∫ ω, C ^ 2 * (K s ω - K t ω) ^ 2 ∂P := by
        apply integral_mono_ae ((hKH2 s t).sub (hKH2 t t)).integrable_sq
          (((hK2 s).sub (hK2 t)).integrable_sq.const_mul (C ^ 2))
        filter_upwards [hbH] with ω hω
        have hs : H t ω ^ 2 ≤ C ^ 2 := by
          simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg _) hC).mpr (hω t)
        calc
          _ = H t ω ^ 2 * (K s ω - K t ω) ^ 2 := by simp only [Pi.sub_apply] <;> ring
          _ ≤ _ := mul_le_mul_of_nonneg_right hs (sq_nonneg _)
      _ = C ^ 2 * ∫ ω, (K s ω - K t ω) ^ 2 ∂P := integral_const_mul _ _
      _ ≤ C ^ 2 * ε := mul_le_mul_of_nonneg_left (happrox i hi) (sq_nonneg C)

theorem mixedSum_difference_tendsto
    (hB : IsPreBrownianReal B P) (hAd : StronglyAdapted F B)
    (hind : ∀ s t, s ≤ t → Indep
      (MeasurableSpace.comap (fun ω => B t ω - B s ω) inferInstance) (F s) P)
    (hH : StronglyAdapted F H) (hK : StronglyAdapted F K)
    (hcK : ∀ᵐ ω ∂P, Continuous (fun t => K t ω))
    {C D : ℝ} (hC : 0 ≤ C) (hD : 0 ≤ D)
    (hbH : ∀ᵐ ω ∂P, ∀ t, |H t ω| ≤ C)
    (hbK : ∀ᵐ ω ∂P, ∀ t, |K t ω| ≤ D) (T : ℝ≥0) :
    Tendsto (fun n => ∫ ω, (mixedSum B H K T (n + 1) (n + 1) ω -
      uniformSum B (fun t ω => K t ω * H t ω) T ((n + 1) * (n + 1)) ω) ^ 2 ∂P)
      atTop (𝓝 0) := by
  let : IsProbabilityMeasure P := hB.isGaussianProcess.isProbabilityMeasure
  apply Metric.tendsto_atTop.mpr
  intro ε hε
  let η := ε / ((T : ℝ) * C ^ 2 + 1)
  have hη : 0 < η := div_pos hε (by positivity)
  obtain ⟨δ, hδ, hmod⟩ := MeanSquareContinuity.uniform_integral_sq_sub_le
    (fun t => ((hK t).mono (F.le t)).aestronglyMeasurable) hcK hD hbK T hη
  have hwidth : Tendsto (fun n : ℕ => (T : ℝ) / (n : ℝ)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
  obtain ⟨N, hN⟩ := (hwidth.eventually (gt_mem_nhds hδ)).exists_forall_of_atTop
  refine ⟨N, ?_⟩
  intro n hn
  have hmesh : (T : ℝ) / ((n + 1 : ℕ) : ℝ) ≤ δ :=
    (hN (n + 1) (hn.trans (Nat.le_succ n))).le
  have hbound := mixedSum_difference_bound hB hAd hind hH hK hC hD hbH hbK T
    (Nat.succ_pos n) (Nat.succ_pos n) (ε := η) (fun i hi => hmod _ _
      (uniformGrid_floor_le T (Nat.succ_pos n) (Nat.succ_pos n) i)
      (uniformGrid_le_horizon T (Nat.mul_pos (Nat.succ_pos n) (Nat.succ_pos n)) hi.le)
      ((uniformGrid_floor_sub_le T (Nat.succ_pos n) (Nat.succ_pos n) i).trans hmesh))
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (integral_nonneg (fun ω => sq_nonneg _))]
  apply hbound.trans_lt
  dsimp [η]
  have hp : 0 < (T : ℝ) * C ^ 2 + 1 := by positivity
  rw [← mul_assoc, ← mul_div_assoc]
  apply (div_lt_iff₀ hp).mpr
  nlinarith

omit mΩ in
theorem uniformSum_stoppedUniformSum_eq_mixedSum
    (B H K : ℝ≥0 → Ω → ℝ) (T : ℝ≥0) {n k : ℕ}
    (hn : 0 < n) (hk : 0 < k) :
    uniformSum (stoppedUniformSum B H T (n * k)) K T n =
      mixedSum B H K T n k := by
  have hp (j : ℕ) (hj : j ≤ n) :
      stoppedUniformSum B H T (n * k) (uniformGrid T n j) =
        integralSum B (uniformGrid T (n * k))
          (fun i => H (uniformGrid T (n * k) i)) (j * k) := by
    rw [← uniformGrid_refine T hn hk j]
    exact stoppedUniformSum_at_grid B H T (Nat.mul_le_mul_right k hj)
  funext ω
  dsimp only [mixedSum]
  rw [← integralSum_compose_refined B (uniformGrid T (n * k))
    (fun i => H (uniformGrid T (n * k) i)) (fun j => K (uniformGrid T n j)) n hk]
  unfold uniformSum integralSum
  apply Finset.sum_congr rfl
  intro i hi
  have hin : i + 1 ≤ n := Finset.mem_range.mp hi
  rw [hp (i + 1) hin, hp i (Nat.le_of_succ_le hin)]
  rfl

theorem uniformSum_memLp {M : ℝ≥0 → Ω → ℝ}
    (hM2 : ∀ t, MemLp (M t) 2 P) (hK : StronglyAdapted F K)
    {D : ℝ} (hbK : ∀ᵐ ω ∂P, ∀ t, |K t ω| ≤ D)
    (T : ℝ≥0) (n : ℕ) : MemLp (uniformSum M K T n) 2 P := by
  exact SimpleIntegral.coarseTransform_memLp (fun j => K (uniformGrid T n j))
    (fun j => ((hK _).mono (F.le _)).aestronglyMeasurable) (fun _ => D)
    (fun j => hbK.mono (fun ω hω => hω _)) (fun j => hM2 _) n

theorem mixedSum_outer_difference_tendsto
    (hB : IsPreBrownianReal B P) (hAd : StronglyAdapted F B)
    (hind : ∀ s t, s ≤ t → Indep
      (MeasurableSpace.comap (fun ω => B t ω - B s ω) inferInstance) (F s) P)
    (hH : StronglyAdapted F H) (hK : StronglyAdapted F K)
    {C D : ℝ} (hD : 0 ≤ D)
    (hbH : ∀ᵐ ω ∂P, ∀ t, |H t ω| ≤ C)
    (hbK : ∀ᵐ ω ∂P, ∀ t, |K t ω| ≤ D)
    {M : ℝ≥0 → Ω → ℝ} (hM : Martingale M F P)
    (hM2 : ∀ t, MemLp (M t) 2 P) (T : ℝ≥0)
    (hlim : Tendsto (fun n => ∫ ω,
      (uniformSum B H T n ω - M T ω) ^ 2 ∂P) atTop (𝓝 0)) :
    Tendsto (fun n => ∫ ω, (mixedSum B H K T (n + 1) (n + 1) ω -
      uniformSum M K T (n + 1) ω) ^ 2 ∂P) atTop (𝓝 0) := by
  let : IsProbabilityMeasure P := hB.isGaussianProcess.isProbabilityMeasure
  have hH2 (t : ℝ≥0) : MemLp (H t) 2 P := by
    apply MemLp.of_bound ((hH t).mono (F.le t)).aestronglyMeasurable C
    filter_upwards [hbH] with ω hω
    exact hω t
  let I (n : ℕ) := stoppedUniformSum B H T ((n + 1) * (n + 1))
  have hI2 (n : ℕ) (t : ℝ≥0) : MemLp (I n t) 2 P :=
    BrownianFiltration.stopped_predictable_sum_memLp_two hB hind _
      (uniformGrid_mono T _) _ (fun i => hH _) (fun i => hH2 _) _ t
  have hIM (n : ℕ) : Martingale (I n) F P := by
    apply BrownianFiltration.stopped_predictable_sum_martingale hB hAd hind _
      (uniformGrid_mono T _) _ (fun i => hH _) (fun _ => C) (fun i => ?_) _
    filter_upwards [hbH] with ω hω
    exact hω _
  have hcofinal : Tendsto (fun n : ℕ => (n + 1) * (n + 1)) atTop atTop := by
    apply tendsto_atTop.mpr
    intro b
    exact eventually_atTop.mpr ⟨b, fun n hn => hn.trans ((Nat.le_succ n).trans (Nat.le_mul_self _))⟩
  have hterminal : Tendsto (fun n => ∫ ω, (I n T ω - M T ω) ^ 2 ∂P)
      atTop (𝓝 0) := by
    simpa only [I, stoppedUniformSum_terminal, Function.comp_def] using hlim.comp hcofinal
  have herr := MartingaleTransformL2.tendsto_integral_sq_grid_transform
    (fun n => (hIM n).sub hM) (fun n t => (hI2 n t).sub (hM2 t))
    (fun n => uniformGrid T (n + 1)) (fun n => uniformGrid_mono T (n + 1))
    (fun n => n + 1) (fun n => uniformGrid_end T (Nat.succ_pos n))
    (fun n j => K (uniformGrid T (n + 1) j)) (fun n j => hK _) hD
    (fun n j => hbK.mono (fun ω hω => hω _)) hterminal
  refine herr.congr (fun n => ?_)
  rw [← uniformSum_stoppedUniformSum_eq_mixedSum B H K T
    (Nat.succ_pos n) (Nat.succ_pos n)]
  congr 1
  funext ω
  simp only [uniformSum, integralSum, Pi.sub_apply, I]
  rw [← Finset.sum_sub_distrib]
  congr 1
  apply Finset.sum_congr rfl
  intro i hi
  ring

theorem mixedSum_memLp
    (hB : IsPreBrownianReal B P)
    (hind : ∀ s t, s ≤ t → Indep
      (MeasurableSpace.comap (fun ω => B t ω - B s ω) inferInstance) (F s) P)
    (hH : StronglyAdapted F H) (hK : StronglyAdapted F K)
    {C D : ℝ} (hbH : ∀ᵐ ω ∂P, ∀ t, |H t ω| ≤ C)
    (hbK : ∀ᵐ ω ∂P, ∀ t, |K t ω| ≤ D)
    (T : ℝ≥0) {n k : ℕ} (hn : 0 < n) (hk : 0 < k) :
    MemLp (mixedSum B H K T n k) 2 P := by
  let : IsProbabilityMeasure P := hB.isGaussianProcess.isProbabilityMeasure
  have hH2 (t : ℝ≥0) : MemLp (H t) 2 P :=
    MemLp.of_bound ((hH t).mono (F.le t)).aestronglyMeasurable C
      (hbH.mono (fun ω hω => hω t))
  rw [← uniformSum_stoppedUniformSum_eq_mixedSum B H K T hn hk]
  exact uniformSum_memLp (fun t =>
    BrownianFiltration.stopped_predictable_sum_memLp_two hB hind _
      (uniformGrid_mono T _) _ (fun i => hH _) (fun i => hH2 _) _ t) hK hbK T n

theorem uniformSum_associativity
    (hB : IsPreBrownianReal B P) (hAd : StronglyAdapted F B)
    (hind : ∀ s t, s ≤ t → Indep
      (MeasurableSpace.comap (fun ω => B t ω - B s ω) inferInstance) (F s) P)
    (hH : StronglyAdapted F H) (hK : StronglyAdapted F K)
    (hcK : ∀ᵐ ω ∂P, Continuous (fun t => K t ω))
    {C D : ℝ} (hC : 0 ≤ C) (hD : 0 ≤ D)
    (hbH : ∀ᵐ ω ∂P, ∀ t, |H t ω| ≤ C)
    (hbK : ∀ᵐ ω ∂P, ∀ t, |K t ω| ≤ D)
    {M : ℝ≥0 → Ω → ℝ} (hM : Martingale M F P)
    (hM2 : ∀ t, MemLp (M t) 2 P) (T : ℝ≥0)
    (hlim : Tendsto (fun n => ∫ ω,
      (uniformSum B H T n ω - M T ω) ^ 2 ∂P) atTop (𝓝 0))
    {Z : Ω → ℝ} (hZ : MemLp Z 2 P)
    (hZlim : Tendsto (fun n => ∫ ω,
      (uniformSum B (fun t ω => K t ω * H t ω) T n ω - Z ω) ^ 2 ∂P)
      atTop (𝓝 0)) :
    Tendsto (fun n => ∫ ω, (uniformSum M K T n ω - Z ω) ^ 2 ∂P)
      atTop (𝓝 0) := by
  let : IsProbabilityMeasure P := hB.isGaussianProcess.isProbabilityMeasure
  have hH2 (t : ℝ≥0) : MemLp (H t) 2 P :=
    MemLp.of_bound ((hH t).mono (F.le t)).aestronglyMeasurable C
      (hbH.mono (fun ω hω => hω t))
  have hKH2 (t : ℝ≥0) : MemLp (fun ω => K t ω * H t ω) 2 P :=
    memLp_compose_of_bounded (hH2 t)
      ((hK t).mono (F.le t)).aestronglyMeasurable (hbK.mono (fun ω hω => hω t))
  have hproduct2 (n : ℕ) :
      MemLp (uniformSum B (fun t ω => K t ω * H t ω) T ((n + 1) * (n + 1))) 2 P :=
    BrownianFiltrationGrid.uniformSum_memLp hB hAd hind _
      (fun t => (hK t).mul (hH t)) hKH2 T _
  have hmixed2 (n : ℕ) : MemLp (mixedSum B H K T (n + 1) (n + 1)) 2 P :=
    mixedSum_memLp hB hind hH hK hbH hbK T (Nat.succ_pos n) (Nat.succ_pos n)
  have hcofinal : Tendsto (fun n : ℕ => (n + 1) * (n + 1)) atTop atTop := by
    apply tendsto_atTop.mpr
    intro b
    exact eventually_atTop.mpr ⟨b, fun n hn =>
      hn.trans ((Nat.le_succ n).trans (Nat.le_mul_self _))⟩
  have hproduct := hZlim.comp hcofinal
  have hclose := mixedSum_difference_tendsto hB hAd hind hH hK hcK hC hD hbH hbK T
  have hclose' : Tendsto (fun n => ∫ ω,
      (uniformSum B (fun t ω => K t ω * H t ω) T ((n + 1) * (n + 1)) ω -
        mixedSum B H K T (n + 1) (n + 1) ω) ^ 2 ∂P) atTop (𝓝 0) := by
    refine hclose.congr (fun n => ?_)
    apply integral_congr_ae
    exact Filter.Eventually.of_forall (fun ω => by ring)
  have hmixed := SimpleIntegral.meanSquare_limit_of_close hproduct2 hmixed2 hZ hclose' hproduct
  apply (tendsto_add_atTop_iff_nat 1).mp
  exact SimpleIntegral.meanSquare_limit_of_close hmixed2
    (fun n => uniformSum_memLp hM2 hK hbK T (n + 1)) hZ
    (mixedSum_outer_difference_tendsto hB hAd hind hH hK hD hbH hbK hM hM2 T hlim)
    hmixed

end Problem367.BrownianContinuousAssociativity

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
-- module Solutions.Q243_FreeIsing.FreeIsing_Brownian_SpatialAssociativity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal Topology

namespace Problem367.BrownianSpatialAssociativity

variable {Ω ι : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}

theorem uniformSum_memLp {M K : ℝ≥0 → Ω → ℝ}
    (hM2 : ∀ t, MemLp (M t) 2 P)
    (hK : ∀ t, AEStronglyMeasurable (K t) P)
    {C : ℝ} (hb : ∀ t, ∀ᵐ ω ∂P, |K t ω| ≤ C) (T : ℝ≥0) (n : ℕ) :
    MemLp (BrownianGrid.uniformSum M K T n) 2 P := by
  exact SimpleIntegral.coarseTransform_memLp
    (fun i => K (BrownianGrid.uniformGrid T n i))
    (fun i => hK _) (fun _ => C) (fun i => hb _)
    (fun i => hM2 (BrownianGrid.uniformGrid T n i)) n

end Problem367.BrownianSpatialAssociativity

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Martingales_RightContinuation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology ENNReal NNReal

namespace Problem367

theorem martingale_rightCont_of_L1_rightContinuous
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsFiniteMeasure P]
    {F : Filtration ℝ≥0 mΩ} {X : ℝ≥0 → Ω → ℝ}
    (hX : Martingale X F P)
    (hcont : ∀ s, Tendsto (fun t => eLpNorm (X t - X s) 1 P)
      (𝓝[>] s) (𝓝 0)) :
    Martingale X F.rightCont P := by
  have had : StronglyAdapted F.rightCont X :=
    fun s => (hX.stronglyAdapted s).mono (F.le_rightCont s)
  refine ⟨had, ?_⟩
  intro s t hst
  rcases hst.eq_or_lt with rfl | hst
  · exact (condExp_of_stronglyMeasurable (F.rightCont.le s) (had s)
      (hX.integrable s)).eventuallyEq
  · apply (ae_eq_condExp_of_forall_setIntegral_eq (F.rightCont.le s)
      (hX.integrable t) (fun A hA _ => (hX.integrable s).integrableOn) ?_
      (had s).aestronglyMeasurable).symm
    intro A hA hAfin
    have hlim := tendsto_setIntegral_of_L1' (X s) (hX.integrable s).aestronglyMeasurable
      (Eventually.of_forall hX.integrable) (hcont s) A
    have heq : ∀ᶠ u in 𝓝[>] s, (∫ ω in A, X u ω ∂P) = ∫ ω in A, X t ω ∂P := by
      filter_upwards [self_mem_nhdsWithin, (eventually_lt_nhds hst).filter_mono nhdsWithin_le_nhds]
        with u hsu hut
      have hFu : F.rightCont s ≤ F u := by
        rw [F.rightCont_eq]
        exact iInf₂_le u hsu
      exact hX.setIntegral_eq hut.le (hFu A hA)
    exact tendsto_nhds_unique hlim (tendsto_const_nhds.congr' (heq.mono (fun _ h => h.symm)))

end Problem367

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Martingales_DominatedMartingaleRightContinuation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal Topology ENNReal

namespace Problem367.DominatedMartingaleRightContinuation

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {μ : Measure Ω} [IsFiniteMeasure μ]
  {F : Filtration ℝ≥0 mΩ} {M : ℝ≥0 → Ω → ℝ}

omit [IsFiniteMeasure μ] in
theorem tendsto_L1_of_ae_continuous_dominated
    (hint : ∀ t, Integrable (M t) μ)
    (hc : ∀ᵐ ω ∂μ, Continuous (fun t => M t ω))
    (hdom : ∀ T : ℝ≥0, ∃ g : Ω → ℝ, Integrable g μ ∧
      ∀ᵐ ω ∂μ, ∀ t ≤ T, |M t ω| ≤ g ω) (s : ℝ≥0) :
    Tendsto (fun t => eLpNorm (M t - M s) 1 μ) (𝓝 s) (𝓝 0) := by
  obtain ⟨g, hg, hgb⟩ := hdom (s + 1)
  have hcont : ContinuousAt (fun t => ∫ ω, ‖M t ω - M s ω‖ ∂μ) s := by
    apply continuousAt_of_dominated
      (Eventually.of_forall (fun t => ((hint t).sub (hint s)).aestronglyMeasurable.norm))
      (bound := fun ω => 2 * g ω)
    · filter_upwards [eventually_lt_nhds (lt_add_one s)] with t ht
      filter_upwards [hgb] with ω hω
      have hst : s ≤ s + 1 := le_add_of_nonneg_right zero_le
      have hb := (norm_sub_le (M t ω) (M s ω)).trans
        (add_le_add (hω t ht.le) (hω s hst))
      simpa only [Pi.sub_apply, norm_norm, two_mul] using hb
    · exact hg.const_mul 2
    · filter_upwards [hc] with ω hω
      exact (hω.sub continuous_const).norm.continuousAt
  have heq (t : ℝ≥0) : eLpNorm (M t - M s) 1 μ =
      ENNReal.ofReal (∫ ω, ‖M t ω - M s ω‖ ∂μ) := by
    rw [eLpNorm_one_eq_lintegral_enorm,
      ← ofReal_integral_norm_eq_lintegral_enorm ((hint t).sub (hint s))]
    rfl
  simp_rw [heq]
  simpa only [Function.comp_def, sub_self, norm_zero, integral_zero, ENNReal.ofReal_zero] using
    (ENNReal.continuous_ofReal.continuousAt.comp hcont).tendsto

theorem martingale_rightCont_of_ae_continuous_dominated
    (hM : Martingale M F μ)
    (hc : ∀ᵐ ω ∂μ, Continuous (fun t => M t ω))
    (hdom : ∀ T : ℝ≥0, ∃ g : Ω → ℝ, Integrable g μ ∧
      ∀ᵐ ω ∂μ, ∀ t ≤ T, |M t ω| ≤ g ω) :
    Martingale M F.rightCont μ := by
  apply Problem367.martingale_rightCont_of_L1_rightContinuous hM
  intro s
  exact (tendsto_L1_of_ae_continuous_dominated hM.integrable hc hdom s).mono_left
    nhdsWithin_le_nhds

end Problem367.DominatedMartingaleRightContinuation

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Martingales_L2MartingaleRightContinuation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Filter
open scoped NNReal Topology

namespace Problem367.DominatedMartingaleRightContinuation

theorem martingale_rightCont_of_ae_continuous_memLp_two
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {μ : Measure Ω} [IsFiniteMeasure μ]
    {F : Filtration ℝ≥0 mΩ} {M : ℝ≥0 → Ω → ℝ}
    (hM : Martingale M F μ) (hM2 : ∀ t, MemLp (M t) 2 μ)
    (hc : ∀ᵐ ω ∂μ, Continuous (fun t => M t ω)) :
    Martingale M F.rightCont μ := by
  apply martingale_rightCont_of_ae_continuous_dominated hM hc
  intro T
  refine ⟨fun ω => 1 + MartingaleStrongMaximal.maximalSquare M T ω,
    (integrable_const 1).add (MartingaleStrongMaximal.integrable_maximalSquare hM hM2 hc T), ?_⟩
  filter_upwards [MartingaleStrongMaximal.ae_all_sq_le_maximalSquare hM hM2 hc T] with ω hω
  intro t ht
  apply abs_le.mpr
  have hsq := hω t ht
  constructor <;> nlinarith [sq_nonneg (M t ω - 1), sq_nonneg (M t ω + 1)]

end Problem367.DominatedMartingaleRightContinuation

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Martingales_RandomEvaluation
attribute [-instance] _root_.OAI.Problem367.WienerSampler.pathMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Filter Set
open scoped NNReal Topology

namespace Problem367.MartingaleRandomEvaluation

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}

theorem stronglyMeasurable_random_evaluation
    {F : Filtration ℝ≥0 mΩ} {M : ℝ≥0 → Ω → ℝ}
    (hp : IsStronglyProgressive F M) {τ : Ω → ℝ≥0} (hτ : Measurable τ)
    {T : ℝ≥0} (hbound : ∀ ω, τ ω ≤ T) :
    StronglyMeasurable (fun ω => M (τ ω) ω) := by
  have hm : StronglyMeasurable (fun p : Iic T × Ω => M p.1 p.2) :=
    (hp T).mono (sup_le_sup le_rfl (MeasurableSpace.comap_mono (F.le T)))
  let τ' : Ω → Iic T := fun ω => ⟨τ ω, hbound ω⟩
  have ht : Measurable τ' := hτ.subtype_mk
  exact hm.comp_measurable (ht.prodMk measurable_id)

theorem aestronglyMeasurable_random_evaluation
    {F : Filtration ℝ≥0 mΩ} {M : ℝ≥0 → Ω → ℝ}
    (hM : StronglyAdapted F M)
    (hc : ∀ᵐ ω ∂P, Continuous (fun t => M t ω))
    {τ : Ω → ℝ≥0} (hτ : Measurable τ) {T : ℝ≥0} (hbound : ∀ ω, τ ω ≤ T) :
    AEStronglyMeasurable (fun ω => M (τ ω) ω) P := by
  have hm := stronglyMeasurable_random_evaluation
    (PredictableMesh.repair_isStronglyPredictable hM).isStronglyProgressive hτ hbound
  apply hm.aestronglyMeasurable.congr
  filter_upwards [hc] with ω hω
  exact PredictableMesh.repair_eq_of_continuousOn (T := τ ω) hω.continuousOn le_rfl

theorem integrable_sq_random_evaluation [IsFiniteMeasure P]
    {F : Filtration ℝ≥0 mΩ} {M : ℝ≥0 → Ω → ℝ}
    (hM : Martingale M F P) (h2 : ∀ t, MemLp (M t) 2 P)
    (hc : ∀ᵐ ω ∂P, Continuous (fun t => M t ω))
    {τ : Ω → ℝ≥0} (hτ : Measurable τ) {T : ℝ≥0} (hbound : ∀ ω, τ ω ≤ T) :
    Integrable (fun ω => M (τ ω) ω ^ 2) P := by
  apply (MartingaleStrongMaximal.integrable_maximalSquare hM h2 hc T).mono'
    ((aestronglyMeasurable_random_evaluation hM.stronglyAdapted hc hτ hbound).pow 2)
  filter_upwards [MartingaleStrongMaximal.ae_all_sq_le_maximalSquare hM h2 hc T] with ω hω
  change ‖M (τ ω) ω ^ 2‖ ≤ _
  simpa only [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg (M (τ ω) ω))] using
    hω (τ ω) (hbound ω)

theorem memLp_random_evaluation [IsFiniteMeasure P]
    {F : Filtration ℝ≥0 mΩ} {M : ℝ≥0 → Ω → ℝ}
    (hM : Martingale M F P) (h2 : ∀ t, MemLp (M t) 2 P)
    (hc : ∀ᵐ ω ∂P, Continuous (fun t => M t ω))
    {τ : Ω → ℝ≥0} (hτ : Measurable τ) {T : ℝ≥0} (hbound : ∀ ω, τ ω ≤ T) :
    MemLp (fun ω => M (τ ω) ω) 2 P :=
  (memLp_two_iff_integrable_sq
    (aestronglyMeasurable_random_evaluation hM.stronglyAdapted hc hτ hbound)).mpr
      (integrable_sq_random_evaluation hM h2 hc hτ hbound)

theorem integral_sq_random_evaluation_le [IsFiniteMeasure P]
    {F : Filtration ℝ≥0 mΩ} {M : ℝ≥0 → Ω → ℝ}
    (hM : Martingale M F P) (h2 : ∀ t, MemLp (M t) 2 P)
    (hc : ∀ᵐ ω ∂P, Continuous (fun t => M t ω))
    {τ : Ω → ℝ≥0} (hτ : Measurable τ) {T : ℝ≥0} (hbound : ∀ ω, τ ω ≤ T) :
    (∫ ω, M (τ ω) ω ^ 2 ∂P) ≤ 4 * ∫ ω, M T ω ^ 2 ∂P := by
  apply le_trans (integral_mono_ae
    (integrable_sq_random_evaluation hM h2 hc hτ hbound)
    (MartingaleStrongMaximal.integrable_maximalSquare hM h2 hc T) ?_)
    (MartingaleStrongMaximal.integral_maximalSquare_le hM h2 hc T)
  filter_upwards [MartingaleStrongMaximal.ae_all_sq_le_maximalSquare hM h2 hc T] with ω hω
  exact hω (τ ω) (hbound ω)

end Problem367.MartingaleRandomEvaluation

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Martingales_StoppedMartingaleL2
attribute [-instance] _root_.OAI.Problem367.WienerSampler.pathMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Filter
open scoped NNReal Topology

namespace Problem367.StoppedMartingaleL2

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {μ : Measure Ω} [IsFiniteMeasure μ]
  {F : Filtration ℝ≥0 mΩ} {M L : ℝ≥0 → Ω → ℝ} {τ : Ω → WithTop ℝ≥0}

theorem measurable_cappedTime (hτ : IsStoppingTime F τ) (t : ℝ≥0) :
    Measurable (fun ω => (min (t : WithTop ℝ≥0) (τ ω)).untopA) :=
  WithTop.measurable_untopA.comp (measurable_const.min (hτ.measurable.mono hτ.measurableSpace_le le_rfl))

theorem memLp_stoppedProcess_two
    (hM : Martingale M F μ) (h2 : ∀ t, MemLp (M t) 2 μ)
    (hc : ∀ᵐ ω ∂μ, Continuous (fun t => M t ω))
    (hτ : IsStoppingTime F τ) (t : ℝ≥0) :
    MemLp (stoppedProcess M τ t) 2 μ :=
  MartingaleRandomEvaluation.memLp_random_evaluation hM h2 hc
    (measurable_cappedTime hτ t) (fun _ => WithTop.untopA_le (min_le_left _ _))

theorem integral_stoppedProcess_sq_le
    (hM : Martingale M F μ) (h2 : ∀ t, MemLp (M t) 2 μ)
    (hc : ∀ᵐ ω ∂μ, Continuous (fun t => M t ω))
    (hτ : IsStoppingTime F τ) {t T : ℝ≥0} (ht : t ≤ T) :
    (∫ ω, (stoppedProcess M τ t ω) ^ 2 ∂μ) ≤ 4 * ∫ ω, (M T ω) ^ 2 ∂μ :=
  MartingaleRandomEvaluation.integral_sq_random_evaluation_le hM h2 hc
    (measurable_cappedTime hτ t)
    (fun _ => (WithTop.untopA_le (min_le_left _ _)).trans ht)

theorem integral_stoppedProcess_sub_sq_le
    (hM : Martingale M F μ) (hL : Martingale L F μ)
    (hM2 : ∀ t, MemLp (M t) 2 μ) (hL2 : ∀ t, MemLp (L t) 2 μ)
    (hcM : ∀ᵐ ω ∂μ, Continuous (fun t => M t ω))
    (hcL : ∀ᵐ ω ∂μ, Continuous (fun t => L t ω))
    (hτ : IsStoppingTime F τ) {t T : ℝ≥0} (ht : t ≤ T) :
    (∫ ω, (stoppedProcess M τ t ω - stoppedProcess L τ t ω) ^ 2 ∂μ) ≤
      4 * ∫ ω, (M T ω - L T ω) ^ 2 ∂μ := by
  have hc : ∀ᵐ ω ∂μ, Continuous (fun t => (M - L) t ω) := by
    filter_upwards [hcM, hcL] with ω hm hl
    exact hm.sub hl
  simpa only [stoppedProcess, Pi.sub_apply] using
    integral_stoppedProcess_sq_le (hM.sub hL) (fun t => (hM2 t).sub (hL2 t)) hc hτ ht

theorem tendsto_stoppedProcess_meanSquare
    {N : ℕ → ℝ≥0 → Ω → ℝ}
    (hN : ∀ n, Martingale (N n) F μ) (hL : Martingale L F μ)
    (hN2 : ∀ n t, MemLp (N n t) 2 μ) (hL2 : ∀ t, MemLp (L t) 2 μ)
    (hcN : ∀ n, ∀ᵐ ω ∂μ, Continuous (fun t => N n t ω))
    (hcL : ∀ᵐ ω ∂μ, Continuous (fun t => L t ω))
    (τn : ℕ → Ω → WithTop ℝ≥0) (hτn : ∀ n, IsStoppingTime F (τn n))
    {t T : ℝ≥0} (ht : t ≤ T)
    (hlim : Tendsto (fun n => ∫ ω, (N n T ω - L T ω) ^ 2 ∂μ) atTop (𝓝 0)) :
    Tendsto (fun n => ∫ ω,
      (stoppedProcess (N n) (τn n) t ω - stoppedProcess L (τn n) t ω) ^ 2 ∂μ)
      atTop (𝓝 0) := by
  apply squeeze_zero (fun n => integral_nonneg (fun ω => sq_nonneg _))
    (fun n => integral_stoppedProcess_sub_sq_le (hN n) hL
      (hN2 n) hL2 (hcN n) hcL (hτn n) ht)
  simpa only [mul_zero] using hlim.const_mul 4

end Problem367.StoppedMartingaleL2

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Stochastic_RandomStoppedSimpleIntegral
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory
open scoped NNReal
namespace Problem367.RandomStoppedSimpleIntegral

variable {Ω I : Type*} [LinearOrder I] [Nonempty I]

theorem stoppedProcess_min (B : I → Ω → ℝ) (τ : Ω → WithTop I) (a t : I) (ω : Ω) :
    stoppedProcess B τ (min t a) ω =
      B (min (min (t : WithTop I) (τ ω)).untopA a) ω := by
  rcases eq_or_ne (τ ω) ⊤ with hτ | hτ
  · simp only [stoppedProcess, hτ, min_eq_left le_top]
    rfl
  · obtain ⟨s, hs⟩ := WithTop.ne_top_iff_exists.mp hτ
    simp only [stoppedProcess, ← hs, ← WithTop.coe_min]
    change B (min (min t a) s) ω = B (min (min t s) a) ω
    rw [min_right_comm t a s]

theorem stopped_intervalSum_integrator (B : I → Ω → ℝ) (H : Ω → ℝ)
    (τ : Ω → WithTop I) (a b t : I) (ω : Ω) :
    stoppedProcess (StoppedSimpleIntegral.intervalSum B H a b) τ t ω =
      StoppedSimpleIntegral.intervalSum (stoppedProcess B τ) H a b t ω := by
  rw [StoppedSimpleIntegral.intervalSum, stoppedProcess_min, stoppedProcess_min]
  rfl

theorem stopped_finite_intervalSum {J : Type*} (s : Finset J)
    (B : I → Ω → ℝ) (H : J → Ω → ℝ) (a b : J → I) (τ : Ω → WithTop I) :
    stoppedProcess (fun t ω => ∑ i ∈ s,
      StoppedSimpleIntegral.intervalSum B (H i) (a i) (b i) t ω) τ =
    fun t ω => ∑ i ∈ s,
      StoppedSimpleIntegral.intervalSum (stoppedProcess B τ) (H i) (a i) (b i) t ω := by
  funext t ω
  change (∑ i ∈ s, stoppedProcess
    (StoppedSimpleIntegral.intervalSum B (H i) (a i) (b i)) τ t ω) = _
  exact Finset.sum_congr rfl fun i hi =>
    stopped_intervalSum_integrator B (H i) τ (a i) (b i) t ω

end Problem367.RandomStoppedSimpleIntegral

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

theorem stoppedUniformSum_martingale [IsFiniteMeasure P]
    {M K : ℝ≥0 → Ω → ℝ} {F : Filtration ℝ≥0 mΩ}
    (hM : Martingale M F P) (hK : StronglyAdapted F K)
    {D : ℝ} (hbK : ∀ᵐ ω ∂P, ∀ t, |K t ω| ≤ D) (T : ℝ≥0) (n : ℕ) :
    Martingale (stoppedUniformSum M K T n) F P := by
  apply StoppedSimpleIntegral.finite_intervalSum_martingale hM (Finset.range n)
    (uniformGrid T n) (fun i => uniformGrid T n (i + 1))
    (fun i => K (uniformGrid T n i))
    (fun i _ => uniformGrid_mono T n (Nat.le_succ i))
    (fun i _ => hK _) (fun _ => D)
  intro i hi
  filter_upwards [hbK] with ω hω
  exact hω _

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

theorem tendsto_stopped_outer_uniformSum [IsFiniteMeasure P]
    {M K J : ℝ≥0 → Ω → ℝ} {F : Filtration ℝ≥0 mΩ}
    (hM : Martingale M F P) (hM2 : ∀ t, MemLp (M t) 2 P)
    (hcM : ∀ᵐ ω ∂P, Continuous (fun t => M t ω))
    (hK : StronglyAdapted F K) {D : ℝ}
    (hbK : ∀ᵐ ω ∂P, ∀ t, |K t ω| ≤ D)
    (hJ : Martingale J F P) (hJ2 : ∀ t, MemLp (J t) 2 P)
    (hcJ : ∀ᵐ ω ∂P, Continuous (fun t => J t ω)) (T : ℝ≥0)
    (hlim : Tendsto (fun n => ∫ ω,
      (uniformSum M K T n ω - J T ω) ^ 2 ∂P) atTop (𝓝 0))
    {τ : Ω → WithTop ℝ≥0} (hτ : IsStoppingTime F τ) :
    Tendsto (fun n => ∫ ω,
      (uniformSum (stoppedProcess M τ) K T n ω - stoppedProcess J τ T ω) ^ 2 ∂P)
      atTop (𝓝 0) := by
  have hterminal : Tendsto (fun n => ∫ ω,
      (stoppedUniformSum M K T n T ω - J T ω) ^ 2 ∂P) atTop (𝓝 0) := by
    simpa only [stoppedUniformSum_terminal] using hlim
  have h := StoppedMartingaleL2.tendsto_stoppedProcess_meanSquare
    (N := fun n => stoppedUniformSum M K T n) (L := J) (t := T) (T := T)
    (fun n => stoppedUniformSum_martingale hM hK hbK T n) hJ
    (fun n t => stoppedUniformSum_memLp hM2 hK hbK T n t) hJ2
    (ae_continuous_stoppedUniformSum hcM T) hcJ (fun _ => τ) (fun _ => hτ)
    le_rfl hterminal
  have heq (n : ℕ) : stoppedProcess (stoppedUniformSum M K T n) τ T =
      uniformSum (stoppedProcess M τ) K T n := by
    have hfinite := RandomStoppedSimpleIntegral.stopped_finite_intervalSum
      (Finset.range n) M (fun i => K (uniformGrid T n i))
      (uniformGrid T n) (fun i => uniformGrid T n (i + 1)) τ
    have ht := congrArg (fun S => S T) hfinite
    change stoppedProcess (stoppedUniformSum M K T n) τ T =
      stoppedUniformSum (stoppedProcess M τ) K T n T at ht
    simpa only [stoppedUniformSum_terminal] using ht
  simpa only [heq] using h

end Problem367.StoppedIntegralAssociativity

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Stochastic_StoppedIntegralLocality
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped NNReal Topology

namespace Problem367.StoppedIntegralLocality

variable {Ω : Type*}

theorem uniformSum_stopped_congr (M H K : ℝ≥0 → Ω → ℝ)
    (τ : Ω → WithTop ℝ≥0) (T : ℝ≥0) (n : ℕ) (ω : Ω)
    (hlocal : ∀ t : ℝ≥0, (t : WithTop ℝ≥0) ≤ τ ω → H t ω = K t ω) :
    BrownianGrid.uniformSum (stoppedProcess M τ) H T n ω =
      BrownianGrid.uniformSum (stoppedProcess M τ) K T n ω := by
  unfold BrownianGrid.uniformSum BrownianGrid.integralSum
  apply Finset.sum_congr rfl
  intro i hi
  dsimp only
  by_cases ht : (BrownianGrid.uniformGrid T n i : WithTop ℝ≥0) ≤ τ ω
  · rw [hlocal _ ht]
  · have ha : τ ω ≤ (BrownianGrid.uniformGrid T n i : WithTop ℝ≥0) :=
      le_of_not_ge ht
    have hab : (BrownianGrid.uniformGrid T n i : WithTop ℝ≥0) ≤
        (BrownianGrid.uniformGrid T n (i + 1) : WithTop ℝ≥0) := by
      exact_mod_cast BrownianGrid.uniformGrid_mono T n (Nat.le_succ i)
    rw [stoppedProcess_eq_of_ge ha, stoppedProcess_eq_of_ge (ha.trans hab)]
    simp only [sub_self, mul_zero]

variable [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsFiniteMeasure P]

theorem stopped_integral_eq_of_local_eq
    {F : Filtration ℝ≥0 mΩ} {M H K I J : ℝ≥0 → Ω → ℝ}
    (hM : Martingale M F P) (hM2 : ∀ t, MemLp (M t) 2 P)
    (hcM : ∀ᵐ ω ∂P, Continuous (fun t => M t ω))
    (hH : StronglyAdapted F H) (hK : StronglyAdapted F K)
    {C D : ℝ} (hbH : ∀ᵐ ω ∂P, ∀ t, |H t ω| ≤ C)
    (hbK : ∀ᵐ ω ∂P, ∀ t, |K t ω| ≤ D)
    (hI : Martingale I F P) (hJ : Martingale J F P)
    (hI2 : ∀ t, MemLp (I t) 2 P) (hJ2 : ∀ t, MemLp (J t) 2 P)
    (hcI : ∀ᵐ ω ∂P, Continuous (fun t => I t ω))
    (hcJ : ∀ᵐ ω ∂P, Continuous (fun t => J t ω))
    (T : ℝ≥0)
    (hIlim : Tendsto (fun n => ∫ ω,
      (BrownianGrid.uniformSum M H T n ω - I T ω) ^ 2 ∂P) atTop (𝓝 0))
    (hJlim : Tendsto (fun n => ∫ ω,
      (BrownianGrid.uniformSum M K T n ω - J T ω) ^ 2 ∂P) atTop (𝓝 0))
    {τ : Ω → WithTop ℝ≥0} (hτ : IsStoppingTime F τ)
    (hlocal : ∀ᵐ ω ∂P, ∀ t : ℝ≥0, (t : WithTop ℝ≥0) ≤ τ ω → H t ω = K t ω) :
    stoppedProcess I τ T =ᵐ[P] stoppedProcess J τ T := by
  have hIs := StoppedMartingaleL2.memLp_stoppedProcess_two hI hI2 hcI hτ T
  have hJs := StoppedMartingaleL2.memLp_stoppedProcess_two hJ hJ2 hcJ hτ T
  have hMs (t : ℝ≥0) :=
    StoppedMartingaleL2.memLp_stoppedProcess_two hM hM2 hcM hτ t
  have hX (n : ℕ) : MemLp (BrownianGrid.uniformSum (stoppedProcess M τ) H T n) 2 P :=
    BrownianSpatialAssociativity.uniformSum_memLp hMs
      (fun t => ((hH t).mono (F.le t)).aestronglyMeasurable)
      (fun t => hbH.mono (fun ω hω => hω t)) T n
  have hi := StoppedIntegralAssociativity.tendsto_stopped_outer_uniformSum
    hM hM2 hcM hH hbH hI hI2 hcI T hIlim hτ
  have hj := StoppedIntegralAssociativity.tendsto_stopped_outer_uniformSum
    hM hM2 hcM hK hbK hJ hJ2 hcJ T hJlim hτ
  apply BrownianGrid.ae_eq_of_mean_square_limits hX hIs hJs hi
  apply hj.congr
  intro n
  apply integral_congr_ae
  filter_upwards [hlocal] with ω hω
  rw [uniformSum_stopped_congr M H K τ T n ω hω]

end Problem367.StoppedIntegralLocality

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Martingales_StoppedRowNormalization
attribute [-instance] _root_.OAI.Problem367.WienerSampler.pathMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped NNReal Topology

namespace Problem367.StoppedRowNormalization
open BrownianGrid BrownianIntegralProcess DominatedMartingaleRightContinuation

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}

theorem stopped_channel_normalization_oai
    {F : Filtration ℝ≥0 mΩ} {B C R K I J : ℝ≥0 → Ω → ℝ}
    (hB : IsPreBrownianReal B P) (hAd : StronglyAdapted F B)
    (hind : ∀ s t, s ≤ t → Indep
      (MeasurableSpace.comap (fun ω => B t ω - B s ω) inferInstance) (F s) P)
    (hcB : ∀ᵐ ω ∂P, Continuous (fun t => B t ω))
    (hC : StronglyAdapted F C) (hR : StronglyAdapted F R) (hK : StronglyAdapted F K)
    (hcC : ∀ᵐ ω ∂P, Continuous (fun t => C t ω))
    (hcK : ∀ᵐ ω ∂P, Continuous (fun t => K t ω))
    {a b c : ℝ} (ha : 0 ≤ a) (hc : 0 ≤ c)
    (hbC : ∀ᵐ ω ∂P, ∀ t, |C t ω| ≤ a)
    (hbR : ∀ᵐ ω ∂P, ∀ t, |R t ω| ≤ b)
    (hbK : ∀ᵐ ω ∂P, ∀ t, |K t ω| ≤ c)
    (hI : Martingale I F P) (hJ : Martingale J F P)
    (hI2 : ∀ t, MemLp (I t) 2 P) (hJ2 : ∀ t, MemLp (J t) 2 P)
    (hcI : ∀ᵐ ω ∂P, Continuous (fun t => I t ω))
    (hcJ : ∀ᵐ ω ∂P, Continuous (fun t => J t ω))
    (T : ℝ≥0)
    (hIlim : Tendsto (fun n => ∫ ω,
      (uniformSum B C T n ω - I T ω) ^ 2 ∂P) atTop (𝓝 0))
    (hJlim : Tendsto (fun n => ∫ ω,
      (uniformSum B R T n ω - J T ω) ^ 2 ∂P) atTop (𝓝 0))
    {τ : Ω → WithTop ℝ≥0} (hτ : IsStoppingTime F.rightCont τ)
    (hlocal : ∀ᵐ ω ∂P, ∀ t : ℝ≥0, (t : WithTop ℝ≥0) ≤ τ ω →
      K t ω * C t ω = R t ω) :
    Tendsto (fun n => ∫ ω,
      (uniformSum (stoppedProcess I τ) K T n ω - stoppedProcess J τ T ω) ^ 2 ∂P)
      atTop (𝓝 0) := by
  let : IsProbabilityMeasure P := hB.isGaussianProcess.isProbabilityMeasure
  have hKC : StronglyAdapted F (fun t ω => K t ω * C t ω) :=
    fun t => (hK t).mul (hC t)
  have hcKC : ∀ᵐ ω ∂P, Continuous (fun t => K t ω * C t ω) :=
    (hcK.and hcC).mono (fun ω hω => hω.1.mul hω.2)
  have hbKC : ∀ᵐ ω ∂P, ∀ t, |K t ω * C t ω| ≤ c * a := by
    filter_upwards [hbK, hbC] with ω hk hcω
    intro t
    exact (abs_mul _ _).trans_le (mul_le_mul (hk t) (hcω t) (abs_nonneg _) hc)
  obtain ⟨L, hLp, hL, hcL, hL2, _, _, _, _, hLlim⟩ :=
    exists_continuous_stopped_uniform_integral hB hAd hind hcB hKC hcKC
      (mul_nonneg hc ha) hbKC T
  have hLterminal : Tendsto (fun n => ∫ ω,
      (uniformSum B (fun t ω => K t ω * C t ω) T n ω - L T ω) ^ 2 ∂P)
        atTop (𝓝 0) := by
    simpa only [stoppedUniformSum_terminal] using hLlim T
  have houter := BrownianContinuousAssociativity.uniformSum_associativity
    hB hAd hind hC hK hcK ha hc hbC hbK hI hI2 T hIlim (hL2 T) hLterminal
  have hIright := martingale_rightCont_of_ae_continuous_memLp_two hI hI2 hcI
  have hJright := martingale_rightCont_of_ae_continuous_memLp_two hJ hJ2 hcJ
  have hLright := martingale_rightCont_of_ae_continuous_memLp_two hL hL2 hcL
  have hKright : StronglyAdapted F.rightCont K :=
    fun t => (hK t).mono (F.le_rightCont t)
  have hstop := StoppedIntegralAssociativity.tendsto_stopped_outer_uniformSum
    hIright hI2 hcI hKright hbK hLright hL2 hcL T houter hτ
  have hBM := BrownianFiltration.martingale_of_independent_past hB hAd hind
  have hB2 (t : ℝ≥0) := (hB.isGaussianProcess.hasGaussianLaw_eval t).memLp_two
  have hBright := martingale_rightCont_of_ae_continuous_memLp_two hBM hB2 hcB
  have heq := StoppedIntegralLocality.stopped_integral_eq_of_local_eq
    hBright hB2 hcB (fun t => (hKC t).mono (F.le_rightCont t))
    (fun t => (hR t).mono (F.le_rightCont t)) hbKC hbR
    hLright hJright hL2 hJ2 hcL hcJ T hLterminal hJlim hτ hlocal
  apply hstop.congr
  intro n
  apply integral_congr_ae
  filter_upwards [heq] with ω hω
  rw [hω]

end Problem367.StoppedRowNormalization

end

end OAI
end

theorem solution.{u_1} : type_of% @OAI.Problem367.StoppedRowNormalization.stopped_channel_normalization_oai.{u_1} := @OAI.Problem367.StoppedRowNormalization.stopped_channel_normalization_oai.{u_1}
