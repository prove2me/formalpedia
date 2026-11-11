-- Prove2me | solution 1 for OAI.Problem367.StoppedRowNormalization.stopped_row_normalization
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T01:40:05.190874+00:00
-- url     : https://prove2.me/submissions/501c0e48-5cde-4df5-bc4c-c310a5419f8d

import Mathlib
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Probability.Process.Stopping
import Definitions.Def_Q243FI001
import Theorems.Thm_OAI_Problem367_StoppedRowNormalization_stopped_channel_normalization

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

end Problem367.SimpleIntegral

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

end Problem367.MartingaleTransformL2

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
-- module Solutions.Q243_FreeIsing.FreeIsing_Martingales_StrongMaximal
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

theorem finiteSum_ae_continuous {M : ι → ℝ≥0 → Ω → ℝ}
    (hc : ∀ i, ∀ᵐ ω ∂μ, Continuous (fun t => M i t ω)) (s : Finset ι) :
    ∀ᵐ ω ∂μ, Continuous (fun t => finiteSum M s t ω) := by
  have hall : ∀ᵐ ω ∂μ, ∀ i ∈ s, Continuous (fun t => M i t ω) :=
    (Filter.eventually_all_finite s.finite_toSet).mpr (fun i _ => hc i)
  filter_upwards [hall] with ω hω
  exact continuous_finsetSum s hω

end Problem367.MartingaleSpatialLimit

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

theorem tendsto_integral_sq_fintype_sum_error
    {ι α : Type*} [Fintype ι] {l : Filter α}
    {I : ι → Ω → ℝ} {S : ι → α → Ω → ℝ}
    (hI : ∀ i, MemLp (I i) 2 μ) (hS : ∀ i n, MemLp (S i n) 2 μ)
    (hlim : ∀ i, Tendsto (fun n => ∫ ω, (S i n ω - I i ω) ^ 2 ∂μ) l (𝓝 0)) :
    Tendsto (fun n => ∫ ω, ((∑ i, S i n ω) - ∑ i, I i ω) ^ 2 ∂μ) l (𝓝 0) := by
  classical
  have h := tendsto_finsetSum Finset.univ (fun i _ =>
    tendsto_toLp_of_integral_sq_error (hS i) (hI i) (hlim i))
  have hn := (h.sub (tendsto_const_nhds (x := ∑ i, (hI i).toLp (I i)))).norm.pow 2
  simp only [sub_self, norm_zero, zero_pow (by decide : 2 ≠ 0)] at hn
  apply hn.congr'
  apply Eventually.of_forall
  intro n
  have he := PredictableL2.norm_toLp_sq
    ((memLp_finsetSum Finset.univ (fun i _ => hS i n)).sub
      (memLp_finsetSum Finset.univ (fun i _ => hI i)))
  change ‖(memLp_finsetSum Finset.univ (fun i _ => hS i n)).toLp
    (fun ω => ∑ i, S i n ω) - (memLp_finsetSum Finset.univ (fun i _ => hI i)).toLp
    (fun ω => ∑ i, I i ω)‖ ^ 2 = _ at he
  rw [PredictableL2.toLp_finsetSum, PredictableL2.toLp_finsetSum] at he
  exact he

end RandomVariables

end Problem367.FilteringRepresentationClosure

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

private theorem tendsto_zero_of_uniform_approximation
    {A N : Type*} {l : Filter N} {k : Filter A} [k.NeBot]
    {f : N → ℝ} {g : A → N → ℝ} {r : A → ℝ}
    (h0 : ∀ n, 0 ≤ f n) (hr : Tendsto r k (𝓝 0))
    (hg : ∀ a, Tendsto (g a) l (𝓝 0))
    (hb : ∀ a n, f n ≤ r a + g a n) : Tendsto f l (𝓝 0) := by
  refine tendsto_order.2 ⟨?_, ?_⟩
  · intro a ha
    exact Eventually.of_forall (fun n => ha.trans_le (h0 n))
  · intro b hb0
    obtain ⟨a, ha⟩ := (hr.eventually (gt_mem_nhds (half_pos hb0))).exists
    filter_upwards [(hg a).eventually (gt_mem_nhds (half_pos hb0))] with n hn
    linarith [hb a n]

omit mΩ in
theorem uniformSum_finiteSum (I : ι → ℝ≥0 → Ω → ℝ)
    (K : ℝ≥0 → Ω → ℝ) (q : Finset ι) (T : ℝ≥0) (n : ℕ) :
    BrownianGrid.uniformSum (MartingaleSpatialLimit.finiteSum I q) K T n =
      fun ω => ∑ a ∈ q, BrownianGrid.uniformSum (I a) K T n ω := by
  funext ω
  simp only [BrownianGrid.uniformSum, BrownianGrid.integralSum,
    MartingaleSpatialLimit.finiteSum]
  simp_rw [← Finset.sum_sub_distrib, Finset.mul_sum]
  rw [Finset.sum_comm]

theorem uniformSum_memLp {M K : ℝ≥0 → Ω → ℝ}
    (hM2 : ∀ t, MemLp (M t) 2 P)
    (hK : ∀ t, AEStronglyMeasurable (K t) P)
    {C : ℝ} (hb : ∀ t, ∀ᵐ ω ∂P, |K t ω| ≤ C) (T : ℝ≥0) (n : ℕ) :
    MemLp (BrownianGrid.uniformSum M K T n) 2 P := by
  exact SimpleIntegral.coarseTransform_memLp
    (fun i => K (BrownianGrid.uniformGrid T n i))
    (fun i => hK _) (fun _ => C) (fun i => hb _)
    (fun i => hM2 (BrownianGrid.uniformGrid T n i)) n

theorem uniformSum_spatial_tail_le [IsFiniteMeasure P]
    {F : Filtration ℝ≥0 mΩ} {I : ι → ℝ≥0 → Ω → ℝ}
    {Y K : ℝ≥0 → Ω → ℝ}
    (hI : ∀ a, Martingale (I a) F P) (hY : Martingale Y F P)
    (hI2 : ∀ a t, MemLp (I a t) 2 P) (hY2 : ∀ t, MemLp (Y t) 2 P)
    (hK : StronglyAdapted F K) {C : ℝ} (hC : 0 ≤ C)
    (hb : ∀ t, ∀ᵐ ω ∂P, |K t ω| ≤ C) (q : Finset ι) (T : ℝ≥0) (n : ℕ) :
    (∫ ω, (BrownianGrid.uniformSum Y K T n ω -
      BrownianGrid.uniformSum (MartingaleSpatialLimit.finiteSum I q) K T n ω) ^ 2 ∂P) ≤
      C ^ 2 * ∫ ω, (Y T ω - ∑ a ∈ q, I a T ω) ^ 2 ∂P := by
  by_cases hn : n = 0
  · subst n
    simp only [BrownianGrid.uniformSum, BrownianGrid.integralSum,
      Finset.range_zero, Finset.sum_empty, sub_self, zero_pow (by decide : 2 ≠ 0), integral_zero]
    exact mul_nonneg (sq_nonneg C) (integral_nonneg (fun ω => sq_nonneg _))
  have h := MartingaleTransformL2.integral_sq_grid_transform_le_terminal
    (hY.sub (MartingaleSpatialLimit.finiteSum_martingale hI q))
    (fun t => (hY2 t).sub (MartingaleSpatialLimit.finiteSum_memLp hI2 q t))
    (BrownianGrid.uniformGrid T n) (BrownianGrid.uniformGrid_mono T n)
    (fun i => K (BrownianGrid.uniformGrid T n i)) (fun i => hK _) hC (fun i => hb _) n
  rw [BrownianGrid.uniformGrid_end T (Nat.pos_of_ne_zero hn)] at h
  simpa only [BrownianGrid.uniformSum, BrownianGrid.integralSum,
    MartingaleSpatialLimit.finiteSum, Pi.sub_apply, mul_sub, Finset.sum_sub_distrib,
    sub_sub_sub_comm] using h

theorem uniformSum_spatial_limit_of_channel_limits [IsFiniteMeasure P]
    {F : Filtration ℝ≥0 mΩ} {I : ι → ℝ≥0 → Ω → ℝ}
    {Y K : ℝ≥0 → Ω → ℝ} {J : ι → Ω → ℝ} {Z : Ω → ℝ}
    (hI : ∀ a, Martingale (I a) F P) (hY : Martingale Y F P)
    (hI2 : ∀ a t, MemLp (I a t) 2 P) (hY2 : ∀ t, MemLp (Y t) 2 P)
    (hJ2 : ∀ a, MemLp (J a) 2 P) (hZ2 : MemLp Z 2 P)
    (hK : StronglyAdapted F K) {C : ℝ} (hC : 0 ≤ C)
    (hb : ∀ t, ∀ᵐ ω ∂P, |K t ω| ≤ C) (T : ℝ≥0)
    (hsumI : HasSum (fun a => (hI2 a T).toLp (I a T)) ((hY2 T).toLp (Y T)))
    (hsumJ : HasSum (fun a => (hJ2 a).toLp (J a)) (hZ2.toLp Z))
    (hlim : ∀ a, Tendsto (fun n => ∫ ω,
      (BrownianGrid.uniformSum (I a) K T n ω - J a ω) ^ 2 ∂P) atTop (𝓝 0)) :
    Tendsto (fun n => ∫ ω,
      (BrownianGrid.uniformSum Y K T n ω - Z ω) ^ 2 ∂P) atTop (𝓝 0) := by
  classical
  have hKm (t : ℝ≥0) : AEStronglyMeasurable (K t) P :=
    ((hK t).mono (F.le t)).aestronglyMeasurable
  let S := MartingaleSpatialLimit.finiteSum I
  let R (q : Finset ι) (ω : Ω) := ∑ a ∈ q, J a ω
  have hS2 (q : Finset ι) (t : ℝ≥0) : MemLp (S q t) 2 P :=
    MartingaleSpatialLimit.finiteSum_memLp hI2 q t
  have hR2 (q : Finset ι) : MemLp (R q) 2 P :=
    memLp_finsetSum q (fun a _ => hJ2 a)
  have hX2 (n : ℕ) : MemLp (BrownianGrid.uniformSum Y K T n) 2 P :=
    uniformSum_memLp hY2 hKm hb T n
  have hXS2 (q : Finset ι) (n : ℕ) :
      MemLp (BrownianGrid.uniformSum (S q) K T n) 2 P :=
    uniformSum_memLp (hS2 q) hKm hb T n
  have hYtail := PredictableL2.tendsto_integral_sq_error_of_hasSum
    (fun a => I a T) (fun a => hI2 a T) (hY2 T) hsumI
  have hZtail := PredictableL2.tendsto_integral_sq_error_of_hasSum J hJ2 hZ2 hsumJ
  have hfinite (q : Finset ι) : Tendsto (fun n => ∫ ω,
      (BrownianGrid.uniformSum (S q) K T n ω - R q ω) ^ 2 ∂P) atTop (𝓝 0) := by
    have hl := FilteringRepresentationClosure.tendsto_integral_sq_fintype_sum_error
      (fun a : q => hJ2 a) (fun a n => uniformSum_memLp (hI2 a) hKm hb T n)
      (fun a => hlim a)
    apply hl.congr
    intro n
    apply integral_congr_ae
    apply Eventually.of_forall
    intro ω
    simp only [S, R, uniformSum_finiteSum]
    rw [Finset.sum_coe_sort q (fun a => BrownianGrid.uniformSum (I a) K T n ω),
      Finset.sum_coe_sort q (fun a => J a ω)]
  apply tendsto_zero_of_uniform_approximation (k := (atTop : Filter (Finset ι)))
    (fun n => integral_nonneg (fun ω => sq_nonneg _))
    (r := fun q : Finset ι =>
      2 * C ^ 2 * (∫ ω, (Y T ω - S q T ω) ^ 2 ∂P) +
        4 * ∫ ω, (Z ω - R q ω) ^ 2 ∂P)
    (g := fun q n => 4 * ∫ ω,
      (BrownianGrid.uniformSum (S q) K T n ω - R q ω) ^ 2 ∂P)
  · simpa only [S, R, MartingaleSpatialLimit.finiteSum, sub_sq_comm,
      mul_zero, add_zero] using
      (hYtail.const_mul (2 * C ^ 2)).add (hZtail.const_mul 4)
  · intro q
    simpa only [mul_zero] using (hfinite q).const_mul 4
  · intro q n
    have h1 := BrownianGrid.integral_sq_sub_le_two (hX2 n) hZ2 (hXS2 q n)
    have h2 := BrownianGrid.integral_sq_sub_le_two hZ2 (hXS2 q n) (hR2 q)
    have h3 := uniformSum_spatial_tail_le hI hY hI2 hY2 hK hC hb q T n
    change (∫ ω, (BrownianGrid.uniformSum Y K T n ω -
      BrownianGrid.uniformSum (S q) K T n ω) ^ 2 ∂P) ≤
      C ^ 2 * (∫ ω, (Y T ω - S q T ω) ^ 2 ∂P) at h3
    linarith

end Problem367.BrownianSpatialAssociativity

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Estimates_RoundedStoppingTimes
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped NNReal Topology

namespace Problem367.RoundedStoppingTimes

private theorem mesh_pos (n : ℕ) : (0 : ℝ≥0) < n + 1 := by positivity

theorem le_round (n : ℕ) (t : ℝ≥0) : t ≤ round n t := by
  rw [round, le_div_iff₀ (mesh_pos n)]
  exact Nat.le_ceil _

theorem round_le_add (n : ℕ) (t : ℝ≥0) :
    round n t ≤ t + 1 / (n + 1 : ℝ≥0) := by
  rw [round, div_le_iff₀ (mesh_pos n), add_mul,
    div_mul_cancel₀ _ (ne_of_gt (mesh_pos n))]
  exact (Nat.ceil_lt_add_one zero_le).le

theorem round_le_iff (n : ℕ) (s t : ℝ≥0) :
    round n s ≤ t ↔ s ≤ (⌊t * (n + 1 : ℝ≥0)⌋₊ : ℝ≥0) / (n + 1 : ℝ≥0) := by
  rw [round, div_le_iff₀ (mesh_pos n), ← Nat.le_floor_iff zero_le,
    Nat.ceil_le, le_div_iff₀ (mesh_pos n)]

theorem floor_div_le (n : ℕ) (t : ℝ≥0) :
    (⌊t * (n + 1 : ℝ≥0)⌋₊ : ℝ≥0) / (n + 1 : ℝ≥0) ≤ t := by
  rw [div_le_iff₀ (mesh_pos n)]
  exact Nat.floor_le zero_le

theorem tendsto_round (t : ℝ≥0) : Tendsto (fun n => round n t) atTop (𝓝 t) := by
  have hu : Tendsto (fun n : ℕ => t + 1 / (n + 1 : ℝ≥0)) atTop (𝓝 t) := by
    simpa using tendsto_const_nhds.add
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ≥0))
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hu
    (fun n => le_round n t) (fun n => round_le_add n t)

theorem roundTop_le_iff (n : ℕ) (s : WithTop ℝ≥0) (t : ℝ≥0) :
    roundTop n s ≤ t ↔
      s ≤ (((⌊t * (n + 1 : ℝ≥0)⌋₊ : ℝ≥0) / (n + 1 : ℝ≥0) : ℝ≥0) : WithTop ℝ≥0) := by
  cases s with
  | top => simp only [roundTop_top, WithTop.top_le_iff, WithTop.coe_ne_top]
  | coe s => simpa only [roundTop_coe, WithTop.coe_le_coe] using round_le_iff n s t

theorem countable_range_roundTop (n : ℕ) : (Set.range (roundTop n)).Countable := by
  refine ((Set.countable_range (fun k : ℕ =>
    ((k : ℝ≥0) / (n + 1 : ℝ≥0) : WithTop ℝ≥0))).insert ⊤).mono ?_
  rintro _ ⟨t, rfl⟩
  cases t with
  | top => exact Set.mem_insert _ _
  | coe t =>
    exact Set.mem_insert_of_mem _ ⟨⌈t * (n + 1 : ℝ≥0)⌉₊, rfl⟩

variable {Ω : Type*} {m : MeasurableSpace Ω} {F : Filtration ℝ≥0 m}

theorem isStoppingTime_roundTop {τ : Ω → WithTop ℝ≥0}
    (hτ : IsStoppingTime F τ) (n : ℕ) : IsStoppingTime F (fun ω => roundTop n (τ ω)) := by
  intro t
  simp only [roundTop_le_iff]
  exact F.mono (floor_div_le n t) _ (hτ _)

theorem countable_range_roundTop_comp (τ : Ω → WithTop ℝ≥0) (n : ℕ) :
    (Set.range (fun ω => roundTop n (τ ω))).Countable :=
  (countable_range_roundTop n).mono (Set.range_comp_subset_range _ _)

theorem tendsto_min_roundTop_untopA (t : ℝ≥0) (s : WithTop ℝ≥0) :
    Tendsto (fun n => (min (t : WithTop ℝ≥0) (roundTop n s)).untopA)
      atTop (𝓝 (min (t : WithTop ℝ≥0) s).untopA) := by
  cases s with
  | top => simp
  | coe s =>
    simpa only [roundTop_coe, ← WithTop.coe_min, WithTop.untopA, WithTop.untopD_coe] using
      (tendsto_const_nhds.min (tendsto_round s) :
        Tendsto (fun n => min t (round n s)) atTop (𝓝 (min t s)))

theorem exists_countable_range_approximation {τ : Ω → WithTop ℝ≥0}
    (hτ : IsStoppingTime F τ) :
    ∃ τn : ℕ → Ω → WithTop ℝ≥0,
      (∀ n, IsStoppingTime F (τn n)) ∧
      (∀ n, (Set.range (τn n)).Countable) ∧
      (∀ (ω : Ω) (t : ℝ≥0), Tendsto (fun n => (min (t : WithTop ℝ≥0) (τn n ω)).untopA)
        atTop (𝓝 (min (t : WithTop ℝ≥0) (τ ω)).untopA)) := by
  exact ⟨fun n ω => roundTop n (τ ω), isStoppingTime_roundTop hτ,
    countable_range_roundTop_comp τ, fun ω t => tendsto_min_roundTop_untopA t (τ ω)⟩

end Problem367.RoundedStoppingTimes

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Estimates_ContinuousOptionalStopping
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal Topology

namespace Problem367.ContinuousOptionalStopping

theorem countable_range_const {Ω α : Type*} (a : α) :
    (range (fun _ : Ω => a)).Countable := by
  apply (countable_singleton a).mono
  rintro x ⟨ω, rfl⟩
  exact mem_singleton a

theorem countable_range_min {Ω α : Type*} [LinearOrder α] {f g : Ω → α}
    (hf : (range f).Countable) (hg : (range g).Countable) :
    (range (fun ω => min (f ω) (g ω))).Countable := by
  apply (hf.union hg).mono
  rintro x ⟨ω, rfl⟩
  rcases le_total (f ω) (g ω) with h | h
  · exact Or.inl ⟨ω, min_eq_left h |>.symm⟩
  · exact Or.inr ⟨ω, min_eq_right h |>.symm⟩

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {μ : Measure Ω} [IsFiniteMeasure μ]
  {F : Filtration ℝ≥0 mΩ} {M : ℝ≥0 → Ω → ℝ} {τ : Ω → WithTop ℝ≥0}

theorem integrable_stoppedValue_of_countable
    (hM : Martingale M F μ) (hτ : IsStoppingTime F τ)
    (hcount : (range τ).Countable) {T : ℝ≥0} (hT : ∀ ω, τ ω ≤ T) :
    Integrable (stoppedValue M τ) μ := by
  exact integrable_condExp.congr
    (hM.stoppedValue_ae_eq_condExp_of_le_const_of_countable_range hτ hT hcount).symm

theorem integral_stoppedValue_of_countable
    (hM : Martingale M F μ) (hτ : IsStoppingTime F τ)
    (hcount : (range τ).Countable) {T : ℝ≥0} (hT : ∀ ω, τ ω ≤ T) :
    (∫ ω, stoppedValue M τ ω ∂μ) = ∫ ω, M T ω ∂μ := by
  rw [integral_congr_ae
    (hM.stoppedValue_ae_eq_condExp_of_le_const_of_countable_range hτ hT hcount)]
  exact integral_condExp hτ.measurableSpace_le

theorem martingale_stoppedProcess_of_countable
    (hM : Martingale M F μ) (hprog : IsStronglyProgressive F M)
    (hτ : IsStoppingTime F τ) (hcount : (range τ).Countable) :
    Martingale (stoppedProcess M τ) F μ := by
  have had := hprog.stronglyAdapted_stoppedProcess hτ
  have hint (t : ℝ≥0) : Integrable (stoppedProcess M τ t) μ := by
    exact integrable_stoppedValue_of_countable hM ((isStoppingTime_const F t).min hτ)
      (countable_range_min (countable_range_const _) hcount) (fun _ => min_le_left _ _)
  refine ⟨had, ?_⟩
  intro s t hst
  apply (ae_eq_condExp_of_forall_setIntegral_eq (F.le s) (hint t)
    (fun A hA _ => (hint s).integrableOn) ?_ (had s).aestronglyMeasurable).symm
  intro A hA hAfin
  classical
  let ν : Ω → WithTop ℝ≥0 := Aᶜ.piecewise (fun _ => s) (fun _ => t)
  have hν : IsStoppingTime F ν := isStoppingTime_piecewise_const hst hA.compl
  have hνcount : (range ν).Countable := by
    apply (Set.to_countable ({(s : WithTop ℝ≥0), (t : WithTop ℝ≥0)} : Set (WithTop ℝ≥0))).mono
    rintro value ⟨sample, rfl⟩
    change ν sample = (s : WithTop ℝ≥0) ∨ ν sample = (t : WithTop ℝ≥0)
    by_cases hsample : sample ∈ A
    · right
      simp only [ν, Set.piecewise, mem_compl_iff, hsample, not_true_eq_false, ite_false, if_false]
    · left
      simp only [ν, Set.piecewise, mem_compl_iff, hsample, not_false_eq_true, ite_true, if_true]
  have hνle (ω : Ω) : ν ω ≤ t := by
    by_cases hω : ω ∈ A
    · simp only [ν, Set.piecewise, mem_compl_iff, hω, not_true_eq_false, ite_false, if_false]
      exact le_rfl
    · simp only [ν, Set.piecewise, mem_compl_iff, hω, not_false_eq_true, ite_true, if_true]
      exact WithTop.coe_le_coe.mpr hst
  let π : Ω → WithTop ℝ≥0 := fun ω => min (ν ω) (τ ω)
  have hπ := hν.min hτ
  have hπcount := countable_range_min hνcount hcount
  have hmeanπ := integral_stoppedValue_of_countable hM hπ hπcount
    (fun ω => (min_le_left _ _).trans (hνle ω))
  have hmeans := integral_stoppedValue_of_countable hM ((isStoppingTime_const F s).min hτ)
    (countable_range_min (countable_range_const _) hcount)
    (fun ω => (min_le_left _ _).trans (WithTop.coe_le_coe.mpr hst))
  have hpiece : stoppedValue M π =
      A.piecewise (stoppedProcess M τ t) (stoppedProcess M τ s) := by
    funext ω
    by_cases hω : ω ∈ A <;> simp [π, ν, Set.piecewise, hω, stoppedValue, stoppedProcess]
  change (∫ ω, stoppedValue M π ω ∂μ) = ∫ ω, M t ω ∂μ at hmeanπ
  have hmean : (∫ ω, stoppedValue M π ω ∂μ) = ∫ ω, stoppedProcess M τ s ω ∂μ :=
    hmeanπ.trans hmeans.symm
  rw [hpiece, integral_piecewise (F.le s A hA) (hint t).integrableOn
    (hint s).integrableOn] at hmean
  have hsplit := integral_add_compl (F.le s A hA) (hint s)
  linarith

theorem martingale_stoppedProcess_of_approximation
    (hM : Martingale M F μ) (hprog : IsStronglyProgressive F M)
    (hc : ∀ᵐ ω ∂μ, Continuous (fun t => M t ω))
    (hdom : ∀ T : ℝ≥0, ∃ g : Ω → ℝ, Integrable g μ ∧
      ∀ᵐ ω ∂μ, ∀ t ≤ T, |M t ω| ≤ g ω)
    (hτ : IsStoppingTime F τ) (τn : ℕ → Ω → WithTop ℝ≥0)
    (hτn : ∀ n, IsStoppingTime F (τn n))
    (hcount : ∀ n, (range (τn n)).Countable)
    (htime : ∀ (ω : Ω) (t : ℝ≥0), Tendsto
      (fun n => (min (t : WithTop ℝ≥0) (τn n ω)).untopA) atTop
      (𝓝 ((min (t : WithTop ℝ≥0) (τ ω)).untopA))) :
    Martingale (stoppedProcess M τ) F μ := by
  have had := hprog.stronglyAdapted_stoppedProcess hτ
  have hMn (n : ℕ) : Martingale (stoppedProcess M (τn n)) F μ :=
    martingale_stoppedProcess_of_countable hM hprog (hτn n) (hcount n)
  have hbound (T : ℝ≥0) (g : Ω → ℝ)
      (hg : ∀ᵐ ω ∂μ, ∀ t ≤ T, |M t ω| ≤ g ω)
      (σ : Ω → WithTop ℝ≥0) :
      ∀ᵐ ω ∂μ, ‖stoppedProcess M σ T ω‖ ≤ g ω := by
    filter_upwards [hg] with ω hω
    exact hω _ (WithTop.untopA_le (min_le_left _ _))
  have hint (t : ℝ≥0) : Integrable (stoppedProcess M τ t) μ := by
    obtain ⟨g, hg, hgb⟩ := hdom t
    exact hg.mono' ((had t).mono (F.le t)).aestronglyMeasurable (hbound t g hgb τ)
  have hlim (t : ℝ≥0) (A : Set Ω) :
      Tendsto (fun n => ∫ ω in A, stoppedProcess M (τn n) t ω ∂μ) atTop
        (𝓝 (∫ ω in A, stoppedProcess M τ t ω ∂μ)) := by
    obtain ⟨g, hg, hgb⟩ := hdom t
    apply tendsto_integral_of_dominated_convergence g
      (fun n => ((hMn n).integrable t).aestronglyMeasurable.restrict) hg.restrict
      (fun n => ae_restrict_of_ae (hbound t g hgb (τn n)))
    filter_upwards [ae_restrict_of_ae hc] with ω hcω
    exact (hcω.tendsto _).comp (htime ω t)
  refine ⟨had, ?_⟩
  intro s t hst
  apply (ae_eq_condExp_of_forall_setIntegral_eq (F.le s) (hint t)
    (fun A hA _ => (hint s).integrableOn) ?_ (had s).aestronglyMeasurable).symm
  intro A hA hAfin
  exact tendsto_nhds_unique (hlim s A)
    (Filter.Tendsto.congr (fun n => ((hMn n).setIntegral_eq hst hA).symm) (hlim t A))

theorem martingale_stoppedProcess_of_continuous_dominated
    (hM : Martingale M F μ) (hprog : IsStronglyProgressive F M)
    (hc : ∀ᵐ ω ∂μ, Continuous (fun t => M t ω))
    (hdom : ∀ T : ℝ≥0, ∃ g : Ω → ℝ, Integrable g μ ∧
      ∀ᵐ ω ∂μ, ∀ t ≤ T, |M t ω| ≤ g ω)
    (hτ : IsStoppingTime F τ) : Martingale (stoppedProcess M τ) F μ := by
  obtain ⟨τn, hτn, hcount, htime⟩ :=
    RoundedStoppingTimes.exists_countable_range_approximation hτ
  exact martingale_stoppedProcess_of_approximation hM hprog hc hdom hτ τn hτn hcount htime

end Problem367.ContinuousOptionalStopping

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

theorem isStronglyProgressive_mono_filtration
    {G : Filtration ℝ≥0 mΩ} (hFG : F ≤ G) (hM : IsStronglyProgressive F M) :
    IsStronglyProgressive G M := by
  intro t
  exact (hM t).mono (sup_le_sup le_rfl (MeasurableSpace.comap_mono (hFG t)))

theorem martingale_stoppedProcess_rightCont
    (hM : Martingale M F μ) (hprog : IsStronglyProgressive F M)
    (hc : ∀ᵐ ω ∂μ, Continuous (fun t => M t ω))
    (hdom : ∀ T : ℝ≥0, ∃ g : Ω → ℝ, Integrable g μ ∧
      ∀ᵐ ω ∂μ, ∀ t ≤ T, |M t ω| ≤ g ω)
    {τ : Ω → WithTop ℝ≥0} (hτ : IsStoppingTime F.rightCont τ) :
    Martingale (stoppedProcess M τ) F.rightCont μ :=
  ContinuousOptionalStopping.martingale_stoppedProcess_of_continuous_dominated
    (martingale_rightCont_of_ae_continuous_dominated hM hc hdom)
    (isStronglyProgressive_mono_filtration F.le_rightCont hprog) hc hdom hτ

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

theorem martingale_stoppedProcess_rightCont_of_memLp_two
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {μ : Measure Ω} [IsFiniteMeasure μ]
    {F : Filtration ℝ≥0 mΩ} {M : ℝ≥0 → Ω → ℝ}
    (hM : Martingale M F μ) (hM2 : ∀ t, MemLp (M t) 2 μ)
    (hprog : IsStronglyProgressive F M)
    (hc : ∀ᵐ ω ∂μ, Continuous (fun t => M t ω))
    {τ : Ω → WithTop ℝ≥0} (hτ : IsStoppingTime F.rightCont τ) :
    Martingale (stoppedProcess M τ) F.rightCont μ := by
  apply martingale_stoppedProcess_rightCont hM hprog hc _ hτ
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
-- module Solutions.Q243_FreeIsing.FreeIsing_Martingales_SpatialRandomEvaluation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Filter
open scoped NNReal Topology

namespace Problem367.MartingaleSpatialRandomEvaluation

variable {Ω ι : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsFiniteMeasure P]
  {F : Filtration ℝ≥0 mΩ} {I : ι → ℝ≥0 → Ω → ℝ} {Y : ℝ≥0 → Ω → ℝ}

theorem tendsto_finiteSum_random_evaluation
    (hI : ∀ a, Martingale (I a) F P) (hY : Martingale Y F P)
    (hI2 : ∀ a t, MemLp (I a t) 2 P) (hY2 : ∀ t, MemLp (Y t) 2 P)
    (hcI : ∀ a, ∀ᵐ ω ∂P, Continuous (fun t => I a t ω))
    (hcY : ∀ᵐ ω ∂P, Continuous (fun t => Y t ω))
    (T : ℝ≥0)
    (hsum : HasSum (fun a => (hI2 a T).toLp (I a T)) ((hY2 T).toLp (Y T)))
    (r : Finset ι → Ω → ℝ≥0) (hr : ∀ q, Measurable (r q))
    (hb : ∀ q ω, r q ω ≤ T) :
    Tendsto (fun q : Finset ι => ∫ ω,
      ((∑ a ∈ q, I a (r q ω) ω) - Y (r q ω) ω) ^ 2 ∂P) atTop (𝓝 0) := by
  classical
  have ht := PredictableL2.tendsto_integral_sq_error_of_hasSum
    (fun a => I a T) (fun a => hI2 a T) (hY2 T) hsum
  apply squeeze_zero (fun q => integral_nonneg (fun ω => sq_nonneg _))
    (fun q => ?_) (by simpa only [mul_zero] using ht.const_mul 4)
  have hc : ∀ᵐ ω ∂P, Continuous
      (fun t => (MartingaleSpatialLimit.finiteSum I q - Y) t ω) := by
    filter_upwards [MartingaleSpatialLimit.finiteSum_ae_continuous hcI q, hcY]
      with ω hq hy
    exact hq.sub hy
  simpa only [MartingaleSpatialLimit.finiteSum, Pi.sub_apply] using
    MartingaleRandomEvaluation.integral_sq_random_evaluation_le
      ((MartingaleSpatialLimit.finiteSum_martingale hI q).sub hY)
      (fun t => (MartingaleSpatialLimit.finiteSum_memLp hI2 q t).sub (hY2 t))
      hc (hr q) (hb q)

theorem exists_hasSum_random_evaluation
    (hI : ∀ a, Martingale (I a) F P) (hY : Martingale Y F P)
    (hI2 : ∀ a t, MemLp (I a t) 2 P) (hY2 : ∀ t, MemLp (Y t) 2 P)
    (hcI : ∀ a, ∀ᵐ ω ∂P, Continuous (fun t => I a t ω))
    (hcY : ∀ᵐ ω ∂P, Continuous (fun t => Y t ω))
    (T : ℝ≥0)
    (hsum : HasSum (fun a => (hI2 a T).toLp (I a T)) ((hY2 T).toLp (Y T)))
    (r : Ω → ℝ≥0) (hr : Measurable r) (hb : ∀ ω, r ω ≤ T) :
    ∃ (hIr : ∀ a, MemLp (fun ω => I a (r ω) ω) 2 P)
      (hYr : MemLp (fun ω => Y (r ω) ω) 2 P),
      HasSum (fun a => (hIr a).toLp (fun ω => I a (r ω) ω))
        (hYr.toLp (fun ω => Y (r ω) ω)) := by
  classical
  have hIr (a : ι) : MemLp (fun ω => I a (r ω) ω) 2 P :=
    MartingaleRandomEvaluation.memLp_random_evaluation (hI a) (hI2 a) (hcI a) hr hb
  have hYr : MemLp (fun ω => Y (r ω) ω) 2 P :=
    MartingaleRandomEvaluation.memLp_random_evaluation hY hY2 hcY hr hb
  refine ⟨hIr, hYr, ?_⟩
  have hl := (SimpleIntegral.tendsto_toLp_iff_meanSquare
    (fun q : Finset ι => memLp_finsetSum q (fun a _ => hIr a)) hYr).mpr
      (tendsto_finiteSum_random_evaluation hI hY hI2 hY2 hcI hcY T hsum
        (fun _ => r) (fun _ => hr) (fun _ => hb))
  change Tendsto (fun q : Finset ι => ∑ a ∈ q, (hIr a).toLp (fun ω => I a (r ω) ω))
    atTop (𝓝 (hYr.toLp (fun ω => Y (r ω) ω)))
  exact hl.congr (fun q => PredictableL2.toLp_finsetSum
    (fun a ω => I a (r ω) ω) hIr q)

theorem exists_hasSum_stoppedProcess
    (hI : ∀ a, Martingale (I a) F P) (hY : Martingale Y F P)
    (hI2 : ∀ a t, MemLp (I a t) 2 P) (hY2 : ∀ t, MemLp (Y t) 2 P)
    (hcI : ∀ a, ∀ᵐ ω ∂P, Continuous (fun t => I a t ω))
    (hcY : ∀ᵐ ω ∂P, Continuous (fun t => Y t ω))
    (T : ℝ≥0)
    (hsum : HasSum (fun a => (hI2 a T).toLp (I a T)) ((hY2 T).toLp (Y T)))
    {τ : Ω → WithTop ℝ≥0} (hτ : IsStoppingTime F τ)
    {t : ℝ≥0} (ht : t ≤ T) :
    ∃ (hIs : ∀ a, MemLp (stoppedProcess (I a) τ t) 2 P)
      (hYs : MemLp (stoppedProcess Y τ t) 2 P),
      HasSum (fun a => (hIs a).toLp (stoppedProcess (I a) τ t))
        (hYs.toLp (stoppedProcess Y τ t)) := by
  exact exists_hasSum_random_evaluation hI hY hI2 hY2 hcI hcY T hsum
    (fun ω => (min (t : WithTop ℝ≥0) (τ ω)).untopA)
    (WithTop.measurable_untopA.comp
      (measurable_const.min (hτ.measurable.mono hτ.measurableSpace_le le_rfl)))
    (fun ω => (WithTop.untopA_le (min_le_left _ _)).trans ht)

end Problem367.MartingaleSpatialRandomEvaluation

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Martingales_StoppedMartingaleL2
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

end Problem367.StoppedMartingaleL2

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Martingales_StoppedRowNormalization
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

theorem stopped_row_normalization_oai {ι : Type*} [IsProbabilityMeasure P]
    {F : Filtration ℝ≥0 mΩ} {B C R I J : ι → ℝ≥0 → Ω → ℝ}
    {M Z K : ℝ≥0 → Ω → ℝ}
    (hB : ∀ a, IsPreBrownianReal (B a) P)
    (hAd : ∀ a, StronglyAdapted F (B a))
    (hind : ∀ a s t, s ≤ t → Indep
      (MeasurableSpace.comap (fun ω => B a t ω - B a s ω) inferInstance) (F s) P)
    (hcB : ∀ a, ∀ᵐ ω ∂P, Continuous (fun t => B a t ω))
    (hC : ∀ a, StronglyAdapted F (C a)) (hR : ∀ a, StronglyAdapted F (R a))
    (hK : StronglyAdapted F K)
    (hcC : ∀ a, ∀ᵐ ω ∂P, Continuous (fun t => C a t ω))
    (hcK : ∀ᵐ ω ∂P, Continuous (fun t => K t ω))
    {c r : ι → ℝ} {k : ℝ} (hc : ∀ a, 0 ≤ c a) (hk : 0 ≤ k)
    (hbC : ∀ a, ∀ᵐ ω ∂P, ∀ t, |C a t ω| ≤ c a)
    (hbR : ∀ a, ∀ᵐ ω ∂P, ∀ t, |R a t ω| ≤ r a)
    (hbK : ∀ᵐ ω ∂P, ∀ t, |K t ω| ≤ k)
    (hI : ∀ a, Martingale (I a) F P) (hJ : ∀ a, Martingale (J a) F P)
    (hM : Martingale M F P) (hZ : Martingale Z F P)
    (hI2 : ∀ a t, MemLp (I a t) 2 P) (hJ2 : ∀ a t, MemLp (J a t) 2 P)
    (hM2 : ∀ t, MemLp (M t) 2 P) (hZ2 : ∀ t, MemLp (Z t) 2 P)
    (hcI : ∀ a, ∀ᵐ ω ∂P, Continuous (fun t => I a t ω))
    (hcJ : ∀ a, ∀ᵐ ω ∂P, Continuous (fun t => J a t ω))
    (hcM : ∀ᵐ ω ∂P, Continuous (fun t => M t ω))
    (hcZ : ∀ᵐ ω ∂P, Continuous (fun t => Z t ω))
    (hpI : ∀ a, IsStronglyProgressive F (I a)) (hpM : IsStronglyProgressive F M)
    (T : ℝ≥0)
    (hsumI : HasSum (fun a => (hI2 a T).toLp (I a T)) ((hM2 T).toLp (M T)))
    (hsumJ : HasSum (fun a => (hJ2 a T).toLp (J a T)) ((hZ2 T).toLp (Z T)))
    (hIlim : ∀ a, Tendsto (fun n => ∫ ω,
      (uniformSum (B a) (C a) T n ω - I a T ω) ^ 2 ∂P) atTop (𝓝 0))
    (hJlim : ∀ a, Tendsto (fun n => ∫ ω,
      (uniformSum (B a) (R a) T n ω - J a T ω) ^ 2 ∂P) atTop (𝓝 0))
    {τ : Ω → WithTop ℝ≥0} (hτ : IsStoppingTime F.rightCont τ)
    (hlocal : ∀ a, ∀ᵐ ω ∂P, ∀ t : ℝ≥0, (t : WithTop ℝ≥0) ≤ τ ω →
      K t ω * C a t ω = R a t ω) :
    Tendsto (fun n => ∫ ω,
      (uniformSum (stoppedProcess M τ) K T n ω - stoppedProcess Z τ T ω) ^ 2 ∂P)
      atTop (𝓝 0) := by
  have hIr (a : ι) := martingale_rightCont_of_ae_continuous_memLp_two (hI a) (hI2 a) (hcI a)
  have hJr (a : ι) := martingale_rightCont_of_ae_continuous_memLp_two (hJ a) (hJ2 a) (hcJ a)
  have hMr := martingale_rightCont_of_ae_continuous_memLp_two hM hM2 hcM
  have hZr := martingale_rightCont_of_ae_continuous_memLp_two hZ hZ2 hcZ
  have hIs (a : ι) := martingale_stoppedProcess_rightCont_of_memLp_two
    (hI a) (hI2 a) (hpI a) (hcI a) hτ
  have hMs := martingale_stoppedProcess_rightCont_of_memLp_two hM hM2 hpM hcM hτ
  have hIs2 (a : ι) (t : ℝ≥0) :=
    StoppedMartingaleL2.memLp_stoppedProcess_two (hIr a) (hI2 a) (hcI a) hτ t
  have hMs2 (t : ℝ≥0) :=
    StoppedMartingaleL2.memLp_stoppedProcess_two hMr hM2 hcM hτ t
  obtain ⟨hIsT, hMsT, hsI⟩ :=
    MartingaleSpatialRandomEvaluation.exists_hasSum_stoppedProcess hIr hMr hI2 hM2
      hcI hcM T hsumI hτ (t := T) le_rfl
  obtain ⟨hJsT, hZsT, hsJ⟩ :=
    MartingaleSpatialRandomEvaluation.exists_hasSum_stoppedProcess hJr hZr hJ2 hZ2
      hcJ hcZ T hsumJ hτ (t := T) le_rfl
  apply BrownianSpatialAssociativity.uniformSum_spatial_limit_of_channel_limits
    hIs hMs hIs2 hMs2 hJsT hZsT (fun t => (hK t).mono (F.le_rightCont t)) hk
    (fun t => hbK.mono (fun ω hω => hω t)) T hsI hsJ
  intro a
  exact stopped_channel_normalization (hB a) (hAd a) (hind a) (hcB a)
    (hC a) (hR a) hK (hcC a) hcK (hc a) hk (hbC a) (hbR a) hbK
    (hI a) (hJ a) (hI2 a) (hJ2 a) (hcI a) (hcJ a) T (hIlim a) (hJlim a)
    hτ (hlocal a)

end Problem367.StoppedRowNormalization

end

end OAI
end

theorem solution.{u_1, u_2} : type_of% @OAI.Problem367.StoppedRowNormalization.stopped_row_normalization_oai.{u_1, u_2} := @OAI.Problem367.StoppedRowNormalization.stopped_row_normalization_oai.{u_1, u_2}
