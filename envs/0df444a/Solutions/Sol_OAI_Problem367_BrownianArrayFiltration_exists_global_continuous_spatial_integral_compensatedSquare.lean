-- Prove2me | solution 1 for OAI.Problem367.BrownianArrayFiltration.exists_global_continuous_spatial_integral_compensatedSquare
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T01:39:37.127241+00:00
-- url     : https://prove2.me/submissions/8c1bb556-dd1d-4476-a89f-b6f506a529a5

import Mathlib
import Definitions.Def_Q243FI000
import Definitions.Def_Q243FI001
import Theorems.Thm_OAI_Problem367_BrownianArrayFiltration_exists_global_continuous_channel_integrals

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

theorem summable_of_orthogonal_sq
    {E ι : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] (f : ι → E)
    (horth : Pairwise fun i j => inner ℝ (f i) (f j) = 0)
    (hsum : Summable fun i => ‖f i‖ ^ 2) : Summable f := by
  let V : ι → Submodule ℝ E := fun i => Submodule.span ℝ {f i}
  have hV : OrthogonalFamily ℝ (fun i => V i) (fun i => (V i).subtypeₗᵢ) := by
    apply OrthogonalFamily.of_pairwise
    intro i j hij
    change (V i) ⟂ (V j)
    simpa only [V, Submodule.isOrtho_span, Set.mem_singleton_iff,
      forall_eq] using horth hij
  let x : (i : ι) → V i := fun i => ⟨f i, Submodule.mem_span_singleton_self (f i)⟩
  exact (hV.summable_iff_norm_sq_summable x).mpr hsum

theorem norm_tsum_sq_of_orthogonal
    {E ι : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] (f : ι → E)
    (horth : Pairwise fun i j => inner ℝ (f i) (f j) = 0)
    (hsum : Summable fun i => ‖f i‖ ^ 2) :
    ‖∑' i, f i‖ ^ 2 = ∑' i, ‖f i‖ ^ 2 := by
  classical
  have hf := summable_of_orthogonal_sq f horth hsum
  have hfinite (s : Finset ι) : ‖∑ i ∈ s, f i‖ ^ 2 = ∑ i ∈ s, ‖f i‖ ^ 2 := by
    rw [← real_inner_self_eq_norm_sq]
    simp only [sum_inner, inner_sum]
    apply Finset.sum_congr rfl
    intro i hi
    rw [Finset.sum_eq_single i]
    · exact real_inner_self_eq_norm_sq (f i)
    · intro j hj hji
      exact horth hji
    · exact fun h => (h hi).elim
  have hn := (hf.hasSum.norm).pow 2
  simp_rw [hfinite] at hn
  exact tendsto_nhds_unique hn hsum.hasSum

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

end Problem367.EnergyRiemann

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

theorem martingale_of_pointwise_time_L1_limit
    {N : Type*} {l : Filter N} [l.NeBot]
    {X : N → ι → Ω → ℝ} {Y : ι → Ω → ℝ}
    (hX : ∀ n, Martingale (X n) F P)
    (hY : StronglyAdapted F Y) (hYint : ∀ t, Integrable (Y t) P)
    (hlim : ∀ t, Tendsto (fun n => eLpNorm (X n t - Y t) 1 P) l (𝓝 0)) :
    Martingale Y F P := by
  refine ⟨hY, ?_⟩
  intro s t hst
  apply (ae_eq_condExp_of_forall_setIntegral_eq (F.le s) (hYint t)
    (fun A hA _ => (hYint s).integrableOn) ?_ (hY s).aestronglyMeasurable).symm
  intro A hA hAfin
  have hs := tendsto_setIntegral_of_L1' (Y s) (hYint s).aestronglyMeasurable
    (Filter.Eventually.of_forall (fun n => (hX n).integrable s)) (hlim s) A
  have ht := tendsto_setIntegral_of_L1' (Y t) (hYint t).aestronglyMeasurable
    (Filter.Eventually.of_forall (fun n => (hX n).integrable t)) (hlim t) A
  have heq : (fun n => ∫ ω in A, X n s ω ∂P) = (fun n => ∫ ω in A, X n t ω ∂P) :=
    funext (fun n => (hX n).setIntegral_eq hst hA)
  rw [heq] at hs
  exact tendsto_nhds_unique hs ht

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
-- module Solutions.Q243_FreeIsing.FreeIsing_Estimates_CompensatedSquareLimit
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology ENNReal

namespace Problem367.CompensatedSquareLimit

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {μ : Measure Ω}

theorem eLpNorm_sq_sub_le {f g : Ω → ℝ}
    (hf : AEStronglyMeasurable f μ) (hg : AEStronglyMeasurable g μ) :
    eLpNorm (fun ω => (f ω) ^ 2 - (g ω) ^ 2) 1 μ ≤
      eLpNorm (f - g) 2 μ *
        (eLpNorm (f - g) 2 μ + (eLpNorm g 2 μ + eLpNorm g 2 μ)) := by
  have hfactor : (fun ω => (f ω) ^ 2 - (g ω) ^ 2) =
      fun ω => (f ω - g ω) * (f ω + g ω) := by
    funext ω
    ring
  have hsum : eLpNorm (f + g) 2 μ ≤
      eLpNorm (f - g) 2 μ + (eLpNorm g 2 μ + eLpNorm g 2 μ) := by
    have heq : f + g = (f - g) + (g + g) := by
      funext ω
      simp only [Pi.add_apply, Pi.sub_apply]
      ring
    rw [heq]
    exact (eLpNorm_add_le (hf := hf.sub hg) (hg := hg.add hg) (by norm_num)).trans
      (add_le_add le_rfl (eLpNorm_add_le (hf := hg) (hg := hg) (p := 2) (by norm_num)))
  rw [hfactor]
  calc
    _ ≤ eLpNorm (f - g) 2 μ * eLpNorm (f + g) 2 μ := by
      simpa using
        (eLpNorm_le_eLpNorm_mul_eLpNorm'_of_norm
          (p := 2) (q := 2) (r := 1)
          (hf.sub hg) (hf.add hg)
          (fun first second : ℝ => first * second) 1
          (Eventually.of_forall (fun ω => by simp [norm_mul])))
    _ ≤ _ := mul_le_mul_right hsum _

theorem tendsto_eLpNorm_sq_sub {N : Type*} {l : Filter N}
    {f : N → Ω → ℝ} {g : Ω → ℝ}
    (hf : ∀ n, AEStronglyMeasurable (f n) μ) (hg : MemLp g 2 μ)
    (hlim : Tendsto (fun n => eLpNorm (f n - g) 2 μ) l (𝓝 0)) :
    Tendsto (fun n => eLpNorm (fun ω => (f n ω) ^ 2 - (g ω) ^ 2) 1 μ)
      l (𝓝 0) := by
  have hsum := hlim.add_const (eLpNorm g 2 μ + eLpNorm g 2 μ)
  have hfinite : (0 : ℝ≥0∞) + (eLpNorm g 2 μ + eLpNorm g 2 μ) ≠ ∞ := by
    simpa using ENNReal.add_ne_top.mpr ⟨hg.eLpNorm_ne_top, hg.eLpNorm_ne_top⟩
  have hb := ENNReal.Tendsto.mul hlim (Or.inr hfinite) hsum
    (Or.inr ENNReal.zero_ne_top)
  simp only [zero_mul] at hb
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hb
    (fun _ => bot_le) (fun n => eLpNorm_sq_sub_le (hf n) hg.aestronglyMeasurable)

theorem martingale_compensatedSquare_of_limits
    {ι N : Type*} [LinearOrder ι]
    {P : Measure Ω} [IsFiniteMeasure P] {F : Filtration ι mΩ}
    {l : Filter N} [l.NeBot]
    {X A : N → ι → Ω → ℝ} {Y Q : ι → Ω → ℝ}
    (hX : ∀ n t, MemLp (X n t) 2 P)
    (_hA : ∀ n t, Integrable (A n t) P)
    (hcomp : ∀ n, Martingale (fun t ω => (X n t ω) ^ 2 - A n t ω) F P)
    (hY : StronglyAdapted F Y) (hY2 : ∀ t, MemLp (Y t) 2 P)
    (hQ : StronglyAdapted F Q) (hQint : ∀ t, Integrable (Q t) P)
    (hlim : ∀ t, Tendsto (fun n => eLpNorm (X n t - Y t) 2 P) l (𝓝 0))
    (hAlim : ∀ t, Tendsto (fun n => eLpNorm (A n t - Q t) 1 P) l (𝓝 0)) :
    Martingale (fun t ω => (Y t ω) ^ 2 - Q t ω) F P := by
  apply StoppedSimpleIntegral.martingale_of_pointwise_time_L1_limit (l := l) hcomp
  · intro t
    exact ((hY t).pow 2).sub (hQ t)
  · intro t
    exact (hY2 t).integrable_sq.sub (hQint t)
  · intro t
    have hs := tendsto_eLpNorm_sq_sub
      (fun n => (hX n t).aestronglyMeasurable) (hY2 t) (hlim t)
    have hb := hs.add (hAlim t)
    simp only [add_zero] at hb
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hb (fun _ => bot_le)
    intro n
    have heq : (fun ω => (X n t ω) ^ 2 - A n t ω) -
        (fun ω => (Y t ω) ^ 2 - Q t ω) =
        (fun ω => (X n t ω) ^ 2 - (Y t ω) ^ 2) - (A n t - Q t) := by
      funext ω
      simp only [Pi.sub_apply]
      ring
    dsimp only
    rw [heq]
    exact eLpNorm_sub_le (hf := ((hX n t).aestronglyMeasurable.pow 2).sub ((hY2 t).aestronglyMeasurable.pow 2)) (hg := ((_hA n t).aestronglyMeasurable.sub (hQint t).aestronglyMeasurable)) le_rfl

theorem eLpNorm_two_eq_ofReal_integral_sq {f : Ω → ℝ} (hf : MemLp f 2 μ) :
    eLpNorm f 2 μ = (ENNReal.ofReal (∫ ω, (f ω) ^ 2 ∂μ)) ^ (1 / 2 : ℝ) := by
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num)]
  simp only [ENNReal.toReal_ofNat]
  congr 1
  rw [ofReal_integral_eq_lintegral_ofReal hf.integrable_sq
    (Eventually.of_forall (fun ω => sq_nonneg _))]
  apply lintegral_congr
  intro ω
  simp [← ofReal_norm, ← ENNReal.ofReal_pow, Real.norm_eq_abs, sq_abs]

theorem tendsto_eLpNorm_two_of_meanSquare {N : Type*} {l : Filter N}
    {f : N → Ω → ℝ} {g : Ω → ℝ} (hf : ∀ n, MemLp (f n) 2 μ) (hg : MemLp g 2 μ)
    (hlim : Tendsto (fun n => ∫ ω, (f n ω - g ω) ^ 2 ∂μ) l (𝓝 0)) :
    Tendsto (fun n => eLpNorm (f n - g) 2 μ) l (𝓝 0) := by
  have ho : Tendsto (fun n => ENNReal.ofReal (∫ ω, (f n ω - g ω) ^ 2 ∂μ)) l (𝓝 0) := by
    simpa only [Function.comp_def, ENNReal.ofReal_zero] using
      (ENNReal.continuous_ofReal.tendsto 0).comp hlim
  have h := (ENNReal.continuous_rpow_const (y := 1 / 2).tendsto (0 : ℝ≥0∞)).comp ho
  have heq (n) := eLpNorm_two_eq_ofReal_integral_sq ((hf n).sub hg)
  simpa only [Function.comp_def, heq, Pi.sub_apply, ENNReal.ofReal_zero, ENNReal.zero_rpow_of_pos (by norm_num : (0 : ℝ) < 1 / 2)] using h

end Problem367.CompensatedSquareLimit

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

theorem abs_partitionSum_le {f : ℝ → ℝ} {τ : ℕ → ℝ} (hτ : Monotone τ)
    (n : ℕ) {C : ℝ} (hb : ∀ i < n, |f (τ i)| ≤ C) :
    |partitionSum f τ n| ≤ C * (τ n - τ 0) := by
  calc
    _ ≤ ∑ i ∈ Finset.range n, |(τ (i + 1) - τ i) * f (τ i)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i ∈ Finset.range n, C * (τ (i + 1) - τ i) := by
      apply Finset.sum_le_sum
      intro i hi
      rw [abs_mul, abs_of_nonneg (sub_nonneg.mpr (hτ (Nat.le_succ i)))]
      nlinarith [mul_le_mul_of_nonneg_left (hb i (Finset.mem_range.mp hi))
        (sub_nonneg.mpr (hτ (Nat.le_succ i)))]
    _ = _ := by rw [← Finset.mul_sum, Finset.sum_range_sub]

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

theorem abs_stoppedSum_le {T t C : ℝ} (hT : 0 ≤ T) (ht : 0 ≤ t)
    {f : ℝ → ℝ} (hb : ∀ x, |f x| ≤ C) (n : ℕ) :
    |stoppedSum f T t n| ≤ C * min t T := by
  by_cases hn : n = 0
  · subst n
    simp only [stoppedSum, Finset.range_zero, Finset.sum_empty, abs_zero]
    exact mul_nonneg ((abs_nonneg (f 0)).trans (hb 0)) (le_min ht hT)
  · rw [stoppedSum_eq_partitionSum hT]
    simpa only [stoppedPoint_zero T ht, stoppedPoint_end T t (Nat.pos_of_ne_zero hn), sub_zero]
      using abs_partitionSum_le (stoppedPoint_mono hT t n) n (fun i _ => hb _)

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

theorem tendsto_stoppedSum_L1
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsFiniteMeasure μ]
    {H : ℝ → Ω → ℝ} (hm : ∀ t, AEStronglyMeasurable (H t) μ)
    (hc : ∀ᵐ ω ∂μ, Continuous (fun t => H t ω))
    {C T t : ℝ} (hb : ∀ᵐ ω ∂μ, ∀ s, |H s ω| ≤ C)
    (hT : 0 ≤ T) (ht : 0 ≤ t) :
    Tendsto (fun n => eLpNorm
      ((fun ω => stoppedSum (fun s => H s ω) T t n) -
        (fun ω => ∫ s in (0 : ℝ)..min t T, H s ω)) 1 μ) atTop (𝓝 0) := by
  have hmeas (n : ℕ) : AEStronglyMeasurable
      (fun ω => stoppedSum (fun s => H s ω) T t n) μ := by
    unfold stoppedSum
    apply Finset.aestronglyMeasurable_fun_sum
    intro i hi
    exact (hm _).const_mul _
  have hbound (n : ℕ) : ∀ᵐ ω ∂μ,
      ‖stoppedSum (fun s => H s ω) T t n‖ ≤ C * min t T := by
    filter_upwards [hb] with ω hω
    exact abs_stoppedSum_le hT ht hω n
  have hlim : ∀ᵐ ω ∂μ, Tendsto (fun n => stoppedSum (fun s => H s ω) T t n)
      atTop (𝓝 (∫ s in (0 : ℝ)..min t T, H s ω)) := by
    filter_upwards [hc] with ω hω
    exact tendsto_stoppedSum hω hT ht
  have h := tendsto_lintegral_norm_of_dominated_convergence hmeas
    (integrable_const (C * min t T)).hasFiniteIntegral hbound hlim
  have hlimitMeas := aestronglyMeasurable_of_tendsto_ae atTop hmeas hlim
  simpa only [eLpNorm_one_eq_lintegral_enorm,
    Pi.sub_apply, ← ofReal_norm] using h

theorem tendsto_stoppedSquareSum_L1
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsFiniteMeasure μ]
    {H : ℝ → Ω → ℝ} (hm : ∀ t, AEStronglyMeasurable (H t) μ)
    (hc : ∀ᵐ ω ∂μ, Continuous (fun t => H t ω))
    {C T t : ℝ} (hC : 0 ≤ C) (hb : ∀ᵐ ω ∂μ, ∀ s, |H s ω| ≤ C)
    (hT : 0 ≤ T) (ht : 0 ≤ t) :
    Tendsto (fun n => eLpNorm
      ((fun ω => stoppedSum (fun s => (H s ω) ^ 2) T t n) -
        (fun ω => ∫ s in (0 : ℝ)..min t T, (H s ω) ^ 2)) 1 μ) atTop (𝓝 0) := by
  apply tendsto_stoppedSum_L1 (fun t => (hm t).pow 2)
    (hc.mono (fun ω hω => hω.pow 2)) (C := C ^ 2) _ hT ht
  filter_upwards [hb] with ω hω
  intro s
  simpa only [Pi.pow_apply, abs_sq, sq_abs] using
    (sq_le_sq₀ (abs_nonneg (H s ω)) hC).mpr (hω s)

theorem tendsto_stoppedSquareSum_L1_nnreal
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsFiniteMeasure μ]
    {H : ℝ≥0 → Ω → ℝ} (hm : ∀ t, AEStronglyMeasurable (H t) μ)
    (hc : ∀ᵐ ω ∂μ, Continuous (fun t => H t ω))
    {C : ℝ} (hC : 0 ≤ C) (hb : ∀ᵐ ω ∂μ, ∀ s, |H s ω| ≤ C)
    (T t : ℝ≥0) :
    Tendsto (fun n => eLpNorm
      ((fun ω => stoppedSum (fun s => (H s.toNNReal ω) ^ 2) T t n) -
        (fun ω => ∫ s in (0 : ℝ)..min (t : ℝ) T, (H s.toNNReal ω) ^ 2)) 1 μ)
      atTop (𝓝 0) := by
  apply tendsto_stoppedSquareSum_L1 (fun s => hm s.toNNReal) _ hC _ T.coe_nonneg t.coe_nonneg
  · filter_upwards [hc] with ω hω
    exact hω.comp (by fun_prop)
  · filter_upwards [hb] with ω hω
    exact fun s => hω s.toNNReal

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

theorem squareSum_stronglyAdapted {F : Filtration ℝ≥0 mΩ}
    {H : ℝ≥0 → Ω → ℝ} (hH : StronglyAdapted F H) (T : ℝ≥0) (n : ℕ) :
    StronglyAdapted F (squareSum H T n) := by
  intro t
  unfold squareSum
  apply Finset.stronglyMeasurable_fun_sum
  intro i hi
  by_cases hit : BrownianGrid.uniformGrid T n i ≤ t
  · exact (((hH _).mono (F.mono hit)).pow 2).const_mul _
  · have hti : t ≤ BrownianGrid.uniformGrid T n i := le_of_not_ge hit
    have hti' := hti.trans (BrownianGrid.uniformGrid_mono T n (Nat.le_succ i))
    have htiR : (t : ℝ) ≤ (BrownianGrid.uniformGrid T n i : ℝ) := hti
    have htiR' : (t : ℝ) ≤ (BrownianGrid.uniformGrid T n (i+1) : ℝ) := hti'
    simpa only [min_eq_left htiR, min_eq_left htiR', sub_self, zero_mul] using
      (stronglyMeasurable_const : StronglyMeasurable[F t] (fun _ : Ω => (0 : ℝ)))

theorem selected_stronglyAdapted {F : Filtration ℝ≥0 mΩ}
    {H : ℝ≥0 → Ω → ℝ} (hH : StronglyAdapted F H) (T : ℝ≥0) :
    StronglyAdapted F (selected H T) := by
  intro t
  have hm (n : ℕ) := squareSum_stronglyAdapted hH T n t
  let : MeasurableSpace Ω := F t
  exact StronglyMeasurable.limUnder hm

omit mΩ in
theorem selected_eq_integral_of_continuous {H : ℝ≥0 → Ω → ℝ} {ω : Ω}
    (hc : Continuous (fun s => H s ω)) (T t : ℝ≥0) :
    selected H T t ω = ∫ s in (0 : ℝ)..min (t : ℝ) T, (H s.toNNReal ω) ^ 2 := by
  apply Filter.Tendsto.limUnder_eq
  have hcR : Continuous (fun s : ℝ => (H s.toNNReal ω) ^ 2) := by fun_prop
  have h := RandomRiemann.tendsto_stoppedSum hcR T.coe_nonneg t.coe_nonneg
  simpa only [squareSum_eq_stoppedSum, Function.comp_apply, Pi.pow_apply] using h

theorem ae_selected_eq_integral {μ : Measure Ω} {H : ℝ≥0 → Ω → ℝ}
    (hc : ∀ᵐ ω ∂μ, Continuous (fun s => H s ω)) (T : ℝ≥0) :
    ∀ᵐ ω ∂μ, ∀ t, selected H T t ω =
      ∫ s in (0 : ℝ)..min (t : ℝ) T, (H s.toNNReal ω) ^ 2 := by
  filter_upwards [hc] with ω hω
  exact selected_eq_integral_of_continuous hω T

omit mΩ in
theorem abs_squareSum_le {H : ℝ≥0 → Ω → ℝ} {ω : Ω} {C : ℝ}
    (hC : 0 ≤ C) (hb : ∀ s, |H s ω| ≤ C) (T t : ℝ≥0) (n : ℕ) :
    |squareSum H T n t ω| ≤ C ^ 2 * min (t : ℝ) T := by
  rw [squareSum_eq_stoppedSum]
  apply RandomRiemann.abs_stoppedSum_le T.coe_nonneg t.coe_nonneg
  intro s
  rw [abs_of_nonneg (sq_nonneg _)]
  nlinarith [hb s.toNNReal, abs_nonneg (H s.toNNReal ω), sq_abs (H s.toNNReal ω)]

omit mΩ in
theorem abs_selected_le {H : ℝ≥0 → Ω → ℝ} {ω : Ω} {C : ℝ}
    (hc : Continuous (fun s => H s ω))
    (hC : 0 ≤ C) (hb : ∀ s, |H s ω| ≤ C) (T t : ℝ≥0) :
    |selected H T t ω| ≤ C ^ 2 * min (t : ℝ) T := by
  rw [selected_eq_integral_of_continuous hc T t, ← Real.norm_eq_abs]
  have h := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := 0) (b := min (t : ℝ) T) (C := C ^ 2)
    (f := fun s : ℝ => (H s.toNNReal ω) ^ 2) (fun s _ => by
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      nlinarith [hb s.toNNReal, abs_nonneg (H s.toNNReal ω), sq_abs (H s.toNNReal ω)])
  simpa only [sub_zero, abs_of_nonneg (le_min t.coe_nonneg T.coe_nonneg)] using h

theorem squareSum_memLp {μ : Measure Ω} [IsFiniteMeasure μ]
    {F : Filtration ℝ≥0 mΩ} {H : ℝ≥0 → Ω → ℝ}
    (hH : StronglyAdapted F H) {C : ℝ} (hC : 0 ≤ C)
    (hb : ∀ᵐ ω ∂μ, ∀ s, |H s ω| ≤ C) (T t : ℝ≥0) (n : ℕ) (p : ℝ≥0∞) :
    MemLp (squareSum H T n t) p μ := by
  apply MemLp.of_bound (squareSum_stronglyAdapted hH T n).stronglyMeasurable.aestronglyMeasurable
    (C ^ 2 * min (t : ℝ) T)
  filter_upwards [hb] with ω hω
  simpa only [Real.norm_eq_abs] using abs_squareSum_le hC hω T t n

theorem selected_memLp {μ : Measure Ω} [IsFiniteMeasure μ]
    {F : Filtration ℝ≥0 mΩ} {H : ℝ≥0 → Ω → ℝ}
    (hH : StronglyAdapted F H) (hc : ∀ᵐ ω ∂μ, Continuous (fun s => H s ω))
    {C : ℝ} (hC : 0 ≤ C) (hb : ∀ᵐ ω ∂μ, ∀ s, |H s ω| ≤ C)
    (T t : ℝ≥0) (p : ℝ≥0∞) : MemLp (selected H T t) p μ := by
  apply MemLp.of_bound (selected_stronglyAdapted hH T).stronglyMeasurable.aestronglyMeasurable
    (C ^ 2 * min (t : ℝ) T)
  filter_upwards [hc, hb] with ω hcω hbω
  simpa only [Real.norm_eq_abs] using abs_selected_le hcω hC hbω T t

theorem tendsto_squareSum_L1_selected
    {μ : Measure Ω} [IsFiniteMeasure μ] {H : ℝ≥0 → Ω → ℝ}
    (hm : ∀ t, AEStronglyMeasurable (H t) μ)
    (hc : ∀ᵐ ω ∂μ, Continuous (fun t => H t ω))
    {C : ℝ} (hC : 0 ≤ C) (hb : ∀ᵐ ω ∂μ, ∀ s, |H s ω| ≤ C) (T t : ℝ≥0) :
    Tendsto (fun n => eLpNorm (squareSum H T n t - selected H T t) 1 μ)
      atTop (𝓝 0) := by
  have h := RandomRiemann.tendsto_stoppedSquareSum_L1_nnreal hm hc hC hb T t
  apply h.congr'
  apply Filter.Eventually.of_forall
  intro n
  apply eLpNorm_congr_ae
  filter_upwards [ae_selected_eq_integral hc T] with ω hω
  simp only [Pi.sub_apply, squareSum_eq_stoppedSum, hω t]

end Problem367.SelectedCompensator

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Estimates_IntervalSumIntegrable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Filter

namespace Problem367.StoppedSimpleIntegral

variable {Ω ι : Type*} [mΩ : MeasurableSpace Ω] [LinearOrder ι]
  {P : Measure Ω} [IsFiniteMeasure P] {F : Filtration ι mΩ}
  {B : ι → Ω → ℝ}

theorem intervalSum_eq_condExp_terminal_of_integrable
    (hB : Martingale B F P) {a b : ι} (hab : a ≤ b)
    {H : Ω → ℝ} (hH : StronglyMeasurable[F a] H)
    (hYint : Integrable (fun ω => H ω * (B b ω - B a ω)) P) (t : ι) :
    P[(fun ω => H ω * (B b ω - B a ω)) | F t] =ᵐ[P]
      intervalSum B H a b t := by
  have hDint : Integrable (fun ω => B b ω - B a ω) P :=
    (hB.integrable b).sub (hB.integrable a)
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

theorem intervalSum_martingale_of_integrable_terminal
    (hB : Martingale B F P) {a b : ι} (hab : a ≤ b)
    {H : Ω → ℝ} (hH : StronglyMeasurable[F a] H)
    (hYint : Integrable (fun ω => H ω * (B b ω - B a ω)) P) :
    Martingale (intervalSum B H a b) F P :=
  (martingale_condExp (fun ω => H ω * (B b ω - B a ω)) F P).congr
    (intervalSum_stronglyAdapted hB hab hH)
    (intervalSum_eq_condExp_terminal_of_integrable hB hab hH hYint)

end Problem367.StoppedSimpleIntegral

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Stochastic_StoppedBrownianSquare
attribute [-instance] _root_.OAI.Problem367.WienerSampler.pathMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace Problem367.StoppedBrownianSquare
open StoppedSimpleIntegral BrownianFiltration

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
  {B : ℝ≥0 → Ω → ℝ} {F : Filtration ℝ≥0 mΩ}

theorem square_sub_time_martingale
    (hB : IsPreBrownianReal B P) (hAd : StronglyAdapted F B)
    (hind : ∀ s t, s ≤ t → Indep
      (MeasurableSpace.comap (fun ω => B t ω - B s ω) inferInstance) (F s) P) :
    Martingale (fun t ω => (B t ω)^2 - (t : ℝ)) F P := by
  let : IsProbabilityMeasure P := hB.isGaussianProcess.isProbabilityMeasure
  have hM := martingale_of_independent_past hB hAd hind
  have hL2 (t) := (hB.isGaussianProcess.hasGaussianLaw_eval t).memLp_two
  refine ⟨fun t => (hM.stronglyAdapted t).pow 2 |>.sub stronglyMeasurable_const, ?_⟩
  intro s t hst
  let G := F s
  let X : Ω → ℝ := B t - B s
  have hXL2 : MemLp X 2 P := (hL2 t).sub (hL2 s)
  have hXint : Integrable X P := (hB.integrable_eval t).sub (hB.integrable_eval s)
  have hXzero : P[X | G] =ᵐ[P] fun _ => 0 := by
    have hsub := condExp_sub (hB.integrable_eval t) (hB.integrable_eval s) G
    filter_upwards [hsub, hM.condExp_ae_eq hst, hM.condExp_ae_eq (le_refl s)] with ω h1 h2 h3
    dsimp [X, G] at *
    simp only [h2, h3, sub_self] at h1
    exact h1
  have hprodInt : Integrable (B s * X) P := (hL2 s).integrable_mul hXL2
  have hprodZero : P[B s * X | G] =ᵐ[P] fun _ => 0 := by
    have hp := condExp_mul_of_stronglyMeasurable_left (hM.stronglyAdapted s) hprodInt hXint
    filter_upwards [hp, hXzero] with ω hp hz
    change P[B s * X | G] ω = B s ω * P[X | G] ω at hp
    rw [hz, mul_zero] at hp
    exact hp
  have htwoZero : P[(fun ω => 2 * (B s ω * X ω)) | G] =ᵐ[P] fun _ => 0 := by
    have hp := condExp_smul (μ := P) (2 : ℝ) (B s * X) G
    filter_upwards [hp, hprodZero] with ω hp hz
    change P[(fun ω => 2 * (B s ω * X ω)) | G] ω = 2 * P[B s * X | G] ω at hp
    rw [hz, mul_zero] at hp
    exact hp
  have hXSq := increment_sq_condExp (mΩ := mΩ) hB hAd hst (hind s t hst)
  have hBSq : P[(fun ω => (B s ω)^2) | G] = (fun ω => (B s ω)^2) :=
    condExp_of_stronglyMeasurable (F |>.le s)
      ((hM.stronglyAdapted s).pow 2) (hL2 s).integrable_sq
  have hfun : (fun ω => (B t ω)^2) =
      (fun ω => (X ω)^2 + 2 * (B s ω * X ω)) + (fun ω => (B s ω)^2) := by
    funext ω
    dsimp [X]
    ring
  have hsum1 := condExp_add hXL2.integrable_sq (hprodInt.const_mul 2) G
  have hsum2 := condExp_add (hXL2.integrable_sq.add (hprodInt.const_mul 2))
    (hL2 s).integrable_sq G
  have hBtSq : P[(fun ω => (B t ω)^2) | G] =ᵐ[P]
      fun ω => ((t : ℝ) - (s : ℝ)) + (B s ω)^2 := by
    rw [hfun]
    filter_upwards [hsum2, hsum1, htwoZero, hXSq] with ω h2 h1 hz hsq
    change P[(fun ω => (X ω)^2) | G] ω = (t : ℝ) - (s : ℝ) at hsq
    simp only [Pi.add_def, Pi.mul_def] at h2 h1
    rw [hBSq] at h2
    rw [h1, hz, hsq] at h2
    simpa only [Pi.add_def, add_zero] using h2
  have hsub := condExp_sub (hL2 t).integrable_sq (integrable_const (t : ℝ)) G
  have hc : P[(fun _ : Ω => (t : ℝ)) | G] = (fun _ => (t : ℝ)) :=
    condExp_const (F |>.le s) (t : ℝ)
  filter_upwards [hsub, hBtSq] with ω hs hsq
  rw [hc] at hs
  simp only [Pi.sub_apply] at hs
  rw [hsq] at hs
  simp only [Pi.sub_def] at hs
  exact hs.trans (by ring)

theorem intervalSum_square_martingale
    (hB : IsPreBrownianReal B P) (hAd : StronglyAdapted F B)
    (hind : ∀ s t, s ≤ t → Indep
      (MeasurableSpace.comap (fun ω => B t ω - B s ω) inferInstance) (F s) P)
    {a b : ℝ≥0} (hab : a ≤ b) {H : Ω → ℝ}
    (hH : StronglyMeasurable[F a] H) {K : ℝ}
    (hbound : ∀ᵐ ω ∂P, ‖H ω‖ ≤ K) :
    Martingale (fun t ω => intervalSum B H a b t ω ^ 2 -
      H ω ^ 2 * ((min t b : ℝ) - (min t a : ℝ))) F P := by
  let : IsProbabilityMeasure P := hB.isGaussianProcess.isProbabilityMeasure
  have hM := martingale_of_independent_past hB hAd hind
  have hQ := square_sub_time_martingale hB hAd hind
  have hHsq : StronglyMeasurable[F a] (fun ω => H ω ^ 2) := hH.pow 2
  have hbSq : ∀ᵐ ω ∂P, ‖H ω ^ 2‖ ≤ K ^ 2 := by
    filter_upwards [hbound] with ω hω
    rw [norm_pow]
    nlinarith [norm_nonneg (H ω)]
  have hfirst := intervalSum_martingale hQ hab hHsq hbSq
  have hL2 (t : ℝ≥0) := (hB.isGaussianProcess.hasGaussianLaw_eval t).memLp_two
  have hprod : Integrable (fun ω => B a ω * (B b ω - B a ω)) P :=
    (hL2 a).integrable_mul ((hL2 b).sub (hL2 a))
  have hcross : Integrable (fun ω => (2 * H ω ^ 2 * B a ω) *
      (B b ω - B a ω)) P := by
    have h := (hprod.bdd_mul (hHsq.mono (F.le a)).aestronglyMeasurable hbSq).const_mul 2
    convert h using 1
    all_goals try with_reducible_and_instances rfl
    funext ω
    ring
  have hsecond := intervalSum_martingale_of_integrable_terminal hM hab
    ((stronglyMeasurable_const.mul hHsq).mul (hAd a)) hcross
  convert hfirst.sub hsecond using 1
  all_goals try with_reducible_and_instances rfl
  funext t ω
  rcases le_total t a with hta | hat
  · simp only [← NNReal.coe_min, intervalSum, min_eq_left hta, min_eq_left (hta.trans hab),
      sub_self, mul_zero, zero_pow (by norm_num : (2 : ℕ) ≠ 0), Pi.sub_apply]
  · simp only [← NNReal.coe_min, intervalSum, min_eq_right hat, Pi.sub_apply, Pi.mul_apply]
    ring

omit mΩ in

theorem sum_intervalSum_eq_terminal
    (τ : ℕ → ℝ≥0) (hτ : Monotone τ) (H : ℕ → Ω → ℝ)
    (n : ℕ) {t : ℝ≥0} (hnt : τ n ≤ t) :
    (fun ω => ∑ i ∈ Finset.range n,
      intervalSum B (H i) (τ i) (τ (i + 1)) t ω) =
    (fun ω => ∑ i ∈ Finset.range n,
      intervalSum B (H i) (τ i) (τ (i + 1)) (τ n) ω) := by
  funext ω
  apply Finset.sum_congr rfl
  intro i hi
  have hin : i + 1 ≤ n := Finset.mem_range.mp hi
  have hia : τ i ≤ τ n := hτ (Nat.le_of_succ_le hin)
  have hib : τ (i + 1) ≤ τ n := hτ hin
  simp only [intervalSum, min_eq_right hia, min_eq_right hib,
    min_eq_right (hia.trans hnt), min_eq_right (hib.trans hnt)]

theorem stopped_predictable_sum_square_martingale
    (hB : IsPreBrownianReal B P) (hAd : StronglyAdapted F B)
    (hind : ∀ s t, s ≤ t → Indep
      (MeasurableSpace.comap (fun ω => B t ω - B s ω) inferInstance) (F s) P)
    (τ : ℕ → ℝ≥0) (hτ : Monotone τ) (H : ℕ → Ω → ℝ)
    (hH : ∀ i, StronglyMeasurable[F (τ i)] (H i))
    (K : ℕ → ℝ) (hbound : ∀ i, ∀ᵐ ω ∂P, ‖H i ω‖ ≤ K i) (n : ℕ) :
    Martingale (fun t ω =>
      (∑ i ∈ Finset.range n, intervalSum B (H i) (τ i) (τ (i + 1)) t ω) ^ 2 -
      ∑ i ∈ Finset.range n, H i ω ^ 2 *
        ((min t (τ (i + 1)) : ℝ) - (min t (τ i) : ℝ))) F P := by
  let : IsProbabilityMeasure P := hB.isGaussianProcess.isProbabilityMeasure
  have hM := martingale_of_independent_past hB hAd hind
  have hH2 (i : ℕ) : MemLp (H i) 2 P :=
    MemLp.of_bound ((hH i).mono (F.le (τ i))).aestronglyMeasurable (K i) (hbound i)
  have hsum2 (m : ℕ) (t : ℝ≥0) :=
    stopped_predictable_sum_memLp_two hB hind τ hτ H hH hH2 (Finset.range m) t
  induction n with
  | zero =>
      convert martingale_zero ℝ F P using 1
      all_goals try with_reducible_and_instances rfl
      funext t ω
      simp
  | succ n ih =>
      let S : ℝ≥0 → Ω → ℝ := fun t ω => ∑ i ∈ Finset.range n,
        intervalSum B (H i) (τ i) (τ (i + 1)) t ω
      have hS : Martingale S F P :=
        stopped_predictable_sum_martingale hB hAd hind τ hτ H hH K hbound (Finset.range n)
      have hY2 : MemLp (fun ω => H n ω * (B (τ (n + 1)) ω - B (τ n) ω)) 2 P :=
        predictable_mul_memLp_two hB (hind (τ n) (τ (n + 1)) (hτ (Nat.le_succ n)))
          (hH n) (hH2 n)
      have hcoeff : StronglyMeasurable[F (τ n)] (fun ω => S (τ n) ω * H n ω) :=
        (hS.stronglyAdapted (τ n)).mul (hH n)
      have hint : Integrable (fun ω => (S (τ n) ω * H n ω) *
          (B (τ (n + 1)) ω - B (τ n) ω)) P := by
        have h := (hsum2 n (τ n)).integrable_mul hY2
        convert h using 1
        all_goals try with_reducible_and_instances rfl
        funext ω
        dsimp [S]
        ring
      have hcross := intervalSum_martingale_of_integrable_terminal hM (hτ (Nat.le_succ n))
        hcoeff hint
      have heq : (fun t ω => S t ω *
          intervalSum B (H n) (τ n) (τ (n + 1)) t ω) =
          intervalSum B (fun ω => S (τ n) ω * H n ω) (τ n) (τ (n + 1)) := by
        funext t ω
        rcases le_total t (τ n) with hta | hat
        · simp only [intervalSum, min_eq_left hta,
            min_eq_left (hta.trans (hτ (Nat.le_succ n))), sub_self, mul_zero]
        · have hconst : S t = S (τ n) := sum_intervalSum_eq_terminal τ hτ H n hat
          rw [hconst]
          simp only [intervalSum]
          ring
      have hcross' : Martingale (fun t ω => S t ω *
          intervalSum B (H n) (τ n) (τ (n + 1)) t ω) F P := by
        rw [heq]
        exact hcross
      have hdiag := intervalSum_square_martingale hB hAd hind (hτ (Nat.le_succ n))
        (hH n) (hbound n)
      have htotal := (ih.add hdiag).add (Martingale.smul 2 hcross')
      convert htotal using 1
      all_goals try with_reducible_and_instances rfl
      funext t ω
      simp only [Finset.sum_range_succ, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      dsimp [S]
      ring

end Problem367.StoppedBrownianSquare

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Brownian_IntegralCompensator
attribute [-instance] _root_.OAI.Problem367.WienerSampler.pathMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal Topology

namespace Problem367.BrownianIntegralProcess

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}

theorem stopped_uniform_limit_compensatedSquare
    {B H M : ℝ≥0 → Ω → ℝ} {F : Filtration ℝ≥0 mΩ}
    (hB : IsPreBrownianReal B P) (hAd : StronglyAdapted F B)
    (hind : ∀ s t, s ≤ t → Indep
      (MeasurableSpace.comap (fun ω => B t ω - B s ω) inferInstance) (F s) P)
    (hH : StronglyAdapted F H)
    (hc : ∀ᵐ ω ∂P, Continuous (fun t => H t ω))
    {C : ℝ} (hC : 0 ≤ C) (hb : ∀ᵐ ω ∂P, ∀ t, |H t ω| ≤ C)
    (T : ℝ≥0) (hM : StronglyAdapted F M) (hM2 : ∀ t, MemLp (M t) 2 P)
    (hlim : ∀ t, Tendsto (fun n => ∫ ω,
      (stoppedUniformSum B H T n t ω - M t ω) ^ 2 ∂P) atTop (𝓝 0)) :
    Martingale (fun t ω => (M t ω) ^ 2 - SelectedCompensator.selected H T t ω) F P := by
  let : IsProbabilityMeasure P := hB.isGaussianProcess.isProbabilityMeasure
  have hH2 (t : ℝ≥0) : MemLp (H t) 2 P := by
    apply MemLp.of_bound hH.stronglyMeasurable.aestronglyMeasurable C
    filter_upwards [hb] with ω hω
    simpa only [Real.norm_eq_abs] using hω t
  have hS2 (n : ℕ) (t : ℝ≥0) : MemLp (stoppedUniformSum B H T n t) 2 P :=
    BrownianFiltration.stopped_predictable_sum_memLp_two hB hind
      (BrownianGrid.uniformGrid T n) (BrownianGrid.uniformGrid_mono T n)
      (fun i => H (BrownianGrid.uniformGrid T n i)) (fun i => hH _) (fun i => hH2 _)
      (Finset.range n) t
  have hfinite (n : ℕ) : Martingale (fun t ω =>
      (stoppedUniformSum B H T n t ω) ^ 2 - SelectedCompensator.squareSum H T n t ω) F P := by
    have h := StoppedBrownianSquare.stopped_predictable_sum_square_martingale hB hAd hind
      (BrownianGrid.uniformGrid T n) (BrownianGrid.uniformGrid_mono T n)
      (fun i => H (BrownianGrid.uniformGrid T n i)) (fun i => hH _) (fun _ => C)
      (fun i => hb.mono (fun ω hω => by simpa only [Real.norm_eq_abs] using hω _)) n
    simpa only [stoppedUniformSum, SelectedCompensator.squareSum, mul_comm] using h
  apply CompensatedSquareLimit.martingale_compensatedSquare_of_limits (l := atTop)
    hS2 (fun n t => (SelectedCompensator.squareSum_memLp hH hC hb T t n 1).integrable le_rfl)
    hfinite hM hM2 (SelectedCompensator.selected_stronglyAdapted hH T)
    (fun t => (SelectedCompensator.selected_memLp hH hc hC hb T t 1).integrable le_rfl)
  · intro t
    exact CompensatedSquareLimit.tendsto_eLpNorm_two_of_meanSquare
      (fun n => hS2 n t) (hM2 t) (hlim t)
  · intro t
    exact SelectedCompensator.tendsto_squareSum_L1_selected
      (fun s => hH.stronglyMeasurable.aestronglyMeasurable) hc hC hb T t

end Problem367.BrownianIntegralProcess

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Brownian_GlobalCompensator
attribute [-instance] _root_.OAI.Problem367.WienerSampler.pathMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal Topology

namespace Problem367.BrownianIntegralProcess

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}

theorem globalCompensator_stronglyAdapted {F : Filtration ℝ≥0 mΩ}
    {H : ℝ≥0 → Ω → ℝ} (hH : StronglyAdapted F H) :
    StronglyAdapted F (globalCompensator H) :=
  fun t => SelectedCompensator.selected_stronglyAdapted hH t t

theorem ae_globalCompensator_eq_integral {H : ℝ≥0 → Ω → ℝ}
    (hc : ∀ᵐ ω ∂P, Continuous (fun t => H t ω)) :
    ∀ᵐ ω ∂P, ∀ t, globalCompensator H t ω =
      ∫ s in (0 : ℝ)..(t : ℝ), (H s.toNNReal ω) ^ 2 := by
  filter_upwards [hc] with ω hω
  intro t
  simpa only [globalCompensator, min_self] using
    SelectedCompensator.selected_eq_integral_of_continuous hω t t

omit mΩ in
theorem stoppedUniformSum_min_horizon (B H : ℝ≥0 → Ω → ℝ)
    (T : ℝ≥0) (n : ℕ) (t : ℝ≥0) :
    stoppedUniformSum B H T n (min t T) = stoppedUniformSum B H T n t := by
  funext ω
  unfold stoppedUniformSum
  apply Finset.sum_congr rfl
  intro i hi
  have hin : i < n := Finset.mem_range.mp hi
  have hn : 0 < n := (Nat.zero_le i).trans_lt hin
  have ha := BrownianGrid.uniformGrid_le_horizon T hn hin.le
  have hb := BrownianGrid.uniformGrid_le_horizon T hn (Nat.succ_le_of_lt hin)
  simp only [StoppedSimpleIntegral.intervalSum, min_assoc, min_eq_right ha, min_eq_right hb]

theorem global_compensatedSquare_of_integer_stopped_limits
    {B H M : ℝ≥0 → Ω → ℝ} {F : Filtration ℝ≥0 mΩ}
    (hB : IsPreBrownianReal B P) (hAd : StronglyAdapted F B)
    (hind : ∀ s t, s ≤ t → Indep
      (MeasurableSpace.comap (fun ω => B t ω - B s ω) inferInstance) (F s) P)
    (hH : StronglyAdapted F H) (hc : ∀ᵐ ω ∂P, Continuous (fun t => H t ω))
    {C : ℝ} (hC : 0 ≤ C) (hb : ∀ᵐ ω ∂P, ∀ t, |H t ω| ≤ C)
    (hM : StronglyAdapted F M) (hM2 : ∀ t, MemLp (M t) 2 P)
    (hlim : ∀ N : ℕ, 0 < N → ∀ t : ℝ≥0, t ≤ N →
      Tendsto (fun n => ∫ ω,
        (stoppedUniformSum B H N n t ω - M t ω) ^ 2 ∂P) atTop (𝓝 0)) :
    Martingale (fun t ω => (M t ω) ^ 2 - globalCompensator H t ω) F P := by
  let : IsProbabilityMeasure P := hB.isGaussianProcess.isProbabilityMeasure
  refine ⟨fun t => ((hM t).pow 2).sub (globalCompensator_stronglyAdapted hH t), ?_⟩
  intro s t hst
  obtain ⟨N, htN⟩ := exists_nat_gt (t : ℝ)
  have hN : 0 < N := by exact_mod_cast (t.coe_nonneg.trans_lt htN)
  have htN' : t ≤ (N : ℝ≥0) := by exact_mod_cast htN.le
  have hsN : s ≤ (N : ℝ≥0) := hst.trans htN'
  let L : ℝ≥0 → Ω → ℝ := fun r => M (min r N)
  have hL : StronglyAdapted F L := fun r =>
    (hM (min r N)).mono (F.mono (min_le_left _ _))
  have hL2 (r : ℝ≥0) : MemLp (L r) 2 P := hM2 (min r N)
  have hLlim (r : ℝ≥0) : Tendsto (fun n => ∫ ω,
      (stoppedUniformSum B H N n r ω - L r ω) ^ 2 ∂P) atTop (𝓝 0) := by
    simpa only [stoppedUniformSum_min_horizon, L] using
      hlim N hN (min r N) (min_le_right _ _)
  have hcomp := stopped_uniform_limit_compensatedSquare hB hAd hind hH hc hC hb N hL hL2 hLlim
  have heq (r : ℝ≥0) (hr : r ≤ N) :
      (fun ω => (L r ω) ^ 2 - SelectedCompensator.selected H N r ω) =ᵐ[P]
        (fun ω => (M r ω) ^ 2 - globalCompensator H r ω) := by
    filter_upwards [hc] with ω hω
    have hrR : (r : ℝ) ≤ (N : ℝ) := by exact_mod_cast hr
    simp only [L, min_eq_left hr, globalCompensator,
      SelectedCompensator.selected_eq_integral_of_continuous hω, NNReal.coe_natCast, min_self, min_eq_left hrR]
  exact (condExp_congr_ae (heq t htN').symm).trans
    ((hcomp.condExp_ae_eq hst).trans (heq s hsN))

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
-- module Solutions.Q243_FreeIsing.FreeIsing_Martingales_SpatialLimit
attribute [-instance] _root_.OAI.Problem367.WienerSampler.pathMeasurableSpace
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

theorem summable_energy_of_integer [IsFiniteMeasure μ]
    {F : Filtration ℝ≥0 mΩ} {M : ι → ℝ≥0 → Ω → ℝ}
    (hM : ∀ i, Martingale (M i) F μ) (h2 : ∀ i t, MemLp (M i t) 2 μ)
    (henergy : ∀ N : ℕ, Summable (fun i => ∫ ω, M i (N : ℝ≥0) ω ^ 2 ∂μ))
    (t : ℝ≥0) : Summable (fun i => ∫ ω, M i t ω ^ 2 ∂μ) := by
  obtain ⟨N, hN⟩ := exists_nat_ge t
  exact Summable.of_nonneg_of_le (fun i => integral_nonneg (fun ω => sq_nonneg _))
    (fun i => MartingaleSquareMaximal.integral_sq_le (hM i) (h2 i) hN) (henergy N)

theorem summable_toLp {M : ι → ℝ≥0 → Ω → ℝ}
    (h2 : ∀ i t, MemLp (M i t) 2 μ) (t : ℝ≥0)
    (horth : Pairwise (fun i j => ∫ ω, M i t ω * M j t ω ∂μ = 0))
    (henergy : Summable (fun i => ∫ ω, M i t ω ^ 2 ∂μ)) :
    Summable (fun i => (h2 i t).toLp (M i t)) := by
  apply PredictableL2.summable_of_orthogonal_sq
  · intro i j hij
    simpa only [PredictableL2.inner_toLp] using horth hij
  · simpa only [PredictableL2.norm_toLp_sq] using henergy

theorem exists_continuous_martingale_sum [Countable ι] [IsFiniteMeasure μ]
    {F : Filtration ℝ≥0 mΩ} {M : ι → ℝ≥0 → Ω → ℝ}
    (hM : ∀ i, Martingale (M i) F μ)
    (h2 : ∀ i t, MemLp (M i t) 2 μ)
    (hc : ∀ i, ∀ᵐ ω ∂μ, Continuous (fun t => M i t ω))
    (horth : ∀ t, Pairwise (fun i j => ∫ ω, M i t ω * M j t ω ∂μ = 0))
    (henergy : ∀ N : ℕ, Summable (fun i => ∫ ω, M i (N : ℝ≥0) ω ^ 2 ∂μ)) :
    ∃ (L : ℝ≥0 → Ω → ℝ) (hL2 : ∀ t, MemLp (L t) 2 μ),
      IsStronglyPredictable F L ∧ Martingale L F μ ∧
      (∀ᵐ ω ∂μ, Continuous (fun t => L t ω)) ∧
      (∀ t, HasSum (fun i => (h2 i t).toLp (M i t)) ((hL2 t).toLp (L t))) ∧
      (∀ T : ℝ≥0, Tendsto (fun s : Finset ι =>
        ∫ ω, MartingaleStrongMaximal.maximalSquare (finiteSum M s - L) T ω ∂μ)
        atTop (𝓝 0)) := by
  classical
  obtain ⟨s, hs⟩ := Filter.exists_seq_tendsto (atTop : Filter (Finset ι))
  have hsum (t : ℝ≥0) : Summable (fun i => (h2 i t).toLp (M i t)) :=
    summable_toLp h2 t (horth t) (summable_energy_of_integer hM h2 henergy t)
  have heq (n : ℕ) (t : ℝ≥0) :
      (finiteSum_memLp h2 (s n) t).toLp (finiteSum M (s n) t) =
        ∑ i ∈ s n, (h2 i t).toLp (M i t) :=
    PredictableL2.toLp_finsetSum (fun i => M i t) (fun i => h2 i t) (s n)
  have hseq (t : ℝ≥0) : Tendsto (fun n =>
      (finiteSum_memLp h2 (s n) t).toLp (finiteSum M (s n) t)) atTop
      (𝓝 (∑' i, (h2 i t).toLp (M i t))) := by
    simp_rw [heq]
    exact (hsum t).hasSum.comp hs
  obtain ⟨L, hpred, hLc, hlim⟩ :=
    MartingaleSquareMaximal.exists_global_predictable_continuous_L2_limit
      (fun n => finiteSum_martingale hM (s n))
      (fun n t => finiteSum_memLp h2 (s n) t)
      (fun n => finiteSum_ae_continuous hc (s n))
      (fun N => (hseq (N : ℝ≥0)).cauchySeq)
  choose hL2 hLlim using hlim
  have hLM : Martingale L F μ := MartingaleSquareMaximal.martingale_of_L2_limits
    (fun n => finiteSum_martingale hM (s n))
    (fun n t => finiteSum_memLp h2 (s n) t)
    hpred.stronglyAdapted hL2 hLlim
  have hHasSum (t : ℝ≥0) : HasSum (fun i => (h2 i t).toLp (M i t))
      ((hL2 t).toLp (L t)) := by
    have heq := tendsto_nhds_unique (hseq t) (hLlim t)
    rw [← heq]
    exact (hsum t).hasSum
  refine ⟨L, hL2, hpred, hLM, hLc, hHasSum, ?_⟩
  intro T
  have hterminal := PredictableL2.tendsto_integral_sq_error_of_hasSum
    (fun i => M i T) (fun i => h2 i T) (hL2 T) (hHasSum T)
  apply squeeze_zero
    (fun q => integral_nonneg (fun ω => ENNReal.toReal_nonneg))
    (fun q => ?_)
    (show Tendsto (fun q : Finset ι => 4 * ∫ ω,
      ((∑ i ∈ q, M i T ω) - L T ω) ^ 2 ∂μ) atTop (𝓝 0) from by
      simpa only [mul_zero] using hterminal.const_mul 4)
  have hbound := MartingaleStrongMaximal.integral_maximalSquare_le
    ((finiteSum_martingale hM q).sub hLM)
    (fun t => (finiteSum_memLp h2 q t).sub (hL2 t))
    (show ∀ᵐ ω ∂μ, Continuous (fun t => (finiteSum M q - L) t ω) from by
      filter_upwards [finiteSum_ae_continuous hc q, hLc] with ω hq hl
      exact hq.sub hl) T
  simpa only [Pi.sub_apply, finiteSum, MartingaleStrongMaximal.maximalSquare] using hbound

end Problem367.MartingaleSpatialLimit

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

theorem tendsto_finsetSum_L1_of_nonnegative
    {f : ι → Ω → ℝ} (hf : ∀ i, Integrable (f i) μ)
    (hn : ∀ i ω, 0 ≤ f i ω) (hs : Summable (fun i => ∫ ω, f i ω ∂μ)) :
    Tendsto (fun s : Finset ι => eLpNorm
      ((fun ω => ∑ i ∈ s, f i ω) - (fun ω => ∑' i, f i ω)) 1 μ)
      atTop (𝓝 0) := by
  classical
  obtain ⟨hae, hint, htotal⟩ := integrable_tsum_of_nonnegative hf hn hs
  have heq (s : Finset ι) : eLpNorm
      ((fun ω => ∑ i ∈ s, f i ω) - (fun ω => ∑' i, f i ω)) 1 μ =
      ENNReal.ofReal ((∑' i, ∫ ω, f i ω ∂μ) - ∑ i ∈ s, ∫ ω, f i ω ∂μ) := by
    have hi : Integrable (fun ω => ∑ i ∈ s, f i ω) μ :=
      integrable_finsetSum s (fun i _ => hf i)
    have hnonneg : ∀ᵐ ω ∂μ, 0 ≤ (∑' i, f i ω) - ∑ i ∈ s, f i ω := by
      filter_upwards [hae] with ω hω
      exact sub_nonneg.mpr (hω.sum_le_tsum s (fun i _ => hn i ω))
    rw [eLpNorm_one_eq_lintegral_enorm]
    calc
      (∫⁻ ω, ‖((fun ω => ∑ i ∈ s, f i ω) - (fun ω => ∑' i, f i ω)) ω‖ₑ ∂μ) =
          ∫⁻ ω, ENNReal.ofReal ((∑' i, f i ω) - ∑ i ∈ s, f i ω) ∂μ := by
        apply lintegral_congr_ae
        filter_upwards [hnonneg] with ω hω
        simp only [Pi.sub_apply, ← ofReal_norm, Real.norm_eq_abs]
        rw [abs_sub_comm, abs_of_nonneg hω]
      _ = ENNReal.ofReal (∫ ω, (∑' i, f i ω) - ∑ i ∈ s, f i ω ∂μ) :=
        (ofReal_integral_eq_lintegral_ofReal (hint.sub hi) hnonneg).symm
      _ = _ := by rw [integral_sub hint hi, htotal, integral_finsetSum s (fun i _ => hf i)]
  have hsum : Tendsto (fun s : Finset ι => ∑ i ∈ s, ∫ ω, f i ω ∂μ)
      atTop (𝓝 (∑' i, ∫ ω, f i ω ∂μ)) := hs.hasSum
  have hlim := hsum.const_sub (∑' i, ∫ ω, f i ω ∂μ)
  simp only [sub_self] at hlim
  simpa only [Function.comp_def, ENNReal.ofReal_zero, heq] using
    (ENNReal.continuous_ofReal.tendsto 0).comp hlim

end Problem367.NonnegativeSeriesL1

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Stochastic_StoppedBrownianArraySquare
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace Problem367.StoppedBrownianArraySquare
open StoppedSimpleIntegral BrownianFiltration StoppedBrownianSquare

variable {Ω ι : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
  {F : Filtration ℝ≥0 mΩ}

private theorem finite_sum_martingale [IsFiniteMeasure P]
    (S : ι → ℝ≥0 → Ω → ℝ) (I : Finset ι)
    (hS : ∀ i ∈ I, Martingale (S i) F P) :
    Martingale (fun t ω => ∑ i ∈ I, S i t ω) F P := by
  classical
  induction I using Finset.induction_on with
  | empty =>
      convert martingale_zero ℝ F P using 1
      all_goals try with_reducible_and_instances rfl
      funext t ω
      simp
  | @insert i I hi ih =>
      have hm := (hS i (Finset.mem_insert_self i I)).add
        (ih (fun j hj => hS j (Finset.mem_insert_of_mem hj)))
      convert hm using 1
      all_goals try with_reducible_and_instances rfl
      funext t ω
      simp only [Finset.sum_insert hi, Pi.add_apply]

theorem finite_sum_compensated_square_martingale [IsFiniteMeasure P]
    (S A : ι → ℝ≥0 → Ω → ℝ)
    (hdiag : ∀ i, Martingale (fun t ω => S i t ω ^ 2 - A i t ω) F P)
    (hcross : Pairwise fun i j => Martingale (fun t ω => S i t ω * S j t ω) F P)
    (I : Finset ι) :
    Martingale (fun t ω => (∑ i ∈ I, S i t ω) ^ 2 - ∑ i ∈ I, A i t ω) F P := by
  classical
  induction I using Finset.induction_on with
  | empty =>
      convert martingale_zero ℝ F P using 1
      all_goals try with_reducible_and_instances rfl
      funext t ω
      simp
  | @insert i I hi ih =>
      have hm := finite_sum_martingale (fun j t ω => S i t ω * S j t ω) I
        (fun j hj => hcross (fun heq => hi (heq ▸ hj)))
      convert ((hdiag i).add ih).add (Martingale.smul 2 hm) using 1
      all_goals try with_reducible_and_instances rfl
      funext t ω
      simp only [Finset.sum_insert hi, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
        ← Finset.mul_sum]
      ring

end Problem367.StoppedBrownianArraySquare

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Martingales_SpatialCompensator
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Filter
open scoped Topology ENNReal NNReal

namespace Problem367.MartingaleSpatialCompensator

variable {Ω ι : Type*} [mΩ : MeasurableSpace Ω]
  {μ : Measure Ω} [IsFiniteMeasure μ] {F : Filtration ℝ≥0 mΩ}

theorem spatial_sum_compensatedSquare_martingale [Countable ι]
    {X A : ι → ℝ≥0 → Ω → ℝ} {Y : ℝ≥0 → Ω → ℝ}
    (hX2 : ∀ i t, MemLp (X i t) 2 μ)
    (hdiag : ∀ i, Martingale (fun t ω => X i t ω ^ 2 - A i t ω) F μ)
    (hcross : Pairwise fun i j => Martingale (fun t ω => X i t ω * X j t ω) F μ)
    (hAad : ∀ i, StronglyAdapted F (A i))
    (hAint : ∀ i t, Integrable (A i t) μ)
    (hAnonneg : ∀ i t ω, 0 ≤ A i t ω)
    (hAsum : ∀ t, Summable (fun i => ∫ ω, A i t ω ∂μ))
    (hYad : StronglyAdapted F Y) (hY2 : ∀ t, MemLp (Y t) 2 μ)
    (hYsum : ∀ t, HasSum (fun i => (hX2 i t).toLp (X i t)) ((hY2 t).toLp (Y t))) :
    Martingale (fun t ω => Y t ω ^ 2 - ∑' i, A i t ω) F μ := by
  classical
  apply CompensatedSquareLimit.martingale_compensatedSquare_of_limits
    (l := (atTop : Filter (Finset ι)))
    (X := fun s t ω => ∑ i ∈ s, X i t ω)
    (A := fun s t ω => ∑ i ∈ s, A i t ω)
  · intro s t
    exact memLp_finsetSum s (fun i _ => hX2 i t)
  · intro s t
    exact integrable_finsetSum s (fun i _ => hAint i t)
  · exact StoppedBrownianArraySquare.finite_sum_compensated_square_martingale X A hdiag hcross
  · exact hYad
  · exact hY2
  · intro t
    let : MeasurableSpace Ω := F t
    exact StronglyMeasurable.tsum (fun i => hAad i t)
  · intro t
    exact (NonnegativeSeriesL1.integrable_tsum_of_nonnegative
      (fun i => hAint i t) (fun i ω => hAnonneg i t ω) (hAsum t)).2.1
  · intro t
    apply CompensatedSquareLimit.tendsto_eLpNorm_two_of_meanSquare
      (fun s => memLp_finsetSum s (fun i _ => hX2 i t)) (hY2 t)
    exact PredictableL2.tendsto_integral_sq_error_of_hasSum
      (fun i => X i t) (fun i => hX2 i t) (hY2 t) (hYsum t)
  · intro t
    exact NonnegativeSeriesL1.tendsto_finsetSum_L1_of_nonnegative
      (fun i => hAint i t) (fun i ω => hAnonneg i t ω) (hAsum t)

end Problem367.MartingaleSpatialCompensator

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Brownian_SpatialCompensator
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
  {F : Filtration ℝ≥0 mΩ}

theorem nonnegativeCompensator_stronglyAdapted
    {H : ℝ≥0 → Ω → ℝ} (hH : StronglyAdapted F H) :
    StronglyAdapted F (nonnegativeCompensator H) := by
  intro t
  have hm := BrownianIntegralProcess.globalCompensator_stronglyAdapted hH t
  let : MeasurableSpace Ω := F t
  exact hm.sup stronglyMeasurable_const

theorem ae_nonnegativeCompensator_eq_global
    {H : ℝ≥0 → Ω → ℝ} (hc : ∀ᵐ ω ∂P, Continuous (fun t => H t ω)) :
    ∀ᵐ ω ∂P, ∀ t, nonnegativeCompensator H t ω =
      BrownianIntegralProcess.globalCompensator H t ω := by
  filter_upwards [BrownianIntegralProcess.ae_globalCompensator_eq_integral hc] with ω hω
  intro t
  unfold nonnegativeCompensator
  apply max_eq_left
  rw [hω t]
  exact intervalIntegral.integral_nonneg t.coe_nonneg (fun s _ => sq_nonneg _)

theorem nonnegativeCompensator_integrable [IsFiniteMeasure P]
    {H : ℝ≥0 → Ω → ℝ} (hH : StronglyAdapted F H)
    (hc : ∀ᵐ ω ∂P, Continuous (fun t => H t ω))
    {C : ℝ} (hC : 0 ≤ C) (hb : ∀ᵐ ω ∂P, ∀ t, |H t ω| ≤ C) (t : ℝ≥0) :
    Integrable (nonnegativeCompensator H t) P := by
  have hi : Integrable (BrownianIntegralProcess.globalCompensator H t) P :=
    (SelectedCompensator.selected_memLp hH hc hC hb t t 1).integrable le_rfl
  exact hi.sup (integrable_const 0)

theorem integral_nonnegativeCompensator_eq_sq [IsFiniteMeasure P]
    {H I : ℝ≥0 → Ω → ℝ}
    (hQ : Martingale (fun t ω => I t ω ^ 2 - nonnegativeCompensator H t ω) F P)
    (hI2 : ∀ t, MemLp (I t) 2 P) (hz : I 0 =ᵐ[P] 0)
    (hAint : ∀ t, Integrable (nonnegativeCompensator H t) P) (t : ℝ≥0) :
    (∫ ω, nonnegativeCompensator H t ω ∂P) = ∫ ω, I t ω ^ 2 ∂P := by
  have hzero : (∫ ω, I 0 ω ^ 2 - nonnegativeCompensator H 0 ω ∂P) = 0 := by
    calc
      _ = ∫ _ : Ω, (0 : ℝ) ∂P := by
        apply integral_congr_ae
        filter_upwards [hz] with ω hω
        simp only [hω, Pi.zero_apply, zero_pow (by norm_num : 2 ≠ 0),
          nonnegativeCompensator_zero, sub_zero]
      _ = 0 := integral_zero _ _
  have heq := hQ.setIntegral_eq (show (0 : ℝ≥0) ≤ t from bot_le) MeasurableSet.univ
  simp only [Measure.restrict_univ] at heq
  rw [hzero, integral_sub (hI2 t).integrable_sq (hAint t)] at heq
  linarith

theorem exists_global_continuous_spatial_integral_compensatedSquare_oai
    [Countable ι] [IsProbabilityMeasure P]
    {B H : ι → ℝ≥0 → Ω → ℝ}
    (hB : ∀ a, IsPreBrownianReal (B a) P)
    (hAd : ∀ a, StronglyAdapted F (B a))
    (hpast : ∀ s t, s ≤ t → Indep (MeasurableSpace.comap
      (fun ω a => B a t ω - B a s ω) inferInstance) (F s) P)
    (hind : ∀ s t, s ≤ t → Pairwise fun a b =>
      IndepFun (fun ω => B a t ω - B a s ω) (fun ω => B b t ω - B b s ω) P)
    (hBc : ∀ a, ∀ᵐ ω ∂P, Continuous (fun t => B a t ω))
    (hH : ∀ a, StronglyAdapted F (H a))
    (hc : ∀ a, ∀ᵐ ω ∂P, Continuous (fun t => H a t ω))
    {C : ι → ℝ} (hC : ∀ a, 0 ≤ C a)
    (hb : ∀ a, ∀ᵐ ω ∂P, ∀ t, |H a t ω| ≤ C a)
    (henergy : ∀ N : ℕ, Summable (fun a =>
      ∫ s in (0 : ℝ)..(N : ℝ), ∫ ω, H a s.toNNReal ω ^ 2 ∂P)) :
    ∃ (I : ι → ℝ≥0 → Ω → ℝ) (Y : ℝ≥0 → Ω → ℝ)
      (hI2 : ∀ a t, MemLp (I a t) 2 P) (hY2 : ∀ t, MemLp (Y t) 2 P),
      (∀ a, IsStronglyPredictable F (I a) ∧ Martingale (I a) F P ∧
        (∀ᵐ ω ∂P, Continuous (fun t => I a t ω))) ∧
      (∀ a (N : ℕ), 0 < N → ∀ t ≤ (N : ℝ≥0),
        Tendsto (fun n => ∫ ω,
          (BrownianIntegralProcess.stoppedUniformSum (B a) (H a) N n t ω - I a t ω) ^ 2 ∂P)
          atTop (𝓝 0)) ∧
      IsStronglyPredictable F Y ∧ Martingale Y F P ∧
      (∀ᵐ ω ∂P, Continuous (fun t => Y t ω)) ∧ Y 0 =ᵐ[P] 0 ∧
      (∀ t, (∫ ω, Y t ω ^ 2 ∂P) =
        ∑' a, ∫ s in (0 : ℝ)..(t : ℝ), ∫ ω, H a s.toNNReal ω ^ 2 ∂P) ∧
      (∀ t, HasSum (fun a => (hI2 a t).toLp (I a t)) ((hY2 t).toLp (Y t))) ∧
      (∀ T : ℝ≥0, Tendsto (fun q : Finset ι =>
        ∫ ω, MartingaleStrongMaximal.maximalSquare
          (MartingaleSpatialLimit.finiteSum I q - Y) T ω ∂P) atTop (𝓝 0)) ∧
      Martingale (fun t ω => Y t ω ^ 2 - spatialCompensator H t ω) F P ∧
      (∀ t, Integrable (spatialCompensator H t) P) ∧
      (∀ t, ∀ᵐ ω ∂P, Summable (fun a => nonnegativeCompensator (H a) t ω)) := by
  obtain ⟨I, hIp, hIM, hIc, hI2, hIz, hImean, hIiso, hIlim, hcross⟩ :=
    exists_global_continuous_channel_integrals hB hAd hpast hind hBc hH hc hC hb
  have horth (t : ℝ≥0) : Pairwise (fun a b => ∫ ω, I a t ω * I b t ω ∂P = 0) := by
    intro a b hab
    have heq := (hcross hab).setIntegral_eq
      (show (0 : ℝ≥0) ≤ t from bot_le) MeasurableSet.univ
    simp only [Measure.restrict_univ] at heq
    rw [← heq]
    calc
      _ = ∫ _ : Ω, (0 : ℝ) ∂P := by
        apply integral_congr_ae
        filter_upwards [hIz a] with ω hω
        simp only [hω, Pi.zero_apply, zero_mul]
      _ = 0 := integral_zero _ _
  have hIenergy (N : ℕ) : Summable (fun a => ∫ ω, I a (N : ℝ≥0) ω ^ 2 ∂P) := by
    simpa only [hIiso, NNReal.coe_natCast] using henergy N
  obtain ⟨Y, hY2, hYp, hYM, hYc, hYsum, hYmax⟩ :=
    MartingaleSpatialLimit.exists_continuous_martingale_sum hIM hI2 hIc horth hIenergy
  have hYiso (t : ℝ≥0) : (∫ ω, Y t ω ^ 2 ∂P) =
      ∑' a, ∫ s in (0 : ℝ)..(t : ℝ), ∫ ω, H a s.toNNReal ω ^ 2 ∂P := by
    have he := MartingaleSpatialLimit.summable_energy_of_integer hIM hI2 hIenergy t
    have hinner : Pairwise (fun a b => inner ℝ
        ((hI2 a t).toLp (I a t)) ((hI2 b t).toLp (I b t)) = 0) := by
      intro a b hab
      simpa only [PredictableL2.inner_toLp] using horth t hab
    have hn := PredictableL2.norm_tsum_sq_of_orthogonal
      (fun a => (hI2 a t).toLp (I a t)) hinner
      (by simpa only [PredictableL2.norm_toLp_sq] using he)
    rw [(hYsum t).tsum_eq] at hn
    simpa only [PredictableL2.norm_toLp_sq, hIiso] using hn
  have hYzero : Y 0 =ᵐ[P] 0 := by
    apply ae_eq_of_integral_sq_sub_eq_zero
    · simpa only [Pi.zero_apply, sub_zero] using (hY2 0).integrable_sq
    · simpa only [Pi.zero_apply, sub_zero, NNReal.coe_zero,
        intervalIntegral.integral_same, tsum_zero] using hYiso 0
  have hAad (a : ι) := nonnegativeCompensator_stronglyAdapted (hH a)
  have hAint (a : ι) (t : ℝ≥0) :=
    nonnegativeCompensator_integrable (hH a) (hc a) (hC a) (hb a) t
  have hdiag (a : ι) :
      Martingale (fun t ω => I a t ω ^ 2 - nonnegativeCompensator (H a) t ω) F P := by
    have hQ := BrownianIntegralProcess.global_compensatedSquare_of_integer_stopped_limits
      (hB a) (hAd a) (fun s t hst => coordinate_increment_indep_past (hpast s t hst) a)
      (hH a) (hc a) (hC a) (hb a) (hIM a).stronglyAdapted (hI2 a) (hIlim a)
    apply hQ.congr (fun t => (((hIM a).stronglyAdapted t).pow 2).sub (hAad a t))
    intro t
    filter_upwards [ae_nonnegativeCompensator_eq_global (hc a)] with ω hω
    change I a t ω ^ 2 - BrownianIntegralProcess.globalCompensator (H a) t ω =
      I a t ω ^ 2 - nonnegativeCompensator (H a) t ω
    rw [hω t]
  have hAsum (t : ℝ≥0) :
      Summable (fun a => ∫ ω, nonnegativeCompensator (H a) t ω ∂P) := by
    have he := MartingaleSpatialLimit.summable_energy_of_integer hIM hI2 hIenergy t
    simpa only [integral_nonnegativeCompensator_eq_sq (hdiag _) (hI2 _) (hIz _) (hAint _)] using he
  have hQ : Martingale (fun t ω => Y t ω ^ 2 - spatialCompensator H t ω) F P :=
    MartingaleSpatialCompensator.spatial_sum_compensatedSquare_martingale hI2 hdiag hcross
      hAad hAint (fun a t ω => le_max_right _ _) hAsum hYM.stronglyAdapted hY2 hYsum
  have hseries (t : ℝ≥0) := NonnegativeSeriesL1.integrable_tsum_of_nonnegative
    (fun a => hAint a t) (fun a ω => le_max_right (BrownianIntegralProcess.globalCompensator (H a) t ω) 0)
    (hAsum t)
  exact ⟨I, Y, hI2, hY2, (fun a => ⟨hIp a, hIM a, hIc a⟩), hIlim,
    hYp, hYM, hYc, hYzero, hYiso, hYsum, hYmax, hQ,
    (fun t => (hseries t).2.1), (fun t => (hseries t).1)⟩

end Problem367.BrownianArrayFiltration

end

end OAI
end

theorem solution.{u_1, u_2} : type_of% @OAI.Problem367.BrownianArrayFiltration.exists_global_continuous_spatial_integral_compensatedSquare_oai.{u_1, u_2} := @OAI.Problem367.BrownianArrayFiltration.exists_global_continuous_spatial_integral_compensatedSquare_oai.{u_1, u_2}
