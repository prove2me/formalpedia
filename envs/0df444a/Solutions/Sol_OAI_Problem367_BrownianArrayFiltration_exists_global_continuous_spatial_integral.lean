-- Prove2me | solution 1 for OAI.Problem367.BrownianArrayFiltration.exists_global_continuous_spatial_integral
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T01:39:35.528494+00:00
-- url     : https://prove2.me/submissions/be972059-e910-44c1-ab8d-941dd70d1892

import Mathlib
import Definitions.Def_Q243FI000
import Definitions.Def_Q243FI001
import Theorems.Thm_OAI_Problem367_BrownianIntegralProcess_exists_global_continuous_uniform_integral

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

theorem hasSum_integral_mul_of_hasSum
    {Ω ι : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    (f : ι → Ω → ℝ) (hf : ∀ i, MemLp (f i) 2 μ)
    {Y Z : Ω → ℝ} (hY : MemLp Y 2 μ) (hZ : MemLp Z 2 μ)
    (hYsum : HasSum (fun i => (hf i).toLp (f i)) (hY.toLp Y)) :
    HasSum (fun i => ∫ ω, Z ω * f i ω ∂μ) (∫ ω, Z ω * Y ω ∂μ) := by
  have h := hYsum.mapL (innerSL ℝ (hZ.toLp Z))
  change HasSum (fun i => inner ℝ (hZ.toLp Z) ((hf i).toLp (f i)))
    (inner ℝ (hZ.toLp Z) (hY.toLp Y)) at h
  simpa only [inner_toLp] using h

theorem integral_eq_zero_of_hasSum
    {Ω ι : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsFiniteMeasure μ]
    (f : ι → Ω → ℝ) (hf : ∀ i, MemLp (f i) 2 μ)
    {Y : Ω → ℝ} (hY : MemLp Y 2 μ)
    (hYsum : HasSum (fun i => (hf i).toLp (f i)) (hY.toLp Y))
    (hcenter : ∀ i, ∫ ω, f i ω ∂μ = 0) : ∫ ω, Y ω ∂μ = 0 := by
  have h := hasSum_integral_mul_of_hasSum f hf hY
    (memLp_const (1 : ℝ)) hYsum
  simp only [one_mul, hcenter] at h
  exact h.unique hasSum_zero

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

end Problem367.BrownianFiltration

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
-- module Solutions.Q243_FreeIsing.FreeIsing_Brownian_ContinuousSpatialIntegral
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
  {B : ι → ℝ≥0 → Ω → ℝ} {F : Filtration ℝ≥0 mΩ}

theorem stopped_grid_sums_orthogonal [IsProbabilityMeasure P]
    (hB : ∀ a, IsPreBrownianReal (B a) P)
    (hAd : ∀ a, StronglyAdapted F (B a))
    (hind : ∀ s t, s ≤ t → Indep
      (MeasurableSpace.comap (fun ω a => B a t ω - B a s ω) inferInstance) (F s) P)
    (hcross : ∀ s t, s ≤ t → Pairwise fun a b =>
      IndepFun (fun ω => B a t ω - B a s ω) (fun ω => B b t ω - B b s ω) P)
    (τ : ℕ → ℝ≥0) (hτ : Monotone τ) (H : ι → ℕ → Ω → ℝ)
    (hH : ∀ a i, StronglyMeasurable[F (τ i)] (H a i))
    (hH2 : ∀ a i, MemLp (H a i) 2 P)
    {a b : ι} (hab : a ≠ b) (u v : Finset ℕ) (t : ℝ≥0) :
    (∫ ω,
      (∑ i ∈ u, StoppedSimpleIntegral.intervalSum (B a) (H a i) (τ i) (τ (i + 1)) t ω) *
      (∑ i ∈ v, StoppedSimpleIntegral.intervalSum (B b) (H b i) (τ i) (τ (i + 1)) t ω)
      ∂P) = 0 := by
  classical
  let σ : ℕ → ℝ≥0 := fun i => min t (τ i)
  let G : ι → ℕ → Ω → ℝ := fun a i => if τ i ≤ t then H a i else 0
  have hσ : Monotone σ := fun i j hij => min_le_min_left t (hτ hij)
  have hG (a : ι) (i : ℕ) : StronglyMeasurable[F (σ i)] (G a i) := by
    change StronglyMeasurable[F (min t (τ i))] (if τ i ≤ t then H a i else 0)
    by_cases hi : τ i ≤ t
    · rw [ite_eq_left hi, min_eq_right hi]
      exact hH a i
    · rw [ite_eq_right hi]
      exact stronglyMeasurable_zero
  have hG2 (a : ι) (i : ℕ) : MemLp (G a i) 2 P := by
    by_cases hi : τ i ≤ t
    · simpa only [G, ite_eq_left hi] using hH2 a i
    · simp only [G, ite_eq_right hi]
      exact MemLp.zero
  have hterm (a : ι) (i : ℕ) (ω : Ω) :
      StoppedSimpleIntegral.intervalSum (B a) (H a i) (τ i) (τ (i + 1)) t ω =
        G a i ω * (B a (σ (i + 1)) ω - B a (σ i) ω) := by
    by_cases hi : τ i ≤ t
    · simp only [G, ite_eq_left hi, σ, StoppedSimpleIntegral.intervalSum]
    · have hti : t ≤ τ i := le_of_not_ge hi
      have hti' : t ≤ τ (i + 1) := hti.trans (hτ (Nat.le_succ i))
      simp only [G, ite_eq_right hi, σ, StoppedSimpleIntegral.intervalSum,
        min_eq_left hti, min_eq_left hti', sub_self, mul_zero, Pi.zero_apply]
  simp_rw [hterm]
  exact grid_sums_orthogonal hB hAd hind hcross σ hσ G hG hG2 hab u v

theorem stopped_uniform_limits_orthogonal [IsProbabilityMeasure P]
    (hB : ∀ a, IsPreBrownianReal (B a) P)
    (hAd : ∀ a, StronglyAdapted F (B a))
    (hind : ∀ s t, s ≤ t → Indep
      (MeasurableSpace.comap (fun ω a => B a t ω - B a s ω) inferInstance) (F s) P)
    (hcross : ∀ s t, s ≤ t → Pairwise fun a b =>
      IndepFun (fun ω => B a t ω - B a s ω) (fun ω => B b t ω - B b s ω) P)
    {H : ι → ℝ≥0 → Ω → ℝ} (hH : ∀ a, StronglyAdapted F (H a))
    (hH2 : ∀ a t, MemLp (H a t) 2 P) (T t : ℝ≥0)
    {I : ι → Ω → ℝ} (hI2 : ∀ a, MemLp (I a) 2 P)
    (hlim : ∀ a, Tendsto (fun n => ∫ ω,
      (BrownianIntegralProcess.stoppedUniformSum (B a) (H a) T n t ω - I a ω) ^ 2 ∂P)
      atTop (𝓝 0)) :
    Pairwise (fun a b => ∫ ω, I a ω * I b ω ∂P = 0) := by
  have hi (a : ι) (s t : ℝ≥0) (hst : s ≤ t) :
      Indep (MeasurableSpace.comap (fun ω => B a t ω - B a s ω) inferInstance) (F s) P :=
    coordinate_increment_indep_past (hind s t hst) a
  have hS2 (a : ι) (n : ℕ) :
      MemLp (BrownianIntegralProcess.stoppedUniformSum (B a) (H a) T n t) 2 P :=
    BrownianFiltration.stopped_predictable_sum_memLp_two (hB a) (hi a)
      (BrownianGrid.uniformGrid T n) (BrownianGrid.uniformGrid_mono T n)
      (fun i => H a (BrownianGrid.uniformGrid T n i)) (fun i => hH a _) (fun i => hH2 a _)
      (Finset.range n) t
  have hLp (a : ι) := BrownianIntegralProcess.L2_tendsto_of_integral_sq_sub_tendsto
    (hS2 a) (hI2 a) (hlim a)
  intro a b hab
  have hinner := (hLp a).inner (𝕜 := ℝ) (hLp b)
  have hz (n : ℕ) : inner ℝ
      ((hS2 a n).toLp (BrownianIntegralProcess.stoppedUniformSum (B a) (H a) T n t))
      ((hS2 b n).toLp (BrownianIntegralProcess.stoppedUniformSum (B b) (H b) T n t)) = 0 := by
    rw [PredictableL2.inner_toLp]
    exact stopped_grid_sums_orthogonal hB hAd hind hcross
      (BrownianGrid.uniformGrid T n) (BrownianGrid.uniformGrid_mono T n)
      (fun a i => H a (BrownianGrid.uniformGrid T n i))
      (fun a i => hH a _) (fun a i => hH2 a _) hab (Finset.range n) (Finset.range n) t
  have heq : inner ℝ ((hI2 a).toLp (I a)) ((hI2 b).toLp (I b)) = 0 :=
    tendsto_nhds_unique hinner (by simpa only [hz] using
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 0)))
  simpa only [PredictableL2.inner_toLp] using heq

theorem exists_global_continuous_spatial_integral_oai [Countable ι] [IsProbabilityMeasure P]
    (hB : ∀ a, IsPreBrownianReal (B a) P)
    (hAd : ∀ a, StronglyAdapted F (B a))
    (hind : ∀ s t, s ≤ t → Indep
      (MeasurableSpace.comap (fun ω a => B a t ω - B a s ω) inferInstance) (F s) P)
    (hcross : ∀ s t, s ≤ t → Pairwise fun a b =>
      IndepFun (fun ω => B a t ω - B a s ω) (fun ω => B b t ω - B b s ω) P)
    (hBc : ∀ a, ∀ᵐ ω ∂P, Continuous (fun t => B a t ω))
    (H : ι → ℝ≥0 → Ω → ℝ) (hH : ∀ a, StronglyAdapted F (H a))
    (hc : ∀ a, ∀ᵐ ω ∂P, Continuous (fun t => H a t ω))
    (C : ι → ℝ) (hC : ∀ a, 0 ≤ C a)
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
      (∀ t, (∫ ω, Y t ω ∂P) = 0) ∧
      (∀ t, (∫ ω, Y t ω ^ 2 ∂P) =
        ∑' a, ∫ s in (0 : ℝ)..(t : ℝ), ∫ ω, H a s.toNNReal ω ^ 2 ∂P) ∧
      (∀ t, HasSum (fun a => (hI2 a t).toLp (I a t)) ((hY2 t).toLp (Y t))) ∧
      (∀ T : ℝ≥0, Tendsto (fun q : Finset ι =>
        ∫ ω, MartingaleStrongMaximal.maximalSquare
          (MartingaleSpatialLimit.finiteSum I q - Y) T ω ∂P) atTop (𝓝 0)) := by
  have hi (a : ι) (s t : ℝ≥0) (hst : s ≤ t) :
      Indep (MeasurableSpace.comap (fun ω => B a t ω - B a s ω) inferInstance) (F s) P :=
    coordinate_increment_indep_past (hind s t hst) a
  have hH2 (a : ι) (t : ℝ≥0) : MemLp (H a t) 2 P := by
    apply MemLp.of_bound ((hH a t).mono (F.le t)).aestronglyMeasurable (C a)
    filter_upwards [hb a] with ω hω
    simpa only [Real.norm_eq_abs] using hω t
  have hex (a : ι) := BrownianIntegralProcess.exists_global_continuous_uniform_integral
    (hB a) (hAd a) (hi a) (hBc a) (hH a) (hc a) (hC a) (hb a)
  choose I hIp hIM hIc hI2 hIz hImean hIiso hIlim using hex
  have horth (t : ℝ≥0) : Pairwise (fun a b => ∫ ω, I a t ω * I b t ω ∂P = 0) := by
    obtain ⟨N, hN⟩ := exists_nat_ge t
    have ht : t ≤ ((N + 1 : ℕ) : ℝ≥0) :=
      hN.trans (by exact_mod_cast Nat.le_succ N)
    exact stopped_uniform_limits_orthogonal hB hAd hind hcross hH hH2
      ((N + 1 : ℕ) : ℝ≥0) t (fun a => hI2 a t)
      (fun a => hIlim a (N + 1) (Nat.succ_pos N) t ht)
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
  exact ⟨I, Y, hI2, hY2, (fun a => ⟨hIp a, hIM a, hIc a⟩), hIlim,
    hYp, hYM, hYc, hYzero,
    (fun t => PredictableL2.integral_eq_zero_of_hasSum
      (fun a => I a t) (fun a => hI2 a t) (hY2 t) (hYsum t) (fun a => hImean a t)),
    hYiso, hYsum, hYmax⟩

end Problem367.BrownianArrayFiltration

end

end OAI
end

theorem solution.{u_1, u_2} : type_of% @OAI.Problem367.BrownianArrayFiltration.exists_global_continuous_spatial_integral_oai.{u_1, u_2} := @OAI.Problem367.BrownianArrayFiltration.exists_global_continuous_spatial_integral_oai.{u_1, u_2}
