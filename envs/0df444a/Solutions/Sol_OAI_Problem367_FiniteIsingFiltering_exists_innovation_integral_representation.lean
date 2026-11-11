-- Prove2me | solution 1 for OAI.Problem367.FiniteIsingFiltering.exists_innovation_integral_representation
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T01:43:39.586775+00:00
-- url     : https://prove2.me/submissions/48ce2d53-55ad-4175-bfe8-0e3ec1ec53eb

import Mathlib
import Definitions.Def_FreeIsing
import Definitions.Def_Q243FI005
import Theorems.Thm_OAI_Problem367_FiniteIsingFiltering_tendsto_cross_uniformSum

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

theorem exists_channel_integrals [IsProbabilityMeasure P]
    (hB : ∀ a, IsPreBrownianReal (B a) P)
    (hAd : ∀ a, StronglyAdapted F (B a))
    (hind : ∀ s t, s ≤ t → Indep
      (MeasurableSpace.comap (fun ω a => B a t ω - B a s ω) inferInstance) (F s) P)
    (hcross : ∀ s t, s ≤ t → Pairwise fun a b =>
      IndepFun (fun ω => B a t ω - B a s ω) (fun ω => B b t ω - B b s ω) P)
    (H : ι → ℝ≥0 → Ω → ℝ) (hH : ∀ a, StronglyAdapted F (H a))
    (hc : ∀ a, ∀ᵐ ω ∂P, Continuous (fun t => H a t ω))
    (C : ι → ℝ) (hC : ∀ a, 0 ≤ C a)
    (hb : ∀ a, ∀ᵐ ω ∂P, ∀ t, |H a t ω| ≤ C a) (T : ℝ≥0) :
    ∃ I : ι → Ω → ℝ,
      (∀ a, MemLp (I a) 2 P) ∧
      (∀ a, StronglyMeasurable (I a)) ∧
      (∀ a, AEStronglyMeasurable[F T] (I a) P) ∧
      (∀ a, (∫ ω, I a ω ∂P) = 0) ∧
      (∀ a, (∫ ω, I a ω ^ 2 ∂P) =
        ∫ t in (0 : ℝ)..(T : ℝ), ∫ ω, H a t.toNNReal ω ^ 2 ∂P) ∧
      (Pairwise fun a b => ∫ ω, I a ω * I b ω ∂P = 0) ∧
      (∀ a, Tendsto (fun n => ∫ ω,
        (BrownianGrid.uniformSum (B a) (H a) T n ω - I a ω) ^ 2 ∂P) atTop (𝓝 0)) := by
  have hi (a : ι) (s t : ℝ≥0) (hst : s ≤ t) :
      Indep (MeasurableSpace.comap (fun ω => B a t ω - B a s ω) inferInstance) (F s) P :=
    coordinate_increment_indep_past (hind s t hst) a
  have hmH (a : ι) (t : ℝ≥0) : AEStronglyMeasurable (H a t) P :=
    ((hH a t).mono (F.le t)).aestronglyMeasurable
  have hH2 (a : ι) (t : ℝ≥0) : MemLp (H a t) 2 P := by
    apply MemLp.of_bound (hmH a t) (C a)
    filter_upwards [hb a] with ω hω
    simpa only [Real.norm_eq_abs] using hω t
  have hex (a : ι) := BrownianFiltrationGrid.exists_uniformSumLp_limit
    (hB a) (hAd a) (hi a) (H a) (hH a) (hH2 a) T
    (fun _ hε => MeanSquareContinuity.uniform_integral_sq_sub_le
      (hmH a) (hc a) (hC a) (hb a) T hε)
  choose I hI using hex
  have hprop (a : ι) := BrownianFiltrationGrid.uniformSumLp_limit_terminal_centered
    (hB a) (hAd a) (hi a) (H a) (hH a) (hH2 a) T (hI a)
  refine ⟨fun a => I a, fun a => Lp.memLp (I a), fun a => Lp.stronglyMeasurable (I a),
    fun a => (hprop a).1, fun a => (hprop a).2, ?_, ?_, ?_⟩
  · intro a
    exact BrownianFiltrationGrid.uniformSumLp_limit_isometry
      (hB a) (hAd a) (hi a) (H a) (hH a) (hH2 a) (hc a) (hC a) (hb a) T (hI a)
  · intro a b hab
    have hlim := (hI a).inner (𝕜 := ℝ) (hI b)
    have hz (n : ℕ) : inner ℝ
        (BrownianFiltrationGrid.uniformSumLp (hB a) (hAd a) (hi a) (H a) (hH a) (hH2 a) T n)
        (BrownianFiltrationGrid.uniformSumLp (hB b) (hAd b) (hi b) (H b) (hH b) (hH2 b) T n) = 0 := by
      rw [BrownianFiltrationGrid.uniformSumLp, BrownianFiltrationGrid.uniformSumLp,
        PredictableL2.inner_toLp]
      exact grid_sums_orthogonal hB hAd hind hcross
        (BrownianGrid.uniformGrid T n) (BrownianGrid.uniformGrid_mono T n)
        (fun a k => H a (BrownianGrid.uniformGrid T n k))
        (fun a k => hH a _) (fun a k => hH2 a _) hab (Finset.range n) (Finset.range n)
    have heq : inner ℝ (I a) (I b) = 0 :=
      tendsto_nhds_unique hlim (by simpa only [hz] using
        (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 0)))
    rw [L2.inner_def] at heq
    simpa only [Real.inner_apply] using heq
  · intro a
    exact BrownianFiltrationGrid.integral_sq_error_tendsto_of_Lp_tendsto
      (hB a) (hAd a) (hi a) (H a) (hH a) (hH2 a) T (hI a)

end Problem367.BrownianArrayFiltration

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Brownian_Innovation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped NNReal
open Problem367.ConditionalCharacteristic

namespace Problem367.BrownianInnovation

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}

theorem isBrownianReal_of_bounded_drift
    {F : Filtration ℝ≥0 mΩ} {B W : ℝ≥0 → Ω → ℝ}
    (hB : IsPreBrownianReal B P) (hW : Martingale W F P)
    (hvariance : ∀ a b : ℝ≥0, a ≤ b →
      P[(fun ω => (B b ω - B a ω)^2) | F a] =ᵐ[P]
        fun _ => (b : ℝ) - (a : ℝ))
    {L : ℝ} (hL : 0 ≤ L)
    (hbound : ∀ a b : ℝ≥0, a ≤ b → ∀ᵐ ω ∂P,
      |(W b ω - W a ω) - (B b ω - B a ω)| ≤ L * ((b : ℝ) - (a : ℝ)))
    (hzero : ∀ᵐ ω ∂P, W 0 ω = 0)
    (hcontinuous : ∀ᵐ ω ∂P, Continuous (fun t => W t ω)) :
    IsBrownianReal W P :=
  ⟨isPreBrownianReal_of_bounded_drift hB hW hvariance hL hbound hzero, hcontinuous⟩

end Problem367.BrownianInnovation

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Conditioning_GaussianVector
attribute [-instance] _root_.OAI.Problem367.WienerSampler.pathMeasurableSpace
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

section FiniteVector

variable {ι : Type*} [Fintype ι]

theorem product_gaussian_law_and_indep_of_condExp_unit_character
    {P : Measure Ω} [IsProbabilityMeasure P]
    (hm : m ≤ mΩ) {X : Ω → ι → ℝ} (hX : Measurable[mΩ] X)
    (v : ℝ≥0)
    (hchar : ∀ a : ι → ℝ, (∑ i, (a i) ^ 2) = 1 → ∀ u : ℝ,
      P[ConditionalCharacteristic.character (fun ω => ∑ i, a i * X ω i) u | m] =ᵐ[P]
        fun _ => Complex.exp (-((v : ℝ) : ℂ) * (u : ℂ) ^ 2 / 2))
    {E : Type*} [MeasurableSpace E] {Y : Ω → E} (hY : Measurable[m] Y) :
    HasLaw X (Measure.pi (fun _ : ι => gaussianReal 0 v)) P ∧ IndepFun X Y P := by
  exact product_gaussian_law_and_indep_of_condExp_linear_character hm hX
    (fun _ => v) (condExp_linear_character_of_unit_character hm v hchar) hY

end FiniteVector

end Problem367.ConditionalGaussianVector

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Estimates_BoundedInnovationDrift
attribute [-instance] _root_.OAI.Problem367.WienerSampler.pathMeasurableSpace
attribute [-simp] _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_apply _root_.OAI.Problem367.innovationPath_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal

namespace Problem367

theorem innovationCorrection_lipschitzWith
    {Ω : Type*} {m : ℝ≥0 → Ω → ℝ} {σ : Ω → ℝ}
    (hm : ∀ ω, Measurable (fun t => m t ω)) {C D : ℝ≥0}
    (hbound : ∀ t ω, ‖m t ω‖ ≤ (C : ℝ))
    (hσ : ∀ ω, ‖σ ω‖ ≤ (D : ℝ)) (ω : Ω) :
    LipschitzWith (D + C)
      (fun t : ℝ≥0 => (t : ℝ) * σ ω - nnrealTimePrimitive m t ω) := by
  apply LipschitzWith.of_dist_le_mul
  intro s t
  calc
    dist ((s : ℝ) * σ ω - nnrealTimePrimitive m s ω)
        ((t : ℝ) * σ ω - nnrealTimePrimitive m t ω)
      ≤ dist ((s : ℝ) * σ ω) ((t : ℝ) * σ ω) +
          dist (nnrealTimePrimitive m s ω) (nnrealTimePrimitive m t ω) :=
        dist_sub_sub_le _ _ _ _
    _ ≤ (D : ℝ) * dist s t + (C : ℝ) * dist s t := by
      apply add_le_add
      · rw [Real.dist_eq, ← sub_mul, abs_mul]
        calc
          |(s : ℝ) - (t : ℝ)| * |σ ω| ≤
              |(s : ℝ) - (t : ℝ)| * D :=
            mul_le_mul_of_nonneg_left (hσ ω) (abs_nonneg _)
          _ = (D : ℝ) * dist s t := by rw [mul_comm]; rfl
      · exact (lipschitzWith_nnrealTimePrimitive hm hbound ω).dist_le_mul s t
    _ = ((D + C : ℝ≥0) : ℝ) * dist s t := by
      push_cast
      ring

theorem innovationCorrection_two_lipschitzWith
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {F : Filtration ℝ≥0 mΩ} {m : ℝ≥0 → Ω → ℝ} {σ : Ω → ℝ}
    (hm : IsStronglyProgressive F m)
    (hbound : ∀ t ω, ‖m t ω‖ ≤ 1) (hσ : ∀ ω, ‖σ ω‖ ≤ 1) (ω : Ω) :
    LipschitzWith 2
      (fun t : ℝ≥0 => (t : ℝ) * σ ω - nnrealTimePrimitive m t ω) := by
  have h := innovationCorrection_lipschitzWith
    (measurable_path_of_isStronglyProgressive hm)
    (C := 1) (D := 1) hbound hσ ω
  norm_num at h ⊢
  exact h

end Problem367

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Gibbs_Weights
attribute [-instance] _root_.OAI.Problem367.IsingConditionalCopyBounds.graphLaw_isProbabilityMeasure _root_.OAI.Problem367.IsingObservationFactor.copies_probability _root_.OAI.Problem367.IsingObservationFactor.kernel_markov _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_observationLaw_probability _root_.OAI.Problem367.IsingObservationInnovation.observationLaw_probability _root_.OAI.Problem367.TreeKoopman.labelProbability _root_.OAI.Problem367.freeIsingMeasure_probability _root_.OAI.Problem367.reducedTailFintype _root_.OAI.Problem367.treeBallFintype _root_.OAI.Problem367.treeShellFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Problem367

theorem finiteIsing_partitionFunction
    {d : ℕ} (beta : ℝ) (D : Finset (TreeVertex d)) (hD : ConnectedFinset D) :
    (∑ eta : D → IsingSpin, Real.exp (beta * ∑ e ∈ inducedEdges D,
      spinSign (extendFiniteSpin D eta e.1) * spinSign (extendFiniteSpin D eta e.2))) =
      2 * (2 * Real.cosh beta) ^ (inducedEdges D).card := by
  classical
  have hden : 0 < 2 * (2 * Real.cosh beta) ^ (inducedEdges D).card := by
    positivity
  have hn := sum_freeCylinderWeight_eq_one (Real.neg_one_lt_tanh beta).le
    (Real.tanh_lt_one beta).le D hD
  simp_rw [freeCylinderWeight_tanh_eq_exp] at hn
  rw [← ENNReal.ofReal_sum_of_nonneg (fun eta _ =>
    div_nonneg (Real.exp_pos _).le hden.le)] at hn
  have hreal := ENNReal.ofReal_eq_one.mp hn
  rw [← Finset.sum_div] at hreal
  exact (div_eq_one_iff_eq (ne_of_gt hden)).mp hreal

end Problem367

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

lemma mean_const [Nonempty ι] (energy signal : ι → ℝ) (t c : ℝ) :
    mean energy signal (fun _ => c) t = c := by
  rw [mean_eq_sum_mass, ← Finset.mul_sum, sum_mass, mul_one]

omit [Fintype ι] in
lemma hasDerivAt_weight (energy signal : ι → ℝ) (t : ℝ) (s : ι) :
    HasDerivAt (fun x => weight energy signal x s)
      (signal s * weight energy signal t s) t := by
  simpa [weight, mul_comm] using
    (((hasDerivAt_id t).mul_const (signal s)).const_add (energy s)).exp

lemma hasDerivAt_partition (energy signal : ι → ℝ) (t : ℝ) :
    HasDerivAt (partition energy signal)
      (∑ s, signal s * weight energy signal t s) t := by
  exact HasDerivAt.fun_sum (fun s _ => hasDerivAt_weight energy signal t s)

theorem hasDerivAt_mean [Nonempty ι] (energy signal observable : ι → ℝ) (t : ℝ) :
    HasDerivAt (mean energy signal observable)
      (mean energy signal (fun s => observable s * signal s) t -
        mean energy signal observable t * mean energy signal signal t) t := by
  have hn : HasDerivAt (fun x => ∑ s, observable s * weight energy signal x s)
      (∑ s, (observable s * signal s) * weight energy signal t s) t := by
    simpa only [mul_assoc] using HasDerivAt.fun_sum
      (fun s (_ : s ∈ Finset.univ) =>
        (hasDerivAt_weight energy signal t s).const_mul (observable s))
  convert! hn.div (hasDerivAt_partition energy signal t)
    (partition_ne_zero energy signal t) using 1
  all_goals try with_reducible_and_instances rfl
  dsimp [mean]
  field_simp

theorem hasDerivAt_spin_mean [Nonempty ι] (energy spin : ι → ℝ) (t : ℝ)
    (hspin : ∀ s, spin s = -1 ∨ spin s = 1) :
    HasDerivAt (mean energy spin spin)
      (1 - (mean energy spin spin t) ^ 2) t := by
  have heq : (fun s => spin s * spin s) = (fun _ : ι => (1 : ℝ)) := by
    funext s
    rcases hspin s with hs | hs <;> simp [hs]
  have hd := hasDerivAt_mean energy spin spin t
  rw [heq, mean_const] at hd
  simpa only [← sq] using hd

end Problem367.FinitePosterior

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Posterior_Fields
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open scoped BigOperators

namespace Problem367.FinitePosterior

variable {S V : Type*} [Fintype S] [Fintype V]

lemma fieldMean_along_line (energy : S → ℝ) (spin : S → V → ℝ)
    (observable : S → ℝ) (x direction : V → ℝ) (t : ℝ) :
    fieldMean energy spin observable (fun v => x v + t * direction v) =
      mean (fieldEnergy energy spin x) (fun s => ∑ v, direction v * spin s v)
        observable t := by
  have heq (s : S) :
      fieldEnergy energy spin (fun v => x v + t * direction v) s =
        fieldEnergy energy spin x s + t * ∑ v, direction v * spin s v := by
    simp only [fieldEnergy, add_mul, Finset.sum_add_distrib,
      Finset.mul_sum, mul_assoc]
    ring
  simp only [fieldMean, heq, mean, partition, weight]

theorem hasDerivAt_fieldMean [Nonempty S] (energy : S → ℝ) (spin : S → V → ℝ)
    (observable : S → ℝ) (x direction : V → ℝ) :
    HasDerivAt (fun t => fieldMean energy spin observable (fun v => x v + t * direction v))
      (fieldMean energy spin (fun s => observable s * ∑ v, direction v * spin s v) x -
        fieldMean energy spin observable x *
          fieldMean energy spin (fun s => ∑ v, direction v * spin s v) x) 0 := by
  simp_rw [fieldMean_along_line]
  simpa only [mean_fieldEnergy_zero] using
    hasDerivAt_mean (fieldEnergy energy spin x)
      (fun s => ∑ v, direction v * spin s v) observable 0

end Problem367.FinitePosterior

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Posterior_Smooth
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open scoped BigOperators ContDiff

namespace Problem367.FinitePosterior

variable {S V : Type*} [Fintype S] [Fintype V]

omit [Fintype S] in

theorem contDiff_fieldEnergy (energy : S → ℝ) (spin : S → V → ℝ)
    (s : S) (n : ℕ∞ω) : ContDiff ℝ n (fun x => fieldEnergy energy spin x s) := by
  unfold fieldEnergy
  fun_prop

theorem contDiff_fieldPartition (energy : S → ℝ) (spin : S → V → ℝ)
    (n : ℕ∞ω) : ContDiff ℝ n (fun x => ∑ s, Real.exp (fieldEnergy energy spin x s)) := by
  apply ContDiff.sum
  intro s _
  exact (contDiff_fieldEnergy energy spin s n).exp

theorem contDiff_fieldMean_all [Nonempty S] (energy : S → ℝ) (spin : S → V → ℝ)
    (observable : S → ℝ) (n : ℕ∞ω) : ContDiff ℝ n (fieldMean energy spin observable) := by
  unfold fieldMean
  apply ContDiff.div
  · apply ContDiff.sum
    intro s _
    exact contDiff_const.mul (contDiff_fieldEnergy energy spin s n).exp
  · exact contDiff_fieldPartition energy spin n
  · intro x
    exact ne_of_gt (fieldPartition_pos energy spin x)

theorem fderiv_fieldMean_apply [Nonempty S] (energy : S → ℝ) (spin : S → V → ℝ)
    (observable : S → ℝ) (x direction : V → ℝ) :
    fderiv ℝ (fieldMean energy spin observable) x direction =
      fieldMean energy spin (fun s => observable s * ∑ v, direction v * spin s v) x -
        fieldMean energy spin observable x *
          fieldMean energy spin (fun s => ∑ v, direction v * spin s v) x := by
  have hd := ((contDiff_fieldMean_all energy spin observable 1).differentiable (by norm_num) x).hasFDerivAt
  have hl : HasDerivAt (fun t : ℝ => x + t • direction) direction 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const direction).const_add x
  have hc := hd.comp_hasDerivAt_of_eq 0 hl (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)
  have he := hasDerivAt_fieldMean energy spin observable x direction
  exact (show HasDerivAt
    (fun t => fieldMean energy spin observable (fun v => x v + t * direction v))
      (fderiv ℝ (fieldMean energy spin observable) x direction) 0 from hc).unique he

end Problem367.FinitePosterior

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Estimates_FiniteIsingZeroField
attribute [-instance] _root_.OAI.Problem367.IsingConditionalCopyBounds.graphLaw_isProbabilityMeasure _root_.OAI.Problem367.IsingObservationFactor.copies_probability _root_.OAI.Problem367.IsingObservationFactor.kernel_markov _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_observationLaw_probability _root_.OAI.Problem367.IsingObservationInnovation.observationLaw_probability _root_.OAI.Problem367.TreeKoopman.labelProbability _root_.OAI.Problem367.WienerSampler.pathMeasurableSpace _root_.OAI.Problem367.freeIsingMeasure_probability _root_.OAI.Problem367.reducedTailFintype _root_.OAI.Problem367.treeBallFintype _root_.OAI.Problem367.treeShellFintype
attribute [-simp] _root_.OAI.Problem367.ConnectedHull.pathAssignment_path _root_.OAI.Problem367.CutContinuationChannels.averageChannel_globalCone _root_.OAI.Problem367.CutContinuationChannels.continuationChannel_globalCone _root_.OAI.Problem367.FactorObservable.centeredSpinLp_coe _root_.OAI.Problem367.FiniteIsingSplit.splitEquiv_fst _root_.OAI.Problem367.FiniteIsingSplit.splitEquiv_snd _root_.OAI.Problem367.FinitePathGibbs.tailPartition_zero _root_.OAI.Problem367.IsingObservationInnovation.uniformObservation_relabel _root_.OAI.Problem367.PathSideBranches.restrictNoisyRegion_array _root_.OAI.Problem367.PosteriorChain.transition_spinMean _root_.OAI.Problem367.PosteriorChain.transition_sum _root_.OAI.Problem367.RootedBroadcast.pos_spinMul _root_.OAI.Problem367.RootedBroadcast.spinMul_pos _root_.OAI.Problem367.RootedBroadcast.spinMul_self _root_.OAI.Problem367.TreeGibbsAut.spinEquiv_apply_image _root_.OAI.Problem367.connectedSpinEncode_apply_root _root_.OAI.Problem367.connectedSpinEquiv_apply _root_.OAI.Problem367.spinAgreementCode_eq_neg_iff _root_.OAI.Problem367.spinAgreementCode_eq_pos_iff _root_.OAI.Problem367.spinSign_flip
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Problem367

private lemma spinSign_global_flip (s : IsingSpin) :
    spinSign s.flip = -spinSign s := by
  cases s <;> norm_num [IsingSpin.flip, spinSign]

theorem finiteIsingEnergy_flipConfig {d : ℕ} (beta : ℝ)
    (D : Finset (TreeVertex d)) (eta : D → IsingSpin) :
    finiteIsingEnergy beta D (flipConfig eta) = finiteIsingEnergy beta D eta := by
  classical
  unfold finiteIsingEnergy
  congr 1
  apply Finset.sum_congr rfl
  intro e he
  have hm := Finset.mem_product.mp (Finset.mem_filter.mp he).1
  have hsign (v : TreeVertex d) (hv : v ∈ D) :
      spinSign (extendFiniteSpin D (flipConfig eta) v) =
        -spinSign (extendFiniteSpin D eta v) := by
    simp only [extendFiniteSpin, dite_eq_left hv, flipConfig_apply, spinSign_global_flip]
  rw [hsign e.1 hm.1, hsign e.2 hm.2, neg_mul_neg]

theorem finiteIsingPosterior_zero_of_odd {d : ℕ} (beta : ℝ)
    (D : Finset (TreeVertex d)) (q : (D → IsingSpin) → ℝ)
    (hq : ∀ eta, q (flipConfig eta) = -q eta) :
    FinitePosterior.fieldMean (finiteIsingEnergy beta D)
      (fun (eta : D → IsingSpin) v => spinSign (eta v)) q (fun _ => 0) = 0 := by
  classical
  have hsum := (flipConfigMeasurableEquiv D).toEquiv.sum_comp
    (fun eta : D → IsingSpin => q eta * Real.exp (finiteIsingEnergy beta D eta))
  change (∑ eta : D → IsingSpin, q (flipConfig eta) *
    Real.exp (finiteIsingEnergy beta D (flipConfig eta))) =
      ∑ eta : D → IsingSpin, q eta * Real.exp (finiteIsingEnergy beta D eta) at hsum
  simp only [hq, finiteIsingEnergy_flipConfig, neg_mul, Finset.sum_neg_distrib] at hsum
  have hzero : (∑ eta : D → IsingSpin,
      q eta * Real.exp (finiteIsingEnergy beta D eta)) = 0 := by linarith
  simp only [FinitePosterior.fieldMean, FinitePosterior.fieldEnergy,
    zero_mul, Finset.sum_const_zero, add_zero, hzero, zero_div]

theorem finiteIsingPosterior_spin_zero {d : ℕ} (beta : ℝ)
    (D : Finset (TreeVertex d)) (v : D) :
    FinitePosterior.fieldMean (finiteIsingEnergy beta D)
      (fun (eta : D → IsingSpin) w => spinSign (eta w))
      (fun eta => spinSign (eta v)) (fun _ => 0) = 0 := by
  apply finiteIsingPosterior_zero_of_odd
  intro eta
  exact spinSign_global_flip (eta v)

end Problem367

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Posterior_GaussianTesting
attribute [-instance] _root_.OAI.Problem367.WienerSampler.pathMeasurableSpace _root_.OAI.Problem367.reducedTailFinite _root_.OAI.Problem367.treeBallFinite _root_.OAI.Problem367.treeShellFinite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal ProbabilityTheory

namespace Problem367

theorem gaussianPi_map_sqrt {I : Type*} [Fintype I]
    (t : ℝ) (ht : 0 ≤ t) :
    (Measure.pi (fun _ : I => gaussianReal 0 1)).map
      (fun x i => Real.sqrt t * x i) =
        Measure.pi (fun _ : I => gaussianReal 0 ⟨t, ht⟩) := by
  rw [Measure.pi_map_pi (μ := fun _ : I => gaussianReal 0 1)
    (f := fun _ (x : ℝ) => Real.sqrt t * x) (fun _ => by fun_prop)]
  congr 1
  funext i
  rw [gaussianReal_map_const_mul]
  congr 1
  · simp
  · apply NNReal.coe_injective
    change (Real.sqrt t) ^ 2 * 1 = t
    rw [mul_one, Real.sq_sqrt ht]

theorem finiteStandardGaussianPlanted_joint_law
    {S I : Type*} [Fintype S] [MeasurableSpace S] [MeasurableSingletonClass S]
    [Fintype I] (μ : Measure S) [IsProbabilityMeasure μ]
    (t : ℝ) (ht : 0 ≤ t) (spin : S → I → ℝ) :
    (μ.prod (Measure.pi (fun _ : I => gaussianReal 0 1))).map
      (fun z : S × (I → ℝ) =>
        (z.1, fun i => t * spin z.1 i + Real.sqrt t * z.2 i)) =
      μ ⊗ₘ finiteGaussianObservationKernel ⟨t, ht⟩ spin := by
  have : IsMarkovKernel (finiteGaussianObservationKernel ⟨t, ht⟩ spin) :=
    finiteGaussianObservationKernel_isMarkov ⟨t, ht⟩ spin
  apply map_planted_eq_compProd μ (Measure.pi (fun _ : I => gaussianReal 0 1))
    (finiteGaussianObservationKernel ⟨t, ht⟩ spin)
    (fun s x i => t * spin s i + Real.sqrt t * x i)
  · exact Measurable.of_eval (fun index =>
      (measurable_const.mul ((measurable_of_finite (fun state => spin state index)).comp
        measurable_fst)).add (measurable_const.mul
          ((measurable_pi_apply index).comp measurable_snd)))
  · intro s
    have hscale : Measurable (fun x : I → ℝ => fun i => Real.sqrt t * x i) := by
      fun_prop
    have hshift : Measurable (fun x : I → ℝ => fun i => t * spin s i + x i) := by
      fun_prop
    rw [show (fun x : I → ℝ => fun i => t * spin s i + Real.sqrt t * x i) =
      (fun x : I → ℝ => fun i => t * spin s i + x i) ∘
        (fun x : I → ℝ => fun i => Real.sqrt t * x i) from rfl,
      ← Measure.map_map hshift hscale, gaussianPi_map_sqrt t ht]
    exact gaussianPi_map_signal ⟨t, ht⟩ (spin s)

namespace FinitePosterior

theorem exponential_posterior_eq_fieldMean
    {S I : Type*} [Fintype S] [Nonempty S] [Fintype I]
    [MeasurableSpace S] (μ : Measure S) (energy : S → ℝ)
    (hprior : ∀ s, μ.real {s} = Real.exp (energy s) / ∑ a, Real.exp (energy a))
    (spin : S → I → ℝ) (q : S → ℝ) (x : I → ℝ) :
    (∑ s, μ.real {s} * Real.exp (∑ i, spin s i * x i) * q s) /
      (∑ s, μ.real {s} * Real.exp (∑ i, spin s i * x i)) =
      fieldMean energy spin q x := by
  let Z := ∑ s, Real.exp (energy s)
  have hZ : Z ≠ 0 := ne_of_gt (Finset.sum_pos
    (fun s _ => Real.exp_pos (energy s)) Finset.univ_nonempty)
  have hw (s : S) :
      μ.real {s} * Real.exp (∑ i, spin s i * x i) =
        Real.exp (fieldEnergy energy spin x s) / Z := by
    rw [hprior s]
    have hsum : (∑ i, spin s i * x i) = ∑ i, x i * spin s i := by
      apply Finset.sum_congr rfl
      intro i _
      ring
    rw [hsum]
    simp only [fieldEnergy, Real.exp_add, Z]
    ring
  simp_rw [hw, div_mul_eq_mul_div, ← Finset.sum_div]
  rw [div_div_div_cancel_right₀ hZ]
  unfold fieldMean
  congr 1
  apply Finset.sum_congr rfl
  intro s _
  ring

end FinitePosterior

theorem finiteStandardGaussianPlanted_condExp_fieldMean
    {S I : Type*} [Fintype S] [MeasurableSpace S] [MeasurableSingletonClass S]
    [StandardBorelSpace S] [Nonempty S] [Fintype I]
    (μ : Measure S) [IsProbabilityMeasure μ] (energy : S → ℝ)
    (hprior : ∀ s, μ.real {s} = Real.exp (energy s) / ∑ a, Real.exp (energy a))
    (t : ℝ) (ht : 0 ≤ t) (spin : S → I → ℝ)
    (hspin : ∀ s i, spin s i ^ 2 = 1) (q : S → ℝ) :
    let ρ := μ.prod (Measure.pi (fun _ : I => gaussianReal 0 1))
    let Y : S × (I → ℝ) → I → ℝ :=
      fun z i => t * spin z.1 i + Real.sqrt t * z.2 i
    ρ[fun z => q z.1 | (inferInstance : MeasurableSpace (I → ℝ)).comap Y] =ᵐ[ρ]
      fun z => FinitePosterior.fieldMean energy spin q (Y z) := by
  dsimp only
  have : IsMarkovKernel (finiteGaussianObservationKernel ⟨t, ht⟩ spin) :=
    finiteGaussianObservationKernel_isMarkov ⟨t, ht⟩ spin
  apply FiniteBayes.condExp_state_eq_of_posterior_integral
    (μ.prod (Measure.pi (fun _ : I => gaussianReal 0 1))) μ
    (finiteGaussianObservationKernel ⟨t, ht⟩ spin) Prod.fst
    (fun z i => t * spin z.1 i + Real.sqrt t * z.2 i) measurable_fst
    (by exact Measurable.of_eval (fun index =>
      (measurable_const.mul ((measurable_of_finite (fun state => spin state index)).comp
        measurable_fst)).add (measurable_const.mul
          ((measurable_pi_apply index).comp measurable_snd))))
    (finiteStandardGaussianPlanted_joint_law μ t ht spin) q
  filter_upwards [finiteGaussianObservation_posterior_mean μ ⟨t, ht⟩ spin hspin q]
    with x hx
  exact hx.trans (FinitePosterior.exponential_posterior_eq_fieldMean
    μ energy hprior spin q x)

theorem finiteStandardGaussianPlanted_integral_test_fieldMean
    {S I : Type*} [Fintype S] [MeasurableSpace S] [MeasurableSingletonClass S]
    [StandardBorelSpace S] [Nonempty S] [Fintype I]
    (μ : Measure S) [IsProbabilityMeasure μ] (energy : S → ℝ)
    (hprior : ∀ s, μ.real {s} = Real.exp (energy s) / ∑ a, Real.exp (energy a))
    (t : ℝ) (ht : 0 ≤ t) (spin : S → I → ℝ)
    (hspin : ∀ s i, spin s i ^ 2 = 1) (q : S → ℝ)
    (h : (I → ℝ) → ℝ) (hh : Measurable h) (C : ℝ)
    (hbound : ∀ x, ‖h x‖ ≤ C) :
    let ρ := μ.prod (Measure.pi (fun _ : I => gaussianReal 0 1))
    let Y : S × (I → ℝ) → I → ℝ :=
      fun z i => t * spin z.1 i + Real.sqrt t * z.2 i
    (∫ z, h (Y z) * q z.1 ∂ρ) =
      ∫ z, h (Y z) * FinitePosterior.fieldMean energy spin q (Y z) ∂ρ := by
  let ρ := μ.prod (Measure.pi (fun _ : I => gaussianReal 0 1))
  let Y : S × (I → ℝ) → I → ℝ :=
    fun z i => t * spin z.1 i + Real.sqrt t * z.2 i
  change (∫ z, h (Y z) * q z.1 ∂ρ) = _
  have hY : Measurable Y := by
    exact Measurable.of_eval (fun index =>
      (measurable_const.mul ((measurable_of_finite (fun state => spin state index)).comp
        measurable_fst)).add (measurable_const.mul
          ((measurable_pi_apply index).comp measurable_snd)))
  have hm : (inferInstance : MeasurableSpace (I → ℝ)).comap Y ≤
      (inferInstance : MeasurableSpace (S × (I → ℝ))) := hY.comap_le
  have htest : StronglyMeasurable[(inferInstance : MeasurableSpace (I → ℝ)).comap Y]
      (fun z => h (Y z)) :=
    (hh.comp (comap_measurable Y)).stronglyMeasurable
  have hq : Integrable (fun z : S × (I → ℝ) => q z.1) ρ := by
    apply (integrable_const (∑ s, |q s|)).mono'
    · exact ((measurable_of_finite q).comp measurable_fst).aestronglyMeasurable
    · filter_upwards [] with z
      rw [Real.norm_eq_abs]
      exact Finset.single_le_sum (fun s _ => abs_nonneg (q s)) (Finset.mem_univ z.1)
  have hpull := condExp_stronglyMeasurable_mul_of_bound hm htest hq C
    (Filter.Eventually.of_forall (fun z => hbound (Y z)))
  have hposterior := finiteStandardGaussianPlanted_condExp_fieldMean
    μ energy hprior t ht spin hspin q
  calc
    (∫ z, h (Y z) * q z.1 ∂ρ) =
        ∫ z, ρ[(fun z => h (Y z)) * (fun z => q z.1) | (inferInstance : MeasurableSpace (I → ℝ)).comap Y] z ∂ρ :=
      (integral_condExp hm).symm
    _ = ∫ z, h (Y z) * ρ[(fun z => q z.1) | (inferInstance : MeasurableSpace (I → ℝ)).comap Y] z ∂ρ :=
      integral_congr_ae hpull
    _ = ∫ z, h (Y z) * FinitePosterior.fieldMean energy spin q (Y z) ∂ρ := by
      apply integral_congr_ae
      filter_upwards [hposterior] with z hz
      rw [hz]

end Problem367

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Gaussian_FiniteIsingGaussianTesting
attribute [-instance] _root_.OAI.Problem367.IsingConditionalCopyBounds.graphLaw_isProbabilityMeasure _root_.OAI.Problem367.IsingObservationFactor.copies_probability _root_.OAI.Problem367.IsingObservationFactor.kernel_markov _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_observationLaw_probability _root_.OAI.Problem367.IsingObservationInnovation.observationLaw_probability _root_.OAI.Problem367.TreeKoopman.labelProbability _root_.OAI.Problem367.WienerSampler.pathMeasurableSpace _root_.OAI.Problem367.freeIsingMeasure_probability _root_.OAI.Problem367.reducedTailFintype _root_.OAI.Problem367.treeBallFintype _root_.OAI.Problem367.treeShellFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace Problem367

local instance instNonemptyIsingSpin_rc6668f_1 : Nonempty IsingSpin := ⟨.neg⟩
theorem HasFreeIsingLaw.restrict_real_eq_normalized_exp
    {d : ℕ} {beta : ℝ} {μ : Measure (TreeVertex d → IsingSpin)}
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ)
    (D : Finset (TreeVertex d)) (hD : ConnectedFinset D)
    (eta : D → IsingSpin) :
    (μ.map D.restrict).real {eta} =
      Real.exp (finiteIsingEnergy beta D eta) /
        ∑ xi, Real.exp (finiteIsingEnergy beta D xi) := by
  rw [Measure.real, hμ.restrict_atom D hD eta, freeCylinderWeight_tanh_eq_exp]
  rw [ENNReal.toReal_ofReal (by positivity)]
  rw [show (∑ xi, Real.exp (finiteIsingEnergy beta D xi)) =
    2 * (2 * Real.cosh beta) ^ (inducedEdges D).card from
      finiteIsing_partitionFunction beta D hD]
  rfl

end Problem367

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Gaussian_IntegrationByParts
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

theorem hasDerivAt_gaussianPDFReal (m : ℝ) {v : ℝ≥0} (hv : v ≠ 0) (x : ℝ) :
    HasDerivAt (gaussianPDFReal m v)
      (-(x - m) / (v : ℝ) * gaussianPDFReal m v x) x := by
  have hv' : (v : ℝ) ≠ 0 := by exact_mod_cast hv
  have h := (((((hasDerivAt_id x).sub_const m).pow 2).neg.div_const
    (2 * (v : ℝ))).exp).const_mul ((Real.sqrt (2 * Real.pi * v))⁻¹)
  convert! h using 1
  all_goals try with_reducible_and_instances rfl
  simp only [gaussianPDFReal, Pi.neg_apply, Pi.pow_apply, id_eq,
    Nat.cast_ofNat, Nat.reduceSub, pow_one, mul_one]
  field_simp

theorem integrable_gaussian_iff_density {m : ℝ} {v : ℝ≥0} (hv : v ≠ 0)
    {f : ℝ → ℝ} :
    Integrable f (gaussianReal m v) ↔
      Integrable (fun x => gaussianPDFReal m v x * f x) := by
  rw [gaussianReal_of_var_ne_zero _ hv]
  simpa only [toReal_gaussianPDF, smul_eq_mul] using
    (integrable_withDensity_iff_integrable_smul'
      (measurable_gaussianPDF m v)
      (Filter.Eventually.of_forall (fun _ => gaussianPDF_lt_top)) (g := f))

theorem gaussian_integral_centered_mul_eq_variance_mul_deriv
    (m : ℝ) (v : ℝ≥0) {f f' : ℝ → ℝ}
    (hf : ∀ x, HasDerivAt f (f' x) x)
    (hfi : Integrable f (gaussianReal m v))
    (hf'i : Integrable f' (gaussianReal m v))
    (hxfi : Integrable (fun x => (x - m) * f x) (gaussianReal m v)) :
    (∫ x, (x - m) * f x ∂gaussianReal m v) =
      (v : ℝ) * ∫ x, f' x ∂gaussianReal m v := by
  by_cases hv : v = 0
  · subst v
    simp
  have hv' : (v : ℝ) ≠ 0 := by exact_mod_cast hv
  have huf := (integrable_gaussian_iff_density hv).mp hfi
  have huf' := (integrable_gaussian_iff_density hv).mp hf'i
  have hxuf := (integrable_gaussian_iff_density hv).mp hxfi
  have hfirst : Integrable (fun x => f x *
      (-(x - m) / (v : ℝ) * gaussianPDFReal m v x)) := by
    convert hxuf.const_mul (-(v : ℝ)⁻¹) using 1
    all_goals try with_reducible_and_instances rfl
    ext x
    ring
  have hsecond : Integrable (fun x => f' x * gaussianPDFReal m v x) := by
    simpa only [mul_comm] using huf'
  have hproduct : Integrable (fun x => f x * gaussianPDFReal m v x) := by
    simpa only [mul_comm] using huf
  have hibp := integral_mul_deriv_eq_deriv_mul_of_integrable
    (u := f) (v := gaussianPDFReal m v)
    (u' := f') (v' := fun x => -(x - m) / (v : ℝ) * gaussianPDFReal m v x)
    (fun x _ => hf x) (fun x _ => hasDerivAt_gaussianPDFReal m hv x)
    hfirst hsecond hproduct
  have hfun : (fun x => f x * (-(x - m) / (v : ℝ) * gaussianPDFReal m v x)) =
      (fun x => -(v : ℝ)⁻¹ * (gaussianPDFReal m v x * ((x - m) * f x))) := by
    funext x
    ring
  rw [hfun, integral_const_mul] at hibp
  simp_rw [mul_comm (f' _) (gaussianPDFReal m v _)] at hibp
  rw [integral_gaussianReal_eq_integral_smul hv,
    integral_gaussianReal_eq_integral_smul hv]
  simp only [smul_eq_mul]
  have hmul := congrArg (fun z : ℝ => -(v : ℝ) * z) hibp
  field_simp at hmul
  simpa only [mul_assoc] using hmul

theorem gaussian_integral_centered_mul_of_bounded
    (m : ℝ) (v : ℝ≥0) {f f' : ℝ → ℝ} {C : ℝ}
    (hf : ∀ x, HasDerivAt f (f' x) x) (hbound : ∀ x, |f x| ≤ C)
    (hf'i : Integrable f' (gaussianReal m v)) :
    (∫ x, (x - m) * f x ∂gaussianReal m v) =
      (v : ℝ) * ∫ x, f' x ∂gaussianReal m v := by
  have hfm : AEStronglyMeasurable f (gaussianReal m v) :=
    (continuous_iff_continuousAt.mpr (fun x => (hf x).continuousAt)).aestronglyMeasurable
  have hb : ∀ᵐ x ∂gaussianReal m v, ‖f x‖ ≤ C :=
    Filter.Eventually.of_forall (fun x => by simpa only [Real.norm_eq_abs] using hbound x)
  have hfi := Integrable.of_bound hfm C hb
  have hxi : Integrable (fun x : ℝ => x - m) (gaussianReal m v) :=
    ((memLp_id_gaussianReal 1).integrable (by norm_num)).sub (integrable_const m)
  exact gaussian_integral_centered_mul_eq_variance_mul_deriv m v hf hfi hf'i
    (hxi.mul_bdd hfm hb)

theorem gaussian_integral_centered_mul_of_bounded_deriv
    (m : ℝ) (v : ℝ≥0) {f f' : ℝ → ℝ} {C D : ℝ}
    (hf : ∀ x, HasDerivAt f (f' x) x)
    (hbound : ∀ x, |f x| ≤ C) (hbound' : ∀ x, |f' x| ≤ D) :
    (∫ x, (x - m) * f x ∂gaussianReal m v) =
      (v : ℝ) * ∫ x, f' x ∂gaussianReal m v := by
  apply gaussian_integral_centered_mul_of_bounded m v hf hbound
  have heq : f' = deriv f := funext (fun x => (hf x).deriv.symm)
  have hfm : AEStronglyMeasurable f' (gaussianReal m v) := by
    rw [heq]
    exact aestronglyMeasurable_deriv f _
  exact Integrable.of_bound hfm D
    (Filter.Eventually.of_forall (fun x => by simpa only [Real.norm_eq_abs] using hbound' x))

end Problem367

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Gaussian_PiIntegrationByParts
attribute [-instance] _root_.OAI.Problem367.WienerSampler.pathMeasurableSpace _root_.OAI.Problem367.reducedTailFinite _root_.OAI.Problem367.reducedTailFintype _root_.OAI.Problem367.treeBallFinite _root_.OAI.Problem367.treeBallFintype _root_.OAI.Problem367.treeShellFinite _root_.OAI.Problem367.treeShellFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace Problem367

section CoordinateSplit

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem measurePreserving_funSplitAt (μ : ι → Measure ℝ)
    [∀ j, SigmaFinite (μ j)] (i : ι) :
    MeasurePreserving (Homeomorph.funSplitAt ℝ i) (Measure.pi μ)
      ((μ i).prod (Measure.pi fun j : {j // j ≠ i} => μ j)) := by
  let e := (Homeomorph.funSplitAt ℝ i).toMeasurableEquiv.symm
  apply MeasurePreserving.symm e
  refine ⟨e.measurable, (Measure.pi_eq fun s hs => ?_).symm⟩
  rw [e.map_apply]
  have hpre : e ⁻¹' Set.pi Set.univ s =
      s i ×ˢ Set.pi Set.univ (fun j : {j // j ≠ i} => s j) := by
    ext x
    simp only [Set.mem_preimage, Set.mem_pi, Set.mem_univ, forall_true_left,
      Set.mem_prod]
    constructor
    · intro h
      constructor
      · simpa [e, Homeomorph.funSplitAt, Homeomorph.piSplitAt,
          Equiv.piSplitAt] using h i
      · intro j
        simpa [e, Homeomorph.funSplitAt, Homeomorph.piSplitAt,
          Equiv.piSplitAt, j.property] using h j
    · rintro ⟨hi, hj⟩ j
      by_cases hji : j = i
      · subst j
        simpa [e, Homeomorph.funSplitAt, Homeomorph.piSplitAt,
          Equiv.piSplitAt] using hi
      · simpa [e, Homeomorph.funSplitAt, Homeomorph.piSplitAt,
          Equiv.piSplitAt, hji] using hj ⟨j, hji⟩
  rw [hpre, Measure.prod_prod, Measure.pi_pi]
  simpa using (Fintype.prod_eq_mul_prod_subtype_ne (fun j => μ j (s j)) i).symm

theorem gaussian_pi_integral_centered_mul_of_bounded_deriv
    (m : ι → ℝ) (v : ι → ℝ≥0) (i : ι)
    {f f' : (ι → ℝ) → ℝ} {C D : ℝ}
    (hfc : Continuous f) (hf'c : Continuous f')
    (hf : ∀ z t, HasDerivAt (fun r => f (Function.update z i r))
      (f' (Function.update z i t)) t)
    (hbound : ∀ z, |f z| ≤ C) (hbound' : ∀ z, |f' z| ≤ D) :
    (∫ z, (z i - m i) * f z ∂Measure.pi (fun j => gaussianReal (m j) (v j))) =
      (v i : ℝ) * ∫ z, f' z ∂Measure.pi (fun j => gaussianReal (m j) (v j)) := by
  let μ : ι → Measure ℝ := fun j => gaussianReal (m j) (v j)
  let ν := Measure.pi (fun j : {j // j ≠ i} => μ j)
  let e := (Homeomorph.funSplitAt ℝ i).toMeasurableEquiv.symm
  have hmp : MeasurePreserving e ((μ i).prod ν) (Measure.pi μ) :=
    (measurePreserving_funSplitAt μ i).symm
  have heval (x : ℝ × ({j // j ≠ i} → ℝ)) : e x i = x.1 := by
    simp [e, Homeomorph.funSplitAt, Homeomorph.piSplitAt, Equiv.piSplitAt]
  have hupdate (x : ℝ × ({j // j ≠ i} → ℝ)) (t : ℝ) :
      Function.update (e x) i t = e (t, x.2) := by
    ext j
    by_cases hji : j = i
    · subst j
      simp [heval]
    · simp [e, Homeomorph.funSplitAt,
        Homeomorph.piSplitAt, Equiv.piSplitAt, hji]
  have hxi : Integrable (fun z : ι → ℝ => z i - m i) (Measure.pi μ) := by
    have hi : Integrable (fun r : ℝ => r - m i) (μ i) :=
      ((memLp_id_gaussianReal 1).integrable (by norm_num)).sub (integrable_const _)
    exact (measurePreserving_eval μ i).integrable_comp_of_integrable hi
  have hxfi : Integrable (fun z : ι → ℝ => (z i - m i) * f z) (Measure.pi μ) :=
    hxi.mul_bdd hfc.aestronglyMeasurable (Filter.Eventually.of_forall fun z => by
      simpa only [Real.norm_eq_abs] using hbound z)
  have hf'i : Integrable f' (Measure.pi μ) :=
    Integrable.of_bound hf'c.aestronglyMeasurable D
      (Filter.Eventually.of_forall fun z => by
        simpa only [Real.norm_eq_abs] using hbound' z)
  have hprod := (hmp.integrable_comp_emb e.measurableEmbedding).2 hxfi
  have hprod' := (hmp.integrable_comp_emb e.measurableEmbedding).2 hf'i
  have hstein (y : {j // j ≠ i} → ℝ) :
      (∫ r, (r - m i) * f (e (r, y)) ∂μ i) =
        (v i : ℝ) * ∫ r, f' (e (r, y)) ∂μ i := by
    apply gaussian_integral_centered_mul_of_bounded_deriv (m i) (v i)
    · intro r
      simpa only [hupdate] using hf (e (0, y)) r
    · exact fun r => hbound _
    · exact fun r => hbound' _
  calc
    _ = ∫ x, (e x i - m i) * f (e x) ∂(μ i).prod ν :=
      (hmp.integral_comp e.measurableEmbedding _).symm
    _ = ∫ y, ∫ r, (r - m i) * f (e (r, y)) ∂μ i ∂ν := by
      simpa only [Function.comp_def, heval] using integral_prod_symm _ hprod
    _ = ∫ y, (v i : ℝ) * ∫ r, f' (e (r, y)) ∂μ i ∂ν := by
      congr 1
      funext y
      exact hstein y
    _ = (v i : ℝ) * ∫ x, f' (e x) ∂(μ i).prod ν := by
      rw [integral_const_mul]
      congr 1
      exact (integral_prod_symm _ hprod').symm
    _ = _ := by rw [hmp.integral_comp e.measurableEmbedding]

theorem gaussian_pi_integral_mul_affine_of_bounded_deriv
    (a b : ι → ℝ) (i : ι)
    {f f' : (ι → ℝ) → ℝ} {C D : ℝ}
    (hfc : Continuous f) (hf'c : Continuous f')
    (hf : ∀ z t, HasDerivAt (fun r => f (Function.update z i r))
      (f' (Function.update z i t)) t)
    (hbound : ∀ z, |f z| ≤ C) (hbound' : ∀ z, |f' z| ≤ D) :
    (∫ z, z i * f (fun j => a j + b j * z j)
      ∂Measure.pi (fun _ : ι => gaussianReal 0 1)) =
      b i * ∫ z, f' (fun j => a j + b j * z j)
        ∂Measure.pi (fun _ : ι => gaussianReal 0 1) := by
  let A : (ι → ℝ) → (ι → ℝ) := fun z j => a j + b j * z j
  have hAc : Continuous A := continuous_pi fun j =>
    continuous_const.add (continuous_const.mul (continuous_apply j))
  have hupdate (z : ι → ℝ) (t : ℝ) :
      A (Function.update z i t) = Function.update (A z) i (a i + b i * t) := by
    ext j
    by_cases hji : j = i
    · subst j
      simp [A]
    · simp [A, hji]
  have hd (z : ι → ℝ) (t : ℝ) :
      HasDerivAt (fun r => f (A (Function.update z i r)))
        (b i * f' (A (Function.update z i t))) t := by
    simp only [hupdate]
    simpa only [Function.comp_def, id_eq, mul_one, mul_comm] using
      (hf (A z) (a i + b i * t)).comp t
        (((hasDerivAt_id t).const_mul (b i)).const_add (a i))
  have hb' (z : ι → ℝ) : |b i * f' (A z)| ≤ |b i| * D := by
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left (hbound' _) (abs_nonneg _)
  have h := gaussian_pi_integral_centered_mul_of_bounded_deriv
    (fun _ => 0) (fun _ => 1) i (hfc.comp hAc)
    (continuous_const.mul (hf'c.comp hAc)) hd
    (fun z => hbound (A z)) hb'
  simpa only [Function.comp_def, Pi.mul_apply, A, sub_zero, NNReal.coe_one,
    one_mul, integral_const_mul] using h

end CoordinateSplit

end Problem367

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Posterior_FieldCalculus
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open scoped BigOperators ContDiff

namespace Problem367.FinitePosterior

variable {S : Type*} [Fintype S] [Nonempty S]

theorem hasDerivAt_mean_covariance (energy signal observable : S → ℝ) (t : ℝ) :
    HasDerivAt (mean energy signal observable)
      (tiltCovariance energy signal observable t) t :=
  hasDerivAt_mean energy signal observable t

theorem hasDerivAt_tiltCovariance (energy signal observable : S → ℝ) (t : ℝ)
    (hsignal : ∀ s, signal s = -1 ∨ signal s = 1) :
    HasDerivAt (tiltCovariance energy signal observable)
      (-2 * mean energy signal signal t * tiltCovariance energy signal observable t) t := by
  have hprod : (fun s => (observable s * signal s) * signal s) = observable := by
    funext s
    rcases hsignal s with hs | hs <;> simp [hs]
  have hc := hasDerivAt_mean energy signal (fun s => observable s * signal s) t
  rw [hprod] at hc
  have hm := hasDerivAt_mean energy signal observable t
  have hn := hasDerivAt_spin_mean energy signal t hsignal
  have hd := hc.sub (hm.mul hn)
  change HasDerivAt (tiltCovariance energy signal observable) _ t at hd
  apply hd.congr_deriv
  unfold tiltCovariance
  ring

theorem mean_square_drift_cancellation (energy signal observable : S → ℝ) (t : ℝ)
    (hsignal : ∀ s, signal s = -1 ∨ signal s = 1) :
    deriv (fun u => mean energy signal observable u ^ 2) t * mean energy signal signal t +
      (1 / 2 : ℝ) * deriv (deriv (fun u => mean energy signal observable u ^ 2)) t =
        tiltCovariance energy signal observable t ^ 2 := by
  have hfun : deriv (fun u => mean energy signal observable u ^ 2) =
      (fun u => 2 * mean energy signal observable u * tiltCovariance energy signal observable u) := by
    funext u
    have hd := (hasDerivAt_mean_covariance energy signal observable u).pow 2
    change HasDerivAt (fun u => mean energy signal observable u ^ 2) _ u at hd
    simpa only [Nat.cast_ofNat, Nat.reduceSub, pow_one] using hd.deriv
  rw [hfun]
  have hd := ((hasDerivAt_mean_covariance energy signal observable t).const_mul 2).mul
    (hasDerivAt_tiltCovariance energy signal observable t hsignal)
  change HasDerivAt (fun u => 2 * mean energy signal observable u *
    tiltCovariance energy signal observable u) _ t at hd
  rw [hd.deriv]
  ring

section Fields

variable {V : Type*} [Fintype V]

omit [Nonempty S] in
lemma fieldMean_sum_mul (energy : S → ℝ) (spin : S → V → ℝ)
    (observable : V → S → ℝ) (a : V → ℝ) (x : V → ℝ) :
    fieldMean energy spin (fun s => ∑ v, a v * observable v s) x =
      ∑ v, a v * fieldMean energy spin (observable v) x := by
  unfold fieldMean
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  simp only [Finset.sum_div, Finset.mul_sum, mul_div_assoc, mul_assoc]

theorem differentiable_fieldMean (energy : S → ℝ) (spin : S → V → ℝ)
    (observable : S → ℝ) : Differentiable ℝ (fieldMean energy spin observable) :=
  (contDiff_fieldMean_all energy spin observable 1).differentiable (by norm_num)

theorem fderiv_fieldMean_covariance_apply (energy : S → ℝ) (spin : S → V → ℝ)
    (observable : S → ℝ) (x direction : V → ℝ) :
    fderiv ℝ (fieldMean energy spin observable) x direction =
      ∑ v, direction v * fieldCovariance energy spin observable x v := by
  rw [fderiv_fieldMean_apply]
  have hobs : (fun s => observable s * ∑ v, direction v * spin s v) =
      (fun s => ∑ v, direction v * (observable s * spin s v)) := by
    funext s
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro v _
    ring
  rw [hobs, fieldMean_sum_mul, fieldMean_sum_mul]
  simp only [fieldCovariance, Finset.mul_sum, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro v _
  ring

theorem hasFDerivAt_fieldMean (energy : S → ℝ) (spin : S → V → ℝ)
    (observable : S → ℝ) (x : V → ℝ) :
    HasFDerivAt (fieldMean energy spin observable)
      (fieldMeanDerivative energy spin observable x) x := by
  have heq : fderiv ℝ (fieldMean energy spin observable) x =
      fieldMeanDerivative energy spin observable x := by
    ext direction
    rw [fderiv_fieldMean_covariance_apply]
    simp only [fieldMeanDerivative, sum_apply,
      smul_apply, ContinuousLinearMap.proj_apply, smul_eq_mul]
    apply Finset.sum_congr rfl
    intro v _
    ring
  rw [← heq]
  exact (differentiable_fieldMean energy spin observable x).hasFDerivAt

variable [DecidableEq V]

omit [Nonempty S] in
lemma fieldMean_coordinate_tilt (energy : S → ℝ) (spin : S → V → ℝ)
    (observable : S → ℝ) (x : V → ℝ) (u : V) (t : ℝ) :
    fieldMean energy spin observable (fun v => x v + if v = u then t else 0) =
      mean (fieldEnergy energy spin x) (fun s => spin s u) observable t := by
  simpa only [mul_ite, mul_one, mul_zero, ite_mul, one_mul, zero_mul,
    Finset.sum_ite_eq', Finset.mem_univ, ite_true, if_true] using
    fieldMean_along_line energy spin observable x (fun v => if v = u then 1 else 0) t

end Fields

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

omit [Fintype S] [Nonempty S] in
lemma abs_spin_eq_one (signal : S → ℝ)
    (hsignal : ∀ s, signal s = -1 ∨ signal s = 1) (s : S) : |signal s| = 1 := by
  rcases hsignal s with hs | hs <;> simp [hs]

theorem abs_mean_spin_le_one (energy signal : S → ℝ) (t : ℝ)
    (hsignal : ∀ s, signal s = -1 ∨ signal s = 1) :
    |mean energy signal signal t| ≤ 1 :=
  abs_mean_le energy signal signal t 1 (fun s => (abs_spin_eq_one signal hsignal s).le)

theorem abs_tiltCovariance_le (energy signal observable : S → ℝ) (t A : ℝ)
    (hsignal : ∀ s, signal s = -1 ∨ signal s = 1)
    (hbound : ∀ s, |observable s| ≤ A) :
    |tiltCovariance energy signal observable t| ≤ 2 * A := by
  have hA : 0 ≤ A := (abs_nonneg (observable (Classical.arbitrary S))).trans
    (hbound (Classical.arbitrary S))
  have hprod : ∀ s, |observable s * signal s| ≤ A := by
    intro s
    rw [abs_mul, abs_spin_eq_one signal hsignal s, mul_one]
    exact hbound s
  unfold tiltCovariance
  calc
    |mean energy signal (fun s => observable s * signal s) t -
        mean energy signal observable t * mean energy signal signal t| ≤
      |mean energy signal (fun s => observable s * signal s) t| +
        |mean energy signal observable t * mean energy signal signal t| := abs_sub _ _
    _ ≤ A + A * 1 := add_le_add (abs_mean_le energy signal _ t A hprod)
      (by
        rw [abs_mul]
        exact mul_le_mul (abs_mean_le energy signal observable t A hbound)
          (abs_mean_spin_le_one energy signal t hsignal) (abs_nonneg _) hA)
    _ = 2 * A := by ring

lemma deriv_mean_square (energy signal observable : S → ℝ) (t : ℝ) :
    deriv (fun u => mean energy signal observable u ^ 2) t =
      2 * mean energy signal observable t * tiltCovariance energy signal observable t := by
  have hd := (hasDerivAt_mean_covariance energy signal observable t).pow 2
  change HasDerivAt (fun u => mean energy signal observable u ^ 2) _ t at hd
  simpa only [Nat.cast_ofNat, Nat.reduceSub, pow_one] using hd.deriv

theorem abs_deriv_mean_square_le (energy signal observable : S → ℝ) (t A : ℝ)
    (hsignal : ∀ s, signal s = -1 ∨ signal s = 1)
    (hbound : ∀ s, |observable s| ≤ A) :
    |deriv (fun u => mean energy signal observable u ^ 2) t| ≤ 4 * A ^ 2 := by
  have hA : 0 ≤ A := (abs_nonneg (observable (Classical.arbitrary S))).trans
    (hbound (Classical.arbitrary S))
  rw [deriv_mean_square, abs_mul, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
  have hm := abs_mean_le energy signal observable t A hbound
  have hc := abs_tiltCovariance_le energy signal observable t A hsignal hbound
  calc
    2 * |mean energy signal observable t| * |tiltCovariance energy signal observable t| ≤
      2 * A * (2 * A) := by gcongr
    _ = 4 * A ^ 2 := by ring

theorem abs_deriv_deriv_mean_square_le (energy signal observable : S → ℝ) (t A : ℝ)
    (hsignal : ∀ s, signal s = -1 ∨ signal s = 1)
    (hbound : ∀ s, |observable s| ≤ A) :
    |deriv (deriv (fun u => mean energy signal observable u ^ 2)) t| ≤ 16 * A ^ 2 := by
  have he := mean_square_drift_cancellation energy signal observable t hsignal
  have hderiv := abs_deriv_mean_square_le energy signal observable t A hsignal hbound
  have hmean := abs_mean_spin_le_one energy signal t hsignal
  have hcov := abs_tiltCovariance_le energy signal observable t A hsignal hbound
  have hA : 0 ≤ A := (abs_nonneg (observable (Classical.arbitrary S))).trans
    (hbound (Classical.arbitrary S))
  have hsq : tiltCovariance energy signal observable t ^ 2 ≤ 4 * A ^ 2 := by
    have hs := mul_le_mul hcov hcov (abs_nonneg _) (by positivity : 0 ≤ 2 * A)
    nlinarith [sq_abs (tiltCovariance energy signal observable t)]
  have heq : deriv (deriv (fun u => mean energy signal observable u ^ 2)) t =
      2 * (tiltCovariance energy signal observable t ^ 2 -
        deriv (fun u => mean energy signal observable u ^ 2) t * mean energy signal signal t) := by
    linarith
  rw [heq, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
  calc
    2 * |tiltCovariance energy signal observable t ^ 2 -
        deriv (fun u => mean energy signal observable u ^ 2) t * mean energy signal signal t| ≤
      2 * (|tiltCovariance energy signal observable t ^ 2| +
        |deriv (fun u => mean energy signal observable u ^ 2) t * mean energy signal signal t|) := by
          exact mul_le_mul_of_nonneg_left (abs_sub _ _) (by norm_num)
    _ ≤ 2 * (4 * A ^ 2 + 4 * A ^ 2 * 1) := by
      rw [abs_of_nonneg (sq_nonneg _), abs_mul]
      gcongr
    _ = 16 * A ^ 2 := by ring

section Fields

variable {V : Type*} [Fintype V]

theorem abs_fieldMean_le (energy : S → ℝ) (spin : S → V → ℝ)
    (observable : S → ℝ) (x : V → ℝ) (A : ℝ)
    (hbound : ∀ s, |observable s| ≤ A) :
    |fieldMean energy spin observable x| ≤ A := by
  rw [← mean_fieldEnergy_zero energy spin (fun _ => 0)]
  exact abs_mean_le _ _ _ _ _ hbound

theorem abs_fieldCovariance_le (energy : S → ℝ) (spin : S → V → ℝ)
    (observable : S → ℝ) (x : V → ℝ) (u : V) (A : ℝ)
    (hcoord : ∀ s, spin s u = -1 ∨ spin s u = 1)
    (hbound : ∀ s, |observable s| ≤ A) :
    |fieldCovariance energy spin observable x u| ≤ 2 * A := by
  have h := abs_tiltCovariance_le (fieldEnergy energy spin x) (fun s => spin s u)
    observable 0 A hcoord hbound
  simpa only [tiltCovariance, mean_fieldEnergy_zero, fieldCovariance] using h

theorem abs_fieldMean_square_le (energy : S → ℝ) (spin : S → V → ℝ)
    (observable : S → ℝ) (x : V → ℝ) (A : ℝ)
    (hbound : ∀ s, |observable s| ≤ A) :
    |fieldMean energy spin observable x ^ 2| ≤ A ^ 2 := by
  have h := abs_fieldMean_le energy spin observable x A hbound
  have hA : 0 ≤ A := (abs_nonneg _).trans h
  have hs := mul_le_mul h h (abs_nonneg _) hA
  rw [abs_of_nonneg (sq_nonneg _)]
  nlinarith [sq_abs (fieldMean energy spin observable x)]

variable [DecidableEq V]

theorem abs_deriv_deriv_fieldMean_square_coordinate_le
    (energy : S → ℝ) (spin : S → V → ℝ) (observable : S → ℝ)
    (x : V → ℝ) (u : V) (t A : ℝ)
    (hcoord : ∀ s, spin s u = -1 ∨ spin s u = 1)
    (hbound : ∀ s, |observable s| ≤ A) :
    |deriv (deriv (fun r => fieldMean energy spin observable
      (fun v => x v + if v = u then r else 0) ^ 2)) t| ≤ 16 * A ^ 2 := by
  simp_rw [fieldMean_coordinate_tilt]
  exact abs_deriv_deriv_mean_square_le _ _ _ _ _ hcoord hbound

end Fields

end Problem367.FinitePosterior

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Posterior_SqrtObservationDerivative
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Filter Set
open scoped Topology

namespace Problem367

theorem hasDerivAt_integral_sqrt_observation_vector
    {Ω E : Type*} [MeasurableSpace Ω] [NormedAddCommGroup E] [NormedSpace ℝ E]
    {P : Measure Ω} [IsFiniteMeasure P]
    {S G : Ω → E} (hS : Integrable S P) (hG : Integrable G P)
    {f : E → ℝ} {f' : E → E →L[ℝ] ℝ}
    (hf : ∀ x, HasFDerivAt f (f' x) x) (hf'cont : Continuous f')
    {C M : ℝ} (hfbound : ∀ x, |f x| ≤ C) (hM : 0 ≤ M)
    (hf'bound : ∀ x, ‖f' x‖ ≤ M) {t : ℝ} (ht : 0 < t) :
    Integrable (fun ω => f' (t • S ω + Real.sqrt t • G ω)
      (S ω + (1 / (2 * Real.sqrt t)) • G ω)) P ∧
    HasDerivAt (fun r : ℝ => ∫ ω, f (r • S ω + Real.sqrt r • G ω) ∂P)
      (∫ ω, f' (t • S ω + Real.sqrt t • G ω)
        (S ω + (1 / (2 * Real.sqrt t)) • G ω) ∂P) t := by
  have hfcont : Continuous f := continuous_iff_continuousAt.mpr
    (fun x => (hf x).continuousAt)
  let F : ℝ → Ω → ℝ := fun r ω => f (r • S ω + Real.sqrt r • G ω)
  let F' : ℝ → Ω → ℝ := fun r ω => f' (r • S ω + Real.sqrt r • G ω)
    (S ω + (1 / (2 * Real.sqrt r)) • G ω)
  let a : ℝ := 1 / (2 * Real.sqrt (t / 2))
  have ha : 0 ≤ a := by dsimp [a] <;> positivity
  have hargm (r : ℝ) : AEStronglyMeasurable
      (fun ω => r • S ω + Real.sqrt r • G ω) P :=
    (hS.aestronglyMeasurable.const_smul r).add
      (hG.aestronglyMeasurable.const_smul (Real.sqrt r))
  have hFm (r : ℝ) : AEStronglyMeasurable (F r) P :=
    hfcont.comp_aestronglyMeasurable (hargm r)
  have hFint : Integrable (F t) P := by
    apply (integrable_const C).mono' (hFm t)
    exact Eventually.of_forall fun ω => by
      simpa only [Real.norm_eq_abs] using (hfbound (t • S ω + Real.sqrt t • G ω))
  have hF'm (r : ℝ) : AEStronglyMeasurable (F' r) P :=
    (isBoundedBilinearMap_apply (𝕜 := ℝ) (E := E) (F := ℝ)).continuous
      |>.comp_aestronglyMeasurable
        ((hf'cont.comp_aestronglyMeasurable (hargm r)).prodMk
          (hS.aestronglyMeasurable.add
            (hG.aestronglyMeasurable.const_smul (1 / (2 * Real.sqrt r)))))
  have hdom : Integrable (fun ω => M * (‖S ω‖ + a * ‖G ω‖)) P :=
    (hS.norm.add (hG.norm.const_mul a)).const_mul M
  have hbound : ∀ᵐ ω ∂P, ∀ r ∈ Ioi (t / 2),
      ‖F' r ω‖ ≤ M * (‖S ω‖ + a * ‖G ω‖) := by
    filter_upwards [] with ω
    intro r hr
    have hrpos : 0 < r := lt_trans (by linarith) hr
    have hden : 0 < 2 * Real.sqrt (t / 2) := by positivity
    have hrecip : 1 / (2 * Real.sqrt r) ≤ a := by
      apply one_div_le_one_div_of_le hden
      exact mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hr.le) (by norm_num)
    have hinner : ‖S ω + (1 / (2 * Real.sqrt r)) • G ω‖ ≤
        ‖S ω‖ + a * ‖G ω‖ := by
      calc
        _ ≤ ‖S ω‖ + ‖(1 / (2 * Real.sqrt r)) • G ω‖ := norm_add_le _ _
        _ = ‖S ω‖ + (1 / (2 * Real.sqrt r)) * ‖G ω‖ := by
          rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
        _ ≤ ‖S ω‖ + a * ‖G ω‖ := by gcongr
    exact ((f' (r • S ω + Real.sqrt r • G ω)).le_opNorm _).trans
      (mul_le_mul (hf'bound _) hinner (norm_nonneg _) hM)
  have hdiff : ∀ᵐ ω ∂P, ∀ r ∈ Ioi (t / 2),
      HasDerivAt (fun q => F q ω) (F' r ω) r := by
    filter_upwards [] with ω
    intro r hr
    have hrpos : 0 < r := lt_trans (by linarith) hr
    have harg := ((hasDerivAt_id r).smul_const (S ω)).add
      ((Real.hasDerivAt_sqrt hrpos.ne').smul_const (G ω))
    have harg' : HasDerivAt (fun q : ℝ => q • S ω + Real.sqrt q • G ω)
        (S ω + (1 / (2 * Real.sqrt r)) • G ω) r := by
      simpa only [Pi.add_def, id_eq, one_smul, one_div] using harg
    exact (hf (r • S ω + Real.sqrt r • G ω)).comp_hasDerivAt r harg'
  exact hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (Ioi_mem_nhds (by linarith : t / 2 < t))
    (Eventually.of_forall hFm) hFint (hF'm t) hbound hdom hdiff

theorem continuous_integral_sqrt_observation
    {Ω E : Type*} [MeasurableSpace Ω] [NormedAddCommGroup E] [NormedSpace ℝ E]
    {P : Measure Ω} [IsFiniteMeasure P] {S G : Ω → E}
    (hS : AEStronglyMeasurable S P) (hG : AEStronglyMeasurable G P)
    {f : E → ℝ} (hf : Continuous f) {C : ℝ} (hbound : ∀ x, |f x| ≤ C) :
    Continuous (fun t : ℝ => ∫ ω, f (t • S ω + Real.sqrt t • G ω) ∂P) := by
  apply continuous_of_dominated (bound := fun _ => C)
  · intro t
    exact hf.comp_aestronglyMeasurable
      ((hS.const_smul t).add (hG.const_smul (Real.sqrt t)))
  · intro t
    exact Eventually.of_forall fun ω => by
      simpa only [Real.norm_eq_abs] using hbound (t • S ω + Real.sqrt t • G ω)
  · exact integrable_const C
  · exact Eventually.of_forall fun ω => hf.comp
      ((continuous_id.smul continuous_const).add
        (Real.continuous_sqrt.smul continuous_const))

end Problem367

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Posterior_GaussianTimeDerivative
attribute [-instance] _root_.OAI.Problem367.WienerSampler.pathMeasurableSpace _root_.OAI.Problem367.reducedTailFinite _root_.OAI.Problem367.treeBallFinite _root_.OAI.Problem367.treeShellFinite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped BigOperators Topology

namespace Problem367.FinitePosterior

variable {V : Type*} [Fintype V]

section Expectation

variable {Ω : Type*} [MeasurableSpace Ω]

theorem hasDerivAt_integral_gaussianObservationCurve
    (μ : Measure Ω) [IsFiniteMeasure μ]
    (f : (V → ℝ) → ℝ) (g : (V → ℝ) → V → ℝ)
    (hdf : ∀ x, HasFDerivAt f (∑ v, g x v •
      (ContinuousLinearMap.proj v : (V → ℝ) →L[ℝ] ℝ)) x)
    (hg : ∀ v, Continuous (fun x => g x v))
    (M C : ℝ) (hC : 0 ≤ C)
    (hfbound : ∀ x, |f x| ≤ M) (hgbound : ∀ x v, |g x v| ≤ C)
    (signal noise : Ω → V → ℝ)
    (hsignal : Measurable signal) (hnoise : Measurable noise)
    (hspin : ∀ ω v, |signal ω v| ≤ 1)
    (hnoiseInt : ∀ v, Integrable (fun ω => noise ω v) μ)
    {t : ℝ} (ht : 0 < t) :
    HasDerivAt (fun r => ∫ ω, f (gaussianObservationCurve (signal ω) (noise ω) r) ∂μ)
      (∫ ω, ∑ v, g (gaussianObservationCurve (signal ω) (noise ω) t) v *
        gaussianObservationVelocity (signal ω) (noise ω) t v ∂μ) t := by
  let D : (V → ℝ) → (V → ℝ) →L[ℝ] ℝ := fun x => ∑ v, g x v •
    (ContinuousLinearMap.proj v : (V → ℝ) →L[ℝ] ℝ)
  have hDcont : Continuous D := by
    apply continuous_finsetSum
    intro v _
    exact (hg v).smul continuous_const
  have hDbound (x : V → ℝ) : ‖D x‖ ≤ (Fintype.card V : ℝ) * C := by
    apply ContinuousLinearMap.opNorm_le_bound _ (mul_nonneg (by positivity) hC)
    intro y
    simp only [D, sum_apply, smul_apply, ContinuousLinearMap.proj_apply, smul_eq_mul]
    calc
      ‖∑ v, g x v * y v‖ ≤ ∑ v, ‖g x v * y v‖ := norm_sum_le _ _
      _ ≤ ∑ v : V, C * ‖y‖ := by
        apply Finset.sum_le_sum
        intro v _
        rw [norm_mul, Real.norm_eq_abs (g x v)]
        exact mul_le_mul (hgbound x v) (norm_le_pi_norm y v) (norm_nonneg _) hC
      _ = _ := by simp [Finset.sum_const, nsmul_eq_mul, mul_assoc]
  have hsInt : Integrable signal μ := Integrable.of_eval fun v =>
    Integrable.of_bound ((measurable_pi_apply v).comp hsignal).aestronglyMeasurable 1
      (Filter.Eventually.of_forall fun ω => by simpa only [Real.norm_eq_abs] using hspin ω v)
  have hnInt : Integrable noise μ :=
    ⟨hnoise.aestronglyMeasurable, (Integrable.of_eval hnoiseInt).hasFiniteIntegral⟩
  have hd := (hasDerivAt_integral_sqrt_observation_vector hsInt hnInt hdf hDcont
    hfbound (mul_nonneg (by positivity) hC) hDbound ht).2
  simpa only [gaussianObservationCurve, gaussianObservationVelocity, D, sum_apply,
    smul_apply, ContinuousLinearMap.proj_apply, smul_eq_mul] using hd

end Expectation

section Posterior

variable {S : Type*} [Fintype S] [Nonempty S]

theorem continuous_fieldCovariance (energy : S → ℝ) (spin : S → V → ℝ)
    (observable : S → ℝ) (v : V) :
    Continuous (fun x => fieldCovariance energy spin observable x v) := by
  exact (continuous_fieldMean energy spin (fun s => observable s * spin s v)).sub
    ((continuous_fieldMean energy spin observable).mul
      (continuous_fieldMean energy spin (fun s => spin s v)))

theorem hasFDerivAt_fieldMean_square (energy : S → ℝ) (spin : S → V → ℝ)
    (observable : S → ℝ) (x : V → ℝ) :
    HasFDerivAt (fun y => fieldMean energy spin observable y ^ 2)
      (∑ v, (2 * fieldMean energy spin observable x * fieldCovariance energy spin observable x v) •
        (ContinuousLinearMap.proj v : (V → ℝ) →L[ℝ] ℝ)) x := by
  have hs : HasDerivAt (fun z : ℝ => z ^ 2)
      (2 * fieldMean energy spin observable x) (fieldMean energy spin observable x) := by
    have hd := (hasDerivAt_id (fieldMean energy spin observable x)).pow 2
    change HasDerivAt (fun z : ℝ => z ^ 2) _ (fieldMean energy spin observable x) at hd
    simpa only [Nat.cast_ofNat, Nat.reduceSub, pow_one, mul_one, id_eq] using hd
  have hd := hs.comp_hasFDerivAt x (hasFDerivAt_fieldMean energy spin observable x)
  simpa only [Function.comp_def, fieldMeanDerivative, Finset.smul_sum, smul_smul] using hd

variable {Ω : Type*} [MeasurableSpace Ω]

theorem hasDerivAt_integral_fieldMean_square_observation
    (μ : Measure Ω) [IsFiniteMeasure μ]
    (energy : S → ℝ) (spin : S → V → ℝ) (observable : S → ℝ)
    (A : ℝ) (hbound : ∀ s, |observable s| ≤ A)
    (hcoords : ∀ s v, spin s v = -1 ∨ spin s v = 1)
    (signal noise : Ω → V → ℝ)
    (hsignal : Measurable signal) (hnoise : Measurable noise)
    (hspin : ∀ ω v, |signal ω v| ≤ 1)
    (hnoiseInt : ∀ v, Integrable (fun ω => noise ω v) μ)
    {t : ℝ} (ht : 0 < t) :
    HasDerivAt (fun r => ∫ ω, fieldMean energy spin observable
        (gaussianObservationCurve (signal ω) (noise ω) r) ^ 2 ∂μ)
      (∫ ω, ∑ v, (2 * fieldMean energy spin observable
        (gaussianObservationCurve (signal ω) (noise ω) t) *
        fieldCovariance energy spin observable (gaussianObservationCurve (signal ω) (noise ω) t) v) *
          gaussianObservationVelocity (signal ω) (noise ω) t v ∂μ) t := by
  have hA : 0 ≤ A := (abs_nonneg (observable (Classical.arbitrary S))).trans
    (hbound (Classical.arbitrary S))
  apply hasDerivAt_integral_gaussianObservationCurve μ
    (fun x => fieldMean energy spin observable x ^ 2)
    (fun x v => 2 * fieldMean energy spin observable x * fieldCovariance energy spin observable x v)
    (hasFDerivAt_fieldMean_square energy spin observable)
    (fun v => ((continuous_fieldMean energy spin observable).const_mul 2).mul
      (continuous_fieldCovariance energy spin observable v))
    (A ^ 2) (4 * A ^ 2) (by positivity)
    (fun x => abs_fieldMean_square_le energy spin observable x A hbound) ?_
    signal noise hsignal hnoise hspin hnoiseInt ht
  intro x v
  rw [abs_mul, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
  have hm := abs_fieldMean_le energy spin observable x A hbound
  have hc := abs_fieldCovariance_le energy spin observable x v A (fun s => hcoords s v) hbound
  calc
    2 * |fieldMean energy spin observable x| * |fieldCovariance energy spin observable x v| ≤
      2 * A * (2 * A) := by gcongr
    _ = 4 * A ^ 2 := by ring

end Posterior

end Problem367.FinitePosterior

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Posterior_GaussianGradient
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Problem367.FinitePosterior

variable {S V : Type*} [Fintype S] [Nonempty S] [Fintype V]

theorem continuous_fieldSquareGradient (energy : S → ℝ) (spin : S → V → ℝ)
    (observable : S → ℝ) (v : V) :
    Continuous (fun x => fieldSquareGradient energy spin observable x v) :=
  ((continuous_fieldMean energy spin observable).const_mul 2).mul
    (continuous_fieldCovariance energy spin observable v)

theorem continuous_fieldSquareHessianDiagonal (energy : S → ℝ) (spin : S → V → ℝ)
    (observable : S → ℝ) (v : V) :
    Continuous (fun x => fieldSquareHessianDiagonal energy spin observable x v) := by
  exact (((continuous_fieldCovariance energy spin observable v).pow 2).const_mul 2).sub
    ((((continuous_fieldMean energy spin observable).const_mul 4).mul
      (continuous_fieldMean energy spin (fun s => spin s v))).mul
        (continuous_fieldCovariance energy spin observable v))

theorem abs_fieldSquareGradient_le (energy : S → ℝ) (spin : S → V → ℝ)
    (observable : S → ℝ) (x : V → ℝ) (v : V) (A : ℝ)
    (hcoord : ∀ s, spin s v = -1 ∨ spin s v = 1)
    (hbound : ∀ s, |observable s| ≤ A) :
    |fieldSquareGradient energy spin observable x v| ≤ 4 * A ^ 2 := by
  have hm := abs_fieldMean_le energy spin observable x A hbound
  have hc := abs_fieldCovariance_le energy spin observable x v A hcoord hbound
  have hA : 0 ≤ A := (abs_nonneg _).trans hm
  unfold fieldSquareGradient
  rw [abs_mul, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
  calc
    2 * |fieldMean energy spin observable x| * |fieldCovariance energy spin observable x v| ≤
      2 * A * (2 * A) := by gcongr
    _ = 4 * A ^ 2 := by ring

variable [DecidableEq V]

omit [Nonempty S] in
lemma fieldCovariance_coordinate_tilt (energy : S → ℝ) (spin : S → V → ℝ)
    (observable : S → ℝ) (x : V → ℝ) (v : V) (t : ℝ) :
    fieldCovariance energy spin observable (fun u => x u + if u = v then t else 0) v =
      tiltCovariance (fieldEnergy energy spin x) (fun s => spin s v) observable t := by
  simp only [fieldCovariance, fieldMean_coordinate_tilt, tiltCovariance]

theorem hasDerivAt_fieldSquareGradient_coordinate (energy : S → ℝ) (spin : S → V → ℝ)
    (observable : S → ℝ) (x : V → ℝ) (v : V) (t : ℝ)
    (hcoord : ∀ s, spin s v = -1 ∨ spin s v = 1) :
    HasDerivAt (fun r => fieldSquareGradient energy spin observable
        (fun u => x u + if u = v then r else 0) v)
      (fieldSquareHessianDiagonal energy spin observable
        (fun u => x u + if u = v then t else 0) v) t := by
  have hd := ((hasDerivAt_mean_covariance (fieldEnergy energy spin x)
    (fun s => spin s v) observable t).const_mul 2).mul
      (hasDerivAt_tiltCovariance (fieldEnergy energy spin x) (fun s => spin s v)
        observable t hcoord)
  simp only [fieldSquareGradient, fieldSquareHessianDiagonal,
    fieldMean_coordinate_tilt, fieldCovariance_coordinate_tilt]
  change HasDerivAt (fun r => 2 * mean (fieldEnergy energy spin x)
    (fun s => spin s v) observable r *
      tiltCovariance (fieldEnergy energy spin x) (fun s => spin s v) observable r) _ t at hd
  apply hd.congr_deriv
  ring

theorem abs_fieldSquareHessianDiagonal_le (energy : S → ℝ) (spin : S → V → ℝ)
    (observable : S → ℝ) (x : V → ℝ) (v : V) (A : ℝ)
    (hcoord : ∀ s, spin s v = -1 ∨ spin s v = 1)
    (hbound : ∀ s, |observable s| ≤ A) :
    |fieldSquareHessianDiagonal energy spin observable x v| ≤ 16 * A ^ 2 := by
  have hd := (hasDerivAt_fieldSquareGradient_coordinate energy spin observable x v 0 hcoord).deriv
  have hfirst : (fun r => fieldSquareGradient energy spin observable
      (fun u => x u + if u = v then r else 0) v) =
      deriv (fun r => fieldMean energy spin observable
        (fun u => x u + if u = v then r else 0) ^ 2) := by
    funext r
    simp only [fieldSquareGradient, fieldMean_coordinate_tilt, fieldCovariance_coordinate_tilt]
    exact (deriv_mean_square _ _ _ _).symm
  rw [hfirst] at hd
  simp only [ite_self, add_zero] at hd
  rw [← hd]
  exact abs_deriv_deriv_fieldMean_square_coordinate_le energy spin observable x v 0 A hcoord hbound

omit [Fintype V] in
lemma update_eq_zero_shift (x : V → ℝ) (v : V) (t : ℝ) :
    Function.update x v t =
      (fun u => Function.update x v 0 u + if u = v then t else 0) := by
  funext u
  by_cases hu : u = v
  · subst u
    simp
  · simp [hu]

theorem hasDerivAt_fieldSquareGradient_update (energy : S → ℝ) (spin : S → V → ℝ)
    (observable : S → ℝ) (x : V → ℝ) (v : V) (t : ℝ)
    (hcoord : ∀ s, spin s v = -1 ∨ spin s v = 1) :
    HasDerivAt (fun r => fieldSquareGradient energy spin observable (Function.update x v r) v)
      (fieldSquareHessianDiagonal energy spin observable (Function.update x v t) v) t := by
  simpa only [← update_eq_zero_shift] using
    hasDerivAt_fieldSquareGradient_coordinate energy spin observable (Function.update x v 0) v t hcoord

end Problem367.FinitePosterior

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Posterior_GaussianEnergy
attribute [-instance] _root_.OAI.Problem367.WienerSampler.pathMeasurableSpace _root_.OAI.Problem367.reducedTailFinite _root_.OAI.Problem367.treeBallFinite _root_.OAI.Problem367.treeShellFinite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace Problem367.FinitePosterior

variable {S V : Type*} [Fintype S] [Nonempty S] [Fintype V] [DecidableEq V]

theorem integral_fieldSquareGradient_mul_noise
    (energy : S → ℝ) (spin : S → V → ℝ) (observable : S → ℝ)
    (A : ℝ) (hbound : ∀ s, |observable s| ≤ A)
    (hcoords : ∀ s v, spin s v = -1 ∨ spin s v = 1)
    (signal : V → ℝ) (t : ℝ) (v : V) :
    (∫ z, fieldSquareGradient energy spin observable
      (gaussianObservationCurve signal z t) v * z v
      ∂Measure.pi (fun _ : V => gaussianReal 0 1)) =
    Real.sqrt t * ∫ z, fieldSquareHessianDiagonal energy spin observable
      (gaussianObservationCurve signal z t) v
      ∂Measure.pi (fun _ : V => gaussianReal 0 1) := by
  have h := Problem367.gaussian_pi_integral_mul_affine_of_bounded_deriv
    (fun j => t * signal j) (fun _ => Real.sqrt t) v
    (continuous_fieldSquareGradient energy spin observable v)
    (continuous_fieldSquareHessianDiagonal energy spin observable v)
    (fun z r => hasDerivAt_fieldSquareGradient_update energy spin observable z v r
      (fun s => hcoords s v))
    (fun z => abs_fieldSquareGradient_le energy spin observable z v A
      (fun s => hcoords s v) hbound)
    (fun z => abs_fieldSquareHessianDiagonal_le energy spin observable z v A
      (fun s => hcoords s v) hbound)
  simpa only [gaussianObservationCurve, Pi.add_def, Pi.smul_def, smul_eq_mul,
    mul_comm] using h

section Planted

variable [MeasurableSpace S] [MeasurableSingletonClass S]

omit [Nonempty S] [Fintype V] [DecidableEq V] in
lemma measurable_finiteStandardObservation (spin : S → V → ℝ) (t : ℝ) :
    Measurable (finiteStandardObservation spin t) := by
  unfold finiteStandardObservation gaussianObservationCurve
  exact ((measurable_of_finite spin).comp measurable_fst).const_smul t |>.add
    (measurable_snd.const_smul (Real.sqrt t))

omit [DecidableEq V] in
private theorem integrable_bounded_test
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsFiniteMeasure μ]
    (X : Ω → V → ℝ) (hX : Measurable X) (f : (V → ℝ) → ℝ)
    (hf : Continuous f) (C : ℝ) (hbound : ∀ z, |f z| ≤ C) :
    Integrable (fun x => f (X x)) μ := by
  apply Integrable.of_bound (hf.measurable.comp hX).aestronglyMeasurable C
  exact Filter.Eventually.of_forall fun x => by
    simpa only [Real.norm_eq_abs, Function.comp_def] using hbound (X x)

omit [Fintype S] [Nonempty S] [DecidableEq V] [MeasurableSingletonClass S] in

theorem integrable_finiteStandardNoise (μ : Measure S) [IsFiniteMeasure μ] (v : V) :
    Integrable (fun x : S × (V → ℝ) => x.2 v)
      (μ.prod (Measure.pi (fun _ : V => gaussianReal 0 1))) := by
  have h := (measurePreserving_eval (fun _ : V => gaussianReal 0 1) v).integrable_comp_of_integrable ((memLp_id_gaussianReal 1).integrable (by norm_num))
  exact h.comp_snd μ

omit [DecidableEq V] in
theorem integrable_finiteStandardGradient (μ : Measure S) [IsFiniteMeasure μ]
    (energy : S → ℝ) (spin : S → V → ℝ) (observable : S → ℝ)
    (A : ℝ) (hbound : ∀ s, |observable s| ≤ A)
    (hcoords : ∀ s v, spin s v = -1 ∨ spin s v = 1) (t : ℝ) (v : V) :
    Integrable (fun x => fieldSquareGradient energy spin observable
      (finiteStandardObservation spin t x) v)
      (μ.prod (Measure.pi (fun _ : V => gaussianReal 0 1))) :=
  integrable_bounded_test _ _ (measurable_finiteStandardObservation spin t) _
    (continuous_fieldSquareGradient energy spin observable v) (4 * A ^ 2)
    (fun z => abs_fieldSquareGradient_le energy spin observable z v A
      (fun s => hcoords s v) hbound)

theorem integrable_finiteStandardHessian (μ : Measure S) [IsFiniteMeasure μ]
    (energy : S → ℝ) (spin : S → V → ℝ) (observable : S → ℝ)
    (A : ℝ) (hbound : ∀ s, |observable s| ≤ A)
    (hcoords : ∀ s v, spin s v = -1 ∨ spin s v = 1) (t : ℝ) (v : V) :
    Integrable (fun x => fieldSquareHessianDiagonal energy spin observable
      (finiteStandardObservation spin t x) v)
      (μ.prod (Measure.pi (fun _ : V => gaussianReal 0 1))) :=
  integrable_bounded_test _ _ (measurable_finiteStandardObservation spin t) _
    (continuous_fieldSquareHessianDiagonal energy spin observable v) (16 * A ^ 2)
    (fun z => abs_fieldSquareHessianDiagonal_le energy spin observable z v A
      (fun s => hcoords s v) hbound)

omit [DecidableEq V] in
theorem integrable_finiteStandardGradient_mul_noise
    (μ : Measure S) [IsFiniteMeasure μ]
    (energy : S → ℝ) (spin : S → V → ℝ) (observable : S → ℝ)
    (A : ℝ) (hbound : ∀ s, |observable s| ≤ A)
    (hcoords : ∀ s v, spin s v = -1 ∨ spin s v = 1) (t : ℝ) (v : V) :
    Integrable (fun x => fieldSquareGradient energy spin observable
      (finiteStandardObservation spin t x) v * x.2 v)
      (μ.prod (Measure.pi (fun _ : V => gaussianReal 0 1))) := by
  have hg := integrable_finiteStandardGradient μ energy spin observable A hbound hcoords t v
  have h := (integrable_finiteStandardNoise μ v).mul_bdd hg.aestronglyMeasurable
    (Filter.Eventually.of_forall fun x => by
      simpa only [Real.norm_eq_abs, Function.comp_def] using abs_fieldSquareGradient_le energy spin observable
        (finiteStandardObservation spin t x) v A (fun s => hcoords s v) hbound)
  simpa only [mul_comm] using h

theorem integral_finiteStandardGradient_mul_noise
    (μ : Measure S) [IsFiniteMeasure μ]
    (energy : S → ℝ) (spin : S → V → ℝ) (observable : S → ℝ)
    (A : ℝ) (hbound : ∀ s, |observable s| ≤ A)
    (hcoords : ∀ s v, spin s v = -1 ∨ spin s v = 1) (t : ℝ) (v : V) :
    (∫ x, fieldSquareGradient energy spin observable
      (finiteStandardObservation spin t x) v * x.2 v
      ∂μ.prod (Measure.pi (fun _ : V => gaussianReal 0 1))) =
    Real.sqrt t * ∫ x, fieldSquareHessianDiagonal energy spin observable
      (finiteStandardObservation spin t x) v
      ∂μ.prod (Measure.pi (fun _ : V => gaussianReal 0 1)) := by
  rw [integral_prod _ (integrable_finiteStandardGradient_mul_noise
    μ energy spin observable A hbound hcoords t v),
    integral_prod _ (integrable_finiteStandardHessian
    μ energy spin observable A hbound hcoords t v), ← integral_const_mul]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun s =>
    integral_fieldSquareGradient_mul_noise energy spin observable A hbound hcoords (spin s) t v

theorem hasDerivAt_finiteStandardEnergy_of_posterior_test
    (μ : Measure S) [IsProbabilityMeasure μ]
    (energy : S → ℝ) (spin : S → V → ℝ) (observable : S → ℝ)
    (A : ℝ) (hbound : ∀ s, |observable s| ≤ A)
    (hcoords : ∀ s v, spin s v = -1 ∨ spin s v = 1)
    {t : ℝ} (ht : 0 < t)
    (hposterior : ∀ v,
      (∫ x, fieldSquareGradient energy spin observable
        (finiteStandardObservation spin t x) v * spin x.1 v
        ∂μ.prod (Measure.pi (fun _ : V => gaussianReal 0 1))) =
      ∫ x, fieldSquareGradient energy spin observable
        (finiteStandardObservation spin t x) v *
          fieldMean energy spin (fun s => spin s v) (finiteStandardObservation spin t x)
        ∂μ.prod (Measure.pi (fun _ : V => gaussianReal 0 1))) :
    HasDerivAt
      (fun r => ∫ x, fieldMean energy spin observable (finiteStandardObservation spin r x) ^ 2
        ∂μ.prod (Measure.pi (fun _ : V => gaussianReal 0 1)))
      (∫ x, ∑ v, fieldCovariance energy spin observable
        (finiteStandardObservation spin t x) v ^ 2
        ∂μ.prod (Measure.pi (fun _ : V => gaussianReal 0 1))) t := by
  let ρ := μ.prod (Measure.pi (fun _ : V => gaussianReal 0 1))
  let Y := finiteStandardObservation spin t
  let g := fun x v => fieldSquareGradient energy spin observable (Y x) v
  let H := fun x v => fieldSquareHessianDiagonal energy spin observable (Y x) v
  let p := fun x v => fieldMean energy spin (fun s => spin s v) (Y x)
  let c := 1 / (2 * Real.sqrt t)
  have hy : Measurable Y := measurable_finiteStandardObservation spin t
  have hg (v : V) : Integrable (fun x => g x v) ρ :=
    integrable_finiteStandardGradient μ energy spin observable A hbound hcoords t v
  have hH (v : V) : Integrable (fun x => H x v) ρ :=
    integrable_finiteStandardHessian μ energy spin observable A hbound hcoords t v
  have hn (v : V) : Integrable (fun x => g x v * x.2 v) ρ :=
    integrable_finiteStandardGradient_mul_noise μ energy spin observable A hbound hcoords t v
  have hs (v : V) : Integrable (fun x => g x v * spin x.1 v) ρ := by
    apply (hg v).mul_bdd
      (((measurable_of_finite (fun s => spin s v)).comp measurable_fst).aestronglyMeasurable)
    exact Filter.Eventually.of_forall fun x => by
      simpa only [Real.norm_eq_abs, Function.comp_def] using
        (abs_spin_eq_one (fun s => spin s v) (fun s => hcoords s v) x.1).le
  have hp (v : V) : Integrable (fun x => g x v * p x v) ρ := by
    apply (hg v).mul_bdd
      (((continuous_fieldMean energy spin (fun s => spin s v)).measurable.comp hy).aestronglyMeasurable)
    exact Filter.Eventually.of_forall fun x => by
      simpa only [Real.norm_eq_abs, Function.comp_def] using abs_fieldMean_le energy spin (fun s => spin s v)
        (Y x) 1 (fun s => (abs_spin_eq_one (fun s => spin s v) (fun s => hcoords s v) s).le)
  have hvEq (v : V) :
      (fun x : S × (V → ℝ) => g x v * gaussianObservationVelocity (spin x.1) x.2 t v) =
        (fun x => g x v * spin x.1 v + c * (g x v * x.2 v)) := by
    funext x
    change g x v * (spin x.1 v + c * x.2 v) = _
    ring
  have hv (v : V) : Integrable
      (fun x => g x v * gaussianObservationVelocity (spin x.1) x.2 t v) ρ := by
    rw [hvEq]
    exact (hs v).add ((hn v).const_mul c)
  have hcancel (x : S × (V → ℝ)) (v : V) :
      g x v * p x v + (1 / 2 : ℝ) * H x v =
        fieldCovariance energy spin observable (Y x) v ^ 2 := by
    dsimp [g, H, p, fieldSquareGradient, fieldSquareHessianDiagonal]
    ring
  have hc (v : V) : Integrable
      (fun x => fieldCovariance energy spin observable (Y x) v ^ 2) ρ := by
    exact ((hp v).add ((hH v).const_mul (1 / 2 : ℝ))).congr
      (Filter.Eventually.of_forall fun x => hcancel x v)
  have hstep (v : V) :
      (∫ x, g x v * gaussianObservationVelocity (spin x.1) x.2 t v ∂ρ) =
        ∫ x, fieldCovariance energy spin observable (Y x) v ^ 2 ∂ρ := by
    rw [hvEq, integral_add (hs v) ((hn v).const_mul c), integral_const_mul]
    have hnoise : (∫ x, g x v * x.2 v ∂ρ) = Real.sqrt t * ∫ x, H x v ∂ρ :=
      integral_finiteStandardGradient_mul_noise μ energy spin observable A hbound hcoords t v
    rw [hnoise]
    have hcoef : c * Real.sqrt t = (1 / 2 : ℝ) := by
      dsimp [c]
      field_simp [ne_of_gt (Real.sqrt_pos.mpr ht)]
    rw [← mul_assoc, hcoef, hposterior v]
    rw [← integral_const_mul, ← integral_add (hp v) ((hH v).const_mul (1 / 2 : ℝ))]
    exact integral_congr_ae (Filter.Eventually.of_forall fun x => hcancel x v)
  have hd := hasDerivAt_integral_fieldMean_square_observation ρ energy spin observable A
    hbound hcoords (fun x : S × (V → ℝ) => spin x.1) Prod.snd
    ((measurable_of_finite spin).comp measurable_fst) measurable_snd
    (fun x v => (abs_spin_eq_one (fun s => spin s v) (fun s => hcoords s v) x.1).le)
    (fun v => integrable_finiteStandardNoise μ v) ht
  apply hd.congr_deriv
  change (∫ x, ∑ v, g x v * gaussianObservationVelocity (spin x.1) x.2 t v ∂ρ) = _
  rw [integral_finsetSum _ (fun v _ => hv v), integral_finsetSum _ (fun v _ => hc v)]
  exact Finset.sum_congr rfl fun v _ => hstep v

theorem hasDerivAt_finiteStandardEnergy [StandardBorelSpace S]
    (μ : Measure S) [IsProbabilityMeasure μ] (energy : S → ℝ)
    (hprior : ∀ s, μ.real {s} = Real.exp (energy s) / ∑ a, Real.exp (energy a))
    (spin : S → V → ℝ) (observable : S → ℝ)
    (A : ℝ) (hbound : ∀ s, |observable s| ≤ A)
    (hcoords : ∀ s v, spin s v = -1 ∨ spin s v = 1)
    {t : ℝ} (ht : 0 < t) :
    HasDerivAt
      (fun r => ∫ x, fieldMean energy spin observable (finiteStandardObservation spin r x) ^ 2
        ∂μ.prod (Measure.pi (fun _ : V => gaussianReal 0 1)))
      (∫ x, ∑ v, fieldCovariance energy spin observable
        (finiteStandardObservation spin t x) v ^ 2
        ∂μ.prod (Measure.pi (fun _ : V => gaussianReal 0 1))) t := by
  apply hasDerivAt_finiteStandardEnergy_of_posterior_test μ energy spin observable A hbound hcoords ht
  intro v
  have hsq : ∀ s i, spin s i ^ 2 = 1 := by
    intro s i
    rcases hcoords s i with h | h <;> simp [h]
  exact Problem367.finiteStandardGaussianPlanted_integral_test_fieldMean μ energy hprior t ht.le
    spin hsq (fun s => spin s v) (fun z => fieldSquareGradient energy spin observable z v)
    (continuous_fieldSquareGradient energy spin observable v).measurable (4 * A ^ 2)
    (fun z => by simpa only [Real.norm_eq_abs] using
      abs_fieldSquareGradient_le energy spin observable z v A (fun s => hcoords s v) hbound)

end Planted
end Problem367.FinitePosterior

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Posterior_GaussianEnergyIntegral
attribute [-instance] _root_.OAI.Problem367.WienerSampler.pathMeasurableSpace _root_.OAI.Problem367.reducedTailFinite _root_.OAI.Problem367.treeBallFinite _root_.OAI.Problem367.treeShellFinite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped NNReal

namespace Problem367.FinitePosterior

variable {S V : Type*} [Fintype S] [Nonempty S] [Fintype V] [DecidableEq V]
  [MeasurableSpace S] [MeasurableSingletonClass S] [StandardBorelSpace S]

theorem integral_finiteStandardEnergy
    (μ : Measure S) [IsProbabilityMeasure μ]
    (energy : S → ℝ)
    (hprior : ∀ s, μ.real {s} = Real.exp (energy s) / ∑ a, Real.exp (energy a))
    (spin : S → V → ℝ) (observable : S → ℝ)
    (A : ℝ) (hbound : ∀ s, |observable s| ≤ A)
    (hcoords : ∀ s v, spin s v = -1 ∨ spin s v = 1)
    {T : ℝ} (hT : 0 ≤ T) :
    let C : ℝ → ℝ := fun t => ∫ x, ∑ v, fieldCovariance energy spin observable
      (finiteStandardObservation spin t x) v ^ 2
      ∂μ.prod (Measure.pi (fun _ : V => gaussianReal 0 1))
    IntervalIntegrable C volume 0 T ∧
      (∫ t in 0..T, C t) =
        (∫ x, fieldMean energy spin observable (finiteStandardObservation spin T x) ^ 2
          ∂μ.prod (Measure.pi (fun _ : V => gaussianReal 0 1))) -
        fieldMean energy spin observable 0 ^ 2 ∧
      0 ≤ (∫ t in 0..T, C t) ∧ (∫ t in 0..T, C t) ≤ A ^ 2 := by
  let ρ := μ.prod (Measure.pi (fun _ : V => gaussianReal 0 1))
  let E : ℝ → ℝ := fun t => ∫ x,
    fieldMean energy spin observable (finiteStandardObservation spin t x) ^ 2 ∂ρ
  let C : ℝ → ℝ := fun t => ∫ x, ∑ v, fieldCovariance energy spin observable
    (finiteStandardObservation spin t x) v ^ 2 ∂ρ
  have hE : Continuous E := by
    simpa only [E, finiteStandardObservation, gaussianObservationCurve, Pi.pow_apply, Function.comp_def] using
      (continuous_integral_sqrt_observation (P := ρ)
        (((measurable_of_finite spin).comp measurable_fst).aestronglyMeasurable)
        (measurable_snd.aestronglyMeasurable)
        ((continuous_fieldMean energy spin observable).pow 2)
        (fun x => abs_fieldMean_square_le energy spin observable x A hbound))
  have hd (t : ℝ) (ht : 0 < t) : HasDerivAt E (C t) t :=
    hasDerivAt_finiteStandardEnergy μ energy hprior spin observable A
      hbound hcoords ht
  have hCpos (t : ℝ) : 0 ≤ C t :=
    integral_nonneg fun x => Finset.sum_nonneg fun v _ => sq_nonneg _
  have hCI : IntervalIntegrable C volume 0 T := by
    apply intervalIntegral.intervalIntegrable_deriv_of_nonneg hE.continuousOn
    · intro t ht
      exact hd t (by simpa only [min_eq_left hT, max_eq_right hT] using ht.1)
    · exact fun t _ => hCpos t
  have hFTC : (∫ t in 0..T, C t) = E T - E 0 :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hT hE.continuousOn
      (fun t ht => hd t ht.1) hCI
  have hzero : E 0 = fieldMean energy spin observable 0 ^ 2 := by
    simp [E, finiteStandardObservation, gaussianObservationCurve, ρ]
  have hm : AEStronglyMeasurable
      (fun x => fieldMean energy spin observable (finiteStandardObservation spin T x) ^ 2) ρ :=
    (((continuous_fieldMean energy spin observable).pow 2).measurable.comp
      (measurable_finiteStandardObservation spin T)).aestronglyMeasurable
  have hb (x : S × (V → ℝ)) :
      |fieldMean energy spin observable (finiteStandardObservation spin T x) ^ 2| ≤ A ^ 2 :=
    abs_fieldMean_square_le energy spin observable _ A hbound
  have hInt : Integrable
      (fun x => fieldMean energy spin observable (finiteStandardObservation spin T x) ^ 2) ρ :=
    Integrable.of_bound hm (A ^ 2) (Filter.Eventually.of_forall fun x => by
      simpa only [Real.norm_eq_abs] using hb x)
  have hEbound : E T ≤ A ^ 2 := by
    calc
      E T ≤ ∫ _x, A ^ 2 ∂ρ := integral_mono hInt (integrable_const _) fun x =>
        (le_abs_self _).trans (hb x)
      _ = A ^ 2 := by simp [ρ]
  refine ⟨hCI, ?_, intervalIntegral.integral_nonneg_of_forall hT hCpos, ?_⟩
  · simpa only [hzero] using hFTC
  · rw [hFTC, hzero]
    exact sub_le_self _ (sq_nonneg _) |>.trans hEbound

end Problem367.FinitePosterior

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Stochastic_FiniteIsingBrownianEnergy
attribute [-instance] _root_.OAI.Problem367.IsingConditionalCopyBounds.graphLaw_isProbabilityMeasure _root_.OAI.Problem367.IsingObservationFactor.copies_probability _root_.OAI.Problem367.IsingObservationFactor.kernel_markov _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_observationLaw_probability _root_.OAI.Problem367.IsingObservationInnovation.observationLaw_probability _root_.OAI.Problem367.TreeKoopman.labelProbability _root_.OAI.Problem367.WienerSampler.pathMeasurableSpace _root_.OAI.Problem367.freeIsingMeasure_probability _root_.OAI.Problem367.reducedTailFinite _root_.OAI.Problem367.reducedTailFintype _root_.OAI.Problem367.treeBallFinite _root_.OAI.Problem367.treeBallFintype _root_.OAI.Problem367.treeShellFinite _root_.OAI.Problem367.treeShellFintype
attribute [-simp] _root_.OAI.Problem367.ConnectedHull.pathAssignment_path _root_.OAI.Problem367.ConnectedHull.path_last _root_.OAI.Problem367.ConnectedHull.path_zero _root_.OAI.Problem367.ConnectedHull.prefix_length _root_.OAI.Problem367.ConnectedHull.prefix_zero _root_.OAI.Problem367.CutContinuationChannels.averageChannel_globalCone _root_.OAI.Problem367.CutContinuationChannels.continuationChannel_globalCone _root_.OAI.Problem367.FactorObservable.centeredSpinLp_coe _root_.OAI.Problem367.FiniteIsingSplit.splitEquiv_fst _root_.OAI.Problem367.FiniteIsingSplit.splitEquiv_snd _root_.OAI.Problem367.FinitePathGibbs.tailPartition_zero _root_.OAI.Problem367.GaussianTreeResponseNaturality.fieldEquiv_apply_image _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_apply _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_uniformObservation _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_zero _root_.OAI.Problem367.IsingObservationInnovation.uniformObservation_relabel _root_.OAI.Problem367.IsingOrientedPath.attenuation_outward _root_.OAI.Problem367.IsingOrientedPath.endpoint_extensionAt _root_.OAI.Problem367.LocalSupportGeometry.prefixVertex_length _root_.OAI.Problem367.PathSideBranches.parent_sideVertex _root_.OAI.Problem367.PathSideBranches.restrictNoisyRegion_array _root_.OAI.Problem367.PathSideBranches.sideVertex_length _root_.OAI.Problem367.PathSideBranches.sideVertex_val _root_.OAI.Problem367.PosteriorChain.transition_spinMean _root_.OAI.Problem367.PosteriorChain.transition_sum _root_.OAI.Problem367.RootedBroadcast.flipBranchToComplement_val _root_.OAI.Problem367.RootedBroadcast.pos_spinMul _root_.OAI.Problem367.RootedBroadcast.prefixFlip_branchRoot _root_.OAI.Problem367.RootedBroadcast.prefixFlip_root _root_.OAI.Problem367.RootedBroadcast.prefixTreeAut_symm_branchRoot _root_.OAI.Problem367.RootedBroadcast.prefixTreeAut_symm_root _root_.OAI.Problem367.RootedBroadcast.spinMul_pos _root_.OAI.Problem367.RootedBroadcast.spinMul_self _root_.OAI.Problem367.TreeConeCoding.length_vertex _root_.OAI.Problem367.TreeConeCoding.vertex_nil _root_.OAI.Problem367.TreeConeCoding.vertex_val _root_.OAI.Problem367.TreeGibbsAut.spinEquiv_apply_image _root_.OAI.Problem367.TreeKoopman.centeredAverage_apply_coe _root_.OAI.Problem367.TreeKoopman.centeredAverage_pow_apply_coe _root_.OAI.Problem367.TreeKoopman.centeredGenerator_apply_coe _root_.OAI.Problem367.TreeKoopman.centeredGenerator_sq _root_.OAI.Problem367.TreeKoopman.generatorOperator_sq _root_.OAI.Problem367.TreeKoopman.reverseVertex_twice _root_.OAI.Problem367.TreeKoopman.wordRelabel_cons _root_.OAI.Problem367.TreeKoopman.wordRelabel_nil _root_.OAI.Problem367.TreeLawKoopman.centeredAverage_apply_coe _root_.OAI.Problem367.TreeLawKoopman.generatorOperator_sq _root_.OAI.Problem367.TreePathGibbs.vertexEquiv_val _root_.OAI.Problem367.branchColorAut_length _root_.OAI.Problem367.branchColorAut_singleton _root_.OAI.Problem367.branchColorAut_val _root_.OAI.Problem367.branchColorMap_symm_apply _root_.OAI.Problem367.card_treeBallFinset _root_.OAI.Problem367.card_treeNeighborFinset _root_.OAI.Problem367.colorPermAut_length _root_.OAI.Problem367.colorPermAut_nil _root_.OAI.Problem367.colorPermAut_val _root_.OAI.Problem367.colorPermMap_symm_apply _root_.OAI.Problem367.colorPermMap_val _root_.OAI.Problem367.connectedSpinEncode_apply_root _root_.OAI.Problem367.connectedSpinEquiv_apply _root_.OAI.Problem367.dropVertex_length _root_.OAI.Problem367.dropVertex_val _root_.OAI.Problem367.iUnion_treeBallFinset _root_.OAI.Problem367.mem_rootComplementFinset _root_.OAI.Problem367.mem_rootComponentFinset _root_.OAI.Problem367.mem_rootComponentIndices _root_.OAI.Problem367.mem_treeBallFinset _root_.OAI.Problem367.mem_treeNeighborFinset _root_.OAI.Problem367.parentVertex_length _root_.OAI.Problem367.parentVertex_val _root_.OAI.Problem367.prefixColorAut_length _root_.OAI.Problem367.prefixColorAut_val _root_.OAI.Problem367.prefixColorMap_symm_apply _root_.OAI.Problem367.prefixFlip_twice _root_.OAI.Problem367.spinAgreementCode_eq_neg_iff _root_.OAI.Problem367.spinAgreementCode_eq_pos_iff _root_.OAI.Problem367.spinSign_flip _root_.OAI.Problem367.sum_treeShell_zero _root_.OAI.Problem367.tsum_treeShell_radial _root_.OAI.Problem367.vertexSampler_relabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal

namespace Problem367

local instance finiteIsingBrownianEnergyNonemptySpin : Nonempty IsingSpin := ⟨.neg⟩

theorem finiteBrownianNoise_restrict_measurePreserving
    {ι Ω : Type*} [MeasurableSpace Ω]
    (ν : ι → Measure Ω) {B : ι → ℝ≥0 → Ω → ℝ}
    (hB : ∀ i, IsPreBrownianReal (B i) (ν i))
    (hmB : ∀ i t, Measurable (B i t)) (D : Finset ι) (t : ℝ≥0) :
    MeasurePreserving (fun ω (v : D) => B v t (ω v))
      (Measure.infinitePi ν) (Measure.pi (fun _ : D => gaussianReal 0 t)) := by
  have (i : ι) : IsProbabilityMeasure (ν i) :=
    (hB i).isGaussianProcess.isProbabilityMeasure
  have hr : MeasurePreserving (D.restrict : (ι → Ω) → D → Ω)
      (Measure.infinitePi ν) (Measure.pi fun v : D => ν v) :=
    ⟨D.measurable_restrict, Measure.infinitePi_map_restrict ν⟩
  have he : MeasurePreserving (fun ω (v : D) => B v t (ω v))
      (Measure.pi fun v : D => ν v) (Measure.pi fun _ : D => gaussianReal 0 t) := by
    refine ⟨Measurable.of_eval (fun vertex => (hmB vertex t).comp
      (measurable_pi_apply vertex)), ?_⟩
    rw [Measure.pi_map_pi (μ := fun v : D => ν v)
      (f := fun v ω => B v t ω) (fun v => (hmB v t).aemeasurable)]
    congr 1
    funext v
    exact (hB v).hasLaw_eval t |>.map_eq
  exact he.comp hr

theorem integral_finiteIsingBrownian_observation_eq_standard
    {d : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure (TreeVertex d → IsingSpin)) [IsProbabilityMeasure μ]
    (ν : TreeVertex d → Measure Ω)
    {B : TreeVertex d → ℝ≥0 → Ω → ℝ}
    (hB : ∀ i, IsPreBrownianReal (B i) (ν i))
    (hmB : ∀ i t, Measurable (B i t))
    (D : Finset (TreeVertex d)) (t : ℝ≥0)
    (f : (D → ℝ) → ℝ) (hf : Measurable f) :
    (∫ p : (TreeVertex d → IsingSpin) × (TreeVertex d → Ω),
      f (fun v : D => (t : ℝ) * spinSign (p.1 v) + B v t (p.2 v))
      ∂μ.prod (Measure.infinitePi ν)) =
    ∫ p : (D → IsingSpin) × (D → ℝ),
      f (FinitePosterior.finiteStandardObservation
        (fun eta v => spinSign (eta v)) t p)
      ∂(μ.map D.restrict).prod (Measure.pi fun _ : D => gaussianReal 0 1) := by
  have (i : TreeVertex d) : IsProbabilityMeasure (ν i) :=
    (hB i).isGaussianProcess.isProbabilityMeasure
  let π := μ.map D.restrict
  let : IsProbabilityMeasure π := by first | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)
  let Y : (D → IsingSpin) × (D → ℝ) → D → ℝ :=
    fun p v => (t : ℝ) * spinSign (p.1 v) + p.2 v
  have hY : Measurable Y := by
    apply Measurable.of_eval
    intro v
    exact (measurable_const.mul
      ((measurable_of_finite (fun eta : D → IsingSpin => spinSign (eta v))).comp
        measurable_fst)).add ((measurable_pi_apply v).comp measurable_snd)
  have hr : MeasurePreserving D.restrict μ π := ⟨D.measurable_restrict, rfl⟩
  have hp := hr.prod (finiteBrownianNoise_restrict_measurePreserving ν hB hmB D t)
  have hs : MeasurePreserving (fun z : D → ℝ => fun v => Real.sqrt (t : ℝ) * z v)
      (Measure.pi fun _ : D => gaussianReal 0 1)
      (Measure.pi fun _ : D => gaussianReal 0 t) := by
    refine ⟨by fun_prop, ?_⟩
    exact gaussianPi_map_sqrt (t : ℝ) t.property
  have hps := (MeasurePreserving.id π).prod hs
  have hleft := integral_map (μ := μ.prod (Measure.infinitePi ν)) hp.measurable.aemeasurable
    (hf.comp hY).aestronglyMeasurable
  have hright := integral_map (μ := π.prod (Measure.pi fun _ : D => gaussianReal 0 1))
    hps.measurable.aemeasurable
    (hf.comp hY).aestronglyMeasurable
  rw [hp.map_eq] at hleft
  rw [hps.map_eq] at hright
  exact hleft.symm.trans hright

theorem HasFreeIsingLaw.integral_finiteIsingBrownianEnergy
    {d : ℕ} {beta : ℝ} {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure (TreeVertex d → IsingSpin)}
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ)
    (ν : TreeVertex d → Measure Ω)
    {B : TreeVertex d → ℝ≥0 → Ω → ℝ}
    (hB : ∀ i, IsPreBrownianReal (B i) (ν i))
    (hmB : ∀ i t, Measurable (B i t))
    (D : Finset (TreeVertex d)) (hD : ConnectedFinset D) (v : D)
    {T : ℝ} (hT : 0 ≤ T) :
    let ρ := μ.prod (Measure.infinitePi ν)
    let E : ℝ → ℝ := fun t => ∫ p,
      ∑ u : D, finiteIsingBrownianCovariance beta D v u B t p ^ 2 ∂ρ
    IntervalIntegrable E volume 0 T ∧
      (∫ t in 0..T, E t) =
        (∫ p, finiteIsingBrownianMean beta D v B T p ^ 2 ∂ρ) ∧
      0 ≤ (∫ t in 0..T, E t) ∧ (∫ t in 0..T, E t) ≤ 1 := by
  classical
  let : IsProbabilityMeasure μ := hμ.isProbabilityMeasure
  let π := μ.map D.restrict
  let : IsProbabilityMeasure π := by first | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)
  let spin : (D → IsingSpin) → D → ℝ := fun eta u => spinSign (eta u)
  let q : (D → IsingSpin) → ℝ := fun eta => spinSign (eta v)
  let F : (D → ℝ) → ℝ := FinitePosterior.fieldMean (finiteIsingEnergy beta D) spin q
  let C : (D → ℝ) → D → ℝ :=
    FinitePosterior.fieldCovariance (finiteIsingEnergy beta D) spin q
  let ρ := μ.prod (Measure.infinitePi ν)
  let ρG := π.prod (Measure.pi fun _ : D => gaussianReal 0 1)
  let EG : ℝ → ℝ := fun t => ∫ p,
    ∑ u : D, C (FinitePosterior.finiteStandardObservation spin t p) u ^ 2 ∂ρG
  let MG : ℝ → ℝ := fun t => ∫ p,
    F (FinitePosterior.finiteStandardObservation spin t p) ^ 2 ∂ρG
  let E : ℝ → ℝ := fun t => ∫ p,
    ∑ u : D, finiteIsingBrownianCovariance beta D v u B t p ^ 2 ∂ρ
  let M : ℝ → ℝ := fun t => ∫ p,
    finiteIsingBrownianMean beta D v B t p ^ 2 ∂ρ
  have hfm : Measurable (fun y => F y ^ 2) :=
    ((FinitePosterior.continuous_fieldMean _ _ _).pow 2).measurable
  have hcm : Measurable (fun y => ∑ u : D, C y u ^ 2) := by
    apply Finset.measurable_sum
    intro u _
    exact ((FinitePosterior.continuous_fieldCovariance _ _ _ u).pow 2).measurable
  have hE (t : ℝ) (ht : 0 ≤ t) : E t = EG t := by
    have h := integral_finiteIsingBrownian_observation_eq_standard μ ν hB hmB D
      t.toNNReal (fun y => ∑ u : D, C y u ^ 2) hcm
    unfold E EG finiteIsingBrownianCovariance finiteIsingBrownianObservation
    simpa only [C, spin, q, ρ, ρG, π, Real.coe_toNNReal t ht] using h
  have hM (t : ℝ) (ht : 0 ≤ t) : M t = MG t := by
    have h := integral_finiteIsingBrownian_observation_eq_standard μ ν hB hmB D
      t.toNNReal (fun y => F y ^ 2) hfm
    unfold M MG finiteIsingBrownianMean finiteIsingBrownianObservation
    simpa only [F, spin, q, ρ, ρG, π, Real.coe_toNNReal t ht] using h
  have hcoords (eta : D → IsingSpin) (u : D) : spin eta u = -1 ∨ spin eta u = 1 := by
    dsimp only [spin]
    cases eta u <;> simp [spinSign]
  have hbound (eta : D → IsingSpin) : |q eta| ≤ 1 := by
    dsimp only [q]
    cases eta v <;> simp [spinSign]
  have hstd := FinitePosterior.integral_finiteStandardEnergy π
    (finiteIsingEnergy beta D) (hμ.restrict_real_eq_normalized_exp D hD)
    spin q 1 hbound hcoords hT
  change IntervalIntegrable EG volume 0 T ∧
    (∫ t in 0..T, EG t) = MG T - F 0 ^ 2 ∧
    0 ≤ (∫ t in 0..T, EG t) ∧ (∫ t in 0..T, EG t) ≤ (1 : ℝ) ^ 2 at hstd
  have hzero : F 0 = 0 := finiteIsingPosterior_spin_zero beta D v
  have hEq : EqOn EG E (uIcc 0 T) := by
    intro t ht
    exact (hE t (by simpa only [min_eq_left hT] using ht.1)).symm
  have hInt : (∫ t in 0..T, EG t) = ∫ t in 0..T, E t :=
    intervalIntegral.integral_congr hEq
  change IntervalIntegrable E volume 0 T ∧
    (∫ t in 0..T, E t) = M T ∧
    0 ≤ (∫ t in 0..T, E t) ∧ (∫ t in 0..T, E t) ≤ 1
  refine ⟨hstd.1.congr (fun t ht => hEq (uIoc_subset_uIcc ht)), ?_, ?_, ?_⟩
  · rw [← hInt, hstd.2.1, hzero, zero_pow (by decide), sub_zero, hM T hT]
  · simpa only [hInt] using hstd.2.2.1
  · simpa only [hInt, one_pow] using hstd.2.2.2

end Problem367

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Posterior_FiniteIsingFilteringRepresentation
attribute [-instance] _root_.OAI.Problem367.IsingConditionalCopyBounds.graphLaw_isProbabilityMeasure _root_.OAI.Problem367.IsingObservationFactor.copies_probability _root_.OAI.Problem367.IsingObservationFactor.kernel_markov _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_observationLaw_probability _root_.OAI.Problem367.IsingObservationInnovation.observationLaw_probability _root_.OAI.Problem367.TreeKoopman.labelProbability _root_.OAI.Problem367.WienerSampler.pathMeasurableSpace _root_.OAI.Problem367.freeIsingMeasure_probability _root_.OAI.Problem367.reducedTailFintype _root_.OAI.Problem367.treeBallFintype _root_.OAI.Problem367.treeShellFintype
attribute [-simp] _root_.OAI.Problem367.ConnectedHull.pathAssignment_path _root_.OAI.Problem367.ConnectedHull.path_last _root_.OAI.Problem367.ConnectedHull.path_zero _root_.OAI.Problem367.ConnectedHull.prefix_length _root_.OAI.Problem367.ConnectedHull.prefix_zero _root_.OAI.Problem367.CutContinuationChannels.averageChannel_globalCone _root_.OAI.Problem367.CutContinuationChannels.continuationChannel_globalCone _root_.OAI.Problem367.FactorObservable.centeredSpinLp_coe _root_.OAI.Problem367.FiniteIsingSplit.splitEquiv_fst _root_.OAI.Problem367.FiniteIsingSplit.splitEquiv_snd _root_.OAI.Problem367.FinitePathGibbs.tailPartition_zero _root_.OAI.Problem367.GaussianTreeResponseNaturality.fieldEquiv_apply_image _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_apply _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_uniformObservation _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_zero _root_.OAI.Problem367.IsingObservationInnovation.uniformObservation_relabel _root_.OAI.Problem367.IsingOrientedPath.attenuation_outward _root_.OAI.Problem367.IsingOrientedPath.endpoint_extensionAt _root_.OAI.Problem367.LocalSupportGeometry.prefixVertex_length _root_.OAI.Problem367.PathSideBranches.parent_sideVertex _root_.OAI.Problem367.PathSideBranches.restrictNoisyRegion_array _root_.OAI.Problem367.PathSideBranches.sideVertex_length _root_.OAI.Problem367.PathSideBranches.sideVertex_val _root_.OAI.Problem367.PosteriorChain.transition_spinMean _root_.OAI.Problem367.PosteriorChain.transition_sum _root_.OAI.Problem367.RootedBroadcast.flipBranchToComplement_val _root_.OAI.Problem367.RootedBroadcast.pos_spinMul _root_.OAI.Problem367.RootedBroadcast.prefixFlip_branchRoot _root_.OAI.Problem367.RootedBroadcast.prefixFlip_root _root_.OAI.Problem367.RootedBroadcast.prefixTreeAut_symm_branchRoot _root_.OAI.Problem367.RootedBroadcast.prefixTreeAut_symm_root _root_.OAI.Problem367.RootedBroadcast.spinMul_pos _root_.OAI.Problem367.RootedBroadcast.spinMul_self _root_.OAI.Problem367.TreeConeCoding.length_vertex _root_.OAI.Problem367.TreeConeCoding.vertex_nil _root_.OAI.Problem367.TreeConeCoding.vertex_val _root_.OAI.Problem367.TreeGibbsAut.spinEquiv_apply_image _root_.OAI.Problem367.TreeKoopman.centeredAverage_apply_coe _root_.OAI.Problem367.TreeKoopman.centeredAverage_pow_apply_coe _root_.OAI.Problem367.TreeKoopman.centeredGenerator_apply_coe _root_.OAI.Problem367.TreeKoopman.centeredGenerator_sq _root_.OAI.Problem367.TreeKoopman.generatorOperator_sq _root_.OAI.Problem367.TreeKoopman.reverseVertex_twice _root_.OAI.Problem367.TreeKoopman.wordRelabel_cons _root_.OAI.Problem367.TreeKoopman.wordRelabel_nil _root_.OAI.Problem367.TreeLawKoopman.centeredAverage_apply_coe _root_.OAI.Problem367.TreeLawKoopman.generatorOperator_sq _root_.OAI.Problem367.TreePathGibbs.vertexEquiv_val _root_.OAI.Problem367.branchColorAut_length _root_.OAI.Problem367.branchColorAut_singleton _root_.OAI.Problem367.branchColorAut_val _root_.OAI.Problem367.branchColorMap_symm_apply _root_.OAI.Problem367.card_treeBallFinset _root_.OAI.Problem367.card_treeNeighborFinset _root_.OAI.Problem367.colorPermAut_length _root_.OAI.Problem367.colorPermAut_nil _root_.OAI.Problem367.colorPermAut_val _root_.OAI.Problem367.colorPermMap_symm_apply _root_.OAI.Problem367.colorPermMap_val _root_.OAI.Problem367.connectedSpinEncode_apply_root _root_.OAI.Problem367.connectedSpinEquiv_apply _root_.OAI.Problem367.dropVertex_length _root_.OAI.Problem367.dropVertex_val _root_.OAI.Problem367.iUnion_treeBallFinset _root_.OAI.Problem367.mem_rootComplementFinset _root_.OAI.Problem367.mem_rootComponentFinset _root_.OAI.Problem367.mem_rootComponentIndices _root_.OAI.Problem367.mem_treeBallFinset _root_.OAI.Problem367.mem_treeNeighborFinset _root_.OAI.Problem367.parentVertex_length _root_.OAI.Problem367.parentVertex_val _root_.OAI.Problem367.prefixColorAut_length _root_.OAI.Problem367.prefixColorAut_val _root_.OAI.Problem367.prefixColorMap_symm_apply _root_.OAI.Problem367.prefixFlip_twice _root_.OAI.Problem367.spinAgreementCode_eq_neg_iff _root_.OAI.Problem367.spinAgreementCode_eq_pos_iff _root_.OAI.Problem367.spinSign_flip _root_.OAI.Problem367.sum_treeShell_zero _root_.OAI.Problem367.tsum_treeShell_radial _root_.OAI.Problem367.vertexSampler_relabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal Topology

namespace Problem367.FiniteIsingFiltering

local instance finiteIsingFilteringNonemptySpin : Nonempty IsingSpin := ⟨.neg⟩

variable {d : ℕ} {Ω : Type*} [MeasurableSpace Ω]

lemma observationFiltration_le_signal
    (B : TreeVertex d → ℝ≥0 → Ω → ℝ)
    (hmB : ∀ i t, Measurable (B i t)) (D : Finset (TreeVertex d)) :
    observationFiltration B hmB D ≤ signalArrayFiltration B hmB := by
  apply arrayNaturalFiltration_le
  intro i t
  exact (arrayNaturalFiltration_stronglyAdapted (plantedArrayObservation B signal)
    (plantedArrayObservation_measurable hmB measurable_signal) i t).mono
      (arrayObservationFiltration_le_signalArrayFiltration B hmB signal measurable_signal t)

lemma observationFiltration_eq_comap
    (B : TreeVertex d → ℝ≥0 → Ω → ℝ)
    (hmB : ∀ i t, Measurable (B i t)) (D : Finset (TreeVertex d)) (t : ℝ≥0) :
    observationFiltration B hmB D t = MeasurableSpace.comap
      (fun p : State d Ω => fun i : D => fun s : Set.Iic t =>
        (s.1 : ℝ) * spinSign (p.1 i) + B i s.1 (p.2 i)) inferInstance := by
  rw [observationFiltration, arrayNaturalFiltration_eq_comap]
  congr 1
  ext p i s
  simp only [plantedArrayObservation, signal, add_comm]

omit [MeasurableSpace Ω] in
lemma mean_eq_fieldMean (beta : ℝ) (D : Finset (TreeVertex d)) (v : D)
    (B : TreeVertex d → ℝ≥0 → Ω → ℝ) (t : ℝ≥0) (p : State d Ω) :
    mean beta D v B t p = FinitePosterior.fieldMean (finiteIsingEnergy beta D)
      (fun eta u => spinSign (eta u)) (fun eta => spinSign (eta v))
      (fun i : D => plantedArrayObservation B signal i t p) := by
  unfold mean finiteIsingBrownianMean
  congr 1
  ext i
  simp only [finiteIsingBrownianObservation, Real.toNNReal_coe,
    plantedArrayObservation, signal, add_comm]

omit [MeasurableSpace Ω] in
lemma covariance_eq_fieldCovariance (beta : ℝ) (D : Finset (TreeVertex d)) (v u : D)
    (B : TreeVertex d → ℝ≥0 → Ω → ℝ) (t : ℝ≥0) (p : State d Ω) :
    covariance beta D v u B t p = FinitePosterior.fieldCovariance (finiteIsingEnergy beta D)
      (fun eta w => spinSign (eta w)) (fun eta => spinSign (eta v))
      (fun i : D => plantedArrayObservation B signal i t p) u := by
  unfold covariance finiteIsingBrownianCovariance
  congr 1
  ext i
  simp only [finiteIsingBrownianObservation, Real.toNNReal_coe,
    plantedArrayObservation, signal, add_comm]

omit [MeasurableSpace Ω] in
lemma abs_mean_le_one (beta : ℝ) (D : Finset (TreeVertex d)) (v : D)
    (B : TreeVertex d → ℝ≥0 → Ω → ℝ) (t : ℝ≥0) (p : State d Ω) :
    |mean beta D v B t p| ≤ 1 := by
  rw [mean_eq_fieldMean]
  apply FinitePosterior.abs_fieldMean_le
  intro eta
  cases eta v <;> simp [spinSign]

omit [MeasurableSpace Ω] in
lemma abs_covariance_le_two (beta : ℝ) (D : Finset (TreeVertex d)) (v u : D)
    (B : TreeVertex d → ℝ≥0 → Ω → ℝ) (t : ℝ≥0) (p : State d Ω) :
    |covariance beta D v u B t p| ≤ 2 := by
  rw [covariance_eq_fieldCovariance]
  apply (FinitePosterior.abs_fieldCovariance_le _ _ _ _ _ 1 ?_ ?_).trans_eq
    (by norm_num)
  · intro eta
    cases eta u <;> simp [spinSign]
  · intro eta
    cases eta v <;> simp [spinSign]

lemma stronglyAdapted_mean (beta : ℝ) (D : Finset (TreeVertex d)) (v : D)
    (B : TreeVertex d → ℝ≥0 → Ω → ℝ) (hmB : ∀ i t, Measurable (B i t)) :
    StronglyAdapted (observationFiltration B hmB D) (mean beta D v B) := by
  intro t
  have hobs : StronglyMeasurable[observationFiltration B hmB D t]
      (fun p : State d Ω => fun i : D => plantedArrayObservation B signal i t p) := by
    apply Measurable.stronglyMeasurable
    refine @Measurable.of_eval (State d Ω) D (fun _ => ℝ)
      (observationFiltration B hmB D t) (fun _ => inferInstance) _ ?_
    intro i
    exact (arrayNaturalFiltration_stronglyAdapted
      (fun j : D => plantedArrayObservation B signal j)
      (fun j r => plantedArrayObservation_measurable hmB measurable_signal j r) i t).measurable
  have h := (FinitePosterior.continuous_fieldMean (finiteIsingEnergy beta D)
    (fun eta u => spinSign (eta u)) (fun eta => spinSign (eta v))).comp_stronglyMeasurable hobs
  change StronglyMeasurable[observationFiltration B hmB D t]
    (fun p => mean beta D v B t p)
  simp_rw [mean_eq_fieldMean]
  exact h

lemma stronglyAdapted_covariance (beta : ℝ) (D : Finset (TreeVertex d)) (v u : D)
    (B : TreeVertex d → ℝ≥0 → Ω → ℝ) (hmB : ∀ i t, Measurable (B i t)) :
    StronglyAdapted (observationFiltration B hmB D) (covariance beta D v u B) := by
  intro t
  have hobs : StronglyMeasurable[observationFiltration B hmB D t]
      (fun p : State d Ω => fun i : D => plantedArrayObservation B signal i t p) := by
    apply Measurable.stronglyMeasurable
    refine @Measurable.of_eval (State d Ω) D (fun _ => ℝ)
      (observationFiltration B hmB D t) (fun _ => inferInstance) _ ?_
    intro i
    exact (arrayNaturalFiltration_stronglyAdapted
      (fun j : D => plantedArrayObservation B signal j)
      (fun j r => plantedArrayObservation_measurable hmB measurable_signal j r) i t).measurable
  have h := (FinitePosterior.continuous_fieldCovariance (finiteIsingEnergy beta D)
    (fun eta w => spinSign (eta w)) (fun eta => spinSign (eta v)) u).comp_stronglyMeasurable hobs
  change StronglyMeasurable[observationFiltration B hmB D t]
    (fun p => covariance beta D v u B t p)
  simp_rw [covariance_eq_fieldCovariance]
  exact h

omit [MeasurableSpace Ω] in
lemma continuous_mean (beta : ℝ) (D : Finset (TreeVertex d)) (v : D)
    (B : TreeVertex d → ℝ≥0 → Ω → ℝ)
    (hcB : ∀ i omega, Continuous (fun t => B i t omega)) (p : State d Ω) :
    Continuous (fun t => mean beta D v B t p) := by
  simp only [mean_eq_fieldMean]
  apply (FinitePosterior.continuous_fieldMean _ _ _).comp
  apply continuous_pi
  intro i
  exact (hcB i (p.2 i)).add (NNReal.continuous_coe.mul continuous_const)

omit [MeasurableSpace Ω] in
lemma continuous_covariance (beta : ℝ) (D : Finset (TreeVertex d)) (v u : D)
    (B : TreeVertex d → ℝ≥0 → Ω → ℝ)
    (hcB : ∀ i omega, Continuous (fun t => B i t omega)) (p : State d Ω) :
    Continuous (fun t => covariance beta D v u B t p) := by
  simp only [covariance_eq_fieldCovariance]
  apply (FinitePosterior.continuous_fieldCovariance _ _ _ _).comp
  apply continuous_pi
  intro i
  exact (hcB i (p.2 i)).add (NNReal.continuous_coe.mul continuous_const)

lemma progressive_mean (beta : ℝ) (D : Finset (TreeVertex d)) (v : D)
    (B : TreeVertex d → ℝ≥0 → Ω → ℝ) (hmB : ∀ i t, Measurable (B i t))
    (hcB : ∀ i omega, Continuous (fun t => B i t omega)) :
    IsStronglyProgressive (observationFiltration B hmB D) (mean beta D v B) :=
  (stronglyAdapted_mean beta D v B hmB).isStronglyProgressive_of_continuous
    (continuous_mean beta D v B hcB)

lemma memLp_mean (P : Measure (State d Ω)) [IsFiniteMeasure P]
    (beta : ℝ) (D : Finset (TreeVertex d)) (v : D)
    (B : TreeVertex d → ℝ≥0 → Ω → ℝ) (hmB : ∀ i t, Measurable (B i t))
    (t : ℝ≥0) (p : ℝ≥0∞) : MemLp (mean beta D v B t) p P := by
  apply MemLp.of_bound
    (((stronglyAdapted_mean beta D v B hmB t).mono
      ((observationFiltration B hmB D).le t)).aestronglyMeasurable) 1
  exact Eventually.of_forall fun x => by
    simpa only [Real.norm_eq_abs] using abs_mean_le_one beta D v B t x

lemma memLp_covariance (P : Measure (State d Ω)) [IsFiniteMeasure P]
    (beta : ℝ) (D : Finset (TreeVertex d)) (v u : D)
    (B : TreeVertex d → ℝ≥0 → Ω → ℝ) (hmB : ∀ i t, Measurable (B i t))
    (t : ℝ≥0) (p : ℝ≥0∞) : MemLp (covariance beta D v u B t) p P := by
  apply MemLp.of_bound
    (((stronglyAdapted_covariance beta D v u B hmB t).mono
      ((observationFiltration B hmB D).le t)).aestronglyMeasurable) 2
  exact Eventually.of_forall fun x => by
    simpa only [Real.norm_eq_abs] using abs_covariance_le_two beta D v u B t x

end Problem367.FiniteIsingFiltering

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Stochastic_FiniteIsingBrownianPosterior
attribute [-instance] _root_.OAI.Problem367.IsingConditionalCopyBounds.graphLaw_isProbabilityMeasure _root_.OAI.Problem367.IsingObservationFactor.copies_probability _root_.OAI.Problem367.IsingObservationFactor.kernel_markov _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_observationLaw_probability _root_.OAI.Problem367.IsingObservationInnovation.observationLaw_probability _root_.OAI.Problem367.TreeKoopman.labelProbability _root_.OAI.Problem367.WienerSampler.pathMeasurableSpace _root_.OAI.Problem367.freeIsingMeasure_probability _root_.OAI.Problem367.reducedTailFinite _root_.OAI.Problem367.reducedTailFintype _root_.OAI.Problem367.treeBallFinite _root_.OAI.Problem367.treeBallFintype _root_.OAI.Problem367.treeShellFinite _root_.OAI.Problem367.treeShellFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal

namespace Problem367

local instance finiteIsingBrownianPosteriorNonemptySpin : Nonempty IsingSpin := ⟨.neg⟩

theorem finiteIsingBrownian_joint_law
    {d : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure (TreeVertex d → IsingSpin)) [IsProbabilityMeasure μ]
    (ν : TreeVertex d → Measure Ω)
    {B : TreeVertex d → ℝ≥0 → Ω → ℝ}
    (hB : ∀ i, IsPreBrownianReal (B i) (ν i))
    (hmB : ∀ i t, Measurable (B i t))
    (D : Finset (TreeVertex d)) (t : ℝ≥0) :
    (μ.prod (Measure.infinitePi ν)).map
      (fun p : (TreeVertex d → IsingSpin) × (TreeVertex d → Ω) =>
        (D.restrict p.1, finiteIsingBrownianObservation B D t p)) =
    (μ.map D.restrict) ⊗ₘ finiteGaussianObservationKernel t
      (fun eta (v : D) => spinSign (eta v)) := by
  have (i : TreeVertex d) : IsProbabilityMeasure (ν i) :=
    (hB i).isGaussianProcess.isProbabilityMeasure
  let π := μ.map D.restrict
  let : IsProbabilityMeasure π := by first | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)
  let spin : (D → IsingSpin) → D → ℝ := fun eta v => spinSign (eta v)
  have hr : MeasurePreserving D.restrict μ π := ⟨D.measurable_restrict, rfl⟩
  have hp := hr.prod (finiteBrownianNoise_restrict_measurePreserving ν hB hmB D t)
  let Y : (D → IsingSpin) × (D → ℝ) → (D → IsingSpin) × (D → ℝ) :=
    fun p => (p.1, fun v => (t : ℝ) * spin p.1 v + p.2 v)
  have hY : Measurable Y := by
    apply measurable_fst.prodMk
    apply Measurable.of_eval
    intro v
    exact (measurable_const.mul
      ((measurable_of_finite (fun eta => spin eta v)).comp measurable_fst)).add
      ((measurable_pi_apply v).comp measurable_snd)
  have h := finiteGaussianPlanted_joint_law π t spin
  change Measure.map Y _ = _ at h
  rw [← hp.map_eq, Measure.map_map hY hp.measurable] at h
  unfold finiteIsingBrownianObservation
  simpa only [Y, spin, Function.comp_def, Prod.map_fst, Prod.map_snd,
    Finset.restrict, Real.toNNReal_coe] using h

theorem measurable_finiteIsingBrownianObservation
    {d : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    {B : TreeVertex d → ℝ≥0 → Ω → ℝ}
    (hmB : ∀ i t, Measurable (B i t))
    (D : Finset (TreeVertex d)) (t : ℝ) :
    Measurable (finiteIsingBrownianObservation B D t) := by
  apply Measurable.of_eval
  intro v
  exact (measurable_const.mul
    ((measurable_of_finite spinSign).comp
      ((measurable_pi_apply (v : TreeVertex d)).comp measurable_fst))).add
    ((hmB v t.toNNReal).comp
      ((measurable_pi_apply (v : TreeVertex d)).comp measurable_snd))

theorem HasFreeIsingLaw.condExp_finiteIsingBrownian_observable
    {d : ℕ} {beta : ℝ} {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure (TreeVertex d → IsingSpin)}
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ)
    (ν : TreeVertex d → Measure Ω)
    {B : TreeVertex d → ℝ≥0 → Ω → ℝ}
    (hB : ∀ i, IsPreBrownianReal (B i) (ν i))
    (hmB : ∀ i t, Measurable (B i t))
    (D : Finset (TreeVertex d)) (hD : ConnectedFinset D)
    (t : ℝ≥0) (q : (D → IsingSpin) → ℝ) :
    let ρ := μ.prod (Measure.infinitePi ν)
    ρ[fun p => q (D.restrict p.1) |
      MeasurableSpace.comap (finiteIsingBrownianObservation B D t) inferInstance] =ᵐ[ρ]
      fun p => FinitePosterior.fieldMean (finiteIsingEnergy beta D)
        (fun eta (v : D) => spinSign (eta v)) q
        (finiteIsingBrownianObservation B D t p) := by
  let : IsProbabilityMeasure μ := hμ.isProbabilityMeasure
  have (i : TreeVertex d) : IsProbabilityMeasure (ν i) :=
    (hB i).isGaussianProcess.isProbabilityMeasure
  let : IsProbabilityMeasure (μ.map D.restrict) := by first | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)
  dsimp only
  exact FiniteBayes.condExp_state_eq_of_posterior_integral
    (μ.prod (Measure.infinitePi ν)) (μ.map D.restrict)
    (finiteGaussianObservationKernel t (fun eta (v : D) => spinSign (eta v)))
    (fun p => D.restrict p.1) (finiteIsingBrownianObservation B D t)
    (D.measurable_restrict.comp measurable_fst)
    (measurable_finiteIsingBrownianObservation hmB D t)
    (finiteIsingBrownian_joint_law μ ν hB hmB D t) q
    (FinitePosterior.fieldMean (finiteIsingEnergy beta D)
      (fun eta (v : D) => spinSign (eta v)) q)
    (hμ.gaussian_restrict_posterior_mean D hD t q)

end Problem367

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Stochastic_SelectedBrownianSufficiency
attribute [-instance] _root_.OAI.Problem367.WienerSampler.pathMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace Problem367.TerminalSufficiency

theorem condExp_planted_selected_past_eq_terminal
    {ι κ S Ω : Type*} [MeasurableSpace S] [MeasurableSpace Ω]
    (ν : Measure S) (μ : κ → Measure Ω) [IsProbabilityMeasure ν]
    {B : κ → ℝ≥0 → Ω → ℝ} (hB : ∀ i, IsPreBrownianReal (B i) (μ i))
    (hmB : ∀ i t, Measurable (B i t))
    (v : ι → κ) (hv : Function.Injective v)
    (signal : S → κ → ℝ) (f : S → ℝ)
    (hSignal : Measurable signal) (hf : Measurable f) (hfint : Integrable f ν)
    (T : ℝ≥0) :
    (ν.prod (Measure.infinitePi μ))[(fun q : S × (κ → Ω) => f q.1) |
      MeasurableSpace.comap
        (fun q : S × (κ → Ω) => fun i (s : Set.Iic T) =>
          (s.1 : ℝ) * signal q.1 (v i) + B (v i) s.1 (q.2 (v i))) inferInstance]
        =ᵐ[ν.prod (Measure.infinitePi μ)]
    (ν.prod (Measure.infinitePi μ))[(fun q : S × (κ → Ω) => f q.1) |
      MeasurableSpace.comap
        (fun q : S × (κ → Ω) => fun i =>
          (T : ℝ) * signal q.1 (v i) + B (v i) T (q.2 (v i))) inferInstance] := by
  have (i : κ) : IsProbabilityMeasure (μ i) :=
    (hB i).isGaussianProcess.isProbabilityMeasure
  let R : S × (κ → Ω) → S × (ι → Ω) :=
    Prod.map id (fun ω i => ω (v i))
  have hselect : MeasurePreserving (fun ω : κ → Ω => fun i => ω (v i))
      (Measure.infinitePi μ) (Measure.infinitePi (fun i => μ (v i))) :=
    ⟨Measurable.of_eval (fun i => measurable_pi_apply (v i)),
      Measure.map_infinitePi_infinitePi_of_inj hv⟩
  have hR : MeasurePreserving R (ν.prod (Measure.infinitePi μ))
      (ν.prod (Measure.infinitePi (fun i => μ (v i)))) :=
    (MeasurePreserving.id ν).prod hselect
  let ambient : MeasurableSpace (S × (ι → Ω)) := inferInstance
  let P : MeasurableSpace (S × (ι → Ω)) := MeasurableSpace.comap
    (fun q : S × (ι → Ω) => fun i (s : Set.Iic T) =>
      (s.1 : ℝ) * signal q.1 (v i) + B (v i) s.1 (q.2 i)) inferInstance
  let Q : MeasurableSpace (S × (ι → Ω)) := MeasurableSpace.comap
    (fun q : S × (ι → Ω) => fun i =>
      (T : ℝ) * signal q.1 (v i) + B (v i) T (q.2 i)) inferInstance
  let : MeasurableSpace (S × (ι → Ω)) := ambient
  have hP : P ≤ (inferInstance : MeasurableSpace (S × (ι → Ω))) := by
    apply Measurable.comap_le
    apply Measurable.of_eval
    intro i
    apply Measurable.of_eval
    intro s
    exact (measurable_const.mul
      (((measurable_pi_apply (v i)).comp hSignal).comp measurable_fst)).add
      ((hmB (v i) s.1).comp ((measurable_pi_apply i).comp measurable_snd))
  have hQ : Q ≤ (inferInstance : MeasurableSpace (S × (ι → Ω))) := by
    apply Measurable.comap_le
    apply Measurable.of_eval
    intro i
    exact (measurable_const.mul
      (((measurable_pi_apply (v i)).comp hSignal).comp measurable_fst)).add
      ((hmB (v i) T).comp ((measurable_pi_apply i).comp measurable_snd))
  have hf' : Integrable (fun q : S × (ι → Ω) => f q.1)
      (ν.prod (Measure.infinitePi (fun i => μ (v i)))) := hfint.comp_fst _
  have hPast := Problem367.condExp_comp_measurePreserving
    (ν.prod (Measure.infinitePi μ))
    (ν.prod (Measure.infinitePi (fun i => μ (v i)))) R hR P hP hf'
  have hTerm := Problem367.condExp_comp_measurePreserving
    (ν.prod (Measure.infinitePi μ))
    (ν.prod (Measure.infinitePi (fun i => μ (v i)))) R hR Q hQ hf'
  have hCore := condExp_planted_infinite_past_eq_terminal ν (fun i => μ (v i))
    (fun i => hB (v i)) (fun i t => hmB (v i) t)
    (fun x i => signal x (v i)) f
    (Measurable.of_eval (fun i => (measurable_pi_apply (v i)).comp hSignal))
    hf hfint T
  have hPull := hR.quasiMeasurePreserving.ae_eq_comp hCore
  simp only [P, Q, MeasurableSpace.comap_comp] at hPast hTerm
  filter_upwards [hPast, hTerm, hPull] with q hp ht hc
  exact hp.trans (hc.trans ht.symm)

end Problem367.TerminalSufficiency

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Stochastic_FiniteIsingBrownianHistory
attribute [-instance] _root_.OAI.Problem367.IsingConditionalCopyBounds.graphLaw_isProbabilityMeasure _root_.OAI.Problem367.IsingObservationFactor.copies_probability _root_.OAI.Problem367.IsingObservationFactor.kernel_markov _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_observationLaw_probability _root_.OAI.Problem367.IsingObservationInnovation.observationLaw_probability _root_.OAI.Problem367.TreeKoopman.labelProbability _root_.OAI.Problem367.WienerSampler.pathMeasurableSpace _root_.OAI.Problem367.freeIsingMeasure_probability _root_.OAI.Problem367.reducedTailFinite _root_.OAI.Problem367.reducedTailFintype _root_.OAI.Problem367.treeBallFinite _root_.OAI.Problem367.treeBallFintype _root_.OAI.Problem367.treeShellFinite _root_.OAI.Problem367.treeShellFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal

namespace Problem367

local instance finiteIsingBrownianHistoryNonemptySpin_rc6668f_1 : Nonempty IsingSpin := ⟨.neg⟩
theorem HasFreeIsingLaw.condExp_finiteIsingBrownian_past
    {d : ℕ} {beta : ℝ} {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure (TreeVertex d → IsingSpin)}
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ)
    (ν : TreeVertex d → Measure Ω)
    {B : TreeVertex d → ℝ≥0 → Ω → ℝ}
    (hB : ∀ i, IsPreBrownianReal (B i) (ν i))
    (hmB : ∀ i t, Measurable (B i t))
    (D : Finset (TreeVertex d)) (hD : ConnectedFinset D)
    (q : (D → IsingSpin) → ℝ) (t : ℝ≥0) :
    let ρ := μ.prod (Measure.infinitePi ν)
    ρ[fun p => q (D.restrict p.1) |
      MeasurableSpace.comap
        (fun p : (TreeVertex d → IsingSpin) × (TreeVertex d → Ω) =>
          fun i : D => fun s : Iic t =>
            (s.1 : ℝ) * spinSign (p.1 i) + B i s.1 (p.2 i)) inferInstance] =ᵐ[ρ]
      fun p => FinitePosterior.fieldMean (finiteIsingEnergy beta D)
        (fun eta (v : D) => spinSign (eta v)) q
        (finiteIsingBrownianObservation B D t p) := by
  let : IsProbabilityMeasure μ := hμ.isProbabilityMeasure
  have hq : Measurable (fun sigma : TreeVertex d → IsingSpin => q (D.restrict sigma)) :=
    (measurable_of_finite q).comp D.measurable_restrict
  have hqi : Integrable (fun sigma : TreeVertex d → IsingSpin => q (D.restrict sigma)) μ := by
    classical
    apply (integrable_const (∑ eta, |q eta|)).mono' hq.aestronglyMeasurable
    filter_upwards with sigma
    exact Finset.single_le_sum (fun eta _ => abs_nonneg (q eta))
      (Finset.mem_univ (D.restrict sigma))
  have hs : Measurable (fun sigma : TreeVertex d → IsingSpin =>
      fun i : TreeVertex d => spinSign (sigma i)) := by
    apply Measurable.of_eval
    intro i
    exact (measurable_of_finite spinSign).comp (measurable_pi_apply (i : TreeVertex d))
  have h := TerminalSufficiency.condExp_planted_selected_past_eq_terminal
    μ ν hB hmB (fun i : D => (i : TreeVertex d)) Subtype.val_injective
    (fun sigma i => spinSign (sigma i))
    (fun sigma => q (D.restrict sigma)) hs hq hqi t
  dsimp only
  apply h.trans
  have hc := hμ.condExp_finiteIsingBrownian_observable ν hB hmB D hD t q
  unfold finiteIsingBrownianObservation at hc ⊢
  simpa only [Real.toNNReal_coe] using hc

end Problem367

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Estimates_FiniteIsingInnovation
attribute [-instance] _root_.OAI.Problem367.IsingConditionalCopyBounds.graphLaw_isProbabilityMeasure _root_.OAI.Problem367.IsingObservationFactor.copies_probability _root_.OAI.Problem367.IsingObservationFactor.kernel_markov _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_observationLaw_probability _root_.OAI.Problem367.IsingObservationInnovation.observationLaw_probability _root_.OAI.Problem367.TreeKoopman.labelProbability _root_.OAI.Problem367.freeIsingMeasure_probability _root_.OAI.Problem367.reducedTailFintype _root_.OAI.Problem367.treeBallFintype _root_.OAI.Problem367.treeShellFintype
attribute [-simp] _root_.OAI.Problem367.ConnectedHull.pathAssignment_path _root_.OAI.Problem367.ConnectedHull.path_last _root_.OAI.Problem367.ConnectedHull.path_zero _root_.OAI.Problem367.ConnectedHull.prefix_length _root_.OAI.Problem367.ConnectedHull.prefix_zero _root_.OAI.Problem367.CutContinuationChannels.averageChannel_globalCone _root_.OAI.Problem367.CutContinuationChannels.continuationChannel_globalCone _root_.OAI.Problem367.FactorObservable.centeredSpinLp_coe _root_.OAI.Problem367.FiniteIsingSplit.splitEquiv_fst _root_.OAI.Problem367.FiniteIsingSplit.splitEquiv_snd _root_.OAI.Problem367.FinitePathGibbs.tailPartition_zero _root_.OAI.Problem367.GaussianTreeResponseNaturality.fieldEquiv_apply_image _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_apply _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_uniformObservation _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_zero _root_.OAI.Problem367.IsingObservationInnovation.uniformObservation_relabel _root_.OAI.Problem367.IsingOrientedPath.attenuation_outward _root_.OAI.Problem367.IsingOrientedPath.endpoint_extensionAt _root_.OAI.Problem367.LocalSupportGeometry.prefixVertex_length _root_.OAI.Problem367.PathSideBranches.parent_sideVertex _root_.OAI.Problem367.PathSideBranches.restrictNoisyRegion_array _root_.OAI.Problem367.PathSideBranches.sideVertex_length _root_.OAI.Problem367.PathSideBranches.sideVertex_val _root_.OAI.Problem367.PosteriorChain.transition_spinMean _root_.OAI.Problem367.PosteriorChain.transition_sum _root_.OAI.Problem367.RootedBroadcast.flipBranchToComplement_val _root_.OAI.Problem367.RootedBroadcast.pos_spinMul _root_.OAI.Problem367.RootedBroadcast.prefixFlip_branchRoot _root_.OAI.Problem367.RootedBroadcast.prefixFlip_root _root_.OAI.Problem367.RootedBroadcast.prefixTreeAut_symm_branchRoot _root_.OAI.Problem367.RootedBroadcast.prefixTreeAut_symm_root _root_.OAI.Problem367.RootedBroadcast.spinMul_pos _root_.OAI.Problem367.RootedBroadcast.spinMul_self _root_.OAI.Problem367.TreeConeCoding.length_vertex _root_.OAI.Problem367.TreeConeCoding.vertex_nil _root_.OAI.Problem367.TreeConeCoding.vertex_val _root_.OAI.Problem367.TreeGibbsAut.spinEquiv_apply_image _root_.OAI.Problem367.TreeKoopman.centeredAverage_apply_coe _root_.OAI.Problem367.TreeKoopman.centeredAverage_pow_apply_coe _root_.OAI.Problem367.TreeKoopman.centeredGenerator_apply_coe _root_.OAI.Problem367.TreeKoopman.centeredGenerator_sq _root_.OAI.Problem367.TreeKoopman.generatorOperator_sq _root_.OAI.Problem367.TreeKoopman.reverseVertex_twice _root_.OAI.Problem367.TreeKoopman.wordRelabel_cons _root_.OAI.Problem367.TreeKoopman.wordRelabel_nil _root_.OAI.Problem367.TreeLawKoopman.centeredAverage_apply_coe _root_.OAI.Problem367.TreeLawKoopman.generatorOperator_sq _root_.OAI.Problem367.TreePathGibbs.vertexEquiv_val _root_.OAI.Problem367.branchColorAut_length _root_.OAI.Problem367.branchColorAut_singleton _root_.OAI.Problem367.branchColorAut_val _root_.OAI.Problem367.branchColorMap_symm_apply _root_.OAI.Problem367.card_treeBallFinset _root_.OAI.Problem367.card_treeNeighborFinset _root_.OAI.Problem367.colorPermAut_length _root_.OAI.Problem367.colorPermAut_nil _root_.OAI.Problem367.colorPermAut_val _root_.OAI.Problem367.colorPermMap_symm_apply _root_.OAI.Problem367.colorPermMap_val _root_.OAI.Problem367.connectedSpinEncode_apply_root _root_.OAI.Problem367.connectedSpinEquiv_apply _root_.OAI.Problem367.dropVertex_length _root_.OAI.Problem367.dropVertex_val _root_.OAI.Problem367.iUnion_treeBallFinset _root_.OAI.Problem367.innovationPath_apply _root_.OAI.Problem367.mem_rootComplementFinset _root_.OAI.Problem367.mem_rootComponentFinset _root_.OAI.Problem367.mem_rootComponentIndices _root_.OAI.Problem367.mem_treeBallFinset _root_.OAI.Problem367.mem_treeNeighborFinset _root_.OAI.Problem367.parentVertex_length _root_.OAI.Problem367.parentVertex_val _root_.OAI.Problem367.prefixColorAut_length _root_.OAI.Problem367.prefixColorAut_val _root_.OAI.Problem367.prefixColorMap_symm_apply _root_.OAI.Problem367.prefixFlip_twice _root_.OAI.Problem367.spinAgreementCode_eq_neg_iff _root_.OAI.Problem367.spinAgreementCode_eq_pos_iff _root_.OAI.Problem367.spinSign_flip _root_.OAI.Problem367.sum_treeShell_zero _root_.OAI.Problem367.tsum_treeShell_radial
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped NNReal
open Problem367.ConditionalCharacteristic

namespace Problem367.FiniteIsingFiltering

variable {d : ℕ} {Ω : Type*} [MeasurableSpace Ω]

theorem innovation_stronglyAdapted
    (beta : ℝ) (D : Finset (TreeVertex d)) (v : D)
    (B : TreeVertex d → ℝ≥0 → Ω → ℝ) (hmB : ∀ i t, Measurable (B i t))
    (hcB : ∀ i omega, Continuous (fun t => B i t omega)) :
    StronglyAdapted (observationFiltration B hmB D) (innovation beta D v B) :=
  (arrayNaturalFiltration_stronglyAdapted
    (fun i : D => plantedArrayObservation B signal i)
    (fun i t => plantedArrayObservation_measurable hmB measurable_signal i t) v).sub
    (stronglyAdapted_nnrealTimePrimitive (progressive_mean beta D v B hmB hcB))

theorem continuous_innovation
    (beta : ℝ) (D : Finset (TreeVertex d)) (v : D)
    (B : TreeVertex d → ℝ≥0 → Ω → ℝ) (hmB : ∀ i t, Measurable (B i t))
    (hcB : ∀ i omega, Continuous (fun t => B i t omega)) (p : State d Ω) :
    Continuous (fun t => innovation beta D v B t p) := by
  have hA := lipschitzWith_nnrealTimePrimitive_of_progressive
    (progressive_mean beta D v B hmB hcB)
    (C := 1) (fun t q => by simpa only [Real.norm_eq_abs, NNReal.coe_one] using abs_mean_le_one beta D v B t q) p
  exact ((hcB v (p.2 v)).add (NNReal.continuous_coe.mul continuous_const)).sub hA.continuous

theorem innovation_increment_drift_bound
    (beta : ℝ) (D : Finset (TreeVertex d)) (v : D)
    (B : TreeVertex d → ℝ≥0 → Ω → ℝ) (hmB : ∀ i t, Measurable (B i t))
    (hcB : ∀ i omega, Continuous (fun t => B i t omega))
    {s t : ℝ≥0} (hst : s ≤ t) (p : State d Ω) :
    |(innovation beta D v B t p - innovation beta D v B s p) -
      (B v t (p.2 v) - B v s (p.2 v))| ≤ 2 * ((t : ℝ) - (s : ℝ)) := by
  have hlip := innovationCorrection_two_lipschitzWith
    (progressive_mean beta D v B hmB hcB)
    (fun r q => by simpa only [Real.norm_eq_abs] using abs_mean_le_one beta D v B r q)
    (σ := fun q : State d Ω => signal q.1 v)
    (fun q => by cases hs : q.1 v <;> norm_num [signal, spinSign, hs]) p
  have h := hlip.dist_le_mul t s
  have heq : (innovation beta D v B t p - innovation beta D v B s p) -
      (B v t (p.2 v) - B v s (p.2 v)) =
      ((t : ℝ) * signal p.1 v - nnrealTimePrimitive (mean beta D v B) t p) -
      ((s : ℝ) * signal p.1 v - nnrealTimePrimitive (mean beta D v B) s p) := by
    unfold innovation plantedArrayObservation
    ring
  rw [heq]
  simpa only [Real.dist_eq, NNReal.dist_eq, NNReal.coe_ofNat,
    abs_of_nonneg (show (0 : ℝ) ≤ (t : ℝ) - (s : ℝ) from sub_nonneg.mpr hst)] using h

section Posterior

variable {beta : ℝ} (D : Finset (TreeVertex d))
  (μ : Measure (TreeVertex d → IsingSpin)) [IsProbabilityMeasure μ]
  (ν : TreeVertex d → Measure Ω)
  {B : TreeVertex d → ℝ≥0 → Ω → ℝ}
  (hB : ∀ i, IsPreBrownianReal (B i) (ν i))
  (hmB : ∀ i t, Measurable (B i t))
  (hcB : ∀ i omega, Continuous (fun t => B i t omega))
  (hposterior : ∀ v : D, ∀ t, mean beta D v B t =ᵐ[μ.prod (Measure.infinitePi ν)]
    (μ.prod (Measure.infinitePi ν))[(fun p : State d Ω => signal p.1 v) |
      observationFiltration B hmB D t])

include hB hmB hcB hposterior

theorem innovation_martingale_of_posterior (v : D) :
    Martingale (innovation beta D v B) (observationFiltration B hmB D)
      (μ.prod (Measure.infinitePi ν)) := by
  have (i : TreeVertex d) : IsProbabilityMeasure (ν i) :=
    (hB i).isGaussianProcess.isProbabilityMeasure
  have hs : Integrable (fun sigma => signal sigma v) μ := by
    apply (integrable_const (1 : ℝ)).mono'
      (((measurable_pi_apply (v : TreeVertex d)).comp measurable_signal).aestronglyMeasurable)
    exact Filter.Eventually.of_forall fun sigma => by
      cases hsig : sigma v <;> norm_num [signal, spinSign, hsig]
  exact compensated_observation_martingale_of_posterior_version
    (preBrownian_martingale_signalArrayFiltration μ ν hB hmB v)
    (observationFiltration_le_signal B hmB D) (hs.comp_fst _)
    (arrayNaturalFiltration_stronglyAdapted
      (fun i : D => plantedArrayObservation B signal i)
      (fun i t => plantedArrayObservation_measurable hmB measurable_signal i t) v)
    (stronglyAdapted_mean beta D v B hmB) (hposterior v)
    (stronglyAdapted_nnrealTimePrimitive (progressive_mean beta D v B hmB hcB))
    (fun s t _ => integrable_nnreal_process_interval_of_progressive_bounded
      (progressive_mean beta D v B hmB hcB) 1
      (fun r => Filter.Eventually.of_forall (fun p => abs_mean_le_one beta D v B r p)) s t)

theorem innovation_isBrownianReal_of_posterior (v : D) :
    IsBrownianReal (innovation beta D v B) (μ.prod (Measure.infinitePi ν)) := by
  have (i : TreeVertex d) : IsProbabilityMeasure (ν i) :=
    (hB i).isGaussianProcess.isProbabilityMeasure
  apply BrownianInnovation.isBrownianReal_of_bounded_drift
    (planted_coordinate_preBrownian μ ν hB v)
    (innovation_martingale_of_posterior D μ ν hB hmB hcB hposterior v)
    (L := 2)
  · intro s t hst
    have h := planted_weighted_increment_sq_condExp_subfield μ ν hB hmB hst
      ({(v : TreeVertex d)} : Finset (TreeVertex d)) (fun _ => (1 : ℝ))
      (observationFiltration_le_signal B hmB D s)
    simpa only [Finset.sum_singleton, one_mul, one_pow, mul_one] using h
  · norm_num
  · intro s t hst
    exact Filter.Eventually.of_forall (innovation_increment_drift_bound beta D v B hmB hcB hst)
  · have hzero := (planted_noise_coordinate_measurePreserving μ ν v).quasiMeasurePreserving.ae
      (hB v).eval_zero_ae_eq_zero
    filter_upwards [hzero] with p hp
    simpa only [innovation, plantedArrayObservation, nnrealTimePrimitive, NNReal.coe_zero,
      zero_mul, add_zero, intervalIntegral.integral_same, sub_zero] using hp
  · exact Filter.Eventually.of_forall (continuous_innovation beta D v B hmB hcB)

theorem innovation_unit_projection_condExp_character_of_posterior
    (a : D → ℝ) (ha : ∑ i, a i ^ 2 = 1)
    {s t : ℝ≥0} (hst : s ≤ t) (u : ℝ) :
    (μ.prod (Measure.infinitePi ν))[character (fun p => ∑ i : D, a i *
      (innovation beta D i B t p - innovation beta D i B s p)) u |
        observationFiltration B hmB D s] =ᵐ[μ.prod (Measure.infinitePi ν)]
      fun _ => Complex.exp (-(((t - s : ℝ≥0) : ℝ) : ℂ) * (u : ℂ)^2 / 2) := by
  classical
  have (i : TreeVertex d) : IsProbabilityMeasure (ν i) :=
    (hB i).isGaussianProcess.isProbabilityMeasure
  let P := μ.prod (Measure.infinitePi ν)
  let F := observationFiltration B hmB D
  let W : ℝ≥0 → State d Ω → ℝ := fun r p => ∑ i : D, a i * innovation beta D i B r p
  let N : ℝ≥0 → State d Ω → ℝ := fun r p => ∑ i : D, a i * B i r (p.2 i)
  have hN : IsPreBrownianReal N P :=
    BrownianLinearCombination.isPreBrownianReal_sum
      (fun i : D => planted_coordinate_preBrownian μ ν hB i)
      ((planted_coordinate_paths_iIndepFun μ ν hmB).precomp Subtype.val_injective) a ha
  have hW : Martingale W F P :=
    BrownianLinearCombination.martingale_sum F
      (fun i : D => innovation_martingale_of_posterior D μ ν hB hmB hcB hposterior i) a
  let c : TreeVertex d → ℝ := fun i => if hi : i ∈ D then a ⟨i, hi⟩ else 0
  have hc (i : D) : c i = a i := by simp [c, i.property]
  have hcs : ∑ i ∈ D, c i ^ 2 = 1 := by
    rw [← Finset.sum_coe_sort D]
    simpa only [hc] using ha
  have hvariance : ∀ r v : ℝ≥0, r ≤ v →
      P[(fun p => (N v p - N r p)^2) | F r] =ᵐ[P]
        fun _ => (v : ℝ) - (r : ℝ) := by
    intro r v hrv
    have heq : (fun p : State d Ω => (N v p - N r p)^2) =
        (fun p => (∑ i ∈ D, c i * (B i v (p.2 i) - B i r (p.2 i)))^2) := by
      funext p
      rw [← Finset.sum_coe_sort D]
      simp only [hc, N, mul_sub, Finset.sum_sub_distrib]
    rw [heq]
    have h := planted_weighted_increment_sq_condExp_subfield μ ν hB hmB hrv D c
      (observationFiltration_le_signal B hmB D r)
    simpa only [hcs, mul_one] using h
  have hbound : ∀ r v : ℝ≥0, r ≤ v → ∀ᵐ p ∂P,
      |(W v p - W r p) - (N v p - N r p)| ≤
        (2 * ∑ i : D, |a i|) * ((v : ℝ) - (r : ℝ)) := by
    intro r v hrv
    apply Filter.Eventually.of_forall
    intro p
    let e : D → ℝ := fun i => (innovation beta D i B v p - innovation beta D i B r p) -
      (B i v (p.2 i) - B i r (p.2 i))
    have heq : (W v p - W r p) - (N v p - N r p) = ∑ i : D, a i * e i := by
      simp only [W, N, e, mul_sub, Finset.sum_sub_distrib]
    rw [heq]
    calc
      |∑ i : D, a i * e i| ≤ ∑ i : D, |a i * e i| := Finset.abs_sum_le_sum_abs _ _
      _ = ∑ i : D, |a i| * |e i| := by simp only [abs_mul]
      _ ≤ ∑ i : D, |a i| * (2 * ((v : ℝ) - (r : ℝ))) := by
        apply Finset.sum_le_sum
        intro i _
        exact mul_le_mul_of_nonneg_left
          (innovation_increment_drift_bound beta D i B hmB hcB hrv p) (abs_nonneg _)
      _ = _ := by rw [← Finset.sum_mul]; ring
  apply BrownianCharacterization.condExp_character_of_setIntegral (F.le s)
  · exact Finset.measurable_sum _ fun i _ =>
      ((((innovation_stronglyAdapted beta D i B hmB hcB t).mono (F.le t)).measurable).sub
        (((innovation_stronglyAdapted beta D i B hmB hcB s).mono (F.le s)).measurable)).const_mul (a i)
  · intro A hA
    have h := BrownianInnovation.setIntegral_character_of_bounded_drift hN hW hvariance
      (by positivity : 0 ≤ 2 * ∑ i : D, |a i|) hbound hst hA u
    simpa only [W, mul_sub, Finset.sum_sub_distrib] using h

theorem innovation_increment_law_and_indep_of_posterior
    {E : Type*} [mE : MeasurableSpace E] {Y : State d Ω → E}
    (s t : ℝ≥0) (hst : s ≤ t)
    (hY : Measurable[observationFiltration B hmB D s] Y) :
    HasLaw (fun p i => innovation beta D i B t p - innovation beta D i B s p)
      (Measure.pi (fun _ : D => gaussianReal 0 (t - s)))
      (μ.prod (Measure.infinitePi ν)) ∧
    iIndepFun (fun i p => innovation beta D i B t p - innovation beta D i B s p)
      (μ.prod (Measure.infinitePi ν)) ∧
    IndepFun (fun p i => innovation beta D i B t p - innovation beta D i B s p) Y
      (μ.prod (Measure.infinitePi ν)) := by
  have (i : TreeVertex d) : IsProbabilityMeasure (ν i) :=
    (hB i).isGaussianProcess.isProbabilityMeasure
  have hm : Measurable (fun p i => innovation beta D i B t p - innovation beta D i B s p) := by
    apply Measurable.of_eval
    intro i
    exact (((innovation_stronglyAdapted beta D i B hmB hcB t).mono
      ((observationFiltration B hmB D).le t)).measurable).sub
      (((innovation_stronglyAdapted beta D i B hmB hcB s).mono
        ((observationFiltration B hmB D).le s)).measurable)
  have h := ConditionalGaussianVector.product_gaussian_law_and_indep_of_condExp_unit_character
    ((observationFiltration B hmB D).le s) hm (t - s)
    (fun a ha u => innovation_unit_projection_condExp_character_of_posterior
      D μ ν hB hmB hcB hposterior a ha hst u) hY
  refine ⟨h.1, ?_, h.2⟩
  apply (iIndepFun_iff_hasLaw_pi_pi (fun i : D =>
    (measurePreserving_eval (fun _ : D => gaussianReal 0 (t - s)) i).fun_comp_hasLaw h.1)).mpr
  exact h.1

theorem innovation_increment_indep_filtration_of_posterior
    (s t : ℝ≥0) (hst : s ≤ t) :
    Indep (MeasurableSpace.comap
      (fun p i => innovation beta D i B t p - innovation beta D i B s p) inferInstance)
      (observationFiltration B hmB D s) (μ.prod (Measure.infinitePi ν)) := by
  have h := (innovation_increment_law_and_indep_of_posterior D μ ν hB hmB hcB hposterior
    (E := State d Ω) (Y := id) (mE := observationFiltration B hmB D s)
    s t hst measurable_id).2.2
  change Indep _ ((observationFiltration B hmB D s).comap id) _ at h
  simpa only [MeasurableSpace.comap_id] using h

end Posterior

section Actual

variable {beta : ℝ} {μ : Measure (TreeVertex d → IsingSpin)}
  (hμ : HasFreeIsingLaw (Real.tanh beta) μ)
  (ν : TreeVertex d → Measure Ω)
  {B : TreeVertex d → ℝ≥0 → Ω → ℝ}
  (hB : ∀ i, IsPreBrownianReal (B i) (ν i))
  (hmB : ∀ i t, Measurable (B i t))
  (hcB : ∀ i omega, Continuous (fun t => B i t omega))
  (D : Finset (TreeVertex d)) (hD : ConnectedFinset D)

include hμ hB hD

theorem mean_eq_condExp (v : D) (t : ℝ≥0) :
    mean beta D v B t =ᵐ[μ.prod (Measure.infinitePi ν)]
      (μ.prod (Measure.infinitePi ν))[(fun p : State d Ω => signal p.1 v) |
        observationFiltration B hmB D t] := by
  have h := hμ.condExp_finiteIsingBrownian_past ν hB hmB D hD
    (fun eta => spinSign (eta v)) t
  rw [← observationFiltration_eq_comap B hmB D t] at h
  exact h.symm

include hmB hcB

theorem innovation_isBrownianReal (v : D) :
    IsBrownianReal (innovation beta D v B) (μ.prod (Measure.infinitePi ν)) := by
  let := hμ.isProbabilityMeasure
  exact innovation_isBrownianReal_of_posterior D μ ν hB hmB hcB
    (mean_eq_condExp hμ ν hB hmB D hD) v

theorem innovation_increment_law_and_indep
    {E : Type*} [MeasurableSpace E] {Y : State d Ω → E}
    (s t : ℝ≥0) (hst : s ≤ t)
    (hY : Measurable[observationFiltration B hmB D s] Y) :
    HasLaw (fun p i => innovation beta D i B t p - innovation beta D i B s p)
      (Measure.pi (fun _ : D => gaussianReal 0 (t - s)))
      (μ.prod (Measure.infinitePi ν)) ∧
    iIndepFun (fun i p => innovation beta D i B t p - innovation beta D i B s p)
      (μ.prod (Measure.infinitePi ν)) ∧
    IndepFun (fun p i => innovation beta D i B t p - innovation beta D i B s p) Y
      (μ.prod (Measure.infinitePi ν)) := by
  let := hμ.isProbabilityMeasure
  exact innovation_increment_law_and_indep_of_posterior D μ ν hB hmB hcB
    (mean_eq_condExp hμ ν hB hmB D hD) s t hst hY

theorem innovation_increment_indep_filtration (s t : ℝ≥0) (hst : s ≤ t) :
    Indep (MeasurableSpace.comap
      (fun p i => innovation beta D i B t p - innovation beta D i B s p) inferInstance)
      (observationFiltration B hmB D s) (μ.prod (Measure.infinitePi ν)) := by
  let := hμ.isProbabilityMeasure
  exact innovation_increment_indep_filtration_of_posterior D μ ν hB hmB hcB
    (mean_eq_condExp hμ ν hB hmB D hD) s t hst

end Actual
end Problem367.FiniteIsingFiltering

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

section Hilbert

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem eq_of_cross_energy {x y : E}
    (hcross : inner ℝ x y = ‖y‖ ^ 2) (henergy : ‖x‖ ^ 2 = ‖y‖ ^ 2) :
    x = y := by
  have hz : ‖x - y‖ ^ 2 = 0 := by
    rw [norm_sub_sq_real, hcross, henergy]
    ring
  exact sub_eq_zero.mp (norm_eq_zero.mp (sq_eq_zero_iff.mp hz))

variable [CompleteSpace E]

theorem hasSum_of_orthogonal_cross_energy
    {ι : Type*} (x : E) (f : ι → E)
    (horth : Pairwise fun i j => inner ℝ (f i) (f j) = 0)
    (hsum : Summable fun i => ‖f i‖ ^ 2)
    (hcross : ∀ i, inner ℝ x (f i) = ‖f i‖ ^ 2)
    (henergy : ‖x‖ ^ 2 = ∑' i, ‖f i‖ ^ 2) : HasSum f x := by
  have hf := PredictableL2.summable_of_orthogonal_sq f horth hsum
  have hinner := hf.hasSum.mapL (innerSL ℝ x)
  change HasSum (fun i => inner ℝ x (f i)) (inner ℝ x (∑' i, f i)) at hinner
  simp only [hcross] at hinner
  have hcross' : inner ℝ x (∑' i, f i) = ‖∑' i, f i‖ ^ 2 := by
    rw [PredictableL2.norm_tsum_sq_of_orthogonal f horth hsum]
    exact hinner.unique hsum.hasSum
  have henergy' : ‖x‖ ^ 2 = ‖∑' i, f i‖ ^ 2 := by
    rw [PredictableL2.norm_tsum_sq_of_orthogonal f horth hsum]
    exact henergy
  rw [eq_of_cross_energy hcross' henergy']
  exact hf.hasSum

end Hilbert

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

theorem integral_mul_eq_of_meanSquare_limit
    {α : Type*} {l : Filter α} [NeBot l]
    {M I : Ω → ℝ} {S : α → Ω → ℝ} {a : ℝ}
    (hM : MemLp M 2 μ) (hI : MemLp I 2 μ)
    (hS : ∀ n, MemLp (S n) 2 μ)
    (hSlim : Tendsto (fun n => ∫ ω, (S n ω - I ω) ^ 2 ∂μ) l (𝓝 0))
    (hcross : Tendsto (fun n => ∫ ω, M ω * S n ω ∂μ) l (𝓝 a)) :
    (∫ ω, M ω * I ω ∂μ) = a := by
  have h := (tendsto_const_nhds (x := hM.toLp M)).inner (𝕜 := ℝ)
    (tendsto_toLp_of_integral_sq_error hS hI hSlim)
  simp only [PredictableL2.inner_toLp] at h
  exact tendsto_nhds_unique h hcross

theorem hasSum_toLp_of_cross_energy
    {ι : Type*} {M : Ω → ℝ} (hM : MemLp M 2 μ)
    (I : ι → Ω → ℝ) (hI : ∀ i, MemLp (I i) 2 μ)
    (horth : Pairwise fun i j => ∫ ω, I i ω * I j ω ∂μ = 0)
    (hsum : Summable fun i => ∫ ω, I i ω ^ 2 ∂μ)
    (hcross : ∀ i, (∫ ω, M ω * I i ω ∂μ) = ∫ ω, I i ω ^ 2 ∂μ)
    (henergy : (∫ ω, M ω ^ 2 ∂μ) = ∑' i, ∫ ω, I i ω ^ 2 ∂μ) :
    HasSum (fun i => (hI i).toLp (I i)) (hM.toLp M) := by
  apply hasSum_of_orthogonal_cross_energy
  · intro i j hij
    simpa only [PredictableL2.inner_toLp] using horth hij
  · simpa only [PredictableL2.norm_toLp_sq] using hsum
  · intro i
    simpa only [PredictableL2.inner_toLp, PredictableL2.norm_toLp_sq] using hcross i
  · simpa only [PredictableL2.norm_toLp_sq] using henergy

theorem ae_eq_fintype_sum_of_cross_energy
    {ι : Type*} [Fintype ι] {M : Ω → ℝ} (hM : MemLp M 2 μ)
    (I : ι → Ω → ℝ) (hI : ∀ i, MemLp (I i) 2 μ)
    (horth : Pairwise fun i j => ∫ ω, I i ω * I j ω ∂μ = 0)
    (hcross : ∀ i, (∫ ω, M ω * I i ω ∂μ) = ∫ ω, I i ω ^ 2 ∂μ)
    (henergy : (∫ ω, M ω ^ 2 ∂μ) = ∑ i, ∫ ω, I i ω ^ 2 ∂μ) :
    M =ᵐ[μ] fun ω => ∑ i, I i ω := by
  classical
  have hs := hasSum_toLp_of_cross_energy hM I hI horth (hasSum_fintype _).summable
    hcross (by simpa only [tsum_fintype] using henergy)
  have heq := hs.unique (hasSum_fintype (fun i => (hI i).toLp (I i)))
  apply (hM.toLp_eq_toLp_iff (memLp_finsetSum Finset.univ (fun i _ => hI i))).mp
  rw [PredictableL2.toLp_finsetSum]
  exact heq

end RandomVariables

end Problem367.FilteringRepresentationClosure

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Stochastic_FiniteIsingFilteringIntegral
attribute [-instance] _root_.OAI.Problem367.IsingConditionalCopyBounds.graphLaw_isProbabilityMeasure _root_.OAI.Problem367.IsingObservationFactor.copies_probability _root_.OAI.Problem367.IsingObservationFactor.kernel_markov _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_observationLaw_probability _root_.OAI.Problem367.IsingObservationInnovation.observationLaw_probability _root_.OAI.Problem367.TreeKoopman.labelProbability _root_.OAI.Problem367.freeIsingMeasure_probability
attribute [-simp] _root_.OAI.Problem367.ConnectedHull.pathAssignment_path _root_.OAI.Problem367.ConnectedHull.path_last _root_.OAI.Problem367.ConnectedHull.path_zero _root_.OAI.Problem367.CutContinuationChannels.averageChannel_globalCone _root_.OAI.Problem367.CutContinuationChannels.continuationChannel_globalCone _root_.OAI.Problem367.FactorObservable.centeredSpinLp_coe _root_.OAI.Problem367.FiniteIsingSplit.splitEquiv_fst _root_.OAI.Problem367.FiniteIsingSplit.splitEquiv_snd _root_.OAI.Problem367.FinitePathGibbs.tailPartition_zero _root_.OAI.Problem367.GaussianTreeResponseNaturality.fieldEquiv_apply_image _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_apply _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_uniformObservation _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_zero _root_.OAI.Problem367.IsingObservationInnovation.uniformObservation_relabel _root_.OAI.Problem367.IsingOrientedPath.attenuation_outward _root_.OAI.Problem367.IsingOrientedPath.endpoint_extensionAt _root_.OAI.Problem367.LocalSupportGeometry.prefixVertex_length _root_.OAI.Problem367.PathSideBranches.parent_sideVertex _root_.OAI.Problem367.PathSideBranches.restrictNoisyRegion_array _root_.OAI.Problem367.PathSideBranches.sideVertex_length _root_.OAI.Problem367.PathSideBranches.sideVertex_val _root_.OAI.Problem367.PosteriorChain.transition_spinMean _root_.OAI.Problem367.PosteriorChain.transition_sum _root_.OAI.Problem367.RootedBroadcast.flipBranchToComplement_val _root_.OAI.Problem367.RootedBroadcast.pos_spinMul _root_.OAI.Problem367.RootedBroadcast.prefixFlip_branchRoot _root_.OAI.Problem367.RootedBroadcast.prefixFlip_root _root_.OAI.Problem367.RootedBroadcast.prefixTreeAut_symm_branchRoot _root_.OAI.Problem367.RootedBroadcast.prefixTreeAut_symm_root _root_.OAI.Problem367.RootedBroadcast.spinMul_pos _root_.OAI.Problem367.RootedBroadcast.spinMul_self _root_.OAI.Problem367.TreeConeCoding.length_vertex _root_.OAI.Problem367.TreeConeCoding.vertex_nil _root_.OAI.Problem367.TreeConeCoding.vertex_val _root_.OAI.Problem367.TreeGibbsAut.spinEquiv_apply_image _root_.OAI.Problem367.TreeKoopman.centeredAverage_apply_coe _root_.OAI.Problem367.TreeKoopman.centeredAverage_pow_apply_coe _root_.OAI.Problem367.TreeKoopman.centeredGenerator_apply_coe _root_.OAI.Problem367.TreeKoopman.centeredGenerator_sq _root_.OAI.Problem367.TreeKoopman.generatorOperator_sq _root_.OAI.Problem367.TreeKoopman.reverseVertex_twice _root_.OAI.Problem367.TreeKoopman.wordRelabel_cons _root_.OAI.Problem367.TreeKoopman.wordRelabel_nil _root_.OAI.Problem367.TreeLawKoopman.centeredAverage_apply_coe _root_.OAI.Problem367.TreeLawKoopman.generatorOperator_sq _root_.OAI.Problem367.TreePathGibbs.vertexEquiv_val _root_.OAI.Problem367.branchColorAut_length _root_.OAI.Problem367.branchColorAut_singleton _root_.OAI.Problem367.branchColorAut_val _root_.OAI.Problem367.branchColorMap_symm_apply _root_.OAI.Problem367.colorPermAut_length _root_.OAI.Problem367.colorPermAut_nil _root_.OAI.Problem367.colorPermAut_val _root_.OAI.Problem367.colorPermMap_symm_apply _root_.OAI.Problem367.colorPermMap_val _root_.OAI.Problem367.connectedSpinEncode_apply_root _root_.OAI.Problem367.connectedSpinEquiv_apply _root_.OAI.Problem367.dropVertex_length _root_.OAI.Problem367.dropVertex_val _root_.OAI.Problem367.mem_rootComplementFinset _root_.OAI.Problem367.mem_rootComponentFinset _root_.OAI.Problem367.mem_rootComponentIndices _root_.OAI.Problem367.parentVertex_length _root_.OAI.Problem367.parentVertex_val _root_.OAI.Problem367.prefixColorAut_length _root_.OAI.Problem367.prefixColorAut_val _root_.OAI.Problem367.prefixColorMap_symm_apply _root_.OAI.Problem367.prefixFlip_twice _root_.OAI.Problem367.spinAgreementCode_eq_neg_iff _root_.OAI.Problem367.spinAgreementCode_eq_pos_iff _root_.OAI.Problem367.spinSign_flip _root_.OAI.Problem367.tsum_treeShell_radial
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal Topology BigOperators

namespace Problem367.FiniteIsingFiltering

variable {d : ℕ} {Ω : Type*} [MeasurableSpace Ω]

theorem continuous_covariance_energy
    (P : Measure (State d Ω)) [IsFiniteMeasure P]
    (beta : ℝ) (D : Finset (TreeVertex d)) (v u : D)
    (B : TreeVertex d → ℝ≥0 → Ω → ℝ) (hmB : ∀ i t, Measurable (B i t))
    (hcB : ∀ i omega, Continuous (fun t => B i t omega)) :
    Continuous (fun r : ℝ => ∫ p, covariance beta D v u B r.toNNReal p ^ 2 ∂P) := by
  have h := EnergyRiemann.continuous_energy
    (fun t => (memLp_covariance P beta D v u B hmB t 2).aestronglyMeasurable)
    (Eventually.of_forall (continuous_covariance beta D v u B hcB))
    (show (0 : ℝ) ≤ 2 by norm_num)
    (Eventually.of_forall fun p t => abs_covariance_le_two beta D v u B t p)
  exact h.comp (by fun_prop)

theorem mean_energy_eq_sum_covariance_energy
    {beta : ℝ} {μ : Measure (TreeVertex d → IsingSpin)}
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ)
    (ν : TreeVertex d → Measure Ω) {B : TreeVertex d → ℝ≥0 → Ω → ℝ}
    (hB : ∀ i, IsPreBrownianReal (B i) (ν i))
    (hmB : ∀ i t, Measurable (B i t))
    (hcB : ∀ i omega, Continuous (fun t => B i t omega))
    (D : Finset (TreeVertex d)) (hD : ConnectedFinset D) (v : D) (T : ℝ≥0) :
    (∫ p, mean beta D v B T p ^ 2 ∂μ.prod (Measure.infinitePi ν)) =
      ∑ u : D, ∫ r in (0 : ℝ)..(T : ℝ),
        ∫ p, covariance beta D v u B r.toNNReal p ^ 2 ∂μ.prod (Measure.infinitePi ν) := by
  classical
  let : IsProbabilityMeasure μ := hμ.isProbabilityMeasure
  have (i : TreeVertex d) : IsProbabilityMeasure (ν i) :=
    (hB i).isGaussianProcess.isProbabilityMeasure
  let P := μ.prod (Measure.infinitePi ν)
  have he := (hμ.integral_finiteIsingBrownianEnergy ν hB hmB D hD v T.coe_nonneg).2.1
  change (∫ r in (0 : ℝ)..(T : ℝ), ∫ p,
    ∑ u : D, finiteIsingBrownianCovariance beta D v u B r p ^ 2 ∂P) =
      ∫ p, mean beta D v B T p ^ 2 ∂P at he
  rw [← he]
  calc
    _ = ∫ r in (0 : ℝ)..(T : ℝ), ∫ p,
        ∑ u : D, covariance beta D v u B r.toNNReal p ^ 2 ∂P := by
      apply intervalIntegral.integral_congr
      intro r hr
      have hr0 : 0 ≤ r := by
        simpa only [min_eq_left T.coe_nonneg] using hr.1
      simp only [covariance, Real.coe_toNNReal r hr0]
    _ = ∫ r in (0 : ℝ)..(T : ℝ),
        ∑ u : D, ∫ p, covariance beta D v u B r.toNNReal p ^ 2 ∂P := by
      apply intervalIntegral.integral_congr
      intro r hr
      exact integral_finsetSum _ (fun u _ =>
        (memLp_covariance P beta D v u B hmB r.toNNReal 2).integrable_sq)
    _ = _ := intervalIntegral.integral_finsetSum (fun u _ =>
      (continuous_covariance_energy P beta D v u B hmB hcB).intervalIntegrable _ _)

private theorem representation_of_driver_laws
    {beta : ℝ} {μ : Measure (TreeVertex d → IsingSpin)}
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ)
    (ν : TreeVertex d → Measure Ω) {B : TreeVertex d → ℝ≥0 → Ω → ℝ}
    (hB : ∀ i, IsPreBrownianReal (B i) (ν i))
    (hmB : ∀ i t, Measurable (B i t))
    (hcB : ∀ i omega, Continuous (fun t => B i t omega))
    (D : Finset (TreeVertex d)) (hD : ConnectedFinset D) (v : D) (T : ℝ≥0)
    (W : D → ℝ≥0 → State d Ω → ℝ)
    (hW : ∀ u, IsPreBrownianReal (W u) (μ.prod (Measure.infinitePi ν)))
    (hAd : ∀ u, StronglyAdapted (observationFiltration B hmB D) (W u))
    (hind : ∀ s t, s ≤ t → Indep
      (MeasurableSpace.comap (fun p u => W u t p - W u s p) inferInstance)
      (observationFiltration B hmB D s) (μ.prod (Measure.infinitePi ν)))
    (hcross : ∀ s t, s ≤ t → Pairwise fun u w =>
      IndepFun (fun p => W u t p - W u s p) (fun p => W w t p - W w s p)
        (μ.prod (Measure.infinitePi ν)))
    (hlimit : ∀ u, Tendsto (fun n : ℕ => ∫ p, mean beta D v B T p *
      BrownianGrid.uniformSum (W u) (covariance beta D v u B) T n p
        ∂μ.prod (Measure.infinitePi ν)) atTop
      (𝓝 (∫ r in (0 : ℝ)..(T : ℝ), ∫ p,
        covariance beta D v u B r.toNNReal p ^ 2 ∂μ.prod (Measure.infinitePi ν)))) :
    ∃ I : D → State d Ω → ℝ,
      (∀ u, MemLp (I u) 2 (μ.prod (Measure.infinitePi ν))) ∧
      (∀ u, AEStronglyMeasurable[observationFiltration B hmB D T]
        (I u) (μ.prod (Measure.infinitePi ν))) ∧
      (∀ u, (∫ p, I u p ∂μ.prod (Measure.infinitePi ν)) = 0) ∧
      (∀ u, (∫ p, I u p ^ 2 ∂μ.prod (Measure.infinitePi ν)) =
        ∫ r in (0 : ℝ)..(T : ℝ), ∫ p,
          covariance beta D v u B r.toNNReal p ^ 2 ∂μ.prod (Measure.infinitePi ν)) ∧
      (Pairwise fun u w => ∫ p, I u p * I w p ∂μ.prod (Measure.infinitePi ν) = 0) ∧
      (∀ u, Tendsto (fun n => ∫ p,
        (BrownianGrid.uniformSum (W u) (covariance beta D v u B) T n p - I u p) ^ 2
          ∂μ.prod (Measure.infinitePi ν)) atTop (𝓝 0)) ∧
      (mean beta D v B T =ᵐ[μ.prod (Measure.infinitePi ν)] fun p => ∑ u, I u p) := by
  classical
  let : IsProbabilityMeasure μ := hμ.isProbabilityMeasure
  have (i : TreeVertex d) : IsProbabilityMeasure (ν i) :=
    (hB i).isGaussianProcess.isProbabilityMeasure
  let P := μ.prod (Measure.infinitePi ν)
  have hK (u : D) := stronglyAdapted_covariance beta D v u B hmB
  have hK2 (u : D) (t : ℝ≥0) := memLp_covariance P beta D v u B hmB t 2
  have hi (u : D) (s t : ℝ≥0) (hst : s ≤ t) :=
    BrownianArrayFiltration.coordinate_increment_indep_past (hind s t hst) u
  obtain ⟨I, hI, _, hterm, hzero, hiso, horth, happrox⟩ :=
    BrownianArrayFiltration.exists_channel_integrals hW hAd hind hcross
      (fun u => covariance beta D v u B) hK
      (fun u => Eventually.of_forall (continuous_covariance beta D v u B hcB))
      (fun _ => 2) (fun _ => by norm_num)
      (fun u => Eventually.of_forall fun p t => abs_covariance_le_two beta D v u B t p) T
  have hM := memLp_mean P beta D v B hmB T 2
  have htest (u : D) : (∫ p, mean beta D v B T p * I u p ∂P) = ∫ p, I u p ^ 2 ∂P := by
    rw [hiso u]
    exact FilteringRepresentationClosure.integral_mul_eq_of_meanSquare_limit hM (hI u)
      (fun n => BrownianFiltrationGrid.uniformSum_memLp (hW u) (hAd u) (hi u)
        _ (hK u) (hK2 u) T n) (happrox u) (hlimit u)
  refine ⟨I, hI, hterm, hzero, hiso, horth, happrox, ?_⟩
  apply FilteringRepresentationClosure.ae_eq_fintype_sum_of_cross_energy hM I hI horth htest
  calc
    _ = ∑ u : D, ∫ r in (0 : ℝ)..(T : ℝ), ∫ p,
        covariance beta D v u B r.toNNReal p ^ 2 ∂P :=
      mean_energy_eq_sum_covariance_energy hμ ν hB hmB hcB D hD v T
    _ = _ := Finset.sum_congr rfl (fun u _ => (hiso u).symm)

theorem exists_innovation_integral_representation_oai
    {beta : ℝ} {μ : Measure (TreeVertex d → IsingSpin)}
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ)
    (ν : TreeVertex d → Measure Ω) {B : TreeVertex d → ℝ≥0 → Ω → ℝ}
    (hB : ∀ i, IsPreBrownianReal (B i) (ν i))
    (hmB : ∀ i t, Measurable (B i t))
    (hcB : ∀ i omega, Continuous (fun t => B i t omega))
    (D : Finset (TreeVertex d)) (hD : ConnectedFinset D) (v : D) (T : ℝ≥0) :
    ∃ I : D → State d Ω → ℝ,
      (∀ u, MemLp (I u) 2 (μ.prod (Measure.infinitePi ν))) ∧
      (∀ u, AEStronglyMeasurable[observationFiltration B hmB D T]
        (I u) (μ.prod (Measure.infinitePi ν))) ∧
      (∀ u, (∫ p, I u p ∂μ.prod (Measure.infinitePi ν)) = 0) ∧
      (∀ u, (∫ p, I u p ^ 2 ∂μ.prod (Measure.infinitePi ν)) =
        ∫ r in (0 : ℝ)..(T : ℝ), ∫ p,
          covariance beta D v u B r.toNNReal p ^ 2 ∂μ.prod (Measure.infinitePi ν)) ∧
      (Pairwise fun u w => ∫ p, I u p * I w p ∂μ.prod (Measure.infinitePi ν) = 0) ∧
      (∀ u, Tendsto (fun n => ∫ p,
        (BrownianGrid.uniformSum (innovation beta D u B) (covariance beta D v u B) T n p - I u p) ^ 2
          ∂μ.prod (Measure.infinitePi ν)) atTop (𝓝 0)) ∧
      (mean beta D v B T =ᵐ[μ.prod (Measure.infinitePi ν)] fun p => ∑ u, I u p) := by
  apply representation_of_driver_laws hμ ν hB hmB hcB D hD v T
    (fun u => innovation beta D u B)
    (fun u => (innovation_isBrownianReal hμ ν hB hmB hcB D hD u).toIsPreBrownianReal)
    (fun u => innovation_stronglyAdapted beta D u B hmB hcB)
    (innovation_increment_indep_filtration hμ ν hB hmB hcB D hD)
  · intro s t hst u w huw
    have hi := (innovation_increment_law_and_indep hμ ν hB hmB hcB D hD s t hst
      (Y := fun _ => ()) measurable_const).2.1
    exact hi.indepFun huw
  · exact fun u => tendsto_cross_uniformSum hμ ν hB hmB hcB D hD v u T

end Problem367.FiniteIsingFiltering

end

end OAI
end

theorem solution.{u_1} : type_of% @OAI.Problem367.FiniteIsingFiltering.exists_innovation_integral_representation_oai.{u_1} := @OAI.Problem367.FiniteIsingFiltering.exists_innovation_integral_representation_oai.{u_1}
