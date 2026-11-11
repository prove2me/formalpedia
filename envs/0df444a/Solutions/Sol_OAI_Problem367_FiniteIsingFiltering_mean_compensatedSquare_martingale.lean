-- Prove2me | solution 1 for OAI.Problem367.FiniteIsingFiltering.mean_compensatedSquare_martingale
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T01:43:41.10817+00:00
-- url     : https://prove2.me/submissions/bf3e6cc0-ec4f-43ce-975c-bd3fa235255b

import Mathlib
import Definitions.Def_FreeIsing
import Definitions.Def_Q243FI005
import Theorems.Thm_OAI_Problem367_FiniteIsingFiltering_exists_innovation_integral_representation

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
-- module Solutions.Q243_FreeIsing.FreeIsing_Brownian_IntegralProcess
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

end Problem367.BrownianIntegralProcess

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
-- module Solutions.Q243_FreeIsing.FreeIsing_Stochastic_StoppedBrownianCross
attribute [-instance] _root_.OAI.Problem367.WienerSampler.pathMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace Problem367.StoppedBrownianCross
open StoppedSimpleIntegral BrownianFiltration StoppedBrownianSquare

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
  {B C : ℝ≥0 → Ω → ℝ} {F : Filtration ℝ≥0 mΩ}

theorem product_martingale_of_increment_product_zero [IsFiniteMeasure P]
    (hB : Martingale B F P) (hC : Martingale C F P)
    (hB2 : ∀ t, MemLp (B t) 2 P) (hC2 : ∀ t, MemLp (C t) 2 P)
    (hcross : ∀ s t, s ≤ t →
      P[(fun ω => (B t ω - B s ω) * (C t ω - C s ω)) | F s] =ᵐ[P] 0) :
    Martingale (fun t ω => B t ω * C t ω) F P := by
  refine ⟨fun t => (hB.stronglyAdapted t).mul (hC.stronglyAdapted t), ?_⟩
  intro s t hst
  have hBC : Integrable (fun ω => B s ω * (C t ω - C s ω)) P :=
    (hB2 s).integrable_mul ((hC2 t).sub (hC2 s))
  have hCB : Integrable (fun ω => C s ω * (B t ω - B s ω)) P :=
    (hC2 s).integrable_mul ((hB2 t).sub (hB2 s))
  have hzBC : P[(fun ω => B s ω * (C t ω - C s ω)) | F s] =ᵐ[P] 0 := by
    have h := intervalSum_eq_condExp_terminal_of_integrable hC hst
      (hB.stronglyAdapted s) hBC s
    filter_upwards [h] with ω hω
    simpa only [intervalSum, min_self, min_eq_left hst, sub_self, mul_zero, Pi.zero_apply] using hω
  have hzCB : P[(fun ω => C s ω * (B t ω - B s ω)) | F s] =ᵐ[P] 0 := by
    have h := intervalSum_eq_condExp_terminal_of_integrable hB hst
      (hC.stronglyAdapted s) hCB s
    filter_upwards [h] with ω hω
    simpa only [intervalSum, min_self, min_eq_left hst, sub_self, mul_zero, Pi.zero_apply] using hω
  have hDC : Integrable (fun ω => (B t ω - B s ω) * (C t ω - C s ω)) P :=
    ((hB2 t).sub (hB2 s)).integrable_mul ((hC2 t).sub (hC2 s))
  have hSS : Integrable (fun ω => B s ω * C s ω) P :=
    (hB2 s).integrable_mul (hC2 s)
  have hself : P[(fun ω => B s ω * C s ω) | F s] =
      (fun ω => B s ω * C s ω) := condExp_of_stronglyMeasurable (F.le s)
        ((hB.stronglyAdapted s).mul (hC.stronglyAdapted s)) hSS
  have hpoly : (fun ω => B t ω * C t ω) =
      ((fun ω => (B t ω - B s ω) * (C t ω - C s ω)) +
        (fun ω => B s ω * (C t ω - C s ω))) +
      ((fun ω => C s ω * (B t ω - B s ω)) + (fun ω => B s ω * C s ω)) := by
    funext ω
    simp only [Pi.add_apply]
    ring
  change P[(fun ω => B t ω * C t ω) | F s] =ᵐ[P] (fun ω => B s ω * C s ω)
  rw [hpoly]
  filter_upwards [condExp_add (hDC.add hBC) (hCB.add hSS) (F s),
    condExp_add hDC hBC (F s), condExp_add hCB hSS (F s),
    hcross s t hst, hzBC, hzCB] with ω h1 h2 h3 h4 h5 h6
  simp only [Pi.add_apply] at h1 h2 h3
  rw [hself] at h3
  rw [h1, h2, h3, h4, h5, h6]
  simp

theorem increment_product_condExp_zero
    (hB : IsPreBrownianReal B P) (_hC : IsPreBrownianReal C P)
    (hAdB : StronglyAdapted F B) (hAdC : StronglyAdapted F C)
    {s t : ℝ≥0}
    (hpair : Indep (MeasurableSpace.comap
      (fun ω => (B t ω - B s ω, C t ω - C s ω)) inferInstance) (F s) P)
    (hind : IndepFun (fun ω => B t ω - B s ω) (fun ω => C t ω - C s ω) P) :
    P[(fun ω => (B t ω - B s ω) * (C t ω - C s ω)) | F s] =ᵐ[P] 0 := by
  let : IsProbabilityMeasure P := hB.isGaussianProcess.isProbabilityMeasure
  have hmB := ((hAdB t).mono (F.le t)).measurable.sub
    ((hAdB s).mono (F.le s)).measurable
  have hmC := ((hAdC t).mono (F.le t)).measurable.sub
    ((hAdC s).mono (F.le s)).measurable
  have hmPair : Measurable[MeasurableSpace.comap
      (fun ω => (B t ω - B s ω, C t ω - C s ω)) inferInstance]
      (fun ω => (B t ω - B s ω, C t ω - C s ω)) :=
    measurable_iff_comap_le.mpr le_rfl
  have hmProd := (measurable_fst.mul measurable_snd).comp hmPair
  have hi : Indep (MeasurableSpace.comap
      (fun ω => (B t ω - B s ω) * (C t ω - C s ω)) inferInstance) (F s) P :=
    indep_of_indep_of_le_left hpair hmProd.comap_le
  have hce := condExp_indep_eq (hmB.mul hmC).comap_le (F.le s)
    (show StronglyMeasurable[MeasurableSpace.comap
      (fun ω => (B t ω - B s ω) * (C t ω - C s ω)) inferInstance]
      (fun ω => (B t ω - B s ω) * (C t ω - C s ω)) from
        (measurable_iff_comap_le.mpr le_rfl).stronglyMeasurable) hi
  have hzB : (∫ ω, B t ω - B s ω ∂P) = 0 := by
    rw [integral_sub (hB.integrable_eval t) (hB.integrable_eval s),
      hB.integral_eval, hB.integral_eval, sub_self]
  have he := hind.integral_fun_mul_eq_mul_integral hmB.aestronglyMeasurable
    hmC.aestronglyMeasurable
  rw [hzB, zero_mul] at he
  filter_upwards [hce] with ω hω
  simpa only [he, Pi.zero_apply] using hω

theorem brownian_product_martingale
    (hB : IsPreBrownianReal B P) (hC : IsPreBrownianReal C P)
    (hAdB : StronglyAdapted F B) (hAdC : StronglyAdapted F C)
    (hpair : ∀ s t, s ≤ t → Indep (MeasurableSpace.comap
      (fun ω => (B t ω - B s ω, C t ω - C s ω)) inferInstance) (F s) P)
    (hind : ∀ s t, s ≤ t →
      IndepFun (fun ω => B t ω - B s ω) (fun ω => C t ω - C s ω) P) :
    Martingale (fun t ω => B t ω * C t ω) F P := by
  let : IsProbabilityMeasure P := hB.isGaussianProcess.isProbabilityMeasure
  have hleft s t (hst : s ≤ t) : Indep (MeasurableSpace.comap
      (fun ω => B t ω - B s ω) inferInstance) (F s) P := by
    apply indep_of_indep_of_le_left (hpair s t hst)
    have hmPair : Measurable[MeasurableSpace.comap
        (fun ω => (B t ω - B s ω, C t ω - C s ω)) inferInstance]
        (fun ω => (B t ω - B s ω, C t ω - C s ω)) :=
      measurable_iff_comap_le.mpr le_rfl
    exact hmPair.fst.comap_le
  have hright s t (hst : s ≤ t) : Indep (MeasurableSpace.comap
      (fun ω => C t ω - C s ω) inferInstance) (F s) P := by
    apply indep_of_indep_of_le_left (hpair s t hst)
    have hmPair : Measurable[MeasurableSpace.comap
        (fun ω => (B t ω - B s ω, C t ω - C s ω)) inferInstance]
        (fun ω => (B t ω - B s ω, C t ω - C s ω)) :=
      measurable_iff_comap_le.mpr le_rfl
    exact hmPair.snd.comap_le
  exact product_martingale_of_increment_product_zero
    (martingale_of_independent_past hB hAdB hleft)
    (martingale_of_independent_past hC hAdC hright)
    (fun t => (hB.isGaussianProcess.hasGaussianLaw_eval t).memLp_two)
    (fun t => (hC.isGaussianProcess.hasGaussianLaw_eval t).memLp_two)
    (fun s t hst => increment_product_condExp_zero hB hC hAdB hAdC
      (hpair s t hst) (hind s t hst))

theorem intervalSum_memLp_two_of_bounded [IsFiniteMeasure P]
    (hB2 : ∀ t, MemLp (B t) 2 P) {a b : ℝ≥0} {H : Ω → ℝ}
    (hH : StronglyMeasurable[F a] H) {K : ℝ}
    (hbound : ∀ᵐ ω ∂P, ‖H ω‖ ≤ K) (t : ℝ≥0) :
    MemLp (intervalSum B H a b t) 2 P := by
  have hHtop : MemLp H (⊤ : ENNReal) P :=
    MemLp.of_bound (hH.mono (F.le a)).aestronglyMeasurable K hbound
  exact MeasureTheory.MemLp.mul' (hφ := hHtop) (hf := ((hB2 (min t b)).sub (hB2 (min t a))))

theorem intervalSum_product_martingale [IsFiniteMeasure P]
    (hB : Martingale B F P) (hC : Martingale C F P)
    (hBC : Martingale (fun t ω => B t ω * C t ω) F P)
    (hB2 : ∀ t, MemLp (B t) 2 P) (hC2 : ∀ t, MemLp (C t) 2 P)
    {a b : ℝ≥0} (hab : a ≤ b) {H G : Ω → ℝ}
    (hH : StronglyMeasurable[F a] H) (hG : StronglyMeasurable[F a] G)
    {K L : ℝ} (hboundH : ∀ᵐ ω ∂P, ‖H ω‖ ≤ K)
    (hboundG : ∀ᵐ ω ∂P, ‖G ω‖ ≤ L) :
    Martingale (fun t ω => intervalSum B H a b t ω * intervalSum C G a b t ω) F P := by
  have hHG : StronglyMeasurable[F a] (fun ω => H ω * G ω) := hH.mul hG
  have hboundHG : ∀ᵐ ω ∂P, ‖H ω * G ω‖ ≤ K * L := by
    filter_upwards [hboundH, hboundG] with ω hω kω
    rw [norm_mul]
    exact mul_le_mul hω kω (norm_nonneg _) ((norm_nonneg _).trans hω)
  have hm1 := intervalSum_martingale hBC hab hHG hboundHG
  have hCB : Integrable (fun ω => C a ω * (B b ω - B a ω)) P :=
    (hC2 a).integrable_mul ((hB2 b).sub (hB2 a))
  have hBC' : Integrable (fun ω => B a ω * (C b ω - C a ω)) P :=
    (hB2 a).integrable_mul ((hC2 b).sub (hC2 a))
  have hCBH : Integrable (fun ω => (H ω * G ω * C a ω) * (B b ω - B a ω)) P := by
    have h := hCB.bdd_mul (hHG.mono (F.le a)).aestronglyMeasurable hboundHG
    convert h using 1
    all_goals try with_reducible_and_instances rfl
    funext ω
    ring
  have hBCH : Integrable (fun ω => (H ω * G ω * B a ω) * (C b ω - C a ω)) P := by
    have h := hBC'.bdd_mul (hHG.mono (F.le a)).aestronglyMeasurable hboundHG
    convert h using 1
    all_goals try with_reducible_and_instances rfl
    funext ω
    ring
  have hm2 := intervalSum_martingale_of_integrable_terminal hB hab
    (hHG.mul (hC.stronglyAdapted a)) hCBH
  have hm3 := intervalSum_martingale_of_integrable_terminal hC hab
    (hHG.mul (hB.stronglyAdapted a)) hBCH
  convert (hm1.sub hm2).sub hm3 using 1
  all_goals try with_reducible_and_instances rfl
  funext t ω
  rcases le_total t a with hta | hat
  · simp only [intervalSum, min_eq_left hta, min_eq_left (hta.trans hab),
      sub_self, mul_zero, Pi.sub_apply]
  · simp only [intervalSum, min_eq_right hat, Pi.sub_apply, Pi.mul_apply]
    ring

theorem stopped_predictable_sum_product_martingale [IsFiniteMeasure P]
    (hB : Martingale B F P) (hC : Martingale C F P)
    (hBC : Martingale (fun t ω => B t ω * C t ω) F P)
    (hB2 : ∀ t, MemLp (B t) 2 P) (hC2 : ∀ t, MemLp (C t) 2 P)
    (τ : ℕ → ℝ≥0) (hτ : Monotone τ) (H G : ℕ → Ω → ℝ)
    (hH : ∀ i, StronglyMeasurable[F (τ i)] (H i))
    (hG : ∀ i, StronglyMeasurable[F (τ i)] (G i))
    (K L : ℕ → ℝ) (hboundH : ∀ i, ∀ᵐ ω ∂P, ‖H i ω‖ ≤ K i)
    (hboundG : ∀ i, ∀ᵐ ω ∂P, ‖G i ω‖ ≤ L i) (n : ℕ) :
    Martingale (fun t ω =>
      (∑ i ∈ Finset.range n, intervalSum B (H i) (τ i) (τ (i + 1)) t ω) *
      (∑ i ∈ Finset.range n, intervalSum C (G i) (τ i) (τ (i + 1)) t ω)) F P := by
  have hsumB2 (m : ℕ) (t : ℝ≥0) : MemLp (fun ω => ∑ i ∈ Finset.range m,
      intervalSum B (H i) (τ i) (τ (i + 1)) t ω) 2 P :=
    memLp_finsetSum _ fun i _ => intervalSum_memLp_two_of_bounded hB2 (hH i) (hboundH i) t
  have hsumC2 (m : ℕ) (t : ℝ≥0) : MemLp (fun ω => ∑ i ∈ Finset.range m,
      intervalSum C (G i) (τ i) (τ (i + 1)) t ω) 2 P :=
    memLp_finsetSum _ fun i _ => intervalSum_memLp_two_of_bounded hC2 (hG i) (hboundG i) t
  induction n with
  | zero =>
      convert martingale_zero ℝ F P using 1
      all_goals try with_reducible_and_instances rfl
      funext t ω
      simp
  | succ n ih =>
      let S : ℝ≥0 → Ω → ℝ := fun t ω => ∑ i ∈ Finset.range n,
        intervalSum B (H i) (τ i) (τ (i + 1)) t ω
      let R : ℝ≥0 → Ω → ℝ := fun t ω => ∑ i ∈ Finset.range n,
        intervalSum C (G i) (τ i) (τ (i + 1)) t ω
      have hS : Martingale S F P := finite_intervalSum_martingale hB (Finset.range n)
        τ (fun i => τ (i + 1)) H (fun i _ => hτ (Nat.le_succ i))
        (fun i _ => hH i) K (fun i _ => hboundH i)
      have hR : Martingale R F P := finite_intervalSum_martingale hC (Finset.range n)
        τ (fun i => τ (i + 1)) G (fun i _ => hτ (Nat.le_succ i))
        (fun i _ => hG i) L (fun i _ => hboundG i)
      have hnewB := intervalSum_memLp_two_of_bounded (b := τ (n + 1)) hB2 (hH n) (hboundH n) (τ (n + 1))
      have hnewC := intervalSum_memLp_two_of_bounded (b := τ (n + 1)) hC2 (hG n) (hboundG n) (τ (n + 1))
      have hiSC : Integrable (fun ω => (S (τ n) ω * G n ω) *
          (C (τ (n + 1)) ω - C (τ n) ω)) P := by
        have h := (hsumB2 n (τ n)).integrable_mul hnewC
        convert h using 1
        all_goals try with_reducible_and_instances rfl
        funext ω
        simp only [Pi.mul_apply, intervalSum, min_self, min_eq_right (hτ (Nat.le_succ n))]
        dsimp [S, R]
        simp only [intervalSum]
        ring
      have hiRB : Integrable (fun ω => (R (τ n) ω * H n ω) *
          (B (τ (n + 1)) ω - B (τ n) ω)) P := by
        have h := (hsumC2 n (τ n)).integrable_mul hnewB
        convert h using 1
        all_goals try with_reducible_and_instances rfl
        funext ω
        simp only [Pi.mul_apply, intervalSum, min_self, min_eq_right (hτ (Nat.le_succ n))]
        dsimp [S, R]
        simp only [intervalSum]
        ring
      have hSC := intervalSum_martingale_of_integrable_terminal hC (hτ (Nat.le_succ n))
        ((hS.stronglyAdapted (τ n)).mul (hG n)) hiSC
      have hRB := intervalSum_martingale_of_integrable_terminal hB (hτ (Nat.le_succ n))
        ((hR.stronglyAdapted (τ n)).mul (hH n)) hiRB
      have heqSC : (fun t ω => S t ω * intervalSum C (G n) (τ n) (τ (n + 1)) t ω) =
          intervalSum C (fun ω => S (τ n) ω * G n ω) (τ n) (τ (n + 1)) := by
        funext t ω
        rcases le_total t (τ n) with hta | hat
        · simp only [intervalSum, min_eq_left hta,
            min_eq_left (hta.trans (hτ (Nat.le_succ n))), sub_self, mul_zero]
        · have hc : S t = S (τ n) := sum_intervalSum_eq_terminal τ hτ H n hat
          rw [hc]
          simp only [intervalSum]
          ring
      have heqRB : (fun t ω => R t ω * intervalSum B (H n) (τ n) (τ (n + 1)) t ω) =
          intervalSum B (fun ω => R (τ n) ω * H n ω) (τ n) (τ (n + 1)) := by
        funext t ω
        rcases le_total t (τ n) with hta | hat
        · simp only [intervalSum, min_eq_left hta,
            min_eq_left (hta.trans (hτ (Nat.le_succ n))), sub_self, mul_zero]
        · have hc : R t = R (τ n) := sum_intervalSum_eq_terminal τ hτ G n hat
          rw [hc]
          simp only [intervalSum]
          ring
      change Martingale (intervalSum C (fun ω => S (τ n) ω * G n ω)
        (τ n) (τ (n + 1))) F P at hSC
      change Martingale (intervalSum B (fun ω => R (τ n) ω * H n ω)
        (τ n) (τ (n + 1))) F P at hRB
      rw [← heqSC] at hSC
      rw [← heqRB] at hRB
      have hdiag := intervalSum_product_martingale hB hC hBC hB2 hC2
        (hτ (Nat.le_succ n)) (hH n) (hG n) (hboundH n) (hboundG n)
      convert ((ih.add hdiag).add hSC).add hRB using 1
      all_goals try with_reducible_and_instances rfl
      funext t ω
      simp only [Finset.sum_range_succ, Pi.add_apply]
      dsimp [S, R]
      ring

theorem stopped_brownian_sum_product_martingale
    (hB : IsPreBrownianReal B P) (hC : IsPreBrownianReal C P)
    (hAdB : StronglyAdapted F B) (hAdC : StronglyAdapted F C)
    (hpair : ∀ s t, s ≤ t → Indep (MeasurableSpace.comap
      (fun ω => (B t ω - B s ω, C t ω - C s ω)) inferInstance) (F s) P)
    (hind : ∀ s t, s ≤ t →
      IndepFun (fun ω => B t ω - B s ω) (fun ω => C t ω - C s ω) P)
    (τ : ℕ → ℝ≥0) (hτ : Monotone τ) (H G : ℕ → Ω → ℝ)
    (hH : ∀ i, StronglyMeasurable[F (τ i)] (H i))
    (hG : ∀ i, StronglyMeasurable[F (τ i)] (G i))
    (K L : ℕ → ℝ) (hboundH : ∀ i, ∀ᵐ ω ∂P, ‖H i ω‖ ≤ K i)
    (hboundG : ∀ i, ∀ᵐ ω ∂P, ‖G i ω‖ ≤ L i) (n : ℕ) :
    Martingale (fun t ω =>
      (∑ i ∈ Finset.range n, intervalSum B (H i) (τ i) (τ (i + 1)) t ω) *
      (∑ i ∈ Finset.range n, intervalSum C (G i) (τ i) (τ (i + 1)) t ω)) F P := by
  let : IsProbabilityMeasure P := hB.isGaussianProcess.isProbabilityMeasure
  have hleft s t (hst : s ≤ t) : Indep (MeasurableSpace.comap
      (fun ω => B t ω - B s ω) inferInstance) (F s) P := by
    apply indep_of_indep_of_le_left (hpair s t hst)
    have hmPair : Measurable[MeasurableSpace.comap
        (fun ω => (B t ω - B s ω, C t ω - C s ω)) inferInstance]
        (fun ω => (B t ω - B s ω, C t ω - C s ω)) :=
      measurable_iff_comap_le.mpr le_rfl
    exact hmPair.fst.comap_le
  have hright s t (hst : s ≤ t) : Indep (MeasurableSpace.comap
      (fun ω => C t ω - C s ω) inferInstance) (F s) P := by
    apply indep_of_indep_of_le_left (hpair s t hst)
    have hmPair : Measurable[MeasurableSpace.comap
        (fun ω => (B t ω - B s ω, C t ω - C s ω)) inferInstance]
        (fun ω => (B t ω - B s ω, C t ω - C s ω)) :=
      measurable_iff_comap_le.mpr le_rfl
    exact hmPair.snd.comap_le
  exact stopped_predictable_sum_product_martingale
    (martingale_of_independent_past hB hAdB hleft)
    (martingale_of_independent_past hC hAdC hright)
    (brownian_product_martingale hB hC hAdB hAdC hpair hind)
    (fun t => (hB.isGaussianProcess.hasGaussianLaw_eval t).memLp_two)
    (fun t => (hC.isGaussianProcess.hasGaussianLaw_eval t).memLp_two)
    τ hτ H G hH hG K L hboundH hboundG n

end Problem367.StoppedBrownianCross

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Stochastic_StoppedBrownianArraySquare
attribute [-instance] _root_.OAI.Problem367.WienerSampler.pathMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace Problem367.StoppedBrownianArraySquare
open StoppedSimpleIntegral BrownianFiltration StoppedBrownianSquare StoppedBrownianCross

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

theorem stopped_brownian_array_square_martingale [IsProbabilityMeasure P]
    (B : ι → ℝ≥0 → Ω → ℝ)
    (hB : ∀ j, IsPreBrownianReal (B j) P)
    (hAd : ∀ j, StronglyAdapted F (B j))
    (hpast : ∀ s t, s ≤ t → Indep (MeasurableSpace.comap
      (fun ω j => B j t ω - B j s ω) inferInstance) (F s) P)
    (hind : ∀ s t, s ≤ t → Pairwise fun j k =>
      IndepFun (fun ω => B j t ω - B j s ω) (fun ω => B k t ω - B k s ω) P)
    (τ : ℕ → ℝ≥0) (hτ : Monotone τ) (H : ι → ℕ → Ω → ℝ)
    (hH : ∀ j i, StronglyMeasurable[F (τ i)] (H j i))
    (K : ι → ℕ → ℝ) (hbound : ∀ j i, ∀ᵐ ω ∂P, ‖H j i ω‖ ≤ K j i)
    (I : Finset ι) (n : ℕ) :
    Martingale (fun t ω =>
      (∑ j ∈ I, ∑ i ∈ Finset.range n,
        intervalSum (B j) (H j i) (τ i) (τ (i + 1)) t ω) ^ 2 -
      ∑ j ∈ I, ∑ i ∈ Finset.range n,
        H j i ω ^ 2 * ((min t (τ (i + 1)) : ℝ) - (min t (τ i) : ℝ))) F P := by
  have hcoord (j : ι) (s t : ℝ≥0) (hst : s ≤ t) : Indep (MeasurableSpace.comap
      (fun ω => B j t ω - B j s ω) inferInstance) (F s) P := by
    apply indep_of_indep_of_le_left (hpast s t hst)
    have hm : Measurable[MeasurableSpace.comap
        (fun ω j => B j t ω - B j s ω) inferInstance]
        (fun ω j => B j t ω - B j s ω) := measurable_iff_comap_le.mpr le_rfl
    exact ((measurable_pi_apply j).comp hm).comap_le
  have hpair (j k : ι) (s t : ℝ≥0) (hst : s ≤ t) : Indep (MeasurableSpace.comap
      (fun ω => (B j t ω - B j s ω, B k t ω - B k s ω)) inferInstance) (F s) P := by
    apply indep_of_indep_of_le_left (hpast s t hst)
    have hm : Measurable[MeasurableSpace.comap
        (fun ω j => B j t ω - B j s ω) inferInstance]
        (fun ω j => B j t ω - B j s ω) := measurable_iff_comap_le.mpr le_rfl
    exact (((measurable_pi_apply j).comp hm).prodMk
      ((measurable_pi_apply k).comp hm)).comap_le
  exact finite_sum_compensated_square_martingale
    (fun j t ω => ∑ i ∈ Finset.range n,
      intervalSum (B j) (H j i) (τ i) (τ (i + 1)) t ω)
    (fun j t ω => ∑ i ∈ Finset.range n,
      H j i ω ^ 2 * ((min t (τ (i + 1)) : ℝ) - (min t (τ i) : ℝ)))
    (fun j => stopped_predictable_sum_square_martingale (hB j) (hAd j) (hcoord j)
      τ hτ (H j) (hH j) (K j) (hbound j) n)
    (fun j k hjk => stopped_brownian_sum_product_martingale (hB j) (hB k)
      (hAd j) (hAd k) (hpair j k) (fun s t hst => hind s t hst hjk)
      τ hτ (H j) (H k) (hH j) (hH k) (K j) (K k) (hbound j) (hbound k) n) I

end Problem367.StoppedBrownianArraySquare

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Brownian_ArrayCompensator
attribute [-instance] _root_.OAI.Problem367.WienerSampler.pathMeasurableSpace _root_.OAI.Problem367.reducedTailFinite _root_.OAI.Problem367.treeBallFinite _root_.OAI.Problem367.treeShellFinite
attribute [-simp] _root_.OAI.Problem367.BrownianIntegralProcess.stoppedUniformSum_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal Topology BigOperators

namespace Problem367.BrownianArrayCompensator

variable {Ω ι : Type*} [mΩ : MeasurableSpace Ω] [Fintype ι]
  {P : Measure Ω} [IsProbabilityMeasure P] {F : Filtration ℝ≥0 mΩ}

theorem compensatedSquare_of_terminal_meanSquare
    {B H : ι → ℝ≥0 → Ω → ℝ} {M : ℝ≥0 → Ω → ℝ}
    (hB : ∀ j, IsPreBrownianReal (B j) P)
    (hAd : ∀ j, StronglyAdapted F (B j))
    (hpast : ∀ s t, s ≤ t → Indep
      (MeasurableSpace.comap (fun ω j => B j t ω - B j s ω) inferInstance) (F s) P)
    (hcross : ∀ s t, s ≤ t → Pairwise fun j k =>
      IndepFun (fun ω => B j t ω - B j s ω) (fun ω => B k t ω - B k s ω) P)
    (hH : ∀ j, StronglyAdapted F (H j))
    (hc : ∀ j, ∀ᵐ ω ∂P, Continuous (fun t => H j t ω))
    (C : ι → ℝ) (hC : ∀ j, 0 ≤ C j)
    (hb : ∀ j, ∀ᵐ ω ∂P, ∀ t, |H j t ω| ≤ C j)
    (hM : Martingale M F P) (hM2 : ∀ t, MemLp (M t) 2 P)
    (hlim : ∀ T, Tendsto (fun n : ℕ => ∫ ω,
      ((∑ j, BrownianGrid.uniformSum (B j) (H j) T n ω) - M T ω) ^ 2 ∂P)
        atTop (𝓝 0)) :
    Martingale (fun t ω => M t ω ^ 2 -
      ∑ j, SelectedCompensator.selected (H j) t t ω) F P := by
  classical
  have hi (j : ι) (s t : ℝ≥0) (hst : s ≤ t) :=
    BrownianArrayFiltration.coordinate_increment_indep_past (hpast s t hst) j
  have hH2 (j : ι) (t : ℝ≥0) : MemLp (H j t) 2 P := by
    apply MemLp.of_bound (hH j).stronglyMeasurable.aestronglyMeasurable (C j)
    filter_upwards [hb j] with ω hω
    simpa only [Real.norm_eq_abs] using hω t
  have hU2 (T : ℝ≥0) (n : ℕ) (j : ι) :
      MemLp (BrownianGrid.uniformSum (B j) (H j) T n) 2 P :=
    BrownianFiltrationGrid.uniformSum_memLp (hB j) (hAd j) (hi j)
      (H j) (hH j) (hH2 j) T n
  have hQ : StronglyAdapted F (fun t ω =>
      ∑ j, SelectedCompensator.selected (H j) t t ω) := by
    intro t
    exact Finset.stronglyMeasurable_fun_sum _ fun j _ =>
      SelectedCompensator.selected_stronglyAdapted (hH j) t t
  refine ⟨fun t => ((hM.stronglyAdapted t).pow 2).sub (hQ t), ?_⟩
  intro s T hsT
  let U (n : ℕ) : Ω → ℝ := fun ω =>
    ∑ j, BrownianGrid.uniformSum (B j) (H j) T n ω
  let X (n : ℕ) (t : ℝ≥0) (ω : Ω) : ℝ :=
    ∑ j, BrownianIntegralProcess.stoppedUniformSum (B j) (H j) T n t ω
  let A (n : ℕ) (t : ℝ≥0) (ω : Ω) : ℝ :=
    ∑ j, SelectedCompensator.squareSum (H j) T n t ω
  let Y (t : ℝ≥0) : Ω → ℝ := P[M T | F t]
  let Q (t : ℝ≥0) (ω : Ω) : ℝ :=
    ∑ j, SelectedCompensator.selected (H j) T t ω
  have hu2 (n : ℕ) : MemLp (U n) 2 P :=
    memLp_finsetSum _ fun j _ => hU2 T n j
  have hx2 (n : ℕ) (t : ℝ≥0) : MemLp (X n t) 2 P := by
    apply memLp_finsetSum
    intro j hj
    exact BrownianFiltration.stopped_predictable_sum_memLp_two (hB j) (hi j)
      (BrownianGrid.uniformGrid T n) (BrownianGrid.uniformGrid_mono T n)
      (fun i => H j (BrownianGrid.uniformGrid T n i)) (fun i => hH j _)
      (fun i => hH2 j _) (Finset.range n) t
  have ha (n : ℕ) (t : ℝ≥0) : Integrable (A n t) P :=
    integrable_finsetSum _ fun j _ =>
      (SelectedCompensator.squareSum_memLp (hH j) (hC j) (hb j) T t n 1).integrable le_rfl
  have hq (t : ℝ≥0) : Integrable (Q t) P :=
    integrable_finsetSum _ fun j _ =>
      (SelectedCompensator.selected_memLp (hH j) (hc j) (hC j) (hb j) T t 1).integrable le_rfl
  have hy2 (t : ℝ≥0) : MemLp (Y t) 2 P := (hM2 T).condExp (by norm_num)
  have hce (n : ℕ) (t : ℝ≥0) : P[U n | F t] =ᵐ[P] X n t := by
    have hsum := condExp_finsetSum (s := Finset.univ)
      (fun j _ => (hU2 T n j).integrable (by norm_num)) (F t)
    have heach : ∀ᵐ ω ∂P, ∀ j,
        P[BrownianGrid.uniformSum (B j) (H j) T n | F t] ω =
          BrownianIntegralProcess.stoppedUniformSum (B j) (H j) T n t ω :=
      ae_all_iff.mpr fun j => BrownianIntegralProcess.stoppedUniformSum_eq_condExp
        (hB j) (hAd j) (hi j) (hH j) (hb j) T n t
    have hsumFun : (∑ j, BrownianGrid.uniformSum (B j) (H j) T n) = U n := by
      funext ω
      simp only [U, Finset.sum_apply]
    rw [hsumFun] at hsum
    filter_upwards [hsum, heach] with ω hω he
    simp only [Finset.sum_apply] at hω
    exact hω.trans (Finset.sum_congr rfl (fun j _ => he j))
  have hxlim (t : ℝ≥0) : Tendsto (fun n => ∫ ω,
      (X n t ω - Y t ω) ^ 2 ∂P) atTop (𝓝 0) := by
    apply squeeze_zero (fun n => integral_nonneg (fun ω => sq_nonneg _)) ?_ (hlim T)
    intro n
    calc
      _ = ∫ ω, (P[U n | F t] ω - P[M T | F t] ω) ^ 2 ∂P := by
        apply integral_congr_ae
        filter_upwards [hce n t] with ω hω
        exact congrArg (fun z => (z - Y t ω) ^ 2) hω.symm
      _ ≤ _ := BrownianIntegralProcess.meanSquare_condExp_sub_le (F t) (hu2 n) (hM2 T)
  have hfinite (n : ℕ) : Martingale (fun t ω => (X n t ω) ^ 2 - A n t ω) F P := by
    have hh := StoppedBrownianArraySquare.stopped_brownian_array_square_martingale
      B hB hAd hpast hcross (BrownianGrid.uniformGrid T n) (BrownianGrid.uniformGrid_mono T n)
      (fun j i => H j (BrownianGrid.uniformGrid T n i)) (fun j i => hH j _)
      (fun j _ => C j)
      (fun j i => (hb j).mono (fun ω hω => by simpa only [Real.norm_eq_abs] using hω _))
      Finset.univ n
    simpa only [X, A, BrownianIntegralProcess.stoppedUniformSum,
      SelectedCompensator.squareSum, mul_comm] using hh
  have halim (t : ℝ≥0) : Tendsto (fun n => eLpNorm (A n t - Q t) 1 P) atTop (𝓝 0) := by
    have hl := tendsto_finsetSum Finset.univ (fun j _ =>
      SelectedCompensator.tendsto_squareSum_L1_selected
        (fun r => (hH j).stronglyMeasurable.aestronglyMeasurable)
        (hc j) (hC j) (hb j) T t)
    simp only [Finset.sum_const_zero] at hl
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hl (fun _ => bot_le)
    intro n
    change eLpNorm (A n t - Q t) 1 P ≤ ∑ j,
      eLpNorm (SelectedCompensator.squareSum (H j) T n t - SelectedCompensator.selected (H j) T t) 1 P
    have heq : A n t - Q t = ∑ j,
        (SelectedCompensator.squareSum (H j) T n t - SelectedCompensator.selected (H j) T t) := by
      funext ω
      simp only [A, Q, Pi.sub_apply, Finset.sum_apply, Finset.sum_sub_distrib]
    rw [heq]
    exact eLpNorm_sum_le (hfs := fun j _ => (((SelectedCompensator.squareSum_stronglyAdapted (hH j) T n t).mono (F.le t)).sub ((SelectedCompensator.selected_stronglyAdapted (hH j) T t).mono (F.le t))).aestronglyMeasurable) le_rfl
  have hcomp := CompensatedSquareLimit.martingale_compensatedSquare_of_limits
    hx2 ha hfinite (martingale_condExp (M T) F P).stronglyAdapted hy2
    (fun t => Finset.stronglyMeasurable_fun_sum _ fun j _ =>
      SelectedCompensator.selected_stronglyAdapted (hH j) T t) hq
    (fun t => CompensatedSquareLimit.tendsto_eLpNorm_two_of_meanSquare
      (fun n => hx2 n t) (hy2 t) (hxlim t)) halim
  have heq (r : ℝ≥0) (hr : r ≤ T) :
      (fun ω => (Y r ω) ^ 2 - Q r ω) =ᵐ[P]
        (fun ω => M r ω ^ 2 - ∑ j, SelectedCompensator.selected (H j) r r ω) := by
    have hcAll : ∀ᵐ ω ∂P, ∀ j, Continuous (fun t => H j t ω) := ae_all_iff.mpr hc
    filter_upwards [hM.condExp_ae_eq hr, hcAll] with ω hω hcω
    change (P[M T | F r] ω) ^ 2 - _ = _
    rw [hω]
    congr 1
    apply Finset.sum_congr rfl
    intro j hj
    simp only [SelectedCompensator.selected_eq_integral_of_continuous (hcω j),
      min_self, min_eq_left (show (r : ℝ) ≤ T from hr)]
  exact (condExp_congr_ae (heq T le_rfl).symm).trans
    ((hcomp.condExp_ae_eq hsT).trans (heq s hsT))

end Problem367.BrownianArrayCompensator

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

end Fields

end Problem367.FinitePosterior

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Posterior_GaussianTimeDerivative
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

section Posterior

variable {S : Type*} [Fintype S] [Nonempty S]

theorem continuous_fieldCovariance (energy : S → ℝ) (spin : S → V → ℝ)
    (observable : S → ℝ) (v : V) :
    Continuous (fun x => fieldCovariance energy spin observable x v) := by
  exact (continuous_fieldMean energy spin (fun s => observable s * spin s v)).sub
    ((continuous_fieldMean energy spin observable).mul
      (continuous_fieldMean energy spin (fun s => spin s v)))

end Posterior

end Problem367.FinitePosterior

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Stochastic_FiniteIsingBrownianEnergy
attribute [-instance] _root_.OAI.Problem367.WienerSampler.pathMeasurableSpace _root_.OAI.Problem367.reducedTailFintype _root_.OAI.Problem367.treeBallFintype _root_.OAI.Problem367.treeShellFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal

namespace Problem367

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

local instance finiteIsingBrownianHistoryNonemptySpin_re97626_1 : Nonempty IsingSpin := ⟨.neg⟩
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
-- module Solutions.Q243_FreeIsing.FreeIsing_Stochastic_FiniteIsingFilteringIntegral
attribute [-instance] _root_.OAI.Problem367.IsingConditionalCopyBounds.graphLaw_isProbabilityMeasure _root_.OAI.Problem367.IsingObservationFactor.copies_probability _root_.OAI.Problem367.IsingObservationFactor.kernel_markov _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_observationLaw_probability _root_.OAI.Problem367.IsingObservationInnovation.observationLaw_probability _root_.OAI.Problem367.TreeKoopman.labelProbability _root_.OAI.Problem367.freeIsingMeasure_probability
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

theorem tendsto_uniformSum_row_meanSquare
    {beta : ℝ} {μ : Measure (TreeVertex d → IsingSpin)}
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ)
    (ν : TreeVertex d → Measure Ω) {B : TreeVertex d → ℝ≥0 → Ω → ℝ}
    (hB : ∀ i, IsPreBrownianReal (B i) (ν i))
    (hmB : ∀ i t, Measurable (B i t))
    (hcB : ∀ i omega, Continuous (fun t => B i t omega))
    (D : Finset (TreeVertex d)) (hD : ConnectedFinset D) (v : D) (T : ℝ≥0) :
    Tendsto (fun n : ℕ => ∫ p,
      ((∑ u : D, BrownianGrid.uniformSum (innovation beta D u B)
        (covariance beta D v u B) T n p) - mean beta D v B T p) ^ 2
        ∂μ.prod (Measure.infinitePi ν)) atTop (𝓝 0) := by
  classical
  let : IsProbabilityMeasure μ := hμ.isProbabilityMeasure
  have (i : TreeVertex d) : IsProbabilityMeasure (ν i) :=
    (hB i).isGaussianProcess.isProbabilityMeasure
  let P := μ.prod (Measure.infinitePi ν)
  obtain ⟨I, hI, _, _, _, _, happrox, heq⟩ :=
    exists_innovation_integral_representation hμ ν hB hmB hcB D hD v T
  have hS (u : D) (n : ℕ) : MemLp
      (BrownianGrid.uniformSum (innovation beta D u B) (covariance beta D v u B) T n) 2 P :=
    BrownianFiltrationGrid.uniformSum_memLp
      (innovation_isBrownianReal hμ ν hB hmB hcB D hD u).toIsPreBrownianReal
      (innovation_stronglyAdapted beta D u B hmB hcB)
      (fun s t hst => BrownianArrayFiltration.coordinate_increment_indep_past
        (innovation_increment_indep_filtration hμ ν hB hmB hcB D hD s t hst) u)
      _ (stronglyAdapted_covariance beta D v u B hmB)
      (fun t => memLp_covariance P beta D v u B hmB t 2) T n
  have hl := FilteringRepresentationClosure.tendsto_integral_sq_fintype_sum_error hI hS happrox
  apply hl.congr'
  apply Eventually.of_forall
  intro n
  apply integral_congr_ae
  filter_upwards [heq] with p hp
  rw [hp]

theorem mean_martingale
    {beta : ℝ} {μ : Measure (TreeVertex d → IsingSpin)}
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ)
    (ν : TreeVertex d → Measure Ω) {B : TreeVertex d → ℝ≥0 → Ω → ℝ}
    (hB : ∀ i, IsPreBrownianReal (B i) (ν i))
    (hmB : ∀ i t, Measurable (B i t))
    (D : Finset (TreeVertex d)) (hD : ConnectedFinset D) (v : D) :
    Martingale (mean beta D v B) (observationFiltration B hmB D)
      (μ.prod (Measure.infinitePi ν)) := by
  let : IsProbabilityMeasure μ := hμ.isProbabilityMeasure
  have (i : TreeVertex d) : IsProbabilityMeasure (ν i) :=
    (hB i).isGaussianProcess.isProbabilityMeasure
  exact (martingale_condExp (fun p : State d Ω => signal p.1 v)
    (observationFiltration B hmB D) (μ.prod (Measure.infinitePi ν))).congr
      (stronglyAdapted_mean beta D v B hmB)
      (fun t => (mean_eq_condExp hμ ν hB hmB D hD v t).symm)

end Problem367.FiniteIsingFiltering

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Estimates_FiniteIsingCompensatedSquare
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

omit [MeasurableSpace Ω] in
theorem quadraticCompensator_eq_selected
    (beta : ℝ) (D : Finset (TreeVertex d)) (v : D)
    (B : TreeVertex d → ℝ≥0 → Ω → ℝ)
    (hcB : ∀ i omega, Continuous (fun t => B i t omega)) (t : ℝ≥0) (p : State d Ω) :
    quadraticCompensator beta D v B t p =
      ∑ u : D, SelectedCompensator.selected (covariance beta D v u B) t t p := by
  apply Finset.sum_congr rfl
  intro u hu
  simpa only [min_self] using
    (SelectedCompensator.selected_eq_integral_of_continuous
      (continuous_covariance beta D v u B hcB p) t t).symm

theorem mean_compensatedSquare_martingale_oai
    {beta : ℝ} {μ : Measure (TreeVertex d → IsingSpin)}
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ)
    (ν : TreeVertex d → Measure Ω) {B : TreeVertex d → ℝ≥0 → Ω → ℝ}
    (hB : ∀ i, IsPreBrownianReal (B i) (ν i))
    (hmB : ∀ i t, Measurable (B i t))
    (hcB : ∀ i omega, Continuous (fun t => B i t omega))
    (D : Finset (TreeVertex d)) (hD : ConnectedFinset D) (v : D) :
    Martingale (fun t p => mean beta D v B t p ^ 2 - quadraticCompensator beta D v B t p)
      (observationFiltration B hmB D) (μ.prod (Measure.infinitePi ν)) := by
  classical
  let : IsProbabilityMeasure μ := hμ.isProbabilityMeasure
  have (i : TreeVertex d) : IsProbabilityMeasure (ν i) :=
    (hB i).isGaussianProcess.isProbabilityMeasure
  have hind (s t : ℝ≥0) (hst : s ≤ t) : Pairwise fun u w : D =>
      IndepFun (fun p => innovation beta D u B t p - innovation beta D u B s p)
        (fun p => innovation beta D w B t p - innovation beta D w B s p)
        (μ.prod (Measure.infinitePi ν)) := by
    intro u w huw
    exact (innovation_increment_law_and_indep hμ ν hB hmB hcB D hD s t hst
      (Y := fun _ => ()) measurable_const).2.1.indepFun huw
  have h := BrownianArrayCompensator.compensatedSquare_of_terminal_meanSquare
    (fun u : D => (innovation_isBrownianReal hμ ν hB hmB hcB D hD u).toIsPreBrownianReal)
    (fun u => innovation_stronglyAdapted beta D u B hmB hcB)
    (innovation_increment_indep_filtration hμ ν hB hmB hcB D hD) hind
    (fun u => stronglyAdapted_covariance beta D v u B hmB)
    (fun u => Eventually.of_forall (continuous_covariance beta D v u B hcB))
    (fun _ => 2) (fun _ => by norm_num)
    (fun u => Eventually.of_forall fun p t => abs_covariance_le_two beta D v u B t p)
    (mean_martingale hμ ν hB hmB D hD v)
    (fun t => memLp_mean (μ.prod (Measure.infinitePi ν)) beta D v B hmB t 2)
    (tendsto_uniformSum_row_meanSquare hμ ν hB hmB hcB D hD v)
  convert h using 1
  all_goals try with_reducible_and_instances rfl
  funext t p
  rw [quadraticCompensator_eq_selected beta D v B hcB t p]

end Problem367.FiniteIsingFiltering

end

end OAI
end

theorem solution.{u_1} : type_of% @OAI.Problem367.FiniteIsingFiltering.mean_compensatedSquare_martingale_oai.{u_1} := @OAI.Problem367.FiniteIsingFiltering.mean_compensatedSquare_martingale_oai.{u_1}
