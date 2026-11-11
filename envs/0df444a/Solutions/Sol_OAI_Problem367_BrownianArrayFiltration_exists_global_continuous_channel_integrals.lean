-- Prove2me | solution 1 for OAI.Problem367.BrownianArrayFiltration.exists_global_continuous_channel_integrals
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T01:39:33.794222+00:00
-- url     : https://prove2.me/submissions/bd63b695-e598-4f3c-90bb-1e63d20b651d

import Mathlib
import Definitions.Def_Q243FI001
import Theorems.Thm_OAI_Problem367_BrownianIntegralProcess_exists_global_continuous_uniform_integral

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Brownian_FiltrationIntegral
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
-- module Solutions.Q243_FreeIsing.FreeIsing_Brownian_ArrayFiltrationIntegral
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

end Problem367.StoppedSimpleIntegral

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Stochastic_StoppedBrownianIntegral
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

end Problem367.StoppedBrownianSquare

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Stochastic_StoppedBrownianCross
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
-- module Solutions.Q243_FreeIsing.FreeIsing_Brownian_ContinuousCross
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal Topology

namespace Problem367.BrownianContinuousCross

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}

theorem tendsto_eLpNorm_mul_sub {N : Type*} {l : Filter N}
    {f g : N → Ω → ℝ} {u v : Ω → ℝ}
    (hf : ∀ n, MemLp (f n) 2 P) (hg : ∀ n, MemLp (g n) 2 P)
    (hu : MemLp u 2 P) (hv : MemLp v 2 P)
    (hfu : Tendsto (fun n => eLpNorm (f n - u) 2 P) l (𝓝 0))
    (hgv : Tendsto (fun n => eLpNorm (g n - v) 2 P) l (𝓝 0)) :
    Tendsto (fun n => eLpNorm (f n * g n - u * v) 1 P) l (𝓝 0) := by
  let M : Lp ℝ 2 P →L[ℝ] Lp ℝ 2 P →L[ℝ] Lp ℝ 1 P :=
    ContinuousLinearMap.holderL P 2 2 1 (ContinuousLinearMap.mul ℝ ℝ)
  have hmul {a b : Ω → ℝ} (ha : MemLp a 2 P) (hb : MemLp b 2 P) :
      M (ha.toLp a) (hb.toLp b) = (memLp_one_iff_integrable.mpr (ha.integrable_mul hb)).toLp (a * b) := by
    apply Lp.ext
    have hm := (ContinuousLinearMap.mul ℝ ℝ).coeFn_holder (r := 1)
      (ha.toLp a) (hb.toLp b)
    filter_upwards [hm, ha.coeFn_toLp, hb.coeFn_toLp,
      (memLp_one_iff_integrable.mpr (ha.integrable_mul hb)).coeFn_toLp] with ω hm hωa hωb hab
    change M (ha.toLp a) (hb.toLp b) ω = (ha.toLp a) ω * (hb.toLp b) ω at hm
    rw [hωa, hωb] at hm
    exact hm.trans hab.symm
  have hfLp := (Lp.tendsto_Lp_iff_tendsto_eLpNorm'' f hf u hu).mpr hfu
  have hgLp := (Lp.tendsto_Lp_iff_tendsto_eLpNorm'' g hg v hv).mpr hgv
  have h := (M.continuous₂.tendsto (hu.toLp u, hv.toLp v)).comp
    (hfLp.prodMk_nhds hgLp)
  change Tendsto (fun n => M ((hf n).toLp (f n)) ((hg n).toLp (g n))) l
    (𝓝 (M (hu.toLp u) (hv.toLp v))) at h
  simp only [hmul] at h
  exact (Lp.tendsto_Lp_iff_tendsto_eLpNorm'' (fun n => f n * g n)
    (fun n => (memLp_one_iff_integrable.mpr ((hf n).integrable_mul (hg n)))) (u * v)
    (memLp_one_iff_integrable.mpr (hu.integrable_mul hv))).mp h

theorem condExp_ae_eq_of_L1_limits
    {ι N : Type*} [LinearOrder ι] [IsFiniteMeasure P]
    {F : Filtration ι mΩ} {l : Filter N} [l.NeBot]
    {X : N → ι → Ω → ℝ} (hX : ∀ n, Martingale (X n) F P)
    {s t : ι} (hst : s ≤ t) {u v : Ω → ℝ}
    (hu : StronglyMeasurable[F s] u) (hui : Integrable u P) (hvi : Integrable v P)
    (hs : Tendsto (fun n => eLpNorm (X n s - u) 1 P) l (𝓝 0))
    (ht : Tendsto (fun n => eLpNorm (X n t - v) 1 P) l (𝓝 0)) :
    P[v | F s] =ᵐ[P] u := by
  apply (ae_eq_condExp_of_forall_setIntegral_eq (F.le s) hvi
    (fun A hA _ => hui.integrableOn) ?_ hu.aestronglyMeasurable).symm
  intro A hA hAfin
  have hs' := tendsto_setIntegral_of_L1' u hui.aestronglyMeasurable
    (Eventually.of_forall (fun n => (hX n).integrable s)) hs A
  have ht' := tendsto_setIntegral_of_L1' v hvi.aestronglyMeasurable
    (Eventually.of_forall (fun n => (hX n).integrable t)) ht A
  have heq : (fun n => ∫ ω in A, X n s ω ∂P) =
      (fun n => ∫ ω in A, X n t ω ∂P) :=
    funext fun n => (hX n).setIntegral_eq hst hA
  rw [heq] at hs'
  exact tendsto_nhds_unique hs' ht'

theorem global_uniform_limits_product_martingale
    {B C H G I J : ℝ≥0 → Ω → ℝ} {F : Filtration ℝ≥0 mΩ}
    (hB : IsPreBrownianReal B P) (hC : IsPreBrownianReal C P)
    (hAdB : StronglyAdapted F B) (hAdC : StronglyAdapted F C)
    (hpair : ∀ s t, s ≤ t → Indep (MeasurableSpace.comap
      (fun ω => (B t ω - B s ω, C t ω - C s ω)) inferInstance) (F s) P)
    (hind : ∀ s t, s ≤ t →
      IndepFun (fun ω => B t ω - B s ω) (fun ω => C t ω - C s ω) P)
    (hH : StronglyAdapted F H) (hG : StronglyAdapted F G)
    {K L : ℝ} (hboundH : ∀ᵐ ω ∂P, ∀ t, ‖H t ω‖ ≤ K)
    (hboundG : ∀ᵐ ω ∂P, ∀ t, ‖G t ω‖ ≤ L)
    (hI : StronglyAdapted F I) (hJ : StronglyAdapted F J)
    (hI2 : ∀ t, MemLp (I t) 2 P) (hJ2 : ∀ t, MemLp (J t) 2 P)
    (hlimI : ∀ (N : ℕ), 0 < N → ∀ t ≤ (N : ℝ≥0),
      Tendsto (fun n => ∫ ω,
        (BrownianIntegralProcess.stoppedUniformSum B H N n t ω - I t ω) ^ 2 ∂P)
        atTop (𝓝 0))
    (hlimJ : ∀ (N : ℕ), 0 < N → ∀ t ≤ (N : ℝ≥0),
      Tendsto (fun n => ∫ ω,
        (BrownianIntegralProcess.stoppedUniformSum C G N n t ω - J t ω) ^ 2 ∂P)
        atTop (𝓝 0)) :
    Martingale (fun t ω => I t ω * J t ω) F P := by
  let : IsProbabilityMeasure P := hB.isGaussianProcess.isProbabilityMeasure
  have hB2 (t : ℝ≥0) := (hB.isGaussianProcess.hasGaussianLaw_eval t).memLp_two
  have hC2 (t : ℝ≥0) := (hC.isGaussianProcess.hasGaussianLaw_eval t).memLp_two
  have hBH (t : ℝ≥0) : ∀ᵐ ω ∂P, ‖H t ω‖ ≤ K := hboundH.mono fun ω hω => hω t
  have hCG (t : ℝ≥0) : ∀ᵐ ω ∂P, ‖G t ω‖ ≤ L := hboundG.mono fun ω hω => hω t
  refine ⟨fun t => (hI t).mul (hJ t), ?_⟩
  intro s t hst
  obtain ⟨N, hN⟩ := exists_nat_ge t
  have htN : t ≤ ((N + 1 : ℕ) : ℝ≥0) :=
    hN.trans (by exact_mod_cast Nat.le_succ N)
  let X := fun n => BrownianIntegralProcess.stoppedUniformSum B H ((N + 1 : ℕ) : ℝ≥0) n
  let Y := fun n => BrownianIntegralProcess.stoppedUniformSum C G ((N + 1 : ℕ) : ℝ≥0) n
  have hX2 (n : ℕ) (r : ℝ≥0) : MemLp (X n r) 2 P := by
    apply memLp_finsetSum (Finset.range n)
    intro i hi
    exact StoppedBrownianCross.intervalSum_memLp_two_of_bounded hB2
      (hH _) (hBH _) r
  have hY2 (n : ℕ) (r : ℝ≥0) : MemLp (Y n r) 2 P := by
    apply memLp_finsetSum (Finset.range n)
    intro i hi
    exact StoppedBrownianCross.intervalSum_memLp_two_of_bounded hC2
      (hG _) (hCG _) r
  have hM (n : ℕ) : Martingale (fun r ω => X n r ω * Y n r ω) F P :=
    StoppedBrownianCross.stopped_brownian_sum_product_martingale hB hC hAdB hAdC
      hpair hind (BrownianGrid.uniformGrid ((N + 1 : ℕ) : ℝ≥0) n) (BrownianGrid.uniformGrid_mono _ _)
      (fun i => H (BrownianGrid.uniformGrid ((N + 1 : ℕ) : ℝ≥0) n i))
      (fun i => G (BrownianGrid.uniformGrid ((N + 1 : ℕ) : ℝ≥0) n i))
      (fun i => hH _) (fun i => hG _) (fun _ => K) (fun _ => L)
      (fun i => hBH _) (fun i => hCG _) n
  have hprod (r : ℝ≥0) (hr : r ≤ ((N + 1 : ℕ) : ℝ≥0)) :
      Tendsto (fun n => eLpNorm (X n r * Y n r - I r * J r) 1 P) atTop (𝓝 0) :=
    tendsto_eLpNorm_mul_sub (fun n => hX2 n r) (fun n => hY2 n r) (hI2 r) (hJ2 r)
      (CompensatedSquareLimit.tendsto_eLpNorm_two_of_meanSquare
        (fun n => hX2 n r) (hI2 r) (hlimI (N + 1) (Nat.succ_pos N) r hr))
      (CompensatedSquareLimit.tendsto_eLpNorm_two_of_meanSquare
        (fun n => hY2 n r) (hJ2 r) (hlimJ (N + 1) (Nat.succ_pos N) r hr))
  exact condExp_ae_eq_of_L1_limits hM hst ((hI s).mul (hJ s))
    ((hI2 s).integrable_mul (hJ2 s)) ((hI2 t).integrable_mul (hJ2 t))
    (hprod s (hst.trans htN)) (hprod t htN)

end Problem367.BrownianContinuousCross

namespace Problem367.BrownianArrayFiltration

variable {Ω ι : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
  {B H I : ι → ℝ≥0 → Ω → ℝ} {F : Filtration ℝ≥0 mΩ}

theorem global_uniform_limits_pairwise_product_martingale
    (hB : ∀ a, IsPreBrownianReal (B a) P)
    (hAd : ∀ a, StronglyAdapted F (B a))
    (hpast : ∀ s t, s ≤ t → Indep (MeasurableSpace.comap
      (fun ω a => B a t ω - B a s ω) inferInstance) (F s) P)
    (hind : ∀ s t, s ≤ t → Pairwise fun a b =>
      IndepFun (fun ω => B a t ω - B a s ω) (fun ω => B b t ω - B b s ω) P)
    (hH : ∀ a, StronglyAdapted F (H a))
    {K : ι → ℝ} (hbound : ∀ a, ∀ᵐ ω ∂P, ∀ t, ‖H a t ω‖ ≤ K a)
    (hI : ∀ a, StronglyAdapted F (I a))
    (hI2 : ∀ a t, MemLp (I a t) 2 P)
    (hlim : ∀ a (N : ℕ), 0 < N → ∀ t ≤ (N : ℝ≥0),
      Tendsto (fun n => ∫ ω,
        (BrownianIntegralProcess.stoppedUniformSum (B a) (H a) N n t ω - I a t ω) ^ 2 ∂P)
        atTop (𝓝 0)) :
    Pairwise fun a b => Martingale (fun t ω => I a t ω * I b t ω) F P := by
  intro a b hab
  apply BrownianContinuousCross.global_uniform_limits_product_martingale
    (hB a) (hB b) (hAd a) (hAd b) ?_ (fun s t hst => hind s t hst hab)
    (hH a) (hH b) (hbound a) (hbound b) (hI a) (hI b) (hI2 a) (hI2 b)
    (hlim a) (hlim b)
  intro s t hst
  apply indep_of_indep_of_le_left (hpast s t hst)
  have hm : Measurable[MeasurableSpace.comap
      (fun ω c => B c t ω - B c s ω) inferInstance]
      (fun ω c => B c t ω - B c s ω) := measurable_iff_comap_le.mpr le_rfl
  exact (((measurable_pi_apply a).comp hm).prodMk
    ((measurable_pi_apply b).comp hm)).comap_le

theorem exists_global_continuous_channel_integrals_oai
    (hB : ∀ a, IsPreBrownianReal (B a) P)
    (hAd : ∀ a, StronglyAdapted F (B a))
    (hpast : ∀ s t, s ≤ t → Indep (MeasurableSpace.comap
      (fun ω a => B a t ω - B a s ω) inferInstance) (F s) P)
    (hind : ∀ s t, s ≤ t → Pairwise fun a b =>
      IndepFun (fun ω => B a t ω - B a s ω) (fun ω => B b t ω - B b s ω) P)
    (hBc : ∀ a, ∀ᵐ ω ∂P, Continuous (fun t => B a t ω))
    (hH : ∀ a, StronglyAdapted F (H a))
    (hHc : ∀ a, ∀ᵐ ω ∂P, Continuous (fun t => H a t ω))
    {K : ι → ℝ} (hK : ∀ a, 0 ≤ K a)
    (hbound : ∀ a, ∀ᵐ ω ∂P, ∀ t, |H a t ω| ≤ K a) :
    ∃ I : ι → ℝ≥0 → Ω → ℝ,
      (∀ a, IsStronglyPredictable F (I a)) ∧
      (∀ a, Martingale (I a) F P) ∧
      (∀ a, ∀ᵐ ω ∂P, Continuous (fun t => I a t ω)) ∧
      (∀ a t, MemLp (I a t) 2 P) ∧
      (∀ a, I a 0 =ᵐ[P] 0) ∧
      (∀ a t, (∫ ω, I a t ω ∂P) = 0) ∧
      (∀ a t, (∫ ω, (I a t ω) ^ 2 ∂P) =
        ∫ s in (0 : ℝ)..(t : ℝ), ∫ ω, (H a s.toNNReal ω) ^ 2 ∂P) ∧
      (∀ a (N : ℕ), 0 < N → ∀ t ≤ (N : ℝ≥0),
        Tendsto (fun n => ∫ ω,
          (BrownianIntegralProcess.stoppedUniformSum (B a) (H a) N n t ω - I a t ω) ^ 2 ∂P)
          atTop (𝓝 0)) ∧
      (Pairwise fun a b => Martingale (fun t ω => I a t ω * I b t ω) F P) := by
  have hex (a : ι) := BrownianIntegralProcess.exists_global_continuous_uniform_integral
    (hB a) (hAd a)
    (fun s t hst => coordinate_increment_indep_past (hpast s t hst) a)
    (hBc a) (hH a) (hHc a) (hK a) (hbound a)
  choose I hIp hIM hIc hI2 hIz hImean hIiso hIlim using hex
  refine ⟨I, hIp, hIM, hIc, hI2, hIz, hImean, hIiso, hIlim, ?_⟩
  exact global_uniform_limits_pairwise_product_martingale hB hAd hpast hind hH
    (by simpa only [Real.norm_eq_abs] using hbound)
    (fun a => (hIM a).stronglyAdapted) hI2 hIlim

end Problem367.BrownianArrayFiltration

end

end OAI
end

theorem solution.{u_1, u_2} : type_of% @OAI.Problem367.BrownianArrayFiltration.exists_global_continuous_channel_integrals_oai.{u_1, u_2} := @OAI.Problem367.BrownianArrayFiltration.exists_global_continuous_channel_integrals_oai.{u_1, u_2}
