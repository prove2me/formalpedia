-- Prove2me | solution 1 for OAI.EntropyRateDimension.ErgodicAux.ae_tendsto_average
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-18T18:33:21.458561+00:00
-- url     : https://prove2.me/submissions/474bcc07-20a5-4b6d-8396-81cd4cc420bf

import Mathlib
import Definitions.Def_OAIQWERD000

section
-- module Solutions.OAIQW_EntropyRateDimension.ErgodicAverages
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uα

section
open scoped BigOperators ENNReal
open MeasureTheory
open MeasureTheory Metric Set Filter
open scoped Topology ENNReal
open MeasureTheory Filter Set ProbabilityTheory
open scoped Topology
open MeasureTheory Metric Set Filter
open scoped ENNReal Topology
open MeasureTheory Filter Set
open scoped Topology BigOperators

namespace EntropyRateDimension
namespace ErgodicAux

variable {α : Type uα}

theorem maxSum_nonneg (T : α → α) (f : α → ℝ) (n : ℕ) (x : α) :
    0 ≤ maxSum T f n x := by
  cases n with
  | zero => exact le_rfl
  | succ n => exact le_max_left _ _

theorem maxSum_mono (T : α → α) (f : α → ℝ) (x : α) :
    Monotone (fun n => maxSum T f n x) := by
  apply monotone_nat_of_le_succ
  intro n
  induction n generalizing x with
  | zero => exact maxSum_nonneg T f 1 x
  | succ n ih => exact max_le_max_left _ (by linarith [ih (T x)])

theorem birkhoffSum_le_maxSum (T : α → α) (f : α → ℝ) (n : ℕ) (x : α) :
    birkhoffSum T f n x ≤ maxSum T f n x := by
  induction n generalizing x with
  | zero => simp
  | succ n ih =>
    rw [birkhoffSum_succ', maxSum_succ]
    exact (show f x + birkhoffSum T f n (T x) ≤ f x + maxSum T f n (T x) by
      linarith [ih (T x)]).trans (le_max_right _ _)

variable [MeasurableSpace α] {μ : Measure α}

theorem maxSum_measurable {T : α → α} {f : α → ℝ}
    (hT : Measurable T) (hf : Measurable f) (n : ℕ) :
    Measurable (maxSum T f n) := by
  induction n with
  | zero => exact measurable_const
  | succ n ih => exact measurable_const.max (hf.add (ih.comp hT))

theorem maxSum_integrable {T : α → α} {f : α → ℝ}
    (hT : MeasurePreserving T μ μ) (hf : Integrable f μ) (n : ℕ) :
    Integrable (maxSum T f n) μ := by
  induction n with
  | zero => exact integrable_zero α ℝ μ
  | succ n ih =>
    exact (integrable_zero α ℝ μ).sup (hf.add (hT.integrable_comp_of_integrable ih))

theorem integral_comp_preserving {T : α → α} {f : α → ℝ}
    (hT : MeasurePreserving T μ μ) (hf : Integrable f μ) :
    (∫ x, f (T x) ∂μ) = ∫ x, f x ∂μ := by
  have hm : AEStronglyMeasurable f (μ.map T) := by rw [hT.map_eq]; exact hf.1
  calc
    (∫ x, f (T x) ∂μ) = ∫ x, f x ∂μ.map T :=
      (integral_map hT.measurable.aemeasurable hm).symm
    _ = ∫ x, f x ∂μ := by rw [hT.map_eq]

theorem hopf_finite {T : α → α} {f : α → ℝ}
    (hT : MeasurePreserving T μ μ) (hfm : Measurable f) (hf : Integrable f μ)
    (n : ℕ) :
    0 ≤ ∫ x in {x | 0 < maxSum T f n x}, f x ∂μ := by
  cases n with
  | zero => simp
  | succ n =>
    let E := {x | 0 < maxSum T f (n+1) x}
    have hE : MeasurableSet E := measurableSet_lt measurable_const
      (maxSum_measurable hT.measurable hfm _)
    have hpoint : ∀ x, maxSum T f (n+1) x - maxSum T f n (T x) ≤ E.indicator f x := by
      intro x
      by_cases hx : x ∈ E
      · rw [Set.indicator_of_mem hx]
        have hp : 0 < maxSum T f (n+1) x := hx
        rw [maxSum_succ, lt_max_iff] at hp
        have hn : 0 ≤ f x + maxSum T f n (T x) := (hp.resolve_left (lt_irrefl _)).le
        rw [maxSum_succ, max_eq_right hn]
        linarith
      · rw [Set.indicator_of_notMem hx]
        have hz : maxSum T f (n+1) x = 0 := le_antisymm (not_lt.mp hx)
          (maxSum_nonneg T f _ x)
        rw [hz]
        linarith [maxSum_nonneg T f n (T x)]
    have hin := maxSum_integrable hT hf n
    have his := maxSum_integrable hT hf (n+1)
    have hmono : (∫ x, maxSum T f n x ∂μ) ≤ ∫ x, maxSum T f (n+1) x ∂μ :=
      integral_mono hin his (fun x => maxSum_mono T f x (Nat.le_succ n))
    have hle := integral_mono (his.sub (hT.integrable_comp_of_integrable hin))
      (hf.indicator hE) hpoint
    have hsub : (∫ x, maxSum T f (n+1) x - maxSum T f n (T x) ∂μ) =
        (∫ x, maxSum T f (n+1) x ∂μ) - (∫ x, maxSum T f n x ∂μ) := by
      calc
        _ = (∫ x, maxSum T f (n+1) x ∂μ) - (∫ x, maxSum T f n (T x) ∂μ) :=
          integral_sub his (hT.integrable_comp_of_integrable hin)
        _ = _ := by rw [integral_comp_preserving hT hin]
    have hnon : 0 ≤ ∫ x, maxSum T f (n+1) x - maxSum T f n (T x) ∂μ := by
      rw [hsub]
      exact sub_nonneg.mpr hmono
    exact (hnon.trans hle).trans_eq (integral_indicator hE)

omit [MeasurableSpace α] in
theorem bddAbove_range_nat_iff (u : ℕ → ℝ) :
    BddAbove (Set.range u) ↔ ∃ N : ℕ, ∀ n, u n ≤ N := by
  constructor
  · rintro ⟨C, hC⟩
    obtain ⟨N, hN⟩ := exists_nat_ge C
    exact ⟨N, fun n => (hC ⟨n,rfl⟩).trans hN⟩
  · rintro ⟨N,hN⟩
    exact ⟨N, fun _ ⟨n,hn⟩ => hn ▸ hN n⟩

theorem sum_measurable {T : α → α} {f : α → ℝ}
    (hT : Measurable T) (hf : Measurable f) (n : ℕ) :
    Measurable (birkhoffSum T f n) := by
  induction n with
  | zero => exact measurable_const
  | succ n ih =>
    have he : birkhoffSum T f (n+1) = fun x => f x + birkhoffSum T f n (T x) :=
      funext (birkhoffSum_succ' T f n)
    rw [he]
    exact hf.add (ih.comp hT)

theorem boundedSums_measurable {T : α → α} {f : α → ℝ}
    (hT : Measurable T) (hf : Measurable f) : MeasurableSet (boundedSums T f) := by
  have he : boundedSums T f = {x | ∃ N : ℕ, ∀ n : ℕ, birkhoffSum T f n x ≤ N} := by
    ext x
    exact bddAbove_range_nat_iff _
  rw [he]
  simp only [Set.ofPred_exists, Set.ofPred_forall]
  exact MeasurableSet.iUnion fun N => MeasurableSet.iInter fun n =>
    measurableSet_le (sum_measurable hT hf n) measurable_const

omit [MeasurableSpace α] in
theorem boundedSums_invariant (T : α → α) (f : α → ℝ) :
    T ⁻¹' boundedSums T f = boundedSums T f := by
  ext x
  change BddAbove (Set.range (fun n : ℕ => birkhoffSum T f n (T x))) ↔
    BddAbove (Set.range (fun n : ℕ => birkhoffSum T f n x))
  constructor
  · rintro ⟨C, hC⟩
    refine ⟨max 0 (f x+C), ?_⟩
    rintro _ ⟨n,rfl⟩
    cases n with
    | zero => exact le_max_left (0 : ℝ) (f x+C)
    | succ n =>
      dsimp only
      rw [birkhoffSum_succ']
      exact (show f x+birkhoffSum T f n (T x) ≤ f x+C by
        linarith [hC ⟨n,rfl⟩]).trans (le_max_right _ _)
  · rintro ⟨C,hC⟩
    refine ⟨C-f x, ?_⟩
    rintro _ ⟨n,rfl⟩
    have hh := hC ⟨n+1,rfl⟩
    dsimp only at hh ⊢
    rw [birkhoffSum_succ'] at hh
    linarith

theorem hopf_of_ae_positive_sum {T : α → α} {f : α → ℝ}
    (hT : MeasurePreserving T μ μ) (hfm : Measurable f) (hf : Integrable f μ)
    (hpos : ∀ᵐ x ∂μ, ∃ n, 0 < maxSum T f n x) :
    0 ≤ ∫ x, f x ∂μ := by
  let E : ℕ → Set α := fun n => {x | 0 < maxSum T f n x}
  have hE : ∀ n, MeasurableSet (E n) := fun n =>
    measurableSet_lt measurable_const (maxSum_measurable hT.measurable hfm n)
  have hlim : ∀ᵐ x ∂μ, Tendsto (fun n => (E n).indicator f x) atTop (𝓝 (f x)) := by
    filter_upwards [hpos] with x hx
    obtain ⟨n, hn⟩ := hx
    apply tendsto_const_nhds.congr'
    filter_upwards [eventually_ge_atTop n] with k hk
    have hxk : x ∈ E k := hn.trans_le (maxSum_mono T f x hk)
    exact (Set.indicator_of_mem hxk f).symm
  have hlimint := tendsto_integral_of_dominated_convergence (fun x => ‖f x‖)
    (fun n => (hf.indicator (hE n)).aestronglyMeasurable) hf.norm
    (fun n => ae_of_all μ fun x => by
      by_cases hx : x ∈ E n
      · simp [Set.indicator_of_mem hx]
      · simp [Set.indicator_of_notMem hx]) hlim
  apply ge_of_tendsto hlimint
  exact Eventually.of_forall fun n => by
    rw [integral_indicator (hE n)]
    exact hopf_finite hT hfm hf n

theorem ae_boundedSums_of_integral_neg {T : α → α} {f : α → ℝ}
    (hT : Ergodic T μ) (hfm : Measurable f) (hf : Integrable f μ)
    (hneg : (∫ x, f x ∂μ) < 0) : ∀ᵐ x ∂μ, x ∈ boundedSums T f := by
  rcases hT.toPreErgodic.ae_mem_or_ae_notMem
    (boundedSums_measurable hT.measurable hfm) (boundedSums_invariant T f) with h | h
  · exact h
  · have hp : ∀ᵐ x ∂μ, ∃ n, 0 < maxSum T f n x := by
      filter_upwards [h] with x hx
      obtain ⟨y, ⟨n,rfl⟩,hn⟩ := not_bddAbove_iff.mp hx 0
      exact ⟨n,hn.trans_le (birkhoffSum_le_maxSum T f n x)⟩
    exact (not_le_of_gt hneg (hopf_of_ae_positive_sum hT.toMeasurePreserving hfm hf hp)).elim

omit [MeasurableSpace α] in
theorem sum_sub_const (T : α → α) (f : α → ℝ) (c : ℝ) (n : ℕ) (x : α) :
    birkhoffSum T (fun y => f y-c) n x = birkhoffSum T f n x - n*c := by
  simp [birkhoffSum, Finset.sum_sub_distrib]

theorem ae_upper_average [IsProbabilityMeasure μ] {T : α → α} {f : α → ℝ}
    (hT : Ergodic T μ) (hfm : Measurable f) (hf : Integrable f μ) :
    ∀ᵐ x ∂μ, ∀ a : ℝ, (∫ x, f x ∂μ) < a →
      ∀ᶠ n : ℕ in atTop, birkhoffSum T f n x / (n : ℝ) < a := by
  have hb : ∀ q : ℚ, ∀ᵐ x ∂μ, (∫ x, f x ∂μ) < (q : ℝ) →
      x ∈ boundedSums T (fun y => f y - q) := by
    intro q
    by_cases hq : (∫ x, f x ∂μ) < (q : ℝ)
    · have hn : (∫ x, (f x - q) ∂μ) < 0 := by
        rw [integral_sub hf (integrable_const _)]
        simpa using sub_neg.mpr hq
      filter_upwards [ae_boundedSums_of_integral_neg hT
        (hfm.sub measurable_const) (hf.sub (integrable_const _)) hn] with x hx using
        fun _ => hx
    · exact ae_of_all μ fun _ h => (hq h).elim
  filter_upwards [ae_all_iff.mpr hb] with x hx
  intro a ha
  obtain ⟨q,hq,hqa⟩ := exists_rat_btwn ha
  obtain ⟨C,hC⟩ := hx q hq
  have hlim : Tendsto (fun n : ℕ => (q : ℝ)+C/n) atTop (𝓝 (q : ℝ)) := by
    simpa using tendsto_const_nhds.add (tendsto_const_div_atTop_nhds_zero_nat C)
  filter_upwards [(tendsto_order.mp hlim).2 a hqa, eventually_ge_atTop 1] with n hn hn1
  have hN : (0 : ℝ) < n := by exact_mod_cast hn1
  have hh := hC ⟨n,rfl⟩
  dsimp only at hh
  rw [sum_sub_const] at hh
  have he : birkhoffSum T f n x / (n : ℝ) ≤ (q : ℝ)+C/n := by
    apply (div_le_iff₀ hN).mpr
    have hre : ((q : ℝ)+C/n)*n = n*(q : ℝ)+C := by field_simp
    rw [hre]
    linarith
  exact he.trans_lt hn

theorem ae_tendsto_average_oai [IsProbabilityMeasure μ] {T : α → α} {f : α → ℝ}
    (hT : Ergodic T μ) (hfm : Measurable f) (hf : Integrable f μ) :
    ∀ᵐ x ∂μ, Tendsto (fun n : ℕ => birkhoffSum T f n x / (n : ℝ)) atTop
      (𝓝 (∫ x, f x ∂μ)) := by
  filter_upwards [ae_upper_average hT hfm hf, ae_upper_average hT hfm.neg hf.neg]
    with x hx hxneg
  apply tendsto_order.mpr
  constructor
  · intro a ha
    have hm : (∫ x, -f x ∂μ) < -a := by rw [integral_neg]; linarith
    filter_upwards [hxneg (-a) hm] with n hn
    have he : birkhoffSum T (fun y => -f y) n x = -birkhoffSum T f n x := by
      simp [birkhoffSum]
    change birkhoffSum T (fun y => -f y) n x / (n : ℝ) < -a at hn
    rw [he, neg_div] at hn
    linarith
  · exact hx

end ErgodicAux
end EntropyRateDimension

end

end OAI
end

theorem solution.{uα} : type_of% @OAI.EntropyRateDimension.ErgodicAux.ae_tendsto_average_oai.{uα} := @OAI.EntropyRateDimension.ErgodicAux.ae_tendsto_average_oai.{uα}
