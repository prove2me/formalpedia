-- Prove2me | solution 1 for OAI.StandardMapEntropy.ReversibleGraphRectangle.exists_weakBernoulli_partitions_q44
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-27T12:36:11.157235+00:00
-- url     : https://prove2.me/submissions/66095a0f-2fea-4fc9-8ccb-fd670bc210f7

import Mathlib
import Definitions.Def_StandardMapComponents
import Definitions.Def_OAIQ44C002

section
-- module Solutions.OAIQ44_CM.StandardMap_LocalScarcity
attribute [-instance] _root_.OAI.StandardMapEntropy.LocalCoding.optionFinsetMeasurableSpace _root_.OAI.StandardMapEntropy.circleVolumeNullSingleton
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory Set
open scoped ENNReal BigOperators

namespace StandardMapEntropy

theorem measurePreserving_standardMap (k : ℝ) : MeasurePreserving (standardMap k) area area := by
  unfold area
  have hkick : MeasurePreserving
      (fun z : Torus => (z.1, z.2 + kick k z.1))
        ((volume : Measure Circle).prod volume) (volume.prod volume) := by
    refine (MeasurePreserving.id (volume : Measure Circle)).skew_product
      (g := fun x y : Circle => y + kick k x) ?_ ?_
    · exact measurable_snd.add ((continuous_kick k).measurable.comp measurable_fst)
    · exact Filter.Eventually.of_forall (fun x => map_add_right_eq_self volume (kick k x))
  convert (measurePreserving_add_prod (volume : Measure Circle) volume).comp hkick using 1
  all_goals try with_reducible_and_instances rfl
  funext z
  simp only [Function.comp_apply, standardMap, kick]
  congr 1
  abel

open scoped Matrix.Norms.Operator

open Filter
open scoped Topology

open Metric

end StandardMapEntropy
open MeasureTheory Set Filter
open scoped Topology ENNReal
open MeasureTheory Set Filter Metric
open scoped Topology ENNReal

end OAI
end

section
-- module Solutions.OAIQ44_CM.StandardMap_Lyapunov_Subadditive
attribute [-instance] _root_.OAI.StandardMapEntropy.LocalCoding.optionFinsetMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open MeasureTheory Filter Set
open scoped ENNReal Topology BigOperators

namespace BoundedSubadditive

variable {X : Type*}

lemma excess_nonneg (T : X → X) (h : X → ℝ) (δ : ℝ) (n : ℕ) (x : X) :
    0 ≤ excess T h δ n x := by
  cases n with
  | zero => rfl
  | succ n => exact le_max_left _ _

lemma excess_succ_mono (T : X → X) (h : X → ℝ) (δ : ℝ) (n : ℕ) (x : X) :
    excess T h δ n x ≤ excess T h δ (n + 1) x := by
  induction n generalizing x with
  | zero => exact excess_nonneg T h δ 1 x
  | succ n ih =>
    exact max_le_max le_rfl (add_le_add le_rfl (ih (T x)))

lemma excess_mono (T : X → X) (h : X → ℝ) (δ : ℝ) (x : X) :
    Monotone (fun n => excess T h δ n x) :=
  monotone_nat_of_le_succ (fun n => excess_succ_mono T h δ n x)

lemma sum_sub_le_excess (T : X → X) (h : X → ℝ) (δ : ℝ) (n : ℕ) (x : X) :
    birkhoffSum T h n x - (n : ℝ) * δ ≤ excess T h δ n x := by
  induction n generalizing x with
  | zero => simp [birkhoffSum, excess]
  | succ n ih =>
    rw [birkhoffSum_succ']
    have hm : h x - δ + excess T h δ n (T x) ≤ excess T h δ (n + 1) x :=
      le_max_right _ _
    have hi := ih (T x)
    push_cast
    linarith

lemma excess_account (T : X → X) (h : X → ℝ) (δ : ℝ)
    (hh : ∀ x, 0 ≤ h x) (n : ℕ) (x : X) :
    (if 0 < excess T h δ (n + 1) x then δ else 0) ≤
      h x + excess T h δ (n + 1) (T x) - excess T h δ (n + 1) x := by
  split_ifs with hp
  · have he : excess T h δ (n + 1) x = h x - δ + excess T h δ n (T x) := by
      apply max_eq_right
      change 0 < max 0 (h x - δ + excess T h δ n (T x)) at hp
      exact (lt_max_iff.mp hp).resolve_left (lt_irrefl 0) |>.le
    rw [he]
    linarith [excess_succ_mono T h δ n (T x)]
  · have he : excess T h δ (n + 1) x = 0 :=
      le_antisymm (not_lt.mp hp) (excess_nonneg T h δ _ x)
    rw [he]
    linarith [hh x, excess_nonneg T h δ (n + 1) (T x)]

section Measure
variable [MeasurableSpace X] {μ : Measure X} [IsFiniteMeasure μ]
variable {T : X → X} {h : X → ℝ} {δ : ℝ}

lemma measurable_excess (hT : Measurable T) (hh : Measurable h) (n : ℕ) :
    Measurable (excess T h δ n) := by
  induction n with
  | zero => exact measurable_const
  | succ n ih => exact measurable_const.max ((hh.sub measurable_const).add (ih.comp hT))

lemma integrable_excess (hT : MeasurePreserving T μ μ) (hh : Integrable h μ) (n : ℕ) :
    Integrable (excess T h δ n) μ := by
  induction n with
  | zero => exact integrable_const 0
  | succ n ih =>
    exact (integrable_const (0 : ℝ)).sup
      ((hh.sub (integrable_const δ)).add (hT.integrable_comp_of_integrable ih))

omit [IsFiniteMeasure μ] in
lemma integral_comp (hT : MeasurePreserving T μ μ) {g : X → ℝ}
    (hg : AEStronglyMeasurable g μ) : (∫ x, g (T x) ∂μ) = ∫ x, g x ∂μ := by
  have hg' : AEStronglyMeasurable g (Measure.map T μ) := by rwa [hT.map_eq]
  simpa only [hT.map_eq] using (integral_map hT.measurable.aemeasurable hg').symm

lemma excess_measure_bound (hT : MeasurePreserving T μ μ) (hm : Measurable h)
    (hi : Integrable h μ) (h0 : ∀ x, 0 ≤ h x) (hδ : 0 < δ) (n : ℕ) :
    μ {x | 0 < excess T h δ n x} ≤ ENNReal.ofReal ((∫ x, h x ∂μ) / δ) := by
  cases n with
  | zero => simp [excess]
  | succ n =>
    let s : Set X := {x | 0 < excess T h δ (n + 1) x}
    have hs : MeasurableSet s := measurableSet_lt measurable_const
      (measurable_excess hT.measurable hm _)
    have he := integrable_excess (δ := δ) hT hi (n + 1)
    have heT : Integrable (fun x => excess T h δ (n + 1) (T x)) μ :=
      hT.integrable_comp_of_integrable he
    have hb : (∫ x, s.indicator (fun _ => δ) x ∂μ) ≤
        ∫ x, h x + excess T h δ (n + 1) (T x) - excess T h δ (n + 1) x ∂μ := by
      apply integral_mono ((integrable_const δ).indicator hs)
        ((hi.add heT).sub he)
      intro x
      simpa only [Set.indicator, s, Set.mem_ofPred_eq, Pi.sub_apply, Pi.add_apply, Function.comp_apply] using excess_account T h δ h0 n x
    have hsub := integral_sub (hi.add heT) he
    have hadd := integral_add hi heT
    simp only [Pi.add_apply] at hsub hadd
    rw [integral_indicator_const δ hs, hsub, hadd,
      integral_comp hT he.aestronglyMeasurable] at hb
    have hb' : μ.real s ≤ (∫ x, h x ∂μ) / δ := by
      apply (le_div_iff₀ hδ).mpr
      simpa only [smul_eq_mul, add_sub_cancel_right] using hb
    calc
      μ s = ENNReal.ofReal (μ.real s) := (ENNReal.ofReal_toReal (measure_ne_top μ s)).symm
      _ ≤ _ := ENNReal.ofReal_le_ofReal hb'

lemma maximal_measure_bound (hT : MeasurePreserving T μ μ) (hm : Measurable h)
    (hi : Integrable h μ) (h0 : ∀ x, 0 ≤ h x) (hδ : 0 < δ) :
    μ {x | ∃ n : ℕ, (n : ℝ) * δ < birkhoffSum T h n x} ≤
      ENNReal.ofReal ((∫ x, h x ∂μ) / δ) := by
  have hsub : {x | ∃ n : ℕ, (n : ℝ) * δ < birkhoffSum T h n x} ⊆
      ⋃ n : ℕ, {x | 0 < excess T h δ n x} := by
    rintro x ⟨n, hn⟩
    apply mem_iUnion.mpr
    refine ⟨n, ?_⟩
    exact lt_of_lt_of_le (sub_pos.mpr hn) (sum_sub_le_excess T h δ n x)
  refine (measure_mono hsub).trans ?_
  have hm' : Monotone (fun n : ℕ => {x | 0 < excess T h δ n x}) := by
    intro m n hmn x hx
    exact lt_of_lt_of_le hx (excess_mono T h δ x hmn)
  rw [hm'.measure_iUnion]
  exact iSup_le (fun n => excess_measure_bound hT hm hi h0 hδ n)

end Measure

namespace Cocycle
variable [MeasurableSpace X] {T : X → X} (f : Cocycle X T)

lemma average_bounds (n : ℕ) (x : X) : 0 ≤ f.average n x ∧ f.average n x ≤ 1 := by
  refine ⟨div_nonneg (f.nonneg n x) (Nat.cast_nonneg n), ?_⟩
  by_cases hn : n = 0
  · simp [average, hn]
  · exact (div_le_one (Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn))).mpr (f.le_time n x)

lemma average_bdd_above (x : X) : IsBoundedUnder (· ≤ ·) atTop (fun n => f.average n x) :=
  isBoundedUnder_of ⟨1, fun n => (f.average_bounds n x).2⟩

lemma average_bdd_below (x : X) : IsBoundedUnder (· ≥ ·) atTop (fun n => f.average n x) :=
  isBoundedUnder_of ⟨0, fun n => (f.average_bounds n x).1⟩

lemma lowerRate_bounds (x : X) : 0 ≤ f.lowerRate x ∧ f.lowerRate x ≤ 1 := by
  constructor
  · exact le_liminf_of_le (f.average_bdd_above x).isCoboundedUnder_ge
      (Eventually.of_forall fun n => (f.average_bounds n x).1)
  · have hh := liminf_le_liminf (Eventually.of_forall fun n => (f.average_bounds n x).2)
      (f.average_bdd_below x) (isBoundedUnder_const.isCoboundedUnder_ge)
    simpa only [liminf_const, lowerRate] using hh

lemma measurable_average (n : ℕ) : Measurable (f.average n) :=
  (f.measurable n).div_const _

lemma measurable_lowerRate : Measurable f.lowerRate :=
  Measurable.liminf (fun n => f.measurable_average n)

lemma average_shift_bound (n : ℕ) (x : X) :
    |f.average n (T x) - f.average n x| ≤ 2 / (n : ℝ) := by
  rw [average, average, ← sub_div, abs_div, abs_of_nonneg (show (0 : ℝ) ≤ n from Nat.cast_nonneg n)]
  exact div_le_div_of_nonneg_right (f.shift_bound n x) (Nat.cast_nonneg n)

lemma lowerRate_shift (x : X) : f.lowerRate (T x) = f.lowerRate x := by
  have hc : Tendsto (fun n : ℕ => (2 : ℝ) / n) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
  have haux (a b : X) (hab : ∀ n, f.average n a - f.average n b ≤ 2 / (n : ℝ)) :
      f.lowerRate a ≤ f.lowerRate b := by
    apply le_of_forall_pos_le_add
    intro ε hε
    have he : ∀ᶠ n : ℕ in atTop, f.average n a ≤ f.average n b + ε := by
      filter_upwards [hc.eventually (gt_mem_nhds hε)] with n hn
      linarith [hab n]
    have hb : IsBoundedUnder (· ≤ ·) atTop (fun n => f.average n b + ε) :=
      isBoundedUnder_of ⟨1 + ε, fun n => add_le_add (f.average_bounds n b).2 le_rfl⟩
    have hh := liminf_le_liminf he (f.average_bdd_below a) hb.isCoboundedUnder_ge
    rw [liminf_add_const atTop (fun n => f.average n b) ε
      (f.average_bdd_above b).isCoboundedUnder_ge (f.average_bdd_below b)] at hh
    exact hh
  apply le_antisymm
  · exact haux (T x) x (fun n => (abs_le.mp (f.average_shift_bound n x)).2)
  · apply haux x (T x)
    intro n
    have hh := (abs_le.mp (f.average_shift_bound n x)).1
    linarith

lemma lowerRate_iterate (n : ℕ) (x : X) : f.lowerRate (T^[n] x) = f.lowerRate x := by
  induction n with
  | zero => rfl
  | succ n ih => rw [Function.iterate_succ_apply', f.lowerRate_shift, ih]

lemma measurableSet_badSet (ε : ℝ) (N : ℕ) : MeasurableSet (f.badSet ε N) := by
  apply MeasurableSet.compl
  apply MeasurableSet.biUnion (Set.to_countable _)
  intro n hn
  exact measurableSet_le (f.measurable n)
    (measurable_const.mul (f.measurable_lowerRate.add_const ε))

lemma measurable_badObservation (ε : ℝ) (N : ℕ) : Measurable (f.badObservation ε N) :=
  measurable_const.indicator (f.measurableSet_badSet ε N)

lemma badObservation_bounds (ε : ℝ) (N : ℕ) (x : X) :
    0 ≤ f.badObservation ε N x ∧ f.badObservation ε N x ≤ 1 := by
  classical
  by_cases hx : x ∈ f.badSet ε N <;> simp [badObservation, hx]

lemma exists_good_block (x : X) (ε : ℝ) (hε : 0 < ε) :
    ∃ n : ℕ, 0 < n ∧ f.value n x ≤ (n : ℝ) * (f.lowerRate x + ε) := by
  have hh : ∃ᶠ n : ℕ in atTop, f.average n x < f.lowerRate x + ε :=
    frequently_lt_of_liminf_lt (f.average_bdd_above x).isCoboundedUnder_ge (lt_add_of_pos_right _ hε)
  obtain ⟨n, hn, he⟩ := frequently_atTop.mp hh 1
  have hn' : 0 < n := by omega
  refine ⟨n, hn', ?_⟩
  have hi := (div_lt_iff₀ (Nat.cast_pos.mpr hn')).mp he
  nlinarith

lemma badObservation_tendsto_zero (x : X) (ε : ℝ) (hε : 0 < ε) :
    Tendsto (fun N => f.badObservation ε N x) atTop (𝓝 0) := by
  obtain ⟨n, hn, hg⟩ := f.exists_good_block x ε hε
  apply tendsto_const_nhds.congr'
  filter_upwards [eventually_ge_atTop n] with N hN
  symm
  apply Set.indicator_of_notMem
  simp only [badSet, mem_compl_iff, mem_iUnion, mem_ofPred_eq, not_not]
  exact ⟨n, ⟨hn, hN⟩, hg⟩

lemma birkhoff_bad_nonneg (ε : ℝ) (N n : ℕ) (x : X) :
    0 ≤ birkhoffSum T (f.badObservation ε N) n x := by
  exact Finset.sum_nonneg fun i hi => (f.badObservation_bounds ε N (T^[i] x)).1

lemma block_bound (ε : ℝ) (hε : 0 ≤ ε) (N n : ℕ) (x : X) :
    f.value n x ≤ (n : ℝ) * (f.lowerRate x + ε) +
      birkhoffSum T (f.badObservation ε N) n x + (N : ℝ) := by
  classical
  induction n using Nat.strong_induction_on generalizing x with
  | h n ih =>
    have ha : 0 ≤ f.lowerRate x + ε := add_nonneg (f.lowerRate_bounds x).1 hε
    by_cases hn : n ≤ N
    · have hcast : (n : ℝ) ≤ N := by exact_mod_cast hn
      have hp := mul_nonneg (Nat.cast_nonneg n : (0 : ℝ) ≤ n) ha
      linarith [f.le_time n x, f.birkhoff_bad_nonneg ε N n x]
    · by_cases hx : x ∈ f.badSet ε N
      · have hn0 : 1 ≤ n := by omega
        have he : 1 + (n - 1) = n := by omega
        have hs := f.subadd 1 (n - 1) x
        simp only [he, Function.iterate_one] at hs
        have hi := ih (n - 1) (by omega) (T x)
        rw [f.lowerRate_shift] at hi
        rw [Nat.cast_sub hn0, Nat.cast_one, sub_mul, one_mul] at hi
        have hb : f.badObservation ε N x = 1 := by simp [badObservation, hx]
        have hsum : birkhoffSum T (f.badObservation ε N) n x =
            1 + birkhoffSum T (f.badObservation ε N) (n - 1) (T x) := by
          conv_lhs => rw [show n = (n - 1) + 1 by omega]
          rw [birkhoffSum_succ', hb]
        rw [hsum]
        have h1 := f.le_time 1 x
        norm_num only [Nat.cast_one] at h1
        linarith
      · have hg : x ∈ ⋃ m ∈ Set.Ioc 0 N,
            {y | f.value m y ≤ (m : ℝ) * (f.lowerRate y + ε)} := not_not.mp hx
        obtain ⟨m, hgm⟩ := mem_iUnion.mp hg
        obtain ⟨hm, hfm⟩ := mem_iUnion.mp hgm
        have hmn : m ≤ n := by have := hm.2; omega
        have he : m + (n - m) = n := Nat.add_sub_of_le hmn
        have hs := f.subadd m (n - m) x
        rw [he] at hs
        have hi := ih (n - m) (by have := hm.1; omega) (T^[m] x)
        rw [f.lowerRate_iterate, Nat.cast_sub hmn, sub_mul] at hi
        have hsum : birkhoffSum T (f.badObservation ε N) n x =
            birkhoffSum T (f.badObservation ε N) m x +
              birkhoffSum T (f.badObservation ε N) (n - m) (T^[m] x) := by
          simpa only [he] using birkhoffSum_add T (f.badObservation ε N) m (n - m) x
        rw [hsum]
        have hp := f.birkhoff_bad_nonneg ε N m x
        change f.value m x ≤ (m : ℝ) * (f.lowerRate x + ε) at hfm
        linarith

lemma upperRate_le_of_bad_averages (ε : ℝ) (hε : 0 ≤ ε) (N : ℕ) (δ : ℝ) (x : X)
    (hb : ∀ n, birkhoffSum T (f.badObservation ε N) n x ≤ (n : ℝ) * δ) :
    f.upperRate x ≤ f.lowerRate x + ε + δ := by
  apply le_of_forall_pos_le_add
  intro γ hγ
  have hc : Tendsto (fun n : ℕ => (N : ℝ) / n) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
  apply limsup_le_of_le (f.average_bdd_below x).isCoboundedUnder_le
  filter_upwards [hc.eventually (gt_mem_nhds hγ), eventually_gt_atTop 0] with n hsmall hn
  have hn' : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  have hN := (div_lt_iff₀ hn').mp hsmall
  apply (div_le_iff₀ hn').mpr
  have hB := f.block_bound ε hε N n x
  have hbad := hb n
  nlinarith

section Measure
variable {μ : Measure X} [IsFiniteMeasure μ]

lemma integrable_badObservation (ε : ℝ) (N : ℕ) :
    Integrable (f.badObservation ε N) μ :=
  (integrable_const (1 : ℝ)).indicator (f.measurableSet_badSet ε N)

lemma integral_badObservation_tendsto_zero (ε : ℝ) (hε : 0 < ε) :
    Tendsto (fun N => ∫ x, f.badObservation ε N x ∂μ) atTop (𝓝 0) := by
  have hh := tendsto_integral_of_dominated_convergence (μ := μ) (fun _ : X => (1 : ℝ))
    (fun N => (f.measurable_badObservation ε N).aestronglyMeasurable)
    (integrable_const 1)
    (fun N => Eventually.of_forall fun x => by
      rw [Real.norm_eq_abs, abs_of_nonneg (f.badObservation_bounds ε N x).1]
      exact (f.badObservation_bounds ε N x).2)
    (Eventually.of_forall fun x => f.badObservation_tendsto_zero x ε hε)
  simpa only [integral_zero] using hh

lemma ae_upperRate_le_add (hT : MeasurePreserving T μ μ) (ε : ℝ) (hε : 0 < ε) :
    ∀ᵐ x ∂μ, f.upperRate x ≤ f.lowerRate x + 2 * ε := by
  let E : Set X := {x | f.lowerRate x + 2 * ε < f.upperRate x}
  have hbound (N : ℕ) : μ E ≤
      ENNReal.ofReal ((∫ x, f.badObservation ε N x ∂μ) / ε) := by
    have hsub : E ⊆ {x | ∃ n : ℕ, (n : ℝ) * ε < birkhoffSum T (f.badObservation ε N) n x} := by
      intro x hx
      by_contra hn
      change ¬ ∃ n : ℕ, (n : ℝ) * ε < birkhoffSum T (f.badObservation ε N) n x at hn
      push Not at hn
      have hh := f.upperRate_le_of_bad_averages ε hε.le N ε x hn
      change f.lowerRate x + 2 * ε < f.upperRate x at hx
      linarith
    exact (measure_mono hsub).trans
      (maximal_measure_bound hT (f.measurable_badObservation ε N)
        (f.integrable_badObservation ε N) (fun x => (f.badObservation_bounds ε N x).1) hε)
  have hc : Tendsto (fun N => ENNReal.ofReal ((∫ x, f.badObservation ε N x ∂μ) / ε))
      atTop (𝓝 0) := by
    have hh := (f.integral_badObservation_tendsto_zero (μ := μ) ε hε).div_const ε
    simpa only [Function.comp_def, zero_div, ENNReal.ofReal_zero] using
      ENNReal.continuous_ofReal.continuousAt.tendsto.comp hh
  have hzero : μ E = 0 := le_antisymm (ge_of_tendsto' hc hbound) zero_le
  simpa only [ae_iff, not_le] using hzero

theorem ae_tendsto_average (hT : MeasurePreserving T μ μ) :
    ∀ᵐ x ∂μ, Tendsto (fun n => f.average n x) atTop (𝓝 (f.lowerRate x)) := by
  have ha : ∀ᵐ x ∂μ, ∀ j : ℕ, f.upperRate x ≤ f.lowerRate x + 2 * (1 / ((j : ℝ) + 1)) := by
    apply ae_all_iff.mpr
    intro j
    exact f.ae_upperRate_le_add hT _ (by positivity)
  filter_upwards [ha] with x hx
  have hc : Tendsto (fun j : ℕ => f.lowerRate x + 2 * (1 / ((j : ℝ) + 1)))
      atTop (𝓝 (f.lowerRate x)) := by
    simpa using tendsto_const_nhds.add
      (tendsto_const_nhds.mul (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)))
  have hu : f.upperRate x ≤ f.lowerRate x := ge_of_tendsto' hc hx
  exact tendsto_of_le_liminf_of_limsup_le le_rfl hu
    (f.average_bdd_above x) (f.average_bdd_below x)

theorem tendsto_integral_average (hT : MeasurePreserving T μ μ) :
    Tendsto (fun n => ∫ x, f.average n x ∂μ) atTop (𝓝 (∫ x, f.lowerRate x ∂μ)) := by
  exact tendsto_integral_of_dominated_convergence (fun _ : X => (1 : ℝ))
    (fun n => (f.measurable_average n).aestronglyMeasurable) (integrable_const 1)
    (fun n => Eventually.of_forall fun x => by
      rw [Real.norm_eq_abs, abs_of_nonneg (f.average_bounds n x).1]
      exact (f.average_bounds n x).2)
    (f.ae_tendsto_average hT)

end Measure
end Cocycle
end BoundedSubadditive

end
end

end OAI
end

section
-- module Solutions.OAIQ44_CM.StandardMap_Lyapunov_DerivativeGrowth
attribute [-instance] _root_.OAI.StandardMapEntropy.LocalCoding.optionFinsetMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace StandardMapEntropy
open MeasureTheory Set Filter
open scoped Topology ENNReal ContDiff

lemma complexProjection_standardInverseLift (k : ℝ) (z : ℂ) :
    complexProjection (standardInverseLift k z) = inverseMap k (complexProjection z) := by
  ext <;> simp [complexProjection, standardInverseLift, inverseMap, kick,
    ← QuotientAddGroup.mk_sub]

end StandardMapEntropy

namespace StandardMapEntropy
open MeasureTheory Set Filter
open scoped Topology ENNReal ContDiff

lemma complexProjection_iterate (k : ℝ) (n : ℕ) (z : ℂ) :
    complexProjection ((standardLift k)^[n] z) = (standardMap k)^[n] (complexProjection z) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply', complexProjection_standardLift, ih]

end StandardMapEntropy

end
end

end OAI
end

section
-- module Solutions.OAIQ44_CM.StandardMap_Lyapunov_InverseLyapunov
attribute [-instance] _root_.OAI.StandardMapEntropy.LocalCoding.optionFinsetMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace StandardMapEntropy
open MeasureTheory Set Filter
open scoped Topology ENNReal

lemma complexProjection_inverse_iterate (k : ℝ) (n : ℕ) (z : ℂ) :
    complexProjection ((standardInverseLift k)^[n] z) = (inverseMap k)^[n] (complexProjection z) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply',
      complexProjection_standardInverseLift, ih]

end StandardMapEntropy

end
end

end OAI
end

section
-- module Solutions.OAIQ44_CM.StandardMap_Lyapunov_TransverseLines
attribute [-instance] _root_.OAI.StandardMapEntropy.LocalCoding.optionFinsetMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace StandardMapEntropy
open MeasureTheory Set Filter
open scoped Topology ENNReal

lemma measurePreserving_inverseMap (k : ℝ) : MeasurePreserving (inverseMap k) area area :=
  (measurePreserving_standardMap k).symm (standardMap_measurableEquiv k)

end StandardMapEntropy

end
end

end OAI
end

section
-- module Solutions.OAIQ44_CM.StandardMap_Lyapunov_MeasurableFrame
attribute [-instance] _root_.OAI.StandardMapEntropy.LocalCoding.optionFinsetMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace StandardMapEntropy
open MeasureTheory Set Filter
open scoped Topology ENNReal

namespace TemperedControl

variable {X : Type*} [MeasurableSpace X]

lemma radius_le_one (e : X ≃ᵐ X) {c : X → ℝ} (hc : ∀ x, 0 ≤ c x) (ε : ℝ) (x : X) :
    radius e c ε x≤1 := by
  have := control_nonneg e hc ε x
  exact (inv_le_one₀ (by linarith : 0<1+control e c ε x)).mpr (by linarith)

end TemperedControl
end StandardMapEntropy

end
section
namespace StandardMapEntropy
open MeasureTheory Set Filter
open scoped Topology ENNReal

lemma diagonalPlane_apply (α β : ℝ) (v : ℂ) :
    diagonalPlane α β v = ⟨α*v.re, β*v.im⟩ := by
  apply Complex.ext <;> simp [diagonalPlane] <;> ring

end StandardMapEntropy

end
section
namespace StandardMapEntropy
open MeasureTheory Set Filter
open scoped Topology ENNReal

lemma chartRadius_le_one (k χ ε : ℝ) (z : Torus) : chartRadius k χ ε z≤1 :=
  TemperedControl.radius_le_one _ (fun z => zero_le_one.trans (chartControl_ge_one k χ z)) ε z

end StandardMapEntropy

end
end

end OAI
end

section
-- module Solutions.OAIQ44_CM.StandardMap_Stable_SmoothRemainder
attribute [-instance] _root_.OAI.StandardMapEntropy.LocalCoding.optionFinsetMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace StandardMapEntropy.NonlinearStable
open Filter
open scoped Topology NNReal

variable {ℓ δ : ℝ≥0}

lemma solution_initial (r : Recurrence ℓ δ) (h : ℓ+δ<1) (s : ℝ) : (r.solution h s 0).1=s := by
  have hh := congrArg (fun x : Sequence => (x 0).1) (solution_fixed r h s)
  exact hh.symm

lemma solution_orbit (r : Recurrence ℓ δ) (h : ℓ+δ<1) (s : ℝ) (n : ℕ) :
    r.solution h s (n+1)=r.step n (r.solution h s n) := by
  have hh := congrArg (fun x : Sequence => x (n+1)) (solution_fixed r h s)
  have hh' := congrArg (fun x : Sequence => x n) (solution_fixed r h s)
  apply Prod.ext
  · exact (congrArg Prod.fst hh).symm
  · have he := congrArg Prod.snd hh'
    change (r.b n)⁻¹*((r.solution h s (n+1)).2-(r.remainder n (r.solution h s n)).2)=
      (r.solution h s n).2 at he
    change _=r.b n*(r.solution h s n).2+(r.remainder n (r.solution h s n)).2
    have he' := congrArg (fun t : ℝ => r.b n*t) he
    rw [← mul_assoc, mul_inv_cancel₀ (r.b_ne n), one_mul] at he'
    linarith

lemma solution_lipschitz (r : Recurrence ℓ δ) (h : ℓ+δ<1) (s t : ℝ) :
    ‖r.solution h s-r.solution h t‖≤|s-t| := by
  apply bound_of_max_contraction (abs_nonneg _) (show ((ℓ+δ : ℝ≥0) : ℝ)<1 from h)
  apply (BoundedContinuousFunction.norm_le (le_trans (abs_nonneg _) (le_max_left _ _))).mpr
  intro n
  have hh := perronValue_sub_bound r (le_trans (le_add_of_nonneg_right (show (0 : ℝ≥0) ≤ δ from bot_le)) h.le)
    s t (r.solution h s) (r.solution h t) n
  have h1 := congrArg (fun x : Sequence => x n) (solution_fixed r h s)
  have h2 := congrArg (fun x : Sequence => x n) (solution_fixed r h t)
  change r.perronValue s (r.solution h s) n=r.solution h s n at h1
  change r.perronValue t (r.solution h t) n=r.solution h t n at h2
  rwa [h1,h2] at hh

end StandardMapEntropy.NonlinearStable

end
section
namespace StandardMapEntropy.NonlinearStable
open Filter
open scoped Topology NNReal
variable {ℓ δ : ℝ≥0}

lemma orbit_fixed (r : Recurrence ℓ δ) (h : ℓ+δ<1) (s : ℝ) (x : Sequence)
    (h0 : (x 0).1=s) (horbit : ∀ n, x (n+1)=r.step n (x n)) :
    r.perron (le_trans (le_add_of_nonneg_right (show (0 : ℝ≥0)≤δ from bot_le)) h.le) s x=x := by
  apply BoundedContinuousFunction.ext
  intro n
  apply Prod.ext
  · cases n with
    | zero => exact h0.symm
    | succ n => exact (congrArg Prod.fst (horbit n)).symm
  · have hh := congrArg Prod.snd (horbit n)
    change (x (n+1)).2=r.b n*(x n).2+(r.remainder n (x n)).2 at hh
    change (r.b n)⁻¹*((x (n+1)).2-(r.remainder n (x n)).2)=(x n).2
    rw [hh,add_sub_cancel_right,←mul_assoc,inv_mul_cancel₀ (r.b_ne n),one_mul]

lemma solution_unique (r : Recurrence ℓ δ) (h : ℓ+δ<1) (s : ℝ) (x : Sequence)
    (h0 : (x 0).1=s) (horbit : ∀ n, x (n+1)=r.step n (x n)) :
    x=r.solution h s :=
  (perron_contracting r h (s := s)).fixedPoint_unique (orbit_fixed r h s x h0 horbit)

lemma solution_tail (r : Recurrence ℓ δ) (h : ℓ+δ<1) (s : ℝ) (m : ℕ) :
    (r.solution h s).tail m=(r.tail m).solution h (r.solution h s m).1 := by
  apply solution_unique
  · simp only [tail_apply,Nat.add_zero]
  · intro n
    simpa only [tail_apply,Recurrence.tail,Recurrence.step,Nat.add_assoc] using
      solution_orbit r h s (m+n)

lemma solution_cone (r : Recurrence ℓ δ) (h : ℓ+δ<1) (s t : ℝ) (n : ℕ) :
    ‖r.solution h s n-r.solution h t n‖≤|(r.solution h s n).1-(r.solution h t n).1| := by
  have hh := solution_lipschitz (r.tail n) h (r.solution h s n).1 (r.solution h t n).1
  rw [←solution_tail,←solution_tail] at hh
  have hb := (point_sub_bound ((r.solution h s).tail n) ((r.solution h t).tail n) 0).trans hh
  simpa only [tail_apply,Nat.add_zero] using hb

lemma step_fst_sub_bound (r : Recurrence ℓ δ) (n : ℕ) (v w : Plane) :
    |(r.step n v).1-(r.step n w).1|≤((ℓ+δ : ℝ≥0) : ℝ)*‖v-w‖ := by
  have hr := (r.lipschitz n).dist_le_mul v w
  rw [dist_eq_norm,dist_eq_norm] at hr
  have hrf := (norm_fst_le (r.remainder n v-r.remainder n w)).trans hr
  have hvw : |v.1-w.1|≤‖v-w‖ := norm_fst_le (v-w)
  change |r.a n*v.1+(r.remainder n v).1-(r.a n*w.1+(r.remainder n w).1)|≤_
  calc
    _ = |r.a n*(v.1-w.1)+((r.remainder n v).1-(r.remainder n w).1)| := by congr 1; ring
    _ ≤ |r.a n| * |v.1-w.1|+|(r.remainder n v).1-(r.remainder n w).1| := by
      simpa only [abs_mul] using abs_add_le (r.a n*(v.1-w.1)) ((r.remainder n v).1-(r.remainder n w).1)
    _ ≤ (ℓ : ℝ)*‖v-w‖+(δ : ℝ)*‖v-w‖ := add_le_add
      (mul_le_mul (r.stable_bound n) hvw (abs_nonneg _) ℓ.coe_nonneg) hrf
    _ = _ := by push_cast; ring

lemma solution_step_contraction (r : Recurrence ℓ δ) (h : ℓ+δ<1) (s t : ℝ) (n : ℕ) :
    ‖r.solution h s (n+1)-r.solution h t (n+1)‖≤
      ((ℓ+δ : ℝ≥0) : ℝ)*‖r.solution h s n-r.solution h t n‖ := by
  apply (solution_cone r h s t (n+1)).trans
  rw [solution_orbit,solution_orbit]
  exact step_fst_sub_bound r n _ _

lemma solution_exponential_contraction (r : Recurrence ℓ δ) (h : ℓ+δ<1) (s t : ℝ) (n : ℕ) :
    ‖r.solution h s n-r.solution h t n‖≤((ℓ+δ : ℝ≥0) : ℝ)^n*|s-t| := by
  induction n with
  | zero => simpa only [pow_zero,one_mul,solution_initial] using solution_cone r h s t 0
  | succ n ih =>
    apply (solution_step_contraction r h s t n).trans
    calc
      _ ≤ ((ℓ+δ : ℝ≥0) : ℝ)*(((ℓ+δ : ℝ≥0) : ℝ)^n*|s-t|) :=
        mul_le_mul_of_nonneg_left ih (ℓ+δ).coe_nonneg
      _ = _ := by rw [pow_succ]; ring

end StandardMapEntropy.NonlinearStable

end
section
namespace StandardMapEntropy
open MeasureTheory Set Filter
open scoped Topology NNReal

lemma flat_diagonal {q p : ℝ} (D F C : ℂ →L[ℝ] ℂ) {a b : ℝ}
    (h : C.comp (D.comp F)=diagonalPlane a b) (v : RealPlane) :
    flatInverse p C (D (flatFrame q F v))=(q/p*a*v.1,q/p*b*v.2) := by
  have hh : C (D (F (pairToComplex v)))=diagonalPlane a b (pairToComplex v) :=
    congrArg (fun T : ℂ →L[ℝ] ℂ => T (pairToComplex v)) h
  simp only [flatInverse,flatFrame,ContinuousLinearMap.comp_apply,smul_apply,map_smul]
  rw [hh]
  simp only [diagonalPlane_apply,complexToPair_apply,pairToComplex_apply]
  apply Prod.ext <;> simp only [Prod.smul_fst,Prod.smul_snd,smul_eq_mul,div_eq_mul_inv] <;> ring

end StandardMapEntropy

end
end

end OAI
end

section
-- module Solutions.OAIQ44_CM.StandardMap_Entropy_LiftGrid
attribute [-instance] _root_.OAI.StandardMapEntropy.LocalCoding.optionFinsetMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace StandardMapEntropy.Entropy
open Set Finset
open scoped BigOperators

lemma shannon_nonneg {α : Type*} [Fintype α] (p : α → ℝ)
    (hp : ∀ a, 0≤p a) (hm : ∑ a,p a≤1) : 0 ≤ shannon p := by
  apply Finset.sum_nonneg
  intro a _
  exact Real.negMulLog_nonneg (hp a) ((Finset.single_le_sum (fun b _ => hp b) (Finset.mem_univ a)).trans hm)

lemma shannon_scale {α : Type*} [Fintype α] (p : α → ℝ) (c : ℝ) :
    shannon (fun a => c*p a)=c*shannon p+(∑ a,p a)*Real.negMulLog c := by
  simp only [shannon,Real.negMulLog_mul,Finset.sum_add_distrib,←Finset.mul_sum,←Finset.sum_mul]
  ring

lemma shannon_bound {α : Type*} [Fintype α] [Nonempty α] (p : α → ℝ)
    (hp : ∀ a, 0≤p a) (hm : ∑ a,p a=1) : shannon p≤Real.log (Fintype.card α) := by
  have hc : 0<(Fintype.card α : ℝ) := by exact_mod_cast Fintype.card_pos
  have hh := shannon_le_cross p (fun _ => (Fintype.card α : ℝ)⁻¹) hp
    (fun _ => (inv_pos.mpr hc).le) (fun _ _ => inv_ne_zero hc.ne') (by simp [hm,hc.ne'])
  rw [←Finset.sum_mul,hm,one_mul,Real.log_inv,neg_neg] at hh
  exact hh

lemma shannon_total_bound {α : Type*} [Fintype α] (p : α → ℝ)
    (hp : ∀ a, 0≤p a) : shannon p≤Real.negMulLog (∑ a,p a)+(∑ a,p a)*Real.log (Fintype.card α) := by
  let T : ℝ := ∑ a,p a
  have hT : 0≤T := Finset.sum_nonneg (fun a _ => hp a)
  by_cases he : T=0
  · have hz (a : α) : p a=0 := le_antisymm
      ((Finset.single_le_sum (fun b _ => hp b) (Finset.mem_univ a) : p a≤T).trans_eq he) (hp a)
    simp only [shannon,hz,Finset.sum_const_zero,Real.negMulLog_zero,zero_mul,add_zero,le_refl]
  have hT' : 0<T := lt_of_le_of_ne hT (Ne.symm he)
  have : Nonempty α := by
    by_contra h
    have : IsEmpty α := not_nonempty_iff.mp h
    exact he (by dsimp [T]; simp)
  let q : α → ℝ := fun a => p a/T
  have hq (a : α) : 0≤q a := div_nonneg (hp a) hT
  have hmass : ∑ a,q a=1 := by dsimp [q]; rw [←Finset.sum_div]; exact div_self he
  have hb := mul_le_mul_of_nonneg_left (shannon_bound q hq hmass) hT
  have hs := shannon_scale q T
  have heq : (fun a => T*q a)=p := by funext a; dsimp [q]; field_simp
  rw [heq,hmass,one_mul] at hs
  change shannon p≤Real.negMulLog T+T*Real.log (Fintype.card α)
  linarith

lemma matrix_super_row {α β : Type*} [Fintype α] [Fintype β]
    (p : α → β → ℝ) (hp : ∀ a b, 0≤p a b) :
    shannon (fun a => ∑ b,p a b)≤ shannon (fun ab : α×β => p ab.1 ab.2) := by
  have hh (a : α) (b : β) : -p a b*Real.log (∑ j,p a j)≤Real.negMulLog (p a b) := by
    by_cases he : p a b=0
    · simp [he]
    have hpos : 0<p a b := lt_of_le_of_ne (hp a b) (Ne.symm he)
    have hlog := Real.log_le_log hpos (matrix_le_row p hp a b)
    exact mul_le_mul_of_nonpos_left hlog (neg_nonpos.mpr (hp a b))
  have hs := Finset.sum_le_sum (s:=Finset.univ) (fun a _ => Finset.sum_le_sum (s:=Finset.univ) (fun b _ => hh a b))
  simp only [neg_mul,←Finset.sum_mul,Finset.sum_neg_distrib] at hs
  simpa only [shannon,Fintype.sum_prod_type,Real.negMulLog,neg_mul,Finset.sum_neg_distrib] using hs

end StandardMapEntropy.Entropy

end
end

end OAI
end

section
-- module Solutions.OAIQ44_CM.StandardMap_Entropy_ObservableEntropy
attribute [-instance] _root_.OAI.StandardMapEntropy.LocalCoding.optionFinsetMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace StandardMapEntropy.Entropy
open MeasureTheory Set Filter
open scoped BigOperators ENNReal
variable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsFiniteMeasure μ]
variable {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ]
variable [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ]
variable [MeasurableSingletonClass α] [MeasurableSingletonClass β] [MeasurableSingletonClass γ]

omit [IsFiniteMeasure μ] [MeasurableSpace α] [MeasurableSpace β]
  [MeasurableSingletonClass α] [MeasurableSingletonClass β] in
lemma obs_pair_swap (p : Ω → α) (q : Ω → β) :
    obs μ (fun x => (p x,q x))=obs μ (fun x => (q x,p x)) := by
  simp only [obs,shannon,Fintype.sum_prod_type]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl (fun b _ => Finset.sum_congr rfl (fun a _ => congrArg Real.negMulLog (mass_joint_swap μ p q a b)))

lemma obs_pair_ge_left (p : Ω → α) (q : Ω → β) (hp : Measurable p) (hq : Measurable q) :
    obs μ p ≤ obs μ (fun x => (p x,q x)) := by
  have h := matrix_super_row (fun a b => mass μ (fun x => (p x,q x)) (a,b))
    (fun a b => mass_nonneg μ _ _)
  simpa only [obs,Prod.mk.eta,←mass_joint_row μ p q hp hq] using h
lemma obs_pair_ge_right (p : Ω → α) (q : Ω → β) (hp : Measurable p) (hq : Measurable q) :
    obs μ q ≤ obs μ (fun x => (p x,q x)) := by
  rw [obs_pair_swap]
  exact obs_pair_ge_left μ q p hq hp

omit [IsFiniteMeasure μ] [Fintype α] [Fintype β] [MeasurableSpace α] [MeasurableSpace β]
  [MeasurableSingletonClass α] [MeasurableSingletonClass β] in
lemma mass_pair_function [DecidableEq β] (p : Ω → α) (g : α → β) (a : α) (b : β) :
    mass μ (fun x => (p x,g (p x))) (a,b)=if g a=b then mass μ p a else 0 := by
  classical
  by_cases h : g a=b
  · rw [ite_eq_left h]
    unfold mass
    congr 2
    ext x
    simp only [mem_preimage,mem_singleton_iff,Prod.mk.injEq]
    exact ⟨And.left,fun hp => ⟨hp,hp ▸ h⟩⟩
  · rw [ite_eq_right h]
    have he : ((fun x => (p x,g (p x))) ⁻¹' {(a,b)})=∅ := by
      apply eq_empty_iff_forall_notMem.mpr
      intro x hx
      exact h ((congrArg g (Prod.mk.inj hx).1).symm.trans (Prod.mk.inj hx).2)
    simp only [mass,he,measure_empty,ENNReal.toReal_zero]
omit [IsFiniteMeasure μ] [MeasurableSpace α] [MeasurableSpace β]
  [MeasurableSingletonClass α] [MeasurableSingletonClass β] in
lemma obs_pair_function (p : Ω → α) (g : α → β) :
    obs μ (fun x => (p x,g (p x)))=obs μ p := by
  classical
  simp only [obs,shannon,Fintype.sum_prod_type,mass_pair_function]
  apply Finset.sum_congr rfl
  intro a _
  simp only [apply_ite Real.negMulLog,Real.negMulLog_zero,Finset.sum_ite_eq,Finset.mem_univ,ite_true]

end StandardMapEntropy.Entropy

end
section
namespace StandardMapEntropy.Entropy
open MeasureTheory Set Filter
open scoped BigOperators ENNReal
variable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsFiniteMeasure μ]
variable {α β γ ζ : Type*} [Fintype α] [Fintype β] [Fintype γ] [Fintype ζ]
variable [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ] [MeasurableSpace ζ]
variable [MeasurableSingletonClass α] [MeasurableSingletonClass β] [MeasurableSingletonClass γ] [MeasurableSingletonClass ζ]

omit [IsFiniteMeasure μ] [Fintype α] [Fintype β] [Fintype γ]
  [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ]
  [MeasurableSingletonClass α] [MeasurableSingletonClass β] [MeasurableSingletonClass γ] in
lemma mass_triple_assoc (p : Ω → α) (q : Ω → β) (r : Ω → γ) (a : α) (b : β) (c : γ) :
    mass μ (fun x => (p x,(q x,r x))) (a,(b,c))=
      mass μ (fun x => ((p x,q x),r x)) ((a,b),c) := by
  unfold mass
  congr 2
  ext x
  simp only [mem_preimage,mem_singleton_iff,Prod.mk.injEq,and_assoc]
omit [IsFiniteMeasure μ] [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ]
  [MeasurableSingletonClass α] [MeasurableSingletonClass β] [MeasurableSingletonClass γ] in
lemma obs_triple_assoc (p : Ω → α) (q : Ω → β) (r : Ω → γ) :
    obs μ (fun x => (p x,(q x,r x)))=obs μ (fun x => ((p x,q x),r x)) := by
  simpa only [Function.comp_def,Equiv.prodAssoc_apply] using obs_equiv μ (fun x => ((p x,q x),r x)) (Equiv.prodAssoc α β γ)

lemma obs_strong_subadd (p : Ω → α) (q : Ω → β) (r : Ω → γ)
    (hp : Measurable p) (hq : Measurable q) (hr : Measurable r) :
    obs μ (fun x => (p x,(q x,r x)))+obs μ q ≤
      obs μ (fun x => (p x,q x))+obs μ (fun x => (q x,r x)) := by
  let P : α → β → γ → ℝ := fun a b c => mass μ (fun x => (p x,(q x,r x))) (a,(b,c))
  have hrow (a : α) (b : β) : ∑ c,P a b c=mass μ (fun x => (p x,q x)) (a,b) := by
    simp only [P,mass_triple_assoc]
    exact (mass_joint_row μ _ r (hp.prodMk hq) hr (a,b)).symm
  have hcol (b : β) (c : γ) : ∑ a,P a b c=mass μ (fun x => (q x,r x)) (b,c) :=
    (mass_joint_col μ p _ hp (hq.prodMk hr) (b,c)).symm
  have htotal (b : β) : ∑ a,∑ c,P a b c=mass μ q b := by
    simp only [hrow]
    exact (mass_joint_col μ p q hp hq b).symm
  have hb (b : β) := matrix_subadd (fun a c => P a b c) (fun a c => mass_nonneg μ _ _)
  have hh := Finset.sum_le_sum (s:=Finset.univ) (fun b _ => hb b)
  simp only [shannon,Fintype.sum_prod_type,hrow,hcol,Finset.sum_sub_distrib,Finset.sum_add_distrib] at hh
  simp only [←mass_joint_col μ p q hp hq] at hh
  rw [Finset.sum_comm (f:=fun b a => ∑ c,Real.negMulLog (P a b c)),
    Finset.sum_comm (f:=fun b a => Real.negMulLog (mass μ (fun x => (p x,q x)) (a,b)))] at hh
  have h : obs μ (fun x => (p x,(q x,r x))) ≤
      obs μ (fun x => (p x,q x))+obs μ (fun x => (q x,r x))-obs μ q := by
    simpa only [obs,shannon,Fintype.sum_prod_type] using hh
  linarith

lemma cond_nonneg (p : Ω → α) (q : Ω → β) (hp : Measurable p) (hq : Measurable q) : 0 ≤ cond μ p q :=
  sub_nonneg.mpr (obs_pair_ge_right μ p q hp hq)
lemma cond_le_obs [IsProbabilityMeasure μ] (p : Ω → α) (q : Ω → β) (hp : Measurable p) (hq : Measurable q) :
    cond μ p q ≤ obs μ p := sub_le_iff_le_add.mpr (obs_pair_subadd_prob μ p q hp hq)
lemma cond_pair_right (p : Ω → α) (q : Ω → β) (r : Ω → γ)
    (hp : Measurable p) (hq : Measurable q) (hr : Measurable r) :
    cond μ p (fun x => (q x,r x)) ≤ cond μ p q := by
  have h := obs_strong_subadd μ p q r hp hq hr
  dsimp [cond]
  linarith
omit [IsFiniteMeasure μ] [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ]
  [MeasurableSingletonClass α] [MeasurableSingletonClass β] [MeasurableSingletonClass γ] in
lemma cond_pair_swap_right (p : Ω → α) (q : Ω → β) (r : Ω → γ) :
    cond μ p (fun x => (q x,r x))=cond μ p (fun x => (r x,q x)) := by
  have he : obs μ (fun x => (p x,(r x,q x)))=obs μ (fun x => (p x,(q x,r x))) := by
    simpa only [Function.comp_def,Equiv.prodCongr_apply,Prod.map_apply,Equiv.refl_apply,Equiv.prodComm_apply,Prod.swap_prod_mk] using
      obs_equiv μ (fun x => (p x,(q x,r x))) (Equiv.prodCongr (Equiv.refl α) (Equiv.prodComm β γ))
  unfold cond
  rw [he,obs_pair_swap μ q r]

omit [IsFiniteMeasure μ] [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ]
  [MeasurableSingletonClass α] [MeasurableSingletonClass β] [MeasurableSingletonClass γ] in
lemma cond_chain (p : Ω → α) (q : Ω → β) (r : Ω → γ) :
    cond μ (fun x => (p x,r x)) q=cond μ p q+cond μ r (fun x => (p x,q x)) := by
  have h1 := obs_pair_swap μ (fun x => (p x,r x)) q
  have h2 := obs_triple_assoc μ q p r
  have h3 := obs_pair_swap μ (fun x => (q x,p x)) r
  have h4 := cond_pair_swap_right μ r q p
  unfold cond at *
  have h5 := obs_pair_swap μ p q
  linarith
lemma cond_factor_right (p : Ω → α) (q : Ω → β) (g : β → γ)
    (hp : Measurable p) (hq : Measurable q) :
    cond μ p q ≤ cond μ p (g ∘ q) := by
  have hg : Measurable (g ∘ q) := (measurable_of_countable g).comp hq
  have h := cond_pair_right μ p (g ∘ q) q hp hg hq
  have he0 : cond μ p (fun x => (q x,g (q x)))=cond μ p q := by
    unfold cond
    dsimp only
    rw [obs_triple_assoc]
    rw [show obs μ (fun x => ((p x,q x),g (q x)))=obs μ (fun x => (p x,q x)) from
      obs_pair_function μ (fun x => (p x,q x)) (fun v : α×β => g v.2)]
    rw [obs_pair_function μ q g]
  have he : cond μ p (fun x => (g (q x),q x))=cond μ p q :=
    (cond_pair_swap_right μ p (g ∘ q) q).trans he0
  calc
    cond μ p q = cond μ p (fun x => (g (q x),q x)) := he.symm
    _ ≤ cond μ p (g ∘ q) := h

lemma cond_pair_subadd (p : Ω → α) (q : Ω → β) (r : Ω → γ) (s : Ω → ζ)
    (hp : Measurable p) (hq : Measurable q) (hr : Measurable r) (hs : Measurable s) :
    cond μ (fun x => (p x,r x)) (fun x => (q x,s x)) ≤ cond μ p q+cond μ r s := by
  rw [cond_chain]
  apply add_le_add (cond_pair_right μ p q s hp hq hs)
  exact cond_factor_right μ r (fun x => (p x,(q x,s x))) (fun v : α×(β×ζ) => v.2.2) hr (hp.prodMk (hq.prodMk hs))

end StandardMapEntropy.Entropy

end
section
namespace StandardMapEntropy.Entropy
open MeasureTheory Set Filter
open scoped BigOperators ENNReal Topology
variable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
variable {α β : Type*} [Fintype α] [Fintype β]
variable [MeasurableSpace α] [MeasurableSpace β]
variable [MeasurableSingletonClass α] [MeasurableSingletonClass β]

lemma obs_nonneg (p : Ω → α) (hp : Measurable p) : 0 ≤ obs μ p := by
  apply shannon_nonneg _ (mass_nonneg μ p)
  rw [mass_sum μ p hp,measure_univ,ENNReal.toReal_one]
omit [MeasurableSpace α] [MeasurableSingletonClass α] in
lemma obs_const [Nonempty α] (a : α) : obs μ (fun _ : Ω => a)=0 := by
  classical
  have he (b : α) : mass μ (fun _ : Ω => a) b=if a=b then 1 else 0 := by
    unfold mass
    by_cases h : a=b
    · subst b; simp
    · have hs : (fun _ : Ω => a) ⁻¹' {b}=∅ := by ext x; simp [h]
      simp [hs,h]
  simp only [obs,shannon,he,apply_ite Real.negMulLog,Real.negMulLog_one,Real.negMulLog_zero,ite_self,Finset.sum_const_zero]

omit [IsProbabilityMeasure μ] in
lemma cond_comp_preserving (f : Ω → Ω) (hf : MeasurePreserving f μ μ) (p : Ω → α) (q : Ω → β)
    (hp : Measurable p) (hq : Measurable q) : cond μ (p ∘ f) (q ∘ f)=cond μ p q := by
  unfold cond
  rw [show (fun x => ((p ∘ f) x,(q ∘ f) x))=(fun x => (p x,q x)) ∘ f from rfl,
    obs_comp_preserving μ f hf _ (hp.prodMk hq),obs_comp_preserving μ f hf q hq]

omit [MeasurableSpace α] [MeasurableSingletonClass α] in
lemma obs_word_zero (f : Ω → Ω) (p : Ω → α) : obs μ (word f p 0)=0 := by
  have he : word f p 0=(fun _ : Ω => (fun i : Fin 0 => Fin.elim0 i)) := by funext x i; exact i.elim0
  rw [he,obs_const]

omit [IsProbabilityMeasure μ] [MeasurableSpace α] [MeasurableSpace β]
  [MeasurableSingletonClass α] [MeasurableSingletonClass β] in
lemma cond_equiv_left (p : Ω → α) (q : Ω → β)
    {γ : Type*} [Fintype γ] [MeasurableSpace γ] [MeasurableSingletonClass γ] (e : α ≃ γ) :
    cond μ (e ∘ p) q=cond μ p q := by
  have h := obs_equiv μ (fun x => (p x,q x)) (Equiv.prodCongr e (Equiv.refl β))
  unfold cond
  rw [show obs μ (fun x => ((e ∘ p) x,q x))=obs μ (fun x => (p x,q x)) from
    by simpa only [Function.comp_def,Equiv.prodCongr_apply,Prod.map_apply,Equiv.refl_apply] using h]
omit [IsProbabilityMeasure μ] [MeasurableSpace α] [MeasurableSpace β]
  [MeasurableSingletonClass α] [MeasurableSingletonClass β] in
lemma cond_equiv_right (p : Ω → α) (q : Ω → β)
    {γ : Type*} [Fintype γ] [MeasurableSpace γ] [MeasurableSingletonClass γ] (e : β ≃ γ) :
    cond μ p (e ∘ q)=cond μ p q := by
  have h := obs_equiv μ (fun x => (p x,q x)) (Equiv.prodCongr (Equiv.refl α) e)
  unfold cond
  rw [show obs μ (fun x => (p x,(e ∘ q) x))=obs μ (fun x => (p x,q x)) from
    by simpa only [Function.comp_def,Equiv.prodCongr_apply,Prod.map_apply,Equiv.refl_apply] using h,
    obs_equiv μ q e]
omit [IsProbabilityMeasure μ] in
lemma cond_word_split (f : Ω → Ω) (p : Ω → α) (q : Ω → β) (n m : ℕ) :
    cond μ (word f p (n+m)) (word f q (n+m))=
      cond μ (fun x => (word f p n x,word f p m (f^[n] x)))
        (fun x => (word f q n x,word f q m (f^[n] x))) := by
  rw [←cond_equiv_left μ (word f p (n+m)) (word f q (n+m)) (wordSplit n m),
    ←cond_equiv_right μ ((wordSplit n m) ∘ word f p (n+m)) (word f q (n+m)) (wordSplit n m)]
  simp only [Function.comp_def,word_split]
lemma cond_word_subadd (f : Ω → Ω) (hf : MeasurePreserving f μ μ) (p : Ω → α) (q : Ω → β)
    (hp : Measurable p) (hq : Measurable q) :
    Subadditive (fun n => cond μ (word f p n) (word f q n)) := by
  intro n m
  dsimp only
  rw [cond_word_split]
  have h := cond_pair_subadd μ (word f p n) (word f q n) ((word f p m) ∘ f^[n]) ((word f q m) ∘ f^[n])
    (word_measurable f hf.measurable p hp n) (word_measurable f hf.measurable q hq n)
    ((word_measurable f hf.measurable p hp m).comp (hf.measurable.iterate n))
    ((word_measurable f hf.measurable q hq m).comp (hf.measurable.iterate n))
  rw [cond_comp_preserving μ (f^[n]) (hf.iterate n) _ _
    (word_measurable f hf.measurable p hp m) (word_measurable f hf.measurable q hq m)] at h
  exact h
omit [IsProbabilityMeasure μ] in
lemma cond_word_one (f : Ω → Ω) (p : Ω → α) (q : Ω → β)
    (_hp : Measurable p) (_hq : Measurable q) :
    cond μ (word f p 1) (word f q 1)=cond μ p q := by
  have hp0 : (Equiv.funUnique (Fin 1) α) ∘ word f p 1=p := by
    funext x
    simp [word,Equiv.funUnique,Fin.default_eq_zero]
  have hq0 : (Equiv.funUnique (Fin 1) β) ∘ word f q 1=q := by
    funext x
    simp [word,Equiv.funUnique,Fin.default_eq_zero]
  rw [←cond_equiv_left μ (word f p 1) (word f q 1) (Equiv.funUnique (Fin 1) α),hp0,
    ←cond_equiv_right μ p (word f q 1) (Equiv.funUnique (Fin 1) β),hq0]
omit [MeasurableSpace α] [MeasurableSpace β]
  [MeasurableSingletonClass α] [MeasurableSingletonClass β] in
lemma cond_word_zero (f : Ω → Ω) (p : Ω → α) (q : Ω → β) :
    cond μ (word f p 0) (word f q 0)=0 := by
  have hp : word f p 0=(fun _ : Ω => (fun i : Fin 0 => Fin.elim0 i)) := by funext x i; exact i.elim0
  have hq : word f q 0=(fun _ : Ω => (fun i : Fin 0 => Fin.elim0 i)) := by funext x i; exact i.elim0
  simp only [cond,hp,hq,obs_const,sub_self]
lemma cond_word_bound (f : Ω → Ω) (hf : MeasurePreserving f μ μ) (p : Ω → α) (q : Ω → β)
    (hp : Measurable p) (hq : Measurable q) (n : ℕ) :
    cond μ (word f p n) (word f q n) ≤ n*cond μ p q := by
  induction n with
  | zero => simp only [cond_word_zero,Nat.cast_zero,zero_mul,le_refl]
  | succ n ih =>
    have h := cond_word_subadd μ f hf p q hp hq n 1
    change cond μ (word f p (n+1)) (word f q (n+1))≤
      cond μ (word f p n) (word f q n)+cond μ (word f p 1) (word f q 1) at h
    rw [cond_word_one μ f p q hp hq] at h
    calc
      _ ≤ cond μ (word f p n) (word f q n)+cond μ p q := h
      _ ≤ n*cond μ p q+cond μ p q := add_le_add ih le_rfl
      _ = _ := by push_cast; ring

lemma obs_word_bddBelow (f : Ω → Ω) (hf : Measurable f) (p : Ω → α) (hp : Measurable p) :
    BddBelow (Set.range (fun n : ℕ => obs μ (word f p n)/(n : ℝ))) := by
  refine ⟨0,?_⟩
  rintro _ ⟨n,rfl⟩
  exact div_nonneg (obs_nonneg μ _ (word_measurable f hf p hp n)) (Nat.cast_nonneg n)

end StandardMapEntropy.Entropy

end
section
namespace StandardMapEntropy.Entropy
open MeasureTheory Set Filter
open scoped BigOperators ENNReal Topology
variable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
variable {α β : Type*} [Fintype α] [Fintype β]
variable [MeasurableSpace α] [MeasurableSpace β]
variable [MeasurableSingletonClass α] [MeasurableSingletonClass β]

lemma rate_eq_lim (f : Ω → Ω) (hf : MeasurePreserving f μ μ) (p : Ω → α) (hp : Measurable p) :
    rate μ f p=(obs_word_subadd μ f hf p hp).lim := by
  rw [Subadditive.lim]; rfl
lemma rate_tendsto (f : Ω → Ω) (hf : MeasurePreserving f μ μ) (p : Ω → α) (hp : Measurable p) :
    Tendsto (fun n : ℕ => obs μ (word f p n)/(n : ℝ)) atTop (𝓝 (rate μ f p)) := by
  rw [rate_eq_lim μ f hf p hp]
  exact (obs_word_subadd μ f hf p hp).tendsto_lim (obs_word_bddBelow μ f hf.measurable p hp)
lemma rate_nonneg (f : Ω → Ω) (hf : MeasurePreserving f μ μ) (p : Ω → α) (hp : Measurable p) :
    0 ≤ rate μ f p :=
  ge_of_tendsto' (rate_tendsto μ f hf p hp) (fun n => div_nonneg
    (obs_nonneg μ _ (word_measurable f hf.measurable p hp n)) (Nat.cast_nonneg n))

end StandardMapEntropy.Entropy

end
end

end OAI
end

section
-- module Solutions.OAIQ44_CM.StandardMap_Stable_LocalStable
attribute [-instance] _root_.OAI.StandardMapEntropy.LocalCoding.optionFinsetMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace StandardMapEntropy.NonlinearStable
open Filter
open scoped Topology NNReal

variable {ℓ δ : ℝ≥0}

lemma extend_step_eq (r : LocalRecurrence ℓ δ) (n : ℕ) {v : Plane} (hv : ‖v‖≤1) :
    r.extend.step n v=r.step n v := by
  simp only [LocalRecurrence.extend,Recurrence.step,LocalRecurrence.step,planeClip_eq hv]

lemma local_solution_orbit (r : LocalRecurrence ℓ δ) (h : ℓ+δ<1) {s : ℝ} (hs : |s|≤1) (n : ℕ) :
    r.extend.solution h s (n+1)=r.step n (r.extend.solution h s n) := by
  rw [solution_orbit,extend_step_eq r n (local_solution_bound r h hs n)]

end StandardMapEntropy.NonlinearStable

end
end

end OAI
end

section
-- module Solutions.OAIQ44_CM.StandardMap_Stable_PerronStability
attribute [-instance] _root_.OAI.StandardMapEntropy.LocalCoding.optionFinsetMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace StandardMapEntropy
open MeasureTheory Set Filter
open scoped Topology ENNReal

lemma tangentReversal_inverseLift (k : ℝ) (w : ℂ) :
    tangentReversal (standardInverseLift k w)=standardLift k (tangentReversal w) := by
  apply Complex.ext <;> simp [standardInverseLift,standardLift] <;> ring
lemma tangentReversal_inverse_lift_iterate (k : ℝ) (n : ℕ) (w : ℂ) :
    tangentReversal ((standardInverseLift k)^[n] w)=(standardLift k)^[n] (tangentReversal w) := by
  induction n with
  | zero => rfl
  | succ n ih => rw [Function.iterate_succ_apply',tangentReversal_inverseLift,ih,Function.iterate_succ_apply']
lemma inverse_lift_iterate_reversed (k : ℝ) (n : ℕ) (w : ℂ) :
    (standardInverseLift k)^[n] (tangentReversal w)=tangentReversal ((standardLift k)^[n] w) := by
  have hh := congrArg tangentReversal (tangentReversal_inverse_lift_iterate k n (tangentReversal w))
  simpa only [tangentReversal_involutive] using hh
lemma tangentReversal_norm_le (w : ℂ) : ‖tangentReversal w‖≤3*‖w‖ := by
  have hh := Complex.norm_le_abs_re_add_abs_im (tangentReversal w)
  simp only [tangentReversal_re,tangentReversal_im,abs_neg] at hh
  have hh' := abs_sub w.re w.im
  have hr := Complex.abs_re_le_norm w
  have hi := Complex.abs_im_le_norm w
  linarith

end StandardMapEntropy

end
end

end OAI
end

section
-- module Solutions.OAIQ44_CM.StandardMap_Entropy_SupportEntropy
attribute [-instance] _root_.OAI.StandardMapEntropy.LocalCoding.optionFinsetMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace StandardMapEntropy.Entropy
open MeasureTheory Set Filter
open scoped BigOperators ENNReal
variable {α β : Type*} [Fintype α] [Fintype β]

lemma shannon_support_bound (p : α → ℝ) (hp : ∀ a,0≤p a) (s : Finset α)
    (hs : ∀ a,a∉s → p a=0) :
    shannon p≤Real.negMulLog (∑ a,p a)+(∑ a,p a)*Real.log (s.card : ℝ) := by
  classical
  have hsum : ∑ a : s,p a=∑ a,p a := by
    rw [Finset.sum_coe_sort]
    exact Finset.sum_subset (Finset.subset_univ s) (fun a _ ha => hs a ha)
  have hent : shannon (fun a : s => p a)=shannon p := by
    unfold shannon
    dsimp only
    rw [←Finset.sum_subtype s (fun a => Iff.rfl) (fun a => Real.negMulLog (p a))]
    exact Finset.sum_subset (Finset.subset_univ s) (fun a _ ha => by rw [hs a ha,Real.negMulLog_zero])
  have h := shannon_total_bound (fun a : s => p a) (fun a => hp a)
  simpa only [hent,hsum,Fintype.card_coe] using h

variable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsFiniteMeasure μ]
variable [MeasurableSpace α] [MeasurableSpace β]
variable [MeasurableSingletonClass α] [MeasurableSingletonClass β]
lemma cond_support_bound (p : Ω → α) (q : Ω → β) (hp : Measurable p) (hq : Measurable q)
    (S : β → Finset α) (hS : ∀ x,p x∈S (q x)) :
    cond μ p q≤∑ b,mass μ q b*Real.log ((S b).card : ℝ) := by
  classical
  have rz (b : β) (a : α) (ha : a∉S b) : mass μ (fun x => (p x,q x)) (a,b)=0 := by
    have he : (fun x => (p x,q x)) ⁻¹' {(a,b)}=∅ := by
      apply Set.eq_empty_iff_forall_notMem.mpr
      intro x hx
      obtain ⟨hx1,hx2⟩ := Prod.mk.inj hx
      exact ha (hx1 ▸ hx2 ▸ hS x)
    simp only [mass,he,measure_empty,ENNReal.toReal_zero]
  have hh := Finset.sum_le_sum (s:=Finset.univ) (fun b _ =>
    shannon_support_bound (fun a => mass μ (fun x => (p x,q x)) (a,b))
      (fun a => mass_nonneg μ _ _) (S b) (rz b))
  simp only [←mass_joint_col μ p q hp hq,shannon,Finset.sum_add_distrib] at hh
  unfold cond obs shannon
  rw [Fintype.sum_prod_type,Finset.sum_comm]
  linarith

end StandardMapEntropy.Entropy
end
section
namespace StandardMapEntropy.Entropy
open MeasureTheory Set Filter
open scoped BigOperators ENNReal Topology
variable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
variable {α : Type*} [Fintype α] [MeasurableSpace α] [MeasurableSingletonClass α]

lemma errorObs_measurable (p q : Ω → α) (hp : Measurable p) (hq : Measurable q) :
    Measurable (errorObs p q) := by
  classical
  exact (measurable_of_countable (fun v : α×α => decide (v.1≠v.2))).comp (hp.prodMk hq)
lemma obs_bool (e : Ω → Bool) (he : Measurable e) :
    obs μ e=Real.negMulLog (mass μ e true)+Real.negMulLog (1-mass μ e true) := by
  have hm := mass_sum μ e he
  simp only [Fintype.sum_bool,measure_univ,ENNReal.toReal_one] at hm
  have hf : mass μ e false=1-mass μ e true := by linarith
  simp only [obs,shannon,Fintype.sum_bool,hf]

lemma cond_fano (p q : Ω → α) (hp : Measurable p) (hq : Measurable q) :
    cond μ p q≤obs μ (errorObs p q)+mass μ (errorObs p q) true*Real.log (Fintype.card α) := by
  classical
  let e := errorObs p q
  have he := errorObs_measurable p q hp hq
  let S : Bool×α → Finset α := fun v => if v.1 then Finset.univ else {v.2}
  have hs (x : Ω) : p x∈S (e x,q x) := by
    by_cases h : p x=q x <;> simp [S,e,errorObs,h]
  have hb := cond_support_bound μ p (fun x => (e x,q x)) hp (he.prodMk hq) S hs
  have hv : (∑ v : Bool×α,mass μ (fun x => (e x,q x)) v*Real.log ((S v).card : ℝ))=
      mass μ e true*Real.log (Fintype.card α) := by
    simp only [Fintype.sum_prod_type,Fintype.sum_bool,S,Bool.false_eq_true,↓reduceIte,
      Finset.card_univ,Finset.card_singleton,Nat.cast_one,Real.log_one,mul_zero,Finset.sum_const_zero,add_zero]
    rw [←Finset.sum_mul,←mass_joint_row μ e q he hq true]
  rw [hv] at hb
  have hm := obs_pair_ge_right μ e (fun x => (p x,q x)) he (hp.prodMk hq)
  rw [obs_triple_assoc] at hm
  have hc := cond_chain μ e q p
  have ho := cond_le_obs μ e q he hq
  unfold cond at hb hc ho ⊢
  linarith
lemma cond_fano_bound (p q : Ω → α) (hp : Measurable p) (hq : Measurable q) :
    cond μ p q≤Real.negMulLog (mass μ (errorObs p q) true)+
      Real.negMulLog (1-mass μ (errorObs p q) true)+
      mass μ (errorObs p q) true*Real.log (Fintype.card α) := by
  rw [←obs_bool μ _ (errorObs_measurable p q hp hq)]
  exact cond_fano μ p q hp hq

lemma cond_small_of_error (ε : ℝ) (hε : 0<ε) :
    ∃ η : ℝ,0<η ∧ ∀ (p q : Ω → α), Measurable p → Measurable q →
      mass μ (errorObs p q) true<η → cond μ p q<ε := by
  let B : ℝ → ℝ := fun d => Real.negMulLog d+Real.negMulLog (1-d)+d*Real.log (Fintype.card α)
  have hB : Continuous B := Real.continuous_negMulLog.add
    (Real.continuous_negMulLog.comp (continuous_const.sub continuous_id)) |>.add
      (continuous_id.mul continuous_const)
  have hB0 : B 0=0 := by simp [B]
  have hev : ∀ᶠ d in 𝓝 (0 : ℝ),B d<ε :=
    (hB.continuousAt : ContinuousAt B 0).eventually (gt_mem_nhds (show B 0<ε by rw [hB0]; exact hε))
  obtain ⟨η,hη,hball⟩ := Metric.mem_nhds_iff.mp hev
  refine ⟨η,hη,?_⟩
  intro p q hp hq he
  have hm := mass_nonneg μ (errorObs p q) true
  have hb := hball (show mass μ (errorObs p q) true∈Metric.ball 0 η from by
    simpa only [Metric.mem_ball,Real.dist_eq,sub_zero,abs_of_nonneg hm] using he)
  exact lt_of_le_of_lt (cond_fano_bound μ p q hp hq) hb

end StandardMapEntropy.Entropy

end
end

end OAI
end

section
-- module Solutions.OAIQ44_CM.StandardMap_Entropy_FineCharts
attribute [-instance] _root_.OAI.StandardMapEntropy.LocalCoding.optionFinsetMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace StandardMapEntropy
open MeasureTheory Set Filter
open scoped Topology NNReal ENNReal

lemma fineSize_le_scale (k χ ε : ℝ) {δ : ℝ} (hδ : 0<δ) (z : Torus) : fineSize k χ ε δ z≤fineScale k ε δ :=
  (mul_le_mul_of_nonneg_left (chartRadius_le_one k χ ε z) (fineScale_pos k ε hδ).le).trans_eq (mul_one _)

end StandardMapEntropy

end
section
namespace StandardMapEntropy
open MeasureTheory Set Filter
open scoped Topology NNReal ENNReal

lemma fine_derivative_diagonal (k χ ε δ : ℝ) (z : Torus) (hz : FineRegular k χ ε z) (v : RealPlane) :
    fineInverse k χ ε δ (standardMap k z) (standardDerivative k z (fineFrame k χ ε δ z v)) =
      (fineStableMultiplier k χ ε δ z*v.1,fineUnstableMultiplier k χ ε δ z*v.2) :=
  flat_diagonal _ _ _ hz.2.1 v
lemma fine_step (k χ ε δ : ℝ) (z : ℂ) (hz : FineRegular k χ ε (complexProjection z)) (v : RealPlane) :
    fineInverse k χ ε δ (standardMap k (complexProjection z))
      (standardLift k (z+fineFrame k χ ε δ (complexProjection z) v)-standardLift k z) =
      (fineStableMultiplier k χ ε δ (complexProjection z)*v.1+(fineRemainder k χ ε δ z v).1,
        fineUnstableMultiplier k χ ε δ (complexProjection z)*v.2+(fineRemainder k χ ε δ z v).2) := by
  have hdiff : standardLift k (z+fineFrame k χ ε δ (complexProjection z) v)-standardLift k z =
      standardDerivative k (complexProjection z) (fineFrame k χ ε δ (complexProjection z) v)+
        liftRemainder k z (fineFrame k χ ε δ (complexProjection z) v) := by unfold liftRemainder; abel
  rw [hdiff,map_add,fine_derivative_diagonal k χ ε δ _ hz]
  rfl
lemma fine_lift_step (k χ ε : ℝ) {δ : ℝ} (hδ : 0<δ) (z : ℂ)
    (hz : FineRegular k χ ε (complexProjection z)) (hn : FineRegular k χ ε (standardMap k (complexProjection z))) (v : RealPlane) :
    standardLift k (z+fineFrame k χ ε δ (complexProjection z) v) = standardLift k z+
      fineFrame k χ ε δ (standardMap k (complexProjection z))
        (fineStableMultiplier k χ ε δ (complexProjection z)*v.1+(fineRemainder k χ ε δ z v).1,
          fineUnstableMultiplier k χ ε δ (complexProjection z)*v.2+(fineRemainder k χ ε δ z v).2) := by
  have hh := congrArg (fineFrame k χ ε δ (standardMap k (complexProjection z))) (fine_step k χ ε δ z hz v)
  rw [fineFrame_inverse k χ ε hδ _ hn.1] at hh
  exact (sub_eq_iff_eq_add.mp hh).trans (add_comm _ _)

end StandardMapEntropy

end
end

end OAI
end

section
-- module Solutions.OAIQ44_CM.StandardMap_Entropy_PhysicalVolume
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace StandardMapEntropy
open MeasureTheory Set Filter
open scoped Topology ENNReal

lemma volume_pairToComplex_image {S : Set RealPlane} (hS : MeasurableSet S) :
    volume (pairToComplex '' S)=volume S := by
  have he : pairToComplex '' S=Complex.measurableEquivRealProd ⁻¹' S := by
    ext z
    constructor
    · rintro ⟨v,hv,rfl⟩; exact hv
    · intro hz
      exact ⟨complexToPair z,hz,pairToComplex_complexToPair z⟩
  rw [he]
  exact Complex.volume_preserving_equiv_real_prod.measure_preimage hS.nullMeasurableSet

end StandardMapEntropy

end
end

end OAI
end

section
-- module Solutions.OAIQ44_CM.StandardMap_Holonomy_FineStableGeometry
attribute [-instance] _root_.OAI.StandardMapEntropy.LocalCoding.optionFinsetMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace StandardMapEntropy
open MeasureTheory Set Filter
open scoped Topology NNReal ENNReal
open NonlinearStable

lemma fineStableCurve_orbit (k χ ε δ : ℝ) (hδ : 0<δ) (hq : Real.exp (-χ+ε)+δ<1)
    (w : ℂ) (hw : ∀ n : ℕ, FineRegular k χ ε (complexProjection ((standardLift k)^[n] w)))
    {s : ℝ} (hs : |s|≤1) (n : ℕ) :
    (standardLift k)^[n] (fineStableCurve k χ ε δ hδ hq w hw s)=(standardLift k)^[n] w+
      fineFrame k χ ε δ (complexProjection ((standardLift k)^[n] w))
        ((fineLocalRecurrence k χ ε δ hδ w hw).extend.solution hq s n) := by
  induction n with
  | zero =>
    have hi : (fineLocalRecurrence k χ ε δ hδ w hw).extend.solution hq s 0=
        (s,fineStableGraph k χ ε δ hδ hq w hw s) := Prod.ext (solution_initial _ _ s) rfl
    simp only [Function.iterate_zero,id_eq,hi,fineStableCurve]
  | succ n ih =>
    rw [Function.iterate_succ_apply',ih,fine_lift_step k χ ε hδ _ (hw n) (fine_regular_lift_next k χ ε w hw n)]
    rw [local_solution_orbit _ hq hs n]
    simp only [Function.iterate_succ_apply',complexProjection_standardLift,fineLocalRecurrence,LocalRecurrence.step]

lemma fineStableCurve_contraction (k χ ε δ : ℝ) (hδ : 0<δ) (hq : Real.exp (-χ+ε)+δ<1)
    (w : ℂ) (hw : ∀ n : ℕ, FineRegular k χ ε (complexProjection ((standardLift k)^[n] w)))
    {s t : ℝ} (hs : |s|≤1) (ht : |t|≤1) (n : ℕ) :
    ‖(standardLift k)^[n] (fineStableCurve k χ ε δ hδ hq w hw s)-
      (standardLift k)^[n] (fineStableCurve k χ ε δ hδ hq w hw t)‖≤
      (2*fineScale k ε δ)*(Real.exp (-χ+ε)+δ)^n*|s-t| := by
  rw [fineStableCurve_orbit k χ ε δ hδ hq w hw hs,fineStableCurve_orbit k χ ε δ hδ hq w hw ht,
    add_sub_add_left_eq_sub,←map_sub]
  have hn : ‖fineFrame k χ ε δ (complexProjection ((standardLift k)^[n] w))‖≤2*fineScale k ε δ :=
    (fineFrame_norm_le k χ ε hδ _).trans (mul_le_mul_of_nonneg_left (fineSize_le_scale k χ ε hδ _) (by norm_num))
  have hx := solution_exponential_contraction (fineLocalRecurrence k χ ε δ hδ w hw).extend hq s t n
  exact ((ContinuousLinearMap.le_opNorm _ _).trans (mul_le_mul hn hx (norm_nonneg _)
    (by linarith [fineScale_pos k ε hδ]))).trans_eq (by
      change (2*fineScale k ε δ)*((Real.exp (-χ+ε)+δ)^n*|s-t|)=_; ring)

end StandardMapEntropy

end
end

end OAI
end

section
-- module Solutions.OAIQ44_CM.StandardMap_Components_BoundedBirkhoff
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open MeasureTheory Filter Set
open scoped Topology ENNReal BigOperators

namespace BoundedSubadditive
variable {X : Type*} [MeasurableSpace X] {T : X → X}

lemma observation_integral_rate {μ : Measure X} [IsFiniteMeasure μ]
    (hT : MeasurePreserving T μ μ) {g : X → ℝ} (hg : Measurable g)
    (h0 : ∀ x,0≤g x) (h1 : ∀ x,g x≤1) :
    ∫ x, (observationCocycle g hT.measurable hg h0 h1).lowerRate x ∂μ = ∫ x,g x ∂μ := by
  let f := observationCocycle g hT.measurable hg h0 h1
  have hi : Integrable g μ := (integrable_const (1 : ℝ)).mono' hg.aestronglyMeasurable
    (Eventually.of_forall fun x => by rw [Real.norm_eq_abs,abs_of_nonneg (h0 x)]; exact h1 x)
  have him (i : ℕ) : Integrable (fun x => g (T^[i] x)) μ := (hT.iterate i).integrable_comp_of_integrable hi
  have he (n : ℕ) (hn : n≠0) : (∫ x,f.average n x ∂μ)=∫ x,g x ∂μ := by
    change (∫ x,birkhoffSum T g n x/(n : ℝ) ∂μ)=_
    rw [integral_div]
    have hs : (∫ x,birkhoffSum T g n x ∂μ)=(n : ℝ)*(∫ x,g x ∂μ) := by
      unfold birkhoffSum
      rw [integral_finsetSum _ (fun i _ => him i)]
      simp only [BoundedSubadditive.integral_comp (hT.iterate _) hi.aestronglyMeasurable,
        Finset.sum_const,Finset.card_range,nsmul_eq_mul]
    rw [hs,mul_div_cancel_left₀ _ (by exact_mod_cast hn)]
  have ht := f.tendsto_integral_average hT
  have hc : Tendsto (fun n => ∫ x,f.average n x ∂μ) atTop (𝓝 (∫ x,g x ∂μ)) := by
    apply tendsto_const_nhds.congr'
    filter_upwards [eventually_ne_atTop 0] with n hn
    exact (he n hn).symm
  exact tendsto_nhds_unique ht hc

theorem exists_bounded_birkhoff_limit {μ : Measure X} [IsFiniteMeasure μ]
    (hT : MeasurePreserving T μ μ) {g : X → ℝ} (hg : Measurable g)
    (h0 : ∀ x,0≤g x) (h1 : ∀ x,g x≤1) :
    ∃ G : X → ℝ, Measurable G ∧ (∀ x,0≤G x ∧ G x≤1) ∧ (∀ x,G (T x)=G x) ∧
      (∀ᵐ x ∂μ,Tendsto (fun n : ℕ => birkhoffSum T g n x/(n : ℝ)) atTop (𝓝 (G x))) ∧
      ∀ A : Set X, MeasurableSet A → T ⁻¹' A=A → ∫ x in A,G x ∂μ=∫ x in A,g x ∂μ := by
  let f := observationCocycle g hT.measurable hg h0 h1
  refine ⟨f.lowerRate,f.measurable_lowerRate,f.lowerRate_bounds,f.lowerRate_shift,f.ae_tendsto_average hT,?_⟩
  intro A hA hTA
  have hm : MeasurePreserving T (μ.restrict A) (μ.restrict A) := by
    simpa only [hTA] using hT.restrict_preimage hA
  exact observation_integral_rate hm hg h0 h1

end BoundedSubadditive

end
section
open MeasureTheory Filter Set Topology
open scoped Topology ENNReal BigOperators

namespace StandardMapEntropy

lemma complexProjection_dist_le (z w : ℂ) : dist (complexProjection z) (complexProjection w)≤‖z-w‖ := by
  change max (dist (z.re : Circle) (w.re : Circle)) (dist (z.im : Circle) (w.im : Circle))≤‖z-w‖
  apply max_le
  · calc
      dist (z.re : Circle) (w.re : Circle)=‖((z.re-w.re : ℝ) : Circle)‖ := by
        rw [dist_eq_norm,←QuotientAddGroup.mk_sub]
      _ ≤ |z.re-w.re| := QuotientAddGroup.norm_mk_le_norm
      _ ≤ ‖z-w‖ := Complex.abs_re_le_norm (z-w)
  · calc
      dist (z.im : Circle) (w.im : Circle)=‖((z.im-w.im : ℝ) : Circle)‖ := by
        rw [dist_eq_norm,←QuotientAddGroup.mk_sub]
      _ ≤ |z.im-w.im| := QuotientAddGroup.norm_mk_le_norm
      _ ≤ ‖z-w‖ := Complex.abs_im_le_norm (z-w)

end StandardMapEntropy

end
section
namespace StandardMapEntropy
open MeasureTheory Set Filter Topology
open scoped Topology NNReal ENNReal
open NonlinearStable

lemma fineUnstableCurve_contraction (k χ ε δ : ℝ) (hδ : 0<δ) (hq : Real.exp (-χ+ε)+δ<1)
    (w : ℂ) (hw : ∀ n : ℕ, FineRegular k χ ε (complexProjection ((standardLift k)^[n] (tangentReversal w))))
    {s t : ℝ} (hs : |s|≤1) (ht : |t|≤1) (n : ℕ) :
    ‖(standardInverseLift k)^[n] (fineUnstableCurve k χ ε δ hδ hq w hw s)-
      (standardInverseLift k)^[n] (fineUnstableCurve k χ ε δ hδ hq w hw t)‖≤
      (6*fineScale k ε δ)*(Real.exp (-χ+ε)+δ)^n*|s-t| := by
  simp only [fineUnstableCurve,inverse_lift_iterate_reversed,←map_sub]
  exact ((tangentReversal_norm_le _).trans (mul_le_mul_of_nonneg_left
    (fineStableCurve_contraction k χ ε δ hδ hq (tangentReversal w) hw hs ht n) (by norm_num))).trans_eq (by ring)

end StandardMapEntropy

end
end

end OAI
end

section
-- module Solutions.OAIQ44_CM.StandardMap_Components_FineChartGraph
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace StandardMapEntropy
open MeasureTheory Set Filter Topology
open scoped Topology ENNReal
open NonlinearStable

namespace ReversibleRectangleBlock
variable {k χ : ℝ} (B : ReversibleRectangleBlock k χ)

lemma continuous_coordinates : Continuous B.coordinates := by unfold coordinates; fun_prop

end ReversibleRectangleBlock

end StandardMapEntropy

end
end

end OAI
end

section
-- module Solutions.OAIQ44_CM.StandardMap_Components_CurvedHolonomy
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace StandardMapEntropy
open MeasureTheory MeasureTheory.Measure Set Filter Topology
open scoped Topology ENNReal
attribute [local instance] Measure.Subtype.measureSpace

namespace ReversibleRectangleBlock
variable {k χ : ℝ} (B : ReversibleRectangleBlock k χ)

lemma compact_coordinateCarrier : IsCompact B.coordinateCarrier := B.compact.image B.continuous_coordinates
lemma chart_image_carrier : B.chart '' B.coordinateCarrier=B.carrier := by
  ext v
  constructor
  · rintro ⟨p,⟨v',hv',hp⟩,rfl⟩
    rw [←hp,B.chart_coordinates]
    exact hv'
  · intro hv
    exact ⟨B.coordinates v,⟨v,hv,rfl⟩,B.chart_coordinates v⟩

lemma volume_chart_image {S : Set RealPlane} (hS : MeasurableSet S) :
    volume (B.chart '' S)=ENNReal.ofReal (fineVolumeFactor k χ B.ε B.δ (complexProjection B.centre))*volume S := by
  have he : B.chart '' S=(fun z : ℂ => B.centre+z) ''
      ((fineSize k χ B.ε B.δ (complexProjection B.centre) • lyapunovFrame k χ (complexProjection B.centre)) '' (pairToComplex '' S)) := by
    rw [Set.image_image,Set.image_image]
    rfl
  rw [he,Set.image_add_left,measure_preimage_add,Measure.addHaar_image_continuousLinearMap,volume_pairToComplex_image hS]
  rfl
lemma positive_coordinateCarrier : 0<volume B.coordinateCarrier := by
  by_contra h
  have hz : volume B.coordinateCarrier=0 := le_antisymm (not_lt.mp h) (bot_le)
  have hh := B.volume_chart_image B.compact_coordinateCarrier.measurableSet
  rw [B.chart_image_carrier,hz,mul_zero] at hh
  exact B.positive.ne' hh
lemma volume_coordinate_univ : (volume : Measure B.coordinateCarrier) univ=volume B.coordinateCarrier := by
  change (Measure.comap Subtype.val volume) univ=volume B.coordinateCarrier
  rw [comap_subtype_coe_apply B.compact_coordinateCarrier.measurableSet]
  simp only [Set.image_univ,Subtype.range_coe]
lemma finite_coordinate_volume : IsFiniteMeasure (volume : Measure B.coordinateCarrier) := by
  apply (isFiniteMeasure_iff _).mpr
  rw [B.volume_coordinate_univ]
  exact B.compact_coordinateCarrier.measure_lt_top

end ReversibleRectangleBlock
end StandardMapEntropy

end
section
open MeasureTheory MeasureTheory.Measure Set Filter
open scoped ENNReal Topology

theorem ae_constant_of_product_rows_columns {A B Y : Type*}
    [MeasurableSpace A] [MeasurableSpace B] {α : Measure A} {β : Measure B}
    [IsProbabilityMeasure α] [IsProbabilityMeasure β]
    {P : A×B → Prop} (hP : ∀ᵐ p ∂α.prod β,P p) {F : A×B → Y}
    (hrow : ∀ a b b',P (a,b) → P (a,b') → F (a,b)=F (a,b'))
    (hcol : ∀ a a' b,P (a,b) → P (a',b) → F (a,b)=F (a',b)) :
    ∃ c : Y, ∀ᵐ p ∂α.prod β,F p=c := by
  have hp : ∀ᵐ a ∂α,∀ᵐ b ∂β,P (a,b) := ae_ae_of_ae_prod hP
  obtain ⟨a₀,ha₀⟩ := hp.exists
  obtain ⟨b₀,hb₀⟩ := ha₀.exists
  refine ⟨F (a₀,b₀),?_⟩
  have hrowc : ∀ᵐ a ∂α,∀ b,P (a,b) → F (a,b)=F (a₀,b₀) := by
    filter_upwards [hp] with a ha
    obtain ⟨b',hab',ha₀b'⟩ := (ha.and ha₀).exists
    intro b hab
    exact (hrow a b b' hab hab').trans ((hcol a a₀ b' hab' ha₀b').trans (hrow a₀ b' b₀ ha₀b' hb₀))
  have hr : ∀ᵐ p ∂α.prod β,∀ b,P (p.1,b) → F (p.1,b)=F (a₀,b₀) :=
    (measurePreserving_fst (μ := α) (ν := β)).quasiMeasurePreserving.ae hrowc
  filter_upwards [hP,hr] with p hp' hr'
  exact hr' p.2 hp'

end
end

end OAI
end

section
-- module Solutions.OAIQ44_CM.StandardMap_Components_BirkhoffAtoms
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace StandardMapEntropy
open MeasureTheory MeasureTheory.Measure Set Filter Topology
open scoped Topology ENNReal
open NonlinearStable BoundedSubadditive
attribute [local instance] Measure.Subtype.measureSpace

namespace ReversibleGraphRectangle
variable {k χ : ℝ} {B : ReversibleRectangleBlock k χ} {F : ReversibleGraphFamilies B} (R : ReversibleGraphRectangle F)
lemma stable_representation (p : B.coordinateCarrier×B.coordinateCarrier) :
    B.chart (R.point p)=fineStableCurve k χ B.ε B.δ B.δ_pos B.contraction (B.label p.1)
      (B.regular (B.label p.1) (B.label p.1).property) (F.stableParameter (B.label p.1) (R.point p).1) := by
  calc
    B.chart (R.point p)=B.chart ((R.point p).1,F.G (B.label p.1) (R.point p).1) := congrArg B.chart (Prod.ext rfl (R.stable p))
    _ = _ := F.stable_representation _ _ ((R.x_bound p).trans (by linarith [B.ρ_small,B.r_pos]))
lemma unstable_representation (p : B.coordinateCarrier×B.coordinateCarrier) :
    B.chart (R.point p)=fineUnstableCurve k χ B.ε B.δ B.δ_pos B.contraction (B.label p.2)
      (B.reversed (B.label p.2) (B.label p.2).property) (F.unstableParameter (B.label p.2) (R.point p).2) := by
  calc
    B.chart (R.point p)=B.chart (F.U (B.label p.2) (R.point p).2,(R.point p).2) := congrArg B.chart (Prod.ext (R.unstable p) rfl)
    _ = _ := F.unstable_representation _ _ ((R.y_bound p).trans (by linarith [B.ρ_reverse,B.ρ_pos]))
end ReversibleGraphRectangle

end StandardMapEntropy

end
end

end OAI
end

section
-- module Solutions.OAIQ44_CM.StandardMap_Bernoulli_ErgodicAverages
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace StandardMapEntropy
open MeasureTheory MeasureTheory.Measure Set Filter Topology
open scoped Topology ENNReal
open BoundedSubadditive HyperbolicCoding
attribute [local instance] Measure.Subtype.measureSpace

namespace ReversibleRectangleBlock
variable {k χ : ℝ} (B : ReversibleRectangleBlock k χ)

instance carrierProbability_probability : IsProbabilityMeasure B.carrierProbability := by
  let _ : IsFiniteMeasure (volume : Measure B.coordinateCarrier) := B.finite_coordinate_volume
  have hp : 0<(volume : Measure B.coordinateCarrier) univ := by
    rw [B.volume_coordinate_univ]
    exact B.positive_coordinateCarrier
  constructor
  simp only [carrierProbability,Measure.smul_apply,smul_eq_mul]
  exact ENNReal.inv_mul_cancel hp.ne' (measure_ne_top _ _)

end ReversibleRectangleBlock

end StandardMapEntropy

end
section
open MeasureTheory MeasureTheory.Measure Set Filter
open scoped Topology ENNReal NNReal BigOperators

namespace HyperbolicCoding

theorem ae_threshold_avoids_exponential {X : Type*} [MeasurableSpace X]
    (μ : Measure X) [IsProbabilityMeasure μ] {T : X → X} (hT : Measurable T)
    {g : X → ℝ} (hg : Measurable g) {ρ : ℝ} (hρ0 : 0≤ρ) (hρ1 : ρ<1) :
    ∀ᵐ r : ℝ ∂volume,∀ᵐ x ∂μ,∀ C : ℕ,∀ᶠ n : ℕ in atTop,
      (C : ℝ)*ρ^n < |g (T^[n] x)-r| := by
  have hC (C : ℕ) : ∀ᵐ r : ℝ ∂volume,∀ᵐ x ∂μ,∀ᶠ n : ℕ in atTop,
      (C : ℝ)*ρ^n < |g (T^[n] x)-r| := by
    let S (n : ℕ) : Set (ℝ×X) := {p | |g (T^[n] p.2)-p.1|≤(C : ℝ)*ρ^n}
    have hSm (n : ℕ) : MeasurableSet (S n) :=
      measurableSet_le (((hg.comp (hT.iterate n)).comp measurable_snd).sub measurable_fst).abs measurable_const
    have hm (n : ℕ) : ((volume : Measure ℝ).prod μ) (S n)=ENNReal.ofReal (2*(C : ℝ)*ρ^n) := by
      rw [Measure.prod_apply_symm (hSm n)]
      calc
        _ = ∫⁻ x : X,ENNReal.ofReal (2*(C : ℝ)*ρ^n) ∂μ := by
          apply lintegral_congr
          intro x
          have he : (fun r : ℝ => (r,x)) ⁻¹' S n=
              Icc (g (T^[n] x)-(C : ℝ)*ρ^n) (g (T^[n] x)+(C : ℝ)*ρ^n) := by
            ext r
            simp only [S,mem_preimage,mem_ofPred_eq,mem_Icc,abs_le]
            constructor <;> rintro ⟨h₁,h₂⟩ <;> constructor <;> linarith
          rw [he,Real.volume_Icc]
          congr 1
          ring
        _ = _ := by simp
    have hsum : (∑' n : ℕ,((volume : Measure ℝ).prod μ) (S n))≠⊤ := by
      simp only [hm,ENNReal.ofReal_mul (by positivity : 0≤2*(C : ℝ)),ENNReal.ofReal_pow hρ0,
        ENNReal.tsum_mul_left,ENNReal.tsum_geometric]
      apply ENNReal.mul_ne_top ENNReal.ofReal_ne_top
      exact ENNReal.inv_ne_top.mpr (ne_of_gt (tsub_pos_iff_lt.mpr (ENNReal.ofReal_lt_one.mpr hρ1)))
    have ha := ae_eventually_notMem hsum
    have hh := ae_ae_of_ae_prod ha
    filter_upwards [hh] with r hr
    filter_upwards [hr] with x hx
    filter_upwards [hx] with n hn
    exact lt_of_not_ge hn
  filter_upwards [ae_all_iff.mpr hC] with r hr
  exact ae_all_iff.mpr hr

theorem ae_threshold_exponential_tail {X : Type*} [PseudoMetricSpace X]
    [MeasurableSpace X] [BorelSpace X] (μ : Measure X) [IsProbabilityMeasure μ]
    {T : X → X} (hT : Measurable T) {g : X → ℝ} {K : ℝ≥0} (hg : LipschitzWith K g)
    {ρ : ℝ} (hρ0 : 0≤ρ) (hρ1 : ρ<1) :
    ∀ᵐ r : ℝ ∂volume,∀ᵐ x ∂μ,∀ y : X,∀ C : ℝ,
      (∀ᶠ n : ℕ in atTop,dist (T^[n] x) (T^[n] y)≤C*ρ^n) →
      ∀ᶠ n : ℕ in atTop,(g (T^[n] x) < r ↔ g (T^[n] y) < r) := by
  filter_upwards [ae_threshold_avoids_exponential μ hT hg.continuous.measurable hρ0 hρ1] with r hr
  filter_upwards [hr] with x hx
  intro y C hxy
  obtain ⟨M,hM⟩ := exists_nat_gt ((K : ℝ)*C)
  filter_upwards [hx M,hxy] with n hn hdist
  have hdiff : |g (T^[n] x)-g (T^[n] y)|≤(M : ℝ)*ρ^n := by
    calc
      _ ≤ (K : ℝ)*dist (T^[n] x) (T^[n] y) := by simpa only [Real.dist_eq] using hg.dist_le_mul (T^[n] x) (T^[n] y)
      _ ≤ (K : ℝ)*(C*ρ^n) := mul_le_mul_of_nonneg_left hdist K.coe_nonneg
      _ ≤ (M : ℝ)*ρ^n := by
        rw [←mul_assoc]
        exact mul_le_mul_of_nonneg_right hM.le (pow_nonneg hρ0 n)
  rcases abs_le.mp hdiff with ⟨hlo,hhi⟩
  by_cases hxr : g (T^[n] x) < r
  · have habs : |g (T^[n] x)-r|=r-g (T^[n] x) := by rw [abs_of_neg (by linarith)]; ring
    rw [habs] at hn
    exact iff_of_true hxr (by linarith)
  · have habs : |g (T^[n] x)-r|=g (T^[n] x)-r := abs_of_nonneg (sub_nonneg.mpr (not_lt.mp hxr))
    rw [habs] at hn
    exact iff_of_false hxr (by linarith)

theorem ae_threshold_all_exponential_tails {X : Type*} [PseudoMetricSpace X]
    [MeasurableSpace X] [BorelSpace X] (μ : Measure X) [IsProbabilityMeasure μ]
    {T : X → X} (hT : Measurable T) {g : X → ℝ} {K : ℝ≥0} (hg : LipschitzWith K g) :
    ∀ᵐ r : ℝ ∂volume,∀ᵐ x ∂μ,∀ y : X,ExponentiallyAsymptotic T x y →
      ∀ᶠ n : ℕ in atTop,(g (T^[n] x) < r ↔ g (T^[n] y) < r) := by
  have hq (q : ℚ) : ∀ᵐ r : ℝ ∂volume,∀ᵐ x ∂μ,
      0≤(q : ℝ) → (q : ℝ)<1 → ∀ y : X,∀ C : ℝ,
      (∀ᶠ n : ℕ in atTop,dist (T^[n] x) (T^[n] y)≤C*(q : ℝ)^n) →
      ∀ᶠ n : ℕ in atTop,(g (T^[n] x) < r ↔ g (T^[n] y) < r) := by
    by_cases hq0 : 0≤(q : ℝ)
    · by_cases hq1 : (q : ℝ)<1
      · exact (ae_threshold_exponential_tail μ hT hg hq0 hq1).mono
          (fun r hr => hr.mono (fun x hx _ _ => hx))
      · exact ae_of_all _ (fun _ => ae_of_all _ (fun _ _ h => (hq1 h).elim))
    · exact ae_of_all _ (fun _ => ae_of_all _ (fun _ h => (hq0 h).elim))
  filter_upwards [ae_all_iff.mpr hq] with r hr
  filter_upwards [ae_all_iff.mpr hr] with x hx
  intro y ⟨ρ,hρ0,hρ1,C,hxy⟩
  obtain ⟨q,hρq,hq1⟩ := exists_rat_btwn hρ1
  apply hx q (hρ0.trans hρq.le) hq1 y (max C 0)
  filter_upwards [hxy] with n hn
  exact hn.trans (mul_le_mul (le_max_left C 0) (pow_le_pow_left₀ hρ0 hρq.le n)
    (pow_nonneg hρ0 n) (le_max_right C 0))

end HyperbolicCoding

end
section
open MeasureTheory MeasureTheory.Measure Set Filter
open scoped Topology NNReal ENNReal

namespace HyperbolicCoding

lemma measurable_joinedBinary {X : Type*} [MeasurableSpace X]
    {α : ℕ → ℕ → X → Bool} (hα : ∀ i j,Measurable (α i j)) (N : ℕ) :
    Measurable (joinedBinary α N) :=
  Measurable.of_eval (fun p => hα p.1 p.2)

theorem exists_good_binary_partitions {X : Type*} [MetricSpace X]
    [SecondCountableTopology X] [MeasurableSpace X] [BorelSpace X] [Nonempty X]
    (μ : Measure X) [IsProbabilityMeasure μ] {T S : X → X}
    (hT : Measurable T) (hS : Measurable S) :
    ∃ α : ℕ → ℕ → X → Bool,
      (∀ i j,Measurable (α i j)) ∧
      Function.Injective (fun x => fun i j => α i j x) ∧
      (∀ᵐ x ∂μ,∀ y : X,ExponentiallyAsymptotic T x y → ∀ N : ℕ,
        ∀ᶠ n : ℕ in atTop,joinedBinary α N (T^[n] x)=joinedBinary α N (T^[n] y)) ∧
      (∀ᵐ x ∂μ,∀ y : X,ExponentiallyAsymptotic S x y → ∀ N : ℕ,
        ∀ᶠ n : ℕ in atTop,joinedBinary α N (S^[n] x)=joinedBinary α N (S^[n] y)) := by
  classical
  let c := TopologicalSpace.denseSeq X
  have hd : DenseRange c := TopologicalSpace.denseRange_denseSeq X
  have hgood (i j : ℕ) : ∃ r : ℝ,
      r∈Ioo (1/((j : ℝ)+1)) (2/((j : ℝ)+1)) ∧
      (∀ᵐ x ∂μ,∀ y : X,ExponentiallyAsymptotic T x y →
        ∀ᶠ n : ℕ in atTop,(dist (T^[n] x) (c i) < r ↔ dist (T^[n] y) (c i) < r)) ∧
      (∀ᵐ x ∂μ,∀ y : X,ExponentiallyAsymptotic S x y →
        ∀ᶠ n : ℕ in atTop,(dist (S^[n] x) (c i) < r ↔ dist (S^[n] y) (c i) < r)) := by
    have ha := (ae_threshold_all_exponential_tails μ hT (LipschitzWith.dist_left (c i))).and
      (ae_threshold_all_exponential_tails μ hS (LipschitzWith.dist_left (c i)))
    have hv : volume (Ioo (1/((j : ℝ)+1)) (2/((j : ℝ)+1)))≠0 := by
      rw [Real.volume_Ioo,ne_eq,ENNReal.ofReal_eq_zero]
      have hp : (0 : ℝ)<(j : ℝ)+1 := by positivity
      push Not
      exact sub_pos.mpr (div_lt_div_of_pos_right (by norm_num) hp)
    exact exists_mem_of_measure_ne_zero_of_ae hv (ae_restrict_of_ae ha)
  choose r hr hTf hSb using hgood
  let α (i j : ℕ) (x : X) : Bool := if dist x (c i) < r i j then true else false
  have hm (i j : ℕ) : Measurable (α i j) :=
    measurable_const.ite (measurableSet_lt (continuous_id.dist continuous_const).measurable measurable_const) measurable_const
  have hinj : Function.Injective (fun x => fun i j => α i j x) := by
    intro x y h
    by_contra hxy
    have hdpos : 0<dist x y := dist_pos.mpr hxy
    obtain ⟨j,hj⟩ := exists_nat_one_div_lt (by linarith : 0<dist x y/3)
    obtain ⟨i,hi⟩ := hd.exists_dist_lt x (by positivity : 0<1/((j : ℝ)+1))
    have hx : dist x (c i) < r i j := hi.trans (hr i j).1
    have hy : ¬dist y (c i) < r i j := by
      intro hy
      have ht := dist_triangle x (c i) y
      rw [dist_comm (c i) y] at ht
      have ht' : 2/((j : ℝ)+1)=2*(1/((j : ℝ)+1)) := by ring
      have hh := (hr i j).2
      rw [ht'] at hh
      linarith
    have hh := congrFun (congrFun h i) j
    simp only [α,ite_eq_left hx,ite_eq_right hy] at hh
    exact Bool.noConfusion hh
  have forward : ∀ᵐ x ∂μ,∀ y : X,ExponentiallyAsymptotic T x y → ∀ N : ℕ,
      ∀ᶠ n : ℕ in atTop,joinedBinary α N (T^[n] x)=joinedBinary α N (T^[n] y) := by
    filter_upwards [ae_all_iff.mpr (fun i => ae_all_iff.mpr (hTf i))] with x hx
    intro y hxy N
    have hp (p : Fin N × Fin N) : ∀ᶠ n : ℕ in atTop,
        α p.1 p.2 (T^[n] x)=α p.1 p.2 (T^[n] y) := by
      filter_upwards [hx p.1 p.2 y hxy] with n hn
      dsimp only [α]
      simp only [hn]
    filter_upwards [Filter.eventually_all.mpr hp] with n hn
    exact funext hn
  have backward : ∀ᵐ x ∂μ,∀ y : X,ExponentiallyAsymptotic S x y → ∀ N : ℕ,
      ∀ᶠ n : ℕ in atTop,joinedBinary α N (S^[n] x)=joinedBinary α N (S^[n] y) := by
    filter_upwards [ae_all_iff.mpr (fun i => ae_all_iff.mpr (hSb i))] with x hx
    intro y hxy N
    have hp (p : Fin N × Fin N) : ∀ᶠ n : ℕ in atTop,
        α p.1 p.2 (S^[n] x)=α p.1 p.2 (S^[n] y) := by
      filter_upwards [hx p.1 p.2 y hxy] with n hn
      dsimp only [α]
      simp only [hn]
    filter_upwards [Filter.eventually_all.mpr hp] with n hn
    exact funext hn
  exact ⟨α,hm,hinj,forward,backward⟩

end HyperbolicCoding

end
end

end OAI
end

section
-- module Solutions.OAIQ44_CM.StandardMap_Bernoulli_TailNameSaturation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open MeasureTheory MeasureTheory.Measure Set Filter
open scoped Topology

namespace HyperbolicCoding

theorem tailEvent_saturation {X A : Type*} [PseudoMetricSpace X]
    [MeasurableSpace X] [MeasurableSpace A] (μ : Measure X) {T : X → X} {α : X → A}
    (hnames : ∀ᵐ x ∂μ,∀ y,ExponentiallyAsymptotic T x y →
      ∀ᶠ n : ℕ in atTop,α (T^[n] x)=α (T^[n] y)) {E : Set X}
    (hE : TailEvent μ T α E) :
    ∃ Q : Set X,(∀ᵐ x ∂μ,x∈Q) ∧ ∀ x∈Q,∀ y∈Q,
      ExponentiallyAsymptotic T x y → (x∈E ↔ y∈E) := by
  choose D hDm hDE using hE
  let Q : Set X := {x | (∀ m,x∈E ↔ tailName T α m x∈D m) ∧
    ∀ y,ExponentiallyAsymptotic T x y → ∀ᶠ n : ℕ in atTop,α (T^[n] x)=α (T^[n] y)}
  have hQ : ∀ᵐ x ∂μ,x∈Q := by
    filter_upwards [ae_all_iff.mpr hDE,hnames] with x hx hn
    exact ⟨fun m => Iff.of_eq (hx m),hn⟩
  refine ⟨Q,hQ,?_⟩
  intro x hx y hy hxy
  obtain ⟨m,hm⟩ := eventually_atTop.mp (hx.2 y hxy)
  have hname : tailName T α m x=tailName T α m y := by
    funext n
    exact hm (n+m) (by omega)
  have hmem : tailName T α m x∈D m ↔ tailName T α m y∈D m := by rw [hname]
  exact (hx.1 m).trans (hmem.trans (hy.1 m).symm)

lemma ExponentiallyAsymptotic.iterate {X : Type*} [PseudoMetricSpace X]
    {T : X → X} {x y : X} (h : ExponentiallyAsymptotic T x y) {N : ℕ} (hN : 0<N) :
    ExponentiallyAsymptotic (T^[N]) x y := by
  obtain ⟨ρ,hρ0,hρ1,C,hC⟩ := h
  have hseq : Tendsto (fun n : ℕ => N*n) atTop atTop :=
    tendsto_atTop_mono (fun n => by change n≤N*n; nlinarith) tendsto_id
  refine ⟨ρ^N,pow_nonneg hρ0 N,pow_lt_one₀ hρ0 hρ1 hN.ne',C,?_⟩
  filter_upwards [hseq.eventually hC] with n hn
  simpa only [Function.iterate_mul,pow_mul] using hn

end HyperbolicCoding

end
section
namespace StandardMapEntropy
open MeasureTheory MeasureTheory.Measure Set Filter Topology
open scoped Topology ENNReal NNReal
open HyperbolicCoding
attribute [local instance] Measure.Subtype.measureSpace

lemma fineStableCurve_exponentiallyAsymptotic (k χ ε δ : ℝ) (hδ : 0<δ)
    (hq : Real.exp (-χ+ε)+δ<1) (w : ℂ)
    (hw : ∀ n : ℕ,FineRegular k χ ε (complexProjection ((standardLift k)^[n] w)))
    {s t : ℝ} (hs : |s|≤1) (ht : |t|≤1) :
    ExponentiallyAsymptotic (standardMap k)
      (complexProjection (fineStableCurve k χ ε δ hδ hq w hw s))
      (complexProjection (fineStableCurve k χ ε δ hδ hq w hw t)) := by
  refine ⟨Real.exp (-χ+ε)+δ,by positivity,hq,(2*fineScale k ε δ)*|s-t|,Filter.Eventually.of_forall ?_⟩
  intro n
  have h := (complexProjection_dist_le _ _).trans (fineStableCurve_contraction k χ ε δ hδ hq w hw hs ht n)
  rw [complexProjection_iterate,complexProjection_iterate] at h
  exact h.trans_eq (by ring)

lemma fineUnstableCurve_exponentiallyAsymptotic (k χ ε δ : ℝ) (hδ : 0<δ)
    (hq : Real.exp (-χ+ε)+δ<1) (w : ℂ)
    (hw : ∀ n : ℕ,FineRegular k χ ε (complexProjection ((standardLift k)^[n] (tangentReversal w))))
    {s t : ℝ} (hs : |s|≤1) (ht : |t|≤1) :
    ExponentiallyAsymptotic (inverseMap k)
      (complexProjection (fineUnstableCurve k χ ε δ hδ hq w hw s))
      (complexProjection (fineUnstableCurve k χ ε δ hδ hq w hw t)) := by
  refine ⟨Real.exp (-χ+ε)+δ,by positivity,hq,(6*fineScale k ε δ)*|s-t|,Filter.Eventually.of_forall ?_⟩
  intro n
  have h := (complexProjection_dist_le _ _).trans (fineUnstableCurve_contraction k χ ε δ hδ hq w hw hs ht n)
  rw [complexProjection_inverse_iterate,complexProjection_inverse_iterate] at h
  exact h.trans_eq (by ring)

namespace ReversibleGraphRectangle
variable {k χ : ℝ} {B : ReversibleRectangleBlock k χ} {F : ReversibleGraphFamilies B}
    (R : ReversibleGraphRectangle F)

lemma row_exponential (a b b' : B.coordinateCarrier) :
    ExponentiallyAsymptotic (standardMap k) (R.torusPoint (a,b)) (R.torusPoint (a,b')) := by
  have h := fineStableCurve_exponentiallyAsymptotic k χ B.ε B.δ B.δ_pos B.contraction (B.label a)
    (B.regular (B.label a) (B.label a).property)
    ((F.stable_bound (B.label a) (R.point (a,b)).1).trans (by linarith [B.r_small]))
    ((F.stable_bound (B.label a) (R.point (a,b')).1).trans (by linarith [B.r_small]))
  simpa only [torusPoint,R.stable_representation] using h

lemma column_exponential (a a' b : B.coordinateCarrier) :
    ExponentiallyAsymptotic (inverseMap k) (R.torusPoint (a,b)) (R.torusPoint (a',b)) := by
  have h := fineUnstableCurve_exponentiallyAsymptotic k χ B.ε B.δ B.δ_pos B.contraction (B.label b)
    (B.reversed (B.label b) (B.label b).property)
    ((F.unstable_bound (B.label b) (R.point (a,b)).2).trans (by linarith [B.r'_small]))
    ((F.unstable_bound (B.label b) (R.point (a',b)).2).trans (by linarith [B.r'_small]))
  simpa only [torusPoint,R.unstable_representation] using h

end ReversibleGraphRectangle
end StandardMapEntropy

end
section
namespace StandardMapEntropy.Entropy
open MeasureTheory MeasureTheory.Measure Set Filter
open scoped BigOperators ENNReal symmDiff
variable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
variable {α β : Type*} [Fintype α] [MeasurableSpace α] [MeasurableSingletonClass α]
    [Fintype β] [MeasurableSpace β] [MeasurableSingletonClass β] [Nonempty β]

omit [Fintype α] [MeasurableSingletonClass α] in
lemma exists_prefix_approx {Z : Ω → (ℕ → α)} (hZ : Measurable Z)
    {G : (ℕ → α) → β} (hG : Measurable G) (ε : ℝ) (hε : 0<ε) :
    ∃ (N : ℕ) (g : (Fin N → α) → β),
      μ {x | g (fun i => Z x i.val)≠G (Z x)}<ENNReal.ofReal ε := by
  classical
  let η := ε/((Fintype.card β : ℝ)+1)
  have hη : 0<η := div_pos hε (by positivity)
  let ν := μ.map Z
  have : IsProbabilityMeasure ν := by first | infer_instance | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | (apply Measurable.aemeasurable; measurability) | measurability)
  have happ (b : β) : ∃ C ∈ measurableCylinders (fun _ : ℕ => α),
      ν (C ∆ (G ⁻¹' {b}))<ENNReal.ofReal η := by
    apply exists_measure_symmDiff_lt_of_generateFrom_isSetRing isSetRing_measurableCylinders
      (μ := ν) ?_ generateFrom_measurableCylinders.symm (hG (measurableSet_singleton b))
      (ENNReal.ofReal_pos.mpr hη)
    refine ⟨{univ},countable_singleton _,?_,by simp⟩
    simpa only [singleton_subset_iff] using (univ_mem_measurableCylinders (fun _ : ℕ => α))
  choose C hC hsmall using happ
  have hcyl (b : β) : ∃ (s : Finset ℕ) (S : Set (∀ i : s,α)),MeasurableSet S ∧ C b=cylinder s S := by
    simpa only [mem_measurableCylinders] using hC b
  choose s S hS hSC using hcyl
  let N : ℕ := 1+∑ b : β,(s b).sup id
  have hindex (b : β) (i : s b) : i.val<N := by
    have hl := Finset.le_sup (f := id) i.property
    have hs := Finset.single_le_sum (f := fun b : β => (s b).sup id)
      (fun b _ => Nat.zero_le _) (Finset.mem_univ b)
    dsimp only [id_eq] at hl
    dsimp [N]
    omega
  let P (b : β) (v : Fin N → α) : Prop := (fun i : s b => v ⟨i.val,hindex b i⟩)∈S b
  let g (v : Fin N → α) : β := if h : ∃ b,P b v then h.choose else Classical.choice inferInstance
  have hPred (b : β) (v : ℕ → α) : P b (fun i : Fin N => v i.val) ↔ v∈C b := by
    rw [hSC b]
    rfl
  have herr : {x | g (fun i => Z x i.val)≠G (Z x)}⊆
      Z ⁻¹' ⋃ b : β,C b ∆ (G ⁻¹' {b}) := by
    intro x hx
    by_contra hn
    have hall (b : β) : (Z x∈C b) ↔ G (Z x)=b := by
      have hb : Z x∉C b ∆ (G ⁻¹' {b}) := fun hb => hn (mem_iUnion_of_mem b hb)
      simp only [mem_symmDiff,mem_preimage,mem_singleton_iff] at hb
      tauto
    have hex : ∃ b,P b (fun i => Z x i.val) :=
      ⟨G (Z x),(hPred _ _).mpr ((hall _).mpr rfl)⟩
    have hg : g (fun i => Z x i.val)=hex.choose := dite_eq_left hex
    exact hx (hg.trans ((hall _).mp ((hPred _ _).mp hex.choose_spec)).symm)
  refine ⟨N,g,?_⟩
  have hCm (b : β) : MeasurableSet (C b) := by rw [hSC b]; exact (hS b).cylinder
  have hU : MeasurableSet (⋃ b : β,C b ∆ (G ⁻¹' {b})) :=
    MeasurableSet.iUnion (fun b => (hCm b).symmDiff (hG (measurableSet_singleton b)))
  calc
    μ {x | g (fun i => Z x i.val)≠G (Z x)}≤μ (Z ⁻¹' ⋃ b : β,C b ∆ (G ⁻¹' {b})) := measure_mono herr
    _=ν (⋃ b : β,C b ∆ (G ⁻¹' {b})) := (Measure.map_apply hZ hU).symm
    _≤∑ b : β,ν (C b ∆ (G ⁻¹' {b})) := measure_iUnion_fintype_le _ _
    _≤∑ _b : β,ENNReal.ofReal η := Finset.sum_le_sum (fun b _ => (hsmall b).le)
    _=ENNReal.ofReal ((Fintype.card β : ℝ)*η) := by
      simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul]
      rw [ENNReal.ofReal_mul (Nat.cast_nonneg _),ENNReal.ofReal_natCast]
    _<ENNReal.ofReal ε := ENNReal.ofReal_lt_ofReal_iff_of_nonneg (by positivity) |>.mpr (by
      have hc : (0 : ℝ)≤Fintype.card β := Nat.cast_nonneg _
      dsimp [η]
      rw [←mul_div_assoc]
      apply (div_lt_iff₀ (by positivity)).mpr
      nlinarith)

lemma exists_cond_prefix_lt {Z : Ω → (ℕ → α)} (hZ : Measurable Z)
    {q : Ω → β} (hq : Measurable q)
    (hfactor : ∃ G : (ℕ → α) → β,Measurable G ∧ q=ᵐ[μ]G ∘ Z)
    (ε : ℝ) (hε : 0<ε) :
    ∃ N : ℕ,cond μ q (fun x => fun i : Fin N => Z x i.val)<ε := by
  classical
  obtain ⟨η,hη,hs⟩ := cond_small_of_error (α := β) μ ε hε
  obtain ⟨G,hG,hqG⟩ := hfactor
  obtain ⟨N,g,hg⟩ := exists_prefix_approx μ hZ hG η hη
  let p : Ω → (Fin N → α) := fun x i => Z x i.val
  have hp : Measurable p := Measurable.of_eval (fun i => (measurable_pi_apply i.val).comp hZ)
  have hm : mass μ (errorObs q (g ∘ p)) true<η := by
    have he : (errorObs q (g ∘ p)) ⁻¹' {true}=ᵐ[μ]{x | g (p x)≠G (Z x)} := by
      filter_upwards [hqG] with x hx
      change (errorObs q (g ∘ p) x=true)=(g (p x)≠G (Z x))
      apply propext
      simp only [errorObs,Function.comp_def,decide_eq_true_eq,hx,ne_comm]
    rw [mass,measure_congr he]
    exact (ENNReal.toReal_lt_of_lt_ofReal hg)
  exact ⟨N,lt_of_le_of_lt (cond_factor_right μ q p g hq hp)
    (hs q (g ∘ p) hq ((measurable_of_countable g).comp hp) hm)⟩

end StandardMapEntropy.Entropy

end
section
namespace HyperbolicCoding
open MeasureTheory Set Filter

lemma TailObservable.word {X A B : Type*} [MeasurableSpace X] [MeasurableSpace A] [MeasurableSpace B]
    {μ : Measure X} {T : X → X} (hT : MeasurePreserving T μ μ)
    {α : X → A} {q : X → B} (hq : TailObservable μ T α q) (n : ℕ) :
    TailObservable μ T α (StandardMapEntropy.Entropy.word T q n) := by
  intro m
  obtain ⟨G,hG,he⟩ := hq m
  let H (v : ℕ → A) (i : Fin n) := G (fun j => v (j+i.val))
  have hH : Measurable H := Measurable.of_eval (fun i => hG.comp
    (Measurable.of_eval (fun j => measurable_pi_apply (j+i.val))))
  refine ⟨H,hH,?_⟩
  have hall := ae_all_iff.mpr (fun i : Fin n => (hT.iterate i.val).quasiMeasurePreserving.ae he)
  filter_upwards [hall] with x hx
  funext i
  have hi := hx i
  change q (T^[i.val] x)=G (fun j => α (T^[j+i.val+m] x))
  rw [hi]
  change G (tailName T α m (T^[i.val] x))=G (fun j => α (T^[j+i.val+m] x))
  congr 1
  funext j
  simp only [tailName,←Function.iterate_add_apply]
  congr 2
  omega

lemma tailEvent_bool {X A : Type*} [MeasurableSpace X] [MeasurableSpace A]
    {μ : Measure X} {T : X → X} {α : X → A} {E : Set X}
    (hE : TailEvent μ T α E) :
    TailObservable μ T α (fun x => by classical exact decide (x∈E)) := by
  classical
  intro m
  obtain ⟨D,hD,he⟩ := hE m
  refine ⟨fun v => decide (v∈D),?_,?_⟩
  · have hF : Measurable (fun v : ℕ → A => if v∈D then (true : Bool) else false) :=
      Measurable.ite hD measurable_const measurable_const
    convert hF using 1
    all_goals try with_reducible_and_instances rfl
    funext v
    by_cases h : v∈D <;> simp [h]
  · filter_upwards [he] with x hx
    change decide (x∈E)=decide (tailName T α m x∈D)
    exact congrArg (fun P : Prop => decide P) hx
end HyperbolicCoding
end
section
namespace StandardMapEntropy.Entropy
open MeasureTheory Set Filter
open scoped BigOperators ENNReal Topology
variable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
variable {α : Type*} [Fintype α] [MeasurableSpace α] [MeasurableSingletonClass α]

omit [IsProbabilityMeasure μ] in
lemma cond_word_future_eq (f : Ω → Ω) (hf : MeasurePreserving f μ μ)
    (p : Ω → α) (hp : Measurable p) (n m : ℕ) :
    cond μ (word f p n) (fun x => word f p m (f^[n] x))=
      obs μ (word f p (n+m))-obs μ (word f p m) := by
  unfold cond
  rw [←obs_word_split μ f p n m]
  exact congrArg (fun t => obs μ (word f p (n+m))-t)
    (obs_comp_preserving μ (f^[n]) (hf.iterate n) (word f p m) (word_measurable f hf.measurable p hp m))

omit [IsProbabilityMeasure μ] in
lemma entropy_increment_eq (f : Ω → Ω) (hf : MeasurePreserving f μ μ)
    (p : Ω → α) (hp : Measurable p) (m : ℕ) :
    obs μ (word f p (m+1))-obs μ (word f p m)=
      cond μ p (fun x => word f p m (f x)) := by
  have h := cond_word_future_eq μ f hf p hp 1 m
  rw [Nat.add_comm 1 m] at h
  have he : (Equiv.funUnique (Fin 1) α) ∘ word f p 1=p := by
    funext x; rfl
  rw [←cond_equiv_left μ (word f p 1) (fun x => word f p m (f^[1] x))
    (Equiv.funUnique (Fin 1) α),he] at h
  simpa only [Function.iterate_one] using h.symm

lemma entropy_increment_antitone (f : Ω → Ω) (hf : MeasurePreserving f μ μ)
    (p : Ω → α) (hp : Measurable p) :
    Antitone (fun m : ℕ => obs μ (word f p (m+1))-obs μ (word f p m)) := by
  apply antitone_nat_of_succ_le
  intro m
  rw [entropy_increment_eq μ f hf p hp,entropy_increment_eq μ f hf p hp]
  exact cond_factor_right μ p (fun x => word f p (m+1) (f x))
    (fun v : Fin (m+1) → α => fun i : Fin m => v i.castSucc) hp
    ((word_measurable f hf.measurable p hp (m+1)).comp hf.measurable)

lemma entropy_increment_nonneg (f : Ω → Ω) (hf : MeasurePreserving f μ μ)
    (p : Ω → α) (hp : Measurable p) (m : ℕ) :
    0≤obs μ (word f p (m+1))-obs μ (word f p m) := by
  rw [entropy_increment_eq μ f hf p hp]
  exact cond_nonneg μ p _ hp ((word_measurable f hf.measurable p hp m).comp hf.measurable)

lemma entropy_increment_tendsto (f : Ω → Ω) (hf : MeasurePreserving f μ μ)
    (p : Ω → α) (hp : Measurable p) :
    Tendsto (fun m : ℕ => obs μ (word f p (m+1))-obs μ (word f p m)) atTop (𝓝 (rate μ f p)) := by
  let d := fun m : ℕ => obs μ (word f p (m+1))-obs μ (word f p m)
  have hbd : BddBelow (Set.range d) := ⟨0,by rintro _ ⟨m,rfl⟩; exact entropy_increment_nonneg μ f hf p hp m⟩
  have hd := tendsto_atTop_ciInf (entropy_increment_antitone μ f hf p hp) hbd
  have hs (n : ℕ) : ∑ j ∈ Finset.range n,d j=obs μ (word f p n) := by
    induction n with
    | zero => simp only [Finset.range_zero,Finset.sum_empty,obs_word_zero]
    | succ n ih => rw [Finset.sum_range_succ,ih]; dsimp [d]; ring
  change Tendsto d atTop (𝓝 (⨅ i,d i)) at hd
  have hh := hd.cesaro
  simp only [hs,←div_eq_inv_mul] at hh
  have he := tendsto_nhds_unique hh (rate_tendsto μ f hf p hp)
  rwa [he] at hd

lemma rate_le_entropy_increment (f : Ω → Ω) (hf : MeasurePreserving f μ μ)
    (p : Ω → α) (hp : Measurable p) (m : ℕ) :
    rate μ f p≤obs μ (word f p (m+1))-obs μ (word f p m) := by
  apply le_of_tendsto (entropy_increment_tendsto μ f hf p hp)
  filter_upwards [eventually_ge_atTop m] with n hn
  exact entropy_increment_antitone μ f hf p hp hn

lemma rate_mul_le_cond_future (f : Ω → Ω) (hf : MeasurePreserving f μ μ)
    (p : Ω → α) (hp : Measurable p) (n m : ℕ) :
    (n : ℝ)*rate μ f p ≤ cond μ (word f p n) (fun x => word f p m (f^[n] x)) := by
  rw [cond_word_future_eq μ f hf p hp]
  induction n with
  | zero =>
    simp only [Nat.cast_zero,zero_mul]
    have he (a b : ℕ) (h : a=b) : obs μ (word f p a)=obs μ (word f p b) := by subst b; rfl
    exact sub_nonneg.mpr (le_of_eq (he (0+m) m (Nat.zero_add m)).symm)
  | succ n ih =>
    have hh := rate_le_entropy_increment μ f hf p hp (n+m)
    rw [Nat.cast_add,Nat.cast_one]
    rw [show n+1+m=n+m+1 from by omega]
    nlinarith

end StandardMapEntropy.Entropy

end
section
namespace StandardMapEntropy.Entropy
open HyperbolicCoding MeasureTheory Set Filter
open scoped Topology
variable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
variable {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ]
variable [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ]
variable [MeasurableSingletonClass α] [MeasurableSingletonClass β] [MeasurableSingletonClass γ]

lemma cond_triangle (p : Ω → α) (q : Ω → β) (r : Ω → γ)
    (hp : Measurable p) (hq : Measurable q) (hr : Measurable r) :
    cond μ p r ≤ cond μ p q+cond μ q r := by
  have h1 := cond_chain μ p r q
  have h2 := cond_chain μ q r p
  have hz := cond_nonneg μ q (fun x => (p x,r x)) hq (hp.prodMk hr)
  have hb := cond_pair_right μ p q r hp hq hr
  have he : cond μ (fun x => (p x,q x)) r=cond μ (fun x => (q x,p x)) r := by
    exact (cond_equiv_left μ (fun x => (p x,q x)) r (Equiv.prodComm α β)).symm
  linarith

lemma cond_word_window_bound (f : Ω → Ω) (hf : MeasurePreserving f μ μ)
    (p : Ω → α) (hp : Measurable p) (q : Ω → β) (hq : Measurable q) (n M : ℕ) :
    cond μ (word f q n) (word f p (n+M))≤(n : ℝ)*cond μ q (word f p M) := by
  let g (v : Fin (n+M) → α) (i : Fin n) (j : Fin M) := v ⟨j.val+i.val,by omega⟩
  have he : g ∘ word f p (n+M)=word f (word f p M) n := by
    funext x i j
    simp only [Function.comp_def,g,word,←Function.iterate_add_apply]
  have hb := cond_factor_right μ (word f q n) (word f p (n+M)) g
    (word_measurable f hf.measurable q hq n) (word_measurable f hf.measurable p hp _)
  rw [he] at hb
  exact hb.trans (cond_word_bound μ f hf q (word f p M) hq
    (word_measurable f hf.measurable p hp M) n)

lemma rate_mul_le_cond_tail [Nonempty β] (f : Ω → Ω) (hf : MeasurePreserving f μ μ)
    (p : Ω → α) (hp : Measurable p) (q : Ω → β) (hq : Measurable q)
    (ht : TailObservable μ f p q) (n : ℕ) :
    (n : ℝ)*rate μ f p ≤ cond μ (word f p n) q := by
  by_contra hn
  have hε : 0<(n : ℝ)*rate μ f p-cond μ (word f p n) q := sub_pos.mpr (lt_of_not_ge hn)
  obtain ⟨M,hM⟩ := exists_cond_prefix_lt μ (measurable_tailName hf.measurable hp n) hq
    (ht n) _ hε
  have he : (fun x => fun i : Fin M => tailName f p n x i.val)=
      (fun x => word f p M (f^[n] x)) := by
    funext x i
    simp only [tailName,word,←Function.iterate_add_apply]
  rw [he] at hM
  have hb := rate_mul_le_cond_future μ f hf p hp n M
  have hc := cond_triangle μ (word f p n) q (fun x => word f p M (f^[n] x))
    (word_measurable f hf.measurable p hp n) hq
    ((word_measurable f hf.measurable p hp M).comp (hf.measurable.iterate n))
  linarith

theorem tailObservable_rate_zero [Nonempty β] (f : Ω → Ω) (hf : MeasurePreserving f μ μ)
    (p : Ω → α) (hp : Measurable p) (q : Ω → β) (hq : Measurable q)
    (ht : TailObservable μ f p q) : rate μ f q=0 := by
  apply le_antisymm ?_ (rate_nonneg μ f hf q hq)
  by_contra hn
  have hε : 0 < rate μ f q/2 := half_pos (lt_of_not_ge hn)
  obtain ⟨M,hM⟩ := exists_cond_prefix_lt μ (measurable_tailName hf.measurable hp 0) hq
    (ht 0) _ hε
  change cond μ q (word f p M) < rate μ f q/2 at hM
  have hb (n : ℕ) : obs μ (word f q n)≤obs μ (word f p n)-(n : ℝ)*rate μ f p+
      obs μ (word f p M)+(n : ℝ)*(rate μ f q/2) := by
    have hl := rate_mul_le_cond_tail μ f hf p hp (word f q n)
      (word_measurable f hf.measurable q hq n) (ht.word hf n) (n+M)
    have hu := cond_word_window_bound μ f hf p hp q hq n M
    have hs := obs_word_subadd μ f hf p hp n M
    have he := obs_pair_swap μ (word f q n) (word f p (n+M))
    have hz := mul_nonneg (Nat.cast_nonneg M) (rate_nonneg μ f hf p hp)
    have hc := mul_le_mul_of_nonneg_left hM.le (Nat.cast_nonneg n)
    unfold cond at hl hu hc
    rw [Nat.cast_add] at hl
    nlinarith
  have hlim : Tendsto (fun n : ℕ => (obs μ (word f p n)/(n : ℝ)-rate μ f p)+
      obs μ (word f p M)/(n : ℝ)+rate μ f q/2) atTop (𝓝 (rate μ f q/2)) := by
    have hh := ((rate_tendsto μ f hf p hp).sub_const (rate μ f p)).add
      (tendsto_const_div_atTop_nhds_zero_nat (obs μ (word f p M)))
    simpa only [sub_self,zero_add] using hh.add_const (rate μ f q/2)
  have hh := le_of_tendsto_of_tendsto (rate_tendsto μ f hf q hq) hlim (show
      ∀ᶠ n : ℕ in atTop,obs μ (word f q n)/(n : ℝ)≤
        (obs μ (word f p n)/(n : ℝ)-rate μ f p)+
          obs μ (word f p M)/(n : ℝ)+rate μ f q/2 from by
    filter_upwards [eventually_ge_atTop 1] with n hn
    have hn0 : (0 : ℝ)<n := by exact_mod_cast hn
    apply (div_le_iff₀ hn0).mpr
    have h1 := div_mul_cancel₀ (obs μ (word f p n)) hn0.ne'
    have h2 := div_mul_cancel₀ (obs μ (word f p M)) hn0.ne'
    nlinarith [hb n])
  linarith

end StandardMapEntropy.Entropy

end
end

end OAI
end

section
-- module Solutions.OAIQ44_CM.StandardMap_Bernoulli_ReverseFano
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace StandardMapEntropy.Entropy
open MeasureTheory Set Filter
open scoped BigOperators ENNReal
variable {α β : Type*} [Fintype α] [Fintype β]

lemma shannon_ge_one_sub_max (p : α → ℝ) (hp : ∀ a,0≤p a)
    (hs : ∑ a,p a=1) (m : ℝ) (hm : ∀ a,p a ≤ m) : 1-m≤ shannon p := by
  have hh (a : α) : p a*(1-m)≤Real.negMulLog (p a) := by
    by_cases hz : p a=0
    · simp only [hz,zero_mul,Real.negMulLog_zero,le_refl]
    have hpos : 0<p a := lt_of_le_of_ne (hp a) (Ne.symm hz)
    have hl := mul_le_mul_of_nonneg_left (Real.log_le_sub_one_of_pos hpos) (hp a)
    have hu := mul_le_mul_of_nonneg_left (sub_le_sub_left (hm a) 1) (hp a)
    unfold Real.negMulLog
    nlinarith
  have hh := Finset.sum_le_sum (s := Finset.univ) (fun a _ => hh a)
  simpa only [←Finset.sum_mul,hs,one_mul,shannon] using hh

lemma shannon_ge_total_sub_max (p : α → ℝ) (hp : ∀ a,0≤p a)
    (a₀ : α) (hm : ∀ a,p a≤p a₀) :
    (∑ a,p a)-p a₀≤ shannon p-Real.negMulLog (∑ a,p a) := by
  let S := ∑ a,p a
  have hS : 0≤S := Finset.sum_nonneg (fun a _ => hp a)
  by_cases hz : S=0
  · have he (a : α) : p a=0 := le_antisymm ((Finset.single_le_sum
        (fun b _ => hp b) (Finset.mem_univ a)).trans_eq hz) (hp a)
    simp only [he,Finset.sum_const_zero,sub_self,shannon,Real.negMulLog_zero,le_refl]
  have hS0 : 0<S := lt_of_le_of_ne hS (Ne.symm hz)
  have ht := shannon_ge_one_sub_max (fun a => p a/S)
    (fun a => div_nonneg (hp a) hS) (by rw [←Finset.sum_div]; exact div_self hz)
    (p a₀/S) (fun a => div_le_div_of_nonneg_right (hm a) hS)
  have hs := shannon_scale (fun a => p a/S) S
  have he : (fun a => S*(p a/S))=p := by funext a; exact mul_div_cancel₀ _ hz
  rw [he,←Finset.sum_div,div_self hz,one_mul] at hs
  have hh := mul_le_mul_of_nonneg_left ht hS
  have hc : S*(1-p a₀/S)=S-p a₀ := by field_simp
  rw [hc] at hh
  dsimp only [S] at hs hh
  linarith

variable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
variable [MeasurableSpace α] [MeasurableSpace β]
variable [MeasurableSingletonClass α] [MeasurableSingletonClass β]

theorem exists_decoder_error_le_cond [Nonempty α] (p : Ω → α) (q : Ω → β)
    (hp : Measurable p) (hq : Measurable q) :
    ∃ g : β → α,(μ {x | p x≠g (q x)}).toReal ≤ cond μ p q := by
  classical
  let J (a : α) (b : β) := mass μ (fun x => (p x,q x)) (a,b)
  have hm (b : β) : ∃ a₀ : α,∀ a,J a b≤J a₀ b := by
    obtain ⟨a,ha,hm⟩ := Finset.exists_max_image Finset.univ (fun a => J a b) Finset.univ_nonempty
    exact ⟨a,fun a' => hm a' (Finset.mem_univ a')⟩
  choose g hg using hm
  refine ⟨g,?_⟩
  have hcol (b : β) : ∑ a,J a b=mass μ q b := (mass_joint_col μ p q hp hq b).symm
  have hbound (b : β) : mass μ q b-J (g b) b≤
      shannon (fun a => J a b)-Real.negMulLog (mass μ q b) := by
    have hs := shannon_ge_total_sub_max (fun a => J a b) (fun a => mass_nonneg μ _ _)
      (g b) (hg b)
    rwa [hcol b] at hs
  have hall := Finset.sum_le_sum (s := Finset.univ) (fun b _ => hbound b)
  have herr : (μ {x | p x≠g (q x)}).toReal=∑ b,(mass μ q b-J (g b) b) := by
    let e : α×β → Bool := fun ab => decide (ab.1≠g ab.2)
    have he : (fun x => (e ((p x,q x)))) ⁻¹' {true}={x | p x≠g (q x)} := by
      ext x
      simp [e]
    have hh := mass_joint_col μ (fun x => (p x,q x)) (e ∘ (fun x => (p x,q x)))
      (hp.prodMk hq) ((measurable_of_countable e).comp (hp.prodMk hq)) true
    change mass μ (fun x => e (p x,q x)) true=_ at hh
    rw [mass,he] at hh
    simp only [Function.comp_def,mass_pair_function,Fintype.sum_prod_type] at hh
    rw [hh,Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro b _
    rw [←hcol b]
    have hsum : (∑ a : α,if a=g b then 0 else J a b)+J (g b) b=∑ a,J a b := by
      have hsingle : (∑ a : α,if a=g b then J a b else 0)=J (g b) b := by simp
      rw [←hsingle,←Finset.sum_add_distrib]
      exact Finset.sum_congr rfl (fun a _ => by split_ifs <;> simp)
    have hid (a : α) : (if e (a,b)=true then J a b else 0)=if a=g b then 0 else J a b := by
      by_cases ha : a=g b <;> simp [e,ha]
    change (∑ a : α,if e (a,b)=true then J a b else 0)=(∑ a,J a b)-J (g b) b
    simp only [hid]
    exact (eq_sub_iff_add_eq.mpr hsum)
  rw [herr]
  unfold cond obs shannon
  simp only [Finset.sum_sub_distrib,shannon] at hall
  rw [Fintype.sum_prod_type,Finset.sum_comm]
  simpa only [Finset.sum_sub_distrib,J] using hall

end StandardMapEntropy.Entropy

end
section
open MeasureTheory Set Filter
open scoped ENNReal Topology

namespace HyperbolicCoding

lemma exists_eventual_decoder {Y B : Type*} [MeasurableSpace Y] [MeasurableSpace B]
    [Fintype B] [MeasurableSingletonClass B] [Nonempty B]
    (G : ℕ → Y → B) (hG : ∀ n,Measurable (G n)) :
    ∃ H : Y → B,Measurable H ∧ ∀ v b,(∀ᶠ n : ℕ in atTop,G n v=b) → H v=b := by
  classical
  let b₀ : B := Classical.choice inferInstance
  let E (b : B) : Set Y := {v | ∀ᶠ n : ℕ in atTop,G n v=b}
  have hEm (b : B) : MeasurableSet (E b) := by
    have he : E b=⋃ N : ℕ,⋂ n : ℕ,⋂ (_h : N≤n),(G n) ⁻¹' {b} := by
      ext v
      simp only [E,mem_ofPred_eq,eventually_atTop,mem_iUnion,mem_iInter,mem_preimage,mem_singleton_iff]
    rw [he]
    exact MeasurableSet.iUnion (fun N => MeasurableSet.iInter (fun n =>
      MeasurableSet.iInter (fun _ : N≤n => hG n (measurableSet_singleton b))))
  have huniq (v : Y) (b c : B) (hb : v∈E b) (hc : v∈E c) : b=c := by
    obtain ⟨n,hn⟩ := (hb.and hc).exists
    exact hn.1.symm.trans hn.2
  let H (v : Y) : B := if h : ∃ b,v∈E b then h.choose else b₀
  have hHb (v : Y) (b : B) (hb : v∈E b) : H v=b := by
    have he : ∃ b,v∈E b := ⟨b,hb⟩
    dsimp only [H]
    rw [dite_eq_left he]
    exact huniq v _ b he.choose_spec hb
  refine ⟨H,?_,hHb⟩
  apply measurable_to_countable'
  intro b
  have he : H ⁻¹' {b}=E b ∪ (if b=b₀ then (⋃ c,E c)ᶜ else ∅) := by
    ext v
    simp only [mem_preimage,mem_singleton_iff,mem_union]
    by_cases hv : ∃ c,v∈E c
    · have hn : v∉(⋃ c,E c)ᶜ := by simpa using hv
      have hh : H v=b ↔ v∈E b :=
        ⟨fun h => h ▸ (show v∈E (H v) from by simpa only [H,dite_eq_left hv] using hv.choose_spec),hHb v b⟩
      by_cases hb : b=b₀
      · rw [ite_eq_left hb]
        simpa only [hn,or_false] using hh
      · rw [ite_eq_right hb]
        simpa only [mem_empty_iff_false,or_false] using hh
    · have hh : H v=b₀ := dite_eq_right hv
      have hn : v∈(⋃ c,E c)ᶜ := by simpa using hv
      have hb : v∉E b := fun hb => hv ⟨b,hb⟩
      by_cases he : b=b₀
      · rw [ite_eq_left he]
        simp only [hn,or_true,iff_true]
        exact hh.trans he.symm
      · rw [ite_eq_right he]
        simp only [hb,mem_empty_iff_false,or_self,iff_false]
        exact fun hc => he (hc.symm.trans hh)
  rw [he]
  apply (hEm b).union
  split_ifs
  · exact (MeasurableSet.iUnion hEm).compl
  · exact MeasurableSet.empty

theorem exists_factor_of_approx {X Y B : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    [MeasurableSpace B] [Fintype B] [MeasurableSingletonClass B] [Nonempty B]
    (μ : Measure X) [IsFiniteMeasure μ] (Z : X → Y) (q : X → B)
    (happrox : ∀ ε : ℝ,0<ε → ∃ G : Y → B,Measurable G ∧
      μ {x | G (Z x)≠q x}<ENNReal.ofReal ε) :
    ∃ G : Y → B,Measurable G ∧ q=ᵐ[μ]G ∘ Z := by
  have happ (n : ℕ) := happrox ((1/2 : ℝ)^n) (pow_pos (by norm_num) n)
  choose G hG hsmall using happ
  obtain ⟨H,hH,hHb⟩ := exists_eventual_decoder G hG
  have hs : (∑' n : ℕ,μ {x | G n (Z x)≠q x})≠⊤ := by
    apply ne_top_of_le_ne_top ?_ (ENNReal.tsum_le_tsum (fun n => (hsmall n).le))
    simp only [ENNReal.ofReal_pow (by norm_num : (0 : ℝ)≤1/2),ENNReal.tsum_geometric]
    exact ENNReal.inv_ne_top.mpr (ne_of_gt (tsub_pos_iff_lt.mpr
      (ENNReal.ofReal_lt_one.mpr (by norm_num))))
  have ha := ae_eventually_notMem hs
  refine ⟨H,hH,?_⟩
  filter_upwards [ha] with x hx
  exact (hHb (Z x) (q x) (hx.mono (fun n hn => not_ne_iff.mp hn))).symm

end HyperbolicCoding

end
section
namespace StandardMapEntropy.Entropy
open HyperbolicCoding MeasureTheory Set Filter
open scoped Topology ENNReal
variable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
variable {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ]
variable [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ]
variable [MeasurableSingletonClass α] [MeasurableSingletonClass β] [MeasurableSingletonClass γ]

lemma cond_future_tendsto (f : Ω → Ω) (hf : MeasurePreserving f μ μ)
    (p : Ω → α) (hp : Measurable p) (n : ℕ) :
    Tendsto (fun m : ℕ => cond μ (word f p n) (fun x => word f p m (f^[n] x))) atTop
      (𝓝 ((n : ℝ)*rate μ f p)) := by
  simp_rw [cond_word_future_eq μ f hf p hp]
  induction n with
  | zero =>
    have he (m : ℕ) : obs μ (word f p (0+m))=obs μ (word f p m) := by
      have hi (a b : ℕ) (h : a=b) : obs μ (word f p a)=obs μ (word f p b) := by subst b; rfl
      exact hi _ _ (Nat.zero_add m)
    simpa only [he,sub_self,Nat.cast_zero,zero_mul] using
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 0))
  | succ n ih =>
    have ht : Tendsto (fun m : ℕ => n+m) atTop atTop :=
      tendsto_atTop_mono (fun m => Nat.le_add_left m n) tendsto_id
    have hd := (entropy_increment_tendsto μ f hf p hp).comp ht
    have hh := hd.add ih
    have he (m : ℕ) :
        (obs μ (word f p ((n+m)+1))-obs μ (word f p (n+m)))+
          (obs μ (word f p (n+m))-obs μ (word f p m))=
            obs μ (word f p (n+1+m))-obs μ (word f p m) := by
      rw [show n+1+m=n+m+1 from by omega]
      ring
    simp only [Function.comp_def,he] at hh
    convert hh using 1
    all_goals try with_reducible_and_instances rfl
    simp only [Nat.cast_add,Nat.cast_one]
    ring_nf

end StandardMapEntropy.Entropy

end
section
namespace StandardMapEntropy.Entropy
open MeasureTheory Set Filter
open scoped Topology
variable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
variable {α β : Type*} [Fintype α] [Fintype β]
variable [MeasurableSpace α] [MeasurableSpace β]
variable [MeasurableSingletonClass α] [MeasurableSingletonClass β]

omit [IsProbabilityMeasure μ] [MeasurableSpace α] [MeasurableSpace β]
  [MeasurableSingletonClass α] [MeasurableSingletonClass β] in
lemma obs_word_pair (f : Ω → Ω) (p : Ω → α) (q : Ω → β) (n : ℕ) :
    obs μ (word f (fun x => (p x,q x)) n)=obs μ (fun x => (word f p n x,word f q n x)) :=
  (obs_equiv μ (word f (fun x => (p x,q x)) n) (wordPairEquiv n)).symm

lemma rate_pair_ge_left (f : Ω → Ω) (hf : MeasurePreserving f μ μ)
    (p : Ω → α) (q : Ω → β) (hp : Measurable p) (hq : Measurable q) :
    rate μ f p ≤ rate μ f (fun x => (p x,q x)) := by
  apply le_of_tendsto_of_tendsto (rate_tendsto μ f hf p hp)
    (rate_tendsto μ f hf (fun x => (p x,q x)) (hp.prodMk hq))
  apply Eventually.of_forall
  intro n
  dsimp only
  rw [obs_word_pair]
  exact div_le_div_of_nonneg_right (obs_pair_ge_left μ (word f p n) (word f q n)
    (word_measurable f hf.measurable p hp n) (word_measurable f hf.measurable q hq n)) (Nat.cast_nonneg n)

lemma rate_pair_subadd (f : Ω → Ω) (hf : MeasurePreserving f μ μ)
    (p : Ω → α) (q : Ω → β) (hp : Measurable p) (hq : Measurable q) :
    rate μ f (fun x => (p x,q x)) ≤ rate μ f p+rate μ f q := by
  apply le_of_tendsto_of_tendsto (rate_tendsto μ f hf (fun x => (p x,q x)) (hp.prodMk hq))
    ((rate_tendsto μ f hf p hp).add (rate_tendsto μ f hf q hq))
  apply Eventually.of_forall
  intro n
  dsimp only
  rw [obs_word_pair,←add_div]
  exact div_le_div_of_nonneg_right (obs_pair_subadd_prob μ (word f p n) (word f q n)
    (word_measurable f hf.measurable p hp n) (word_measurable f hf.measurable q hq n)) (Nat.cast_nonneg n)

lemma rate_pair_eq_of_zero (f : Ω → Ω) (hf : MeasurePreserving f μ μ)
    (p : Ω → α) (q : Ω → β) (hp : Measurable p) (hq : Measurable q) (hz : rate μ f q=0) :
    rate μ f (fun x => (p x,q x))=rate μ f p := by
  have hl := rate_pair_ge_left μ f hf p q hp hq
  have hu := rate_pair_subadd μ f hf p q hp hq
  rw [hz,add_zero] at hu
  exact le_antisymm hu hl

omit [IsProbabilityMeasure μ] in
lemma rate_comp_iterate (f : Ω → Ω) (hf : MeasurePreserving f μ μ)
    (p : Ω → α) (hp : Measurable p) (s : ℕ) : rate μ f (p ∘ f^[s])=rate μ f p := by
  have he (n : ℕ) : word f (p ∘ f^[s]) n=(word f p n) ∘ f^[s] := by
    funext x i
    simp only [word,Function.comp_def,←Function.iterate_add_apply,Nat.add_comm]
  have hs (n : ℕ) : obs μ (word f (p ∘ f^[s]) n)=obs μ (word f p n) := by
    rw [he]
    exact obs_comp_preserving μ (f^[s]) (hf.iterate s) (word f p n) (word_measurable f hf.measurable p hp n)
  unfold rate
  simp only [hs]

end StandardMapEntropy.Entropy

end
section
namespace StandardMapEntropy.Entropy
open HyperbolicCoding MeasureTheory Set Filter
open scoped Topology
variable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
variable {α β : Type*} [Fintype α] [Fintype β]
variable [MeasurableSpace α] [MeasurableSpace β]
variable [MeasurableSingletonClass α] [MeasurableSingletonClass β]

lemma rate_mul_le_cond_future_zero (f : Ω → Ω) (hf : MeasurePreserving f μ μ)
    (p : Ω → α) (q : Ω → β) (hp : Measurable p) (hq : Measurable q)
    (hz : rate μ f q=0) (n M : ℕ) :
    (n : ℝ)*rate μ f p ≤ cond μ (word f p n) (fun x => (word f p M (f^[n] x),q x)) := by
  by_cases hn : n=0
  · subst n
    simp only [Nat.cast_zero,zero_mul]
    exact cond_nonneg μ (word f p 0) _ (word_measurable f hf.measurable p hp 0)
      (((word_measurable f hf.measurable p hp M).comp (hf.measurable.iterate 0)).prodMk hq)
  by_contra h
  have hε : 0<(n : ℝ)*rate μ f p-cond μ (word f p n) (fun x => (word f p M (f^[n] x),q x)) :=
    sub_pos.mpr (lt_of_not_ge h)
  have ht := cond_future_tendsto μ f hf q hq n
  rw [hz,mul_zero] at ht
  obtain ⟨L,hL,hLM⟩ := ((ht.eventually (gt_mem_nhds hε)).and (eventually_ge_atTop M)).exists
  let r : Ω → α×β := fun x => (p x,q x)
  let R : Ω → (Fin L → α×β) := fun x => word f r L (f^[n] x)
  have hR : Measurable R := (word_measurable f hf.measurable r (hp.prodMk hq) L).comp (hf.measurable.iterate n)
  have hpN := word_measurable f hf.measurable p hp n
  have hqN := word_measurable f hf.measurable q hq n
  have hlo := rate_mul_le_cond_future μ f hf r (hp.prodMk hq) n L
  rw [rate_pair_eq_of_zero μ f hf p q hp hq hz] at hlo
  have he : cond μ (word f r n) R=cond μ (word f q n) R+
      cond μ (word f p n) (fun x => (word f q n x,R x)) := by
    rw [←cond_equiv_left μ (word f r n) R
      ((wordPairEquiv n).trans (Equiv.prodComm (Fin n → α) (Fin n → β)))]
    exact cond_chain μ (word f q n) R (word f p n)
  change _ ≤ cond μ (word f r n) R at hlo
  rw [he] at hlo
  have hQ : cond μ (word f q n) R ≤ cond μ (word f q n) (fun x => word f q L (f^[n] x)) :=
    cond_factor_right μ (word f q n) R (fun v : Fin L → α×β => fun i => (v i).2) hqN hR
  let g (v : (Fin n → β)×(Fin L → α×β)) : (Fin M → α)×β :=
    (fun i => (v.2 ⟨i.val,lt_of_lt_of_le i.isLt hLM⟩).1,v.1 ⟨0,Nat.pos_of_ne_zero hn⟩)
  have hge : g ∘ (fun x => (word f q n x,R x))=
      (fun x => (word f p M (f^[n] x),q x)) := rfl
  have hP := cond_factor_right μ (word f p n) (fun x => (word f q n x,R x)) g hpN (hqN.prodMk hR)
  rw [hge] at hP
  linarith

lemma cond_future_zero_bound (f : Ω → Ω) (hf : MeasurePreserving f μ μ)
    (p : Ω → α) (q : Ω → β) (hp : Measurable p) (hq : Measurable q)
    (hz : rate μ f q=0) (n M : ℕ) :
    cond μ q (fun x => word f p M (f^[n] x)) ≤ cond μ q (word f p n)+
      cond μ (word f p n) (fun x => word f p M (f^[n] x))-(n : ℝ)*rate μ f p := by
  let P := word f p n
  let R : Ω → (Fin M → α) := fun x => word f p M (f^[n] x)
  have hPm : Measurable P := word_measurable f hf.measurable p hp n
  have hRm : Measurable R := (word_measurable f hf.measurable p hp M).comp (hf.measurable.iterate n)
  have hl := rate_mul_le_cond_future_zero μ f hf p q hp hq hz n M
  have hs := cond_pair_swap_right μ P q R
  have h1 := cond_chain μ P R q
  have h2 := cond_chain μ q R P
  have he : cond μ (fun x => (P x,q x)) R=cond μ (fun x => (q x,P x)) R :=
    (cond_equiv_left μ (fun x => (P x,q x)) R (Equiv.prodComm _ _)).symm
  have hu := cond_pair_right μ q P R hq hPm hRm
  change (n : ℝ)*rate μ f p ≤ cond μ P (fun x => (R x,q x)) at hl
  rw [←hs] at hl
  change cond μ q R ≤ cond μ q P+cond μ P R-(n : ℝ)*rate μ f p
  linarith

end StandardMapEntropy.Entropy

end
section
namespace StandardMapEntropy.Entropy
open MeasureTheory Set Filter
open scoped Topology
variable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
variable {α : Type*} [Fintype α] [MeasurableSpace α] [MeasurableSingletonClass α]

lemma inverse_iterate_forward_sub (e : Ω ≃ᵐ Ω) {M i : ℕ} (hi : i≤M) (x : Ω) :
    e.symm^[i] (e^[M] x)=e^[M-i] x := by
  have hx : e^[M] x=e^[i] (e^[M-i] x) := by
    rw [←Function.iterate_add_apply,show i+(M-i)=M from by omega]
  rw [hx]
  exact (show Function.LeftInverse (e.symm : Ω → Ω) e from e.symm_apply_apply).iterate i _

lemma forward_iterate_inverse_sub (e : Ω ≃ᵐ Ω) {M i : ℕ} (hi : i≤M) (x : Ω) :
    e^[M] (e.symm^[i] x)=e^[M-i] x := by
  have hx : e^[M] (e.symm^[i] x)=e^[M-i] (e^[i] (e.symm^[i] x)) := by
    rw [←Function.iterate_add_apply,show M-i+i=M from by omega]
  rw [hx,(show Function.LeftInverse (e : Ω → Ω) e.symm from e.apply_symm_apply).iterate i x]

omit [IsProbabilityMeasure μ] in
lemma obs_word_inverse (e : Ω ≃ᵐ Ω) (he : MeasurePreserving e μ μ)
    (p : Ω → α) (hp : Measurable p) (n : ℕ) :
    obs μ (word e.symm p n)=obs μ (word e p n) := by
  have hw : (word e.symm p n) ∘ e^[n-1]=(wordReverseEquiv n) ∘ word e p n := by
    funext x i
    change p (e.symm^[i.val] (e^[n-1] x))=p (e^[i.rev.val] x)
    rw [inverse_iterate_forward_sub e (by omega)]
    congr 2
    have h := Fin.val_rev i
    omega
  have h := obs_comp_preserving μ (e^[n-1]) (he.iterate (n-1)) (word e.symm p n)
    (word_measurable e.symm e.symm.measurable p hp n)
  rw [hw,obs_equiv] at h
  exact h.symm

omit [IsProbabilityMeasure μ] in
lemma rate_inverse (e : Ω ≃ᵐ Ω) (he : MeasurePreserving e μ μ)
    (p : Ω → α) (hp : Measurable p) : rate μ e.symm p=rate μ e p := by
  unfold rate
  simp only [obs_word_inverse μ e he p hp]

end StandardMapEntropy.Entropy

end
end

end OAI
end

section
-- module Solutions.OAIQ44_CM.StandardMap_Bernoulli_RohlinSinaiFinite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace HyperbolicCoding
open StandardMapEntropy.Entropy MeasureTheory Set Filter
open scoped Topology ENNReal
variable {X : Type*} [MeasurableSpace X] (μ : Measure X) [IsProbabilityMeasure μ]
variable {A B : Type*} [Fintype A] [Fintype B]
variable [MeasurableSpace A] [MeasurableSpace B]
variable [MeasurableSingletonClass A] [MeasurableSingletonClass B] [Nonempty B]

theorem zero_entropy_opposite_factor (e : X ≃ᵐ X) (he : MeasurePreserving e μ μ)
    (p : X → A) (q : X → B) (hp : Measurable p) (hq : Measurable q)
    (hz : rate μ e q=0)
    (hfactor : ∃ F : (ℕ → A) → B,Measurable F ∧ q=ᵐ[μ]F ∘ tailName e.symm p 0) :
    TailObservable μ e p q := by
  intro m
  apply exists_factor_of_approx μ (tailName e p m) q
  intro ε hε
  obtain ⟨M,hM⟩ := exists_cond_prefix_lt μ (measurable_tailName e.symm.measurable hp 0) hq
    hfactor (ε/2) (half_pos hε)
  change cond μ q (word e.symm p M)<ε/2 at hM
  let n := M+m+1
  let qS := q ∘ e^[M]
  have hqS : Measurable qS := hq.comp (e.measurable.iterate M)
  have hqz : rate μ e qS=0 := (rate_comp_iterate μ e he q hq M).trans hz
  let g₀ (v : Fin n → A) (i : Fin M) := v ⟨M-i.val,by dsimp [n]; omega⟩
  have hg₀ : g₀ ∘ word e p n=(word e.symm p M) ∘ e^[M] := by
    funext x i
    change p (e^[M-i.val] x)=p (e.symm^[i.val] (e^[M] x))
    rw [inverse_iterate_forward_sub e (by omega)]
  have hP : cond μ qS (word e p n) ≤ cond μ q (word e.symm p M) := by
    have hh := cond_factor_right μ qS (word e p n) g₀ hqS (word_measurable e e.measurable p hp n)
    rw [hg₀] at hh
    exact hh.trans_eq (cond_comp_preserving μ (e^[M]) (he.iterate M) q (word e.symm p M)
      hq (word_measurable e.symm e.symm.measurable p hp M))
  have hsmall : cond μ qS (word e p n)<ε := lt_trans (hP.trans_lt hM) (by linarith)
  have ht : Tendsto (fun L : ℕ => cond μ qS (word e p n)+
      cond μ (word e p n) (fun x => word e p L (e^[n] x))-(n : ℝ)*rate μ e p)
      atTop (𝓝 (cond μ qS (word e p n))) := by
    simpa only [add_sub_cancel_right] using
      ((cond_future_tendsto μ e he p hp n).const_add (cond μ qS (word e p n))).sub_const ((n : ℝ)*rate μ e p)
  obtain ⟨L,hL⟩ := (ht.eventually (gt_mem_nhds hsmall)).exists
  let r : X → (Fin L → A) := fun x => word e p L (e^[n] x)
  have hr : Measurable r := (word_measurable e e.measurable p hp L).comp (e.measurable.iterate n)
  have hc : cond μ qS r<ε := (cond_future_zero_bound μ e he p qS hp hqS hqz n L).trans_lt hL
  obtain ⟨g,hg⟩ := exists_decoder_error_le_cond μ qS r hqS hr
  let G (v : ℕ → A) := g (fun i : Fin L => v (i.val+1))
  have hG : Measurable G := (measurable_of_countable g).comp
    (Measurable.of_eval (fun i : Fin L => measurable_pi_apply (i.val+1)))
  have hcancel (x : X) : e^[M] (e.symm^[M] x)=x :=
    (show Function.LeftInverse (e : X → X) e.symm from e.apply_symm_apply).iterate M x
  have hnM : M≤n := by dsimp [n]; omega
  have hrx (x : X) : r (e.symm^[M] x)=(fun i : Fin L => tailName e p m x (i.val+1)) := by
    funext i
    change p (e^[i.val] (e^[n] (e.symm^[M] x)))=p (e^[i.val+1+m] x)
    rw [forward_iterate_inverse_sub e hnM,←Function.iterate_add_apply]
    congr 2
    dsimp [n]
    omega
  have hset : {x | G (tailName e p m x)≠q x}=
      (e.symm^[M]) ⁻¹' {x | qS x≠g (r x)} := by
    ext x
    change g (fun i : Fin L => tailName e p m x (i.val+1))≠q x ↔
      q (e^[M] (e.symm^[M] x))≠g (r (e.symm^[M] x))
    rw [hcancel,hrx]
    exact ne_comm
  have hEm : MeasurableSet {x | qS x≠g (r x)} :=
    (measurableSet_eq_fun hqS ((measurable_of_countable g).comp hr)).compl
  refine ⟨G,hG,?_⟩
  rw [hset,((he.symm e).iterate M).measure_preimage hEm.nullMeasurableSet,
    ←ENNReal.toReal_lt_toReal (measure_ne_top _ _) ENNReal.ofReal_ne_top,ENNReal.toReal_ofReal hε.le]
  exact hg.trans_lt hc

theorem TailObservable.reverse (e : X ≃ᵐ X) (he : MeasurePreserving e μ μ)
    (p : X → A) (q : X → B) (hp : Measurable p) (hq : Measurable q)
    (ht : TailObservable μ e p q) : TailObservable μ e.symm p q := by
  have hz := tailObservable_rate_zero μ e he p hp q hq ht
  apply zero_entropy_opposite_factor μ e.symm (he.symm e) p q hp hq
  · simpa only [rate_inverse μ e he q hq] using hz
  · simpa only [MeasurableEquiv.symm_symm] using ht 0

end HyperbolicCoding

end
section
namespace HyperbolicCoding
open MeasureTheory Set Filter
variable {X A : Type*} [MeasurableSpace X] [MeasurableSpace A]
variable {μ : Measure X} {T : X → X} {α : X → A} {E F : Set X}

lemma TailEvent.congr (hE : TailEvent μ T α E) (hEF : E=ᵐ[μ]F) : TailEvent μ T α F := by
  intro m
  obtain ⟨D,hD,he⟩ := hE m
  exact ⟨D,hD,hEF.symm.trans he⟩

lemma TailEvent.nullMeasurable (hT : Measurable T) (hα : Measurable α)
    (hE : TailEvent μ T α E) : NullMeasurableSet E μ := by
  obtain ⟨D,hD,he⟩ := hE 0
  exact (hD.preimage (measurable_tailName hT hα 0)).nullMeasurableSet.congr he.symm

lemma TailEvent.univ : TailEvent μ T α (Set.univ : Set X) := by
  intro m
  exact ⟨Set.univ,MeasurableSet.univ,by simp⟩

lemma TailEvent.compl (hE : TailEvent μ T α E) : TailEvent μ T α Eᶜ := by
  intro m
  obtain ⟨D,hD,he⟩ := hE m
  refine ⟨Dᶜ,hD.compl,?_⟩
  filter_upwards [he] with x hx
  exact congrArg Not hx

lemma TailEvent.iInter {I : Type*} [Countable I] {E : I → Set X}
    (hE : ∀ i,TailEvent μ T α (E i)) : TailEvent μ T α (⋂ i,E i) := by
  intro m
  choose D hD he using fun i => hE i m
  refine ⟨⋂ i,D i,MeasurableSet.iInter hD,?_⟩
  filter_upwards [ae_all_iff.mpr he] with x hx
  change (x∈⋂ i,E i)=(tailName T α m x∈⋂ i,D i)
  exact propext (by simp only [mem_iInter]; exact forall_congr' (fun i => Iff.of_eq (hx i)))

lemma TailEvent.inter (hE : TailEvent μ T α E) (hF : TailEvent μ T α F) :
    TailEvent μ T α (E∩F) := by
  intro m
  obtain ⟨D,hD,he⟩ := hE m
  obtain ⟨C,hC,hf⟩ := hF m
  refine ⟨D∩C,hD.inter hC,?_⟩
  filter_upwards [he,hf] with x hx hy
  exact congrArg₂ And hx hy

lemma TailEvent.preimage (hT : MeasurePreserving T μ μ) (hE : TailEvent μ T α E) :
    TailEvent μ T α (T ⁻¹' E) := by
  intro m
  obtain ⟨D,hD,he⟩ := hE m
  let σ (v : ℕ → A) (n : ℕ) := v (n+1)
  refine ⟨σ ⁻¹' D,hD.preimage (Measurable.of_eval (fun n => measurable_pi_apply (n+1))),?_⟩
  filter_upwards [hT.quasiMeasurePreserving.ae he] with x hx
  change (T x∈E)=(σ (tailName T α m x)∈D)
  change (T x∈E)=(tailName T α m (T x)∈D) at hx
  rw [hx]
  congr 1
  funext n
  simp only [tailName,σ,←Function.iterate_succ_apply]
  congr 2
  omega

lemma TailEvent.reverse [IsProbabilityMeasure μ] [Fintype A] [MeasurableSingletonClass A]
    (e : X ≃ᵐ X) (he : MeasurePreserving e μ μ) (hα : Measurable α)
    (hE : TailEvent μ e α E) : TailEvent μ e.symm α E := by
  classical
  obtain ⟨D,hD,hED⟩ := hE 0
  let F := tailName e α 0 ⁻¹' D
  have hF : MeasurableSet F := hD.preimage (measurable_tailName e.measurable hα 0)
  have hq : Measurable (fun x => decide (x∈F)) := by
    have hf : Measurable (fun x => if x∈F then (true : Bool) else false) := Measurable.ite hF measurable_const measurable_const
    convert hf using 1
    all_goals try with_reducible_and_instances rfl
    funext x
    by_cases hx : x∈F <;> simp [hx]
  have ht := (tailEvent_bool (hE.congr hED)).reverse μ e he α _ hα hq
  intro m
  obtain ⟨G,hG,hqG⟩ := ht m
  refine ⟨G ⁻¹' {true},hG (measurableSet_singleton true),?_⟩
  filter_upwards [hED,hqG] with x hx hy
  change (x∈E)=(G (tailName e.symm α m x)=true)
  change (x∈E)=(x∈F) at hx
  rw [hx]
  simpa only [Function.comp_def,decide_eq_true_eq] using congrArg (· = true) hy

end HyperbolicCoding

end
section
namespace HyperbolicCoding
open MeasureTheory Set Filter
open scoped ENNReal Topology
variable {X A : Type*} [MeasurableSpace X] [MeasurableSpace A]
variable {μ : Measure X} [IsFiniteMeasure μ] {T : X → X} {α : X → A}

theorem exists_tailAtom_of_local_constancy (hT : Measurable T) (hα : Measurable α)
    {H : Set X} (hHp : 0<μ H)
    (hc : ∀ E,TailEvent μ T α E → H ≤ᵐ[μ] E ∨ H ≤ᵐ[μ] Eᶜ) :
    ∃ C : Set X,IsTailAtom μ T α C := by
  classical
  let S : Set ℝ≥0∞ := {r | ∃ E : Set X,TailEvent μ T α E ∧ H ≤ᵐ[μ] E ∧ μ E=r}
  have hS : S.Nonempty := ⟨μ univ,univ,TailEvent.univ,ae_of_all _ (fun x _ => @Set.mem_univ X x),rfl⟩
  obtain ⟨u,_,hu,hun⟩ := exists_seq_tendsto_sInf hS (OrderBot.bddBelow S)
  choose C hCt hHC hμC using hun
  let D : Set X := ⋂ n : ℕ,C n
  have hDt : TailEvent μ T α D := TailEvent.iInter hCt
  have hHD : H ≤ᵐ[μ] D := by
    filter_upwards [ae_all_iff.mpr hHC] with x hx hH
    exact mem_iInter.mpr (fun n => hx n hH)
  have hDmin : ∀ E,TailEvent μ T α E → H ≤ᵐ[μ] E → μ D≤μ E := by
    intro E ht hHE
    have hi : μ D ≤ sInf S := ge_of_tendsto hu (Eventually.of_forall (fun n => by
      rw [←hμC n]
      exact measure_mono (iInter_subset C n)))
    exact hi.trans (sInf_le (show μ E∈S from ⟨E,ht,hHE,rfl⟩))
  have hDp : 0<μ D := hHp.trans_le (measure_mono_ae hHD)
  refine ⟨D,hDt,hDp,?_⟩
  intro E hE
  have hmem (F : Set X) (hF : TailEvent μ T α F) (hHF : H ≤ᵐ[μ] F) : D ≤ᵐ[μ] F := by
    have hsub : (D∩F : Set X) ≤ᵐ[μ] D := ae_of_all _ (fun _ hx => hx.1)
    have hHDF : H ≤ᵐ[μ] (D∩F : Set X) := by
      filter_upwards [hHD,hHF] with x hx hy hz
      exact ⟨hx hz,hy hz⟩
    have he := ae_eq_of_ae_subset_of_measure_ge hsub (hDmin _ (hDt.inter hF) hHDF)
      ((hDt.inter hF).nullMeasurable hT hα) (measure_ne_top μ D)
    filter_upwards [he] with x hx hD
    exact ((Iff.of_eq hx).mpr hD).2
  rcases hc E hE with he|he
  · exact Or.inl (hmem E hE he)
  · exact Or.inr (hmem Eᶜ hE.compl he)

theorem tail_trivial_of_atom (hT : MeasurePreserving T μ μ) (hα : Measurable α)
    (herg : ∀ n : ℕ,0<n → Ergodic (T^[n]) μ)
    {C : Set X} (hC : IsTailAtom μ T α C) :
    ∀ E,TailEvent μ T α E → (∀ᵐ x ∂μ,x∈E) ∨ (∀ᵐ x ∂μ,x∉E) := by
  have hCm := hC.1.nullMeasurable hT.measurable hα
  obtain ⟨n,hn,hi⟩ := hT.conservative.exists_gt_measure_inter_ne_zero hCm hC.2.1.ne' 0
  have hpre : TailEvent μ T α (T^[n] ⁻¹' C) := by
    clear hn hi
    induction n with
    | zero => simpa using hC.1
    | succ n ih =>
      convert ih.preimage hT using 1
      all_goals try with_reducible_and_instances rfl
      ext x
      simp only [mem_preimage,Function.iterate_succ_apply]
  have hsub : C ≤ᵐ[μ] (T^[n] ⁻¹' C) := by
    rcases hC.2.2 _ hpre with hh|hh
    · exact hh
    · have hz : μ (C∩T^[n] ⁻¹' C)=0 := by
        apply measure_mono_null_ae (t := (∅ : Set X)) _ (measure_empty)
        filter_upwards [hh] with x hx hy
        exact (hx hy.1 hy.2).elim
      exact (hi hz).elim
  have heq := ae_eq_of_ae_subset_of_measure_ge hsub
    ((hT.iterate n).measure_preimage hCm).le hCm (measure_ne_top μ _)
  have hfull : ∀ᵐ x ∂μ,x∈C := by
    rcases (herg n hn).quasiErgodic.ae_mem_or_ae_notMem₀ hCm heq.symm with hh|hh
    · exact hh
    · have hz : μ C=0 := by simpa only [ae_iff,not_not,Set.ofPred_mem_eq] using hh
      exact (hC.2.1.ne' hz).elim
  intro E hE
  rcases hC.2.2 E hE with hh|hh
  · exact Or.inl (hfull.mp hh)
  · exact Or.inr (hfull.mp hh)

end HyperbolicCoding

end
section
open MeasureTheory MeasureTheory.Measure Set Filter
open scoped Topology ENNReal symmDiff

namespace HyperbolicCoding

lemma law_distance_le_disagreement {Ω Y : Type*} [MeasurableSpace Ω] [MeasurableSpace Y]
    (κ : Measure Ω) [IsFiniteMeasure κ] {p q : Ω → Y}
    (hp : Measurable p) (hq : Measurable q) {D : Set Y} (hD : MeasurableSet D) :
    |(κ.map p).real D-(κ.map q).real D|≤κ.real {w | p w≠q w} := by
  simp only [Measure.real,Measure.map_apply hp hD,Measure.map_apply hq hD]
  apply (abs_measureReal_sub_le_measureReal_symmDiff
    (hD.preimage hp).nullMeasurableSet (hD.preimage hq).nullMeasurableSet).trans
  apply ENNReal.toReal_mono (measure_ne_top _ _)
  apply measure_mono
  intro w hw he
  have hh : (w∈p ⁻¹' D)=(w∈q ⁻¹' D) := by simp only [mem_preimage,he]
  simp only [Set.mem_symmDiff,hh,and_not_self,or_self] at hw

lemma tail_disagreement_tendsto_zero {Ω X A : Type*}
    [MeasurableSpace Ω] [MeasurableSpace X] [MeasurableSpace A] [MeasurableEq A]
    (κ : Measure Ω) [IsFiniteMeasure κ] {T : X → X} (hT : Measurable T)
    {α : X → A} (hα : Measurable α) {p q : Ω → X}
    (hp : Measurable p) (hq : Measurable q)
    (hname : ∀ᵐ w ∂κ,∀ᶠ n : ℕ in atTop,α (T^[n] (p w))=α (T^[n] (q w))) :
    Tendsto (fun m : ℕ => κ.real {w | tailName T α m (p w)≠tailName T α m (q w)})
      atTop (𝓝 0) := by
  let D (m : ℕ) : Set Ω := {w | tailName T α m (p w)≠tailName T α m (q w)}
  have hDm (m : ℕ) : MeasurableSet (D m) := by
    have he : {w | tailName T α m (p w)=tailName T α m (q w)}=
        ⋂ n : ℕ,{w | α (T^[n+m] (p w))=α (T^[n+m] (q w))} := by
      ext w
      simp only [mem_ofPred_eq,mem_iInter,funext_iff,tailName]
    change MeasurableSet ({w | tailName T α m (p w)=tailName T α m (q w)}ᶜ)
    rw [he]
    exact (MeasurableSet.iInter (fun n => measurableSet_eq_fun
      ((hα.comp (hT.iterate (n+m))).comp hp) ((hα.comp (hT.iterate (n+m))).comp hq))).compl
  have hDanti : Antitone D := by
    intro m n hmn w hw hwm
    apply hw
    funext i
    have hi := congrFun hwm (i+n-m)
    simpa only [tailName,show i+n-m+m=i+n from by omega] using hi
  have hi : κ (⋂ m,D m)=0 := by
    apply measure_eq_zero_iff_ae_notMem.mpr
    filter_upwards [hname] with w hw hmem
    obtain ⟨m,hm⟩ := eventually_atTop.mp hw
    apply (mem_iInter.mp hmem m)
    funext i
    exact hm (i+m) (by omega)
  have h := tendsto_measure_iInter_atTop (μ := κ) (fun m => (hDm m).nullMeasurableSet)
    hDanti ⟨0,measure_ne_top _ _⟩
  rw [hi] at h
  have ht := (ENNReal.tendsto_toReal (by simp : (0 : ℝ≥0∞)≠⊤)).comp h
  simpa only [Function.comp_def,ENNReal.toReal_zero,Measure.real,D] using ht

end HyperbolicCoding

end
section
open MeasureTheory MeasureTheory.Measure Set Filter
open scoped ENNReal

namespace HyperbolicCoding

lemma map_withDensity_comp {Ω X : Type*} [MeasurableSpace Ω] [MeasurableSpace X]
    (κ : Measure Ω) {π : Ω → X} (hπ : Measurable π) {w : X → ℝ≥0∞} (hw : Measurable w) :
    (κ.withDensity (w ∘ π)).map π=(κ.map π).withDensity w := by
  ext D hD
  rw [Measure.map_apply hπ hD,withDensity_apply _ (hD.preimage hπ),
    withDensity_apply _ hD]
  exact (setLIntegral_map hD hw hπ).symm

theorem exists_exact_density_lift {Ω X : Type*} [MeasurableSpace Ω] [MeasurableSpace X]
    (κ : Measure Ω) (μ : Measure X) [IsProbabilityMeasure κ] [IsFiniteMeasure μ]
    {π : Ω → X} (hπ : Measurable π) (hac : κ.map π≪μ) :
    ∃ H : Set X,MeasurableSet H ∧ 0<μ H ∧
      ∃ w : Ω → ℝ≥0∞,Measurable w ∧
        MeasurePreserving π (κ.withDensity w) ((μ H)⁻¹ • μ.restrict H) ∧
        IsProbabilityMeasure (κ.withDensity w) ∧ κ.withDensity w≪κ := by
  let η := κ.map π
  have : IsProbabilityMeasure η := by first | infer_instance | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | (apply Measurable.aemeasurable; measurability) | measurability)
  let H : Set X := {x | η.rnDeriv μ x≠0}
  have hH : MeasurableSet H := (measurableSet_eq_fun (measurable_rnDeriv η μ) measurable_const).compl
  have hηH : η H=1 := by
    have hh : ∀ᵐ x ∂η,x∈H := (rnDeriv_pos hac).mono (fun _ hx => hx.ne')
    rw [← measure_univ (μ := η)]
    apply measure_congr
    filter_upwards [hh] with x hx
    exact propext ⟨fun _ => trivial, fun _ => hx⟩
  have hp : 0<μ H := by
    apply pos_iff_ne_zero.mpr
    intro hh
    have hz := hac hh
    rw [hηH] at hz
    exact one_ne_zero hz
  have hres : μ.restrict H≪η := by
    have hh : μ.restrict H≪(μ.restrict H).withDensity (η.rnDeriv μ) :=
      withDensity_absolutelyContinuous' (measurable_rnDeriv η μ).aemeasurable
        (by filter_upwards [ae_restrict_mem hH] with x hx; exact hx)
    rw [← restrict_withDensity hH,withDensity_rnDeriv_eq η μ hac] at hh
    exact hh.trans Measure.absolutelyContinuous_restrict
  let σ := (μ H)⁻¹ • μ.restrict H
  have hσ : σ≪η := smul_absolutelyContinuous.trans hres
  have : IsProbabilityMeasure σ := by
    constructor
    simp only [σ,Measure.smul_apply,Measure.restrict_apply_univ,smul_eq_mul]
    exact ENNReal.inv_mul_cancel hp.ne' (measure_ne_top μ H)
  let w := σ.rnDeriv η ∘ π
  have hw : Measurable w := (measurable_rnDeriv σ η).comp hπ
  have hm : MeasurePreserving π (κ.withDensity w) σ := by
    refine ⟨hπ,?_⟩
    rw [show w=σ.rnDeriv η ∘ π from rfl,map_withDensity_comp κ hπ (measurable_rnDeriv σ η)]
    exact withDensity_rnDeriv_eq σ η hσ
  have hprob : IsProbabilityMeasure (κ.withDensity w) := by
    constructor
    have hu := congrArg (fun ν : Measure X => ν univ) hm.map_eq
    rw [Measure.map_apply hπ MeasurableSet.univ,preimage_univ,show σ univ=1 from measure_univ] at hu
    exact hu
  exact ⟨H,hH,hp,w,hw,hm,hprob,withDensity_absolutelyContinuous κ w⟩

end HyperbolicCoding

end
section
namespace HyperbolicCoding
open MeasureTheory MeasureTheory.Measure Set Filter
open scoped ENNReal Topology
variable {X Ω A : Type*} [MeasurableSpace X] [MeasurableSpace Ω] [MeasurableSpace A]
variable [Fintype A] [MeasurableSingletonClass A]

theorem tailAtom_of_rectangle (μ : Measure X) (κ : Measure Ω)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure κ]
    (e : X ≃ᵐ X) (he : MeasurePreserving e μ μ)
    (α : X → A) (hα : Measurable α) {π : Ω → X}
    (hπ : QuasiMeasurePreserving π κ μ)
    (hc : ∀ E : Set X,TailEvent μ e α E → TailEvent μ e.symm α E →
      ∃ c : Prop,∀ᵐ p ∂κ,(π p∈E ↔ c)) :
    ∃ C : Set X,IsTailAtom μ e α C := by
  obtain ⟨H,hH,hHp,w,_,hm,_,hac⟩ := exists_exact_density_lift κ μ hπ.measurable hπ.absolutelyContinuous
  apply exists_tailAtom_of_local_constancy e.measurable hα hHp
  intro E hE
  obtain ⟨D,hD,heD⟩ := hE 0
  let F := tailName e α 0 ⁻¹' D
  have hF : MeasurableSet F := hD.preimage (measurable_tailName e.measurable hα 0)
  have hFt : TailEvent μ e α F := hE.congr heD
  obtain ⟨c,hc⟩ := hc F hFt (hFt.reverse e he hα)
  have hconst : ∀ᵐ p ∂κ.withDensity w,(π p∈F ↔ c) := hac.ae_le hc
  have hnorm : ∀ {p : X → Prop},(∀ᵐ x ∂((μ H)⁻¹ • μ.restrict H),p x) →
      ∀ᵐ x ∂μ,x∈H → p x := fun hh =>
    (ae_restrict_iff' hH).mp ((ae_ennreal_smul_measure_iff (ENNReal.inv_ne_zero.mpr (measure_ne_top μ H))).mp hh)
  by_cases hc : c
  · have hh : ∀ᵐ p ∂κ.withDensity w,π p∈F := hconst.mono (fun _ hp => hp.mpr hc)
    have hf : ∀ᵐ x ∂((μ H)⁻¹ • μ.restrict H),x∈F := by
      rw [←hm.map_eq]
      exact (ae_map_iff hm.measurable.aemeasurable hF).mpr hh
    refine Or.inl ?_
    filter_upwards [hnorm hf,heD] with x hx hy hz
    exact (Iff.of_eq hy).mpr (hx hz)
  · have hh : ∀ᵐ p ∂κ.withDensity w,π p∉F := hconst.mono (fun _ hp hf => hc (hp.mp hf))
    have hf : ∀ᵐ x ∂((μ H)⁻¹ • μ.restrict H),x∉F := by
      rw [←hm.map_eq]
      exact (ae_map_iff hm.measurable.aemeasurable hF.compl).mpr hh
    refine Or.inr ?_
    filter_upwards [hnorm hf,heD] with x hx hy hz hE
    exact hx hz ((Iff.of_eq hy).mp hE)

end HyperbolicCoding

end
end

end OAI
end

section
-- module Solutions.OAIQ44_CM.StandardMap_Bernoulli_IntegerDynamics
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open MeasureTheory Set Filter

namespace HyperbolicCoding
variable {X A : Type*} [MeasurableSpace X]

lemma iterateEquiv_apply (e : X ≃ᵐ X) (n : ℕ) (x : X) : iterateEquiv e n x=e^[n] x := by
  change ((e.toEquiv^n) x)=_
  rw [Equiv.Perm.coe_pow]
  rfl

end HyperbolicCoding

end
section
namespace HyperbolicCoding
open MeasureTheory MeasureTheory.Measure Set Filter
lemma iterateEquiv_symm_apply {X : Type*} [MeasurableSpace X] (e : X ≃ᵐ X) (N : ℕ) (x : X) :
    (iterateEquiv e N).symm x=e.symm^[N] x := by
  change ((e.toEquiv^N)⁻¹ x)=_
  rw [←inv_pow,Equiv.Perm.inv_def,Equiv.Perm.coe_pow]
  rfl
end HyperbolicCoding

end
section

namespace StandardMapEntropy
open MeasureTheory MeasureTheory.Measure Set Filter Topology HyperbolicCoding
open scoped ENNReal
namespace ReversibleGraphRectangle
variable {k χ : ℝ} {B : ReversibleRectangleBlock k χ} {F : ReversibleGraphFamilies B}
    (R : ReversibleGraphRectangle F)

theorem doubleTail_constant_of_good_names {N : ℕ} (hN : 0<N)
    (μ : Measure Torus) [IsProbabilityMeasure μ]
    (hπ : QuasiMeasurePreserving R.torusPoint (B.carrierProbability.prod B.carrierProbability) μ)
    {A : Type*} [MeasurableSpace A] (α : Torus → A)
    (hf : GoodNames μ ((standardMap k)^[N]) α)
    (hb : GoodNames μ ((inverseMap k)^[N]) α)
    (E : Set Torus)
    (hEf : TailEvent μ ((standardMap k)^[N]) α E)
    (hEb : TailEvent μ ((inverseMap k)^[N]) α E) :
    ∃ c : Prop,∀ᵐ p ∂B.carrierProbability.prod B.carrierProbability,(R.torusPoint p∈E ↔ c) := by
  obtain ⟨Qf,hQf,hSatf⟩ := tailEvent_saturation μ hf hEf
  obtain ⟨Qb,hQb,hSatb⟩ := tailEvent_saturation μ hb hEb
  have hQ := hπ.ae (hQf.and hQb)
  have hrow (a b b' : B.coordinateCarrier)
      (hx : R.torusPoint (a,b)∈Qf ∧ R.torusPoint (a,b)∈Qb)
      (hy : R.torusPoint (a,b')∈Qf ∧ R.torusPoint (a,b')∈Qb) :
      (R.torusPoint (a,b)∈E)=(R.torusPoint (a,b')∈E) :=
    propext (hSatf _ hx.1 _ hy.1 ((R.row_exponential a b b').iterate hN))
  have hcol (a a' b : B.coordinateCarrier)
      (hx : R.torusPoint (a,b)∈Qf ∧ R.torusPoint (a,b)∈Qb)
      (hy : R.torusPoint (a',b)∈Qf ∧ R.torusPoint (a',b)∈Qb) :
      (R.torusPoint (a,b)∈E)=(R.torusPoint (a',b)∈E) :=
    propext (hSatb _ hx.2 _ hy.2 ((R.column_exponential a a' b).iterate hN))
  obtain ⟨c,hc⟩ := ae_constant_of_product_rows_columns
    (F := fun p => R.torusPoint p∈E) hQ hrow hcol
  exact ⟨c,hc.mono (fun p hp => Iff.of_eq hp)⟩

theorem tail_trivial_of_good_names {N : ℕ} (hN : 0<N)
    (μ : Measure Torus) [IsProbabilityMeasure μ]
    (herg : ∀ r : ℕ,0 < r → Ergodic (((standardMap k)^[N])^[r]) μ)
    (hπ : QuasiMeasurePreserving R.torusPoint (B.carrierProbability.prod B.carrierProbability) μ)
    {A : Type*} [Fintype A] [MeasurableSpace A] [MeasurableSingletonClass A]
    (α : Torus → A) (hα : Measurable α)
    (hf : GoodNames μ ((standardMap k)^[N]) α)
    (hb : GoodNames μ ((inverseMap k)^[N]) α) :
    ∀ E,TailEvent μ ((standardMap k)^[N]) α E → (∀ᵐ x ∂μ,x∈E) ∨ (∀ᵐ x ∂μ,x∉E) := by
  let e := iterateEquiv (standardMap_measurableEquiv k) N
  have heq : (e : Torus → Torus)=(standardMap k)^[N] := funext (iterateEquiv_apply _ N)
  have heq' : (e.symm : Torus → Torus)=(inverseMap k)^[N] := funext (iterateEquiv_symm_apply _ N)
  have he : MeasurePreserving e μ μ := by
    rw [heq]
    simpa only [Function.iterate_one] using (herg 1 (by omega)).toMeasurePreserving
  obtain ⟨C,hC⟩ := tailAtom_of_rectangle μ (B.carrierProbability.prod B.carrierProbability)
    e he α hα hπ (by
      intro D hDf hDb
      rw [heq] at hDf
      rw [heq'] at hDb
      exact R.doubleTail_constant_of_good_names hN μ hπ α hf hb D hDf hDb)
  rw [heq] at hC
  have hT : MeasurePreserving ((standardMap k)^[N]) μ μ := by rwa [heq] at he
  exact tail_trivial_of_atom hT hα herg hC

theorem exists_good_K_partitions {N : ℕ} (hN : 0<N)
    (μ : Measure Torus) [IsProbabilityMeasure μ]
    (herg : ∀ r : ℕ,0 < r → Ergodic (((standardMap k)^[N])^[r]) μ)
    (hπ : QuasiMeasurePreserving R.torusPoint (B.carrierProbability.prod B.carrierProbability) μ) :
    ∃ α : ℕ → ℕ → Torus → Bool,
      (∀ i j,Measurable (α i j)) ∧ Function.Injective (fun z => fun i j => α i j z) ∧
      ∀ M : ℕ,GoodNames μ ((standardMap k)^[N]) (joinedBinary α M) ∧
        GoodNames μ ((inverseMap k)^[N]) (joinedBinary α M) ∧
        (∀ E,TailEvent μ ((standardMap k)^[N]) (joinedBinary α M) E →
          (∀ᵐ x ∂μ,x∈E) ∨ (∀ᵐ x ∂μ,x∉E)) := by
  obtain ⟨α,hm,hi,hf,hb⟩ := exists_good_binary_partitions μ
    ((measurePreserving_standardMap k).measurable.iterate N)
    ((measurePreserving_inverseMap k).measurable.iterate N)
  refine ⟨α,hm,hi,?_⟩
  intro M
  have hfM : GoodNames μ ((standardMap k)^[N]) (joinedBinary α M) :=
    hf.mono (fun x hx y hy => hx y hy M)
  have hbM : GoodNames μ ((inverseMap k)^[N]) (joinedBinary α M) :=
    hb.mono (fun x hx y hy => hx y hy M)
  exact ⟨hfM,hbM,R.tail_trivial_of_good_names hN μ herg hπ _ (measurable_joinedBinary hm M) hfM hbM⟩

end ReversibleGraphRectangle
end StandardMapEntropy

end
section
namespace HyperbolicCoding
open MeasureTheory MeasureTheory.Measure Set Filter
open scoped ENNReal Topology
variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]

lemma LawClose.triangle {μ ν κ : Measure X} {ε δ : ℝ}
    (h : LawClose μ ν ε) (h' : LawClose ν κ δ) : LawClose μ κ (ε+δ) := by
  intro D hD
  exact (abs_sub_le (μ.real D) (ν.real D) (κ.real D)).trans (add_le_add (h D hD) (h' D hD))

lemma LawClose.map {μ ν : Measure X} {ε : ℝ} (h : LawClose μ ν ε)
    {f : X → Y} (hf : Measurable f) : LawClose (μ.map f) (ν.map f) ε := by
  intro D hD
  simp only [Measure.real,Measure.map_apply hf hD]
  exact h _ (hD.preimage hf)

lemma real_prod_apply (μ : Measure X) (ν : Measure Y) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    {D : Set (X×Y)} (hD : MeasurableSet D) :
    (μ.prod ν).real D=∫ x,ν.real ((Prod.mk x) ⁻¹' D) ∂μ := by
  rw [Measure.real,Measure.prod_apply hD]
  exact (integral_toReal (measurable_measure_prodMk_left hD).aemeasurable
    (Filter.Eventually.of_forall (fun _ => measure_lt_top ν _))).symm

lemma integrable_real_section (μ : Measure X) (ν : Measure Y) [IsFiniteMeasure μ] [IsProbabilityMeasure ν]
    {D : Set (X×Y)} (hD : MeasurableSet D) :
    Integrable (fun x => ν.real ((Prod.mk x) ⁻¹' D)) μ := by
  apply (integrable_const (1 : ℝ)).mono'
    (measurable_measure_prodMk_left hD).ennreal_toReal.aestronglyMeasurable
  exact Filter.Eventually.of_forall (fun x => by
    rw [Real.norm_eq_abs,abs_of_nonneg ENNReal.toReal_nonneg]
    exact measureReal_le_one)

lemma LawClose.prod_same_left (μ : Measure X) [IsProbabilityMeasure μ]
    {ν η : Measure Y} [IsProbabilityMeasure ν] [IsProbabilityMeasure η]
    {ε : ℝ} (h : LawClose ν η ε) : LawClose (μ.prod ν) (μ.prod η) ε := by
  intro D hD
  rw [real_prod_apply μ ν hD,real_prod_apply μ η hD,
    ←integral_sub (integrable_real_section μ ν hD) (integrable_real_section μ η hD)]
  calc
    _≤∫ x,|ν.real ((Prod.mk x) ⁻¹' D)-η.real ((Prod.mk x) ⁻¹' D)| ∂μ := by
      simpa only [Real.norm_eq_abs] using (norm_integral_le_integral_norm
        (fun x => ν.real ((Prod.mk x) ⁻¹' D)-η.real ((Prod.mk x) ⁻¹' D)))
    _≤∫ _x : X,ε ∂μ := integral_mono_ae
      ((integrable_real_section μ ν hD).sub (integrable_real_section μ η hD)).abs
      (integrable_const ε) (Filter.Eventually.of_forall (fun x => h _ (hD.preimage measurable_prodMk_left)))
    _=ε := by simp

lemma LawClose.prod_same_right {μ ν : Measure X} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {ε : ℝ} (h : LawClose μ ν ε) (η : Measure Y) [IsProbabilityMeasure η] :
    LawClose (μ.prod η) (ν.prod η) ε := by
  simpa only [Measure.prod_swap] using (h.prod_same_left η).map measurable_swap

lemma LawClose.prod {μ ν : Measure X} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {η κ : Measure Y} [IsProbabilityMeasure η] [IsProbabilityMeasure κ]
    {ε δ : ℝ} (h : LawClose μ ν ε) (h' : LawClose η κ δ) :
    LawClose (μ.prod η) (ν.prod κ) (ε+δ) :=
  (h.prod_same_right η).triangle (h'.prod_same_left ν)

end HyperbolicCoding

end
section
namespace HyperbolicCoding
open Set Filter
open scoped Topology
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]

theorem decreasing_projection_limit (K : ℕ → Submodule ℝ V)
    [∀ n,(K n).HasOrthogonalProjection]
    (hK : Antitone K) (hclosed : ∀ n,IsClosed (K n : Set V)) (f : V) :
    ∃ g : V,(∀ n,g∈K n) ∧ Tendsto (fun n => (K n).starProjection f) atTop (𝓝 g) := by
  let p (n : ℕ) : V := (K n).starProjection f
  have hid {n m : ℕ} (hnm : n ≤ m) :
      ‖p n-p m‖^2=‖p n‖^2-‖p m‖^2 := by
    have hcomp : (K m).starProjection (p n)=p m := by
      exact congrArg (fun L : V →L[ℝ] V => L f) (Submodule.starProjection_comp_starProjection_of_le (hK hnm))
    have ho := Submodule.starProjection_inner_eq_zero (K := K m) (p n) (p m)
      ((K m).starProjection_apply_mem f)
    rw [hcomp,inner_sub_left,real_inner_self_eq_norm_sq] at ho
    rw [norm_sub_sq_real]
    linarith
  have hanti : Antitone (fun n => ‖p n‖^2) := by
    intro n m hnm
    have hh := hid hnm
    nlinarith [sq_nonneg ‖p n-p m‖]
  have ht := tendsto_atTop_ciInf hanti (show BddBelow (range (fun n => ‖p n‖^2)) from
    ⟨0,by rintro _ ⟨n,rfl⟩; exact sq_nonneg _⟩)
  have hc : CauchySeq p := by
    apply Metric.cauchySeq_iff'.mpr
    intro ε hε
    obtain ⟨N,hN⟩ := Metric.cauchySeq_iff'.mp ht.cauchySeq (ε^2) (sq_pos_of_pos hε)
    refine ⟨N,?_⟩
    intro n hn
    have hn' := hN n hn
    rw [Real.dist_eq] at hn'
    have hab := (abs_sub_comm (‖p n‖^2) (‖p N‖^2)) ▸ hn'
    have hdiff : ‖p N-p n‖^2<ε^2 := by
      rw [hid hn]
      exact lt_of_le_of_lt (le_abs_self _) hab
    rw [dist_comm,dist_eq_norm]
    nlinarith [norm_nonneg (p N-p n)]
  obtain ⟨g,hg⟩ := cauchySeq_tendsto_of_complete hc
  refine ⟨g,?_,hg⟩
  intro n
  exact (hclosed n).mem_of_tendsto hg ((eventually_ge_atTop n).mono (fun m hnm => hK hnm ((K m).starProjection_apply_mem f)))

end HyperbolicCoding

end
end

end OAI
end

section
-- module Solutions.OAIQ44_CM.StandardMap_Bernoulli_ReverseTailProjection
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace HyperbolicCoding
open MeasureTheory MeasureTheory.Measure Set Filter
open scoped ENNReal Topology
variable {X A : Type*} [MeasurableSpace X] [MeasurableSpace A]

omit [MeasurableSpace X] in
lemma tailSigma_antitone (T : X → X) (α : X → A) : Antitone (tailSigma T α) := by
  intro n m hnm E hE
  obtain ⟨D,hD,rfl⟩ := hE
  let S (v : ℕ → A) (j : ℕ) := v (j+m-n)
  have hS : Measurable S := Measurable.of_eval (fun j => measurable_pi_apply (j+m-n))
  refine ⟨S ⁻¹' D,hD.preimage hS,?_⟩
  ext x
  change (S (tailName T α n x)∈D) ↔ (tailName T α m x∈D)
  have hh : S (tailName T α n x)=tailName T α m x := by
    funext j
    simp only [S,tailName]
    congr 2
    omega
  rw [hh]

lemma tailEvent_of_aestronglyMeasurable (μ : Measure X) (T : X → X) (α : X → A)
    {f : X → ℝ} (hf : ∀ n,AEStronglyMeasurable[tailSigma T α n] f μ) (r : ℝ) :
    TailEvent μ T α {x | f x < r} := by
  intro n
  have hset := (hf n).measurable_mk (measurableSet_Iio (a := r))
  obtain ⟨D,hD,hpre⟩ := hset
  refine ⟨D,hD,?_⟩
  filter_upwards [(hf n).ae_eq_mk] with x hx
  change (f x < r)=(tailName T α n x∈D)
  have hh : (tailName T α n x∈D) ↔ (hf n).mk f x < r := by
    change (x∈tailName T α n ⁻¹' D) ↔ (x∈(hf n).mk f ⁻¹' Iio r)
    rw [hpre]
  exact propext (by rw [hx]; exact hh.symm)

lemma ae_constant_of_trivial_thresholds (μ : Measure X) [IsProbabilityMeasure μ]
    (f : X → ℝ) (hf : ∀ r : ℚ,(∀ᵐ x ∂μ,f x<(r : ℝ)) ∨ (∀ᵐ x ∂μ,¬f x<(r : ℝ))) :
    ∃ c : ℝ,f=ᵐ[μ](fun _ => c) := by
  have hr (r : ℚ) : ∃ b : Prop,∀ᵐ x ∂μ,(f x<(r : ℝ) ↔ b) := by
    rcases hf r with h|h
    · exact ⟨True,h.mono (fun _ hx => by simp only [hx])⟩
    · exact ⟨False,h.mono (fun _ hx => by simp only [hx])⟩
  choose b hb using hr
  have hall := ae_all_iff.mpr hb
  obtain ⟨x₀,hx₀⟩ := hall.exists
  refine ⟨f x₀,hall.mono ?_⟩
  intro x hx
  exact eq_of_forall_lt_rat_iff_lt (fun r => (hx r).trans (hx₀ r).symm)

theorem tail_condExpL2_limit (μ : Measure X) {T : X → X} {α : X → A}
    (hT : Measurable T) (hα : Measurable α) (f : Lp ℝ 2 μ) :
    ∃ g : Lp ℝ 2 μ,(∀ n,AEStronglyMeasurable[tailSigma T α n] g μ) ∧
      Tendsto (fun n => (condExpL2 ℝ ℝ (tailSigma_le hT hα n) f : Lp ℝ 2 μ)) atTop (𝓝 g) := by
  let K (n : ℕ) := lpMeas ℝ ℝ (tailSigma T α n) 2 μ
  let (n : ℕ) : Fact (tailSigma T α n ≤ (inferInstance : MeasurableSpace X)) := ⟨tailSigma_le hT hα n⟩
  have (n : ℕ) : (K n).HasOrthogonalProjection := by dsimp only [K]; infer_instance
  have hK : Antitone K := by
    intro n m hnm f hf
    exact mem_lpMeas_iff_aestronglyMeasurable.mpr
      (AEStronglyMeasurable.mono (tailSigma_antitone T α hnm) (mem_lpMeas_iff_aestronglyMeasurable.mp hf))
  have hc (n : ℕ) : IsClosed (K n : Set (Lp ℝ 2 μ)) := isClosed_aestronglyMeasurable (tailSigma_le hT hα n)
  obtain ⟨g,hg,ht⟩ := decreasing_projection_limit K hK hc f
  refine ⟨g,fun n => mem_lpMeas_iff_aestronglyMeasurable.mp (hg n),?_⟩
  exact ht

theorem tail_condExpL2_constant_limit (μ : Measure X) [IsProbabilityMeasure μ]
    {T : X → X} {α : X → A} (hT : Measurable T) (hα : Measurable α)
    (htriv : ∀ E,TailEvent μ T α E → (∀ᵐ x ∂μ,x∈E) ∨ (∀ᵐ x ∂μ,x∉E))
    (f : Lp ℝ 2 μ) :
    ∃ (g : Lp ℝ 2 μ) (c : ℝ),g=ᵐ[μ](fun _ => c) ∧
      Tendsto (fun n => (condExpL2 ℝ ℝ (tailSigma_le hT hα n) f : Lp ℝ 2 μ)) atTop (𝓝 g) := by
  obtain ⟨g,hg,ht⟩ := tail_condExpL2_limit μ hT hα f
  obtain ⟨c,hc⟩ := ae_constant_of_trivial_thresholds μ g (fun r =>
    htriv _ (tailEvent_of_aestronglyMeasurable μ T α hg r))
  exact ⟨g,c,hc,ht⟩

end HyperbolicCoding

end
section
namespace HyperbolicCoding
open MeasureTheory MeasureTheory.Measure Set Filter
open scoped ENNReal Topology
variable {X A : Type*} [MeasurableSpace X] [MeasurableSpace A]

lemma constL2_ae (μ : Measure X) [IsFiniteMeasure μ] (c : ℝ) :
    constL2 μ c=ᵐ[μ](fun _ : X => c) := by
  simpa only [constL2,indicator_univ] using
    (indicatorConstLp_coeFn (p := 2) (hs := MeasurableSet.univ) (hμs := measure_ne_top μ univ) (c := c))

lemma inner_constL2_one (μ : Measure X) [IsFiniteMeasure μ] (f : Lp ℝ 2 μ) :
    inner ℝ (constL2 μ 1) f=∫ x,f x ∂μ := by
  simpa only [constL2,setIntegral_univ] using (L2.inner_indicatorConstLp_one MeasurableSet.univ (measure_ne_top μ univ) f)

theorem tail_condExpL2_mean_limit (μ : Measure X) [IsProbabilityMeasure μ]
    {T : X → X} {α : X → A} (hT : Measurable T) (hα : Measurable α)
    (htriv : ∀ E,TailEvent μ T α E → (∀ᵐ x ∂μ,x∈E) ∨ (∀ᵐ x ∂μ,x∉E))
    (f : Lp ℝ 2 μ) :
    Tendsto (fun n => (condExpL2 ℝ ℝ (tailSigma_le hT hα n) f : Lp ℝ 2 μ))
      atTop (𝓝 (constL2 μ (∫ x,f x ∂μ))) := by
  obtain ⟨g,c,hc,ht⟩ := tail_condExpL2_constant_limit μ hT hα htriv f
  have hi (n : ℕ) : inner ℝ (constL2 μ 1) (condExpL2 ℝ ℝ (tailSigma_le hT hα n) f : Lp ℝ 2 μ)=∫ x,f x ∂μ := by
    rw [inner_constL2_one]
    simpa only [setIntegral_univ] using
      (integral_condExpL2_eq_of_fin_meas_real (hm := tailSigma_le hT hα n) f MeasurableSet.univ (measure_ne_top μ univ))
  have hl : inner ℝ (constL2 μ 1) g=∫ x,f x ∂μ :=
    tendsto_nhds_unique (tendsto_const_nhds.inner ht) (by simpa only [hi] using tendsto_const_nhds)
  have hcg : inner ℝ (constL2 μ 1) g=c := by
    rw [inner_constL2_one,integral_congr_ae hc]
    simp
  have hmean : c=∫ x,f x ∂μ := hcg.symm.trans hl
  have heq : g=constL2 μ (∫ x,f x ∂μ) :=
    Lp.ext (hc.trans (by simpa only [hmean] using (constL2_ae μ c).symm))
  rwa [heq] at ht

lemma norm_indicatorConstLp_one_le (μ : Measure X) [IsProbabilityMeasure μ]
    {C : Set X} (hC : MeasurableSet C) :
    ‖indicatorConstLp 2 hC (measure_ne_top μ C) (1 : ℝ)‖ ≤ 1 := by
  rw [norm_indicatorConstLp (by norm_num) (by norm_num),norm_one,one_mul]
  exact Real.rpow_le_one (measureReal_nonneg) measureReal_le_one (by positivity)

lemma tail_covariance_projection_bound (μ : Measure X) [IsProbabilityMeasure μ]
    {T : X → X} {α : X → A} (hT : Measurable T) (hα : Measurable α)
    (f : Lp ℝ 2 μ) (n : ℕ) {C : Set X} (hC : MeasurableSet[tailSigma T α n] C) :
    |(∫ x in C,f x ∂μ)-μ.real C*(∫ x,f x ∂μ)| ≤
      ‖(condExpL2 ℝ ℝ (tailSigma_le hT hα n) f : Lp ℝ 2 μ)-constL2 μ (∫ x,f x ∂μ)‖ := by
  let hm := tailSigma_le hT hα n
  let v : Lp ℝ 2 μ := indicatorConstLp 2 (hm C hC) (measure_ne_top μ C) 1
  let p : Lp ℝ 2 μ := condExpL2 ℝ ℝ hm f
  let c : Lp ℝ 2 μ := constL2 μ (∫ x,f x ∂μ)
  have hv : AEStronglyMeasurable[tailSigma T α n] v μ :=
    mem_lpMeas_iff_aestronglyMeasurable.mp (mem_lpMeas_indicatorConstLp (𝕜 := ℝ) hm hC (measure_ne_top μ C))
  have hp : inner ℝ v p=inner ℝ v f := by
    rw [real_inner_comm p v,real_inner_comm f v]
    exact inner_condExpL2_eq_inner_fun hm f v hv
  have hvf : inner ℝ v f=∫ x in C,f x ∂μ := L2.inner_indicatorConstLp_one _ _ f
  have hvc : inner ℝ v c=μ.real C*(∫ x,f x ∂μ) := by
    rw [show inner ℝ v c=∫ x in C,c x ∂μ from L2.inner_indicatorConstLp_one _ _ c]
    rw [integral_congr_ae (ae_restrict_of_ae (constL2_ae μ (∫ x,f x ∂μ)))]
    simp only [integral_const,Measure.restrict_apply_univ,smul_eq_mul,Measure.real]
  have he : (∫ x in C,f x ∂μ)-μ.real C*(∫ x,f x ∂μ)=inner ℝ v (p-c) := by
    rw [inner_sub_right,hp,hvf,hvc]
  rw [he]
  exact (abs_real_inner_le_norm v (p-c)).trans
    (mul_le_of_le_one_left (norm_nonneg _) (norm_indicatorConstLp_one_le μ (hm C hC)))

theorem uniform_tail_covariance_small (μ : Measure X) [IsProbabilityMeasure μ]
    {T : X → X} {α : X → A} (hT : Measurable T) (hα : Measurable α)
    (htriv : ∀ E,TailEvent μ T α E → (∀ᵐ x ∂μ,x∈E) ∨ (∀ᵐ x ∂μ,x∉E))
    (f : Lp ℝ 2 μ) {ε : ℝ} (hε : 0<ε) :
    ∀ᶠ n : ℕ in atTop,∀ C : Set X,MeasurableSet[tailSigma T α n] C →
      |(∫ x in C,f x ∂μ)-μ.real C*(∫ x,f x ∂μ)|<ε := by
  have ht := ((tail_condExpL2_mean_limit μ hT hα htriv f).sub_const (constL2 μ (∫ x,f x ∂μ))).norm
  simp only [sub_self,norm_zero] at ht
  filter_upwards [ht.eventually (gt_mem_nhds hε)] with n hn C hC
  exact (tail_covariance_projection_bound μ hT hα f n hC).trans_lt hn

end HyperbolicCoding

end
section
namespace HyperbolicCoding
open MeasureTheory MeasureTheory.Measure Set Filter
open scoped ENNReal Topology
variable {X A : Type*} [MeasurableSpace X] [MeasurableSpace A]

lemma abs_setIntegral_le_L1 (μ : Measure X) {f : X → ℝ} (hf : Integrable f μ) (C : Set X) :
    |∫ x in C,f x ∂μ| ≤ ∫ x,|f x| ∂μ := by
  exact (norm_integral_le_integral_norm _).trans
    (setIntegral_le_integral hf.norm (Filter.Eventually.of_forall (fun _ => norm_nonneg _)))

theorem uniform_tail_covariance_small_L1 (μ : Measure X) [IsProbabilityMeasure μ]
    {T : X → X} {α : X → A} (hT : Measurable T) (hα : Measurable α)
    (htriv : ∀ E,TailEvent μ T α E → (∀ᵐ x ∂μ,x∈E) ∨ (∀ᵐ x ∂μ,x∉E))
    {f : X → ℝ} (hf : Integrable f μ) {ε : ℝ} (hε : 0<ε) :
    ∀ᶠ n : ℕ in atTop,∀ C : Set X,MeasurableSet[tailSigma T α n] C →
      |(∫ x in C,f x ∂μ)-μ.real C*(∫ x,f x ∂μ)|<ε := by
  obtain ⟨g,hg,hgm⟩ := (memLp_one_iff_integrable.mpr hf).exists_simpleFunc_eLpNorm_sub_lt
    (by simp : (1 : ℝ≥0∞)≠⊤) (ne_of_gt (ENNReal.ofReal_pos.mpr (by linarith : 0<ε/4)))
  have hg2 : MemLp g 2 μ := SimpleFunc.memLp_of_finite_measure_preimage 2
    (fun y _ => measure_lt_top μ (g ⁻¹' {y}))
  have gi : Integrable g μ := memLp_one_iff_integrable.mp hgm
  have hi : ∫ x,|f x-g x| ∂μ<ε/4 := by
    simp_rw [← Real.norm_eq_abs]
    change (∫ x,‖(f-⇑g) x‖ ∂μ)<ε/4
    rw [integral_norm_eq_lintegral_enorm (hf.sub gi).aestronglyMeasurable]
    rw [eLpNorm_one_eq_lintegral_enorm] at hg
    exact ENNReal.toReal_lt_of_lt_ofReal hg
  have ht := uniform_tail_covariance_small μ hT hα htriv (hg2.toLp g) (by linarith : 0<ε/2)
  filter_upwards [ht] with n hn C hC
  have hgc := hg2.coeFn_toLp
  have hgn := hn C hC
  rw [integral_congr_ae (ae_restrict_of_ae hgc),integral_congr_ae hgc] at hgn
  have hdiff : |(∫ x in C,f x ∂μ)-(∫ x in C,g x ∂μ)|≤∫ x,|f x-g x| ∂μ := by
    rw [← integral_sub hf.integrableOn gi.integrableOn]
    exact abs_setIntegral_le_L1 μ (hf.sub gi) C
  have hmean : |(∫ x,f x ∂μ)-(∫ x,g x ∂μ)|≤∫ x,|f x-g x| ∂μ := by
    rw [←integral_sub hf gi]
    simpa only [Real.norm_eq_abs] using (norm_integral_le_integral_norm (fun x => f x-g x))
  have hmul : |μ.real C*((∫ x,f x ∂μ)-(∫ x,g x ∂μ))|≤∫ x,|f x-g x| ∂μ := by
    rw [abs_mul,abs_of_nonneg measureReal_nonneg]
    exact (mul_le_of_le_one_left (abs_nonneg _) measureReal_le_one).trans hmean
  have htri := abs_add_le ((∫ x in C,f x ∂μ)-(∫ x in C,g x ∂μ))
    (((∫ x in C,g x ∂μ)-μ.real C*(∫ x,g x ∂μ))-μ.real C*((∫ x,f x ∂μ)-(∫ x,g x ∂μ)))
  have htri' := abs_sub_le ((∫ x in C,g x ∂μ)-μ.real C*(∫ x,g x ∂μ)) 0
    (μ.real C*((∫ x,f x ∂μ)-(∫ x,g x ∂μ)))
  simp only [sub_zero,zero_sub,abs_neg] at htri'
  have heq : (∫ x in C,f x ∂μ)-μ.real C*(∫ x,f x ∂μ)=
      ((∫ x in C,f x ∂μ)-(∫ x in C,g x ∂μ))+
      (((∫ x in C,g x ∂μ)-μ.real C*(∫ x,g x ∂μ))-μ.real C*((∫ x,f x ∂μ)-(∫ x,g x ∂μ))) := by ring
  rw [heq]
  linarith

theorem ac_remote_tail_law (μ η : Measure X) [IsProbabilityMeasure μ] [IsProbabilityMeasure η]
    (hac : η≪μ) {T : X → X} {α : X → A} (hT : Measurable T) (hα : Measurable α)
    (htriv : ∀ E,TailEvent μ T α E → (∀ᵐ x ∂μ,x∈E) ∨ (∀ᵐ x ∂μ,x∉E))
    {ε : ℝ} (hε : 0<ε) :
    ∀ᶠ n : ℕ in atTop,∀ D : Set (ℕ → A),MeasurableSet D →
      |(η.map (tailName T α n)).real D-(μ.map (tailName T α n)).real D|<ε := by
  let f : X → ℝ := fun x => (η.rnDeriv μ x).toReal
  have hf : Integrable f μ := by
    simpa only [mul_one] using (integrable_toReal_rnDeriv_mul_iff (f := fun _ => (1 : ℝ)) hac).mpr (integrable_const 1)
  have hmean : ∫ x,f x ∂μ=1 := by
    simpa [f,Measure.real] using
      (integral_toReal_rnDeriv_mul (f := fun _ => (1 : ℝ)) hac)
  filter_upwards [uniform_tail_covariance_small_L1 μ hT hα htriv hf hε] with n hn D hD
  have hC : MeasurableSet[tailSigma T α n] (tailName T α n ⁻¹' D) := ⟨D,hD,rfl⟩
  have hi : ∫ x in tailName T α n ⁻¹' D,f x ∂μ=η.real (tailName T α n ⁻¹' D) := by
    simpa only [mul_one,integral_const,Measure.restrict_apply_univ,smul_eq_mul,mul_one,Measure.real] using
      (setIntegral_toReal_rnDeriv_mul (f := fun _ => (1 : ℝ)) hac ((measurable_tailName hT hα n) hD))
  have hh := hn _ hC
  rw [hmean,mul_one,hi] at hh
  simpa only [Measure.real,Measure.map_apply (measurable_tailName hT hα n) hD] using hh

end HyperbolicCoding

end
section
namespace HyperbolicCoding
open MeasureTheory MeasureTheory.Measure Set Filter
open scoped ENNReal Topology
variable {X A : Type*} [MeasurableSpace X] [MeasurableSpace A]

lemma LawClose.mono {μ ν : Measure X} {ε δ : ℝ} (h : LawClose μ ν ε) (hεδ : ε≤δ) :
    LawClose μ ν δ := fun D hD => (h D hD).trans hεδ

lemma measurable_remotePair {T S : X → X} {α : X → A}
    (hT : Measurable T) (hS : Measurable S) (hα : Measurable α) (n : ℕ) :
    Measurable (remotePair T S α n) :=
  (measurable_tailName hS hα n).prodMk (measurable_tailName hT hα n)

lemma stationary_tail_law (μ : Measure X) {T : X → X} (hT : MeasurePreserving T μ μ)
    {α : X → A} (hα : Measurable α) (n : ℕ) :
    μ.map (tailName T α n)=μ.map (tailName T α 0) := by
  have heq : tailName T α n=(tailName T α 0) ∘ T^[n] := by
    funext x i
    simp only [tailName,Function.comp_apply,Nat.add_zero,←Function.iterate_add_apply]
  rw [heq,←Measure.map_map (measurable_tailName hT.measurable hα 0) (hT.measurable.iterate n),
    (hT.iterate n).map_eq]

lemma ac_stationary_tail_law (μ η : Measure X) [IsProbabilityMeasure μ] [IsProbabilityMeasure η]
    (hac : η≪μ) {T : X → X} (hT : MeasurePreserving T μ μ) {α : X → A} (hα : Measurable α)
    (htriv : ∀ E,TailEvent μ T α E → (∀ᵐ x ∂μ,x∈E) ∨ (∀ᵐ x ∂μ,x∉E))
    {ε : ℝ} (hε : 0<ε) : ∀ᶠ n : ℕ in atTop,
      LawClose (η.map (tailName T α n)) (μ.map (tailName T α 0)) ε := by
  filter_upwards [ac_remote_tail_law μ η hac hT.measurable hα htriv hε] with n hn D hD
  rw [←stationary_tail_law μ hT hα n]
  exact (hn D hD).le

lemma tail_trivial_symm (μ : Measure X) [IsProbabilityMeasure μ]
    (e : X ≃ᵐ X) (he : MeasurePreserving e μ μ)
    [Fintype A] [MeasurableSingletonClass A] {α : X → A} (hα : Measurable α)
    (htriv : ∀ E,TailEvent μ e α E → (∀ᵐ x ∂μ,x∈E) ∨ (∀ᵐ x ∂μ,x∉E)) :
    ∀ E,TailEvent μ e.symm α E → (∀ᵐ x ∂μ,x∈E) ∨ (∀ᵐ x ∂μ,x∉E) := by
  intro E hE
  exact htriv E (hE.reverse e.symm (he.symm e) hα)

lemma measurable_dropName (k : ℕ) : Measurable (dropName (A := A) k) :=
  Measurable.of_eval (fun i => measurable_pi_apply (i+k))

lemma stationary_drop_law (μ : Measure X) {T : X → X} (hT : MeasurePreserving T μ μ)
    {α : X → A} (hα : Measurable α) (k : ℕ) :
    (μ.map (tailName T α 0)).map (dropName k)=μ.map (tailName T α 0) := by
  rw [Measure.map_map (measurable_dropName k) (measurable_tailName hT.measurable hα 0)]
  have hcomp : dropName k ∘ tailName T α 0=tailName T α k := by
    funext x i
    simp only [dropName,Function.comp_apply,tailName,Nat.add_zero]
  rw [hcomp,stationary_tail_law μ hT hα k]

end HyperbolicCoding

end
section
namespace HyperbolicCoding
open MeasureTheory MeasureTheory.Measure Set Filter
open scoped ENNReal Topology

lemma measurePreserving_exchange_first {A B : Type*} [MeasurableSpace A] [MeasurableSpace B]
    (ν : Measure A) (η : Measure B) [IsProbabilityMeasure ν] [IsProbabilityMeasure η] :
    MeasurePreserving (fun w : (A×B)×(A×B) => ((w.2.1,w.1.2),(w.1.1,w.2.2)))
      ((ν.prod η).prod (ν.prod η)) ((ν.prod η).prod (ν.prod η)) := by
  have ht : MeasurePreserving (fun w : (A×B)×A => ((w.2,w.1.2),w.1.1))
      ((ν.prod η).prod ν) ((ν.prod η).prod ν) :=
    ((measurePreserving_prodAssoc ν η ν).symm MeasurableEquiv.prodAssoc).comp
      (((MeasurePreserving.id ν).prod (measurePreserving_swap (μ := ν) (ν := η))).comp
        (measurePreserving_swap (μ := ν.prod η) (ν := ν)))
  exact (measurePreserving_prodAssoc (ν.prod η) ν η).comp
    ((ht.prod (MeasurePreserving.id η)).comp
      ((measurePreserving_prodAssoc (ν.prod η) ν η).symm MeasurableEquiv.prodAssoc))

theorem product_remote_two_tail_independence {A B X C : Type*}
    [MeasurableSpace A] [MeasurableSpace B] [MeasurableSpace X]
    [MeasurableSpace C] [MeasurableEq C]
    (ν : Measure A) (η : Measure B) [IsProbabilityMeasure ν] [IsProbabilityMeasure η]
    {π : A×B → X} (hπ : Measurable π) {T S : X → X} (hT : Measurable T) (hS : Measurable S)
    {α : X → C} (hα : Measurable α)
    (hpast : ∀ᵐ w : (A×B)×(A×B) ∂(ν.prod η).prod (ν.prod η),∀ᶠ n : ℕ in atTop,
      α (S^[n] (π w.1))=α (S^[n] (π (w.2.1,w.1.2))))
    (hfuture : ∀ᵐ w : (A×B)×(A×B) ∂(ν.prod η).prod (ν.prod η),∀ᶠ n : ℕ in atTop,
      α (T^[n] (π w.1))=α (T^[n] (π (w.1.1,w.2.2)))) :
    ∃ δ : ℕ → ℝ,Tendsto δ atTop (𝓝 0) ∧ (∀ n,0≤δ n) ∧ ∀ n : ℕ,
      LawClose ((ν.prod η).map (fun p => (tailName S α n (π p),tailName T α n (π p))))
        (((ν.prod η).map (fun p => tailName S α n (π p))).prod
          ((ν.prod η).map (fun p => tailName T α n (π p)))) (δ n) := by
  let κ := (ν.prod η).prod (ν.prod η)
  let p : (A×B)×(A×B) → X := fun w => π w.1
  let q : (A×B)×(A×B) → X := fun w => π (w.2.1,w.1.2)
  let r : (A×B)×(A×B) → X := fun w => π (w.1.1,w.2.2)
  have hp : Measurable p := hπ.comp measurable_fst
  have hq : Measurable q := hπ.comp ((measurable_fst.comp measurable_snd).prodMk (measurable_snd.comp measurable_fst))
  have hr : Measurable r := hπ.comp ((measurable_fst.comp measurable_fst).prodMk (measurable_snd.comp measurable_snd))
  let Ds n := {w | tailName S α n (p w)≠tailName S α n (q w)}
  let Dt n := {w | tailName T α n (p w)≠tailName T α n (r w)}
  let δ n := κ.real (Ds n)+κ.real (Dt n)
  have hds := tail_disagreement_tendsto_zero κ hS hα hp hq hpast
  have hdt := tail_disagreement_tendsto_zero κ hT hα hp hr hfuture
  refine ⟨δ,by simpa only [add_zero] using hds.add hdt,fun _ => add_nonneg measureReal_nonneg measureReal_nonneg,?_⟩
  intro n D hD
  let s : A×B → (ℕ → C) := fun w => tailName S α n (π w)
  let t : A×B → (ℕ → C) := fun w => tailName T α n (π w)
  have hs : Measurable s := (measurable_tailName hS hα n).comp hπ
  have ht : Measurable t := (measurable_tailName hT hα n).comp hπ
  let P : (A×B)×(A×B) → (ℕ → C)×(ℕ → C) := fun w => (s w.1,t w.1)
  let Q : (A×B)×(A×B) → (ℕ → C)×(ℕ → C) := fun w => (s (w.2.1,w.1.2),t (w.1.1,w.2.2))
  have hP : Measurable P := (hs.prodMk ht).comp measurable_fst
  have harr := measurePreserving_exchange_first ν η
  have hQ : Measurable Q := (hs.prodMap ht).comp harr.measurable
  have hmapP : κ.map P=(ν.prod η).map (fun w => (s w,t w)) := by
    have hfst : MeasurePreserving (Prod.fst : (A×B)×(A×B) → A×B) κ (ν.prod η) := measurePreserving_fst
    rw [←hfst.map_eq,Measure.map_map (hs.prodMk ht) measurable_fst]
    rfl
  have hmapQ : κ.map Q=((ν.prod η).map s).prod ((ν.prod η).map t) := by
    calc
      κ.map Q=κ.map (Prod.map s t) := by
        change κ.map (Prod.map s t ∘ (fun w : (A×B)×(A×B) => ((w.2.1,w.1.2),(w.1.1,w.2.2))))=_
        rw [←Measure.map_map (hs.prodMap ht) harr.measurable,harr.map_eq]
      _=_ := (Measure.map_prod_map (ν.prod η) (ν.prod η) hs ht).symm
  have h := law_distance_le_disagreement κ hP hQ hD
  rw [hmapP,hmapQ] at h
  apply h.trans
  calc
    κ.real {w | P w≠Q w}≤κ.real (Ds n∪Dt n) := measureReal_mono (by
      intro w hw
      change (tailName S α n (p w)≠tailName S α n (q w)) ∨ (tailName T α n (p w)≠tailName T α n (r w))
      simpa only [mem_ofPred_eq,P,Q,s,t,p,q,r,ne_eq,Prod.mk.injEq,not_and_or] using hw)
    _≤δ n := measureReal_union_le _ _

end HyperbolicCoding

end
section
namespace HyperbolicCoding
open MeasureTheory MeasureTheory.Measure Set Filter
open scoped ENNReal Topology

theorem local_remote_independent {A B X C : Type*}
    [MeasurableSpace A] [MeasurableSpace B] [MeasurableSpace X]
    [MeasurableSpace C] [MeasurableEq C]
    (ν : Measure A) (η : Measure B) (μ : Measure X)
    [IsProbabilityMeasure ν] [IsProbabilityMeasure η] [IsProbabilityMeasure μ]
    {π : A×B → X} (hπ : QuasiMeasurePreserving π (ν.prod η) μ)
    {T S : X → X} (hT : MeasurePreserving T μ μ) (hS : MeasurePreserving S μ μ)
    {α : X → C} (hα : Measurable α)
    (htrivT : ∀ E,TailEvent μ T α E → (∀ᵐ x ∂μ,x∈E) ∨ (∀ᵐ x ∂μ,x∉E))
    (htrivS : ∀ E,TailEvent μ S α E → (∀ᵐ x ∂μ,x∈E) ∨ (∀ᵐ x ∂μ,x∉E))
    (hpast : ∀ᵐ w : (A×B)×(A×B) ∂(ν.prod η).prod (ν.prod η),∀ᶠ n : ℕ in atTop,
      α (S^[n] (π w.1))=α (S^[n] (π (w.2.1,w.1.2))))
    (hfuture : ∀ᵐ w : (A×B)×(A×B) ∂(ν.prod η).prod (ν.prod η),∀ᶠ n : ℕ in atTop,
      α (T^[n] (π w.1))=α (T^[n] (π (w.1.1,w.2.2)))) :
    RemoteIndependent μ ((ν.prod η).map π) T S α := by
  obtain ⟨δ,hd,hδ,hclose⟩ := product_remote_two_tail_independence ν η hπ.measurable hT.measurable hS.measurable hα hpast hfuture
  let ζ := (ν.prod η).map π
  have : IsProbabilityMeasure ζ := by first | infer_instance | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | (apply Measurable.aemeasurable; measurability) | measurability)
  have (n : ℕ) : IsProbabilityMeasure (ζ.map (tailName S α n)) := Measure.isProbabilityMeasure_map (measurable_tailName hS.measurable hα n).aemeasurable
  have (n : ℕ) : IsProbabilityMeasure (ζ.map (tailName T α n)) := Measure.isProbabilityMeasure_map (measurable_tailName hT.measurable hα n).aemeasurable
  have : IsProbabilityMeasure (μ.map (tailName S α 0)) := Measure.isProbabilityMeasure_map (measurable_tailName hS.measurable hα 0).aemeasurable
  have _hunusedS : True := by first | trivial | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | (apply Measurable.aemeasurable; measurability) | measurability)
  have : IsProbabilityMeasure (μ.map (tailName T α 0)) := Measure.isProbabilityMeasure_map (measurable_tailName hT.measurable hα 0).aemeasurable
  have _hunusedT : True := by first | trivial | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | (apply Measurable.aemeasurable; measurability) | measurability)
  intro ε hε
  have hthird : 0<ε/3 := by linarith
  filter_upwards [hd.eventually (gt_mem_nhds hthird),
    ac_stationary_tail_law μ ζ hπ.absolutelyContinuous hT hα htrivT hthird,
    ac_stationary_tail_law μ ζ hπ.absolutelyContinuous hS hα htrivS hthird] with n hn htn hsn
  have hjoin : LawClose (ζ.map (remotePair T S α n))
      ((ζ.map (tailName S α n)).prod (ζ.map (tailName T α n))) (δ n) := by
    simpa only [ζ,Measure.map_map (measurable_remotePair hT.measurable hS.measurable hα n) hπ.measurable,
      Measure.map_map (measurable_tailName hS.measurable hα n) hπ.measurable,
      Measure.map_map (measurable_tailName hT.measurable hα n) hπ.measurable,Function.comp_def,remotePair]
      using hclose n
  exact ((hjoin.mono hn.le).triangle (hsn.prod htn)).mono (by linarith)

end HyperbolicCoding

end
end

end OAI
end

section
-- module Solutions.OAIQ44_CM.StandardMap_Bernoulli_ErgodicL1
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace HyperbolicCoding
open MeasureTheory MeasureTheory.Measure Set Filter BoundedSubadditive
open scoped ENNReal Topology BigOperators
variable {X : Type*} [MeasurableSpace X] {μ : Measure X} [IsProbabilityMeasure μ]

omit [IsProbabilityMeasure μ] in
lemma orbitAverage_integrable {T : X → X} (hT : MeasurePreserving T μ μ)
    {f : X → ℝ} (hf : Integrable f μ) (n : ℕ) : Integrable (orbitAverage T f n) μ := by
  exact (integrable_finsetSum _ (fun i _ => (hT.iterate i).integrable_comp_of_integrable hf)).div_const _

omit [MeasurableSpace X] in
lemma orbitAverage_sub (T : X → X) (f g : X → ℝ) (n : ℕ) (x : X) :
    orbitAverage T (f-g) n x=orbitAverage T f n x-orbitAverage T g n x := by
  simp only [orbitAverage,birkhoffSum,Pi.sub_apply,Finset.sum_sub_distrib,sub_div]

omit [MeasurableSpace X] in
lemma orbitAverage_abs_le (T : X → X) (f : X → ℝ) (n : ℕ) (x : X) :
    |orbitAverage T f n x|≤orbitAverage T (fun y => |f y|) n x := by
  rw [orbitAverage,abs_div,abs_of_nonneg (Nat.cast_nonneg n : (0 : ℝ)≤n)]
  exact div_le_div_of_nonneg_right (Finset.abs_sum_le_sum_abs _ _) (Nat.cast_nonneg _)

omit [IsProbabilityMeasure μ] in
lemma integral_orbitAverage {T : X → X} (hT : MeasurePreserving T μ μ)
    {f : X → ℝ} (hf : Integrable f μ) {n : ℕ} (hn : 0<n) :
    (∫ x,orbitAverage T f n x ∂μ)=∫ x,f x ∂μ := by
  have him (i : ℕ) : Integrable (fun x => f (T^[i] x)) μ := (hT.iterate i).integrable_comp_of_integrable hf
  simp only [orbitAverage,birkhoffSum]
  rw [integral_div,integral_finsetSum _ (fun i _ => him i)]
  simp only [BoundedSubadditive.integral_comp (hT.iterate _) hf.aestronglyMeasurable,
    Finset.sum_const,Finset.card_range,nsmul_eq_mul]
  exact mul_div_cancel_left₀ _ (by exact_mod_cast hn.ne')

omit [IsProbabilityMeasure μ] in
lemma orbitAverage_L1_contraction {T : X → X} (hT : MeasurePreserving T μ μ)
    {f g : X → ℝ} (hf : Integrable f μ) (hg : Integrable g μ) {n : ℕ} (hn : 0<n) :
    (∫ x,|orbitAverage T f n x-orbitAverage T g n x| ∂μ)≤∫ x,|f x-g x| ∂μ := by
  simp_rw [←orbitAverage_sub]
  calc
    _≤∫ x,orbitAverage T (fun y => |(f-g) y|) n x ∂μ :=
      integral_mono (orbitAverage_integrable hT (hf.sub hg) n).abs
        (orbitAverage_integrable hT (hf.sub hg).abs n) (orbitAverage_abs_le T (f-g) n)
    _=_ := integral_orbitAverage hT (hf.sub hg).abs hn

theorem ergodic_L1_unit {T : X → X} (hT : Ergodic T μ)
    {g : X → ℝ} (hg : Measurable g) (h0 : ∀ x,0≤g x) (h1 : ∀ x,g x≤1) :
    Tendsto (fun n => ∫ x,|orbitAverage T g n x-(∫ y,g y ∂μ)| ∂μ) atTop (𝓝 0) := by
  obtain ⟨G,hGm,hGb,hGT,hGconv,hGint⟩ := exists_bounded_birkhoff_limit hT.toMeasurePreserving hg h0 h1
  obtain ⟨c,hc⟩ := hT.ae_eq_const_of_ae_eq_comp_ae hGm.aestronglyMeasurable
    (Filter.Eventually.of_forall hGT)
  have hmean : c=∫ x,g x ∂μ := by
    have hh := hGint univ MeasurableSet.univ preimage_univ
    rw [setIntegral_univ,setIntegral_univ,integral_congr_ae hc] at hh
    simpa using hh
  have gi : Integrable g μ := (integrable_const (1 : ℝ)).mono' hg.aestronglyMeasurable
    (Filter.Eventually.of_forall (fun x => by rw [Real.norm_eq_abs,abs_of_nonneg (h0 x)]; exact h1 x))
  have hm0 : 0≤∫ x,g x ∂μ := integral_nonneg h0
  have hm1 : (∫ x,g x ∂μ)≤1 := by
    simpa using integral_mono gi (integrable_const (1 : ℝ)) h1
  let f := observationCocycle g hT.toMeasurePreserving.measurable hg h0 h1
  have ha (n : ℕ) (x : X) : 0≤orbitAverage T g n x ∧ orbitAverage T g n x≤1 := f.average_bounds n x
  have hmeas (n : ℕ) : AEStronglyMeasurable (fun x => |orbitAverage T g n x-(∫ y,g y ∂μ)|) μ :=
    ((f.measurable_average n).sub_const _).abs.aestronglyMeasurable
  have ht := tendsto_integral_of_dominated_convergence (fun _ : X => (1 : ℝ)) hmeas
    (integrable_const 1) (fun n => Filter.Eventually.of_forall (fun x => by
      rw [Real.norm_eq_abs,abs_abs,abs_le]
      constructor <;> linarith [(ha n x).1,(ha n x).2])) (by
      filter_upwards [hGconv,hc] with x hx hxc
      have hGx : G x=∫ y,g y ∂μ := hxc.trans hmean
      have h := (hx.sub_const (∫ y,g y ∂μ)).abs
      simpa only [hGx,sub_self,abs_zero,orbitAverage] using h)
  simpa only [integral_zero] using ht

theorem ergodic_L1_bounded {T : X → X} (hT : Ergodic T μ)
    {f : X → ℝ} (hf : Measurable f) {C : ℝ} (hC : 0≤C) (hbound : ∀ x,|f x|≤C) :
    Tendsto (fun n => ∫ x,|orbitAverage T f n x-(∫ y,f y ∂μ)| ∂μ) atTop (𝓝 0) := by
  let d := 2*C+1
  have hd : 0<d := by dsimp [d]; positivity
  let g (x : X) := (f x+C)/d
  have hg : Measurable g := (hf.add_const C).div_const d
  have h0 (x : X) : 0≤g x := div_nonneg (by linarith [(abs_le.mp (hbound x)).1]) hd.le
  have h1 (x : X) : g x≤1 := by
    apply (div_le_one hd).mpr
    dsimp [d]
    linarith [(abs_le.mp (hbound x)).2]
  have fi : Integrable f μ := (integrable_const C).mono' hf.aestronglyMeasurable (Filter.Eventually.of_forall hbound)
  have hmean : (∫ x,g x ∂μ)=((∫ x,f x ∂μ)+C)/d := by
    dsimp [g]
    rw [integral_div,integral_add fi (integrable_const C)]
    simp
  have hav (n : ℕ) (hn : 0<n) (x : X) :
      orbitAverage T f n x-(∫ y,f y ∂μ)=d*(orbitAverage T g n x-(∫ y,g y ∂μ)) := by
    have hn' : (n : ℝ)≠0 := by exact_mod_cast hn.ne'
    have he : birkhoffSum T g n x=(birkhoffSum T f n x+(n : ℝ)*C)/d := by
      simp only [birkhoffSum,g]
      rw [←Finset.sum_div,Finset.sum_add_distrib]
      simp only [Finset.sum_const,Finset.card_range,nsmul_eq_mul]
    rw [orbitAverage,orbitAverage,he,hmean]
    field_simp
    ring
  have ht := (ergodic_L1_unit hT hg h0 h1).const_mul d
  rw [mul_zero] at ht
  apply ht.congr'
  filter_upwards [eventually_gt_atTop 0] with n hn
  simp_rw [hav n hn,abs_mul,abs_of_pos hd,integral_const_mul]

end HyperbolicCoding

end
section
namespace HyperbolicCoding
open MeasureTheory MeasureTheory.Measure Set Filter
open scoped ENNReal Topology BigOperators
variable {X : Type*} [MeasurableSpace X] {μ : Measure X} [IsProbabilityMeasure μ]

lemma ergodic_L1_error_bound {T : X → X} (hT : MeasurePreserving T μ μ)
    {f g : X → ℝ} (hf : Integrable f μ) (hg : Integrable g μ) {n : ℕ} (hn : 0<n) :
    (∫ x,|orbitAverage T f n x-(∫ y,f y ∂μ)| ∂μ)≤
      (∫ x,|f x-g x| ∂μ)+(∫ x,|orbitAverage T g n x-(∫ y,g y ∂μ)| ∂μ)+
      (∫ x,|f x-g x| ∂μ) := by
  have havf := orbitAverage_integrable hT hf n
  have havg := orbitAverage_integrable hT hg n
  have hi : Integrable (fun x => |orbitAverage T f n x-orbitAverage T g n x|) μ := (havf.sub havg).abs
  have hj : Integrable (fun x => |orbitAverage T g n x-(∫ y,g y ∂μ)|) μ := (havg.sub (integrable_const (∫ y,g y ∂μ))).abs
  have hij : Integrable (fun x => |orbitAverage T f n x-orbitAverage T g n x|+|orbitAverage T g n x-(∫ y,g y ∂μ)|) μ := hi.add hj
  have hc : |(∫ y,g y ∂μ)-(∫ y,f y ∂μ)|≤∫ x,|f x-g x| ∂μ := by
    rw [abs_sub_comm,←integral_sub hf hg]
    simpa only [Real.norm_eq_abs] using (norm_integral_le_integral_norm (fun x => f x-g x))
  calc
    _≤∫ x,|orbitAverage T f n x-orbitAverage T g n x|+
        |orbitAverage T g n x-(∫ y,g y ∂μ)|+|(∫ y,g y ∂μ)-(∫ y,f y ∂μ)| ∂μ := by
      apply integral_mono (havf.sub (integrable_const _)).abs ((hi.add hj).add (integrable_const _))
      intro x
      exact (abs_sub_le _ (∫ y,g y ∂μ) _).trans
        (add_le_add_left (abs_sub_le _ (orbitAverage T g n x) _) _)
    _=(∫ x,|orbitAverage T f n x-orbitAverage T g n x| ∂μ)+
        (∫ x,|orbitAverage T g n x-(∫ y,g y ∂μ)| ∂μ)+|(∫ y,g y ∂μ)-(∫ y,f y ∂μ)| := by
      rw [integral_add hij (integrable_const _),integral_add hi hj]
      simp
    _≤_ := add_le_add (add_le_add_left (orbitAverage_L1_contraction hT hf hg hn) _) hc

theorem ergodic_L1 {T : X → X} (hT : Ergodic T μ) {f : X → ℝ} (hf : Integrable f μ) :
    Tendsto (fun n => ∫ x,|orbitAverage T f n x-(∫ y,f y ∂μ)| ∂μ) atTop (𝓝 0) := by
  classical
  refine tendsto_order.2 ⟨?_,?_⟩
  · intro a ha
    exact Filter.Eventually.of_forall (fun _ => ha.trans_le (integral_nonneg (fun _ => abs_nonneg _)))
  intro ε hε
  obtain ⟨g,hg,hgm⟩ := (memLp_one_iff_integrable.mpr hf).exists_simpleFunc_eLpNorm_sub_lt
    (by simp : (1 : ℝ≥0∞)≠⊤) (ne_of_gt (ENNReal.ofReal_pos.mpr (by linarith : 0<ε/4)))
  have gi : Integrable g μ := memLp_one_iff_integrable.mp hgm
  have hi : ∫ x,|f x-g x| ∂μ<ε/4 := by
    simp_rw [←Real.norm_eq_abs]
    change (∫ x,‖(f-⇑g) x‖ ∂μ)<ε/4
    rw [integral_norm_eq_lintegral_enorm (hf.sub gi).aestronglyMeasurable]
    rw [eLpNorm_one_eq_lintegral_enorm] at hg
    exact ENNReal.toReal_lt_of_lt_ofReal hg
  let C := ∑ y∈g.range,|y|
  have hC : 0≤C := Finset.sum_nonneg (fun _ _ => abs_nonneg _)
  have hb (x : X) : |g x|≤C := Finset.single_le_sum (fun _ _ => abs_nonneg _) (g.mem_range_self x)
  have ht := (ergodic_L1_bounded hT g.measurable hC hb).eventually (gt_mem_nhds (by linarith : 0<ε/2))
  filter_upwards [ht,eventually_gt_atTop 0] with n hn hn0
  have hh := ergodic_L1_error_bound hT.toMeasurePreserving hf gi hn0
  linarith

end HyperbolicCoding

end
section
namespace HyperbolicCoding
open MeasureTheory MeasureTheory.Measure Set Filter
open scoped ENNReal Topology BigOperators
variable {X : Type*} [MeasurableSpace X]

lemma iterateLawMass_density (μ η : Measure X) [IsProbabilityMeasure μ] [IsProbabilityMeasure η]
    (e : X ≃ᵐ X) (he : MeasurePreserving e μ μ) (hac : η≪μ) (i : ℕ)
    {D : Set X} (hD : MeasurableSet D) :
    (η.map (e^[i])).real D=∫ x in D,(η.rnDeriv μ (e.symm^[i] x)).toReal ∂μ := by
  let f : X → ℝ := fun x => (η.rnDeriv μ x).toReal
  have hcomp (x : X) : f (e.symm^[i] (e^[i] x))=f x :=
    congrArg f ((show Function.LeftInverse (e.symm : X → X) e from e.symm_apply_apply).iterate i x)
  have hemb : MeasurableEmbedding (e^[i]) := by
    simpa only [funext (iterateEquiv_apply e i)] using (iterateEquiv e i).measurableEmbedding
  change (η.map (e^[i])).real D=∫ x in D,f (e.symm^[i] x) ∂μ
  rw [Measure.real,Measure.map_apply (e.measurable.iterate i) hD]
  calc
    _=∫ x in (e^[i]) ⁻¹' D,f x ∂μ := (setIntegral_toReal_rnDeriv hac _).symm
    _=∫ x in (e^[i]) ⁻¹' D,f (e.symm^[i] (e^[i] x)) ∂μ := by simp only [hcomp]
    _=_ := (he.iterate i).setIntegral_preimage_emb hemb (fun x => f (e.symm^[i] x)) D

lemma cesaroLawMass_density (μ η : Measure X) [IsProbabilityMeasure μ] [IsProbabilityMeasure η]
    (e : X ≃ᵐ X) (he : MeasurePreserving e μ μ) (hac : η≪μ) (N : ℕ)
    {D : Set X} (hD : MeasurableSet D) :
    cesaroLawMass e η N D=∫ x in D,orbitAverage e.symm (fun y => (η.rnDeriv μ y).toReal) N x ∂μ := by
  let f : X → ℝ := fun x => (η.rnDeriv μ x).toReal
  have hf : Integrable f μ := by
    simpa only [mul_one] using (integrable_toReal_rnDeriv_mul_iff (f := fun _ => (1 : ℝ)) hac).mpr (integrable_const 1)
  have hi (i : ℕ) : Integrable (fun x => f (e.symm^[i] x)) (μ.restrict D) :=
    (((he.symm e).iterate i).integrable_comp_of_integrable hf).integrableOn
  simp only [cesaroLawMass,iterateLawMass_density μ η e he hac _ hD,orbitAverage,birkhoffSum]
  rw [integral_div,integral_finsetSum _ (fun i _ => hi i)]

theorem cesaro_ac_uniform (μ η : Measure X) [IsProbabilityMeasure μ] [IsProbabilityMeasure η]
    (e : X ≃ᵐ X) (he : Ergodic e μ) (hac : η≪μ) {ε : ℝ} (hε : 0<ε) :
    ∀ᶠ N : ℕ in atTop,0<N ∧ ∀ D : Set X,MeasurableSet D →
      |cesaroLawMass e η N D-μ.real D|<ε := by
  let f : X → ℝ := fun x => (η.rnDeriv μ x).toReal
  have hf : Integrable f μ := by
    simpa only [mul_one] using (integrable_toReal_rnDeriv_mul_iff (f := fun _ => (1 : ℝ)) hac).mpr (integrable_const 1)
  have hmean : ∫ x,f x ∂μ=1 := by simpa only [f,Measure.real,measure_univ,ENNReal.toReal_one] using integral_toReal_rnDeriv hac
  have ht := (ergodic_L1 he.symm hf).eventually (gt_mem_nhds hε)
  filter_upwards [ht,eventually_gt_atTop 0] with N hN hN0
  refine ⟨hN0,fun D hD => ?_⟩
  rw [cesaroLawMass_density μ η e he.toMeasurePreserving hac N hD]
  have hmu : μ.real D=∫ _x : X in D,(1 : ℝ) ∂μ := by simp
  rw [hmu,←integral_sub (orbitAverage_integrable he.symm.toMeasurePreserving hf N).integrableOn (integrable_const 1)]
  exact (abs_setIntegral_le_L1 μ ((orbitAverage_integrable he.symm.toMeasurePreserving hf N).sub (integrable_const 1)) D).trans_lt
    (by simpa only [Pi.sub_apply,hmean] using hN)

end HyperbolicCoding

end
section
namespace HyperbolicCoding
open MeasureTheory MeasureTheory.Measure Set Filter
open scoped ENNReal Topology
variable {X A : Type*} [MeasurableSpace X] [MeasurableSpace A]

omit [MeasurableSpace A] in
lemma remotePair_translate (e : X ≃ᵐ X) (α : X → A) (n i : ℕ) :
    remotePair e e.symm α (n+i) ∘ e^[i]=
      (Prod.map id (dropName (2*i))) ∘ remotePair e e.symm α n := by
  funext x
  apply Prod.ext
  · funext j
    change α (e.symm^[j+(n+i)] (e^[i] x))=α (e.symm^[j+n] x)
    rw [←Nat.add_assoc,Function.iterate_add_apply]
    rw [(show Function.LeftInverse (e.symm : X → X) e from e.symm_apply_apply).iterate i x]
  · funext j
    change α (e^[j+(n+i)] (e^[i] x))=α (e^[(j+2*i)+n] x)
    rw [←Function.iterate_add_apply]
    congr 2
    omega

lemma remoteProduct_drop (μ : Measure X) [IsProbabilityMeasure μ]
    (e : X ≃ᵐ X) (he : MeasurePreserving e μ μ) {α : X → A} (hα : Measurable α) (i : ℕ) :
    (remoteProductLaw μ e e.symm α).map (Prod.map id (dropName i))=
      remoteProductLaw μ e e.symm α := by
  have : IsProbabilityMeasure (μ.map (tailName e.symm α 0)) := Measure.isProbabilityMeasure_map (measurable_tailName e.symm.measurable hα 0).aemeasurable
  have _hunused : True := by first | trivial | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | (apply Measurable.aemeasurable; measurability) | measurability)
  have : IsProbabilityMeasure (μ.map (tailName e α 0)) := Measure.isProbabilityMeasure_map (measurable_tailName e.measurable hα 0).aemeasurable
  have _hunused : True := by first | trivial | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | (apply Measurable.aemeasurable; measurability) | measurability)
  rw [remoteProductLaw,←Measure.map_prod_map _ _ measurable_id (measurable_dropName i),Measure.map_id,
    stationary_drop_law μ he hα i]

lemma RemoteIndependent.translate {μ η : Measure X} [IsProbabilityMeasure μ]
    (e : X ≃ᵐ X) (he : MeasurePreserving e μ μ) {α : X → A} (hα : Measurable α)
    (h : RemoteIndependent μ η e e.symm α) (i : ℕ) :
    RemoteIndependent μ (η.map (e^[i])) e e.symm α := by
  intro ε hε
  have ht := (tendsto_sub_atTop_nat i).eventually (h ε hε)
  filter_upwards [ht,eventually_ge_atTop i] with n hn hni
  have hc := hn.map (measurable_id.prodMap (measurable_dropName (2*i)))
  rw [remoteProduct_drop μ e he hα (2*i)] at hc
  rw [Measure.map_map (measurable_id.prodMap (measurable_dropName (2*i)))
    (measurable_remotePair e.measurable e.symm.measurable hα (n-i))] at hc
  rw [←remotePair_translate e α (n-i) i,Nat.sub_add_cancel hni] at hc
  rw [Measure.map_map (measurable_remotePair e.measurable e.symm.measurable hα n) (e.measurable.iterate i)]
  exact hc

end HyperbolicCoding

end
section
namespace HyperbolicCoding
open MeasureTheory MeasureTheory.Measure Set Filter
open scoped ENNReal Topology BigOperators
variable {X A : Type*} [MeasurableSpace X] [MeasurableSpace A]

lemma cesaroLawMass_close (e : X ≃ᵐ X) (η : Measure X) {N : ℕ} (hN : 0<N)
    (D : Set X) {b δ : ℝ} (h : ∀ i∈Finset.range N,|(η.map (e^[i])).real D-b|≤δ) :
    |cesaroLawMass e η N D-b|≤δ := by
  have hN' : (0 : ℝ)<N := by exact_mod_cast hN
  have heq : cesaroLawMass e η N D-b=
      (∑ i∈Finset.range N,((η.map (e^[i])).real D-b))/(N : ℝ) := by
    simp only [cesaroLawMass,Finset.sum_sub_distrib,Finset.sum_const,Finset.card_range,nsmul_eq_mul,sub_div]
    rw [mul_div_cancel_left₀ b hN'.ne']
  rw [heq,abs_div,abs_of_pos hN']
  calc
    _≤(∑ i∈Finset.range N,|(η.map (e^[i])).real D-b|)/(N : ℝ) :=
      div_le_div_of_nonneg_right (Finset.abs_sum_le_sum_abs _ _) hN'.le
    _≤(∑ _i∈Finset.range N,δ)/(N : ℝ) :=
      div_le_div_of_nonneg_right (Finset.sum_le_sum h) hN'.le
    _=δ := by simp only [Finset.sum_const,Finset.card_range,nsmul_eq_mul,mul_div_cancel_left₀ δ hN'.ne']

theorem weakBernoulli_of_ac_remote (μ η : Measure X)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure η]
    (e : X ≃ᵐ X) (he : Ergodic e μ) (hac : η≪μ)
    {α : X → A} (hα : Measurable α) (h : RemoteIndependent μ η e e.symm α) :
    WeakBernoulliProcess μ e α := by
  intro ε hε
  have hh : 0<ε/2 := by linarith
  obtain ⟨N,hN,happrox⟩ := (cesaro_ac_uniform μ η e he hac hh).exists
  have hall : ∀ᶠ n : ℕ in atTop,∀ i : Fin N,
      LawClose ((η.map (e^[i.val])).map (remotePair e e.symm α n))
        (remoteProductLaw μ e e.symm α) (ε/2) := by
    exact Filter.eventually_all.2 (fun i => h.translate e he.toMeasurePreserving hα i.val (ε/2) hh)
  filter_upwards [hall] with n hn D hD
  let C := remotePair e e.symm α n ⁻¹' D
  have hC : MeasurableSet C := hD.preimage (measurable_remotePair e.measurable e.symm.measurable hα n)
  have hav := cesaroLawMass_close e η hN C (b := (remoteProductLaw μ e e.symm α).real D)
    (δ := ε/2) (fun i hi => by
      have hc := hn ⟨i,Finset.mem_range.mp hi⟩ D hD
      simpa only [Measure.real,Measure.map_apply (measurable_remotePair e.measurable e.symm.measurable hα n) hD,C]
        using hc)
  have ha := happrox C hC
  rw [abs_sub_comm] at ha
  simp only [Measure.real,Measure.map_apply (measurable_remotePair e.measurable e.symm.measurable hα n) hD]
  change |μ.real C-(remoteProductLaw μ e e.symm α).real D|≤ε
  exact (abs_sub_le _ (cesaroLawMass e η N C) _).trans
    ((add_le_add ha.le hav).trans (by linarith))

end HyperbolicCoding

end
section
namespace StandardMapEntropy
open MeasureTheory MeasureTheory.Measure Set Filter Topology HyperbolicCoding
open scoped ENNReal
namespace ReversibleGraphRectangle
variable {k χ : ℝ} {B : ReversibleRectangleBlock k χ} {F : ReversibleGraphFamilies B}
    (R : ReversibleGraphRectangle F)

theorem weakBernoulli_of_good_names {N : ℕ} (hN : 0<N)
    (μ : Measure Torus) [IsProbabilityMeasure μ]
    (herg : ∀ r : ℕ,0 < r → Ergodic (((standardMap k)^[N])^[r]) μ)
    (hπ : QuasiMeasurePreserving R.torusPoint (B.carrierProbability.prod B.carrierProbability) μ)
    {A : Type*} [Fintype A] [MeasurableSpace A] [MeasurableSingletonClass A]
    (α : Torus → A) (hα : Measurable α)
    (hf : GoodNames μ ((standardMap k)^[N]) α)
    (hb : GoodNames μ ((inverseMap k)^[N]) α) :
    WeakBernoulliProcess μ (iterateEquiv (standardMap_measurableEquiv k) N) α := by
  let e := iterateEquiv (standardMap_measurableEquiv k) N
  have heq : (e : Torus → Torus)=(standardMap k)^[N] := funext (iterateEquiv_apply _ N)
  have heq' : (e.symm : Torus → Torus)=(inverseMap k)^[N] := funext (iterateEquiv_symm_apply _ N)
  have he : Ergodic e μ := by
    rw [heq]
    simpa only [Function.iterate_one] using herg 1 (by omega)
  let ζ := (B.carrierProbability.prod B.carrierProbability).map R.torusPoint
  have : IsProbabilityMeasure ζ := by first | infer_instance | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | (apply Measurable.aemeasurable; measurability) | measurability)
  apply weakBernoulli_of_ac_remote μ ζ e he hπ.absolutelyContinuous hα
  have htriv : ∀ E,TailEvent μ e α E → (∀ᵐ x ∂μ,x∈E) ∨ (∀ᵐ x ∂μ,x∉E) := by
    rw [heq]
    exact R.tail_trivial_of_good_names hN μ herg hπ α hα hf hb
  have hfst : MeasurePreserving (Prod.fst : (B.coordinateCarrier×B.coordinateCarrier)×
      (B.coordinateCarrier×B.coordinateCarrier) → B.coordinateCarrier×B.coordinateCarrier)
      ((B.carrierProbability.prod B.carrierProbability).prod (B.carrierProbability.prod B.carrierProbability))
      (B.carrierProbability.prod B.carrierProbability) := measurePreserving_fst
  have hgood := hfst.quasiMeasurePreserving.ae (hπ.ae (hf.and hb))
  apply local_remote_independent B.carrierProbability B.carrierProbability μ hπ
    he.toMeasurePreserving (he.toMeasurePreserving.symm e) hα htriv
    (tail_trivial_symm μ e he.toMeasurePreserving hα htriv)
  · filter_upwards [hgood] with w hw
    rw [heq']
    exact hw.2 _ ((R.column_exponential w.1.1 w.2.1 w.1.2).iterate hN)
  · filter_upwards [hgood] with w hw
    rw [heq]
    exact hw.1 _ ((R.row_exponential w.1.1 w.1.2 w.2.2).iterate hN)

theorem exists_weakBernoulli_partitions_q44_oai {N : ℕ} (hN : 0<N)
    (μ : Measure Torus) [IsProbabilityMeasure μ]
    (herg : ∀ r : ℕ,0 < r → Ergodic (((standardMap k)^[N])^[r]) μ)
    (hπ : QuasiMeasurePreserving R.torusPoint (B.carrierProbability.prod B.carrierProbability) μ) :
    ∃ α : ℕ → ℕ → Torus → Bool,
      (∀ i j,Measurable (α i j)) ∧ Function.Injective (fun z => fun i j => α i j z) ∧
      ∀ M : ℕ,WeakBernoulliProcess μ (iterateEquiv (standardMap_measurableEquiv k) N) (joinedBinary α M) := by
  obtain ⟨α,hm,hi,hgood⟩ := R.exists_good_K_partitions hN μ herg hπ
  exact ⟨α,hm,hi,fun M => R.weakBernoulli_of_good_names hN μ herg hπ _
    (measurable_joinedBinary hm M) (hgood M).1 (hgood M).2.1⟩

end ReversibleGraphRectangle

end StandardMapEntropy

end
end

end OAI
end

theorem solution : type_of% @OAI.StandardMapEntropy.ReversibleGraphRectangle.exists_weakBernoulli_partitions_q44_oai := @OAI.StandardMapEntropy.ReversibleGraphRectangle.exists_weakBernoulli_partitions_q44_oai
